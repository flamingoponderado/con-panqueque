import ConPanqueque.Translate.Ev
open Lean Meta Elab Command Term
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString

/-!
# Translator, part 1: word expressions

`pan_exp N := fun (x₁ … xₙ : UInt64) => t` compiles a Lean `UInt64` term (literals,
`+ - * &&& ||| ^^^`, constant shifts, `/` and `%` by powers of two, `if` on
`< ≤ = ≠` as `y + (x - y)·[c]`, `let`) to a Pancake expression `N` over the
locals `x₁ … xₙ`, and proves `N.eval`: in any state where those locals hold the
words, `N` evaluates to `t`. The proof is generated (evaluation by `simp`), so
con-leche's word-level code (hashing, data-word arithmetic) translates without
hand-written proofs.
-/

namespace ConPanqueque.Translate

/-- Compile a Lean `UInt64` term (variables `vars`, each named after its Pancake
local) to surface syntax for an `ExpHOL 64`, together with a proof term of
`PEv s e t` built from the compositional lemmas of `Translate/Ev.lean` (the local
`x` is assumed by the hypothesis `h_x`). -/
partial def toPanPair (vars : Array (Expr × String)) (e : Expr) :
    StateT (Array Name) MetaM (TSyntax `term × TSyntax `term) := do
  let e ← instantiateMVars e
  for (v, n) in vars do
    if e == v then
      let h := mkIdent (Name.mkSimple ("h_" ++ n))
      return (← `(ExpHOL.var .local (ofString $(quote n))), ← `(ConPanqueque.Translate.ev_var $h))
  let bin (op : TSyntax `term) (lem : Name) (a b : Expr) : StateT (Array Name) MetaM (TSyntax `term × TSyntax `term) := do
    let (a', pa) ← toPanPair vars a
    let (b', pb) ← toPanPair vars b
    return (← `(ExpHOL.op $op [$a', $b']), ← `($(mkIdent lem) $pa $pb))
  let litK (x : Expr) : Option Nat :=
    match x with
    | .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal k))) _ => some k
    | _ => none
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[_, .lit (.natVal n), _]) =>
      return (← `(ExpHOL.const (BitVec.ofNat 64 $(quote n))), ← `(ConPanqueque.Translate.ev_lit s $(quote n)))
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => bin (← `(.add)) ``ConPanqueque.Translate.ev_add a b
  | (``HSub.hSub, #[_, _, _, _, a, b]) => bin (← `(.sub)) ``ConPanqueque.Translate.ev_sub a b
  | (``HXor.hXor, #[_, _, _, _, a, b]) => bin (← `(.xor)) ``ConPanqueque.Translate.ev_xor a b
  | (``HAnd.hAnd, #[_, _, _, _, a, b]) => bin (← `(.and)) ``ConPanqueque.Translate.ev_and a b
  | (``HOr.hOr, #[_, _, _, _, a, b]) => bin (← `(.or)) ``ConPanqueque.Translate.ev_or a b
  | (``HMul.hMul, #[_, _, _, _, a, b]) => do
      let (a', pa) ← toPanPair vars a
      let (b', pb) ← toPanPair vars b
      return (← `(ExpHOL.panop .mul [$a', $b']), ← `(ConPanqueque.Translate.ev_mul $pa $pb))
  | (``ConPanqueque.Hash.leanMixHash, #[a, b]) => do
      let (a', pa) ← toPanPair vars a
      let (b', pb) ← toPanPair vars b
      return (← `(ConPanqueque.Hash.mixExp $a' $b'), ← `(ConPanqueque.Translate.ev_mix $pa $pb))
  | (``HShiftRight.hShiftRight, #[_, _, _, _, a, kx]) =>
      match litK kx with
      | some k =>
        if k < 64 then do
          let (a', pa) ← toPanPair vars a
          return (← `(ExpHOL.shift .lsr $a' (ExpHOL.const (BitVec.ofNat 64 $(quote k)))),
            ← `(ConPanqueque.Translate.ev_shr $(quote k) (by decide) $pa))
        else throwError "toPanSyntax: shift by {k}"
      | none => throwError "toPanSyntax: shift by a non-literal"
  | (``HShiftLeft.hShiftLeft, #[_, _, _, _, a, kx]) =>
      match litK kx with
      | some k =>
        if k < 64 then do
          let (a', pa) ← toPanPair vars a
          return (← `(ExpHOL.shift .lsl $a' (ExpHOL.const (BitVec.ofNat 64 $(quote k)))),
            ← `(ConPanqueque.Translate.ev_shl $(quote k) (by decide) $pa))
        else throwError "toPanSyntax: shift by {k}"
      | none => throwError "toPanSyntax: shift by a non-literal"
  | (``HDiv.hDiv, #[_, _, _, _, a, nx]) =>
      match litK nx with
      | some n =>
        match (List.range 64).find? (fun k => 2 ^ k = n) with
        | some k => do
            let (a', pa) ← toPanPair vars a
            return (← `(ExpHOL.shift .lsr $a' (ExpHOL.const (BitVec.ofNat 64 $(quote k)))),
              ← `(ConPanqueque.Translate.ev_div $(quote k) $(quote n) (by decide) (by decide) $pa))
        | none => throwError "toPanSyntax: division by {n} (not a power of two)"
      | none => throwError "toPanSyntax: division by a non-literal"
  | (``HMod.hMod, #[_, _, _, _, a, nx]) =>
      match litK nx with
      | some n =>
        match (List.range 64).find? (fun k => 2 ^ k = n) with
        | some 0 => do
            let (_, pa) ← toPanPair vars a
            let _ := pa
            return (← `(ExpHOL.const (BitVec.ofNat 64 0)), ← `(ConPanqueque.Translate.ev_mod1 s _))
        | some k => do
            let j := 64 - k
            let (a', pa) ← toPanPair vars a
            return (← `(ExpHOL.shift .lsr (ExpHOL.shift .lsl $a' (ExpHOL.const (BitVec.ofNat 64 $(quote j))))
                (ExpHOL.const (BitVec.ofNat 64 $(quote j)))),
              ← `(ConPanqueque.Translate.ev_mod $(quote k) $(quote n) $(quote j) (by decide) (by decide) (by decide)
                (by decide) $pa))
        | none => throwError "toPanSyntax: modulo by {n} (not a power of two)"
      | none => throwError "toPanSyntax: modulo by a non-literal"
  | (``ite, #[_, c, _, x, y]) => do
      let (x', px) ← toPanPair vars x
      let (y', py) ← toPanPair vars y
      let (cmp, prf) ← match c.getAppFnArgs with
        | (``LT.lt, #[_, _, a, b]) => do
            let (a', pa) ← toPanPair vars a; let (b', pb) ← toPanPair vars b
            pure (← `(ExpHOL.cmp .lower $a' $b'), ← `(ConPanqueque.Translate.ev_ite_lt $pa $pb $px $py))
        | (``LE.le, #[_, _, a, b]) => do
            let (a', pa) ← toPanPair vars a; let (b', pb) ← toPanPair vars b
            pure (← `(ExpHOL.cmp .notLower $b' $a'), ← `(ConPanqueque.Translate.ev_ite_le $pa $pb $px $py))
        | (``Eq, #[_, a, b]) => do
            let (a', pa) ← toPanPair vars a; let (b', pb) ← toPanPair vars b
            pure (← `(ExpHOL.cmp .equal $a' $b'), ← `(ConPanqueque.Translate.ev_ite_eq $pa $pb $px $py))
        | (``Ne, #[_, a, b]) => do
            let (a', pa) ← toPanPair vars a; let (b', pb) ← toPanPair vars b
            pure (← `(ExpHOL.cmp .notEqual $a' $b'), ← `(ConPanqueque.Translate.ev_ite_ne $pa $pb $px $py))
        | _ => throwError "toPanSyntax: unsupported condition {c}"
      return (← `(ExpHOL.op .add [$y', ExpHOL.panop .mul [ExpHOL.op .sub [$x', $y'], $cmp]]), prf)
  | _ =>
    -- a non-recursive definition (e.g. one of con-leche's helpers): unfold it
    if e.getAppFn.isConst then
      if let some e' ← unfoldDefinition? e then
        modify (·.push e.getAppFn.constName!)
        return ← toPanPair vars (← zetaReduce e'.headBeta)
    throwError "toPanSyntax: unsupported term {e}"

/-- The expression part of `toPanPair`. -/
def toPanSyntax (vars : Array (Expr × String)) (e : Expr) : StateT (Array Name) MetaM (TSyntax `term) := do
  return (← toPanPair vars e).1

/-- `pan_exp N := fun (x₁ … xₙ : UInt64) => t` defines `N : ExpHOL 64` computing `t`
from the locals `x₁ … xₙ`, and `N_eval`, its correctness, proved by evaluation. -/
elab "pan_exp " nm:ident " := " t:term : command => do
  let (body, prf, names) ← liftTermElabM do
    let f ← elabTerm t none
    synthesizeSyntheticMVarsNoPostponing
    let f ← instantiateMVars f
    lambdaTelescope f fun xs b => do
      let names ← xs.mapM fun x => do return (← x.fvarId!.getUserName).toString
      let b ← zetaReduce b
      let ((s, p), _) ← (toPanPair (xs.zip names) b).run #[]
      return (s, p, names)
  let defName := nm.getId
  elabCommand (← `(def $nm : ExpHOL 64 := $body))
  let binders ← names.mapM fun n => `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent n.toName) : UInt64))
  let hyps ← names.mapM fun n => do
    let h := mkIdent (Name.mkSimple ("h_" ++ n))
    `(Lean.Parser.Term.bracketedBinderF|
      ($h : s.locals.lookup (ofString $(quote n)) = some (.val (.word $(mkIdent n.toName).toBitVec))))
  let app ← `($t $(names.map (fun n => (mkIdent n.toName : TSyntax `term)))*)
  let thm := mkIdent (defName ++ `eval)
  elabCommand (← `(
    theorem $thm {σ : Type} (s : PanSemStateFiniteExact 64 σ) $binders* $hyps* :
        @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) $nm =
          some (.val (.word ($app).toBitVec)) := by
      have hp := $prf
      exact hp))

end ConPanqueque.Translate

/-! Example: `leanMixHash`'s body, translated and proved. -/
open ConPanqueque.Translate Flapjack.PanSemStateFiniteExact in
pan_exp mixTest := fun (h k : UInt64) =>
  let m : UInt64 := 0xc6a4a7935bd1e995
  let k := k * m
  let k := k ^^^ (k >>> 47)
  let k := k ^^^ m
  let h := h ^^^ k
  h * m

/-! Examples: con-leche's data-word arithmetic, in its own style (division and
modulo by powers of two, `max` as `if`), translated and proved. -/
open ConPanqueque.Translate Flapjack.PanSemStateFiniteExact in
pan_exp hashOfDataT := fun (w : UInt64) => w / 4294967296
open ConPanqueque.Translate Flapjack.PanSemStateFiniteExact in
pan_exp bvarOfDataT := fun (w : UInt64) => w / 65536 % 32768
open ConPanqueque.Translate Flapjack.PanSemStateFiniteExact in
pan_exp maxT := fun (x y : UInt64) => if x < y then y else x
open ConPanqueque.Translate Flapjack.PanSemStateFiniteExact in
pan_exp packDataT := fun (h b f : UInt64) => h * 4294967296 + b * 65536 + f * 2
