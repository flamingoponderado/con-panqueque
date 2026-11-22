import ConPanqueque.Logic.Basic
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
local) to surface syntax for an `ExpHOL 64`. -/
partial def toPanSyntax (vars : Array (Expr × String)) (e : Expr) : StateT (Array Name) MetaM (TSyntax `term) := do
  let e ← instantiateMVars e
  for (v, n) in vars do
    if e == v then return ← `(ExpHOL.var .local (ofString $(quote n)))
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[_, .lit (.natVal n), _]) => `(ExpHOL.const (BitVec.ofNat 64 $(quote n)))
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => do
      `(ExpHOL.op .add [$(← toPanSyntax vars a), $(← toPanSyntax vars b)])
  | (``HSub.hSub, #[_, _, _, _, a, b]) => do
      `(ExpHOL.op .sub [$(← toPanSyntax vars a), $(← toPanSyntax vars b)])
  | (``HMul.hMul, #[_, _, _, _, a, b]) => do
      `(ExpHOL.panop .mul [$(← toPanSyntax vars a), $(← toPanSyntax vars b)])
  | (``HXor.hXor, #[_, _, _, _, a, b]) => do
      `(ExpHOL.op .xor [$(← toPanSyntax vars a), $(← toPanSyntax vars b)])
  | (``HAnd.hAnd, #[_, _, _, _, a, b]) => do
      `(ExpHOL.op .and [$(← toPanSyntax vars a), $(← toPanSyntax vars b)])
  | (``HOr.hOr, #[_, _, _, _, a, b]) => do
      `(ExpHOL.op .or [$(← toPanSyntax vars a), $(← toPanSyntax vars b)])
  | (``HShiftRight.hShiftRight, #[_, _, _, _, a, .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal k))) _]) =>
      if k < 64 then do `(ExpHOL.shift .lsr $(← toPanSyntax vars a) (ExpHOL.const (BitVec.ofNat 64 $(quote k))))
      else throwError "toPanSyntax: shift by {k}"
  | (``HShiftLeft.hShiftLeft, #[_, _, _, _, a, .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal k))) _]) =>
      if k < 64 then do `(ExpHOL.shift .lsl $(← toPanSyntax vars a) (ExpHOL.const (BitVec.ofNat 64 $(quote k))))
      else throwError "toPanSyntax: shift by {k}"
  | (``HDiv.hDiv, #[_, _, _, _, a, .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _]) =>
      match (List.range 64).find? (fun k => 2 ^ k = n) with
      | some k => do `(ExpHOL.shift .lsr $(← toPanSyntax vars a) (ExpHOL.const (BitVec.ofNat 64 $(quote k))))
      | none => throwError "toPanSyntax: division by {n} (not a power of two)"
  | (``HMod.hMod, #[_, _, _, _, a, .app (.app (.app (.const ``OfNat.ofNat _) _) (.lit (.natVal n))) _]) =>
      match (List.range 64).find? (fun k => 2 ^ k = n) with
      | some 0 => `(ExpHOL.const (BitVec.ofNat 64 0))
      | some k => do
          let j := 64 - k
          `(ExpHOL.shift .lsr (ExpHOL.shift .lsl $(← toPanSyntax vars a) (ExpHOL.const (BitVec.ofNat 64 $(quote j))))
              (ExpHOL.const (BitVec.ofNat 64 $(quote j))))
      | none => throwError "toPanSyntax: modulo by {n} (not a power of two)"
  | (``ite, #[_, c, _, x, y]) => do
      let x' ← toPanSyntax vars x
      let y' ← toPanSyntax vars y
      let cmp ← match c.getAppFnArgs with
        | (``LT.lt, #[_, _, a, b]) => do `(ExpHOL.cmp .lower $(← toPanSyntax vars a) $(← toPanSyntax vars b))
        | (``LE.le, #[_, _, a, b]) => do `(ExpHOL.cmp .notLower $(← toPanSyntax vars b) $(← toPanSyntax vars a))
        | (``Eq, #[_, a, b]) => do `(ExpHOL.cmp .equal $(← toPanSyntax vars a) $(← toPanSyntax vars b))
        | (``Ne, #[_, a, b]) => do `(ExpHOL.cmp .notEqual $(← toPanSyntax vars a) $(← toPanSyntax vars b))
        | _ => throwError "toPanSyntax: unsupported condition {c}"
      `(ExpHOL.op .add [$y', ExpHOL.panop .mul [ExpHOL.op .sub [$x', $y'], $cmp]])
  | _ =>
    -- a non-recursive definition (e.g. one of con-leche's helpers): unfold it
    if e.getAppFn.isConst then
      if let some e' ← unfoldDefinition? e then
        modify (·.push e.getAppFn.constName!)
        return ← toPanSyntax vars e'.headBeta
    throwError "toPanSyntax: unsupported term {e}"

/-- `pan_exp N := fun (x₁ … xₙ : UInt64) => t` defines `N : ExpHOL 64` computing `t`
from the locals `x₁ … xₙ`, and `N_eval`, its correctness, proved by evaluation. -/
elab "pan_exp " nm:ident " := " t:term : command => do
  let (body, names, unfolded) ← liftTermElabM do
    let f ← elabTerm t none
    synthesizeSyntheticMVarsNoPostponing
    let f ← instantiateMVars f
    lambdaTelescope f fun xs b => do
      let names ← xs.mapM fun x => do return (← x.fvarId!.getUserName).toString
      let b ← zetaReduce b
      let (s, unf) ← (toPanSyntax (xs.zip names) b).run #[]
      return (s, names, unf)
  let defName := nm.getId
  elabCommand (← `(def $nm : ExpHOL 64 := $body))
  let binders ← names.mapM fun n => `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent n.toName) : UInt64))
  let hyps ← names.mapM fun n => do
    let h := mkIdent (Name.mkSimple ("h_" ++ n))
    `(Lean.Parser.Term.bracketedBinderF|
      ($h : s.locals.lookup (ofString $(quote n)) = some (.val (.word $(mkIdent n.toName).toBitVec))))
  let hnames := names.map fun n => mkIdent (Name.mkSimple ("h_" ++ n))
  let simpArgs : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    (hnames ++ unfolded.map (fun c => mkIdent c)).mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:term)
  let app ← `($t $(names.map (fun n => (mkIdent n.toName : TSyntax `term)))*)
  let thm := mkIdent (defName ++ `eval)
  elabCommand (← `(
    theorem $thm {σ : Type} (s : PanSemStateFiniteExact 64 σ) $binders* $hyps* :
        @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) $nm =
          some (.val (.word ($app).toBitVec)) := by
      simp [$nm:ident, evalHOLExact, evalListHOLExact, wordOpHOL, wordOp, valueIsWord, valueWord, panOpHOL,
        wordShiftHOL, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, $simpArgs,*] <;>
      (try split) <;> (try split) <;>
      (try simp_all [UInt64.lt_iff_toBitVec_lt, UInt64.le_iff_toBitVec_le]) <;> (try bv_omega) <;>
      (try (apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft,
        Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow] <;> omega))))

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
