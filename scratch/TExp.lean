import ConPanqueque.Logic.Basic
open Lean Meta Elab Command Term
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString

namespace ConPanqueque.Translate

/-- Compile a Lean `UInt64` term (variables `vars`, each named after its Pancake
local) to surface syntax for an `ExpHOL 64`. -/
partial def toPanSyntax (vars : Array (Expr × String)) (e : Expr) : MetaM (TSyntax `term) := do
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
  | _ => throwError "toPanSyntax: unsupported term {e}"

/-- `pan_exp N := fun (x₁ … xₙ : UInt64) => t` defines `N : ExpHOL 64` computing `t`
from the locals `x₁ … xₙ`, and `N_eval`, its correctness, proved by evaluation. -/
elab "pan_exp " nm:ident " := " t:term : command => do
  let (body, names) ← liftTermElabM do
    let f ← elabTerm t none
    synthesizeSyntheticMVarsNoPostponing
    let f ← instantiateMVars f
    lambdaTelescope f fun xs b => do
      let names ← xs.mapM fun x => do return (← x.fvarId!.getUserName).toString
      let b ← zetaReduce b
      let s ← toPanSyntax (xs.zip names) b
      return (s, names)
  let defName := nm.getId
  elabCommand (← `(def $nm : ExpHOL 64 := $body))
  let binders ← names.mapM fun n => `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent n.toName) : UInt64))
  let hyps ← names.mapM fun n => do
    let h := mkIdent (Name.mkSimple ("h_" ++ n))
    `(Lean.Parser.Term.bracketedBinderF|
      ($h : s.locals.lookup (ofString $(quote n)) = some (.val (.word $(mkIdent n.toName).toBitVec))))
  let hnames := names.map fun n => mkIdent (Name.mkSimple ("h_" ++ n))
  let simpArgs : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ← hnames.mapM fun h =>
    `(Lean.Parser.Tactic.simpLemma| $h:term)
  let app ← `($t $(names.map (fun n => (mkIdent n.toName : TSyntax `term)))*)
  let thm := mkIdent (defName ++ `eval)
  elabCommand (← `(
    theorem $thm {σ : Type} (s : PanSemStateFiniteExact 64 σ) $binders* $hyps* :
        @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) $nm =
          some (.val (.word ($app).toBitVec)) := by
      simp [$nm:ident, evalHOLExact, evalListHOLExact, wordOpHOL, wordOp, valueIsWord, valueWord, panOpHOL,
        wordShiftHOL, $simpArgs,*]))

end ConPanqueque.Translate

open ConPanqueque.Translate Flapjack.PanSemStateFiniteExact
pan_exp mixTest := fun (h k : UInt64) =>
  let m : UInt64 := 0xc6a4a7935bd1e995
  let k := k * m
  let k := k ^^^ (k >>> 47)
  let k := k ^^^ m
  let h := h ^^^ k
  h * m
#check @mixTest.eval
