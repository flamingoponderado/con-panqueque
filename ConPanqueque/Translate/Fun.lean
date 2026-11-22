import ConPanqueque.Translate.Exp
open Lean Meta Elab Command Term
open Flapjack Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString

/-!
# Translator, part 2: straight-line functions

`pan_fun N := fun (x₁ … xₙ : UInt64) => t` compiles a `let`-chain over words to a
Pancake program (each `let` a declaration, shadowing as in Lean, the last term a
`return`) and proves `N.spec` by evaluation. Intermediate values are computed
once, unlike `pan_exp`, which inlines them.
-/

namespace ConPanqueque.Translate

/-- Compile a let-chain ending in a `UInt64` term to a Pancake program: each
`let x := v` a declaration, the final term a `return`. -/
partial def toPanProg (vars : Array (Expr × String)) (e : Expr) : StateT (Array Name) MetaM (TSyntax `term) := do
  match e with
  | .letE n _ v b _ =>
    let v' ← toPanSyntax vars v
    let nm := n.toString
    withLocalDeclD n (mkConst ``UInt64) fun x => do
      let rest ← toPanProg (vars.push (x, nm)) (b.instantiate1 x)
      `(ProgHOL.dec (ofString $(quote nm)) .one $v' $rest)
  | _ => do `(ProgHOL.return $(← toPanSyntax vars e))

/-- `pan_fun N := fun (x₁ … xₙ : UInt64) => t` defines the program `N : ProgHOL 64`
(lets as declarations, then `return`) and proves `N.spec`: from any state whose
locals `x₁ … xₙ` hold the arguments, it returns `t`. -/
elab "pan_fun " nm:ident " := " t:term : command => do
  let (body, names, unfolded) ← liftTermElabM do
    let f ← elabTerm t none
    synthesizeSyntheticMVarsNoPostponing
    let f ← instantiateMVars f
    lambdaTelescope f fun xs b => do
      let names ← xs.mapM fun x => do return (← x.fvarId!.getUserName).toString
      let (s, unf) ← (toPanProg (xs.zip names) b).run #[]
      return (s, names, unf)
  elabCommand (← `(def $nm : ProgHOL 64 := $body))
  let binders ← names.mapM fun n => `(Lean.Parser.Term.bracketedBinderF| ($(mkIdent n.toName) : UInt64))
  let hyps ← names.mapM fun n => do
    let h := mkIdent (Name.mkSimple ("h_" ++ n))
    `(Lean.Parser.Term.bracketedBinderF|
      ($h : s.locals.lookup (ofString $(quote n)) = some (.val (.word $(mkIdent n.toName).toBitVec))))
  let hnames := names.map fun n => mkIdent (Name.mkSimple ("h_" ++ n))
  let simpArgs : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) ←
    (hnames ++ unfolded.map (fun c => mkIdent c)).mapM fun h => `(Lean.Parser.Tactic.simpLemma| $h:term)
  let app ← `($t $(names.map (fun n => (mkIdent n.toName : TSyntax `term)))*)
  let thm := mkIdent (nm.getId ++ `spec)
  elabCommand (← `(
    theorem $thm {σ : Type} (s : PanSemStateFiniteExact 64 σ) $binders* $hyps* :
        (Flapjack.PanSemStateFiniteExact.evaluateHOLFiniteState s $nm).1 =
          some (Flapjack.PanSemResultExact.returned (.val (.word ($app).toBitVec))) := by
      simp (config := { decide := true }) [$nm:ident, Flapjack.evaluateHOLFiniteState_eq_evaluate_def, evalHOLExact, evalListHOLExact, wordOpHOL, wordOp,
        valueIsWord, valueWord, panOpHOL, wordShiftHOL, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        shapeOfHOLExact, shapeEqHOL, Flapjack.PanSemStateFiniteExact.setVarHOLFinite, FUPDATE, $simpArgs,*]))

end ConPanqueque.Translate

/-! Example: `leanMixHash` as a function body. -/
open ConPanqueque.Translate Flapjack.PanSemStateFiniteExact in
pan_fun mixF := fun (h k : UInt64) =>
  let m : UInt64 := 0xc6a4a7935bd1e995
  let k := k * m
  let k := k ^^^ (k >>> 47)
  let k := k ^^^ m
  let h := h ^^^ k
  h * m
