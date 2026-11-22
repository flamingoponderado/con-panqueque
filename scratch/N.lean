import ConPanqueque.Logic.Basic
open Flapjack Flapjack.PanSemStateFiniteExact
open Lean in
#eval show Lean.MetaM Unit from do
  let e ← Lean.Meta.mkConstWithFreshMVarLevels (← Lean.Elab.Term.TermElabM.run' (Lean.Elab.realizeGlobalConstNoOverloadWithInfo (Lean.mkIdent `evaluateHOLFiniteState_eq_evaluate_def)))
  IO.println s!"{e}"
