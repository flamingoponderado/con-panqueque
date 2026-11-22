import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

example {σ : Type} (s : PanSemStateFiniteExact 64 σ) (k : VarKind) (n : MlS) (e : ExpHOL 64)
    (v : ValueHOL 64)
    (he : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v)
    (hv : isValidValueHOLFinite s k n v = true) :
    evaluateHOLFiniteState s (.assign k n e) = (none, setKvarHOLFinite k n v s) := by
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  simp only [he, hv, if_true]

#check @isValidValueHOLFinite
#print setKvarHOLFinite
#print setVarHOLFinite
