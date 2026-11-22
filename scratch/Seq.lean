import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

example {σ : Type} (s s1 : PanSemStateFiniteExact 64 σ) (p q : ProgHOL 64)
    (h : evaluateHOLFiniteState s p = (none, s1)) :
    evaluateHOLFiniteState s (.seq p q) = evaluateHOLFiniteState s1 q := by
  rw [evaluateHOLFiniteState_eq_evaluate_def s (.seq p q)]
  simp only [h]
