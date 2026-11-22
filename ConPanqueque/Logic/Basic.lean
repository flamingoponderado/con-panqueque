import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

/-!
# A program logic over Flapjack's Pancake semantics (beginning)

Flapjack ports Pancake's semantics (`evaluateHOLFiniteState`, with the
per-construct equations `evaluateHOLFiniteState_eq_evaluate_def`) and its
compiler; it has no program logic. Proofs that con-panqueque's Pancake code
refines con-leche's functions are built here, one construct at a time.

First step: an expression of local words, returned.
-/

namespace ConPanqueque.Logic
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- `return a + b` on two local words returns their (wrapping) sum. -/
theorem return_add {σ : Type} (s : PanSemStateFiniteExact 64 σ) (a b : MlS) (x y : BitVec 64)
    (ha : s.locals.lookup a = some (.val (.word x)))
    (hb : s.locals.lookup b = some (.val (.word y))) :
    (evaluateHOLFiniteState s (.return (.op .add [.var .local a, .var .local b]))).1 =
      some (.returned (.val (.word (x + y)))) := by
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  simp only
  simp [evalHOLExact, evalListHOLExact, ha, hb, wordOpHOL, wordOp, valueIsWord, valueWord,
    shapeOfHOLExact]

end ConPanqueque.Logic
