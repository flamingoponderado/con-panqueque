import ConPanqueque.Logic.Basic
/-!
# The bump allocator (beginning)

Pancake has no allocation: con-panqueque keeps a global heap pointer `hp`
(PLAN.md, "Memory"). `allocBody` is the allocator's body; the bounds check
against `@top`, the state postcondition (`hp = h + n`) and the call wrapper
follow.
-/

namespace ConPanqueque.Alloc
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString

/-- `var p = hp; hp = hp + n; return p;` -/
def allocBody : ProgHOL 64 :=
  .dec (ofString "p") .one (.var .global (ofString "hp"))
    (.seq (.assign .global (ofString "hp") (.op .add [.var .global (ofString "hp"), .var .local (ofString "n")]))
      (.return (.var .local (ofString "p"))))

theorem allocBody_ret {σ : Type} (s : PanSemStateFiniteExact 64 σ) (h n : BitVec 64)
    (hhp : s.globals.lookup (ofString "hp") = some (.val (.word h)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n))) :
    (evaluateHOLFiniteState s allocBody).1 = some (.returned (.val (.word h))) := by
  unfold allocBody
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  simp [evalHOLExact, hhp, shapeOfHOLExact, shapeEqHOL]
  have hne : ofString "n" ≠ ofString "p" := by decide
  have hn' : (setVarHOLFinite (ofString "p") (.val (.word h)) s).locals.lookup (ofString "n") =
      some (.val (.word n)) := by rw [ConPanqueque.Logic.lookup_setVar_other _ _ hne, hn]
  rw [ConPanqueque.Logic.seq_normal _ (ConPanqueque.Logic.assign_ok _ .global _ _ (.val (.word (h + n))) ?he ?hv)]
  · rw [evaluateHOLFiniteState_eq_evaluate_def]
    simp [evalHOLExact, setKvarHOLFinite, setGlobalHOLFinite, shapeOfHOLExact]
  · simp [evalHOLExact, evalListHOLExact, setVarHOLFinite, FUPDATE, Ne.symm hne, hn, hhp, wordOpHOL,
      wordOp, valueIsWord, valueWord]
  · simp [isValidValueHOLFinite, lookupKvarHOLFinite, setVarHOLFinite, hhp, shapeOfHOLExact, shapeEqHOL]

open ConPanqueque.Logic in
/-- The allocator body's full effect: it returns the old pointer `h`, leaves
`hp = h + n`, and changes neither memory, its domain nor the code. -/
theorem allocBody_spec {σ : Type} (s : PanSemStateFiniteExact 64 σ) (h n : BitVec 64)
    (hhp : s.globals.lookup (ofString "hp") = some (.val (.word h)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n))) :
    ∃ s', evaluateHOLFiniteState s allocBody = (some (.returned (.val (.word h))), s') ∧
      s'.globals.lookup (ofString "hp") = some (.val (.word (h + n))) ∧ s'.memory = s.memory ∧
      s'.memaddrs = s.memaddrs ∧ s'.code = s.code := by
  have hne : ofString "n" ≠ ofString "p" := by decide
  have hset : evaluateHOLFiniteState (setVarHOLFinite (ofString "p") (.val (.word h)) s)
      (.seq (.assign .global (ofString "hp") (.op .add [.var .global (ofString "hp"), .var .local (ofString "n")]))
        (.return (.var .local (ofString "p")))) =
      evaluateHOLFiniteState (setKvarHOLFinite .global (ofString "hp") (.val (.word (h + n)))
        (setVarHOLFinite (ofString "p") (.val (.word h)) s)) (.return (.var .local (ofString "p"))) := by
    apply seq_normal
    apply assign_ok
    · simp [evalHOLExact, evalListHOLExact, setVarHOLFinite, FUPDATE, Ne.symm hne, hn, hhp, wordOpHOL,
        wordOp, valueIsWord, valueWord]
    · simp [isValidValueHOLFinite, lookupKvarHOLFinite, setVarHOLFinite, hhp, shapeOfHOLExact, shapeEqHOL]
  unfold allocBody
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  simp only [evalHOLExact, hhp]
  simp [shapeOfHOLExact, shapeEqHOL, hset]
  simp [evalHOLExact, setKvarHOLFinite, setGlobalHOLFinite, setVarHOLFinite, shapeOfHOLExact,
    emptyLocalsHOLFinite, FUPDATE]

end ConPanqueque.Alloc
