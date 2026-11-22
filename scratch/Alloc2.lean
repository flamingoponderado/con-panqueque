import ConPanqueque.Alloc
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Alloc ConPanqueque.Logic

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
