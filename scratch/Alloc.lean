import ConPanqueque.Logic.Basic
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
