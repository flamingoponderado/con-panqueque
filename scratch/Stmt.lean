import ConPanqueque.Logic.Basic
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString

example {σ : Type} (s : PanSemStateFiniteExact 64 σ) (x : UInt64)
    (hx : s.locals.lookup (ofString "x") = some (.val (.word x.toBitVec))) :
    (evaluateHOLFiniteState s
      (.dec (ofString "y") .one (.op .add [.var .local (ofString "x"), .const 5])
        (.return (.panop .mul [.var .local (ofString "y"), .var .local (ofString "y")])))).1 =
      some (.returned (.val (.word ((x + 5) * (x + 5)).toBitVec))) := by
  simp [evaluateHOLFiniteState_eq_evaluate_def, evalHOLExact, evalListHOLExact, hx, wordOpHOL, wordOp,
    valueIsWord, valueWord, panOpHOL, shapeOfHOLExact, shapeEqHOL, setVarHOLFinite, FUPDATE]

example {σ : Type} (s : PanSemStateFiniteExact 64 σ) (x : UInt64)
    (hx : s.locals.lookup (ofString "x") = some (.val (.word x.toBitVec)))
    (hc : s.code.lookup (ofString "sq") = some ([(ofString "a", .one)],
      .return (.panop .mul [.var .local (ofString "a"), .var .local (ofString "a")]), .one))
    (hclk : s.clock ≠ 0) :
    (evaluateHOLFiniteState s
      (.dec (ofString "y") .one (.const 0)
        (.seq (.call (some (some (.local, ofString "y"), none)) (ofString "sq") [.op .add [.var .local (ofString "x"), .const 1]])
          (.return (.var .local (ofString "y")))))).1 =
      some (.returned (.val (.word ((x + 1) * (x + 1)).toBitVec))) := by
  simp [evaluateHOLFiniteState_eq_evaluate_def, evaluateHOLFiniteState_call, evalHOLExact, evalListHOLExact,
    evalListHOLFinite, hx, hc, hclk, wordOpHOL, wordOp,
    valueIsWord, valueWord, panOpHOL, shapeOfHOLExact, shapeEqHOL, setVarHOLFinite, FUPDATE, lookupCodeHOLFinite,
    lookupCodeHOLExact, callEntryStateHOLFinite, isValidValueHOLExact, lookupKvarHOLExact, setKvarHOLFinite]
