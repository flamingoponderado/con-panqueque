import ConPanqueque.Alloc
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Alloc ConPanqueque.Logic

/-- `var p = hp; if (@top - hp < n) { return 0; } else { hp = hp + n; return p; }` -/
def allocChecked : ProgHOL 64 :=
  .dec (ofString "p") .one (.var .global (ofString "hp"))
    (.ite (.cmp .lower (.op .sub [.topAddr, .var .global (ofString "hp")]) (.var .local (ofString "n")))
      (.return (.const 0))
      (.seq (.assign .global (ofString "hp") (.op .add [.var .global (ofString "hp"), .var .local (ofString "n")]))
        (.return (.var .local (ofString "p")))))

/-- Out of space: `return 0`, nothing else changes. -/
theorem allocChecked_full {σ : Type} (s : PanSemStateFiniteExact 64 σ) (h n : BitVec 64)
    (hhp : s.globals.lookup (ofString "hp") = some (.val (.word h)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hfull : s.topAddr - h < n) :
    (evaluateHOLFiniteState s allocChecked).1 = some (.returned (.val (.word 0))) := by
  have hne : ofString "n" ≠ ofString "p" := by decide
  unfold allocChecked
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  simp only [evalHOLExact, hhp]
  simp [shapeOfHOLExact, shapeEqHOL]
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  simp [evalHOLExact, evalListHOLExact, setVarHOLFinite, FUPDATE, Ne.symm hne, hn, hhp, wordOpHOL,
    wordOp, valueIsWord, valueWord, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hfull]
  simp [shapeOfHOLExact]

/-- Enough space: return the old pointer `h` and advance `hp` by `n`. -/
theorem allocChecked_ok {σ : Type} (s : PanSemStateFiniteExact 64 σ) (h n : BitVec 64)
    (hhp : s.globals.lookup (ofString "hp") = some (.val (.word h)))
    (hn : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (hfit : ¬ s.topAddr - h < n) :
    ∃ s', evaluateHOLFiniteState s allocChecked = (some (.returned (.val (.word h))), s') ∧
      s'.globals.lookup (ofString "hp") = some (.val (.word (h + n))) ∧ s'.memory = s.memory ∧
      s'.memaddrs = s.memaddrs ∧ s'.code = s.code ∧ s'.topAddr = s.topAddr := by
  have hne : ofString "n" ≠ ofString "p" := by decide
  unfold allocChecked
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  simp only [evalHOLExact, hhp]
  simp [shapeOfHOLExact, shapeEqHOL]
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  simp [evalHOLExact, evalListHOLExact, setVarHOLFinite, FUPDATE, Ne.symm hne, hn, hhp, wordOpHOL,
    wordOp, valueIsWord, valueWord, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hfit]
  simp [evalHOLExact, isValidValueHOLExact, lookupKvarHOLExact, setKvarHOLFinite, setGlobalHOLFinite,
    shapeOfHOLExact, shapeEqHOL, emptyLocalsHOLFinite, FUPDATE, hhp]
