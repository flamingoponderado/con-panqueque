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

/-- The free region: `[h, @top)` is in the memory domain, and `h ≤ @top`. -/
def Free {σ : Type} (s : PanSemStateFiniteExact 64 σ) (h : BitVec 64) : Prop :=
  h ≤ s.topAddr ∧ ∀ a : BitVec 64, h ≤ a → a < s.topAddr → s.memaddrs a

/-- A successful allocation of `n` bytes at `h`: the block `[h, h + n)` is in the
memory domain (and does not wrap around), and `[h + n, @top)` is free. -/
theorem alloc_fresh {σ : Type} (s : PanSemStateFiniteExact 64 σ) (h n : BitVec 64)
    (hf : Free s h) (hfit : ¬ s.topAddr - h < n) :
    h.toNat + n.toNat ≤ s.topAddr.toNat ∧
    (∀ a : BitVec 64, h ≤ a → a < h + n → s.memaddrs a) ∧ Free s (h + n) := by
  obtain ⟨hle, hdom⟩ := hf
  have hsum : h.toNat + n.toNat ≤ s.topAddr.toNat := by bv_omega
  refine ⟨hsum, fun a h1 h2 => hdom a h1 (by bv_omega), by bv_omega, fun a h1 h2 => hdom a (by bv_omega) h2⟩

end ConPanqueque.Alloc
