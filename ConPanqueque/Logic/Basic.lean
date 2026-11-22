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

/-! ## Structural rules -/

/-- `p; q` after `p` finished normally is `q`. -/
theorem seq_normal {σ : Type} {s s₁ : PanSemStateFiniteExact 64 σ} {p : ProgHOL 64} (q : ProgHOL 64)
    (h : evaluateHOLFiniteState s p = (none, s₁)) :
    evaluateHOLFiniteState s (.seq p q) = evaluateHOLFiniteState s₁ q := by
  rw [evaluateHOLFiniteState_eq_evaluate_def s (.seq p q)]
  simp only [h]

/-- An assignment of an expression's value, when the value fits the variable. -/
theorem assign_ok {σ : Type} (s : PanSemStateFiniteExact 64 σ) (k : VarKind) (n : MlS)
    (e : ExpHOL 64) (v : ValueHOL 64)
    (he : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v)
    (hv : isValidValueHOLFinite s k n v = true) :
    evaluateHOLFiniteState s (.assign k n e) = (none, setKvarHOLFinite k n v s) := by
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  simp only [he, hv, ite_true]

/-! ## Locals -/

@[simp] theorem lookup_setVar_same {σ : Type} (s : PanSemStateFiniteExact 64 σ) (n : MlS)
    (v : ValueHOL 64) : (setVarHOLFinite n v s).locals.lookup n = some v := by
  simp [setVarHOLFinite, FUPDATE]

theorem lookup_setVar_other {σ : Type} (s : PanSemStateFiniteExact 64 σ) {n m : MlS}
    (v : ValueHOL 64) (h : m ≠ n) :
    (setVarHOLFinite n v s).locals.lookup m = s.locals.lookup m := by
  simp [setVarHOLFinite, FUPDATE, Ne.symm h]

/-! ## Loops -/

/-- Loop rule: an invariant `I` and a measure `m` bounded by the clock. While the
condition holds (a nonzero word), the body ends normally in a state satisfying `I`
with a smaller measure; when it is zero the loop ends normally. -/
theorem while_rule {σ : Type} (c : ExpHOL 64) (body : ProgHOL 64)
    (I : PanSemStateFiniteExact 64 σ → Prop) (m : PanSemStateFiniteExact 64 σ → Nat)
    (Q : PanSemStateFiniteExact 64 σ → Prop)
    (hc : ∀ s, I s → ∃ w : BitVec 64,
      @evalHOLFinite 64 σ _ s (fun a => Classical.propDecidable (s.memaddrs a)) c = some (.val (.word w)) ∧
      (w = 0 → Q s) ∧
      (w ≠ 0 → m s ≤ s.clock ∧ 0 < m s ∧ ∃ s', evaluateHOLFiniteState (decClockHOLFinite s) body = (none, s') ∧
        I s' ∧ m s' < m s)) :
    ∀ s, I s → ∃ s', evaluateHOLFiniteState s (.while c body) = (none, s') ∧ Q s' := by
  intro s hs
  induction h : m s using Nat.strongRecOn generalizing s with
  | _ n ih =>
    obtain ⟨w, hw, h0, h1⟩ := hc s hs
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.while c body)]
    by_cases hw0 : w = 0
    · subst hw0; simp only [hw]; exact ⟨s, by simp, h0 rfl⟩
    · obtain ⟨hclk, hpos, s', hb, hs', hlt⟩ := h1 hw0
      have hck : s.clock ≠ 0 := by omega
      simp only [hw, ne_eq, hw0, not_false_eq_true, ite_true, hck, ite_false, hb]
      exact ih (m s') (by omega) s' hs' rfl

/-! ## Memory -/

/-- A one-word store to an address in the memory domain. -/
theorem store_word {σ : Type} (s : PanSemStateFiniteExact 64 σ) (dst src : ExpHOL 64)
    (a w : BitVec 64)
    (hd : @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) dst =
      some (.val (.word a)))
    (hs : @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) src =
      some (.val (.word w)))
    (hdom : s.memaddrs a) :
    evaluateHOLFiniteState s (.store dst src) =
      (none, { s with memory := fun c => if c = a then .word w else s.memory c }) := by
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  simp [hd, hs, flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom]

/-- A one-word load from an address in the memory domain. -/
theorem eval_load_word {σ : Type} (s : PanSemStateFiniteExact 64 σ) (e : ExpHOL 64) (a : BitVec 64)
    (he : @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e =
      some (.val (.word a)))
    (hdom : s.memaddrs a) :
    @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) (.load .one e) =
      some (.val (s.memory a)) := by
  simp [evalHOLExact, he, memLoadHOLExact, hdom]

end ConPanqueque.Logic
