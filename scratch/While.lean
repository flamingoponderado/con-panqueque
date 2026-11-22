import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

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
