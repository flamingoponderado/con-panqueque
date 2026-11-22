import ConPanqueque.Logic.Sep
open Flapjack Flapjack.PanSemStateFiniteExact
namespace ConPanqueque.Sep

theorem union_comm {h₁ h₂ : Heap} (hd : Disj h₁ h₂) : union h₁ h₂ = union h₂ h₁ := by
  funext a; rcases hd a with h | h <;> cases h₁ a <;> cases h₂ a <;> simp_all [union]

theorem sep_comm (P Q : Assn) (h : Heap) : (P ∗ Q) h → (Q ∗ P) h := by
  rintro ⟨h₁, h₂, hd, rfl, hp, hq⟩
  exact ⟨h₂, h₁, fun a => (hd a).symm, union_comm hd, hq, hp⟩

theorem sep_assoc (P Q R : Assn) (h : Heap) : ((P ∗ Q) ∗ R) h → (P ∗ (Q ∗ R)) h := by
  rintro ⟨h₁₂, h₃, hd, rfl, ⟨h₁, h₂, hd12, rfl, hp, hq⟩, hr⟩
  refine ⟨h₁, union h₂ h₃, ?_, ?_, hp, h₂, h₃, ?_, rfl, hq, hr⟩
  · intro a
    have := hd a; have := hd12 a
    cases e1 : h₁ a <;> cases e2 : h₂ a <;> cases e3 : h₃ a <;> simp_all [union]
  · funext a; cases e1 : h₁ a <;> cases e2 : h₂ a <;> simp [union, e1, e2]
  · intro a
    have := hd a
    cases e1 : h₁ a <;> cases e2 : h₂ a <;> simp_all [union]

/-- Satisfaction is affine: a conjunct may be forgotten. -/
theorem sat_sep_left {σ : Type} {s : PanSemStateFiniteExact 64 σ} {P Q : Assn}
    (hs : Sat s (P ∗ Q)) : Sat s P := by
  obtain ⟨h, ⟨h₁, h₂, _, rfl, hp, _⟩, hm⟩ := hs
  refine ⟨h₁, hp, fun a w ha => hm a w (by simp [union, ha])⟩

theorem sat_mono {σ : Type} {s : PanSemStateFiniteExact 64 σ} {P Q : Assn}
    (hpq : ∀ h, P h → Q h) (hs : Sat s P) : Sat s Q := by
  obtain ⟨h, hp, hm⟩ := hs; exact ⟨h, hpq h hp, hm⟩

end ConPanqueque.Sep
