import ConPanqueque.Pipeline.IndExt.PosBase
import ConPanqueque.Pipeline.IndExt.Base

/-! # Constructor lists across a push

`CtorsAgree X₁ X₂` (a stored inductive's constructor names read alike on both sides) survives a
push of the same constants on both sides, when each pushed inductive lists only pushed names or
names neither side holds. -/

namespace ConPanqueque.Pipeline.IndExt

open ConLeche ConLeche.Verify ConPanqueque.Pipeline

set_option autoImplicit false

theorem find?_prepend_agree {R : List ConstantInfo} {X₁ X₂ : Env} (ts₁ ts₂ : List ProjTable) {n : Name}
    (h : n ∈ R.map (·.name) ∨ X₂.find? n = X₁.find? n) :
    Env.find? ⟨R ++ X₂.consts, ts₂⟩ n = Env.find? ⟨R ++ X₁.consts, ts₁⟩ n := by
  rw [find?_prepend, find?_prepend]
  rcases h with hm | he
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
    cases hr : R.find? (·.name == x.name) with
    | some c => rfl
    | none => rw [List.find?_eq_none] at hr; exact absurd (hr x hx) (by simp)
  · show (R.find? (·.name == n)).or (X₂.find? n) = (R.find? (·.name == n)).or (X₁.find? n)
    rw [he]

theorem ctorsAgree_prepend {X₁ X₂ : Env} (R : List ConstantInfo) (ts₁ ts₂ : List ProjTable)
    (hc : CtorsAgree X₁ X₂)
    (hR : ∀ c ∈ R, ∀ cv caps, c = .indInfo cv caps → ∀ n ∈ caps.ctors,
      n ∈ R.map (·.name) ∨ X₂.find? n = X₁.find? n) :
    CtorsAgree ⟨R ++ X₁.consts, ts₁⟩ ⟨R ++ X₂.consts, ts₂⟩ := by
  intro I cv caps hI n hn
  apply find?_prepend_agree
  rcases find?_prepend_mem hI with ⟨hm, -⟩ | ⟨hnI, h1⟩
  · exact hR _ hm cv caps rfl n hn
  · by_cases hm : n ∈ R.map (·.name)
    · exact Or.inl hm
    · exact Or.inr (hc I cv caps h1 n hn)

theorem ctorsAgree_empty (X : Env) : CtorsAgree Env.empty X := fun _ _ _ h => by
  simp [Env.empty, Env.find?] at h

end ConPanqueque.Pipeline.IndExt
