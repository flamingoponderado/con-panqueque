import ConRon.Arena.Core
import ConRon.Bridge.Pers
import ConRon.Bridge.Rel
open ConRon.Arena ConRon.Bridge

/-!
# Twin facts: where returned level handles come from

A level handle a twin walk returns was read off a sort node of the final store, so it is valid there.
-/

namespace ConPanqueque.T.Comp

theorem viewSort_run (w : EIdx) (s : AState) :
    ConRon.Arena.viewSort w s = .ok (s.store.viewSort w, s) := rfl

/-- `formerSortLoop`'s level is a sort node's level in the final store. -/
theorem formerSortLoop_sort (r : CoreFnsA) : ∀ (n d : Nat) (e : EIdx) (s : AState) (u : LIdx) (s' : AState),
    formerSortLoop r d n e s = .ok (some u, s') → ∃ w, s'.store.view w = some (.sort u) := by
  intro n
  induction n with
  | zero =>
    intro d e s u s' h
    rw [formerSortLoop] at h
    obtain ⟨w, s1, -, h⟩ := AM.bind_ok h
    split at h
    · rename_i htg
      obtain ⟨o, s2, ho, h⟩ := AM.bind_ok h
      rw [viewSort_run] at ho
      cases ho
      cases hv : s1.store.viewSort w with
      | none => rw [hv] at h; exact absurd h AM.fail_ok
      | some x =>
        rw [hv] at h
        cases h
        exact ⟨w, view_of_viewSort_tag htg hv⟩
    · cases h
  | succ n ih =>
    intro d e s u s' h
    rw [formerSortLoop] at h
    obtain ⟨w, s1, -, h⟩ := AM.bind_ok h
    split at h
    · obtain ⟨o, s2, -, h⟩ := AM.bind_ok h
      rcases o with _ | ⟨dom, b⟩
      · exact absurd h AM.fail_ok
      · obtain ⟨fv, s3, -, h⟩ := AM.bind_ok h
        obtain ⟨b2, s4, -, h⟩ := AM.bind_ok h
        exact ih _ _ _ _ _ h
    · cases h

/-- `formerResSort`'s level is a sort node's level. -/
theorem formerResSort_sort (ty : EIdx) (s : AState) (u : LIdx) (s' : AState)
    (h : formerResSort ty s = .ok (some u, s')) : ∃ w, s'.store.view w = some (.sort u) := by
  rw [formerResSort] at h
  obtain ⟨pr, s1, -, h⟩ := AM.bind_ok h
  split at h
  · rename_i htg
    obtain ⟨o, s2, ho, h⟩ := AM.bind_ok h
    rw [viewSort_run] at ho
    cases ho
    cases hv : s1.store.viewSort pr with
    | none => rw [hv] at h; exact absurd h AM.fail_ok
    | some x =>
      rw [hv] at h
      cases h
      exact ⟨pr, view_of_viewSort_tag htg hv⟩
  · cases h

end ConPanqueque.T.Comp
