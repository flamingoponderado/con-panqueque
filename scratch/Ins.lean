import ConPanqueque.Table
open Flapjack ConPanqueque.Table

namespace ConPanqueque.Table

/-- Insert `(k, v)` into the first slot holding `k` or empty (key `0`); `none` if full. -/
def insSlots (k v : BitVec 64) : List (BitVec 64 × BitVec 64) → Option (List (BitVec 64 × BitVec 64))
  | [] => none
  | (k', v') :: rest =>
    if k' = k ∨ k' = 0 then some ((k, v) :: rest)
    else (insSlots k v rest).map ((k', v') :: ·)

theorem find?_ins (k v : BitVec 64) (hk : k ≠ 0) :
    ∀ (slots slots' : List (BitVec 64 × BitVec 64)), insSlots k v slots = some slots' →
      find? slots' k = some v ∧ ∀ k', k' ≠ k → k' ≠ 0 → find? slots' k' = find? slots k'
  | [], _, h => by simp [insSlots] at h
  | (k1, v1) :: rest, slots', h => by
    simp only [insSlots] at h
    split at h
    · rename_i hc
      cases h
      refine ⟨by simp [find?, List.find?], fun k' hk' hk0 => ?_⟩
      rcases hc with rfl | rfl
      · simp [find?, List.find?, Ne.symm hk', hk']
      · simp [find?, List.find?, Ne.symm hk', show ¬ (0#64 = k') from fun e => hk0 e.symm]
    · rename_i hc
      simp only [not_or] at hc
      cases e : insSlots k v rest with
      | none => simp [e] at h
      | some r =>
        simp [e] at h; subst h
        obtain ⟨h1, h2⟩ := find?_ins k v hk rest r e
        refine ⟨by simpa [find?, List.find?, hc.1] using h1, fun k' hk' hk0 => ?_⟩
        by_cases e1 : k1 = k'
        · subst e1; simp [find?, List.find?]
        · simpa [find?, List.find?, e1] using h2 k' hk' hk0

end ConPanqueque.Table
