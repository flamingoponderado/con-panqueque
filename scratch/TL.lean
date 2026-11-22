import ConPanqueque.Table
open Flapjack ConPanqueque.Table

namespace ConPanqueque.Table

theorem insSlots_length (k v : BitVec 64) : ∀ (slots sl' : List (BitVec 64 × BitVec 64)),
    insSlots k v slots = some sl' → sl'.length = slots.length
  | [], _, h => by simp [insSlots] at h
  | (k1, v1) :: rest, sl', h => by
    simp only [insSlots] at h
    split at h
    · cases h; simp
    · cases e : insSlots k v rest with
      | none => simp [e] at h
      | some r => simp [e] at h; subst h; simp [insSlots_length k v rest r e]

theorem find?_mem (k v : BitVec 64) : ∀ (slots : List (BitVec 64 × BitVec 64)),
    find? slots k = some v → (k, v) ∈ slots
  | [], h => by simp [find?] at h
  | (k1, v1) :: rest, h => by
    simp only [find?, List.find?] at h
    by_cases e : k1 = k
    · simp [e] at h; subst e; subst h; simp
    · simp [e] at h
      have := find?_mem k v rest (by simpa [find?] using h)
      simp [this]

end ConPanqueque.Table
