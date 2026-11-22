import ConPanqueque.Table
open Flapjack ConPanqueque.Table

namespace ConPanqueque.Table

theorem insSlots_at (k v : BitVec 64) : ∀ (slots : List (BitVec 64 × BitVec 64)) (i : Nat) (hi : i < slots.length),
    (∀ m (hm : m < slots.length), m < i → slots[m].1 ≠ k ∧ slots[m].1 ≠ 0) →
    (slots[i].1 = k ∨ slots[i].1 = 0) → insSlots k v slots = some (slots.set i (k, v))
  | [], _, hi, _, _ => absurd hi (by simp)
  | (k1, v1) :: rest, 0, _, _, hc => by simp at hc; simp [insSlots, hc]
  | (k1, v1) :: rest, i + 1, hi, hb, hc => by
    have h0 := hb 0 (by simp) (by omega)
    simp at h0
    have := insSlots_at k v rest i (by simpa using hi)
      (fun m hm hmi => by have := hb (m + 1) (by simp; omega) (by omega); simpa using this)
      (by simpa using hc)
    simp [insSlots, h0, this]

theorem insSlots_none (k v : BitVec 64) : ∀ (slots : List (BitVec 64 × BitVec 64)),
    (∀ m (hm : m < slots.length), slots[m].1 ≠ k ∧ slots[m].1 ≠ 0) → insSlots k v slots = none
  | [], _ => rfl
  | (k1, v1) :: rest, hb => by
    have h0 := hb 0 (by simp)
    simp at h0
    have := insSlots_none k v rest (fun m hm => by have := hb (m + 1) (by simp; omega); simpa using this)
    simp [insSlots, h0, this]

theorem flat_set : ∀ (slots : List (BitVec 64 × BitVec 64)) (i : Nat) (k v : BitVec 64),
    ((slots.set i (k, v)).flatMap fun (k, v) => [HolWordLab.word k, .word v]) =
      (((slots.flatMap fun (k, v) => [HolWordLab.word k, .word v]).set (2 * i) (.word k)).set (2 * i + 1) (.word v))
  | [], _, _, _ => by simp
  | (k1, v1) :: rest, 0, k, v => by simp
  | (k1, v1) :: rest, i + 1, k, v => by
    have := flat_set rest i k v
    simp only [List.set_cons_succ, List.flatMap_cons, List.cons_append, List.nil_append, this]
    rw [show 2 * (i + 1) = 2 * i + 1 + 1 from by omega, show 2 * i + 1 + 1 + 1 = (2 * i + 1) + 1 + 1 from rfl]
    simp [List.set_cons_succ]

end ConPanqueque.Table
