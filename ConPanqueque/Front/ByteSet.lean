import ConPanqueque.Logic.Byte
import Flapjack.Pancake.Semantics.PanSemStateEval

/-! # A byte store inside a word

`panSetByteHOL a v cell false` (little-endian, 64-bit) replaces byte `a % 8` of `cell` with
`v % 256` and keeps the other bytes (`byteW_setByte`). -/

namespace ConPanqueque.Front

open ConPanqueque.Logic Flapjack

theorem digit_eq (low d high i : Nat) (hl : low < 256 ^ i) (hd : d < 256) :
    (low + d * 256 ^ i + high * (256 ^ i * 256)) / 256 ^ i % 256 = d := by
  have hp : 0 < 256 ^ i := Nat.pow_pos (by decide)
  have : (low + d * 256 ^ i + high * (256 ^ i * 256)) / 256 ^ i = d + high * 256 := by
    rw [show low + d * 256 ^ i + high * (256 ^ i * 256) = low + 256 ^ i * (d + high * 256) by rw [Nat.mul_comm (256 ^ i) (d + high * 256), Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 256 (256 ^ i), Nat.add_assoc]]
    rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hl, Nat.zero_add]
  rw [this, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hd]

theorem pow256_split (k j : Nat) : 256 ^ (k + j) = 256 ^ k * 256 ^ j := Nat.pow_add 256 k j

/-- Truncation to 64 bits keeps the low 8 bytes. -/
theorem mod64_digit (X k : Nat) (hk : k < 8) : X % 2 ^ 64 / 256 ^ k % 256 = X / 256 ^ k % 256 := by
  have e : (2 : Nat) ^ 64 = 256 ^ k * 256 ^ (8 - k) := by
    rw [← Nat.pow_add, show k + (8 - k) = 8 by omega]
  rw [e, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  exact Nat.dvd_of_mod_eq_zero (by rw [show 8 - k = (8 - k - 1) + 1 by omega, Nat.pow_succ, Nat.mul_mod_left])

/-- The digits of `low + 256^i * (d + 256 * high)` below `i` are `low`'s. -/
theorem digit_below (low d high i k : Nat) (hki : k < i) :
    (low + 256 ^ i * (d + 256 * high)) / 256 ^ k % 256 = low / 256 ^ k % 256 := by
  have hp : 0 < 256 ^ k := Nat.pow_pos (by decide)
  have e : 256 ^ i = 256 ^ k * 256 ^ (i - k) := by rw [← Nat.pow_add, show k + (i - k) = i by omega]
  rw [e, Nat.mul_assoc, Nat.add_mul_div_left _ _ hp]
  have : (256 : Nat) ∣ 256 ^ (i - k) * (d + 256 * high) := Nat.dvd_mul_right_of_dvd (Nat.dvd_of_mod_eq_zero (by
    rw [show i - k = (i - k - 1) + 1 by omega, Nat.pow_succ, Nat.mul_mod_left])) _
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd this, Nat.add_zero, Nat.mod_mod]

theorem digit_above (low d high i k : Nat) (hl : low < 256 ^ i) (hd : d < 256) (hik : i < k) :
    (low + 256 ^ i * (d + 256 * high)) / 256 ^ k = high / 256 ^ (k - i - 1) := by
  have hp : 0 < 256 ^ (i + 1) := Nat.pow_pos (by decide)
  have e1 : low + 256 ^ i * (d + 256 * high) = (low + 256 ^ i * d) + 256 ^ (i + 1) * high := by
    rw [Nat.mul_add, Nat.pow_succ, Nat.mul_assoc, Nat.add_assoc]
  have hb : low + 256 ^ i * d < 256 ^ (i + 1) := by
    rw [Nat.pow_succ]
    have : 256 ^ i * d + 256 ^ i ≤ 256 ^ i * 256 := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hd
    omega
  have e2 : 256 ^ k = 256 ^ (i + 1) * 256 ^ (k - i - 1) := by rw [← Nat.pow_add, show i + 1 + (k - i - 1) = k by omega]
  rw [e1, e2, ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hb, Nat.zero_add]

theorem byteW_below (cell i k : Nat) (hki : k < i) : cell % 256 ^ i / 256 ^ k % 256 = cell / 256 ^ k % 256 := by
  have e : 256 ^ i = 256 ^ k * 256 ^ (i - k) := by rw [← Nat.pow_add, show k + (i - k) = i by omega]
  rw [e, Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd]
  exact Nat.dvd_of_mod_eq_zero (by rw [show i - k = (i - k - 1) + 1 by omega, Nat.pow_succ, Nat.mul_mod_left])

theorem byteW_above (cell i k : Nat) (hik : i < k) : cell / (256 ^ i * 256) / 256 ^ (k - i - 1) = cell / 256 ^ k := by
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ, ← Nat.pow_add, show i + 1 + (k - i - 1) = k by omega]

/-- **A byte store sets one byte of the word.** -/
theorem byteW_setByte (a v cell : BitVec 64) (k : Nat) (hk : k < 8) :
    byteW (panSetByteHOL a v cell false) k = if k = a.toNat % 8 then v.toNat % 256 else byteW cell k := by
  unfold panSetByteHOL byteW
  simp only [show (64 : Nat) / 8 = 8 from rfl, Bool.false_eq_true, ↓reduceIte, BitVec.toNat_ofNat]
  rw [mod64_digit _ _ hk]
  generalize hi : a.toNat % 8 = i
  have hi8 : i < 8 := by omega
  have hl : cell.toNat % 256 ^ i < 256 ^ i := Nat.mod_lt _ (Nat.pow_pos (by decide))
  have hd : v.toNat % 256 < 256 := Nat.mod_lt _ (by decide)
  have e : cell.toNat % 256 ^ i + v.toNat % 256 * 256 ^ i + cell.toNat / (256 ^ i * 256) * (256 ^ i * 256) =
      cell.toNat % 256 ^ i + 256 ^ i * (v.toNat % 256 + 256 * (cell.toNat / (256 ^ i * 256))) := by
    rw [Nat.mul_add, Nat.add_assoc, Nat.mul_comm (v.toNat % 256), Nat.mul_comm _ (256 ^ i * 256), Nat.mul_assoc]
  rw [e]
  rcases Nat.lt_trichotomy k i with h | rfl | h
  · rw [ite_eq_right (by omega), digit_below _ _ _ _ _ h, byteW_below _ _ _ h]
  · rw [ite_eq_left rfl]
    have := digit_eq (cell.toNat % 256 ^ k) (v.toNat % 256) (cell.toNat / (256 ^ k * 256)) k hl hd
    rw [← e]; exact this
  · rw [ite_eq_right (by omega), digit_above _ _ _ _ _ hl hd h, byteW_above _ _ _ h]

end ConPanqueque.Front
