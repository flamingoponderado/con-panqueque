import ConPanqueque.T.Big.MulRow

/-!
# Shifts, limb by limb

`a >>> (64 q + r)`: limb `k` is limb `k + q` shifted down by `r` plus limb `k + q + 1` shifted up by `64 - r`
(mod `2^64`); the word code shifts up in two steps (`<<< 1` then `<<< (63 - r)`) so no shift reaches 64.
-/

namespace ConPanqueque.T.Big

theorem two_pow_split (r : Nat) (hr : r ≤ 64) : B = 2 ^ r * 2 ^ (64 - r) := by
  have hB : B = 2 ^ 64 := rfl
  rw [hB, ← Nat.pow_add]; congr 1; omega

/-- Limb `k` of a right shift. -/
theorem shr_digit (a q r k : Nat) (hr : r < 64) :
    dg (a / 2 ^ (64 * q + r)) k = (dg a (k + q) / 2 ^ r + dg a (k + q + 1) * 2 ^ (64 - r)) % B := by
  unfold dg
  have e1 : a / 2 ^ (64 * q + r) / B ^ k = a / B ^ (k + q) / 2 ^ r := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul]
    congr 1
    have hB : B = 2 ^ 64 := rfl
    rw [hB, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_add, ← Nat.pow_add]; congr 1; ring
  rw [e1]
  have hs := div_step a (k + q)
  generalize a / B ^ (k + q) = A at hs ⊢
  generalize a / B ^ (k + q + 1) = A1 at hs ⊢
  have hA1 := Nat.div_add_mod A1 B
  have hp := two_pow_split r (by omega)
  have hd0 := Nat.mod_lt A Bpos
  generalize A % B = d0 at hs hd0 ⊢
  generalize A1 % B = d1 at hA1 ⊢
  rw [hs]
  have : (B * A1 + d0) / 2 ^ r = A1 * 2 ^ (64 - r) + d0 / 2 ^ r := by
    rw [hp, show 2 ^ r * 2 ^ (64 - r) * A1 = 2 ^ r * (A1 * 2 ^ (64 - r)) by ring, Nat.mul_add_div (Nat.pow_pos (by decide))]
  rw [this]
  rw [← hA1]
  have : (B * (A1 / B) + d1) * 2 ^ (64 - r) = B * (A1 / B * 2 ^ (64 - r)) + d1 * 2 ^ (64 - r) := by ring
  rw [this]
  generalize A1 / B * 2 ^ (64 - r) = X
  generalize d1 * 2 ^ (64 - r) = Y
  generalize d0 / 2 ^ r = Z
  have hB : B = 18446744073709551616 := rfl
  rw [hB]
  omega

end ConPanqueque.T.Big
