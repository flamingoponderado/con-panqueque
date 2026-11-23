import ConPanqueque.T.Big.ShiftMath

/-!
# Restoring division of a word

After `i` steps the remainder and quotient are those of the top `i` bits of `x` (`x >>> (64 - i)`) by `y`.
A step doubles the remainder and brings the next bit in; it subtracts `y` exactly when the doubled
remainder reaches `y` — which the word code detects from the bit shifted out and a comparison.
-/

namespace ConPanqueque.T.Big

def topBits (x i : Nat) : Nat := x / 2 ^ (64 - i)

theorem topBits_succ (x i : Nat) (hi : i < 64) :
    topBits x (i + 1) = 2 * topBits x i + x / 2 ^ (63 - i) % 2 := by
  unfold topBits
  have e : 64 - i = (63 - i) + 1 := by omega
  rw [e, Nat.pow_succ, ← Nat.div_div_eq_div_mul, show 64 - (i + 1) = 63 - i by omega]
  have := Nat.div_add_mod (x / 2 ^ (63 - i)) 2
  omega

theorem divmod_step (T y : Nat) (bit : Nat) (hy : 0 < y) (hb : bit < 2) :
    (2 * T + bit) / y = 2 * (T / y) + (if y ≤ 2 * (T % y) + bit then 1 else 0) ∧
    (2 * T + bit) % y = 2 * (T % y) + bit - (if y ≤ 2 * (T % y) + bit then y else 0) := by
  have hT := Nat.div_add_mod T y
  have hm := Nat.mod_lt T hy
  generalize T / y = Q at hT
  generalize T % y = R at hT hm
  subst hT
  have e : 2 * (y * Q + R) + bit = y * (2 * Q) + (2 * R + bit) := by ring
  rw [e]
  by_cases h : y ≤ 2 * R + bit
  · rw [if_pos h, if_pos h]
    have e2 : y * (2 * Q) + (2 * R + bit) = y * (2 * Q + 1) + (2 * R + bit - y) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    rw [e2, Nat.mul_add_div hy, Nat.mul_add_mod, Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    constructor <;> omega
  · rw [if_neg h, if_neg h, Nat.mul_add_div hy, Nat.mul_add_mod, Nat.div_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    constructor <;> omega

end ConPanqueque.T.Big
