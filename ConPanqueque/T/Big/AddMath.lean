import ConPanqueque.T.Big.Limbs

/-!
# The arithmetic of a carry chain

`S i = x % B^i + y % B^i` is the sum of the low `i` limbs; its carry `S i / B^i` is `0` or `1`; limb `i` of
`x + y` and the next carry follow from the two limbs and the carry. The word lemma `addc_words` is the
64-bit add-with-carry the loop computes, branch-free.
-/

namespace ConPanqueque.T.Big

def S (x y i : Nat) : Nat := x % B ^ i + y % B ^ i

theorem Bpos : 0 < B := by decide

theorem pow_pos' (i : Nat) : 0 < B ^ i := Nat.pow_pos Bpos

theorem S_lt (x y i : Nat) : S x y i < 2 * B ^ i := by
  unfold S
  have := Nat.mod_lt x (pow_pos' i)
  have := Nat.mod_lt y (pow_pos' i)
  omega

theorem carry_le (x y i : Nat) : S x y i / B ^ i ≤ 1 := by
  have h := S_lt x y i
  have := Nat.div_lt_of_lt_mul (show S x y i < B ^ i * 2 by rw [Nat.mul_comm]; exact h)
  omega

theorem S_succ (x y i : Nat) : S x y (i + 1) = S x y i + B ^ i * (x / B ^ i % B + y / B ^ i % B) := by
  unfold S
  rw [@Nat.mod_pow_succ x B i, @Nat.mod_pow_succ y B i, Nat.mul_add]
  ac_rfl

theorem add_div_pow (a m i : Nat) : (a + B ^ i * m) / B ^ i = a / B ^ i + m := by
  rw [Nat.add_comm, Nat.mul_add_div (pow_pos' i), Nat.add_comm]

/-- The next carry. -/
theorem carry_succ (x y i : Nat) :
    S x y (i + 1) / B ^ (i + 1) = (x / B ^ i % B + y / B ^ i % B + S x y i / B ^ i) / B := by
  rw [S_succ, Nat.pow_succ, ← Nat.div_div_eq_div_mul, add_div_pow]
  congr 1; omega

/-- The sum of everything above limb `i`. -/
theorem sum_div (x y i : Nat) : (x + y) / B ^ i = S x y i / B ^ i + x / B ^ i + y / B ^ i := by
  have ex := Nat.div_add_mod x (B ^ i)
  have ey := Nat.div_add_mod y (B ^ i)
  have : x + y = S x y i + B ^ i * (x / B ^ i + y / B ^ i) := by
    unfold S; rw [Nat.mul_add]
    generalize B ^ i * (x / B ^ i) = p at ex ⊢
    generalize B ^ i * (y / B ^ i) = q at ey ⊢
    omega
  rw [this, add_div_pow]; omega

/-- Limb `i` of the sum. -/
theorem sum_digit (x y i : Nat) :
    (x + y) / B ^ i % B = (x / B ^ i % B + y / B ^ i % B + S x y i / B ^ i) % B := by
  rw [sum_div]
  generalize S x y i / B ^ i = c
  generalize x / B ^ i = X
  generalize y / B ^ i = Y
  have hB : B = 18446744073709551616 := rfl
  rw [hB]
  omega

theorem S_full (x y n : Nat) (hx : x < B ^ n) (hy : y < B ^ n) : S x y n = x + y := by
  unfold S; rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

theorem S_zero (x y : Nat) : S x y 0 = 0 := by unfold S; simp [Nat.mod_one]

/-- The 64-bit add-with-carry, branch-free. -/
theorem addc_words (dx dy c : Nat) (hdx : dx < B) (hdy : dy < B) (hc : c ≤ 1) :
    BitVec.ofNat 64 dx + BitVec.ofNat 64 dy + BitVec.ofNat 64 c = BitVec.ofNat 64 ((dx + dy + c) % B) ∧
    (if BitVec.ofNat 64 dx + BitVec.ofNat 64 dy < BitVec.ofNat 64 dx then (1 : BitVec 64) else 0) +
      (if BitVec.ofNat 64 dx + BitVec.ofNat 64 dy + BitVec.ofNat 64 c < BitVec.ofNat 64 dx + BitVec.ofNat 64 dy
        then (1 : BitVec 64) else 0) = BitVec.ofNat 64 ((dx + dy + c) / B) := by
  have hB : B = 18446744073709551616 := rfl
  rw [hB] at hdx hdy ⊢
  constructor
  · apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add, Nat.mod_eq_of_lt hdx, Nat.mod_eq_of_lt hdy, Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)]
  · simp only [BitVec.lt_def, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdx, Nat.mod_eq_of_lt hdy,
      Nat.mod_eq_of_lt (show c < 2 ^ 64 by omega)]
    by_cases h1 : dx + dy < 2 ^ 64
    · rw [Nat.mod_eq_of_lt h1]
      by_cases h2 : dx + dy + c < 2 ^ 64
      · rw [Nat.mod_eq_of_lt h2]
        have : (dx + dy + c) / 18446744073709551616 = 0 := Nat.div_eq_of_lt h2
        simp [show ¬ dx + dy < dx by omega, show ¬ dx + dy + c < dx + dy by omega, this]
      · have e : (dx + dy + c) % 2 ^ 64 = dx + dy + c - 2 ^ 64 := by omega
        rw [e]
        have : (dx + dy + c) / 18446744073709551616 = 1 := by omega
        simp [show ¬ dx + dy < dx by omega, show dx + dy + c - 2 ^ 64 < dx + dy by omega, this]
    · have e : (dx + dy) % 2 ^ 64 = dx + dy - 2 ^ 64 := by omega
      rw [e]
      have e2 : (dx + dy - 2 ^ 64 + c) % 2 ^ 64 = dx + dy - 2 ^ 64 + c := by omega
      rw [e2]
      have : (dx + dy + c) / 18446744073709551616 = 1 := by omega
      simp [show dx + dy - 2 ^ 64 < dx by omega, show ¬ dx + dy - 2 ^ 64 + c < dx + dy - 2 ^ 64 by omega, this]

end ConPanqueque.T.Big
