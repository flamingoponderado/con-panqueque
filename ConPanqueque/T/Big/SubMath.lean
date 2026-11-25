import ConPanqueque.T.Big.AddMath

/-!
# The arithmetic of a borrow chain

For `y ≤ x`: the borrow into limb `i` is `[x % B^i < y % B^i]`; limb `i` of `x - y` and the next borrow
follow from the two limbs and the borrow. `subb_words` is the 64-bit subtract-with-borrow, branch-free.
-/

namespace ConPanqueque.T.Big

def bor (x y i : Nat) : Nat := if x % B ^ i < y % B ^ i then 1 else 0

theorem bor_le (x y i : Nat) : bor x y i ≤ 1 := by unfold bor; split <;> omega

theorem bor_zero (x y : Nat) : bor x y 0 = 0 := by simp [bor, Nat.mod_one]

/-- The low part of the difference, borrowed up. -/
theorem low_eq (x y i : Nat) :
    x % B ^ i + B ^ i * bor x y i = y % B ^ i + (x % B ^ i + B ^ i * bor x y i - y % B ^ i) ∧
    x % B ^ i + B ^ i * bor x y i - y % B ^ i < B ^ i := by
  have hx := Nat.mod_lt x (pow_pos' i)
  have hy := Nat.mod_lt y (pow_pos' i)
  unfold bor
  generalize x % B ^ i = a at *
  generalize y % B ^ i = b at *
  generalize B ^ i = P at *
  split
  · rename_i h; simp only [Nat.mul_one]; constructor <;> omega
  · rename_i h; simp only [Nat.mul_zero, Nat.add_zero]; constructor <;> omega

theorem bor_succ (x y i : Nat) :
    bor x y (i + 1) = if x / B ^ i % B < y / B ^ i % B + bor x y i then 1 else 0 := by
  have ex := @Nat.mod_pow_succ x B i
  have ey := @Nat.mod_pow_succ y B i
  have hx := Nat.mod_lt x (pow_pos' i)
  have hy := Nat.mod_lt y (pow_pos' i)
  have hdx := Nat.mod_lt (x / B ^ i) Bpos
  have hdy := Nat.mod_lt (y / B ^ i) Bpos
  have hb := bor_le x y i
  unfold bor at hb ⊢
  rw [ex, ey]
  generalize x % B ^ i = a at *
  generalize y % B ^ i = b at *
  generalize x / B ^ i % B = dx at *
  generalize y / B ^ i % B = dy at *
  generalize hP : B ^ i = P at *
  by_cases h1 : a < b
  · simp only [h1, ite_true] at hb ⊢
    by_cases h2 : dx < dy + 1
    · have : a + P * dx < b + P * dy := by
        have : P * dx ≤ P * dy := Nat.mul_le_mul_left _ (by omega)
        omega
      rw [ite_eq_left this, ite_eq_left h2]
    · have : ¬ a + P * dx < b + P * dy := by
        have : P * (dy + 1) ≤ P * dx := Nat.mul_le_mul_left _ (by omega)
        rw [Nat.mul_succ] at this; omega
      rw [ite_eq_right this, ite_eq_right h2]
  · simp only [h1, ite_false] at hb ⊢
    by_cases h2 : dx < dy + 0
    · have : a + P * dx < b + P * dy := by
        have : P * (dx + 1) ≤ P * dy := Nat.mul_le_mul_left _ (by omega)
        rw [Nat.mul_succ] at this; omega
      rw [ite_eq_left this, ite_eq_left h2]
    · have : ¬ a + P * dx < b + P * dy := by
        have : P * dy ≤ P * dx := Nat.mul_le_mul_left _ (by omega)
        omega
      rw [ite_eq_right this, ite_eq_right h2]

theorem sub_div (x y i : Nat) (hxy : y ≤ x) :
    (x - y) / B ^ i = x / B ^ i - y / B ^ i - bor x y i := by
  obtain ⟨e1, e2⟩ := low_eq x y i
  have ex := Nat.div_add_mod x (B ^ i)
  have ey := Nat.div_add_mod y (B ^ i)
  generalize hT : x % B ^ i + B ^ i * bor x y i - y % B ^ i = T at e1 e2
  have hb := bor_le x y i
  have hge : y / B ^ i + bor x y i ≤ x / B ^ i := by
    refine Nat.le_of_not_lt (fun hc => ?_)
    have : x / B ^ i + 1 ≤ y / B ^ i + bor x y i := by omega
    have h3 : B ^ i * (x / B ^ i + 1) ≤ B ^ i * (y / B ^ i + bor x y i) := Nat.mul_le_mul_left _ this
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one] at h3
    omega
  have : x - y = T + B ^ i * (x / B ^ i - y / B ^ i - bor x y i) := by
    rw [Nat.mul_sub, Nat.mul_sub]
    have h4 : B ^ i * (y / B ^ i) + B ^ i * bor x y i ≤ B ^ i * (x / B ^ i) := by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hge
    omega
  rw [this, add_div_pow, Nat.div_eq_of_lt e2, Nat.zero_add]

theorem sub_digit (x y i : Nat) (hxy : y ≤ x) :
    (x - y) / B ^ i % B = (x / B ^ i % B + B - y / B ^ i % B - bor x y i) % B := by
  rw [sub_div x y i hxy]
  have hb := bor_le x y i
  have hge : y / B ^ i + bor x y i ≤ x / B ^ i := by
    refine Nat.le_of_not_lt (fun hc => ?_)
    obtain ⟨e1, e2⟩ := low_eq x y i
    have ex := Nat.div_add_mod x (B ^ i)
    have ey := Nat.div_add_mod y (B ^ i)
    have : x / B ^ i + 1 ≤ y / B ^ i + bor x y i := by omega
    have h3 : B ^ i * (x / B ^ i + 1) ≤ B ^ i * (y / B ^ i + bor x y i) := Nat.mul_le_mul_left _ this
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one] at h3
    omega
  generalize x / B ^ i = X at *
  generalize y / B ^ i = Y at *
  generalize bor x y i = b at *
  have hB : B = 18446744073709551616 := rfl
  rw [hB]
  omega

/-- The 64-bit subtract-with-borrow, branch-free. -/
theorem subb_words (dx dy b : Nat) (hdx : dx < B) (hdy : dy < B) (hb : b ≤ 1) :
    BitVec.ofNat 64 dx - BitVec.ofNat 64 dy - BitVec.ofNat 64 b = BitVec.ofNat 64 ((dx + B - dy - b) % B) ∧
    (if BitVec.ofNat 64 dx < BitVec.ofNat 64 dy then (1 : BitVec 64) else 0) +
      (if BitVec.ofNat 64 dx - BitVec.ofNat 64 dy < BitVec.ofNat 64 b then (1 : BitVec 64) else 0) =
      BitVec.ofNat 64 (if dx < dy + b then 1 else 0) := by
  have hB : B = 18446744073709551616 := rfl
  rw [hB] at hdx hdy ⊢
  constructor
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdx, Nat.mod_eq_of_lt hdy,
      Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega)]
    omega
  · simp only [BitVec.lt_def, BitVec.toNat_sub, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hdx, Nat.mod_eq_of_lt hdy,
      Nat.mod_eq_of_lt (show b < 2 ^ 64 by omega)]
    by_cases h1 : dx < dy
    · have e : (2 ^ 64 - dy + dx) % 2 ^ 64 = 2 ^ 64 - dy + dx := by omega
      rw [e]
      simp [h1, show dx < dy + b by omega, show ¬ 2 ^ 64 - dy + dx < b by omega]
    · have e : (2 ^ 64 - dy + dx) % 2 ^ 64 = dx - dy := by omega
      rw [e]
      by_cases h2 : dx - dy < b
      · simp [h1, h2, show dx < dy + b by omega]
      · simp [h1, h2, show ¬ dx < dy + b by omega]

end ConPanqueque.T.Big
