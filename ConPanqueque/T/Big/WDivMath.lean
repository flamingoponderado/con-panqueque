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

/-- The word code of one step: `c := r >>> 63; r' := (r <<< 1) + bit; ge := c ||| ((r' < y) ^^^ 1);
r'' := r' - ge * y`. -/
theorem wdiv_word (R y bit : Nat) (hR : R < y) (hy : y < B) (hb : bit < 2) :
    let r := BitVec.ofNat 64 R
    let yw := BitVec.ofNat 64 y
    let c := r >>> 63
    let r1 := (r <<< 1) + BitVec.ofNat 64 bit
    let ge := c ||| ((if r1 < yw then (1 : BitVec 64) else 0) ^^^ 1)
    ge = BitVec.ofNat 64 (if y ≤ 2 * R + bit then 1 else 0) ∧
      r1 - ge * yw = BitVec.ofNat 64 (2 * R + bit - (if y ≤ 2 * R + bit then y else 0)) := by
  intro r yw c r1 ge
  have hB : B = 2 ^ 64 := rfl
  rw [hB] at hy
  have hR2 : R < 2 ^ 64 := by omega
  have er1 : r1.toNat = (2 * R + bit) % 2 ^ 64 := by
    simp only [r1, r, BitVec.toNat_add, BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hR2,
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt (show bit < 2 ^ 64 by omega)]
    omega
  have ec : c.toNat = R / 2 ^ 63 := by
    simp only [c, r, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hR2, Nat.shiftRight_eq_div_pow]
  have eyw : yw.toNat = y := by simp only [yw, BitVec.toNat_ofNat]; omega
  have hlt : (r1 < yw) ↔ (2 * R + bit) % 2 ^ 64 < y := by rw [BitVec.lt_def, er1, eyw]
  have hc01 : c = 0 ∨ c = 1 := by
    rcases (by omega : R / 2 ^ 63 = 0 ∨ R / 2 ^ 63 = 1) with h | h
    · left; apply BitVec.eq_of_toNat_eq; rw [ec, h]; rfl
    · right; apply BitVec.eq_of_toNat_eq; rw [ec, h]; rfl
  have hge : ge = BitVec.ofNat 64 (if y ≤ 2 * R + bit then 1 else 0) := by
    simp only [ge]
    rcases hc01 with h | h
    · have hc0 : R / 2 ^ 63 = 0 := by rw [← ec, h]; rfl
      have hsm : (2 * R + bit) % 2 ^ 64 = 2 * R + bit := Nat.mod_eq_of_lt (by omega)
      rw [hsm] at hlt
      by_cases hq : y ≤ 2 * R + bit
      · rw [if_pos hq, if_neg (by rw [hlt]; omega), h]; decide
      · rw [if_neg hq, if_pos (by rw [hlt]; omega), h]; decide
    · have hc1 : R / 2 ^ 63 = 1 := by rw [← ec, h]; rfl
      rw [if_pos (by omega : y ≤ 2 * R + bit), h]
      split <;> decide
  refine ⟨hge, ?_⟩
  rw [hge]
  apply BitVec.eq_of_toNat_eq
  by_cases hq : y ≤ 2 * R + bit
  · rw [if_pos hq, if_pos hq]
    simp only [BitVec.toNat_sub, BitVec.toNat_mul, er1, eyw, BitVec.toNat_ofNat]
    rw [show (1 : Nat) % 2 ^ 64 = 1 from rfl, one_mul, Nat.mod_eq_of_lt (show y < 2 ^ 64 by omega)]
    omega
  · rw [if_neg hq, if_neg hq]
    simp only [BitVec.toNat_sub, BitVec.toNat_mul, er1, BitVec.toNat_ofNat]
    rw [show (0 : Nat) % 2 ^ 64 = 0 from rfl, zero_mul]
    omega

end ConPanqueque.T.Big
