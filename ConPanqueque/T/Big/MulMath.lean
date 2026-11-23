import ConPanqueque.T.Big.SubMath
import Mathlib.Tactic.Ring

/-!
# The 64×64→128 multiply-accumulate

Pancake has the low half of a product only, so `a * b + r + c` (all below `2^64`) is assembled from the
four 32-bit half products: the middle sum's overflow and the low sum's carry go into the high word.
-/

namespace ConPanqueque.T.Big

theorem mul_halves (a b : Nat) :
    a * b = 2 ^ 64 * (a / 2 ^ 32 * (b / 2 ^ 32)) + 2 ^ 32 * (a % 2 ^ 32 * (b / 2 ^ 32) + a / 2 ^ 32 * (b % 2 ^ 32)) +
      a % 2 ^ 32 * (b % 2 ^ 32) := by
  conv_lhs => rw [← Nat.div_add_mod a (2 ^ 32), ← Nat.div_add_mod b (2 ^ 32)]
  ring

theorem half_mul_lt (x y : Nat) (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) : x * y < 2 ^ 64 := by
  calc x * y < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul'' hx hy
    _ = 2 ^ 64 := by norm_num

theorem toNat_lo32 (a : Nat) (ha : a < 2 ^ 64) :
    (BitVec.ofNat 64 a &&& 0xffffffff).toNat = a % 2 ^ 32 := by
  rw [BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]
  have : (0xffffffff : BitVec 64).toNat = 2 ^ 32 - 1 := rfl
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem toNat_hi32 (a : Nat) (ha : a < 2 ^ 64) : (BitVec.ofNat 64 a >>> 32).toNat = a / 2 ^ 32 := by
  rw [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.shiftRight_eq_div_pow]

/-- The multiply-accumulate words. -/
theorem mulw (a b r c : Nat) (ha : a < B) (hb : b < B) (hr : r < B) (hc : c < B) :
    let A := BitVec.ofNat 64 a
    let Bb := BitVec.ofNat 64 b
    let a0 := A &&& 0xffffffff
    let a1 := A >>> 32
    let b0 := Bb &&& 0xffffffff
    let b1 := Bb >>> 32
    let p00 := a0 * b0
    let p01 := a0 * b1
    let p10 := a1 * b0
    let p11 := a1 * b1
    let mid := p01 + p10
    let m1 : BitVec 64 := if mid < p01 then 1 else 0
    let lo1 := p00 + (mid <<< 32)
    let c1 : BitVec 64 := if lo1 < p00 then 1 else 0
    let hi1 := p11 + (mid >>> 32) + (m1 <<< 32) + c1
    let lo2 := lo1 + BitVec.ofNat 64 r
    let c2 : BitVec 64 := if lo2 < lo1 then 1 else 0
    let lo3 := lo2 + BitVec.ofNat 64 c
    let c3 : BitVec 64 := if lo3 < lo2 then 1 else 0
    let hi3 := hi1 + c2 + c3
    lo3 = BitVec.ofNat 64 ((a * b + r + c) % B) ∧ hi3 = BitVec.ofNat 64 ((a * b + r + c) / B) := by
  intro A Bb a0 a1 b0 b1 p00 p01 p10 p11 mid m1 lo1 c1 hi1 lo2 c2 lo3 c3 hi3
  have hB : B = 2 ^ 64 := rfl
  rw [hB] at ha hb hr hc ⊢
  -- the halves
  have ea0 : a0.toNat = a % 2 ^ 32 := toNat_lo32 a ha
  have ea1 : a1.toNat = a / 2 ^ 32 := toNat_hi32 a ha
  have eb0 : b0.toNat = b % 2 ^ 32 := toNat_lo32 b hb
  have eb1 : b1.toNat = b / 2 ^ 32 := toNat_hi32 b hb
  have la0 : a % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
  have lb0 : b % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
  have la1 : a / 2 ^ 32 < 2 ^ 32 := Nat.div_lt_of_lt_mul (by norm_num; omega)
  have lb1 : b / 2 ^ 32 < 2 ^ 32 := Nat.div_lt_of_lt_mul (by norm_num; omega)
  -- the half products
  have e00 : p00.toNat = a % 2 ^ 32 * (b % 2 ^ 32) := by
    simp only [p00, BitVec.toNat_mul, ea0, eb0]; exact Nat.mod_eq_of_lt (half_mul_lt _ _ la0 lb0)
  have e01 : p01.toNat = a % 2 ^ 32 * (b / 2 ^ 32) := by
    simp only [p01, BitVec.toNat_mul, ea0, eb1]; exact Nat.mod_eq_of_lt (half_mul_lt _ _ la0 lb1)
  have e10 : p10.toNat = a / 2 ^ 32 * (b % 2 ^ 32) := by
    simp only [p10, BitVec.toNat_mul, ea1, eb0]; exact Nat.mod_eq_of_lt (half_mul_lt _ _ la1 lb0)
  have e11 : p11.toNat = a / 2 ^ 32 * (b / 2 ^ 32) := by
    simp only [p11, BitVec.toNat_mul, ea1, eb1]; exact Nat.mod_eq_of_lt (half_mul_lt _ _ la1 lb1)
  have hab := mul_halves a b
  have l00 := half_mul_lt _ _ la0 lb0
  have l01 := half_mul_lt _ _ la0 lb1
  have l10 := half_mul_lt _ _ la1 lb0
  have l11 := half_mul_lt _ _ la1 lb1
  generalize a % 2 ^ 32 * (b % 2 ^ 32) = P00 at *
  generalize a % 2 ^ 32 * (b / 2 ^ 32) = P01 at *
  generalize a / 2 ^ 32 * (b % 2 ^ 32) = P10 at *
  generalize a / 2 ^ 32 * (b / 2 ^ 32) = P11 at *
  -- the middle sum and its overflow
  have emid : mid.toNat = (P01 + P10) % 2 ^ 64 := by simp only [mid, BitVec.toNat_add, e01, e10]
  have em1 : m1.toNat = (P01 + P10) / 2 ^ 64 := by
    simp only [m1, BitVec.lt_def, emid, e01]
    by_cases h : P01 + P10 < 2 ^ 64
    · rw [Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h]; simp
    · have e1 : (P01 + P10) % 2 ^ 64 = P01 + P10 - 2 ^ 64 := by omega
      have e2 : (P01 + P10) / 2 ^ 64 = 1 := by omega
      rw [e1, e2, if_pos (by omega)]; rfl
  -- the low sum and its carry
  have esh : (mid <<< 32).toNat = (P01 + P10) % 2 ^ 64 % 2 ^ 32 * 2 ^ 32 := by
    rw [BitVec.toNat_shiftLeft, emid, Nat.shiftLeft_eq]
    have hm := Nat.mod_lt (P01 + P10) (show 2 ^ 64 > 0 by norm_num)
    generalize (P01 + P10) % 2 ^ 64 = M at *
    have : M * 2 ^ 32 = (M / 2 ^ 32) * 2 ^ 64 + M % 2 ^ 32 * 2 ^ 32 := by
      have := Nat.div_add_mod M (2 ^ 32)
      calc M * 2 ^ 32 = (2 ^ 32 * (M / 2 ^ 32) + M % 2 ^ 32) * 2 ^ 32 := by rw [this]
        _ = (M / 2 ^ 32) * 2 ^ 64 + M % 2 ^ 32 * 2 ^ 32 := by ring
    rw [this, Nat.add_mod, Nat.mul_mod_left, Nat.zero_add, Nat.mod_mod]
    exact Nat.mod_eq_of_lt (by
      have := Nat.mod_lt M (show 2 ^ 32 > 0 by norm_num)
      calc M % 2 ^ 32 * 2 ^ 32 < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right this (by norm_num)
        _ = 2 ^ 64 := by norm_num)
  have hM := Nat.mod_lt (P01 + P10) (show 2 ^ 64 > 0 by norm_num)
  have em1v : (P01 + P10) / 2 ^ 64 ≤ 1 := by omega
  have esr : (mid >>> 32).toNat = (P01 + P10) % 2 ^ 64 / 2 ^ 32 := by
    rw [BitVec.toNat_ushiftRight, emid, Nat.shiftRight_eq_div_pow]
  have esm : (m1 <<< 32).toNat = (P01 + P10) / 2 ^ 64 * 2 ^ 32 := by
    rw [BitVec.toNat_shiftLeft, em1, Nat.shiftLeft_eq]
    exact Nat.mod_eq_of_lt (by
      rcases (by omega : (P01 + P10) / 2 ^ 64 = 0 ∨ (P01 + P10) / 2 ^ 64 = 1) with h | h <;> rw [h] <;> norm_num)
  have elo1 : lo1.toNat = (P00 + (P01 + P10) % 2 ^ 64 % 2 ^ 32 * 2 ^ 32) % 2 ^ 64 := by
    simp only [lo1, BitVec.toNat_add, e00, esh]
  have hsh : (P01 + P10) % 2 ^ 64 % 2 ^ 32 * 2 ^ 32 < 2 ^ 64 := by
    have := Nat.mod_lt ((P01 + P10) % 2 ^ 64) (show 2 ^ 32 > 0 by norm_num)
    calc (P01 + P10) % 2 ^ 64 % 2 ^ 32 * 2 ^ 32 < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right this (by norm_num)
      _ = 2 ^ 64 := by norm_num
  have ec1 : c1.toNat = (P00 + (P01 + P10) % 2 ^ 64 % 2 ^ 32 * 2 ^ 32) / 2 ^ 64 := by
    simp only [c1, BitVec.lt_def, elo1, e00]
    generalize (P01 + P10) % 2 ^ 64 % 2 ^ 32 * 2 ^ 32 = SH at hsh ⊢
    by_cases h : P00 + SH < 2 ^ 64
    · rw [Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h]; simp
    · have e1 : (P00 + SH) % 2 ^ 64 = P00 + SH - 2 ^ 64 := by omega
      have e2 : (P00 + SH) / 2 ^ 64 = 1 := by omega
      rw [e1, e2, if_pos (by omega)]; rfl
  -- the whole product
  have hab2 : a * b < 2 ^ 128 := by
    calc a * b < 2 ^ 64 * 2 ^ 64 := Nat.mul_lt_mul'' ha hb
      _ = 2 ^ 128 := by norm_num
  generalize a * b = AB at hab hab2 ⊢
  have hPm := Nat.div_add_mod (P01 + P10) (2 ^ 64)
  generalize (P01 + P10) % 2 ^ 64 = M at *
  generalize (P01 + P10) / 2 ^ 64 = m at *
  have hMd := Nat.div_add_mod M (2 ^ 32)
  generalize M / 2 ^ 32 = Mh at *
  generalize M % 2 ^ 32 = Ml at *
  generalize hSH : Ml * 2 ^ 32 = SH at esh elo1 hsh ec1
  have hL := Nat.div_add_mod (P00 + SH) (2 ^ 64)
  generalize (P00 + SH) / 2 ^ 64 = c1N at *
  generalize (P00 + SH) % 2 ^ 64 = LO1 at *
  -- the high word does not wrap
  have hHI : P11 + Mh + m * 2 ^ 32 + c1N < 2 ^ 64 := by omega
  have ehi1 : hi1.toNat = P11 + Mh + m * 2 ^ 32 + c1N := by
    rw [BitVec.toNat_add, BitVec.toNat_add, BitVec.toNat_add, e11, esr, esm, ec1]
    rw [Nat.mod_eq_of_lt (show P11 + Mh < 2 ^ 64 by omega), Nat.mod_eq_of_lt (show P11 + Mh + m * 2 ^ 32 < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt hHI]
  have hAB : AB = 2 ^ 64 * (P11 + Mh + m * 2 ^ 32 + c1N) + LO1 := by omega
  have hLO : LO1 < 2 ^ 64 := by omega
  -- adding the old digit and the carry
  constructor
  · apply BitVec.eq_of_toNat_eq
    simp only [lo3, lo2, BitVec.toNat_add, elo1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr, Nat.mod_eq_of_lt hc]
    omega
  · apply BitVec.eq_of_toNat_eq
    have el2 : lo2.toNat = (LO1 + r) % 2 ^ 64 := by
      simp only [lo2, BitVec.toNat_add, elo1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hr]
    have ec2 : c2.toNat = (LO1 + r) / 2 ^ 64 := by
      simp only [c2, BitVec.lt_def, el2, elo1]
      by_cases h : LO1 + r < 2 ^ 64
      · rw [Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h]; simp
      · rw [if_pos (by omega)]; show 1 = _; omega
    have el3 : lo3.toNat = ((LO1 + r) % 2 ^ 64 + c) % 2 ^ 64 := by
      simp only [lo3, BitVec.toNat_add, el2, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hc]
    have ec3 : c3.toNat = ((LO1 + r) % 2 ^ 64 + c) / 2 ^ 64 := by
      simp only [c3, BitVec.lt_def, el3, el2]
      by_cases h : (LO1 + r) % 2 ^ 64 + c < 2 ^ 64
      · rw [Nat.mod_eq_of_lt h, Nat.div_eq_of_lt h]; simp
      · rw [if_pos (by omega)]; show 1 = _; omega
    simp only [hi3, BitVec.toNat_add, ehi1, ec2, ec3, BitVec.toNat_ofNat]
    omega

end ConPanqueque.T.Big
