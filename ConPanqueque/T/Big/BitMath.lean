import ConPanqueque.T.Big.MulRow

/-!
# Bitwise operations, limb by limb

For `f ∈ {land, lor, xor}` the `k`-th limb of `f a b` is `f` of the `k`-th limbs (bit extensionality), and on
words the operation is the same one.
-/

namespace ConPanqueque.T.Big

inductive BitOp | and | or | xor
  deriving DecidableEq

def BitOp.f : BitOp → Nat → Nat → Nat
  | .and => Nat.land | .or => Nat.lor | .xor => Nat.xor

theorem BitOp.testBit_f (o : BitOp) (a b i : Nat) : (o.f a b).testBit i =
    match o with
    | .and => a.testBit i && b.testBit i
    | .or => a.testBit i || b.testBit i
    | .xor => a.testBit i ^^ b.testBit i := by
  cases o
  · exact Nat.testBit_and a b i
  · exact Nat.testBit_or a b i
  · exact Nat.testBit_xor a b i

theorem testBit_dg (n k j : Nat) (hj : j < 64) : (dg n k).testBit j = n.testBit (64 * k + j) := by
  unfold dg
  have hB : B = 2 ^ 64 := rfl
  rw [hB, ← Nat.pow_mul, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
  simp only [hj, decide_true, Bool.true_and]
  congr 1; omega

theorem BitOp.dg_f (o : BitOp) (a b k : Nat) : dg (o.f a b) k = o.f (dg a k) (dg b k) := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 64
  · rw [testBit_dg _ _ _ hj, BitOp.testBit_f, BitOp.testBit_f, testBit_dg _ _ _ hj, testBit_dg _ _ _ hj]
  · have h1 : dg (o.f a b) k < 2 ^ j := by
      unfold dg; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ Bpos) (Nat.pow_le_pow_right (by decide) (by omega))
    have h2 : dg a k < 2 ^ j := by
      unfold dg; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ Bpos) (Nat.pow_le_pow_right (by decide) (by omega))
    have h3 : dg b k < 2 ^ j := by
      unfold dg; exact Nat.lt_of_lt_of_le (Nat.mod_lt _ Bpos) (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.testBit_lt_two_pow h1, BitOp.testBit_f, Nat.testBit_lt_two_pow h2, Nat.testBit_lt_two_pow h3]
    cases o <;> rfl

theorem BitOp.lt (o : BitOp) (a b n : Nat) (ha : a < 2 ^ n) (hb : b < 2 ^ n) : o.f a b < 2 ^ n := by
  cases o
  · exact Nat.lt_of_le_of_lt Nat.and_le_left ha
  · exact Nat.or_lt_two_pow ha hb
  · exact Nat.xor_lt_two_pow ha hb

theorem BitOp.zero (o : BitOp) (a : Nat) : o.f a 0 = if o = .and then 0 else a := by
  cases o <;> simp [BitOp.f]

end ConPanqueque.T.Big
