import ConPanqueque.V.Enc

/-!
# Limb arithmetic

Facts about `Enc.limbs` (canonical little-endian base-`2^64` digits) that the bignum loops use: the
length of a number's limbs, its `i`-th limb, and comparison from the top limb down.
-/

namespace ConPanqueque.T.Big

open ConPanqueque.V.Enc

abbrev B : Nat := 2 ^ 64

theorem limbs_zero : limbs 0 = [] := by unfold limbs; simp

theorem limbs_pos {n : Nat} (h : n ≠ 0) : limbs n = BitVec.ofNat 64 (n % B) :: limbs (n / B) := by
  conv => lhs; unfold limbs
  simp [h]

/-- The number of limbs: `0` for `0`, else one more than for `n / 2^64`. -/
theorem limbs_length_lt_iff (n k : Nat) : (limbs n).length ≤ k ↔ n < B ^ k := by
  induction k generalizing n with
  | zero =>
    by_cases h : n = 0
    · subst h; simp [limbs_zero]
    · rw [limbs_pos h]; simp; omega
  | succ k ih =>
    by_cases h : n = 0
    · subst h; simp [limbs_zero]; exact Nat.pow_pos (by decide)
    · rw [limbs_pos h, List.length_cons, Nat.add_le_add_iff_right, ih, Nat.pow_succ]
      constructor
      · intro h1
        have := Nat.div_add_mod n B
        calc n = B * (n / B) + n % B := this.symm
          _ < B * (n / B) + B := by have := Nat.mod_lt n (show B > 0 by decide); omega
          _ = B * (n / B + 1) := by rw [Nat.mul_succ]
          _ ≤ B * B ^ k := Nat.mul_le_mul_left _ h1
          _ = B ^ k * B := Nat.mul_comm _ _
      · intro h1
        exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h1)

theorem lt_of_length_lt {a b : Nat} (h : (limbs a).length < (limbs b).length) : a < b := by
  have h1 := (limbs_length_lt_iff a (limbs a).length).mp (Nat.le_refl _)
  have h2 : ¬ (limbs b).length ≤ (limbs a).length := by omega
  rw [limbs_length_lt_iff] at h2
  omega

/-- The `i`-th limb. -/
theorem limbs_getElem? (n i : Nat) :
    (limbs n)[i]? = if n / B ^ i = 0 then none else some (BitVec.ofNat 64 (n / B ^ i % B)) := by
  induction i generalizing n with
  | zero =>
    by_cases h : n = 0
    · subst h; simp [limbs_zero]
    · rw [limbs_pos h]; simp [h]
  | succ i ih =>
    by_cases h : n = 0
    · subst h; simp [limbs_zero]
    · rw [limbs_pos h, List.getElem?_cons_succ, ih, Nat.div_div_eq_div_mul, ← Nat.pow_succ']

theorem limbs_getElem (n i : Nat) (hi : i < (limbs n).length) :
    (limbs n)[i] = BitVec.ofNat 64 (n / B ^ i % B) := by
  have := limbs_getElem? n i
  rw [List.getElem?_eq_getElem hi] at this
  split at this
  · simp at this
  · exact Option.some.inj this

/-- One step of the top-down comparison: below the equal high part, the next limb decides. -/
theorem div_step (n i : Nat) : n / B ^ i = B * (n / B ^ (i + 1)) + n / B ^ i % B := by
  rw [Nat.pow_succ, ← Nat.div_div_eq_div_mul]
  exact (Nat.div_add_mod _ _).symm

theorem cmp_step {a b i : Nat} (hhi : a / B ^ (i + 1) = b / B ^ (i + 1)) :
    (a / B ^ i < b / B ^ i ↔ a / B ^ i % B < b / B ^ i % B) ∧
    (a / B ^ i = b / B ^ i ↔ a / B ^ i % B = b / B ^ i % B) := by
  have ea := div_step a i
  have eb := div_step b i
  rw [hhi] at ea
  generalize a / B ^ i = A at ea ⊢
  generalize b / B ^ i = C at eb ⊢
  generalize b / B ^ (i + 1) = H at ea eb
  have hB : B = 18446744073709551616 := rfl
  rw [hB] at ea eb ⊢
  constructor <;> constructor <;> intro h <;> omega

theorem lt_of_div_lt {a b k : Nat} (h : a / k < b / k) : a < b :=
  Nat.lt_of_not_le fun hc => absurd (Nat.div_le_div_right (c := k) hc) (Nat.not_le.mpr h)

end ConPanqueque.T.Big

namespace ConPanqueque.T.Big

open ConPanqueque.V.Enc

/-- A number's limbs are its first `L` digits when it has exactly `L` limbs. -/
theorem limbs_eq_digits (n L : Nat) (hn : n < B ^ L) (htop : L = 0 ∨ B ^ (L - 1) ≤ n) :
    limbs n = (List.range L).map (fun k => BitVec.ofNat 64 (n / B ^ k % B)) := by
  have hlen : (limbs n).length = L := by
    have h1 := (limbs_length_lt_iff n L).mpr hn
    rcases htop with h | h
    · subst h; omega
    · have h2 : ¬ (limbs n).length ≤ L - 1 := by
        rw [limbs_length_lt_iff]; omega
      omega
  apply List.ext_getElem
  · simp [hlen]
  · intro k h1 h2
    rw [limbs_getElem n k h1]
    simp

end ConPanqueque.T.Big
