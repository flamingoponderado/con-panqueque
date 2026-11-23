import ConPanqueque.T.Big.MulLimbs

/-!
# The schoolbook product in closed form

Before row `i` the cells hold the digits of `P i = (x % B^i) * y`; during row `i` at column `j` the low `i + j`
cells hold the digits of `T i j = P i + x_i * (y % B^j) * B^i` and the rest still those of `P i`; the carry is
`cr i j = T i j / B^(i+j) - P i / B^(i+j)`.
-/

namespace ConPanqueque.T.Big

open ConPanqueque.V.Enc

def dg (n k : Nat) : Nat := n / B ^ k % B
def Pm (x y i : Nat) : Nat := x % B ^ i * y
def Tm (x y i j : Nat) : Nat := Pm x y i + x / B ^ i % B * (y % B ^ j) * B ^ i
def cr (x y i j : Nat) : Nat := Tm x y i j / B ^ (i + j) - Pm x y i / B ^ (i + j)

theorem Tm_zero (x y i : Nat) : Tm x y i 0 = Pm x y i := by simp [Tm, Nat.mod_one]

theorem Tm_succ (x y i j : Nat) :
    Tm x y i (j + 1) = Tm x y i j + x / B ^ i % B * (y / B ^ j % B) * B ^ (i + j) := by
  unfold Tm
  rw [@Nat.mod_pow_succ y B j, Nat.pow_add]
  ring

theorem Pm_le_Tm (x y i j : Nat) : Pm x y i ≤ Tm x y i j := by unfold Tm; omega

theorem Pm_succ (x y i : Nat) (hy : y < B ^ (limbs y).length) :
    Pm x y (i + 1) = Tm x y i (limbs y).length := by
  simp only [Tm, Pm]
  rw [@Nat.mod_pow_succ x B i, Nat.mod_eq_of_lt hy]
  ring

theorem cr_zero (x y i : Nat) : cr x y i 0 = 0 := by simp [cr, Tm_zero]

theorem digit_step (x y i j : Nat) :
    dg (Tm x y i (j + 1)) (i + j) = (x / B ^ i % B * (y / B ^ j % B) + dg (Pm x y i) (i + j) + cr x y i j) % B ∧
    cr x y i (j + 1) = (x / B ^ i % B * (y / B ^ j % B) + dg (Pm x y i) (i + j) + cr x y i j) / B := by
  have hU : (Tm x y i (j + 1)) / B ^ (i + j) = Tm x y i j / B ^ (i + j) + x / B ^ i % B * (y / B ^ j % B) := by
    rw [Tm_succ, Nat.add_mul_div_right _ _ (pow_pos' _)]
  have hge : Pm x y i / B ^ (i + j) ≤ Tm x y i j / B ^ (i + j) := Nat.div_le_div_right (Pm_le_Tm x y i j)
  have hQ := div_step (Pm x y i) (i + j)
  have hQ2 := div_step (Tm x y i (j + 1)) (i + j)
  unfold dg cr
  rw [show i + (j + 1) = i + j + 1 by omega]
  rw [hU] at hQ2 ⊢
  generalize Tm x y i j / B ^ (i + j) = U at *
  generalize x / B ^ i % B * (y / B ^ j % B) = m at *
  generalize Pm x y i / B ^ (i + j) = Q at *
  generalize Pm x y i / B ^ (i + j + 1) = Q' at *
  generalize Tm x y i (j + 1) / B ^ (i + j + 1) = V at *
  have hB : B = 18446744073709551616 := rfl
  rw [hB] at hQ hQ2 ⊢
  constructor <;> omega

theorem digit_low (n m k e : Nat) (hk : k < e) : dg (n + m * B ^ e) k = dg n k := by
  unfold dg
  obtain ⟨d, rfl⟩ : ∃ d, e = k + d + 1 := ⟨e - k - 1, by omega⟩
  have : n + m * B ^ (k + d + 1) = n + (m * B ^ d * B) * B ^ k := by ring
  rw [this, Nat.add_mul_div_right _ _ (pow_pos' _), Nat.add_mul_mod_self_right]

theorem prod_lt (a b k l : Nat) (ha : a < B ^ k) (hb : b < B ^ l) : a * b < B ^ (k + l) := by
  rw [Nat.pow_add]
  rcases Nat.eq_zero_or_pos b with h | h
  · subst h; simp [Nat.mul_pos (pow_pos' k) (pow_pos' l)]
  · exact Nat.mul_lt_mul'' ha hb

theorem Pm_lt (x y i : Nat) (hy : y < B ^ (limbs y).length) : Pm x y i < B ^ (i + (limbs y).length) :=
  prod_lt _ _ _ _ (Nat.mod_lt _ (pow_pos' i)) hy

theorem dg_big (n k : Nat) (h : n < B ^ k) : dg n k = 0 := by
  unfold dg; rw [Nat.div_eq_of_lt h]; rfl

theorem cr_lt (x y i j : Nat) : cr x y i j < B := by
  induction j with
  | zero => rw [cr_zero]; exact Bpos
  | succ j ih =>
    rw [(digit_step x y i j).2]
    have h1 := Nat.mod_lt (x / B ^ i) Bpos
    have h2 := Nat.mod_lt (y / B ^ j) Bpos
    have h3 := Nat.mod_lt (Pm x y i / B ^ (i + j)) Bpos
    have h4 : x / B ^ i % B * (y / B ^ j % B) ≤ 340282366920938463426481119284349108225 := by
      have := Nat.mul_le_mul (show x / B ^ i % B ≤ B - 1 by omega) (show y / B ^ j % B ≤ B - 1 by omega)
      have e : (B - 1) * (B - 1) = 340282366920938463426481119284349108225 := by decide
      omega
    unfold dg
    obtain ⟨m, hm⟩ : ∃ m, m = x / B ^ i % B * (y / B ^ j % B) := ⟨_, rfl⟩
    obtain ⟨d, hd⟩ : ∃ d, d = Pm x y i / B ^ (i + j) % B := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c, c = cr x y i j := ⟨_, rfl⟩
    rw [← hm, ← hd, ← hc]
    rw [← hm] at h4; rw [← hd] at h3; rw [← hc] at ih
    have hB : B = 18446744073709551616 := rfl
    rw [hB] at h3 ih ⊢
    omega

/-- The row's carry is the top digit of the finished row. -/
theorem cr_row (x y i : Nat) (hy : y < B ^ (limbs y).length) :
    cr x y i (limbs y).length = dg (Tm x y i (limbs y).length) (i + (limbs y).length) := by
  have hP := Pm_lt x y i hy
  have hT : Tm x y i (limbs y).length < B ^ (i + (limbs y).length + 1) := by
    rw [← Pm_succ x y i hy, show i + (limbs y).length + 1 = (i + 1) + (limbs y).length by omega]
    exact Pm_lt x y (i + 1) hy
  unfold cr dg
  rw [Nat.div_eq_of_lt hP, Nat.sub_zero, Nat.mod_eq_of_lt]
  have e : B ^ (i + (limbs y).length) * B = B ^ (i + (limbs y).length + 1) := (Nat.pow_succ _ _).symm
  exact Nat.div_lt_of_lt_mul (by rw [e]; exact hT)

theorem Pm_full (x y : Nat) : Pm x y (limbs x).length = x * y := by
  unfold Pm; rw [Nat.mod_eq_of_lt ((limbs_length_lt_iff x _).mp (Nat.le_refl _))]

/-- The result cells during row `i` at column `j`. -/
def Rl (x y N i j : Nat) : List (BitVec 64) :=
  (List.range N).map fun k => BitVec.ofNat 64 (if k < i + j then dg (Tm x y i j) k else dg (Pm x y i) k)

theorem Rl_length (x y N i j : Nat) : (Rl x y N i j).length = N := by simp [Rl]

theorem Rl_get (x y N i j k : Nat) (hk : k < N) :
    (Rl x y N i j)[k]'(by rw [Rl_length]; exact hk) =
      BitVec.ofNat 64 (if k < i + j then dg (Tm x y i j) k else dg (Pm x y i) k) := by
  simp [Rl]

theorem Rl_step (x y N i j : Nat) (h : i + j < N) :
    (Rl x y N i j).set (i + j) (BitVec.ofNat 64 (dg (Tm x y i (j + 1)) (i + j))) = Rl x y N i (j + 1) := by
  apply List.ext_getElem
  · simp [Rl_length]
  · intro k h1 h2
    rw [List.getElem_set]
    have hk : k < N := by simpa [Rl_length] using h2
    rw [Rl_get x y N i (j + 1) k hk]
    split
    · rename_i e; subst e; simp
    · rename_i e
      rw [Rl_get x y N i j k hk]
      by_cases hl : k < i + j
      · rw [if_pos hl, if_pos (by omega), Tm_succ, digit_low _ _ _ _ hl]
      · rw [if_neg hl, if_neg (by omega)]

theorem Rl_read (x y N i j : Nat) (h : i + j < N) :
    (Rl x y N i j)[i + j]? = some (BitVec.ofNat 64 (dg (Pm x y i) (i + j))) := by
  rw [List.getElem?_eq_getElem (by rw [Rl_length]; exact h), Rl_get x y N i j _ h, if_neg (by omega)]

theorem Rl_row (x y N i : Nat) (hy : y < B ^ (limbs y).length) (h : i + (limbs y).length < N) :
    (Rl x y N i (limbs y).length).set (i + (limbs y).length) (BitVec.ofNat 64 (cr x y i (limbs y).length)) =
      Rl x y N (i + 1) 0 := by
  apply List.ext_getElem
  · simp [Rl_length]
  · intro k h1 h2
    have hk : k < N := by simpa [Rl_length] using h2
    rw [List.getElem_set, Rl_get x y N (i + 1) 0 k hk, Tm_zero]
    have e : (if k < i + 1 + 0 then dg (Pm x y (i + 1)) k else dg (Pm x y (i + 1)) k) = dg (Pm x y (i + 1)) k := by
      split <;> rfl
    rw [e]
    split
    · rename_i e2; subst e2; rw [cr_row x y i hy, Pm_succ x y i hy]
    · rename_i e2
      rw [Rl_get x y N i _ k hk]
      by_cases hl : k < i + (limbs y).length
      · rw [if_pos hl, Pm_succ x y i hy]
      · rw [if_neg hl, dg_big _ _ (Nat.lt_of_lt_of_le (Pm_lt x y i hy) (Nat.pow_le_pow_right Bpos (by omega))),
          dg_big _ _ (Nat.lt_of_lt_of_le (Pm_lt x y (i + 1) hy) (Nat.pow_le_pow_right Bpos (by omega)))]

theorem Rl_init (x y N : Nat) : Rl x y N 0 0 = List.replicate N 0 := by
  apply List.ext_getElem
  · simp [Rl_length]
  · intro k h1 h2
    have hk : k < N := by simpa [Rl_length] using h1
    rw [Rl_get x y N 0 0 k hk]
    simp [Pm, dg, Nat.mod_one]

theorem Rl_final (x y N k : Nat) (hk : k < N) :
    (Rl x y N (limbs x).length 0)[k]? = some (BitVec.ofNat 64 (dg (x * y) k)) := by
  rw [List.getElem?_eq_getElem (by rw [Rl_length]; exact hk), Rl_get x y N _ 0 k hk, Tm_zero, Pm_full]
  split <;> rfl

end ConPanqueque.T.Big
