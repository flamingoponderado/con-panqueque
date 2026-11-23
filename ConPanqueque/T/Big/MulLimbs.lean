import ConPanqueque.T.Big.MulMath

/-!
# Digit lists for the schoolbook product

The product's cells are rewritten many times, so its digits are an arbitrary list `R` (value
`ofLimbs R`), held in the image by `setR`.
-/

namespace ConPanqueque.T.Big

open ConPanqueque.V.Enc

theorem ofLimbs_set : ∀ (R : List (BitVec 64)) (k : Nat) (w : BitVec 64) (hk : k < R.length),
    ofLimbs (R.set k w) + R[k].toNat * B ^ k = ofLimbs R + w.toNat * B ^ k
  | [], _, _, hk => absurd hk (by simp)
  | r :: R, 0, w, _ => by simp [ofLimbs]; omega
  | r :: R, k + 1, w, hk => by
    have hk' : k < R.length := by simpa using hk
    have ih := ofLimbs_set R k w hk'
    simp only [List.set_cons_succ, ofLimbs, List.getElem_cons_succ]
    have e1 : R[k].toNat * B ^ (k + 1) = B * (R[k].toNat * B ^ k) := by ring
    have e2 : w.toNat * B ^ (k + 1) = B * (w.toNat * B ^ k) := by ring
    rw [e1, e2]
    have := congrArg (B * ·) ih
    simp only [Nat.mul_add] at this
    have hB : B = 2 ^ 64 := rfl
    rw [hB] at this ⊢
    generalize R[k].toNat * (2 ^ 64) ^ k = u at this ⊢
    generalize w.toNat * (2 ^ 64) ^ k = v at this ⊢
    omega

theorem ofLimbs_lt : ∀ R : List (BitVec 64), ofLimbs R < B ^ R.length
  | [] => by simp [ofLimbs]
  | r :: R => by
    have ih := ofLimbs_lt R
    have hr := r.isLt
    simp only [ofLimbs, List.length_cons, Nat.pow_succ]
    have : B * ofLimbs R + B ≤ B * B ^ R.length := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ ih
    have hB : B = 2 ^ 64 := rfl
    rw [Nat.mul_comm (B ^ R.length)]
    omega

theorem ofLimbs_digit : ∀ (R : List (BitVec 64)) (k : Nat) (hk : k < R.length),
    R[k] = BitVec.ofNat 64 (ofLimbs R / B ^ k % B)
  | [], _, hk => absurd hk (by simp)
  | r :: R, 0, _ => by
    simp [ofLimbs]
    apply BitVec.eq_of_toNat_eq
    simp [Nat.add_mul_mod_self_left]
    exact (Nat.mod_eq_of_lt r.isLt).symm
  | r :: R, k + 1, hk => by
    rw [List.getElem_cons_succ, ofLimbs_digit R k (by simpa using hk)]
    congr 2
    simp only [ofLimbs, Nat.pow_succ']
    rw [← Nat.div_div_eq_div_mul]
    congr 1
    rw [Nat.add_mul_div_left _ _ (by decide), Nat.div_eq_of_lt r.isLt, Nat.zero_add]

theorem ofLimbs_replicate (n : Nat) : ofLimbs (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, ofLimbs, ih]; rfl

/-- The image `B0` with the cells `o …` replaced by the digits `R`. -/
def setR (B0 : List (BitVec 64)) (o : Nat) (R : List (BitVec 64)) : List (BitVec 64) :=
  B0.take o ++ R ++ B0.drop (o + R.length)

theorem setR_length (B0 R : List (BitVec 64)) (o : Nat) (h : o + R.length ≤ B0.length) :
    (setR B0 o R).length = B0.length := by
  simp [setR]; omega

theorem setR_get_in (B0 R : List (BitVec 64)) (o k : Nat) (h : o + R.length ≤ B0.length) (hk : k < R.length) :
    (setR B0 o R)[o + k]? = some R[k] := by
  simp only [setR, List.append_assoc]
  have ht : (List.take o B0).length = o := by simp; omega
  rw [List.getElem?_append_right (by omega), ht, show o + k - o = k by omega, List.getElem?_append_left hk,
    List.getElem?_eq_getElem hk]

theorem setR_get_lo (B0 R : List (BitVec 64)) (o k : Nat) (h : o ≤ B0.length) (hk : k < o) :
    (setR B0 o R)[k]? = B0[k]? := by
  simp only [setR, List.append_assoc]
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hk]

theorem setR_set (B0 R : List (BitVec 64)) (o k : Nat) (w : BitVec 64) (h : o + R.length ≤ B0.length)
    (hk : k < R.length) : (setR B0 o R).set (o + k) w = setR B0 o (R.set k w) := by
  simp only [setR, List.append_assoc, List.length_set]
  have ht : (List.take o B0).length = o := by simp; omega
  rw [List.set_append_right _ _ (by omega), ht, show o + k - o = k by omega, List.set_append_left _ _ hk]

theorem setR_prefix {P B0 R : List (BitVec 64)} {o : Nat} (hp : P <+: B0) (ho : P.length ≤ o) :
    P <+: setR B0 o R := by
  obtain ⟨r, rfl⟩ := hp
  have h1 : P <+: List.take o (P ++ r) := ⟨List.take (o - P.length) r, by rw [List.take_append, List.take_of_length_le ho]⟩
  have h2 : List.take o (P ++ r) <+: setR (P ++ r) o R :=
    ⟨R ++ List.drop (o + R.length) (P ++ r), by simp [setR]⟩
  exact h1.trans h2

end ConPanqueque.T.Big
