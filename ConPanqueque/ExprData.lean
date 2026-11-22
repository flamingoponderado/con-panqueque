import ConPanqueque.Translate.ConLecheWords
import ConPanqueque.Hash
open ConPanqueque.Translate ConPanqueque.Hash Flapjack.PanSemStateFiniteExact

/-!
# Data words of the remaining expression nodes

con-leche's `Expr.data` for `bvar`, `letE` and `proj`, as word functions
(`bvarDataW`, `letDataW`, `projDataW`) proved equal to it (`bvar_data`,
`letE_data`, `proj_data`, under the runtime's `mixHash`), and translated to
Pancake expressions by `pan_exp` (`bvarDataE`, `letDataE`, `projDataE`).
-/

namespace ConPanqueque.ExprData

def maxU (a b : UInt64) : UInt64 := if a < b then b else a
def satPredU (x : UInt64) : UInt64 := if x = 32767 then 32767 else if x = 0 then 0 else x - 1
def lpU (w : UInt64) : UInt64 := w % 2

/-- `Expr.bvar i`'s data word, from the index as a word. -/
def bvarDataW (iw : UInt64) : UInt64 :=
  ConLeche.hash32 (leanMixHash 3 iw) * 4294967296 + (if iw < 32766 then iw + 1 else 32767) * 65536

/-- `Expr.letE ty v b`'s data word, from the children's. -/
def letDataW (dt dv db : UInt64) : UInt64 :=
  ConLeche.hash32 (leanMixHash 29 (leanMixHash (ConLeche.hashOfData dt)
      (leanMixHash (ConLeche.hashOfData dv) (ConLeche.hashOfData db)))) * 4294967296 +
    maxU (maxU (ConLeche.bvarOfData dt) (ConLeche.bvarOfData dv)) (satPredU (ConLeche.bvarOfData db)) * 65536 +
    maxU (maxU (ConLeche.fvarOfData dt) (ConLeche.fvarOfData dv)) (ConLeche.fvarOfData db) * 2 +
    maxU (maxU (lpU dt) (lpU dv)) (lpU db)

/-- `Expr.proj s i e`'s data word, from the name's hash, the index as a word, and `e`'s data word. -/
def projDataW (hs iw de : UInt64) : UInt64 :=
  ConLeche.hash32 (leanMixHash 37 (leanMixHash hs (leanMixHash iw (ConLeche.hashOfData de)))) * 4294967296 +
    ConLeche.bvarOfData de * 65536 + ConLeche.fvarOfData de * 2 + lpU de

pan_exp bvarDataE := fun (iw : UInt64) => bvarDataW iw
pan_exp letDataE := fun (dt dv db : UInt64) => letDataW dt dv db
pan_exp projDataE := fun (hs iw de : UInt64) => projDataW hs iw de


theorem maxU_eq (a b : UInt64) : max a b = maxU a b := by
  rw [UInt64.max_def, maxU]
  by_cases h : a < b
  · simp [h, UInt64.le_of_lt h]
  · by_cases h2 : a ≤ b
    · have : a = b := by
        rw [UInt64.le_iff_toNat_le] at h2; rw [UInt64.lt_iff_toNat_lt] at h
        exact UInt64.toNat_inj.mp (by omega)
      subst this; simp
    · simp [h, h2]

theorem satPredU_eq (x : UInt64) : ConLeche.satPred x = satPredU x := by
  unfold ConLeche.satPred satPredU
  by_cases h1 : x = 32767
  · simp [h1]
  · by_cases h0 : x = 0
    · simp [h0]
    · simp [h1, h0]

theorem lp_bit (w : UInt64) : (if ConLeche.lpOfData w then (1 : UInt64) else 0) = lpU w := by
  unfold ConLeche.lpOfData lpU
  have : (w % 2).toNat < 2 := by rw [UInt64.toNat_mod]; exact Nat.mod_lt _ (by decide)
  by_cases h : w % 2 = 1
  · simp [h]
  · have h0 : w % 2 = 0 := UInt64.toNat_inj.mp (by
      have := mt (fun e => UInt64.toNat_inj.mp (by simpa using e)) h; simp at this ⊢; omega)
    simp [h0]

theorem lp_or (a b : Bool) :
    (if (a || b) then (1 : UInt64) else 0) = maxU (if a then 1 else 0) (if b then 1 else 0) := by
  cases a <;> cases b <;> decide

theorem bvar_data (ra : RuntimeAssumptions) (i : Nat) (hi : i < 2 ^ 63) :
    (ConLeche.Expr.bvar i).data = bvarDataW (UInt64.ofNat i) := by
  have hs : UInt64.ofNat (min (i + 1) 32767) =
      if UInt64.ofNat i < 32766 then UInt64.ofNat i + 1 else 32767 := by
    have ht : (UInt64.ofNat i).toNat = i := by simp; omega
    have h32 : (32766 : UInt64).toNat = 32766 := rfl
    split <;> rename_i h <;> rw [UInt64.lt_iff_toNat_lt, ht, h32] at h <;> apply UInt64.toNat_inj.mp
    · rw [UInt64.toNat_add, ht]; simp; omega
    · simp; omega
  simp only [ConLeche.Expr.data, ConLeche.packData, ra.mixHash, bvarDataW, ConLeche.satSucc, ConLeche.satRange, hs]
  simp; rfl

theorem letE_data (ra : RuntimeAssumptions) (ty v b : ConLeche.Expr) :
    (ConLeche.Expr.letE ty v b).data = letDataW ty.data v.data b.data := by
  simp only [ConLeche.Expr.data, ConLeche.packData, ra.mixHash, letDataW, maxU_eq, satPredU_eq]
  rw [lp_or, lp_or, lp_bit, lp_bit, lp_bit]

theorem proj_data (ra : RuntimeAssumptions) (n : ConLeche.Name) (i : Nat) (e : ConLeche.Expr) :
    (ConLeche.Expr.proj n i e).data = projDataW n.hashData (UInt64.ofNat i) e.data := by
  simp only [ConLeche.Expr.data, ConLeche.packData, ra.mixHash, projDataW, lp_bit]
  rfl
/-- `Expr.sort u`'s data word, from the level's hash and has-parameter bit. -/
def sortDataW (lh lp : UInt64) : UInt64 :=
  ConLeche.hash32 (leanMixHash 7 lh) * 4294967296 + lp

/-- `Expr.fvar i ty`'s data word, from the index as a word and the type's data word. -/
def fvarDataW (iw dty : UInt64) : UInt64 :=
  ConLeche.hash32 (leanMixHash 5 (leanMixHash iw (ConLeche.hashOfData dty))) * 4294967296 +
    (if iw < 32766 then iw + 1 else 32767) * 2 + lpU dty

pan_exp sortDataE := fun (lh lp : UInt64) => sortDataW lh lp
pan_exp fvarDataE := fun (iw dty : UInt64) => fvarDataW iw dty

theorem sort_data (ra : RuntimeAssumptions) (u : ConLeche.Level) :
    (ConLeche.Expr.sort u).data = sortDataW u.hashData (if ConLeche.levelHasParam u then 1 else 0) := by
  simp only [ConLeche.Expr.data, ConLeche.packData, ra.mixHash, sortDataW, ConLeche.levelHash]
  simp

theorem fvar_data (ra : RuntimeAssumptions) (i : Nat) (hi : i < 2 ^ 63) (ty : ConLeche.Expr) :
    (ConLeche.Expr.fvar i ty).data = fvarDataW (UInt64.ofNat i) ty.data := by
  have hs : UInt64.ofNat (min (i + 1) 32767) =
      if UInt64.ofNat i < 32766 then UInt64.ofNat i + 1 else 32767 := by
    have ht : (UInt64.ofNat i).toNat = i := by simp; omega
    have h32 : (32766 : UInt64).toNat = 32766 := rfl
    split <;> rename_i h <;> rw [UInt64.lt_iff_toNat_lt, ht, h32] at h <;> apply UInt64.toNat_inj.mp
    · rw [UInt64.toNat_add, ht]; simp; omega
    · simp; omega
  simp only [ConLeche.Expr.data, ConLeche.packData, ra.mixHash, fvarDataW, ConLeche.satSucc, ConLeche.satRange, hs, lp_bit]
  simp; rfl

end ConPanqueque.ExprData
