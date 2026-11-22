import ConPanqueque.ExprData
import ConRon.Arena.Store
open ConPanqueque.Translate ConPanqueque.Hash ConPanqueque.ExprData Flapjack.PanSemStateFiniteExact
open ConRon.Arena

/-!
# Derived values as word functions

con-ron's `derOf*` for every constructor, as word functions of the children's
derived words (under the runtime's hash assumptions), translated to Pancake
expressions by `pan_exp`.
-/

namespace ConPanqueque.V.Der

/-- `app` from the children's derived words. -/
def appDataW (df da : UInt64) : UInt64 :=
  ConLeche.hash32 (leanMixHash 17 (leanMixHash (ConLeche.hashOfData df) (ConLeche.hashOfData da)))
      * 4294967296 +
    maxU (ConLeche.bvarOfData df) (ConLeche.bvarOfData da) * 65536 +
    maxU (ConLeche.fvarOfData df) (ConLeche.fvarOfData da) * 2 +
    maxU (lpU df) (lpU da)

/-- A binder (`tag` 19 for `lam`, 23 for `forallE`) from the type's and body's derived words. -/
def bindDataW (tag dt db : UInt64) : UInt64 :=
  ConLeche.hash32 (leanMixHash tag (leanMixHash (ConLeche.hashOfData dt) (ConLeche.hashOfData db)))
      * 4294967296 +
    maxU (ConLeche.bvarOfData dt) (satPredU (ConLeche.bvarOfData db)) * 65536 +
    maxU (ConLeche.fvarOfData dt) (ConLeche.fvarOfData db) * 2 +
    maxU (lpU dt) (lpU db)

/-- A literal from its hash. -/
def litDataW (h : UInt64) : UInt64 := ConLeche.hash32 (leanMixHash 31 h) * 4294967296

pan_exp appDataE := fun (df da : UInt64) => appDataW df da
pan_exp bindDataE := fun (tag dt db : UInt64) => bindDataW tag dt db
pan_exp litDataE := fun (h : UInt64) => litDataW h

section
variable (ra : RuntimeAssumptions) (st : EStore)
include ra

theorem derOfApp_eq (f a : EIdx) : st.derOfApp f a = appDataW (st.derived f) (st.derived a) := by
  simp only [EStore.derOfApp, ConLeche.packData, ra.mixHash, appDataW, maxU_eq]
  rw [lp_or, lp_bit, lp_bit]

theorem derOfBind_eq (tag : UInt64) (ty b : EIdx) :
    st.derOfBindAt tag ty b = bindDataW tag (st.derived ty) (st.derived b) := by
  simp only [EStore.derOfBindAt, derOfBind, ConLeche.packData, ra.mixHash, bindDataW, maxU_eq, satPredU_eq]
  rw [lp_or, lp_bit, lp_bit]

theorem derOfLet_eq (ty v b : EIdx) :
    st.derOfLetAt ty v b = letDataW (st.derived ty) (st.derived v) (st.derived b) := by
  simp only [EStore.derOfLetAt, derOfLet, ConLeche.packData, ra.mixHash, letDataW, maxU_eq, satPredU_eq]
  rw [lp_or, lp_or, lp_bit, lp_bit, lp_bit]

theorem derOfSort_eq (u : LIdx) :
    st.derOfSort u = sortDataW (st.lder u).hash (if (st.lder u).hasParam then 1 else 0) := by
  simp only [EStore.derOfSort, ConLeche.packData, ra.mixHash, sortDataW]
  simp

theorem derOfConst_eq (n : NIdx) (us : LsIdx) :
    st.derOfConst n us = constDataW (st.nder n) (st.lsder us).hash (if (st.lsder us).hasParam then 1 else 0) := by
  simp only [EStore.derOfConst, ConLeche.packData, ra.mixHash, constDataW]
  simp

theorem derOfProj_eq (s : NIdx) (i : Nat) (e : EIdx) :
    st.derOfProj s i e = projDataW (st.nder s) (UInt64.ofNat i) (st.derived e) := by
  simp only [EStore.derOfProj, ConLeche.packData, ra.mixHash, projDataW, lp_bit]
  rfl

theorem derOfLit_eq (l : ConLeche.Literal) : st.derOfLit l = litDataW (ConLeche.Literal.hash l) := by
  simp only [EStore.derOfLit, ConLeche.packData, ra.mixHash, litDataW]
  simp; rfl

end

section
variable (ra : RuntimeAssumptions) (st : EStore)
include ra

theorem derOfBVar_eq (i : Nat) (hi : i < 2 ^ 63) : st.derOfBVar i = bvarDataW (UInt64.ofNat i) := by
  have := bvar_data ra i hi
  simp only [ConLeche.Expr.data] at this
  simp only [EStore.derOfBVar]; rw [← this]

theorem derOfFVar_eq (idx : Nat) (hi : idx < 2 ^ 63) (ty : EIdx) :
    st.derOfFVar idx ty = fvarDataW (UInt64.ofNat idx) (st.derived ty) := by
  have hs : UInt64.ofNat (min (idx + 1) 32767) =
      if UInt64.ofNat idx < 32766 then UInt64.ofNat idx + 1 else 32767 := by
    have ht : (UInt64.ofNat idx).toNat = idx := by simp; omega
    have h32 : (32766 : UInt64).toNat = 32766 := rfl
    split <;> rename_i h <;> rw [UInt64.lt_iff_toNat_lt, ht, h32] at h <;> apply UInt64.toNat_inj.mp
    · rw [UInt64.toNat_add, ht]; simp; omega
    · simp; omega
  simp only [EStore.derOfFVar, ConLeche.packData, ra.mixHash, fvarDataW, ConLeche.satSucc, ConLeche.satRange, hs,
    lp_bit]
  simp; rfl

end

/-- A `str` name from the prefix's derived word and the string's hash. -/
def strDerW (dp hs : UInt64) : UInt64 := leanMixHash (leanMixHash 1 dp) hs
/-- A `num` name from the prefix's derived word and the number's low word. -/
def numDerW (dp nw : UInt64) : UInt64 := leanMixHash (leanMixHash 2 dp) nw

pan_exp strDerE := fun (dp hs : UInt64) => strDerW dp hs
pan_exp numDerE := fun (dp nw : UInt64) => numDerW dp nw

theorem nstr_eq (ra : RuntimeAssumptions) (st : NStore) (p : NIdx) (s : String) :
    st.derOfView (.str p s) = strDerW (st.derived p) (leanStringHash s.toByteArray.data.toList) := by
  simp only [NStore.derOfView, strDerW, ra.mixHash]
  rw [show hash s = String.hash s from rfl, ra.stringHash]

theorem nnum_eq (ra : RuntimeAssumptions) (st : NStore) (p : NIdx) (n : Nat) :
    st.derOfView (.num p n) = numDerW (st.derived p) (UInt64.ofNat n) := by
  simp only [NStore.derOfView, numDerW, ra.mixHash]; rfl

/-- Level hashes from the children's. -/
def succHashW (h : UInt64) : UInt64 := leanMixHash 3 h
def binHashW (tag hu hv : UInt64) : UInt64 := leanMixHash tag (leanMixHash hu hv)
def paramHashW (hn : UInt64) : UInt64 := leanMixHash 11 hn

pan_exp succHashE := fun (h : UInt64) => succHashW h
pan_exp binHashE := fun (tag hu hv : UInt64) => binHashW tag hu hv
pan_exp paramHashE := fun (hn : UInt64) => paramHashW hn

section
variable (ra : RuntimeAssumptions) (st : LStore)
include ra

omit ra in
theorem lzero_eq : st.derOfView .zero = ⟨1, false⟩ := rfl
theorem lsucc_eq (u : LIdx) : st.derOfView (.succ u) = ⟨succHashW (st.derived u).hash, (st.derived u).hasParam⟩ := by
  simp only [LStore.derOfView, succHashW, ra.mixHash]
theorem lmax_eq (u v : LIdx) : st.derOfView (.max u v) =
    ⟨binHashW 5 (st.derived u).hash (st.derived v).hash, (st.derived u).hasParam || (st.derived v).hasParam⟩ := by
  simp only [LStore.derOfView, binHashW, ra.mixHash]
theorem limax_eq (u v : LIdx) : st.derOfView (.imax u v) =
    ⟨binHashW 7 (st.derived u).hash (st.derived v).hash, (st.derived u).hasParam || (st.derived v).hasParam⟩ := by
  simp only [LStore.derOfView, binHashW, ra.mixHash]
theorem lparam_eq (n : NIdx) : st.derOfView (.param n) = ⟨paramHashW (st.ns.derived n), true⟩ := by
  simp only [LStore.derOfView, paramHashW, ra.mixHash]

end

end ConPanqueque.V.Der
