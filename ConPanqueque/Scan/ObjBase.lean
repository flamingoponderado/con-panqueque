import ConPanqueque.Scan.NatList

/-! # Shared definitions of the Pancake scanners (key indices, local and function names) -/

namespace ConPanqueque.Scan

open ConLeche.Frontend
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

/-- Every key, in constructor order. -/
def allKeys : List Key := [.kUnknown, .kAll, .kApp, .kArg, .kAxiom, .kBinderInfo, .kBody, .kBvar, .kCidx, .kConst, .kCtor, .kCtors, .kDef, .kFn, .kForallE, .kHints, .kI, .kIdx, .kIe, .kIl, .kImax, .kIn, .kInduct, .kInductive, .kIsRec, .kIsReflexive, .kIsUnsafe, .kK, .kKind, .kLam, .kLetE, .kLevelParams, .kMax, .kMeta, .kName, .kNatVal, .kNfields, .kNondep, .kNum, .kNumFields, .kNumIndices, .kNumMinors, .kNumMotives, .kNumNested, .kNumParams, .kOpaque, .kParam, .kPre, .kProj, .kQuot, .kRecs, .kRegular, .kRhs, .kRules, .kSafety, .kSort, .kStr, .kStrVal, .kStruct, .kSucc, .kThm, .kType, .kTypeName, .kTypes, .kUs, .kValue]

def keyOfIdx (n : Nat) : Key := allKeys.getD n .kUnknown

theorem keyOfIdx_ctorIdx (k : Key) : keyOfIdx k.ctorIdx = k := by
  cases k <;> rfl

theorem key_ctorIdx_inj {k k' : Key} (h : k.ctorIdx = k'.ctorIdx) : k = k' := by
  rw [← keyOfIdx_ctorIdx k, ← keyOfIdx_ctorIdx k', h]

theorem key_ctorIdx_lt (k : Key) : k.ctorIdx < 128 := by
  cases k <;> decide

theorem word_and_u32 (a b : UInt32) :
    BitVec.ofNat 64 a.toNat &&& BitVec.ofNat 64 b.toNat = BitVec.ofNat 64 (a &&& b).toNat := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_and, UInt32.toNat_and]

theorem word_or_u32 (a b : UInt32) :
    BitVec.ofNat 64 a.toNat ||| BitVec.ofNat 64 b.toNat = BitVec.ofNat 64 (a ||| b).toNat := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_or, UInt32.toNat_or]

/-! ## The code -/

def slotNames : List MlS :=
  [ofString "s0", ofString "s1", ofString "s2", ofString "s3", ofString "s4", ofString "s5",
    ofString "s6", ofString "s7", ofString "s8", ofString "s9"]

def slotName (k : Nat) : MlS := slotNames.getD k (ofString "sx")
def sS := ofString "seen"
def sV := ofString "v"
def sKK := ofString "kk"

def fKeyEnd := ofString "keyEnd"
def fValueAt := ofString "valueAt"
def fKeyAt := ofString "keyAt"
def fReadNat := ofString "readNatSat"
def fBinder := ofString "scanBinderInfo"
def fNatList := ofString "scanNatList"
def fStr := ofString "scanString"
def fBool := ofString "scanBool"

def callTo (x f : MlS) (args : List (ExpHOL 64)) : ProgHOL 64 := .call (some (some (.local, x), none)) f args

theorem keyEndL_lt (bs : List UInt8) (j : Nat) (h : keyEndL bs j ≠ 0) : keyEndL bs j < bs.length ∧ j ≤ keyEndL bs j := by
  have hge := skipL_ge isKeyN bs _ j rfl
  unfold keyEndL at *; simp only at *
  split at h
  · rename_i hq
    rw [if_pos hq]
    refine ⟨?_, hge⟩
    by_cases hl : skipL isKeyN bs j < bs.length
    · exact hl
    · rw [List.getElem?_eq_none (by omega)] at hq; simp at hq
  · exact absurd rfl h

theorem valueAtL_le (bs : List UInt8) (i ke : Nat) (hi : i ≤ bs.length) (hke : ke < bs.length) :
    valueAtL bs i ke ≤ bs.length := by
  unfold valueAtL; simp only
  split
  · rename_i hq
    have h1 := skipL_le_length isWsN bs _ (ke + 1) rfl (by omega)
    have hl : skipWsL bs (ke + 1) < bs.length := by
      by_cases h : skipWsL bs (ke + 1) < bs.length
      · exact h
      · rw [List.getElem?_eq_none (by omega)] at hq; simp at hq
    exact skipL_le_length isWsN bs _ _ rfl (by omega)
  · exact hi

theorem usz_lt (x : USize) : x.toNat < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (USize.toNat_lt_two_pow_numBits x)
    (Nat.pow_le_pow_right (by decide) (by rcases System.Platform.numBits_eq with h | h <;> omega))

theorem numEndL_skip (bs : List UInt8) (i : Nat) (h : numEndL bs i ≠ i) : numEndL bs i = skipDigitsL bs i := by
  unfold numEndL at *; simp only at *
  split at h
  · exact absurd rfl h
  · rename_i h1; rw [if_neg h1]; split at h
    · exact absurd rfl h
    · rename_i h2; rw [if_neg h2]

end ConPanqueque.Scan
