import ConPanqueque.Scan.NatList
import ConPanqueque.Scan.Obj

/-! # The object loop in Pancake: helpers -/

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

def slotName (k : Nat) : MlS := ofString ("s" ++ toString k)
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

def advance (bit : UInt32) : ProgHOL 64 :=
  .seq (.assign .local sS (.op .or [vv sS, .const (BitVec.ofNat 64 bit.toNat)]))
    (.seq (.assign .local sW (.const 0)) (.assign .local sI (vv sE2)))

/-- The code of one key's value. -/
def actCode (bit : UInt32) : VAct → ProgHOL 64
  | .natSet sl => .seq (callTo sE2 fNumEnd [vv sB, vv sN, vv sV])
      (.ite (.cmp .equal (vv sE2) (vv sV)) hang
        (.ite (.cmp .lower (vv sI) (vv sE2))
          (.seq (callTo (slotName sl) fReadNat [vv sB, vv sV, vv sE2]) (advance bit)) hang))
  | .natDrop => .seq (callTo sE2 fNumEnd [vv sB, vv sN, vv sV])
      (.ite (.cmp .equal (vv sE2) (vv sV)) hang
        (.ite (.cmp .lower (vv sI) (vv sE2)) (advance bit) hang))
  | .binder => .seq (callTo sE2 fBinder [vv sB, vv sN, vv sV])
      (.ite (.cmp .lower (vv sI) (vv sE2)) (advance bit) hang)
  | .natList sl => .seq (callTo sE2 fNatList [vv sB, vv sN, vv sV])
      (.ite (.cmp .lower (vv sI) (vv sE2)) (.seq (.assign .local (slotName sl) (vv sV)) (advance bit)) hang)
  | .natListDrop => .seq (callTo sE2 fNatList [vv sB, vv sN, vv sV])
      (.ite (.cmp .lower (vv sI) (vv sE2)) (advance bit) hang)
  | .str sl => .seq (callTo sE2 fStr [vv sB, vv sN, vv sV])
      (.seq (.assign .local sE2 (.op .add [vv sE2, .const 1]))
        (.ite (.cmp .lower (vv sI) (vv sE2)) (.seq (.assign .local (slotName sl) (vv sV)) (advance bit)) hang))
  | .bool sl => .seq (callTo sE2 fBool [vv sB, vv sN, vv sV])
      (.ite (.cmp .lower (vv sI) (vv sE2))
        (.seq (bAt (slotName sl) (vv sV))
          (.seq (.assign .local (slotName sl) (.cmp .equal (vv (slotName sl)) (.const 116))) (advance bit)))
        hang)
  | .boolDrop => .seq (callTo sE2 fBool [vv sB, vv sN, vv sV])
      (.ite (.cmp .lower (vv sI) (vv sE2)) (advance bit) hang)
  | .hints _ => hang

/-- The key dispatch, read off the table. -/
def dispatch : List (Key × UInt32 × VAct) → ProgHOL 64
  | [] => hang
  | (k, bit, a) :: r =>
    .ite (.cmp .equal (vv sKK) (.const (BitVec.ofNat 64 k.ctorIdx)))
      (.ite (.cmp .notEqual (.op .and [vv sS, .const (BitVec.ofNat 64 bit.toNat)]) (.const 0)) hang (actCode bit a))
      (dispatch r)

def keyPart (ks : List (Key × UInt32 × VAct)) : ProgHOL 64 :=
  .seq (callTo sK fKeyEnd [vv sB, vv sN, .op .add [vv sI, .const 1]])
    (.ite (.cmp .equal (vv sK) (.const 0)) hang
      (.seq (callTo sV fValueAt [vv sB, vv sN, vv sI, vv sK])
        (.ite (.cmp .equal (vv sV) (vv sI)) hang
          (.seq (callTo sKK fKeyAt [vv sB, vv sN, vv sI, .op .sub [vv sK, .op .add [vv sI, .const 1]]])
            (dispatch ks)))))

def objBody (sp : ObjSpec) : ProgHOL 64 :=
  .ite (.cmp .lower (vv sI) (vv sN))
    (.seq (.assign .local sC (.loadByte (.op .add [vv sB, vv sI])))
      (.ite wsTest incI
        (.ite (.cmp .equal (vv sC) (.const 125))
          (.ite (.op .and [vv sW, .cmp .notEqual (vv sS) (.const 0)]) hang
            (.ite (.cmp .notEqual (.op .and [vv sS, .const (BitVec.ofNat 64 sp.need.toNat)])
                (.const (BitVec.ofNat 64 sp.need.toNat))) hang
              (.seq incI (.assign .local sG (.const 0)))))
          (.ite (.cmp .equal (vv sC) (.const 44))
            (.ite (vv sW) hang (.seq (.assign .local sW (.const 1)) incI))
            (.ite (.cmp .equal (vv sC) (.const 34)) (.ite (vv sW) (keyPart sp.keys) hang) hang)))))
    hang

def objLoopP (sp : ObjSpec) : ProgHOL 64 := .while (vv sG) (objBody sp)

/-! ## The invariant -/

def listSentinel : Nat := 2 ^ 63

/-- How a slot's word stands for con-leche's slot value: a number (capped), the position a list or a
string is read again from, or a flag. -/
def SlotOK (b : ByteArray) (w : BitVec 64) : SVal → Prop
  | .n x => w = BitVec.ofNat 64 (min x natCap)
  | .l xs => (∃ (p e : USize), w = BitVec.ofNat 64 p.toNat ∧ scanNatList b p = .ok xs e) ∨
      (xs = [] ∧ w = BitVec.ofNat 64 listSentinel)
  | .s x => (∃ (p e : USize), w = BitVec.ofNat 64 p.toNat ∧ scanString b p = .ok x e) ∨
      (x = "" ∧ w = BitVec.ofNat 64 listSentinel)
  | .b x => w = bw (x = true)
  | .h _ => True

section
variable {σ : Type}

def ObjI (sp : ObjSpec) (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray)
    (R : ScanRes (List SVal)) (u : PanSemStateFiniteExact 64 σ) : Prop :=
  u.memory = t.memory ∧ u.memaddrs = t.memaddrs ∧ u.code = t.code ∧ u.globals = t.globals ∧
  u.be = t.be ∧
  u.locals.lookup sB = some (.val (.word A)) ∧
  u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))) ∧
  (∀ x ∈ [sC, sK, sV, sKK, sE2], ∃ w, u.locals.lookup x = some (.val (.word w))) ∧
  ∃ (j : USize) (wm : Bool) (seen : UInt32) (slots : List SVal), j.toNat ≤ b.size ∧
    u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) ∧
    u.locals.lookup sW = some (.val (.word (bw (wm = true)))) ∧
    u.locals.lookup sS = some (.val (.word (BitVec.ofNat 64 seen.toNat))) ∧
    (∀ k (hk : k < slots.length), ∃ w, u.locals.lookup (slotName k) = some (.val (.word w)) ∧
      SlotOK b w slots[k]) ∧
    ((u.locals.lookup sG = some (.val (.word 1)) ∧ objLoop sp b j wm seen slots = R) ∨
     (u.locals.lookup sG = some (.val (.word 0)) ∧ R = .ok slots j))

end

end ConPanqueque.Scan
