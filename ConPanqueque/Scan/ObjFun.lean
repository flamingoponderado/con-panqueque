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

/-! ## Slot names -/

/-- The fixed locals of the object loop. -/
def fixedLocals : List MlS := [sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2]

theorem slotName_fixed : ∀ k, k < 10 → ∀ x ∈ fixedLocals, slotName k ≠ x := by decide

theorem slotName_inj : ∀ k, k < 10 → ∀ k', k' < 10 → k ≠ k' → slotName k ≠ slotName k' := by decide

/-! ## The code table the scanner needs -/

section
variable {σ : Type}

/-- Every scanner function, at its name, with its parameters. -/
def ScanCodes (t : PanSemStateFiniteExact 64 σ) : Prop :=
  SkipWsCode t ∧ SkipDigitsCode t ∧ SkipKeyCode t ∧ SkipPlainCode t ∧ NumEndCode t ∧
  t.code.lookup fReadNat = some ([(sB, .one), (sI, .one), (sE, .one)], rnFun, .one) ∧
  t.code.lookup fBinder = some ([(sB, .one), (sN, .one), (sI, .one)], biFun, .one) ∧
  t.code.lookup fNatList = some ([(sB, .one), (sN, .one), (sI, .one)], nlFun, .one) ∧
  t.code.lookup fStr = some ([(sB, .one), (sN, .one), (sI, .one)], ssFun, .one) ∧
  t.code.lookup fBool = some ([(sB, .one), (sN, .one), (sI, .one)], sbFun, .one) ∧
  t.code.lookup fKeyEnd = some ([(sB, .one), (sN, .one), (sI, .one)], keFun, .one) ∧
  t.code.lookup fValueAt = some ([(sB, .one), (sN, .one), (sI, .one), (sK, .one)], vaFun, .one) ∧
  t.code.lookup fKeyAt = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], kaFun, .one)

theorem ScanCodes.congr {t u : PanSemStateFiniteExact 64 σ} (h : ScanCodes t) (hc : u.code = t.code) :
    ScanCodes u := by
  unfold ScanCodes SkipWsCode SkipDigitsCode SkipKeyCode SkipPlainCode NumEndCode at *
  rw [hc]; exact h

theorem ScanCodes.entry {t s : PanSemStateFiniteExact 64 σ} (h : ScanCodes t) (hc : s.code = t.code)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) : ScanCodes (callEntryStateHOLFinite s callee) :=
  h.congr (by simp only [callEntryStateHOLFinite]; exact hc)

end

/-! ## One key's value -/

theorem numEndL_skip (bs : List UInt8) (i : Nat) (h : numEndL bs i ≠ i) : numEndL bs i = skipDigitsL bs i := by
  unfold numEndL at *; simp only at *
  split at h
  · exact absurd rfl h
  · rename_i h1; rw [if_neg h1]; split at h
    · exact absurd rfl h
    · rename_i h2; rw [if_neg h2]

section
variable {σ : Type}

/-- The state the key dispatch hands to a value's code. -/
structure KCtx (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (j v : USize)
    (seen : UInt32) (slots : List SVal) (u : PanSemStateFiniteExact 64 σ) : Prop where
  mem : u.memory = t.memory
  dom : u.memaddrs = t.memaddrs
  code : u.code = t.code
  glob : u.globals = t.globals
  be : u.be = t.be
  lb : u.locals.lookup sB = some (.val (.word A))
  ln : u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size)))
  li : u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat)))
  lv : u.locals.lookup sV = some (.val (.word (BitVec.ofNat 64 v.toNat)))
  ls : u.locals.lookup sS = some (.val (.word (BitVec.ofNat 64 seen.toNat)))
  lg : u.locals.lookup sG = some (.val (.word 1))
  lw : ∃ w, u.locals.lookup sW = some (.val (.word w))
  scratch : ∀ x ∈ [sC, sK, sV, sKK, sE2], ∃ w, u.locals.lookup x = some (.val (.word w))
  slotsOK : ∀ k (hk : k < slots.length), ∃ w, u.locals.lookup (slotName k) = some (.val (.word w)) ∧
    SlotOK b w slots[k]
  short : slots.length ≤ 10
  hj : j.toNat < b.size
  hv : v.toNat ≤ b.size

end

section
variable {σ : Type}

theorem advance_spec (sp : ObjSpec) (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray)
    (R : ScanRes (List SVal)) (u : PanSemStateFiniteExact 64 σ) (E : USize) (seen bit : UInt32)
    (slots : List SVal)
    (m0 : u.memory = t.memory) (d0 : u.memaddrs = t.memaddrs) (c0 : u.code = t.code) (g0 : u.globals = t.globals)
    (b0 : u.be = t.be)
    (lb : u.locals.lookup sB = some (.val (.word A)))
    (ln : u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (scratch : ∀ x ∈ [sC, sK, sV, sKK, sE2], ∃ w, u.locals.lookup x = some (.val (.word w)))
    (ls : u.locals.lookup sS = some (.val (.word (BitVec.ofNat 64 seen.toNat))))
    (lE : u.locals.lookup sE2 = some (.val (.word (BitVec.ofNat 64 E.toNat))))
    (lg : u.locals.lookup sG = some (.val (.word 1)))
    (lw : ∃ w, u.locals.lookup sW = some (.val (.word w)))
    (li : ∃ w, u.locals.lookup sI = some (.val (.word w)))
    (hslots : ∀ k (hk : k < slots.length), ∃ w, u.locals.lookup (slotName k) = some (.val (.word w)) ∧
      SlotOK b w slots[k])
    (hshort : slots.length ≤ 10) (hE : E.toNat ≤ b.size)
    (hR : objLoop sp b E false (seen ||| bit) slots = R) :
    ∃ u', evaluateHOLFiniteState u (advance bit) = (none, u') ∧ ObjI sp t A b R u' := by
  obtain ⟨ww, lw⟩ := lw
  obtain ⟨wi, li⟩ := li
  have hor : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
      (.op .or [vv sS, .const (BitVec.ofNat 64 bit.toNat)]) =
      some (.val (.word (BitVec.ofNat 64 (seen ||| bit).toNat))) := by
    rw [← word_or_u32 seen bit]
    simp [vv, evalHOLExact, evalListHOLExact, ls, wordOpHOL, wordOp, valueIsWord, valueWord]
    change _ ||| (_ ||| 0#64) = _
    rw [BitVec.or_zero]
  unfold advance
  rw [seq_normal _ (ConsLoop.assign_local u sS _ _ _ hor ls)]
  let u1 := setVarHOLFinite sS (.val (.word (BitVec.ofNat 64 (seen ||| bit).toNat))) u
  rw [seq_normal _ (ConsLoop.assign_local u1 sW (.const 0) 0 ww (by simp [evalHOLExact]) (by lk [u1]; exact lw))]
  let u2 := setVarHOLFinite sW (.val (.word 0)) u1
  rw [ConsLoop.assign_local u2 sI (vv sE2) (BitVec.ofNat 64 E.toNat) wi (eval_vv u2 sE2 _ (by lk [u2, u1]; exact lE))
    (by lk [u2, u1]; exact li)]
  let u3 := setVarHOLFinite sI (.val (.word (BitVec.ofNat 64 E.toNat))) u2
  have hfx : ∀ k, k < 10 → ∀ x ∈ fixedLocals, slotName k ≠ x := slotName_fixed
  refine ⟨u3, rfl, m0, d0, c0, g0, b0, by lk [u3, u2, u1]; exact lb, by lk [u3, u2, u1]; exact ln, ?_,
    E, false, seen ||| bit, slots, hE, by lk [u3], by lk [u3, u2]; rfl, by lk [u3, u2, u1], ?_,
    Or.inl ⟨by lk [u3, u2, u1]; exact lg, hR⟩⟩
  · intro x hx
    obtain ⟨w, hw⟩ := scratch x hx
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
    refine ⟨w, ?_⟩
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> (lk [u3, u2, u1]; exact hw)
  · intro k hk
    obtain ⟨w, hw, hok⟩ := hslots k hk
    have h1 := hfx k (by omega) sI (by simp [fixedLocals])
    have h2 := hfx k (by omega) sW (by simp [fixedLocals])
    have h3 := hfx k (by omega) sS (by simp [fixedLocals])
    refine ⟨w, ?_, hok⟩
    show (setVarHOLFinite sI _ u2).locals.lookup _ = _
    rw [lookup_setVar_other _ _ h1, lookup_setVar_other _ _ h2, lookup_setVar_other _ _ h3]; exact hw

end

end ConPanqueque.Scan
