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

def ObjI (sp : ObjSpec) (nS : Nat) (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray)
    (R : ScanRes (List SVal)) (u : PanSemStateFiniteExact 64 σ) : Prop :=
  u.memory = t.memory ∧ u.memaddrs = t.memaddrs ∧ u.code = t.code ∧ u.globals = t.globals ∧
  u.be = t.be ∧
  u.locals.lookup sB = some (.val (.word A)) ∧
  u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))) ∧
  (∀ x ∈ [sC, sK, sV, sKK, sE2], ∃ w, u.locals.lookup x = some (.val (.word w))) ∧
  ∃ (j : USize) (wm : Bool) (seen : UInt32) (slots : List SVal), j.toNat ≤ b.size + 64 ∧ slots.length = nS ∧
    u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) ∧
    u.locals.lookup sW = some (.val (.word (bw (wm = true)))) ∧
    u.locals.lookup sS = some (.val (.word (BitVec.ofNat 64 seen.toNat))) ∧
    (∀ k (hk : k < slots.length), ∃ w, u.locals.lookup (slotName k) = some (.val (.word w)) ∧
      SlotOK b w slots[k]) ∧
    ((u.locals.lookup sG = some (.val (.word 1)) ∧ objLoop sp b j wm seen slots = R) ∨
     (u.locals.lookup sG = some (.val (.word 0)) ∧ R = .ok slots j))

end

theorem usz_lt (x : USize) : x.toNat < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (USize.toNat_lt_two_pow_numBits x)
    (Nat.pow_le_pow_right (by decide) (by rcases System.Platform.numBits_eq with h | h <;> omega))

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

theorem scanBool_facts {b : ByteArray} (hp : Plat b) (v : USize) (hv : v.toNat ≤ b.size) {x : Bool} {e : USize}
    (h : ConLeche.Frontend.scanBool b v = .ok x e) :
    e.toNat ≤ v.toNat + 5 ∧ (x = true ↔ (byteL b.data.toList v.toNat).toNat = 116) := by
  have hroom := hp.room
  have mt := matchLit_L hp "true".toUTF8 (by decide) (by decide) _ v 0 rfl
    (by rw [show "true".toUTF8.size = 4 by decide]; simp; omega) (by simp)
  have mf := matchLit_L hp "false".toUTF8 (by decide) (by decide) _ v 0 rfl
    (by rw [show "false".toUTF8.size = 5 by decide]; simp; omega) (by simp)
  simp only [show "true".toUTF8.data.toList = [116, 114, 117, 101] by decide,
    show "false".toUTF8.data.toList = [102, 97, 108, 115, 101] by decide, List.drop_zero, USize.toNat_zero] at mt mf
  have h4 : (v + 4).toNat = v.toNat + 4 := usize_add_toNat hp.bits v 4 (by omega)
  have h5 : (v + 5).toNat = v.toNat + 5 := usize_add_toNat hp.bits v 5 (by omega)
  rw [ConLeche.Frontend.scanBool, mt, mf] at h
  split at h
  · rename_i ht
    simp only [ConLeche.Frontend.ScanRes.ok.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [litsL, Nat.add_zero, Bool.and_eq_true, beq_iff_eq] at ht
    refine ⟨by omega, ?_⟩
    simp [ht.1]
  · split at h
    · rename_i _ hf
      simp only [ConLeche.Frontend.ScanRes.ok.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp only [litsL, Nat.add_zero, Bool.and_eq_true, beq_iff_eq] at hf
      refine ⟨by omega, ?_⟩
      simp [hf.1]
    · simp at h

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

theorem advance_spec (sp : ObjSpec) (nS : Nat) (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray)
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
    (hshort : slots.length ≤ 10) (hE : E.toNat ≤ b.size + 64) (hn : slots.length = nS)
    (hR : objLoop sp b E false (seen ||| bit) slots = R) :
    ∃ u', evaluateHOLFiniteState u (advance bit) = (none, u') ∧ ObjI sp nS t A b R u' := by
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
    E, false, seen ||| bit, slots, hE, hn, by lk [u3], by lk [u3, u2]; rfl, by lk [u3, u2, u1], ?_,
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

section
variable {σ : Type}

def ActOK (n : Nat) : VAct → Prop
  | .natSet sl => sl < n
  | .natList sl => sl < n
  | .str sl => sl < n
  | .bool sl => sl < n
  | .hints sl => sl < n
  | _ => True

/-- The continuation of con-leche's loop after one key's value. -/
def contAfter (sp : ObjSpec) (b : ByteArray) (j v : USize) (seen bit : UInt32) (slots : List SVal) (a : VAct) :
    ScanRes (List SVal) :=
  match stepVal b j v a with
  | .err er => .err er
  | .ok upd e => if j < e then objLoop sp b e false (seen ||| bit) (applyUpd slots upd)
      else .err ⟨j.toNat, .noProgress⟩

theorem act_natSet (sp : ObjSpec) (nS : Nat) (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (R : ScanRes (List SVal)) (j v : USize) (seen bit : UInt32)
    (slots : List SVal) (sl : Nat) (u : PanSemStateFiniteExact 64 σ) (hk : KCtx t A b j v seen slots u) (hn : slots.length = nS)
    (hsl : sl < slots.length) (hR : contAfter sp b j v seen bit slots (.natSet sl) = R) :
    Stop (evaluateHOLFiniteState u (actCode bit (.natSet sl))).1 ∨
      ((evaluateHOLFiniteState u (actCode bit (.natSet sl))).1 = none ∧
        ObjI sp nS t A b R (evaluateHOLFiniteState u (actCode bit (.natSet sl))).2) := by
  have hL : b.size < 2 ^ 64 := hp.size
  have hvb := hk.hv
  have hjb := hk.hj
  have hcu : ScanCodes u := hc.congr hk.code
  obtain ⟨e0, le0⟩ := hk.scratch sE2 (by simp)
  have hcall := call3_ret u sE2 fNumEnd sB sN sI neFun (vv sB) (vv sN) (vv sV) A
    (BitVec.ofNat 64 b.size) (BitVec.ofNat 64 v.toNat) (BitVec.ofNat 64 (ConLeche.Frontend.numEnd b v).toNat) e0
    (by decide) (by decide) (by decide) hcu.2.2.2.2.1 (eval_vv u sB _ hk.lb) (eval_vv u sN _ hk.ln)
    (eval_vv u sV _ hk.lv) le0
    (fun callee h1 h2 h3 => numEnd_refines (callEntryStateHOLFinite u callee) A b hp
      (bytesAt_congr hb (by exact hk.mem) (by exact hk.dom) (by exact hk.be)) v hk.hv
      ((hcu.entry rfl callee).2.1) h1 h2 h3)
  simp only [actCode, callTo]
  rcases hcall with hs | ⟨u1, hu1, m1, d1, g1, k1, b1, le1, lo1⟩
  · exact Or.inl (seq_stop u _ _ hs)
  rw [seq_normal _ hu1]
  obtain ⟨E, hE⟩ : ∃ E, E = ConLeche.Frontend.numEnd b v := ⟨_, rfl⟩
  rw [← hE] at le1
  have hne := numEnd_eq hp v hk.hv
  rw [← hE] at hne
  have hEl : E.toNat ≤ b.size := by
    have := numEndL_le b.data.toList v.toNat (by simp; exact hk.hv); rw [hne]; simpa using this
  have lv1 : u1.locals.lookup sV = some (.val (.word (BitVec.ofNat 64 v.toNat))) := by
    rw [lo1 sV (by decide)]; exact hk.lv
  rw [ite_word u1 _ _ _ _ (ConsLoop.eval_cmp_of u1 .equal (vv sE2) (vv sV) _ _ (eval_vv u1 sE2 _ le1)
    (eval_vv u1 sV _ lv1)), bw_eq _ _ (by omega) (by omega)]
  by_cases hEv : E.toNat = v.toNat
  · simp only [bw, hEv, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    exact Or.inl (stop_hang u1)
  simp only [bw, hEv, ↓reduceIte, ne_eq, not_true_eq_false]
  have li1 : u1.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by
    rw [lo1 sI (by decide)]; exact hk.li
  rw [ite_word u1 _ _ _ _ (eval_lower u1 (vv sI) (vv sE2) j.toNat E.toNat (by omega) (by omega)
    (eval_vv u1 sI _ li1) (eval_vv u1 sE2 _ le1))]
  by_cases hjE0 : ¬ j.toNat < E.toNat
  · simp only [bw, hjE0, ↓reduceIte, ne_eq, not_true_eq_false]; exact Or.inl (stop_hang u1)
  have hjE : j.toNat < E.toNat := by omega
  simp only [bw, hjE, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
  -- the value
  have hskip : E.toNat = skipDigitsL b.data.toList v.toNat := by
    rw [hne]; exact numEndL_skip _ _ (by rw [← hne]; exact hEv)
  have hfx : ∀ x ∈ fixedLocals, slotName sl ≠ x := slotName_fixed sl (by have := hk.short; omega)
  obtain ⟨w0, lw0, -⟩ := hk.slotsOK sl hsl
  have hcall2 := call3_ret u1 (slotName sl) fReadNat sB sI sE rnFun (vv sB) (vv sV) (vv sE2) A
    (BitVec.ofNat 64 v.toNat) (BitVec.ofNat 64 E.toNat)
    (BitVec.ofNat 64 (min (ConLeche.Frontend.readNatAt b v E) natCap)) w0
    (by decide) (by decide) (by decide) (by rw [k1]; exact hcu.2.2.2.2.2.1)
    (eval_vv u1 sB _ (by rw [lo1 sB (by decide)]; exact hk.lb)) (eval_vv u1 sV _ lv1) (eval_vv u1 sE2 _ le1)
    (by rw [lo1 _ (hfx sE2 (by simp [fixedLocals]))]; exact lw0)
    (fun callee h1 h2 h3 => rnFun_refines (callEntryStateHOLFinite u1 callee) A b hp
      (bytesAt_congr hb (by exact m1.trans hk.mem) (by exact d1.trans hk.dom) (by exact b1.trans hk.be))
      v E hk.hv hskip h1 h3 h2)
  rcases hcall2 with hs | ⟨u2, hu2, m2, d2, g2, k2, b2, lx2, lo2⟩
  · exact Or.inl (seq_stop u1 _ _ hs)
  rw [seq_normal _ hu2]
  have hR' : objLoop sp b E false (seen ||| bit)
      (slots.set sl (.n (ConLeche.Frontend.readNatAt b v E))) = R := by
    rw [← hR]; unfold contAfter stepVal; simp only [← hE]
    have : (E == v) = false := beq_eq_false_iff_ne.mpr (fun h => hEv (by rw [h]))
    rw [this]; simp only [Bool.false_eq_true, ↓reduceIte, applyUpd]
    rw [if_pos (USize.lt_iff_toNat_lt.mpr hjE)]
  have hlo : ∀ y, y ≠ slotName sl → y ≠ sE2 → u2.locals.lookup y = u.locals.lookup y := fun y h1 h2 => by
    rw [lo2 y h1, lo1 y h2]
  obtain ⟨u3, hu3, hI⟩ := advance_spec sp nS t A b R u2 E seen bit _ (m2.trans (m1.trans hk.mem))
    (d2.trans (d1.trans hk.dom)) (k2.trans (k1.trans hk.code)) (g2.trans (g1.trans hk.glob))
    (b2.trans (b1.trans hk.be))
    (by rw [hlo sB (Ne.symm (hfx sB (by simp [fixedLocals]))) (by decide)]; exact hk.lb)
    (by rw [hlo sN (Ne.symm (hfx sN (by simp [fixedLocals]))) (by decide)]; exact hk.ln)
    (by
      intro x hx
      by_cases hxe : x = sE2
      · subst hxe; exact ⟨_, by rw [lo2 sE2 (Ne.symm (hfx sE2 (by simp [fixedLocals])))]; exact le1⟩
      · have hxs : x ≠ slotName sl := fun h => hfx x (by
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
          simp only [fixedLocals, List.mem_cons, List.not_mem_nil, or_false]
          rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp) h.symm
        rw [hlo x hxs hxe]; exact hk.scratch x hx)
    (by rw [hlo sS (Ne.symm (hfx sS (by simp [fixedLocals]))) (by decide)]; exact hk.ls)
    (by rw [lo2 sE2 (Ne.symm (hfx sE2 (by simp [fixedLocals])))]; exact le1)
    (by rw [hlo sG (Ne.symm (hfx sG (by simp [fixedLocals]))) (by decide)]; exact hk.lg)
    (by rw [hlo sW (Ne.symm (hfx sW (by simp [fixedLocals]))) (by decide)]; exact hk.lw)
    ⟨_, by rw [hlo sI (Ne.symm (hfx sI (by simp [fixedLocals]))) (by decide)]; exact hk.li⟩
    (by
      intro k hk'
      simp only [List.length_set] at hk'
      by_cases hks : k = sl
      · subst hks
        refine ⟨_, lx2, ?_⟩
        simp [SlotOK]
      · have hne : slotName k ≠ slotName sl := slotName_inj k (by have := hk.short; omega) sl
          (by have := hk.short; omega) hks
        obtain ⟨w, hw, hok⟩ := hk.slotsOK k hk'
        refine ⟨w, ?_, by rw [List.getElem_set_ne (Ne.symm hks)]; exact hok⟩
        rw [hlo _ hne (slotName_fixed k (by have := hk.short; omega) sE2 (by simp [fixedLocals]))]
        exact hw)
    (by simp only [List.length_set]; exact hk.short) (by omega) (by simp [hn]) hR'
  rw [hu3]
  exact Or.inr ⟨rfl, hI⟩

end

section
variable {σ : Type}

theorem adv_from_ctx (sp : ObjSpec) (nS : Nat) (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray)
    (R : ScanRes (List SVal)) (u u2 : PanSemStateFiniteExact 64 σ) (j v E : USize) (seen bit : UInt32)
    (slots slots' : List SVal) (hk : KCtx t A b j v seen slots u)
    (m : u2.memory = u.memory) (d : u2.memaddrs = u.memaddrs) (c : u2.code = u.code) (g : u2.globals = u.globals)
    (be : u2.be = u.be)
    (hlo : ∀ y ∈ fixedLocals, y ≠ sE2 → u2.locals.lookup y = u.locals.lookup y)
    (le : u2.locals.lookup sE2 = some (.val (.word (BitVec.ofNat 64 E.toNat))))
    (hslots : ∀ k (hk : k < slots'.length), ∃ w, u2.locals.lookup (slotName k) = some (.val (.word w)) ∧
      SlotOK b w slots'[k])
    (hlen : slots'.length = slots.length) (hE : E.toNat ≤ b.size + 64) (hn : slots.length = nS)
    (hR : objLoop sp b E false (seen ||| bit) slots' = R) :
    ∃ u3, evaluateHOLFiniteState u2 (advance bit) = (none, u3) ∧ ObjI sp nS t A b R u3 := by
  have q : ∀ y ∈ fixedLocals, y ≠ sE2 → ∀ w, u.locals.lookup y = some (.val (.word w)) →
      u2.locals.lookup y = some (.val (.word w)) := fun y hy hne w h => by rw [hlo y hy hne]; exact h
  exact advance_spec sp nS t A b R u2 E seen bit slots' (m.trans hk.mem) (d.trans hk.dom) (c.trans hk.code)
    (g.trans hk.glob) (be.trans hk.be) (q sB (by simp [fixedLocals]) (by decide) _ hk.lb)
    (q sN (by simp [fixedLocals]) (by decide) _ hk.ln)
    (by
      intro x hx
      by_cases hxe : x = sE2
      · subst hxe; exact ⟨_, le⟩
      · obtain ⟨w, hw⟩ := hk.scratch x hx
        refine ⟨w, q x ?_ hxe w hw⟩
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
        simp only [fixedLocals, List.mem_cons, List.not_mem_nil, or_false]
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp)
    (q sS (by simp [fixedLocals]) (by decide) _ hk.ls) le (q sG (by simp [fixedLocals]) (by decide) _ hk.lg)
    (by obtain ⟨w, hw⟩ := hk.lw; exact ⟨w, q sW (by simp [fixedLocals]) (by decide) _ hw⟩)
    ⟨_, q sI (by simp [fixedLocals]) (by decide) _ hk.li⟩ hslots (by rw [hlen]; exact hk.short) hE (by rw [hlen, hn]) hR

/-- The slots of a state that changed only fixed locals. -/
theorem slots_keep (b : ByteArray) (u u2 : PanSemStateFiniteExact 64 σ) (slots : List SVal) (hshort : slots.length ≤ 10)
    (hlo : ∀ y, (∀ k, k < 10 → y ≠ slotName k) → u2.locals.lookup y = u.locals.lookup y)
    (hs : ∀ k (hk : k < slots.length), ∃ w, u.locals.lookup (slotName k) = some (.val (.word w)) ∧ SlotOK b w slots[k])
    (hkeep : ∀ k, k < 10 → u2.locals.lookup (slotName k) = u.locals.lookup (slotName k)) :
    ∀ k (hk : k < slots.length), ∃ w, u2.locals.lookup (slotName k) = some (.val (.word w)) ∧ SlotOK b w slots[k] :=
  fun k hk => by rw [hkeep k (by omega)]; exact hs k hk

end

section
variable {σ : Type}

theorem act_natDrop (sp : ObjSpec) (nS : Nat) (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (R : ScanRes (List SVal)) (j v : USize) (seen bit : UInt32)
    (slots : List SVal) (u : PanSemStateFiniteExact 64 σ) (hk : KCtx t A b j v seen slots u) (hn : slots.length = nS)
    (hR : contAfter sp b j v seen bit slots .natDrop = R) :
    Stop (evaluateHOLFiniteState u (actCode bit .natDrop)).1 ∨
      ((evaluateHOLFiniteState u (actCode bit .natDrop)).1 = none ∧
        ObjI sp nS t A b R (evaluateHOLFiniteState u (actCode bit .natDrop)).2) := by
  have hL : b.size < 2 ^ 64 := hp.size
  have hvb := hk.hv
  have hjb := hk.hj
  have hcu : ScanCodes u := hc.congr hk.code
  obtain ⟨e0, le0⟩ := hk.scratch sE2 (by simp)
  have hcall := call3_ret u sE2 fNumEnd sB sN sI neFun (vv sB) (vv sN) (vv sV) A
    (BitVec.ofNat 64 b.size) (BitVec.ofNat 64 v.toNat) (BitVec.ofNat 64 (ConLeche.Frontend.numEnd b v).toNat) e0
    (by decide) (by decide) (by decide) hcu.2.2.2.2.1 (eval_vv u sB _ hk.lb) (eval_vv u sN _ hk.ln)
    (eval_vv u sV _ hk.lv) le0
    (fun callee h1 h2 h3 => numEnd_refines (callEntryStateHOLFinite u callee) A b hp
      (bytesAt_congr hb (by exact hk.mem) (by exact hk.dom) (by exact hk.be)) v hk.hv
      ((hcu.entry rfl callee).2.1) h1 h2 h3)
  simp only [actCode, callTo]
  rcases hcall with hs | ⟨u1, hu1, m1, d1, g1, k1, b1, le1, lo1⟩
  · exact Or.inl (seq_stop u _ _ hs)
  rw [seq_normal _ hu1]
  obtain ⟨E, hE⟩ : ∃ E, E = ConLeche.Frontend.numEnd b v := ⟨_, rfl⟩
  rw [← hE] at le1
  have hne := numEnd_eq hp v hk.hv
  rw [← hE] at hne
  have hEl : E.toNat ≤ b.size := by
    have := numEndL_le b.data.toList v.toNat (by simp; exact hk.hv); rw [hne]; simpa using this
  have lv1 : u1.locals.lookup sV = some (.val (.word (BitVec.ofNat 64 v.toNat))) := by
    rw [lo1 sV (by decide)]; exact hk.lv
  rw [ite_word u1 _ _ _ _ (ConsLoop.eval_cmp_of u1 .equal (vv sE2) (vv sV) _ _ (eval_vv u1 sE2 _ le1)
    (eval_vv u1 sV _ lv1)), bw_eq _ _ (by omega) (by omega)]
  by_cases hEv : E.toNat = v.toNat
  · simp only [bw, hEv, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    exact Or.inl (stop_hang u1)
  simp only [bw, hEv, ↓reduceIte, ne_eq, not_true_eq_false]
  have li1 : u1.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by
    rw [lo1 sI (by decide)]; exact hk.li
  rw [ite_word u1 _ _ _ _ (eval_lower u1 (vv sI) (vv sE2) j.toNat E.toNat (by omega) (by omega)
    (eval_vv u1 sI _ li1) (eval_vv u1 sE2 _ le1))]
  by_cases hjE0 : ¬ j.toNat < E.toNat
  · simp only [bw, hjE0, ↓reduceIte, ne_eq, not_true_eq_false]; exact Or.inl (stop_hang u1)
  have hjE : j.toNat < E.toNat := by omega
  simp only [bw, hjE, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
  have hR' : objLoop sp b E false (seen ||| bit) slots = R := by
    rw [← hR]; unfold contAfter stepVal; simp only [← hE]
    have : (E == v) = false := beq_eq_false_iff_ne.mpr (fun h => hEv (by rw [h]))
    rw [this]; simp only [Bool.false_eq_true, ↓reduceIte, applyUpd]
    rw [if_pos (USize.lt_iff_toNat_lt.mpr hjE)]
  obtain ⟨u3, hu3, hI⟩ := adv_from_ctx sp nS t A b R u u1 j v E seen bit slots slots hk m1 d1 k1 g1 b1
    (fun y _ hy => lo1 y hy) le1
    (fun k hk' => by
      rw [lo1 _ (slotName_fixed k (by have := hk.short; omega) sE2 (by simp [fixedLocals]))]
      exact hk.slotsOK k hk') rfl (by omega) hn hR'
  rw [hu3]; exact Or.inr ⟨rfl, hI⟩

theorem act_binder (sp : ObjSpec) (nS : Nat) (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (R : ScanRes (List SVal)) (j v : USize) (seen bit : UInt32)
    (slots : List SVal) (u : PanSemStateFiniteExact 64 σ) (hk : KCtx t A b j v seen slots u) (hn : slots.length = nS)
    (hR : contAfter sp b j v seen bit slots .binder = R) :
    Stop (evaluateHOLFiniteState u (actCode bit .binder)).1 ∨
      ((evaluateHOLFiniteState u (actCode bit .binder)).1 = none ∧
        ObjI sp nS t A b R (evaluateHOLFiniteState u (actCode bit .binder)).2) := by
  have hL : b.size < 2 ^ 64 := hp.size
  have hroom := hp.room
  have hvb := hk.hv
  have hjb := hk.hj
  have hcu : ScanCodes u := hc.congr hk.code
  obtain ⟨e0, le0⟩ := hk.scratch sE2 (by simp)
  have hcall := call3_retP u sE2 fBinder sB sN sI biFun (vv sB) (vv sN) (vv sV) A
    (BitVec.ofNat 64 b.size) (BitVec.ofNat 64 v.toNat) e0 _
    (by decide) (by decide) (by decide) hcu.2.2.2.2.2.2.1 (eval_vv u sB _ hk.lb) (eval_vv u sN _ hk.ln)
    (eval_vv u sV _ hk.lv) le0
    (fun callee h1 h2 h3 => biFun_sound (callEntryStateHOLFinite u callee) A b hp
      (bytesAt_congr hb (by exact hk.mem) (by exact hk.dom) (by exact hk.be)) v (by omega) h1 h2 h3)
  simp only [actCode, callTo]
  rcases hcall with hs | ⟨w, u1, ⟨E, rfl, hbi, hE0⟩, hu1, m1, d1, g1, k1, b1, le1, lo1⟩
  · exact Or.inl (seq_stop u _ _ hs)
  rw [seq_normal _ hu1]
  have hv16 : ∀ k : Nat, k ≤ 16 → (v + USize.ofNat k).toNat = v.toNat + k := fun k hk =>
    usize_add_toNat hp.bits v k (by omega)
  have hEl : E.toNat ≤ v.toNat + 16 := by
    rw [← hbi]; unfold ConLeche.Frontend.scanBinderInfo
    split
    · simp
    split
    · rw [show (v + 9) = v + USize.ofNat 9 from rfl, hv16 9 (by decide)]; omega
    split
    · rw [show (v + 10) = v + USize.ofNat 10 from rfl, hv16 10 (by decide)]; omega
    split
    · rw [show (v + 16) = v + USize.ofNat 16 from rfl, hv16 16 (by decide)]; omega
    split
    · rw [show (v + 14) = v + USize.ofNat 14 from rfl, hv16 14 (by decide)]; omega
    · simp
  have li1 : u1.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by
    rw [lo1 sI (by decide)]; exact hk.li
  rw [ite_word u1 _ _ _ _ (eval_lower u1 (vv sI) (vv sE2) j.toNat E.toNat (by omega) (by omega)
    (eval_vv u1 sI _ li1) (eval_vv u1 sE2 _ le1))]
  by_cases hjE0 : ¬ j.toNat < E.toNat
  · simp only [bw, hjE0, ↓reduceIte, ne_eq, not_true_eq_false]; exact Or.inl (stop_hang u1)
  have hjE : j.toNat < E.toNat := by omega
  simp only [bw, hjE, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
  have hR' : objLoop sp b E false (seen ||| bit) slots = R := by
    rw [← hR]; unfold contAfter stepVal; simp only [hbi]
    have : (E == 0) = false := beq_eq_false_iff_ne.mpr hE0
    rw [this]; simp only [Bool.false_eq_true, ↓reduceIte, applyUpd]
    rw [if_pos (USize.lt_iff_toNat_lt.mpr hjE)]
  obtain ⟨u3, hu3, hI⟩ := adv_from_ctx sp nS t A b R u u1 j v E seen bit slots slots hk m1 d1 k1 g1 b1
    (fun y _ hy => lo1 y hy) le1
    (fun k hk' => by
      rw [lo1 _ (slotName_fixed k (by have := hk.short; omega) sE2 (by simp [fixedLocals]))]
      exact hk.slotsOK k hk') rfl (by omega) hn hR'
  rw [hu3]; exact Or.inr ⟨rfl, hI⟩
end

section
variable {σ : Type}

theorem act_natListDrop (sp : ObjSpec) (nS : Nat) (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (R : ScanRes (List SVal)) (j v : USize) (seen bit : UInt32)
    (slots : List SVal) (u : PanSemStateFiniteExact 64 σ) (hk : KCtx t A b j v seen slots u) (hn : slots.length = nS)
    (hR : contAfter sp b j v seen bit slots (.natListDrop) = R) :
    Stop (evaluateHOLFiniteState u (actCode bit (.natListDrop))).1 ∨
      ((evaluateHOLFiniteState u (actCode bit (.natListDrop))).1 = none ∧
        ObjI sp nS t A b R (evaluateHOLFiniteState u (actCode bit (.natListDrop))).2) := by
  have hL : b.size < 2 ^ 64 := hp.size
  have hroom := hp.room
  have hvb := hk.hv
  have hjb := hk.hj
  have hcu : ScanCodes u := hc.congr hk.code
  obtain ⟨e0, le0⟩ := hk.scratch sE2 (by simp)
  have hcall := call3_retP u sE2 fNatList sB sN sI nlFun (vv sB) (vv sN) (vv sV) A
    (BitVec.ofNat 64 b.size) (BitVec.ofNat 64 v.toNat) e0 _
    (by decide) (by decide) (by decide) hcu.2.2.2.2.2.2.2.1 (eval_vv u sB _ hk.lb) (eval_vv u sN _ hk.ln)
    (eval_vv u sV _ hk.lv) le0
    (fun callee h1 h2 h3 => nlFun_sound (callEntryStateHOLFinite u callee) A b hp
      (bytesAt_congr hb (by exact hk.mem) (by exact hk.dom) (by exact hk.be)) v hk.hv
      (hcu.entry rfl callee).2.2.2.2.1 (hcu.entry rfl callee).2.1 h1 h2 h3)
  simp only [actCode, callTo]
  rcases hcall with hs | ⟨w, u1, ⟨E, xs, rfl, hEl, hnl⟩, hu1, m1, d1, g1, k1, b1, le1, lo1⟩
  · exact Or.inl (seq_stop u _ _ hs)
  rw [seq_normal _ hu1]
  have li1 : u1.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by
    rw [lo1 sI (by decide)]; exact hk.li
  rw [ite_word u1 _ _ _ _ (eval_lower u1 (vv sI) (vv sE2) j.toNat E.toNat (by omega) (by omega)
    (eval_vv u1 sI _ li1) (eval_vv u1 sE2 _ le1))]
  by_cases hjE0 : ¬ j.toNat < E.toNat
  · simp only [bw, hjE0, ↓reduceIte, ne_eq, not_true_eq_false]; exact Or.inl (stop_hang u1)
  have hjE : j.toNat < E.toNat := by omega
  simp only [bw, hjE, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
  have hR' : objLoop sp b E false (seen ||| bit) slots = R := by
    rw [← hR]; unfold contAfter stepVal; simp only [hnl, applyUpd]
    rw [if_pos (USize.lt_iff_toNat_lt.mpr hjE)]
  obtain ⟨u3, hu3, hI⟩ := adv_from_ctx sp nS t A b R u u1 j v E seen bit slots slots hk m1 d1 k1 g1 b1
    (fun y _ hy => lo1 y hy) le1
    (fun k hk' => by
      rw [lo1 _ (slotName_fixed k (by have := hk.short; omega) sE2 (by simp [fixedLocals]))]
      exact hk.slotsOK k hk') rfl (by omega) hn hR'
  rw [hu3]; exact Or.inr ⟨rfl, hI⟩

theorem act_natList (sp : ObjSpec) (nS : Nat) (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (R : ScanRes (List SVal)) (j v : USize) (seen bit : UInt32)
    (slots : List SVal) (sl : Nat) (hsl : sl < slots.length) (u : PanSemStateFiniteExact 64 σ) (hk : KCtx t A b j v seen slots u) (hn : slots.length = nS)
    (hR : contAfter sp b j v seen bit slots (.natList sl) = R) :
    Stop (evaluateHOLFiniteState u (actCode bit (.natList sl))).1 ∨
      ((evaluateHOLFiniteState u (actCode bit (.natList sl))).1 = none ∧
        ObjI sp nS t A b R (evaluateHOLFiniteState u (actCode bit (.natList sl))).2) := by
  have hL : b.size < 2 ^ 64 := hp.size
  have hroom := hp.room
  have hvb := hk.hv
  have hjb := hk.hj
  have hcu : ScanCodes u := hc.congr hk.code
  obtain ⟨e0, le0⟩ := hk.scratch sE2 (by simp)
  have hcall := call3_retP u sE2 fNatList sB sN sI nlFun (vv sB) (vv sN) (vv sV) A
    (BitVec.ofNat 64 b.size) (BitVec.ofNat 64 v.toNat) e0 _
    (by decide) (by decide) (by decide) hcu.2.2.2.2.2.2.2.1 (eval_vv u sB _ hk.lb) (eval_vv u sN _ hk.ln)
    (eval_vv u sV _ hk.lv) le0
    (fun callee h1 h2 h3 => nlFun_sound (callEntryStateHOLFinite u callee) A b hp
      (bytesAt_congr hb (by exact hk.mem) (by exact hk.dom) (by exact hk.be)) v hk.hv
      (hcu.entry rfl callee).2.2.2.2.1 (hcu.entry rfl callee).2.1 h1 h2 h3)
  simp only [actCode, callTo]
  rcases hcall with hs | ⟨w, u1, ⟨E, xs, rfl, hEl, hnl⟩, hu1, m1, d1, g1, k1, b1, le1, lo1⟩
  · exact Or.inl (seq_stop u _ _ hs)
  rw [seq_normal _ hu1]
  have li1 : u1.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by
    rw [lo1 sI (by decide)]; exact hk.li
  rw [ite_word u1 _ _ _ _ (eval_lower u1 (vv sI) (vv sE2) j.toNat E.toNat (by omega) (by omega)
    (eval_vv u1 sI _ li1) (eval_vv u1 sE2 _ le1))]
  by_cases hjE0 : ¬ j.toNat < E.toNat
  · simp only [bw, hjE0, ↓reduceIte, ne_eq, not_true_eq_false]; exact Or.inl (stop_hang u1)
  have hjE : j.toNat < E.toNat := by omega
  simp only [bw, hjE, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
  have hR' : objLoop sp b E false (seen ||| bit) (slots.set sl (.l xs)) = R := by
    rw [← hR]; unfold contAfter stepVal; simp only [hnl, applyUpd]
    rw [if_pos (USize.lt_iff_toNat_lt.mpr hjE)]
  have hfx : ∀ x ∈ fixedLocals, slotName sl ≠ x := slotName_fixed sl (by have := hk.short; omega)
  obtain ⟨ws, lws⟩ : ∃ w, u1.locals.lookup (slotName sl) = some (.val (.word w)) := by
    obtain ⟨w, hw, -⟩ := hk.slotsOK sl hsl
    exact ⟨w, by rw [lo1 _ (hfx sE2 (by simp [fixedLocals]))]; exact hw⟩
  have lv1 : u1.locals.lookup sV = some (.val (.word (BitVec.ofNat 64 v.toNat))) := by
    rw [lo1 sV (by decide)]; exact hk.lv
  rw [seq_normal _ (ConsLoop.assign_local u1 (slotName sl) (vv sV) _ ws (eval_vv u1 sV _ lv1) lws)]
  let u2 := setVarHOLFinite (slotName sl) (.val (.word (BitVec.ofNat 64 v.toNat))) u1
  obtain ⟨u3, hu3, hI⟩ := adv_from_ctx sp nS t A b R u u2 j v E seen bit slots (slots.set sl (.l xs)) hk m1 d1 k1 g1 b1
    (fun y hy hne => by
      show (setVarHOLFinite _ _ u1).locals.lookup y = _
      rw [lookup_setVar_other _ _ (Ne.symm (hfx y hy)), lo1 y hne])
    (by show (setVarHOLFinite _ _ u1).locals.lookup sE2 = _
        rw [lookup_setVar_other _ _ (Ne.symm (hfx sE2 (by simp [fixedLocals])))]; exact le1)
    (fun k hk' => by
      simp only [List.length_set] at hk'
      by_cases hks : k = sl
      · subst hks
        refine ⟨_, lookup_setVar_same _ _ _, ?_⟩
        simp only [List.getElem_set_self, SlotOK]
        exact Or.inl ⟨v, E, rfl, hnl⟩
      · have hne : slotName k ≠ slotName sl := slotName_inj k (by have := hk.short; omega) sl
          (by have := hk.short; omega) hks
        obtain ⟨w, hw, hok⟩ := hk.slotsOK k hk'
        refine ⟨w, ?_, by rw [List.getElem_set_ne (Ne.symm hks)]; exact hok⟩
        show (setVarHOLFinite _ _ u1).locals.lookup _ = _
        rw [lookup_setVar_other _ _ hne, lo1 _ (slotName_fixed k (by have := hk.short; omega) sE2
          (by simp [fixedLocals]))]
        exact hw)
    (by simp) (by omega) hn hR'
  rw [hu3]; exact Or.inr ⟨rfl, hI⟩

theorem act_hints (sp : ObjSpec) (nS : Nat) (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray)
    (R : ScanRes (List SVal)) (bit : UInt32) (sl : Nat) (u : PanSemStateFiniteExact 64 σ) :
    Stop (evaluateHOLFiniteState u (actCode bit (.hints sl))).1 ∨
      ((evaluateHOLFiniteState u (actCode bit (.hints sl))).1 = none ∧
        ObjI sp nS t A b R (evaluateHOLFiniteState u (actCode bit (.hints sl))).2) :=
  Or.inl (by simp only [actCode]; exact stop_hang u)

end

section
variable {σ : Type}

theorem act_boolDrop (sp : ObjSpec) (nS : Nat) (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (R : ScanRes (List SVal)) (j v : USize) (seen bit : UInt32)
    (slots : List SVal) (u : PanSemStateFiniteExact 64 σ) (hk : KCtx t A b j v seen slots u) (hn : slots.length = nS)
    (hR : contAfter sp b j v seen bit slots (.boolDrop) = R) :
    Stop (evaluateHOLFiniteState u (actCode bit (.boolDrop))).1 ∨
      ((evaluateHOLFiniteState u (actCode bit (.boolDrop))).1 = none ∧
        ObjI sp nS t A b R (evaluateHOLFiniteState u (actCode bit (.boolDrop))).2) := by
  have hL : b.size < 2 ^ 64 := hp.size
  have hroom := hp.room
  have hvb := hk.hv
  have hjb := hk.hj
  have hcu : ScanCodes u := hc.congr hk.code
  obtain ⟨e0, le0⟩ := hk.scratch sE2 (by simp)
  have hcall := call3_retP u sE2 fBool sB sN sI sbFun (vv sB) (vv sN) (vv sV) A
    (BitVec.ofNat 64 b.size) (BitVec.ofNat 64 v.toNat) e0 _
    (by decide) (by decide) (by decide) hcu.2.2.2.2.2.2.2.2.2.1 (eval_vv u sB _ hk.lb) (eval_vv u sN _ hk.ln)
    (eval_vv u sV _ hk.lv) le0
    (fun callee h1 h2 h3 => sbFun_sound (callEntryStateHOLFinite u callee) A b hp
      (bytesAt_congr hb (by exact hk.mem) (by exact hk.dom) (by exact hk.be)) v (by omega) h1 h2 h3)
  simp only [actCode, callTo]
  rcases hcall with hs | ⟨w, u1, ⟨E, x, rfl, hsb⟩, hu1, m1, d1, g1, k1, b1, le1, lo1⟩
  · exact Or.inl (seq_stop u _ _ hs)
  rw [seq_normal _ hu1]
  obtain ⟨hEb, hx⟩ := scanBool_facts hp v hk.hv hsb
  have li1 : u1.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by
    rw [lo1 sI (by decide)]; exact hk.li
  rw [ite_word u1 _ _ _ _ (eval_lower u1 (vv sI) (vv sE2) j.toNat E.toNat (by omega) (by omega)
    (eval_vv u1 sI _ li1) (eval_vv u1 sE2 _ le1))]
  by_cases hjE0 : ¬ j.toNat < E.toNat
  · simp only [bw, hjE0, ↓reduceIte, ne_eq, not_true_eq_false]; exact Or.inl (stop_hang u1)
  have hjE : j.toNat < E.toNat := by omega
  simp only [bw, hjE, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
  have hR' : objLoop sp b E false (seen ||| bit) slots = R := by
    rw [← hR]; unfold contAfter stepVal; simp only [hsb, applyUpd]
    rw [if_pos (USize.lt_iff_toNat_lt.mpr hjE)]
  obtain ⟨u3, hu3, hI⟩ := adv_from_ctx sp nS t A b R u u1 j v E seen bit slots slots hk m1 d1 k1 g1 b1
    (fun y _ hy => lo1 y hy) le1
    (fun k hk' => by
      rw [lo1 _ (slotName_fixed k (by have := hk.short; omega) sE2 (by simp [fixedLocals]))]
      exact hk.slotsOK k hk') rfl (by omega) hn hR'
  rw [hu3]; exact Or.inr ⟨rfl, hI⟩

theorem act_bool (sp : ObjSpec) (nS : Nat) (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (R : ScanRes (List SVal)) (j v : USize) (seen bit : UInt32)
    (slots : List SVal) (sl : Nat) (hsl : sl < slots.length) (u : PanSemStateFiniteExact 64 σ) (hk : KCtx t A b j v seen slots u) (hn : slots.length = nS)
    (hR : contAfter sp b j v seen bit slots (.bool sl) = R) :
    Stop (evaluateHOLFiniteState u (actCode bit (.bool sl))).1 ∨
      ((evaluateHOLFiniteState u (actCode bit (.bool sl))).1 = none ∧
        ObjI sp nS t A b R (evaluateHOLFiniteState u (actCode bit (.bool sl))).2) := by
  have hL : b.size < 2 ^ 64 := hp.size
  have hroom := hp.room
  have hvb := hk.hv
  have hjb := hk.hj
  have hcu : ScanCodes u := hc.congr hk.code
  obtain ⟨e0, le0⟩ := hk.scratch sE2 (by simp)
  have hcall := call3_retP u sE2 fBool sB sN sI sbFun (vv sB) (vv sN) (vv sV) A
    (BitVec.ofNat 64 b.size) (BitVec.ofNat 64 v.toNat) e0 _
    (by decide) (by decide) (by decide) hcu.2.2.2.2.2.2.2.2.2.1 (eval_vv u sB _ hk.lb) (eval_vv u sN _ hk.ln)
    (eval_vv u sV _ hk.lv) le0
    (fun callee h1 h2 h3 => sbFun_sound (callEntryStateHOLFinite u callee) A b hp
      (bytesAt_congr hb (by exact hk.mem) (by exact hk.dom) (by exact hk.be)) v (by omega) h1 h2 h3)
  simp only [actCode, callTo]
  rcases hcall with hs | ⟨w, u1, ⟨E, x, rfl, hsb⟩, hu1, m1, d1, g1, k1, b1, le1, lo1⟩
  · exact Or.inl (seq_stop u _ _ hs)
  rw [seq_normal _ hu1]
  obtain ⟨hEb, hx⟩ := scanBool_facts hp v hk.hv hsb
  have li1 : u1.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by
    rw [lo1 sI (by decide)]; exact hk.li
  rw [ite_word u1 _ _ _ _ (eval_lower u1 (vv sI) (vv sE2) j.toNat E.toNat (by omega) (by omega)
    (eval_vv u1 sI _ li1) (eval_vv u1 sE2 _ le1))]
  by_cases hjE0 : ¬ j.toNat < E.toNat
  · simp only [bw, hjE0, ↓reduceIte, ne_eq, not_true_eq_false]; exact Or.inl (stop_hang u1)
  have hjE : j.toNat < E.toNat := by omega
  simp only [bw, hjE, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
  have hR' : objLoop sp b E false (seen ||| bit) (slots.set sl (.b x)) = R := by
    rw [← hR]; unfold contAfter stepVal; simp only [hsb, applyUpd]
    rw [if_pos (USize.lt_iff_toNat_lt.mpr hjE)]
  have hfx : ∀ x ∈ fixedLocals, slotName sl ≠ x := slotName_fixed sl (by have := hk.short; omega)
  obtain ⟨ws, lws⟩ : ∃ w, u1.locals.lookup (slotName sl) = some (.val (.word w)) := by
    obtain ⟨w, hw, -⟩ := hk.slotsOK sl hsl
    exact ⟨w, by rw [lo1 _ (hfx sE2 (by simp [fixedLocals]))]; exact hw⟩
  have lv1 : u1.locals.lookup sV = some (.val (.word (BitVec.ofNat 64 v.toNat))) := by
    rw [lo1 sV (by decide)]; exact hk.lv
  have e2 := bAt_spec u1 A b.data.toList (slotName sl) (vv sV) v.toNat
    (bytesAt_congr hb (m1.trans hk.mem) (d1.trans hk.dom) (b1.trans hk.be)) (by omega) ws lws
    (by rw [lo1 sB (by decide)]; exact hk.lb) (by rw [lo1 sN (by decide)]; simpa using hk.ln) (eval_vv u1 sV _ lv1)
  rw [seq_normal _ e2]
  let u2 := setVarHOLFinite (slotName sl) (.val (.word (BitVec.ofNat 64 (byteL b.data.toList v.toNat).toNat))) u1
  have lsl2 : u2.locals.lookup (slotName sl) =
      some (.val (.word (BitVec.ofNat 64 (byteL b.data.toList v.toNat).toNat))) := lookup_setVar_same _ _ _
  have hcmp := eval_eq_c u2 (slotName sl) (byteL b.data.toList v.toNat).toNat 116
    (by have := UInt8.toNat_lt (byteL b.data.toList v.toNat); omega) (by decide) lsl2
  simp only [show (116 : BitVec 64) = BitVec.ofNat 64 116 from rfl] at *
  rw [seq_normal _ (ConsLoop.assign_local u2 (slotName sl) _ _ _ hcmp lsl2)]
  let u3 := setVarHOLFinite (slotName sl) (.val (.word (bw ((byteL b.data.toList v.toNat).toNat = 116)))) u2
  obtain ⟨u4, hu4, hI⟩ := adv_from_ctx sp nS t A b R u u3 j v E seen bit slots (slots.set sl (.b x)) hk m1 d1 k1 g1 b1
    (fun y hy hne => by
      show (setVarHOLFinite _ _ (setVarHOLFinite _ _ u1)).locals.lookup y = _
      rw [lookup_setVar_other _ _ (Ne.symm (hfx y hy)), lookup_setVar_other _ _ (Ne.symm (hfx y hy)), lo1 y hne])
    (by show (setVarHOLFinite _ _ (setVarHOLFinite _ _ u1)).locals.lookup sE2 = _
        rw [lookup_setVar_other _ _ (Ne.symm (hfx sE2 (by simp [fixedLocals]))),
          lookup_setVar_other _ _ (Ne.symm (hfx sE2 (by simp [fixedLocals])))]; exact le1)
    (fun k hk' => by
      simp only [List.length_set] at hk'
      by_cases hks : k = sl
      · subst hks
        refine ⟨_, lookup_setVar_same _ _ _, ?_⟩
        simp only [List.getElem_set_self, SlotOK]
        cases x <;> simp_all [bw]
      · have hne : slotName k ≠ slotName sl := slotName_inj k (by have := hk.short; omega) sl
          (by have := hk.short; omega) hks
        obtain ⟨w, hw, hok⟩ := hk.slotsOK k hk'
        refine ⟨w, ?_, by rw [List.getElem_set_ne (Ne.symm hks)]; exact hok⟩
        show (setVarHOLFinite _ _ (setVarHOLFinite _ _ u1)).locals.lookup _ = _
        rw [lookup_setVar_other _ _ hne, lookup_setVar_other _ _ hne, lo1 _ (slotName_fixed k (by have := hk.short; omega) sE2
          (by simp [fixedLocals]))]
        exact hw)
    (by simp) (by omega) hn hR'
  rw [hu4]; exact Or.inr ⟨rfl, hI⟩

theorem act_str (sp : ObjSpec) (nS : Nat) (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (R : ScanRes (List SVal)) (j v : USize) (seen bit : UInt32)
    (slots : List SVal) (sl : Nat) (hsl : sl < slots.length) (u : PanSemStateFiniteExact 64 σ) (hk : KCtx t A b j v seen slots u) (hn : slots.length = nS)
    (hR : contAfter sp b j v seen bit slots (.str sl) = R) :
    Stop (evaluateHOLFiniteState u (actCode bit (.str sl))).1 ∨
      ((evaluateHOLFiniteState u (actCode bit (.str sl))).1 = none ∧
        ObjI sp nS t A b R (evaluateHOLFiniteState u (actCode bit (.str sl))).2) := by
  have hL : b.size < 2 ^ 64 := hp.size
  have hroom := hp.room
  have hvb := hk.hv
  have hjb := hk.hj
  have hcu : ScanCodes u := hc.congr hk.code
  obtain ⟨e0, le0⟩ := hk.scratch sE2 (by simp)
  have hcall := call3_retP u sE2 fStr sB sN sI ssFun (vv sB) (vv sN) (vv sV) A
    (BitVec.ofNat 64 b.size) (BitVec.ofNat 64 v.toNat) e0 _
    (by decide) (by decide) (by decide) hcu.2.2.2.2.2.2.2.2.1 (eval_vv u sB _ hk.lb) (eval_vv u sN _ hk.ln)
    (eval_vv u sV _ hk.lv) le0
    (fun callee h1 h2 h3 => ssFun_sound (callEntryStateHOLFinite u callee) A b hp
      (bytesAt_congr hb (by exact hk.mem) (by exact hk.dom) (by exact hk.be)) v hk.hv
      (hcu.entry rfl callee).2.2.2.1 h1 h2 h3)
  simp only [actCode, callTo]
  rcases hcall with hs | ⟨w, u1, ⟨e, rfl, hel, str, hss, -⟩, hu1, m1, d1, g1, k1, b1, le1', lo1⟩
  · exact Or.inl (seq_stop u _ _ hs)
  rw [seq_normal _ hu1]
  have he1 : (e + 1).toNat = e.toNat + 1 := ConLeche.Frontend.usizeStep b e ((hp.lt_iff e).mpr hel)
  obtain ⟨E, hE⟩ : ∃ E, E = e + 1 := ⟨_, rfl⟩
  rw [seq_normal _ (ConsLoop.assign_local u1 sE2 _ (BitVec.ofNat 64 E.toNat) _ (by
    rw [eval_add_c u1 sE2 _ _ le1', hE, he1]; congr 3; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add]; try omega) le1')]
  let u1' := setVarHOLFinite sE2 (.val (.word (BitVec.ofNat 64 E.toNat))) u1
  have le1 : u1'.locals.lookup sE2 = some (.val (.word (BitVec.ofNat 64 E.toNat))) := lookup_setVar_same _ _ _
  have lo1' : ∀ y, y ≠ sE2 → u1'.locals.lookup y = u.locals.lookup y := fun y hy => by
    show (setVarHOLFinite _ _ u1).locals.lookup y = _; rw [lookup_setVar_other _ _ hy, lo1 y hy]
  have hEb : E.toNat ≤ b.size := by rw [hE, he1]; omega
  clear lo1
  have li1 : u1'.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by
    rw [lo1' sI (by decide)]; exact hk.li
  rw [ite_word u1' _ _ _ _ (eval_lower u1' (vv sI) (vv sE2) j.toNat E.toNat (by omega) (by omega)
    (eval_vv u1' sI _ li1) (eval_vv u1' sE2 _ le1))]
  by_cases hjE0 : ¬ j.toNat < E.toNat
  · simp only [bw, hjE0, ↓reduceIte, ne_eq, not_true_eq_false]; exact Or.inl (stop_hang u1')
  have hjE : j.toNat < E.toNat := by omega
  simp only [bw, hjE, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
  have hR' : objLoop sp b E false (seen ||| bit) (slots.set sl (.s str)) = R := by
    rw [← hR]; unfold contAfter stepVal; simp only [hss, applyUpd, ← hE]
    rw [if_pos (USize.lt_iff_toNat_lt.mpr hjE)]
  have hfx : ∀ x ∈ fixedLocals, slotName sl ≠ x := slotName_fixed sl (by have := hk.short; omega)
  obtain ⟨ws, lws⟩ : ∃ w, u1'.locals.lookup (slotName sl) = some (.val (.word w)) := by
    obtain ⟨w, hw, -⟩ := hk.slotsOK sl hsl
    exact ⟨w, by rw [lo1' _ (hfx sE2 (by simp [fixedLocals]))]; exact hw⟩
  have lv1 : u1'.locals.lookup sV = some (.val (.word (BitVec.ofNat 64 v.toNat))) := by
    rw [lo1' sV (by decide)]; exact hk.lv
  rw [seq_normal _ (ConsLoop.assign_local u1' (slotName sl) (vv sV) _ ws (eval_vv u1' sV _ lv1) lws)]
  let u2 := setVarHOLFinite (slotName sl) (.val (.word (BitVec.ofNat 64 v.toNat))) u1'
  obtain ⟨u3, hu3, hI⟩ := adv_from_ctx sp nS t A b R u u2 j v E seen bit slots (slots.set sl (.s str)) hk m1 d1 k1 g1 b1
    (fun y hy hne => by
      show (setVarHOLFinite _ _ u1').locals.lookup y = _
      rw [lookup_setVar_other _ _ (Ne.symm (hfx y hy)), lo1' y hne])
    (by show (setVarHOLFinite _ _ u1').locals.lookup sE2 = _
        rw [lookup_setVar_other _ _ (Ne.symm (hfx sE2 (by simp [fixedLocals])))]; exact le1)
    (fun k hk' => by
      simp only [List.length_set] at hk'
      by_cases hks : k = sl
      · subst hks
        refine ⟨_, lookup_setVar_same _ _ _, ?_⟩
        simp only [List.getElem_set_self, SlotOK]
        exact Or.inl ⟨v, e + 1, rfl, hss⟩
      · have hne : slotName k ≠ slotName sl := slotName_inj k (by have := hk.short; omega) sl
          (by have := hk.short; omega) hks
        obtain ⟨w, hw, hok⟩ := hk.slotsOK k hk'
        refine ⟨w, ?_, by rw [List.getElem_set_ne (Ne.symm hks)]; exact hok⟩
        show (setVarHOLFinite _ _ u1').locals.lookup _ = _
        rw [lookup_setVar_other _ _ hne, lo1' _ (slotName_fixed k (by have := hk.short; omega) sE2
          (by simp [fixedLocals]))]
        exact hw)
    (by simp) (by omega) hn hR'
  rw [hu3]; exact Or.inr ⟨rfl, hI⟩

end

section
variable {σ : Type}

theorem act_spec (sp : ObjSpec) (nS : Nat) (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (R : ScanRes (List SVal)) (j v : USize) (seen bit : UInt32)
    (slots : List SVal) (a : VAct) (ha : ActOK slots.length a) (u : PanSemStateFiniteExact 64 σ)
    (hk : KCtx t A b j v seen slots u) (hn : slots.length = nS) (hR : contAfter sp b j v seen bit slots a = R) :
    Stop (evaluateHOLFiniteState u (actCode bit a)).1 ∨
      ((evaluateHOLFiniteState u (actCode bit a)).1 = none ∧
        ObjI sp nS t A b R (evaluateHOLFiniteState u (actCode bit a)).2) := by
  cases a with
  | natSet sl => exact act_natSet sp nS t A b hp hb hc R j v seen bit slots sl u hk hn ha hR
  | natDrop => exact act_natDrop sp nS t A b hp hb hc R j v seen bit slots u hk hn hR
  | binder => exact act_binder sp nS t A b hp hb hc R j v seen bit slots u hk hn hR
  | natList sl => exact act_natList sp nS t A b hp hb hc R j v seen bit slots sl ha u hk hn hR
  | natListDrop => exact act_natListDrop sp nS t A b hp hb hc R j v seen bit slots u hk hn hR
  | str sl => exact act_str sp nS t A b hp hb hc R j v seen bit slots sl ha u hk hn hR
  | bool sl => exact act_bool sp nS t A b hp hb hc R j v seen bit slots sl ha u hk hn hR
  | boolDrop => exact act_boolDrop sp nS t A b hp hb hc R j v seen bit slots u hk hn hR
  | hints sl => exact act_hints sp nS t A b R bit sl u

/-- The key branch of con-leche's loop, at the key `K`. -/
def keyBranch (sp : ObjSpec) (b : ByteArray) (j v : USize) (seen : UInt32) (slots : List SVal) (K : Key)
    (ks : List (Key × UInt32 × VAct)) : ScanRes (List SVal) :=
  match lookupKey K ks with
  | some (bit, a) =>
    if (seen &&& bit) != 0 then .err ⟨j.toNat, .duplicateKey⟩ else contAfter sp b j v seen bit slots a
  | none => .err ⟨j.toNat, .unknownKey⟩

theorem dispatch_spec (sp : ObjSpec) (nS : Nat) (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (R : ScanRes (List SVal)) (j v : USize) (seen : UInt32)
    (slots : List SVal) (K : Key) :
    ∀ (ks : List (Key × UInt32 × VAct)) (u : PanSemStateFiniteExact 64 σ),
      (∀ e ∈ ks, ActOK slots.length e.2.2) → KCtx t A b j v seen slots u → slots.length = nS →
      u.locals.lookup sKK = some (.val (.word (BitVec.ofNat 64 K.ctorIdx))) →
      keyBranch sp b j v seen slots K ks = R →
      Stop (evaluateHOLFiniteState u (dispatch ks)).1 ∨
        ((evaluateHOLFiniteState u (dispatch ks)).1 = none ∧
          ObjI sp nS t A b R (evaluateHOLFiniteState u (dispatch ks)).2) := by
  intro ks
  induction ks with
  | nil => intro u _ _ _ _ _; exact Or.inl (stop_hang u)
  | cons e r ih =>
    intro u hks hk hn lkk hR
    obtain ⟨k, bit, a⟩ := e
    unfold dispatch
    have hcmp := eval_eq_c u sKK K.ctorIdx k.ctorIdx (by have := key_ctorIdx_lt K; omega)
      (by have := key_ctorIdx_lt k; omega) lkk
    rw [ite_word u _ _ _ _ hcmp]
    by_cases hK : K.ctorIdx = k.ctorIdx
    · simp only [bw, hK, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
      have hKk : K = k := key_ctorIdx_inj hK
      subst hKk
      simp only [keyBranch, lookupKey, ↓reduceIte] at hR
      have hand : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
          (.cmp .notEqual (.op .and [vv sS, .const (BitVec.ofNat 64 bit.toNat)]) (.const 0)) =
          some (.val (.word (bw ((seen &&& bit).toNat ≠ 0)))) := by
        have hx : @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a))
            (.op .and [vv sS, .const (BitVec.ofNat 64 bit.toNat)]) =
            some (.val (.word (BitVec.ofNat 64 (seen &&& bit).toNat))) := by
          rw [← word_and_u32]
          simp [vv, evalHOLExact, evalListHOLExact, hk.ls, wordOpHOL, wordOp, valueIsWord, valueWord]
          change _ &&& (_ &&& BitVec.allOnes 64) = _
          rw [BitVec.and_allOnes]
        rw [ConsLoop.eval_cmp_of u .notEqual _ _ _ (BitVec.ofNat 64 0) hx (by simp [evalHOLExact])]
        have hlt : (seen &&& bit).toNat < 2 ^ 64 := by have := (seen &&& bit).toNat_lt; omega
        by_cases h0 : (seen &&& bit).toNat = 0
        · have e0 : (BitVec.ofNat 64 (seen &&& bit).toNat == BitVec.ofNat 64 0) = true := by rw [h0]; rfl
          simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e0, Bool.not_true, Bool.false_eq_true,
            ↓reduceIte, bw, h0, ne_eq, not_true_eq_false]
          rfl
        · have : ¬ BitVec.ofNat 64 (seen &&& bit).toNat = BitVec.ofNat 64 0 :=
            fun e => h0 ((ofNat_inj _ 0 hlt (by decide)).mp e)
          have e0 : (BitVec.ofNat 64 (seen &&& bit).toNat == BitVec.ofNat 64 0) = false := beq_eq_false_iff_ne.mpr this
          simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e0, Bool.not_false, ↓reduceIte, bw, h0, ne_eq,
            not_false_eq_true]
      rw [ite_word u _ _ _ _ hand]
      by_cases hd : (seen &&& bit).toNat ≠ 0
      · simp only [bw, hd, ne_eq, not_false_eq_true, ↓reduceIte, show ¬ (1 : BitVec 64) = 0 from by decide]
        exact Or.inl (stop_hang u)
      · simp only [bw, hd, ↓reduceIte, ne_eq, not_true_eq_false]
        have hd' : ((seen &&& bit) != 0) = false := by
          simp only [bne_eq_false_iff_eq]; apply UInt32.toNat_inj.mp; simpa using hd
        rw [hd'] at hR; simp only [Bool.false_eq_true, ↓reduceIte] at hR
        exact act_spec sp nS t A b hp hb hc R j v seen bit slots a (hks _ (List.mem_cons_self ..)) u hk hn hR
    · simp only [bw, hK, ↓reduceIte, ne_eq, not_true_eq_false]
      have hKk : K ≠ k := fun h => hK (by rw [h])
      simp only [keyBranch, lookupKey, hKk, ↓reduceIte] at hR
      exact ih u (fun e he => hks e (List.mem_cons_of_mem _ he)) hk hn lkk (by simp only [keyBranch]; exact hR)

end

section
variable {σ : Type}

theorem obj_step (sp : ObjSpec) (nS : Nat) (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray)
    (hp : Plat b) (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (R : ScanRes (List SVal))
    (hks : ∀ e ∈ sp.keys, ActOK nS e.2.2) (hn10 : nS ≤ 10)
    (u : PanSemStateFiniteExact 64 σ) (hu : ObjI sp nS t A b R u)
    (hg : u.locals.lookup sG = some (.val (.word 1))) :
    Stop (evaluateHOLFiniteState (decClockHOLFinite u) (objBody sp)).1 ∨
      ((evaluateHOLFiniteState (decClockHOLFinite u) (objBody sp)).1 = none ∧
        ObjI sp nS t A b R (evaluateHOLFiniteState (decClockHOLFinite u) (objBody sp)).2) := by
  obtain ⟨m0, d0, c0, g0, b0, lb, ln, scr, j, wm, seen, slots, hj, hlen, li, lw, ls, hsl, br⟩ := hu
  obtain ⟨_, hR⟩ := br.resolve_right (fun ⟨h0, _⟩ => by rw [hg] at h0; cases h0)
  have hL : b.size < 2 ^ 64 := hp.size
  have hroom := hp.room
  let v0 := decClockHOLFinite u
  have hlt := eval_lower v0 (vv sI) (vv sN) j.toNat b.size (by omega) hL
    (eval_vv v0 sI _ (by lk [v0]; exact li)) (eval_vv v0 sN _ (by lk [v0]; exact ln))
  unfold objBody
  rw [ite_word v0 _ _ _ _ hlt]
  by_cases hjl0 : ¬ j.toNat < b.size
  · simp only [bw, hjl0, ↓reduceIte, ne_eq, not_true_eq_false]; exact Or.inl (stop_hang v0)
  have hjl : j.toNat < b.size := by omega
  simp only [bw, hjl, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
  have hjl' : j.toNat < b.data.toList.length := by simpa using hjl
  have hju : j < b.usize := (hp.lt_iff j).mpr hjl
  have hj1 : (j + 1).toNat = j.toNat + 1 := ConLeche.Frontend.usizeStep b j hju
  have hbv : BytesAt v0 A b.data.toList := bytesAt_congr hb m0 d0 b0
  have haddr : @evalHOLExact 64 σ _ v0.toExact (fun a => Classical.propDecidable (v0.memaddrs a))
      (.op .add [vv sB, vv sI]) = some (.val (.word (A + BitVec.ofNat 64 j.toNat))) := by
    have lb' : v0.locals.lookup sB = some (.val (.word A)) := by lk [v0]; exact lb
    have li' : v0.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by lk [v0]; exact li
    simp [vv, evalHOLExact, evalListHOLExact, lb', li', wordOpHOL, wordOp, valueIsWord, valueWord]
  obtain ⟨wc, lc⟩ := scr sC (by simp)
  obtain ⟨c, hcx⟩ : ∃ c, c = b.data.toList[j.toNat] := ⟨_, rfl⟩
  rw [seq_normal _ (ConsLoop.assign_local v0 sC _ (BitVec.ofNat 64 c.toNat) wc
    (by rw [hcx]; exact eval_loadByte_bytes v0 _ A b.data.toList j.toNat hbv hjl' haddr) (by lk [v0]; exact lc))]
  let v1 := setVarHOLFinite sC (.val (.word (BitVec.ofNat 64 c.toNat))) v0
  have lc1 : v1.locals.lookup sC = some (.val (.word (BitVec.ofNat 64 c.toNat))) := by lk [v1]
  have li1 : v1.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by lk [v1, v0]; exact li
  have lw1 : v1.locals.lookup sW = some (.val (.word (bw (wm = true)))) := by lk [v1, v0]; exact lw
  have ls1 : v1.locals.lookup sS = some (.val (.word (BitVec.ofNat 64 seen.toNat))) := by lk [v1, v0]; exact ls
  have lg1 : v1.locals.lookup sG = some (.val (.word 1)) := by lk [v1, v0]; exact hg
  have hct : c.toNat < 256 := UInt8.toNat_lt c
  have hstep := objLoop.eq_1 sp b j wm seen slots
  rw [dif_pos hju, uget_eq b j hjl hju, ← hcx] at hstep
  simp only at hstep
  have hfx : ∀ k, k < nS → ∀ x ∈ fixedLocals, slotName k ≠ x := fun k hk => slotName_fixed k (by omega)
  -- slots survive assignments to fixed locals
  have hslv1 : ∀ k (hk : k < slots.length), ∃ w, v1.locals.lookup (slotName k) = some (.val (.word w)) ∧
      SlotOK b w slots[k] := fun k hk => by
    obtain ⟨w, hw, hok⟩ := hsl k hk
    refine ⟨w, ?_, hok⟩
    show (setVarHOLFinite _ _ v0).locals.lookup _ = _
    rw [lookup_setVar_other _ _ (hfx k (by omega) sC (by simp [fixedLocals]))]; lk [v0]; exact hw
  have hscr1 : ∀ x ∈ [sC, sK, sV, sKK, sE2], ∃ w, v1.locals.lookup x = some (.val (.word w)) := by
    intro x hx
    by_cases hxc : x = sC
    · subst hxc; exact ⟨_, lc1⟩
    · obtain ⟨w, hw⟩ := scr x hx
      exact ⟨w, by show (setVarHOLFinite _ _ v0).locals.lookup _ = _
                   rw [lookup_setVar_other _ _ hxc]; lk [v0]; exact hw⟩
  rw [ite_word v1 _ _ _ _ (wsTest_ok v1 c.toNat hct lc1)]
  by_cases hws : isWsN c.toNat = true
  · simp only [bw, hws, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    rw [incI, ConsLoop.assign_local v1 sI _ (BitVec.ofNat 64 (j + 1).toNat) _ (by
      rw [eval_add_c v1 sI _ _ li1, hj1]; congr 3; apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add]; try omega) li1]
    rw [isWs_eq, hws] at hstep; simp only [↓reduceIte] at hstep
    let w := setVarHOLFinite sI (.val (.word (BitVec.ofNat 64 (j + 1).toNat))) v1
    refine Or.inr ⟨rfl, m0, d0, c0, g0, b0, by lk [w, v1, v0]; exact lb, by lk [w, v1, v0]; exact ln, ?_,
      j + 1, wm, seen, slots, by omega, hlen, by lk [w], by lk [w]; exact lw1, by lk [w]; exact ls1, ?_,
      Or.inl ⟨by lk [w]; exact lg1, by rw [← hR, hstep]⟩⟩
    · intro x hx
      obtain ⟨wx, hwx⟩ := hscr1 x hx
      refine ⟨wx, ?_⟩
      have : x ≠ sI := by
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide
      show (setVarHOLFinite _ _ v1).locals.lookup _ = _
      rw [lookup_setVar_other _ _ this]; exact hwx
    · intro k hk
      obtain ⟨wx, hwx, hok⟩ := hslv1 k hk
      refine ⟨wx, ?_, hok⟩
      show (setVarHOLFinite _ _ v1).locals.lookup _ = _
      rw [lookup_setVar_other _ _ (hfx k (by omega) sI (by simp [fixedLocals]))]; exact hwx
  simp only [bw, hws, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]
  rw [isWs_eq] at hstep; simp only [hws, Bool.false_eq_true, ↓reduceIte] at hstep
  -- the new state's invariant, once the position and the flag are known
  have mk : ∀ (w : PanSemStateFiniteExact 64 σ) (j' : USize) (wm' : Bool),
      w.memory = v1.memory → w.memaddrs = v1.memaddrs → w.code = v1.code → w.globals = v1.globals →
      w.be = v1.be → (∀ y, y ∉ [sI, sW, sG] → w.locals.lookup y = v1.locals.lookup y) →
      j'.toNat ≤ b.size + 64 →
      w.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j'.toNat))) →
      w.locals.lookup sW = some (.val (.word (bw (wm' = true)))) →
      ((w.locals.lookup sG = some (.val (.word 1)) ∧ objLoop sp b j' wm' seen slots = R) ∨
       (w.locals.lookup sG = some (.val (.word 0)) ∧ R = .ok slots j')) →
      ObjI sp nS t A b R w := by
    intro w j' wm' a1 a2 a3 a4 a5 hlo hj' li' lw' hg'
    refine ⟨a1.trans m0, a2.trans d0, a3.trans c0, a4.trans g0, a5.trans b0,
      by rw [hlo sB (by decide)]; lk [v1, v0]; exact lb, by rw [hlo sN (by decide)]; lk [v1, v0]; exact ln, ?_,
      j', wm', seen, slots, hj', hlen, li', lw', by rw [hlo sS (by decide)]; exact ls1, ?_, hg'⟩
    · intro x hx
      obtain ⟨wx, hwx⟩ := hscr1 x hx
      refine ⟨wx, ?_⟩
      have : x ∉ [sI, sW, sG] := by
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide
      rw [hlo x this]; exact hwx
    · intro k hk
      obtain ⟨wx, hwx, hok⟩ := hslv1 k hk
      refine ⟨wx, ?_, hok⟩
      have : slotName k ∉ [sI, sW, sG] := by
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or]
        exact ⟨hfx k (by omega) sI (by simp [fixedLocals]), hfx k (by omega) sW (by simp [fixedLocals]),
          hfx k (by omega) sG (by simp [fixedLocals])⟩
      rw [hlo _ this]; exact hwx
  have hc125 := eval_eq_c v1 sC c.toNat 125 (by omega) (by decide) lc1
  simp only [show (125 : BitVec 64) = BitVec.ofNat 64 125 from rfl] at *
  rw [ite_word v1 _ _ _ _ hc125]
  by_cases h125 : c.toNat = 125
  · simp only [bw, h125, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    have hc' : (c == 125) = true := by
      rw [show (125 : UInt8) = UInt8.ofNat 125 from rfl, beq_ofNat c 125 (by decide)]; simp [h125]
    rw [hc'] at hstep; simp only [↓reduceIte] at hstep
    have hs0 : @evalHOLExact 64 σ _ v1.toExact (fun a => Classical.propDecidable (v1.memaddrs a))
        (.cmp .notEqual (vv sS) (.const 0)) = some (.val (.word (bw (seen.toNat ≠ 0)))) := by
      rw [ConsLoop.eval_cmp_of v1 .notEqual _ _ _ (BitVec.ofNat 64 0) (eval_vv v1 sS _ ls1) (by simp [evalHOLExact])]
      have hlt : seen.toNat < 2 ^ 64 := by have := seen.toNat_lt; omega
      by_cases h0 : seen.toNat = 0
      · have e0 : (BitVec.ofNat 64 seen.toNat == BitVec.ofNat 64 0) = true := by rw [h0]; rfl
        simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e0, Bool.not_true, Bool.false_eq_true, ↓reduceIte, bw,
          h0, ne_eq, not_true_eq_false]; rfl
      · have e0 : (BitVec.ofNat 64 seen.toNat == BitVec.ofNat 64 0) = false :=
          beq_eq_false_iff_ne.mpr (fun e => h0 ((ofNat_inj _ 0 hlt (by decide)).mp e))
        simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e0, Bool.not_false, ↓reduceIte, bw, h0, ne_eq,
          not_false_eq_true]
    have hand : @evalHOLExact 64 σ _ v1.toExact (fun a => Classical.propDecidable (v1.memaddrs a))
        (.op .and [vv sW, .cmp .notEqual (vv sS) (.const 0)]) = some (.val (.word (bw (wm = true ∧ seen.toNat ≠ 0)))) := by
      rw [evalHOLExact]; simp only [evalListHOLExact, eval_vv v1 sW _ lw1, hs0]
      simp [valueIsWord, valueWord, bw_and]
    rw [ite_word v1 _ _ _ _ hand]
    by_cases hbad : wm = true ∧ seen.toNat ≠ 0
    · simp only [bw, hbad, ne_eq, not_false_eq_true, and_self, ↓reduceIte, show ¬ (1 : BitVec 64) = 0 from by decide]
      exact Or.inl (stop_hang v1)
    simp only [bw, hbad, ↓reduceIte, ne_eq, not_true_eq_false]
    have hok1 : (wm && seen != 0) = false := by
      cases wm
      · rfl
      · simp only [Bool.true_and, bne_eq_false_iff_eq]
        apply UInt32.toNat_inj.mp; simp only [UInt32.toNat_zero]; by_cases h : seen.toNat = 0 <;> simp_all
    rw [hok1] at hstep; simp only [Bool.false_eq_true, ↓reduceIte] at hstep
    have hmask : @evalHOLExact 64 σ _ v1.toExact (fun a => Classical.propDecidable (v1.memaddrs a))
        (.cmp .notEqual (.op .and [vv sS, .const (BitVec.ofNat 64 sp.need.toNat)]) (.const (BitVec.ofNat 64 sp.need.toNat))) =
        some (.val (.word (bw ((seen &&& sp.need).toNat ≠ sp.need.toNat)))) := by
      have hx : @evalHOLExact 64 σ _ v1.toExact (fun a => Classical.propDecidable (v1.memaddrs a))
          (.op .and [vv sS, .const (BitVec.ofNat 64 sp.need.toNat)]) =
          some (.val (.word (BitVec.ofNat 64 (seen &&& sp.need).toNat))) := by
        rw [← word_and_u32]
        simp [vv, evalHOLExact, evalListHOLExact, ls1, wordOpHOL, wordOp, valueIsWord, valueWord]
        change _ &&& (_ &&& BitVec.allOnes 64) = _
        rw [BitVec.and_allOnes]
      rw [ConsLoop.eval_cmp_of v1 .notEqual _ _ (BitVec.ofNat 64 (seen &&& sp.need).toNat)
        (BitVec.ofNat 64 sp.need.toNat) hx (by simp [evalHOLExact])]
      have h1 : (seen &&& sp.need).toNat < 2 ^ 64 := by have := (seen &&& sp.need).toNat_lt; omega
      have h2 : sp.need.toNat < 2 ^ 64 := by have := sp.need.toNat_lt; omega
      by_cases he : (seen &&& sp.need).toNat = sp.need.toNat
      · rw [he]; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, bw]
      · have e0 : (BitVec.ofNat 64 (seen &&& sp.need).toNat == BitVec.ofNat 64 sp.need.toNat) = false :=
          beq_eq_false_iff_ne.mpr (fun e => he ((ofNat_inj _ _ h1 h2).mp e))
        simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e0, Bool.not_false, ↓reduceIte, bw, he, ne_eq,
          not_false_eq_true]
    rw [ite_word v1 _ _ _ _ hmask]
    by_cases hmiss : (seen &&& sp.need).toNat ≠ sp.need.toNat
    · simp only [bw, hmiss, ne_eq, not_false_eq_true, ↓reduceIte, show ¬ (1 : BitVec 64) = 0 from by decide]
      exact Or.inl (stop_hang v1)
    simp only [bw, hmiss, ↓reduceIte, ne_eq, not_true_eq_false]
    have hok2 : ((seen &&& sp.need) != sp.need) = false := by
      simp only [bne_eq_false_iff_eq]; apply UInt32.toNat_inj.mp; simpa using hmiss
    rw [hok2] at hstep; simp only [Bool.false_eq_true, ↓reduceIte] at hstep
    unfold incI
    rw [seq_normal _ (ConsLoop.assign_local v1 sI _ (BitVec.ofNat 64 (j + 1).toNat) _ (by
      rw [eval_add_c v1 sI _ _ li1, hj1]; congr 3; apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add]; try omega) li1)]
    let w1 := setVarHOLFinite sI (.val (.word (BitVec.ofNat 64 (j + 1).toNat))) v1
    rw [ConsLoop.assign_local w1 sG (.const 0) 0 1 (by simp [evalHOLExact]) (by lk [w1]; exact lg1)]
    refine Or.inr ⟨rfl, mk _ (j + 1) wm rfl rfl rfl rfl rfl (fun y hy => ?_) (by omega) (by lk [w1])
      (by lk [w1]; exact lw1) (Or.inr ⟨by lk, by rw [← hR, hstep]⟩)⟩
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at hy
    show (setVarHOLFinite _ _ (setVarHOLFinite _ _ v1)).locals.lookup y = _
    rw [lookup_setVar_other _ _ hy.2.2, lookup_setVar_other _ _ hy.1]
  simp only [bw, h125, ↓reduceIte, ne_eq, not_true_eq_false]
  have hc' : (c == 125) = false := by
    rw [show (125 : UInt8) = UInt8.ofNat 125 from rfl, beq_ofNat c 125 (by decide)]; simp [h125]
  rw [hc'] at hstep; simp only [Bool.false_eq_true, ↓reduceIte] at hstep
  have hc44 := eval_eq_c v1 sC c.toNat 44 (by omega) (by decide) lc1
  simp only [show (44 : BitVec 64) = BitVec.ofNat 64 44 from rfl] at *
  rw [ite_word v1 _ _ _ _ hc44]
  by_cases h44 : c.toNat = 44
  · simp only [bw, h44, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    have hc44' : (c == 44) = true := by
      rw [show (44 : UInt8) = UInt8.ofNat 44 from rfl, beq_ofNat c 44 (by decide)]; simp [h44]
    rw [hc44'] at hstep; simp only [↓reduceIte] at hstep
    rw [ite_word v1 _ _ _ _ (eval_vv v1 sW _ lw1)]
    cases wm
    · simp only [bw, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false] at hstep ⊢
      rw [seq_normal _ (ConsLoop.assign_local v1 sW (.const 1) 1 0 (by simp [evalHOLExact]) lw1)]
      let w1 := setVarHOLFinite sW (.val (.word 1)) v1
      have li2 : w1.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by lk [w1]; exact li1
      rw [incI, ConsLoop.assign_local w1 sI _ (BitVec.ofNat 64 (j + 1).toNat) _ (by
        rw [eval_add_c w1 sI _ _ li2, hj1]; congr 3; apply BitVec.eq_of_toNat_eq
        simp [BitVec.toNat_add]; try omega) li2]
      refine Or.inr ⟨rfl, mk _ (j + 1) true rfl rfl rfl rfl rfl (fun y hy => ?_) (by omega) (by lk)
        (by lk [w1]; rfl) (Or.inl ⟨by lk [w1]; exact lg1, by rw [← hR, hstep]⟩)⟩
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at hy
      show (setVarHOLFinite _ _ (setVarHOLFinite _ _ v1)).locals.lookup y = _
      rw [lookup_setVar_other _ _ hy.1, lookup_setVar_other _ _ hy.2.1]
    · simp only [bw, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
      exact Or.inl (stop_hang v1)
  simp only [bw, h44, ↓reduceIte, ne_eq, not_true_eq_false]
  have hc44' : (c == 44) = false := by
    rw [show (44 : UInt8) = UInt8.ofNat 44 from rfl, beq_ofNat c 44 (by decide)]; simp [h44]
  rw [hc44'] at hstep; simp only [Bool.false_eq_true, ↓reduceIte] at hstep
  have hc34 := eval_eq_c v1 sC c.toNat 34 (by omega) (by decide) lc1
  simp only [show (34 : BitVec 64) = BitVec.ofNat 64 34 from rfl] at *
  rw [ite_word v1 _ _ _ _ hc34]
  by_cases h34 : ¬ c.toNat = 34
  · simp only [bw, h34, ↓reduceIte, ne_eq, not_true_eq_false]; exact Or.inl (stop_hang v1)
  have h34' : c.toNat = 34 := by omega
  simp only [bw, h34', ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
  have hc34' : (c == 34) = true := by
    rw [show (34 : UInt8) = UInt8.ofNat 34 from rfl, beq_ofNat c 34 (by decide)]; simp [h34']
  rw [hc34'] at hstep; simp only [↓reduceIte] at hstep
  rw [ite_word v1 _ _ _ _ (eval_vv v1 sW _ lw1)]
  cases wm
  · simp only [bw, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false]; exact Or.inl (stop_hang v1)
  simp only [bw, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hstep
  have hcu : ScanCodes v1 := hc.congr c0
  simp only [keyPart, callTo]
  -- keyEnd
  obtain ⟨wk, lk0⟩ := hscr1 sK (by simp)
  have hcall1 := call3_ret v1 sK fKeyEnd sB sN sI keFun (vv sB) (vv sN) (.op .add [vv sI, .const 1]) A
    (BitVec.ofNat 64 b.size) (BitVec.ofNat 64 (j + 1).toNat) (BitVec.ofNat 64 (ConLeche.Frontend.keyEnd b (j + 1)).toNat) wk
    (by decide) (by decide) (by decide) hcu.2.2.2.2.2.2.2.2.2.2.1
    (eval_vv v1 sB _ (by lk [v1, v0]; exact lb)) (eval_vv v1 sN _ (by lk [v1, v0]; exact ln))
    (by rw [eval_add_c v1 sI _ _ li1, hj1]; congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; try omega)
    lk0
    (fun callee h1 h2 h3 => keyEnd_refines (callEntryStateHOLFinite v1 callee) A b hp
      (bytesAt_congr hb (by exact m0) (by exact d0) (by exact b0)) (j + 1) (by omega)
      (hcu.entry rfl callee).2.2.1 h1 h2 h3)
  rcases hcall1 with hs | ⟨u1, hu1, m1, d1, g1, k1, b1, lke, lo1⟩
  · exact Or.inl (seq_stop v1 _ _ hs)
  rw [seq_normal _ hu1]
  obtain ⟨ke, hke⟩ : ∃ ke, ke = ConLeche.Frontend.keyEnd b (j + 1) := ⟨_, rfl⟩
  rw [← hke] at lke hstep
  have hkeL := keyEnd_eq hp _ (j + 1) rfl
  rw [← hke, hj1] at hkeL
  have hz := eval_eq_c u1 sK ke.toNat 0 (usz_lt ke) (by decide) lke
  rw [show BitVec.ofNat 64 0 = (0 : BitVec 64) from rfl] at hz
  rw [ite_word u1 _ _ _ _ hz]
  by_cases hk0 : ke.toNat = 0
  · simp only [bw, hk0, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    exact Or.inl (stop_hang u1)
  simp only [bw, hk0, ↓reduceIte, ne_eq, not_true_eq_false]
  have hk0' : (ke == 0) = false := beq_eq_false_iff_ne.mpr (fun h => hk0 (by rw [h]; rfl))
  rw [hk0'] at hstep; simp only [Bool.false_eq_true, ↓reduceIte] at hstep
  obtain ⟨hkel, hjke⟩ := keyEndL_lt b.data.toList (j.toNat + 1) (by rw [← hkeL]; exact hk0)
  rw [← hkeL] at hkel hjke
  replace hkel : ke.toNat < b.size := by simpa using hkel
  have lof : ∀ y, y ≠ sK → u1.locals.lookup y = v1.locals.lookup y := lo1
  -- valueAt
  obtain ⟨wv, lv0⟩ := hscr1 sV (by simp)
  have hcall2 := call4_ret u1 sV fValueAt sB sN sI sK vaFun (vv sB) (vv sN) (vv sI) (vv sK) A
    (BitVec.ofNat 64 b.size) (BitVec.ofNat 64 j.toNat) (BitVec.ofNat 64 ke.toNat)
    (BitVec.ofNat 64 (ConLeche.Frontend.valueAt b j ke).toNat) wv (by decide)
    (by rw [k1]; exact hcu.2.2.2.2.2.2.2.2.2.2.2.1)
    (eval_vv u1 sB _ (by rw [lof sB (by decide)]; lk [v1, v0]; exact lb))
    (eval_vv u1 sN _ (by rw [lof sN (by decide)]; lk [v1, v0]; exact ln))
    (eval_vv u1 sI _ (by rw [lof sI (by decide)]; exact li1)) (eval_vv u1 sK _ lke)
    (by rw [lof sV (by decide)]; exact lv0)
    (fun callee h1 h2 h3 h4 => valueAt_refines (callEntryStateHOLFinite u1 callee) A b hp
      (bytesAt_congr hb (by exact m1.trans m0) (by exact d1.trans d0) (by exact b1.trans b0)) j ke hkel
      ((hcu.congr k1).entry rfl callee).1 h1 h2 h3 h4)
  rcases hcall2 with hs | ⟨u2, hu2, m2, d2, g2, k2, b2, lv2, lo2⟩
  · exact Or.inl (seq_stop u1 _ _ hs)
  rw [seq_normal _ hu2]
  obtain ⟨v, hv⟩ : ∃ v, v = ConLeche.Frontend.valueAt b j ke := ⟨_, rfl⟩
  rw [← hv] at lv2 hstep
  have hvL := valueAt_eq hp j ke hkel
  rw [← hv] at hvL
  have hvb : v.toNat ≤ b.size := by
    have := valueAtL_le b.data.toList j.toNat ke.toNat (by simp; omega) (by simpa using hkel)
    rw [hvL]; simpa using this
  have li2 : u2.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 j.toNat))) := by
    rw [lo2 sI (by decide), lof sI (by decide)]; exact li1
  rw [ite_word u2 _ _ _ _ (ConsLoop.eval_cmp_of u2 .equal (vv sV) (vv sI) _ _ (eval_vv u2 sV _ lv2)
    (eval_vv u2 sI _ li2)), bw_eq _ _ (by omega) (by omega)]
  by_cases hvj : v.toNat = j.toNat
  · simp only [bw, hvj, ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
    exact Or.inl (stop_hang u2)
  simp only [bw, hvj, ↓reduceIte, ne_eq, not_true_eq_false]
  have hvj' : (v == j) = false := beq_eq_false_iff_ne.mpr (fun h => hvj (by rw [h]))
  rw [hvj'] at hstep; simp only [Bool.false_eq_true, ↓reduceIte] at hstep
  -- keyAt
  obtain ⟨wq, lq0⟩ := hscr1 sKK (by simp)
  have hkl : (ke - (j + 1)).toNat = ke.toNat - (j.toNat + 1) := by
    rw [USize.toNat_sub_of_le, hj1]; rw [USize.le_iff_toNat_le, hj1]; omega
  have hcall3 := call4_ret u2 sKK fKeyAt sB sN sI sL kaFun (vv sB) (vv sN) (vv sI)
    (.op .sub [vv sK, .op .add [vv sI, .const 1]]) A (BitVec.ofNat 64 b.size) (BitVec.ofNat 64 j.toNat)
    (BitVec.ofNat 64 (ke - (j + 1)).toNat)
    (BitVec.ofNat 64 (ConLeche.Frontend.keyAt b j (ke - (j + 1))).ctorIdx) wq (by decide)
    (by rw [k2, k1]; exact hcu.2.2.2.2.2.2.2.2.2.2.2.2)
    (eval_vv u2 sB _ (by rw [lo2 sB (by decide), lof sB (by decide)]; lk [v1, v0]; exact lb))
    (eval_vv u2 sN _ (by rw [lo2 sN (by decide), lof sN (by decide)]; lk [v1, v0]; exact ln))
    (eval_vv u2 sI _ li2)
    (by
      have lk2 : u2.locals.lookup sK = some (.val (.word (BitVec.ofNat 64 ke.toNat))) := by
        rw [lo2 sK (by decide)]; exact lke
      simp [vv, evalHOLExact, evalListHOLExact, lk2, li2, wordOpHOL, wordOp, valueIsWord, valueWord]
      rw [hkl]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub, BitVec.toNat_add]; omega)
    (by rw [lo2 sKK (by decide), lof sKK (by decide)]; exact lq0)
    (fun callee h1 h2 h3 h4 => keyAt_refines (callEntryStateHOLFinite u2 callee) A b hp
      (bytesAt_congr hb (by exact m2.trans (m1.trans m0)) (by exact d2.trans (d1.trans d0))
        (by exact b2.trans (b1.trans b0))) j (ke - (j + 1)) (by omega) h1 h2 h3 h4)
  rcases hcall3 with hs | ⟨u3, hu3, m3, d3, g3, k3, b3, lq3, lo3⟩
  · exact Or.inl (seq_stop u2 _ _ hs)
  rw [seq_normal _ hu3]
  -- the dispatch, at the key context
  have lo : ∀ y, y ≠ sKK → y ≠ sV → y ≠ sK → u3.locals.lookup y = v1.locals.lookup y := fun y h1 h2 h3 => by
    rw [lo3 y h1, lo2 y h2, lof y h3]
  have hkc : KCtx t A b j v seen slots u3 :=
    { mem := m3.trans (m2.trans (m1.trans m0)), dom := d3.trans (d2.trans (d1.trans d0)),
      code := k3.trans (k2.trans (k1.trans c0)), glob := g3.trans (g2.trans (g1.trans g0)),
      be := b3.trans (b2.trans (b1.trans b0)),
      lb := by rw [lo sB (by decide) (by decide) (by decide)]; lk [v1, v0]; exact lb,
      ln := by rw [lo sN (by decide) (by decide) (by decide)]; lk [v1, v0]; exact ln,
      li := by rw [lo3 sI (by decide)]; exact li2,
      lv := by rw [lo3 sV (by decide)]; exact lv2,
      ls := by rw [lo sS (by decide) (by decide) (by decide)]; exact ls1,
      lg := by rw [lo sG (by decide) (by decide) (by decide)]; exact lg1,
      lw := ⟨_, by rw [lo sW (by decide) (by decide) (by decide)]; exact lw1⟩,
      scratch := by
        intro x hx
        simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl
        · exact ⟨_, by rw [lo sC (by decide) (by decide) (by decide)]; exact lc1⟩
        · exact ⟨_, by rw [lo3 sK (by decide), lo2 sK (by decide)]; exact lke⟩
        · exact ⟨_, by rw [lo3 sV (by decide)]; exact lv2⟩
        · exact ⟨_, lq3⟩
        · obtain ⟨we, le⟩ := hscr1 sE2 (by simp)
          exact ⟨we, by rw [lo sE2 (by decide) (by decide) (by decide)]; exact le⟩,
      slotsOK := fun k hk => by
        obtain ⟨wx, hwx, hok⟩ := hslv1 k hk
        refine ⟨wx, ?_, hok⟩
        rw [lo _ (hfx k (by omega) sKK (by simp [fixedLocals])) (hfx k (by omega) sV (by simp [fixedLocals]))
          (hfx k (by omega) sK (by simp [fixedLocals]))]; exact hwx,
      short := by omega, hj := hjl, hv := hvb }
  exact dispatch_spec sp nS t A b hp hb hc R j v seen slots _ sp.keys u3 (by rw [hlen]; exact hks) hkc hlen lq3
    (by rw [← hR, hstep]; rfl)

end

section
variable {σ : Type}

/-- **The Pancake object loop refines con-leche's**: from the invariant, it stops, or exits with
`go = 0`, where con-leche's loop has accepted the object (`R = .ok slots j`, the slots related). -/
theorem objLoopP_spec (sp : ObjSpec) (nS : Nat) (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray)
    (hp : Plat b) (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (R : ScanRes (List SVal))
    (hks : ∀ e ∈ sp.keys, ActOK nS e.2.2) (hn10 : nS ≤ 10)
    (u : PanSemStateFiniteExact 64 σ) (hu : ObjI sp nS t A b R u) :
    Stop (evaluateHOLFiniteState u (objLoopP sp)).1 ∨ ((evaluateHOLFiniteState u (objLoopP sp)).1 = none ∧
      ObjI sp nS t A b R (evaluateHOLFiniteState u (objLoopP sp)).2 ∧
      (evaluateHOLFiniteState u (objLoopP sp)).2.locals.lookup sG = some (.val (.word 0))) := by
  have := while_stop (vv sG) (objBody sp) (ObjI sp nS t A b R)
    (fun u => ObjI sp nS t A b R u ∧ u.locals.lookup sG = some (.val (.word 0)))
    (fun u hu => by
      obtain ⟨_, _, _, _, _, _, _, _, j, wm, seen, slots, _, _, _, _, _, _, br⟩ := id hu
      rcases br with ⟨hg, _⟩ | ⟨hg, _⟩
      · refine ⟨1, by simp [evalHOLFinite, vv, evalHOLExact, hg], fun h => absurd h (by decide), fun _ _ => ?_⟩
        exact obj_step sp nS t A b hp hb hc R hks hn10 u hu hg
      · exact ⟨0, by simp [evalHOLFinite, vv, evalHOLExact, hg], fun _ => ⟨hu, hg⟩, fun h => absurd rfl h⟩)
    u hu
  rcases this with h | ⟨h1, h2, h3⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2, h3⟩

end

/-! ## A record: the opening brace, then the loop -/

/-- `{ … }` at `i`: check the brace, step past it, run the loop.  The caller declares the locals and
sets `go = 1`, `want = 1`, `seen = 0` and the slots' initial words. -/
def objStmt (sp : ObjSpec) : ProgHOL 64 :=
  .seq (bAt sC (vv sI))
    (.ite (.cmp .equal (vv sC) (.const 123)) (.seq incI (objLoopP sp)) hang)

section
variable {σ : Type}

theorem objStmt_spec (sp : ObjSpec) (nS : Nat) (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray)
    (hp : Plat b) (hb : BytesAt t A b.data.toList) (hc : ScanCodes t)
    (hks : ∀ e ∈ sp.keys, ActOK nS e.2.2) (hn10 : nS ≤ 10)
    (i : USize) (hi : i.toNat ≤ b.size) (slots : List SVal) (hlen : slots.length = nS)
    (u : PanSemStateFiniteExact 64 σ)
    (m0 : u.memory = t.memory) (d0 : u.memaddrs = t.memaddrs) (c0 : u.code = t.code) (g0 : u.globals = t.globals)
    (b0 : u.be = t.be)
    (lb : u.locals.lookup sB = some (.val (.word A)))
    (ln : u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat))))
    (lg : u.locals.lookup sG = some (.val (.word 1)))
    (lw : u.locals.lookup sW = some (.val (.word 1)))
    (ls : u.locals.lookup sS = some (.val (.word 0)))
    (scr : ∀ x ∈ [sC, sK, sV, sKK, sE2], ∃ w, u.locals.lookup x = some (.val (.word w)))
    (hsl : ∀ k (hk : k < slots.length), ∃ w, u.locals.lookup (slotName k) = some (.val (.word w)) ∧
      SlotOK b w slots[k]) :
    Stop (evaluateHOLFiniteState u (objStmt sp)).1 ∨ ((evaluateHOLFiniteState u (objStmt sp)).1 = none ∧
      ∃ (j : USize) (slots' : List SVal),
        (if ConLeche.Frontend.byteAt b i == 123 then objLoop sp b (i + 1) true 0 slots
          else .err ⟨i.toNat, .expectedObject⟩) = .ok slots' j ∧
        ObjI sp nS t A b (.ok slots' j) (evaluateHOLFiniteState u (objStmt sp)).2 ∧
        (evaluateHOLFiniteState u (objStmt sp)).2.locals.lookup sG = some (.val (.word 0))) := by
  have hL : b.size < 2 ^ 64 := hp.size
  have hroom := hp.room
  obtain ⟨wc, lc⟩ := scr sC (by simp)
  have e1 := bAt_spec u A b.data.toList sC (vv sI) i.toNat (bytesAt_congr hb m0 d0 b0) (by omega) wc lc lb
    (by simpa using ln) (eval_vv u sI _ li)
  unfold objStmt
  rw [seq_normal _ e1]
  let u1 := setVarHOLFinite sC (.val (.word (BitVec.ofNat 64 (byteL b.data.toList i.toNat).toNat))) u
  have hcmp := eval_eq_c u1 sC (byteL b.data.toList i.toNat).toNat 123
    (by have := UInt8.toNat_lt (byteL b.data.toList i.toNat); omega) (by decide) (by lk [u1])
  simp only [show (123 : BitVec 64) = BitVec.ofNat 64 123 from rfl] at *
  rw [ite_word u1 _ _ _ _ hcmp]
  by_cases h123 : ¬ (byteL b.data.toList i.toNat).toNat = 123
  · simp only [bw, h123, ↓reduceIte, ne_eq, not_true_eq_false]; exact Or.inl (stop_hang u1)
  have h123' : (byteL b.data.toList i.toNat).toNat = 123 := by omega
  simp only [bw, h123', ↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
  have hil : i.toNat < b.size := by
    by_cases h : i.toNat < b.size
    · exact h
    · simp [byteL, List.getElem?_eq_none (by simp; omega : b.data.toList.length ≤ i.toNat)] at h123'
  have hi1 : (i + 1).toNat = i.toNat + 1 := ConLeche.Frontend.usizeStep b i ((hp.lt_iff i).mpr hil)
  have li1 : u1.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat))) := by lk [u1]; exact li
  unfold incI
  rw [seq_normal _ (ConsLoop.assign_local u1 sI _ (BitVec.ofNat 64 (i + 1).toNat) _ (by
    rw [eval_add_c u1 sI _ _ li1, hi1]; congr 3; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_add]; try omega) li1)]
  let u2 := setVarHOLFinite sI (.val (.word (BitVec.ofNat 64 (i + 1).toNat))) u1
  have hfx : ∀ k, k < nS → ∀ x ∈ fixedLocals, slotName k ≠ x := fun k hk => slotName_fixed k (by omega)
  have hbyte : (ConLeche.Frontend.byteAt b i == 123) = true := by
    rw [byteAt_eq hp, show (123 : UInt8) = UInt8.ofNat 123 from rfl, beq_ofNat _ 123 (by decide)]
    simpa [byteL] using h123'
  simp only [hbyte, ↓reduceIte]
  have h0 : ObjI sp nS t A b (objLoop sp b (i + 1) true 0 slots) u2 := by
    refine ⟨m0, d0, c0, g0, b0, by lk [u2, u1]; exact lb, by lk [u2, u1]; exact ln, ?_, i + 1, true, 0, slots,
      by omega, hlen, by lk [u2], by lk [u2, u1]; exact lw, by lk [u2, u1]; exact ls, ?_,
      Or.inl ⟨by lk [u2, u1]; exact lg, rfl⟩⟩
    · intro x hx
      by_cases hxc : x = sC
      · subst hxc; exact ⟨BitVec.ofNat 64 (byteL b.data.toList i.toNat).toNat, by lk [u2, u1]⟩
      · obtain ⟨w, hw⟩ := scr x hx
        have : x ≠ sI := by
          simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide
        exact ⟨w, by show (setVarHOLFinite _ _ (setVarHOLFinite _ _ u)).locals.lookup _ = _
                     rw [lookup_setVar_other _ _ this, lookup_setVar_other _ _ hxc]; exact hw⟩
    · intro k hk
      obtain ⟨w, hw, hok⟩ := hsl k hk
      refine ⟨w, ?_, hok⟩
      show (setVarHOLFinite _ _ (setVarHOLFinite _ _ u)).locals.lookup _ = _
      rw [lookup_setVar_other _ _ (hfx k (by omega) sI (by simp [fixedLocals])),
        lookup_setVar_other _ _ (hfx k (by omega) sC (by simp [fixedLocals]))]; exact hw
  rcases objLoopP_spec sp nS t A b hp hb hc _ hks hn10 u2 h0 with hs | ⟨hn, hI, hg⟩
  · exact Or.inl hs
  refine Or.inr ⟨hn, ?_⟩
  obtain ⟨m', d', c', g', b', lb', ln', scr', j, wm, seen, slots', hj', hlen', li', lw', ls', hsl', br⟩ := hI
  have hR := (br.resolve_left (fun ⟨h1, _⟩ => by rw [hg] at h1; cases h1)).2
  exact ⟨j, slots', hR, ⟨m', d', c', g', b', lb', ln', scr', j, wm, seen, slots', hj', hlen', li', lw', ls',
    hsl', Or.inr ⟨hg, rfl⟩⟩, hg⟩

end

/-! ## A record as a function -/

/-- Nested declarations of word locals. -/
def decsOf : List (MlS × BitVec 64) → ProgHOL 64 → ProgHOL 64
  | [], body => body
  | (x, w) :: r, body => .dec x .one (.const w) (decsOf r body)

section
variable {σ : Type}

theorem retP_decsOf (P : BitVec 64 → Prop) :
    ∀ (ds : List (MlS × BitVec 64)) (body : ProgHOL 64) (u : PanSemStateFiniteExact 64 σ),
      RetP (ds.foldl (fun s (x, w) => setVarHOLFinite x (.val (.word w)) s) u) body P →
      RetP u (decsOf ds body) P := by
  intro ds
  induction ds with
  | nil => intro body u h; exact h
  | cons d r ih =>
    intro body u h
    obtain ⟨x, w⟩ := d
    exact retP_dec (by simp [evalHOLExact]) (ih body _ h)

end

/-- The record function's locals: the loop's fixed locals and the slots, with their initial words. -/
def recLocals (inits : List (BitVec 64)) : List (MlS × BitVec 64) :=
  [(sG, 1), (sW, 1), (sS, 0), (sC, 0), (sK, 0), (sV, 0), (sKK, 0), (sE2, 0)] ++
    inits.zipIdx.map (fun (w, k) => (slotName k, w))

/-- `rec(b, n, i)`: the record at `i`; returns `ret` (its end, or one of its slots). -/
def recFun (sp : ObjSpec) (inits : List (BitVec 64)) (ret : ExpHOL 64) : ProgHOL 64 :=
  decsOf (recLocals inits) (.seq (objStmt sp) (.return ret))

section
variable {σ : Type}

/-- The record body's result: con-leche's record at `i` accepted, ending at `j`, with these slots. -/
def RecOut (sp : ObjSpec) (b : ByteArray) (i : USize) (slots : List SVal) (j : USize) (slots' : List SVal) : Prop :=
  (if ConLeche.Frontend.byteAt b i == 123 then objLoop sp b (i + 1) true 0 slots
    else .err ⟨i.toNat, .expectedObject⟩) = .ok slots' j

theorem recBody_spec (sp : ObjSpec) (nS : Nat) (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray)
    (hp : Plat b) (hb : BytesAt t A b.data.toList) (hc : ScanCodes t)
    (hks : ∀ e ∈ sp.keys, ActOK nS e.2.2) (hn10 : nS ≤ 10)
    (i : USize) (hi : i.toNat ≤ b.size) (slots : List SVal) (hlen : slots.length = nS)
    (x : MlS) (hx : x = sI ∨ ∃ k, k < nS ∧ x = slotName k)
    (u : PanSemStateFiniteExact 64 σ)
    (m0 : u.memory = t.memory) (d0 : u.memaddrs = t.memaddrs) (c0 : u.code = t.code) (g0 : u.globals = t.globals)
    (b0 : u.be = t.be)
    (lb : u.locals.lookup sB = some (.val (.word A)))
    (ln : u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : u.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat))))
    (lg : u.locals.lookup sG = some (.val (.word 1)))
    (lw : u.locals.lookup sW = some (.val (.word 1)))
    (ls : u.locals.lookup sS = some (.val (.word 0)))
    (scr : ∀ x ∈ [sC, sK, sV, sKK, sE2], ∃ w, u.locals.lookup x = some (.val (.word w)))
    (hsl : ∀ k (hk : k < slots.length), ∃ w, u.locals.lookup (slotName k) = some (.val (.word w)) ∧
      SlotOK b w slots[k]) :
    RetP u (.seq (objStmt sp) (.return (vv x))) (fun w => ∃ j slots', RecOut sp b i slots j slots' ∧
      j.toNat ≤ b.size + 64 ∧ (x = sI → w = BitVec.ofNat 64 j.toNat) ∧
      (∀ k (hk : k < slots'.length), x = slotName k → SlotOK b w slots'[k])) := by
  rcases objStmt_spec sp nS t A b hp hb hc hks hn10 i hi slots hlen u m0 d0 c0 g0 b0 lb ln li lg lw ls scr hsl with
    hs | ⟨hn, j, slots', hR, hI, hg⟩
  · exact Or.inl (seq_stop u _ _ hs)
  generalize he : evaluateHOLFiniteState u (objStmt sp) = r at hn hI hg
  obtain ⟨r1, r2⟩ := r
  simp only at hn hI hg
  subst hn
  obtain ⟨m', d', c', g', b', -, -, -, j', wm, seen, sl2, hj', hlen2, li', -, -, hsl2, br⟩ := hI
  have hR2 := (br.resolve_left (fun ⟨h1, _⟩ => by rw [hg] at h1; cases h1)).2
  simp only [ScanRes.ok.injEq] at hR2
  obtain ⟨rfl, rfl⟩ := hR2
  refine retP_seq he ?_ (m'.trans m0.symm) (d'.trans d0.symm) (g'.trans g0.symm) (c'.trans c0.symm)
    (b'.trans b0.symm)
  rcases hx with rfl | ⟨k, hk, rfl⟩
  · obtain ⟨q1, q2, q3, q4, q5, q6⟩ := return_vv r2 sI _ li'
    exact Or.inr ⟨_, q1, ⟨j, slots', hR, hj', fun _ => rfl, fun k hk h => absurd h (Ne.symm (slotName_fixed k
      (by omega) sI (by simp [fixedLocals])))⟩, q2, q3, q4, q5, q6⟩
  · obtain ⟨w, hw, hok⟩ := hsl2 k (by omega)
    obtain ⟨q1, q2, q3, q4, q5, q6⟩ := return_vv r2 (slotName k) _ hw
    refine Or.inr ⟨_, q1, ⟨j, slots', hR, hj', fun h => absurd h (slotName_fixed k (by omega) sI (by simp [fixedLocals])),
      fun k' hk' h => ?_⟩, q2, q3, q4, q5, q6⟩
    have : k' = k := by
      by_cases hkk : k' = k
      · exact hkk
      · exact absurd h (slotName_inj k (by omega) k' (by omega) (Ne.symm hkk))
    subst this; exact hok

end

section
variable {σ : Type}

theorem lookup_foldl_setVar (y : MlS) :
    ∀ (ds : List (MlS × BitVec 64)) (u : PanSemStateFiniteExact 64 σ),
      (ds.foldl (fun s (x, w) => setVarHOLFinite x (.val (.word w)) s) u).locals.lookup y =
        match (ds.reverse.find? (fun d => d.1 = y)) with
        | some d => some (.val (.word d.2))
        | none => u.locals.lookup y := by
  intro ds
  induction ds with
  | nil => intro u; simp
  | cons d ds ih =>
    intro u
    obtain ⟨x, w⟩ := d
    simp only [List.foldl_cons, List.reverse_cons, List.find?_append]
    rw [ih]
    cases hf : ds.reverse.find? (fun d => d.1 = y) with
    | some d => simp
    | none =>
      simp only [Option.none_or, List.find?_cons, List.find?_nil]
      by_cases hxy : x = y
      · subst hxy; simp [lookup_setVar_same]
      · simp [hxy, lookup_setVar_other _ _ (Ne.symm hxy)]

end

end ConPanqueque.Scan
