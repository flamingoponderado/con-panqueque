import ConPanqueque.Scan.IndList

/-! # The inductive record functions: code names, the code table they need, and their soundness

Design (see also `Scan/IndSpec.lean`):
* a record (`types`/`ctors`/`recs` members, recursor rules, the declaration itself) is read by
  `recFun spec inits ret`, the compiled object loop: `ret = vv sI` gives its end (`f{Rule,IndType,
  IndCtor,IndRec}` and the line-table entry `fRecInd`); `ret = vv (slotName k)` gives slot `k`
  (`fRuF k`, `fItF k`, `fIcF k`, `fIrF k`, `fIdF k`);
* a list of records is read by `olFun3 item ret`/`olFun4 item ret` (`Scan/IndList.lean`): its end
  (`subName 0..3`, the `.sub` callees of the rules/ctors/recs/types keys), its length
  (`f*N`) or the position of item `l` (`f*At`, the extra parameter `sL`).

All functions take the buffer address `sB`, its size `sN` and a position `sI`.  `IndCodes` lists
them; the line table needs `fRecInd`, which needs the rest. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

namespace ConPanqueque.Scan

open ConLeche.Frontend

def fRule := ofString "recRule"
def fIndType := ofString "recIndType"
def fIndCtor := ofString "recIndCtor"
def fIndRec := ofString "recIndRec"
def fRecInd := ofString "recInd"
def fRulesN := ofString "rulesCount"
def fIndCtorsN := ofString "indCtorsCount"
def fIndRecsN := ofString "indRecsCount"
def fIndTypesN := ofString "indTypesCount"
def fRulesAt := ofString "rulesAt"
def fIndCtorsAt := ofString "indCtorsAt"
def fIndRecsAt := ofString "indRecsAt"
def fIndTypesAt := ofString "indTypesAt"
/-- Slot `k` of the declaration record (`0` ctors, `1` recs, `2` types: list positions). -/
def fIdF (k : Nat) : MlS := ofString ("idf" ++ toString k)
/-- Slot `k` of a `types` member. -/
def fItF (k : Nat) : MlS := ofString ("itf" ++ toString k)
/-- Slot `k` of a `ctors` member. -/
def fIcF (k : Nat) : MlS := ofString ("icf" ++ toString k)
/-- Slot `k` of a `recs` member. -/
def fIrF (k : Nat) : MlS := ofString ("irf" ++ toString k)
/-- Slot `k` of a recursor rule. -/
def fRuF (k : Nat) : MlS := ofString ("ruf" ++ toString k)

/-- The slots of an accepted record (`objLoop_slots`). -/
def SlotsOK (b : ByteArray) (sp : ObjSpec) (slots0 slots' : List SVal) : Prop :=
  slots'.length = slots0.length ∧
  (∀ sl (h : sl < slots0.length) (h' : sl < slots'.length), slots'[sl] = slots0[sl] ∨ WrBy b sp sl slots'[sl]) ∧
  ∃ seen', (seen' &&& sp.need) = sp.need ∧ SeenWr b sp seen' slots'

def ruleInits : List (BitVec 64) := [0, 0, 0]
def ruleSlots0 : List SVal := [.n 0, .n 0, .n 0]
def indTypeInits : List (BitVec 64) := [BitVec.ofNat 64 listSentinel, 0, 0, 0, BitVec.ofNat 64 listSentinel, 0, 0, 0, 0, 0]
def indTypeSlots0 : List SVal := [.l [], .b false, .b false, .b false, .l [], .n 0, .n 0, .n 0, .n 0, .n 0]
def indCtorInits : List (BitVec 64) := [0, BitVec.ofNat 64 listSentinel, 0, 0, 0, 0, BitVec.ofNat 64 listSentinel, BitVec.ofNat 64 listSentinel]
def indCtorSlots0 : List SVal := [.b false, .l [], .n 0, .n 0, .n 0, .n 0, optSV none, optSV none]
def indRecInits : List (BitVec 64) := [0, 0, BitVec.ofNat 64 listSentinel, 0, 0, 0, 0, 0, 0, 0]
def indRecSlots0 : List SVal := [.b false, .b false, .l [], .n 0, .n 0, .n 0, .n 0, .n 0, .p (2 ^ 64), .n 0]
def indDeclInits : List (BitVec 64) := [0, 0, 0]
def indDeclSlots0 : List SVal := [.p (2 ^ 64), .p (2 ^ 64), .p (2 ^ 64)]

section
variable {σ : Type}

structure IndCodes (t : PanSemStateFiniteExact 64 σ) : Prop where
  rule : t.code.lookup fRule = some ([(sB, .one), (sN, .one), (sI, .one)], recFun ruleSpec ruleInits (vv sI), .one)
  ty : t.code.lookup fIndType = some ([(sB, .one), (sN, .one), (sI, .one)], recFun indTypeSpec indTypeInits (vv sI), .one)
  ctor : t.code.lookup fIndCtor = some ([(sB, .one), (sN, .one), (sI, .one)], recFun indCtorSpec indCtorInits (vv sI), .one)
  irec : t.code.lookup fIndRec = some ([(sB, .one), (sN, .one), (sI, .one)], recFun indRecSpec indRecInits (vv sI), .one)
  sub0 : t.code.lookup (subName 0) = some ([(sB, .one), (sN, .one), (sI, .one)], olFun3 fRule sI, .one)
  sub1 : t.code.lookup (subName 1) = some ([(sB, .one), (sN, .one), (sI, .one)], olFun3 fIndCtor sI, .one)
  sub2 : t.code.lookup (subName 2) = some ([(sB, .one), (sN, .one), (sI, .one)], olFun3 fIndRec sI, .one)
  sub3 : t.code.lookup (subName 3) = some ([(sB, .one), (sN, .one), (sI, .one)], olFun3 fIndType sI, .one)
  rulesN : t.code.lookup fRulesN = some ([(sB, .one), (sN, .one), (sI, .one)], olFun3 fRule sM, .one)
  ctorsN : t.code.lookup fIndCtorsN = some ([(sB, .one), (sN, .one), (sI, .one)], olFun3 fIndCtor sM, .one)
  recsN : t.code.lookup fIndRecsN = some ([(sB, .one), (sN, .one), (sI, .one)], olFun3 fIndRec sM, .one)
  typesN : t.code.lookup fIndTypesN = some ([(sB, .one), (sN, .one), (sI, .one)], olFun3 fIndType sM, .one)
  rulesAt : t.code.lookup fRulesAt = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], olFun4 fRule sR, .one)
  ctorsAt : t.code.lookup fIndCtorsAt = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], olFun4 fIndCtor sR, .one)
  recsAt : t.code.lookup fIndRecsAt = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], olFun4 fIndRec sR, .one)
  typesAt : t.code.lookup fIndTypesAt = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], olFun4 fIndType sR, .one)
  declF : ∀ k, k < 3 → t.code.lookup (fIdF k) = some ([(sB, .one), (sN, .one), (sI, .one)], recFun indDeclSpec indDeclInits (vv (slotName k)), .one)
  typeF : ∀ k, k < 10 → t.code.lookup (fItF k) = some ([(sB, .one), (sN, .one), (sI, .one)], recFun indTypeSpec indTypeInits (vv (slotName k)), .one)
  ctorF : ∀ k, k < 8 → t.code.lookup (fIcF k) = some ([(sB, .one), (sN, .one), (sI, .one)], recFun indCtorSpec indCtorInits (vv (slotName k)), .one)
  recF : ∀ k, k < 10 → t.code.lookup (fIrF k) = some ([(sB, .one), (sN, .one), (sI, .one)], recFun indRecSpec indRecInits (vv (slotName k)), .one)
  ruleF : ∀ k, k < 3 → t.code.lookup (fRuF k) = some ([(sB, .one), (sN, .one), (sI, .one)], recFun ruleSpec ruleInits (vv (slotName k)), .one)

theorem IndCodes.congr {t u : PanSemStateFiniteExact 64 σ} (h : IndCodes t) (hc : u.code = t.code) : IndCodes u := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18, a19, a20⟩ := h
  exact ⟨by rw [hc]; exact a0, by rw [hc]; exact a1, by rw [hc]; exact a2, by rw [hc]; exact a3, by rw [hc]; exact a4, by rw [hc]; exact a5, by rw [hc]; exact a6, by rw [hc]; exact a7, by rw [hc]; exact a8, by rw [hc]; exact a9, by rw [hc]; exact a10, by rw [hc]; exact a11, by rw [hc]; exact a12, by rw [hc]; exact a13, by rw [hc]; exact a14, by rw [hc]; exact a15, fun k hk => by rw [hc]; exact a16 k hk, fun k hk => by rw [hc]; exact a17 k hk, fun k hk => by rw [hc]; exact a18 k hk, fun k hk => by rw [hc]; exact a19 k hk, fun k hk => by rw [hc]; exact a20 k hk⟩



theorem rule_body (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t)  (i : USize) (hi : i.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat))))
    (x : MlS) (hx : x = sI ∨ ∃ k, k < 3 ∧ x = slotName k) :
    RetP t (recFun ruleSpec ruleInits (vv x)) (fun w => ∃ j slots', RecOut ruleSpec b i ruleSlots0 j slots' ∧
      j.toNat ≤ b.size + 64 ∧ (x = sI → w = BitVec.ofNat 64 j.toNat) ∧
      (∀ k (hk : k < slots'.length), x = slotName k → SlotOK b w slots'[k])) := by
  unfold recFun
  apply retP_decsOf
  have hlk := recEntry_lookup ruleInits t
  have hks : ∀ e ∈ ruleSpec.keys, ActOK 3 e.2.2 := by simp [ruleSpec, ActOK]
  exact recBody_spec (σ := σ) ruleSpec 3 t A b hp hb hc hks (by decide) i hi ruleSlots0 rfl x hx
    ((ruleInits |> recLocals).foldl (fun s (x, w) => setVarHOLFinite x (.val (.word w)) s) t) rfl rfl rfl rfl rfl
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, ruleInits]; exact lb)
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, ruleInits]; exact ln)
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, ruleInits]; exact li)
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, ruleInits])
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, ruleInits])
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, ruleInits])
    (by intro x hx; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, ruleInits]⟩)
    (by intro k hk; simp only [ruleSlots0, List.length_cons, List.length_nil] at hk
        rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, ruleInits], by simp [ruleSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, ruleInits], by simp [ruleSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, ruleInits], by simp [ruleSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩)

/-- The record's end: con-leche's `scanRule` accepts the record at `i` and ends there. -/
theorem ruleEnd_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t)  (i : USize) (hi : i.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat)))) :
    RetP t (recFun ruleSpec ruleInits (vv sI)) (fun w => ∃ (j : USize), w = BitVec.ofNat 64 j.toNat ∧
      j.toNat ≤ b.size + 64 ∧ ∃ r : RuleRec, scanRule b i = .ok r j) := by
  refine retP_mono (rule_body t A b hp hb hc  i hi lb ln li sI (Or.inl rfl)) ?_
  rintro w ⟨j, slots', hro, hjb, hw, -⟩
  refine ⟨j, hw rfl, hjb, ?_⟩
  unfold RecOut at hro
  simp only [ruleSlots0, indTypeSlots0, indCtorSlots0, indRecSlots0, indDeclSlots0] at hro
  have hq := scanRuleLoop_eq b _ (i + 1) true 0 0 0 0 rfl
  rw [scanRule, hq]
  split at hro
  · rename_i hbyte; rw [ite_eq_left hbyte, hro]; exact ⟨_, rfl⟩
  · simp at hro

/-- Slot `k` of the record: when con-leche reads the record as `r`, the word is slot `k` of a slot
list that builds `r`, each slot being its initial value or one the spec writes, every required key
written. -/
theorem ruleSlot_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t)  (i : USize) (hi : i.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat))))
    (k : Nat) (hk : k < 3) (r : RuleRec) (e0 : USize) (hd : scanRule b i = .ok r e0) :
    RetP t (recFun ruleSpec ruleInits (vv (slotName k))) (fun w => ∃ slots', r = ruleOf slots' ∧
      SlotsOK b ruleSpec ruleSlots0 slots' ∧ ∀ hk' : k < slots'.length, SlotOK b w slots'[k]) := by
  refine retP_mono (rule_body t A b hp hb hc  i hi lb ln li (slotName k) (Or.inr ⟨k, hk, rfl⟩)) ?_
  rintro w ⟨j, slots', hro, -, -, hsl⟩
  unfold RecOut at hro
  simp only [ruleSlots0, indTypeSlots0, indCtorSlots0, indRecSlots0, indDeclSlots0] at hro
  split at hro
  · rename_i hbyte
    have hq := scanRuleLoop_eq b _ (i + 1) true 0 0 0 0 rfl
    have hs : scanRule b i = .ok (ruleOf slots') j := by
      rw [scanRule, hq, ite_eq_left hbyte, hro]; rfl
    rw [hd] at hs
    simp only [ScanRes.ok.injEq] at hs
    exact ⟨slots', hs.1, objLoop_slots ruleSpec (by unfold BitsOK; decide) b _ (i + 1) true 0 _ rfl slots' j hro (seenWr_zero _ _ _),
      fun hk' => hsl k hk' rfl⟩
  · simp at hro



theorem indType_body (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t)  (i : USize) (hi : i.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat))))
    (x : MlS) (hx : x = sI ∨ ∃ k, k < 10 ∧ x = slotName k) :
    RetP t (recFun indTypeSpec indTypeInits (vv x)) (fun w => ∃ j slots', RecOut indTypeSpec b i indTypeSlots0 j slots' ∧
      j.toNat ≤ b.size + 64 ∧ (x = sI → w = BitVec.ofNat 64 j.toNat) ∧
      (∀ k (hk : k < slots'.length), x = slotName k → SlotOK b w slots'[k])) := by
  unfold recFun
  apply retP_decsOf
  have hlk := recEntry_lookup indTypeInits t
  have hks : ∀ e ∈ indTypeSpec.keys, ActOK 10 e.2.2 := by simp [indTypeSpec, ActOK]
  exact recBody_spec (σ := σ) indTypeSpec 10 t A b hp hb hc hks (by decide) i hi indTypeSlots0 rfl x hx
    ((indTypeInits |> recLocals).foldl (fun s (x, w) => setVarHOLFinite x (.val (.word w)) s) t) rfl rfl rfl rfl rfl
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indTypeInits]; exact lb)
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indTypeInits]; exact ln)
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indTypeInits]; exact li)
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indTypeInits])
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indTypeInits])
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indTypeInits])
    (by intro x hx; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indTypeInits]⟩)
    (by intro k hk; simp only [indTypeSlots0, List.length_cons, List.length_nil] at hk
        rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨BitVec.ofNat 64 listSentinel, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indTypeInits], by simp [indTypeSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indTypeInits], by simp [indTypeSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indTypeInits], by simp [indTypeSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indTypeInits], by simp [indTypeSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨BitVec.ofNat 64 listSentinel, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indTypeInits], by simp [indTypeSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indTypeInits], by simp [indTypeSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indTypeInits], by simp [indTypeSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indTypeInits], by simp [indTypeSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indTypeInits], by simp [indTypeSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indTypeInits], by simp [indTypeSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩)

/-- The record's end: con-leche's `scanIndType` accepts the record at `i` and ends there. -/
theorem indTypeEnd_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t)  (i : USize) (hi : i.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat)))) :
    RetP t (recFun indTypeSpec indTypeInits (vv sI)) (fun w => ∃ (j : USize), w = BitVec.ofNat 64 j.toNat ∧
      j.toNat ≤ b.size + 64 ∧ ∃ r : IndTypeRec, scanIndType b i = .ok r j) := by
  refine retP_mono (indType_body t A b hp hb hc  i hi lb ln li sI (Or.inl rfl)) ?_
  rintro w ⟨j, slots', hro, hjb, hw, -⟩
  refine ⟨j, hw rfl, hjb, ?_⟩
  unfold RecOut at hro
  simp only [ruleSlots0, indTypeSlots0, indCtorSlots0, indRecSlots0, indDeclSlots0] at hro
  have hq := scanIndTypeLoop_eq b _ (i + 1) true 0 [] false false false [] 0 0 0 0 0 rfl
  rw [scanIndType, hq]
  split at hro
  · rename_i hbyte; rw [ite_eq_left hbyte, hro]; exact ⟨_, rfl⟩
  · simp at hro

/-- Slot `k` of the record: when con-leche reads the record as `r`, the word is slot `k` of a slot
list that builds `r`, each slot being its initial value or one the spec writes, every required key
written. -/
theorem indTypeSlot_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t)  (i : USize) (hi : i.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat))))
    (k : Nat) (hk : k < 10) (r : IndTypeRec) (e0 : USize) (hd : scanIndType b i = .ok r e0) :
    RetP t (recFun indTypeSpec indTypeInits (vv (slotName k))) (fun w => ∃ slots', r = indTypeOf slots' ∧
      SlotsOK b indTypeSpec indTypeSlots0 slots' ∧ ∀ hk' : k < slots'.length, SlotOK b w slots'[k]) := by
  refine retP_mono (indType_body t A b hp hb hc  i hi lb ln li (slotName k) (Or.inr ⟨k, hk, rfl⟩)) ?_
  rintro w ⟨j, slots', hro, -, -, hsl⟩
  unfold RecOut at hro
  simp only [ruleSlots0, indTypeSlots0, indCtorSlots0, indRecSlots0, indDeclSlots0] at hro
  split at hro
  · rename_i hbyte
    have hq := scanIndTypeLoop_eq b _ (i + 1) true 0 [] false false false [] 0 0 0 0 0 rfl
    have hs : scanIndType b i = .ok (indTypeOf slots') j := by
      rw [scanIndType, hq, ite_eq_left hbyte, hro]; rfl
    rw [hd] at hs
    simp only [ScanRes.ok.injEq] at hs
    exact ⟨slots', hs.1, objLoop_slots indTypeSpec (by unfold BitsOK; decide) b _ (i + 1) true 0 _ rfl slots' j hro (seenWr_zero _ _ _),
      fun hk' => hsl k hk' rfl⟩
  · simp at hro



theorem indCtor_body (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t)  (i : USize) (hi : i.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat))))
    (x : MlS) (hx : x = sI ∨ ∃ k, k < 8 ∧ x = slotName k) :
    RetP t (recFun indCtorSpec indCtorInits (vv x)) (fun w => ∃ j slots', RecOut indCtorSpec b i indCtorSlots0 j slots' ∧
      j.toNat ≤ b.size + 64 ∧ (x = sI → w = BitVec.ofNat 64 j.toNat) ∧
      (∀ k (hk : k < slots'.length), x = slotName k → SlotOK b w slots'[k])) := by
  unfold recFun
  apply retP_decsOf
  have hlk := recEntry_lookup indCtorInits t
  have hks : ∀ e ∈ indCtorSpec.keys, ActOK 8 e.2.2 := by simp [indCtorSpec, ActOK]
  exact recBody_spec (σ := σ) indCtorSpec 8 t A b hp hb hc hks (by decide) i hi indCtorSlots0 rfl x hx
    ((indCtorInits |> recLocals).foldl (fun s (x, w) => setVarHOLFinite x (.val (.word w)) s) t) rfl rfl rfl rfl rfl
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indCtorInits]; exact lb)
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indCtorInits]; exact ln)
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indCtorInits]; exact li)
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indCtorInits])
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indCtorInits])
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indCtorInits])
    (by intro x hx; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indCtorInits]⟩)
    (by intro k hk; simp only [indCtorSlots0, List.length_cons, List.length_nil] at hk
        rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indCtorInits], by simp [indCtorSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨BitVec.ofNat 64 listSentinel, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indCtorInits], by simp [indCtorSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indCtorInits], by simp [indCtorSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indCtorInits], by simp [indCtorSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indCtorInits], by simp [indCtorSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indCtorInits], by simp [indCtorSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨BitVec.ofNat 64 listSentinel, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indCtorInits], by simp [indCtorSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨BitVec.ofNat 64 listSentinel, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indCtorInits], by simp [indCtorSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩)

/-- The record's end: con-leche's `scanIndCtor` accepts the record at `i` and ends there. -/
theorem indCtorEnd_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t)  (i : USize) (hi : i.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat)))) :
    RetP t (recFun indCtorSpec indCtorInits (vv sI)) (fun w => ∃ (j : USize), w = BitVec.ofNat 64 j.toNat ∧
      j.toNat ≤ b.size + 64 ∧ ∃ r : IndCtorRec, scanIndCtor b i = .ok r j) := by
  refine retP_mono (indCtor_body t A b hp hb hc  i hi lb ln li sI (Or.inl rfl)) ?_
  rintro w ⟨j, slots', hro, hjb, hw, -⟩
  refine ⟨j, hw rfl, hjb, ?_⟩
  unfold RecOut at hro
  simp only [ruleSlots0, indTypeSlots0, indCtorSlots0, indRecSlots0, indDeclSlots0] at hro
  have hq := scanIndCtorLoop_eq b _ (i + 1) true 0 false [] 0 0 0 0 none none rfl
  rw [scanIndCtor, hq]
  split at hro
  · rename_i hbyte; rw [ite_eq_left hbyte, hro]; exact ⟨_, rfl⟩
  · simp at hro

/-- Slot `k` of the record: when con-leche reads the record as `r`, the word is slot `k` of a slot
list that builds `r`, each slot being its initial value or one the spec writes, every required key
written. -/
theorem indCtorSlot_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t)  (i : USize) (hi : i.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat))))
    (k : Nat) (hk : k < 8) (r : IndCtorRec) (e0 : USize) (hd : scanIndCtor b i = .ok r e0) :
    RetP t (recFun indCtorSpec indCtorInits (vv (slotName k))) (fun w => ∃ slots', r = indCtorOf slots' ∧
      SlotsOK b indCtorSpec indCtorSlots0 slots' ∧ ∀ hk' : k < slots'.length, SlotOK b w slots'[k]) := by
  refine retP_mono (indCtor_body t A b hp hb hc  i hi lb ln li (slotName k) (Or.inr ⟨k, hk, rfl⟩)) ?_
  rintro w ⟨j, slots', hro, -, -, hsl⟩
  unfold RecOut at hro
  simp only [ruleSlots0, indTypeSlots0, indCtorSlots0, indRecSlots0, indDeclSlots0] at hro
  split at hro
  · rename_i hbyte
    have hq := scanIndCtorLoop_eq b _ (i + 1) true 0 false [] 0 0 0 0 none none rfl
    have hs : scanIndCtor b i = .ok (indCtorOf slots') j := by
      rw [scanIndCtor, hq, ite_eq_left hbyte, hro]; rfl
    rw [hd] at hs
    simp only [ScanRes.ok.injEq] at hs
    exact ⟨slots', hs.1, objLoop_slots indCtorSpec (by unfold BitsOK; decide) b _ (i + 1) true 0 _ rfl slots' j hro (seenWr_zero _ _ _),
      fun hk' => hsl k hk' rfl⟩
  · simp at hro



theorem indRec_body (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (hs0 : SubSound t 0 scRulesU) (i : USize) (hi : i.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat))))
    (x : MlS) (hx : x = sI ∨ ∃ k, k < 10 ∧ x = slotName k) :
    RetP t (recFun indRecSpec indRecInits (vv x)) (fun w => ∃ j slots', RecOut indRecSpec b i indRecSlots0 j slots' ∧
      j.toNat ≤ b.size + 64 ∧ (x = sI → w = BitVec.ofNat 64 j.toNat) ∧
      (∀ k (hk : k < slots'.length), x = slotName k → SlotOK b w slots'[k])) := by
  unfold recFun
  apply retP_decsOf
  have hlk := recEntry_lookup indRecInits t
  have hks : ∀ e ∈ indRecSpec.keys, ActOKX t 10 e.2.2 := by
    intro e he
    simp only [indRecSpec, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp only [ActOKX, ActOK] <;>
      first | decide | trivial | exact ⟨by decide, by assumption⟩
  exact recBody_specX (σ := σ) indRecSpec 10 t A b hp hb hc hks (by decide) i hi indRecSlots0 rfl x hx
    ((indRecInits |> recLocals).foldl (fun s (x, w) => setVarHOLFinite x (.val (.word w)) s) t) rfl rfl rfl rfl rfl
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indRecInits]; exact lb)
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indRecInits]; exact ln)
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indRecInits]; exact li)
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indRecInits])
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indRecInits])
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indRecInits])
    (by intro x hx; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indRecInits]⟩)
    (by intro k hk; simp only [indRecSlots0, List.length_cons, List.length_nil] at hk
        rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indRecInits], by simp [indRecSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indRecInits], by simp [indRecSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨BitVec.ofNat 64 listSentinel, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indRecInits], by simp [indRecSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indRecInits], by simp [indRecSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indRecInits], by simp [indRecSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indRecInits], by simp [indRecSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indRecInits], by simp [indRecSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indRecInits], by simp [indRecSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indRecInits], by simp [indRecSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indRecInits], by simp [indRecSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩)

/-- The record's end: con-leche's `scanIndRec` accepts the record at `i` and ends there. -/
theorem indRecEnd_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (hs0 : SubSound t 0 scRulesU) (i : USize) (hi : i.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat)))) :
    RetP t (recFun indRecSpec indRecInits (vv sI)) (fun w => ∃ (j : USize), w = BitVec.ofNat 64 j.toNat ∧
      j.toNat ≤ b.size + 64 ∧ ∃ r : IndRecRec, scanIndRec b i = .ok r j) := by
  refine retP_mono (indRec_body t A b hp hb hc hs0 i hi lb ln li sI (Or.inl rfl)) ?_
  rintro w ⟨j, slots', hro, hjb, hw, -⟩
  refine ⟨j, hw rfl, hjb, ?_⟩
  unfold RecOut at hro
  simp only [ruleSlots0, indTypeSlots0, indCtorSlots0, indRecSlots0, indDeclSlots0] at hro
  have hq := scanIndRecLoop_eq b _ (i + 1) true 0 false false [] 0 0 0 0 0 (2 ^ 64) 0 rfl
  simp only [rescanL_top] at hq
  rw [scanIndRec, hq]
  split at hro
  · rename_i hbyte; rw [ite_eq_left hbyte, hro]; exact ⟨_, rfl⟩
  · simp at hro

/-- Slot `k` of the record: when con-leche reads the record as `r`, the word is slot `k` of a slot
list that builds `r`, each slot being its initial value or one the spec writes, every required key
written. -/
theorem indRecSlot_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (hs0 : SubSound t 0 scRulesU) (i : USize) (hi : i.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat))))
    (k : Nat) (hk : k < 10) (r : IndRecRec) (e0 : USize) (hd : scanIndRec b i = .ok r e0) :
    RetP t (recFun indRecSpec indRecInits (vv (slotName k))) (fun w => ∃ slots', r = indRecOf b slots' ∧
      SlotsOK b indRecSpec indRecSlots0 slots' ∧ ∀ hk' : k < slots'.length, SlotOK b w slots'[k]) := by
  refine retP_mono (indRec_body t A b hp hb hc hs0 i hi lb ln li (slotName k) (Or.inr ⟨k, hk, rfl⟩)) ?_
  rintro w ⟨j, slots', hro, -, -, hsl⟩
  unfold RecOut at hro
  simp only [ruleSlots0, indTypeSlots0, indCtorSlots0, indRecSlots0, indDeclSlots0] at hro
  split at hro
  · rename_i hbyte
    have hq := scanIndRecLoop_eq b _ (i + 1) true 0 false false [] 0 0 0 0 0 (2 ^ 64) 0 rfl
    simp only [rescanL_top] at hq
    have hs : scanIndRec b i = .ok (indRecOf b slots') j := by
      rw [scanIndRec, hq, ite_eq_left hbyte, hro]; rfl
    rw [hd] at hs
    simp only [ScanRes.ok.injEq] at hs
    exact ⟨slots', hs.1, objLoop_slots indRecSpec (by unfold BitsOK; decide) b _ (i + 1) true 0 _ rfl slots' j hro (seenWr_zero _ _ _),
      fun hk' => hsl k hk' rfl⟩
  · simp at hro



theorem indDecl_body (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (hs1 : SubSound t 1 scCtorsU) (hs2 : SubSound t 2 scRecsU) (hs3 : SubSound t 3 scTypesU) (i : USize) (hi : i.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat))))
    (x : MlS) (hx : x = sI ∨ ∃ k, k < 3 ∧ x = slotName k) :
    RetP t (recFun indDeclSpec indDeclInits (vv x)) (fun w => ∃ j slots', RecOut indDeclSpec b i indDeclSlots0 j slots' ∧
      j.toNat ≤ b.size + 64 ∧ (x = sI → w = BitVec.ofNat 64 j.toNat) ∧
      (∀ k (hk : k < slots'.length), x = slotName k → SlotOK b w slots'[k])) := by
  unfold recFun
  apply retP_decsOf
  have hlk := recEntry_lookup indDeclInits t
  have hks : ∀ e ∈ indDeclSpec.keys, ActOKX t 3 e.2.2 := by
    intro e he
    simp only [indDeclSpec, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl <;> simp only [ActOKX, ActOK] <;>
      first | decide | trivial | exact ⟨by decide, by assumption⟩
  exact recBody_specX (σ := σ) indDeclSpec 3 t A b hp hb hc hks (by decide) i hi indDeclSlots0 rfl x hx
    ((indDeclInits |> recLocals).foldl (fun s (x, w) => setVarHOLFinite x (.val (.word w)) s) t) rfl rfl rfl rfl rfl
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indDeclInits]; exact lb)
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indDeclInits]; exact ln)
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indDeclInits]; exact li)
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indDeclInits])
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indDeclInits])
    (by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indDeclInits])
    (by intro x hx; simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl | rfl | rfl <;> exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indDeclInits]⟩)
    (by intro k hk; simp only [indDeclSlots0, List.length_cons, List.length_nil] at hk
        rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indDeclInits], by simp [indDeclSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indDeclInits], by simp [indDeclSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩
        · exact ⟨0, by rw [hlk]; simp (config := {decide := true}) [recLocals, slotName, slotNames, sB, sN, sI, sG, sW, sS, sC, sK, sV, sKK, sE2, indDeclInits], by simp [indDeclSlots0, SlotOK, natCap, bw, listSentinel, optSV]⟩)

/-- The record's end: con-leche's `scanIndDecl` accepts the record at `i` and ends there. -/
theorem indDeclEnd_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (hs1 : SubSound t 1 scCtorsU) (hs2 : SubSound t 2 scRecsU) (hs3 : SubSound t 3 scTypesU) (i : USize) (hi : i.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat)))) :
    RetP t (recFun indDeclSpec indDeclInits (vv sI)) (fun w => ∃ (j : USize), w = BitVec.ofNat 64 j.toNat ∧
      j.toNat ≤ b.size + 64 ∧ ∃ r : DeclRec, scanIndDecl b i = .ok r j) := by
  refine retP_mono (indDecl_body t A b hp hb hc hs1 hs2 hs3 i hi lb ln li sI (Or.inl rfl)) ?_
  rintro w ⟨j, slots', hro, hjb, hw, -⟩
  refine ⟨j, hw rfl, hjb, ?_⟩
  unfold RecOut at hro
  simp only [ruleSlots0, indTypeSlots0, indCtorSlots0, indRecSlots0, indDeclSlots0] at hro
  have hq := scanIndDeclLoop_eq b _ (i + 1) true 0 (2 ^ 64) (2 ^ 64) (2 ^ 64) rfl
  simp only [rescanL_top] at hq
  rw [scanIndDecl, hq]
  split at hro
  · rename_i hbyte; rw [ite_eq_left hbyte, hro]; exact ⟨_, rfl⟩
  · simp at hro

/-- Slot `k` of the record: when con-leche reads the record as `r`, the word is slot `k` of a slot
list that builds `r`, each slot being its initial value or one the spec writes, every required key
written. -/
theorem indDeclSlot_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (hs1 : SubSound t 1 scCtorsU) (hs2 : SubSound t 2 scRecsU) (hs3 : SubSound t 3 scTypesU) (i : USize) (hi : i.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat))))
    (k : Nat) (hk : k < 3) (r : DeclRec) (e0 : USize) (hd : scanIndDecl b i = .ok r e0) :
    RetP t (recFun indDeclSpec indDeclInits (vv (slotName k))) (fun w => ∃ slots', r = indDeclOf b slots' ∧
      SlotsOK b indDeclSpec indDeclSlots0 slots' ∧ ∀ hk' : k < slots'.length, SlotOK b w slots'[k]) := by
  refine retP_mono (indDecl_body t A b hp hb hc hs1 hs2 hs3 i hi lb ln li (slotName k) (Or.inr ⟨k, hk, rfl⟩)) ?_
  rintro w ⟨j, slots', hro, -, -, hsl⟩
  unfold RecOut at hro
  simp only [ruleSlots0, indTypeSlots0, indCtorSlots0, indRecSlots0, indDeclSlots0] at hro
  split at hro
  · rename_i hbyte
    have hq := scanIndDeclLoop_eq b _ (i + 1) true 0 (2 ^ 64) (2 ^ 64) (2 ^ 64) rfl
    simp only [rescanL_top] at hq
    have hs : scanIndDecl b i = .ok (indDeclOf b slots') j := by
      rw [scanIndDecl, hq, ite_eq_left hbyte, hro]; rfl
    rw [hd] at hs
    simp only [ScanRes.ok.injEq] at hs
    exact ⟨slots', hs.1, objLoop_slots indDeclSpec (by unfold BitsOK; decide) b _ (i + 1) true 0 _ rfl slots' j hro (seenWr_zero _ _ _),
      fun hk' => hsl k hk' rfl⟩
  · simp at hro


/-! ## The callees: record functions and list functions -/

theorem scU_iff {α : Type} (sc : ByteArray → USize → ScanRes (List α)) (item : ByteArray → USize → ScanRes α)
    (heq : ∀ b v, sc b v = objListOpen item b v) (b : ByteArray) (v e : USize) :
    srMap (fun _ => ()) (sc b v) = .ok () e ↔ ∃ xs, objListOpen item b v = .ok xs e := by
  rw [← heq]
  cases sc b v with
  | ok xs e' => simp [srMap]
  | err er => simp [srMap]

theorem rule_item (t : PanSemStateFiniteExact 64 σ) (hc : ScanCodes t) (hic : IndCodes t) :
    ItemSound t fRule scanRule :=
  ⟨_, hic.rule, fun s A b hsc hp hb v hv lb ln li => ruleEnd_sound s A b hp hb (hc.congr hsc) v hv lb ln li⟩

theorem indType_item (t : PanSemStateFiniteExact 64 σ) (hc : ScanCodes t) (hic : IndCodes t) :
    ItemSound t fIndType scanIndType :=
  ⟨_, hic.ty, fun s A b hsc hp hb v hv lb ln li => indTypeEnd_sound s A b hp hb (hc.congr hsc) v hv lb ln li⟩

theorem indCtor_item (t : PanSemStateFiniteExact 64 σ) (hc : ScanCodes t) (hic : IndCodes t) :
    ItemSound t fIndCtor scanIndCtor :=
  ⟨_, hic.ctor, fun s A b hsc hp hb v hv lb ln li => indCtorEnd_sound s A b hp hb (hc.congr hsc) v hv lb ln li⟩

theorem sub0_ok (t : PanSemStateFiniteExact 64 σ) (hc : ScanCodes t) (hic : IndCodes t) : SubSound t 0 scRulesU :=
  subSound_of_list t 0 fRule scanRule scRulesU (scU_iff scanRules scanRule scanRules_objList) hic.sub0
    (rule_item t hc hic)

theorem indRec_item (t : PanSemStateFiniteExact 64 σ) (hc : ScanCodes t) (hic : IndCodes t) :
    ItemSound t fIndRec scanIndRec :=
  ⟨_, hic.irec, fun s A b hsc hp hb v hv lb ln li => indRecEnd_sound s A b hp hb (hc.congr hsc)
    (sub0_ok s (hc.congr hsc) (hic.congr hsc)) v hv lb ln li⟩

theorem sub1_ok (t : PanSemStateFiniteExact 64 σ) (hc : ScanCodes t) (hic : IndCodes t) : SubSound t 1 scCtorsU :=
  subSound_of_list t 1 fIndCtor scanIndCtor scCtorsU (scU_iff scanIndCtors scanIndCtor scanIndCtors_objList)
    hic.sub1 (indCtor_item t hc hic)

theorem sub2_ok (t : PanSemStateFiniteExact 64 σ) (hc : ScanCodes t) (hic : IndCodes t) : SubSound t 2 scRecsU :=
  subSound_of_list t 2 fIndRec scanIndRec scRecsU (scU_iff scanIndRecs scanIndRec scanIndRecs_objList)
    hic.sub2 (indRec_item t hc hic)

theorem sub3_ok (t : PanSemStateFiniteExact 64 σ) (hc : ScanCodes t) (hic : IndCodes t) : SubSound t 3 scTypesU :=
  subSound_of_list t 3 fIndType scanIndType scTypesU (scU_iff scanIndTypes scanIndType scanIndTypes_objList)
    hic.sub3 (indType_item t hc hic)

/-- **The line-table function for `inductive`**: when it returns `j`, con-leche's `scanIndDecl`
accepts the payload at `i` and ends at `j`. -/
theorem recInd_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (hic : IndCodes t) (i : USize) (hi : i.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat)))) :
    RetP t (recFun indDeclSpec indDeclInits (vv sI)) (fun w => ∃ (j : USize), w = BitVec.ofNat 64 j.toNat ∧
      j.toNat ≤ b.size + 64 ∧ ∃ r : DeclRec, scanIndDecl b i = .ok r j) :=
  indDeclEnd_sound t A b hp hb hc (sub1_ok t hc hic) (sub2_ok t hc hic) (sub3_ok t hc hic) i hi lb ln li

theorem objListOpen_pos {α : Type} {item : ByteArray → USize → ScanRes α} {b : ByteArray} (hp : Plat b)
    {p e : USize} {xs : List α} (h : objListOpen item b p = .ok xs e) : p.toNat < b.size := by
  rw [objListOpen] at h
  split at h
  · rename_i hb
    by_cases hl : p.toNat < b.size
    · exact hl
    · rw [byteAt_eq hp, List.getElem?_eq_none (by simp; omega)] at hb
      simp at hb
  · simp at h

/-- **The number of records** in the list at `p` (exact, and at most the buffer size). -/
theorem ruleCount_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (hic : IndCodes t) (p e : USize) (xs : List RuleRec)
    (hs : scanRules b p = .ok xs e)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 p.toNat)))) :
    RetP t (olFun3 fRule sM) (fun w => w = BitVec.ofNat 64 xs.length ∧ xs.length ≤ b.size) := by
  rw [scanRules_objList] at hs
  refine retP_mono (olFun3_sound t A b hp hb fRule scanRule (rule_item t hc hic) sM (Or.inr (Or.inl rfl)) p
    (Nat.le_of_lt (objListOpen_pos hp hs)) lb ln li) ?_
  rintro w ⟨xs', e', hok, -, -, -, hw, -⟩
  rw [hs] at hok
  simp only [ScanRes.ok.injEq] at hok
  obtain ⟨rfl, rfl⟩ := hok
  exact ⟨hw rfl, objListOpen_len hs⟩

/-- **The position of record `J`** of the list at `p`: con-leche reads `xs[J]` there. -/
theorem ruleAt_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (hic : IndCodes t) (p e : USize) (xs : List RuleRec)
    (hs : scanRules b p = .ok xs e) (J : Nat) (hJ : J < 2 ^ 64)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 p.toNat))))
    (ll : t.locals.lookup sL = some (.val (.word (BitVec.ofNat 64 J)))) :
    RetP t (olFun4 fRule sR) (fun w => ∀ hJl : J < xs.length, ∃ (q e' : USize), w = BitVec.ofNat 64 q.toNat ∧
      q.toNat ≤ b.size ∧ scanRule b q = .ok xs[J] e') := by
  rw [scanRules_objList] at hs
  refine retP_mono (olFun4_sound t A b hp hb fRule scanRule (rule_item t hc hic) sR (Or.inr (Or.inr rfl)) p
    (Nat.le_of_lt (objListOpen_pos hp hs)) J hJ lb ln li ll) ?_
  rintro w ⟨xs', e', hok, -, -, -, -, hw⟩ hJl
  rw [hs] at hok
  simp only [ScanRes.ok.injEq] at hok
  obtain ⟨rfl, rfl⟩ := hok
  obtain ⟨q, e'', x, hwq, hx, hsc⟩ := hw rfl hJl
  rw [List.getElem?_eq_getElem hJl] at hx
  simp only [Option.some.injEq] at hx
  subst hx
  refine ⟨q, e'', hwq, ?_, hsc⟩
  rw [scanRule] at hsc
  split at hsc
  · rename_i hb'
    by_cases hl : q.toNat < b.size
    · exact Nat.le_of_lt hl
    · rw [byteAt_eq hp, List.getElem?_eq_none (by simp; omega)] at hb'
      simp at hb'
  · simp at hsc

/-- **The number of records** in the list at `p` (exact, and at most the buffer size). -/
theorem indCtorCount_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (hic : IndCodes t) (p e : USize) (xs : List IndCtorRec)
    (hs : scanIndCtors b p = .ok xs e)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 p.toNat)))) :
    RetP t (olFun3 fIndCtor sM) (fun w => w = BitVec.ofNat 64 xs.length ∧ xs.length ≤ b.size) := by
  rw [scanIndCtors_objList] at hs
  refine retP_mono (olFun3_sound t A b hp hb fIndCtor scanIndCtor (indCtor_item t hc hic) sM (Or.inr (Or.inl rfl)) p
    (Nat.le_of_lt (objListOpen_pos hp hs)) lb ln li) ?_
  rintro w ⟨xs', e', hok, -, -, -, hw, -⟩
  rw [hs] at hok
  simp only [ScanRes.ok.injEq] at hok
  obtain ⟨rfl, rfl⟩ := hok
  exact ⟨hw rfl, objListOpen_len hs⟩

/-- **The position of record `J`** of the list at `p`: con-leche reads `xs[J]` there. -/
theorem indCtorAt_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (hic : IndCodes t) (p e : USize) (xs : List IndCtorRec)
    (hs : scanIndCtors b p = .ok xs e) (J : Nat) (hJ : J < 2 ^ 64)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 p.toNat))))
    (ll : t.locals.lookup sL = some (.val (.word (BitVec.ofNat 64 J)))) :
    RetP t (olFun4 fIndCtor sR) (fun w => ∀ hJl : J < xs.length, ∃ (q e' : USize), w = BitVec.ofNat 64 q.toNat ∧
      q.toNat ≤ b.size ∧ scanIndCtor b q = .ok xs[J] e') := by
  rw [scanIndCtors_objList] at hs
  refine retP_mono (olFun4_sound t A b hp hb fIndCtor scanIndCtor (indCtor_item t hc hic) sR (Or.inr (Or.inr rfl)) p
    (Nat.le_of_lt (objListOpen_pos hp hs)) J hJ lb ln li ll) ?_
  rintro w ⟨xs', e', hok, -, -, -, -, hw⟩ hJl
  rw [hs] at hok
  simp only [ScanRes.ok.injEq] at hok
  obtain ⟨rfl, rfl⟩ := hok
  obtain ⟨q, e'', x, hwq, hx, hsc⟩ := hw rfl hJl
  rw [List.getElem?_eq_getElem hJl] at hx
  simp only [Option.some.injEq] at hx
  subst hx
  refine ⟨q, e'', hwq, ?_, hsc⟩
  rw [scanIndCtor] at hsc
  split at hsc
  · rename_i hb'
    by_cases hl : q.toNat < b.size
    · exact Nat.le_of_lt hl
    · rw [byteAt_eq hp, List.getElem?_eq_none (by simp; omega)] at hb'
      simp at hb'
  · simp at hsc

/-- **The number of records** in the list at `p` (exact, and at most the buffer size). -/
theorem indRecCount_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (hic : IndCodes t) (p e : USize) (xs : List IndRecRec)
    (hs : scanIndRecs b p = .ok xs e)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 p.toNat)))) :
    RetP t (olFun3 fIndRec sM) (fun w => w = BitVec.ofNat 64 xs.length ∧ xs.length ≤ b.size) := by
  rw [scanIndRecs_objList] at hs
  refine retP_mono (olFun3_sound t A b hp hb fIndRec scanIndRec (indRec_item t hc hic) sM (Or.inr (Or.inl rfl)) p
    (Nat.le_of_lt (objListOpen_pos hp hs)) lb ln li) ?_
  rintro w ⟨xs', e', hok, -, -, -, hw, -⟩
  rw [hs] at hok
  simp only [ScanRes.ok.injEq] at hok
  obtain ⟨rfl, rfl⟩ := hok
  exact ⟨hw rfl, objListOpen_len hs⟩

/-- **The position of record `J`** of the list at `p`: con-leche reads `xs[J]` there. -/
theorem indRecAt_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (hic : IndCodes t) (p e : USize) (xs : List IndRecRec)
    (hs : scanIndRecs b p = .ok xs e) (J : Nat) (hJ : J < 2 ^ 64)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 p.toNat))))
    (ll : t.locals.lookup sL = some (.val (.word (BitVec.ofNat 64 J)))) :
    RetP t (olFun4 fIndRec sR) (fun w => ∀ hJl : J < xs.length, ∃ (q e' : USize), w = BitVec.ofNat 64 q.toNat ∧
      q.toNat ≤ b.size ∧ scanIndRec b q = .ok xs[J] e') := by
  rw [scanIndRecs_objList] at hs
  refine retP_mono (olFun4_sound t A b hp hb fIndRec scanIndRec (indRec_item t hc hic) sR (Or.inr (Or.inr rfl)) p
    (Nat.le_of_lt (objListOpen_pos hp hs)) J hJ lb ln li ll) ?_
  rintro w ⟨xs', e', hok, -, -, -, -, hw⟩ hJl
  rw [hs] at hok
  simp only [ScanRes.ok.injEq] at hok
  obtain ⟨rfl, rfl⟩ := hok
  obtain ⟨q, e'', x, hwq, hx, hsc⟩ := hw rfl hJl
  rw [List.getElem?_eq_getElem hJl] at hx
  simp only [Option.some.injEq] at hx
  subst hx
  refine ⟨q, e'', hwq, ?_, hsc⟩
  rw [scanIndRec] at hsc
  split at hsc
  · rename_i hb'
    by_cases hl : q.toNat < b.size
    · exact Nat.le_of_lt hl
    · rw [byteAt_eq hp, List.getElem?_eq_none (by simp; omega)] at hb'
      simp at hb'
  · simp at hsc

/-- **The number of records** in the list at `p` (exact, and at most the buffer size). -/
theorem indTypeCount_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (hic : IndCodes t) (p e : USize) (xs : List IndTypeRec)
    (hs : scanIndTypes b p = .ok xs e)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 p.toNat)))) :
    RetP t (olFun3 fIndType sM) (fun w => w = BitVec.ofNat 64 xs.length ∧ xs.length ≤ b.size) := by
  rw [scanIndTypes_objList] at hs
  refine retP_mono (olFun3_sound t A b hp hb fIndType scanIndType (indType_item t hc hic) sM (Or.inr (Or.inl rfl)) p
    (Nat.le_of_lt (objListOpen_pos hp hs)) lb ln li) ?_
  rintro w ⟨xs', e', hok, -, -, -, hw, -⟩
  rw [hs] at hok
  simp only [ScanRes.ok.injEq] at hok
  obtain ⟨rfl, rfl⟩ := hok
  exact ⟨hw rfl, objListOpen_len hs⟩

/-- **The position of record `J`** of the list at `p`: con-leche reads `xs[J]` there. -/
theorem indTypeAt_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (hic : IndCodes t) (p e : USize) (xs : List IndTypeRec)
    (hs : scanIndTypes b p = .ok xs e) (J : Nat) (hJ : J < 2 ^ 64)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 p.toNat))))
    (ll : t.locals.lookup sL = some (.val (.word (BitVec.ofNat 64 J)))) :
    RetP t (olFun4 fIndType sR) (fun w => ∀ hJl : J < xs.length, ∃ (q e' : USize), w = BitVec.ofNat 64 q.toNat ∧
      q.toNat ≤ b.size ∧ scanIndType b q = .ok xs[J] e') := by
  rw [scanIndTypes_objList] at hs
  refine retP_mono (olFun4_sound t A b hp hb fIndType scanIndType (indType_item t hc hic) sR (Or.inr (Or.inr rfl)) p
    (Nat.le_of_lt (objListOpen_pos hp hs)) J hJ lb ln li ll) ?_
  rintro w ⟨xs', e', hok, -, -, -, -, hw⟩ hJl
  rw [hs] at hok
  simp only [ScanRes.ok.injEq] at hok
  obtain ⟨rfl, rfl⟩ := hok
  obtain ⟨q, e'', x, hwq, hx, hsc⟩ := hw rfl hJl
  rw [List.getElem?_eq_getElem hJl] at hx
  simp only [Option.some.injEq] at hx
  subst hx
  refine ⟨q, e'', hwq, ?_, hsc⟩
  rw [scanIndType] at hsc
  split at hsc
  · rename_i hb'
    by_cases hl : q.toNat < b.size
    · exact Nat.le_of_lt hl
    · rw [byteAt_eq hp, List.getElem?_eq_none (by simp; omega)] at hb'
      simp at hb'
  · simp at hsc

end

end ConPanqueque.Scan
