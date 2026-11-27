import ConPanqueque.Scan.IndFuns

/-! # The fields of an inductive line, read again from the buffer

Given the payload position `i` with `scanIndDecl b i = .ok (.ind tys cts rcs) e0`:

* `fIdF k` (`k < 3`) returns the position of the `ctors` (`0`), `recs` (`1`) or `types` (`2`) list
  (`indDeclField_sound`);
* at a list's position, `f*N` returns its length and `f*At` (fourth parameter `l`) the position of
  record `l` (`*Count_sound`, `*At_sound` in `Scan/IndFuns.lean`);
* at a record's position, `fItF k`/`fIcF k`/`fIrF k`/`fRuF k` return field `k` of the record
  (`indTypeField_sound`, `indCtorField_sound`, `indRecField_sound`, `ruleField_sound`), and the
  rules list position of a recursor is its field `8`.

Word conventions (those of the other record readers):
* a number: capped, `natW x = min x natCap` (`natCap = 2 ^ 62`); an index at or above `natCap`
  misses every table, so a capped word is sound where it is used as an index;
* a flag: `bw (x = true)`, i.e. `1` or `0`;
* a number list (`levelParams`, `ctors` of a type): `ListAt`, the position the list is read again
  from (`nnFun` gives its elements), or the sentinel `listSentinel = 2 ^ 63` for an absent `[]`;
* an optional number (`cidx`, `induct` of a constructor): `optWord`, the sentinel `2 ^ 63` for
  `none`, the capped number for `some x` (never the sentinel, since `min x natCap < 2 ^ 63`);
* a list of records: the exact position of its `[`.
Lists are no longer than the buffer (`objListOpen_len`), so counts and positions are exact words. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

namespace ConPanqueque.Scan

open ConLeche.Frontend

/-- A capped number. -/
def natW (x : Nat) : BitVec 64 := BitVec.ofNat 64 (min x natCap)

/-- A number list's word: a position con-leche reads it from, or the sentinel for `[]`. -/
def ListAt (b : ByteArray) (w : BitVec 64) (xs : List Nat) : Prop :=
  (∃ (p e : USize), w = BitVec.ofNat 64 p.toNat ∧ scanNatList b p = .ok xs e) ∨
    (xs = [] ∧ w = BitVec.ofNat 64 listSentinel)

/-- An optional number's word. -/
def optWord : Option Nat → BitVec 64
  | none => BitVec.ofNat 64 listSentinel
  | some x => natW x

theorem optWord_ne (x : Nat) : optWord (some x) ≠ optWord none := by
  intro h
  have := congrArg BitVec.toNat h
  simp only [optWord, natW, BitVec.toNat_ofNat, listSentinel, natCap] at this
  have h1 : min x (2 ^ 62) < 2 ^ 64 := by have := Nat.min_le_right x (2 ^ 62); omega
  rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by decide)] at this
  have := Nat.min_le_right x (2 ^ 62); omega

theorem slotOK_n {b : ByteArray} {w : BitVec 64} {sv : SVal} (h : SlotOK b w sv) (hk : sv.kind = 0) :
    w = natW sv.nat := by
  cases sv <;> simp [SVal.kind] at hk; simpa [SlotOK, SVal.nat, natW] using h

theorem slotOK_l {b : ByteArray} {w : BitVec 64} {sv : SVal} (h : SlotOK b w sv) (hk : sv.kind = 1) :
    ListAt b w sv.list := by
  cases sv <;> simp [SVal.kind] at hk; simpa [SlotOK, SVal.list, ListAt] using h

theorem slotOK_b {b : ByteArray} {w : BitVec 64} {sv : SVal} (h : SlotOK b w sv) (hk : sv.kind = 3) :
    w = bw (sv.bool = true) := by
  cases sv <;> simp [SVal.kind] at hk; exact h

theorem slotOK_opt {b : ByteArray} {w : BitVec 64} {sv : SVal} (h : SlotOK b w sv)
    (hk : sv = .p (2 ^ 63) ∨ sv.kind = 0) : w = optWord sv.opt := by
  rcases hk with rfl | hk
  · simpa [SlotOK, SVal.opt, optWord, listSentinel] using h
  · cases sv <;> simp [SVal.kind] at hk; simpa [SlotOK, SVal.opt, optWord, natW] using h

/-- A slot's kind, when the spec writes only that kind to it. -/
theorem slots_kind {b : ByteArray} {sp : ObjSpec} {slots0 slots' : List SVal} (h : SlotsOK b sp slots0 slots')
    (sl K : Nat) (hl : sl < slots0.length) (h0 : slots0[sl].kind = K)
    (hw : ∀ e ∈ sp.keys, e.2.2.wr.map Prod.fst = some sl → e.2.2.wr = some (sl, K)) (hl' : sl < slots'.length) :
    slots'[sl].kind = K := by
  rcases h.2.1 sl hl hl' with he | he
  · rw [he]; exact h0
  · obtain ⟨e, hm, hwe⟩ := wrBy_kind he
    have := hw e hm (by rw [hwe]; rfl)
    rw [hwe] at this
    simp only [Option.some.injEq, Prod.mk.injEq] at this
    exact this.2

/-- An optional slot: its initial value, or a number. -/
theorem slots_opt {b : ByteArray} {sp : ObjSpec} {slots0 slots' : List SVal} (h : SlotsOK b sp slots0 slots')
    (sl : Nat) (hl : sl < slots0.length)
    (hw : ∀ e ∈ sp.keys, e.2.2.wr.map Prod.fst = some sl → e.2.2.wr = some (sl, 0)) (hl' : sl < slots'.length) :
    slots'[sl] = slots0[sl] ∨ slots'[sl].kind = 0 := by
  rcases h.2.1 sl hl hl' with he | he
  · exact Or.inl he
  · obtain ⟨e, hm, hwe⟩ := wrBy_kind he
    have := hw e hm (by rw [hwe]; rfl)
    rw [hwe] at this
    simp only [Option.some.injEq, Prod.mk.injEq] at this
    exact Or.inr this.2

theorem getD_of {l : List SVal} {k : Nat} (h : k < l.length) : l.getD k default = l[k] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

/-! ## The fields -/

def IndTypeField (b : ByteArray) (r : IndTypeRec) : Nat → BitVec 64 → Prop
  | 0, w => ListAt b w r.ctors
  | 1, w => w = bw (r.isRec = true)
  | 2, w => w = bw (r.isReflexive = true)
  | 3, w => w = bw (r.isUnsafe = true)
  | 4, w => ListAt b w r.cv.levelParams
  | 5, w => w = natW r.cv.name
  | 6, w => w = natW r.numIndices
  | 7, w => w = natW r.numNested
  | 8, w => w = natW r.numParams
  | 9, w => w = natW r.cv.type
  | _, _ => True

def IndCtorField (b : ByteArray) (r : IndCtorRec) : Nat → BitVec 64 → Prop
  | 0, w => w = bw (r.isUnsafe = true)
  | 1, w => ListAt b w r.cv.levelParams
  | 2, w => w = natW r.cv.name
  | 3, w => w = natW r.numFields
  | 4, w => w = natW r.numParams
  | 5, w => w = natW r.cv.type
  | 6, w => w = optWord r.cidx
  | 7, w => w = optWord r.induct
  | _, _ => True

def IndRecField (b : ByteArray) (r : IndRecRec) : Nat → BitVec 64 → Prop
  | 0, w => w = bw (r.isUnsafe = true)
  | 1, w => w = bw (r.k = true)
  | 2, w => ListAt b w r.cv.levelParams
  | 3, w => w = natW r.cv.name
  | 4, w => w = natW r.numIndices
  | 5, w => w = natW r.numMinors
  | 6, w => w = natW r.numMotives
  | 7, w => w = natW r.numParams
  | 8, w => ∃ (p e : USize), w = BitVec.ofNat 64 p.toNat ∧ scanRules b p = .ok r.rules e
  | 9, w => w = natW r.cv.type
  | _, _ => True

def RuleField (r : RuleRec) : Nat → BitVec 64 → Prop
  | 0, w => w = natW r.ctor
  | 1, w => w = natW r.nfields
  | 2, w => w = natW r.rhs
  | _, _ => True

/-- The declaration's lists: `0` ctors, `1` recs, `2` types, each at the exact position of its `[`. -/
def IndDeclField (b : ByteArray) (tys : List IndTypeRec) (cts : List IndCtorRec) (rcs : List IndRecRec) :
    Nat → BitVec 64 → Prop
  | 0, w => ∃ (p e : USize), w = BitVec.ofNat 64 p.toNat ∧ scanIndCtors b p = .ok cts e
  | 1, w => ∃ (p e : USize), w = BitVec.ofNat 64 p.toNat ∧ scanIndRecs b p = .ok rcs e
  | 2, w => ∃ (p e : USize), w = BitVec.ofNat 64 p.toNat ∧ scanIndTypes b p = .ok tys e
  | _, _ => True

section
variable {σ : Type}

theorem indTypeField_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (i : USize) (hi : i.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat))))
    (k : Nat) (hk : k < 10) (r : IndTypeRec) (e0 : USize) (hd : scanIndType b i = .ok r e0) :
    RetP t (recFun indTypeSpec indTypeInits (vv (slotName k))) (IndTypeField b r k) := by
  refine retP_mono (indTypeSlot_sound t A b hp hb hc i hi lb ln li k hk r e0 hd) ?_
  rintro w ⟨sl, rfl, hS, hw⟩
  have hlen : sl.length = 10 := hS.1
  have hw' := hw (by omega)
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := omega) only [IndTypeField, indTypeOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some]
  · exact slotOK_l hw' (slots_kind hS 0 1 (by decide) rfl (by decide) (by omega))
  · exact slotOK_b hw' (slots_kind hS 1 3 (by decide) rfl (by decide) (by omega))
  · exact slotOK_b hw' (slots_kind hS 2 3 (by decide) rfl (by decide) (by omega))
  · exact slotOK_b hw' (slots_kind hS 3 3 (by decide) rfl (by decide) (by omega))
  · exact slotOK_l hw' (slots_kind hS 4 1 (by decide) rfl (by decide) (by omega))
  · exact slotOK_n hw' (slots_kind hS 5 0 (by decide) rfl (by decide) (by omega))
  · exact slotOK_n hw' (slots_kind hS 6 0 (by decide) rfl (by decide) (by omega))
  · exact slotOK_n hw' (slots_kind hS 7 0 (by decide) rfl (by decide) (by omega))
  · exact slotOK_n hw' (slots_kind hS 8 0 (by decide) rfl (by decide) (by omega))
  · exact slotOK_n hw' (slots_kind hS 9 0 (by decide) rfl (by decide) (by omega))

theorem indCtorField_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (i : USize) (hi : i.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat))))
    (k : Nat) (hk : k < 8) (r : IndCtorRec) (e0 : USize) (hd : scanIndCtor b i = .ok r e0) :
    RetP t (recFun indCtorSpec indCtorInits (vv (slotName k))) (IndCtorField b r k) := by
  refine retP_mono (indCtorSlot_sound t A b hp hb hc i hi lb ln li k hk r e0 hd) ?_
  rintro w ⟨sl, rfl, hS, hw⟩
  have hlen : sl.length = 8 := hS.1
  have hw' := hw (by omega)
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := omega) only [IndCtorField, indCtorOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some]
  · exact slotOK_b hw' (slots_kind hS 0 3 (by decide) rfl (by decide) (by omega))
  · exact slotOK_l hw' (slots_kind hS 1 1 (by decide) rfl (by decide) (by omega))
  · exact slotOK_n hw' (slots_kind hS 2 0 (by decide) rfl (by decide) (by omega))
  · exact slotOK_n hw' (slots_kind hS 3 0 (by decide) rfl (by decide) (by omega))
  · exact slotOK_n hw' (slots_kind hS 4 0 (by decide) rfl (by decide) (by omega))
  · exact slotOK_n hw' (slots_kind hS 5 0 (by decide) rfl (by decide) (by omega))
  · exact slotOK_opt hw' (slots_opt hS 6 (by decide) (by decide) (by omega))
  · exact slotOK_opt hw' (slots_opt hS 7 (by decide) (by decide) (by omega))

theorem recSlot8 {b : ByteArray} {sv : SVal} (hw : WrBy b indRecSpec 8 sv) :
    ∃ (v e : USize), sv = .p v.toNat ∧ scRulesU b v = .ok () e := by
  obtain ⟨e, he, i, v, e', hs⟩ := hw
  simp only [indRecSpec, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | (obtain ⟨-, rfl, h⟩ := stepVal_sub hs; exact ⟨v, e', rfl, h⟩)
    | (have := stepVal_wr' hs; simp [VAct.wr] at this)

theorem indRecField_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (hic : IndCodes t) (i : USize) (hi : i.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat))))
    (k : Nat) (hk : k < 10) (r : IndRecRec) (e0 : USize) (hd : scanIndRec b i = .ok r e0) :
    RetP t (recFun indRecSpec indRecInits (vv (slotName k))) (IndRecField b r k) := by
  refine retP_mono (indRecSlot_sound t A b hp hb hc (sub0_ok t hc hic) i hi lb ln li k hk r e0 hd) ?_
  rintro w ⟨sl, rfl, hS, hw⟩
  have hlen : sl.length = 10 := hS.1
  have hw' := hw (by omega)
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
  simp (disch := omega) only [IndRecField, indRecOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some]
  · exact slotOK_b hw' (slots_kind hS 0 3 (by decide) rfl (by decide) (by omega))
  · exact slotOK_b hw' (slots_kind hS 1 3 (by decide) rfl (by decide) (by omega))
  · exact slotOK_l hw' (slots_kind hS 2 1 (by decide) rfl (by decide) (by omega))
  · exact slotOK_n hw' (slots_kind hS 3 0 (by decide) rfl (by decide) (by omega))
  · exact slotOK_n hw' (slots_kind hS 4 0 (by decide) rfl (by decide) (by omega))
  · exact slotOK_n hw' (slots_kind hS 5 0 (by decide) rfl (by decide) (by omega))
  · exact slotOK_n hw' (slots_kind hS 6 0 (by decide) rfl (by decide) (by omega))
  · exact slotOK_n hw' (slots_kind hS 7 0 (by decide) rfl (by decide) (by omega))
  · obtain ⟨seen', hn, hsw⟩ := hS.2.2
    have hwr := need_wr hn hsw (e := (.kRules, 512, .sub 0 scRulesU 8)) (by simp [indRecSpec])
      (by decide) (by decide) (sl := 8) (kd := 5) rfl (by omega)
    obtain ⟨v, e, hv, hsc⟩ := recSlot8 hwr
    rw [hv] at hw' ⊢
    simp only [SlotOK] at hw'
    simp only [scRulesU] at hsc
    cases hr : scanRules b v with
    | err er => rw [hr] at hsc; simp [srMap] at hsc
    | ok xs e' =>
      rw [hr] at hsc
      simp only [srMap, ScanRes.ok.injEq] at hsc
      obtain ⟨-, rfl⟩ := hsc
      exact ⟨v, e', hw', by simp only [SVal.pos]; rw [rescanL_of hr]; exact hr⟩
  · exact slotOK_n hw' (slots_kind hS 9 0 (by decide) rfl (by decide) (by omega))

theorem ruleField_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (i : USize) (hi : i.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat))))
    (k : Nat) (hk : k < 3) (r : RuleRec) (e0 : USize) (hd : scanRule b i = .ok r e0) :
    RetP t (recFun ruleSpec ruleInits (vv (slotName k))) (RuleField r k) := by
  refine retP_mono (ruleSlot_sound t A b hp hb hc i hi lb ln li k hk r e0 hd) ?_
  rintro w ⟨sl, rfl, hS, hw⟩
  have hlen : sl.length = 3 := hS.1
  have hw' := hw (by omega)
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl <;>
  simp (disch := omega) only [RuleField, ruleOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem, Option.getD_some]
  · exact slotOK_n hw' (slots_kind hS 0 0 (by decide) rfl (by decide) (by omega))
  · exact slotOK_n hw' (slots_kind hS 1 0 (by decide) rfl (by decide) (by omega))
  · exact slotOK_n hw' (slots_kind hS 2 0 (by decide) rfl (by decide) (by omega))

theorem declSlot_sub {b : ByteArray} {sl : Nat} {sv : SVal} (hw : WrBy b indDeclSpec sl sv) :
    ∃ (v e : USize), sv = .p v.toNat ∧ (sl = 0 → scCtorsU b v = .ok () e) ∧ (sl = 1 → scRecsU b v = .ok () e) ∧
      (sl = 2 → scTypesU b v = .ok () e) := by
  obtain ⟨e, he, i, v, e', hs⟩ := hw
  simp only [indDeclSpec, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · have := stepVal_wr' hs; simp [VAct.wr] at this
  · obtain ⟨rfl, rfl, h⟩ := stepVal_sub hs
    exact ⟨v, e', rfl, fun _ => h, fun h' => absurd h' (by decide), fun h' => absurd h' (by decide)⟩
  · have := stepVal_wr' hs; simp [VAct.wr] at this
  · obtain ⟨rfl, rfl, h⟩ := stepVal_sub hs
    exact ⟨v, e', rfl, fun h' => absurd h' (by decide), fun _ => h, fun h' => absurd h' (by decide)⟩
  · obtain ⟨rfl, rfl, h⟩ := stepVal_sub hs
    exact ⟨v, e', rfl, fun h' => absurd h' (by decide), fun h' => absurd h' (by decide), fun _ => h⟩

theorem srMapU_ok {α : Type} {x : ScanRes α} {e : USize} (h : srMap (fun _ => ()) x = .ok () e) :
    ∃ a, x = .ok a e := by
  cases x with
  | ok a e' => simp only [srMap, ScanRes.ok.injEq] at h; exact ⟨a, by rw [h.2]⟩
  | err er => simp [srMap] at h

/-- **The declaration's list positions.** -/
theorem indDeclField_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (hc : ScanCodes t) (hic : IndCodes t) (i : USize) (hi : i.toNat ≤ b.size)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i.toNat))))
    (k : Nat) (hk : k < 3) (tys : List IndTypeRec) (cts : List IndCtorRec) (rcs : List IndRecRec) (e0 : USize)
    (hd : scanIndDecl b i = .ok (.ind tys cts rcs) e0) :
    RetP t (recFun indDeclSpec indDeclInits (vv (slotName k))) (IndDeclField b tys cts rcs k) := by
  refine retP_mono (indDeclSlot_sound t A b hp hb hc (sub1_ok t hc hic) (sub2_ok t hc hic) (sub3_ok t hc hic)
    i hi lb ln li k hk _ e0 hd) ?_
  rintro w ⟨sl, hr, hS, hw⟩
  have hlen : sl.length = 3 := hS.1
  have hw' := hw (by omega)
  obtain ⟨seen', hn, hsw⟩ := hS.2.2
  simp only [indDeclOf, DeclRec.ind.injEq] at hr
  obtain ⟨rt, rc, rr⟩ := hr
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
  · have hwr := need_wr hn hsw (e := (.kCtors, 2, .sub 1 scCtorsU 0)) (by simp [indDeclSpec])
      (by decide) (by decide) (sl := 0) (kd := 5) rfl (by omega)
    obtain ⟨v, e, hv, h0, -, -⟩ := declSlot_sub hwr
    obtain ⟨xs, hxs⟩ := srMapU_ok (h0 rfl)
    rw [hv] at hw'
    simp only [SlotOK] at hw'
    refine ⟨v, e, hw', ?_⟩
    rw [rc, getD_of (show 0 < sl.length by omega), hv]
    simp only [SVal.pos]; rw [rescanL_of hxs]; exact hxs
  · have hwr := need_wr hn hsw (e := (.kRecs, 8, .sub 2 scRecsU 1)) (by simp [indDeclSpec])
      (by decide) (by decide) (sl := 1) (kd := 5) rfl (by omega)
    obtain ⟨v, e, hv, -, h1, -⟩ := declSlot_sub hwr
    obtain ⟨xs, hxs⟩ := srMapU_ok (h1 rfl)
    rw [hv] at hw'
    simp only [SlotOK] at hw'
    refine ⟨v, e, hw', ?_⟩
    rw [rr, getD_of (show 1 < sl.length by omega), hv]
    simp only [SVal.pos]; rw [rescanL_of hxs]; exact hxs
  · have hwr := need_wr hn hsw (e := (.kTypes, 16, .sub 3 scTypesU 2)) (by simp [indDeclSpec])
      (by decide) (by decide) (sl := 2) (kd := 5) rfl (by omega)
    obtain ⟨v, e, hv, -, -, h2⟩ := declSlot_sub hwr
    obtain ⟨xs, hxs⟩ := srMapU_ok (h2 rfl)
    rw [hv] at hw'
    simp only [SlotOK] at hw'
    refine ⟨v, e, hw', ?_⟩
    rw [rt, getD_of (show 2 < sl.length by omega), hv]
    simp only [SVal.pos]; rw [rescanL_of hxs]; exact hxs

end

end ConPanqueque.Scan
