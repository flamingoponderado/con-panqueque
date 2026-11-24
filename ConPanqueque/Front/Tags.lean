import ConPanqueque.Front.LineCall

/-! # From the line's tag to con-leche's payload

The line scanner returns the payload's tag and slot (`PlOK`).  The tags of `lineTblP` are distinct,
so a tag names one entry, and the entry's scanner gives con-leche's payload. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

namespace ConPanqueque.Scan

open ConPanqueque.Scan
open ConLeche.Frontend

def LActP.tag : ConPanqueque.Scan.LActP → Nat
  | .idxP _ => 0
  | .natP t _ _ => t
  | .strP t _ _ => t
  | .objP t _ _ _ => t

end ConPanqueque.Scan

namespace ConPanqueque.Front

open ConPanqueque.Scan
open ConLeche.Frontend

theorem plEntry_tag {b : ByteArray} {wpl ws0 : BitVec 64} {pl : LinePayload} {a : LActP}
    (h : PlEntry b wpl ws0 pl a) : wpl = BitVec.ofNat 64 a.tag := by
  cases a <;> simp only [PlEntry] at h
  · exact h.1
  · exact h.1
  · exact h.1

theorem lineTblP_tag_lt : ∀ e ∈ lineTblP, e.2.tag < 32 := by
  intro e he; simp only [lineTblP, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- A nonzero tag names its entry. -/
theorem plOK_tag {b : ByteArray} {ws0 : BitVec 64} {pl : LinePayload} {t : Nat} (ht : t < 32) (h0 : t ≠ 0)
    (h : PlOK b (BitVec.ofNat 64 t) ws0 pl) : ∃ k a, (k, a) ∈ lineTblP ∧ a.tag = t ∧ PlEntry b (BitVec.ofNat 64 t) ws0 pl a := by
  rcases h with ⟨-, h⟩ | ⟨k, a, hm, he⟩
  · have := congrArg BitVec.toNat h; simp at this; omega
  · refine ⟨k, a, hm, ?_, he⟩
    have e := congrArg BitVec.toNat (plEntry_tag he)
    have := lineTblP_tag_lt _ hm
    simp only [BitVec.toNat_ofNat] at e
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by simp at this ⊢; omega)] at e
    exact e.symm

/-- The payload of an object entry with scanner `scan` and wrapper `wrap`. -/
theorem objPl {b : ByteArray} {ws0 : BitVec 64} {pl : LinePayload} {t g : Nat} {fn : MlS} {α : Type}
    {sc : ByteArray → USize → ScanRes α} {wrap : α → LinePayload}
    (h : PlEntry b (BitVec.ofNat 64 t) ws0 pl (.objP t g fn (fun b v => srMap wrap (sc b v)))) :
    ∃ (v e : USize) (r : α), ws0 = BitVec.ofNat 64 v.toNat ∧ sc b v = .ok r e ∧ pl = wrap r := by
  obtain ⟨-, v, e, hs, hw⟩ := h
  simp only at hs
  cases hr : sc b v with
  | err er => rw [hr] at hs; simp [srMap] at hs
  | ok r e' => rw [hr] at hs; simp only [srMap, ScanRes.ok.injEq] at hs; exact ⟨v, e', r, hw, hr, hs.1.symm⟩

theorem tag_1 {k : Key} {a : LActP} (hm : (k, a) ∈ lineTblP) (ht : a.tag = 1) : a = .natP 1 3 (fun n => .expr (.bvar n)) := by
  simp only [lineTblP, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h) <;>
    first | rfl | (simp [LActP.tag] at ht)

theorem tag_2 {k : Key} {a : LActP} (hm : (k, a) ∈ lineTblP) (ht : a.tag = 2) : a = .natP 2 3 (fun n => .expr (.sort n)) := by
  simp only [lineTblP, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h) <;>
    first | rfl | (simp [LActP.tag] at ht)

theorem tag_3 {k : Key} {a : LActP} (hm : (k, a) ∈ lineTblP) (ht : a.tag = 3) : a = .natP 3 2 (fun n => .level (.succ n)) := by
  simp only [lineTblP, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h) <;>
    first | rfl | (simp [LActP.tag] at ht)

theorem tag_4 {k : Key} {a : LActP} (hm : (k, a) ∈ lineTblP) (ht : a.tag = 4) : a = .natP 4 2 (fun n => .level (.param n)) := by
  simp only [lineTblP, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h) <;>
    first | rfl | (simp [LActP.tag] at ht)

theorem tag_5 {k : Key} {a : LActP} (hm : (k, a) ∈ lineTblP) (ht : a.tag = 5) : a = .objP 5 1 fRecStr nameStr := by
  simp only [lineTblP, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h) <;>
    first | rfl | (simp [LActP.tag] at ht)

theorem tag_6 {k : Key} {a : LActP} (hm : (k, a) ∈ lineTblP) (ht : a.tag = 6) : a = .objP 6 1 fRecNum nameNum := by
  simp only [lineTblP, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h) <;>
    first | rfl | (simp [LActP.tag] at ht)

theorem tag_7 {k : Key} {a : LActP} (hm : (k, a) ∈ lineTblP) (ht : a.tag = 7) : a = .objP 7 3 fRecApp exprApp := by
  simp only [lineTblP, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h) <;>
    first | rfl | (simp [LActP.tag] at ht)

theorem tag_8 {k : Key} {a : LActP} (hm : (k, a) ∈ lineTblP) (ht : a.tag = 8) : a = .objP 8 3 fRecLam exprLam := by
  simp only [lineTblP, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h) <;>
    first | rfl | (simp [LActP.tag] at ht)

theorem tag_9 {k : Key} {a : LActP} (hm : (k, a) ∈ lineTblP) (ht : a.tag = 9) : a = .objP 9 3 fRecForall exprForall := by
  simp only [lineTblP, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h) <;>
    first | rfl | (simp [LActP.tag] at ht)

theorem tag_10 {k : Key} {a : LActP} (hm : (k, a) ∈ lineTblP) (ht : a.tag = 10) : a = .objP 10 3 fRecLet exprLet := by
  simp only [lineTblP, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h) <;>
    first | rfl | (simp [LActP.tag] at ht)

theorem tag_11 {k : Key} {a : LActP} (hm : (k, a) ∈ lineTblP) (ht : a.tag = 11) : a = .objP 11 3 fRecConst exprConst := by
  simp only [lineTblP, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h) <;>
    first | rfl | (simp [LActP.tag] at ht)

theorem tag_12 {k : Key} {a : LActP} (hm : (k, a) ∈ lineTblP) (ht : a.tag = 12) : a = .objP 12 3 fRecProj exprProj := by
  simp only [lineTblP, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h) <;>
    first | rfl | (simp [LActP.tag] at ht)

theorem tag_13 {k : Key} {a : LActP} (hm : (k, a) ∈ lineTblP) (ht : a.tag = 13) : a = .strP 13 3 (fun s => .expr (.strVal s)) := by
  simp only [lineTblP, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h) <;>
    first | rfl | (simp [LActP.tag] at ht)

theorem tag_14 {k : Key} {a : LActP} (hm : (k, a) ∈ lineTblP) (ht : a.tag = 14) : a = .objP 14 0 fRecDef declDef := by
  simp only [lineTblP, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h) <;>
    first | rfl | (simp [LActP.tag] at ht)

theorem tag_15 {k : Key} {a : LActP} (hm : (k, a) ∈ lineTblP) (ht : a.tag = 15) : a = .objP 15 0 fRecThm declThm := by
  simp only [lineTblP, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h) <;>
    first | rfl | (simp [LActP.tag] at ht)

theorem tag_16 {k : Key} {a : LActP} (hm : (k, a) ∈ lineTblP) (ht : a.tag = 16) : a = .objP 16 0 fRecOpaque declOpaque := by
  simp only [lineTblP, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h) <;>
    first | rfl | (simp [LActP.tag] at ht)

theorem tag_17 {k : Key} {a : LActP} (hm : (k, a) ∈ lineTblP) (ht : a.tag = 17) : a = .objP 17 0 fRecMeta metaHdr := by
  simp only [lineTblP, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h) <;>
    first | rfl | (simp [LActP.tag] at ht)

theorem tag_18 {k : Key} {a : LActP} (hm : (k, a) ∈ lineTblP) (ht : a.tag = 18) : a = .objP 18 2 fRecMax levMax := by
  simp only [lineTblP, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h) <;>
    first | rfl | (simp [LActP.tag] at ht)

theorem tag_19 {k : Key} {a : LActP} (hm : (k, a) ∈ lineTblP) (ht : a.tag = 19) : a = .objP 19 2 fRecImax levImax := by
  simp only [lineTblP, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h) <;>
    first | rfl | (simp [LActP.tag] at ht)

theorem tag_20 {k : Key} {a : LActP} (hm : (k, a) ∈ lineTblP) (ht : a.tag = 20) : a = .objP 20 3 fRecNatVal natValPl := by
  simp only [lineTblP, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h) <;>
    first | rfl | (simp [LActP.tag] at ht)

end ConPanqueque.Front
