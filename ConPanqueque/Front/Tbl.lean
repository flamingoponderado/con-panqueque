import ConPanqueque.Front.Buf

/-! # The parse tables as arrays in the value heap

con-leche's parse state keeps three stream-index tables (`IdTable`) of handles.  The Pancake
frontend keeps each as `cap` cells of the value heap from cell `j`: cell `j + i` holds `0` when
index `i` is unbound and `idxW h + 1` when it is bound to `h`, and no index at or past `cap` is
bound (a record there is rejected, which is sound).  `IdTable.get?_insert` is the only fact about
con-leche's table this needs.

Three operations, as SpecR rules in the declaration layer's `Inv` world:
* `tblGetP`: read a bound index (an unbound one, or one past `cap`, hangs, as the twin fails);
* `tblFreshP`: insist an index is unbound (the twin's `fresh*` test);
* `tblSetP`: bind it. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

namespace ConPanqueque.Front

open ConPanqueque.T
open ConLeche.Frontend (IdTable)

variable {σ : Type}

def tblW {k : IdxKind} : Option (Idx k) → BitVec 64
  | none => 0
  | some h => Enc.idxW h + 1

def TblRel {k : IdxKind} (H : List (BitVec 64)) (j cap : Nat) (tbl : IdTable (Idx k)) : Prop :=
  (∀ i, i < cap → H[j + i]? = some (tblW (tbl.get? i))) ∧ (∀ i, cap ≤ i → tbl.get? i = none)

theorem idxW_lt {k : IdxKind} (h : Idx k) : (Enc.idxW h).toNat < 2 ^ 32 := by
  simp [Enc.idxW]; exact h.word.toNat_lt

theorem tblW_some_ne {k : IdxKind} (h : Idx k) : tblW (some h) ≠ 0 := by
  intro e
  have h1 := idxW_lt h
  have := congrArg BitVec.toNat e
  simp only [tblW, BitVec.toNat_add, show (1 : BitVec 64).toNat = 1 from rfl,
    show (0 : BitVec 64).toNat = 0 from rfl] at this
  omega

theorem shl3 (i : Nat) (hi : 8 * i < 2 ^ 64) : BitVec.ofNat 64 i <<< (3 : Nat) = BitVec.ofNat 64 (8 * i) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat]
  rw [Nat.shiftLeft_eq]
  have : i < 2 ^ 64 := by omega
  rw [Nat.mod_eq_of_lt this]; omega

/-- The cell address of index `ei` in the table at `A`. -/
def tblAddr (eA ei : ExpHOL 64) : ExpHOL 64 := .op .add [eA, .shift .lsl ei (.const 3)]

theorem sev_tblAddr (Γ : Env) (C : Ctx) (j i : Nat) (eA ei : ExpHOL 64) (heA : sev Γ eA = some (cellA C j))
    (hei : sev Γ ei = some (BitVec.ofNat 64 i))
    (hi : 8 * i < 2 ^ 64) : sev Γ (tblAddr eA ei) = some (cellA C (j + i)) := by
  simp only [tblAddr, sev, heA, hei, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some,
    show (3 : BitVec 64).toNat = 3 from rfl, show (3 : Nat) < 64 by decide, if_true]
  rw [shl3 i hi, cellA_add]

theorem sev_lower (Γ : Env) (ei ec : ExpHOL 64) (i cap : Nat) (hei : sev Γ ei = some (BitVec.ofNat 64 i))
    (hec : sev Γ ec = some (BitVec.ofNat 64 cap)) (hi : i < 2 ^ 64) (hc : cap < 2 ^ 64) :
    sev Γ (.cmp .lower ei ec) = some (bw (i < cap)) := by
  simp only [sev, hei, hec, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  congr 1
  simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, bw, BitVec.ult, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hc]
  by_cases h : i < cap <;> simp [h] <;> omega

theorem sev_eq0 (Γ : Env) (x : MlS) (w : BitVec 64) (hx : Γ.get x = some w) :
    sev Γ (.cmp .equal (.var .local x) (.const 0)) = some (bw (w = 0)) := by
  simp only [sev, hx, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  congr 1
  simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, bw]
  by_cases h : w = 0 <;> simp [h]

theorem Env.get_cons_self (Γ : Env) (x : MlS) (v : BitVec 64) : Env.get ((x, v) :: Γ) x = some v := by
  simp [Env.get]

/-- `x := table[ei]`, rejecting an index that is unbound or past the capacity. -/
def tblGetP (x : MlS) (eA ec ei : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .ite (.cmp .lower ei ec)
    (.seq (.assign .local x (.load .one (tblAddr eA ei)))
      (.ite (.cmp .equal (.var .local x) (.const 0)) hang
        (.seq (.assign .local x (.op .sub [.var .local x, .const 1])) rest)))
    hang

theorem specR_tblGetI {α : Type} {k : IdxKind} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (hx : x ∈ D) (j cap : Nat) (tbl : IdTable (Idx k)) (hrel : TblRel C.H j cap tbl)
    (hcap : 8 * cap < 2 ^ 64) (eA ec ei : ExpHOL 64) (heA : sev Γ eA = some (cellA C j))
    (hec : sev Γ ec = some (BitVec.ofNat 64 cap)) (i : Nat) (hi : i < 2 ^ 64)
    (hei : sev Γ ei = some (BitVec.ofNat 64 i))
    (hk : ∀ h, tbl.get? i = some h →
      SpecR (Inv C s ((x, Enc.idxW h) :: (x, Enc.idxW h + 1) :: Γ) M D) rest s m R) :
    SpecR (Inv C s Γ M D) (tblGetP x eA ec ei rest) s m R := by
  unfold tblGetP
  refine specR_ifI _ _ (sev_lower Γ ei ec i cap hei hec hi (by omega)) (fun hw => ?_) (fun _ => specR_hangI)
  have hic : i < cap := by
    by_cases h : i < cap
    · exact h
    · simp [bw, h] at hw
  have hcell := hrel.1 i hic
  have hlen : j + i < C.H.length := by
    by_cases hl : j + i < C.H.length
    · exact hl
    · rw [List.getElem?_eq_none (by omega)] at hcell; cases hcell
  have hHi : C.H[j + i] = tblW (tbl.get? i) := by
    rw [List.getElem?_eq_getElem hlen] at hcell; exact Option.some.inj hcell
  refine specR_heapLoadI x _ (j + i) hlen hx (sev_tblAddr Γ C j i eA ei heA hei (by omega)) ?_
  rw [hHi]
  cases hg : tbl.get? i with
  | none =>
    refine specR_ifI _ _ (sev_eq0 _ x _ (Env.get_cons_self _ _ _)) (fun _ => specR_hangI) (fun hw => ?_)
    simp [bw, tblW] at hw
  | some h =>
    refine specR_ifI _ _ (sev_eq0 _ x _ (Env.get_cons_self _ _ _)) (fun hw => ?_) (fun _ => ?_)
    · exact absurd (by simpa [bw] using hw) (tblW_some_ne h)
    · refine specR_assignI x _ (Enc.idxW h) hx ?_ (hk h hg)
      simp [sev, Env.get_cons_self, tblW, BitVec.add_sub_cancel]

/-- Insist that index `ei` is unbound (and below the capacity). -/
def tblFreshP (x : MlS) (eA ec ei : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .ite (.cmp .lower ei ec)
    (.seq (.assign .local x (.load .one (tblAddr eA ei)))
      (.ite (.cmp .equal (.var .local x) (.const 0)) rest hang))
    hang

theorem specR_tblFreshI {α : Type} {k : IdxKind} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (hx : x ∈ D) (j cap : Nat) (tbl : IdTable (Idx k)) (hrel : TblRel C.H j cap tbl)
    (hcap : 8 * cap < 2 ^ 64) (eA ec ei : ExpHOL 64) (heA : sev Γ eA = some (cellA C j))
    (hec : sev Γ ec = some (BitVec.ofNat 64 cap)) (i : Nat) (hi : i < 2 ^ 64)
    (hei : sev Γ ei = some (BitVec.ofNat 64 i))
    (hk : i < cap → tbl.get? i = none → SpecR (Inv C s ((x, 0) :: Γ) M D) rest s m R) :
    SpecR (Inv C s Γ M D) (tblFreshP x eA ec ei rest) s m R := by
  unfold tblFreshP
  refine specR_ifI _ _ (sev_lower Γ ei ec i cap hei hec hi (by omega)) (fun hw => ?_) (fun _ => specR_hangI)
  have hic : i < cap := by
    by_cases h : i < cap
    · exact h
    · simp [bw, h] at hw
  have hcell := hrel.1 i hic
  have hlen : j + i < C.H.length := by
    by_cases hl : j + i < C.H.length
    · exact hl
    · rw [List.getElem?_eq_none (by omega)] at hcell; cases hcell
  have hHi : C.H[j + i] = tblW (tbl.get? i) := by
    rw [List.getElem?_eq_getElem hlen] at hcell; exact Option.some.inj hcell
  refine specR_heapLoadI x _ (j + i) hlen hx (sev_tblAddr Γ C j i eA ei heA hei (by omega)) ?_
  rw [hHi]
  cases hg : tbl.get? i with
  | none =>
    refine specR_ifI _ _ (sev_eq0 _ x _ (Env.get_cons_self _ _ _)) (fun _ => hk hic hg) (fun hw => ?_)
    simp [bw, tblW] at hw
  | some h =>
    refine specR_ifI _ _ (sev_eq0 _ x _ (Env.get_cons_self _ _ _)) (fun hw => ?_) (fun _ => specR_hangI)
    exact absurd (by simpa [bw] using hw) (tblW_some_ne h)

/-- Binding an index keeps the relation, at the inserted table. -/
theorem tblRel_insert {k : IdxKind} {H : List (BitVec 64)} {j cap : Nat} {tbl : IdTable (Idx k)}
    (hrel : TblRel H j cap tbl) (i : Nat) (hi : i < cap) (h : Idx k) :
    TblRel (H.set (j + i) (Enc.idxW h + 1)) j cap (tbl.insert i h) := by
  refine ⟨fun i' hi' => ?_, fun i' hi' => ?_⟩
  · rw [IdTable.get?_insert, List.getElem?_set]
    by_cases e : i' = i
    · subst e
      have hl : j + i' < H.length := by
        have := hrel.1 i' hi'
        by_cases hl : j + i' < H.length
        · exact hl
        · rw [List.getElem?_eq_none (by omega)] at this; cases this
      simp [hl, tblW]
    · have e' : ¬ i = i' := fun h => e h.symm
      have : j + i ≠ j + i' := by omega
      simp [this, e, e', hrel.1 i' hi']
  · rw [IdTable.get?_insert, if_neg (by omega)]; exact hrel.2 i' hi'

/-- Another table's cells are unchanged by a write outside them. -/
theorem tblRel_set_other {k : IdxKind} {H : List (BitVec 64)} {j cap : Nat} {tbl : IdTable (Idx k)}
    (hrel : TblRel H j cap tbl) (c : Nat) (hc : c < j ∨ j + cap ≤ c) (w : BitVec 64) :
    TblRel (H.set c w) j cap tbl := by
  refine ⟨fun i hi => ?_, hrel.2⟩
  rw [List.getElem?_set, if_neg (by omega)]; exact hrel.1 i hi

/-- Bind index `ei` to the handle in `eh` (`*cell := eh + 1`). -/
def tblSetP (eA ei eh : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (tblAddr eA ei) (.op .add [eh, .const 1])) rest

theorem specR_tblSetI {α : Type} {k : IdxKind} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem}
    {D : List MlS} {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (j cap : Nat) (tbl : IdTable (Idx k)) (hrel : TblRel C.H j cap tbl) (hcap : 8 * cap < 2 ^ 64)
    (eA ei eh : ExpHOL 64) (heA : sev Γ eA = some (cellA C j)) (i : Nat) (hic : i < cap) (h : Idx k)
    (hei : sev Γ ei = some (BitVec.ofNat 64 i)) (heh : sev Γ eh = some (Enc.idxW h))
    (hk : TblRel (C.H.set (j + i) (Enc.idxW h + 1)) j cap (tbl.insert i h) →
      SpecR (Inv (ctxH C (C.H.set (j + i) (Enc.idxW h + 1))) s Γ [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (tblSetP eA ei eh rest) s m R := by
  have hcell := hrel.1 i hic
  have hlen : j + i < C.H.length := by
    by_cases hl : j + i < C.H.length
    · exact hl
    · rw [List.getElem?_eq_none (by omega)] at hcell; cases hcell
  exact specR_heapStoreI hok _ _ (j + i) hlen _ (sev_tblAddr Γ C j i eA ei heA hei (by omega))
    (by simp [sev, heh]) (hk (tblRel_insert hrel i hic h))

end ConPanqueque.Front
