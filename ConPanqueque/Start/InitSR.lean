import ConPanqueque.Start.InitMem

/-! # The stores after the initial image

`srep_init`: after `storesP initL` from a zeroed region, memory represents the bootstrap store
(`SRep` at the concrete layout). -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open ConRon.Arena ConPanqueque.V ConPanqueque.T ConPanqueque.Code

namespace ConPanqueque.Start

variable {σ : Type}

set_option maxRecDepth 100000

theorem geo_eq (k tier : Nat) : layout.geo k tier = geoAt (T0 + (2 * k + tier) * TW) := rfl

theorem tab_empty {t : PanSemStateFiniteExact 64 σ} (hm : InitMem t) (k tier : Nat) (hk : k < 19) (ht : tier < 2)
    (h0 : 2 * k + tier ≠ 0) (h6 : 2 * k + tier ≠ 6) {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α]
    (enc : α → List (BitVec 64)) (dW : δ → BitVec 64 × BitVec 64) (mkI : Nat → ι) :
    TabAt (tI t) layout k tier enc dW (Tbl.empty : Tbl α ι δ) mkI :=
  tabAt_empty _ _ _ _ _ _ _ (descV_store hm k tier hk ht) (by simp [geo_eq, geoAt])
    (by rw [geo_eq]; exact emptyMem_store hm _ (by omega) h0 h6)

/-- The four scratch-flag words are not written. -/
theorem clear_fl : ∀ p ∈ initL, p.1.toNat ≠ base + 4096 ∧ p.1.toNat ≠ base + 4104 ∧ p.1.toNat ≠ base + 4112 ∧
    p.1.toNat ≠ base + 4120 := by decide +kernel

theorem fl_zero {t : PanSemStateFiniteExact 64 σ} (hm : InitMem t) (j : Nat) (hj : j < 4) :
    (tI t).memaddrs (BitVec.ofNat 64 (base + 4096 + 8 * j)) ∧
      (tI t).memory (BitVec.ofNat 64 (base + 4096 + 8 * j)) = .word 0 :=
  tI_out hm _ (by addr_tac) (by addr_tac) (by addr_tac) (fun p hp e => by
    have c := clear_fl p hp
    rw [e] at c
    rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
    · exact c.1 (by addr_tac)
    · exact c.2.1 (by addr_tac)
    · exact c.2.2.1 (by addr_tac)
    · exact c.2.2.2 (by addr_tac))

theorem fl_word {t : PanSemStateFiniteExact 64 σ} (hm : InitMem t) (j : Nat) (hj : j < 4) (b : Bool) (hb : b = false) :
    (tI t).memaddrs (BitVec.ofNat 64 (base + 4096 + 8 * j)) ∧
      (tI t).memory (BitVec.ofNat 64 (base + 4096 + 8 * j)) = .word (if b then 1 else 0) := by
  subst hb; exact fl_zero hm j hj

theorem srep_init {t : PanSemStateFiniteExact 64 σ} (hm : InitMem t) :
    SRep (tI t) layout (BitVec.ofNat 64 (base + 4096)) (BitVec.ofNat 64 (base + 4104))
      (BitVec.ofNat 64 (base + 4112)) (BitVec.ofNat 64 (base + 4120)) bootStore where
  e := {
    fl := fl_word hm 3 (by decide) _ bootStore_on.1
    p0 := tab_empty hm 9 0 (by decide) (by decide) (by decide) (by decide) _ _ _
    p1 := tab_empty hm 10 0 (by decide) (by decide) (by decide) (by decide) _ _ _
    p2 := tab_empty hm 11 0 (by decide) (by decide) (by decide) (by decide) _ _ _
    p3 := tab_empty hm 12 0 (by decide) (by decide) (by decide) (by decide) _ _ _
    p4 := tab_empty hm 13 0 (by decide) (by decide) (by decide) (by decide) _ _ _
    p5 := tab_empty hm 14 0 (by decide) (by decide) (by decide) (by decide) _ _ _
    p6 := tab_empty hm 15 0 (by decide) (by decide) (by decide) (by decide) _ _ _
    p7 := tab_empty hm 16 0 (by decide) (by decide) (by decide) (by decide) _ _ _
    p8 := tab_empty hm 17 0 (by decide) (by decide) (by decide) (by decide) _ _ _
    p9 := tab_empty hm 18 0 (by decide) (by decide) (by decide) (by decide) _ _ _
    s0 := tab_empty hm 9 1 (by decide) (by decide) (by decide) (by decide) _ _ _
    s1 := tab_empty hm 10 1 (by decide) (by decide) (by decide) (by decide) _ _ _
    s2 := tab_empty hm 11 1 (by decide) (by decide) (by decide) (by decide) _ _ _
    s3 := tab_empty hm 12 1 (by decide) (by decide) (by decide) (by decide) _ _ _
    s4 := tab_empty hm 13 1 (by decide) (by decide) (by decide) (by decide) _ _ _
    s5 := tab_empty hm 14 1 (by decide) (by decide) (by decide) (by decide) _ _ _
    s6 := tab_empty hm 15 1 (by decide) (by decide) (by decide) (by decide) _ _ _
    s7 := tab_empty hm 16 1 (by decide) (by decide) (by decide) (by decide) _ _ _
    s8 := tab_empty hm 17 1 (by decide) (by decide) (by decide) (by decide) _ _ _
    s9 := tab_empty hm 18 1 (by decide) (by decide) (by decide) (by decide) _ _ _ }
  ls := {
    fl := fl_word hm 2 (by decide) _ bootStore_on.2.1
    pl := tab_empty hm 8 0 (by decide) (by decide) (by decide) (by decide) _ _ _
    sl := tab_empty hm 8 1 (by decide) (by decide) (by decide) (by decide) _ _ _ }
  l := {
    fl := fl_word hm 1 (by decide) _ bootStore_on.2.2.1
    pz := by
      rw [show bootStore.lss.ls.pers = _ from bootStore_lsP]
      exact tabAt_one _ _ _ _ _ _ _ ZeroNode.mk rfl _ (descV_store hm 3 0 (by decide) (by decide))
        (by simp [geo_eq, geoAt]) (by rw [geo_eq]; exact oneMem_store hm 6 (by decide) _ rfl)
    ps := by rw [show bootStore.lss.ls.pers = _ from bootStore_lsP]; exact tab_empty hm 4 0 (by decide) (by decide) (by decide) (by decide) _ _ _
    pm := by rw [show bootStore.lss.ls.pers = _ from bootStore_lsP]; exact tab_empty hm 5 0 (by decide) (by decide) (by decide) (by decide) _ _ _
    pi := by rw [show bootStore.lss.ls.pers = _ from bootStore_lsP]; exact tab_empty hm 6 0 (by decide) (by decide) (by decide) (by decide) _ _ _
    pp := by rw [show bootStore.lss.ls.pers = _ from bootStore_lsP]; exact tab_empty hm 7 0 (by decide) (by decide) (by decide) (by decide) _ _ _
    sz := by rw [show bootStore.lss.ls.scr = _ from bootStore_lsS]; exact tab_empty hm 3 1 (by decide) (by decide) (by decide) (by decide) _ _ _
    ss := by rw [show bootStore.lss.ls.scr = _ from bootStore_lsS]; exact tab_empty hm 4 1 (by decide) (by decide) (by decide) (by decide) _ _ _
    sm := by rw [show bootStore.lss.ls.scr = _ from bootStore_lsS]; exact tab_empty hm 5 1 (by decide) (by decide) (by decide) (by decide) _ _ _
    si := by rw [show bootStore.lss.ls.scr = _ from bootStore_lsS]; exact tab_empty hm 6 1 (by decide) (by decide) (by decide) (by decide) _ _ _
    sp := by rw [show bootStore.lss.ls.scr = _ from bootStore_lsS]; exact tab_empty hm 7 1 (by decide) (by decide) (by decide) (by decide) _ _ _ }
  n := {
    fl := fl_word hm 0 (by decide) _ bootStore_on.2.2.2
    pa := by
      rw [show bootStore.lss.ls.ns.pers = _ from bootStore_nsP]
      exact tabAt_one _ _ _ _ _ _ _ AnonNode.mk rfl _ (descV_store hm 0 0 (by decide) (by decide))
        (by simp [geo_eq, geoAt]) (by rw [geo_eq]; exact oneMem_store hm 0 (by decide) _ rfl)
    ps := by rw [show bootStore.lss.ls.ns.pers = _ from bootStore_nsP]; exact tab_empty hm 1 0 (by decide) (by decide) (by decide) (by decide) _ _ _
    pn := by rw [show bootStore.lss.ls.ns.pers = _ from bootStore_nsP]; exact tab_empty hm 2 0 (by decide) (by decide) (by decide) (by decide) _ _ _
    sa := by rw [show bootStore.lss.ls.ns.scr = _ from bootStore_nsS]; exact tab_empty hm 0 1 (by decide) (by decide) (by decide) (by decide) _ _ _
    ss := by rw [show bootStore.lss.ls.ns.scr = _ from bootStore_nsS]; exact tab_empty hm 1 1 (by decide) (by decide) (by decide) (by decide) _ _ _
    sn := by rw [show bootStore.lss.ls.ns.scr = _ from bootStore_nsS]; exact tab_empty hm 2 1 (by decide) (by decide) (by decide) (by decide) _ _ _ }

end ConPanqueque.Start
