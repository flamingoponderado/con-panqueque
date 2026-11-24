import ConPanqueque.Start.Image
import ConPanqueque.Start.Empty

/-! # Memory after the initial stores

`InitMem t`: the harness's mapping, every aligned word of the region `[base, base + SZ)` addressable
and zero.  After `storesP initL` (`tI t`), a listed address holds its word, any other address in the
region holds zero.  From that, every table's descriptor (`DescV`) and its empty or one-row contents
(`EmptyMem`, `OneMem`). -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open ConRon.Arena ConPanqueque.V ConPanqueque.T ConPanqueque.Code

namespace ConPanqueque.Start

variable {σ : Type}

set_option maxRecDepth 100000

def SZ : Nat := H0 + 8 * HNw

structure InitMem (t : PanSemStateFiniteExact 64 σ) : Prop where
  zero : ∀ a : BitVec 64, a.toNat % 8 = 0 → base ≤ a.toNat → a.toNat < base + SZ →
    t.memaddrs a ∧ t.memory a = .word 0

def tI (t : PanSemStateFiniteExact 64 σ) : PanSemStateFiniteExact 64 σ := { t with memory := updL t.memory initL }

theorem tI_in {t : PanSemStateFiniteExact 64 σ} (hm : InitMem t) (a w : BitVec 64) (hal : a.toNat % 8 = 0)
    (h1 : base ≤ a.toNat) (h2 : a.toNat < base + SZ) (h : (a, w) ∈ initL) :
    (tI t).memaddrs a ∧ (tI t).memory a = .word w :=
  ⟨(hm.zero a hal h1 h2).1, updL_mem _ _ _ _ initL_nodup h⟩

theorem tI_out {t : PanSemStateFiniteExact 64 σ} (hm : InitMem t) (a : BitVec 64) (hal : a.toNat % 8 = 0)
    (h1 : base ≤ a.toNat) (h2 : a.toNat < base + SZ) (h : ∀ p ∈ initL, p.1.toNat ≠ a.toNat) :
    (tI t).memaddrs a ∧ (tI t).memory a = .word 0 := by
  refine ⟨(hm.zero a hal h1 h2).1, ?_⟩
  show updL t.memory initL a = _
  rw [updL_not_mem _ _ _ (fun hm' => ?_)]
  · exact (hm.zero a hal h1 h2).2
  · obtain ⟨p, hp, e⟩ := List.mem_map.mp hm'
    exact h p hp (by rw [e])

theorem tI_dom {t : PanSemStateFiniteExact 64 σ} (hm : InitMem t) (a : BitVec 64) (hal : a.toNat % 8 = 0)
    (h1 : base ≤ a.toNat) (h2 : a.toNat < base + SZ) : (tI t).memaddrs a := (hm.zero a hal h1 h2).1

/-! ## Where the list writes -/

/-- A store table's slots past slot 0 are not written. -/
theorem clear_slots : ∀ i, i < 38 → ∀ p ∈ initL,
    ¬ (base + T0 + i * TW + 24 ≤ p.1.toNat ∧ p.1.toNat < base + T0 + i * TW + 16 + 8 * 2 ^ 14) := by
  decide +kernel

/-- An empty store table's count word and slot 0 are not written. -/
theorem clear_head : ∀ i, i < 38 → i ≠ 0 → i ≠ 6 → ∀ p ∈ initL,
    p.1.toNat ≠ base + T0 + i * TW ∧ p.1.toNat ≠ base + T0 + i * TW + 16 := by
  decide +kernel

/-- The bootstrap rows' length words (and the anonymous name's second derived word) are not written. -/
theorem clear_row : ∀ p ∈ initL,
    p.1.toNat ≠ base + T0 + 0 * TW + 16 + 8 * 2 ^ 14 + 8 ∧ p.1.toNat ≠ base + T0 + 6 * TW + 16 + 8 * 2 ^ 14 + 8 ∧
    p.1.toNat ≠ base + T0 + 0 * TW + 16 + 8 * 2 ^ 14 + 16 * 2 ^ 16 + 8 := by
  decide +kernel

/-- A memo table's count word and slots are not written. -/
theorem clear_memo : ∀ i, i < 37 → ∀ p ∈ initL, p.1.toNat ≠ base + M0 + i * TW ∧
    ¬ (base + M0 + i * TW + 16 ≤ p.1.toNat ∧ p.1.toNat < base + M0 + i * TW + 16 + 8 * 2 ^ 14) := by
  decide +kernel

/-! ## Address arithmetic -/

set_option hygiene false in
macro "addr_tac" : tactic => `(tactic| (
    simp only [descAddr, layout, geoAt, w64, addr_add, base, T0, TW, M0, E0, H0, HNw, SZ, BitVec.ofNat_eq_ofNat] at *
    try simp (disch := omega) only [toNat_addr] at *
    try simp only [BitVec.toNat_ofNat] at *
    all_goals omega))

theorem toNat_w64 (n : Nat) (h : n < 2 ^ 64) : (w64 n).toNat = n := toNat_addr n h

/-! ## Descriptors -/

theorem mem_storeDesc (k tier m : Nat) (hk : k < 19) (ht : tier < 2) (hm8 : m < 8) :
    (descAddr layout k tier + w64 (8 * m), (descV (layout.geo k tier) (layout.base k tier)).getD m 0) ∈ initL := by
  unfold initL
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ ?_)))
  refine List.mem_flatMap.mpr ⟨19 * tier + k, List.mem_range.mpr (by omega), ?_⟩
  rw [show (19 * tier + k) % 19 = k by omega, show (19 * tier + k) / 19 = tier by omega]
  exact List.mem_map.mpr ⟨m, List.mem_range.mpr hm8, rfl⟩

theorem descV_getD (g : VGeo) (b : BitVec 64) (m : Nat) (hm : m < 8) :
    (descV g b).getD m 0 = (descV g b)[m]'(by simp [descV]; omega) := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show m < (descV g b).length by simp [descV]; omega)]

theorem descV_store {t : PanSemStateFiniteExact 64 σ} (hm : InitMem t) (k tier : Nat) (hk : k < 19) (ht : tier < 2) :
    DescV (tI t) (descAddr layout k tier) (layout.geo k tier) (layout.base k tier) := by
  intro m hm8
  have h := tI_in hm _ _ (by addr_tac) (by addr_tac) (by addr_tac) (mem_storeDesc k tier m hk ht hm8)
  rw [descV_getD _ _ m hm8] at h
  exact ⟨by simpa [w64] using h.1, by simpa [w64] using h.2⟩

theorem mem_memoDesc (i m : Nat) (hi : i < 37) (hm8 : m < 8) :
    (w64 (base + 65536 + 64 * i) + w64 (8 * m), (descV (geoAt (M0 + i * TW)) 1).getD m 0) ∈ initL := by
  unfold initL
  refine List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ ?_)))
  exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, List.mem_map.mpr ⟨m, List.mem_range.mpr hm8, rfl⟩⟩

theorem descV_memo {t : PanSemStateFiniteExact 64 σ} (hm : InitMem t) (i : Nat) (hi : i < 37) :
    DescV (tI t) (w64 (base + 65536 + 64 * i)) (geoAt (M0 + i * TW)) 1 := by
  intro m hm8
  have h := tI_in hm _ _ (by addr_tac) (by addr_tac) (by addr_tac) (mem_memoDesc i m hi hm8)
  rw [descV_getD _ _ m hm8] at h
  exact ⟨by simpa [w64] using h.1, by simpa [w64] using h.2⟩

/-! ## Table contents -/

theorem mem_storeTbl (i : Nat) (hi : i < 38) (p : BitVec 64 × BitVec 64) (hp : p ∈ tblL i) : p ∈ initL := by
  unfold initL
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _
    (List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, hp⟩)))

theorem mem_memoTbl (i : Nat) (hi : i < 37) :
    ((geoAt (M0 + i * TW)).C + 8, (geoAt (M0 + i * TW)).KH) ∈ initL := by
  unfold initL
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))

theorem emptyMem_store {t : PanSemStateFiniteExact 64 σ} (hm : InitMem t) (i : Nat) (hi : i < 38) (h0 : i ≠ 0)
    (h6 : i ≠ 6) : EmptyMem (tI t) (geoAt (T0 + i * TW)) where
  slot j hj := by
    simp only [geoAt] at hj
    refine tI_out hm _ (by addr_tac) (by addr_tac) (by addr_tac) (fun p hp e => ?_)
    have c1 := clear_slots i hi p hp
    have c2 := (clear_head i hi h0 h6 p hp).2
    simp only [geoAt] at e
    rw [e] at c1 c2
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · exact c2 (by addr_tac)
    · exact c1 ⟨by addr_tac, by addr_tac⟩
  room i' hi' := by
    simp only [geoAt] at hi' ⊢
    exact ⟨tI_dom hm _ (by addr_tac) (by addr_tac) (by addr_tac), tI_dom hm _ (by addr_tac) (by addr_tac) (by addr_tac),
      tI_dom hm _ (by addr_tac) (by addr_tac) (by addr_tac), tI_dom hm _ (by addr_tac) (by addr_tac) (by addr_tac)⟩
  hroom k hk := by
    simp only [geoAt] at hk ⊢
    exact tI_dom hm _ (by addr_tac) (by addr_tac) (by addr_tac)
  cnt := tI_out hm _ (by addr_tac) (by addr_tac) (by addr_tac) (fun p hp e => (clear_head i hi h0 h6 p hp).1 (by
    rw [e]; addr_tac))
  top := tI_in hm _ _ (by addr_tac) (by addr_tac) (by addr_tac)
    (mem_storeTbl i hi _ (by simp [tblL, h0, h6]))
  layC := by addr_tac
  layS := by addr_tac
  layR := by addr_tac
  layD := by addr_tac
  layK := by addr_tac
  pos := by simp [geoAt]
  pow := rfl

theorem oneMem_store {t : PanSemStateFiniteExact 64 σ} (hm : InitMem t) (i : Nat) (hi : i = 0 ∨ i = 6)
    (d : BitVec 64 × BitVec 64) (hd : d = if i = 0 then (dAnon, 0) else dZero) :
    OneMem (tI t) (geoAt (T0 + i * TW)) d where
  slot0 := tI_in hm _ _ (by rcases hi with rfl | rfl <;> addr_tac) (by rcases hi with rfl | rfl <;> addr_tac)
    (by rcases hi with rfl | rfl <;> addr_tac) (mem_storeTbl i (by omega) _ (by rcases hi with rfl | rfl <;> simp [tblL]))
  slot j hj0 hj := by
    simp only [geoAt] at hj
    refine tI_out hm _ (by rcases hi with rfl | rfl <;> addr_tac) (by rcases hi with rfl | rfl <;> addr_tac)
      (by rcases hi with rfl | rfl <;> addr_tac) (fun p hp e => ?_)
    have c1 := clear_slots i (by omega) p hp
    simp only [geoAt] at e
    rw [e] at c1
    exact c1 ⟨by rcases hi with rfl | rfl <;> addr_tac, by rcases hi with rfl | rfl <;> addr_tac⟩
  row := by
    refine ⟨(tI_in hm _ _ (by rcases hi with rfl | rfl <;> addr_tac) (by rcases hi with rfl | rfl <;> addr_tac)
      (by rcases hi with rfl | rfl <;> addr_tac)
      (mem_storeTbl i (by omega) _ (by rcases hi with rfl | rfl <;> simp [tblL]))).2, ?_⟩
    refine (tI_out hm _ (by rcases hi with rfl | rfl <;> addr_tac) (by rcases hi with rfl | rfl <;> addr_tac)
      (by rcases hi with rfl | rfl <;> addr_tac) (fun p hp e => ?_)).2
    have c := clear_row p hp
    rw [e] at c
    rcases hi with rfl | rfl
    · exact c.1 (by addr_tac)
    · exact c.2.1 (by addr_tac)
  der := by
    rcases hi with rfl | rfl
    · subst hd
      refine ⟨(tI_in hm _ _ (by addr_tac) (by addr_tac) (by addr_tac)
        (mem_storeTbl 0 (by omega) _ (by simp [tblL]))).2, ?_⟩
      refine (tI_out hm _ (by addr_tac) (by addr_tac) (by addr_tac) (fun p hp e => ?_)).2
      have c := (clear_row p hp).2.2
      rw [e] at c; exact c (by addr_tac)
    · subst hd
      exact ⟨(tI_in hm _ _ (by addr_tac) (by addr_tac) (by addr_tac)
        (mem_storeTbl 6 (by omega) _ (by simp [tblL]))).2,
        (tI_in hm _ _ (by addr_tac) (by addr_tac) (by addr_tac)
        (mem_storeTbl 6 (by omega) _ (by simp [tblL]))).2⟩
  room i' hi' := by
    simp only [geoAt] at hi' ⊢
    rcases hi with rfl | rfl <;>
    exact ⟨tI_dom hm _ (by addr_tac) (by addr_tac) (by addr_tac), tI_dom hm _ (by addr_tac) (by addr_tac) (by addr_tac),
      tI_dom hm _ (by addr_tac) (by addr_tac) (by addr_tac), tI_dom hm _ (by addr_tac) (by addr_tac) (by addr_tac)⟩
  hroom k hk := by
    simp only [geoAt] at hk ⊢
    rcases hi with rfl | rfl <;> exact tI_dom hm _ (by addr_tac) (by addr_tac) (by addr_tac)
  cnt := tI_in hm _ _ (by rcases hi with rfl | rfl <;> addr_tac) (by rcases hi with rfl | rfl <;> addr_tac)
    (by rcases hi with rfl | rfl <;> addr_tac) (mem_storeTbl i (by omega) _ (by rcases hi with rfl | rfl <;> simp [tblL]))
  top := tI_in hm _ _ (by rcases hi with rfl | rfl <;> addr_tac) (by rcases hi with rfl | rfl <;> addr_tac)
    (by rcases hi with rfl | rfl <;> addr_tac) (mem_storeTbl i (by omega) _ (by rcases hi with rfl | rfl <;> simp [tblL]))
  layC := by addr_tac
  layS := by addr_tac
  layR := by addr_tac
  layD := by addr_tac
  layK := by rcases hi with rfl | rfl <;> addr_tac
  pos := by simp [geoAt]
  cap1 := by simp [geoAt]
  pow := rfl

theorem emptyMem_memo {t : PanSemStateFiniteExact 64 σ} (hm : InitMem t) (i : Nat) (hi : i < 37) :
    EmptyMem (tI t) (geoAt (M0 + i * TW)) where
  slot j hj := by
    simp only [geoAt] at hj
    refine tI_out hm _ (by addr_tac) (by addr_tac) (by addr_tac) (fun p hp e => ?_)
    have c1 := (clear_memo i hi p hp).2
    simp only [geoAt] at e
    rw [e] at c1
    exact c1 ⟨by addr_tac, by addr_tac⟩
  room i' hi' := by
    simp only [geoAt] at hi' ⊢
    exact ⟨tI_dom hm _ (by addr_tac) (by addr_tac) (by addr_tac), tI_dom hm _ (by addr_tac) (by addr_tac) (by addr_tac),
      tI_dom hm _ (by addr_tac) (by addr_tac) (by addr_tac), tI_dom hm _ (by addr_tac) (by addr_tac) (by addr_tac)⟩
  hroom k hk := by
    simp only [geoAt] at hk ⊢
    exact tI_dom hm _ (by addr_tac) (by addr_tac) (by addr_tac)
  cnt := tI_out hm _ (by addr_tac) (by addr_tac) (by addr_tac) (fun p hp e => (clear_memo i hi p hp).1 (by
    rw [e]; addr_tac))
  top := tI_in hm _ _ (by addr_tac) (by addr_tac) (by addr_tac) (mem_memoTbl i hi)
  layC := by addr_tac
  layS := by addr_tac
  layR := by addr_tac
  layD := by addr_tac
  layK := by addr_tac
  pos := by simp [geoAt]
  pow := rfl

end ConPanqueque.Start
