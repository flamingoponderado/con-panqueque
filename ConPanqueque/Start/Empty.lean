import ConPanqueque.Code.Layout

/-! # Empty tables in zeroed memory

A table whose descriptor is written, whose count word and slots are zero and whose top word is
its key-heap base represents the empty table (`TabAt` of `Tbl.empty`, `MemoAtG` of `∅`). -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open ConPanqueque.V ConPanqueque.T ConPanqueque.ConsModel ConPanqueque.ConsTbl ConRon.Arena

namespace ConPanqueque.Start

variable {σ : Type}

/-- The memory facts an empty table needs at geometry `g`. -/
structure EmptyMem (t : PanSemStateFiniteExact 64 σ) (g : VGeo) : Prop where
  slot : ∀ j, j < g.n → t.memaddrs (g.S + BitVec.ofNat 64 (8 * j)) ∧
    t.memory (g.S + BitVec.ofNat 64 (8 * j)) = .word 0
  room : ∀ i, i < g.cap → t.memaddrs (g.R + BitVec.ofNat 64 (16 * i)) ∧
    t.memaddrs (g.R + BitVec.ofNat 64 (16 * i) + 8) ∧ t.memaddrs (g.D + BitVec.ofNat 64 (16 * i)) ∧
    t.memaddrs (g.D + BitVec.ofNat 64 (16 * i) + 8)
  hroom : ∀ k, k < g.kcap → t.memaddrs (g.KH + BitVec.ofNat 64 (8 * k))
  cnt : t.memaddrs g.C ∧ t.memory g.C = .word 0
  top : t.memaddrs (g.C + 8) ∧ t.memory (g.C + 8) = .word g.KH
  layC : g.C.toNat + 16 ≤ g.S.toNat
  layS : g.S.toNat + 8 * g.n ≤ g.R.toNat
  layR : g.R.toNat + 16 * g.cap ≤ g.D.toNat
  layD : g.D.toNat + 16 * g.cap ≤ g.KH.toNat
  layK : g.KH.toNat + 8 * g.kcap < 2 ^ 64
  pos : 0 < g.n
  pow : g.n = 2 ^ g.b

theorem vt_empty {α : Type} (t : PanSemStateFiniteExact 64 σ) (enc : α → List (BitVec 64)) (g : VGeo)
    (h : EmptyMem t g) : VT t enc [] [] (List.replicate g.n 0) g 0 where
  slot j hj := ⟨0, by simp [hj], by decide, (h.slot j hj).1, by rw [(h.slot j hj).2]; rfl⟩
  row i hi := absurd hi (by simp)
  short i hi := absurd hi (by simp)
  cnt := ⟨h.cnt.1, by rw [h.cnt.2]; rfl⟩
  top := ⟨h.top.1, by rw [h.top.2]; simp⟩
  hu_le := Nat.zero_le _
  dlen := rfl
  der i hi := absurd hi (by simp)
  le := Nat.zero_le _
  room := h.room
  hroom := h.hroom
  layC := h.layC
  layS := h.layS
  layR := h.layR
  layD := h.layD
  layK := h.layK

theorem inv_empty {α : Type} (enc : α → List (BitVec 64)) (g : VGeo) (h : EmptyMem t g) :
    Inv (homeV enc g.b) ([] : List α) (List.replicate g.n 0) g.n where
  len := by simp
  pos := h.pos
  home_lt a := by unfold homeV; rw [h.pow]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  named j i hj := by
    rw [List.getElem?_replicate] at hj; split at hj <;> simp at hj
  reach i hi := absurd hi (by simp)
  rows_nodup := List.nodup_nil
  uniq j _ i hj _ := by
    rw [List.getElem?_replicate] at hj; split at hj <;> simp at hj

theorem tblRel_empty {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α] (mk : Nat → ι) :
    TblRel (Tbl.empty : Tbl α ι δ) [] mk :=
  ⟨rfl, fun a => by simp [Tbl.empty]⟩

theorem tabAt_empty {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α]
    (t : PanSemStateFiniteExact 64 σ) (L : Layout) (k tier : Nat) (enc : α → List (BitVec 64))
    (dW : δ → BitVec 64 × BitVec 64) (mkI : Nat → ι)
    (hd : DescV t (descAddr L k tier) (L.geo k tier) (L.base k tier)) (hcap : (L.geo k tier).cap < 2 ^ 30)
    (h : EmptyMem t (L.geo k tier)) : TabAt t L k tier enc dW (Tbl.empty : Tbl α ι δ) mkI :=
  ⟨hd, hcap, [], [], _, 0, ⟨vt_empty t enc _ h, inv_empty enc _ h, tblRel_empty mkI, rfl⟩⟩

theorem memoAtG_empty {K V : Type} [BEq K] [LawfulBEq K] [Hashable K] [DecidableEq K] [Inhabited V]
    (enc : K → List (BitVec 64)) (valW : V → BitVec 64) (t : PanSemStateFiniteExact 64 σ) (G : BitVec 64) (g : VGeo)
    (hd : DescV t G g 1) (hb : g.b ≤ 56) (hcap : g.cap < 2 ^ 30) (h : EmptyMem t g) :
    MemoAtG enc valW t G g (∅ : Std.HashMap K V) :=
  ⟨hd, h.pow, hb, hcap, Tbl.empty, [], [], _, 0, vt_empty t enc _ h, inv_empty enc _ h, tblRel_empty id, rfl,
    fun k => by simp [Tbl.empty, Tbl.find?]⟩

/-- The memory facts of a one-row table whose row has the empty key, at home slot 0. -/
structure OneMem (t : PanSemStateFiniteExact 64 σ) (g : VGeo) (d : BitVec 64 × BitVec 64) : Prop where
  slot0 : t.memaddrs g.S ∧ t.memory g.S = .word 1
  slot : ∀ j, 0 < j → j < g.n → t.memaddrs (g.S + BitVec.ofNat 64 (8 * j)) ∧
    t.memory (g.S + BitVec.ofNat 64 (8 * j)) = .word 0
  row : t.memory g.R = .word g.KH ∧ t.memory (g.R + 8) = .word 0
  der : t.memory g.D = .word d.1 ∧ t.memory (g.D + 8) = .word d.2
  room : ∀ i, i < g.cap → t.memaddrs (g.R + BitVec.ofNat 64 (16 * i)) ∧
    t.memaddrs (g.R + BitVec.ofNat 64 (16 * i) + 8) ∧ t.memaddrs (g.D + BitVec.ofNat 64 (16 * i)) ∧
    t.memaddrs (g.D + BitVec.ofNat 64 (16 * i) + 8)
  hroom : ∀ k, k < g.kcap → t.memaddrs (g.KH + BitVec.ofNat 64 (8 * k))
  cnt : t.memaddrs g.C ∧ t.memory g.C = .word 1
  top : t.memaddrs (g.C + 8) ∧ t.memory (g.C + 8) = .word g.KH
  layC : g.C.toNat + 16 ≤ g.S.toNat
  layS : g.S.toNat + 8 * g.n ≤ g.R.toNat
  layR : g.R.toNat + 16 * g.cap ≤ g.D.toNat
  layD : g.D.toNat + 16 * g.cap ≤ g.KH.toNat
  layK : g.KH.toNat + 8 * g.kcap < 2 ^ 64
  pos : 1 < g.n
  cap1 : 1 ≤ g.cap
  pow : g.n = 2 ^ g.b

def slots1 (n : Nat) : List Nat := (List.replicate n 0).set 0 1

theorem slots1_get (n j : Nat) (hj : j < n) : (slots1 n)[j]? = some (if j = 0 then 1 else 0) := by
  unfold slots1; rw [List.getElem?_set]; split
  · subst_vars; simp [hj]
  · rename_i h; simp [List.getElem?_replicate, hj, show ¬ j = 0 from fun e => h e.symm]

theorem vt_one {α : Type} (t : PanSemStateFiniteExact 64 σ) (enc : α → List (BitVec 64)) (g : VGeo) (x : α)
    (hx : enc x = []) (d : BitVec 64 × BitVec 64) (h : OneMem t g d) : VT t enc [x] [d] (slots1 g.n) g 0 where
  slot j hj := by
    refine ⟨if j = 0 then 1 else 0, slots1_get _ _ hj, by split <;> decide, ?_⟩
    by_cases h0 : j = 0
    · subst h0; simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero, if_true]
      exact ⟨h.slot0.1, by rw [h.slot0.2]; rfl⟩
    · rw [if_neg h0]; exact ⟨(h.slot j (by omega) hj).1, by rw [(h.slot j (by omega) hj).2]; rfl⟩
  row i hi := by
    have : i = 0 := by simpa using hi
    subst this
    have r0 := h.room 0 h.cap1
    simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at r0 ⊢
    refine ⟨g.KH, r0.1, r0.2.1, h.row.1, by simpa [hx] using h.row.2, fun k hk => by simp [hx] at hk, le_refl _,
      by simp [hx]⟩
  short i hi := by have : i = 0 := by simpa using hi
                   subst this; simp [hx]
  cnt := ⟨h.cnt.1, by rw [h.cnt.2]; rfl⟩
  top := ⟨h.top.1, by rw [h.top.2]; simp⟩
  hu_le := Nat.zero_le _
  dlen := rfl
  der i hi := by
    have : i = 0 := by simpa using hi
    subst this
    have r0 := h.room 0 h.cap1
    simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at r0 ⊢
    exact ⟨r0.2.2.1, r0.2.2.2, h.der.1, h.der.2⟩
  le := by simpa using h.cap1
  room := h.room
  hroom := h.hroom
  layC := h.layC
  layS := h.layS
  layR := h.layR
  layD := h.layD
  layK := h.layK

theorem inv_one {α : Type} (enc : α → List (BitVec 64)) (g : VGeo) (x : α) (hx : enc x = []) (d)
    (h : OneMem t g d) : Inv (homeV enc g.b) [x] (slots1 g.n) g.n where
  len := by simp [slots1]
  pos := by have := h.pos; omega
  home_lt a := by unfold homeV; rw [h.pow]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  named j i hj := by
    by_cases hjn : j < g.n
    · rw [slots1_get _ _ hjn] at hj; split at hj <;> simp at hj ⊢; omega
    · rw [List.getElem?_eq_none (by simp [slots1]; omega)] at hj; cases hj
  reach i hi := by
    have : i = 0 := by simpa using hi
    subst this
    refine ⟨0, by have := h.pos; omega, ?_, fun d' hd' => absurd hd' (by omega)⟩
    have h0 : homeV enc g.b x = 0 := by simp [homeV, hx, hashW]
    simp only [List.getElem_cons_zero, h0, at_, Nat.add_zero, Nat.zero_mod]
    rw [slots1_get _ _ (by have := h.pos; omega)]; rfl
  rows_nodup := by simp
  uniq j j' i hj hj' := by
    have g : ∀ x, (slots1 g.n)[x]? = some (i + 1) → x = 0 := by
      intro x hx
      by_cases hxn : x < g.n
      · rw [slots1_get _ _ hxn] at hx; split at hx <;> simp_all
      · rw [List.getElem?_eq_none (by simp [slots1]; omega)] at hx; cases hx
    rw [g j hj, g j' hj']

theorem tabAt_one {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α]
    (t : PanSemStateFiniteExact 64 σ) (L : Layout) (k tier : Nat) (enc : α → List (BitVec 64))
    (dW : δ → BitVec 64 × BitVec 64) (mkI : Nat → ι) (x : α) (hx : enc x = []) (dv : δ)
    (hd : DescV t (descAddr L k tier) (L.geo k tier) (L.base k tier)) (hcap : (L.geo k tier).cap < 2 ^ 30)
    (h : OneMem t (L.geo k tier) (dW dv)) :
    TabAt t L k tier enc dW ((Tbl.empty : Tbl α ι δ).push x dv (mkI 0)) mkI :=
  ⟨hd, hcap, [x], [dW dv], _, 0, ⟨vt_one t enc _ x hx _ h, inv_one enc _ x hx _ h,
    push_rel Tbl.empty [] mkI (tblRel_empty mkI) x dv (List.not_mem_nil), rfl⟩⟩

end ConPanqueque.Start
