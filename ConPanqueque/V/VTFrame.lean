import ConPanqueque.V.Ins

/-!
# A memo table's representation depends only on its live cells

`VT` reads the slot array, the rows and derived words below the row count, the key heap below its top, and the
count and top words. A state agreeing with another on those cells (and on the address set) represents the same
table: the base of undoing fresh inserts.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString

namespace ConPanqueque.V

section
variable {σ : Type} {α : Type}

theorem vt_frameLive {t u : PanSemStateFiniteExact 64 σ} {enc : α → List (BitVec 64)} {rows : List α}
    {ders : List (BitVec 64 × BitVec 64)} {slots : List Nat} {g : VGeo} {hu : Nat}
    (h : VT t enc rows ders slots g hu) (hd : u.memaddrs = t.memaddrs)
    (hS : ∀ j, j < g.n → u.memory (g.S + BitVec.ofNat 64 (8 * j)) = t.memory (g.S + BitVec.ofNat 64 (8 * j)))
    (hR : ∀ i, i < rows.length → u.memory (g.R + BitVec.ofNat 64 (16 * i)) = t.memory (g.R + BitVec.ofNat 64 (16 * i)) ∧
      u.memory (g.R + BitVec.ofNat 64 (16 * i) + 8) = t.memory (g.R + BitVec.ofNat 64 (16 * i) + 8))
    (hD : ∀ i, i < rows.length → u.memory (g.D + BitVec.ofNat 64 (16 * i)) = t.memory (g.D + BitVec.ofNat 64 (16 * i)) ∧
      u.memory (g.D + BitVec.ofNat 64 (16 * i) + 8) = t.memory (g.D + BitVec.ofNat 64 (16 * i) + 8))
    (hK : ∀ c : BitVec 64, g.KH.toNat ≤ c.toNat → c.toNat < g.KH.toNat + 8 * hu → u.memory c = t.memory c)
    (hC : u.memory g.C = t.memory g.C) (hT : u.memory (g.C + 8) = t.memory (g.C + 8)) :
    VT u enc rows ders slots g hu where
  slot j hj := by
    obtain ⟨v, h1, h2, h3, h4⟩ := h.slot j hj
    exact ⟨v, h1, h2, by rw [hd]; exact h3, by rw [hS j hj]; exact h4⟩
  row i hi := by
    obtain ⟨P, a1, a2, a3, a4, a5, a6, a7⟩ := h.row i hi
    refine ⟨P, by rw [hd]; exact a1, by rw [hd]; exact a2, by rw [(hR i hi).1]; exact a3,
      by rw [(hR i hi).2]; exact a4, fun k hk => ?_, a6, a7⟩
    obtain ⟨b1, b2⟩ := a5 k hk
    refine ⟨by rw [hd]; exact b1, ?_⟩
    have hlt := h.layK
    have hle := h.hu_le
    rw [hK _ (by simp [BitVec.toNat_add]; omega) (by simp [BitVec.toNat_add]; omega)]
    exact b2
  short := h.short
  cnt := ⟨by rw [hd]; exact h.cnt.1, by rw [hC]; exact h.cnt.2⟩
  top := ⟨by rw [hd]; exact h.top.1, by rw [hT]; exact h.top.2⟩
  hu_le := h.hu_le
  dlen := h.dlen
  der i hi := by
    obtain ⟨a1, a2, a3, a4⟩ := h.der i hi
    exact ⟨by rw [hd]; exact a1, by rw [hd]; exact a2, by rw [(hD i hi).1]; exact a3, by rw [(hD i hi).2]; exact a4⟩
  le := h.le
  room i hi := by rw [hd]; exact h.room i hi
  hroom k hk := by rw [hd]; exact h.hroom k hk
  layC := h.layC
  layS := h.layS
  layR := h.layR
  layD := h.layD
  layK := h.layK

end

end ConPanqueque.V
