import ConPanqueque.V.Two
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic

/-!
# Overwriting a row's derived word

A store at `D + 16 i` (row `i < rows.length`) keeps the table's representation, with the
derived pair's first word replaced: every other word of the table lies elsewhere by the layout.
-/

namespace ConPanqueque.V

section
variable {σ : Type} {α : Type}

theorem toNat_add_of_lt (x : BitVec 64) (k : Nat) (h : x.toNat + k < 2 ^ 64) :
    (x + BitVec.ofNat 64 k).toNat = x.toNat + k := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega), Nat.mod_eq_of_lt h]

theorem toNat_add8 (x : BitVec 64) (h : x.toNat + 8 < 2 ^ 64) : (x + 8).toNat = x.toNat + 8 :=
  toNat_add_of_lt x 8 h

theorem ne_of_toNat_ne {a b : BitVec 64} (h : a.toNat ≠ b.toNat) : a ≠ b := fun e => h (by rw [e])

theorem vt_setDer {t : PanSemStateFiniteExact 64 σ} {enc : α → List (BitVec 64)} {rows : List α}
    {ders : List (BitVec 64 × BitVec 64)} {slots : List Nat} {g : VGeo} {hu : Nat}
    (h : VT t enc rows ders slots g hu) (i : Nat) (hi : i < rows.length) (w : BitVec 64) :
    VT { t with memory := fun c => if c = g.D + BitVec.ofNat 64 (16 * i) then .word w else t.memory c } enc rows
      (ders.set i (w, (ders[i]'(by rw [h.dlen]; exact hi)).2)) slots g hu := by
  have lC := h.layC; have lS := h.layS; have lR := h.layR; have lD := h.layD; have lK := h.layK
  have hle := h.le; have hule := h.hu_le
  have hA : (g.D + BitVec.ofNat 64 (16 * i)).toNat = g.D.toNat + 16 * i := toNat_add_of_lt _ _ (by omega)
  have keep : ∀ c, c.toNat ≠ g.D.toNat + 16 * i →
      (if c = g.D + BitVec.ofNat 64 (16 * i) then HolWordLab.word w else t.memory c) = t.memory c :=
    fun c hc => by rw [ite_eq_right (ne_of_toNat_ne (by rw [hA]; exact hc))]
  refine ⟨fun j hj => ?_, fun k hk => ?_, h.short, ?_, ?_, hule, by simp [h.dlen], fun k hk => ?_, hle, h.room,
    h.hroom, lC, lS, lR, lD, lK⟩
  · obtain ⟨v, a, b, c, d⟩ := h.slot j hj
    refine ⟨v, a, b, c, ?_⟩
    dsimp only; rw [keep _ (by rw [toNat_add_of_lt _ _ (by omega)]; omega)]; exact d
  · obtain ⟨P, a1, a2, a3, a4, a5, a6, a7⟩ := h.row k hk
    have hR1 : (g.R + BitVec.ofNat 64 (16 * k)).toNat = g.R.toNat + 16 * k := toNat_add_of_lt _ _ (by omega)
    refine ⟨P, a1, a2, ?_, ?_, fun j hj => ?_, a6, a7⟩
    · dsimp only; rw [keep _ (by rw [hR1]; omega)]; exact a3
    · dsimp only; rw [keep _ (by rw [toNat_add8 _ (by rw [hR1]; omega), hR1]; omega)]; exact a4
    · obtain ⟨b1, b2⟩ := a5 j hj
      refine ⟨b1, ?_⟩
      have hPj : P.toNat + 8 * j < 2 ^ 64 := by omega
      dsimp only; rw [keep _ (by rw [toNat_add_of_lt _ _ hPj]; omega)]; exact b2
  · refine ⟨h.cnt.1, ?_⟩; dsimp only; rw [keep _ (by omega)]; exact h.cnt.2
  · refine ⟨h.top.1, ?_⟩; dsimp only; rw [keep _ (by rw [toNat_add8 _ (by omega)]; omega)]; exact h.top.2
  · have hk' : k < rows.length := by simpa using hk
    obtain ⟨d1, d2, d3, d4⟩ := h.der k hk'
    have hDk : (g.D + BitVec.ofNat 64 (16 * k)).toNat = g.D.toNat + 16 * k := toNat_add_of_lt _ _ (by omega)
    refine ⟨d1, d2, ?_, ?_⟩
    · by_cases e : k = i
      · subst e; simp
      · dsimp only; rw [keep _ (by rw [hDk]; omega)]; simp [List.getElem_set, Ne.symm e, d3]
    · dsimp only; rw [keep _ (by rw [toNat_add8 _ (by rw [hDk]; omega), hDk]; omega)]
      by_cases e : k = i
      · subst e; rw [List.getElem_set_self]; exact d4
      · rw [List.getElem_set_ne (Ne.symm e)]; exact d4

end

end ConPanqueque.V
