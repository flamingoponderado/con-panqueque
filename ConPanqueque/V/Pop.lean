import ConPanqueque.V.Intern

/-!
# Undoing the newest insert of a table

The memory differs only at the count cell (back to the old row count) and at the newest row's slot (back to
empty); the key heap's top is kept.  The rows before the newest one still form a table.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open ConPanqueque.ConsModel

namespace ConPanqueque.V

section
variable {σ : Type} {α : Type}

theorem tn_lt (X : BitVec 64) (k : Nat) (h : X.toNat + k < 2 ^ 64) : (X + BitVec.ofNat 64 k).toNat = X.toNat + k := by
  simp [BitVec.toNat_add]; omega

/-- **The table of the rows before the newest**, after its slot is cleared and the count lowered. -/
theorem vt_pop {t t' : PanSemStateFiniteExact 64 σ} {enc : α → List (BitVec 64)} {rows : List α} {a : α}
    {ders : List (BitVec 64 × BitVec 64)} {slots : List Nat} {g : VGeo} {hu : Nat}
    (h : VT t enc (rows ++ [a]) ders slots g hu) (j : Nat) (hj : j < g.n)
    (hd : t'.memaddrs = t.memaddrs)
    (hC : t'.memory g.C = .word (BitVec.ofNat 64 rows.length))
    (hS : t'.memory (g.S + BitVec.ofNat 64 (8 * j)) = .word 0)
    (hrest : ∀ c, c ≠ g.C → c ≠ g.S + BitVec.ofNat 64 (8 * j) → t'.memory c = t.memory c) :
    VT t' enc rows ders.dropLast (slots.set j 0) g hu := by
  have lC := h.layC; have lS := h.layS; have lR := h.layR; have lD := h.layD; have lK := h.layK
  have hlen : (rows ++ [a]).length = rows.length + 1 := by simp
  have hcap := h.le
  have hule := h.hu_le
  have hC8 : (g.C + 8).toNat = g.C.toNat + 8 := by simp [BitVec.toNat_add]; omega
  rw [hlen] at hcap
  -- addresses in the slot array, rows, ders and key heap avoid the two written cells
  have neC : ∀ c : BitVec 64, g.C.toNat + 16 ≤ c.toNat → c ≠ g.C := fun c hc e => by subst e; omega
  have hSj : (g.S + BitVec.ofNat 64 (8 * j)).toNat = g.S.toNat + 8 * j := tn_lt _ _ (by omega)
  have neS : ∀ c : BitVec 64, c.toNat ≠ g.S.toNat + 8 * j → c ≠ g.S + BitVec.ofNat 64 (8 * j) :=
    fun c hc e => by subst e; exact hc hSj
  refine ⟨fun j' hj' => ?_, fun i hi => ?_, fun i hi => ?_, ⟨by rw [hd]; exact h.cnt.1, hC⟩,
    ⟨by rw [hd]; exact h.top.1, by
      rw [hrest _ (fun e => by have := congrArg BitVec.toNat e; rw [hC8] at this; omega)
        (neS _ (by rw [hC8]; omega))]; exact h.top.2⟩,
    h.hu_le, by simp [h.dlen], fun i hi => ?_, by omega, fun i hi => by rw [hd]; exact h.room i hi,
    fun k hk => by rw [hd]; exact h.hroom k hk, lC, lS, lR, lD, lK⟩
  · obtain ⟨v, hv, hvlt, hma, hmv⟩ := h.slot j' hj'
    by_cases e : j' = j
    · subst e
      refine ⟨0, by rw [List.getElem?_set]; simp [(List.getElem?_eq_some_iff.mp hv).1], by omega, by rw [hd]; exact hma, hS⟩
    · have hSj' : (g.S + BitVec.ofNat 64 (8 * j')).toNat = g.S.toNat + 8 * j' := tn_lt _ _ (by omega)
      refine ⟨v, by rw [List.getElem?_set]; simp [Ne.symm e, hv], hvlt, by rw [hd]; exact hma, ?_⟩
      rw [hrest _ (neC _ (by rw [hSj']; omega)) (neS _ (by rw [hSj']; omega))]; exact hmv
  · have hi' : i < (rows ++ [a]).length := by simp; omega
    obtain ⟨P, a1, a2, a3, a4, a5, a6, a7⟩ := h.row i hi'
    have hri : (rows ++ [a])[i] = rows[i] := List.getElem_append_left hi
    rw [hri] at a4 a5 a7
    have hR1 : (g.R + BitVec.ofNat 64 (16 * i)).toNat = g.R.toNat + 16 * i := tn_lt _ _ (by omega)
    have hR2 : (g.R + BitVec.ofNat 64 (16 * i) + 8).toNat = g.R.toNat + 16 * i + 8 := by
      rw [show g.R + BitVec.ofNat 64 (16 * i) + 8 = g.R + BitVec.ofNat 64 (16 * i + 8) by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp]
      exact tn_lt _ _ (by omega)
    have hsh := h.short i hi'
    rw [hri] at hsh
    refine ⟨P, by rw [hd]; exact a1, by rw [hd]; exact a2, ?_, ?_, fun k hk => ?_, a6, a7⟩
    · rw [hrest _ (neC _ (by rw [hR1]; omega)) (neS _ (by rw [hR1]; omega))]; exact a3
    · rw [hrest _ (neC _ (by rw [hR2]; omega)) (neS _ (by rw [hR2]; omega))]; exact a4
    · obtain ⟨w1, w2⟩ := a5 k hk
      have hPk : (P + BitVec.ofNat 64 (8 * k)).toNat = P.toNat + 8 * k := tn_lt _ _ (by omega)
      refine ⟨by rw [hd]; exact w1, ?_⟩
      rw [hrest _ (neC _ (by rw [hPk]; omega)) (neS _ (by rw [hPk]; omega))]; exact w2
  · have := h.short i (by rw [hlen]; omega)
    rwa [List.getElem_append_left hi] at this
  · have hi' : i < (rows ++ [a]).length := by rw [hlen]; omega
    obtain ⟨d1, d2, d3, d4⟩ := h.der i hi'
    have hdl := h.dlen
    rw [hlen] at hdl
    have hD1 : (g.D + BitVec.ofNat 64 (16 * i)).toNat = g.D.toNat + 16 * i := tn_lt _ _ (by omega)
    have hD2 : (g.D + BitVec.ofNat 64 (16 * i) + 8).toNat = g.D.toNat + 16 * i + 8 := by
      rw [show g.D + BitVec.ofNat 64 (16 * i) + 8 = g.D + BitVec.ofNat 64 (16 * i + 8) by
        rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp]
      exact tn_lt _ _ (by omega)
    have hdi : (ders.dropLast[i]'(by simp; omega)) = ders[i]'(by omega) := List.getElem_dropLast ..
    refine ⟨by rw [hd]; exact d1, by rw [hd]; exact d2, ?_, ?_⟩
    · rw [hrest _ (neC _ (by rw [hD1]; omega)) (neS _ (by rw [hD1]; omega)), hdi]; exact d3
    · rw [hrest _ (neC _ (by rw [hD2]; omega)) (neS _ (by rw [hD2]; omega)), hdi]; exact d4

end

end ConPanqueque.V
