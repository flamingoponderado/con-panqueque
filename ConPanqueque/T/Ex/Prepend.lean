import ConPanqueque.T.Ex.AppArgs
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Prepending a word to a heap block

`n := len(y); w := alloc(n + 2); w[0] := n + 1; w[1] := x; copy y's words to w[2..]`: the block
`x :: xs` from the block `xs`, in a bigger image.
-/

namespace ConPanqueque.T.ExPre
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExG

theorem cellA_off (C : Ctx) (o k : Nat) : cellA C o + BitVec.ofNat 64 (8 * k) = cellA C (o + k) := by
  simp only [cellA, BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega

def prependP (C : Ctx) (x : MlS) : ProgHOL 64 :=
  .seq (.assign .local lCn (.load .one (vv lY)))
  (allocP C lW (.shift .lsl (.op .add [vv lCn, .const 2]) (.const 3))
  (.seq (.store (vv lW) (.op .add [vv lCn, .const 1]))
  (.seq (.store (.op .add [vv lW, .const 8]) (vv x))
  (.seq (.assign .local lSrc (.op .add [vv lY, .const 8]))
  (.seq (.assign .local lDst (.op .add [vv lW, .const 16]))
  (.seq (.assign .local lCi (.const 0))
  (.seq copyLoop (.return (vv lW)))))))))

section
variable {σ : Type}

theorem prepend_spec {α : Type} (C : Ctx) (hok : CtxOK C) {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem}
    {D : List MlS} {a : α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (xv : BitVec 64) (oy : Nat) (xs : List (BitVec 64))
    (hD : lCn ∈ D ∧ lW ∈ D ∧ lSrc ∈ D ∧ lDst ∈ D ∧ lCi ∈ D ∧ lCz ∈ D)
    (hy : Γ.get lY = some (cellA C oy)) (hx : Γ.get x = some xv) (hblk : BlkAt H oy xs)
    (hxn : x ≠ lCn ∧ x ≠ lW ∧ x ≠ lSrc ∧ x ≠ lDst ∧ x ≠ lCi) (hz : Γ.get lCz = none)
    (hz2 : lY ≠ lCn ∧ lY ≠ lW ∧ lY ≠ lSrc ∧ lY ≠ lDst ∧ lY ≠ lCi)
    (hR : ∀ H' o (t : PState σ), H <+: H' → BlkAt H' o (xv :: xs) → SR (ctxH C H') s t →
      R a (cellA C o) s t) :
    SpecR (Inv (σ := σ) (ctxH C H) s Γ M D) (prependP C x) s (pure a) R := by
  have hlen := blkAt_len hblk
  obtain ⟨hol, hv0⟩ := blkAt_get0 hblk
  refine specR_heapLoadI (C := ctxH C H) lCn (vv lY) oy hol hD.1 (by simp [hy, cellA, ctxH]) ?_
  rw [show (ctxH C H).H[oy]'hol = BitVec.ofNat 64 xs.length from hv0]
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hlay := hok.heapLay
  have hHN' : H.length ≤ C.HN := hHN
  refine specR_allocI (C := ctxH C H) lW _ (xs.length + 2) (by omega) hD.2.1 (fun v => ?_)
    (fun H2 ws hp2 hws hroom => ?_)
  · simp +decide [sev]
    rw [shl_ofNat _ _ (by omega), show (16#64) = BitVec.ofNat 64 16 from rfl, BitVec.ofNat_add_ofNat]
    congr 1 <;> omega
  have hp2' : H <+: H2 := hp2
  have hH12 := hp2'.length_le
  have hroom' : H2.length + (xs.length + 2) ≤ C.HN := hroom
  have hq0 : H2.length < (ctxH C (H2 ++ ws)).H.length := by show H2.length < (H2 ++ ws).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok (H2 ++ ws)) (vv lW) (.op .add [vv lCn, .const 1]) H2.length hq0
    (BitVec.ofNat 64 (xs.length + 1)) (by simp +decide [cellA, ctxH]) (by simp +decide [sev]; exact word_add1_eq _) ?_
  generalize hB1 : (ctxH C (H2 ++ ws)).H.set H2.length (BitVec.ofNat 64 (xs.length + 1)) = B1
  have hB1len : B1.length = H2.length + (xs.length + 2) := by
    rw [← hB1]; show ((H2 ++ ws).set _ _).length = _; simp [hws]
  have hq1 : H2.length + 1 < (ctxH C B1).H.length := by show _ < B1.length; omega
  refine specR_heapStoreI (ctxOK_H hok B1) (.op .add [vv lW, .const 8]) (vv x) (H2.length + 1) hq1 xv
    (by simp +decide [sev]; exact cellA_add8 C _) (by simp +decide [hx, hxn.1, hxn.2.1]) ?_
  generalize hB : (ctxH C B1).H.set (H2.length + 1) xv = B
  have hBlen : B.length = H2.length + (xs.length + 2) := by rw [← hB]; show (B1.set _ _).length = _; simp [hB1len]
  refine specR_assignI lSrc _ (cellA C (oy + 1)) hD.2.2.1 (by simp +decide [sev, hz2.1, hz2.2.1, hy]; exact cellA_add8 C oy) ?_
  refine specR_assignI lDst _ (cellA C (H2.length + 2)) hD.2.2.2.1
    (by simp +decide [sev]; rw [show (16#64) = BitVec.ofNat 64 (8 * 2) from rfl]; exact cellA_off C _ 2) ?_
  refine specR_assignI lCi (.const 0) (BitVec.ofNat 64 0) hD.2.2.2.2.1 rfl ?_
  have hsrc : ∀ j (hj : j < xs.length), B[oy + 1 + j]? = some xs[j] := by
    intro j hj
    rw [← hB]; show (B1.set _ _)[oy + 1 + j]? = _
    rw [List.getElem?_set_ne (by omega), ← hB1]; show ((H2 ++ ws).set _ _)[oy + 1 + j]? = _
    rw [List.getElem?_set_ne (by omega), List.getElem?_append_left (by omega)]
    exact (blkAt_mono hblk hp2').2 j hj
  refine specR_copyI (C := C) hok B xs (oy + 1) (H2.length + 2) ⟨hD.2.2.1, hD.2.2.2.1, hD.2.2.2.2.1, hD.2.2.2.2.2⟩
    hsrc (by omega) (by omega) (by omega) (by simp +decide [hz2.1]) (by decide) (by simp +decide [hz]) ?_
  generalize hF : fillI B xs (H2.length + 2) xs.length = F
  have hFlen : F.length = B.length := by rw [← hF, fillI_length]
  refine specR_returnI (vv lW) (cellA C H2.length) (by simp +decide <;> rfl) (fun t ht => ?_)
  have hFg : ∀ k, F[k]? = if H2.length + 2 ≤ k ∧ k < H2.length + 2 + xs.length ∧ k < B.length
      then some (xs.getD (k - (H2.length + 2)) 0) else B[k]? := by
    intro k; rw [← hF, fillI_get?]
  refine hR F H2.length _ ?_ ?_ (sr_of_eq ht.sr rfl rfl rfl rfl)
  · refine hp2'.trans (prefix_of_get? (by omega) (fun k hk => ?_))
    rw [hFg k, ite_eq_right (by omega), ← hB]
    show (B1.set _ _)[k]? = _
    rw [List.getElem?_set_ne (by omega), ← hB1]
    show ((H2 ++ ws).set _ _)[k]? = _
    rw [List.getElem?_set_ne (by omega), List.getElem?_append_left hk]
  · refine ⟨?_, fun i hi => ?_⟩
    · rw [hFg, ite_eq_right (by omega), ← hB]
      show (B1.set _ _)[H2.length]? = _
      rw [List.getElem?_set_ne (by omega), ← hB1]
      show ((H2 ++ ws).set _ _)[H2.length]? = _
      rw [List.getElem?_set_self (by simp; omega)]; simp
    · simp only [List.length_cons] at hi
      cases i with
      | zero =>
        rw [hFg, ite_eq_right (by omega), ← hB]
        show (B1.set _ _)[H2.length + 1 + 0]? = _
        rw [List.getElem?_set_self (by omega)]; simp
      | succ i =>
        rw [show H2.length + 1 + (i + 1) = H2.length + 2 + i by omega, hFg, ite_eq_left ⟨by omega, by omega, by omega⟩]
        simp [List.getD_eq_getElem?_getD, show i < xs.length by omega]

end

end ConPanqueque.T.ExPre
