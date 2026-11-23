import ConPanqueque.T.Ex.Prepend
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Appending a word to a heap block

`n := len(y); w := alloc(n + 2); w[0] := n + 1; copy y's words to w[1..]; w[n + 1] := x`: the block `xs ++ [x]`
from the block `xs`, in a bigger image.
-/

namespace ConPanqueque.T.ExPre
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExG

def appendP (C : Ctx) (x : MlS) : ProgHOL 64 :=
  .seq (.assign .local lCn (.load .one (vv lY)))
  (allocP C lW (.shift .lsl (.op .add [vv lCn, .const 2]) (.const 3))
  (.seq (.store (vv lW) (.op .add [vv lCn, .const 1]))
  (.seq (.assign .local lSrc (.op .add [vv lY, .const 8]))
  (.seq (.assign .local lDst (.op .add [vv lW, .const 8]))
  (.seq (.assign .local lCi (.const 0))
  (.seq copyLoop (.seq (.store (vv lDst) (vv x)) (.return (vv lW)))))))))

section
variable {σ : Type}

theorem append_spec {α : Type} (C : Ctx) (hok : CtxOK C) {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem}
    {D : List MlS} {a : α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (xv : BitVec 64) (oy : Nat) (xs : List (BitVec 64))
    (hD : lCn ∈ D ∧ lW ∈ D ∧ lSrc ∈ D ∧ lDst ∈ D ∧ lCi ∈ D ∧ lCz ∈ D)
    (hy : Γ.get lY = some (cellA C oy)) (hx : Γ.get x = some xv) (hblk : BlkAt H oy xs)
    (hxn : x ≠ lCn ∧ x ≠ lW ∧ x ≠ lSrc ∧ x ≠ lDst ∧ x ≠ lCi) (hz : Γ.get lCz = none)
    (hz2 : lY ≠ lCn ∧ lY ≠ lW ∧ lY ≠ lSrc ∧ lY ≠ lDst ∧ lY ≠ lCi)
    (hR : ∀ H' o (t : PState σ), H <+: H' → BlkAt H' o (xs ++ [xv]) → SR (ctxH C H') s t →
      R a (cellA C o) s t) :
    SpecR (Inv (σ := σ) (ctxH C H) s Γ M D) (appendP C x) s (pure a) R := by
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
  generalize hB : (ctxH C (H2 ++ ws)).H.set H2.length (BitVec.ofNat 64 (xs.length + 1)) = B
  have hBlen : B.length = H2.length + (xs.length + 2) := by
    rw [← hB]; show ((H2 ++ ws).set _ _).length = _; simp [hws]
  refine specR_assignI lSrc _ (cellA C (oy + 1)) hD.2.2.1 (by simp +decide [sev, hz2.1, hz2.2.1, hy]; exact cellA_add8 C oy) ?_
  refine specR_assignI lDst _ (cellA C (H2.length + 1)) hD.2.2.2.1
    (by simp +decide [sev]; exact cellA_add8 C _) ?_
  refine specR_assignI lCi (.const 0) (BitVec.ofNat 64 0) hD.2.2.2.2.1 rfl ?_
  have hsrc : ∀ j (hj : j < xs.length), B[oy + 1 + j]? = some xs[j] := by
    intro j hj
    rw [← hB]; show ((H2 ++ ws).set _ _)[oy + 1 + j]? = _
    rw [List.getElem?_set_ne (by omega), List.getElem?_append_left (by omega)]
    exact (blkAt_mono hblk hp2').2 j hj
  refine specR_copyI (C := C) hok B xs (oy + 1) (H2.length + 1) ⟨hD.2.2.1, hD.2.2.2.1, hD.2.2.2.2.1, hD.2.2.2.2.2⟩
    hsrc (by omega) (by omega) (by omega) (by simp +decide [hz2.1]) (by decide) (by simp +decide [hz]) ?_
  generalize hF : fillI B xs (H2.length + 1) xs.length = F
  have hFlen : F.length = B.length := by rw [← hF, fillI_length]
  have hq2 : H2.length + 1 + xs.length < (ctxH C F).H.length := by show _ < F.length; omega
  refine specR_heapStoreI (ctxOK_H hok F) (vv lDst) (vv x) (H2.length + 1 + xs.length) hq2 xv (by simp +decide; rfl)
    (by simp +decide [hx, hxn.1, hxn.2.1, hxn.2.2.1, hxn.2.2.2.1, hxn.2.2.2.2]) ?_
  generalize hG : (ctxH C F).H.set (H2.length + 1 + xs.length) xv = G
  refine specR_returnI (vv lW) (cellA C H2.length) (by simp +decide <;> rfl) (fun t ht => ?_)
  have hFg : ∀ k, F[k]? = if H2.length + 1 ≤ k ∧ k < H2.length + 1 + xs.length ∧ k < B.length
      then some (xs.getD (k - (H2.length + 1)) 0) else B[k]? := by
    intro k; rw [← hF, fillI_get?]
  have hGg : ∀ k, k ≠ H2.length + 1 + xs.length → G[k]? = F[k]? := by
    intro k hk; rw [← hG]; exact List.getElem?_set_ne (Ne.symm hk)
  refine hR G H2.length _ ?_ ?_ (sr_of_eq ht.sr rfl rfl rfl rfl)
  · refine hp2'.trans (prefix_of_get? (by rw [← hG]; show _ ≤ (F.set _ _).length; simp; omega) (fun k hk => ?_))
    rw [hGg k (by omega), hFg k, if_neg (by omega), ← hB]
    show ((H2 ++ ws).set _ _)[k]? = _
    rw [List.getElem?_set_ne (by omega), List.getElem?_append_left hk]
  · refine ⟨?_, fun i hi => ?_⟩
    · rw [hGg _ (by omega), hFg, if_neg (by omega), ← hB]
      show ((H2 ++ ws).set _ _)[H2.length]? = _
      rw [List.getElem?_set_self (by simp; omega)]; simp
    · simp only [List.length_append, List.length_cons, List.length_nil] at hi
      by_cases hil : i < xs.length
      · rw [hGg _ (by omega), hFg, if_pos ⟨by omega, by omega, by omega⟩]
        simp [List.getD_eq_getElem?_getD, show H2.length + 1 + i - (H2.length + 1) = i by omega, hil,
          List.getElem_append_left hil]
      · have : i = xs.length := by omega
        subst this
        rw [← hG]; show (F.set _ _)[_]? = _
        rw [List.getElem?_set_self (by omega)]; simp

end

end ConPanqueque.T.ExPre
