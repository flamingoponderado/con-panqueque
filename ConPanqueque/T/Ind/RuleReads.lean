import ConPanqueque.T.Ind.IotaRel
import ConPanqueque.T.EnvCopy

/-!
# One rule reads (`ruleReads`)

Its parts read off the recursor's type (`iotaPartsOfAt`) are the parts read through its constructor
(`iotaPartsAt`), up to `iotaPartsRel`. The constructor's level parameters are copied from its environment record
into the value heap, where `iotaPartsAt` reads them.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP

/-- A fresh value-heap block holding the environment block at `src`. -/
def envBlkCopyP (C : Ctx) (x src : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local lCn (.load .one (vv src)))
  (allocP C x (.shift .lsl (.op .add [vv lCn, .const 1]) (.const 3))
  (.seq (.store (vv x) (vv lCn))
  (.seq (.assign .local lSrc (.op .add [vv src, .const 8]))
  (.seq (.assign .local lDst (.op .add [vv x, .const 8]))
  (.seq (.assign .local lCi (.const 0))
  (.seq copyLoop rest))))))

section
variable {σ : Type}

theorem specR_envBlkCopyI {α : Type} {C : Ctx} (hok : CtxOK C) {H : List (BitVec 64)} {s : AState} {Γ : Env}
    {M : Mem} {D : List MlS} {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (x src : MlS) (os : Nat) (xs : List (BitVec 64))
    (hD : x ∈ D ∧ lCn ∈ D ∧ lSrc ∈ D ∧ lDst ∈ D ∧ lCi ∈ D ∧ lCz ∈ D)
    (hsrc : Γ.get src = some (ecell C os)) (hb : EBlk C.EH os xs) (hxl : xs.length < 2 ^ 58) (hz : Γ.get lCz = none)
    (hne : x ≠ lCn ∧ x ≠ lSrc ∧ x ≠ lDst ∧ x ≠ lCi ∧ x ≠ lCz) (hsn : src ≠ lCn ∧ src ≠ x)
    (hcont : ∀ (H' : List (BitVec 64)) o, H <+: H' → H.length ≤ o → BlkAt H' o xs →
      SpecR (Inv (ctxH C H') s ((lCi, BitVec.ofNat 64 xs.length) :: (lDst, cellA C (o + 1 + xs.length)) ::
        (lSrc, ecell C (os + 1 + xs.length)) :: (x, cellA C o) :: (lCn, BitVec.ofNat 64 xs.length) :: Γ) [] D)
        rest s m R) :
    SpecR (Inv (ctxH C H) s Γ M D) (envBlkCopyP C x src rest) s m R := by
  refine specR_envLoadI (C := ctxH C H) lCn (vv src) os (BitVec.ofNat 64 xs.length) hD.2.1
    (by simp only [sev, sev_vv]; exact hsrc) (by show C.EH[os]? = _; rw [hb.1]) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : H.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  let k := xs.length
  refine specR_allocI (C := ctxH C H) x _ (k + 1) (by omega) hD.1 (fun v => ?_)
    (fun H2 ws hp2 hws hroom => ?_)
  · simp +decide [sev, Env.get, hne.1.symm]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, k]; omega
  have hp2' : H <+: H2 := hp2
  have hH12 := hp2'.length_le
  have hq0 : H2.length < (ctxH (ctxH C H) (H2 ++ ws)).H.length := by show H2.length < (H2 ++ ws).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv x) (vv lCn) H2.length hq0 (BitVec.ofNat 64 k)
    (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, hne.1.symm]; rfl) ?_
  change SpecR (Inv (ctxH C ((H2 ++ ws).set H2.length (BitVec.ofNat 64 k))) _ _ _ _) _ _ _ _
  generalize hB : (H2 ++ ws).set H2.length (BitVec.ofNat 64 k) = B
  have hBlen : B.length = H2.length + (k + 1) := by rw [← hB]; simp [hws]
  refine specR_assignI lSrc _ (ecell C (os + 1)) hD.2.2.1
    (by simp +decide [sev, Env.get, hsn.1, hsn.2, hsrc]; exact ecell_add8 C os) ?_
  refine specR_assignI lDst _ (cellA C (H2.length + 1)) hD.2.2.2.1
    (by simp +decide [sev, Env.get, hne.2.1]; exact cellA_add8 C _) ?_
  refine specR_assignI lCi (.const 0) (BitVec.ofNat 64 0) hD.2.2.2.2.1 rfl ?_
  refine specR_copyEI (C := C) hok B xs (os + 1) (H2.length + 1)
    ⟨hD.2.2.1, hD.2.2.2.1, hD.2.2.2.2.1, hD.2.2.2.2.2⟩ (fun j hj => hb.2 j hj) (by omega) (by omega)
    (by simp +decide [Env.get, hne.1.symm]) (by decide)
    (by simp +decide [Env.get, hne.2.2.2.2.symm]; exact hz) ?_
  refine hcont _ H2.length ?_ hH12 ?_
  · refine hp2'.trans (prefix_of_get? (by rw [fillI_length, hBlen]; omega) (fun j hj => ?_))
    rw [fillI_get?, ite_eq_right (by omega), ← hB, List.getElem?_set_ne (by omega), List.getElem?_append_left hj]
  · exact WC.blk_of_fillI_hdr B xs H2.length (by rw [← hB, List.getElem?_set_self (by simp; omega)])
      (by rw [hBlen]; omega)

end

end ConPanqueque.T.Ind
