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

def ryT := ofString "ry_t"
def ryC := ofString "ry_c"
def ryN := ofString "ry_n"
def ryH := ofString "ry_h"
def ryW1 := ofString "ry_w1"
def ryW2 := ofString "ry_w2"
def ryB1 := ofString "ry_b1"
def ryB2 := ofString "ry_b2"

/-- The rule record at environment pointer `q` rebuilt in the value heap, its address into `x`. -/
def ruleCopyP (C : Ctx) (x q : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local ryT (.load .one (.op .add [vv q, .const 16])))
  (.seq (.assign .local ryC (.load .one (vv q)))
  (.seq (.assign .local ryN (.load .one (.op .add [vv q, .const 8])))
  (.seq (.assign .local ryH (.load .one (.op .add [vv q, .const 40])))
  (.ite (veEqC ryT 0)
    (alloc6 C x (vv ryC) (vv ryN) (.const 0) (.const 0) (.const 0) (vv ryH) rest)
    (.seq (.assign .local ryW1 (.load .one (.op .add [vv q, .const 24])))
    (envBlkCopyP C ryB1 ryW1
    (.ite (veEqC ryT 1)
      (.seq (.assign .local ryW2 (.load .one (.op .add [vv q, .const 32])))
      (envBlkCopyP C ryB2 ryW2
        (alloc6 C x (vv ryC) (vv ryN) (.const 1) (vv ryB1) (vv ryB2) (vv ryH) rest)))
      (alloc6 C x (vv ryC) (vv ryN) (.const 2) (vv ryB1) (.const 0) (vv ryH) rest))))))))

section
variable {σ : Type}

theorem specR_envBlkCopyI {α : Type} {C : Ctx} (hok : CtxOK C) {H : List (BitVec 64)} {s : AState} {Γ : Env}
    {M : Mem} {D : List MlS} {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (x src : MlS) (os : Nat) (xs : List (BitVec 64))
    (hD : x ∈ D ∧ lCn ∈ D ∧ lSrc ∈ D ∧ lDst ∈ D ∧ lCi ∈ D ∧ lCz ∈ D)
    (hsrc : Γ.get src = some (ecell C os)) (hb : EBlk C.EH os xs) (hz : Γ.get lCz = none)
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
  refine specR_fact (fun t ht => ht.sr.env.1.len) (fun hEN => ?_)
  have hEN' : C.EH.length ≤ C.EN := hEN
  have hle := hok.envLay
  have hbl : os + 1 + xs.length ≤ C.EH.length := blkAt_len hb
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

def rySc : List MlS := [ryT, ryC, ryN, ryH, ryW1, ryW2, ryB1, ryB2, lCn, lSrc, lDst, lCi]

theorem specR_ruleCopyI {α : Type} {C : Ctx} (hok : CtxOK C) {H : List (BitVec 64)} {s : AState} {Γ : Env}
    {M : Mem} {D : List MlS} {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (x q : MlS) (oq : Nat) (rl : IRecRule) (hD : ∀ z, z ∈ x :: lCz :: rySc → z ∈ D)
    (hq : Γ.get q = some (ecell C oq)) (hr : RuleE C.EB C.EH oq rl) (hz : Γ.get lCz = none)
    (hx : x ∉ lCz :: rySc) (hqs : q ∉ x :: lCz :: rySc)
    (hcont : ∀ (H' : List (BitVec 64)) (Γ' : Env) (q' : Nat), H <+: H' → RuleE C.HB H' q' rl →
      Γ'.get x = some (cellA C q') → (∀ z, z ∉ x :: rySc → Γ'.get z = Γ.get z) →
      SpecR (Inv (ctxH C H') s Γ' [] D) rest s m R) :
    SpecR (Inv (ctxH C H) s Γ M D) (ruleCopyP C x q rest) s m R := by
  have hDx := hD x (by simp)
  have hqv : ∀ (Γ' : Env), (∀ z, z ∉ x :: rySc → Γ'.get z = Γ.get z) → Γ'.get q = some (ecell C oq) := by
    intro Γ' h
    rw [h q (fun hm => hqs (List.mem_cons.mpr (by
      rcases List.mem_cons.mp hm with e | e
      · exact Or.inl e
      · exact Or.inr (List.mem_cons_of_mem _ e))))]
    exact hq
  have hq' := hqs
  simp only [rySc, List.mem_cons, List.not_mem_nil, or_false, not_or] at hq'
  obtain ⟨qx, qz, qT, qC, qN, qH, qW1, qW2, qB1, qB2, qCn, qSrc, qDst, qCi⟩ := hq'
  have hx' := hx
  simp only [rySc, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx'
  obtain ⟨xz, xT, xC, xN, xH, xW1, xW2, xB1, xB2, xCn, xSrc, xDst, xCi⟩ := hx'
  obtain ⟨hc0, ⟨hn0, hnb⟩, hfire, hh0⟩ := hr
  have addr : ∀ k, ecell C oq + BitVec.ofNat 64 (8 * k) = ecell C (oq + k) := fun k => ecell_add C oq k
  have ldq : ∀ (Γ' : Env) (k : Nat), Γ'.get q = some (ecell C oq) →
      sev Γ' (.op .add [vv q, .const (BitVec.ofNat 64 (8 * k))]) = some (ecell (ctxH C H) (oq + k)) := by
    intro Γ' k h; simp only [sev, sev_vv, h]; simp; exact addr k
  have hlay := hok.heapLay
  unfold ruleCopyP
  rcases hfr : rl.fire with _ | ⟨lv, pins⟩ | lv <;> rw [hfr] at hfire
  · -- plain
    refine specR_envLoadI (C := ctxH C H) ryT _ (oq + 2) (BitVec.ofNat 64 0) (hD _ (by simp [rySc]))
      (ldq Γ 2 hq) hfire ?_
    refine specR_envLoadI (C := ctxH C H) ryC (vv q) oq (Enc.idxW rl.ctor) (hD _ (by simp [rySc]))
      (by simp only [sev, sev_vv, Env.get_cons, qT, ite_false]; exact hq) hc0 ?_
    refine specR_envLoadI (C := ctxH C H) ryN _ (oq + 1) (BitVec.ofNat 64 rl.nfields) (hD _ (by simp [rySc]))
      (ldq _ 1 (by simp only [Env.get_cons, qT, qC, ite_false]; exact hq)) hn0 ?_
    refine specR_envLoadI (C := ctxH C H) ryH _ (oq + 5) (Enc.idxW rl.rhs) (hD _ (by simp [rySc]))
      (ldq _ 5 (by simp only [Env.get_cons, qT, qC, qN, ite_false]; exact hq)) hh0 ?_
    refine specR_ifI _ 1 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_alloc6I (ctxOK_H hok H) x (vv ryC) (vv ryN) (.const 0) (.const 0) (.const 0) (vv ryH)
      (Enc.idxW rl.ctor) (BitVec.ofNat 64 rl.nfields) 0 0 0 (Enc.idxW rl.rhs) hDx
      (fun _ => by simp +decide [sev, Env.get_cons, Ne.symm xC]) (fun _ => by simp +decide [sev, Env.get_cons, Ne.symm xN])
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => by simp +decide [sev, Env.get_cons, Ne.symm xH])
      (fun H2 ws hp2 hws hroom => ?_)
    obtain ⟨g0, g1, g2, -, -, g5⟩ := img6_get H2 ws (Enc.idxW rl.ctor) (BitVec.ofNat 64 rl.nfields) 0 0 0
      (Enc.idxW rl.rhs) hws
    refine hcont _ _ H2.length (hp2.trans (img6_prefix _ _ _ _ _ _ _ _ hws))
      ⟨g0, ⟨g1, hnb⟩, by rw [hfr]; exact g2, by rw [show H2.length + 5 = H2.length + 5 from rfl]; exact g5⟩
      (by simp [Env.get_cons]; rfl) (fun z hz => ?_)
    simp only [rySc, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    obtain ⟨zx, zT, zC, zN, zH, -, -, -, -, -, -, -, -⟩ := hz
    simp [Env.get_cons, zx, zT, zC, zN, zH]
  · -- nested
    refine specR_envLoadI (C := ctxH C H) ryT _ (oq + 2) (BitVec.ofNat 64 1) (hD _ (by simp [rySc]))
      (ldq Γ 2 hq) hfire.1 ?_
    refine specR_envLoadI (C := ctxH C H) ryC (vv q) oq (Enc.idxW rl.ctor) (hD _ (by simp [rySc]))
      (by simp only [sev, sev_vv, Env.get_cons, qT, ite_false]; exact hq) hc0 ?_
    refine specR_envLoadI (C := ctxH C H) ryN _ (oq + 1) (BitVec.ofNat 64 rl.nfields) (hD _ (by simp [rySc]))
      (ldq _ 1 (by simp only [Env.get_cons, qT, qC, ite_false]; exact hq)) hn0 ?_
    refine specR_envLoadI (C := ctxH C H) ryH _ (oq + 5) (Enc.idxW rl.rhs) (hD _ (by simp [rySc]))
      (ldq _ 5 (by simp only [Env.get_cons, qT, qC, qN, ite_false]; exact hq)) hh0 ?_
    refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    obtain ⟨w1, hw1, o1, rfl, hb1⟩ := hfire.2.1
    refine specR_envLoadI (C := ctxH C H) ryW1 _ (oq + 3) (C.EB + BitVec.ofNat 64 (8 * o1)) (hD _ (by simp [rySc]))
      (ldq _ 3 (by simp only [Env.get_cons, qT, qC, qN, qH, ite_false]; exact hq))
      (by rw [show oq + 3 = oq + 2 + 1 by omega]; exact hw1) ?_
    refine specR_envBlkCopyI hok ryB1 ryW1 o1 (lv.map Enc.idxW)
      ⟨hD _ (by simp [rySc]), hD _ (by simp [rySc]), hD _ (by simp [rySc]), hD _ (by simp [rySc]), hD _ (by simp [rySc]),
        hD _ (by simp)⟩
      (by simp [Env.get_cons]; rfl) hb1 (by simp +decide [Env.get_cons]; exact hz) (by decide) (by decide)
      (fun H3 o3 hp3 hl3 hb3 => ?_)
    have hp3' : H <+: H3 := hp3
    refine specR_ifI _ 1 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨w2, hw2, o2, rfl, hb2⟩ := hfire.2.2
    refine specR_envLoadI (C := ctxH C H3) ryW2 _ (oq + 4) (C.EB + BitVec.ofNat 64 (8 * o2)) (hD _ (by simp [rySc]))
      (ldq _ 4 (by simp only [Env.get_cons, qT, qC, qN, qH, qW1, qB1, qCn, qSrc, qDst, qCi, ite_false]; exact hq))
      (by rw [show oq + 4 = oq + 2 + 2 by omega]; exact hw2) ?_
    refine specR_envBlkCopyI hok ryB2 ryW2 o2 (pins.map Enc.idxW)
      ⟨hD _ (by simp [rySc]), hD _ (by simp [rySc]), hD _ (by simp [rySc]), hD _ (by simp [rySc]), hD _ (by simp [rySc]),
        hD _ (by simp)⟩
      (by simp [Env.get_cons]; rfl) hb2 (by simp +decide [Env.get_cons]; exact hz) (by decide) (by decide)
      (fun H4 o4 hp4 hl4 hb4 => ?_)
    have hp4' : H3 <+: H4 := hp4
    refine specR_alloc6I (ctxOK_H hok H4) x (vv ryC) (vv ryN) (.const 1) (vv ryB1) (vv ryB2) (vv ryH)
      (Enc.idxW rl.ctor) (BitVec.ofNat 64 rl.nfields) 1 (cellA C o3) (cellA C o4) (Enc.idxW rl.rhs) hDx
      (fun _ => by simp +decide [sev, Env.get_cons, Ne.symm xC]) (fun _ => by simp +decide [sev, Env.get_cons, Ne.symm xN])
      (fun _ => rfl) (fun _ => by simp +decide [sev, Env.get_cons, Ne.symm xB1])
      (fun _ => by simp +decide [sev, Env.get_cons, Ne.symm xB2]) (fun _ => by simp +decide [sev, Env.get_cons, Ne.symm xH])
      (fun H5 ws hp5 hws hroom => ?_)
    obtain ⟨g0, g1, g2, g3, g4, g5⟩ := img6_get H5 ws (Enc.idxW rl.ctor) (BitVec.ofNat 64 rl.nfields) 1 (cellA C o3)
      (cellA C o4) (Enc.idxW rl.rhs) hws
    have hpi := img6_prefix H5 ws (Enc.idxW rl.ctor) (BitVec.ofNat 64 rl.nfields) 1 (cellA C o3) (cellA C o4)
      (Enc.idxW rl.rhs) hws
    have hp45 : H4 <+: H5 := hp5
    refine hcont _ _ H5.length (((hp3'.trans hp4').trans hp45).trans hpi)
      ⟨g0, ⟨g1, hnb⟩, by
        rw [hfr]
        exact ⟨g2, ⟨cellA C o3, g3, o3, rfl, blkAt_mono hb3 ((hp4'.trans hp45).trans hpi)⟩,
          ⟨cellA C o4, by rw [show H5.length + 2 + 2 = H5.length + 4 by omega]; exact g4, o4, rfl,
            blkAt_mono hb4 (hp45.trans hpi)⟩⟩, g5⟩
      (by simp [Env.get_cons]; rfl) (fun z hz => ?_)
    simp only [rySc, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    obtain ⟨zx, zT, zC, zN, zH, zW1, zW2, zB1, zB2, zCn, zSrc, zDst, zCi⟩ := hz
    simp [Env.get_cons, zx, zT, zC, zN, zH, zW1, zW2, zB1, zB2, zCn, zSrc, zDst, zCi]
  · -- recorded levels
    refine specR_envLoadI (C := ctxH C H) ryT _ (oq + 2) (BitVec.ofNat 64 2) (hD _ (by simp [rySc]))
      (ldq Γ 2 hq) hfire.1 ?_
    refine specR_envLoadI (C := ctxH C H) ryC (vv q) oq (Enc.idxW rl.ctor) (hD _ (by simp [rySc]))
      (by simp only [sev, sev_vv, Env.get_cons, qT, ite_false]; exact hq) hc0 ?_
    refine specR_envLoadI (C := ctxH C H) ryN _ (oq + 1) (BitVec.ofNat 64 rl.nfields) (hD _ (by simp [rySc]))
      (ldq _ 1 (by simp only [Env.get_cons, qT, qC, ite_false]; exact hq)) hn0 ?_
    refine specR_envLoadI (C := ctxH C H) ryH _ (oq + 5) (Enc.idxW rl.rhs) (hD _ (by simp [rySc]))
      (ldq _ 5 (by simp only [Env.get_cons, qT, qC, qN, ite_false]; exact hq)) hh0 ?_
    refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    obtain ⟨w1, hw1, o1, rfl, hb1⟩ := hfire.2
    refine specR_envLoadI (C := ctxH C H) ryW1 _ (oq + 3) (C.EB + BitVec.ofNat 64 (8 * o1)) (hD _ (by simp [rySc]))
      (ldq _ 3 (by simp only [Env.get_cons, qT, qC, qN, qH, ite_false]; exact hq))
      (by rw [show oq + 3 = oq + 2 + 1 by omega]; exact hw1) ?_
    refine specR_envBlkCopyI hok ryB1 ryW1 o1 (lv.map Enc.idxW)
      ⟨hD _ (by simp [rySc]), hD _ (by simp [rySc]), hD _ (by simp [rySc]), hD _ (by simp [rySc]), hD _ (by simp [rySc]),
        hD _ (by simp)⟩
      (by simp [Env.get_cons]; rfl) hb1 (by simp +decide [Env.get_cons]; exact hz) (by decide) (by decide)
      (fun H3 o3 hp3 hl3 hb3 => ?_)
    have hp3' : H <+: H3 := hp3
    refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_alloc6I (ctxOK_H hok H3) x (vv ryC) (vv ryN) (.const 2) (vv ryB1) (.const 0) (vv ryH)
      (Enc.idxW rl.ctor) (BitVec.ofNat 64 rl.nfields) 2 (cellA C o3) 0 (Enc.idxW rl.rhs) hDx
      (fun _ => by simp +decide [sev, Env.get_cons, Ne.symm xC]) (fun _ => by simp +decide [sev, Env.get_cons, Ne.symm xN])
      (fun _ => rfl) (fun _ => by simp +decide [sev, Env.get_cons, Ne.symm xB1])
      (fun _ => rfl) (fun _ => by simp +decide [sev, Env.get_cons, Ne.symm xH])
      (fun H5 ws hp5 hws hroom => ?_)
    obtain ⟨g0, g1, g2, g3, -, g5⟩ := img6_get H5 ws (Enc.idxW rl.ctor) (BitVec.ofNat 64 rl.nfields) 2 (cellA C o3)
      0 (Enc.idxW rl.rhs) hws
    have hpi := img6_prefix H5 ws (Enc.idxW rl.ctor) (BitVec.ofNat 64 rl.nfields) 2 (cellA C o3) 0
      (Enc.idxW rl.rhs) hws
    have hp35 : H3 <+: H5 := hp5
    refine hcont _ _ H5.length ((hp3'.trans hp35).trans hpi)
      ⟨g0, ⟨g1, hnb⟩, by
        rw [hfr]
        exact ⟨g2, ⟨cellA C o3, g3, o3, rfl, blkAt_mono hb3 (hp35.trans hpi)⟩⟩, g5⟩
      (by simp [Env.get_cons]; rfl) (fun z hz => ?_)
    simp only [rySc, List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
    obtain ⟨zx, zT, zC, zN, zH, zW1, zW2, zB1, zB2, zCn, zSrc, zDst, zCi⟩ := hz
    simp [Env.get_cons, zx, zT, zC, zN, zH, zW1, zB1, zCn, zSrc, zDst, zCi]

end

end ConPanqueque.T.Ind
