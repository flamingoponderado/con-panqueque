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

def rdR := ofString "rd_r"
def rdMI := ofString "rd_mi"
def rdRP := ofString "rd_rp"
def rdI := ofString "rd_i"
def rdQ := ofString "rd_q"
def rdT := ofString "rd_t"
def rdX := ofString "rd_x"
def rdK := ofString "rd_k"
def rdNF := ofString "rd_nf"
def rdP1 := ofString "rd_p1"
def rdCt := ofString "rd_ct"
def rdE := ofString "rd_e"
def rdTg := ofString "rd_tg"
def rdCn := ofString "rd_cn"
def rdLw := ofString "rd_lw"
def rdL := ofString "rd_l"
def rdTy := ofString "rd_ty"
def rdP2 := ofString "rd_p2"
def rdPd := ofString "rd_pd"
def rdZ := ofString "rd_z"
def fRuleReads := ofString "ruleReads"

def rdParams : List MlS := [rdR, rdMI, rdRP, rdI, rdQ, rdT]
def rdLocals : List MlS := [rdX, rdK, rdNF, rdP1, rdCt, rdE, rdTg, rdCn, rdLw, rdL, rdTy, rdP2, rdPd, rdZ,
  ryT, ryC, ryN, ryH, ryW1, ryW2, ryB1, ryB2, lCn, lSrc, lDst, lCi, lCz]

def rdBody (C : Ctx) : ProgHOL 64 := prologue rdLocals
  (.ite (veEqC rdR 0) (.return (.const 0))
  (guardP rdRP 58 (guardP rdMI 58 (guardP rdI 58
  (ruleCopyP C rdX rdQ
  (.seq (.call (some (some (.local, rdK), none)) fTSub [vv rdMI, vv rdRP])
  (.seq (.assign .local rdNF (.load .one (.op .add [vv rdQ, .const 8])))
  (guardP rdNF 58
  (.seq (.call (some (some (.local, rdP1), none)) fIotaPartsOf [vv rdR, vv rdRP, vv rdK, vv rdI, vv rdNF])
  (.ite (veEqC rdP1 0) (.return (.const 0))
  (.seq (.assign .local rdCt (.load .one (vv rdQ)))
  (envFindP C rdE (vv rdCt)
  (.ite (veEqC rdE 0) (.return (.const 0))
  (.seq (.assign .local rdTg (.load .one (.op .sub [vv rdE, .const 1])))
  (.ite (veEqC rdTg 4)
    (.seq (.assign .local rdCn (.load .one (.op .add [vv rdE, .const 31])))
    (guardP rdCn 58
    (.seq (.assign .local rdLw (.load .one (.op .add [vv rdE, .const 15])))
    (envBlkCopyP C rdL rdLw
    (.seq (.assign .local rdTy (.load .one (.op .add [vv rdE, .const 23])))
    (.seq (.call (some (some (.local, rdP2), none)) fIotaPartsAt [vv rdX, vv rdL, vv rdTy, vv rdCn, vv rdMI, vv rdRP])
    (.ite (veEqC rdP2 0) (.return (.const 0))
    (.seq (.assign .local rdPd (.load .one (.op .add [vv rdP2, .const 32])))
    (.seq (.call (some (some (.local, rdZ), none)) fIotaPartsRel [vv rdCn, vv rdT, vv rdX, vv rdP1, vv rdP2, vv rdPd])
      (.return (vv rdZ)))))))))))
    (.return (.const 0)))))))))))))))))

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

theorem denoteLList_some_of {st : LStore} : ∀ (us : List LIdx), (∀ u ∈ us, (denoteL st u).isSome = true) →
    ∃ ls, denoteLList st us = some ls
  | [], _ => ⟨[], rfl⟩
  | u :: us, h => by
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp (h u (by simp))
    obtain ⟨ls, hls⟩ := denoteLList_some_of us (fun v hv => h v (by simp [hv]))
    exact ⟨l :: ls, by simp [denoteLList, hl, hls]⟩

theorem rd_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rdLocals → (ctxEnv C ++ rdParams.zip vals).get x = none :=
  Knot.params_none C rdLocals rdParams vals (by decide) (by decide)

/-- The code `ruleReads` runs. -/
structure RDCodes (C : Ctx) : Prop where
  iq : IQCodes C
  ap : APCodes C
  pr : PRCodes C
  apL : C.code.lookup fIotaPartsAt = some (apParams.map (fun p => (p, ShapeHOL.one)), apBody C, .one)
  prL : C.code.lookup fIotaPartsRel = some (prParams.map (fun p => (p, ShapeHOL.one)), prBody, .one)

/-- **`ruleReads`** at a rule of a stored recursor. -/
theorem rd_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : Front.FrontOK C)
    (hc : RDCodes C) (hAn : denoteN C.St.ns anonH = some .anonymous)
    (cv : IConstantVal) (rr : Option IotaRec) (wr : BitVec 64) (mI rP i : Nat) (rl : IRecRule) (oq : Nat)
    (hm : mI < 2 ^ 64) (hr : rP < 2 ^ 64) (hi : i < 2 ^ 64)
    (H : List (BitVec 64)) (hp : C.H <+: H) (hrn : rr = none → wr = 0)
    (hrs : ∀ r, rr = some r → ∃ ob, wr = cellA C ob ∧ IotaRecRep C H ob r)
    (hq : RuleE C.EB C.EH oq rl) (crec : NIdx) (isK : Bool) (rules : List IRecRule)
    (hrec : C.fe.find? crec = some (.recInfo cv mI rP isK rules)) (hmem : rl ∈ rules) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (rdParams.zip [wr, BitVec.ofNat 64 mI, BitVec.ofNat 64 rP, BitVec.ofNat 64 i,
      ecell C oq, Enc.idxW cv.type])) (rdBody C) s (ruleReads C.fe cv rr mI rP i rl) (PostB (ctxH C H)) := by
  refine specR_prologue (postB_locals _) (rd_none _ _) ?_
  unfold ruleReads
  let Γ0 : Env := ctxEnv (ctxH C H) ++ rdParams.zip [wr, BitVec.ofNat 64 mI, BitVec.ofNat 64 rP, BitVec.ofNat 64 i,
      ecell C oq, Enc.idxW cv.type]
  have cnl : ∀ {Γ : Env} {x z : MlS} {v : BitVec 64}, x ∈ rdLocals → z ∉ rdLocals →
      Env.get ((x, v) :: Γ) z = Env.get Γ z := fun {Γ x z v} hx hz => by
    have hne : z ≠ x := fun e => hz (e ▸ hx)
    simp only [Env.get_cons, hne, ite_false]
  have pk : ∀ (Γ : Env), (∀ z, z ∉ rdLocals → Γ.get z = Γ0.get z) → ∀ y, y ∈ rdParams → ∀ v,
      Γ0.get y = some v → Γ.get y = some v := fun Γ hΓ y hy v h => by
    have hyl : y ∉ rdLocals := by
      simp only [rdParams, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    rw [hΓ y hyl, h]
  have gR : Γ0.get rdR = some wr := by simp +decide [Γ0, Env.get, rdParams, ctxEnv]
  have gMI : Γ0.get rdMI = some (BitVec.ofNat 64 mI) := by simp +decide [Γ0, Env.get, rdParams, ctxEnv]
  have gRP : Γ0.get rdRP = some (BitVec.ofNat 64 rP) := by simp +decide [Γ0, Env.get, rdParams, ctxEnv]
  have gI : Γ0.get rdI = some (BitVec.ofNat 64 i) := by simp +decide [Γ0, Env.get, rdParams, ctxEnv]
  have gQ : Γ0.get rdQ = some (ecell C oq) := by simp +decide [Γ0, Env.get, rdParams, ctxEnv]
  have gT : Γ0.get rdT = some (Enc.idxW cv.type) := by simp +decide [Γ0, Env.get, rdParams, ctxEnv]
  have vZ : Γ0.get lCz = none := rd_none (ctxH C H) _ lCz (by decide)
  have ret0 : ∀ (H1 : List (BitVec 64)) (s1 : AState) (Γ : Env) (M : Mem), H <+: H1 →
      SpecR (σ := σ) (Inv (ctxH C H1) s1 Γ M (ctxLocals ++ rdLocals)) (.return (.const 0)) s1 (pure false)
        (PostB (ctxH C H)) := fun H1 s1 Γ M hp1 =>
    specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : H.length ≤ C.HN := hHN
  rcases rr with _ | r
  · rw [hrn rfl] at gR
    refine specR_ifI _ 1 (by simp +decide [veEqC, sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; simp only [Γ0] at gR; rw [gR]; rfl)
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact ret0 H s _ _ (List.prefix_refl _)
  obtain ⟨ob, hwr, hrep⟩ := hrs r rfl
  subst hwr
  have hob : ob < H.length := by
    obtain ⟨⟨op, h1, -⟩, -⟩ := hrep; exact (List.getElem?_eq_some_iff.mp h1).1
  have hne : cellA C ob ≠ 0 := cellA_ne0 C hok ob (by omega)
  refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; simp only [Γ0] at gR; rw [gR]; simp; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only
  refine specR_guardI rdRP rP 58 (by decide) gRP hr (fun hr' => ?_)
  refine specR_guardI rdMI mI 58 (by decide) gMI hm (fun hm' => ?_)
  refine specR_guardI rdI i 58 (by decide) gI hi (fun hi' => ?_)
  refine specR_ruleCopyI hok rdX rdQ oq rl (fun z hz => by
      simp only [rySc, List.mem_cons, List.not_mem_nil, or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide)
    gQ hq vZ (by decide) (by decide) (fun H1 Γ1 q1 hp1 hq1 gX hΓ1 => ?_)
  have hp1' : H <+: H1 := hp1
  have g1 : ∀ y, y ∈ rdParams → ∀ v, Γ0.get y = some v → Γ1.get y = some v := fun y hy v h => by
    have hyl : y ∉ rdX :: rySc := by
      simp only [rdParams, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    rw [hΓ1 y hyl, h]
  refine specR_pureBind (mI - rP) ?_
  refine rb_tsub (D := ctxLocals ++ rdLocals) C hc.iq.ts mI rP (by omega) (by omega) H1 s rdK (vv rdMI) (vv rdRP)
    (by decide) (by simp only [sev, sev_vv]; exact g1 rdMI (by decide) _ gMI)
    (by simp only [sev, sev_vv]; exact g1 rdRP (by decide) _ gRP) (fun H2 hp2 => ?_)
  have hp12 : H <+: H2 := hp1'.trans hp2
  obtain ⟨hc0, ⟨hn0, hnb⟩, hfire, hh0⟩ := hq
  refine specR_envLoadI (C := ctxH C H2) rdNF _ (oq + 1) (BitVec.ofNat 64 rl.nfields) (by decide)
    (by
      simp only [sev, sev_vv, Env.get_cons]; simp +decide
      rw [g1 rdQ (by decide) _ gQ]; simp; exact ecell_add C oq 1) hn0 ?_
  refine specR_guardI rdNF rl.nfields 58 (by decide) (by simp [Env.get_cons]) (by omega) (fun hnf => ?_)
  let Γ2 : Env := (rdNF, BitVec.ofNat 64 rl.nfields) :: (rdK, BitVec.ofNat 64 (mI - rP)) :: Γ1
  have g2 : ∀ y, y ∈ rdParams → ∀ v, Γ0.get y = some v → Γ2.get y = some v := fun y hy v h => by
    have hyl : y ∉ rdLocals := by
      simp only [rdParams, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    simp only [Γ2]; rw [cnl (by decide) hyl, cnl (by decide) hyl]; exact g1 y hy v h
  refine specR_callNIH (C := ctxH C H2) rdP1 fIotaPartsOf iqoParams [vv rdR, vv rdRP, vv rdK, vv rdI, vv rdNF]
    (iqoBody C) [cellA C ob, BitVec.ofNat 64 rP, BitVec.ofNat 64 (mI - rP), BitVec.ofNat 64 i,
      BitVec.ofNat 64 rl.nfields] (by decide) rfl (by decide) hc.iq.iqo
    ⟨by simp only [sev, sev_vv]; exact g2 rdR (by decide) _ gR, by simp only [sev, sev_vv]; exact g2 rdRP (by decide) _ gRP,
      by simp +decide [Γ2, sev, Env.get_cons], by simp only [sev, sev_vv]; exact g2 rdI (by decide) _ gI,
      by simp [Γ2, sev, Env.get_cons], trivial⟩
    (PostIP (ctxH C H2))
    (fun o w _ H' => (o = none → w = 0) ∧ ∀ ip, o = some ip → ∃ ob', w = cellA C ob' ∧ PartsRep C H' ob' ip)
    (fun o w s' st ⟨H', hp', hs', h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hs'⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu iqoParams _ rfl hlk)
      (iqo_spec ra C hok hc.iq r ob rP (mI - rP) i rl (by omega) (by omega) (by omega) (by omega) H2
        (hp.trans hp12)
        (iotaRecRep_mono hrep hp12) s))
    (fun o w s1 H3 hp3 ⟨hn1, hs1⟩ => ?_)
  have hp13 : H <+: H3 := hp12.trans hp3
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN3 => ?_)
  have hHN3' : H3.length ≤ C.HN := hHN3
  have hlay := hok.heapLay
  let Γ3 : Env := (rdP1, w) :: Γ2
  have g3 : ∀ y, y ∈ rdParams → ∀ v, Γ0.get y = some v → Γ3.get y = some v := fun y hy v h => by
    have hyl : y ∉ rdLocals := by
      simp only [rdParams, List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
    simp only [Γ3]; rw [cnl (by decide) hyl]; exact g2 y hy v h
  rcases o with _ | pp
  · rw [hn1 rfl]
    refine specR_ifI _ 1 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact ret0 H3 s1 _ _ hp13
  obtain ⟨ob1, rfl, hpr1⟩ := hs1 pp rfl
  have hob1 : ob1 < H3.length := by
    obtain ⟨⟨o1, h1, -⟩, -⟩ := hpr1; exact (List.getElem?_eq_some_iff.mp h1).1
  have hne1 : cellA C ob1 ≠ 0 := cellA_ne0 C hok ob1 (by omega)
  refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne1)
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only
  refine specR_envLoadI (C := ctxH C H3) rdCt (vv rdQ) oq (Enc.idxW rl.ctor) (by decide)
    (by simp only [sev, sev_vv]; exact g3 rdQ (by decide) _ gQ) hc0 ?_
  have hkb : Env.get ((rdCt, Enc.idxW rl.ctor) :: Γ3) lKb = some (ctxH C H3).KB := by
    simp +decide only [Γ3, Γ2, Env.get_cons, ite_false]
    rw [hΓ1 lKb (by decide)]
    simp +decide [Γ0, Env.get, rdParams, ctxEnv]; rfl
  refine specR_envFindI (C := ctxH C H3) (ctxOK_H hok H3) hc.pr.ae.cG hc.pr.ae.cP rdE (vv rdCt) rl.ctor (by decide)
    (by simp [sev, Env.get_cons]) hkb ?_
  have hfr := find_rel (ctxOK_H hok H3) rl.ctor
  have efe : (ctxH C H3).fe = C.fe := rfl
  rw [efe] at hfr
  cases hfm : C.fe.find? rl.ctor with
  | none =>
    rw [hfm] at hfr
    simp only [hfr, optWG]
    refine specR_ifI _ 1 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact ret0 H3 s1 _ _ hp13
  | some ci =>
    rw [hfm] at hfr
    obtain ⟨o, he, hcie⟩ := hfr
    simp only [he, optWG, id]
    refine specR_fact (fun t ht => ht.sr.env.1.len) (fun hEN => ?_)
    have hEN' : C.EH.length ≤ C.EN := hEN
    have ho : o < C.EN := by have := cie_lt hcie; exact Nat.lt_of_lt_of_le this hEN
    have hne2 : ecell (ctxH C H3) o + 1 ≠ 0 := ecell_succ_ne (ctxOK_H hok H3) ho
    refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne2)
      (fun h => absurd rfl h) (fun _ => ?_)
    have hle := hok.envLay
    cases ci with
    | ctorInfo cvj cnP nfc ind =>
      obtain ⟨hcve, h4, ⟨hnp, hnpb⟩, -, -⟩ := hcie
      refine specR_envLoadI (C := ctxH C H3) rdTg _ o (BitVec.ofNat 64 4) (by decide)
        (by simp +decide [sev, Env.get_cons]; exact ecell_succ_sub _ o) h4 ?_
      refine specR_ifI _ 1 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only
      have eaddr : ∀ k : Nat, 1 ≤ k ∧ k ≤ 64 → ∀ (Γ' : Env), Γ'.get rdE = some (ecell (ctxH C H3) o + 1) →
          sev Γ' (.op .add [vv rdE, .const (BitVec.ofNat 64 (8 * k - 1))]) = some (ecell (ctxH C H3) (o + k)) := by
        intro k hk Γ' h
        simp only [sev, sev_vv, h]; simp
        simp only [ecell]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega
      refine specR_envLoadI (C := ctxH C H3) rdCn _ (o + 4) (BitVec.ofNat 64 cnP) (by decide)
        (eaddr 4 (by decide) _ (by simp +decide [Env.get_cons])) hnp ?_
      refine specR_guardI rdCn cnP 58 (by decide) (by simp [Env.get_cons]) (by omega) (fun hcn => ?_)
      obtain ⟨wl, hwl, oL0, hwlo, hebL⟩ := hcve.2.1
      refine specR_envLoadI (C := ctxH C H3) rdLw _ (o + 2) wl (by decide)
        (eaddr 2 (by decide) _ (by simp +decide [Env.get_cons])) (by rw [show o + 2 = o + 1 + 1 by omega]; exact hwl) ?_
      refine specR_envBlkCopyI hok rdL rdLw oL0 (cvj.levelParams.map Enc.idxW)
        ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
        (by simp [Env.get_cons, hwlo]; rfl) hebL
        (by
          simp +decide only [Γ3, Γ2, Env.get_cons, ite_false]
          rw [hΓ1 lCz (by decide)]; exact vZ)
        (by decide) (by decide) (fun H4 oL hp4 hl4 hbL => ?_)
      have hp14 : H <+: H4 := hp13.trans hp4
      refine specR_envLoadI (C := ctxH C H4) rdTy _ (o + 3) (Enc.idxW cvj.type) (by decide)
        (eaddr 3 (by decide) _ (by simp +decide [Env.get_cons])) (by rw [show o + 3 = o + 1 + 2 by omega]; exact hcve.2.2)
        ?_
      refine specR_fact (fun t ht => And.intro (sr_lpDen ht.sr rl.ctor _ hfm)
        (And.intro (sr_tyDen ht.sr rl.ctor _ hfm) (sr_recDen ht.sr hrec hmem))) (fun ⟨⟨ks, hks⟩, hty, hrd⟩ => ?_)
      obtain ⟨tyP, htyP⟩ := Option.isSome_iff_exists.mp hty
      have hfl : ∀ lv, ((∃ pins, rl.fire = .nested lv pins) ∨ rl.fire = .levels lv) →
          ∃ ls, denoteLList s1.store.ls lv = some ls := fun lv h => denoteLList_some_of lv (hrd.1 lv h).1
      have hq14 : RuleE C.HB H4 q1 rl := ConPanqueque.T.Decl.ruleE_mono (hp2.trans (hp3.trans hp4)) hq1
      have gX4 : ∀ v, Env.get ((rdTy, v) :: (lCi, BitVec.ofNat 64 (cvj.levelParams.map Enc.idxW).length) ::
          (lDst, cellA C (oL + 1 + (cvj.levelParams.map Enc.idxW).length)) ::
          (lSrc, ecell C (oL0 + 1 + (cvj.levelParams.map Enc.idxW).length)) :: (rdL, cellA C oL) ::
          (lCn, BitVec.ofNat 64 (cvj.levelParams.map Enc.idxW).length) :: (rdLw, wl) :: (rdCn, BitVec.ofNat 64 cnP) ::
          (rdTg, BitVec.ofNat 64 4) :: (rdE, ecell (ctxH C H3) o + 1) :: (rdCt, Enc.idxW rl.ctor) :: Γ3) rdX =
          some (cellA C q1) := fun v => by
        simp +decide only [Γ3, Γ2, Env.get_cons, ite_false]; exact gX
      have gP4 : ∀ v y, y ∈ rdParams → ∀ w', Γ0.get y = some w' → Env.get ((rdTy, v) ::
          (lCi, BitVec.ofNat 64 (cvj.levelParams.map Enc.idxW).length) ::
          (lDst, cellA C (oL + 1 + (cvj.levelParams.map Enc.idxW).length)) ::
          (lSrc, ecell C (oL0 + 1 + (cvj.levelParams.map Enc.idxW).length)) :: (rdL, cellA C oL) ::
          (lCn, BitVec.ofNat 64 (cvj.levelParams.map Enc.idxW).length) :: (rdLw, wl) :: (rdCn, BitVec.ofNat 64 cnP) ::
          (rdTg, BitVec.ofNat 64 4) :: (rdE, ecell (ctxH C H3) o + 1) :: (rdCt, Enc.idxW rl.ctor) :: Γ3) y = some w' := by
        intro v y hy w' h
        have hyl : y ∉ rdLocals := by
          simp only [rdParams, List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
        have hy2 : y ≠ lCi ∧ y ≠ lDst ∧ y ≠ lSrc ∧ y ≠ lCn := by
          simp only [rdParams, List.mem_cons, List.not_mem_nil, or_false] at hy
          rcases hy with rfl|rfl|rfl|rfl|rfl|rfl <;> decide
        rw [cnl (by decide) hyl, Env.get_cons, if_neg hy2.1, Env.get_cons, if_neg hy2.2.1, Env.get_cons, if_neg hy2.2.2.1,
          cnl (by decide) hyl, Env.get_cons, if_neg hy2.2.2.2, cnl (by decide) hyl, cnl (by decide) hyl,
          cnl (by decide) hyl, cnl (by decide) hyl, cnl (by decide) hyl]
        exact g3 y hy w' h
      refine specR_callNIH (C := ctxH C H4) rdP2 fIotaPartsAt apParams [vv rdX, vv rdL, vv rdTy, vv rdCn, vv rdMI, vv rdRP]
        (apBody C) [cellA C q1, cellA C oL, Enc.idxW cvj.type, BitVec.ofNat 64 cnP, BitVec.ofNat 64 mI,
          BitVec.ofNat 64 rP] (by decide) rfl (by decide) hc.apL
        ⟨by simp only [sev, sev_vv]; exact gX4 _, by simp +decide [sev, Env.get_cons], by simp [sev, Env.get_cons],
          by simp +decide [sev, Env.get_cons], by simp only [sev, sev_vv]; exact gP4 _ rdMI (by decide) _ gMI,
          by simp only [sev, sev_vv]; exact gP4 _ rdRP (by decide) _ gRP, trivial⟩
        (PostAB (ctxH C H4))
        (fun o w _ H' => (o = none → w = 0) ∧ ∀ ip pd, o = some (ip, pd) → ∃ ob, w = cellA C ob ∧ PartsRep C H' ob ip ∧
          ∃ o4, H'[ob + 4]? = some (cellA C o4) ∧ BlkAt H' o4 (pd.map Enc.idxW))
        (fun o w s' st ⟨H', hp', hs', h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hs'⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu apParams _ rfl hlk)
          (ap_spec ra C hok hc.ap cvj cnP mI rP rl q1 oL (by omega) hm hr H4 hq14 hbL s1 hks htyP hfl))
        (fun o2 w2 s2 H5 hp5 ⟨hn2, hs2⟩ => ?_)
      have hp45 : H4 <+: H5 := hp5
      have hp15 : H <+: H5 := hp14.trans hp45
      refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN5 => ?_)
      have hHN5' : H5.length ≤ C.HN := hHN5
      rcases o2 with _ | ⟨p, pd⟩
      · rw [hn2 rfl]
        refine specR_ifI _ 1 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun h => absurd h (by decide))
        exact ret0 H5 s2 _ _ hp15
      obtain ⟨ob2, rfl, hpr2, o4, h4c, hbpd⟩ := hs2 p pd rfl
      have hob2 : ob2 < H5.length := by
        obtain ⟨⟨o1, h1, -⟩, -⟩ := hpr2; exact (List.getElem?_eq_some_iff.mp h1).1
      have hne5 : cellA C ob2 ≠ 0 := cellA_ne0 C hok ob2 (by omega)
      refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne5)
        (fun h => absurd rfl h) (fun _ => ?_)
      simp only
      refine UD.specR_heapLoadI' (C := ctxH C H5) rdPd _ (ob2 + 4) _ h4c (by decide)
        (by simp +decide [sev, Env.get_cons]; exact cellA_plus C ob2 4) ?_
      refine specR_congr (m' := iotaPartsRel C.fe cnP cv rl pp p pd >>= fun r => pure r) (by rw [bind_pure]) ?_
      refine specR_callNIH (C := ctxH C H5) rdZ fIotaPartsRel prParams
        [vv rdCn, vv rdT, vv rdX, vv rdP1, vv rdP2, vv rdPd] prBody
        [BitVec.ofNat 64 cnP, Enc.idxW cv.type, cellA C q1, cellA C ob1, cellA C ob2, cellA C o4] (by decide) rfl
        (by decide) hc.prL
        ⟨by simp +decide [sev, Env.get_cons],
          by simp only [sev, sev_vv, Env.get_cons]; simp +decide; exact gP4 (Enc.idxW cvj.type) rdT (by decide) _ gT,
          by simp only [sev, sev_vv, Env.get_cons]; simp +decide; exact gX4 (Enc.idxW cvj.type),
          by simp +decide [sev, Env.get_cons, Γ3], by simp +decide [sev, Env.get_cons],
          by simp +decide [sev, Env.get_cons], trivial⟩
        (PostB (ctxH C H5)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu prParams _ rfl hlk)
          (pr_spec ra C hok hf hc.pr hAn cnP hcn cv rl pp p pd q1 ob1 ob2 o4 H5
            (ConPanqueque.T.Decl.ruleE_mono hp45 hq14) (partsRep_mono hpr1 (hp4.trans hp45)) hpr2 hbpd s2))
        (fun r w s3 H6 hp6 hw => ?_)
      subst hw
      have hp6' : H5 <+: H6 := hp6
      exact specR_returnI _ _ (by simp [sev, Env.get_cons])
        (fun t ht => ⟨H6, hp15.trans hp6', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | _ =>
      obtain ⟨k, hk, hk1⟩ : ∃ k : Nat, C.EH[o]? = some (BitVec.ofNat 64 k) ∧ k ≠ 4 ∧ k < 16 := by
        first
          | exact ⟨0, hcie.2, by decide, by decide⟩
          | exact ⟨1, hcie.2.1, by decide, by decide⟩
          | exact ⟨2, hcie.2, by decide, by decide⟩
          | exact ⟨3, hcie.2.1, by decide, by decide⟩
          | exact ⟨5, hcie.2.1, by decide, by decide⟩
      refine specR_envLoadI (C := ctxH C H3) rdTg _ o (BitVec.ofNat 64 k) (by decide)
        (by simp +decide [sev, Env.get_cons]; exact ecell_succ_sub _ o) hk ?_
      have hne4 : BitVec.ofNat 64 k ≠ BitVec.ofNat 64 4 := (ofNat_eq_iff (by omega) (by decide)).not.mpr hk1.1
      refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne4])
        (fun h => absurd rfl h) (fun _ => ?_)
      exact ret0 H3 s1 _ _ hp13

end

end ConPanqueque.T.Ind
