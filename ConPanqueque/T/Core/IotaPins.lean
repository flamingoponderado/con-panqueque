import ConPanqueque.T.Core.RecFire
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `instSpinePins`: a nested rule's stored parameter pins at the recursor's instantiation

Each pin (an environment cell) is level-instantiated (`instLPFast`, the recursor's level parameters a heap
block) and instantiated at the recursor's leading arguments (`instSpine` over a block holding `args.take rP`,
from index `rP - 1` saturating), then appended to an accumulator block. The twin-side preconditions of
`instLPFast` are an invariant family `Q`, closed under the two runs.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.T.ILP (fInstLPF ilpfBody ilpf_spec CodesILP ilpParams ilpBody PostILP)
open ConPanqueque.V.Enc

def ipS := ofString "ips"
def ipN := ofString "ipn"
def ipK := ofString "ipk"
def ipU := ofString "ipu"
def ipT := ofString "ipt"
def ipRp := ofString "iprp"
def ipA := ofString "ipa"
def ipP := ofString "ipp"
def ipQ := ofString "ipq"
def ipD := ofString "ipd"
def ipR := ofString "ipr"
def ipA2 := ofString "ipa2"
def ipX := ofString "ipx"
def fIp := ofString "instSpinePins"

@[simp] theorem ip_ipS_ne_ipN : ipS ≠ ipN := by decide
@[simp] theorem ip_ipS_ne_ipK : ipS ≠ ipK := by decide
@[simp] theorem ip_ipS_ne_ipU : ipS ≠ ipU := by decide
@[simp] theorem ip_ipS_ne_ipT : ipS ≠ ipT := by decide
@[simp] theorem ip_ipS_ne_ipRp : ipS ≠ ipRp := by decide
@[simp] theorem ip_ipS_ne_ipA : ipS ≠ ipA := by decide
@[simp] theorem ip_ipS_ne_ipP : ipS ≠ ipP := by decide
@[simp] theorem ip_ipS_ne_ipQ : ipS ≠ ipQ := by decide
@[simp] theorem ip_ipS_ne_ipD : ipS ≠ ipD := by decide
@[simp] theorem ip_ipS_ne_ipR : ipS ≠ ipR := by decide
@[simp] theorem ip_ipS_ne_ipA2 : ipS ≠ ipA2 := by decide
@[simp] theorem ip_ipS_ne_ipX : ipS ≠ ipX := by decide
@[simp] theorem ip_ipS_ne_lKb : ipS ≠ lKb := by decide
@[simp] theorem ip_ipN_ne_ipS : ipN ≠ ipS := by decide
@[simp] theorem ip_ipN_ne_ipK : ipN ≠ ipK := by decide
@[simp] theorem ip_ipN_ne_ipU : ipN ≠ ipU := by decide
@[simp] theorem ip_ipN_ne_ipT : ipN ≠ ipT := by decide
@[simp] theorem ip_ipN_ne_ipRp : ipN ≠ ipRp := by decide
@[simp] theorem ip_ipN_ne_ipA : ipN ≠ ipA := by decide
@[simp] theorem ip_ipN_ne_ipP : ipN ≠ ipP := by decide
@[simp] theorem ip_ipN_ne_ipQ : ipN ≠ ipQ := by decide
@[simp] theorem ip_ipN_ne_ipD : ipN ≠ ipD := by decide
@[simp] theorem ip_ipN_ne_ipR : ipN ≠ ipR := by decide
@[simp] theorem ip_ipN_ne_ipA2 : ipN ≠ ipA2 := by decide
@[simp] theorem ip_ipN_ne_ipX : ipN ≠ ipX := by decide
@[simp] theorem ip_ipN_ne_lKb : ipN ≠ lKb := by decide
@[simp] theorem ip_ipK_ne_ipS : ipK ≠ ipS := by decide
@[simp] theorem ip_ipK_ne_ipN : ipK ≠ ipN := by decide
@[simp] theorem ip_ipK_ne_ipU : ipK ≠ ipU := by decide
@[simp] theorem ip_ipK_ne_ipT : ipK ≠ ipT := by decide
@[simp] theorem ip_ipK_ne_ipRp : ipK ≠ ipRp := by decide
@[simp] theorem ip_ipK_ne_ipA : ipK ≠ ipA := by decide
@[simp] theorem ip_ipK_ne_ipP : ipK ≠ ipP := by decide
@[simp] theorem ip_ipK_ne_ipQ : ipK ≠ ipQ := by decide
@[simp] theorem ip_ipK_ne_ipD : ipK ≠ ipD := by decide
@[simp] theorem ip_ipK_ne_ipR : ipK ≠ ipR := by decide
@[simp] theorem ip_ipK_ne_ipA2 : ipK ≠ ipA2 := by decide
@[simp] theorem ip_ipK_ne_ipX : ipK ≠ ipX := by decide
@[simp] theorem ip_ipK_ne_lKb : ipK ≠ lKb := by decide
@[simp] theorem ip_ipU_ne_ipS : ipU ≠ ipS := by decide
@[simp] theorem ip_ipU_ne_ipN : ipU ≠ ipN := by decide
@[simp] theorem ip_ipU_ne_ipK : ipU ≠ ipK := by decide
@[simp] theorem ip_ipU_ne_ipT : ipU ≠ ipT := by decide
@[simp] theorem ip_ipU_ne_ipRp : ipU ≠ ipRp := by decide
@[simp] theorem ip_ipU_ne_ipA : ipU ≠ ipA := by decide
@[simp] theorem ip_ipU_ne_ipP : ipU ≠ ipP := by decide
@[simp] theorem ip_ipU_ne_ipQ : ipU ≠ ipQ := by decide
@[simp] theorem ip_ipU_ne_ipD : ipU ≠ ipD := by decide
@[simp] theorem ip_ipU_ne_ipR : ipU ≠ ipR := by decide
@[simp] theorem ip_ipU_ne_ipA2 : ipU ≠ ipA2 := by decide
@[simp] theorem ip_ipU_ne_ipX : ipU ≠ ipX := by decide
@[simp] theorem ip_ipU_ne_lKb : ipU ≠ lKb := by decide
@[simp] theorem ip_ipT_ne_ipS : ipT ≠ ipS := by decide
@[simp] theorem ip_ipT_ne_ipN : ipT ≠ ipN := by decide
@[simp] theorem ip_ipT_ne_ipK : ipT ≠ ipK := by decide
@[simp] theorem ip_ipT_ne_ipU : ipT ≠ ipU := by decide
@[simp] theorem ip_ipT_ne_ipRp : ipT ≠ ipRp := by decide
@[simp] theorem ip_ipT_ne_ipA : ipT ≠ ipA := by decide
@[simp] theorem ip_ipT_ne_ipP : ipT ≠ ipP := by decide
@[simp] theorem ip_ipT_ne_ipQ : ipT ≠ ipQ := by decide
@[simp] theorem ip_ipT_ne_ipD : ipT ≠ ipD := by decide
@[simp] theorem ip_ipT_ne_ipR : ipT ≠ ipR := by decide
@[simp] theorem ip_ipT_ne_ipA2 : ipT ≠ ipA2 := by decide
@[simp] theorem ip_ipT_ne_ipX : ipT ≠ ipX := by decide
@[simp] theorem ip_ipT_ne_lKb : ipT ≠ lKb := by decide
@[simp] theorem ip_ipRp_ne_ipS : ipRp ≠ ipS := by decide
@[simp] theorem ip_ipRp_ne_ipN : ipRp ≠ ipN := by decide
@[simp] theorem ip_ipRp_ne_ipK : ipRp ≠ ipK := by decide
@[simp] theorem ip_ipRp_ne_ipU : ipRp ≠ ipU := by decide
@[simp] theorem ip_ipRp_ne_ipT : ipRp ≠ ipT := by decide
@[simp] theorem ip_ipRp_ne_ipA : ipRp ≠ ipA := by decide
@[simp] theorem ip_ipRp_ne_ipP : ipRp ≠ ipP := by decide
@[simp] theorem ip_ipRp_ne_ipQ : ipRp ≠ ipQ := by decide
@[simp] theorem ip_ipRp_ne_ipD : ipRp ≠ ipD := by decide
@[simp] theorem ip_ipRp_ne_ipR : ipRp ≠ ipR := by decide
@[simp] theorem ip_ipRp_ne_ipA2 : ipRp ≠ ipA2 := by decide
@[simp] theorem ip_ipRp_ne_ipX : ipRp ≠ ipX := by decide
@[simp] theorem ip_ipRp_ne_lKb : ipRp ≠ lKb := by decide
@[simp] theorem ip_ipA_ne_ipS : ipA ≠ ipS := by decide
@[simp] theorem ip_ipA_ne_ipN : ipA ≠ ipN := by decide
@[simp] theorem ip_ipA_ne_ipK : ipA ≠ ipK := by decide
@[simp] theorem ip_ipA_ne_ipU : ipA ≠ ipU := by decide
@[simp] theorem ip_ipA_ne_ipT : ipA ≠ ipT := by decide
@[simp] theorem ip_ipA_ne_ipRp : ipA ≠ ipRp := by decide
@[simp] theorem ip_ipA_ne_ipP : ipA ≠ ipP := by decide
@[simp] theorem ip_ipA_ne_ipQ : ipA ≠ ipQ := by decide
@[simp] theorem ip_ipA_ne_ipD : ipA ≠ ipD := by decide
@[simp] theorem ip_ipA_ne_ipR : ipA ≠ ipR := by decide
@[simp] theorem ip_ipA_ne_ipA2 : ipA ≠ ipA2 := by decide
@[simp] theorem ip_ipA_ne_ipX : ipA ≠ ipX := by decide
@[simp] theorem ip_ipA_ne_lKb : ipA ≠ lKb := by decide
@[simp] theorem ip_ipP_ne_ipS : ipP ≠ ipS := by decide
@[simp] theorem ip_ipP_ne_ipN : ipP ≠ ipN := by decide
@[simp] theorem ip_ipP_ne_ipK : ipP ≠ ipK := by decide
@[simp] theorem ip_ipP_ne_ipU : ipP ≠ ipU := by decide
@[simp] theorem ip_ipP_ne_ipT : ipP ≠ ipT := by decide
@[simp] theorem ip_ipP_ne_ipRp : ipP ≠ ipRp := by decide
@[simp] theorem ip_ipP_ne_ipA : ipP ≠ ipA := by decide
@[simp] theorem ip_ipP_ne_ipQ : ipP ≠ ipQ := by decide
@[simp] theorem ip_ipP_ne_ipD : ipP ≠ ipD := by decide
@[simp] theorem ip_ipP_ne_ipR : ipP ≠ ipR := by decide
@[simp] theorem ip_ipP_ne_ipA2 : ipP ≠ ipA2 := by decide
@[simp] theorem ip_ipP_ne_ipX : ipP ≠ ipX := by decide
@[simp] theorem ip_ipP_ne_lKb : ipP ≠ lKb := by decide
@[simp] theorem ip_ipQ_ne_ipS : ipQ ≠ ipS := by decide
@[simp] theorem ip_ipQ_ne_ipN : ipQ ≠ ipN := by decide
@[simp] theorem ip_ipQ_ne_ipK : ipQ ≠ ipK := by decide
@[simp] theorem ip_ipQ_ne_ipU : ipQ ≠ ipU := by decide
@[simp] theorem ip_ipQ_ne_ipT : ipQ ≠ ipT := by decide
@[simp] theorem ip_ipQ_ne_ipRp : ipQ ≠ ipRp := by decide
@[simp] theorem ip_ipQ_ne_ipA : ipQ ≠ ipA := by decide
@[simp] theorem ip_ipQ_ne_ipP : ipQ ≠ ipP := by decide
@[simp] theorem ip_ipQ_ne_ipD : ipQ ≠ ipD := by decide
@[simp] theorem ip_ipQ_ne_ipR : ipQ ≠ ipR := by decide
@[simp] theorem ip_ipQ_ne_ipA2 : ipQ ≠ ipA2 := by decide
@[simp] theorem ip_ipQ_ne_ipX : ipQ ≠ ipX := by decide
@[simp] theorem ip_ipQ_ne_lKb : ipQ ≠ lKb := by decide
@[simp] theorem ip_ipD_ne_ipS : ipD ≠ ipS := by decide
@[simp] theorem ip_ipD_ne_ipN : ipD ≠ ipN := by decide
@[simp] theorem ip_ipD_ne_ipK : ipD ≠ ipK := by decide
@[simp] theorem ip_ipD_ne_ipU : ipD ≠ ipU := by decide
@[simp] theorem ip_ipD_ne_ipT : ipD ≠ ipT := by decide
@[simp] theorem ip_ipD_ne_ipRp : ipD ≠ ipRp := by decide
@[simp] theorem ip_ipD_ne_ipA : ipD ≠ ipA := by decide
@[simp] theorem ip_ipD_ne_ipP : ipD ≠ ipP := by decide
@[simp] theorem ip_ipD_ne_ipQ : ipD ≠ ipQ := by decide
@[simp] theorem ip_ipD_ne_ipR : ipD ≠ ipR := by decide
@[simp] theorem ip_ipD_ne_ipA2 : ipD ≠ ipA2 := by decide
@[simp] theorem ip_ipD_ne_ipX : ipD ≠ ipX := by decide
@[simp] theorem ip_ipD_ne_lKb : ipD ≠ lKb := by decide
@[simp] theorem ip_ipR_ne_ipS : ipR ≠ ipS := by decide
@[simp] theorem ip_ipR_ne_ipN : ipR ≠ ipN := by decide
@[simp] theorem ip_ipR_ne_ipK : ipR ≠ ipK := by decide
@[simp] theorem ip_ipR_ne_ipU : ipR ≠ ipU := by decide
@[simp] theorem ip_ipR_ne_ipT : ipR ≠ ipT := by decide
@[simp] theorem ip_ipR_ne_ipRp : ipR ≠ ipRp := by decide
@[simp] theorem ip_ipR_ne_ipA : ipR ≠ ipA := by decide
@[simp] theorem ip_ipR_ne_ipP : ipR ≠ ipP := by decide
@[simp] theorem ip_ipR_ne_ipQ : ipR ≠ ipQ := by decide
@[simp] theorem ip_ipR_ne_ipD : ipR ≠ ipD := by decide
@[simp] theorem ip_ipR_ne_ipA2 : ipR ≠ ipA2 := by decide
@[simp] theorem ip_ipR_ne_ipX : ipR ≠ ipX := by decide
@[simp] theorem ip_ipR_ne_lKb : ipR ≠ lKb := by decide
@[simp] theorem ip_ipA2_ne_ipS : ipA2 ≠ ipS := by decide
@[simp] theorem ip_ipA2_ne_ipN : ipA2 ≠ ipN := by decide
@[simp] theorem ip_ipA2_ne_ipK : ipA2 ≠ ipK := by decide
@[simp] theorem ip_ipA2_ne_ipU : ipA2 ≠ ipU := by decide
@[simp] theorem ip_ipA2_ne_ipT : ipA2 ≠ ipT := by decide
@[simp] theorem ip_ipA2_ne_ipRp : ipA2 ≠ ipRp := by decide
@[simp] theorem ip_ipA2_ne_ipA : ipA2 ≠ ipA := by decide
@[simp] theorem ip_ipA2_ne_ipP : ipA2 ≠ ipP := by decide
@[simp] theorem ip_ipA2_ne_ipQ : ipA2 ≠ ipQ := by decide
@[simp] theorem ip_ipA2_ne_ipD : ipA2 ≠ ipD := by decide
@[simp] theorem ip_ipA2_ne_ipR : ipA2 ≠ ipR := by decide
@[simp] theorem ip_ipA2_ne_ipX : ipA2 ≠ ipX := by decide
@[simp] theorem ip_ipA2_ne_lKb : ipA2 ≠ lKb := by decide
@[simp] theorem ip_ipX_ne_ipS : ipX ≠ ipS := by decide
@[simp] theorem ip_ipX_ne_ipN : ipX ≠ ipN := by decide
@[simp] theorem ip_ipX_ne_ipK : ipX ≠ ipK := by decide
@[simp] theorem ip_ipX_ne_ipU : ipX ≠ ipU := by decide
@[simp] theorem ip_ipX_ne_ipT : ipX ≠ ipT := by decide
@[simp] theorem ip_ipX_ne_ipRp : ipX ≠ ipRp := by decide
@[simp] theorem ip_ipX_ne_ipA : ipX ≠ ipA := by decide
@[simp] theorem ip_ipX_ne_ipP : ipX ≠ ipP := by decide
@[simp] theorem ip_ipX_ne_ipQ : ipX ≠ ipQ := by decide
@[simp] theorem ip_ipX_ne_ipD : ipX ≠ ipD := by decide
@[simp] theorem ip_ipX_ne_ipR : ipX ≠ ipR := by decide
@[simp] theorem ip_ipX_ne_ipA2 : ipX ≠ ipA2 := by decide
@[simp] theorem ip_ipX_ne_lKb : ipX ≠ lKb := by decide
@[simp] theorem ip_lKb_ne_ipS : lKb ≠ ipS := by decide
@[simp] theorem ip_lKb_ne_ipN : lKb ≠ ipN := by decide
@[simp] theorem ip_lKb_ne_ipK : lKb ≠ ipK := by decide
@[simp] theorem ip_lKb_ne_ipU : lKb ≠ ipU := by decide
@[simp] theorem ip_lKb_ne_ipT : lKb ≠ ipT := by decide
@[simp] theorem ip_lKb_ne_ipRp : lKb ≠ ipRp := by decide
@[simp] theorem ip_lKb_ne_ipA : lKb ≠ ipA := by decide
@[simp] theorem ip_lKb_ne_ipP : lKb ≠ ipP := by decide
@[simp] theorem ip_lKb_ne_ipQ : lKb ≠ ipQ := by decide
@[simp] theorem ip_lKb_ne_ipD : lKb ≠ ipD := by decide
@[simp] theorem ip_lKb_ne_ipR : lKb ≠ ipR := by decide
@[simp] theorem ip_lKb_ne_ipA2 : lKb ≠ ipA2 := by decide
@[simp] theorem ip_lKb_ne_ipX : lKb ≠ ipX := by decide

def ipParams : List MlS := [ipS, ipN, ipK, ipU, ipT, ipRp, ipA]
def ipLocals : List MlS := [ipP, ipQ, ipD, ipR, ipA2, ipX]

def ipCore : ProgHOL 64 :=
  .ite (.cmp .equal (vv ipN) (.const 0)) (.return (vv ipA))
  (.seq (.assign .local ipP (.load .one (vv ipS)))
  (.seq (.call (some (some (.local, ipQ), none)) fInstLPF [.const (BitVec.ofNat 64 coreWalkFuel), vv ipP, vv ipK, vv ipU])
  (.seq (.assign .local ipD (.op .sub [vv ipRp, .cmp .notEqual (vv ipRp) (.const 0)]))
  (.seq (.call (some (some (.local, ipR), none)) ExIS.fInstSpine
      [.const (BitVec.ofNat 64 coreWalkFuel), vv ipT, .const 0, vv ipD, vv ipQ])
  (.seq (.call (some (some (.local, ipA2), none)) ExPre.fAppend [vv ipA, vv ipR])
  (.seq (.call (some (some (.local, ipX), none)) fIp
      [.op .add [vv ipS, .const 8], .op .sub [vv ipN, .const 1], vv ipK, vv ipU, vv ipT, vv ipRp, vv ipA2])
    (.return (vv ipX))))))))

def ipBody : ProgHOL 64 := prologue ipLocals ipCore

structure IpCodes (C : Ctx) : Prop where
  ilpf : C.code.lookup fInstLPF = some (ilpParams.map (fun p => (p, ShapeHOL.one)), ilpfBody C, .one)
  ilp : CodesILP C (ilpBody C)
  isc : ExI.Codes C (ExI.body C)
  i1 : C.code.lookup ExI.fInst1F = some ([(pFu, .one), (pH, .one), (ExI.pV, .one), (ExI.pD, .one)], ExI.fastBody C, .one)
  is : C.code.lookup ExIS.fInstSpine = some (ExIS.isParams.map (fun p => (p, ShapeHOL.one)), ExIS.isBody, .one)
  app : C.code.lookup ExPre.fAppend = some (ExPre.appParams.map (fun p => (p, ShapeHOL.one)), ExPre.appBody C, .one)
  self : C.code.lookup fIp = some (ipParams.map (fun p => (p, ShapeHOL.one)), ipBody, .one)

section
variable {σ : Type}

theorem ip_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ipLocals → (ctxEnv C ++ ipParams.zip vals).get x = none :=
  Knot.params_none C ipLocals ipParams vals (by decide) (by decide)

theorem ip_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : IpCodes C)
    (lps : List NIdx) (ks : List ConLeche.Name) (us : LsIdx) (vs : List ConLeche.Level) (args : List EIdx) (rP : Nat)
    (hrP : rP < 2 ^ 63) (ok ot : Nat) (P0 : List EIdx) (Q : AState → Prop)
    (hQ : ∀ s, Q s → StateOK s ∧ ReadNCacheOK s.caches.readNC s.store ∧ ReadLCacheOK s.caches.readLC s.store ∧
      ReadLsCacheOK s.caches.readLsC s.store ∧ Frontend.denoteNList s.store.ns lps = some ks ∧
      denoteLs s.store.lss us = some vs ∧ ∀ p, p ∈ P0 → (denoteE s.store p).isSome = true)
    (hQi : ∀ s p q s', Q s → instLPFast coreWalkFuel lps us p s = .ok (q, s') → Q s')
    (hQs : ∀ s q r s', Q s → instSpine coreWalkFuel (args.take rP) (rP - 1) q s = .ok (r, s') → Q s') :
    ∀ (pins : List EIdx) (qs : Nat) (H : List (BitVec 64)) (acc : List EIdx) (oa : Nat) (s : AState), C.H <+: H →
      (∀ p, p ∈ pins → p ∈ P0) → (∀ j (hj : j < pins.length), C.EH[qs + j]? = some (Enc.idxW pins[j])) →
      BlkAt H oa (acc.map Enc.idxW) → BlkAt H ok (lps.map Enc.idxW) → BlkAt H ot ((args.take rP).map Enc.idxW) →
      Q s → pins.length < 2 ^ 60 →
      SpecR (σ := σ) (Pre (ctxH C H) s (ipParams.zip [ecell C qs, BitVec.ofNat 64 pins.length, cellA C ok, Enc.idxW us,
        cellA C ot, BitVec.ofNat 64 rP, cellA C oa])) ipBody s
        (instSpinePins lps us args rP pins >>= fun xs => pure (acc ++ xs)) (PostA (ctxH C H)) := by
  intro pins
  induction pins with
  | nil =>
    intro qs H acc oa s hp hsub hsrc hb hko hbt hq hlen
    refine specR_prologue (postA_locals _) (ip_none _ _) ?_
    unfold ipCore
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ipParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [instSpinePins, pure_bind, List.append_nil]
    exact specR_returnI _ (cellA C oa) (by simp +decide [Env.get, ipParams, ctxEnv] <;> rfl)
      (fun t ht => ⟨H, oa, List.prefix_refl _, rfl, hb, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | cons p pins ih =>
    intro qs H acc oa s hp hsub hsrc hb hko hbt hq hlen
    obtain ⟨hst, hcn, hcl, hcls, hks, hus, hden⟩ := hQ s hq
    refine specR_prologue (postA_locals _) (ip_none _ _) ?_
    unfold ipCore
    have hne := ofNat_succ_ne pins.length (by simp at hlen; omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ipParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_envLoadI ipP (vv ipS) qs (Enc.idxW p) (by decide) (by simp +decide [Env.get, ipParams, ctxEnv]; rfl)
      (hsrc 0 (by simp) : C.EH[qs]? = _) ?_
    simp only [instSpinePins, bind_assoc, pure_bind]
    refine specR_callNIH (C := ctxH C H) ipQ fInstLPF ilpParams
      [.const (BitVec.ofNat 64 coreWalkFuel), vv ipP, vv ipK, vv ipU] (ilpfBody C)
      [BitVec.ofNat 64 coreWalkFuel, Enc.idxW p, cellA C ok, Enc.idxW us] (by decide) rfl (by decide) hc.ilpf
      ⟨rfl, by simp, by simp +decide [Env.get, ipParams, ctxEnv] <;> rfl, by simp +decide [Env.get, ipParams, ctxEnv],
        trivial⟩
      (fun a w s' st => instLPFast coreWalkFuel lps us p s = .ok (a, s') ∧ PostILP (ctxH C H) a w s' st)
      (fun a w s' _ => instLPFast coreWalkFuel lps us p s = .ok (a, s') ∧ w = Enc.idxW a)
      (fun a w s' st ⟨hrun, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hrun, hw⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu ilpParams _ rfl hlk)
        (ilpf_spec ra C hok hc.ilp coreWalkFuel CV.coreWalkFuel_lt ok lps ks us vs H s p hks hus hst hcn hcl hcls
          (hden p (hsub p (by simp))) hko)))
      (fun q w s1 H1 hp1 ⟨hrun1, hw⟩ => ?_)
    subst hw
    have hq1 := hQi s p q s1 hq hrun1
    refine specR_assignI ipD _ (BitVec.ofNat 64 (rP - 1)) (by decide)
      (by simp +decide [sev, Env.get, ipParams, ctxEnv]; exact ExIS.satPred rP hrP) ?_
    refine specR_callNIH (C := ctxH C H1) ipR ExIS.fInstSpine ExIS.isParams
      [.const (BitVec.ofNat 64 coreWalkFuel), vv ipT, .const 0, vv ipD, vv ipQ] ExIS.isBody
      [BitVec.ofNat 64 coreWalkFuel, cellA C ot, BitVec.ofNat 64 0, BitVec.ofNat 64 (rP - 1), Enc.idxW q]
      (by decide) rfl (by decide) hc.is
      ⟨rfl, by simp +decide [Env.get, ipParams, ctxEnv] <;> rfl, rfl, by simp, by simp, trivial⟩
      (fun a w s' st => instSpine coreWalkFuel ((args.take rP).drop 0) (rP - 1) q s1 = .ok (a, s') ∧
        PostE (ctxH C H1) a w s' st)
      (fun a w s' H' => instSpine coreWalkFuel ((args.take rP).drop 0) (rP - 1) q s1 = .ok (a, s') ∧
        w = Enc.idxW a ∧ H' = H1)
      (fun a w s' st ⟨hrun, hw, hsr⟩ => ⟨H1, List.prefix_refl _, ⟨hrun, hw, rfl⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu ExIS.isParams _ rfl hlk)
        (ExIS.is_spec ra C hok hc.isc hc.i1 hc.is coreWalkFuel CV.coreWalkFuel_lt ot (args.take rP) _ H1 s1 0 (rP - 1)
          q rfl (by omega) (by omega) (blkAt_mono hbt hp1))))
      (fun r w s2 H2 hp2 ⟨hrun2, hw, hH2⟩ => ?_)
    subst hw; subst hH2
    simp only [List.drop_zero] at hrun2
    have hq2 := hQs s1 q r s2 hq1 hrun2
    refine ExPre.specR_callApp (C := ctxH C H2) (ctxOK_H hok H2) hc.app ipA2 (vv ipA) (vv ipR) oa (acc.map Enc.idxW)
      (Enc.idxW r) (by decide) (blkAt_mono hb hp1) (by simp +decide [Env.get, ipParams, ctxEnv]; rfl) (by simp)
      (fun H3 o3 hp3 hb3 => ?_)
    have hb3' : BlkAt H3 o3 ((acc ++ [r]).map Enc.idxW) := by simpa using hb3
    refine specR_congr (m' := (instSpinePins lps us args rP pins >>= fun xs => pure ((acc ++ [r]) ++ xs)) >>= fun y =>
      pure y) (by simp) ?_
    refine specR_callNIH (C := ctxH C H3) ipX fIp ipParams
      [.op .add [vv ipS, .const 8], .op .sub [vv ipN, .const 1], vv ipK, vv ipU, vv ipT, vv ipRp, vv ipA2] ipBody
      [ecell C (qs + 1), BitVec.ofNat 64 pins.length, cellA C ok, Enc.idxW us, cellA C ot, BitVec.ofNat 64 rP,
        cellA C o3] (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get, ipParams, ctxEnv]; exact ecell_add8 C qs,
        by simp +decide [sev, Env.get, ipParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _,
        by simp +decide [Env.get, ipParams, ctxEnv] <;> rfl, by simp +decide [Env.get, ipParams, ctxEnv],
        by simp +decide [Env.get, ipParams, ctxEnv] <;> rfl, by simp +decide [Env.get, ipParams, ctxEnv],
        by simp <;> rfl, trivial⟩
      (PostA (ctxH C H3)) (fun a w _ H4 => ∃ o4, w = cellA C o4 ∧ BlkAt H4 o4 (a.map Enc.idxW))
      (fun a w s' st ⟨H4, o4, hp4, hw, hb4, hsr⟩ => ⟨H4, hp4, ⟨o4, hw, hb4⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ipParams _ rfl hlk)
        (ih (qs + 1) H3 (acc ++ [r]) o3 s2 (hp.trans (hp1.trans hp3)) (fun x hx => hsub x (by simp [hx]))
          (fun j hj => by have h' := hsrc (j + 1) (by simp; omega); rw [show qs + (j + 1) = qs + 1 + j by omega] at h'; simpa using h')
          hb3' (blkAt_mono hko (hp1.trans hp3)) (blkAt_mono hbt (hp1.trans hp3)) hq2 (by simp at hlen; omega)))
      (fun res w s4 H4 hp4 ⟨o4, hw, hb4⟩ => ?_)
    subst hw
    exact specR_returnI _ (cellA C o4) (by simp)
      (fun t ht => ⟨H4, o4, hp1.trans (hp3.trans hp4), rfl, by simpa using hb4, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
