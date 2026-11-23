import ConPanqueque.T.Core.ProofPW
import ConPanqueque.T.Core.ProofIrrel
import ConPanqueque.T.Core.DefeqLazy
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `propIrrel`: the hoisted proof-irrelevance test

Both fast "not a proof" reads, then both fast "is a proof" reads (each pair evaluated in full, as the twin's lifted
binds are), then the inference route `proofIrrel`.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc
open ConLeche (Level Name)

def priX := ofString "ppri_prix"
def priY := ofString "ppri_priy"
def priR := ofString "ppri_prir"

@[simp] theorem ppri_priX_ne_priY : priX ≠ priY := by decide
@[simp] theorem ppri_priX_ne_priR : priX ≠ priR := by decide
@[simp] theorem ppri_priX_ne_lFl : priX ≠ lFl := by decide
@[simp] theorem ppri_lFl_ne_priX : lFl ≠ priX := by decide
@[simp] theorem ppri_priX_ne_lDh : priX ≠ lDh := by decide
@[simp] theorem ppri_lDh_ne_priX : lDh ≠ priX := by decide
@[simp] theorem ppri_priX_ne_lDt : priX ≠ lDt := by decide
@[simp] theorem ppri_lDt_ne_priX : lDt ≠ priX := by decide
@[simp] theorem ppri_priX_ne_lDg : priX ≠ lDg := by decide
@[simp] theorem ppri_lDg_ne_priX : lDg ≠ priX := by decide
@[simp] theorem ppri_priX_ne_lDi : priX ≠ lDi := by decide
@[simp] theorem ppri_lDi_ne_priX : lDi ≠ priX := by decide
@[simp] theorem ppri_priX_ne_lRp : priX ≠ lRp := by decide
@[simp] theorem ppri_lRp_ne_priX : lRp ≠ priX := by decide
@[simp] theorem ppri_priX_ne_lRn : priX ≠ lRn := by decide
@[simp] theorem ppri_lRn_ne_priX : lRn ≠ priX := by decide
@[simp] theorem ppri_priX_ne_lFle : priX ≠ lFle := by decide
@[simp] theorem ppri_lFle_ne_priX : lFle ≠ priX := by decide
@[simp] theorem ppri_priX_ne_lKb : priX ≠ lKb := by decide
@[simp] theorem ppri_lKb_ne_priX : lKb ≠ priX := by decide
@[simp] theorem ppri_priX_ne_lDir : priX ≠ lDir := by decide
@[simp] theorem ppri_lDir_ne_priX : lDir ≠ priX := by decide
@[simp] theorem ppri_priX_ne_lFln : priX ≠ lFln := by decide
@[simp] theorem ppri_lFln_ne_priX : lFln ≠ priX := by decide
@[simp] theorem ppri_priX_ne_lFll : priX ≠ lFll := by decide
@[simp] theorem ppri_lFll_ne_priX : lFll ≠ priX := by decide
@[simp] theorem ppri_priX_ne_lFls : priX ≠ lFls := by decide
@[simp] theorem ppri_lFls_ne_priX : lFls ≠ priX := by decide
@[simp] theorem ppri_priX_ne_kFu : priX ≠ kFu := by decide
@[simp] theorem ppri_kFu_ne_priX : kFu ≠ priX := by decide
@[simp] theorem ppri_priX_ne_kD : priX ≠ kD := by decide
@[simp] theorem ppri_kD_ne_priX : kD ≠ priX := by decide
@[simp] theorem ppri_priY_ne_priX : priY ≠ priX := by decide
@[simp] theorem ppri_priY_ne_priR : priY ≠ priR := by decide
@[simp] theorem ppri_priY_ne_lFl : priY ≠ lFl := by decide
@[simp] theorem ppri_lFl_ne_priY : lFl ≠ priY := by decide
@[simp] theorem ppri_priY_ne_lDh : priY ≠ lDh := by decide
@[simp] theorem ppri_lDh_ne_priY : lDh ≠ priY := by decide
@[simp] theorem ppri_priY_ne_lDt : priY ≠ lDt := by decide
@[simp] theorem ppri_lDt_ne_priY : lDt ≠ priY := by decide
@[simp] theorem ppri_priY_ne_lDg : priY ≠ lDg := by decide
@[simp] theorem ppri_lDg_ne_priY : lDg ≠ priY := by decide
@[simp] theorem ppri_priY_ne_lDi : priY ≠ lDi := by decide
@[simp] theorem ppri_lDi_ne_priY : lDi ≠ priY := by decide
@[simp] theorem ppri_priY_ne_lRp : priY ≠ lRp := by decide
@[simp] theorem ppri_lRp_ne_priY : lRp ≠ priY := by decide
@[simp] theorem ppri_priY_ne_lRn : priY ≠ lRn := by decide
@[simp] theorem ppri_lRn_ne_priY : lRn ≠ priY := by decide
@[simp] theorem ppri_priY_ne_lFle : priY ≠ lFle := by decide
@[simp] theorem ppri_lFle_ne_priY : lFle ≠ priY := by decide
@[simp] theorem ppri_priY_ne_lKb : priY ≠ lKb := by decide
@[simp] theorem ppri_lKb_ne_priY : lKb ≠ priY := by decide
@[simp] theorem ppri_priY_ne_lDir : priY ≠ lDir := by decide
@[simp] theorem ppri_lDir_ne_priY : lDir ≠ priY := by decide
@[simp] theorem ppri_priY_ne_lFln : priY ≠ lFln := by decide
@[simp] theorem ppri_lFln_ne_priY : lFln ≠ priY := by decide
@[simp] theorem ppri_priY_ne_lFll : priY ≠ lFll := by decide
@[simp] theorem ppri_lFll_ne_priY : lFll ≠ priY := by decide
@[simp] theorem ppri_priY_ne_lFls : priY ≠ lFls := by decide
@[simp] theorem ppri_lFls_ne_priY : lFls ≠ priY := by decide
@[simp] theorem ppri_priY_ne_kFu : priY ≠ kFu := by decide
@[simp] theorem ppri_kFu_ne_priY : kFu ≠ priY := by decide
@[simp] theorem ppri_priY_ne_kD : priY ≠ kD := by decide
@[simp] theorem ppri_kD_ne_priY : kD ≠ priY := by decide
@[simp] theorem ppri_priR_ne_priX : priR ≠ priX := by decide
@[simp] theorem ppri_priR_ne_priY : priR ≠ priY := by decide
@[simp] theorem ppri_priR_ne_lFl : priR ≠ lFl := by decide
@[simp] theorem ppri_lFl_ne_priR : lFl ≠ priR := by decide
@[simp] theorem ppri_priR_ne_lDh : priR ≠ lDh := by decide
@[simp] theorem ppri_lDh_ne_priR : lDh ≠ priR := by decide
@[simp] theorem ppri_priR_ne_lDt : priR ≠ lDt := by decide
@[simp] theorem ppri_lDt_ne_priR : lDt ≠ priR := by decide
@[simp] theorem ppri_priR_ne_lDg : priR ≠ lDg := by decide
@[simp] theorem ppri_lDg_ne_priR : lDg ≠ priR := by decide
@[simp] theorem ppri_priR_ne_lDi : priR ≠ lDi := by decide
@[simp] theorem ppri_lDi_ne_priR : lDi ≠ priR := by decide
@[simp] theorem ppri_priR_ne_lRp : priR ≠ lRp := by decide
@[simp] theorem ppri_lRp_ne_priR : lRp ≠ priR := by decide
@[simp] theorem ppri_priR_ne_lRn : priR ≠ lRn := by decide
@[simp] theorem ppri_lRn_ne_priR : lRn ≠ priR := by decide
@[simp] theorem ppri_priR_ne_lFle : priR ≠ lFle := by decide
@[simp] theorem ppri_lFle_ne_priR : lFle ≠ priR := by decide
@[simp] theorem ppri_priR_ne_lKb : priR ≠ lKb := by decide
@[simp] theorem ppri_lKb_ne_priR : lKb ≠ priR := by decide
@[simp] theorem ppri_priR_ne_lDir : priR ≠ lDir := by decide
@[simp] theorem ppri_lDir_ne_priR : lDir ≠ priR := by decide
@[simp] theorem ppri_priR_ne_lFln : priR ≠ lFln := by decide
@[simp] theorem ppri_lFln_ne_priR : lFln ≠ priR := by decide
@[simp] theorem ppri_priR_ne_lFll : priR ≠ lFll := by decide
@[simp] theorem ppri_lFll_ne_priR : lFll ≠ priR := by decide
@[simp] theorem ppri_priR_ne_lFls : priR ≠ lFls := by decide
@[simp] theorem ppri_lFls_ne_priR : lFls ≠ priR := by decide
@[simp] theorem ppri_priR_ne_kFu : priR ≠ kFu := by decide
@[simp] theorem ppri_kFu_ne_priR : kFu ≠ priR := by decide
@[simp] theorem ppri_priR_ne_kD : priR ≠ kD := by decide
@[simp] theorem ppri_kD_ne_priR : kD ≠ priR := by decide

def priLocals : List MlS := [priX, priY, priR]
def priBody (C : Ctx) : ProgHOL 64 := prologue priLocals (.seq (.call (some (some (.local, priX), none)) fNpf [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv (ofString "pri_a"))]) (.seq (.call (some (some (.local, priY), none)) fNpf [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv (ofString "pri_b"))]) (.ite (.op .or [vv priX, vv priY]) (.return (.const 0)) (.seq (.call (some (some (.local, priX), none)) fIpf [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv (ofString "pri_a"))]) (.seq (.call (some (some (.local, priY), none)) fIpf [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv (ofString "pri_b"))]) (.ite (.op .and [vv priX, vv priY]) (.return (.const 1)) (.seq (.call (some (some (.local, priR), none)) fPi [(vv kFu), (vv kD), (vv (ofString "pri_a")), (vv (ofString "pri_b"))]) (.return (vv priR)))))))))

structure PriCodes (C : Ctx) : Prop where
  np : C.code.lookup fNpf = some (npfParams.map (fun p => (p, ShapeHOL.one)), npfBody C, .one)
  ip : C.code.lookup fIpf = some (ipfParams.map (fun p => (p, ShapeHOL.one)), ipfBody C, .one)
  ipc : IpfCodes C
  pi : C.code.lookup fPi = some (piParams.map (fun p => (p, ShapeHOL.one)), piBody C, .one)
  io : C.code.lookup fIO = some (pmap kParams, inferIOE C fIOB, .one)
  w : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one)
  e : C.code.lookup LLeq.fEqv = some ([(LEq.pLa, .one), (LEq.pLb, .one)], LLeq.eqvBody, .one)

section
variable {σ : Type}

theorem pri_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) (hok : CtxOK C) (hc : PriCodes C) (s : AState)
    (hwf : LStoreWF s.store.ls) (hrd : RdOK s)
    (hSD : ∀ h u, s.store.view h = some (.sort u) → ∃ l, denoteL s.store.ls u = some l)
    (hLP : ∀ c ci, C.fe.find? c = some ci → ∃ ks, Frontend.denoteNList s.store.ns ci.toConstantVal.levelParams = some ks)
    (hLPl : ∀ c ci, C.fe.find? c = some ci → ci.toConstantVal.levelParams.length < 2 ^ 60)
    (hLS : ∀ us uh, s.store.lss.view us = some uh → ∃ vs, denoteLs s.store.lss us = some vs ∧ ∃ hl : vs.length = uh.length,
      ∀ j (hj : j < uh.length), denoteL s.store.ls uh[j] = some (vs[j]'(by rw [hl]; exact hj)))
    (hTB : ∀ T tb, C.fe.findTable? T = some tb → tb.bodies.size = tb.numFields) (d : Nat) (a b : EIdx)
    (hIO : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ e', Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e'] (inferIOE C fIOB) s1 ((knot mode C n).inferIO d e')
      (PostK (ctxH C H)))
    (hW : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ e', Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d e')
      (PostK (ctxH C H)))
    (hLE : ∀ (H : List (BitVec 64)) s1 (u v : LIdx), C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s1 [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s1 (lvlEq? u v)
        (LLeq.PostOB (ctxH C H))) :
    ∀ (H : List (BitVec 64)), C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (priParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b]))
        (priBody C) s (propIrrel (knot mode C n) C.fe d a b) (PostB (ctxH C H)) := by
  intro H hpH
  refine specR_prologue (Knot.postB_locals _) (Knot.params_none _ priLocals priParams _ (by decide) (by decide)) ?_
  unfold propIrrel
  refine specR_callNIH (C := ctxH C H) priX fNpf npfParams [(.const (BitVec.ofNat 64 coreWalkFuel)), vv (ofString "pri_a")] (npfBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW a] (by decide) rfl (by decide) hc.np
    ⟨by simp [sev], by simp +decide [Env.get, priParams, ctxEnv], trivial⟩
    (PostRB (ctxH C H) s) (fun b w s' H' => RdStep s s' ∧ w = boolW b)
    (fun b w s' st ⟨hst, hw, H', hp', hsr⟩ => ⟨H', hp', ⟨hst, hw⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu npfParams _ rfl hlk)
      (npf_spec C hok hc.ipc s hwf hrd hSD hLP hLPl hLS hTB coreWalkFuel a H hpH (by decide)))
    (fun x w1 s1 H1 hp1 ⟨hst1, hw1⟩ => ?_)
  have e1 : s1.store = s.store := hst1.1
  have hp01 : C.H <+: H1 := hpH.trans hp1
  refine specR_callNIH (C := ctxH C H1) priY fNpf npfParams [(.const (BitVec.ofNat 64 coreWalkFuel)), vv (ofString "pri_b")] (npfBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW b] (by decide) rfl (by decide) hc.np
    ⟨by simp [sev], by simp +decide [Env.get, priParams, ctxEnv], trivial⟩
    (PostRB (ctxH C H1) s1) (fun b w s' H' => RdStep s1 s' ∧ w = boolW b)
    (fun b w s' st ⟨hst, hw, H', hp', hsr⟩ => ⟨H', hp', ⟨hst, hw⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu npfParams _ rfl hlk)
      (npf_spec C hok hc.ipc s1 (by rw [e1]; exact hwf) hst1.2.2.2.2 (by rw [e1]; exact hSD) (by rw [e1]; exact hLP) hLPl (by rw [e1]; exact hLS) hTB coreWalkFuel b H1 hp01 (by decide)))
    (fun y w2 s2 H2 hp2 ⟨hst2, hw2⟩ => ?_)
  have e2 : s2.store = s.store := hst2.1.trans e1
  have hp02 : C.H <+: H2 := hp01.trans hp2
  subst hw1; subst hw2
  refine specR_ifI _ (boolW x ||| boolW y) (by simp [sev]) (fun hnz => ?_) (fun hz => ?_)
  · have hxy : (x || y) = true := by cases x <;> cases y <;> simp_all [boolW]
    rw [if_pos hxy]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H2, hp1.trans hp2, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  have hxy : ¬ (x || y) = true := by cases x <;> cases y <;> simp_all [boolW]
  rw [if_neg hxy]
  have hst2' : RdStep s s2 := rdStep_trans hst1 hst2
  refine specR_callNIH (C := ctxH C H2) priX fIpf ipfParams [(.const (BitVec.ofNat 64 coreWalkFuel)), vv (ofString "pri_a")] (ipfBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW a] (by decide) rfl (by decide) hc.ip
    ⟨by simp [sev], by simp +decide [Env.get, priParams, ctxEnv], trivial⟩
    (PostRB (ctxH C H2) s2) (fun b w s' H' => RdStep s2 s' ∧ w = boolW b)
    (fun b w s' st ⟨hst, hw, H', hp', hsr⟩ => ⟨H', hp', ⟨hst, hw⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ipfParams _ rfl hlk)
      (ipf_spec C hok hc.ipc s2 (by rw [e2]; exact hwf) hst2'.2.2.2.2 (by rw [e2]; exact hSD) (by rw [e2]; exact hLP) hLPl (by rw [e2]; exact hLS) hTB coreWalkFuel a H2 hp02 (by decide)))
    (fun x' w3 s3 H3 hp3 ⟨hst3, hw3⟩ => ?_)
  have e3 : s3.store = s.store := hst3.1.trans e2
  have hp03 : C.H <+: H3 := hp02.trans hp3
  have hst3' : RdStep s s3 := rdStep_trans hst2' hst3
  refine specR_callNIH (C := ctxH C H3) priY fIpf ipfParams [(.const (BitVec.ofNat 64 coreWalkFuel)), vv (ofString "pri_b")] (ipfBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW b] (by decide) rfl (by decide) hc.ip
    ⟨by simp [sev], by simp +decide [Env.get, priParams, ctxEnv], trivial⟩
    (PostRB (ctxH C H3) s3) (fun b w s' H' => RdStep s3 s' ∧ w = boolW b)
    (fun b w s' st ⟨hst, hw, H', hp', hsr⟩ => ⟨H', hp', ⟨hst, hw⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ipfParams _ rfl hlk)
      (ipf_spec C hok hc.ipc s3 (by rw [e3]; exact hwf) hst3'.2.2.2.2 (by rw [e3]; exact hSD) (by rw [e3]; exact hLP) hLPl (by rw [e3]; exact hLS) hTB coreWalkFuel b H3 hp03 (by decide)))
    (fun y' w4 s4 H4 hp4 ⟨hst4, hw4⟩ => ?_)
  have hp04 : C.H <+: H4 := hp03.trans hp4
  subst hw3; subst hw4
  refine specR_ifI _ (boolW x' &&& boolW y') (by simp [sev]) (fun hnz => ?_) (fun hz => ?_)
  · have hxy' : (x' && y') = true := by cases x' <;> cases y' <;> simp_all [boolW]
    rw [if_pos hxy']
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H4, hp1.trans (hp2.trans (hp3.trans hp4)), by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  have hxy' : ¬ (x' && y') = true := by cases x' <;> cases y' <;> simp_all [boolW]
  rw [if_neg hxy']
  refine specR_congr (m' := proofIrrel (knot mode C n) C.fe d a b >>= fun r => pure r) (by simp [proofIrrel]) ?_
  refine specR_callNIH (C := ctxH C H4) priR fPi piParams [vv kFu, vv kD, vv (ofString "pri_a"), vv (ofString "pri_b")] (piBody C)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (by decide) rfl (by decide) hc.pi
    ⟨by simp +decide [Env.get, priParams, ctxEnv], by simp +decide [Env.get, priParams, ctxEnv], by simp +decide [Env.get, priParams, ctxEnv], by simp +decide [Env.get, priParams, ctxEnv], trivial⟩
    (PostB (ctxH C H4)) (fun b w s' H' => w = boolW b)
    (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu piParams _ rfl hlk)
      (pi_spec mode n (ctxH C H4) (ctxOK_H hok H4) hc.io hc.w hc.e s4 d a b
        (fun H' s' hp e' => hIO H' s' (hp04.trans hp) e') (fun H' s' hp e' => hW H' s' (hp04.trans hp) e')
        (fun H' s' u v hp => hLE H' s' u v (hp04.trans hp))))
    (fun r w s5 H5 hp5 hw => ?_)
  exact specR_returnI _ w (by simp) (fun t ht => ⟨H5, hp1.trans (hp2.trans (hp3.trans (hp4.trans hp5))), hw, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
