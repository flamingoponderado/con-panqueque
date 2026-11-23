import ConPanqueque.T.Core.StructEtaArms
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `stuckIrrel`: the fallbacks for structurally distinct stuck terms

Structure η both ways, unit-likeness, proof irrelevance. `structUnitCert` (function `fSuc`, any body `sB`
refining it) is a callee here; its port is separate.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def siA := ofString "sti_sia"
def siB := ofString "sti_sib"
def siX := ofString "sti_six"
def siY := ofString "sti_siy"
def siZ := ofString "sti_siz"
def siR := ofString "sti_sir"
def fSi := ofString "stuckIrrel"
def fSuc := ofString "structUnitCert"
def sucParams : List MlS := [kFu, kD, ofString "suc_a", ofString "suc_b"]

@[simp] theorem sti_siA_ne_siB : siA ≠ siB := by decide
@[simp] theorem sti_siA_ne_siX : siA ≠ siX := by decide
@[simp] theorem sti_siA_ne_siY : siA ≠ siY := by decide
@[simp] theorem sti_siA_ne_siZ : siA ≠ siZ := by decide
@[simp] theorem sti_siA_ne_siR : siA ≠ siR := by decide
@[simp] theorem sti_siA_ne_lFl : siA ≠ lFl := by decide
@[simp] theorem sti_lFl_ne_siA : lFl ≠ siA := by decide
@[simp] theorem sti_siA_ne_lDh : siA ≠ lDh := by decide
@[simp] theorem sti_lDh_ne_siA : lDh ≠ siA := by decide
@[simp] theorem sti_siA_ne_lDt : siA ≠ lDt := by decide
@[simp] theorem sti_lDt_ne_siA : lDt ≠ siA := by decide
@[simp] theorem sti_siA_ne_lDg : siA ≠ lDg := by decide
@[simp] theorem sti_lDg_ne_siA : lDg ≠ siA := by decide
@[simp] theorem sti_siA_ne_lDi : siA ≠ lDi := by decide
@[simp] theorem sti_lDi_ne_siA : lDi ≠ siA := by decide
@[simp] theorem sti_siA_ne_lRp : siA ≠ lRp := by decide
@[simp] theorem sti_lRp_ne_siA : lRp ≠ siA := by decide
@[simp] theorem sti_siA_ne_lRn : siA ≠ lRn := by decide
@[simp] theorem sti_lRn_ne_siA : lRn ≠ siA := by decide
@[simp] theorem sti_siA_ne_lFle : siA ≠ lFle := by decide
@[simp] theorem sti_lFle_ne_siA : lFle ≠ siA := by decide
@[simp] theorem sti_siA_ne_lKb : siA ≠ lKb := by decide
@[simp] theorem sti_lKb_ne_siA : lKb ≠ siA := by decide
@[simp] theorem sti_siA_ne_lDir : siA ≠ lDir := by decide
@[simp] theorem sti_lDir_ne_siA : lDir ≠ siA := by decide
@[simp] theorem sti_siA_ne_lFln : siA ≠ lFln := by decide
@[simp] theorem sti_lFln_ne_siA : lFln ≠ siA := by decide
@[simp] theorem sti_siA_ne_lFll : siA ≠ lFll := by decide
@[simp] theorem sti_lFll_ne_siA : lFll ≠ siA := by decide
@[simp] theorem sti_siA_ne_lFls : siA ≠ lFls := by decide
@[simp] theorem sti_lFls_ne_siA : lFls ≠ siA := by decide
@[simp] theorem sti_siA_ne_kFu : siA ≠ kFu := by decide
@[simp] theorem sti_kFu_ne_siA : kFu ≠ siA := by decide
@[simp] theorem sti_siA_ne_kD : siA ≠ kD := by decide
@[simp] theorem sti_kD_ne_siA : kD ≠ siA := by decide
@[simp] theorem sti_siB_ne_siA : siB ≠ siA := by decide
@[simp] theorem sti_siB_ne_siX : siB ≠ siX := by decide
@[simp] theorem sti_siB_ne_siY : siB ≠ siY := by decide
@[simp] theorem sti_siB_ne_siZ : siB ≠ siZ := by decide
@[simp] theorem sti_siB_ne_siR : siB ≠ siR := by decide
@[simp] theorem sti_siB_ne_lFl : siB ≠ lFl := by decide
@[simp] theorem sti_lFl_ne_siB : lFl ≠ siB := by decide
@[simp] theorem sti_siB_ne_lDh : siB ≠ lDh := by decide
@[simp] theorem sti_lDh_ne_siB : lDh ≠ siB := by decide
@[simp] theorem sti_siB_ne_lDt : siB ≠ lDt := by decide
@[simp] theorem sti_lDt_ne_siB : lDt ≠ siB := by decide
@[simp] theorem sti_siB_ne_lDg : siB ≠ lDg := by decide
@[simp] theorem sti_lDg_ne_siB : lDg ≠ siB := by decide
@[simp] theorem sti_siB_ne_lDi : siB ≠ lDi := by decide
@[simp] theorem sti_lDi_ne_siB : lDi ≠ siB := by decide
@[simp] theorem sti_siB_ne_lRp : siB ≠ lRp := by decide
@[simp] theorem sti_lRp_ne_siB : lRp ≠ siB := by decide
@[simp] theorem sti_siB_ne_lRn : siB ≠ lRn := by decide
@[simp] theorem sti_lRn_ne_siB : lRn ≠ siB := by decide
@[simp] theorem sti_siB_ne_lFle : siB ≠ lFle := by decide
@[simp] theorem sti_lFle_ne_siB : lFle ≠ siB := by decide
@[simp] theorem sti_siB_ne_lKb : siB ≠ lKb := by decide
@[simp] theorem sti_lKb_ne_siB : lKb ≠ siB := by decide
@[simp] theorem sti_siB_ne_lDir : siB ≠ lDir := by decide
@[simp] theorem sti_lDir_ne_siB : lDir ≠ siB := by decide
@[simp] theorem sti_siB_ne_lFln : siB ≠ lFln := by decide
@[simp] theorem sti_lFln_ne_siB : lFln ≠ siB := by decide
@[simp] theorem sti_siB_ne_lFll : siB ≠ lFll := by decide
@[simp] theorem sti_lFll_ne_siB : lFll ≠ siB := by decide
@[simp] theorem sti_siB_ne_lFls : siB ≠ lFls := by decide
@[simp] theorem sti_lFls_ne_siB : lFls ≠ siB := by decide
@[simp] theorem sti_siB_ne_kFu : siB ≠ kFu := by decide
@[simp] theorem sti_kFu_ne_siB : kFu ≠ siB := by decide
@[simp] theorem sti_siB_ne_kD : siB ≠ kD := by decide
@[simp] theorem sti_kD_ne_siB : kD ≠ siB := by decide
@[simp] theorem sti_siX_ne_siA : siX ≠ siA := by decide
@[simp] theorem sti_siX_ne_siB : siX ≠ siB := by decide
@[simp] theorem sti_siX_ne_siY : siX ≠ siY := by decide
@[simp] theorem sti_siX_ne_siZ : siX ≠ siZ := by decide
@[simp] theorem sti_siX_ne_siR : siX ≠ siR := by decide
@[simp] theorem sti_siX_ne_lFl : siX ≠ lFl := by decide
@[simp] theorem sti_lFl_ne_siX : lFl ≠ siX := by decide
@[simp] theorem sti_siX_ne_lDh : siX ≠ lDh := by decide
@[simp] theorem sti_lDh_ne_siX : lDh ≠ siX := by decide
@[simp] theorem sti_siX_ne_lDt : siX ≠ lDt := by decide
@[simp] theorem sti_lDt_ne_siX : lDt ≠ siX := by decide
@[simp] theorem sti_siX_ne_lDg : siX ≠ lDg := by decide
@[simp] theorem sti_lDg_ne_siX : lDg ≠ siX := by decide
@[simp] theorem sti_siX_ne_lDi : siX ≠ lDi := by decide
@[simp] theorem sti_lDi_ne_siX : lDi ≠ siX := by decide
@[simp] theorem sti_siX_ne_lRp : siX ≠ lRp := by decide
@[simp] theorem sti_lRp_ne_siX : lRp ≠ siX := by decide
@[simp] theorem sti_siX_ne_lRn : siX ≠ lRn := by decide
@[simp] theorem sti_lRn_ne_siX : lRn ≠ siX := by decide
@[simp] theorem sti_siX_ne_lFle : siX ≠ lFle := by decide
@[simp] theorem sti_lFle_ne_siX : lFle ≠ siX := by decide
@[simp] theorem sti_siX_ne_lKb : siX ≠ lKb := by decide
@[simp] theorem sti_lKb_ne_siX : lKb ≠ siX := by decide
@[simp] theorem sti_siX_ne_lDir : siX ≠ lDir := by decide
@[simp] theorem sti_lDir_ne_siX : lDir ≠ siX := by decide
@[simp] theorem sti_siX_ne_lFln : siX ≠ lFln := by decide
@[simp] theorem sti_lFln_ne_siX : lFln ≠ siX := by decide
@[simp] theorem sti_siX_ne_lFll : siX ≠ lFll := by decide
@[simp] theorem sti_lFll_ne_siX : lFll ≠ siX := by decide
@[simp] theorem sti_siX_ne_lFls : siX ≠ lFls := by decide
@[simp] theorem sti_lFls_ne_siX : lFls ≠ siX := by decide
@[simp] theorem sti_siX_ne_kFu : siX ≠ kFu := by decide
@[simp] theorem sti_kFu_ne_siX : kFu ≠ siX := by decide
@[simp] theorem sti_siX_ne_kD : siX ≠ kD := by decide
@[simp] theorem sti_kD_ne_siX : kD ≠ siX := by decide
@[simp] theorem sti_siY_ne_siA : siY ≠ siA := by decide
@[simp] theorem sti_siY_ne_siB : siY ≠ siB := by decide
@[simp] theorem sti_siY_ne_siX : siY ≠ siX := by decide
@[simp] theorem sti_siY_ne_siZ : siY ≠ siZ := by decide
@[simp] theorem sti_siY_ne_siR : siY ≠ siR := by decide
@[simp] theorem sti_siY_ne_lFl : siY ≠ lFl := by decide
@[simp] theorem sti_lFl_ne_siY : lFl ≠ siY := by decide
@[simp] theorem sti_siY_ne_lDh : siY ≠ lDh := by decide
@[simp] theorem sti_lDh_ne_siY : lDh ≠ siY := by decide
@[simp] theorem sti_siY_ne_lDt : siY ≠ lDt := by decide
@[simp] theorem sti_lDt_ne_siY : lDt ≠ siY := by decide
@[simp] theorem sti_siY_ne_lDg : siY ≠ lDg := by decide
@[simp] theorem sti_lDg_ne_siY : lDg ≠ siY := by decide
@[simp] theorem sti_siY_ne_lDi : siY ≠ lDi := by decide
@[simp] theorem sti_lDi_ne_siY : lDi ≠ siY := by decide
@[simp] theorem sti_siY_ne_lRp : siY ≠ lRp := by decide
@[simp] theorem sti_lRp_ne_siY : lRp ≠ siY := by decide
@[simp] theorem sti_siY_ne_lRn : siY ≠ lRn := by decide
@[simp] theorem sti_lRn_ne_siY : lRn ≠ siY := by decide
@[simp] theorem sti_siY_ne_lFle : siY ≠ lFle := by decide
@[simp] theorem sti_lFle_ne_siY : lFle ≠ siY := by decide
@[simp] theorem sti_siY_ne_lKb : siY ≠ lKb := by decide
@[simp] theorem sti_lKb_ne_siY : lKb ≠ siY := by decide
@[simp] theorem sti_siY_ne_lDir : siY ≠ lDir := by decide
@[simp] theorem sti_lDir_ne_siY : lDir ≠ siY := by decide
@[simp] theorem sti_siY_ne_lFln : siY ≠ lFln := by decide
@[simp] theorem sti_lFln_ne_siY : lFln ≠ siY := by decide
@[simp] theorem sti_siY_ne_lFll : siY ≠ lFll := by decide
@[simp] theorem sti_lFll_ne_siY : lFll ≠ siY := by decide
@[simp] theorem sti_siY_ne_lFls : siY ≠ lFls := by decide
@[simp] theorem sti_lFls_ne_siY : lFls ≠ siY := by decide
@[simp] theorem sti_siY_ne_kFu : siY ≠ kFu := by decide
@[simp] theorem sti_kFu_ne_siY : kFu ≠ siY := by decide
@[simp] theorem sti_siY_ne_kD : siY ≠ kD := by decide
@[simp] theorem sti_kD_ne_siY : kD ≠ siY := by decide
@[simp] theorem sti_siZ_ne_siA : siZ ≠ siA := by decide
@[simp] theorem sti_siZ_ne_siB : siZ ≠ siB := by decide
@[simp] theorem sti_siZ_ne_siX : siZ ≠ siX := by decide
@[simp] theorem sti_siZ_ne_siY : siZ ≠ siY := by decide
@[simp] theorem sti_siZ_ne_siR : siZ ≠ siR := by decide
@[simp] theorem sti_siZ_ne_lFl : siZ ≠ lFl := by decide
@[simp] theorem sti_lFl_ne_siZ : lFl ≠ siZ := by decide
@[simp] theorem sti_siZ_ne_lDh : siZ ≠ lDh := by decide
@[simp] theorem sti_lDh_ne_siZ : lDh ≠ siZ := by decide
@[simp] theorem sti_siZ_ne_lDt : siZ ≠ lDt := by decide
@[simp] theorem sti_lDt_ne_siZ : lDt ≠ siZ := by decide
@[simp] theorem sti_siZ_ne_lDg : siZ ≠ lDg := by decide
@[simp] theorem sti_lDg_ne_siZ : lDg ≠ siZ := by decide
@[simp] theorem sti_siZ_ne_lDi : siZ ≠ lDi := by decide
@[simp] theorem sti_lDi_ne_siZ : lDi ≠ siZ := by decide
@[simp] theorem sti_siZ_ne_lRp : siZ ≠ lRp := by decide
@[simp] theorem sti_lRp_ne_siZ : lRp ≠ siZ := by decide
@[simp] theorem sti_siZ_ne_lRn : siZ ≠ lRn := by decide
@[simp] theorem sti_lRn_ne_siZ : lRn ≠ siZ := by decide
@[simp] theorem sti_siZ_ne_lFle : siZ ≠ lFle := by decide
@[simp] theorem sti_lFle_ne_siZ : lFle ≠ siZ := by decide
@[simp] theorem sti_siZ_ne_lKb : siZ ≠ lKb := by decide
@[simp] theorem sti_lKb_ne_siZ : lKb ≠ siZ := by decide
@[simp] theorem sti_siZ_ne_lDir : siZ ≠ lDir := by decide
@[simp] theorem sti_lDir_ne_siZ : lDir ≠ siZ := by decide
@[simp] theorem sti_siZ_ne_lFln : siZ ≠ lFln := by decide
@[simp] theorem sti_lFln_ne_siZ : lFln ≠ siZ := by decide
@[simp] theorem sti_siZ_ne_lFll : siZ ≠ lFll := by decide
@[simp] theorem sti_lFll_ne_siZ : lFll ≠ siZ := by decide
@[simp] theorem sti_siZ_ne_lFls : siZ ≠ lFls := by decide
@[simp] theorem sti_lFls_ne_siZ : lFls ≠ siZ := by decide
@[simp] theorem sti_siZ_ne_kFu : siZ ≠ kFu := by decide
@[simp] theorem sti_kFu_ne_siZ : kFu ≠ siZ := by decide
@[simp] theorem sti_siZ_ne_kD : siZ ≠ kD := by decide
@[simp] theorem sti_kD_ne_siZ : kD ≠ siZ := by decide
@[simp] theorem sti_siR_ne_siA : siR ≠ siA := by decide
@[simp] theorem sti_siR_ne_siB : siR ≠ siB := by decide
@[simp] theorem sti_siR_ne_siX : siR ≠ siX := by decide
@[simp] theorem sti_siR_ne_siY : siR ≠ siY := by decide
@[simp] theorem sti_siR_ne_siZ : siR ≠ siZ := by decide
@[simp] theorem sti_siR_ne_lFl : siR ≠ lFl := by decide
@[simp] theorem sti_lFl_ne_siR : lFl ≠ siR := by decide
@[simp] theorem sti_siR_ne_lDh : siR ≠ lDh := by decide
@[simp] theorem sti_lDh_ne_siR : lDh ≠ siR := by decide
@[simp] theorem sti_siR_ne_lDt : siR ≠ lDt := by decide
@[simp] theorem sti_lDt_ne_siR : lDt ≠ siR := by decide
@[simp] theorem sti_siR_ne_lDg : siR ≠ lDg := by decide
@[simp] theorem sti_lDg_ne_siR : lDg ≠ siR := by decide
@[simp] theorem sti_siR_ne_lDi : siR ≠ lDi := by decide
@[simp] theorem sti_lDi_ne_siR : lDi ≠ siR := by decide
@[simp] theorem sti_siR_ne_lRp : siR ≠ lRp := by decide
@[simp] theorem sti_lRp_ne_siR : lRp ≠ siR := by decide
@[simp] theorem sti_siR_ne_lRn : siR ≠ lRn := by decide
@[simp] theorem sti_lRn_ne_siR : lRn ≠ siR := by decide
@[simp] theorem sti_siR_ne_lFle : siR ≠ lFle := by decide
@[simp] theorem sti_lFle_ne_siR : lFle ≠ siR := by decide
@[simp] theorem sti_siR_ne_lKb : siR ≠ lKb := by decide
@[simp] theorem sti_lKb_ne_siR : lKb ≠ siR := by decide
@[simp] theorem sti_siR_ne_lDir : siR ≠ lDir := by decide
@[simp] theorem sti_lDir_ne_siR : lDir ≠ siR := by decide
@[simp] theorem sti_siR_ne_lFln : siR ≠ lFln := by decide
@[simp] theorem sti_lFln_ne_siR : lFln ≠ siR := by decide
@[simp] theorem sti_siR_ne_lFll : siR ≠ lFll := by decide
@[simp] theorem sti_lFll_ne_siR : lFll ≠ siR := by decide
@[simp] theorem sti_siR_ne_lFls : siR ≠ lFls := by decide
@[simp] theorem sti_lFls_ne_siR : lFls ≠ siR := by decide
@[simp] theorem sti_siR_ne_kFu : siR ≠ kFu := by decide
@[simp] theorem sti_kFu_ne_siR : kFu ≠ siR := by decide
@[simp] theorem sti_siR_ne_kD : siR ≠ kD := by decide
@[simp] theorem sti_kD_ne_siR : kD ≠ siR := by decide

def siParams : List MlS := [kFu, kD, siA, siB]
def siBody : ProgHOL 64 := prologue [siX, siY, siZ, siR] (.seq (.call (some (some (.local, siX), none)) fSc [(vv kFu), (vv kD), (vv siA), (vv siB)]) (.ite (vv siX) (.return (.const 1)) (.seq (.call (some (some (.local, siY), none)) fSc [(vv kFu), (vv kD), (vv siB), (vv siA)]) (.ite (vv siY) (.return (.const 1)) (.seq (.call (some (some (.local, siZ), none)) fSuc [(vv kFu), (vv kD), (vv siA), (vv siB)]) (.ite (vv siZ) (.return (.const 1)) (.seq (.call (some (some (.local, siR), none)) fPi [(vv kFu), (vv kD), (vv siA), (vv siB)]) (.return (vv siR)))))))))

structure SiCodes (C : Ctx) (sB : ProgHOL 64) : Prop where
  sc : C.code.lookup fSc = some (ccParams.map (fun p => (p, ShapeHOL.one)), ccBody, .one)
  su : C.code.lookup fSuc = some (sucParams.map (fun p => (p, ShapeHOL.one)), sB, .one)
  pi : C.code.lookup fPi = some (piParams.map (fun p => (p, ShapeHOL.one)), piBody C, .one)

section
variable {σ : Type}

theorem si_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) (sB : ProgHOL 64) (hc : SiCodes C sB)
    (hSC : ∀ (H : List (BitVec 64)) s1 d a b, C.H <+: H → d < 2 ^ 63 → SpecR (σ := σ) (Pre (ctxH C H) s1 (ccParams.zip
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b])) ccBody s1
      (structEtaCert (knot mode C n) C.fe d a b) (PostB (ctxH C H)))
    (hSU : ∀ (H : List (BitVec 64)) s1 d a b, C.H <+: H → d < 2 ^ 63 → SpecR (σ := σ) (Pre (ctxH C H) s1 (sucParams.zip
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b])) sB s1
      (structUnitCert (knot mode C n) C.fe d a b) (PostB (ctxH C H)))
    (hPI : ∀ (H : List (BitVec 64)) s1 d a b, C.H <+: H → d < 2 ^ 63 → SpecR (σ := σ) (Pre (ctxH C H) s1 (piParams.zip
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b])) (piBody C) s1
      (proofIrrel (knot mode C n) C.fe d a b) (PostB (ctxH C H))) :
    ∀ (H : List (BitVec 64)) (s : AState) (d : Nat) (a b : EIdx), C.H <+: H → d < 2 ^ 63 →
      SpecR (σ := σ) (Pre (ctxH C H) s (siParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b]))
        siBody s (stuckIrrel (knot mode C n) C.fe d a b) (PostB (ctxH C H)) := by
  intro H s d a b hpH hdd
  refine specR_prologue (postB_locals _) (Knot.params_none _ [siX, siY, siZ, siR] siParams _ (by decide) (by decide)) ?_
  unfold stuckIrrel
  refine specR_callNIH (C := ctxH C H) siX fSc ccParams [(vv kFu), (vv kD), (vv siA), (vv siB)] ccBody
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (by decide) rfl (by decide) hc.sc
    ⟨by simp +decide [Env.get, siParams, ctxEnv], by simp +decide [Env.get, siParams, ctxEnv], by simp +decide [Env.get, siParams, ctxEnv], by simp +decide [Env.get, siParams, ctxEnv], trivial⟩
    (PostB (ctxH C H)) (fun r_ w _ _ => w = boolW r_) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ccParams _ rfl hlk) (hSC H s d a b hpH hdd))
    (fun x w1 s1 H1 hp1 hw1 => ?_)
  subst hw1
  cases x
  swap
  · refine specR_ifI _ 1 (by simp [boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [↓reduceIte]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 0 (by simp [boolW]) (fun h => absurd rfl h) (fun _ => ?_)
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine specR_callNIH (C := ctxH C H1) siY fSc ccParams [(vv kFu), (vv kD), (vv siB), (vv siA)] ccBody
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW b, Enc.idxW a] (by decide) rfl (by decide) hc.sc
    ⟨by simp +decide [Env.get, siParams, ctxEnv], by simp +decide [Env.get, siParams, ctxEnv], by simp +decide [Env.get, siParams, ctxEnv], by simp +decide [Env.get, siParams, ctxEnv], trivial⟩
    (PostB (ctxH C H1)) (fun r_ w _ _ => w = boolW r_) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ccParams _ rfl hlk) (hSC H1 s1 d b a (hpH.trans hp1) hdd))
    (fun y w2 s2 H2 hp2 hw2 => ?_)
  subst hw2
  cases y
  swap
  · refine specR_ifI _ 1 (by simp [boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [↓reduceIte]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H2, hp1.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 0 (by simp [boolW]) (fun h => absurd rfl h) (fun _ => ?_)
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine specR_callNIH (C := ctxH C H2) siZ fSuc sucParams [(vv kFu), (vv kD), (vv siA), (vv siB)] sB
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (by decide) rfl (by decide) hc.su
    ⟨by simp +decide [Env.get, siParams, ctxEnv], by simp +decide [Env.get, siParams, ctxEnv], by simp +decide [Env.get, siParams, ctxEnv], by simp +decide [Env.get, siParams, ctxEnv], trivial⟩
    (PostB (ctxH C H2)) (fun r_ w _ _ => w = boolW r_) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu sucParams _ rfl hlk) (hSU H2 s2 d a b (hpH.trans (hp1.trans hp2)) hdd))
    (fun z w3 s3 H3 hp3 hw3 => ?_)
  subst hw3
  cases z
  swap
  · refine specR_ifI _ 1 (by simp [boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [↓reduceIte]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H3, hp1.trans (hp2.trans hp3), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 0 (by simp [boolW]) (fun h => absurd rfl h) (fun _ => ?_)
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine specR_congr (m' := proofIrrel (knot mode C n) C.fe d a b >>= fun r => pure r) (by simp) ?_
  refine specR_callNIH (C := ctxH C H3) siR fPi piParams [(vv kFu), (vv kD), (vv siA), (vv siB)] (piBody C)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (by decide) rfl (by decide) hc.pi
    ⟨by simp +decide [Env.get, siParams, ctxEnv], by simp +decide [Env.get, siParams, ctxEnv], by simp +decide [Env.get, siParams, ctxEnv], by simp +decide [Env.get, siParams, ctxEnv], trivial⟩
    (PostB (ctxH C H3)) (fun r_ w _ _ => w = boolW r_) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu piParams _ rfl hlk) (hPI H3 s3 d a b (hpH.trans (hp1.trans (hp2.trans hp3))) hdd))
    (fun r w4 s4 H4 hp4 hw4 => ?_)
  subst hw4
  exact specR_returnI _ (boolW r) (by simp) (fun t ht => ⟨H4, hp1.trans (hp2.trans (hp3.trans hp4)), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
