import ConPanqueque.T.Core.InferSpine
import ConPanqueque.T.Core.StepApp
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# The application arm's wrapper: `inferApp`

`headAndArgs` (the head and the argument block), the head's type inferred once, then the `inferSpine` walk
from an empty accumulator.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def qaHd := ofString "qan_hd"
def qaVa := ofString "qan_va"
def qaN := ofString "qan_n"
def qaTf := ofString "qan_tf"
def qaE0 := ofString "qan_e0"
def qaR := ofString "qan_r"

@[simp] theorem qa_qaHd_ne_qaVa : qaHd ≠ qaVa := by decide
@[simp] theorem qa_qaHd_ne_qaN : qaHd ≠ qaN := by decide
@[simp] theorem qa_qaHd_ne_qaTf : qaHd ≠ qaTf := by decide
@[simp] theorem qa_qaHd_ne_qaE0 : qaHd ≠ qaE0 := by decide
@[simp] theorem qa_qaHd_ne_qaR : qaHd ≠ qaR := by decide
@[simp] theorem qa_qaHd_ne_kFu : qaHd ≠ kFu := by decide
@[simp] theorem qa_kFu_ne_qaHd : kFu ≠ qaHd := by decide
@[simp] theorem qa_qaHd_ne_kD : qaHd ≠ kD := by decide
@[simp] theorem qa_kD_ne_qaHd : kD ≠ qaHd := by decide
@[simp] theorem qa_qaHd_ne_kE : qaHd ≠ kE := by decide
@[simp] theorem qa_kE_ne_qaHd : kE ≠ qaHd := by decide
@[simp] theorem qa_qaHd_ne_lFl : qaHd ≠ lFl := by decide
@[simp] theorem qa_lFl_ne_qaHd : lFl ≠ qaHd := by decide
@[simp] theorem qa_qaHd_ne_lDh : qaHd ≠ lDh := by decide
@[simp] theorem qa_lDh_ne_qaHd : lDh ≠ qaHd := by decide
@[simp] theorem qa_qaHd_ne_lDt : qaHd ≠ lDt := by decide
@[simp] theorem qa_lDt_ne_qaHd : lDt ≠ qaHd := by decide
@[simp] theorem qa_qaHd_ne_lDg : qaHd ≠ lDg := by decide
@[simp] theorem qa_lDg_ne_qaHd : lDg ≠ qaHd := by decide
@[simp] theorem qa_qaHd_ne_lDi : qaHd ≠ lDi := by decide
@[simp] theorem qa_lDi_ne_qaHd : lDi ≠ qaHd := by decide
@[simp] theorem qa_qaHd_ne_lRp : qaHd ≠ lRp := by decide
@[simp] theorem qa_lRp_ne_qaHd : lRp ≠ qaHd := by decide
@[simp] theorem qa_qaHd_ne_lRn : qaHd ≠ lRn := by decide
@[simp] theorem qa_lRn_ne_qaHd : lRn ≠ qaHd := by decide
@[simp] theorem qa_qaHd_ne_lDir : qaHd ≠ lDir := by decide
@[simp] theorem qa_lDir_ne_qaHd : lDir ≠ qaHd := by decide
@[simp] theorem qa_qaHd_ne_lFle : qaHd ≠ lFle := by decide
@[simp] theorem qa_lFle_ne_qaHd : lFle ≠ qaHd := by decide
@[simp] theorem qa_qaHd_ne_lKb : qaHd ≠ lKb := by decide
@[simp] theorem qa_lKb_ne_qaHd : lKb ≠ qaHd := by decide
@[simp] theorem qa_qaVa_ne_qaHd : qaVa ≠ qaHd := by decide
@[simp] theorem qa_qaVa_ne_qaN : qaVa ≠ qaN := by decide
@[simp] theorem qa_qaVa_ne_qaTf : qaVa ≠ qaTf := by decide
@[simp] theorem qa_qaVa_ne_qaE0 : qaVa ≠ qaE0 := by decide
@[simp] theorem qa_qaVa_ne_qaR : qaVa ≠ qaR := by decide
@[simp] theorem qa_qaVa_ne_kFu : qaVa ≠ kFu := by decide
@[simp] theorem qa_kFu_ne_qaVa : kFu ≠ qaVa := by decide
@[simp] theorem qa_qaVa_ne_kD : qaVa ≠ kD := by decide
@[simp] theorem qa_kD_ne_qaVa : kD ≠ qaVa := by decide
@[simp] theorem qa_qaVa_ne_kE : qaVa ≠ kE := by decide
@[simp] theorem qa_kE_ne_qaVa : kE ≠ qaVa := by decide
@[simp] theorem qa_qaVa_ne_lFl : qaVa ≠ lFl := by decide
@[simp] theorem qa_lFl_ne_qaVa : lFl ≠ qaVa := by decide
@[simp] theorem qa_qaVa_ne_lDh : qaVa ≠ lDh := by decide
@[simp] theorem qa_lDh_ne_qaVa : lDh ≠ qaVa := by decide
@[simp] theorem qa_qaVa_ne_lDt : qaVa ≠ lDt := by decide
@[simp] theorem qa_lDt_ne_qaVa : lDt ≠ qaVa := by decide
@[simp] theorem qa_qaVa_ne_lDg : qaVa ≠ lDg := by decide
@[simp] theorem qa_lDg_ne_qaVa : lDg ≠ qaVa := by decide
@[simp] theorem qa_qaVa_ne_lDi : qaVa ≠ lDi := by decide
@[simp] theorem qa_lDi_ne_qaVa : lDi ≠ qaVa := by decide
@[simp] theorem qa_qaVa_ne_lRp : qaVa ≠ lRp := by decide
@[simp] theorem qa_lRp_ne_qaVa : lRp ≠ qaVa := by decide
@[simp] theorem qa_qaVa_ne_lRn : qaVa ≠ lRn := by decide
@[simp] theorem qa_lRn_ne_qaVa : lRn ≠ qaVa := by decide
@[simp] theorem qa_qaVa_ne_lDir : qaVa ≠ lDir := by decide
@[simp] theorem qa_lDir_ne_qaVa : lDir ≠ qaVa := by decide
@[simp] theorem qa_qaVa_ne_lFle : qaVa ≠ lFle := by decide
@[simp] theorem qa_lFle_ne_qaVa : lFle ≠ qaVa := by decide
@[simp] theorem qa_qaVa_ne_lKb : qaVa ≠ lKb := by decide
@[simp] theorem qa_lKb_ne_qaVa : lKb ≠ qaVa := by decide
@[simp] theorem qa_qaN_ne_qaHd : qaN ≠ qaHd := by decide
@[simp] theorem qa_qaN_ne_qaVa : qaN ≠ qaVa := by decide
@[simp] theorem qa_qaN_ne_qaTf : qaN ≠ qaTf := by decide
@[simp] theorem qa_qaN_ne_qaE0 : qaN ≠ qaE0 := by decide
@[simp] theorem qa_qaN_ne_qaR : qaN ≠ qaR := by decide
@[simp] theorem qa_qaN_ne_kFu : qaN ≠ kFu := by decide
@[simp] theorem qa_kFu_ne_qaN : kFu ≠ qaN := by decide
@[simp] theorem qa_qaN_ne_kD : qaN ≠ kD := by decide
@[simp] theorem qa_kD_ne_qaN : kD ≠ qaN := by decide
@[simp] theorem qa_qaN_ne_kE : qaN ≠ kE := by decide
@[simp] theorem qa_kE_ne_qaN : kE ≠ qaN := by decide
@[simp] theorem qa_qaN_ne_lFl : qaN ≠ lFl := by decide
@[simp] theorem qa_lFl_ne_qaN : lFl ≠ qaN := by decide
@[simp] theorem qa_qaN_ne_lDh : qaN ≠ lDh := by decide
@[simp] theorem qa_lDh_ne_qaN : lDh ≠ qaN := by decide
@[simp] theorem qa_qaN_ne_lDt : qaN ≠ lDt := by decide
@[simp] theorem qa_lDt_ne_qaN : lDt ≠ qaN := by decide
@[simp] theorem qa_qaN_ne_lDg : qaN ≠ lDg := by decide
@[simp] theorem qa_lDg_ne_qaN : lDg ≠ qaN := by decide
@[simp] theorem qa_qaN_ne_lDi : qaN ≠ lDi := by decide
@[simp] theorem qa_lDi_ne_qaN : lDi ≠ qaN := by decide
@[simp] theorem qa_qaN_ne_lRp : qaN ≠ lRp := by decide
@[simp] theorem qa_lRp_ne_qaN : lRp ≠ qaN := by decide
@[simp] theorem qa_qaN_ne_lRn : qaN ≠ lRn := by decide
@[simp] theorem qa_lRn_ne_qaN : lRn ≠ qaN := by decide
@[simp] theorem qa_qaN_ne_lDir : qaN ≠ lDir := by decide
@[simp] theorem qa_lDir_ne_qaN : lDir ≠ qaN := by decide
@[simp] theorem qa_qaN_ne_lFle : qaN ≠ lFle := by decide
@[simp] theorem qa_lFle_ne_qaN : lFle ≠ qaN := by decide
@[simp] theorem qa_qaN_ne_lKb : qaN ≠ lKb := by decide
@[simp] theorem qa_lKb_ne_qaN : lKb ≠ qaN := by decide
@[simp] theorem qa_qaTf_ne_qaHd : qaTf ≠ qaHd := by decide
@[simp] theorem qa_qaTf_ne_qaVa : qaTf ≠ qaVa := by decide
@[simp] theorem qa_qaTf_ne_qaN : qaTf ≠ qaN := by decide
@[simp] theorem qa_qaTf_ne_qaE0 : qaTf ≠ qaE0 := by decide
@[simp] theorem qa_qaTf_ne_qaR : qaTf ≠ qaR := by decide
@[simp] theorem qa_qaTf_ne_kFu : qaTf ≠ kFu := by decide
@[simp] theorem qa_kFu_ne_qaTf : kFu ≠ qaTf := by decide
@[simp] theorem qa_qaTf_ne_kD : qaTf ≠ kD := by decide
@[simp] theorem qa_kD_ne_qaTf : kD ≠ qaTf := by decide
@[simp] theorem qa_qaTf_ne_kE : qaTf ≠ kE := by decide
@[simp] theorem qa_kE_ne_qaTf : kE ≠ qaTf := by decide
@[simp] theorem qa_qaTf_ne_lFl : qaTf ≠ lFl := by decide
@[simp] theorem qa_lFl_ne_qaTf : lFl ≠ qaTf := by decide
@[simp] theorem qa_qaTf_ne_lDh : qaTf ≠ lDh := by decide
@[simp] theorem qa_lDh_ne_qaTf : lDh ≠ qaTf := by decide
@[simp] theorem qa_qaTf_ne_lDt : qaTf ≠ lDt := by decide
@[simp] theorem qa_lDt_ne_qaTf : lDt ≠ qaTf := by decide
@[simp] theorem qa_qaTf_ne_lDg : qaTf ≠ lDg := by decide
@[simp] theorem qa_lDg_ne_qaTf : lDg ≠ qaTf := by decide
@[simp] theorem qa_qaTf_ne_lDi : qaTf ≠ lDi := by decide
@[simp] theorem qa_lDi_ne_qaTf : lDi ≠ qaTf := by decide
@[simp] theorem qa_qaTf_ne_lRp : qaTf ≠ lRp := by decide
@[simp] theorem qa_lRp_ne_qaTf : lRp ≠ qaTf := by decide
@[simp] theorem qa_qaTf_ne_lRn : qaTf ≠ lRn := by decide
@[simp] theorem qa_lRn_ne_qaTf : lRn ≠ qaTf := by decide
@[simp] theorem qa_qaTf_ne_lDir : qaTf ≠ lDir := by decide
@[simp] theorem qa_lDir_ne_qaTf : lDir ≠ qaTf := by decide
@[simp] theorem qa_qaTf_ne_lFle : qaTf ≠ lFle := by decide
@[simp] theorem qa_lFle_ne_qaTf : lFle ≠ qaTf := by decide
@[simp] theorem qa_qaTf_ne_lKb : qaTf ≠ lKb := by decide
@[simp] theorem qa_lKb_ne_qaTf : lKb ≠ qaTf := by decide
@[simp] theorem qa_qaE0_ne_qaHd : qaE0 ≠ qaHd := by decide
@[simp] theorem qa_qaE0_ne_qaVa : qaE0 ≠ qaVa := by decide
@[simp] theorem qa_qaE0_ne_qaN : qaE0 ≠ qaN := by decide
@[simp] theorem qa_qaE0_ne_qaTf : qaE0 ≠ qaTf := by decide
@[simp] theorem qa_qaE0_ne_qaR : qaE0 ≠ qaR := by decide
@[simp] theorem qa_qaE0_ne_kFu : qaE0 ≠ kFu := by decide
@[simp] theorem qa_kFu_ne_qaE0 : kFu ≠ qaE0 := by decide
@[simp] theorem qa_qaE0_ne_kD : qaE0 ≠ kD := by decide
@[simp] theorem qa_kD_ne_qaE0 : kD ≠ qaE0 := by decide
@[simp] theorem qa_qaE0_ne_kE : qaE0 ≠ kE := by decide
@[simp] theorem qa_kE_ne_qaE0 : kE ≠ qaE0 := by decide
@[simp] theorem qa_qaE0_ne_lFl : qaE0 ≠ lFl := by decide
@[simp] theorem qa_lFl_ne_qaE0 : lFl ≠ qaE0 := by decide
@[simp] theorem qa_qaE0_ne_lDh : qaE0 ≠ lDh := by decide
@[simp] theorem qa_lDh_ne_qaE0 : lDh ≠ qaE0 := by decide
@[simp] theorem qa_qaE0_ne_lDt : qaE0 ≠ lDt := by decide
@[simp] theorem qa_lDt_ne_qaE0 : lDt ≠ qaE0 := by decide
@[simp] theorem qa_qaE0_ne_lDg : qaE0 ≠ lDg := by decide
@[simp] theorem qa_lDg_ne_qaE0 : lDg ≠ qaE0 := by decide
@[simp] theorem qa_qaE0_ne_lDi : qaE0 ≠ lDi := by decide
@[simp] theorem qa_lDi_ne_qaE0 : lDi ≠ qaE0 := by decide
@[simp] theorem qa_qaE0_ne_lRp : qaE0 ≠ lRp := by decide
@[simp] theorem qa_lRp_ne_qaE0 : lRp ≠ qaE0 := by decide
@[simp] theorem qa_qaE0_ne_lRn : qaE0 ≠ lRn := by decide
@[simp] theorem qa_lRn_ne_qaE0 : lRn ≠ qaE0 := by decide
@[simp] theorem qa_qaE0_ne_lDir : qaE0 ≠ lDir := by decide
@[simp] theorem qa_lDir_ne_qaE0 : lDir ≠ qaE0 := by decide
@[simp] theorem qa_qaE0_ne_lFle : qaE0 ≠ lFle := by decide
@[simp] theorem qa_lFle_ne_qaE0 : lFle ≠ qaE0 := by decide
@[simp] theorem qa_qaE0_ne_lKb : qaE0 ≠ lKb := by decide
@[simp] theorem qa_lKb_ne_qaE0 : lKb ≠ qaE0 := by decide
@[simp] theorem qa_qaR_ne_qaHd : qaR ≠ qaHd := by decide
@[simp] theorem qa_qaR_ne_qaVa : qaR ≠ qaVa := by decide
@[simp] theorem qa_qaR_ne_qaN : qaR ≠ qaN := by decide
@[simp] theorem qa_qaR_ne_qaTf : qaR ≠ qaTf := by decide
@[simp] theorem qa_qaR_ne_qaE0 : qaR ≠ qaE0 := by decide
@[simp] theorem qa_qaR_ne_kFu : qaR ≠ kFu := by decide
@[simp] theorem qa_kFu_ne_qaR : kFu ≠ qaR := by decide
@[simp] theorem qa_qaR_ne_kD : qaR ≠ kD := by decide
@[simp] theorem qa_kD_ne_qaR : kD ≠ qaR := by decide
@[simp] theorem qa_qaR_ne_kE : qaR ≠ kE := by decide
@[simp] theorem qa_kE_ne_qaR : kE ≠ qaR := by decide
@[simp] theorem qa_qaR_ne_lFl : qaR ≠ lFl := by decide
@[simp] theorem qa_lFl_ne_qaR : lFl ≠ qaR := by decide
@[simp] theorem qa_qaR_ne_lDh : qaR ≠ lDh := by decide
@[simp] theorem qa_lDh_ne_qaR : lDh ≠ qaR := by decide
@[simp] theorem qa_qaR_ne_lDt : qaR ≠ lDt := by decide
@[simp] theorem qa_lDt_ne_qaR : lDt ≠ qaR := by decide
@[simp] theorem qa_qaR_ne_lDg : qaR ≠ lDg := by decide
@[simp] theorem qa_lDg_ne_qaR : lDg ≠ qaR := by decide
@[simp] theorem qa_qaR_ne_lDi : qaR ≠ lDi := by decide
@[simp] theorem qa_lDi_ne_qaR : lDi ≠ qaR := by decide
@[simp] theorem qa_qaR_ne_lRp : qaR ≠ lRp := by decide
@[simp] theorem qa_lRp_ne_qaR : lRp ≠ qaR := by decide
@[simp] theorem qa_qaR_ne_lRn : qaR ≠ lRn := by decide
@[simp] theorem qa_lRn_ne_qaR : lRn ≠ qaR := by decide
@[simp] theorem qa_qaR_ne_lDir : qaR ≠ lDir := by decide
@[simp] theorem qa_lDir_ne_qaR : lDir ≠ qaR := by decide
@[simp] theorem qa_qaR_ne_lFle : qaR ≠ lFle := by decide
@[simp] theorem qa_lFle_ne_qaR : lFle ≠ qaR := by decide
@[simp] theorem qa_qaR_ne_lKb : qaR ≠ lKb := by decide
@[simp] theorem qa_lKb_ne_qaR : lKb ≠ qaR := by decide

def qaLocals : List MlS := [qaHd, qaVa, qaN, qaTf, qaE0, qaR]

def qaRest (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local qaN (.load .one (vv qaVa)))
  (.seq (.call (some (some (.local, qaTf), none)) fI [vv kFu, vv kD, vv qaHd])
  (allocP C qaE0 (.const 8) (.seq (.store (vv qaE0) (.const 0))
  (.seq (.call (some (some (.local, qaR), none)) fSp [vv kFu, vv kD, vv qaTf, vv qaE0, vv qaVa, .const 0, vv qaN])
    (.return (vv qaR))))))

def qaCore (C : Ctx) : ProgHOL 64 :=
  .ite (tagIs4E kE)
    (.seq (.call (some (some (.local, qaHd), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv kE])
    (.seq (.call (some (some (.local, qaVa), none)) ExG.fGaa [.const (BitVec.ofNat 64 coreWalkFuel), vv kE])
      (qaRest C)))
    (.seq (.assign .local qaHd (vv kE)) (allocP C qaVa (.const 8) (.seq (.store (vv qaVa) (.const 0)) (qaRest C))))

def qaBody (C : Ctx) : ProgHOL 64 := prologue qaLocals (qaCore C)

section
variable {σ : Type}

theorem qa_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ qaLocals → (ctxEnv C ++ kParams.zip vals).get x = none :=
  Knot.params_none C qaLocals kParams vals (by decide) (by decide)

structure QaCodes (C : Ctx) : Prop where
  sp : SpCodes C
  af : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  gaa : C.code.lookup ExG.fGaa = some ([(pFu, .one), (pH, .one)], ExG.gaaBody C, .one)

theorem qa_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (hc : QaCodes C)
    (hI : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → d' < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (inferE C fIB) s1 ((knot mode C n).infer d' e')
      (PostK (ctxH C H)))
    (hW : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → d' < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d' e')
      (PostK (ctxH C H)))
    (hD : ∀ (H : List (BitVec 64)) s1 d' a b, C.H <+: H → d' < 2 ^ 63 → Callee (σ := σ) (ctxH C H) dParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW a, Enc.idxW b] (dE C) s1 ((knot mode C n).defeq d' a b)
      (PostB (ctxH C H)))
    (hDE : ∀ (H : List (BitVec 64)) s1 d' a b, C.H <+: H → d' < 2 ^ 63 → Callee (σ := σ) (ctxH C H) dParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW a, Enc.idxW b] (dEE C) s1 ((knot mode C n).defeqE d' a b)
      (PostB (ctxH C H)))
    (s : AState) (d : Nat) (hdd : d < 2 ^ 63) (e : EIdx) :
    SpecR (σ := σ) (Pre C s (kParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e])) (qaBody C) s
      (inferApp (knot mode C n) C.fe d e) (PostK C) := by
  refine specR_prologue (postK_locals C) (qa_none C _) ?_
  have rest : ∀ (hd : EIdx) (va : List EIdx) (ov : Nat) (H : List (BitVec 64)) (s1 : AState) (Γ : Env),
      C.H <+: H → BlkAt H ov (va.map Enc.idxW) → Γ.get qaHd = some (Enc.idxW hd) →
      Γ.get qaVa = some (cellA C ov) → Γ.get kFu = some (BitVec.ofNat 64 n) → Γ.get kD = some (BitVec.ofNat 64 d) →
      SpecR (σ := σ) (Inv (ctxH C H) s1 Γ [] (ctxLocals ++ qaLocals)) (qaRest C) s1
        ((knot mode C n).infer d hd >>= fun tf => inferSpine (knot mode C n) C.fe d tf #[] va.toArray 0) (PostK C) := by
    intro hd va ov H s1 Γ hp hb h1 h2 h3 h4
    unfold qaRest
    refine specR_atEntry fun t0 ht0 => ?_
    have hsa := blk_small0 (C := ctxH C H) (ctxOK_H hok _) ht0.sr hb
    simp only [List.length_map] at hsa
    obtain ⟨hlo, hlv⟩ := blkAt_get0 hb
    refine UD.specR_heapLoadI' (C := ctxH C H) qaN (vv qaVa) ov (BitVec.ofNat 64 va.length)
      (by show H[ov]? = _; rw [List.getElem?_eq_getElem hlo, hlv]; simp) (by decide) (by simp [h2]; rfl) ?_
    refine Big.specR_callKC (C := ctxH C H) qaTf fI kParams [vv kFu, vv kD, vv qaHd] (inferE C fIB)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW hd] (by decide) rfl (by decide) hc.sp.i
      ⟨by simp [h3], by simp [h4], by simp [h1], trivial⟩ (hI H s1 d hd hp hdd) (fun tf s2 H2 hp2 _ => ?_)
    refine specR_emptyBlk (C0 := C) hok (H := H2) qaE0 (by decide) (fun H3 oe hp3 hbe => ?_)
    refine specR_congr (m' := inferSpine (knot mode C n) C.fe d tf ([] : List EIdx).toArray va.toArray 0
      >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H3) qaR fSp spParams
      [vv kFu, vv kD, vv qaTf, vv qaE0, vv qaVa, .const 0, vv qaN] (spBody C)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW tf, cellA C oe, cellA C ov, BitVec.ofNat 64 0,
        BitVec.ofNat 64 va.length] (by decide) rfl (by decide) hc.sp.self
      ⟨by simp [h3], by simp [h4], by simp, by simp <;> rfl, by simp [h2], rfl, by simp, trivial⟩
      (PostK (ctxH C H3)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu spParams _ rfl hlk)
        (sp_spec ra mode n C hok hc.sp hI hW hD hDE d hdd va ov H hp hb hsa (va.length - 0) tf [] oe 0 H3 s2
          (hp2.trans hp3) (by simpa using hbe) (by simp) (by simp) (by simp)))
      (fun r w s4 H4 hp4 hw => ?_)
    subst hw
    exact specR_returnI _ (Enc.idxW r) (by simp)
      (fun t ht => ⟨H4, hp.trans (hp2.trans (hp3.trans hp4)), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  unfold qaCore inferApp headAndArgs
  have hT := sev_tagIs4B (ctxEnv C ++ kParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e]) kE e
    (by simp +decide [Env.get, kParams, ctxEnv])
  by_cases ht : (e.tag == 4) = true
  · rw [if_pos (show (e.tag == ETag.app) = true from ht)]
    simp only [bind_assoc, pure_bind]
    refine specR_ifI _ 1 (by rw [hT, ht]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_callNIM (C := C) qaHd fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv kE]
      getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e] (by decide) rfl (by decide) hc.af
      ⟨rfl, by simp +decide [Env.get, kParams, ctxEnv], trivial⟩
      (fun a w s' st => getAppFn coreWalkFuel e s = .ok (a, s') ∧ Post C s a w s' st)
      (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
      (fun u hu _ hlk => specR_run (fun t ht => by
        subst ht
        exact getAppFn_spec C hc.af coreWalkFuel e s CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide),
          hlk 1 (by decide)⟩))
      (fun hd w s' st ⟨hrun2, hw, hs, _⟩ => ?_)
    subst hw
    have hs' : s = s' := hs.symm
    subst hs'
    refine specR_callNIH (C := C) qaVa ExG.fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv kE]
      (ExG.gaaBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e] (by decide) rfl (by decide) hc.gaa
      ⟨rfl, by simp +decide [Env.get, kParams, ctxEnv], trivial⟩
      (PostA C) (fun a w _ H3 => ∃ o3, w = cellA C o3 ∧ BlkAt H3 o3 (a.map Enc.idxW))
      (fun a w s' st ⟨H3, o3, hp, hw, hb, hsr⟩ => ⟨H3, hp, ⟨o3, hw, hb⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
        (ExG.gaa_spec C hok hc.gaa coreWalkFuel CV.coreWalkFuel_lt C.H e s))
      (fun va w s3 H3 hp3 ⟨o3, hw, hb3⟩ => ?_)
    subst hw
    refine rest hd va o3 H3 s3 _ hp3 hb3 ?_ ?_ ?_ ?_ <;> first | (simp +decide [Env.get, kParams, ctxEnv]; done) | (simp; rfl) | simp +decide [Env.get, kParams, ctxEnv] <;> rfl
  · rw [if_neg (show ¬ (e.tag == ETag.app) = true from ht)]
    refine specR_ifI _ 0 (by rw [hT]; simp [ht, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI qaHd (vv kE) (Enc.idxW e) (by decide) (by simp +decide [Env.get, kParams, ctxEnv]) ?_
    simp only [pure_bind]
    refine specR_emptyBlk (C0 := C) hok (H := C.H) qaVa (by decide) (fun H3 oe hp3 hbe => ?_)
    refine rest e [] oe H3 s _ hp3 (by simpa using hbe) ?_ ?_ ?_ ?_ <;> first | (simp +decide [Env.get, kParams, ctxEnv]; done) | (simp; rfl) | simp +decide [Env.get, kParams, ctxEnv] <;> rfl

end

end ConPanqueque.T.WC
