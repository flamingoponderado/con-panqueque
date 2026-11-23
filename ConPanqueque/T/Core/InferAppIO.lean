import ConPanqueque.T.Core.InferSpineIO
import ConPanqueque.T.Core.StepApp
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# The io grade's application arm's wrapper: `inferAppIOAt`

As `inferApp`, with the io spine walk (`inferSpineIO`).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def qaoHd := ofString "qaon_hd"
def qaoVa := ofString "qaon_va"
def qaoN := ofString "qaon_n"
def qaoTf := ofString "qaon_tf"
def qaoE0 := ofString "qaon_e0"
def qaoR := ofString "qaon_r"

@[simp] theorem qao_qaHd_ne_qaVa : qaoHd ≠ qaoVa := by decide
@[simp] theorem qao_qaHd_ne_qaN : qaoHd ≠ qaoN := by decide
@[simp] theorem qao_qaHd_ne_qaTf : qaoHd ≠ qaoTf := by decide
@[simp] theorem qao_qaHd_ne_qaE0 : qaoHd ≠ qaoE0 := by decide
@[simp] theorem qao_qaHd_ne_qaR : qaoHd ≠ qaoR := by decide
@[simp] theorem qao_qaHd_ne_kFu : qaoHd ≠ kFu := by decide
@[simp] theorem qao_kFu_ne_qaHd : kFu ≠ qaoHd := by decide
@[simp] theorem qao_qaHd_ne_kD : qaoHd ≠ kD := by decide
@[simp] theorem qao_kD_ne_qaHd : kD ≠ qaoHd := by decide
@[simp] theorem qao_qaHd_ne_kE : qaoHd ≠ kE := by decide
@[simp] theorem qao_kE_ne_qaHd : kE ≠ qaoHd := by decide
@[simp] theorem qao_qaHd_ne_lFl : qaoHd ≠ lFl := by decide
@[simp] theorem qao_lFl_ne_qaHd : lFl ≠ qaoHd := by decide
@[simp] theorem qao_qaHd_ne_lDh : qaoHd ≠ lDh := by decide
@[simp] theorem qao_lDh_ne_qaHd : lDh ≠ qaoHd := by decide
@[simp] theorem qao_qaHd_ne_lDt : qaoHd ≠ lDt := by decide
@[simp] theorem qao_lDt_ne_qaHd : lDt ≠ qaoHd := by decide
@[simp] theorem qao_qaHd_ne_lDg : qaoHd ≠ lDg := by decide
@[simp] theorem qao_lDg_ne_qaHd : lDg ≠ qaoHd := by decide
@[simp] theorem qao_qaHd_ne_lDi : qaoHd ≠ lDi := by decide
@[simp] theorem qao_lDi_ne_qaHd : lDi ≠ qaoHd := by decide
@[simp] theorem qao_qaHd_ne_lRp : qaoHd ≠ lRp := by decide
@[simp] theorem qao_lRp_ne_qaHd : lRp ≠ qaoHd := by decide
@[simp] theorem qao_qaHd_ne_lRn : qaoHd ≠ lRn := by decide
@[simp] theorem qao_lRn_ne_qaHd : lRn ≠ qaoHd := by decide
@[simp] theorem qao_qaHd_ne_lDir : qaoHd ≠ lDir := by decide
@[simp] theorem qao_lDir_ne_qaHd : lDir ≠ qaoHd := by decide
@[simp] theorem qao_qaHd_ne_lFle : qaoHd ≠ lFle := by decide
@[simp] theorem qao_lFle_ne_qaHd : lFle ≠ qaoHd := by decide
@[simp] theorem qao_qaHd_ne_lKb : qaoHd ≠ lKb := by decide
@[simp] theorem qao_lKb_ne_qaHd : lKb ≠ qaoHd := by decide
@[simp] theorem qao_qaVa_ne_qaHd : qaoVa ≠ qaoHd := by decide
@[simp] theorem qao_qaVa_ne_qaN : qaoVa ≠ qaoN := by decide
@[simp] theorem qao_qaVa_ne_qaTf : qaoVa ≠ qaoTf := by decide
@[simp] theorem qao_qaVa_ne_qaE0 : qaoVa ≠ qaoE0 := by decide
@[simp] theorem qao_qaVa_ne_qaR : qaoVa ≠ qaoR := by decide
@[simp] theorem qao_qaVa_ne_kFu : qaoVa ≠ kFu := by decide
@[simp] theorem qao_kFu_ne_qaVa : kFu ≠ qaoVa := by decide
@[simp] theorem qao_qaVa_ne_kD : qaoVa ≠ kD := by decide
@[simp] theorem qao_kD_ne_qaVa : kD ≠ qaoVa := by decide
@[simp] theorem qao_qaVa_ne_kE : qaoVa ≠ kE := by decide
@[simp] theorem qao_kE_ne_qaVa : kE ≠ qaoVa := by decide
@[simp] theorem qao_qaVa_ne_lFl : qaoVa ≠ lFl := by decide
@[simp] theorem qao_lFl_ne_qaVa : lFl ≠ qaoVa := by decide
@[simp] theorem qao_qaVa_ne_lDh : qaoVa ≠ lDh := by decide
@[simp] theorem qao_lDh_ne_qaVa : lDh ≠ qaoVa := by decide
@[simp] theorem qao_qaVa_ne_lDt : qaoVa ≠ lDt := by decide
@[simp] theorem qao_lDt_ne_qaVa : lDt ≠ qaoVa := by decide
@[simp] theorem qao_qaVa_ne_lDg : qaoVa ≠ lDg := by decide
@[simp] theorem qao_lDg_ne_qaVa : lDg ≠ qaoVa := by decide
@[simp] theorem qao_qaVa_ne_lDi : qaoVa ≠ lDi := by decide
@[simp] theorem qao_lDi_ne_qaVa : lDi ≠ qaoVa := by decide
@[simp] theorem qao_qaVa_ne_lRp : qaoVa ≠ lRp := by decide
@[simp] theorem qao_lRp_ne_qaVa : lRp ≠ qaoVa := by decide
@[simp] theorem qao_qaVa_ne_lRn : qaoVa ≠ lRn := by decide
@[simp] theorem qao_lRn_ne_qaVa : lRn ≠ qaoVa := by decide
@[simp] theorem qao_qaVa_ne_lDir : qaoVa ≠ lDir := by decide
@[simp] theorem qao_lDir_ne_qaVa : lDir ≠ qaoVa := by decide
@[simp] theorem qao_qaVa_ne_lFle : qaoVa ≠ lFle := by decide
@[simp] theorem qao_lFle_ne_qaVa : lFle ≠ qaoVa := by decide
@[simp] theorem qao_qaVa_ne_lKb : qaoVa ≠ lKb := by decide
@[simp] theorem qao_lKb_ne_qaVa : lKb ≠ qaoVa := by decide
@[simp] theorem qao_qaN_ne_qaHd : qaoN ≠ qaoHd := by decide
@[simp] theorem qao_qaN_ne_qaVa : qaoN ≠ qaoVa := by decide
@[simp] theorem qao_qaN_ne_qaTf : qaoN ≠ qaoTf := by decide
@[simp] theorem qao_qaN_ne_qaE0 : qaoN ≠ qaoE0 := by decide
@[simp] theorem qao_qaN_ne_qaR : qaoN ≠ qaoR := by decide
@[simp] theorem qao_qaN_ne_kFu : qaoN ≠ kFu := by decide
@[simp] theorem qao_kFu_ne_qaN : kFu ≠ qaoN := by decide
@[simp] theorem qao_qaN_ne_kD : qaoN ≠ kD := by decide
@[simp] theorem qao_kD_ne_qaN : kD ≠ qaoN := by decide
@[simp] theorem qao_qaN_ne_kE : qaoN ≠ kE := by decide
@[simp] theorem qao_kE_ne_qaN : kE ≠ qaoN := by decide
@[simp] theorem qao_qaN_ne_lFl : qaoN ≠ lFl := by decide
@[simp] theorem qao_lFl_ne_qaN : lFl ≠ qaoN := by decide
@[simp] theorem qao_qaN_ne_lDh : qaoN ≠ lDh := by decide
@[simp] theorem qao_lDh_ne_qaN : lDh ≠ qaoN := by decide
@[simp] theorem qao_qaN_ne_lDt : qaoN ≠ lDt := by decide
@[simp] theorem qao_lDt_ne_qaN : lDt ≠ qaoN := by decide
@[simp] theorem qao_qaN_ne_lDg : qaoN ≠ lDg := by decide
@[simp] theorem qao_lDg_ne_qaN : lDg ≠ qaoN := by decide
@[simp] theorem qao_qaN_ne_lDi : qaoN ≠ lDi := by decide
@[simp] theorem qao_lDi_ne_qaN : lDi ≠ qaoN := by decide
@[simp] theorem qao_qaN_ne_lRp : qaoN ≠ lRp := by decide
@[simp] theorem qao_lRp_ne_qaN : lRp ≠ qaoN := by decide
@[simp] theorem qao_qaN_ne_lRn : qaoN ≠ lRn := by decide
@[simp] theorem qao_lRn_ne_qaN : lRn ≠ qaoN := by decide
@[simp] theorem qao_qaN_ne_lDir : qaoN ≠ lDir := by decide
@[simp] theorem qao_lDir_ne_qaN : lDir ≠ qaoN := by decide
@[simp] theorem qao_qaN_ne_lFle : qaoN ≠ lFle := by decide
@[simp] theorem qao_lFle_ne_qaN : lFle ≠ qaoN := by decide
@[simp] theorem qao_qaN_ne_lKb : qaoN ≠ lKb := by decide
@[simp] theorem qao_lKb_ne_qaN : lKb ≠ qaoN := by decide
@[simp] theorem qao_qaTf_ne_qaHd : qaoTf ≠ qaoHd := by decide
@[simp] theorem qao_qaTf_ne_qaVa : qaoTf ≠ qaoVa := by decide
@[simp] theorem qao_qaTf_ne_qaN : qaoTf ≠ qaoN := by decide
@[simp] theorem qao_qaTf_ne_qaE0 : qaoTf ≠ qaoE0 := by decide
@[simp] theorem qao_qaTf_ne_qaR : qaoTf ≠ qaoR := by decide
@[simp] theorem qao_qaTf_ne_kFu : qaoTf ≠ kFu := by decide
@[simp] theorem qao_kFu_ne_qaTf : kFu ≠ qaoTf := by decide
@[simp] theorem qao_qaTf_ne_kD : qaoTf ≠ kD := by decide
@[simp] theorem qao_kD_ne_qaTf : kD ≠ qaoTf := by decide
@[simp] theorem qao_qaTf_ne_kE : qaoTf ≠ kE := by decide
@[simp] theorem qao_kE_ne_qaTf : kE ≠ qaoTf := by decide
@[simp] theorem qao_qaTf_ne_lFl : qaoTf ≠ lFl := by decide
@[simp] theorem qao_lFl_ne_qaTf : lFl ≠ qaoTf := by decide
@[simp] theorem qao_qaTf_ne_lDh : qaoTf ≠ lDh := by decide
@[simp] theorem qao_lDh_ne_qaTf : lDh ≠ qaoTf := by decide
@[simp] theorem qao_qaTf_ne_lDt : qaoTf ≠ lDt := by decide
@[simp] theorem qao_lDt_ne_qaTf : lDt ≠ qaoTf := by decide
@[simp] theorem qao_qaTf_ne_lDg : qaoTf ≠ lDg := by decide
@[simp] theorem qao_lDg_ne_qaTf : lDg ≠ qaoTf := by decide
@[simp] theorem qao_qaTf_ne_lDi : qaoTf ≠ lDi := by decide
@[simp] theorem qao_lDi_ne_qaTf : lDi ≠ qaoTf := by decide
@[simp] theorem qao_qaTf_ne_lRp : qaoTf ≠ lRp := by decide
@[simp] theorem qao_lRp_ne_qaTf : lRp ≠ qaoTf := by decide
@[simp] theorem qao_qaTf_ne_lRn : qaoTf ≠ lRn := by decide
@[simp] theorem qao_lRn_ne_qaTf : lRn ≠ qaoTf := by decide
@[simp] theorem qao_qaTf_ne_lDir : qaoTf ≠ lDir := by decide
@[simp] theorem qao_lDir_ne_qaTf : lDir ≠ qaoTf := by decide
@[simp] theorem qao_qaTf_ne_lFle : qaoTf ≠ lFle := by decide
@[simp] theorem qao_lFle_ne_qaTf : lFle ≠ qaoTf := by decide
@[simp] theorem qao_qaTf_ne_lKb : qaoTf ≠ lKb := by decide
@[simp] theorem qao_lKb_ne_qaTf : lKb ≠ qaoTf := by decide
@[simp] theorem qao_qaE0_ne_qaHd : qaoE0 ≠ qaoHd := by decide
@[simp] theorem qao_qaE0_ne_qaVa : qaoE0 ≠ qaoVa := by decide
@[simp] theorem qao_qaE0_ne_qaN : qaoE0 ≠ qaoN := by decide
@[simp] theorem qao_qaE0_ne_qaTf : qaoE0 ≠ qaoTf := by decide
@[simp] theorem qao_qaE0_ne_qaR : qaoE0 ≠ qaoR := by decide
@[simp] theorem qao_qaE0_ne_kFu : qaoE0 ≠ kFu := by decide
@[simp] theorem qao_kFu_ne_qaE0 : kFu ≠ qaoE0 := by decide
@[simp] theorem qao_qaE0_ne_kD : qaoE0 ≠ kD := by decide
@[simp] theorem qao_kD_ne_qaE0 : kD ≠ qaoE0 := by decide
@[simp] theorem qao_qaE0_ne_kE : qaoE0 ≠ kE := by decide
@[simp] theorem qao_kE_ne_qaE0 : kE ≠ qaoE0 := by decide
@[simp] theorem qao_qaE0_ne_lFl : qaoE0 ≠ lFl := by decide
@[simp] theorem qao_lFl_ne_qaE0 : lFl ≠ qaoE0 := by decide
@[simp] theorem qao_qaE0_ne_lDh : qaoE0 ≠ lDh := by decide
@[simp] theorem qao_lDh_ne_qaE0 : lDh ≠ qaoE0 := by decide
@[simp] theorem qao_qaE0_ne_lDt : qaoE0 ≠ lDt := by decide
@[simp] theorem qao_lDt_ne_qaE0 : lDt ≠ qaoE0 := by decide
@[simp] theorem qao_qaE0_ne_lDg : qaoE0 ≠ lDg := by decide
@[simp] theorem qao_lDg_ne_qaE0 : lDg ≠ qaoE0 := by decide
@[simp] theorem qao_qaE0_ne_lDi : qaoE0 ≠ lDi := by decide
@[simp] theorem qao_lDi_ne_qaE0 : lDi ≠ qaoE0 := by decide
@[simp] theorem qao_qaE0_ne_lRp : qaoE0 ≠ lRp := by decide
@[simp] theorem qao_lRp_ne_qaE0 : lRp ≠ qaoE0 := by decide
@[simp] theorem qao_qaE0_ne_lRn : qaoE0 ≠ lRn := by decide
@[simp] theorem qao_lRn_ne_qaE0 : lRn ≠ qaoE0 := by decide
@[simp] theorem qao_qaE0_ne_lDir : qaoE0 ≠ lDir := by decide
@[simp] theorem qao_lDir_ne_qaE0 : lDir ≠ qaoE0 := by decide
@[simp] theorem qao_qaE0_ne_lFle : qaoE0 ≠ lFle := by decide
@[simp] theorem qao_lFle_ne_qaE0 : lFle ≠ qaoE0 := by decide
@[simp] theorem qao_qaE0_ne_lKb : qaoE0 ≠ lKb := by decide
@[simp] theorem qao_lKb_ne_qaE0 : lKb ≠ qaoE0 := by decide
@[simp] theorem qao_qaR_ne_qaHd : qaoR ≠ qaoHd := by decide
@[simp] theorem qao_qaR_ne_qaVa : qaoR ≠ qaoVa := by decide
@[simp] theorem qao_qaR_ne_qaN : qaoR ≠ qaoN := by decide
@[simp] theorem qao_qaR_ne_qaTf : qaoR ≠ qaoTf := by decide
@[simp] theorem qao_qaR_ne_qaE0 : qaoR ≠ qaoE0 := by decide
@[simp] theorem qao_qaR_ne_kFu : qaoR ≠ kFu := by decide
@[simp] theorem qao_kFu_ne_qaR : kFu ≠ qaoR := by decide
@[simp] theorem qao_qaR_ne_kD : qaoR ≠ kD := by decide
@[simp] theorem qao_kD_ne_qaR : kD ≠ qaoR := by decide
@[simp] theorem qao_qaR_ne_kE : qaoR ≠ kE := by decide
@[simp] theorem qao_kE_ne_qaR : kE ≠ qaoR := by decide
@[simp] theorem qao_qaR_ne_lFl : qaoR ≠ lFl := by decide
@[simp] theorem qao_lFl_ne_qaR : lFl ≠ qaoR := by decide
@[simp] theorem qao_qaR_ne_lDh : qaoR ≠ lDh := by decide
@[simp] theorem qao_lDh_ne_qaR : lDh ≠ qaoR := by decide
@[simp] theorem qao_qaR_ne_lDt : qaoR ≠ lDt := by decide
@[simp] theorem qao_lDt_ne_qaR : lDt ≠ qaoR := by decide
@[simp] theorem qao_qaR_ne_lDg : qaoR ≠ lDg := by decide
@[simp] theorem qao_lDg_ne_qaR : lDg ≠ qaoR := by decide
@[simp] theorem qao_qaR_ne_lDi : qaoR ≠ lDi := by decide
@[simp] theorem qao_lDi_ne_qaR : lDi ≠ qaoR := by decide
@[simp] theorem qao_qaR_ne_lRp : qaoR ≠ lRp := by decide
@[simp] theorem qao_lRp_ne_qaR : lRp ≠ qaoR := by decide
@[simp] theorem qao_qaR_ne_lRn : qaoR ≠ lRn := by decide
@[simp] theorem qao_lRn_ne_qaR : lRn ≠ qaoR := by decide
@[simp] theorem qao_qaR_ne_lDir : qaoR ≠ lDir := by decide
@[simp] theorem qao_lDir_ne_qaR : lDir ≠ qaoR := by decide
@[simp] theorem qao_qaR_ne_lFle : qaoR ≠ lFle := by decide
@[simp] theorem qao_lFle_ne_qaR : lFle ≠ qaoR := by decide
@[simp] theorem qao_qaR_ne_lKb : qaoR ≠ lKb := by decide
@[simp] theorem qao_lKb_ne_qaR : lKb ≠ qaoR := by decide

def qaoLocals : List MlS := [qaoHd, qaoVa, qaoN, qaoTf, qaoE0, qaoR]

def qaoRest (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local qaoN (.load .one (vv qaoVa)))
  (.seq (.call (some (some (.local, qaoTf), none)) fI [vv kFu, vv kD, vv qaoHd])
  (allocP C qaoE0 (.const 8) (.seq (.store (vv qaoE0) (.const 0))
  (.seq (.call (some (some (.local, qaoR), none)) fSo [vv kFu, vv kD, vv qaoTf, vv qaoE0, vv qaoVa, .const 0, vv qaoN])
    (.return (vv qaoR))))))

def qaoCore (C : Ctx) : ProgHOL 64 :=
  .ite (tagIs4E kE)
    (.seq (.call (some (some (.local, qaoHd), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv kE])
    (.seq (.call (some (some (.local, qaoVa), none)) ExG.fGaa [.const (BitVec.ofNat 64 coreWalkFuel), vv kE])
      (qaoRest C)))
    (.seq (.assign .local qaoHd (vv kE)) (allocP C qaoVa (.const 8) (.seq (.store (vv qaoVa) (.const 0)) (qaoRest C))))

def qaoBody (C : Ctx) : ProgHOL 64 := prologue qaoLocals (qaoCore C)

section
variable {σ : Type}

theorem qao_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ qaoLocals → (ctxEnv C ++ kParams.zip vals).get x = none :=
  Knot.params_none C qaoLocals kParams vals (by decide) (by decide)

structure QaoCodes (C : Ctx) : Prop where
  so : SoCodes C
  i : C.code.lookup fI = some (pmap kParams, inferE C fIB, .one)
  af : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  gaa : C.code.lookup ExG.fGaa = some ([(pFu, .one), (pH, .one)], ExG.gaaBody C, .one)

theorem qao_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (hc : QaoCodes C)
    (hI : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (inferE C fIB) s1 ((knot mode C n).infer d' e')
      (PostK (ctxH C H)))
    (hW : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d' e')
      (PostK (ctxH C H)))
    (s : AState) (d : Nat) (e : EIdx) :
    SpecR (σ := σ) (Pre C s (kParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e])) (qaoBody C) s
      (inferAppIOAt (knot mode C n) C.fe d e) (PostK C) := by
  refine specR_prologue (postK_locals C) (qao_none C _) ?_
  have rest : ∀ (hd : EIdx) (va : List EIdx) (ov : Nat) (H : List (BitVec 64)) (s1 : AState) (Γ : Env),
      C.H <+: H → BlkAt H ov (va.map Enc.idxW) → Γ.get qaoHd = some (Enc.idxW hd) →
      Γ.get qaoVa = some (cellA C ov) → Γ.get kFu = some (BitVec.ofNat 64 n) → Γ.get kD = some (BitVec.ofNat 64 d) →
      SpecR (σ := σ) (Inv (ctxH C H) s1 Γ [] (ctxLocals ++ qaoLocals)) (qaoRest C) s1
        ((knot mode C n).infer d hd >>= fun tf => inferSpineIO (knot mode C n) C.fe d tf #[] va.toArray 0) (PostK C) := by
    intro hd va ov H s1 Γ hp hb h1 h2 h3 h4
    unfold qaoRest
    refine specR_atEntry fun t0 ht0 => ?_
    have hsa := blk_small0 (C := ctxH C H) (ctxOK_H hok _) ht0.sr hb
    simp only [List.length_map] at hsa
    obtain ⟨hlo, hlv⟩ := blkAt_get0 hb
    refine UD.specR_heapLoadI' (C := ctxH C H) qaoN (vv qaoVa) ov (BitVec.ofNat 64 va.length)
      (by show H[ov]? = _; rw [List.getElem?_eq_getElem hlo, hlv]; simp) (by decide) (by simp [h2]; rfl) ?_
    refine Big.specR_callKC (C := ctxH C H) qaoTf fI kParams [vv kFu, vv kD, vv qaoHd] (inferE C fIB)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW hd] (by decide) rfl (by decide) hc.i
      ⟨by simp [h3], by simp [h4], by simp [h1], trivial⟩ (hI H s1 d hd hp) (fun tf s2 H2 hp2 _ => ?_)
    refine specR_emptyBlk (C0 := C) hok (H := H2) qaoE0 (by decide) (fun H3 oe hp3 hbe => ?_)
    refine specR_congr (m' := inferSpineIO (knot mode C n) C.fe d tf ([] : List EIdx).toArray va.toArray 0
      >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H3) qaoR fSo soParams
      [vv kFu, vv kD, vv qaoTf, vv qaoE0, vv qaoVa, .const 0, vv qaoN] (soBody C)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW tf, cellA C oe, cellA C ov, BitVec.ofNat 64 0,
        BitVec.ofNat 64 va.length] (by decide) rfl (by decide) hc.so.self
      ⟨by simp [h3], by simp [h4], by simp, by simp <;> rfl, by simp [h2], rfl, by simp, trivial⟩
      (PostK (ctxH C H3)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu soParams _ rfl hlk)
        (so_spec ra mode n C hok hc.so hW d va ov H hp hb hsa (va.length - 0) tf [] oe 0 H3 s2
          (hp2.trans hp3) (by simpa using hbe) (by simp) (by simp) (by simp)))
      (fun r w s4 H4 hp4 hw => ?_)
    subst hw
    exact specR_returnI _ (Enc.idxW r) (by simp)
      (fun t ht => ⟨H4, hp.trans (hp2.trans (hp3.trans hp4)), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  unfold qaoCore inferAppIOAt headAndArgs
  have hT := sev_tagIs4B (ctxEnv C ++ kParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e]) kE e
    (by simp +decide [Env.get, kParams, ctxEnv])
  by_cases ht : (e.tag == 4) = true
  · rw [if_pos (show (e.tag == ETag.app) = true from ht)]
    simp only [bind_assoc, pure_bind]
    refine specR_ifI _ 1 (by rw [hT, ht]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_callNIM (C := C) qaoHd fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv kE]
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
    refine specR_callNIH (C := C) qaoVa ExG.fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv kE]
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
    refine specR_assignI qaoHd (vv kE) (Enc.idxW e) (by decide) (by simp +decide [Env.get, kParams, ctxEnv]) ?_
    simp only [pure_bind]
    refine specR_emptyBlk (C0 := C) hok (H := C.H) qaoVa (by decide) (fun H3 oe hp3 hbe => ?_)
    refine rest e [] oe H3 s _ hp3 (by simpa using hbe) ?_ ?_ ?_ ?_ <;> first | (simp +decide [Env.get, kParams, ctxEnv]; done) | (simp; rfl) | simp +decide [Env.get, kParams, ctxEnv] <;> rfl

end

end ConPanqueque.T.WC
