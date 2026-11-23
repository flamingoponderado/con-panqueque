import ConPanqueque.T.Core.DefeqBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# PropRead's telescope readers: `binderDom`

The domain of the `k`-th syntactic ∀ binder (`optW`).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def bdK := ofString "prd_bdk"
def bdH := ofString "prd_bdh"
def bdA := ofString "prd_bda"
def bdB := ofString "prd_bdb"
def bdR := ofString "prd_bdr"
def fBd := ofString "binderDom"

@[simp] theorem prd_bdK_ne_bdH : bdK ≠ bdH := by decide
@[simp] theorem prd_bdK_ne_bdA : bdK ≠ bdA := by decide
@[simp] theorem prd_bdK_ne_bdB : bdK ≠ bdB := by decide
@[simp] theorem prd_bdK_ne_bdR : bdK ≠ bdR := by decide
@[simp] theorem prd_bdK_ne_lFl : bdK ≠ lFl := by decide
@[simp] theorem prd_lFl_ne_bdK : lFl ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_lDh : bdK ≠ lDh := by decide
@[simp] theorem prd_lDh_ne_bdK : lDh ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_lDt : bdK ≠ lDt := by decide
@[simp] theorem prd_lDt_ne_bdK : lDt ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_lDg : bdK ≠ lDg := by decide
@[simp] theorem prd_lDg_ne_bdK : lDg ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_lDi : bdK ≠ lDi := by decide
@[simp] theorem prd_lDi_ne_bdK : lDi ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_lRp : bdK ≠ lRp := by decide
@[simp] theorem prd_lRp_ne_bdK : lRp ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_lRn : bdK ≠ lRn := by decide
@[simp] theorem prd_lRn_ne_bdK : lRn ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_lFle : bdK ≠ lFle := by decide
@[simp] theorem prd_lFle_ne_bdK : lFle ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_lKb : bdK ≠ lKb := by decide
@[simp] theorem prd_lKb_ne_bdK : lKb ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_lDir : bdK ≠ lDir := by decide
@[simp] theorem prd_lDir_ne_bdK : lDir ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_lFln : bdK ≠ lFln := by decide
@[simp] theorem prd_lFln_ne_bdK : lFln ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_lFll : bdK ≠ lFll := by decide
@[simp] theorem prd_lFll_ne_bdK : lFll ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_lFls : bdK ≠ lFls := by decide
@[simp] theorem prd_lFls_ne_bdK : lFls ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_kFu : bdK ≠ kFu := by decide
@[simp] theorem prd_kFu_ne_bdK : kFu ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_kD : bdK ≠ kD := by decide
@[simp] theorem prd_kD_ne_bdK : kD ≠ bdK := by decide
@[simp] theorem prd_bdH_ne_bdK : bdH ≠ bdK := by decide
@[simp] theorem prd_bdH_ne_bdA : bdH ≠ bdA := by decide
@[simp] theorem prd_bdH_ne_bdB : bdH ≠ bdB := by decide
@[simp] theorem prd_bdH_ne_bdR : bdH ≠ bdR := by decide
@[simp] theorem prd_bdH_ne_lFl : bdH ≠ lFl := by decide
@[simp] theorem prd_lFl_ne_bdH : lFl ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_lDh : bdH ≠ lDh := by decide
@[simp] theorem prd_lDh_ne_bdH : lDh ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_lDt : bdH ≠ lDt := by decide
@[simp] theorem prd_lDt_ne_bdH : lDt ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_lDg : bdH ≠ lDg := by decide
@[simp] theorem prd_lDg_ne_bdH : lDg ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_lDi : bdH ≠ lDi := by decide
@[simp] theorem prd_lDi_ne_bdH : lDi ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_lRp : bdH ≠ lRp := by decide
@[simp] theorem prd_lRp_ne_bdH : lRp ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_lRn : bdH ≠ lRn := by decide
@[simp] theorem prd_lRn_ne_bdH : lRn ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_lFle : bdH ≠ lFle := by decide
@[simp] theorem prd_lFle_ne_bdH : lFle ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_lKb : bdH ≠ lKb := by decide
@[simp] theorem prd_lKb_ne_bdH : lKb ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_lDir : bdH ≠ lDir := by decide
@[simp] theorem prd_lDir_ne_bdH : lDir ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_lFln : bdH ≠ lFln := by decide
@[simp] theorem prd_lFln_ne_bdH : lFln ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_lFll : bdH ≠ lFll := by decide
@[simp] theorem prd_lFll_ne_bdH : lFll ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_lFls : bdH ≠ lFls := by decide
@[simp] theorem prd_lFls_ne_bdH : lFls ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_kFu : bdH ≠ kFu := by decide
@[simp] theorem prd_kFu_ne_bdH : kFu ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_kD : bdH ≠ kD := by decide
@[simp] theorem prd_kD_ne_bdH : kD ≠ bdH := by decide
@[simp] theorem prd_bdA_ne_bdK : bdA ≠ bdK := by decide
@[simp] theorem prd_bdA_ne_bdH : bdA ≠ bdH := by decide
@[simp] theorem prd_bdA_ne_bdB : bdA ≠ bdB := by decide
@[simp] theorem prd_bdA_ne_bdR : bdA ≠ bdR := by decide
@[simp] theorem prd_bdA_ne_lFl : bdA ≠ lFl := by decide
@[simp] theorem prd_lFl_ne_bdA : lFl ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_lDh : bdA ≠ lDh := by decide
@[simp] theorem prd_lDh_ne_bdA : lDh ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_lDt : bdA ≠ lDt := by decide
@[simp] theorem prd_lDt_ne_bdA : lDt ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_lDg : bdA ≠ lDg := by decide
@[simp] theorem prd_lDg_ne_bdA : lDg ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_lDi : bdA ≠ lDi := by decide
@[simp] theorem prd_lDi_ne_bdA : lDi ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_lRp : bdA ≠ lRp := by decide
@[simp] theorem prd_lRp_ne_bdA : lRp ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_lRn : bdA ≠ lRn := by decide
@[simp] theorem prd_lRn_ne_bdA : lRn ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_lFle : bdA ≠ lFle := by decide
@[simp] theorem prd_lFle_ne_bdA : lFle ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_lKb : bdA ≠ lKb := by decide
@[simp] theorem prd_lKb_ne_bdA : lKb ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_lDir : bdA ≠ lDir := by decide
@[simp] theorem prd_lDir_ne_bdA : lDir ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_lFln : bdA ≠ lFln := by decide
@[simp] theorem prd_lFln_ne_bdA : lFln ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_lFll : bdA ≠ lFll := by decide
@[simp] theorem prd_lFll_ne_bdA : lFll ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_lFls : bdA ≠ lFls := by decide
@[simp] theorem prd_lFls_ne_bdA : lFls ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_kFu : bdA ≠ kFu := by decide
@[simp] theorem prd_kFu_ne_bdA : kFu ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_kD : bdA ≠ kD := by decide
@[simp] theorem prd_kD_ne_bdA : kD ≠ bdA := by decide
@[simp] theorem prd_bdB_ne_bdK : bdB ≠ bdK := by decide
@[simp] theorem prd_bdB_ne_bdH : bdB ≠ bdH := by decide
@[simp] theorem prd_bdB_ne_bdA : bdB ≠ bdA := by decide
@[simp] theorem prd_bdB_ne_bdR : bdB ≠ bdR := by decide
@[simp] theorem prd_bdB_ne_lFl : bdB ≠ lFl := by decide
@[simp] theorem prd_lFl_ne_bdB : lFl ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_lDh : bdB ≠ lDh := by decide
@[simp] theorem prd_lDh_ne_bdB : lDh ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_lDt : bdB ≠ lDt := by decide
@[simp] theorem prd_lDt_ne_bdB : lDt ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_lDg : bdB ≠ lDg := by decide
@[simp] theorem prd_lDg_ne_bdB : lDg ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_lDi : bdB ≠ lDi := by decide
@[simp] theorem prd_lDi_ne_bdB : lDi ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_lRp : bdB ≠ lRp := by decide
@[simp] theorem prd_lRp_ne_bdB : lRp ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_lRn : bdB ≠ lRn := by decide
@[simp] theorem prd_lRn_ne_bdB : lRn ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_lFle : bdB ≠ lFle := by decide
@[simp] theorem prd_lFle_ne_bdB : lFle ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_lKb : bdB ≠ lKb := by decide
@[simp] theorem prd_lKb_ne_bdB : lKb ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_lDir : bdB ≠ lDir := by decide
@[simp] theorem prd_lDir_ne_bdB : lDir ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_lFln : bdB ≠ lFln := by decide
@[simp] theorem prd_lFln_ne_bdB : lFln ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_lFll : bdB ≠ lFll := by decide
@[simp] theorem prd_lFll_ne_bdB : lFll ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_lFls : bdB ≠ lFls := by decide
@[simp] theorem prd_lFls_ne_bdB : lFls ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_kFu : bdB ≠ kFu := by decide
@[simp] theorem prd_kFu_ne_bdB : kFu ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_kD : bdB ≠ kD := by decide
@[simp] theorem prd_kD_ne_bdB : kD ≠ bdB := by decide
@[simp] theorem prd_bdR_ne_bdK : bdR ≠ bdK := by decide
@[simp] theorem prd_bdR_ne_bdH : bdR ≠ bdH := by decide
@[simp] theorem prd_bdR_ne_bdA : bdR ≠ bdA := by decide
@[simp] theorem prd_bdR_ne_bdB : bdR ≠ bdB := by decide
@[simp] theorem prd_bdR_ne_lFl : bdR ≠ lFl := by decide
@[simp] theorem prd_lFl_ne_bdR : lFl ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_lDh : bdR ≠ lDh := by decide
@[simp] theorem prd_lDh_ne_bdR : lDh ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_lDt : bdR ≠ lDt := by decide
@[simp] theorem prd_lDt_ne_bdR : lDt ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_lDg : bdR ≠ lDg := by decide
@[simp] theorem prd_lDg_ne_bdR : lDg ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_lDi : bdR ≠ lDi := by decide
@[simp] theorem prd_lDi_ne_bdR : lDi ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_lRp : bdR ≠ lRp := by decide
@[simp] theorem prd_lRp_ne_bdR : lRp ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_lRn : bdR ≠ lRn := by decide
@[simp] theorem prd_lRn_ne_bdR : lRn ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_lFle : bdR ≠ lFle := by decide
@[simp] theorem prd_lFle_ne_bdR : lFle ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_lKb : bdR ≠ lKb := by decide
@[simp] theorem prd_lKb_ne_bdR : lKb ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_lDir : bdR ≠ lDir := by decide
@[simp] theorem prd_lDir_ne_bdR : lDir ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_lFln : bdR ≠ lFln := by decide
@[simp] theorem prd_lFln_ne_bdR : lFln ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_lFll : bdR ≠ lFll := by decide
@[simp] theorem prd_lFll_ne_bdR : lFll ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_lFls : bdR ≠ lFls := by decide
@[simp] theorem prd_lFls_ne_bdR : lFls ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_kFu : bdR ≠ kFu := by decide
@[simp] theorem prd_kFu_ne_bdR : kFu ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_kD : bdR ≠ kD := by decide
@[simp] theorem prd_kD_ne_bdR : kD ≠ bdR := by decide

def bdParams : List MlS := [bdK, bdH]
def bdLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, bdA, bdB, bdR]
def bdBody : ProgHOL 64 := prologue bdLocals (.ite (tagIsE bdH 6) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv bdH)) (.seq eViewP (.seq (.assign .local bdA (.load .one (vv lRp))) (.seq (.assign .local bdB (.load .one (.op .add [(vv lRp), (.const 8)]))) (.ite (.cmp .equal (vv bdK) (.const 0)) (.return (.op .add [(vv bdA), (.const 1)])) (.seq (.call (some (some (.local, bdR), none)) fBd [(.op .sub [(vv bdK), (.const 1)]), (vv bdB)]) (.return (vv bdR))))))))) (.return (.const 0)))

section
variable {σ : Type}

theorem bd_spec (C : Ctx) (hcb : C.code.lookup fBd = some (bdParams.map (fun p => (p, ShapeHOL.one)), bdBody, .one)) :
    ∀ k (h : EIdx) (s : AState), k < 2 ^ 64 →
      SpecR (σ := σ) (Pre C s (bdParams.zip [BitVec.ofNat 64 k, Enc.idxW h])) bdBody s (binderDom k h) (UD.PostO C) := by
  intro k
  induction k with
  | zero =>
    intro h s _
    refine specR_prologue (UD.postO_locals C) (Knot.params_none C bdLocals bdParams _ (by decide) (by decide)) ?_
    rw [binderDom]
    refine Knot.specR_tagIteV bdH h 6 (by decide) (by decide) (by simp +decide [Env.get, bdParams, ctxEnv])
      (fun htg => ?_) (fun htg => ?_)
    swap
    · rw [if_neg (show ¬ (h.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg)]
      exact specR_returnI _ (optW none) (by simp [optWG]; rfl)
        (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    rw [if_pos (show (h.tag == ETag.forallE) = true by simp [htg, ETag.forallE])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv bdH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, bdParams, ctxEnv]) ?_
    refine specR_viewP h (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
      (fun v P hv htn _ => ?_)
    have h6 : v.tagN = 6 := by rw [htn, htg]; rfl
    obtain ⟨ty, b, rfl⟩ : ∃ ty b, v = .forallE ty b := by
      cases v <;> simp [ENodeView.tagN] at h6 ⊢
    have hvb : s.store.viewBind h = some (ty, b) := viewBind_of_view_forallE (by rw [htg]; rfl) hv
    refine specR_runBind (by rw [viewBind_run, hvb]) ?_
    dsimp only
    refine specR_loadI' bdA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW ty) [Enc.idxW b] []) ?_
    refine specR_loadI' bdB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW b) [] []) ?_
    refine specR_dropM ?_

    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, bdParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ (optW (some ty)) (by simp [sev, optWG])
      (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro h s hk
    refine specR_prologue (UD.postO_locals C) (Knot.params_none C bdLocals bdParams _ (by decide) (by decide)) ?_
    rw [binderDom]
    refine Knot.specR_tagIteV bdH h 6 (by decide) (by decide) (by simp +decide [Env.get, bdParams, ctxEnv])
      (fun htg => ?_) (fun htg => ?_)
    swap
    · rw [if_neg (show ¬ (h.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg)]
      exact specR_returnI _ (optW none) (by simp [optWG]; rfl)
        (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    rw [if_pos (show (h.tag == ETag.forallE) = true by simp [htg, ETag.forallE])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv bdH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, bdParams, ctxEnv]) ?_
    refine specR_viewP h (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
      (fun v P hv htn _ => ?_)
    have h6 : v.tagN = 6 := by rw [htn, htg]; rfl
    obtain ⟨ty, b, rfl⟩ : ∃ ty b, v = .forallE ty b := by
      cases v <;> simp [ENodeView.tagN] at h6 ⊢
    have hvb : s.store.viewBind h = some (ty, b) := viewBind_of_view_forallE (by rw [htg]; rfl) hv
    refine specR_runBind (by rw [viewBind_run, hvb]) ?_
    dsimp only
    refine specR_loadI' bdA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW ty) [Enc.idxW b] []) ?_
    refine specR_loadI' bdB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW b) [] []) ?_
    refine specR_dropM ?_

    have hne : BitVec.ofNat 64 (k + 1) ≠ 0 := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, bdParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_callO bdR fBd bdParams [.op .sub [vv bdK, .const 1], vv bdB] bdBody
      [BitVec.ofNat 64 k, Enc.idxW b] (by decide) rfl (by decide) hcb
      ⟨by simp +decide [sev, Env.get, bdParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, by simp, trivial⟩
      (ih b s (by omega))

end

end ConPanqueque.T.WC
