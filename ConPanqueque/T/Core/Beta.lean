import ConPanqueque.T.Core.Spine
import ConPanqueque.T.Ex.InstListGo
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `betaPeel`: one batched β

Peel consecutive λ binders over the arguments `args[i..]`, then substitute the peeled range `args[s..i]` in one
walk (`instantiateRevRange`) and apply the rest (`mkAppNFrom`). A recursive function over `i`.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

theorem viewBind_of_view_lam {st : EStore} {i ty b : EIdx}
    (htg : i.tag = ETag.lam) (h : st.view i = some (.lam ty b)) : st.viewBind i = some (ty, b) := by
  cases hc : st.viewBind i with
  | some p =>
    obtain ⟨ty', b'⟩ := p
    have := ConRon.Bridge.view_of_viewBind_lam htg hc
    rw [h] at this; cases this; rfl
  | none =>
    exfalso
    revert h hc
    simp only [EStore.view, EStore.viewBind, EStore.persGetBind]
    split <;> [skip; split] <;> simp [ETables.get, ETables.getBind, htg] <;>
      (simp only [show ETag.lam ≠ ETag.bvar by decide, show ETag.lam ≠ ETag.fvar by decide,
        show ETag.lam ≠ ETag.sort by decide, show ETag.lam ≠ ETag.const by decide,
        show ETag.lam ≠ ETag.app by decide, ite_false]; intro h1 h2; rw [h2] at h1; simp at h1)


def bT := ofString "bpt"
def bS := ofString "bps"
def bA := ofString "bpa"
def bI := ofString "bpi"
def bN := ofString "bpn"
def bB := ofString "bpb"
def bE2 := ofString "bpe2"
def bE3 := ofString "bpe3"
def bR := ofString "bpr"
def fBp := ofString "betaPeel"

@[simp] theorem bp_bT_ne_bS : bT ≠ bS := by decide
@[simp] theorem bp_bT_ne_bA : bT ≠ bA := by decide
@[simp] theorem bp_bT_ne_bI : bT ≠ bI := by decide
@[simp] theorem bp_bT_ne_bN : bT ≠ bN := by decide
@[simp] theorem bp_bT_ne_bB : bT ≠ bB := by decide
@[simp] theorem bp_bT_ne_bE2 : bT ≠ bE2 := by decide
@[simp] theorem bp_bT_ne_bE3 : bT ≠ bE3 := by decide
@[simp] theorem bp_bT_ne_bR : bT ≠ bR := by decide
@[simp] theorem bp_bT_ne_lFl : bT ≠ lFl := by decide
@[simp] theorem bp_lFl_ne_bT : lFl ≠ bT := by decide
@[simp] theorem bp_bT_ne_lDh : bT ≠ lDh := by decide
@[simp] theorem bp_lDh_ne_bT : lDh ≠ bT := by decide
@[simp] theorem bp_bT_ne_lDt : bT ≠ lDt := by decide
@[simp] theorem bp_lDt_ne_bT : lDt ≠ bT := by decide
@[simp] theorem bp_bT_ne_lDg : bT ≠ lDg := by decide
@[simp] theorem bp_lDg_ne_bT : lDg ≠ bT := by decide
@[simp] theorem bp_bT_ne_lDi : bT ≠ lDi := by decide
@[simp] theorem bp_lDi_ne_bT : lDi ≠ bT := by decide
@[simp] theorem bp_bT_ne_lRp : bT ≠ lRp := by decide
@[simp] theorem bp_lRp_ne_bT : lRp ≠ bT := by decide
@[simp] theorem bp_bT_ne_lRn : bT ≠ lRn := by decide
@[simp] theorem bp_lRn_ne_bT : lRn ≠ bT := by decide
@[simp] theorem bp_bT_ne_lFle : bT ≠ lFle := by decide
@[simp] theorem bp_lFle_ne_bT : lFle ≠ bT := by decide
@[simp] theorem bp_bT_ne_lDir : bT ≠ lDir := by decide
@[simp] theorem bp_lDir_ne_bT : lDir ≠ bT := by decide
@[simp] theorem bp_bT_ne_lKb : bT ≠ lKb := by decide
@[simp] theorem bp_lKb_ne_bT : lKb ≠ bT := by decide
@[simp] theorem bp_bS_ne_bT : bS ≠ bT := by decide
@[simp] theorem bp_bS_ne_bA : bS ≠ bA := by decide
@[simp] theorem bp_bS_ne_bI : bS ≠ bI := by decide
@[simp] theorem bp_bS_ne_bN : bS ≠ bN := by decide
@[simp] theorem bp_bS_ne_bB : bS ≠ bB := by decide
@[simp] theorem bp_bS_ne_bE2 : bS ≠ bE2 := by decide
@[simp] theorem bp_bS_ne_bE3 : bS ≠ bE3 := by decide
@[simp] theorem bp_bS_ne_bR : bS ≠ bR := by decide
@[simp] theorem bp_bS_ne_lFl : bS ≠ lFl := by decide
@[simp] theorem bp_lFl_ne_bS : lFl ≠ bS := by decide
@[simp] theorem bp_bS_ne_lDh : bS ≠ lDh := by decide
@[simp] theorem bp_lDh_ne_bS : lDh ≠ bS := by decide
@[simp] theorem bp_bS_ne_lDt : bS ≠ lDt := by decide
@[simp] theorem bp_lDt_ne_bS : lDt ≠ bS := by decide
@[simp] theorem bp_bS_ne_lDg : bS ≠ lDg := by decide
@[simp] theorem bp_lDg_ne_bS : lDg ≠ bS := by decide
@[simp] theorem bp_bS_ne_lDi : bS ≠ lDi := by decide
@[simp] theorem bp_lDi_ne_bS : lDi ≠ bS := by decide
@[simp] theorem bp_bS_ne_lRp : bS ≠ lRp := by decide
@[simp] theorem bp_lRp_ne_bS : lRp ≠ bS := by decide
@[simp] theorem bp_bS_ne_lRn : bS ≠ lRn := by decide
@[simp] theorem bp_lRn_ne_bS : lRn ≠ bS := by decide
@[simp] theorem bp_bS_ne_lFle : bS ≠ lFle := by decide
@[simp] theorem bp_lFle_ne_bS : lFle ≠ bS := by decide
@[simp] theorem bp_bS_ne_lDir : bS ≠ lDir := by decide
@[simp] theorem bp_lDir_ne_bS : lDir ≠ bS := by decide
@[simp] theorem bp_bS_ne_lKb : bS ≠ lKb := by decide
@[simp] theorem bp_lKb_ne_bS : lKb ≠ bS := by decide
@[simp] theorem bp_bA_ne_bT : bA ≠ bT := by decide
@[simp] theorem bp_bA_ne_bS : bA ≠ bS := by decide
@[simp] theorem bp_bA_ne_bI : bA ≠ bI := by decide
@[simp] theorem bp_bA_ne_bN : bA ≠ bN := by decide
@[simp] theorem bp_bA_ne_bB : bA ≠ bB := by decide
@[simp] theorem bp_bA_ne_bE2 : bA ≠ bE2 := by decide
@[simp] theorem bp_bA_ne_bE3 : bA ≠ bE3 := by decide
@[simp] theorem bp_bA_ne_bR : bA ≠ bR := by decide
@[simp] theorem bp_bA_ne_lFl : bA ≠ lFl := by decide
@[simp] theorem bp_lFl_ne_bA : lFl ≠ bA := by decide
@[simp] theorem bp_bA_ne_lDh : bA ≠ lDh := by decide
@[simp] theorem bp_lDh_ne_bA : lDh ≠ bA := by decide
@[simp] theorem bp_bA_ne_lDt : bA ≠ lDt := by decide
@[simp] theorem bp_lDt_ne_bA : lDt ≠ bA := by decide
@[simp] theorem bp_bA_ne_lDg : bA ≠ lDg := by decide
@[simp] theorem bp_lDg_ne_bA : lDg ≠ bA := by decide
@[simp] theorem bp_bA_ne_lDi : bA ≠ lDi := by decide
@[simp] theorem bp_lDi_ne_bA : lDi ≠ bA := by decide
@[simp] theorem bp_bA_ne_lRp : bA ≠ lRp := by decide
@[simp] theorem bp_lRp_ne_bA : lRp ≠ bA := by decide
@[simp] theorem bp_bA_ne_lRn : bA ≠ lRn := by decide
@[simp] theorem bp_lRn_ne_bA : lRn ≠ bA := by decide
@[simp] theorem bp_bA_ne_lFle : bA ≠ lFle := by decide
@[simp] theorem bp_lFle_ne_bA : lFle ≠ bA := by decide
@[simp] theorem bp_bA_ne_lDir : bA ≠ lDir := by decide
@[simp] theorem bp_lDir_ne_bA : lDir ≠ bA := by decide
@[simp] theorem bp_bA_ne_lKb : bA ≠ lKb := by decide
@[simp] theorem bp_lKb_ne_bA : lKb ≠ bA := by decide
@[simp] theorem bp_bI_ne_bT : bI ≠ bT := by decide
@[simp] theorem bp_bI_ne_bS : bI ≠ bS := by decide
@[simp] theorem bp_bI_ne_bA : bI ≠ bA := by decide
@[simp] theorem bp_bI_ne_bN : bI ≠ bN := by decide
@[simp] theorem bp_bI_ne_bB : bI ≠ bB := by decide
@[simp] theorem bp_bI_ne_bE2 : bI ≠ bE2 := by decide
@[simp] theorem bp_bI_ne_bE3 : bI ≠ bE3 := by decide
@[simp] theorem bp_bI_ne_bR : bI ≠ bR := by decide
@[simp] theorem bp_bI_ne_lFl : bI ≠ lFl := by decide
@[simp] theorem bp_lFl_ne_bI : lFl ≠ bI := by decide
@[simp] theorem bp_bI_ne_lDh : bI ≠ lDh := by decide
@[simp] theorem bp_lDh_ne_bI : lDh ≠ bI := by decide
@[simp] theorem bp_bI_ne_lDt : bI ≠ lDt := by decide
@[simp] theorem bp_lDt_ne_bI : lDt ≠ bI := by decide
@[simp] theorem bp_bI_ne_lDg : bI ≠ lDg := by decide
@[simp] theorem bp_lDg_ne_bI : lDg ≠ bI := by decide
@[simp] theorem bp_bI_ne_lDi : bI ≠ lDi := by decide
@[simp] theorem bp_lDi_ne_bI : lDi ≠ bI := by decide
@[simp] theorem bp_bI_ne_lRp : bI ≠ lRp := by decide
@[simp] theorem bp_lRp_ne_bI : lRp ≠ bI := by decide
@[simp] theorem bp_bI_ne_lRn : bI ≠ lRn := by decide
@[simp] theorem bp_lRn_ne_bI : lRn ≠ bI := by decide
@[simp] theorem bp_bI_ne_lFle : bI ≠ lFle := by decide
@[simp] theorem bp_lFle_ne_bI : lFle ≠ bI := by decide
@[simp] theorem bp_bI_ne_lDir : bI ≠ lDir := by decide
@[simp] theorem bp_lDir_ne_bI : lDir ≠ bI := by decide
@[simp] theorem bp_bI_ne_lKb : bI ≠ lKb := by decide
@[simp] theorem bp_lKb_ne_bI : lKb ≠ bI := by decide
@[simp] theorem bp_bN_ne_bT : bN ≠ bT := by decide
@[simp] theorem bp_bN_ne_bS : bN ≠ bS := by decide
@[simp] theorem bp_bN_ne_bA : bN ≠ bA := by decide
@[simp] theorem bp_bN_ne_bI : bN ≠ bI := by decide
@[simp] theorem bp_bN_ne_bB : bN ≠ bB := by decide
@[simp] theorem bp_bN_ne_bE2 : bN ≠ bE2 := by decide
@[simp] theorem bp_bN_ne_bE3 : bN ≠ bE3 := by decide
@[simp] theorem bp_bN_ne_bR : bN ≠ bR := by decide
@[simp] theorem bp_bN_ne_lFl : bN ≠ lFl := by decide
@[simp] theorem bp_lFl_ne_bN : lFl ≠ bN := by decide
@[simp] theorem bp_bN_ne_lDh : bN ≠ lDh := by decide
@[simp] theorem bp_lDh_ne_bN : lDh ≠ bN := by decide
@[simp] theorem bp_bN_ne_lDt : bN ≠ lDt := by decide
@[simp] theorem bp_lDt_ne_bN : lDt ≠ bN := by decide
@[simp] theorem bp_bN_ne_lDg : bN ≠ lDg := by decide
@[simp] theorem bp_lDg_ne_bN : lDg ≠ bN := by decide
@[simp] theorem bp_bN_ne_lDi : bN ≠ lDi := by decide
@[simp] theorem bp_lDi_ne_bN : lDi ≠ bN := by decide
@[simp] theorem bp_bN_ne_lRp : bN ≠ lRp := by decide
@[simp] theorem bp_lRp_ne_bN : lRp ≠ bN := by decide
@[simp] theorem bp_bN_ne_lRn : bN ≠ lRn := by decide
@[simp] theorem bp_lRn_ne_bN : lRn ≠ bN := by decide
@[simp] theorem bp_bN_ne_lFle : bN ≠ lFle := by decide
@[simp] theorem bp_lFle_ne_bN : lFle ≠ bN := by decide
@[simp] theorem bp_bN_ne_lDir : bN ≠ lDir := by decide
@[simp] theorem bp_lDir_ne_bN : lDir ≠ bN := by decide
@[simp] theorem bp_bN_ne_lKb : bN ≠ lKb := by decide
@[simp] theorem bp_lKb_ne_bN : lKb ≠ bN := by decide
@[simp] theorem bp_bB_ne_bT : bB ≠ bT := by decide
@[simp] theorem bp_bB_ne_bS : bB ≠ bS := by decide
@[simp] theorem bp_bB_ne_bA : bB ≠ bA := by decide
@[simp] theorem bp_bB_ne_bI : bB ≠ bI := by decide
@[simp] theorem bp_bB_ne_bN : bB ≠ bN := by decide
@[simp] theorem bp_bB_ne_bE2 : bB ≠ bE2 := by decide
@[simp] theorem bp_bB_ne_bE3 : bB ≠ bE3 := by decide
@[simp] theorem bp_bB_ne_bR : bB ≠ bR := by decide
@[simp] theorem bp_bB_ne_lFl : bB ≠ lFl := by decide
@[simp] theorem bp_lFl_ne_bB : lFl ≠ bB := by decide
@[simp] theorem bp_bB_ne_lDh : bB ≠ lDh := by decide
@[simp] theorem bp_lDh_ne_bB : lDh ≠ bB := by decide
@[simp] theorem bp_bB_ne_lDt : bB ≠ lDt := by decide
@[simp] theorem bp_lDt_ne_bB : lDt ≠ bB := by decide
@[simp] theorem bp_bB_ne_lDg : bB ≠ lDg := by decide
@[simp] theorem bp_lDg_ne_bB : lDg ≠ bB := by decide
@[simp] theorem bp_bB_ne_lDi : bB ≠ lDi := by decide
@[simp] theorem bp_lDi_ne_bB : lDi ≠ bB := by decide
@[simp] theorem bp_bB_ne_lRp : bB ≠ lRp := by decide
@[simp] theorem bp_lRp_ne_bB : lRp ≠ bB := by decide
@[simp] theorem bp_bB_ne_lRn : bB ≠ lRn := by decide
@[simp] theorem bp_lRn_ne_bB : lRn ≠ bB := by decide
@[simp] theorem bp_bB_ne_lFle : bB ≠ lFle := by decide
@[simp] theorem bp_lFle_ne_bB : lFle ≠ bB := by decide
@[simp] theorem bp_bB_ne_lDir : bB ≠ lDir := by decide
@[simp] theorem bp_lDir_ne_bB : lDir ≠ bB := by decide
@[simp] theorem bp_bB_ne_lKb : bB ≠ lKb := by decide
@[simp] theorem bp_lKb_ne_bB : lKb ≠ bB := by decide
@[simp] theorem bp_bE2_ne_bT : bE2 ≠ bT := by decide
@[simp] theorem bp_bE2_ne_bS : bE2 ≠ bS := by decide
@[simp] theorem bp_bE2_ne_bA : bE2 ≠ bA := by decide
@[simp] theorem bp_bE2_ne_bI : bE2 ≠ bI := by decide
@[simp] theorem bp_bE2_ne_bN : bE2 ≠ bN := by decide
@[simp] theorem bp_bE2_ne_bB : bE2 ≠ bB := by decide
@[simp] theorem bp_bE2_ne_bE3 : bE2 ≠ bE3 := by decide
@[simp] theorem bp_bE2_ne_bR : bE2 ≠ bR := by decide
@[simp] theorem bp_bE2_ne_lFl : bE2 ≠ lFl := by decide
@[simp] theorem bp_lFl_ne_bE2 : lFl ≠ bE2 := by decide
@[simp] theorem bp_bE2_ne_lDh : bE2 ≠ lDh := by decide
@[simp] theorem bp_lDh_ne_bE2 : lDh ≠ bE2 := by decide
@[simp] theorem bp_bE2_ne_lDt : bE2 ≠ lDt := by decide
@[simp] theorem bp_lDt_ne_bE2 : lDt ≠ bE2 := by decide
@[simp] theorem bp_bE2_ne_lDg : bE2 ≠ lDg := by decide
@[simp] theorem bp_lDg_ne_bE2 : lDg ≠ bE2 := by decide
@[simp] theorem bp_bE2_ne_lDi : bE2 ≠ lDi := by decide
@[simp] theorem bp_lDi_ne_bE2 : lDi ≠ bE2 := by decide
@[simp] theorem bp_bE2_ne_lRp : bE2 ≠ lRp := by decide
@[simp] theorem bp_lRp_ne_bE2 : lRp ≠ bE2 := by decide
@[simp] theorem bp_bE2_ne_lRn : bE2 ≠ lRn := by decide
@[simp] theorem bp_lRn_ne_bE2 : lRn ≠ bE2 := by decide
@[simp] theorem bp_bE2_ne_lFle : bE2 ≠ lFle := by decide
@[simp] theorem bp_lFle_ne_bE2 : lFle ≠ bE2 := by decide
@[simp] theorem bp_bE2_ne_lDir : bE2 ≠ lDir := by decide
@[simp] theorem bp_lDir_ne_bE2 : lDir ≠ bE2 := by decide
@[simp] theorem bp_bE2_ne_lKb : bE2 ≠ lKb := by decide
@[simp] theorem bp_lKb_ne_bE2 : lKb ≠ bE2 := by decide
@[simp] theorem bp_bE3_ne_bT : bE3 ≠ bT := by decide
@[simp] theorem bp_bE3_ne_bS : bE3 ≠ bS := by decide
@[simp] theorem bp_bE3_ne_bA : bE3 ≠ bA := by decide
@[simp] theorem bp_bE3_ne_bI : bE3 ≠ bI := by decide
@[simp] theorem bp_bE3_ne_bN : bE3 ≠ bN := by decide
@[simp] theorem bp_bE3_ne_bB : bE3 ≠ bB := by decide
@[simp] theorem bp_bE3_ne_bE2 : bE3 ≠ bE2 := by decide
@[simp] theorem bp_bE3_ne_bR : bE3 ≠ bR := by decide
@[simp] theorem bp_bE3_ne_lFl : bE3 ≠ lFl := by decide
@[simp] theorem bp_lFl_ne_bE3 : lFl ≠ bE3 := by decide
@[simp] theorem bp_bE3_ne_lDh : bE3 ≠ lDh := by decide
@[simp] theorem bp_lDh_ne_bE3 : lDh ≠ bE3 := by decide
@[simp] theorem bp_bE3_ne_lDt : bE3 ≠ lDt := by decide
@[simp] theorem bp_lDt_ne_bE3 : lDt ≠ bE3 := by decide
@[simp] theorem bp_bE3_ne_lDg : bE3 ≠ lDg := by decide
@[simp] theorem bp_lDg_ne_bE3 : lDg ≠ bE3 := by decide
@[simp] theorem bp_bE3_ne_lDi : bE3 ≠ lDi := by decide
@[simp] theorem bp_lDi_ne_bE3 : lDi ≠ bE3 := by decide
@[simp] theorem bp_bE3_ne_lRp : bE3 ≠ lRp := by decide
@[simp] theorem bp_lRp_ne_bE3 : lRp ≠ bE3 := by decide
@[simp] theorem bp_bE3_ne_lRn : bE3 ≠ lRn := by decide
@[simp] theorem bp_lRn_ne_bE3 : lRn ≠ bE3 := by decide
@[simp] theorem bp_bE3_ne_lFle : bE3 ≠ lFle := by decide
@[simp] theorem bp_lFle_ne_bE3 : lFle ≠ bE3 := by decide
@[simp] theorem bp_bE3_ne_lDir : bE3 ≠ lDir := by decide
@[simp] theorem bp_lDir_ne_bE3 : lDir ≠ bE3 := by decide
@[simp] theorem bp_bE3_ne_lKb : bE3 ≠ lKb := by decide
@[simp] theorem bp_lKb_ne_bE3 : lKb ≠ bE3 := by decide
@[simp] theorem bp_bR_ne_bT : bR ≠ bT := by decide
@[simp] theorem bp_bR_ne_bS : bR ≠ bS := by decide
@[simp] theorem bp_bR_ne_bA : bR ≠ bA := by decide
@[simp] theorem bp_bR_ne_bI : bR ≠ bI := by decide
@[simp] theorem bp_bR_ne_bN : bR ≠ bN := by decide
@[simp] theorem bp_bR_ne_bB : bR ≠ bB := by decide
@[simp] theorem bp_bR_ne_bE2 : bR ≠ bE2 := by decide
@[simp] theorem bp_bR_ne_bE3 : bR ≠ bE3 := by decide
@[simp] theorem bp_bR_ne_lFl : bR ≠ lFl := by decide
@[simp] theorem bp_lFl_ne_bR : lFl ≠ bR := by decide
@[simp] theorem bp_bR_ne_lDh : bR ≠ lDh := by decide
@[simp] theorem bp_lDh_ne_bR : lDh ≠ bR := by decide
@[simp] theorem bp_bR_ne_lDt : bR ≠ lDt := by decide
@[simp] theorem bp_lDt_ne_bR : lDt ≠ bR := by decide
@[simp] theorem bp_bR_ne_lDg : bR ≠ lDg := by decide
@[simp] theorem bp_lDg_ne_bR : lDg ≠ bR := by decide
@[simp] theorem bp_bR_ne_lDi : bR ≠ lDi := by decide
@[simp] theorem bp_lDi_ne_bR : lDi ≠ bR := by decide
@[simp] theorem bp_bR_ne_lRp : bR ≠ lRp := by decide
@[simp] theorem bp_lRp_ne_bR : lRp ≠ bR := by decide
@[simp] theorem bp_bR_ne_lRn : bR ≠ lRn := by decide
@[simp] theorem bp_lRn_ne_bR : lRn ≠ bR := by decide
@[simp] theorem bp_bR_ne_lFle : bR ≠ lFle := by decide
@[simp] theorem bp_lFle_ne_bR : lFle ≠ bR := by decide
@[simp] theorem bp_bR_ne_lDir : bR ≠ lDir := by decide
@[simp] theorem bp_lDir_ne_bR : lDir ≠ bR := by decide
@[simp] theorem bp_bR_ne_lKb : bR ≠ lKb := by decide
@[simp] theorem bp_lKb_ne_bR : lKb ≠ bR := by decide

def bpParams : List MlS := [bT, bS, bA, bI, bN]
def bpLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, bB, bE2, bE3, bR]

def bpCore : ProgHOL 64 :=
  .ite (.cmp .lower (vv bI) (vv bN))
    (.ite (tagIsE bT 5)
      (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv bT)) (.seq eViewP
      (.seq (.assign .local bB (.load .one (.op .add [vv lRp, .const 8])))
      (.seq (.call (some (some (.local, bR), none)) fBp [vv bB, vv bS, vv bA, .op .add [vv bI, .const 1], vv bN])
        (.return (vv bR)))))))
      (.seq (.call (some (some (.local, bE2), none)) ExQ.fIrr
        [vv bA, vv bS, vv bI, .const (BitVec.ofNat 64 coreWalkFuel), vv bT, .const 0])
      (.seq (.call (some (some (.local, bE3), none)) ExK.fMka [vv bE2, vv bA, vv bI, vv bN])
        (.return (.op .add [.shift .lsl (vv bE3) (.const 1), .const 1])))))
    (.seq (.call (some (some (.local, bE2), none)) ExQ.fIrr
      [vv bA, vv bS, vv bI, .const (BitVec.ofNat 64 coreWalkFuel), vv bT, .const 0])
      (.return (.op .add [.shift .lsl (vv bE2) (.const 1), .const 1])))

def bpBody : ProgHOL 64 := prologue bpLocals bpCore

section
variable {σ : Type}

theorem bp_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ bpLocals → (ctxEnv C ++ bpParams.zip vals).get x = none :=
  Knot.params_none C bpLocals bpParams vals (by decide) (by decide)

theorem viewBind_run (h : EIdx) (s : AState) : viewBind h s = .ok (s.store.viewBind h, s) := rfl

theorem bp_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : ExQ.CodesQ C)
    (hcb : C.code.lookup fBp = some (bpParams.map (fun p => (p, ShapeHOL.one)), bpBody, .one))
    (hci : C.code.lookup ExQ.fIrr = some (ExQ.irrParams.map (fun p => (p, ShapeHOL.one)), ExQ.irrBody C, .one))
    (hcm : C.code.lookup ExK.fMka = some ([(ExK.pF, .one), (ExK.pP, .one), (ExK.pI, .one), (ExK.pN, .one)],
      ExK.mkaBody, .one))
    (hcI : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one))
    (args : Array EIdx) (o : Nat) (hblk : BlkAt C.H o (args.toList.map Enc.idxW)) (hsz : args.size < 2 ^ 59)
    (st : Nat) (hst : st < 2 ^ 63) :
    ∀ k (t : EIdx) (i : Nat) (s : AState), args.size - i = k → i ≤ args.size →
      SpecR (σ := σ) (Pre C s (bpParams.zip [Enc.idxW t, BitVec.ofNat 64 st, cellA C o, BitVec.ofNat 64 i,
        BitVec.ofNat 64 args.size])) bpBody s (betaPeel t st args i) (PostWS C) := by
  intro k
  induction k with
  | zero =>
    intro t i s hk hi
    have hi' : i = args.size := by omega
    refine specR_prologue (postWS_locals C) (bp_none C _) ?_
    unfold bpCore
    rw [betaPeel, dif_neg (by omega)]
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, bpParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hi'])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine ILP.callE_spec bE2 ExQ.fIrr ExQ.irrParams
        [vv bA, vv bS, vv bI, .const (BitVec.ofNat 64 coreWalkFuel), vv bT, .const 0] (ExQ.irrBody C)
        [cellA C o, BitVec.ofNat 64 st, BitVec.ofNat 64 i, BitVec.ofNat 64 coreWalkFuel, Enc.idxW t, BitVec.ofNat 64 0]
        (by decide) rfl (by decide) hci
        ⟨by simp +decide [Env.get, bpParams, ctxEnv], by simp +decide [Env.get, bpParams, ctxEnv],
          by simp +decide [Env.get, bpParams, ctxEnv], rfl, by simp +decide [Env.get, bpParams, ctxEnv], rfl, trivial⟩
        (ExQ.irr_spec ra C hok hc args o hblk hsz s coreWalkFuel st i 0 t CV.coreWalkFuel_lt hst (by omega) (by decide)) (fun e2 s1 => ?_)
    exact specR_returnI _ (encWS (.cont e2)) (by simp [sev, vv, encWS]) (fun t ht =>
      ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro t i s hk hi
    have hlt : i < args.size := by omega
    refine specR_prologue (postWS_locals C) (bp_none C _) ?_
    unfold bpCore
    rw [betaPeel, dif_pos hlt]
    have hlw := word_lt_iff i args.size (by unfold B; omega) (by unfold B; omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, bpParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
      hlw.mpr hlt]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine Knot.specR_tagIteV bT t 5 (by decide) (by decide) (by simp +decide [Env.get, bpParams, ctxEnv])
      (fun htg => ?_) (fun htg => ?_)
    · rw [if_pos (show (t.tag == ETag.lam) = true by simp [htg, ETag.lam])]
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
      refine specR_assignI lDh (vv bT) (Enc.idxW t) (by decide) (by simp +decide [Env.get, bpParams, ctxEnv]) ?_
      refine specR_viewP t (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
        (fun v P hv htn _ => ?_)
      have h5 : v.tagN = 5 := by rw [htn, htg]; rfl
      obtain ⟨ty, b, rfl⟩ : ∃ ty b, v = .lam ty b := by
        cases v <;> simp [ENodeView.tagN] at h5 ⊢
      have hvb : s.store.viewBind t = some (ty, b) := viewBind_of_view_lam (by rw [htg]; rfl) hv
      refine specR_runBind (by rw [viewBind_run, hvb]) ?_
      refine specR_loadI' bB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      exact specR_callWS bR fBp bpParams [vv bB, vv bS, vv bA, .op .add [vv bI, .const 1], vv bN] bpBody
        [Enc.idxW b, BitVec.ofNat 64 st, cellA C o, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 args.size] (by decide)
        rfl (by decide) hcb
        ⟨by simp, by simp +decide [Env.get, bpParams, ctxEnv], by simp +decide [Env.get, bpParams, ctxEnv],
          by simp +decide [sev, Env.get, bpParams, ctxEnv]; exact word_add1_eq i,
          by simp +decide [Env.get, bpParams, ctxEnv], trivial⟩
        (ih b (i + 1) s (by omega) (by omega))
    · rw [if_neg (show ¬ (t.tag == ETag.lam) = true by simpa [ETag.lam] using htg)]
      refine ILP.callE_spec bE2 ExQ.fIrr ExQ.irrParams
        [vv bA, vv bS, vv bI, .const (BitVec.ofNat 64 coreWalkFuel), vv bT, .const 0] (ExQ.irrBody C)
        [cellA C o, BitVec.ofNat 64 st, BitVec.ofNat 64 i, BitVec.ofNat 64 coreWalkFuel, Enc.idxW t, BitVec.ofNat 64 0]
        (by decide) rfl (by decide) hci
        ⟨by simp +decide [Env.get, bpParams, ctxEnv], by simp +decide [Env.get, bpParams, ctxEnv],
          by simp +decide [Env.get, bpParams, ctxEnv], rfl, by simp +decide [Env.get, bpParams, ctxEnv], rfl, trivial⟩
        (ExQ.irr_spec ra C hok hc args o hblk hsz s coreWalkFuel st i 0 t CV.coreWalkFuel_lt hst (by omega) (by decide)) (fun e2 s1 => ?_)
      refine ILP.callE_spec bE3 ExK.fMka [ExK.pF, ExK.pP, ExK.pI, ExK.pN] [vv bE2, vv bA, vv bI, vv bN] ExK.mkaBody
        [Enc.idxW e2, cellA C o, BitVec.ofNat 64 i, BitVec.ofNat 64 args.toList.length] (by decide) rfl (by decide)
        hcm ⟨by simp, by simp +decide [Env.get, bpParams, ctxEnv], by simp +decide [Env.get, bpParams, ctxEnv],
          by simp +decide [Env.get, bpParams, ctxEnv], trivial⟩
        (ExK.mkAppNFrom_spec ra C hok hcm hcI o args hblk hsz i (by omega) e2 s1) (fun e3 s2 => ?_)
      exact specR_returnI _ (encWS (.cont e3)) (by simp [sev, vv, encWS]) (fun t ht =>
        ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
