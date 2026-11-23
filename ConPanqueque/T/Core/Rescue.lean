import ConPanqueque.T.Core.RescueTwin
import ConPanqueque.T.Core.PrepMajor
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `majorToCtorRescue`: the dispatch

A single rule; its constructor's record; the constructor's family's record; then the K branch, or the
structure-η branch at the table `etaRescueTable?` finds, or the `And` branch (each a callee). Every miss answers
the major itself.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def rsN := ofString "rsn"
def rsQ := ofString "rsq"
def rsC := ofString "rsc"
def rsW := ofString "rsw"
def rsJ := ofString "rsj"
def rsTg := ofString "rstg"
def rsT := ofString "rst"
def rsV := ofString "rsv"
def rsF := ofString "rsf"
def rsTg2 := ofString "rstg2"
def rsE := ofString "rse"
def rsX := ofString "rsx"
def fRk := ofString "rescueK"
def fRe := ofString "rescueEta"
def fRa := ofString "rescueAnd"
def rkR := ofString "rkr"
def rkJ := ofString "rkj"
def rkT := ofString "rkt"
def rkM := ofString "rkm"
def reF := ofString "ref"
def reO := ofString "reo"
def rkParams : List MlS := [kFu, kD, rkR, rkJ, rkT, rkM]
def reParams : List MlS := [kFu, kD, rkR, rkJ, rkT, rkM, reF, reO]

@[simp] theorem rs_rsN_ne_rsQ : rsN ≠ rsQ := by decide
@[simp] theorem rs_rsN_ne_rsC : rsN ≠ rsC := by decide
@[simp] theorem rs_rsN_ne_rsW : rsN ≠ rsW := by decide
@[simp] theorem rs_rsN_ne_rsJ : rsN ≠ rsJ := by decide
@[simp] theorem rs_rsN_ne_rsTg : rsN ≠ rsTg := by decide
@[simp] theorem rs_rsN_ne_rsT : rsN ≠ rsT := by decide
@[simp] theorem rs_rsN_ne_rsV : rsN ≠ rsV := by decide
@[simp] theorem rs_rsN_ne_rsF : rsN ≠ rsF := by decide
@[simp] theorem rs_rsN_ne_rsTg2 : rsN ≠ rsTg2 := by decide
@[simp] theorem rs_rsN_ne_rsE : rsN ≠ rsE := by decide
@[simp] theorem rs_rsN_ne_rsX : rsN ≠ rsX := by decide
@[simp] theorem rs_rsN_ne_kFu : rsN ≠ kFu := by decide
@[simp] theorem rs_kFu_ne_rsN : kFu ≠ rsN := by decide
@[simp] theorem rs_rsN_ne_kD : rsN ≠ kD := by decide
@[simp] theorem rs_kD_ne_rsN : kD ≠ rsN := by decide
@[simp] theorem rs_rsN_ne_pmC : rsN ≠ pmC := by decide
@[simp] theorem rs_pmC_ne_rsN : pmC ≠ rsN := by decide
@[simp] theorem rs_rsN_ne_pmK : rsN ≠ pmK := by decide
@[simp] theorem rs_pmK_ne_rsN : pmK ≠ rsN := by decide
@[simp] theorem rs_rsN_ne_pmR : rsN ≠ pmR := by decide
@[simp] theorem rs_pmR_ne_rsN : pmR ≠ rsN := by decide
@[simp] theorem rs_rsN_ne_pmM : rsN ≠ pmM := by decide
@[simp] theorem rs_pmM_ne_rsN : pmM ≠ rsN := by decide
@[simp] theorem rs_rsN_ne_lKb : rsN ≠ lKb := by decide
@[simp] theorem rs_lKb_ne_rsN : lKb ≠ rsN := by decide
@[simp] theorem rs_rsQ_ne_rsN : rsQ ≠ rsN := by decide
@[simp] theorem rs_rsQ_ne_rsC : rsQ ≠ rsC := by decide
@[simp] theorem rs_rsQ_ne_rsW : rsQ ≠ rsW := by decide
@[simp] theorem rs_rsQ_ne_rsJ : rsQ ≠ rsJ := by decide
@[simp] theorem rs_rsQ_ne_rsTg : rsQ ≠ rsTg := by decide
@[simp] theorem rs_rsQ_ne_rsT : rsQ ≠ rsT := by decide
@[simp] theorem rs_rsQ_ne_rsV : rsQ ≠ rsV := by decide
@[simp] theorem rs_rsQ_ne_rsF : rsQ ≠ rsF := by decide
@[simp] theorem rs_rsQ_ne_rsTg2 : rsQ ≠ rsTg2 := by decide
@[simp] theorem rs_rsQ_ne_rsE : rsQ ≠ rsE := by decide
@[simp] theorem rs_rsQ_ne_rsX : rsQ ≠ rsX := by decide
@[simp] theorem rs_rsQ_ne_kFu : rsQ ≠ kFu := by decide
@[simp] theorem rs_kFu_ne_rsQ : kFu ≠ rsQ := by decide
@[simp] theorem rs_rsQ_ne_kD : rsQ ≠ kD := by decide
@[simp] theorem rs_kD_ne_rsQ : kD ≠ rsQ := by decide
@[simp] theorem rs_rsQ_ne_pmC : rsQ ≠ pmC := by decide
@[simp] theorem rs_pmC_ne_rsQ : pmC ≠ rsQ := by decide
@[simp] theorem rs_rsQ_ne_pmK : rsQ ≠ pmK := by decide
@[simp] theorem rs_pmK_ne_rsQ : pmK ≠ rsQ := by decide
@[simp] theorem rs_rsQ_ne_pmR : rsQ ≠ pmR := by decide
@[simp] theorem rs_pmR_ne_rsQ : pmR ≠ rsQ := by decide
@[simp] theorem rs_rsQ_ne_pmM : rsQ ≠ pmM := by decide
@[simp] theorem rs_pmM_ne_rsQ : pmM ≠ rsQ := by decide
@[simp] theorem rs_rsQ_ne_lKb : rsQ ≠ lKb := by decide
@[simp] theorem rs_lKb_ne_rsQ : lKb ≠ rsQ := by decide
@[simp] theorem rs_rsC_ne_rsN : rsC ≠ rsN := by decide
@[simp] theorem rs_rsC_ne_rsQ : rsC ≠ rsQ := by decide
@[simp] theorem rs_rsC_ne_rsW : rsC ≠ rsW := by decide
@[simp] theorem rs_rsC_ne_rsJ : rsC ≠ rsJ := by decide
@[simp] theorem rs_rsC_ne_rsTg : rsC ≠ rsTg := by decide
@[simp] theorem rs_rsC_ne_rsT : rsC ≠ rsT := by decide
@[simp] theorem rs_rsC_ne_rsV : rsC ≠ rsV := by decide
@[simp] theorem rs_rsC_ne_rsF : rsC ≠ rsF := by decide
@[simp] theorem rs_rsC_ne_rsTg2 : rsC ≠ rsTg2 := by decide
@[simp] theorem rs_rsC_ne_rsE : rsC ≠ rsE := by decide
@[simp] theorem rs_rsC_ne_rsX : rsC ≠ rsX := by decide
@[simp] theorem rs_rsC_ne_kFu : rsC ≠ kFu := by decide
@[simp] theorem rs_kFu_ne_rsC : kFu ≠ rsC := by decide
@[simp] theorem rs_rsC_ne_kD : rsC ≠ kD := by decide
@[simp] theorem rs_kD_ne_rsC : kD ≠ rsC := by decide
@[simp] theorem rs_rsC_ne_pmC : rsC ≠ pmC := by decide
@[simp] theorem rs_pmC_ne_rsC : pmC ≠ rsC := by decide
@[simp] theorem rs_rsC_ne_pmK : rsC ≠ pmK := by decide
@[simp] theorem rs_pmK_ne_rsC : pmK ≠ rsC := by decide
@[simp] theorem rs_rsC_ne_pmR : rsC ≠ pmR := by decide
@[simp] theorem rs_pmR_ne_rsC : pmR ≠ rsC := by decide
@[simp] theorem rs_rsC_ne_pmM : rsC ≠ pmM := by decide
@[simp] theorem rs_pmM_ne_rsC : pmM ≠ rsC := by decide
@[simp] theorem rs_rsC_ne_lKb : rsC ≠ lKb := by decide
@[simp] theorem rs_lKb_ne_rsC : lKb ≠ rsC := by decide
@[simp] theorem rs_rsW_ne_rsN : rsW ≠ rsN := by decide
@[simp] theorem rs_rsW_ne_rsQ : rsW ≠ rsQ := by decide
@[simp] theorem rs_rsW_ne_rsC : rsW ≠ rsC := by decide
@[simp] theorem rs_rsW_ne_rsJ : rsW ≠ rsJ := by decide
@[simp] theorem rs_rsW_ne_rsTg : rsW ≠ rsTg := by decide
@[simp] theorem rs_rsW_ne_rsT : rsW ≠ rsT := by decide
@[simp] theorem rs_rsW_ne_rsV : rsW ≠ rsV := by decide
@[simp] theorem rs_rsW_ne_rsF : rsW ≠ rsF := by decide
@[simp] theorem rs_rsW_ne_rsTg2 : rsW ≠ rsTg2 := by decide
@[simp] theorem rs_rsW_ne_rsE : rsW ≠ rsE := by decide
@[simp] theorem rs_rsW_ne_rsX : rsW ≠ rsX := by decide
@[simp] theorem rs_rsW_ne_kFu : rsW ≠ kFu := by decide
@[simp] theorem rs_kFu_ne_rsW : kFu ≠ rsW := by decide
@[simp] theorem rs_rsW_ne_kD : rsW ≠ kD := by decide
@[simp] theorem rs_kD_ne_rsW : kD ≠ rsW := by decide
@[simp] theorem rs_rsW_ne_pmC : rsW ≠ pmC := by decide
@[simp] theorem rs_pmC_ne_rsW : pmC ≠ rsW := by decide
@[simp] theorem rs_rsW_ne_pmK : rsW ≠ pmK := by decide
@[simp] theorem rs_pmK_ne_rsW : pmK ≠ rsW := by decide
@[simp] theorem rs_rsW_ne_pmR : rsW ≠ pmR := by decide
@[simp] theorem rs_pmR_ne_rsW : pmR ≠ rsW := by decide
@[simp] theorem rs_rsW_ne_pmM : rsW ≠ pmM := by decide
@[simp] theorem rs_pmM_ne_rsW : pmM ≠ rsW := by decide
@[simp] theorem rs_rsW_ne_lKb : rsW ≠ lKb := by decide
@[simp] theorem rs_lKb_ne_rsW : lKb ≠ rsW := by decide
@[simp] theorem rs_rsJ_ne_rsN : rsJ ≠ rsN := by decide
@[simp] theorem rs_rsJ_ne_rsQ : rsJ ≠ rsQ := by decide
@[simp] theorem rs_rsJ_ne_rsC : rsJ ≠ rsC := by decide
@[simp] theorem rs_rsJ_ne_rsW : rsJ ≠ rsW := by decide
@[simp] theorem rs_rsJ_ne_rsTg : rsJ ≠ rsTg := by decide
@[simp] theorem rs_rsJ_ne_rsT : rsJ ≠ rsT := by decide
@[simp] theorem rs_rsJ_ne_rsV : rsJ ≠ rsV := by decide
@[simp] theorem rs_rsJ_ne_rsF : rsJ ≠ rsF := by decide
@[simp] theorem rs_rsJ_ne_rsTg2 : rsJ ≠ rsTg2 := by decide
@[simp] theorem rs_rsJ_ne_rsE : rsJ ≠ rsE := by decide
@[simp] theorem rs_rsJ_ne_rsX : rsJ ≠ rsX := by decide
@[simp] theorem rs_rsJ_ne_kFu : rsJ ≠ kFu := by decide
@[simp] theorem rs_kFu_ne_rsJ : kFu ≠ rsJ := by decide
@[simp] theorem rs_rsJ_ne_kD : rsJ ≠ kD := by decide
@[simp] theorem rs_kD_ne_rsJ : kD ≠ rsJ := by decide
@[simp] theorem rs_rsJ_ne_pmC : rsJ ≠ pmC := by decide
@[simp] theorem rs_pmC_ne_rsJ : pmC ≠ rsJ := by decide
@[simp] theorem rs_rsJ_ne_pmK : rsJ ≠ pmK := by decide
@[simp] theorem rs_pmK_ne_rsJ : pmK ≠ rsJ := by decide
@[simp] theorem rs_rsJ_ne_pmR : rsJ ≠ pmR := by decide
@[simp] theorem rs_pmR_ne_rsJ : pmR ≠ rsJ := by decide
@[simp] theorem rs_rsJ_ne_pmM : rsJ ≠ pmM := by decide
@[simp] theorem rs_pmM_ne_rsJ : pmM ≠ rsJ := by decide
@[simp] theorem rs_rsJ_ne_lKb : rsJ ≠ lKb := by decide
@[simp] theorem rs_lKb_ne_rsJ : lKb ≠ rsJ := by decide
@[simp] theorem rs_rsTg_ne_rsN : rsTg ≠ rsN := by decide
@[simp] theorem rs_rsTg_ne_rsQ : rsTg ≠ rsQ := by decide
@[simp] theorem rs_rsTg_ne_rsC : rsTg ≠ rsC := by decide
@[simp] theorem rs_rsTg_ne_rsW : rsTg ≠ rsW := by decide
@[simp] theorem rs_rsTg_ne_rsJ : rsTg ≠ rsJ := by decide
@[simp] theorem rs_rsTg_ne_rsT : rsTg ≠ rsT := by decide
@[simp] theorem rs_rsTg_ne_rsV : rsTg ≠ rsV := by decide
@[simp] theorem rs_rsTg_ne_rsF : rsTg ≠ rsF := by decide
@[simp] theorem rs_rsTg_ne_rsTg2 : rsTg ≠ rsTg2 := by decide
@[simp] theorem rs_rsTg_ne_rsE : rsTg ≠ rsE := by decide
@[simp] theorem rs_rsTg_ne_rsX : rsTg ≠ rsX := by decide
@[simp] theorem rs_rsTg_ne_kFu : rsTg ≠ kFu := by decide
@[simp] theorem rs_kFu_ne_rsTg : kFu ≠ rsTg := by decide
@[simp] theorem rs_rsTg_ne_kD : rsTg ≠ kD := by decide
@[simp] theorem rs_kD_ne_rsTg : kD ≠ rsTg := by decide
@[simp] theorem rs_rsTg_ne_pmC : rsTg ≠ pmC := by decide
@[simp] theorem rs_pmC_ne_rsTg : pmC ≠ rsTg := by decide
@[simp] theorem rs_rsTg_ne_pmK : rsTg ≠ pmK := by decide
@[simp] theorem rs_pmK_ne_rsTg : pmK ≠ rsTg := by decide
@[simp] theorem rs_rsTg_ne_pmR : rsTg ≠ pmR := by decide
@[simp] theorem rs_pmR_ne_rsTg : pmR ≠ rsTg := by decide
@[simp] theorem rs_rsTg_ne_pmM : rsTg ≠ pmM := by decide
@[simp] theorem rs_pmM_ne_rsTg : pmM ≠ rsTg := by decide
@[simp] theorem rs_rsTg_ne_lKb : rsTg ≠ lKb := by decide
@[simp] theorem rs_lKb_ne_rsTg : lKb ≠ rsTg := by decide
@[simp] theorem rs_rsT_ne_rsN : rsT ≠ rsN := by decide
@[simp] theorem rs_rsT_ne_rsQ : rsT ≠ rsQ := by decide
@[simp] theorem rs_rsT_ne_rsC : rsT ≠ rsC := by decide
@[simp] theorem rs_rsT_ne_rsW : rsT ≠ rsW := by decide
@[simp] theorem rs_rsT_ne_rsJ : rsT ≠ rsJ := by decide
@[simp] theorem rs_rsT_ne_rsTg : rsT ≠ rsTg := by decide
@[simp] theorem rs_rsT_ne_rsV : rsT ≠ rsV := by decide
@[simp] theorem rs_rsT_ne_rsF : rsT ≠ rsF := by decide
@[simp] theorem rs_rsT_ne_rsTg2 : rsT ≠ rsTg2 := by decide
@[simp] theorem rs_rsT_ne_rsE : rsT ≠ rsE := by decide
@[simp] theorem rs_rsT_ne_rsX : rsT ≠ rsX := by decide
@[simp] theorem rs_rsT_ne_kFu : rsT ≠ kFu := by decide
@[simp] theorem rs_kFu_ne_rsT : kFu ≠ rsT := by decide
@[simp] theorem rs_rsT_ne_kD : rsT ≠ kD := by decide
@[simp] theorem rs_kD_ne_rsT : kD ≠ rsT := by decide
@[simp] theorem rs_rsT_ne_pmC : rsT ≠ pmC := by decide
@[simp] theorem rs_pmC_ne_rsT : pmC ≠ rsT := by decide
@[simp] theorem rs_rsT_ne_pmK : rsT ≠ pmK := by decide
@[simp] theorem rs_pmK_ne_rsT : pmK ≠ rsT := by decide
@[simp] theorem rs_rsT_ne_pmR : rsT ≠ pmR := by decide
@[simp] theorem rs_pmR_ne_rsT : pmR ≠ rsT := by decide
@[simp] theorem rs_rsT_ne_pmM : rsT ≠ pmM := by decide
@[simp] theorem rs_pmM_ne_rsT : pmM ≠ rsT := by decide
@[simp] theorem rs_rsT_ne_lKb : rsT ≠ lKb := by decide
@[simp] theorem rs_lKb_ne_rsT : lKb ≠ rsT := by decide
@[simp] theorem rs_rsV_ne_rsN : rsV ≠ rsN := by decide
@[simp] theorem rs_rsV_ne_rsQ : rsV ≠ rsQ := by decide
@[simp] theorem rs_rsV_ne_rsC : rsV ≠ rsC := by decide
@[simp] theorem rs_rsV_ne_rsW : rsV ≠ rsW := by decide
@[simp] theorem rs_rsV_ne_rsJ : rsV ≠ rsJ := by decide
@[simp] theorem rs_rsV_ne_rsTg : rsV ≠ rsTg := by decide
@[simp] theorem rs_rsV_ne_rsT : rsV ≠ rsT := by decide
@[simp] theorem rs_rsV_ne_rsF : rsV ≠ rsF := by decide
@[simp] theorem rs_rsV_ne_rsTg2 : rsV ≠ rsTg2 := by decide
@[simp] theorem rs_rsV_ne_rsE : rsV ≠ rsE := by decide
@[simp] theorem rs_rsV_ne_rsX : rsV ≠ rsX := by decide
@[simp] theorem rs_rsV_ne_kFu : rsV ≠ kFu := by decide
@[simp] theorem rs_kFu_ne_rsV : kFu ≠ rsV := by decide
@[simp] theorem rs_rsV_ne_kD : rsV ≠ kD := by decide
@[simp] theorem rs_kD_ne_rsV : kD ≠ rsV := by decide
@[simp] theorem rs_rsV_ne_pmC : rsV ≠ pmC := by decide
@[simp] theorem rs_pmC_ne_rsV : pmC ≠ rsV := by decide
@[simp] theorem rs_rsV_ne_pmK : rsV ≠ pmK := by decide
@[simp] theorem rs_pmK_ne_rsV : pmK ≠ rsV := by decide
@[simp] theorem rs_rsV_ne_pmR : rsV ≠ pmR := by decide
@[simp] theorem rs_pmR_ne_rsV : pmR ≠ rsV := by decide
@[simp] theorem rs_rsV_ne_pmM : rsV ≠ pmM := by decide
@[simp] theorem rs_pmM_ne_rsV : pmM ≠ rsV := by decide
@[simp] theorem rs_rsV_ne_lKb : rsV ≠ lKb := by decide
@[simp] theorem rs_lKb_ne_rsV : lKb ≠ rsV := by decide
@[simp] theorem rs_rsF_ne_rsN : rsF ≠ rsN := by decide
@[simp] theorem rs_rsF_ne_rsQ : rsF ≠ rsQ := by decide
@[simp] theorem rs_rsF_ne_rsC : rsF ≠ rsC := by decide
@[simp] theorem rs_rsF_ne_rsW : rsF ≠ rsW := by decide
@[simp] theorem rs_rsF_ne_rsJ : rsF ≠ rsJ := by decide
@[simp] theorem rs_rsF_ne_rsTg : rsF ≠ rsTg := by decide
@[simp] theorem rs_rsF_ne_rsT : rsF ≠ rsT := by decide
@[simp] theorem rs_rsF_ne_rsV : rsF ≠ rsV := by decide
@[simp] theorem rs_rsF_ne_rsTg2 : rsF ≠ rsTg2 := by decide
@[simp] theorem rs_rsF_ne_rsE : rsF ≠ rsE := by decide
@[simp] theorem rs_rsF_ne_rsX : rsF ≠ rsX := by decide
@[simp] theorem rs_rsF_ne_kFu : rsF ≠ kFu := by decide
@[simp] theorem rs_kFu_ne_rsF : kFu ≠ rsF := by decide
@[simp] theorem rs_rsF_ne_kD : rsF ≠ kD := by decide
@[simp] theorem rs_kD_ne_rsF : kD ≠ rsF := by decide
@[simp] theorem rs_rsF_ne_pmC : rsF ≠ pmC := by decide
@[simp] theorem rs_pmC_ne_rsF : pmC ≠ rsF := by decide
@[simp] theorem rs_rsF_ne_pmK : rsF ≠ pmK := by decide
@[simp] theorem rs_pmK_ne_rsF : pmK ≠ rsF := by decide
@[simp] theorem rs_rsF_ne_pmR : rsF ≠ pmR := by decide
@[simp] theorem rs_pmR_ne_rsF : pmR ≠ rsF := by decide
@[simp] theorem rs_rsF_ne_pmM : rsF ≠ pmM := by decide
@[simp] theorem rs_pmM_ne_rsF : pmM ≠ rsF := by decide
@[simp] theorem rs_rsF_ne_lKb : rsF ≠ lKb := by decide
@[simp] theorem rs_lKb_ne_rsF : lKb ≠ rsF := by decide
@[simp] theorem rs_rsTg2_ne_rsN : rsTg2 ≠ rsN := by decide
@[simp] theorem rs_rsTg2_ne_rsQ : rsTg2 ≠ rsQ := by decide
@[simp] theorem rs_rsTg2_ne_rsC : rsTg2 ≠ rsC := by decide
@[simp] theorem rs_rsTg2_ne_rsW : rsTg2 ≠ rsW := by decide
@[simp] theorem rs_rsTg2_ne_rsJ : rsTg2 ≠ rsJ := by decide
@[simp] theorem rs_rsTg2_ne_rsTg : rsTg2 ≠ rsTg := by decide
@[simp] theorem rs_rsTg2_ne_rsT : rsTg2 ≠ rsT := by decide
@[simp] theorem rs_rsTg2_ne_rsV : rsTg2 ≠ rsV := by decide
@[simp] theorem rs_rsTg2_ne_rsF : rsTg2 ≠ rsF := by decide
@[simp] theorem rs_rsTg2_ne_rsE : rsTg2 ≠ rsE := by decide
@[simp] theorem rs_rsTg2_ne_rsX : rsTg2 ≠ rsX := by decide
@[simp] theorem rs_rsTg2_ne_kFu : rsTg2 ≠ kFu := by decide
@[simp] theorem rs_kFu_ne_rsTg2 : kFu ≠ rsTg2 := by decide
@[simp] theorem rs_rsTg2_ne_kD : rsTg2 ≠ kD := by decide
@[simp] theorem rs_kD_ne_rsTg2 : kD ≠ rsTg2 := by decide
@[simp] theorem rs_rsTg2_ne_pmC : rsTg2 ≠ pmC := by decide
@[simp] theorem rs_pmC_ne_rsTg2 : pmC ≠ rsTg2 := by decide
@[simp] theorem rs_rsTg2_ne_pmK : rsTg2 ≠ pmK := by decide
@[simp] theorem rs_pmK_ne_rsTg2 : pmK ≠ rsTg2 := by decide
@[simp] theorem rs_rsTg2_ne_pmR : rsTg2 ≠ pmR := by decide
@[simp] theorem rs_pmR_ne_rsTg2 : pmR ≠ rsTg2 := by decide
@[simp] theorem rs_rsTg2_ne_pmM : rsTg2 ≠ pmM := by decide
@[simp] theorem rs_pmM_ne_rsTg2 : pmM ≠ rsTg2 := by decide
@[simp] theorem rs_rsTg2_ne_lKb : rsTg2 ≠ lKb := by decide
@[simp] theorem rs_lKb_ne_rsTg2 : lKb ≠ rsTg2 := by decide
@[simp] theorem rs_rsE_ne_rsN : rsE ≠ rsN := by decide
@[simp] theorem rs_rsE_ne_rsQ : rsE ≠ rsQ := by decide
@[simp] theorem rs_rsE_ne_rsC : rsE ≠ rsC := by decide
@[simp] theorem rs_rsE_ne_rsW : rsE ≠ rsW := by decide
@[simp] theorem rs_rsE_ne_rsJ : rsE ≠ rsJ := by decide
@[simp] theorem rs_rsE_ne_rsTg : rsE ≠ rsTg := by decide
@[simp] theorem rs_rsE_ne_rsT : rsE ≠ rsT := by decide
@[simp] theorem rs_rsE_ne_rsV : rsE ≠ rsV := by decide
@[simp] theorem rs_rsE_ne_rsF : rsE ≠ rsF := by decide
@[simp] theorem rs_rsE_ne_rsTg2 : rsE ≠ rsTg2 := by decide
@[simp] theorem rs_rsE_ne_rsX : rsE ≠ rsX := by decide
@[simp] theorem rs_rsE_ne_kFu : rsE ≠ kFu := by decide
@[simp] theorem rs_kFu_ne_rsE : kFu ≠ rsE := by decide
@[simp] theorem rs_rsE_ne_kD : rsE ≠ kD := by decide
@[simp] theorem rs_kD_ne_rsE : kD ≠ rsE := by decide
@[simp] theorem rs_rsE_ne_pmC : rsE ≠ pmC := by decide
@[simp] theorem rs_pmC_ne_rsE : pmC ≠ rsE := by decide
@[simp] theorem rs_rsE_ne_pmK : rsE ≠ pmK := by decide
@[simp] theorem rs_pmK_ne_rsE : pmK ≠ rsE := by decide
@[simp] theorem rs_rsE_ne_pmR : rsE ≠ pmR := by decide
@[simp] theorem rs_pmR_ne_rsE : pmR ≠ rsE := by decide
@[simp] theorem rs_rsE_ne_pmM : rsE ≠ pmM := by decide
@[simp] theorem rs_pmM_ne_rsE : pmM ≠ rsE := by decide
@[simp] theorem rs_rsE_ne_lKb : rsE ≠ lKb := by decide
@[simp] theorem rs_lKb_ne_rsE : lKb ≠ rsE := by decide
@[simp] theorem rs_rsX_ne_rsN : rsX ≠ rsN := by decide
@[simp] theorem rs_rsX_ne_rsQ : rsX ≠ rsQ := by decide
@[simp] theorem rs_rsX_ne_rsC : rsX ≠ rsC := by decide
@[simp] theorem rs_rsX_ne_rsW : rsX ≠ rsW := by decide
@[simp] theorem rs_rsX_ne_rsJ : rsX ≠ rsJ := by decide
@[simp] theorem rs_rsX_ne_rsTg : rsX ≠ rsTg := by decide
@[simp] theorem rs_rsX_ne_rsT : rsX ≠ rsT := by decide
@[simp] theorem rs_rsX_ne_rsV : rsX ≠ rsV := by decide
@[simp] theorem rs_rsX_ne_rsF : rsX ≠ rsF := by decide
@[simp] theorem rs_rsX_ne_rsTg2 : rsX ≠ rsTg2 := by decide
@[simp] theorem rs_rsX_ne_rsE : rsX ≠ rsE := by decide
@[simp] theorem rs_rsX_ne_kFu : rsX ≠ kFu := by decide
@[simp] theorem rs_kFu_ne_rsX : kFu ≠ rsX := by decide
@[simp] theorem rs_rsX_ne_kD : rsX ≠ kD := by decide
@[simp] theorem rs_kD_ne_rsX : kD ≠ rsX := by decide
@[simp] theorem rs_rsX_ne_pmC : rsX ≠ pmC := by decide
@[simp] theorem rs_pmC_ne_rsX : pmC ≠ rsX := by decide
@[simp] theorem rs_rsX_ne_pmK : rsX ≠ pmK := by decide
@[simp] theorem rs_pmK_ne_rsX : pmK ≠ rsX := by decide
@[simp] theorem rs_rsX_ne_pmR : rsX ≠ pmR := by decide
@[simp] theorem rs_pmR_ne_rsX : pmR ≠ rsX := by decide
@[simp] theorem rs_rsX_ne_pmM : rsX ≠ pmM := by decide
@[simp] theorem rs_pmM_ne_rsX : pmM ≠ rsX := by decide
@[simp] theorem rs_rsX_ne_lKb : rsX ≠ lKb := by decide
@[simp] theorem rs_lKb_ne_rsX : lKb ≠ rsX := by decide

def rsLocals : List MlS := [rsN, rsQ, rsC, rsW, rsJ, rsTg, rsT, rsV, rsF, rsTg2, rsE, rsX]

def rsBody (C : Ctx) : ProgHOL 64 := prologue rsLocals
  (.seq (.assign .local rsN (.load .one (vv pmR)))
  (.ite (.cmp .notEqual (vv rsN) (.const 1)) (.return (vv pmM))
  (.seq (.assign .local rsQ (.load .one (.op .add [vv pmR, .const 8])))
  (.seq (.assign .local rsC (.load .one (vv rsQ)))
  (envFindP C rsW (vv rsC)
  (.ite (.cmp .equal (vv rsW) (.const 0)) (.return (vv pmM))
  (.seq (.assign .local rsJ (.op .sub [vv rsW, .const 1]))
  (.seq (.assign .local rsTg (.load .one (vv rsJ)))
  (.ite (.cmp .notEqual (vv rsTg) (.const 4)) (.return (vv pmM))
  (.seq (.assign .local rsT (.load .one (.op .add [vv rsJ, .const 48])))
  (envFindP C rsV (vv rsT)
  (.ite (.cmp .equal (vv rsV) (.const 0)) (.return (vv pmM))
  (.seq (.assign .local rsF (.op .sub [vv rsV, .const 1]))
  (.seq (.assign .local rsTg2 (.load .one (vv rsF)))
  (.ite (.cmp .notEqual (vv rsTg2) (.const 3)) (.return (vv pmM))
  (.ite (vv pmK)
  (.seq (.call (some (some (.local, rsX), none)) fRk [vv kFu, vv kD, vv rsQ, vv rsJ, vv rsT, vv pmM])
  (.return (vv rsX)))
  (.seq (.call (some (some (.local, rsE), none)) fEr [vv rsT, vv rsC, vv rsJ, vv rsF])
  (.ite (.cmp .notEqual (vv rsE) (.const 0))
  (.seq (.call (some (some (.local, rsX), none)) fRe [vv kFu, vv kD, vv rsQ, vv rsJ, vv rsT, vv pmM, vv rsF, .op .sub [vv rsE, .const 1]])
  (.return (vv rsX)))
  (.seq (.call (some (some (.local, rsX), none)) fRa [vv kFu, vv kD, vv rsQ, vv rsJ, vv rsT, vv pmM])
  (.return (vv rsX)))))))))))))))))))))

section
variable {σ : Type}

theorem rs_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rsLocals → (ctxEnv C ++ pmParams.zip vals).get x = none :=
  Knot.params_none C rsLocals pmParams vals (by decide) (by decide)

structure RsCodes (C : Ctx) (Brk Bre Bra : ProgHOL 64) : Prop where
  mg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  mp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  lq : C.code.lookup fLq = some (lqParams.map (fun p => (p, ShapeHOL.one)), lqBody, .one)
  er : C.code.lookup fEr = some (erParams.map (fun p => (p, ShapeHOL.one)), erBody C, .one)
  rk : C.code.lookup fRk = some (rkParams.map (fun p => (p, ShapeHOL.one)), Brk, .one)
  re : C.code.lookup fRe = some (reParams.map (fun p => (p, ShapeHOL.one)), Bre, .one)
  ra : C.code.lookup fRa = some (rkParams.map (fun p => (p, ShapeHOL.one)), Bra, .one)

theorem rs_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) (hok : CtxOK C) (Brk Bre Bra : ProgHOL 64)
    (hc : RsCodes C Brk Bre Bra) (s : AState) (d : Nat) (c : NIdx) (isK : Bool) (rules : List IRecRule)
    (rw : BitVec 64) (m : EIdx) (hrules : RulesE C.EB C.EH rw rules)
    (hK : ∀ (H : List (BitVec 64)) s1 (rl : IRecRule) qr cvj cnP nF T qj, C.H <+: H → RuleE C.EB C.EH qr rl →
      CIE C.EB C.EH qj (.ctorInfo cvj cnP nF T) →
      SpecR (σ := σ) (Pre (ctxH C H) s1 (rkParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, ecell C qr, ecell C qj,
        Enc.idxW T, Enc.idxW m])) Brk s1 (rescueK mode (knot mode C n) C.fe d rl cvj cnP T m) (PostK (ctxH C H)))
    (hE : ∀ (H : List (BitVec 64)) s1 (rl : IRecRule) qr cvj cnP nF T qj cvT caps qT tbl o, C.H <+: H →
      RuleE C.EB C.EH qr rl → CIE C.EB C.EH qj (.ctorInfo cvj cnP nF T) → CIE C.EB C.EH qT (.indInfo cvT caps) →
      TblE C.EB C.EH o tbl →
      SpecR (σ := σ) (Pre (ctxH C H) s1 (reParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, ecell C qr, ecell C qj,
        Enc.idxW T, Enc.idxW m, ecell C qT, ecell C o])) Bre s1
        (rescueEta mode (knot mode C n) C.fe d rl cvj cnP T m cvT caps tbl) (PostK (ctxH C H)))
    (hA : ∀ (H : List (BitVec 64)) s1 (rl : IRecRule) qr cvj cnP nF T qj, C.H <+: H → RuleE C.EB C.EH qr rl →
      CIE C.EB C.EH qj (.ctorInfo cvj cnP nF T) →
      SpecR (σ := σ) (Pre (ctxH C H) s1 (rkParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, ecell C qr, ecell C qj,
        Enc.idxW T, Enc.idxW m])) Bra s1 (rescueAnd mode (knot mode C n) C.fe d rl cvj cnP T m) (PostK (ctxH C H))) :
    SpecR (σ := σ) (Pre C s (pmParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c, boolW isK, rw,
      Enc.idxW m])) (rsBody C) s (majorToCtorRescue mode (knot mode C n) C.fe d c isK rules m) (PostK C) := by
  refine specR_prologue (Knot.postK_locals C) (rs_none C _) ?_
  rw [majorToCtorRescue_eq]
  have hretM : ∀ {Γ : Env} {M : Mem}, Γ.get pmM = some (Enc.idxW m) →
      SpecR (σ := σ) (Inv C s Γ M (ctxLocals ++ rsLocals)) (.return (vv pmM)) s (pure m) (PostK C) :=
    fun hE => specR_returnI _ (Enc.idxW m) (by simpa using hE)
      (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  obtain ⟨orl, hwr, hrlen, hrels⟩ := hrules
  refine specR_envLoadI rsN (vv pmR) orl _ (by decide) (by simp +decide [Env.get, pmParams, ctxEnv, hwr]; rfl)
    hrlen ?_
  rcases rules with _ | ⟨rl, _ | ⟨rl2, rs⟩⟩
  · refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact hretM (by simp +decide [Env.get, pmParams, ctxEnv])
  swap
  · refine specR_atEntry fun t0 ht0 => ?_
    have hEN := ht0.sr.env.1.len
    have hne : BitVec.ofNat 64 (rl :: rl2 :: rs).length ≠ 1 := by
      intro e
      obtain ⟨q, hq1, _⟩ := hrels ((rl :: rl2 :: rs).length - 1) (by simp)
      have := congrArg BitVec.toNat e
      have hlt := (List.getElem?_eq_some_iff.mp hq1).1
      have h2 := hok.envLay
      simp only [List.length_cons] at this hlt
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
      simp at this
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact hretM (by simp +decide [Env.get, pmParams, ctxEnv])
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
  dsimp only
  obtain ⟨qr, hqr, hrule⟩ := hrels 0 (by simp)
  simp only [List.getElem_cons_zero] at hrule
  refine specR_envLoadI rsQ (.op .add [vv pmR, .const 8]) (orl + 1 + 0) _ (by decide)
    (by simp +decide [sev, Env.get, pmParams, ctxEnv, hwr]; show ecell C orl + BitVec.ofNat 64 (8 * 1) = _;
        rw [ecell_add])
    hqr ?_
  refine specR_envLoadI rsC (vv rsQ) qr _ (by decide) (by simp; rfl) hrule.1 ?_
  refine specR_envFindI hok hc.mg hc.mp rsW (vv rsC) rl.ctor (by decide) (by simp) (by simp +decide [Env.get, ctxEnv]) ?_
  have hrel := find_rel hok rl.ctor
  revert hrel
  rcases hfind : C.fe.find? rl.ctor with _ | ci
  · intro hrel; simp only at hrel
    rw [hrel]
    refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact hretM (by simp +decide [Env.get, pmParams, ctxEnv])
  intro ⟨qj, hm, hcij⟩
  rw [hm]
  refine specR_atEntry fun t ht => ?_
  have hqjE : qj < C.EN := Nat.lt_of_lt_of_le (cie_lt hcij) ht.sr.env.1.len
  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hqjE)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI rsJ _ (ecell C qj) (by decide) (by simp [sev, optWG]; exact ecell_succ_sub C qj) ?_
  refine specR_envLoadI rsTg (vv rsJ) qj _ (by decide) (by simp) (UD.cie_tag hcij) ?_
  cases ci
  case ctorInfo cvj cnP nF T =>
    dsimp only
    refine specR_ifI _ 0 (by simp +decide [sev, UD.ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    have hind : C.EH[qj + 6]? = some (Enc.idxW T) := hcij.2.2.2.2
    refine specR_envLoadI rsT (.op .add [vv rsJ, .const 48]) (qj + 6) _ (by decide)
      (by simp [sev, vv]; rw [show (48#64 : BitVec 64) = BitVec.ofNat 64 (8 * 6) from rfl, ecell_add]) hind ?_
    refine specR_envFindI hok hc.mg hc.mp rsV (vv rsT) T (by decide) (by simp) (by simp +decide [Env.get, ctxEnv]) ?_
    have hrel2 := find_rel hok T
    revert hrel2
    rcases hfind2 : C.fe.find? T with _ | ci2
    · intro hrel2; simp only at hrel2
      rw [hrel2]
      refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      exact hretM (by simp +decide [Env.get, pmParams, ctxEnv])
    intro ⟨qT, hm2, hciT⟩
    rw [hm2]
    have hqTE : qT < C.EN := Nat.lt_of_lt_of_le (cie_lt hciT) ht.sr.env.1.len
    refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hqTE)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI rsF _ (ecell C qT) (by decide) (by simp [sev, optWG]; exact ecell_succ_sub C qT) ?_
    refine specR_envLoadI rsTg2 (vv rsF) qT _ (by decide) (by simp) (UD.cie_tag hciT) ?_
    cases ci2
    case indInfo cvT caps =>
      dsimp only
      refine specR_ifI _ 0 (by simp +decide [sev, UD.ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      cases isK
      · refine specR_ifI _ 0 (by simp +decide [Env.get, pmParams, ctxEnv, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
        simp only [Bool.false_eq_true, ite_false]
        refine specR_callNIH rsE fEr erParams [vv rsT, vv rsC, vv rsJ, vv rsF] (erBody C)
          [Enc.idxW T, Enc.idxW rl.ctor, ecell C qj, ecell C qT] (by decide) rfl (by decide) hc.er
          ⟨by simp, by simp, by simp, by simp, trivial⟩ (PostTB C s)
          (fun o w s' H' => s' = s ∧ match o with
            | none => w = 0
            | some t => ∃ ot, w = ecell C ot + 1 ∧ ot < C.EN ∧ TblE C.EB C.EH ot t)
          (fun o w s' st ⟨hs, ⟨H', hp, hsr⟩, hr⟩ => ⟨H', hp, ⟨hs, hr⟩, hs ▸ hsr⟩)
          (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu erParams _ rfl hlk)
            (er_spec C hok hc.mg hc.mp hc.lq s T rl.ctor cvj cvT caps qj qT cnP nF T hcij hciT))
          (fun o w s1 H1 hp1 ⟨hs, hr⟩ => ?_)
        subst s1
        rcases o with _ | tbl
        · simp only at hr
          subst hr
          refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
            (fun _ => ?_)
          refine specR_bindPure ?_
          refine specR_callKH (C := ctxH C H1) rsX fRa rkParams [vv kFu, vv kD, vv rsQ, vv rsJ, vv rsT, vv pmM] Bra
            [BitVec.ofNat 64 n, BitVec.ofNat 64 d, ecell C qr, ecell C qj, Enc.idxW T, Enc.idxW m] (by decide) rfl
            (by decide) hc.ra
            ⟨by simp +decide [Env.get, pmParams, ctxEnv], by simp +decide [Env.get, pmParams, ctxEnv],
              by simp; rfl, by simp, by simp, by simp +decide [Env.get, pmParams, ctxEnv], trivial⟩
            (hA H1 s rl qr cvj cnP nF T qj hp1 hrule hcij) (fun r s2 H2 hp2 => ?_)
          exact specR_returnI _ (Enc.idxW r) (by simp)
            (fun t ht => ⟨H2, hp1.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
        · obtain ⟨ot, hw, hotE, htb⟩ := hr
          subst hw
          refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hotE)
            (fun _ => ?_) (fun h => absurd h (by decide))
          dsimp only
          refine specR_bindPure ?_
          refine specR_callKH (C := ctxH C H1) rsX fRe reParams
            [vv kFu, vv kD, vv rsQ, vv rsJ, vv rsT, vv pmM, vv rsF, .op .sub [vv rsE, .const 1]] Bre
            [BitVec.ofNat 64 n, BitVec.ofNat 64 d, ecell C qr, ecell C qj, Enc.idxW T, Enc.idxW m, ecell C qT,
              ecell C ot] (by decide) rfl (by decide) hc.re
            ⟨by simp +decide [Env.get, pmParams, ctxEnv], by simp +decide [Env.get, pmParams, ctxEnv],
              by simp; rfl, by simp, by simp, by simp +decide [Env.get, pmParams, ctxEnv], by simp,
              by simp [sev]; exact ecell_succ_sub C ot, trivial⟩
            (hE H1 s rl qr cvj cnP nF T qj cvT caps qT tbl ot hp1 hrule hcij hciT htb) (fun r s2 H2 hp2 => ?_)
          exact specR_returnI _ (Enc.idxW r) (by simp)
            (fun t ht => ⟨H2, hp1.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      · refine specR_ifI _ 1 (by simp +decide [Env.get, pmParams, ctxEnv, boolW]) (fun _ => ?_)
          (fun h => absurd h (by decide))
        simp only [ite_true]
        refine specR_bindPure ?_
        refine specR_callKH rsX fRk rkParams [vv kFu, vv kD, vv rsQ, vv rsJ, vv rsT, vv pmM] Brk
          [BitVec.ofNat 64 n, BitVec.ofNat 64 d, ecell C qr, ecell C qj, Enc.idxW T, Enc.idxW m] (by decide) rfl
          (by decide) hc.rk
          ⟨by simp +decide [Env.get, pmParams, ctxEnv], by simp +decide [Env.get, pmParams, ctxEnv],
            by simp; rfl, by simp, by simp, by simp +decide [Env.get, pmParams, ctxEnv], trivial⟩
          (hK C.H s rl qr cvj cnP nF T qj (List.prefix_refl _) hrule hcij) (fun r s2 H2 hp2 => ?_)
        exact specR_returnI _ (Enc.idxW r) (by simp)
          (fun t ht => ⟨H2, hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    all_goals
      dsimp only
      refine specR_ifI _ 1 (by simp +decide [sev, UD.ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact hretM (by simp +decide [Env.get, pmParams, ctxEnv])
  all_goals
    dsimp only
    refine specR_ifI _ 1 (by simp +decide [sev, UD.ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact hretM (by simp +decide [Env.get, pmParams, ctxEnv])

end

end ConPanqueque.T.WC
