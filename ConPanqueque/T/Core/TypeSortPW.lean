import ConPanqueque.T.Core.HeadTypePW
import ConPanqueque.T.Core.NumArgs
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# PropRead's `typeSortPWGo`

Peel the ∀ telescope counting binders; a sort is `never`; else the residual's head (`headTypePW`) at the walk's
current fuel.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc
open ConLeche (Level Name)

def tgF := ofString "ptg_tgf"
def tgR := ofString "ptg_tgr"
def tgE := ofString "ptg_tge"
def tgD := ofString "ptg_tgd"
def tgB := ofString "ptg_tgb"
def tgH := ofString "ptg_tgh"
def tgN := ofString "ptg_tgn"
def tgS := ofString "ptg_tgs"
def fTg := ofString "typeSortPWGo"

@[simp] theorem ptg_tgF_ne_tgR : tgF ≠ tgR := by decide
@[simp] theorem ptg_tgF_ne_tgE : tgF ≠ tgE := by decide
@[simp] theorem ptg_tgF_ne_tgD : tgF ≠ tgD := by decide
@[simp] theorem ptg_tgF_ne_tgB : tgF ≠ tgB := by decide
@[simp] theorem ptg_tgF_ne_tgH : tgF ≠ tgH := by decide
@[simp] theorem ptg_tgF_ne_tgN : tgF ≠ tgN := by decide
@[simp] theorem ptg_tgF_ne_tgS : tgF ≠ tgS := by decide
@[simp] theorem ptg_tgF_ne_lFl : tgF ≠ lFl := by decide
@[simp] theorem ptg_lFl_ne_tgF : lFl ≠ tgF := by decide
@[simp] theorem ptg_tgF_ne_lDh : tgF ≠ lDh := by decide
@[simp] theorem ptg_lDh_ne_tgF : lDh ≠ tgF := by decide
@[simp] theorem ptg_tgF_ne_lDt : tgF ≠ lDt := by decide
@[simp] theorem ptg_lDt_ne_tgF : lDt ≠ tgF := by decide
@[simp] theorem ptg_tgF_ne_lDg : tgF ≠ lDg := by decide
@[simp] theorem ptg_lDg_ne_tgF : lDg ≠ tgF := by decide
@[simp] theorem ptg_tgF_ne_lDi : tgF ≠ lDi := by decide
@[simp] theorem ptg_lDi_ne_tgF : lDi ≠ tgF := by decide
@[simp] theorem ptg_tgF_ne_lRp : tgF ≠ lRp := by decide
@[simp] theorem ptg_lRp_ne_tgF : lRp ≠ tgF := by decide
@[simp] theorem ptg_tgF_ne_lRn : tgF ≠ lRn := by decide
@[simp] theorem ptg_lRn_ne_tgF : lRn ≠ tgF := by decide
@[simp] theorem ptg_tgF_ne_lFle : tgF ≠ lFle := by decide
@[simp] theorem ptg_lFle_ne_tgF : lFle ≠ tgF := by decide
@[simp] theorem ptg_tgF_ne_lKb : tgF ≠ lKb := by decide
@[simp] theorem ptg_lKb_ne_tgF : lKb ≠ tgF := by decide
@[simp] theorem ptg_tgF_ne_lDir : tgF ≠ lDir := by decide
@[simp] theorem ptg_lDir_ne_tgF : lDir ≠ tgF := by decide
@[simp] theorem ptg_tgF_ne_lFln : tgF ≠ lFln := by decide
@[simp] theorem ptg_lFln_ne_tgF : lFln ≠ tgF := by decide
@[simp] theorem ptg_tgF_ne_lFll : tgF ≠ lFll := by decide
@[simp] theorem ptg_lFll_ne_tgF : lFll ≠ tgF := by decide
@[simp] theorem ptg_tgF_ne_lFls : tgF ≠ lFls := by decide
@[simp] theorem ptg_lFls_ne_tgF : lFls ≠ tgF := by decide
@[simp] theorem ptg_tgF_ne_kFu : tgF ≠ kFu := by decide
@[simp] theorem ptg_kFu_ne_tgF : kFu ≠ tgF := by decide
@[simp] theorem ptg_tgF_ne_kD : tgF ≠ kD := by decide
@[simp] theorem ptg_kD_ne_tgF : kD ≠ tgF := by decide
@[simp] theorem ptg_tgR_ne_tgF : tgR ≠ tgF := by decide
@[simp] theorem ptg_tgR_ne_tgE : tgR ≠ tgE := by decide
@[simp] theorem ptg_tgR_ne_tgD : tgR ≠ tgD := by decide
@[simp] theorem ptg_tgR_ne_tgB : tgR ≠ tgB := by decide
@[simp] theorem ptg_tgR_ne_tgH : tgR ≠ tgH := by decide
@[simp] theorem ptg_tgR_ne_tgN : tgR ≠ tgN := by decide
@[simp] theorem ptg_tgR_ne_tgS : tgR ≠ tgS := by decide
@[simp] theorem ptg_tgR_ne_lFl : tgR ≠ lFl := by decide
@[simp] theorem ptg_lFl_ne_tgR : lFl ≠ tgR := by decide
@[simp] theorem ptg_tgR_ne_lDh : tgR ≠ lDh := by decide
@[simp] theorem ptg_lDh_ne_tgR : lDh ≠ tgR := by decide
@[simp] theorem ptg_tgR_ne_lDt : tgR ≠ lDt := by decide
@[simp] theorem ptg_lDt_ne_tgR : lDt ≠ tgR := by decide
@[simp] theorem ptg_tgR_ne_lDg : tgR ≠ lDg := by decide
@[simp] theorem ptg_lDg_ne_tgR : lDg ≠ tgR := by decide
@[simp] theorem ptg_tgR_ne_lDi : tgR ≠ lDi := by decide
@[simp] theorem ptg_lDi_ne_tgR : lDi ≠ tgR := by decide
@[simp] theorem ptg_tgR_ne_lRp : tgR ≠ lRp := by decide
@[simp] theorem ptg_lRp_ne_tgR : lRp ≠ tgR := by decide
@[simp] theorem ptg_tgR_ne_lRn : tgR ≠ lRn := by decide
@[simp] theorem ptg_lRn_ne_tgR : lRn ≠ tgR := by decide
@[simp] theorem ptg_tgR_ne_lFle : tgR ≠ lFle := by decide
@[simp] theorem ptg_lFle_ne_tgR : lFle ≠ tgR := by decide
@[simp] theorem ptg_tgR_ne_lKb : tgR ≠ lKb := by decide
@[simp] theorem ptg_lKb_ne_tgR : lKb ≠ tgR := by decide
@[simp] theorem ptg_tgR_ne_lDir : tgR ≠ lDir := by decide
@[simp] theorem ptg_lDir_ne_tgR : lDir ≠ tgR := by decide
@[simp] theorem ptg_tgR_ne_lFln : tgR ≠ lFln := by decide
@[simp] theorem ptg_lFln_ne_tgR : lFln ≠ tgR := by decide
@[simp] theorem ptg_tgR_ne_lFll : tgR ≠ lFll := by decide
@[simp] theorem ptg_lFll_ne_tgR : lFll ≠ tgR := by decide
@[simp] theorem ptg_tgR_ne_lFls : tgR ≠ lFls := by decide
@[simp] theorem ptg_lFls_ne_tgR : lFls ≠ tgR := by decide
@[simp] theorem ptg_tgR_ne_kFu : tgR ≠ kFu := by decide
@[simp] theorem ptg_kFu_ne_tgR : kFu ≠ tgR := by decide
@[simp] theorem ptg_tgR_ne_kD : tgR ≠ kD := by decide
@[simp] theorem ptg_kD_ne_tgR : kD ≠ tgR := by decide
@[simp] theorem ptg_tgE_ne_tgF : tgE ≠ tgF := by decide
@[simp] theorem ptg_tgE_ne_tgR : tgE ≠ tgR := by decide
@[simp] theorem ptg_tgE_ne_tgD : tgE ≠ tgD := by decide
@[simp] theorem ptg_tgE_ne_tgB : tgE ≠ tgB := by decide
@[simp] theorem ptg_tgE_ne_tgH : tgE ≠ tgH := by decide
@[simp] theorem ptg_tgE_ne_tgN : tgE ≠ tgN := by decide
@[simp] theorem ptg_tgE_ne_tgS : tgE ≠ tgS := by decide
@[simp] theorem ptg_tgE_ne_lFl : tgE ≠ lFl := by decide
@[simp] theorem ptg_lFl_ne_tgE : lFl ≠ tgE := by decide
@[simp] theorem ptg_tgE_ne_lDh : tgE ≠ lDh := by decide
@[simp] theorem ptg_lDh_ne_tgE : lDh ≠ tgE := by decide
@[simp] theorem ptg_tgE_ne_lDt : tgE ≠ lDt := by decide
@[simp] theorem ptg_lDt_ne_tgE : lDt ≠ tgE := by decide
@[simp] theorem ptg_tgE_ne_lDg : tgE ≠ lDg := by decide
@[simp] theorem ptg_lDg_ne_tgE : lDg ≠ tgE := by decide
@[simp] theorem ptg_tgE_ne_lDi : tgE ≠ lDi := by decide
@[simp] theorem ptg_lDi_ne_tgE : lDi ≠ tgE := by decide
@[simp] theorem ptg_tgE_ne_lRp : tgE ≠ lRp := by decide
@[simp] theorem ptg_lRp_ne_tgE : lRp ≠ tgE := by decide
@[simp] theorem ptg_tgE_ne_lRn : tgE ≠ lRn := by decide
@[simp] theorem ptg_lRn_ne_tgE : lRn ≠ tgE := by decide
@[simp] theorem ptg_tgE_ne_lFle : tgE ≠ lFle := by decide
@[simp] theorem ptg_lFle_ne_tgE : lFle ≠ tgE := by decide
@[simp] theorem ptg_tgE_ne_lKb : tgE ≠ lKb := by decide
@[simp] theorem ptg_lKb_ne_tgE : lKb ≠ tgE := by decide
@[simp] theorem ptg_tgE_ne_lDir : tgE ≠ lDir := by decide
@[simp] theorem ptg_lDir_ne_tgE : lDir ≠ tgE := by decide
@[simp] theorem ptg_tgE_ne_lFln : tgE ≠ lFln := by decide
@[simp] theorem ptg_lFln_ne_tgE : lFln ≠ tgE := by decide
@[simp] theorem ptg_tgE_ne_lFll : tgE ≠ lFll := by decide
@[simp] theorem ptg_lFll_ne_tgE : lFll ≠ tgE := by decide
@[simp] theorem ptg_tgE_ne_lFls : tgE ≠ lFls := by decide
@[simp] theorem ptg_lFls_ne_tgE : lFls ≠ tgE := by decide
@[simp] theorem ptg_tgE_ne_kFu : tgE ≠ kFu := by decide
@[simp] theorem ptg_kFu_ne_tgE : kFu ≠ tgE := by decide
@[simp] theorem ptg_tgE_ne_kD : tgE ≠ kD := by decide
@[simp] theorem ptg_kD_ne_tgE : kD ≠ tgE := by decide
@[simp] theorem ptg_tgD_ne_tgF : tgD ≠ tgF := by decide
@[simp] theorem ptg_tgD_ne_tgR : tgD ≠ tgR := by decide
@[simp] theorem ptg_tgD_ne_tgE : tgD ≠ tgE := by decide
@[simp] theorem ptg_tgD_ne_tgB : tgD ≠ tgB := by decide
@[simp] theorem ptg_tgD_ne_tgH : tgD ≠ tgH := by decide
@[simp] theorem ptg_tgD_ne_tgN : tgD ≠ tgN := by decide
@[simp] theorem ptg_tgD_ne_tgS : tgD ≠ tgS := by decide
@[simp] theorem ptg_tgD_ne_lFl : tgD ≠ lFl := by decide
@[simp] theorem ptg_lFl_ne_tgD : lFl ≠ tgD := by decide
@[simp] theorem ptg_tgD_ne_lDh : tgD ≠ lDh := by decide
@[simp] theorem ptg_lDh_ne_tgD : lDh ≠ tgD := by decide
@[simp] theorem ptg_tgD_ne_lDt : tgD ≠ lDt := by decide
@[simp] theorem ptg_lDt_ne_tgD : lDt ≠ tgD := by decide
@[simp] theorem ptg_tgD_ne_lDg : tgD ≠ lDg := by decide
@[simp] theorem ptg_lDg_ne_tgD : lDg ≠ tgD := by decide
@[simp] theorem ptg_tgD_ne_lDi : tgD ≠ lDi := by decide
@[simp] theorem ptg_lDi_ne_tgD : lDi ≠ tgD := by decide
@[simp] theorem ptg_tgD_ne_lRp : tgD ≠ lRp := by decide
@[simp] theorem ptg_lRp_ne_tgD : lRp ≠ tgD := by decide
@[simp] theorem ptg_tgD_ne_lRn : tgD ≠ lRn := by decide
@[simp] theorem ptg_lRn_ne_tgD : lRn ≠ tgD := by decide
@[simp] theorem ptg_tgD_ne_lFle : tgD ≠ lFle := by decide
@[simp] theorem ptg_lFle_ne_tgD : lFle ≠ tgD := by decide
@[simp] theorem ptg_tgD_ne_lKb : tgD ≠ lKb := by decide
@[simp] theorem ptg_lKb_ne_tgD : lKb ≠ tgD := by decide
@[simp] theorem ptg_tgD_ne_lDir : tgD ≠ lDir := by decide
@[simp] theorem ptg_lDir_ne_tgD : lDir ≠ tgD := by decide
@[simp] theorem ptg_tgD_ne_lFln : tgD ≠ lFln := by decide
@[simp] theorem ptg_lFln_ne_tgD : lFln ≠ tgD := by decide
@[simp] theorem ptg_tgD_ne_lFll : tgD ≠ lFll := by decide
@[simp] theorem ptg_lFll_ne_tgD : lFll ≠ tgD := by decide
@[simp] theorem ptg_tgD_ne_lFls : tgD ≠ lFls := by decide
@[simp] theorem ptg_lFls_ne_tgD : lFls ≠ tgD := by decide
@[simp] theorem ptg_tgD_ne_kFu : tgD ≠ kFu := by decide
@[simp] theorem ptg_kFu_ne_tgD : kFu ≠ tgD := by decide
@[simp] theorem ptg_tgD_ne_kD : tgD ≠ kD := by decide
@[simp] theorem ptg_kD_ne_tgD : kD ≠ tgD := by decide
@[simp] theorem ptg_tgB_ne_tgF : tgB ≠ tgF := by decide
@[simp] theorem ptg_tgB_ne_tgR : tgB ≠ tgR := by decide
@[simp] theorem ptg_tgB_ne_tgE : tgB ≠ tgE := by decide
@[simp] theorem ptg_tgB_ne_tgD : tgB ≠ tgD := by decide
@[simp] theorem ptg_tgB_ne_tgH : tgB ≠ tgH := by decide
@[simp] theorem ptg_tgB_ne_tgN : tgB ≠ tgN := by decide
@[simp] theorem ptg_tgB_ne_tgS : tgB ≠ tgS := by decide
@[simp] theorem ptg_tgB_ne_lFl : tgB ≠ lFl := by decide
@[simp] theorem ptg_lFl_ne_tgB : lFl ≠ tgB := by decide
@[simp] theorem ptg_tgB_ne_lDh : tgB ≠ lDh := by decide
@[simp] theorem ptg_lDh_ne_tgB : lDh ≠ tgB := by decide
@[simp] theorem ptg_tgB_ne_lDt : tgB ≠ lDt := by decide
@[simp] theorem ptg_lDt_ne_tgB : lDt ≠ tgB := by decide
@[simp] theorem ptg_tgB_ne_lDg : tgB ≠ lDg := by decide
@[simp] theorem ptg_lDg_ne_tgB : lDg ≠ tgB := by decide
@[simp] theorem ptg_tgB_ne_lDi : tgB ≠ lDi := by decide
@[simp] theorem ptg_lDi_ne_tgB : lDi ≠ tgB := by decide
@[simp] theorem ptg_tgB_ne_lRp : tgB ≠ lRp := by decide
@[simp] theorem ptg_lRp_ne_tgB : lRp ≠ tgB := by decide
@[simp] theorem ptg_tgB_ne_lRn : tgB ≠ lRn := by decide
@[simp] theorem ptg_lRn_ne_tgB : lRn ≠ tgB := by decide
@[simp] theorem ptg_tgB_ne_lFle : tgB ≠ lFle := by decide
@[simp] theorem ptg_lFle_ne_tgB : lFle ≠ tgB := by decide
@[simp] theorem ptg_tgB_ne_lKb : tgB ≠ lKb := by decide
@[simp] theorem ptg_lKb_ne_tgB : lKb ≠ tgB := by decide
@[simp] theorem ptg_tgB_ne_lDir : tgB ≠ lDir := by decide
@[simp] theorem ptg_lDir_ne_tgB : lDir ≠ tgB := by decide
@[simp] theorem ptg_tgB_ne_lFln : tgB ≠ lFln := by decide
@[simp] theorem ptg_lFln_ne_tgB : lFln ≠ tgB := by decide
@[simp] theorem ptg_tgB_ne_lFll : tgB ≠ lFll := by decide
@[simp] theorem ptg_lFll_ne_tgB : lFll ≠ tgB := by decide
@[simp] theorem ptg_tgB_ne_lFls : tgB ≠ lFls := by decide
@[simp] theorem ptg_lFls_ne_tgB : lFls ≠ tgB := by decide
@[simp] theorem ptg_tgB_ne_kFu : tgB ≠ kFu := by decide
@[simp] theorem ptg_kFu_ne_tgB : kFu ≠ tgB := by decide
@[simp] theorem ptg_tgB_ne_kD : tgB ≠ kD := by decide
@[simp] theorem ptg_kD_ne_tgB : kD ≠ tgB := by decide
@[simp] theorem ptg_tgH_ne_tgF : tgH ≠ tgF := by decide
@[simp] theorem ptg_tgH_ne_tgR : tgH ≠ tgR := by decide
@[simp] theorem ptg_tgH_ne_tgE : tgH ≠ tgE := by decide
@[simp] theorem ptg_tgH_ne_tgD : tgH ≠ tgD := by decide
@[simp] theorem ptg_tgH_ne_tgB : tgH ≠ tgB := by decide
@[simp] theorem ptg_tgH_ne_tgN : tgH ≠ tgN := by decide
@[simp] theorem ptg_tgH_ne_tgS : tgH ≠ tgS := by decide
@[simp] theorem ptg_tgH_ne_lFl : tgH ≠ lFl := by decide
@[simp] theorem ptg_lFl_ne_tgH : lFl ≠ tgH := by decide
@[simp] theorem ptg_tgH_ne_lDh : tgH ≠ lDh := by decide
@[simp] theorem ptg_lDh_ne_tgH : lDh ≠ tgH := by decide
@[simp] theorem ptg_tgH_ne_lDt : tgH ≠ lDt := by decide
@[simp] theorem ptg_lDt_ne_tgH : lDt ≠ tgH := by decide
@[simp] theorem ptg_tgH_ne_lDg : tgH ≠ lDg := by decide
@[simp] theorem ptg_lDg_ne_tgH : lDg ≠ tgH := by decide
@[simp] theorem ptg_tgH_ne_lDi : tgH ≠ lDi := by decide
@[simp] theorem ptg_lDi_ne_tgH : lDi ≠ tgH := by decide
@[simp] theorem ptg_tgH_ne_lRp : tgH ≠ lRp := by decide
@[simp] theorem ptg_lRp_ne_tgH : lRp ≠ tgH := by decide
@[simp] theorem ptg_tgH_ne_lRn : tgH ≠ lRn := by decide
@[simp] theorem ptg_lRn_ne_tgH : lRn ≠ tgH := by decide
@[simp] theorem ptg_tgH_ne_lFle : tgH ≠ lFle := by decide
@[simp] theorem ptg_lFle_ne_tgH : lFle ≠ tgH := by decide
@[simp] theorem ptg_tgH_ne_lKb : tgH ≠ lKb := by decide
@[simp] theorem ptg_lKb_ne_tgH : lKb ≠ tgH := by decide
@[simp] theorem ptg_tgH_ne_lDir : tgH ≠ lDir := by decide
@[simp] theorem ptg_lDir_ne_tgH : lDir ≠ tgH := by decide
@[simp] theorem ptg_tgH_ne_lFln : tgH ≠ lFln := by decide
@[simp] theorem ptg_lFln_ne_tgH : lFln ≠ tgH := by decide
@[simp] theorem ptg_tgH_ne_lFll : tgH ≠ lFll := by decide
@[simp] theorem ptg_lFll_ne_tgH : lFll ≠ tgH := by decide
@[simp] theorem ptg_tgH_ne_lFls : tgH ≠ lFls := by decide
@[simp] theorem ptg_lFls_ne_tgH : lFls ≠ tgH := by decide
@[simp] theorem ptg_tgH_ne_kFu : tgH ≠ kFu := by decide
@[simp] theorem ptg_kFu_ne_tgH : kFu ≠ tgH := by decide
@[simp] theorem ptg_tgH_ne_kD : tgH ≠ kD := by decide
@[simp] theorem ptg_kD_ne_tgH : kD ≠ tgH := by decide
@[simp] theorem ptg_tgN_ne_tgF : tgN ≠ tgF := by decide
@[simp] theorem ptg_tgN_ne_tgR : tgN ≠ tgR := by decide
@[simp] theorem ptg_tgN_ne_tgE : tgN ≠ tgE := by decide
@[simp] theorem ptg_tgN_ne_tgD : tgN ≠ tgD := by decide
@[simp] theorem ptg_tgN_ne_tgB : tgN ≠ tgB := by decide
@[simp] theorem ptg_tgN_ne_tgH : tgN ≠ tgH := by decide
@[simp] theorem ptg_tgN_ne_tgS : tgN ≠ tgS := by decide
@[simp] theorem ptg_tgN_ne_lFl : tgN ≠ lFl := by decide
@[simp] theorem ptg_lFl_ne_tgN : lFl ≠ tgN := by decide
@[simp] theorem ptg_tgN_ne_lDh : tgN ≠ lDh := by decide
@[simp] theorem ptg_lDh_ne_tgN : lDh ≠ tgN := by decide
@[simp] theorem ptg_tgN_ne_lDt : tgN ≠ lDt := by decide
@[simp] theorem ptg_lDt_ne_tgN : lDt ≠ tgN := by decide
@[simp] theorem ptg_tgN_ne_lDg : tgN ≠ lDg := by decide
@[simp] theorem ptg_lDg_ne_tgN : lDg ≠ tgN := by decide
@[simp] theorem ptg_tgN_ne_lDi : tgN ≠ lDi := by decide
@[simp] theorem ptg_lDi_ne_tgN : lDi ≠ tgN := by decide
@[simp] theorem ptg_tgN_ne_lRp : tgN ≠ lRp := by decide
@[simp] theorem ptg_lRp_ne_tgN : lRp ≠ tgN := by decide
@[simp] theorem ptg_tgN_ne_lRn : tgN ≠ lRn := by decide
@[simp] theorem ptg_lRn_ne_tgN : lRn ≠ tgN := by decide
@[simp] theorem ptg_tgN_ne_lFle : tgN ≠ lFle := by decide
@[simp] theorem ptg_lFle_ne_tgN : lFle ≠ tgN := by decide
@[simp] theorem ptg_tgN_ne_lKb : tgN ≠ lKb := by decide
@[simp] theorem ptg_lKb_ne_tgN : lKb ≠ tgN := by decide
@[simp] theorem ptg_tgN_ne_lDir : tgN ≠ lDir := by decide
@[simp] theorem ptg_lDir_ne_tgN : lDir ≠ tgN := by decide
@[simp] theorem ptg_tgN_ne_lFln : tgN ≠ lFln := by decide
@[simp] theorem ptg_lFln_ne_tgN : lFln ≠ tgN := by decide
@[simp] theorem ptg_tgN_ne_lFll : tgN ≠ lFll := by decide
@[simp] theorem ptg_lFll_ne_tgN : lFll ≠ tgN := by decide
@[simp] theorem ptg_tgN_ne_lFls : tgN ≠ lFls := by decide
@[simp] theorem ptg_lFls_ne_tgN : lFls ≠ tgN := by decide
@[simp] theorem ptg_tgN_ne_kFu : tgN ≠ kFu := by decide
@[simp] theorem ptg_kFu_ne_tgN : kFu ≠ tgN := by decide
@[simp] theorem ptg_tgN_ne_kD : tgN ≠ kD := by decide
@[simp] theorem ptg_kD_ne_tgN : kD ≠ tgN := by decide
@[simp] theorem ptg_tgS_ne_tgF : tgS ≠ tgF := by decide
@[simp] theorem ptg_tgS_ne_tgR : tgS ≠ tgR := by decide
@[simp] theorem ptg_tgS_ne_tgE : tgS ≠ tgE := by decide
@[simp] theorem ptg_tgS_ne_tgD : tgS ≠ tgD := by decide
@[simp] theorem ptg_tgS_ne_tgB : tgS ≠ tgB := by decide
@[simp] theorem ptg_tgS_ne_tgH : tgS ≠ tgH := by decide
@[simp] theorem ptg_tgS_ne_tgN : tgS ≠ tgN := by decide
@[simp] theorem ptg_tgS_ne_lFl : tgS ≠ lFl := by decide
@[simp] theorem ptg_lFl_ne_tgS : lFl ≠ tgS := by decide
@[simp] theorem ptg_tgS_ne_lDh : tgS ≠ lDh := by decide
@[simp] theorem ptg_lDh_ne_tgS : lDh ≠ tgS := by decide
@[simp] theorem ptg_tgS_ne_lDt : tgS ≠ lDt := by decide
@[simp] theorem ptg_lDt_ne_tgS : lDt ≠ tgS := by decide
@[simp] theorem ptg_tgS_ne_lDg : tgS ≠ lDg := by decide
@[simp] theorem ptg_lDg_ne_tgS : lDg ≠ tgS := by decide
@[simp] theorem ptg_tgS_ne_lDi : tgS ≠ lDi := by decide
@[simp] theorem ptg_lDi_ne_tgS : lDi ≠ tgS := by decide
@[simp] theorem ptg_tgS_ne_lRp : tgS ≠ lRp := by decide
@[simp] theorem ptg_lRp_ne_tgS : lRp ≠ tgS := by decide
@[simp] theorem ptg_tgS_ne_lRn : tgS ≠ lRn := by decide
@[simp] theorem ptg_lRn_ne_tgS : lRn ≠ tgS := by decide
@[simp] theorem ptg_tgS_ne_lFle : tgS ≠ lFle := by decide
@[simp] theorem ptg_lFle_ne_tgS : lFle ≠ tgS := by decide
@[simp] theorem ptg_tgS_ne_lKb : tgS ≠ lKb := by decide
@[simp] theorem ptg_lKb_ne_tgS : lKb ≠ tgS := by decide
@[simp] theorem ptg_tgS_ne_lDir : tgS ≠ lDir := by decide
@[simp] theorem ptg_lDir_ne_tgS : lDir ≠ tgS := by decide
@[simp] theorem ptg_tgS_ne_lFln : tgS ≠ lFln := by decide
@[simp] theorem ptg_lFln_ne_tgS : lFln ≠ tgS := by decide
@[simp] theorem ptg_tgS_ne_lFll : tgS ≠ lFll := by decide
@[simp] theorem ptg_lFll_ne_tgS : lFll ≠ tgS := by decide
@[simp] theorem ptg_tgS_ne_lFls : tgS ≠ lFls := by decide
@[simp] theorem ptg_lFls_ne_tgS : lFls ≠ tgS := by decide
@[simp] theorem ptg_tgS_ne_kFu : tgS ≠ kFu := by decide
@[simp] theorem ptg_kFu_ne_tgS : kFu ≠ tgS := by decide
@[simp] theorem ptg_tgS_ne_kD : tgS ≠ kD := by decide
@[simp] theorem ptg_kD_ne_tgS : kD ≠ tgS := by decide

def tgParams : List MlS := [tgF, tgR, tgE, tgD]
def tgLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, tgB, tgH, tgN, tgS]
def tgBody (C : Ctx) : ProgHOL 64 := prologue tgLocals (.ite (.cmp .equal (vv tgF) (.const 0)) hang (.ite (tagIsE tgE 6) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv tgE)) (.seq eViewP (.seq (.assign .local tgB (.load .one (.op .add [(vv lRp), (.const 8)]))) (.seq (.call (some (some (.local, tgS), none)) fTg [(.op .sub [(vv tgF), (.const 1)]), (vv tgR), (vv tgB), (.op .add [(vv tgD), (.const 1)])]) (.return (vv tgS))))))) (.ite (tagIsE tgE 2) (.return (.const 1)) (.seq (.call (some (some (.local, tgH), none)) fGetAppFn [(.op .sub [(vv tgF), (.const 1)]), (vv tgE)]) (.seq (.call (some (some (.local, tgN), none)) fNa [(.op .sub [(vv tgF), (.const 1)]), (vv tgE)]) (.seq (.call (some (some (.local, tgS), none)) fHtp [(.op .sub [(vv tgF), (.const 1)]), (vv tgR), (vv tgD), (vv tgH), (vv tgN)]) (.return (vv tgS))))))))

structure TgCodes (C : Ctx) : Prop where
  gaf : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  na : C.code.lookup fNa = some (naParams.map (fun p => (p, ShapeHOL.one)), naBody, .one)
  ht : C.code.lookup fHtp = some (htParams.map (fun p => (p, ShapeHOL.one)), htBody C, .one)
  htc : HtCodes C
  self : C.code.lookup fTg = some (tgParams.map (fun p => (p, ShapeHOL.one)), tgBody C, .one)

section
variable {σ : Type}

theorem tg_spec (C : Ctx) (hok : CtxOK C) (hc : TgCodes C) (s : AState) (hwf : LStoreWF s.store.ls) (hrd : RdOK s)
    (hSD : ∀ h u, s.store.view h = some (.sort u) → ∃ l, denoteL s.store.ls u = some l)
    (hLP : ∀ c ci, C.fe.find? c = some ci → ∃ ks, Frontend.denoteNList s.store.ns ci.toConstantVal.levelParams = some ks)
    (hLPl : ∀ c ci, C.fe.find? c = some ci → ci.toConstantVal.levelParams.length < 2 ^ 60)
    (hLS : ∀ us uh, s.store.lss.view us = some uh → ∃ vs, denoteLs s.store.lss us = some vs ∧ ∃ hl : vs.length = uh.length,
      ∀ j (hj : j < uh.length), denoteL s.store.ls uh[j] = some (vs[j]'(by rw [hl]; exact hj))) :
    ∀ (F : Nat) (root R : EIdx) (d : Nat) (H : List (BitVec 64)), C.H <+: H → F < 2 ^ 62 → d + F < 2 ^ 62 →
      SpecR (σ := σ) (Pre (ctxH C H) s (tgParams.zip [BitVec.ofNat 64 F, Enc.idxW root, Enc.idxW R, BitVec.ofNat 64 d]))
        (tgBody C) s (typeSortPWGo C.fe root F R d) (PostSA (ctxH C H) s) := by
  intro F
  induction F with
  | zero =>
    intro root R d H hpH _ _
    refine specR_prologue (postSA_locals _ s) (Knot.params_none _ tgLocals tgParams _ (by decide) (by decide)) ?_
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get, tgParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
  | succ F ih =>
    intro root R d H hpH hF hdF
    refine specR_prologue (postSA_locals _ s) (Knot.params_none _ tgLocals tgParams _ (by decide) (by decide)) ?_
    have hne := ofNat_succ_ne F (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, tgParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
    rw [typeSortPWGo]
    refine Knot.specR_tagIteV tgE R 6 (by decide) (by decide) (by simp +decide [Env.get, tgParams, ctxEnv]) (fun htg => ?_) (fun htg => ?_)
    · rw [ite_eq_left (show (R.tag == ETag.forallE) = true by simp [htg, ETag.forallE])]
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv tgE) (Enc.idxW R) (by decide) (by simp +decide [Env.get, tgParams, ctxEnv]) ?_
      refine specR_viewP (C := ctxH C H) R (by simp) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
        (fun v P hv htn _ => ?_)
      have h6 : v.tagN = 6 := by rw [htn, htg]; rfl
      obtain ⟨ty, b, rfl⟩ : ∃ ty b, v = .forallE ty b := by cases v <;> simp [ENodeView.tagN] at h6 ⊢
      have hvb : s.store.viewBind R = some (ty, b) := viewBind_of_view_forallE (by rw [htg]; rfl) hv
      refine specR_runBind (by rw [viewBind_run, hvb]) ?_
      dsimp only
      refine specR_loadI' tgB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      refine specR_congr (m' := typeSortPWGo C.fe root F b (d + 1) >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H) tgS fTg tgParams [.op .sub [vv tgF, .const 1], vv tgR, vv tgB, .op .add [vv tgD, .const 1]] (tgBody C)
        [BitVec.ofNat 64 F, Enc.idxW root, Enc.idxW b, BitVec.ofNat 64 (d + 1)] (by decide) rfl (by decide) hc.self
        ⟨by simp +decide [sev, Env.get, tgParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, by simp +decide [Env.get, tgParams, ctxEnv], by simp, by simp +decide [sev, Env.get, tgParams, ctxEnv]; exact word_add1_eq d, trivial⟩
        (PostSA (ctxH C H) s) (fun r_ w s' H' => RdStep s s' ∧ optPW C H' s r_ w)
        (fun r_ w s' st ⟨hst, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hst, hw⟩, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tgParams _ rfl hlk) (ih root b (d + 1) H hpH (by omega) (by omega)))
        (fun r w s1 H1 hp1 ⟨hst, hw⟩ => ?_)
      exact specR_returnI _ w (by simp) (fun t ht => ⟨hst, H1, hp1, hw, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    rw [ite_eq_right (show ¬ (R.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg)]
    refine Knot.specR_tagIteV tgE R 2 (by decide) (by decide) (by simp +decide [Env.get, tgParams, ctxEnv]) (fun hts => ?_) (fun hts => ?_)
    · rw [ite_eq_left (show (R.tag == ETag.sort) = true by simp [hts, ETag.sort])]
      exact specR_returnI _ 1 rfl (fun t ht => ⟨rdStep_refl hrd, H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    rw [ite_eq_right (show ¬ (R.tag == ETag.sort) = true by simpa [ETag.sort] using hts)]
    refine specR_callNIM (C := ctxH C H) tgH fGetAppFn [pFu, pH] [.op .sub [vv tgF, .const 1], vv tgE]
      getAppFnBody [BitVec.ofNat 64 F, Enc.idxW R] (by decide) rfl (by decide) hc.gaf
      ⟨by simp +decide [sev, Env.get, tgParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, by simp +decide [Env.get, tgParams, ctxEnv], trivial⟩
      (fun x w' s' st => getAppFn F R s = .ok (x, s') ∧ Post (ctxH C H) s x w' s' st)
      (fun x w' s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
      (fun u hu _ hlk => specR_run (fun t ht => by
        subst ht
        exact getAppFn_spec (ctxH C H) hc.gaf F R s (by omega) t ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
      (fun fn w' s' st ⟨hrun, hw, hs, _⟩ => ?_)
    subst hw
    have hs' : s = s' := hs.symm
    subst hs'
    refine specR_callNIH (C := ctxH C H) tgN fNa naParams [.op .sub [vv tgF, .const 1], vv tgE] naBody
      [BitVec.ofNat 64 F, Enc.idxW R] (by decide) rfl (by decide) hc.na
      ⟨by simp +decide [sev, Env.get, tgParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, by simp +decide [Env.get, tgParams, ctxEnv], trivial⟩
      (PostNa (ctxH C H) s F) (fun a w s' H' => s' = s ∧ a ≤ F ∧ w = BitVec.ofNat 64 a ∧ H' = H)
      (fun a w s' st ⟨h1, h2, h3, h4⟩ => ⟨H, List.prefix_refl _, ⟨h1, h2, h3, rfl⟩, by subst h1; exact h4⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu naParams _ rfl hlk) (na_spec (ctxH C H) hc.na F R s (by omega)))
      (fun na w s1 H1 _ ⟨hs1, hna, hw, eH⟩ => ?_)
    subst s1; subst hw; subst H1
    refine specR_congr (m' := headTypePW C.fe F root d fn na >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H) tgS fHtp htParams [.op .sub [vv tgF, .const 1], vv tgR, vv tgD, vv tgH, vv tgN] (htBody C)
      [BitVec.ofNat 64 F, Enc.idxW root, BitVec.ofNat 64 d, Enc.idxW fn, BitVec.ofNat 64 na] (by decide) rfl (by decide) hc.ht
      ⟨by simp +decide [sev, Env.get, tgParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, by simp +decide [Env.get, tgParams, ctxEnv], by simp +decide [Env.get, tgParams, ctxEnv], by simp, by simp, trivial⟩
      (PostSA (ctxH C H) s) (fun r_ w s' H' => RdStep s s' ∧ optPW C H' s r_ w)
      (fun r_ w s' st ⟨hst, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hst, hw⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu htParams _ rfl hlk)
        (ht_spec C hok hc.htc F (by omega) s hwf hrd hSD hLP hLPl hLS H root d fn na hpH (by omega) (by omega)))
      (fun r w s2 H2 hp2 ⟨hst, hw⟩ => ?_)
    exact specR_returnI _ w (by simp) (fun t ht => ⟨hst, H2, hp2, hw, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
