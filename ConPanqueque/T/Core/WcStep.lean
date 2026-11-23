import ConPanqueque.T.Core.WhnfCore
import ConPanqueque.T.Ex.Inst1Fast
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `whnfCoreStep`: the dispatch

View the term: a value is `.done` itself; ζ instantiates the body (`instantiate1`); an application goes to the
stuck-spine step (ι) or the β spine; a projection to its step; a loose `bvar` declines. The β, ι and projection
steps are functions given by their specs.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot

def zN2 := ofString "wsn"
def zP2 := ofString "wsp"
def zI2 := ofString "wsi"
def zV2 := ofString "wsv"
def zB2 := ofString "wsb"
def zX2 := ofString "wsx"
def sN := ofString "wpn"
def sI := ofString "wpi"
def sP := ofString "wpp"
def fStuck := ofString "whnfStuck"
def fStepApp := ofString "whnfCoreStepApp"
def fStepProj := ofString "whnfCoreStepProj"

@[simp] theorem ws_zN2_ne_zP2 : zN2 ≠ zP2 := by decide
@[simp] theorem ws_zN2_ne_zI2 : zN2 ≠ zI2 := by decide
@[simp] theorem ws_zN2_ne_zV2 : zN2 ≠ zV2 := by decide
@[simp] theorem ws_zN2_ne_zB2 : zN2 ≠ zB2 := by decide
@[simp] theorem ws_zN2_ne_zX2 : zN2 ≠ zX2 := by decide
@[simp] theorem ws_zN2_ne_sN : zN2 ≠ sN := by decide
@[simp] theorem ws_zN2_ne_sI : zN2 ≠ sI := by decide
@[simp] theorem ws_zN2_ne_sP : zN2 ≠ sP := by decide
@[simp] theorem ws_zN2_ne_lFl : zN2 ≠ lFl := by decide
@[simp] theorem ws_lFl_ne_zN2 : lFl ≠ zN2 := by decide
@[simp] theorem ws_zN2_ne_lDh : zN2 ≠ lDh := by decide
@[simp] theorem ws_lDh_ne_zN2 : lDh ≠ zN2 := by decide
@[simp] theorem ws_zN2_ne_lDt : zN2 ≠ lDt := by decide
@[simp] theorem ws_lDt_ne_zN2 : lDt ≠ zN2 := by decide
@[simp] theorem ws_zN2_ne_lDg : zN2 ≠ lDg := by decide
@[simp] theorem ws_lDg_ne_zN2 : lDg ≠ zN2 := by decide
@[simp] theorem ws_zN2_ne_lDi : zN2 ≠ lDi := by decide
@[simp] theorem ws_lDi_ne_zN2 : lDi ≠ zN2 := by decide
@[simp] theorem ws_zN2_ne_lRp : zN2 ≠ lRp := by decide
@[simp] theorem ws_lRp_ne_zN2 : lRp ≠ zN2 := by decide
@[simp] theorem ws_zN2_ne_lRn : zN2 ≠ lRn := by decide
@[simp] theorem ws_lRn_ne_zN2 : lRn ≠ zN2 := by decide
@[simp] theorem ws_zN2_ne_kFu : zN2 ≠ kFu := by decide
@[simp] theorem ws_kFu_ne_zN2 : kFu ≠ zN2 := by decide
@[simp] theorem ws_zN2_ne_kC : zN2 ≠ kC := by decide
@[simp] theorem ws_kC_ne_zN2 : kC ≠ zN2 := by decide
@[simp] theorem ws_zN2_ne_kD : zN2 ≠ kD := by decide
@[simp] theorem ws_kD_ne_zN2 : kD ≠ zN2 := by decide
@[simp] theorem ws_zN2_ne_sH : zN2 ≠ sH := by decide
@[simp] theorem ws_sH_ne_zN2 : sH ≠ zN2 := by decide
@[simp] theorem ws_zN2_ne_sE : zN2 ≠ sE := by decide
@[simp] theorem ws_sE_ne_zN2 : sE ≠ zN2 := by decide
@[simp] theorem ws_zN2_ne_lFle : zN2 ≠ lFle := by decide
@[simp] theorem ws_lFle_ne_zN2 : lFle ≠ zN2 := by decide
@[simp] theorem ws_zN2_ne_lDir : zN2 ≠ lDir := by decide
@[simp] theorem ws_lDir_ne_zN2 : lDir ≠ zN2 := by decide
@[simp] theorem ws_zN2_ne_lKb : zN2 ≠ lKb := by decide
@[simp] theorem ws_lKb_ne_zN2 : lKb ≠ zN2 := by decide
@[simp] theorem ws_zN2_ne_pFu : zN2 ≠ pFu := by decide
@[simp] theorem ws_pFu_ne_zN2 : pFu ≠ zN2 := by decide
@[simp] theorem ws_zN2_ne_pH : zN2 ≠ pH := by decide
@[simp] theorem ws_pH_ne_zN2 : pH ≠ zN2 := by decide
@[simp] theorem ws_zP2_ne_zN2 : zP2 ≠ zN2 := by decide
@[simp] theorem ws_zP2_ne_zI2 : zP2 ≠ zI2 := by decide
@[simp] theorem ws_zP2_ne_zV2 : zP2 ≠ zV2 := by decide
@[simp] theorem ws_zP2_ne_zB2 : zP2 ≠ zB2 := by decide
@[simp] theorem ws_zP2_ne_zX2 : zP2 ≠ zX2 := by decide
@[simp] theorem ws_zP2_ne_sN : zP2 ≠ sN := by decide
@[simp] theorem ws_zP2_ne_sI : zP2 ≠ sI := by decide
@[simp] theorem ws_zP2_ne_sP : zP2 ≠ sP := by decide
@[simp] theorem ws_zP2_ne_lFl : zP2 ≠ lFl := by decide
@[simp] theorem ws_lFl_ne_zP2 : lFl ≠ zP2 := by decide
@[simp] theorem ws_zP2_ne_lDh : zP2 ≠ lDh := by decide
@[simp] theorem ws_lDh_ne_zP2 : lDh ≠ zP2 := by decide
@[simp] theorem ws_zP2_ne_lDt : zP2 ≠ lDt := by decide
@[simp] theorem ws_lDt_ne_zP2 : lDt ≠ zP2 := by decide
@[simp] theorem ws_zP2_ne_lDg : zP2 ≠ lDg := by decide
@[simp] theorem ws_lDg_ne_zP2 : lDg ≠ zP2 := by decide
@[simp] theorem ws_zP2_ne_lDi : zP2 ≠ lDi := by decide
@[simp] theorem ws_lDi_ne_zP2 : lDi ≠ zP2 := by decide
@[simp] theorem ws_zP2_ne_lRp : zP2 ≠ lRp := by decide
@[simp] theorem ws_lRp_ne_zP2 : lRp ≠ zP2 := by decide
@[simp] theorem ws_zP2_ne_lRn : zP2 ≠ lRn := by decide
@[simp] theorem ws_lRn_ne_zP2 : lRn ≠ zP2 := by decide
@[simp] theorem ws_zP2_ne_kFu : zP2 ≠ kFu := by decide
@[simp] theorem ws_kFu_ne_zP2 : kFu ≠ zP2 := by decide
@[simp] theorem ws_zP2_ne_kC : zP2 ≠ kC := by decide
@[simp] theorem ws_kC_ne_zP2 : kC ≠ zP2 := by decide
@[simp] theorem ws_zP2_ne_kD : zP2 ≠ kD := by decide
@[simp] theorem ws_kD_ne_zP2 : kD ≠ zP2 := by decide
@[simp] theorem ws_zP2_ne_sH : zP2 ≠ sH := by decide
@[simp] theorem ws_sH_ne_zP2 : sH ≠ zP2 := by decide
@[simp] theorem ws_zP2_ne_sE : zP2 ≠ sE := by decide
@[simp] theorem ws_sE_ne_zP2 : sE ≠ zP2 := by decide
@[simp] theorem ws_zP2_ne_lFle : zP2 ≠ lFle := by decide
@[simp] theorem ws_lFle_ne_zP2 : lFle ≠ zP2 := by decide
@[simp] theorem ws_zP2_ne_lDir : zP2 ≠ lDir := by decide
@[simp] theorem ws_lDir_ne_zP2 : lDir ≠ zP2 := by decide
@[simp] theorem ws_zP2_ne_lKb : zP2 ≠ lKb := by decide
@[simp] theorem ws_lKb_ne_zP2 : lKb ≠ zP2 := by decide
@[simp] theorem ws_zP2_ne_pFu : zP2 ≠ pFu := by decide
@[simp] theorem ws_pFu_ne_zP2 : pFu ≠ zP2 := by decide
@[simp] theorem ws_zP2_ne_pH : zP2 ≠ pH := by decide
@[simp] theorem ws_pH_ne_zP2 : pH ≠ zP2 := by decide
@[simp] theorem ws_zI2_ne_zN2 : zI2 ≠ zN2 := by decide
@[simp] theorem ws_zI2_ne_zP2 : zI2 ≠ zP2 := by decide
@[simp] theorem ws_zI2_ne_zV2 : zI2 ≠ zV2 := by decide
@[simp] theorem ws_zI2_ne_zB2 : zI2 ≠ zB2 := by decide
@[simp] theorem ws_zI2_ne_zX2 : zI2 ≠ zX2 := by decide
@[simp] theorem ws_zI2_ne_sN : zI2 ≠ sN := by decide
@[simp] theorem ws_zI2_ne_sI : zI2 ≠ sI := by decide
@[simp] theorem ws_zI2_ne_sP : zI2 ≠ sP := by decide
@[simp] theorem ws_zI2_ne_lFl : zI2 ≠ lFl := by decide
@[simp] theorem ws_lFl_ne_zI2 : lFl ≠ zI2 := by decide
@[simp] theorem ws_zI2_ne_lDh : zI2 ≠ lDh := by decide
@[simp] theorem ws_lDh_ne_zI2 : lDh ≠ zI2 := by decide
@[simp] theorem ws_zI2_ne_lDt : zI2 ≠ lDt := by decide
@[simp] theorem ws_lDt_ne_zI2 : lDt ≠ zI2 := by decide
@[simp] theorem ws_zI2_ne_lDg : zI2 ≠ lDg := by decide
@[simp] theorem ws_lDg_ne_zI2 : lDg ≠ zI2 := by decide
@[simp] theorem ws_zI2_ne_lDi : zI2 ≠ lDi := by decide
@[simp] theorem ws_lDi_ne_zI2 : lDi ≠ zI2 := by decide
@[simp] theorem ws_zI2_ne_lRp : zI2 ≠ lRp := by decide
@[simp] theorem ws_lRp_ne_zI2 : lRp ≠ zI2 := by decide
@[simp] theorem ws_zI2_ne_lRn : zI2 ≠ lRn := by decide
@[simp] theorem ws_lRn_ne_zI2 : lRn ≠ zI2 := by decide
@[simp] theorem ws_zI2_ne_kFu : zI2 ≠ kFu := by decide
@[simp] theorem ws_kFu_ne_zI2 : kFu ≠ zI2 := by decide
@[simp] theorem ws_zI2_ne_kC : zI2 ≠ kC := by decide
@[simp] theorem ws_kC_ne_zI2 : kC ≠ zI2 := by decide
@[simp] theorem ws_zI2_ne_kD : zI2 ≠ kD := by decide
@[simp] theorem ws_kD_ne_zI2 : kD ≠ zI2 := by decide
@[simp] theorem ws_zI2_ne_sH : zI2 ≠ sH := by decide
@[simp] theorem ws_sH_ne_zI2 : sH ≠ zI2 := by decide
@[simp] theorem ws_zI2_ne_sE : zI2 ≠ sE := by decide
@[simp] theorem ws_sE_ne_zI2 : sE ≠ zI2 := by decide
@[simp] theorem ws_zI2_ne_lFle : zI2 ≠ lFle := by decide
@[simp] theorem ws_lFle_ne_zI2 : lFle ≠ zI2 := by decide
@[simp] theorem ws_zI2_ne_lDir : zI2 ≠ lDir := by decide
@[simp] theorem ws_lDir_ne_zI2 : lDir ≠ zI2 := by decide
@[simp] theorem ws_zI2_ne_lKb : zI2 ≠ lKb := by decide
@[simp] theorem ws_lKb_ne_zI2 : lKb ≠ zI2 := by decide
@[simp] theorem ws_zI2_ne_pFu : zI2 ≠ pFu := by decide
@[simp] theorem ws_pFu_ne_zI2 : pFu ≠ zI2 := by decide
@[simp] theorem ws_zI2_ne_pH : zI2 ≠ pH := by decide
@[simp] theorem ws_pH_ne_zI2 : pH ≠ zI2 := by decide
@[simp] theorem ws_zV2_ne_zN2 : zV2 ≠ zN2 := by decide
@[simp] theorem ws_zV2_ne_zP2 : zV2 ≠ zP2 := by decide
@[simp] theorem ws_zV2_ne_zI2 : zV2 ≠ zI2 := by decide
@[simp] theorem ws_zV2_ne_zB2 : zV2 ≠ zB2 := by decide
@[simp] theorem ws_zV2_ne_zX2 : zV2 ≠ zX2 := by decide
@[simp] theorem ws_zV2_ne_sN : zV2 ≠ sN := by decide
@[simp] theorem ws_zV2_ne_sI : zV2 ≠ sI := by decide
@[simp] theorem ws_zV2_ne_sP : zV2 ≠ sP := by decide
@[simp] theorem ws_zV2_ne_lFl : zV2 ≠ lFl := by decide
@[simp] theorem ws_lFl_ne_zV2 : lFl ≠ zV2 := by decide
@[simp] theorem ws_zV2_ne_lDh : zV2 ≠ lDh := by decide
@[simp] theorem ws_lDh_ne_zV2 : lDh ≠ zV2 := by decide
@[simp] theorem ws_zV2_ne_lDt : zV2 ≠ lDt := by decide
@[simp] theorem ws_lDt_ne_zV2 : lDt ≠ zV2 := by decide
@[simp] theorem ws_zV2_ne_lDg : zV2 ≠ lDg := by decide
@[simp] theorem ws_lDg_ne_zV2 : lDg ≠ zV2 := by decide
@[simp] theorem ws_zV2_ne_lDi : zV2 ≠ lDi := by decide
@[simp] theorem ws_lDi_ne_zV2 : lDi ≠ zV2 := by decide
@[simp] theorem ws_zV2_ne_lRp : zV2 ≠ lRp := by decide
@[simp] theorem ws_lRp_ne_zV2 : lRp ≠ zV2 := by decide
@[simp] theorem ws_zV2_ne_lRn : zV2 ≠ lRn := by decide
@[simp] theorem ws_lRn_ne_zV2 : lRn ≠ zV2 := by decide
@[simp] theorem ws_zV2_ne_kFu : zV2 ≠ kFu := by decide
@[simp] theorem ws_kFu_ne_zV2 : kFu ≠ zV2 := by decide
@[simp] theorem ws_zV2_ne_kC : zV2 ≠ kC := by decide
@[simp] theorem ws_kC_ne_zV2 : kC ≠ zV2 := by decide
@[simp] theorem ws_zV2_ne_kD : zV2 ≠ kD := by decide
@[simp] theorem ws_kD_ne_zV2 : kD ≠ zV2 := by decide
@[simp] theorem ws_zV2_ne_sH : zV2 ≠ sH := by decide
@[simp] theorem ws_sH_ne_zV2 : sH ≠ zV2 := by decide
@[simp] theorem ws_zV2_ne_sE : zV2 ≠ sE := by decide
@[simp] theorem ws_sE_ne_zV2 : sE ≠ zV2 := by decide
@[simp] theorem ws_zV2_ne_lFle : zV2 ≠ lFle := by decide
@[simp] theorem ws_lFle_ne_zV2 : lFle ≠ zV2 := by decide
@[simp] theorem ws_zV2_ne_lDir : zV2 ≠ lDir := by decide
@[simp] theorem ws_lDir_ne_zV2 : lDir ≠ zV2 := by decide
@[simp] theorem ws_zV2_ne_lKb : zV2 ≠ lKb := by decide
@[simp] theorem ws_lKb_ne_zV2 : lKb ≠ zV2 := by decide
@[simp] theorem ws_zV2_ne_pFu : zV2 ≠ pFu := by decide
@[simp] theorem ws_pFu_ne_zV2 : pFu ≠ zV2 := by decide
@[simp] theorem ws_zV2_ne_pH : zV2 ≠ pH := by decide
@[simp] theorem ws_pH_ne_zV2 : pH ≠ zV2 := by decide
@[simp] theorem ws_zB2_ne_zN2 : zB2 ≠ zN2 := by decide
@[simp] theorem ws_zB2_ne_zP2 : zB2 ≠ zP2 := by decide
@[simp] theorem ws_zB2_ne_zI2 : zB2 ≠ zI2 := by decide
@[simp] theorem ws_zB2_ne_zV2 : zB2 ≠ zV2 := by decide
@[simp] theorem ws_zB2_ne_zX2 : zB2 ≠ zX2 := by decide
@[simp] theorem ws_zB2_ne_sN : zB2 ≠ sN := by decide
@[simp] theorem ws_zB2_ne_sI : zB2 ≠ sI := by decide
@[simp] theorem ws_zB2_ne_sP : zB2 ≠ sP := by decide
@[simp] theorem ws_zB2_ne_lFl : zB2 ≠ lFl := by decide
@[simp] theorem ws_lFl_ne_zB2 : lFl ≠ zB2 := by decide
@[simp] theorem ws_zB2_ne_lDh : zB2 ≠ lDh := by decide
@[simp] theorem ws_lDh_ne_zB2 : lDh ≠ zB2 := by decide
@[simp] theorem ws_zB2_ne_lDt : zB2 ≠ lDt := by decide
@[simp] theorem ws_lDt_ne_zB2 : lDt ≠ zB2 := by decide
@[simp] theorem ws_zB2_ne_lDg : zB2 ≠ lDg := by decide
@[simp] theorem ws_lDg_ne_zB2 : lDg ≠ zB2 := by decide
@[simp] theorem ws_zB2_ne_lDi : zB2 ≠ lDi := by decide
@[simp] theorem ws_lDi_ne_zB2 : lDi ≠ zB2 := by decide
@[simp] theorem ws_zB2_ne_lRp : zB2 ≠ lRp := by decide
@[simp] theorem ws_lRp_ne_zB2 : lRp ≠ zB2 := by decide
@[simp] theorem ws_zB2_ne_lRn : zB2 ≠ lRn := by decide
@[simp] theorem ws_lRn_ne_zB2 : lRn ≠ zB2 := by decide
@[simp] theorem ws_zB2_ne_kFu : zB2 ≠ kFu := by decide
@[simp] theorem ws_kFu_ne_zB2 : kFu ≠ zB2 := by decide
@[simp] theorem ws_zB2_ne_kC : zB2 ≠ kC := by decide
@[simp] theorem ws_kC_ne_zB2 : kC ≠ zB2 := by decide
@[simp] theorem ws_zB2_ne_kD : zB2 ≠ kD := by decide
@[simp] theorem ws_kD_ne_zB2 : kD ≠ zB2 := by decide
@[simp] theorem ws_zB2_ne_sH : zB2 ≠ sH := by decide
@[simp] theorem ws_sH_ne_zB2 : sH ≠ zB2 := by decide
@[simp] theorem ws_zB2_ne_sE : zB2 ≠ sE := by decide
@[simp] theorem ws_sE_ne_zB2 : sE ≠ zB2 := by decide
@[simp] theorem ws_zB2_ne_lFle : zB2 ≠ lFle := by decide
@[simp] theorem ws_lFle_ne_zB2 : lFle ≠ zB2 := by decide
@[simp] theorem ws_zB2_ne_lDir : zB2 ≠ lDir := by decide
@[simp] theorem ws_lDir_ne_zB2 : lDir ≠ zB2 := by decide
@[simp] theorem ws_zB2_ne_lKb : zB2 ≠ lKb := by decide
@[simp] theorem ws_lKb_ne_zB2 : lKb ≠ zB2 := by decide
@[simp] theorem ws_zB2_ne_pFu : zB2 ≠ pFu := by decide
@[simp] theorem ws_pFu_ne_zB2 : pFu ≠ zB2 := by decide
@[simp] theorem ws_zB2_ne_pH : zB2 ≠ pH := by decide
@[simp] theorem ws_pH_ne_zB2 : pH ≠ zB2 := by decide
@[simp] theorem ws_zX2_ne_zN2 : zX2 ≠ zN2 := by decide
@[simp] theorem ws_zX2_ne_zP2 : zX2 ≠ zP2 := by decide
@[simp] theorem ws_zX2_ne_zI2 : zX2 ≠ zI2 := by decide
@[simp] theorem ws_zX2_ne_zV2 : zX2 ≠ zV2 := by decide
@[simp] theorem ws_zX2_ne_zB2 : zX2 ≠ zB2 := by decide
@[simp] theorem ws_zX2_ne_sN : zX2 ≠ sN := by decide
@[simp] theorem ws_zX2_ne_sI : zX2 ≠ sI := by decide
@[simp] theorem ws_zX2_ne_sP : zX2 ≠ sP := by decide
@[simp] theorem ws_zX2_ne_lFl : zX2 ≠ lFl := by decide
@[simp] theorem ws_lFl_ne_zX2 : lFl ≠ zX2 := by decide
@[simp] theorem ws_zX2_ne_lDh : zX2 ≠ lDh := by decide
@[simp] theorem ws_lDh_ne_zX2 : lDh ≠ zX2 := by decide
@[simp] theorem ws_zX2_ne_lDt : zX2 ≠ lDt := by decide
@[simp] theorem ws_lDt_ne_zX2 : lDt ≠ zX2 := by decide
@[simp] theorem ws_zX2_ne_lDg : zX2 ≠ lDg := by decide
@[simp] theorem ws_lDg_ne_zX2 : lDg ≠ zX2 := by decide
@[simp] theorem ws_zX2_ne_lDi : zX2 ≠ lDi := by decide
@[simp] theorem ws_lDi_ne_zX2 : lDi ≠ zX2 := by decide
@[simp] theorem ws_zX2_ne_lRp : zX2 ≠ lRp := by decide
@[simp] theorem ws_lRp_ne_zX2 : lRp ≠ zX2 := by decide
@[simp] theorem ws_zX2_ne_lRn : zX2 ≠ lRn := by decide
@[simp] theorem ws_lRn_ne_zX2 : lRn ≠ zX2 := by decide
@[simp] theorem ws_zX2_ne_kFu : zX2 ≠ kFu := by decide
@[simp] theorem ws_kFu_ne_zX2 : kFu ≠ zX2 := by decide
@[simp] theorem ws_zX2_ne_kC : zX2 ≠ kC := by decide
@[simp] theorem ws_kC_ne_zX2 : kC ≠ zX2 := by decide
@[simp] theorem ws_zX2_ne_kD : zX2 ≠ kD := by decide
@[simp] theorem ws_kD_ne_zX2 : kD ≠ zX2 := by decide
@[simp] theorem ws_zX2_ne_sH : zX2 ≠ sH := by decide
@[simp] theorem ws_sH_ne_zX2 : sH ≠ zX2 := by decide
@[simp] theorem ws_zX2_ne_sE : zX2 ≠ sE := by decide
@[simp] theorem ws_sE_ne_zX2 : sE ≠ zX2 := by decide
@[simp] theorem ws_zX2_ne_lFle : zX2 ≠ lFle := by decide
@[simp] theorem ws_lFle_ne_zX2 : lFle ≠ zX2 := by decide
@[simp] theorem ws_zX2_ne_lDir : zX2 ≠ lDir := by decide
@[simp] theorem ws_lDir_ne_zX2 : lDir ≠ zX2 := by decide
@[simp] theorem ws_zX2_ne_lKb : zX2 ≠ lKb := by decide
@[simp] theorem ws_lKb_ne_zX2 : lKb ≠ zX2 := by decide
@[simp] theorem ws_zX2_ne_pFu : zX2 ≠ pFu := by decide
@[simp] theorem ws_pFu_ne_zX2 : pFu ≠ zX2 := by decide
@[simp] theorem ws_zX2_ne_pH : zX2 ≠ pH := by decide
@[simp] theorem ws_pH_ne_zX2 : pH ≠ zX2 := by decide
@[simp] theorem ws_sN_ne_zN2 : sN ≠ zN2 := by decide
@[simp] theorem ws_sN_ne_zP2 : sN ≠ zP2 := by decide
@[simp] theorem ws_sN_ne_zI2 : sN ≠ zI2 := by decide
@[simp] theorem ws_sN_ne_zV2 : sN ≠ zV2 := by decide
@[simp] theorem ws_sN_ne_zB2 : sN ≠ zB2 := by decide
@[simp] theorem ws_sN_ne_zX2 : sN ≠ zX2 := by decide
@[simp] theorem ws_sN_ne_sI : sN ≠ sI := by decide
@[simp] theorem ws_sN_ne_sP : sN ≠ sP := by decide
@[simp] theorem ws_sN_ne_lFl : sN ≠ lFl := by decide
@[simp] theorem ws_lFl_ne_sN : lFl ≠ sN := by decide
@[simp] theorem ws_sN_ne_lDh : sN ≠ lDh := by decide
@[simp] theorem ws_lDh_ne_sN : lDh ≠ sN := by decide
@[simp] theorem ws_sN_ne_lDt : sN ≠ lDt := by decide
@[simp] theorem ws_lDt_ne_sN : lDt ≠ sN := by decide
@[simp] theorem ws_sN_ne_lDg : sN ≠ lDg := by decide
@[simp] theorem ws_lDg_ne_sN : lDg ≠ sN := by decide
@[simp] theorem ws_sN_ne_lDi : sN ≠ lDi := by decide
@[simp] theorem ws_lDi_ne_sN : lDi ≠ sN := by decide
@[simp] theorem ws_sN_ne_lRp : sN ≠ lRp := by decide
@[simp] theorem ws_lRp_ne_sN : lRp ≠ sN := by decide
@[simp] theorem ws_sN_ne_lRn : sN ≠ lRn := by decide
@[simp] theorem ws_lRn_ne_sN : lRn ≠ sN := by decide
@[simp] theorem ws_sN_ne_kFu : sN ≠ kFu := by decide
@[simp] theorem ws_kFu_ne_sN : kFu ≠ sN := by decide
@[simp] theorem ws_sN_ne_kC : sN ≠ kC := by decide
@[simp] theorem ws_kC_ne_sN : kC ≠ sN := by decide
@[simp] theorem ws_sN_ne_kD : sN ≠ kD := by decide
@[simp] theorem ws_kD_ne_sN : kD ≠ sN := by decide
@[simp] theorem ws_sN_ne_sH : sN ≠ sH := by decide
@[simp] theorem ws_sH_ne_sN : sH ≠ sN := by decide
@[simp] theorem ws_sN_ne_sE : sN ≠ sE := by decide
@[simp] theorem ws_sE_ne_sN : sE ≠ sN := by decide
@[simp] theorem ws_sN_ne_lFle : sN ≠ lFle := by decide
@[simp] theorem ws_lFle_ne_sN : lFle ≠ sN := by decide
@[simp] theorem ws_sN_ne_lDir : sN ≠ lDir := by decide
@[simp] theorem ws_lDir_ne_sN : lDir ≠ sN := by decide
@[simp] theorem ws_sN_ne_lKb : sN ≠ lKb := by decide
@[simp] theorem ws_lKb_ne_sN : lKb ≠ sN := by decide
@[simp] theorem ws_sN_ne_pFu : sN ≠ pFu := by decide
@[simp] theorem ws_pFu_ne_sN : pFu ≠ sN := by decide
@[simp] theorem ws_sN_ne_pH : sN ≠ pH := by decide
@[simp] theorem ws_pH_ne_sN : pH ≠ sN := by decide
@[simp] theorem ws_sI_ne_zN2 : sI ≠ zN2 := by decide
@[simp] theorem ws_sI_ne_zP2 : sI ≠ zP2 := by decide
@[simp] theorem ws_sI_ne_zI2 : sI ≠ zI2 := by decide
@[simp] theorem ws_sI_ne_zV2 : sI ≠ zV2 := by decide
@[simp] theorem ws_sI_ne_zB2 : sI ≠ zB2 := by decide
@[simp] theorem ws_sI_ne_zX2 : sI ≠ zX2 := by decide
@[simp] theorem ws_sI_ne_sN : sI ≠ sN := by decide
@[simp] theorem ws_sI_ne_sP : sI ≠ sP := by decide
@[simp] theorem ws_sI_ne_lFl : sI ≠ lFl := by decide
@[simp] theorem ws_lFl_ne_sI : lFl ≠ sI := by decide
@[simp] theorem ws_sI_ne_lDh : sI ≠ lDh := by decide
@[simp] theorem ws_lDh_ne_sI : lDh ≠ sI := by decide
@[simp] theorem ws_sI_ne_lDt : sI ≠ lDt := by decide
@[simp] theorem ws_lDt_ne_sI : lDt ≠ sI := by decide
@[simp] theorem ws_sI_ne_lDg : sI ≠ lDg := by decide
@[simp] theorem ws_lDg_ne_sI : lDg ≠ sI := by decide
@[simp] theorem ws_sI_ne_lDi : sI ≠ lDi := by decide
@[simp] theorem ws_lDi_ne_sI : lDi ≠ sI := by decide
@[simp] theorem ws_sI_ne_lRp : sI ≠ lRp := by decide
@[simp] theorem ws_lRp_ne_sI : lRp ≠ sI := by decide
@[simp] theorem ws_sI_ne_lRn : sI ≠ lRn := by decide
@[simp] theorem ws_lRn_ne_sI : lRn ≠ sI := by decide
@[simp] theorem ws_sI_ne_kFu : sI ≠ kFu := by decide
@[simp] theorem ws_kFu_ne_sI : kFu ≠ sI := by decide
@[simp] theorem ws_sI_ne_kC : sI ≠ kC := by decide
@[simp] theorem ws_kC_ne_sI : kC ≠ sI := by decide
@[simp] theorem ws_sI_ne_kD : sI ≠ kD := by decide
@[simp] theorem ws_kD_ne_sI : kD ≠ sI := by decide
@[simp] theorem ws_sI_ne_sH : sI ≠ sH := by decide
@[simp] theorem ws_sH_ne_sI : sH ≠ sI := by decide
@[simp] theorem ws_sI_ne_sE : sI ≠ sE := by decide
@[simp] theorem ws_sE_ne_sI : sE ≠ sI := by decide
@[simp] theorem ws_sI_ne_lFle : sI ≠ lFle := by decide
@[simp] theorem ws_lFle_ne_sI : lFle ≠ sI := by decide
@[simp] theorem ws_sI_ne_lDir : sI ≠ lDir := by decide
@[simp] theorem ws_lDir_ne_sI : lDir ≠ sI := by decide
@[simp] theorem ws_sI_ne_lKb : sI ≠ lKb := by decide
@[simp] theorem ws_lKb_ne_sI : lKb ≠ sI := by decide
@[simp] theorem ws_sI_ne_pFu : sI ≠ pFu := by decide
@[simp] theorem ws_pFu_ne_sI : pFu ≠ sI := by decide
@[simp] theorem ws_sI_ne_pH : sI ≠ pH := by decide
@[simp] theorem ws_pH_ne_sI : pH ≠ sI := by decide
@[simp] theorem ws_sP_ne_zN2 : sP ≠ zN2 := by decide
@[simp] theorem ws_sP_ne_zP2 : sP ≠ zP2 := by decide
@[simp] theorem ws_sP_ne_zI2 : sP ≠ zI2 := by decide
@[simp] theorem ws_sP_ne_zV2 : sP ≠ zV2 := by decide
@[simp] theorem ws_sP_ne_zB2 : sP ≠ zB2 := by decide
@[simp] theorem ws_sP_ne_zX2 : sP ≠ zX2 := by decide
@[simp] theorem ws_sP_ne_sN : sP ≠ sN := by decide
@[simp] theorem ws_sP_ne_sI : sP ≠ sI := by decide
@[simp] theorem ws_sP_ne_lFl : sP ≠ lFl := by decide
@[simp] theorem ws_lFl_ne_sP : lFl ≠ sP := by decide
@[simp] theorem ws_sP_ne_lDh : sP ≠ lDh := by decide
@[simp] theorem ws_lDh_ne_sP : lDh ≠ sP := by decide
@[simp] theorem ws_sP_ne_lDt : sP ≠ lDt := by decide
@[simp] theorem ws_lDt_ne_sP : lDt ≠ sP := by decide
@[simp] theorem ws_sP_ne_lDg : sP ≠ lDg := by decide
@[simp] theorem ws_lDg_ne_sP : lDg ≠ sP := by decide
@[simp] theorem ws_sP_ne_lDi : sP ≠ lDi := by decide
@[simp] theorem ws_lDi_ne_sP : lDi ≠ sP := by decide
@[simp] theorem ws_sP_ne_lRp : sP ≠ lRp := by decide
@[simp] theorem ws_lRp_ne_sP : lRp ≠ sP := by decide
@[simp] theorem ws_sP_ne_lRn : sP ≠ lRn := by decide
@[simp] theorem ws_lRn_ne_sP : lRn ≠ sP := by decide
@[simp] theorem ws_sP_ne_kFu : sP ≠ kFu := by decide
@[simp] theorem ws_kFu_ne_sP : kFu ≠ sP := by decide
@[simp] theorem ws_sP_ne_kC : sP ≠ kC := by decide
@[simp] theorem ws_kC_ne_sP : kC ≠ sP := by decide
@[simp] theorem ws_sP_ne_kD : sP ≠ kD := by decide
@[simp] theorem ws_kD_ne_sP : kD ≠ sP := by decide
@[simp] theorem ws_sP_ne_sH : sP ≠ sH := by decide
@[simp] theorem ws_sH_ne_sP : sH ≠ sP := by decide
@[simp] theorem ws_sP_ne_sE : sP ≠ sE := by decide
@[simp] theorem ws_sE_ne_sP : sE ≠ sP := by decide
@[simp] theorem ws_sP_ne_lFle : sP ≠ lFle := by decide
@[simp] theorem ws_lFle_ne_sP : lFle ≠ sP := by decide
@[simp] theorem ws_sP_ne_lDir : sP ≠ lDir := by decide
@[simp] theorem ws_lDir_ne_sP : lDir ≠ sP := by decide
@[simp] theorem ws_sP_ne_lKb : sP ≠ lKb := by decide
@[simp] theorem ws_lKb_ne_sP : lKb ≠ sP := by decide
@[simp] theorem ws_sP_ne_pFu : sP ≠ pFu := by decide
@[simp] theorem ws_pFu_ne_sP : pFu ≠ sP := by decide
@[simp] theorem ws_sP_ne_pH : sP ≠ pH := by decide
@[simp] theorem ws_pH_ne_sP : pH ≠ sP := by decide

def stParams : List MlS := [kFu, kD, sH, sE]
def apParams : List MlS := [kFu, kC, kD, sE]
def prParams : List MlS := [kFu, kC, kD, sE, sN, sI, sP]
def wcsLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, zN2, zP2, zI2, zV2, zB2, zX2]

def prCall : ProgHOL 64 :=
  .seq (.call (some (some (.local, zX2), none)) fStepProj [vv kFu, vv kC, vv kD, vv sE, vv zN2, vv zI2, vv zP2])
    (.return (vv zX2))

def wcsCore : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv sE)) (.seq eViewP
  (.ite (.cmp .equal (vv lDg) (.const 4))
    (.ite (stuckHeadE sH)
      (.seq (.call (some (some (.local, zX2), none)) fStuck [vv kFu, vv kD, vv sH, vv sE]) (.return (vv zX2)))
      (.seq (.call (some (some (.local, zX2), none)) fStepApp [vv kFu, vv kC, vv kD, vv sE]) (.return (vv zX2))))
  (.ite (.cmp .equal (vv lDg) (.const 9))
    (.seq (.assign .local zN2 (.load .one (vv lRp)))
    (.seq (.assign .local zP2 (.load .one (.op .add [vv lRp, .const 8])))
    (.ite (.cmp .equal (vv lRn) (.const 2)) (.seq (.assign .local zI2 (.const 0)) prCall)
      (.ite (.cmp .equal (vv lRn) (.const 3))
        (.seq (.assign .local zI2 (.load .one (.op .add [vv lRp, .const 16]))) prCall) hang))))
  (.ite (.cmp .equal (vv lDg) (.const 7))
    (.seq (.assign .local zV2 (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.assign .local zB2 (.load .one (.op .add [vv lRp, .const 16])))
    (.seq (.call (some (some (.local, zX2), none)) ExI.fInst1F
      [.const (BitVec.ofNat 64 coreWalkFuel), vv zB2, vv zV2, .const 0])
      (.return (.op .add [.shift .lsl (vv zX2) (.const 1), .const 1])))))
  (.ite (.cmp .equal (vv lDg) (.const 0)) hang
    (.return (.shift .lsl (vv sE) (.const 1)))))))))

def wcsBody : ProgHOL 64 := prologue wcsLocals wcsCore

end ConPanqueque.T.WC
