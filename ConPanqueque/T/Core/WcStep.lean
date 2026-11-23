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

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

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

theorem postWS_locals {σ : Type} (C : Ctx) : ∀ (a : WhnfStep) w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostWS C a w s' st → PostWS C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', h1, h2, h3⟩ => ⟨H', h1, h2, sr_of_eq h3 rfl rfl rfl rfl⟩

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


section
variable {σ : Type}

theorem wcs_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ wcsLocals → (ctxEnv C ++ wcsParams.zip vals).get x = none :=
  Knot.params_none C wcsLocals wcsParams vals (by decide) (by decide)

/-- Calling a step function (its post `PostWS`). -/
theorem specR_callWS {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {m : AM WhnfStep}
    (x f : MlS) (ps : List MlS) (es : List (ExpHOL 64)) (Bd : ProgHOL 64) (vs : List (BitVec 64))
    (hnd : ps.Nodup) (hl : vs.length = ps.length) (hx : x ∈ D)
    (hC : C.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), Bd, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs)
    (hspec : SpecR (σ := σ) (Pre C s (ps.zip vs)) Bd s m (PostWS C)) :
    SpecR (σ := σ) (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f es) (.return (vv x))) s m (PostWS C) := by
  refine specR_congr (m' := m >>= fun st => pure st) (by simp) ?_
  refine specR_callNIH x f ps es Bd vs hnd hl hx hC hes (PostWS C) (fun st w _ _ => w = encWS st)
    (fun st w s' t' ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ps vs hl hlk) hspec)
    (fun st w s' H' hp hw => ?_)
  subst hw
  exact specR_returnI _ (encWS st) (by simp) (fun t ht => ⟨H', hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem wcs_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (Bst Bap Bpr : ProgHOL 64)
    (hcst : C.code.lookup fStuck = some (stParams.map (fun p => (p, ShapeHOL.one)), Bst, .one))
    (hcap : C.code.lookup fStepApp = some (apParams.map (fun p => (p, ShapeHOL.one)), Bap, .one))
    (hcpr : C.code.lookup fStepProj = some (prParams.map (fun p => (p, ShapeHOL.one)), Bpr, .one))
    (hcI : C.code.lookup ExI.fInst1F = some ([pFu, pH, ExI.pV, ExI.pD].map (fun p => (p, ShapeHOL.one)),
      ExI.fastBody C, .one))
    (hcI' : ExI.Codes C (ExI.body C))
    (s : AState) (cheap : Bool) (d : Nat) (h e : EIdx)
    (hSt : SpecR (σ := σ) (Pre C s (stParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW h, Enc.idxW e])) Bst s
      (whnfStuck mode (knot mode C n) C.fe d h e) (PostWS C))
    (hAp : SpecR (σ := σ) (Pre C s (apParams.zip [BitVec.ofNat 64 n, boolW cheap, BitVec.ofNat 64 d, Enc.idxW e])) Bap s
      (whnfCoreStepApp mode (knot mode C n) C.fe cheap d e) (PostWS C))
    (hPr : ∀ sn i pe, i < 2 ^ 64 → SpecR (σ := σ) (Pre C s (prParams.zip [BitVec.ofNat 64 n, boolW cheap,
      BitVec.ofNat 64 d, Enc.idxW e, Enc.idxW sn, BitVec.ofNat 64 i, Enc.idxW pe])) Bpr s
      (whnfCoreStepProj mode (knot mode C n) C.fe cheap d e sn i pe) (PostWS C)) :
    SpecR (σ := σ) (Pre C s (wcsParams.zip [BitVec.ofNat 64 n, boolW cheap, BitVec.ofNat 64 d, Enc.idxW h,
      Enc.idxW e])) wcsBody s (whnfCoreStep mode (knot mode C n) C.fe cheap d h e) (PostWS C) := by
  refine specR_prologue (postWS_locals C) (wcs_none C _) ?_
  unfold wcsCore
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv sE) (Enc.idxW e) (by decide) (by simp +decide [Env.get, wcsParams, ctxEnv]) ?_
  refine ILP.specR_viewIv e (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
    (fun v P hv htn hl => ?_)
  have hret0 : ∀ {Γ' : Env} {M' : Mem}, Γ'.get sE = some (Enc.idxW e) →
      SpecR (σ := σ) (Inv C s Γ' M' (ctxLocals ++ wcsLocals)) (.return (.shift .lsl (vv sE) (.const 1))) s
        (pure (.done e)) (PostWS C) := fun hE =>
    specR_returnI _ (encWS (.done e)) (by simp [sev, vv, hE, encWS]) (fun t ht =>
      ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  cases v with
  | app f a =>
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    show SpecR _ _ s (if isStuckHead h then whnfStuck mode (knot mode C n) C.fe d h e
      else whnfCoreStepApp mode (knot mode C n) C.fe cheap d e) _
    have hsh := sev_stuckHead ((lRp, P) :: (lRn, BitVec.ofNat 64 (encEView (.app f a)).length) ::
      (lDt, BitVec.ofNat 64 e.tier.toNat) :: (lDg, BitVec.ofNat 64 (ENodeView.app f a).tagN) ::
      (lDi, BitVec.ofNat 64 e.idxNat) :: (lDh, Enc.idxW e) :: (lFl, C.FLe) ::
      (ctxEnv C ++ wcsParams.zip [BitVec.ofNat 64 n, boolW cheap, BitVec.ofNat 64 d, Enc.idxW h, Enc.idxW e])) sH h
      (by simp +decide [Env.get, wcsParams, ctxEnv])
    by_cases hstk : isStuckHead h = true
    · rw [if_pos hstk]
      refine specR_ifI _ 1 (by rw [hsh, hstk]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
      refine Big.specR_dropM ?_
      exact specR_callWS zX2 fStuck stParams [vv kFu, vv kD, vv sH, vv sE] Bst
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW h, Enc.idxW e] (by decide) rfl (by decide) hcst
        ⟨by simp +decide [Env.get, wcsParams, ctxEnv], by simp +decide [Env.get, wcsParams, ctxEnv],
          by simp +decide [Env.get, wcsParams, ctxEnv], by simp +decide [Env.get, wcsParams, ctxEnv], trivial⟩ hSt
    · rw [if_neg hstk]
      refine specR_ifI _ 0 (by rw [hsh]; simp [hstk, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
      refine Big.specR_dropM ?_
      exact specR_callWS zX2 fStepApp apParams [vv kFu, vv kC, vv kD, vv sE] Bap
        [BitVec.ofNat 64 n, boolW cheap, BitVec.ofNat 64 d, Enc.idxW e] (by decide) rfl (by decide) hcap
        ⟨by simp +decide [Env.get, wcsParams, ctxEnv], by simp +decide [Env.get, wcsParams, ctxEnv],
          by simp +decide [Env.get, wcsParams, ctxEnv], by simp +decide [Env.get, wcsParams, ctxEnv], trivial⟩ hAp
  | proj sn i pe =>
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    show SpecR _ _ s (whnfCoreStepProj mode (knot mode C n) C.fe cheap d e sn i pe) _
    have er : encEView (.proj sn i pe) = Enc.idxW sn :: Enc.idxW pe :: limbs i := rfl
    refine specR_loadI' zN2 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW sn) (by decide) (by simp) (by simp)
      (by simpa [er] using wordsAt_mem0 P (Enc.idxW sn) (Enc.idxW pe :: limbs i) []) ?_
    refine specR_loadI' zP2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW pe) (by decide) (by simp +decide [sev]) rfl
      (by simpa [er] using wordsAt_mem1 P (Enc.idxW sn) (Enc.idxW pe) (limbs i) []) ?_
    have hlen : (encEView (.proj sn i pe)).length = (limbs i).length + 2 := by rw [er]; simp
    have hl58 : (limbs i).length + 2 < 2 ^ 61 := by rw [← hlen]; exact hl
    rcases (by omega : (limbs i).length = 0 ∨ (limbs i).length = 1 ∨ 2 ≤ (limbs i).length) with h0 | h1 | h2
    · have hi0 : i = 0 := by have := (limbs_length_lt_iff i 0).mp (by omega); simpa using this
      subst hi0
      refine specR_ifI _ 1 (by simp [sev, hlen, h0, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      refine specR_assignI zI2 (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
      refine Big.specR_dropM ?_
      exact specR_callWS zX2 fStepProj prParams [vv kFu, vv kC, vv kD, vv sE, vv zN2, vv zI2, vv zP2] Bpr
        [BitVec.ofNat 64 n, boolW cheap, BitVec.ofNat 64 d, Enc.idxW e, Enc.idxW sn, BitVec.ofNat 64 0, Enc.idxW pe]
        (by decide) rfl (by decide) hcpr
        ⟨by simp +decide [Env.get, wcsParams, ctxEnv], by simp +decide [Env.get, wcsParams, ctxEnv],
          by simp +decide [Env.get, wcsParams, ctxEnv], by simp +decide [Env.get, wcsParams, ctxEnv],
          by simp, by simp, by simp, trivial⟩ (hPr sn 0 pe (by decide))
    · have hiB : i < B := by have := (limbs_length_lt_iff i 1).mp (by omega); simpa using this
      have h2w : BitVec.ofNat 64 ((limbs i).length + 2) ≠ 2#64 := by
        rw [h1]; decide
      refine specR_ifI _ 0 (by simp [sev, hlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact h2w)
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp [sev, hlen, h1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      have hx2 : (Enc.idxW sn :: Enc.idxW pe :: limbs i)[2]'(by simp; omega) = BitVec.ofNat 64 i := by
        show (limbs i)[0]'(by omega) = _
        rw [limbs_getElem i 0 (by omega)]; simp [Nat.mod_eq_of_lt hiB]
      refine specR_loadI' zI2 _ (P + 16) (P + BitVec.ofNat 64 (8 * 2)) (BitVec.ofNat 64 i) (by decide)
        (by simp +decide [sev]) rfl (by
          have := wordsAt_get P (Enc.idxW sn :: Enc.idxW pe :: limbs i) 2 (by simp; omega) []
          rw [hx2] at this; simpa [er] using this) ?_
      refine Big.specR_dropM ?_
      exact specR_callWS zX2 fStepProj prParams [vv kFu, vv kC, vv kD, vv sE, vv zN2, vv zI2, vv zP2] Bpr
        [BitVec.ofNat 64 n, boolW cheap, BitVec.ofNat 64 d, Enc.idxW e, Enc.idxW sn, BitVec.ofNat 64 i, Enc.idxW pe]
        (by decide) rfl (by decide) hcpr
        ⟨by simp +decide [Env.get, wcsParams, ctxEnv], by simp +decide [Env.get, wcsParams, ctxEnv],
          by simp +decide [Env.get, wcsParams, ctxEnv], by simp +decide [Env.get, wcsParams, ctxEnv],
          by simp, by simp, by simp, trivial⟩ (hPr sn i pe hiB)
    · have h2w : BitVec.ofNat 64 ((limbs i).length + 2) ≠ 2#64 := by
        intro h0; have := congrArg BitVec.toNat h0; simp at this; omega
      have h3w : BitVec.ofNat 64 ((limbs i).length + 2) ≠ 3#64 := by
        intro h0; have := congrArg BitVec.toNat h0; simp at this; omega
      refine specR_ifI _ 0 (by simp [sev, hlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact h2w)
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp [sev, hlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact h3w)
        (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_hangI
  | letE ty v b =>
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    show SpecR _ _ s (instantiate1Fast coreWalkFuel b v 0 >>= fun e' => pure (WhnfStep.cont e')) _
    have er : encEView (.letE ty v b) = [Enc.idxW ty, Enc.idxW v, Enc.idxW b] := rfl
    refine specR_loadI' zV2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW v) (by decide) (by simp +decide [sev]) rfl
      (by simpa [er] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW v) [Enc.idxW b] []) ?_
    refine specR_loadI' zB2 _ (P + 16) (P + BitVec.ofNat 64 (8 * 2)) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [er] using wordsAt_get P [Enc.idxW ty, Enc.idxW v, Enc.idxW b] 2 (by simp) []) ?_
    refine Big.specR_dropM ?_
    refine ILP.callE_spec zX2 ExI.fInst1F [pFu, pH, ExI.pV, ExI.pD]
      [.const (BitVec.ofNat 64 coreWalkFuel), vv zB2, vv zV2, .const 0] (ExI.fastBody C)
      [BitVec.ofNat 64 coreWalkFuel, Enc.idxW b, Enc.idxW v, BitVec.ofNat 64 0] (by decide) rfl (by decide) hcI
      ⟨rfl, by simp, by simp, rfl, trivial⟩
      (ExI.fast_spec ra C hok hcI' s coreWalkFuel b v 0 CV.coreWalkFuel_lt (by decide)) (fun e' s' => ?_)
    exact specR_returnI _ (encWS (.cont e')) (by simp [sev, vv, encWS]) (fun t ht =>
      ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | bvar i =>
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact specR_hangI
  | sort u =>
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact hret0 (by simp +decide [Env.get, wcsParams, ctxEnv])
  | fvar idx ty =>
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact hret0 (by simp +decide [Env.get, wcsParams, ctxEnv])
  | forallE ty b =>
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact hret0 (by simp +decide [Env.get, wcsParams, ctxEnv])
  | lam ty b =>
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact hret0 (by simp +decide [Env.get, wcsParams, ctxEnv])
  | const c us =>
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact hret0 (by simp +decide [Env.get, wcsParams, ctxEnv])
  | lit l =>
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact hret0 (by simp +decide [Env.get, wcsParams, ctxEnv])


end


def fRPC := ofString "reduceProjCore"
def rpcParams : List MlS := [kFu, kD, sN, sI, sP]
def wprLocals : List MlS := [zX2, zN2]

def wprRest : ProgHOL 64 :=
  .seq (.call (some (some (.local, zN2), none)) fRPC [vv kFu, vv kD, vv sN, vv sI, vv zX2])
  (.ite (.cmp .notEqual (vv zN2) (.const 0))
    (.return (.op .add [.shift .lsl (.op .sub [vv zN2, .const 1]) (.const 1), .const 1]))
    (.return (.shift .lsl (vv sE) (.const 1))))

def wprBody : ProgHOL 64 :=
  prologue wprLocals (.ite (vv kC)
    (.seq (.call (some (some (.local, zX2), none)) fWC [vv kFu, .const 1, vv kD, vv sP]) wprRest)
    (.seq (.call (some (some (.local, zX2), none)) fW [vv kFu, vv kD, vv sP]) wprRest))

section
variable {σ : Type}

theorem wpr_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ wprLocals → (ctxEnv C ++ prParams.zip vals).get x = none :=
  Knot.params_none C wprLocals prParams vals (by decide) (by decide)

theorem wpr_rest (mode : ConLeche.CheckMode) (n : Nat) {C : Ctx} (Brpc : ProgHOL 64)
    (hcr : C.code.lookup fRPC = some (rpcParams.map (fun p => (p, ShapeHOL.one)), Brpc, .one))
    {H : List (BitVec 64)} {s1 : AState} {Γ : Env} {D : List MlS} (hpre : C.H <+: H) (d : Nat) (e c : EIdx)
    (sn : NIdx) (i : Nat)
    (hRPC : SpecR (σ := σ) (Pre (ctxH C H) s1 (rpcParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW sn,
      BitVec.ofNat 64 i, Enc.idxW c])) Brpc s1 (reduceProjCore mode (knot mode C n) C.fe d sn i c) (UD.PostO (ctxH C H)))
    (hFu : Γ.get kFu = some (BitVec.ofNat 64 n)) (hD0 : Γ.get kD = some (BitVec.ofNat 64 d))
    (hN : Γ.get sN = some (Enc.idxW sn)) (hI : Γ.get sI = some (BitVec.ofNat 64 i))
    (hX : Γ.get zX2 = some (Enc.idxW c)) (hE : Γ.get sE = some (Enc.idxW e)) (hDN : zN2 ∈ D) :
    SpecR (σ := σ) (Inv (ctxH C H) s1 Γ [] D) wprRest s1
      (reduceProjCore mode (knot mode C n) C.fe d sn i c >>= fun o => match o with
        | some m' => pure (WhnfStep.cont m')
        | none => pure (WhnfStep.done e)) (PostWS C) := by
  unfold wprRest
  refine specR_callNIH (C := ctxH C H) zN2 fRPC rpcParams [vv kFu, vv kD, vv sN, vv sI, vv zX2] Brpc
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW sn, BitVec.ofNat 64 i, Enc.idxW c] (by decide) rfl hDN hcr
    ⟨by simp [hFu], by simp [hD0], by simp [hN], by simp [hI], by simp [hX], trivial⟩ (UD.PostO (ctxH C H))
    (fun o w _ _ => w = optW o) (fun o w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rpcParams _ rfl hlk) hRPC)
    (fun o w s2 H2 hp2 hw => ?_)
  subst hw
  rcases o with _ | m'
  · refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    exact specR_returnI _ (encWS (.done e)) (by simp [sev, vv, hE, encWS]) (fun t ht =>
      ⟨H2, hpre.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · have hne : optW (some m') ≠ 0 := WB.idxW_succ_ne m'
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact specR_returnI _ (encWS (.cont m')) (by simp [sev, optWG, encWS, BitVec.add_sub_cancel])
      (fun t ht => ⟨H2, hpre.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem wpr_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) (Brpc : ProgHOL 64)
    (hcr : C.code.lookup fRPC = some (rpcParams.map (fun p => (p, ShapeHOL.one)), Brpc, .one))
    (hcwc : C.code.lookup fWC = some (pmap wcParams, wcE, .one))
    (hcw : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one))
    (s : AState) (cheap : Bool) (d : Nat) (e pe : EIdx) (sn : NIdx) (i : Nat)
    (hWC : Callee (σ := σ) C wcParams [BitVec.ofNat 64 n, boolW true, BitVec.ofNat 64 d, Enc.idxW pe] wcE s
      ((knot mode C n).whnfCore true d pe) (PostK C))
    (hW : Callee (σ := σ) C kParams [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW pe] (whnfE C fWB) s
      ((knot mode C n).whnf d pe) (PostK C))
    (hRPC : ∀ (H : List (BitVec 64)) s1 c, C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s1 (rpcParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW sn,
        BitVec.ofNat 64 i, Enc.idxW c])) Brpc s1 (reduceProjCore mode (knot mode C n) C.fe d sn i c)
        (UD.PostO (ctxH C H))) :
    SpecR (σ := σ) (Pre C s (prParams.zip [BitVec.ofNat 64 n, boolW cheap, BitVec.ofNat 64 d, Enc.idxW e, Enc.idxW sn,
      BitVec.ofNat 64 i, Enc.idxW pe])) wprBody s
      (whnfCoreStepProj mode (knot mode C n) C.fe cheap d e sn i pe) (PostWS C) := by
  refine specR_prologue (postWS_locals C) (wpr_none C _) ?_
  unfold whnfCoreStepProj
  cases cheap
  · refine specR_ifI _ 0 (by simp +decide [sev, Env.get, prParams, ctxEnv, boolW]) (fun h => absurd rfl h)
      (fun _ => ?_)
    simp only [Bool.false_eq_true, ite_false]
    refine Big.specR_callKC zX2 fW kParams [vv kFu, vv kD, vv sP] (whnfE C fWB)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW pe] (by decide) rfl (by decide) hcw
      ⟨by simp +decide [Env.get, prParams, ctxEnv], by simp +decide [Env.get, prParams, ctxEnv],
        by simp +decide [Env.get, prParams, ctxEnv], trivial⟩ hW (fun c s1 H1 hp1 _ => ?_)
    exact wpr_rest mode n Brpc hcr hp1 d e c sn i (hRPC H1 s1 c hp1)
      (by simp +decide [Env.get, prParams, ctxEnv]) (by simp +decide [Env.get, prParams, ctxEnv])
      (by simp +decide [Env.get, prParams, ctxEnv]) (by simp +decide [Env.get, prParams, ctxEnv]) (by simp)
      (by simp +decide [Env.get, prParams, ctxEnv]) (by decide)
  · refine specR_ifI _ 1 (by simp +decide [sev, Env.get, prParams, ctxEnv, boolW]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    simp only [ite_true]
    refine Big.specR_callKC zX2 fWC wcParams [vv kFu, .const 1, vv kD, vv sP] wcE
      [BitVec.ofNat 64 n, boolW true, BitVec.ofNat 64 d, Enc.idxW pe] (by decide) rfl (by decide) hcwc
      ⟨by simp +decide [Env.get, prParams, ctxEnv], rfl, by simp +decide [Env.get, prParams, ctxEnv],
        by simp +decide [Env.get, prParams, ctxEnv], trivial⟩ hWC (fun c s1 H1 hp1 _ => ?_)
    exact wpr_rest mode n Brpc hcr hp1 d e c sn i (hRPC H1 s1 c hp1)
      (by simp +decide [Env.get, prParams, ctxEnv]) (by simp +decide [Env.get, prParams, ctxEnv])
      (by simp +decide [Env.get, prParams, ctxEnv]) (by simp +decide [Env.get, prParams, ctxEnv]) (by simp)
      (by simp +decide [Env.get, prParams, ctxEnv]) (by decide)

end

end ConPanqueque.T.WC
