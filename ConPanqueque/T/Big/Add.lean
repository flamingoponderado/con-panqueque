import ConPanqueque.T.Big.Cmp
import ConPanqueque.T.Big.AddMath
import ConPanqueque.T.Core.ConstVal
import ConPanqueque.T.Big.LitCopy
import ConPanqueque.T.Core.Unfold
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Adding two `Nat` literals

`addCore(x, y)` (the longer first) writes the digits of `x + y` into a fresh heap block: a carry loop over
the shared limbs, one over the rest of `x` (with a zero limb for `y`), the final carry, the length.
-/

namespace ConPanqueque.T.Big

open ConPanqueque.T ConPanqueque.T.Ex
open ConPanqueque.V.Enc

def aX := ofString "ax"
def aY := ofString "ay"
def aPa := ofString "apa"
def aLa := ofString "ala"
def aLb := ofString "alb"
def aO := ofString "ao"
def aQa := ofString "aqa"
def aQb := ofString "aqb"
def aQo := ofString "aqo"
def aU := ofString "au"
def aV := ofString "av"
def aS1 := ofString "as1"
def aS := ofString "as"
def aC := ofString "ac"
def aI := ofString "ai"

@[simp] theorem aX_ne_aY : aX ≠ aY := by decide
@[simp] theorem aX_ne_aPa : aX ≠ aPa := by decide
@[simp] theorem aX_ne_aLa : aX ≠ aLa := by decide
@[simp] theorem aX_ne_aLb : aX ≠ aLb := by decide
@[simp] theorem aX_ne_aO : aX ≠ aO := by decide
@[simp] theorem aX_ne_aQa : aX ≠ aQa := by decide
@[simp] theorem aX_ne_aQb : aX ≠ aQb := by decide
@[simp] theorem aX_ne_aQo : aX ≠ aQo := by decide
@[simp] theorem aX_ne_aU : aX ≠ aU := by decide
@[simp] theorem aX_ne_aV : aX ≠ aV := by decide
@[simp] theorem aX_ne_aS1 : aX ≠ aS1 := by decide
@[simp] theorem aX_ne_aS : aX ≠ aS := by decide
@[simp] theorem aX_ne_aC : aX ≠ aC := by decide
@[simp] theorem aX_ne_aI : aX ≠ aI := by decide
@[simp] theorem aY_ne_aX : aY ≠ aX := by decide
@[simp] theorem aY_ne_aPa : aY ≠ aPa := by decide
@[simp] theorem aY_ne_aLa : aY ≠ aLa := by decide
@[simp] theorem aY_ne_aLb : aY ≠ aLb := by decide
@[simp] theorem aY_ne_aO : aY ≠ aO := by decide
@[simp] theorem aY_ne_aQa : aY ≠ aQa := by decide
@[simp] theorem aY_ne_aQb : aY ≠ aQb := by decide
@[simp] theorem aY_ne_aQo : aY ≠ aQo := by decide
@[simp] theorem aY_ne_aU : aY ≠ aU := by decide
@[simp] theorem aY_ne_aV : aY ≠ aV := by decide
@[simp] theorem aY_ne_aS1 : aY ≠ aS1 := by decide
@[simp] theorem aY_ne_aS : aY ≠ aS := by decide
@[simp] theorem aY_ne_aC : aY ≠ aC := by decide
@[simp] theorem aY_ne_aI : aY ≠ aI := by decide
@[simp] theorem aPa_ne_aX : aPa ≠ aX := by decide
@[simp] theorem aPa_ne_aY : aPa ≠ aY := by decide
@[simp] theorem aPa_ne_aLa : aPa ≠ aLa := by decide
@[simp] theorem aPa_ne_aLb : aPa ≠ aLb := by decide
@[simp] theorem aPa_ne_aO : aPa ≠ aO := by decide
@[simp] theorem aPa_ne_aQa : aPa ≠ aQa := by decide
@[simp] theorem aPa_ne_aQb : aPa ≠ aQb := by decide
@[simp] theorem aPa_ne_aQo : aPa ≠ aQo := by decide
@[simp] theorem aPa_ne_aU : aPa ≠ aU := by decide
@[simp] theorem aPa_ne_aV : aPa ≠ aV := by decide
@[simp] theorem aPa_ne_aS1 : aPa ≠ aS1 := by decide
@[simp] theorem aPa_ne_aS : aPa ≠ aS := by decide
@[simp] theorem aPa_ne_aC : aPa ≠ aC := by decide
@[simp] theorem aPa_ne_aI : aPa ≠ aI := by decide
@[simp] theorem aLa_ne_aX : aLa ≠ aX := by decide
@[simp] theorem aLa_ne_aY : aLa ≠ aY := by decide
@[simp] theorem aLa_ne_aPa : aLa ≠ aPa := by decide
@[simp] theorem aLa_ne_aLb : aLa ≠ aLb := by decide
@[simp] theorem aLa_ne_aO : aLa ≠ aO := by decide
@[simp] theorem aLa_ne_aQa : aLa ≠ aQa := by decide
@[simp] theorem aLa_ne_aQb : aLa ≠ aQb := by decide
@[simp] theorem aLa_ne_aQo : aLa ≠ aQo := by decide
@[simp] theorem aLa_ne_aU : aLa ≠ aU := by decide
@[simp] theorem aLa_ne_aV : aLa ≠ aV := by decide
@[simp] theorem aLa_ne_aS1 : aLa ≠ aS1 := by decide
@[simp] theorem aLa_ne_aS : aLa ≠ aS := by decide
@[simp] theorem aLa_ne_aC : aLa ≠ aC := by decide
@[simp] theorem aLa_ne_aI : aLa ≠ aI := by decide
@[simp] theorem aLb_ne_aX : aLb ≠ aX := by decide
@[simp] theorem aLb_ne_aY : aLb ≠ aY := by decide
@[simp] theorem aLb_ne_aPa : aLb ≠ aPa := by decide
@[simp] theorem aLb_ne_aLa : aLb ≠ aLa := by decide
@[simp] theorem aLb_ne_aO : aLb ≠ aO := by decide
@[simp] theorem aLb_ne_aQa : aLb ≠ aQa := by decide
@[simp] theorem aLb_ne_aQb : aLb ≠ aQb := by decide
@[simp] theorem aLb_ne_aQo : aLb ≠ aQo := by decide
@[simp] theorem aLb_ne_aU : aLb ≠ aU := by decide
@[simp] theorem aLb_ne_aV : aLb ≠ aV := by decide
@[simp] theorem aLb_ne_aS1 : aLb ≠ aS1 := by decide
@[simp] theorem aLb_ne_aS : aLb ≠ aS := by decide
@[simp] theorem aLb_ne_aC : aLb ≠ aC := by decide
@[simp] theorem aLb_ne_aI : aLb ≠ aI := by decide
@[simp] theorem aO_ne_aX : aO ≠ aX := by decide
@[simp] theorem aO_ne_aY : aO ≠ aY := by decide
@[simp] theorem aO_ne_aPa : aO ≠ aPa := by decide
@[simp] theorem aO_ne_aLa : aO ≠ aLa := by decide
@[simp] theorem aO_ne_aLb : aO ≠ aLb := by decide
@[simp] theorem aO_ne_aQa : aO ≠ aQa := by decide
@[simp] theorem aO_ne_aQb : aO ≠ aQb := by decide
@[simp] theorem aO_ne_aQo : aO ≠ aQo := by decide
@[simp] theorem aO_ne_aU : aO ≠ aU := by decide
@[simp] theorem aO_ne_aV : aO ≠ aV := by decide
@[simp] theorem aO_ne_aS1 : aO ≠ aS1 := by decide
@[simp] theorem aO_ne_aS : aO ≠ aS := by decide
@[simp] theorem aO_ne_aC : aO ≠ aC := by decide
@[simp] theorem aO_ne_aI : aO ≠ aI := by decide
@[simp] theorem aQa_ne_aX : aQa ≠ aX := by decide
@[simp] theorem aQa_ne_aY : aQa ≠ aY := by decide
@[simp] theorem aQa_ne_aPa : aQa ≠ aPa := by decide
@[simp] theorem aQa_ne_aLa : aQa ≠ aLa := by decide
@[simp] theorem aQa_ne_aLb : aQa ≠ aLb := by decide
@[simp] theorem aQa_ne_aO : aQa ≠ aO := by decide
@[simp] theorem aQa_ne_aQb : aQa ≠ aQb := by decide
@[simp] theorem aQa_ne_aQo : aQa ≠ aQo := by decide
@[simp] theorem aQa_ne_aU : aQa ≠ aU := by decide
@[simp] theorem aQa_ne_aV : aQa ≠ aV := by decide
@[simp] theorem aQa_ne_aS1 : aQa ≠ aS1 := by decide
@[simp] theorem aQa_ne_aS : aQa ≠ aS := by decide
@[simp] theorem aQa_ne_aC : aQa ≠ aC := by decide
@[simp] theorem aQa_ne_aI : aQa ≠ aI := by decide
@[simp] theorem aQb_ne_aX : aQb ≠ aX := by decide
@[simp] theorem aQb_ne_aY : aQb ≠ aY := by decide
@[simp] theorem aQb_ne_aPa : aQb ≠ aPa := by decide
@[simp] theorem aQb_ne_aLa : aQb ≠ aLa := by decide
@[simp] theorem aQb_ne_aLb : aQb ≠ aLb := by decide
@[simp] theorem aQb_ne_aO : aQb ≠ aO := by decide
@[simp] theorem aQb_ne_aQa : aQb ≠ aQa := by decide
@[simp] theorem aQb_ne_aQo : aQb ≠ aQo := by decide
@[simp] theorem aQb_ne_aU : aQb ≠ aU := by decide
@[simp] theorem aQb_ne_aV : aQb ≠ aV := by decide
@[simp] theorem aQb_ne_aS1 : aQb ≠ aS1 := by decide
@[simp] theorem aQb_ne_aS : aQb ≠ aS := by decide
@[simp] theorem aQb_ne_aC : aQb ≠ aC := by decide
@[simp] theorem aQb_ne_aI : aQb ≠ aI := by decide
@[simp] theorem aQo_ne_aX : aQo ≠ aX := by decide
@[simp] theorem aQo_ne_aY : aQo ≠ aY := by decide
@[simp] theorem aQo_ne_aPa : aQo ≠ aPa := by decide
@[simp] theorem aQo_ne_aLa : aQo ≠ aLa := by decide
@[simp] theorem aQo_ne_aLb : aQo ≠ aLb := by decide
@[simp] theorem aQo_ne_aO : aQo ≠ aO := by decide
@[simp] theorem aQo_ne_aQa : aQo ≠ aQa := by decide
@[simp] theorem aQo_ne_aQb : aQo ≠ aQb := by decide
@[simp] theorem aQo_ne_aU : aQo ≠ aU := by decide
@[simp] theorem aQo_ne_aV : aQo ≠ aV := by decide
@[simp] theorem aQo_ne_aS1 : aQo ≠ aS1 := by decide
@[simp] theorem aQo_ne_aS : aQo ≠ aS := by decide
@[simp] theorem aQo_ne_aC : aQo ≠ aC := by decide
@[simp] theorem aQo_ne_aI : aQo ≠ aI := by decide
@[simp] theorem aU_ne_aX : aU ≠ aX := by decide
@[simp] theorem aU_ne_aY : aU ≠ aY := by decide
@[simp] theorem aU_ne_aPa : aU ≠ aPa := by decide
@[simp] theorem aU_ne_aLa : aU ≠ aLa := by decide
@[simp] theorem aU_ne_aLb : aU ≠ aLb := by decide
@[simp] theorem aU_ne_aO : aU ≠ aO := by decide
@[simp] theorem aU_ne_aQa : aU ≠ aQa := by decide
@[simp] theorem aU_ne_aQb : aU ≠ aQb := by decide
@[simp] theorem aU_ne_aQo : aU ≠ aQo := by decide
@[simp] theorem aU_ne_aV : aU ≠ aV := by decide
@[simp] theorem aU_ne_aS1 : aU ≠ aS1 := by decide
@[simp] theorem aU_ne_aS : aU ≠ aS := by decide
@[simp] theorem aU_ne_aC : aU ≠ aC := by decide
@[simp] theorem aU_ne_aI : aU ≠ aI := by decide
@[simp] theorem aV_ne_aX : aV ≠ aX := by decide
@[simp] theorem aV_ne_aY : aV ≠ aY := by decide
@[simp] theorem aV_ne_aPa : aV ≠ aPa := by decide
@[simp] theorem aV_ne_aLa : aV ≠ aLa := by decide
@[simp] theorem aV_ne_aLb : aV ≠ aLb := by decide
@[simp] theorem aV_ne_aO : aV ≠ aO := by decide
@[simp] theorem aV_ne_aQa : aV ≠ aQa := by decide
@[simp] theorem aV_ne_aQb : aV ≠ aQb := by decide
@[simp] theorem aV_ne_aQo : aV ≠ aQo := by decide
@[simp] theorem aV_ne_aU : aV ≠ aU := by decide
@[simp] theorem aV_ne_aS1 : aV ≠ aS1 := by decide
@[simp] theorem aV_ne_aS : aV ≠ aS := by decide
@[simp] theorem aV_ne_aC : aV ≠ aC := by decide
@[simp] theorem aV_ne_aI : aV ≠ aI := by decide
@[simp] theorem aS1_ne_aX : aS1 ≠ aX := by decide
@[simp] theorem aS1_ne_aY : aS1 ≠ aY := by decide
@[simp] theorem aS1_ne_aPa : aS1 ≠ aPa := by decide
@[simp] theorem aS1_ne_aLa : aS1 ≠ aLa := by decide
@[simp] theorem aS1_ne_aLb : aS1 ≠ aLb := by decide
@[simp] theorem aS1_ne_aO : aS1 ≠ aO := by decide
@[simp] theorem aS1_ne_aQa : aS1 ≠ aQa := by decide
@[simp] theorem aS1_ne_aQb : aS1 ≠ aQb := by decide
@[simp] theorem aS1_ne_aQo : aS1 ≠ aQo := by decide
@[simp] theorem aS1_ne_aU : aS1 ≠ aU := by decide
@[simp] theorem aS1_ne_aV : aS1 ≠ aV := by decide
@[simp] theorem aS1_ne_aS : aS1 ≠ aS := by decide
@[simp] theorem aS1_ne_aC : aS1 ≠ aC := by decide
@[simp] theorem aS1_ne_aI : aS1 ≠ aI := by decide
@[simp] theorem aS_ne_aX : aS ≠ aX := by decide
@[simp] theorem aS_ne_aY : aS ≠ aY := by decide
@[simp] theorem aS_ne_aPa : aS ≠ aPa := by decide
@[simp] theorem aS_ne_aLa : aS ≠ aLa := by decide
@[simp] theorem aS_ne_aLb : aS ≠ aLb := by decide
@[simp] theorem aS_ne_aO : aS ≠ aO := by decide
@[simp] theorem aS_ne_aQa : aS ≠ aQa := by decide
@[simp] theorem aS_ne_aQb : aS ≠ aQb := by decide
@[simp] theorem aS_ne_aQo : aS ≠ aQo := by decide
@[simp] theorem aS_ne_aU : aS ≠ aU := by decide
@[simp] theorem aS_ne_aV : aS ≠ aV := by decide
@[simp] theorem aS_ne_aS1 : aS ≠ aS1 := by decide
@[simp] theorem aS_ne_aC : aS ≠ aC := by decide
@[simp] theorem aS_ne_aI : aS ≠ aI := by decide
@[simp] theorem aC_ne_aX : aC ≠ aX := by decide
@[simp] theorem aC_ne_aY : aC ≠ aY := by decide
@[simp] theorem aC_ne_aPa : aC ≠ aPa := by decide
@[simp] theorem aC_ne_aLa : aC ≠ aLa := by decide
@[simp] theorem aC_ne_aLb : aC ≠ aLb := by decide
@[simp] theorem aC_ne_aO : aC ≠ aO := by decide
@[simp] theorem aC_ne_aQa : aC ≠ aQa := by decide
@[simp] theorem aC_ne_aQb : aC ≠ aQb := by decide
@[simp] theorem aC_ne_aQo : aC ≠ aQo := by decide
@[simp] theorem aC_ne_aU : aC ≠ aU := by decide
@[simp] theorem aC_ne_aV : aC ≠ aV := by decide
@[simp] theorem aC_ne_aS1 : aC ≠ aS1 := by decide
@[simp] theorem aC_ne_aS : aC ≠ aS := by decide
@[simp] theorem aC_ne_aI : aC ≠ aI := by decide
@[simp] theorem aI_ne_aX : aI ≠ aX := by decide
@[simp] theorem aI_ne_aY : aI ≠ aY := by decide
@[simp] theorem aI_ne_aPa : aI ≠ aPa := by decide
@[simp] theorem aI_ne_aLa : aI ≠ aLa := by decide
@[simp] theorem aI_ne_aLb : aI ≠ aLb := by decide
@[simp] theorem aI_ne_aO : aI ≠ aO := by decide
@[simp] theorem aI_ne_aQa : aI ≠ aQa := by decide
@[simp] theorem aI_ne_aQb : aI ≠ aQb := by decide
@[simp] theorem aI_ne_aQo : aI ≠ aQo := by decide
@[simp] theorem aI_ne_aU : aI ≠ aU := by decide
@[simp] theorem aI_ne_aV : aI ≠ aV := by decide
@[simp] theorem aI_ne_aS1 : aI ≠ aS1 := by decide
@[simp] theorem aI_ne_aS : aI ≠ aS := by decide
@[simp] theorem aI_ne_aC : aI ≠ aC := by decide
@[simp] theorem aX_ne_lFl : aX ≠ lFl := by decide
@[simp] theorem lFl_ne_aX : lFl ≠ aX := by decide
@[simp] theorem aX_ne_lDh : aX ≠ lDh := by decide
@[simp] theorem lDh_ne_aX : lDh ≠ aX := by decide
@[simp] theorem aX_ne_lDt : aX ≠ lDt := by decide
@[simp] theorem lDt_ne_aX : lDt ≠ aX := by decide
@[simp] theorem aX_ne_lDg : aX ≠ lDg := by decide
@[simp] theorem lDg_ne_aX : lDg ≠ aX := by decide
@[simp] theorem aX_ne_lDi : aX ≠ lDi := by decide
@[simp] theorem lDi_ne_aX : lDi ≠ aX := by decide
@[simp] theorem aX_ne_lRp : aX ≠ lRp := by decide
@[simp] theorem lRp_ne_aX : lRp ≠ aX := by decide
@[simp] theorem aX_ne_lRn : aX ≠ lRn := by decide
@[simp] theorem lRn_ne_aX : lRn ≠ aX := by decide
@[simp] theorem aX_ne_lFle : aX ≠ lFle := by decide
@[simp] theorem lFle_ne_aX : lFle ≠ aX := by decide
@[simp] theorem aX_ne_lDir : aX ≠ lDir := by decide
@[simp] theorem lDir_ne_aX : lDir ≠ aX := by decide
@[simp] theorem aX_ne_lFln : aX ≠ lFln := by decide
@[simp] theorem lFln_ne_aX : lFln ≠ aX := by decide
@[simp] theorem aX_ne_lFll : aX ≠ lFll := by decide
@[simp] theorem lFll_ne_aX : lFll ≠ aX := by decide
@[simp] theorem aX_ne_lFls : aX ≠ lFls := by decide
@[simp] theorem lFls_ne_aX : lFls ≠ aX := by decide
@[simp] theorem aX_ne_lKb : aX ≠ lKb := by decide
@[simp] theorem lKb_ne_aX : lKb ≠ aX := by decide
@[simp] theorem aY_ne_lFl : aY ≠ lFl := by decide
@[simp] theorem lFl_ne_aY : lFl ≠ aY := by decide
@[simp] theorem aY_ne_lDh : aY ≠ lDh := by decide
@[simp] theorem lDh_ne_aY : lDh ≠ aY := by decide
@[simp] theorem aY_ne_lDt : aY ≠ lDt := by decide
@[simp] theorem lDt_ne_aY : lDt ≠ aY := by decide
@[simp] theorem aY_ne_lDg : aY ≠ lDg := by decide
@[simp] theorem lDg_ne_aY : lDg ≠ aY := by decide
@[simp] theorem aY_ne_lDi : aY ≠ lDi := by decide
@[simp] theorem lDi_ne_aY : lDi ≠ aY := by decide
@[simp] theorem aY_ne_lRp : aY ≠ lRp := by decide
@[simp] theorem lRp_ne_aY : lRp ≠ aY := by decide
@[simp] theorem aY_ne_lRn : aY ≠ lRn := by decide
@[simp] theorem lRn_ne_aY : lRn ≠ aY := by decide
@[simp] theorem aY_ne_lFle : aY ≠ lFle := by decide
@[simp] theorem lFle_ne_aY : lFle ≠ aY := by decide
@[simp] theorem aY_ne_lDir : aY ≠ lDir := by decide
@[simp] theorem lDir_ne_aY : lDir ≠ aY := by decide
@[simp] theorem aY_ne_lFln : aY ≠ lFln := by decide
@[simp] theorem lFln_ne_aY : lFln ≠ aY := by decide
@[simp] theorem aY_ne_lFll : aY ≠ lFll := by decide
@[simp] theorem lFll_ne_aY : lFll ≠ aY := by decide
@[simp] theorem aY_ne_lFls : aY ≠ lFls := by decide
@[simp] theorem lFls_ne_aY : lFls ≠ aY := by decide
@[simp] theorem aY_ne_lKb : aY ≠ lKb := by decide
@[simp] theorem lKb_ne_aY : lKb ≠ aY := by decide
@[simp] theorem aPa_ne_lFl : aPa ≠ lFl := by decide
@[simp] theorem lFl_ne_aPa : lFl ≠ aPa := by decide
@[simp] theorem aPa_ne_lDh : aPa ≠ lDh := by decide
@[simp] theorem lDh_ne_aPa : lDh ≠ aPa := by decide
@[simp] theorem aPa_ne_lDt : aPa ≠ lDt := by decide
@[simp] theorem lDt_ne_aPa : lDt ≠ aPa := by decide
@[simp] theorem aPa_ne_lDg : aPa ≠ lDg := by decide
@[simp] theorem lDg_ne_aPa : lDg ≠ aPa := by decide
@[simp] theorem aPa_ne_lDi : aPa ≠ lDi := by decide
@[simp] theorem lDi_ne_aPa : lDi ≠ aPa := by decide
@[simp] theorem aPa_ne_lRp : aPa ≠ lRp := by decide
@[simp] theorem lRp_ne_aPa : lRp ≠ aPa := by decide
@[simp] theorem aPa_ne_lRn : aPa ≠ lRn := by decide
@[simp] theorem lRn_ne_aPa : lRn ≠ aPa := by decide
@[simp] theorem aPa_ne_lFle : aPa ≠ lFle := by decide
@[simp] theorem lFle_ne_aPa : lFle ≠ aPa := by decide
@[simp] theorem aPa_ne_lDir : aPa ≠ lDir := by decide
@[simp] theorem lDir_ne_aPa : lDir ≠ aPa := by decide
@[simp] theorem aPa_ne_lFln : aPa ≠ lFln := by decide
@[simp] theorem lFln_ne_aPa : lFln ≠ aPa := by decide
@[simp] theorem aPa_ne_lFll : aPa ≠ lFll := by decide
@[simp] theorem lFll_ne_aPa : lFll ≠ aPa := by decide
@[simp] theorem aPa_ne_lFls : aPa ≠ lFls := by decide
@[simp] theorem lFls_ne_aPa : lFls ≠ aPa := by decide
@[simp] theorem aPa_ne_lKb : aPa ≠ lKb := by decide
@[simp] theorem lKb_ne_aPa : lKb ≠ aPa := by decide
@[simp] theorem aLa_ne_lFl : aLa ≠ lFl := by decide
@[simp] theorem lFl_ne_aLa : lFl ≠ aLa := by decide
@[simp] theorem aLa_ne_lDh : aLa ≠ lDh := by decide
@[simp] theorem lDh_ne_aLa : lDh ≠ aLa := by decide
@[simp] theorem aLa_ne_lDt : aLa ≠ lDt := by decide
@[simp] theorem lDt_ne_aLa : lDt ≠ aLa := by decide
@[simp] theorem aLa_ne_lDg : aLa ≠ lDg := by decide
@[simp] theorem lDg_ne_aLa : lDg ≠ aLa := by decide
@[simp] theorem aLa_ne_lDi : aLa ≠ lDi := by decide
@[simp] theorem lDi_ne_aLa : lDi ≠ aLa := by decide
@[simp] theorem aLa_ne_lRp : aLa ≠ lRp := by decide
@[simp] theorem lRp_ne_aLa : lRp ≠ aLa := by decide
@[simp] theorem aLa_ne_lRn : aLa ≠ lRn := by decide
@[simp] theorem lRn_ne_aLa : lRn ≠ aLa := by decide
@[simp] theorem aLa_ne_lFle : aLa ≠ lFle := by decide
@[simp] theorem lFle_ne_aLa : lFle ≠ aLa := by decide
@[simp] theorem aLa_ne_lDir : aLa ≠ lDir := by decide
@[simp] theorem lDir_ne_aLa : lDir ≠ aLa := by decide
@[simp] theorem aLa_ne_lFln : aLa ≠ lFln := by decide
@[simp] theorem lFln_ne_aLa : lFln ≠ aLa := by decide
@[simp] theorem aLa_ne_lFll : aLa ≠ lFll := by decide
@[simp] theorem lFll_ne_aLa : lFll ≠ aLa := by decide
@[simp] theorem aLa_ne_lFls : aLa ≠ lFls := by decide
@[simp] theorem lFls_ne_aLa : lFls ≠ aLa := by decide
@[simp] theorem aLa_ne_lKb : aLa ≠ lKb := by decide
@[simp] theorem lKb_ne_aLa : lKb ≠ aLa := by decide
@[simp] theorem aLb_ne_lFl : aLb ≠ lFl := by decide
@[simp] theorem lFl_ne_aLb : lFl ≠ aLb := by decide
@[simp] theorem aLb_ne_lDh : aLb ≠ lDh := by decide
@[simp] theorem lDh_ne_aLb : lDh ≠ aLb := by decide
@[simp] theorem aLb_ne_lDt : aLb ≠ lDt := by decide
@[simp] theorem lDt_ne_aLb : lDt ≠ aLb := by decide
@[simp] theorem aLb_ne_lDg : aLb ≠ lDg := by decide
@[simp] theorem lDg_ne_aLb : lDg ≠ aLb := by decide
@[simp] theorem aLb_ne_lDi : aLb ≠ lDi := by decide
@[simp] theorem lDi_ne_aLb : lDi ≠ aLb := by decide
@[simp] theorem aLb_ne_lRp : aLb ≠ lRp := by decide
@[simp] theorem lRp_ne_aLb : lRp ≠ aLb := by decide
@[simp] theorem aLb_ne_lRn : aLb ≠ lRn := by decide
@[simp] theorem lRn_ne_aLb : lRn ≠ aLb := by decide
@[simp] theorem aLb_ne_lFle : aLb ≠ lFle := by decide
@[simp] theorem lFle_ne_aLb : lFle ≠ aLb := by decide
@[simp] theorem aLb_ne_lDir : aLb ≠ lDir := by decide
@[simp] theorem lDir_ne_aLb : lDir ≠ aLb := by decide
@[simp] theorem aLb_ne_lFln : aLb ≠ lFln := by decide
@[simp] theorem lFln_ne_aLb : lFln ≠ aLb := by decide
@[simp] theorem aLb_ne_lFll : aLb ≠ lFll := by decide
@[simp] theorem lFll_ne_aLb : lFll ≠ aLb := by decide
@[simp] theorem aLb_ne_lFls : aLb ≠ lFls := by decide
@[simp] theorem lFls_ne_aLb : lFls ≠ aLb := by decide
@[simp] theorem aLb_ne_lKb : aLb ≠ lKb := by decide
@[simp] theorem lKb_ne_aLb : lKb ≠ aLb := by decide
@[simp] theorem aO_ne_lFl : aO ≠ lFl := by decide
@[simp] theorem lFl_ne_aO : lFl ≠ aO := by decide
@[simp] theorem aO_ne_lDh : aO ≠ lDh := by decide
@[simp] theorem lDh_ne_aO : lDh ≠ aO := by decide
@[simp] theorem aO_ne_lDt : aO ≠ lDt := by decide
@[simp] theorem lDt_ne_aO : lDt ≠ aO := by decide
@[simp] theorem aO_ne_lDg : aO ≠ lDg := by decide
@[simp] theorem lDg_ne_aO : lDg ≠ aO := by decide
@[simp] theorem aO_ne_lDi : aO ≠ lDi := by decide
@[simp] theorem lDi_ne_aO : lDi ≠ aO := by decide
@[simp] theorem aO_ne_lRp : aO ≠ lRp := by decide
@[simp] theorem lRp_ne_aO : lRp ≠ aO := by decide
@[simp] theorem aO_ne_lRn : aO ≠ lRn := by decide
@[simp] theorem lRn_ne_aO : lRn ≠ aO := by decide
@[simp] theorem aO_ne_lFle : aO ≠ lFle := by decide
@[simp] theorem lFle_ne_aO : lFle ≠ aO := by decide
@[simp] theorem aO_ne_lDir : aO ≠ lDir := by decide
@[simp] theorem lDir_ne_aO : lDir ≠ aO := by decide
@[simp] theorem aO_ne_lFln : aO ≠ lFln := by decide
@[simp] theorem lFln_ne_aO : lFln ≠ aO := by decide
@[simp] theorem aO_ne_lFll : aO ≠ lFll := by decide
@[simp] theorem lFll_ne_aO : lFll ≠ aO := by decide
@[simp] theorem aO_ne_lFls : aO ≠ lFls := by decide
@[simp] theorem lFls_ne_aO : lFls ≠ aO := by decide
@[simp] theorem aO_ne_lKb : aO ≠ lKb := by decide
@[simp] theorem lKb_ne_aO : lKb ≠ aO := by decide
@[simp] theorem aQa_ne_lFl : aQa ≠ lFl := by decide
@[simp] theorem lFl_ne_aQa : lFl ≠ aQa := by decide
@[simp] theorem aQa_ne_lDh : aQa ≠ lDh := by decide
@[simp] theorem lDh_ne_aQa : lDh ≠ aQa := by decide
@[simp] theorem aQa_ne_lDt : aQa ≠ lDt := by decide
@[simp] theorem lDt_ne_aQa : lDt ≠ aQa := by decide
@[simp] theorem aQa_ne_lDg : aQa ≠ lDg := by decide
@[simp] theorem lDg_ne_aQa : lDg ≠ aQa := by decide
@[simp] theorem aQa_ne_lDi : aQa ≠ lDi := by decide
@[simp] theorem lDi_ne_aQa : lDi ≠ aQa := by decide
@[simp] theorem aQa_ne_lRp : aQa ≠ lRp := by decide
@[simp] theorem lRp_ne_aQa : lRp ≠ aQa := by decide
@[simp] theorem aQa_ne_lRn : aQa ≠ lRn := by decide
@[simp] theorem lRn_ne_aQa : lRn ≠ aQa := by decide
@[simp] theorem aQa_ne_lFle : aQa ≠ lFle := by decide
@[simp] theorem lFle_ne_aQa : lFle ≠ aQa := by decide
@[simp] theorem aQa_ne_lDir : aQa ≠ lDir := by decide
@[simp] theorem lDir_ne_aQa : lDir ≠ aQa := by decide
@[simp] theorem aQa_ne_lFln : aQa ≠ lFln := by decide
@[simp] theorem lFln_ne_aQa : lFln ≠ aQa := by decide
@[simp] theorem aQa_ne_lFll : aQa ≠ lFll := by decide
@[simp] theorem lFll_ne_aQa : lFll ≠ aQa := by decide
@[simp] theorem aQa_ne_lFls : aQa ≠ lFls := by decide
@[simp] theorem lFls_ne_aQa : lFls ≠ aQa := by decide
@[simp] theorem aQa_ne_lKb : aQa ≠ lKb := by decide
@[simp] theorem lKb_ne_aQa : lKb ≠ aQa := by decide
@[simp] theorem aQb_ne_lFl : aQb ≠ lFl := by decide
@[simp] theorem lFl_ne_aQb : lFl ≠ aQb := by decide
@[simp] theorem aQb_ne_lDh : aQb ≠ lDh := by decide
@[simp] theorem lDh_ne_aQb : lDh ≠ aQb := by decide
@[simp] theorem aQb_ne_lDt : aQb ≠ lDt := by decide
@[simp] theorem lDt_ne_aQb : lDt ≠ aQb := by decide
@[simp] theorem aQb_ne_lDg : aQb ≠ lDg := by decide
@[simp] theorem lDg_ne_aQb : lDg ≠ aQb := by decide
@[simp] theorem aQb_ne_lDi : aQb ≠ lDi := by decide
@[simp] theorem lDi_ne_aQb : lDi ≠ aQb := by decide
@[simp] theorem aQb_ne_lRp : aQb ≠ lRp := by decide
@[simp] theorem lRp_ne_aQb : lRp ≠ aQb := by decide
@[simp] theorem aQb_ne_lRn : aQb ≠ lRn := by decide
@[simp] theorem lRn_ne_aQb : lRn ≠ aQb := by decide
@[simp] theorem aQb_ne_lFle : aQb ≠ lFle := by decide
@[simp] theorem lFle_ne_aQb : lFle ≠ aQb := by decide
@[simp] theorem aQb_ne_lDir : aQb ≠ lDir := by decide
@[simp] theorem lDir_ne_aQb : lDir ≠ aQb := by decide
@[simp] theorem aQb_ne_lFln : aQb ≠ lFln := by decide
@[simp] theorem lFln_ne_aQb : lFln ≠ aQb := by decide
@[simp] theorem aQb_ne_lFll : aQb ≠ lFll := by decide
@[simp] theorem lFll_ne_aQb : lFll ≠ aQb := by decide
@[simp] theorem aQb_ne_lFls : aQb ≠ lFls := by decide
@[simp] theorem lFls_ne_aQb : lFls ≠ aQb := by decide
@[simp] theorem aQb_ne_lKb : aQb ≠ lKb := by decide
@[simp] theorem lKb_ne_aQb : lKb ≠ aQb := by decide
@[simp] theorem aQo_ne_lFl : aQo ≠ lFl := by decide
@[simp] theorem lFl_ne_aQo : lFl ≠ aQo := by decide
@[simp] theorem aQo_ne_lDh : aQo ≠ lDh := by decide
@[simp] theorem lDh_ne_aQo : lDh ≠ aQo := by decide
@[simp] theorem aQo_ne_lDt : aQo ≠ lDt := by decide
@[simp] theorem lDt_ne_aQo : lDt ≠ aQo := by decide
@[simp] theorem aQo_ne_lDg : aQo ≠ lDg := by decide
@[simp] theorem lDg_ne_aQo : lDg ≠ aQo := by decide
@[simp] theorem aQo_ne_lDi : aQo ≠ lDi := by decide
@[simp] theorem lDi_ne_aQo : lDi ≠ aQo := by decide
@[simp] theorem aQo_ne_lRp : aQo ≠ lRp := by decide
@[simp] theorem lRp_ne_aQo : lRp ≠ aQo := by decide
@[simp] theorem aQo_ne_lRn : aQo ≠ lRn := by decide
@[simp] theorem lRn_ne_aQo : lRn ≠ aQo := by decide
@[simp] theorem aQo_ne_lFle : aQo ≠ lFle := by decide
@[simp] theorem lFle_ne_aQo : lFle ≠ aQo := by decide
@[simp] theorem aQo_ne_lDir : aQo ≠ lDir := by decide
@[simp] theorem lDir_ne_aQo : lDir ≠ aQo := by decide
@[simp] theorem aQo_ne_lFln : aQo ≠ lFln := by decide
@[simp] theorem lFln_ne_aQo : lFln ≠ aQo := by decide
@[simp] theorem aQo_ne_lFll : aQo ≠ lFll := by decide
@[simp] theorem lFll_ne_aQo : lFll ≠ aQo := by decide
@[simp] theorem aQo_ne_lFls : aQo ≠ lFls := by decide
@[simp] theorem lFls_ne_aQo : lFls ≠ aQo := by decide
@[simp] theorem aQo_ne_lKb : aQo ≠ lKb := by decide
@[simp] theorem lKb_ne_aQo : lKb ≠ aQo := by decide
@[simp] theorem aU_ne_lFl : aU ≠ lFl := by decide
@[simp] theorem lFl_ne_aU : lFl ≠ aU := by decide
@[simp] theorem aU_ne_lDh : aU ≠ lDh := by decide
@[simp] theorem lDh_ne_aU : lDh ≠ aU := by decide
@[simp] theorem aU_ne_lDt : aU ≠ lDt := by decide
@[simp] theorem lDt_ne_aU : lDt ≠ aU := by decide
@[simp] theorem aU_ne_lDg : aU ≠ lDg := by decide
@[simp] theorem lDg_ne_aU : lDg ≠ aU := by decide
@[simp] theorem aU_ne_lDi : aU ≠ lDi := by decide
@[simp] theorem lDi_ne_aU : lDi ≠ aU := by decide
@[simp] theorem aU_ne_lRp : aU ≠ lRp := by decide
@[simp] theorem lRp_ne_aU : lRp ≠ aU := by decide
@[simp] theorem aU_ne_lRn : aU ≠ lRn := by decide
@[simp] theorem lRn_ne_aU : lRn ≠ aU := by decide
@[simp] theorem aU_ne_lFle : aU ≠ lFle := by decide
@[simp] theorem lFle_ne_aU : lFle ≠ aU := by decide
@[simp] theorem aU_ne_lDir : aU ≠ lDir := by decide
@[simp] theorem lDir_ne_aU : lDir ≠ aU := by decide
@[simp] theorem aU_ne_lFln : aU ≠ lFln := by decide
@[simp] theorem lFln_ne_aU : lFln ≠ aU := by decide
@[simp] theorem aU_ne_lFll : aU ≠ lFll := by decide
@[simp] theorem lFll_ne_aU : lFll ≠ aU := by decide
@[simp] theorem aU_ne_lFls : aU ≠ lFls := by decide
@[simp] theorem lFls_ne_aU : lFls ≠ aU := by decide
@[simp] theorem aU_ne_lKb : aU ≠ lKb := by decide
@[simp] theorem lKb_ne_aU : lKb ≠ aU := by decide
@[simp] theorem aV_ne_lFl : aV ≠ lFl := by decide
@[simp] theorem lFl_ne_aV : lFl ≠ aV := by decide
@[simp] theorem aV_ne_lDh : aV ≠ lDh := by decide
@[simp] theorem lDh_ne_aV : lDh ≠ aV := by decide
@[simp] theorem aV_ne_lDt : aV ≠ lDt := by decide
@[simp] theorem lDt_ne_aV : lDt ≠ aV := by decide
@[simp] theorem aV_ne_lDg : aV ≠ lDg := by decide
@[simp] theorem lDg_ne_aV : lDg ≠ aV := by decide
@[simp] theorem aV_ne_lDi : aV ≠ lDi := by decide
@[simp] theorem lDi_ne_aV : lDi ≠ aV := by decide
@[simp] theorem aV_ne_lRp : aV ≠ lRp := by decide
@[simp] theorem lRp_ne_aV : lRp ≠ aV := by decide
@[simp] theorem aV_ne_lRn : aV ≠ lRn := by decide
@[simp] theorem lRn_ne_aV : lRn ≠ aV := by decide
@[simp] theorem aV_ne_lFle : aV ≠ lFle := by decide
@[simp] theorem lFle_ne_aV : lFle ≠ aV := by decide
@[simp] theorem aV_ne_lDir : aV ≠ lDir := by decide
@[simp] theorem lDir_ne_aV : lDir ≠ aV := by decide
@[simp] theorem aV_ne_lFln : aV ≠ lFln := by decide
@[simp] theorem lFln_ne_aV : lFln ≠ aV := by decide
@[simp] theorem aV_ne_lFll : aV ≠ lFll := by decide
@[simp] theorem lFll_ne_aV : lFll ≠ aV := by decide
@[simp] theorem aV_ne_lFls : aV ≠ lFls := by decide
@[simp] theorem lFls_ne_aV : lFls ≠ aV := by decide
@[simp] theorem aV_ne_lKb : aV ≠ lKb := by decide
@[simp] theorem lKb_ne_aV : lKb ≠ aV := by decide
@[simp] theorem aS1_ne_lFl : aS1 ≠ lFl := by decide
@[simp] theorem lFl_ne_aS1 : lFl ≠ aS1 := by decide
@[simp] theorem aS1_ne_lDh : aS1 ≠ lDh := by decide
@[simp] theorem lDh_ne_aS1 : lDh ≠ aS1 := by decide
@[simp] theorem aS1_ne_lDt : aS1 ≠ lDt := by decide
@[simp] theorem lDt_ne_aS1 : lDt ≠ aS1 := by decide
@[simp] theorem aS1_ne_lDg : aS1 ≠ lDg := by decide
@[simp] theorem lDg_ne_aS1 : lDg ≠ aS1 := by decide
@[simp] theorem aS1_ne_lDi : aS1 ≠ lDi := by decide
@[simp] theorem lDi_ne_aS1 : lDi ≠ aS1 := by decide
@[simp] theorem aS1_ne_lRp : aS1 ≠ lRp := by decide
@[simp] theorem lRp_ne_aS1 : lRp ≠ aS1 := by decide
@[simp] theorem aS1_ne_lRn : aS1 ≠ lRn := by decide
@[simp] theorem lRn_ne_aS1 : lRn ≠ aS1 := by decide
@[simp] theorem aS1_ne_lFle : aS1 ≠ lFle := by decide
@[simp] theorem lFle_ne_aS1 : lFle ≠ aS1 := by decide
@[simp] theorem aS1_ne_lDir : aS1 ≠ lDir := by decide
@[simp] theorem lDir_ne_aS1 : lDir ≠ aS1 := by decide
@[simp] theorem aS1_ne_lFln : aS1 ≠ lFln := by decide
@[simp] theorem lFln_ne_aS1 : lFln ≠ aS1 := by decide
@[simp] theorem aS1_ne_lFll : aS1 ≠ lFll := by decide
@[simp] theorem lFll_ne_aS1 : lFll ≠ aS1 := by decide
@[simp] theorem aS1_ne_lFls : aS1 ≠ lFls := by decide
@[simp] theorem lFls_ne_aS1 : lFls ≠ aS1 := by decide
@[simp] theorem aS1_ne_lKb : aS1 ≠ lKb := by decide
@[simp] theorem lKb_ne_aS1 : lKb ≠ aS1 := by decide
@[simp] theorem aS_ne_lFl : aS ≠ lFl := by decide
@[simp] theorem lFl_ne_aS : lFl ≠ aS := by decide
@[simp] theorem aS_ne_lDh : aS ≠ lDh := by decide
@[simp] theorem lDh_ne_aS : lDh ≠ aS := by decide
@[simp] theorem aS_ne_lDt : aS ≠ lDt := by decide
@[simp] theorem lDt_ne_aS : lDt ≠ aS := by decide
@[simp] theorem aS_ne_lDg : aS ≠ lDg := by decide
@[simp] theorem lDg_ne_aS : lDg ≠ aS := by decide
@[simp] theorem aS_ne_lDi : aS ≠ lDi := by decide
@[simp] theorem lDi_ne_aS : lDi ≠ aS := by decide
@[simp] theorem aS_ne_lRp : aS ≠ lRp := by decide
@[simp] theorem lRp_ne_aS : lRp ≠ aS := by decide
@[simp] theorem aS_ne_lRn : aS ≠ lRn := by decide
@[simp] theorem lRn_ne_aS : lRn ≠ aS := by decide
@[simp] theorem aS_ne_lFle : aS ≠ lFle := by decide
@[simp] theorem lFle_ne_aS : lFle ≠ aS := by decide
@[simp] theorem aS_ne_lDir : aS ≠ lDir := by decide
@[simp] theorem lDir_ne_aS : lDir ≠ aS := by decide
@[simp] theorem aS_ne_lFln : aS ≠ lFln := by decide
@[simp] theorem lFln_ne_aS : lFln ≠ aS := by decide
@[simp] theorem aS_ne_lFll : aS ≠ lFll := by decide
@[simp] theorem lFll_ne_aS : lFll ≠ aS := by decide
@[simp] theorem aS_ne_lFls : aS ≠ lFls := by decide
@[simp] theorem lFls_ne_aS : lFls ≠ aS := by decide
@[simp] theorem aS_ne_lKb : aS ≠ lKb := by decide
@[simp] theorem lKb_ne_aS : lKb ≠ aS := by decide
@[simp] theorem aC_ne_lFl : aC ≠ lFl := by decide
@[simp] theorem lFl_ne_aC : lFl ≠ aC := by decide
@[simp] theorem aC_ne_lDh : aC ≠ lDh := by decide
@[simp] theorem lDh_ne_aC : lDh ≠ aC := by decide
@[simp] theorem aC_ne_lDt : aC ≠ lDt := by decide
@[simp] theorem lDt_ne_aC : lDt ≠ aC := by decide
@[simp] theorem aC_ne_lDg : aC ≠ lDg := by decide
@[simp] theorem lDg_ne_aC : lDg ≠ aC := by decide
@[simp] theorem aC_ne_lDi : aC ≠ lDi := by decide
@[simp] theorem lDi_ne_aC : lDi ≠ aC := by decide
@[simp] theorem aC_ne_lRp : aC ≠ lRp := by decide
@[simp] theorem lRp_ne_aC : lRp ≠ aC := by decide
@[simp] theorem aC_ne_lRn : aC ≠ lRn := by decide
@[simp] theorem lRn_ne_aC : lRn ≠ aC := by decide
@[simp] theorem aC_ne_lFle : aC ≠ lFle := by decide
@[simp] theorem lFle_ne_aC : lFle ≠ aC := by decide
@[simp] theorem aC_ne_lDir : aC ≠ lDir := by decide
@[simp] theorem lDir_ne_aC : lDir ≠ aC := by decide
@[simp] theorem aC_ne_lFln : aC ≠ lFln := by decide
@[simp] theorem lFln_ne_aC : lFln ≠ aC := by decide
@[simp] theorem aC_ne_lFll : aC ≠ lFll := by decide
@[simp] theorem lFll_ne_aC : lFll ≠ aC := by decide
@[simp] theorem aC_ne_lFls : aC ≠ lFls := by decide
@[simp] theorem lFls_ne_aC : lFls ≠ aC := by decide
@[simp] theorem aC_ne_lKb : aC ≠ lKb := by decide
@[simp] theorem lKb_ne_aC : lKb ≠ aC := by decide
@[simp] theorem aI_ne_lFl : aI ≠ lFl := by decide
@[simp] theorem lFl_ne_aI : lFl ≠ aI := by decide
@[simp] theorem aI_ne_lDh : aI ≠ lDh := by decide
@[simp] theorem lDh_ne_aI : lDh ≠ aI := by decide
@[simp] theorem aI_ne_lDt : aI ≠ lDt := by decide
@[simp] theorem lDt_ne_aI : lDt ≠ aI := by decide
@[simp] theorem aI_ne_lDg : aI ≠ lDg := by decide
@[simp] theorem lDg_ne_aI : lDg ≠ aI := by decide
@[simp] theorem aI_ne_lDi : aI ≠ lDi := by decide
@[simp] theorem lDi_ne_aI : lDi ≠ aI := by decide
@[simp] theorem aI_ne_lRp : aI ≠ lRp := by decide
@[simp] theorem lRp_ne_aI : lRp ≠ aI := by decide
@[simp] theorem aI_ne_lRn : aI ≠ lRn := by decide
@[simp] theorem lRn_ne_aI : lRn ≠ aI := by decide
@[simp] theorem aI_ne_lFle : aI ≠ lFle := by decide
@[simp] theorem lFle_ne_aI : lFle ≠ aI := by decide
@[simp] theorem aI_ne_lDir : aI ≠ lDir := by decide
@[simp] theorem lDir_ne_aI : lDir ≠ aI := by decide
@[simp] theorem aI_ne_lFln : aI ≠ lFln := by decide
@[simp] theorem lFln_ne_aI : lFln ≠ aI := by decide
@[simp] theorem aI_ne_lFll : aI ≠ lFll := by decide
@[simp] theorem lFll_ne_aI : lFll ≠ aI := by decide
@[simp] theorem aI_ne_lFls : aI ≠ lFls := by decide
@[simp] theorem lFls_ne_aI : lFls ≠ aI := by decide
@[simp] theorem aI_ne_lKb : aI ≠ lKb := by decide
@[simp] theorem lKb_ne_aI : lKb ≠ aI := by decide

/-- One digit: `s1 := u + v; s := s1 + c; c := (s1 < u) + (s < s1); [qo] := s`. -/
def digitP : ProgHOL 64 :=
  .seq (.assign .local aS1 (.op .add [vv aU, vv aV]))
  (.seq (.assign .local aS (.op .add [vv aS1, vv aC]))
  (.seq (.assign .local aC (.op .add [.cmp .lower (vv aS1) (vv aU), .cmp .lower (vv aS) (vv aS1)]))
  (.store (vv aQo) (vv aS))))

def addLoop1 : ProgHOL 64 :=
  .while (.cmp .lower (vv aI) (vv aLb))
    (.seq (.assign .local aU (.load .one (vv aQa)))
    (.seq (.assign .local aV (.load .one (vv aQb)))
    (.seq digitP
    (.seq (.assign .local aQa (.op .add [vv aQa, .const 8]))
    (.seq (.assign .local aQb (.op .add [vv aQb, .const 8]))
    (.seq (.assign .local aQo (.op .add [vv aQo, .const 8]))
    (.assign .local aI (.op .add [vv aI, .const 1]))))))))

def addLoop2 : ProgHOL 64 :=
  .while (.cmp .lower (vv aI) (vv aLa))
    (.seq (.assign .local aU (.load .one (vv aQa)))
    (.seq (.assign .local aV (.const 0))
    (.seq digitP
    (.seq (.assign .local aQa (.op .add [vv aQa, .const 8]))
    (.seq (.assign .local aQo (.op .add [vv aQo, .const 8]))
    (.assign .local aI (.op .add [vv aI, .const 1])))))))

/-- `x + y` for heap blocks `x` (at `aX`) and `y` (at `aY`), `x` the longer. -/
def addCore (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local aLa (.load .one (vv aX)))
  (.seq (.assign .local aLb (.load .one (vv aY)))
  (allocP C aO (.panop .mul [.op .add [vv aLa, .const 2], .const 8])
  (.seq (.assign .local aQa (.op .add [vv aX, .const 8]))
  (.seq (.assign .local aQb (.op .add [vv aY, .const 8]))
  (.seq (.assign .local aQo (.op .add [vv aO, .const 8]))
  (.seq (.assign .local aC (.const 0)) (.seq (.assign .local aI (.const 0))
  (.seq addLoop1 (.seq addLoop2
  (.seq (.store (vv aQo) (vv aC))
  (.seq (.store (vv aO) (.op .add [vv aLa, vv aC]))
  (.return (vv aO)))))))))))))

def addLocals : List MlS := [aLa, aLb, aO, aQa, aQb, aQo, aU, aV, aS1, aS, aC, aI]
def addParams : List MlS := [aX, aY]

def addBody (C : Ctx) : ProgHOL 64 := prologue addLocals (addCore C)

/-! ## Math -/

/-- The digits of `x + y`, one past `x`'s length. -/
def sumW (x y lx : Nat) : List (BitVec 64) := (List.range (lx + 1)).map fun k => BitVec.ofNat 64 ((x + y) / B ^ k % B)

theorem sumW_get (x y lx k : Nat) (hk : k < lx + 1) :
    (sumW x y lx)[k]? = some (BitVec.ofNat 64 ((x + y) / B ^ k % B)) := by
  simp [sumW, hk]

/-- The result's limbs: `lx + c` digits, `c` the final carry. -/
theorem add_final (x y : Nat) (hy : y < B ^ (limbs x).length) :
    limbs (x + y) = (List.range ((limbs x).length + S x y (limbs x).length / B ^ (limbs x).length)).map
      (fun k => BitVec.ofNat 64 ((x + y) / B ^ k % B)) := by
  generalize hL : (limbs x).length = L at hy ⊢
  have hx : x < B ^ L := hL ▸ (limbs_length_lt_iff x _).mp (Nat.le_refl _)
  have hS := S_full x y L hx hy
  rw [hS]
  have hc := carry_le x y L
  rw [hS] at hc
  have hP : B ^ (L + 1) = B ^ L * 18446744073709551616 := Nat.pow_succ _ _
  have hpos := pow_pos' L
  have hlow : L = 0 ∨ B ^ (L - 1) ≤ x := by
    by_cases h0 : L = 0
    · exact Or.inl h0
    · right
      have h2 : ¬ (limbs x).length ≤ L - 1 := by omega
      rw [limbs_length_lt_iff] at h2
      omega
  have hq := Nat.div_add_mod (x + y) (B ^ L)
  have hm := Nat.mod_lt (x + y) hpos
  generalize hd : (x + y) / B ^ L = q at hc hq ⊢
  generalize hr : (x + y) % B ^ L = r at hq hm
  apply limbs_eq_digits
  · rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl
    · simp only [Nat.add_zero]
      generalize B ^ L = P at *; omega
    · rw [hP]; generalize B ^ L = P at *; omega
  · rcases (by omega : q = 0 ∨ q = 1) with rfl | rfl
    · simp only [Nat.add_zero]
      rcases hlow with h | h
      · exact Or.inl h
      · right; omega
    · right; simp only [Nat.add_sub_cancel]
      generalize B ^ L = P at *; omega

section
variable {σ : Type}

theorem fillI_succ_eq (B0 W : List (BitVec 64)) (o i : Nat) (w : BitVec 64) (hw : W[i]? = some w) :
    (fillI B0 W o i).set (o + i) w = fillI B0 W o (i + 1) := by
  simp [fillI, List.getD_eq_getElem?_getD, hw]

/-- One digit of the sum: from the limbs and the carry, the digit is stored and the carry advances. -/
theorem step_digit {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {D : List MlS} (B0 W : List (BitVec 64))
    (od i x y : Nat) (hW : W[i]? = some (BitVec.ofNat 64 ((x + y) / B ^ i % B)))
    (hlen : od + 1 + i < B0.length)
    (hu : Γ.get aU = some (BitVec.ofNat 64 (x / B ^ i % B))) (hv : Γ.get aV = some (BitVec.ofNat 64 (y / B ^ i % B)))
    (hc : Γ.get aC = some (BitVec.ofNat 64 (S x y i / B ^ i))) (hq : Γ.get aQo = some (cellA C (od + 1 + i)))
    (hD : aS1 ∈ D ∧ aS ∈ D ∧ aC ∈ D) :
    Step (Inv (σ := σ) (ctxH C (fillI B0 W (od + 1) i)) s Γ [] D) digitP
      (Inv (ctxH C (fillI B0 W (od + 1) (i + 1))) s
        ((aC, BitVec.ofNat 64 (S x y (i + 1) / B ^ (i + 1))) :: (aS, BitVec.ofNat 64 ((x + y) / B ^ i % B)) ::
          (aS1, BitVec.ofNat 64 (x / B ^ i % B) + BitVec.ofNat 64 (y / B ^ i % B)) :: Γ) [] D) := by
  obtain ⟨d1, d2, d3⟩ := hD
  have hdx := Nat.mod_lt (x / B ^ i) Bpos
  have hdy := Nat.mod_lt (y / B ^ i) Bpos
  obtain ⟨wa, wc⟩ := addc_words (x / B ^ i % B) (y / B ^ i % B) (S x y i / B ^ i) hdx hdy (carry_le x y i)
  rw [← sum_digit] at wa
  rw [← carry_succ] at wc
  unfold digitP
  refine step_seq (step_assignI aS1 _ (BitVec.ofNat 64 (x / B ^ i % B) + BitVec.ofNat 64 (y / B ^ i % B)) d1
    (by simp [sev, hu, hv])) ?_
  refine step_seq (step_assignI aS _ (BitVec.ofNat 64 ((x + y) / B ^ i % B)) d2 (by simp [sev, hc]; exact wa)) ?_
  refine step_seq (step_assignI aC _ (BitVec.ofNat 64 (S x y (i + 1) / B ^ (i + 1))) d3
    (by simp [sev, hu, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [← wc, ← wa]; rfl)) ?_
  have hl := fillI_length B0 W (od + 1)
  have hj : od + 1 + i < (ctxH C (fillI B0 W (od + 1) i)).H.length := by
    show od + 1 + i < (fillI B0 W (od + 1) i).length; rw [hl]; exact hlen
  refine step_mono (step_heapStoreI (ctxOK_H hok _) (vv aQo) (vv aS) (od + 1 + i) hj
    (BitVec.ofNat 64 ((x + y) / B ^ i % B))
    (by simp [hq]; rfl) (by simp)) (fun _ h => h) (fun t ht => ?_)
  change Inv (ctxH C ((fillI B0 W (od + 1) i).set (od + 1 + i) (BitVec.ofNat 64 ((x + y) / B ^ i % B)))) s _ [] D t
    at ht
  rw [fillI_succ_eq B0 W (od + 1) i _ hW] at ht
  exact ht

theorem step_heapLoadI' {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (x : MlS) (e : ExpHOL 64) (j : Nat)
    (w : BitVec 64) (hw : C.H[j]? = some w) (hx : x ∈ D) (he : sev Γ e = some (cellA C j)) :
    Step (Inv (σ := σ) C s Γ M D) (.assign .local x (.load .one e)) (Inv C s ((x, w) :: Γ) M D) := by
  obtain ⟨hj, hjw⟩ := List.getElem?_eq_some_iff.mp hw
  have := step_heapLoadI (σ := σ) (C := C) (s := s) (Γ := Γ) (M := M) (D := D) x e j hj hx he
  rw [hjw] at this; exact this

/-- The operand's limb, read through the image the loop has extended above it. -/
theorem fill_limb (B0 W : List (BitVec 64)) (od i oa : Nat) (x : Nat) (hb : BlkAt B0 oa (limbs x))
    (hlo : oa + 1 + (limbs x).length ≤ od + 1) (hk : i < (limbs x).length) :
    (fillI B0 W (od + 1) i)[oa + 1 + i]? = some (BitVec.ofNat 64 (x / B ^ i % B)) := by
  rw [fillI_get?, ite_eq_right (by omega), hb.2 i (by simpa using hk)]
  simp [limbs_getElem x i hk]

def addG1 (Γ0 : Env) (C : Ctx) (od oa ob x y i : Nat) : Env :=
  (aI, BitVec.ofNat 64 i) :: (aC, BitVec.ofNat 64 (S x y i / B ^ i)) :: (aQo, cellA C (od + 1 + i)) ::
    (aQb, cellA C (ob + 1 + i)) :: (aQa, cellA C (oa + 1 + i)) :: Γ0

theorem add_loop1 {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ0 : Env} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x y : Nat) (B0 : List (BitVec 64)) (od oa ob : Nat)
    (hxy : (limbs y).length ≤ (limbs x).length) (hba : BlkAt B0 oa (limbs x)) (hbb : BlkAt B0 ob (limbs y))
    (hla : oa + 1 + (limbs x).length ≤ od + 1) (hlb : ob + 1 + (limbs y).length ≤ od + 1)
    (hdst : od + 1 + ((limbs x).length + 1) ≤ B0.length) (h61 : (limbs x).length < 2 ^ 61)
    (hD : aU ∈ D ∧ aV ∈ D ∧ aS1 ∈ D ∧ aS ∈ D ∧ aC ∈ D ∧ aQa ∈ D ∧ aQb ∈ D ∧ aQo ∈ D ∧ aI ∈ D)
    (hLb : Γ0.get aLb = some (BitVec.ofNat 64 (limbs y).length))
    (hn : Γ0.get aU = none ∧ Γ0.get aV = none ∧ Γ0.get aS1 = none ∧ Γ0.get aS = none)
    (hr : SpecR (Inv (ctxH C (fillI B0 (sumW x y (limbs x).length) (od + 1) (limbs y).length)) s
      (addG1 Γ0 C od oa ob x y (limbs y).length) [] D) rest s m R) :
    SpecR (Inv (ctxH C (fillI B0 (sumW x y (limbs x).length) (od + 1) 0)) s (addG1 Γ0 C od oa ob x y 0) [] D)
      (.seq addLoop1 rest) s m R := by
  obtain ⟨du, dv, d1, d2, dc, dqa, dqb, dqo, di⟩ := hD
  obtain ⟨n1, n2, n3, n4⟩ := hn
  refine specR_forI (σ := σ) (D := D) (M := []) _ _ rest (limbs y).length
    (fun i => ctxH C (fillI B0 (sumW x y (limbs x).length) (od + 1) i)) (addG1 Γ0 C od oa ob x y)
    (fun i hi => ⟨if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 i)
      (BitVec.ofNat 64 (limbs y).length) then 1 else 0, by simp [sev, addG1, Env.get, hLb], ?_⟩) (fun i hi => ?_) hr
  · have e := word_lt_iff i (limbs y).length (by unfold B; omega) (by unfold B; omega)
    by_cases h' : i < (limbs y).length
    · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e.mpr h', h']
    · have : ¬ BitVec.ofNat 64 i < BitVec.ofNat 64 (limbs y).length := fun x => h' (e.mp x)
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this, h']
  refine step_seq (step_heapLoadI' (C := ctxH C _) aU (vv aQa) (oa + 1 + i) _
    (fill_limb B0 _ od i oa x hba hla (by omega)) du (by simp [addG1]; rfl)) ?_
  refine step_seq (step_heapLoadI' (C := ctxH C _) aV (vv aQb) (ob + 1 + i) _
    (fill_limb B0 _ od i ob y hbb hlb hi) dv (by simp [addG1]; rfl)) ?_
  refine step_seq (step_digit hok B0 (sumW x y (limbs x).length) od i x y (sumW_get x y _ i (by omega))
    (by omega) (by simp) (by simp) (by simp [addG1]) (by simp [addG1]) ⟨d1, d2, dc⟩) ?_
  refine step_seq (step_assignI aQa _ (cellA C (oa + 1 + i + 1)) dqa (by simp [sev, addG1]; exact cellA_add8 C _)) ?_
  refine step_seq (step_assignI aQb _ (cellA C (ob + 1 + i + 1)) dqb (by simp [sev, addG1]; exact cellA_add8 C _)) ?_
  refine step_seq (step_assignI aQo _ (cellA C (od + 1 + i + 1)) dqo (by simp [sev, addG1]; exact cellA_add8 C _)) ?_
  refine step_mono (step_assignI aI _ (BitVec.ofNat 64 (i + 1)) di (by simp [sev, addG1]; exact word_add1_eq i))
    (fun _ h => h) (fun t ht => inv_envMono ht (fun z v hz => ?_))
  simp only [addG1, Env.get_cons] at hz ⊢
  by_cases e1 : z = aI
  · subst e1; simp_all
  by_cases e2 : z = aC
  · subst e2; simp_all
  by_cases e3 : z = aQo
  · subst e3; simp_all [Nat.add_assoc]
  by_cases e4 : z = aQb
  · subst e4; simp_all [Nat.add_assoc]
  by_cases e5 : z = aQa
  · subst e5; simp_all [Nat.add_assoc]
  simp only [e1, e2, e3, e4, e5, ite_false] at hz
  have f1 : z ≠ aU := by intro e; subst e; rw [n1] at hz; simp at hz
  have f2 : z ≠ aV := by intro e; subst e; rw [n2] at hz; simp at hz
  have f3 : z ≠ aS1 := by intro e; subst e; rw [n3] at hz; simp at hz
  have f4 : z ≠ aS := by intro e; subst e; rw [n4] at hz; simp at hz
  simp [e1, e2, e3, e4, e5, f1, f2, f3, f4, hz]

def addG2 (Γ1 : Env) (C : Ctx) (od oa x y ly i : Nat) : Env :=
  (aI, BitVec.ofNat 64 (ly + i)) :: (aC, BitVec.ofNat 64 (S x y (ly + i) / B ^ (ly + i))) ::
    (aQo, cellA C (od + 1 + (ly + i))) :: (aQa, cellA C (oa + 1 + (ly + i))) :: Γ1

theorem digit_zero (y k : Nat) (hy : y < B ^ (limbs y).length) (hk : (limbs y).length ≤ k) :
    BitVec.ofNat 64 0 = BitVec.ofNat 64 (y / B ^ k % B) := by
  have : y / B ^ k = 0 := Nat.div_eq_of_lt (Nat.lt_of_lt_of_le hy (Nat.pow_le_pow_right Bpos hk))
  rw [this]; rfl

theorem add_loop2 {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ1 : Env} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x y : Nat) (B0 : List (BitVec 64)) (od oa : Nat)
    (hxy : (limbs y).length ≤ (limbs x).length) (hba : BlkAt B0 oa (limbs x))
    (hla : oa + 1 + (limbs x).length ≤ od + 1)
    (hdst : od + 1 + ((limbs x).length + 1) ≤ B0.length) (h61 : (limbs x).length < 2 ^ 61)
    (hD : aU ∈ D ∧ aV ∈ D ∧ aS1 ∈ D ∧ aS ∈ D ∧ aC ∈ D ∧ aQa ∈ D ∧ aQo ∈ D ∧ aI ∈ D)
    (hLa : Γ1.get aLa = some (BitVec.ofNat 64 (limbs x).length))
    (hn : Γ1.get aU = none ∧ Γ1.get aV = none ∧ Γ1.get aS1 = none ∧ Γ1.get aS = none)
    (hr : SpecR (Inv (ctxH C (fillI B0 (sumW x y (limbs x).length) (od + 1) (limbs x).length)) s
      (addG2 Γ1 C od oa x y (limbs y).length ((limbs x).length - (limbs y).length)) [] D) rest s m R) :
    SpecR (Inv (ctxH C (fillI B0 (sumW x y (limbs x).length) (od + 1) (limbs y).length)) s
      (addG2 Γ1 C od oa x y (limbs y).length 0) [] D) (.seq addLoop2 rest) s m R := by
  obtain ⟨du, dv, d1, d2, dc, dqa, dqo, di⟩ := hD
  obtain ⟨n1, n2, n3, n4⟩ := hn
  have hyB : y < B ^ (limbs y).length := (limbs_length_lt_iff y _).mp (Nat.le_refl _)
  have hk := Nat.add_sub_cancel' hxy
  refine specR_forI (σ := σ) (D := D) (M := []) _ _ rest ((limbs x).length - (limbs y).length)
    (fun i => ctxH C (fillI B0 (sumW x y (limbs x).length) (od + 1) ((limbs y).length + i)))
    (addG2 Γ1 C od oa x y (limbs y).length)
    (fun i hi => ⟨if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 ((limbs y).length + i))
      (BitVec.ofNat 64 (limbs x).length) then 1 else 0, by simp [sev, addG2, Env.get, hLa], ?_⟩) (fun i hi => ?_)
    (by rw [hk]; exact hr)
  · have e := word_lt_iff ((limbs y).length + i) (limbs x).length (by unfold B; omega) (by unfold B; omega)
    by_cases h' : (limbs y).length + i < (limbs x).length
    · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e.mpr h', show i < (limbs x).length - (limbs y).length by omega]
    · have : ¬ BitVec.ofNat 64 ((limbs y).length + i) < BitVec.ofNat 64 (limbs x).length := fun x => h' (e.mp x)
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this, show ¬ i < (limbs x).length - (limbs y).length by omega]
  · refine step_seq (step_heapLoadI' (C := ctxH C _) aU (vv aQa) (oa + 1 + ((limbs y).length + i)) _
      (fill_limb B0 _ od _ oa x hba hla (by omega)) du (by simp [addG2]; rfl)) ?_
    refine step_seq (step_assignI aV (.const 0) (BitVec.ofNat 64 0) dv rfl) ?_
    rw [digit_zero y ((limbs y).length + i) hyB (by omega)]
    refine step_seq (step_digit hok B0 (sumW x y (limbs x).length) od _ x y (sumW_get x y _ _ (by omega))
      (by omega) (by simp) (by simp) (by simp [addG2]) (by simp [addG2]) ⟨d1, d2, dc⟩) ?_
    refine step_seq (step_assignI aQa _ (cellA C (oa + 1 + ((limbs y).length + i) + 1)) dqa
      (by simp [sev, addG2]; exact cellA_add8 C _)) ?_
    refine step_seq (step_assignI aQo _ (cellA C (od + 1 + ((limbs y).length + i) + 1)) dqo
      (by simp [sev, addG2]; exact cellA_add8 C _)) ?_
    refine step_mono (step_assignI aI _ (BitVec.ofNat 64 ((limbs y).length + i + 1)) di
      (by simp [sev, addG2]; exact word_add1_eq _)) (fun _ h => h) (fun t ht => ?_)
    rw [show (limbs y).length + (i + 1) = (limbs y).length + i + 1 by omega]
    refine inv_envMono ht (fun z v hz => ?_)
    simp only [addG2, Env.get_cons] at hz ⊢
    rw [show (limbs y).length + (i + 1) = (limbs y).length + i + 1 by omega] at hz
    by_cases e1 : z = aI
    · subst e1; simp_all
    by_cases e2 : z = aC
    · subst e2; simp_all
    by_cases e3 : z = aQo
    · subst e3; simp_all [Nat.add_assoc]
    by_cases e5 : z = aQa
    · subst e5; simp_all [Nat.add_assoc]
    simp only [e1, e2, e3, e5, ite_false] at hz
    have f1 : z ≠ aU := by intro e; subst e; rw [n1] at hz; simp at hz
    have f2 : z ≠ aV := by intro e; subst e; rw [n2] at hz; simp at hz
    have f3 : z ≠ aS1 := by intro e; subst e; rw [n3] at hz; simp at hz
    have f4 : z ≠ aS := by intro e; subst e; rw [n4] at hz; simp at hz
    simp [e1, e2, e3, e5, f1, f2, f3, f4, hz]

theorem add_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ addLocals → (ctxEnv C ++ addParams.zip vals).get x = none :=
  Knot.params_none C addLocals addParams vals (by decide) (by decide)

theorem add_spec (C : Ctx) (hok : CtxOK C) (s : AState) (x y : Nat) (oa ob : Nat)
    (hba : BlkAt C.H oa (limbs x)) (hbb : BlkAt C.H ob (limbs y)) (hxy : (limbs y).length ≤ (limbs x).length)
    (h61 : (limbs x).length < 2 ^ 60) :
    SpecR (σ := σ) (Pre C s (addParams.zip [cellA C oa, cellA C ob])) (addBody C) s (pure (x + y) : AM Nat)
      (PostH C s) := by
  refine specR_prologue (postH_locals C s) (add_none C _) ?_
  unfold addCore
  have hla0 : C.H[oa]? = some (BitVec.ofNat 64 (limbs x).length) := by simpa using hba.1
  have hlb0 : C.H[ob]? = some (BitVec.ofNat 64 (limbs y).length) := by simpa using hbb.1
  refine UD.specR_heapLoadI' aLa (vv aX) oa _ hla0 (by decide) (by simp +decide [Env.get, addParams, ctxEnv]) ?_
  refine UD.specR_heapLoadI' aLb (vv aY) ob _ hlb0 (by decide) (by simp +decide [Env.get, addParams, ctxEnv]) ?_
  refine specR_allocI aO (.panop .mul [.op .add [vv aLa, .const 2], .const 8]) ((limbs x).length + 2) (by omega)
    (by decide) (fun v => by
      simp [sev, Env.get]
      rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, BitVec.ofNat_add_ofNat]; exact CV.mul8_eq _)
    (fun H' wsN hpre hwl hcap => ?_)
  have hbl := blkAt_len hba
  have hbl2 := blkAt_len hbb
  have hpl := hpre.length_le
  let B0 := H' ++ wsN
  have hB0 : B0.length = H'.length + ((limbs x).length + 2) := by simp [B0, hwl]
  have hba' : BlkAt B0 oa (limbs x) := blkAt_mono hba (hpre.trans (List.prefix_append _ _))
  have hbb' : BlkAt B0 ob (limbs y) := blkAt_mono hbb (hpre.trans (List.prefix_append _ _))
  refine specR_assignI aQa _ (cellA C (oa + 1)) (by decide) (by simp [sev, Env.get, addParams, ctxEnv]; exact cellA_add8 C _) ?_
  refine specR_assignI aQb _ (cellA C (ob + 1)) (by decide) (by simp [sev, Env.get, addParams, ctxEnv]; exact cellA_add8 C _) ?_
  refine specR_assignI aQo _ (cellA C (H'.length + 1)) (by decide) (by simp [sev, Env.get]; exact cellA_add8 C _) ?_
  refine specR_assignI aC (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
  refine specR_assignI aI (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
  let Γ0 : Env := [(aLa, BitVec.ofNat 64 (limbs x).length), (aLb, BitVec.ofNat 64 (limbs y).length),
    (aO, cellA C H'.length)]
  refine specR_envWeak (Γb := addG1 Γ0 C H'.length oa ob x y 0) (fun z v hz => ?_) ?_
  · simp only [addG1, Γ0, Env.get_cons, S_zero, Nat.zero_div, Nat.add_zero] at hz ⊢
    by_cases e1 : z = aI
    · subst e1; simpa using hz
    by_cases e2 : z = aC
    · subst e2; simpa using hz
    by_cases e3 : z = aQo
    · subst e3; simpa using hz
    by_cases e4 : z = aQb
    · subst e4; simpa using hz
    by_cases e5 : z = aQa
    · subst e5; simpa using hz
    by_cases e6 : z = aLa
    · subst e6; simpa using hz
    by_cases e7 : z = aLb
    · subst e7; simpa using hz
    by_cases e8 : z = aO
    · subst e8; simpa using hz
    simp [e1, e2, e3, e4, e5, e6, e7, e8, Env.get] at hz
  refine add_loop1 hok x y B0 H'.length oa ob hxy hba' hbb' (by omega) (by omega) (by rw [hB0]; omega) (by omega)
    (by decide) (by simp [Γ0]) (by simp [Γ0, Env.get]) ?_
  refine specR_envWeak (Γb := addG2 Γ0 C H'.length oa x y (limbs y).length 0) (fun z v hz => ?_) ?_
  · simp only [addG1, addG2, Env.get_cons, Nat.add_zero] at hz ⊢
    by_cases e1 : z = aI
    · subst e1; simpa using hz
    by_cases e2 : z = aC
    · subst e2; simpa using hz
    by_cases e3 : z = aQo
    · subst e3; simpa using hz
    by_cases e5 : z = aQa
    · subst e5; simpa using hz
    have e4 : z ≠ aQb := by intro e; subst e; simp [Γ0, Env.get] at hz
    simp [e1, e2, e3, e4, e5] at hz ⊢; exact hz
  refine add_loop2 hok x y B0 H'.length oa hxy hba' (by omega) (by rw [hB0]; omega) (by omega) (by decide)
    (by simp [Γ0]) (by simp [Γ0, Env.get]) ?_
  have hly : (limbs y).length + ((limbs x).length - (limbs y).length) = (limbs x).length := by omega
  -- the top digit and the length
  have hxB : x < B ^ (limbs x).length := (limbs_length_lt_iff x _).mp (Nat.le_refl _)
  have hyB : y < B ^ (limbs x).length :=
    Nat.lt_of_lt_of_le ((limbs_length_lt_iff y _).mp (Nat.le_refl _)) (Nat.pow_le_pow_right Bpos hxy)
  have hSf := S_full x y _ hxB hyB
  have hcl := carry_le x y (limbs x).length
  generalize hc : S x y (limbs x).length / B ^ (limbs x).length = c at hcl
  have hcd : (x + y) / B ^ (limbs x).length = c := by rw [← hSf]; exact hc
  have hW : (sumW x y (limbs x).length)[(limbs x).length]? = some (BitVec.ofNat 64 c) := by
    rw [sumW_get x y _ _ (by omega), hcd, Nat.mod_eq_of_lt (by unfold B; omega)]
  have hl := fillI_length B0 (sumW x y (limbs x).length) (H'.length + 1)
  have hj1 : H'.length + 1 + (limbs x).length <
      (ctxH C (fillI B0 (sumW x y (limbs x).length) (H'.length + 1) (limbs x).length)).H.length := by
    show _ < (fillI _ _ _ _).length; rw [hl, hB0]; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv aQo) (vv aC) _ hj1 (BitVec.ofNat 64 c) (by simp [addG2, hly]; rfl)
    (by simp [addG2, hly, hc]) ?_
  change SpecR (Inv (ctxH C ((fillI B0 (sumW x y (limbs x).length) (H'.length + 1) (limbs x).length).set
    (H'.length + 1 + (limbs x).length) (BitVec.ofNat 64 c))) s _ [] _) _ _ _ _
  rw [fillI_succ_eq _ _ _ _ _ hW]
  have hl2 := fillI_length B0 (sumW x y (limbs x).length) (H'.length + 1)
  have hj2 : H'.length <
      (ctxH C (fillI B0 (sumW x y (limbs x).length) (H'.length + 1) ((limbs x).length + 1))).H.length := by
    show _ < (fillI _ _ _ _).length; rw [hl2, hB0]; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv aO) _ _ hj2 (BitVec.ofNat 64 ((limbs x).length + c))
    (by simp [addG2, Γ0]; rfl) (by simp [sev, addG2, Γ0]; rw [BitVec.ofNat_add_ofNat, hly, hc]) ?_
  refine specR_returnI _ (cellA C H'.length) (by simp [addG2, Γ0]) (fun t ht => ?_)
  refine ⟨_, H'.length, ?_, rfl, ?_, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
  · exact prefix_set_ge (CV.prefix_fillI _ _ _ C.H (by omega) (hpre.trans (List.prefix_append _ _)) _) _ hpl _
  · have hfin := add_final x y hyB
    rw [hc] at hfin
    rw [hfin]
    have hl3 := fillI_length B0 (sumW x y (limbs x).length) (H'.length + 1)
    constructor
    · rw [List.getElem?_set_self (by show H'.length < (fillI _ _ _ _).length; rw [hl3, hB0]; omega)]
      simp
    · intro i hi
      simp only [List.length_map, List.length_range] at hi
      rw [List.getElem?_set_ne (by omega)]
      show (fillI B0 (sumW x y (limbs x).length) (H'.length + 1) ((limbs x).length + 1))[H'.length + 1 + i]? = _
      rw [fillI_get?, ite_eq_left ⟨by omega, by omega, by rw [hB0]; omega⟩]
      simp [show H'.length + 1 + i - (H'.length + 1) = i by omega, List.getD_eq_getElem?_getD,
        sumW_get x y (limbs x).length i (by omega)]

end

end ConPanqueque.T.Big
