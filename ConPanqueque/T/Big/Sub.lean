import ConPanqueque.T.Big.Add
import ConPanqueque.T.Big.SubMath
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Subtracting `Nat`s (for `y ≤ x`)

`subCore(x, y)` writes the digits of `x - y` with a borrow loop over the shared limbs and one over the rest
of `x`, then scans the digits (a counted loop, branch-free) for the canonical length.
-/

namespace ConPanqueque.T.Big

open ConPanqueque.T ConPanqueque.T.Ex
open ConPanqueque.V.Enc

def sX := ofString "sx"
def sY := ofString "sy"
def sLa := ofString "sla"
def sLb := ofString "slb"
def sO := ofString "so"
def sQa := ofString "sqa"
def sQb := ofString "sqb"
def sQo := ofString "sqo"
def sU := ofString "su"
def sV := ofString "sv"
def sD1 := ofString "sd1"
def sD := ofString "sd"
def sB := ofString "sb"
def sI := ofString "si"
def sK := ofString "sk"
def sL := ofString "sl"

@[simp] theorem sX_ne_sY : sX ≠ sY := by decide
@[simp] theorem sX_ne_sLa : sX ≠ sLa := by decide
@[simp] theorem sX_ne_sLb : sX ≠ sLb := by decide
@[simp] theorem sX_ne_sO : sX ≠ sO := by decide
@[simp] theorem sX_ne_sQa : sX ≠ sQa := by decide
@[simp] theorem sX_ne_sQb : sX ≠ sQb := by decide
@[simp] theorem sX_ne_sQo : sX ≠ sQo := by decide
@[simp] theorem sX_ne_sU : sX ≠ sU := by decide
@[simp] theorem sX_ne_sV : sX ≠ sV := by decide
@[simp] theorem sX_ne_sD1 : sX ≠ sD1 := by decide
@[simp] theorem sX_ne_sD : sX ≠ sD := by decide
@[simp] theorem sX_ne_sB : sX ≠ sB := by decide
@[simp] theorem sX_ne_sI : sX ≠ sI := by decide
@[simp] theorem sX_ne_sK : sX ≠ sK := by decide
@[simp] theorem sX_ne_sL : sX ≠ sL := by decide
@[simp] theorem sY_ne_sX : sY ≠ sX := by decide
@[simp] theorem sY_ne_sLa : sY ≠ sLa := by decide
@[simp] theorem sY_ne_sLb : sY ≠ sLb := by decide
@[simp] theorem sY_ne_sO : sY ≠ sO := by decide
@[simp] theorem sY_ne_sQa : sY ≠ sQa := by decide
@[simp] theorem sY_ne_sQb : sY ≠ sQb := by decide
@[simp] theorem sY_ne_sQo : sY ≠ sQo := by decide
@[simp] theorem sY_ne_sU : sY ≠ sU := by decide
@[simp] theorem sY_ne_sV : sY ≠ sV := by decide
@[simp] theorem sY_ne_sD1 : sY ≠ sD1 := by decide
@[simp] theorem sY_ne_sD : sY ≠ sD := by decide
@[simp] theorem sY_ne_sB : sY ≠ sB := by decide
@[simp] theorem sY_ne_sI : sY ≠ sI := by decide
@[simp] theorem sY_ne_sK : sY ≠ sK := by decide
@[simp] theorem sY_ne_sL : sY ≠ sL := by decide
@[simp] theorem sLa_ne_sX : sLa ≠ sX := by decide
@[simp] theorem sLa_ne_sY : sLa ≠ sY := by decide
@[simp] theorem sLa_ne_sLb : sLa ≠ sLb := by decide
@[simp] theorem sLa_ne_sO : sLa ≠ sO := by decide
@[simp] theorem sLa_ne_sQa : sLa ≠ sQa := by decide
@[simp] theorem sLa_ne_sQb : sLa ≠ sQb := by decide
@[simp] theorem sLa_ne_sQo : sLa ≠ sQo := by decide
@[simp] theorem sLa_ne_sU : sLa ≠ sU := by decide
@[simp] theorem sLa_ne_sV : sLa ≠ sV := by decide
@[simp] theorem sLa_ne_sD1 : sLa ≠ sD1 := by decide
@[simp] theorem sLa_ne_sD : sLa ≠ sD := by decide
@[simp] theorem sLa_ne_sB : sLa ≠ sB := by decide
@[simp] theorem sLa_ne_sI : sLa ≠ sI := by decide
@[simp] theorem sLa_ne_sK : sLa ≠ sK := by decide
@[simp] theorem sLa_ne_sL : sLa ≠ sL := by decide
@[simp] theorem sLb_ne_sX : sLb ≠ sX := by decide
@[simp] theorem sLb_ne_sY : sLb ≠ sY := by decide
@[simp] theorem sLb_ne_sLa : sLb ≠ sLa := by decide
@[simp] theorem sLb_ne_sO : sLb ≠ sO := by decide
@[simp] theorem sLb_ne_sQa : sLb ≠ sQa := by decide
@[simp] theorem sLb_ne_sQb : sLb ≠ sQb := by decide
@[simp] theorem sLb_ne_sQo : sLb ≠ sQo := by decide
@[simp] theorem sLb_ne_sU : sLb ≠ sU := by decide
@[simp] theorem sLb_ne_sV : sLb ≠ sV := by decide
@[simp] theorem sLb_ne_sD1 : sLb ≠ sD1 := by decide
@[simp] theorem sLb_ne_sD : sLb ≠ sD := by decide
@[simp] theorem sLb_ne_sB : sLb ≠ sB := by decide
@[simp] theorem sLb_ne_sI : sLb ≠ sI := by decide
@[simp] theorem sLb_ne_sK : sLb ≠ sK := by decide
@[simp] theorem sLb_ne_sL : sLb ≠ sL := by decide
@[simp] theorem sO_ne_sX : sO ≠ sX := by decide
@[simp] theorem sO_ne_sY : sO ≠ sY := by decide
@[simp] theorem sO_ne_sLa : sO ≠ sLa := by decide
@[simp] theorem sO_ne_sLb : sO ≠ sLb := by decide
@[simp] theorem sO_ne_sQa : sO ≠ sQa := by decide
@[simp] theorem sO_ne_sQb : sO ≠ sQb := by decide
@[simp] theorem sO_ne_sQo : sO ≠ sQo := by decide
@[simp] theorem sO_ne_sU : sO ≠ sU := by decide
@[simp] theorem sO_ne_sV : sO ≠ sV := by decide
@[simp] theorem sO_ne_sD1 : sO ≠ sD1 := by decide
@[simp] theorem sO_ne_sD : sO ≠ sD := by decide
@[simp] theorem sO_ne_sB : sO ≠ sB := by decide
@[simp] theorem sO_ne_sI : sO ≠ sI := by decide
@[simp] theorem sO_ne_sK : sO ≠ sK := by decide
@[simp] theorem sO_ne_sL : sO ≠ sL := by decide
@[simp] theorem sQa_ne_sX : sQa ≠ sX := by decide
@[simp] theorem sQa_ne_sY : sQa ≠ sY := by decide
@[simp] theorem sQa_ne_sLa : sQa ≠ sLa := by decide
@[simp] theorem sQa_ne_sLb : sQa ≠ sLb := by decide
@[simp] theorem sQa_ne_sO : sQa ≠ sO := by decide
@[simp] theorem sQa_ne_sQb : sQa ≠ sQb := by decide
@[simp] theorem sQa_ne_sQo : sQa ≠ sQo := by decide
@[simp] theorem sQa_ne_sU : sQa ≠ sU := by decide
@[simp] theorem sQa_ne_sV : sQa ≠ sV := by decide
@[simp] theorem sQa_ne_sD1 : sQa ≠ sD1 := by decide
@[simp] theorem sQa_ne_sD : sQa ≠ sD := by decide
@[simp] theorem sQa_ne_sB : sQa ≠ sB := by decide
@[simp] theorem sQa_ne_sI : sQa ≠ sI := by decide
@[simp] theorem sQa_ne_sK : sQa ≠ sK := by decide
@[simp] theorem sQa_ne_sL : sQa ≠ sL := by decide
@[simp] theorem sQb_ne_sX : sQb ≠ sX := by decide
@[simp] theorem sQb_ne_sY : sQb ≠ sY := by decide
@[simp] theorem sQb_ne_sLa : sQb ≠ sLa := by decide
@[simp] theorem sQb_ne_sLb : sQb ≠ sLb := by decide
@[simp] theorem sQb_ne_sO : sQb ≠ sO := by decide
@[simp] theorem sQb_ne_sQa : sQb ≠ sQa := by decide
@[simp] theorem sQb_ne_sQo : sQb ≠ sQo := by decide
@[simp] theorem sQb_ne_sU : sQb ≠ sU := by decide
@[simp] theorem sQb_ne_sV : sQb ≠ sV := by decide
@[simp] theorem sQb_ne_sD1 : sQb ≠ sD1 := by decide
@[simp] theorem sQb_ne_sD : sQb ≠ sD := by decide
@[simp] theorem sQb_ne_sB : sQb ≠ sB := by decide
@[simp] theorem sQb_ne_sI : sQb ≠ sI := by decide
@[simp] theorem sQb_ne_sK : sQb ≠ sK := by decide
@[simp] theorem sQb_ne_sL : sQb ≠ sL := by decide
@[simp] theorem sQo_ne_sX : sQo ≠ sX := by decide
@[simp] theorem sQo_ne_sY : sQo ≠ sY := by decide
@[simp] theorem sQo_ne_sLa : sQo ≠ sLa := by decide
@[simp] theorem sQo_ne_sLb : sQo ≠ sLb := by decide
@[simp] theorem sQo_ne_sO : sQo ≠ sO := by decide
@[simp] theorem sQo_ne_sQa : sQo ≠ sQa := by decide
@[simp] theorem sQo_ne_sQb : sQo ≠ sQb := by decide
@[simp] theorem sQo_ne_sU : sQo ≠ sU := by decide
@[simp] theorem sQo_ne_sV : sQo ≠ sV := by decide
@[simp] theorem sQo_ne_sD1 : sQo ≠ sD1 := by decide
@[simp] theorem sQo_ne_sD : sQo ≠ sD := by decide
@[simp] theorem sQo_ne_sB : sQo ≠ sB := by decide
@[simp] theorem sQo_ne_sI : sQo ≠ sI := by decide
@[simp] theorem sQo_ne_sK : sQo ≠ sK := by decide
@[simp] theorem sQo_ne_sL : sQo ≠ sL := by decide
@[simp] theorem sU_ne_sX : sU ≠ sX := by decide
@[simp] theorem sU_ne_sY : sU ≠ sY := by decide
@[simp] theorem sU_ne_sLa : sU ≠ sLa := by decide
@[simp] theorem sU_ne_sLb : sU ≠ sLb := by decide
@[simp] theorem sU_ne_sO : sU ≠ sO := by decide
@[simp] theorem sU_ne_sQa : sU ≠ sQa := by decide
@[simp] theorem sU_ne_sQb : sU ≠ sQb := by decide
@[simp] theorem sU_ne_sQo : sU ≠ sQo := by decide
@[simp] theorem sU_ne_sV : sU ≠ sV := by decide
@[simp] theorem sU_ne_sD1 : sU ≠ sD1 := by decide
@[simp] theorem sU_ne_sD : sU ≠ sD := by decide
@[simp] theorem sU_ne_sB : sU ≠ sB := by decide
@[simp] theorem sU_ne_sI : sU ≠ sI := by decide
@[simp] theorem sU_ne_sK : sU ≠ sK := by decide
@[simp] theorem sU_ne_sL : sU ≠ sL := by decide
@[simp] theorem sV_ne_sX : sV ≠ sX := by decide
@[simp] theorem sV_ne_sY : sV ≠ sY := by decide
@[simp] theorem sV_ne_sLa : sV ≠ sLa := by decide
@[simp] theorem sV_ne_sLb : sV ≠ sLb := by decide
@[simp] theorem sV_ne_sO : sV ≠ sO := by decide
@[simp] theorem sV_ne_sQa : sV ≠ sQa := by decide
@[simp] theorem sV_ne_sQb : sV ≠ sQb := by decide
@[simp] theorem sV_ne_sQo : sV ≠ sQo := by decide
@[simp] theorem sV_ne_sU : sV ≠ sU := by decide
@[simp] theorem sV_ne_sD1 : sV ≠ sD1 := by decide
@[simp] theorem sV_ne_sD : sV ≠ sD := by decide
@[simp] theorem sV_ne_sB : sV ≠ sB := by decide
@[simp] theorem sV_ne_sI : sV ≠ sI := by decide
@[simp] theorem sV_ne_sK : sV ≠ sK := by decide
@[simp] theorem sV_ne_sL : sV ≠ sL := by decide
@[simp] theorem sD1_ne_sX : sD1 ≠ sX := by decide
@[simp] theorem sD1_ne_sY : sD1 ≠ sY := by decide
@[simp] theorem sD1_ne_sLa : sD1 ≠ sLa := by decide
@[simp] theorem sD1_ne_sLb : sD1 ≠ sLb := by decide
@[simp] theorem sD1_ne_sO : sD1 ≠ sO := by decide
@[simp] theorem sD1_ne_sQa : sD1 ≠ sQa := by decide
@[simp] theorem sD1_ne_sQb : sD1 ≠ sQb := by decide
@[simp] theorem sD1_ne_sQo : sD1 ≠ sQo := by decide
@[simp] theorem sD1_ne_sU : sD1 ≠ sU := by decide
@[simp] theorem sD1_ne_sV : sD1 ≠ sV := by decide
@[simp] theorem sD1_ne_sD : sD1 ≠ sD := by decide
@[simp] theorem sD1_ne_sB : sD1 ≠ sB := by decide
@[simp] theorem sD1_ne_sI : sD1 ≠ sI := by decide
@[simp] theorem sD1_ne_sK : sD1 ≠ sK := by decide
@[simp] theorem sD1_ne_sL : sD1 ≠ sL := by decide
@[simp] theorem sD_ne_sX : sD ≠ sX := by decide
@[simp] theorem sD_ne_sY : sD ≠ sY := by decide
@[simp] theorem sD_ne_sLa : sD ≠ sLa := by decide
@[simp] theorem sD_ne_sLb : sD ≠ sLb := by decide
@[simp] theorem sD_ne_sO : sD ≠ sO := by decide
@[simp] theorem sD_ne_sQa : sD ≠ sQa := by decide
@[simp] theorem sD_ne_sQb : sD ≠ sQb := by decide
@[simp] theorem sD_ne_sQo : sD ≠ sQo := by decide
@[simp] theorem sD_ne_sU : sD ≠ sU := by decide
@[simp] theorem sD_ne_sV : sD ≠ sV := by decide
@[simp] theorem sD_ne_sD1 : sD ≠ sD1 := by decide
@[simp] theorem sD_ne_sB : sD ≠ sB := by decide
@[simp] theorem sD_ne_sI : sD ≠ sI := by decide
@[simp] theorem sD_ne_sK : sD ≠ sK := by decide
@[simp] theorem sD_ne_sL : sD ≠ sL := by decide
@[simp] theorem sB_ne_sX : sB ≠ sX := by decide
@[simp] theorem sB_ne_sY : sB ≠ sY := by decide
@[simp] theorem sB_ne_sLa : sB ≠ sLa := by decide
@[simp] theorem sB_ne_sLb : sB ≠ sLb := by decide
@[simp] theorem sB_ne_sO : sB ≠ sO := by decide
@[simp] theorem sB_ne_sQa : sB ≠ sQa := by decide
@[simp] theorem sB_ne_sQb : sB ≠ sQb := by decide
@[simp] theorem sB_ne_sQo : sB ≠ sQo := by decide
@[simp] theorem sB_ne_sU : sB ≠ sU := by decide
@[simp] theorem sB_ne_sV : sB ≠ sV := by decide
@[simp] theorem sB_ne_sD1 : sB ≠ sD1 := by decide
@[simp] theorem sB_ne_sD : sB ≠ sD := by decide
@[simp] theorem sB_ne_sI : sB ≠ sI := by decide
@[simp] theorem sB_ne_sK : sB ≠ sK := by decide
@[simp] theorem sB_ne_sL : sB ≠ sL := by decide
@[simp] theorem sI_ne_sX : sI ≠ sX := by decide
@[simp] theorem sI_ne_sY : sI ≠ sY := by decide
@[simp] theorem sI_ne_sLa : sI ≠ sLa := by decide
@[simp] theorem sI_ne_sLb : sI ≠ sLb := by decide
@[simp] theorem sI_ne_sO : sI ≠ sO := by decide
@[simp] theorem sI_ne_sQa : sI ≠ sQa := by decide
@[simp] theorem sI_ne_sQb : sI ≠ sQb := by decide
@[simp] theorem sI_ne_sQo : sI ≠ sQo := by decide
@[simp] theorem sI_ne_sU : sI ≠ sU := by decide
@[simp] theorem sI_ne_sV : sI ≠ sV := by decide
@[simp] theorem sI_ne_sD1 : sI ≠ sD1 := by decide
@[simp] theorem sI_ne_sD : sI ≠ sD := by decide
@[simp] theorem sI_ne_sB : sI ≠ sB := by decide
@[simp] theorem sI_ne_sK : sI ≠ sK := by decide
@[simp] theorem sI_ne_sL : sI ≠ sL := by decide
@[simp] theorem sK_ne_sX : sK ≠ sX := by decide
@[simp] theorem sK_ne_sY : sK ≠ sY := by decide
@[simp] theorem sK_ne_sLa : sK ≠ sLa := by decide
@[simp] theorem sK_ne_sLb : sK ≠ sLb := by decide
@[simp] theorem sK_ne_sO : sK ≠ sO := by decide
@[simp] theorem sK_ne_sQa : sK ≠ sQa := by decide
@[simp] theorem sK_ne_sQb : sK ≠ sQb := by decide
@[simp] theorem sK_ne_sQo : sK ≠ sQo := by decide
@[simp] theorem sK_ne_sU : sK ≠ sU := by decide
@[simp] theorem sK_ne_sV : sK ≠ sV := by decide
@[simp] theorem sK_ne_sD1 : sK ≠ sD1 := by decide
@[simp] theorem sK_ne_sD : sK ≠ sD := by decide
@[simp] theorem sK_ne_sB : sK ≠ sB := by decide
@[simp] theorem sK_ne_sI : sK ≠ sI := by decide
@[simp] theorem sK_ne_sL : sK ≠ sL := by decide
@[simp] theorem sL_ne_sX : sL ≠ sX := by decide
@[simp] theorem sL_ne_sY : sL ≠ sY := by decide
@[simp] theorem sL_ne_sLa : sL ≠ sLa := by decide
@[simp] theorem sL_ne_sLb : sL ≠ sLb := by decide
@[simp] theorem sL_ne_sO : sL ≠ sO := by decide
@[simp] theorem sL_ne_sQa : sL ≠ sQa := by decide
@[simp] theorem sL_ne_sQb : sL ≠ sQb := by decide
@[simp] theorem sL_ne_sQo : sL ≠ sQo := by decide
@[simp] theorem sL_ne_sU : sL ≠ sU := by decide
@[simp] theorem sL_ne_sV : sL ≠ sV := by decide
@[simp] theorem sL_ne_sD1 : sL ≠ sD1 := by decide
@[simp] theorem sL_ne_sD : sL ≠ sD := by decide
@[simp] theorem sL_ne_sB : sL ≠ sB := by decide
@[simp] theorem sL_ne_sI : sL ≠ sI := by decide
@[simp] theorem sL_ne_sK : sL ≠ sK := by decide
@[simp] theorem sX_ne_lFl : sX ≠ lFl := by decide
@[simp] theorem lFl_ne_sX : lFl ≠ sX := by decide
@[simp] theorem sX_ne_lDh : sX ≠ lDh := by decide
@[simp] theorem lDh_ne_sX : lDh ≠ sX := by decide
@[simp] theorem sX_ne_lDt : sX ≠ lDt := by decide
@[simp] theorem lDt_ne_sX : lDt ≠ sX := by decide
@[simp] theorem sX_ne_lDg : sX ≠ lDg := by decide
@[simp] theorem lDg_ne_sX : lDg ≠ sX := by decide
@[simp] theorem sX_ne_lDi : sX ≠ lDi := by decide
@[simp] theorem lDi_ne_sX : lDi ≠ sX := by decide
@[simp] theorem sX_ne_lRp : sX ≠ lRp := by decide
@[simp] theorem lRp_ne_sX : lRp ≠ sX := by decide
@[simp] theorem sX_ne_lRn : sX ≠ lRn := by decide
@[simp] theorem lRn_ne_sX : lRn ≠ sX := by decide
@[simp] theorem sX_ne_lFle : sX ≠ lFle := by decide
@[simp] theorem lFle_ne_sX : lFle ≠ sX := by decide
@[simp] theorem sX_ne_lDir : sX ≠ lDir := by decide
@[simp] theorem lDir_ne_sX : lDir ≠ sX := by decide
@[simp] theorem sX_ne_lFln : sX ≠ lFln := by decide
@[simp] theorem lFln_ne_sX : lFln ≠ sX := by decide
@[simp] theorem sX_ne_lFll : sX ≠ lFll := by decide
@[simp] theorem lFll_ne_sX : lFll ≠ sX := by decide
@[simp] theorem sX_ne_lFls : sX ≠ lFls := by decide
@[simp] theorem lFls_ne_sX : lFls ≠ sX := by decide
@[simp] theorem sX_ne_lKb : sX ≠ lKb := by decide
@[simp] theorem lKb_ne_sX : lKb ≠ sX := by decide
@[simp] theorem sY_ne_lFl : sY ≠ lFl := by decide
@[simp] theorem lFl_ne_sY : lFl ≠ sY := by decide
@[simp] theorem sY_ne_lDh : sY ≠ lDh := by decide
@[simp] theorem lDh_ne_sY : lDh ≠ sY := by decide
@[simp] theorem sY_ne_lDt : sY ≠ lDt := by decide
@[simp] theorem lDt_ne_sY : lDt ≠ sY := by decide
@[simp] theorem sY_ne_lDg : sY ≠ lDg := by decide
@[simp] theorem lDg_ne_sY : lDg ≠ sY := by decide
@[simp] theorem sY_ne_lDi : sY ≠ lDi := by decide
@[simp] theorem lDi_ne_sY : lDi ≠ sY := by decide
@[simp] theorem sY_ne_lRp : sY ≠ lRp := by decide
@[simp] theorem lRp_ne_sY : lRp ≠ sY := by decide
@[simp] theorem sY_ne_lRn : sY ≠ lRn := by decide
@[simp] theorem lRn_ne_sY : lRn ≠ sY := by decide
@[simp] theorem sY_ne_lFle : sY ≠ lFle := by decide
@[simp] theorem lFle_ne_sY : lFle ≠ sY := by decide
@[simp] theorem sY_ne_lDir : sY ≠ lDir := by decide
@[simp] theorem lDir_ne_sY : lDir ≠ sY := by decide
@[simp] theorem sY_ne_lFln : sY ≠ lFln := by decide
@[simp] theorem lFln_ne_sY : lFln ≠ sY := by decide
@[simp] theorem sY_ne_lFll : sY ≠ lFll := by decide
@[simp] theorem lFll_ne_sY : lFll ≠ sY := by decide
@[simp] theorem sY_ne_lFls : sY ≠ lFls := by decide
@[simp] theorem lFls_ne_sY : lFls ≠ sY := by decide
@[simp] theorem sY_ne_lKb : sY ≠ lKb := by decide
@[simp] theorem lKb_ne_sY : lKb ≠ sY := by decide
@[simp] theorem sLa_ne_lFl : sLa ≠ lFl := by decide
@[simp] theorem lFl_ne_sLa : lFl ≠ sLa := by decide
@[simp] theorem sLa_ne_lDh : sLa ≠ lDh := by decide
@[simp] theorem lDh_ne_sLa : lDh ≠ sLa := by decide
@[simp] theorem sLa_ne_lDt : sLa ≠ lDt := by decide
@[simp] theorem lDt_ne_sLa : lDt ≠ sLa := by decide
@[simp] theorem sLa_ne_lDg : sLa ≠ lDg := by decide
@[simp] theorem lDg_ne_sLa : lDg ≠ sLa := by decide
@[simp] theorem sLa_ne_lDi : sLa ≠ lDi := by decide
@[simp] theorem lDi_ne_sLa : lDi ≠ sLa := by decide
@[simp] theorem sLa_ne_lRp : sLa ≠ lRp := by decide
@[simp] theorem lRp_ne_sLa : lRp ≠ sLa := by decide
@[simp] theorem sLa_ne_lRn : sLa ≠ lRn := by decide
@[simp] theorem lRn_ne_sLa : lRn ≠ sLa := by decide
@[simp] theorem sLa_ne_lFle : sLa ≠ lFle := by decide
@[simp] theorem lFle_ne_sLa : lFle ≠ sLa := by decide
@[simp] theorem sLa_ne_lDir : sLa ≠ lDir := by decide
@[simp] theorem lDir_ne_sLa : lDir ≠ sLa := by decide
@[simp] theorem sLa_ne_lFln : sLa ≠ lFln := by decide
@[simp] theorem lFln_ne_sLa : lFln ≠ sLa := by decide
@[simp] theorem sLa_ne_lFll : sLa ≠ lFll := by decide
@[simp] theorem lFll_ne_sLa : lFll ≠ sLa := by decide
@[simp] theorem sLa_ne_lFls : sLa ≠ lFls := by decide
@[simp] theorem lFls_ne_sLa : lFls ≠ sLa := by decide
@[simp] theorem sLa_ne_lKb : sLa ≠ lKb := by decide
@[simp] theorem lKb_ne_sLa : lKb ≠ sLa := by decide
@[simp] theorem sLb_ne_lFl : sLb ≠ lFl := by decide
@[simp] theorem lFl_ne_sLb : lFl ≠ sLb := by decide
@[simp] theorem sLb_ne_lDh : sLb ≠ lDh := by decide
@[simp] theorem lDh_ne_sLb : lDh ≠ sLb := by decide
@[simp] theorem sLb_ne_lDt : sLb ≠ lDt := by decide
@[simp] theorem lDt_ne_sLb : lDt ≠ sLb := by decide
@[simp] theorem sLb_ne_lDg : sLb ≠ lDg := by decide
@[simp] theorem lDg_ne_sLb : lDg ≠ sLb := by decide
@[simp] theorem sLb_ne_lDi : sLb ≠ lDi := by decide
@[simp] theorem lDi_ne_sLb : lDi ≠ sLb := by decide
@[simp] theorem sLb_ne_lRp : sLb ≠ lRp := by decide
@[simp] theorem lRp_ne_sLb : lRp ≠ sLb := by decide
@[simp] theorem sLb_ne_lRn : sLb ≠ lRn := by decide
@[simp] theorem lRn_ne_sLb : lRn ≠ sLb := by decide
@[simp] theorem sLb_ne_lFle : sLb ≠ lFle := by decide
@[simp] theorem lFle_ne_sLb : lFle ≠ sLb := by decide
@[simp] theorem sLb_ne_lDir : sLb ≠ lDir := by decide
@[simp] theorem lDir_ne_sLb : lDir ≠ sLb := by decide
@[simp] theorem sLb_ne_lFln : sLb ≠ lFln := by decide
@[simp] theorem lFln_ne_sLb : lFln ≠ sLb := by decide
@[simp] theorem sLb_ne_lFll : sLb ≠ lFll := by decide
@[simp] theorem lFll_ne_sLb : lFll ≠ sLb := by decide
@[simp] theorem sLb_ne_lFls : sLb ≠ lFls := by decide
@[simp] theorem lFls_ne_sLb : lFls ≠ sLb := by decide
@[simp] theorem sLb_ne_lKb : sLb ≠ lKb := by decide
@[simp] theorem lKb_ne_sLb : lKb ≠ sLb := by decide
@[simp] theorem sO_ne_lFl : sO ≠ lFl := by decide
@[simp] theorem lFl_ne_sO : lFl ≠ sO := by decide
@[simp] theorem sO_ne_lDh : sO ≠ lDh := by decide
@[simp] theorem lDh_ne_sO : lDh ≠ sO := by decide
@[simp] theorem sO_ne_lDt : sO ≠ lDt := by decide
@[simp] theorem lDt_ne_sO : lDt ≠ sO := by decide
@[simp] theorem sO_ne_lDg : sO ≠ lDg := by decide
@[simp] theorem lDg_ne_sO : lDg ≠ sO := by decide
@[simp] theorem sO_ne_lDi : sO ≠ lDi := by decide
@[simp] theorem lDi_ne_sO : lDi ≠ sO := by decide
@[simp] theorem sO_ne_lRp : sO ≠ lRp := by decide
@[simp] theorem lRp_ne_sO : lRp ≠ sO := by decide
@[simp] theorem sO_ne_lRn : sO ≠ lRn := by decide
@[simp] theorem lRn_ne_sO : lRn ≠ sO := by decide
@[simp] theorem sO_ne_lFle : sO ≠ lFle := by decide
@[simp] theorem lFle_ne_sO : lFle ≠ sO := by decide
@[simp] theorem sO_ne_lDir : sO ≠ lDir := by decide
@[simp] theorem lDir_ne_sO : lDir ≠ sO := by decide
@[simp] theorem sO_ne_lFln : sO ≠ lFln := by decide
@[simp] theorem lFln_ne_sO : lFln ≠ sO := by decide
@[simp] theorem sO_ne_lFll : sO ≠ lFll := by decide
@[simp] theorem lFll_ne_sO : lFll ≠ sO := by decide
@[simp] theorem sO_ne_lFls : sO ≠ lFls := by decide
@[simp] theorem lFls_ne_sO : lFls ≠ sO := by decide
@[simp] theorem sO_ne_lKb : sO ≠ lKb := by decide
@[simp] theorem lKb_ne_sO : lKb ≠ sO := by decide
@[simp] theorem sQa_ne_lFl : sQa ≠ lFl := by decide
@[simp] theorem lFl_ne_sQa : lFl ≠ sQa := by decide
@[simp] theorem sQa_ne_lDh : sQa ≠ lDh := by decide
@[simp] theorem lDh_ne_sQa : lDh ≠ sQa := by decide
@[simp] theorem sQa_ne_lDt : sQa ≠ lDt := by decide
@[simp] theorem lDt_ne_sQa : lDt ≠ sQa := by decide
@[simp] theorem sQa_ne_lDg : sQa ≠ lDg := by decide
@[simp] theorem lDg_ne_sQa : lDg ≠ sQa := by decide
@[simp] theorem sQa_ne_lDi : sQa ≠ lDi := by decide
@[simp] theorem lDi_ne_sQa : lDi ≠ sQa := by decide
@[simp] theorem sQa_ne_lRp : sQa ≠ lRp := by decide
@[simp] theorem lRp_ne_sQa : lRp ≠ sQa := by decide
@[simp] theorem sQa_ne_lRn : sQa ≠ lRn := by decide
@[simp] theorem lRn_ne_sQa : lRn ≠ sQa := by decide
@[simp] theorem sQa_ne_lFle : sQa ≠ lFle := by decide
@[simp] theorem lFle_ne_sQa : lFle ≠ sQa := by decide
@[simp] theorem sQa_ne_lDir : sQa ≠ lDir := by decide
@[simp] theorem lDir_ne_sQa : lDir ≠ sQa := by decide
@[simp] theorem sQa_ne_lFln : sQa ≠ lFln := by decide
@[simp] theorem lFln_ne_sQa : lFln ≠ sQa := by decide
@[simp] theorem sQa_ne_lFll : sQa ≠ lFll := by decide
@[simp] theorem lFll_ne_sQa : lFll ≠ sQa := by decide
@[simp] theorem sQa_ne_lFls : sQa ≠ lFls := by decide
@[simp] theorem lFls_ne_sQa : lFls ≠ sQa := by decide
@[simp] theorem sQa_ne_lKb : sQa ≠ lKb := by decide
@[simp] theorem lKb_ne_sQa : lKb ≠ sQa := by decide
@[simp] theorem sQb_ne_lFl : sQb ≠ lFl := by decide
@[simp] theorem lFl_ne_sQb : lFl ≠ sQb := by decide
@[simp] theorem sQb_ne_lDh : sQb ≠ lDh := by decide
@[simp] theorem lDh_ne_sQb : lDh ≠ sQb := by decide
@[simp] theorem sQb_ne_lDt : sQb ≠ lDt := by decide
@[simp] theorem lDt_ne_sQb : lDt ≠ sQb := by decide
@[simp] theorem sQb_ne_lDg : sQb ≠ lDg := by decide
@[simp] theorem lDg_ne_sQb : lDg ≠ sQb := by decide
@[simp] theorem sQb_ne_lDi : sQb ≠ lDi := by decide
@[simp] theorem lDi_ne_sQb : lDi ≠ sQb := by decide
@[simp] theorem sQb_ne_lRp : sQb ≠ lRp := by decide
@[simp] theorem lRp_ne_sQb : lRp ≠ sQb := by decide
@[simp] theorem sQb_ne_lRn : sQb ≠ lRn := by decide
@[simp] theorem lRn_ne_sQb : lRn ≠ sQb := by decide
@[simp] theorem sQb_ne_lFle : sQb ≠ lFle := by decide
@[simp] theorem lFle_ne_sQb : lFle ≠ sQb := by decide
@[simp] theorem sQb_ne_lDir : sQb ≠ lDir := by decide
@[simp] theorem lDir_ne_sQb : lDir ≠ sQb := by decide
@[simp] theorem sQb_ne_lFln : sQb ≠ lFln := by decide
@[simp] theorem lFln_ne_sQb : lFln ≠ sQb := by decide
@[simp] theorem sQb_ne_lFll : sQb ≠ lFll := by decide
@[simp] theorem lFll_ne_sQb : lFll ≠ sQb := by decide
@[simp] theorem sQb_ne_lFls : sQb ≠ lFls := by decide
@[simp] theorem lFls_ne_sQb : lFls ≠ sQb := by decide
@[simp] theorem sQb_ne_lKb : sQb ≠ lKb := by decide
@[simp] theorem lKb_ne_sQb : lKb ≠ sQb := by decide
@[simp] theorem sQo_ne_lFl : sQo ≠ lFl := by decide
@[simp] theorem lFl_ne_sQo : lFl ≠ sQo := by decide
@[simp] theorem sQo_ne_lDh : sQo ≠ lDh := by decide
@[simp] theorem lDh_ne_sQo : lDh ≠ sQo := by decide
@[simp] theorem sQo_ne_lDt : sQo ≠ lDt := by decide
@[simp] theorem lDt_ne_sQo : lDt ≠ sQo := by decide
@[simp] theorem sQo_ne_lDg : sQo ≠ lDg := by decide
@[simp] theorem lDg_ne_sQo : lDg ≠ sQo := by decide
@[simp] theorem sQo_ne_lDi : sQo ≠ lDi := by decide
@[simp] theorem lDi_ne_sQo : lDi ≠ sQo := by decide
@[simp] theorem sQo_ne_lRp : sQo ≠ lRp := by decide
@[simp] theorem lRp_ne_sQo : lRp ≠ sQo := by decide
@[simp] theorem sQo_ne_lRn : sQo ≠ lRn := by decide
@[simp] theorem lRn_ne_sQo : lRn ≠ sQo := by decide
@[simp] theorem sQo_ne_lFle : sQo ≠ lFle := by decide
@[simp] theorem lFle_ne_sQo : lFle ≠ sQo := by decide
@[simp] theorem sQo_ne_lDir : sQo ≠ lDir := by decide
@[simp] theorem lDir_ne_sQo : lDir ≠ sQo := by decide
@[simp] theorem sQo_ne_lFln : sQo ≠ lFln := by decide
@[simp] theorem lFln_ne_sQo : lFln ≠ sQo := by decide
@[simp] theorem sQo_ne_lFll : sQo ≠ lFll := by decide
@[simp] theorem lFll_ne_sQo : lFll ≠ sQo := by decide
@[simp] theorem sQo_ne_lFls : sQo ≠ lFls := by decide
@[simp] theorem lFls_ne_sQo : lFls ≠ sQo := by decide
@[simp] theorem sQo_ne_lKb : sQo ≠ lKb := by decide
@[simp] theorem lKb_ne_sQo : lKb ≠ sQo := by decide
@[simp] theorem sU_ne_lFl : sU ≠ lFl := by decide
@[simp] theorem lFl_ne_sU : lFl ≠ sU := by decide
@[simp] theorem sU_ne_lDh : sU ≠ lDh := by decide
@[simp] theorem lDh_ne_sU : lDh ≠ sU := by decide
@[simp] theorem sU_ne_lDt : sU ≠ lDt := by decide
@[simp] theorem lDt_ne_sU : lDt ≠ sU := by decide
@[simp] theorem sU_ne_lDg : sU ≠ lDg := by decide
@[simp] theorem lDg_ne_sU : lDg ≠ sU := by decide
@[simp] theorem sU_ne_lDi : sU ≠ lDi := by decide
@[simp] theorem lDi_ne_sU : lDi ≠ sU := by decide
@[simp] theorem sU_ne_lRp : sU ≠ lRp := by decide
@[simp] theorem lRp_ne_sU : lRp ≠ sU := by decide
@[simp] theorem sU_ne_lRn : sU ≠ lRn := by decide
@[simp] theorem lRn_ne_sU : lRn ≠ sU := by decide
@[simp] theorem sU_ne_lFle : sU ≠ lFle := by decide
@[simp] theorem lFle_ne_sU : lFle ≠ sU := by decide
@[simp] theorem sU_ne_lDir : sU ≠ lDir := by decide
@[simp] theorem lDir_ne_sU : lDir ≠ sU := by decide
@[simp] theorem sU_ne_lFln : sU ≠ lFln := by decide
@[simp] theorem lFln_ne_sU : lFln ≠ sU := by decide
@[simp] theorem sU_ne_lFll : sU ≠ lFll := by decide
@[simp] theorem lFll_ne_sU : lFll ≠ sU := by decide
@[simp] theorem sU_ne_lFls : sU ≠ lFls := by decide
@[simp] theorem lFls_ne_sU : lFls ≠ sU := by decide
@[simp] theorem sU_ne_lKb : sU ≠ lKb := by decide
@[simp] theorem lKb_ne_sU : lKb ≠ sU := by decide
@[simp] theorem sV_ne_lFl : sV ≠ lFl := by decide
@[simp] theorem lFl_ne_sV : lFl ≠ sV := by decide
@[simp] theorem sV_ne_lDh : sV ≠ lDh := by decide
@[simp] theorem lDh_ne_sV : lDh ≠ sV := by decide
@[simp] theorem sV_ne_lDt : sV ≠ lDt := by decide
@[simp] theorem lDt_ne_sV : lDt ≠ sV := by decide
@[simp] theorem sV_ne_lDg : sV ≠ lDg := by decide
@[simp] theorem lDg_ne_sV : lDg ≠ sV := by decide
@[simp] theorem sV_ne_lDi : sV ≠ lDi := by decide
@[simp] theorem lDi_ne_sV : lDi ≠ sV := by decide
@[simp] theorem sV_ne_lRp : sV ≠ lRp := by decide
@[simp] theorem lRp_ne_sV : lRp ≠ sV := by decide
@[simp] theorem sV_ne_lRn : sV ≠ lRn := by decide
@[simp] theorem lRn_ne_sV : lRn ≠ sV := by decide
@[simp] theorem sV_ne_lFle : sV ≠ lFle := by decide
@[simp] theorem lFle_ne_sV : lFle ≠ sV := by decide
@[simp] theorem sV_ne_lDir : sV ≠ lDir := by decide
@[simp] theorem lDir_ne_sV : lDir ≠ sV := by decide
@[simp] theorem sV_ne_lFln : sV ≠ lFln := by decide
@[simp] theorem lFln_ne_sV : lFln ≠ sV := by decide
@[simp] theorem sV_ne_lFll : sV ≠ lFll := by decide
@[simp] theorem lFll_ne_sV : lFll ≠ sV := by decide
@[simp] theorem sV_ne_lFls : sV ≠ lFls := by decide
@[simp] theorem lFls_ne_sV : lFls ≠ sV := by decide
@[simp] theorem sV_ne_lKb : sV ≠ lKb := by decide
@[simp] theorem lKb_ne_sV : lKb ≠ sV := by decide
@[simp] theorem sD1_ne_lFl : sD1 ≠ lFl := by decide
@[simp] theorem lFl_ne_sD1 : lFl ≠ sD1 := by decide
@[simp] theorem sD1_ne_lDh : sD1 ≠ lDh := by decide
@[simp] theorem lDh_ne_sD1 : lDh ≠ sD1 := by decide
@[simp] theorem sD1_ne_lDt : sD1 ≠ lDt := by decide
@[simp] theorem lDt_ne_sD1 : lDt ≠ sD1 := by decide
@[simp] theorem sD1_ne_lDg : sD1 ≠ lDg := by decide
@[simp] theorem lDg_ne_sD1 : lDg ≠ sD1 := by decide
@[simp] theorem sD1_ne_lDi : sD1 ≠ lDi := by decide
@[simp] theorem lDi_ne_sD1 : lDi ≠ sD1 := by decide
@[simp] theorem sD1_ne_lRp : sD1 ≠ lRp := by decide
@[simp] theorem lRp_ne_sD1 : lRp ≠ sD1 := by decide
@[simp] theorem sD1_ne_lRn : sD1 ≠ lRn := by decide
@[simp] theorem lRn_ne_sD1 : lRn ≠ sD1 := by decide
@[simp] theorem sD1_ne_lFle : sD1 ≠ lFle := by decide
@[simp] theorem lFle_ne_sD1 : lFle ≠ sD1 := by decide
@[simp] theorem sD1_ne_lDir : sD1 ≠ lDir := by decide
@[simp] theorem lDir_ne_sD1 : lDir ≠ sD1 := by decide
@[simp] theorem sD1_ne_lFln : sD1 ≠ lFln := by decide
@[simp] theorem lFln_ne_sD1 : lFln ≠ sD1 := by decide
@[simp] theorem sD1_ne_lFll : sD1 ≠ lFll := by decide
@[simp] theorem lFll_ne_sD1 : lFll ≠ sD1 := by decide
@[simp] theorem sD1_ne_lFls : sD1 ≠ lFls := by decide
@[simp] theorem lFls_ne_sD1 : lFls ≠ sD1 := by decide
@[simp] theorem sD1_ne_lKb : sD1 ≠ lKb := by decide
@[simp] theorem lKb_ne_sD1 : lKb ≠ sD1 := by decide
@[simp] theorem sD_ne_lFl : sD ≠ lFl := by decide
@[simp] theorem lFl_ne_sD : lFl ≠ sD := by decide
@[simp] theorem sD_ne_lDh : sD ≠ lDh := by decide
@[simp] theorem lDh_ne_sD : lDh ≠ sD := by decide
@[simp] theorem sD_ne_lDt : sD ≠ lDt := by decide
@[simp] theorem lDt_ne_sD : lDt ≠ sD := by decide
@[simp] theorem sD_ne_lDg : sD ≠ lDg := by decide
@[simp] theorem lDg_ne_sD : lDg ≠ sD := by decide
@[simp] theorem sD_ne_lDi : sD ≠ lDi := by decide
@[simp] theorem lDi_ne_sD : lDi ≠ sD := by decide
@[simp] theorem sD_ne_lRp : sD ≠ lRp := by decide
@[simp] theorem lRp_ne_sD : lRp ≠ sD := by decide
@[simp] theorem sD_ne_lRn : sD ≠ lRn := by decide
@[simp] theorem lRn_ne_sD : lRn ≠ sD := by decide
@[simp] theorem sD_ne_lFle : sD ≠ lFle := by decide
@[simp] theorem lFle_ne_sD : lFle ≠ sD := by decide
@[simp] theorem sD_ne_lDir : sD ≠ lDir := by decide
@[simp] theorem lDir_ne_sD : lDir ≠ sD := by decide
@[simp] theorem sD_ne_lFln : sD ≠ lFln := by decide
@[simp] theorem lFln_ne_sD : lFln ≠ sD := by decide
@[simp] theorem sD_ne_lFll : sD ≠ lFll := by decide
@[simp] theorem lFll_ne_sD : lFll ≠ sD := by decide
@[simp] theorem sD_ne_lFls : sD ≠ lFls := by decide
@[simp] theorem lFls_ne_sD : lFls ≠ sD := by decide
@[simp] theorem sD_ne_lKb : sD ≠ lKb := by decide
@[simp] theorem lKb_ne_sD : lKb ≠ sD := by decide
@[simp] theorem sB_ne_lFl : sB ≠ lFl := by decide
@[simp] theorem lFl_ne_sB : lFl ≠ sB := by decide
@[simp] theorem sB_ne_lDh : sB ≠ lDh := by decide
@[simp] theorem lDh_ne_sB : lDh ≠ sB := by decide
@[simp] theorem sB_ne_lDt : sB ≠ lDt := by decide
@[simp] theorem lDt_ne_sB : lDt ≠ sB := by decide
@[simp] theorem sB_ne_lDg : sB ≠ lDg := by decide
@[simp] theorem lDg_ne_sB : lDg ≠ sB := by decide
@[simp] theorem sB_ne_lDi : sB ≠ lDi := by decide
@[simp] theorem lDi_ne_sB : lDi ≠ sB := by decide
@[simp] theorem sB_ne_lRp : sB ≠ lRp := by decide
@[simp] theorem lRp_ne_sB : lRp ≠ sB := by decide
@[simp] theorem sB_ne_lRn : sB ≠ lRn := by decide
@[simp] theorem lRn_ne_sB : lRn ≠ sB := by decide
@[simp] theorem sB_ne_lFle : sB ≠ lFle := by decide
@[simp] theorem lFle_ne_sB : lFle ≠ sB := by decide
@[simp] theorem sB_ne_lDir : sB ≠ lDir := by decide
@[simp] theorem lDir_ne_sB : lDir ≠ sB := by decide
@[simp] theorem sB_ne_lFln : sB ≠ lFln := by decide
@[simp] theorem lFln_ne_sB : lFln ≠ sB := by decide
@[simp] theorem sB_ne_lFll : sB ≠ lFll := by decide
@[simp] theorem lFll_ne_sB : lFll ≠ sB := by decide
@[simp] theorem sB_ne_lFls : sB ≠ lFls := by decide
@[simp] theorem lFls_ne_sB : lFls ≠ sB := by decide
@[simp] theorem sB_ne_lKb : sB ≠ lKb := by decide
@[simp] theorem lKb_ne_sB : lKb ≠ sB := by decide
@[simp] theorem sI_ne_lFl : sI ≠ lFl := by decide
@[simp] theorem lFl_ne_sI : lFl ≠ sI := by decide
@[simp] theorem sI_ne_lDh : sI ≠ lDh := by decide
@[simp] theorem lDh_ne_sI : lDh ≠ sI := by decide
@[simp] theorem sI_ne_lDt : sI ≠ lDt := by decide
@[simp] theorem lDt_ne_sI : lDt ≠ sI := by decide
@[simp] theorem sI_ne_lDg : sI ≠ lDg := by decide
@[simp] theorem lDg_ne_sI : lDg ≠ sI := by decide
@[simp] theorem sI_ne_lDi : sI ≠ lDi := by decide
@[simp] theorem lDi_ne_sI : lDi ≠ sI := by decide
@[simp] theorem sI_ne_lRp : sI ≠ lRp := by decide
@[simp] theorem lRp_ne_sI : lRp ≠ sI := by decide
@[simp] theorem sI_ne_lRn : sI ≠ lRn := by decide
@[simp] theorem lRn_ne_sI : lRn ≠ sI := by decide
@[simp] theorem sI_ne_lFle : sI ≠ lFle := by decide
@[simp] theorem lFle_ne_sI : lFle ≠ sI := by decide
@[simp] theorem sI_ne_lDir : sI ≠ lDir := by decide
@[simp] theorem lDir_ne_sI : lDir ≠ sI := by decide
@[simp] theorem sI_ne_lFln : sI ≠ lFln := by decide
@[simp] theorem lFln_ne_sI : lFln ≠ sI := by decide
@[simp] theorem sI_ne_lFll : sI ≠ lFll := by decide
@[simp] theorem lFll_ne_sI : lFll ≠ sI := by decide
@[simp] theorem sI_ne_lFls : sI ≠ lFls := by decide
@[simp] theorem lFls_ne_sI : lFls ≠ sI := by decide
@[simp] theorem sI_ne_lKb : sI ≠ lKb := by decide
@[simp] theorem lKb_ne_sI : lKb ≠ sI := by decide
@[simp] theorem sK_ne_lFl : sK ≠ lFl := by decide
@[simp] theorem lFl_ne_sK : lFl ≠ sK := by decide
@[simp] theorem sK_ne_lDh : sK ≠ lDh := by decide
@[simp] theorem lDh_ne_sK : lDh ≠ sK := by decide
@[simp] theorem sK_ne_lDt : sK ≠ lDt := by decide
@[simp] theorem lDt_ne_sK : lDt ≠ sK := by decide
@[simp] theorem sK_ne_lDg : sK ≠ lDg := by decide
@[simp] theorem lDg_ne_sK : lDg ≠ sK := by decide
@[simp] theorem sK_ne_lDi : sK ≠ lDi := by decide
@[simp] theorem lDi_ne_sK : lDi ≠ sK := by decide
@[simp] theorem sK_ne_lRp : sK ≠ lRp := by decide
@[simp] theorem lRp_ne_sK : lRp ≠ sK := by decide
@[simp] theorem sK_ne_lRn : sK ≠ lRn := by decide
@[simp] theorem lRn_ne_sK : lRn ≠ sK := by decide
@[simp] theorem sK_ne_lFle : sK ≠ lFle := by decide
@[simp] theorem lFle_ne_sK : lFle ≠ sK := by decide
@[simp] theorem sK_ne_lDir : sK ≠ lDir := by decide
@[simp] theorem lDir_ne_sK : lDir ≠ sK := by decide
@[simp] theorem sK_ne_lFln : sK ≠ lFln := by decide
@[simp] theorem lFln_ne_sK : lFln ≠ sK := by decide
@[simp] theorem sK_ne_lFll : sK ≠ lFll := by decide
@[simp] theorem lFll_ne_sK : lFll ≠ sK := by decide
@[simp] theorem sK_ne_lFls : sK ≠ lFls := by decide
@[simp] theorem lFls_ne_sK : lFls ≠ sK := by decide
@[simp] theorem sK_ne_lKb : sK ≠ lKb := by decide
@[simp] theorem lKb_ne_sK : lKb ≠ sK := by decide
@[simp] theorem sL_ne_lFl : sL ≠ lFl := by decide
@[simp] theorem lFl_ne_sL : lFl ≠ sL := by decide
@[simp] theorem sL_ne_lDh : sL ≠ lDh := by decide
@[simp] theorem lDh_ne_sL : lDh ≠ sL := by decide
@[simp] theorem sL_ne_lDt : sL ≠ lDt := by decide
@[simp] theorem lDt_ne_sL : lDt ≠ sL := by decide
@[simp] theorem sL_ne_lDg : sL ≠ lDg := by decide
@[simp] theorem lDg_ne_sL : lDg ≠ sL := by decide
@[simp] theorem sL_ne_lDi : sL ≠ lDi := by decide
@[simp] theorem lDi_ne_sL : lDi ≠ sL := by decide
@[simp] theorem sL_ne_lRp : sL ≠ lRp := by decide
@[simp] theorem lRp_ne_sL : lRp ≠ sL := by decide
@[simp] theorem sL_ne_lRn : sL ≠ lRn := by decide
@[simp] theorem lRn_ne_sL : lRn ≠ sL := by decide
@[simp] theorem sL_ne_lFle : sL ≠ lFle := by decide
@[simp] theorem lFle_ne_sL : lFle ≠ sL := by decide
@[simp] theorem sL_ne_lDir : sL ≠ lDir := by decide
@[simp] theorem lDir_ne_sL : lDir ≠ sL := by decide
@[simp] theorem sL_ne_lFln : sL ≠ lFln := by decide
@[simp] theorem lFln_ne_sL : lFln ≠ sL := by decide
@[simp] theorem sL_ne_lFll : sL ≠ lFll := by decide
@[simp] theorem lFll_ne_sL : lFll ≠ sL := by decide
@[simp] theorem sL_ne_lFls : sL ≠ lFls := by decide
@[simp] theorem lFls_ne_sL : lFls ≠ sL := by decide
@[simp] theorem sL_ne_lKb : sL ≠ lKb := by decide
@[simp] theorem lKb_ne_sL : lKb ≠ sL := by decide

/-- One digit: `d1 := u - v; d := d1 - b; b := (u < v) + (d1 < b); [qo] := d`. -/
def sdigitP : ProgHOL 64 :=
  .seq (.assign .local sD1 (.op .sub [vv sU, vv sV]))
  (.seq (.assign .local sD (.op .sub [vv sD1, vv sB]))
  (.seq (.assign .local sB (.op .add [.cmp .lower (vv sU) (vv sV), .cmp .lower (vv sD1) (vv sB)]))
  (.store (vv sQo) (vv sD))))

def subLoop1 : ProgHOL 64 :=
  .while (.cmp .lower (vv sI) (vv sLb))
    (.seq (.assign .local sU (.load .one (vv sQa)))
    (.seq (.assign .local sV (.load .one (vv sQb)))
    (.seq sdigitP
    (.seq (.assign .local sQa (.op .add [vv sQa, .const 8]))
    (.seq (.assign .local sQb (.op .add [vv sQb, .const 8]))
    (.seq (.assign .local sQo (.op .add [vv sQo, .const 8]))
    (.assign .local sI (.op .add [vv sI, .const 1]))))))))

def subLoop2 : ProgHOL 64 :=
  .while (.cmp .lower (vv sI) (vv sLa))
    (.seq (.assign .local sU (.load .one (vv sQa)))
    (.seq (.assign .local sV (.const 0))
    (.seq sdigitP
    (.seq (.assign .local sQa (.op .add [vv sQa, .const 8]))
    (.seq (.assign .local sQo (.op .add [vv sQo, .const 8]))
    (.assign .local sI (.op .add [vv sI, .const 1])))))))

/-- The trim scan: `L := L + (u ≠ 0) * ((k + 1) - L)`. -/
def trimE : ExpHOL 64 :=
  .op .add [vv sL, .panop .mul [.cmp .notEqual (vv sU) (.const 0), .op .sub [.op .add [vv sK, .const 1], vv sL]]]

def subLoop3 : ProgHOL 64 :=
  .while (.cmp .lower (vv sK) (vv sLa))
    (.seq (.assign .local sU (.load .one (vv sQo)))
    (.seq (.assign .local sL trimE)
    (.seq (.assign .local sQo (.op .add [vv sQo, .const 8]))
    (.assign .local sK (.op .add [vv sK, .const 1])))))

def subCore (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local sLa (.load .one (vv sX)))
  (.seq (.assign .local sLb (.load .one (vv sY)))
  (allocP C sO (.panop .mul [.op .add [vv sLa, .const 2], .const 8])
  (.seq (.assign .local sQa (.op .add [vv sX, .const 8]))
  (.seq (.assign .local sQb (.op .add [vv sY, .const 8]))
  (.seq (.assign .local sQo (.op .add [vv sO, .const 8]))
  (.seq (.assign .local sB (.const 0)) (.seq (.assign .local sI (.const 0))
  (.seq subLoop1 (.seq subLoop2
  (.seq (.assign .local sK (.const 0)) (.seq (.assign .local sL (.const 0))
  (.seq (.assign .local sQo (.op .add [vv sO, .const 8]))
  (.seq subLoop3
  (.seq (.store (vv sO) (vv sL))
  (.return (vv sO))))))))))))))))

def subLocals : List MlS := [sLa, sLb, sO, sQa, sQb, sQo, sU, sV, sD1, sD, sB, sI, sK, sL]
def subParams : List MlS := [sX, sY]
def subBody (C : Ctx) : ProgHOL 64 := prologue subLocals (subCore C)

/-- The digits of `x - y`, `x`'s length many. -/
def subW (x y lx : Nat) : List (BitVec 64) := (List.range lx).map fun k => BitVec.ofNat 64 ((x - y) / B ^ k % B)

theorem subW_get (x y lx k : Nat) (hk : k < lx) :
    (subW x y lx)[k]? = some (BitVec.ofNat 64 ((x - y) / B ^ k % B)) := by
  simp [subW, hk]

theorem limbs_len_eq (m L : Nat) (h1 : m < B ^ L) (h2 : L = 0 ∨ B ^ (L - 1) ≤ m) : (limbs m).length = L := by
  have a := (limbs_length_lt_iff m L).mpr h1
  rcases h2 with h | h
  · subst h; omega
  · have b : ¬ (limbs m).length ≤ L - 1 := by rw [limbs_length_lt_iff]; omega
    omega

theorem len_mod_succ (n k : Nat) :
    (limbs (n % B ^ (k + 1))).length = if n / B ^ k % B ≠ 0 then k + 1 else (limbs (n % B ^ k)).length := by
  rw [@Nat.mod_pow_succ n B k]
  by_cases hd : n / B ^ k % B = 0
  · simp [hd]
  · rw [ite_eq_left hd]
    apply limbs_len_eq
    · have := Nat.mod_lt n (pow_pos' k)
      have hd2 := Nat.mod_lt (n / B ^ k) Bpos
      rw [Nat.pow_succ]
      generalize n % B ^ k = a at *
      generalize n / B ^ k % B = d at *
      generalize B ^ k = P at *
      have : P * d + P ≤ P * B := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hd2
      rw [Nat.mul_comm P B] at this ⊢
      omega
    · right; simp only [Nat.add_sub_cancel]
      have : B ^ k * 1 ≤ B ^ k * (n / B ^ k % B) := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_one] at this
      exact Nat.le_trans this (Nat.le_add_left _ _)

theorem trim_word (L k d : Nat) (hd : d < B) :
    BitVec.ofNat 64 L + (if BitVec.ofNat 64 d ≠ 0 then (1 : BitVec 64) else 0) *
      (BitVec.ofNat 64 k + 1 - BitVec.ofNat 64 L) = BitVec.ofNat 64 (if d ≠ 0 then k + 1 else L) := by
  by_cases h : d = 0
  · subst h; simp
  · have : BitVec.ofNat 64 d ≠ 0 := by
      intro e; have := congrArg BitVec.toNat e; simp at this; rw [Nat.mod_eq_of_lt hd] at this; exact h this
    simp only [this, ne_eq, not_false_eq_true, ite_true, h, BitVec.one_mul]
    have e1 : ∀ x : BitVec 64, (1 : BitVec 64) * x = x := fun x => BitVec.one_mul x
    rw [e1, BitVec.add_comm, BitVec.sub_add_cancel]; exact word_add1_eq k

section
variable {σ : Type}

/-- One digit of the difference: from the limbs and the borrow, the digit is stored and the borrow advances. -/
theorem step_sdigit {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {D : List MlS} (B0 W : List (BitVec 64))
    (od i x y : Nat) (hxy : y ≤ x) (hW : W[i]? = some (BitVec.ofNat 64 ((x - y) / B ^ i % B)))
    (hlen : od + 1 + i < B0.length)
    (hu : Γ.get sU = some (BitVec.ofNat 64 (x / B ^ i % B))) (hv : Γ.get sV = some (BitVec.ofNat 64 (y / B ^ i % B)))
    (hc : Γ.get sB = some (BitVec.ofNat 64 (bor x y i))) (hq : Γ.get sQo = some (cellA C (od + 1 + i)))
    (hD : sD1 ∈ D ∧ sD ∈ D ∧ sB ∈ D) :
    Step (Inv (σ := σ) (ctxH C (fillI B0 W (od + 1) i)) s Γ [] D) sdigitP
      (Inv (ctxH C (fillI B0 W (od + 1) (i + 1))) s
        ((sB, BitVec.ofNat 64 (bor x y (i + 1))) :: (sD, BitVec.ofNat 64 ((x - y) / B ^ i % B)) ::
          (sD1, BitVec.ofNat 64 (x / B ^ i % B) - BitVec.ofNat 64 (y / B ^ i % B)) :: Γ) [] D) := by
  obtain ⟨d1, d2, d3⟩ := hD
  have hdx := Nat.mod_lt (x / B ^ i) Bpos
  have hdy := Nat.mod_lt (y / B ^ i) Bpos
  obtain ⟨wa, wc⟩ := subb_words (x / B ^ i % B) (y / B ^ i % B) (bor x y i) hdx hdy (bor_le x y i)
  rw [← sub_digit x y i hxy] at wa
  rw [← bor_succ] at wc
  unfold sdigitP
  refine step_seq (step_assignI sD1 _ (BitVec.ofNat 64 (x / B ^ i % B) - BitVec.ofNat 64 (y / B ^ i % B)) d1
    (by simp [sev, hu, hv])) ?_
  refine step_seq (step_assignI sD _ (BitVec.ofNat 64 ((x - y) / B ^ i % B)) d2 (by simp [sev, hc]; exact wa)) ?_
  refine step_seq (step_assignI sB _ (BitVec.ofNat 64 (bor x y (i + 1))) d3
    (by rw [← wc]; simp [sev, hu, hv, hc, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])) ?_
  have hl := fillI_length B0 W (od + 1)
  have hj : od + 1 + i < (ctxH C (fillI B0 W (od + 1) i)).H.length := by
    show od + 1 + i < (fillI B0 W (od + 1) i).length; rw [hl]; exact hlen
  refine step_mono (step_heapStoreI (ctxOK_H hok _) (vv sQo) (vv sD) (od + 1 + i) hj
    (BitVec.ofNat 64 ((x - y) / B ^ i % B))
    (by simp [hq]; rfl) (by simp)) (fun _ h => h) (fun t ht => ?_)
  change Inv (ctxH C ((fillI B0 W (od + 1) i).set (od + 1 + i) (BitVec.ofNat 64 ((x - y) / B ^ i % B)))) s _ [] D t
    at ht
  rw [fillI_succ_eq B0 W (od + 1) i _ hW] at ht
  exact ht


def subG1 (Γ0 : Env) (C : Ctx) (od oa ob x y i : Nat) : Env :=
  (sI, BitVec.ofNat 64 i) :: (sB, BitVec.ofNat 64 (bor x y i)) :: (sQo, cellA C (od + 1 + i)) ::
    (sQb, cellA C (ob + 1 + i)) :: (sQa, cellA C (oa + 1 + i)) :: Γ0

theorem sub_loop1 {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ0 : Env} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x y : Nat) (B0 : List (BitVec 64)) (od oa ob : Nat)
    (hxyv : y ≤ x) (hxy : (limbs y).length ≤ (limbs x).length) (hba : BlkAt B0 oa (limbs x)) (hbb : BlkAt B0 ob (limbs y))
    (hla : oa + 1 + (limbs x).length ≤ od + 1) (hlb : ob + 1 + (limbs y).length ≤ od + 1)
    (hdst : od + 1 + ((limbs x).length + 1) ≤ B0.length) (h61 : (limbs x).length < 2 ^ 61)
    (hD : sU ∈ D ∧ sV ∈ D ∧ sD1 ∈ D ∧ sD ∈ D ∧ sB ∈ D ∧ sQa ∈ D ∧ sQb ∈ D ∧ sQo ∈ D ∧ sI ∈ D)
    (hLb : Γ0.get sLb = some (BitVec.ofNat 64 (limbs y).length))
    (hn : Γ0.get sU = none ∧ Γ0.get sV = none ∧ Γ0.get sD1 = none ∧ Γ0.get sD = none)
    (hr : SpecR (Inv (ctxH C (fillI B0 (subW x y (limbs x).length) (od + 1) (limbs y).length)) s
      (subG1 Γ0 C od oa ob x y (limbs y).length) [] D) rest s m R) :
    SpecR (Inv (ctxH C (fillI B0 (subW x y (limbs x).length) (od + 1) 0)) s (subG1 Γ0 C od oa ob x y 0) [] D)
      (.seq subLoop1 rest) s m R := by
  obtain ⟨du, dv, d1, d2, dc, dqa, dqb, dqo, di⟩ := hD
  obtain ⟨n1, n2, n3, n4⟩ := hn
  refine specR_forI (σ := σ) (D := D) (M := []) _ _ rest (limbs y).length
    (fun i => ctxH C (fillI B0 (subW x y (limbs x).length) (od + 1) i)) (subG1 Γ0 C od oa ob x y)
    (fun i hi => ⟨if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 i)
      (BitVec.ofNat 64 (limbs y).length) then 1 else 0, by simp [sev, subG1, Env.get, hLb], ?_⟩) (fun i hi => ?_) hr
  · have e := word_lt_iff i (limbs y).length (by unfold B; omega) (by unfold B; omega)
    by_cases h' : i < (limbs y).length
    · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e.mpr h', h']
    · have : ¬ BitVec.ofNat 64 i < BitVec.ofNat 64 (limbs y).length := fun x => h' (e.mp x)
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this, h']
  refine step_seq (step_heapLoadI' (C := ctxH C _) sU (vv sQa) (oa + 1 + i) _
    (fill_limb B0 _ od i oa x hba hla (by omega)) du (by simp [subG1]; rfl)) ?_
  refine step_seq (step_heapLoadI' (C := ctxH C _) sV (vv sQb) (ob + 1 + i) _
    (fill_limb B0 _ od i ob y hbb hlb hi) dv (by simp [subG1]; rfl)) ?_
  refine step_seq (step_sdigit hok B0 (subW x y (limbs x).length) od i x y hxyv (subW_get x y _ i (by omega))
    (by omega) (by simp) (by simp) (by simp [subG1]) (by simp [subG1]) ⟨d1, d2, dc⟩) ?_
  refine step_seq (step_assignI sQa _ (cellA C (oa + 1 + i + 1)) dqa (by simp [sev, subG1]; exact cellA_add8 C _)) ?_
  refine step_seq (step_assignI sQb _ (cellA C (ob + 1 + i + 1)) dqb (by simp [sev, subG1]; exact cellA_add8 C _)) ?_
  refine step_seq (step_assignI sQo _ (cellA C (od + 1 + i + 1)) dqo (by simp [sev, subG1]; exact cellA_add8 C _)) ?_
  refine step_mono (step_assignI sI _ (BitVec.ofNat 64 (i + 1)) di (by simp [sev, subG1]; exact word_add1_eq i))
    (fun _ h => h) (fun t ht => inv_envMono ht (fun z v hz => ?_))
  simp only [subG1, Env.get_cons] at hz ⊢
  by_cases e1 : z = sI
  · subst e1; simp_all
  by_cases e2 : z = sB
  · subst e2; simp_all
  by_cases e3 : z = sQo
  · subst e3; simp_all [Nat.add_assoc]
  by_cases e4 : z = sQb
  · subst e4; simp_all [Nat.add_assoc]
  by_cases e5 : z = sQa
  · subst e5; simp_all [Nat.add_assoc]
  simp only [e1, e2, e3, e4, e5, ite_false] at hz
  have f1 : z ≠ sU := by intro e; subst e; rw [n1] at hz; simp at hz
  have f2 : z ≠ sV := by intro e; subst e; rw [n2] at hz; simp at hz
  have f3 : z ≠ sD1 := by intro e; subst e; rw [n3] at hz; simp at hz
  have f4 : z ≠ sD := by intro e; subst e; rw [n4] at hz; simp at hz
  simp [e1, e2, e3, e4, e5, f1, f2, f3, f4, hz]


def subG2 (Γ1 : Env) (C : Ctx) (od oa x y ly i : Nat) : Env :=
  (sI, BitVec.ofNat 64 (ly + i)) :: (sB, BitVec.ofNat 64 (bor x y (ly + i))) ::
    (sQo, cellA C (od + 1 + (ly + i))) :: (sQa, cellA C (oa + 1 + (ly + i))) :: Γ1

theorem sub_loop2 {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ1 : Env} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x y : Nat) (B0 : List (BitVec 64)) (od oa : Nat)
    (hxyv : y ≤ x) (hxy : (limbs y).length ≤ (limbs x).length) (hba : BlkAt B0 oa (limbs x))
    (hla : oa + 1 + (limbs x).length ≤ od + 1)
    (hdst : od + 1 + ((limbs x).length + 1) ≤ B0.length) (h61 : (limbs x).length < 2 ^ 61)
    (hD : sU ∈ D ∧ sV ∈ D ∧ sD1 ∈ D ∧ sD ∈ D ∧ sB ∈ D ∧ sQa ∈ D ∧ sQo ∈ D ∧ sI ∈ D)
    (hLa : Γ1.get sLa = some (BitVec.ofNat 64 (limbs x).length))
    (hn : Γ1.get sU = none ∧ Γ1.get sV = none ∧ Γ1.get sD1 = none ∧ Γ1.get sD = none)
    (hr : SpecR (Inv (ctxH C (fillI B0 (subW x y (limbs x).length) (od + 1) (limbs x).length)) s
      (subG2 Γ1 C od oa x y (limbs y).length ((limbs x).length - (limbs y).length)) [] D) rest s m R) :
    SpecR (Inv (ctxH C (fillI B0 (subW x y (limbs x).length) (od + 1) (limbs y).length)) s
      (subG2 Γ1 C od oa x y (limbs y).length 0) [] D) (.seq subLoop2 rest) s m R := by
  obtain ⟨du, dv, d1, d2, dc, dqa, dqo, di⟩ := hD
  obtain ⟨n1, n2, n3, n4⟩ := hn
  have hyB : y < B ^ (limbs y).length := (limbs_length_lt_iff y _).mp (Nat.le_refl _)
  have hk := Nat.add_sub_cancel' hxy
  refine specR_forI (σ := σ) (D := D) (M := []) _ _ rest ((limbs x).length - (limbs y).length)
    (fun i => ctxH C (fillI B0 (subW x y (limbs x).length) (od + 1) ((limbs y).length + i)))
    (subG2 Γ1 C od oa x y (limbs y).length)
    (fun i hi => ⟨if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 ((limbs y).length + i))
      (BitVec.ofNat 64 (limbs x).length) then 1 else 0, by simp [sev, subG2, Env.get, hLa], ?_⟩) (fun i hi => ?_)
    (by rw [hk]; exact hr)
  · have e := word_lt_iff ((limbs y).length + i) (limbs x).length (by unfold B; omega) (by unfold B; omega)
    by_cases h' : (limbs y).length + i < (limbs x).length
    · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e.mpr h', show i < (limbs x).length - (limbs y).length by omega]
    · have : ¬ BitVec.ofNat 64 ((limbs y).length + i) < BitVec.ofNat 64 (limbs x).length := fun x => h' (e.mp x)
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this, show ¬ i < (limbs x).length - (limbs y).length by omega]
  · refine step_seq (step_heapLoadI' (C := ctxH C _) sU (vv sQa) (oa + 1 + ((limbs y).length + i)) _
      (fill_limb B0 _ od _ oa x hba hla (by omega)) du (by simp [subG2]; rfl)) ?_
    refine step_seq (step_assignI sV (.const 0) (BitVec.ofNat 64 0) dv rfl) ?_
    rw [digit_zero y ((limbs y).length + i) hyB (by omega)]
    refine step_seq (step_sdigit hok B0 (subW x y (limbs x).length) od _ x y hxyv (subW_get x y _ _ (by omega))
      (by omega) (by simp) (by simp) (by simp [subG2]) (by simp [subG2]) ⟨d1, d2, dc⟩) ?_
    refine step_seq (step_assignI sQa _ (cellA C (oa + 1 + ((limbs y).length + i) + 1)) dqa
      (by simp [sev, subG2]; exact cellA_add8 C _)) ?_
    refine step_seq (step_assignI sQo _ (cellA C (od + 1 + ((limbs y).length + i) + 1)) dqo
      (by simp [sev, subG2]; exact cellA_add8 C _)) ?_
    refine step_mono (step_assignI sI _ (BitVec.ofNat 64 ((limbs y).length + i + 1)) di
      (by simp [sev, subG2]; exact word_add1_eq _)) (fun _ h => h) (fun t ht => ?_)
    rw [show (limbs y).length + (i + 1) = (limbs y).length + i + 1 by omega]
    refine inv_envMono ht (fun z v hz => ?_)
    simp only [subG2, Env.get_cons] at hz ⊢
    rw [show (limbs y).length + (i + 1) = (limbs y).length + i + 1 by omega] at hz
    by_cases e1 : z = sI
    · subst e1; simp_all
    by_cases e2 : z = sB
    · subst e2; simp_all
    by_cases e3 : z = sQo
    · subst e3; simp_all [Nat.add_assoc]
    by_cases e5 : z = sQa
    · subst e5; simp_all [Nat.add_assoc]
    simp only [e1, e2, e3, e5, ite_false] at hz
    have f1 : z ≠ sU := by intro e; subst e; rw [n1] at hz; simp at hz
    have f2 : z ≠ sV := by intro e; subst e; rw [n2] at hz; simp at hz
    have f3 : z ≠ sD1 := by intro e; subst e; rw [n3] at hz; simp at hz
    have f4 : z ≠ sD := by intro e; subst e; rw [n4] at hz; simp at hz
    simp [e1, e2, e3, e5, f1, f2, f3, f4, hz]


def subG3 (Γ2 : Env) (C : Ctx) (od n k : Nat) : Env :=
  (sK, BitVec.ofNat 64 k) :: (sQo, cellA C (od + 1 + k)) :: (sL, BitVec.ofNat 64 (limbs (n % B ^ k)).length) :: Γ2

theorem sub_loop3 {α : Type} {C : Ctx} {s : AState} {Γ2 : Env} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (n lx : Nat) (Bf W : List (BitVec 64)) (od : Nat)
    (hW : ∀ k, k < lx → Bf[od + 1 + k]? = some (BitVec.ofNat 64 (n / B ^ k % B))) (h61 : lx < 2 ^ 61)
    (hD : sU ∈ D ∧ sL ∈ D ∧ sQo ∈ D ∧ sK ∈ D)
    (hLa : Γ2.get sLa = some (BitVec.ofNat 64 lx)) (hn : Γ2.get sU = none)
    (hr : SpecR (Inv (ctxH C Bf) s (subG3 Γ2 C od n lx) [] D) rest s m R) :
    SpecR (Inv (ctxH C Bf) s (subG3 Γ2 C od n 0) [] D) (.seq subLoop3 rest) s m R := by
  obtain ⟨du, dl, dq, dk⟩ := hD
  refine specR_forI (σ := σ) (D := D) (M := []) _ _ rest lx (fun _ => ctxH C Bf) (subG3 Γ2 C od n)
    (fun i hi => ⟨if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 i) (BitVec.ofNat 64 lx)
      then 1 else 0, by simp [sev, subG3, Env.get, hLa], ?_⟩) (fun i hi => ?_) hr
  · have e := word_lt_iff i lx (by unfold B; omega) (by unfold B; omega)
    by_cases h' : i < lx
    · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e.mpr h', h']
    · have : ¬ BitVec.ofNat 64 i < BitVec.ofNat 64 lx := fun x => h' (e.mp x)
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this, h']
  refine step_seq (step_heapLoadI' (C := ctxH C Bf) sU (vv sQo) (od + 1 + i) _ (hW i hi) du
    (by simp [subG3]; rfl)) ?_
  refine step_seq (step_assignI sL trimE (BitVec.ofNat 64 (limbs (n % B ^ (i + 1))).length) dl ?_) ?_
  · simp only [trimE, sev, sev_vv, Env.get_cons, subG3]
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [len_mod_succ, ← trim_word _ i _ (Nat.mod_lt _ Bpos)]
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  refine step_seq (step_assignI sQo _ (cellA C (od + 1 + i + 1)) dq (by simp [sev, subG3]; exact cellA_add8 C _)) ?_
  refine step_mono (step_assignI sK _ (BitVec.ofNat 64 (i + 1)) dk (by simp [sev, subG3]; exact word_add1_eq i))
    (fun _ h => h) (fun t ht => inv_envMono ht (fun z v hz => ?_))
  simp only [subG3, Env.get_cons] at hz ⊢
  by_cases e1 : z = sK
  · subst e1; simp_all
  by_cases e2 : z = sQo
  · subst e2; simp_all [Nat.add_assoc]
  by_cases e3 : z = sL
  · subst e3; simp_all
  simp only [e1, e2, e3, ite_false] at hz
  have f1 : z ≠ sU := by intro e; subst e; rw [hn] at hz; simp at hz
  simp [e1, e2, e3, f1, hz]

theorem sub_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ subLocals → (ctxEnv C ++ subParams.zip vals).get x = none :=
  Knot.params_none C subLocals subParams vals (by decide) (by decide)

theorem sub_spec (C : Ctx) (hok : CtxOK C) (s : AState) (x y : Nat) (oa ob : Nat)
    (hba : BlkAt C.H oa (limbs x)) (hbb : BlkAt C.H ob (limbs y)) (hxyv : y ≤ x) (hxy : (limbs y).length ≤ (limbs x).length)
    (h61 : (limbs x).length < 2 ^ 60) :
    SpecR (σ := σ) (Pre C s (subParams.zip [cellA C oa, cellA C ob])) (subBody C) s (pure (x - y) : AM Nat)
      (PostH C s) := by
  refine specR_prologue (postH_locals C s) (sub_none C _) ?_
  unfold subCore
  have hla0 : C.H[oa]? = some (BitVec.ofNat 64 (limbs x).length) := by simpa using hba.1
  have hlb0 : C.H[ob]? = some (BitVec.ofNat 64 (limbs y).length) := by simpa using hbb.1
  refine UD.specR_heapLoadI' sLa (vv sX) oa _ hla0 (by decide) (by simp +decide [Env.get, subParams, ctxEnv]) ?_
  refine UD.specR_heapLoadI' sLb (vv sY) ob _ hlb0 (by decide) (by simp +decide [Env.get, subParams, ctxEnv]) ?_
  refine specR_allocI sO (.panop .mul [.op .add [vv sLa, .const 2], .const 8]) ((limbs x).length + 2) (by omega)
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
  refine specR_assignI sQa _ (cellA C (oa + 1)) (by decide) (by simp [sev, Env.get, subParams, ctxEnv]; exact cellA_add8 C _) ?_
  refine specR_assignI sQb _ (cellA C (ob + 1)) (by decide) (by simp [sev, Env.get, subParams, ctxEnv]; exact cellA_add8 C _) ?_
  refine specR_assignI sQo _ (cellA C (H'.length + 1)) (by decide) (by simp [sev, Env.get]; exact cellA_add8 C _) ?_
  refine specR_assignI sB (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
  refine specR_assignI sI (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
  let Γ0 : Env := [(sLa, BitVec.ofNat 64 (limbs x).length), (sLb, BitVec.ofNat 64 (limbs y).length),
    (sO, cellA C H'.length)]
  refine specR_envWeak (Γb := subG1 Γ0 C H'.length oa ob x y 0) (fun z v hz => ?_) ?_
  · simp only [subG1, Γ0, Env.get_cons, bor_zero, Nat.add_zero] at hz ⊢
    by_cases e1 : z = sI
    · subst e1; simpa using hz
    by_cases e2 : z = sB
    · subst e2; simpa using hz
    by_cases e3 : z = sQo
    · subst e3; simpa using hz
    by_cases e4 : z = sQb
    · subst e4; simpa using hz
    by_cases e5 : z = sQa
    · subst e5; simpa using hz
    by_cases e6 : z = sLa
    · subst e6; simpa using hz
    by_cases e7 : z = sLb
    · subst e7; simpa using hz
    by_cases e8 : z = sO
    · subst e8; simpa using hz
    simp [e1, e2, e3, e4, e5, e6, e7, e8, Env.get] at hz
  refine sub_loop1 hok x y B0 H'.length oa ob hxyv hxy hba' hbb' (by omega) (by omega) (by rw [hB0]; omega) (by omega)
    (by decide) (by simp [Γ0]) (by simp [Γ0, Env.get]) ?_
  refine specR_envWeak (Γb := subG2 Γ0 C H'.length oa x y (limbs y).length 0) (fun z v hz => ?_) ?_
  · simp only [subG1, subG2, Env.get_cons, Nat.add_zero] at hz ⊢
    by_cases e1 : z = sI
    · subst e1; simpa using hz
    by_cases e2 : z = sB
    · subst e2; simpa using hz
    by_cases e3 : z = sQo
    · subst e3; simpa using hz
    by_cases e5 : z = sQa
    · subst e5; simpa using hz
    have e4 : z ≠ sQb := by intro e; subst e; simp [Γ0, Env.get] at hz
    simp [e1, e2, e3, e4, e5] at hz ⊢; exact hz
  refine sub_loop2 hok x y B0 H'.length oa hxyv hxy hba' (by omega) (by rw [hB0]; omega) (by omega) (by decide)
    (by simp [Γ0]) (by simp [Γ0, Env.get]) ?_
  have hly : (limbs y).length + ((limbs x).length - (limbs y).length) = (limbs x).length := by omega
  -- the trim scan
  refine specR_assignI sK (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
  refine specR_assignI sL (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
  refine specR_assignI sQo _ (cellA C (H'.length + 1)) (by decide) (by simp [sev, subG2, Γ0]; exact cellA_add8 C _) ?_
  let Bf := fillI B0 (subW x y (limbs x).length) (H'.length + 1) (limbs x).length
  have hlf := fillI_length B0 (subW x y (limbs x).length) (H'.length + 1)
  have hWf : ∀ k, k < (limbs x).length → Bf[H'.length + 1 + k]? = some (BitVec.ofNat 64 ((x - y) / B ^ k % B)) := by
    intro k hk
    rw [fillI_get?, ite_eq_left ⟨by omega, by omega, by rw [hB0]; omega⟩]
    simp [show H'.length + 1 + k - (H'.length + 1) = k by omega, List.getD_eq_getElem?_getD, subW_get x y _ k hk]
  refine specR_envWeak (Γb := subG3 Γ0 C H'.length (x - y) 0) (fun z v hz => ?_) ?_
  · simp only [subG3, subG2, Γ0, Env.get_cons, Nat.pow_zero, Nat.mod_one, Nat.add_zero] at hz ⊢
    by_cases e1 : z = sK
    · subst e1; simpa using hz
    by_cases e2 : z = sQo
    · subst e2; simpa using hz
    by_cases e3 : z = sL
    · subst e3; simp at hz ⊢; rw [← hz, limbs_zero]; rfl
    simp only [e1, e2, e3, ite_false] at hz ⊢
    by_cases f1 : z = sLa
    · subst f1; simpa using hz
    by_cases f2 : z = sLb
    · subst f2; simpa using hz
    by_cases f3 : z = sO
    · subst f3; simpa using hz
    simp [f1, f2, f3, Env.get] at hz
  refine sub_loop3 (x - y) (limbs x).length Bf (subW x y (limbs x).length) H'.length hWf (by omega) (by decide)
    (by simp [Γ0]) (by simp [Γ0, Env.get]) ?_
  have hxB : x < B ^ (limbs x).length := (limbs_length_lt_iff x _).mp (Nat.le_refl _)
  have hmod : (x - y) % B ^ (limbs x).length = x - y := Nat.mod_eq_of_lt (by omega)
  have hj2 : H'.length < (ctxH C Bf).H.length := by show _ < Bf.length; rw [hlf, hB0]; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv sO) (vv sL) _ hj2 (BitVec.ofNat 64 (limbs (x - y)).length)
    (by simp [subG3, Γ0]; rfl) (by simp [subG3, hmod]) ?_
  refine specR_returnI _ (cellA C H'.length) (by simp [subG3, Γ0]) (fun t ht => ?_)
  refine ⟨_, H'.length, ?_, rfl, ?_, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
  · exact prefix_set_ge (CV.prefix_fillI _ _ _ C.H (by omega) (hpre.trans (List.prefix_append _ _)) _) _ hpl _
  · have hlen := (limbs_length_lt_iff (x - y) (limbs x).length).mpr (by omega)
    constructor
    · rw [List.getElem?_set_self (by show H'.length < Bf.length; rw [hlf, hB0]; omega)]
    · intro i hi
      rw [List.getElem?_set_ne (by omega)]
      show Bf[H'.length + 1 + i]? = _
      rw [hWf i (by omega), limbs_getElem (x - y) i hi]

end

end ConPanqueque.T.Big
