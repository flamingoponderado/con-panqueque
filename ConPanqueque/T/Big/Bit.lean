import ConPanqueque.T.Big.Sub
import ConPanqueque.T.Big.BitMath
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `land`, `lor`, `xor` on `Nat`s

The borrow loops' shape with the borrow held at `0`: a pass over the shared limbs, one over the rest of the
longer `x` (a zero limb for `y`), then the trim scan.
-/

namespace ConPanqueque.T.Big

open ConPanqueque.T ConPanqueque.T.Ex
open ConPanqueque.V.Enc

def tX := ofString "tx"
def tY := ofString "ty"
def tLa := ofString "tla"
def tLb := ofString "tlb"
def tO := ofString "to"
def tQa := ofString "tqa"
def tQb := ofString "tqb"
def tQo := ofString "tqo"
def tU := ofString "tu"
def tV := ofString "tv"
def tD1 := ofString "td1"
def tD := ofString "td"
def tB := ofString "tb"
def tI := ofString "ti"
def tK := ofString "tk"
def tL := ofString "tl"

@[simp] theorem tX_ne_tY : tX ≠ tY := by decide
@[simp] theorem tX_ne_tLa : tX ≠ tLa := by decide
@[simp] theorem tX_ne_tLb : tX ≠ tLb := by decide
@[simp] theorem tX_ne_tO : tX ≠ tO := by decide
@[simp] theorem tX_ne_tQa : tX ≠ tQa := by decide
@[simp] theorem tX_ne_tQb : tX ≠ tQb := by decide
@[simp] theorem tX_ne_tQo : tX ≠ tQo := by decide
@[simp] theorem tX_ne_tU : tX ≠ tU := by decide
@[simp] theorem tX_ne_tV : tX ≠ tV := by decide
@[simp] theorem tX_ne_tD1 : tX ≠ tD1 := by decide
@[simp] theorem tX_ne_tD : tX ≠ tD := by decide
@[simp] theorem tX_ne_tB : tX ≠ tB := by decide
@[simp] theorem tX_ne_tI : tX ≠ tI := by decide
@[simp] theorem tX_ne_tK : tX ≠ tK := by decide
@[simp] theorem tX_ne_tL : tX ≠ tL := by decide
@[simp] theorem tY_ne_tX : tY ≠ tX := by decide
@[simp] theorem tY_ne_tLa : tY ≠ tLa := by decide
@[simp] theorem tY_ne_tLb : tY ≠ tLb := by decide
@[simp] theorem tY_ne_tO : tY ≠ tO := by decide
@[simp] theorem tY_ne_tQa : tY ≠ tQa := by decide
@[simp] theorem tY_ne_tQb : tY ≠ tQb := by decide
@[simp] theorem tY_ne_tQo : tY ≠ tQo := by decide
@[simp] theorem tY_ne_tU : tY ≠ tU := by decide
@[simp] theorem tY_ne_tV : tY ≠ tV := by decide
@[simp] theorem tY_ne_tD1 : tY ≠ tD1 := by decide
@[simp] theorem tY_ne_tD : tY ≠ tD := by decide
@[simp] theorem tY_ne_tB : tY ≠ tB := by decide
@[simp] theorem tY_ne_tI : tY ≠ tI := by decide
@[simp] theorem tY_ne_tK : tY ≠ tK := by decide
@[simp] theorem tY_ne_tL : tY ≠ tL := by decide
@[simp] theorem tLa_ne_tX : tLa ≠ tX := by decide
@[simp] theorem tLa_ne_tY : tLa ≠ tY := by decide
@[simp] theorem tLa_ne_tLb : tLa ≠ tLb := by decide
@[simp] theorem tLa_ne_tO : tLa ≠ tO := by decide
@[simp] theorem tLa_ne_tQa : tLa ≠ tQa := by decide
@[simp] theorem tLa_ne_tQb : tLa ≠ tQb := by decide
@[simp] theorem tLa_ne_tQo : tLa ≠ tQo := by decide
@[simp] theorem tLa_ne_tU : tLa ≠ tU := by decide
@[simp] theorem tLa_ne_tV : tLa ≠ tV := by decide
@[simp] theorem tLa_ne_tD1 : tLa ≠ tD1 := by decide
@[simp] theorem tLa_ne_tD : tLa ≠ tD := by decide
@[simp] theorem tLa_ne_tB : tLa ≠ tB := by decide
@[simp] theorem tLa_ne_tI : tLa ≠ tI := by decide
@[simp] theorem tLa_ne_tK : tLa ≠ tK := by decide
@[simp] theorem tLa_ne_tL : tLa ≠ tL := by decide
@[simp] theorem tLb_ne_tX : tLb ≠ tX := by decide
@[simp] theorem tLb_ne_tY : tLb ≠ tY := by decide
@[simp] theorem tLb_ne_tLa : tLb ≠ tLa := by decide
@[simp] theorem tLb_ne_tO : tLb ≠ tO := by decide
@[simp] theorem tLb_ne_tQa : tLb ≠ tQa := by decide
@[simp] theorem tLb_ne_tQb : tLb ≠ tQb := by decide
@[simp] theorem tLb_ne_tQo : tLb ≠ tQo := by decide
@[simp] theorem tLb_ne_tU : tLb ≠ tU := by decide
@[simp] theorem tLb_ne_tV : tLb ≠ tV := by decide
@[simp] theorem tLb_ne_tD1 : tLb ≠ tD1 := by decide
@[simp] theorem tLb_ne_tD : tLb ≠ tD := by decide
@[simp] theorem tLb_ne_tB : tLb ≠ tB := by decide
@[simp] theorem tLb_ne_tI : tLb ≠ tI := by decide
@[simp] theorem tLb_ne_tK : tLb ≠ tK := by decide
@[simp] theorem tLb_ne_tL : tLb ≠ tL := by decide
@[simp] theorem tO_ne_tX : tO ≠ tX := by decide
@[simp] theorem tO_ne_tY : tO ≠ tY := by decide
@[simp] theorem tO_ne_tLa : tO ≠ tLa := by decide
@[simp] theorem tO_ne_tLb : tO ≠ tLb := by decide
@[simp] theorem tO_ne_tQa : tO ≠ tQa := by decide
@[simp] theorem tO_ne_tQb : tO ≠ tQb := by decide
@[simp] theorem tO_ne_tQo : tO ≠ tQo := by decide
@[simp] theorem tO_ne_tU : tO ≠ tU := by decide
@[simp] theorem tO_ne_tV : tO ≠ tV := by decide
@[simp] theorem tO_ne_tD1 : tO ≠ tD1 := by decide
@[simp] theorem tO_ne_tD : tO ≠ tD := by decide
@[simp] theorem tO_ne_tB : tO ≠ tB := by decide
@[simp] theorem tO_ne_tI : tO ≠ tI := by decide
@[simp] theorem tO_ne_tK : tO ≠ tK := by decide
@[simp] theorem tO_ne_tL : tO ≠ tL := by decide
@[simp] theorem tQa_ne_tX : tQa ≠ tX := by decide
@[simp] theorem tQa_ne_tY : tQa ≠ tY := by decide
@[simp] theorem tQa_ne_tLa : tQa ≠ tLa := by decide
@[simp] theorem tQa_ne_tLb : tQa ≠ tLb := by decide
@[simp] theorem tQa_ne_tO : tQa ≠ tO := by decide
@[simp] theorem tQa_ne_tQb : tQa ≠ tQb := by decide
@[simp] theorem tQa_ne_tQo : tQa ≠ tQo := by decide
@[simp] theorem tQa_ne_tU : tQa ≠ tU := by decide
@[simp] theorem tQa_ne_tV : tQa ≠ tV := by decide
@[simp] theorem tQa_ne_tD1 : tQa ≠ tD1 := by decide
@[simp] theorem tQa_ne_tD : tQa ≠ tD := by decide
@[simp] theorem tQa_ne_tB : tQa ≠ tB := by decide
@[simp] theorem tQa_ne_tI : tQa ≠ tI := by decide
@[simp] theorem tQa_ne_tK : tQa ≠ tK := by decide
@[simp] theorem tQa_ne_tL : tQa ≠ tL := by decide
@[simp] theorem tQb_ne_tX : tQb ≠ tX := by decide
@[simp] theorem tQb_ne_tY : tQb ≠ tY := by decide
@[simp] theorem tQb_ne_tLa : tQb ≠ tLa := by decide
@[simp] theorem tQb_ne_tLb : tQb ≠ tLb := by decide
@[simp] theorem tQb_ne_tO : tQb ≠ tO := by decide
@[simp] theorem tQb_ne_tQa : tQb ≠ tQa := by decide
@[simp] theorem tQb_ne_tQo : tQb ≠ tQo := by decide
@[simp] theorem tQb_ne_tU : tQb ≠ tU := by decide
@[simp] theorem tQb_ne_tV : tQb ≠ tV := by decide
@[simp] theorem tQb_ne_tD1 : tQb ≠ tD1 := by decide
@[simp] theorem tQb_ne_tD : tQb ≠ tD := by decide
@[simp] theorem tQb_ne_tB : tQb ≠ tB := by decide
@[simp] theorem tQb_ne_tI : tQb ≠ tI := by decide
@[simp] theorem tQb_ne_tK : tQb ≠ tK := by decide
@[simp] theorem tQb_ne_tL : tQb ≠ tL := by decide
@[simp] theorem tQo_ne_tX : tQo ≠ tX := by decide
@[simp] theorem tQo_ne_tY : tQo ≠ tY := by decide
@[simp] theorem tQo_ne_tLa : tQo ≠ tLa := by decide
@[simp] theorem tQo_ne_tLb : tQo ≠ tLb := by decide
@[simp] theorem tQo_ne_tO : tQo ≠ tO := by decide
@[simp] theorem tQo_ne_tQa : tQo ≠ tQa := by decide
@[simp] theorem tQo_ne_tQb : tQo ≠ tQb := by decide
@[simp] theorem tQo_ne_tU : tQo ≠ tU := by decide
@[simp] theorem tQo_ne_tV : tQo ≠ tV := by decide
@[simp] theorem tQo_ne_tD1 : tQo ≠ tD1 := by decide
@[simp] theorem tQo_ne_tD : tQo ≠ tD := by decide
@[simp] theorem tQo_ne_tB : tQo ≠ tB := by decide
@[simp] theorem tQo_ne_tI : tQo ≠ tI := by decide
@[simp] theorem tQo_ne_tK : tQo ≠ tK := by decide
@[simp] theorem tQo_ne_tL : tQo ≠ tL := by decide
@[simp] theorem tU_ne_tX : tU ≠ tX := by decide
@[simp] theorem tU_ne_tY : tU ≠ tY := by decide
@[simp] theorem tU_ne_tLa : tU ≠ tLa := by decide
@[simp] theorem tU_ne_tLb : tU ≠ tLb := by decide
@[simp] theorem tU_ne_tO : tU ≠ tO := by decide
@[simp] theorem tU_ne_tQa : tU ≠ tQa := by decide
@[simp] theorem tU_ne_tQb : tU ≠ tQb := by decide
@[simp] theorem tU_ne_tQo : tU ≠ tQo := by decide
@[simp] theorem tU_ne_tV : tU ≠ tV := by decide
@[simp] theorem tU_ne_tD1 : tU ≠ tD1 := by decide
@[simp] theorem tU_ne_tD : tU ≠ tD := by decide
@[simp] theorem tU_ne_tB : tU ≠ tB := by decide
@[simp] theorem tU_ne_tI : tU ≠ tI := by decide
@[simp] theorem tU_ne_tK : tU ≠ tK := by decide
@[simp] theorem tU_ne_tL : tU ≠ tL := by decide
@[simp] theorem tV_ne_tX : tV ≠ tX := by decide
@[simp] theorem tV_ne_tY : tV ≠ tY := by decide
@[simp] theorem tV_ne_tLa : tV ≠ tLa := by decide
@[simp] theorem tV_ne_tLb : tV ≠ tLb := by decide
@[simp] theorem tV_ne_tO : tV ≠ tO := by decide
@[simp] theorem tV_ne_tQa : tV ≠ tQa := by decide
@[simp] theorem tV_ne_tQb : tV ≠ tQb := by decide
@[simp] theorem tV_ne_tQo : tV ≠ tQo := by decide
@[simp] theorem tV_ne_tU : tV ≠ tU := by decide
@[simp] theorem tV_ne_tD1 : tV ≠ tD1 := by decide
@[simp] theorem tV_ne_tD : tV ≠ tD := by decide
@[simp] theorem tV_ne_tB : tV ≠ tB := by decide
@[simp] theorem tV_ne_tI : tV ≠ tI := by decide
@[simp] theorem tV_ne_tK : tV ≠ tK := by decide
@[simp] theorem tV_ne_tL : tV ≠ tL := by decide
@[simp] theorem tD1_ne_tX : tD1 ≠ tX := by decide
@[simp] theorem tD1_ne_tY : tD1 ≠ tY := by decide
@[simp] theorem tD1_ne_tLa : tD1 ≠ tLa := by decide
@[simp] theorem tD1_ne_tLb : tD1 ≠ tLb := by decide
@[simp] theorem tD1_ne_tO : tD1 ≠ tO := by decide
@[simp] theorem tD1_ne_tQa : tD1 ≠ tQa := by decide
@[simp] theorem tD1_ne_tQb : tD1 ≠ tQb := by decide
@[simp] theorem tD1_ne_tQo : tD1 ≠ tQo := by decide
@[simp] theorem tD1_ne_tU : tD1 ≠ tU := by decide
@[simp] theorem tD1_ne_tV : tD1 ≠ tV := by decide
@[simp] theorem tD1_ne_tD : tD1 ≠ tD := by decide
@[simp] theorem tD1_ne_tB : tD1 ≠ tB := by decide
@[simp] theorem tD1_ne_tI : tD1 ≠ tI := by decide
@[simp] theorem tD1_ne_tK : tD1 ≠ tK := by decide
@[simp] theorem tD1_ne_tL : tD1 ≠ tL := by decide
@[simp] theorem tD_ne_tX : tD ≠ tX := by decide
@[simp] theorem tD_ne_tY : tD ≠ tY := by decide
@[simp] theorem tD_ne_tLa : tD ≠ tLa := by decide
@[simp] theorem tD_ne_tLb : tD ≠ tLb := by decide
@[simp] theorem tD_ne_tO : tD ≠ tO := by decide
@[simp] theorem tD_ne_tQa : tD ≠ tQa := by decide
@[simp] theorem tD_ne_tQb : tD ≠ tQb := by decide
@[simp] theorem tD_ne_tQo : tD ≠ tQo := by decide
@[simp] theorem tD_ne_tU : tD ≠ tU := by decide
@[simp] theorem tD_ne_tV : tD ≠ tV := by decide
@[simp] theorem tD_ne_tD1 : tD ≠ tD1 := by decide
@[simp] theorem tD_ne_tB : tD ≠ tB := by decide
@[simp] theorem tD_ne_tI : tD ≠ tI := by decide
@[simp] theorem tD_ne_tK : tD ≠ tK := by decide
@[simp] theorem tD_ne_tL : tD ≠ tL := by decide
@[simp] theorem tB_ne_tX : tB ≠ tX := by decide
@[simp] theorem tB_ne_tY : tB ≠ tY := by decide
@[simp] theorem tB_ne_tLa : tB ≠ tLa := by decide
@[simp] theorem tB_ne_tLb : tB ≠ tLb := by decide
@[simp] theorem tB_ne_tO : tB ≠ tO := by decide
@[simp] theorem tB_ne_tQa : tB ≠ tQa := by decide
@[simp] theorem tB_ne_tQb : tB ≠ tQb := by decide
@[simp] theorem tB_ne_tQo : tB ≠ tQo := by decide
@[simp] theorem tB_ne_tU : tB ≠ tU := by decide
@[simp] theorem tB_ne_tV : tB ≠ tV := by decide
@[simp] theorem tB_ne_tD1 : tB ≠ tD1 := by decide
@[simp] theorem tB_ne_tD : tB ≠ tD := by decide
@[simp] theorem tB_ne_tI : tB ≠ tI := by decide
@[simp] theorem tB_ne_tK : tB ≠ tK := by decide
@[simp] theorem tB_ne_tL : tB ≠ tL := by decide
@[simp] theorem tI_ne_tX : tI ≠ tX := by decide
@[simp] theorem tI_ne_tY : tI ≠ tY := by decide
@[simp] theorem tI_ne_tLa : tI ≠ tLa := by decide
@[simp] theorem tI_ne_tLb : tI ≠ tLb := by decide
@[simp] theorem tI_ne_tO : tI ≠ tO := by decide
@[simp] theorem tI_ne_tQa : tI ≠ tQa := by decide
@[simp] theorem tI_ne_tQb : tI ≠ tQb := by decide
@[simp] theorem tI_ne_tQo : tI ≠ tQo := by decide
@[simp] theorem tI_ne_tU : tI ≠ tU := by decide
@[simp] theorem tI_ne_tV : tI ≠ tV := by decide
@[simp] theorem tI_ne_tD1 : tI ≠ tD1 := by decide
@[simp] theorem tI_ne_tD : tI ≠ tD := by decide
@[simp] theorem tI_ne_tB : tI ≠ tB := by decide
@[simp] theorem tI_ne_tK : tI ≠ tK := by decide
@[simp] theorem tI_ne_tL : tI ≠ tL := by decide
@[simp] theorem tK_ne_tX : tK ≠ tX := by decide
@[simp] theorem tK_ne_tY : tK ≠ tY := by decide
@[simp] theorem tK_ne_tLa : tK ≠ tLa := by decide
@[simp] theorem tK_ne_tLb : tK ≠ tLb := by decide
@[simp] theorem tK_ne_tO : tK ≠ tO := by decide
@[simp] theorem tK_ne_tQa : tK ≠ tQa := by decide
@[simp] theorem tK_ne_tQb : tK ≠ tQb := by decide
@[simp] theorem tK_ne_tQo : tK ≠ tQo := by decide
@[simp] theorem tK_ne_tU : tK ≠ tU := by decide
@[simp] theorem tK_ne_tV : tK ≠ tV := by decide
@[simp] theorem tK_ne_tD1 : tK ≠ tD1 := by decide
@[simp] theorem tK_ne_tD : tK ≠ tD := by decide
@[simp] theorem tK_ne_tB : tK ≠ tB := by decide
@[simp] theorem tK_ne_tI : tK ≠ tI := by decide
@[simp] theorem tK_ne_tL : tK ≠ tL := by decide
@[simp] theorem tL_ne_tX : tL ≠ tX := by decide
@[simp] theorem tL_ne_tY : tL ≠ tY := by decide
@[simp] theorem tL_ne_tLa : tL ≠ tLa := by decide
@[simp] theorem tL_ne_tLb : tL ≠ tLb := by decide
@[simp] theorem tL_ne_tO : tL ≠ tO := by decide
@[simp] theorem tL_ne_tQa : tL ≠ tQa := by decide
@[simp] theorem tL_ne_tQb : tL ≠ tQb := by decide
@[simp] theorem tL_ne_tQo : tL ≠ tQo := by decide
@[simp] theorem tL_ne_tU : tL ≠ tU := by decide
@[simp] theorem tL_ne_tV : tL ≠ tV := by decide
@[simp] theorem tL_ne_tD1 : tL ≠ tD1 := by decide
@[simp] theorem tL_ne_tD : tL ≠ tD := by decide
@[simp] theorem tL_ne_tB : tL ≠ tB := by decide
@[simp] theorem tL_ne_tI : tL ≠ tI := by decide
@[simp] theorem tL_ne_tK : tL ≠ tK := by decide
@[simp] theorem tX_ne_lFl : tX ≠ lFl := by decide
@[simp] theorem lFl_ne_tX : lFl ≠ tX := by decide
@[simp] theorem tX_ne_lDh : tX ≠ lDh := by decide
@[simp] theorem lDh_ne_tX : lDh ≠ tX := by decide
@[simp] theorem tX_ne_lDt : tX ≠ lDt := by decide
@[simp] theorem lDt_ne_tX : lDt ≠ tX := by decide
@[simp] theorem tX_ne_lDg : tX ≠ lDg := by decide
@[simp] theorem lDg_ne_tX : lDg ≠ tX := by decide
@[simp] theorem tX_ne_lDi : tX ≠ lDi := by decide
@[simp] theorem lDi_ne_tX : lDi ≠ tX := by decide
@[simp] theorem tX_ne_lRp : tX ≠ lRp := by decide
@[simp] theorem lRp_ne_tX : lRp ≠ tX := by decide
@[simp] theorem tX_ne_lRn : tX ≠ lRn := by decide
@[simp] theorem lRn_ne_tX : lRn ≠ tX := by decide
@[simp] theorem tX_ne_lFle : tX ≠ lFle := by decide
@[simp] theorem lFle_ne_tX : lFle ≠ tX := by decide
@[simp] theorem tX_ne_lDir : tX ≠ lDir := by decide
@[simp] theorem lDir_ne_tX : lDir ≠ tX := by decide
@[simp] theorem tX_ne_lFln : tX ≠ lFln := by decide
@[simp] theorem lFln_ne_tX : lFln ≠ tX := by decide
@[simp] theorem tX_ne_lFll : tX ≠ lFll := by decide
@[simp] theorem lFll_ne_tX : lFll ≠ tX := by decide
@[simp] theorem tX_ne_lFls : tX ≠ lFls := by decide
@[simp] theorem lFls_ne_tX : lFls ≠ tX := by decide
@[simp] theorem tX_ne_lKb : tX ≠ lKb := by decide
@[simp] theorem lKb_ne_tX : lKb ≠ tX := by decide
@[simp] theorem tY_ne_lFl : tY ≠ lFl := by decide
@[simp] theorem lFl_ne_tY : lFl ≠ tY := by decide
@[simp] theorem tY_ne_lDh : tY ≠ lDh := by decide
@[simp] theorem lDh_ne_tY : lDh ≠ tY := by decide
@[simp] theorem tY_ne_lDt : tY ≠ lDt := by decide
@[simp] theorem lDt_ne_tY : lDt ≠ tY := by decide
@[simp] theorem tY_ne_lDg : tY ≠ lDg := by decide
@[simp] theorem lDg_ne_tY : lDg ≠ tY := by decide
@[simp] theorem tY_ne_lDi : tY ≠ lDi := by decide
@[simp] theorem lDi_ne_tY : lDi ≠ tY := by decide
@[simp] theorem tY_ne_lRp : tY ≠ lRp := by decide
@[simp] theorem lRp_ne_tY : lRp ≠ tY := by decide
@[simp] theorem tY_ne_lRn : tY ≠ lRn := by decide
@[simp] theorem lRn_ne_tY : lRn ≠ tY := by decide
@[simp] theorem tY_ne_lFle : tY ≠ lFle := by decide
@[simp] theorem lFle_ne_tY : lFle ≠ tY := by decide
@[simp] theorem tY_ne_lDir : tY ≠ lDir := by decide
@[simp] theorem lDir_ne_tY : lDir ≠ tY := by decide
@[simp] theorem tY_ne_lFln : tY ≠ lFln := by decide
@[simp] theorem lFln_ne_tY : lFln ≠ tY := by decide
@[simp] theorem tY_ne_lFll : tY ≠ lFll := by decide
@[simp] theorem lFll_ne_tY : lFll ≠ tY := by decide
@[simp] theorem tY_ne_lFls : tY ≠ lFls := by decide
@[simp] theorem lFls_ne_tY : lFls ≠ tY := by decide
@[simp] theorem tY_ne_lKb : tY ≠ lKb := by decide
@[simp] theorem lKb_ne_tY : lKb ≠ tY := by decide
@[simp] theorem tLa_ne_lFl : tLa ≠ lFl := by decide
@[simp] theorem lFl_ne_tLa : lFl ≠ tLa := by decide
@[simp] theorem tLa_ne_lDh : tLa ≠ lDh := by decide
@[simp] theorem lDh_ne_tLa : lDh ≠ tLa := by decide
@[simp] theorem tLa_ne_lDt : tLa ≠ lDt := by decide
@[simp] theorem lDt_ne_tLa : lDt ≠ tLa := by decide
@[simp] theorem tLa_ne_lDg : tLa ≠ lDg := by decide
@[simp] theorem lDg_ne_tLa : lDg ≠ tLa := by decide
@[simp] theorem tLa_ne_lDi : tLa ≠ lDi := by decide
@[simp] theorem lDi_ne_tLa : lDi ≠ tLa := by decide
@[simp] theorem tLa_ne_lRp : tLa ≠ lRp := by decide
@[simp] theorem lRp_ne_tLa : lRp ≠ tLa := by decide
@[simp] theorem tLa_ne_lRn : tLa ≠ lRn := by decide
@[simp] theorem lRn_ne_tLa : lRn ≠ tLa := by decide
@[simp] theorem tLa_ne_lFle : tLa ≠ lFle := by decide
@[simp] theorem lFle_ne_tLa : lFle ≠ tLa := by decide
@[simp] theorem tLa_ne_lDir : tLa ≠ lDir := by decide
@[simp] theorem lDir_ne_tLa : lDir ≠ tLa := by decide
@[simp] theorem tLa_ne_lFln : tLa ≠ lFln := by decide
@[simp] theorem lFln_ne_tLa : lFln ≠ tLa := by decide
@[simp] theorem tLa_ne_lFll : tLa ≠ lFll := by decide
@[simp] theorem lFll_ne_tLa : lFll ≠ tLa := by decide
@[simp] theorem tLa_ne_lFls : tLa ≠ lFls := by decide
@[simp] theorem lFls_ne_tLa : lFls ≠ tLa := by decide
@[simp] theorem tLa_ne_lKb : tLa ≠ lKb := by decide
@[simp] theorem lKb_ne_tLa : lKb ≠ tLa := by decide
@[simp] theorem tLb_ne_lFl : tLb ≠ lFl := by decide
@[simp] theorem lFl_ne_tLb : lFl ≠ tLb := by decide
@[simp] theorem tLb_ne_lDh : tLb ≠ lDh := by decide
@[simp] theorem lDh_ne_tLb : lDh ≠ tLb := by decide
@[simp] theorem tLb_ne_lDt : tLb ≠ lDt := by decide
@[simp] theorem lDt_ne_tLb : lDt ≠ tLb := by decide
@[simp] theorem tLb_ne_lDg : tLb ≠ lDg := by decide
@[simp] theorem lDg_ne_tLb : lDg ≠ tLb := by decide
@[simp] theorem tLb_ne_lDi : tLb ≠ lDi := by decide
@[simp] theorem lDi_ne_tLb : lDi ≠ tLb := by decide
@[simp] theorem tLb_ne_lRp : tLb ≠ lRp := by decide
@[simp] theorem lRp_ne_tLb : lRp ≠ tLb := by decide
@[simp] theorem tLb_ne_lRn : tLb ≠ lRn := by decide
@[simp] theorem lRn_ne_tLb : lRn ≠ tLb := by decide
@[simp] theorem tLb_ne_lFle : tLb ≠ lFle := by decide
@[simp] theorem lFle_ne_tLb : lFle ≠ tLb := by decide
@[simp] theorem tLb_ne_lDir : tLb ≠ lDir := by decide
@[simp] theorem lDir_ne_tLb : lDir ≠ tLb := by decide
@[simp] theorem tLb_ne_lFln : tLb ≠ lFln := by decide
@[simp] theorem lFln_ne_tLb : lFln ≠ tLb := by decide
@[simp] theorem tLb_ne_lFll : tLb ≠ lFll := by decide
@[simp] theorem lFll_ne_tLb : lFll ≠ tLb := by decide
@[simp] theorem tLb_ne_lFls : tLb ≠ lFls := by decide
@[simp] theorem lFls_ne_tLb : lFls ≠ tLb := by decide
@[simp] theorem tLb_ne_lKb : tLb ≠ lKb := by decide
@[simp] theorem lKb_ne_tLb : lKb ≠ tLb := by decide
@[simp] theorem tO_ne_lFl : tO ≠ lFl := by decide
@[simp] theorem lFl_ne_tO : lFl ≠ tO := by decide
@[simp] theorem tO_ne_lDh : tO ≠ lDh := by decide
@[simp] theorem lDh_ne_tO : lDh ≠ tO := by decide
@[simp] theorem tO_ne_lDt : tO ≠ lDt := by decide
@[simp] theorem lDt_ne_tO : lDt ≠ tO := by decide
@[simp] theorem tO_ne_lDg : tO ≠ lDg := by decide
@[simp] theorem lDg_ne_tO : lDg ≠ tO := by decide
@[simp] theorem tO_ne_lDi : tO ≠ lDi := by decide
@[simp] theorem lDi_ne_tO : lDi ≠ tO := by decide
@[simp] theorem tO_ne_lRp : tO ≠ lRp := by decide
@[simp] theorem lRp_ne_tO : lRp ≠ tO := by decide
@[simp] theorem tO_ne_lRn : tO ≠ lRn := by decide
@[simp] theorem lRn_ne_tO : lRn ≠ tO := by decide
@[simp] theorem tO_ne_lFle : tO ≠ lFle := by decide
@[simp] theorem lFle_ne_tO : lFle ≠ tO := by decide
@[simp] theorem tO_ne_lDir : tO ≠ lDir := by decide
@[simp] theorem lDir_ne_tO : lDir ≠ tO := by decide
@[simp] theorem tO_ne_lFln : tO ≠ lFln := by decide
@[simp] theorem lFln_ne_tO : lFln ≠ tO := by decide
@[simp] theorem tO_ne_lFll : tO ≠ lFll := by decide
@[simp] theorem lFll_ne_tO : lFll ≠ tO := by decide
@[simp] theorem tO_ne_lFls : tO ≠ lFls := by decide
@[simp] theorem lFls_ne_tO : lFls ≠ tO := by decide
@[simp] theorem tO_ne_lKb : tO ≠ lKb := by decide
@[simp] theorem lKb_ne_tO : lKb ≠ tO := by decide
@[simp] theorem tQa_ne_lFl : tQa ≠ lFl := by decide
@[simp] theorem lFl_ne_tQa : lFl ≠ tQa := by decide
@[simp] theorem tQa_ne_lDh : tQa ≠ lDh := by decide
@[simp] theorem lDh_ne_tQa : lDh ≠ tQa := by decide
@[simp] theorem tQa_ne_lDt : tQa ≠ lDt := by decide
@[simp] theorem lDt_ne_tQa : lDt ≠ tQa := by decide
@[simp] theorem tQa_ne_lDg : tQa ≠ lDg := by decide
@[simp] theorem lDg_ne_tQa : lDg ≠ tQa := by decide
@[simp] theorem tQa_ne_lDi : tQa ≠ lDi := by decide
@[simp] theorem lDi_ne_tQa : lDi ≠ tQa := by decide
@[simp] theorem tQa_ne_lRp : tQa ≠ lRp := by decide
@[simp] theorem lRp_ne_tQa : lRp ≠ tQa := by decide
@[simp] theorem tQa_ne_lRn : tQa ≠ lRn := by decide
@[simp] theorem lRn_ne_tQa : lRn ≠ tQa := by decide
@[simp] theorem tQa_ne_lFle : tQa ≠ lFle := by decide
@[simp] theorem lFle_ne_tQa : lFle ≠ tQa := by decide
@[simp] theorem tQa_ne_lDir : tQa ≠ lDir := by decide
@[simp] theorem lDir_ne_tQa : lDir ≠ tQa := by decide
@[simp] theorem tQa_ne_lFln : tQa ≠ lFln := by decide
@[simp] theorem lFln_ne_tQa : lFln ≠ tQa := by decide
@[simp] theorem tQa_ne_lFll : tQa ≠ lFll := by decide
@[simp] theorem lFll_ne_tQa : lFll ≠ tQa := by decide
@[simp] theorem tQa_ne_lFls : tQa ≠ lFls := by decide
@[simp] theorem lFls_ne_tQa : lFls ≠ tQa := by decide
@[simp] theorem tQa_ne_lKb : tQa ≠ lKb := by decide
@[simp] theorem lKb_ne_tQa : lKb ≠ tQa := by decide
@[simp] theorem tQb_ne_lFl : tQb ≠ lFl := by decide
@[simp] theorem lFl_ne_tQb : lFl ≠ tQb := by decide
@[simp] theorem tQb_ne_lDh : tQb ≠ lDh := by decide
@[simp] theorem lDh_ne_tQb : lDh ≠ tQb := by decide
@[simp] theorem tQb_ne_lDt : tQb ≠ lDt := by decide
@[simp] theorem lDt_ne_tQb : lDt ≠ tQb := by decide
@[simp] theorem tQb_ne_lDg : tQb ≠ lDg := by decide
@[simp] theorem lDg_ne_tQb : lDg ≠ tQb := by decide
@[simp] theorem tQb_ne_lDi : tQb ≠ lDi := by decide
@[simp] theorem lDi_ne_tQb : lDi ≠ tQb := by decide
@[simp] theorem tQb_ne_lRp : tQb ≠ lRp := by decide
@[simp] theorem lRp_ne_tQb : lRp ≠ tQb := by decide
@[simp] theorem tQb_ne_lRn : tQb ≠ lRn := by decide
@[simp] theorem lRn_ne_tQb : lRn ≠ tQb := by decide
@[simp] theorem tQb_ne_lFle : tQb ≠ lFle := by decide
@[simp] theorem lFle_ne_tQb : lFle ≠ tQb := by decide
@[simp] theorem tQb_ne_lDir : tQb ≠ lDir := by decide
@[simp] theorem lDir_ne_tQb : lDir ≠ tQb := by decide
@[simp] theorem tQb_ne_lFln : tQb ≠ lFln := by decide
@[simp] theorem lFln_ne_tQb : lFln ≠ tQb := by decide
@[simp] theorem tQb_ne_lFll : tQb ≠ lFll := by decide
@[simp] theorem lFll_ne_tQb : lFll ≠ tQb := by decide
@[simp] theorem tQb_ne_lFls : tQb ≠ lFls := by decide
@[simp] theorem lFls_ne_tQb : lFls ≠ tQb := by decide
@[simp] theorem tQb_ne_lKb : tQb ≠ lKb := by decide
@[simp] theorem lKb_ne_tQb : lKb ≠ tQb := by decide
@[simp] theorem tQo_ne_lFl : tQo ≠ lFl := by decide
@[simp] theorem lFl_ne_tQo : lFl ≠ tQo := by decide
@[simp] theorem tQo_ne_lDh : tQo ≠ lDh := by decide
@[simp] theorem lDh_ne_tQo : lDh ≠ tQo := by decide
@[simp] theorem tQo_ne_lDt : tQo ≠ lDt := by decide
@[simp] theorem lDt_ne_tQo : lDt ≠ tQo := by decide
@[simp] theorem tQo_ne_lDg : tQo ≠ lDg := by decide
@[simp] theorem lDg_ne_tQo : lDg ≠ tQo := by decide
@[simp] theorem tQo_ne_lDi : tQo ≠ lDi := by decide
@[simp] theorem lDi_ne_tQo : lDi ≠ tQo := by decide
@[simp] theorem tQo_ne_lRp : tQo ≠ lRp := by decide
@[simp] theorem lRp_ne_tQo : lRp ≠ tQo := by decide
@[simp] theorem tQo_ne_lRn : tQo ≠ lRn := by decide
@[simp] theorem lRn_ne_tQo : lRn ≠ tQo := by decide
@[simp] theorem tQo_ne_lFle : tQo ≠ lFle := by decide
@[simp] theorem lFle_ne_tQo : lFle ≠ tQo := by decide
@[simp] theorem tQo_ne_lDir : tQo ≠ lDir := by decide
@[simp] theorem lDir_ne_tQo : lDir ≠ tQo := by decide
@[simp] theorem tQo_ne_lFln : tQo ≠ lFln := by decide
@[simp] theorem lFln_ne_tQo : lFln ≠ tQo := by decide
@[simp] theorem tQo_ne_lFll : tQo ≠ lFll := by decide
@[simp] theorem lFll_ne_tQo : lFll ≠ tQo := by decide
@[simp] theorem tQo_ne_lFls : tQo ≠ lFls := by decide
@[simp] theorem lFls_ne_tQo : lFls ≠ tQo := by decide
@[simp] theorem tQo_ne_lKb : tQo ≠ lKb := by decide
@[simp] theorem lKb_ne_tQo : lKb ≠ tQo := by decide
@[simp] theorem tU_ne_lFl : tU ≠ lFl := by decide
@[simp] theorem lFl_ne_tU : lFl ≠ tU := by decide
@[simp] theorem tU_ne_lDh : tU ≠ lDh := by decide
@[simp] theorem lDh_ne_tU : lDh ≠ tU := by decide
@[simp] theorem tU_ne_lDt : tU ≠ lDt := by decide
@[simp] theorem lDt_ne_tU : lDt ≠ tU := by decide
@[simp] theorem tU_ne_lDg : tU ≠ lDg := by decide
@[simp] theorem lDg_ne_tU : lDg ≠ tU := by decide
@[simp] theorem tU_ne_lDi : tU ≠ lDi := by decide
@[simp] theorem lDi_ne_tU : lDi ≠ tU := by decide
@[simp] theorem tU_ne_lRp : tU ≠ lRp := by decide
@[simp] theorem lRp_ne_tU : lRp ≠ tU := by decide
@[simp] theorem tU_ne_lRn : tU ≠ lRn := by decide
@[simp] theorem lRn_ne_tU : lRn ≠ tU := by decide
@[simp] theorem tU_ne_lFle : tU ≠ lFle := by decide
@[simp] theorem lFle_ne_tU : lFle ≠ tU := by decide
@[simp] theorem tU_ne_lDir : tU ≠ lDir := by decide
@[simp] theorem lDir_ne_tU : lDir ≠ tU := by decide
@[simp] theorem tU_ne_lFln : tU ≠ lFln := by decide
@[simp] theorem lFln_ne_tU : lFln ≠ tU := by decide
@[simp] theorem tU_ne_lFll : tU ≠ lFll := by decide
@[simp] theorem lFll_ne_tU : lFll ≠ tU := by decide
@[simp] theorem tU_ne_lFls : tU ≠ lFls := by decide
@[simp] theorem lFls_ne_tU : lFls ≠ tU := by decide
@[simp] theorem tU_ne_lKb : tU ≠ lKb := by decide
@[simp] theorem lKb_ne_tU : lKb ≠ tU := by decide
@[simp] theorem tV_ne_lFl : tV ≠ lFl := by decide
@[simp] theorem lFl_ne_tV : lFl ≠ tV := by decide
@[simp] theorem tV_ne_lDh : tV ≠ lDh := by decide
@[simp] theorem lDh_ne_tV : lDh ≠ tV := by decide
@[simp] theorem tV_ne_lDt : tV ≠ lDt := by decide
@[simp] theorem lDt_ne_tV : lDt ≠ tV := by decide
@[simp] theorem tV_ne_lDg : tV ≠ lDg := by decide
@[simp] theorem lDg_ne_tV : lDg ≠ tV := by decide
@[simp] theorem tV_ne_lDi : tV ≠ lDi := by decide
@[simp] theorem lDi_ne_tV : lDi ≠ tV := by decide
@[simp] theorem tV_ne_lRp : tV ≠ lRp := by decide
@[simp] theorem lRp_ne_tV : lRp ≠ tV := by decide
@[simp] theorem tV_ne_lRn : tV ≠ lRn := by decide
@[simp] theorem lRn_ne_tV : lRn ≠ tV := by decide
@[simp] theorem tV_ne_lFle : tV ≠ lFle := by decide
@[simp] theorem lFle_ne_tV : lFle ≠ tV := by decide
@[simp] theorem tV_ne_lDir : tV ≠ lDir := by decide
@[simp] theorem lDir_ne_tV : lDir ≠ tV := by decide
@[simp] theorem tV_ne_lFln : tV ≠ lFln := by decide
@[simp] theorem lFln_ne_tV : lFln ≠ tV := by decide
@[simp] theorem tV_ne_lFll : tV ≠ lFll := by decide
@[simp] theorem lFll_ne_tV : lFll ≠ tV := by decide
@[simp] theorem tV_ne_lFls : tV ≠ lFls := by decide
@[simp] theorem lFls_ne_tV : lFls ≠ tV := by decide
@[simp] theorem tV_ne_lKb : tV ≠ lKb := by decide
@[simp] theorem lKb_ne_tV : lKb ≠ tV := by decide
@[simp] theorem tD1_ne_lFl : tD1 ≠ lFl := by decide
@[simp] theorem lFl_ne_tD1 : lFl ≠ tD1 := by decide
@[simp] theorem tD1_ne_lDh : tD1 ≠ lDh := by decide
@[simp] theorem lDh_ne_tD1 : lDh ≠ tD1 := by decide
@[simp] theorem tD1_ne_lDt : tD1 ≠ lDt := by decide
@[simp] theorem lDt_ne_tD1 : lDt ≠ tD1 := by decide
@[simp] theorem tD1_ne_lDg : tD1 ≠ lDg := by decide
@[simp] theorem lDg_ne_tD1 : lDg ≠ tD1 := by decide
@[simp] theorem tD1_ne_lDi : tD1 ≠ lDi := by decide
@[simp] theorem lDi_ne_tD1 : lDi ≠ tD1 := by decide
@[simp] theorem tD1_ne_lRp : tD1 ≠ lRp := by decide
@[simp] theorem lRp_ne_tD1 : lRp ≠ tD1 := by decide
@[simp] theorem tD1_ne_lRn : tD1 ≠ lRn := by decide
@[simp] theorem lRn_ne_tD1 : lRn ≠ tD1 := by decide
@[simp] theorem tD1_ne_lFle : tD1 ≠ lFle := by decide
@[simp] theorem lFle_ne_tD1 : lFle ≠ tD1 := by decide
@[simp] theorem tD1_ne_lDir : tD1 ≠ lDir := by decide
@[simp] theorem lDir_ne_tD1 : lDir ≠ tD1 := by decide
@[simp] theorem tD1_ne_lFln : tD1 ≠ lFln := by decide
@[simp] theorem lFln_ne_tD1 : lFln ≠ tD1 := by decide
@[simp] theorem tD1_ne_lFll : tD1 ≠ lFll := by decide
@[simp] theorem lFll_ne_tD1 : lFll ≠ tD1 := by decide
@[simp] theorem tD1_ne_lFls : tD1 ≠ lFls := by decide
@[simp] theorem lFls_ne_tD1 : lFls ≠ tD1 := by decide
@[simp] theorem tD1_ne_lKb : tD1 ≠ lKb := by decide
@[simp] theorem lKb_ne_tD1 : lKb ≠ tD1 := by decide
@[simp] theorem tD_ne_lFl : tD ≠ lFl := by decide
@[simp] theorem lFl_ne_tD : lFl ≠ tD := by decide
@[simp] theorem tD_ne_lDh : tD ≠ lDh := by decide
@[simp] theorem lDh_ne_tD : lDh ≠ tD := by decide
@[simp] theorem tD_ne_lDt : tD ≠ lDt := by decide
@[simp] theorem lDt_ne_tD : lDt ≠ tD := by decide
@[simp] theorem tD_ne_lDg : tD ≠ lDg := by decide
@[simp] theorem lDg_ne_tD : lDg ≠ tD := by decide
@[simp] theorem tD_ne_lDi : tD ≠ lDi := by decide
@[simp] theorem lDi_ne_tD : lDi ≠ tD := by decide
@[simp] theorem tD_ne_lRp : tD ≠ lRp := by decide
@[simp] theorem lRp_ne_tD : lRp ≠ tD := by decide
@[simp] theorem tD_ne_lRn : tD ≠ lRn := by decide
@[simp] theorem lRn_ne_tD : lRn ≠ tD := by decide
@[simp] theorem tD_ne_lFle : tD ≠ lFle := by decide
@[simp] theorem lFle_ne_tD : lFle ≠ tD := by decide
@[simp] theorem tD_ne_lDir : tD ≠ lDir := by decide
@[simp] theorem lDir_ne_tD : lDir ≠ tD := by decide
@[simp] theorem tD_ne_lFln : tD ≠ lFln := by decide
@[simp] theorem lFln_ne_tD : lFln ≠ tD := by decide
@[simp] theorem tD_ne_lFll : tD ≠ lFll := by decide
@[simp] theorem lFll_ne_tD : lFll ≠ tD := by decide
@[simp] theorem tD_ne_lFls : tD ≠ lFls := by decide
@[simp] theorem lFls_ne_tD : lFls ≠ tD := by decide
@[simp] theorem tD_ne_lKb : tD ≠ lKb := by decide
@[simp] theorem lKb_ne_tD : lKb ≠ tD := by decide
@[simp] theorem tB_ne_lFl : tB ≠ lFl := by decide
@[simp] theorem lFl_ne_tB : lFl ≠ tB := by decide
@[simp] theorem tB_ne_lDh : tB ≠ lDh := by decide
@[simp] theorem lDh_ne_tB : lDh ≠ tB := by decide
@[simp] theorem tB_ne_lDt : tB ≠ lDt := by decide
@[simp] theorem lDt_ne_tB : lDt ≠ tB := by decide
@[simp] theorem tB_ne_lDg : tB ≠ lDg := by decide
@[simp] theorem lDg_ne_tB : lDg ≠ tB := by decide
@[simp] theorem tB_ne_lDi : tB ≠ lDi := by decide
@[simp] theorem lDi_ne_tB : lDi ≠ tB := by decide
@[simp] theorem tB_ne_lRp : tB ≠ lRp := by decide
@[simp] theorem lRp_ne_tB : lRp ≠ tB := by decide
@[simp] theorem tB_ne_lRn : tB ≠ lRn := by decide
@[simp] theorem lRn_ne_tB : lRn ≠ tB := by decide
@[simp] theorem tB_ne_lFle : tB ≠ lFle := by decide
@[simp] theorem lFle_ne_tB : lFle ≠ tB := by decide
@[simp] theorem tB_ne_lDir : tB ≠ lDir := by decide
@[simp] theorem lDir_ne_tB : lDir ≠ tB := by decide
@[simp] theorem tB_ne_lFln : tB ≠ lFln := by decide
@[simp] theorem lFln_ne_tB : lFln ≠ tB := by decide
@[simp] theorem tB_ne_lFll : tB ≠ lFll := by decide
@[simp] theorem lFll_ne_tB : lFll ≠ tB := by decide
@[simp] theorem tB_ne_lFls : tB ≠ lFls := by decide
@[simp] theorem lFls_ne_tB : lFls ≠ tB := by decide
@[simp] theorem tB_ne_lKb : tB ≠ lKb := by decide
@[simp] theorem lKb_ne_tB : lKb ≠ tB := by decide
@[simp] theorem tI_ne_lFl : tI ≠ lFl := by decide
@[simp] theorem lFl_ne_tI : lFl ≠ tI := by decide
@[simp] theorem tI_ne_lDh : tI ≠ lDh := by decide
@[simp] theorem lDh_ne_tI : lDh ≠ tI := by decide
@[simp] theorem tI_ne_lDt : tI ≠ lDt := by decide
@[simp] theorem lDt_ne_tI : lDt ≠ tI := by decide
@[simp] theorem tI_ne_lDg : tI ≠ lDg := by decide
@[simp] theorem lDg_ne_tI : lDg ≠ tI := by decide
@[simp] theorem tI_ne_lDi : tI ≠ lDi := by decide
@[simp] theorem lDi_ne_tI : lDi ≠ tI := by decide
@[simp] theorem tI_ne_lRp : tI ≠ lRp := by decide
@[simp] theorem lRp_ne_tI : lRp ≠ tI := by decide
@[simp] theorem tI_ne_lRn : tI ≠ lRn := by decide
@[simp] theorem lRn_ne_tI : lRn ≠ tI := by decide
@[simp] theorem tI_ne_lFle : tI ≠ lFle := by decide
@[simp] theorem lFle_ne_tI : lFle ≠ tI := by decide
@[simp] theorem tI_ne_lDir : tI ≠ lDir := by decide
@[simp] theorem lDir_ne_tI : lDir ≠ tI := by decide
@[simp] theorem tI_ne_lFln : tI ≠ lFln := by decide
@[simp] theorem lFln_ne_tI : lFln ≠ tI := by decide
@[simp] theorem tI_ne_lFll : tI ≠ lFll := by decide
@[simp] theorem lFll_ne_tI : lFll ≠ tI := by decide
@[simp] theorem tI_ne_lFls : tI ≠ lFls := by decide
@[simp] theorem lFls_ne_tI : lFls ≠ tI := by decide
@[simp] theorem tI_ne_lKb : tI ≠ lKb := by decide
@[simp] theorem lKb_ne_tI : lKb ≠ tI := by decide
@[simp] theorem tK_ne_lFl : tK ≠ lFl := by decide
@[simp] theorem lFl_ne_tK : lFl ≠ tK := by decide
@[simp] theorem tK_ne_lDh : tK ≠ lDh := by decide
@[simp] theorem lDh_ne_tK : lDh ≠ tK := by decide
@[simp] theorem tK_ne_lDt : tK ≠ lDt := by decide
@[simp] theorem lDt_ne_tK : lDt ≠ tK := by decide
@[simp] theorem tK_ne_lDg : tK ≠ lDg := by decide
@[simp] theorem lDg_ne_tK : lDg ≠ tK := by decide
@[simp] theorem tK_ne_lDi : tK ≠ lDi := by decide
@[simp] theorem lDi_ne_tK : lDi ≠ tK := by decide
@[simp] theorem tK_ne_lRp : tK ≠ lRp := by decide
@[simp] theorem lRp_ne_tK : lRp ≠ tK := by decide
@[simp] theorem tK_ne_lRn : tK ≠ lRn := by decide
@[simp] theorem lRn_ne_tK : lRn ≠ tK := by decide
@[simp] theorem tK_ne_lFle : tK ≠ lFle := by decide
@[simp] theorem lFle_ne_tK : lFle ≠ tK := by decide
@[simp] theorem tK_ne_lDir : tK ≠ lDir := by decide
@[simp] theorem lDir_ne_tK : lDir ≠ tK := by decide
@[simp] theorem tK_ne_lFln : tK ≠ lFln := by decide
@[simp] theorem lFln_ne_tK : lFln ≠ tK := by decide
@[simp] theorem tK_ne_lFll : tK ≠ lFll := by decide
@[simp] theorem lFll_ne_tK : lFll ≠ tK := by decide
@[simp] theorem tK_ne_lFls : tK ≠ lFls := by decide
@[simp] theorem lFls_ne_tK : lFls ≠ tK := by decide
@[simp] theorem tK_ne_lKb : tK ≠ lKb := by decide
@[simp] theorem lKb_ne_tK : lKb ≠ tK := by decide
@[simp] theorem tL_ne_lFl : tL ≠ lFl := by decide
@[simp] theorem lFl_ne_tL : lFl ≠ tL := by decide
@[simp] theorem tL_ne_lDh : tL ≠ lDh := by decide
@[simp] theorem lDh_ne_tL : lDh ≠ tL := by decide
@[simp] theorem tL_ne_lDt : tL ≠ lDt := by decide
@[simp] theorem lDt_ne_tL : lDt ≠ tL := by decide
@[simp] theorem tL_ne_lDg : tL ≠ lDg := by decide
@[simp] theorem lDg_ne_tL : lDg ≠ tL := by decide
@[simp] theorem tL_ne_lDi : tL ≠ lDi := by decide
@[simp] theorem lDi_ne_tL : lDi ≠ tL := by decide
@[simp] theorem tL_ne_lRp : tL ≠ lRp := by decide
@[simp] theorem lRp_ne_tL : lRp ≠ tL := by decide
@[simp] theorem tL_ne_lRn : tL ≠ lRn := by decide
@[simp] theorem lRn_ne_tL : lRn ≠ tL := by decide
@[simp] theorem tL_ne_lFle : tL ≠ lFle := by decide
@[simp] theorem lFle_ne_tL : lFle ≠ tL := by decide
@[simp] theorem tL_ne_lDir : tL ≠ lDir := by decide
@[simp] theorem lDir_ne_tL : lDir ≠ tL := by decide
@[simp] theorem tL_ne_lFln : tL ≠ lFln := by decide
@[simp] theorem lFln_ne_tL : lFln ≠ tL := by decide
@[simp] theorem tL_ne_lFll : tL ≠ lFll := by decide
@[simp] theorem lFll_ne_tL : lFll ≠ tL := by decide
@[simp] theorem tL_ne_lFls : tL ≠ lFls := by decide
@[simp] theorem lFls_ne_tL : lFls ≠ tL := by decide
@[simp] theorem tL_ne_lKb : tL ≠ lKb := by decide
@[simp] theorem lKb_ne_tL : lKb ≠ tL := by decide

def BitOp.op : BitOp → BinOp
  | .and => .and | .or => .or | .xor => .xor

/-- One digit: `d1 := u op v; d := d1 - b; b := b; [qo] := d` (`b` stays `0`; the shape of the borrow loops). -/
def bdigitP (o : BitOp) : ProgHOL 64 :=
  .seq (.assign .local tD1 (.op o.op [vv tU, vv tV]))
  (.seq (.assign .local tD (.op .sub [vv tD1, vv tB]))
  (.seq (.assign .local tB (vv tB))
  (.store (vv tQo) (vv tD))))

def bitLoop1 (o : BitOp) : ProgHOL 64 :=
  .while (.cmp .lower (vv tI) (vv tLb))
    (.seq (.assign .local tU (.load .one (vv tQa)))
    (.seq (.assign .local tV (.load .one (vv tQb)))
    (.seq (bdigitP o)
    (.seq (.assign .local tQa (.op .add [vv tQa, .const 8]))
    (.seq (.assign .local tQb (.op .add [vv tQb, .const 8]))
    (.seq (.assign .local tQo (.op .add [vv tQo, .const 8]))
    (.assign .local tI (.op .add [vv tI, .const 1]))))))))

def bitLoop2 (o : BitOp) : ProgHOL 64 :=
  .while (.cmp .lower (vv tI) (vv tLa))
    (.seq (.assign .local tU (.load .one (vv tQa)))
    (.seq (.assign .local tV (.const 0))
    (.seq (bdigitP o)
    (.seq (.assign .local tQa (.op .add [vv tQa, .const 8]))
    (.seq (.assign .local tQo (.op .add [vv tQo, .const 8]))
    (.assign .local tI (.op .add [vv tI, .const 1])))))))

/-- The trim scan: `L := L + (u ≠ 0) * ((k + 1) - L)`. -/
def bitTrimE : ExpHOL 64 :=
  .op .add [vv tL, .panop .mul [.cmp .notEqual (vv tU) (.const 0), .op .sub [.op .add [vv tK, .const 1], vv tL]]]

def bitLoop3 : ProgHOL 64 :=
  .while (.cmp .lower (vv tK) (vv tLa))
    (.seq (.assign .local tU (.load .one (vv tQo)))
    (.seq (.assign .local tL bitTrimE)
    (.seq (.assign .local tQo (.op .add [vv tQo, .const 8]))
    (.assign .local tK (.op .add [vv tK, .const 1])))))

def bitCore (o : BitOp) (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local tLa (.load .one (vv tX)))
  (.seq (.assign .local tLb (.load .one (vv tY)))
  (allocP C tO (.panop .mul [.op .add [vv tLa, .const 2], .const 8])
  (.seq (.assign .local tQa (.op .add [vv tX, .const 8]))
  (.seq (.assign .local tQb (.op .add [vv tY, .const 8]))
  (.seq (.assign .local tQo (.op .add [vv tO, .const 8]))
  (.seq (.assign .local tB (.const 0)) (.seq (.assign .local tI (.const 0))
  (.seq (bitLoop1 o) (.seq (bitLoop2 o)
  (.seq (.assign .local tK (.const 0)) (.seq (.assign .local tL (.const 0))
  (.seq (.assign .local tQo (.op .add [vv tO, .const 8]))
  (.seq bitLoop3
  (.seq (.store (vv tO) (vv tL))
  (.return (vv tO))))))))))))))))

def bitLocals : List MlS := [tLa, tLb, tO, tQa, tQb, tQo, tU, tV, tD1, tD, tB, tI, tK, tL]
def bitParams : List MlS := [tX, tY]
def bitBody (o : BitOp) (C : Ctx) : ProgHOL 64 := prologue bitLocals (bitCore o C)

/-- The digits of `o x y`, `x`'s length many. -/
def bitW (o : BitOp) (x y lx : Nat) : List (BitVec 64) :=
  (List.range lx).map fun k => BitVec.ofNat 64 (o.f x y / B ^ k % B)

theorem bitW_get (o : BitOp) (x y lx k : Nat) (hk : k < lx) :
    (bitW o x y lx)[k]? = some (BitVec.ofNat 64 (o.f x y / B ^ k % B)) := by
  simp [bitW, hk]


section
variable {σ : Type}

def BitOp.w : BitOp → BitVec 64 → BitVec 64 → BitVec 64
  | .and, a, b => a &&& b
  | .or, a, b => a ||| b
  | .xor, a, b => a ^^^ b

theorem sev_bitop (o : BitOp) (Γ : Env) (u v : BitVec 64) (hu : Γ.get tU = some u) (hv : Γ.get tV = some v) :
    sev Γ (.op o.op [vv tU, vv tV]) = some (o.w u v) := by
  cases o <;> simp [sev, BitOp.op, BitOp.w, hu, hv]

theorem bitop_word (o : BitOp) (a b : Nat) (ha : a < B) (hb : b < B) :
    o.w (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = BitVec.ofNat 64 (o.f a b) := by
  have hB : B = 2 ^ 64 := rfl
  rw [hB] at ha hb
  have hl := o.lt a b 64 ha hb
  apply BitVec.eq_of_toNat_eq
  cases o <;> simp [BitOp.w, BitOp.f, BitVec.toNat_and, BitVec.toNat_or, BitVec.toNat_xor, Nat.mod_eq_of_lt ha,
    Nat.mod_eq_of_lt hb] <;> exact (Nat.mod_eq_of_lt hl).symm

/-- One digit of `o x y`, stored; the dummy borrow stays `0`. -/
theorem step_bdigit (o : BitOp) {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {D : List MlS} (B0 W : List (BitVec 64))
    (od i x y : Nat) (hW : W[i]? = some (BitVec.ofNat 64 (o.f x y / B ^ i % B)))
    (hlen : od + 1 + i < B0.length)
    (hu : Γ.get tU = some (BitVec.ofNat 64 (x / B ^ i % B))) (hv : Γ.get tV = some (BitVec.ofNat 64 (y / B ^ i % B)))
    (hc : Γ.get tB = some (BitVec.ofNat 64 0)) (hq : Γ.get tQo = some (cellA C (od + 1 + i)))
    (hD : tD1 ∈ D ∧ tD ∈ D ∧ tB ∈ D) :
    Step (Inv (σ := σ) (ctxH C (fillI B0 W (od + 1) i)) s Γ [] D) (bdigitP o)
      (Inv (ctxH C (fillI B0 W (od + 1) (i + 1))) s
        ((tB, BitVec.ofNat 64 0) :: (tD, BitVec.ofNat 64 (o.f x y / B ^ i % B)) ::
          (tD1, BitVec.ofNat 64 (o.f x y / B ^ i % B)) :: Γ) [] D) := by
  obtain ⟨d1, d2, d3⟩ := hD
  have hdx := Nat.mod_lt (x / B ^ i) Bpos
  have hdy := Nat.mod_lt (y / B ^ i) Bpos
  have hw := bitop_word o _ _ hdx hdy
  have hdg := o.dg_f x y i
  unfold dg at hdg
  rw [← hdg] at hw
  unfold bdigitP
  refine step_seq (step_assignI tD1 _ (BitVec.ofNat 64 (o.f x y / B ^ i % B)) d1
    (by rw [sev_bitop o _ _ _ hu hv, hw])) ?_
  refine step_seq (step_assignI tD _ (BitVec.ofNat 64 (o.f x y / B ^ i % B)) d2 (by simp [sev, hc])) ?_
  refine step_seq (step_assignI tB _ (BitVec.ofNat 64 0) d3 (by simp [hc])) ?_
  have hl := fillI_length B0 W (od + 1)
  have hj : od + 1 + i < (ctxH C (fillI B0 W (od + 1) i)).H.length := by
    show od + 1 + i < (fillI B0 W (od + 1) i).length; rw [hl]; exact hlen
  refine step_mono (step_heapStoreI (ctxOK_H hok _) (vv tQo) (vv tD) (od + 1 + i) hj
    (BitVec.ofNat 64 (o.f x y / B ^ i % B))
    (by simp [hq]; rfl) (by simp)) (fun _ h => h) (fun t ht => ?_)
  change Inv (ctxH C ((fillI B0 W (od + 1) i).set (od + 1 + i) (BitVec.ofNat 64 (o.f x y / B ^ i % B)))) s _ [] D t
    at ht
  rw [fillI_succ_eq B0 W (od + 1) i _ hW] at ht
  exact ht

def bitG1 (Γ0 : Env) (C : Ctx) (od oa ob x y i : Nat) : Env :=
  (tI, BitVec.ofNat 64 i) :: (tB, BitVec.ofNat 64 (0)) :: (tQo, cellA C (od + 1 + i)) ::
    (tQb, cellA C (ob + 1 + i)) :: (tQa, cellA C (oa + 1 + i)) :: Γ0

theorem bit_loop1 (o : BitOp) {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ0 : Env} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x y : Nat) (B0 : List (BitVec 64)) (od oa ob : Nat)
    (hxy : (limbs y).length ≤ (limbs x).length) (hba : BlkAt B0 oa (limbs x)) (hbb : BlkAt B0 ob (limbs y))
    (hla : oa + 1 + (limbs x).length ≤ od + 1) (hlb : ob + 1 + (limbs y).length ≤ od + 1)
    (hdst : od + 1 + ((limbs x).length + 1) ≤ B0.length) (h61 : (limbs x).length < 2 ^ 61)
    (hD : tU ∈ D ∧ tV ∈ D ∧ tD1 ∈ D ∧ tD ∈ D ∧ tB ∈ D ∧ tQa ∈ D ∧ tQb ∈ D ∧ tQo ∈ D ∧ tI ∈ D)
    (hLb : Γ0.get tLb = some (BitVec.ofNat 64 (limbs y).length))
    (hn : Γ0.get tU = none ∧ Γ0.get tV = none ∧ Γ0.get tD1 = none ∧ Γ0.get tD = none)
    (hr : SpecR (Inv (ctxH C (fillI B0 (bitW o x y (limbs x).length) (od + 1) (limbs y).length)) s
      (bitG1 Γ0 C od oa ob x y (limbs y).length) [] D) rest s m R) :
    SpecR (Inv (ctxH C (fillI B0 (bitW o x y (limbs x).length) (od + 1) 0)) s (bitG1 Γ0 C od oa ob x y 0) [] D)
      (.seq (bitLoop1 o) rest) s m R := by
  obtain ⟨du, dv, d1, d2, dc, dqa, dqb, dqo, di⟩ := hD
  obtain ⟨n1, n2, n3, n4⟩ := hn
  refine specR_forI (σ := σ) (D := D) (M := []) _ _ rest (limbs y).length
    (fun i => ctxH C (fillI B0 (bitW o x y (limbs x).length) (od + 1) i)) (bitG1 Γ0 C od oa ob x y)
    (fun i hi => ⟨if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 i)
      (BitVec.ofNat 64 (limbs y).length) then 1 else 0, by simp [sev, bitG1, Env.get, hLb], ?_⟩) (fun i hi => ?_) hr
  · have e := word_lt_iff i (limbs y).length (by unfold B; omega) (by unfold B; omega)
    by_cases h' : i < (limbs y).length
    · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e.mpr h', h']
    · have : ¬ BitVec.ofNat 64 i < BitVec.ofNat 64 (limbs y).length := fun x => h' (e.mp x)
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this, h']
  refine step_seq (step_heapLoadI' (C := ctxH C _) tU (vv tQa) (oa + 1 + i) _
    (fill_limb B0 _ od i oa x hba hla (by omega)) du (by simp [bitG1]; rfl)) ?_
  refine step_seq (step_heapLoadI' (C := ctxH C _) tV (vv tQb) (ob + 1 + i) _
    (fill_limb B0 _ od i ob y hbb hlb hi) dv (by simp [bitG1]; rfl)) ?_
  refine step_seq (step_bdigit o hok B0 (bitW o x y (limbs x).length) od i x y (bitW_get o x y _ i (by omega))
    (by omega) (by simp) (by simp) (by simp [bitG1]) (by simp [bitG1]) ⟨d1, d2, dc⟩) ?_
  refine step_seq (step_assignI tQa _ (cellA C (oa + 1 + i + 1)) dqa (by simp [sev, bitG1]; exact cellA_add8 C _)) ?_
  refine step_seq (step_assignI tQb _ (cellA C (ob + 1 + i + 1)) dqb (by simp [sev, bitG1]; exact cellA_add8 C _)) ?_
  refine step_seq (step_assignI tQo _ (cellA C (od + 1 + i + 1)) dqo (by simp [sev, bitG1]; exact cellA_add8 C _)) ?_
  refine step_mono (step_assignI tI _ (BitVec.ofNat 64 (i + 1)) di (by simp [sev, bitG1]; exact word_add1_eq i))
    (fun _ h => h) (fun t ht => inv_envMono ht (fun z v hz => ?_))
  simp only [bitG1, Env.get_cons] at hz ⊢
  by_cases e1 : z = tI
  · subst e1; simp_all
  by_cases e2 : z = tB
  · subst e2; simp_all
  by_cases e3 : z = tQo
  · subst e3; simp_all [Nat.add_assoc]
  by_cases e4 : z = tQb
  · subst e4; simp_all [Nat.add_assoc]
  by_cases e5 : z = tQa
  · subst e5; simp_all [Nat.add_assoc]
  simp only [e1, e2, e3, e4, e5, ite_false] at hz
  have f1 : z ≠ tU := by intro e; subst e; rw [n1] at hz; simp at hz
  have f2 : z ≠ tV := by intro e; subst e; rw [n2] at hz; simp at hz
  have f3 : z ≠ tD1 := by intro e; subst e; rw [n3] at hz; simp at hz
  have f4 : z ≠ tD := by intro e; subst e; rw [n4] at hz; simp at hz
  simp [e1, e2, e3, e4, e5, f1, f2, f3, f4, hz]


def bitG2 (Γ1 : Env) (C : Ctx) (od oa x y ly i : Nat) : Env :=
  (tI, BitVec.ofNat 64 (ly + i)) :: (tB, BitVec.ofNat 64 (0)) ::
    (tQo, cellA C (od + 1 + (ly + i))) :: (tQa, cellA C (oa + 1 + (ly + i))) :: Γ1

theorem bit_loop2 (o : BitOp) {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ1 : Env} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x y : Nat) (B0 : List (BitVec 64)) (od oa : Nat)
    (hxy : (limbs y).length ≤ (limbs x).length) (hba : BlkAt B0 oa (limbs x))
    (hla : oa + 1 + (limbs x).length ≤ od + 1)
    (hdst : od + 1 + ((limbs x).length + 1) ≤ B0.length) (h61 : (limbs x).length < 2 ^ 61)
    (hD : tU ∈ D ∧ tV ∈ D ∧ tD1 ∈ D ∧ tD ∈ D ∧ tB ∈ D ∧ tQa ∈ D ∧ tQo ∈ D ∧ tI ∈ D)
    (hLa : Γ1.get tLa = some (BitVec.ofNat 64 (limbs x).length))
    (hn : Γ1.get tU = none ∧ Γ1.get tV = none ∧ Γ1.get tD1 = none ∧ Γ1.get tD = none)
    (hr : SpecR (Inv (ctxH C (fillI B0 (bitW o x y (limbs x).length) (od + 1) (limbs x).length)) s
      (bitG2 Γ1 C od oa x y (limbs y).length ((limbs x).length - (limbs y).length)) [] D) rest s m R) :
    SpecR (Inv (ctxH C (fillI B0 (bitW o x y (limbs x).length) (od + 1) (limbs y).length)) s
      (bitG2 Γ1 C od oa x y (limbs y).length 0) [] D) (.seq (bitLoop2 o) rest) s m R := by
  obtain ⟨du, dv, d1, d2, dc, dqa, dqo, di⟩ := hD
  obtain ⟨n1, n2, n3, n4⟩ := hn
  have hyB : y < B ^ (limbs y).length := (limbs_length_lt_iff y _).mp (Nat.le_refl _)
  have hk := Nat.add_sub_cancel' hxy
  refine specR_forI (σ := σ) (D := D) (M := []) _ _ rest ((limbs x).length - (limbs y).length)
    (fun i => ctxH C (fillI B0 (bitW o x y (limbs x).length) (od + 1) ((limbs y).length + i)))
    (bitG2 Γ1 C od oa x y (limbs y).length)
    (fun i hi => ⟨if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 ((limbs y).length + i))
      (BitVec.ofNat 64 (limbs x).length) then 1 else 0, by simp [sev, bitG2, Env.get, hLa], ?_⟩) (fun i hi => ?_)
    (by rw [hk]; exact hr)
  · have e := word_lt_iff ((limbs y).length + i) (limbs x).length (by unfold B; omega) (by unfold B; omega)
    by_cases h' : (limbs y).length + i < (limbs x).length
    · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e.mpr h', show i < (limbs x).length - (limbs y).length by omega]
    · have : ¬ BitVec.ofNat 64 ((limbs y).length + i) < BitVec.ofNat 64 (limbs x).length := fun x => h' (e.mp x)
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this, show ¬ i < (limbs x).length - (limbs y).length by omega]
  · refine step_seq (step_heapLoadI' (C := ctxH C _) tU (vv tQa) (oa + 1 + ((limbs y).length + i)) _
      (fill_limb B0 _ od _ oa x hba hla (by omega)) du (by simp [bitG2]; rfl)) ?_
    refine step_seq (step_assignI tV (.const 0) (BitVec.ofNat 64 0) dv rfl) ?_
    rw [digit_zero y ((limbs y).length + i) hyB (by omega)]
    refine step_seq (step_bdigit o hok B0 (bitW o x y (limbs x).length) od _ x y (bitW_get o x y _ _ (by omega))
      (by omega) (by simp) (by simp) (by simp [bitG2]) (by simp [bitG2]) ⟨d1, d2, dc⟩) ?_
    refine step_seq (step_assignI tQa _ (cellA C (oa + 1 + ((limbs y).length + i) + 1)) dqa
      (by simp [sev, bitG2]; exact cellA_add8 C _)) ?_
    refine step_seq (step_assignI tQo _ (cellA C (od + 1 + ((limbs y).length + i) + 1)) dqo
      (by simp [sev, bitG2]; exact cellA_add8 C _)) ?_
    refine step_mono (step_assignI tI _ (BitVec.ofNat 64 ((limbs y).length + i + 1)) di
      (by simp [sev, bitG2]; exact word_add1_eq _)) (fun _ h => h) (fun t ht => ?_)
    rw [show (limbs y).length + (i + 1) = (limbs y).length + i + 1 by omega]
    refine inv_envMono ht (fun z v hz => ?_)
    simp only [bitG2, Env.get_cons] at hz ⊢
    rw [show (limbs y).length + (i + 1) = (limbs y).length + i + 1 by omega] at hz
    by_cases e1 : z = tI
    · subst e1; simp_all
    by_cases e2 : z = tB
    · subst e2; simp_all
    by_cases e3 : z = tQo
    · subst e3; simp_all [Nat.add_assoc]
    by_cases e5 : z = tQa
    · subst e5; simp_all [Nat.add_assoc]
    simp only [e1, e2, e3, e5, ite_false] at hz
    have f1 : z ≠ tU := by intro e; subst e; rw [n1] at hz; simp at hz
    have f2 : z ≠ tV := by intro e; subst e; rw [n2] at hz; simp at hz
    have f3 : z ≠ tD1 := by intro e; subst e; rw [n3] at hz; simp at hz
    have f4 : z ≠ tD := by intro e; subst e; rw [n4] at hz; simp at hz
    simp [e1, e2, e3, e5, f1, f2, f3, f4, hz]


def bitG3 (Γ2 : Env) (C : Ctx) (od n k : Nat) : Env :=
  (tK, BitVec.ofNat 64 k) :: (tQo, cellA C (od + 1 + k)) :: (tL, BitVec.ofNat 64 (limbs (n % B ^ k)).length) :: Γ2

theorem bit_loop3 {α : Type} {C : Ctx} {s : AState} {Γ2 : Env} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (n lx : Nat) (Bf W : List (BitVec 64)) (od : Nat)
    (hW : ∀ k, k < lx → Bf[od + 1 + k]? = some (BitVec.ofNat 64 (n / B ^ k % B))) (h61 : lx < 2 ^ 61)
    (hD : tU ∈ D ∧ tL ∈ D ∧ tQo ∈ D ∧ tK ∈ D)
    (hLa : Γ2.get tLa = some (BitVec.ofNat 64 lx)) (hn : Γ2.get tU = none)
    (hr : SpecR (Inv (ctxH C Bf) s (bitG3 Γ2 C od n lx) [] D) rest s m R) :
    SpecR (Inv (ctxH C Bf) s (bitG3 Γ2 C od n 0) [] D) (.seq bitLoop3 rest) s m R := by
  obtain ⟨du, dl, dq, dk⟩ := hD
  refine specR_forI (σ := σ) (D := D) (M := []) _ _ rest lx (fun _ => ctxH C Bf) (bitG3 Γ2 C od n)
    (fun i hi => ⟨if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 i) (BitVec.ofNat 64 lx)
      then 1 else 0, by simp [sev, bitG3, Env.get, hLa], ?_⟩) (fun i hi => ?_) hr
  · have e := word_lt_iff i lx (by unfold B; omega) (by unfold B; omega)
    by_cases h' : i < lx
    · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e.mpr h', h']
    · have : ¬ BitVec.ofNat 64 i < BitVec.ofNat 64 lx := fun x => h' (e.mp x)
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this, h']
  refine step_seq (step_heapLoadI' (C := ctxH C Bf) tU (vv tQo) (od + 1 + i) _ (hW i hi) du
    (by simp [bitG3]; rfl)) ?_
  refine step_seq (step_assignI tL bitTrimE (BitVec.ofNat 64 (limbs (n % B ^ (i + 1))).length) dl ?_) ?_
  · simp only [bitTrimE, sev, sev_vv, Env.get_cons, bitG3]
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [len_mod_succ, ← trim_word _ i _ (Nat.mod_lt _ Bpos)]
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  refine step_seq (step_assignI tQo _ (cellA C (od + 1 + i + 1)) dq (by simp [sev, bitG3]; exact cellA_add8 C _)) ?_
  refine step_mono (step_assignI tK _ (BitVec.ofNat 64 (i + 1)) dk (by simp [sev, bitG3]; exact word_add1_eq i))
    (fun _ h => h) (fun t ht => inv_envMono ht (fun z v hz => ?_))
  simp only [bitG3, Env.get_cons] at hz ⊢
  by_cases e1 : z = tK
  · subst e1; simp_all
  by_cases e2 : z = tQo
  · subst e2; simp_all [Nat.add_assoc]
  by_cases e3 : z = tL
  · subst e3; simp_all
  simp only [e1, e2, e3, ite_false] at hz
  have f1 : z ≠ tU := by intro e; subst e; rw [hn] at hz; simp at hz
  simp [e1, e2, e3, f1, hz]

theorem bit_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ bitLocals → (ctxEnv C ++ bitParams.zip vals).get x = none :=
  Knot.params_none C bitLocals bitParams vals (by decide) (by decide)

theorem bit_spec (o : BitOp) (C : Ctx) (hok : CtxOK C) (s : AState) (x y : Nat) (oa ob : Nat)
    (hba : BlkAt C.H oa (limbs x)) (hbb : BlkAt C.H ob (limbs y)) (hxy : (limbs y).length ≤ (limbs x).length)
    (h61 : (limbs x).length < 2 ^ 60) :
    SpecR (σ := σ) (Pre C s (bitParams.zip [cellA C oa, cellA C ob])) (bitBody o C) s (pure (o.f x y) : AM Nat)
      (PostH C s) := by
  refine specR_prologue (postH_locals C s) (bit_none C _) ?_
  unfold bitCore
  have hla0 : C.H[oa]? = some (BitVec.ofNat 64 (limbs x).length) := by simpa using hba.1
  have hlb0 : C.H[ob]? = some (BitVec.ofNat 64 (limbs y).length) := by simpa using hbb.1
  refine UD.specR_heapLoadI' tLa (vv tX) oa _ hla0 (by decide) (by simp +decide [Env.get, bitParams, ctxEnv]) ?_
  refine UD.specR_heapLoadI' tLb (vv tY) ob _ hlb0 (by decide) (by simp +decide [Env.get, bitParams, ctxEnv]) ?_
  refine specR_allocI tO (.panop .mul [.op .add [vv tLa, .const 2], .const 8]) ((limbs x).length + 2) (by omega)
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
  refine specR_assignI tQa _ (cellA C (oa + 1)) (by decide) (by simp [sev, Env.get, bitParams, ctxEnv]; exact cellA_add8 C _) ?_
  refine specR_assignI tQb _ (cellA C (ob + 1)) (by decide) (by simp [sev, Env.get, bitParams, ctxEnv]; exact cellA_add8 C _) ?_
  refine specR_assignI tQo _ (cellA C (H'.length + 1)) (by decide) (by simp [sev, Env.get]; exact cellA_add8 C _) ?_
  refine specR_assignI tB (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
  refine specR_assignI tI (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
  let Γ0 : Env := [(tLa, BitVec.ofNat 64 (limbs x).length), (tLb, BitVec.ofNat 64 (limbs y).length),
    (tO, cellA C H'.length)]
  refine specR_envWeak (Γb := bitG1 Γ0 C H'.length oa ob x y 0) (fun z v hz => ?_) ?_
  · simp only [bitG1, Γ0, Env.get_cons, bor_zero, Nat.add_zero] at hz ⊢
    by_cases e1 : z = tI
    · subst e1; simpa using hz
    by_cases e2 : z = tB
    · subst e2; simpa using hz
    by_cases e3 : z = tQo
    · subst e3; simpa using hz
    by_cases e4 : z = tQb
    · subst e4; simpa using hz
    by_cases e5 : z = tQa
    · subst e5; simpa using hz
    by_cases e6 : z = tLa
    · subst e6; simpa using hz
    by_cases e7 : z = tLb
    · subst e7; simpa using hz
    by_cases e8 : z = tO
    · subst e8; simpa using hz
    simp [e1, e2, e3, e4, e5, e6, e7, e8, Env.get] at hz
  refine bit_loop1 o hok x y B0 H'.length oa ob hxy hba' hbb' (by omega) (by omega) (by rw [hB0]; omega) (by omega)
    (by decide) (by simp [Γ0]) (by simp [Γ0, Env.get]) ?_
  refine specR_envWeak (Γb := bitG2 Γ0 C H'.length oa x y (limbs y).length 0) (fun z v hz => ?_) ?_
  · simp only [bitG1, bitG2, Env.get_cons, Nat.add_zero] at hz ⊢
    by_cases e1 : z = tI
    · subst e1; simpa using hz
    by_cases e2 : z = tB
    · subst e2; simpa using hz
    by_cases e3 : z = tQo
    · subst e3; simpa using hz
    by_cases e5 : z = tQa
    · subst e5; simpa using hz
    have e4 : z ≠ tQb := by intro e; subst e; simp [Γ0, Env.get] at hz
    simp [e1, e2, e3, e4, e5] at hz ⊢; exact hz
  refine bit_loop2 o hok x y B0 H'.length oa hxy hba' (by omega) (by rw [hB0]; omega) (by omega) (by decide)
    (by simp [Γ0]) (by simp [Γ0, Env.get]) ?_
  have hly : (limbs y).length + ((limbs x).length - (limbs y).length) = (limbs x).length := by omega
  -- the trim scan
  refine specR_assignI tK (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
  refine specR_assignI tL (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
  refine specR_assignI tQo _ (cellA C (H'.length + 1)) (by decide) (by simp [sev, bitG2, Γ0]; exact cellA_add8 C _) ?_
  let Bf := fillI B0 (bitW o x y (limbs x).length) (H'.length + 1) (limbs x).length
  have hlf := fillI_length B0 (bitW o x y (limbs x).length) (H'.length + 1)
  have hWf : ∀ k, k < (limbs x).length → Bf[H'.length + 1 + k]? = some (BitVec.ofNat 64 ((o.f x y) / B ^ k % B)) := by
    intro k hk
    rw [fillI_get?, if_pos ⟨by omega, by omega, by rw [hB0]; omega⟩]
    simp [show H'.length + 1 + k - (H'.length + 1) = k by omega, List.getD_eq_getElem?_getD, bitW_get o x y _ k hk]
  refine specR_envWeak (Γb := bitG3 Γ0 C H'.length (o.f x y) 0) (fun z v hz => ?_) ?_
  · simp only [bitG3, bitG2, Γ0, Env.get_cons, Nat.pow_zero, Nat.mod_one, Nat.add_zero] at hz ⊢
    by_cases e1 : z = tK
    · subst e1; simpa using hz
    by_cases e2 : z = tQo
    · subst e2; simpa using hz
    by_cases e3 : z = tL
    · subst e3; simp at hz ⊢; rw [← hz, limbs_zero]; rfl
    simp only [e1, e2, e3, ite_false] at hz ⊢
    by_cases f1 : z = tLa
    · subst f1; simpa using hz
    by_cases f2 : z = tLb
    · subst f2; simpa using hz
    by_cases f3 : z = tO
    · subst f3; simpa using hz
    simp [f1, f2, f3, Env.get] at hz
  refine bit_loop3 (o.f x y) (limbs x).length Bf (bitW o x y (limbs x).length) H'.length hWf (by omega) (by decide)
    (by simp [Γ0]) (by simp [Γ0, Env.get]) ?_
  have hxB : x < B ^ (limbs x).length := (limbs_length_lt_iff x _).mp (Nat.le_refl _)
  have hyB : y < B ^ (limbs x).length :=
    Nat.lt_of_lt_of_le ((limbs_length_lt_iff y _).mp (Nat.le_refl _)) (Nat.pow_le_pow_right Bpos hxy)
  have hpw : B ^ (limbs x).length = 2 ^ (64 * (limbs x).length) := by rw [Nat.pow_mul]
  have hfB : o.f x y < B ^ (limbs x).length := by
    rw [hpw] at hxB hyB ⊢; exact o.lt x y _ hxB hyB
  have hmod : (o.f x y) % B ^ (limbs x).length = o.f x y := Nat.mod_eq_of_lt hfB
  have hj2 : H'.length < (ctxH C Bf).H.length := by show _ < Bf.length; rw [hlf, hB0]; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv tO) (vv tL) _ hj2 (BitVec.ofNat 64 (limbs (o.f x y)).length)
    (by simp [bitG3, Γ0]; rfl) (by simp [bitG3, hmod]) ?_
  refine specR_returnI _ (cellA C H'.length) (by simp [bitG3, Γ0]) (fun t ht => ?_)
  refine ⟨_, H'.length, ?_, rfl, ?_, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
  · exact prefix_set_ge (CV.prefix_fillI _ _ _ C.H (by omega) (hpre.trans (List.prefix_append _ _)) _) _ hpl _
  · have hlen := (limbs_length_lt_iff (o.f x y) (limbs x).length).mpr hfB
    constructor
    · rw [List.getElem?_set_self (by show H'.length < Bf.length; rw [hlf, hB0]; omega)]
    · intro i hi
      rw [List.getElem?_set_ne (by omega)]
      show Bf[H'.length + 1 + i]? = _
      rw [hWf i (by omega), limbs_getElem (o.f x y) i hi]

end

end ConPanqueque.T.Big
