import ConPanqueque.T.Core.IotaIndex
import ConPanqueque.T.Core.CtorTarget
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `defeqSpine`: the same-head congruence

Both heads the same stored constant with equal argument counts and equal level lists: the arguments
pairwise, **last to first** (`defEqList` on the reversed spines). `dlr` is `defEqList` walking two runs of
cells downwards (a last cell and a count each); the argument blocks come from `getAppArgs`.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def dsA := ofString "dsp_a"
def dsB := ofString "dsp_b"
def dsH := ofString "dsp_h"
def dsN := ofString "dsp_n"
def dsU := ofString "dsp_u"
def dsH2 := ofString "dsp_h2"
def dsN2 := ofString "dsp_n2"
def dsU2 := ofString "dsp_u2"
def dsXa := ofString "dsp_xa"
def dsXb := ofString "dsp_xb"
def dsLa := ofString "dsp_la"
def dsLb := ofString "dsp_lb"
def dsQ := ofString "dsp_q"
def dsR := ofString "dsp_r"
def fDlr := ofString "defEqListRev"
def fDsp := ofString "defeqSpine"

@[simp] theorem dsp_dsA_ne_dsB : dsA ≠ dsB := by decide
@[simp] theorem dsp_dsA_ne_dsH : dsA ≠ dsH := by decide
@[simp] theorem dsp_dsA_ne_dsN : dsA ≠ dsN := by decide
@[simp] theorem dsp_dsA_ne_dsU : dsA ≠ dsU := by decide
@[simp] theorem dsp_dsA_ne_dsH2 : dsA ≠ dsH2 := by decide
@[simp] theorem dsp_dsA_ne_dsN2 : dsA ≠ dsN2 := by decide
@[simp] theorem dsp_dsA_ne_dsU2 : dsA ≠ dsU2 := by decide
@[simp] theorem dsp_dsA_ne_dsXa : dsA ≠ dsXa := by decide
@[simp] theorem dsp_dsA_ne_dsXb : dsA ≠ dsXb := by decide
@[simp] theorem dsp_dsA_ne_dsLa : dsA ≠ dsLa := by decide
@[simp] theorem dsp_dsA_ne_dsLb : dsA ≠ dsLb := by decide
@[simp] theorem dsp_dsA_ne_dsQ : dsA ≠ dsQ := by decide
@[simp] theorem dsp_dsA_ne_dsR : dsA ≠ dsR := by decide
@[simp] theorem dsp_dsA_ne_lFl : dsA ≠ lFl := by decide
@[simp] theorem dsp_lFl_ne_dsA : lFl ≠ dsA := by decide
@[simp] theorem dsp_dsA_ne_lDh : dsA ≠ lDh := by decide
@[simp] theorem dsp_lDh_ne_dsA : lDh ≠ dsA := by decide
@[simp] theorem dsp_dsA_ne_lDt : dsA ≠ lDt := by decide
@[simp] theorem dsp_lDt_ne_dsA : lDt ≠ dsA := by decide
@[simp] theorem dsp_dsA_ne_lDg : dsA ≠ lDg := by decide
@[simp] theorem dsp_lDg_ne_dsA : lDg ≠ dsA := by decide
@[simp] theorem dsp_dsA_ne_lDi : dsA ≠ lDi := by decide
@[simp] theorem dsp_lDi_ne_dsA : lDi ≠ dsA := by decide
@[simp] theorem dsp_dsA_ne_lRp : dsA ≠ lRp := by decide
@[simp] theorem dsp_lRp_ne_dsA : lRp ≠ dsA := by decide
@[simp] theorem dsp_dsA_ne_lRn : dsA ≠ lRn := by decide
@[simp] theorem dsp_lRn_ne_dsA : lRn ≠ dsA := by decide
@[simp] theorem dsp_dsA_ne_lFle : dsA ≠ lFle := by decide
@[simp] theorem dsp_lFle_ne_dsA : lFle ≠ dsA := by decide
@[simp] theorem dsp_dsA_ne_lKb : dsA ≠ lKb := by decide
@[simp] theorem dsp_lKb_ne_dsA : lKb ≠ dsA := by decide
@[simp] theorem dsp_dsA_ne_lDir : dsA ≠ lDir := by decide
@[simp] theorem dsp_lDir_ne_dsA : lDir ≠ dsA := by decide
@[simp] theorem dsp_dsA_ne_lFln : dsA ≠ lFln := by decide
@[simp] theorem dsp_lFln_ne_dsA : lFln ≠ dsA := by decide
@[simp] theorem dsp_dsA_ne_lFll : dsA ≠ lFll := by decide
@[simp] theorem dsp_lFll_ne_dsA : lFll ≠ dsA := by decide
@[simp] theorem dsp_dsA_ne_lFls : dsA ≠ lFls := by decide
@[simp] theorem dsp_lFls_ne_dsA : lFls ≠ dsA := by decide
@[simp] theorem dsp_dsA_ne_kFu : dsA ≠ kFu := by decide
@[simp] theorem dsp_kFu_ne_dsA : kFu ≠ dsA := by decide
@[simp] theorem dsp_dsA_ne_kD : dsA ≠ kD := by decide
@[simp] theorem dsp_kD_ne_dsA : kD ≠ dsA := by decide
@[simp] theorem dsp_dsB_ne_dsA : dsB ≠ dsA := by decide
@[simp] theorem dsp_dsB_ne_dsH : dsB ≠ dsH := by decide
@[simp] theorem dsp_dsB_ne_dsN : dsB ≠ dsN := by decide
@[simp] theorem dsp_dsB_ne_dsU : dsB ≠ dsU := by decide
@[simp] theorem dsp_dsB_ne_dsH2 : dsB ≠ dsH2 := by decide
@[simp] theorem dsp_dsB_ne_dsN2 : dsB ≠ dsN2 := by decide
@[simp] theorem dsp_dsB_ne_dsU2 : dsB ≠ dsU2 := by decide
@[simp] theorem dsp_dsB_ne_dsXa : dsB ≠ dsXa := by decide
@[simp] theorem dsp_dsB_ne_dsXb : dsB ≠ dsXb := by decide
@[simp] theorem dsp_dsB_ne_dsLa : dsB ≠ dsLa := by decide
@[simp] theorem dsp_dsB_ne_dsLb : dsB ≠ dsLb := by decide
@[simp] theorem dsp_dsB_ne_dsQ : dsB ≠ dsQ := by decide
@[simp] theorem dsp_dsB_ne_dsR : dsB ≠ dsR := by decide
@[simp] theorem dsp_dsB_ne_lFl : dsB ≠ lFl := by decide
@[simp] theorem dsp_lFl_ne_dsB : lFl ≠ dsB := by decide
@[simp] theorem dsp_dsB_ne_lDh : dsB ≠ lDh := by decide
@[simp] theorem dsp_lDh_ne_dsB : lDh ≠ dsB := by decide
@[simp] theorem dsp_dsB_ne_lDt : dsB ≠ lDt := by decide
@[simp] theorem dsp_lDt_ne_dsB : lDt ≠ dsB := by decide
@[simp] theorem dsp_dsB_ne_lDg : dsB ≠ lDg := by decide
@[simp] theorem dsp_lDg_ne_dsB : lDg ≠ dsB := by decide
@[simp] theorem dsp_dsB_ne_lDi : dsB ≠ lDi := by decide
@[simp] theorem dsp_lDi_ne_dsB : lDi ≠ dsB := by decide
@[simp] theorem dsp_dsB_ne_lRp : dsB ≠ lRp := by decide
@[simp] theorem dsp_lRp_ne_dsB : lRp ≠ dsB := by decide
@[simp] theorem dsp_dsB_ne_lRn : dsB ≠ lRn := by decide
@[simp] theorem dsp_lRn_ne_dsB : lRn ≠ dsB := by decide
@[simp] theorem dsp_dsB_ne_lFle : dsB ≠ lFle := by decide
@[simp] theorem dsp_lFle_ne_dsB : lFle ≠ dsB := by decide
@[simp] theorem dsp_dsB_ne_lKb : dsB ≠ lKb := by decide
@[simp] theorem dsp_lKb_ne_dsB : lKb ≠ dsB := by decide
@[simp] theorem dsp_dsB_ne_lDir : dsB ≠ lDir := by decide
@[simp] theorem dsp_lDir_ne_dsB : lDir ≠ dsB := by decide
@[simp] theorem dsp_dsB_ne_lFln : dsB ≠ lFln := by decide
@[simp] theorem dsp_lFln_ne_dsB : lFln ≠ dsB := by decide
@[simp] theorem dsp_dsB_ne_lFll : dsB ≠ lFll := by decide
@[simp] theorem dsp_lFll_ne_dsB : lFll ≠ dsB := by decide
@[simp] theorem dsp_dsB_ne_lFls : dsB ≠ lFls := by decide
@[simp] theorem dsp_lFls_ne_dsB : lFls ≠ dsB := by decide
@[simp] theorem dsp_dsB_ne_kFu : dsB ≠ kFu := by decide
@[simp] theorem dsp_kFu_ne_dsB : kFu ≠ dsB := by decide
@[simp] theorem dsp_dsB_ne_kD : dsB ≠ kD := by decide
@[simp] theorem dsp_kD_ne_dsB : kD ≠ dsB := by decide
@[simp] theorem dsp_dsH_ne_dsA : dsH ≠ dsA := by decide
@[simp] theorem dsp_dsH_ne_dsB : dsH ≠ dsB := by decide
@[simp] theorem dsp_dsH_ne_dsN : dsH ≠ dsN := by decide
@[simp] theorem dsp_dsH_ne_dsU : dsH ≠ dsU := by decide
@[simp] theorem dsp_dsH_ne_dsH2 : dsH ≠ dsH2 := by decide
@[simp] theorem dsp_dsH_ne_dsN2 : dsH ≠ dsN2 := by decide
@[simp] theorem dsp_dsH_ne_dsU2 : dsH ≠ dsU2 := by decide
@[simp] theorem dsp_dsH_ne_dsXa : dsH ≠ dsXa := by decide
@[simp] theorem dsp_dsH_ne_dsXb : dsH ≠ dsXb := by decide
@[simp] theorem dsp_dsH_ne_dsLa : dsH ≠ dsLa := by decide
@[simp] theorem dsp_dsH_ne_dsLb : dsH ≠ dsLb := by decide
@[simp] theorem dsp_dsH_ne_dsQ : dsH ≠ dsQ := by decide
@[simp] theorem dsp_dsH_ne_dsR : dsH ≠ dsR := by decide
@[simp] theorem dsp_dsH_ne_lFl : dsH ≠ lFl := by decide
@[simp] theorem dsp_lFl_ne_dsH : lFl ≠ dsH := by decide
@[simp] theorem dsp_dsH_ne_lDh : dsH ≠ lDh := by decide
@[simp] theorem dsp_lDh_ne_dsH : lDh ≠ dsH := by decide
@[simp] theorem dsp_dsH_ne_lDt : dsH ≠ lDt := by decide
@[simp] theorem dsp_lDt_ne_dsH : lDt ≠ dsH := by decide
@[simp] theorem dsp_dsH_ne_lDg : dsH ≠ lDg := by decide
@[simp] theorem dsp_lDg_ne_dsH : lDg ≠ dsH := by decide
@[simp] theorem dsp_dsH_ne_lDi : dsH ≠ lDi := by decide
@[simp] theorem dsp_lDi_ne_dsH : lDi ≠ dsH := by decide
@[simp] theorem dsp_dsH_ne_lRp : dsH ≠ lRp := by decide
@[simp] theorem dsp_lRp_ne_dsH : lRp ≠ dsH := by decide
@[simp] theorem dsp_dsH_ne_lRn : dsH ≠ lRn := by decide
@[simp] theorem dsp_lRn_ne_dsH : lRn ≠ dsH := by decide
@[simp] theorem dsp_dsH_ne_lFle : dsH ≠ lFle := by decide
@[simp] theorem dsp_lFle_ne_dsH : lFle ≠ dsH := by decide
@[simp] theorem dsp_dsH_ne_lKb : dsH ≠ lKb := by decide
@[simp] theorem dsp_lKb_ne_dsH : lKb ≠ dsH := by decide
@[simp] theorem dsp_dsH_ne_lDir : dsH ≠ lDir := by decide
@[simp] theorem dsp_lDir_ne_dsH : lDir ≠ dsH := by decide
@[simp] theorem dsp_dsH_ne_lFln : dsH ≠ lFln := by decide
@[simp] theorem dsp_lFln_ne_dsH : lFln ≠ dsH := by decide
@[simp] theorem dsp_dsH_ne_lFll : dsH ≠ lFll := by decide
@[simp] theorem dsp_lFll_ne_dsH : lFll ≠ dsH := by decide
@[simp] theorem dsp_dsH_ne_lFls : dsH ≠ lFls := by decide
@[simp] theorem dsp_lFls_ne_dsH : lFls ≠ dsH := by decide
@[simp] theorem dsp_dsH_ne_kFu : dsH ≠ kFu := by decide
@[simp] theorem dsp_kFu_ne_dsH : kFu ≠ dsH := by decide
@[simp] theorem dsp_dsH_ne_kD : dsH ≠ kD := by decide
@[simp] theorem dsp_kD_ne_dsH : kD ≠ dsH := by decide
@[simp] theorem dsp_dsN_ne_dsA : dsN ≠ dsA := by decide
@[simp] theorem dsp_dsN_ne_dsB : dsN ≠ dsB := by decide
@[simp] theorem dsp_dsN_ne_dsH : dsN ≠ dsH := by decide
@[simp] theorem dsp_dsN_ne_dsU : dsN ≠ dsU := by decide
@[simp] theorem dsp_dsN_ne_dsH2 : dsN ≠ dsH2 := by decide
@[simp] theorem dsp_dsN_ne_dsN2 : dsN ≠ dsN2 := by decide
@[simp] theorem dsp_dsN_ne_dsU2 : dsN ≠ dsU2 := by decide
@[simp] theorem dsp_dsN_ne_dsXa : dsN ≠ dsXa := by decide
@[simp] theorem dsp_dsN_ne_dsXb : dsN ≠ dsXb := by decide
@[simp] theorem dsp_dsN_ne_dsLa : dsN ≠ dsLa := by decide
@[simp] theorem dsp_dsN_ne_dsLb : dsN ≠ dsLb := by decide
@[simp] theorem dsp_dsN_ne_dsQ : dsN ≠ dsQ := by decide
@[simp] theorem dsp_dsN_ne_dsR : dsN ≠ dsR := by decide
@[simp] theorem dsp_dsN_ne_lFl : dsN ≠ lFl := by decide
@[simp] theorem dsp_lFl_ne_dsN : lFl ≠ dsN := by decide
@[simp] theorem dsp_dsN_ne_lDh : dsN ≠ lDh := by decide
@[simp] theorem dsp_lDh_ne_dsN : lDh ≠ dsN := by decide
@[simp] theorem dsp_dsN_ne_lDt : dsN ≠ lDt := by decide
@[simp] theorem dsp_lDt_ne_dsN : lDt ≠ dsN := by decide
@[simp] theorem dsp_dsN_ne_lDg : dsN ≠ lDg := by decide
@[simp] theorem dsp_lDg_ne_dsN : lDg ≠ dsN := by decide
@[simp] theorem dsp_dsN_ne_lDi : dsN ≠ lDi := by decide
@[simp] theorem dsp_lDi_ne_dsN : lDi ≠ dsN := by decide
@[simp] theorem dsp_dsN_ne_lRp : dsN ≠ lRp := by decide
@[simp] theorem dsp_lRp_ne_dsN : lRp ≠ dsN := by decide
@[simp] theorem dsp_dsN_ne_lRn : dsN ≠ lRn := by decide
@[simp] theorem dsp_lRn_ne_dsN : lRn ≠ dsN := by decide
@[simp] theorem dsp_dsN_ne_lFle : dsN ≠ lFle := by decide
@[simp] theorem dsp_lFle_ne_dsN : lFle ≠ dsN := by decide
@[simp] theorem dsp_dsN_ne_lKb : dsN ≠ lKb := by decide
@[simp] theorem dsp_lKb_ne_dsN : lKb ≠ dsN := by decide
@[simp] theorem dsp_dsN_ne_lDir : dsN ≠ lDir := by decide
@[simp] theorem dsp_lDir_ne_dsN : lDir ≠ dsN := by decide
@[simp] theorem dsp_dsN_ne_lFln : dsN ≠ lFln := by decide
@[simp] theorem dsp_lFln_ne_dsN : lFln ≠ dsN := by decide
@[simp] theorem dsp_dsN_ne_lFll : dsN ≠ lFll := by decide
@[simp] theorem dsp_lFll_ne_dsN : lFll ≠ dsN := by decide
@[simp] theorem dsp_dsN_ne_lFls : dsN ≠ lFls := by decide
@[simp] theorem dsp_lFls_ne_dsN : lFls ≠ dsN := by decide
@[simp] theorem dsp_dsN_ne_kFu : dsN ≠ kFu := by decide
@[simp] theorem dsp_kFu_ne_dsN : kFu ≠ dsN := by decide
@[simp] theorem dsp_dsN_ne_kD : dsN ≠ kD := by decide
@[simp] theorem dsp_kD_ne_dsN : kD ≠ dsN := by decide
@[simp] theorem dsp_dsU_ne_dsA : dsU ≠ dsA := by decide
@[simp] theorem dsp_dsU_ne_dsB : dsU ≠ dsB := by decide
@[simp] theorem dsp_dsU_ne_dsH : dsU ≠ dsH := by decide
@[simp] theorem dsp_dsU_ne_dsN : dsU ≠ dsN := by decide
@[simp] theorem dsp_dsU_ne_dsH2 : dsU ≠ dsH2 := by decide
@[simp] theorem dsp_dsU_ne_dsN2 : dsU ≠ dsN2 := by decide
@[simp] theorem dsp_dsU_ne_dsU2 : dsU ≠ dsU2 := by decide
@[simp] theorem dsp_dsU_ne_dsXa : dsU ≠ dsXa := by decide
@[simp] theorem dsp_dsU_ne_dsXb : dsU ≠ dsXb := by decide
@[simp] theorem dsp_dsU_ne_dsLa : dsU ≠ dsLa := by decide
@[simp] theorem dsp_dsU_ne_dsLb : dsU ≠ dsLb := by decide
@[simp] theorem dsp_dsU_ne_dsQ : dsU ≠ dsQ := by decide
@[simp] theorem dsp_dsU_ne_dsR : dsU ≠ dsR := by decide
@[simp] theorem dsp_dsU_ne_lFl : dsU ≠ lFl := by decide
@[simp] theorem dsp_lFl_ne_dsU : lFl ≠ dsU := by decide
@[simp] theorem dsp_dsU_ne_lDh : dsU ≠ lDh := by decide
@[simp] theorem dsp_lDh_ne_dsU : lDh ≠ dsU := by decide
@[simp] theorem dsp_dsU_ne_lDt : dsU ≠ lDt := by decide
@[simp] theorem dsp_lDt_ne_dsU : lDt ≠ dsU := by decide
@[simp] theorem dsp_dsU_ne_lDg : dsU ≠ lDg := by decide
@[simp] theorem dsp_lDg_ne_dsU : lDg ≠ dsU := by decide
@[simp] theorem dsp_dsU_ne_lDi : dsU ≠ lDi := by decide
@[simp] theorem dsp_lDi_ne_dsU : lDi ≠ dsU := by decide
@[simp] theorem dsp_dsU_ne_lRp : dsU ≠ lRp := by decide
@[simp] theorem dsp_lRp_ne_dsU : lRp ≠ dsU := by decide
@[simp] theorem dsp_dsU_ne_lRn : dsU ≠ lRn := by decide
@[simp] theorem dsp_lRn_ne_dsU : lRn ≠ dsU := by decide
@[simp] theorem dsp_dsU_ne_lFle : dsU ≠ lFle := by decide
@[simp] theorem dsp_lFle_ne_dsU : lFle ≠ dsU := by decide
@[simp] theorem dsp_dsU_ne_lKb : dsU ≠ lKb := by decide
@[simp] theorem dsp_lKb_ne_dsU : lKb ≠ dsU := by decide
@[simp] theorem dsp_dsU_ne_lDir : dsU ≠ lDir := by decide
@[simp] theorem dsp_lDir_ne_dsU : lDir ≠ dsU := by decide
@[simp] theorem dsp_dsU_ne_lFln : dsU ≠ lFln := by decide
@[simp] theorem dsp_lFln_ne_dsU : lFln ≠ dsU := by decide
@[simp] theorem dsp_dsU_ne_lFll : dsU ≠ lFll := by decide
@[simp] theorem dsp_lFll_ne_dsU : lFll ≠ dsU := by decide
@[simp] theorem dsp_dsU_ne_lFls : dsU ≠ lFls := by decide
@[simp] theorem dsp_lFls_ne_dsU : lFls ≠ dsU := by decide
@[simp] theorem dsp_dsU_ne_kFu : dsU ≠ kFu := by decide
@[simp] theorem dsp_kFu_ne_dsU : kFu ≠ dsU := by decide
@[simp] theorem dsp_dsU_ne_kD : dsU ≠ kD := by decide
@[simp] theorem dsp_kD_ne_dsU : kD ≠ dsU := by decide
@[simp] theorem dsp_dsH2_ne_dsA : dsH2 ≠ dsA := by decide
@[simp] theorem dsp_dsH2_ne_dsB : dsH2 ≠ dsB := by decide
@[simp] theorem dsp_dsH2_ne_dsH : dsH2 ≠ dsH := by decide
@[simp] theorem dsp_dsH2_ne_dsN : dsH2 ≠ dsN := by decide
@[simp] theorem dsp_dsH2_ne_dsU : dsH2 ≠ dsU := by decide
@[simp] theorem dsp_dsH2_ne_dsN2 : dsH2 ≠ dsN2 := by decide
@[simp] theorem dsp_dsH2_ne_dsU2 : dsH2 ≠ dsU2 := by decide
@[simp] theorem dsp_dsH2_ne_dsXa : dsH2 ≠ dsXa := by decide
@[simp] theorem dsp_dsH2_ne_dsXb : dsH2 ≠ dsXb := by decide
@[simp] theorem dsp_dsH2_ne_dsLa : dsH2 ≠ dsLa := by decide
@[simp] theorem dsp_dsH2_ne_dsLb : dsH2 ≠ dsLb := by decide
@[simp] theorem dsp_dsH2_ne_dsQ : dsH2 ≠ dsQ := by decide
@[simp] theorem dsp_dsH2_ne_dsR : dsH2 ≠ dsR := by decide
@[simp] theorem dsp_dsH2_ne_lFl : dsH2 ≠ lFl := by decide
@[simp] theorem dsp_lFl_ne_dsH2 : lFl ≠ dsH2 := by decide
@[simp] theorem dsp_dsH2_ne_lDh : dsH2 ≠ lDh := by decide
@[simp] theorem dsp_lDh_ne_dsH2 : lDh ≠ dsH2 := by decide
@[simp] theorem dsp_dsH2_ne_lDt : dsH2 ≠ lDt := by decide
@[simp] theorem dsp_lDt_ne_dsH2 : lDt ≠ dsH2 := by decide
@[simp] theorem dsp_dsH2_ne_lDg : dsH2 ≠ lDg := by decide
@[simp] theorem dsp_lDg_ne_dsH2 : lDg ≠ dsH2 := by decide
@[simp] theorem dsp_dsH2_ne_lDi : dsH2 ≠ lDi := by decide
@[simp] theorem dsp_lDi_ne_dsH2 : lDi ≠ dsH2 := by decide
@[simp] theorem dsp_dsH2_ne_lRp : dsH2 ≠ lRp := by decide
@[simp] theorem dsp_lRp_ne_dsH2 : lRp ≠ dsH2 := by decide
@[simp] theorem dsp_dsH2_ne_lRn : dsH2 ≠ lRn := by decide
@[simp] theorem dsp_lRn_ne_dsH2 : lRn ≠ dsH2 := by decide
@[simp] theorem dsp_dsH2_ne_lFle : dsH2 ≠ lFle := by decide
@[simp] theorem dsp_lFle_ne_dsH2 : lFle ≠ dsH2 := by decide
@[simp] theorem dsp_dsH2_ne_lKb : dsH2 ≠ lKb := by decide
@[simp] theorem dsp_lKb_ne_dsH2 : lKb ≠ dsH2 := by decide
@[simp] theorem dsp_dsH2_ne_lDir : dsH2 ≠ lDir := by decide
@[simp] theorem dsp_lDir_ne_dsH2 : lDir ≠ dsH2 := by decide
@[simp] theorem dsp_dsH2_ne_lFln : dsH2 ≠ lFln := by decide
@[simp] theorem dsp_lFln_ne_dsH2 : lFln ≠ dsH2 := by decide
@[simp] theorem dsp_dsH2_ne_lFll : dsH2 ≠ lFll := by decide
@[simp] theorem dsp_lFll_ne_dsH2 : lFll ≠ dsH2 := by decide
@[simp] theorem dsp_dsH2_ne_lFls : dsH2 ≠ lFls := by decide
@[simp] theorem dsp_lFls_ne_dsH2 : lFls ≠ dsH2 := by decide
@[simp] theorem dsp_dsH2_ne_kFu : dsH2 ≠ kFu := by decide
@[simp] theorem dsp_kFu_ne_dsH2 : kFu ≠ dsH2 := by decide
@[simp] theorem dsp_dsH2_ne_kD : dsH2 ≠ kD := by decide
@[simp] theorem dsp_kD_ne_dsH2 : kD ≠ dsH2 := by decide
@[simp] theorem dsp_dsN2_ne_dsA : dsN2 ≠ dsA := by decide
@[simp] theorem dsp_dsN2_ne_dsB : dsN2 ≠ dsB := by decide
@[simp] theorem dsp_dsN2_ne_dsH : dsN2 ≠ dsH := by decide
@[simp] theorem dsp_dsN2_ne_dsN : dsN2 ≠ dsN := by decide
@[simp] theorem dsp_dsN2_ne_dsU : dsN2 ≠ dsU := by decide
@[simp] theorem dsp_dsN2_ne_dsH2 : dsN2 ≠ dsH2 := by decide
@[simp] theorem dsp_dsN2_ne_dsU2 : dsN2 ≠ dsU2 := by decide
@[simp] theorem dsp_dsN2_ne_dsXa : dsN2 ≠ dsXa := by decide
@[simp] theorem dsp_dsN2_ne_dsXb : dsN2 ≠ dsXb := by decide
@[simp] theorem dsp_dsN2_ne_dsLa : dsN2 ≠ dsLa := by decide
@[simp] theorem dsp_dsN2_ne_dsLb : dsN2 ≠ dsLb := by decide
@[simp] theorem dsp_dsN2_ne_dsQ : dsN2 ≠ dsQ := by decide
@[simp] theorem dsp_dsN2_ne_dsR : dsN2 ≠ dsR := by decide
@[simp] theorem dsp_dsN2_ne_lFl : dsN2 ≠ lFl := by decide
@[simp] theorem dsp_lFl_ne_dsN2 : lFl ≠ dsN2 := by decide
@[simp] theorem dsp_dsN2_ne_lDh : dsN2 ≠ lDh := by decide
@[simp] theorem dsp_lDh_ne_dsN2 : lDh ≠ dsN2 := by decide
@[simp] theorem dsp_dsN2_ne_lDt : dsN2 ≠ lDt := by decide
@[simp] theorem dsp_lDt_ne_dsN2 : lDt ≠ dsN2 := by decide
@[simp] theorem dsp_dsN2_ne_lDg : dsN2 ≠ lDg := by decide
@[simp] theorem dsp_lDg_ne_dsN2 : lDg ≠ dsN2 := by decide
@[simp] theorem dsp_dsN2_ne_lDi : dsN2 ≠ lDi := by decide
@[simp] theorem dsp_lDi_ne_dsN2 : lDi ≠ dsN2 := by decide
@[simp] theorem dsp_dsN2_ne_lRp : dsN2 ≠ lRp := by decide
@[simp] theorem dsp_lRp_ne_dsN2 : lRp ≠ dsN2 := by decide
@[simp] theorem dsp_dsN2_ne_lRn : dsN2 ≠ lRn := by decide
@[simp] theorem dsp_lRn_ne_dsN2 : lRn ≠ dsN2 := by decide
@[simp] theorem dsp_dsN2_ne_lFle : dsN2 ≠ lFle := by decide
@[simp] theorem dsp_lFle_ne_dsN2 : lFle ≠ dsN2 := by decide
@[simp] theorem dsp_dsN2_ne_lKb : dsN2 ≠ lKb := by decide
@[simp] theorem dsp_lKb_ne_dsN2 : lKb ≠ dsN2 := by decide
@[simp] theorem dsp_dsN2_ne_lDir : dsN2 ≠ lDir := by decide
@[simp] theorem dsp_lDir_ne_dsN2 : lDir ≠ dsN2 := by decide
@[simp] theorem dsp_dsN2_ne_lFln : dsN2 ≠ lFln := by decide
@[simp] theorem dsp_lFln_ne_dsN2 : lFln ≠ dsN2 := by decide
@[simp] theorem dsp_dsN2_ne_lFll : dsN2 ≠ lFll := by decide
@[simp] theorem dsp_lFll_ne_dsN2 : lFll ≠ dsN2 := by decide
@[simp] theorem dsp_dsN2_ne_lFls : dsN2 ≠ lFls := by decide
@[simp] theorem dsp_lFls_ne_dsN2 : lFls ≠ dsN2 := by decide
@[simp] theorem dsp_dsN2_ne_kFu : dsN2 ≠ kFu := by decide
@[simp] theorem dsp_kFu_ne_dsN2 : kFu ≠ dsN2 := by decide
@[simp] theorem dsp_dsN2_ne_kD : dsN2 ≠ kD := by decide
@[simp] theorem dsp_kD_ne_dsN2 : kD ≠ dsN2 := by decide
@[simp] theorem dsp_dsU2_ne_dsA : dsU2 ≠ dsA := by decide
@[simp] theorem dsp_dsU2_ne_dsB : dsU2 ≠ dsB := by decide
@[simp] theorem dsp_dsU2_ne_dsH : dsU2 ≠ dsH := by decide
@[simp] theorem dsp_dsU2_ne_dsN : dsU2 ≠ dsN := by decide
@[simp] theorem dsp_dsU2_ne_dsU : dsU2 ≠ dsU := by decide
@[simp] theorem dsp_dsU2_ne_dsH2 : dsU2 ≠ dsH2 := by decide
@[simp] theorem dsp_dsU2_ne_dsN2 : dsU2 ≠ dsN2 := by decide
@[simp] theorem dsp_dsU2_ne_dsXa : dsU2 ≠ dsXa := by decide
@[simp] theorem dsp_dsU2_ne_dsXb : dsU2 ≠ dsXb := by decide
@[simp] theorem dsp_dsU2_ne_dsLa : dsU2 ≠ dsLa := by decide
@[simp] theorem dsp_dsU2_ne_dsLb : dsU2 ≠ dsLb := by decide
@[simp] theorem dsp_dsU2_ne_dsQ : dsU2 ≠ dsQ := by decide
@[simp] theorem dsp_dsU2_ne_dsR : dsU2 ≠ dsR := by decide
@[simp] theorem dsp_dsU2_ne_lFl : dsU2 ≠ lFl := by decide
@[simp] theorem dsp_lFl_ne_dsU2 : lFl ≠ dsU2 := by decide
@[simp] theorem dsp_dsU2_ne_lDh : dsU2 ≠ lDh := by decide
@[simp] theorem dsp_lDh_ne_dsU2 : lDh ≠ dsU2 := by decide
@[simp] theorem dsp_dsU2_ne_lDt : dsU2 ≠ lDt := by decide
@[simp] theorem dsp_lDt_ne_dsU2 : lDt ≠ dsU2 := by decide
@[simp] theorem dsp_dsU2_ne_lDg : dsU2 ≠ lDg := by decide
@[simp] theorem dsp_lDg_ne_dsU2 : lDg ≠ dsU2 := by decide
@[simp] theorem dsp_dsU2_ne_lDi : dsU2 ≠ lDi := by decide
@[simp] theorem dsp_lDi_ne_dsU2 : lDi ≠ dsU2 := by decide
@[simp] theorem dsp_dsU2_ne_lRp : dsU2 ≠ lRp := by decide
@[simp] theorem dsp_lRp_ne_dsU2 : lRp ≠ dsU2 := by decide
@[simp] theorem dsp_dsU2_ne_lRn : dsU2 ≠ lRn := by decide
@[simp] theorem dsp_lRn_ne_dsU2 : lRn ≠ dsU2 := by decide
@[simp] theorem dsp_dsU2_ne_lFle : dsU2 ≠ lFle := by decide
@[simp] theorem dsp_lFle_ne_dsU2 : lFle ≠ dsU2 := by decide
@[simp] theorem dsp_dsU2_ne_lKb : dsU2 ≠ lKb := by decide
@[simp] theorem dsp_lKb_ne_dsU2 : lKb ≠ dsU2 := by decide
@[simp] theorem dsp_dsU2_ne_lDir : dsU2 ≠ lDir := by decide
@[simp] theorem dsp_lDir_ne_dsU2 : lDir ≠ dsU2 := by decide
@[simp] theorem dsp_dsU2_ne_lFln : dsU2 ≠ lFln := by decide
@[simp] theorem dsp_lFln_ne_dsU2 : lFln ≠ dsU2 := by decide
@[simp] theorem dsp_dsU2_ne_lFll : dsU2 ≠ lFll := by decide
@[simp] theorem dsp_lFll_ne_dsU2 : lFll ≠ dsU2 := by decide
@[simp] theorem dsp_dsU2_ne_lFls : dsU2 ≠ lFls := by decide
@[simp] theorem dsp_lFls_ne_dsU2 : lFls ≠ dsU2 := by decide
@[simp] theorem dsp_dsU2_ne_kFu : dsU2 ≠ kFu := by decide
@[simp] theorem dsp_kFu_ne_dsU2 : kFu ≠ dsU2 := by decide
@[simp] theorem dsp_dsU2_ne_kD : dsU2 ≠ kD := by decide
@[simp] theorem dsp_kD_ne_dsU2 : kD ≠ dsU2 := by decide
@[simp] theorem dsp_dsXa_ne_dsA : dsXa ≠ dsA := by decide
@[simp] theorem dsp_dsXa_ne_dsB : dsXa ≠ dsB := by decide
@[simp] theorem dsp_dsXa_ne_dsH : dsXa ≠ dsH := by decide
@[simp] theorem dsp_dsXa_ne_dsN : dsXa ≠ dsN := by decide
@[simp] theorem dsp_dsXa_ne_dsU : dsXa ≠ dsU := by decide
@[simp] theorem dsp_dsXa_ne_dsH2 : dsXa ≠ dsH2 := by decide
@[simp] theorem dsp_dsXa_ne_dsN2 : dsXa ≠ dsN2 := by decide
@[simp] theorem dsp_dsXa_ne_dsU2 : dsXa ≠ dsU2 := by decide
@[simp] theorem dsp_dsXa_ne_dsXb : dsXa ≠ dsXb := by decide
@[simp] theorem dsp_dsXa_ne_dsLa : dsXa ≠ dsLa := by decide
@[simp] theorem dsp_dsXa_ne_dsLb : dsXa ≠ dsLb := by decide
@[simp] theorem dsp_dsXa_ne_dsQ : dsXa ≠ dsQ := by decide
@[simp] theorem dsp_dsXa_ne_dsR : dsXa ≠ dsR := by decide
@[simp] theorem dsp_dsXa_ne_lFl : dsXa ≠ lFl := by decide
@[simp] theorem dsp_lFl_ne_dsXa : lFl ≠ dsXa := by decide
@[simp] theorem dsp_dsXa_ne_lDh : dsXa ≠ lDh := by decide
@[simp] theorem dsp_lDh_ne_dsXa : lDh ≠ dsXa := by decide
@[simp] theorem dsp_dsXa_ne_lDt : dsXa ≠ lDt := by decide
@[simp] theorem dsp_lDt_ne_dsXa : lDt ≠ dsXa := by decide
@[simp] theorem dsp_dsXa_ne_lDg : dsXa ≠ lDg := by decide
@[simp] theorem dsp_lDg_ne_dsXa : lDg ≠ dsXa := by decide
@[simp] theorem dsp_dsXa_ne_lDi : dsXa ≠ lDi := by decide
@[simp] theorem dsp_lDi_ne_dsXa : lDi ≠ dsXa := by decide
@[simp] theorem dsp_dsXa_ne_lRp : dsXa ≠ lRp := by decide
@[simp] theorem dsp_lRp_ne_dsXa : lRp ≠ dsXa := by decide
@[simp] theorem dsp_dsXa_ne_lRn : dsXa ≠ lRn := by decide
@[simp] theorem dsp_lRn_ne_dsXa : lRn ≠ dsXa := by decide
@[simp] theorem dsp_dsXa_ne_lFle : dsXa ≠ lFle := by decide
@[simp] theorem dsp_lFle_ne_dsXa : lFle ≠ dsXa := by decide
@[simp] theorem dsp_dsXa_ne_lKb : dsXa ≠ lKb := by decide
@[simp] theorem dsp_lKb_ne_dsXa : lKb ≠ dsXa := by decide
@[simp] theorem dsp_dsXa_ne_lDir : dsXa ≠ lDir := by decide
@[simp] theorem dsp_lDir_ne_dsXa : lDir ≠ dsXa := by decide
@[simp] theorem dsp_dsXa_ne_lFln : dsXa ≠ lFln := by decide
@[simp] theorem dsp_lFln_ne_dsXa : lFln ≠ dsXa := by decide
@[simp] theorem dsp_dsXa_ne_lFll : dsXa ≠ lFll := by decide
@[simp] theorem dsp_lFll_ne_dsXa : lFll ≠ dsXa := by decide
@[simp] theorem dsp_dsXa_ne_lFls : dsXa ≠ lFls := by decide
@[simp] theorem dsp_lFls_ne_dsXa : lFls ≠ dsXa := by decide
@[simp] theorem dsp_dsXa_ne_kFu : dsXa ≠ kFu := by decide
@[simp] theorem dsp_kFu_ne_dsXa : kFu ≠ dsXa := by decide
@[simp] theorem dsp_dsXa_ne_kD : dsXa ≠ kD := by decide
@[simp] theorem dsp_kD_ne_dsXa : kD ≠ dsXa := by decide
@[simp] theorem dsp_dsXb_ne_dsA : dsXb ≠ dsA := by decide
@[simp] theorem dsp_dsXb_ne_dsB : dsXb ≠ dsB := by decide
@[simp] theorem dsp_dsXb_ne_dsH : dsXb ≠ dsH := by decide
@[simp] theorem dsp_dsXb_ne_dsN : dsXb ≠ dsN := by decide
@[simp] theorem dsp_dsXb_ne_dsU : dsXb ≠ dsU := by decide
@[simp] theorem dsp_dsXb_ne_dsH2 : dsXb ≠ dsH2 := by decide
@[simp] theorem dsp_dsXb_ne_dsN2 : dsXb ≠ dsN2 := by decide
@[simp] theorem dsp_dsXb_ne_dsU2 : dsXb ≠ dsU2 := by decide
@[simp] theorem dsp_dsXb_ne_dsXa : dsXb ≠ dsXa := by decide
@[simp] theorem dsp_dsXb_ne_dsLa : dsXb ≠ dsLa := by decide
@[simp] theorem dsp_dsXb_ne_dsLb : dsXb ≠ dsLb := by decide
@[simp] theorem dsp_dsXb_ne_dsQ : dsXb ≠ dsQ := by decide
@[simp] theorem dsp_dsXb_ne_dsR : dsXb ≠ dsR := by decide
@[simp] theorem dsp_dsXb_ne_lFl : dsXb ≠ lFl := by decide
@[simp] theorem dsp_lFl_ne_dsXb : lFl ≠ dsXb := by decide
@[simp] theorem dsp_dsXb_ne_lDh : dsXb ≠ lDh := by decide
@[simp] theorem dsp_lDh_ne_dsXb : lDh ≠ dsXb := by decide
@[simp] theorem dsp_dsXb_ne_lDt : dsXb ≠ lDt := by decide
@[simp] theorem dsp_lDt_ne_dsXb : lDt ≠ dsXb := by decide
@[simp] theorem dsp_dsXb_ne_lDg : dsXb ≠ lDg := by decide
@[simp] theorem dsp_lDg_ne_dsXb : lDg ≠ dsXb := by decide
@[simp] theorem dsp_dsXb_ne_lDi : dsXb ≠ lDi := by decide
@[simp] theorem dsp_lDi_ne_dsXb : lDi ≠ dsXb := by decide
@[simp] theorem dsp_dsXb_ne_lRp : dsXb ≠ lRp := by decide
@[simp] theorem dsp_lRp_ne_dsXb : lRp ≠ dsXb := by decide
@[simp] theorem dsp_dsXb_ne_lRn : dsXb ≠ lRn := by decide
@[simp] theorem dsp_lRn_ne_dsXb : lRn ≠ dsXb := by decide
@[simp] theorem dsp_dsXb_ne_lFle : dsXb ≠ lFle := by decide
@[simp] theorem dsp_lFle_ne_dsXb : lFle ≠ dsXb := by decide
@[simp] theorem dsp_dsXb_ne_lKb : dsXb ≠ lKb := by decide
@[simp] theorem dsp_lKb_ne_dsXb : lKb ≠ dsXb := by decide
@[simp] theorem dsp_dsXb_ne_lDir : dsXb ≠ lDir := by decide
@[simp] theorem dsp_lDir_ne_dsXb : lDir ≠ dsXb := by decide
@[simp] theorem dsp_dsXb_ne_lFln : dsXb ≠ lFln := by decide
@[simp] theorem dsp_lFln_ne_dsXb : lFln ≠ dsXb := by decide
@[simp] theorem dsp_dsXb_ne_lFll : dsXb ≠ lFll := by decide
@[simp] theorem dsp_lFll_ne_dsXb : lFll ≠ dsXb := by decide
@[simp] theorem dsp_dsXb_ne_lFls : dsXb ≠ lFls := by decide
@[simp] theorem dsp_lFls_ne_dsXb : lFls ≠ dsXb := by decide
@[simp] theorem dsp_dsXb_ne_kFu : dsXb ≠ kFu := by decide
@[simp] theorem dsp_kFu_ne_dsXb : kFu ≠ dsXb := by decide
@[simp] theorem dsp_dsXb_ne_kD : dsXb ≠ kD := by decide
@[simp] theorem dsp_kD_ne_dsXb : kD ≠ dsXb := by decide
@[simp] theorem dsp_dsLa_ne_dsA : dsLa ≠ dsA := by decide
@[simp] theorem dsp_dsLa_ne_dsB : dsLa ≠ dsB := by decide
@[simp] theorem dsp_dsLa_ne_dsH : dsLa ≠ dsH := by decide
@[simp] theorem dsp_dsLa_ne_dsN : dsLa ≠ dsN := by decide
@[simp] theorem dsp_dsLa_ne_dsU : dsLa ≠ dsU := by decide
@[simp] theorem dsp_dsLa_ne_dsH2 : dsLa ≠ dsH2 := by decide
@[simp] theorem dsp_dsLa_ne_dsN2 : dsLa ≠ dsN2 := by decide
@[simp] theorem dsp_dsLa_ne_dsU2 : dsLa ≠ dsU2 := by decide
@[simp] theorem dsp_dsLa_ne_dsXa : dsLa ≠ dsXa := by decide
@[simp] theorem dsp_dsLa_ne_dsXb : dsLa ≠ dsXb := by decide
@[simp] theorem dsp_dsLa_ne_dsLb : dsLa ≠ dsLb := by decide
@[simp] theorem dsp_dsLa_ne_dsQ : dsLa ≠ dsQ := by decide
@[simp] theorem dsp_dsLa_ne_dsR : dsLa ≠ dsR := by decide
@[simp] theorem dsp_dsLa_ne_lFl : dsLa ≠ lFl := by decide
@[simp] theorem dsp_lFl_ne_dsLa : lFl ≠ dsLa := by decide
@[simp] theorem dsp_dsLa_ne_lDh : dsLa ≠ lDh := by decide
@[simp] theorem dsp_lDh_ne_dsLa : lDh ≠ dsLa := by decide
@[simp] theorem dsp_dsLa_ne_lDt : dsLa ≠ lDt := by decide
@[simp] theorem dsp_lDt_ne_dsLa : lDt ≠ dsLa := by decide
@[simp] theorem dsp_dsLa_ne_lDg : dsLa ≠ lDg := by decide
@[simp] theorem dsp_lDg_ne_dsLa : lDg ≠ dsLa := by decide
@[simp] theorem dsp_dsLa_ne_lDi : dsLa ≠ lDi := by decide
@[simp] theorem dsp_lDi_ne_dsLa : lDi ≠ dsLa := by decide
@[simp] theorem dsp_dsLa_ne_lRp : dsLa ≠ lRp := by decide
@[simp] theorem dsp_lRp_ne_dsLa : lRp ≠ dsLa := by decide
@[simp] theorem dsp_dsLa_ne_lRn : dsLa ≠ lRn := by decide
@[simp] theorem dsp_lRn_ne_dsLa : lRn ≠ dsLa := by decide
@[simp] theorem dsp_dsLa_ne_lFle : dsLa ≠ lFle := by decide
@[simp] theorem dsp_lFle_ne_dsLa : lFle ≠ dsLa := by decide
@[simp] theorem dsp_dsLa_ne_lKb : dsLa ≠ lKb := by decide
@[simp] theorem dsp_lKb_ne_dsLa : lKb ≠ dsLa := by decide
@[simp] theorem dsp_dsLa_ne_lDir : dsLa ≠ lDir := by decide
@[simp] theorem dsp_lDir_ne_dsLa : lDir ≠ dsLa := by decide
@[simp] theorem dsp_dsLa_ne_lFln : dsLa ≠ lFln := by decide
@[simp] theorem dsp_lFln_ne_dsLa : lFln ≠ dsLa := by decide
@[simp] theorem dsp_dsLa_ne_lFll : dsLa ≠ lFll := by decide
@[simp] theorem dsp_lFll_ne_dsLa : lFll ≠ dsLa := by decide
@[simp] theorem dsp_dsLa_ne_lFls : dsLa ≠ lFls := by decide
@[simp] theorem dsp_lFls_ne_dsLa : lFls ≠ dsLa := by decide
@[simp] theorem dsp_dsLa_ne_kFu : dsLa ≠ kFu := by decide
@[simp] theorem dsp_kFu_ne_dsLa : kFu ≠ dsLa := by decide
@[simp] theorem dsp_dsLa_ne_kD : dsLa ≠ kD := by decide
@[simp] theorem dsp_kD_ne_dsLa : kD ≠ dsLa := by decide
@[simp] theorem dsp_dsLb_ne_dsA : dsLb ≠ dsA := by decide
@[simp] theorem dsp_dsLb_ne_dsB : dsLb ≠ dsB := by decide
@[simp] theorem dsp_dsLb_ne_dsH : dsLb ≠ dsH := by decide
@[simp] theorem dsp_dsLb_ne_dsN : dsLb ≠ dsN := by decide
@[simp] theorem dsp_dsLb_ne_dsU : dsLb ≠ dsU := by decide
@[simp] theorem dsp_dsLb_ne_dsH2 : dsLb ≠ dsH2 := by decide
@[simp] theorem dsp_dsLb_ne_dsN2 : dsLb ≠ dsN2 := by decide
@[simp] theorem dsp_dsLb_ne_dsU2 : dsLb ≠ dsU2 := by decide
@[simp] theorem dsp_dsLb_ne_dsXa : dsLb ≠ dsXa := by decide
@[simp] theorem dsp_dsLb_ne_dsXb : dsLb ≠ dsXb := by decide
@[simp] theorem dsp_dsLb_ne_dsLa : dsLb ≠ dsLa := by decide
@[simp] theorem dsp_dsLb_ne_dsQ : dsLb ≠ dsQ := by decide
@[simp] theorem dsp_dsLb_ne_dsR : dsLb ≠ dsR := by decide
@[simp] theorem dsp_dsLb_ne_lFl : dsLb ≠ lFl := by decide
@[simp] theorem dsp_lFl_ne_dsLb : lFl ≠ dsLb := by decide
@[simp] theorem dsp_dsLb_ne_lDh : dsLb ≠ lDh := by decide
@[simp] theorem dsp_lDh_ne_dsLb : lDh ≠ dsLb := by decide
@[simp] theorem dsp_dsLb_ne_lDt : dsLb ≠ lDt := by decide
@[simp] theorem dsp_lDt_ne_dsLb : lDt ≠ dsLb := by decide
@[simp] theorem dsp_dsLb_ne_lDg : dsLb ≠ lDg := by decide
@[simp] theorem dsp_lDg_ne_dsLb : lDg ≠ dsLb := by decide
@[simp] theorem dsp_dsLb_ne_lDi : dsLb ≠ lDi := by decide
@[simp] theorem dsp_lDi_ne_dsLb : lDi ≠ dsLb := by decide
@[simp] theorem dsp_dsLb_ne_lRp : dsLb ≠ lRp := by decide
@[simp] theorem dsp_lRp_ne_dsLb : lRp ≠ dsLb := by decide
@[simp] theorem dsp_dsLb_ne_lRn : dsLb ≠ lRn := by decide
@[simp] theorem dsp_lRn_ne_dsLb : lRn ≠ dsLb := by decide
@[simp] theorem dsp_dsLb_ne_lFle : dsLb ≠ lFle := by decide
@[simp] theorem dsp_lFle_ne_dsLb : lFle ≠ dsLb := by decide
@[simp] theorem dsp_dsLb_ne_lKb : dsLb ≠ lKb := by decide
@[simp] theorem dsp_lKb_ne_dsLb : lKb ≠ dsLb := by decide
@[simp] theorem dsp_dsLb_ne_lDir : dsLb ≠ lDir := by decide
@[simp] theorem dsp_lDir_ne_dsLb : lDir ≠ dsLb := by decide
@[simp] theorem dsp_dsLb_ne_lFln : dsLb ≠ lFln := by decide
@[simp] theorem dsp_lFln_ne_dsLb : lFln ≠ dsLb := by decide
@[simp] theorem dsp_dsLb_ne_lFll : dsLb ≠ lFll := by decide
@[simp] theorem dsp_lFll_ne_dsLb : lFll ≠ dsLb := by decide
@[simp] theorem dsp_dsLb_ne_lFls : dsLb ≠ lFls := by decide
@[simp] theorem dsp_lFls_ne_dsLb : lFls ≠ dsLb := by decide
@[simp] theorem dsp_dsLb_ne_kFu : dsLb ≠ kFu := by decide
@[simp] theorem dsp_kFu_ne_dsLb : kFu ≠ dsLb := by decide
@[simp] theorem dsp_dsLb_ne_kD : dsLb ≠ kD := by decide
@[simp] theorem dsp_kD_ne_dsLb : kD ≠ dsLb := by decide
@[simp] theorem dsp_dsQ_ne_dsA : dsQ ≠ dsA := by decide
@[simp] theorem dsp_dsQ_ne_dsB : dsQ ≠ dsB := by decide
@[simp] theorem dsp_dsQ_ne_dsH : dsQ ≠ dsH := by decide
@[simp] theorem dsp_dsQ_ne_dsN : dsQ ≠ dsN := by decide
@[simp] theorem dsp_dsQ_ne_dsU : dsQ ≠ dsU := by decide
@[simp] theorem dsp_dsQ_ne_dsH2 : dsQ ≠ dsH2 := by decide
@[simp] theorem dsp_dsQ_ne_dsN2 : dsQ ≠ dsN2 := by decide
@[simp] theorem dsp_dsQ_ne_dsU2 : dsQ ≠ dsU2 := by decide
@[simp] theorem dsp_dsQ_ne_dsXa : dsQ ≠ dsXa := by decide
@[simp] theorem dsp_dsQ_ne_dsXb : dsQ ≠ dsXb := by decide
@[simp] theorem dsp_dsQ_ne_dsLa : dsQ ≠ dsLa := by decide
@[simp] theorem dsp_dsQ_ne_dsLb : dsQ ≠ dsLb := by decide
@[simp] theorem dsp_dsQ_ne_dsR : dsQ ≠ dsR := by decide
@[simp] theorem dsp_dsQ_ne_lFl : dsQ ≠ lFl := by decide
@[simp] theorem dsp_lFl_ne_dsQ : lFl ≠ dsQ := by decide
@[simp] theorem dsp_dsQ_ne_lDh : dsQ ≠ lDh := by decide
@[simp] theorem dsp_lDh_ne_dsQ : lDh ≠ dsQ := by decide
@[simp] theorem dsp_dsQ_ne_lDt : dsQ ≠ lDt := by decide
@[simp] theorem dsp_lDt_ne_dsQ : lDt ≠ dsQ := by decide
@[simp] theorem dsp_dsQ_ne_lDg : dsQ ≠ lDg := by decide
@[simp] theorem dsp_lDg_ne_dsQ : lDg ≠ dsQ := by decide
@[simp] theorem dsp_dsQ_ne_lDi : dsQ ≠ lDi := by decide
@[simp] theorem dsp_lDi_ne_dsQ : lDi ≠ dsQ := by decide
@[simp] theorem dsp_dsQ_ne_lRp : dsQ ≠ lRp := by decide
@[simp] theorem dsp_lRp_ne_dsQ : lRp ≠ dsQ := by decide
@[simp] theorem dsp_dsQ_ne_lRn : dsQ ≠ lRn := by decide
@[simp] theorem dsp_lRn_ne_dsQ : lRn ≠ dsQ := by decide
@[simp] theorem dsp_dsQ_ne_lFle : dsQ ≠ lFle := by decide
@[simp] theorem dsp_lFle_ne_dsQ : lFle ≠ dsQ := by decide
@[simp] theorem dsp_dsQ_ne_lKb : dsQ ≠ lKb := by decide
@[simp] theorem dsp_lKb_ne_dsQ : lKb ≠ dsQ := by decide
@[simp] theorem dsp_dsQ_ne_lDir : dsQ ≠ lDir := by decide
@[simp] theorem dsp_lDir_ne_dsQ : lDir ≠ dsQ := by decide
@[simp] theorem dsp_dsQ_ne_lFln : dsQ ≠ lFln := by decide
@[simp] theorem dsp_lFln_ne_dsQ : lFln ≠ dsQ := by decide
@[simp] theorem dsp_dsQ_ne_lFll : dsQ ≠ lFll := by decide
@[simp] theorem dsp_lFll_ne_dsQ : lFll ≠ dsQ := by decide
@[simp] theorem dsp_dsQ_ne_lFls : dsQ ≠ lFls := by decide
@[simp] theorem dsp_lFls_ne_dsQ : lFls ≠ dsQ := by decide
@[simp] theorem dsp_dsQ_ne_kFu : dsQ ≠ kFu := by decide
@[simp] theorem dsp_kFu_ne_dsQ : kFu ≠ dsQ := by decide
@[simp] theorem dsp_dsQ_ne_kD : dsQ ≠ kD := by decide
@[simp] theorem dsp_kD_ne_dsQ : kD ≠ dsQ := by decide
@[simp] theorem dsp_dsR_ne_dsA : dsR ≠ dsA := by decide
@[simp] theorem dsp_dsR_ne_dsB : dsR ≠ dsB := by decide
@[simp] theorem dsp_dsR_ne_dsH : dsR ≠ dsH := by decide
@[simp] theorem dsp_dsR_ne_dsN : dsR ≠ dsN := by decide
@[simp] theorem dsp_dsR_ne_dsU : dsR ≠ dsU := by decide
@[simp] theorem dsp_dsR_ne_dsH2 : dsR ≠ dsH2 := by decide
@[simp] theorem dsp_dsR_ne_dsN2 : dsR ≠ dsN2 := by decide
@[simp] theorem dsp_dsR_ne_dsU2 : dsR ≠ dsU2 := by decide
@[simp] theorem dsp_dsR_ne_dsXa : dsR ≠ dsXa := by decide
@[simp] theorem dsp_dsR_ne_dsXb : dsR ≠ dsXb := by decide
@[simp] theorem dsp_dsR_ne_dsLa : dsR ≠ dsLa := by decide
@[simp] theorem dsp_dsR_ne_dsLb : dsR ≠ dsLb := by decide
@[simp] theorem dsp_dsR_ne_dsQ : dsR ≠ dsQ := by decide
@[simp] theorem dsp_dsR_ne_lFl : dsR ≠ lFl := by decide
@[simp] theorem dsp_lFl_ne_dsR : lFl ≠ dsR := by decide
@[simp] theorem dsp_dsR_ne_lDh : dsR ≠ lDh := by decide
@[simp] theorem dsp_lDh_ne_dsR : lDh ≠ dsR := by decide
@[simp] theorem dsp_dsR_ne_lDt : dsR ≠ lDt := by decide
@[simp] theorem dsp_lDt_ne_dsR : lDt ≠ dsR := by decide
@[simp] theorem dsp_dsR_ne_lDg : dsR ≠ lDg := by decide
@[simp] theorem dsp_lDg_ne_dsR : lDg ≠ dsR := by decide
@[simp] theorem dsp_dsR_ne_lDi : dsR ≠ lDi := by decide
@[simp] theorem dsp_lDi_ne_dsR : lDi ≠ dsR := by decide
@[simp] theorem dsp_dsR_ne_lRp : dsR ≠ lRp := by decide
@[simp] theorem dsp_lRp_ne_dsR : lRp ≠ dsR := by decide
@[simp] theorem dsp_dsR_ne_lRn : dsR ≠ lRn := by decide
@[simp] theorem dsp_lRn_ne_dsR : lRn ≠ dsR := by decide
@[simp] theorem dsp_dsR_ne_lFle : dsR ≠ lFle := by decide
@[simp] theorem dsp_lFle_ne_dsR : lFle ≠ dsR := by decide
@[simp] theorem dsp_dsR_ne_lKb : dsR ≠ lKb := by decide
@[simp] theorem dsp_lKb_ne_dsR : lKb ≠ dsR := by decide
@[simp] theorem dsp_dsR_ne_lDir : dsR ≠ lDir := by decide
@[simp] theorem dsp_lDir_ne_dsR : lDir ≠ dsR := by decide
@[simp] theorem dsp_dsR_ne_lFln : dsR ≠ lFln := by decide
@[simp] theorem dsp_lFln_ne_dsR : lFln ≠ dsR := by decide
@[simp] theorem dsp_dsR_ne_lFll : dsR ≠ lFll := by decide
@[simp] theorem dsp_lFll_ne_dsR : lFll ≠ dsR := by decide
@[simp] theorem dsp_dsR_ne_lFls : dsR ≠ lFls := by decide
@[simp] theorem dsp_lFls_ne_dsR : lFls ≠ dsR := by decide
@[simp] theorem dsp_dsR_ne_kFu : dsR ≠ kFu := by decide
@[simp] theorem dsp_kFu_ne_dsR : kFu ≠ dsR := by decide
@[simp] theorem dsp_dsR_ne_kD : dsR ≠ kD := by decide
@[simp] theorem dsp_kD_ne_dsR : kD ≠ dsR := by decide

def dlrCore : ProgHOL 64 := (.ite (.cmp .equal (vv dlNa) (.const 0)) (.return (.cmp .equal (vv dlNb) (.const 0))) (.ite (.cmp .equal (vv dlNb) (.const 0)) (.return (.const 0)) (.seq (.assign .local dlX (.load .one (vv dlA))) (.seq (.assign .local dlY (.load .one (vv dlB))) (.seq (.call (some (some (.local, dlR), none)) fD [(vv kFu), (vv kD), (vv dlX), (vv dlY)]) (.ite (.cmp .equal (vv dlR) (.const 0)) (.return (.const 0)) (.seq (.call (some (some (.local, dlS), none)) fDlr [(vv kFu), (vv kD), (.op .sub [(vv dlA), (.const 8)]), (.op .sub [(vv dlNa), (.const 1)]), (.op .sub [(vv dlB), (.const 8)]), (.op .sub [(vv dlNb), (.const 1)])]) (.return (vv dlS)))))))))

def dlrBody : ProgHOL 64 := prologue dlLocals dlrCore

structure DlrCodes (C : Ctx) : Prop where
  d : C.code.lookup fD = some (pmap dParams, dE C, .one)
  self : C.code.lookup fDlr = some (dlParams.map (fun p => (p, ShapeHOL.one)), dlrBody, .one)

def dsParams : List MlS := [kFu, kD, dsA, dsB]
def dsLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, dsH, dsN, dsU, dsH2, dsN2, dsU2, dsXa, dsXb, dsLa, dsLb, dsQ, dsR]
def dsBody : ProgHOL 64 := prologue dsLocals (.seq (.call (some (some (.local, dsH), none)) fGetAppFn [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv dsA)]) (.ite (tagIsE dsH 3) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv dsH)) (.seq eViewP (.seq (.assign .local dsN (.load .one (vv lRp))) (.seq (.assign .local dsU (.load .one (.op .add [(vv lRp), (.const 8)]))) (.seq (.call (some (some (.local, dsH2), none)) fGetAppFn [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv dsB)]) (.ite (tagIsE dsH2 3) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv dsH2)) (.seq eViewP (.seq (.assign .local dsN2 (.load .one (vv lRp))) (.seq (.assign .local dsU2 (.load .one (.op .add [(vv lRp), (.const 8)]))) (.seq (.call (some (some (.local, dsXa), none)) ExG.fGaa [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv dsA)]) (.seq (.call (some (some (.local, dsXb), none)) ExG.fGaa [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv dsB)]) (.seq (.assign .local dsLa (.load .one (vv dsXa))) (.seq (.assign .local dsLb (.load .one (vv dsXb))) (.ite (.cmp .notEqual (vv dsN) (vv dsN2)) (.return (.const 0)) (.ite (.cmp .notEqual (vv dsLa) (vv dsLb)) (.return (.const 0)) (.seq (.call (some (some (.local, dsQ), none)) LLeq.fLsGo [(vv dsU), (vv dsU2), (.const 0)]) (.ite (.cmp .notEqual (vv dsQ) (.const 2)) (.return (.const 0)) (.seq (.call (some (some (.local, dsR), none)) fDlr [(vv kFu), (vv kD), (.op .add [(vv dsXa), (.shift .lsl (vv dsLa) (.const 3))]), (vv dsLa), (.op .add [(vv dsXb), (.shift .lsl (vv dsLb) (.const 3))]), (vv dsLb)]) (.return (vv dsR)))))))))))))))) (.return (.const 0))))))))) (.return (.const 0))))

section
variable {σ : Type}

theorem cellA_sub8 (C : Ctx) (q : Nat) (hq : 1 ≤ q) : cellA C q - 8 = cellA C (q - 1) := by
  have h := cellA_add8 C (q - 1)
  rw [Nat.sub_add_cancel hq] at h
  rw [← h, BitVec.add_sub_cancel]

theorem dlr_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) (hc : DlrCodes C) (d : Nat)
    (hD : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ a b, Callee (σ := σ) (ctxH C H) dParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (dE C) s1 ((knot mode C n).defeq d a b)
      (PostB (ctxH C H))) :
    ∀ (as bs : List EIdx) (qa qb : Nat) (H : List (BitVec 64)) (s : AState), C.H <+: H →
      (∀ j (hj : j < as.length), H[qa - j]? = some (Enc.idxW as[j])) → as.length ≤ qa →
      (∀ j (hj : j < bs.length), H[qb - j]? = some (Enc.idxW bs[j])) → bs.length ≤ qb →
      as.length < 2 ^ 63 → bs.length < 2 ^ 63 →
      SpecR (σ := σ) (Pre (ctxH C H) s (dlParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, cellA C qa,
        BitVec.ofNat 64 as.length, cellA C qb, BitVec.ofNat 64 bs.length])) dlrBody s
        (defEqList (knot mode C n) C.fe d as bs) (PostB (ctxH C H)) := by
  intro as
  induction as with
  | nil =>
    intro bs qa qb H s hp ha hqa hb hqb hla hlb
    refine specR_prologue (postB_locals _) (dl_none _ _) ?_
    unfold dlrCore
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, dlParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    cases bs with
    | nil =>
      exact specR_returnI _ 1 (by simp +decide [sev, Env.get, dlParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | cons b bs =>
      have hne := ofNat_succ_ne bs.length (by simp at hlb; omega)
      exact specR_returnI _ 0 (by simp +decide [sev, Env.get, dlParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
        (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | cons a as ih =>
    intro bs qa qb H s hp ha hqa hb hqb hla hlb
    refine specR_prologue (postB_locals _) (dl_none _ _) ?_
    unfold dlrCore
    have hnea := ofNat_succ_ne as.length (by simp at hla; omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, dlParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hnea)
      (fun h => absurd rfl h) (fun _ => ?_)
    cases bs with
    | nil =>
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, dlParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | cons b bs =>
      have hneb := ofNat_succ_ne bs.length (by simp at hlb; omega)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, dlParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hneb)
        (fun h => absurd rfl h) (fun _ => ?_)
      refine UD.specR_heapLoadI' (C := ctxH C H) dlX (vv dlA) qa (Enc.idxW a) (by have h := ha 0 (by simp); simp only [Nat.sub_zero, List.getElem_cons_zero] at h; exact h) (by decide)
        (by simp +decide [sev, Env.get, dlParams, ctxEnv]; rfl) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H) dlY (vv dlB) qb (Enc.idxW b) (by have h := hb 0 (by simp); simp only [Nat.sub_zero, List.getElem_cons_zero] at h; exact h) (by decide)
        (by simp +decide [sev, Env.get, dlParams, ctxEnv]; rfl) ?_
      rw [defEqList]
      refine specR_callNIH (C := ctxH C H) dlR fD dParams [vv kFu, vv kD, vv dlX, vv dlY] (dE C)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (by decide) rfl (by decide) hc.d
        ⟨by simp +decide [Env.get, dlParams, ctxEnv], by simp +decide [Env.get, dlParams, ctxEnv], by simp, by simp,
          trivial⟩
        (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => hD H s hp a b u hu (fun i hi _ => hlk i (by omega)))
        (fun df w s1 H1 hp1 hw => ?_)
      subst hw
      cases df
      · refine specR_ifI _ 1 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
          (fun h => absurd h (by decide))
        exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      · refine specR_ifI _ 0 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
          (fun _ => ?_)
        simp only [ite_true]
        refine specR_congr (m' := defEqList (knot mode C n) C.fe d as bs >>= fun r => pure r) (by simp) ?_
        refine specR_callNIH (C := ctxH C H1) dlS fDlr dlParams
          [vv kFu, vv kD, .op .sub [vv dlA, .const 8], .op .sub [vv dlNa, .const 1],
            .op .sub [vv dlB, .const 8], .op .sub [vv dlNb, .const 1]] dlrBody
          [BitVec.ofNat 64 n, BitVec.ofNat 64 d, cellA C (qa - 1), BitVec.ofNat 64 as.length, cellA C (qb - 1),
            BitVec.ofNat 64 bs.length] (by decide) rfl (by decide) hc.self
          ⟨by simp +decide [Env.get, dlParams, ctxEnv], by simp +decide [Env.get, dlParams, ctxEnv],
            by simp +decide [sev, Env.get, dlParams, ctxEnv]; exact cellA_sub8 C qa (by simp at hqa; omega),
            by simp +decide [sev, Env.get, dlParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _,
            by simp +decide [sev, Env.get, dlParams, ctxEnv]; exact cellA_sub8 C qb (by simp at hqb; omega),
            by simp +decide [sev, Env.get, dlParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, trivial⟩
          (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
          (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu dlParams _ rfl hlk)
            (ih bs (qa - 1) (qb - 1) H1 s1 (hp.trans hp1)
              (fun j hj => by have h := ha (j + 1) (by simp; omega); rw [show qa - (j + 1) = qa - 1 - j by omega] at h; exact pfx_get (H := H) hp1 (by simpa using h))
              (by simp at hqa; omega)
              (fun j hj => by have h := hb (j + 1) (by simp; omega); rw [show qb - (j + 1) = qb - 1 - j by omega] at h; exact pfx_get (H := H) hp1 (by simpa using h))
              (by simp at hqb; omega)
              (by simp at hla; omega) (by simp at hlb; omega)))
          (fun r w s2 H2 hp2 hw => ?_)
        subst hw
        exact specR_returnI _ (boolW r) (by simp)
          (fun t ht => ⟨H2, hp1.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

structure DsCodes (C : Ctx) : Prop where
  gaf : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  gaa : C.code.lookup ExG.fGaa = some ([(pFu, .one), (pH, .one)], ExG.gaaBody C, .one)
  ls : C.code.lookup LLeq.fLsGo = some (LLeq.lsParams.map (fun p => (p, ShapeHOL.one)), LLeq.lsGoBody, .one)
  dlr : DlrCodes C

theorem ds_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) (hok : CtxOK C) (hc : DsCodes C) (d : Nat)
    (hD : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ a b, Callee (σ := σ) (ctxH C H) dParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (dE C) s1 ((knot mode C n).defeq d a b)
      (PostB (ctxH C H)))
    (hLS : ∀ (H : List (BitVec 64)) s1 (u v : LsIdx), C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s1 (LLeq.lsParams.zip [Enc.idxW u, Enc.idxW v, BitVec.ofNat 64 0])) LLeq.lsGoBody
        s1 (lvlsEq? u v) (LLeq.PostOB (ctxH C H)))
    (s : AState) (a b : EIdx) :
    SpecR (σ := σ) (Pre C s (dsParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b])) dsBody s
      (defeqSpine (knot mode C n) C.fe d a b) (PostB C) := by
  refine specR_prologue (postB_locals C) (Knot.params_none C dsLocals dsParams _ (by decide) (by decide)) ?_
  unfold defeqSpine
  refine specR_callNIM (C := C) dsH fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv dsA]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW a] (by decide) rfl (by decide) hc.gaf
    ⟨rfl, by simp +decide [Env.get, dsParams, ctxEnv], trivial⟩
    (fun x w' s' st => getAppFn coreWalkFuel a s = .ok (x, s') ∧ Post C s x w' s' st)
    (fun x w' s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec C hc.gaf coreWalkFuel a s CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun h w' s' st ⟨hrun, hw, hs, _⟩ => ?_)
  subst hw
  have hs' : s = s' := hs.symm
  subst hs'
  refine Knot.specR_tagIteV dsH h 3 (by decide) (by decide) (by simp) (fun htc => ?_) (fun htc => ?_)
  swap
  · rw [if_neg (show ¬ (h.tag == ETag.const) = true by simpa [ETag.const] using htc)]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [if_pos (show (h.tag == ETag.const) = true by simp [htc, ETag.const])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv dsH) (Enc.idxW h) (by decide) (by simp) ?_
  refine specR_viewP h (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
    (fun v P hv htn _ => ?_)
  refine specR_congr (Big.view_bind_eq h v _ s hv) ?_
  have h3 : v.tagN = 3 := by rw [htn, htc]; rfl
  obtain ⟨c, us, rfl⟩ := UD.tagN_const h3
  dsimp only
  refine specR_loadI' dsN (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW c) (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW c) [Enc.idxW us] []) ?_
  refine specR_loadI' dsU _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW us) (by decide) (by simp +decide [sev]) rfl
    (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW c) (Enc.idxW us) [] []) ?_
  refine specR_dropM ?_
  refine specR_callNIM (C := C) dsH2 fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv dsB]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW b] (by decide) rfl (by decide) hc.gaf
    ⟨rfl, by simp +decide [Env.get, dsParams, ctxEnv], trivial⟩
    (fun x w' s' st => getAppFn coreWalkFuel b s = .ok (x, s') ∧ Post C s x w' s' st)
    (fun x w' s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec C hc.gaf coreWalkFuel b s CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun h2 w' s' st ⟨hrun, hw, hs, _⟩ => ?_)
  subst hw
  have hs' : s = s' := hs.symm
  subst hs'
  refine Knot.specR_tagIteV dsH2 h2 3 (by decide) (by decide) (by simp) (fun htc => ?_) (fun htc => ?_)
  swap
  · rw [if_neg (show ¬ (h2.tag == ETag.const) = true by simpa [ETag.const] using htc)]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [if_pos (show (h2.tag == ETag.const) = true by simp [htc, ETag.const])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv dsH2) (Enc.idxW h2) (by decide) (by simp) ?_
  refine specR_viewP h2 (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
    (fun v2 P2 hv htn _ => ?_)
  refine specR_congr (Big.view_bind_eq h2 v2 _ s hv) ?_
  have h3 : v2.tagN = 3 := by rw [htn, htc]; rfl
  obtain ⟨c2, us2, rfl⟩ := UD.tagN_const h3
  dsimp only
  refine specR_loadI' dsN2 (vv lRp) P2 (P2 + BitVec.ofNat 64 0) (Enc.idxW c2) (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P2 (Enc.idxW c2) [Enc.idxW us2] []) ?_
  refine specR_loadI' dsU2 _ (P2 + 8) (P2 + BitVec.ofNat 64 8) (Enc.idxW us2) (by decide) (by simp +decide [sev]) rfl
    (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P2 (Enc.idxW c2) (Enc.idxW us2) [] []) ?_
  refine specR_dropM ?_
  refine specR_callNIH (C := C) dsXa ExG.fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv dsA] (ExG.gaaBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW a] (by decide) rfl (by decide) hc.gaa
    ⟨rfl, by simp +decide [Env.get, dsParams, ctxEnv], trivial⟩
    (PostA C) (fun xs w _ H1 => ∃ o1, w = cellA C o1 ∧ BlkAt H1 o1 (xs.map Enc.idxW))
    (fun xs w s' st ⟨H1, o1, hp, hw, hb, hsr⟩ => ⟨H1, hp, ⟨o1, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (ExG.gaa_spec C hok hc.gaa coreWalkFuel CV.coreWalkFuel_lt C.H a s))
    (fun aa w s1 H1 hp1 ⟨o1, hw, hba⟩ => ?_)
  subst hw
  refine specR_callNIH (C := ctxH C H1) dsXb ExG.fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv dsB]
    (ExG.gaaBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW b] (by decide) rfl (by decide) hc.gaa
    ⟨rfl, by simp +decide [Env.get, dsParams, ctxEnv], trivial⟩
    (PostA (ctxH C H1)) (fun xs w _ H2 => ∃ o2, w = cellA C o2 ∧ BlkAt H2 o2 (xs.map Enc.idxW))
    (fun xs w s' st ⟨H2, o2, hp, hw, hb, hsr⟩ => ⟨H2, hp, ⟨o2, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (ExG.gaa_spec C hok hc.gaa coreWalkFuel CV.coreWalkFuel_lt H1 b s1))
    (fun bb w s2 H2 hp2 ⟨o2, hw, hbb⟩ => ?_)
  subst hw
  have hp12 : C.H <+: H2 := hp1.trans hp2
  have hba' := blkAt_mono hba hp2
  refine UD.specR_heapLoadI' (C := ctxH C H2) dsLa (vv dsXa) o1 _ (by have h := hba'.1; simp only [List.length_map] at h; exact h) (by decide)
    (by simp +decide [sev, Env.get]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H2) dsLb (vv dsXb) o2 _ (by have h := hbb.1; simp only [List.length_map] at h; exact h) (by decide)
    (by simp +decide [sev, Env.get]; rfl) ?_
  refine specR_atEntry fun t ht => ?_
  have hsza := blk_small0 (ctxOK_H hok H2) ht.sr hba'
  have hszb := blk_small0 (ctxOK_H hok H2) ht.sr hbb
  simp only [List.length_map] at hsza hszb
  by_cases hcn : c = c2
  swap
  · have hne : Enc.idxW c ≠ Enc.idxW c2 := fun e => hcn (Enc.idxW_inj e)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, dsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    rw [if_neg (fun h => hcn h.1)]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H2, hp12, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  subst hcn
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, dsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
  by_cases hln : aa.length = bb.length
  swap
  · have hne : BitVec.ofNat 64 aa.length ≠ BitVec.ofNat 64 bb.length := by
      intro x; apply hln
      have := congrArg BitVec.toNat x
      simp only [BitVec.toNat_ofNat] at this
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, dsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    rw [if_neg (fun h => hln h.2)]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H2, hp12, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, dsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hln]) (fun h => absurd rfl h) (fun _ => ?_)
  rw [if_pos ⟨rfl, hln⟩]
  refine specR_callNIH (C := ctxH C H2) dsQ LLeq.fLsGo LLeq.lsParams [vv dsU, vv dsU2, .const 0] LLeq.lsGoBody
    [Enc.idxW us, Enc.idxW us2, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.ls
    ⟨by simp +decide [Env.get, dsParams, ctxEnv], by simp +decide [Env.get, dsParams, ctxEnv], rfl, trivial⟩
    (LLeq.PostOB (ctxH C H2)) (fun o w _ H' => H' = H2 ∧ w = LLeq.obW o)
    (fun o w s' st ⟨hw, hsr⟩ => ⟨H2, List.prefix_refl _, ⟨rfl, hw⟩, hsr⟩)
    (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu LLeq.lsParams _ rfl hlk)
      (hLS H2 s2 us us2 hp12)) (fun o w s3 H3 _ ⟨eH, hw⟩ => ?_)
  subst H3; subst hw
  rcases o with _ | ⟨_ | _⟩
  · refine specR_ifI _ 1 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H2, hp12, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_ifI _ 1 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H2, hp12, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 0 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
  dsimp only
  refine specR_congr (m' := defEqList (knot mode C n) C.fe d aa.reverse bb.reverse >>= fun r => pure r) (by simp) ?_
  refine specR_callNIH (C := ctxH C H2) dsR fDlr dlParams
    [vv kFu, vv kD, .op .add [vv dsXa, .shift .lsl (vv dsLa) (.const 3)], vv dsLa,
      .op .add [vv dsXb, .shift .lsl (vv dsLb) (.const 3)], vv dsLb] dlrBody
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, cellA C (o1 + aa.length), BitVec.ofNat 64 aa.reverse.length,
      cellA C (o2 + bb.length), BitVec.ofNat 64 bb.reverse.length] (by decide) rfl (by decide) hc.dlr.self
    ⟨by simp +decide [Env.get, dsParams, ctxEnv], by simp +decide [Env.get, dsParams, ctxEnv],
      by simp +decide [sev, Env.get]; rw [← cellA_shl C o1 aa.length (by omega)],
      by simp +decide [sev, Env.get],
      by simp +decide [sev, Env.get]; rw [← cellA_shl C o2 bb.length (by omega)],
      by simp +decide [sev, Env.get], trivial⟩
    (PostB (ctxH C H2)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu dlParams _ rfl hlk)
      (dlr_spec mode n C hc.dlr d hD aa.reverse bb.reverse (o1 + aa.length) (o2 + bb.length) H2 s3 hp12
        (fun j hj => by
          have hj' : j < aa.length := by simpa using hj
          have h := hba'.2 (aa.length - 1 - j) (by simp; omega)
          rw [List.getElem_map] at h
          rw [List.getElem_reverse, show o1 + aa.length - j = o1 + 1 + (aa.length - 1 - j) by omega]
          exact h)
        (by simp)
        (fun j hj => by
          have hj' : j < bb.length := by simpa using hj
          have h := hbb.2 (bb.length - 1 - j) (by simp; omega)
          rw [List.getElem_map] at h
          rw [List.getElem_reverse, show o2 + bb.length - j = o2 + 1 + (bb.length - 1 - j) by omega]
          exact h)
        (by simp) (by simp; omega) (by simp; omega)))
    (fun r w s4 H4 hp4 hw => ?_)
  subst hw
  exact specR_returnI _ (boolW r) (by simp)
    (fun t ht => ⟨H4, hp12.trans hp4, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
