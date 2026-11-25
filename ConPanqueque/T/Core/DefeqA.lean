import ConPanqueque.T.Core.InferBodyIO
import ConPanqueque.T.Core.NatLitCtor
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `defeqBody`'s small helpers

`headIsProj` (the spine head a projection?), `defeqNoFvars` (both sides free of free variables), `isNatZero`
(`Nat.zero` or the literal `0`).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def hpE := ofString "hpn_e"
def hpH := ofString "hpn_h"
def dnA := ofString "dnn_a"
def dnB := ofString "dnn_b"
def dnX := ofString "dnn_x"
def dnY := ofString "dnn_y"
def izE := ofString "izn_e"
def izW := ofString "izn_w"
def izC := ofString "izn_c"
def izU := ofString "izn_u"
def izZ := ofString "izn_z"
def izL := ofString "izn_l"
def fHp := ofString "headIsProj"
def fDn := ofString "defeqNoFvars"
def fIz := ofString "isNatZero"

@[simp] theorem dfa_hpE_ne_hpH : hpE ≠ hpH := by decide
@[simp] theorem dfa_hpE_ne_lFl : hpE ≠ lFl := by decide
@[simp] theorem dfa_lFl_ne_hpE : lFl ≠ hpE := by decide
@[simp] theorem dfa_hpE_ne_lDh : hpE ≠ lDh := by decide
@[simp] theorem dfa_lDh_ne_hpE : lDh ≠ hpE := by decide
@[simp] theorem dfa_hpE_ne_lDt : hpE ≠ lDt := by decide
@[simp] theorem dfa_lDt_ne_hpE : lDt ≠ hpE := by decide
@[simp] theorem dfa_hpE_ne_lDg : hpE ≠ lDg := by decide
@[simp] theorem dfa_lDg_ne_hpE : lDg ≠ hpE := by decide
@[simp] theorem dfa_hpE_ne_lDi : hpE ≠ lDi := by decide
@[simp] theorem dfa_lDi_ne_hpE : lDi ≠ hpE := by decide
@[simp] theorem dfa_hpE_ne_lRp : hpE ≠ lRp := by decide
@[simp] theorem dfa_lRp_ne_hpE : lRp ≠ hpE := by decide
@[simp] theorem dfa_hpE_ne_lRn : hpE ≠ lRn := by decide
@[simp] theorem dfa_lRn_ne_hpE : lRn ≠ hpE := by decide
@[simp] theorem dfa_hpE_ne_lDir : hpE ≠ lDir := by decide
@[simp] theorem dfa_lDir_ne_hpE : lDir ≠ hpE := by decide
@[simp] theorem dfa_hpE_ne_lFle : hpE ≠ lFle := by decide
@[simp] theorem dfa_lFle_ne_hpE : lFle ≠ hpE := by decide
@[simp] theorem dfa_hpE_ne_lKb : hpE ≠ lKb := by decide
@[simp] theorem dfa_lKb_ne_hpE : lKb ≠ hpE := by decide
@[simp] theorem dfa_hpH_ne_hpE : hpH ≠ hpE := by decide
@[simp] theorem dfa_hpH_ne_lFl : hpH ≠ lFl := by decide
@[simp] theorem dfa_lFl_ne_hpH : lFl ≠ hpH := by decide
@[simp] theorem dfa_hpH_ne_lDh : hpH ≠ lDh := by decide
@[simp] theorem dfa_lDh_ne_hpH : lDh ≠ hpH := by decide
@[simp] theorem dfa_hpH_ne_lDt : hpH ≠ lDt := by decide
@[simp] theorem dfa_lDt_ne_hpH : lDt ≠ hpH := by decide
@[simp] theorem dfa_hpH_ne_lDg : hpH ≠ lDg := by decide
@[simp] theorem dfa_lDg_ne_hpH : lDg ≠ hpH := by decide
@[simp] theorem dfa_hpH_ne_lDi : hpH ≠ lDi := by decide
@[simp] theorem dfa_lDi_ne_hpH : lDi ≠ hpH := by decide
@[simp] theorem dfa_hpH_ne_lRp : hpH ≠ lRp := by decide
@[simp] theorem dfa_lRp_ne_hpH : lRp ≠ hpH := by decide
@[simp] theorem dfa_hpH_ne_lRn : hpH ≠ lRn := by decide
@[simp] theorem dfa_lRn_ne_hpH : lRn ≠ hpH := by decide
@[simp] theorem dfa_hpH_ne_lDir : hpH ≠ lDir := by decide
@[simp] theorem dfa_lDir_ne_hpH : lDir ≠ hpH := by decide
@[simp] theorem dfa_hpH_ne_lFle : hpH ≠ lFle := by decide
@[simp] theorem dfa_lFle_ne_hpH : lFle ≠ hpH := by decide
@[simp] theorem dfa_hpH_ne_lKb : hpH ≠ lKb := by decide
@[simp] theorem dfa_lKb_ne_hpH : lKb ≠ hpH := by decide
@[simp] theorem dfa_dnA_ne_dnB : dnA ≠ dnB := by decide
@[simp] theorem dfa_dnA_ne_dnX : dnA ≠ dnX := by decide
@[simp] theorem dfa_dnA_ne_dnY : dnA ≠ dnY := by decide
@[simp] theorem dfa_dnA_ne_lFl : dnA ≠ lFl := by decide
@[simp] theorem dfa_lFl_ne_dnA : lFl ≠ dnA := by decide
@[simp] theorem dfa_dnA_ne_lDh : dnA ≠ lDh := by decide
@[simp] theorem dfa_lDh_ne_dnA : lDh ≠ dnA := by decide
@[simp] theorem dfa_dnA_ne_lDt : dnA ≠ lDt := by decide
@[simp] theorem dfa_lDt_ne_dnA : lDt ≠ dnA := by decide
@[simp] theorem dfa_dnA_ne_lDg : dnA ≠ lDg := by decide
@[simp] theorem dfa_lDg_ne_dnA : lDg ≠ dnA := by decide
@[simp] theorem dfa_dnA_ne_lDi : dnA ≠ lDi := by decide
@[simp] theorem dfa_lDi_ne_dnA : lDi ≠ dnA := by decide
@[simp] theorem dfa_dnA_ne_lRp : dnA ≠ lRp := by decide
@[simp] theorem dfa_lRp_ne_dnA : lRp ≠ dnA := by decide
@[simp] theorem dfa_dnA_ne_lRn : dnA ≠ lRn := by decide
@[simp] theorem dfa_lRn_ne_dnA : lRn ≠ dnA := by decide
@[simp] theorem dfa_dnA_ne_lDir : dnA ≠ lDir := by decide
@[simp] theorem dfa_lDir_ne_dnA : lDir ≠ dnA := by decide
@[simp] theorem dfa_dnA_ne_lFle : dnA ≠ lFle := by decide
@[simp] theorem dfa_lFle_ne_dnA : lFle ≠ dnA := by decide
@[simp] theorem dfa_dnA_ne_lKb : dnA ≠ lKb := by decide
@[simp] theorem dfa_lKb_ne_dnA : lKb ≠ dnA := by decide
@[simp] theorem dfa_dnB_ne_dnA : dnB ≠ dnA := by decide
@[simp] theorem dfa_dnB_ne_dnX : dnB ≠ dnX := by decide
@[simp] theorem dfa_dnB_ne_dnY : dnB ≠ dnY := by decide
@[simp] theorem dfa_dnB_ne_lFl : dnB ≠ lFl := by decide
@[simp] theorem dfa_lFl_ne_dnB : lFl ≠ dnB := by decide
@[simp] theorem dfa_dnB_ne_lDh : dnB ≠ lDh := by decide
@[simp] theorem dfa_lDh_ne_dnB : lDh ≠ dnB := by decide
@[simp] theorem dfa_dnB_ne_lDt : dnB ≠ lDt := by decide
@[simp] theorem dfa_lDt_ne_dnB : lDt ≠ dnB := by decide
@[simp] theorem dfa_dnB_ne_lDg : dnB ≠ lDg := by decide
@[simp] theorem dfa_lDg_ne_dnB : lDg ≠ dnB := by decide
@[simp] theorem dfa_dnB_ne_lDi : dnB ≠ lDi := by decide
@[simp] theorem dfa_lDi_ne_dnB : lDi ≠ dnB := by decide
@[simp] theorem dfa_dnB_ne_lRp : dnB ≠ lRp := by decide
@[simp] theorem dfa_lRp_ne_dnB : lRp ≠ dnB := by decide
@[simp] theorem dfa_dnB_ne_lRn : dnB ≠ lRn := by decide
@[simp] theorem dfa_lRn_ne_dnB : lRn ≠ dnB := by decide
@[simp] theorem dfa_dnB_ne_lDir : dnB ≠ lDir := by decide
@[simp] theorem dfa_lDir_ne_dnB : lDir ≠ dnB := by decide
@[simp] theorem dfa_dnB_ne_lFle : dnB ≠ lFle := by decide
@[simp] theorem dfa_lFle_ne_dnB : lFle ≠ dnB := by decide
@[simp] theorem dfa_dnB_ne_lKb : dnB ≠ lKb := by decide
@[simp] theorem dfa_lKb_ne_dnB : lKb ≠ dnB := by decide
@[simp] theorem dfa_dnX_ne_dnA : dnX ≠ dnA := by decide
@[simp] theorem dfa_dnX_ne_dnB : dnX ≠ dnB := by decide
@[simp] theorem dfa_dnX_ne_dnY : dnX ≠ dnY := by decide
@[simp] theorem dfa_dnX_ne_lFl : dnX ≠ lFl := by decide
@[simp] theorem dfa_lFl_ne_dnX : lFl ≠ dnX := by decide
@[simp] theorem dfa_dnX_ne_lDh : dnX ≠ lDh := by decide
@[simp] theorem dfa_lDh_ne_dnX : lDh ≠ dnX := by decide
@[simp] theorem dfa_dnX_ne_lDt : dnX ≠ lDt := by decide
@[simp] theorem dfa_lDt_ne_dnX : lDt ≠ dnX := by decide
@[simp] theorem dfa_dnX_ne_lDg : dnX ≠ lDg := by decide
@[simp] theorem dfa_lDg_ne_dnX : lDg ≠ dnX := by decide
@[simp] theorem dfa_dnX_ne_lDi : dnX ≠ lDi := by decide
@[simp] theorem dfa_lDi_ne_dnX : lDi ≠ dnX := by decide
@[simp] theorem dfa_dnX_ne_lRp : dnX ≠ lRp := by decide
@[simp] theorem dfa_lRp_ne_dnX : lRp ≠ dnX := by decide
@[simp] theorem dfa_dnX_ne_lRn : dnX ≠ lRn := by decide
@[simp] theorem dfa_lRn_ne_dnX : lRn ≠ dnX := by decide
@[simp] theorem dfa_dnX_ne_lDir : dnX ≠ lDir := by decide
@[simp] theorem dfa_lDir_ne_dnX : lDir ≠ dnX := by decide
@[simp] theorem dfa_dnX_ne_lFle : dnX ≠ lFle := by decide
@[simp] theorem dfa_lFle_ne_dnX : lFle ≠ dnX := by decide
@[simp] theorem dfa_dnX_ne_lKb : dnX ≠ lKb := by decide
@[simp] theorem dfa_lKb_ne_dnX : lKb ≠ dnX := by decide
@[simp] theorem dfa_dnY_ne_dnA : dnY ≠ dnA := by decide
@[simp] theorem dfa_dnY_ne_dnB : dnY ≠ dnB := by decide
@[simp] theorem dfa_dnY_ne_dnX : dnY ≠ dnX := by decide
@[simp] theorem dfa_dnY_ne_lFl : dnY ≠ lFl := by decide
@[simp] theorem dfa_lFl_ne_dnY : lFl ≠ dnY := by decide
@[simp] theorem dfa_dnY_ne_lDh : dnY ≠ lDh := by decide
@[simp] theorem dfa_lDh_ne_dnY : lDh ≠ dnY := by decide
@[simp] theorem dfa_dnY_ne_lDt : dnY ≠ lDt := by decide
@[simp] theorem dfa_lDt_ne_dnY : lDt ≠ dnY := by decide
@[simp] theorem dfa_dnY_ne_lDg : dnY ≠ lDg := by decide
@[simp] theorem dfa_lDg_ne_dnY : lDg ≠ dnY := by decide
@[simp] theorem dfa_dnY_ne_lDi : dnY ≠ lDi := by decide
@[simp] theorem dfa_lDi_ne_dnY : lDi ≠ dnY := by decide
@[simp] theorem dfa_dnY_ne_lRp : dnY ≠ lRp := by decide
@[simp] theorem dfa_lRp_ne_dnY : lRp ≠ dnY := by decide
@[simp] theorem dfa_dnY_ne_lRn : dnY ≠ lRn := by decide
@[simp] theorem dfa_lRn_ne_dnY : lRn ≠ dnY := by decide
@[simp] theorem dfa_dnY_ne_lDir : dnY ≠ lDir := by decide
@[simp] theorem dfa_lDir_ne_dnY : lDir ≠ dnY := by decide
@[simp] theorem dfa_dnY_ne_lFle : dnY ≠ lFle := by decide
@[simp] theorem dfa_lFle_ne_dnY : lFle ≠ dnY := by decide
@[simp] theorem dfa_dnY_ne_lKb : dnY ≠ lKb := by decide
@[simp] theorem dfa_lKb_ne_dnY : lKb ≠ dnY := by decide
@[simp] theorem dfa_izE_ne_izW : izE ≠ izW := by decide
@[simp] theorem dfa_izE_ne_izC : izE ≠ izC := by decide
@[simp] theorem dfa_izE_ne_izU : izE ≠ izU := by decide
@[simp] theorem dfa_izE_ne_izZ : izE ≠ izZ := by decide
@[simp] theorem dfa_izE_ne_izL : izE ≠ izL := by decide
@[simp] theorem dfa_izE_ne_lFl : izE ≠ lFl := by decide
@[simp] theorem dfa_lFl_ne_izE : lFl ≠ izE := by decide
@[simp] theorem dfa_izE_ne_lDh : izE ≠ lDh := by decide
@[simp] theorem dfa_lDh_ne_izE : lDh ≠ izE := by decide
@[simp] theorem dfa_izE_ne_lDt : izE ≠ lDt := by decide
@[simp] theorem dfa_lDt_ne_izE : lDt ≠ izE := by decide
@[simp] theorem dfa_izE_ne_lDg : izE ≠ lDg := by decide
@[simp] theorem dfa_lDg_ne_izE : lDg ≠ izE := by decide
@[simp] theorem dfa_izE_ne_lDi : izE ≠ lDi := by decide
@[simp] theorem dfa_lDi_ne_izE : lDi ≠ izE := by decide
@[simp] theorem dfa_izE_ne_lRp : izE ≠ lRp := by decide
@[simp] theorem dfa_lRp_ne_izE : lRp ≠ izE := by decide
@[simp] theorem dfa_izE_ne_lRn : izE ≠ lRn := by decide
@[simp] theorem dfa_lRn_ne_izE : lRn ≠ izE := by decide
@[simp] theorem dfa_izE_ne_lDir : izE ≠ lDir := by decide
@[simp] theorem dfa_lDir_ne_izE : lDir ≠ izE := by decide
@[simp] theorem dfa_izE_ne_lFle : izE ≠ lFle := by decide
@[simp] theorem dfa_lFle_ne_izE : lFle ≠ izE := by decide
@[simp] theorem dfa_izE_ne_lKb : izE ≠ lKb := by decide
@[simp] theorem dfa_lKb_ne_izE : lKb ≠ izE := by decide
@[simp] theorem dfa_izW_ne_izE : izW ≠ izE := by decide
@[simp] theorem dfa_izW_ne_izC : izW ≠ izC := by decide
@[simp] theorem dfa_izW_ne_izU : izW ≠ izU := by decide
@[simp] theorem dfa_izW_ne_izZ : izW ≠ izZ := by decide
@[simp] theorem dfa_izW_ne_izL : izW ≠ izL := by decide
@[simp] theorem dfa_izW_ne_lFl : izW ≠ lFl := by decide
@[simp] theorem dfa_lFl_ne_izW : lFl ≠ izW := by decide
@[simp] theorem dfa_izW_ne_lDh : izW ≠ lDh := by decide
@[simp] theorem dfa_lDh_ne_izW : lDh ≠ izW := by decide
@[simp] theorem dfa_izW_ne_lDt : izW ≠ lDt := by decide
@[simp] theorem dfa_lDt_ne_izW : lDt ≠ izW := by decide
@[simp] theorem dfa_izW_ne_lDg : izW ≠ lDg := by decide
@[simp] theorem dfa_lDg_ne_izW : lDg ≠ izW := by decide
@[simp] theorem dfa_izW_ne_lDi : izW ≠ lDi := by decide
@[simp] theorem dfa_lDi_ne_izW : lDi ≠ izW := by decide
@[simp] theorem dfa_izW_ne_lRp : izW ≠ lRp := by decide
@[simp] theorem dfa_lRp_ne_izW : lRp ≠ izW := by decide
@[simp] theorem dfa_izW_ne_lRn : izW ≠ lRn := by decide
@[simp] theorem dfa_lRn_ne_izW : lRn ≠ izW := by decide
@[simp] theorem dfa_izW_ne_lDir : izW ≠ lDir := by decide
@[simp] theorem dfa_lDir_ne_izW : lDir ≠ izW := by decide
@[simp] theorem dfa_izW_ne_lFle : izW ≠ lFle := by decide
@[simp] theorem dfa_lFle_ne_izW : lFle ≠ izW := by decide
@[simp] theorem dfa_izW_ne_lKb : izW ≠ lKb := by decide
@[simp] theorem dfa_lKb_ne_izW : lKb ≠ izW := by decide
@[simp] theorem dfa_izC_ne_izE : izC ≠ izE := by decide
@[simp] theorem dfa_izC_ne_izW : izC ≠ izW := by decide
@[simp] theorem dfa_izC_ne_izU : izC ≠ izU := by decide
@[simp] theorem dfa_izC_ne_izZ : izC ≠ izZ := by decide
@[simp] theorem dfa_izC_ne_izL : izC ≠ izL := by decide
@[simp] theorem dfa_izC_ne_lFl : izC ≠ lFl := by decide
@[simp] theorem dfa_lFl_ne_izC : lFl ≠ izC := by decide
@[simp] theorem dfa_izC_ne_lDh : izC ≠ lDh := by decide
@[simp] theorem dfa_lDh_ne_izC : lDh ≠ izC := by decide
@[simp] theorem dfa_izC_ne_lDt : izC ≠ lDt := by decide
@[simp] theorem dfa_lDt_ne_izC : lDt ≠ izC := by decide
@[simp] theorem dfa_izC_ne_lDg : izC ≠ lDg := by decide
@[simp] theorem dfa_lDg_ne_izC : lDg ≠ izC := by decide
@[simp] theorem dfa_izC_ne_lDi : izC ≠ lDi := by decide
@[simp] theorem dfa_lDi_ne_izC : lDi ≠ izC := by decide
@[simp] theorem dfa_izC_ne_lRp : izC ≠ lRp := by decide
@[simp] theorem dfa_lRp_ne_izC : lRp ≠ izC := by decide
@[simp] theorem dfa_izC_ne_lRn : izC ≠ lRn := by decide
@[simp] theorem dfa_lRn_ne_izC : lRn ≠ izC := by decide
@[simp] theorem dfa_izC_ne_lDir : izC ≠ lDir := by decide
@[simp] theorem dfa_lDir_ne_izC : lDir ≠ izC := by decide
@[simp] theorem dfa_izC_ne_lFle : izC ≠ lFle := by decide
@[simp] theorem dfa_lFle_ne_izC : lFle ≠ izC := by decide
@[simp] theorem dfa_izC_ne_lKb : izC ≠ lKb := by decide
@[simp] theorem dfa_lKb_ne_izC : lKb ≠ izC := by decide
@[simp] theorem dfa_izU_ne_izE : izU ≠ izE := by decide
@[simp] theorem dfa_izU_ne_izW : izU ≠ izW := by decide
@[simp] theorem dfa_izU_ne_izC : izU ≠ izC := by decide
@[simp] theorem dfa_izU_ne_izZ : izU ≠ izZ := by decide
@[simp] theorem dfa_izU_ne_izL : izU ≠ izL := by decide
@[simp] theorem dfa_izU_ne_lFl : izU ≠ lFl := by decide
@[simp] theorem dfa_lFl_ne_izU : lFl ≠ izU := by decide
@[simp] theorem dfa_izU_ne_lDh : izU ≠ lDh := by decide
@[simp] theorem dfa_lDh_ne_izU : lDh ≠ izU := by decide
@[simp] theorem dfa_izU_ne_lDt : izU ≠ lDt := by decide
@[simp] theorem dfa_lDt_ne_izU : lDt ≠ izU := by decide
@[simp] theorem dfa_izU_ne_lDg : izU ≠ lDg := by decide
@[simp] theorem dfa_lDg_ne_izU : lDg ≠ izU := by decide
@[simp] theorem dfa_izU_ne_lDi : izU ≠ lDi := by decide
@[simp] theorem dfa_lDi_ne_izU : lDi ≠ izU := by decide
@[simp] theorem dfa_izU_ne_lRp : izU ≠ lRp := by decide
@[simp] theorem dfa_lRp_ne_izU : lRp ≠ izU := by decide
@[simp] theorem dfa_izU_ne_lRn : izU ≠ lRn := by decide
@[simp] theorem dfa_lRn_ne_izU : lRn ≠ izU := by decide
@[simp] theorem dfa_izU_ne_lDir : izU ≠ lDir := by decide
@[simp] theorem dfa_lDir_ne_izU : lDir ≠ izU := by decide
@[simp] theorem dfa_izU_ne_lFle : izU ≠ lFle := by decide
@[simp] theorem dfa_lFle_ne_izU : lFle ≠ izU := by decide
@[simp] theorem dfa_izU_ne_lKb : izU ≠ lKb := by decide
@[simp] theorem dfa_lKb_ne_izU : lKb ≠ izU := by decide
@[simp] theorem dfa_izZ_ne_izE : izZ ≠ izE := by decide
@[simp] theorem dfa_izZ_ne_izW : izZ ≠ izW := by decide
@[simp] theorem dfa_izZ_ne_izC : izZ ≠ izC := by decide
@[simp] theorem dfa_izZ_ne_izU : izZ ≠ izU := by decide
@[simp] theorem dfa_izZ_ne_izL : izZ ≠ izL := by decide
@[simp] theorem dfa_izZ_ne_lFl : izZ ≠ lFl := by decide
@[simp] theorem dfa_lFl_ne_izZ : lFl ≠ izZ := by decide
@[simp] theorem dfa_izZ_ne_lDh : izZ ≠ lDh := by decide
@[simp] theorem dfa_lDh_ne_izZ : lDh ≠ izZ := by decide
@[simp] theorem dfa_izZ_ne_lDt : izZ ≠ lDt := by decide
@[simp] theorem dfa_lDt_ne_izZ : lDt ≠ izZ := by decide
@[simp] theorem dfa_izZ_ne_lDg : izZ ≠ lDg := by decide
@[simp] theorem dfa_lDg_ne_izZ : lDg ≠ izZ := by decide
@[simp] theorem dfa_izZ_ne_lDi : izZ ≠ lDi := by decide
@[simp] theorem dfa_lDi_ne_izZ : lDi ≠ izZ := by decide
@[simp] theorem dfa_izZ_ne_lRp : izZ ≠ lRp := by decide
@[simp] theorem dfa_lRp_ne_izZ : lRp ≠ izZ := by decide
@[simp] theorem dfa_izZ_ne_lRn : izZ ≠ lRn := by decide
@[simp] theorem dfa_lRn_ne_izZ : lRn ≠ izZ := by decide
@[simp] theorem dfa_izZ_ne_lDir : izZ ≠ lDir := by decide
@[simp] theorem dfa_lDir_ne_izZ : lDir ≠ izZ := by decide
@[simp] theorem dfa_izZ_ne_lFle : izZ ≠ lFle := by decide
@[simp] theorem dfa_lFle_ne_izZ : lFle ≠ izZ := by decide
@[simp] theorem dfa_izZ_ne_lKb : izZ ≠ lKb := by decide
@[simp] theorem dfa_lKb_ne_izZ : lKb ≠ izZ := by decide
@[simp] theorem dfa_izL_ne_izE : izL ≠ izE := by decide
@[simp] theorem dfa_izL_ne_izW : izL ≠ izW := by decide
@[simp] theorem dfa_izL_ne_izC : izL ≠ izC := by decide
@[simp] theorem dfa_izL_ne_izU : izL ≠ izU := by decide
@[simp] theorem dfa_izL_ne_izZ : izL ≠ izZ := by decide
@[simp] theorem dfa_izL_ne_lFl : izL ≠ lFl := by decide
@[simp] theorem dfa_lFl_ne_izL : lFl ≠ izL := by decide
@[simp] theorem dfa_izL_ne_lDh : izL ≠ lDh := by decide
@[simp] theorem dfa_lDh_ne_izL : lDh ≠ izL := by decide
@[simp] theorem dfa_izL_ne_lDt : izL ≠ lDt := by decide
@[simp] theorem dfa_lDt_ne_izL : lDt ≠ izL := by decide
@[simp] theorem dfa_izL_ne_lDg : izL ≠ lDg := by decide
@[simp] theorem dfa_lDg_ne_izL : lDg ≠ izL := by decide
@[simp] theorem dfa_izL_ne_lDi : izL ≠ lDi := by decide
@[simp] theorem dfa_lDi_ne_izL : lDi ≠ izL := by decide
@[simp] theorem dfa_izL_ne_lRp : izL ≠ lRp := by decide
@[simp] theorem dfa_lRp_ne_izL : lRp ≠ izL := by decide
@[simp] theorem dfa_izL_ne_lRn : izL ≠ lRn := by decide
@[simp] theorem dfa_lRn_ne_izL : lRn ≠ izL := by decide
@[simp] theorem dfa_izL_ne_lDir : izL ≠ lDir := by decide
@[simp] theorem dfa_lDir_ne_izL : lDir ≠ izL := by decide
@[simp] theorem dfa_izL_ne_lFle : izL ≠ lFle := by decide
@[simp] theorem dfa_lFle_ne_izL : lFle ≠ izL := by decide
@[simp] theorem dfa_izL_ne_lKb : izL ≠ lKb := by decide
@[simp] theorem dfa_lKb_ne_izL : lKb ≠ izL := by decide

def hpBody : ProgHOL 64 := prologue [hpH] (.seq (.call (some (some (.local, hpH), none)) fGetAppFn [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv hpE)]) (.ite (tagIsE hpH 9) (.return (.const 1)) (.return (.const 0))))
def dnBody : ProgHOL 64 := prologue [dnX, dnY] (.seq (.call (some (some (.local, dnX), none)) ExM.fHasFvar [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv dnA)]) (.ite (vv dnX) (.return (.const 0)) (.seq (.call (some (some (.local, dnY), none)) ExM.fHasFvar [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv dnB)]) (.ite (vv dnY) (.return (.const 0)) (.return (.const 1))))))
def izLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, izW, izC, izU, izZ, izL]
def izBody (C : Ctx) : ProgHOL 64 := prologue izLocals (.ite (tagIsE izE 8) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv izE)) (.seq eViewP (.seq (.assign .local izW (.load .one (vv lRp))) (.ite (.cmp .equal (vv izW) (.const 0)) (.return (.cmp .equal (vv lRn) (.const 1))) (.return (.const 0))))))) (.ite (tagIsE izE 3) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv izE)) (.seq eViewP (.seq (.assign .local izC (.load .one (vv lRp))) (.seq (.assign .local izU (.load .one (.op .add [(vv lRp), (.const 8)]))) (.seq (.assign .local izL (.load .one (.const (ecell C (C.PO + pinCount + 0))))) (.seq (.assign .local izZ (.load .one (.const (ecell C (C.PO + PIN_NAT_ZERO))))) (.return (.op .and [.cmp .equal (vv izC) (vv izZ), .cmp .equal (vv izU) (vv izL)]))))))))) (.return (.const 0))))

section
variable {σ : Type}

theorem hp_spec (C : Ctx) (hcaf : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one))
    (s : AState) (e : EIdx) :
    SpecR (σ := σ) (Pre C s ([hpE].zip [Enc.idxW e])) hpBody s (headIsProj e) (PostB C) := by
  refine specR_prologue (postB_locals C) (Knot.params_none C [hpH] [hpE] _ (by decide) (by decide)) ?_
  unfold headIsProj
  refine specR_callNIM (C := C) hpH fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv hpE]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e] (by decide) rfl (by decide) hcaf
    ⟨rfl, by simp +decide [Env.get, ctxEnv], trivial⟩
    (fun a w s' st => getAppFn coreWalkFuel e s = .ok (a, s') ∧ Post C s a w s' st)
    (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec C hcaf coreWalkFuel e s CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun h w s' st ⟨hrun, hw, hs, _⟩ => ?_)
  subst hw
  refine Knot.specR_tagIteV hpH h 9 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
  · exact specR_returnI _ (boolW true) (by simp [boolW]; rfl)
      (fun t ht => ⟨C.H, List.prefix_refl _, by simp [htg, ETag.proj], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · exact specR_returnI _ (boolW false) (by simp [boolW]; rfl)
      (fun t ht => ⟨C.H, List.prefix_refl _, by simpa [ETag.proj, boolW] using htg, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem dn_spec (C : Ctx) (hok : CtxOK C) (hcF : ExF.CodesF C (ExF.bodyF C))
    (hfvb : C.code.lookup ExF.fFvarB = some ([(pFu, .one), (pH, .one)], ExF.fvbBody C, .one))
    (hhf : C.code.lookup ExM.fHasFvar = some ([(pFu, .one), (pH, .one)], ExM.hasFvarBody, .one))
    (s : AState) (a b : EIdx) :
    SpecR (σ := σ) (Pre C s ([dnA, dnB].zip [Enc.idxW a, Enc.idxW b])) dnBody s (defeqNoFvars a b) (PostB C) := by
  refine specR_prologue (postB_locals C) (Knot.params_none C [dnX, dnY] [dnA, dnB] _ (by decide) (by decide)) ?_
  unfold defeqNoFvars
  refine specR_callNIM (C := C) dnX ExM.fHasFvar [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv dnA]
    ExM.hasFvarBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW a] (by decide) rfl (by decide) hhf
    ⟨rfl, by simp +decide [Env.get, ctxEnv], trivial⟩ (ExM.PostB C) (fun _ _ _ _ hp => hp.2)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (ExM.hasFvar_spec C hok hcF hfvb s coreWalkFuel a CV.coreWalkFuel_lt))
    (fun x w s1 st ⟨hw, _⟩ => ?_)
  subst hw
  cases x
  · refine specR_ifI _ 0 (by simp) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine specR_callNIM (C := C) dnY ExM.fHasFvar [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv dnB]
      ExM.hasFvarBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW b] (by decide) rfl (by decide) hhf
      ⟨rfl, by simp +decide [Env.get, ctxEnv], trivial⟩ (ExM.PostB C) (fun _ _ _ _ hp => hp.2)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
        (ExM.hasFvar_spec C hok hcF hfvb s1 coreWalkFuel b CV.coreWalkFuel_lt))
      (fun y w s2 st ⟨hw, _⟩ => ?_)
    subst hw
    cases y
    · refine specR_ifI _ 0 (by simp) (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_returnI _ (boolW true) (by simp [boolW]; rfl)
        (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_ifI _ 1 (by simp) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ (boolW false) (by simp [boolW]; rfl)
        (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_ifI _ 1 (by simp) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [↓reduceIte]
    exact specR_returnI _ (boolW false) (by simp [boolW]; rfl)
      (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem iz_spec (C : Ctx) (hok : CtxOK C) (s : AState) (e : EIdx) :
    SpecR (σ := σ) (Pre C s ([izE].zip [Enc.idxW e])) (izBody C) s (isNatZero e) (PostB C) := by
  refine specR_prologue (postB_locals C) (Knot.params_none C izLocals [izE] _ (by decide) (by decide)) ?_
  unfold isNatZero
  have hno : ∀ {Γ : Env} {M : Mem} {D : List MlS},
      SpecR (σ := σ) (Inv C s Γ M D) (.return (.const 0)) s (pure false) (PostB C) := fun {Γ M D} =>
    specR_returnI _ (boolW false) (by simp [sev, boolW])
      (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine Knot.specR_tagIteV izE e 8 (by decide) (by decide) (by simp +decide [Env.get, ctxEnv]) (fun htg => ?_) (fun htg => ?_)
  · rw [ite_eq_left (show (e.tag == ETag.lit) = true by simp [htg, ETag.lit])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv izE) (Enc.idxW e) (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine ILP.specR_viewIv e (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
      (fun v P hv htn _ => ?_)
    have h8 : v.tagN = 8 := by rw [htn, htg]; rfl
    obtain ⟨l, rfl⟩ := tagN_lit h8
    rcases l with m | str
    · refine specR_loadI' izW (vv lRp) P (P + BitVec.ofNat 64 0) 0 (by decide) (by simp) (by simp)
        (by simpa [encEView, Enc.encLit] using wordsAt_mem0 P 0 (limbs m) []) ?_
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      dsimp only
      refine specR_returnI _ (boolW (m == 0)) ?_
        (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      have hl1 : (encEView (.lit (.natVal m))).length = (limbs m).length + 1 := by simp [encEView, Enc.encLit]
      by_cases m0 : m = 0
      · subst m0; simp [sev, hl1, limbs_zero, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      · have hpos : (limbs m).length ≠ 0 := by rw [limbs_pos m0]; simp
        have hlt : (limbs m).length + 1 < 2 ^ 61 := by rw [← hl1]; assumption
        have hne : BitVec.ofNat 64 ((limbs m).length + 1) ≠ 1#64 := by
          intro e; have := congrArg BitVec.toNat e; simp at this; omega
        simp [sev, hl1, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne, m0]
    · refine specR_loadI' izW (vv lRp) P (P + BitVec.ofNat 64 0) 1 (by decide) (by simp) (by simp)
        (by simpa [encEView, Enc.encLit] using wordsAt_mem0 P 1 (strW str) []) ?_
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
        (fun _ => ?_)
      dsimp only
      exact hno
  · rw [ite_eq_right (show ¬ (e.tag == ETag.lit) = true by simpa [ETag.lit] using htg)]
    refine Knot.specR_tagIteV izE e 3 (by decide) (by decide) (by simp +decide [Env.get, ctxEnv]) (fun htc => ?_)
      (fun htc => ?_)
    swap
    · rw [ite_eq_right (show ¬ (e.tag == ETag.const) = true by simpa [ETag.const] using htc)]
      exact hno
    rw [ite_eq_left (show (e.tag == ETag.const) = true by simp [htc, ETag.const])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv izE) (Enc.idxW e) (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_viewP e (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
      (fun v P hv htn _ => ?_)
    refine specR_congr (view_bind_eq e v _ s hv) ?_
    have h3 : v.tagN = 3 := by rw [htn, htc]; rfl
    obtain ⟨c, us, rfl⟩ := UD.tagN_const h3
    dsimp only
    refine specR_loadI' izC (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW c) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW c) [Enc.idxW us] []) ?_
    refine specR_loadI' izU _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW us) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW c) (Enc.idxW us) [] []) ?_
    refine specR_dropM ?_
    refine specR_pinXI hok pinEmptyLevels 0 C.pins.emptyLevels _ (fun s hp => pinEmptyLevels_run hok hp)
      (pin_emptyLevels_cell hok) izL (by decide) ?_
    unfold pinNatZero
    refine specR_pinAtI hok PIN_NAT_ZERO (by decide) izZ (by decide) ?_
    refine specR_returnI _ (boolW (c == C.pins.names[PIN_NAT_ZERO]'(by rw [hok.pinsRel.1]; decide) &&
      us == C.pins.emptyLevels)) ?_ (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    simp only [sev, sev_vv]
    simp
    by_cases e1 : c = C.pins.names[PIN_NAT_ZERO]'(by rw [hok.pinsRel.1]; decide)
    · by_cases e2 : us = C.pins.emptyLevels
      · simp [e1, e2, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      · have : Enc.idxW us ≠ Enc.idxW C.pins.emptyLevels := fun x => e2 (Enc.idxW_inj x)
        simp [e1, e2, this, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    · have : Enc.idxW c ≠ Enc.idxW (C.pins.names[PIN_NAT_ZERO]'(by rw [hok.pinsRel.1]; decide)) :=
        fun x => e1 (Enc.idxW_inj x)
      simp [e1, this, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

end

end ConPanqueque.T.WC
