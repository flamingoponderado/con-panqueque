import ConPanqueque.T.Core.ProjGuardRows
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `openPisRawGo`

Open the first `n` ∀-binders at fresh free variables `i, i+1, …`, each domain instantiated with the accumulator,
the residual left raw. Answers `0` for `none`, else a pair block `[acc block, residual]` (the opened free
variables themselves are not used downstream and are not built).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def opA := ofString "opn_a"
def opN := ofString "opn_n"
def opH := ofString "opn_h"
def opI := ofString "opn_i"
def opDm := ofString "opn_dm"
def opB := ofString "opn_b"
def opL := ofString "opn_l"
def opD := ofString "opn_d"
def opV := ofString "opn_v"
def opA2 := ofString "opn_a2"
def opR := ofString "opn_r"
def opO := ofString "opn_o"
def fOp := ofString "openPisRawGo"

@[simp] theorem op_opA_ne_opN : opA ≠ opN := by decide
@[simp] theorem op_opA_ne_opH : opA ≠ opH := by decide
@[simp] theorem op_opA_ne_opI : opA ≠ opI := by decide
@[simp] theorem op_opA_ne_opDm : opA ≠ opDm := by decide
@[simp] theorem op_opA_ne_opB : opA ≠ opB := by decide
@[simp] theorem op_opA_ne_opL : opA ≠ opL := by decide
@[simp] theorem op_opA_ne_opD : opA ≠ opD := by decide
@[simp] theorem op_opA_ne_opV : opA ≠ opV := by decide
@[simp] theorem op_opA_ne_opA2 : opA ≠ opA2 := by decide
@[simp] theorem op_opA_ne_opR : opA ≠ opR := by decide
@[simp] theorem op_opA_ne_opO : opA ≠ opO := by decide
@[simp] theorem op_opA_ne_lFl : opA ≠ lFl := by decide
@[simp] theorem op_lFl_ne_opA : lFl ≠ opA := by decide
@[simp] theorem op_opA_ne_lDh : opA ≠ lDh := by decide
@[simp] theorem op_lDh_ne_opA : lDh ≠ opA := by decide
@[simp] theorem op_opA_ne_lDt : opA ≠ lDt := by decide
@[simp] theorem op_lDt_ne_opA : lDt ≠ opA := by decide
@[simp] theorem op_opA_ne_lDg : opA ≠ lDg := by decide
@[simp] theorem op_lDg_ne_opA : lDg ≠ opA := by decide
@[simp] theorem op_opA_ne_lDi : opA ≠ lDi := by decide
@[simp] theorem op_lDi_ne_opA : lDi ≠ opA := by decide
@[simp] theorem op_opA_ne_lRp : opA ≠ lRp := by decide
@[simp] theorem op_lRp_ne_opA : lRp ≠ opA := by decide
@[simp] theorem op_opA_ne_lRn : opA ≠ lRn := by decide
@[simp] theorem op_lRn_ne_opA : lRn ≠ opA := by decide
@[simp] theorem op_opA_ne_lDir : opA ≠ lDir := by decide
@[simp] theorem op_lDir_ne_opA : lDir ≠ opA := by decide
@[simp] theorem op_opA_ne_lFle : opA ≠ lFle := by decide
@[simp] theorem op_lFle_ne_opA : lFle ≠ opA := by decide
@[simp] theorem op_opA_ne_lKb : opA ≠ lKb := by decide
@[simp] theorem op_lKb_ne_opA : lKb ≠ opA := by decide
@[simp] theorem op_opN_ne_opA : opN ≠ opA := by decide
@[simp] theorem op_opN_ne_opH : opN ≠ opH := by decide
@[simp] theorem op_opN_ne_opI : opN ≠ opI := by decide
@[simp] theorem op_opN_ne_opDm : opN ≠ opDm := by decide
@[simp] theorem op_opN_ne_opB : opN ≠ opB := by decide
@[simp] theorem op_opN_ne_opL : opN ≠ opL := by decide
@[simp] theorem op_opN_ne_opD : opN ≠ opD := by decide
@[simp] theorem op_opN_ne_opV : opN ≠ opV := by decide
@[simp] theorem op_opN_ne_opA2 : opN ≠ opA2 := by decide
@[simp] theorem op_opN_ne_opR : opN ≠ opR := by decide
@[simp] theorem op_opN_ne_opO : opN ≠ opO := by decide
@[simp] theorem op_opN_ne_lFl : opN ≠ lFl := by decide
@[simp] theorem op_lFl_ne_opN : lFl ≠ opN := by decide
@[simp] theorem op_opN_ne_lDh : opN ≠ lDh := by decide
@[simp] theorem op_lDh_ne_opN : lDh ≠ opN := by decide
@[simp] theorem op_opN_ne_lDt : opN ≠ lDt := by decide
@[simp] theorem op_lDt_ne_opN : lDt ≠ opN := by decide
@[simp] theorem op_opN_ne_lDg : opN ≠ lDg := by decide
@[simp] theorem op_lDg_ne_opN : lDg ≠ opN := by decide
@[simp] theorem op_opN_ne_lDi : opN ≠ lDi := by decide
@[simp] theorem op_lDi_ne_opN : lDi ≠ opN := by decide
@[simp] theorem op_opN_ne_lRp : opN ≠ lRp := by decide
@[simp] theorem op_lRp_ne_opN : lRp ≠ opN := by decide
@[simp] theorem op_opN_ne_lRn : opN ≠ lRn := by decide
@[simp] theorem op_lRn_ne_opN : lRn ≠ opN := by decide
@[simp] theorem op_opN_ne_lDir : opN ≠ lDir := by decide
@[simp] theorem op_lDir_ne_opN : lDir ≠ opN := by decide
@[simp] theorem op_opN_ne_lFle : opN ≠ lFle := by decide
@[simp] theorem op_lFle_ne_opN : lFle ≠ opN := by decide
@[simp] theorem op_opN_ne_lKb : opN ≠ lKb := by decide
@[simp] theorem op_lKb_ne_opN : lKb ≠ opN := by decide
@[simp] theorem op_opH_ne_opA : opH ≠ opA := by decide
@[simp] theorem op_opH_ne_opN : opH ≠ opN := by decide
@[simp] theorem op_opH_ne_opI : opH ≠ opI := by decide
@[simp] theorem op_opH_ne_opDm : opH ≠ opDm := by decide
@[simp] theorem op_opH_ne_opB : opH ≠ opB := by decide
@[simp] theorem op_opH_ne_opL : opH ≠ opL := by decide
@[simp] theorem op_opH_ne_opD : opH ≠ opD := by decide
@[simp] theorem op_opH_ne_opV : opH ≠ opV := by decide
@[simp] theorem op_opH_ne_opA2 : opH ≠ opA2 := by decide
@[simp] theorem op_opH_ne_opR : opH ≠ opR := by decide
@[simp] theorem op_opH_ne_opO : opH ≠ opO := by decide
@[simp] theorem op_opH_ne_lFl : opH ≠ lFl := by decide
@[simp] theorem op_lFl_ne_opH : lFl ≠ opH := by decide
@[simp] theorem op_opH_ne_lDh : opH ≠ lDh := by decide
@[simp] theorem op_lDh_ne_opH : lDh ≠ opH := by decide
@[simp] theorem op_opH_ne_lDt : opH ≠ lDt := by decide
@[simp] theorem op_lDt_ne_opH : lDt ≠ opH := by decide
@[simp] theorem op_opH_ne_lDg : opH ≠ lDg := by decide
@[simp] theorem op_lDg_ne_opH : lDg ≠ opH := by decide
@[simp] theorem op_opH_ne_lDi : opH ≠ lDi := by decide
@[simp] theorem op_lDi_ne_opH : lDi ≠ opH := by decide
@[simp] theorem op_opH_ne_lRp : opH ≠ lRp := by decide
@[simp] theorem op_lRp_ne_opH : lRp ≠ opH := by decide
@[simp] theorem op_opH_ne_lRn : opH ≠ lRn := by decide
@[simp] theorem op_lRn_ne_opH : lRn ≠ opH := by decide
@[simp] theorem op_opH_ne_lDir : opH ≠ lDir := by decide
@[simp] theorem op_lDir_ne_opH : lDir ≠ opH := by decide
@[simp] theorem op_opH_ne_lFle : opH ≠ lFle := by decide
@[simp] theorem op_lFle_ne_opH : lFle ≠ opH := by decide
@[simp] theorem op_opH_ne_lKb : opH ≠ lKb := by decide
@[simp] theorem op_lKb_ne_opH : lKb ≠ opH := by decide
@[simp] theorem op_opI_ne_opA : opI ≠ opA := by decide
@[simp] theorem op_opI_ne_opN : opI ≠ opN := by decide
@[simp] theorem op_opI_ne_opH : opI ≠ opH := by decide
@[simp] theorem op_opI_ne_opDm : opI ≠ opDm := by decide
@[simp] theorem op_opI_ne_opB : opI ≠ opB := by decide
@[simp] theorem op_opI_ne_opL : opI ≠ opL := by decide
@[simp] theorem op_opI_ne_opD : opI ≠ opD := by decide
@[simp] theorem op_opI_ne_opV : opI ≠ opV := by decide
@[simp] theorem op_opI_ne_opA2 : opI ≠ opA2 := by decide
@[simp] theorem op_opI_ne_opR : opI ≠ opR := by decide
@[simp] theorem op_opI_ne_opO : opI ≠ opO := by decide
@[simp] theorem op_opI_ne_lFl : opI ≠ lFl := by decide
@[simp] theorem op_lFl_ne_opI : lFl ≠ opI := by decide
@[simp] theorem op_opI_ne_lDh : opI ≠ lDh := by decide
@[simp] theorem op_lDh_ne_opI : lDh ≠ opI := by decide
@[simp] theorem op_opI_ne_lDt : opI ≠ lDt := by decide
@[simp] theorem op_lDt_ne_opI : lDt ≠ opI := by decide
@[simp] theorem op_opI_ne_lDg : opI ≠ lDg := by decide
@[simp] theorem op_lDg_ne_opI : lDg ≠ opI := by decide
@[simp] theorem op_opI_ne_lDi : opI ≠ lDi := by decide
@[simp] theorem op_lDi_ne_opI : lDi ≠ opI := by decide
@[simp] theorem op_opI_ne_lRp : opI ≠ lRp := by decide
@[simp] theorem op_lRp_ne_opI : lRp ≠ opI := by decide
@[simp] theorem op_opI_ne_lRn : opI ≠ lRn := by decide
@[simp] theorem op_lRn_ne_opI : lRn ≠ opI := by decide
@[simp] theorem op_opI_ne_lDir : opI ≠ lDir := by decide
@[simp] theorem op_lDir_ne_opI : lDir ≠ opI := by decide
@[simp] theorem op_opI_ne_lFle : opI ≠ lFle := by decide
@[simp] theorem op_lFle_ne_opI : lFle ≠ opI := by decide
@[simp] theorem op_opI_ne_lKb : opI ≠ lKb := by decide
@[simp] theorem op_lKb_ne_opI : lKb ≠ opI := by decide
@[simp] theorem op_opDm_ne_opA : opDm ≠ opA := by decide
@[simp] theorem op_opDm_ne_opN : opDm ≠ opN := by decide
@[simp] theorem op_opDm_ne_opH : opDm ≠ opH := by decide
@[simp] theorem op_opDm_ne_opI : opDm ≠ opI := by decide
@[simp] theorem op_opDm_ne_opB : opDm ≠ opB := by decide
@[simp] theorem op_opDm_ne_opL : opDm ≠ opL := by decide
@[simp] theorem op_opDm_ne_opD : opDm ≠ opD := by decide
@[simp] theorem op_opDm_ne_opV : opDm ≠ opV := by decide
@[simp] theorem op_opDm_ne_opA2 : opDm ≠ opA2 := by decide
@[simp] theorem op_opDm_ne_opR : opDm ≠ opR := by decide
@[simp] theorem op_opDm_ne_opO : opDm ≠ opO := by decide
@[simp] theorem op_opDm_ne_lFl : opDm ≠ lFl := by decide
@[simp] theorem op_lFl_ne_opDm : lFl ≠ opDm := by decide
@[simp] theorem op_opDm_ne_lDh : opDm ≠ lDh := by decide
@[simp] theorem op_lDh_ne_opDm : lDh ≠ opDm := by decide
@[simp] theorem op_opDm_ne_lDt : opDm ≠ lDt := by decide
@[simp] theorem op_lDt_ne_opDm : lDt ≠ opDm := by decide
@[simp] theorem op_opDm_ne_lDg : opDm ≠ lDg := by decide
@[simp] theorem op_lDg_ne_opDm : lDg ≠ opDm := by decide
@[simp] theorem op_opDm_ne_lDi : opDm ≠ lDi := by decide
@[simp] theorem op_lDi_ne_opDm : lDi ≠ opDm := by decide
@[simp] theorem op_opDm_ne_lRp : opDm ≠ lRp := by decide
@[simp] theorem op_lRp_ne_opDm : lRp ≠ opDm := by decide
@[simp] theorem op_opDm_ne_lRn : opDm ≠ lRn := by decide
@[simp] theorem op_lRn_ne_opDm : lRn ≠ opDm := by decide
@[simp] theorem op_opDm_ne_lDir : opDm ≠ lDir := by decide
@[simp] theorem op_lDir_ne_opDm : lDir ≠ opDm := by decide
@[simp] theorem op_opDm_ne_lFle : opDm ≠ lFle := by decide
@[simp] theorem op_lFle_ne_opDm : lFle ≠ opDm := by decide
@[simp] theorem op_opDm_ne_lKb : opDm ≠ lKb := by decide
@[simp] theorem op_lKb_ne_opDm : lKb ≠ opDm := by decide
@[simp] theorem op_opB_ne_opA : opB ≠ opA := by decide
@[simp] theorem op_opB_ne_opN : opB ≠ opN := by decide
@[simp] theorem op_opB_ne_opH : opB ≠ opH := by decide
@[simp] theorem op_opB_ne_opI : opB ≠ opI := by decide
@[simp] theorem op_opB_ne_opDm : opB ≠ opDm := by decide
@[simp] theorem op_opB_ne_opL : opB ≠ opL := by decide
@[simp] theorem op_opB_ne_opD : opB ≠ opD := by decide
@[simp] theorem op_opB_ne_opV : opB ≠ opV := by decide
@[simp] theorem op_opB_ne_opA2 : opB ≠ opA2 := by decide
@[simp] theorem op_opB_ne_opR : opB ≠ opR := by decide
@[simp] theorem op_opB_ne_opO : opB ≠ opO := by decide
@[simp] theorem op_opB_ne_lFl : opB ≠ lFl := by decide
@[simp] theorem op_lFl_ne_opB : lFl ≠ opB := by decide
@[simp] theorem op_opB_ne_lDh : opB ≠ lDh := by decide
@[simp] theorem op_lDh_ne_opB : lDh ≠ opB := by decide
@[simp] theorem op_opB_ne_lDt : opB ≠ lDt := by decide
@[simp] theorem op_lDt_ne_opB : lDt ≠ opB := by decide
@[simp] theorem op_opB_ne_lDg : opB ≠ lDg := by decide
@[simp] theorem op_lDg_ne_opB : lDg ≠ opB := by decide
@[simp] theorem op_opB_ne_lDi : opB ≠ lDi := by decide
@[simp] theorem op_lDi_ne_opB : lDi ≠ opB := by decide
@[simp] theorem op_opB_ne_lRp : opB ≠ lRp := by decide
@[simp] theorem op_lRp_ne_opB : lRp ≠ opB := by decide
@[simp] theorem op_opB_ne_lRn : opB ≠ lRn := by decide
@[simp] theorem op_lRn_ne_opB : lRn ≠ opB := by decide
@[simp] theorem op_opB_ne_lDir : opB ≠ lDir := by decide
@[simp] theorem op_lDir_ne_opB : lDir ≠ opB := by decide
@[simp] theorem op_opB_ne_lFle : opB ≠ lFle := by decide
@[simp] theorem op_lFle_ne_opB : lFle ≠ opB := by decide
@[simp] theorem op_opB_ne_lKb : opB ≠ lKb := by decide
@[simp] theorem op_lKb_ne_opB : lKb ≠ opB := by decide
@[simp] theorem op_opL_ne_opA : opL ≠ opA := by decide
@[simp] theorem op_opL_ne_opN : opL ≠ opN := by decide
@[simp] theorem op_opL_ne_opH : opL ≠ opH := by decide
@[simp] theorem op_opL_ne_opI : opL ≠ opI := by decide
@[simp] theorem op_opL_ne_opDm : opL ≠ opDm := by decide
@[simp] theorem op_opL_ne_opB : opL ≠ opB := by decide
@[simp] theorem op_opL_ne_opD : opL ≠ opD := by decide
@[simp] theorem op_opL_ne_opV : opL ≠ opV := by decide
@[simp] theorem op_opL_ne_opA2 : opL ≠ opA2 := by decide
@[simp] theorem op_opL_ne_opR : opL ≠ opR := by decide
@[simp] theorem op_opL_ne_opO : opL ≠ opO := by decide
@[simp] theorem op_opL_ne_lFl : opL ≠ lFl := by decide
@[simp] theorem op_lFl_ne_opL : lFl ≠ opL := by decide
@[simp] theorem op_opL_ne_lDh : opL ≠ lDh := by decide
@[simp] theorem op_lDh_ne_opL : lDh ≠ opL := by decide
@[simp] theorem op_opL_ne_lDt : opL ≠ lDt := by decide
@[simp] theorem op_lDt_ne_opL : lDt ≠ opL := by decide
@[simp] theorem op_opL_ne_lDg : opL ≠ lDg := by decide
@[simp] theorem op_lDg_ne_opL : lDg ≠ opL := by decide
@[simp] theorem op_opL_ne_lDi : opL ≠ lDi := by decide
@[simp] theorem op_lDi_ne_opL : lDi ≠ opL := by decide
@[simp] theorem op_opL_ne_lRp : opL ≠ lRp := by decide
@[simp] theorem op_lRp_ne_opL : lRp ≠ opL := by decide
@[simp] theorem op_opL_ne_lRn : opL ≠ lRn := by decide
@[simp] theorem op_lRn_ne_opL : lRn ≠ opL := by decide
@[simp] theorem op_opL_ne_lDir : opL ≠ lDir := by decide
@[simp] theorem op_lDir_ne_opL : lDir ≠ opL := by decide
@[simp] theorem op_opL_ne_lFle : opL ≠ lFle := by decide
@[simp] theorem op_lFle_ne_opL : lFle ≠ opL := by decide
@[simp] theorem op_opL_ne_lKb : opL ≠ lKb := by decide
@[simp] theorem op_lKb_ne_opL : lKb ≠ opL := by decide
@[simp] theorem op_opD_ne_opA : opD ≠ opA := by decide
@[simp] theorem op_opD_ne_opN : opD ≠ opN := by decide
@[simp] theorem op_opD_ne_opH : opD ≠ opH := by decide
@[simp] theorem op_opD_ne_opI : opD ≠ opI := by decide
@[simp] theorem op_opD_ne_opDm : opD ≠ opDm := by decide
@[simp] theorem op_opD_ne_opB : opD ≠ opB := by decide
@[simp] theorem op_opD_ne_opL : opD ≠ opL := by decide
@[simp] theorem op_opD_ne_opV : opD ≠ opV := by decide
@[simp] theorem op_opD_ne_opA2 : opD ≠ opA2 := by decide
@[simp] theorem op_opD_ne_opR : opD ≠ opR := by decide
@[simp] theorem op_opD_ne_opO : opD ≠ opO := by decide
@[simp] theorem op_opD_ne_lFl : opD ≠ lFl := by decide
@[simp] theorem op_lFl_ne_opD : lFl ≠ opD := by decide
@[simp] theorem op_opD_ne_lDh : opD ≠ lDh := by decide
@[simp] theorem op_lDh_ne_opD : lDh ≠ opD := by decide
@[simp] theorem op_opD_ne_lDt : opD ≠ lDt := by decide
@[simp] theorem op_lDt_ne_opD : lDt ≠ opD := by decide
@[simp] theorem op_opD_ne_lDg : opD ≠ lDg := by decide
@[simp] theorem op_lDg_ne_opD : lDg ≠ opD := by decide
@[simp] theorem op_opD_ne_lDi : opD ≠ lDi := by decide
@[simp] theorem op_lDi_ne_opD : lDi ≠ opD := by decide
@[simp] theorem op_opD_ne_lRp : opD ≠ lRp := by decide
@[simp] theorem op_lRp_ne_opD : lRp ≠ opD := by decide
@[simp] theorem op_opD_ne_lRn : opD ≠ lRn := by decide
@[simp] theorem op_lRn_ne_opD : lRn ≠ opD := by decide
@[simp] theorem op_opD_ne_lDir : opD ≠ lDir := by decide
@[simp] theorem op_lDir_ne_opD : lDir ≠ opD := by decide
@[simp] theorem op_opD_ne_lFle : opD ≠ lFle := by decide
@[simp] theorem op_lFle_ne_opD : lFle ≠ opD := by decide
@[simp] theorem op_opD_ne_lKb : opD ≠ lKb := by decide
@[simp] theorem op_lKb_ne_opD : lKb ≠ opD := by decide
@[simp] theorem op_opV_ne_opA : opV ≠ opA := by decide
@[simp] theorem op_opV_ne_opN : opV ≠ opN := by decide
@[simp] theorem op_opV_ne_opH : opV ≠ opH := by decide
@[simp] theorem op_opV_ne_opI : opV ≠ opI := by decide
@[simp] theorem op_opV_ne_opDm : opV ≠ opDm := by decide
@[simp] theorem op_opV_ne_opB : opV ≠ opB := by decide
@[simp] theorem op_opV_ne_opL : opV ≠ opL := by decide
@[simp] theorem op_opV_ne_opD : opV ≠ opD := by decide
@[simp] theorem op_opV_ne_opA2 : opV ≠ opA2 := by decide
@[simp] theorem op_opV_ne_opR : opV ≠ opR := by decide
@[simp] theorem op_opV_ne_opO : opV ≠ opO := by decide
@[simp] theorem op_opV_ne_lFl : opV ≠ lFl := by decide
@[simp] theorem op_lFl_ne_opV : lFl ≠ opV := by decide
@[simp] theorem op_opV_ne_lDh : opV ≠ lDh := by decide
@[simp] theorem op_lDh_ne_opV : lDh ≠ opV := by decide
@[simp] theorem op_opV_ne_lDt : opV ≠ lDt := by decide
@[simp] theorem op_lDt_ne_opV : lDt ≠ opV := by decide
@[simp] theorem op_opV_ne_lDg : opV ≠ lDg := by decide
@[simp] theorem op_lDg_ne_opV : lDg ≠ opV := by decide
@[simp] theorem op_opV_ne_lDi : opV ≠ lDi := by decide
@[simp] theorem op_lDi_ne_opV : lDi ≠ opV := by decide
@[simp] theorem op_opV_ne_lRp : opV ≠ lRp := by decide
@[simp] theorem op_lRp_ne_opV : lRp ≠ opV := by decide
@[simp] theorem op_opV_ne_lRn : opV ≠ lRn := by decide
@[simp] theorem op_lRn_ne_opV : lRn ≠ opV := by decide
@[simp] theorem op_opV_ne_lDir : opV ≠ lDir := by decide
@[simp] theorem op_lDir_ne_opV : lDir ≠ opV := by decide
@[simp] theorem op_opV_ne_lFle : opV ≠ lFle := by decide
@[simp] theorem op_lFle_ne_opV : lFle ≠ opV := by decide
@[simp] theorem op_opV_ne_lKb : opV ≠ lKb := by decide
@[simp] theorem op_lKb_ne_opV : lKb ≠ opV := by decide
@[simp] theorem op_opA2_ne_opA : opA2 ≠ opA := by decide
@[simp] theorem op_opA2_ne_opN : opA2 ≠ opN := by decide
@[simp] theorem op_opA2_ne_opH : opA2 ≠ opH := by decide
@[simp] theorem op_opA2_ne_opI : opA2 ≠ opI := by decide
@[simp] theorem op_opA2_ne_opDm : opA2 ≠ opDm := by decide
@[simp] theorem op_opA2_ne_opB : opA2 ≠ opB := by decide
@[simp] theorem op_opA2_ne_opL : opA2 ≠ opL := by decide
@[simp] theorem op_opA2_ne_opD : opA2 ≠ opD := by decide
@[simp] theorem op_opA2_ne_opV : opA2 ≠ opV := by decide
@[simp] theorem op_opA2_ne_opR : opA2 ≠ opR := by decide
@[simp] theorem op_opA2_ne_opO : opA2 ≠ opO := by decide
@[simp] theorem op_opA2_ne_lFl : opA2 ≠ lFl := by decide
@[simp] theorem op_lFl_ne_opA2 : lFl ≠ opA2 := by decide
@[simp] theorem op_opA2_ne_lDh : opA2 ≠ lDh := by decide
@[simp] theorem op_lDh_ne_opA2 : lDh ≠ opA2 := by decide
@[simp] theorem op_opA2_ne_lDt : opA2 ≠ lDt := by decide
@[simp] theorem op_lDt_ne_opA2 : lDt ≠ opA2 := by decide
@[simp] theorem op_opA2_ne_lDg : opA2 ≠ lDg := by decide
@[simp] theorem op_lDg_ne_opA2 : lDg ≠ opA2 := by decide
@[simp] theorem op_opA2_ne_lDi : opA2 ≠ lDi := by decide
@[simp] theorem op_lDi_ne_opA2 : lDi ≠ opA2 := by decide
@[simp] theorem op_opA2_ne_lRp : opA2 ≠ lRp := by decide
@[simp] theorem op_lRp_ne_opA2 : lRp ≠ opA2 := by decide
@[simp] theorem op_opA2_ne_lRn : opA2 ≠ lRn := by decide
@[simp] theorem op_lRn_ne_opA2 : lRn ≠ opA2 := by decide
@[simp] theorem op_opA2_ne_lDir : opA2 ≠ lDir := by decide
@[simp] theorem op_lDir_ne_opA2 : lDir ≠ opA2 := by decide
@[simp] theorem op_opA2_ne_lFle : opA2 ≠ lFle := by decide
@[simp] theorem op_lFle_ne_opA2 : lFle ≠ opA2 := by decide
@[simp] theorem op_opA2_ne_lKb : opA2 ≠ lKb := by decide
@[simp] theorem op_lKb_ne_opA2 : lKb ≠ opA2 := by decide
@[simp] theorem op_opR_ne_opA : opR ≠ opA := by decide
@[simp] theorem op_opR_ne_opN : opR ≠ opN := by decide
@[simp] theorem op_opR_ne_opH : opR ≠ opH := by decide
@[simp] theorem op_opR_ne_opI : opR ≠ opI := by decide
@[simp] theorem op_opR_ne_opDm : opR ≠ opDm := by decide
@[simp] theorem op_opR_ne_opB : opR ≠ opB := by decide
@[simp] theorem op_opR_ne_opL : opR ≠ opL := by decide
@[simp] theorem op_opR_ne_opD : opR ≠ opD := by decide
@[simp] theorem op_opR_ne_opV : opR ≠ opV := by decide
@[simp] theorem op_opR_ne_opA2 : opR ≠ opA2 := by decide
@[simp] theorem op_opR_ne_opO : opR ≠ opO := by decide
@[simp] theorem op_opR_ne_lFl : opR ≠ lFl := by decide
@[simp] theorem op_lFl_ne_opR : lFl ≠ opR := by decide
@[simp] theorem op_opR_ne_lDh : opR ≠ lDh := by decide
@[simp] theorem op_lDh_ne_opR : lDh ≠ opR := by decide
@[simp] theorem op_opR_ne_lDt : opR ≠ lDt := by decide
@[simp] theorem op_lDt_ne_opR : lDt ≠ opR := by decide
@[simp] theorem op_opR_ne_lDg : opR ≠ lDg := by decide
@[simp] theorem op_lDg_ne_opR : lDg ≠ opR := by decide
@[simp] theorem op_opR_ne_lDi : opR ≠ lDi := by decide
@[simp] theorem op_lDi_ne_opR : lDi ≠ opR := by decide
@[simp] theorem op_opR_ne_lRp : opR ≠ lRp := by decide
@[simp] theorem op_lRp_ne_opR : lRp ≠ opR := by decide
@[simp] theorem op_opR_ne_lRn : opR ≠ lRn := by decide
@[simp] theorem op_lRn_ne_opR : lRn ≠ opR := by decide
@[simp] theorem op_opR_ne_lDir : opR ≠ lDir := by decide
@[simp] theorem op_lDir_ne_opR : lDir ≠ opR := by decide
@[simp] theorem op_opR_ne_lFle : opR ≠ lFle := by decide
@[simp] theorem op_lFle_ne_opR : lFle ≠ opR := by decide
@[simp] theorem op_opR_ne_lKb : opR ≠ lKb := by decide
@[simp] theorem op_lKb_ne_opR : lKb ≠ opR := by decide
@[simp] theorem op_opO_ne_opA : opO ≠ opA := by decide
@[simp] theorem op_opO_ne_opN : opO ≠ opN := by decide
@[simp] theorem op_opO_ne_opH : opO ≠ opH := by decide
@[simp] theorem op_opO_ne_opI : opO ≠ opI := by decide
@[simp] theorem op_opO_ne_opDm : opO ≠ opDm := by decide
@[simp] theorem op_opO_ne_opB : opO ≠ opB := by decide
@[simp] theorem op_opO_ne_opL : opO ≠ opL := by decide
@[simp] theorem op_opO_ne_opD : opO ≠ opD := by decide
@[simp] theorem op_opO_ne_opV : opO ≠ opV := by decide
@[simp] theorem op_opO_ne_opA2 : opO ≠ opA2 := by decide
@[simp] theorem op_opO_ne_opR : opO ≠ opR := by decide
@[simp] theorem op_opO_ne_lFl : opO ≠ lFl := by decide
@[simp] theorem op_lFl_ne_opO : lFl ≠ opO := by decide
@[simp] theorem op_opO_ne_lDh : opO ≠ lDh := by decide
@[simp] theorem op_lDh_ne_opO : lDh ≠ opO := by decide
@[simp] theorem op_opO_ne_lDt : opO ≠ lDt := by decide
@[simp] theorem op_lDt_ne_opO : lDt ≠ opO := by decide
@[simp] theorem op_opO_ne_lDg : opO ≠ lDg := by decide
@[simp] theorem op_lDg_ne_opO : lDg ≠ opO := by decide
@[simp] theorem op_opO_ne_lDi : opO ≠ lDi := by decide
@[simp] theorem op_lDi_ne_opO : lDi ≠ opO := by decide
@[simp] theorem op_opO_ne_lRp : opO ≠ lRp := by decide
@[simp] theorem op_lRp_ne_opO : lRp ≠ opO := by decide
@[simp] theorem op_opO_ne_lRn : opO ≠ lRn := by decide
@[simp] theorem op_lRn_ne_opO : lRn ≠ opO := by decide
@[simp] theorem op_opO_ne_lDir : opO ≠ lDir := by decide
@[simp] theorem op_lDir_ne_opO : lDir ≠ opO := by decide
@[simp] theorem op_opO_ne_lFle : opO ≠ lFle := by decide
@[simp] theorem op_lFle_ne_opO : lFle ≠ opO := by decide
@[simp] theorem op_opO_ne_lKb : opO ≠ lKb := by decide
@[simp] theorem op_lKb_ne_opO : lKb ≠ opO := by decide

def opParams : List MlS := [opA, opN, opH, opI]
def opLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, opDm, opB, opL, opD, opV, opA2, opR, opO]

def opBody (C : Ctx) : ProgHOL 64 := prologue opLocals
  (.ite (.cmp .equal (vv opN) (.const 0))
    (allocP C opO (.const 16) (.seq (.store (vv opO) (vv opA)) (.seq (.store (.op .add [vv opO, .const 8]) (vv opH))
      (.return (vv opO)))))
  (.ite (tagIsE opH 6)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv opH)) (.seq eViewP
    (.seq (.assign .local opDm (.load .one (vv lRp)))
    (.seq (.assign .local opB (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.assign .local opL (.load .one (vv opA)))
    (.seq (.call (some (some (.local, opD), none)) ExQ.fIrr
        [vv opA, .const 0, vv opL, .const (BitVec.ofNat 64 coreWalkFuel), vv opDm, .const 0])
    (.seq (.call (some (some (.local, opV), none)) fInternFVar [vv opD, vv opI])
    (.seq (.call (some (some (.local, opA2), none)) ExPre.fAppend [vv opA, vv opV])
    (.seq (.call (some (some (.local, opR), none)) fOp
        [vv opA2, .op .sub [vv opN, .const 1], vv opB, .op .add [vv opI, .const 1]])
      (.return (vv opR))))))))))))
    (.return (.const 0))))

section
variable {σ : Type}

/-- `0` for `none`, else the pair block `[acc block, residual]`. -/
def PostOp (C : Ctx) (o : Option (List EIdx × Array EIdx × EIdx)) (w : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧ (o = none → w = 0) ∧
    ∀ fvs acc r, o = some (fvs, acc, r) → ∃ ob oa, w = cellA C ob ∧ H'[ob]? = some (cellA C oa) ∧
      H'[ob + 1]? = some (Enc.idxW r) ∧ BlkAt H' oa (acc.toList.map Enc.idxW) ∧ acc.size < 2 ^ 58

theorem postOp_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostOp C a w s' st → PostOp C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h1, h2⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h1, h2⟩

theorem op_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ opLocals → (ctxEnv C ++ opParams.zip vals).get x = none :=
  Knot.params_none C opLocals opParams vals (by decide) (by decide)

structure OpCodes (C : Ctx) : Prop where
  irr : C.code.lookup ExQ.fIrr = some (ExQ.irrParams.map (fun p => (p, ShapeHOL.one)), ExQ.irrBody C, .one)
  q : ExQ.CodesQ C
  fv : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one)
  app : C.code.lookup ExPre.fAppend = some (ExPre.appParams.map (fun p => (p, ShapeHOL.one)), ExPre.appBody C, .one)
  self : C.code.lookup fOp = some (opParams.map (fun p => (p, ShapeHOL.one)), opBody C, .one)

theorem op_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : OpCodes C) :
    ∀ n (acc : List EIdx) (h : EIdx) (i : Nat) (oa : Nat) (H : List (BitVec 64)) (s : AState), C.H <+: H →
      BlkAt H oa (acc.map Enc.idxW) → acc.length + n < 2 ^ 57 → i + n < 2 ^ 63 →
      SpecR (σ := σ) (Pre (ctxH C H) s (opParams.zip [cellA C oa, BitVec.ofNat 64 n, Enc.idxW h, BitVec.ofNat 64 i]))
        (opBody C) s (openPisRawGo acc.toArray n h i) (PostOp (ctxH C H)) := by
  intro n
  induction n with
  | zero =>
    intro acc h i oa H s hp hba hal hin
    refine specR_prologue (postOp_locals _) (op_none _ _) ?_
    rw [openPisRawGo]
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, opParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hlay := hok.heapLay
    refine specR_allocI (C := ctxH C H) opO (.const 16) 2 (by omega) (by decide) (fun _ => rfl)
      (fun H1 ws hp1 hws hroom => ?_)
    have hp1' : H <+: H1 := hp1
    have hL := hp1'.length_le
    change SpecR (Inv (ctxH C (H1 ++ ws)) s ((opO, cellA C H1.length) :: _) _ _) _ _ _ _
    refine specR_heapStoreI (ctxOK_H hok _) (vv opO) (vv opA) H1.length (by show _ < (H1 ++ ws).length; simp; omega)
      (cellA C oa) (by simp <;> rfl) (by simp +decide [Env.get, opParams, ctxEnv] <;> rfl) ?_
    change SpecR (Inv (ctxH C ((H1 ++ ws).set H1.length (cellA C oa))) _ _ _ _) _ _ _ _
    refine specR_heapStoreI (ctxOK_H hok _) (.op .add [vv opO, .const 8]) (vv opH) (H1.length + 1)
      (by show _ < ((H1 ++ ws).set _ _).length; simp; omega) (Enc.idxW h) (by simp +decide [sev]; exact cellA_add8 C _)
      (by simp +decide [Env.get, opParams, ctxEnv]) ?_
    have g0 : (((H1 ++ ws).set H1.length (cellA C oa)).set (H1.length + 1) (Enc.idxW h))[H1.length]? =
        some (cellA C oa) := by simp [List.getElem?_set, hws]
    have g1 : (((H1 ++ ws).set H1.length (cellA C oa)).set (H1.length + 1) (Enc.idxW h))[H1.length + 1]? =
        some (Enc.idxW h) := by simp [List.getElem?_set, hws]
    have hpre : H <+: ((H1 ++ ws).set H1.length (cellA C oa)).set (H1.length + 1) (Enc.idxW h) :=
      prefix_set_ge (prefix_set_ge (hp1'.trans (List.prefix_append _ _)) _ (by omega) _) _ (by omega) _
    exact specR_returnI _ (cellA C H1.length) (by simp +decide [Env.get] <;> rfl)
      (fun t ht => ⟨_, hpre, sr_of_eq ht.sr rfl rfl rfl rfl, (fun h => by cases h), fun fvs acc' r hr => by
        cases hr; exact ⟨H1.length, oa, rfl, g0, g1, by simpa using blkAt_mono hba hpre, by simp; omega⟩⟩)
  | succ n ih =>
    intro acc h i oa H s hp hba hal hin
    refine specR_prologue (postOp_locals _) (op_none _ _) ?_
    rw [openPisRawGo]
    have hne := ofNat_succ_ne n (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, opParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine Knot.specR_tagIteV opH h 6 (by decide) (by decide) (by simp +decide [Env.get, opParams, ctxEnv]) (fun htg => ?_) (fun htg => ?_)
    swap
    · rw [ite_eq_right (show ¬ (h.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg)]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl,
        fun _ => rfl, fun fvs acc r hr => by cases hr⟩)
    rw [ite_eq_left (show (h.tag == ETag.forallE) = true by simp [htg, ETag.forallE])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv opH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, opParams, ctxEnv]) ?_
    refine specR_viewP (C := ctxH C H) h (by simp) (by simp +decide [Env.get] <;> rfl)
      (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
    refine specR_congr (view_bind_eq h v _ s hv) ?_
    have h6 : v.tagN = 6 := by rw [htn, htg]; rfl
    obtain ⟨dom, b, rfl⟩ : ∃ dom b, v = .forallE dom b := by cases v <;> simp [ENodeView.tagN] at h6 ⊢
    dsimp only
    refine specR_loadI' opDm (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW dom) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW dom) [Enc.idxW b] []) ?_
    refine specR_loadI' opB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW dom) (Enc.idxW b) [] []) ?_
    refine specR_dropM ?_
    obtain ⟨hlo, hlv0⟩ := blkAt_get0 hba
    refine UD.specR_heapLoadI' (C := ctxH C H) opL (vv opA) oa (BitVec.ofNat 64 acc.length)
      (by show H[oa]? = _; rw [List.getElem?_eq_getElem hlo, hlv0]; simp) (by decide) (by simp +decide [Env.get, opParams, ctxEnv] <;> rfl) ?_
    simp only [instantiateListFast, List.size_toArray, bind_assoc]
    refine ILP.callE_spec (C := ctxH C H) opD ExQ.fIrr ExQ.irrParams
      [vv opA, .const 0, vv opL, .const (BitVec.ofNat 64 coreWalkFuel), vv opDm, .const 0] (ExQ.irrBody C)
      [cellA C oa, BitVec.ofNat 64 0, BitVec.ofNat 64 acc.length, BitVec.ofNat 64 coreWalkFuel, Enc.idxW dom,
        BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.irr
      ⟨by simp +decide [Env.get, opParams, ctxEnv] <;> rfl, rfl, by simp, rfl, by simp, rfl, trivial⟩
      (ExQ.irr_spec ra (ctxH C H) (ctxOK_H hok H) (codesQ_H hc.q H) acc.toArray oa
        (show BlkAt H oa (acc.toArray.toList.map Enc.idxW) by simpa using hba) (by simp; omega) s
        coreWalkFuel 0 acc.length 0 dom CV.coreWalkFuel_lt (by decide) (by omega) (by decide)) (fun d s1 => ?_)
    refine ILP.specR_internFVarI (C := ctxH C H) ra (ctxOK_H hok H) hc.fv opV (vv opD) (vv opI) d i
      (by omega) (by decide) (by simp) (by simp +decide [Env.get, opParams, ctxEnv]) (fun fv s2 => ?_)
    refine ExPre.specR_callApp (C := ctxH C H) (ctxOK_H hok H) hc.app opA2 (vv opA) (vv opV) oa
      (acc.map Enc.idxW) (Enc.idxW fv) (by decide) hba (by simp +decide [Env.get, opParams, ctxEnv] <;> rfl) (by simp) (fun H1 o1 hp1 hb1 => ?_)
    have hb1' : BlkAt H1 o1 ((acc ++ [fv]).map Enc.idxW) := by simpa using hb1
    rw [show acc.toArray.push fv = (acc ++ [fv]).toArray by simp]
    refine specR_callNIH (C := ctxH C H1) opR fOp opParams
      [vv opA2, .op .sub [vv opN, .const 1], vv opB, .op .add [vv opI, .const 1]] (opBody C)
      [cellA C o1, BitVec.ofNat 64 n, Enc.idxW b, BitVec.ofNat 64 (i + 1)] (by decide) rfl (by decide) hc.self
      ⟨by simp <;> rfl, by simp +decide [sev, Env.get, opParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, by simp,
        by simp +decide [sev, Env.get, opParams, ctxEnv]; exact word_add1_eq i, trivial⟩
      (PostOp (ctxH C H1))
      (fun r w _ H' => (r = none → w = 0) ∧ ∀ fvs acc r', r = some (fvs, acc, r') → ∃ ob oa, w = cellA C ob ∧
        H'[ob]? = some (cellA C oa) ∧ H'[ob + 1]? = some (Enc.idxW r') ∧ BlkAt H' oa (acc.toList.map Enc.idxW) ∧
        acc.size < 2 ^ 58)
      (fun r w s' st ⟨H', hp', hsr, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu opParams _ rfl hlk)
        (ih (acc ++ [fv]) b (i + 1) o1 H1 s2 (hp.trans hp1) hb1' (by simp; omega) (by omega)))
      (fun r w s3 H2 hp2 ⟨h1, h2⟩ => ?_)
    rcases r with _ | ⟨fvs, acc', e⟩
    · dsimp only
      exact specR_returnI _ w (by simp) (fun t ht => ⟨H2, hp1.trans hp2, sr_of_eq ht.sr rfl rfl rfl rfl,
        fun _ => h1 rfl, fun fvs acc r hr => by cases hr⟩)
    · dsimp only
      exact specR_returnI _ w (by simp) (fun t ht => ⟨H2, hp1.trans hp2, sr_of_eq ht.sr rfl rfl rfl rfl,
        (fun hr => by cases hr), fun fvs2 acc2 r2 hr => by cases hr; exact h2 fvs acc' e rfl⟩)

end

end ConPanqueque.T.WC
