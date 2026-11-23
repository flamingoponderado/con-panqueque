import ConPanqueque.T.Core.DefeqOffset
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `defeqBindersInner`

The innermost level of the binder-telescope congruence: the opened bodies compared, and for two λ-telescopes at
the verified mode their full-grade types (the λ check). The mode is static (the body is chosen by `v`).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def diL := ofString "din_l"
def diB1 := ofString "din_b1"
def diB2 := ofString "din_b2"
def diD1 := ofString "din_d1"
def diQ := ofString "din_q"
def diT1 := ofString "din_t1"
def diT2 := ofString "din_t2"
def diR := ofString "din_r"
def fDi := ofString "defeqBindersInner"
def fDb := ofString "defeqBinders"
def fBPr := ofString "binderPair"
def dbL := ofString "dbn_l"
def dbF := ofString "dbn_f"
def dbV := ofString "dbn_v"
def dbT1 := ofString "dbn_t1"
def dbB1 := ofString "dbn_b1"
def dbT2 := ofString "dbn_t2"
def dbB2 := ofString "dbn_b2"
def dbVl := ofString "dbn_vl"
def dbD2 := ofString "dbn_d2"
def dbD1 := ofString "dbn_d1"
def dbQ := ofString "dbn_q"
def dbFv := ofString "dbn_fv"
def dbV2 := ofString "dbn_v2"
def dbP := ofString "dbn_p"
def dbU1 := ofString "dbn_u1"
def dbC1 := ofString "dbn_c1"
def dbU2 := ofString "dbn_u2"
def dbC2 := ofString "dbn_c2"
def dbD3 := ofString "dbn_d3"
def dbVl2 := ofString "dbn_vl2"
def dbX1 := ofString "dbn_x1"
def dbX2 := ofString "dbn_x2"
def dbR := ofString "dbn_r"

@[simp] theorem db_dbL_ne_dbF : dbL ≠ dbF := by decide
@[simp] theorem db_dbL_ne_dbV : dbL ≠ dbV := by decide
@[simp] theorem db_dbL_ne_dbT1 : dbL ≠ dbT1 := by decide
@[simp] theorem db_dbL_ne_dbB1 : dbL ≠ dbB1 := by decide
@[simp] theorem db_dbL_ne_dbT2 : dbL ≠ dbT2 := by decide
@[simp] theorem db_dbL_ne_dbB2 : dbL ≠ dbB2 := by decide
@[simp] theorem db_dbL_ne_dbVl : dbL ≠ dbVl := by decide
@[simp] theorem db_dbL_ne_dbD2 : dbL ≠ dbD2 := by decide
@[simp] theorem db_dbL_ne_dbD1 : dbL ≠ dbD1 := by decide
@[simp] theorem db_dbL_ne_dbQ : dbL ≠ dbQ := by decide
@[simp] theorem db_dbL_ne_dbFv : dbL ≠ dbFv := by decide
@[simp] theorem db_dbL_ne_dbV2 : dbL ≠ dbV2 := by decide
@[simp] theorem db_dbL_ne_dbP : dbL ≠ dbP := by decide
@[simp] theorem db_dbL_ne_dbU1 : dbL ≠ dbU1 := by decide
@[simp] theorem db_dbL_ne_dbC1 : dbL ≠ dbC1 := by decide
@[simp] theorem db_dbL_ne_dbU2 : dbL ≠ dbU2 := by decide
@[simp] theorem db_dbL_ne_dbC2 : dbL ≠ dbC2 := by decide
@[simp] theorem db_dbL_ne_dbD3 : dbL ≠ dbD3 := by decide
@[simp] theorem db_dbL_ne_dbVl2 : dbL ≠ dbVl2 := by decide
@[simp] theorem db_dbL_ne_dbX1 : dbL ≠ dbX1 := by decide
@[simp] theorem db_dbL_ne_dbX2 : dbL ≠ dbX2 := by decide
@[simp] theorem db_dbL_ne_dbR : dbL ≠ dbR := by decide
@[simp] theorem db_dbL_ne_kFu : dbL ≠ kFu := by decide
@[simp] theorem db_kFu_ne_dbL : kFu ≠ dbL := by decide
@[simp] theorem db_dbL_ne_kD : dbL ≠ kD := by decide
@[simp] theorem db_kD_ne_dbL : kD ≠ dbL := by decide
@[simp] theorem db_dbL_ne_lFl : dbL ≠ lFl := by decide
@[simp] theorem db_lFl_ne_dbL : lFl ≠ dbL := by decide
@[simp] theorem db_dbL_ne_lDh : dbL ≠ lDh := by decide
@[simp] theorem db_lDh_ne_dbL : lDh ≠ dbL := by decide
@[simp] theorem db_dbL_ne_lDt : dbL ≠ lDt := by decide
@[simp] theorem db_lDt_ne_dbL : lDt ≠ dbL := by decide
@[simp] theorem db_dbL_ne_lDg : dbL ≠ lDg := by decide
@[simp] theorem db_lDg_ne_dbL : lDg ≠ dbL := by decide
@[simp] theorem db_dbL_ne_lDi : dbL ≠ lDi := by decide
@[simp] theorem db_lDi_ne_dbL : lDi ≠ dbL := by decide
@[simp] theorem db_dbL_ne_lRp : dbL ≠ lRp := by decide
@[simp] theorem db_lRp_ne_dbL : lRp ≠ dbL := by decide
@[simp] theorem db_dbL_ne_lRn : dbL ≠ lRn := by decide
@[simp] theorem db_lRn_ne_dbL : lRn ≠ dbL := by decide
@[simp] theorem db_dbL_ne_lDir : dbL ≠ lDir := by decide
@[simp] theorem db_lDir_ne_dbL : lDir ≠ dbL := by decide
@[simp] theorem db_dbL_ne_lFle : dbL ≠ lFle := by decide
@[simp] theorem db_lFle_ne_dbL : lFle ≠ dbL := by decide
@[simp] theorem db_dbL_ne_lKb : dbL ≠ lKb := by decide
@[simp] theorem db_lKb_ne_dbL : lKb ≠ dbL := by decide
@[simp] theorem db_dbF_ne_dbL : dbF ≠ dbL := by decide
@[simp] theorem db_dbF_ne_dbV : dbF ≠ dbV := by decide
@[simp] theorem db_dbF_ne_dbT1 : dbF ≠ dbT1 := by decide
@[simp] theorem db_dbF_ne_dbB1 : dbF ≠ dbB1 := by decide
@[simp] theorem db_dbF_ne_dbT2 : dbF ≠ dbT2 := by decide
@[simp] theorem db_dbF_ne_dbB2 : dbF ≠ dbB2 := by decide
@[simp] theorem db_dbF_ne_dbVl : dbF ≠ dbVl := by decide
@[simp] theorem db_dbF_ne_dbD2 : dbF ≠ dbD2 := by decide
@[simp] theorem db_dbF_ne_dbD1 : dbF ≠ dbD1 := by decide
@[simp] theorem db_dbF_ne_dbQ : dbF ≠ dbQ := by decide
@[simp] theorem db_dbF_ne_dbFv : dbF ≠ dbFv := by decide
@[simp] theorem db_dbF_ne_dbV2 : dbF ≠ dbV2 := by decide
@[simp] theorem db_dbF_ne_dbP : dbF ≠ dbP := by decide
@[simp] theorem db_dbF_ne_dbU1 : dbF ≠ dbU1 := by decide
@[simp] theorem db_dbF_ne_dbC1 : dbF ≠ dbC1 := by decide
@[simp] theorem db_dbF_ne_dbU2 : dbF ≠ dbU2 := by decide
@[simp] theorem db_dbF_ne_dbC2 : dbF ≠ dbC2 := by decide
@[simp] theorem db_dbF_ne_dbD3 : dbF ≠ dbD3 := by decide
@[simp] theorem db_dbF_ne_dbVl2 : dbF ≠ dbVl2 := by decide
@[simp] theorem db_dbF_ne_dbX1 : dbF ≠ dbX1 := by decide
@[simp] theorem db_dbF_ne_dbX2 : dbF ≠ dbX2 := by decide
@[simp] theorem db_dbF_ne_dbR : dbF ≠ dbR := by decide
@[simp] theorem db_dbF_ne_kFu : dbF ≠ kFu := by decide
@[simp] theorem db_kFu_ne_dbF : kFu ≠ dbF := by decide
@[simp] theorem db_dbF_ne_kD : dbF ≠ kD := by decide
@[simp] theorem db_kD_ne_dbF : kD ≠ dbF := by decide
@[simp] theorem db_dbF_ne_lFl : dbF ≠ lFl := by decide
@[simp] theorem db_lFl_ne_dbF : lFl ≠ dbF := by decide
@[simp] theorem db_dbF_ne_lDh : dbF ≠ lDh := by decide
@[simp] theorem db_lDh_ne_dbF : lDh ≠ dbF := by decide
@[simp] theorem db_dbF_ne_lDt : dbF ≠ lDt := by decide
@[simp] theorem db_lDt_ne_dbF : lDt ≠ dbF := by decide
@[simp] theorem db_dbF_ne_lDg : dbF ≠ lDg := by decide
@[simp] theorem db_lDg_ne_dbF : lDg ≠ dbF := by decide
@[simp] theorem db_dbF_ne_lDi : dbF ≠ lDi := by decide
@[simp] theorem db_lDi_ne_dbF : lDi ≠ dbF := by decide
@[simp] theorem db_dbF_ne_lRp : dbF ≠ lRp := by decide
@[simp] theorem db_lRp_ne_dbF : lRp ≠ dbF := by decide
@[simp] theorem db_dbF_ne_lRn : dbF ≠ lRn := by decide
@[simp] theorem db_lRn_ne_dbF : lRn ≠ dbF := by decide
@[simp] theorem db_dbF_ne_lDir : dbF ≠ lDir := by decide
@[simp] theorem db_lDir_ne_dbF : lDir ≠ dbF := by decide
@[simp] theorem db_dbF_ne_lFle : dbF ≠ lFle := by decide
@[simp] theorem db_lFle_ne_dbF : lFle ≠ dbF := by decide
@[simp] theorem db_dbF_ne_lKb : dbF ≠ lKb := by decide
@[simp] theorem db_lKb_ne_dbF : lKb ≠ dbF := by decide
@[simp] theorem db_dbV_ne_dbL : dbV ≠ dbL := by decide
@[simp] theorem db_dbV_ne_dbF : dbV ≠ dbF := by decide
@[simp] theorem db_dbV_ne_dbT1 : dbV ≠ dbT1 := by decide
@[simp] theorem db_dbV_ne_dbB1 : dbV ≠ dbB1 := by decide
@[simp] theorem db_dbV_ne_dbT2 : dbV ≠ dbT2 := by decide
@[simp] theorem db_dbV_ne_dbB2 : dbV ≠ dbB2 := by decide
@[simp] theorem db_dbV_ne_dbVl : dbV ≠ dbVl := by decide
@[simp] theorem db_dbV_ne_dbD2 : dbV ≠ dbD2 := by decide
@[simp] theorem db_dbV_ne_dbD1 : dbV ≠ dbD1 := by decide
@[simp] theorem db_dbV_ne_dbQ : dbV ≠ dbQ := by decide
@[simp] theorem db_dbV_ne_dbFv : dbV ≠ dbFv := by decide
@[simp] theorem db_dbV_ne_dbV2 : dbV ≠ dbV2 := by decide
@[simp] theorem db_dbV_ne_dbP : dbV ≠ dbP := by decide
@[simp] theorem db_dbV_ne_dbU1 : dbV ≠ dbU1 := by decide
@[simp] theorem db_dbV_ne_dbC1 : dbV ≠ dbC1 := by decide
@[simp] theorem db_dbV_ne_dbU2 : dbV ≠ dbU2 := by decide
@[simp] theorem db_dbV_ne_dbC2 : dbV ≠ dbC2 := by decide
@[simp] theorem db_dbV_ne_dbD3 : dbV ≠ dbD3 := by decide
@[simp] theorem db_dbV_ne_dbVl2 : dbV ≠ dbVl2 := by decide
@[simp] theorem db_dbV_ne_dbX1 : dbV ≠ dbX1 := by decide
@[simp] theorem db_dbV_ne_dbX2 : dbV ≠ dbX2 := by decide
@[simp] theorem db_dbV_ne_dbR : dbV ≠ dbR := by decide
@[simp] theorem db_dbV_ne_kFu : dbV ≠ kFu := by decide
@[simp] theorem db_kFu_ne_dbV : kFu ≠ dbV := by decide
@[simp] theorem db_dbV_ne_kD : dbV ≠ kD := by decide
@[simp] theorem db_kD_ne_dbV : kD ≠ dbV := by decide
@[simp] theorem db_dbV_ne_lFl : dbV ≠ lFl := by decide
@[simp] theorem db_lFl_ne_dbV : lFl ≠ dbV := by decide
@[simp] theorem db_dbV_ne_lDh : dbV ≠ lDh := by decide
@[simp] theorem db_lDh_ne_dbV : lDh ≠ dbV := by decide
@[simp] theorem db_dbV_ne_lDt : dbV ≠ lDt := by decide
@[simp] theorem db_lDt_ne_dbV : lDt ≠ dbV := by decide
@[simp] theorem db_dbV_ne_lDg : dbV ≠ lDg := by decide
@[simp] theorem db_lDg_ne_dbV : lDg ≠ dbV := by decide
@[simp] theorem db_dbV_ne_lDi : dbV ≠ lDi := by decide
@[simp] theorem db_lDi_ne_dbV : lDi ≠ dbV := by decide
@[simp] theorem db_dbV_ne_lRp : dbV ≠ lRp := by decide
@[simp] theorem db_lRp_ne_dbV : lRp ≠ dbV := by decide
@[simp] theorem db_dbV_ne_lRn : dbV ≠ lRn := by decide
@[simp] theorem db_lRn_ne_dbV : lRn ≠ dbV := by decide
@[simp] theorem db_dbV_ne_lDir : dbV ≠ lDir := by decide
@[simp] theorem db_lDir_ne_dbV : lDir ≠ dbV := by decide
@[simp] theorem db_dbV_ne_lFle : dbV ≠ lFle := by decide
@[simp] theorem db_lFle_ne_dbV : lFle ≠ dbV := by decide
@[simp] theorem db_dbV_ne_lKb : dbV ≠ lKb := by decide
@[simp] theorem db_lKb_ne_dbV : lKb ≠ dbV := by decide
@[simp] theorem db_dbT1_ne_dbL : dbT1 ≠ dbL := by decide
@[simp] theorem db_dbT1_ne_dbF : dbT1 ≠ dbF := by decide
@[simp] theorem db_dbT1_ne_dbV : dbT1 ≠ dbV := by decide
@[simp] theorem db_dbT1_ne_dbB1 : dbT1 ≠ dbB1 := by decide
@[simp] theorem db_dbT1_ne_dbT2 : dbT1 ≠ dbT2 := by decide
@[simp] theorem db_dbT1_ne_dbB2 : dbT1 ≠ dbB2 := by decide
@[simp] theorem db_dbT1_ne_dbVl : dbT1 ≠ dbVl := by decide
@[simp] theorem db_dbT1_ne_dbD2 : dbT1 ≠ dbD2 := by decide
@[simp] theorem db_dbT1_ne_dbD1 : dbT1 ≠ dbD1 := by decide
@[simp] theorem db_dbT1_ne_dbQ : dbT1 ≠ dbQ := by decide
@[simp] theorem db_dbT1_ne_dbFv : dbT1 ≠ dbFv := by decide
@[simp] theorem db_dbT1_ne_dbV2 : dbT1 ≠ dbV2 := by decide
@[simp] theorem db_dbT1_ne_dbP : dbT1 ≠ dbP := by decide
@[simp] theorem db_dbT1_ne_dbU1 : dbT1 ≠ dbU1 := by decide
@[simp] theorem db_dbT1_ne_dbC1 : dbT1 ≠ dbC1 := by decide
@[simp] theorem db_dbT1_ne_dbU2 : dbT1 ≠ dbU2 := by decide
@[simp] theorem db_dbT1_ne_dbC2 : dbT1 ≠ dbC2 := by decide
@[simp] theorem db_dbT1_ne_dbD3 : dbT1 ≠ dbD3 := by decide
@[simp] theorem db_dbT1_ne_dbVl2 : dbT1 ≠ dbVl2 := by decide
@[simp] theorem db_dbT1_ne_dbX1 : dbT1 ≠ dbX1 := by decide
@[simp] theorem db_dbT1_ne_dbX2 : dbT1 ≠ dbX2 := by decide
@[simp] theorem db_dbT1_ne_dbR : dbT1 ≠ dbR := by decide
@[simp] theorem db_dbT1_ne_kFu : dbT1 ≠ kFu := by decide
@[simp] theorem db_kFu_ne_dbT1 : kFu ≠ dbT1 := by decide
@[simp] theorem db_dbT1_ne_kD : dbT1 ≠ kD := by decide
@[simp] theorem db_kD_ne_dbT1 : kD ≠ dbT1 := by decide
@[simp] theorem db_dbT1_ne_lFl : dbT1 ≠ lFl := by decide
@[simp] theorem db_lFl_ne_dbT1 : lFl ≠ dbT1 := by decide
@[simp] theorem db_dbT1_ne_lDh : dbT1 ≠ lDh := by decide
@[simp] theorem db_lDh_ne_dbT1 : lDh ≠ dbT1 := by decide
@[simp] theorem db_dbT1_ne_lDt : dbT1 ≠ lDt := by decide
@[simp] theorem db_lDt_ne_dbT1 : lDt ≠ dbT1 := by decide
@[simp] theorem db_dbT1_ne_lDg : dbT1 ≠ lDg := by decide
@[simp] theorem db_lDg_ne_dbT1 : lDg ≠ dbT1 := by decide
@[simp] theorem db_dbT1_ne_lDi : dbT1 ≠ lDi := by decide
@[simp] theorem db_lDi_ne_dbT1 : lDi ≠ dbT1 := by decide
@[simp] theorem db_dbT1_ne_lRp : dbT1 ≠ lRp := by decide
@[simp] theorem db_lRp_ne_dbT1 : lRp ≠ dbT1 := by decide
@[simp] theorem db_dbT1_ne_lRn : dbT1 ≠ lRn := by decide
@[simp] theorem db_lRn_ne_dbT1 : lRn ≠ dbT1 := by decide
@[simp] theorem db_dbT1_ne_lDir : dbT1 ≠ lDir := by decide
@[simp] theorem db_lDir_ne_dbT1 : lDir ≠ dbT1 := by decide
@[simp] theorem db_dbT1_ne_lFle : dbT1 ≠ lFle := by decide
@[simp] theorem db_lFle_ne_dbT1 : lFle ≠ dbT1 := by decide
@[simp] theorem db_dbT1_ne_lKb : dbT1 ≠ lKb := by decide
@[simp] theorem db_lKb_ne_dbT1 : lKb ≠ dbT1 := by decide
@[simp] theorem db_dbB1_ne_dbL : dbB1 ≠ dbL := by decide
@[simp] theorem db_dbB1_ne_dbF : dbB1 ≠ dbF := by decide
@[simp] theorem db_dbB1_ne_dbV : dbB1 ≠ dbV := by decide
@[simp] theorem db_dbB1_ne_dbT1 : dbB1 ≠ dbT1 := by decide
@[simp] theorem db_dbB1_ne_dbT2 : dbB1 ≠ dbT2 := by decide
@[simp] theorem db_dbB1_ne_dbB2 : dbB1 ≠ dbB2 := by decide
@[simp] theorem db_dbB1_ne_dbVl : dbB1 ≠ dbVl := by decide
@[simp] theorem db_dbB1_ne_dbD2 : dbB1 ≠ dbD2 := by decide
@[simp] theorem db_dbB1_ne_dbD1 : dbB1 ≠ dbD1 := by decide
@[simp] theorem db_dbB1_ne_dbQ : dbB1 ≠ dbQ := by decide
@[simp] theorem db_dbB1_ne_dbFv : dbB1 ≠ dbFv := by decide
@[simp] theorem db_dbB1_ne_dbV2 : dbB1 ≠ dbV2 := by decide
@[simp] theorem db_dbB1_ne_dbP : dbB1 ≠ dbP := by decide
@[simp] theorem db_dbB1_ne_dbU1 : dbB1 ≠ dbU1 := by decide
@[simp] theorem db_dbB1_ne_dbC1 : dbB1 ≠ dbC1 := by decide
@[simp] theorem db_dbB1_ne_dbU2 : dbB1 ≠ dbU2 := by decide
@[simp] theorem db_dbB1_ne_dbC2 : dbB1 ≠ dbC2 := by decide
@[simp] theorem db_dbB1_ne_dbD3 : dbB1 ≠ dbD3 := by decide
@[simp] theorem db_dbB1_ne_dbVl2 : dbB1 ≠ dbVl2 := by decide
@[simp] theorem db_dbB1_ne_dbX1 : dbB1 ≠ dbX1 := by decide
@[simp] theorem db_dbB1_ne_dbX2 : dbB1 ≠ dbX2 := by decide
@[simp] theorem db_dbB1_ne_dbR : dbB1 ≠ dbR := by decide
@[simp] theorem db_dbB1_ne_kFu : dbB1 ≠ kFu := by decide
@[simp] theorem db_kFu_ne_dbB1 : kFu ≠ dbB1 := by decide
@[simp] theorem db_dbB1_ne_kD : dbB1 ≠ kD := by decide
@[simp] theorem db_kD_ne_dbB1 : kD ≠ dbB1 := by decide
@[simp] theorem db_dbB1_ne_lFl : dbB1 ≠ lFl := by decide
@[simp] theorem db_lFl_ne_dbB1 : lFl ≠ dbB1 := by decide
@[simp] theorem db_dbB1_ne_lDh : dbB1 ≠ lDh := by decide
@[simp] theorem db_lDh_ne_dbB1 : lDh ≠ dbB1 := by decide
@[simp] theorem db_dbB1_ne_lDt : dbB1 ≠ lDt := by decide
@[simp] theorem db_lDt_ne_dbB1 : lDt ≠ dbB1 := by decide
@[simp] theorem db_dbB1_ne_lDg : dbB1 ≠ lDg := by decide
@[simp] theorem db_lDg_ne_dbB1 : lDg ≠ dbB1 := by decide
@[simp] theorem db_dbB1_ne_lDi : dbB1 ≠ lDi := by decide
@[simp] theorem db_lDi_ne_dbB1 : lDi ≠ dbB1 := by decide
@[simp] theorem db_dbB1_ne_lRp : dbB1 ≠ lRp := by decide
@[simp] theorem db_lRp_ne_dbB1 : lRp ≠ dbB1 := by decide
@[simp] theorem db_dbB1_ne_lRn : dbB1 ≠ lRn := by decide
@[simp] theorem db_lRn_ne_dbB1 : lRn ≠ dbB1 := by decide
@[simp] theorem db_dbB1_ne_lDir : dbB1 ≠ lDir := by decide
@[simp] theorem db_lDir_ne_dbB1 : lDir ≠ dbB1 := by decide
@[simp] theorem db_dbB1_ne_lFle : dbB1 ≠ lFle := by decide
@[simp] theorem db_lFle_ne_dbB1 : lFle ≠ dbB1 := by decide
@[simp] theorem db_dbB1_ne_lKb : dbB1 ≠ lKb := by decide
@[simp] theorem db_lKb_ne_dbB1 : lKb ≠ dbB1 := by decide
@[simp] theorem db_dbT2_ne_dbL : dbT2 ≠ dbL := by decide
@[simp] theorem db_dbT2_ne_dbF : dbT2 ≠ dbF := by decide
@[simp] theorem db_dbT2_ne_dbV : dbT2 ≠ dbV := by decide
@[simp] theorem db_dbT2_ne_dbT1 : dbT2 ≠ dbT1 := by decide
@[simp] theorem db_dbT2_ne_dbB1 : dbT2 ≠ dbB1 := by decide
@[simp] theorem db_dbT2_ne_dbB2 : dbT2 ≠ dbB2 := by decide
@[simp] theorem db_dbT2_ne_dbVl : dbT2 ≠ dbVl := by decide
@[simp] theorem db_dbT2_ne_dbD2 : dbT2 ≠ dbD2 := by decide
@[simp] theorem db_dbT2_ne_dbD1 : dbT2 ≠ dbD1 := by decide
@[simp] theorem db_dbT2_ne_dbQ : dbT2 ≠ dbQ := by decide
@[simp] theorem db_dbT2_ne_dbFv : dbT2 ≠ dbFv := by decide
@[simp] theorem db_dbT2_ne_dbV2 : dbT2 ≠ dbV2 := by decide
@[simp] theorem db_dbT2_ne_dbP : dbT2 ≠ dbP := by decide
@[simp] theorem db_dbT2_ne_dbU1 : dbT2 ≠ dbU1 := by decide
@[simp] theorem db_dbT2_ne_dbC1 : dbT2 ≠ dbC1 := by decide
@[simp] theorem db_dbT2_ne_dbU2 : dbT2 ≠ dbU2 := by decide
@[simp] theorem db_dbT2_ne_dbC2 : dbT2 ≠ dbC2 := by decide
@[simp] theorem db_dbT2_ne_dbD3 : dbT2 ≠ dbD3 := by decide
@[simp] theorem db_dbT2_ne_dbVl2 : dbT2 ≠ dbVl2 := by decide
@[simp] theorem db_dbT2_ne_dbX1 : dbT2 ≠ dbX1 := by decide
@[simp] theorem db_dbT2_ne_dbX2 : dbT2 ≠ dbX2 := by decide
@[simp] theorem db_dbT2_ne_dbR : dbT2 ≠ dbR := by decide
@[simp] theorem db_dbT2_ne_kFu : dbT2 ≠ kFu := by decide
@[simp] theorem db_kFu_ne_dbT2 : kFu ≠ dbT2 := by decide
@[simp] theorem db_dbT2_ne_kD : dbT2 ≠ kD := by decide
@[simp] theorem db_kD_ne_dbT2 : kD ≠ dbT2 := by decide
@[simp] theorem db_dbT2_ne_lFl : dbT2 ≠ lFl := by decide
@[simp] theorem db_lFl_ne_dbT2 : lFl ≠ dbT2 := by decide
@[simp] theorem db_dbT2_ne_lDh : dbT2 ≠ lDh := by decide
@[simp] theorem db_lDh_ne_dbT2 : lDh ≠ dbT2 := by decide
@[simp] theorem db_dbT2_ne_lDt : dbT2 ≠ lDt := by decide
@[simp] theorem db_lDt_ne_dbT2 : lDt ≠ dbT2 := by decide
@[simp] theorem db_dbT2_ne_lDg : dbT2 ≠ lDg := by decide
@[simp] theorem db_lDg_ne_dbT2 : lDg ≠ dbT2 := by decide
@[simp] theorem db_dbT2_ne_lDi : dbT2 ≠ lDi := by decide
@[simp] theorem db_lDi_ne_dbT2 : lDi ≠ dbT2 := by decide
@[simp] theorem db_dbT2_ne_lRp : dbT2 ≠ lRp := by decide
@[simp] theorem db_lRp_ne_dbT2 : lRp ≠ dbT2 := by decide
@[simp] theorem db_dbT2_ne_lRn : dbT2 ≠ lRn := by decide
@[simp] theorem db_lRn_ne_dbT2 : lRn ≠ dbT2 := by decide
@[simp] theorem db_dbT2_ne_lDir : dbT2 ≠ lDir := by decide
@[simp] theorem db_lDir_ne_dbT2 : lDir ≠ dbT2 := by decide
@[simp] theorem db_dbT2_ne_lFle : dbT2 ≠ lFle := by decide
@[simp] theorem db_lFle_ne_dbT2 : lFle ≠ dbT2 := by decide
@[simp] theorem db_dbT2_ne_lKb : dbT2 ≠ lKb := by decide
@[simp] theorem db_lKb_ne_dbT2 : lKb ≠ dbT2 := by decide
@[simp] theorem db_dbB2_ne_dbL : dbB2 ≠ dbL := by decide
@[simp] theorem db_dbB2_ne_dbF : dbB2 ≠ dbF := by decide
@[simp] theorem db_dbB2_ne_dbV : dbB2 ≠ dbV := by decide
@[simp] theorem db_dbB2_ne_dbT1 : dbB2 ≠ dbT1 := by decide
@[simp] theorem db_dbB2_ne_dbB1 : dbB2 ≠ dbB1 := by decide
@[simp] theorem db_dbB2_ne_dbT2 : dbB2 ≠ dbT2 := by decide
@[simp] theorem db_dbB2_ne_dbVl : dbB2 ≠ dbVl := by decide
@[simp] theorem db_dbB2_ne_dbD2 : dbB2 ≠ dbD2 := by decide
@[simp] theorem db_dbB2_ne_dbD1 : dbB2 ≠ dbD1 := by decide
@[simp] theorem db_dbB2_ne_dbQ : dbB2 ≠ dbQ := by decide
@[simp] theorem db_dbB2_ne_dbFv : dbB2 ≠ dbFv := by decide
@[simp] theorem db_dbB2_ne_dbV2 : dbB2 ≠ dbV2 := by decide
@[simp] theorem db_dbB2_ne_dbP : dbB2 ≠ dbP := by decide
@[simp] theorem db_dbB2_ne_dbU1 : dbB2 ≠ dbU1 := by decide
@[simp] theorem db_dbB2_ne_dbC1 : dbB2 ≠ dbC1 := by decide
@[simp] theorem db_dbB2_ne_dbU2 : dbB2 ≠ dbU2 := by decide
@[simp] theorem db_dbB2_ne_dbC2 : dbB2 ≠ dbC2 := by decide
@[simp] theorem db_dbB2_ne_dbD3 : dbB2 ≠ dbD3 := by decide
@[simp] theorem db_dbB2_ne_dbVl2 : dbB2 ≠ dbVl2 := by decide
@[simp] theorem db_dbB2_ne_dbX1 : dbB2 ≠ dbX1 := by decide
@[simp] theorem db_dbB2_ne_dbX2 : dbB2 ≠ dbX2 := by decide
@[simp] theorem db_dbB2_ne_dbR : dbB2 ≠ dbR := by decide
@[simp] theorem db_dbB2_ne_kFu : dbB2 ≠ kFu := by decide
@[simp] theorem db_kFu_ne_dbB2 : kFu ≠ dbB2 := by decide
@[simp] theorem db_dbB2_ne_kD : dbB2 ≠ kD := by decide
@[simp] theorem db_kD_ne_dbB2 : kD ≠ dbB2 := by decide
@[simp] theorem db_dbB2_ne_lFl : dbB2 ≠ lFl := by decide
@[simp] theorem db_lFl_ne_dbB2 : lFl ≠ dbB2 := by decide
@[simp] theorem db_dbB2_ne_lDh : dbB2 ≠ lDh := by decide
@[simp] theorem db_lDh_ne_dbB2 : lDh ≠ dbB2 := by decide
@[simp] theorem db_dbB2_ne_lDt : dbB2 ≠ lDt := by decide
@[simp] theorem db_lDt_ne_dbB2 : lDt ≠ dbB2 := by decide
@[simp] theorem db_dbB2_ne_lDg : dbB2 ≠ lDg := by decide
@[simp] theorem db_lDg_ne_dbB2 : lDg ≠ dbB2 := by decide
@[simp] theorem db_dbB2_ne_lDi : dbB2 ≠ lDi := by decide
@[simp] theorem db_lDi_ne_dbB2 : lDi ≠ dbB2 := by decide
@[simp] theorem db_dbB2_ne_lRp : dbB2 ≠ lRp := by decide
@[simp] theorem db_lRp_ne_dbB2 : lRp ≠ dbB2 := by decide
@[simp] theorem db_dbB2_ne_lRn : dbB2 ≠ lRn := by decide
@[simp] theorem db_lRn_ne_dbB2 : lRn ≠ dbB2 := by decide
@[simp] theorem db_dbB2_ne_lDir : dbB2 ≠ lDir := by decide
@[simp] theorem db_lDir_ne_dbB2 : lDir ≠ dbB2 := by decide
@[simp] theorem db_dbB2_ne_lFle : dbB2 ≠ lFle := by decide
@[simp] theorem db_lFle_ne_dbB2 : lFle ≠ dbB2 := by decide
@[simp] theorem db_dbB2_ne_lKb : dbB2 ≠ lKb := by decide
@[simp] theorem db_lKb_ne_dbB2 : lKb ≠ dbB2 := by decide
@[simp] theorem db_dbVl_ne_dbL : dbVl ≠ dbL := by decide
@[simp] theorem db_dbVl_ne_dbF : dbVl ≠ dbF := by decide
@[simp] theorem db_dbVl_ne_dbV : dbVl ≠ dbV := by decide
@[simp] theorem db_dbVl_ne_dbT1 : dbVl ≠ dbT1 := by decide
@[simp] theorem db_dbVl_ne_dbB1 : dbVl ≠ dbB1 := by decide
@[simp] theorem db_dbVl_ne_dbT2 : dbVl ≠ dbT2 := by decide
@[simp] theorem db_dbVl_ne_dbB2 : dbVl ≠ dbB2 := by decide
@[simp] theorem db_dbVl_ne_dbD2 : dbVl ≠ dbD2 := by decide
@[simp] theorem db_dbVl_ne_dbD1 : dbVl ≠ dbD1 := by decide
@[simp] theorem db_dbVl_ne_dbQ : dbVl ≠ dbQ := by decide
@[simp] theorem db_dbVl_ne_dbFv : dbVl ≠ dbFv := by decide
@[simp] theorem db_dbVl_ne_dbV2 : dbVl ≠ dbV2 := by decide
@[simp] theorem db_dbVl_ne_dbP : dbVl ≠ dbP := by decide
@[simp] theorem db_dbVl_ne_dbU1 : dbVl ≠ dbU1 := by decide
@[simp] theorem db_dbVl_ne_dbC1 : dbVl ≠ dbC1 := by decide
@[simp] theorem db_dbVl_ne_dbU2 : dbVl ≠ dbU2 := by decide
@[simp] theorem db_dbVl_ne_dbC2 : dbVl ≠ dbC2 := by decide
@[simp] theorem db_dbVl_ne_dbD3 : dbVl ≠ dbD3 := by decide
@[simp] theorem db_dbVl_ne_dbVl2 : dbVl ≠ dbVl2 := by decide
@[simp] theorem db_dbVl_ne_dbX1 : dbVl ≠ dbX1 := by decide
@[simp] theorem db_dbVl_ne_dbX2 : dbVl ≠ dbX2 := by decide
@[simp] theorem db_dbVl_ne_dbR : dbVl ≠ dbR := by decide
@[simp] theorem db_dbVl_ne_kFu : dbVl ≠ kFu := by decide
@[simp] theorem db_kFu_ne_dbVl : kFu ≠ dbVl := by decide
@[simp] theorem db_dbVl_ne_kD : dbVl ≠ kD := by decide
@[simp] theorem db_kD_ne_dbVl : kD ≠ dbVl := by decide
@[simp] theorem db_dbVl_ne_lFl : dbVl ≠ lFl := by decide
@[simp] theorem db_lFl_ne_dbVl : lFl ≠ dbVl := by decide
@[simp] theorem db_dbVl_ne_lDh : dbVl ≠ lDh := by decide
@[simp] theorem db_lDh_ne_dbVl : lDh ≠ dbVl := by decide
@[simp] theorem db_dbVl_ne_lDt : dbVl ≠ lDt := by decide
@[simp] theorem db_lDt_ne_dbVl : lDt ≠ dbVl := by decide
@[simp] theorem db_dbVl_ne_lDg : dbVl ≠ lDg := by decide
@[simp] theorem db_lDg_ne_dbVl : lDg ≠ dbVl := by decide
@[simp] theorem db_dbVl_ne_lDi : dbVl ≠ lDi := by decide
@[simp] theorem db_lDi_ne_dbVl : lDi ≠ dbVl := by decide
@[simp] theorem db_dbVl_ne_lRp : dbVl ≠ lRp := by decide
@[simp] theorem db_lRp_ne_dbVl : lRp ≠ dbVl := by decide
@[simp] theorem db_dbVl_ne_lRn : dbVl ≠ lRn := by decide
@[simp] theorem db_lRn_ne_dbVl : lRn ≠ dbVl := by decide
@[simp] theorem db_dbVl_ne_lDir : dbVl ≠ lDir := by decide
@[simp] theorem db_lDir_ne_dbVl : lDir ≠ dbVl := by decide
@[simp] theorem db_dbVl_ne_lFle : dbVl ≠ lFle := by decide
@[simp] theorem db_lFle_ne_dbVl : lFle ≠ dbVl := by decide
@[simp] theorem db_dbVl_ne_lKb : dbVl ≠ lKb := by decide
@[simp] theorem db_lKb_ne_dbVl : lKb ≠ dbVl := by decide
@[simp] theorem db_dbD2_ne_dbL : dbD2 ≠ dbL := by decide
@[simp] theorem db_dbD2_ne_dbF : dbD2 ≠ dbF := by decide
@[simp] theorem db_dbD2_ne_dbV : dbD2 ≠ dbV := by decide
@[simp] theorem db_dbD2_ne_dbT1 : dbD2 ≠ dbT1 := by decide
@[simp] theorem db_dbD2_ne_dbB1 : dbD2 ≠ dbB1 := by decide
@[simp] theorem db_dbD2_ne_dbT2 : dbD2 ≠ dbT2 := by decide
@[simp] theorem db_dbD2_ne_dbB2 : dbD2 ≠ dbB2 := by decide
@[simp] theorem db_dbD2_ne_dbVl : dbD2 ≠ dbVl := by decide
@[simp] theorem db_dbD2_ne_dbD1 : dbD2 ≠ dbD1 := by decide
@[simp] theorem db_dbD2_ne_dbQ : dbD2 ≠ dbQ := by decide
@[simp] theorem db_dbD2_ne_dbFv : dbD2 ≠ dbFv := by decide
@[simp] theorem db_dbD2_ne_dbV2 : dbD2 ≠ dbV2 := by decide
@[simp] theorem db_dbD2_ne_dbP : dbD2 ≠ dbP := by decide
@[simp] theorem db_dbD2_ne_dbU1 : dbD2 ≠ dbU1 := by decide
@[simp] theorem db_dbD2_ne_dbC1 : dbD2 ≠ dbC1 := by decide
@[simp] theorem db_dbD2_ne_dbU2 : dbD2 ≠ dbU2 := by decide
@[simp] theorem db_dbD2_ne_dbC2 : dbD2 ≠ dbC2 := by decide
@[simp] theorem db_dbD2_ne_dbD3 : dbD2 ≠ dbD3 := by decide
@[simp] theorem db_dbD2_ne_dbVl2 : dbD2 ≠ dbVl2 := by decide
@[simp] theorem db_dbD2_ne_dbX1 : dbD2 ≠ dbX1 := by decide
@[simp] theorem db_dbD2_ne_dbX2 : dbD2 ≠ dbX2 := by decide
@[simp] theorem db_dbD2_ne_dbR : dbD2 ≠ dbR := by decide
@[simp] theorem db_dbD2_ne_kFu : dbD2 ≠ kFu := by decide
@[simp] theorem db_kFu_ne_dbD2 : kFu ≠ dbD2 := by decide
@[simp] theorem db_dbD2_ne_kD : dbD2 ≠ kD := by decide
@[simp] theorem db_kD_ne_dbD2 : kD ≠ dbD2 := by decide
@[simp] theorem db_dbD2_ne_lFl : dbD2 ≠ lFl := by decide
@[simp] theorem db_lFl_ne_dbD2 : lFl ≠ dbD2 := by decide
@[simp] theorem db_dbD2_ne_lDh : dbD2 ≠ lDh := by decide
@[simp] theorem db_lDh_ne_dbD2 : lDh ≠ dbD2 := by decide
@[simp] theorem db_dbD2_ne_lDt : dbD2 ≠ lDt := by decide
@[simp] theorem db_lDt_ne_dbD2 : lDt ≠ dbD2 := by decide
@[simp] theorem db_dbD2_ne_lDg : dbD2 ≠ lDg := by decide
@[simp] theorem db_lDg_ne_dbD2 : lDg ≠ dbD2 := by decide
@[simp] theorem db_dbD2_ne_lDi : dbD2 ≠ lDi := by decide
@[simp] theorem db_lDi_ne_dbD2 : lDi ≠ dbD2 := by decide
@[simp] theorem db_dbD2_ne_lRp : dbD2 ≠ lRp := by decide
@[simp] theorem db_lRp_ne_dbD2 : lRp ≠ dbD2 := by decide
@[simp] theorem db_dbD2_ne_lRn : dbD2 ≠ lRn := by decide
@[simp] theorem db_lRn_ne_dbD2 : lRn ≠ dbD2 := by decide
@[simp] theorem db_dbD2_ne_lDir : dbD2 ≠ lDir := by decide
@[simp] theorem db_lDir_ne_dbD2 : lDir ≠ dbD2 := by decide
@[simp] theorem db_dbD2_ne_lFle : dbD2 ≠ lFle := by decide
@[simp] theorem db_lFle_ne_dbD2 : lFle ≠ dbD2 := by decide
@[simp] theorem db_dbD2_ne_lKb : dbD2 ≠ lKb := by decide
@[simp] theorem db_lKb_ne_dbD2 : lKb ≠ dbD2 := by decide
@[simp] theorem db_dbD1_ne_dbL : dbD1 ≠ dbL := by decide
@[simp] theorem db_dbD1_ne_dbF : dbD1 ≠ dbF := by decide
@[simp] theorem db_dbD1_ne_dbV : dbD1 ≠ dbV := by decide
@[simp] theorem db_dbD1_ne_dbT1 : dbD1 ≠ dbT1 := by decide
@[simp] theorem db_dbD1_ne_dbB1 : dbD1 ≠ dbB1 := by decide
@[simp] theorem db_dbD1_ne_dbT2 : dbD1 ≠ dbT2 := by decide
@[simp] theorem db_dbD1_ne_dbB2 : dbD1 ≠ dbB2 := by decide
@[simp] theorem db_dbD1_ne_dbVl : dbD1 ≠ dbVl := by decide
@[simp] theorem db_dbD1_ne_dbD2 : dbD1 ≠ dbD2 := by decide
@[simp] theorem db_dbD1_ne_dbQ : dbD1 ≠ dbQ := by decide
@[simp] theorem db_dbD1_ne_dbFv : dbD1 ≠ dbFv := by decide
@[simp] theorem db_dbD1_ne_dbV2 : dbD1 ≠ dbV2 := by decide
@[simp] theorem db_dbD1_ne_dbP : dbD1 ≠ dbP := by decide
@[simp] theorem db_dbD1_ne_dbU1 : dbD1 ≠ dbU1 := by decide
@[simp] theorem db_dbD1_ne_dbC1 : dbD1 ≠ dbC1 := by decide
@[simp] theorem db_dbD1_ne_dbU2 : dbD1 ≠ dbU2 := by decide
@[simp] theorem db_dbD1_ne_dbC2 : dbD1 ≠ dbC2 := by decide
@[simp] theorem db_dbD1_ne_dbD3 : dbD1 ≠ dbD3 := by decide
@[simp] theorem db_dbD1_ne_dbVl2 : dbD1 ≠ dbVl2 := by decide
@[simp] theorem db_dbD1_ne_dbX1 : dbD1 ≠ dbX1 := by decide
@[simp] theorem db_dbD1_ne_dbX2 : dbD1 ≠ dbX2 := by decide
@[simp] theorem db_dbD1_ne_dbR : dbD1 ≠ dbR := by decide
@[simp] theorem db_dbD1_ne_kFu : dbD1 ≠ kFu := by decide
@[simp] theorem db_kFu_ne_dbD1 : kFu ≠ dbD1 := by decide
@[simp] theorem db_dbD1_ne_kD : dbD1 ≠ kD := by decide
@[simp] theorem db_kD_ne_dbD1 : kD ≠ dbD1 := by decide
@[simp] theorem db_dbD1_ne_lFl : dbD1 ≠ lFl := by decide
@[simp] theorem db_lFl_ne_dbD1 : lFl ≠ dbD1 := by decide
@[simp] theorem db_dbD1_ne_lDh : dbD1 ≠ lDh := by decide
@[simp] theorem db_lDh_ne_dbD1 : lDh ≠ dbD1 := by decide
@[simp] theorem db_dbD1_ne_lDt : dbD1 ≠ lDt := by decide
@[simp] theorem db_lDt_ne_dbD1 : lDt ≠ dbD1 := by decide
@[simp] theorem db_dbD1_ne_lDg : dbD1 ≠ lDg := by decide
@[simp] theorem db_lDg_ne_dbD1 : lDg ≠ dbD1 := by decide
@[simp] theorem db_dbD1_ne_lDi : dbD1 ≠ lDi := by decide
@[simp] theorem db_lDi_ne_dbD1 : lDi ≠ dbD1 := by decide
@[simp] theorem db_dbD1_ne_lRp : dbD1 ≠ lRp := by decide
@[simp] theorem db_lRp_ne_dbD1 : lRp ≠ dbD1 := by decide
@[simp] theorem db_dbD1_ne_lRn : dbD1 ≠ lRn := by decide
@[simp] theorem db_lRn_ne_dbD1 : lRn ≠ dbD1 := by decide
@[simp] theorem db_dbD1_ne_lDir : dbD1 ≠ lDir := by decide
@[simp] theorem db_lDir_ne_dbD1 : lDir ≠ dbD1 := by decide
@[simp] theorem db_dbD1_ne_lFle : dbD1 ≠ lFle := by decide
@[simp] theorem db_lFle_ne_dbD1 : lFle ≠ dbD1 := by decide
@[simp] theorem db_dbD1_ne_lKb : dbD1 ≠ lKb := by decide
@[simp] theorem db_lKb_ne_dbD1 : lKb ≠ dbD1 := by decide
@[simp] theorem db_dbQ_ne_dbL : dbQ ≠ dbL := by decide
@[simp] theorem db_dbQ_ne_dbF : dbQ ≠ dbF := by decide
@[simp] theorem db_dbQ_ne_dbV : dbQ ≠ dbV := by decide
@[simp] theorem db_dbQ_ne_dbT1 : dbQ ≠ dbT1 := by decide
@[simp] theorem db_dbQ_ne_dbB1 : dbQ ≠ dbB1 := by decide
@[simp] theorem db_dbQ_ne_dbT2 : dbQ ≠ dbT2 := by decide
@[simp] theorem db_dbQ_ne_dbB2 : dbQ ≠ dbB2 := by decide
@[simp] theorem db_dbQ_ne_dbVl : dbQ ≠ dbVl := by decide
@[simp] theorem db_dbQ_ne_dbD2 : dbQ ≠ dbD2 := by decide
@[simp] theorem db_dbQ_ne_dbD1 : dbQ ≠ dbD1 := by decide
@[simp] theorem db_dbQ_ne_dbFv : dbQ ≠ dbFv := by decide
@[simp] theorem db_dbQ_ne_dbV2 : dbQ ≠ dbV2 := by decide
@[simp] theorem db_dbQ_ne_dbP : dbQ ≠ dbP := by decide
@[simp] theorem db_dbQ_ne_dbU1 : dbQ ≠ dbU1 := by decide
@[simp] theorem db_dbQ_ne_dbC1 : dbQ ≠ dbC1 := by decide
@[simp] theorem db_dbQ_ne_dbU2 : dbQ ≠ dbU2 := by decide
@[simp] theorem db_dbQ_ne_dbC2 : dbQ ≠ dbC2 := by decide
@[simp] theorem db_dbQ_ne_dbD3 : dbQ ≠ dbD3 := by decide
@[simp] theorem db_dbQ_ne_dbVl2 : dbQ ≠ dbVl2 := by decide
@[simp] theorem db_dbQ_ne_dbX1 : dbQ ≠ dbX1 := by decide
@[simp] theorem db_dbQ_ne_dbX2 : dbQ ≠ dbX2 := by decide
@[simp] theorem db_dbQ_ne_dbR : dbQ ≠ dbR := by decide
@[simp] theorem db_dbQ_ne_kFu : dbQ ≠ kFu := by decide
@[simp] theorem db_kFu_ne_dbQ : kFu ≠ dbQ := by decide
@[simp] theorem db_dbQ_ne_kD : dbQ ≠ kD := by decide
@[simp] theorem db_kD_ne_dbQ : kD ≠ dbQ := by decide
@[simp] theorem db_dbQ_ne_lFl : dbQ ≠ lFl := by decide
@[simp] theorem db_lFl_ne_dbQ : lFl ≠ dbQ := by decide
@[simp] theorem db_dbQ_ne_lDh : dbQ ≠ lDh := by decide
@[simp] theorem db_lDh_ne_dbQ : lDh ≠ dbQ := by decide
@[simp] theorem db_dbQ_ne_lDt : dbQ ≠ lDt := by decide
@[simp] theorem db_lDt_ne_dbQ : lDt ≠ dbQ := by decide
@[simp] theorem db_dbQ_ne_lDg : dbQ ≠ lDg := by decide
@[simp] theorem db_lDg_ne_dbQ : lDg ≠ dbQ := by decide
@[simp] theorem db_dbQ_ne_lDi : dbQ ≠ lDi := by decide
@[simp] theorem db_lDi_ne_dbQ : lDi ≠ dbQ := by decide
@[simp] theorem db_dbQ_ne_lRp : dbQ ≠ lRp := by decide
@[simp] theorem db_lRp_ne_dbQ : lRp ≠ dbQ := by decide
@[simp] theorem db_dbQ_ne_lRn : dbQ ≠ lRn := by decide
@[simp] theorem db_lRn_ne_dbQ : lRn ≠ dbQ := by decide
@[simp] theorem db_dbQ_ne_lDir : dbQ ≠ lDir := by decide
@[simp] theorem db_lDir_ne_dbQ : lDir ≠ dbQ := by decide
@[simp] theorem db_dbQ_ne_lFle : dbQ ≠ lFle := by decide
@[simp] theorem db_lFle_ne_dbQ : lFle ≠ dbQ := by decide
@[simp] theorem db_dbQ_ne_lKb : dbQ ≠ lKb := by decide
@[simp] theorem db_lKb_ne_dbQ : lKb ≠ dbQ := by decide
@[simp] theorem db_dbFv_ne_dbL : dbFv ≠ dbL := by decide
@[simp] theorem db_dbFv_ne_dbF : dbFv ≠ dbF := by decide
@[simp] theorem db_dbFv_ne_dbV : dbFv ≠ dbV := by decide
@[simp] theorem db_dbFv_ne_dbT1 : dbFv ≠ dbT1 := by decide
@[simp] theorem db_dbFv_ne_dbB1 : dbFv ≠ dbB1 := by decide
@[simp] theorem db_dbFv_ne_dbT2 : dbFv ≠ dbT2 := by decide
@[simp] theorem db_dbFv_ne_dbB2 : dbFv ≠ dbB2 := by decide
@[simp] theorem db_dbFv_ne_dbVl : dbFv ≠ dbVl := by decide
@[simp] theorem db_dbFv_ne_dbD2 : dbFv ≠ dbD2 := by decide
@[simp] theorem db_dbFv_ne_dbD1 : dbFv ≠ dbD1 := by decide
@[simp] theorem db_dbFv_ne_dbQ : dbFv ≠ dbQ := by decide
@[simp] theorem db_dbFv_ne_dbV2 : dbFv ≠ dbV2 := by decide
@[simp] theorem db_dbFv_ne_dbP : dbFv ≠ dbP := by decide
@[simp] theorem db_dbFv_ne_dbU1 : dbFv ≠ dbU1 := by decide
@[simp] theorem db_dbFv_ne_dbC1 : dbFv ≠ dbC1 := by decide
@[simp] theorem db_dbFv_ne_dbU2 : dbFv ≠ dbU2 := by decide
@[simp] theorem db_dbFv_ne_dbC2 : dbFv ≠ dbC2 := by decide
@[simp] theorem db_dbFv_ne_dbD3 : dbFv ≠ dbD3 := by decide
@[simp] theorem db_dbFv_ne_dbVl2 : dbFv ≠ dbVl2 := by decide
@[simp] theorem db_dbFv_ne_dbX1 : dbFv ≠ dbX1 := by decide
@[simp] theorem db_dbFv_ne_dbX2 : dbFv ≠ dbX2 := by decide
@[simp] theorem db_dbFv_ne_dbR : dbFv ≠ dbR := by decide
@[simp] theorem db_dbFv_ne_kFu : dbFv ≠ kFu := by decide
@[simp] theorem db_kFu_ne_dbFv : kFu ≠ dbFv := by decide
@[simp] theorem db_dbFv_ne_kD : dbFv ≠ kD := by decide
@[simp] theorem db_kD_ne_dbFv : kD ≠ dbFv := by decide
@[simp] theorem db_dbFv_ne_lFl : dbFv ≠ lFl := by decide
@[simp] theorem db_lFl_ne_dbFv : lFl ≠ dbFv := by decide
@[simp] theorem db_dbFv_ne_lDh : dbFv ≠ lDh := by decide
@[simp] theorem db_lDh_ne_dbFv : lDh ≠ dbFv := by decide
@[simp] theorem db_dbFv_ne_lDt : dbFv ≠ lDt := by decide
@[simp] theorem db_lDt_ne_dbFv : lDt ≠ dbFv := by decide
@[simp] theorem db_dbFv_ne_lDg : dbFv ≠ lDg := by decide
@[simp] theorem db_lDg_ne_dbFv : lDg ≠ dbFv := by decide
@[simp] theorem db_dbFv_ne_lDi : dbFv ≠ lDi := by decide
@[simp] theorem db_lDi_ne_dbFv : lDi ≠ dbFv := by decide
@[simp] theorem db_dbFv_ne_lRp : dbFv ≠ lRp := by decide
@[simp] theorem db_lRp_ne_dbFv : lRp ≠ dbFv := by decide
@[simp] theorem db_dbFv_ne_lRn : dbFv ≠ lRn := by decide
@[simp] theorem db_lRn_ne_dbFv : lRn ≠ dbFv := by decide
@[simp] theorem db_dbFv_ne_lDir : dbFv ≠ lDir := by decide
@[simp] theorem db_lDir_ne_dbFv : lDir ≠ dbFv := by decide
@[simp] theorem db_dbFv_ne_lFle : dbFv ≠ lFle := by decide
@[simp] theorem db_lFle_ne_dbFv : lFle ≠ dbFv := by decide
@[simp] theorem db_dbFv_ne_lKb : dbFv ≠ lKb := by decide
@[simp] theorem db_lKb_ne_dbFv : lKb ≠ dbFv := by decide
@[simp] theorem db_dbV2_ne_dbL : dbV2 ≠ dbL := by decide
@[simp] theorem db_dbV2_ne_dbF : dbV2 ≠ dbF := by decide
@[simp] theorem db_dbV2_ne_dbV : dbV2 ≠ dbV := by decide
@[simp] theorem db_dbV2_ne_dbT1 : dbV2 ≠ dbT1 := by decide
@[simp] theorem db_dbV2_ne_dbB1 : dbV2 ≠ dbB1 := by decide
@[simp] theorem db_dbV2_ne_dbT2 : dbV2 ≠ dbT2 := by decide
@[simp] theorem db_dbV2_ne_dbB2 : dbV2 ≠ dbB2 := by decide
@[simp] theorem db_dbV2_ne_dbVl : dbV2 ≠ dbVl := by decide
@[simp] theorem db_dbV2_ne_dbD2 : dbV2 ≠ dbD2 := by decide
@[simp] theorem db_dbV2_ne_dbD1 : dbV2 ≠ dbD1 := by decide
@[simp] theorem db_dbV2_ne_dbQ : dbV2 ≠ dbQ := by decide
@[simp] theorem db_dbV2_ne_dbFv : dbV2 ≠ dbFv := by decide
@[simp] theorem db_dbV2_ne_dbP : dbV2 ≠ dbP := by decide
@[simp] theorem db_dbV2_ne_dbU1 : dbV2 ≠ dbU1 := by decide
@[simp] theorem db_dbV2_ne_dbC1 : dbV2 ≠ dbC1 := by decide
@[simp] theorem db_dbV2_ne_dbU2 : dbV2 ≠ dbU2 := by decide
@[simp] theorem db_dbV2_ne_dbC2 : dbV2 ≠ dbC2 := by decide
@[simp] theorem db_dbV2_ne_dbD3 : dbV2 ≠ dbD3 := by decide
@[simp] theorem db_dbV2_ne_dbVl2 : dbV2 ≠ dbVl2 := by decide
@[simp] theorem db_dbV2_ne_dbX1 : dbV2 ≠ dbX1 := by decide
@[simp] theorem db_dbV2_ne_dbX2 : dbV2 ≠ dbX2 := by decide
@[simp] theorem db_dbV2_ne_dbR : dbV2 ≠ dbR := by decide
@[simp] theorem db_dbV2_ne_kFu : dbV2 ≠ kFu := by decide
@[simp] theorem db_kFu_ne_dbV2 : kFu ≠ dbV2 := by decide
@[simp] theorem db_dbV2_ne_kD : dbV2 ≠ kD := by decide
@[simp] theorem db_kD_ne_dbV2 : kD ≠ dbV2 := by decide
@[simp] theorem db_dbV2_ne_lFl : dbV2 ≠ lFl := by decide
@[simp] theorem db_lFl_ne_dbV2 : lFl ≠ dbV2 := by decide
@[simp] theorem db_dbV2_ne_lDh : dbV2 ≠ lDh := by decide
@[simp] theorem db_lDh_ne_dbV2 : lDh ≠ dbV2 := by decide
@[simp] theorem db_dbV2_ne_lDt : dbV2 ≠ lDt := by decide
@[simp] theorem db_lDt_ne_dbV2 : lDt ≠ dbV2 := by decide
@[simp] theorem db_dbV2_ne_lDg : dbV2 ≠ lDg := by decide
@[simp] theorem db_lDg_ne_dbV2 : lDg ≠ dbV2 := by decide
@[simp] theorem db_dbV2_ne_lDi : dbV2 ≠ lDi := by decide
@[simp] theorem db_lDi_ne_dbV2 : lDi ≠ dbV2 := by decide
@[simp] theorem db_dbV2_ne_lRp : dbV2 ≠ lRp := by decide
@[simp] theorem db_lRp_ne_dbV2 : lRp ≠ dbV2 := by decide
@[simp] theorem db_dbV2_ne_lRn : dbV2 ≠ lRn := by decide
@[simp] theorem db_lRn_ne_dbV2 : lRn ≠ dbV2 := by decide
@[simp] theorem db_dbV2_ne_lDir : dbV2 ≠ lDir := by decide
@[simp] theorem db_lDir_ne_dbV2 : lDir ≠ dbV2 := by decide
@[simp] theorem db_dbV2_ne_lFle : dbV2 ≠ lFle := by decide
@[simp] theorem db_lFle_ne_dbV2 : lFle ≠ dbV2 := by decide
@[simp] theorem db_dbV2_ne_lKb : dbV2 ≠ lKb := by decide
@[simp] theorem db_lKb_ne_dbV2 : lKb ≠ dbV2 := by decide
@[simp] theorem db_dbP_ne_dbL : dbP ≠ dbL := by decide
@[simp] theorem db_dbP_ne_dbF : dbP ≠ dbF := by decide
@[simp] theorem db_dbP_ne_dbV : dbP ≠ dbV := by decide
@[simp] theorem db_dbP_ne_dbT1 : dbP ≠ dbT1 := by decide
@[simp] theorem db_dbP_ne_dbB1 : dbP ≠ dbB1 := by decide
@[simp] theorem db_dbP_ne_dbT2 : dbP ≠ dbT2 := by decide
@[simp] theorem db_dbP_ne_dbB2 : dbP ≠ dbB2 := by decide
@[simp] theorem db_dbP_ne_dbVl : dbP ≠ dbVl := by decide
@[simp] theorem db_dbP_ne_dbD2 : dbP ≠ dbD2 := by decide
@[simp] theorem db_dbP_ne_dbD1 : dbP ≠ dbD1 := by decide
@[simp] theorem db_dbP_ne_dbQ : dbP ≠ dbQ := by decide
@[simp] theorem db_dbP_ne_dbFv : dbP ≠ dbFv := by decide
@[simp] theorem db_dbP_ne_dbV2 : dbP ≠ dbV2 := by decide
@[simp] theorem db_dbP_ne_dbU1 : dbP ≠ dbU1 := by decide
@[simp] theorem db_dbP_ne_dbC1 : dbP ≠ dbC1 := by decide
@[simp] theorem db_dbP_ne_dbU2 : dbP ≠ dbU2 := by decide
@[simp] theorem db_dbP_ne_dbC2 : dbP ≠ dbC2 := by decide
@[simp] theorem db_dbP_ne_dbD3 : dbP ≠ dbD3 := by decide
@[simp] theorem db_dbP_ne_dbVl2 : dbP ≠ dbVl2 := by decide
@[simp] theorem db_dbP_ne_dbX1 : dbP ≠ dbX1 := by decide
@[simp] theorem db_dbP_ne_dbX2 : dbP ≠ dbX2 := by decide
@[simp] theorem db_dbP_ne_dbR : dbP ≠ dbR := by decide
@[simp] theorem db_dbP_ne_kFu : dbP ≠ kFu := by decide
@[simp] theorem db_kFu_ne_dbP : kFu ≠ dbP := by decide
@[simp] theorem db_dbP_ne_kD : dbP ≠ kD := by decide
@[simp] theorem db_kD_ne_dbP : kD ≠ dbP := by decide
@[simp] theorem db_dbP_ne_lFl : dbP ≠ lFl := by decide
@[simp] theorem db_lFl_ne_dbP : lFl ≠ dbP := by decide
@[simp] theorem db_dbP_ne_lDh : dbP ≠ lDh := by decide
@[simp] theorem db_lDh_ne_dbP : lDh ≠ dbP := by decide
@[simp] theorem db_dbP_ne_lDt : dbP ≠ lDt := by decide
@[simp] theorem db_lDt_ne_dbP : lDt ≠ dbP := by decide
@[simp] theorem db_dbP_ne_lDg : dbP ≠ lDg := by decide
@[simp] theorem db_lDg_ne_dbP : lDg ≠ dbP := by decide
@[simp] theorem db_dbP_ne_lDi : dbP ≠ lDi := by decide
@[simp] theorem db_lDi_ne_dbP : lDi ≠ dbP := by decide
@[simp] theorem db_dbP_ne_lRp : dbP ≠ lRp := by decide
@[simp] theorem db_lRp_ne_dbP : lRp ≠ dbP := by decide
@[simp] theorem db_dbP_ne_lRn : dbP ≠ lRn := by decide
@[simp] theorem db_lRn_ne_dbP : lRn ≠ dbP := by decide
@[simp] theorem db_dbP_ne_lDir : dbP ≠ lDir := by decide
@[simp] theorem db_lDir_ne_dbP : lDir ≠ dbP := by decide
@[simp] theorem db_dbP_ne_lFle : dbP ≠ lFle := by decide
@[simp] theorem db_lFle_ne_dbP : lFle ≠ dbP := by decide
@[simp] theorem db_dbP_ne_lKb : dbP ≠ lKb := by decide
@[simp] theorem db_lKb_ne_dbP : lKb ≠ dbP := by decide
@[simp] theorem db_dbU1_ne_dbL : dbU1 ≠ dbL := by decide
@[simp] theorem db_dbU1_ne_dbF : dbU1 ≠ dbF := by decide
@[simp] theorem db_dbU1_ne_dbV : dbU1 ≠ dbV := by decide
@[simp] theorem db_dbU1_ne_dbT1 : dbU1 ≠ dbT1 := by decide
@[simp] theorem db_dbU1_ne_dbB1 : dbU1 ≠ dbB1 := by decide
@[simp] theorem db_dbU1_ne_dbT2 : dbU1 ≠ dbT2 := by decide
@[simp] theorem db_dbU1_ne_dbB2 : dbU1 ≠ dbB2 := by decide
@[simp] theorem db_dbU1_ne_dbVl : dbU1 ≠ dbVl := by decide
@[simp] theorem db_dbU1_ne_dbD2 : dbU1 ≠ dbD2 := by decide
@[simp] theorem db_dbU1_ne_dbD1 : dbU1 ≠ dbD1 := by decide
@[simp] theorem db_dbU1_ne_dbQ : dbU1 ≠ dbQ := by decide
@[simp] theorem db_dbU1_ne_dbFv : dbU1 ≠ dbFv := by decide
@[simp] theorem db_dbU1_ne_dbV2 : dbU1 ≠ dbV2 := by decide
@[simp] theorem db_dbU1_ne_dbP : dbU1 ≠ dbP := by decide
@[simp] theorem db_dbU1_ne_dbC1 : dbU1 ≠ dbC1 := by decide
@[simp] theorem db_dbU1_ne_dbU2 : dbU1 ≠ dbU2 := by decide
@[simp] theorem db_dbU1_ne_dbC2 : dbU1 ≠ dbC2 := by decide
@[simp] theorem db_dbU1_ne_dbD3 : dbU1 ≠ dbD3 := by decide
@[simp] theorem db_dbU1_ne_dbVl2 : dbU1 ≠ dbVl2 := by decide
@[simp] theorem db_dbU1_ne_dbX1 : dbU1 ≠ dbX1 := by decide
@[simp] theorem db_dbU1_ne_dbX2 : dbU1 ≠ dbX2 := by decide
@[simp] theorem db_dbU1_ne_dbR : dbU1 ≠ dbR := by decide
@[simp] theorem db_dbU1_ne_kFu : dbU1 ≠ kFu := by decide
@[simp] theorem db_kFu_ne_dbU1 : kFu ≠ dbU1 := by decide
@[simp] theorem db_dbU1_ne_kD : dbU1 ≠ kD := by decide
@[simp] theorem db_kD_ne_dbU1 : kD ≠ dbU1 := by decide
@[simp] theorem db_dbU1_ne_lFl : dbU1 ≠ lFl := by decide
@[simp] theorem db_lFl_ne_dbU1 : lFl ≠ dbU1 := by decide
@[simp] theorem db_dbU1_ne_lDh : dbU1 ≠ lDh := by decide
@[simp] theorem db_lDh_ne_dbU1 : lDh ≠ dbU1 := by decide
@[simp] theorem db_dbU1_ne_lDt : dbU1 ≠ lDt := by decide
@[simp] theorem db_lDt_ne_dbU1 : lDt ≠ dbU1 := by decide
@[simp] theorem db_dbU1_ne_lDg : dbU1 ≠ lDg := by decide
@[simp] theorem db_lDg_ne_dbU1 : lDg ≠ dbU1 := by decide
@[simp] theorem db_dbU1_ne_lDi : dbU1 ≠ lDi := by decide
@[simp] theorem db_lDi_ne_dbU1 : lDi ≠ dbU1 := by decide
@[simp] theorem db_dbU1_ne_lRp : dbU1 ≠ lRp := by decide
@[simp] theorem db_lRp_ne_dbU1 : lRp ≠ dbU1 := by decide
@[simp] theorem db_dbU1_ne_lRn : dbU1 ≠ lRn := by decide
@[simp] theorem db_lRn_ne_dbU1 : lRn ≠ dbU1 := by decide
@[simp] theorem db_dbU1_ne_lDir : dbU1 ≠ lDir := by decide
@[simp] theorem db_lDir_ne_dbU1 : lDir ≠ dbU1 := by decide
@[simp] theorem db_dbU1_ne_lFle : dbU1 ≠ lFle := by decide
@[simp] theorem db_lFle_ne_dbU1 : lFle ≠ dbU1 := by decide
@[simp] theorem db_dbU1_ne_lKb : dbU1 ≠ lKb := by decide
@[simp] theorem db_lKb_ne_dbU1 : lKb ≠ dbU1 := by decide
@[simp] theorem db_dbC1_ne_dbL : dbC1 ≠ dbL := by decide
@[simp] theorem db_dbC1_ne_dbF : dbC1 ≠ dbF := by decide
@[simp] theorem db_dbC1_ne_dbV : dbC1 ≠ dbV := by decide
@[simp] theorem db_dbC1_ne_dbT1 : dbC1 ≠ dbT1 := by decide
@[simp] theorem db_dbC1_ne_dbB1 : dbC1 ≠ dbB1 := by decide
@[simp] theorem db_dbC1_ne_dbT2 : dbC1 ≠ dbT2 := by decide
@[simp] theorem db_dbC1_ne_dbB2 : dbC1 ≠ dbB2 := by decide
@[simp] theorem db_dbC1_ne_dbVl : dbC1 ≠ dbVl := by decide
@[simp] theorem db_dbC1_ne_dbD2 : dbC1 ≠ dbD2 := by decide
@[simp] theorem db_dbC1_ne_dbD1 : dbC1 ≠ dbD1 := by decide
@[simp] theorem db_dbC1_ne_dbQ : dbC1 ≠ dbQ := by decide
@[simp] theorem db_dbC1_ne_dbFv : dbC1 ≠ dbFv := by decide
@[simp] theorem db_dbC1_ne_dbV2 : dbC1 ≠ dbV2 := by decide
@[simp] theorem db_dbC1_ne_dbP : dbC1 ≠ dbP := by decide
@[simp] theorem db_dbC1_ne_dbU1 : dbC1 ≠ dbU1 := by decide
@[simp] theorem db_dbC1_ne_dbU2 : dbC1 ≠ dbU2 := by decide
@[simp] theorem db_dbC1_ne_dbC2 : dbC1 ≠ dbC2 := by decide
@[simp] theorem db_dbC1_ne_dbD3 : dbC1 ≠ dbD3 := by decide
@[simp] theorem db_dbC1_ne_dbVl2 : dbC1 ≠ dbVl2 := by decide
@[simp] theorem db_dbC1_ne_dbX1 : dbC1 ≠ dbX1 := by decide
@[simp] theorem db_dbC1_ne_dbX2 : dbC1 ≠ dbX2 := by decide
@[simp] theorem db_dbC1_ne_dbR : dbC1 ≠ dbR := by decide
@[simp] theorem db_dbC1_ne_kFu : dbC1 ≠ kFu := by decide
@[simp] theorem db_kFu_ne_dbC1 : kFu ≠ dbC1 := by decide
@[simp] theorem db_dbC1_ne_kD : dbC1 ≠ kD := by decide
@[simp] theorem db_kD_ne_dbC1 : kD ≠ dbC1 := by decide
@[simp] theorem db_dbC1_ne_lFl : dbC1 ≠ lFl := by decide
@[simp] theorem db_lFl_ne_dbC1 : lFl ≠ dbC1 := by decide
@[simp] theorem db_dbC1_ne_lDh : dbC1 ≠ lDh := by decide
@[simp] theorem db_lDh_ne_dbC1 : lDh ≠ dbC1 := by decide
@[simp] theorem db_dbC1_ne_lDt : dbC1 ≠ lDt := by decide
@[simp] theorem db_lDt_ne_dbC1 : lDt ≠ dbC1 := by decide
@[simp] theorem db_dbC1_ne_lDg : dbC1 ≠ lDg := by decide
@[simp] theorem db_lDg_ne_dbC1 : lDg ≠ dbC1 := by decide
@[simp] theorem db_dbC1_ne_lDi : dbC1 ≠ lDi := by decide
@[simp] theorem db_lDi_ne_dbC1 : lDi ≠ dbC1 := by decide
@[simp] theorem db_dbC1_ne_lRp : dbC1 ≠ lRp := by decide
@[simp] theorem db_lRp_ne_dbC1 : lRp ≠ dbC1 := by decide
@[simp] theorem db_dbC1_ne_lRn : dbC1 ≠ lRn := by decide
@[simp] theorem db_lRn_ne_dbC1 : lRn ≠ dbC1 := by decide
@[simp] theorem db_dbC1_ne_lDir : dbC1 ≠ lDir := by decide
@[simp] theorem db_lDir_ne_dbC1 : lDir ≠ dbC1 := by decide
@[simp] theorem db_dbC1_ne_lFle : dbC1 ≠ lFle := by decide
@[simp] theorem db_lFle_ne_dbC1 : lFle ≠ dbC1 := by decide
@[simp] theorem db_dbC1_ne_lKb : dbC1 ≠ lKb := by decide
@[simp] theorem db_lKb_ne_dbC1 : lKb ≠ dbC1 := by decide
@[simp] theorem db_dbU2_ne_dbL : dbU2 ≠ dbL := by decide
@[simp] theorem db_dbU2_ne_dbF : dbU2 ≠ dbF := by decide
@[simp] theorem db_dbU2_ne_dbV : dbU2 ≠ dbV := by decide
@[simp] theorem db_dbU2_ne_dbT1 : dbU2 ≠ dbT1 := by decide
@[simp] theorem db_dbU2_ne_dbB1 : dbU2 ≠ dbB1 := by decide
@[simp] theorem db_dbU2_ne_dbT2 : dbU2 ≠ dbT2 := by decide
@[simp] theorem db_dbU2_ne_dbB2 : dbU2 ≠ dbB2 := by decide
@[simp] theorem db_dbU2_ne_dbVl : dbU2 ≠ dbVl := by decide
@[simp] theorem db_dbU2_ne_dbD2 : dbU2 ≠ dbD2 := by decide
@[simp] theorem db_dbU2_ne_dbD1 : dbU2 ≠ dbD1 := by decide
@[simp] theorem db_dbU2_ne_dbQ : dbU2 ≠ dbQ := by decide
@[simp] theorem db_dbU2_ne_dbFv : dbU2 ≠ dbFv := by decide
@[simp] theorem db_dbU2_ne_dbV2 : dbU2 ≠ dbV2 := by decide
@[simp] theorem db_dbU2_ne_dbP : dbU2 ≠ dbP := by decide
@[simp] theorem db_dbU2_ne_dbU1 : dbU2 ≠ dbU1 := by decide
@[simp] theorem db_dbU2_ne_dbC1 : dbU2 ≠ dbC1 := by decide
@[simp] theorem db_dbU2_ne_dbC2 : dbU2 ≠ dbC2 := by decide
@[simp] theorem db_dbU2_ne_dbD3 : dbU2 ≠ dbD3 := by decide
@[simp] theorem db_dbU2_ne_dbVl2 : dbU2 ≠ dbVl2 := by decide
@[simp] theorem db_dbU2_ne_dbX1 : dbU2 ≠ dbX1 := by decide
@[simp] theorem db_dbU2_ne_dbX2 : dbU2 ≠ dbX2 := by decide
@[simp] theorem db_dbU2_ne_dbR : dbU2 ≠ dbR := by decide
@[simp] theorem db_dbU2_ne_kFu : dbU2 ≠ kFu := by decide
@[simp] theorem db_kFu_ne_dbU2 : kFu ≠ dbU2 := by decide
@[simp] theorem db_dbU2_ne_kD : dbU2 ≠ kD := by decide
@[simp] theorem db_kD_ne_dbU2 : kD ≠ dbU2 := by decide
@[simp] theorem db_dbU2_ne_lFl : dbU2 ≠ lFl := by decide
@[simp] theorem db_lFl_ne_dbU2 : lFl ≠ dbU2 := by decide
@[simp] theorem db_dbU2_ne_lDh : dbU2 ≠ lDh := by decide
@[simp] theorem db_lDh_ne_dbU2 : lDh ≠ dbU2 := by decide
@[simp] theorem db_dbU2_ne_lDt : dbU2 ≠ lDt := by decide
@[simp] theorem db_lDt_ne_dbU2 : lDt ≠ dbU2 := by decide
@[simp] theorem db_dbU2_ne_lDg : dbU2 ≠ lDg := by decide
@[simp] theorem db_lDg_ne_dbU2 : lDg ≠ dbU2 := by decide
@[simp] theorem db_dbU2_ne_lDi : dbU2 ≠ lDi := by decide
@[simp] theorem db_lDi_ne_dbU2 : lDi ≠ dbU2 := by decide
@[simp] theorem db_dbU2_ne_lRp : dbU2 ≠ lRp := by decide
@[simp] theorem db_lRp_ne_dbU2 : lRp ≠ dbU2 := by decide
@[simp] theorem db_dbU2_ne_lRn : dbU2 ≠ lRn := by decide
@[simp] theorem db_lRn_ne_dbU2 : lRn ≠ dbU2 := by decide
@[simp] theorem db_dbU2_ne_lDir : dbU2 ≠ lDir := by decide
@[simp] theorem db_lDir_ne_dbU2 : lDir ≠ dbU2 := by decide
@[simp] theorem db_dbU2_ne_lFle : dbU2 ≠ lFle := by decide
@[simp] theorem db_lFle_ne_dbU2 : lFle ≠ dbU2 := by decide
@[simp] theorem db_dbU2_ne_lKb : dbU2 ≠ lKb := by decide
@[simp] theorem db_lKb_ne_dbU2 : lKb ≠ dbU2 := by decide
@[simp] theorem db_dbC2_ne_dbL : dbC2 ≠ dbL := by decide
@[simp] theorem db_dbC2_ne_dbF : dbC2 ≠ dbF := by decide
@[simp] theorem db_dbC2_ne_dbV : dbC2 ≠ dbV := by decide
@[simp] theorem db_dbC2_ne_dbT1 : dbC2 ≠ dbT1 := by decide
@[simp] theorem db_dbC2_ne_dbB1 : dbC2 ≠ dbB1 := by decide
@[simp] theorem db_dbC2_ne_dbT2 : dbC2 ≠ dbT2 := by decide
@[simp] theorem db_dbC2_ne_dbB2 : dbC2 ≠ dbB2 := by decide
@[simp] theorem db_dbC2_ne_dbVl : dbC2 ≠ dbVl := by decide
@[simp] theorem db_dbC2_ne_dbD2 : dbC2 ≠ dbD2 := by decide
@[simp] theorem db_dbC2_ne_dbD1 : dbC2 ≠ dbD1 := by decide
@[simp] theorem db_dbC2_ne_dbQ : dbC2 ≠ dbQ := by decide
@[simp] theorem db_dbC2_ne_dbFv : dbC2 ≠ dbFv := by decide
@[simp] theorem db_dbC2_ne_dbV2 : dbC2 ≠ dbV2 := by decide
@[simp] theorem db_dbC2_ne_dbP : dbC2 ≠ dbP := by decide
@[simp] theorem db_dbC2_ne_dbU1 : dbC2 ≠ dbU1 := by decide
@[simp] theorem db_dbC2_ne_dbC1 : dbC2 ≠ dbC1 := by decide
@[simp] theorem db_dbC2_ne_dbU2 : dbC2 ≠ dbU2 := by decide
@[simp] theorem db_dbC2_ne_dbD3 : dbC2 ≠ dbD3 := by decide
@[simp] theorem db_dbC2_ne_dbVl2 : dbC2 ≠ dbVl2 := by decide
@[simp] theorem db_dbC2_ne_dbX1 : dbC2 ≠ dbX1 := by decide
@[simp] theorem db_dbC2_ne_dbX2 : dbC2 ≠ dbX2 := by decide
@[simp] theorem db_dbC2_ne_dbR : dbC2 ≠ dbR := by decide
@[simp] theorem db_dbC2_ne_kFu : dbC2 ≠ kFu := by decide
@[simp] theorem db_kFu_ne_dbC2 : kFu ≠ dbC2 := by decide
@[simp] theorem db_dbC2_ne_kD : dbC2 ≠ kD := by decide
@[simp] theorem db_kD_ne_dbC2 : kD ≠ dbC2 := by decide
@[simp] theorem db_dbC2_ne_lFl : dbC2 ≠ lFl := by decide
@[simp] theorem db_lFl_ne_dbC2 : lFl ≠ dbC2 := by decide
@[simp] theorem db_dbC2_ne_lDh : dbC2 ≠ lDh := by decide
@[simp] theorem db_lDh_ne_dbC2 : lDh ≠ dbC2 := by decide
@[simp] theorem db_dbC2_ne_lDt : dbC2 ≠ lDt := by decide
@[simp] theorem db_lDt_ne_dbC2 : lDt ≠ dbC2 := by decide
@[simp] theorem db_dbC2_ne_lDg : dbC2 ≠ lDg := by decide
@[simp] theorem db_lDg_ne_dbC2 : lDg ≠ dbC2 := by decide
@[simp] theorem db_dbC2_ne_lDi : dbC2 ≠ lDi := by decide
@[simp] theorem db_lDi_ne_dbC2 : lDi ≠ dbC2 := by decide
@[simp] theorem db_dbC2_ne_lRp : dbC2 ≠ lRp := by decide
@[simp] theorem db_lRp_ne_dbC2 : lRp ≠ dbC2 := by decide
@[simp] theorem db_dbC2_ne_lRn : dbC2 ≠ lRn := by decide
@[simp] theorem db_lRn_ne_dbC2 : lRn ≠ dbC2 := by decide
@[simp] theorem db_dbC2_ne_lDir : dbC2 ≠ lDir := by decide
@[simp] theorem db_lDir_ne_dbC2 : lDir ≠ dbC2 := by decide
@[simp] theorem db_dbC2_ne_lFle : dbC2 ≠ lFle := by decide
@[simp] theorem db_lFle_ne_dbC2 : lFle ≠ dbC2 := by decide
@[simp] theorem db_dbC2_ne_lKb : dbC2 ≠ lKb := by decide
@[simp] theorem db_lKb_ne_dbC2 : lKb ≠ dbC2 := by decide
@[simp] theorem db_dbD3_ne_dbL : dbD3 ≠ dbL := by decide
@[simp] theorem db_dbD3_ne_dbF : dbD3 ≠ dbF := by decide
@[simp] theorem db_dbD3_ne_dbV : dbD3 ≠ dbV := by decide
@[simp] theorem db_dbD3_ne_dbT1 : dbD3 ≠ dbT1 := by decide
@[simp] theorem db_dbD3_ne_dbB1 : dbD3 ≠ dbB1 := by decide
@[simp] theorem db_dbD3_ne_dbT2 : dbD3 ≠ dbT2 := by decide
@[simp] theorem db_dbD3_ne_dbB2 : dbD3 ≠ dbB2 := by decide
@[simp] theorem db_dbD3_ne_dbVl : dbD3 ≠ dbVl := by decide
@[simp] theorem db_dbD3_ne_dbD2 : dbD3 ≠ dbD2 := by decide
@[simp] theorem db_dbD3_ne_dbD1 : dbD3 ≠ dbD1 := by decide
@[simp] theorem db_dbD3_ne_dbQ : dbD3 ≠ dbQ := by decide
@[simp] theorem db_dbD3_ne_dbFv : dbD3 ≠ dbFv := by decide
@[simp] theorem db_dbD3_ne_dbV2 : dbD3 ≠ dbV2 := by decide
@[simp] theorem db_dbD3_ne_dbP : dbD3 ≠ dbP := by decide
@[simp] theorem db_dbD3_ne_dbU1 : dbD3 ≠ dbU1 := by decide
@[simp] theorem db_dbD3_ne_dbC1 : dbD3 ≠ dbC1 := by decide
@[simp] theorem db_dbD3_ne_dbU2 : dbD3 ≠ dbU2 := by decide
@[simp] theorem db_dbD3_ne_dbC2 : dbD3 ≠ dbC2 := by decide
@[simp] theorem db_dbD3_ne_dbVl2 : dbD3 ≠ dbVl2 := by decide
@[simp] theorem db_dbD3_ne_dbX1 : dbD3 ≠ dbX1 := by decide
@[simp] theorem db_dbD3_ne_dbX2 : dbD3 ≠ dbX2 := by decide
@[simp] theorem db_dbD3_ne_dbR : dbD3 ≠ dbR := by decide
@[simp] theorem db_dbD3_ne_kFu : dbD3 ≠ kFu := by decide
@[simp] theorem db_kFu_ne_dbD3 : kFu ≠ dbD3 := by decide
@[simp] theorem db_dbD3_ne_kD : dbD3 ≠ kD := by decide
@[simp] theorem db_kD_ne_dbD3 : kD ≠ dbD3 := by decide
@[simp] theorem db_dbD3_ne_lFl : dbD3 ≠ lFl := by decide
@[simp] theorem db_lFl_ne_dbD3 : lFl ≠ dbD3 := by decide
@[simp] theorem db_dbD3_ne_lDh : dbD3 ≠ lDh := by decide
@[simp] theorem db_lDh_ne_dbD3 : lDh ≠ dbD3 := by decide
@[simp] theorem db_dbD3_ne_lDt : dbD3 ≠ lDt := by decide
@[simp] theorem db_lDt_ne_dbD3 : lDt ≠ dbD3 := by decide
@[simp] theorem db_dbD3_ne_lDg : dbD3 ≠ lDg := by decide
@[simp] theorem db_lDg_ne_dbD3 : lDg ≠ dbD3 := by decide
@[simp] theorem db_dbD3_ne_lDi : dbD3 ≠ lDi := by decide
@[simp] theorem db_lDi_ne_dbD3 : lDi ≠ dbD3 := by decide
@[simp] theorem db_dbD3_ne_lRp : dbD3 ≠ lRp := by decide
@[simp] theorem db_lRp_ne_dbD3 : lRp ≠ dbD3 := by decide
@[simp] theorem db_dbD3_ne_lRn : dbD3 ≠ lRn := by decide
@[simp] theorem db_lRn_ne_dbD3 : lRn ≠ dbD3 := by decide
@[simp] theorem db_dbD3_ne_lDir : dbD3 ≠ lDir := by decide
@[simp] theorem db_lDir_ne_dbD3 : lDir ≠ dbD3 := by decide
@[simp] theorem db_dbD3_ne_lFle : dbD3 ≠ lFle := by decide
@[simp] theorem db_lFle_ne_dbD3 : lFle ≠ dbD3 := by decide
@[simp] theorem db_dbD3_ne_lKb : dbD3 ≠ lKb := by decide
@[simp] theorem db_lKb_ne_dbD3 : lKb ≠ dbD3 := by decide
@[simp] theorem db_dbVl2_ne_dbL : dbVl2 ≠ dbL := by decide
@[simp] theorem db_dbVl2_ne_dbF : dbVl2 ≠ dbF := by decide
@[simp] theorem db_dbVl2_ne_dbV : dbVl2 ≠ dbV := by decide
@[simp] theorem db_dbVl2_ne_dbT1 : dbVl2 ≠ dbT1 := by decide
@[simp] theorem db_dbVl2_ne_dbB1 : dbVl2 ≠ dbB1 := by decide
@[simp] theorem db_dbVl2_ne_dbT2 : dbVl2 ≠ dbT2 := by decide
@[simp] theorem db_dbVl2_ne_dbB2 : dbVl2 ≠ dbB2 := by decide
@[simp] theorem db_dbVl2_ne_dbVl : dbVl2 ≠ dbVl := by decide
@[simp] theorem db_dbVl2_ne_dbD2 : dbVl2 ≠ dbD2 := by decide
@[simp] theorem db_dbVl2_ne_dbD1 : dbVl2 ≠ dbD1 := by decide
@[simp] theorem db_dbVl2_ne_dbQ : dbVl2 ≠ dbQ := by decide
@[simp] theorem db_dbVl2_ne_dbFv : dbVl2 ≠ dbFv := by decide
@[simp] theorem db_dbVl2_ne_dbV2 : dbVl2 ≠ dbV2 := by decide
@[simp] theorem db_dbVl2_ne_dbP : dbVl2 ≠ dbP := by decide
@[simp] theorem db_dbVl2_ne_dbU1 : dbVl2 ≠ dbU1 := by decide
@[simp] theorem db_dbVl2_ne_dbC1 : dbVl2 ≠ dbC1 := by decide
@[simp] theorem db_dbVl2_ne_dbU2 : dbVl2 ≠ dbU2 := by decide
@[simp] theorem db_dbVl2_ne_dbC2 : dbVl2 ≠ dbC2 := by decide
@[simp] theorem db_dbVl2_ne_dbD3 : dbVl2 ≠ dbD3 := by decide
@[simp] theorem db_dbVl2_ne_dbX1 : dbVl2 ≠ dbX1 := by decide
@[simp] theorem db_dbVl2_ne_dbX2 : dbVl2 ≠ dbX2 := by decide
@[simp] theorem db_dbVl2_ne_dbR : dbVl2 ≠ dbR := by decide
@[simp] theorem db_dbVl2_ne_kFu : dbVl2 ≠ kFu := by decide
@[simp] theorem db_kFu_ne_dbVl2 : kFu ≠ dbVl2 := by decide
@[simp] theorem db_dbVl2_ne_kD : dbVl2 ≠ kD := by decide
@[simp] theorem db_kD_ne_dbVl2 : kD ≠ dbVl2 := by decide
@[simp] theorem db_dbVl2_ne_lFl : dbVl2 ≠ lFl := by decide
@[simp] theorem db_lFl_ne_dbVl2 : lFl ≠ dbVl2 := by decide
@[simp] theorem db_dbVl2_ne_lDh : dbVl2 ≠ lDh := by decide
@[simp] theorem db_lDh_ne_dbVl2 : lDh ≠ dbVl2 := by decide
@[simp] theorem db_dbVl2_ne_lDt : dbVl2 ≠ lDt := by decide
@[simp] theorem db_lDt_ne_dbVl2 : lDt ≠ dbVl2 := by decide
@[simp] theorem db_dbVl2_ne_lDg : dbVl2 ≠ lDg := by decide
@[simp] theorem db_lDg_ne_dbVl2 : lDg ≠ dbVl2 := by decide
@[simp] theorem db_dbVl2_ne_lDi : dbVl2 ≠ lDi := by decide
@[simp] theorem db_lDi_ne_dbVl2 : lDi ≠ dbVl2 := by decide
@[simp] theorem db_dbVl2_ne_lRp : dbVl2 ≠ lRp := by decide
@[simp] theorem db_lRp_ne_dbVl2 : lRp ≠ dbVl2 := by decide
@[simp] theorem db_dbVl2_ne_lRn : dbVl2 ≠ lRn := by decide
@[simp] theorem db_lRn_ne_dbVl2 : lRn ≠ dbVl2 := by decide
@[simp] theorem db_dbVl2_ne_lDir : dbVl2 ≠ lDir := by decide
@[simp] theorem db_lDir_ne_dbVl2 : lDir ≠ dbVl2 := by decide
@[simp] theorem db_dbVl2_ne_lFle : dbVl2 ≠ lFle := by decide
@[simp] theorem db_lFle_ne_dbVl2 : lFle ≠ dbVl2 := by decide
@[simp] theorem db_dbVl2_ne_lKb : dbVl2 ≠ lKb := by decide
@[simp] theorem db_lKb_ne_dbVl2 : lKb ≠ dbVl2 := by decide
@[simp] theorem db_dbX1_ne_dbL : dbX1 ≠ dbL := by decide
@[simp] theorem db_dbX1_ne_dbF : dbX1 ≠ dbF := by decide
@[simp] theorem db_dbX1_ne_dbV : dbX1 ≠ dbV := by decide
@[simp] theorem db_dbX1_ne_dbT1 : dbX1 ≠ dbT1 := by decide
@[simp] theorem db_dbX1_ne_dbB1 : dbX1 ≠ dbB1 := by decide
@[simp] theorem db_dbX1_ne_dbT2 : dbX1 ≠ dbT2 := by decide
@[simp] theorem db_dbX1_ne_dbB2 : dbX1 ≠ dbB2 := by decide
@[simp] theorem db_dbX1_ne_dbVl : dbX1 ≠ dbVl := by decide
@[simp] theorem db_dbX1_ne_dbD2 : dbX1 ≠ dbD2 := by decide
@[simp] theorem db_dbX1_ne_dbD1 : dbX1 ≠ dbD1 := by decide
@[simp] theorem db_dbX1_ne_dbQ : dbX1 ≠ dbQ := by decide
@[simp] theorem db_dbX1_ne_dbFv : dbX1 ≠ dbFv := by decide
@[simp] theorem db_dbX1_ne_dbV2 : dbX1 ≠ dbV2 := by decide
@[simp] theorem db_dbX1_ne_dbP : dbX1 ≠ dbP := by decide
@[simp] theorem db_dbX1_ne_dbU1 : dbX1 ≠ dbU1 := by decide
@[simp] theorem db_dbX1_ne_dbC1 : dbX1 ≠ dbC1 := by decide
@[simp] theorem db_dbX1_ne_dbU2 : dbX1 ≠ dbU2 := by decide
@[simp] theorem db_dbX1_ne_dbC2 : dbX1 ≠ dbC2 := by decide
@[simp] theorem db_dbX1_ne_dbD3 : dbX1 ≠ dbD3 := by decide
@[simp] theorem db_dbX1_ne_dbVl2 : dbX1 ≠ dbVl2 := by decide
@[simp] theorem db_dbX1_ne_dbX2 : dbX1 ≠ dbX2 := by decide
@[simp] theorem db_dbX1_ne_dbR : dbX1 ≠ dbR := by decide
@[simp] theorem db_dbX1_ne_kFu : dbX1 ≠ kFu := by decide
@[simp] theorem db_kFu_ne_dbX1 : kFu ≠ dbX1 := by decide
@[simp] theorem db_dbX1_ne_kD : dbX1 ≠ kD := by decide
@[simp] theorem db_kD_ne_dbX1 : kD ≠ dbX1 := by decide
@[simp] theorem db_dbX1_ne_lFl : dbX1 ≠ lFl := by decide
@[simp] theorem db_lFl_ne_dbX1 : lFl ≠ dbX1 := by decide
@[simp] theorem db_dbX1_ne_lDh : dbX1 ≠ lDh := by decide
@[simp] theorem db_lDh_ne_dbX1 : lDh ≠ dbX1 := by decide
@[simp] theorem db_dbX1_ne_lDt : dbX1 ≠ lDt := by decide
@[simp] theorem db_lDt_ne_dbX1 : lDt ≠ dbX1 := by decide
@[simp] theorem db_dbX1_ne_lDg : dbX1 ≠ lDg := by decide
@[simp] theorem db_lDg_ne_dbX1 : lDg ≠ dbX1 := by decide
@[simp] theorem db_dbX1_ne_lDi : dbX1 ≠ lDi := by decide
@[simp] theorem db_lDi_ne_dbX1 : lDi ≠ dbX1 := by decide
@[simp] theorem db_dbX1_ne_lRp : dbX1 ≠ lRp := by decide
@[simp] theorem db_lRp_ne_dbX1 : lRp ≠ dbX1 := by decide
@[simp] theorem db_dbX1_ne_lRn : dbX1 ≠ lRn := by decide
@[simp] theorem db_lRn_ne_dbX1 : lRn ≠ dbX1 := by decide
@[simp] theorem db_dbX1_ne_lDir : dbX1 ≠ lDir := by decide
@[simp] theorem db_lDir_ne_dbX1 : lDir ≠ dbX1 := by decide
@[simp] theorem db_dbX1_ne_lFle : dbX1 ≠ lFle := by decide
@[simp] theorem db_lFle_ne_dbX1 : lFle ≠ dbX1 := by decide
@[simp] theorem db_dbX1_ne_lKb : dbX1 ≠ lKb := by decide
@[simp] theorem db_lKb_ne_dbX1 : lKb ≠ dbX1 := by decide
@[simp] theorem db_dbX2_ne_dbL : dbX2 ≠ dbL := by decide
@[simp] theorem db_dbX2_ne_dbF : dbX2 ≠ dbF := by decide
@[simp] theorem db_dbX2_ne_dbV : dbX2 ≠ dbV := by decide
@[simp] theorem db_dbX2_ne_dbT1 : dbX2 ≠ dbT1 := by decide
@[simp] theorem db_dbX2_ne_dbB1 : dbX2 ≠ dbB1 := by decide
@[simp] theorem db_dbX2_ne_dbT2 : dbX2 ≠ dbT2 := by decide
@[simp] theorem db_dbX2_ne_dbB2 : dbX2 ≠ dbB2 := by decide
@[simp] theorem db_dbX2_ne_dbVl : dbX2 ≠ dbVl := by decide
@[simp] theorem db_dbX2_ne_dbD2 : dbX2 ≠ dbD2 := by decide
@[simp] theorem db_dbX2_ne_dbD1 : dbX2 ≠ dbD1 := by decide
@[simp] theorem db_dbX2_ne_dbQ : dbX2 ≠ dbQ := by decide
@[simp] theorem db_dbX2_ne_dbFv : dbX2 ≠ dbFv := by decide
@[simp] theorem db_dbX2_ne_dbV2 : dbX2 ≠ dbV2 := by decide
@[simp] theorem db_dbX2_ne_dbP : dbX2 ≠ dbP := by decide
@[simp] theorem db_dbX2_ne_dbU1 : dbX2 ≠ dbU1 := by decide
@[simp] theorem db_dbX2_ne_dbC1 : dbX2 ≠ dbC1 := by decide
@[simp] theorem db_dbX2_ne_dbU2 : dbX2 ≠ dbU2 := by decide
@[simp] theorem db_dbX2_ne_dbC2 : dbX2 ≠ dbC2 := by decide
@[simp] theorem db_dbX2_ne_dbD3 : dbX2 ≠ dbD3 := by decide
@[simp] theorem db_dbX2_ne_dbVl2 : dbX2 ≠ dbVl2 := by decide
@[simp] theorem db_dbX2_ne_dbX1 : dbX2 ≠ dbX1 := by decide
@[simp] theorem db_dbX2_ne_dbR : dbX2 ≠ dbR := by decide
@[simp] theorem db_dbX2_ne_kFu : dbX2 ≠ kFu := by decide
@[simp] theorem db_kFu_ne_dbX2 : kFu ≠ dbX2 := by decide
@[simp] theorem db_dbX2_ne_kD : dbX2 ≠ kD := by decide
@[simp] theorem db_kD_ne_dbX2 : kD ≠ dbX2 := by decide
@[simp] theorem db_dbX2_ne_lFl : dbX2 ≠ lFl := by decide
@[simp] theorem db_lFl_ne_dbX2 : lFl ≠ dbX2 := by decide
@[simp] theorem db_dbX2_ne_lDh : dbX2 ≠ lDh := by decide
@[simp] theorem db_lDh_ne_dbX2 : lDh ≠ dbX2 := by decide
@[simp] theorem db_dbX2_ne_lDt : dbX2 ≠ lDt := by decide
@[simp] theorem db_lDt_ne_dbX2 : lDt ≠ dbX2 := by decide
@[simp] theorem db_dbX2_ne_lDg : dbX2 ≠ lDg := by decide
@[simp] theorem db_lDg_ne_dbX2 : lDg ≠ dbX2 := by decide
@[simp] theorem db_dbX2_ne_lDi : dbX2 ≠ lDi := by decide
@[simp] theorem db_lDi_ne_dbX2 : lDi ≠ dbX2 := by decide
@[simp] theorem db_dbX2_ne_lRp : dbX2 ≠ lRp := by decide
@[simp] theorem db_lRp_ne_dbX2 : lRp ≠ dbX2 := by decide
@[simp] theorem db_dbX2_ne_lRn : dbX2 ≠ lRn := by decide
@[simp] theorem db_lRn_ne_dbX2 : lRn ≠ dbX2 := by decide
@[simp] theorem db_dbX2_ne_lDir : dbX2 ≠ lDir := by decide
@[simp] theorem db_lDir_ne_dbX2 : lDir ≠ dbX2 := by decide
@[simp] theorem db_dbX2_ne_lFle : dbX2 ≠ lFle := by decide
@[simp] theorem db_lFle_ne_dbX2 : lFle ≠ dbX2 := by decide
@[simp] theorem db_dbX2_ne_lKb : dbX2 ≠ lKb := by decide
@[simp] theorem db_lKb_ne_dbX2 : lKb ≠ dbX2 := by decide
@[simp] theorem db_dbR_ne_dbL : dbR ≠ dbL := by decide
@[simp] theorem db_dbR_ne_dbF : dbR ≠ dbF := by decide
@[simp] theorem db_dbR_ne_dbV : dbR ≠ dbV := by decide
@[simp] theorem db_dbR_ne_dbT1 : dbR ≠ dbT1 := by decide
@[simp] theorem db_dbR_ne_dbB1 : dbR ≠ dbB1 := by decide
@[simp] theorem db_dbR_ne_dbT2 : dbR ≠ dbT2 := by decide
@[simp] theorem db_dbR_ne_dbB2 : dbR ≠ dbB2 := by decide
@[simp] theorem db_dbR_ne_dbVl : dbR ≠ dbVl := by decide
@[simp] theorem db_dbR_ne_dbD2 : dbR ≠ dbD2 := by decide
@[simp] theorem db_dbR_ne_dbD1 : dbR ≠ dbD1 := by decide
@[simp] theorem db_dbR_ne_dbQ : dbR ≠ dbQ := by decide
@[simp] theorem db_dbR_ne_dbFv : dbR ≠ dbFv := by decide
@[simp] theorem db_dbR_ne_dbV2 : dbR ≠ dbV2 := by decide
@[simp] theorem db_dbR_ne_dbP : dbR ≠ dbP := by decide
@[simp] theorem db_dbR_ne_dbU1 : dbR ≠ dbU1 := by decide
@[simp] theorem db_dbR_ne_dbC1 : dbR ≠ dbC1 := by decide
@[simp] theorem db_dbR_ne_dbU2 : dbR ≠ dbU2 := by decide
@[simp] theorem db_dbR_ne_dbC2 : dbR ≠ dbC2 := by decide
@[simp] theorem db_dbR_ne_dbD3 : dbR ≠ dbD3 := by decide
@[simp] theorem db_dbR_ne_dbVl2 : dbR ≠ dbVl2 := by decide
@[simp] theorem db_dbR_ne_dbX1 : dbR ≠ dbX1 := by decide
@[simp] theorem db_dbR_ne_dbX2 : dbR ≠ dbX2 := by decide
@[simp] theorem db_dbR_ne_kFu : dbR ≠ kFu := by decide
@[simp] theorem db_kFu_ne_dbR : kFu ≠ dbR := by decide
@[simp] theorem db_dbR_ne_kD : dbR ≠ kD := by decide
@[simp] theorem db_kD_ne_dbR : kD ≠ dbR := by decide
@[simp] theorem db_dbR_ne_lFl : dbR ≠ lFl := by decide
@[simp] theorem db_lFl_ne_dbR : lFl ≠ dbR := by decide
@[simp] theorem db_dbR_ne_lDh : dbR ≠ lDh := by decide
@[simp] theorem db_lDh_ne_dbR : lDh ≠ dbR := by decide
@[simp] theorem db_dbR_ne_lDt : dbR ≠ lDt := by decide
@[simp] theorem db_lDt_ne_dbR : lDt ≠ dbR := by decide
@[simp] theorem db_dbR_ne_lDg : dbR ≠ lDg := by decide
@[simp] theorem db_lDg_ne_dbR : lDg ≠ dbR := by decide
@[simp] theorem db_dbR_ne_lDi : dbR ≠ lDi := by decide
@[simp] theorem db_lDi_ne_dbR : lDi ≠ dbR := by decide
@[simp] theorem db_dbR_ne_lRp : dbR ≠ lRp := by decide
@[simp] theorem db_lRp_ne_dbR : lRp ≠ dbR := by decide
@[simp] theorem db_dbR_ne_lRn : dbR ≠ lRn := by decide
@[simp] theorem db_lRn_ne_dbR : lRn ≠ dbR := by decide
@[simp] theorem db_dbR_ne_lDir : dbR ≠ lDir := by decide
@[simp] theorem db_lDir_ne_dbR : lDir ≠ dbR := by decide
@[simp] theorem db_dbR_ne_lFle : dbR ≠ lFle := by decide
@[simp] theorem db_lFle_ne_dbR : lFle ≠ dbR := by decide
@[simp] theorem db_dbR_ne_lKb : dbR ≠ lKb := by decide
@[simp] theorem db_lKb_ne_dbR : lKb ≠ dbR := by decide

@[simp] theorem di_diL_ne_diB1 : diL ≠ diB1 := by decide
@[simp] theorem di_diL_ne_diB2 : diL ≠ diB2 := by decide
@[simp] theorem di_diL_ne_diD1 : diL ≠ diD1 := by decide
@[simp] theorem di_diL_ne_diQ : diL ≠ diQ := by decide
@[simp] theorem di_diL_ne_diT1 : diL ≠ diT1 := by decide
@[simp] theorem di_diL_ne_diT2 : diL ≠ diT2 := by decide
@[simp] theorem di_diL_ne_diR : diL ≠ diR := by decide
@[simp] theorem di_diL_ne_kFu : diL ≠ kFu := by decide
@[simp] theorem di_kFu_ne_diL : kFu ≠ diL := by decide
@[simp] theorem di_diL_ne_kD : diL ≠ kD := by decide
@[simp] theorem di_kD_ne_diL : kD ≠ diL := by decide
@[simp] theorem di_diL_ne_lFl : diL ≠ lFl := by decide
@[simp] theorem di_lFl_ne_diL : lFl ≠ diL := by decide
@[simp] theorem di_diL_ne_lDh : diL ≠ lDh := by decide
@[simp] theorem di_lDh_ne_diL : lDh ≠ diL := by decide
@[simp] theorem di_diL_ne_lDt : diL ≠ lDt := by decide
@[simp] theorem di_lDt_ne_diL : lDt ≠ diL := by decide
@[simp] theorem di_diL_ne_lDg : diL ≠ lDg := by decide
@[simp] theorem di_lDg_ne_diL : lDg ≠ diL := by decide
@[simp] theorem di_diL_ne_lDi : diL ≠ lDi := by decide
@[simp] theorem di_lDi_ne_diL : lDi ≠ diL := by decide
@[simp] theorem di_diL_ne_lRp : diL ≠ lRp := by decide
@[simp] theorem di_lRp_ne_diL : lRp ≠ diL := by decide
@[simp] theorem di_diL_ne_lRn : diL ≠ lRn := by decide
@[simp] theorem di_lRn_ne_diL : lRn ≠ diL := by decide
@[simp] theorem di_diL_ne_lDir : diL ≠ lDir := by decide
@[simp] theorem di_lDir_ne_diL : lDir ≠ diL := by decide
@[simp] theorem di_diL_ne_lFle : diL ≠ lFle := by decide
@[simp] theorem di_lFle_ne_diL : lFle ≠ diL := by decide
@[simp] theorem di_diL_ne_lKb : diL ≠ lKb := by decide
@[simp] theorem di_lKb_ne_diL : lKb ≠ diL := by decide
@[simp] theorem di_diB1_ne_diL : diB1 ≠ diL := by decide
@[simp] theorem di_diB1_ne_diB2 : diB1 ≠ diB2 := by decide
@[simp] theorem di_diB1_ne_diD1 : diB1 ≠ diD1 := by decide
@[simp] theorem di_diB1_ne_diQ : diB1 ≠ diQ := by decide
@[simp] theorem di_diB1_ne_diT1 : diB1 ≠ diT1 := by decide
@[simp] theorem di_diB1_ne_diT2 : diB1 ≠ diT2 := by decide
@[simp] theorem di_diB1_ne_diR : diB1 ≠ diR := by decide
@[simp] theorem di_diB1_ne_kFu : diB1 ≠ kFu := by decide
@[simp] theorem di_kFu_ne_diB1 : kFu ≠ diB1 := by decide
@[simp] theorem di_diB1_ne_kD : diB1 ≠ kD := by decide
@[simp] theorem di_kD_ne_diB1 : kD ≠ diB1 := by decide
@[simp] theorem di_diB1_ne_lFl : diB1 ≠ lFl := by decide
@[simp] theorem di_lFl_ne_diB1 : lFl ≠ diB1 := by decide
@[simp] theorem di_diB1_ne_lDh : diB1 ≠ lDh := by decide
@[simp] theorem di_lDh_ne_diB1 : lDh ≠ diB1 := by decide
@[simp] theorem di_diB1_ne_lDt : diB1 ≠ lDt := by decide
@[simp] theorem di_lDt_ne_diB1 : lDt ≠ diB1 := by decide
@[simp] theorem di_diB1_ne_lDg : diB1 ≠ lDg := by decide
@[simp] theorem di_lDg_ne_diB1 : lDg ≠ diB1 := by decide
@[simp] theorem di_diB1_ne_lDi : diB1 ≠ lDi := by decide
@[simp] theorem di_lDi_ne_diB1 : lDi ≠ diB1 := by decide
@[simp] theorem di_diB1_ne_lRp : diB1 ≠ lRp := by decide
@[simp] theorem di_lRp_ne_diB1 : lRp ≠ diB1 := by decide
@[simp] theorem di_diB1_ne_lRn : diB1 ≠ lRn := by decide
@[simp] theorem di_lRn_ne_diB1 : lRn ≠ diB1 := by decide
@[simp] theorem di_diB1_ne_lDir : diB1 ≠ lDir := by decide
@[simp] theorem di_lDir_ne_diB1 : lDir ≠ diB1 := by decide
@[simp] theorem di_diB1_ne_lFle : diB1 ≠ lFle := by decide
@[simp] theorem di_lFle_ne_diB1 : lFle ≠ diB1 := by decide
@[simp] theorem di_diB1_ne_lKb : diB1 ≠ lKb := by decide
@[simp] theorem di_lKb_ne_diB1 : lKb ≠ diB1 := by decide
@[simp] theorem di_diB2_ne_diL : diB2 ≠ diL := by decide
@[simp] theorem di_diB2_ne_diB1 : diB2 ≠ diB1 := by decide
@[simp] theorem di_diB2_ne_diD1 : diB2 ≠ diD1 := by decide
@[simp] theorem di_diB2_ne_diQ : diB2 ≠ diQ := by decide
@[simp] theorem di_diB2_ne_diT1 : diB2 ≠ diT1 := by decide
@[simp] theorem di_diB2_ne_diT2 : diB2 ≠ diT2 := by decide
@[simp] theorem di_diB2_ne_diR : diB2 ≠ diR := by decide
@[simp] theorem di_diB2_ne_kFu : diB2 ≠ kFu := by decide
@[simp] theorem di_kFu_ne_diB2 : kFu ≠ diB2 := by decide
@[simp] theorem di_diB2_ne_kD : diB2 ≠ kD := by decide
@[simp] theorem di_kD_ne_diB2 : kD ≠ diB2 := by decide
@[simp] theorem di_diB2_ne_lFl : diB2 ≠ lFl := by decide
@[simp] theorem di_lFl_ne_diB2 : lFl ≠ diB2 := by decide
@[simp] theorem di_diB2_ne_lDh : diB2 ≠ lDh := by decide
@[simp] theorem di_lDh_ne_diB2 : lDh ≠ diB2 := by decide
@[simp] theorem di_diB2_ne_lDt : diB2 ≠ lDt := by decide
@[simp] theorem di_lDt_ne_diB2 : lDt ≠ diB2 := by decide
@[simp] theorem di_diB2_ne_lDg : diB2 ≠ lDg := by decide
@[simp] theorem di_lDg_ne_diB2 : lDg ≠ diB2 := by decide
@[simp] theorem di_diB2_ne_lDi : diB2 ≠ lDi := by decide
@[simp] theorem di_lDi_ne_diB2 : lDi ≠ diB2 := by decide
@[simp] theorem di_diB2_ne_lRp : diB2 ≠ lRp := by decide
@[simp] theorem di_lRp_ne_diB2 : lRp ≠ diB2 := by decide
@[simp] theorem di_diB2_ne_lRn : diB2 ≠ lRn := by decide
@[simp] theorem di_lRn_ne_diB2 : lRn ≠ diB2 := by decide
@[simp] theorem di_diB2_ne_lDir : diB2 ≠ lDir := by decide
@[simp] theorem di_lDir_ne_diB2 : lDir ≠ diB2 := by decide
@[simp] theorem di_diB2_ne_lFle : diB2 ≠ lFle := by decide
@[simp] theorem di_lFle_ne_diB2 : lFle ≠ diB2 := by decide
@[simp] theorem di_diB2_ne_lKb : diB2 ≠ lKb := by decide
@[simp] theorem di_lKb_ne_diB2 : lKb ≠ diB2 := by decide
@[simp] theorem di_diD1_ne_diL : diD1 ≠ diL := by decide
@[simp] theorem di_diD1_ne_diB1 : diD1 ≠ diB1 := by decide
@[simp] theorem di_diD1_ne_diB2 : diD1 ≠ diB2 := by decide
@[simp] theorem di_diD1_ne_diQ : diD1 ≠ diQ := by decide
@[simp] theorem di_diD1_ne_diT1 : diD1 ≠ diT1 := by decide
@[simp] theorem di_diD1_ne_diT2 : diD1 ≠ diT2 := by decide
@[simp] theorem di_diD1_ne_diR : diD1 ≠ diR := by decide
@[simp] theorem di_diD1_ne_kFu : diD1 ≠ kFu := by decide
@[simp] theorem di_kFu_ne_diD1 : kFu ≠ diD1 := by decide
@[simp] theorem di_diD1_ne_kD : diD1 ≠ kD := by decide
@[simp] theorem di_kD_ne_diD1 : kD ≠ diD1 := by decide
@[simp] theorem di_diD1_ne_lFl : diD1 ≠ lFl := by decide
@[simp] theorem di_lFl_ne_diD1 : lFl ≠ diD1 := by decide
@[simp] theorem di_diD1_ne_lDh : diD1 ≠ lDh := by decide
@[simp] theorem di_lDh_ne_diD1 : lDh ≠ diD1 := by decide
@[simp] theorem di_diD1_ne_lDt : diD1 ≠ lDt := by decide
@[simp] theorem di_lDt_ne_diD1 : lDt ≠ diD1 := by decide
@[simp] theorem di_diD1_ne_lDg : diD1 ≠ lDg := by decide
@[simp] theorem di_lDg_ne_diD1 : lDg ≠ diD1 := by decide
@[simp] theorem di_diD1_ne_lDi : diD1 ≠ lDi := by decide
@[simp] theorem di_lDi_ne_diD1 : lDi ≠ diD1 := by decide
@[simp] theorem di_diD1_ne_lRp : diD1 ≠ lRp := by decide
@[simp] theorem di_lRp_ne_diD1 : lRp ≠ diD1 := by decide
@[simp] theorem di_diD1_ne_lRn : diD1 ≠ lRn := by decide
@[simp] theorem di_lRn_ne_diD1 : lRn ≠ diD1 := by decide
@[simp] theorem di_diD1_ne_lDir : diD1 ≠ lDir := by decide
@[simp] theorem di_lDir_ne_diD1 : lDir ≠ diD1 := by decide
@[simp] theorem di_diD1_ne_lFle : diD1 ≠ lFle := by decide
@[simp] theorem di_lFle_ne_diD1 : lFle ≠ diD1 := by decide
@[simp] theorem di_diD1_ne_lKb : diD1 ≠ lKb := by decide
@[simp] theorem di_lKb_ne_diD1 : lKb ≠ diD1 := by decide
@[simp] theorem di_diQ_ne_diL : diQ ≠ diL := by decide
@[simp] theorem di_diQ_ne_diB1 : diQ ≠ diB1 := by decide
@[simp] theorem di_diQ_ne_diB2 : diQ ≠ diB2 := by decide
@[simp] theorem di_diQ_ne_diD1 : diQ ≠ diD1 := by decide
@[simp] theorem di_diQ_ne_diT1 : diQ ≠ diT1 := by decide
@[simp] theorem di_diQ_ne_diT2 : diQ ≠ diT2 := by decide
@[simp] theorem di_diQ_ne_diR : diQ ≠ diR := by decide
@[simp] theorem di_diQ_ne_kFu : diQ ≠ kFu := by decide
@[simp] theorem di_kFu_ne_diQ : kFu ≠ diQ := by decide
@[simp] theorem di_diQ_ne_kD : diQ ≠ kD := by decide
@[simp] theorem di_kD_ne_diQ : kD ≠ diQ := by decide
@[simp] theorem di_diQ_ne_lFl : diQ ≠ lFl := by decide
@[simp] theorem di_lFl_ne_diQ : lFl ≠ diQ := by decide
@[simp] theorem di_diQ_ne_lDh : diQ ≠ lDh := by decide
@[simp] theorem di_lDh_ne_diQ : lDh ≠ diQ := by decide
@[simp] theorem di_diQ_ne_lDt : diQ ≠ lDt := by decide
@[simp] theorem di_lDt_ne_diQ : lDt ≠ diQ := by decide
@[simp] theorem di_diQ_ne_lDg : diQ ≠ lDg := by decide
@[simp] theorem di_lDg_ne_diQ : lDg ≠ diQ := by decide
@[simp] theorem di_diQ_ne_lDi : diQ ≠ lDi := by decide
@[simp] theorem di_lDi_ne_diQ : lDi ≠ diQ := by decide
@[simp] theorem di_diQ_ne_lRp : diQ ≠ lRp := by decide
@[simp] theorem di_lRp_ne_diQ : lRp ≠ diQ := by decide
@[simp] theorem di_diQ_ne_lRn : diQ ≠ lRn := by decide
@[simp] theorem di_lRn_ne_diQ : lRn ≠ diQ := by decide
@[simp] theorem di_diQ_ne_lDir : diQ ≠ lDir := by decide
@[simp] theorem di_lDir_ne_diQ : lDir ≠ diQ := by decide
@[simp] theorem di_diQ_ne_lFle : diQ ≠ lFle := by decide
@[simp] theorem di_lFle_ne_diQ : lFle ≠ diQ := by decide
@[simp] theorem di_diQ_ne_lKb : diQ ≠ lKb := by decide
@[simp] theorem di_lKb_ne_diQ : lKb ≠ diQ := by decide
@[simp] theorem di_diT1_ne_diL : diT1 ≠ diL := by decide
@[simp] theorem di_diT1_ne_diB1 : diT1 ≠ diB1 := by decide
@[simp] theorem di_diT1_ne_diB2 : diT1 ≠ diB2 := by decide
@[simp] theorem di_diT1_ne_diD1 : diT1 ≠ diD1 := by decide
@[simp] theorem di_diT1_ne_diQ : diT1 ≠ diQ := by decide
@[simp] theorem di_diT1_ne_diT2 : diT1 ≠ diT2 := by decide
@[simp] theorem di_diT1_ne_diR : diT1 ≠ diR := by decide
@[simp] theorem di_diT1_ne_kFu : diT1 ≠ kFu := by decide
@[simp] theorem di_kFu_ne_diT1 : kFu ≠ diT1 := by decide
@[simp] theorem di_diT1_ne_kD : diT1 ≠ kD := by decide
@[simp] theorem di_kD_ne_diT1 : kD ≠ diT1 := by decide
@[simp] theorem di_diT1_ne_lFl : diT1 ≠ lFl := by decide
@[simp] theorem di_lFl_ne_diT1 : lFl ≠ diT1 := by decide
@[simp] theorem di_diT1_ne_lDh : diT1 ≠ lDh := by decide
@[simp] theorem di_lDh_ne_diT1 : lDh ≠ diT1 := by decide
@[simp] theorem di_diT1_ne_lDt : diT1 ≠ lDt := by decide
@[simp] theorem di_lDt_ne_diT1 : lDt ≠ diT1 := by decide
@[simp] theorem di_diT1_ne_lDg : diT1 ≠ lDg := by decide
@[simp] theorem di_lDg_ne_diT1 : lDg ≠ diT1 := by decide
@[simp] theorem di_diT1_ne_lDi : diT1 ≠ lDi := by decide
@[simp] theorem di_lDi_ne_diT1 : lDi ≠ diT1 := by decide
@[simp] theorem di_diT1_ne_lRp : diT1 ≠ lRp := by decide
@[simp] theorem di_lRp_ne_diT1 : lRp ≠ diT1 := by decide
@[simp] theorem di_diT1_ne_lRn : diT1 ≠ lRn := by decide
@[simp] theorem di_lRn_ne_diT1 : lRn ≠ diT1 := by decide
@[simp] theorem di_diT1_ne_lDir : diT1 ≠ lDir := by decide
@[simp] theorem di_lDir_ne_diT1 : lDir ≠ diT1 := by decide
@[simp] theorem di_diT1_ne_lFle : diT1 ≠ lFle := by decide
@[simp] theorem di_lFle_ne_diT1 : lFle ≠ diT1 := by decide
@[simp] theorem di_diT1_ne_lKb : diT1 ≠ lKb := by decide
@[simp] theorem di_lKb_ne_diT1 : lKb ≠ diT1 := by decide
@[simp] theorem di_diT2_ne_diL : diT2 ≠ diL := by decide
@[simp] theorem di_diT2_ne_diB1 : diT2 ≠ diB1 := by decide
@[simp] theorem di_diT2_ne_diB2 : diT2 ≠ diB2 := by decide
@[simp] theorem di_diT2_ne_diD1 : diT2 ≠ diD1 := by decide
@[simp] theorem di_diT2_ne_diQ : diT2 ≠ diQ := by decide
@[simp] theorem di_diT2_ne_diT1 : diT2 ≠ diT1 := by decide
@[simp] theorem di_diT2_ne_diR : diT2 ≠ diR := by decide
@[simp] theorem di_diT2_ne_kFu : diT2 ≠ kFu := by decide
@[simp] theorem di_kFu_ne_diT2 : kFu ≠ diT2 := by decide
@[simp] theorem di_diT2_ne_kD : diT2 ≠ kD := by decide
@[simp] theorem di_kD_ne_diT2 : kD ≠ diT2 := by decide
@[simp] theorem di_diT2_ne_lFl : diT2 ≠ lFl := by decide
@[simp] theorem di_lFl_ne_diT2 : lFl ≠ diT2 := by decide
@[simp] theorem di_diT2_ne_lDh : diT2 ≠ lDh := by decide
@[simp] theorem di_lDh_ne_diT2 : lDh ≠ diT2 := by decide
@[simp] theorem di_diT2_ne_lDt : diT2 ≠ lDt := by decide
@[simp] theorem di_lDt_ne_diT2 : lDt ≠ diT2 := by decide
@[simp] theorem di_diT2_ne_lDg : diT2 ≠ lDg := by decide
@[simp] theorem di_lDg_ne_diT2 : lDg ≠ diT2 := by decide
@[simp] theorem di_diT2_ne_lDi : diT2 ≠ lDi := by decide
@[simp] theorem di_lDi_ne_diT2 : lDi ≠ diT2 := by decide
@[simp] theorem di_diT2_ne_lRp : diT2 ≠ lRp := by decide
@[simp] theorem di_lRp_ne_diT2 : lRp ≠ diT2 := by decide
@[simp] theorem di_diT2_ne_lRn : diT2 ≠ lRn := by decide
@[simp] theorem di_lRn_ne_diT2 : lRn ≠ diT2 := by decide
@[simp] theorem di_diT2_ne_lDir : diT2 ≠ lDir := by decide
@[simp] theorem di_lDir_ne_diT2 : lDir ≠ diT2 := by decide
@[simp] theorem di_diT2_ne_lFle : diT2 ≠ lFle := by decide
@[simp] theorem di_lFle_ne_diT2 : lFle ≠ diT2 := by decide
@[simp] theorem di_diT2_ne_lKb : diT2 ≠ lKb := by decide
@[simp] theorem di_lKb_ne_diT2 : lKb ≠ diT2 := by decide
@[simp] theorem di_diR_ne_diL : diR ≠ diL := by decide
@[simp] theorem di_diR_ne_diB1 : diR ≠ diB1 := by decide
@[simp] theorem di_diR_ne_diB2 : diR ≠ diB2 := by decide
@[simp] theorem di_diR_ne_diD1 : diR ≠ diD1 := by decide
@[simp] theorem di_diR_ne_diQ : diR ≠ diQ := by decide
@[simp] theorem di_diR_ne_diT1 : diR ≠ diT1 := by decide
@[simp] theorem di_diR_ne_diT2 : diR ≠ diT2 := by decide
@[simp] theorem di_diR_ne_kFu : diR ≠ kFu := by decide
@[simp] theorem di_kFu_ne_diR : kFu ≠ diR := by decide
@[simp] theorem di_diR_ne_kD : diR ≠ kD := by decide
@[simp] theorem di_kD_ne_diR : kD ≠ diR := by decide
@[simp] theorem di_diR_ne_lFl : diR ≠ lFl := by decide
@[simp] theorem di_lFl_ne_diR : lFl ≠ diR := by decide
@[simp] theorem di_diR_ne_lDh : diR ≠ lDh := by decide
@[simp] theorem di_lDh_ne_diR : lDh ≠ diR := by decide
@[simp] theorem di_diR_ne_lDt : diR ≠ lDt := by decide
@[simp] theorem di_lDt_ne_diR : lDt ≠ diR := by decide
@[simp] theorem di_diR_ne_lDg : diR ≠ lDg := by decide
@[simp] theorem di_lDg_ne_diR : lDg ≠ diR := by decide
@[simp] theorem di_diR_ne_lDi : diR ≠ lDi := by decide
@[simp] theorem di_lDi_ne_diR : lDi ≠ diR := by decide
@[simp] theorem di_diR_ne_lRp : diR ≠ lRp := by decide
@[simp] theorem di_lRp_ne_diR : lRp ≠ diR := by decide
@[simp] theorem di_diR_ne_lRn : diR ≠ lRn := by decide
@[simp] theorem di_lRn_ne_diR : lRn ≠ diR := by decide
@[simp] theorem di_diR_ne_lDir : diR ≠ lDir := by decide
@[simp] theorem di_lDir_ne_diR : lDir ≠ diR := by decide
@[simp] theorem di_diR_ne_lFle : diR ≠ lFle := by decide
@[simp] theorem di_lFle_ne_diR : lFle ≠ diR := by decide
@[simp] theorem di_diR_ne_lKb : diR ≠ lKb := by decide
@[simp] theorem di_lKb_ne_diR : lKb ≠ diR := by decide

def diParams : List MlS := [kFu, kD, diL, diB1, diB2]
def diLocals : List MlS := [diD1, diQ, diT1, diT2, diR]
def diBody (v : Bool) : ProgHOL 64 := prologue diLocals
  (.seq (.assign .local diD1 (.op .add [(vv kD), (.const 1)])) (.seq (.call (some (some (.local, diQ), none)) fD [(vv kFu), (vv diD1), (vv diB1), (vv diB2)]) (.ite (.cmp .equal (vv diQ) (.const 0)) (.return (.const 0)) (if v then (.ite (vv diL) (.seq (.call (some (some (.local, diT1), none)) fI [(vv kFu), (vv diD1), (vv diB1)]) (.seq (.call (some (some (.local, diT2), none)) fI [(vv kFu), (vv diD1), (vv diB2)]) (.seq (.call (some (some (.local, diR), none)) fD [(vv kFu), (vv diD1), (vv diT1), (vv diT2)]) (.return (vv diR))))) (.return (.const 1))) else (.return (.const 1))))))

def dbParams : List MlS := [kFu, kD, dbL, dbF, dbV, dbT1, dbB1, dbT2, dbB2]
def dbLocals : List MlS := [dbVl, dbD2, dbD1, dbQ, dbFv, dbV2, dbP, dbU1, dbC1, dbU2, dbC2, dbD3, dbVl2, dbX1, dbX2, dbR]
def dbInner : ProgHOL 64 := (.seq (.assign .local dbVl2 (.load .one (vv dbV2))) (.seq (.call (some (some (.local, dbX1), none)) ExQ.fIrr [(vv dbV2), (.const 0), (vv dbVl2), (.const (BitVec.ofNat 64 coreWalkFuel)), (vv dbB1), (.const 0)]) (.seq (.call (some (some (.local, dbX2), none)) ExQ.fIrr [(vv dbV2), (.const 0), (vv dbVl2), (.const (BitVec.ofNat 64 coreWalkFuel)), (vv dbB2), (.const 0)]) (.seq (.call (some (some (.local, dbR), none)) fDi [(vv kFu), (vv kD), (vv dbL), (vv dbX1), (vv dbX2)]) (.return (vv dbR))))))
def dbCont : ProgHOL 64 := (.seq (.call (some (some (.local, dbFv), none)) fInternFVar [(vv dbD2), (vv kD)]) (.seq (.call (some (some (.local, dbV2), none)) ExPre.fAppend [(vv dbV), (vv dbFv)]) (.ite (.cmp .equal (vv dbF) (.const 0)) dbInner (.seq (.call (some (some (.local, dbP), none)) fBPr [(vv dbL), (vv dbB1), (vv dbB2)]) (.ite (.cmp .equal (vv dbP) (.const 0)) dbInner (.seq (.assign .local dbU1 (.load .one (.op .add [(vv dbP), (.const 8)]))) (.seq (.assign .local dbC1 (.load .one (.op .add [(vv dbP), (.const 16)]))) (.seq (.assign .local dbU2 (.load .one (.op .add [(vv dbP), (.const 24)]))) (.seq (.assign .local dbC2 (.load .one (.op .add [(vv dbP), (.const 32)]))) (.seq (.assign .local dbD3 (.op .add [(vv kD), (.const 1)])) (.seq (.call (some (some (.local, dbR), none)) fDb [(vv kFu), (vv dbD3), (vv dbL), (.op .sub [(vv dbF), (.const 1)]), (vv dbV2), (vv dbU1), (vv dbC1), (vv dbU2), (vv dbC2)]) (.return (vv dbR)))))))))))))
def dbBody : ProgHOL 64 := prologue dbLocals (.seq (.assign .local dbVl (.load .one (vv dbV))) (.seq (.call (some (some (.local, dbD2), none)) ExQ.fIrr [(vv dbV), (.const 0), (vv dbVl), (.const (BitVec.ofNat 64 coreWalkFuel)), (vv dbT2), (.const 0)]) (.ite (.cmp .equal (vv dbT1) (vv dbT2)) dbCont (.seq (.call (some (some (.local, dbD1), none)) ExQ.fIrr [(vv dbV), (.const 0), (vv dbVl), (.const (BitVec.ofNat 64 coreWalkFuel)), (vv dbT1), (.const 0)]) (.seq (.call (some (some (.local, dbQ), none)) fD [(vv kFu), (vv kD), (vv dbD1), (vv dbD2)]) (.ite (.cmp .equal (vv dbQ) (.const 0)) (.return (.const 0)) dbCont))))))

section
variable {σ : Type}

theorem di_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hci : C.code.lookup fI = some (pmap kParams, inferE C fIB, .one))
    (hcd : C.code.lookup fD = some (pmap dParams, dE C, .one))
    (hI : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → d' < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (inferE C fIB) s1 ((knot mode C n).infer d' e')
      (PostK (ctxH C H)))
    (hD : ∀ (H : List (BitVec 64)) s1 d' a b, C.H <+: H → d' < 2 ^ 63 → Callee (σ := σ) (ctxH C H) dParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW a, Enc.idxW b] (dE C) s1 ((knot mode C n).defeq d' a b)
      (PostB (ctxH C H)))
    (s : AState) (d : Nat) (hdd : d + 1 < 2 ^ 63) (lam : Bool) (b1 b2 : EIdx) :
    SpecR (σ := σ) (Pre C s (diParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, boolW lam, Enc.idxW b1, Enc.idxW b2]))
      (diBody mode.verifiedChecks) s (defeqBindersInner mode (knot mode C n) lam d b1 b2) (PostB C) := by
  refine specR_prologue (postB_locals C) (Knot.params_none C diLocals diParams _ (by decide) (by decide)) ?_
  unfold defeqBindersInner
  refine specR_assignI diD1 _ (BitVec.ofNat 64 (d + 1)) (by decide)
    (by simp +decide [sev, Env.get, diParams, ctxEnv]; exact word_add1_eq d) ?_
  refine specR_callNIH (C := C) diQ fD dParams [vv kFu, vv diD1, vv diB1, vv diB2] (dE C)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 (d + 1), Enc.idxW b1, Enc.idxW b2] (by decide) rfl (by decide) hcd
    ⟨by simp +decide [Env.get, diParams, ctxEnv], by simp, by simp +decide [Env.get, diParams, ctxEnv],
      by simp +decide [Env.get, diParams, ctxEnv], trivial⟩
    (PostB C) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => hD C.H s (d + 1) b1 b2 (List.prefix_refl _) (by omega) u hu (fun i hi _ => hlk i (by omega)))
    (fun q w s1 H1 hp1 hw => ?_)
  subst hw
  cases q
  · refine specR_ifI _ 1 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    simp only [Bool.not_false, ↓reduceIte]
    exact specR_returnI _ (boolW false) (by simp [boolW]; rfl)
      (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 0 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
    (fun _ => ?_)
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  cases hv : mode.verifiedChecks
  · simp only [Bool.and_false, Bool.false_eq_true, ↓reduceIte]
    exact specR_returnI _ (boolW true) (by simp [boolW]; rfl)
      (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  simp only [Bool.and_true, ↓reduceIte]
  cases lam
  · refine specR_ifI _ 0 (by simp +decide [sev, Env.get, diParams, ctxEnv, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact specR_returnI _ (boolW true) (by simp [boolW]; rfl)
      (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get, diParams, ctxEnv, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
  simp only [↓reduceIte]
  refine Big.specR_callKC (C := ctxH C H1) diT1 fI kParams [vv kFu, vv diD1, vv diB1] (inferE C fIB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 (d + 1), Enc.idxW b1] (by decide) rfl (by decide) hci
    ⟨by simp +decide [Env.get, diParams, ctxEnv], by simp, by simp +decide [Env.get, diParams, ctxEnv], trivial⟩
    (hI H1 s1 (d + 1) b1 hp1 (by omega)) (fun t1 s2 H2 hp2 _ => ?_)
  refine Big.specR_callKC (C := ctxH C H2) diT2 fI kParams [vv kFu, vv diD1, vv diB2] (inferE C fIB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 (d + 1), Enc.idxW b2] (by decide) rfl (by decide) hci
    ⟨by simp +decide [Env.get, diParams, ctxEnv], by simp, by simp +decide [Env.get, diParams, ctxEnv], trivial⟩
    (hI H2 s2 (d + 1) b2 (hp1.trans hp2) (by omega)) (fun t2 s3 H3 hp3 _ => ?_)
  refine specR_congr (m' := (knot mode C n).defeq (d + 1) t1 t2 >>= fun r => pure r) (by simp) ?_
  refine specR_callNIH (C := ctxH C H3) diR fD dParams [vv kFu, vv diD1, vv diT1, vv diT2] (dE C)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 (d + 1), Enc.idxW t1, Enc.idxW t2] (by decide) rfl (by decide) hcd
    ⟨by simp +decide [Env.get, diParams, ctxEnv], by simp, by simp, by simp, trivial⟩
    (PostB (ctxH C H3)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => hD H3 s3 (d + 1) t1 t2 (hp1.trans (hp2.trans hp3)) (by omega) u hu (fun i hi _ => hlk i (by omega)))
    (fun r w s4 H4 hp4 hw => ?_)
  subst hw
  exact specR_returnI _ (boolW r) (by simp)
    (fun t ht => ⟨H4, hp1.trans (hp2.trans (hp3.trans hp4)), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

structure DbCodes (C : Ctx) (v : Bool) : Prop where
  ci : C.code.lookup fI = some (pmap kParams, inferE C fIB, .one)
  d : C.code.lookup fD = some (pmap dParams, dE C, .one)
  irr : C.code.lookup ExQ.fIrr = some (ExQ.irrParams.map (fun p => (p, ShapeHOL.one)), ExQ.irrBody C, .one)
  q : ExQ.CodesQ C
  fv : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one)
  app : C.code.lookup ExPre.fAppend = some (ExPre.appParams.map (fun p => (p, ShapeHOL.one)), ExPre.appBody C, .one)
  bp : C.code.lookup fBPr = some (ExBP.bpParams.map (fun p => (p, ShapeHOL.one)), ExBP.bpBody C, .one)
  di : C.code.lookup fDi = some (diParams.map (fun p => (p, ShapeHOL.one)), diBody v, .one)
  self : C.code.lookup fDb = some (dbParams.map (fun p => (p, ShapeHOL.one)), dbBody, .one)

theorem db_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (hc : DbCodes C mode.verifiedChecks)
    (hI : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → d' < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (inferE C fIB) s1 ((knot mode C n).infer d' e')
      (PostK (ctxH C H)))
    (hD : ∀ (H : List (BitVec 64)) s1 d' a b, C.H <+: H → d' < 2 ^ 63 → Callee (σ := σ) (ctxH C H) dParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW a, Enc.idxW b] (dE C) s1 ((knot mode C n).defeq d' a b)
      (PostB (ctxH C H)))
    (lam : Bool) :
    ∀ fuel (d : Nat) (fvs : List EIdx) (ofv : Nat) (ty1 b1 ty2 b2 : EIdx) (H : List (BitVec 64)) (s : AState),
      C.H <+: H → BlkAt H ofv (fvs.map Enc.idxW) → d + fuel + 1 < 2 ^ 63 →
      SpecR (σ := σ) (Pre (ctxH C H) s (dbParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, boolW lam,
        BitVec.ofNat 64 fuel, cellA C ofv, Enc.idxW ty1, Enc.idxW b1, Enc.idxW ty2, Enc.idxW b2])) dbBody s
        (defeqBinders mode (knot mode C n) lam fuel d fvs.toArray ty1 b1 ty2 b2) (PostB (ctxH C H)) := by
  intro fuel
  induction fuel with
  | zero =>
    intro d fvs ofv ty1 b1 ty2 b2 H s hp hbv hdf
    refine specR_prologue (postB_locals _) (Knot.params_none C dbLocals dbParams _ (by decide) (by decide)) ?_
    rw [defeqBinders]
    refine specR_atEntry fun t0 ht0 => ?_
    have hsm := blk_small0 (C := ctxH C H) (ctxOK_H hok _) ht0.sr hbv
    simp only [List.length_map] at hsm
    obtain ⟨hlo, hlv0⟩ := blkAt_get0 hbv
    refine UD.specR_heapLoadI' (C := ctxH C H) dbVl (vv dbV) ofv (BitVec.ofNat 64 fvs.length)
      (by show H[ofv]? = _; rw [List.getElem?_eq_getElem hlo, hlv0]; simp) (by decide) (by simp +decide [Env.get, dbParams, ctxEnv] <;> rfl) ?_
    simp only [instantiateListFast, List.size_toArray, bind_assoc]
    refine ILP.callE_spec (C := ctxH C H) dbD2 ExQ.fIrr ExQ.irrParams
      [vv dbV, .const 0, vv dbVl, .const (BitVec.ofNat 64 coreWalkFuel), vv dbT2, .const 0] (ExQ.irrBody C)
      [cellA C ofv, BitVec.ofNat 64 0, BitVec.ofNat 64 fvs.length, BitVec.ofNat 64 coreWalkFuel, Enc.idxW ty2,
        BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.irr
      ⟨by simp +decide [Env.get, dbParams, ctxEnv] <;> rfl, rfl, by simp +decide [Env.get, dbParams, ctxEnv], rfl, by simp +decide [Env.get, dbParams, ctxEnv], rfl, trivial⟩
      (ExQ.irr_spec ra (ctxH C H) (ctxOK_H hok H) (codesQ_H hc.q H) fvs.toArray ofv
        (show BlkAt H ofv (fvs.toArray.toList.map Enc.idxW) by simpa using hbv) (by simp; omega) s
        coreWalkFuel 0 fvs.length 0 ty2 CV.coreWalkFuel_lt (by decide) (by omega) (by decide)) (fun dom2 s1 => ?_)
    have hcont : ∀ (H' : List (BitVec 64)) (s' : AState) (Γ : Env), H <+: H' →
        Γ.get dbD2 = some (Enc.idxW dom2) → Γ.get dbV = some (cellA C ofv) → Γ.get kFu = some (BitVec.ofNat 64 n) →
        Γ.get kD = some (BitVec.ofNat 64 d) → Γ.get dbL = some (boolW lam) → Γ.get dbF = some (BitVec.ofNat 64 0) →
        Γ.get dbB1 = some (Enc.idxW b1) → Γ.get dbB2 = some (Enc.idxW b2) →
        SpecR (σ := σ) (Inv (ctxH C H') s' Γ [] (ctxLocals ++ dbLocals)) dbCont s'
          (internFVarE d dom2 >>= fun fv => (instantiateRevRange coreWalkFuel b1 (fvs.toArray.push fv) 0 (fvs.toArray.push fv).size 0 >>= fun x1 => instantiateRevRange coreWalkFuel b2 (fvs.toArray.push fv) 0 (fvs.toArray.push fv).size 0 >>= fun x2 => defeqBindersInner mode (knot mode C n) lam d x1 x2)) (PostB (ctxH C H)) := by
      intro H' s' Γ hpH hD2 hV hFu hDv hL hF hB1 hB2
      unfold dbCont
      refine ILP.specR_internFVarI (C := ctxH C H') ra (ctxOK_H hok H') hc.fv dbFv (vv dbD2) (vv kD) dom2 d (by omega)
        (by decide) (by simp [hD2]) (by simp [hDv]) (fun fv s2 => ?_)
      refine ExPre.specR_callApp (C := ctxH C H') (ctxOK_H hok H') hc.app dbV2 (vv dbV) (vv dbFv) ofv
        (fvs.map Enc.idxW) (Enc.idxW fv) (by decide) (blkAt_mono hbv hpH) (by simp [hV]; rfl) (by simp)
        (fun H2 o2 hp2 hb2 => ?_)
      have hb2' : BlkAt H2 o2 ((fvs ++ [fv]).map Enc.idxW) := by simpa using hb2
      have hinner : ∀ (H3 : List (BitVec 64)) (sI : AState) (Γ3 : Env), H2 <+: H3 →
          Γ3.get dbV2 = some (cellA C o2) → Γ3.get kFu = some (BitVec.ofNat 64 n) → Γ3.get kD = some (BitVec.ofNat 64 d) →
          Γ3.get dbL = some (boolW lam) → Γ3.get dbB1 = some (Enc.idxW b1) → Γ3.get dbB2 = some (Enc.idxW b2) →
          SpecR (σ := σ) (Inv (ctxH C H3) sI Γ3 [] (ctxLocals ++ dbLocals)) dbInner sI
            (instantiateRevRange coreWalkFuel b1 (fvs ++ [fv]).toArray 0 (fvs ++ [fv]).toArray.size 0 >>= fun x1 =>
              instantiateRevRange coreWalkFuel b2 (fvs ++ [fv]).toArray 0 (fvs ++ [fv]).toArray.size 0 >>= fun x2 =>
              defeqBindersInner mode (knot mode C n) lam d x1 x2) (PostB (ctxH C H)) := by
        intro H3 sI Γ3 hp3 hV2 hFu3 hD3 hL3 hB13 hB23
        unfold dbInner
        have hb3 := blkAt_mono hb2' hp3
        refine specR_atEntry fun t3 ht3 => ?_
        have hsm3 := blk_small0 (C := ctxH C H3) (ctxOK_H hok _) ht3.sr hb3
        simp only [List.length_map] at hsm3
        obtain ⟨hlo3, hlv3⟩ := blkAt_get0 hb3
        refine UD.specR_heapLoadI' (C := ctxH C H3) dbVl2 (vv dbV2) o2 (BitVec.ofNat 64 (fvs ++ [fv]).length)
          (by show H3[o2]? = _; rw [List.getElem?_eq_getElem hlo3, hlv3]; simp) (by decide) (by simp [hV2]; rfl) ?_
        refine ILP.callE_spec (C := ctxH C H3) dbX1 ExQ.fIrr ExQ.irrParams
          [vv dbV2, .const 0, vv dbVl2, .const (BitVec.ofNat 64 coreWalkFuel), vv dbB1, .const 0] (ExQ.irrBody C)
          [cellA C o2, BitVec.ofNat 64 0, BitVec.ofNat 64 (fvs ++ [fv]).toArray.size, BitVec.ofNat 64 coreWalkFuel,
            Enc.idxW b1, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.irr
          ⟨by simp [hV2], rfl, by simp, rfl, by simp [hB13], rfl, trivial⟩
          (ExQ.irr_spec ra (ctxH C H3) (ctxOK_H hok H3) (codesQ_H hc.q H3) (fvs ++ [fv]).toArray o2
            (show BlkAt H3 o2 ((fvs ++ [fv]).toArray.toList.map Enc.idxW) by simpa using hb3) (by simp; omega) sI coreWalkFuel 0 (fvs ++ [fv]).toArray.size 0 b1 CV.coreWalkFuel_lt
            (by decide) (by simp; omega) (by decide)) (fun x1 s3 => ?_)
        refine ILP.callE_spec (C := ctxH C H3) dbX2 ExQ.fIrr ExQ.irrParams
          [vv dbV2, .const 0, vv dbVl2, .const (BitVec.ofNat 64 coreWalkFuel), vv dbB2, .const 0] (ExQ.irrBody C)
          [cellA C o2, BitVec.ofNat 64 0, BitVec.ofNat 64 (fvs ++ [fv]).toArray.size, BitVec.ofNat 64 coreWalkFuel,
            Enc.idxW b2, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.irr
          ⟨by simp [hV2], rfl, by simp, rfl, by simp [hB23], rfl, trivial⟩
          (ExQ.irr_spec ra (ctxH C H3) (ctxOK_H hok H3) (codesQ_H hc.q H3) (fvs ++ [fv]).toArray o2
            (show BlkAt H3 o2 ((fvs ++ [fv]).toArray.toList.map Enc.idxW) by simpa using hb3) (by simp; omega) s3 coreWalkFuel 0 (fvs ++ [fv]).toArray.size 0 b2 CV.coreWalkFuel_lt
            (by decide) (by simp; omega) (by decide)) (fun x2 s4 => ?_)
        refine specR_congr (m' := defeqBindersInner mode (knot mode C n) lam d x1 x2 >>= fun r => pure r) (by simp) ?_
        refine specR_callNIH (C := ctxH C H3) dbR fDi diParams [vv kFu, vv kD, vv dbL, vv dbX1, vv dbX2]
          (diBody mode.verifiedChecks) [BitVec.ofNat 64 n, BitVec.ofNat 64 d, boolW lam, Enc.idxW x1, Enc.idxW x2]
          (by decide) rfl (by decide) hc.di ⟨by simp [hFu3], by simp [hD3], by simp [hL3], by simp, by simp, trivial⟩
          (PostB (ctxH C H3)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
          (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu diParams _ rfl hlk)
            (di_spec mode n (ctxH C H3) hc.ci hc.d
              (fun H' s1 d' e' hp' hd' => hI H' s1 d' e' ((hp.trans (hpH.trans (hp2.trans hp3))).trans hp') hd')
              (fun H' s1 d' a b hp' hd' => hD H' s1 d' a b ((hp.trans (hpH.trans (hp2.trans hp3))).trans hp') hd')
              s4 d (by omega) lam x1 x2))
          (fun r w s5 H5 hp5 hw => ?_)
        subst hw
        exact specR_returnI _ (boolW r) (by simp)
          (fun t ht => ⟨H5, hpH.trans (hp2.trans (hp3.trans hp5)), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      refine specR_ifI _ 1 (by simp [sev, hF, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      rw [show fvs.toArray.push fv = (fvs ++ [fv]).toArray by simp]
      exact hinner H2 s2 _ (List.prefix_refl _) (by simp; rfl) (by simp [hFu]) (by simp [hDv]) (by simp [hL]) (by simp [hB1])
        (by simp [hB2])
    unfold defeqDomain
    simp only [instantiateListFast, List.size_toArray, bind_assoc]
    by_cases hty : ty1 = ty2
    · subst hty
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, dbParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [beq_self_eq_true, ↓reduceIte, pure_bind, Bool.not_true, Bool.false_eq_true]
      exact hcont H s1 _ (List.prefix_refl _) (by simp) (by simp +decide [Env.get, dbParams, ctxEnv] <;> rfl) (by simp +decide [Env.get, dbParams, ctxEnv]) (by simp +decide [Env.get, dbParams, ctxEnv]) (by simp +decide [Env.get, dbParams, ctxEnv]) (by simp +decide [Env.get, dbParams, ctxEnv]) (by simp +decide [Env.get, dbParams, ctxEnv])
        (by simp +decide [Env.get, dbParams, ctxEnv])
    have hne : Enc.idxW ty1 ≠ Enc.idxW ty2 := fun e => hty (Enc.idxW_inj e)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, dbParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [show (ty1 == ty2) = false by simpa using hty, Bool.false_eq_true, ↓reduceIte, bind_assoc]
    refine ILP.callE_spec (C := ctxH C H) dbD1 ExQ.fIrr ExQ.irrParams
      [vv dbV, .const 0, vv dbVl, .const (BitVec.ofNat 64 coreWalkFuel), vv dbT1, .const 0] (ExQ.irrBody C)
      [cellA C ofv, BitVec.ofNat 64 0, BitVec.ofNat 64 fvs.length, BitVec.ofNat 64 coreWalkFuel, Enc.idxW ty1,
        BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.irr
      ⟨by simp +decide [Env.get, dbParams, ctxEnv] <;> rfl, rfl, by simp +decide [Env.get, dbParams, ctxEnv], rfl, by simp +decide [Env.get, dbParams, ctxEnv], rfl, trivial⟩
      (ExQ.irr_spec ra (ctxH C H) (ctxOK_H hok H) (codesQ_H hc.q H) fvs.toArray ofv
        (show BlkAt H ofv (fvs.toArray.toList.map Enc.idxW) by simpa using hbv) (by simp; omega) s1
        coreWalkFuel 0 fvs.length 0 ty1 CV.coreWalkFuel_lt (by decide) (by omega) (by decide)) (fun dom1 s2 => ?_)
    refine specR_callNIH (C := ctxH C H) dbQ fD dParams [vv kFu, vv kD, vv dbD1, vv dbD2] (dE C)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW dom1, Enc.idxW dom2] (by decide) rfl (by decide) hc.d
      ⟨by simp +decide [Env.get, dbParams, ctxEnv], by simp +decide [Env.get, dbParams, ctxEnv], by simp, by simp, trivial⟩
      (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => hD H s2 d dom1 dom2 hp (by omega) u hu (fun i hi _ => hlk i (by omega)))
      (fun ok w s3 H3 hp3 hw => ?_)
    subst hw
    cases ok
    · refine specR_ifI _ 1 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      simp only [Bool.not_false, ↓reduceIte]
      exact specR_returnI _ (boolW false) (by simp [boolW]; rfl)
        (fun t ht => ⟨H3, hp3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine specR_ifI _ 0 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact hcont H3 s3 _ hp3 (by simp) (by simp +decide [Env.get, dbParams, ctxEnv] <;> rfl) (by simp +decide [Env.get, dbParams, ctxEnv]) (by simp +decide [Env.get, dbParams, ctxEnv]) (by simp +decide [Env.get, dbParams, ctxEnv]) (by simp +decide [Env.get, dbParams, ctxEnv]) (by simp +decide [Env.get, dbParams, ctxEnv]) (by simp +decide [Env.get, dbParams, ctxEnv])
  | succ fuel ih =>
    intro d fvs ofv ty1 b1 ty2 b2 H s hp hbv hdf
    refine specR_prologue (postB_locals _) (Knot.params_none C dbLocals dbParams _ (by decide) (by decide)) ?_
    rw [defeqBinders]
    refine specR_atEntry fun t0 ht0 => ?_
    have hsm := blk_small0 (C := ctxH C H) (ctxOK_H hok _) ht0.sr hbv
    simp only [List.length_map] at hsm
    obtain ⟨hlo, hlv0⟩ := blkAt_get0 hbv
    refine UD.specR_heapLoadI' (C := ctxH C H) dbVl (vv dbV) ofv (BitVec.ofNat 64 fvs.length)
      (by show H[ofv]? = _; rw [List.getElem?_eq_getElem hlo, hlv0]; simp) (by decide) (by simp +decide [Env.get, dbParams, ctxEnv] <;> rfl) ?_
    simp only [instantiateListFast, List.size_toArray, bind_assoc]
    refine ILP.callE_spec (C := ctxH C H) dbD2 ExQ.fIrr ExQ.irrParams
      [vv dbV, .const 0, vv dbVl, .const (BitVec.ofNat 64 coreWalkFuel), vv dbT2, .const 0] (ExQ.irrBody C)
      [cellA C ofv, BitVec.ofNat 64 0, BitVec.ofNat 64 fvs.length, BitVec.ofNat 64 coreWalkFuel, Enc.idxW ty2,
        BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.irr
      ⟨by simp +decide [Env.get, dbParams, ctxEnv] <;> rfl, rfl, by simp +decide [Env.get, dbParams, ctxEnv], rfl, by simp +decide [Env.get, dbParams, ctxEnv], rfl, trivial⟩
      (ExQ.irr_spec ra (ctxH C H) (ctxOK_H hok H) (codesQ_H hc.q H) fvs.toArray ofv
        (show BlkAt H ofv (fvs.toArray.toList.map Enc.idxW) by simpa using hbv) (by simp; omega) s
        coreWalkFuel 0 fvs.length 0 ty2 CV.coreWalkFuel_lt (by decide) (by omega) (by decide)) (fun dom2 s1 => ?_)
    have hcont : ∀ (H' : List (BitVec 64)) (s' : AState) (Γ : Env), H <+: H' →
        Γ.get dbD2 = some (Enc.idxW dom2) → Γ.get dbV = some (cellA C ofv) → Γ.get kFu = some (BitVec.ofNat 64 n) →
        Γ.get kD = some (BitVec.ofNat 64 d) → Γ.get dbL = some (boolW lam) → Γ.get dbF = some (BitVec.ofNat 64 (fuel + 1)) →
        Γ.get dbB1 = some (Enc.idxW b1) → Γ.get dbB2 = some (Enc.idxW b2) →
        SpecR (σ := σ) (Inv (ctxH C H') s' Γ [] (ctxLocals ++ dbLocals)) dbCont s'
          (internFVarE d dom2 >>= fun fv => (binderPair? lam b1 b2 >>= fun o => match o with
            | some (ty1', body1', ty2', body2') =>
              defeqBinders mode (knot mode C n) lam fuel (d + 1) (fvs.toArray.push fv) ty1' body1' ty2' body2'
            | none => instantiateRevRange coreWalkFuel b1 (fvs.toArray.push fv) 0 (fvs.toArray.push fv).size 0 >>= fun x1 =>
              instantiateRevRange coreWalkFuel b2 (fvs.toArray.push fv) 0 (fvs.toArray.push fv).size 0 >>= fun x2 =>
              defeqBindersInner mode (knot mode C n) lam d x1 x2)) (PostB (ctxH C H)) := by
      intro H' s' Γ hpH hD2 hV hFu hDv hL hF hB1 hB2
      unfold dbCont
      refine ILP.specR_internFVarI (C := ctxH C H') ra (ctxOK_H hok H') hc.fv dbFv (vv dbD2) (vv kD) dom2 d (by omega)
        (by decide) (by simp [hD2]) (by simp [hDv]) (fun fv s2 => ?_)
      refine ExPre.specR_callApp (C := ctxH C H') (ctxOK_H hok H') hc.app dbV2 (vv dbV) (vv dbFv) ofv
        (fvs.map Enc.idxW) (Enc.idxW fv) (by decide) (blkAt_mono hbv hpH) (by simp [hV]; rfl) (by simp)
        (fun H2 o2 hp2 hb2 => ?_)
      have hb2' : BlkAt H2 o2 ((fvs ++ [fv]).map Enc.idxW) := by simpa using hb2
      have hinner : ∀ (H3 : List (BitVec 64)) (sI : AState) (Γ3 : Env), H2 <+: H3 →
          Γ3.get dbV2 = some (cellA C o2) → Γ3.get kFu = some (BitVec.ofNat 64 n) → Γ3.get kD = some (BitVec.ofNat 64 d) →
          Γ3.get dbL = some (boolW lam) → Γ3.get dbB1 = some (Enc.idxW b1) → Γ3.get dbB2 = some (Enc.idxW b2) →
          SpecR (σ := σ) (Inv (ctxH C H3) sI Γ3 [] (ctxLocals ++ dbLocals)) dbInner sI
            (instantiateRevRange coreWalkFuel b1 (fvs ++ [fv]).toArray 0 (fvs ++ [fv]).toArray.size 0 >>= fun x1 =>
              instantiateRevRange coreWalkFuel b2 (fvs ++ [fv]).toArray 0 (fvs ++ [fv]).toArray.size 0 >>= fun x2 =>
              defeqBindersInner mode (knot mode C n) lam d x1 x2) (PostB (ctxH C H)) := by
        intro H3 sI Γ3 hp3 hV2 hFu3 hD3 hL3 hB13 hB23
        unfold dbInner
        have hb3 := blkAt_mono hb2' hp3
        refine specR_atEntry fun t3 ht3 => ?_
        have hsm3 := blk_small0 (C := ctxH C H3) (ctxOK_H hok _) ht3.sr hb3
        simp only [List.length_map] at hsm3
        obtain ⟨hlo3, hlv3⟩ := blkAt_get0 hb3
        refine UD.specR_heapLoadI' (C := ctxH C H3) dbVl2 (vv dbV2) o2 (BitVec.ofNat 64 (fvs ++ [fv]).length)
          (by show H3[o2]? = _; rw [List.getElem?_eq_getElem hlo3, hlv3]; simp) (by decide) (by simp [hV2]; rfl) ?_
        refine ILP.callE_spec (C := ctxH C H3) dbX1 ExQ.fIrr ExQ.irrParams
          [vv dbV2, .const 0, vv dbVl2, .const (BitVec.ofNat 64 coreWalkFuel), vv dbB1, .const 0] (ExQ.irrBody C)
          [cellA C o2, BitVec.ofNat 64 0, BitVec.ofNat 64 (fvs ++ [fv]).toArray.size, BitVec.ofNat 64 coreWalkFuel,
            Enc.idxW b1, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.irr
          ⟨by simp [hV2], rfl, by simp, rfl, by simp [hB13], rfl, trivial⟩
          (ExQ.irr_spec ra (ctxH C H3) (ctxOK_H hok H3) (codesQ_H hc.q H3) (fvs ++ [fv]).toArray o2
            (show BlkAt H3 o2 ((fvs ++ [fv]).toArray.toList.map Enc.idxW) by simpa using hb3) (by simp; omega) sI coreWalkFuel 0 (fvs ++ [fv]).toArray.size 0 b1 CV.coreWalkFuel_lt
            (by decide) (by simp; omega) (by decide)) (fun x1 s3 => ?_)
        refine ILP.callE_spec (C := ctxH C H3) dbX2 ExQ.fIrr ExQ.irrParams
          [vv dbV2, .const 0, vv dbVl2, .const (BitVec.ofNat 64 coreWalkFuel), vv dbB2, .const 0] (ExQ.irrBody C)
          [cellA C o2, BitVec.ofNat 64 0, BitVec.ofNat 64 (fvs ++ [fv]).toArray.size, BitVec.ofNat 64 coreWalkFuel,
            Enc.idxW b2, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.irr
          ⟨by simp [hV2], rfl, by simp, rfl, by simp [hB23], rfl, trivial⟩
          (ExQ.irr_spec ra (ctxH C H3) (ctxOK_H hok H3) (codesQ_H hc.q H3) (fvs ++ [fv]).toArray o2
            (show BlkAt H3 o2 ((fvs ++ [fv]).toArray.toList.map Enc.idxW) by simpa using hb3) (by simp; omega) s3 coreWalkFuel 0 (fvs ++ [fv]).toArray.size 0 b2 CV.coreWalkFuel_lt
            (by decide) (by simp; omega) (by decide)) (fun x2 s4 => ?_)
        refine specR_congr (m' := defeqBindersInner mode (knot mode C n) lam d x1 x2 >>= fun r => pure r) (by simp) ?_
        refine specR_callNIH (C := ctxH C H3) dbR fDi diParams [vv kFu, vv kD, vv dbL, vv dbX1, vv dbX2]
          (diBody mode.verifiedChecks) [BitVec.ofNat 64 n, BitVec.ofNat 64 d, boolW lam, Enc.idxW x1, Enc.idxW x2]
          (by decide) rfl (by decide) hc.di ⟨by simp [hFu3], by simp [hD3], by simp [hL3], by simp, by simp, trivial⟩
          (PostB (ctxH C H3)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
          (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu diParams _ rfl hlk)
            (di_spec mode n (ctxH C H3) hc.ci hc.d
              (fun H' s1 d' e' hp' hd' => hI H' s1 d' e' ((hp.trans (hpH.trans (hp2.trans hp3))).trans hp') hd')
              (fun H' s1 d' a b hp' hd' => hD H' s1 d' a b ((hp.trans (hpH.trans (hp2.trans hp3))).trans hp') hd')
              s4 d (by omega) lam x1 x2))
          (fun r w s5 H5 hp5 hw => ?_)
        subst hw
        exact specR_returnI _ (boolW r) (by simp)
          (fun t ht => ⟨H5, hpH.trans (hp2.trans (hp3.trans hp5)), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      have hne0 := ofNat_succ_ne fuel (by omega)
      refine specR_ifI _ 0 (by simp [sev, hF, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne0)
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_callNIH (C := ctxH C H2) dbP fBPr ExBP.bpParams [vv dbL, vv dbB1, vv dbB2] (ExBP.bpBody C)
        [if lam then 1 else 0, Enc.idxW b1, Enc.idxW b2] (by decide) rfl (by decide) hc.bp
        ⟨by simp [hL, boolW], by simp [hB1], by simp [hB2], trivial⟩
        (ExBP.PostBP (ctxH C H2))
        (fun o w _ H' => (o = none → w = 0) ∧ ∀ q, o = some q → ∃ ob, w = cellA C ob ∧
          BlkAt H' ob [Enc.idxW q.1, Enc.idxW q.2.1, Enc.idxW q.2.2.1, Enc.idxW q.2.2.2])
        (fun o w s' st ⟨H', hp', hsr, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ExBP.bpParams _ rfl hlk)
          (ExBP.bp_spec C hok H2 s2 lam b1 b2))
        (fun o w s3 H3 hp3 ⟨h1, h2⟩ => ?_)
      rcases o with _ | ⟨ty1', body1', ty2', body2'⟩
      · have hw0 := h1 rfl; subst hw0
        refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
          (fun h => absurd h (by decide))
        dsimp only
        rw [show fvs.toArray.push fv = (fvs ++ [fv]).toArray by simp]
        refine hinner H3 s3 _ hp3 ?_ ?_ ?_ ?_ ?_ ?_ <;> (try simp [hFu, hDv, hL, hB1, hB2]) <;> rfl
      obtain ⟨ob, hw, hbq⟩ := h2 _ rfl
      subst hw
      refine specR_atEntry fun t4 ht4 => ?_
      have hobN : ob < C.HN := by
        obtain ⟨H0, hp0, ha0⟩ := ht4.sr.heap
        have hl := blkAt_lt hbq
        have := ha0.len; have := hp0.length_le
        simp only [ctxH] at *; omega
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ExSP.cellA_ne0 C hok ob hobN)
        (fun h => absurd rfl h) (fun _ => ?_)
      dsimp only
      have hq1 : (ctxH C H3).H[ob + 1 + 0]? = some (Enc.idxW ty1') := hbq.2 0 (by simp)
      have hq2 : (ctxH C H3).H[ob + 1 + 1]? = some (Enc.idxW body1') := hbq.2 1 (by simp)
      have hq3 : (ctxH C H3).H[ob + 1 + 2]? = some (Enc.idxW ty2') := hbq.2 2 (by simp)
      have hq4 : (ctxH C H3).H[ob + 1 + 3]? = some (Enc.idxW body2') := hbq.2 3 (by simp)
      refine UD.specR_heapLoadI' (C := ctxH C H3) dbU1 (.op .add [vv dbP, .const 8]) (ob + 1 + 0) _ hq1 (by decide)
        (by simp [sev]; exact cellA_add8 C ob) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H3) dbC1 (.op .add [vv dbP, .const 16]) (ob + 1 + 1) _ hq2 (by decide)
        (by simp [sev]; rw [show (16#64 : BitVec 64) = BitVec.ofNat 64 (8 * 2) from rfl]; exact ExPre.cellA_off C _ 2) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H3) dbU2 (.op .add [vv dbP, .const 24]) (ob + 1 + 2) _ hq3 (by decide)
        (by simp [sev]; rw [show (24#64 : BitVec 64) = BitVec.ofNat 64 (8 * 3) from rfl]; exact ExPre.cellA_off C _ 3) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H3) dbC2 (.op .add [vv dbP, .const 32]) (ob + 1 + 3) _ hq4 (by decide)
        (by simp [sev]; rw [show (32#64 : BitVec 64) = BitVec.ofNat 64 (8 * 4) from rfl]; exact ExPre.cellA_off C _ 4) ?_
      refine specR_assignI dbD3 _ (BitVec.ofNat 64 (d + 1)) (by decide)
        (by simp [sev, hDv]; exact word_add1_eq d) ?_
      rw [show fvs.toArray.push fv = (fvs ++ [fv]).toArray by simp]
      refine specR_congr (m' := defeqBinders mode (knot mode C n) lam fuel (d + 1) (fvs ++ [fv]).toArray ty1' body1'
        ty2' body2' >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H3) dbR fDb dbParams
        [vv kFu, vv dbD3, vv dbL, .op .sub [vv dbF, .const 1], vv dbV2, vv dbU1, vv dbC1, vv dbU2, vv dbC2] dbBody
        [BitVec.ofNat 64 n, BitVec.ofNat 64 (d + 1), boolW lam, BitVec.ofNat 64 fuel, cellA C o2, Enc.idxW ty1',
          Enc.idxW body1', Enc.idxW ty2', Enc.idxW body2'] (by decide) rfl (by decide) hc.self
        ⟨by simp [hFu], by simp, by simp [hL], by simp [sev, hF]; exact Ex.ofNat_succ_sub_one _, by simp <;> rfl,
          by simp, by simp, by simp, by simp, trivial⟩
        (PostB (ctxH C H3)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu dbParams _ rfl hlk)
          (ih (d + 1) (fvs ++ [fv]) o2 ty1' body1' ty2' body2' H3 s3 (hp.trans (hpH.trans (hp2.trans hp3)))
            (blkAt_mono hb2' hp3) (by omega)))
        (fun r w s5 H5 hp5 hw => ?_)
      subst hw
      exact specR_returnI _ (boolW r) (by simp)
        (fun t ht => ⟨H5, hpH.trans (hp2.trans (hp3.trans hp5)), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    unfold defeqDomain
    simp only [instantiateListFast, List.size_toArray, bind_assoc]
    by_cases hty : ty1 = ty2
    · subst hty
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, dbParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [beq_self_eq_true, ↓reduceIte, pure_bind, Bool.not_true, Bool.false_eq_true]
      exact hcont H s1 _ (List.prefix_refl _) (by simp) (by simp +decide [Env.get, dbParams, ctxEnv] <;> rfl) (by simp +decide [Env.get, dbParams, ctxEnv]) (by simp +decide [Env.get, dbParams, ctxEnv]) (by simp +decide [Env.get, dbParams, ctxEnv]) (by simp +decide [Env.get, dbParams, ctxEnv]) (by simp +decide [Env.get, dbParams, ctxEnv])
        (by simp +decide [Env.get, dbParams, ctxEnv])
    have hne : Enc.idxW ty1 ≠ Enc.idxW ty2 := fun e => hty (Enc.idxW_inj e)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, dbParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [show (ty1 == ty2) = false by simpa using hty, Bool.false_eq_true, ↓reduceIte, bind_assoc]
    refine ILP.callE_spec (C := ctxH C H) dbD1 ExQ.fIrr ExQ.irrParams
      [vv dbV, .const 0, vv dbVl, .const (BitVec.ofNat 64 coreWalkFuel), vv dbT1, .const 0] (ExQ.irrBody C)
      [cellA C ofv, BitVec.ofNat 64 0, BitVec.ofNat 64 fvs.length, BitVec.ofNat 64 coreWalkFuel, Enc.idxW ty1,
        BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.irr
      ⟨by simp +decide [Env.get, dbParams, ctxEnv] <;> rfl, rfl, by simp +decide [Env.get, dbParams, ctxEnv], rfl, by simp +decide [Env.get, dbParams, ctxEnv], rfl, trivial⟩
      (ExQ.irr_spec ra (ctxH C H) (ctxOK_H hok H) (codesQ_H hc.q H) fvs.toArray ofv
        (show BlkAt H ofv (fvs.toArray.toList.map Enc.idxW) by simpa using hbv) (by simp; omega) s1
        coreWalkFuel 0 fvs.length 0 ty1 CV.coreWalkFuel_lt (by decide) (by omega) (by decide)) (fun dom1 s2 => ?_)
    refine specR_callNIH (C := ctxH C H) dbQ fD dParams [vv kFu, vv kD, vv dbD1, vv dbD2] (dE C)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW dom1, Enc.idxW dom2] (by decide) rfl (by decide) hc.d
      ⟨by simp +decide [Env.get, dbParams, ctxEnv], by simp +decide [Env.get, dbParams, ctxEnv], by simp, by simp, trivial⟩
      (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => hD H s2 d dom1 dom2 hp (by omega) u hu (fun i hi _ => hlk i (by omega)))
      (fun ok w s3 H3 hp3 hw => ?_)
    subst hw
    cases ok
    · refine specR_ifI _ 1 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      simp only [Bool.not_false, ↓reduceIte]
      exact specR_returnI _ (boolW false) (by simp [boolW]; rfl)
        (fun t ht => ⟨H3, hp3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine specR_ifI _ 0 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact hcont H3 s3 _ hp3 (by simp) (by simp +decide [Env.get, dbParams, ctxEnv] <;> rfl) (by simp +decide [Env.get, dbParams, ctxEnv]) (by simp +decide [Env.get, dbParams, ctxEnv]) (by simp +decide [Env.get, dbParams, ctxEnv]) (by simp +decide [Env.get, dbParams, ctxEnv]) (by simp +decide [Env.get, dbParams, ctxEnv]) (by simp +decide [Env.get, dbParams, ctxEnv])

end

end ConPanqueque.T.WC
