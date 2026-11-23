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

section
variable {σ : Type}

theorem di_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hci : C.code.lookup fI = some (pmap kParams, inferE C fIB, .one))
    (hcd : C.code.lookup fD = some (pmap dParams, dE C, .one))
    (hI : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (inferE C fIB) s1 ((knot mode C n).infer d' e')
      (PostK (ctxH C H)))
    (hD : ∀ (H : List (BitVec 64)) s1 d' a b, C.H <+: H → Callee (σ := σ) (ctxH C H) dParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW a, Enc.idxW b] (dE C) s1 ((knot mode C n).defeq d' a b)
      (PostB (ctxH C H)))
    (s : AState) (d : Nat) (lam : Bool) (b1 b2 : EIdx) :
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
    (fun u hu _ hlk => hD C.H s (d + 1) b1 b2 (List.prefix_refl _) u hu (fun i hi _ => hlk i (by omega)))
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
    (hI H1 s1 (d + 1) b1 hp1) (fun t1 s2 H2 hp2 _ => ?_)
  refine Big.specR_callKC (C := ctxH C H2) diT2 fI kParams [vv kFu, vv diD1, vv diB2] (inferE C fIB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 (d + 1), Enc.idxW b2] (by decide) rfl (by decide) hci
    ⟨by simp +decide [Env.get, diParams, ctxEnv], by simp, by simp +decide [Env.get, diParams, ctxEnv], trivial⟩
    (hI H2 s2 (d + 1) b2 (hp1.trans hp2)) (fun t2 s3 H3 hp3 _ => ?_)
  refine specR_congr (m' := (knot mode C n).defeq (d + 1) t1 t2 >>= fun r => pure r) (by simp) ?_
  refine specR_callNIH (C := ctxH C H3) diR fD dParams [vv kFu, vv diD1, vv diT1, vv diT2] (dE C)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 (d + 1), Enc.idxW t1, Enc.idxW t2] (by decide) rfl (by decide) hcd
    ⟨by simp +decide [Env.get, diParams, ctxEnv], by simp, by simp, by simp, trivial⟩
    (PostB (ctxH C H3)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => hD H3 s3 (d + 1) t1 t2 (hp1.trans (hp2.trans hp3)) u hu (fun i hi _ => hlk i (by omega)))
    (fun r w s4 H4 hp4 hw => ?_)
  subst hw
  exact specR_returnI _ (boolW r) (by simp)
    (fun t ht => ⟨H4, hp1.trans (hp2.trans (hp3.trans hp4)), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
