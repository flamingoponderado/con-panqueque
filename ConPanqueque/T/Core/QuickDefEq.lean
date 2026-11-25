import ConPanqueque.T.Core.LitEq
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `quickDefEq`

The easy cases: the same handle; two sorts (`lvlEq?`, a callee); two literals (row equality); two ∀s or two λs
(the binder-telescope congruence, from an empty variable block; a depth of `2 ^ 61` or more halts). Any
other pair is "not an easy case". Answers `obW`.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def qdA := ofString "qdn_a"
def qdB := ofString "qdn_b"
def qdU := ofString "qdn_u"
def qdV := ofString "qdn_v"
def qdQ := ofString "qdn_q"
def qdT1 := ofString "qdn_t1"
def qdB1 := ofString "qdn_b1"
def qdT2 := ofString "qdn_t2"
def qdB2 := ofString "qdn_b2"
def qdE := ofString "qdn_e"
def qdR := ofString "qdn_r"
def fQd := ofString "quickDefEq"

@[simp] theorem qd_qdA_ne_qdB : qdA ≠ qdB := by decide
@[simp] theorem qd_qdA_ne_qdU : qdA ≠ qdU := by decide
@[simp] theorem qd_qdA_ne_qdV : qdA ≠ qdV := by decide
@[simp] theorem qd_qdA_ne_qdQ : qdA ≠ qdQ := by decide
@[simp] theorem qd_qdA_ne_qdT1 : qdA ≠ qdT1 := by decide
@[simp] theorem qd_qdA_ne_qdB1 : qdA ≠ qdB1 := by decide
@[simp] theorem qd_qdA_ne_qdT2 : qdA ≠ qdT2 := by decide
@[simp] theorem qd_qdA_ne_qdB2 : qdA ≠ qdB2 := by decide
@[simp] theorem qd_qdA_ne_qdE : qdA ≠ qdE := by decide
@[simp] theorem qd_qdA_ne_qdR : qdA ≠ qdR := by decide
@[simp] theorem qd_qdA_ne_kFu : qdA ≠ kFu := by decide
@[simp] theorem qd_kFu_ne_qdA : kFu ≠ qdA := by decide
@[simp] theorem qd_qdA_ne_kD : qdA ≠ kD := by decide
@[simp] theorem qd_kD_ne_qdA : kD ≠ qdA := by decide
@[simp] theorem qd_qdA_ne_lFl : qdA ≠ lFl := by decide
@[simp] theorem qd_lFl_ne_qdA : lFl ≠ qdA := by decide
@[simp] theorem qd_qdA_ne_lDh : qdA ≠ lDh := by decide
@[simp] theorem qd_lDh_ne_qdA : lDh ≠ qdA := by decide
@[simp] theorem qd_qdA_ne_lDt : qdA ≠ lDt := by decide
@[simp] theorem qd_lDt_ne_qdA : lDt ≠ qdA := by decide
@[simp] theorem qd_qdA_ne_lDg : qdA ≠ lDg := by decide
@[simp] theorem qd_lDg_ne_qdA : lDg ≠ qdA := by decide
@[simp] theorem qd_qdA_ne_lDi : qdA ≠ lDi := by decide
@[simp] theorem qd_lDi_ne_qdA : lDi ≠ qdA := by decide
@[simp] theorem qd_qdA_ne_lRp : qdA ≠ lRp := by decide
@[simp] theorem qd_lRp_ne_qdA : lRp ≠ qdA := by decide
@[simp] theorem qd_qdA_ne_lRn : qdA ≠ lRn := by decide
@[simp] theorem qd_lRn_ne_qdA : lRn ≠ qdA := by decide
@[simp] theorem qd_qdA_ne_lDir : qdA ≠ lDir := by decide
@[simp] theorem qd_lDir_ne_qdA : lDir ≠ qdA := by decide
@[simp] theorem qd_qdA_ne_lFle : qdA ≠ lFle := by decide
@[simp] theorem qd_lFle_ne_qdA : lFle ≠ qdA := by decide
@[simp] theorem qd_qdA_ne_lKb : qdA ≠ lKb := by decide
@[simp] theorem qd_lKb_ne_qdA : lKb ≠ qdA := by decide
@[simp] theorem qd_qdB_ne_qdA : qdB ≠ qdA := by decide
@[simp] theorem qd_qdB_ne_qdU : qdB ≠ qdU := by decide
@[simp] theorem qd_qdB_ne_qdV : qdB ≠ qdV := by decide
@[simp] theorem qd_qdB_ne_qdQ : qdB ≠ qdQ := by decide
@[simp] theorem qd_qdB_ne_qdT1 : qdB ≠ qdT1 := by decide
@[simp] theorem qd_qdB_ne_qdB1 : qdB ≠ qdB1 := by decide
@[simp] theorem qd_qdB_ne_qdT2 : qdB ≠ qdT2 := by decide
@[simp] theorem qd_qdB_ne_qdB2 : qdB ≠ qdB2 := by decide
@[simp] theorem qd_qdB_ne_qdE : qdB ≠ qdE := by decide
@[simp] theorem qd_qdB_ne_qdR : qdB ≠ qdR := by decide
@[simp] theorem qd_qdB_ne_kFu : qdB ≠ kFu := by decide
@[simp] theorem qd_kFu_ne_qdB : kFu ≠ qdB := by decide
@[simp] theorem qd_qdB_ne_kD : qdB ≠ kD := by decide
@[simp] theorem qd_kD_ne_qdB : kD ≠ qdB := by decide
@[simp] theorem qd_qdB_ne_lFl : qdB ≠ lFl := by decide
@[simp] theorem qd_lFl_ne_qdB : lFl ≠ qdB := by decide
@[simp] theorem qd_qdB_ne_lDh : qdB ≠ lDh := by decide
@[simp] theorem qd_lDh_ne_qdB : lDh ≠ qdB := by decide
@[simp] theorem qd_qdB_ne_lDt : qdB ≠ lDt := by decide
@[simp] theorem qd_lDt_ne_qdB : lDt ≠ qdB := by decide
@[simp] theorem qd_qdB_ne_lDg : qdB ≠ lDg := by decide
@[simp] theorem qd_lDg_ne_qdB : lDg ≠ qdB := by decide
@[simp] theorem qd_qdB_ne_lDi : qdB ≠ lDi := by decide
@[simp] theorem qd_lDi_ne_qdB : lDi ≠ qdB := by decide
@[simp] theorem qd_qdB_ne_lRp : qdB ≠ lRp := by decide
@[simp] theorem qd_lRp_ne_qdB : lRp ≠ qdB := by decide
@[simp] theorem qd_qdB_ne_lRn : qdB ≠ lRn := by decide
@[simp] theorem qd_lRn_ne_qdB : lRn ≠ qdB := by decide
@[simp] theorem qd_qdB_ne_lDir : qdB ≠ lDir := by decide
@[simp] theorem qd_lDir_ne_qdB : lDir ≠ qdB := by decide
@[simp] theorem qd_qdB_ne_lFle : qdB ≠ lFle := by decide
@[simp] theorem qd_lFle_ne_qdB : lFle ≠ qdB := by decide
@[simp] theorem qd_qdB_ne_lKb : qdB ≠ lKb := by decide
@[simp] theorem qd_lKb_ne_qdB : lKb ≠ qdB := by decide
@[simp] theorem qd_qdU_ne_qdA : qdU ≠ qdA := by decide
@[simp] theorem qd_qdU_ne_qdB : qdU ≠ qdB := by decide
@[simp] theorem qd_qdU_ne_qdV : qdU ≠ qdV := by decide
@[simp] theorem qd_qdU_ne_qdQ : qdU ≠ qdQ := by decide
@[simp] theorem qd_qdU_ne_qdT1 : qdU ≠ qdT1 := by decide
@[simp] theorem qd_qdU_ne_qdB1 : qdU ≠ qdB1 := by decide
@[simp] theorem qd_qdU_ne_qdT2 : qdU ≠ qdT2 := by decide
@[simp] theorem qd_qdU_ne_qdB2 : qdU ≠ qdB2 := by decide
@[simp] theorem qd_qdU_ne_qdE : qdU ≠ qdE := by decide
@[simp] theorem qd_qdU_ne_qdR : qdU ≠ qdR := by decide
@[simp] theorem qd_qdU_ne_kFu : qdU ≠ kFu := by decide
@[simp] theorem qd_kFu_ne_qdU : kFu ≠ qdU := by decide
@[simp] theorem qd_qdU_ne_kD : qdU ≠ kD := by decide
@[simp] theorem qd_kD_ne_qdU : kD ≠ qdU := by decide
@[simp] theorem qd_qdU_ne_lFl : qdU ≠ lFl := by decide
@[simp] theorem qd_lFl_ne_qdU : lFl ≠ qdU := by decide
@[simp] theorem qd_qdU_ne_lDh : qdU ≠ lDh := by decide
@[simp] theorem qd_lDh_ne_qdU : lDh ≠ qdU := by decide
@[simp] theorem qd_qdU_ne_lDt : qdU ≠ lDt := by decide
@[simp] theorem qd_lDt_ne_qdU : lDt ≠ qdU := by decide
@[simp] theorem qd_qdU_ne_lDg : qdU ≠ lDg := by decide
@[simp] theorem qd_lDg_ne_qdU : lDg ≠ qdU := by decide
@[simp] theorem qd_qdU_ne_lDi : qdU ≠ lDi := by decide
@[simp] theorem qd_lDi_ne_qdU : lDi ≠ qdU := by decide
@[simp] theorem qd_qdU_ne_lRp : qdU ≠ lRp := by decide
@[simp] theorem qd_lRp_ne_qdU : lRp ≠ qdU := by decide
@[simp] theorem qd_qdU_ne_lRn : qdU ≠ lRn := by decide
@[simp] theorem qd_lRn_ne_qdU : lRn ≠ qdU := by decide
@[simp] theorem qd_qdU_ne_lDir : qdU ≠ lDir := by decide
@[simp] theorem qd_lDir_ne_qdU : lDir ≠ qdU := by decide
@[simp] theorem qd_qdU_ne_lFle : qdU ≠ lFle := by decide
@[simp] theorem qd_lFle_ne_qdU : lFle ≠ qdU := by decide
@[simp] theorem qd_qdU_ne_lKb : qdU ≠ lKb := by decide
@[simp] theorem qd_lKb_ne_qdU : lKb ≠ qdU := by decide
@[simp] theorem qd_qdV_ne_qdA : qdV ≠ qdA := by decide
@[simp] theorem qd_qdV_ne_qdB : qdV ≠ qdB := by decide
@[simp] theorem qd_qdV_ne_qdU : qdV ≠ qdU := by decide
@[simp] theorem qd_qdV_ne_qdQ : qdV ≠ qdQ := by decide
@[simp] theorem qd_qdV_ne_qdT1 : qdV ≠ qdT1 := by decide
@[simp] theorem qd_qdV_ne_qdB1 : qdV ≠ qdB1 := by decide
@[simp] theorem qd_qdV_ne_qdT2 : qdV ≠ qdT2 := by decide
@[simp] theorem qd_qdV_ne_qdB2 : qdV ≠ qdB2 := by decide
@[simp] theorem qd_qdV_ne_qdE : qdV ≠ qdE := by decide
@[simp] theorem qd_qdV_ne_qdR : qdV ≠ qdR := by decide
@[simp] theorem qd_qdV_ne_kFu : qdV ≠ kFu := by decide
@[simp] theorem qd_kFu_ne_qdV : kFu ≠ qdV := by decide
@[simp] theorem qd_qdV_ne_kD : qdV ≠ kD := by decide
@[simp] theorem qd_kD_ne_qdV : kD ≠ qdV := by decide
@[simp] theorem qd_qdV_ne_lFl : qdV ≠ lFl := by decide
@[simp] theorem qd_lFl_ne_qdV : lFl ≠ qdV := by decide
@[simp] theorem qd_qdV_ne_lDh : qdV ≠ lDh := by decide
@[simp] theorem qd_lDh_ne_qdV : lDh ≠ qdV := by decide
@[simp] theorem qd_qdV_ne_lDt : qdV ≠ lDt := by decide
@[simp] theorem qd_lDt_ne_qdV : lDt ≠ qdV := by decide
@[simp] theorem qd_qdV_ne_lDg : qdV ≠ lDg := by decide
@[simp] theorem qd_lDg_ne_qdV : lDg ≠ qdV := by decide
@[simp] theorem qd_qdV_ne_lDi : qdV ≠ lDi := by decide
@[simp] theorem qd_lDi_ne_qdV : lDi ≠ qdV := by decide
@[simp] theorem qd_qdV_ne_lRp : qdV ≠ lRp := by decide
@[simp] theorem qd_lRp_ne_qdV : lRp ≠ qdV := by decide
@[simp] theorem qd_qdV_ne_lRn : qdV ≠ lRn := by decide
@[simp] theorem qd_lRn_ne_qdV : lRn ≠ qdV := by decide
@[simp] theorem qd_qdV_ne_lDir : qdV ≠ lDir := by decide
@[simp] theorem qd_lDir_ne_qdV : lDir ≠ qdV := by decide
@[simp] theorem qd_qdV_ne_lFle : qdV ≠ lFle := by decide
@[simp] theorem qd_lFle_ne_qdV : lFle ≠ qdV := by decide
@[simp] theorem qd_qdV_ne_lKb : qdV ≠ lKb := by decide
@[simp] theorem qd_lKb_ne_qdV : lKb ≠ qdV := by decide
@[simp] theorem qd_qdQ_ne_qdA : qdQ ≠ qdA := by decide
@[simp] theorem qd_qdQ_ne_qdB : qdQ ≠ qdB := by decide
@[simp] theorem qd_qdQ_ne_qdU : qdQ ≠ qdU := by decide
@[simp] theorem qd_qdQ_ne_qdV : qdQ ≠ qdV := by decide
@[simp] theorem qd_qdQ_ne_qdT1 : qdQ ≠ qdT1 := by decide
@[simp] theorem qd_qdQ_ne_qdB1 : qdQ ≠ qdB1 := by decide
@[simp] theorem qd_qdQ_ne_qdT2 : qdQ ≠ qdT2 := by decide
@[simp] theorem qd_qdQ_ne_qdB2 : qdQ ≠ qdB2 := by decide
@[simp] theorem qd_qdQ_ne_qdE : qdQ ≠ qdE := by decide
@[simp] theorem qd_qdQ_ne_qdR : qdQ ≠ qdR := by decide
@[simp] theorem qd_qdQ_ne_kFu : qdQ ≠ kFu := by decide
@[simp] theorem qd_kFu_ne_qdQ : kFu ≠ qdQ := by decide
@[simp] theorem qd_qdQ_ne_kD : qdQ ≠ kD := by decide
@[simp] theorem qd_kD_ne_qdQ : kD ≠ qdQ := by decide
@[simp] theorem qd_qdQ_ne_lFl : qdQ ≠ lFl := by decide
@[simp] theorem qd_lFl_ne_qdQ : lFl ≠ qdQ := by decide
@[simp] theorem qd_qdQ_ne_lDh : qdQ ≠ lDh := by decide
@[simp] theorem qd_lDh_ne_qdQ : lDh ≠ qdQ := by decide
@[simp] theorem qd_qdQ_ne_lDt : qdQ ≠ lDt := by decide
@[simp] theorem qd_lDt_ne_qdQ : lDt ≠ qdQ := by decide
@[simp] theorem qd_qdQ_ne_lDg : qdQ ≠ lDg := by decide
@[simp] theorem qd_lDg_ne_qdQ : lDg ≠ qdQ := by decide
@[simp] theorem qd_qdQ_ne_lDi : qdQ ≠ lDi := by decide
@[simp] theorem qd_lDi_ne_qdQ : lDi ≠ qdQ := by decide
@[simp] theorem qd_qdQ_ne_lRp : qdQ ≠ lRp := by decide
@[simp] theorem qd_lRp_ne_qdQ : lRp ≠ qdQ := by decide
@[simp] theorem qd_qdQ_ne_lRn : qdQ ≠ lRn := by decide
@[simp] theorem qd_lRn_ne_qdQ : lRn ≠ qdQ := by decide
@[simp] theorem qd_qdQ_ne_lDir : qdQ ≠ lDir := by decide
@[simp] theorem qd_lDir_ne_qdQ : lDir ≠ qdQ := by decide
@[simp] theorem qd_qdQ_ne_lFle : qdQ ≠ lFle := by decide
@[simp] theorem qd_lFle_ne_qdQ : lFle ≠ qdQ := by decide
@[simp] theorem qd_qdQ_ne_lKb : qdQ ≠ lKb := by decide
@[simp] theorem qd_lKb_ne_qdQ : lKb ≠ qdQ := by decide
@[simp] theorem qd_qdT1_ne_qdA : qdT1 ≠ qdA := by decide
@[simp] theorem qd_qdT1_ne_qdB : qdT1 ≠ qdB := by decide
@[simp] theorem qd_qdT1_ne_qdU : qdT1 ≠ qdU := by decide
@[simp] theorem qd_qdT1_ne_qdV : qdT1 ≠ qdV := by decide
@[simp] theorem qd_qdT1_ne_qdQ : qdT1 ≠ qdQ := by decide
@[simp] theorem qd_qdT1_ne_qdB1 : qdT1 ≠ qdB1 := by decide
@[simp] theorem qd_qdT1_ne_qdT2 : qdT1 ≠ qdT2 := by decide
@[simp] theorem qd_qdT1_ne_qdB2 : qdT1 ≠ qdB2 := by decide
@[simp] theorem qd_qdT1_ne_qdE : qdT1 ≠ qdE := by decide
@[simp] theorem qd_qdT1_ne_qdR : qdT1 ≠ qdR := by decide
@[simp] theorem qd_qdT1_ne_kFu : qdT1 ≠ kFu := by decide
@[simp] theorem qd_kFu_ne_qdT1 : kFu ≠ qdT1 := by decide
@[simp] theorem qd_qdT1_ne_kD : qdT1 ≠ kD := by decide
@[simp] theorem qd_kD_ne_qdT1 : kD ≠ qdT1 := by decide
@[simp] theorem qd_qdT1_ne_lFl : qdT1 ≠ lFl := by decide
@[simp] theorem qd_lFl_ne_qdT1 : lFl ≠ qdT1 := by decide
@[simp] theorem qd_qdT1_ne_lDh : qdT1 ≠ lDh := by decide
@[simp] theorem qd_lDh_ne_qdT1 : lDh ≠ qdT1 := by decide
@[simp] theorem qd_qdT1_ne_lDt : qdT1 ≠ lDt := by decide
@[simp] theorem qd_lDt_ne_qdT1 : lDt ≠ qdT1 := by decide
@[simp] theorem qd_qdT1_ne_lDg : qdT1 ≠ lDg := by decide
@[simp] theorem qd_lDg_ne_qdT1 : lDg ≠ qdT1 := by decide
@[simp] theorem qd_qdT1_ne_lDi : qdT1 ≠ lDi := by decide
@[simp] theorem qd_lDi_ne_qdT1 : lDi ≠ qdT1 := by decide
@[simp] theorem qd_qdT1_ne_lRp : qdT1 ≠ lRp := by decide
@[simp] theorem qd_lRp_ne_qdT1 : lRp ≠ qdT1 := by decide
@[simp] theorem qd_qdT1_ne_lRn : qdT1 ≠ lRn := by decide
@[simp] theorem qd_lRn_ne_qdT1 : lRn ≠ qdT1 := by decide
@[simp] theorem qd_qdT1_ne_lDir : qdT1 ≠ lDir := by decide
@[simp] theorem qd_lDir_ne_qdT1 : lDir ≠ qdT1 := by decide
@[simp] theorem qd_qdT1_ne_lFle : qdT1 ≠ lFle := by decide
@[simp] theorem qd_lFle_ne_qdT1 : lFle ≠ qdT1 := by decide
@[simp] theorem qd_qdT1_ne_lKb : qdT1 ≠ lKb := by decide
@[simp] theorem qd_lKb_ne_qdT1 : lKb ≠ qdT1 := by decide
@[simp] theorem qd_qdB1_ne_qdA : qdB1 ≠ qdA := by decide
@[simp] theorem qd_qdB1_ne_qdB : qdB1 ≠ qdB := by decide
@[simp] theorem qd_qdB1_ne_qdU : qdB1 ≠ qdU := by decide
@[simp] theorem qd_qdB1_ne_qdV : qdB1 ≠ qdV := by decide
@[simp] theorem qd_qdB1_ne_qdQ : qdB1 ≠ qdQ := by decide
@[simp] theorem qd_qdB1_ne_qdT1 : qdB1 ≠ qdT1 := by decide
@[simp] theorem qd_qdB1_ne_qdT2 : qdB1 ≠ qdT2 := by decide
@[simp] theorem qd_qdB1_ne_qdB2 : qdB1 ≠ qdB2 := by decide
@[simp] theorem qd_qdB1_ne_qdE : qdB1 ≠ qdE := by decide
@[simp] theorem qd_qdB1_ne_qdR : qdB1 ≠ qdR := by decide
@[simp] theorem qd_qdB1_ne_kFu : qdB1 ≠ kFu := by decide
@[simp] theorem qd_kFu_ne_qdB1 : kFu ≠ qdB1 := by decide
@[simp] theorem qd_qdB1_ne_kD : qdB1 ≠ kD := by decide
@[simp] theorem qd_kD_ne_qdB1 : kD ≠ qdB1 := by decide
@[simp] theorem qd_qdB1_ne_lFl : qdB1 ≠ lFl := by decide
@[simp] theorem qd_lFl_ne_qdB1 : lFl ≠ qdB1 := by decide
@[simp] theorem qd_qdB1_ne_lDh : qdB1 ≠ lDh := by decide
@[simp] theorem qd_lDh_ne_qdB1 : lDh ≠ qdB1 := by decide
@[simp] theorem qd_qdB1_ne_lDt : qdB1 ≠ lDt := by decide
@[simp] theorem qd_lDt_ne_qdB1 : lDt ≠ qdB1 := by decide
@[simp] theorem qd_qdB1_ne_lDg : qdB1 ≠ lDg := by decide
@[simp] theorem qd_lDg_ne_qdB1 : lDg ≠ qdB1 := by decide
@[simp] theorem qd_qdB1_ne_lDi : qdB1 ≠ lDi := by decide
@[simp] theorem qd_lDi_ne_qdB1 : lDi ≠ qdB1 := by decide
@[simp] theorem qd_qdB1_ne_lRp : qdB1 ≠ lRp := by decide
@[simp] theorem qd_lRp_ne_qdB1 : lRp ≠ qdB1 := by decide
@[simp] theorem qd_qdB1_ne_lRn : qdB1 ≠ lRn := by decide
@[simp] theorem qd_lRn_ne_qdB1 : lRn ≠ qdB1 := by decide
@[simp] theorem qd_qdB1_ne_lDir : qdB1 ≠ lDir := by decide
@[simp] theorem qd_lDir_ne_qdB1 : lDir ≠ qdB1 := by decide
@[simp] theorem qd_qdB1_ne_lFle : qdB1 ≠ lFle := by decide
@[simp] theorem qd_lFle_ne_qdB1 : lFle ≠ qdB1 := by decide
@[simp] theorem qd_qdB1_ne_lKb : qdB1 ≠ lKb := by decide
@[simp] theorem qd_lKb_ne_qdB1 : lKb ≠ qdB1 := by decide
@[simp] theorem qd_qdT2_ne_qdA : qdT2 ≠ qdA := by decide
@[simp] theorem qd_qdT2_ne_qdB : qdT2 ≠ qdB := by decide
@[simp] theorem qd_qdT2_ne_qdU : qdT2 ≠ qdU := by decide
@[simp] theorem qd_qdT2_ne_qdV : qdT2 ≠ qdV := by decide
@[simp] theorem qd_qdT2_ne_qdQ : qdT2 ≠ qdQ := by decide
@[simp] theorem qd_qdT2_ne_qdT1 : qdT2 ≠ qdT1 := by decide
@[simp] theorem qd_qdT2_ne_qdB1 : qdT2 ≠ qdB1 := by decide
@[simp] theorem qd_qdT2_ne_qdB2 : qdT2 ≠ qdB2 := by decide
@[simp] theorem qd_qdT2_ne_qdE : qdT2 ≠ qdE := by decide
@[simp] theorem qd_qdT2_ne_qdR : qdT2 ≠ qdR := by decide
@[simp] theorem qd_qdT2_ne_kFu : qdT2 ≠ kFu := by decide
@[simp] theorem qd_kFu_ne_qdT2 : kFu ≠ qdT2 := by decide
@[simp] theorem qd_qdT2_ne_kD : qdT2 ≠ kD := by decide
@[simp] theorem qd_kD_ne_qdT2 : kD ≠ qdT2 := by decide
@[simp] theorem qd_qdT2_ne_lFl : qdT2 ≠ lFl := by decide
@[simp] theorem qd_lFl_ne_qdT2 : lFl ≠ qdT2 := by decide
@[simp] theorem qd_qdT2_ne_lDh : qdT2 ≠ lDh := by decide
@[simp] theorem qd_lDh_ne_qdT2 : lDh ≠ qdT2 := by decide
@[simp] theorem qd_qdT2_ne_lDt : qdT2 ≠ lDt := by decide
@[simp] theorem qd_lDt_ne_qdT2 : lDt ≠ qdT2 := by decide
@[simp] theorem qd_qdT2_ne_lDg : qdT2 ≠ lDg := by decide
@[simp] theorem qd_lDg_ne_qdT2 : lDg ≠ qdT2 := by decide
@[simp] theorem qd_qdT2_ne_lDi : qdT2 ≠ lDi := by decide
@[simp] theorem qd_lDi_ne_qdT2 : lDi ≠ qdT2 := by decide
@[simp] theorem qd_qdT2_ne_lRp : qdT2 ≠ lRp := by decide
@[simp] theorem qd_lRp_ne_qdT2 : lRp ≠ qdT2 := by decide
@[simp] theorem qd_qdT2_ne_lRn : qdT2 ≠ lRn := by decide
@[simp] theorem qd_lRn_ne_qdT2 : lRn ≠ qdT2 := by decide
@[simp] theorem qd_qdT2_ne_lDir : qdT2 ≠ lDir := by decide
@[simp] theorem qd_lDir_ne_qdT2 : lDir ≠ qdT2 := by decide
@[simp] theorem qd_qdT2_ne_lFle : qdT2 ≠ lFle := by decide
@[simp] theorem qd_lFle_ne_qdT2 : lFle ≠ qdT2 := by decide
@[simp] theorem qd_qdT2_ne_lKb : qdT2 ≠ lKb := by decide
@[simp] theorem qd_lKb_ne_qdT2 : lKb ≠ qdT2 := by decide
@[simp] theorem qd_qdB2_ne_qdA : qdB2 ≠ qdA := by decide
@[simp] theorem qd_qdB2_ne_qdB : qdB2 ≠ qdB := by decide
@[simp] theorem qd_qdB2_ne_qdU : qdB2 ≠ qdU := by decide
@[simp] theorem qd_qdB2_ne_qdV : qdB2 ≠ qdV := by decide
@[simp] theorem qd_qdB2_ne_qdQ : qdB2 ≠ qdQ := by decide
@[simp] theorem qd_qdB2_ne_qdT1 : qdB2 ≠ qdT1 := by decide
@[simp] theorem qd_qdB2_ne_qdB1 : qdB2 ≠ qdB1 := by decide
@[simp] theorem qd_qdB2_ne_qdT2 : qdB2 ≠ qdT2 := by decide
@[simp] theorem qd_qdB2_ne_qdE : qdB2 ≠ qdE := by decide
@[simp] theorem qd_qdB2_ne_qdR : qdB2 ≠ qdR := by decide
@[simp] theorem qd_qdB2_ne_kFu : qdB2 ≠ kFu := by decide
@[simp] theorem qd_kFu_ne_qdB2 : kFu ≠ qdB2 := by decide
@[simp] theorem qd_qdB2_ne_kD : qdB2 ≠ kD := by decide
@[simp] theorem qd_kD_ne_qdB2 : kD ≠ qdB2 := by decide
@[simp] theorem qd_qdB2_ne_lFl : qdB2 ≠ lFl := by decide
@[simp] theorem qd_lFl_ne_qdB2 : lFl ≠ qdB2 := by decide
@[simp] theorem qd_qdB2_ne_lDh : qdB2 ≠ lDh := by decide
@[simp] theorem qd_lDh_ne_qdB2 : lDh ≠ qdB2 := by decide
@[simp] theorem qd_qdB2_ne_lDt : qdB2 ≠ lDt := by decide
@[simp] theorem qd_lDt_ne_qdB2 : lDt ≠ qdB2 := by decide
@[simp] theorem qd_qdB2_ne_lDg : qdB2 ≠ lDg := by decide
@[simp] theorem qd_lDg_ne_qdB2 : lDg ≠ qdB2 := by decide
@[simp] theorem qd_qdB2_ne_lDi : qdB2 ≠ lDi := by decide
@[simp] theorem qd_lDi_ne_qdB2 : lDi ≠ qdB2 := by decide
@[simp] theorem qd_qdB2_ne_lRp : qdB2 ≠ lRp := by decide
@[simp] theorem qd_lRp_ne_qdB2 : lRp ≠ qdB2 := by decide
@[simp] theorem qd_qdB2_ne_lRn : qdB2 ≠ lRn := by decide
@[simp] theorem qd_lRn_ne_qdB2 : lRn ≠ qdB2 := by decide
@[simp] theorem qd_qdB2_ne_lDir : qdB2 ≠ lDir := by decide
@[simp] theorem qd_lDir_ne_qdB2 : lDir ≠ qdB2 := by decide
@[simp] theorem qd_qdB2_ne_lFle : qdB2 ≠ lFle := by decide
@[simp] theorem qd_lFle_ne_qdB2 : lFle ≠ qdB2 := by decide
@[simp] theorem qd_qdB2_ne_lKb : qdB2 ≠ lKb := by decide
@[simp] theorem qd_lKb_ne_qdB2 : lKb ≠ qdB2 := by decide
@[simp] theorem qd_qdE_ne_qdA : qdE ≠ qdA := by decide
@[simp] theorem qd_qdE_ne_qdB : qdE ≠ qdB := by decide
@[simp] theorem qd_qdE_ne_qdU : qdE ≠ qdU := by decide
@[simp] theorem qd_qdE_ne_qdV : qdE ≠ qdV := by decide
@[simp] theorem qd_qdE_ne_qdQ : qdE ≠ qdQ := by decide
@[simp] theorem qd_qdE_ne_qdT1 : qdE ≠ qdT1 := by decide
@[simp] theorem qd_qdE_ne_qdB1 : qdE ≠ qdB1 := by decide
@[simp] theorem qd_qdE_ne_qdT2 : qdE ≠ qdT2 := by decide
@[simp] theorem qd_qdE_ne_qdB2 : qdE ≠ qdB2 := by decide
@[simp] theorem qd_qdE_ne_qdR : qdE ≠ qdR := by decide
@[simp] theorem qd_qdE_ne_kFu : qdE ≠ kFu := by decide
@[simp] theorem qd_kFu_ne_qdE : kFu ≠ qdE := by decide
@[simp] theorem qd_qdE_ne_kD : qdE ≠ kD := by decide
@[simp] theorem qd_kD_ne_qdE : kD ≠ qdE := by decide
@[simp] theorem qd_qdE_ne_lFl : qdE ≠ lFl := by decide
@[simp] theorem qd_lFl_ne_qdE : lFl ≠ qdE := by decide
@[simp] theorem qd_qdE_ne_lDh : qdE ≠ lDh := by decide
@[simp] theorem qd_lDh_ne_qdE : lDh ≠ qdE := by decide
@[simp] theorem qd_qdE_ne_lDt : qdE ≠ lDt := by decide
@[simp] theorem qd_lDt_ne_qdE : lDt ≠ qdE := by decide
@[simp] theorem qd_qdE_ne_lDg : qdE ≠ lDg := by decide
@[simp] theorem qd_lDg_ne_qdE : lDg ≠ qdE := by decide
@[simp] theorem qd_qdE_ne_lDi : qdE ≠ lDi := by decide
@[simp] theorem qd_lDi_ne_qdE : lDi ≠ qdE := by decide
@[simp] theorem qd_qdE_ne_lRp : qdE ≠ lRp := by decide
@[simp] theorem qd_lRp_ne_qdE : lRp ≠ qdE := by decide
@[simp] theorem qd_qdE_ne_lRn : qdE ≠ lRn := by decide
@[simp] theorem qd_lRn_ne_qdE : lRn ≠ qdE := by decide
@[simp] theorem qd_qdE_ne_lDir : qdE ≠ lDir := by decide
@[simp] theorem qd_lDir_ne_qdE : lDir ≠ qdE := by decide
@[simp] theorem qd_qdE_ne_lFle : qdE ≠ lFle := by decide
@[simp] theorem qd_lFle_ne_qdE : lFle ≠ qdE := by decide
@[simp] theorem qd_qdE_ne_lKb : qdE ≠ lKb := by decide
@[simp] theorem qd_lKb_ne_qdE : lKb ≠ qdE := by decide
@[simp] theorem qd_qdR_ne_qdA : qdR ≠ qdA := by decide
@[simp] theorem qd_qdR_ne_qdB : qdR ≠ qdB := by decide
@[simp] theorem qd_qdR_ne_qdU : qdR ≠ qdU := by decide
@[simp] theorem qd_qdR_ne_qdV : qdR ≠ qdV := by decide
@[simp] theorem qd_qdR_ne_qdQ : qdR ≠ qdQ := by decide
@[simp] theorem qd_qdR_ne_qdT1 : qdR ≠ qdT1 := by decide
@[simp] theorem qd_qdR_ne_qdB1 : qdR ≠ qdB1 := by decide
@[simp] theorem qd_qdR_ne_qdT2 : qdR ≠ qdT2 := by decide
@[simp] theorem qd_qdR_ne_qdB2 : qdR ≠ qdB2 := by decide
@[simp] theorem qd_qdR_ne_qdE : qdR ≠ qdE := by decide
@[simp] theorem qd_qdR_ne_kFu : qdR ≠ kFu := by decide
@[simp] theorem qd_kFu_ne_qdR : kFu ≠ qdR := by decide
@[simp] theorem qd_qdR_ne_kD : qdR ≠ kD := by decide
@[simp] theorem qd_kD_ne_qdR : kD ≠ qdR := by decide
@[simp] theorem qd_qdR_ne_lFl : qdR ≠ lFl := by decide
@[simp] theorem qd_lFl_ne_qdR : lFl ≠ qdR := by decide
@[simp] theorem qd_qdR_ne_lDh : qdR ≠ lDh := by decide
@[simp] theorem qd_lDh_ne_qdR : lDh ≠ qdR := by decide
@[simp] theorem qd_qdR_ne_lDt : qdR ≠ lDt := by decide
@[simp] theorem qd_lDt_ne_qdR : lDt ≠ qdR := by decide
@[simp] theorem qd_qdR_ne_lDg : qdR ≠ lDg := by decide
@[simp] theorem qd_lDg_ne_qdR : lDg ≠ qdR := by decide
@[simp] theorem qd_qdR_ne_lDi : qdR ≠ lDi := by decide
@[simp] theorem qd_lDi_ne_qdR : lDi ≠ qdR := by decide
@[simp] theorem qd_qdR_ne_lRp : qdR ≠ lRp := by decide
@[simp] theorem qd_lRp_ne_qdR : lRp ≠ qdR := by decide
@[simp] theorem qd_qdR_ne_lRn : qdR ≠ lRn := by decide
@[simp] theorem qd_lRn_ne_qdR : lRn ≠ qdR := by decide
@[simp] theorem qd_qdR_ne_lDir : qdR ≠ lDir := by decide
@[simp] theorem qd_lDir_ne_qdR : lDir ≠ qdR := by decide
@[simp] theorem qd_qdR_ne_lFle : qdR ≠ lFle := by decide
@[simp] theorem qd_lFle_ne_qdR : lFle ≠ qdR := by decide
@[simp] theorem qd_qdR_ne_lKb : qdR ≠ lKb := by decide
@[simp] theorem qd_lKb_ne_qdR : lKb ≠ qdR := by decide

def qdParams : List MlS := [kFu, kD, qdA, qdB]
def qdLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, qdU, qdV, qdQ, qdT1, qdB1, qdT2, qdB2, qdE, qdR]
def qdBody (C : Ctx) : ProgHOL 64 := prologue qdLocals
  (.ite (.cmp .equal (vv qdA) (vv qdB)) (.return (.const 2)) (.ite (tagIsE qdA 2) (.ite (tagIsE qdB 2) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv qdA)) (.seq eViewP (.seq (.assign .local qdU (.load .one (vv lRp))) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv qdB)) (.seq eViewP (.seq (.assign .local qdV (.load .one (vv lRp))) (.seq (.call (some (some (.local, qdQ), none)) LLeq.fEqv [(vv qdU), (vv qdV)]) (.ite (.cmp .equal (vv qdQ) (.const 0)) hang (.return (vv qdQ)))))))))))) (.return (.const 0))) (.ite (tagIsE qdA 8) (.ite (tagIsE qdB 8) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv qdA)) (.seq eViewP (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv qdB)) (.seq eViewP (.seq (.call (some (some (.local, qdQ), none)) LE.fLe [(vv qdA), (vv qdB)]) (.return (.op .add [(vv qdQ), (.const 1)]))))))))) (.return (.const 0))) (.ite (tagIsE qdA 6) (.ite (tagIsE qdB 6) (.ite (.cmp .lower (vv kD) (.const (BitVec.ofNat 64 (2 ^ 61)))) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv qdA)) (.seq eViewP (.seq (.assign .local qdT1 (.load .one (vv lRp))) (.seq (.assign .local qdB1 (.load .one (.op .add [(vv lRp), (.const 8)]))) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv qdB)) (.seq eViewP (.seq (.assign .local qdT2 (.load .one (vv lRp))) (.seq (.assign .local qdB2 (.load .one (.op .add [(vv lRp), (.const 8)]))) (allocP C qdE (.const 8) (.seq (.store (vv qdE) (.const 0)) (.seq (.call (some (some (.local, qdR), none)) fDb [(vv kFu), (vv kD), (.const 0), (.const (BitVec.ofNat 64 bindersFuel)), (vv qdE), (vv qdT1), (vv qdB1), (vv qdT2), (vv qdB2)]) (.return (.op .add [(vv qdR), (.const 1)]))))))))))))))) hang) (.return (.const 0))) (.ite (tagIsE qdA 5) (.ite (tagIsE qdB 5) (.ite (.cmp .lower (vv kD) (.const (BitVec.ofNat 64 (2 ^ 61)))) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv qdA)) (.seq eViewP (.seq (.assign .local qdT1 (.load .one (vv lRp))) (.seq (.assign .local qdB1 (.load .one (.op .add [(vv lRp), (.const 8)]))) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv qdB)) (.seq eViewP (.seq (.assign .local qdT2 (.load .one (vv lRp))) (.seq (.assign .local qdB2 (.load .one (.op .add [(vv lRp), (.const 8)]))) (allocP C qdE (.const 8) (.seq (.store (vv qdE) (.const 0)) (.seq (.call (some (some (.local, qdR), none)) fDb [(vv kFu), (vv kD), (.const 1), (.const (BitVec.ofNat 64 bindersFuel)), (vv qdE), (vv qdT1), (vv qdB1), (vv qdT2), (vv qdB2)]) (.return (.op .add [(vv qdR), (.const 1)]))))))))))))))) hang) (.return (.const 0))) (.return (.const 0)))))))

section
variable {σ : Type}

structure QdCodes (C : Ctx) (v : Bool) : Prop where
  eqv : C.code.lookup LLeq.fEqv = some ([(LEq.pLa, .one), (LEq.pLb, .one)], LLeq.eqvBody, .one)
  le : C.code.lookup LE.fLe = some ([LE.leA, LE.leB].map (fun p => (p, ShapeHOL.one)), LE.leBody, .one)
  db : DbCodes C v

theorem qd_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (hc : QdCodes C mode.verifiedChecks)
    (hI : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → d' < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (inferE C fIB) s1 ((knot mode C n).infer d' e')
      (PostK (ctxH C H)))
    (hD : ∀ (H : List (BitVec 64)) s1 d' a b, C.H <+: H → d' < 2 ^ 63 → Callee (σ := σ) (ctxH C H) dParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW a, Enc.idxW b] (dE C) s1 ((knot mode C n).defeq d' a b)
      (PostB (ctxH C H)))
    (hLE : ∀ (H : List (BitVec 64)) s1 (u v : LIdx), C.H <+: H → (denoteL s1.store.ls u).isSome = true →
      (denoteL s1.store.ls v).isSome = true →
      SpecR (σ := σ) (Pre (ctxH C H) s1 [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s1 (lvlEq? u v)
        (LLeq.PostOB (ctxH C H)))
    (s : AState) (d : Nat) (hd : d < 2 ^ 64) (a b : EIdx) :
    SpecR (σ := σ) (Pre C s (qdParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b])) (qdBody C) s
      (quickDefEq mode (knot mode C n) d a b) (PostOBH C) := by
  refine specR_prologue (postOBH_locals C) (Knot.params_none C qdLocals qdParams _ (by decide) (by decide)) ?_
  unfold quickDefEq
  by_cases hab : a = b
  · subst hab
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, qdParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [beq_self_eq_true, ↓reduceIte]
    exact specR_returnI _ (LLeq.obW (some true)) rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  have hne : Enc.idxW a ≠ Enc.idxW b := fun e => hab (Enc.idxW_inj e)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, qdParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only [show (a == b) = false by simpa using hab, Bool.false_eq_true, ↓reduceIte]
  refine Knot.specR_tagIteV qdA a 2 (by decide) (by decide) (by simp +decide [Env.get, qdParams, ctxEnv]) (fun hA2 => ?_) (fun hA2 => ?_)
  · refine Knot.specR_tagIteV qdB b 2 (by decide) (by decide) (by simp +decide [Env.get, qdParams, ctxEnv]) (fun hB2 => ?_) (fun hB2 => ?_)
    swap
    · have hbn : (a.tag != b.tag) = true := by rw [bne_iff_ne, hA2]; exact fun h => hB2 h.symm
      rw [ite_eq_left hbn]
      exact specR_returnI _ (LLeq.obW none) rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have hbn : ¬ (a.tag != b.tag) = true := by rw [bne_iff_ne, hA2, hB2]; simp
    rw [ite_eq_right hbn, ite_eq_left (by simp [hA2, ETag.sort, ETag.lit, ETag.forallE, ETag.lam])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv qdA) (Enc.idxW a) (by decide) (by simp +decide [Env.get, qdParams, ctxEnv]) ?_
    refine specR_viewP a (by simp) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl)
      (by decide) (fun va P hva htna _ => ?_)
    refine specR_congr (view_bind_eq a va _ s hva) ?_
    have hta : va.tagN = 2 := by rw [htna, hA2]; rfl
    obtain ⟨u, rfl⟩ : ∃ u, va = .sort u := by cases va <;> simp [ENodeView.tagN] at hta ⊢
    try dsimp only
    refine specR_loadI' qdU (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW u) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encSort] using wordsAt_mem0 P (Enc.idxW u) [] []) ?_
    refine specR_dropM ?_
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv qdB) (Enc.idxW b) (by decide) (by simp +decide [Env.get, qdParams, ctxEnv]) ?_
    refine specR_viewP b (by simp) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl)
      (by decide) (fun vb P2 hvb htnb _ => ?_)
    refine specR_congr (view_bind_eq b vb _ s hvb) ?_
    have htb : vb.tagN = 2 := by rw [htnb, hB2]; rfl
    obtain ⟨v, rfl⟩ : ∃ v, vb = .sort v := by cases vb <;> simp [ENodeView.tagN] at htb ⊢
    try dsimp only
    refine specR_loadI' qdV (vv lRp) P2 (P2 + BitVec.ofNat 64 0) (Enc.idxW v) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encSort] using wordsAt_mem0 P2 (Enc.idxW v) [] []) ?_
    refine specR_dropM ?_
    refine specR_callNIH (C := C) qdQ LLeq.fEqv [LEq.pLa, LEq.pLb] [vv qdU, vv qdV] LLeq.eqvBody
      [Enc.idxW u, Enc.idxW v] (by decide) rfl (by decide) hc.eqv ⟨by simp, by simp, trivial⟩
      (LLeq.PostOB C) (fun o w _ H' => H' = C.H ∧ w = LLeq.obW o)
      (fun o w s' st ⟨hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, hsr⟩)
      (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu [LEq.pLa, LEq.pLb] _ rfl hlk)
        (hLE C.H s u v (List.prefix_refl _) (sr_sortSome hu hva) (sr_sortSome hu hvb))) (fun o w s1 H1 _ ⟨eH, hw⟩ => ?_)
    subst H1; subst hw
    rcases o with _ | ok
    · exact specR_ifI _ 1 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI)
        (fun h => absurd h (by decide))
    have hne : LLeq.obW (some ok) ≠ 0 := by cases ok <;> decide
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [liftFueled, pure_bind]
    exact specR_returnI _ (LLeq.obW (some ok)) (by simp)
      (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine Knot.specR_tagIteV qdA a 8 (by decide) (by decide) (by simp +decide [Env.get, qdParams, ctxEnv]) (fun hA8 => ?_) (fun hA8 => ?_)
  · refine Knot.specR_tagIteV qdB b 8 (by decide) (by decide) (by simp +decide [Env.get, qdParams, ctxEnv]) (fun hB8 => ?_) (fun hB8 => ?_)
    swap
    · have hbn : (a.tag != b.tag) = true := by rw [bne_iff_ne, hA8]; exact fun h => hB8 h.symm
      rw [ite_eq_left hbn]
      exact specR_returnI _ (LLeq.obW none) rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have hbn : ¬ (a.tag != b.tag) = true := by rw [bne_iff_ne, hA8, hB8]; simp
    rw [ite_eq_right hbn, ite_eq_left (by simp [hA8, ETag.sort, ETag.lit, ETag.forallE, ETag.lam])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv qdA) (Enc.idxW a) (by decide) (by simp +decide [Env.get, qdParams, ctxEnv]) ?_
    refine specR_viewP a (by simp) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl)
      (by decide) (fun va P hva htna _ => ?_)
    refine specR_congr (view_bind_eq a va _ s hva) ?_
    have hta : va.tagN = 8 := by rw [htna, hA8]; rfl
    obtain ⟨l1, rfl⟩ := tagN_lit hta
    try dsimp only
    refine specR_dropM ?_
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv qdB) (Enc.idxW b) (by decide) (by simp +decide [Env.get, qdParams, ctxEnv]) ?_
    refine specR_viewP b (by simp) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl)
      (by decide) (fun vb P2 hvb htnb _ => ?_)
    refine specR_congr (view_bind_eq b vb _ s hvb) ?_
    have htb : vb.tagN = 8 := by rw [htnb, hB8]; rfl
    obtain ⟨l2, rfl⟩ := tagN_lit htb
    try dsimp only
    refine specR_dropM ?_
    refine specR_callPure (C := C) qdQ LE.fLe [LE.leA, LE.leB] [vv qdA, vv qdB] LE.leBody [Enc.idxW a, Enc.idxW b]
      (l1 == l2) (by decide) rfl (by decide) hc.le ⟨by simp +decide [Env.get, qdParams, ctxEnv], by simp +decide [Env.get, qdParams, ctxEnv], trivial⟩
      (PostBS C s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
      (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [LE.leA, LE.leB] _ rfl hlk)
        (LE.le_spec C s a b l1 l2 hva hvb))
      (fun w H1 _ ⟨eH, hw⟩ => ?_)
    subst H1; subst hw
    exact specR_returnI _ (LLeq.obW (some (l1 == l2))) (by simp [sev, obW_some])
      (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine Knot.specR_tagIteV qdA a 6 (by decide) (by decide) (by simp +decide [Env.get, qdParams, ctxEnv]) (fun hA6 => ?_) (fun hA6 => ?_)
  · refine Knot.specR_tagIteV qdB b 6 (by decide) (by decide) (by simp +decide [Env.get, qdParams, ctxEnv]) (fun hB6 => ?_) (fun hB6 => ?_)
    swap
    · have hbn : (a.tag != b.tag) = true := by rw [bne_iff_ne, hA6]; exact fun h => hB6 h.symm
      rw [ite_eq_left hbn]
      exact specR_returnI _ (LLeq.obW none) rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have hbn : ¬ (a.tag != b.tag) = true := by rw [bne_iff_ne, hA6, hB6]; simp
    rw [ite_eq_right hbn, ite_eq_left (by simp [hA6, ETag.sort, ETag.lit, ETag.forallE, ETag.lam])]
    by_cases hd2 : d < 2 ^ 61
    swap
    · have hl : ¬ (BitVec.ofNat 64 d < BitVec.ofNat 64 (2 ^ 61)) := by
        rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]; norm_num; omega
      exact specR_ifI _ 0 (by simp +decide [sev, Env.get, qdParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; first | exact hl | (rw [Nat.mod_eq_of_lt (show d < 18446744073709551616 by omega)]; omega))
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    have hl : BitVec.ofNat 64 d < BitVec.ofNat 64 (2 ^ 61) := by
      rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]; norm_num; omega
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, qdParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; first | exact hl | (rw [Nat.mod_eq_of_lt (show d < 18446744073709551616 by omega)]; omega))
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv qdA) (Enc.idxW a) (by decide) (by simp +decide [Env.get, qdParams, ctxEnv]) ?_
    refine specR_viewP a (by simp) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl)
      (by decide) (fun va P hva htna _ => ?_)
    refine specR_congr (view_bind_eq a va _ s hva) ?_
    have hta : va.tagN = 6 := by rw [htna, hA6]; rfl
    obtain ⟨ty1, b1, rfl⟩ : ∃ ty b, va = .forallE ty b := by cases va <;> simp [ENodeView.tagN] at hta ⊢
    try dsimp only
    refine specR_loadI' qdT1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty1) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW ty1) [Enc.idxW b1] []) ?_
    refine specR_loadI' qdB1 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b1) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW ty1) (Enc.idxW b1) [] []) ?_
    refine specR_dropM ?_
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv qdB) (Enc.idxW b) (by decide) (by simp +decide [Env.get, qdParams, ctxEnv]) ?_
    refine specR_viewP b (by simp) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl)
      (by decide) (fun vb P2 hvb htnb _ => ?_)
    refine specR_congr (view_bind_eq b vb _ s hvb) ?_
    have htb : vb.tagN = 6 := by rw [htnb, hB6]; rfl
    obtain ⟨ty2, b2, rfl⟩ : ∃ ty b, vb = .forallE ty b := by cases vb <;> simp [ENodeView.tagN] at htb ⊢
    try dsimp only
    refine specR_loadI' qdT2 (vv lRp) P2 (P2 + BitVec.ofNat 64 0) (Enc.idxW ty2) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P2 (Enc.idxW ty2) [Enc.idxW b2] []) ?_
    refine specR_loadI' qdB2 _ (P2 + 8) (P2 + BitVec.ofNat 64 8) (Enc.idxW b2) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P2 (Enc.idxW ty2) (Enc.idxW b2) [] []) ?_
    refine specR_dropM ?_
    refine specR_emptyBlk (C0 := C) hok (H := C.H) qdE (by decide) (fun H1 oe hp1 hbe => ?_)
    refine specR_congr (m' := defeqBinders mode (knot mode C n) false bindersFuel d ([] : List EIdx).toArray ty1 b1 ty2 b2
      >>= fun ok => pure (some ok)) (by simp) ?_
    refine specR_callNIH (C := ctxH C H1) qdR fDb dbParams
      [vv kFu, vv kD, .const 0, .const (BitVec.ofNat 64 bindersFuel), vv qdE, vv qdT1, vv qdB1, vv qdT2, vv qdB2]
      dbBody [BitVec.ofNat 64 n, BitVec.ofNat 64 d, boolW false, BitVec.ofNat 64 bindersFuel, cellA C oe, Enc.idxW ty1,
        Enc.idxW b1, Enc.idxW ty2, Enc.idxW b2] (by decide) rfl (by decide) hc.db.self
      ⟨by simp +decide [Env.get, qdParams, ctxEnv], by simp +decide [Env.get, qdParams, ctxEnv], rfl, rfl, by simp <;> rfl, by simp, by simp, by simp, by simp, trivial⟩
      (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu dbParams _ rfl hlk)
        (db_spec ra mode n C hok hc.db hI hD false bindersFuel d [] oe ty1 b1 ty2 b2 H1 s hp1 (by simpa using hbe)
          (by unfold bindersFuel; omega)))
      (fun ok w s2 H2 hp2 hw => ?_)
    subst hw
    exact specR_returnI _ (LLeq.obW (some ok)) (by simp [sev, obW_some])
      (fun t ht => ⟨H2, hp1.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine Knot.specR_tagIteV qdA a 5 (by decide) (by decide) (by simp +decide [Env.get, qdParams, ctxEnv]) (fun hA5 => ?_) (fun hA5 => ?_)
  · refine Knot.specR_tagIteV qdB b 5 (by decide) (by decide) (by simp +decide [Env.get, qdParams, ctxEnv]) (fun hB5 => ?_) (fun hB5 => ?_)
    swap
    · have hbn : (a.tag != b.tag) = true := by rw [bne_iff_ne, hA5]; exact fun h => hB5 h.symm
      rw [ite_eq_left hbn]
      exact specR_returnI _ (LLeq.obW none) rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have hbn : ¬ (a.tag != b.tag) = true := by rw [bne_iff_ne, hA5, hB5]; simp
    rw [ite_eq_right hbn, ite_eq_left (by simp [hA5, ETag.sort, ETag.lit, ETag.forallE, ETag.lam])]
    by_cases hd2 : d < 2 ^ 61
    swap
    · have hl : ¬ (BitVec.ofNat 64 d < BitVec.ofNat 64 (2 ^ 61)) := by
        rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]; norm_num; omega
      exact specR_ifI _ 0 (by simp +decide [sev, Env.get, qdParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; first | exact hl | (rw [Nat.mod_eq_of_lt (show d < 18446744073709551616 by omega)]; omega))
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    have hl : BitVec.ofNat 64 d < BitVec.ofNat 64 (2 ^ 61) := by
      rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]; norm_num; omega
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, qdParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; first | exact hl | (rw [Nat.mod_eq_of_lt (show d < 18446744073709551616 by omega)]; omega))
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv qdA) (Enc.idxW a) (by decide) (by simp +decide [Env.get, qdParams, ctxEnv]) ?_
    refine specR_viewP a (by simp) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl)
      (by decide) (fun va P hva htna _ => ?_)
    refine specR_congr (view_bind_eq a va _ s hva) ?_
    have hta : va.tagN = 5 := by rw [htna, hA5]; rfl
    obtain ⟨ty1, b1, rfl⟩ : ∃ ty b, va = .lam ty b := by cases va <;> simp [ENodeView.tagN] at hta ⊢
    try dsimp only
    refine specR_loadI' qdT1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty1) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW ty1) [Enc.idxW b1] []) ?_
    refine specR_loadI' qdB1 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b1) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW ty1) (Enc.idxW b1) [] []) ?_
    refine specR_dropM ?_
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv qdB) (Enc.idxW b) (by decide) (by simp +decide [Env.get, qdParams, ctxEnv]) ?_
    refine specR_viewP b (by simp) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl)
      (by decide) (fun vb P2 hvb htnb _ => ?_)
    refine specR_congr (view_bind_eq b vb _ s hvb) ?_
    have htb : vb.tagN = 5 := by rw [htnb, hB5]; rfl
    obtain ⟨ty2, b2, rfl⟩ : ∃ ty b, vb = .lam ty b := by cases vb <;> simp [ENodeView.tagN] at htb ⊢
    try dsimp only
    refine specR_loadI' qdT2 (vv lRp) P2 (P2 + BitVec.ofNat 64 0) (Enc.idxW ty2) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P2 (Enc.idxW ty2) [Enc.idxW b2] []) ?_
    refine specR_loadI' qdB2 _ (P2 + 8) (P2 + BitVec.ofNat 64 8) (Enc.idxW b2) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P2 (Enc.idxW ty2) (Enc.idxW b2) [] []) ?_
    refine specR_dropM ?_
    refine specR_emptyBlk (C0 := C) hok (H := C.H) qdE (by decide) (fun H1 oe hp1 hbe => ?_)
    refine specR_congr (m' := defeqBinders mode (knot mode C n) true bindersFuel d ([] : List EIdx).toArray ty1 b1 ty2 b2
      >>= fun ok => pure (some ok)) (by simp) ?_
    refine specR_callNIH (C := ctxH C H1) qdR fDb dbParams
      [vv kFu, vv kD, .const 1, .const (BitVec.ofNat 64 bindersFuel), vv qdE, vv qdT1, vv qdB1, vv qdT2, vv qdB2]
      dbBody [BitVec.ofNat 64 n, BitVec.ofNat 64 d, boolW true, BitVec.ofNat 64 bindersFuel, cellA C oe, Enc.idxW ty1,
        Enc.idxW b1, Enc.idxW ty2, Enc.idxW b2] (by decide) rfl (by decide) hc.db.self
      ⟨by simp +decide [Env.get, qdParams, ctxEnv], by simp +decide [Env.get, qdParams, ctxEnv], rfl, rfl, by simp <;> rfl, by simp, by simp, by simp, by simp, trivial⟩
      (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu dbParams _ rfl hlk)
        (db_spec ra mode n C hok hc.db hI hD true bindersFuel d [] oe ty1 b1 ty2 b2 H1 s hp1 (by simpa using hbe)
          (by unfold bindersFuel; omega)))
      (fun ok w s2 H2 hp2 hw => ?_)
    subst hw
    exact specR_returnI _ (LLeq.obW (some ok)) (by simp [sev, obW_some])
      (fun t ht => ⟨H2, hp1.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  by_cases htt : (a.tag != b.tag) = true
  · rw [ite_eq_left htt]
    exact specR_returnI _ (LLeq.obW none) rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [ite_eq_right htt, ite_eq_right (by simp [ETag.sort, ETag.lit, ETag.forallE, ETag.lam]; exact ⟨⟨⟨hA2, hA8⟩, hA6⟩, hA5⟩)]
  exact specR_returnI _ (LLeq.obW none) rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
