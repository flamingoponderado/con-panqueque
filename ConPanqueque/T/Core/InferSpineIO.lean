import ConPanqueque.T.Core.InferIOArms
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# The io grade's application arm: `inferSpineIO`

`inferSpine` without the argument checks (official `infer_only`): the head's type is walked down the argument
vector, the pending substitutions kept in an accumulator block.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def soT := ofString "son_t"
def soA := ofString "son_a"
def soG := ofString "son_g"
def soI := ofString "son_i"
def soN := ofString "son_n"
def soX := ofString "son_x"
def soDm := ofString "son_dm"
def soB := ofString "son_b"
def soL := ofString "son_l"
def soO := ofString "son_o"
def soA2 := ofString "son_a2"
def soW := ofString "son_w"
def soE0 := ofString "son_e0"
def soR := ofString "son_r"
def fSo := ofString "inferSpineIO"

@[simp] theorem so_soT_ne_soA : soT ≠ soA := by decide
@[simp] theorem so_soT_ne_soG : soT ≠ soG := by decide
@[simp] theorem so_soT_ne_soI : soT ≠ soI := by decide
@[simp] theorem so_soT_ne_soN : soT ≠ soN := by decide
@[simp] theorem so_soT_ne_soX : soT ≠ soX := by decide
@[simp] theorem so_soT_ne_soDm : soT ≠ soDm := by decide
@[simp] theorem so_soT_ne_soB : soT ≠ soB := by decide
@[simp] theorem so_soT_ne_soL : soT ≠ soL := by decide
@[simp] theorem so_soT_ne_soO : soT ≠ soO := by decide
@[simp] theorem so_soT_ne_soA2 : soT ≠ soA2 := by decide
@[simp] theorem so_soT_ne_soW : soT ≠ soW := by decide
@[simp] theorem so_soT_ne_soE0 : soT ≠ soE0 := by decide
@[simp] theorem so_soT_ne_soR : soT ≠ soR := by decide
@[simp] theorem so_soT_ne_kFu : soT ≠ kFu := by decide
@[simp] theorem so_kFu_ne_soT : kFu ≠ soT := by decide
@[simp] theorem so_soT_ne_kD : soT ≠ kD := by decide
@[simp] theorem so_kD_ne_soT : kD ≠ soT := by decide
@[simp] theorem so_soT_ne_lFl : soT ≠ lFl := by decide
@[simp] theorem so_lFl_ne_soT : lFl ≠ soT := by decide
@[simp] theorem so_soT_ne_lDh : soT ≠ lDh := by decide
@[simp] theorem so_lDh_ne_soT : lDh ≠ soT := by decide
@[simp] theorem so_soT_ne_lDt : soT ≠ lDt := by decide
@[simp] theorem so_lDt_ne_soT : lDt ≠ soT := by decide
@[simp] theorem so_soT_ne_lDg : soT ≠ lDg := by decide
@[simp] theorem so_lDg_ne_soT : lDg ≠ soT := by decide
@[simp] theorem so_soT_ne_lDi : soT ≠ lDi := by decide
@[simp] theorem so_lDi_ne_soT : lDi ≠ soT := by decide
@[simp] theorem so_soT_ne_lRp : soT ≠ lRp := by decide
@[simp] theorem so_lRp_ne_soT : lRp ≠ soT := by decide
@[simp] theorem so_soT_ne_lRn : soT ≠ lRn := by decide
@[simp] theorem so_lRn_ne_soT : lRn ≠ soT := by decide
@[simp] theorem so_soT_ne_lDir : soT ≠ lDir := by decide
@[simp] theorem so_lDir_ne_soT : lDir ≠ soT := by decide
@[simp] theorem so_soT_ne_lFle : soT ≠ lFle := by decide
@[simp] theorem so_lFle_ne_soT : lFle ≠ soT := by decide
@[simp] theorem so_soT_ne_lKb : soT ≠ lKb := by decide
@[simp] theorem so_lKb_ne_soT : lKb ≠ soT := by decide
@[simp] theorem so_soA_ne_soT : soA ≠ soT := by decide
@[simp] theorem so_soA_ne_soG : soA ≠ soG := by decide
@[simp] theorem so_soA_ne_soI : soA ≠ soI := by decide
@[simp] theorem so_soA_ne_soN : soA ≠ soN := by decide
@[simp] theorem so_soA_ne_soX : soA ≠ soX := by decide
@[simp] theorem so_soA_ne_soDm : soA ≠ soDm := by decide
@[simp] theorem so_soA_ne_soB : soA ≠ soB := by decide
@[simp] theorem so_soA_ne_soL : soA ≠ soL := by decide
@[simp] theorem so_soA_ne_soO : soA ≠ soO := by decide
@[simp] theorem so_soA_ne_soA2 : soA ≠ soA2 := by decide
@[simp] theorem so_soA_ne_soW : soA ≠ soW := by decide
@[simp] theorem so_soA_ne_soE0 : soA ≠ soE0 := by decide
@[simp] theorem so_soA_ne_soR : soA ≠ soR := by decide
@[simp] theorem so_soA_ne_kFu : soA ≠ kFu := by decide
@[simp] theorem so_kFu_ne_soA : kFu ≠ soA := by decide
@[simp] theorem so_soA_ne_kD : soA ≠ kD := by decide
@[simp] theorem so_kD_ne_soA : kD ≠ soA := by decide
@[simp] theorem so_soA_ne_lFl : soA ≠ lFl := by decide
@[simp] theorem so_lFl_ne_soA : lFl ≠ soA := by decide
@[simp] theorem so_soA_ne_lDh : soA ≠ lDh := by decide
@[simp] theorem so_lDh_ne_soA : lDh ≠ soA := by decide
@[simp] theorem so_soA_ne_lDt : soA ≠ lDt := by decide
@[simp] theorem so_lDt_ne_soA : lDt ≠ soA := by decide
@[simp] theorem so_soA_ne_lDg : soA ≠ lDg := by decide
@[simp] theorem so_lDg_ne_soA : lDg ≠ soA := by decide
@[simp] theorem so_soA_ne_lDi : soA ≠ lDi := by decide
@[simp] theorem so_lDi_ne_soA : lDi ≠ soA := by decide
@[simp] theorem so_soA_ne_lRp : soA ≠ lRp := by decide
@[simp] theorem so_lRp_ne_soA : lRp ≠ soA := by decide
@[simp] theorem so_soA_ne_lRn : soA ≠ lRn := by decide
@[simp] theorem so_lRn_ne_soA : lRn ≠ soA := by decide
@[simp] theorem so_soA_ne_lDir : soA ≠ lDir := by decide
@[simp] theorem so_lDir_ne_soA : lDir ≠ soA := by decide
@[simp] theorem so_soA_ne_lFle : soA ≠ lFle := by decide
@[simp] theorem so_lFle_ne_soA : lFle ≠ soA := by decide
@[simp] theorem so_soA_ne_lKb : soA ≠ lKb := by decide
@[simp] theorem so_lKb_ne_soA : lKb ≠ soA := by decide
@[simp] theorem so_soG_ne_soT : soG ≠ soT := by decide
@[simp] theorem so_soG_ne_soA : soG ≠ soA := by decide
@[simp] theorem so_soG_ne_soI : soG ≠ soI := by decide
@[simp] theorem so_soG_ne_soN : soG ≠ soN := by decide
@[simp] theorem so_soG_ne_soX : soG ≠ soX := by decide
@[simp] theorem so_soG_ne_soDm : soG ≠ soDm := by decide
@[simp] theorem so_soG_ne_soB : soG ≠ soB := by decide
@[simp] theorem so_soG_ne_soL : soG ≠ soL := by decide
@[simp] theorem so_soG_ne_soO : soG ≠ soO := by decide
@[simp] theorem so_soG_ne_soA2 : soG ≠ soA2 := by decide
@[simp] theorem so_soG_ne_soW : soG ≠ soW := by decide
@[simp] theorem so_soG_ne_soE0 : soG ≠ soE0 := by decide
@[simp] theorem so_soG_ne_soR : soG ≠ soR := by decide
@[simp] theorem so_soG_ne_kFu : soG ≠ kFu := by decide
@[simp] theorem so_kFu_ne_soG : kFu ≠ soG := by decide
@[simp] theorem so_soG_ne_kD : soG ≠ kD := by decide
@[simp] theorem so_kD_ne_soG : kD ≠ soG := by decide
@[simp] theorem so_soG_ne_lFl : soG ≠ lFl := by decide
@[simp] theorem so_lFl_ne_soG : lFl ≠ soG := by decide
@[simp] theorem so_soG_ne_lDh : soG ≠ lDh := by decide
@[simp] theorem so_lDh_ne_soG : lDh ≠ soG := by decide
@[simp] theorem so_soG_ne_lDt : soG ≠ lDt := by decide
@[simp] theorem so_lDt_ne_soG : lDt ≠ soG := by decide
@[simp] theorem so_soG_ne_lDg : soG ≠ lDg := by decide
@[simp] theorem so_lDg_ne_soG : lDg ≠ soG := by decide
@[simp] theorem so_soG_ne_lDi : soG ≠ lDi := by decide
@[simp] theorem so_lDi_ne_soG : lDi ≠ soG := by decide
@[simp] theorem so_soG_ne_lRp : soG ≠ lRp := by decide
@[simp] theorem so_lRp_ne_soG : lRp ≠ soG := by decide
@[simp] theorem so_soG_ne_lRn : soG ≠ lRn := by decide
@[simp] theorem so_lRn_ne_soG : lRn ≠ soG := by decide
@[simp] theorem so_soG_ne_lDir : soG ≠ lDir := by decide
@[simp] theorem so_lDir_ne_soG : lDir ≠ soG := by decide
@[simp] theorem so_soG_ne_lFle : soG ≠ lFle := by decide
@[simp] theorem so_lFle_ne_soG : lFle ≠ soG := by decide
@[simp] theorem so_soG_ne_lKb : soG ≠ lKb := by decide
@[simp] theorem so_lKb_ne_soG : lKb ≠ soG := by decide
@[simp] theorem so_soI_ne_soT : soI ≠ soT := by decide
@[simp] theorem so_soI_ne_soA : soI ≠ soA := by decide
@[simp] theorem so_soI_ne_soG : soI ≠ soG := by decide
@[simp] theorem so_soI_ne_soN : soI ≠ soN := by decide
@[simp] theorem so_soI_ne_soX : soI ≠ soX := by decide
@[simp] theorem so_soI_ne_soDm : soI ≠ soDm := by decide
@[simp] theorem so_soI_ne_soB : soI ≠ soB := by decide
@[simp] theorem so_soI_ne_soL : soI ≠ soL := by decide
@[simp] theorem so_soI_ne_soO : soI ≠ soO := by decide
@[simp] theorem so_soI_ne_soA2 : soI ≠ soA2 := by decide
@[simp] theorem so_soI_ne_soW : soI ≠ soW := by decide
@[simp] theorem so_soI_ne_soE0 : soI ≠ soE0 := by decide
@[simp] theorem so_soI_ne_soR : soI ≠ soR := by decide
@[simp] theorem so_soI_ne_kFu : soI ≠ kFu := by decide
@[simp] theorem so_kFu_ne_soI : kFu ≠ soI := by decide
@[simp] theorem so_soI_ne_kD : soI ≠ kD := by decide
@[simp] theorem so_kD_ne_soI : kD ≠ soI := by decide
@[simp] theorem so_soI_ne_lFl : soI ≠ lFl := by decide
@[simp] theorem so_lFl_ne_soI : lFl ≠ soI := by decide
@[simp] theorem so_soI_ne_lDh : soI ≠ lDh := by decide
@[simp] theorem so_lDh_ne_soI : lDh ≠ soI := by decide
@[simp] theorem so_soI_ne_lDt : soI ≠ lDt := by decide
@[simp] theorem so_lDt_ne_soI : lDt ≠ soI := by decide
@[simp] theorem so_soI_ne_lDg : soI ≠ lDg := by decide
@[simp] theorem so_lDg_ne_soI : lDg ≠ soI := by decide
@[simp] theorem so_soI_ne_lDi : soI ≠ lDi := by decide
@[simp] theorem so_lDi_ne_soI : lDi ≠ soI := by decide
@[simp] theorem so_soI_ne_lRp : soI ≠ lRp := by decide
@[simp] theorem so_lRp_ne_soI : lRp ≠ soI := by decide
@[simp] theorem so_soI_ne_lRn : soI ≠ lRn := by decide
@[simp] theorem so_lRn_ne_soI : lRn ≠ soI := by decide
@[simp] theorem so_soI_ne_lDir : soI ≠ lDir := by decide
@[simp] theorem so_lDir_ne_soI : lDir ≠ soI := by decide
@[simp] theorem so_soI_ne_lFle : soI ≠ lFle := by decide
@[simp] theorem so_lFle_ne_soI : lFle ≠ soI := by decide
@[simp] theorem so_soI_ne_lKb : soI ≠ lKb := by decide
@[simp] theorem so_lKb_ne_soI : lKb ≠ soI := by decide
@[simp] theorem so_soN_ne_soT : soN ≠ soT := by decide
@[simp] theorem so_soN_ne_soA : soN ≠ soA := by decide
@[simp] theorem so_soN_ne_soG : soN ≠ soG := by decide
@[simp] theorem so_soN_ne_soI : soN ≠ soI := by decide
@[simp] theorem so_soN_ne_soX : soN ≠ soX := by decide
@[simp] theorem so_soN_ne_soDm : soN ≠ soDm := by decide
@[simp] theorem so_soN_ne_soB : soN ≠ soB := by decide
@[simp] theorem so_soN_ne_soL : soN ≠ soL := by decide
@[simp] theorem so_soN_ne_soO : soN ≠ soO := by decide
@[simp] theorem so_soN_ne_soA2 : soN ≠ soA2 := by decide
@[simp] theorem so_soN_ne_soW : soN ≠ soW := by decide
@[simp] theorem so_soN_ne_soE0 : soN ≠ soE0 := by decide
@[simp] theorem so_soN_ne_soR : soN ≠ soR := by decide
@[simp] theorem so_soN_ne_kFu : soN ≠ kFu := by decide
@[simp] theorem so_kFu_ne_soN : kFu ≠ soN := by decide
@[simp] theorem so_soN_ne_kD : soN ≠ kD := by decide
@[simp] theorem so_kD_ne_soN : kD ≠ soN := by decide
@[simp] theorem so_soN_ne_lFl : soN ≠ lFl := by decide
@[simp] theorem so_lFl_ne_soN : lFl ≠ soN := by decide
@[simp] theorem so_soN_ne_lDh : soN ≠ lDh := by decide
@[simp] theorem so_lDh_ne_soN : lDh ≠ soN := by decide
@[simp] theorem so_soN_ne_lDt : soN ≠ lDt := by decide
@[simp] theorem so_lDt_ne_soN : lDt ≠ soN := by decide
@[simp] theorem so_soN_ne_lDg : soN ≠ lDg := by decide
@[simp] theorem so_lDg_ne_soN : lDg ≠ soN := by decide
@[simp] theorem so_soN_ne_lDi : soN ≠ lDi := by decide
@[simp] theorem so_lDi_ne_soN : lDi ≠ soN := by decide
@[simp] theorem so_soN_ne_lRp : soN ≠ lRp := by decide
@[simp] theorem so_lRp_ne_soN : lRp ≠ soN := by decide
@[simp] theorem so_soN_ne_lRn : soN ≠ lRn := by decide
@[simp] theorem so_lRn_ne_soN : lRn ≠ soN := by decide
@[simp] theorem so_soN_ne_lDir : soN ≠ lDir := by decide
@[simp] theorem so_lDir_ne_soN : lDir ≠ soN := by decide
@[simp] theorem so_soN_ne_lFle : soN ≠ lFle := by decide
@[simp] theorem so_lFle_ne_soN : lFle ≠ soN := by decide
@[simp] theorem so_soN_ne_lKb : soN ≠ lKb := by decide
@[simp] theorem so_lKb_ne_soN : lKb ≠ soN := by decide
@[simp] theorem so_soX_ne_soT : soX ≠ soT := by decide
@[simp] theorem so_soX_ne_soA : soX ≠ soA := by decide
@[simp] theorem so_soX_ne_soG : soX ≠ soG := by decide
@[simp] theorem so_soX_ne_soI : soX ≠ soI := by decide
@[simp] theorem so_soX_ne_soN : soX ≠ soN := by decide
@[simp] theorem so_soX_ne_soDm : soX ≠ soDm := by decide
@[simp] theorem so_soX_ne_soB : soX ≠ soB := by decide
@[simp] theorem so_soX_ne_soL : soX ≠ soL := by decide
@[simp] theorem so_soX_ne_soO : soX ≠ soO := by decide
@[simp] theorem so_soX_ne_soA2 : soX ≠ soA2 := by decide
@[simp] theorem so_soX_ne_soW : soX ≠ soW := by decide
@[simp] theorem so_soX_ne_soE0 : soX ≠ soE0 := by decide
@[simp] theorem so_soX_ne_soR : soX ≠ soR := by decide
@[simp] theorem so_soX_ne_kFu : soX ≠ kFu := by decide
@[simp] theorem so_kFu_ne_soX : kFu ≠ soX := by decide
@[simp] theorem so_soX_ne_kD : soX ≠ kD := by decide
@[simp] theorem so_kD_ne_soX : kD ≠ soX := by decide
@[simp] theorem so_soX_ne_lFl : soX ≠ lFl := by decide
@[simp] theorem so_lFl_ne_soX : lFl ≠ soX := by decide
@[simp] theorem so_soX_ne_lDh : soX ≠ lDh := by decide
@[simp] theorem so_lDh_ne_soX : lDh ≠ soX := by decide
@[simp] theorem so_soX_ne_lDt : soX ≠ lDt := by decide
@[simp] theorem so_lDt_ne_soX : lDt ≠ soX := by decide
@[simp] theorem so_soX_ne_lDg : soX ≠ lDg := by decide
@[simp] theorem so_lDg_ne_soX : lDg ≠ soX := by decide
@[simp] theorem so_soX_ne_lDi : soX ≠ lDi := by decide
@[simp] theorem so_lDi_ne_soX : lDi ≠ soX := by decide
@[simp] theorem so_soX_ne_lRp : soX ≠ lRp := by decide
@[simp] theorem so_lRp_ne_soX : lRp ≠ soX := by decide
@[simp] theorem so_soX_ne_lRn : soX ≠ lRn := by decide
@[simp] theorem so_lRn_ne_soX : lRn ≠ soX := by decide
@[simp] theorem so_soX_ne_lDir : soX ≠ lDir := by decide
@[simp] theorem so_lDir_ne_soX : lDir ≠ soX := by decide
@[simp] theorem so_soX_ne_lFle : soX ≠ lFle := by decide
@[simp] theorem so_lFle_ne_soX : lFle ≠ soX := by decide
@[simp] theorem so_soX_ne_lKb : soX ≠ lKb := by decide
@[simp] theorem so_lKb_ne_soX : lKb ≠ soX := by decide
@[simp] theorem so_soDm_ne_soT : soDm ≠ soT := by decide
@[simp] theorem so_soDm_ne_soA : soDm ≠ soA := by decide
@[simp] theorem so_soDm_ne_soG : soDm ≠ soG := by decide
@[simp] theorem so_soDm_ne_soI : soDm ≠ soI := by decide
@[simp] theorem so_soDm_ne_soN : soDm ≠ soN := by decide
@[simp] theorem so_soDm_ne_soX : soDm ≠ soX := by decide
@[simp] theorem so_soDm_ne_soB : soDm ≠ soB := by decide
@[simp] theorem so_soDm_ne_soL : soDm ≠ soL := by decide
@[simp] theorem so_soDm_ne_soO : soDm ≠ soO := by decide
@[simp] theorem so_soDm_ne_soA2 : soDm ≠ soA2 := by decide
@[simp] theorem so_soDm_ne_soW : soDm ≠ soW := by decide
@[simp] theorem so_soDm_ne_soE0 : soDm ≠ soE0 := by decide
@[simp] theorem so_soDm_ne_soR : soDm ≠ soR := by decide
@[simp] theorem so_soDm_ne_kFu : soDm ≠ kFu := by decide
@[simp] theorem so_kFu_ne_soDm : kFu ≠ soDm := by decide
@[simp] theorem so_soDm_ne_kD : soDm ≠ kD := by decide
@[simp] theorem so_kD_ne_soDm : kD ≠ soDm := by decide
@[simp] theorem so_soDm_ne_lFl : soDm ≠ lFl := by decide
@[simp] theorem so_lFl_ne_soDm : lFl ≠ soDm := by decide
@[simp] theorem so_soDm_ne_lDh : soDm ≠ lDh := by decide
@[simp] theorem so_lDh_ne_soDm : lDh ≠ soDm := by decide
@[simp] theorem so_soDm_ne_lDt : soDm ≠ lDt := by decide
@[simp] theorem so_lDt_ne_soDm : lDt ≠ soDm := by decide
@[simp] theorem so_soDm_ne_lDg : soDm ≠ lDg := by decide
@[simp] theorem so_lDg_ne_soDm : lDg ≠ soDm := by decide
@[simp] theorem so_soDm_ne_lDi : soDm ≠ lDi := by decide
@[simp] theorem so_lDi_ne_soDm : lDi ≠ soDm := by decide
@[simp] theorem so_soDm_ne_lRp : soDm ≠ lRp := by decide
@[simp] theorem so_lRp_ne_soDm : lRp ≠ soDm := by decide
@[simp] theorem so_soDm_ne_lRn : soDm ≠ lRn := by decide
@[simp] theorem so_lRn_ne_soDm : lRn ≠ soDm := by decide
@[simp] theorem so_soDm_ne_lDir : soDm ≠ lDir := by decide
@[simp] theorem so_lDir_ne_soDm : lDir ≠ soDm := by decide
@[simp] theorem so_soDm_ne_lFle : soDm ≠ lFle := by decide
@[simp] theorem so_lFle_ne_soDm : lFle ≠ soDm := by decide
@[simp] theorem so_soDm_ne_lKb : soDm ≠ lKb := by decide
@[simp] theorem so_lKb_ne_soDm : lKb ≠ soDm := by decide
@[simp] theorem so_soB_ne_soT : soB ≠ soT := by decide
@[simp] theorem so_soB_ne_soA : soB ≠ soA := by decide
@[simp] theorem so_soB_ne_soG : soB ≠ soG := by decide
@[simp] theorem so_soB_ne_soI : soB ≠ soI := by decide
@[simp] theorem so_soB_ne_soN : soB ≠ soN := by decide
@[simp] theorem so_soB_ne_soX : soB ≠ soX := by decide
@[simp] theorem so_soB_ne_soDm : soB ≠ soDm := by decide
@[simp] theorem so_soB_ne_soL : soB ≠ soL := by decide
@[simp] theorem so_soB_ne_soO : soB ≠ soO := by decide
@[simp] theorem so_soB_ne_soA2 : soB ≠ soA2 := by decide
@[simp] theorem so_soB_ne_soW : soB ≠ soW := by decide
@[simp] theorem so_soB_ne_soE0 : soB ≠ soE0 := by decide
@[simp] theorem so_soB_ne_soR : soB ≠ soR := by decide
@[simp] theorem so_soB_ne_kFu : soB ≠ kFu := by decide
@[simp] theorem so_kFu_ne_soB : kFu ≠ soB := by decide
@[simp] theorem so_soB_ne_kD : soB ≠ kD := by decide
@[simp] theorem so_kD_ne_soB : kD ≠ soB := by decide
@[simp] theorem so_soB_ne_lFl : soB ≠ lFl := by decide
@[simp] theorem so_lFl_ne_soB : lFl ≠ soB := by decide
@[simp] theorem so_soB_ne_lDh : soB ≠ lDh := by decide
@[simp] theorem so_lDh_ne_soB : lDh ≠ soB := by decide
@[simp] theorem so_soB_ne_lDt : soB ≠ lDt := by decide
@[simp] theorem so_lDt_ne_soB : lDt ≠ soB := by decide
@[simp] theorem so_soB_ne_lDg : soB ≠ lDg := by decide
@[simp] theorem so_lDg_ne_soB : lDg ≠ soB := by decide
@[simp] theorem so_soB_ne_lDi : soB ≠ lDi := by decide
@[simp] theorem so_lDi_ne_soB : lDi ≠ soB := by decide
@[simp] theorem so_soB_ne_lRp : soB ≠ lRp := by decide
@[simp] theorem so_lRp_ne_soB : lRp ≠ soB := by decide
@[simp] theorem so_soB_ne_lRn : soB ≠ lRn := by decide
@[simp] theorem so_lRn_ne_soB : lRn ≠ soB := by decide
@[simp] theorem so_soB_ne_lDir : soB ≠ lDir := by decide
@[simp] theorem so_lDir_ne_soB : lDir ≠ soB := by decide
@[simp] theorem so_soB_ne_lFle : soB ≠ lFle := by decide
@[simp] theorem so_lFle_ne_soB : lFle ≠ soB := by decide
@[simp] theorem so_soB_ne_lKb : soB ≠ lKb := by decide
@[simp] theorem so_lKb_ne_soB : lKb ≠ soB := by decide
@[simp] theorem so_soL_ne_soT : soL ≠ soT := by decide
@[simp] theorem so_soL_ne_soA : soL ≠ soA := by decide
@[simp] theorem so_soL_ne_soG : soL ≠ soG := by decide
@[simp] theorem so_soL_ne_soI : soL ≠ soI := by decide
@[simp] theorem so_soL_ne_soN : soL ≠ soN := by decide
@[simp] theorem so_soL_ne_soX : soL ≠ soX := by decide
@[simp] theorem so_soL_ne_soDm : soL ≠ soDm := by decide
@[simp] theorem so_soL_ne_soB : soL ≠ soB := by decide
@[simp] theorem so_soL_ne_soO : soL ≠ soO := by decide
@[simp] theorem so_soL_ne_soA2 : soL ≠ soA2 := by decide
@[simp] theorem so_soL_ne_soW : soL ≠ soW := by decide
@[simp] theorem so_soL_ne_soE0 : soL ≠ soE0 := by decide
@[simp] theorem so_soL_ne_soR : soL ≠ soR := by decide
@[simp] theorem so_soL_ne_kFu : soL ≠ kFu := by decide
@[simp] theorem so_kFu_ne_soL : kFu ≠ soL := by decide
@[simp] theorem so_soL_ne_kD : soL ≠ kD := by decide
@[simp] theorem so_kD_ne_soL : kD ≠ soL := by decide
@[simp] theorem so_soL_ne_lFl : soL ≠ lFl := by decide
@[simp] theorem so_lFl_ne_soL : lFl ≠ soL := by decide
@[simp] theorem so_soL_ne_lDh : soL ≠ lDh := by decide
@[simp] theorem so_lDh_ne_soL : lDh ≠ soL := by decide
@[simp] theorem so_soL_ne_lDt : soL ≠ lDt := by decide
@[simp] theorem so_lDt_ne_soL : lDt ≠ soL := by decide
@[simp] theorem so_soL_ne_lDg : soL ≠ lDg := by decide
@[simp] theorem so_lDg_ne_soL : lDg ≠ soL := by decide
@[simp] theorem so_soL_ne_lDi : soL ≠ lDi := by decide
@[simp] theorem so_lDi_ne_soL : lDi ≠ soL := by decide
@[simp] theorem so_soL_ne_lRp : soL ≠ lRp := by decide
@[simp] theorem so_lRp_ne_soL : lRp ≠ soL := by decide
@[simp] theorem so_soL_ne_lRn : soL ≠ lRn := by decide
@[simp] theorem so_lRn_ne_soL : lRn ≠ soL := by decide
@[simp] theorem so_soL_ne_lDir : soL ≠ lDir := by decide
@[simp] theorem so_lDir_ne_soL : lDir ≠ soL := by decide
@[simp] theorem so_soL_ne_lFle : soL ≠ lFle := by decide
@[simp] theorem so_lFle_ne_soL : lFle ≠ soL := by decide
@[simp] theorem so_soL_ne_lKb : soL ≠ lKb := by decide
@[simp] theorem so_lKb_ne_soL : lKb ≠ soL := by decide
@[simp] theorem so_soO_ne_soT : soO ≠ soT := by decide
@[simp] theorem so_soO_ne_soA : soO ≠ soA := by decide
@[simp] theorem so_soO_ne_soG : soO ≠ soG := by decide
@[simp] theorem so_soO_ne_soI : soO ≠ soI := by decide
@[simp] theorem so_soO_ne_soN : soO ≠ soN := by decide
@[simp] theorem so_soO_ne_soX : soO ≠ soX := by decide
@[simp] theorem so_soO_ne_soDm : soO ≠ soDm := by decide
@[simp] theorem so_soO_ne_soB : soO ≠ soB := by decide
@[simp] theorem so_soO_ne_soL : soO ≠ soL := by decide
@[simp] theorem so_soO_ne_soA2 : soO ≠ soA2 := by decide
@[simp] theorem so_soO_ne_soW : soO ≠ soW := by decide
@[simp] theorem so_soO_ne_soE0 : soO ≠ soE0 := by decide
@[simp] theorem so_soO_ne_soR : soO ≠ soR := by decide
@[simp] theorem so_soO_ne_kFu : soO ≠ kFu := by decide
@[simp] theorem so_kFu_ne_soO : kFu ≠ soO := by decide
@[simp] theorem so_soO_ne_kD : soO ≠ kD := by decide
@[simp] theorem so_kD_ne_soO : kD ≠ soO := by decide
@[simp] theorem so_soO_ne_lFl : soO ≠ lFl := by decide
@[simp] theorem so_lFl_ne_soO : lFl ≠ soO := by decide
@[simp] theorem so_soO_ne_lDh : soO ≠ lDh := by decide
@[simp] theorem so_lDh_ne_soO : lDh ≠ soO := by decide
@[simp] theorem so_soO_ne_lDt : soO ≠ lDt := by decide
@[simp] theorem so_lDt_ne_soO : lDt ≠ soO := by decide
@[simp] theorem so_soO_ne_lDg : soO ≠ lDg := by decide
@[simp] theorem so_lDg_ne_soO : lDg ≠ soO := by decide
@[simp] theorem so_soO_ne_lDi : soO ≠ lDi := by decide
@[simp] theorem so_lDi_ne_soO : lDi ≠ soO := by decide
@[simp] theorem so_soO_ne_lRp : soO ≠ lRp := by decide
@[simp] theorem so_lRp_ne_soO : lRp ≠ soO := by decide
@[simp] theorem so_soO_ne_lRn : soO ≠ lRn := by decide
@[simp] theorem so_lRn_ne_soO : lRn ≠ soO := by decide
@[simp] theorem so_soO_ne_lDir : soO ≠ lDir := by decide
@[simp] theorem so_lDir_ne_soO : lDir ≠ soO := by decide
@[simp] theorem so_soO_ne_lFle : soO ≠ lFle := by decide
@[simp] theorem so_lFle_ne_soO : lFle ≠ soO := by decide
@[simp] theorem so_soO_ne_lKb : soO ≠ lKb := by decide
@[simp] theorem so_lKb_ne_soO : lKb ≠ soO := by decide
@[simp] theorem so_soA2_ne_soT : soA2 ≠ soT := by decide
@[simp] theorem so_soA2_ne_soA : soA2 ≠ soA := by decide
@[simp] theorem so_soA2_ne_soG : soA2 ≠ soG := by decide
@[simp] theorem so_soA2_ne_soI : soA2 ≠ soI := by decide
@[simp] theorem so_soA2_ne_soN : soA2 ≠ soN := by decide
@[simp] theorem so_soA2_ne_soX : soA2 ≠ soX := by decide
@[simp] theorem so_soA2_ne_soDm : soA2 ≠ soDm := by decide
@[simp] theorem so_soA2_ne_soB : soA2 ≠ soB := by decide
@[simp] theorem so_soA2_ne_soL : soA2 ≠ soL := by decide
@[simp] theorem so_soA2_ne_soO : soA2 ≠ soO := by decide
@[simp] theorem so_soA2_ne_soW : soA2 ≠ soW := by decide
@[simp] theorem so_soA2_ne_soE0 : soA2 ≠ soE0 := by decide
@[simp] theorem so_soA2_ne_soR : soA2 ≠ soR := by decide
@[simp] theorem so_soA2_ne_kFu : soA2 ≠ kFu := by decide
@[simp] theorem so_kFu_ne_soA2 : kFu ≠ soA2 := by decide
@[simp] theorem so_soA2_ne_kD : soA2 ≠ kD := by decide
@[simp] theorem so_kD_ne_soA2 : kD ≠ soA2 := by decide
@[simp] theorem so_soA2_ne_lFl : soA2 ≠ lFl := by decide
@[simp] theorem so_lFl_ne_soA2 : lFl ≠ soA2 := by decide
@[simp] theorem so_soA2_ne_lDh : soA2 ≠ lDh := by decide
@[simp] theorem so_lDh_ne_soA2 : lDh ≠ soA2 := by decide
@[simp] theorem so_soA2_ne_lDt : soA2 ≠ lDt := by decide
@[simp] theorem so_lDt_ne_soA2 : lDt ≠ soA2 := by decide
@[simp] theorem so_soA2_ne_lDg : soA2 ≠ lDg := by decide
@[simp] theorem so_lDg_ne_soA2 : lDg ≠ soA2 := by decide
@[simp] theorem so_soA2_ne_lDi : soA2 ≠ lDi := by decide
@[simp] theorem so_lDi_ne_soA2 : lDi ≠ soA2 := by decide
@[simp] theorem so_soA2_ne_lRp : soA2 ≠ lRp := by decide
@[simp] theorem so_lRp_ne_soA2 : lRp ≠ soA2 := by decide
@[simp] theorem so_soA2_ne_lRn : soA2 ≠ lRn := by decide
@[simp] theorem so_lRn_ne_soA2 : lRn ≠ soA2 := by decide
@[simp] theorem so_soA2_ne_lDir : soA2 ≠ lDir := by decide
@[simp] theorem so_lDir_ne_soA2 : lDir ≠ soA2 := by decide
@[simp] theorem so_soA2_ne_lFle : soA2 ≠ lFle := by decide
@[simp] theorem so_lFle_ne_soA2 : lFle ≠ soA2 := by decide
@[simp] theorem so_soA2_ne_lKb : soA2 ≠ lKb := by decide
@[simp] theorem so_lKb_ne_soA2 : lKb ≠ soA2 := by decide
@[simp] theorem so_soW_ne_soT : soW ≠ soT := by decide
@[simp] theorem so_soW_ne_soA : soW ≠ soA := by decide
@[simp] theorem so_soW_ne_soG : soW ≠ soG := by decide
@[simp] theorem so_soW_ne_soI : soW ≠ soI := by decide
@[simp] theorem so_soW_ne_soN : soW ≠ soN := by decide
@[simp] theorem so_soW_ne_soX : soW ≠ soX := by decide
@[simp] theorem so_soW_ne_soDm : soW ≠ soDm := by decide
@[simp] theorem so_soW_ne_soB : soW ≠ soB := by decide
@[simp] theorem so_soW_ne_soL : soW ≠ soL := by decide
@[simp] theorem so_soW_ne_soO : soW ≠ soO := by decide
@[simp] theorem so_soW_ne_soA2 : soW ≠ soA2 := by decide
@[simp] theorem so_soW_ne_soE0 : soW ≠ soE0 := by decide
@[simp] theorem so_soW_ne_soR : soW ≠ soR := by decide
@[simp] theorem so_soW_ne_kFu : soW ≠ kFu := by decide
@[simp] theorem so_kFu_ne_soW : kFu ≠ soW := by decide
@[simp] theorem so_soW_ne_kD : soW ≠ kD := by decide
@[simp] theorem so_kD_ne_soW : kD ≠ soW := by decide
@[simp] theorem so_soW_ne_lFl : soW ≠ lFl := by decide
@[simp] theorem so_lFl_ne_soW : lFl ≠ soW := by decide
@[simp] theorem so_soW_ne_lDh : soW ≠ lDh := by decide
@[simp] theorem so_lDh_ne_soW : lDh ≠ soW := by decide
@[simp] theorem so_soW_ne_lDt : soW ≠ lDt := by decide
@[simp] theorem so_lDt_ne_soW : lDt ≠ soW := by decide
@[simp] theorem so_soW_ne_lDg : soW ≠ lDg := by decide
@[simp] theorem so_lDg_ne_soW : lDg ≠ soW := by decide
@[simp] theorem so_soW_ne_lDi : soW ≠ lDi := by decide
@[simp] theorem so_lDi_ne_soW : lDi ≠ soW := by decide
@[simp] theorem so_soW_ne_lRp : soW ≠ lRp := by decide
@[simp] theorem so_lRp_ne_soW : lRp ≠ soW := by decide
@[simp] theorem so_soW_ne_lRn : soW ≠ lRn := by decide
@[simp] theorem so_lRn_ne_soW : lRn ≠ soW := by decide
@[simp] theorem so_soW_ne_lDir : soW ≠ lDir := by decide
@[simp] theorem so_lDir_ne_soW : lDir ≠ soW := by decide
@[simp] theorem so_soW_ne_lFle : soW ≠ lFle := by decide
@[simp] theorem so_lFle_ne_soW : lFle ≠ soW := by decide
@[simp] theorem so_soW_ne_lKb : soW ≠ lKb := by decide
@[simp] theorem so_lKb_ne_soW : lKb ≠ soW := by decide
@[simp] theorem so_soE0_ne_soT : soE0 ≠ soT := by decide
@[simp] theorem so_soE0_ne_soA : soE0 ≠ soA := by decide
@[simp] theorem so_soE0_ne_soG : soE0 ≠ soG := by decide
@[simp] theorem so_soE0_ne_soI : soE0 ≠ soI := by decide
@[simp] theorem so_soE0_ne_soN : soE0 ≠ soN := by decide
@[simp] theorem so_soE0_ne_soX : soE0 ≠ soX := by decide
@[simp] theorem so_soE0_ne_soDm : soE0 ≠ soDm := by decide
@[simp] theorem so_soE0_ne_soB : soE0 ≠ soB := by decide
@[simp] theorem so_soE0_ne_soL : soE0 ≠ soL := by decide
@[simp] theorem so_soE0_ne_soO : soE0 ≠ soO := by decide
@[simp] theorem so_soE0_ne_soA2 : soE0 ≠ soA2 := by decide
@[simp] theorem so_soE0_ne_soW : soE0 ≠ soW := by decide
@[simp] theorem so_soE0_ne_soR : soE0 ≠ soR := by decide
@[simp] theorem so_soE0_ne_kFu : soE0 ≠ kFu := by decide
@[simp] theorem so_kFu_ne_soE0 : kFu ≠ soE0 := by decide
@[simp] theorem so_soE0_ne_kD : soE0 ≠ kD := by decide
@[simp] theorem so_kD_ne_soE0 : kD ≠ soE0 := by decide
@[simp] theorem so_soE0_ne_lFl : soE0 ≠ lFl := by decide
@[simp] theorem so_lFl_ne_soE0 : lFl ≠ soE0 := by decide
@[simp] theorem so_soE0_ne_lDh : soE0 ≠ lDh := by decide
@[simp] theorem so_lDh_ne_soE0 : lDh ≠ soE0 := by decide
@[simp] theorem so_soE0_ne_lDt : soE0 ≠ lDt := by decide
@[simp] theorem so_lDt_ne_soE0 : lDt ≠ soE0 := by decide
@[simp] theorem so_soE0_ne_lDg : soE0 ≠ lDg := by decide
@[simp] theorem so_lDg_ne_soE0 : lDg ≠ soE0 := by decide
@[simp] theorem so_soE0_ne_lDi : soE0 ≠ lDi := by decide
@[simp] theorem so_lDi_ne_soE0 : lDi ≠ soE0 := by decide
@[simp] theorem so_soE0_ne_lRp : soE0 ≠ lRp := by decide
@[simp] theorem so_lRp_ne_soE0 : lRp ≠ soE0 := by decide
@[simp] theorem so_soE0_ne_lRn : soE0 ≠ lRn := by decide
@[simp] theorem so_lRn_ne_soE0 : lRn ≠ soE0 := by decide
@[simp] theorem so_soE0_ne_lDir : soE0 ≠ lDir := by decide
@[simp] theorem so_lDir_ne_soE0 : lDir ≠ soE0 := by decide
@[simp] theorem so_soE0_ne_lFle : soE0 ≠ lFle := by decide
@[simp] theorem so_lFle_ne_soE0 : lFle ≠ soE0 := by decide
@[simp] theorem so_soE0_ne_lKb : soE0 ≠ lKb := by decide
@[simp] theorem so_lKb_ne_soE0 : lKb ≠ soE0 := by decide
@[simp] theorem so_soR_ne_soT : soR ≠ soT := by decide
@[simp] theorem so_soR_ne_soA : soR ≠ soA := by decide
@[simp] theorem so_soR_ne_soG : soR ≠ soG := by decide
@[simp] theorem so_soR_ne_soI : soR ≠ soI := by decide
@[simp] theorem so_soR_ne_soN : soR ≠ soN := by decide
@[simp] theorem so_soR_ne_soX : soR ≠ soX := by decide
@[simp] theorem so_soR_ne_soDm : soR ≠ soDm := by decide
@[simp] theorem so_soR_ne_soB : soR ≠ soB := by decide
@[simp] theorem so_soR_ne_soL : soR ≠ soL := by decide
@[simp] theorem so_soR_ne_soO : soR ≠ soO := by decide
@[simp] theorem so_soR_ne_soA2 : soR ≠ soA2 := by decide
@[simp] theorem so_soR_ne_soW : soR ≠ soW := by decide
@[simp] theorem so_soR_ne_soE0 : soR ≠ soE0 := by decide
@[simp] theorem so_soR_ne_kFu : soR ≠ kFu := by decide
@[simp] theorem so_kFu_ne_soR : kFu ≠ soR := by decide
@[simp] theorem so_soR_ne_kD : soR ≠ kD := by decide
@[simp] theorem so_kD_ne_soR : kD ≠ soR := by decide
@[simp] theorem so_soR_ne_lFl : soR ≠ lFl := by decide
@[simp] theorem so_lFl_ne_soR : lFl ≠ soR := by decide
@[simp] theorem so_soR_ne_lDh : soR ≠ lDh := by decide
@[simp] theorem so_lDh_ne_soR : lDh ≠ soR := by decide
@[simp] theorem so_soR_ne_lDt : soR ≠ lDt := by decide
@[simp] theorem so_lDt_ne_soR : lDt ≠ soR := by decide
@[simp] theorem so_soR_ne_lDg : soR ≠ lDg := by decide
@[simp] theorem so_lDg_ne_soR : lDg ≠ soR := by decide
@[simp] theorem so_soR_ne_lDi : soR ≠ lDi := by decide
@[simp] theorem so_lDi_ne_soR : lDi ≠ soR := by decide
@[simp] theorem so_soR_ne_lRp : soR ≠ lRp := by decide
@[simp] theorem so_lRp_ne_soR : lRp ≠ soR := by decide
@[simp] theorem so_soR_ne_lRn : soR ≠ lRn := by decide
@[simp] theorem so_lRn_ne_soR : lRn ≠ soR := by decide
@[simp] theorem so_soR_ne_lDir : soR ≠ lDir := by decide
@[simp] theorem so_lDir_ne_soR : lDir ≠ soR := by decide
@[simp] theorem so_soR_ne_lFle : soR ≠ lFle := by decide
@[simp] theorem so_lFle_ne_soR : lFle ≠ soR := by decide
@[simp] theorem so_soR_ne_lKb : soR ≠ lKb := by decide
@[simp] theorem so_lKb_ne_soR : lKb ≠ soR := by decide

def soParams : List MlS := [kFu, kD, soT, soA, soG, soI, soN]
def soLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, soX, soDm, soB, soL, soO, soA2, soW, soE0, soR]

def soRec : ProgHOL 64 :=
  .seq (.call (some (some (.local, soR), none)) fSo
    [vv kFu, vv kD, vv soB, vv soA2, vv soG, .op .add [vv soI, .const 1], vv soN]) (.return (vv soR))

def soBody (C : Ctx) : ProgHOL 64 := prologue soLocals
  (.ite (.cmp .lower (vv soI) (vv soN)) (.seq (.assign .local soX (.load .one (.op .add [vv soG, .op .add [.panop .mul [vv soI, .const 8], .const 8]]))) (.ite (tagIsE soT 6) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv soT)) (.seq eViewP (.seq (.assign .local soDm (.load .one (vv lRp))) (.seq (.assign .local soB (.load .one (.op .add [(vv lRp), (.const 8)]))) (.seq (.call (some (some (.local, soA2), none)) ExPre.fAppend [(vv soA), (vv soX)]) soRec)))))) (.seq (.assign .local soL (.load .one (vv soA))) (.seq (.call (some (some (.local, soO), none)) ExQ.fIrr [(vv soA), (.const 0), (vv soL), (.const (BitVec.ofNat 64 coreWalkFuel)), (vv soT), (.const 0)]) (.seq (.call (some (some (.local, soW), none)) fW [(vv kFu), (vv kD), (vv soO)]) (.ite (tagIsE soW 6) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv soW)) (.seq eViewP (.seq (.assign .local soDm (.load .one (vv lRp))) (.seq (.assign .local soB (.load .one (.op .add [(vv lRp), (.const 8)]))) (allocP C soE0 (.const 8) (.seq (.store (vv soE0) (.const 0)) (.seq (.call (some (some (.local, soA2), none)) ExPre.fAppend [(vv soE0), (vv soX)]) soRec)))))))) hang)))))) (.seq (.assign .local soL (.load .one (vv soA))) (.seq (.call (some (some (.local, soO), none)) ExQ.fIrr [(vv soA), (.const 0), (vv soL), (.const (BitVec.ofNat 64 coreWalkFuel)), (vv soT), (.const 0)]) (.return (vv soO)))))

section
variable {σ : Type}

theorem so_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ soLocals → (ctxEnv C ++ soParams.zip vals).get x = none :=
  Knot.params_none C soLocals soParams vals (by decide) (by decide)

structure SoCodes (C : Ctx) : Prop where
  w : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one)
  irr : C.code.lookup ExQ.fIrr = some (ExQ.irrParams.map (fun p => (p, ShapeHOL.one)), ExQ.irrBody C, .one)
  q : ExQ.CodesQ C
  app : C.code.lookup ExPre.fAppend = some (ExPre.appParams.map (fun p => (p, ShapeHOL.one)), ExPre.appBody C, .one)
  self : C.code.lookup fSo = some (soParams.map (fun p => (p, ShapeHOL.one)), soBody C, .one)

theorem so_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (hc : SoCodes C)
    (hW : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d' e')
      (PostK (ctxH C H)))
    (d : Nat) (args : List EIdx) (og : Nat) (H0 : List (BitVec 64)) (hp0 : C.H <+: H0)
    (hga : BlkAt H0 og (args.map Enc.idxW)) (hsz : args.length < 2 ^ 58) :
    ∀ m (ty : EIdx) (acc : List EIdx) (oa i : Nat) (H : List (BitVec 64)) (s : AState), H0 <+: H →
      BlkAt H oa (acc.map Enc.idxW) → acc.length ≤ i → args.length - i = m → i ≤ args.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (soParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty, cellA C oa,
        cellA C og, BitVec.ofNat 64 i, BitVec.ofNat 64 args.length])) (soBody C) s
        (inferSpineIO (knot mode C n) C.fe d ty acc.toArray args.toArray i) (PostK (ctxH C H)) := by
  intro m
  induction m with
  | zero =>
    intro ty acc oa i H s hp hba hai hk hi
    refine specR_prologue (postK_locals _) (so_none _ _) ?_
    rw [inferSpineIO, dif_neg (by simp; omega)]
    have hlw := word_lt_iff i args.length (by unfold B; omega) (by unfold B; omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, soParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
      (not_congr hlw).mpr (by omega)]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_congr (m' := instantiateListFast coreWalkFuel ty acc.toArray 0 >>= fun r => pure r) (by simp) ?_
    obtain ⟨hlo, hlv0⟩ := blkAt_get0 hba
    refine UD.specR_heapLoadI' (C := ctxH C H) soL (vv soA) oa (BitVec.ofNat 64 acc.length)
      (by show H[oa]? = _; rw [List.getElem?_eq_getElem hlo, hlv0]; simp) (by decide) (by simp +decide [Env.get, soParams, ctxEnv] <;> rfl) ?_
    simp only [instantiateListFast, List.size_toArray, bind_assoc]
    refine ILP.callE_spec (C := ctxH C H) soO ExQ.fIrr ExQ.irrParams
      [vv soA, .const 0, vv soL, .const (BitVec.ofNat 64 coreWalkFuel), vv soT, .const 0] (ExQ.irrBody C)
      [cellA C oa, BitVec.ofNat 64 0, BitVec.ofNat 64 acc.length, BitVec.ofNat 64 coreWalkFuel, Enc.idxW ty,
        BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.irr
      ⟨by simp +decide [Env.get, soParams, ctxEnv] <;> rfl, rfl, by simp, rfl, by simp +decide [Env.get, soParams, ctxEnv], rfl, trivial⟩
      (ExQ.irr_spec ra (ctxH C H) (ctxOK_H hok H) (codesQ_H hc.q H) acc.toArray oa
        (show BlkAt H oa (acc.toArray.toList.map Enc.idxW) by simpa using hba) (by simp; omega) s
        coreWalkFuel 0 acc.length 0 ty CV.coreWalkFuel_lt (by decide) (by omega) (by decide)) (fun r s1 => ?_)
    exact specR_returnI _ (Enc.idxW r) (by simp)
      (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ m ih =>
    intro ty acc oa i H s hp hba hai hk hi
    have hlt : i < args.length := by omega
    refine specR_prologue (postK_locals _) (so_none _ _) ?_
    rw [inferSpineIO, dif_pos (by simpa using hlt)]
    have hlw := word_lt_iff i args.length (by unfold B; omega) (by unfold B; omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, soParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
      hlw.mpr hlt]) (fun _ => ?_) (fun h => absurd h (by decide))
    have hga' := blkAt_mono hga hp
    have hxi : (ctxH C H).H[og + 1 + i]? = some (Enc.idxW args[i]) := by
      have := hga'.2 i (by simp; omega); simp at this; exact this
    refine UD.specR_heapLoadI' (C := ctxH C H) soX _ (og + 1 + i) _ hxi (by decide)
      (by simp +decide [sev, Env.get, soParams, ctxEnv]; exact cellA_idx C og i) ?_
    simp only [List.getElem_toArray]
    refine Knot.specR_tagIteV soT ty 6 (by decide) (by decide) (by simp +decide [Env.get, soParams, ctxEnv]) (fun htg => ?_) (fun htg => ?_)
    · rw [if_pos (show (ty.tag == ETag.forallE) = true by simp [htg, ETag.forallE])]
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv soT) (Enc.idxW ty) (by decide) (by simp +decide [Env.get, soParams, ctxEnv]) ?_
      refine specR_viewP (C := ctxH C H) ty (by simp) (by simp +decide [Env.get] <;> rfl)
        (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
      have h6 : v.tagN = 6 := by rw [htn, htg]; rfl
      obtain ⟨dom, b, rfl⟩ : ∃ dom b, v = .forallE dom b := by cases v <;> simp [ENodeView.tagN] at h6 ⊢
      have hvb : s.store.viewBind ty = some (dom, b) := viewBind_of_view_forallE (by rw [htg]; rfl) hv
      refine specR_runBind (by rw [viewBind_run, hvb]) ?_
      dsimp only
      refine specR_loadI' soDm (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW dom) (by decide) (by simp) (by simp)
        (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW dom) [Enc.idxW b] []) ?_
      refine specR_loadI' soB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW dom) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      refine ExPre.specR_callApp (C := ctxH C H) (ctxOK_H hok H) hc.app soA2 (vv soA) (vv soX) oa
        (acc.map Enc.idxW) (Enc.idxW args[i]) (by decide) hba (by simp +decide [Env.get, soParams, ctxEnv] <;> rfl) (by simp)
        (fun H4 o4 hp4 hb4 => ?_)
      have hb4' : BlkAt H4 o4 ((acc ++ [args[i]]).map Enc.idxW) := by simpa using hb4
      have hpall : H <+: H4 := hp4
      rw [show acc.toArray.push args[i] = (acc ++ [args[i]]).toArray by simp]
      unfold soRec
      refine specR_congr (m' := inferSpineIO (knot mode C n) C.fe d b (acc ++ [args[i]]).toArray args.toArray (i + 1)
        >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H4) soR fSo soParams
        [vv kFu, vv kD, vv soB, vv soA2, vv soG, .op .add [vv soI, .const 1], vv soN] (soBody C)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW b, cellA C o4, cellA C og, BitVec.ofNat 64 (i + 1),
          BitVec.ofNat 64 args.length] (by decide) rfl (by decide) hc.self
        ⟨by simp +decide [Env.get, soParams, ctxEnv], by simp +decide [Env.get, soParams, ctxEnv], by simp, by simp <;> rfl, by simp +decide [Env.get, soParams, ctxEnv] <;> rfl,
          by simp +decide [sev, Env.get, soParams, ctxEnv]; exact word_add1_eq i, by simp +decide [Env.get, soParams, ctxEnv], trivial⟩
        (PostK (ctxH C H4)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu soParams _ rfl hlk)
          (ih b (acc ++ [args[i]]) o4 (i + 1) H4 s (hp.trans hpall) hb4' (by simp; omega) (by omega) (by omega)))
        (fun r w s9 H9 hp9 hw => ?_)
      subst hw
      exact specR_returnI _ (Enc.idxW r) (by simp)
        (fun t ht => ⟨H9, hpall.trans hp9, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · rw [if_neg (show ¬ (ty.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg)]
      obtain ⟨hlo, hlv0⟩ := blkAt_get0 hba
      refine UD.specR_heapLoadI' (C := ctxH C H) soL (vv soA) oa (BitVec.ofNat 64 acc.length)
        (by show H[oa]? = _; rw [List.getElem?_eq_getElem hlo, hlv0]; simp) (by decide) (by simp +decide [Env.get, soParams, ctxEnv] <;> rfl) ?_
      simp only [instantiateListFast, List.size_toArray, bind_assoc]
      refine ILP.callE_spec (C := ctxH C H) soO ExQ.fIrr ExQ.irrParams
        [vv soA, .const 0, vv soL, .const (BitVec.ofNat 64 coreWalkFuel), vv soT, .const 0] (ExQ.irrBody C)
        [cellA C oa, BitVec.ofNat 64 0, BitVec.ofNat 64 acc.length, BitVec.ofNat 64 coreWalkFuel, Enc.idxW ty,
          BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.irr
        ⟨by simp +decide [Env.get, soParams, ctxEnv] <;> rfl, rfl, by simp, rfl, by simp +decide [Env.get, soParams, ctxEnv], rfl, trivial⟩
        (ExQ.irr_spec ra (ctxH C H) (ctxOK_H hok H) (codesQ_H hc.q H) acc.toArray oa
          (show BlkAt H oa (acc.toArray.toList.map Enc.idxW) by simpa using hba) (by simp; omega) s
          coreWalkFuel 0 acc.length 0 ty CV.coreWalkFuel_lt (by decide) (by omega) (by decide)) (fun ty2 s1 => ?_)
      refine Big.specR_callKC (C := ctxH C H) soW fW kParams [vv kFu, vv kD, vv soO] (whnfE C fWB)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty2] (by decide) rfl (by decide) hc.w
        ⟨by simp +decide [Env.get, soParams, ctxEnv], by simp +decide [Env.get, soParams, ctxEnv], by simp, trivial⟩ (hW H s1 d ty2 (hp0.trans hp)) (fun w s2 H2 hp2 _ => ?_)
      refine Knot.specR_tagIteV soW w 6 (by decide) (by decide) (by simp) (fun htg2 => ?_) (fun htg2 => ?_)
      swap
      · rw [if_neg (show ¬ (w.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg2)]
        exact specR_hangI
      rw [if_pos (show (w.tag == ETag.forallE) = true by simp [htg2, ETag.forallE])]
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv soW) (Enc.idxW w) (by decide) (by simp +decide [Env.get, soParams, ctxEnv]) ?_
      refine specR_viewP (C := ctxH C H2) w (by simp) (by simp +decide [Env.get] <;> rfl)
        (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
      have h6 : v.tagN = 6 := by rw [htn, htg2]; rfl
      obtain ⟨dom, b, rfl⟩ : ∃ dom b, v = .forallE dom b := by cases v <;> simp [ENodeView.tagN] at h6 ⊢
      have hvb : s2.store.viewBind w = some (dom, b) := viewBind_of_view_forallE (by rw [htg2]; rfl) hv
      refine specR_runBind (by rw [viewBind_run, hvb]) ?_
      dsimp only
      refine specR_loadI' soDm (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW dom) (by decide) (by simp) (by simp)
        (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW dom) [Enc.idxW b] []) ?_
      refine specR_loadI' soB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW dom) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      refine specR_emptyBlk (C0 := C) hok (H := H2) soE0 (by decide) (fun H5 oe hp5 hbe => ?_)
      refine ExPre.specR_callApp (C := ctxH C H5) (ctxOK_H hok H5) hc.app soA2 (vv soE0) (vv soX) oe
        [] (Enc.idxW args[i]) (by decide) hbe (by simp <;> rfl) (by simp) (fun H6 o6 hp6 hb6 => ?_)
      have hb6' : BlkAt H6 o6 ([args[i]].map Enc.idxW) := by simpa using hb6
      have hpall : H <+: H6 := hp2.trans (hp5.trans hp6)
      unfold soRec
      refine specR_congr (m' := inferSpineIO (knot mode C n) C.fe d b [args[i]].toArray args.toArray (i + 1)
        >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H6) soR fSo soParams
        [vv kFu, vv kD, vv soB, vv soA2, vv soG, .op .add [vv soI, .const 1], vv soN] (soBody C)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW b, cellA C o6, cellA C og, BitVec.ofNat 64 (i + 1),
          BitVec.ofNat 64 args.length] (by decide) rfl (by decide) hc.self
        ⟨by simp +decide [Env.get, soParams, ctxEnv], by simp +decide [Env.get, soParams, ctxEnv], by simp, by simp <;> rfl, by simp +decide [Env.get, soParams, ctxEnv] <;> rfl,
          by simp +decide [sev, Env.get, soParams, ctxEnv]; exact word_add1_eq i, by simp +decide [Env.get, soParams, ctxEnv], trivial⟩
        (PostK (ctxH C H6)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu soParams _ rfl hlk)
          (ih b [args[i]] o6 (i + 1) H6 s2 (hp.trans hpall) hb6' (by simp <;> omega) (by omega) (by omega)))
        (fun r w s9 H9 hp9 hw => ?_)
      subst hw
      exact specR_returnI _ (Enc.idxW r) (by simp)
        (fun t ht => ⟨H9, hpall.trans hp9, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
