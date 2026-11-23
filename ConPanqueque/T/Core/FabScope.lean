import ConPanqueque.T.Core.FvarLeaves
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `fabScopeOk`: the rescue's scope guard

Every free variable of the fabrication below the depth (`wscopedBGo` from the empty memo), no loose bound
variable (`looseBVarsBounded` at `0`), and the leaf guard: a fabrication with free variables has every reachable
leaf among the major's (`fvarLeavesGo` on the major from empty lists, `leavesSubGo` from the empty memo).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def fsW := ofString "fso_w"
def fsR := ofString "fso_r"
def fsV := ofString "fso_v"
def fsB := ofString "fso_b"
def fsL := ofString "fso_l"
def fsA := ofString "fso_a"
def fsZ := ofString "fso_z"
def fsZr := ofString "fso_zr"

@[simp] theorem fso_fsW_ne_fsR : fsW ≠ fsR := by decide
@[simp] theorem fso_fsW_ne_fsV : fsW ≠ fsV := by decide
@[simp] theorem fso_fsW_ne_fsB : fsW ≠ fsB := by decide
@[simp] theorem fso_fsW_ne_fsL : fsW ≠ fsL := by decide
@[simp] theorem fso_fsW_ne_fsA : fsW ≠ fsA := by decide
@[simp] theorem fso_fsW_ne_fsZ : fsW ≠ fsZ := by decide
@[simp] theorem fso_fsW_ne_fsZr : fsW ≠ fsZr := by decide
@[simp] theorem fso_fsW_ne_lKb : fsW ≠ lKb := by decide
@[simp] theorem fso_fsW_ne_lFl : fsW ≠ lFl := by decide
@[simp] theorem fso_fsW_ne_lDh : fsW ≠ lDh := by decide
@[simp] theorem fso_fsW_ne_lDt : fsW ≠ lDt := by decide
@[simp] theorem fso_fsW_ne_lDg : fsW ≠ lDg := by decide
@[simp] theorem fso_fsW_ne_lDi : fsW ≠ lDi := by decide
@[simp] theorem fso_fsW_ne_lDo1 : fsW ≠ lDo1 := by decide
@[simp] theorem fso_fsW_ne_lDo2 : fsW ≠ lDo2 := by decide
@[simp] theorem fso_fsW_ne_lFle : fsW ≠ lFle := by decide
@[simp] theorem fso_fsW_ne_lDir : fsW ≠ lDir := by decide
@[simp] theorem fso_fsW_ne_kD : fsW ≠ kD := by decide
@[simp] theorem fso_fsW_ne_fbF : fsW ≠ fbF := by decide
@[simp] theorem fso_fsW_ne_fbM : fsW ≠ fbM := by decide
@[simp] theorem fso_fsR_ne_fsW : fsR ≠ fsW := by decide
@[simp] theorem fso_fsR_ne_fsV : fsR ≠ fsV := by decide
@[simp] theorem fso_fsR_ne_fsB : fsR ≠ fsB := by decide
@[simp] theorem fso_fsR_ne_fsL : fsR ≠ fsL := by decide
@[simp] theorem fso_fsR_ne_fsA : fsR ≠ fsA := by decide
@[simp] theorem fso_fsR_ne_fsZ : fsR ≠ fsZ := by decide
@[simp] theorem fso_fsR_ne_fsZr : fsR ≠ fsZr := by decide
@[simp] theorem fso_fsR_ne_lKb : fsR ≠ lKb := by decide
@[simp] theorem fso_fsR_ne_lFl : fsR ≠ lFl := by decide
@[simp] theorem fso_fsR_ne_lDh : fsR ≠ lDh := by decide
@[simp] theorem fso_fsR_ne_lDt : fsR ≠ lDt := by decide
@[simp] theorem fso_fsR_ne_lDg : fsR ≠ lDg := by decide
@[simp] theorem fso_fsR_ne_lDi : fsR ≠ lDi := by decide
@[simp] theorem fso_fsR_ne_lDo1 : fsR ≠ lDo1 := by decide
@[simp] theorem fso_fsR_ne_lDo2 : fsR ≠ lDo2 := by decide
@[simp] theorem fso_fsR_ne_lFle : fsR ≠ lFle := by decide
@[simp] theorem fso_fsR_ne_lDir : fsR ≠ lDir := by decide
@[simp] theorem fso_fsR_ne_kD : fsR ≠ kD := by decide
@[simp] theorem fso_fsR_ne_fbF : fsR ≠ fbF := by decide
@[simp] theorem fso_fsR_ne_fbM : fsR ≠ fbM := by decide
@[simp] theorem fso_fsV_ne_fsW : fsV ≠ fsW := by decide
@[simp] theorem fso_fsV_ne_fsR : fsV ≠ fsR := by decide
@[simp] theorem fso_fsV_ne_fsB : fsV ≠ fsB := by decide
@[simp] theorem fso_fsV_ne_fsL : fsV ≠ fsL := by decide
@[simp] theorem fso_fsV_ne_fsA : fsV ≠ fsA := by decide
@[simp] theorem fso_fsV_ne_fsZ : fsV ≠ fsZ := by decide
@[simp] theorem fso_fsV_ne_fsZr : fsV ≠ fsZr := by decide
@[simp] theorem fso_fsV_ne_lKb : fsV ≠ lKb := by decide
@[simp] theorem fso_fsV_ne_lFl : fsV ≠ lFl := by decide
@[simp] theorem fso_fsV_ne_lDh : fsV ≠ lDh := by decide
@[simp] theorem fso_fsV_ne_lDt : fsV ≠ lDt := by decide
@[simp] theorem fso_fsV_ne_lDg : fsV ≠ lDg := by decide
@[simp] theorem fso_fsV_ne_lDi : fsV ≠ lDi := by decide
@[simp] theorem fso_fsV_ne_lDo1 : fsV ≠ lDo1 := by decide
@[simp] theorem fso_fsV_ne_lDo2 : fsV ≠ lDo2 := by decide
@[simp] theorem fso_fsV_ne_lFle : fsV ≠ lFle := by decide
@[simp] theorem fso_fsV_ne_lDir : fsV ≠ lDir := by decide
@[simp] theorem fso_fsV_ne_kD : fsV ≠ kD := by decide
@[simp] theorem fso_fsV_ne_fbF : fsV ≠ fbF := by decide
@[simp] theorem fso_fsV_ne_fbM : fsV ≠ fbM := by decide
@[simp] theorem fso_fsB_ne_fsW : fsB ≠ fsW := by decide
@[simp] theorem fso_fsB_ne_fsR : fsB ≠ fsR := by decide
@[simp] theorem fso_fsB_ne_fsV : fsB ≠ fsV := by decide
@[simp] theorem fso_fsB_ne_fsL : fsB ≠ fsL := by decide
@[simp] theorem fso_fsB_ne_fsA : fsB ≠ fsA := by decide
@[simp] theorem fso_fsB_ne_fsZ : fsB ≠ fsZ := by decide
@[simp] theorem fso_fsB_ne_fsZr : fsB ≠ fsZr := by decide
@[simp] theorem fso_fsB_ne_lKb : fsB ≠ lKb := by decide
@[simp] theorem fso_fsB_ne_lFl : fsB ≠ lFl := by decide
@[simp] theorem fso_fsB_ne_lDh : fsB ≠ lDh := by decide
@[simp] theorem fso_fsB_ne_lDt : fsB ≠ lDt := by decide
@[simp] theorem fso_fsB_ne_lDg : fsB ≠ lDg := by decide
@[simp] theorem fso_fsB_ne_lDi : fsB ≠ lDi := by decide
@[simp] theorem fso_fsB_ne_lDo1 : fsB ≠ lDo1 := by decide
@[simp] theorem fso_fsB_ne_lDo2 : fsB ≠ lDo2 := by decide
@[simp] theorem fso_fsB_ne_lFle : fsB ≠ lFle := by decide
@[simp] theorem fso_fsB_ne_lDir : fsB ≠ lDir := by decide
@[simp] theorem fso_fsB_ne_kD : fsB ≠ kD := by decide
@[simp] theorem fso_fsB_ne_fbF : fsB ≠ fbF := by decide
@[simp] theorem fso_fsB_ne_fbM : fsB ≠ fbM := by decide
@[simp] theorem fso_fsL_ne_fsW : fsL ≠ fsW := by decide
@[simp] theorem fso_fsL_ne_fsR : fsL ≠ fsR := by decide
@[simp] theorem fso_fsL_ne_fsV : fsL ≠ fsV := by decide
@[simp] theorem fso_fsL_ne_fsB : fsL ≠ fsB := by decide
@[simp] theorem fso_fsL_ne_fsA : fsL ≠ fsA := by decide
@[simp] theorem fso_fsL_ne_fsZ : fsL ≠ fsZ := by decide
@[simp] theorem fso_fsL_ne_fsZr : fsL ≠ fsZr := by decide
@[simp] theorem fso_fsL_ne_lKb : fsL ≠ lKb := by decide
@[simp] theorem fso_fsL_ne_lFl : fsL ≠ lFl := by decide
@[simp] theorem fso_fsL_ne_lDh : fsL ≠ lDh := by decide
@[simp] theorem fso_fsL_ne_lDt : fsL ≠ lDt := by decide
@[simp] theorem fso_fsL_ne_lDg : fsL ≠ lDg := by decide
@[simp] theorem fso_fsL_ne_lDi : fsL ≠ lDi := by decide
@[simp] theorem fso_fsL_ne_lDo1 : fsL ≠ lDo1 := by decide
@[simp] theorem fso_fsL_ne_lDo2 : fsL ≠ lDo2 := by decide
@[simp] theorem fso_fsL_ne_lFle : fsL ≠ lFle := by decide
@[simp] theorem fso_fsL_ne_lDir : fsL ≠ lDir := by decide
@[simp] theorem fso_fsL_ne_kD : fsL ≠ kD := by decide
@[simp] theorem fso_fsL_ne_fbF : fsL ≠ fbF := by decide
@[simp] theorem fso_fsL_ne_fbM : fsL ≠ fbM := by decide
@[simp] theorem fso_fsA_ne_fsW : fsA ≠ fsW := by decide
@[simp] theorem fso_fsA_ne_fsR : fsA ≠ fsR := by decide
@[simp] theorem fso_fsA_ne_fsV : fsA ≠ fsV := by decide
@[simp] theorem fso_fsA_ne_fsB : fsA ≠ fsB := by decide
@[simp] theorem fso_fsA_ne_fsL : fsA ≠ fsL := by decide
@[simp] theorem fso_fsA_ne_fsZ : fsA ≠ fsZ := by decide
@[simp] theorem fso_fsA_ne_fsZr : fsA ≠ fsZr := by decide
@[simp] theorem fso_fsA_ne_lKb : fsA ≠ lKb := by decide
@[simp] theorem fso_fsA_ne_lFl : fsA ≠ lFl := by decide
@[simp] theorem fso_fsA_ne_lDh : fsA ≠ lDh := by decide
@[simp] theorem fso_fsA_ne_lDt : fsA ≠ lDt := by decide
@[simp] theorem fso_fsA_ne_lDg : fsA ≠ lDg := by decide
@[simp] theorem fso_fsA_ne_lDi : fsA ≠ lDi := by decide
@[simp] theorem fso_fsA_ne_lDo1 : fsA ≠ lDo1 := by decide
@[simp] theorem fso_fsA_ne_lDo2 : fsA ≠ lDo2 := by decide
@[simp] theorem fso_fsA_ne_lFle : fsA ≠ lFle := by decide
@[simp] theorem fso_fsA_ne_lDir : fsA ≠ lDir := by decide
@[simp] theorem fso_fsA_ne_kD : fsA ≠ kD := by decide
@[simp] theorem fso_fsA_ne_fbF : fsA ≠ fbF := by decide
@[simp] theorem fso_fsA_ne_fbM : fsA ≠ fbM := by decide
@[simp] theorem fso_fsZ_ne_fsW : fsZ ≠ fsW := by decide
@[simp] theorem fso_fsZ_ne_fsR : fsZ ≠ fsR := by decide
@[simp] theorem fso_fsZ_ne_fsV : fsZ ≠ fsV := by decide
@[simp] theorem fso_fsZ_ne_fsB : fsZ ≠ fsB := by decide
@[simp] theorem fso_fsZ_ne_fsL : fsZ ≠ fsL := by decide
@[simp] theorem fso_fsZ_ne_fsA : fsZ ≠ fsA := by decide
@[simp] theorem fso_fsZ_ne_fsZr : fsZ ≠ fsZr := by decide
@[simp] theorem fso_fsZ_ne_lKb : fsZ ≠ lKb := by decide
@[simp] theorem fso_fsZ_ne_lFl : fsZ ≠ lFl := by decide
@[simp] theorem fso_fsZ_ne_lDh : fsZ ≠ lDh := by decide
@[simp] theorem fso_fsZ_ne_lDt : fsZ ≠ lDt := by decide
@[simp] theorem fso_fsZ_ne_lDg : fsZ ≠ lDg := by decide
@[simp] theorem fso_fsZ_ne_lDi : fsZ ≠ lDi := by decide
@[simp] theorem fso_fsZ_ne_lDo1 : fsZ ≠ lDo1 := by decide
@[simp] theorem fso_fsZ_ne_lDo2 : fsZ ≠ lDo2 := by decide
@[simp] theorem fso_fsZ_ne_lFle : fsZ ≠ lFle := by decide
@[simp] theorem fso_fsZ_ne_lDir : fsZ ≠ lDir := by decide
@[simp] theorem fso_fsZ_ne_kD : fsZ ≠ kD := by decide
@[simp] theorem fso_fsZ_ne_fbF : fsZ ≠ fbF := by decide
@[simp] theorem fso_fsZ_ne_fbM : fsZ ≠ fbM := by decide
@[simp] theorem fso_fsZr_ne_fsW : fsZr ≠ fsW := by decide
@[simp] theorem fso_fsZr_ne_fsR : fsZr ≠ fsR := by decide
@[simp] theorem fso_fsZr_ne_fsV : fsZr ≠ fsV := by decide
@[simp] theorem fso_fsZr_ne_fsB : fsZr ≠ fsB := by decide
@[simp] theorem fso_fsZr_ne_fsL : fsZr ≠ fsL := by decide
@[simp] theorem fso_fsZr_ne_fsA : fsZr ≠ fsA := by decide
@[simp] theorem fso_fsZr_ne_fsZ : fsZr ≠ fsZ := by decide
@[simp] theorem fso_fsZr_ne_lKb : fsZr ≠ lKb := by decide
@[simp] theorem fso_fsZr_ne_lFl : fsZr ≠ lFl := by decide
@[simp] theorem fso_fsZr_ne_lDh : fsZr ≠ lDh := by decide
@[simp] theorem fso_fsZr_ne_lDt : fsZr ≠ lDt := by decide
@[simp] theorem fso_fsZr_ne_lDg : fsZr ≠ lDg := by decide
@[simp] theorem fso_fsZr_ne_lDi : fsZr ≠ lDi := by decide
@[simp] theorem fso_fsZr_ne_lDo1 : fsZr ≠ lDo1 := by decide
@[simp] theorem fso_fsZr_ne_lDo2 : fsZr ≠ lDo2 := by decide
@[simp] theorem fso_fsZr_ne_lFle : fsZr ≠ lFle := by decide
@[simp] theorem fso_fsZr_ne_lDir : fsZr ≠ lDir := by decide
@[simp] theorem fso_fsZr_ne_kD : fsZr ≠ kD := by decide
@[simp] theorem fso_fsZr_ne_fbF : fsZr ≠ fbF := by decide
@[simp] theorem fso_fsZr_ne_fbM : fsZr ≠ fbM := by decide
@[simp] theorem fso_lKb_ne_fsW : lKb ≠ fsW := by decide
@[simp] theorem fso_lKb_ne_fsR : lKb ≠ fsR := by decide
@[simp] theorem fso_lKb_ne_fsV : lKb ≠ fsV := by decide
@[simp] theorem fso_lKb_ne_fsB : lKb ≠ fsB := by decide
@[simp] theorem fso_lKb_ne_fsL : lKb ≠ fsL := by decide
@[simp] theorem fso_lKb_ne_fsA : lKb ≠ fsA := by decide
@[simp] theorem fso_lKb_ne_fsZ : lKb ≠ fsZ := by decide
@[simp] theorem fso_lKb_ne_fsZr : lKb ≠ fsZr := by decide
@[simp] theorem fso_lFl_ne_fsW : lFl ≠ fsW := by decide
@[simp] theorem fso_lFl_ne_fsR : lFl ≠ fsR := by decide
@[simp] theorem fso_lFl_ne_fsV : lFl ≠ fsV := by decide
@[simp] theorem fso_lFl_ne_fsB : lFl ≠ fsB := by decide
@[simp] theorem fso_lFl_ne_fsL : lFl ≠ fsL := by decide
@[simp] theorem fso_lFl_ne_fsA : lFl ≠ fsA := by decide
@[simp] theorem fso_lFl_ne_fsZ : lFl ≠ fsZ := by decide
@[simp] theorem fso_lFl_ne_fsZr : lFl ≠ fsZr := by decide
@[simp] theorem fso_lDh_ne_fsW : lDh ≠ fsW := by decide
@[simp] theorem fso_lDh_ne_fsR : lDh ≠ fsR := by decide
@[simp] theorem fso_lDh_ne_fsV : lDh ≠ fsV := by decide
@[simp] theorem fso_lDh_ne_fsB : lDh ≠ fsB := by decide
@[simp] theorem fso_lDh_ne_fsL : lDh ≠ fsL := by decide
@[simp] theorem fso_lDh_ne_fsA : lDh ≠ fsA := by decide
@[simp] theorem fso_lDh_ne_fsZ : lDh ≠ fsZ := by decide
@[simp] theorem fso_lDh_ne_fsZr : lDh ≠ fsZr := by decide
@[simp] theorem fso_lDt_ne_fsW : lDt ≠ fsW := by decide
@[simp] theorem fso_lDt_ne_fsR : lDt ≠ fsR := by decide
@[simp] theorem fso_lDt_ne_fsV : lDt ≠ fsV := by decide
@[simp] theorem fso_lDt_ne_fsB : lDt ≠ fsB := by decide
@[simp] theorem fso_lDt_ne_fsL : lDt ≠ fsL := by decide
@[simp] theorem fso_lDt_ne_fsA : lDt ≠ fsA := by decide
@[simp] theorem fso_lDt_ne_fsZ : lDt ≠ fsZ := by decide
@[simp] theorem fso_lDt_ne_fsZr : lDt ≠ fsZr := by decide
@[simp] theorem fso_lDg_ne_fsW : lDg ≠ fsW := by decide
@[simp] theorem fso_lDg_ne_fsR : lDg ≠ fsR := by decide
@[simp] theorem fso_lDg_ne_fsV : lDg ≠ fsV := by decide
@[simp] theorem fso_lDg_ne_fsB : lDg ≠ fsB := by decide
@[simp] theorem fso_lDg_ne_fsL : lDg ≠ fsL := by decide
@[simp] theorem fso_lDg_ne_fsA : lDg ≠ fsA := by decide
@[simp] theorem fso_lDg_ne_fsZ : lDg ≠ fsZ := by decide
@[simp] theorem fso_lDg_ne_fsZr : lDg ≠ fsZr := by decide
@[simp] theorem fso_lDi_ne_fsW : lDi ≠ fsW := by decide
@[simp] theorem fso_lDi_ne_fsR : lDi ≠ fsR := by decide
@[simp] theorem fso_lDi_ne_fsV : lDi ≠ fsV := by decide
@[simp] theorem fso_lDi_ne_fsB : lDi ≠ fsB := by decide
@[simp] theorem fso_lDi_ne_fsL : lDi ≠ fsL := by decide
@[simp] theorem fso_lDi_ne_fsA : lDi ≠ fsA := by decide
@[simp] theorem fso_lDi_ne_fsZ : lDi ≠ fsZ := by decide
@[simp] theorem fso_lDi_ne_fsZr : lDi ≠ fsZr := by decide
@[simp] theorem fso_lDo1_ne_fsW : lDo1 ≠ fsW := by decide
@[simp] theorem fso_lDo1_ne_fsR : lDo1 ≠ fsR := by decide
@[simp] theorem fso_lDo1_ne_fsV : lDo1 ≠ fsV := by decide
@[simp] theorem fso_lDo1_ne_fsB : lDo1 ≠ fsB := by decide
@[simp] theorem fso_lDo1_ne_fsL : lDo1 ≠ fsL := by decide
@[simp] theorem fso_lDo1_ne_fsA : lDo1 ≠ fsA := by decide
@[simp] theorem fso_lDo1_ne_fsZ : lDo1 ≠ fsZ := by decide
@[simp] theorem fso_lDo1_ne_fsZr : lDo1 ≠ fsZr := by decide
@[simp] theorem fso_lDo2_ne_fsW : lDo2 ≠ fsW := by decide
@[simp] theorem fso_lDo2_ne_fsR : lDo2 ≠ fsR := by decide
@[simp] theorem fso_lDo2_ne_fsV : lDo2 ≠ fsV := by decide
@[simp] theorem fso_lDo2_ne_fsB : lDo2 ≠ fsB := by decide
@[simp] theorem fso_lDo2_ne_fsL : lDo2 ≠ fsL := by decide
@[simp] theorem fso_lDo2_ne_fsA : lDo2 ≠ fsA := by decide
@[simp] theorem fso_lDo2_ne_fsZ : lDo2 ≠ fsZ := by decide
@[simp] theorem fso_lDo2_ne_fsZr : lDo2 ≠ fsZr := by decide
@[simp] theorem fso_lFle_ne_fsW : lFle ≠ fsW := by decide
@[simp] theorem fso_lFle_ne_fsR : lFle ≠ fsR := by decide
@[simp] theorem fso_lFle_ne_fsV : lFle ≠ fsV := by decide
@[simp] theorem fso_lFle_ne_fsB : lFle ≠ fsB := by decide
@[simp] theorem fso_lFle_ne_fsL : lFle ≠ fsL := by decide
@[simp] theorem fso_lFle_ne_fsA : lFle ≠ fsA := by decide
@[simp] theorem fso_lFle_ne_fsZ : lFle ≠ fsZ := by decide
@[simp] theorem fso_lFle_ne_fsZr : lFle ≠ fsZr := by decide
@[simp] theorem fso_lDir_ne_fsW : lDir ≠ fsW := by decide
@[simp] theorem fso_lDir_ne_fsR : lDir ≠ fsR := by decide
@[simp] theorem fso_lDir_ne_fsV : lDir ≠ fsV := by decide
@[simp] theorem fso_lDir_ne_fsB : lDir ≠ fsB := by decide
@[simp] theorem fso_lDir_ne_fsL : lDir ≠ fsL := by decide
@[simp] theorem fso_lDir_ne_fsA : lDir ≠ fsA := by decide
@[simp] theorem fso_lDir_ne_fsZ : lDir ≠ fsZ := by decide
@[simp] theorem fso_lDir_ne_fsZr : lDir ≠ fsZr := by decide
@[simp] theorem fso_kD_ne_fsW : kD ≠ fsW := by decide
@[simp] theorem fso_kD_ne_fsR : kD ≠ fsR := by decide
@[simp] theorem fso_kD_ne_fsV : kD ≠ fsV := by decide
@[simp] theorem fso_kD_ne_fsB : kD ≠ fsB := by decide
@[simp] theorem fso_kD_ne_fsL : kD ≠ fsL := by decide
@[simp] theorem fso_kD_ne_fsA : kD ≠ fsA := by decide
@[simp] theorem fso_kD_ne_fsZ : kD ≠ fsZ := by decide
@[simp] theorem fso_kD_ne_fsZr : kD ≠ fsZr := by decide
@[simp] theorem fso_fbF_ne_fsW : fbF ≠ fsW := by decide
@[simp] theorem fso_fbF_ne_fsR : fbF ≠ fsR := by decide
@[simp] theorem fso_fbF_ne_fsV : fbF ≠ fsV := by decide
@[simp] theorem fso_fbF_ne_fsB : fbF ≠ fsB := by decide
@[simp] theorem fso_fbF_ne_fsL : fbF ≠ fsL := by decide
@[simp] theorem fso_fbF_ne_fsA : fbF ≠ fsA := by decide
@[simp] theorem fso_fbF_ne_fsZ : fbF ≠ fsZ := by decide
@[simp] theorem fso_fbF_ne_fsZr : fbF ≠ fsZr := by decide
@[simp] theorem fso_fbM_ne_fsW : fbM ≠ fsW := by decide
@[simp] theorem fso_fbM_ne_fsR : fbM ≠ fsR := by decide
@[simp] theorem fso_fbM_ne_fsV : fbM ≠ fsV := by decide
@[simp] theorem fso_fbM_ne_fsB : fbM ≠ fsB := by decide
@[simp] theorem fso_fbM_ne_fsL : fbM ≠ fsL := by decide
@[simp] theorem fso_fbM_ne_fsA : fbM ≠ fsA := by decide
@[simp] theorem fso_fbM_ne_fsZ : fbM ≠ fsZ := by decide
@[simp] theorem fso_fbM_ne_fsZr : fbM ≠ fsZr := by decide

def fsoLocals : List MlS := [fsW, fsR, fsV, lFl, lDh, lDt, lDg, lDi, lDo1, lDo2, fsB, fsL, fsA, fsZ, fsZr]

def fsoCore : ProgHOL 64 :=
  .seq (.call (some (some (.local, fsW), none)) fWs [.const (BitVec.ofNat 64 coreWalkFuel), vv kD, vv fbF, .const 0])
  (.seq (.assign .local fsR (.load .one (vv fsW)))
  (.ite (.cmp .equal (vv fsR) (.const 0)) (.return (.const 0))
  (.seq (.call (some (some (.local, fsV), none)) ExM.fLBB [.const (BitVec.ofNat 64 coreWalkFuel), .const 0, vv fbF])
  (.ite (.cmp .equal (vv fsV) (.const 0)) (.return (.const 0))
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv fbF)) (.seq (storeDerived 9 10)
  (.seq (.assign .local fsB (.op .and [.shift .lsr (vv lDo1) (.const 1), .const 32767]))
  (.ite (.cmp .equal (vv fsB) (.const 0)) (.return (.const 1))
  (.seq (.call (some (some (.local, fsL), none)) fFl [.const (BitVec.ofNat 64 coreWalkFuel), .const 0, vv fbM, .const 0])
  (.seq (.assign .local fsA (.load .one (vv fsL)))
  (.seq (.call (some (some (.local, fsZ), none)) fLz [.const (BitVec.ofNat 64 coreWalkFuel), vv fsA, vv fbF, .const 0])
  (.seq (.assign .local fsZr (.load .one (vv fsZ))) (.return (vv fsZr)))))))))))))))

def fsoBody : ProgHOL 64 := prologue fsoLocals fsoCore

structure FsoCodes (C : Ctx) : Prop where
  ws : WsCodes C
  wsf : C.code.lookup fWs = some (wsParams.map (fun p => (p, ShapeHOL.one)), wsBody C, .one)
  lbb : C.code.lookup ExM.fLBB = some ([(pFu, .one), (ExM.pKb, .one), (pH, .one)], ExM.lbbBody, .one)
  cb : ExB.CodesB C (ExB.bodyB C)
  bvb : C.code.lookup ExB.fBvarB = some ([(pFu, .one), (pH, .one)], ExB.bvbBody C, .one)
  fl : FlCodes C
  lz : LzCodes C

section
variable {σ : Type}

theorem fso_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ fsoLocals → (ctxEnv C ++ fbParams.zip vals).get x = none :=
  Knot.params_none C fsoLocals fbParams vals (by decide) (by decide)

theorem fso_spec (C : Ctx) (hok : CtxOK C) (hc : FsoCodes C) (d : Nat) (hd : d < 2 ^ 63) :
    ∀ (H : List (BitVec 64)) (s : AState) (f mj : EIdx), C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (fbParams.zip [BitVec.ofNat 64 d, Enc.idxW f, Enc.idxW mj])) fsoBody s
        (fabScopeOk d f mj) (PostB (ctxH C H)) := by
  intro H s f mj hp
  refine specR_prologue (postB_locals _) (fso_none _ _) ?_
  unfold fsoCore fabScopeOk wscopedBFast
  simp only [bind_assoc, pure_bind]
  refine specR_callNIH (C := ctxH C H) fsW fWs wsParams [.const (BitVec.ofNat 64 coreWalkFuel), vv kD, vv fbF, .const 0]
    (wsBody C) [BitVec.ofNat 64 coreWalkFuel, BitVec.ofNat 64 d, Enc.idxW f, 0] (by decide) rfl (by decide) hc.wsf
    ⟨rfl, by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, fbParams, ctxEnv], by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, fbParams, ctxEnv], rfl, trivial⟩
    (PostWs (ctxH C H) s) (fun rm w s' H' => s' = s ∧ ∃ o pm, w = cellA C o ∧ H'[o]? = some (boolW rm.1) ∧
      H'[o + 1]? = some pm)
    (fun rm w s' st ⟨h1, H', o, pm, hp', hw, h0, h1', _, hsr⟩ => ⟨H', hp', ⟨h1, o, pm, hw, h0, h1'⟩, by subst h1; exact hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu wsParams _ rfl hlk)
      (ws_spec C hok hc.ws coreWalkFuel CV.coreWalkFuel_lt d f ∅ H s 0 hp hd (wsRep_empty C H)))
    (fun rm w s1 H1 hp1 ⟨hs1, o, pm, hw, h0, h1'⟩ => ?_)
  subst hs1 hw
  obtain ⟨r1, m1⟩ := rm
  refine UD.specR_heapLoadI' (C := ctxH C H1) fsR (vv fsW) o (boolW r1) h0 (by decide) (by simp [Env.get]; rfl) ?_
  dsimp only
  cases r1
  · refine specR_ifI _ 1 (by simp [sev, Env.get, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    simp only [Bool.not_false, ↓reduceIte]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 0 (by simp [sev, Env.get, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
    (fun _ => ?_)
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hp1' : C.H <+: H1 := hp.trans hp1
  refine specR_callNIH (C := ctxH C H1) fsV ExM.fLBB [pFu, ExM.pKb, pH]
    [.const (BitVec.ofNat 64 coreWalkFuel), .const 0, vv fbF] ExM.lbbBody
    [BitVec.ofNat 64 coreWalkFuel, BitVec.ofNat 64 0, Enc.idxW f] (by decide) rfl (by decide) hc.lbb
    ⟨rfl, rfl, by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, fbParams, ctxEnv], trivial⟩
    (ExM.PostB (ctxH C H1)) (fun b w s' H' => w = boolW b ∧ H' = H1)
    (fun b w s' st ⟨hw, hsr⟩ => ⟨H1, List.prefix_refl _, ⟨hw, rfl⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, ExM.pKb, pH] _ rfl hlk)
      (ExM.lbb_spec (ctxH C H1) (ctxOK_H hok H1) ⟨hc.cb.bvr, hc.cb.memoGet, hc.cb.memoProbe, hc.cb.memoSet, hc.cb.memoIns⟩
        hc.bvb s1 coreWalkFuel 0 f CV.coreWalkFuel_lt (by decide)))
    (fun b2 w s2 H2 _ ⟨hw, hH2⟩ => ?_)
  subst hw; subst H2
  cases b2
  · refine specR_ifI _ 1 (by simp [sev, Env.get, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    simp only [Bool.not_false, ↓reduceIte]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 0 (by simp [sev, Env.get, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
    (fun _ => ?_)
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  unfold leafGuard fvarLeavesFast
  simp only [bind_assoc, pure_bind]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv fbF) (Enc.idxW f) (by decide) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, fbParams, ctxEnv]) ?_
  refine specR_derivedEI (C := ctxH C H1) f (by simp) (by simp <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) ?_
  have hb15 : (ConLeche.fvarOfData (s2.store.derived f)).toNat < 2 ^ 15 := by
    simp only [ConLeche.fvarOfData, UInt64.toNat_mod]; simp; omega
  have hbt : (ConLeche.fvarOfData (s2.store.derived f)).toBitVec =
      BitVec.ofNat 64 (ConLeche.fvarOfData (s2.store.derived f)).toNat := by
    apply BitVec.eq_of_toNat_eq; simp
  refine specR_assignI fsB _ (ConLeche.fvarOfData (s2.store.derived f)).toBitVec (by decide)
    (by simp [sev]; exact ExF.fvarOfData_word _) ?_
  generalize hbdef : (ConLeche.fvarOfData (s2.store.derived f)).toNat = b at hb15 hbt
  rw [hbt]
  by_cases hb0 : b = 0
  · subst hb0
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    simp only [beq_self_eq_true, ↓reduceIte]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  have hbne : BitVec.ofNat 64 b ≠ 0 := by intro e; have := congrArg BitVec.toNat e; simp at this; omega
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hbne) (fun h => absurd rfl h)
    (fun _ => ?_)
  simp only [show (b == 0) = false by simpa using hb0, Bool.false_eq_true, ↓reduceIte]
  refine specR_callNIH (C := ctxH C H1) fsL fFl flParams
    [.const (BitVec.ofNat 64 coreWalkFuel), .const 0, vv fbM, .const 0] (flBody C)
    [BitVec.ofNat 64 coreWalkFuel, 0, Enc.idxW mj, 0] (by decide) rfl (by decide) hc.fl.self
    ⟨rfl, rfl, by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, fbParams, ctxEnv], rfl, trivial⟩
    (PostFl (ctxH C H1) s2)
    (fun as w s' H' => s' = s2 ∧ ∃ o pa ps, w = cellA C o ∧ H'[o]? = some pa ∧ H'[o + 1]? = some ps ∧
      AccRep C H' pa as.1)
    (fun as w s' st ⟨h1, H', o, pa, ps, hp', hw, h0, h1', ha, _, hsr⟩ =>
      ⟨H', hp', ⟨h1, o, pa, ps, hw, h0, h1', accRep_ofH ha⟩, by subst h1; exact hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu flParams _ rfl hlk)
      (fl_spec C hok hc.fl coreWalkFuel CV.coreWalkFuel_lt [] ∅ mj H1 s2 0 0 hp1' ⟨rfl, by simp⟩ (seenRep_empty C H1)))
    (fun as w s3 H3 hp3 ⟨hs3, o3, pa, ps, hw, h0, h1', ha3⟩ => ?_)
  subst hs3 hw
  obtain ⟨acc, seen⟩ := as
  refine UD.specR_heapLoadI' (C := ctxH C H3) fsA (vv fsL) o3 pa h0 (by decide) (by simp [Env.get]; rfl) ?_
  dsimp only
  have hp13 : C.H <+: H3 := hp1'.trans hp3
  refine specR_callNIH (C := ctxH C H3) fsZ fLz lzParams
    [.const (BitVec.ofNat 64 coreWalkFuel), vv fsA, vv fbF, .const 0] (lzBody C)
    [BitVec.ofNat 64 coreWalkFuel, pa, Enc.idxW f, 0] (by decide) rfl (by decide) hc.lz.self
    ⟨rfl, by simp [Env.get], by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, fbParams, ctxEnv], rfl, trivial⟩
    (PostLb (ctxH (ctxH C H3) H3) s3) (fun rm w s' H' => s' = s3 ∧ ∃ o, w = cellA C o ∧ H'[o]? = some (boolW rm.1))
    (fun rm w s' st ⟨h1, H', o, pm, hp', hw, h0, _, _, hsr⟩ => ⟨H', hp', ⟨h1, o, hw, h0⟩, by subst h1; exact hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu lzParams _ rfl hlk)
      (lz_spec (ctxH C H3) (ctxOK_H hok H3) ⟨hc.lz.ml, hc.lz.self⟩ acc pa (accRep_toH ha3) coreWalkFuel
        CV.coreWalkFuel_lt f ∅ H3 s3 0 (List.prefix_refl _) (lbRep_empty _ _)))
    (fun rm w s4 H4 hp4 ⟨hs4, o4, hw, h4⟩ => ?_)
  subst hs4 hw
  refine UD.specR_heapLoadI' (C := ctxH C H4) fsZr (vv fsZ) o4 (boolW rm.1) h4 (by decide) (by simp [Env.get]; rfl) ?_
  exact specR_returnI _ (boolW rm.1) (by simp [Env.get])
    (fun t ht => ⟨H4, hp1.trans (hp3.trans hp4), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
