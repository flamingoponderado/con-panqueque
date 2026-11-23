import ConPanqueque.T.Core.DeltaHeads
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `deltaQuick` and `tryUnfoldProjApp`

A lazy-delta step's outcome as a word (`dsW`): `unknown` 0, `eq` 1, `diff` 2, `cont a b` a fresh two-cell
block `[a, b]` (a heap address, at least `2^32`). `deltaQuick` is `quickDefEq` on the new pair;
`tryUnfoldProjApp` the FULL `whnfCore` of a projection-headed term, `some` when it changed (`optW`).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def dqA := ofString "dqkdq_a"
def dqB := ofString "dqkdq_b"
def dqQ := ofString "dqkdq_q"
def dqW := ofString "dqkdq_w"
def tuE := ofString "dqktu_e"
def tuX := ofString "dqktu_x"
def tuY := ofString "dqktu_y"
def fDq := ofString "deltaQuick"
def fTu := ofString "tryUnfoldProjApp"

@[simp] theorem dqk_dqA_ne_dqB : dqA ≠ dqB := by decide
@[simp] theorem dqk_dqA_ne_dqQ : dqA ≠ dqQ := by decide
@[simp] theorem dqk_dqA_ne_dqW : dqA ≠ dqW := by decide
@[simp] theorem dqk_dqA_ne_tuE : dqA ≠ tuE := by decide
@[simp] theorem dqk_dqA_ne_tuX : dqA ≠ tuX := by decide
@[simp] theorem dqk_dqA_ne_tuY : dqA ≠ tuY := by decide
@[simp] theorem dqk_dqA_ne_lFl : dqA ≠ lFl := by decide
@[simp] theorem dqk_lFl_ne_dqA : lFl ≠ dqA := by decide
@[simp] theorem dqk_dqA_ne_lDh : dqA ≠ lDh := by decide
@[simp] theorem dqk_lDh_ne_dqA : lDh ≠ dqA := by decide
@[simp] theorem dqk_dqA_ne_lDt : dqA ≠ lDt := by decide
@[simp] theorem dqk_lDt_ne_dqA : lDt ≠ dqA := by decide
@[simp] theorem dqk_dqA_ne_lDg : dqA ≠ lDg := by decide
@[simp] theorem dqk_lDg_ne_dqA : lDg ≠ dqA := by decide
@[simp] theorem dqk_dqA_ne_lDi : dqA ≠ lDi := by decide
@[simp] theorem dqk_lDi_ne_dqA : lDi ≠ dqA := by decide
@[simp] theorem dqk_dqA_ne_lRp : dqA ≠ lRp := by decide
@[simp] theorem dqk_lRp_ne_dqA : lRp ≠ dqA := by decide
@[simp] theorem dqk_dqA_ne_lRn : dqA ≠ lRn := by decide
@[simp] theorem dqk_lRn_ne_dqA : lRn ≠ dqA := by decide
@[simp] theorem dqk_dqA_ne_lFle : dqA ≠ lFle := by decide
@[simp] theorem dqk_lFle_ne_dqA : lFle ≠ dqA := by decide
@[simp] theorem dqk_dqA_ne_lKb : dqA ≠ lKb := by decide
@[simp] theorem dqk_lKb_ne_dqA : lKb ≠ dqA := by decide
@[simp] theorem dqk_dqA_ne_lDir : dqA ≠ lDir := by decide
@[simp] theorem dqk_lDir_ne_dqA : lDir ≠ dqA := by decide
@[simp] theorem dqk_dqA_ne_lFln : dqA ≠ lFln := by decide
@[simp] theorem dqk_lFln_ne_dqA : lFln ≠ dqA := by decide
@[simp] theorem dqk_dqA_ne_lFll : dqA ≠ lFll := by decide
@[simp] theorem dqk_lFll_ne_dqA : lFll ≠ dqA := by decide
@[simp] theorem dqk_dqA_ne_lFls : dqA ≠ lFls := by decide
@[simp] theorem dqk_lFls_ne_dqA : lFls ≠ dqA := by decide
@[simp] theorem dqk_dqA_ne_kFu : dqA ≠ kFu := by decide
@[simp] theorem dqk_kFu_ne_dqA : kFu ≠ dqA := by decide
@[simp] theorem dqk_dqA_ne_kD : dqA ≠ kD := by decide
@[simp] theorem dqk_kD_ne_dqA : kD ≠ dqA := by decide
@[simp] theorem dqk_dqB_ne_dqA : dqB ≠ dqA := by decide
@[simp] theorem dqk_dqB_ne_dqQ : dqB ≠ dqQ := by decide
@[simp] theorem dqk_dqB_ne_dqW : dqB ≠ dqW := by decide
@[simp] theorem dqk_dqB_ne_tuE : dqB ≠ tuE := by decide
@[simp] theorem dqk_dqB_ne_tuX : dqB ≠ tuX := by decide
@[simp] theorem dqk_dqB_ne_tuY : dqB ≠ tuY := by decide
@[simp] theorem dqk_dqB_ne_lFl : dqB ≠ lFl := by decide
@[simp] theorem dqk_lFl_ne_dqB : lFl ≠ dqB := by decide
@[simp] theorem dqk_dqB_ne_lDh : dqB ≠ lDh := by decide
@[simp] theorem dqk_lDh_ne_dqB : lDh ≠ dqB := by decide
@[simp] theorem dqk_dqB_ne_lDt : dqB ≠ lDt := by decide
@[simp] theorem dqk_lDt_ne_dqB : lDt ≠ dqB := by decide
@[simp] theorem dqk_dqB_ne_lDg : dqB ≠ lDg := by decide
@[simp] theorem dqk_lDg_ne_dqB : lDg ≠ dqB := by decide
@[simp] theorem dqk_dqB_ne_lDi : dqB ≠ lDi := by decide
@[simp] theorem dqk_lDi_ne_dqB : lDi ≠ dqB := by decide
@[simp] theorem dqk_dqB_ne_lRp : dqB ≠ lRp := by decide
@[simp] theorem dqk_lRp_ne_dqB : lRp ≠ dqB := by decide
@[simp] theorem dqk_dqB_ne_lRn : dqB ≠ lRn := by decide
@[simp] theorem dqk_lRn_ne_dqB : lRn ≠ dqB := by decide
@[simp] theorem dqk_dqB_ne_lFle : dqB ≠ lFle := by decide
@[simp] theorem dqk_lFle_ne_dqB : lFle ≠ dqB := by decide
@[simp] theorem dqk_dqB_ne_lKb : dqB ≠ lKb := by decide
@[simp] theorem dqk_lKb_ne_dqB : lKb ≠ dqB := by decide
@[simp] theorem dqk_dqB_ne_lDir : dqB ≠ lDir := by decide
@[simp] theorem dqk_lDir_ne_dqB : lDir ≠ dqB := by decide
@[simp] theorem dqk_dqB_ne_lFln : dqB ≠ lFln := by decide
@[simp] theorem dqk_lFln_ne_dqB : lFln ≠ dqB := by decide
@[simp] theorem dqk_dqB_ne_lFll : dqB ≠ lFll := by decide
@[simp] theorem dqk_lFll_ne_dqB : lFll ≠ dqB := by decide
@[simp] theorem dqk_dqB_ne_lFls : dqB ≠ lFls := by decide
@[simp] theorem dqk_lFls_ne_dqB : lFls ≠ dqB := by decide
@[simp] theorem dqk_dqB_ne_kFu : dqB ≠ kFu := by decide
@[simp] theorem dqk_kFu_ne_dqB : kFu ≠ dqB := by decide
@[simp] theorem dqk_dqB_ne_kD : dqB ≠ kD := by decide
@[simp] theorem dqk_kD_ne_dqB : kD ≠ dqB := by decide
@[simp] theorem dqk_dqQ_ne_dqA : dqQ ≠ dqA := by decide
@[simp] theorem dqk_dqQ_ne_dqB : dqQ ≠ dqB := by decide
@[simp] theorem dqk_dqQ_ne_dqW : dqQ ≠ dqW := by decide
@[simp] theorem dqk_dqQ_ne_tuE : dqQ ≠ tuE := by decide
@[simp] theorem dqk_dqQ_ne_tuX : dqQ ≠ tuX := by decide
@[simp] theorem dqk_dqQ_ne_tuY : dqQ ≠ tuY := by decide
@[simp] theorem dqk_dqQ_ne_lFl : dqQ ≠ lFl := by decide
@[simp] theorem dqk_lFl_ne_dqQ : lFl ≠ dqQ := by decide
@[simp] theorem dqk_dqQ_ne_lDh : dqQ ≠ lDh := by decide
@[simp] theorem dqk_lDh_ne_dqQ : lDh ≠ dqQ := by decide
@[simp] theorem dqk_dqQ_ne_lDt : dqQ ≠ lDt := by decide
@[simp] theorem dqk_lDt_ne_dqQ : lDt ≠ dqQ := by decide
@[simp] theorem dqk_dqQ_ne_lDg : dqQ ≠ lDg := by decide
@[simp] theorem dqk_lDg_ne_dqQ : lDg ≠ dqQ := by decide
@[simp] theorem dqk_dqQ_ne_lDi : dqQ ≠ lDi := by decide
@[simp] theorem dqk_lDi_ne_dqQ : lDi ≠ dqQ := by decide
@[simp] theorem dqk_dqQ_ne_lRp : dqQ ≠ lRp := by decide
@[simp] theorem dqk_lRp_ne_dqQ : lRp ≠ dqQ := by decide
@[simp] theorem dqk_dqQ_ne_lRn : dqQ ≠ lRn := by decide
@[simp] theorem dqk_lRn_ne_dqQ : lRn ≠ dqQ := by decide
@[simp] theorem dqk_dqQ_ne_lFle : dqQ ≠ lFle := by decide
@[simp] theorem dqk_lFle_ne_dqQ : lFle ≠ dqQ := by decide
@[simp] theorem dqk_dqQ_ne_lKb : dqQ ≠ lKb := by decide
@[simp] theorem dqk_lKb_ne_dqQ : lKb ≠ dqQ := by decide
@[simp] theorem dqk_dqQ_ne_lDir : dqQ ≠ lDir := by decide
@[simp] theorem dqk_lDir_ne_dqQ : lDir ≠ dqQ := by decide
@[simp] theorem dqk_dqQ_ne_lFln : dqQ ≠ lFln := by decide
@[simp] theorem dqk_lFln_ne_dqQ : lFln ≠ dqQ := by decide
@[simp] theorem dqk_dqQ_ne_lFll : dqQ ≠ lFll := by decide
@[simp] theorem dqk_lFll_ne_dqQ : lFll ≠ dqQ := by decide
@[simp] theorem dqk_dqQ_ne_lFls : dqQ ≠ lFls := by decide
@[simp] theorem dqk_lFls_ne_dqQ : lFls ≠ dqQ := by decide
@[simp] theorem dqk_dqQ_ne_kFu : dqQ ≠ kFu := by decide
@[simp] theorem dqk_kFu_ne_dqQ : kFu ≠ dqQ := by decide
@[simp] theorem dqk_dqQ_ne_kD : dqQ ≠ kD := by decide
@[simp] theorem dqk_kD_ne_dqQ : kD ≠ dqQ := by decide
@[simp] theorem dqk_dqW_ne_dqA : dqW ≠ dqA := by decide
@[simp] theorem dqk_dqW_ne_dqB : dqW ≠ dqB := by decide
@[simp] theorem dqk_dqW_ne_dqQ : dqW ≠ dqQ := by decide
@[simp] theorem dqk_dqW_ne_tuE : dqW ≠ tuE := by decide
@[simp] theorem dqk_dqW_ne_tuX : dqW ≠ tuX := by decide
@[simp] theorem dqk_dqW_ne_tuY : dqW ≠ tuY := by decide
@[simp] theorem dqk_dqW_ne_lFl : dqW ≠ lFl := by decide
@[simp] theorem dqk_lFl_ne_dqW : lFl ≠ dqW := by decide
@[simp] theorem dqk_dqW_ne_lDh : dqW ≠ lDh := by decide
@[simp] theorem dqk_lDh_ne_dqW : lDh ≠ dqW := by decide
@[simp] theorem dqk_dqW_ne_lDt : dqW ≠ lDt := by decide
@[simp] theorem dqk_lDt_ne_dqW : lDt ≠ dqW := by decide
@[simp] theorem dqk_dqW_ne_lDg : dqW ≠ lDg := by decide
@[simp] theorem dqk_lDg_ne_dqW : lDg ≠ dqW := by decide
@[simp] theorem dqk_dqW_ne_lDi : dqW ≠ lDi := by decide
@[simp] theorem dqk_lDi_ne_dqW : lDi ≠ dqW := by decide
@[simp] theorem dqk_dqW_ne_lRp : dqW ≠ lRp := by decide
@[simp] theorem dqk_lRp_ne_dqW : lRp ≠ dqW := by decide
@[simp] theorem dqk_dqW_ne_lRn : dqW ≠ lRn := by decide
@[simp] theorem dqk_lRn_ne_dqW : lRn ≠ dqW := by decide
@[simp] theorem dqk_dqW_ne_lFle : dqW ≠ lFle := by decide
@[simp] theorem dqk_lFle_ne_dqW : lFle ≠ dqW := by decide
@[simp] theorem dqk_dqW_ne_lKb : dqW ≠ lKb := by decide
@[simp] theorem dqk_lKb_ne_dqW : lKb ≠ dqW := by decide
@[simp] theorem dqk_dqW_ne_lDir : dqW ≠ lDir := by decide
@[simp] theorem dqk_lDir_ne_dqW : lDir ≠ dqW := by decide
@[simp] theorem dqk_dqW_ne_lFln : dqW ≠ lFln := by decide
@[simp] theorem dqk_lFln_ne_dqW : lFln ≠ dqW := by decide
@[simp] theorem dqk_dqW_ne_lFll : dqW ≠ lFll := by decide
@[simp] theorem dqk_lFll_ne_dqW : lFll ≠ dqW := by decide
@[simp] theorem dqk_dqW_ne_lFls : dqW ≠ lFls := by decide
@[simp] theorem dqk_lFls_ne_dqW : lFls ≠ dqW := by decide
@[simp] theorem dqk_dqW_ne_kFu : dqW ≠ kFu := by decide
@[simp] theorem dqk_kFu_ne_dqW : kFu ≠ dqW := by decide
@[simp] theorem dqk_dqW_ne_kD : dqW ≠ kD := by decide
@[simp] theorem dqk_kD_ne_dqW : kD ≠ dqW := by decide
@[simp] theorem dqk_tuE_ne_dqA : tuE ≠ dqA := by decide
@[simp] theorem dqk_tuE_ne_dqB : tuE ≠ dqB := by decide
@[simp] theorem dqk_tuE_ne_dqQ : tuE ≠ dqQ := by decide
@[simp] theorem dqk_tuE_ne_dqW : tuE ≠ dqW := by decide
@[simp] theorem dqk_tuE_ne_tuX : tuE ≠ tuX := by decide
@[simp] theorem dqk_tuE_ne_tuY : tuE ≠ tuY := by decide
@[simp] theorem dqk_tuE_ne_lFl : tuE ≠ lFl := by decide
@[simp] theorem dqk_lFl_ne_tuE : lFl ≠ tuE := by decide
@[simp] theorem dqk_tuE_ne_lDh : tuE ≠ lDh := by decide
@[simp] theorem dqk_lDh_ne_tuE : lDh ≠ tuE := by decide
@[simp] theorem dqk_tuE_ne_lDt : tuE ≠ lDt := by decide
@[simp] theorem dqk_lDt_ne_tuE : lDt ≠ tuE := by decide
@[simp] theorem dqk_tuE_ne_lDg : tuE ≠ lDg := by decide
@[simp] theorem dqk_lDg_ne_tuE : lDg ≠ tuE := by decide
@[simp] theorem dqk_tuE_ne_lDi : tuE ≠ lDi := by decide
@[simp] theorem dqk_lDi_ne_tuE : lDi ≠ tuE := by decide
@[simp] theorem dqk_tuE_ne_lRp : tuE ≠ lRp := by decide
@[simp] theorem dqk_lRp_ne_tuE : lRp ≠ tuE := by decide
@[simp] theorem dqk_tuE_ne_lRn : tuE ≠ lRn := by decide
@[simp] theorem dqk_lRn_ne_tuE : lRn ≠ tuE := by decide
@[simp] theorem dqk_tuE_ne_lFle : tuE ≠ lFle := by decide
@[simp] theorem dqk_lFle_ne_tuE : lFle ≠ tuE := by decide
@[simp] theorem dqk_tuE_ne_lKb : tuE ≠ lKb := by decide
@[simp] theorem dqk_lKb_ne_tuE : lKb ≠ tuE := by decide
@[simp] theorem dqk_tuE_ne_lDir : tuE ≠ lDir := by decide
@[simp] theorem dqk_lDir_ne_tuE : lDir ≠ tuE := by decide
@[simp] theorem dqk_tuE_ne_lFln : tuE ≠ lFln := by decide
@[simp] theorem dqk_lFln_ne_tuE : lFln ≠ tuE := by decide
@[simp] theorem dqk_tuE_ne_lFll : tuE ≠ lFll := by decide
@[simp] theorem dqk_lFll_ne_tuE : lFll ≠ tuE := by decide
@[simp] theorem dqk_tuE_ne_lFls : tuE ≠ lFls := by decide
@[simp] theorem dqk_lFls_ne_tuE : lFls ≠ tuE := by decide
@[simp] theorem dqk_tuE_ne_kFu : tuE ≠ kFu := by decide
@[simp] theorem dqk_kFu_ne_tuE : kFu ≠ tuE := by decide
@[simp] theorem dqk_tuE_ne_kD : tuE ≠ kD := by decide
@[simp] theorem dqk_kD_ne_tuE : kD ≠ tuE := by decide
@[simp] theorem dqk_tuX_ne_dqA : tuX ≠ dqA := by decide
@[simp] theorem dqk_tuX_ne_dqB : tuX ≠ dqB := by decide
@[simp] theorem dqk_tuX_ne_dqQ : tuX ≠ dqQ := by decide
@[simp] theorem dqk_tuX_ne_dqW : tuX ≠ dqW := by decide
@[simp] theorem dqk_tuX_ne_tuE : tuX ≠ tuE := by decide
@[simp] theorem dqk_tuX_ne_tuY : tuX ≠ tuY := by decide
@[simp] theorem dqk_tuX_ne_lFl : tuX ≠ lFl := by decide
@[simp] theorem dqk_lFl_ne_tuX : lFl ≠ tuX := by decide
@[simp] theorem dqk_tuX_ne_lDh : tuX ≠ lDh := by decide
@[simp] theorem dqk_lDh_ne_tuX : lDh ≠ tuX := by decide
@[simp] theorem dqk_tuX_ne_lDt : tuX ≠ lDt := by decide
@[simp] theorem dqk_lDt_ne_tuX : lDt ≠ tuX := by decide
@[simp] theorem dqk_tuX_ne_lDg : tuX ≠ lDg := by decide
@[simp] theorem dqk_lDg_ne_tuX : lDg ≠ tuX := by decide
@[simp] theorem dqk_tuX_ne_lDi : tuX ≠ lDi := by decide
@[simp] theorem dqk_lDi_ne_tuX : lDi ≠ tuX := by decide
@[simp] theorem dqk_tuX_ne_lRp : tuX ≠ lRp := by decide
@[simp] theorem dqk_lRp_ne_tuX : lRp ≠ tuX := by decide
@[simp] theorem dqk_tuX_ne_lRn : tuX ≠ lRn := by decide
@[simp] theorem dqk_lRn_ne_tuX : lRn ≠ tuX := by decide
@[simp] theorem dqk_tuX_ne_lFle : tuX ≠ lFle := by decide
@[simp] theorem dqk_lFle_ne_tuX : lFle ≠ tuX := by decide
@[simp] theorem dqk_tuX_ne_lKb : tuX ≠ lKb := by decide
@[simp] theorem dqk_lKb_ne_tuX : lKb ≠ tuX := by decide
@[simp] theorem dqk_tuX_ne_lDir : tuX ≠ lDir := by decide
@[simp] theorem dqk_lDir_ne_tuX : lDir ≠ tuX := by decide
@[simp] theorem dqk_tuX_ne_lFln : tuX ≠ lFln := by decide
@[simp] theorem dqk_lFln_ne_tuX : lFln ≠ tuX := by decide
@[simp] theorem dqk_tuX_ne_lFll : tuX ≠ lFll := by decide
@[simp] theorem dqk_lFll_ne_tuX : lFll ≠ tuX := by decide
@[simp] theorem dqk_tuX_ne_lFls : tuX ≠ lFls := by decide
@[simp] theorem dqk_lFls_ne_tuX : lFls ≠ tuX := by decide
@[simp] theorem dqk_tuX_ne_kFu : tuX ≠ kFu := by decide
@[simp] theorem dqk_kFu_ne_tuX : kFu ≠ tuX := by decide
@[simp] theorem dqk_tuX_ne_kD : tuX ≠ kD := by decide
@[simp] theorem dqk_kD_ne_tuX : kD ≠ tuX := by decide
@[simp] theorem dqk_tuY_ne_dqA : tuY ≠ dqA := by decide
@[simp] theorem dqk_tuY_ne_dqB : tuY ≠ dqB := by decide
@[simp] theorem dqk_tuY_ne_dqQ : tuY ≠ dqQ := by decide
@[simp] theorem dqk_tuY_ne_dqW : tuY ≠ dqW := by decide
@[simp] theorem dqk_tuY_ne_tuE : tuY ≠ tuE := by decide
@[simp] theorem dqk_tuY_ne_tuX : tuY ≠ tuX := by decide
@[simp] theorem dqk_tuY_ne_lFl : tuY ≠ lFl := by decide
@[simp] theorem dqk_lFl_ne_tuY : lFl ≠ tuY := by decide
@[simp] theorem dqk_tuY_ne_lDh : tuY ≠ lDh := by decide
@[simp] theorem dqk_lDh_ne_tuY : lDh ≠ tuY := by decide
@[simp] theorem dqk_tuY_ne_lDt : tuY ≠ lDt := by decide
@[simp] theorem dqk_lDt_ne_tuY : lDt ≠ tuY := by decide
@[simp] theorem dqk_tuY_ne_lDg : tuY ≠ lDg := by decide
@[simp] theorem dqk_lDg_ne_tuY : lDg ≠ tuY := by decide
@[simp] theorem dqk_tuY_ne_lDi : tuY ≠ lDi := by decide
@[simp] theorem dqk_lDi_ne_tuY : lDi ≠ tuY := by decide
@[simp] theorem dqk_tuY_ne_lRp : tuY ≠ lRp := by decide
@[simp] theorem dqk_lRp_ne_tuY : lRp ≠ tuY := by decide
@[simp] theorem dqk_tuY_ne_lRn : tuY ≠ lRn := by decide
@[simp] theorem dqk_lRn_ne_tuY : lRn ≠ tuY := by decide
@[simp] theorem dqk_tuY_ne_lFle : tuY ≠ lFle := by decide
@[simp] theorem dqk_lFle_ne_tuY : lFle ≠ tuY := by decide
@[simp] theorem dqk_tuY_ne_lKb : tuY ≠ lKb := by decide
@[simp] theorem dqk_lKb_ne_tuY : lKb ≠ tuY := by decide
@[simp] theorem dqk_tuY_ne_lDir : tuY ≠ lDir := by decide
@[simp] theorem dqk_lDir_ne_tuY : lDir ≠ tuY := by decide
@[simp] theorem dqk_tuY_ne_lFln : tuY ≠ lFln := by decide
@[simp] theorem dqk_lFln_ne_tuY : lFln ≠ tuY := by decide
@[simp] theorem dqk_tuY_ne_lFll : tuY ≠ lFll := by decide
@[simp] theorem dqk_lFll_ne_tuY : lFll ≠ tuY := by decide
@[simp] theorem dqk_tuY_ne_lFls : tuY ≠ lFls := by decide
@[simp] theorem dqk_lFls_ne_tuY : lFls ≠ tuY := by decide
@[simp] theorem dqk_tuY_ne_kFu : tuY ≠ kFu := by decide
@[simp] theorem dqk_kFu_ne_tuY : kFu ≠ tuY := by decide
@[simp] theorem dqk_tuY_ne_kD : tuY ≠ kD := by decide
@[simp] theorem dqk_kD_ne_tuY : kD ≠ tuY := by decide

def dqParams : List MlS := [kFu, kD, dqA, dqB]
def dqBody (C : Ctx) : ProgHOL 64 := prologue [dqQ, dqW] (.seq (.call (some (some (.local, dqQ), none)) fQd [(vv kFu), (vv kD), (vv dqA), (vv dqB)]) (.ite (.cmp .equal (vv dqQ) (.const 2)) (.return (.const 1)) (.ite (.cmp .equal (vv dqQ) (.const 1)) (.return (.const 2)) (alloc2 C dqW (vv dqA) (vv dqB) (.return (vv dqW))))))
def tuParams : List MlS := [kFu, kD, tuE]
def tuBody : ProgHOL 64 := prologue [tuX, tuY] (.seq (.call (some (some (.local, tuX), none)) fHp [(vv tuE)]) (.ite (vv tuX) (.seq (.call (some (some (.local, tuY), none)) fWC [(vv kFu), (.const 0), (vv kD), (vv tuE)]) (.ite (.cmp .equal (vv tuY) (vv tuE)) (.return (.const 0)) (.return (.op .add [(vv tuY), (.const 1)])))) (.return (.const 0))))

section
variable {σ : Type}

def dsW (C : Ctx) (H : List (BitVec 64)) : DeltaStepA → BitVec 64 → Prop
  | .unknown, w => w = 0
  | .eq, w => w = 1
  | .diff, w => w = 2
  | .cont a b, w => ∃ o, w = cellA C o ∧ H[o]? = some (Enc.idxW a) ∧ H[o + 1]? = some (Enc.idxW b)

def PostDS (C : Ctx) (r : DeltaStepA) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ dsW C H' r w ∧ SR (ctxH C H') s' st

theorem postDS_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostDS C a w s' st → PostDS C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', h1, h2, h3⟩ => ⟨H', h1, h2, sr_of_eq h3 rfl rfl rfl rfl⟩

theorem dq_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) (hok : CtxOK C)
    (hcq : C.code.lookup fQd = some (qdParams.map (fun p => (p, ShapeHOL.one)), qdBody C, .one))
    (hQD : ∀ (H : List (BitVec 64)) s1 a b, C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s1 (qdParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b]))
        (qdBody C) s1 (quickDefEq mode (knot mode C n) d a b) (PostOBH (ctxH C H)))
    (s : AState) (a b : EIdx) :
    SpecR (σ := σ) (Pre C s (dqParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b])) (dqBody C) s
      (deltaQuick mode (knot mode C n) d a b) (PostDS C) := by
  refine specR_prologue (postDS_locals C) (Knot.params_none C [dqQ, dqW] dqParams _ (by decide) (by decide)) ?_
  unfold deltaQuick
  refine specR_callNIH (C := C) dqQ fQd qdParams [vv kFu, vv kD, vv dqA, vv dqB] (qdBody C)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (by decide) rfl (by decide) hcq
    ⟨by simp +decide [Env.get, dqParams, ctxEnv], by simp +decide [Env.get, dqParams, ctxEnv],
      by simp +decide [Env.get, dqParams, ctxEnv], by simp +decide [Env.get, dqParams, ctxEnv], trivial⟩
    (PostOBH C) (fun o w _ _ => w = LLeq.obW o) (fun o w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu qdParams _ rfl hlk) (hQD C.H s a b (List.prefix_refl _)))
    (fun o w s1 H1 hp1 hw => ?_)
  subst hw
  rcases o with _ | ⟨_ | _⟩
  · refine specR_ifI _ 0 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    refine specR_alloc2I (C := ctxH C H1) (ctxOK_H hok H1) dqW (vv dqA) (vv dqB) (Enc.idxW a) (Enc.idxW b) (by decide)
      (fun _ => by simp +decide [Env.get, dqParams, ctxEnv]) (fun _ => by simp +decide [Env.get, dqParams, ctxEnv])
      (fun H2 ws hp2 hws => ?_)
    refine specR_returnI (vv dqW) (cellA C H2.length) (by simp +decide <;> rfl) (fun t ht => ?_)
    have hp2' : H1 <+: H2 := hp2
    exact ⟨_, hp1.trans (hp2'.trans (img2_prefix H2 ws _ _ hws)), ⟨H2.length, rfl, (img2_get H2 ws _ _ hws).1, (img2_get H2 ws _ _ hws).2⟩,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩
  · refine specR_ifI _ 0 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact specR_returnI _ 2 rfl (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_ifI _ 1 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem tu_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hcaf : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one))
    (hchp : C.code.lookup fHp = some ([(hpE, .one)], hpBody, .one))
    (hcwc : C.code.lookup fWC = some (pmap wcParams, wcE, .one))
    (hWC : ∀ (H : List (BitVec 64)) s1 c d e, C.H <+: H → Callee (σ := σ) (ctxH C H) wcParams
      [BitVec.ofNat 64 n, boolW c, BitVec.ofNat 64 d, Enc.idxW e] wcE s1 ((knot mode C n).whnfCore c d e)
      (PostK (ctxH C H)))
    (s : AState) (d : Nat) (e : EIdx) :
    SpecR (σ := σ) (Pre C s (tuParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e])) tuBody s
      (tryUnfoldProjApp (knot mode C n) d e) (UD.PostO C) := by
  refine specR_prologue (UD.postO_locals C) (Knot.params_none C [tuX, tuY] tuParams _ (by decide) (by decide)) ?_
  unfold tryUnfoldProjApp
  refine specR_callNIH (C := C) tuX fHp [hpE] [vv tuE] hpBody [Enc.idxW e] (by decide) rfl (by decide) hchp
    ⟨by simp +decide [Env.get, tuParams, ctxEnv], trivial⟩ (PostB C) (fun x w _ _ => w = boolW x)
    (fun x w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [hpE] _ rfl hlk) (hp_spec C hcaf s e))
    (fun x w s1 H1 hp1 hw => ?_)
  subst hw
  cases x
  · refine specR_ifI _ 0 (by simp [boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 1 (by simp [boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
  simp only [↓reduceIte]
  refine specR_callNIH (C := ctxH C H1) tuY fWC wcParams [vv kFu, .const 0, vv kD, vv tuE] wcE
    [BitVec.ofNat 64 n, boolW false, BitVec.ofNat 64 d, Enc.idxW e] (by decide) rfl (by decide) hcwc
    ⟨by simp +decide [Env.get, tuParams, ctxEnv], rfl, by simp +decide [Env.get, tuParams, ctxEnv],
      by simp +decide [Env.get, tuParams, ctxEnv], trivial⟩
    (PostK (ctxH C H1)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
    (fun u hu _ hlk => hWC H1 s1 false d e hp1 u hu (fun i hi _ => hlk i (by omega)))
    (fun e' w s2 H2 hp2 hw => ?_)
  subst hw
  have hp12 : C.H <+: H2 := hp1.trans hp2
  by_cases he : e' = e
  · subst he
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, tuParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [beq_self_eq_true, ↓reduceIte]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H2, hp12, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  have hne : Enc.idxW e' ≠ Enc.idxW e := fun x => he (Enc.idxW_inj x)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, tuParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun h => absurd rfl h) (fun _ => ?_)
  simp only [show (e' == e) = false by simpa using he, Bool.false_eq_true, ↓reduceIte]
  exact specR_returnI _ (optW (some e')) (by simp [sev, optWG])
    (fun t ht => ⟨H2, hp12, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
