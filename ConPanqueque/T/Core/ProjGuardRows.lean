import ConPanqueque.T.Core.ProjGuardFast
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `projGuardRowsGo`

Step `k` field binders of the substituted constructor telescope; a field whose body mentions it (its row is
needed later) is opened at a fresh `fvar` and its row `(d, dom)` kept; the projected field's row is the last.
Answers `0` for `none`, else the rows block (`rowsW`).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def gqK := ofString "gqn_k"
def gqD := ofString "gqn_d"
def gqH := ofString "gqn_h"
def gqO := ofString "gqn_o"
def gqDm := ofString "gqn_dm"
def gqB := ofString "gqn_b"
def gqX := ofString "gqn_x"
def gqO1 := ofString "gqn_o1"
def gqO2 := ofString "gqn_o2"
def gqV := ofString "gqn_v"
def gqB2 := ofString "gqn_b2"
def gqR := ofString "gqn_r"
def fGq := ofString "projGuardRowsGo"

@[simp] theorem gq_prK_ne_prD : gqK ≠ gqD := by decide
@[simp] theorem gq_prK_ne_prH : gqK ≠ gqH := by decide
@[simp] theorem gq_prK_ne_prO : gqK ≠ gqO := by decide
@[simp] theorem gq_prK_ne_prDm : gqK ≠ gqDm := by decide
@[simp] theorem gq_prK_ne_prB : gqK ≠ gqB := by decide
@[simp] theorem gq_prK_ne_prX : gqK ≠ gqX := by decide
@[simp] theorem gq_prK_ne_prO1 : gqK ≠ gqO1 := by decide
@[simp] theorem gq_prK_ne_prO2 : gqK ≠ gqO2 := by decide
@[simp] theorem gq_prK_ne_prV : gqK ≠ gqV := by decide
@[simp] theorem gq_prK_ne_prB2 : gqK ≠ gqB2 := by decide
@[simp] theorem gq_prK_ne_prR : gqK ≠ gqR := by decide
@[simp] theorem gq_prK_ne_lFl : gqK ≠ lFl := by decide
@[simp] theorem gq_lFl_ne_prK : lFl ≠ gqK := by decide
@[simp] theorem gq_prK_ne_lDh : gqK ≠ lDh := by decide
@[simp] theorem gq_lDh_ne_prK : lDh ≠ gqK := by decide
@[simp] theorem gq_prK_ne_lDt : gqK ≠ lDt := by decide
@[simp] theorem gq_lDt_ne_prK : lDt ≠ gqK := by decide
@[simp] theorem gq_prK_ne_lDg : gqK ≠ lDg := by decide
@[simp] theorem gq_lDg_ne_prK : lDg ≠ gqK := by decide
@[simp] theorem gq_prK_ne_lDi : gqK ≠ lDi := by decide
@[simp] theorem gq_lDi_ne_prK : lDi ≠ gqK := by decide
@[simp] theorem gq_prK_ne_lRp : gqK ≠ lRp := by decide
@[simp] theorem gq_lRp_ne_prK : lRp ≠ gqK := by decide
@[simp] theorem gq_prK_ne_lRn : gqK ≠ lRn := by decide
@[simp] theorem gq_lRn_ne_prK : lRn ≠ gqK := by decide
@[simp] theorem gq_prK_ne_lDir : gqK ≠ lDir := by decide
@[simp] theorem gq_lDir_ne_prK : lDir ≠ gqK := by decide
@[simp] theorem gq_prK_ne_lFle : gqK ≠ lFle := by decide
@[simp] theorem gq_lFle_ne_prK : lFle ≠ gqK := by decide
@[simp] theorem gq_prK_ne_lKb : gqK ≠ lKb := by decide
@[simp] theorem gq_lKb_ne_prK : lKb ≠ gqK := by decide
@[simp] theorem gq_prD_ne_prK : gqD ≠ gqK := by decide
@[simp] theorem gq_prD_ne_prH : gqD ≠ gqH := by decide
@[simp] theorem gq_prD_ne_prO : gqD ≠ gqO := by decide
@[simp] theorem gq_prD_ne_prDm : gqD ≠ gqDm := by decide
@[simp] theorem gq_prD_ne_prB : gqD ≠ gqB := by decide
@[simp] theorem gq_prD_ne_prX : gqD ≠ gqX := by decide
@[simp] theorem gq_prD_ne_prO1 : gqD ≠ gqO1 := by decide
@[simp] theorem gq_prD_ne_prO2 : gqD ≠ gqO2 := by decide
@[simp] theorem gq_prD_ne_prV : gqD ≠ gqV := by decide
@[simp] theorem gq_prD_ne_prB2 : gqD ≠ gqB2 := by decide
@[simp] theorem gq_prD_ne_prR : gqD ≠ gqR := by decide
@[simp] theorem gq_prD_ne_lFl : gqD ≠ lFl := by decide
@[simp] theorem gq_lFl_ne_prD : lFl ≠ gqD := by decide
@[simp] theorem gq_prD_ne_lDh : gqD ≠ lDh := by decide
@[simp] theorem gq_lDh_ne_prD : lDh ≠ gqD := by decide
@[simp] theorem gq_prD_ne_lDt : gqD ≠ lDt := by decide
@[simp] theorem gq_lDt_ne_prD : lDt ≠ gqD := by decide
@[simp] theorem gq_prD_ne_lDg : gqD ≠ lDg := by decide
@[simp] theorem gq_lDg_ne_prD : lDg ≠ gqD := by decide
@[simp] theorem gq_prD_ne_lDi : gqD ≠ lDi := by decide
@[simp] theorem gq_lDi_ne_prD : lDi ≠ gqD := by decide
@[simp] theorem gq_prD_ne_lRp : gqD ≠ lRp := by decide
@[simp] theorem gq_lRp_ne_prD : lRp ≠ gqD := by decide
@[simp] theorem gq_prD_ne_lRn : gqD ≠ lRn := by decide
@[simp] theorem gq_lRn_ne_prD : lRn ≠ gqD := by decide
@[simp] theorem gq_prD_ne_lDir : gqD ≠ lDir := by decide
@[simp] theorem gq_lDir_ne_prD : lDir ≠ gqD := by decide
@[simp] theorem gq_prD_ne_lFle : gqD ≠ lFle := by decide
@[simp] theorem gq_lFle_ne_prD : lFle ≠ gqD := by decide
@[simp] theorem gq_prD_ne_lKb : gqD ≠ lKb := by decide
@[simp] theorem gq_lKb_ne_prD : lKb ≠ gqD := by decide
@[simp] theorem gq_prH_ne_prK : gqH ≠ gqK := by decide
@[simp] theorem gq_prH_ne_prD : gqH ≠ gqD := by decide
@[simp] theorem gq_prH_ne_prO : gqH ≠ gqO := by decide
@[simp] theorem gq_prH_ne_prDm : gqH ≠ gqDm := by decide
@[simp] theorem gq_prH_ne_prB : gqH ≠ gqB := by decide
@[simp] theorem gq_prH_ne_prX : gqH ≠ gqX := by decide
@[simp] theorem gq_prH_ne_prO1 : gqH ≠ gqO1 := by decide
@[simp] theorem gq_prH_ne_prO2 : gqH ≠ gqO2 := by decide
@[simp] theorem gq_prH_ne_prV : gqH ≠ gqV := by decide
@[simp] theorem gq_prH_ne_prB2 : gqH ≠ gqB2 := by decide
@[simp] theorem gq_prH_ne_prR : gqH ≠ gqR := by decide
@[simp] theorem gq_prH_ne_lFl : gqH ≠ lFl := by decide
@[simp] theorem gq_lFl_ne_prH : lFl ≠ gqH := by decide
@[simp] theorem gq_prH_ne_lDh : gqH ≠ lDh := by decide
@[simp] theorem gq_lDh_ne_prH : lDh ≠ gqH := by decide
@[simp] theorem gq_prH_ne_lDt : gqH ≠ lDt := by decide
@[simp] theorem gq_lDt_ne_prH : lDt ≠ gqH := by decide
@[simp] theorem gq_prH_ne_lDg : gqH ≠ lDg := by decide
@[simp] theorem gq_lDg_ne_prH : lDg ≠ gqH := by decide
@[simp] theorem gq_prH_ne_lDi : gqH ≠ lDi := by decide
@[simp] theorem gq_lDi_ne_prH : lDi ≠ gqH := by decide
@[simp] theorem gq_prH_ne_lRp : gqH ≠ lRp := by decide
@[simp] theorem gq_lRp_ne_prH : lRp ≠ gqH := by decide
@[simp] theorem gq_prH_ne_lRn : gqH ≠ lRn := by decide
@[simp] theorem gq_lRn_ne_prH : lRn ≠ gqH := by decide
@[simp] theorem gq_prH_ne_lDir : gqH ≠ lDir := by decide
@[simp] theorem gq_lDir_ne_prH : lDir ≠ gqH := by decide
@[simp] theorem gq_prH_ne_lFle : gqH ≠ lFle := by decide
@[simp] theorem gq_lFle_ne_prH : lFle ≠ gqH := by decide
@[simp] theorem gq_prH_ne_lKb : gqH ≠ lKb := by decide
@[simp] theorem gq_lKb_ne_prH : lKb ≠ gqH := by decide
@[simp] theorem gq_prO_ne_prK : gqO ≠ gqK := by decide
@[simp] theorem gq_prO_ne_prD : gqO ≠ gqD := by decide
@[simp] theorem gq_prO_ne_prH : gqO ≠ gqH := by decide
@[simp] theorem gq_prO_ne_prDm : gqO ≠ gqDm := by decide
@[simp] theorem gq_prO_ne_prB : gqO ≠ gqB := by decide
@[simp] theorem gq_prO_ne_prX : gqO ≠ gqX := by decide
@[simp] theorem gq_prO_ne_prO1 : gqO ≠ gqO1 := by decide
@[simp] theorem gq_prO_ne_prO2 : gqO ≠ gqO2 := by decide
@[simp] theorem gq_prO_ne_prV : gqO ≠ gqV := by decide
@[simp] theorem gq_prO_ne_prB2 : gqO ≠ gqB2 := by decide
@[simp] theorem gq_prO_ne_prR : gqO ≠ gqR := by decide
@[simp] theorem gq_prO_ne_lFl : gqO ≠ lFl := by decide
@[simp] theorem gq_lFl_ne_prO : lFl ≠ gqO := by decide
@[simp] theorem gq_prO_ne_lDh : gqO ≠ lDh := by decide
@[simp] theorem gq_lDh_ne_prO : lDh ≠ gqO := by decide
@[simp] theorem gq_prO_ne_lDt : gqO ≠ lDt := by decide
@[simp] theorem gq_lDt_ne_prO : lDt ≠ gqO := by decide
@[simp] theorem gq_prO_ne_lDg : gqO ≠ lDg := by decide
@[simp] theorem gq_lDg_ne_prO : lDg ≠ gqO := by decide
@[simp] theorem gq_prO_ne_lDi : gqO ≠ lDi := by decide
@[simp] theorem gq_lDi_ne_prO : lDi ≠ gqO := by decide
@[simp] theorem gq_prO_ne_lRp : gqO ≠ lRp := by decide
@[simp] theorem gq_lRp_ne_prO : lRp ≠ gqO := by decide
@[simp] theorem gq_prO_ne_lRn : gqO ≠ lRn := by decide
@[simp] theorem gq_lRn_ne_prO : lRn ≠ gqO := by decide
@[simp] theorem gq_prO_ne_lDir : gqO ≠ lDir := by decide
@[simp] theorem gq_lDir_ne_prO : lDir ≠ gqO := by decide
@[simp] theorem gq_prO_ne_lFle : gqO ≠ lFle := by decide
@[simp] theorem gq_lFle_ne_prO : lFle ≠ gqO := by decide
@[simp] theorem gq_prO_ne_lKb : gqO ≠ lKb := by decide
@[simp] theorem gq_lKb_ne_prO : lKb ≠ gqO := by decide
@[simp] theorem gq_prDm_ne_prK : gqDm ≠ gqK := by decide
@[simp] theorem gq_prDm_ne_prD : gqDm ≠ gqD := by decide
@[simp] theorem gq_prDm_ne_prH : gqDm ≠ gqH := by decide
@[simp] theorem gq_prDm_ne_prO : gqDm ≠ gqO := by decide
@[simp] theorem gq_prDm_ne_prB : gqDm ≠ gqB := by decide
@[simp] theorem gq_prDm_ne_prX : gqDm ≠ gqX := by decide
@[simp] theorem gq_prDm_ne_prO1 : gqDm ≠ gqO1 := by decide
@[simp] theorem gq_prDm_ne_prO2 : gqDm ≠ gqO2 := by decide
@[simp] theorem gq_prDm_ne_prV : gqDm ≠ gqV := by decide
@[simp] theorem gq_prDm_ne_prB2 : gqDm ≠ gqB2 := by decide
@[simp] theorem gq_prDm_ne_prR : gqDm ≠ gqR := by decide
@[simp] theorem gq_prDm_ne_lFl : gqDm ≠ lFl := by decide
@[simp] theorem gq_lFl_ne_prDm : lFl ≠ gqDm := by decide
@[simp] theorem gq_prDm_ne_lDh : gqDm ≠ lDh := by decide
@[simp] theorem gq_lDh_ne_prDm : lDh ≠ gqDm := by decide
@[simp] theorem gq_prDm_ne_lDt : gqDm ≠ lDt := by decide
@[simp] theorem gq_lDt_ne_prDm : lDt ≠ gqDm := by decide
@[simp] theorem gq_prDm_ne_lDg : gqDm ≠ lDg := by decide
@[simp] theorem gq_lDg_ne_prDm : lDg ≠ gqDm := by decide
@[simp] theorem gq_prDm_ne_lDi : gqDm ≠ lDi := by decide
@[simp] theorem gq_lDi_ne_prDm : lDi ≠ gqDm := by decide
@[simp] theorem gq_prDm_ne_lRp : gqDm ≠ lRp := by decide
@[simp] theorem gq_lRp_ne_prDm : lRp ≠ gqDm := by decide
@[simp] theorem gq_prDm_ne_lRn : gqDm ≠ lRn := by decide
@[simp] theorem gq_lRn_ne_prDm : lRn ≠ gqDm := by decide
@[simp] theorem gq_prDm_ne_lDir : gqDm ≠ lDir := by decide
@[simp] theorem gq_lDir_ne_prDm : lDir ≠ gqDm := by decide
@[simp] theorem gq_prDm_ne_lFle : gqDm ≠ lFle := by decide
@[simp] theorem gq_lFle_ne_prDm : lFle ≠ gqDm := by decide
@[simp] theorem gq_prDm_ne_lKb : gqDm ≠ lKb := by decide
@[simp] theorem gq_lKb_ne_prDm : lKb ≠ gqDm := by decide
@[simp] theorem gq_prB_ne_prK : gqB ≠ gqK := by decide
@[simp] theorem gq_prB_ne_prD : gqB ≠ gqD := by decide
@[simp] theorem gq_prB_ne_prH : gqB ≠ gqH := by decide
@[simp] theorem gq_prB_ne_prO : gqB ≠ gqO := by decide
@[simp] theorem gq_prB_ne_prDm : gqB ≠ gqDm := by decide
@[simp] theorem gq_prB_ne_prX : gqB ≠ gqX := by decide
@[simp] theorem gq_prB_ne_prO1 : gqB ≠ gqO1 := by decide
@[simp] theorem gq_prB_ne_prO2 : gqB ≠ gqO2 := by decide
@[simp] theorem gq_prB_ne_prV : gqB ≠ gqV := by decide
@[simp] theorem gq_prB_ne_prB2 : gqB ≠ gqB2 := by decide
@[simp] theorem gq_prB_ne_prR : gqB ≠ gqR := by decide
@[simp] theorem gq_prB_ne_lFl : gqB ≠ lFl := by decide
@[simp] theorem gq_lFl_ne_prB : lFl ≠ gqB := by decide
@[simp] theorem gq_prB_ne_lDh : gqB ≠ lDh := by decide
@[simp] theorem gq_lDh_ne_prB : lDh ≠ gqB := by decide
@[simp] theorem gq_prB_ne_lDt : gqB ≠ lDt := by decide
@[simp] theorem gq_lDt_ne_prB : lDt ≠ gqB := by decide
@[simp] theorem gq_prB_ne_lDg : gqB ≠ lDg := by decide
@[simp] theorem gq_lDg_ne_prB : lDg ≠ gqB := by decide
@[simp] theorem gq_prB_ne_lDi : gqB ≠ lDi := by decide
@[simp] theorem gq_lDi_ne_prB : lDi ≠ gqB := by decide
@[simp] theorem gq_prB_ne_lRp : gqB ≠ lRp := by decide
@[simp] theorem gq_lRp_ne_prB : lRp ≠ gqB := by decide
@[simp] theorem gq_prB_ne_lRn : gqB ≠ lRn := by decide
@[simp] theorem gq_lRn_ne_prB : lRn ≠ gqB := by decide
@[simp] theorem gq_prB_ne_lDir : gqB ≠ lDir := by decide
@[simp] theorem gq_lDir_ne_prB : lDir ≠ gqB := by decide
@[simp] theorem gq_prB_ne_lFle : gqB ≠ lFle := by decide
@[simp] theorem gq_lFle_ne_prB : lFle ≠ gqB := by decide
@[simp] theorem gq_prB_ne_lKb : gqB ≠ lKb := by decide
@[simp] theorem gq_lKb_ne_prB : lKb ≠ gqB := by decide
@[simp] theorem gq_prX_ne_prK : gqX ≠ gqK := by decide
@[simp] theorem gq_prX_ne_prD : gqX ≠ gqD := by decide
@[simp] theorem gq_prX_ne_prH : gqX ≠ gqH := by decide
@[simp] theorem gq_prX_ne_prO : gqX ≠ gqO := by decide
@[simp] theorem gq_prX_ne_prDm : gqX ≠ gqDm := by decide
@[simp] theorem gq_prX_ne_prB : gqX ≠ gqB := by decide
@[simp] theorem gq_prX_ne_prO1 : gqX ≠ gqO1 := by decide
@[simp] theorem gq_prX_ne_prO2 : gqX ≠ gqO2 := by decide
@[simp] theorem gq_prX_ne_prV : gqX ≠ gqV := by decide
@[simp] theorem gq_prX_ne_prB2 : gqX ≠ gqB2 := by decide
@[simp] theorem gq_prX_ne_prR : gqX ≠ gqR := by decide
@[simp] theorem gq_prX_ne_lFl : gqX ≠ lFl := by decide
@[simp] theorem gq_lFl_ne_prX : lFl ≠ gqX := by decide
@[simp] theorem gq_prX_ne_lDh : gqX ≠ lDh := by decide
@[simp] theorem gq_lDh_ne_prX : lDh ≠ gqX := by decide
@[simp] theorem gq_prX_ne_lDt : gqX ≠ lDt := by decide
@[simp] theorem gq_lDt_ne_prX : lDt ≠ gqX := by decide
@[simp] theorem gq_prX_ne_lDg : gqX ≠ lDg := by decide
@[simp] theorem gq_lDg_ne_prX : lDg ≠ gqX := by decide
@[simp] theorem gq_prX_ne_lDi : gqX ≠ lDi := by decide
@[simp] theorem gq_lDi_ne_prX : lDi ≠ gqX := by decide
@[simp] theorem gq_prX_ne_lRp : gqX ≠ lRp := by decide
@[simp] theorem gq_lRp_ne_prX : lRp ≠ gqX := by decide
@[simp] theorem gq_prX_ne_lRn : gqX ≠ lRn := by decide
@[simp] theorem gq_lRn_ne_prX : lRn ≠ gqX := by decide
@[simp] theorem gq_prX_ne_lDir : gqX ≠ lDir := by decide
@[simp] theorem gq_lDir_ne_prX : lDir ≠ gqX := by decide
@[simp] theorem gq_prX_ne_lFle : gqX ≠ lFle := by decide
@[simp] theorem gq_lFle_ne_prX : lFle ≠ gqX := by decide
@[simp] theorem gq_prX_ne_lKb : gqX ≠ lKb := by decide
@[simp] theorem gq_lKb_ne_prX : lKb ≠ gqX := by decide
@[simp] theorem gq_prO1_ne_prK : gqO1 ≠ gqK := by decide
@[simp] theorem gq_prO1_ne_prD : gqO1 ≠ gqD := by decide
@[simp] theorem gq_prO1_ne_prH : gqO1 ≠ gqH := by decide
@[simp] theorem gq_prO1_ne_prO : gqO1 ≠ gqO := by decide
@[simp] theorem gq_prO1_ne_prDm : gqO1 ≠ gqDm := by decide
@[simp] theorem gq_prO1_ne_prB : gqO1 ≠ gqB := by decide
@[simp] theorem gq_prO1_ne_prX : gqO1 ≠ gqX := by decide
@[simp] theorem gq_prO1_ne_prO2 : gqO1 ≠ gqO2 := by decide
@[simp] theorem gq_prO1_ne_prV : gqO1 ≠ gqV := by decide
@[simp] theorem gq_prO1_ne_prB2 : gqO1 ≠ gqB2 := by decide
@[simp] theorem gq_prO1_ne_prR : gqO1 ≠ gqR := by decide
@[simp] theorem gq_prO1_ne_lFl : gqO1 ≠ lFl := by decide
@[simp] theorem gq_lFl_ne_prO1 : lFl ≠ gqO1 := by decide
@[simp] theorem gq_prO1_ne_lDh : gqO1 ≠ lDh := by decide
@[simp] theorem gq_lDh_ne_prO1 : lDh ≠ gqO1 := by decide
@[simp] theorem gq_prO1_ne_lDt : gqO1 ≠ lDt := by decide
@[simp] theorem gq_lDt_ne_prO1 : lDt ≠ gqO1 := by decide
@[simp] theorem gq_prO1_ne_lDg : gqO1 ≠ lDg := by decide
@[simp] theorem gq_lDg_ne_prO1 : lDg ≠ gqO1 := by decide
@[simp] theorem gq_prO1_ne_lDi : gqO1 ≠ lDi := by decide
@[simp] theorem gq_lDi_ne_prO1 : lDi ≠ gqO1 := by decide
@[simp] theorem gq_prO1_ne_lRp : gqO1 ≠ lRp := by decide
@[simp] theorem gq_lRp_ne_prO1 : lRp ≠ gqO1 := by decide
@[simp] theorem gq_prO1_ne_lRn : gqO1 ≠ lRn := by decide
@[simp] theorem gq_lRn_ne_prO1 : lRn ≠ gqO1 := by decide
@[simp] theorem gq_prO1_ne_lDir : gqO1 ≠ lDir := by decide
@[simp] theorem gq_lDir_ne_prO1 : lDir ≠ gqO1 := by decide
@[simp] theorem gq_prO1_ne_lFle : gqO1 ≠ lFle := by decide
@[simp] theorem gq_lFle_ne_prO1 : lFle ≠ gqO1 := by decide
@[simp] theorem gq_prO1_ne_lKb : gqO1 ≠ lKb := by decide
@[simp] theorem gq_lKb_ne_prO1 : lKb ≠ gqO1 := by decide
@[simp] theorem gq_prO2_ne_prK : gqO2 ≠ gqK := by decide
@[simp] theorem gq_prO2_ne_prD : gqO2 ≠ gqD := by decide
@[simp] theorem gq_prO2_ne_prH : gqO2 ≠ gqH := by decide
@[simp] theorem gq_prO2_ne_prO : gqO2 ≠ gqO := by decide
@[simp] theorem gq_prO2_ne_prDm : gqO2 ≠ gqDm := by decide
@[simp] theorem gq_prO2_ne_prB : gqO2 ≠ gqB := by decide
@[simp] theorem gq_prO2_ne_prX : gqO2 ≠ gqX := by decide
@[simp] theorem gq_prO2_ne_prO1 : gqO2 ≠ gqO1 := by decide
@[simp] theorem gq_prO2_ne_prV : gqO2 ≠ gqV := by decide
@[simp] theorem gq_prO2_ne_prB2 : gqO2 ≠ gqB2 := by decide
@[simp] theorem gq_prO2_ne_prR : gqO2 ≠ gqR := by decide
@[simp] theorem gq_prO2_ne_lFl : gqO2 ≠ lFl := by decide
@[simp] theorem gq_lFl_ne_prO2 : lFl ≠ gqO2 := by decide
@[simp] theorem gq_prO2_ne_lDh : gqO2 ≠ lDh := by decide
@[simp] theorem gq_lDh_ne_prO2 : lDh ≠ gqO2 := by decide
@[simp] theorem gq_prO2_ne_lDt : gqO2 ≠ lDt := by decide
@[simp] theorem gq_lDt_ne_prO2 : lDt ≠ gqO2 := by decide
@[simp] theorem gq_prO2_ne_lDg : gqO2 ≠ lDg := by decide
@[simp] theorem gq_lDg_ne_prO2 : lDg ≠ gqO2 := by decide
@[simp] theorem gq_prO2_ne_lDi : gqO2 ≠ lDi := by decide
@[simp] theorem gq_lDi_ne_prO2 : lDi ≠ gqO2 := by decide
@[simp] theorem gq_prO2_ne_lRp : gqO2 ≠ lRp := by decide
@[simp] theorem gq_lRp_ne_prO2 : lRp ≠ gqO2 := by decide
@[simp] theorem gq_prO2_ne_lRn : gqO2 ≠ lRn := by decide
@[simp] theorem gq_lRn_ne_prO2 : lRn ≠ gqO2 := by decide
@[simp] theorem gq_prO2_ne_lDir : gqO2 ≠ lDir := by decide
@[simp] theorem gq_lDir_ne_prO2 : lDir ≠ gqO2 := by decide
@[simp] theorem gq_prO2_ne_lFle : gqO2 ≠ lFle := by decide
@[simp] theorem gq_lFle_ne_prO2 : lFle ≠ gqO2 := by decide
@[simp] theorem gq_prO2_ne_lKb : gqO2 ≠ lKb := by decide
@[simp] theorem gq_lKb_ne_prO2 : lKb ≠ gqO2 := by decide
@[simp] theorem gq_prV_ne_prK : gqV ≠ gqK := by decide
@[simp] theorem gq_prV_ne_prD : gqV ≠ gqD := by decide
@[simp] theorem gq_prV_ne_prH : gqV ≠ gqH := by decide
@[simp] theorem gq_prV_ne_prO : gqV ≠ gqO := by decide
@[simp] theorem gq_prV_ne_prDm : gqV ≠ gqDm := by decide
@[simp] theorem gq_prV_ne_prB : gqV ≠ gqB := by decide
@[simp] theorem gq_prV_ne_prX : gqV ≠ gqX := by decide
@[simp] theorem gq_prV_ne_prO1 : gqV ≠ gqO1 := by decide
@[simp] theorem gq_prV_ne_prO2 : gqV ≠ gqO2 := by decide
@[simp] theorem gq_prV_ne_prB2 : gqV ≠ gqB2 := by decide
@[simp] theorem gq_prV_ne_prR : gqV ≠ gqR := by decide
@[simp] theorem gq_prV_ne_lFl : gqV ≠ lFl := by decide
@[simp] theorem gq_lFl_ne_prV : lFl ≠ gqV := by decide
@[simp] theorem gq_prV_ne_lDh : gqV ≠ lDh := by decide
@[simp] theorem gq_lDh_ne_prV : lDh ≠ gqV := by decide
@[simp] theorem gq_prV_ne_lDt : gqV ≠ lDt := by decide
@[simp] theorem gq_lDt_ne_prV : lDt ≠ gqV := by decide
@[simp] theorem gq_prV_ne_lDg : gqV ≠ lDg := by decide
@[simp] theorem gq_lDg_ne_prV : lDg ≠ gqV := by decide
@[simp] theorem gq_prV_ne_lDi : gqV ≠ lDi := by decide
@[simp] theorem gq_lDi_ne_prV : lDi ≠ gqV := by decide
@[simp] theorem gq_prV_ne_lRp : gqV ≠ lRp := by decide
@[simp] theorem gq_lRp_ne_prV : lRp ≠ gqV := by decide
@[simp] theorem gq_prV_ne_lRn : gqV ≠ lRn := by decide
@[simp] theorem gq_lRn_ne_prV : lRn ≠ gqV := by decide
@[simp] theorem gq_prV_ne_lDir : gqV ≠ lDir := by decide
@[simp] theorem gq_lDir_ne_prV : lDir ≠ gqV := by decide
@[simp] theorem gq_prV_ne_lFle : gqV ≠ lFle := by decide
@[simp] theorem gq_lFle_ne_prV : lFle ≠ gqV := by decide
@[simp] theorem gq_prV_ne_lKb : gqV ≠ lKb := by decide
@[simp] theorem gq_lKb_ne_prV : lKb ≠ gqV := by decide
@[simp] theorem gq_prB2_ne_prK : gqB2 ≠ gqK := by decide
@[simp] theorem gq_prB2_ne_prD : gqB2 ≠ gqD := by decide
@[simp] theorem gq_prB2_ne_prH : gqB2 ≠ gqH := by decide
@[simp] theorem gq_prB2_ne_prO : gqB2 ≠ gqO := by decide
@[simp] theorem gq_prB2_ne_prDm : gqB2 ≠ gqDm := by decide
@[simp] theorem gq_prB2_ne_prB : gqB2 ≠ gqB := by decide
@[simp] theorem gq_prB2_ne_prX : gqB2 ≠ gqX := by decide
@[simp] theorem gq_prB2_ne_prO1 : gqB2 ≠ gqO1 := by decide
@[simp] theorem gq_prB2_ne_prO2 : gqB2 ≠ gqO2 := by decide
@[simp] theorem gq_prB2_ne_prV : gqB2 ≠ gqV := by decide
@[simp] theorem gq_prB2_ne_prR : gqB2 ≠ gqR := by decide
@[simp] theorem gq_prB2_ne_lFl : gqB2 ≠ lFl := by decide
@[simp] theorem gq_lFl_ne_prB2 : lFl ≠ gqB2 := by decide
@[simp] theorem gq_prB2_ne_lDh : gqB2 ≠ lDh := by decide
@[simp] theorem gq_lDh_ne_prB2 : lDh ≠ gqB2 := by decide
@[simp] theorem gq_prB2_ne_lDt : gqB2 ≠ lDt := by decide
@[simp] theorem gq_lDt_ne_prB2 : lDt ≠ gqB2 := by decide
@[simp] theorem gq_prB2_ne_lDg : gqB2 ≠ lDg := by decide
@[simp] theorem gq_lDg_ne_prB2 : lDg ≠ gqB2 := by decide
@[simp] theorem gq_prB2_ne_lDi : gqB2 ≠ lDi := by decide
@[simp] theorem gq_lDi_ne_prB2 : lDi ≠ gqB2 := by decide
@[simp] theorem gq_prB2_ne_lRp : gqB2 ≠ lRp := by decide
@[simp] theorem gq_lRp_ne_prB2 : lRp ≠ gqB2 := by decide
@[simp] theorem gq_prB2_ne_lRn : gqB2 ≠ lRn := by decide
@[simp] theorem gq_lRn_ne_prB2 : lRn ≠ gqB2 := by decide
@[simp] theorem gq_prB2_ne_lDir : gqB2 ≠ lDir := by decide
@[simp] theorem gq_lDir_ne_prB2 : lDir ≠ gqB2 := by decide
@[simp] theorem gq_prB2_ne_lFle : gqB2 ≠ lFle := by decide
@[simp] theorem gq_lFle_ne_prB2 : lFle ≠ gqB2 := by decide
@[simp] theorem gq_prB2_ne_lKb : gqB2 ≠ lKb := by decide
@[simp] theorem gq_lKb_ne_prB2 : lKb ≠ gqB2 := by decide
@[simp] theorem gq_prR_ne_prK : gqR ≠ gqK := by decide
@[simp] theorem gq_prR_ne_prD : gqR ≠ gqD := by decide
@[simp] theorem gq_prR_ne_prH : gqR ≠ gqH := by decide
@[simp] theorem gq_prR_ne_prO : gqR ≠ gqO := by decide
@[simp] theorem gq_prR_ne_prDm : gqR ≠ gqDm := by decide
@[simp] theorem gq_prR_ne_prB : gqR ≠ gqB := by decide
@[simp] theorem gq_prR_ne_prX : gqR ≠ gqX := by decide
@[simp] theorem gq_prR_ne_prO1 : gqR ≠ gqO1 := by decide
@[simp] theorem gq_prR_ne_prO2 : gqR ≠ gqO2 := by decide
@[simp] theorem gq_prR_ne_prV : gqR ≠ gqV := by decide
@[simp] theorem gq_prR_ne_prB2 : gqR ≠ gqB2 := by decide
@[simp] theorem gq_prR_ne_lFl : gqR ≠ lFl := by decide
@[simp] theorem gq_lFl_ne_prR : lFl ≠ gqR := by decide
@[simp] theorem gq_prR_ne_lDh : gqR ≠ lDh := by decide
@[simp] theorem gq_lDh_ne_prR : lDh ≠ gqR := by decide
@[simp] theorem gq_prR_ne_lDt : gqR ≠ lDt := by decide
@[simp] theorem gq_lDt_ne_prR : lDt ≠ gqR := by decide
@[simp] theorem gq_prR_ne_lDg : gqR ≠ lDg := by decide
@[simp] theorem gq_lDg_ne_prR : lDg ≠ gqR := by decide
@[simp] theorem gq_prR_ne_lDi : gqR ≠ lDi := by decide
@[simp] theorem gq_lDi_ne_prR : lDi ≠ gqR := by decide
@[simp] theorem gq_prR_ne_lRp : gqR ≠ lRp := by decide
@[simp] theorem gq_lRp_ne_prR : lRp ≠ gqR := by decide
@[simp] theorem gq_prR_ne_lRn : gqR ≠ lRn := by decide
@[simp] theorem gq_lRn_ne_prR : lRn ≠ gqR := by decide
@[simp] theorem gq_prR_ne_lDir : gqR ≠ lDir := by decide
@[simp] theorem gq_lDir_ne_prR : lDir ≠ gqR := by decide
@[simp] theorem gq_prR_ne_lFle : gqR ≠ lFle := by decide
@[simp] theorem gq_lFle_ne_prR : lFle ≠ gqR := by decide
@[simp] theorem gq_prR_ne_lKb : gqR ≠ lKb := by decide
@[simp] theorem gq_lKb_ne_prR : lKb ≠ gqR := by decide

theorem rowsW_append (xs : List (Nat × EIdx)) (p : Nat × EIdx) :
    rowsW (xs ++ [p]) = rowsW xs ++ [BitVec.ofNat 64 p.1, Enc.idxW p.2] := by
  induction xs with
  | nil => rfl
  | cons q qs ih => simp [rowsW, ih]

def gqParams : List MlS := [gqK, gqD, gqH, gqO]
def gqLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, gqDm, gqB, gqX, gqO1, gqO2, gqV, gqB2, gqR]

def gqBody : ProgHOL 64 := prologue gqLocals
  (.ite (tagIsE gqH 6)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv gqH)) (.seq eViewP
    (.seq (.assign .local gqDm (.load .one (vv lRp)))
    (.seq (.assign .local gqB (.load .one (.op .add [vv lRp, .const 8])))
    (.ite (.cmp .equal (vv gqK) (.const 0))
      (.seq (.call (some (some (.local, gqO1), none)) ExPre.fAppend [vv gqO, vv gqD])
      (.seq (.call (some (some (.local, gqO2), none)) ExPre.fAppend [vv gqO1, vv gqDm]) (.return (vv gqO2))))
      (.seq (.call (some (some (.local, gqX), none)) fHi [.const 0, .const 1, vv gqB])
      (.ite (vv gqX)
        (.seq (.call (some (some (.local, gqO1), none)) ExPre.fAppend [vv gqO, vv gqD])
        (.seq (.call (some (some (.local, gqO2), none)) ExPre.fAppend [vv gqO1, vv gqDm])
        (.seq (.call (some (some (.local, gqV), none)) fInternFVar [vv gqDm, vv gqD])
        (.seq (.call (some (some (.local, gqB2), none)) ExI.fInst1F
            [.const (BitVec.ofNat 64 coreWalkFuel), vv gqB, vv gqV, .const 0])
        (.seq (.call (some (some (.local, gqR), none)) fGq
            [.op .sub [vv gqK, .const 1], .op .add [vv gqD, .const 1], vv gqB2, vv gqO2])
          (.return (vv gqR)))))))
        (.seq (.call (some (some (.local, gqR), none)) fGq
            [.op .sub [vv gqK, .const 1], .op .add [vv gqD, .const 1], vv gqB, vv gqO])
          (.return (vv gqR)))))))))))
    (.return (.const 0)))

section
variable {σ : Type}

/-- `0` for `none`, else a rows block (rows below `2 ^ 63`, fewer than `2 ^ 58`). -/
def PostRows (C : Ctx) (o : Option (Array (Nat × EIdx))) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧ (o = none → w = 0) ∧
    ∀ rows, o = some rows → ∃ ob, w = cellA C ob ∧ BlkAt H' ob (rowsW rows.toList) ∧
      (∀ p ∈ rows.toList, p.1 < 2 ^ 63) ∧ rows.size < 2 ^ 58

theorem postRows_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostRows C a w s' st → PostRows C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h1, h2⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h1, h2⟩

theorem gq_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ gqLocals → (ctxEnv C ++ gqParams.zip vals).get x = none :=
  Knot.params_none C gqLocals gqParams vals (by decide) (by decide)

structure GqCodes (C : Ctx) : Prop where
  pf : PfCodes C
  app : C.code.lookup ExPre.fAppend = some (ExPre.appParams.map (fun p => (p, ShapeHOL.one)), ExPre.appBody C, .one)
  fv : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one)
  inst : C.code.lookup ExI.fInst1F = some ([pFu, pH, ExI.pV, ExI.pD].map (fun p => (p, ShapeHOL.one)),
    ExI.fastBody C, .one)
  instC : ExI.Codes C (ExI.body C)
  self : C.code.lookup fGq = some (gqParams.map (fun p => (p, ShapeHOL.one)), gqBody, .one)

theorem gq_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : GqCodes C) :
    ∀ k (d : Nat) (h : EIdx) (out : List (Nat × EIdx)) (o : Nat) (H : List (BitVec 64)) (s : AState), C.H <+: H →
      BlkAt H o (rowsW out) → d + k < 2 ^ 63 → out.length + k < 2 ^ 57 → (∀ p ∈ out, p.1 < 2 ^ 63) →
      SpecR (σ := σ) (Pre (ctxH C H) s (gqParams.zip [BitVec.ofNat 64 k, BitVec.ofNat 64 d, Enc.idxW h, cellA C o]))
        gqBody s (projGuardRowsGo k d h out.toArray) (PostRows (ctxH C H)) := by
  intro k
  induction k with
  | zero =>
    intro d h out o H s hp hbo hdk hok' hout
    refine specR_prologue (postRows_locals _) (gq_none _ _) ?_
    rw [projGuardRowsGo]
    refine Knot.specR_tagIteV gqH h 6 (by decide) (by decide) (by simp +decide [Env.get, gqParams, ctxEnv]) (fun htg => ?_) (fun htg => ?_)
    swap
    · rw [if_neg (show ¬ (h.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg)]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl,
        fun _ => rfl, fun rows hr => by cases hr⟩)
    rw [if_pos (show (h.tag == ETag.forallE) = true by simp [htg, ETag.forallE])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv gqH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, gqParams, ctxEnv]) ?_
    refine specR_viewP (C := ctxH C H) h (by simp) (by simp +decide [Env.get] <;> rfl)
      (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
    refine specR_congr (view_bind_eq h v _ s hv) ?_
    have h6 : v.tagN = 6 := by rw [htn, htg]; rfl
    obtain ⟨dom, b, rfl⟩ : ∃ dom b, v = .forallE dom b := by cases v <;> simp [ENodeView.tagN] at h6 ⊢
    dsimp only
    refine specR_loadI' gqDm (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW dom) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW dom) [Enc.idxW b] []) ?_
    refine specR_loadI' gqB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW dom) (Enc.idxW b) [] []) ?_
    refine specR_dropM ?_
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, gqParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine ExPre.specR_callApp (C := ctxH C H) (ctxOK_H hok H) hc.app gqO1 (vv gqO) (vv gqD) o (rowsW out)
      (BitVec.ofNat 64 d) (by decide) hbo (by simp +decide [Env.get, gqParams, ctxEnv] <;> rfl) (by simp +decide [Env.get, gqParams, ctxEnv]) (fun Ha oa hpa hba => ?_)
    refine ExPre.specR_callApp (C := ctxH C Ha) (ctxOK_H hok Ha) hc.app gqO2 (vv gqO1) (vv gqDm) oa
      (rowsW out ++ [BitVec.ofNat 64 d]) (Enc.idxW dom) (by decide) hba (by simp <;> rfl) (by simp) (fun Hb ob hpb hbb => ?_)
    have hbb' : BlkAt Hb ob (rowsW (out ++ [(d, dom)])) := by rw [rowsW_append]; simpa using hbb
    have hall : ∀ p ∈ out ++ [(d, dom)], p.1 < 2 ^ 63 := by
      intro p hp'
      simp at hp'
      rcases hp' with hp' | hp'
      · exact hout p hp'
      · subst hp'; simp; omega
    exact specR_returnI _ (cellA C ob) (by simp; rfl) (fun t ht => ⟨Hb, hpa.trans hpb, sr_of_eq ht.sr rfl rfl rfl rfl,
      (fun h => by cases h), fun rows hr => by cases hr; exact ⟨ob, rfl, by simpa using hbb', by simpa using hall, by simp; omega⟩⟩)
  | succ k ih =>
    intro d h out o H s hp hbo hdk hok' hout
    refine specR_prologue (postRows_locals _) (gq_none _ _) ?_
    rw [projGuardRowsGo]
    refine Knot.specR_tagIteV gqH h 6 (by decide) (by decide) (by simp +decide [Env.get, gqParams, ctxEnv]) (fun htg => ?_) (fun htg => ?_)
    swap
    · rw [if_neg (show ¬ (h.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg)]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl,
        fun _ => rfl, fun rows hr => by cases hr⟩)
    rw [if_pos (show (h.tag == ETag.forallE) = true by simp [htg, ETag.forallE])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv gqH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, gqParams, ctxEnv]) ?_
    refine specR_viewP (C := ctxH C H) h (by simp) (by simp +decide [Env.get] <;> rfl)
      (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
    refine specR_congr (view_bind_eq h v _ s hv) ?_
    have h6 : v.tagN = 6 := by rw [htn, htg]; rfl
    obtain ⟨dom, b, rfl⟩ : ∃ dom b, v = .forallE dom b := by cases v <;> simp [ENodeView.tagN] at h6 ⊢
    dsimp only
    refine specR_loadI' gqDm (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW dom) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW dom) [Enc.idxW b] []) ?_
    refine specR_loadI' gqB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW dom) (Enc.idxW b) [] []) ?_
    refine specR_dropM ?_
    have hne := ofNat_succ_ne k (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, gqParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_callNIH (C := ctxH C H) gqX fHi hiParams [.const 0, .const 1, vv gqB] hiBody
      [BitVec.ofNat 64 0, BitVec.ofNat 64 1, Enc.idxW b] (by decide) rfl (by decide) hc.pf.hi
      ⟨rfl, rfl, by simp, trivial⟩ (PostB (ctxH C H)) (fun c w _ _ => w = boolW c)
      (fun c w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu hiParams _ rfl hlk)
        (hb_spec (ctxH C H) (ctxOK_H hok H) (hvCodes_H hc.pf.hv H) s 0 b (by unfold coreWalkFuel; norm_num)))
      (fun c w s1 HA hpA hw => ?_)
    subst hw
    have hRet : ∀ (Hc : List (BitVec 64)) (sc : AState) (Γ : Env) (r : Option (Array (Nat × EIdx))) (w : BitVec 64)
        (H' : List (BitVec 64)), H <+: Hc → Hc <+: H' → Γ.get gqR = some w → (r = none → w = 0) →
        (∀ rows, r = some rows → ∃ ob, w = cellA C ob ∧ BlkAt H' ob (rowsW rows.toList) ∧
          (∀ p ∈ rows.toList, p.1 < 2 ^ 63) ∧ rows.size < 2 ^ 58) →
        SpecR (σ := σ) (Inv (ctxH C H') sc Γ [] (ctxLocals ++ gqLocals)) (.return (vv gqR)) sc (pure r)
          (PostRows (ctxH C H)) :=
      fun Hc sc Γ r w H' h1 h2 hR hn hs => specR_returnI _ w (by simp [hR])
        (fun t ht => ⟨H', h1.trans h2, sr_of_eq ht.sr rfl rfl rfl rfl, hn, hs⟩)
    cases c
    · refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine specR_congr (m' := projGuardRowsGo k (d + 1) b out.toArray >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C HA) gqR fGq gqParams
        [.op .sub [vv gqK, .const 1], .op .add [vv gqD, .const 1], vv gqB, vv gqO] gqBody
        [BitVec.ofNat 64 k, BitVec.ofNat 64 (d + 1), Enc.idxW b, cellA C o] (by decide) rfl (by decide) hc.self
        ⟨by simp +decide [sev, Env.get, gqParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _,
          by simp +decide [sev, Env.get, gqParams, ctxEnv]; exact word_add1_eq d, by simp, by simp +decide [Env.get, gqParams, ctxEnv] <;> rfl, trivial⟩
        (PostRows (ctxH C HA))
        (fun r w _ H' => (r = none → w = 0) ∧ ∀ rows, r = some rows → ∃ ob, w = cellA C ob ∧
          BlkAt H' ob (rowsW rows.toList) ∧ (∀ p ∈ rows.toList, p.1 < 2 ^ 63) ∧ rows.size < 2 ^ 58)
        (fun r w s' st ⟨H', hp', hsr, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu gqParams _ rfl hlk)
          (ih (d + 1) b out o HA s1 (hp.trans hpA) (blkAt_mono hbo hpA) (by omega) (by omega) hout))
        (fun r w s2 HB hpB ⟨h1, h2⟩ => ?_)
      exact hRet HA s2 _ r w HB hpA hpB (by simp) h1 h2
    · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [↓reduceIte]
      refine ExPre.specR_callApp (C := ctxH C HA) (ctxOK_H hok HA) hc.app gqO1 (vv gqO) (vv gqD) o (rowsW out)
        (BitVec.ofNat 64 d) (by decide) (blkAt_mono hbo hpA) (by simp +decide [Env.get, gqParams, ctxEnv] <;> rfl) (by simp +decide [Env.get, gqParams, ctxEnv]) (fun Ha oa hpa hba => ?_)
      refine ExPre.specR_callApp (C := ctxH C Ha) (ctxOK_H hok Ha) hc.app gqO2 (vv gqO1) (vv gqDm) oa
        (rowsW out ++ [BitVec.ofNat 64 d]) (Enc.idxW dom) (by decide) hba (by simp <;> rfl) (by simp) (fun Hb ob hpb hbb => ?_)
      have hbb' : BlkAt Hb ob (rowsW (out ++ [(d, dom)])) := by rw [rowsW_append]; simpa using hbb
      refine ILP.specR_internFVarI (C := ctxH C Hb) ra (ctxOK_H hok Hb) hc.fv gqV (vv gqDm) (vv gqD) dom d
        (by omega) (by decide) (by simp) (by simp +decide [Env.get, gqParams, ctxEnv]) (fun fv s2 => ?_)
      refine ILP.callE_spec (C := ctxH C Hb) gqB2 ExI.fInst1F [pFu, pH, ExI.pV, ExI.pD]
        [.const (BitVec.ofNat 64 coreWalkFuel), vv gqB, vv gqV, .const 0] (ExI.fastBody C)
        [BitVec.ofNat 64 coreWalkFuel, Enc.idxW b, Enc.idxW fv, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.inst
        ⟨rfl, by simp, by simp, rfl, trivial⟩
        (ExI.fast_spec ra (ctxH C Hb) (ctxOK_H hok Hb) (ExIS.codes_H C Hb hc.instC) s2 coreWalkFuel b fv 0
          CV.coreWalkFuel_lt (by decide)) (fun b2 s3 => ?_)
      have hall : ∀ p ∈ out ++ [(d, dom)], p.1 < 2 ^ 63 := by
        intro p hp'
        simp at hp'
        rcases hp' with hp' | hp'
        · exact hout p hp'
        · subst hp'; simp; omega
      rw [show out.toArray.push (d, dom) = (out ++ [(d, dom)]).toArray by simp]
      refine specR_congr (m' := projGuardRowsGo k (d + 1) b2 (out ++ [(d, dom)]).toArray >>= fun r => pure r)
        (by simp) ?_
      refine specR_callNIH (C := ctxH C Hb) gqR fGq gqParams
        [.op .sub [vv gqK, .const 1], .op .add [vv gqD, .const 1], vv gqB2, vv gqO2] gqBody
        [BitVec.ofNat 64 k, BitVec.ofNat 64 (d + 1), Enc.idxW b2, cellA C ob] (by decide) rfl (by decide) hc.self
        ⟨by simp +decide [sev, Env.get, gqParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _,
          by simp +decide [sev, Env.get, gqParams, ctxEnv]; exact word_add1_eq d, by simp, by simp <;> rfl, trivial⟩
        (PostRows (ctxH C Hb))
        (fun r w _ H' => (r = none → w = 0) ∧ ∀ rows, r = some rows → ∃ ob, w = cellA C ob ∧
          BlkAt H' ob (rowsW rows.toList) ∧ (∀ p ∈ rows.toList, p.1 < 2 ^ 63) ∧ rows.size < 2 ^ 58)
        (fun r w s' st ⟨H', hp', hsr, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu gqParams _ rfl hlk)
          (ih (d + 1) b2 (out ++ [(d, dom)]) ob Hb s3 (hp.trans (hpA.trans (hpa.trans hpb))) hbb' (by omega)
            (by simp; omega) hall))
        (fun r w s4 HB hpB ⟨h1, h2⟩ => ?_)
      exact hRet Hb s4 _ r w HB (hpA.trans (hpa.trans hpb)) hpB (by simp) h1 h2

end

end ConPanqueque.T.WC
