import ConPanqueque.T.Core.DeltaQuick
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `lazyDeltaStep`: one lazy-delta step

The outcome as `dsW` (see `DeltaQuick`). Hints are compared on their `hintN` words (`hltE`, `hsrE`). Every callee
is a hypothesis restricted to the states of an invariant `Q`, which each callee's twin preserves.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def ldA := ofString "lds_a"
def ldB := ofString "lds_b"
def ldUa := ofString "lds_ua"
def ldUb := ofString "lds_ub"
def ldX := ofString "lds_x"
def ldY := ofString "lds_y"
def ldZ := ofString "lds_z"
def ldR := ofString "lds_r"
def ldHa := ofString "lds_ha"
def ldHb := ofString "lds_hb"
def ldS := ofString "lds_s"
def ldP := ofString "lds_p"
def ldX2 := ofString "lds_x2"
def ldY2 := ofString "lds_y2"
def ldZ2 := ofString "lds_z2"
def fLds := ofString "lazyDeltaStep"

@[simp] theorem lds_ldA_ne_ldB : ldA ≠ ldB := by decide
@[simp] theorem lds_ldA_ne_ldUa : ldA ≠ ldUa := by decide
@[simp] theorem lds_ldA_ne_ldUb : ldA ≠ ldUb := by decide
@[simp] theorem lds_ldA_ne_ldX : ldA ≠ ldX := by decide
@[simp] theorem lds_ldA_ne_ldY : ldA ≠ ldY := by decide
@[simp] theorem lds_ldA_ne_ldZ : ldA ≠ ldZ := by decide
@[simp] theorem lds_ldA_ne_ldR : ldA ≠ ldR := by decide
@[simp] theorem lds_ldA_ne_ldHa : ldA ≠ ldHa := by decide
@[simp] theorem lds_ldA_ne_ldHb : ldA ≠ ldHb := by decide
@[simp] theorem lds_ldA_ne_ldS : ldA ≠ ldS := by decide
@[simp] theorem lds_ldA_ne_ldP : ldA ≠ ldP := by decide
@[simp] theorem lds_ldA_ne_ldX2 : ldA ≠ ldX2 := by decide
@[simp] theorem lds_ldA_ne_ldY2 : ldA ≠ ldY2 := by decide
@[simp] theorem lds_ldA_ne_ldZ2 : ldA ≠ ldZ2 := by decide
@[simp] theorem lds_ldA_ne_lFl : ldA ≠ lFl := by decide
@[simp] theorem lds_lFl_ne_ldA : lFl ≠ ldA := by decide
@[simp] theorem lds_ldA_ne_lDh : ldA ≠ lDh := by decide
@[simp] theorem lds_lDh_ne_ldA : lDh ≠ ldA := by decide
@[simp] theorem lds_ldA_ne_lDt : ldA ≠ lDt := by decide
@[simp] theorem lds_lDt_ne_ldA : lDt ≠ ldA := by decide
@[simp] theorem lds_ldA_ne_lDg : ldA ≠ lDg := by decide
@[simp] theorem lds_lDg_ne_ldA : lDg ≠ ldA := by decide
@[simp] theorem lds_ldA_ne_lDi : ldA ≠ lDi := by decide
@[simp] theorem lds_lDi_ne_ldA : lDi ≠ ldA := by decide
@[simp] theorem lds_ldA_ne_lRp : ldA ≠ lRp := by decide
@[simp] theorem lds_lRp_ne_ldA : lRp ≠ ldA := by decide
@[simp] theorem lds_ldA_ne_lRn : ldA ≠ lRn := by decide
@[simp] theorem lds_lRn_ne_ldA : lRn ≠ ldA := by decide
@[simp] theorem lds_ldA_ne_lFle : ldA ≠ lFle := by decide
@[simp] theorem lds_lFle_ne_ldA : lFle ≠ ldA := by decide
@[simp] theorem lds_ldA_ne_lKb : ldA ≠ lKb := by decide
@[simp] theorem lds_lKb_ne_ldA : lKb ≠ ldA := by decide
@[simp] theorem lds_ldA_ne_lDir : ldA ≠ lDir := by decide
@[simp] theorem lds_lDir_ne_ldA : lDir ≠ ldA := by decide
@[simp] theorem lds_ldA_ne_lFln : ldA ≠ lFln := by decide
@[simp] theorem lds_lFln_ne_ldA : lFln ≠ ldA := by decide
@[simp] theorem lds_ldA_ne_lFll : ldA ≠ lFll := by decide
@[simp] theorem lds_lFll_ne_ldA : lFll ≠ ldA := by decide
@[simp] theorem lds_ldA_ne_lFls : ldA ≠ lFls := by decide
@[simp] theorem lds_lFls_ne_ldA : lFls ≠ ldA := by decide
@[simp] theorem lds_ldA_ne_kFu : ldA ≠ kFu := by decide
@[simp] theorem lds_kFu_ne_ldA : kFu ≠ ldA := by decide
@[simp] theorem lds_ldA_ne_kD : ldA ≠ kD := by decide
@[simp] theorem lds_kD_ne_ldA : kD ≠ ldA := by decide
@[simp] theorem lds_ldB_ne_ldA : ldB ≠ ldA := by decide
@[simp] theorem lds_ldB_ne_ldUa : ldB ≠ ldUa := by decide
@[simp] theorem lds_ldB_ne_ldUb : ldB ≠ ldUb := by decide
@[simp] theorem lds_ldB_ne_ldX : ldB ≠ ldX := by decide
@[simp] theorem lds_ldB_ne_ldY : ldB ≠ ldY := by decide
@[simp] theorem lds_ldB_ne_ldZ : ldB ≠ ldZ := by decide
@[simp] theorem lds_ldB_ne_ldR : ldB ≠ ldR := by decide
@[simp] theorem lds_ldB_ne_ldHa : ldB ≠ ldHa := by decide
@[simp] theorem lds_ldB_ne_ldHb : ldB ≠ ldHb := by decide
@[simp] theorem lds_ldB_ne_ldS : ldB ≠ ldS := by decide
@[simp] theorem lds_ldB_ne_ldP : ldB ≠ ldP := by decide
@[simp] theorem lds_ldB_ne_ldX2 : ldB ≠ ldX2 := by decide
@[simp] theorem lds_ldB_ne_ldY2 : ldB ≠ ldY2 := by decide
@[simp] theorem lds_ldB_ne_ldZ2 : ldB ≠ ldZ2 := by decide
@[simp] theorem lds_ldB_ne_lFl : ldB ≠ lFl := by decide
@[simp] theorem lds_lFl_ne_ldB : lFl ≠ ldB := by decide
@[simp] theorem lds_ldB_ne_lDh : ldB ≠ lDh := by decide
@[simp] theorem lds_lDh_ne_ldB : lDh ≠ ldB := by decide
@[simp] theorem lds_ldB_ne_lDt : ldB ≠ lDt := by decide
@[simp] theorem lds_lDt_ne_ldB : lDt ≠ ldB := by decide
@[simp] theorem lds_ldB_ne_lDg : ldB ≠ lDg := by decide
@[simp] theorem lds_lDg_ne_ldB : lDg ≠ ldB := by decide
@[simp] theorem lds_ldB_ne_lDi : ldB ≠ lDi := by decide
@[simp] theorem lds_lDi_ne_ldB : lDi ≠ ldB := by decide
@[simp] theorem lds_ldB_ne_lRp : ldB ≠ lRp := by decide
@[simp] theorem lds_lRp_ne_ldB : lRp ≠ ldB := by decide
@[simp] theorem lds_ldB_ne_lRn : ldB ≠ lRn := by decide
@[simp] theorem lds_lRn_ne_ldB : lRn ≠ ldB := by decide
@[simp] theorem lds_ldB_ne_lFle : ldB ≠ lFle := by decide
@[simp] theorem lds_lFle_ne_ldB : lFle ≠ ldB := by decide
@[simp] theorem lds_ldB_ne_lKb : ldB ≠ lKb := by decide
@[simp] theorem lds_lKb_ne_ldB : lKb ≠ ldB := by decide
@[simp] theorem lds_ldB_ne_lDir : ldB ≠ lDir := by decide
@[simp] theorem lds_lDir_ne_ldB : lDir ≠ ldB := by decide
@[simp] theorem lds_ldB_ne_lFln : ldB ≠ lFln := by decide
@[simp] theorem lds_lFln_ne_ldB : lFln ≠ ldB := by decide
@[simp] theorem lds_ldB_ne_lFll : ldB ≠ lFll := by decide
@[simp] theorem lds_lFll_ne_ldB : lFll ≠ ldB := by decide
@[simp] theorem lds_ldB_ne_lFls : ldB ≠ lFls := by decide
@[simp] theorem lds_lFls_ne_ldB : lFls ≠ ldB := by decide
@[simp] theorem lds_ldB_ne_kFu : ldB ≠ kFu := by decide
@[simp] theorem lds_kFu_ne_ldB : kFu ≠ ldB := by decide
@[simp] theorem lds_ldB_ne_kD : ldB ≠ kD := by decide
@[simp] theorem lds_kD_ne_ldB : kD ≠ ldB := by decide
@[simp] theorem lds_ldUa_ne_ldA : ldUa ≠ ldA := by decide
@[simp] theorem lds_ldUa_ne_ldB : ldUa ≠ ldB := by decide
@[simp] theorem lds_ldUa_ne_ldUb : ldUa ≠ ldUb := by decide
@[simp] theorem lds_ldUa_ne_ldX : ldUa ≠ ldX := by decide
@[simp] theorem lds_ldUa_ne_ldY : ldUa ≠ ldY := by decide
@[simp] theorem lds_ldUa_ne_ldZ : ldUa ≠ ldZ := by decide
@[simp] theorem lds_ldUa_ne_ldR : ldUa ≠ ldR := by decide
@[simp] theorem lds_ldUa_ne_ldHa : ldUa ≠ ldHa := by decide
@[simp] theorem lds_ldUa_ne_ldHb : ldUa ≠ ldHb := by decide
@[simp] theorem lds_ldUa_ne_ldS : ldUa ≠ ldS := by decide
@[simp] theorem lds_ldUa_ne_ldP : ldUa ≠ ldP := by decide
@[simp] theorem lds_ldUa_ne_ldX2 : ldUa ≠ ldX2 := by decide
@[simp] theorem lds_ldUa_ne_ldY2 : ldUa ≠ ldY2 := by decide
@[simp] theorem lds_ldUa_ne_ldZ2 : ldUa ≠ ldZ2 := by decide
@[simp] theorem lds_ldUa_ne_lFl : ldUa ≠ lFl := by decide
@[simp] theorem lds_lFl_ne_ldUa : lFl ≠ ldUa := by decide
@[simp] theorem lds_ldUa_ne_lDh : ldUa ≠ lDh := by decide
@[simp] theorem lds_lDh_ne_ldUa : lDh ≠ ldUa := by decide
@[simp] theorem lds_ldUa_ne_lDt : ldUa ≠ lDt := by decide
@[simp] theorem lds_lDt_ne_ldUa : lDt ≠ ldUa := by decide
@[simp] theorem lds_ldUa_ne_lDg : ldUa ≠ lDg := by decide
@[simp] theorem lds_lDg_ne_ldUa : lDg ≠ ldUa := by decide
@[simp] theorem lds_ldUa_ne_lDi : ldUa ≠ lDi := by decide
@[simp] theorem lds_lDi_ne_ldUa : lDi ≠ ldUa := by decide
@[simp] theorem lds_ldUa_ne_lRp : ldUa ≠ lRp := by decide
@[simp] theorem lds_lRp_ne_ldUa : lRp ≠ ldUa := by decide
@[simp] theorem lds_ldUa_ne_lRn : ldUa ≠ lRn := by decide
@[simp] theorem lds_lRn_ne_ldUa : lRn ≠ ldUa := by decide
@[simp] theorem lds_ldUa_ne_lFle : ldUa ≠ lFle := by decide
@[simp] theorem lds_lFle_ne_ldUa : lFle ≠ ldUa := by decide
@[simp] theorem lds_ldUa_ne_lKb : ldUa ≠ lKb := by decide
@[simp] theorem lds_lKb_ne_ldUa : lKb ≠ ldUa := by decide
@[simp] theorem lds_ldUa_ne_lDir : ldUa ≠ lDir := by decide
@[simp] theorem lds_lDir_ne_ldUa : lDir ≠ ldUa := by decide
@[simp] theorem lds_ldUa_ne_lFln : ldUa ≠ lFln := by decide
@[simp] theorem lds_lFln_ne_ldUa : lFln ≠ ldUa := by decide
@[simp] theorem lds_ldUa_ne_lFll : ldUa ≠ lFll := by decide
@[simp] theorem lds_lFll_ne_ldUa : lFll ≠ ldUa := by decide
@[simp] theorem lds_ldUa_ne_lFls : ldUa ≠ lFls := by decide
@[simp] theorem lds_lFls_ne_ldUa : lFls ≠ ldUa := by decide
@[simp] theorem lds_ldUa_ne_kFu : ldUa ≠ kFu := by decide
@[simp] theorem lds_kFu_ne_ldUa : kFu ≠ ldUa := by decide
@[simp] theorem lds_ldUa_ne_kD : ldUa ≠ kD := by decide
@[simp] theorem lds_kD_ne_ldUa : kD ≠ ldUa := by decide
@[simp] theorem lds_ldUb_ne_ldA : ldUb ≠ ldA := by decide
@[simp] theorem lds_ldUb_ne_ldB : ldUb ≠ ldB := by decide
@[simp] theorem lds_ldUb_ne_ldUa : ldUb ≠ ldUa := by decide
@[simp] theorem lds_ldUb_ne_ldX : ldUb ≠ ldX := by decide
@[simp] theorem lds_ldUb_ne_ldY : ldUb ≠ ldY := by decide
@[simp] theorem lds_ldUb_ne_ldZ : ldUb ≠ ldZ := by decide
@[simp] theorem lds_ldUb_ne_ldR : ldUb ≠ ldR := by decide
@[simp] theorem lds_ldUb_ne_ldHa : ldUb ≠ ldHa := by decide
@[simp] theorem lds_ldUb_ne_ldHb : ldUb ≠ ldHb := by decide
@[simp] theorem lds_ldUb_ne_ldS : ldUb ≠ ldS := by decide
@[simp] theorem lds_ldUb_ne_ldP : ldUb ≠ ldP := by decide
@[simp] theorem lds_ldUb_ne_ldX2 : ldUb ≠ ldX2 := by decide
@[simp] theorem lds_ldUb_ne_ldY2 : ldUb ≠ ldY2 := by decide
@[simp] theorem lds_ldUb_ne_ldZ2 : ldUb ≠ ldZ2 := by decide
@[simp] theorem lds_ldUb_ne_lFl : ldUb ≠ lFl := by decide
@[simp] theorem lds_lFl_ne_ldUb : lFl ≠ ldUb := by decide
@[simp] theorem lds_ldUb_ne_lDh : ldUb ≠ lDh := by decide
@[simp] theorem lds_lDh_ne_ldUb : lDh ≠ ldUb := by decide
@[simp] theorem lds_ldUb_ne_lDt : ldUb ≠ lDt := by decide
@[simp] theorem lds_lDt_ne_ldUb : lDt ≠ ldUb := by decide
@[simp] theorem lds_ldUb_ne_lDg : ldUb ≠ lDg := by decide
@[simp] theorem lds_lDg_ne_ldUb : lDg ≠ ldUb := by decide
@[simp] theorem lds_ldUb_ne_lDi : ldUb ≠ lDi := by decide
@[simp] theorem lds_lDi_ne_ldUb : lDi ≠ ldUb := by decide
@[simp] theorem lds_ldUb_ne_lRp : ldUb ≠ lRp := by decide
@[simp] theorem lds_lRp_ne_ldUb : lRp ≠ ldUb := by decide
@[simp] theorem lds_ldUb_ne_lRn : ldUb ≠ lRn := by decide
@[simp] theorem lds_lRn_ne_ldUb : lRn ≠ ldUb := by decide
@[simp] theorem lds_ldUb_ne_lFle : ldUb ≠ lFle := by decide
@[simp] theorem lds_lFle_ne_ldUb : lFle ≠ ldUb := by decide
@[simp] theorem lds_ldUb_ne_lKb : ldUb ≠ lKb := by decide
@[simp] theorem lds_lKb_ne_ldUb : lKb ≠ ldUb := by decide
@[simp] theorem lds_ldUb_ne_lDir : ldUb ≠ lDir := by decide
@[simp] theorem lds_lDir_ne_ldUb : lDir ≠ ldUb := by decide
@[simp] theorem lds_ldUb_ne_lFln : ldUb ≠ lFln := by decide
@[simp] theorem lds_lFln_ne_ldUb : lFln ≠ ldUb := by decide
@[simp] theorem lds_ldUb_ne_lFll : ldUb ≠ lFll := by decide
@[simp] theorem lds_lFll_ne_ldUb : lFll ≠ ldUb := by decide
@[simp] theorem lds_ldUb_ne_lFls : ldUb ≠ lFls := by decide
@[simp] theorem lds_lFls_ne_ldUb : lFls ≠ ldUb := by decide
@[simp] theorem lds_ldUb_ne_kFu : ldUb ≠ kFu := by decide
@[simp] theorem lds_kFu_ne_ldUb : kFu ≠ ldUb := by decide
@[simp] theorem lds_ldUb_ne_kD : ldUb ≠ kD := by decide
@[simp] theorem lds_kD_ne_ldUb : kD ≠ ldUb := by decide
@[simp] theorem lds_ldX_ne_ldA : ldX ≠ ldA := by decide
@[simp] theorem lds_ldX_ne_ldB : ldX ≠ ldB := by decide
@[simp] theorem lds_ldX_ne_ldUa : ldX ≠ ldUa := by decide
@[simp] theorem lds_ldX_ne_ldUb : ldX ≠ ldUb := by decide
@[simp] theorem lds_ldX_ne_ldY : ldX ≠ ldY := by decide
@[simp] theorem lds_ldX_ne_ldZ : ldX ≠ ldZ := by decide
@[simp] theorem lds_ldX_ne_ldR : ldX ≠ ldR := by decide
@[simp] theorem lds_ldX_ne_ldHa : ldX ≠ ldHa := by decide
@[simp] theorem lds_ldX_ne_ldHb : ldX ≠ ldHb := by decide
@[simp] theorem lds_ldX_ne_ldS : ldX ≠ ldS := by decide
@[simp] theorem lds_ldX_ne_ldP : ldX ≠ ldP := by decide
@[simp] theorem lds_ldX_ne_ldX2 : ldX ≠ ldX2 := by decide
@[simp] theorem lds_ldX_ne_ldY2 : ldX ≠ ldY2 := by decide
@[simp] theorem lds_ldX_ne_ldZ2 : ldX ≠ ldZ2 := by decide
@[simp] theorem lds_ldX_ne_lFl : ldX ≠ lFl := by decide
@[simp] theorem lds_lFl_ne_ldX : lFl ≠ ldX := by decide
@[simp] theorem lds_ldX_ne_lDh : ldX ≠ lDh := by decide
@[simp] theorem lds_lDh_ne_ldX : lDh ≠ ldX := by decide
@[simp] theorem lds_ldX_ne_lDt : ldX ≠ lDt := by decide
@[simp] theorem lds_lDt_ne_ldX : lDt ≠ ldX := by decide
@[simp] theorem lds_ldX_ne_lDg : ldX ≠ lDg := by decide
@[simp] theorem lds_lDg_ne_ldX : lDg ≠ ldX := by decide
@[simp] theorem lds_ldX_ne_lDi : ldX ≠ lDi := by decide
@[simp] theorem lds_lDi_ne_ldX : lDi ≠ ldX := by decide
@[simp] theorem lds_ldX_ne_lRp : ldX ≠ lRp := by decide
@[simp] theorem lds_lRp_ne_ldX : lRp ≠ ldX := by decide
@[simp] theorem lds_ldX_ne_lRn : ldX ≠ lRn := by decide
@[simp] theorem lds_lRn_ne_ldX : lRn ≠ ldX := by decide
@[simp] theorem lds_ldX_ne_lFle : ldX ≠ lFle := by decide
@[simp] theorem lds_lFle_ne_ldX : lFle ≠ ldX := by decide
@[simp] theorem lds_ldX_ne_lKb : ldX ≠ lKb := by decide
@[simp] theorem lds_lKb_ne_ldX : lKb ≠ ldX := by decide
@[simp] theorem lds_ldX_ne_lDir : ldX ≠ lDir := by decide
@[simp] theorem lds_lDir_ne_ldX : lDir ≠ ldX := by decide
@[simp] theorem lds_ldX_ne_lFln : ldX ≠ lFln := by decide
@[simp] theorem lds_lFln_ne_ldX : lFln ≠ ldX := by decide
@[simp] theorem lds_ldX_ne_lFll : ldX ≠ lFll := by decide
@[simp] theorem lds_lFll_ne_ldX : lFll ≠ ldX := by decide
@[simp] theorem lds_ldX_ne_lFls : ldX ≠ lFls := by decide
@[simp] theorem lds_lFls_ne_ldX : lFls ≠ ldX := by decide
@[simp] theorem lds_ldX_ne_kFu : ldX ≠ kFu := by decide
@[simp] theorem lds_kFu_ne_ldX : kFu ≠ ldX := by decide
@[simp] theorem lds_ldX_ne_kD : ldX ≠ kD := by decide
@[simp] theorem lds_kD_ne_ldX : kD ≠ ldX := by decide
@[simp] theorem lds_ldY_ne_ldA : ldY ≠ ldA := by decide
@[simp] theorem lds_ldY_ne_ldB : ldY ≠ ldB := by decide
@[simp] theorem lds_ldY_ne_ldUa : ldY ≠ ldUa := by decide
@[simp] theorem lds_ldY_ne_ldUb : ldY ≠ ldUb := by decide
@[simp] theorem lds_ldY_ne_ldX : ldY ≠ ldX := by decide
@[simp] theorem lds_ldY_ne_ldZ : ldY ≠ ldZ := by decide
@[simp] theorem lds_ldY_ne_ldR : ldY ≠ ldR := by decide
@[simp] theorem lds_ldY_ne_ldHa : ldY ≠ ldHa := by decide
@[simp] theorem lds_ldY_ne_ldHb : ldY ≠ ldHb := by decide
@[simp] theorem lds_ldY_ne_ldS : ldY ≠ ldS := by decide
@[simp] theorem lds_ldY_ne_ldP : ldY ≠ ldP := by decide
@[simp] theorem lds_ldY_ne_ldX2 : ldY ≠ ldX2 := by decide
@[simp] theorem lds_ldY_ne_ldY2 : ldY ≠ ldY2 := by decide
@[simp] theorem lds_ldY_ne_ldZ2 : ldY ≠ ldZ2 := by decide
@[simp] theorem lds_ldY_ne_lFl : ldY ≠ lFl := by decide
@[simp] theorem lds_lFl_ne_ldY : lFl ≠ ldY := by decide
@[simp] theorem lds_ldY_ne_lDh : ldY ≠ lDh := by decide
@[simp] theorem lds_lDh_ne_ldY : lDh ≠ ldY := by decide
@[simp] theorem lds_ldY_ne_lDt : ldY ≠ lDt := by decide
@[simp] theorem lds_lDt_ne_ldY : lDt ≠ ldY := by decide
@[simp] theorem lds_ldY_ne_lDg : ldY ≠ lDg := by decide
@[simp] theorem lds_lDg_ne_ldY : lDg ≠ ldY := by decide
@[simp] theorem lds_ldY_ne_lDi : ldY ≠ lDi := by decide
@[simp] theorem lds_lDi_ne_ldY : lDi ≠ ldY := by decide
@[simp] theorem lds_ldY_ne_lRp : ldY ≠ lRp := by decide
@[simp] theorem lds_lRp_ne_ldY : lRp ≠ ldY := by decide
@[simp] theorem lds_ldY_ne_lRn : ldY ≠ lRn := by decide
@[simp] theorem lds_lRn_ne_ldY : lRn ≠ ldY := by decide
@[simp] theorem lds_ldY_ne_lFle : ldY ≠ lFle := by decide
@[simp] theorem lds_lFle_ne_ldY : lFle ≠ ldY := by decide
@[simp] theorem lds_ldY_ne_lKb : ldY ≠ lKb := by decide
@[simp] theorem lds_lKb_ne_ldY : lKb ≠ ldY := by decide
@[simp] theorem lds_ldY_ne_lDir : ldY ≠ lDir := by decide
@[simp] theorem lds_lDir_ne_ldY : lDir ≠ ldY := by decide
@[simp] theorem lds_ldY_ne_lFln : ldY ≠ lFln := by decide
@[simp] theorem lds_lFln_ne_ldY : lFln ≠ ldY := by decide
@[simp] theorem lds_ldY_ne_lFll : ldY ≠ lFll := by decide
@[simp] theorem lds_lFll_ne_ldY : lFll ≠ ldY := by decide
@[simp] theorem lds_ldY_ne_lFls : ldY ≠ lFls := by decide
@[simp] theorem lds_lFls_ne_ldY : lFls ≠ ldY := by decide
@[simp] theorem lds_ldY_ne_kFu : ldY ≠ kFu := by decide
@[simp] theorem lds_kFu_ne_ldY : kFu ≠ ldY := by decide
@[simp] theorem lds_ldY_ne_kD : ldY ≠ kD := by decide
@[simp] theorem lds_kD_ne_ldY : kD ≠ ldY := by decide
@[simp] theorem lds_ldZ_ne_ldA : ldZ ≠ ldA := by decide
@[simp] theorem lds_ldZ_ne_ldB : ldZ ≠ ldB := by decide
@[simp] theorem lds_ldZ_ne_ldUa : ldZ ≠ ldUa := by decide
@[simp] theorem lds_ldZ_ne_ldUb : ldZ ≠ ldUb := by decide
@[simp] theorem lds_ldZ_ne_ldX : ldZ ≠ ldX := by decide
@[simp] theorem lds_ldZ_ne_ldY : ldZ ≠ ldY := by decide
@[simp] theorem lds_ldZ_ne_ldR : ldZ ≠ ldR := by decide
@[simp] theorem lds_ldZ_ne_ldHa : ldZ ≠ ldHa := by decide
@[simp] theorem lds_ldZ_ne_ldHb : ldZ ≠ ldHb := by decide
@[simp] theorem lds_ldZ_ne_ldS : ldZ ≠ ldS := by decide
@[simp] theorem lds_ldZ_ne_ldP : ldZ ≠ ldP := by decide
@[simp] theorem lds_ldZ_ne_ldX2 : ldZ ≠ ldX2 := by decide
@[simp] theorem lds_ldZ_ne_ldY2 : ldZ ≠ ldY2 := by decide
@[simp] theorem lds_ldZ_ne_ldZ2 : ldZ ≠ ldZ2 := by decide
@[simp] theorem lds_ldZ_ne_lFl : ldZ ≠ lFl := by decide
@[simp] theorem lds_lFl_ne_ldZ : lFl ≠ ldZ := by decide
@[simp] theorem lds_ldZ_ne_lDh : ldZ ≠ lDh := by decide
@[simp] theorem lds_lDh_ne_ldZ : lDh ≠ ldZ := by decide
@[simp] theorem lds_ldZ_ne_lDt : ldZ ≠ lDt := by decide
@[simp] theorem lds_lDt_ne_ldZ : lDt ≠ ldZ := by decide
@[simp] theorem lds_ldZ_ne_lDg : ldZ ≠ lDg := by decide
@[simp] theorem lds_lDg_ne_ldZ : lDg ≠ ldZ := by decide
@[simp] theorem lds_ldZ_ne_lDi : ldZ ≠ lDi := by decide
@[simp] theorem lds_lDi_ne_ldZ : lDi ≠ ldZ := by decide
@[simp] theorem lds_ldZ_ne_lRp : ldZ ≠ lRp := by decide
@[simp] theorem lds_lRp_ne_ldZ : lRp ≠ ldZ := by decide
@[simp] theorem lds_ldZ_ne_lRn : ldZ ≠ lRn := by decide
@[simp] theorem lds_lRn_ne_ldZ : lRn ≠ ldZ := by decide
@[simp] theorem lds_ldZ_ne_lFle : ldZ ≠ lFle := by decide
@[simp] theorem lds_lFle_ne_ldZ : lFle ≠ ldZ := by decide
@[simp] theorem lds_ldZ_ne_lKb : ldZ ≠ lKb := by decide
@[simp] theorem lds_lKb_ne_ldZ : lKb ≠ ldZ := by decide
@[simp] theorem lds_ldZ_ne_lDir : ldZ ≠ lDir := by decide
@[simp] theorem lds_lDir_ne_ldZ : lDir ≠ ldZ := by decide
@[simp] theorem lds_ldZ_ne_lFln : ldZ ≠ lFln := by decide
@[simp] theorem lds_lFln_ne_ldZ : lFln ≠ ldZ := by decide
@[simp] theorem lds_ldZ_ne_lFll : ldZ ≠ lFll := by decide
@[simp] theorem lds_lFll_ne_ldZ : lFll ≠ ldZ := by decide
@[simp] theorem lds_ldZ_ne_lFls : ldZ ≠ lFls := by decide
@[simp] theorem lds_lFls_ne_ldZ : lFls ≠ ldZ := by decide
@[simp] theorem lds_ldZ_ne_kFu : ldZ ≠ kFu := by decide
@[simp] theorem lds_kFu_ne_ldZ : kFu ≠ ldZ := by decide
@[simp] theorem lds_ldZ_ne_kD : ldZ ≠ kD := by decide
@[simp] theorem lds_kD_ne_ldZ : kD ≠ ldZ := by decide
@[simp] theorem lds_ldR_ne_ldA : ldR ≠ ldA := by decide
@[simp] theorem lds_ldR_ne_ldB : ldR ≠ ldB := by decide
@[simp] theorem lds_ldR_ne_ldUa : ldR ≠ ldUa := by decide
@[simp] theorem lds_ldR_ne_ldUb : ldR ≠ ldUb := by decide
@[simp] theorem lds_ldR_ne_ldX : ldR ≠ ldX := by decide
@[simp] theorem lds_ldR_ne_ldY : ldR ≠ ldY := by decide
@[simp] theorem lds_ldR_ne_ldZ : ldR ≠ ldZ := by decide
@[simp] theorem lds_ldR_ne_ldHa : ldR ≠ ldHa := by decide
@[simp] theorem lds_ldR_ne_ldHb : ldR ≠ ldHb := by decide
@[simp] theorem lds_ldR_ne_ldS : ldR ≠ ldS := by decide
@[simp] theorem lds_ldR_ne_ldP : ldR ≠ ldP := by decide
@[simp] theorem lds_ldR_ne_ldX2 : ldR ≠ ldX2 := by decide
@[simp] theorem lds_ldR_ne_ldY2 : ldR ≠ ldY2 := by decide
@[simp] theorem lds_ldR_ne_ldZ2 : ldR ≠ ldZ2 := by decide
@[simp] theorem lds_ldR_ne_lFl : ldR ≠ lFl := by decide
@[simp] theorem lds_lFl_ne_ldR : lFl ≠ ldR := by decide
@[simp] theorem lds_ldR_ne_lDh : ldR ≠ lDh := by decide
@[simp] theorem lds_lDh_ne_ldR : lDh ≠ ldR := by decide
@[simp] theorem lds_ldR_ne_lDt : ldR ≠ lDt := by decide
@[simp] theorem lds_lDt_ne_ldR : lDt ≠ ldR := by decide
@[simp] theorem lds_ldR_ne_lDg : ldR ≠ lDg := by decide
@[simp] theorem lds_lDg_ne_ldR : lDg ≠ ldR := by decide
@[simp] theorem lds_ldR_ne_lDi : ldR ≠ lDi := by decide
@[simp] theorem lds_lDi_ne_ldR : lDi ≠ ldR := by decide
@[simp] theorem lds_ldR_ne_lRp : ldR ≠ lRp := by decide
@[simp] theorem lds_lRp_ne_ldR : lRp ≠ ldR := by decide
@[simp] theorem lds_ldR_ne_lRn : ldR ≠ lRn := by decide
@[simp] theorem lds_lRn_ne_ldR : lRn ≠ ldR := by decide
@[simp] theorem lds_ldR_ne_lFle : ldR ≠ lFle := by decide
@[simp] theorem lds_lFle_ne_ldR : lFle ≠ ldR := by decide
@[simp] theorem lds_ldR_ne_lKb : ldR ≠ lKb := by decide
@[simp] theorem lds_lKb_ne_ldR : lKb ≠ ldR := by decide
@[simp] theorem lds_ldR_ne_lDir : ldR ≠ lDir := by decide
@[simp] theorem lds_lDir_ne_ldR : lDir ≠ ldR := by decide
@[simp] theorem lds_ldR_ne_lFln : ldR ≠ lFln := by decide
@[simp] theorem lds_lFln_ne_ldR : lFln ≠ ldR := by decide
@[simp] theorem lds_ldR_ne_lFll : ldR ≠ lFll := by decide
@[simp] theorem lds_lFll_ne_ldR : lFll ≠ ldR := by decide
@[simp] theorem lds_ldR_ne_lFls : ldR ≠ lFls := by decide
@[simp] theorem lds_lFls_ne_ldR : lFls ≠ ldR := by decide
@[simp] theorem lds_ldR_ne_kFu : ldR ≠ kFu := by decide
@[simp] theorem lds_kFu_ne_ldR : kFu ≠ ldR := by decide
@[simp] theorem lds_ldR_ne_kD : ldR ≠ kD := by decide
@[simp] theorem lds_kD_ne_ldR : kD ≠ ldR := by decide
@[simp] theorem lds_ldHa_ne_ldA : ldHa ≠ ldA := by decide
@[simp] theorem lds_ldHa_ne_ldB : ldHa ≠ ldB := by decide
@[simp] theorem lds_ldHa_ne_ldUa : ldHa ≠ ldUa := by decide
@[simp] theorem lds_ldHa_ne_ldUb : ldHa ≠ ldUb := by decide
@[simp] theorem lds_ldHa_ne_ldX : ldHa ≠ ldX := by decide
@[simp] theorem lds_ldHa_ne_ldY : ldHa ≠ ldY := by decide
@[simp] theorem lds_ldHa_ne_ldZ : ldHa ≠ ldZ := by decide
@[simp] theorem lds_ldHa_ne_ldR : ldHa ≠ ldR := by decide
@[simp] theorem lds_ldHa_ne_ldHb : ldHa ≠ ldHb := by decide
@[simp] theorem lds_ldHa_ne_ldS : ldHa ≠ ldS := by decide
@[simp] theorem lds_ldHa_ne_ldP : ldHa ≠ ldP := by decide
@[simp] theorem lds_ldHa_ne_ldX2 : ldHa ≠ ldX2 := by decide
@[simp] theorem lds_ldHa_ne_ldY2 : ldHa ≠ ldY2 := by decide
@[simp] theorem lds_ldHa_ne_ldZ2 : ldHa ≠ ldZ2 := by decide
@[simp] theorem lds_ldHa_ne_lFl : ldHa ≠ lFl := by decide
@[simp] theorem lds_lFl_ne_ldHa : lFl ≠ ldHa := by decide
@[simp] theorem lds_ldHa_ne_lDh : ldHa ≠ lDh := by decide
@[simp] theorem lds_lDh_ne_ldHa : lDh ≠ ldHa := by decide
@[simp] theorem lds_ldHa_ne_lDt : ldHa ≠ lDt := by decide
@[simp] theorem lds_lDt_ne_ldHa : lDt ≠ ldHa := by decide
@[simp] theorem lds_ldHa_ne_lDg : ldHa ≠ lDg := by decide
@[simp] theorem lds_lDg_ne_ldHa : lDg ≠ ldHa := by decide
@[simp] theorem lds_ldHa_ne_lDi : ldHa ≠ lDi := by decide
@[simp] theorem lds_lDi_ne_ldHa : lDi ≠ ldHa := by decide
@[simp] theorem lds_ldHa_ne_lRp : ldHa ≠ lRp := by decide
@[simp] theorem lds_lRp_ne_ldHa : lRp ≠ ldHa := by decide
@[simp] theorem lds_ldHa_ne_lRn : ldHa ≠ lRn := by decide
@[simp] theorem lds_lRn_ne_ldHa : lRn ≠ ldHa := by decide
@[simp] theorem lds_ldHa_ne_lFle : ldHa ≠ lFle := by decide
@[simp] theorem lds_lFle_ne_ldHa : lFle ≠ ldHa := by decide
@[simp] theorem lds_ldHa_ne_lKb : ldHa ≠ lKb := by decide
@[simp] theorem lds_lKb_ne_ldHa : lKb ≠ ldHa := by decide
@[simp] theorem lds_ldHa_ne_lDir : ldHa ≠ lDir := by decide
@[simp] theorem lds_lDir_ne_ldHa : lDir ≠ ldHa := by decide
@[simp] theorem lds_ldHa_ne_lFln : ldHa ≠ lFln := by decide
@[simp] theorem lds_lFln_ne_ldHa : lFln ≠ ldHa := by decide
@[simp] theorem lds_ldHa_ne_lFll : ldHa ≠ lFll := by decide
@[simp] theorem lds_lFll_ne_ldHa : lFll ≠ ldHa := by decide
@[simp] theorem lds_ldHa_ne_lFls : ldHa ≠ lFls := by decide
@[simp] theorem lds_lFls_ne_ldHa : lFls ≠ ldHa := by decide
@[simp] theorem lds_ldHa_ne_kFu : ldHa ≠ kFu := by decide
@[simp] theorem lds_kFu_ne_ldHa : kFu ≠ ldHa := by decide
@[simp] theorem lds_ldHa_ne_kD : ldHa ≠ kD := by decide
@[simp] theorem lds_kD_ne_ldHa : kD ≠ ldHa := by decide
@[simp] theorem lds_ldHb_ne_ldA : ldHb ≠ ldA := by decide
@[simp] theorem lds_ldHb_ne_ldB : ldHb ≠ ldB := by decide
@[simp] theorem lds_ldHb_ne_ldUa : ldHb ≠ ldUa := by decide
@[simp] theorem lds_ldHb_ne_ldUb : ldHb ≠ ldUb := by decide
@[simp] theorem lds_ldHb_ne_ldX : ldHb ≠ ldX := by decide
@[simp] theorem lds_ldHb_ne_ldY : ldHb ≠ ldY := by decide
@[simp] theorem lds_ldHb_ne_ldZ : ldHb ≠ ldZ := by decide
@[simp] theorem lds_ldHb_ne_ldR : ldHb ≠ ldR := by decide
@[simp] theorem lds_ldHb_ne_ldHa : ldHb ≠ ldHa := by decide
@[simp] theorem lds_ldHb_ne_ldS : ldHb ≠ ldS := by decide
@[simp] theorem lds_ldHb_ne_ldP : ldHb ≠ ldP := by decide
@[simp] theorem lds_ldHb_ne_ldX2 : ldHb ≠ ldX2 := by decide
@[simp] theorem lds_ldHb_ne_ldY2 : ldHb ≠ ldY2 := by decide
@[simp] theorem lds_ldHb_ne_ldZ2 : ldHb ≠ ldZ2 := by decide
@[simp] theorem lds_ldHb_ne_lFl : ldHb ≠ lFl := by decide
@[simp] theorem lds_lFl_ne_ldHb : lFl ≠ ldHb := by decide
@[simp] theorem lds_ldHb_ne_lDh : ldHb ≠ lDh := by decide
@[simp] theorem lds_lDh_ne_ldHb : lDh ≠ ldHb := by decide
@[simp] theorem lds_ldHb_ne_lDt : ldHb ≠ lDt := by decide
@[simp] theorem lds_lDt_ne_ldHb : lDt ≠ ldHb := by decide
@[simp] theorem lds_ldHb_ne_lDg : ldHb ≠ lDg := by decide
@[simp] theorem lds_lDg_ne_ldHb : lDg ≠ ldHb := by decide
@[simp] theorem lds_ldHb_ne_lDi : ldHb ≠ lDi := by decide
@[simp] theorem lds_lDi_ne_ldHb : lDi ≠ ldHb := by decide
@[simp] theorem lds_ldHb_ne_lRp : ldHb ≠ lRp := by decide
@[simp] theorem lds_lRp_ne_ldHb : lRp ≠ ldHb := by decide
@[simp] theorem lds_ldHb_ne_lRn : ldHb ≠ lRn := by decide
@[simp] theorem lds_lRn_ne_ldHb : lRn ≠ ldHb := by decide
@[simp] theorem lds_ldHb_ne_lFle : ldHb ≠ lFle := by decide
@[simp] theorem lds_lFle_ne_ldHb : lFle ≠ ldHb := by decide
@[simp] theorem lds_ldHb_ne_lKb : ldHb ≠ lKb := by decide
@[simp] theorem lds_lKb_ne_ldHb : lKb ≠ ldHb := by decide
@[simp] theorem lds_ldHb_ne_lDir : ldHb ≠ lDir := by decide
@[simp] theorem lds_lDir_ne_ldHb : lDir ≠ ldHb := by decide
@[simp] theorem lds_ldHb_ne_lFln : ldHb ≠ lFln := by decide
@[simp] theorem lds_lFln_ne_ldHb : lFln ≠ ldHb := by decide
@[simp] theorem lds_ldHb_ne_lFll : ldHb ≠ lFll := by decide
@[simp] theorem lds_lFll_ne_ldHb : lFll ≠ ldHb := by decide
@[simp] theorem lds_ldHb_ne_lFls : ldHb ≠ lFls := by decide
@[simp] theorem lds_lFls_ne_ldHb : lFls ≠ ldHb := by decide
@[simp] theorem lds_ldHb_ne_kFu : ldHb ≠ kFu := by decide
@[simp] theorem lds_kFu_ne_ldHb : kFu ≠ ldHb := by decide
@[simp] theorem lds_ldHb_ne_kD : ldHb ≠ kD := by decide
@[simp] theorem lds_kD_ne_ldHb : kD ≠ ldHb := by decide
@[simp] theorem lds_ldS_ne_ldA : ldS ≠ ldA := by decide
@[simp] theorem lds_ldS_ne_ldB : ldS ≠ ldB := by decide
@[simp] theorem lds_ldS_ne_ldUa : ldS ≠ ldUa := by decide
@[simp] theorem lds_ldS_ne_ldUb : ldS ≠ ldUb := by decide
@[simp] theorem lds_ldS_ne_ldX : ldS ≠ ldX := by decide
@[simp] theorem lds_ldS_ne_ldY : ldS ≠ ldY := by decide
@[simp] theorem lds_ldS_ne_ldZ : ldS ≠ ldZ := by decide
@[simp] theorem lds_ldS_ne_ldR : ldS ≠ ldR := by decide
@[simp] theorem lds_ldS_ne_ldHa : ldS ≠ ldHa := by decide
@[simp] theorem lds_ldS_ne_ldHb : ldS ≠ ldHb := by decide
@[simp] theorem lds_ldS_ne_ldP : ldS ≠ ldP := by decide
@[simp] theorem lds_ldS_ne_ldX2 : ldS ≠ ldX2 := by decide
@[simp] theorem lds_ldS_ne_ldY2 : ldS ≠ ldY2 := by decide
@[simp] theorem lds_ldS_ne_ldZ2 : ldS ≠ ldZ2 := by decide
@[simp] theorem lds_ldS_ne_lFl : ldS ≠ lFl := by decide
@[simp] theorem lds_lFl_ne_ldS : lFl ≠ ldS := by decide
@[simp] theorem lds_ldS_ne_lDh : ldS ≠ lDh := by decide
@[simp] theorem lds_lDh_ne_ldS : lDh ≠ ldS := by decide
@[simp] theorem lds_ldS_ne_lDt : ldS ≠ lDt := by decide
@[simp] theorem lds_lDt_ne_ldS : lDt ≠ ldS := by decide
@[simp] theorem lds_ldS_ne_lDg : ldS ≠ lDg := by decide
@[simp] theorem lds_lDg_ne_ldS : lDg ≠ ldS := by decide
@[simp] theorem lds_ldS_ne_lDi : ldS ≠ lDi := by decide
@[simp] theorem lds_lDi_ne_ldS : lDi ≠ ldS := by decide
@[simp] theorem lds_ldS_ne_lRp : ldS ≠ lRp := by decide
@[simp] theorem lds_lRp_ne_ldS : lRp ≠ ldS := by decide
@[simp] theorem lds_ldS_ne_lRn : ldS ≠ lRn := by decide
@[simp] theorem lds_lRn_ne_ldS : lRn ≠ ldS := by decide
@[simp] theorem lds_ldS_ne_lFle : ldS ≠ lFle := by decide
@[simp] theorem lds_lFle_ne_ldS : lFle ≠ ldS := by decide
@[simp] theorem lds_ldS_ne_lKb : ldS ≠ lKb := by decide
@[simp] theorem lds_lKb_ne_ldS : lKb ≠ ldS := by decide
@[simp] theorem lds_ldS_ne_lDir : ldS ≠ lDir := by decide
@[simp] theorem lds_lDir_ne_ldS : lDir ≠ ldS := by decide
@[simp] theorem lds_ldS_ne_lFln : ldS ≠ lFln := by decide
@[simp] theorem lds_lFln_ne_ldS : lFln ≠ ldS := by decide
@[simp] theorem lds_ldS_ne_lFll : ldS ≠ lFll := by decide
@[simp] theorem lds_lFll_ne_ldS : lFll ≠ ldS := by decide
@[simp] theorem lds_ldS_ne_lFls : ldS ≠ lFls := by decide
@[simp] theorem lds_lFls_ne_ldS : lFls ≠ ldS := by decide
@[simp] theorem lds_ldS_ne_kFu : ldS ≠ kFu := by decide
@[simp] theorem lds_kFu_ne_ldS : kFu ≠ ldS := by decide
@[simp] theorem lds_ldS_ne_kD : ldS ≠ kD := by decide
@[simp] theorem lds_kD_ne_ldS : kD ≠ ldS := by decide
@[simp] theorem lds_ldP_ne_ldA : ldP ≠ ldA := by decide
@[simp] theorem lds_ldP_ne_ldB : ldP ≠ ldB := by decide
@[simp] theorem lds_ldP_ne_ldUa : ldP ≠ ldUa := by decide
@[simp] theorem lds_ldP_ne_ldUb : ldP ≠ ldUb := by decide
@[simp] theorem lds_ldP_ne_ldX : ldP ≠ ldX := by decide
@[simp] theorem lds_ldP_ne_ldY : ldP ≠ ldY := by decide
@[simp] theorem lds_ldP_ne_ldZ : ldP ≠ ldZ := by decide
@[simp] theorem lds_ldP_ne_ldR : ldP ≠ ldR := by decide
@[simp] theorem lds_ldP_ne_ldHa : ldP ≠ ldHa := by decide
@[simp] theorem lds_ldP_ne_ldHb : ldP ≠ ldHb := by decide
@[simp] theorem lds_ldP_ne_ldS : ldP ≠ ldS := by decide
@[simp] theorem lds_ldP_ne_ldX2 : ldP ≠ ldX2 := by decide
@[simp] theorem lds_ldP_ne_ldY2 : ldP ≠ ldY2 := by decide
@[simp] theorem lds_ldP_ne_ldZ2 : ldP ≠ ldZ2 := by decide
@[simp] theorem lds_ldP_ne_lFl : ldP ≠ lFl := by decide
@[simp] theorem lds_lFl_ne_ldP : lFl ≠ ldP := by decide
@[simp] theorem lds_ldP_ne_lDh : ldP ≠ lDh := by decide
@[simp] theorem lds_lDh_ne_ldP : lDh ≠ ldP := by decide
@[simp] theorem lds_ldP_ne_lDt : ldP ≠ lDt := by decide
@[simp] theorem lds_lDt_ne_ldP : lDt ≠ ldP := by decide
@[simp] theorem lds_ldP_ne_lDg : ldP ≠ lDg := by decide
@[simp] theorem lds_lDg_ne_ldP : lDg ≠ ldP := by decide
@[simp] theorem lds_ldP_ne_lDi : ldP ≠ lDi := by decide
@[simp] theorem lds_lDi_ne_ldP : lDi ≠ ldP := by decide
@[simp] theorem lds_ldP_ne_lRp : ldP ≠ lRp := by decide
@[simp] theorem lds_lRp_ne_ldP : lRp ≠ ldP := by decide
@[simp] theorem lds_ldP_ne_lRn : ldP ≠ lRn := by decide
@[simp] theorem lds_lRn_ne_ldP : lRn ≠ ldP := by decide
@[simp] theorem lds_ldP_ne_lFle : ldP ≠ lFle := by decide
@[simp] theorem lds_lFle_ne_ldP : lFle ≠ ldP := by decide
@[simp] theorem lds_ldP_ne_lKb : ldP ≠ lKb := by decide
@[simp] theorem lds_lKb_ne_ldP : lKb ≠ ldP := by decide
@[simp] theorem lds_ldP_ne_lDir : ldP ≠ lDir := by decide
@[simp] theorem lds_lDir_ne_ldP : lDir ≠ ldP := by decide
@[simp] theorem lds_ldP_ne_lFln : ldP ≠ lFln := by decide
@[simp] theorem lds_lFln_ne_ldP : lFln ≠ ldP := by decide
@[simp] theorem lds_ldP_ne_lFll : ldP ≠ lFll := by decide
@[simp] theorem lds_lFll_ne_ldP : lFll ≠ ldP := by decide
@[simp] theorem lds_ldP_ne_lFls : ldP ≠ lFls := by decide
@[simp] theorem lds_lFls_ne_ldP : lFls ≠ ldP := by decide
@[simp] theorem lds_ldP_ne_kFu : ldP ≠ kFu := by decide
@[simp] theorem lds_kFu_ne_ldP : kFu ≠ ldP := by decide
@[simp] theorem lds_ldP_ne_kD : ldP ≠ kD := by decide
@[simp] theorem lds_kD_ne_ldP : kD ≠ ldP := by decide
@[simp] theorem lds_ldX2_ne_ldA : ldX2 ≠ ldA := by decide
@[simp] theorem lds_ldX2_ne_ldB : ldX2 ≠ ldB := by decide
@[simp] theorem lds_ldX2_ne_ldUa : ldX2 ≠ ldUa := by decide
@[simp] theorem lds_ldX2_ne_ldUb : ldX2 ≠ ldUb := by decide
@[simp] theorem lds_ldX2_ne_ldX : ldX2 ≠ ldX := by decide
@[simp] theorem lds_ldX2_ne_ldY : ldX2 ≠ ldY := by decide
@[simp] theorem lds_ldX2_ne_ldZ : ldX2 ≠ ldZ := by decide
@[simp] theorem lds_ldX2_ne_ldR : ldX2 ≠ ldR := by decide
@[simp] theorem lds_ldX2_ne_ldHa : ldX2 ≠ ldHa := by decide
@[simp] theorem lds_ldX2_ne_ldHb : ldX2 ≠ ldHb := by decide
@[simp] theorem lds_ldX2_ne_ldS : ldX2 ≠ ldS := by decide
@[simp] theorem lds_ldX2_ne_ldP : ldX2 ≠ ldP := by decide
@[simp] theorem lds_ldX2_ne_ldY2 : ldX2 ≠ ldY2 := by decide
@[simp] theorem lds_ldX2_ne_ldZ2 : ldX2 ≠ ldZ2 := by decide
@[simp] theorem lds_ldX2_ne_lFl : ldX2 ≠ lFl := by decide
@[simp] theorem lds_lFl_ne_ldX2 : lFl ≠ ldX2 := by decide
@[simp] theorem lds_ldX2_ne_lDh : ldX2 ≠ lDh := by decide
@[simp] theorem lds_lDh_ne_ldX2 : lDh ≠ ldX2 := by decide
@[simp] theorem lds_ldX2_ne_lDt : ldX2 ≠ lDt := by decide
@[simp] theorem lds_lDt_ne_ldX2 : lDt ≠ ldX2 := by decide
@[simp] theorem lds_ldX2_ne_lDg : ldX2 ≠ lDg := by decide
@[simp] theorem lds_lDg_ne_ldX2 : lDg ≠ ldX2 := by decide
@[simp] theorem lds_ldX2_ne_lDi : ldX2 ≠ lDi := by decide
@[simp] theorem lds_lDi_ne_ldX2 : lDi ≠ ldX2 := by decide
@[simp] theorem lds_ldX2_ne_lRp : ldX2 ≠ lRp := by decide
@[simp] theorem lds_lRp_ne_ldX2 : lRp ≠ ldX2 := by decide
@[simp] theorem lds_ldX2_ne_lRn : ldX2 ≠ lRn := by decide
@[simp] theorem lds_lRn_ne_ldX2 : lRn ≠ ldX2 := by decide
@[simp] theorem lds_ldX2_ne_lFle : ldX2 ≠ lFle := by decide
@[simp] theorem lds_lFle_ne_ldX2 : lFle ≠ ldX2 := by decide
@[simp] theorem lds_ldX2_ne_lKb : ldX2 ≠ lKb := by decide
@[simp] theorem lds_lKb_ne_ldX2 : lKb ≠ ldX2 := by decide
@[simp] theorem lds_ldX2_ne_lDir : ldX2 ≠ lDir := by decide
@[simp] theorem lds_lDir_ne_ldX2 : lDir ≠ ldX2 := by decide
@[simp] theorem lds_ldX2_ne_lFln : ldX2 ≠ lFln := by decide
@[simp] theorem lds_lFln_ne_ldX2 : lFln ≠ ldX2 := by decide
@[simp] theorem lds_ldX2_ne_lFll : ldX2 ≠ lFll := by decide
@[simp] theorem lds_lFll_ne_ldX2 : lFll ≠ ldX2 := by decide
@[simp] theorem lds_ldX2_ne_lFls : ldX2 ≠ lFls := by decide
@[simp] theorem lds_lFls_ne_ldX2 : lFls ≠ ldX2 := by decide
@[simp] theorem lds_ldX2_ne_kFu : ldX2 ≠ kFu := by decide
@[simp] theorem lds_kFu_ne_ldX2 : kFu ≠ ldX2 := by decide
@[simp] theorem lds_ldX2_ne_kD : ldX2 ≠ kD := by decide
@[simp] theorem lds_kD_ne_ldX2 : kD ≠ ldX2 := by decide
@[simp] theorem lds_ldY2_ne_ldA : ldY2 ≠ ldA := by decide
@[simp] theorem lds_ldY2_ne_ldB : ldY2 ≠ ldB := by decide
@[simp] theorem lds_ldY2_ne_ldUa : ldY2 ≠ ldUa := by decide
@[simp] theorem lds_ldY2_ne_ldUb : ldY2 ≠ ldUb := by decide
@[simp] theorem lds_ldY2_ne_ldX : ldY2 ≠ ldX := by decide
@[simp] theorem lds_ldY2_ne_ldY : ldY2 ≠ ldY := by decide
@[simp] theorem lds_ldY2_ne_ldZ : ldY2 ≠ ldZ := by decide
@[simp] theorem lds_ldY2_ne_ldR : ldY2 ≠ ldR := by decide
@[simp] theorem lds_ldY2_ne_ldHa : ldY2 ≠ ldHa := by decide
@[simp] theorem lds_ldY2_ne_ldHb : ldY2 ≠ ldHb := by decide
@[simp] theorem lds_ldY2_ne_ldS : ldY2 ≠ ldS := by decide
@[simp] theorem lds_ldY2_ne_ldP : ldY2 ≠ ldP := by decide
@[simp] theorem lds_ldY2_ne_ldX2 : ldY2 ≠ ldX2 := by decide
@[simp] theorem lds_ldY2_ne_ldZ2 : ldY2 ≠ ldZ2 := by decide
@[simp] theorem lds_ldY2_ne_lFl : ldY2 ≠ lFl := by decide
@[simp] theorem lds_lFl_ne_ldY2 : lFl ≠ ldY2 := by decide
@[simp] theorem lds_ldY2_ne_lDh : ldY2 ≠ lDh := by decide
@[simp] theorem lds_lDh_ne_ldY2 : lDh ≠ ldY2 := by decide
@[simp] theorem lds_ldY2_ne_lDt : ldY2 ≠ lDt := by decide
@[simp] theorem lds_lDt_ne_ldY2 : lDt ≠ ldY2 := by decide
@[simp] theorem lds_ldY2_ne_lDg : ldY2 ≠ lDg := by decide
@[simp] theorem lds_lDg_ne_ldY2 : lDg ≠ ldY2 := by decide
@[simp] theorem lds_ldY2_ne_lDi : ldY2 ≠ lDi := by decide
@[simp] theorem lds_lDi_ne_ldY2 : lDi ≠ ldY2 := by decide
@[simp] theorem lds_ldY2_ne_lRp : ldY2 ≠ lRp := by decide
@[simp] theorem lds_lRp_ne_ldY2 : lRp ≠ ldY2 := by decide
@[simp] theorem lds_ldY2_ne_lRn : ldY2 ≠ lRn := by decide
@[simp] theorem lds_lRn_ne_ldY2 : lRn ≠ ldY2 := by decide
@[simp] theorem lds_ldY2_ne_lFle : ldY2 ≠ lFle := by decide
@[simp] theorem lds_lFle_ne_ldY2 : lFle ≠ ldY2 := by decide
@[simp] theorem lds_ldY2_ne_lKb : ldY2 ≠ lKb := by decide
@[simp] theorem lds_lKb_ne_ldY2 : lKb ≠ ldY2 := by decide
@[simp] theorem lds_ldY2_ne_lDir : ldY2 ≠ lDir := by decide
@[simp] theorem lds_lDir_ne_ldY2 : lDir ≠ ldY2 := by decide
@[simp] theorem lds_ldY2_ne_lFln : ldY2 ≠ lFln := by decide
@[simp] theorem lds_lFln_ne_ldY2 : lFln ≠ ldY2 := by decide
@[simp] theorem lds_ldY2_ne_lFll : ldY2 ≠ lFll := by decide
@[simp] theorem lds_lFll_ne_ldY2 : lFll ≠ ldY2 := by decide
@[simp] theorem lds_ldY2_ne_lFls : ldY2 ≠ lFls := by decide
@[simp] theorem lds_lFls_ne_ldY2 : lFls ≠ ldY2 := by decide
@[simp] theorem lds_ldY2_ne_kFu : ldY2 ≠ kFu := by decide
@[simp] theorem lds_kFu_ne_ldY2 : kFu ≠ ldY2 := by decide
@[simp] theorem lds_ldY2_ne_kD : ldY2 ≠ kD := by decide
@[simp] theorem lds_kD_ne_ldY2 : kD ≠ ldY2 := by decide
@[simp] theorem lds_ldZ2_ne_ldA : ldZ2 ≠ ldA := by decide
@[simp] theorem lds_ldZ2_ne_ldB : ldZ2 ≠ ldB := by decide
@[simp] theorem lds_ldZ2_ne_ldUa : ldZ2 ≠ ldUa := by decide
@[simp] theorem lds_ldZ2_ne_ldUb : ldZ2 ≠ ldUb := by decide
@[simp] theorem lds_ldZ2_ne_ldX : ldZ2 ≠ ldX := by decide
@[simp] theorem lds_ldZ2_ne_ldY : ldZ2 ≠ ldY := by decide
@[simp] theorem lds_ldZ2_ne_ldZ : ldZ2 ≠ ldZ := by decide
@[simp] theorem lds_ldZ2_ne_ldR : ldZ2 ≠ ldR := by decide
@[simp] theorem lds_ldZ2_ne_ldHa : ldZ2 ≠ ldHa := by decide
@[simp] theorem lds_ldZ2_ne_ldHb : ldZ2 ≠ ldHb := by decide
@[simp] theorem lds_ldZ2_ne_ldS : ldZ2 ≠ ldS := by decide
@[simp] theorem lds_ldZ2_ne_ldP : ldZ2 ≠ ldP := by decide
@[simp] theorem lds_ldZ2_ne_ldX2 : ldZ2 ≠ ldX2 := by decide
@[simp] theorem lds_ldZ2_ne_ldY2 : ldZ2 ≠ ldY2 := by decide
@[simp] theorem lds_ldZ2_ne_lFl : ldZ2 ≠ lFl := by decide
@[simp] theorem lds_lFl_ne_ldZ2 : lFl ≠ ldZ2 := by decide
@[simp] theorem lds_ldZ2_ne_lDh : ldZ2 ≠ lDh := by decide
@[simp] theorem lds_lDh_ne_ldZ2 : lDh ≠ ldZ2 := by decide
@[simp] theorem lds_ldZ2_ne_lDt : ldZ2 ≠ lDt := by decide
@[simp] theorem lds_lDt_ne_ldZ2 : lDt ≠ ldZ2 := by decide
@[simp] theorem lds_ldZ2_ne_lDg : ldZ2 ≠ lDg := by decide
@[simp] theorem lds_lDg_ne_ldZ2 : lDg ≠ ldZ2 := by decide
@[simp] theorem lds_ldZ2_ne_lDi : ldZ2 ≠ lDi := by decide
@[simp] theorem lds_lDi_ne_ldZ2 : lDi ≠ ldZ2 := by decide
@[simp] theorem lds_ldZ2_ne_lRp : ldZ2 ≠ lRp := by decide
@[simp] theorem lds_lRp_ne_ldZ2 : lRp ≠ ldZ2 := by decide
@[simp] theorem lds_ldZ2_ne_lRn : ldZ2 ≠ lRn := by decide
@[simp] theorem lds_lRn_ne_ldZ2 : lRn ≠ ldZ2 := by decide
@[simp] theorem lds_ldZ2_ne_lFle : ldZ2 ≠ lFle := by decide
@[simp] theorem lds_lFle_ne_ldZ2 : lFle ≠ ldZ2 := by decide
@[simp] theorem lds_ldZ2_ne_lKb : ldZ2 ≠ lKb := by decide
@[simp] theorem lds_lKb_ne_ldZ2 : lKb ≠ ldZ2 := by decide
@[simp] theorem lds_ldZ2_ne_lDir : ldZ2 ≠ lDir := by decide
@[simp] theorem lds_lDir_ne_ldZ2 : lDir ≠ ldZ2 := by decide
@[simp] theorem lds_ldZ2_ne_lFln : ldZ2 ≠ lFln := by decide
@[simp] theorem lds_lFln_ne_ldZ2 : lFln ≠ ldZ2 := by decide
@[simp] theorem lds_ldZ2_ne_lFll : ldZ2 ≠ lFll := by decide
@[simp] theorem lds_lFll_ne_ldZ2 : lFll ≠ ldZ2 := by decide
@[simp] theorem lds_ldZ2_ne_lFls : ldZ2 ≠ lFls := by decide
@[simp] theorem lds_lFls_ne_ldZ2 : lFls ≠ ldZ2 := by decide
@[simp] theorem lds_ldZ2_ne_kFu : ldZ2 ≠ kFu := by decide
@[simp] theorem lds_kFu_ne_ldZ2 : kFu ≠ ldZ2 := by decide
@[simp] theorem lds_ldZ2_ne_kD : ldZ2 ≠ kD := by decide
@[simp] theorem lds_kD_ne_ldZ2 : kD ≠ ldZ2 := by decide

def hltE (x y : ExpHOL 64) : ExpHOL 64 :=
  .op .and [.cmp .notEqual y (.const 0), .op .and [.cmp .notEqual x (.const 1),
    .op .or [.cmp .equal x (.const 0), .op .or [.cmp .equal y (.const 1), .cmp .lower x y]]]]

def hsrE (x y : ExpHOL 64) : ExpHOL 64 :=
  .op .and [.cmp .notEqual x (.const 0), .op .and [.cmp .notEqual x (.const 1), .cmp .equal x y]]

theorem ofNat_k2_ne (k : Nat) (c : Nat) (hc : c < 2) (hk : k + 2 < 2 ^ 63) :
    BitVec.ofNat 64 (k + 2) ≠ BitVec.ofNat 64 c := by
  intro e; have := congrArg BitVec.toNat e
  simp only [BitVec.toNat_ofNat] at this
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; omega

theorem sev_hltE (Γ : Env) (x y : ExpHOL 64) (h1 h2 : ConLeche.ReducibilityHint)
    (hx : sev Γ x = some (BitVec.ofNat 64 (hintN h1))) (hy : sev Γ y = some (BitVec.ofNat 64 (hintN h2)))
    (b1 : hintN h1 < 2 ^ 63) (b2 : hintN h2 < 2 ^ 63) :
    sev Γ (hltE x y) = some (boolW (h1.lt h2)) := by
  simp only [hltE, sev, hx, hy]
  cases h1 <;> cases h2 <;> simp [hintN, ConLeche.ReducibilityHint.lt, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, boolW] at b1 b2 ⊢
  all_goals (simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat]; split_ifs <;> first | rfl | omega | decide)

theorem sev_hsrE (Γ : Env) (x y : ExpHOL 64) (h1 h2 : ConLeche.ReducibilityHint)
    (hx : sev Γ x = some (BitVec.ofNat 64 (hintN h1))) (hy : sev Γ y = some (BitVec.ofNat 64 (hintN h2)))
    (b1 : hintN h1 < 2 ^ 63) (b2 : hintN h2 < 2 ^ 63) :
    sev Γ (hsrE x y) = some (boolW (h1.sameRegular h2)) := by
  simp only [hsrE, sev, hx, hy]
  cases h1 <;> cases h2 <;> simp [hintN, ConLeche.ReducibilityHint.sameRegular, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, boolW] at b1 b2 ⊢
  all_goals (simp only [← BitVec.toNat_inj, BitVec.toNat_ofNat]; split_ifs <;> first | rfl | omega | decide)


theorem boolW_and (x y : Bool) : boolW x &&& boolW y = boolW (x && y) := by cases x <;> cases y <;> decide

theorem sev_and_hsr (Γ : Env) (x y z : ExpHOL 64) (h1 h2 : ConLeche.ReducibilityHint) (c : Bool)
    (hx : sev Γ x = some (BitVec.ofNat 64 (hintN h1))) (hy : sev Γ y = some (BitVec.ofNat 64 (hintN h2)))
    (hz : sev Γ z = some (boolW c)) (b1 : hintN h1 < 2 ^ 63) (b2 : hintN h2 < 2 ^ 63) :
    sev Γ (.op .and [hsrE x y, z]) = some (boolW (h1.sameRegular h2 && c)) := by
  simp only [sev, sev_hsrE Γ x y h1 h2 hx hy b1 b2, hz]
  simp [boolW_and]

def ldParams : List MlS := [kFu, kD, ldA, ldB]
def ldLocals : List MlS := [ldUa, ldUb, ldX, ldY, ldZ, ldR, ldHa, ldHb, ldS, ldP, ldX2, ldY2, ldZ2]
def ldBody : ProgHOL 64 := prologue ldLocals (.seq (.call (some (some (.local, ldUa), none)) fUk [(vv ldA)]) (.seq (.call (some (some (.local, ldUb), none)) fUk [(vv ldB)]) (.ite (vv ldUa) (.ite (vv ldUb) (.seq (.call (some (some (.local, ldHa), none)) fHn [(vv ldA)]) (.seq (.call (some (some (.local, ldHb), none)) fHn [(vv ldB)]) (.ite (hltE (vv ldHb) (vv ldHa)) (.seq (.call (some (some (.local, ldX), none)) UD.fUnfold [(vv ldA)]) (.ite (.cmp .equal (vv ldX) (.const 0)) (.return (.const 0)) (.seq (.call (some (some (.local, ldY), none)) fWC [(vv kFu), (.const 1), (vv kD), (.op .sub [(vv ldX), (.const 1)])]) (.seq (.call (some (some (.local, ldR), none)) fDq [(vv kFu), (vv kD), (vv ldY), (vv ldB)]) (.return (vv ldR)))))) (.ite (hltE (vv ldHa) (vv ldHb)) (.seq (.call (some (some (.local, ldX), none)) UD.fUnfold [(vv ldB)]) (.ite (.cmp .equal (vv ldX) (.const 0)) (.return (.const 0)) (.seq (.call (some (some (.local, ldY), none)) fWC [(vv kFu), (.const 1), (vv kD), (.op .sub [(vv ldX), (.const 1)])]) (.seq (.call (some (some (.local, ldR), none)) fDq [(vv kFu), (vv kD), (vv ldA), (vv ldY)]) (.return (vv ldR)))))) (.seq (.call (some (some (.local, ldS), none)) fSq [(vv ldA), (vv ldB)]) (.ite (.op .and [(hsrE (vv ldHa) (vv ldHb)), (vv ldS)]) (.seq (.call (some (some (.local, ldP), none)) fDsp [(vv kFu), (vv kD), (vv ldA), (vv ldB)]) (.ite (vv ldP) (.return (.const 1)) (.seq (.call (some (some (.local, ldX2), none)) UD.fUnfold [(vv ldA)]) (.seq (.call (some (some (.local, ldY2), none)) UD.fUnfold [(vv ldB)]) (.ite (.cmp .equal (vv ldX2) (.const 0)) (.return (.const 0)) (.ite (.cmp .equal (vv ldY2) (.const 0)) (.return (.const 0)) (.seq (.call (some (some (.local, ldZ), none)) fWC [(vv kFu), (.const 1), (vv kD), (.op .sub [(vv ldX2), (.const 1)])]) (.seq (.call (some (some (.local, ldZ2), none)) fWC [(vv kFu), (.const 1), (vv kD), (.op .sub [(vv ldY2), (.const 1)])]) (.seq (.call (some (some (.local, ldR), none)) fDq [(vv kFu), (vv kD), (vv ldZ), (vv ldZ2)]) (.return (vv ldR))))))))))) (.seq (.call (some (some (.local, ldX2), none)) UD.fUnfold [(vv ldA)]) (.seq (.call (some (some (.local, ldY2), none)) UD.fUnfold [(vv ldB)]) (.ite (.cmp .equal (vv ldX2) (.const 0)) (.return (.const 0)) (.ite (.cmp .equal (vv ldY2) (.const 0)) (.return (.const 0)) (.seq (.call (some (some (.local, ldZ), none)) fWC [(vv kFu), (.const 1), (vv kD), (.op .sub [(vv ldX2), (.const 1)])]) (.seq (.call (some (some (.local, ldZ2), none)) fWC [(vv kFu), (.const 1), (vv kD), (.op .sub [(vv ldY2), (.const 1)])]) (.seq (.call (some (some (.local, ldR), none)) fDq [(vv kFu), (vv kD), (vv ldZ), (vv ldZ2)]) (.return (vv ldR))))))))))))))) (.seq (.call (some (some (.local, ldZ), none)) fTu [(vv kFu), (vv kD), (vv ldB)]) (.ite (.cmp .equal (vv ldZ) (.const 0)) (.seq (.call (some (some (.local, ldX), none)) UD.fUnfold [(vv ldA)]) (.ite (.cmp .equal (vv ldX) (.const 0)) (.return (.const 0)) (.seq (.call (some (some (.local, ldY), none)) fWC [(vv kFu), (.const 1), (vv kD), (.op .sub [(vv ldX), (.const 1)])]) (.seq (.call (some (some (.local, ldR), none)) fDq [(vv kFu), (vv kD), (vv ldY), (vv ldB)]) (.return (vv ldR)))))) (.seq (.call (some (some (.local, ldR), none)) fDq [(vv kFu), (vv kD), (vv ldA), (.op .sub [(vv ldZ), (.const 1)])]) (.return (vv ldR)))))) (.ite (vv ldUb) (.seq (.call (some (some (.local, ldZ), none)) fTu [(vv kFu), (vv kD), (vv ldA)]) (.ite (.cmp .equal (vv ldZ) (.const 0)) (.seq (.call (some (some (.local, ldX), none)) UD.fUnfold [(vv ldB)]) (.ite (.cmp .equal (vv ldX) (.const 0)) (.return (.const 0)) (.seq (.call (some (some (.local, ldY), none)) fWC [(vv kFu), (.const 1), (vv kD), (.op .sub [(vv ldX), (.const 1)])]) (.seq (.call (some (some (.local, ldR), none)) fDq [(vv kFu), (vv kD), (vv ldA), (vv ldY)]) (.return (vv ldR)))))) (.seq (.call (some (some (.local, ldR), none)) fDq [(vv kFu), (vv kD), (.op .sub [(vv ldZ), (.const 1)]), (vv ldB)]) (.return (vv ldR))))) (.return (.const 0))))))

structure LdCodes (C : Ctx) : Prop where
  uk : C.code.lookup fUk = some ([ukE].map (fun p => (p, ShapeHOL.one)), ukBody C, .one)
  hn : C.code.lookup fHn = some ([hnE].map (fun p => (p, ShapeHOL.one)), hnBody C, .one)
  sq : C.code.lookup fSq = some (sqParams.map (fun p => (p, ShapeHOL.one)), sqBody, .one)
  tu : C.code.lookup fTu = some (tuParams.map (fun p => (p, ShapeHOL.one)), tuBody, .one)
  uf : C.code.lookup UD.fUnfold = some ([UD.uE].map (fun p => (p, ShapeHOL.one)), UD.ufBody C, .one)
  wc : C.code.lookup fWC = some (wcParams.map (fun p => (p, ShapeHOL.one)), wcE, .one)
  ds : C.code.lookup fDsp = some (dsParams.map (fun p => (p, ShapeHOL.one)), dsBody, .one)
  dq : C.code.lookup fDq = some (dqParams.map (fun p => (p, ShapeHOL.one)), dqBody C, .one)

section
variable {σ : Type}

theorem lds_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) (hc : LdCodes C) (Q : AState → Prop) (d : Nat) (hdd : d < 2 ^ 63)
    (hQuk : ∀ s1 e a s2, Q s1 → unfoldableHead C.fe e s1 = .ok (a, s2) → Q s2)
    (hQhn : ∀ s1 e a s2, Q s1 → headHint C.fe e s1 = .ok (a, s2) → Q s2)
    (hQsq : ∀ s1 a b r s2, Q s1 → sameConstHeads a b s1 = .ok (r, s2) → Q s2)
    (hQtu : ∀ s1 d e r s2, Q s1 → tryUnfoldProjApp (knot mode C n) d e s1 = .ok (r, s2) → Q s2)
    (hQuf : ∀ s1 e r s2, Q s1 → unfoldDefinition C.fe e s1 = .ok (r, s2) → Q s2)
    (hQwc : ∀ s1 c d e r s2, Q s1 → (knot mode C n).whnfCore c d e s1 = .ok (r, s2) → Q s2)
    (hQds : ∀ s1 d a b r s2, Q s1 → defeqSpine (knot mode C n) C.fe d a b s1 = .ok (r, s2) → Q s2)
    (hUK : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ e, SpecR (σ := σ) (Pre (ctxH C H) s1 ([ukE].zip [Enc.idxW e])) (ukBody C) s1
      (unfoldableHead C.fe e) (PostB (ctxH C H)))
    (hHN : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ e, SpecR (σ := σ) (Pre (ctxH C H) s1 ([hnE].zip [Enc.idxW e])) (hnBody C) s1
      (headHint C.fe e) (PostHn (ctxH C H)))
    (hSQ : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ a b, SpecR (σ := σ) (Pre (ctxH C H) s1 (sqParams.zip [Enc.idxW a, Enc.idxW b])) sqBody s1
      (sameConstHeads a b) (PostB (ctxH C H)))
    (hTU : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ d e, d < 2 ^ 63 → SpecR (σ := σ) (Pre (ctxH C H) s1 (tuParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d,
      Enc.idxW e])) tuBody s1 (tryUnfoldProjApp (knot mode C n) d e) (UD.PostO (ctxH C H)))
    (hUF : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ e, SpecR (σ := σ) (Pre (ctxH C H) s1 ([UD.uE].zip [Enc.idxW e])) (UD.ufBody C) s1
      (unfoldDefinition C.fe e) (UD.PostO (ctxH C H)))
    (hWC : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ c d e, d < 2 ^ 63 → Callee (σ := σ) (ctxH C H) wcParams
      [BitVec.ofNat 64 n, boolW c, BitVec.ofNat 64 d, Enc.idxW e] wcE s1 ((knot mode C n).whnfCore c d e)
      (PostK (ctxH C H)))
    (hDS : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ d a b, d < 2 ^ 63 → SpecR (σ := σ) (Pre (ctxH C H) s1 (dsParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d,
      Enc.idxW a, Enc.idxW b])) dsBody s1 (defeqSpine (knot mode C n) C.fe d a b) (PostB (ctxH C H)))
    (hDQ : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ a b, SpecR (σ := σ) (Pre (ctxH C H) s1 (dqParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d,
      Enc.idxW a, Enc.idxW b])) (dqBody C) s1 (deltaQuick mode (knot mode C n) d a b) (PostDS (ctxH C H)))
    (s : AState) (hq : Q s) (a b : EIdx) :
    SpecR (σ := σ) (Pre C s (ldParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b])) ldBody s
      (lazyDeltaStep mode (knot mode C n) C.fe d a b) (PostDS C) := by
  refine specR_prologue (postDS_locals C) (Knot.params_none C ldLocals ldParams _ (by decide) (by decide)) ?_
  unfold lazyDeltaStep
  refine specR_callNIH (C := C) ldUa fUk [ukE] [(vv ldA)] (ukBody C)
    [Enc.idxW a] (by decide) rfl (by decide) hc.uk
    ⟨by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
    (fun r_ w s' st => unfoldableHead C.fe a s = .ok (r_, s') ∧ PostB (C) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ unfoldableHead C.fe a s = .ok (r_, s'))
    (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [ukE] _ rfl hlk) (hUK C.H s (List.prefix_refl _) hq a)))
    (fun ua w1 s1 H1 hp1 ⟨hw1, hrun1⟩ => ?_)
  have hq1 := hQuk s a ua s1 hq hrun1
  have hpa1 : C.H <+: H1 := (List.prefix_refl _).trans hp1
  subst hw1
  refine specR_callNIH (C := ctxH C H1) ldUb fUk [ukE] [(vv ldB)] (ukBody C)
    [Enc.idxW b] (by decide) rfl (by decide) hc.uk
    ⟨by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
    (fun r_ w s' st => unfoldableHead C.fe b s1 = .ok (r_, s') ∧ PostB (ctxH C H1) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ unfoldableHead C.fe b s1 = .ok (r_, s'))
    (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [ukE] _ rfl hlk) (hUK H1 s1 hpa1 hq1 b)))
    (fun ub w2 s2 H2 hp2 ⟨hw2, hrun2⟩ => ?_)
  have hq2 := hQuk s1 b ub s2 hq1 hrun2
  have hpa2 : C.H <+: H2 := hpa1.trans hp2
  subst hw2
  cases ua <;> cases ub
  · refine specR_ifI _ 0 (by simp [boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H2, hpa2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_ifI _ 0 (by simp [boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    refine specR_callNIH (C := ctxH C H2) ldZ fTu tuParams [(vv kFu), (vv kD), (vv ldA)] tuBody
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a] (by decide) rfl (by decide) hc.tu
      ⟨by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
      (fun r_ w s' st => tryUnfoldProjApp (knot mode C n) d a s2 = .ok (r_, s') ∧ UD.PostO (ctxH C H2) r_ w s' st) (fun r_ w s' H' => w = optW r_ ∧ tryUnfoldProjApp (knot mode C n) d a s2 = .ok (r_, s'))
      (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu tuParams _ rfl hlk) (hTU H2 s2 hpa2 hq2 d a hdd)))
      (fun oz w3 s3 H3 hp3 ⟨hw3, hrun3⟩ => ?_)
    have hq3 := hQtu s2 d a oz s3 hq2 hrun3
    have hpa3 : C.H <+: H3 := hpa2.trans hp3
    subst hw3
    rcases oz with _ | ozv
    · refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      try dsimp only
      refine specR_callNIH (C := ctxH C H3) ldX UD.fUnfold [UD.uE] [(vv ldB)] (UD.ufBody C)
        [Enc.idxW b] (by decide) rfl (by decide) hc.uf
        ⟨by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
        (fun r_ w s' st => unfoldDefinition C.fe b s3 = .ok (r_, s') ∧ UD.PostO (ctxH C H3) r_ w s' st) (fun r_ w s' H' => w = optW r_ ∧ unfoldDefinition C.fe b s3 = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [UD.uE] _ rfl hlk) (hUF H3 s3 hpa3 hq3 b)))
        (fun ou w4 s4 H4 hp4 ⟨hw4, hrun4⟩ => ?_)
      have hq4 := hQuf s3 b ou s4 hq3 hrun4
      have hpa4 : C.H <+: H4 := hpa3.trans hp4
      subst hw4
      rcases ou with _ | ouv
      · refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
        try dsimp only
        exact specR_returnI _ 0 rfl (fun t ht => ⟨H4, hpa4, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

      refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne ouv) (fun h => absurd rfl h) (fun _ => ?_)
      try dsimp only
      refine specR_callNIH (C := ctxH C H4) ldY fWC wcParams [(vv kFu), (.const 1), (vv kD), (.op .sub [(vv ldX), (.const 1)])] wcE
        [BitVec.ofNat 64 n, boolW true, BitVec.ofNat 64 d, Enc.idxW ouv] (by decide) rfl (by decide) hc.wc
        ⟨by simp +decide [Env.get, ldParams, ctxEnv], rfl, by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [sev, Env.get, ldParams, ctxEnv, optWG]; exact BitVec.add_sub_cancel _ _, trivial⟩
        (fun r_ w s' st => (knot mode C n).whnfCore true d ouv s4 = .ok (r_, s') ∧ PostK (ctxH C H4) r_ w s' st) (fun r_ w s' H' => w = Enc.idxW r_ ∧ (knot mode C n).whnfCore true d ouv s4 = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (hWC H4 s4 hpa4 hq4 true d ouv hdd u hu (fun i hi _ => hlk i (by omega))))
        (fun e3 w5 s5 H5 hp5 ⟨hw5, hrun5⟩ => ?_)
      have hq5 := hQwc s4 true d ouv e3 s5 hq4 hrun5
      have hpa5 : C.H <+: H5 := hpa4.trans hp5
      subst hw5
      refine specR_congr (m' := deltaQuick mode (knot mode C n) d a e3 >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H5) ldR fDq dqParams [vv kFu, vv kD, vv ldA, vv ldY] (dqBody C)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW e3] (by decide) rfl (by decide) hc.dq
        ⟨by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
        (PostDS (ctxH C H5)) (fun r_ w _ H' => dsW C H' r_ w) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu dqParams _ rfl hlk) (hDQ H5 s5 hpa5 hq5 a e3))
        (fun r6 w6 s6 H6 hp6 hw6 => ?_)
      exact specR_returnI _ w6 (by simp) (fun t ht => ⟨H6, hpa5.trans hp6, hw6, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne ozv) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    refine specR_congr (m' := deltaQuick mode (knot mode C n) d ozv b >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H3) ldR fDq dqParams [vv kFu, vv kD, .op .sub [vv ldZ, .const 1], vv ldB] (dqBody C)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ozv, Enc.idxW b] (by decide) rfl (by decide) hc.dq
      ⟨by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [sev, Env.get, ldParams, ctxEnv, optWG]; exact BitVec.add_sub_cancel _ _, by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
      (PostDS (ctxH C H3)) (fun r_ w _ H' => dsW C H' r_ w) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu dqParams _ rfl hlk) (hDQ H3 s3 hpa3 hq3 ozv b))
      (fun r7 w7 s7 H7 hp7 hw7 => ?_)
    exact specR_returnI _ w7 (by simp) (fun t ht => ⟨H7, hpa3.trans hp7, hw7, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

  · refine specR_ifI _ 1 (by simp [boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    refine specR_callNIH (C := ctxH C H2) ldZ fTu tuParams [(vv kFu), (vv kD), (vv ldB)] tuBody
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW b] (by decide) rfl (by decide) hc.tu
      ⟨by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
      (fun r_ w s' st => tryUnfoldProjApp (knot mode C n) d b s2 = .ok (r_, s') ∧ UD.PostO (ctxH C H2) r_ w s' st) (fun r_ w s' H' => w = optW r_ ∧ tryUnfoldProjApp (knot mode C n) d b s2 = .ok (r_, s'))
      (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu tuParams _ rfl hlk) (hTU H2 s2 hpa2 hq2 d b hdd)))
      (fun oz w8 s8 H8 hp8 ⟨hw8, hrun8⟩ => ?_)
    have hq8 := hQtu s2 d b oz s8 hq2 hrun8
    have hpa8 : C.H <+: H8 := hpa2.trans hp8
    subst hw8
    rcases oz with _ | ozv
    · refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      try dsimp only
      refine specR_callNIH (C := ctxH C H8) ldX UD.fUnfold [UD.uE] [(vv ldA)] (UD.ufBody C)
        [Enc.idxW a] (by decide) rfl (by decide) hc.uf
        ⟨by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
        (fun r_ w s' st => unfoldDefinition C.fe a s8 = .ok (r_, s') ∧ UD.PostO (ctxH C H8) r_ w s' st) (fun r_ w s' H' => w = optW r_ ∧ unfoldDefinition C.fe a s8 = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [UD.uE] _ rfl hlk) (hUF H8 s8 hpa8 hq8 a)))
        (fun ou w9 s9 H9 hp9 ⟨hw9, hrun9⟩ => ?_)
      have hq9 := hQuf s8 a ou s9 hq8 hrun9
      have hpa9 : C.H <+: H9 := hpa8.trans hp9
      subst hw9
      rcases ou with _ | ouv
      · refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
        try dsimp only
        exact specR_returnI _ 0 rfl (fun t ht => ⟨H9, hpa9, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

      refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne ouv) (fun h => absurd rfl h) (fun _ => ?_)
      try dsimp only
      refine specR_callNIH (C := ctxH C H9) ldY fWC wcParams [(vv kFu), (.const 1), (vv kD), (.op .sub [(vv ldX), (.const 1)])] wcE
        [BitVec.ofNat 64 n, boolW true, BitVec.ofNat 64 d, Enc.idxW ouv] (by decide) rfl (by decide) hc.wc
        ⟨by simp +decide [Env.get, ldParams, ctxEnv], rfl, by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [sev, Env.get, ldParams, ctxEnv, optWG]; exact BitVec.add_sub_cancel _ _, trivial⟩
        (fun r_ w s' st => (knot mode C n).whnfCore true d ouv s9 = .ok (r_, s') ∧ PostK (ctxH C H9) r_ w s' st) (fun r_ w s' H' => w = Enc.idxW r_ ∧ (knot mode C n).whnfCore true d ouv s9 = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (hWC H9 s9 hpa9 hq9 true d ouv hdd u hu (fun i hi _ => hlk i (by omega))))
        (fun e3 w10 s10 H10 hp10 ⟨hw10, hrun10⟩ => ?_)
      have hq10 := hQwc s9 true d ouv e3 s10 hq9 hrun10
      have hpa10 : C.H <+: H10 := hpa9.trans hp10
      subst hw10
      refine specR_congr (m' := deltaQuick mode (knot mode C n) d e3 b >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H10) ldR fDq dqParams [vv kFu, vv kD, vv ldY, vv ldB] (dqBody C)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e3, Enc.idxW b] (by decide) rfl (by decide) hc.dq
        ⟨by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
        (PostDS (ctxH C H10)) (fun r_ w _ H' => dsW C H' r_ w) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu dqParams _ rfl hlk) (hDQ H10 s10 hpa10 hq10 e3 b))
        (fun r11 w11 s11 H11 hp11 hw11 => ?_)
      exact specR_returnI _ w11 (by simp) (fun t ht => ⟨H11, hpa10.trans hp11, hw11, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne ozv) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    refine specR_congr (m' := deltaQuick mode (knot mode C n) d a ozv >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H8) ldR fDq dqParams [vv kFu, vv kD, vv ldA, .op .sub [vv ldZ, .const 1]] (dqBody C)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW ozv] (by decide) rfl (by decide) hc.dq
      ⟨by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [sev, Env.get, ldParams, ctxEnv, optWG]; exact BitVec.add_sub_cancel _ _, trivial⟩
      (PostDS (ctxH C H8)) (fun r_ w _ H' => dsW C H' r_ w) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu dqParams _ rfl hlk) (hDQ H8 s8 hpa8 hq8 a ozv))
      (fun r12 w12 s12 H12 hp12 hw12 => ?_)
    exact specR_returnI _ w12 (by simp) (fun t ht => ⟨H12, hpa8.trans hp12, hw12, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

  refine specR_ifI _ 1 (by simp [boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
  refine specR_ifI _ 1 (by simp [boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
  try dsimp only
  refine specR_callNIH (C := ctxH C H2) ldHa fHn [hnE] [(vv ldA)] (hnBody C)
    [Enc.idxW a] (by decide) rfl (by decide) hc.hn
    ⟨by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
    (fun r_ w s' st => headHint C.fe a s2 = .ok (r_, s') ∧ PostHn (ctxH C H2) r_ w s' st) (fun r_ w s' _ => w = BitVec.ofNat 64 (hintN r_) ∧ hintN r_ < 2 ^ 63 ∧ headHint C.fe a s2 = .ok (r_, s'))
    (fun r_ w s' st ⟨hr, H', hp', hw, hl, hsr⟩ => ⟨H', hp', ⟨hw, hl, hr⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [hnE] _ rfl hlk) (hHN H2 s2 hpa2 hq2 a)))
    (fun ha w13 s13 H13 hp13 ⟨hw13, hl13, hrun13⟩ => ?_)
  have hq13 := hQhn s2 a ha s13 hq2 hrun13
  have hpa13 : C.H <+: H13 := hpa2.trans hp13
  subst hw13
  refine specR_callNIH (C := ctxH C H13) ldHb fHn [hnE] [(vv ldB)] (hnBody C)
    [Enc.idxW b] (by decide) rfl (by decide) hc.hn
    ⟨by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
    (fun r_ w s' st => headHint C.fe b s13 = .ok (r_, s') ∧ PostHn (ctxH C H13) r_ w s' st) (fun r_ w s' _ => w = BitVec.ofNat 64 (hintN r_) ∧ hintN r_ < 2 ^ 63 ∧ headHint C.fe b s13 = .ok (r_, s'))
    (fun r_ w s' st ⟨hr, H', hp', hw, hl, hsr⟩ => ⟨H', hp', ⟨hw, hl, hr⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [hnE] _ rfl hlk) (hHN H13 s13 hpa13 hq13 b)))
    (fun hb w14 s14 H14 hp14 ⟨hw14, hl14, hrun14⟩ => ?_)
  have hq14 := hQhn s13 b hb s14 hq13 hrun14
  have hpa14 : C.H <+: H14 := hpa13.trans hp14
  subst hw14
  cases hbc : ConLeche.ReducibilityHint.lt hb ha
  · refine specR_ifI _ 0 (by rw [sev_hltE _ _ _ hb ha (by simp +decide [Env.get, ldParams, ctxEnv]) (by simp +decide [Env.get, ldParams, ctxEnv]) hl14 hl13]; rw [hbc]; rfl) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [hbc, Bool.false_eq_true, ↓reduceIte]
    cases hbc2 : ConLeche.ReducibilityHint.lt ha hb
    · refine specR_ifI _ 0 (by rw [sev_hltE _ _ _ ha hb (by simp +decide [Env.get, ldParams, ctxEnv]) (by simp +decide [Env.get, ldParams, ctxEnv]) hl13 hl14]; rw [hbc2]; rfl) (fun h => absurd rfl h) (fun _ => ?_)
      simp only [hbc2, Bool.false_eq_true, ↓reduceIte]
      refine specR_callNIH (C := ctxH C H14) ldS fSq sqParams [(vv ldA), (vv ldB)] sqBody
        [Enc.idxW a, Enc.idxW b] (by decide) rfl (by decide) hc.sq
        ⟨by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
        (fun r_ w s' st => sameConstHeads a b s14 = .ok (r_, s') ∧ PostB (ctxH C H14) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ sameConstHeads a b s14 = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu sqParams _ rfl hlk) (hSQ H14 s14 hpa14 hq14 a b)))
        (fun sch w15 s15 H15 hp15 ⟨hw15, hrun15⟩ => ?_)
      have hq15 := hQsq s14 a b sch s15 hq14 hrun15
      have hpa15 : C.H <+: H15 := hpa14.trans hp15
      subst hw15
      cases hbc2 : (ConLeche.ReducibilityHint.sameRegular ha hb && sch)
      · refine specR_ifI _ _ (sev_and_hsr _ _ _ _ ha hb sch (by simp +decide [Env.get, ldParams, ctxEnv]) (by simp +decide [Env.get, ldParams, ctxEnv]) (by simp +decide [Env.get, ldParams, ctxEnv]) hl13 hl14) (fun h => absurd (by rw [hbc2]; rfl) h) (fun _ => ?_)
        simp only [hbc2, Bool.false_eq_true, ↓reduceIte, pure_bind]
        refine specR_callNIH (C := ctxH C H15) ldX2 UD.fUnfold [UD.uE] [(vv ldA)] (UD.ufBody C)
          [Enc.idxW a] (by decide) rfl (by decide) hc.uf
          ⟨by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
          (fun r_ w s' st => unfoldDefinition C.fe a s15 = .ok (r_, s') ∧ UD.PostO (ctxH C H15) r_ w s' st) (fun r_ w s' H' => w = optW r_ ∧ unfoldDefinition C.fe a s15 = .ok (r_, s'))
          (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
          (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [UD.uE] _ rfl hlk) (hUF H15 s15 hpa15 hq15 a)))
          (fun oa w22 s22 H22 hp22 ⟨hw22, hrun22⟩ => ?_)
        have hq22 := hQuf s15 a oa s22 hq15 hrun22
        have hpa22 : C.H <+: H22 := hpa15.trans hp22
        subst hw22
        refine specR_callNIH (C := ctxH C H22) ldY2 UD.fUnfold [UD.uE] [(vv ldB)] (UD.ufBody C)
          [Enc.idxW b] (by decide) rfl (by decide) hc.uf
          ⟨by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
          (fun r_ w s' st => unfoldDefinition C.fe b s22 = .ok (r_, s') ∧ UD.PostO (ctxH C H22) r_ w s' st) (fun r_ w s' H' => w = optW r_ ∧ unfoldDefinition C.fe b s22 = .ok (r_, s'))
          (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
          (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [UD.uE] _ rfl hlk) (hUF H22 s22 hpa22 hq22 b)))
          (fun ob w23 s23 H23 hp23 ⟨hw23, hrun23⟩ => ?_)
        have hq23 := hQuf s22 b ob s23 hq22 hrun23
        have hpa23 : C.H <+: H23 := hpa22.trans hp23
        subst hw23
        rcases oa with _ | a2 <;> rcases ob with _ | b2
        · refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
          try dsimp only
          exact specR_returnI _ 0 rfl (fun t ht => ⟨H23, hpa23, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
        · refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
          try dsimp only
          exact specR_returnI _ 0 rfl (fun t ht => ⟨H23, hpa23, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
        · refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne a2) (fun h => absurd rfl h) (fun _ => ?_)
          refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
          try dsimp only
          exact specR_returnI _ 0 rfl (fun t ht => ⟨H23, hpa23, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
        · refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne a2) (fun h => absurd rfl h) (fun _ => ?_)
          refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne b2) (fun h => absurd rfl h) (fun _ => ?_)
          try dsimp only
          refine specR_callNIH (C := ctxH C H23) ldZ fWC wcParams [(vv kFu), (.const 1), (vv kD), (.op .sub [(vv ldX2), (.const 1)])] wcE
            [BitVec.ofNat 64 n, boolW true, BitVec.ofNat 64 d, Enc.idxW a2] (by decide) rfl (by decide) hc.wc
            ⟨by simp +decide [Env.get, ldParams, ctxEnv], rfl, by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [sev, Env.get, ldParams, ctxEnv, optWG]; exact BitVec.add_sub_cancel _ _, trivial⟩
            (fun r_ w s' st => (knot mode C n).whnfCore true d a2 s23 = .ok (r_, s') ∧ PostK (ctxH C H23) r_ w s' st) (fun r_ w s' H' => w = Enc.idxW r_ ∧ (knot mode C n).whnfCore true d a2 s23 = .ok (r_, s'))
            (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
            (fun u hu _ hlk => specR_run (hWC H23 s23 hpa23 hq23 true d a2 hdd u hu (fun i hi _ => hlk i (by omega))))
            (fun a3 w24 s24 H24 hp24 ⟨hw24, hrun24⟩ => ?_)
          have hq24 := hQwc s23 true d a2 a3 s24 hq23 hrun24
          have hpa24 : C.H <+: H24 := hpa23.trans hp24
          subst hw24
          refine specR_callNIH (C := ctxH C H24) ldZ2 fWC wcParams [(vv kFu), (.const 1), (vv kD), (.op .sub [(vv ldY2), (.const 1)])] wcE
            [BitVec.ofNat 64 n, boolW true, BitVec.ofNat 64 d, Enc.idxW b2] (by decide) rfl (by decide) hc.wc
            ⟨by simp +decide [Env.get, ldParams, ctxEnv], rfl, by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [sev, Env.get, ldParams, ctxEnv, optWG]; exact BitVec.add_sub_cancel _ _, trivial⟩
            (fun r_ w s' st => (knot mode C n).whnfCore true d b2 s24 = .ok (r_, s') ∧ PostK (ctxH C H24) r_ w s' st) (fun r_ w s' H' => w = Enc.idxW r_ ∧ (knot mode C n).whnfCore true d b2 s24 = .ok (r_, s'))
            (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
            (fun u hu _ hlk => specR_run (hWC H24 s24 hpa24 hq24 true d b2 hdd u hu (fun i hi _ => hlk i (by omega))))
            (fun b3 w25 s25 H25 hp25 ⟨hw25, hrun25⟩ => ?_)
          have hq25 := hQwc s24 true d b2 b3 s25 hq24 hrun25
          have hpa25 : C.H <+: H25 := hpa24.trans hp25
          subst hw25
          refine specR_congr (m' := deltaQuick mode (knot mode C n) d a3 b3 >>= fun r => pure r) (by simp) ?_
          refine specR_callNIH (C := ctxH C H25) ldR fDq dqParams [vv kFu, vv kD, vv ldZ, vv ldZ2] (dqBody C)
            [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a3, Enc.idxW b3] (by decide) rfl (by decide) hc.dq
            ⟨by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
            (PostDS (ctxH C H25)) (fun r_ w _ H' => dsW C H' r_ w) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
            (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu dqParams _ rfl hlk) (hDQ H25 s25 hpa25 hq25 a3 b3))
            (fun r26 w26 s26 H26 hp26 hw26 => ?_)
          exact specR_returnI _ w26 (by simp) (fun t ht => ⟨H26, hpa25.trans hp26, hw26, sr_of_eq ht.sr rfl rfl rfl rfl⟩)


      refine specR_ifI _ _ (sev_and_hsr _ _ _ _ ha hb sch (by simp +decide [Env.get, ldParams, ctxEnv]) (by simp +decide [Env.get, ldParams, ctxEnv]) (by simp +decide [Env.get, ldParams, ctxEnv]) hl13 hl14) (fun _ => ?_) (fun h => absurd h (by rw [hbc2]; decide))
      simp only [hbc2, ↓reduceIte]
      refine specR_callNIH (C := ctxH C H15) ldP fDsp dsParams [(vv kFu), (vv kD), (vv ldA), (vv ldB)] dsBody
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (by decide) rfl (by decide) hc.ds
        ⟨by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
        (fun r_ w s' st => defeqSpine (knot mode C n) C.fe d a b s15 = .ok (r_, s') ∧ PostB (ctxH C H15) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ defeqSpine (knot mode C n) C.fe d a b s15 = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu dsParams _ rfl hlk) (hDS H15 s15 hpa15 hq15 d a b hdd)))
        (fun sp w16 s16 H16 hp16 ⟨hw16, hrun16⟩ => ?_)
      have hq16 := hQds s15 d a b sp s16 hq15 hrun16
      have hpa16 : C.H <+: H16 := hpa15.trans hp16
      subst hw16
      cases sp
      · refine specR_ifI _ 0 (by simp [boolW]) (fun h => absurd rfl h) (fun _ => ?_)
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine specR_callNIH (C := ctxH C H16) ldX2 UD.fUnfold [UD.uE] [(vv ldA)] (UD.ufBody C)
          [Enc.idxW a] (by decide) rfl (by decide) hc.uf
          ⟨by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
          (fun r_ w s' st => unfoldDefinition C.fe a s16 = .ok (r_, s') ∧ UD.PostO (ctxH C H16) r_ w s' st) (fun r_ w s' H' => w = optW r_ ∧ unfoldDefinition C.fe a s16 = .ok (r_, s'))
          (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
          (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [UD.uE] _ rfl hlk) (hUF H16 s16 hpa16 hq16 a)))
          (fun oa w17 s17 H17 hp17 ⟨hw17, hrun17⟩ => ?_)
        have hq17 := hQuf s16 a oa s17 hq16 hrun17
        have hpa17 : C.H <+: H17 := hpa16.trans hp17
        subst hw17
        refine specR_callNIH (C := ctxH C H17) ldY2 UD.fUnfold [UD.uE] [(vv ldB)] (UD.ufBody C)
          [Enc.idxW b] (by decide) rfl (by decide) hc.uf
          ⟨by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
          (fun r_ w s' st => unfoldDefinition C.fe b s17 = .ok (r_, s') ∧ UD.PostO (ctxH C H17) r_ w s' st) (fun r_ w s' H' => w = optW r_ ∧ unfoldDefinition C.fe b s17 = .ok (r_, s'))
          (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
          (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [UD.uE] _ rfl hlk) (hUF H17 s17 hpa17 hq17 b)))
          (fun ob w18 s18 H18 hp18 ⟨hw18, hrun18⟩ => ?_)
        have hq18 := hQuf s17 b ob s18 hq17 hrun18
        have hpa18 : C.H <+: H18 := hpa17.trans hp18
        subst hw18
        rcases oa with _ | a2 <;> rcases ob with _ | b2
        · refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
          try dsimp only
          exact specR_returnI _ 0 rfl (fun t ht => ⟨H18, hpa18, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
        · refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
          try dsimp only
          exact specR_returnI _ 0 rfl (fun t ht => ⟨H18, hpa18, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
        · refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne a2) (fun h => absurd rfl h) (fun _ => ?_)
          refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
          try dsimp only
          exact specR_returnI _ 0 rfl (fun t ht => ⟨H18, hpa18, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
        · refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne a2) (fun h => absurd rfl h) (fun _ => ?_)
          refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne b2) (fun h => absurd rfl h) (fun _ => ?_)
          try dsimp only
          refine specR_callNIH (C := ctxH C H18) ldZ fWC wcParams [(vv kFu), (.const 1), (vv kD), (.op .sub [(vv ldX2), (.const 1)])] wcE
            [BitVec.ofNat 64 n, boolW true, BitVec.ofNat 64 d, Enc.idxW a2] (by decide) rfl (by decide) hc.wc
            ⟨by simp +decide [Env.get, ldParams, ctxEnv], rfl, by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [sev, Env.get, ldParams, ctxEnv, optWG]; exact BitVec.add_sub_cancel _ _, trivial⟩
            (fun r_ w s' st => (knot mode C n).whnfCore true d a2 s18 = .ok (r_, s') ∧ PostK (ctxH C H18) r_ w s' st) (fun r_ w s' H' => w = Enc.idxW r_ ∧ (knot mode C n).whnfCore true d a2 s18 = .ok (r_, s'))
            (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
            (fun u hu _ hlk => specR_run (hWC H18 s18 hpa18 hq18 true d a2 hdd u hu (fun i hi _ => hlk i (by omega))))
            (fun a3 w19 s19 H19 hp19 ⟨hw19, hrun19⟩ => ?_)
          have hq19 := hQwc s18 true d a2 a3 s19 hq18 hrun19
          have hpa19 : C.H <+: H19 := hpa18.trans hp19
          subst hw19
          refine specR_callNIH (C := ctxH C H19) ldZ2 fWC wcParams [(vv kFu), (.const 1), (vv kD), (.op .sub [(vv ldY2), (.const 1)])] wcE
            [BitVec.ofNat 64 n, boolW true, BitVec.ofNat 64 d, Enc.idxW b2] (by decide) rfl (by decide) hc.wc
            ⟨by simp +decide [Env.get, ldParams, ctxEnv], rfl, by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [sev, Env.get, ldParams, ctxEnv, optWG]; exact BitVec.add_sub_cancel _ _, trivial⟩
            (fun r_ w s' st => (knot mode C n).whnfCore true d b2 s19 = .ok (r_, s') ∧ PostK (ctxH C H19) r_ w s' st) (fun r_ w s' H' => w = Enc.idxW r_ ∧ (knot mode C n).whnfCore true d b2 s19 = .ok (r_, s'))
            (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
            (fun u hu _ hlk => specR_run (hWC H19 s19 hpa19 hq19 true d b2 hdd u hu (fun i hi _ => hlk i (by omega))))
            (fun b3 w20 s20 H20 hp20 ⟨hw20, hrun20⟩ => ?_)
          have hq20 := hQwc s19 true d b2 b3 s20 hq19 hrun20
          have hpa20 : C.H <+: H20 := hpa19.trans hp20
          subst hw20
          refine specR_congr (m' := deltaQuick mode (knot mode C n) d a3 b3 >>= fun r => pure r) (by simp) ?_
          refine specR_callNIH (C := ctxH C H20) ldR fDq dqParams [vv kFu, vv kD, vv ldZ, vv ldZ2] (dqBody C)
            [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a3, Enc.idxW b3] (by decide) rfl (by decide) hc.dq
            ⟨by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
            (PostDS (ctxH C H20)) (fun r_ w _ H' => dsW C H' r_ w) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
            (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu dqParams _ rfl hlk) (hDQ H20 s20 hpa20 hq20 a3 b3))
            (fun r21 w21 s21 H21 hp21 hw21 => ?_)
          exact specR_returnI _ w21 (by simp) (fun t ht => ⟨H21, hpa20.trans hp21, hw21, sr_of_eq ht.sr rfl rfl rfl rfl⟩)


      refine specR_ifI _ 1 (by simp [boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [↓reduceIte]
      exact specR_returnI _ 1 rfl (fun t ht => ⟨H16, hpa16, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    refine specR_ifI _ 1 (by rw [sev_hltE _ _ _ ha hb (by simp +decide [Env.get, ldParams, ctxEnv]) (by simp +decide [Env.get, ldParams, ctxEnv]) hl13 hl14]; rw [hbc2]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [hbc2, ↓reduceIte]
    refine specR_callNIH (C := ctxH C H14) ldX UD.fUnfold [UD.uE] [(vv ldB)] (UD.ufBody C)
      [Enc.idxW b] (by decide) rfl (by decide) hc.uf
      ⟨by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
      (fun r_ w s' st => unfoldDefinition C.fe b s14 = .ok (r_, s') ∧ UD.PostO (ctxH C H14) r_ w s' st) (fun r_ w s' H' => w = optW r_ ∧ unfoldDefinition C.fe b s14 = .ok (r_, s'))
      (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [UD.uE] _ rfl hlk) (hUF H14 s14 hpa14 hq14 b)))
      (fun ou w27 s27 H27 hp27 ⟨hw27, hrun27⟩ => ?_)
    have hq27 := hQuf s14 b ou s27 hq14 hrun27
    have hpa27 : C.H <+: H27 := hpa14.trans hp27
    subst hw27
    rcases ou with _ | ouv
    · refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      try dsimp only
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H27, hpa27, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne ouv) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    refine specR_callNIH (C := ctxH C H27) ldY fWC wcParams [(vv kFu), (.const 1), (vv kD), (.op .sub [(vv ldX), (.const 1)])] wcE
      [BitVec.ofNat 64 n, boolW true, BitVec.ofNat 64 d, Enc.idxW ouv] (by decide) rfl (by decide) hc.wc
      ⟨by simp +decide [Env.get, ldParams, ctxEnv], rfl, by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [sev, Env.get, ldParams, ctxEnv, optWG]; exact BitVec.add_sub_cancel _ _, trivial⟩
      (fun r_ w s' st => (knot mode C n).whnfCore true d ouv s27 = .ok (r_, s') ∧ PostK (ctxH C H27) r_ w s' st) (fun r_ w s' H' => w = Enc.idxW r_ ∧ (knot mode C n).whnfCore true d ouv s27 = .ok (r_, s'))
      (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (hWC H27 s27 hpa27 hq27 true d ouv hdd u hu (fun i hi _ => hlk i (by omega))))
      (fun e3 w28 s28 H28 hp28 ⟨hw28, hrun28⟩ => ?_)
    have hq28 := hQwc s27 true d ouv e3 s28 hq27 hrun28
    have hpa28 : C.H <+: H28 := hpa27.trans hp28
    subst hw28
    refine specR_congr (m' := deltaQuick mode (knot mode C n) d a e3 >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H28) ldR fDq dqParams [vv kFu, vv kD, vv ldA, vv ldY] (dqBody C)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW e3] (by decide) rfl (by decide) hc.dq
      ⟨by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
      (PostDS (ctxH C H28)) (fun r_ w _ H' => dsW C H' r_ w) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu dqParams _ rfl hlk) (hDQ H28 s28 hpa28 hq28 a e3))
      (fun r29 w29 s29 H29 hp29 hw29 => ?_)
    exact specR_returnI _ w29 (by simp) (fun t ht => ⟨H29, hpa28.trans hp29, hw29, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

  refine specR_ifI _ 1 (by rw [sev_hltE _ _ _ hb ha (by simp +decide [Env.get, ldParams, ctxEnv]) (by simp +decide [Env.get, ldParams, ctxEnv]) hl14 hl13]; rw [hbc]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
  simp only [hbc, ↓reduceIte]
  refine specR_callNIH (C := ctxH C H14) ldX UD.fUnfold [UD.uE] [(vv ldA)] (UD.ufBody C)
    [Enc.idxW a] (by decide) rfl (by decide) hc.uf
    ⟨by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
    (fun r_ w s' st => unfoldDefinition C.fe a s14 = .ok (r_, s') ∧ UD.PostO (ctxH C H14) r_ w s' st) (fun r_ w s' H' => w = optW r_ ∧ unfoldDefinition C.fe a s14 = .ok (r_, s'))
    (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [UD.uE] _ rfl hlk) (hUF H14 s14 hpa14 hq14 a)))
    (fun ou w30 s30 H30 hp30 ⟨hw30, hrun30⟩ => ?_)
  have hq30 := hQuf s14 a ou s30 hq14 hrun30
  have hpa30 : C.H <+: H30 := hpa14.trans hp30
  subst hw30
  rcases ou with _ | ouv
  · refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H30, hpa30, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne ouv) (fun h => absurd rfl h) (fun _ => ?_)
  try dsimp only
  refine specR_callNIH (C := ctxH C H30) ldY fWC wcParams [(vv kFu), (.const 1), (vv kD), (.op .sub [(vv ldX), (.const 1)])] wcE
    [BitVec.ofNat 64 n, boolW true, BitVec.ofNat 64 d, Enc.idxW ouv] (by decide) rfl (by decide) hc.wc
    ⟨by simp +decide [Env.get, ldParams, ctxEnv], rfl, by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [sev, Env.get, ldParams, ctxEnv, optWG]; exact BitVec.add_sub_cancel _ _, trivial⟩
    (fun r_ w s' st => (knot mode C n).whnfCore true d ouv s30 = .ok (r_, s') ∧ PostK (ctxH C H30) r_ w s' st) (fun r_ w s' H' => w = Enc.idxW r_ ∧ (knot mode C n).whnfCore true d ouv s30 = .ok (r_, s'))
    (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (hWC H30 s30 hpa30 hq30 true d ouv hdd u hu (fun i hi _ => hlk i (by omega))))
    (fun e3 w31 s31 H31 hp31 ⟨hw31, hrun31⟩ => ?_)
  have hq31 := hQwc s30 true d ouv e3 s31 hq30 hrun31
  have hpa31 : C.H <+: H31 := hpa30.trans hp31
  subst hw31
  refine specR_congr (m' := deltaQuick mode (knot mode C n) d e3 b >>= fun r => pure r) (by simp) ?_
  refine specR_callNIH (C := ctxH C H31) ldR fDq dqParams [vv kFu, vv kD, vv ldY, vv ldB] (dqBody C)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e3, Enc.idxW b] (by decide) rfl (by decide) hc.dq
    ⟨by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], by simp +decide [Env.get, ldParams, ctxEnv], trivial⟩
    (PostDS (ctxH C H31)) (fun r_ w _ H' => dsW C H' r_ w) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu dqParams _ rfl hlk) (hDQ H31 s31 hpa31 hq31 e3 b))
    (fun r32 w32 s32 H32 hp32 hw32 => ?_)
  exact specR_returnI _ w32 (by simp) (fun t ht => ⟨H32, hpa31.trans hp32, hw32, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
