import ConPanqueque.T.Core.NzParam
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `nzS` over a level handle: never zero after a parameter substitution

As `nz`, except that a `param` node is looked up among the parameter names and its argument walked (`nzParam`).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def zsU := ofString "zsu"
def zsK := ofString "zsk"
def zsL := ofString "zsl"
def zsUs := ofString "zsus"
def zsA := ofString "zsa"
def zsB := ofString "zsb"
def zsX := ofString "zsx"
def zsY := ofString "zsy"
def zsN := ofString "zsn"
def fZs := ofString "neverZeroSubst"

@[simp] theorem zs_zsU_ne_zsK : zsU ≠ zsK := by decide
@[simp] theorem zs_zsU_ne_zsL : zsU ≠ zsL := by decide
@[simp] theorem zs_zsU_ne_zsUs : zsU ≠ zsUs := by decide
@[simp] theorem zs_zsU_ne_zsA : zsU ≠ zsA := by decide
@[simp] theorem zs_zsU_ne_zsB : zsU ≠ zsB := by decide
@[simp] theorem zs_zsU_ne_zsX : zsU ≠ zsX := by decide
@[simp] theorem zs_zsU_ne_zsY : zsU ≠ zsY := by decide
@[simp] theorem zs_zsU_ne_zsN : zsU ≠ zsN := by decide
@[simp] theorem zs_zsU_ne_lFl : zsU ≠ lFl := by decide
@[simp] theorem zs_lFl_ne_zsU : lFl ≠ zsU := by decide
@[simp] theorem zs_zsU_ne_lDh : zsU ≠ lDh := by decide
@[simp] theorem zs_lDh_ne_zsU : lDh ≠ zsU := by decide
@[simp] theorem zs_zsU_ne_lDt : zsU ≠ lDt := by decide
@[simp] theorem zs_lDt_ne_zsU : lDt ≠ zsU := by decide
@[simp] theorem zs_zsU_ne_lDg : zsU ≠ lDg := by decide
@[simp] theorem zs_lDg_ne_zsU : lDg ≠ zsU := by decide
@[simp] theorem zs_zsU_ne_lDi : zsU ≠ lDi := by decide
@[simp] theorem zs_lDi_ne_zsU : lDi ≠ zsU := by decide
@[simp] theorem zs_zsU_ne_lRp : zsU ≠ lRp := by decide
@[simp] theorem zs_lRp_ne_zsU : lRp ≠ zsU := by decide
@[simp] theorem zs_zsU_ne_lRn : zsU ≠ lRn := by decide
@[simp] theorem zs_lRn_ne_zsU : lRn ≠ zsU := by decide
@[simp] theorem zs_zsU_ne_lFll : zsU ≠ lFll := by decide
@[simp] theorem zs_lFll_ne_zsU : lFll ≠ zsU := by decide
@[simp] theorem zs_zsU_ne_lDir : zsU ≠ lDir := by decide
@[simp] theorem zs_lDir_ne_zsU : lDir ≠ zsU := by decide
@[simp] theorem zs_zsU_ne_lKb : zsU ≠ lKb := by decide
@[simp] theorem zs_lKb_ne_zsU : lKb ≠ zsU := by decide
@[simp] theorem zs_zsK_ne_zsU : zsK ≠ zsU := by decide
@[simp] theorem zs_zsK_ne_zsL : zsK ≠ zsL := by decide
@[simp] theorem zs_zsK_ne_zsUs : zsK ≠ zsUs := by decide
@[simp] theorem zs_zsK_ne_zsA : zsK ≠ zsA := by decide
@[simp] theorem zs_zsK_ne_zsB : zsK ≠ zsB := by decide
@[simp] theorem zs_zsK_ne_zsX : zsK ≠ zsX := by decide
@[simp] theorem zs_zsK_ne_zsY : zsK ≠ zsY := by decide
@[simp] theorem zs_zsK_ne_zsN : zsK ≠ zsN := by decide
@[simp] theorem zs_zsK_ne_lFl : zsK ≠ lFl := by decide
@[simp] theorem zs_lFl_ne_zsK : lFl ≠ zsK := by decide
@[simp] theorem zs_zsK_ne_lDh : zsK ≠ lDh := by decide
@[simp] theorem zs_lDh_ne_zsK : lDh ≠ zsK := by decide
@[simp] theorem zs_zsK_ne_lDt : zsK ≠ lDt := by decide
@[simp] theorem zs_lDt_ne_zsK : lDt ≠ zsK := by decide
@[simp] theorem zs_zsK_ne_lDg : zsK ≠ lDg := by decide
@[simp] theorem zs_lDg_ne_zsK : lDg ≠ zsK := by decide
@[simp] theorem zs_zsK_ne_lDi : zsK ≠ lDi := by decide
@[simp] theorem zs_lDi_ne_zsK : lDi ≠ zsK := by decide
@[simp] theorem zs_zsK_ne_lRp : zsK ≠ lRp := by decide
@[simp] theorem zs_lRp_ne_zsK : lRp ≠ zsK := by decide
@[simp] theorem zs_zsK_ne_lRn : zsK ≠ lRn := by decide
@[simp] theorem zs_lRn_ne_zsK : lRn ≠ zsK := by decide
@[simp] theorem zs_zsK_ne_lFll : zsK ≠ lFll := by decide
@[simp] theorem zs_lFll_ne_zsK : lFll ≠ zsK := by decide
@[simp] theorem zs_zsK_ne_lDir : zsK ≠ lDir := by decide
@[simp] theorem zs_lDir_ne_zsK : lDir ≠ zsK := by decide
@[simp] theorem zs_zsK_ne_lKb : zsK ≠ lKb := by decide
@[simp] theorem zs_lKb_ne_zsK : lKb ≠ zsK := by decide
@[simp] theorem zs_zsL_ne_zsU : zsL ≠ zsU := by decide
@[simp] theorem zs_zsL_ne_zsK : zsL ≠ zsK := by decide
@[simp] theorem zs_zsL_ne_zsUs : zsL ≠ zsUs := by decide
@[simp] theorem zs_zsL_ne_zsA : zsL ≠ zsA := by decide
@[simp] theorem zs_zsL_ne_zsB : zsL ≠ zsB := by decide
@[simp] theorem zs_zsL_ne_zsX : zsL ≠ zsX := by decide
@[simp] theorem zs_zsL_ne_zsY : zsL ≠ zsY := by decide
@[simp] theorem zs_zsL_ne_zsN : zsL ≠ zsN := by decide
@[simp] theorem zs_zsL_ne_lFl : zsL ≠ lFl := by decide
@[simp] theorem zs_lFl_ne_zsL : lFl ≠ zsL := by decide
@[simp] theorem zs_zsL_ne_lDh : zsL ≠ lDh := by decide
@[simp] theorem zs_lDh_ne_zsL : lDh ≠ zsL := by decide
@[simp] theorem zs_zsL_ne_lDt : zsL ≠ lDt := by decide
@[simp] theorem zs_lDt_ne_zsL : lDt ≠ zsL := by decide
@[simp] theorem zs_zsL_ne_lDg : zsL ≠ lDg := by decide
@[simp] theorem zs_lDg_ne_zsL : lDg ≠ zsL := by decide
@[simp] theorem zs_zsL_ne_lDi : zsL ≠ lDi := by decide
@[simp] theorem zs_lDi_ne_zsL : lDi ≠ zsL := by decide
@[simp] theorem zs_zsL_ne_lRp : zsL ≠ lRp := by decide
@[simp] theorem zs_lRp_ne_zsL : lRp ≠ zsL := by decide
@[simp] theorem zs_zsL_ne_lRn : zsL ≠ lRn := by decide
@[simp] theorem zs_lRn_ne_zsL : lRn ≠ zsL := by decide
@[simp] theorem zs_zsL_ne_lFll : zsL ≠ lFll := by decide
@[simp] theorem zs_lFll_ne_zsL : lFll ≠ zsL := by decide
@[simp] theorem zs_zsL_ne_lDir : zsL ≠ lDir := by decide
@[simp] theorem zs_lDir_ne_zsL : lDir ≠ zsL := by decide
@[simp] theorem zs_zsL_ne_lKb : zsL ≠ lKb := by decide
@[simp] theorem zs_lKb_ne_zsL : lKb ≠ zsL := by decide
@[simp] theorem zs_zsUs_ne_zsU : zsUs ≠ zsU := by decide
@[simp] theorem zs_zsUs_ne_zsK : zsUs ≠ zsK := by decide
@[simp] theorem zs_zsUs_ne_zsL : zsUs ≠ zsL := by decide
@[simp] theorem zs_zsUs_ne_zsA : zsUs ≠ zsA := by decide
@[simp] theorem zs_zsUs_ne_zsB : zsUs ≠ zsB := by decide
@[simp] theorem zs_zsUs_ne_zsX : zsUs ≠ zsX := by decide
@[simp] theorem zs_zsUs_ne_zsY : zsUs ≠ zsY := by decide
@[simp] theorem zs_zsUs_ne_zsN : zsUs ≠ zsN := by decide
@[simp] theorem zs_zsUs_ne_lFl : zsUs ≠ lFl := by decide
@[simp] theorem zs_lFl_ne_zsUs : lFl ≠ zsUs := by decide
@[simp] theorem zs_zsUs_ne_lDh : zsUs ≠ lDh := by decide
@[simp] theorem zs_lDh_ne_zsUs : lDh ≠ zsUs := by decide
@[simp] theorem zs_zsUs_ne_lDt : zsUs ≠ lDt := by decide
@[simp] theorem zs_lDt_ne_zsUs : lDt ≠ zsUs := by decide
@[simp] theorem zs_zsUs_ne_lDg : zsUs ≠ lDg := by decide
@[simp] theorem zs_lDg_ne_zsUs : lDg ≠ zsUs := by decide
@[simp] theorem zs_zsUs_ne_lDi : zsUs ≠ lDi := by decide
@[simp] theorem zs_lDi_ne_zsUs : lDi ≠ zsUs := by decide
@[simp] theorem zs_zsUs_ne_lRp : zsUs ≠ lRp := by decide
@[simp] theorem zs_lRp_ne_zsUs : lRp ≠ zsUs := by decide
@[simp] theorem zs_zsUs_ne_lRn : zsUs ≠ lRn := by decide
@[simp] theorem zs_lRn_ne_zsUs : lRn ≠ zsUs := by decide
@[simp] theorem zs_zsUs_ne_lFll : zsUs ≠ lFll := by decide
@[simp] theorem zs_lFll_ne_zsUs : lFll ≠ zsUs := by decide
@[simp] theorem zs_zsUs_ne_lDir : zsUs ≠ lDir := by decide
@[simp] theorem zs_lDir_ne_zsUs : lDir ≠ zsUs := by decide
@[simp] theorem zs_zsUs_ne_lKb : zsUs ≠ lKb := by decide
@[simp] theorem zs_lKb_ne_zsUs : lKb ≠ zsUs := by decide
@[simp] theorem zs_zsA_ne_zsU : zsA ≠ zsU := by decide
@[simp] theorem zs_zsA_ne_zsK : zsA ≠ zsK := by decide
@[simp] theorem zs_zsA_ne_zsL : zsA ≠ zsL := by decide
@[simp] theorem zs_zsA_ne_zsUs : zsA ≠ zsUs := by decide
@[simp] theorem zs_zsA_ne_zsB : zsA ≠ zsB := by decide
@[simp] theorem zs_zsA_ne_zsX : zsA ≠ zsX := by decide
@[simp] theorem zs_zsA_ne_zsY : zsA ≠ zsY := by decide
@[simp] theorem zs_zsA_ne_zsN : zsA ≠ zsN := by decide
@[simp] theorem zs_zsA_ne_lFl : zsA ≠ lFl := by decide
@[simp] theorem zs_lFl_ne_zsA : lFl ≠ zsA := by decide
@[simp] theorem zs_zsA_ne_lDh : zsA ≠ lDh := by decide
@[simp] theorem zs_lDh_ne_zsA : lDh ≠ zsA := by decide
@[simp] theorem zs_zsA_ne_lDt : zsA ≠ lDt := by decide
@[simp] theorem zs_lDt_ne_zsA : lDt ≠ zsA := by decide
@[simp] theorem zs_zsA_ne_lDg : zsA ≠ lDg := by decide
@[simp] theorem zs_lDg_ne_zsA : lDg ≠ zsA := by decide
@[simp] theorem zs_zsA_ne_lDi : zsA ≠ lDi := by decide
@[simp] theorem zs_lDi_ne_zsA : lDi ≠ zsA := by decide
@[simp] theorem zs_zsA_ne_lRp : zsA ≠ lRp := by decide
@[simp] theorem zs_lRp_ne_zsA : lRp ≠ zsA := by decide
@[simp] theorem zs_zsA_ne_lRn : zsA ≠ lRn := by decide
@[simp] theorem zs_lRn_ne_zsA : lRn ≠ zsA := by decide
@[simp] theorem zs_zsA_ne_lFll : zsA ≠ lFll := by decide
@[simp] theorem zs_lFll_ne_zsA : lFll ≠ zsA := by decide
@[simp] theorem zs_zsA_ne_lDir : zsA ≠ lDir := by decide
@[simp] theorem zs_lDir_ne_zsA : lDir ≠ zsA := by decide
@[simp] theorem zs_zsA_ne_lKb : zsA ≠ lKb := by decide
@[simp] theorem zs_lKb_ne_zsA : lKb ≠ zsA := by decide
@[simp] theorem zs_zsB_ne_zsU : zsB ≠ zsU := by decide
@[simp] theorem zs_zsB_ne_zsK : zsB ≠ zsK := by decide
@[simp] theorem zs_zsB_ne_zsL : zsB ≠ zsL := by decide
@[simp] theorem zs_zsB_ne_zsUs : zsB ≠ zsUs := by decide
@[simp] theorem zs_zsB_ne_zsA : zsB ≠ zsA := by decide
@[simp] theorem zs_zsB_ne_zsX : zsB ≠ zsX := by decide
@[simp] theorem zs_zsB_ne_zsY : zsB ≠ zsY := by decide
@[simp] theorem zs_zsB_ne_zsN : zsB ≠ zsN := by decide
@[simp] theorem zs_zsB_ne_lFl : zsB ≠ lFl := by decide
@[simp] theorem zs_lFl_ne_zsB : lFl ≠ zsB := by decide
@[simp] theorem zs_zsB_ne_lDh : zsB ≠ lDh := by decide
@[simp] theorem zs_lDh_ne_zsB : lDh ≠ zsB := by decide
@[simp] theorem zs_zsB_ne_lDt : zsB ≠ lDt := by decide
@[simp] theorem zs_lDt_ne_zsB : lDt ≠ zsB := by decide
@[simp] theorem zs_zsB_ne_lDg : zsB ≠ lDg := by decide
@[simp] theorem zs_lDg_ne_zsB : lDg ≠ zsB := by decide
@[simp] theorem zs_zsB_ne_lDi : zsB ≠ lDi := by decide
@[simp] theorem zs_lDi_ne_zsB : lDi ≠ zsB := by decide
@[simp] theorem zs_zsB_ne_lRp : zsB ≠ lRp := by decide
@[simp] theorem zs_lRp_ne_zsB : lRp ≠ zsB := by decide
@[simp] theorem zs_zsB_ne_lRn : zsB ≠ lRn := by decide
@[simp] theorem zs_lRn_ne_zsB : lRn ≠ zsB := by decide
@[simp] theorem zs_zsB_ne_lFll : zsB ≠ lFll := by decide
@[simp] theorem zs_lFll_ne_zsB : lFll ≠ zsB := by decide
@[simp] theorem zs_zsB_ne_lDir : zsB ≠ lDir := by decide
@[simp] theorem zs_lDir_ne_zsB : lDir ≠ zsB := by decide
@[simp] theorem zs_zsB_ne_lKb : zsB ≠ lKb := by decide
@[simp] theorem zs_lKb_ne_zsB : lKb ≠ zsB := by decide
@[simp] theorem zs_zsX_ne_zsU : zsX ≠ zsU := by decide
@[simp] theorem zs_zsX_ne_zsK : zsX ≠ zsK := by decide
@[simp] theorem zs_zsX_ne_zsL : zsX ≠ zsL := by decide
@[simp] theorem zs_zsX_ne_zsUs : zsX ≠ zsUs := by decide
@[simp] theorem zs_zsX_ne_zsA : zsX ≠ zsA := by decide
@[simp] theorem zs_zsX_ne_zsB : zsX ≠ zsB := by decide
@[simp] theorem zs_zsX_ne_zsY : zsX ≠ zsY := by decide
@[simp] theorem zs_zsX_ne_zsN : zsX ≠ zsN := by decide
@[simp] theorem zs_zsX_ne_lFl : zsX ≠ lFl := by decide
@[simp] theorem zs_lFl_ne_zsX : lFl ≠ zsX := by decide
@[simp] theorem zs_zsX_ne_lDh : zsX ≠ lDh := by decide
@[simp] theorem zs_lDh_ne_zsX : lDh ≠ zsX := by decide
@[simp] theorem zs_zsX_ne_lDt : zsX ≠ lDt := by decide
@[simp] theorem zs_lDt_ne_zsX : lDt ≠ zsX := by decide
@[simp] theorem zs_zsX_ne_lDg : zsX ≠ lDg := by decide
@[simp] theorem zs_lDg_ne_zsX : lDg ≠ zsX := by decide
@[simp] theorem zs_zsX_ne_lDi : zsX ≠ lDi := by decide
@[simp] theorem zs_lDi_ne_zsX : lDi ≠ zsX := by decide
@[simp] theorem zs_zsX_ne_lRp : zsX ≠ lRp := by decide
@[simp] theorem zs_lRp_ne_zsX : lRp ≠ zsX := by decide
@[simp] theorem zs_zsX_ne_lRn : zsX ≠ lRn := by decide
@[simp] theorem zs_lRn_ne_zsX : lRn ≠ zsX := by decide
@[simp] theorem zs_zsX_ne_lFll : zsX ≠ lFll := by decide
@[simp] theorem zs_lFll_ne_zsX : lFll ≠ zsX := by decide
@[simp] theorem zs_zsX_ne_lDir : zsX ≠ lDir := by decide
@[simp] theorem zs_lDir_ne_zsX : lDir ≠ zsX := by decide
@[simp] theorem zs_zsX_ne_lKb : zsX ≠ lKb := by decide
@[simp] theorem zs_lKb_ne_zsX : lKb ≠ zsX := by decide
@[simp] theorem zs_zsY_ne_zsU : zsY ≠ zsU := by decide
@[simp] theorem zs_zsY_ne_zsK : zsY ≠ zsK := by decide
@[simp] theorem zs_zsY_ne_zsL : zsY ≠ zsL := by decide
@[simp] theorem zs_zsY_ne_zsUs : zsY ≠ zsUs := by decide
@[simp] theorem zs_zsY_ne_zsA : zsY ≠ zsA := by decide
@[simp] theorem zs_zsY_ne_zsB : zsY ≠ zsB := by decide
@[simp] theorem zs_zsY_ne_zsX : zsY ≠ zsX := by decide
@[simp] theorem zs_zsY_ne_zsN : zsY ≠ zsN := by decide
@[simp] theorem zs_zsY_ne_lFl : zsY ≠ lFl := by decide
@[simp] theorem zs_lFl_ne_zsY : lFl ≠ zsY := by decide
@[simp] theorem zs_zsY_ne_lDh : zsY ≠ lDh := by decide
@[simp] theorem zs_lDh_ne_zsY : lDh ≠ zsY := by decide
@[simp] theorem zs_zsY_ne_lDt : zsY ≠ lDt := by decide
@[simp] theorem zs_lDt_ne_zsY : lDt ≠ zsY := by decide
@[simp] theorem zs_zsY_ne_lDg : zsY ≠ lDg := by decide
@[simp] theorem zs_lDg_ne_zsY : lDg ≠ zsY := by decide
@[simp] theorem zs_zsY_ne_lDi : zsY ≠ lDi := by decide
@[simp] theorem zs_lDi_ne_zsY : lDi ≠ zsY := by decide
@[simp] theorem zs_zsY_ne_lRp : zsY ≠ lRp := by decide
@[simp] theorem zs_lRp_ne_zsY : lRp ≠ zsY := by decide
@[simp] theorem zs_zsY_ne_lRn : zsY ≠ lRn := by decide
@[simp] theorem zs_lRn_ne_zsY : lRn ≠ zsY := by decide
@[simp] theorem zs_zsY_ne_lFll : zsY ≠ lFll := by decide
@[simp] theorem zs_lFll_ne_zsY : lFll ≠ zsY := by decide
@[simp] theorem zs_zsY_ne_lDir : zsY ≠ lDir := by decide
@[simp] theorem zs_lDir_ne_zsY : lDir ≠ zsY := by decide
@[simp] theorem zs_zsY_ne_lKb : zsY ≠ lKb := by decide
@[simp] theorem zs_lKb_ne_zsY : lKb ≠ zsY := by decide
@[simp] theorem zs_zsN_ne_zsU : zsN ≠ zsU := by decide
@[simp] theorem zs_zsN_ne_zsK : zsN ≠ zsK := by decide
@[simp] theorem zs_zsN_ne_zsL : zsN ≠ zsL := by decide
@[simp] theorem zs_zsN_ne_zsUs : zsN ≠ zsUs := by decide
@[simp] theorem zs_zsN_ne_zsA : zsN ≠ zsA := by decide
@[simp] theorem zs_zsN_ne_zsB : zsN ≠ zsB := by decide
@[simp] theorem zs_zsN_ne_zsX : zsN ≠ zsX := by decide
@[simp] theorem zs_zsN_ne_zsY : zsN ≠ zsY := by decide
@[simp] theorem zs_zsN_ne_lFl : zsN ≠ lFl := by decide
@[simp] theorem zs_lFl_ne_zsN : lFl ≠ zsN := by decide
@[simp] theorem zs_zsN_ne_lDh : zsN ≠ lDh := by decide
@[simp] theorem zs_lDh_ne_zsN : lDh ≠ zsN := by decide
@[simp] theorem zs_zsN_ne_lDt : zsN ≠ lDt := by decide
@[simp] theorem zs_lDt_ne_zsN : lDt ≠ zsN := by decide
@[simp] theorem zs_zsN_ne_lDg : zsN ≠ lDg := by decide
@[simp] theorem zs_lDg_ne_zsN : lDg ≠ zsN := by decide
@[simp] theorem zs_zsN_ne_lDi : zsN ≠ lDi := by decide
@[simp] theorem zs_lDi_ne_zsN : lDi ≠ zsN := by decide
@[simp] theorem zs_zsN_ne_lRp : zsN ≠ lRp := by decide
@[simp] theorem zs_lRp_ne_zsN : lRp ≠ zsN := by decide
@[simp] theorem zs_zsN_ne_lRn : zsN ≠ lRn := by decide
@[simp] theorem zs_lRn_ne_zsN : lRn ≠ zsN := by decide
@[simp] theorem zs_zsN_ne_lFll : zsN ≠ lFll := by decide
@[simp] theorem zs_lFll_ne_zsN : lFll ≠ zsN := by decide
@[simp] theorem zs_zsN_ne_lDir : zsN ≠ lDir := by decide
@[simp] theorem zs_lDir_ne_zsN : lDir ≠ zsN := by decide
@[simp] theorem zs_zsN_ne_lKb : zsN ≠ lKb := by decide
@[simp] theorem zs_lKb_ne_zsN : lKb ≠ zsN := by decide

def zsLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, zsA, zsB, zsX, zsY, zsN]
def zsParams : List MlS := [zsU, zsK, zsL, zsUs]

def zsBody : ProgHOL 64 := prologue zsLocals
  (.seq (.assign .local lFl (vv lFll)) (.seq (.assign .local lDh (vv zsU)) (.seq lViewP
  (.ite (.cmp .equal (vv lDg) (.const 0)) (.return (.const 0))
  (.ite (.cmp .equal (vv lDg) (.const 1)) (.return (.const 1))
  (.ite (.cmp .equal (vv lDg) (.const 4))
    (.seq (.assign .local zsN (.load .one (vv lRp)))
    (.seq (.call (some (some (.local, zsX), none)) fZp [vv zsN, vv zsK, vv zsL, vv zsUs, .const 0]) (.return (vv zsX))))
  (.seq (.assign .local zsA (.load .one (vv lRp)))
  (.seq (.assign .local zsB (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (.call (some (some (.local, zsY), none)) fZs [vv zsB, vv zsK, vv zsL, vv zsUs])
  (.ite (.cmp .equal (vv lDg) (.const 3)) (.return (vv zsY))
  (.ite (vv zsY) (.return (.const 1))
  (.seq (.call (some (some (.local, zsX), none)) fZs [vv zsA, vv zsK, vv zsL, vv zsUs]) (.return (vv zsX))))))))))))))


section
variable {σ : Type}

theorem zs_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ zsLocals → (ctxEnv C ++ zsParams.zip vals).get x = none :=
  Knot.params_none C zsLocals zsParams vals (by decide) (by decide)

theorem zs_spec (C : Ctx) (hcf : C.code.lookup fZs = some (zsParams.map (fun p => (p, ShapeHOL.one)), zsBody, .one))
    (hcp : C.code.lookup fZp = some (zpParams.map (fun p => (p, ShapeHOL.one)), zpBody, .one))
    (hcn : C.code.lookup NEq.fNeq = some ([(NEq.pNa, .one), (NEq.pNb, .one)], NEq.neqBody, .one))
    (hcz : C.code.lookup fNz0 = some ([(nzU, ShapeHOL.one)], nzBody, .one)) (s : AState)
    (hwf : LStoreWF s.store.ls)
    (khs : List NIdx) (ks : List ConLeche.Name) (ok : Nat)
    (hks : ∀ j (hj : j < khs.length), C.EH[ok + j]? = some (Enc.idxW khs[j])) (hkl : ks.length = khs.length)
    (hkd : ∀ j (hj : j < khs.length), ∃ f, denoteNAux s.store.ns f khs[j] = some (ks[j]'(by omega)))
    (hklen : khs.length < 2 ^ 60)
    (us : LsIdx) (uh : List LIdx) (vs : List ConLeche.Level) (huv : s.store.lss.view us = some uh)
    (hvl : vs.length = uh.length) (hvd : ∀ j (hj : j < uh.length), denoteL s.store.ls uh[j] = some (vs[j]'(by omega))) :
    ∀ (l : ConLeche.Level) (u : LIdx), denoteL s.store.ls u = some l →
      SpecR (σ := σ) (Pre C s (zsParams.zip [Enc.idxW u, ecell C ok, BitVec.ofNat 64 khs.length, Enc.idxW us])) zsBody s
        (pure (nzS ks vs l) : AM Bool) (PostBS C s) := by
  intro l
  induction l with
  | zero => ?_ | succ p ih => ?_ | max p q ihp ihq => ?_ | imax p q ihp ihq => ?_ | param nm => ?_
  all_goals
    intro u hd
    refine specR_prologue (postBS_locals C s) (zs_none C _) ?_
    refine specR_assignI lFl (vv lFll) C.FLl (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv zsU) (Enc.idxW u) (by decide) (by simp +decide [Env.get, zsParams, ctxEnv]) ?_
    refine specR_lviewPI u (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
      (fun v P hv _ _ => ?_)
  -- zero
  · rcases v with _ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨n⟩
    · refine specR_ifI _ 1 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      exact specR_returnI _ (boolW false) (by simp [boolW]; rfl)
        (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    all_goals first
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_succ_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_max_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_imax_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_param_inv hwf hv hd; cases h)
  -- succ
  · rcases v with _ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨n⟩
    rotate_left
    · refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
        (fun _ => ?_)
      refine specR_ifI _ 1 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      exact specR_returnI _ (boolW true) (by simp [boolW]; rfl)
        (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    all_goals first
      | (have h := ConRon.Bridge.denoteL_zero_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_max_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_imax_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_param_inv hwf hv hd; cases h)
  -- max
  · rcases v with _ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨n⟩
    rotate_left 2
    · obtain ⟨p', q', he, hda, hdb⟩ := ConRon.Bridge.denoteL_max_inv hwf hv hd
      cases he
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_loadI' zsA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp) (by simp)
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' zsB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      refine specR_callPure zsY fZs zsParams [vv zsB, vv zsK, vv zsL, vv zsUs] zsBody
        [Enc.idxW _, ecell C ok, BitVec.ofNat 64 khs.length, Enc.idxW us] (nzS ks vs _) (by decide) rfl (by decide) hcf
        ⟨by simp, by simp +decide [Env.get, zsParams, ctxEnv], by simp +decide [Env.get, zsParams, ctxEnv],
          by simp +decide [Env.get, zsParams, ctxEnv], trivial⟩ (PostBS C s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
        (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu zsParams _ rfl hlk) (ihq _ hdb))
        (fun w H1 hp1 ⟨eH, hw⟩ => ?_)
      subst eH hw
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      cases hq : nzS ks vs q
      · refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
        refine specR_callPure zsX fZs zsParams [vv zsA, vv zsK, vv zsL, vv zsUs] zsBody
          [Enc.idxW _, ecell C ok, BitVec.ofNat 64 khs.length, Enc.idxW us] (nzS ks vs _) (by decide) rfl (by decide) hcf
          ⟨by simp, by simp +decide [Env.get, zsParams, ctxEnv], by simp +decide [Env.get, zsParams, ctxEnv],
            by simp +decide [Env.get, zsParams, ctxEnv], trivial⟩ (PostBS C s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
          (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
          (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu zsParams _ rfl hlk) (ihp _ hda))
          (fun w H2 hp2 ⟨eH2, hw⟩ => ?_)
        subst eH2 hw
        exact specR_returnI _ (boolW (nzS ks vs p)) (by simp)
          (fun t ht => ⟨rfl, by simp [nzS, hq], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
        exact specR_returnI _ (boolW true) (by simp [boolW]; rfl)
          (fun t ht => ⟨rfl, by simp [nzS, hq], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    all_goals first
      | (have h := ConRon.Bridge.denoteL_zero_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_succ_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_imax_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_param_inv hwf hv hd; cases h)
  -- imax
  · rcases v with _ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨n⟩
    rotate_left 3
    · obtain ⟨p', q', he, hda, hdb⟩ := ConRon.Bridge.denoteL_imax_inv hwf hv hd
      cases he
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_loadI' zsA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW a) (by decide) (by simp) (by simp)
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem0 P (Enc.idxW a) [Enc.idxW b] []) ?_
      refine specR_loadI' zsB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encLView, Enc.encBinL] using wordsAt_mem1 P (Enc.idxW a) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      refine specR_callPure zsY fZs zsParams [vv zsB, vv zsK, vv zsL, vv zsUs] zsBody
        [Enc.idxW _, ecell C ok, BitVec.ofNat 64 khs.length, Enc.idxW us] (nzS ks vs _) (by decide) rfl (by decide) hcf
        ⟨by simp, by simp +decide [Env.get, zsParams, ctxEnv], by simp +decide [Env.get, zsParams, ctxEnv],
          by simp +decide [Env.get, zsParams, ctxEnv], trivial⟩ (PostBS C s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
        (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu zsParams _ rfl hlk) (ihq _ hdb))
        (fun w H1 hp1 ⟨eH, hw⟩ => ?_)
      subst eH hw
      refine specR_ifI _ 1 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ (boolW (nzS ks vs q)) (by simp)
        (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    all_goals first
      | (have h := ConRon.Bridge.denoteL_zero_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_succ_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_max_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_param_inv hwf hv hd; cases h)
  -- param
  · rcases v with _ | ⟨a⟩ | ⟨a, b⟩ | ⟨a, b⟩ | ⟨n⟩
    rotate_left 4
    · obtain ⟨nm', he, hdn⟩ := ConRon.Bridge.denoteL_param_inv hwf hv hd
      cases he
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp [sev, LNodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_loadI' zsN (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW n) (by decide) (by simp) (by simp)
        (by simpa [encLView, Enc.encParam] using wordsAt_mem0 P (Enc.idxW n) [] []) ?_
      refine specR_dropM ?_
      refine specR_callPure zsX fZp zpParams [vv zsN, vv zsK, vv zsL, vv zsUs, .const 0] zpBody
        [Enc.idxW n, ecell C ok, BitVec.ofNat 64 khs.length, Enc.idxW us, BitVec.ofNat 64 0]
        (nz (ConLeche.Level.subst.go (ks.drop 0) (vs.drop 0) nm)) (by decide) rfl (by decide) hcp
        ⟨by simp, by simp +decide [Env.get, zsParams, ctxEnv], by simp +decide [Env.get, zsParams, ctxEnv],
          by simp +decide [Env.get, zsParams, ctxEnv], rfl, trivial⟩
        (PostBS C s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
        (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu zpParams _ rfl hlk)
          (zp_spec C hcp hcn hcz s hwf khs ks ok hks hkl hkd hklen us uh vs huv hvl hvd n nm _ hdn _ 0 rfl
            (Nat.zero_le _)))
        (fun w H1 hp1 ⟨eH, hw⟩ => ?_)
      subst eH hw
      exact specR_returnI _ (boolW (nz (ConLeche.Level.subst.go (ks.drop 0) (vs.drop 0) nm))) (by simp)
        (fun t ht => ⟨rfl, by simp [nzS], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    all_goals first
      | (have h := ConRon.Bridge.denoteL_zero_inv hwf hv hd; cases h)
      | (obtain ⟨_, h, _⟩ := ConRon.Bridge.denoteL_succ_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_max_inv hwf hv hd; cases h)
      | (obtain ⟨_, _, h, _⟩ := ConRon.Bridge.denoteL_imax_inv hwf hv hd; cases h)
end

end ConPanqueque.T.WC
