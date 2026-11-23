import ConPanqueque.T.Core.PropPW
import ConPanqueque.T.Core.FormerNZ
import ConPanqueque.T.Core.LazyDelta
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `substPWAt`: a datum at a use's universe arguments

A nonempty `ifAllZero` datum is substituted (`sb`), after the twin's cached readbacks of the parameter names and the
arguments (`readNamesM`, `readLevelsM`); any other datum is its own answer. The read caches change (`RdStep`).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc
open ConLeche (Level Name)

def saK := ofString "psa_sak"
def saL := ofString "psa_sal"
def saU := ofString "psa_sau"
def saW := ofString "psa_saw"
def saN := ofString "psa_san"
def saA := ofString "psa_saa"
def saR := ofString "psa_sar"
def fSa := ofString "substPWAt"

@[simp] theorem psa_saK_ne_saL : saK ≠ saL := by decide
@[simp] theorem psa_saK_ne_saU : saK ≠ saU := by decide
@[simp] theorem psa_saK_ne_saW : saK ≠ saW := by decide
@[simp] theorem psa_saK_ne_saN : saK ≠ saN := by decide
@[simp] theorem psa_saK_ne_saA : saK ≠ saA := by decide
@[simp] theorem psa_saK_ne_saR : saK ≠ saR := by decide
@[simp] theorem psa_saK_ne_lFl : saK ≠ lFl := by decide
@[simp] theorem psa_lFl_ne_saK : lFl ≠ saK := by decide
@[simp] theorem psa_saK_ne_lDh : saK ≠ lDh := by decide
@[simp] theorem psa_lDh_ne_saK : lDh ≠ saK := by decide
@[simp] theorem psa_saK_ne_lDt : saK ≠ lDt := by decide
@[simp] theorem psa_lDt_ne_saK : lDt ≠ saK := by decide
@[simp] theorem psa_saK_ne_lDg : saK ≠ lDg := by decide
@[simp] theorem psa_lDg_ne_saK : lDg ≠ saK := by decide
@[simp] theorem psa_saK_ne_lDi : saK ≠ lDi := by decide
@[simp] theorem psa_lDi_ne_saK : lDi ≠ saK := by decide
@[simp] theorem psa_saK_ne_lRp : saK ≠ lRp := by decide
@[simp] theorem psa_lRp_ne_saK : lRp ≠ saK := by decide
@[simp] theorem psa_saK_ne_lRn : saK ≠ lRn := by decide
@[simp] theorem psa_lRn_ne_saK : lRn ≠ saK := by decide
@[simp] theorem psa_saK_ne_lFle : saK ≠ lFle := by decide
@[simp] theorem psa_lFle_ne_saK : lFle ≠ saK := by decide
@[simp] theorem psa_saK_ne_lKb : saK ≠ lKb := by decide
@[simp] theorem psa_lKb_ne_saK : lKb ≠ saK := by decide
@[simp] theorem psa_saK_ne_lDir : saK ≠ lDir := by decide
@[simp] theorem psa_lDir_ne_saK : lDir ≠ saK := by decide
@[simp] theorem psa_saK_ne_lFln : saK ≠ lFln := by decide
@[simp] theorem psa_lFln_ne_saK : lFln ≠ saK := by decide
@[simp] theorem psa_saK_ne_lFll : saK ≠ lFll := by decide
@[simp] theorem psa_lFll_ne_saK : lFll ≠ saK := by decide
@[simp] theorem psa_saK_ne_lFls : saK ≠ lFls := by decide
@[simp] theorem psa_lFls_ne_saK : lFls ≠ saK := by decide
@[simp] theorem psa_saK_ne_kFu : saK ≠ kFu := by decide
@[simp] theorem psa_kFu_ne_saK : kFu ≠ saK := by decide
@[simp] theorem psa_saK_ne_kD : saK ≠ kD := by decide
@[simp] theorem psa_kD_ne_saK : kD ≠ saK := by decide
@[simp] theorem psa_saL_ne_saK : saL ≠ saK := by decide
@[simp] theorem psa_saL_ne_saU : saL ≠ saU := by decide
@[simp] theorem psa_saL_ne_saW : saL ≠ saW := by decide
@[simp] theorem psa_saL_ne_saN : saL ≠ saN := by decide
@[simp] theorem psa_saL_ne_saA : saL ≠ saA := by decide
@[simp] theorem psa_saL_ne_saR : saL ≠ saR := by decide
@[simp] theorem psa_saL_ne_lFl : saL ≠ lFl := by decide
@[simp] theorem psa_lFl_ne_saL : lFl ≠ saL := by decide
@[simp] theorem psa_saL_ne_lDh : saL ≠ lDh := by decide
@[simp] theorem psa_lDh_ne_saL : lDh ≠ saL := by decide
@[simp] theorem psa_saL_ne_lDt : saL ≠ lDt := by decide
@[simp] theorem psa_lDt_ne_saL : lDt ≠ saL := by decide
@[simp] theorem psa_saL_ne_lDg : saL ≠ lDg := by decide
@[simp] theorem psa_lDg_ne_saL : lDg ≠ saL := by decide
@[simp] theorem psa_saL_ne_lDi : saL ≠ lDi := by decide
@[simp] theorem psa_lDi_ne_saL : lDi ≠ saL := by decide
@[simp] theorem psa_saL_ne_lRp : saL ≠ lRp := by decide
@[simp] theorem psa_lRp_ne_saL : lRp ≠ saL := by decide
@[simp] theorem psa_saL_ne_lRn : saL ≠ lRn := by decide
@[simp] theorem psa_lRn_ne_saL : lRn ≠ saL := by decide
@[simp] theorem psa_saL_ne_lFle : saL ≠ lFle := by decide
@[simp] theorem psa_lFle_ne_saL : lFle ≠ saL := by decide
@[simp] theorem psa_saL_ne_lKb : saL ≠ lKb := by decide
@[simp] theorem psa_lKb_ne_saL : lKb ≠ saL := by decide
@[simp] theorem psa_saL_ne_lDir : saL ≠ lDir := by decide
@[simp] theorem psa_lDir_ne_saL : lDir ≠ saL := by decide
@[simp] theorem psa_saL_ne_lFln : saL ≠ lFln := by decide
@[simp] theorem psa_lFln_ne_saL : lFln ≠ saL := by decide
@[simp] theorem psa_saL_ne_lFll : saL ≠ lFll := by decide
@[simp] theorem psa_lFll_ne_saL : lFll ≠ saL := by decide
@[simp] theorem psa_saL_ne_lFls : saL ≠ lFls := by decide
@[simp] theorem psa_lFls_ne_saL : lFls ≠ saL := by decide
@[simp] theorem psa_saL_ne_kFu : saL ≠ kFu := by decide
@[simp] theorem psa_kFu_ne_saL : kFu ≠ saL := by decide
@[simp] theorem psa_saL_ne_kD : saL ≠ kD := by decide
@[simp] theorem psa_kD_ne_saL : kD ≠ saL := by decide
@[simp] theorem psa_saU_ne_saK : saU ≠ saK := by decide
@[simp] theorem psa_saU_ne_saL : saU ≠ saL := by decide
@[simp] theorem psa_saU_ne_saW : saU ≠ saW := by decide
@[simp] theorem psa_saU_ne_saN : saU ≠ saN := by decide
@[simp] theorem psa_saU_ne_saA : saU ≠ saA := by decide
@[simp] theorem psa_saU_ne_saR : saU ≠ saR := by decide
@[simp] theorem psa_saU_ne_lFl : saU ≠ lFl := by decide
@[simp] theorem psa_lFl_ne_saU : lFl ≠ saU := by decide
@[simp] theorem psa_saU_ne_lDh : saU ≠ lDh := by decide
@[simp] theorem psa_lDh_ne_saU : lDh ≠ saU := by decide
@[simp] theorem psa_saU_ne_lDt : saU ≠ lDt := by decide
@[simp] theorem psa_lDt_ne_saU : lDt ≠ saU := by decide
@[simp] theorem psa_saU_ne_lDg : saU ≠ lDg := by decide
@[simp] theorem psa_lDg_ne_saU : lDg ≠ saU := by decide
@[simp] theorem psa_saU_ne_lDi : saU ≠ lDi := by decide
@[simp] theorem psa_lDi_ne_saU : lDi ≠ saU := by decide
@[simp] theorem psa_saU_ne_lRp : saU ≠ lRp := by decide
@[simp] theorem psa_lRp_ne_saU : lRp ≠ saU := by decide
@[simp] theorem psa_saU_ne_lRn : saU ≠ lRn := by decide
@[simp] theorem psa_lRn_ne_saU : lRn ≠ saU := by decide
@[simp] theorem psa_saU_ne_lFle : saU ≠ lFle := by decide
@[simp] theorem psa_lFle_ne_saU : lFle ≠ saU := by decide
@[simp] theorem psa_saU_ne_lKb : saU ≠ lKb := by decide
@[simp] theorem psa_lKb_ne_saU : lKb ≠ saU := by decide
@[simp] theorem psa_saU_ne_lDir : saU ≠ lDir := by decide
@[simp] theorem psa_lDir_ne_saU : lDir ≠ saU := by decide
@[simp] theorem psa_saU_ne_lFln : saU ≠ lFln := by decide
@[simp] theorem psa_lFln_ne_saU : lFln ≠ saU := by decide
@[simp] theorem psa_saU_ne_lFll : saU ≠ lFll := by decide
@[simp] theorem psa_lFll_ne_saU : lFll ≠ saU := by decide
@[simp] theorem psa_saU_ne_lFls : saU ≠ lFls := by decide
@[simp] theorem psa_lFls_ne_saU : lFls ≠ saU := by decide
@[simp] theorem psa_saU_ne_kFu : saU ≠ kFu := by decide
@[simp] theorem psa_kFu_ne_saU : kFu ≠ saU := by decide
@[simp] theorem psa_saU_ne_kD : saU ≠ kD := by decide
@[simp] theorem psa_kD_ne_saU : kD ≠ saU := by decide
@[simp] theorem psa_saW_ne_saK : saW ≠ saK := by decide
@[simp] theorem psa_saW_ne_saL : saW ≠ saL := by decide
@[simp] theorem psa_saW_ne_saU : saW ≠ saU := by decide
@[simp] theorem psa_saW_ne_saN : saW ≠ saN := by decide
@[simp] theorem psa_saW_ne_saA : saW ≠ saA := by decide
@[simp] theorem psa_saW_ne_saR : saW ≠ saR := by decide
@[simp] theorem psa_saW_ne_lFl : saW ≠ lFl := by decide
@[simp] theorem psa_lFl_ne_saW : lFl ≠ saW := by decide
@[simp] theorem psa_saW_ne_lDh : saW ≠ lDh := by decide
@[simp] theorem psa_lDh_ne_saW : lDh ≠ saW := by decide
@[simp] theorem psa_saW_ne_lDt : saW ≠ lDt := by decide
@[simp] theorem psa_lDt_ne_saW : lDt ≠ saW := by decide
@[simp] theorem psa_saW_ne_lDg : saW ≠ lDg := by decide
@[simp] theorem psa_lDg_ne_saW : lDg ≠ saW := by decide
@[simp] theorem psa_saW_ne_lDi : saW ≠ lDi := by decide
@[simp] theorem psa_lDi_ne_saW : lDi ≠ saW := by decide
@[simp] theorem psa_saW_ne_lRp : saW ≠ lRp := by decide
@[simp] theorem psa_lRp_ne_saW : lRp ≠ saW := by decide
@[simp] theorem psa_saW_ne_lRn : saW ≠ lRn := by decide
@[simp] theorem psa_lRn_ne_saW : lRn ≠ saW := by decide
@[simp] theorem psa_saW_ne_lFle : saW ≠ lFle := by decide
@[simp] theorem psa_lFle_ne_saW : lFle ≠ saW := by decide
@[simp] theorem psa_saW_ne_lKb : saW ≠ lKb := by decide
@[simp] theorem psa_lKb_ne_saW : lKb ≠ saW := by decide
@[simp] theorem psa_saW_ne_lDir : saW ≠ lDir := by decide
@[simp] theorem psa_lDir_ne_saW : lDir ≠ saW := by decide
@[simp] theorem psa_saW_ne_lFln : saW ≠ lFln := by decide
@[simp] theorem psa_lFln_ne_saW : lFln ≠ saW := by decide
@[simp] theorem psa_saW_ne_lFll : saW ≠ lFll := by decide
@[simp] theorem psa_lFll_ne_saW : lFll ≠ saW := by decide
@[simp] theorem psa_saW_ne_lFls : saW ≠ lFls := by decide
@[simp] theorem psa_lFls_ne_saW : lFls ≠ saW := by decide
@[simp] theorem psa_saW_ne_kFu : saW ≠ kFu := by decide
@[simp] theorem psa_kFu_ne_saW : kFu ≠ saW := by decide
@[simp] theorem psa_saW_ne_kD : saW ≠ kD := by decide
@[simp] theorem psa_kD_ne_saW : kD ≠ saW := by decide
@[simp] theorem psa_saN_ne_saK : saN ≠ saK := by decide
@[simp] theorem psa_saN_ne_saL : saN ≠ saL := by decide
@[simp] theorem psa_saN_ne_saU : saN ≠ saU := by decide
@[simp] theorem psa_saN_ne_saW : saN ≠ saW := by decide
@[simp] theorem psa_saN_ne_saA : saN ≠ saA := by decide
@[simp] theorem psa_saN_ne_saR : saN ≠ saR := by decide
@[simp] theorem psa_saN_ne_lFl : saN ≠ lFl := by decide
@[simp] theorem psa_lFl_ne_saN : lFl ≠ saN := by decide
@[simp] theorem psa_saN_ne_lDh : saN ≠ lDh := by decide
@[simp] theorem psa_lDh_ne_saN : lDh ≠ saN := by decide
@[simp] theorem psa_saN_ne_lDt : saN ≠ lDt := by decide
@[simp] theorem psa_lDt_ne_saN : lDt ≠ saN := by decide
@[simp] theorem psa_saN_ne_lDg : saN ≠ lDg := by decide
@[simp] theorem psa_lDg_ne_saN : lDg ≠ saN := by decide
@[simp] theorem psa_saN_ne_lDi : saN ≠ lDi := by decide
@[simp] theorem psa_lDi_ne_saN : lDi ≠ saN := by decide
@[simp] theorem psa_saN_ne_lRp : saN ≠ lRp := by decide
@[simp] theorem psa_lRp_ne_saN : lRp ≠ saN := by decide
@[simp] theorem psa_saN_ne_lRn : saN ≠ lRn := by decide
@[simp] theorem psa_lRn_ne_saN : lRn ≠ saN := by decide
@[simp] theorem psa_saN_ne_lFle : saN ≠ lFle := by decide
@[simp] theorem psa_lFle_ne_saN : lFle ≠ saN := by decide
@[simp] theorem psa_saN_ne_lKb : saN ≠ lKb := by decide
@[simp] theorem psa_lKb_ne_saN : lKb ≠ saN := by decide
@[simp] theorem psa_saN_ne_lDir : saN ≠ lDir := by decide
@[simp] theorem psa_lDir_ne_saN : lDir ≠ saN := by decide
@[simp] theorem psa_saN_ne_lFln : saN ≠ lFln := by decide
@[simp] theorem psa_lFln_ne_saN : lFln ≠ saN := by decide
@[simp] theorem psa_saN_ne_lFll : saN ≠ lFll := by decide
@[simp] theorem psa_lFll_ne_saN : lFll ≠ saN := by decide
@[simp] theorem psa_saN_ne_lFls : saN ≠ lFls := by decide
@[simp] theorem psa_lFls_ne_saN : lFls ≠ saN := by decide
@[simp] theorem psa_saN_ne_kFu : saN ≠ kFu := by decide
@[simp] theorem psa_kFu_ne_saN : kFu ≠ saN := by decide
@[simp] theorem psa_saN_ne_kD : saN ≠ kD := by decide
@[simp] theorem psa_kD_ne_saN : kD ≠ saN := by decide
@[simp] theorem psa_saA_ne_saK : saA ≠ saK := by decide
@[simp] theorem psa_saA_ne_saL : saA ≠ saL := by decide
@[simp] theorem psa_saA_ne_saU : saA ≠ saU := by decide
@[simp] theorem psa_saA_ne_saW : saA ≠ saW := by decide
@[simp] theorem psa_saA_ne_saN : saA ≠ saN := by decide
@[simp] theorem psa_saA_ne_saR : saA ≠ saR := by decide
@[simp] theorem psa_saA_ne_lFl : saA ≠ lFl := by decide
@[simp] theorem psa_lFl_ne_saA : lFl ≠ saA := by decide
@[simp] theorem psa_saA_ne_lDh : saA ≠ lDh := by decide
@[simp] theorem psa_lDh_ne_saA : lDh ≠ saA := by decide
@[simp] theorem psa_saA_ne_lDt : saA ≠ lDt := by decide
@[simp] theorem psa_lDt_ne_saA : lDt ≠ saA := by decide
@[simp] theorem psa_saA_ne_lDg : saA ≠ lDg := by decide
@[simp] theorem psa_lDg_ne_saA : lDg ≠ saA := by decide
@[simp] theorem psa_saA_ne_lDi : saA ≠ lDi := by decide
@[simp] theorem psa_lDi_ne_saA : lDi ≠ saA := by decide
@[simp] theorem psa_saA_ne_lRp : saA ≠ lRp := by decide
@[simp] theorem psa_lRp_ne_saA : lRp ≠ saA := by decide
@[simp] theorem psa_saA_ne_lRn : saA ≠ lRn := by decide
@[simp] theorem psa_lRn_ne_saA : lRn ≠ saA := by decide
@[simp] theorem psa_saA_ne_lFle : saA ≠ lFle := by decide
@[simp] theorem psa_lFle_ne_saA : lFle ≠ saA := by decide
@[simp] theorem psa_saA_ne_lKb : saA ≠ lKb := by decide
@[simp] theorem psa_lKb_ne_saA : lKb ≠ saA := by decide
@[simp] theorem psa_saA_ne_lDir : saA ≠ lDir := by decide
@[simp] theorem psa_lDir_ne_saA : lDir ≠ saA := by decide
@[simp] theorem psa_saA_ne_lFln : saA ≠ lFln := by decide
@[simp] theorem psa_lFln_ne_saA : lFln ≠ saA := by decide
@[simp] theorem psa_saA_ne_lFll : saA ≠ lFll := by decide
@[simp] theorem psa_lFll_ne_saA : lFll ≠ saA := by decide
@[simp] theorem psa_saA_ne_lFls : saA ≠ lFls := by decide
@[simp] theorem psa_lFls_ne_saA : lFls ≠ saA := by decide
@[simp] theorem psa_saA_ne_kFu : saA ≠ kFu := by decide
@[simp] theorem psa_kFu_ne_saA : kFu ≠ saA := by decide
@[simp] theorem psa_saA_ne_kD : saA ≠ kD := by decide
@[simp] theorem psa_kD_ne_saA : kD ≠ saA := by decide
@[simp] theorem psa_saR_ne_saK : saR ≠ saK := by decide
@[simp] theorem psa_saR_ne_saL : saR ≠ saL := by decide
@[simp] theorem psa_saR_ne_saU : saR ≠ saU := by decide
@[simp] theorem psa_saR_ne_saW : saR ≠ saW := by decide
@[simp] theorem psa_saR_ne_saN : saR ≠ saN := by decide
@[simp] theorem psa_saR_ne_saA : saR ≠ saA := by decide
@[simp] theorem psa_saR_ne_lFl : saR ≠ lFl := by decide
@[simp] theorem psa_lFl_ne_saR : lFl ≠ saR := by decide
@[simp] theorem psa_saR_ne_lDh : saR ≠ lDh := by decide
@[simp] theorem psa_lDh_ne_saR : lDh ≠ saR := by decide
@[simp] theorem psa_saR_ne_lDt : saR ≠ lDt := by decide
@[simp] theorem psa_lDt_ne_saR : lDt ≠ saR := by decide
@[simp] theorem psa_saR_ne_lDg : saR ≠ lDg := by decide
@[simp] theorem psa_lDg_ne_saR : lDg ≠ saR := by decide
@[simp] theorem psa_saR_ne_lDi : saR ≠ lDi := by decide
@[simp] theorem psa_lDi_ne_saR : lDi ≠ saR := by decide
@[simp] theorem psa_saR_ne_lRp : saR ≠ lRp := by decide
@[simp] theorem psa_lRp_ne_saR : lRp ≠ saR := by decide
@[simp] theorem psa_saR_ne_lRn : saR ≠ lRn := by decide
@[simp] theorem psa_lRn_ne_saR : lRn ≠ saR := by decide
@[simp] theorem psa_saR_ne_lFle : saR ≠ lFle := by decide
@[simp] theorem psa_lFle_ne_saR : lFle ≠ saR := by decide
@[simp] theorem psa_saR_ne_lKb : saR ≠ lKb := by decide
@[simp] theorem psa_lKb_ne_saR : lKb ≠ saR := by decide
@[simp] theorem psa_saR_ne_lDir : saR ≠ lDir := by decide
@[simp] theorem psa_lDir_ne_saR : lDir ≠ saR := by decide
@[simp] theorem psa_saR_ne_lFln : saR ≠ lFln := by decide
@[simp] theorem psa_lFln_ne_saR : lFln ≠ saR := by decide
@[simp] theorem psa_saR_ne_lFll : saR ≠ lFll := by decide
@[simp] theorem psa_lFll_ne_saR : lFll ≠ saR := by decide
@[simp] theorem psa_saR_ne_lFls : saR ≠ lFls := by decide
@[simp] theorem psa_lFls_ne_saR : lFls ≠ saR := by decide
@[simp] theorem psa_saR_ne_kFu : saR ≠ kFu := by decide
@[simp] theorem psa_kFu_ne_saR : kFu ≠ saR := by decide
@[simp] theorem psa_saR_ne_kD : saR ≠ kD := by decide
@[simp] theorem psa_kD_ne_saR : kD ≠ saR := by decide

def saParams : List MlS := [saK, saL, saU, saW]
def saLocals : List MlS := [saN, saA, saR]
def saBody (C : Ctx) : ProgHOL 64 := prologue saLocals (.ite (.cmp .equal (vv saW) (.const 1)) (.return (.const 1)) (.seq (.assign .local saN (.load .one (vv saW))) (.ite (.cmp .equal (vv saN) (.const 0)) (.return (vv saW)) (allocP C saA (.const 8) (.seq (.store (vv saA) (.const 0)) (.seq (.call (some (some (.local, saR), none)) fSb [(vv saW), (.const 0), (vv saN), (vv saK), (vv saL), (vv saU), (vv saA)]) (.return (vv saR))))))))

structure SaCodes (C : Ctx) : Prop where
  sb : SbCodes C

/-- The three read caches agree with the store. -/
def RdOK (s : AState) : Prop :=
  ReadNCacheOK s.caches.readNC s.store ∧ ReadLCacheOK s.caches.readLC s.store ∧ ReadLsCacheOK s.caches.readLsC s.store

/-- A step that only fills the read caches. -/
def RdStep (s s' : AState) : Prop :=
  s'.store = s.store ∧ s'.memos = s.memos ∧ s'.pins = s.pins ∧ MirrorEq s'.caches s.caches ∧ RdOK s'

theorem sbCodes_H {C : Ctx} (hc : SbCodes C) (H : List (BitVec 64)) : SbCodes (ctxH C H) :=
  ⟨hc.app, hc.af, hc.neq, hc.nz, ⟨hc.zc.app, hc.zc.self⟩, hc.self⟩

theorem rdStep_refl {s : AState} (h : RdOK s) : RdStep s s := ⟨rfl, rfl, rfl, mirrorEq_refl _, h⟩

theorem nil_inter (p : ConLeche.PropWhen) : (ConLeche.PropWhen.ifAllZero []).inter p = p := by
  cases p <;> simp [ConLeche.PropWhen.inter]

theorem blkAt_mono' {H H' : List (BitVec 64)} {o : Nat} {xs : List (BitVec 64)} (h : BlkAt H o xs) (hp : H <+: H') :
    BlkAt H' o xs := blkAt_mono h hp

theorem readLevelsM_runC' (h : LsIdx) (s : AState) (l : List ConLeche.Level)
    (hrl : ReadLsCacheOK s.caches.readLsC s.store) (hd : denoteLs s.store.lss h = some l) :
    ∃ X, readLevelsM h s = .ok (l, { s with caches := { s.caches with readLsC := X } }) ∧ ReadLsCacheOK X s.store := by
  unfold readLevelsM
  rcases hc : s.caches.readLsC[h]? with _ | l'
  · refine ⟨s.caches.readLsC.insert h l, ?_, ?_⟩
    · simp [hc, hd, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, bind, StateT.bind, pure, StateT.pure,
        Except.bind, Except.pure]
    · intro k u hk
      simp only [Std.HashMap.getElem?_insert] at hk
      split at hk
      · rename_i e; simp at e; subst e; simp at hk; subst hk; exact hd
      · exact hrl k u hk
  · have := hrl h l' hc
    rw [hd] at this; cases this
    exact ⟨s.caches.readLsC, by simp [hc, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure,
      StateT.pure, Except.bind, Except.pure], hrl⟩

section
variable {σ : Type}

def PostSA (C : Ctx) (s : AState) (r : Option ConLeche.PropWhen) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  RdStep s s' ∧ ∃ H', C.H <+: H' ∧ optPW C H' s r w ∧ SR (ctxH C H') s' st

theorem postSA_locals (C : Ctx) (s : AState) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostSA C s a w s' st → PostSA C s a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, H', h2, h3, h4⟩ => ⟨h1, H', h2, h3, sr_of_eq h4 rfl rfl rfl rfl⟩

theorem sa_spec (C : Ctx) (hok : CtxOK C) (hc : SaCodes C) (s : AState) (hwf : LStoreWF s.store.ls) (hrd : RdOK s)
    (khs : List NIdx) (ks : List Name) (ok : Nat)
    (hks : ∀ j (hj : j < khs.length), C.EH[ok + j]? = some (Enc.idxW khs[j])) (hkl : ks.length = khs.length)
    (hkdN : Frontend.denoteNList s.store.ns khs = some ks) (hklen : khs.length < 2 ^ 60)
    (us : LsIdx) (uh : List LIdx) (vs : List Level) (huv : s.store.lss.view us = some uh)
    (hvl : vs.length = uh.length) (hvd : ∀ j (hj : j < uh.length), denoteL s.store.ls uh[j] = some (vs[j]'(by omega)))
    (hul0 : uh.length < 2 ^ 61) (hdl : denoteLs s.store.lss us = some vs) :
    ∀ (H : List (BitVec 64)) (pw : ConLeche.PropWhen) (w : BitVec 64), C.H <+: H → pwEnc C H s pw w →
      SpecR (σ := σ) (Pre (ctxH C H) s (saParams.zip [ecell C ok, BitVec.ofNat 64 khs.length, Enc.idxW us, w])) (saBody C) s
        (substPWAt khs us pw) (PostSA (ctxH C H) s) := by
  intro H pw w hpH hpw
  refine specR_prologue (postSA_locals _ s) (Knot.params_none _ saLocals saParams _ (by decide) (by decide)) ?_
  unfold substPWAt
  cases pw with
  | never =>
    simp only [pwEnc] at hpw; subst hpw
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, saParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 1 rfl (fun t ht => ⟨rdStep_refl hrd, H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | ifAllZero ps =>
    obtain ⟨o, ns, rfl, hb, hdn⟩ := hpw
    refine specR_atEntry fun t ht => ?_
    have hbig := cellA_big hok ht.sr (blkAt_lt hb)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, saParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hbig.2.1) (fun h => absurd rfl h) (fun _ => ?_)
    refine UD.specR_heapLoadI' (C := ctxH C H) saN (vv saW) o _ (by have h := hb.1; simp only [List.length_map] at h; exact h)
      (by decide) (by simp +decide [Env.get, saParams, ctxEnv] <;> rfl) ?_
    obtain ⟨hlen, hget⟩ := LSub.denoteNList_get _ ns ps hdn
    have hsz := blk_small0 (ctxOK_H hok H) ht.sr hb
    simp only [List.length_map] at hsz
    cases ps with
    | nil =>
      have hns : ns = [] := List.eq_nil_of_length_eq_zero (by simp at hlen; omega)
      subst hns
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, saParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ (cellA C o) (by simp +decide [Env.get, saParams, ctxEnv] <;> rfl)
        (fun t ht => ⟨rdStep_refl hrd, H, List.prefix_refl _, ⟨o, [], rfl, hb, hdn⟩, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | cons n rest =>
      have hne : BitVec.ofNat 64 ns.length ≠ 0 := by
        intro e; have := congrArg BitVec.toNat e; simp at this hlen; omega
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, saParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
      dsimp only
      obtain ⟨hrn, hrl, hrls⟩ := hrd
      obtain ⟨c1, hn1, hc1, hok1⟩ := ILP.readNamesM_eq khs s ks hrn hkdN
      obtain ⟨X, hx, hxok⟩ := readLevelsM_runC' us (withC s c1) vs (by show ReadLsCacheOK c1.readLsC s.store; rw [hc1]; exact hrls) hdl
      refine LLeq.specR_ofRun (R' := fun r w s' st => s' = s ∧ ∃ H', H <+: H' ∧ optPW (ctxH C H) H' s r w ∧ SR (ctxH C H') s st)
        (am_run_bind hn1 (am_run_bind hx rfl)) ?_
        (fun w st ⟨_, H', hp, hw, hsr⟩ => ⟨⟨rfl, rfl, rfl, ?_, ?_⟩, H', hp, hw, LLeq.sr_congrS hsr rfl rfl ?_ rfl⟩)
      rotate_left
      · rw [hc1]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      · refine ⟨hok1, ?_, hxok⟩
        show ReadLCacheOK c1.readLC s.store; rw [hc1]; exact hrl
      · rw [hc1]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
      refine specR_congr (m' := pure (some ((ConLeche.PropWhen.ifAllZero []).inter
        (ConLeche.PropWhen.bindZ.go (fun n => ConLeche.Level.zeronessOf (ConLeche.Level.subst.go ks vs n)) ((n :: rest).drop 0))))) (by
          simp [ConLeche.Level.substPW, ConLeche.PropWhen.bindZ, nil_inter]) ?_
      refine specR_emptyBlk (C0 := C) hok (H := H) saA (by decide) (fun H2 oe hp2 hbe => ?_)
      refine specR_congr (m' := (pure ((ConLeche.PropWhen.ifAllZero []).inter
        (ConLeche.PropWhen.bindZ.go (fun n => ConLeche.Level.zeronessOf (ConLeche.Level.subst.go ks vs n)) ((n :: rest).drop 0))) : AM _) >>= fun r => pure (some r)) (by simp) ?_
      refine specR_callNIH (C := ctxH C H2) saR fSb sbParams [vv saW, .const 0, vv saN, vv saK, vv saL, vv saU, vv saA] sbBody
        [cellA C o, BitVec.ofNat 64 0, BitVec.ofNat 64 ns.length, ecell C ok, BitVec.ofNat 64 khs.length, Enc.idxW us, cellA C oe]
        (by decide) rfl (by decide) hc.sb.self
        ⟨by simp +decide [Env.get, saParams, ctxEnv] <;> rfl, rfl, by simp, by simp +decide [Env.get, saParams, ctxEnv] <;> rfl, by simp +decide [Env.get, saParams, ctxEnv], by simp +decide [Env.get, saParams, ctxEnv], by simp <;> rfl, trivial⟩
        (PostSB (ctxH C H2) s) (fun r w s' H' => s' = s ∧ pwEnc C H' s r w)
        (fun r w s' st ⟨hs, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hs, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu sbParams _ rfl hlk)
          (sb_spec (ctxH C H) (ctxOK_H hok H) (sbCodes_H hc.sb H) s hwf khs ks ok hks hkl (fun j hj => ⟨_, (LSub.denoteNList_get _ khs ks hkdN).2 j hj⟩) hklen
            us uh vs huv hvl hvd hul0 o ns (n :: rest) hb hdn hlen (by omega) ns.length 0 H2 [] [] oe hp2
            (by simp) (Nat.zero_le _) (by simpa using hbe) rfl))
        (fun r w s3 H3 hp3 ⟨hs3, hw⟩ => ?_)
      subst hs3
      exact specR_returnI _ w (by simp) (fun t ht => ⟨rfl, H3, hp2.trans hp3, hw, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
