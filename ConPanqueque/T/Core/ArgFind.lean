import ConPanqueque.T.Core.NzParam
import ConPanqueque.T.NameEq
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `argFind`: the argument a substituted parameter takes

`subst.go ks vs n` located: walk the parameter names (an environment block) and the level arguments (the
universe-list handle's row) together; at the first name equal to `n` (structural name equality), the argument's
position + 1; where either list ends, `0` (the parameter stays).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def afN := ofString "afn"
def afK := ofString "afk"
def afL := ofString "afl"
def afU := ofString "afu"
def afI := ofString "afi"
def afK1 := ofString "afk1"
def afE := ofString "afe"
def afV := ofString "afv"
def afR := ofString "afr"
def fAf := ofString "argFind"

@[simp] theorem af_zpN_ne_zpK : afN ≠ afK := by decide
@[simp] theorem af_zpN_ne_zpL : afN ≠ afL := by decide
@[simp] theorem af_zpN_ne_zpU : afN ≠ afU := by decide
@[simp] theorem af_zpN_ne_zpI : afN ≠ afI := by decide
@[simp] theorem af_zpN_ne_zpK1 : afN ≠ afK1 := by decide
@[simp] theorem af_zpN_ne_zpE : afN ≠ afE := by decide
@[simp] theorem af_zpN_ne_zpV : afN ≠ afV := by decide
@[simp] theorem af_zpN_ne_zpR : afN ≠ afR := by decide
@[simp] theorem af_zpN_ne_lFl : afN ≠ lFl := by decide
@[simp] theorem af_lFl_ne_zpN : lFl ≠ afN := by decide
@[simp] theorem af_zpN_ne_lDh : afN ≠ lDh := by decide
@[simp] theorem af_lDh_ne_zpN : lDh ≠ afN := by decide
@[simp] theorem af_zpN_ne_lDt : afN ≠ lDt := by decide
@[simp] theorem af_lDt_ne_zpN : lDt ≠ afN := by decide
@[simp] theorem af_zpN_ne_lDg : afN ≠ lDg := by decide
@[simp] theorem af_lDg_ne_zpN : lDg ≠ afN := by decide
@[simp] theorem af_zpN_ne_lDi : afN ≠ lDi := by decide
@[simp] theorem af_lDi_ne_zpN : lDi ≠ afN := by decide
@[simp] theorem af_zpN_ne_lRp : afN ≠ lRp := by decide
@[simp] theorem af_lRp_ne_zpN : lRp ≠ afN := by decide
@[simp] theorem af_zpN_ne_lRn : afN ≠ lRn := by decide
@[simp] theorem af_lRn_ne_zpN : lRn ≠ afN := by decide
@[simp] theorem af_zpN_ne_lFls : afN ≠ lFls := by decide
@[simp] theorem af_lFls_ne_zpN : lFls ≠ afN := by decide
@[simp] theorem af_zpN_ne_lDir : afN ≠ lDir := by decide
@[simp] theorem af_lDir_ne_zpN : lDir ≠ afN := by decide
@[simp] theorem af_zpN_ne_lKb : afN ≠ lKb := by decide
@[simp] theorem af_lKb_ne_zpN : lKb ≠ afN := by decide
@[simp] theorem af_zpK_ne_zpN : afK ≠ afN := by decide
@[simp] theorem af_zpK_ne_zpL : afK ≠ afL := by decide
@[simp] theorem af_zpK_ne_zpU : afK ≠ afU := by decide
@[simp] theorem af_zpK_ne_zpI : afK ≠ afI := by decide
@[simp] theorem af_zpK_ne_zpK1 : afK ≠ afK1 := by decide
@[simp] theorem af_zpK_ne_zpE : afK ≠ afE := by decide
@[simp] theorem af_zpK_ne_zpV : afK ≠ afV := by decide
@[simp] theorem af_zpK_ne_zpR : afK ≠ afR := by decide
@[simp] theorem af_zpK_ne_lFl : afK ≠ lFl := by decide
@[simp] theorem af_lFl_ne_zpK : lFl ≠ afK := by decide
@[simp] theorem af_zpK_ne_lDh : afK ≠ lDh := by decide
@[simp] theorem af_lDh_ne_zpK : lDh ≠ afK := by decide
@[simp] theorem af_zpK_ne_lDt : afK ≠ lDt := by decide
@[simp] theorem af_lDt_ne_zpK : lDt ≠ afK := by decide
@[simp] theorem af_zpK_ne_lDg : afK ≠ lDg := by decide
@[simp] theorem af_lDg_ne_zpK : lDg ≠ afK := by decide
@[simp] theorem af_zpK_ne_lDi : afK ≠ lDi := by decide
@[simp] theorem af_lDi_ne_zpK : lDi ≠ afK := by decide
@[simp] theorem af_zpK_ne_lRp : afK ≠ lRp := by decide
@[simp] theorem af_lRp_ne_zpK : lRp ≠ afK := by decide
@[simp] theorem af_zpK_ne_lRn : afK ≠ lRn := by decide
@[simp] theorem af_lRn_ne_zpK : lRn ≠ afK := by decide
@[simp] theorem af_zpK_ne_lFls : afK ≠ lFls := by decide
@[simp] theorem af_lFls_ne_zpK : lFls ≠ afK := by decide
@[simp] theorem af_zpK_ne_lDir : afK ≠ lDir := by decide
@[simp] theorem af_lDir_ne_zpK : lDir ≠ afK := by decide
@[simp] theorem af_zpK_ne_lKb : afK ≠ lKb := by decide
@[simp] theorem af_lKb_ne_zpK : lKb ≠ afK := by decide
@[simp] theorem af_zpL_ne_zpN : afL ≠ afN := by decide
@[simp] theorem af_zpL_ne_zpK : afL ≠ afK := by decide
@[simp] theorem af_zpL_ne_zpU : afL ≠ afU := by decide
@[simp] theorem af_zpL_ne_zpI : afL ≠ afI := by decide
@[simp] theorem af_zpL_ne_zpK1 : afL ≠ afK1 := by decide
@[simp] theorem af_zpL_ne_zpE : afL ≠ afE := by decide
@[simp] theorem af_zpL_ne_zpV : afL ≠ afV := by decide
@[simp] theorem af_zpL_ne_zpR : afL ≠ afR := by decide
@[simp] theorem af_zpL_ne_lFl : afL ≠ lFl := by decide
@[simp] theorem af_lFl_ne_zpL : lFl ≠ afL := by decide
@[simp] theorem af_zpL_ne_lDh : afL ≠ lDh := by decide
@[simp] theorem af_lDh_ne_zpL : lDh ≠ afL := by decide
@[simp] theorem af_zpL_ne_lDt : afL ≠ lDt := by decide
@[simp] theorem af_lDt_ne_zpL : lDt ≠ afL := by decide
@[simp] theorem af_zpL_ne_lDg : afL ≠ lDg := by decide
@[simp] theorem af_lDg_ne_zpL : lDg ≠ afL := by decide
@[simp] theorem af_zpL_ne_lDi : afL ≠ lDi := by decide
@[simp] theorem af_lDi_ne_zpL : lDi ≠ afL := by decide
@[simp] theorem af_zpL_ne_lRp : afL ≠ lRp := by decide
@[simp] theorem af_lRp_ne_zpL : lRp ≠ afL := by decide
@[simp] theorem af_zpL_ne_lRn : afL ≠ lRn := by decide
@[simp] theorem af_lRn_ne_zpL : lRn ≠ afL := by decide
@[simp] theorem af_zpL_ne_lFls : afL ≠ lFls := by decide
@[simp] theorem af_lFls_ne_zpL : lFls ≠ afL := by decide
@[simp] theorem af_zpL_ne_lDir : afL ≠ lDir := by decide
@[simp] theorem af_lDir_ne_zpL : lDir ≠ afL := by decide
@[simp] theorem af_zpL_ne_lKb : afL ≠ lKb := by decide
@[simp] theorem af_lKb_ne_zpL : lKb ≠ afL := by decide
@[simp] theorem af_zpU_ne_zpN : afU ≠ afN := by decide
@[simp] theorem af_zpU_ne_zpK : afU ≠ afK := by decide
@[simp] theorem af_zpU_ne_zpL : afU ≠ afL := by decide
@[simp] theorem af_zpU_ne_zpI : afU ≠ afI := by decide
@[simp] theorem af_zpU_ne_zpK1 : afU ≠ afK1 := by decide
@[simp] theorem af_zpU_ne_zpE : afU ≠ afE := by decide
@[simp] theorem af_zpU_ne_zpV : afU ≠ afV := by decide
@[simp] theorem af_zpU_ne_zpR : afU ≠ afR := by decide
@[simp] theorem af_zpU_ne_lFl : afU ≠ lFl := by decide
@[simp] theorem af_lFl_ne_zpU : lFl ≠ afU := by decide
@[simp] theorem af_zpU_ne_lDh : afU ≠ lDh := by decide
@[simp] theorem af_lDh_ne_zpU : lDh ≠ afU := by decide
@[simp] theorem af_zpU_ne_lDt : afU ≠ lDt := by decide
@[simp] theorem af_lDt_ne_zpU : lDt ≠ afU := by decide
@[simp] theorem af_zpU_ne_lDg : afU ≠ lDg := by decide
@[simp] theorem af_lDg_ne_zpU : lDg ≠ afU := by decide
@[simp] theorem af_zpU_ne_lDi : afU ≠ lDi := by decide
@[simp] theorem af_lDi_ne_zpU : lDi ≠ afU := by decide
@[simp] theorem af_zpU_ne_lRp : afU ≠ lRp := by decide
@[simp] theorem af_lRp_ne_zpU : lRp ≠ afU := by decide
@[simp] theorem af_zpU_ne_lRn : afU ≠ lRn := by decide
@[simp] theorem af_lRn_ne_zpU : lRn ≠ afU := by decide
@[simp] theorem af_zpU_ne_lFls : afU ≠ lFls := by decide
@[simp] theorem af_lFls_ne_zpU : lFls ≠ afU := by decide
@[simp] theorem af_zpU_ne_lDir : afU ≠ lDir := by decide
@[simp] theorem af_lDir_ne_zpU : lDir ≠ afU := by decide
@[simp] theorem af_zpU_ne_lKb : afU ≠ lKb := by decide
@[simp] theorem af_lKb_ne_zpU : lKb ≠ afU := by decide
@[simp] theorem af_zpI_ne_zpN : afI ≠ afN := by decide
@[simp] theorem af_zpI_ne_zpK : afI ≠ afK := by decide
@[simp] theorem af_zpI_ne_zpL : afI ≠ afL := by decide
@[simp] theorem af_zpI_ne_zpU : afI ≠ afU := by decide
@[simp] theorem af_zpI_ne_zpK1 : afI ≠ afK1 := by decide
@[simp] theorem af_zpI_ne_zpE : afI ≠ afE := by decide
@[simp] theorem af_zpI_ne_zpV : afI ≠ afV := by decide
@[simp] theorem af_zpI_ne_zpR : afI ≠ afR := by decide
@[simp] theorem af_zpI_ne_lFl : afI ≠ lFl := by decide
@[simp] theorem af_lFl_ne_zpI : lFl ≠ afI := by decide
@[simp] theorem af_zpI_ne_lDh : afI ≠ lDh := by decide
@[simp] theorem af_lDh_ne_zpI : lDh ≠ afI := by decide
@[simp] theorem af_zpI_ne_lDt : afI ≠ lDt := by decide
@[simp] theorem af_lDt_ne_zpI : lDt ≠ afI := by decide
@[simp] theorem af_zpI_ne_lDg : afI ≠ lDg := by decide
@[simp] theorem af_lDg_ne_zpI : lDg ≠ afI := by decide
@[simp] theorem af_zpI_ne_lDi : afI ≠ lDi := by decide
@[simp] theorem af_lDi_ne_zpI : lDi ≠ afI := by decide
@[simp] theorem af_zpI_ne_lRp : afI ≠ lRp := by decide
@[simp] theorem af_lRp_ne_zpI : lRp ≠ afI := by decide
@[simp] theorem af_zpI_ne_lRn : afI ≠ lRn := by decide
@[simp] theorem af_lRn_ne_zpI : lRn ≠ afI := by decide
@[simp] theorem af_zpI_ne_lFls : afI ≠ lFls := by decide
@[simp] theorem af_lFls_ne_zpI : lFls ≠ afI := by decide
@[simp] theorem af_zpI_ne_lDir : afI ≠ lDir := by decide
@[simp] theorem af_lDir_ne_zpI : lDir ≠ afI := by decide
@[simp] theorem af_zpI_ne_lKb : afI ≠ lKb := by decide
@[simp] theorem af_lKb_ne_zpI : lKb ≠ afI := by decide
@[simp] theorem af_zpK1_ne_zpN : afK1 ≠ afN := by decide
@[simp] theorem af_zpK1_ne_zpK : afK1 ≠ afK := by decide
@[simp] theorem af_zpK1_ne_zpL : afK1 ≠ afL := by decide
@[simp] theorem af_zpK1_ne_zpU : afK1 ≠ afU := by decide
@[simp] theorem af_zpK1_ne_zpI : afK1 ≠ afI := by decide
@[simp] theorem af_zpK1_ne_zpE : afK1 ≠ afE := by decide
@[simp] theorem af_zpK1_ne_zpV : afK1 ≠ afV := by decide
@[simp] theorem af_zpK1_ne_zpR : afK1 ≠ afR := by decide
@[simp] theorem af_zpK1_ne_lFl : afK1 ≠ lFl := by decide
@[simp] theorem af_lFl_ne_zpK1 : lFl ≠ afK1 := by decide
@[simp] theorem af_zpK1_ne_lDh : afK1 ≠ lDh := by decide
@[simp] theorem af_lDh_ne_zpK1 : lDh ≠ afK1 := by decide
@[simp] theorem af_zpK1_ne_lDt : afK1 ≠ lDt := by decide
@[simp] theorem af_lDt_ne_zpK1 : lDt ≠ afK1 := by decide
@[simp] theorem af_zpK1_ne_lDg : afK1 ≠ lDg := by decide
@[simp] theorem af_lDg_ne_zpK1 : lDg ≠ afK1 := by decide
@[simp] theorem af_zpK1_ne_lDi : afK1 ≠ lDi := by decide
@[simp] theorem af_lDi_ne_zpK1 : lDi ≠ afK1 := by decide
@[simp] theorem af_zpK1_ne_lRp : afK1 ≠ lRp := by decide
@[simp] theorem af_lRp_ne_zpK1 : lRp ≠ afK1 := by decide
@[simp] theorem af_zpK1_ne_lRn : afK1 ≠ lRn := by decide
@[simp] theorem af_lRn_ne_zpK1 : lRn ≠ afK1 := by decide
@[simp] theorem af_zpK1_ne_lFls : afK1 ≠ lFls := by decide
@[simp] theorem af_lFls_ne_zpK1 : lFls ≠ afK1 := by decide
@[simp] theorem af_zpK1_ne_lDir : afK1 ≠ lDir := by decide
@[simp] theorem af_lDir_ne_zpK1 : lDir ≠ afK1 := by decide
@[simp] theorem af_zpK1_ne_lKb : afK1 ≠ lKb := by decide
@[simp] theorem af_lKb_ne_zpK1 : lKb ≠ afK1 := by decide
@[simp] theorem af_zpE_ne_zpN : afE ≠ afN := by decide
@[simp] theorem af_zpE_ne_zpK : afE ≠ afK := by decide
@[simp] theorem af_zpE_ne_zpL : afE ≠ afL := by decide
@[simp] theorem af_zpE_ne_zpU : afE ≠ afU := by decide
@[simp] theorem af_zpE_ne_zpI : afE ≠ afI := by decide
@[simp] theorem af_zpE_ne_zpK1 : afE ≠ afK1 := by decide
@[simp] theorem af_zpE_ne_zpV : afE ≠ afV := by decide
@[simp] theorem af_zpE_ne_zpR : afE ≠ afR := by decide
@[simp] theorem af_zpE_ne_lFl : afE ≠ lFl := by decide
@[simp] theorem af_lFl_ne_zpE : lFl ≠ afE := by decide
@[simp] theorem af_zpE_ne_lDh : afE ≠ lDh := by decide
@[simp] theorem af_lDh_ne_zpE : lDh ≠ afE := by decide
@[simp] theorem af_zpE_ne_lDt : afE ≠ lDt := by decide
@[simp] theorem af_lDt_ne_zpE : lDt ≠ afE := by decide
@[simp] theorem af_zpE_ne_lDg : afE ≠ lDg := by decide
@[simp] theorem af_lDg_ne_zpE : lDg ≠ afE := by decide
@[simp] theorem af_zpE_ne_lDi : afE ≠ lDi := by decide
@[simp] theorem af_lDi_ne_zpE : lDi ≠ afE := by decide
@[simp] theorem af_zpE_ne_lRp : afE ≠ lRp := by decide
@[simp] theorem af_lRp_ne_zpE : lRp ≠ afE := by decide
@[simp] theorem af_zpE_ne_lRn : afE ≠ lRn := by decide
@[simp] theorem af_lRn_ne_zpE : lRn ≠ afE := by decide
@[simp] theorem af_zpE_ne_lFls : afE ≠ lFls := by decide
@[simp] theorem af_lFls_ne_zpE : lFls ≠ afE := by decide
@[simp] theorem af_zpE_ne_lDir : afE ≠ lDir := by decide
@[simp] theorem af_lDir_ne_zpE : lDir ≠ afE := by decide
@[simp] theorem af_zpE_ne_lKb : afE ≠ lKb := by decide
@[simp] theorem af_lKb_ne_zpE : lKb ≠ afE := by decide
@[simp] theorem af_zpV_ne_zpN : afV ≠ afN := by decide
@[simp] theorem af_zpV_ne_zpK : afV ≠ afK := by decide
@[simp] theorem af_zpV_ne_zpL : afV ≠ afL := by decide
@[simp] theorem af_zpV_ne_zpU : afV ≠ afU := by decide
@[simp] theorem af_zpV_ne_zpI : afV ≠ afI := by decide
@[simp] theorem af_zpV_ne_zpK1 : afV ≠ afK1 := by decide
@[simp] theorem af_zpV_ne_zpE : afV ≠ afE := by decide
@[simp] theorem af_zpV_ne_zpR : afV ≠ afR := by decide
@[simp] theorem af_zpV_ne_lFl : afV ≠ lFl := by decide
@[simp] theorem af_lFl_ne_zpV : lFl ≠ afV := by decide
@[simp] theorem af_zpV_ne_lDh : afV ≠ lDh := by decide
@[simp] theorem af_lDh_ne_zpV : lDh ≠ afV := by decide
@[simp] theorem af_zpV_ne_lDt : afV ≠ lDt := by decide
@[simp] theorem af_lDt_ne_zpV : lDt ≠ afV := by decide
@[simp] theorem af_zpV_ne_lDg : afV ≠ lDg := by decide
@[simp] theorem af_lDg_ne_zpV : lDg ≠ afV := by decide
@[simp] theorem af_zpV_ne_lDi : afV ≠ lDi := by decide
@[simp] theorem af_lDi_ne_zpV : lDi ≠ afV := by decide
@[simp] theorem af_zpV_ne_lRp : afV ≠ lRp := by decide
@[simp] theorem af_lRp_ne_zpV : lRp ≠ afV := by decide
@[simp] theorem af_zpV_ne_lRn : afV ≠ lRn := by decide
@[simp] theorem af_lRn_ne_zpV : lRn ≠ afV := by decide
@[simp] theorem af_zpV_ne_lFls : afV ≠ lFls := by decide
@[simp] theorem af_lFls_ne_zpV : lFls ≠ afV := by decide
@[simp] theorem af_zpV_ne_lDir : afV ≠ lDir := by decide
@[simp] theorem af_lDir_ne_zpV : lDir ≠ afV := by decide
@[simp] theorem af_zpV_ne_lKb : afV ≠ lKb := by decide
@[simp] theorem af_lKb_ne_zpV : lKb ≠ afV := by decide
@[simp] theorem af_zpR_ne_zpN : afR ≠ afN := by decide
@[simp] theorem af_zpR_ne_zpK : afR ≠ afK := by decide
@[simp] theorem af_zpR_ne_zpL : afR ≠ afL := by decide
@[simp] theorem af_zpR_ne_zpU : afR ≠ afU := by decide
@[simp] theorem af_zpR_ne_zpI : afR ≠ afI := by decide
@[simp] theorem af_zpR_ne_zpK1 : afR ≠ afK1 := by decide
@[simp] theorem af_zpR_ne_zpE : afR ≠ afE := by decide
@[simp] theorem af_zpR_ne_zpV : afR ≠ afV := by decide
@[simp] theorem af_zpR_ne_lFl : afR ≠ lFl := by decide
@[simp] theorem af_lFl_ne_zpR : lFl ≠ afR := by decide
@[simp] theorem af_zpR_ne_lDh : afR ≠ lDh := by decide
@[simp] theorem af_lDh_ne_zpR : lDh ≠ afR := by decide
@[simp] theorem af_zpR_ne_lDt : afR ≠ lDt := by decide
@[simp] theorem af_lDt_ne_zpR : lDt ≠ afR := by decide
@[simp] theorem af_zpR_ne_lDg : afR ≠ lDg := by decide
@[simp] theorem af_lDg_ne_zpR : lDg ≠ afR := by decide
@[simp] theorem af_zpR_ne_lDi : afR ≠ lDi := by decide
@[simp] theorem af_lDi_ne_zpR : lDi ≠ afR := by decide
@[simp] theorem af_zpR_ne_lRp : afR ≠ lRp := by decide
@[simp] theorem af_lRp_ne_zpR : lRp ≠ afR := by decide
@[simp] theorem af_zpR_ne_lRn : afR ≠ lRn := by decide
@[simp] theorem af_lRn_ne_zpR : lRn ≠ afR := by decide
@[simp] theorem af_zpR_ne_lFls : afR ≠ lFls := by decide
@[simp] theorem af_lFls_ne_zpR : lFls ≠ afR := by decide
@[simp] theorem af_zpR_ne_lDir : afR ≠ lDir := by decide
@[simp] theorem af_lDir_ne_zpR : lDir ≠ afR := by decide
@[simp] theorem af_zpR_ne_lKb : afR ≠ lKb := by decide
@[simp] theorem af_lKb_ne_zpR : lKb ≠ afR := by decide

def afParams : List MlS := [afN, afK, afL, afU, afI]
def afLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, afK1, afE, afR]

/-- `afN` the name, `afK` the names' first cell, `afL` their count, `afU` the arguments' list handle, `afI` the
position. -/
def afBody : ProgHOL 64 := prologue afLocals
  (.ite (.cmp .equal (vv afI) (vv afL)) (.return (.const 0))
  (.seq (.assign .local lFl (vv lFls)) (.seq (.assign .local lDh (vv afU)) (.seq lsViewP
  (.ite (.cmp .lower (vv afI) (vv lRn))
    (.seq (.assign .local afK1 (.load .one (.op .add [vv afK, .shift .lsl (vv afI) (.const 3)])))
    (.seq (.call (some (some (.local, afE), none)) NEq.fNeq [vv afK1, vv afN])
    (.ite (vv afE)
      (.return (.op .add [vv afI, .const 1]))
      (.seq (.call (some (some (.local, afR), none)) fAf [vv afN, vv afK, vv afL, vv afU, .op .add [vv afI, .const 1]])
        (.return (vv afR))))))
    (.return (.const 0)))))))

section
variable {σ : Type}

theorem af_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ afLocals → (ctxEnv C ++ afParams.zip vals).get x = none :=
  Knot.params_none C afLocals afParams vals (by decide) (by decide)

/-- `argFind`: the position (`+ 1`) of the first parameter name equal to `nm`, or `0`; the twin's
`subst.go` answer is that argument, or the parameter itself. -/
def PostAF (C : Ctx) (s : AState) (vs : List ConLeche.Level) (uh : List LIdx) (nm : ConLeche.Name) (r : ConLeche.Level)
    (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ SR C s st ∧ ((w = 0 ∧ r = .param nm) ∨
    ∃ j, ∃ (hj : j < uh.length) (hjv : j < vs.length), w = BitVec.ofNat 64 (j + 1) ∧ r = vs[j])

theorem postAF_locals (C : Ctx) (s : AState) vs uh nm : ∀ a w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostAF C s vs uh nm a w s' st → PostAF C s vs uh nm a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2, h3⟩ => ⟨h1, sr_of_eq h2 rfl rfl rfl rfl, h3⟩

theorem af_spec (C : Ctx) (hcf : C.code.lookup fAf = some (afParams.map (fun p => (p, ShapeHOL.one)), afBody, .one))
    (hcn : C.code.lookup NEq.fNeq = some ([(NEq.pNa, .one), (NEq.pNb, .one)], NEq.neqBody, .one))
    (s : AState)
    (hwf : LStoreWF s.store.ls)
    (khs : List NIdx) (ks : List ConLeche.Name) (ok : Nat)
    (hks : ∀ j (hj : j < khs.length), C.EH[ok + j]? = some (Enc.idxW khs[j])) (hkl : ks.length = khs.length)
    (hkd : ∀ j (hj : j < khs.length), ∃ f, denoteNAux s.store.ns f khs[j] = some (ks[j]'(by omega)))
    (hklen : khs.length < 2 ^ 60)
    (us : LsIdx) (uh : List LIdx) (vs : List ConLeche.Level) (huv : s.store.lss.view us = some uh)
    (hvl : vs.length = uh.length) (hvd : ∀ j (hj : j < uh.length), denoteL s.store.ls uh[j] = some (vs[j]'(by omega)))
    (n : NIdx) (nm : ConLeche.Name) (fn : Nat) (hn : denoteNAux s.store.ns fn n = some nm) :
    ∀ k i, khs.length - i = k → i ≤ khs.length →
      SpecR (σ := σ) (Pre C s (afParams.zip [Enc.idxW n, ecell C ok, BitVec.ofNat 64 khs.length, Enc.idxW us,
        BitVec.ofNat 64 i])) afBody s (pure (ConLeche.Level.subst.go (ks.drop i) (vs.drop i) nm) : AM ConLeche.Level)
        (PostAF C s vs uh nm) := by
  intro k
  induction k with
  | zero =>
    intro i hk hi
    have hi' : i = khs.length := by omega
    subst hi'
    refine specR_prologue (postAF_locals C s vs uh nm) (af_none C _) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, afParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_of_length_le (by omega)]
    exact specR_returnI _ 0 rfl
      (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl, Or.inl ⟨rfl, by simp [ConLeche.Level.subst.go]⟩⟩)
  | succ k ih =>
    intro i hk hi
    have hil : i < khs.length := by omega
    refine specR_prologue (postAF_locals C s vs uh nm) (af_none C _) ?_
    have hne : BitVec.ofNat 64 i ≠ BitVec.ofNat 64 khs.length := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, afParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv afU) (Enc.idxW us) (by decide) (by simp +decide [Env.get, afParams, ctxEnv]) ?_
    refine specR_lsviewPI us (by simp) (by simp) (by simp +decide [Env.get, ctxEnv]) (by decide)
      (fun vl Pl hvl _ hvll => ?_)
    rw [huv] at hvl
    cases hvl
    have hul : uh.length < 2 ^ 61 := by simpa using hvll
    rw [List.drop_eq_getElem_cons (show i < ks.length by omega)]
    by_cases hiv : i < uh.length
    swap
    · have hlw := word_lt_iff i uh.length (by unfold B; omega) (by unfold B; omega)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, afParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega)
        (fun h => absurd rfl h) (fun _ => ?_)
      rw [List.drop_of_length_le (show vs.length ≤ i by omega)]
      exact specR_returnI _ 0 rfl
        (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl, Or.inl ⟨rfl, by simp [ConLeche.Level.subst.go]⟩⟩)
    have hlw := word_lt_iff i uh.length (by unfold B; omega) (by unfold B; omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, afParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega) (fun _ => ?_)
      (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons (show i < vs.length by omega)]
    refine specR_envLoadI afK1 _ (ok + i) _ (by decide)
      (by simp +decide [sev, Env.get, afParams, ctxEnv]; exact ecell_shl3 C ok i (by omega)) (hks i hil) ?_
    refine specR_dropM ?_
    obtain ⟨fk, hfk⟩ := hkd i hil
    refine specR_callPure afE NEq.fNeq [NEq.pNa, NEq.pNb] [vv afK1, vv afN] NEq.neqBody [Enc.idxW khs[i], Enc.idxW n]
      (decide (ks[i] = nm)) (by decide) rfl (by decide) hcn ⟨by simp, by simp +decide [Env.get, afParams, ctxEnv], trivial⟩
      (ExM.PostB C) (fun b w _ H' => H' = C.H ∧ w = boolW b)
      (fun b w s' st ⟨hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, by rw [hw]; cases b <;> rfl⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [NEq.pNa, NEq.pNb] _ rfl hlk)
        (NEq.neq_spec C hcn ks[i] khs[i] n nm fk fn s hfk hn))
      (fun w H1 hp1 ⟨eH1, hw⟩ => ?_)
    subst hw
    subst H1
    by_cases heq : ks[i] = nm
    · refine specR_ifI _ 1 (by simp [sev, boolW, heq]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [ConLeche.Level.subst.go, heq, ite_true]
      exact specR_returnI _ (BitVec.ofNat 64 (i + 1)) (by simp +decide [sev, Env.get, afParams, ctxEnv]; exact word_add1_eq i)
        (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl, Or.inr ⟨i, hiv, by omega, rfl, rfl⟩⟩)
    · refine specR_ifI _ 0 (by simp [sev, boolW, heq]) (fun h => absurd rfl h) (fun _ => ?_)
      simp only [ConLeche.Level.subst.go, heq, ite_false]
      refine specR_callPure (C := ctxH C C.H) afR fAf afParams
        [vv afN, vv afK, vv afL, vv afU, .op .add [vv afI, .const 1]] afBody
        [Enc.idxW n, ecell C ok, BitVec.ofNat 64 khs.length, Enc.idxW us, BitVec.ofNat 64 (i + 1)]
        (ConLeche.Level.subst.go (ks.drop (i + 1)) (vs.drop (i + 1)) nm) (by decide) rfl (by decide) hcf
        ⟨by simp +decide [Env.get, afParams, ctxEnv], by simp +decide [Env.get, afParams, ctxEnv] <;> rfl,
          by simp +decide [Env.get, afParams, ctxEnv], by simp +decide [Env.get, afParams, ctxEnv],
          by simp +decide [sev, Env.get, afParams, ctxEnv]; exact word_add1_eq i, trivial⟩
        (PostAF C s vs uh nm) (fun r w _ H' => H' = C.H ∧ ((w = 0 ∧ r = .param nm) ∨
          ∃ j, ∃ (hj : j < uh.length) (hjv : j < vs.length), w = BitVec.ofNat 64 (j + 1) ∧ r = vs[j]))
        (fun r w s' st ⟨hs, hsr, hw⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu afParams _ rfl hlk) (ih (i + 1) (by omega) (by omega)))
        (fun w H2 hp2 ⟨eH2, hw⟩ => ?_)
      subst H2
      exact specR_returnI _ w (by simp) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl, hw⟩)

end

end ConPanqueque.T.WC
