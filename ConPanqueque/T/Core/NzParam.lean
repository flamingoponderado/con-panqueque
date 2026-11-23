import ConPanqueque.T.Core.NzWalk
import ConPanqueque.T.NameEq
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# A substituted parameter's never-zero test

`subst.go ks vs n`, then `nz`: walk the parameter names (an environment block) and the level arguments (the
universe-list handle's row) together; at the first name equal to `n` (structural name equality), the argument's
`nz`; where either list ends, the parameter stays, which may be zero.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def zpN := ofString "zpn"
def zpK := ofString "zpk"
def zpL := ofString "zpl"
def zpU := ofString "zpu"
def zpI := ofString "zpi"
def zpK1 := ofString "zpk1"
def zpE := ofString "zpe"
def zpV := ofString "zpv"
def zpR := ofString "zpr"
def fZp := ofString "nzParam"

@[simp] theorem zp_zpN_ne_zpK : zpN ≠ zpK := by decide
@[simp] theorem zp_zpN_ne_zpL : zpN ≠ zpL := by decide
@[simp] theorem zp_zpN_ne_zpU : zpN ≠ zpU := by decide
@[simp] theorem zp_zpN_ne_zpI : zpN ≠ zpI := by decide
@[simp] theorem zp_zpN_ne_zpK1 : zpN ≠ zpK1 := by decide
@[simp] theorem zp_zpN_ne_zpE : zpN ≠ zpE := by decide
@[simp] theorem zp_zpN_ne_zpV : zpN ≠ zpV := by decide
@[simp] theorem zp_zpN_ne_zpR : zpN ≠ zpR := by decide
@[simp] theorem zp_zpN_ne_lFl : zpN ≠ lFl := by decide
@[simp] theorem zp_lFl_ne_zpN : lFl ≠ zpN := by decide
@[simp] theorem zp_zpN_ne_lDh : zpN ≠ lDh := by decide
@[simp] theorem zp_lDh_ne_zpN : lDh ≠ zpN := by decide
@[simp] theorem zp_zpN_ne_lDt : zpN ≠ lDt := by decide
@[simp] theorem zp_lDt_ne_zpN : lDt ≠ zpN := by decide
@[simp] theorem zp_zpN_ne_lDg : zpN ≠ lDg := by decide
@[simp] theorem zp_lDg_ne_zpN : lDg ≠ zpN := by decide
@[simp] theorem zp_zpN_ne_lDi : zpN ≠ lDi := by decide
@[simp] theorem zp_lDi_ne_zpN : lDi ≠ zpN := by decide
@[simp] theorem zp_zpN_ne_lRp : zpN ≠ lRp := by decide
@[simp] theorem zp_lRp_ne_zpN : lRp ≠ zpN := by decide
@[simp] theorem zp_zpN_ne_lRn : zpN ≠ lRn := by decide
@[simp] theorem zp_lRn_ne_zpN : lRn ≠ zpN := by decide
@[simp] theorem zp_zpN_ne_lFls : zpN ≠ lFls := by decide
@[simp] theorem zp_lFls_ne_zpN : lFls ≠ zpN := by decide
@[simp] theorem zp_zpN_ne_lDir : zpN ≠ lDir := by decide
@[simp] theorem zp_lDir_ne_zpN : lDir ≠ zpN := by decide
@[simp] theorem zp_zpN_ne_lKb : zpN ≠ lKb := by decide
@[simp] theorem zp_lKb_ne_zpN : lKb ≠ zpN := by decide
@[simp] theorem zp_zpK_ne_zpN : zpK ≠ zpN := by decide
@[simp] theorem zp_zpK_ne_zpL : zpK ≠ zpL := by decide
@[simp] theorem zp_zpK_ne_zpU : zpK ≠ zpU := by decide
@[simp] theorem zp_zpK_ne_zpI : zpK ≠ zpI := by decide
@[simp] theorem zp_zpK_ne_zpK1 : zpK ≠ zpK1 := by decide
@[simp] theorem zp_zpK_ne_zpE : zpK ≠ zpE := by decide
@[simp] theorem zp_zpK_ne_zpV : zpK ≠ zpV := by decide
@[simp] theorem zp_zpK_ne_zpR : zpK ≠ zpR := by decide
@[simp] theorem zp_zpK_ne_lFl : zpK ≠ lFl := by decide
@[simp] theorem zp_lFl_ne_zpK : lFl ≠ zpK := by decide
@[simp] theorem zp_zpK_ne_lDh : zpK ≠ lDh := by decide
@[simp] theorem zp_lDh_ne_zpK : lDh ≠ zpK := by decide
@[simp] theorem zp_zpK_ne_lDt : zpK ≠ lDt := by decide
@[simp] theorem zp_lDt_ne_zpK : lDt ≠ zpK := by decide
@[simp] theorem zp_zpK_ne_lDg : zpK ≠ lDg := by decide
@[simp] theorem zp_lDg_ne_zpK : lDg ≠ zpK := by decide
@[simp] theorem zp_zpK_ne_lDi : zpK ≠ lDi := by decide
@[simp] theorem zp_lDi_ne_zpK : lDi ≠ zpK := by decide
@[simp] theorem zp_zpK_ne_lRp : zpK ≠ lRp := by decide
@[simp] theorem zp_lRp_ne_zpK : lRp ≠ zpK := by decide
@[simp] theorem zp_zpK_ne_lRn : zpK ≠ lRn := by decide
@[simp] theorem zp_lRn_ne_zpK : lRn ≠ zpK := by decide
@[simp] theorem zp_zpK_ne_lFls : zpK ≠ lFls := by decide
@[simp] theorem zp_lFls_ne_zpK : lFls ≠ zpK := by decide
@[simp] theorem zp_zpK_ne_lDir : zpK ≠ lDir := by decide
@[simp] theorem zp_lDir_ne_zpK : lDir ≠ zpK := by decide
@[simp] theorem zp_zpK_ne_lKb : zpK ≠ lKb := by decide
@[simp] theorem zp_lKb_ne_zpK : lKb ≠ zpK := by decide
@[simp] theorem zp_zpL_ne_zpN : zpL ≠ zpN := by decide
@[simp] theorem zp_zpL_ne_zpK : zpL ≠ zpK := by decide
@[simp] theorem zp_zpL_ne_zpU : zpL ≠ zpU := by decide
@[simp] theorem zp_zpL_ne_zpI : zpL ≠ zpI := by decide
@[simp] theorem zp_zpL_ne_zpK1 : zpL ≠ zpK1 := by decide
@[simp] theorem zp_zpL_ne_zpE : zpL ≠ zpE := by decide
@[simp] theorem zp_zpL_ne_zpV : zpL ≠ zpV := by decide
@[simp] theorem zp_zpL_ne_zpR : zpL ≠ zpR := by decide
@[simp] theorem zp_zpL_ne_lFl : zpL ≠ lFl := by decide
@[simp] theorem zp_lFl_ne_zpL : lFl ≠ zpL := by decide
@[simp] theorem zp_zpL_ne_lDh : zpL ≠ lDh := by decide
@[simp] theorem zp_lDh_ne_zpL : lDh ≠ zpL := by decide
@[simp] theorem zp_zpL_ne_lDt : zpL ≠ lDt := by decide
@[simp] theorem zp_lDt_ne_zpL : lDt ≠ zpL := by decide
@[simp] theorem zp_zpL_ne_lDg : zpL ≠ lDg := by decide
@[simp] theorem zp_lDg_ne_zpL : lDg ≠ zpL := by decide
@[simp] theorem zp_zpL_ne_lDi : zpL ≠ lDi := by decide
@[simp] theorem zp_lDi_ne_zpL : lDi ≠ zpL := by decide
@[simp] theorem zp_zpL_ne_lRp : zpL ≠ lRp := by decide
@[simp] theorem zp_lRp_ne_zpL : lRp ≠ zpL := by decide
@[simp] theorem zp_zpL_ne_lRn : zpL ≠ lRn := by decide
@[simp] theorem zp_lRn_ne_zpL : lRn ≠ zpL := by decide
@[simp] theorem zp_zpL_ne_lFls : zpL ≠ lFls := by decide
@[simp] theorem zp_lFls_ne_zpL : lFls ≠ zpL := by decide
@[simp] theorem zp_zpL_ne_lDir : zpL ≠ lDir := by decide
@[simp] theorem zp_lDir_ne_zpL : lDir ≠ zpL := by decide
@[simp] theorem zp_zpL_ne_lKb : zpL ≠ lKb := by decide
@[simp] theorem zp_lKb_ne_zpL : lKb ≠ zpL := by decide
@[simp] theorem zp_zpU_ne_zpN : zpU ≠ zpN := by decide
@[simp] theorem zp_zpU_ne_zpK : zpU ≠ zpK := by decide
@[simp] theorem zp_zpU_ne_zpL : zpU ≠ zpL := by decide
@[simp] theorem zp_zpU_ne_zpI : zpU ≠ zpI := by decide
@[simp] theorem zp_zpU_ne_zpK1 : zpU ≠ zpK1 := by decide
@[simp] theorem zp_zpU_ne_zpE : zpU ≠ zpE := by decide
@[simp] theorem zp_zpU_ne_zpV : zpU ≠ zpV := by decide
@[simp] theorem zp_zpU_ne_zpR : zpU ≠ zpR := by decide
@[simp] theorem zp_zpU_ne_lFl : zpU ≠ lFl := by decide
@[simp] theorem zp_lFl_ne_zpU : lFl ≠ zpU := by decide
@[simp] theorem zp_zpU_ne_lDh : zpU ≠ lDh := by decide
@[simp] theorem zp_lDh_ne_zpU : lDh ≠ zpU := by decide
@[simp] theorem zp_zpU_ne_lDt : zpU ≠ lDt := by decide
@[simp] theorem zp_lDt_ne_zpU : lDt ≠ zpU := by decide
@[simp] theorem zp_zpU_ne_lDg : zpU ≠ lDg := by decide
@[simp] theorem zp_lDg_ne_zpU : lDg ≠ zpU := by decide
@[simp] theorem zp_zpU_ne_lDi : zpU ≠ lDi := by decide
@[simp] theorem zp_lDi_ne_zpU : lDi ≠ zpU := by decide
@[simp] theorem zp_zpU_ne_lRp : zpU ≠ lRp := by decide
@[simp] theorem zp_lRp_ne_zpU : lRp ≠ zpU := by decide
@[simp] theorem zp_zpU_ne_lRn : zpU ≠ lRn := by decide
@[simp] theorem zp_lRn_ne_zpU : lRn ≠ zpU := by decide
@[simp] theorem zp_zpU_ne_lFls : zpU ≠ lFls := by decide
@[simp] theorem zp_lFls_ne_zpU : lFls ≠ zpU := by decide
@[simp] theorem zp_zpU_ne_lDir : zpU ≠ lDir := by decide
@[simp] theorem zp_lDir_ne_zpU : lDir ≠ zpU := by decide
@[simp] theorem zp_zpU_ne_lKb : zpU ≠ lKb := by decide
@[simp] theorem zp_lKb_ne_zpU : lKb ≠ zpU := by decide
@[simp] theorem zp_zpI_ne_zpN : zpI ≠ zpN := by decide
@[simp] theorem zp_zpI_ne_zpK : zpI ≠ zpK := by decide
@[simp] theorem zp_zpI_ne_zpL : zpI ≠ zpL := by decide
@[simp] theorem zp_zpI_ne_zpU : zpI ≠ zpU := by decide
@[simp] theorem zp_zpI_ne_zpK1 : zpI ≠ zpK1 := by decide
@[simp] theorem zp_zpI_ne_zpE : zpI ≠ zpE := by decide
@[simp] theorem zp_zpI_ne_zpV : zpI ≠ zpV := by decide
@[simp] theorem zp_zpI_ne_zpR : zpI ≠ zpR := by decide
@[simp] theorem zp_zpI_ne_lFl : zpI ≠ lFl := by decide
@[simp] theorem zp_lFl_ne_zpI : lFl ≠ zpI := by decide
@[simp] theorem zp_zpI_ne_lDh : zpI ≠ lDh := by decide
@[simp] theorem zp_lDh_ne_zpI : lDh ≠ zpI := by decide
@[simp] theorem zp_zpI_ne_lDt : zpI ≠ lDt := by decide
@[simp] theorem zp_lDt_ne_zpI : lDt ≠ zpI := by decide
@[simp] theorem zp_zpI_ne_lDg : zpI ≠ lDg := by decide
@[simp] theorem zp_lDg_ne_zpI : lDg ≠ zpI := by decide
@[simp] theorem zp_zpI_ne_lDi : zpI ≠ lDi := by decide
@[simp] theorem zp_lDi_ne_zpI : lDi ≠ zpI := by decide
@[simp] theorem zp_zpI_ne_lRp : zpI ≠ lRp := by decide
@[simp] theorem zp_lRp_ne_zpI : lRp ≠ zpI := by decide
@[simp] theorem zp_zpI_ne_lRn : zpI ≠ lRn := by decide
@[simp] theorem zp_lRn_ne_zpI : lRn ≠ zpI := by decide
@[simp] theorem zp_zpI_ne_lFls : zpI ≠ lFls := by decide
@[simp] theorem zp_lFls_ne_zpI : lFls ≠ zpI := by decide
@[simp] theorem zp_zpI_ne_lDir : zpI ≠ lDir := by decide
@[simp] theorem zp_lDir_ne_zpI : lDir ≠ zpI := by decide
@[simp] theorem zp_zpI_ne_lKb : zpI ≠ lKb := by decide
@[simp] theorem zp_lKb_ne_zpI : lKb ≠ zpI := by decide
@[simp] theorem zp_zpK1_ne_zpN : zpK1 ≠ zpN := by decide
@[simp] theorem zp_zpK1_ne_zpK : zpK1 ≠ zpK := by decide
@[simp] theorem zp_zpK1_ne_zpL : zpK1 ≠ zpL := by decide
@[simp] theorem zp_zpK1_ne_zpU : zpK1 ≠ zpU := by decide
@[simp] theorem zp_zpK1_ne_zpI : zpK1 ≠ zpI := by decide
@[simp] theorem zp_zpK1_ne_zpE : zpK1 ≠ zpE := by decide
@[simp] theorem zp_zpK1_ne_zpV : zpK1 ≠ zpV := by decide
@[simp] theorem zp_zpK1_ne_zpR : zpK1 ≠ zpR := by decide
@[simp] theorem zp_zpK1_ne_lFl : zpK1 ≠ lFl := by decide
@[simp] theorem zp_lFl_ne_zpK1 : lFl ≠ zpK1 := by decide
@[simp] theorem zp_zpK1_ne_lDh : zpK1 ≠ lDh := by decide
@[simp] theorem zp_lDh_ne_zpK1 : lDh ≠ zpK1 := by decide
@[simp] theorem zp_zpK1_ne_lDt : zpK1 ≠ lDt := by decide
@[simp] theorem zp_lDt_ne_zpK1 : lDt ≠ zpK1 := by decide
@[simp] theorem zp_zpK1_ne_lDg : zpK1 ≠ lDg := by decide
@[simp] theorem zp_lDg_ne_zpK1 : lDg ≠ zpK1 := by decide
@[simp] theorem zp_zpK1_ne_lDi : zpK1 ≠ lDi := by decide
@[simp] theorem zp_lDi_ne_zpK1 : lDi ≠ zpK1 := by decide
@[simp] theorem zp_zpK1_ne_lRp : zpK1 ≠ lRp := by decide
@[simp] theorem zp_lRp_ne_zpK1 : lRp ≠ zpK1 := by decide
@[simp] theorem zp_zpK1_ne_lRn : zpK1 ≠ lRn := by decide
@[simp] theorem zp_lRn_ne_zpK1 : lRn ≠ zpK1 := by decide
@[simp] theorem zp_zpK1_ne_lFls : zpK1 ≠ lFls := by decide
@[simp] theorem zp_lFls_ne_zpK1 : lFls ≠ zpK1 := by decide
@[simp] theorem zp_zpK1_ne_lDir : zpK1 ≠ lDir := by decide
@[simp] theorem zp_lDir_ne_zpK1 : lDir ≠ zpK1 := by decide
@[simp] theorem zp_zpK1_ne_lKb : zpK1 ≠ lKb := by decide
@[simp] theorem zp_lKb_ne_zpK1 : lKb ≠ zpK1 := by decide
@[simp] theorem zp_zpE_ne_zpN : zpE ≠ zpN := by decide
@[simp] theorem zp_zpE_ne_zpK : zpE ≠ zpK := by decide
@[simp] theorem zp_zpE_ne_zpL : zpE ≠ zpL := by decide
@[simp] theorem zp_zpE_ne_zpU : zpE ≠ zpU := by decide
@[simp] theorem zp_zpE_ne_zpI : zpE ≠ zpI := by decide
@[simp] theorem zp_zpE_ne_zpK1 : zpE ≠ zpK1 := by decide
@[simp] theorem zp_zpE_ne_zpV : zpE ≠ zpV := by decide
@[simp] theorem zp_zpE_ne_zpR : zpE ≠ zpR := by decide
@[simp] theorem zp_zpE_ne_lFl : zpE ≠ lFl := by decide
@[simp] theorem zp_lFl_ne_zpE : lFl ≠ zpE := by decide
@[simp] theorem zp_zpE_ne_lDh : zpE ≠ lDh := by decide
@[simp] theorem zp_lDh_ne_zpE : lDh ≠ zpE := by decide
@[simp] theorem zp_zpE_ne_lDt : zpE ≠ lDt := by decide
@[simp] theorem zp_lDt_ne_zpE : lDt ≠ zpE := by decide
@[simp] theorem zp_zpE_ne_lDg : zpE ≠ lDg := by decide
@[simp] theorem zp_lDg_ne_zpE : lDg ≠ zpE := by decide
@[simp] theorem zp_zpE_ne_lDi : zpE ≠ lDi := by decide
@[simp] theorem zp_lDi_ne_zpE : lDi ≠ zpE := by decide
@[simp] theorem zp_zpE_ne_lRp : zpE ≠ lRp := by decide
@[simp] theorem zp_lRp_ne_zpE : lRp ≠ zpE := by decide
@[simp] theorem zp_zpE_ne_lRn : zpE ≠ lRn := by decide
@[simp] theorem zp_lRn_ne_zpE : lRn ≠ zpE := by decide
@[simp] theorem zp_zpE_ne_lFls : zpE ≠ lFls := by decide
@[simp] theorem zp_lFls_ne_zpE : lFls ≠ zpE := by decide
@[simp] theorem zp_zpE_ne_lDir : zpE ≠ lDir := by decide
@[simp] theorem zp_lDir_ne_zpE : lDir ≠ zpE := by decide
@[simp] theorem zp_zpE_ne_lKb : zpE ≠ lKb := by decide
@[simp] theorem zp_lKb_ne_zpE : lKb ≠ zpE := by decide
@[simp] theorem zp_zpV_ne_zpN : zpV ≠ zpN := by decide
@[simp] theorem zp_zpV_ne_zpK : zpV ≠ zpK := by decide
@[simp] theorem zp_zpV_ne_zpL : zpV ≠ zpL := by decide
@[simp] theorem zp_zpV_ne_zpU : zpV ≠ zpU := by decide
@[simp] theorem zp_zpV_ne_zpI : zpV ≠ zpI := by decide
@[simp] theorem zp_zpV_ne_zpK1 : zpV ≠ zpK1 := by decide
@[simp] theorem zp_zpV_ne_zpE : zpV ≠ zpE := by decide
@[simp] theorem zp_zpV_ne_zpR : zpV ≠ zpR := by decide
@[simp] theorem zp_zpV_ne_lFl : zpV ≠ lFl := by decide
@[simp] theorem zp_lFl_ne_zpV : lFl ≠ zpV := by decide
@[simp] theorem zp_zpV_ne_lDh : zpV ≠ lDh := by decide
@[simp] theorem zp_lDh_ne_zpV : lDh ≠ zpV := by decide
@[simp] theorem zp_zpV_ne_lDt : zpV ≠ lDt := by decide
@[simp] theorem zp_lDt_ne_zpV : lDt ≠ zpV := by decide
@[simp] theorem zp_zpV_ne_lDg : zpV ≠ lDg := by decide
@[simp] theorem zp_lDg_ne_zpV : lDg ≠ zpV := by decide
@[simp] theorem zp_zpV_ne_lDi : zpV ≠ lDi := by decide
@[simp] theorem zp_lDi_ne_zpV : lDi ≠ zpV := by decide
@[simp] theorem zp_zpV_ne_lRp : zpV ≠ lRp := by decide
@[simp] theorem zp_lRp_ne_zpV : lRp ≠ zpV := by decide
@[simp] theorem zp_zpV_ne_lRn : zpV ≠ lRn := by decide
@[simp] theorem zp_lRn_ne_zpV : lRn ≠ zpV := by decide
@[simp] theorem zp_zpV_ne_lFls : zpV ≠ lFls := by decide
@[simp] theorem zp_lFls_ne_zpV : lFls ≠ zpV := by decide
@[simp] theorem zp_zpV_ne_lDir : zpV ≠ lDir := by decide
@[simp] theorem zp_lDir_ne_zpV : lDir ≠ zpV := by decide
@[simp] theorem zp_zpV_ne_lKb : zpV ≠ lKb := by decide
@[simp] theorem zp_lKb_ne_zpV : lKb ≠ zpV := by decide
@[simp] theorem zp_zpR_ne_zpN : zpR ≠ zpN := by decide
@[simp] theorem zp_zpR_ne_zpK : zpR ≠ zpK := by decide
@[simp] theorem zp_zpR_ne_zpL : zpR ≠ zpL := by decide
@[simp] theorem zp_zpR_ne_zpU : zpR ≠ zpU := by decide
@[simp] theorem zp_zpR_ne_zpI : zpR ≠ zpI := by decide
@[simp] theorem zp_zpR_ne_zpK1 : zpR ≠ zpK1 := by decide
@[simp] theorem zp_zpR_ne_zpE : zpR ≠ zpE := by decide
@[simp] theorem zp_zpR_ne_zpV : zpR ≠ zpV := by decide
@[simp] theorem zp_zpR_ne_lFl : zpR ≠ lFl := by decide
@[simp] theorem zp_lFl_ne_zpR : lFl ≠ zpR := by decide
@[simp] theorem zp_zpR_ne_lDh : zpR ≠ lDh := by decide
@[simp] theorem zp_lDh_ne_zpR : lDh ≠ zpR := by decide
@[simp] theorem zp_zpR_ne_lDt : zpR ≠ lDt := by decide
@[simp] theorem zp_lDt_ne_zpR : lDt ≠ zpR := by decide
@[simp] theorem zp_zpR_ne_lDg : zpR ≠ lDg := by decide
@[simp] theorem zp_lDg_ne_zpR : lDg ≠ zpR := by decide
@[simp] theorem zp_zpR_ne_lDi : zpR ≠ lDi := by decide
@[simp] theorem zp_lDi_ne_zpR : lDi ≠ zpR := by decide
@[simp] theorem zp_zpR_ne_lRp : zpR ≠ lRp := by decide
@[simp] theorem zp_lRp_ne_zpR : lRp ≠ zpR := by decide
@[simp] theorem zp_zpR_ne_lRn : zpR ≠ lRn := by decide
@[simp] theorem zp_lRn_ne_zpR : lRn ≠ zpR := by decide
@[simp] theorem zp_zpR_ne_lFls : zpR ≠ lFls := by decide
@[simp] theorem zp_lFls_ne_zpR : lFls ≠ zpR := by decide
@[simp] theorem zp_zpR_ne_lDir : zpR ≠ lDir := by decide
@[simp] theorem zp_lDir_ne_zpR : lDir ≠ zpR := by decide
@[simp] theorem zp_zpR_ne_lKb : zpR ≠ lKb := by decide
@[simp] theorem zp_lKb_ne_zpR : lKb ≠ zpR := by decide

def zpParams : List MlS := [zpN, zpK, zpL, zpU, zpI]
def zpLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, zpK1, zpE, zpV, zpR]

/-- `zpN` the name, `zpK` the names' first cell, `zpL` their count, `zpU` the arguments' list handle, `zpI` the
position. -/
def zpBody : ProgHOL 64 := prologue zpLocals
  (.ite (.cmp .equal (vv zpI) (vv zpL)) (.return (.const 0))
  (.seq (.assign .local lFl (vv lFls)) (.seq (.assign .local lDh (vv zpU)) (.seq lsViewP
  (.ite (.cmp .lower (vv zpI) (vv lRn))
    (.seq (.assign .local zpK1 (.load .one (.op .add [vv zpK, .shift .lsl (vv zpI) (.const 3)])))
    (.seq (.call (some (some (.local, zpE), none)) NEq.fNeq [vv zpK1, vv zpN])
    (.ite (vv zpE)
      (.seq (.assign .local lFl (vv lFls)) (.seq (.assign .local lDh (vv zpU)) (.seq lsViewP
      (.seq (.assign .local zpV (.load .one (.op .add [vv lRp, .shift .lsl (vv zpI) (.const 3)])))
      (.seq (.call (some (some (.local, zpR), none)) fNz0 [vv zpV]) (.return (vv zpR)))))))
      (.seq (.call (some (some (.local, zpR), none)) fZp [vv zpN, vv zpK, vv zpL, vv zpU, .op .add [vv zpI, .const 1]])
        (.return (vv zpR))))))
    (.return (.const 0)))))))

section
variable {σ : Type}

theorem zp_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ zpLocals → (ctxEnv C ++ zpParams.zip vals).get x = none :=
  Knot.params_none C zpLocals zpParams vals (by decide) (by decide)

/-- A read-only Boolean answer at the given state; callees may have grown the heap. -/
def PostBX (C : Ctx) (s : AState) (b : Bool) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ w = boolW b ∧ ∃ H', C.H <+: H' ∧ SR (ctxH C H') s st

theorem postBX_locals (C : Ctx) (s : AState) : ∀ (a : Bool) w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostBX C s a w s' st → PostBX C s a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2, H', hp, h3⟩ => ⟨h1, h2, H', hp, sr_of_eq h3 rfl rfl rfl rfl⟩

theorem zp_spec (C : Ctx) (hcf : C.code.lookup fZp = some (zpParams.map (fun p => (p, ShapeHOL.one)), zpBody, .one))
    (hcn : C.code.lookup NEq.fNeq = some ([(NEq.pNa, .one), (NEq.pNb, .one)], NEq.neqBody, .one))
    (hcz : C.code.lookup fNz0 = some ([(nzU, ShapeHOL.one)], nzBody, .one)) (s : AState)
    (hwf : LStoreWF s.store.ls)
    (khs : List NIdx) (ks : List ConLeche.Name) (ok : Nat)
    (hks : ∀ j (hj : j < khs.length), C.EH[ok + j]? = some (Enc.idxW khs[j])) (hkl : ks.length = khs.length)
    (hkd : ∀ j (hj : j < khs.length), ∃ f, denoteNAux s.store.ns f khs[j] = some (ks[j]'(by omega)))
    (hklen : khs.length < 2 ^ 60)
    (us : LsIdx) (uh : List LIdx) (vs : List ConLeche.Level) (huv : s.store.lss.view us = some uh)
    (hvl : vs.length = uh.length) (hvd : ∀ j (hj : j < uh.length), denoteL s.store.ls uh[j] = some (vs[j]'(by omega)))
    (n : NIdx) (nm : ConLeche.Name) (fn : Nat) (hn : denoteNAux s.store.ns fn n = some nm) :
    ∀ k i, khs.length - i = k → i ≤ khs.length →
      SpecR (σ := σ) (Pre C s (zpParams.zip [Enc.idxW n, ecell C ok, BitVec.ofNat 64 khs.length, Enc.idxW us,
        BitVec.ofNat 64 i])) zpBody s (pure (nz (ConLeche.Level.subst.go (ks.drop i) (vs.drop i) nm)) : AM Bool)
        (PostBS C s) := by
  intro k
  induction k with
  | zero =>
    intro i hk hi
    have hi' : i = khs.length := by omega
    subst hi'
    refine specR_prologue (postBS_locals C s) (zp_none C _) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, zpParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_of_length_le (by omega)]
    exact specR_returnI _ (boolW false) (by simp [boolW]; rfl)
      (fun t ht => ⟨rfl, by simp [ConLeche.Level.subst.go, nz], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro i hk hi
    have hil : i < khs.length := by omega
    refine specR_prologue (postBS_locals C s) (zp_none C _) ?_
    have hne : BitVec.ofNat 64 i ≠ BitVec.ofNat 64 khs.length := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, zpParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv zpU) (Enc.idxW us) (by decide) (by simp +decide [Env.get, zpParams, ctxEnv]) ?_
    refine specR_lsviewPI us (by simp) (by simp) (by simp +decide [Env.get, ctxEnv]) (by decide)
      (fun vl Pl hvl _ hvll => ?_)
    rw [huv] at hvl
    cases hvl
    have hul : uh.length < 2 ^ 61 := by simpa using hvll
    rw [List.drop_eq_getElem_cons (show i < ks.length by omega)]
    by_cases hiv : i < uh.length
    swap
    · have hlw := word_lt_iff i uh.length (by unfold B; omega) (by unfold B; omega)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, zpParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega)
        (fun h => absurd rfl h) (fun _ => ?_)
      rw [List.drop_of_length_le (show vs.length ≤ i by omega)]
      exact specR_returnI _ (boolW false) (by simp [boolW]; rfl)
        (fun t ht => ⟨rfl, by simp [ConLeche.Level.subst.go, nz], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have hlw := word_lt_iff i uh.length (by unfold B; omega) (by unfold B; omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, zpParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega) (fun _ => ?_)
      (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons (show i < vs.length by omega)]
    refine specR_envLoadI zpK1 _ (ok + i) _ (by decide)
      (by simp +decide [sev, Env.get, zpParams, ctxEnv]; exact ecell_shl3 C ok i (by omega)) (hks i hil) ?_
    refine specR_dropM ?_
    obtain ⟨fk, hfk⟩ := hkd i hil
    refine specR_callPure zpE NEq.fNeq [NEq.pNa, NEq.pNb] [vv zpK1, vv zpN] NEq.neqBody [Enc.idxW khs[i], Enc.idxW n]
      (decide (ks[i] = nm)) (by decide) rfl (by decide) hcn ⟨by simp, by simp +decide [Env.get, zpParams, ctxEnv], trivial⟩
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
      refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv zpU) (Enc.idxW us) (by decide) (by simp +decide [Env.get, zpParams, ctxEnv]) ?_
      refine specR_lsviewPI (C := ctxH C C.H) us (by simp) (by simp <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
        (fun vl2 Pl2 hvl2 _ _ => ?_)
      rw [huv] at hvl2
      cases hvl2
      refine specR_loadI' zpV _ (Pl2 + BitVec.ofNat 64 (8 * i)) (Pl2 + BitVec.ofNat 64 (8 * i)) (Enc.idxW uh[i])
        (by decide) (by simp +decide [sev, Env.get, zpParams, ctxEnv]; rw [Str.w_shl i 3 (by omega), show i * 2 ^ 3 = 8 * i by omega]) rfl
        (by have h := wordsAt_get Pl2 (uh.map Enc.idxW) i (by simpa using hiv) []; simp only [List.getElem_map] at h; exact h) ?_
      refine specR_dropM ?_
      refine specR_callPure (C := ctxH C C.H) zpR fNz0 [nzU] [vv zpV] nzBody [Enc.idxW uh[i]] (nz (vs[i]'(by omega)))
        (by decide) rfl (by decide) hcz ⟨by simp, trivial⟩ (PostBS (ctxH C C.H) s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
        (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [nzU] _ rfl hlk)
          (nz0_spec (ctxH C C.H) hcz s hwf _ uh[i] (hvd i hiv)))
        (fun w H2 hp2 ⟨eH, hw⟩ => ?_)
      subst H2; subst hw
      exact specR_returnI _ (boolW (nz (vs[i]'(by omega)))) (by simp)
        (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_ifI _ 0 (by simp [sev, boolW, heq]) (fun h => absurd rfl h) (fun _ => ?_)
      simp only [ConLeche.Level.subst.go, heq, ite_false]
      refine specR_callPure (C := ctxH C C.H) zpR fZp zpParams
        [vv zpN, vv zpK, vv zpL, vv zpU, .op .add [vv zpI, .const 1]] zpBody
        [Enc.idxW n, ecell C ok, BitVec.ofNat 64 khs.length, Enc.idxW us, BitVec.ofNat 64 (i + 1)]
        (nz (ConLeche.Level.subst.go (ks.drop (i + 1)) (vs.drop (i + 1)) nm)) (by decide) rfl (by decide) hcf
        ⟨by simp +decide [Env.get, zpParams, ctxEnv], by simp +decide [Env.get, zpParams, ctxEnv] <;> rfl,
          by simp +decide [Env.get, zpParams, ctxEnv], by simp +decide [Env.get, zpParams, ctxEnv],
          by simp +decide [sev, Env.get, zpParams, ctxEnv]; exact word_add1_eq i, trivial⟩
        (PostBS C s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
        (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu zpParams _ rfl hlk) (ih (i + 1) (by omega) (by omega)))
        (fun w H2 hp2 ⟨eH2, hw⟩ => ?_)
      subst H2; subst hw
      exact specR_returnI _ _ (by simp) (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
