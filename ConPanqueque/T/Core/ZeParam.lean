import ConPanqueque.T.Core.ZeWalk
import ConPanqueque.T.Core.NzParam
import ConPanqueque.T.NameEq
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# A substituted parameter's never-zero test

`subst.go ks vs n`, then `ze`: walk the parameter names (an environment block) and the level arguments (the
universe-list handle's row) together; at the first name equal to `n` (structural name equality), the argument's
`ze`; where either list ends, the parameter stays, which may be zero.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def ztN := ofString "ztn"
def ztK := ofString "ztk"
def ztL := ofString "ztl"
def ztU := ofString "ztu"
def ztI := ofString "zti"
def ztK1 := ofString "ztk1"
def ztE := ofString "zte"
def ztV := ofString "ztv"
def ztR := ofString "ztr"
def fZt := ofString "zeParam"

@[simp] theorem zt_zpN_ne_zpK : ztN ≠ ztK := by decide
@[simp] theorem zt_zpN_ne_zpL : ztN ≠ ztL := by decide
@[simp] theorem zt_zpN_ne_zpU : ztN ≠ ztU := by decide
@[simp] theorem zt_zpN_ne_zpI : ztN ≠ ztI := by decide
@[simp] theorem zt_zpN_ne_zpK1 : ztN ≠ ztK1 := by decide
@[simp] theorem zt_zpN_ne_zpE : ztN ≠ ztE := by decide
@[simp] theorem zt_zpN_ne_zpV : ztN ≠ ztV := by decide
@[simp] theorem zt_zpN_ne_zpR : ztN ≠ ztR := by decide
@[simp] theorem zt_zpN_ne_lFl : ztN ≠ lFl := by decide
@[simp] theorem zt_lFl_ne_zpN : lFl ≠ ztN := by decide
@[simp] theorem zt_zpN_ne_lDh : ztN ≠ lDh := by decide
@[simp] theorem zt_lDh_ne_zpN : lDh ≠ ztN := by decide
@[simp] theorem zt_zpN_ne_lDt : ztN ≠ lDt := by decide
@[simp] theorem zt_lDt_ne_zpN : lDt ≠ ztN := by decide
@[simp] theorem zt_zpN_ne_lDg : ztN ≠ lDg := by decide
@[simp] theorem zt_lDg_ne_zpN : lDg ≠ ztN := by decide
@[simp] theorem zt_zpN_ne_lDi : ztN ≠ lDi := by decide
@[simp] theorem zt_lDi_ne_zpN : lDi ≠ ztN := by decide
@[simp] theorem zt_zpN_ne_lRp : ztN ≠ lRp := by decide
@[simp] theorem zt_lRp_ne_zpN : lRp ≠ ztN := by decide
@[simp] theorem zt_zpN_ne_lRn : ztN ≠ lRn := by decide
@[simp] theorem zt_lRn_ne_zpN : lRn ≠ ztN := by decide
@[simp] theorem zt_zpN_ne_lFls : ztN ≠ lFls := by decide
@[simp] theorem zt_lFls_ne_zpN : lFls ≠ ztN := by decide
@[simp] theorem zt_zpN_ne_lDir : ztN ≠ lDir := by decide
@[simp] theorem zt_lDir_ne_zpN : lDir ≠ ztN := by decide
@[simp] theorem zt_zpN_ne_lKb : ztN ≠ lKb := by decide
@[simp] theorem zt_lKb_ne_zpN : lKb ≠ ztN := by decide
@[simp] theorem zt_zpK_ne_zpN : ztK ≠ ztN := by decide
@[simp] theorem zt_zpK_ne_zpL : ztK ≠ ztL := by decide
@[simp] theorem zt_zpK_ne_zpU : ztK ≠ ztU := by decide
@[simp] theorem zt_zpK_ne_zpI : ztK ≠ ztI := by decide
@[simp] theorem zt_zpK_ne_zpK1 : ztK ≠ ztK1 := by decide
@[simp] theorem zt_zpK_ne_zpE : ztK ≠ ztE := by decide
@[simp] theorem zt_zpK_ne_zpV : ztK ≠ ztV := by decide
@[simp] theorem zt_zpK_ne_zpR : ztK ≠ ztR := by decide
@[simp] theorem zt_zpK_ne_lFl : ztK ≠ lFl := by decide
@[simp] theorem zt_lFl_ne_zpK : lFl ≠ ztK := by decide
@[simp] theorem zt_zpK_ne_lDh : ztK ≠ lDh := by decide
@[simp] theorem zt_lDh_ne_zpK : lDh ≠ ztK := by decide
@[simp] theorem zt_zpK_ne_lDt : ztK ≠ lDt := by decide
@[simp] theorem zt_lDt_ne_zpK : lDt ≠ ztK := by decide
@[simp] theorem zt_zpK_ne_lDg : ztK ≠ lDg := by decide
@[simp] theorem zt_lDg_ne_zpK : lDg ≠ ztK := by decide
@[simp] theorem zt_zpK_ne_lDi : ztK ≠ lDi := by decide
@[simp] theorem zt_lDi_ne_zpK : lDi ≠ ztK := by decide
@[simp] theorem zt_zpK_ne_lRp : ztK ≠ lRp := by decide
@[simp] theorem zt_lRp_ne_zpK : lRp ≠ ztK := by decide
@[simp] theorem zt_zpK_ne_lRn : ztK ≠ lRn := by decide
@[simp] theorem zt_lRn_ne_zpK : lRn ≠ ztK := by decide
@[simp] theorem zt_zpK_ne_lFls : ztK ≠ lFls := by decide
@[simp] theorem zt_lFls_ne_zpK : lFls ≠ ztK := by decide
@[simp] theorem zt_zpK_ne_lDir : ztK ≠ lDir := by decide
@[simp] theorem zt_lDir_ne_zpK : lDir ≠ ztK := by decide
@[simp] theorem zt_zpK_ne_lKb : ztK ≠ lKb := by decide
@[simp] theorem zt_lKb_ne_zpK : lKb ≠ ztK := by decide
@[simp] theorem zt_zpL_ne_zpN : ztL ≠ ztN := by decide
@[simp] theorem zt_zpL_ne_zpK : ztL ≠ ztK := by decide
@[simp] theorem zt_zpL_ne_zpU : ztL ≠ ztU := by decide
@[simp] theorem zt_zpL_ne_zpI : ztL ≠ ztI := by decide
@[simp] theorem zt_zpL_ne_zpK1 : ztL ≠ ztK1 := by decide
@[simp] theorem zt_zpL_ne_zpE : ztL ≠ ztE := by decide
@[simp] theorem zt_zpL_ne_zpV : ztL ≠ ztV := by decide
@[simp] theorem zt_zpL_ne_zpR : ztL ≠ ztR := by decide
@[simp] theorem zt_zpL_ne_lFl : ztL ≠ lFl := by decide
@[simp] theorem zt_lFl_ne_zpL : lFl ≠ ztL := by decide
@[simp] theorem zt_zpL_ne_lDh : ztL ≠ lDh := by decide
@[simp] theorem zt_lDh_ne_zpL : lDh ≠ ztL := by decide
@[simp] theorem zt_zpL_ne_lDt : ztL ≠ lDt := by decide
@[simp] theorem zt_lDt_ne_zpL : lDt ≠ ztL := by decide
@[simp] theorem zt_zpL_ne_lDg : ztL ≠ lDg := by decide
@[simp] theorem zt_lDg_ne_zpL : lDg ≠ ztL := by decide
@[simp] theorem zt_zpL_ne_lDi : ztL ≠ lDi := by decide
@[simp] theorem zt_lDi_ne_zpL : lDi ≠ ztL := by decide
@[simp] theorem zt_zpL_ne_lRp : ztL ≠ lRp := by decide
@[simp] theorem zt_lRp_ne_zpL : lRp ≠ ztL := by decide
@[simp] theorem zt_zpL_ne_lRn : ztL ≠ lRn := by decide
@[simp] theorem zt_lRn_ne_zpL : lRn ≠ ztL := by decide
@[simp] theorem zt_zpL_ne_lFls : ztL ≠ lFls := by decide
@[simp] theorem zt_lFls_ne_zpL : lFls ≠ ztL := by decide
@[simp] theorem zt_zpL_ne_lDir : ztL ≠ lDir := by decide
@[simp] theorem zt_lDir_ne_zpL : lDir ≠ ztL := by decide
@[simp] theorem zt_zpL_ne_lKb : ztL ≠ lKb := by decide
@[simp] theorem zt_lKb_ne_zpL : lKb ≠ ztL := by decide
@[simp] theorem zt_zpU_ne_zpN : ztU ≠ ztN := by decide
@[simp] theorem zt_zpU_ne_zpK : ztU ≠ ztK := by decide
@[simp] theorem zt_zpU_ne_zpL : ztU ≠ ztL := by decide
@[simp] theorem zt_zpU_ne_zpI : ztU ≠ ztI := by decide
@[simp] theorem zt_zpU_ne_zpK1 : ztU ≠ ztK1 := by decide
@[simp] theorem zt_zpU_ne_zpE : ztU ≠ ztE := by decide
@[simp] theorem zt_zpU_ne_zpV : ztU ≠ ztV := by decide
@[simp] theorem zt_zpU_ne_zpR : ztU ≠ ztR := by decide
@[simp] theorem zt_zpU_ne_lFl : ztU ≠ lFl := by decide
@[simp] theorem zt_lFl_ne_zpU : lFl ≠ ztU := by decide
@[simp] theorem zt_zpU_ne_lDh : ztU ≠ lDh := by decide
@[simp] theorem zt_lDh_ne_zpU : lDh ≠ ztU := by decide
@[simp] theorem zt_zpU_ne_lDt : ztU ≠ lDt := by decide
@[simp] theorem zt_lDt_ne_zpU : lDt ≠ ztU := by decide
@[simp] theorem zt_zpU_ne_lDg : ztU ≠ lDg := by decide
@[simp] theorem zt_lDg_ne_zpU : lDg ≠ ztU := by decide
@[simp] theorem zt_zpU_ne_lDi : ztU ≠ lDi := by decide
@[simp] theorem zt_lDi_ne_zpU : lDi ≠ ztU := by decide
@[simp] theorem zt_zpU_ne_lRp : ztU ≠ lRp := by decide
@[simp] theorem zt_lRp_ne_zpU : lRp ≠ ztU := by decide
@[simp] theorem zt_zpU_ne_lRn : ztU ≠ lRn := by decide
@[simp] theorem zt_lRn_ne_zpU : lRn ≠ ztU := by decide
@[simp] theorem zt_zpU_ne_lFls : ztU ≠ lFls := by decide
@[simp] theorem zt_lFls_ne_zpU : lFls ≠ ztU := by decide
@[simp] theorem zt_zpU_ne_lDir : ztU ≠ lDir := by decide
@[simp] theorem zt_lDir_ne_zpU : lDir ≠ ztU := by decide
@[simp] theorem zt_zpU_ne_lKb : ztU ≠ lKb := by decide
@[simp] theorem zt_lKb_ne_zpU : lKb ≠ ztU := by decide
@[simp] theorem zt_zpI_ne_zpN : ztI ≠ ztN := by decide
@[simp] theorem zt_zpI_ne_zpK : ztI ≠ ztK := by decide
@[simp] theorem zt_zpI_ne_zpL : ztI ≠ ztL := by decide
@[simp] theorem zt_zpI_ne_zpU : ztI ≠ ztU := by decide
@[simp] theorem zt_zpI_ne_zpK1 : ztI ≠ ztK1 := by decide
@[simp] theorem zt_zpI_ne_zpE : ztI ≠ ztE := by decide
@[simp] theorem zt_zpI_ne_zpV : ztI ≠ ztV := by decide
@[simp] theorem zt_zpI_ne_zpR : ztI ≠ ztR := by decide
@[simp] theorem zt_zpI_ne_lFl : ztI ≠ lFl := by decide
@[simp] theorem zt_lFl_ne_zpI : lFl ≠ ztI := by decide
@[simp] theorem zt_zpI_ne_lDh : ztI ≠ lDh := by decide
@[simp] theorem zt_lDh_ne_zpI : lDh ≠ ztI := by decide
@[simp] theorem zt_zpI_ne_lDt : ztI ≠ lDt := by decide
@[simp] theorem zt_lDt_ne_zpI : lDt ≠ ztI := by decide
@[simp] theorem zt_zpI_ne_lDg : ztI ≠ lDg := by decide
@[simp] theorem zt_lDg_ne_zpI : lDg ≠ ztI := by decide
@[simp] theorem zt_zpI_ne_lDi : ztI ≠ lDi := by decide
@[simp] theorem zt_lDi_ne_zpI : lDi ≠ ztI := by decide
@[simp] theorem zt_zpI_ne_lRp : ztI ≠ lRp := by decide
@[simp] theorem zt_lRp_ne_zpI : lRp ≠ ztI := by decide
@[simp] theorem zt_zpI_ne_lRn : ztI ≠ lRn := by decide
@[simp] theorem zt_lRn_ne_zpI : lRn ≠ ztI := by decide
@[simp] theorem zt_zpI_ne_lFls : ztI ≠ lFls := by decide
@[simp] theorem zt_lFls_ne_zpI : lFls ≠ ztI := by decide
@[simp] theorem zt_zpI_ne_lDir : ztI ≠ lDir := by decide
@[simp] theorem zt_lDir_ne_zpI : lDir ≠ ztI := by decide
@[simp] theorem zt_zpI_ne_lKb : ztI ≠ lKb := by decide
@[simp] theorem zt_lKb_ne_zpI : lKb ≠ ztI := by decide
@[simp] theorem zt_zpK1_ne_zpN : ztK1 ≠ ztN := by decide
@[simp] theorem zt_zpK1_ne_zpK : ztK1 ≠ ztK := by decide
@[simp] theorem zt_zpK1_ne_zpL : ztK1 ≠ ztL := by decide
@[simp] theorem zt_zpK1_ne_zpU : ztK1 ≠ ztU := by decide
@[simp] theorem zt_zpK1_ne_zpI : ztK1 ≠ ztI := by decide
@[simp] theorem zt_zpK1_ne_zpE : ztK1 ≠ ztE := by decide
@[simp] theorem zt_zpK1_ne_zpV : ztK1 ≠ ztV := by decide
@[simp] theorem zt_zpK1_ne_zpR : ztK1 ≠ ztR := by decide
@[simp] theorem zt_zpK1_ne_lFl : ztK1 ≠ lFl := by decide
@[simp] theorem zt_lFl_ne_zpK1 : lFl ≠ ztK1 := by decide
@[simp] theorem zt_zpK1_ne_lDh : ztK1 ≠ lDh := by decide
@[simp] theorem zt_lDh_ne_zpK1 : lDh ≠ ztK1 := by decide
@[simp] theorem zt_zpK1_ne_lDt : ztK1 ≠ lDt := by decide
@[simp] theorem zt_lDt_ne_zpK1 : lDt ≠ ztK1 := by decide
@[simp] theorem zt_zpK1_ne_lDg : ztK1 ≠ lDg := by decide
@[simp] theorem zt_lDg_ne_zpK1 : lDg ≠ ztK1 := by decide
@[simp] theorem zt_zpK1_ne_lDi : ztK1 ≠ lDi := by decide
@[simp] theorem zt_lDi_ne_zpK1 : lDi ≠ ztK1 := by decide
@[simp] theorem zt_zpK1_ne_lRp : ztK1 ≠ lRp := by decide
@[simp] theorem zt_lRp_ne_zpK1 : lRp ≠ ztK1 := by decide
@[simp] theorem zt_zpK1_ne_lRn : ztK1 ≠ lRn := by decide
@[simp] theorem zt_lRn_ne_zpK1 : lRn ≠ ztK1 := by decide
@[simp] theorem zt_zpK1_ne_lFls : ztK1 ≠ lFls := by decide
@[simp] theorem zt_lFls_ne_zpK1 : lFls ≠ ztK1 := by decide
@[simp] theorem zt_zpK1_ne_lDir : ztK1 ≠ lDir := by decide
@[simp] theorem zt_lDir_ne_zpK1 : lDir ≠ ztK1 := by decide
@[simp] theorem zt_zpK1_ne_lKb : ztK1 ≠ lKb := by decide
@[simp] theorem zt_lKb_ne_zpK1 : lKb ≠ ztK1 := by decide
@[simp] theorem zt_zpE_ne_zpN : ztE ≠ ztN := by decide
@[simp] theorem zt_zpE_ne_zpK : ztE ≠ ztK := by decide
@[simp] theorem zt_zpE_ne_zpL : ztE ≠ ztL := by decide
@[simp] theorem zt_zpE_ne_zpU : ztE ≠ ztU := by decide
@[simp] theorem zt_zpE_ne_zpI : ztE ≠ ztI := by decide
@[simp] theorem zt_zpE_ne_zpK1 : ztE ≠ ztK1 := by decide
@[simp] theorem zt_zpE_ne_zpV : ztE ≠ ztV := by decide
@[simp] theorem zt_zpE_ne_zpR : ztE ≠ ztR := by decide
@[simp] theorem zt_zpE_ne_lFl : ztE ≠ lFl := by decide
@[simp] theorem zt_lFl_ne_zpE : lFl ≠ ztE := by decide
@[simp] theorem zt_zpE_ne_lDh : ztE ≠ lDh := by decide
@[simp] theorem zt_lDh_ne_zpE : lDh ≠ ztE := by decide
@[simp] theorem zt_zpE_ne_lDt : ztE ≠ lDt := by decide
@[simp] theorem zt_lDt_ne_zpE : lDt ≠ ztE := by decide
@[simp] theorem zt_zpE_ne_lDg : ztE ≠ lDg := by decide
@[simp] theorem zt_lDg_ne_zpE : lDg ≠ ztE := by decide
@[simp] theorem zt_zpE_ne_lDi : ztE ≠ lDi := by decide
@[simp] theorem zt_lDi_ne_zpE : lDi ≠ ztE := by decide
@[simp] theorem zt_zpE_ne_lRp : ztE ≠ lRp := by decide
@[simp] theorem zt_lRp_ne_zpE : lRp ≠ ztE := by decide
@[simp] theorem zt_zpE_ne_lRn : ztE ≠ lRn := by decide
@[simp] theorem zt_lRn_ne_zpE : lRn ≠ ztE := by decide
@[simp] theorem zt_zpE_ne_lFls : ztE ≠ lFls := by decide
@[simp] theorem zt_lFls_ne_zpE : lFls ≠ ztE := by decide
@[simp] theorem zt_zpE_ne_lDir : ztE ≠ lDir := by decide
@[simp] theorem zt_lDir_ne_zpE : lDir ≠ ztE := by decide
@[simp] theorem zt_zpE_ne_lKb : ztE ≠ lKb := by decide
@[simp] theorem zt_lKb_ne_zpE : lKb ≠ ztE := by decide
@[simp] theorem zt_zpV_ne_zpN : ztV ≠ ztN := by decide
@[simp] theorem zt_zpV_ne_zpK : ztV ≠ ztK := by decide
@[simp] theorem zt_zpV_ne_zpL : ztV ≠ ztL := by decide
@[simp] theorem zt_zpV_ne_zpU : ztV ≠ ztU := by decide
@[simp] theorem zt_zpV_ne_zpI : ztV ≠ ztI := by decide
@[simp] theorem zt_zpV_ne_zpK1 : ztV ≠ ztK1 := by decide
@[simp] theorem zt_zpV_ne_zpE : ztV ≠ ztE := by decide
@[simp] theorem zt_zpV_ne_zpR : ztV ≠ ztR := by decide
@[simp] theorem zt_zpV_ne_lFl : ztV ≠ lFl := by decide
@[simp] theorem zt_lFl_ne_zpV : lFl ≠ ztV := by decide
@[simp] theorem zt_zpV_ne_lDh : ztV ≠ lDh := by decide
@[simp] theorem zt_lDh_ne_zpV : lDh ≠ ztV := by decide
@[simp] theorem zt_zpV_ne_lDt : ztV ≠ lDt := by decide
@[simp] theorem zt_lDt_ne_zpV : lDt ≠ ztV := by decide
@[simp] theorem zt_zpV_ne_lDg : ztV ≠ lDg := by decide
@[simp] theorem zt_lDg_ne_zpV : lDg ≠ ztV := by decide
@[simp] theorem zt_zpV_ne_lDi : ztV ≠ lDi := by decide
@[simp] theorem zt_lDi_ne_zpV : lDi ≠ ztV := by decide
@[simp] theorem zt_zpV_ne_lRp : ztV ≠ lRp := by decide
@[simp] theorem zt_lRp_ne_zpV : lRp ≠ ztV := by decide
@[simp] theorem zt_zpV_ne_lRn : ztV ≠ lRn := by decide
@[simp] theorem zt_lRn_ne_zpV : lRn ≠ ztV := by decide
@[simp] theorem zt_zpV_ne_lFls : ztV ≠ lFls := by decide
@[simp] theorem zt_lFls_ne_zpV : lFls ≠ ztV := by decide
@[simp] theorem zt_zpV_ne_lDir : ztV ≠ lDir := by decide
@[simp] theorem zt_lDir_ne_zpV : lDir ≠ ztV := by decide
@[simp] theorem zt_zpV_ne_lKb : ztV ≠ lKb := by decide
@[simp] theorem zt_lKb_ne_zpV : lKb ≠ ztV := by decide
@[simp] theorem zt_zpR_ne_zpN : ztR ≠ ztN := by decide
@[simp] theorem zt_zpR_ne_zpK : ztR ≠ ztK := by decide
@[simp] theorem zt_zpR_ne_zpL : ztR ≠ ztL := by decide
@[simp] theorem zt_zpR_ne_zpU : ztR ≠ ztU := by decide
@[simp] theorem zt_zpR_ne_zpI : ztR ≠ ztI := by decide
@[simp] theorem zt_zpR_ne_zpK1 : ztR ≠ ztK1 := by decide
@[simp] theorem zt_zpR_ne_zpE : ztR ≠ ztE := by decide
@[simp] theorem zt_zpR_ne_zpV : ztR ≠ ztV := by decide
@[simp] theorem zt_zpR_ne_lFl : ztR ≠ lFl := by decide
@[simp] theorem zt_lFl_ne_zpR : lFl ≠ ztR := by decide
@[simp] theorem zt_zpR_ne_lDh : ztR ≠ lDh := by decide
@[simp] theorem zt_lDh_ne_zpR : lDh ≠ ztR := by decide
@[simp] theorem zt_zpR_ne_lDt : ztR ≠ lDt := by decide
@[simp] theorem zt_lDt_ne_zpR : lDt ≠ ztR := by decide
@[simp] theorem zt_zpR_ne_lDg : ztR ≠ lDg := by decide
@[simp] theorem zt_lDg_ne_zpR : lDg ≠ ztR := by decide
@[simp] theorem zt_zpR_ne_lDi : ztR ≠ lDi := by decide
@[simp] theorem zt_lDi_ne_zpR : lDi ≠ ztR := by decide
@[simp] theorem zt_zpR_ne_lRp : ztR ≠ lRp := by decide
@[simp] theorem zt_lRp_ne_zpR : lRp ≠ ztR := by decide
@[simp] theorem zt_zpR_ne_lRn : ztR ≠ lRn := by decide
@[simp] theorem zt_lRn_ne_zpR : lRn ≠ ztR := by decide
@[simp] theorem zt_zpR_ne_lFls : ztR ≠ lFls := by decide
@[simp] theorem zt_lFls_ne_zpR : lFls ≠ ztR := by decide
@[simp] theorem zt_zpR_ne_lDir : ztR ≠ lDir := by decide
@[simp] theorem zt_lDir_ne_zpR : lDir ≠ ztR := by decide
@[simp] theorem zt_zpR_ne_lKb : ztR ≠ lKb := by decide
@[simp] theorem zt_lKb_ne_zpR : lKb ≠ ztR := by decide

def ztParams : List MlS := [ztN, ztK, ztL, ztU, ztI]
def ztLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, ztK1, ztE, ztV, ztR]

/-- `ztN` the name, `ztK` the names' first cell, `ztL` their count, `ztU` the arguments' list handle, `ztI` the
position. -/
def ztBody : ProgHOL 64 := prologue ztLocals
  (.ite (.cmp .equal (vv ztI) (vv ztL)) (.return (.const 0))
  (.seq (.assign .local lFl (vv lFls)) (.seq (.assign .local lDh (vv ztU)) (.seq lsViewP
  (.ite (.cmp .lower (vv ztI) (vv lRn))
    (.seq (.assign .local ztK1 (.load .one (.op .add [vv ztK, .shift .lsl (vv ztI) (.const 3)])))
    (.seq (.call (some (some (.local, ztE), none)) NEq.fNeq [vv ztK1, vv ztN])
    (.ite (vv ztE)
      (.seq (.assign .local lFl (vv lFls)) (.seq (.assign .local lDh (vv ztU)) (.seq lsViewP
      (.seq (.assign .local ztV (.load .one (.op .add [vv lRp, .shift .lsl (vv ztI) (.const 3)])))
      (.seq (.call (some (some (.local, ztR), none)) fZe0 [vv ztV]) (.return (vv ztR)))))))
      (.seq (.call (some (some (.local, ztR), none)) fZt [vv ztN, vv ztK, vv ztL, vv ztU, .op .add [vv ztI, .const 1]])
        (.return (vv ztR))))))
    (.return (.const 0)))))))

section
variable {σ : Type}

theorem zt_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ztLocals → (ctxEnv C ++ ztParams.zip vals).get x = none :=
  Knot.params_none C ztLocals ztParams vals (by decide) (by decide)



theorem zt_spec (C : Ctx) (hcf : C.code.lookup fZt = some (ztParams.map (fun p => (p, ShapeHOL.one)), ztBody, .one))
    (hcn : C.code.lookup NEq.fNeq = some ([(NEq.pNa, .one), (NEq.pNb, .one)], NEq.neqBody, .one))
    (hcz : C.code.lookup fZe0 = some ([(zeU, ShapeHOL.one)], zeBody, .one)) (s : AState)
    (hwf : LStoreWF s.store.ls)
    (khs : List NIdx) (ks : List ConLeche.Name) (ok : Nat)
    (hks : ∀ j (hj : j < khs.length), C.EH[ok + j]? = some (Enc.idxW khs[j])) (hkl : ks.length = khs.length)
    (hkd : ∀ j (hj : j < khs.length), ∃ f, denoteNAux s.store.ns f khs[j] = some (ks[j]'(by omega)))
    (hklen : khs.length < 2 ^ 60)
    (us : LsIdx) (uh : List LIdx) (vs : List ConLeche.Level) (huv : s.store.lss.view us = some uh)
    (hvl : vs.length = uh.length) (hvd : ∀ j (hj : j < uh.length), denoteL s.store.ls uh[j] = some (vs[j]'(by omega)))
    (n : NIdx) (nm : ConLeche.Name) (fn : Nat) (hn : denoteNAux s.store.ns fn n = some nm) :
    ∀ k i, khs.length - i = k → i ≤ khs.length →
      SpecR (σ := σ) (Pre C s (ztParams.zip [Enc.idxW n, ecell C ok, BitVec.ofNat 64 khs.length, Enc.idxW us,
        BitVec.ofNat 64 i])) ztBody s (pure (ze (ConLeche.Level.subst.go (ks.drop i) (vs.drop i) nm)) : AM Bool)
        (PostBS C s) := by
  intro k
  induction k with
  | zero =>
    intro i hk hi
    have hi' : i = khs.length := by omega
    subst hi'
    refine specR_prologue (postBS_locals C s) (zt_none C _) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ztParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_of_length_le (by omega)]
    exact specR_returnI _ (boolW false) (by simp [boolW]; rfl)
      (fun t ht => ⟨rfl, by simp [ConLeche.Level.subst.go, ze], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro i hk hi
    have hil : i < khs.length := by omega
    refine specR_prologue (postBS_locals C s) (zt_none C _) ?_
    have hne : BitVec.ofNat 64 i ≠ BitVec.ofNat 64 khs.length := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ztParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv ztU) (Enc.idxW us) (by decide) (by simp +decide [Env.get, ztParams, ctxEnv]) ?_
    refine specR_lsviewPI us (by simp) (by simp) (by simp +decide [Env.get, ctxEnv]) (by decide)
      (fun vl Pl hvl _ hvll => ?_)
    rw [huv] at hvl
    cases hvl
    have hul : uh.length < 2 ^ 61 := by simpa using hvll
    rw [List.drop_eq_getElem_cons (show i < ks.length by omega)]
    by_cases hiv : i < uh.length
    swap
    · have hlw := word_lt_iff i uh.length (by unfold B; omega) (by unfold B; omega)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ztParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega)
        (fun h => absurd rfl h) (fun _ => ?_)
      rw [List.drop_of_length_le (show vs.length ≤ i by omega)]
      exact specR_returnI _ (boolW false) (by simp [boolW]; rfl)
        (fun t ht => ⟨rfl, by simp [ConLeche.Level.subst.go, ze], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    have hlw := word_lt_iff i uh.length (by unfold B; omega) (by unfold B; omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ztParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega) (fun _ => ?_)
      (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons (show i < vs.length by omega)]
    refine specR_envLoadI ztK1 _ (ok + i) _ (by decide)
      (by simp +decide [sev, Env.get, ztParams, ctxEnv]; exact ecell_shl3 C ok i (by omega)) (hks i hil) ?_
    refine specR_dropM ?_
    obtain ⟨fk, hfk⟩ := hkd i hil
    refine specR_callPure ztE NEq.fNeq [NEq.pNa, NEq.pNb] [vv ztK1, vv ztN] NEq.neqBody [Enc.idxW khs[i], Enc.idxW n]
      (decide (ks[i] = nm)) (by decide) rfl (by decide) hcn ⟨by simp, by simp +decide [Env.get, ztParams, ctxEnv], trivial⟩
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
      refine specR_assignI lDh (vv ztU) (Enc.idxW us) (by decide) (by simp +decide [Env.get, ztParams, ctxEnv]) ?_
      refine specR_lsviewPI (C := ctxH C C.H) us (by simp) (by simp <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
        (fun vl2 Pl2 hvl2 _ _ => ?_)
      rw [huv] at hvl2
      cases hvl2
      refine specR_loadI' ztV _ (Pl2 + BitVec.ofNat 64 (8 * i)) (Pl2 + BitVec.ofNat 64 (8 * i)) (Enc.idxW uh[i])
        (by decide) (by simp +decide [sev, Env.get, ztParams, ctxEnv]; rw [Str.w_shl i 3 (by omega), show i * 2 ^ 3 = 8 * i by omega]) rfl
        (by have h := wordsAt_get Pl2 (uh.map Enc.idxW) i (by simpa using hiv) []; simp only [List.getElem_map] at h; exact h) ?_
      refine specR_dropM ?_
      refine specR_callPure (C := ctxH C C.H) ztR fZe0 [zeU] [vv ztV] zeBody [Enc.idxW uh[i]] (ze (vs[i]'(by omega)))
        (by decide) rfl (by decide) hcz ⟨by simp, trivial⟩ (PostBS (ctxH C C.H) s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
        (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [zeU] _ rfl hlk)
          (ze0_spec (ctxH C C.H) hcz s hwf _ uh[i] (hvd i hiv)))
        (fun w H2 hp2 ⟨eH, hw⟩ => ?_)
      subst H2; subst hw
      exact specR_returnI _ (boolW (ze (vs[i]'(by omega)))) (by simp)
        (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_ifI _ 0 (by simp [sev, boolW, heq]) (fun h => absurd rfl h) (fun _ => ?_)
      simp only [ConLeche.Level.subst.go, heq, ite_false]
      refine specR_callPure (C := ctxH C C.H) ztR fZt ztParams
        [vv ztN, vv ztK, vv ztL, vv ztU, .op .add [vv ztI, .const 1]] ztBody
        [Enc.idxW n, ecell C ok, BitVec.ofNat 64 khs.length, Enc.idxW us, BitVec.ofNat 64 (i + 1)]
        (ze (ConLeche.Level.subst.go (ks.drop (i + 1)) (vs.drop (i + 1)) nm)) (by decide) rfl (by decide) hcf
        ⟨by simp +decide [Env.get, ztParams, ctxEnv], by simp +decide [Env.get, ztParams, ctxEnv] <;> rfl,
          by simp +decide [Env.get, ztParams, ctxEnv], by simp +decide [Env.get, ztParams, ctxEnv],
          by simp +decide [sev, Env.get, ztParams, ctxEnv]; exact word_add1_eq i, trivial⟩
        (PostBS C s) (fun b w _ H' => H' = C.H ∧ w = boolW b)
        (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨C.H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ztParams _ rfl hlk) (ih (i + 1) (by omega) (by omega)))
        (fun w H2 hp2 ⟨eH2, hw⟩ => ?_)
      subst H2; subst hw
      exact specR_returnI _ _ (by simp) (fun t ht => ⟨rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
