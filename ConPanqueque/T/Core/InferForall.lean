import ConPanqueque.T.Core.InferPis
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# The ∀ arm's wrapper: `inferForall`

Infer the domain's type, `whnf` it to a sort, open the binder with a fresh free variable, then run the
`inferPis` loop from `k = 1` with singleton blocks `[fv]` and `[u]` (built by appending to one empty block).
A depth of `2 ^ 62` or more is a resource-limit decline (halt): it keeps every `d + k + peel` below `2 ^ 63`.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def qfA := ofString "qfn_a"
def qfH := ofString "qfn_h"
def qfU := ofString "qfn_u"
def qfV := ofString "qfn_v"
def qfE := ofString "qfn_e"
def qfF := ofString "qfn_f"
def qfS := ofString "qfn_s"
def qfR := ofString "qfn_r"

@[simp] theorem qf_qfA_ne_qfH : qfA ≠ qfH := by decide
@[simp] theorem qf_qfA_ne_qfU : qfA ≠ qfU := by decide
@[simp] theorem qf_qfA_ne_qfV : qfA ≠ qfV := by decide
@[simp] theorem qf_qfA_ne_qfE : qfA ≠ qfE := by decide
@[simp] theorem qf_qfA_ne_qfF : qfA ≠ qfF := by decide
@[simp] theorem qf_qfA_ne_qfS : qfA ≠ qfS := by decide
@[simp] theorem qf_qfA_ne_qfR : qfA ≠ qfR := by decide
@[simp] theorem qf_qfA_ne_kFu : qfA ≠ kFu := by decide
@[simp] theorem qf_kFu_ne_qfA : kFu ≠ qfA := by decide
@[simp] theorem qf_qfA_ne_kD : qfA ≠ kD := by decide
@[simp] theorem qf_kD_ne_qfA : kD ≠ qfA := by decide
@[simp] theorem qf_qfA_ne_ibT1 : qfA ≠ ibT1 := by decide
@[simp] theorem qf_ibT1_ne_qfA : ibT1 ≠ qfA := by decide
@[simp] theorem qf_qfA_ne_ibT2 : qfA ≠ ibT2 := by decide
@[simp] theorem qf_ibT2_ne_qfA : ibT2 ≠ qfA := by decide
@[simp] theorem qf_qfA_ne_lFl : qfA ≠ lFl := by decide
@[simp] theorem qf_lFl_ne_qfA : lFl ≠ qfA := by decide
@[simp] theorem qf_qfA_ne_lDh : qfA ≠ lDh := by decide
@[simp] theorem qf_lDh_ne_qfA : lDh ≠ qfA := by decide
@[simp] theorem qf_qfA_ne_lDt : qfA ≠ lDt := by decide
@[simp] theorem qf_lDt_ne_qfA : lDt ≠ qfA := by decide
@[simp] theorem qf_qfA_ne_lDg : qfA ≠ lDg := by decide
@[simp] theorem qf_lDg_ne_qfA : lDg ≠ qfA := by decide
@[simp] theorem qf_qfA_ne_lDi : qfA ≠ lDi := by decide
@[simp] theorem qf_lDi_ne_qfA : lDi ≠ qfA := by decide
@[simp] theorem qf_qfA_ne_lRp : qfA ≠ lRp := by decide
@[simp] theorem qf_lRp_ne_qfA : lRp ≠ qfA := by decide
@[simp] theorem qf_qfA_ne_lRn : qfA ≠ lRn := by decide
@[simp] theorem qf_lRn_ne_qfA : lRn ≠ qfA := by decide
@[simp] theorem qf_qfA_ne_lDir : qfA ≠ lDir := by decide
@[simp] theorem qf_lDir_ne_qfA : lDir ≠ qfA := by decide
@[simp] theorem qf_qfA_ne_lFle : qfA ≠ lFle := by decide
@[simp] theorem qf_lFle_ne_qfA : lFle ≠ qfA := by decide
@[simp] theorem qf_qfA_ne_lKb : qfA ≠ lKb := by decide
@[simp] theorem qf_lKb_ne_qfA : lKb ≠ qfA := by decide
@[simp] theorem qf_qfH_ne_qfA : qfH ≠ qfA := by decide
@[simp] theorem qf_qfH_ne_qfU : qfH ≠ qfU := by decide
@[simp] theorem qf_qfH_ne_qfV : qfH ≠ qfV := by decide
@[simp] theorem qf_qfH_ne_qfE : qfH ≠ qfE := by decide
@[simp] theorem qf_qfH_ne_qfF : qfH ≠ qfF := by decide
@[simp] theorem qf_qfH_ne_qfS : qfH ≠ qfS := by decide
@[simp] theorem qf_qfH_ne_qfR : qfH ≠ qfR := by decide
@[simp] theorem qf_qfH_ne_kFu : qfH ≠ kFu := by decide
@[simp] theorem qf_kFu_ne_qfH : kFu ≠ qfH := by decide
@[simp] theorem qf_qfH_ne_kD : qfH ≠ kD := by decide
@[simp] theorem qf_kD_ne_qfH : kD ≠ qfH := by decide
@[simp] theorem qf_qfH_ne_ibT1 : qfH ≠ ibT1 := by decide
@[simp] theorem qf_ibT1_ne_qfH : ibT1 ≠ qfH := by decide
@[simp] theorem qf_qfH_ne_ibT2 : qfH ≠ ibT2 := by decide
@[simp] theorem qf_ibT2_ne_qfH : ibT2 ≠ qfH := by decide
@[simp] theorem qf_qfH_ne_lFl : qfH ≠ lFl := by decide
@[simp] theorem qf_lFl_ne_qfH : lFl ≠ qfH := by decide
@[simp] theorem qf_qfH_ne_lDh : qfH ≠ lDh := by decide
@[simp] theorem qf_lDh_ne_qfH : lDh ≠ qfH := by decide
@[simp] theorem qf_qfH_ne_lDt : qfH ≠ lDt := by decide
@[simp] theorem qf_lDt_ne_qfH : lDt ≠ qfH := by decide
@[simp] theorem qf_qfH_ne_lDg : qfH ≠ lDg := by decide
@[simp] theorem qf_lDg_ne_qfH : lDg ≠ qfH := by decide
@[simp] theorem qf_qfH_ne_lDi : qfH ≠ lDi := by decide
@[simp] theorem qf_lDi_ne_qfH : lDi ≠ qfH := by decide
@[simp] theorem qf_qfH_ne_lRp : qfH ≠ lRp := by decide
@[simp] theorem qf_lRp_ne_qfH : lRp ≠ qfH := by decide
@[simp] theorem qf_qfH_ne_lRn : qfH ≠ lRn := by decide
@[simp] theorem qf_lRn_ne_qfH : lRn ≠ qfH := by decide
@[simp] theorem qf_qfH_ne_lDir : qfH ≠ lDir := by decide
@[simp] theorem qf_lDir_ne_qfH : lDir ≠ qfH := by decide
@[simp] theorem qf_qfH_ne_lFle : qfH ≠ lFle := by decide
@[simp] theorem qf_lFle_ne_qfH : lFle ≠ qfH := by decide
@[simp] theorem qf_qfH_ne_lKb : qfH ≠ lKb := by decide
@[simp] theorem qf_lKb_ne_qfH : lKb ≠ qfH := by decide
@[simp] theorem qf_qfU_ne_qfA : qfU ≠ qfA := by decide
@[simp] theorem qf_qfU_ne_qfH : qfU ≠ qfH := by decide
@[simp] theorem qf_qfU_ne_qfV : qfU ≠ qfV := by decide
@[simp] theorem qf_qfU_ne_qfE : qfU ≠ qfE := by decide
@[simp] theorem qf_qfU_ne_qfF : qfU ≠ qfF := by decide
@[simp] theorem qf_qfU_ne_qfS : qfU ≠ qfS := by decide
@[simp] theorem qf_qfU_ne_qfR : qfU ≠ qfR := by decide
@[simp] theorem qf_qfU_ne_kFu : qfU ≠ kFu := by decide
@[simp] theorem qf_kFu_ne_qfU : kFu ≠ qfU := by decide
@[simp] theorem qf_qfU_ne_kD : qfU ≠ kD := by decide
@[simp] theorem qf_kD_ne_qfU : kD ≠ qfU := by decide
@[simp] theorem qf_qfU_ne_ibT1 : qfU ≠ ibT1 := by decide
@[simp] theorem qf_ibT1_ne_qfU : ibT1 ≠ qfU := by decide
@[simp] theorem qf_qfU_ne_ibT2 : qfU ≠ ibT2 := by decide
@[simp] theorem qf_ibT2_ne_qfU : ibT2 ≠ qfU := by decide
@[simp] theorem qf_qfU_ne_lFl : qfU ≠ lFl := by decide
@[simp] theorem qf_lFl_ne_qfU : lFl ≠ qfU := by decide
@[simp] theorem qf_qfU_ne_lDh : qfU ≠ lDh := by decide
@[simp] theorem qf_lDh_ne_qfU : lDh ≠ qfU := by decide
@[simp] theorem qf_qfU_ne_lDt : qfU ≠ lDt := by decide
@[simp] theorem qf_lDt_ne_qfU : lDt ≠ qfU := by decide
@[simp] theorem qf_qfU_ne_lDg : qfU ≠ lDg := by decide
@[simp] theorem qf_lDg_ne_qfU : lDg ≠ qfU := by decide
@[simp] theorem qf_qfU_ne_lDi : qfU ≠ lDi := by decide
@[simp] theorem qf_lDi_ne_qfU : lDi ≠ qfU := by decide
@[simp] theorem qf_qfU_ne_lRp : qfU ≠ lRp := by decide
@[simp] theorem qf_lRp_ne_qfU : lRp ≠ qfU := by decide
@[simp] theorem qf_qfU_ne_lRn : qfU ≠ lRn := by decide
@[simp] theorem qf_lRn_ne_qfU : lRn ≠ qfU := by decide
@[simp] theorem qf_qfU_ne_lDir : qfU ≠ lDir := by decide
@[simp] theorem qf_lDir_ne_qfU : lDir ≠ qfU := by decide
@[simp] theorem qf_qfU_ne_lFle : qfU ≠ lFle := by decide
@[simp] theorem qf_lFle_ne_qfU : lFle ≠ qfU := by decide
@[simp] theorem qf_qfU_ne_lKb : qfU ≠ lKb := by decide
@[simp] theorem qf_lKb_ne_qfU : lKb ≠ qfU := by decide
@[simp] theorem qf_qfV_ne_qfA : qfV ≠ qfA := by decide
@[simp] theorem qf_qfV_ne_qfH : qfV ≠ qfH := by decide
@[simp] theorem qf_qfV_ne_qfU : qfV ≠ qfU := by decide
@[simp] theorem qf_qfV_ne_qfE : qfV ≠ qfE := by decide
@[simp] theorem qf_qfV_ne_qfF : qfV ≠ qfF := by decide
@[simp] theorem qf_qfV_ne_qfS : qfV ≠ qfS := by decide
@[simp] theorem qf_qfV_ne_qfR : qfV ≠ qfR := by decide
@[simp] theorem qf_qfV_ne_kFu : qfV ≠ kFu := by decide
@[simp] theorem qf_kFu_ne_qfV : kFu ≠ qfV := by decide
@[simp] theorem qf_qfV_ne_kD : qfV ≠ kD := by decide
@[simp] theorem qf_kD_ne_qfV : kD ≠ qfV := by decide
@[simp] theorem qf_qfV_ne_ibT1 : qfV ≠ ibT1 := by decide
@[simp] theorem qf_ibT1_ne_qfV : ibT1 ≠ qfV := by decide
@[simp] theorem qf_qfV_ne_ibT2 : qfV ≠ ibT2 := by decide
@[simp] theorem qf_ibT2_ne_qfV : ibT2 ≠ qfV := by decide
@[simp] theorem qf_qfV_ne_lFl : qfV ≠ lFl := by decide
@[simp] theorem qf_lFl_ne_qfV : lFl ≠ qfV := by decide
@[simp] theorem qf_qfV_ne_lDh : qfV ≠ lDh := by decide
@[simp] theorem qf_lDh_ne_qfV : lDh ≠ qfV := by decide
@[simp] theorem qf_qfV_ne_lDt : qfV ≠ lDt := by decide
@[simp] theorem qf_lDt_ne_qfV : lDt ≠ qfV := by decide
@[simp] theorem qf_qfV_ne_lDg : qfV ≠ lDg := by decide
@[simp] theorem qf_lDg_ne_qfV : lDg ≠ qfV := by decide
@[simp] theorem qf_qfV_ne_lDi : qfV ≠ lDi := by decide
@[simp] theorem qf_lDi_ne_qfV : lDi ≠ qfV := by decide
@[simp] theorem qf_qfV_ne_lRp : qfV ≠ lRp := by decide
@[simp] theorem qf_lRp_ne_qfV : lRp ≠ qfV := by decide
@[simp] theorem qf_qfV_ne_lRn : qfV ≠ lRn := by decide
@[simp] theorem qf_lRn_ne_qfV : lRn ≠ qfV := by decide
@[simp] theorem qf_qfV_ne_lDir : qfV ≠ lDir := by decide
@[simp] theorem qf_lDir_ne_qfV : lDir ≠ qfV := by decide
@[simp] theorem qf_qfV_ne_lFle : qfV ≠ lFle := by decide
@[simp] theorem qf_lFle_ne_qfV : lFle ≠ qfV := by decide
@[simp] theorem qf_qfV_ne_lKb : qfV ≠ lKb := by decide
@[simp] theorem qf_lKb_ne_qfV : lKb ≠ qfV := by decide
@[simp] theorem qf_qfE_ne_qfA : qfE ≠ qfA := by decide
@[simp] theorem qf_qfE_ne_qfH : qfE ≠ qfH := by decide
@[simp] theorem qf_qfE_ne_qfU : qfE ≠ qfU := by decide
@[simp] theorem qf_qfE_ne_qfV : qfE ≠ qfV := by decide
@[simp] theorem qf_qfE_ne_qfF : qfE ≠ qfF := by decide
@[simp] theorem qf_qfE_ne_qfS : qfE ≠ qfS := by decide
@[simp] theorem qf_qfE_ne_qfR : qfE ≠ qfR := by decide
@[simp] theorem qf_qfE_ne_kFu : qfE ≠ kFu := by decide
@[simp] theorem qf_kFu_ne_qfE : kFu ≠ qfE := by decide
@[simp] theorem qf_qfE_ne_kD : qfE ≠ kD := by decide
@[simp] theorem qf_kD_ne_qfE : kD ≠ qfE := by decide
@[simp] theorem qf_qfE_ne_ibT1 : qfE ≠ ibT1 := by decide
@[simp] theorem qf_ibT1_ne_qfE : ibT1 ≠ qfE := by decide
@[simp] theorem qf_qfE_ne_ibT2 : qfE ≠ ibT2 := by decide
@[simp] theorem qf_ibT2_ne_qfE : ibT2 ≠ qfE := by decide
@[simp] theorem qf_qfE_ne_lFl : qfE ≠ lFl := by decide
@[simp] theorem qf_lFl_ne_qfE : lFl ≠ qfE := by decide
@[simp] theorem qf_qfE_ne_lDh : qfE ≠ lDh := by decide
@[simp] theorem qf_lDh_ne_qfE : lDh ≠ qfE := by decide
@[simp] theorem qf_qfE_ne_lDt : qfE ≠ lDt := by decide
@[simp] theorem qf_lDt_ne_qfE : lDt ≠ qfE := by decide
@[simp] theorem qf_qfE_ne_lDg : qfE ≠ lDg := by decide
@[simp] theorem qf_lDg_ne_qfE : lDg ≠ qfE := by decide
@[simp] theorem qf_qfE_ne_lDi : qfE ≠ lDi := by decide
@[simp] theorem qf_lDi_ne_qfE : lDi ≠ qfE := by decide
@[simp] theorem qf_qfE_ne_lRp : qfE ≠ lRp := by decide
@[simp] theorem qf_lRp_ne_qfE : lRp ≠ qfE := by decide
@[simp] theorem qf_qfE_ne_lRn : qfE ≠ lRn := by decide
@[simp] theorem qf_lRn_ne_qfE : lRn ≠ qfE := by decide
@[simp] theorem qf_qfE_ne_lDir : qfE ≠ lDir := by decide
@[simp] theorem qf_lDir_ne_qfE : lDir ≠ qfE := by decide
@[simp] theorem qf_qfE_ne_lFle : qfE ≠ lFle := by decide
@[simp] theorem qf_lFle_ne_qfE : lFle ≠ qfE := by decide
@[simp] theorem qf_qfE_ne_lKb : qfE ≠ lKb := by decide
@[simp] theorem qf_lKb_ne_qfE : lKb ≠ qfE := by decide
@[simp] theorem qf_qfF_ne_qfA : qfF ≠ qfA := by decide
@[simp] theorem qf_qfF_ne_qfH : qfF ≠ qfH := by decide
@[simp] theorem qf_qfF_ne_qfU : qfF ≠ qfU := by decide
@[simp] theorem qf_qfF_ne_qfV : qfF ≠ qfV := by decide
@[simp] theorem qf_qfF_ne_qfE : qfF ≠ qfE := by decide
@[simp] theorem qf_qfF_ne_qfS : qfF ≠ qfS := by decide
@[simp] theorem qf_qfF_ne_qfR : qfF ≠ qfR := by decide
@[simp] theorem qf_qfF_ne_kFu : qfF ≠ kFu := by decide
@[simp] theorem qf_kFu_ne_qfF : kFu ≠ qfF := by decide
@[simp] theorem qf_qfF_ne_kD : qfF ≠ kD := by decide
@[simp] theorem qf_kD_ne_qfF : kD ≠ qfF := by decide
@[simp] theorem qf_qfF_ne_ibT1 : qfF ≠ ibT1 := by decide
@[simp] theorem qf_ibT1_ne_qfF : ibT1 ≠ qfF := by decide
@[simp] theorem qf_qfF_ne_ibT2 : qfF ≠ ibT2 := by decide
@[simp] theorem qf_ibT2_ne_qfF : ibT2 ≠ qfF := by decide
@[simp] theorem qf_qfF_ne_lFl : qfF ≠ lFl := by decide
@[simp] theorem qf_lFl_ne_qfF : lFl ≠ qfF := by decide
@[simp] theorem qf_qfF_ne_lDh : qfF ≠ lDh := by decide
@[simp] theorem qf_lDh_ne_qfF : lDh ≠ qfF := by decide
@[simp] theorem qf_qfF_ne_lDt : qfF ≠ lDt := by decide
@[simp] theorem qf_lDt_ne_qfF : lDt ≠ qfF := by decide
@[simp] theorem qf_qfF_ne_lDg : qfF ≠ lDg := by decide
@[simp] theorem qf_lDg_ne_qfF : lDg ≠ qfF := by decide
@[simp] theorem qf_qfF_ne_lDi : qfF ≠ lDi := by decide
@[simp] theorem qf_lDi_ne_qfF : lDi ≠ qfF := by decide
@[simp] theorem qf_qfF_ne_lRp : qfF ≠ lRp := by decide
@[simp] theorem qf_lRp_ne_qfF : lRp ≠ qfF := by decide
@[simp] theorem qf_qfF_ne_lRn : qfF ≠ lRn := by decide
@[simp] theorem qf_lRn_ne_qfF : lRn ≠ qfF := by decide
@[simp] theorem qf_qfF_ne_lDir : qfF ≠ lDir := by decide
@[simp] theorem qf_lDir_ne_qfF : lDir ≠ qfF := by decide
@[simp] theorem qf_qfF_ne_lFle : qfF ≠ lFle := by decide
@[simp] theorem qf_lFle_ne_qfF : lFle ≠ qfF := by decide
@[simp] theorem qf_qfF_ne_lKb : qfF ≠ lKb := by decide
@[simp] theorem qf_lKb_ne_qfF : lKb ≠ qfF := by decide
@[simp] theorem qf_qfS_ne_qfA : qfS ≠ qfA := by decide
@[simp] theorem qf_qfS_ne_qfH : qfS ≠ qfH := by decide
@[simp] theorem qf_qfS_ne_qfU : qfS ≠ qfU := by decide
@[simp] theorem qf_qfS_ne_qfV : qfS ≠ qfV := by decide
@[simp] theorem qf_qfS_ne_qfE : qfS ≠ qfE := by decide
@[simp] theorem qf_qfS_ne_qfF : qfS ≠ qfF := by decide
@[simp] theorem qf_qfS_ne_qfR : qfS ≠ qfR := by decide
@[simp] theorem qf_qfS_ne_kFu : qfS ≠ kFu := by decide
@[simp] theorem qf_kFu_ne_qfS : kFu ≠ qfS := by decide
@[simp] theorem qf_qfS_ne_kD : qfS ≠ kD := by decide
@[simp] theorem qf_kD_ne_qfS : kD ≠ qfS := by decide
@[simp] theorem qf_qfS_ne_ibT1 : qfS ≠ ibT1 := by decide
@[simp] theorem qf_ibT1_ne_qfS : ibT1 ≠ qfS := by decide
@[simp] theorem qf_qfS_ne_ibT2 : qfS ≠ ibT2 := by decide
@[simp] theorem qf_ibT2_ne_qfS : ibT2 ≠ qfS := by decide
@[simp] theorem qf_qfS_ne_lFl : qfS ≠ lFl := by decide
@[simp] theorem qf_lFl_ne_qfS : lFl ≠ qfS := by decide
@[simp] theorem qf_qfS_ne_lDh : qfS ≠ lDh := by decide
@[simp] theorem qf_lDh_ne_qfS : lDh ≠ qfS := by decide
@[simp] theorem qf_qfS_ne_lDt : qfS ≠ lDt := by decide
@[simp] theorem qf_lDt_ne_qfS : lDt ≠ qfS := by decide
@[simp] theorem qf_qfS_ne_lDg : qfS ≠ lDg := by decide
@[simp] theorem qf_lDg_ne_qfS : lDg ≠ qfS := by decide
@[simp] theorem qf_qfS_ne_lDi : qfS ≠ lDi := by decide
@[simp] theorem qf_lDi_ne_qfS : lDi ≠ qfS := by decide
@[simp] theorem qf_qfS_ne_lRp : qfS ≠ lRp := by decide
@[simp] theorem qf_lRp_ne_qfS : lRp ≠ qfS := by decide
@[simp] theorem qf_qfS_ne_lRn : qfS ≠ lRn := by decide
@[simp] theorem qf_lRn_ne_qfS : lRn ≠ qfS := by decide
@[simp] theorem qf_qfS_ne_lDir : qfS ≠ lDir := by decide
@[simp] theorem qf_lDir_ne_qfS : lDir ≠ qfS := by decide
@[simp] theorem qf_qfS_ne_lFle : qfS ≠ lFle := by decide
@[simp] theorem qf_lFle_ne_qfS : lFle ≠ qfS := by decide
@[simp] theorem qf_qfS_ne_lKb : qfS ≠ lKb := by decide
@[simp] theorem qf_lKb_ne_qfS : lKb ≠ qfS := by decide
@[simp] theorem qf_qfR_ne_qfA : qfR ≠ qfA := by decide
@[simp] theorem qf_qfR_ne_qfH : qfR ≠ qfH := by decide
@[simp] theorem qf_qfR_ne_qfU : qfR ≠ qfU := by decide
@[simp] theorem qf_qfR_ne_qfV : qfR ≠ qfV := by decide
@[simp] theorem qf_qfR_ne_qfE : qfR ≠ qfE := by decide
@[simp] theorem qf_qfR_ne_qfF : qfR ≠ qfF := by decide
@[simp] theorem qf_qfR_ne_qfS : qfR ≠ qfS := by decide
@[simp] theorem qf_qfR_ne_kFu : qfR ≠ kFu := by decide
@[simp] theorem qf_kFu_ne_qfR : kFu ≠ qfR := by decide
@[simp] theorem qf_qfR_ne_kD : qfR ≠ kD := by decide
@[simp] theorem qf_kD_ne_qfR : kD ≠ qfR := by decide
@[simp] theorem qf_qfR_ne_ibT1 : qfR ≠ ibT1 := by decide
@[simp] theorem qf_ibT1_ne_qfR : ibT1 ≠ qfR := by decide
@[simp] theorem qf_qfR_ne_ibT2 : qfR ≠ ibT2 := by decide
@[simp] theorem qf_ibT2_ne_qfR : ibT2 ≠ qfR := by decide
@[simp] theorem qf_qfR_ne_lFl : qfR ≠ lFl := by decide
@[simp] theorem qf_lFl_ne_qfR : lFl ≠ qfR := by decide
@[simp] theorem qf_qfR_ne_lDh : qfR ≠ lDh := by decide
@[simp] theorem qf_lDh_ne_qfR : lDh ≠ qfR := by decide
@[simp] theorem qf_qfR_ne_lDt : qfR ≠ lDt := by decide
@[simp] theorem qf_lDt_ne_qfR : lDt ≠ qfR := by decide
@[simp] theorem qf_qfR_ne_lDg : qfR ≠ lDg := by decide
@[simp] theorem qf_lDg_ne_qfR : lDg ≠ qfR := by decide
@[simp] theorem qf_qfR_ne_lDi : qfR ≠ lDi := by decide
@[simp] theorem qf_lDi_ne_qfR : lDi ≠ qfR := by decide
@[simp] theorem qf_qfR_ne_lRp : qfR ≠ lRp := by decide
@[simp] theorem qf_lRp_ne_qfR : lRp ≠ qfR := by decide
@[simp] theorem qf_qfR_ne_lRn : qfR ≠ lRn := by decide
@[simp] theorem qf_lRn_ne_qfR : lRn ≠ qfR := by decide
@[simp] theorem qf_qfR_ne_lDir : qfR ≠ lDir := by decide
@[simp] theorem qf_lDir_ne_qfR : lDir ≠ qfR := by decide
@[simp] theorem qf_qfR_ne_lFle : qfR ≠ lFle := by decide
@[simp] theorem qf_lFle_ne_qfR : lFle ≠ qfR := by decide
@[simp] theorem qf_qfR_ne_lKb : qfR ≠ lKb := by decide
@[simp] theorem qf_lKb_ne_qfR : lKb ≠ qfR := by decide

def qfLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, qfA, qfH, qfU, qfV, qfE, qfF, qfS, qfR]

def qfCore (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .lower (vv kD) (.const (BitVec.ofNat 64 (2 ^ 62))))
  (.seq (.call (some (some (.local, qfA), none)) fI [vv kFu, vv kD, vv ibT1])
  (.seq (.call (some (some (.local, qfH), none)) fW [vv kFu, vv kD, vv qfA])
  (.ite (tagIsE qfH 2)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv qfH)) (.seq eViewP
    (.seq (.assign .local qfU (.load .one (vv lRp)))
    (.seq (.call (some (some (.local, qfV), none)) fInternFVar [vv ibT1, vv kD])
    (allocP C qfE (.const 8) (.seq (.store (vv qfE) (.const 0))
    (.seq (.call (some (some (.local, qfF), none)) ExPre.fAppend [vv qfE, vv qfV])
    (.seq (.call (some (some (.local, qfS), none)) ExPre.fAppend [vv qfE, vv qfU])
    (.seq (.call (some (some (.local, qfR), none)) fTq
        [vv kFu, vv kD, .const (BitVec.ofNat 64 peelFuel), vv ibT2, .const 1, vv qfF, vv qfS])
      (.return (vv qfR))))))))))))
    hang)))
  hang

def qfBody (C : Ctx) : ProgHOL 64 := prologue qfLocals (qfCore C)

section
variable {σ : Type}

theorem qf_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ qfLocals → (ctxEnv C ++ ifaParams.zip vals).get x = none :=
  Knot.params_none C qfLocals ifaParams vals (by decide) (by decide)

theorem qf_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (hc : TqCodes C)
    (hI : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → d' < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (inferE C fIB) s1 ((knot mode C n).infer d' e')
      (PostK (ctxH C H)))
    (hW : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → d' < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d' e')
      (PostK (ctxH C H)))
    (s : AState) (d : Nat) (hd : d < 2 ^ 63) (ty b : EIdx) :
    SpecR (σ := σ) (Pre C s (ifaParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty, Enc.idxW b]))
      (qfBody C) s (inferForall (knot mode C n) C.fe d ty b) (PostK C) := by
  refine specR_prologue (postK_locals C) (qf_none C _) ?_
  unfold qfCore
  by_cases hd2 : d < 2 ^ 62
  swap
  · have hl : ¬ (BitVec.ofNat 64 d < BitVec.ofNat 64 (2 ^ 62)) := by
      rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega)]; norm_num; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ifaParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; first | exact hl | (rw [Nat.mod_eq_of_lt (show d < 18446744073709551616 by omega)]; omega))
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  have hl : BitVec.ofNat 64 d < BitVec.ofNat 64 (2 ^ 62) := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show d < 2 ^ 64 by omega)]; norm_num; omega
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ifaParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; first | exact hl | (rw [Nat.mod_eq_of_lt (show d < 18446744073709551616 by omega)]; omega))
    (fun _ => ?_) (fun h => absurd h (by decide))
  unfold inferForall
  refine Big.specR_callKC (C := C) qfA fI kParams [vv kFu, vv kD, vv ibT1] (inferE C fIB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty] (by decide) rfl (by decide) hc.pz.i
    ⟨by simp +decide [Env.get, ifaParams, ctxEnv], by simp +decide [Env.get, ifaParams, ctxEnv], by simp +decide [Env.get, ifaParams, ctxEnv], trivial⟩ (hI C.H s d ty (List.prefix_refl _) (by omega)) (fun tty s2 H2 hp2 _ => ?_)
  refine Big.specR_callKC (C := ctxH C H2) qfH fW kParams [vv kFu, vv kD, vv qfA] (whnfE C fWB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW tty] (by decide) rfl (by decide) hc.pz.w
    ⟨by simp +decide [Env.get, ifaParams, ctxEnv], by simp +decide [Env.get, ifaParams, ctxEnv], by simp, trivial⟩ (hW H2 s2 d tty hp2 (by omega)) (fun w s3 H3 hp3 _ => ?_)
  have hp13 : C.H <+: H3 := hp2.trans hp3
  refine Knot.specR_tagIteV qfH w 2 (by decide) (by decide) (by simp) (fun htg2 => ?_) (fun htg2 => ?_)
  · rw [if_pos (show (w.tag == ETag.sort) = true by simp [htg2, ETag.sort])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv qfH) (Enc.idxW w) (by decide) (by simp) ?_
    refine specR_viewP (C := ctxH C H3) w (by simp) (by simp +decide [Env.get] <;> rfl)
      (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun vw P2 hv2 htn2 _ => ?_)
    have h2 : vw.tagN = 2 := by rw [htn2, htg2]; rfl
    obtain ⟨u, rfl⟩ : ∃ u, vw = .sort u := by cases vw <;> simp [ENodeView.tagN] at h2 ⊢
    have hvs : s3.store.viewSort w = some u := viewSort_of_view (by rw [htg2]; rfl) hv2
    refine specR_runBind (show ConRon.Arena.viewSort w s3 = .ok (some u, s3) by
      show Except.ok (s3.store.viewSort w, s3) = _; rw [hvs]) ?_
    dsimp only
    refine specR_loadI' qfU (vv lRp) P2 (P2 + BitVec.ofNat 64 0) (Enc.idxW u) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encSort] using wordsAt_mem0 P2 (Enc.idxW u) [] []) ?_
    refine specR_dropM ?_
    refine ILP.specR_internFVarI (C := ctxH C H3) ra (ctxOK_H hok H3) hc.fv qfV (vv ibT1) (vv kD) ty d
      (by omega) (by decide) (by simp +decide [Env.get, ifaParams, ctxEnv]) (by simp +decide [Env.get, ifaParams, ctxEnv]) (fun fv s4 => ?_)
    refine specR_emptyBlk (C0 := C) hok (H := H3) qfE (by decide) (fun H4 oe hp4 hbe => ?_)
    refine ExPre.specR_callApp (C := ctxH C H4) (ctxOK_H hok H4) hc.app qfF (vv qfE) (vv qfV) oe
      [] (Enc.idxW fv) (by decide) hbe (by simp <;> rfl) (by simp) (fun H5 o5 hp5 hb5 => ?_)
    refine ExPre.specR_callApp (C := ctxH C H5) (ctxOK_H hok H5) hc.app qfS (vv qfE) (vv qfU) oe
      [] (Enc.idxW u) (by decide) (blkAt_mono hbe hp5) (by simp <;> rfl) (by simp) (fun H6 o6 hp6 hb6 => ?_)
    have hb5' : BlkAt H6 o5 ([fv].map Enc.idxW) := by simpa using blkAt_mono hb5 hp6
    have hb6' : BlkAt H6 o6 ([u].map Enc.idxW) := by simpa using hb6
    have hpall : C.H <+: H6 := hp13.trans (hp4.trans (hp5.trans hp6))
    refine specR_congr (m' := inferPis (knot mode C n) C.fe d peelFuel b 1 [fv].toArray [u].toArray
      >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H6) qfR fTq tqParams
      [vv kFu, vv kD, .const (BitVec.ofNat 64 peelFuel), vv ibT2, .const 1, vv qfF, vv qfS] tqBody
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, BitVec.ofNat 64 peelFuel, Enc.idxW b, BitVec.ofNat 64 1, cellA C o5,
        cellA C o6] (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [Env.get, ifaParams, ctxEnv], by simp +decide [Env.get, ifaParams, ctxEnv], rfl, by simp +decide [Env.get, ifaParams, ctxEnv], rfl, by simp <;> rfl, by simp <;> rfl, trivial⟩
      (PostK (ctxH C H6)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu tqParams _ rfl hlk)
        (tq_spec ra mode n C hok hc hI hW d peelFuel b 1 [fv] [u] o5 o6 H6 s4 hpall hb5' hb6' rfl rfl
          (by simp [peelFuel]) (by simp [peelFuel]; omega)))
      (fun r w s7 H7 hp7 hw => ?_)
    subst hw
    exact specR_returnI _ (Enc.idxW r) (by simp)
      (fun t ht => ⟨H7, hpall.trans hp7, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · rw [if_neg (show ¬ (w.tag == ETag.sort) = true by simpa [ETag.sort] using htg2)]
    exact specR_hangI

end

end ConPanqueque.T.WC
