import ConPanqueque.T.Core.InferForall
import ConPanqueque.T.Ex.AbstractRange
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# The λ arm: `inferLams` and its pieces

`inferLamsOut` (`qo`): the outward rebuild over the stacked opened domains (a heap block), innermost first:
close each domain over the `j` free variables below it (`abstractRangeFast`) and intern the ∀ node.
`inferLamsLeaf` (`qe`): open the residual body against every free variable, infer it, close the result
over the `k` binders, and hand it to `qo`.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def qoD := ofString "qon_d"
def qoS := ofString "qon_s"
def qoN := ofString "qon_n"
def qoC := ofString "qon_c"
def qoJ := ofString "qon_j"
def qoA := ofString "qon_a"
def qoB := ofString "qon_b"
def qoW := ofString "qon_w"
def qoR := ofString "qon_r"
def qeT := ofString "qen_t"
def qeK := ofString "qen_k"
def qeF := ofString "qen_f"
def qeS := ofString "qen_s"
def qeL := ofString "qen_l"
def qeO := ofString "qen_o"
def qeDk := ofString "qen_dk"
def qeB := ofString "qen_b"
def qeC := ofString "qen_c"
def qeSl := ofString "qen_sl"
def qeR := ofString "qen_r"
def fQo := ofString "inferLamsOut"
def fQe := ofString "inferLamsLeaf"
/-- `abstractRangeFast` as a Pancake function (`ExR.fastBodyR`). -/
def fAbsRF := ofString "abstractRangeFast"
def absRFParams : List MlS := [pFu, ExA.pAd, ExR.pAk, ExI.pD, pH]

@[simp] theorem qo_qoD_ne_qoS : qoD ≠ qoS := by decide
@[simp] theorem qo_qoD_ne_qoN : qoD ≠ qoN := by decide
@[simp] theorem qo_qoD_ne_qoC : qoD ≠ qoC := by decide
@[simp] theorem qo_qoD_ne_qoJ : qoD ≠ qoJ := by decide
@[simp] theorem qo_qoD_ne_qoA : qoD ≠ qoA := by decide
@[simp] theorem qo_qoD_ne_qoB : qoD ≠ qoB := by decide
@[simp] theorem qo_qoD_ne_qoW : qoD ≠ qoW := by decide
@[simp] theorem qo_qoD_ne_qoR : qoD ≠ qoR := by decide
@[simp] theorem qo_qoD_ne_qeT : qoD ≠ qeT := by decide
@[simp] theorem qo_qoD_ne_qeK : qoD ≠ qeK := by decide
@[simp] theorem qo_qoD_ne_qeF : qoD ≠ qeF := by decide
@[simp] theorem qo_qoD_ne_qeS : qoD ≠ qeS := by decide
@[simp] theorem qo_qoD_ne_qeL : qoD ≠ qeL := by decide
@[simp] theorem qo_qoD_ne_qeO : qoD ≠ qeO := by decide
@[simp] theorem qo_qoD_ne_qeDk : qoD ≠ qeDk := by decide
@[simp] theorem qo_qoD_ne_qeB : qoD ≠ qeB := by decide
@[simp] theorem qo_qoD_ne_qeC : qoD ≠ qeC := by decide
@[simp] theorem qo_qoD_ne_qeSl : qoD ≠ qeSl := by decide
@[simp] theorem qo_qoD_ne_qeR : qoD ≠ qeR := by decide
@[simp] theorem qo_qoD_ne_kFu : qoD ≠ kFu := by decide
@[simp] theorem qo_kFu_ne_qoD : kFu ≠ qoD := by decide
@[simp] theorem qo_qoD_ne_kD : qoD ≠ kD := by decide
@[simp] theorem qo_kD_ne_qoD : kD ≠ qoD := by decide
@[simp] theorem qo_qoD_ne_lFl : qoD ≠ lFl := by decide
@[simp] theorem qo_lFl_ne_qoD : lFl ≠ qoD := by decide
@[simp] theorem qo_qoD_ne_lDh : qoD ≠ lDh := by decide
@[simp] theorem qo_lDh_ne_qoD : lDh ≠ qoD := by decide
@[simp] theorem qo_qoD_ne_lDt : qoD ≠ lDt := by decide
@[simp] theorem qo_lDt_ne_qoD : lDt ≠ qoD := by decide
@[simp] theorem qo_qoD_ne_lDg : qoD ≠ lDg := by decide
@[simp] theorem qo_lDg_ne_qoD : lDg ≠ qoD := by decide
@[simp] theorem qo_qoD_ne_lDi : qoD ≠ lDi := by decide
@[simp] theorem qo_lDi_ne_qoD : lDi ≠ qoD := by decide
@[simp] theorem qo_qoD_ne_lRp : qoD ≠ lRp := by decide
@[simp] theorem qo_lRp_ne_qoD : lRp ≠ qoD := by decide
@[simp] theorem qo_qoD_ne_lRn : qoD ≠ lRn := by decide
@[simp] theorem qo_lRn_ne_qoD : lRn ≠ qoD := by decide
@[simp] theorem qo_qoD_ne_lDir : qoD ≠ lDir := by decide
@[simp] theorem qo_lDir_ne_qoD : lDir ≠ qoD := by decide
@[simp] theorem qo_qoD_ne_lFle : qoD ≠ lFle := by decide
@[simp] theorem qo_lFle_ne_qoD : lFle ≠ qoD := by decide
@[simp] theorem qo_qoD_ne_lKb : qoD ≠ lKb := by decide
@[simp] theorem qo_lKb_ne_qoD : lKb ≠ qoD := by decide
@[simp] theorem qo_qoS_ne_qoD : qoS ≠ qoD := by decide
@[simp] theorem qo_qoS_ne_qoN : qoS ≠ qoN := by decide
@[simp] theorem qo_qoS_ne_qoC : qoS ≠ qoC := by decide
@[simp] theorem qo_qoS_ne_qoJ : qoS ≠ qoJ := by decide
@[simp] theorem qo_qoS_ne_qoA : qoS ≠ qoA := by decide
@[simp] theorem qo_qoS_ne_qoB : qoS ≠ qoB := by decide
@[simp] theorem qo_qoS_ne_qoW : qoS ≠ qoW := by decide
@[simp] theorem qo_qoS_ne_qoR : qoS ≠ qoR := by decide
@[simp] theorem qo_qoS_ne_qeT : qoS ≠ qeT := by decide
@[simp] theorem qo_qoS_ne_qeK : qoS ≠ qeK := by decide
@[simp] theorem qo_qoS_ne_qeF : qoS ≠ qeF := by decide
@[simp] theorem qo_qoS_ne_qeS : qoS ≠ qeS := by decide
@[simp] theorem qo_qoS_ne_qeL : qoS ≠ qeL := by decide
@[simp] theorem qo_qoS_ne_qeO : qoS ≠ qeO := by decide
@[simp] theorem qo_qoS_ne_qeDk : qoS ≠ qeDk := by decide
@[simp] theorem qo_qoS_ne_qeB : qoS ≠ qeB := by decide
@[simp] theorem qo_qoS_ne_qeC : qoS ≠ qeC := by decide
@[simp] theorem qo_qoS_ne_qeSl : qoS ≠ qeSl := by decide
@[simp] theorem qo_qoS_ne_qeR : qoS ≠ qeR := by decide
@[simp] theorem qo_qoS_ne_kFu : qoS ≠ kFu := by decide
@[simp] theorem qo_kFu_ne_qoS : kFu ≠ qoS := by decide
@[simp] theorem qo_qoS_ne_kD : qoS ≠ kD := by decide
@[simp] theorem qo_kD_ne_qoS : kD ≠ qoS := by decide
@[simp] theorem qo_qoS_ne_lFl : qoS ≠ lFl := by decide
@[simp] theorem qo_lFl_ne_qoS : lFl ≠ qoS := by decide
@[simp] theorem qo_qoS_ne_lDh : qoS ≠ lDh := by decide
@[simp] theorem qo_lDh_ne_qoS : lDh ≠ qoS := by decide
@[simp] theorem qo_qoS_ne_lDt : qoS ≠ lDt := by decide
@[simp] theorem qo_lDt_ne_qoS : lDt ≠ qoS := by decide
@[simp] theorem qo_qoS_ne_lDg : qoS ≠ lDg := by decide
@[simp] theorem qo_lDg_ne_qoS : lDg ≠ qoS := by decide
@[simp] theorem qo_qoS_ne_lDi : qoS ≠ lDi := by decide
@[simp] theorem qo_lDi_ne_qoS : lDi ≠ qoS := by decide
@[simp] theorem qo_qoS_ne_lRp : qoS ≠ lRp := by decide
@[simp] theorem qo_lRp_ne_qoS : lRp ≠ qoS := by decide
@[simp] theorem qo_qoS_ne_lRn : qoS ≠ lRn := by decide
@[simp] theorem qo_lRn_ne_qoS : lRn ≠ qoS := by decide
@[simp] theorem qo_qoS_ne_lDir : qoS ≠ lDir := by decide
@[simp] theorem qo_lDir_ne_qoS : lDir ≠ qoS := by decide
@[simp] theorem qo_qoS_ne_lFle : qoS ≠ lFle := by decide
@[simp] theorem qo_lFle_ne_qoS : lFle ≠ qoS := by decide
@[simp] theorem qo_qoS_ne_lKb : qoS ≠ lKb := by decide
@[simp] theorem qo_lKb_ne_qoS : lKb ≠ qoS := by decide
@[simp] theorem qo_qoN_ne_qoD : qoN ≠ qoD := by decide
@[simp] theorem qo_qoN_ne_qoS : qoN ≠ qoS := by decide
@[simp] theorem qo_qoN_ne_qoC : qoN ≠ qoC := by decide
@[simp] theorem qo_qoN_ne_qoJ : qoN ≠ qoJ := by decide
@[simp] theorem qo_qoN_ne_qoA : qoN ≠ qoA := by decide
@[simp] theorem qo_qoN_ne_qoB : qoN ≠ qoB := by decide
@[simp] theorem qo_qoN_ne_qoW : qoN ≠ qoW := by decide
@[simp] theorem qo_qoN_ne_qoR : qoN ≠ qoR := by decide
@[simp] theorem qo_qoN_ne_qeT : qoN ≠ qeT := by decide
@[simp] theorem qo_qoN_ne_qeK : qoN ≠ qeK := by decide
@[simp] theorem qo_qoN_ne_qeF : qoN ≠ qeF := by decide
@[simp] theorem qo_qoN_ne_qeS : qoN ≠ qeS := by decide
@[simp] theorem qo_qoN_ne_qeL : qoN ≠ qeL := by decide
@[simp] theorem qo_qoN_ne_qeO : qoN ≠ qeO := by decide
@[simp] theorem qo_qoN_ne_qeDk : qoN ≠ qeDk := by decide
@[simp] theorem qo_qoN_ne_qeB : qoN ≠ qeB := by decide
@[simp] theorem qo_qoN_ne_qeC : qoN ≠ qeC := by decide
@[simp] theorem qo_qoN_ne_qeSl : qoN ≠ qeSl := by decide
@[simp] theorem qo_qoN_ne_qeR : qoN ≠ qeR := by decide
@[simp] theorem qo_qoN_ne_kFu : qoN ≠ kFu := by decide
@[simp] theorem qo_kFu_ne_qoN : kFu ≠ qoN := by decide
@[simp] theorem qo_qoN_ne_kD : qoN ≠ kD := by decide
@[simp] theorem qo_kD_ne_qoN : kD ≠ qoN := by decide
@[simp] theorem qo_qoN_ne_lFl : qoN ≠ lFl := by decide
@[simp] theorem qo_lFl_ne_qoN : lFl ≠ qoN := by decide
@[simp] theorem qo_qoN_ne_lDh : qoN ≠ lDh := by decide
@[simp] theorem qo_lDh_ne_qoN : lDh ≠ qoN := by decide
@[simp] theorem qo_qoN_ne_lDt : qoN ≠ lDt := by decide
@[simp] theorem qo_lDt_ne_qoN : lDt ≠ qoN := by decide
@[simp] theorem qo_qoN_ne_lDg : qoN ≠ lDg := by decide
@[simp] theorem qo_lDg_ne_qoN : lDg ≠ qoN := by decide
@[simp] theorem qo_qoN_ne_lDi : qoN ≠ lDi := by decide
@[simp] theorem qo_lDi_ne_qoN : lDi ≠ qoN := by decide
@[simp] theorem qo_qoN_ne_lRp : qoN ≠ lRp := by decide
@[simp] theorem qo_lRp_ne_qoN : lRp ≠ qoN := by decide
@[simp] theorem qo_qoN_ne_lRn : qoN ≠ lRn := by decide
@[simp] theorem qo_lRn_ne_qoN : lRn ≠ qoN := by decide
@[simp] theorem qo_qoN_ne_lDir : qoN ≠ lDir := by decide
@[simp] theorem qo_lDir_ne_qoN : lDir ≠ qoN := by decide
@[simp] theorem qo_qoN_ne_lFle : qoN ≠ lFle := by decide
@[simp] theorem qo_lFle_ne_qoN : lFle ≠ qoN := by decide
@[simp] theorem qo_qoN_ne_lKb : qoN ≠ lKb := by decide
@[simp] theorem qo_lKb_ne_qoN : lKb ≠ qoN := by decide
@[simp] theorem qo_qoC_ne_qoD : qoC ≠ qoD := by decide
@[simp] theorem qo_qoC_ne_qoS : qoC ≠ qoS := by decide
@[simp] theorem qo_qoC_ne_qoN : qoC ≠ qoN := by decide
@[simp] theorem qo_qoC_ne_qoJ : qoC ≠ qoJ := by decide
@[simp] theorem qo_qoC_ne_qoA : qoC ≠ qoA := by decide
@[simp] theorem qo_qoC_ne_qoB : qoC ≠ qoB := by decide
@[simp] theorem qo_qoC_ne_qoW : qoC ≠ qoW := by decide
@[simp] theorem qo_qoC_ne_qoR : qoC ≠ qoR := by decide
@[simp] theorem qo_qoC_ne_qeT : qoC ≠ qeT := by decide
@[simp] theorem qo_qoC_ne_qeK : qoC ≠ qeK := by decide
@[simp] theorem qo_qoC_ne_qeF : qoC ≠ qeF := by decide
@[simp] theorem qo_qoC_ne_qeS : qoC ≠ qeS := by decide
@[simp] theorem qo_qoC_ne_qeL : qoC ≠ qeL := by decide
@[simp] theorem qo_qoC_ne_qeO : qoC ≠ qeO := by decide
@[simp] theorem qo_qoC_ne_qeDk : qoC ≠ qeDk := by decide
@[simp] theorem qo_qoC_ne_qeB : qoC ≠ qeB := by decide
@[simp] theorem qo_qoC_ne_qeC : qoC ≠ qeC := by decide
@[simp] theorem qo_qoC_ne_qeSl : qoC ≠ qeSl := by decide
@[simp] theorem qo_qoC_ne_qeR : qoC ≠ qeR := by decide
@[simp] theorem qo_qoC_ne_kFu : qoC ≠ kFu := by decide
@[simp] theorem qo_kFu_ne_qoC : kFu ≠ qoC := by decide
@[simp] theorem qo_qoC_ne_kD : qoC ≠ kD := by decide
@[simp] theorem qo_kD_ne_qoC : kD ≠ qoC := by decide
@[simp] theorem qo_qoC_ne_lFl : qoC ≠ lFl := by decide
@[simp] theorem qo_lFl_ne_qoC : lFl ≠ qoC := by decide
@[simp] theorem qo_qoC_ne_lDh : qoC ≠ lDh := by decide
@[simp] theorem qo_lDh_ne_qoC : lDh ≠ qoC := by decide
@[simp] theorem qo_qoC_ne_lDt : qoC ≠ lDt := by decide
@[simp] theorem qo_lDt_ne_qoC : lDt ≠ qoC := by decide
@[simp] theorem qo_qoC_ne_lDg : qoC ≠ lDg := by decide
@[simp] theorem qo_lDg_ne_qoC : lDg ≠ qoC := by decide
@[simp] theorem qo_qoC_ne_lDi : qoC ≠ lDi := by decide
@[simp] theorem qo_lDi_ne_qoC : lDi ≠ qoC := by decide
@[simp] theorem qo_qoC_ne_lRp : qoC ≠ lRp := by decide
@[simp] theorem qo_lRp_ne_qoC : lRp ≠ qoC := by decide
@[simp] theorem qo_qoC_ne_lRn : qoC ≠ lRn := by decide
@[simp] theorem qo_lRn_ne_qoC : lRn ≠ qoC := by decide
@[simp] theorem qo_qoC_ne_lDir : qoC ≠ lDir := by decide
@[simp] theorem qo_lDir_ne_qoC : lDir ≠ qoC := by decide
@[simp] theorem qo_qoC_ne_lFle : qoC ≠ lFle := by decide
@[simp] theorem qo_lFle_ne_qoC : lFle ≠ qoC := by decide
@[simp] theorem qo_qoC_ne_lKb : qoC ≠ lKb := by decide
@[simp] theorem qo_lKb_ne_qoC : lKb ≠ qoC := by decide
@[simp] theorem qo_qoJ_ne_qoD : qoJ ≠ qoD := by decide
@[simp] theorem qo_qoJ_ne_qoS : qoJ ≠ qoS := by decide
@[simp] theorem qo_qoJ_ne_qoN : qoJ ≠ qoN := by decide
@[simp] theorem qo_qoJ_ne_qoC : qoJ ≠ qoC := by decide
@[simp] theorem qo_qoJ_ne_qoA : qoJ ≠ qoA := by decide
@[simp] theorem qo_qoJ_ne_qoB : qoJ ≠ qoB := by decide
@[simp] theorem qo_qoJ_ne_qoW : qoJ ≠ qoW := by decide
@[simp] theorem qo_qoJ_ne_qoR : qoJ ≠ qoR := by decide
@[simp] theorem qo_qoJ_ne_qeT : qoJ ≠ qeT := by decide
@[simp] theorem qo_qoJ_ne_qeK : qoJ ≠ qeK := by decide
@[simp] theorem qo_qoJ_ne_qeF : qoJ ≠ qeF := by decide
@[simp] theorem qo_qoJ_ne_qeS : qoJ ≠ qeS := by decide
@[simp] theorem qo_qoJ_ne_qeL : qoJ ≠ qeL := by decide
@[simp] theorem qo_qoJ_ne_qeO : qoJ ≠ qeO := by decide
@[simp] theorem qo_qoJ_ne_qeDk : qoJ ≠ qeDk := by decide
@[simp] theorem qo_qoJ_ne_qeB : qoJ ≠ qeB := by decide
@[simp] theorem qo_qoJ_ne_qeC : qoJ ≠ qeC := by decide
@[simp] theorem qo_qoJ_ne_qeSl : qoJ ≠ qeSl := by decide
@[simp] theorem qo_qoJ_ne_qeR : qoJ ≠ qeR := by decide
@[simp] theorem qo_qoJ_ne_kFu : qoJ ≠ kFu := by decide
@[simp] theorem qo_kFu_ne_qoJ : kFu ≠ qoJ := by decide
@[simp] theorem qo_qoJ_ne_kD : qoJ ≠ kD := by decide
@[simp] theorem qo_kD_ne_qoJ : kD ≠ qoJ := by decide
@[simp] theorem qo_qoJ_ne_lFl : qoJ ≠ lFl := by decide
@[simp] theorem qo_lFl_ne_qoJ : lFl ≠ qoJ := by decide
@[simp] theorem qo_qoJ_ne_lDh : qoJ ≠ lDh := by decide
@[simp] theorem qo_lDh_ne_qoJ : lDh ≠ qoJ := by decide
@[simp] theorem qo_qoJ_ne_lDt : qoJ ≠ lDt := by decide
@[simp] theorem qo_lDt_ne_qoJ : lDt ≠ qoJ := by decide
@[simp] theorem qo_qoJ_ne_lDg : qoJ ≠ lDg := by decide
@[simp] theorem qo_lDg_ne_qoJ : lDg ≠ qoJ := by decide
@[simp] theorem qo_qoJ_ne_lDi : qoJ ≠ lDi := by decide
@[simp] theorem qo_lDi_ne_qoJ : lDi ≠ qoJ := by decide
@[simp] theorem qo_qoJ_ne_lRp : qoJ ≠ lRp := by decide
@[simp] theorem qo_lRp_ne_qoJ : lRp ≠ qoJ := by decide
@[simp] theorem qo_qoJ_ne_lRn : qoJ ≠ lRn := by decide
@[simp] theorem qo_lRn_ne_qoJ : lRn ≠ qoJ := by decide
@[simp] theorem qo_qoJ_ne_lDir : qoJ ≠ lDir := by decide
@[simp] theorem qo_lDir_ne_qoJ : lDir ≠ qoJ := by decide
@[simp] theorem qo_qoJ_ne_lFle : qoJ ≠ lFle := by decide
@[simp] theorem qo_lFle_ne_qoJ : lFle ≠ qoJ := by decide
@[simp] theorem qo_qoJ_ne_lKb : qoJ ≠ lKb := by decide
@[simp] theorem qo_lKb_ne_qoJ : lKb ≠ qoJ := by decide
@[simp] theorem qo_qoA_ne_qoD : qoA ≠ qoD := by decide
@[simp] theorem qo_qoA_ne_qoS : qoA ≠ qoS := by decide
@[simp] theorem qo_qoA_ne_qoN : qoA ≠ qoN := by decide
@[simp] theorem qo_qoA_ne_qoC : qoA ≠ qoC := by decide
@[simp] theorem qo_qoA_ne_qoJ : qoA ≠ qoJ := by decide
@[simp] theorem qo_qoA_ne_qoB : qoA ≠ qoB := by decide
@[simp] theorem qo_qoA_ne_qoW : qoA ≠ qoW := by decide
@[simp] theorem qo_qoA_ne_qoR : qoA ≠ qoR := by decide
@[simp] theorem qo_qoA_ne_qeT : qoA ≠ qeT := by decide
@[simp] theorem qo_qoA_ne_qeK : qoA ≠ qeK := by decide
@[simp] theorem qo_qoA_ne_qeF : qoA ≠ qeF := by decide
@[simp] theorem qo_qoA_ne_qeS : qoA ≠ qeS := by decide
@[simp] theorem qo_qoA_ne_qeL : qoA ≠ qeL := by decide
@[simp] theorem qo_qoA_ne_qeO : qoA ≠ qeO := by decide
@[simp] theorem qo_qoA_ne_qeDk : qoA ≠ qeDk := by decide
@[simp] theorem qo_qoA_ne_qeB : qoA ≠ qeB := by decide
@[simp] theorem qo_qoA_ne_qeC : qoA ≠ qeC := by decide
@[simp] theorem qo_qoA_ne_qeSl : qoA ≠ qeSl := by decide
@[simp] theorem qo_qoA_ne_qeR : qoA ≠ qeR := by decide
@[simp] theorem qo_qoA_ne_kFu : qoA ≠ kFu := by decide
@[simp] theorem qo_kFu_ne_qoA : kFu ≠ qoA := by decide
@[simp] theorem qo_qoA_ne_kD : qoA ≠ kD := by decide
@[simp] theorem qo_kD_ne_qoA : kD ≠ qoA := by decide
@[simp] theorem qo_qoA_ne_lFl : qoA ≠ lFl := by decide
@[simp] theorem qo_lFl_ne_qoA : lFl ≠ qoA := by decide
@[simp] theorem qo_qoA_ne_lDh : qoA ≠ lDh := by decide
@[simp] theorem qo_lDh_ne_qoA : lDh ≠ qoA := by decide
@[simp] theorem qo_qoA_ne_lDt : qoA ≠ lDt := by decide
@[simp] theorem qo_lDt_ne_qoA : lDt ≠ qoA := by decide
@[simp] theorem qo_qoA_ne_lDg : qoA ≠ lDg := by decide
@[simp] theorem qo_lDg_ne_qoA : lDg ≠ qoA := by decide
@[simp] theorem qo_qoA_ne_lDi : qoA ≠ lDi := by decide
@[simp] theorem qo_lDi_ne_qoA : lDi ≠ qoA := by decide
@[simp] theorem qo_qoA_ne_lRp : qoA ≠ lRp := by decide
@[simp] theorem qo_lRp_ne_qoA : lRp ≠ qoA := by decide
@[simp] theorem qo_qoA_ne_lRn : qoA ≠ lRn := by decide
@[simp] theorem qo_lRn_ne_qoA : lRn ≠ qoA := by decide
@[simp] theorem qo_qoA_ne_lDir : qoA ≠ lDir := by decide
@[simp] theorem qo_lDir_ne_qoA : lDir ≠ qoA := by decide
@[simp] theorem qo_qoA_ne_lFle : qoA ≠ lFle := by decide
@[simp] theorem qo_lFle_ne_qoA : lFle ≠ qoA := by decide
@[simp] theorem qo_qoA_ne_lKb : qoA ≠ lKb := by decide
@[simp] theorem qo_lKb_ne_qoA : lKb ≠ qoA := by decide
@[simp] theorem qo_qoB_ne_qoD : qoB ≠ qoD := by decide
@[simp] theorem qo_qoB_ne_qoS : qoB ≠ qoS := by decide
@[simp] theorem qo_qoB_ne_qoN : qoB ≠ qoN := by decide
@[simp] theorem qo_qoB_ne_qoC : qoB ≠ qoC := by decide
@[simp] theorem qo_qoB_ne_qoJ : qoB ≠ qoJ := by decide
@[simp] theorem qo_qoB_ne_qoA : qoB ≠ qoA := by decide
@[simp] theorem qo_qoB_ne_qoW : qoB ≠ qoW := by decide
@[simp] theorem qo_qoB_ne_qoR : qoB ≠ qoR := by decide
@[simp] theorem qo_qoB_ne_qeT : qoB ≠ qeT := by decide
@[simp] theorem qo_qoB_ne_qeK : qoB ≠ qeK := by decide
@[simp] theorem qo_qoB_ne_qeF : qoB ≠ qeF := by decide
@[simp] theorem qo_qoB_ne_qeS : qoB ≠ qeS := by decide
@[simp] theorem qo_qoB_ne_qeL : qoB ≠ qeL := by decide
@[simp] theorem qo_qoB_ne_qeO : qoB ≠ qeO := by decide
@[simp] theorem qo_qoB_ne_qeDk : qoB ≠ qeDk := by decide
@[simp] theorem qo_qoB_ne_qeB : qoB ≠ qeB := by decide
@[simp] theorem qo_qoB_ne_qeC : qoB ≠ qeC := by decide
@[simp] theorem qo_qoB_ne_qeSl : qoB ≠ qeSl := by decide
@[simp] theorem qo_qoB_ne_qeR : qoB ≠ qeR := by decide
@[simp] theorem qo_qoB_ne_kFu : qoB ≠ kFu := by decide
@[simp] theorem qo_kFu_ne_qoB : kFu ≠ qoB := by decide
@[simp] theorem qo_qoB_ne_kD : qoB ≠ kD := by decide
@[simp] theorem qo_kD_ne_qoB : kD ≠ qoB := by decide
@[simp] theorem qo_qoB_ne_lFl : qoB ≠ lFl := by decide
@[simp] theorem qo_lFl_ne_qoB : lFl ≠ qoB := by decide
@[simp] theorem qo_qoB_ne_lDh : qoB ≠ lDh := by decide
@[simp] theorem qo_lDh_ne_qoB : lDh ≠ qoB := by decide
@[simp] theorem qo_qoB_ne_lDt : qoB ≠ lDt := by decide
@[simp] theorem qo_lDt_ne_qoB : lDt ≠ qoB := by decide
@[simp] theorem qo_qoB_ne_lDg : qoB ≠ lDg := by decide
@[simp] theorem qo_lDg_ne_qoB : lDg ≠ qoB := by decide
@[simp] theorem qo_qoB_ne_lDi : qoB ≠ lDi := by decide
@[simp] theorem qo_lDi_ne_qoB : lDi ≠ qoB := by decide
@[simp] theorem qo_qoB_ne_lRp : qoB ≠ lRp := by decide
@[simp] theorem qo_lRp_ne_qoB : lRp ≠ qoB := by decide
@[simp] theorem qo_qoB_ne_lRn : qoB ≠ lRn := by decide
@[simp] theorem qo_lRn_ne_qoB : lRn ≠ qoB := by decide
@[simp] theorem qo_qoB_ne_lDir : qoB ≠ lDir := by decide
@[simp] theorem qo_lDir_ne_qoB : lDir ≠ qoB := by decide
@[simp] theorem qo_qoB_ne_lFle : qoB ≠ lFle := by decide
@[simp] theorem qo_lFle_ne_qoB : lFle ≠ qoB := by decide
@[simp] theorem qo_qoB_ne_lKb : qoB ≠ lKb := by decide
@[simp] theorem qo_lKb_ne_qoB : lKb ≠ qoB := by decide
@[simp] theorem qo_qoW_ne_qoD : qoW ≠ qoD := by decide
@[simp] theorem qo_qoW_ne_qoS : qoW ≠ qoS := by decide
@[simp] theorem qo_qoW_ne_qoN : qoW ≠ qoN := by decide
@[simp] theorem qo_qoW_ne_qoC : qoW ≠ qoC := by decide
@[simp] theorem qo_qoW_ne_qoJ : qoW ≠ qoJ := by decide
@[simp] theorem qo_qoW_ne_qoA : qoW ≠ qoA := by decide
@[simp] theorem qo_qoW_ne_qoB : qoW ≠ qoB := by decide
@[simp] theorem qo_qoW_ne_qoR : qoW ≠ qoR := by decide
@[simp] theorem qo_qoW_ne_qeT : qoW ≠ qeT := by decide
@[simp] theorem qo_qoW_ne_qeK : qoW ≠ qeK := by decide
@[simp] theorem qo_qoW_ne_qeF : qoW ≠ qeF := by decide
@[simp] theorem qo_qoW_ne_qeS : qoW ≠ qeS := by decide
@[simp] theorem qo_qoW_ne_qeL : qoW ≠ qeL := by decide
@[simp] theorem qo_qoW_ne_qeO : qoW ≠ qeO := by decide
@[simp] theorem qo_qoW_ne_qeDk : qoW ≠ qeDk := by decide
@[simp] theorem qo_qoW_ne_qeB : qoW ≠ qeB := by decide
@[simp] theorem qo_qoW_ne_qeC : qoW ≠ qeC := by decide
@[simp] theorem qo_qoW_ne_qeSl : qoW ≠ qeSl := by decide
@[simp] theorem qo_qoW_ne_qeR : qoW ≠ qeR := by decide
@[simp] theorem qo_qoW_ne_kFu : qoW ≠ kFu := by decide
@[simp] theorem qo_kFu_ne_qoW : kFu ≠ qoW := by decide
@[simp] theorem qo_qoW_ne_kD : qoW ≠ kD := by decide
@[simp] theorem qo_kD_ne_qoW : kD ≠ qoW := by decide
@[simp] theorem qo_qoW_ne_lFl : qoW ≠ lFl := by decide
@[simp] theorem qo_lFl_ne_qoW : lFl ≠ qoW := by decide
@[simp] theorem qo_qoW_ne_lDh : qoW ≠ lDh := by decide
@[simp] theorem qo_lDh_ne_qoW : lDh ≠ qoW := by decide
@[simp] theorem qo_qoW_ne_lDt : qoW ≠ lDt := by decide
@[simp] theorem qo_lDt_ne_qoW : lDt ≠ qoW := by decide
@[simp] theorem qo_qoW_ne_lDg : qoW ≠ lDg := by decide
@[simp] theorem qo_lDg_ne_qoW : lDg ≠ qoW := by decide
@[simp] theorem qo_qoW_ne_lDi : qoW ≠ lDi := by decide
@[simp] theorem qo_lDi_ne_qoW : lDi ≠ qoW := by decide
@[simp] theorem qo_qoW_ne_lRp : qoW ≠ lRp := by decide
@[simp] theorem qo_lRp_ne_qoW : lRp ≠ qoW := by decide
@[simp] theorem qo_qoW_ne_lRn : qoW ≠ lRn := by decide
@[simp] theorem qo_lRn_ne_qoW : lRn ≠ qoW := by decide
@[simp] theorem qo_qoW_ne_lDir : qoW ≠ lDir := by decide
@[simp] theorem qo_lDir_ne_qoW : lDir ≠ qoW := by decide
@[simp] theorem qo_qoW_ne_lFle : qoW ≠ lFle := by decide
@[simp] theorem qo_lFle_ne_qoW : lFle ≠ qoW := by decide
@[simp] theorem qo_qoW_ne_lKb : qoW ≠ lKb := by decide
@[simp] theorem qo_lKb_ne_qoW : lKb ≠ qoW := by decide
@[simp] theorem qo_qoR_ne_qoD : qoR ≠ qoD := by decide
@[simp] theorem qo_qoR_ne_qoS : qoR ≠ qoS := by decide
@[simp] theorem qo_qoR_ne_qoN : qoR ≠ qoN := by decide
@[simp] theorem qo_qoR_ne_qoC : qoR ≠ qoC := by decide
@[simp] theorem qo_qoR_ne_qoJ : qoR ≠ qoJ := by decide
@[simp] theorem qo_qoR_ne_qoA : qoR ≠ qoA := by decide
@[simp] theorem qo_qoR_ne_qoB : qoR ≠ qoB := by decide
@[simp] theorem qo_qoR_ne_qoW : qoR ≠ qoW := by decide
@[simp] theorem qo_qoR_ne_qeT : qoR ≠ qeT := by decide
@[simp] theorem qo_qoR_ne_qeK : qoR ≠ qeK := by decide
@[simp] theorem qo_qoR_ne_qeF : qoR ≠ qeF := by decide
@[simp] theorem qo_qoR_ne_qeS : qoR ≠ qeS := by decide
@[simp] theorem qo_qoR_ne_qeL : qoR ≠ qeL := by decide
@[simp] theorem qo_qoR_ne_qeO : qoR ≠ qeO := by decide
@[simp] theorem qo_qoR_ne_qeDk : qoR ≠ qeDk := by decide
@[simp] theorem qo_qoR_ne_qeB : qoR ≠ qeB := by decide
@[simp] theorem qo_qoR_ne_qeC : qoR ≠ qeC := by decide
@[simp] theorem qo_qoR_ne_qeSl : qoR ≠ qeSl := by decide
@[simp] theorem qo_qoR_ne_qeR : qoR ≠ qeR := by decide
@[simp] theorem qo_qoR_ne_kFu : qoR ≠ kFu := by decide
@[simp] theorem qo_kFu_ne_qoR : kFu ≠ qoR := by decide
@[simp] theorem qo_qoR_ne_kD : qoR ≠ kD := by decide
@[simp] theorem qo_kD_ne_qoR : kD ≠ qoR := by decide
@[simp] theorem qo_qoR_ne_lFl : qoR ≠ lFl := by decide
@[simp] theorem qo_lFl_ne_qoR : lFl ≠ qoR := by decide
@[simp] theorem qo_qoR_ne_lDh : qoR ≠ lDh := by decide
@[simp] theorem qo_lDh_ne_qoR : lDh ≠ qoR := by decide
@[simp] theorem qo_qoR_ne_lDt : qoR ≠ lDt := by decide
@[simp] theorem qo_lDt_ne_qoR : lDt ≠ qoR := by decide
@[simp] theorem qo_qoR_ne_lDg : qoR ≠ lDg := by decide
@[simp] theorem qo_lDg_ne_qoR : lDg ≠ qoR := by decide
@[simp] theorem qo_qoR_ne_lDi : qoR ≠ lDi := by decide
@[simp] theorem qo_lDi_ne_qoR : lDi ≠ qoR := by decide
@[simp] theorem qo_qoR_ne_lRp : qoR ≠ lRp := by decide
@[simp] theorem qo_lRp_ne_qoR : lRp ≠ qoR := by decide
@[simp] theorem qo_qoR_ne_lRn : qoR ≠ lRn := by decide
@[simp] theorem qo_lRn_ne_qoR : lRn ≠ qoR := by decide
@[simp] theorem qo_qoR_ne_lDir : qoR ≠ lDir := by decide
@[simp] theorem qo_lDir_ne_qoR : lDir ≠ qoR := by decide
@[simp] theorem qo_qoR_ne_lFle : qoR ≠ lFle := by decide
@[simp] theorem qo_lFle_ne_qoR : lFle ≠ qoR := by decide
@[simp] theorem qo_qoR_ne_lKb : qoR ≠ lKb := by decide
@[simp] theorem qo_lKb_ne_qoR : lKb ≠ qoR := by decide
@[simp] theorem qo_qeT_ne_qoD : qeT ≠ qoD := by decide
@[simp] theorem qo_qeT_ne_qoS : qeT ≠ qoS := by decide
@[simp] theorem qo_qeT_ne_qoN : qeT ≠ qoN := by decide
@[simp] theorem qo_qeT_ne_qoC : qeT ≠ qoC := by decide
@[simp] theorem qo_qeT_ne_qoJ : qeT ≠ qoJ := by decide
@[simp] theorem qo_qeT_ne_qoA : qeT ≠ qoA := by decide
@[simp] theorem qo_qeT_ne_qoB : qeT ≠ qoB := by decide
@[simp] theorem qo_qeT_ne_qoW : qeT ≠ qoW := by decide
@[simp] theorem qo_qeT_ne_qoR : qeT ≠ qoR := by decide
@[simp] theorem qo_qeT_ne_qeK : qeT ≠ qeK := by decide
@[simp] theorem qo_qeT_ne_qeF : qeT ≠ qeF := by decide
@[simp] theorem qo_qeT_ne_qeS : qeT ≠ qeS := by decide
@[simp] theorem qo_qeT_ne_qeL : qeT ≠ qeL := by decide
@[simp] theorem qo_qeT_ne_qeO : qeT ≠ qeO := by decide
@[simp] theorem qo_qeT_ne_qeDk : qeT ≠ qeDk := by decide
@[simp] theorem qo_qeT_ne_qeB : qeT ≠ qeB := by decide
@[simp] theorem qo_qeT_ne_qeC : qeT ≠ qeC := by decide
@[simp] theorem qo_qeT_ne_qeSl : qeT ≠ qeSl := by decide
@[simp] theorem qo_qeT_ne_qeR : qeT ≠ qeR := by decide
@[simp] theorem qo_qeT_ne_kFu : qeT ≠ kFu := by decide
@[simp] theorem qo_kFu_ne_qeT : kFu ≠ qeT := by decide
@[simp] theorem qo_qeT_ne_kD : qeT ≠ kD := by decide
@[simp] theorem qo_kD_ne_qeT : kD ≠ qeT := by decide
@[simp] theorem qo_qeT_ne_lFl : qeT ≠ lFl := by decide
@[simp] theorem qo_lFl_ne_qeT : lFl ≠ qeT := by decide
@[simp] theorem qo_qeT_ne_lDh : qeT ≠ lDh := by decide
@[simp] theorem qo_lDh_ne_qeT : lDh ≠ qeT := by decide
@[simp] theorem qo_qeT_ne_lDt : qeT ≠ lDt := by decide
@[simp] theorem qo_lDt_ne_qeT : lDt ≠ qeT := by decide
@[simp] theorem qo_qeT_ne_lDg : qeT ≠ lDg := by decide
@[simp] theorem qo_lDg_ne_qeT : lDg ≠ qeT := by decide
@[simp] theorem qo_qeT_ne_lDi : qeT ≠ lDi := by decide
@[simp] theorem qo_lDi_ne_qeT : lDi ≠ qeT := by decide
@[simp] theorem qo_qeT_ne_lRp : qeT ≠ lRp := by decide
@[simp] theorem qo_lRp_ne_qeT : lRp ≠ qeT := by decide
@[simp] theorem qo_qeT_ne_lRn : qeT ≠ lRn := by decide
@[simp] theorem qo_lRn_ne_qeT : lRn ≠ qeT := by decide
@[simp] theorem qo_qeT_ne_lDir : qeT ≠ lDir := by decide
@[simp] theorem qo_lDir_ne_qeT : lDir ≠ qeT := by decide
@[simp] theorem qo_qeT_ne_lFle : qeT ≠ lFle := by decide
@[simp] theorem qo_lFle_ne_qeT : lFle ≠ qeT := by decide
@[simp] theorem qo_qeT_ne_lKb : qeT ≠ lKb := by decide
@[simp] theorem qo_lKb_ne_qeT : lKb ≠ qeT := by decide
@[simp] theorem qo_qeK_ne_qoD : qeK ≠ qoD := by decide
@[simp] theorem qo_qeK_ne_qoS : qeK ≠ qoS := by decide
@[simp] theorem qo_qeK_ne_qoN : qeK ≠ qoN := by decide
@[simp] theorem qo_qeK_ne_qoC : qeK ≠ qoC := by decide
@[simp] theorem qo_qeK_ne_qoJ : qeK ≠ qoJ := by decide
@[simp] theorem qo_qeK_ne_qoA : qeK ≠ qoA := by decide
@[simp] theorem qo_qeK_ne_qoB : qeK ≠ qoB := by decide
@[simp] theorem qo_qeK_ne_qoW : qeK ≠ qoW := by decide
@[simp] theorem qo_qeK_ne_qoR : qeK ≠ qoR := by decide
@[simp] theorem qo_qeK_ne_qeT : qeK ≠ qeT := by decide
@[simp] theorem qo_qeK_ne_qeF : qeK ≠ qeF := by decide
@[simp] theorem qo_qeK_ne_qeS : qeK ≠ qeS := by decide
@[simp] theorem qo_qeK_ne_qeL : qeK ≠ qeL := by decide
@[simp] theorem qo_qeK_ne_qeO : qeK ≠ qeO := by decide
@[simp] theorem qo_qeK_ne_qeDk : qeK ≠ qeDk := by decide
@[simp] theorem qo_qeK_ne_qeB : qeK ≠ qeB := by decide
@[simp] theorem qo_qeK_ne_qeC : qeK ≠ qeC := by decide
@[simp] theorem qo_qeK_ne_qeSl : qeK ≠ qeSl := by decide
@[simp] theorem qo_qeK_ne_qeR : qeK ≠ qeR := by decide
@[simp] theorem qo_qeK_ne_kFu : qeK ≠ kFu := by decide
@[simp] theorem qo_kFu_ne_qeK : kFu ≠ qeK := by decide
@[simp] theorem qo_qeK_ne_kD : qeK ≠ kD := by decide
@[simp] theorem qo_kD_ne_qeK : kD ≠ qeK := by decide
@[simp] theorem qo_qeK_ne_lFl : qeK ≠ lFl := by decide
@[simp] theorem qo_lFl_ne_qeK : lFl ≠ qeK := by decide
@[simp] theorem qo_qeK_ne_lDh : qeK ≠ lDh := by decide
@[simp] theorem qo_lDh_ne_qeK : lDh ≠ qeK := by decide
@[simp] theorem qo_qeK_ne_lDt : qeK ≠ lDt := by decide
@[simp] theorem qo_lDt_ne_qeK : lDt ≠ qeK := by decide
@[simp] theorem qo_qeK_ne_lDg : qeK ≠ lDg := by decide
@[simp] theorem qo_lDg_ne_qeK : lDg ≠ qeK := by decide
@[simp] theorem qo_qeK_ne_lDi : qeK ≠ lDi := by decide
@[simp] theorem qo_lDi_ne_qeK : lDi ≠ qeK := by decide
@[simp] theorem qo_qeK_ne_lRp : qeK ≠ lRp := by decide
@[simp] theorem qo_lRp_ne_qeK : lRp ≠ qeK := by decide
@[simp] theorem qo_qeK_ne_lRn : qeK ≠ lRn := by decide
@[simp] theorem qo_lRn_ne_qeK : lRn ≠ qeK := by decide
@[simp] theorem qo_qeK_ne_lDir : qeK ≠ lDir := by decide
@[simp] theorem qo_lDir_ne_qeK : lDir ≠ qeK := by decide
@[simp] theorem qo_qeK_ne_lFle : qeK ≠ lFle := by decide
@[simp] theorem qo_lFle_ne_qeK : lFle ≠ qeK := by decide
@[simp] theorem qo_qeK_ne_lKb : qeK ≠ lKb := by decide
@[simp] theorem qo_lKb_ne_qeK : lKb ≠ qeK := by decide
@[simp] theorem qo_qeF_ne_qoD : qeF ≠ qoD := by decide
@[simp] theorem qo_qeF_ne_qoS : qeF ≠ qoS := by decide
@[simp] theorem qo_qeF_ne_qoN : qeF ≠ qoN := by decide
@[simp] theorem qo_qeF_ne_qoC : qeF ≠ qoC := by decide
@[simp] theorem qo_qeF_ne_qoJ : qeF ≠ qoJ := by decide
@[simp] theorem qo_qeF_ne_qoA : qeF ≠ qoA := by decide
@[simp] theorem qo_qeF_ne_qoB : qeF ≠ qoB := by decide
@[simp] theorem qo_qeF_ne_qoW : qeF ≠ qoW := by decide
@[simp] theorem qo_qeF_ne_qoR : qeF ≠ qoR := by decide
@[simp] theorem qo_qeF_ne_qeT : qeF ≠ qeT := by decide
@[simp] theorem qo_qeF_ne_qeK : qeF ≠ qeK := by decide
@[simp] theorem qo_qeF_ne_qeS : qeF ≠ qeS := by decide
@[simp] theorem qo_qeF_ne_qeL : qeF ≠ qeL := by decide
@[simp] theorem qo_qeF_ne_qeO : qeF ≠ qeO := by decide
@[simp] theorem qo_qeF_ne_qeDk : qeF ≠ qeDk := by decide
@[simp] theorem qo_qeF_ne_qeB : qeF ≠ qeB := by decide
@[simp] theorem qo_qeF_ne_qeC : qeF ≠ qeC := by decide
@[simp] theorem qo_qeF_ne_qeSl : qeF ≠ qeSl := by decide
@[simp] theorem qo_qeF_ne_qeR : qeF ≠ qeR := by decide
@[simp] theorem qo_qeF_ne_kFu : qeF ≠ kFu := by decide
@[simp] theorem qo_kFu_ne_qeF : kFu ≠ qeF := by decide
@[simp] theorem qo_qeF_ne_kD : qeF ≠ kD := by decide
@[simp] theorem qo_kD_ne_qeF : kD ≠ qeF := by decide
@[simp] theorem qo_qeF_ne_lFl : qeF ≠ lFl := by decide
@[simp] theorem qo_lFl_ne_qeF : lFl ≠ qeF := by decide
@[simp] theorem qo_qeF_ne_lDh : qeF ≠ lDh := by decide
@[simp] theorem qo_lDh_ne_qeF : lDh ≠ qeF := by decide
@[simp] theorem qo_qeF_ne_lDt : qeF ≠ lDt := by decide
@[simp] theorem qo_lDt_ne_qeF : lDt ≠ qeF := by decide
@[simp] theorem qo_qeF_ne_lDg : qeF ≠ lDg := by decide
@[simp] theorem qo_lDg_ne_qeF : lDg ≠ qeF := by decide
@[simp] theorem qo_qeF_ne_lDi : qeF ≠ lDi := by decide
@[simp] theorem qo_lDi_ne_qeF : lDi ≠ qeF := by decide
@[simp] theorem qo_qeF_ne_lRp : qeF ≠ lRp := by decide
@[simp] theorem qo_lRp_ne_qeF : lRp ≠ qeF := by decide
@[simp] theorem qo_qeF_ne_lRn : qeF ≠ lRn := by decide
@[simp] theorem qo_lRn_ne_qeF : lRn ≠ qeF := by decide
@[simp] theorem qo_qeF_ne_lDir : qeF ≠ lDir := by decide
@[simp] theorem qo_lDir_ne_qeF : lDir ≠ qeF := by decide
@[simp] theorem qo_qeF_ne_lFle : qeF ≠ lFle := by decide
@[simp] theorem qo_lFle_ne_qeF : lFle ≠ qeF := by decide
@[simp] theorem qo_qeF_ne_lKb : qeF ≠ lKb := by decide
@[simp] theorem qo_lKb_ne_qeF : lKb ≠ qeF := by decide
@[simp] theorem qo_qeS_ne_qoD : qeS ≠ qoD := by decide
@[simp] theorem qo_qeS_ne_qoS : qeS ≠ qoS := by decide
@[simp] theorem qo_qeS_ne_qoN : qeS ≠ qoN := by decide
@[simp] theorem qo_qeS_ne_qoC : qeS ≠ qoC := by decide
@[simp] theorem qo_qeS_ne_qoJ : qeS ≠ qoJ := by decide
@[simp] theorem qo_qeS_ne_qoA : qeS ≠ qoA := by decide
@[simp] theorem qo_qeS_ne_qoB : qeS ≠ qoB := by decide
@[simp] theorem qo_qeS_ne_qoW : qeS ≠ qoW := by decide
@[simp] theorem qo_qeS_ne_qoR : qeS ≠ qoR := by decide
@[simp] theorem qo_qeS_ne_qeT : qeS ≠ qeT := by decide
@[simp] theorem qo_qeS_ne_qeK : qeS ≠ qeK := by decide
@[simp] theorem qo_qeS_ne_qeF : qeS ≠ qeF := by decide
@[simp] theorem qo_qeS_ne_qeL : qeS ≠ qeL := by decide
@[simp] theorem qo_qeS_ne_qeO : qeS ≠ qeO := by decide
@[simp] theorem qo_qeS_ne_qeDk : qeS ≠ qeDk := by decide
@[simp] theorem qo_qeS_ne_qeB : qeS ≠ qeB := by decide
@[simp] theorem qo_qeS_ne_qeC : qeS ≠ qeC := by decide
@[simp] theorem qo_qeS_ne_qeSl : qeS ≠ qeSl := by decide
@[simp] theorem qo_qeS_ne_qeR : qeS ≠ qeR := by decide
@[simp] theorem qo_qeS_ne_kFu : qeS ≠ kFu := by decide
@[simp] theorem qo_kFu_ne_qeS : kFu ≠ qeS := by decide
@[simp] theorem qo_qeS_ne_kD : qeS ≠ kD := by decide
@[simp] theorem qo_kD_ne_qeS : kD ≠ qeS := by decide
@[simp] theorem qo_qeS_ne_lFl : qeS ≠ lFl := by decide
@[simp] theorem qo_lFl_ne_qeS : lFl ≠ qeS := by decide
@[simp] theorem qo_qeS_ne_lDh : qeS ≠ lDh := by decide
@[simp] theorem qo_lDh_ne_qeS : lDh ≠ qeS := by decide
@[simp] theorem qo_qeS_ne_lDt : qeS ≠ lDt := by decide
@[simp] theorem qo_lDt_ne_qeS : lDt ≠ qeS := by decide
@[simp] theorem qo_qeS_ne_lDg : qeS ≠ lDg := by decide
@[simp] theorem qo_lDg_ne_qeS : lDg ≠ qeS := by decide
@[simp] theorem qo_qeS_ne_lDi : qeS ≠ lDi := by decide
@[simp] theorem qo_lDi_ne_qeS : lDi ≠ qeS := by decide
@[simp] theorem qo_qeS_ne_lRp : qeS ≠ lRp := by decide
@[simp] theorem qo_lRp_ne_qeS : lRp ≠ qeS := by decide
@[simp] theorem qo_qeS_ne_lRn : qeS ≠ lRn := by decide
@[simp] theorem qo_lRn_ne_qeS : lRn ≠ qeS := by decide
@[simp] theorem qo_qeS_ne_lDir : qeS ≠ lDir := by decide
@[simp] theorem qo_lDir_ne_qeS : lDir ≠ qeS := by decide
@[simp] theorem qo_qeS_ne_lFle : qeS ≠ lFle := by decide
@[simp] theorem qo_lFle_ne_qeS : lFle ≠ qeS := by decide
@[simp] theorem qo_qeS_ne_lKb : qeS ≠ lKb := by decide
@[simp] theorem qo_lKb_ne_qeS : lKb ≠ qeS := by decide
@[simp] theorem qo_qeL_ne_qoD : qeL ≠ qoD := by decide
@[simp] theorem qo_qeL_ne_qoS : qeL ≠ qoS := by decide
@[simp] theorem qo_qeL_ne_qoN : qeL ≠ qoN := by decide
@[simp] theorem qo_qeL_ne_qoC : qeL ≠ qoC := by decide
@[simp] theorem qo_qeL_ne_qoJ : qeL ≠ qoJ := by decide
@[simp] theorem qo_qeL_ne_qoA : qeL ≠ qoA := by decide
@[simp] theorem qo_qeL_ne_qoB : qeL ≠ qoB := by decide
@[simp] theorem qo_qeL_ne_qoW : qeL ≠ qoW := by decide
@[simp] theorem qo_qeL_ne_qoR : qeL ≠ qoR := by decide
@[simp] theorem qo_qeL_ne_qeT : qeL ≠ qeT := by decide
@[simp] theorem qo_qeL_ne_qeK : qeL ≠ qeK := by decide
@[simp] theorem qo_qeL_ne_qeF : qeL ≠ qeF := by decide
@[simp] theorem qo_qeL_ne_qeS : qeL ≠ qeS := by decide
@[simp] theorem qo_qeL_ne_qeO : qeL ≠ qeO := by decide
@[simp] theorem qo_qeL_ne_qeDk : qeL ≠ qeDk := by decide
@[simp] theorem qo_qeL_ne_qeB : qeL ≠ qeB := by decide
@[simp] theorem qo_qeL_ne_qeC : qeL ≠ qeC := by decide
@[simp] theorem qo_qeL_ne_qeSl : qeL ≠ qeSl := by decide
@[simp] theorem qo_qeL_ne_qeR : qeL ≠ qeR := by decide
@[simp] theorem qo_qeL_ne_kFu : qeL ≠ kFu := by decide
@[simp] theorem qo_kFu_ne_qeL : kFu ≠ qeL := by decide
@[simp] theorem qo_qeL_ne_kD : qeL ≠ kD := by decide
@[simp] theorem qo_kD_ne_qeL : kD ≠ qeL := by decide
@[simp] theorem qo_qeL_ne_lFl : qeL ≠ lFl := by decide
@[simp] theorem qo_lFl_ne_qeL : lFl ≠ qeL := by decide
@[simp] theorem qo_qeL_ne_lDh : qeL ≠ lDh := by decide
@[simp] theorem qo_lDh_ne_qeL : lDh ≠ qeL := by decide
@[simp] theorem qo_qeL_ne_lDt : qeL ≠ lDt := by decide
@[simp] theorem qo_lDt_ne_qeL : lDt ≠ qeL := by decide
@[simp] theorem qo_qeL_ne_lDg : qeL ≠ lDg := by decide
@[simp] theorem qo_lDg_ne_qeL : lDg ≠ qeL := by decide
@[simp] theorem qo_qeL_ne_lDi : qeL ≠ lDi := by decide
@[simp] theorem qo_lDi_ne_qeL : lDi ≠ qeL := by decide
@[simp] theorem qo_qeL_ne_lRp : qeL ≠ lRp := by decide
@[simp] theorem qo_lRp_ne_qeL : lRp ≠ qeL := by decide
@[simp] theorem qo_qeL_ne_lRn : qeL ≠ lRn := by decide
@[simp] theorem qo_lRn_ne_qeL : lRn ≠ qeL := by decide
@[simp] theorem qo_qeL_ne_lDir : qeL ≠ lDir := by decide
@[simp] theorem qo_lDir_ne_qeL : lDir ≠ qeL := by decide
@[simp] theorem qo_qeL_ne_lFle : qeL ≠ lFle := by decide
@[simp] theorem qo_lFle_ne_qeL : lFle ≠ qeL := by decide
@[simp] theorem qo_qeL_ne_lKb : qeL ≠ lKb := by decide
@[simp] theorem qo_lKb_ne_qeL : lKb ≠ qeL := by decide
@[simp] theorem qo_qeO_ne_qoD : qeO ≠ qoD := by decide
@[simp] theorem qo_qeO_ne_qoS : qeO ≠ qoS := by decide
@[simp] theorem qo_qeO_ne_qoN : qeO ≠ qoN := by decide
@[simp] theorem qo_qeO_ne_qoC : qeO ≠ qoC := by decide
@[simp] theorem qo_qeO_ne_qoJ : qeO ≠ qoJ := by decide
@[simp] theorem qo_qeO_ne_qoA : qeO ≠ qoA := by decide
@[simp] theorem qo_qeO_ne_qoB : qeO ≠ qoB := by decide
@[simp] theorem qo_qeO_ne_qoW : qeO ≠ qoW := by decide
@[simp] theorem qo_qeO_ne_qoR : qeO ≠ qoR := by decide
@[simp] theorem qo_qeO_ne_qeT : qeO ≠ qeT := by decide
@[simp] theorem qo_qeO_ne_qeK : qeO ≠ qeK := by decide
@[simp] theorem qo_qeO_ne_qeF : qeO ≠ qeF := by decide
@[simp] theorem qo_qeO_ne_qeS : qeO ≠ qeS := by decide
@[simp] theorem qo_qeO_ne_qeL : qeO ≠ qeL := by decide
@[simp] theorem qo_qeO_ne_qeDk : qeO ≠ qeDk := by decide
@[simp] theorem qo_qeO_ne_qeB : qeO ≠ qeB := by decide
@[simp] theorem qo_qeO_ne_qeC : qeO ≠ qeC := by decide
@[simp] theorem qo_qeO_ne_qeSl : qeO ≠ qeSl := by decide
@[simp] theorem qo_qeO_ne_qeR : qeO ≠ qeR := by decide
@[simp] theorem qo_qeO_ne_kFu : qeO ≠ kFu := by decide
@[simp] theorem qo_kFu_ne_qeO : kFu ≠ qeO := by decide
@[simp] theorem qo_qeO_ne_kD : qeO ≠ kD := by decide
@[simp] theorem qo_kD_ne_qeO : kD ≠ qeO := by decide
@[simp] theorem qo_qeO_ne_lFl : qeO ≠ lFl := by decide
@[simp] theorem qo_lFl_ne_qeO : lFl ≠ qeO := by decide
@[simp] theorem qo_qeO_ne_lDh : qeO ≠ lDh := by decide
@[simp] theorem qo_lDh_ne_qeO : lDh ≠ qeO := by decide
@[simp] theorem qo_qeO_ne_lDt : qeO ≠ lDt := by decide
@[simp] theorem qo_lDt_ne_qeO : lDt ≠ qeO := by decide
@[simp] theorem qo_qeO_ne_lDg : qeO ≠ lDg := by decide
@[simp] theorem qo_lDg_ne_qeO : lDg ≠ qeO := by decide
@[simp] theorem qo_qeO_ne_lDi : qeO ≠ lDi := by decide
@[simp] theorem qo_lDi_ne_qeO : lDi ≠ qeO := by decide
@[simp] theorem qo_qeO_ne_lRp : qeO ≠ lRp := by decide
@[simp] theorem qo_lRp_ne_qeO : lRp ≠ qeO := by decide
@[simp] theorem qo_qeO_ne_lRn : qeO ≠ lRn := by decide
@[simp] theorem qo_lRn_ne_qeO : lRn ≠ qeO := by decide
@[simp] theorem qo_qeO_ne_lDir : qeO ≠ lDir := by decide
@[simp] theorem qo_lDir_ne_qeO : lDir ≠ qeO := by decide
@[simp] theorem qo_qeO_ne_lFle : qeO ≠ lFle := by decide
@[simp] theorem qo_lFle_ne_qeO : lFle ≠ qeO := by decide
@[simp] theorem qo_qeO_ne_lKb : qeO ≠ lKb := by decide
@[simp] theorem qo_lKb_ne_qeO : lKb ≠ qeO := by decide
@[simp] theorem qo_qeDk_ne_qoD : qeDk ≠ qoD := by decide
@[simp] theorem qo_qeDk_ne_qoS : qeDk ≠ qoS := by decide
@[simp] theorem qo_qeDk_ne_qoN : qeDk ≠ qoN := by decide
@[simp] theorem qo_qeDk_ne_qoC : qeDk ≠ qoC := by decide
@[simp] theorem qo_qeDk_ne_qoJ : qeDk ≠ qoJ := by decide
@[simp] theorem qo_qeDk_ne_qoA : qeDk ≠ qoA := by decide
@[simp] theorem qo_qeDk_ne_qoB : qeDk ≠ qoB := by decide
@[simp] theorem qo_qeDk_ne_qoW : qeDk ≠ qoW := by decide
@[simp] theorem qo_qeDk_ne_qoR : qeDk ≠ qoR := by decide
@[simp] theorem qo_qeDk_ne_qeT : qeDk ≠ qeT := by decide
@[simp] theorem qo_qeDk_ne_qeK : qeDk ≠ qeK := by decide
@[simp] theorem qo_qeDk_ne_qeF : qeDk ≠ qeF := by decide
@[simp] theorem qo_qeDk_ne_qeS : qeDk ≠ qeS := by decide
@[simp] theorem qo_qeDk_ne_qeL : qeDk ≠ qeL := by decide
@[simp] theorem qo_qeDk_ne_qeO : qeDk ≠ qeO := by decide
@[simp] theorem qo_qeDk_ne_qeB : qeDk ≠ qeB := by decide
@[simp] theorem qo_qeDk_ne_qeC : qeDk ≠ qeC := by decide
@[simp] theorem qo_qeDk_ne_qeSl : qeDk ≠ qeSl := by decide
@[simp] theorem qo_qeDk_ne_qeR : qeDk ≠ qeR := by decide
@[simp] theorem qo_qeDk_ne_kFu : qeDk ≠ kFu := by decide
@[simp] theorem qo_kFu_ne_qeDk : kFu ≠ qeDk := by decide
@[simp] theorem qo_qeDk_ne_kD : qeDk ≠ kD := by decide
@[simp] theorem qo_kD_ne_qeDk : kD ≠ qeDk := by decide
@[simp] theorem qo_qeDk_ne_lFl : qeDk ≠ lFl := by decide
@[simp] theorem qo_lFl_ne_qeDk : lFl ≠ qeDk := by decide
@[simp] theorem qo_qeDk_ne_lDh : qeDk ≠ lDh := by decide
@[simp] theorem qo_lDh_ne_qeDk : lDh ≠ qeDk := by decide
@[simp] theorem qo_qeDk_ne_lDt : qeDk ≠ lDt := by decide
@[simp] theorem qo_lDt_ne_qeDk : lDt ≠ qeDk := by decide
@[simp] theorem qo_qeDk_ne_lDg : qeDk ≠ lDg := by decide
@[simp] theorem qo_lDg_ne_qeDk : lDg ≠ qeDk := by decide
@[simp] theorem qo_qeDk_ne_lDi : qeDk ≠ lDi := by decide
@[simp] theorem qo_lDi_ne_qeDk : lDi ≠ qeDk := by decide
@[simp] theorem qo_qeDk_ne_lRp : qeDk ≠ lRp := by decide
@[simp] theorem qo_lRp_ne_qeDk : lRp ≠ qeDk := by decide
@[simp] theorem qo_qeDk_ne_lRn : qeDk ≠ lRn := by decide
@[simp] theorem qo_lRn_ne_qeDk : lRn ≠ qeDk := by decide
@[simp] theorem qo_qeDk_ne_lDir : qeDk ≠ lDir := by decide
@[simp] theorem qo_lDir_ne_qeDk : lDir ≠ qeDk := by decide
@[simp] theorem qo_qeDk_ne_lFle : qeDk ≠ lFle := by decide
@[simp] theorem qo_lFle_ne_qeDk : lFle ≠ qeDk := by decide
@[simp] theorem qo_qeDk_ne_lKb : qeDk ≠ lKb := by decide
@[simp] theorem qo_lKb_ne_qeDk : lKb ≠ qeDk := by decide
@[simp] theorem qo_qeB_ne_qoD : qeB ≠ qoD := by decide
@[simp] theorem qo_qeB_ne_qoS : qeB ≠ qoS := by decide
@[simp] theorem qo_qeB_ne_qoN : qeB ≠ qoN := by decide
@[simp] theorem qo_qeB_ne_qoC : qeB ≠ qoC := by decide
@[simp] theorem qo_qeB_ne_qoJ : qeB ≠ qoJ := by decide
@[simp] theorem qo_qeB_ne_qoA : qeB ≠ qoA := by decide
@[simp] theorem qo_qeB_ne_qoB : qeB ≠ qoB := by decide
@[simp] theorem qo_qeB_ne_qoW : qeB ≠ qoW := by decide
@[simp] theorem qo_qeB_ne_qoR : qeB ≠ qoR := by decide
@[simp] theorem qo_qeB_ne_qeT : qeB ≠ qeT := by decide
@[simp] theorem qo_qeB_ne_qeK : qeB ≠ qeK := by decide
@[simp] theorem qo_qeB_ne_qeF : qeB ≠ qeF := by decide
@[simp] theorem qo_qeB_ne_qeS : qeB ≠ qeS := by decide
@[simp] theorem qo_qeB_ne_qeL : qeB ≠ qeL := by decide
@[simp] theorem qo_qeB_ne_qeO : qeB ≠ qeO := by decide
@[simp] theorem qo_qeB_ne_qeDk : qeB ≠ qeDk := by decide
@[simp] theorem qo_qeB_ne_qeC : qeB ≠ qeC := by decide
@[simp] theorem qo_qeB_ne_qeSl : qeB ≠ qeSl := by decide
@[simp] theorem qo_qeB_ne_qeR : qeB ≠ qeR := by decide
@[simp] theorem qo_qeB_ne_kFu : qeB ≠ kFu := by decide
@[simp] theorem qo_kFu_ne_qeB : kFu ≠ qeB := by decide
@[simp] theorem qo_qeB_ne_kD : qeB ≠ kD := by decide
@[simp] theorem qo_kD_ne_qeB : kD ≠ qeB := by decide
@[simp] theorem qo_qeB_ne_lFl : qeB ≠ lFl := by decide
@[simp] theorem qo_lFl_ne_qeB : lFl ≠ qeB := by decide
@[simp] theorem qo_qeB_ne_lDh : qeB ≠ lDh := by decide
@[simp] theorem qo_lDh_ne_qeB : lDh ≠ qeB := by decide
@[simp] theorem qo_qeB_ne_lDt : qeB ≠ lDt := by decide
@[simp] theorem qo_lDt_ne_qeB : lDt ≠ qeB := by decide
@[simp] theorem qo_qeB_ne_lDg : qeB ≠ lDg := by decide
@[simp] theorem qo_lDg_ne_qeB : lDg ≠ qeB := by decide
@[simp] theorem qo_qeB_ne_lDi : qeB ≠ lDi := by decide
@[simp] theorem qo_lDi_ne_qeB : lDi ≠ qeB := by decide
@[simp] theorem qo_qeB_ne_lRp : qeB ≠ lRp := by decide
@[simp] theorem qo_lRp_ne_qeB : lRp ≠ qeB := by decide
@[simp] theorem qo_qeB_ne_lRn : qeB ≠ lRn := by decide
@[simp] theorem qo_lRn_ne_qeB : lRn ≠ qeB := by decide
@[simp] theorem qo_qeB_ne_lDir : qeB ≠ lDir := by decide
@[simp] theorem qo_lDir_ne_qeB : lDir ≠ qeB := by decide
@[simp] theorem qo_qeB_ne_lFle : qeB ≠ lFle := by decide
@[simp] theorem qo_lFle_ne_qeB : lFle ≠ qeB := by decide
@[simp] theorem qo_qeB_ne_lKb : qeB ≠ lKb := by decide
@[simp] theorem qo_lKb_ne_qeB : lKb ≠ qeB := by decide
@[simp] theorem qo_qeC_ne_qoD : qeC ≠ qoD := by decide
@[simp] theorem qo_qeC_ne_qoS : qeC ≠ qoS := by decide
@[simp] theorem qo_qeC_ne_qoN : qeC ≠ qoN := by decide
@[simp] theorem qo_qeC_ne_qoC : qeC ≠ qoC := by decide
@[simp] theorem qo_qeC_ne_qoJ : qeC ≠ qoJ := by decide
@[simp] theorem qo_qeC_ne_qoA : qeC ≠ qoA := by decide
@[simp] theorem qo_qeC_ne_qoB : qeC ≠ qoB := by decide
@[simp] theorem qo_qeC_ne_qoW : qeC ≠ qoW := by decide
@[simp] theorem qo_qeC_ne_qoR : qeC ≠ qoR := by decide
@[simp] theorem qo_qeC_ne_qeT : qeC ≠ qeT := by decide
@[simp] theorem qo_qeC_ne_qeK : qeC ≠ qeK := by decide
@[simp] theorem qo_qeC_ne_qeF : qeC ≠ qeF := by decide
@[simp] theorem qo_qeC_ne_qeS : qeC ≠ qeS := by decide
@[simp] theorem qo_qeC_ne_qeL : qeC ≠ qeL := by decide
@[simp] theorem qo_qeC_ne_qeO : qeC ≠ qeO := by decide
@[simp] theorem qo_qeC_ne_qeDk : qeC ≠ qeDk := by decide
@[simp] theorem qo_qeC_ne_qeB : qeC ≠ qeB := by decide
@[simp] theorem qo_qeC_ne_qeSl : qeC ≠ qeSl := by decide
@[simp] theorem qo_qeC_ne_qeR : qeC ≠ qeR := by decide
@[simp] theorem qo_qeC_ne_kFu : qeC ≠ kFu := by decide
@[simp] theorem qo_kFu_ne_qeC : kFu ≠ qeC := by decide
@[simp] theorem qo_qeC_ne_kD : qeC ≠ kD := by decide
@[simp] theorem qo_kD_ne_qeC : kD ≠ qeC := by decide
@[simp] theorem qo_qeC_ne_lFl : qeC ≠ lFl := by decide
@[simp] theorem qo_lFl_ne_qeC : lFl ≠ qeC := by decide
@[simp] theorem qo_qeC_ne_lDh : qeC ≠ lDh := by decide
@[simp] theorem qo_lDh_ne_qeC : lDh ≠ qeC := by decide
@[simp] theorem qo_qeC_ne_lDt : qeC ≠ lDt := by decide
@[simp] theorem qo_lDt_ne_qeC : lDt ≠ qeC := by decide
@[simp] theorem qo_qeC_ne_lDg : qeC ≠ lDg := by decide
@[simp] theorem qo_lDg_ne_qeC : lDg ≠ qeC := by decide
@[simp] theorem qo_qeC_ne_lDi : qeC ≠ lDi := by decide
@[simp] theorem qo_lDi_ne_qeC : lDi ≠ qeC := by decide
@[simp] theorem qo_qeC_ne_lRp : qeC ≠ lRp := by decide
@[simp] theorem qo_lRp_ne_qeC : lRp ≠ qeC := by decide
@[simp] theorem qo_qeC_ne_lRn : qeC ≠ lRn := by decide
@[simp] theorem qo_lRn_ne_qeC : lRn ≠ qeC := by decide
@[simp] theorem qo_qeC_ne_lDir : qeC ≠ lDir := by decide
@[simp] theorem qo_lDir_ne_qeC : lDir ≠ qeC := by decide
@[simp] theorem qo_qeC_ne_lFle : qeC ≠ lFle := by decide
@[simp] theorem qo_lFle_ne_qeC : lFle ≠ qeC := by decide
@[simp] theorem qo_qeC_ne_lKb : qeC ≠ lKb := by decide
@[simp] theorem qo_lKb_ne_qeC : lKb ≠ qeC := by decide
@[simp] theorem qo_qeSl_ne_qoD : qeSl ≠ qoD := by decide
@[simp] theorem qo_qeSl_ne_qoS : qeSl ≠ qoS := by decide
@[simp] theorem qo_qeSl_ne_qoN : qeSl ≠ qoN := by decide
@[simp] theorem qo_qeSl_ne_qoC : qeSl ≠ qoC := by decide
@[simp] theorem qo_qeSl_ne_qoJ : qeSl ≠ qoJ := by decide
@[simp] theorem qo_qeSl_ne_qoA : qeSl ≠ qoA := by decide
@[simp] theorem qo_qeSl_ne_qoB : qeSl ≠ qoB := by decide
@[simp] theorem qo_qeSl_ne_qoW : qeSl ≠ qoW := by decide
@[simp] theorem qo_qeSl_ne_qoR : qeSl ≠ qoR := by decide
@[simp] theorem qo_qeSl_ne_qeT : qeSl ≠ qeT := by decide
@[simp] theorem qo_qeSl_ne_qeK : qeSl ≠ qeK := by decide
@[simp] theorem qo_qeSl_ne_qeF : qeSl ≠ qeF := by decide
@[simp] theorem qo_qeSl_ne_qeS : qeSl ≠ qeS := by decide
@[simp] theorem qo_qeSl_ne_qeL : qeSl ≠ qeL := by decide
@[simp] theorem qo_qeSl_ne_qeO : qeSl ≠ qeO := by decide
@[simp] theorem qo_qeSl_ne_qeDk : qeSl ≠ qeDk := by decide
@[simp] theorem qo_qeSl_ne_qeB : qeSl ≠ qeB := by decide
@[simp] theorem qo_qeSl_ne_qeC : qeSl ≠ qeC := by decide
@[simp] theorem qo_qeSl_ne_qeR : qeSl ≠ qeR := by decide
@[simp] theorem qo_qeSl_ne_kFu : qeSl ≠ kFu := by decide
@[simp] theorem qo_kFu_ne_qeSl : kFu ≠ qeSl := by decide
@[simp] theorem qo_qeSl_ne_kD : qeSl ≠ kD := by decide
@[simp] theorem qo_kD_ne_qeSl : kD ≠ qeSl := by decide
@[simp] theorem qo_qeSl_ne_lFl : qeSl ≠ lFl := by decide
@[simp] theorem qo_lFl_ne_qeSl : lFl ≠ qeSl := by decide
@[simp] theorem qo_qeSl_ne_lDh : qeSl ≠ lDh := by decide
@[simp] theorem qo_lDh_ne_qeSl : lDh ≠ qeSl := by decide
@[simp] theorem qo_qeSl_ne_lDt : qeSl ≠ lDt := by decide
@[simp] theorem qo_lDt_ne_qeSl : lDt ≠ qeSl := by decide
@[simp] theorem qo_qeSl_ne_lDg : qeSl ≠ lDg := by decide
@[simp] theorem qo_lDg_ne_qeSl : lDg ≠ qeSl := by decide
@[simp] theorem qo_qeSl_ne_lDi : qeSl ≠ lDi := by decide
@[simp] theorem qo_lDi_ne_qeSl : lDi ≠ qeSl := by decide
@[simp] theorem qo_qeSl_ne_lRp : qeSl ≠ lRp := by decide
@[simp] theorem qo_lRp_ne_qeSl : lRp ≠ qeSl := by decide
@[simp] theorem qo_qeSl_ne_lRn : qeSl ≠ lRn := by decide
@[simp] theorem qo_lRn_ne_qeSl : lRn ≠ qeSl := by decide
@[simp] theorem qo_qeSl_ne_lDir : qeSl ≠ lDir := by decide
@[simp] theorem qo_lDir_ne_qeSl : lDir ≠ qeSl := by decide
@[simp] theorem qo_qeSl_ne_lFle : qeSl ≠ lFle := by decide
@[simp] theorem qo_lFle_ne_qeSl : lFle ≠ qeSl := by decide
@[simp] theorem qo_qeSl_ne_lKb : qeSl ≠ lKb := by decide
@[simp] theorem qo_lKb_ne_qeSl : lKb ≠ qeSl := by decide
@[simp] theorem qo_qeR_ne_qoD : qeR ≠ qoD := by decide
@[simp] theorem qo_qeR_ne_qoS : qeR ≠ qoS := by decide
@[simp] theorem qo_qeR_ne_qoN : qeR ≠ qoN := by decide
@[simp] theorem qo_qeR_ne_qoC : qeR ≠ qoC := by decide
@[simp] theorem qo_qeR_ne_qoJ : qeR ≠ qoJ := by decide
@[simp] theorem qo_qeR_ne_qoA : qeR ≠ qoA := by decide
@[simp] theorem qo_qeR_ne_qoB : qeR ≠ qoB := by decide
@[simp] theorem qo_qeR_ne_qoW : qeR ≠ qoW := by decide
@[simp] theorem qo_qeR_ne_qoR : qeR ≠ qoR := by decide
@[simp] theorem qo_qeR_ne_qeT : qeR ≠ qeT := by decide
@[simp] theorem qo_qeR_ne_qeK : qeR ≠ qeK := by decide
@[simp] theorem qo_qeR_ne_qeF : qeR ≠ qeF := by decide
@[simp] theorem qo_qeR_ne_qeS : qeR ≠ qeS := by decide
@[simp] theorem qo_qeR_ne_qeL : qeR ≠ qeL := by decide
@[simp] theorem qo_qeR_ne_qeO : qeR ≠ qeO := by decide
@[simp] theorem qo_qeR_ne_qeDk : qeR ≠ qeDk := by decide
@[simp] theorem qo_qeR_ne_qeB : qeR ≠ qeB := by decide
@[simp] theorem qo_qeR_ne_qeC : qeR ≠ qeC := by decide
@[simp] theorem qo_qeR_ne_qeSl : qeR ≠ qeSl := by decide
@[simp] theorem qo_qeR_ne_kFu : qeR ≠ kFu := by decide
@[simp] theorem qo_kFu_ne_qeR : kFu ≠ qeR := by decide
@[simp] theorem qo_qeR_ne_kD : qeR ≠ kD := by decide
@[simp] theorem qo_kD_ne_qeR : kD ≠ qeR := by decide
@[simp] theorem qo_qeR_ne_lFl : qeR ≠ lFl := by decide
@[simp] theorem qo_lFl_ne_qeR : lFl ≠ qeR := by decide
@[simp] theorem qo_qeR_ne_lDh : qeR ≠ lDh := by decide
@[simp] theorem qo_lDh_ne_qeR : lDh ≠ qeR := by decide
@[simp] theorem qo_qeR_ne_lDt : qeR ≠ lDt := by decide
@[simp] theorem qo_lDt_ne_qeR : lDt ≠ qeR := by decide
@[simp] theorem qo_qeR_ne_lDg : qeR ≠ lDg := by decide
@[simp] theorem qo_lDg_ne_qeR : lDg ≠ qeR := by decide
@[simp] theorem qo_qeR_ne_lDi : qeR ≠ lDi := by decide
@[simp] theorem qo_lDi_ne_qeR : lDi ≠ qeR := by decide
@[simp] theorem qo_qeR_ne_lRp : qeR ≠ lRp := by decide
@[simp] theorem qo_lRp_ne_qeR : lRp ≠ qeR := by decide
@[simp] theorem qo_qeR_ne_lRn : qeR ≠ lRn := by decide
@[simp] theorem qo_lRn_ne_qeR : lRn ≠ qeR := by decide
@[simp] theorem qo_qeR_ne_lDir : qeR ≠ lDir := by decide
@[simp] theorem qo_lDir_ne_qeR : lDir ≠ qeR := by decide
@[simp] theorem qo_qeR_ne_lFle : qeR ≠ lFle := by decide
@[simp] theorem qo_lFle_ne_qeR : lFle ≠ qeR := by decide
@[simp] theorem qo_qeR_ne_lKb : qeR ≠ lKb := by decide
@[simp] theorem qo_lKb_ne_qeR : lKb ≠ qeR := by decide

theorem codesR_H {C : Ctx} (hc : ExR.CodesR C (ExR.bodyR C)) (H : List (BitVec 64)) :
    ExR.CodesR (ctxH C H) (ExR.bodyR (ctxH C H)) :=
  ⟨hc.absR, hc.fvarB, ⟨hc.fvr.fvr, hc.fvr.memoGet, hc.fvr.memoProbe, hc.fvr.memoSet, hc.fvr.memoIns⟩, hc.internApp,
    hc.internLam, hc.internForallE, hc.internLet, hc.internBVar, hc.internProj⟩

def qoParams : List MlS := [qoD, qoS, qoN, qoC]
def qoLocals : List MlS := [qoJ, qoA, qoB, qoW, qoR]

def qoBody : ProgHOL 64 := prologue qoLocals
  (.ite (.cmp .equal (vv qoN) (.const 0)) (.return (vv qoC))
  (.seq (.assign .local qoJ (.op .sub [vv qoN, .const 1]))
  (.seq (.assign .local qoA (.load .one (.op .add [.op .add [vv qoS, .const 8], .shift .lsl (vv qoJ) (.const 3)])))
  (.seq (.call (some (some (.local, qoB), none)) fAbsRF
      [.const (BitVec.ofNat 64 coreWalkFuel), vv qoD, vv qoJ, .const 0, vv qoA])
  (.seq (.call (some (some (.local, qoW), none)) fInternForallE [vv qoB, vv qoC])
  (.seq (.call (some (some (.local, qoR), none)) fQo [vv qoD, vv qoS, vv qoJ, vv qoW]) (.return (vv qoR))))))))

def qeParams : List MlS := [kFu, kD, qeT, qeK, qeF, qeS]
def qeLocals : List MlS := [qeL, qeO, qeDk, qeB, qeC, qeSl, qeR]

def qeBody : ProgHOL 64 := prologue qeLocals
  (.seq (.assign .local qeL (.load .one (vv qeF)))
  (.seq (.call (some (some (.local, qeO), none)) ExQ.fIrr
      [vv qeF, .const 0, vv qeL, .const (BitVec.ofNat 64 coreWalkFuel), vv qeT, .const 0])
  (.seq (.assign .local qeDk (.op .add [vv kD, vv qeK]))
  (.seq (.call (some (some (.local, qeB), none)) fI [vv kFu, vv qeDk, vv qeO])
  (.seq (.call (some (some (.local, qeC), none)) fAbsRF
      [.const (BitVec.ofNat 64 coreWalkFuel), vv kD, vv qeK, .const 0, vv qeB])
  (.seq (.assign .local qeSl (.load .one (vv qeS)))
  (.seq (.call (some (some (.local, qeR), none)) fQo [vv kD, vv qeS, vv qeSl, vv qeC]) (.return (vv qeR)))))))))

section
variable {σ : Type}

theorem qo_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ qoLocals → (ctxEnv C ++ qoParams.zip vals).get x = none :=
  Knot.params_none C qoLocals qoParams vals (by decide) (by decide)

structure QoCodes (C : Ctx) : Prop where
  cR : ExR.CodesR C (ExR.bodyR C)
  absf : C.code.lookup fAbsRF = some (absRFParams.map (fun p => (p, ShapeHOL.one)), ExR.fastBodyR C, .one)
  self : C.code.lookup fQo = some (qoParams.map (fun p => (p, ShapeHOL.one)), qoBody, .one)

theorem qo_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : QoCodes C)
    (d : Nat) (hd : d < 2 ^ 63) (stk : List EIdx) (o : Nat) (hsl : stk.length < 2 ^ 58) :
    ∀ n (cur : EIdx) (H : List (BitVec 64)) (s : AState), C.H <+: H → BlkAt H o (stk.map Enc.idxW) →
      n ≤ stk.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (qoParams.zip [BitVec.ofNat 64 d, cellA C o, BitVec.ofNat 64 n,
        Enc.idxW cur])) qoBody s (inferLamsOut d stk.toArray n cur) (PostK (ctxH C H)) := by
  intro n
  induction n with
  | zero =>
    intro cur H s hp hb hn
    refine specR_prologue (postK_locals _) (qo_none _ _) ?_
    rw [inferLamsOut]
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, qoParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [↓reduceIte]
    exact specR_returnI _ (Enc.idxW cur) (by simp +decide [Env.get, qoParams, ctxEnv])
      (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ n ih =>
    intro cur H s hp hb hn
    refine specR_prologue (postK_locals _) (qo_none _ _) ?_
    rw [inferLamsOut]
    have hne := ofNat_succ_ne n (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, qoParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [show ¬ (n + 1 = 0) from by omega, ↓reduceIte, Nat.add_sub_cancel]
    refine specR_assignI qoJ _ (BitVec.ofNat 64 n) (by decide)
      (by simp +decide [sev, Env.get, qoParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _) ?_
    have hn' : n < stk.length := by omega
    have h1 := hb.2 n (by simpa using hn')
    rw [List.getElem_map] at h1
    refine UD.specR_heapLoadI' (C := ctxH C H) qoA _ (o + 1 + n) (Enc.idxW stk[n]) h1 (by decide)
      (by simp +decide [sev, Env.get, qoParams, ctxEnv]; show _ = cellA C (o + 1 + n); rw [← cellA_shl C (o + 1) n (by omega), ← cellA_add8]; rfl) ?_
    have hgx : stk.toArray[n]! = stk[n] := by simp [hn']
    rw [hgx]
    refine ILP.callE_spec (C := ctxH C H) qoB fAbsRF absRFParams
      [.const (BitVec.ofNat 64 coreWalkFuel), vv qoD, vv qoJ, .const 0, vv qoA] (ExR.fastBodyR C)
      [BitVec.ofNat 64 coreWalkFuel, BitVec.ofNat 64 d, BitVec.ofNat 64 n, BitVec.ofNat 64 0, Enc.idxW stk[n]]
      (by decide) rfl (by decide) hc.absf ⟨rfl, by simp +decide [Env.get, qoParams, ctxEnv], by simp, rfl, by simp, trivial⟩
      (ExR.fastR_spec ra (ctxH C H) (ctxOK_H hok H) (codesR_H hc.cR H) s coreWalkFuel d n 0 stk[n]
        CV.coreWalkFuel_lt hd (by omega) (by decide)) (fun ta s1 => ?_)
    refine specR_internForallEI ra (ctxOK_H hok H) hc.cR.internForallE qoW (vv qoB) (vv qoC) ta cur (by decide)
      (by simp) (by simp +decide [Env.get, qoParams, ctxEnv]) (fun nd s2 => ?_)
    refine specR_congr (m' := inferLamsOut d stk.toArray n nd >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H) qoR fQo qoParams [vv qoD, vv qoS, vv qoJ, vv qoW] qoBody
      [BitVec.ofNat 64 d, cellA C o, BitVec.ofNat 64 n, Enc.idxW nd] (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [Env.get, qoParams, ctxEnv], by simp +decide [Env.get, qoParams, ctxEnv] <;> rfl, by simp, by simp, trivial⟩
      (PostK (ctxH C H)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu qoParams _ rfl hlk) (ih nd H s2 hp hb (by omega)))
      (fun r w s3 H3 hp3 hw => ?_)
    subst hw
    exact specR_returnI _ (Enc.idxW r) (by simp) (fun t ht => ⟨H3, hp3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem qe_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ qeLocals → (ctxEnv C ++ qeParams.zip vals).get x = none :=
  Knot.params_none C qeLocals qeParams vals (by decide) (by decide)

structure QeCodes (C : Ctx) : Prop where
  qo : QoCodes C
  i : C.code.lookup fI = some (pmap kParams, inferE C fIB, .one)
  irr : C.code.lookup ExQ.fIrr = some (ExQ.irrParams.map (fun p => (p, ShapeHOL.one)), ExQ.irrBody C, .one)
  q : ExQ.CodesQ C

theorem qe_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (hc : QeCodes C)
    (hI : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (inferE C fIB) s1 ((knot mode C n).infer d' e')
      (PostK (ctxH C H)))
    (s : AState) (d k : Nat) (t : EIdx) (fvs stk : List EIdx) (ofv ost : Nat)
    (H : List (BitVec 64)) (hp : C.H <+: H) (hbf : BlkAt H ofv (fvs.map Enc.idxW))
    (hbs : BlkAt H ost (stk.map Enc.idxW)) (hfl : fvs.length < 2 ^ 58) (hsl : stk.length < 2 ^ 58)
    (hdk : d + k < 2 ^ 63) :
    SpecR (σ := σ) (Pre (ctxH C H) s (qeParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW t,
      BitVec.ofNat 64 k, cellA C ofv, cellA C ost])) qeBody s
      (inferLamsLeaf (knot mode C n) d t k fvs.toArray stk.toArray) (PostK (ctxH C H)) := by
  refine specR_prologue (postK_locals _) (qe_none _ _) ?_
  unfold inferLamsLeaf
  simp only [bind_assoc, instantiateListFast, List.size_toArray]
  obtain ⟨hlo, hlv0⟩ := blkAt_get0 hbf
  refine UD.specR_heapLoadI' (C := ctxH C H) qeL (vv qeF) ofv (BitVec.ofNat 64 fvs.length)
    (by show H[ofv]? = _; rw [List.getElem?_eq_getElem hlo, hlv0]; simp) (by decide)
    (by simp +decide [Env.get, qeParams, ctxEnv]; rfl) ?_
  refine ILP.callE_spec (C := ctxH C H) qeO ExQ.fIrr ExQ.irrParams
    [vv qeF, .const 0, vv qeL, .const (BitVec.ofNat 64 coreWalkFuel), vv qeT, .const 0] (ExQ.irrBody C)
    [cellA C ofv, BitVec.ofNat 64 0, BitVec.ofNat 64 fvs.length, BitVec.ofNat 64 coreWalkFuel, Enc.idxW t,
      BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.irr
    ⟨by simp +decide [Env.get, qeParams, ctxEnv] <;> rfl, rfl, by simp, rfl, by simp +decide [Env.get, qeParams, ctxEnv], rfl, trivial⟩
    (ExQ.irr_spec ra (ctxH C H) (ctxOK_H hok H) (codesQ_H hc.q H) fvs.toArray ofv
      (show BlkAt H ofv (fvs.toArray.toList.map Enc.idxW) by simpa using hbf) (by simp; omega) s
      coreWalkFuel 0 fvs.length 0 t CV.coreWalkFuel_lt (by decide) (by omega) (by decide)) (fun ob s1 => ?_)
  refine specR_assignI qeDk _ (BitVec.ofNat 64 (d + k)) (by decide)
    (by simp +decide [sev, Env.get, qeParams, ctxEnv]; exact BitVec.ofNat_add_ofNat ..) ?_
  refine Big.specR_callKC (C := ctxH C H) qeB fI kParams [vv kFu, vv qeDk, vv qeO] (inferE C fIB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 (d + k), Enc.idxW ob] (by decide) rfl (by decide) hc.i
    ⟨by simp +decide [Env.get, qeParams, ctxEnv], by simp, by simp, trivial⟩ (hI H s1 (d + k) ob hp) (fun bt s2 H2 hp2 _ => ?_)
  refine ILP.callE_spec (C := ctxH C H2) qeC fAbsRF absRFParams
    [.const (BitVec.ofNat 64 coreWalkFuel), vv kD, vv qeK, .const 0, vv qeB] (ExR.fastBodyR C)
    [BitVec.ofNat 64 coreWalkFuel, BitVec.ofNat 64 d, BitVec.ofNat 64 k, BitVec.ofNat 64 0, Enc.idxW bt]
    (by decide) rfl (by decide) hc.qo.absf ⟨rfl, by simp +decide [Env.get, qeParams, ctxEnv], by simp +decide [Env.get, qeParams, ctxEnv], rfl, by simp, trivial⟩
    (ExR.fastR_spec ra (ctxH C H2) (ctxOK_H hok H2) (codesR_H hc.qo.cR H2) s2 coreWalkFuel d k 0 bt
      CV.coreWalkFuel_lt (by omega) (by omega) (by decide)) (fun cur s3 => ?_)
  have hbs2 := blkAt_mono hbs hp2
  obtain ⟨hlo2, hlv2⟩ := blkAt_get0 hbs2
  refine UD.specR_heapLoadI' (C := ctxH C H2) qeSl (vv qeS) ost (BitVec.ofNat 64 stk.length)
    (by show H2[ost]? = _; rw [List.getElem?_eq_getElem hlo2, hlv2]; simp) (by decide)
    (by simp +decide [Env.get, qeParams, ctxEnv]; rfl) ?_
  refine specR_congr (m' := inferLamsOut d stk.toArray stk.length cur >>= fun r => pure r) (by simp) ?_
  refine specR_callNIH (C := ctxH C H2) qeR fQo qoParams [vv kD, vv qeS, vv qeSl, vv qeC] qoBody
    [BitVec.ofNat 64 d, cellA C ost, BitVec.ofNat 64 stk.length, Enc.idxW cur] (by decide) rfl (by decide)
    hc.qo.self ⟨by simp +decide [Env.get, qeParams, ctxEnv], by simp +decide [Env.get, qeParams, ctxEnv] <;> rfl, by simp, by simp, trivial⟩
    (PostK (ctxH C H2)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu qoParams _ rfl hlk)
      (qo_spec ra C hok hc.qo d (by omega) stk ost hsl stk.length cur H2 s3 (hp.trans hp2) hbs2 (Nat.le_refl _)))
    (fun r w s4 H4 hp4 hw => ?_)
  subst hw
  exact specR_returnI _ (Enc.idxW r) (by simp) (fun t ht => ⟨H4, hp2.trans hp4, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
