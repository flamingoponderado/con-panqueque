import ConPanqueque.T.Core.InferLams
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# The λ arm: the `inferLams` loop and the `inferLam` wrapper

`qn` peels a run of λ binders: open each domain against the free variables so far, check that its type
`whnf`s to a sort, open the binder and stack the opened domain. `qm` is the `.lam` arm's wrapper: it checks
the outer domain, then runs `qn` from `k = 1` with singleton blocks (a depth of `2 ^ 62` or more declines).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def qnP := ofString "qnn_p"
def qnT := ofString "qnn_t"
def qnK := ofString "qnn_k"
def qnF := ofString "qnn_f"
def qnS := ofString "qnn_s"
def qnTy := ofString "qnn_ty"
def qnB := ofString "qnn_b"
def qnL := ofString "qnn_l"
def qnO := ofString "qnn_o"
def qnDk := ofString "qnn_dk"
def qnA := ofString "qnn_a"
def qnH := ofString "qnn_h"
def qnV := ofString "qnn_v"
def qnF2 := ofString "qnn_f2"
def qnS2 := ofString "qnn_s2"
def qnR := ofString "qnn_r"
def qmA := ofString "qmn_a"
def qmH := ofString "qmn_h"
def qmV := ofString "qmn_v"
def qmE := ofString "qmn_e"
def qmF := ofString "qmn_f"
def qmS := ofString "qmn_s"
def qmR := ofString "qmn_r"
def fQn := ofString "inferLams"

@[simp] theorem qn_qnP_ne_qnT : qnP ≠ qnT := by decide
@[simp] theorem qn_qnP_ne_qnK : qnP ≠ qnK := by decide
@[simp] theorem qn_qnP_ne_qnF : qnP ≠ qnF := by decide
@[simp] theorem qn_qnP_ne_qnS : qnP ≠ qnS := by decide
@[simp] theorem qn_qnP_ne_qnTy : qnP ≠ qnTy := by decide
@[simp] theorem qn_qnP_ne_qnB : qnP ≠ qnB := by decide
@[simp] theorem qn_qnP_ne_qnL : qnP ≠ qnL := by decide
@[simp] theorem qn_qnP_ne_qnO : qnP ≠ qnO := by decide
@[simp] theorem qn_qnP_ne_qnDk : qnP ≠ qnDk := by decide
@[simp] theorem qn_qnP_ne_qnA : qnP ≠ qnA := by decide
@[simp] theorem qn_qnP_ne_qnH : qnP ≠ qnH := by decide
@[simp] theorem qn_qnP_ne_qnV : qnP ≠ qnV := by decide
@[simp] theorem qn_qnP_ne_qnF2 : qnP ≠ qnF2 := by decide
@[simp] theorem qn_qnP_ne_qnS2 : qnP ≠ qnS2 := by decide
@[simp] theorem qn_qnP_ne_qnR : qnP ≠ qnR := by decide
@[simp] theorem qn_qnP_ne_kFu : qnP ≠ kFu := by decide
@[simp] theorem qn_kFu_ne_qnP : kFu ≠ qnP := by decide
@[simp] theorem qn_qnP_ne_kD : qnP ≠ kD := by decide
@[simp] theorem qn_kD_ne_qnP : kD ≠ qnP := by decide
@[simp] theorem qn_qnP_ne_ibT1 : qnP ≠ ibT1 := by decide
@[simp] theorem qn_ibT1_ne_qnP : ibT1 ≠ qnP := by decide
@[simp] theorem qn_qnP_ne_ibT2 : qnP ≠ ibT2 := by decide
@[simp] theorem qn_ibT2_ne_qnP : ibT2 ≠ qnP := by decide
@[simp] theorem qn_qnP_ne_lFl : qnP ≠ lFl := by decide
@[simp] theorem qn_lFl_ne_qnP : lFl ≠ qnP := by decide
@[simp] theorem qn_qnP_ne_lDh : qnP ≠ lDh := by decide
@[simp] theorem qn_lDh_ne_qnP : lDh ≠ qnP := by decide
@[simp] theorem qn_qnP_ne_lDt : qnP ≠ lDt := by decide
@[simp] theorem qn_lDt_ne_qnP : lDt ≠ qnP := by decide
@[simp] theorem qn_qnP_ne_lDg : qnP ≠ lDg := by decide
@[simp] theorem qn_lDg_ne_qnP : lDg ≠ qnP := by decide
@[simp] theorem qn_qnP_ne_lDi : qnP ≠ lDi := by decide
@[simp] theorem qn_lDi_ne_qnP : lDi ≠ qnP := by decide
@[simp] theorem qn_qnP_ne_lRp : qnP ≠ lRp := by decide
@[simp] theorem qn_lRp_ne_qnP : lRp ≠ qnP := by decide
@[simp] theorem qn_qnP_ne_lRn : qnP ≠ lRn := by decide
@[simp] theorem qn_lRn_ne_qnP : lRn ≠ qnP := by decide
@[simp] theorem qn_qnP_ne_lDir : qnP ≠ lDir := by decide
@[simp] theorem qn_lDir_ne_qnP : lDir ≠ qnP := by decide
@[simp] theorem qn_qnP_ne_lFle : qnP ≠ lFle := by decide
@[simp] theorem qn_lFle_ne_qnP : lFle ≠ qnP := by decide
@[simp] theorem qn_qnP_ne_lKb : qnP ≠ lKb := by decide
@[simp] theorem qn_lKb_ne_qnP : lKb ≠ qnP := by decide
@[simp] theorem qn_qnT_ne_qnP : qnT ≠ qnP := by decide
@[simp] theorem qn_qnT_ne_qnK : qnT ≠ qnK := by decide
@[simp] theorem qn_qnT_ne_qnF : qnT ≠ qnF := by decide
@[simp] theorem qn_qnT_ne_qnS : qnT ≠ qnS := by decide
@[simp] theorem qn_qnT_ne_qnTy : qnT ≠ qnTy := by decide
@[simp] theorem qn_qnT_ne_qnB : qnT ≠ qnB := by decide
@[simp] theorem qn_qnT_ne_qnL : qnT ≠ qnL := by decide
@[simp] theorem qn_qnT_ne_qnO : qnT ≠ qnO := by decide
@[simp] theorem qn_qnT_ne_qnDk : qnT ≠ qnDk := by decide
@[simp] theorem qn_qnT_ne_qnA : qnT ≠ qnA := by decide
@[simp] theorem qn_qnT_ne_qnH : qnT ≠ qnH := by decide
@[simp] theorem qn_qnT_ne_qnV : qnT ≠ qnV := by decide
@[simp] theorem qn_qnT_ne_qnF2 : qnT ≠ qnF2 := by decide
@[simp] theorem qn_qnT_ne_qnS2 : qnT ≠ qnS2 := by decide
@[simp] theorem qn_qnT_ne_qnR : qnT ≠ qnR := by decide
@[simp] theorem qn_qnT_ne_kFu : qnT ≠ kFu := by decide
@[simp] theorem qn_kFu_ne_qnT : kFu ≠ qnT := by decide
@[simp] theorem qn_qnT_ne_kD : qnT ≠ kD := by decide
@[simp] theorem qn_kD_ne_qnT : kD ≠ qnT := by decide
@[simp] theorem qn_qnT_ne_ibT1 : qnT ≠ ibT1 := by decide
@[simp] theorem qn_ibT1_ne_qnT : ibT1 ≠ qnT := by decide
@[simp] theorem qn_qnT_ne_ibT2 : qnT ≠ ibT2 := by decide
@[simp] theorem qn_ibT2_ne_qnT : ibT2 ≠ qnT := by decide
@[simp] theorem qn_qnT_ne_lFl : qnT ≠ lFl := by decide
@[simp] theorem qn_lFl_ne_qnT : lFl ≠ qnT := by decide
@[simp] theorem qn_qnT_ne_lDh : qnT ≠ lDh := by decide
@[simp] theorem qn_lDh_ne_qnT : lDh ≠ qnT := by decide
@[simp] theorem qn_qnT_ne_lDt : qnT ≠ lDt := by decide
@[simp] theorem qn_lDt_ne_qnT : lDt ≠ qnT := by decide
@[simp] theorem qn_qnT_ne_lDg : qnT ≠ lDg := by decide
@[simp] theorem qn_lDg_ne_qnT : lDg ≠ qnT := by decide
@[simp] theorem qn_qnT_ne_lDi : qnT ≠ lDi := by decide
@[simp] theorem qn_lDi_ne_qnT : lDi ≠ qnT := by decide
@[simp] theorem qn_qnT_ne_lRp : qnT ≠ lRp := by decide
@[simp] theorem qn_lRp_ne_qnT : lRp ≠ qnT := by decide
@[simp] theorem qn_qnT_ne_lRn : qnT ≠ lRn := by decide
@[simp] theorem qn_lRn_ne_qnT : lRn ≠ qnT := by decide
@[simp] theorem qn_qnT_ne_lDir : qnT ≠ lDir := by decide
@[simp] theorem qn_lDir_ne_qnT : lDir ≠ qnT := by decide
@[simp] theorem qn_qnT_ne_lFle : qnT ≠ lFle := by decide
@[simp] theorem qn_lFle_ne_qnT : lFle ≠ qnT := by decide
@[simp] theorem qn_qnT_ne_lKb : qnT ≠ lKb := by decide
@[simp] theorem qn_lKb_ne_qnT : lKb ≠ qnT := by decide
@[simp] theorem qn_qnK_ne_qnP : qnK ≠ qnP := by decide
@[simp] theorem qn_qnK_ne_qnT : qnK ≠ qnT := by decide
@[simp] theorem qn_qnK_ne_qnF : qnK ≠ qnF := by decide
@[simp] theorem qn_qnK_ne_qnS : qnK ≠ qnS := by decide
@[simp] theorem qn_qnK_ne_qnTy : qnK ≠ qnTy := by decide
@[simp] theorem qn_qnK_ne_qnB : qnK ≠ qnB := by decide
@[simp] theorem qn_qnK_ne_qnL : qnK ≠ qnL := by decide
@[simp] theorem qn_qnK_ne_qnO : qnK ≠ qnO := by decide
@[simp] theorem qn_qnK_ne_qnDk : qnK ≠ qnDk := by decide
@[simp] theorem qn_qnK_ne_qnA : qnK ≠ qnA := by decide
@[simp] theorem qn_qnK_ne_qnH : qnK ≠ qnH := by decide
@[simp] theorem qn_qnK_ne_qnV : qnK ≠ qnV := by decide
@[simp] theorem qn_qnK_ne_qnF2 : qnK ≠ qnF2 := by decide
@[simp] theorem qn_qnK_ne_qnS2 : qnK ≠ qnS2 := by decide
@[simp] theorem qn_qnK_ne_qnR : qnK ≠ qnR := by decide
@[simp] theorem qn_qnK_ne_kFu : qnK ≠ kFu := by decide
@[simp] theorem qn_kFu_ne_qnK : kFu ≠ qnK := by decide
@[simp] theorem qn_qnK_ne_kD : qnK ≠ kD := by decide
@[simp] theorem qn_kD_ne_qnK : kD ≠ qnK := by decide
@[simp] theorem qn_qnK_ne_ibT1 : qnK ≠ ibT1 := by decide
@[simp] theorem qn_ibT1_ne_qnK : ibT1 ≠ qnK := by decide
@[simp] theorem qn_qnK_ne_ibT2 : qnK ≠ ibT2 := by decide
@[simp] theorem qn_ibT2_ne_qnK : ibT2 ≠ qnK := by decide
@[simp] theorem qn_qnK_ne_lFl : qnK ≠ lFl := by decide
@[simp] theorem qn_lFl_ne_qnK : lFl ≠ qnK := by decide
@[simp] theorem qn_qnK_ne_lDh : qnK ≠ lDh := by decide
@[simp] theorem qn_lDh_ne_qnK : lDh ≠ qnK := by decide
@[simp] theorem qn_qnK_ne_lDt : qnK ≠ lDt := by decide
@[simp] theorem qn_lDt_ne_qnK : lDt ≠ qnK := by decide
@[simp] theorem qn_qnK_ne_lDg : qnK ≠ lDg := by decide
@[simp] theorem qn_lDg_ne_qnK : lDg ≠ qnK := by decide
@[simp] theorem qn_qnK_ne_lDi : qnK ≠ lDi := by decide
@[simp] theorem qn_lDi_ne_qnK : lDi ≠ qnK := by decide
@[simp] theorem qn_qnK_ne_lRp : qnK ≠ lRp := by decide
@[simp] theorem qn_lRp_ne_qnK : lRp ≠ qnK := by decide
@[simp] theorem qn_qnK_ne_lRn : qnK ≠ lRn := by decide
@[simp] theorem qn_lRn_ne_qnK : lRn ≠ qnK := by decide
@[simp] theorem qn_qnK_ne_lDir : qnK ≠ lDir := by decide
@[simp] theorem qn_lDir_ne_qnK : lDir ≠ qnK := by decide
@[simp] theorem qn_qnK_ne_lFle : qnK ≠ lFle := by decide
@[simp] theorem qn_lFle_ne_qnK : lFle ≠ qnK := by decide
@[simp] theorem qn_qnK_ne_lKb : qnK ≠ lKb := by decide
@[simp] theorem qn_lKb_ne_qnK : lKb ≠ qnK := by decide
@[simp] theorem qn_qnF_ne_qnP : qnF ≠ qnP := by decide
@[simp] theorem qn_qnF_ne_qnT : qnF ≠ qnT := by decide
@[simp] theorem qn_qnF_ne_qnK : qnF ≠ qnK := by decide
@[simp] theorem qn_qnF_ne_qnS : qnF ≠ qnS := by decide
@[simp] theorem qn_qnF_ne_qnTy : qnF ≠ qnTy := by decide
@[simp] theorem qn_qnF_ne_qnB : qnF ≠ qnB := by decide
@[simp] theorem qn_qnF_ne_qnL : qnF ≠ qnL := by decide
@[simp] theorem qn_qnF_ne_qnO : qnF ≠ qnO := by decide
@[simp] theorem qn_qnF_ne_qnDk : qnF ≠ qnDk := by decide
@[simp] theorem qn_qnF_ne_qnA : qnF ≠ qnA := by decide
@[simp] theorem qn_qnF_ne_qnH : qnF ≠ qnH := by decide
@[simp] theorem qn_qnF_ne_qnV : qnF ≠ qnV := by decide
@[simp] theorem qn_qnF_ne_qnF2 : qnF ≠ qnF2 := by decide
@[simp] theorem qn_qnF_ne_qnS2 : qnF ≠ qnS2 := by decide
@[simp] theorem qn_qnF_ne_qnR : qnF ≠ qnR := by decide
@[simp] theorem qn_qnF_ne_kFu : qnF ≠ kFu := by decide
@[simp] theorem qn_kFu_ne_qnF : kFu ≠ qnF := by decide
@[simp] theorem qn_qnF_ne_kD : qnF ≠ kD := by decide
@[simp] theorem qn_kD_ne_qnF : kD ≠ qnF := by decide
@[simp] theorem qn_qnF_ne_ibT1 : qnF ≠ ibT1 := by decide
@[simp] theorem qn_ibT1_ne_qnF : ibT1 ≠ qnF := by decide
@[simp] theorem qn_qnF_ne_ibT2 : qnF ≠ ibT2 := by decide
@[simp] theorem qn_ibT2_ne_qnF : ibT2 ≠ qnF := by decide
@[simp] theorem qn_qnF_ne_lFl : qnF ≠ lFl := by decide
@[simp] theorem qn_lFl_ne_qnF : lFl ≠ qnF := by decide
@[simp] theorem qn_qnF_ne_lDh : qnF ≠ lDh := by decide
@[simp] theorem qn_lDh_ne_qnF : lDh ≠ qnF := by decide
@[simp] theorem qn_qnF_ne_lDt : qnF ≠ lDt := by decide
@[simp] theorem qn_lDt_ne_qnF : lDt ≠ qnF := by decide
@[simp] theorem qn_qnF_ne_lDg : qnF ≠ lDg := by decide
@[simp] theorem qn_lDg_ne_qnF : lDg ≠ qnF := by decide
@[simp] theorem qn_qnF_ne_lDi : qnF ≠ lDi := by decide
@[simp] theorem qn_lDi_ne_qnF : lDi ≠ qnF := by decide
@[simp] theorem qn_qnF_ne_lRp : qnF ≠ lRp := by decide
@[simp] theorem qn_lRp_ne_qnF : lRp ≠ qnF := by decide
@[simp] theorem qn_qnF_ne_lRn : qnF ≠ lRn := by decide
@[simp] theorem qn_lRn_ne_qnF : lRn ≠ qnF := by decide
@[simp] theorem qn_qnF_ne_lDir : qnF ≠ lDir := by decide
@[simp] theorem qn_lDir_ne_qnF : lDir ≠ qnF := by decide
@[simp] theorem qn_qnF_ne_lFle : qnF ≠ lFle := by decide
@[simp] theorem qn_lFle_ne_qnF : lFle ≠ qnF := by decide
@[simp] theorem qn_qnF_ne_lKb : qnF ≠ lKb := by decide
@[simp] theorem qn_lKb_ne_qnF : lKb ≠ qnF := by decide
@[simp] theorem qn_qnS_ne_qnP : qnS ≠ qnP := by decide
@[simp] theorem qn_qnS_ne_qnT : qnS ≠ qnT := by decide
@[simp] theorem qn_qnS_ne_qnK : qnS ≠ qnK := by decide
@[simp] theorem qn_qnS_ne_qnF : qnS ≠ qnF := by decide
@[simp] theorem qn_qnS_ne_qnTy : qnS ≠ qnTy := by decide
@[simp] theorem qn_qnS_ne_qnB : qnS ≠ qnB := by decide
@[simp] theorem qn_qnS_ne_qnL : qnS ≠ qnL := by decide
@[simp] theorem qn_qnS_ne_qnO : qnS ≠ qnO := by decide
@[simp] theorem qn_qnS_ne_qnDk : qnS ≠ qnDk := by decide
@[simp] theorem qn_qnS_ne_qnA : qnS ≠ qnA := by decide
@[simp] theorem qn_qnS_ne_qnH : qnS ≠ qnH := by decide
@[simp] theorem qn_qnS_ne_qnV : qnS ≠ qnV := by decide
@[simp] theorem qn_qnS_ne_qnF2 : qnS ≠ qnF2 := by decide
@[simp] theorem qn_qnS_ne_qnS2 : qnS ≠ qnS2 := by decide
@[simp] theorem qn_qnS_ne_qnR : qnS ≠ qnR := by decide
@[simp] theorem qn_qnS_ne_kFu : qnS ≠ kFu := by decide
@[simp] theorem qn_kFu_ne_qnS : kFu ≠ qnS := by decide
@[simp] theorem qn_qnS_ne_kD : qnS ≠ kD := by decide
@[simp] theorem qn_kD_ne_qnS : kD ≠ qnS := by decide
@[simp] theorem qn_qnS_ne_ibT1 : qnS ≠ ibT1 := by decide
@[simp] theorem qn_ibT1_ne_qnS : ibT1 ≠ qnS := by decide
@[simp] theorem qn_qnS_ne_ibT2 : qnS ≠ ibT2 := by decide
@[simp] theorem qn_ibT2_ne_qnS : ibT2 ≠ qnS := by decide
@[simp] theorem qn_qnS_ne_lFl : qnS ≠ lFl := by decide
@[simp] theorem qn_lFl_ne_qnS : lFl ≠ qnS := by decide
@[simp] theorem qn_qnS_ne_lDh : qnS ≠ lDh := by decide
@[simp] theorem qn_lDh_ne_qnS : lDh ≠ qnS := by decide
@[simp] theorem qn_qnS_ne_lDt : qnS ≠ lDt := by decide
@[simp] theorem qn_lDt_ne_qnS : lDt ≠ qnS := by decide
@[simp] theorem qn_qnS_ne_lDg : qnS ≠ lDg := by decide
@[simp] theorem qn_lDg_ne_qnS : lDg ≠ qnS := by decide
@[simp] theorem qn_qnS_ne_lDi : qnS ≠ lDi := by decide
@[simp] theorem qn_lDi_ne_qnS : lDi ≠ qnS := by decide
@[simp] theorem qn_qnS_ne_lRp : qnS ≠ lRp := by decide
@[simp] theorem qn_lRp_ne_qnS : lRp ≠ qnS := by decide
@[simp] theorem qn_qnS_ne_lRn : qnS ≠ lRn := by decide
@[simp] theorem qn_lRn_ne_qnS : lRn ≠ qnS := by decide
@[simp] theorem qn_qnS_ne_lDir : qnS ≠ lDir := by decide
@[simp] theorem qn_lDir_ne_qnS : lDir ≠ qnS := by decide
@[simp] theorem qn_qnS_ne_lFle : qnS ≠ lFle := by decide
@[simp] theorem qn_lFle_ne_qnS : lFle ≠ qnS := by decide
@[simp] theorem qn_qnS_ne_lKb : qnS ≠ lKb := by decide
@[simp] theorem qn_lKb_ne_qnS : lKb ≠ qnS := by decide
@[simp] theorem qn_qnTy_ne_qnP : qnTy ≠ qnP := by decide
@[simp] theorem qn_qnTy_ne_qnT : qnTy ≠ qnT := by decide
@[simp] theorem qn_qnTy_ne_qnK : qnTy ≠ qnK := by decide
@[simp] theorem qn_qnTy_ne_qnF : qnTy ≠ qnF := by decide
@[simp] theorem qn_qnTy_ne_qnS : qnTy ≠ qnS := by decide
@[simp] theorem qn_qnTy_ne_qnB : qnTy ≠ qnB := by decide
@[simp] theorem qn_qnTy_ne_qnL : qnTy ≠ qnL := by decide
@[simp] theorem qn_qnTy_ne_qnO : qnTy ≠ qnO := by decide
@[simp] theorem qn_qnTy_ne_qnDk : qnTy ≠ qnDk := by decide
@[simp] theorem qn_qnTy_ne_qnA : qnTy ≠ qnA := by decide
@[simp] theorem qn_qnTy_ne_qnH : qnTy ≠ qnH := by decide
@[simp] theorem qn_qnTy_ne_qnV : qnTy ≠ qnV := by decide
@[simp] theorem qn_qnTy_ne_qnF2 : qnTy ≠ qnF2 := by decide
@[simp] theorem qn_qnTy_ne_qnS2 : qnTy ≠ qnS2 := by decide
@[simp] theorem qn_qnTy_ne_qnR : qnTy ≠ qnR := by decide
@[simp] theorem qn_qnTy_ne_kFu : qnTy ≠ kFu := by decide
@[simp] theorem qn_kFu_ne_qnTy : kFu ≠ qnTy := by decide
@[simp] theorem qn_qnTy_ne_kD : qnTy ≠ kD := by decide
@[simp] theorem qn_kD_ne_qnTy : kD ≠ qnTy := by decide
@[simp] theorem qn_qnTy_ne_ibT1 : qnTy ≠ ibT1 := by decide
@[simp] theorem qn_ibT1_ne_qnTy : ibT1 ≠ qnTy := by decide
@[simp] theorem qn_qnTy_ne_ibT2 : qnTy ≠ ibT2 := by decide
@[simp] theorem qn_ibT2_ne_qnTy : ibT2 ≠ qnTy := by decide
@[simp] theorem qn_qnTy_ne_lFl : qnTy ≠ lFl := by decide
@[simp] theorem qn_lFl_ne_qnTy : lFl ≠ qnTy := by decide
@[simp] theorem qn_qnTy_ne_lDh : qnTy ≠ lDh := by decide
@[simp] theorem qn_lDh_ne_qnTy : lDh ≠ qnTy := by decide
@[simp] theorem qn_qnTy_ne_lDt : qnTy ≠ lDt := by decide
@[simp] theorem qn_lDt_ne_qnTy : lDt ≠ qnTy := by decide
@[simp] theorem qn_qnTy_ne_lDg : qnTy ≠ lDg := by decide
@[simp] theorem qn_lDg_ne_qnTy : lDg ≠ qnTy := by decide
@[simp] theorem qn_qnTy_ne_lDi : qnTy ≠ lDi := by decide
@[simp] theorem qn_lDi_ne_qnTy : lDi ≠ qnTy := by decide
@[simp] theorem qn_qnTy_ne_lRp : qnTy ≠ lRp := by decide
@[simp] theorem qn_lRp_ne_qnTy : lRp ≠ qnTy := by decide
@[simp] theorem qn_qnTy_ne_lRn : qnTy ≠ lRn := by decide
@[simp] theorem qn_lRn_ne_qnTy : lRn ≠ qnTy := by decide
@[simp] theorem qn_qnTy_ne_lDir : qnTy ≠ lDir := by decide
@[simp] theorem qn_lDir_ne_qnTy : lDir ≠ qnTy := by decide
@[simp] theorem qn_qnTy_ne_lFle : qnTy ≠ lFle := by decide
@[simp] theorem qn_lFle_ne_qnTy : lFle ≠ qnTy := by decide
@[simp] theorem qn_qnTy_ne_lKb : qnTy ≠ lKb := by decide
@[simp] theorem qn_lKb_ne_qnTy : lKb ≠ qnTy := by decide
@[simp] theorem qn_qnB_ne_qnP : qnB ≠ qnP := by decide
@[simp] theorem qn_qnB_ne_qnT : qnB ≠ qnT := by decide
@[simp] theorem qn_qnB_ne_qnK : qnB ≠ qnK := by decide
@[simp] theorem qn_qnB_ne_qnF : qnB ≠ qnF := by decide
@[simp] theorem qn_qnB_ne_qnS : qnB ≠ qnS := by decide
@[simp] theorem qn_qnB_ne_qnTy : qnB ≠ qnTy := by decide
@[simp] theorem qn_qnB_ne_qnL : qnB ≠ qnL := by decide
@[simp] theorem qn_qnB_ne_qnO : qnB ≠ qnO := by decide
@[simp] theorem qn_qnB_ne_qnDk : qnB ≠ qnDk := by decide
@[simp] theorem qn_qnB_ne_qnA : qnB ≠ qnA := by decide
@[simp] theorem qn_qnB_ne_qnH : qnB ≠ qnH := by decide
@[simp] theorem qn_qnB_ne_qnV : qnB ≠ qnV := by decide
@[simp] theorem qn_qnB_ne_qnF2 : qnB ≠ qnF2 := by decide
@[simp] theorem qn_qnB_ne_qnS2 : qnB ≠ qnS2 := by decide
@[simp] theorem qn_qnB_ne_qnR : qnB ≠ qnR := by decide
@[simp] theorem qn_qnB_ne_kFu : qnB ≠ kFu := by decide
@[simp] theorem qn_kFu_ne_qnB : kFu ≠ qnB := by decide
@[simp] theorem qn_qnB_ne_kD : qnB ≠ kD := by decide
@[simp] theorem qn_kD_ne_qnB : kD ≠ qnB := by decide
@[simp] theorem qn_qnB_ne_ibT1 : qnB ≠ ibT1 := by decide
@[simp] theorem qn_ibT1_ne_qnB : ibT1 ≠ qnB := by decide
@[simp] theorem qn_qnB_ne_ibT2 : qnB ≠ ibT2 := by decide
@[simp] theorem qn_ibT2_ne_qnB : ibT2 ≠ qnB := by decide
@[simp] theorem qn_qnB_ne_lFl : qnB ≠ lFl := by decide
@[simp] theorem qn_lFl_ne_qnB : lFl ≠ qnB := by decide
@[simp] theorem qn_qnB_ne_lDh : qnB ≠ lDh := by decide
@[simp] theorem qn_lDh_ne_qnB : lDh ≠ qnB := by decide
@[simp] theorem qn_qnB_ne_lDt : qnB ≠ lDt := by decide
@[simp] theorem qn_lDt_ne_qnB : lDt ≠ qnB := by decide
@[simp] theorem qn_qnB_ne_lDg : qnB ≠ lDg := by decide
@[simp] theorem qn_lDg_ne_qnB : lDg ≠ qnB := by decide
@[simp] theorem qn_qnB_ne_lDi : qnB ≠ lDi := by decide
@[simp] theorem qn_lDi_ne_qnB : lDi ≠ qnB := by decide
@[simp] theorem qn_qnB_ne_lRp : qnB ≠ lRp := by decide
@[simp] theorem qn_lRp_ne_qnB : lRp ≠ qnB := by decide
@[simp] theorem qn_qnB_ne_lRn : qnB ≠ lRn := by decide
@[simp] theorem qn_lRn_ne_qnB : lRn ≠ qnB := by decide
@[simp] theorem qn_qnB_ne_lDir : qnB ≠ lDir := by decide
@[simp] theorem qn_lDir_ne_qnB : lDir ≠ qnB := by decide
@[simp] theorem qn_qnB_ne_lFle : qnB ≠ lFle := by decide
@[simp] theorem qn_lFle_ne_qnB : lFle ≠ qnB := by decide
@[simp] theorem qn_qnB_ne_lKb : qnB ≠ lKb := by decide
@[simp] theorem qn_lKb_ne_qnB : lKb ≠ qnB := by decide
@[simp] theorem qn_qnL_ne_qnP : qnL ≠ qnP := by decide
@[simp] theorem qn_qnL_ne_qnT : qnL ≠ qnT := by decide
@[simp] theorem qn_qnL_ne_qnK : qnL ≠ qnK := by decide
@[simp] theorem qn_qnL_ne_qnF : qnL ≠ qnF := by decide
@[simp] theorem qn_qnL_ne_qnS : qnL ≠ qnS := by decide
@[simp] theorem qn_qnL_ne_qnTy : qnL ≠ qnTy := by decide
@[simp] theorem qn_qnL_ne_qnB : qnL ≠ qnB := by decide
@[simp] theorem qn_qnL_ne_qnO : qnL ≠ qnO := by decide
@[simp] theorem qn_qnL_ne_qnDk : qnL ≠ qnDk := by decide
@[simp] theorem qn_qnL_ne_qnA : qnL ≠ qnA := by decide
@[simp] theorem qn_qnL_ne_qnH : qnL ≠ qnH := by decide
@[simp] theorem qn_qnL_ne_qnV : qnL ≠ qnV := by decide
@[simp] theorem qn_qnL_ne_qnF2 : qnL ≠ qnF2 := by decide
@[simp] theorem qn_qnL_ne_qnS2 : qnL ≠ qnS2 := by decide
@[simp] theorem qn_qnL_ne_qnR : qnL ≠ qnR := by decide
@[simp] theorem qn_qnL_ne_kFu : qnL ≠ kFu := by decide
@[simp] theorem qn_kFu_ne_qnL : kFu ≠ qnL := by decide
@[simp] theorem qn_qnL_ne_kD : qnL ≠ kD := by decide
@[simp] theorem qn_kD_ne_qnL : kD ≠ qnL := by decide
@[simp] theorem qn_qnL_ne_ibT1 : qnL ≠ ibT1 := by decide
@[simp] theorem qn_ibT1_ne_qnL : ibT1 ≠ qnL := by decide
@[simp] theorem qn_qnL_ne_ibT2 : qnL ≠ ibT2 := by decide
@[simp] theorem qn_ibT2_ne_qnL : ibT2 ≠ qnL := by decide
@[simp] theorem qn_qnL_ne_lFl : qnL ≠ lFl := by decide
@[simp] theorem qn_lFl_ne_qnL : lFl ≠ qnL := by decide
@[simp] theorem qn_qnL_ne_lDh : qnL ≠ lDh := by decide
@[simp] theorem qn_lDh_ne_qnL : lDh ≠ qnL := by decide
@[simp] theorem qn_qnL_ne_lDt : qnL ≠ lDt := by decide
@[simp] theorem qn_lDt_ne_qnL : lDt ≠ qnL := by decide
@[simp] theorem qn_qnL_ne_lDg : qnL ≠ lDg := by decide
@[simp] theorem qn_lDg_ne_qnL : lDg ≠ qnL := by decide
@[simp] theorem qn_qnL_ne_lDi : qnL ≠ lDi := by decide
@[simp] theorem qn_lDi_ne_qnL : lDi ≠ qnL := by decide
@[simp] theorem qn_qnL_ne_lRp : qnL ≠ lRp := by decide
@[simp] theorem qn_lRp_ne_qnL : lRp ≠ qnL := by decide
@[simp] theorem qn_qnL_ne_lRn : qnL ≠ lRn := by decide
@[simp] theorem qn_lRn_ne_qnL : lRn ≠ qnL := by decide
@[simp] theorem qn_qnL_ne_lDir : qnL ≠ lDir := by decide
@[simp] theorem qn_lDir_ne_qnL : lDir ≠ qnL := by decide
@[simp] theorem qn_qnL_ne_lFle : qnL ≠ lFle := by decide
@[simp] theorem qn_lFle_ne_qnL : lFle ≠ qnL := by decide
@[simp] theorem qn_qnL_ne_lKb : qnL ≠ lKb := by decide
@[simp] theorem qn_lKb_ne_qnL : lKb ≠ qnL := by decide
@[simp] theorem qn_qnO_ne_qnP : qnO ≠ qnP := by decide
@[simp] theorem qn_qnO_ne_qnT : qnO ≠ qnT := by decide
@[simp] theorem qn_qnO_ne_qnK : qnO ≠ qnK := by decide
@[simp] theorem qn_qnO_ne_qnF : qnO ≠ qnF := by decide
@[simp] theorem qn_qnO_ne_qnS : qnO ≠ qnS := by decide
@[simp] theorem qn_qnO_ne_qnTy : qnO ≠ qnTy := by decide
@[simp] theorem qn_qnO_ne_qnB : qnO ≠ qnB := by decide
@[simp] theorem qn_qnO_ne_qnL : qnO ≠ qnL := by decide
@[simp] theorem qn_qnO_ne_qnDk : qnO ≠ qnDk := by decide
@[simp] theorem qn_qnO_ne_qnA : qnO ≠ qnA := by decide
@[simp] theorem qn_qnO_ne_qnH : qnO ≠ qnH := by decide
@[simp] theorem qn_qnO_ne_qnV : qnO ≠ qnV := by decide
@[simp] theorem qn_qnO_ne_qnF2 : qnO ≠ qnF2 := by decide
@[simp] theorem qn_qnO_ne_qnS2 : qnO ≠ qnS2 := by decide
@[simp] theorem qn_qnO_ne_qnR : qnO ≠ qnR := by decide
@[simp] theorem qn_qnO_ne_kFu : qnO ≠ kFu := by decide
@[simp] theorem qn_kFu_ne_qnO : kFu ≠ qnO := by decide
@[simp] theorem qn_qnO_ne_kD : qnO ≠ kD := by decide
@[simp] theorem qn_kD_ne_qnO : kD ≠ qnO := by decide
@[simp] theorem qn_qnO_ne_ibT1 : qnO ≠ ibT1 := by decide
@[simp] theorem qn_ibT1_ne_qnO : ibT1 ≠ qnO := by decide
@[simp] theorem qn_qnO_ne_ibT2 : qnO ≠ ibT2 := by decide
@[simp] theorem qn_ibT2_ne_qnO : ibT2 ≠ qnO := by decide
@[simp] theorem qn_qnO_ne_lFl : qnO ≠ lFl := by decide
@[simp] theorem qn_lFl_ne_qnO : lFl ≠ qnO := by decide
@[simp] theorem qn_qnO_ne_lDh : qnO ≠ lDh := by decide
@[simp] theorem qn_lDh_ne_qnO : lDh ≠ qnO := by decide
@[simp] theorem qn_qnO_ne_lDt : qnO ≠ lDt := by decide
@[simp] theorem qn_lDt_ne_qnO : lDt ≠ qnO := by decide
@[simp] theorem qn_qnO_ne_lDg : qnO ≠ lDg := by decide
@[simp] theorem qn_lDg_ne_qnO : lDg ≠ qnO := by decide
@[simp] theorem qn_qnO_ne_lDi : qnO ≠ lDi := by decide
@[simp] theorem qn_lDi_ne_qnO : lDi ≠ qnO := by decide
@[simp] theorem qn_qnO_ne_lRp : qnO ≠ lRp := by decide
@[simp] theorem qn_lRp_ne_qnO : lRp ≠ qnO := by decide
@[simp] theorem qn_qnO_ne_lRn : qnO ≠ lRn := by decide
@[simp] theorem qn_lRn_ne_qnO : lRn ≠ qnO := by decide
@[simp] theorem qn_qnO_ne_lDir : qnO ≠ lDir := by decide
@[simp] theorem qn_lDir_ne_qnO : lDir ≠ qnO := by decide
@[simp] theorem qn_qnO_ne_lFle : qnO ≠ lFle := by decide
@[simp] theorem qn_lFle_ne_qnO : lFle ≠ qnO := by decide
@[simp] theorem qn_qnO_ne_lKb : qnO ≠ lKb := by decide
@[simp] theorem qn_lKb_ne_qnO : lKb ≠ qnO := by decide
@[simp] theorem qn_qnDk_ne_qnP : qnDk ≠ qnP := by decide
@[simp] theorem qn_qnDk_ne_qnT : qnDk ≠ qnT := by decide
@[simp] theorem qn_qnDk_ne_qnK : qnDk ≠ qnK := by decide
@[simp] theorem qn_qnDk_ne_qnF : qnDk ≠ qnF := by decide
@[simp] theorem qn_qnDk_ne_qnS : qnDk ≠ qnS := by decide
@[simp] theorem qn_qnDk_ne_qnTy : qnDk ≠ qnTy := by decide
@[simp] theorem qn_qnDk_ne_qnB : qnDk ≠ qnB := by decide
@[simp] theorem qn_qnDk_ne_qnL : qnDk ≠ qnL := by decide
@[simp] theorem qn_qnDk_ne_qnO : qnDk ≠ qnO := by decide
@[simp] theorem qn_qnDk_ne_qnA : qnDk ≠ qnA := by decide
@[simp] theorem qn_qnDk_ne_qnH : qnDk ≠ qnH := by decide
@[simp] theorem qn_qnDk_ne_qnV : qnDk ≠ qnV := by decide
@[simp] theorem qn_qnDk_ne_qnF2 : qnDk ≠ qnF2 := by decide
@[simp] theorem qn_qnDk_ne_qnS2 : qnDk ≠ qnS2 := by decide
@[simp] theorem qn_qnDk_ne_qnR : qnDk ≠ qnR := by decide
@[simp] theorem qn_qnDk_ne_kFu : qnDk ≠ kFu := by decide
@[simp] theorem qn_kFu_ne_qnDk : kFu ≠ qnDk := by decide
@[simp] theorem qn_qnDk_ne_kD : qnDk ≠ kD := by decide
@[simp] theorem qn_kD_ne_qnDk : kD ≠ qnDk := by decide
@[simp] theorem qn_qnDk_ne_ibT1 : qnDk ≠ ibT1 := by decide
@[simp] theorem qn_ibT1_ne_qnDk : ibT1 ≠ qnDk := by decide
@[simp] theorem qn_qnDk_ne_ibT2 : qnDk ≠ ibT2 := by decide
@[simp] theorem qn_ibT2_ne_qnDk : ibT2 ≠ qnDk := by decide
@[simp] theorem qn_qnDk_ne_lFl : qnDk ≠ lFl := by decide
@[simp] theorem qn_lFl_ne_qnDk : lFl ≠ qnDk := by decide
@[simp] theorem qn_qnDk_ne_lDh : qnDk ≠ lDh := by decide
@[simp] theorem qn_lDh_ne_qnDk : lDh ≠ qnDk := by decide
@[simp] theorem qn_qnDk_ne_lDt : qnDk ≠ lDt := by decide
@[simp] theorem qn_lDt_ne_qnDk : lDt ≠ qnDk := by decide
@[simp] theorem qn_qnDk_ne_lDg : qnDk ≠ lDg := by decide
@[simp] theorem qn_lDg_ne_qnDk : lDg ≠ qnDk := by decide
@[simp] theorem qn_qnDk_ne_lDi : qnDk ≠ lDi := by decide
@[simp] theorem qn_lDi_ne_qnDk : lDi ≠ qnDk := by decide
@[simp] theorem qn_qnDk_ne_lRp : qnDk ≠ lRp := by decide
@[simp] theorem qn_lRp_ne_qnDk : lRp ≠ qnDk := by decide
@[simp] theorem qn_qnDk_ne_lRn : qnDk ≠ lRn := by decide
@[simp] theorem qn_lRn_ne_qnDk : lRn ≠ qnDk := by decide
@[simp] theorem qn_qnDk_ne_lDir : qnDk ≠ lDir := by decide
@[simp] theorem qn_lDir_ne_qnDk : lDir ≠ qnDk := by decide
@[simp] theorem qn_qnDk_ne_lFle : qnDk ≠ lFle := by decide
@[simp] theorem qn_lFle_ne_qnDk : lFle ≠ qnDk := by decide
@[simp] theorem qn_qnDk_ne_lKb : qnDk ≠ lKb := by decide
@[simp] theorem qn_lKb_ne_qnDk : lKb ≠ qnDk := by decide
@[simp] theorem qn_qnA_ne_qnP : qnA ≠ qnP := by decide
@[simp] theorem qn_qnA_ne_qnT : qnA ≠ qnT := by decide
@[simp] theorem qn_qnA_ne_qnK : qnA ≠ qnK := by decide
@[simp] theorem qn_qnA_ne_qnF : qnA ≠ qnF := by decide
@[simp] theorem qn_qnA_ne_qnS : qnA ≠ qnS := by decide
@[simp] theorem qn_qnA_ne_qnTy : qnA ≠ qnTy := by decide
@[simp] theorem qn_qnA_ne_qnB : qnA ≠ qnB := by decide
@[simp] theorem qn_qnA_ne_qnL : qnA ≠ qnL := by decide
@[simp] theorem qn_qnA_ne_qnO : qnA ≠ qnO := by decide
@[simp] theorem qn_qnA_ne_qnDk : qnA ≠ qnDk := by decide
@[simp] theorem qn_qnA_ne_qnH : qnA ≠ qnH := by decide
@[simp] theorem qn_qnA_ne_qnV : qnA ≠ qnV := by decide
@[simp] theorem qn_qnA_ne_qnF2 : qnA ≠ qnF2 := by decide
@[simp] theorem qn_qnA_ne_qnS2 : qnA ≠ qnS2 := by decide
@[simp] theorem qn_qnA_ne_qnR : qnA ≠ qnR := by decide
@[simp] theorem qn_qnA_ne_kFu : qnA ≠ kFu := by decide
@[simp] theorem qn_kFu_ne_qnA : kFu ≠ qnA := by decide
@[simp] theorem qn_qnA_ne_kD : qnA ≠ kD := by decide
@[simp] theorem qn_kD_ne_qnA : kD ≠ qnA := by decide
@[simp] theorem qn_qnA_ne_ibT1 : qnA ≠ ibT1 := by decide
@[simp] theorem qn_ibT1_ne_qnA : ibT1 ≠ qnA := by decide
@[simp] theorem qn_qnA_ne_ibT2 : qnA ≠ ibT2 := by decide
@[simp] theorem qn_ibT2_ne_qnA : ibT2 ≠ qnA := by decide
@[simp] theorem qn_qnA_ne_lFl : qnA ≠ lFl := by decide
@[simp] theorem qn_lFl_ne_qnA : lFl ≠ qnA := by decide
@[simp] theorem qn_qnA_ne_lDh : qnA ≠ lDh := by decide
@[simp] theorem qn_lDh_ne_qnA : lDh ≠ qnA := by decide
@[simp] theorem qn_qnA_ne_lDt : qnA ≠ lDt := by decide
@[simp] theorem qn_lDt_ne_qnA : lDt ≠ qnA := by decide
@[simp] theorem qn_qnA_ne_lDg : qnA ≠ lDg := by decide
@[simp] theorem qn_lDg_ne_qnA : lDg ≠ qnA := by decide
@[simp] theorem qn_qnA_ne_lDi : qnA ≠ lDi := by decide
@[simp] theorem qn_lDi_ne_qnA : lDi ≠ qnA := by decide
@[simp] theorem qn_qnA_ne_lRp : qnA ≠ lRp := by decide
@[simp] theorem qn_lRp_ne_qnA : lRp ≠ qnA := by decide
@[simp] theorem qn_qnA_ne_lRn : qnA ≠ lRn := by decide
@[simp] theorem qn_lRn_ne_qnA : lRn ≠ qnA := by decide
@[simp] theorem qn_qnA_ne_lDir : qnA ≠ lDir := by decide
@[simp] theorem qn_lDir_ne_qnA : lDir ≠ qnA := by decide
@[simp] theorem qn_qnA_ne_lFle : qnA ≠ lFle := by decide
@[simp] theorem qn_lFle_ne_qnA : lFle ≠ qnA := by decide
@[simp] theorem qn_qnA_ne_lKb : qnA ≠ lKb := by decide
@[simp] theorem qn_lKb_ne_qnA : lKb ≠ qnA := by decide
@[simp] theorem qn_qnH_ne_qnP : qnH ≠ qnP := by decide
@[simp] theorem qn_qnH_ne_qnT : qnH ≠ qnT := by decide
@[simp] theorem qn_qnH_ne_qnK : qnH ≠ qnK := by decide
@[simp] theorem qn_qnH_ne_qnF : qnH ≠ qnF := by decide
@[simp] theorem qn_qnH_ne_qnS : qnH ≠ qnS := by decide
@[simp] theorem qn_qnH_ne_qnTy : qnH ≠ qnTy := by decide
@[simp] theorem qn_qnH_ne_qnB : qnH ≠ qnB := by decide
@[simp] theorem qn_qnH_ne_qnL : qnH ≠ qnL := by decide
@[simp] theorem qn_qnH_ne_qnO : qnH ≠ qnO := by decide
@[simp] theorem qn_qnH_ne_qnDk : qnH ≠ qnDk := by decide
@[simp] theorem qn_qnH_ne_qnA : qnH ≠ qnA := by decide
@[simp] theorem qn_qnH_ne_qnV : qnH ≠ qnV := by decide
@[simp] theorem qn_qnH_ne_qnF2 : qnH ≠ qnF2 := by decide
@[simp] theorem qn_qnH_ne_qnS2 : qnH ≠ qnS2 := by decide
@[simp] theorem qn_qnH_ne_qnR : qnH ≠ qnR := by decide
@[simp] theorem qn_qnH_ne_kFu : qnH ≠ kFu := by decide
@[simp] theorem qn_kFu_ne_qnH : kFu ≠ qnH := by decide
@[simp] theorem qn_qnH_ne_kD : qnH ≠ kD := by decide
@[simp] theorem qn_kD_ne_qnH : kD ≠ qnH := by decide
@[simp] theorem qn_qnH_ne_ibT1 : qnH ≠ ibT1 := by decide
@[simp] theorem qn_ibT1_ne_qnH : ibT1 ≠ qnH := by decide
@[simp] theorem qn_qnH_ne_ibT2 : qnH ≠ ibT2 := by decide
@[simp] theorem qn_ibT2_ne_qnH : ibT2 ≠ qnH := by decide
@[simp] theorem qn_qnH_ne_lFl : qnH ≠ lFl := by decide
@[simp] theorem qn_lFl_ne_qnH : lFl ≠ qnH := by decide
@[simp] theorem qn_qnH_ne_lDh : qnH ≠ lDh := by decide
@[simp] theorem qn_lDh_ne_qnH : lDh ≠ qnH := by decide
@[simp] theorem qn_qnH_ne_lDt : qnH ≠ lDt := by decide
@[simp] theorem qn_lDt_ne_qnH : lDt ≠ qnH := by decide
@[simp] theorem qn_qnH_ne_lDg : qnH ≠ lDg := by decide
@[simp] theorem qn_lDg_ne_qnH : lDg ≠ qnH := by decide
@[simp] theorem qn_qnH_ne_lDi : qnH ≠ lDi := by decide
@[simp] theorem qn_lDi_ne_qnH : lDi ≠ qnH := by decide
@[simp] theorem qn_qnH_ne_lRp : qnH ≠ lRp := by decide
@[simp] theorem qn_lRp_ne_qnH : lRp ≠ qnH := by decide
@[simp] theorem qn_qnH_ne_lRn : qnH ≠ lRn := by decide
@[simp] theorem qn_lRn_ne_qnH : lRn ≠ qnH := by decide
@[simp] theorem qn_qnH_ne_lDir : qnH ≠ lDir := by decide
@[simp] theorem qn_lDir_ne_qnH : lDir ≠ qnH := by decide
@[simp] theorem qn_qnH_ne_lFle : qnH ≠ lFle := by decide
@[simp] theorem qn_lFle_ne_qnH : lFle ≠ qnH := by decide
@[simp] theorem qn_qnH_ne_lKb : qnH ≠ lKb := by decide
@[simp] theorem qn_lKb_ne_qnH : lKb ≠ qnH := by decide
@[simp] theorem qn_qnV_ne_qnP : qnV ≠ qnP := by decide
@[simp] theorem qn_qnV_ne_qnT : qnV ≠ qnT := by decide
@[simp] theorem qn_qnV_ne_qnK : qnV ≠ qnK := by decide
@[simp] theorem qn_qnV_ne_qnF : qnV ≠ qnF := by decide
@[simp] theorem qn_qnV_ne_qnS : qnV ≠ qnS := by decide
@[simp] theorem qn_qnV_ne_qnTy : qnV ≠ qnTy := by decide
@[simp] theorem qn_qnV_ne_qnB : qnV ≠ qnB := by decide
@[simp] theorem qn_qnV_ne_qnL : qnV ≠ qnL := by decide
@[simp] theorem qn_qnV_ne_qnO : qnV ≠ qnO := by decide
@[simp] theorem qn_qnV_ne_qnDk : qnV ≠ qnDk := by decide
@[simp] theorem qn_qnV_ne_qnA : qnV ≠ qnA := by decide
@[simp] theorem qn_qnV_ne_qnH : qnV ≠ qnH := by decide
@[simp] theorem qn_qnV_ne_qnF2 : qnV ≠ qnF2 := by decide
@[simp] theorem qn_qnV_ne_qnS2 : qnV ≠ qnS2 := by decide
@[simp] theorem qn_qnV_ne_qnR : qnV ≠ qnR := by decide
@[simp] theorem qn_qnV_ne_kFu : qnV ≠ kFu := by decide
@[simp] theorem qn_kFu_ne_qnV : kFu ≠ qnV := by decide
@[simp] theorem qn_qnV_ne_kD : qnV ≠ kD := by decide
@[simp] theorem qn_kD_ne_qnV : kD ≠ qnV := by decide
@[simp] theorem qn_qnV_ne_ibT1 : qnV ≠ ibT1 := by decide
@[simp] theorem qn_ibT1_ne_qnV : ibT1 ≠ qnV := by decide
@[simp] theorem qn_qnV_ne_ibT2 : qnV ≠ ibT2 := by decide
@[simp] theorem qn_ibT2_ne_qnV : ibT2 ≠ qnV := by decide
@[simp] theorem qn_qnV_ne_lFl : qnV ≠ lFl := by decide
@[simp] theorem qn_lFl_ne_qnV : lFl ≠ qnV := by decide
@[simp] theorem qn_qnV_ne_lDh : qnV ≠ lDh := by decide
@[simp] theorem qn_lDh_ne_qnV : lDh ≠ qnV := by decide
@[simp] theorem qn_qnV_ne_lDt : qnV ≠ lDt := by decide
@[simp] theorem qn_lDt_ne_qnV : lDt ≠ qnV := by decide
@[simp] theorem qn_qnV_ne_lDg : qnV ≠ lDg := by decide
@[simp] theorem qn_lDg_ne_qnV : lDg ≠ qnV := by decide
@[simp] theorem qn_qnV_ne_lDi : qnV ≠ lDi := by decide
@[simp] theorem qn_lDi_ne_qnV : lDi ≠ qnV := by decide
@[simp] theorem qn_qnV_ne_lRp : qnV ≠ lRp := by decide
@[simp] theorem qn_lRp_ne_qnV : lRp ≠ qnV := by decide
@[simp] theorem qn_qnV_ne_lRn : qnV ≠ lRn := by decide
@[simp] theorem qn_lRn_ne_qnV : lRn ≠ qnV := by decide
@[simp] theorem qn_qnV_ne_lDir : qnV ≠ lDir := by decide
@[simp] theorem qn_lDir_ne_qnV : lDir ≠ qnV := by decide
@[simp] theorem qn_qnV_ne_lFle : qnV ≠ lFle := by decide
@[simp] theorem qn_lFle_ne_qnV : lFle ≠ qnV := by decide
@[simp] theorem qn_qnV_ne_lKb : qnV ≠ lKb := by decide
@[simp] theorem qn_lKb_ne_qnV : lKb ≠ qnV := by decide
@[simp] theorem qn_qnF2_ne_qnP : qnF2 ≠ qnP := by decide
@[simp] theorem qn_qnF2_ne_qnT : qnF2 ≠ qnT := by decide
@[simp] theorem qn_qnF2_ne_qnK : qnF2 ≠ qnK := by decide
@[simp] theorem qn_qnF2_ne_qnF : qnF2 ≠ qnF := by decide
@[simp] theorem qn_qnF2_ne_qnS : qnF2 ≠ qnS := by decide
@[simp] theorem qn_qnF2_ne_qnTy : qnF2 ≠ qnTy := by decide
@[simp] theorem qn_qnF2_ne_qnB : qnF2 ≠ qnB := by decide
@[simp] theorem qn_qnF2_ne_qnL : qnF2 ≠ qnL := by decide
@[simp] theorem qn_qnF2_ne_qnO : qnF2 ≠ qnO := by decide
@[simp] theorem qn_qnF2_ne_qnDk : qnF2 ≠ qnDk := by decide
@[simp] theorem qn_qnF2_ne_qnA : qnF2 ≠ qnA := by decide
@[simp] theorem qn_qnF2_ne_qnH : qnF2 ≠ qnH := by decide
@[simp] theorem qn_qnF2_ne_qnV : qnF2 ≠ qnV := by decide
@[simp] theorem qn_qnF2_ne_qnS2 : qnF2 ≠ qnS2 := by decide
@[simp] theorem qn_qnF2_ne_qnR : qnF2 ≠ qnR := by decide
@[simp] theorem qn_qnF2_ne_kFu : qnF2 ≠ kFu := by decide
@[simp] theorem qn_kFu_ne_qnF2 : kFu ≠ qnF2 := by decide
@[simp] theorem qn_qnF2_ne_kD : qnF2 ≠ kD := by decide
@[simp] theorem qn_kD_ne_qnF2 : kD ≠ qnF2 := by decide
@[simp] theorem qn_qnF2_ne_ibT1 : qnF2 ≠ ibT1 := by decide
@[simp] theorem qn_ibT1_ne_qnF2 : ibT1 ≠ qnF2 := by decide
@[simp] theorem qn_qnF2_ne_ibT2 : qnF2 ≠ ibT2 := by decide
@[simp] theorem qn_ibT2_ne_qnF2 : ibT2 ≠ qnF2 := by decide
@[simp] theorem qn_qnF2_ne_lFl : qnF2 ≠ lFl := by decide
@[simp] theorem qn_lFl_ne_qnF2 : lFl ≠ qnF2 := by decide
@[simp] theorem qn_qnF2_ne_lDh : qnF2 ≠ lDh := by decide
@[simp] theorem qn_lDh_ne_qnF2 : lDh ≠ qnF2 := by decide
@[simp] theorem qn_qnF2_ne_lDt : qnF2 ≠ lDt := by decide
@[simp] theorem qn_lDt_ne_qnF2 : lDt ≠ qnF2 := by decide
@[simp] theorem qn_qnF2_ne_lDg : qnF2 ≠ lDg := by decide
@[simp] theorem qn_lDg_ne_qnF2 : lDg ≠ qnF2 := by decide
@[simp] theorem qn_qnF2_ne_lDi : qnF2 ≠ lDi := by decide
@[simp] theorem qn_lDi_ne_qnF2 : lDi ≠ qnF2 := by decide
@[simp] theorem qn_qnF2_ne_lRp : qnF2 ≠ lRp := by decide
@[simp] theorem qn_lRp_ne_qnF2 : lRp ≠ qnF2 := by decide
@[simp] theorem qn_qnF2_ne_lRn : qnF2 ≠ lRn := by decide
@[simp] theorem qn_lRn_ne_qnF2 : lRn ≠ qnF2 := by decide
@[simp] theorem qn_qnF2_ne_lDir : qnF2 ≠ lDir := by decide
@[simp] theorem qn_lDir_ne_qnF2 : lDir ≠ qnF2 := by decide
@[simp] theorem qn_qnF2_ne_lFle : qnF2 ≠ lFle := by decide
@[simp] theorem qn_lFle_ne_qnF2 : lFle ≠ qnF2 := by decide
@[simp] theorem qn_qnF2_ne_lKb : qnF2 ≠ lKb := by decide
@[simp] theorem qn_lKb_ne_qnF2 : lKb ≠ qnF2 := by decide
@[simp] theorem qn_qnS2_ne_qnP : qnS2 ≠ qnP := by decide
@[simp] theorem qn_qnS2_ne_qnT : qnS2 ≠ qnT := by decide
@[simp] theorem qn_qnS2_ne_qnK : qnS2 ≠ qnK := by decide
@[simp] theorem qn_qnS2_ne_qnF : qnS2 ≠ qnF := by decide
@[simp] theorem qn_qnS2_ne_qnS : qnS2 ≠ qnS := by decide
@[simp] theorem qn_qnS2_ne_qnTy : qnS2 ≠ qnTy := by decide
@[simp] theorem qn_qnS2_ne_qnB : qnS2 ≠ qnB := by decide
@[simp] theorem qn_qnS2_ne_qnL : qnS2 ≠ qnL := by decide
@[simp] theorem qn_qnS2_ne_qnO : qnS2 ≠ qnO := by decide
@[simp] theorem qn_qnS2_ne_qnDk : qnS2 ≠ qnDk := by decide
@[simp] theorem qn_qnS2_ne_qnA : qnS2 ≠ qnA := by decide
@[simp] theorem qn_qnS2_ne_qnH : qnS2 ≠ qnH := by decide
@[simp] theorem qn_qnS2_ne_qnV : qnS2 ≠ qnV := by decide
@[simp] theorem qn_qnS2_ne_qnF2 : qnS2 ≠ qnF2 := by decide
@[simp] theorem qn_qnS2_ne_qnR : qnS2 ≠ qnR := by decide
@[simp] theorem qn_qnS2_ne_kFu : qnS2 ≠ kFu := by decide
@[simp] theorem qn_kFu_ne_qnS2 : kFu ≠ qnS2 := by decide
@[simp] theorem qn_qnS2_ne_kD : qnS2 ≠ kD := by decide
@[simp] theorem qn_kD_ne_qnS2 : kD ≠ qnS2 := by decide
@[simp] theorem qn_qnS2_ne_ibT1 : qnS2 ≠ ibT1 := by decide
@[simp] theorem qn_ibT1_ne_qnS2 : ibT1 ≠ qnS2 := by decide
@[simp] theorem qn_qnS2_ne_ibT2 : qnS2 ≠ ibT2 := by decide
@[simp] theorem qn_ibT2_ne_qnS2 : ibT2 ≠ qnS2 := by decide
@[simp] theorem qn_qnS2_ne_lFl : qnS2 ≠ lFl := by decide
@[simp] theorem qn_lFl_ne_qnS2 : lFl ≠ qnS2 := by decide
@[simp] theorem qn_qnS2_ne_lDh : qnS2 ≠ lDh := by decide
@[simp] theorem qn_lDh_ne_qnS2 : lDh ≠ qnS2 := by decide
@[simp] theorem qn_qnS2_ne_lDt : qnS2 ≠ lDt := by decide
@[simp] theorem qn_lDt_ne_qnS2 : lDt ≠ qnS2 := by decide
@[simp] theorem qn_qnS2_ne_lDg : qnS2 ≠ lDg := by decide
@[simp] theorem qn_lDg_ne_qnS2 : lDg ≠ qnS2 := by decide
@[simp] theorem qn_qnS2_ne_lDi : qnS2 ≠ lDi := by decide
@[simp] theorem qn_lDi_ne_qnS2 : lDi ≠ qnS2 := by decide
@[simp] theorem qn_qnS2_ne_lRp : qnS2 ≠ lRp := by decide
@[simp] theorem qn_lRp_ne_qnS2 : lRp ≠ qnS2 := by decide
@[simp] theorem qn_qnS2_ne_lRn : qnS2 ≠ lRn := by decide
@[simp] theorem qn_lRn_ne_qnS2 : lRn ≠ qnS2 := by decide
@[simp] theorem qn_qnS2_ne_lDir : qnS2 ≠ lDir := by decide
@[simp] theorem qn_lDir_ne_qnS2 : lDir ≠ qnS2 := by decide
@[simp] theorem qn_qnS2_ne_lFle : qnS2 ≠ lFle := by decide
@[simp] theorem qn_lFle_ne_qnS2 : lFle ≠ qnS2 := by decide
@[simp] theorem qn_qnS2_ne_lKb : qnS2 ≠ lKb := by decide
@[simp] theorem qn_lKb_ne_qnS2 : lKb ≠ qnS2 := by decide
@[simp] theorem qn_qnR_ne_qnP : qnR ≠ qnP := by decide
@[simp] theorem qn_qnR_ne_qnT : qnR ≠ qnT := by decide
@[simp] theorem qn_qnR_ne_qnK : qnR ≠ qnK := by decide
@[simp] theorem qn_qnR_ne_qnF : qnR ≠ qnF := by decide
@[simp] theorem qn_qnR_ne_qnS : qnR ≠ qnS := by decide
@[simp] theorem qn_qnR_ne_qnTy : qnR ≠ qnTy := by decide
@[simp] theorem qn_qnR_ne_qnB : qnR ≠ qnB := by decide
@[simp] theorem qn_qnR_ne_qnL : qnR ≠ qnL := by decide
@[simp] theorem qn_qnR_ne_qnO : qnR ≠ qnO := by decide
@[simp] theorem qn_qnR_ne_qnDk : qnR ≠ qnDk := by decide
@[simp] theorem qn_qnR_ne_qnA : qnR ≠ qnA := by decide
@[simp] theorem qn_qnR_ne_qnH : qnR ≠ qnH := by decide
@[simp] theorem qn_qnR_ne_qnV : qnR ≠ qnV := by decide
@[simp] theorem qn_qnR_ne_qnF2 : qnR ≠ qnF2 := by decide
@[simp] theorem qn_qnR_ne_qnS2 : qnR ≠ qnS2 := by decide
@[simp] theorem qn_qnR_ne_kFu : qnR ≠ kFu := by decide
@[simp] theorem qn_kFu_ne_qnR : kFu ≠ qnR := by decide
@[simp] theorem qn_qnR_ne_kD : qnR ≠ kD := by decide
@[simp] theorem qn_kD_ne_qnR : kD ≠ qnR := by decide
@[simp] theorem qn_qnR_ne_ibT1 : qnR ≠ ibT1 := by decide
@[simp] theorem qn_ibT1_ne_qnR : ibT1 ≠ qnR := by decide
@[simp] theorem qn_qnR_ne_ibT2 : qnR ≠ ibT2 := by decide
@[simp] theorem qn_ibT2_ne_qnR : ibT2 ≠ qnR := by decide
@[simp] theorem qn_qnR_ne_lFl : qnR ≠ lFl := by decide
@[simp] theorem qn_lFl_ne_qnR : lFl ≠ qnR := by decide
@[simp] theorem qn_qnR_ne_lDh : qnR ≠ lDh := by decide
@[simp] theorem qn_lDh_ne_qnR : lDh ≠ qnR := by decide
@[simp] theorem qn_qnR_ne_lDt : qnR ≠ lDt := by decide
@[simp] theorem qn_lDt_ne_qnR : lDt ≠ qnR := by decide
@[simp] theorem qn_qnR_ne_lDg : qnR ≠ lDg := by decide
@[simp] theorem qn_lDg_ne_qnR : lDg ≠ qnR := by decide
@[simp] theorem qn_qnR_ne_lDi : qnR ≠ lDi := by decide
@[simp] theorem qn_lDi_ne_qnR : lDi ≠ qnR := by decide
@[simp] theorem qn_qnR_ne_lRp : qnR ≠ lRp := by decide
@[simp] theorem qn_lRp_ne_qnR : lRp ≠ qnR := by decide
@[simp] theorem qn_qnR_ne_lRn : qnR ≠ lRn := by decide
@[simp] theorem qn_lRn_ne_qnR : lRn ≠ qnR := by decide
@[simp] theorem qn_qnR_ne_lDir : qnR ≠ lDir := by decide
@[simp] theorem qn_lDir_ne_qnR : lDir ≠ qnR := by decide
@[simp] theorem qn_qnR_ne_lFle : qnR ≠ lFle := by decide
@[simp] theorem qn_lFle_ne_qnR : lFle ≠ qnR := by decide
@[simp] theorem qn_qnR_ne_lKb : qnR ≠ lKb := by decide
@[simp] theorem qn_lKb_ne_qnR : lKb ≠ qnR := by decide
@[simp] theorem qn_qmA_ne_qmH : qmA ≠ qmH := by decide
@[simp] theorem qn_qmA_ne_qmV : qmA ≠ qmV := by decide
@[simp] theorem qn_qmA_ne_qmE : qmA ≠ qmE := by decide
@[simp] theorem qn_qmA_ne_qmF : qmA ≠ qmF := by decide
@[simp] theorem qn_qmA_ne_qmS : qmA ≠ qmS := by decide
@[simp] theorem qn_qmA_ne_qmR : qmA ≠ qmR := by decide
@[simp] theorem qn_qmA_ne_kFu : qmA ≠ kFu := by decide
@[simp] theorem qn_kFu_ne_qmA : kFu ≠ qmA := by decide
@[simp] theorem qn_qmA_ne_kD : qmA ≠ kD := by decide
@[simp] theorem qn_kD_ne_qmA : kD ≠ qmA := by decide
@[simp] theorem qn_qmA_ne_ibT1 : qmA ≠ ibT1 := by decide
@[simp] theorem qn_ibT1_ne_qmA : ibT1 ≠ qmA := by decide
@[simp] theorem qn_qmA_ne_ibT2 : qmA ≠ ibT2 := by decide
@[simp] theorem qn_ibT2_ne_qmA : ibT2 ≠ qmA := by decide
@[simp] theorem qn_qmA_ne_lFl : qmA ≠ lFl := by decide
@[simp] theorem qn_lFl_ne_qmA : lFl ≠ qmA := by decide
@[simp] theorem qn_qmA_ne_lDh : qmA ≠ lDh := by decide
@[simp] theorem qn_lDh_ne_qmA : lDh ≠ qmA := by decide
@[simp] theorem qn_qmA_ne_lDt : qmA ≠ lDt := by decide
@[simp] theorem qn_lDt_ne_qmA : lDt ≠ qmA := by decide
@[simp] theorem qn_qmA_ne_lDg : qmA ≠ lDg := by decide
@[simp] theorem qn_lDg_ne_qmA : lDg ≠ qmA := by decide
@[simp] theorem qn_qmA_ne_lDi : qmA ≠ lDi := by decide
@[simp] theorem qn_lDi_ne_qmA : lDi ≠ qmA := by decide
@[simp] theorem qn_qmA_ne_lRp : qmA ≠ lRp := by decide
@[simp] theorem qn_lRp_ne_qmA : lRp ≠ qmA := by decide
@[simp] theorem qn_qmA_ne_lRn : qmA ≠ lRn := by decide
@[simp] theorem qn_lRn_ne_qmA : lRn ≠ qmA := by decide
@[simp] theorem qn_qmA_ne_lDir : qmA ≠ lDir := by decide
@[simp] theorem qn_lDir_ne_qmA : lDir ≠ qmA := by decide
@[simp] theorem qn_qmA_ne_lFle : qmA ≠ lFle := by decide
@[simp] theorem qn_lFle_ne_qmA : lFle ≠ qmA := by decide
@[simp] theorem qn_qmA_ne_lKb : qmA ≠ lKb := by decide
@[simp] theorem qn_lKb_ne_qmA : lKb ≠ qmA := by decide
@[simp] theorem qn_qmH_ne_qmA : qmH ≠ qmA := by decide
@[simp] theorem qn_qmH_ne_qmV : qmH ≠ qmV := by decide
@[simp] theorem qn_qmH_ne_qmE : qmH ≠ qmE := by decide
@[simp] theorem qn_qmH_ne_qmF : qmH ≠ qmF := by decide
@[simp] theorem qn_qmH_ne_qmS : qmH ≠ qmS := by decide
@[simp] theorem qn_qmH_ne_qmR : qmH ≠ qmR := by decide
@[simp] theorem qn_qmH_ne_kFu : qmH ≠ kFu := by decide
@[simp] theorem qn_kFu_ne_qmH : kFu ≠ qmH := by decide
@[simp] theorem qn_qmH_ne_kD : qmH ≠ kD := by decide
@[simp] theorem qn_kD_ne_qmH : kD ≠ qmH := by decide
@[simp] theorem qn_qmH_ne_ibT1 : qmH ≠ ibT1 := by decide
@[simp] theorem qn_ibT1_ne_qmH : ibT1 ≠ qmH := by decide
@[simp] theorem qn_qmH_ne_ibT2 : qmH ≠ ibT2 := by decide
@[simp] theorem qn_ibT2_ne_qmH : ibT2 ≠ qmH := by decide
@[simp] theorem qn_qmH_ne_lFl : qmH ≠ lFl := by decide
@[simp] theorem qn_lFl_ne_qmH : lFl ≠ qmH := by decide
@[simp] theorem qn_qmH_ne_lDh : qmH ≠ lDh := by decide
@[simp] theorem qn_lDh_ne_qmH : lDh ≠ qmH := by decide
@[simp] theorem qn_qmH_ne_lDt : qmH ≠ lDt := by decide
@[simp] theorem qn_lDt_ne_qmH : lDt ≠ qmH := by decide
@[simp] theorem qn_qmH_ne_lDg : qmH ≠ lDg := by decide
@[simp] theorem qn_lDg_ne_qmH : lDg ≠ qmH := by decide
@[simp] theorem qn_qmH_ne_lDi : qmH ≠ lDi := by decide
@[simp] theorem qn_lDi_ne_qmH : lDi ≠ qmH := by decide
@[simp] theorem qn_qmH_ne_lRp : qmH ≠ lRp := by decide
@[simp] theorem qn_lRp_ne_qmH : lRp ≠ qmH := by decide
@[simp] theorem qn_qmH_ne_lRn : qmH ≠ lRn := by decide
@[simp] theorem qn_lRn_ne_qmH : lRn ≠ qmH := by decide
@[simp] theorem qn_qmH_ne_lDir : qmH ≠ lDir := by decide
@[simp] theorem qn_lDir_ne_qmH : lDir ≠ qmH := by decide
@[simp] theorem qn_qmH_ne_lFle : qmH ≠ lFle := by decide
@[simp] theorem qn_lFle_ne_qmH : lFle ≠ qmH := by decide
@[simp] theorem qn_qmH_ne_lKb : qmH ≠ lKb := by decide
@[simp] theorem qn_lKb_ne_qmH : lKb ≠ qmH := by decide
@[simp] theorem qn_qmV_ne_qmA : qmV ≠ qmA := by decide
@[simp] theorem qn_qmV_ne_qmH : qmV ≠ qmH := by decide
@[simp] theorem qn_qmV_ne_qmE : qmV ≠ qmE := by decide
@[simp] theorem qn_qmV_ne_qmF : qmV ≠ qmF := by decide
@[simp] theorem qn_qmV_ne_qmS : qmV ≠ qmS := by decide
@[simp] theorem qn_qmV_ne_qmR : qmV ≠ qmR := by decide
@[simp] theorem qn_qmV_ne_kFu : qmV ≠ kFu := by decide
@[simp] theorem qn_kFu_ne_qmV : kFu ≠ qmV := by decide
@[simp] theorem qn_qmV_ne_kD : qmV ≠ kD := by decide
@[simp] theorem qn_kD_ne_qmV : kD ≠ qmV := by decide
@[simp] theorem qn_qmV_ne_ibT1 : qmV ≠ ibT1 := by decide
@[simp] theorem qn_ibT1_ne_qmV : ibT1 ≠ qmV := by decide
@[simp] theorem qn_qmV_ne_ibT2 : qmV ≠ ibT2 := by decide
@[simp] theorem qn_ibT2_ne_qmV : ibT2 ≠ qmV := by decide
@[simp] theorem qn_qmV_ne_lFl : qmV ≠ lFl := by decide
@[simp] theorem qn_lFl_ne_qmV : lFl ≠ qmV := by decide
@[simp] theorem qn_qmV_ne_lDh : qmV ≠ lDh := by decide
@[simp] theorem qn_lDh_ne_qmV : lDh ≠ qmV := by decide
@[simp] theorem qn_qmV_ne_lDt : qmV ≠ lDt := by decide
@[simp] theorem qn_lDt_ne_qmV : lDt ≠ qmV := by decide
@[simp] theorem qn_qmV_ne_lDg : qmV ≠ lDg := by decide
@[simp] theorem qn_lDg_ne_qmV : lDg ≠ qmV := by decide
@[simp] theorem qn_qmV_ne_lDi : qmV ≠ lDi := by decide
@[simp] theorem qn_lDi_ne_qmV : lDi ≠ qmV := by decide
@[simp] theorem qn_qmV_ne_lRp : qmV ≠ lRp := by decide
@[simp] theorem qn_lRp_ne_qmV : lRp ≠ qmV := by decide
@[simp] theorem qn_qmV_ne_lRn : qmV ≠ lRn := by decide
@[simp] theorem qn_lRn_ne_qmV : lRn ≠ qmV := by decide
@[simp] theorem qn_qmV_ne_lDir : qmV ≠ lDir := by decide
@[simp] theorem qn_lDir_ne_qmV : lDir ≠ qmV := by decide
@[simp] theorem qn_qmV_ne_lFle : qmV ≠ lFle := by decide
@[simp] theorem qn_lFle_ne_qmV : lFle ≠ qmV := by decide
@[simp] theorem qn_qmV_ne_lKb : qmV ≠ lKb := by decide
@[simp] theorem qn_lKb_ne_qmV : lKb ≠ qmV := by decide
@[simp] theorem qn_qmE_ne_qmA : qmE ≠ qmA := by decide
@[simp] theorem qn_qmE_ne_qmH : qmE ≠ qmH := by decide
@[simp] theorem qn_qmE_ne_qmV : qmE ≠ qmV := by decide
@[simp] theorem qn_qmE_ne_qmF : qmE ≠ qmF := by decide
@[simp] theorem qn_qmE_ne_qmS : qmE ≠ qmS := by decide
@[simp] theorem qn_qmE_ne_qmR : qmE ≠ qmR := by decide
@[simp] theorem qn_qmE_ne_kFu : qmE ≠ kFu := by decide
@[simp] theorem qn_kFu_ne_qmE : kFu ≠ qmE := by decide
@[simp] theorem qn_qmE_ne_kD : qmE ≠ kD := by decide
@[simp] theorem qn_kD_ne_qmE : kD ≠ qmE := by decide
@[simp] theorem qn_qmE_ne_ibT1 : qmE ≠ ibT1 := by decide
@[simp] theorem qn_ibT1_ne_qmE : ibT1 ≠ qmE := by decide
@[simp] theorem qn_qmE_ne_ibT2 : qmE ≠ ibT2 := by decide
@[simp] theorem qn_ibT2_ne_qmE : ibT2 ≠ qmE := by decide
@[simp] theorem qn_qmE_ne_lFl : qmE ≠ lFl := by decide
@[simp] theorem qn_lFl_ne_qmE : lFl ≠ qmE := by decide
@[simp] theorem qn_qmE_ne_lDh : qmE ≠ lDh := by decide
@[simp] theorem qn_lDh_ne_qmE : lDh ≠ qmE := by decide
@[simp] theorem qn_qmE_ne_lDt : qmE ≠ lDt := by decide
@[simp] theorem qn_lDt_ne_qmE : lDt ≠ qmE := by decide
@[simp] theorem qn_qmE_ne_lDg : qmE ≠ lDg := by decide
@[simp] theorem qn_lDg_ne_qmE : lDg ≠ qmE := by decide
@[simp] theorem qn_qmE_ne_lDi : qmE ≠ lDi := by decide
@[simp] theorem qn_lDi_ne_qmE : lDi ≠ qmE := by decide
@[simp] theorem qn_qmE_ne_lRp : qmE ≠ lRp := by decide
@[simp] theorem qn_lRp_ne_qmE : lRp ≠ qmE := by decide
@[simp] theorem qn_qmE_ne_lRn : qmE ≠ lRn := by decide
@[simp] theorem qn_lRn_ne_qmE : lRn ≠ qmE := by decide
@[simp] theorem qn_qmE_ne_lDir : qmE ≠ lDir := by decide
@[simp] theorem qn_lDir_ne_qmE : lDir ≠ qmE := by decide
@[simp] theorem qn_qmE_ne_lFle : qmE ≠ lFle := by decide
@[simp] theorem qn_lFle_ne_qmE : lFle ≠ qmE := by decide
@[simp] theorem qn_qmE_ne_lKb : qmE ≠ lKb := by decide
@[simp] theorem qn_lKb_ne_qmE : lKb ≠ qmE := by decide
@[simp] theorem qn_qmF_ne_qmA : qmF ≠ qmA := by decide
@[simp] theorem qn_qmF_ne_qmH : qmF ≠ qmH := by decide
@[simp] theorem qn_qmF_ne_qmV : qmF ≠ qmV := by decide
@[simp] theorem qn_qmF_ne_qmE : qmF ≠ qmE := by decide
@[simp] theorem qn_qmF_ne_qmS : qmF ≠ qmS := by decide
@[simp] theorem qn_qmF_ne_qmR : qmF ≠ qmR := by decide
@[simp] theorem qn_qmF_ne_kFu : qmF ≠ kFu := by decide
@[simp] theorem qn_kFu_ne_qmF : kFu ≠ qmF := by decide
@[simp] theorem qn_qmF_ne_kD : qmF ≠ kD := by decide
@[simp] theorem qn_kD_ne_qmF : kD ≠ qmF := by decide
@[simp] theorem qn_qmF_ne_ibT1 : qmF ≠ ibT1 := by decide
@[simp] theorem qn_ibT1_ne_qmF : ibT1 ≠ qmF := by decide
@[simp] theorem qn_qmF_ne_ibT2 : qmF ≠ ibT2 := by decide
@[simp] theorem qn_ibT2_ne_qmF : ibT2 ≠ qmF := by decide
@[simp] theorem qn_qmF_ne_lFl : qmF ≠ lFl := by decide
@[simp] theorem qn_lFl_ne_qmF : lFl ≠ qmF := by decide
@[simp] theorem qn_qmF_ne_lDh : qmF ≠ lDh := by decide
@[simp] theorem qn_lDh_ne_qmF : lDh ≠ qmF := by decide
@[simp] theorem qn_qmF_ne_lDt : qmF ≠ lDt := by decide
@[simp] theorem qn_lDt_ne_qmF : lDt ≠ qmF := by decide
@[simp] theorem qn_qmF_ne_lDg : qmF ≠ lDg := by decide
@[simp] theorem qn_lDg_ne_qmF : lDg ≠ qmF := by decide
@[simp] theorem qn_qmF_ne_lDi : qmF ≠ lDi := by decide
@[simp] theorem qn_lDi_ne_qmF : lDi ≠ qmF := by decide
@[simp] theorem qn_qmF_ne_lRp : qmF ≠ lRp := by decide
@[simp] theorem qn_lRp_ne_qmF : lRp ≠ qmF := by decide
@[simp] theorem qn_qmF_ne_lRn : qmF ≠ lRn := by decide
@[simp] theorem qn_lRn_ne_qmF : lRn ≠ qmF := by decide
@[simp] theorem qn_qmF_ne_lDir : qmF ≠ lDir := by decide
@[simp] theorem qn_lDir_ne_qmF : lDir ≠ qmF := by decide
@[simp] theorem qn_qmF_ne_lFle : qmF ≠ lFle := by decide
@[simp] theorem qn_lFle_ne_qmF : lFle ≠ qmF := by decide
@[simp] theorem qn_qmF_ne_lKb : qmF ≠ lKb := by decide
@[simp] theorem qn_lKb_ne_qmF : lKb ≠ qmF := by decide
@[simp] theorem qn_qmS_ne_qmA : qmS ≠ qmA := by decide
@[simp] theorem qn_qmS_ne_qmH : qmS ≠ qmH := by decide
@[simp] theorem qn_qmS_ne_qmV : qmS ≠ qmV := by decide
@[simp] theorem qn_qmS_ne_qmE : qmS ≠ qmE := by decide
@[simp] theorem qn_qmS_ne_qmF : qmS ≠ qmF := by decide
@[simp] theorem qn_qmS_ne_qmR : qmS ≠ qmR := by decide
@[simp] theorem qn_qmS_ne_kFu : qmS ≠ kFu := by decide
@[simp] theorem qn_kFu_ne_qmS : kFu ≠ qmS := by decide
@[simp] theorem qn_qmS_ne_kD : qmS ≠ kD := by decide
@[simp] theorem qn_kD_ne_qmS : kD ≠ qmS := by decide
@[simp] theorem qn_qmS_ne_ibT1 : qmS ≠ ibT1 := by decide
@[simp] theorem qn_ibT1_ne_qmS : ibT1 ≠ qmS := by decide
@[simp] theorem qn_qmS_ne_ibT2 : qmS ≠ ibT2 := by decide
@[simp] theorem qn_ibT2_ne_qmS : ibT2 ≠ qmS := by decide
@[simp] theorem qn_qmS_ne_lFl : qmS ≠ lFl := by decide
@[simp] theorem qn_lFl_ne_qmS : lFl ≠ qmS := by decide
@[simp] theorem qn_qmS_ne_lDh : qmS ≠ lDh := by decide
@[simp] theorem qn_lDh_ne_qmS : lDh ≠ qmS := by decide
@[simp] theorem qn_qmS_ne_lDt : qmS ≠ lDt := by decide
@[simp] theorem qn_lDt_ne_qmS : lDt ≠ qmS := by decide
@[simp] theorem qn_qmS_ne_lDg : qmS ≠ lDg := by decide
@[simp] theorem qn_lDg_ne_qmS : lDg ≠ qmS := by decide
@[simp] theorem qn_qmS_ne_lDi : qmS ≠ lDi := by decide
@[simp] theorem qn_lDi_ne_qmS : lDi ≠ qmS := by decide
@[simp] theorem qn_qmS_ne_lRp : qmS ≠ lRp := by decide
@[simp] theorem qn_lRp_ne_qmS : lRp ≠ qmS := by decide
@[simp] theorem qn_qmS_ne_lRn : qmS ≠ lRn := by decide
@[simp] theorem qn_lRn_ne_qmS : lRn ≠ qmS := by decide
@[simp] theorem qn_qmS_ne_lDir : qmS ≠ lDir := by decide
@[simp] theorem qn_lDir_ne_qmS : lDir ≠ qmS := by decide
@[simp] theorem qn_qmS_ne_lFle : qmS ≠ lFle := by decide
@[simp] theorem qn_lFle_ne_qmS : lFle ≠ qmS := by decide
@[simp] theorem qn_qmS_ne_lKb : qmS ≠ lKb := by decide
@[simp] theorem qn_lKb_ne_qmS : lKb ≠ qmS := by decide
@[simp] theorem qn_qmR_ne_qmA : qmR ≠ qmA := by decide
@[simp] theorem qn_qmR_ne_qmH : qmR ≠ qmH := by decide
@[simp] theorem qn_qmR_ne_qmV : qmR ≠ qmV := by decide
@[simp] theorem qn_qmR_ne_qmE : qmR ≠ qmE := by decide
@[simp] theorem qn_qmR_ne_qmF : qmR ≠ qmF := by decide
@[simp] theorem qn_qmR_ne_qmS : qmR ≠ qmS := by decide
@[simp] theorem qn_qmR_ne_kFu : qmR ≠ kFu := by decide
@[simp] theorem qn_kFu_ne_qmR : kFu ≠ qmR := by decide
@[simp] theorem qn_qmR_ne_kD : qmR ≠ kD := by decide
@[simp] theorem qn_kD_ne_qmR : kD ≠ qmR := by decide
@[simp] theorem qn_qmR_ne_ibT1 : qmR ≠ ibT1 := by decide
@[simp] theorem qn_ibT1_ne_qmR : ibT1 ≠ qmR := by decide
@[simp] theorem qn_qmR_ne_ibT2 : qmR ≠ ibT2 := by decide
@[simp] theorem qn_ibT2_ne_qmR : ibT2 ≠ qmR := by decide
@[simp] theorem qn_qmR_ne_lFl : qmR ≠ lFl := by decide
@[simp] theorem qn_lFl_ne_qmR : lFl ≠ qmR := by decide
@[simp] theorem qn_qmR_ne_lDh : qmR ≠ lDh := by decide
@[simp] theorem qn_lDh_ne_qmR : lDh ≠ qmR := by decide
@[simp] theorem qn_qmR_ne_lDt : qmR ≠ lDt := by decide
@[simp] theorem qn_lDt_ne_qmR : lDt ≠ qmR := by decide
@[simp] theorem qn_qmR_ne_lDg : qmR ≠ lDg := by decide
@[simp] theorem qn_lDg_ne_qmR : lDg ≠ qmR := by decide
@[simp] theorem qn_qmR_ne_lDi : qmR ≠ lDi := by decide
@[simp] theorem qn_lDi_ne_qmR : lDi ≠ qmR := by decide
@[simp] theorem qn_qmR_ne_lRp : qmR ≠ lRp := by decide
@[simp] theorem qn_lRp_ne_qmR : lRp ≠ qmR := by decide
@[simp] theorem qn_qmR_ne_lRn : qmR ≠ lRn := by decide
@[simp] theorem qn_lRn_ne_qmR : lRn ≠ qmR := by decide
@[simp] theorem qn_qmR_ne_lDir : qmR ≠ lDir := by decide
@[simp] theorem qn_lDir_ne_qmR : lDir ≠ qmR := by decide
@[simp] theorem qn_qmR_ne_lFle : qmR ≠ lFle := by decide
@[simp] theorem qn_lFle_ne_qmR : lFle ≠ qmR := by decide
@[simp] theorem qn_qmR_ne_lKb : qmR ≠ lKb := by decide
@[simp] theorem qn_lKb_ne_qmR : lKb ≠ qmR := by decide

def qnParams : List MlS := [kFu, kD, qnP, qnT, qnK, qnF, qnS]
def qnLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, qnTy, qnB, qnL, qnO, qnDk, qnA, qnH, qnV, qnF2, qnS2,
  qnR]

def qnLeaf : ProgHOL 64 :=
  .seq (.call (some (some (.local, qnR), none)) fQe [vv kFu, vv kD, vv qnT, vv qnK, vv qnF, vv qnS]) (.return (vv qnR))

def qnCore : ProgHOL 64 :=
  .ite (.cmp .equal (vv qnP) (.const 0)) qnLeaf
  (.ite (tagIsE qnT 5)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv qnT)) (.seq eViewP
    (.seq (.assign .local qnTy (.load .one (vv lRp)))
    (.seq (.assign .local qnB (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.assign .local qnL (.load .one (vv qnF)))
    (.seq (.call (some (some (.local, qnO), none)) ExQ.fIrr
        [vv qnF, .const 0, vv qnL, .const (BitVec.ofNat 64 coreWalkFuel), vv qnTy, .const 0])
    (.seq (.assign .local qnDk (.op .add [vv kD, vv qnK]))
    (.seq (.call (some (some (.local, qnA), none)) fI [vv kFu, vv qnDk, vv qnO])
    (.seq (.call (some (some (.local, qnH), none)) fW [vv kFu, vv qnDk, vv qnA])
    (.ite (tagIsE qnH 2)
      (.seq (.call (some (some (.local, qnV), none)) fInternFVar [vv qnO, vv qnDk])
      (.seq (.call (some (some (.local, qnF2), none)) ExPre.fAppend [vv qnF, vv qnV])
      (.seq (.call (some (some (.local, qnS2), none)) ExPre.fAppend [vv qnS, vv qnO])
      (.seq (.call (some (some (.local, qnR), none)) fQn
          [vv kFu, vv kD, .op .sub [vv qnP, .const 1], vv qnB, .op .add [vv qnK, .const 1], vv qnF2, vv qnS2])
        (.return (vv qnR))))))
      hang)))))))))))
    qnLeaf)

def qnBody : ProgHOL 64 := prologue qnLocals qnCore

def qmLocals : List MlS := [qmA, qmH, qmV, qmE, qmF, qmS, qmR]

def qmCore (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .lower (vv kD) (.const (BitVec.ofNat 64 (2 ^ 62))))
  (.seq (.call (some (some (.local, qmA), none)) fI [vv kFu, vv kD, vv ibT1])
  (.seq (.call (some (some (.local, qmH), none)) fW [vv kFu, vv kD, vv qmA])
  (.ite (tagIsE qmH 2)
    (.seq (.call (some (some (.local, qmV), none)) fInternFVar [vv ibT1, vv kD])
    (allocP C qmE (.const 8) (.seq (.store (vv qmE) (.const 0))
    (.seq (.call (some (some (.local, qmF), none)) ExPre.fAppend [vv qmE, vv qmV])
    (.seq (.call (some (some (.local, qmS), none)) ExPre.fAppend [vv qmE, vv ibT1])
    (.seq (.call (some (some (.local, qmR), none)) fQn
        [vv kFu, vv kD, .const (BitVec.ofNat 64 peelFuel), vv ibT2, .const 1, vv qmF, vv qmS])
      (.return (vv qmR))))))))
    hang)))
  hang

def qmBody (C : Ctx) : ProgHOL 64 := prologue qmLocals (qmCore C)

section
variable {σ : Type}

theorem qn_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ qnLocals → (ctxEnv C ++ qnParams.zip vals).get x = none :=
  Knot.params_none C qnLocals qnParams vals (by decide) (by decide)

structure QnCodes (C : Ctx) : Prop where
  qe : QeCodes C
  qef : C.code.lookup fQe = some (qeParams.map (fun p => (p, ShapeHOL.one)), qeBody, .one)
  w : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one)
  fv : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one)
  app : C.code.lookup ExPre.fAppend = some (ExPre.appParams.map (fun p => (p, ShapeHOL.one)), ExPre.appBody C, .one)
  self : C.code.lookup fQn = some (qnParams.map (fun p => (p, ShapeHOL.one)), qnBody, .one)

theorem qn_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (hc : QnCodes C)
    (hI : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → d' < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (inferE C fIB) s1 ((knot mode C n).infer d' e')
      (PostK (ctxH C H)))
    (hW : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → d' < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d' e')
      (PostK (ctxH C H)))
    (d : Nat) :
    ∀ peel (t : EIdx) (k : Nat) (fvs stk : List EIdx) (ofv ost : Nat) (H : List (BitVec 64))
      (s : AState), C.H <+: H → BlkAt H ofv (fvs.map Enc.idxW) → BlkAt H ost (stk.map Enc.idxW) →
      fvs.length = k → stk.length = k → k + peel < 2 ^ 57 → d + k + peel < 2 ^ 63 →
      SpecR (σ := σ) (Pre (ctxH C H) s (qnParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, BitVec.ofNat 64 peel,
        Enc.idxW t, BitVec.ofNat 64 k, cellA C ofv, cellA C ost])) qnBody s
        (inferLams (knot mode C n) d peel t k fvs.toArray stk.toArray) (PostK (ctxH C H)) := by
  have leaf : ∀ (t : EIdx) (k : Nat) (fvs stk : List EIdx) (ofv ost : Nat) (H : List (BitVec 64))
      (s : AState) (Γ : Env) (M : Mem), C.H <+: H → BlkAt H ofv (fvs.map Enc.idxW) →
      BlkAt H ost (stk.map Enc.idxW) → fvs.length < 2 ^ 58 → stk.length < 2 ^ 58 → d + k < 2 ^ 63 →
      Γ.get kFu = some (BitVec.ofNat 64 n) → Γ.get kD = some (BitVec.ofNat 64 d) → Γ.get qnT = some (Enc.idxW t) →
      Γ.get qnK = some (BitVec.ofNat 64 k) → Γ.get qnF = some (cellA C ofv) → Γ.get qnS = some (cellA C ost) →
      SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ qnLocals)) qnLeaf s
        (inferLamsLeaf (knot mode C n) d t k fvs.toArray stk.toArray) (PostK (ctxH C H)) :=
    fun t k fvs stk ofv ost H s Γ M hp hbf hbs hfl hsl hdk h1 h2 h3 h4 h5 h6 =>
      specR_callKR qnR fQe qeParams [vv kFu, vv kD, vv qnT, vv qnK, vv qnF, vv qnS] qeBody
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW t, BitVec.ofNat 64 k, cellA C ofv, cellA C ost]
        (by decide) rfl (by decide) hc.qef
        ⟨by simp [h1], by simp [h2], by simp [h3], by simp [h4], by simp [h5], by simp [h6], trivial⟩
        (qe_spec ra mode n C hok hc.qe hI s d k t fvs stk ofv ost H hp hbf hbs hfl hsl hdk)
  intro peel
  induction peel with
  | zero =>
    intro t k fvs stk ofv ost H s hp hbf hbs hfl hsl hkp hdk
    refine specR_prologue (postK_locals _) (qn_none _ _) ?_
    unfold qnCore
    rw [inferLams]
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, qnParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact leaf t k fvs stk ofv ost H s _ _ hp hbf hbs (by omega) (by omega) (by omega)
      (by simp +decide [Env.get, qnParams, ctxEnv]) (by simp +decide [Env.get, qnParams, ctxEnv]) (by simp +decide [Env.get, qnParams, ctxEnv]) (by simp +decide [Env.get, qnParams, ctxEnv]) (by simp +decide [Env.get, qnParams, ctxEnv] <;> rfl) (by simp +decide [Env.get, qnParams, ctxEnv] <;> rfl)
  | succ peel ih =>
    intro t k fvs stk ofv ost H s hp hbf hbs hfl hsl hkp hdk
    refine specR_prologue (postK_locals _) (qn_none _ _) ?_
    unfold qnCore
    rw [inferLams]
    have hne := ofNat_succ_ne peel (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, qnParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine Knot.specR_tagIteV qnT t 5 (by decide) (by decide) (by simp +decide [Env.get, qnParams, ctxEnv]) (fun htg => ?_) (fun htg => ?_)
    swap
    · rw [if_pos (show (t.tag != ETag.lam) = true by simpa [ETag.lam] using htg)]
      exact leaf t k fvs stk ofv ost H s _ _ hp hbf hbs (by omega) (by omega) (by omega)
        (by simp +decide [Env.get, qnParams, ctxEnv]) (by simp +decide [Env.get, qnParams, ctxEnv]) (by simp +decide [Env.get, qnParams, ctxEnv]) (by simp +decide [Env.get, qnParams, ctxEnv]) (by simp +decide [Env.get, qnParams, ctxEnv] <;> rfl) (by simp +decide [Env.get, qnParams, ctxEnv] <;> rfl)
    rw [if_neg (show ¬ (t.tag != ETag.lam) = true by simp [htg, ETag.lam])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv qnT) (Enc.idxW t) (by decide) (by simp +decide [Env.get, qnParams, ctxEnv]) ?_
    refine specR_viewP (C := ctxH C H) t (by simp) (by simp +decide [Env.get] <;> rfl)
      (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
    have h5 : v.tagN = 5 := by rw [htn, htg]; rfl
    obtain ⟨ty, b, rfl⟩ : ∃ ty b, v = .lam ty b := by cases v <;> simp [ENodeView.tagN] at h5 ⊢
    have hvb : s.store.viewBind t = some (ty, b) := viewBind_of_view_lam (by rw [htg]; rfl) hv
    refine specR_runBind (by rw [viewBind_run, hvb]) ?_
    dsimp only
    refine specR_loadI' qnTy (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW ty) [Enc.idxW b] []) ?_
    refine specR_loadI' qnB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW b) [] []) ?_
    refine specR_dropM ?_
    obtain ⟨hlo, hlv0⟩ := blkAt_get0 hbf
    refine UD.specR_heapLoadI' (C := ctxH C H) qnL (vv qnF) ofv (BitVec.ofNat 64 fvs.length)
      (by show H[ofv]? = _; rw [List.getElem?_eq_getElem hlo, hlv0]; simp) (by decide) (by simp +decide [Env.get, qnParams, ctxEnv] <;> rfl) ?_
    simp only [instantiateListFast, List.size_toArray, bind_assoc]
    refine ILP.callE_spec (C := ctxH C H) qnO ExQ.fIrr ExQ.irrParams
      [vv qnF, .const 0, vv qnL, .const (BitVec.ofNat 64 coreWalkFuel), vv qnTy, .const 0] (ExQ.irrBody C)
      [cellA C ofv, BitVec.ofNat 64 0, BitVec.ofNat 64 fvs.length, BitVec.ofNat 64 coreWalkFuel, Enc.idxW ty,
        BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.qe.irr
      ⟨by simp +decide [Env.get, qnParams, ctxEnv] <;> rfl, rfl, by simp, rfl, by simp, rfl, trivial⟩
      (ExQ.irr_spec ra (ctxH C H) (ctxOK_H hok H) (codesQ_H hc.qe.q H) fvs.toArray ofv
        (show BlkAt H ofv (fvs.toArray.toList.map Enc.idxW) by simpa using hbf) (by simp; omega) s
        coreWalkFuel 0 fvs.length 0 ty CV.coreWalkFuel_lt (by decide) (by omega) (by decide)) (fun tyo s1 => ?_)
    refine specR_assignI qnDk _ (BitVec.ofNat 64 (d + k)) (by decide)
      (by simp +decide [sev, Env.get, qnParams, ctxEnv]; exact BitVec.ofNat_add_ofNat ..) ?_
    refine Big.specR_callKC (C := ctxH C H) qnA fI kParams [vv kFu, vv qnDk, vv qnO] (inferE C fIB)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 (d + k), Enc.idxW tyo] (by decide) rfl (by decide) hc.qe.i
      ⟨by simp +decide [Env.get, qnParams, ctxEnv], by simp, by simp, trivial⟩ (hI H s1 (d + k) tyo hp (by omega)) (fun tty s2 H2 hp2 _ => ?_)
    refine Big.specR_callKC (C := ctxH C H2) qnH fW kParams [vv kFu, vv qnDk, vv qnA] (whnfE C fWB)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 (d + k), Enc.idxW tty] (by decide) rfl (by decide) hc.w
      ⟨by simp +decide [Env.get, qnParams, ctxEnv], by simp, by simp, trivial⟩ (hW H2 s2 (d + k) tty (hp.trans hp2) (by omega)) (fun w s3 H3 hp3 _ => ?_)
    have hp13 : H <+: H3 := hp2.trans hp3
    refine Knot.specR_tagIteV qnH w 2 (by decide) (by decide) (by simp) (fun htg2 => ?_) (fun htg2 => ?_)
    · rw [if_pos (show (w.tag == ETag.sort) = true by simp [htg2, ETag.sort])]
      refine ILP.specR_internFVarI (C := ctxH C H3) ra (ctxOK_H hok H3) hc.fv qnV (vv qnO) (vv qnDk) tyo (d + k)
        (by omega) (by decide) (by simp) (by simp) (fun fv s4 => ?_)
      refine ExPre.specR_callApp (C := ctxH C H3) (ctxOK_H hok H3) hc.app qnF2 (vv qnF) (vv qnV) ofv
        (fvs.map Enc.idxW) (Enc.idxW fv) (by decide) (blkAt_mono hbf hp13) (by simp +decide [Env.get, qnParams, ctxEnv] <;> rfl) (by simp)
        (fun H4 o4 hp4 hb4 => ?_)
      refine ExPre.specR_callApp (C := ctxH C H4) (ctxOK_H hok H4) hc.app qnS2 (vv qnS) (vv qnO) ost
        (stk.map Enc.idxW) (Enc.idxW tyo) (by decide) (blkAt_mono hbs (hp13.trans hp4)) (by simp +decide [Env.get, qnParams, ctxEnv] <;> rfl) (by simp)
        (fun H5 o5 hp5 hb5 => ?_)
      have hb4' : BlkAt H5 o4 ((fvs ++ [fv]).map Enc.idxW) := by simpa using blkAt_mono hb4 hp5
      have hb5' : BlkAt H5 o5 ((stk ++ [tyo]).map Enc.idxW) := by simpa using hb5
      rw [show fvs.toArray.push fv = (fvs ++ [fv]).toArray by simp,
        show stk.toArray.push tyo = (stk ++ [tyo]).toArray by simp]
      refine specR_congr (m' := inferLams (knot mode C n) d peel b (k + 1) (fvs ++ [fv]).toArray
        (stk ++ [tyo]).toArray >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H5) qnR fQn qnParams
        [vv kFu, vv kD, .op .sub [vv qnP, .const 1], vv qnB, .op .add [vv qnK, .const 1], vv qnF2, vv qnS2] qnBody
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, BitVec.ofNat 64 peel, Enc.idxW b, BitVec.ofNat 64 (k + 1), cellA C o4,
          cellA C o5] (by decide) rfl (by decide) hc.self
        ⟨by simp +decide [Env.get, qnParams, ctxEnv], by simp +decide [Env.get, qnParams, ctxEnv], by simp +decide [sev, Env.get, qnParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _,
          by simp, by simp +decide [sev, Env.get, qnParams, ctxEnv]; exact word_add1_eq k, by simp <;> rfl,
          by simp <;> rfl, trivial⟩
        (PostK (ctxH C H5)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu qnParams _ rfl hlk)
          (ih b (k + 1) (fvs ++ [fv]) (stk ++ [tyo]) o4 o5 H5 s4 (hp.trans (hp13.trans (hp4.trans hp5))) hb4' hb5'
            (by simp; omega) (by simp; omega) (by omega) (by omega)))
        (fun r w s6 H6 hp6 hw => ?_)
      subst hw
      exact specR_returnI _ (Enc.idxW r) (by simp)
        (fun t ht => ⟨H6, hp13.trans (hp4.trans (hp5.trans hp6)), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · rw [if_neg (show ¬ (w.tag == ETag.sort) = true by simpa [ETag.sort] using htg2)]
      exact specR_hangI

theorem qm_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ qmLocals → (ctxEnv C ++ ifaParams.zip vals).get x = none :=
  Knot.params_none C qmLocals ifaParams vals (by decide) (by decide)

theorem qm_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (hc : QnCodes C)
    (hI : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → d' < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (inferE C fIB) s1 ((knot mode C n).infer d' e')
      (PostK (ctxH C H)))
    (hW : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → d' < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d' e')
      (PostK (ctxH C H)))
    (s : AState) (d : Nat) (hd : d < 2 ^ 63) (ty b : EIdx) :
    SpecR (σ := σ) (Pre C s (ifaParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty, Enc.idxW b]))
      (qmBody C) s (inferLam (knot mode C n) d ty b) (PostK C) := by
  refine specR_prologue (postK_locals C) (qm_none C _) ?_
  unfold qmCore
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
  unfold inferLam
  refine Big.specR_callKC (C := C) qmA fI kParams [vv kFu, vv kD, vv ibT1] (inferE C fIB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty] (by decide) rfl (by decide) hc.qe.i
    ⟨by simp +decide [Env.get, ifaParams, ctxEnv], by simp +decide [Env.get, ifaParams, ctxEnv], by simp +decide [Env.get, ifaParams, ctxEnv], trivial⟩ (hI C.H s d ty (List.prefix_refl _) (by omega)) (fun tty s2 H2 hp2 _ => ?_)
  refine Big.specR_callKC (C := ctxH C H2) qmH fW kParams [vv kFu, vv kD, vv qmA] (whnfE C fWB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW tty] (by decide) rfl (by decide) hc.w
    ⟨by simp +decide [Env.get, ifaParams, ctxEnv], by simp +decide [Env.get, ifaParams, ctxEnv], by simp, trivial⟩ (hW H2 s2 d tty hp2 (by omega)) (fun w s3 H3 hp3 _ => ?_)
  have hp13 : C.H <+: H3 := hp2.trans hp3
  refine Knot.specR_tagIteV qmH w 2 (by decide) (by decide) (by simp) (fun htg2 => ?_) (fun htg2 => ?_)
  · rw [if_pos (show (w.tag == ETag.sort) = true by simp [htg2, ETag.sort])]
    refine ILP.specR_internFVarI (C := ctxH C H3) ra (ctxOK_H hok H3) hc.fv qmV (vv ibT1) (vv kD) ty d
      (by omega) (by decide) (by simp +decide [Env.get, ifaParams, ctxEnv]) (by simp +decide [Env.get, ifaParams, ctxEnv]) (fun fv s4 => ?_)
    refine specR_emptyBlk (C0 := C) hok (H := H3) qmE (by decide) (fun H4 oe hp4 hbe => ?_)
    refine ExPre.specR_callApp (C := ctxH C H4) (ctxOK_H hok H4) hc.app qmF (vv qmE) (vv qmV) oe
      [] (Enc.idxW fv) (by decide) hbe (by simp <;> rfl) (by simp) (fun H5 o5 hp5 hb5 => ?_)
    refine ExPre.specR_callApp (C := ctxH C H5) (ctxOK_H hok H5) hc.app qmS (vv qmE) (vv ibT1) oe
      [] (Enc.idxW ty) (by decide) (blkAt_mono hbe hp5) (by simp <;> rfl) (by simp +decide [Env.get, ifaParams, ctxEnv]) (fun H6 o6 hp6 hb6 => ?_)
    have hb5' : BlkAt H6 o5 ([fv].map Enc.idxW) := by simpa using blkAt_mono hb5 hp6
    have hb6' : BlkAt H6 o6 ([ty].map Enc.idxW) := by simpa using hb6
    have hpall : C.H <+: H6 := hp13.trans (hp4.trans (hp5.trans hp6))
    refine specR_congr (m' := inferLams (knot mode C n) d peelFuel b 1 [fv].toArray [ty].toArray
      >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H6) qmR fQn qnParams
      [vv kFu, vv kD, .const (BitVec.ofNat 64 peelFuel), vv ibT2, .const 1, vv qmF, vv qmS] qnBody
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, BitVec.ofNat 64 peelFuel, Enc.idxW b, BitVec.ofNat 64 1, cellA C o5,
        cellA C o6] (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [Env.get, ifaParams, ctxEnv], by simp +decide [Env.get, ifaParams, ctxEnv], rfl, by simp +decide [Env.get, ifaParams, ctxEnv], rfl, by simp <;> rfl, by simp <;> rfl, trivial⟩
      (PostK (ctxH C H6)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu qnParams _ rfl hlk)
        (qn_spec ra mode n C hok hc hI hW d peelFuel b 1 [fv] [ty] o5 o6 H6 s4 hpall hb5' hb6' rfl rfl
          (by simp [peelFuel]) (by simp [peelFuel]; omega)))
      (fun r w s7 H7 hp7 hw => ?_)
    subst hw
    exact specR_returnI _ (Enc.idxW r) (by simp)
      (fun t ht => ⟨H7, hpall.trans hp7, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · rw [if_neg (show ¬ (w.tag == ETag.sort) = true by simpa [ETag.sort] using htg2)]
    exact specR_hangI

end

end ConPanqueque.T.WC
