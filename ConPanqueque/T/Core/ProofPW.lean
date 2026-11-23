import ConPanqueque.T.Core.HeadProofPW
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# PropRead's `proofPW` and its two fast arms

`proofPW` peels λ bodies, `let` bodies and application functions down to a head (`headProofPW`); `isProofFast` /
`notProofFast` read the datum: known and always-zero (an empty parameter block), or known and not.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc
open ConLeche (Level Name)

def pqF := ofString "ppq_pqf"
def pqE := ofString "ppq_pqe"
def pqB := ofString "ppq_pqb"
def pqS := ofString "ppq_pqs"
def ipfF := ofString "ppq_ipff"
def ipfE := ofString "ppq_ipfe"
def ipfW := ofString "ppq_ipfw"
def ipfL := ofString "ppq_ipfl"
def npfF := ofString "ppq_npff"
def npfE := ofString "ppq_npfe"
def npfW := ofString "ppq_npfw"
def npfL := ofString "ppq_npfl"
def fPq := ofString "proofPW"
def fIpf := ofString "isProofFast"
def fNpf := ofString "notProofFast"

@[simp] theorem ppq_pqF_ne_pqE : pqF ≠ pqE := by decide
@[simp] theorem ppq_pqF_ne_pqB : pqF ≠ pqB := by decide
@[simp] theorem ppq_pqF_ne_pqS : pqF ≠ pqS := by decide
@[simp] theorem ppq_pqF_ne_ipfF : pqF ≠ ipfF := by decide
@[simp] theorem ppq_pqF_ne_ipfE : pqF ≠ ipfE := by decide
@[simp] theorem ppq_pqF_ne_ipfW : pqF ≠ ipfW := by decide
@[simp] theorem ppq_pqF_ne_ipfL : pqF ≠ ipfL := by decide
@[simp] theorem ppq_pqF_ne_npfF : pqF ≠ npfF := by decide
@[simp] theorem ppq_pqF_ne_npfE : pqF ≠ npfE := by decide
@[simp] theorem ppq_pqF_ne_npfW : pqF ≠ npfW := by decide
@[simp] theorem ppq_pqF_ne_npfL : pqF ≠ npfL := by decide
@[simp] theorem ppq_pqF_ne_lFl : pqF ≠ lFl := by decide
@[simp] theorem ppq_lFl_ne_pqF : lFl ≠ pqF := by decide
@[simp] theorem ppq_pqF_ne_lDh : pqF ≠ lDh := by decide
@[simp] theorem ppq_lDh_ne_pqF : lDh ≠ pqF := by decide
@[simp] theorem ppq_pqF_ne_lDt : pqF ≠ lDt := by decide
@[simp] theorem ppq_lDt_ne_pqF : lDt ≠ pqF := by decide
@[simp] theorem ppq_pqF_ne_lDg : pqF ≠ lDg := by decide
@[simp] theorem ppq_lDg_ne_pqF : lDg ≠ pqF := by decide
@[simp] theorem ppq_pqF_ne_lDi : pqF ≠ lDi := by decide
@[simp] theorem ppq_lDi_ne_pqF : lDi ≠ pqF := by decide
@[simp] theorem ppq_pqF_ne_lRp : pqF ≠ lRp := by decide
@[simp] theorem ppq_lRp_ne_pqF : lRp ≠ pqF := by decide
@[simp] theorem ppq_pqF_ne_lRn : pqF ≠ lRn := by decide
@[simp] theorem ppq_lRn_ne_pqF : lRn ≠ pqF := by decide
@[simp] theorem ppq_pqF_ne_lFle : pqF ≠ lFle := by decide
@[simp] theorem ppq_lFle_ne_pqF : lFle ≠ pqF := by decide
@[simp] theorem ppq_pqF_ne_lKb : pqF ≠ lKb := by decide
@[simp] theorem ppq_lKb_ne_pqF : lKb ≠ pqF := by decide
@[simp] theorem ppq_pqF_ne_lDir : pqF ≠ lDir := by decide
@[simp] theorem ppq_lDir_ne_pqF : lDir ≠ pqF := by decide
@[simp] theorem ppq_pqF_ne_lFln : pqF ≠ lFln := by decide
@[simp] theorem ppq_lFln_ne_pqF : lFln ≠ pqF := by decide
@[simp] theorem ppq_pqF_ne_lFll : pqF ≠ lFll := by decide
@[simp] theorem ppq_lFll_ne_pqF : lFll ≠ pqF := by decide
@[simp] theorem ppq_pqF_ne_lFls : pqF ≠ lFls := by decide
@[simp] theorem ppq_lFls_ne_pqF : lFls ≠ pqF := by decide
@[simp] theorem ppq_pqF_ne_kFu : pqF ≠ kFu := by decide
@[simp] theorem ppq_kFu_ne_pqF : kFu ≠ pqF := by decide
@[simp] theorem ppq_pqF_ne_kD : pqF ≠ kD := by decide
@[simp] theorem ppq_kD_ne_pqF : kD ≠ pqF := by decide
@[simp] theorem ppq_pqE_ne_pqF : pqE ≠ pqF := by decide
@[simp] theorem ppq_pqE_ne_pqB : pqE ≠ pqB := by decide
@[simp] theorem ppq_pqE_ne_pqS : pqE ≠ pqS := by decide
@[simp] theorem ppq_pqE_ne_ipfF : pqE ≠ ipfF := by decide
@[simp] theorem ppq_pqE_ne_ipfE : pqE ≠ ipfE := by decide
@[simp] theorem ppq_pqE_ne_ipfW : pqE ≠ ipfW := by decide
@[simp] theorem ppq_pqE_ne_ipfL : pqE ≠ ipfL := by decide
@[simp] theorem ppq_pqE_ne_npfF : pqE ≠ npfF := by decide
@[simp] theorem ppq_pqE_ne_npfE : pqE ≠ npfE := by decide
@[simp] theorem ppq_pqE_ne_npfW : pqE ≠ npfW := by decide
@[simp] theorem ppq_pqE_ne_npfL : pqE ≠ npfL := by decide
@[simp] theorem ppq_pqE_ne_lFl : pqE ≠ lFl := by decide
@[simp] theorem ppq_lFl_ne_pqE : lFl ≠ pqE := by decide
@[simp] theorem ppq_pqE_ne_lDh : pqE ≠ lDh := by decide
@[simp] theorem ppq_lDh_ne_pqE : lDh ≠ pqE := by decide
@[simp] theorem ppq_pqE_ne_lDt : pqE ≠ lDt := by decide
@[simp] theorem ppq_lDt_ne_pqE : lDt ≠ pqE := by decide
@[simp] theorem ppq_pqE_ne_lDg : pqE ≠ lDg := by decide
@[simp] theorem ppq_lDg_ne_pqE : lDg ≠ pqE := by decide
@[simp] theorem ppq_pqE_ne_lDi : pqE ≠ lDi := by decide
@[simp] theorem ppq_lDi_ne_pqE : lDi ≠ pqE := by decide
@[simp] theorem ppq_pqE_ne_lRp : pqE ≠ lRp := by decide
@[simp] theorem ppq_lRp_ne_pqE : lRp ≠ pqE := by decide
@[simp] theorem ppq_pqE_ne_lRn : pqE ≠ lRn := by decide
@[simp] theorem ppq_lRn_ne_pqE : lRn ≠ pqE := by decide
@[simp] theorem ppq_pqE_ne_lFle : pqE ≠ lFle := by decide
@[simp] theorem ppq_lFle_ne_pqE : lFle ≠ pqE := by decide
@[simp] theorem ppq_pqE_ne_lKb : pqE ≠ lKb := by decide
@[simp] theorem ppq_lKb_ne_pqE : lKb ≠ pqE := by decide
@[simp] theorem ppq_pqE_ne_lDir : pqE ≠ lDir := by decide
@[simp] theorem ppq_lDir_ne_pqE : lDir ≠ pqE := by decide
@[simp] theorem ppq_pqE_ne_lFln : pqE ≠ lFln := by decide
@[simp] theorem ppq_lFln_ne_pqE : lFln ≠ pqE := by decide
@[simp] theorem ppq_pqE_ne_lFll : pqE ≠ lFll := by decide
@[simp] theorem ppq_lFll_ne_pqE : lFll ≠ pqE := by decide
@[simp] theorem ppq_pqE_ne_lFls : pqE ≠ lFls := by decide
@[simp] theorem ppq_lFls_ne_pqE : lFls ≠ pqE := by decide
@[simp] theorem ppq_pqE_ne_kFu : pqE ≠ kFu := by decide
@[simp] theorem ppq_kFu_ne_pqE : kFu ≠ pqE := by decide
@[simp] theorem ppq_pqE_ne_kD : pqE ≠ kD := by decide
@[simp] theorem ppq_kD_ne_pqE : kD ≠ pqE := by decide
@[simp] theorem ppq_pqB_ne_pqF : pqB ≠ pqF := by decide
@[simp] theorem ppq_pqB_ne_pqE : pqB ≠ pqE := by decide
@[simp] theorem ppq_pqB_ne_pqS : pqB ≠ pqS := by decide
@[simp] theorem ppq_pqB_ne_ipfF : pqB ≠ ipfF := by decide
@[simp] theorem ppq_pqB_ne_ipfE : pqB ≠ ipfE := by decide
@[simp] theorem ppq_pqB_ne_ipfW : pqB ≠ ipfW := by decide
@[simp] theorem ppq_pqB_ne_ipfL : pqB ≠ ipfL := by decide
@[simp] theorem ppq_pqB_ne_npfF : pqB ≠ npfF := by decide
@[simp] theorem ppq_pqB_ne_npfE : pqB ≠ npfE := by decide
@[simp] theorem ppq_pqB_ne_npfW : pqB ≠ npfW := by decide
@[simp] theorem ppq_pqB_ne_npfL : pqB ≠ npfL := by decide
@[simp] theorem ppq_pqB_ne_lFl : pqB ≠ lFl := by decide
@[simp] theorem ppq_lFl_ne_pqB : lFl ≠ pqB := by decide
@[simp] theorem ppq_pqB_ne_lDh : pqB ≠ lDh := by decide
@[simp] theorem ppq_lDh_ne_pqB : lDh ≠ pqB := by decide
@[simp] theorem ppq_pqB_ne_lDt : pqB ≠ lDt := by decide
@[simp] theorem ppq_lDt_ne_pqB : lDt ≠ pqB := by decide
@[simp] theorem ppq_pqB_ne_lDg : pqB ≠ lDg := by decide
@[simp] theorem ppq_lDg_ne_pqB : lDg ≠ pqB := by decide
@[simp] theorem ppq_pqB_ne_lDi : pqB ≠ lDi := by decide
@[simp] theorem ppq_lDi_ne_pqB : lDi ≠ pqB := by decide
@[simp] theorem ppq_pqB_ne_lRp : pqB ≠ lRp := by decide
@[simp] theorem ppq_lRp_ne_pqB : lRp ≠ pqB := by decide
@[simp] theorem ppq_pqB_ne_lRn : pqB ≠ lRn := by decide
@[simp] theorem ppq_lRn_ne_pqB : lRn ≠ pqB := by decide
@[simp] theorem ppq_pqB_ne_lFle : pqB ≠ lFle := by decide
@[simp] theorem ppq_lFle_ne_pqB : lFle ≠ pqB := by decide
@[simp] theorem ppq_pqB_ne_lKb : pqB ≠ lKb := by decide
@[simp] theorem ppq_lKb_ne_pqB : lKb ≠ pqB := by decide
@[simp] theorem ppq_pqB_ne_lDir : pqB ≠ lDir := by decide
@[simp] theorem ppq_lDir_ne_pqB : lDir ≠ pqB := by decide
@[simp] theorem ppq_pqB_ne_lFln : pqB ≠ lFln := by decide
@[simp] theorem ppq_lFln_ne_pqB : lFln ≠ pqB := by decide
@[simp] theorem ppq_pqB_ne_lFll : pqB ≠ lFll := by decide
@[simp] theorem ppq_lFll_ne_pqB : lFll ≠ pqB := by decide
@[simp] theorem ppq_pqB_ne_lFls : pqB ≠ lFls := by decide
@[simp] theorem ppq_lFls_ne_pqB : lFls ≠ pqB := by decide
@[simp] theorem ppq_pqB_ne_kFu : pqB ≠ kFu := by decide
@[simp] theorem ppq_kFu_ne_pqB : kFu ≠ pqB := by decide
@[simp] theorem ppq_pqB_ne_kD : pqB ≠ kD := by decide
@[simp] theorem ppq_kD_ne_pqB : kD ≠ pqB := by decide
@[simp] theorem ppq_pqS_ne_pqF : pqS ≠ pqF := by decide
@[simp] theorem ppq_pqS_ne_pqE : pqS ≠ pqE := by decide
@[simp] theorem ppq_pqS_ne_pqB : pqS ≠ pqB := by decide
@[simp] theorem ppq_pqS_ne_ipfF : pqS ≠ ipfF := by decide
@[simp] theorem ppq_pqS_ne_ipfE : pqS ≠ ipfE := by decide
@[simp] theorem ppq_pqS_ne_ipfW : pqS ≠ ipfW := by decide
@[simp] theorem ppq_pqS_ne_ipfL : pqS ≠ ipfL := by decide
@[simp] theorem ppq_pqS_ne_npfF : pqS ≠ npfF := by decide
@[simp] theorem ppq_pqS_ne_npfE : pqS ≠ npfE := by decide
@[simp] theorem ppq_pqS_ne_npfW : pqS ≠ npfW := by decide
@[simp] theorem ppq_pqS_ne_npfL : pqS ≠ npfL := by decide
@[simp] theorem ppq_pqS_ne_lFl : pqS ≠ lFl := by decide
@[simp] theorem ppq_lFl_ne_pqS : lFl ≠ pqS := by decide
@[simp] theorem ppq_pqS_ne_lDh : pqS ≠ lDh := by decide
@[simp] theorem ppq_lDh_ne_pqS : lDh ≠ pqS := by decide
@[simp] theorem ppq_pqS_ne_lDt : pqS ≠ lDt := by decide
@[simp] theorem ppq_lDt_ne_pqS : lDt ≠ pqS := by decide
@[simp] theorem ppq_pqS_ne_lDg : pqS ≠ lDg := by decide
@[simp] theorem ppq_lDg_ne_pqS : lDg ≠ pqS := by decide
@[simp] theorem ppq_pqS_ne_lDi : pqS ≠ lDi := by decide
@[simp] theorem ppq_lDi_ne_pqS : lDi ≠ pqS := by decide
@[simp] theorem ppq_pqS_ne_lRp : pqS ≠ lRp := by decide
@[simp] theorem ppq_lRp_ne_pqS : lRp ≠ pqS := by decide
@[simp] theorem ppq_pqS_ne_lRn : pqS ≠ lRn := by decide
@[simp] theorem ppq_lRn_ne_pqS : lRn ≠ pqS := by decide
@[simp] theorem ppq_pqS_ne_lFle : pqS ≠ lFle := by decide
@[simp] theorem ppq_lFle_ne_pqS : lFle ≠ pqS := by decide
@[simp] theorem ppq_pqS_ne_lKb : pqS ≠ lKb := by decide
@[simp] theorem ppq_lKb_ne_pqS : lKb ≠ pqS := by decide
@[simp] theorem ppq_pqS_ne_lDir : pqS ≠ lDir := by decide
@[simp] theorem ppq_lDir_ne_pqS : lDir ≠ pqS := by decide
@[simp] theorem ppq_pqS_ne_lFln : pqS ≠ lFln := by decide
@[simp] theorem ppq_lFln_ne_pqS : lFln ≠ pqS := by decide
@[simp] theorem ppq_pqS_ne_lFll : pqS ≠ lFll := by decide
@[simp] theorem ppq_lFll_ne_pqS : lFll ≠ pqS := by decide
@[simp] theorem ppq_pqS_ne_lFls : pqS ≠ lFls := by decide
@[simp] theorem ppq_lFls_ne_pqS : lFls ≠ pqS := by decide
@[simp] theorem ppq_pqS_ne_kFu : pqS ≠ kFu := by decide
@[simp] theorem ppq_kFu_ne_pqS : kFu ≠ pqS := by decide
@[simp] theorem ppq_pqS_ne_kD : pqS ≠ kD := by decide
@[simp] theorem ppq_kD_ne_pqS : kD ≠ pqS := by decide
@[simp] theorem ppq_ipfF_ne_pqF : ipfF ≠ pqF := by decide
@[simp] theorem ppq_ipfF_ne_pqE : ipfF ≠ pqE := by decide
@[simp] theorem ppq_ipfF_ne_pqB : ipfF ≠ pqB := by decide
@[simp] theorem ppq_ipfF_ne_pqS : ipfF ≠ pqS := by decide
@[simp] theorem ppq_ipfF_ne_ipfE : ipfF ≠ ipfE := by decide
@[simp] theorem ppq_ipfF_ne_ipfW : ipfF ≠ ipfW := by decide
@[simp] theorem ppq_ipfF_ne_ipfL : ipfF ≠ ipfL := by decide
@[simp] theorem ppq_ipfF_ne_npfF : ipfF ≠ npfF := by decide
@[simp] theorem ppq_ipfF_ne_npfE : ipfF ≠ npfE := by decide
@[simp] theorem ppq_ipfF_ne_npfW : ipfF ≠ npfW := by decide
@[simp] theorem ppq_ipfF_ne_npfL : ipfF ≠ npfL := by decide
@[simp] theorem ppq_ipfF_ne_lFl : ipfF ≠ lFl := by decide
@[simp] theorem ppq_lFl_ne_ipfF : lFl ≠ ipfF := by decide
@[simp] theorem ppq_ipfF_ne_lDh : ipfF ≠ lDh := by decide
@[simp] theorem ppq_lDh_ne_ipfF : lDh ≠ ipfF := by decide
@[simp] theorem ppq_ipfF_ne_lDt : ipfF ≠ lDt := by decide
@[simp] theorem ppq_lDt_ne_ipfF : lDt ≠ ipfF := by decide
@[simp] theorem ppq_ipfF_ne_lDg : ipfF ≠ lDg := by decide
@[simp] theorem ppq_lDg_ne_ipfF : lDg ≠ ipfF := by decide
@[simp] theorem ppq_ipfF_ne_lDi : ipfF ≠ lDi := by decide
@[simp] theorem ppq_lDi_ne_ipfF : lDi ≠ ipfF := by decide
@[simp] theorem ppq_ipfF_ne_lRp : ipfF ≠ lRp := by decide
@[simp] theorem ppq_lRp_ne_ipfF : lRp ≠ ipfF := by decide
@[simp] theorem ppq_ipfF_ne_lRn : ipfF ≠ lRn := by decide
@[simp] theorem ppq_lRn_ne_ipfF : lRn ≠ ipfF := by decide
@[simp] theorem ppq_ipfF_ne_lFle : ipfF ≠ lFle := by decide
@[simp] theorem ppq_lFle_ne_ipfF : lFle ≠ ipfF := by decide
@[simp] theorem ppq_ipfF_ne_lKb : ipfF ≠ lKb := by decide
@[simp] theorem ppq_lKb_ne_ipfF : lKb ≠ ipfF := by decide
@[simp] theorem ppq_ipfF_ne_lDir : ipfF ≠ lDir := by decide
@[simp] theorem ppq_lDir_ne_ipfF : lDir ≠ ipfF := by decide
@[simp] theorem ppq_ipfF_ne_lFln : ipfF ≠ lFln := by decide
@[simp] theorem ppq_lFln_ne_ipfF : lFln ≠ ipfF := by decide
@[simp] theorem ppq_ipfF_ne_lFll : ipfF ≠ lFll := by decide
@[simp] theorem ppq_lFll_ne_ipfF : lFll ≠ ipfF := by decide
@[simp] theorem ppq_ipfF_ne_lFls : ipfF ≠ lFls := by decide
@[simp] theorem ppq_lFls_ne_ipfF : lFls ≠ ipfF := by decide
@[simp] theorem ppq_ipfF_ne_kFu : ipfF ≠ kFu := by decide
@[simp] theorem ppq_kFu_ne_ipfF : kFu ≠ ipfF := by decide
@[simp] theorem ppq_ipfF_ne_kD : ipfF ≠ kD := by decide
@[simp] theorem ppq_kD_ne_ipfF : kD ≠ ipfF := by decide
@[simp] theorem ppq_ipfE_ne_pqF : ipfE ≠ pqF := by decide
@[simp] theorem ppq_ipfE_ne_pqE : ipfE ≠ pqE := by decide
@[simp] theorem ppq_ipfE_ne_pqB : ipfE ≠ pqB := by decide
@[simp] theorem ppq_ipfE_ne_pqS : ipfE ≠ pqS := by decide
@[simp] theorem ppq_ipfE_ne_ipfF : ipfE ≠ ipfF := by decide
@[simp] theorem ppq_ipfE_ne_ipfW : ipfE ≠ ipfW := by decide
@[simp] theorem ppq_ipfE_ne_ipfL : ipfE ≠ ipfL := by decide
@[simp] theorem ppq_ipfE_ne_npfF : ipfE ≠ npfF := by decide
@[simp] theorem ppq_ipfE_ne_npfE : ipfE ≠ npfE := by decide
@[simp] theorem ppq_ipfE_ne_npfW : ipfE ≠ npfW := by decide
@[simp] theorem ppq_ipfE_ne_npfL : ipfE ≠ npfL := by decide
@[simp] theorem ppq_ipfE_ne_lFl : ipfE ≠ lFl := by decide
@[simp] theorem ppq_lFl_ne_ipfE : lFl ≠ ipfE := by decide
@[simp] theorem ppq_ipfE_ne_lDh : ipfE ≠ lDh := by decide
@[simp] theorem ppq_lDh_ne_ipfE : lDh ≠ ipfE := by decide
@[simp] theorem ppq_ipfE_ne_lDt : ipfE ≠ lDt := by decide
@[simp] theorem ppq_lDt_ne_ipfE : lDt ≠ ipfE := by decide
@[simp] theorem ppq_ipfE_ne_lDg : ipfE ≠ lDg := by decide
@[simp] theorem ppq_lDg_ne_ipfE : lDg ≠ ipfE := by decide
@[simp] theorem ppq_ipfE_ne_lDi : ipfE ≠ lDi := by decide
@[simp] theorem ppq_lDi_ne_ipfE : lDi ≠ ipfE := by decide
@[simp] theorem ppq_ipfE_ne_lRp : ipfE ≠ lRp := by decide
@[simp] theorem ppq_lRp_ne_ipfE : lRp ≠ ipfE := by decide
@[simp] theorem ppq_ipfE_ne_lRn : ipfE ≠ lRn := by decide
@[simp] theorem ppq_lRn_ne_ipfE : lRn ≠ ipfE := by decide
@[simp] theorem ppq_ipfE_ne_lFle : ipfE ≠ lFle := by decide
@[simp] theorem ppq_lFle_ne_ipfE : lFle ≠ ipfE := by decide
@[simp] theorem ppq_ipfE_ne_lKb : ipfE ≠ lKb := by decide
@[simp] theorem ppq_lKb_ne_ipfE : lKb ≠ ipfE := by decide
@[simp] theorem ppq_ipfE_ne_lDir : ipfE ≠ lDir := by decide
@[simp] theorem ppq_lDir_ne_ipfE : lDir ≠ ipfE := by decide
@[simp] theorem ppq_ipfE_ne_lFln : ipfE ≠ lFln := by decide
@[simp] theorem ppq_lFln_ne_ipfE : lFln ≠ ipfE := by decide
@[simp] theorem ppq_ipfE_ne_lFll : ipfE ≠ lFll := by decide
@[simp] theorem ppq_lFll_ne_ipfE : lFll ≠ ipfE := by decide
@[simp] theorem ppq_ipfE_ne_lFls : ipfE ≠ lFls := by decide
@[simp] theorem ppq_lFls_ne_ipfE : lFls ≠ ipfE := by decide
@[simp] theorem ppq_ipfE_ne_kFu : ipfE ≠ kFu := by decide
@[simp] theorem ppq_kFu_ne_ipfE : kFu ≠ ipfE := by decide
@[simp] theorem ppq_ipfE_ne_kD : ipfE ≠ kD := by decide
@[simp] theorem ppq_kD_ne_ipfE : kD ≠ ipfE := by decide
@[simp] theorem ppq_ipfW_ne_pqF : ipfW ≠ pqF := by decide
@[simp] theorem ppq_ipfW_ne_pqE : ipfW ≠ pqE := by decide
@[simp] theorem ppq_ipfW_ne_pqB : ipfW ≠ pqB := by decide
@[simp] theorem ppq_ipfW_ne_pqS : ipfW ≠ pqS := by decide
@[simp] theorem ppq_ipfW_ne_ipfF : ipfW ≠ ipfF := by decide
@[simp] theorem ppq_ipfW_ne_ipfE : ipfW ≠ ipfE := by decide
@[simp] theorem ppq_ipfW_ne_ipfL : ipfW ≠ ipfL := by decide
@[simp] theorem ppq_ipfW_ne_npfF : ipfW ≠ npfF := by decide
@[simp] theorem ppq_ipfW_ne_npfE : ipfW ≠ npfE := by decide
@[simp] theorem ppq_ipfW_ne_npfW : ipfW ≠ npfW := by decide
@[simp] theorem ppq_ipfW_ne_npfL : ipfW ≠ npfL := by decide
@[simp] theorem ppq_ipfW_ne_lFl : ipfW ≠ lFl := by decide
@[simp] theorem ppq_lFl_ne_ipfW : lFl ≠ ipfW := by decide
@[simp] theorem ppq_ipfW_ne_lDh : ipfW ≠ lDh := by decide
@[simp] theorem ppq_lDh_ne_ipfW : lDh ≠ ipfW := by decide
@[simp] theorem ppq_ipfW_ne_lDt : ipfW ≠ lDt := by decide
@[simp] theorem ppq_lDt_ne_ipfW : lDt ≠ ipfW := by decide
@[simp] theorem ppq_ipfW_ne_lDg : ipfW ≠ lDg := by decide
@[simp] theorem ppq_lDg_ne_ipfW : lDg ≠ ipfW := by decide
@[simp] theorem ppq_ipfW_ne_lDi : ipfW ≠ lDi := by decide
@[simp] theorem ppq_lDi_ne_ipfW : lDi ≠ ipfW := by decide
@[simp] theorem ppq_ipfW_ne_lRp : ipfW ≠ lRp := by decide
@[simp] theorem ppq_lRp_ne_ipfW : lRp ≠ ipfW := by decide
@[simp] theorem ppq_ipfW_ne_lRn : ipfW ≠ lRn := by decide
@[simp] theorem ppq_lRn_ne_ipfW : lRn ≠ ipfW := by decide
@[simp] theorem ppq_ipfW_ne_lFle : ipfW ≠ lFle := by decide
@[simp] theorem ppq_lFle_ne_ipfW : lFle ≠ ipfW := by decide
@[simp] theorem ppq_ipfW_ne_lKb : ipfW ≠ lKb := by decide
@[simp] theorem ppq_lKb_ne_ipfW : lKb ≠ ipfW := by decide
@[simp] theorem ppq_ipfW_ne_lDir : ipfW ≠ lDir := by decide
@[simp] theorem ppq_lDir_ne_ipfW : lDir ≠ ipfW := by decide
@[simp] theorem ppq_ipfW_ne_lFln : ipfW ≠ lFln := by decide
@[simp] theorem ppq_lFln_ne_ipfW : lFln ≠ ipfW := by decide
@[simp] theorem ppq_ipfW_ne_lFll : ipfW ≠ lFll := by decide
@[simp] theorem ppq_lFll_ne_ipfW : lFll ≠ ipfW := by decide
@[simp] theorem ppq_ipfW_ne_lFls : ipfW ≠ lFls := by decide
@[simp] theorem ppq_lFls_ne_ipfW : lFls ≠ ipfW := by decide
@[simp] theorem ppq_ipfW_ne_kFu : ipfW ≠ kFu := by decide
@[simp] theorem ppq_kFu_ne_ipfW : kFu ≠ ipfW := by decide
@[simp] theorem ppq_ipfW_ne_kD : ipfW ≠ kD := by decide
@[simp] theorem ppq_kD_ne_ipfW : kD ≠ ipfW := by decide
@[simp] theorem ppq_ipfL_ne_pqF : ipfL ≠ pqF := by decide
@[simp] theorem ppq_ipfL_ne_pqE : ipfL ≠ pqE := by decide
@[simp] theorem ppq_ipfL_ne_pqB : ipfL ≠ pqB := by decide
@[simp] theorem ppq_ipfL_ne_pqS : ipfL ≠ pqS := by decide
@[simp] theorem ppq_ipfL_ne_ipfF : ipfL ≠ ipfF := by decide
@[simp] theorem ppq_ipfL_ne_ipfE : ipfL ≠ ipfE := by decide
@[simp] theorem ppq_ipfL_ne_ipfW : ipfL ≠ ipfW := by decide
@[simp] theorem ppq_ipfL_ne_npfF : ipfL ≠ npfF := by decide
@[simp] theorem ppq_ipfL_ne_npfE : ipfL ≠ npfE := by decide
@[simp] theorem ppq_ipfL_ne_npfW : ipfL ≠ npfW := by decide
@[simp] theorem ppq_ipfL_ne_npfL : ipfL ≠ npfL := by decide
@[simp] theorem ppq_ipfL_ne_lFl : ipfL ≠ lFl := by decide
@[simp] theorem ppq_lFl_ne_ipfL : lFl ≠ ipfL := by decide
@[simp] theorem ppq_ipfL_ne_lDh : ipfL ≠ lDh := by decide
@[simp] theorem ppq_lDh_ne_ipfL : lDh ≠ ipfL := by decide
@[simp] theorem ppq_ipfL_ne_lDt : ipfL ≠ lDt := by decide
@[simp] theorem ppq_lDt_ne_ipfL : lDt ≠ ipfL := by decide
@[simp] theorem ppq_ipfL_ne_lDg : ipfL ≠ lDg := by decide
@[simp] theorem ppq_lDg_ne_ipfL : lDg ≠ ipfL := by decide
@[simp] theorem ppq_ipfL_ne_lDi : ipfL ≠ lDi := by decide
@[simp] theorem ppq_lDi_ne_ipfL : lDi ≠ ipfL := by decide
@[simp] theorem ppq_ipfL_ne_lRp : ipfL ≠ lRp := by decide
@[simp] theorem ppq_lRp_ne_ipfL : lRp ≠ ipfL := by decide
@[simp] theorem ppq_ipfL_ne_lRn : ipfL ≠ lRn := by decide
@[simp] theorem ppq_lRn_ne_ipfL : lRn ≠ ipfL := by decide
@[simp] theorem ppq_ipfL_ne_lFle : ipfL ≠ lFle := by decide
@[simp] theorem ppq_lFle_ne_ipfL : lFle ≠ ipfL := by decide
@[simp] theorem ppq_ipfL_ne_lKb : ipfL ≠ lKb := by decide
@[simp] theorem ppq_lKb_ne_ipfL : lKb ≠ ipfL := by decide
@[simp] theorem ppq_ipfL_ne_lDir : ipfL ≠ lDir := by decide
@[simp] theorem ppq_lDir_ne_ipfL : lDir ≠ ipfL := by decide
@[simp] theorem ppq_ipfL_ne_lFln : ipfL ≠ lFln := by decide
@[simp] theorem ppq_lFln_ne_ipfL : lFln ≠ ipfL := by decide
@[simp] theorem ppq_ipfL_ne_lFll : ipfL ≠ lFll := by decide
@[simp] theorem ppq_lFll_ne_ipfL : lFll ≠ ipfL := by decide
@[simp] theorem ppq_ipfL_ne_lFls : ipfL ≠ lFls := by decide
@[simp] theorem ppq_lFls_ne_ipfL : lFls ≠ ipfL := by decide
@[simp] theorem ppq_ipfL_ne_kFu : ipfL ≠ kFu := by decide
@[simp] theorem ppq_kFu_ne_ipfL : kFu ≠ ipfL := by decide
@[simp] theorem ppq_ipfL_ne_kD : ipfL ≠ kD := by decide
@[simp] theorem ppq_kD_ne_ipfL : kD ≠ ipfL := by decide
@[simp] theorem ppq_npfF_ne_pqF : npfF ≠ pqF := by decide
@[simp] theorem ppq_npfF_ne_pqE : npfF ≠ pqE := by decide
@[simp] theorem ppq_npfF_ne_pqB : npfF ≠ pqB := by decide
@[simp] theorem ppq_npfF_ne_pqS : npfF ≠ pqS := by decide
@[simp] theorem ppq_npfF_ne_ipfF : npfF ≠ ipfF := by decide
@[simp] theorem ppq_npfF_ne_ipfE : npfF ≠ ipfE := by decide
@[simp] theorem ppq_npfF_ne_ipfW : npfF ≠ ipfW := by decide
@[simp] theorem ppq_npfF_ne_ipfL : npfF ≠ ipfL := by decide
@[simp] theorem ppq_npfF_ne_npfE : npfF ≠ npfE := by decide
@[simp] theorem ppq_npfF_ne_npfW : npfF ≠ npfW := by decide
@[simp] theorem ppq_npfF_ne_npfL : npfF ≠ npfL := by decide
@[simp] theorem ppq_npfF_ne_lFl : npfF ≠ lFl := by decide
@[simp] theorem ppq_lFl_ne_npfF : lFl ≠ npfF := by decide
@[simp] theorem ppq_npfF_ne_lDh : npfF ≠ lDh := by decide
@[simp] theorem ppq_lDh_ne_npfF : lDh ≠ npfF := by decide
@[simp] theorem ppq_npfF_ne_lDt : npfF ≠ lDt := by decide
@[simp] theorem ppq_lDt_ne_npfF : lDt ≠ npfF := by decide
@[simp] theorem ppq_npfF_ne_lDg : npfF ≠ lDg := by decide
@[simp] theorem ppq_lDg_ne_npfF : lDg ≠ npfF := by decide
@[simp] theorem ppq_npfF_ne_lDi : npfF ≠ lDi := by decide
@[simp] theorem ppq_lDi_ne_npfF : lDi ≠ npfF := by decide
@[simp] theorem ppq_npfF_ne_lRp : npfF ≠ lRp := by decide
@[simp] theorem ppq_lRp_ne_npfF : lRp ≠ npfF := by decide
@[simp] theorem ppq_npfF_ne_lRn : npfF ≠ lRn := by decide
@[simp] theorem ppq_lRn_ne_npfF : lRn ≠ npfF := by decide
@[simp] theorem ppq_npfF_ne_lFle : npfF ≠ lFle := by decide
@[simp] theorem ppq_lFle_ne_npfF : lFle ≠ npfF := by decide
@[simp] theorem ppq_npfF_ne_lKb : npfF ≠ lKb := by decide
@[simp] theorem ppq_lKb_ne_npfF : lKb ≠ npfF := by decide
@[simp] theorem ppq_npfF_ne_lDir : npfF ≠ lDir := by decide
@[simp] theorem ppq_lDir_ne_npfF : lDir ≠ npfF := by decide
@[simp] theorem ppq_npfF_ne_lFln : npfF ≠ lFln := by decide
@[simp] theorem ppq_lFln_ne_npfF : lFln ≠ npfF := by decide
@[simp] theorem ppq_npfF_ne_lFll : npfF ≠ lFll := by decide
@[simp] theorem ppq_lFll_ne_npfF : lFll ≠ npfF := by decide
@[simp] theorem ppq_npfF_ne_lFls : npfF ≠ lFls := by decide
@[simp] theorem ppq_lFls_ne_npfF : lFls ≠ npfF := by decide
@[simp] theorem ppq_npfF_ne_kFu : npfF ≠ kFu := by decide
@[simp] theorem ppq_kFu_ne_npfF : kFu ≠ npfF := by decide
@[simp] theorem ppq_npfF_ne_kD : npfF ≠ kD := by decide
@[simp] theorem ppq_kD_ne_npfF : kD ≠ npfF := by decide
@[simp] theorem ppq_npfE_ne_pqF : npfE ≠ pqF := by decide
@[simp] theorem ppq_npfE_ne_pqE : npfE ≠ pqE := by decide
@[simp] theorem ppq_npfE_ne_pqB : npfE ≠ pqB := by decide
@[simp] theorem ppq_npfE_ne_pqS : npfE ≠ pqS := by decide
@[simp] theorem ppq_npfE_ne_ipfF : npfE ≠ ipfF := by decide
@[simp] theorem ppq_npfE_ne_ipfE : npfE ≠ ipfE := by decide
@[simp] theorem ppq_npfE_ne_ipfW : npfE ≠ ipfW := by decide
@[simp] theorem ppq_npfE_ne_ipfL : npfE ≠ ipfL := by decide
@[simp] theorem ppq_npfE_ne_npfF : npfE ≠ npfF := by decide
@[simp] theorem ppq_npfE_ne_npfW : npfE ≠ npfW := by decide
@[simp] theorem ppq_npfE_ne_npfL : npfE ≠ npfL := by decide
@[simp] theorem ppq_npfE_ne_lFl : npfE ≠ lFl := by decide
@[simp] theorem ppq_lFl_ne_npfE : lFl ≠ npfE := by decide
@[simp] theorem ppq_npfE_ne_lDh : npfE ≠ lDh := by decide
@[simp] theorem ppq_lDh_ne_npfE : lDh ≠ npfE := by decide
@[simp] theorem ppq_npfE_ne_lDt : npfE ≠ lDt := by decide
@[simp] theorem ppq_lDt_ne_npfE : lDt ≠ npfE := by decide
@[simp] theorem ppq_npfE_ne_lDg : npfE ≠ lDg := by decide
@[simp] theorem ppq_lDg_ne_npfE : lDg ≠ npfE := by decide
@[simp] theorem ppq_npfE_ne_lDi : npfE ≠ lDi := by decide
@[simp] theorem ppq_lDi_ne_npfE : lDi ≠ npfE := by decide
@[simp] theorem ppq_npfE_ne_lRp : npfE ≠ lRp := by decide
@[simp] theorem ppq_lRp_ne_npfE : lRp ≠ npfE := by decide
@[simp] theorem ppq_npfE_ne_lRn : npfE ≠ lRn := by decide
@[simp] theorem ppq_lRn_ne_npfE : lRn ≠ npfE := by decide
@[simp] theorem ppq_npfE_ne_lFle : npfE ≠ lFle := by decide
@[simp] theorem ppq_lFle_ne_npfE : lFle ≠ npfE := by decide
@[simp] theorem ppq_npfE_ne_lKb : npfE ≠ lKb := by decide
@[simp] theorem ppq_lKb_ne_npfE : lKb ≠ npfE := by decide
@[simp] theorem ppq_npfE_ne_lDir : npfE ≠ lDir := by decide
@[simp] theorem ppq_lDir_ne_npfE : lDir ≠ npfE := by decide
@[simp] theorem ppq_npfE_ne_lFln : npfE ≠ lFln := by decide
@[simp] theorem ppq_lFln_ne_npfE : lFln ≠ npfE := by decide
@[simp] theorem ppq_npfE_ne_lFll : npfE ≠ lFll := by decide
@[simp] theorem ppq_lFll_ne_npfE : lFll ≠ npfE := by decide
@[simp] theorem ppq_npfE_ne_lFls : npfE ≠ lFls := by decide
@[simp] theorem ppq_lFls_ne_npfE : lFls ≠ npfE := by decide
@[simp] theorem ppq_npfE_ne_kFu : npfE ≠ kFu := by decide
@[simp] theorem ppq_kFu_ne_npfE : kFu ≠ npfE := by decide
@[simp] theorem ppq_npfE_ne_kD : npfE ≠ kD := by decide
@[simp] theorem ppq_kD_ne_npfE : kD ≠ npfE := by decide
@[simp] theorem ppq_npfW_ne_pqF : npfW ≠ pqF := by decide
@[simp] theorem ppq_npfW_ne_pqE : npfW ≠ pqE := by decide
@[simp] theorem ppq_npfW_ne_pqB : npfW ≠ pqB := by decide
@[simp] theorem ppq_npfW_ne_pqS : npfW ≠ pqS := by decide
@[simp] theorem ppq_npfW_ne_ipfF : npfW ≠ ipfF := by decide
@[simp] theorem ppq_npfW_ne_ipfE : npfW ≠ ipfE := by decide
@[simp] theorem ppq_npfW_ne_ipfW : npfW ≠ ipfW := by decide
@[simp] theorem ppq_npfW_ne_ipfL : npfW ≠ ipfL := by decide
@[simp] theorem ppq_npfW_ne_npfF : npfW ≠ npfF := by decide
@[simp] theorem ppq_npfW_ne_npfE : npfW ≠ npfE := by decide
@[simp] theorem ppq_npfW_ne_npfL : npfW ≠ npfL := by decide
@[simp] theorem ppq_npfW_ne_lFl : npfW ≠ lFl := by decide
@[simp] theorem ppq_lFl_ne_npfW : lFl ≠ npfW := by decide
@[simp] theorem ppq_npfW_ne_lDh : npfW ≠ lDh := by decide
@[simp] theorem ppq_lDh_ne_npfW : lDh ≠ npfW := by decide
@[simp] theorem ppq_npfW_ne_lDt : npfW ≠ lDt := by decide
@[simp] theorem ppq_lDt_ne_npfW : lDt ≠ npfW := by decide
@[simp] theorem ppq_npfW_ne_lDg : npfW ≠ lDg := by decide
@[simp] theorem ppq_lDg_ne_npfW : lDg ≠ npfW := by decide
@[simp] theorem ppq_npfW_ne_lDi : npfW ≠ lDi := by decide
@[simp] theorem ppq_lDi_ne_npfW : lDi ≠ npfW := by decide
@[simp] theorem ppq_npfW_ne_lRp : npfW ≠ lRp := by decide
@[simp] theorem ppq_lRp_ne_npfW : lRp ≠ npfW := by decide
@[simp] theorem ppq_npfW_ne_lRn : npfW ≠ lRn := by decide
@[simp] theorem ppq_lRn_ne_npfW : lRn ≠ npfW := by decide
@[simp] theorem ppq_npfW_ne_lFle : npfW ≠ lFle := by decide
@[simp] theorem ppq_lFle_ne_npfW : lFle ≠ npfW := by decide
@[simp] theorem ppq_npfW_ne_lKb : npfW ≠ lKb := by decide
@[simp] theorem ppq_lKb_ne_npfW : lKb ≠ npfW := by decide
@[simp] theorem ppq_npfW_ne_lDir : npfW ≠ lDir := by decide
@[simp] theorem ppq_lDir_ne_npfW : lDir ≠ npfW := by decide
@[simp] theorem ppq_npfW_ne_lFln : npfW ≠ lFln := by decide
@[simp] theorem ppq_lFln_ne_npfW : lFln ≠ npfW := by decide
@[simp] theorem ppq_npfW_ne_lFll : npfW ≠ lFll := by decide
@[simp] theorem ppq_lFll_ne_npfW : lFll ≠ npfW := by decide
@[simp] theorem ppq_npfW_ne_lFls : npfW ≠ lFls := by decide
@[simp] theorem ppq_lFls_ne_npfW : lFls ≠ npfW := by decide
@[simp] theorem ppq_npfW_ne_kFu : npfW ≠ kFu := by decide
@[simp] theorem ppq_kFu_ne_npfW : kFu ≠ npfW := by decide
@[simp] theorem ppq_npfW_ne_kD : npfW ≠ kD := by decide
@[simp] theorem ppq_kD_ne_npfW : kD ≠ npfW := by decide
@[simp] theorem ppq_npfL_ne_pqF : npfL ≠ pqF := by decide
@[simp] theorem ppq_npfL_ne_pqE : npfL ≠ pqE := by decide
@[simp] theorem ppq_npfL_ne_pqB : npfL ≠ pqB := by decide
@[simp] theorem ppq_npfL_ne_pqS : npfL ≠ pqS := by decide
@[simp] theorem ppq_npfL_ne_ipfF : npfL ≠ ipfF := by decide
@[simp] theorem ppq_npfL_ne_ipfE : npfL ≠ ipfE := by decide
@[simp] theorem ppq_npfL_ne_ipfW : npfL ≠ ipfW := by decide
@[simp] theorem ppq_npfL_ne_ipfL : npfL ≠ ipfL := by decide
@[simp] theorem ppq_npfL_ne_npfF : npfL ≠ npfF := by decide
@[simp] theorem ppq_npfL_ne_npfE : npfL ≠ npfE := by decide
@[simp] theorem ppq_npfL_ne_npfW : npfL ≠ npfW := by decide
@[simp] theorem ppq_npfL_ne_lFl : npfL ≠ lFl := by decide
@[simp] theorem ppq_lFl_ne_npfL : lFl ≠ npfL := by decide
@[simp] theorem ppq_npfL_ne_lDh : npfL ≠ lDh := by decide
@[simp] theorem ppq_lDh_ne_npfL : lDh ≠ npfL := by decide
@[simp] theorem ppq_npfL_ne_lDt : npfL ≠ lDt := by decide
@[simp] theorem ppq_lDt_ne_npfL : lDt ≠ npfL := by decide
@[simp] theorem ppq_npfL_ne_lDg : npfL ≠ lDg := by decide
@[simp] theorem ppq_lDg_ne_npfL : lDg ≠ npfL := by decide
@[simp] theorem ppq_npfL_ne_lDi : npfL ≠ lDi := by decide
@[simp] theorem ppq_lDi_ne_npfL : lDi ≠ npfL := by decide
@[simp] theorem ppq_npfL_ne_lRp : npfL ≠ lRp := by decide
@[simp] theorem ppq_lRp_ne_npfL : lRp ≠ npfL := by decide
@[simp] theorem ppq_npfL_ne_lRn : npfL ≠ lRn := by decide
@[simp] theorem ppq_lRn_ne_npfL : lRn ≠ npfL := by decide
@[simp] theorem ppq_npfL_ne_lFle : npfL ≠ lFle := by decide
@[simp] theorem ppq_lFle_ne_npfL : lFle ≠ npfL := by decide
@[simp] theorem ppq_npfL_ne_lKb : npfL ≠ lKb := by decide
@[simp] theorem ppq_lKb_ne_npfL : lKb ≠ npfL := by decide
@[simp] theorem ppq_npfL_ne_lDir : npfL ≠ lDir := by decide
@[simp] theorem ppq_lDir_ne_npfL : lDir ≠ npfL := by decide
@[simp] theorem ppq_npfL_ne_lFln : npfL ≠ lFln := by decide
@[simp] theorem ppq_lFln_ne_npfL : lFln ≠ npfL := by decide
@[simp] theorem ppq_npfL_ne_lFll : npfL ≠ lFll := by decide
@[simp] theorem ppq_lFll_ne_npfL : lFll ≠ npfL := by decide
@[simp] theorem ppq_npfL_ne_lFls : npfL ≠ lFls := by decide
@[simp] theorem ppq_lFls_ne_npfL : lFls ≠ npfL := by decide
@[simp] theorem ppq_npfL_ne_kFu : npfL ≠ kFu := by decide
@[simp] theorem ppq_kFu_ne_npfL : kFu ≠ npfL := by decide
@[simp] theorem ppq_npfL_ne_kD : npfL ≠ kD := by decide
@[simp] theorem ppq_kD_ne_npfL : kD ≠ npfL := by decide

def pqParams : List MlS := [pqF, pqE]
def pqLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, pqB, pqS]
def pqBody (C : Ctx) : ProgHOL 64 := prologue pqLocals (.ite (.cmp .equal (vv pqF) (.const 0)) hang (.ite (tagIsE pqE 5) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pqE)) (.seq eViewP (.seq (.assign .local pqB (.load .one (.op .add [(vv lRp), (.const 8)]))) (.seq (.call (some (some (.local, pqS), none)) fPq [(.op .sub [(vv pqF), (.const 1)]), (vv pqB)]) (.return (vv pqS))))))) (.ite (tagIsE pqE 7) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pqE)) (.seq eViewP (.seq (.assign .local pqB (.load .one (.op .add [(vv lRp), (.const 16)]))) (.seq (.call (some (some (.local, pqS), none)) fPq [(.op .sub [(vv pqF), (.const 1)]), (vv pqB)]) (.return (vv pqS))))))) (.ite (isAppE (vv pqE)) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pqE)) (.seq eViewP (.seq (.assign .local pqB (.load .one (.op .add [(vv lRp), (.const 0)]))) (.seq (.call (some (some (.local, pqS), none)) fPq [(.op .sub [(vv pqF), (.const 1)]), (vv pqB)]) (.return (vv pqS))))))) (.seq (.call (some (some (.local, pqS), none)) fHq [(.op .sub [(vv pqF), (.const 1)]), (vv pqE)]) (.return (vv pqS)))))))
def ipfParams : List MlS := [ipfF, ipfE]
def ipfLocals : List MlS := [ipfW, ipfL]
def ipfBody (C : Ctx) : ProgHOL 64 := prologue ipfLocals (.seq (.call (some (some (.local, ipfW), none)) fPq [(vv ipfF), (vv ipfE)]) (.ite (.cmp .equal (vv ipfW) (.const 0)) (.return (.const 0)) (.ite (.cmp .equal (vv ipfW) (.const 1)) (.return (.const 0)) (.seq (.assign .local ipfL (.load .one (vv ipfW))) (.ite (.cmp .equal (vv ipfL) (.const 0)) (.return (.const 1)) (.return (.const 0)))))))
def npfParams : List MlS := [npfF, npfE]
def npfLocals : List MlS := [npfW, npfL]
def npfBody (C : Ctx) : ProgHOL 64 := prologue npfLocals (.seq (.call (some (some (.local, npfW), none)) fPq [(vv npfF), (vv npfE)]) (.ite (.cmp .equal (vv npfW) (.const 0)) (.return (.const 0)) (.ite (.cmp .equal (vv npfW) (.const 1)) (.return (.const 1)) (.seq (.assign .local npfL (.load .one (vv npfW))) (.ite (.cmp .equal (vv npfL) (.const 0)) (.return (.const 0)) (.return (.const 1)))))))

structure PqCodes (C : Ctx) : Prop where
  hq : C.code.lookup fHq = some (hqParams.map (fun p => (p, ShapeHOL.one)), hqBody C, .one)
  hqc : HqCodes C
  self : C.code.lookup fPq = some (pqParams.map (fun p => (p, ShapeHOL.one)), pqBody C, .one)

structure IpfCodes (C : Ctx) : Prop where
  pq : C.code.lookup fPq = some (pqParams.map (fun p => (p, ShapeHOL.one)), pqBody C, .one)
  pqc : PqCodes C

/-- A fast arm's answer: the read caches may fill, the word is the Boolean. -/
def PostRB (C : Ctx) (s : AState) (b : Bool) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  RdStep s s' ∧ w = boolW b ∧ ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st

theorem postRB_locals (C : Ctx) (s : AState) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostRB C s a w s' st → PostRB C s a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2, H', h3, h4⟩ => ⟨h1, h2, H', h3, sr_of_eq h4 rfl rfl rfl rfl⟩

theorem specR_appIteX {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {c1 c2 : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (h : EIdx) (hh : Γ.get x = some (Enc.idxW h))
    (h1 : h.tag = 4 → SpecR (Inv C s Γ M D) c1 s m R) (h2 : h.tag ≠ 4 → SpecR (Inv C s Γ M D) c2 s m R) :
    SpecR (Inv C s Γ M D) (.ite (isAppE (vv x)) c1 c2) s m R :=
  specR_ifI _ _ (Ex2.sev_isApp Γ x _ hh) (fun e => h1 ((isApp_iff h).mp e))
    (fun e => h2 (fun t => by have := (isApp_iff h).mpr t; exact this e))

theorem blk_len_small {C : Ctx} (hok : CtxOK C) {H : List (BitVec 64)} {s : AState} {t : PState σ}
    (hsr : SR (ctxH C H) s t) {o : Nat} {xs : List (BitVec 64)} (hb : BlkAt H o xs) : xs.length < 2 ^ 61 := by
  obtain ⟨H0, hp0, ha0⟩ := hsr.heap
  have h1 := ha0.len
  have h2 := hp0.length_le
  have hlay := hok.heapLay
  have hhi := hok.heapHigh
  have e1 : (ctxH C H).HN = C.HN := rfl
  have e2 : (ctxH C H).H = H := rfl
  rw [e1] at h1; rw [e2] at h2
  have := blkAt_len hb
  omega

section
variable {σ : Type}

theorem pq_spec (C : Ctx) (hok : CtxOK C) (hc : PqCodes C) (s : AState) (hwf : LStoreWF s.store.ls) (hrd : RdOK s)
    (hSD : ∀ h u, s.store.view h = some (.sort u) → ∃ l, denoteL s.store.ls u = some l)
    (hLP : ∀ c ci, C.fe.find? c = some ci → ∃ ks, Frontend.denoteNList s.store.ns ci.toConstantVal.levelParams = some ks)
    (hLPl : ∀ c ci, C.fe.find? c = some ci → ci.toConstantVal.levelParams.length < 2 ^ 60)
    (hLS : ∀ us uh, s.store.lss.view us = some uh → ∃ vs, denoteLs s.store.lss us = some vs ∧ ∃ hl : vs.length = uh.length,
      ∀ j (hj : j < uh.length), denoteL s.store.ls uh[j] = some (vs[j]'(by rw [hl]; exact hj)))
    (hTB : ∀ T tb, C.fe.findTable? T = some tb → tb.bodies.size = tb.numFields) :
    ∀ (F : Nat) (e : EIdx) (H : List (BitVec 64)), C.H <+: H → F < 2 ^ 61 →
      SpecR (σ := σ) (Pre (ctxH C H) s (pqParams.zip [BitVec.ofNat 64 F, Enc.idxW e])) (pqBody C) s
        (proofPW C.fe F e) (PostSA (ctxH C H) s) := by
  intro F
  induction F with
  | zero =>
    intro e H hpH _
    refine specR_prologue (postSA_locals _ s) (Knot.params_none _ pqLocals pqParams _ (by decide) (by decide)) ?_
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get, pqParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
  | succ F ih =>
    intro e H hpH hF
    refine specR_prologue (postSA_locals _ s) (Knot.params_none _ pqLocals pqParams _ (by decide) (by decide)) ?_
    have hne := ofNat_succ_ne F (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, pqParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
    rw [proofPW]
    refine Knot.specR_tagIteV pqE e 5 (by decide) (by decide) (by simp +decide [Env.get, pqParams, ctxEnv]) (fun htg => ?_) (fun htg5 => ?_)
    · rw [if_pos (show (e.tag == ETag.lam) = true by simp [htg, ETag.lam])]
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv pqE) (Enc.idxW e) (by decide) (by simp +decide [Env.get, pqParams, ctxEnv]) ?_
      refine specR_viewP (C := ctxH C H) e (by simp) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
        (fun v P hv htn _ => ?_)
      have h5 : v.tagN = 5 := by rw [htn, htg]; rfl
      obtain ⟨ty, b, rfl⟩ : ∃ ty b, v = .lam ty b := by cases v <;> simp [ENodeView.tagN] at h5 ⊢
      have hvb : s.store.viewBind e = some (ty, b) := viewBind_of_view_lam (by rw [htg]; rfl) hv
      refine specR_runBind (by rw [viewBind_run, hvb]) ?_
      dsimp only
      refine specR_loadI' pqB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      refine specR_congr (m' := proofPW C.fe F b >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H) pqS fPq pqParams [.op .sub [vv pqF, .const 1], vv pqB] (pqBody C)
        [BitVec.ofNat 64 F, Enc.idxW b] (by decide) rfl (by decide) hc.self
        ⟨by simp +decide [sev, Env.get, pqParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, by simp, trivial⟩
        (PostSA (ctxH C H) s) (fun r_ w s' H' => RdStep s s' ∧ optPW C H' s r_ w)
        (fun r_ w s' st ⟨hst, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hst, hw⟩, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pqParams _ rfl hlk) (ih b H hpH (by omega)))
        (fun r w s1 H1 hp1 ⟨hst, hw⟩ => ?_)
      exact specR_returnI _ w (by simp) (fun t ht => ⟨hst, H1, hp1, hw, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    rw [if_neg (show ¬ (e.tag == ETag.lam) = true by simpa [ETag.lam] using htg5)]
    refine Knot.specR_tagIteV pqE e 7 (by decide) (by decide) (by simp +decide [Env.get, pqParams, ctxEnv]) (fun htg => ?_) (fun htg7 => ?_)
    · rw [if_pos (show (e.tag == ETag.letE) = true by simp [htg, ETag.letE])]
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv pqE) (Enc.idxW e) (by decide) (by simp +decide [Env.get, pqParams, ctxEnv]) ?_
      refine specR_viewP (C := ctxH C H) e (by simp) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
        (fun v P hv htn _ => ?_)
      have h7 : v.tagN = 7 := by rw [htn, htg]; rfl
      obtain ⟨ty, v1, b, rfl⟩ : ∃ ty v1 b, v = .letE ty v1 b := by cases v <;> simp [ENodeView.tagN] at h7 ⊢
      have hvb : s.store.viewLet e = some (ty, v1, b) := by rw [viewLet_bind _ _ (by rw [htg]; rfl), hv]; rfl
      refine specR_runBind (show ConRon.Arena.viewLet e s = .ok (some (ty, v1, b), s) by
        rw [show ConRon.Arena.viewLet e s = .ok (s.store.viewLet e, s) from rfl, hvb]) ?_
      dsimp only
      refine specR_loadI' pqB _ (P + 16) (P + BitVec.ofNat 64 16) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encLet] using wordsAt_mem2 P (Enc.idxW ty) (Enc.idxW v1) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      refine specR_congr (m' := proofPW C.fe F b >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H) pqS fPq pqParams [.op .sub [vv pqF, .const 1], vv pqB] (pqBody C)
        [BitVec.ofNat 64 F, Enc.idxW b] (by decide) rfl (by decide) hc.self
        ⟨by simp +decide [sev, Env.get, pqParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, by simp, trivial⟩
        (PostSA (ctxH C H) s) (fun r_ w s' H' => RdStep s s' ∧ optPW C H' s r_ w)
        (fun r_ w s' st ⟨hst, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hst, hw⟩, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pqParams _ rfl hlk) (ih b H hpH (by omega)))
        (fun r w s1 H1 hp1 ⟨hst, hw⟩ => ?_)
      exact specR_returnI _ w (by simp) (fun t ht => ⟨hst, H1, hp1, hw, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    rw [if_neg (show ¬ (e.tag == ETag.letE) = true by simpa [ETag.letE] using htg7)]
    refine specR_appIteX pqE e (by simp +decide [Env.get, pqParams, ctxEnv]) (fun htg => ?_) (fun htg4 => ?_)
    · rw [if_pos (show (e.tag == ETag.app) = true by simp [htg, ETag.app])]
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv pqE) (Enc.idxW e) (by decide) (by simp +decide [Env.get, pqParams, ctxEnv]) ?_
      refine specR_viewP (C := ctxH C H) e (by simp) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
        (fun v P hv htn _ => ?_)
      have h4 : v.tagN = 4 := by rw [htn, htg]; rfl
      obtain ⟨b, a1, rfl⟩ : ∃ f a, v = .app f a := by cases v <;> simp [ENodeView.tagN] at h4 ⊢
      have hvb : s.store.viewApp e = some (b, a1) := viewApp_of_view (by rw [htg]; rfl) hv
      refine specR_runBind (by rw [viewApp_run, hvb]) ?_
      dsimp only
      refine specR_loadI' pqB _ P (P + BitVec.ofNat 64 0) (Enc.idxW b) (by decide) (by simp +decide [sev]) (by simp)
        (by simpa [encEView, Enc.encApp] using wordsAt_mem0 P (Enc.idxW b) [Enc.idxW a1] []) ?_
      refine specR_dropM ?_
      refine specR_congr (m' := proofPW C.fe F b >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H) pqS fPq pqParams [.op .sub [vv pqF, .const 1], vv pqB] (pqBody C)
        [BitVec.ofNat 64 F, Enc.idxW b] (by decide) rfl (by decide) hc.self
        ⟨by simp +decide [sev, Env.get, pqParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, by simp, trivial⟩
        (PostSA (ctxH C H) s) (fun r_ w s' H' => RdStep s s' ∧ optPW C H' s r_ w)
        (fun r_ w s' st ⟨hst, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hst, hw⟩, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pqParams _ rfl hlk) (ih b H hpH (by omega)))
        (fun r w s1 H1 hp1 ⟨hst, hw⟩ => ?_)
      exact specR_returnI _ w (by simp) (fun t ht => ⟨hst, H1, hp1, hw, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    rw [if_neg (show ¬ (e.tag == ETag.app) = true by simpa [ETag.app] using htg4)]
    refine specR_congr (m' := headProofPW C.fe F e >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H) pqS fHq hqParams [.op .sub [vv pqF, .const 1], vv pqE] (hqBody C)
      [BitVec.ofNat 64 F, Enc.idxW e] (by decide) rfl (by decide) hc.hq
      ⟨by simp +decide [sev, Env.get, pqParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, by simp +decide [Env.get, pqParams, ctxEnv], trivial⟩
      (PostSA (ctxH C H) s) (fun r_ w s' H' => RdStep s s' ∧ optPW C H' s r_ w)
      (fun r_ w s' st ⟨hst, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hst, hw⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu hqParams _ rfl hlk)
        (hq_spec C hok hc.hqc F (by omega) s hwf hrd hSD hLP hLPl hLS hTB H e hpH))
      (fun r w s2 H2 hp2 ⟨hst, hw⟩ => ?_)
    exact specR_returnI _ w (by simp) (fun t ht => ⟨hst, H2, hp2, hw, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem ipf_spec (C : Ctx) (hok : CtxOK C) (hc : IpfCodes C) (s : AState) (hwf : LStoreWF s.store.ls) (hrd : RdOK s)
    (hSD : ∀ h u, s.store.view h = some (.sort u) → ∃ l, denoteL s.store.ls u = some l)
    (hLP : ∀ c ci, C.fe.find? c = some ci → ∃ ks, Frontend.denoteNList s.store.ns ci.toConstantVal.levelParams = some ks)
    (hLPl : ∀ c ci, C.fe.find? c = some ci → ci.toConstantVal.levelParams.length < 2 ^ 60)
    (hLS : ∀ us uh, s.store.lss.view us = some uh → ∃ vs, denoteLs s.store.lss us = some vs ∧ ∃ hl : vs.length = uh.length,
      ∀ j (hj : j < uh.length), denoteL s.store.ls uh[j] = some (vs[j]'(by rw [hl]; exact hj)))
    (hTB : ∀ T tb, C.fe.findTable? T = some tb → tb.bodies.size = tb.numFields) :
    ∀ (F : Nat) (e : EIdx) (H : List (BitVec 64)), C.H <+: H → F < 2 ^ 61 →
      SpecR (σ := σ) (Pre (ctxH C H) s (ipfParams.zip [BitVec.ofNat 64 F, Enc.idxW e])) (ipfBody C) s
        (isProofFast C.fe F e) (PostRB (ctxH C H) s) := by
  intro F e H hpH hF
  refine specR_prologue (postRB_locals _ s) (Knot.params_none _ ipfLocals ipfParams _ (by decide) (by decide)) ?_
  unfold isProofFast
  refine specR_callNIH (C := ctxH C H) ipfW fPq pqParams [vv ipfF, vv ipfE] (pqBody C)
    [BitVec.ofNat 64 F, Enc.idxW e] (by decide) rfl (by decide) hc.pq
    ⟨by simp +decide [Env.get, ipfParams, ctxEnv], by simp +decide [Env.get, ipfParams, ctxEnv], trivial⟩
    (PostSA (ctxH C H) s) (fun r_ w s' H' => RdStep s s' ∧ optPW C H' s r_ w)
    (fun r_ w s' st ⟨hst, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hst, hw⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pqParams _ rfl hlk)
      (pq_spec C hok hc.pqc s hwf hrd hSD hLP hLPl hLS hTB F e H hpH hF))
    (fun r w1 s1 H1 hp1 ⟨hst1, hw1⟩ => ?_)
  rcases r with _ | pw
  · simp only [optPW] at hw1; subst hw1
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨hst1, rfl, H1, hp1, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  simp only [optPW] at hw1
  cases pw with
  | never =>
    simp only [pwEnc] at hw1; subst hw1
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨hst1, by simp [ConLeche.PropWhen.isProp, boolW], H1, hp1, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | ifAllZero ps =>
    obtain ⟨o, ns, rfl, hb, hdn⟩ := hw1
    refine specR_atEntry fun t ht => ?_
    have hbig := cellA_big hok ht.sr (blkAt_lt hb)
    have hsm := blk_len_small hok ht.sr hb
    simp only [List.length_map] at hsm
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hbig.1) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hbig.2.1) (fun h => absurd rfl h) (fun _ => ?_)
    refine UD.specR_heapLoadI' (C := ctxH C H1) ipfL (vv ipfW) o (BitVec.ofNat 64 ns.length) (by have h0 := hb.1; simp only [List.length_map] at h0; exact h0) (by decide)
      (by simp; rfl) ?_
    have hl := (LSub.denoteNList_get _ _ _ hdn).1
    rcases ps with _ | ⟨p0, ps⟩
    · have hn0 : ns = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
      subst hn0
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ _ rfl (fun t ht => ⟨hst1, by simp [ConLeche.PropWhen.isProp, boolW], H1, hp1, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · have hne : BitVec.ofNat 64 ns.length ≠ 0 := by
        intro e0; have := congrArg BitVec.toNat e0; simp at hl; simp at this; omega
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_returnI _ _ rfl (fun t ht => ⟨hst1, by simp [ConLeche.PropWhen.isProp, boolW], H1, hp1, sr_of_eq ht.sr rfl rfl rfl rfl⟩)


theorem npf_spec (C : Ctx) (hok : CtxOK C) (hc : IpfCodes C) (s : AState) (hwf : LStoreWF s.store.ls) (hrd : RdOK s)
    (hSD : ∀ h u, s.store.view h = some (.sort u) → ∃ l, denoteL s.store.ls u = some l)
    (hLP : ∀ c ci, C.fe.find? c = some ci → ∃ ks, Frontend.denoteNList s.store.ns ci.toConstantVal.levelParams = some ks)
    (hLPl : ∀ c ci, C.fe.find? c = some ci → ci.toConstantVal.levelParams.length < 2 ^ 60)
    (hLS : ∀ us uh, s.store.lss.view us = some uh → ∃ vs, denoteLs s.store.lss us = some vs ∧ ∃ hl : vs.length = uh.length,
      ∀ j (hj : j < uh.length), denoteL s.store.ls uh[j] = some (vs[j]'(by rw [hl]; exact hj)))
    (hTB : ∀ T tb, C.fe.findTable? T = some tb → tb.bodies.size = tb.numFields) :
    ∀ (F : Nat) (e : EIdx) (H : List (BitVec 64)), C.H <+: H → F < 2 ^ 61 →
      SpecR (σ := σ) (Pre (ctxH C H) s (npfParams.zip [BitVec.ofNat 64 F, Enc.idxW e])) (npfBody C) s
        (notProofFast C.fe F e) (PostRB (ctxH C H) s) := by
  intro F e H hpH hF
  refine specR_prologue (postRB_locals _ s) (Knot.params_none _ npfLocals npfParams _ (by decide) (by decide)) ?_
  unfold notProofFast
  refine specR_callNIH (C := ctxH C H) npfW fPq pqParams [vv npfF, vv npfE] (pqBody C)
    [BitVec.ofNat 64 F, Enc.idxW e] (by decide) rfl (by decide) hc.pq
    ⟨by simp +decide [Env.get, npfParams, ctxEnv], by simp +decide [Env.get, npfParams, ctxEnv], trivial⟩
    (PostSA (ctxH C H) s) (fun r_ w s' H' => RdStep s s' ∧ optPW C H' s r_ w)
    (fun r_ w s' st ⟨hst, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hst, hw⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pqParams _ rfl hlk)
      (pq_spec C hok hc.pqc s hwf hrd hSD hLP hLPl hLS hTB F e H hpH hF))
    (fun r w1 s1 H1 hp1 ⟨hst1, hw1⟩ => ?_)
  rcases r with _ | pw
  · simp only [optPW] at hw1; subst hw1
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨hst1, rfl, H1, hp1, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  simp only [optPW] at hw1
  cases pw with
  | never =>
    simp only [pwEnc] at hw1; subst hw1
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 1 rfl (fun t ht => ⟨hst1, by simp [ConLeche.PropWhen.isProp, boolW], H1, hp1, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | ifAllZero ps =>
    obtain ⟨o, ns, rfl, hb, hdn⟩ := hw1
    refine specR_atEntry fun t ht => ?_
    have hbig := cellA_big hok ht.sr (blkAt_lt hb)
    have hsm := blk_len_small hok ht.sr hb
    simp only [List.length_map] at hsm
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hbig.1) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hbig.2.1) (fun h => absurd rfl h) (fun _ => ?_)
    refine UD.specR_heapLoadI' (C := ctxH C H1) npfL (vv npfW) o (BitVec.ofNat 64 ns.length) (by have h0 := hb.1; simp only [List.length_map] at h0; exact h0) (by decide)
      (by simp; rfl) ?_
    have hl := (LSub.denoteNList_get _ _ _ hdn).1
    rcases ps with _ | ⟨p0, ps⟩
    · have hn0 : ns = [] := List.eq_nil_of_length_eq_zero (by simpa using hl.symm)
      subst hn0
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ _ rfl (fun t ht => ⟨hst1, by simp [ConLeche.PropWhen.isProp, boolW], H1, hp1, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · have hne : BitVec.ofNat 64 ns.length ≠ 0 := by
        intro e0; have := congrArg BitVec.toNat e0; simp at hl; simp at this; omega
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_returnI _ _ rfl (fun t ht => ⟨hst1, by simp [ConLeche.PropWhen.isProp, boolW], H1, hp1, sr_of_eq ht.sr rfl rfl rfl rfl⟩)


end

end ConPanqueque.T.WC
