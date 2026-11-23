import ConPanqueque.T.Core.Rescue
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# The rescue's K branch (`to_cnstr_when_K`)

The major's type (`inferIO`, `whnf`) headed by the family's constant at the constructor's level arity; the
constructor applied to the type's leading arguments; the scope guard (`fabScopeOk`, a callee), the type check
(`defeq` against the fabrication's type), and at the verified mode the proof-irrelevance certificate.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def kq1 := ofString "kq1"
def kqTm := ofString "kqtm"
def kqHh := ofString "kqhh"
def kqTp := ofString "kqtp"
def kqUs := ofString "kqus"
def kqLp := ofString "kqlp"
def kqLl := ofString "kqll"
def kqTa := ofString "kqta"
def kqTl := ofString "kqtl"
def kqNp := ofString "kqnp"
def kqRc := ofString "kqrc"
def kqHd := ofString "kqhd"
def kqFab := ofString "kqfab"
def kqFs := ofString "kqfs"
def kqK2 := ofString "kqk2"
def kqDf := ofString "kqdf"
def kqIr := ofString "kqir"
def fFab := ofString "fabScopeOk"
def fbF := ofString "fbf"
def fbM := ofString "fbm"
def fbParams : List MlS := [kD, fbF, fbM]

@[simp] theorem kq_kq1_ne_kqTm : kq1 ≠ kqTm := by decide
@[simp] theorem kq_kq1_ne_kqHh : kq1 ≠ kqHh := by decide
@[simp] theorem kq_kq1_ne_kqTp : kq1 ≠ kqTp := by decide
@[simp] theorem kq_kq1_ne_kqUs : kq1 ≠ kqUs := by decide
@[simp] theorem kq_kq1_ne_kqLp : kq1 ≠ kqLp := by decide
@[simp] theorem kq_kq1_ne_kqLl : kq1 ≠ kqLl := by decide
@[simp] theorem kq_kq1_ne_kqTa : kq1 ≠ kqTa := by decide
@[simp] theorem kq_kq1_ne_kqTl : kq1 ≠ kqTl := by decide
@[simp] theorem kq_kq1_ne_kqNp : kq1 ≠ kqNp := by decide
@[simp] theorem kq_kq1_ne_kqRc : kq1 ≠ kqRc := by decide
@[simp] theorem kq_kq1_ne_kqHd : kq1 ≠ kqHd := by decide
@[simp] theorem kq_kq1_ne_kqFab : kq1 ≠ kqFab := by decide
@[simp] theorem kq_kq1_ne_kqFs : kq1 ≠ kqFs := by decide
@[simp] theorem kq_kq1_ne_kqK2 : kq1 ≠ kqK2 := by decide
@[simp] theorem kq_kq1_ne_kqDf : kq1 ≠ kqDf := by decide
@[simp] theorem kq_kq1_ne_kqIr : kq1 ≠ kqIr := by decide
@[simp] theorem kq_kq1_ne_lFl : kq1 ≠ lFl := by decide
@[simp] theorem kq_lFl_ne_kq1 : lFl ≠ kq1 := by decide
@[simp] theorem kq_kq1_ne_lDh : kq1 ≠ lDh := by decide
@[simp] theorem kq_lDh_ne_kq1 : lDh ≠ kq1 := by decide
@[simp] theorem kq_kq1_ne_lDt : kq1 ≠ lDt := by decide
@[simp] theorem kq_lDt_ne_kq1 : lDt ≠ kq1 := by decide
@[simp] theorem kq_kq1_ne_lDg : kq1 ≠ lDg := by decide
@[simp] theorem kq_lDg_ne_kq1 : lDg ≠ kq1 := by decide
@[simp] theorem kq_kq1_ne_lDi : kq1 ≠ lDi := by decide
@[simp] theorem kq_lDi_ne_kq1 : lDi ≠ kq1 := by decide
@[simp] theorem kq_kq1_ne_lRp : kq1 ≠ lRp := by decide
@[simp] theorem kq_lRp_ne_kq1 : lRp ≠ kq1 := by decide
@[simp] theorem kq_kq1_ne_lRn : kq1 ≠ lRn := by decide
@[simp] theorem kq_lRn_ne_kq1 : lRn ≠ kq1 := by decide
@[simp] theorem kq_kq1_ne_lFle : kq1 ≠ lFle := by decide
@[simp] theorem kq_lFle_ne_kq1 : lFle ≠ kq1 := by decide
@[simp] theorem kq_kq1_ne_lFls : kq1 ≠ lFls := by decide
@[simp] theorem kq_lFls_ne_kq1 : lFls ≠ kq1 := by decide
@[simp] theorem kq_kq1_ne_lDir : kq1 ≠ lDir := by decide
@[simp] theorem kq_lDir_ne_kq1 : lDir ≠ kq1 := by decide
@[simp] theorem kq_kq1_ne_lKb : kq1 ≠ lKb := by decide
@[simp] theorem kq_lKb_ne_kq1 : lKb ≠ kq1 := by decide
@[simp] theorem kq_kq1_ne_kFu : kq1 ≠ kFu := by decide
@[simp] theorem kq_kFu_ne_kq1 : kFu ≠ kq1 := by decide
@[simp] theorem kq_kq1_ne_kD : kq1 ≠ kD := by decide
@[simp] theorem kq_kD_ne_kq1 : kD ≠ kq1 := by decide
@[simp] theorem kq_kq1_ne_rkR : kq1 ≠ rkR := by decide
@[simp] theorem kq_rkR_ne_kq1 : rkR ≠ kq1 := by decide
@[simp] theorem kq_kq1_ne_rkJ : kq1 ≠ rkJ := by decide
@[simp] theorem kq_rkJ_ne_kq1 : rkJ ≠ kq1 := by decide
@[simp] theorem kq_kq1_ne_rkT : kq1 ≠ rkT := by decide
@[simp] theorem kq_rkT_ne_kq1 : rkT ≠ kq1 := by decide
@[simp] theorem kq_kq1_ne_rkM : kq1 ≠ rkM := by decide
@[simp] theorem kq_rkM_ne_kq1 : rkM ≠ kq1 := by decide
@[simp] theorem kq_kqTm_ne_kq1 : kqTm ≠ kq1 := by decide
@[simp] theorem kq_kqTm_ne_kqHh : kqTm ≠ kqHh := by decide
@[simp] theorem kq_kqTm_ne_kqTp : kqTm ≠ kqTp := by decide
@[simp] theorem kq_kqTm_ne_kqUs : kqTm ≠ kqUs := by decide
@[simp] theorem kq_kqTm_ne_kqLp : kqTm ≠ kqLp := by decide
@[simp] theorem kq_kqTm_ne_kqLl : kqTm ≠ kqLl := by decide
@[simp] theorem kq_kqTm_ne_kqTa : kqTm ≠ kqTa := by decide
@[simp] theorem kq_kqTm_ne_kqTl : kqTm ≠ kqTl := by decide
@[simp] theorem kq_kqTm_ne_kqNp : kqTm ≠ kqNp := by decide
@[simp] theorem kq_kqTm_ne_kqRc : kqTm ≠ kqRc := by decide
@[simp] theorem kq_kqTm_ne_kqHd : kqTm ≠ kqHd := by decide
@[simp] theorem kq_kqTm_ne_kqFab : kqTm ≠ kqFab := by decide
@[simp] theorem kq_kqTm_ne_kqFs : kqTm ≠ kqFs := by decide
@[simp] theorem kq_kqTm_ne_kqK2 : kqTm ≠ kqK2 := by decide
@[simp] theorem kq_kqTm_ne_kqDf : kqTm ≠ kqDf := by decide
@[simp] theorem kq_kqTm_ne_kqIr : kqTm ≠ kqIr := by decide
@[simp] theorem kq_kqTm_ne_lFl : kqTm ≠ lFl := by decide
@[simp] theorem kq_lFl_ne_kqTm : lFl ≠ kqTm := by decide
@[simp] theorem kq_kqTm_ne_lDh : kqTm ≠ lDh := by decide
@[simp] theorem kq_lDh_ne_kqTm : lDh ≠ kqTm := by decide
@[simp] theorem kq_kqTm_ne_lDt : kqTm ≠ lDt := by decide
@[simp] theorem kq_lDt_ne_kqTm : lDt ≠ kqTm := by decide
@[simp] theorem kq_kqTm_ne_lDg : kqTm ≠ lDg := by decide
@[simp] theorem kq_lDg_ne_kqTm : lDg ≠ kqTm := by decide
@[simp] theorem kq_kqTm_ne_lDi : kqTm ≠ lDi := by decide
@[simp] theorem kq_lDi_ne_kqTm : lDi ≠ kqTm := by decide
@[simp] theorem kq_kqTm_ne_lRp : kqTm ≠ lRp := by decide
@[simp] theorem kq_lRp_ne_kqTm : lRp ≠ kqTm := by decide
@[simp] theorem kq_kqTm_ne_lRn : kqTm ≠ lRn := by decide
@[simp] theorem kq_lRn_ne_kqTm : lRn ≠ kqTm := by decide
@[simp] theorem kq_kqTm_ne_lFle : kqTm ≠ lFle := by decide
@[simp] theorem kq_lFle_ne_kqTm : lFle ≠ kqTm := by decide
@[simp] theorem kq_kqTm_ne_lFls : kqTm ≠ lFls := by decide
@[simp] theorem kq_lFls_ne_kqTm : lFls ≠ kqTm := by decide
@[simp] theorem kq_kqTm_ne_lDir : kqTm ≠ lDir := by decide
@[simp] theorem kq_lDir_ne_kqTm : lDir ≠ kqTm := by decide
@[simp] theorem kq_kqTm_ne_lKb : kqTm ≠ lKb := by decide
@[simp] theorem kq_lKb_ne_kqTm : lKb ≠ kqTm := by decide
@[simp] theorem kq_kqTm_ne_kFu : kqTm ≠ kFu := by decide
@[simp] theorem kq_kFu_ne_kqTm : kFu ≠ kqTm := by decide
@[simp] theorem kq_kqTm_ne_kD : kqTm ≠ kD := by decide
@[simp] theorem kq_kD_ne_kqTm : kD ≠ kqTm := by decide
@[simp] theorem kq_kqTm_ne_rkR : kqTm ≠ rkR := by decide
@[simp] theorem kq_rkR_ne_kqTm : rkR ≠ kqTm := by decide
@[simp] theorem kq_kqTm_ne_rkJ : kqTm ≠ rkJ := by decide
@[simp] theorem kq_rkJ_ne_kqTm : rkJ ≠ kqTm := by decide
@[simp] theorem kq_kqTm_ne_rkT : kqTm ≠ rkT := by decide
@[simp] theorem kq_rkT_ne_kqTm : rkT ≠ kqTm := by decide
@[simp] theorem kq_kqTm_ne_rkM : kqTm ≠ rkM := by decide
@[simp] theorem kq_rkM_ne_kqTm : rkM ≠ kqTm := by decide
@[simp] theorem kq_kqHh_ne_kq1 : kqHh ≠ kq1 := by decide
@[simp] theorem kq_kqHh_ne_kqTm : kqHh ≠ kqTm := by decide
@[simp] theorem kq_kqHh_ne_kqTp : kqHh ≠ kqTp := by decide
@[simp] theorem kq_kqHh_ne_kqUs : kqHh ≠ kqUs := by decide
@[simp] theorem kq_kqHh_ne_kqLp : kqHh ≠ kqLp := by decide
@[simp] theorem kq_kqHh_ne_kqLl : kqHh ≠ kqLl := by decide
@[simp] theorem kq_kqHh_ne_kqTa : kqHh ≠ kqTa := by decide
@[simp] theorem kq_kqHh_ne_kqTl : kqHh ≠ kqTl := by decide
@[simp] theorem kq_kqHh_ne_kqNp : kqHh ≠ kqNp := by decide
@[simp] theorem kq_kqHh_ne_kqRc : kqHh ≠ kqRc := by decide
@[simp] theorem kq_kqHh_ne_kqHd : kqHh ≠ kqHd := by decide
@[simp] theorem kq_kqHh_ne_kqFab : kqHh ≠ kqFab := by decide
@[simp] theorem kq_kqHh_ne_kqFs : kqHh ≠ kqFs := by decide
@[simp] theorem kq_kqHh_ne_kqK2 : kqHh ≠ kqK2 := by decide
@[simp] theorem kq_kqHh_ne_kqDf : kqHh ≠ kqDf := by decide
@[simp] theorem kq_kqHh_ne_kqIr : kqHh ≠ kqIr := by decide
@[simp] theorem kq_kqHh_ne_lFl : kqHh ≠ lFl := by decide
@[simp] theorem kq_lFl_ne_kqHh : lFl ≠ kqHh := by decide
@[simp] theorem kq_kqHh_ne_lDh : kqHh ≠ lDh := by decide
@[simp] theorem kq_lDh_ne_kqHh : lDh ≠ kqHh := by decide
@[simp] theorem kq_kqHh_ne_lDt : kqHh ≠ lDt := by decide
@[simp] theorem kq_lDt_ne_kqHh : lDt ≠ kqHh := by decide
@[simp] theorem kq_kqHh_ne_lDg : kqHh ≠ lDg := by decide
@[simp] theorem kq_lDg_ne_kqHh : lDg ≠ kqHh := by decide
@[simp] theorem kq_kqHh_ne_lDi : kqHh ≠ lDi := by decide
@[simp] theorem kq_lDi_ne_kqHh : lDi ≠ kqHh := by decide
@[simp] theorem kq_kqHh_ne_lRp : kqHh ≠ lRp := by decide
@[simp] theorem kq_lRp_ne_kqHh : lRp ≠ kqHh := by decide
@[simp] theorem kq_kqHh_ne_lRn : kqHh ≠ lRn := by decide
@[simp] theorem kq_lRn_ne_kqHh : lRn ≠ kqHh := by decide
@[simp] theorem kq_kqHh_ne_lFle : kqHh ≠ lFle := by decide
@[simp] theorem kq_lFle_ne_kqHh : lFle ≠ kqHh := by decide
@[simp] theorem kq_kqHh_ne_lFls : kqHh ≠ lFls := by decide
@[simp] theorem kq_lFls_ne_kqHh : lFls ≠ kqHh := by decide
@[simp] theorem kq_kqHh_ne_lDir : kqHh ≠ lDir := by decide
@[simp] theorem kq_lDir_ne_kqHh : lDir ≠ kqHh := by decide
@[simp] theorem kq_kqHh_ne_lKb : kqHh ≠ lKb := by decide
@[simp] theorem kq_lKb_ne_kqHh : lKb ≠ kqHh := by decide
@[simp] theorem kq_kqHh_ne_kFu : kqHh ≠ kFu := by decide
@[simp] theorem kq_kFu_ne_kqHh : kFu ≠ kqHh := by decide
@[simp] theorem kq_kqHh_ne_kD : kqHh ≠ kD := by decide
@[simp] theorem kq_kD_ne_kqHh : kD ≠ kqHh := by decide
@[simp] theorem kq_kqHh_ne_rkR : kqHh ≠ rkR := by decide
@[simp] theorem kq_rkR_ne_kqHh : rkR ≠ kqHh := by decide
@[simp] theorem kq_kqHh_ne_rkJ : kqHh ≠ rkJ := by decide
@[simp] theorem kq_rkJ_ne_kqHh : rkJ ≠ kqHh := by decide
@[simp] theorem kq_kqHh_ne_rkT : kqHh ≠ rkT := by decide
@[simp] theorem kq_rkT_ne_kqHh : rkT ≠ kqHh := by decide
@[simp] theorem kq_kqHh_ne_rkM : kqHh ≠ rkM := by decide
@[simp] theorem kq_rkM_ne_kqHh : rkM ≠ kqHh := by decide
@[simp] theorem kq_kqTp_ne_kq1 : kqTp ≠ kq1 := by decide
@[simp] theorem kq_kqTp_ne_kqTm : kqTp ≠ kqTm := by decide
@[simp] theorem kq_kqTp_ne_kqHh : kqTp ≠ kqHh := by decide
@[simp] theorem kq_kqTp_ne_kqUs : kqTp ≠ kqUs := by decide
@[simp] theorem kq_kqTp_ne_kqLp : kqTp ≠ kqLp := by decide
@[simp] theorem kq_kqTp_ne_kqLl : kqTp ≠ kqLl := by decide
@[simp] theorem kq_kqTp_ne_kqTa : kqTp ≠ kqTa := by decide
@[simp] theorem kq_kqTp_ne_kqTl : kqTp ≠ kqTl := by decide
@[simp] theorem kq_kqTp_ne_kqNp : kqTp ≠ kqNp := by decide
@[simp] theorem kq_kqTp_ne_kqRc : kqTp ≠ kqRc := by decide
@[simp] theorem kq_kqTp_ne_kqHd : kqTp ≠ kqHd := by decide
@[simp] theorem kq_kqTp_ne_kqFab : kqTp ≠ kqFab := by decide
@[simp] theorem kq_kqTp_ne_kqFs : kqTp ≠ kqFs := by decide
@[simp] theorem kq_kqTp_ne_kqK2 : kqTp ≠ kqK2 := by decide
@[simp] theorem kq_kqTp_ne_kqDf : kqTp ≠ kqDf := by decide
@[simp] theorem kq_kqTp_ne_kqIr : kqTp ≠ kqIr := by decide
@[simp] theorem kq_kqTp_ne_lFl : kqTp ≠ lFl := by decide
@[simp] theorem kq_lFl_ne_kqTp : lFl ≠ kqTp := by decide
@[simp] theorem kq_kqTp_ne_lDh : kqTp ≠ lDh := by decide
@[simp] theorem kq_lDh_ne_kqTp : lDh ≠ kqTp := by decide
@[simp] theorem kq_kqTp_ne_lDt : kqTp ≠ lDt := by decide
@[simp] theorem kq_lDt_ne_kqTp : lDt ≠ kqTp := by decide
@[simp] theorem kq_kqTp_ne_lDg : kqTp ≠ lDg := by decide
@[simp] theorem kq_lDg_ne_kqTp : lDg ≠ kqTp := by decide
@[simp] theorem kq_kqTp_ne_lDi : kqTp ≠ lDi := by decide
@[simp] theorem kq_lDi_ne_kqTp : lDi ≠ kqTp := by decide
@[simp] theorem kq_kqTp_ne_lRp : kqTp ≠ lRp := by decide
@[simp] theorem kq_lRp_ne_kqTp : lRp ≠ kqTp := by decide
@[simp] theorem kq_kqTp_ne_lRn : kqTp ≠ lRn := by decide
@[simp] theorem kq_lRn_ne_kqTp : lRn ≠ kqTp := by decide
@[simp] theorem kq_kqTp_ne_lFle : kqTp ≠ lFle := by decide
@[simp] theorem kq_lFle_ne_kqTp : lFle ≠ kqTp := by decide
@[simp] theorem kq_kqTp_ne_lFls : kqTp ≠ lFls := by decide
@[simp] theorem kq_lFls_ne_kqTp : lFls ≠ kqTp := by decide
@[simp] theorem kq_kqTp_ne_lDir : kqTp ≠ lDir := by decide
@[simp] theorem kq_lDir_ne_kqTp : lDir ≠ kqTp := by decide
@[simp] theorem kq_kqTp_ne_lKb : kqTp ≠ lKb := by decide
@[simp] theorem kq_lKb_ne_kqTp : lKb ≠ kqTp := by decide
@[simp] theorem kq_kqTp_ne_kFu : kqTp ≠ kFu := by decide
@[simp] theorem kq_kFu_ne_kqTp : kFu ≠ kqTp := by decide
@[simp] theorem kq_kqTp_ne_kD : kqTp ≠ kD := by decide
@[simp] theorem kq_kD_ne_kqTp : kD ≠ kqTp := by decide
@[simp] theorem kq_kqTp_ne_rkR : kqTp ≠ rkR := by decide
@[simp] theorem kq_rkR_ne_kqTp : rkR ≠ kqTp := by decide
@[simp] theorem kq_kqTp_ne_rkJ : kqTp ≠ rkJ := by decide
@[simp] theorem kq_rkJ_ne_kqTp : rkJ ≠ kqTp := by decide
@[simp] theorem kq_kqTp_ne_rkT : kqTp ≠ rkT := by decide
@[simp] theorem kq_rkT_ne_kqTp : rkT ≠ kqTp := by decide
@[simp] theorem kq_kqTp_ne_rkM : kqTp ≠ rkM := by decide
@[simp] theorem kq_rkM_ne_kqTp : rkM ≠ kqTp := by decide
@[simp] theorem kq_kqUs_ne_kq1 : kqUs ≠ kq1 := by decide
@[simp] theorem kq_kqUs_ne_kqTm : kqUs ≠ kqTm := by decide
@[simp] theorem kq_kqUs_ne_kqHh : kqUs ≠ kqHh := by decide
@[simp] theorem kq_kqUs_ne_kqTp : kqUs ≠ kqTp := by decide
@[simp] theorem kq_kqUs_ne_kqLp : kqUs ≠ kqLp := by decide
@[simp] theorem kq_kqUs_ne_kqLl : kqUs ≠ kqLl := by decide
@[simp] theorem kq_kqUs_ne_kqTa : kqUs ≠ kqTa := by decide
@[simp] theorem kq_kqUs_ne_kqTl : kqUs ≠ kqTl := by decide
@[simp] theorem kq_kqUs_ne_kqNp : kqUs ≠ kqNp := by decide
@[simp] theorem kq_kqUs_ne_kqRc : kqUs ≠ kqRc := by decide
@[simp] theorem kq_kqUs_ne_kqHd : kqUs ≠ kqHd := by decide
@[simp] theorem kq_kqUs_ne_kqFab : kqUs ≠ kqFab := by decide
@[simp] theorem kq_kqUs_ne_kqFs : kqUs ≠ kqFs := by decide
@[simp] theorem kq_kqUs_ne_kqK2 : kqUs ≠ kqK2 := by decide
@[simp] theorem kq_kqUs_ne_kqDf : kqUs ≠ kqDf := by decide
@[simp] theorem kq_kqUs_ne_kqIr : kqUs ≠ kqIr := by decide
@[simp] theorem kq_kqUs_ne_lFl : kqUs ≠ lFl := by decide
@[simp] theorem kq_lFl_ne_kqUs : lFl ≠ kqUs := by decide
@[simp] theorem kq_kqUs_ne_lDh : kqUs ≠ lDh := by decide
@[simp] theorem kq_lDh_ne_kqUs : lDh ≠ kqUs := by decide
@[simp] theorem kq_kqUs_ne_lDt : kqUs ≠ lDt := by decide
@[simp] theorem kq_lDt_ne_kqUs : lDt ≠ kqUs := by decide
@[simp] theorem kq_kqUs_ne_lDg : kqUs ≠ lDg := by decide
@[simp] theorem kq_lDg_ne_kqUs : lDg ≠ kqUs := by decide
@[simp] theorem kq_kqUs_ne_lDi : kqUs ≠ lDi := by decide
@[simp] theorem kq_lDi_ne_kqUs : lDi ≠ kqUs := by decide
@[simp] theorem kq_kqUs_ne_lRp : kqUs ≠ lRp := by decide
@[simp] theorem kq_lRp_ne_kqUs : lRp ≠ kqUs := by decide
@[simp] theorem kq_kqUs_ne_lRn : kqUs ≠ lRn := by decide
@[simp] theorem kq_lRn_ne_kqUs : lRn ≠ kqUs := by decide
@[simp] theorem kq_kqUs_ne_lFle : kqUs ≠ lFle := by decide
@[simp] theorem kq_lFle_ne_kqUs : lFle ≠ kqUs := by decide
@[simp] theorem kq_kqUs_ne_lFls : kqUs ≠ lFls := by decide
@[simp] theorem kq_lFls_ne_kqUs : lFls ≠ kqUs := by decide
@[simp] theorem kq_kqUs_ne_lDir : kqUs ≠ lDir := by decide
@[simp] theorem kq_lDir_ne_kqUs : lDir ≠ kqUs := by decide
@[simp] theorem kq_kqUs_ne_lKb : kqUs ≠ lKb := by decide
@[simp] theorem kq_lKb_ne_kqUs : lKb ≠ kqUs := by decide
@[simp] theorem kq_kqUs_ne_kFu : kqUs ≠ kFu := by decide
@[simp] theorem kq_kFu_ne_kqUs : kFu ≠ kqUs := by decide
@[simp] theorem kq_kqUs_ne_kD : kqUs ≠ kD := by decide
@[simp] theorem kq_kD_ne_kqUs : kD ≠ kqUs := by decide
@[simp] theorem kq_kqUs_ne_rkR : kqUs ≠ rkR := by decide
@[simp] theorem kq_rkR_ne_kqUs : rkR ≠ kqUs := by decide
@[simp] theorem kq_kqUs_ne_rkJ : kqUs ≠ rkJ := by decide
@[simp] theorem kq_rkJ_ne_kqUs : rkJ ≠ kqUs := by decide
@[simp] theorem kq_kqUs_ne_rkT : kqUs ≠ rkT := by decide
@[simp] theorem kq_rkT_ne_kqUs : rkT ≠ kqUs := by decide
@[simp] theorem kq_kqUs_ne_rkM : kqUs ≠ rkM := by decide
@[simp] theorem kq_rkM_ne_kqUs : rkM ≠ kqUs := by decide
@[simp] theorem kq_kqLp_ne_kq1 : kqLp ≠ kq1 := by decide
@[simp] theorem kq_kqLp_ne_kqTm : kqLp ≠ kqTm := by decide
@[simp] theorem kq_kqLp_ne_kqHh : kqLp ≠ kqHh := by decide
@[simp] theorem kq_kqLp_ne_kqTp : kqLp ≠ kqTp := by decide
@[simp] theorem kq_kqLp_ne_kqUs : kqLp ≠ kqUs := by decide
@[simp] theorem kq_kqLp_ne_kqLl : kqLp ≠ kqLl := by decide
@[simp] theorem kq_kqLp_ne_kqTa : kqLp ≠ kqTa := by decide
@[simp] theorem kq_kqLp_ne_kqTl : kqLp ≠ kqTl := by decide
@[simp] theorem kq_kqLp_ne_kqNp : kqLp ≠ kqNp := by decide
@[simp] theorem kq_kqLp_ne_kqRc : kqLp ≠ kqRc := by decide
@[simp] theorem kq_kqLp_ne_kqHd : kqLp ≠ kqHd := by decide
@[simp] theorem kq_kqLp_ne_kqFab : kqLp ≠ kqFab := by decide
@[simp] theorem kq_kqLp_ne_kqFs : kqLp ≠ kqFs := by decide
@[simp] theorem kq_kqLp_ne_kqK2 : kqLp ≠ kqK2 := by decide
@[simp] theorem kq_kqLp_ne_kqDf : kqLp ≠ kqDf := by decide
@[simp] theorem kq_kqLp_ne_kqIr : kqLp ≠ kqIr := by decide
@[simp] theorem kq_kqLp_ne_lFl : kqLp ≠ lFl := by decide
@[simp] theorem kq_lFl_ne_kqLp : lFl ≠ kqLp := by decide
@[simp] theorem kq_kqLp_ne_lDh : kqLp ≠ lDh := by decide
@[simp] theorem kq_lDh_ne_kqLp : lDh ≠ kqLp := by decide
@[simp] theorem kq_kqLp_ne_lDt : kqLp ≠ lDt := by decide
@[simp] theorem kq_lDt_ne_kqLp : lDt ≠ kqLp := by decide
@[simp] theorem kq_kqLp_ne_lDg : kqLp ≠ lDg := by decide
@[simp] theorem kq_lDg_ne_kqLp : lDg ≠ kqLp := by decide
@[simp] theorem kq_kqLp_ne_lDi : kqLp ≠ lDi := by decide
@[simp] theorem kq_lDi_ne_kqLp : lDi ≠ kqLp := by decide
@[simp] theorem kq_kqLp_ne_lRp : kqLp ≠ lRp := by decide
@[simp] theorem kq_lRp_ne_kqLp : lRp ≠ kqLp := by decide
@[simp] theorem kq_kqLp_ne_lRn : kqLp ≠ lRn := by decide
@[simp] theorem kq_lRn_ne_kqLp : lRn ≠ kqLp := by decide
@[simp] theorem kq_kqLp_ne_lFle : kqLp ≠ lFle := by decide
@[simp] theorem kq_lFle_ne_kqLp : lFle ≠ kqLp := by decide
@[simp] theorem kq_kqLp_ne_lFls : kqLp ≠ lFls := by decide
@[simp] theorem kq_lFls_ne_kqLp : lFls ≠ kqLp := by decide
@[simp] theorem kq_kqLp_ne_lDir : kqLp ≠ lDir := by decide
@[simp] theorem kq_lDir_ne_kqLp : lDir ≠ kqLp := by decide
@[simp] theorem kq_kqLp_ne_lKb : kqLp ≠ lKb := by decide
@[simp] theorem kq_lKb_ne_kqLp : lKb ≠ kqLp := by decide
@[simp] theorem kq_kqLp_ne_kFu : kqLp ≠ kFu := by decide
@[simp] theorem kq_kFu_ne_kqLp : kFu ≠ kqLp := by decide
@[simp] theorem kq_kqLp_ne_kD : kqLp ≠ kD := by decide
@[simp] theorem kq_kD_ne_kqLp : kD ≠ kqLp := by decide
@[simp] theorem kq_kqLp_ne_rkR : kqLp ≠ rkR := by decide
@[simp] theorem kq_rkR_ne_kqLp : rkR ≠ kqLp := by decide
@[simp] theorem kq_kqLp_ne_rkJ : kqLp ≠ rkJ := by decide
@[simp] theorem kq_rkJ_ne_kqLp : rkJ ≠ kqLp := by decide
@[simp] theorem kq_kqLp_ne_rkT : kqLp ≠ rkT := by decide
@[simp] theorem kq_rkT_ne_kqLp : rkT ≠ kqLp := by decide
@[simp] theorem kq_kqLp_ne_rkM : kqLp ≠ rkM := by decide
@[simp] theorem kq_rkM_ne_kqLp : rkM ≠ kqLp := by decide
@[simp] theorem kq_kqLl_ne_kq1 : kqLl ≠ kq1 := by decide
@[simp] theorem kq_kqLl_ne_kqTm : kqLl ≠ kqTm := by decide
@[simp] theorem kq_kqLl_ne_kqHh : kqLl ≠ kqHh := by decide
@[simp] theorem kq_kqLl_ne_kqTp : kqLl ≠ kqTp := by decide
@[simp] theorem kq_kqLl_ne_kqUs : kqLl ≠ kqUs := by decide
@[simp] theorem kq_kqLl_ne_kqLp : kqLl ≠ kqLp := by decide
@[simp] theorem kq_kqLl_ne_kqTa : kqLl ≠ kqTa := by decide
@[simp] theorem kq_kqLl_ne_kqTl : kqLl ≠ kqTl := by decide
@[simp] theorem kq_kqLl_ne_kqNp : kqLl ≠ kqNp := by decide
@[simp] theorem kq_kqLl_ne_kqRc : kqLl ≠ kqRc := by decide
@[simp] theorem kq_kqLl_ne_kqHd : kqLl ≠ kqHd := by decide
@[simp] theorem kq_kqLl_ne_kqFab : kqLl ≠ kqFab := by decide
@[simp] theorem kq_kqLl_ne_kqFs : kqLl ≠ kqFs := by decide
@[simp] theorem kq_kqLl_ne_kqK2 : kqLl ≠ kqK2 := by decide
@[simp] theorem kq_kqLl_ne_kqDf : kqLl ≠ kqDf := by decide
@[simp] theorem kq_kqLl_ne_kqIr : kqLl ≠ kqIr := by decide
@[simp] theorem kq_kqLl_ne_lFl : kqLl ≠ lFl := by decide
@[simp] theorem kq_lFl_ne_kqLl : lFl ≠ kqLl := by decide
@[simp] theorem kq_kqLl_ne_lDh : kqLl ≠ lDh := by decide
@[simp] theorem kq_lDh_ne_kqLl : lDh ≠ kqLl := by decide
@[simp] theorem kq_kqLl_ne_lDt : kqLl ≠ lDt := by decide
@[simp] theorem kq_lDt_ne_kqLl : lDt ≠ kqLl := by decide
@[simp] theorem kq_kqLl_ne_lDg : kqLl ≠ lDg := by decide
@[simp] theorem kq_lDg_ne_kqLl : lDg ≠ kqLl := by decide
@[simp] theorem kq_kqLl_ne_lDi : kqLl ≠ lDi := by decide
@[simp] theorem kq_lDi_ne_kqLl : lDi ≠ kqLl := by decide
@[simp] theorem kq_kqLl_ne_lRp : kqLl ≠ lRp := by decide
@[simp] theorem kq_lRp_ne_kqLl : lRp ≠ kqLl := by decide
@[simp] theorem kq_kqLl_ne_lRn : kqLl ≠ lRn := by decide
@[simp] theorem kq_lRn_ne_kqLl : lRn ≠ kqLl := by decide
@[simp] theorem kq_kqLl_ne_lFle : kqLl ≠ lFle := by decide
@[simp] theorem kq_lFle_ne_kqLl : lFle ≠ kqLl := by decide
@[simp] theorem kq_kqLl_ne_lFls : kqLl ≠ lFls := by decide
@[simp] theorem kq_lFls_ne_kqLl : lFls ≠ kqLl := by decide
@[simp] theorem kq_kqLl_ne_lDir : kqLl ≠ lDir := by decide
@[simp] theorem kq_lDir_ne_kqLl : lDir ≠ kqLl := by decide
@[simp] theorem kq_kqLl_ne_lKb : kqLl ≠ lKb := by decide
@[simp] theorem kq_lKb_ne_kqLl : lKb ≠ kqLl := by decide
@[simp] theorem kq_kqLl_ne_kFu : kqLl ≠ kFu := by decide
@[simp] theorem kq_kFu_ne_kqLl : kFu ≠ kqLl := by decide
@[simp] theorem kq_kqLl_ne_kD : kqLl ≠ kD := by decide
@[simp] theorem kq_kD_ne_kqLl : kD ≠ kqLl := by decide
@[simp] theorem kq_kqLl_ne_rkR : kqLl ≠ rkR := by decide
@[simp] theorem kq_rkR_ne_kqLl : rkR ≠ kqLl := by decide
@[simp] theorem kq_kqLl_ne_rkJ : kqLl ≠ rkJ := by decide
@[simp] theorem kq_rkJ_ne_kqLl : rkJ ≠ kqLl := by decide
@[simp] theorem kq_kqLl_ne_rkT : kqLl ≠ rkT := by decide
@[simp] theorem kq_rkT_ne_kqLl : rkT ≠ kqLl := by decide
@[simp] theorem kq_kqLl_ne_rkM : kqLl ≠ rkM := by decide
@[simp] theorem kq_rkM_ne_kqLl : rkM ≠ kqLl := by decide
@[simp] theorem kq_kqTa_ne_kq1 : kqTa ≠ kq1 := by decide
@[simp] theorem kq_kqTa_ne_kqTm : kqTa ≠ kqTm := by decide
@[simp] theorem kq_kqTa_ne_kqHh : kqTa ≠ kqHh := by decide
@[simp] theorem kq_kqTa_ne_kqTp : kqTa ≠ kqTp := by decide
@[simp] theorem kq_kqTa_ne_kqUs : kqTa ≠ kqUs := by decide
@[simp] theorem kq_kqTa_ne_kqLp : kqTa ≠ kqLp := by decide
@[simp] theorem kq_kqTa_ne_kqLl : kqTa ≠ kqLl := by decide
@[simp] theorem kq_kqTa_ne_kqTl : kqTa ≠ kqTl := by decide
@[simp] theorem kq_kqTa_ne_kqNp : kqTa ≠ kqNp := by decide
@[simp] theorem kq_kqTa_ne_kqRc : kqTa ≠ kqRc := by decide
@[simp] theorem kq_kqTa_ne_kqHd : kqTa ≠ kqHd := by decide
@[simp] theorem kq_kqTa_ne_kqFab : kqTa ≠ kqFab := by decide
@[simp] theorem kq_kqTa_ne_kqFs : kqTa ≠ kqFs := by decide
@[simp] theorem kq_kqTa_ne_kqK2 : kqTa ≠ kqK2 := by decide
@[simp] theorem kq_kqTa_ne_kqDf : kqTa ≠ kqDf := by decide
@[simp] theorem kq_kqTa_ne_kqIr : kqTa ≠ kqIr := by decide
@[simp] theorem kq_kqTa_ne_lFl : kqTa ≠ lFl := by decide
@[simp] theorem kq_lFl_ne_kqTa : lFl ≠ kqTa := by decide
@[simp] theorem kq_kqTa_ne_lDh : kqTa ≠ lDh := by decide
@[simp] theorem kq_lDh_ne_kqTa : lDh ≠ kqTa := by decide
@[simp] theorem kq_kqTa_ne_lDt : kqTa ≠ lDt := by decide
@[simp] theorem kq_lDt_ne_kqTa : lDt ≠ kqTa := by decide
@[simp] theorem kq_kqTa_ne_lDg : kqTa ≠ lDg := by decide
@[simp] theorem kq_lDg_ne_kqTa : lDg ≠ kqTa := by decide
@[simp] theorem kq_kqTa_ne_lDi : kqTa ≠ lDi := by decide
@[simp] theorem kq_lDi_ne_kqTa : lDi ≠ kqTa := by decide
@[simp] theorem kq_kqTa_ne_lRp : kqTa ≠ lRp := by decide
@[simp] theorem kq_lRp_ne_kqTa : lRp ≠ kqTa := by decide
@[simp] theorem kq_kqTa_ne_lRn : kqTa ≠ lRn := by decide
@[simp] theorem kq_lRn_ne_kqTa : lRn ≠ kqTa := by decide
@[simp] theorem kq_kqTa_ne_lFle : kqTa ≠ lFle := by decide
@[simp] theorem kq_lFle_ne_kqTa : lFle ≠ kqTa := by decide
@[simp] theorem kq_kqTa_ne_lFls : kqTa ≠ lFls := by decide
@[simp] theorem kq_lFls_ne_kqTa : lFls ≠ kqTa := by decide
@[simp] theorem kq_kqTa_ne_lDir : kqTa ≠ lDir := by decide
@[simp] theorem kq_lDir_ne_kqTa : lDir ≠ kqTa := by decide
@[simp] theorem kq_kqTa_ne_lKb : kqTa ≠ lKb := by decide
@[simp] theorem kq_lKb_ne_kqTa : lKb ≠ kqTa := by decide
@[simp] theorem kq_kqTa_ne_kFu : kqTa ≠ kFu := by decide
@[simp] theorem kq_kFu_ne_kqTa : kFu ≠ kqTa := by decide
@[simp] theorem kq_kqTa_ne_kD : kqTa ≠ kD := by decide
@[simp] theorem kq_kD_ne_kqTa : kD ≠ kqTa := by decide
@[simp] theorem kq_kqTa_ne_rkR : kqTa ≠ rkR := by decide
@[simp] theorem kq_rkR_ne_kqTa : rkR ≠ kqTa := by decide
@[simp] theorem kq_kqTa_ne_rkJ : kqTa ≠ rkJ := by decide
@[simp] theorem kq_rkJ_ne_kqTa : rkJ ≠ kqTa := by decide
@[simp] theorem kq_kqTa_ne_rkT : kqTa ≠ rkT := by decide
@[simp] theorem kq_rkT_ne_kqTa : rkT ≠ kqTa := by decide
@[simp] theorem kq_kqTa_ne_rkM : kqTa ≠ rkM := by decide
@[simp] theorem kq_rkM_ne_kqTa : rkM ≠ kqTa := by decide
@[simp] theorem kq_kqTl_ne_kq1 : kqTl ≠ kq1 := by decide
@[simp] theorem kq_kqTl_ne_kqTm : kqTl ≠ kqTm := by decide
@[simp] theorem kq_kqTl_ne_kqHh : kqTl ≠ kqHh := by decide
@[simp] theorem kq_kqTl_ne_kqTp : kqTl ≠ kqTp := by decide
@[simp] theorem kq_kqTl_ne_kqUs : kqTl ≠ kqUs := by decide
@[simp] theorem kq_kqTl_ne_kqLp : kqTl ≠ kqLp := by decide
@[simp] theorem kq_kqTl_ne_kqLl : kqTl ≠ kqLl := by decide
@[simp] theorem kq_kqTl_ne_kqTa : kqTl ≠ kqTa := by decide
@[simp] theorem kq_kqTl_ne_kqNp : kqTl ≠ kqNp := by decide
@[simp] theorem kq_kqTl_ne_kqRc : kqTl ≠ kqRc := by decide
@[simp] theorem kq_kqTl_ne_kqHd : kqTl ≠ kqHd := by decide
@[simp] theorem kq_kqTl_ne_kqFab : kqTl ≠ kqFab := by decide
@[simp] theorem kq_kqTl_ne_kqFs : kqTl ≠ kqFs := by decide
@[simp] theorem kq_kqTl_ne_kqK2 : kqTl ≠ kqK2 := by decide
@[simp] theorem kq_kqTl_ne_kqDf : kqTl ≠ kqDf := by decide
@[simp] theorem kq_kqTl_ne_kqIr : kqTl ≠ kqIr := by decide
@[simp] theorem kq_kqTl_ne_lFl : kqTl ≠ lFl := by decide
@[simp] theorem kq_lFl_ne_kqTl : lFl ≠ kqTl := by decide
@[simp] theorem kq_kqTl_ne_lDh : kqTl ≠ lDh := by decide
@[simp] theorem kq_lDh_ne_kqTl : lDh ≠ kqTl := by decide
@[simp] theorem kq_kqTl_ne_lDt : kqTl ≠ lDt := by decide
@[simp] theorem kq_lDt_ne_kqTl : lDt ≠ kqTl := by decide
@[simp] theorem kq_kqTl_ne_lDg : kqTl ≠ lDg := by decide
@[simp] theorem kq_lDg_ne_kqTl : lDg ≠ kqTl := by decide
@[simp] theorem kq_kqTl_ne_lDi : kqTl ≠ lDi := by decide
@[simp] theorem kq_lDi_ne_kqTl : lDi ≠ kqTl := by decide
@[simp] theorem kq_kqTl_ne_lRp : kqTl ≠ lRp := by decide
@[simp] theorem kq_lRp_ne_kqTl : lRp ≠ kqTl := by decide
@[simp] theorem kq_kqTl_ne_lRn : kqTl ≠ lRn := by decide
@[simp] theorem kq_lRn_ne_kqTl : lRn ≠ kqTl := by decide
@[simp] theorem kq_kqTl_ne_lFle : kqTl ≠ lFle := by decide
@[simp] theorem kq_lFle_ne_kqTl : lFle ≠ kqTl := by decide
@[simp] theorem kq_kqTl_ne_lFls : kqTl ≠ lFls := by decide
@[simp] theorem kq_lFls_ne_kqTl : lFls ≠ kqTl := by decide
@[simp] theorem kq_kqTl_ne_lDir : kqTl ≠ lDir := by decide
@[simp] theorem kq_lDir_ne_kqTl : lDir ≠ kqTl := by decide
@[simp] theorem kq_kqTl_ne_lKb : kqTl ≠ lKb := by decide
@[simp] theorem kq_lKb_ne_kqTl : lKb ≠ kqTl := by decide
@[simp] theorem kq_kqTl_ne_kFu : kqTl ≠ kFu := by decide
@[simp] theorem kq_kFu_ne_kqTl : kFu ≠ kqTl := by decide
@[simp] theorem kq_kqTl_ne_kD : kqTl ≠ kD := by decide
@[simp] theorem kq_kD_ne_kqTl : kD ≠ kqTl := by decide
@[simp] theorem kq_kqTl_ne_rkR : kqTl ≠ rkR := by decide
@[simp] theorem kq_rkR_ne_kqTl : rkR ≠ kqTl := by decide
@[simp] theorem kq_kqTl_ne_rkJ : kqTl ≠ rkJ := by decide
@[simp] theorem kq_rkJ_ne_kqTl : rkJ ≠ kqTl := by decide
@[simp] theorem kq_kqTl_ne_rkT : kqTl ≠ rkT := by decide
@[simp] theorem kq_rkT_ne_kqTl : rkT ≠ kqTl := by decide
@[simp] theorem kq_kqTl_ne_rkM : kqTl ≠ rkM := by decide
@[simp] theorem kq_rkM_ne_kqTl : rkM ≠ kqTl := by decide
@[simp] theorem kq_kqNp_ne_kq1 : kqNp ≠ kq1 := by decide
@[simp] theorem kq_kqNp_ne_kqTm : kqNp ≠ kqTm := by decide
@[simp] theorem kq_kqNp_ne_kqHh : kqNp ≠ kqHh := by decide
@[simp] theorem kq_kqNp_ne_kqTp : kqNp ≠ kqTp := by decide
@[simp] theorem kq_kqNp_ne_kqUs : kqNp ≠ kqUs := by decide
@[simp] theorem kq_kqNp_ne_kqLp : kqNp ≠ kqLp := by decide
@[simp] theorem kq_kqNp_ne_kqLl : kqNp ≠ kqLl := by decide
@[simp] theorem kq_kqNp_ne_kqTa : kqNp ≠ kqTa := by decide
@[simp] theorem kq_kqNp_ne_kqTl : kqNp ≠ kqTl := by decide
@[simp] theorem kq_kqNp_ne_kqRc : kqNp ≠ kqRc := by decide
@[simp] theorem kq_kqNp_ne_kqHd : kqNp ≠ kqHd := by decide
@[simp] theorem kq_kqNp_ne_kqFab : kqNp ≠ kqFab := by decide
@[simp] theorem kq_kqNp_ne_kqFs : kqNp ≠ kqFs := by decide
@[simp] theorem kq_kqNp_ne_kqK2 : kqNp ≠ kqK2 := by decide
@[simp] theorem kq_kqNp_ne_kqDf : kqNp ≠ kqDf := by decide
@[simp] theorem kq_kqNp_ne_kqIr : kqNp ≠ kqIr := by decide
@[simp] theorem kq_kqNp_ne_lFl : kqNp ≠ lFl := by decide
@[simp] theorem kq_lFl_ne_kqNp : lFl ≠ kqNp := by decide
@[simp] theorem kq_kqNp_ne_lDh : kqNp ≠ lDh := by decide
@[simp] theorem kq_lDh_ne_kqNp : lDh ≠ kqNp := by decide
@[simp] theorem kq_kqNp_ne_lDt : kqNp ≠ lDt := by decide
@[simp] theorem kq_lDt_ne_kqNp : lDt ≠ kqNp := by decide
@[simp] theorem kq_kqNp_ne_lDg : kqNp ≠ lDg := by decide
@[simp] theorem kq_lDg_ne_kqNp : lDg ≠ kqNp := by decide
@[simp] theorem kq_kqNp_ne_lDi : kqNp ≠ lDi := by decide
@[simp] theorem kq_lDi_ne_kqNp : lDi ≠ kqNp := by decide
@[simp] theorem kq_kqNp_ne_lRp : kqNp ≠ lRp := by decide
@[simp] theorem kq_lRp_ne_kqNp : lRp ≠ kqNp := by decide
@[simp] theorem kq_kqNp_ne_lRn : kqNp ≠ lRn := by decide
@[simp] theorem kq_lRn_ne_kqNp : lRn ≠ kqNp := by decide
@[simp] theorem kq_kqNp_ne_lFle : kqNp ≠ lFle := by decide
@[simp] theorem kq_lFle_ne_kqNp : lFle ≠ kqNp := by decide
@[simp] theorem kq_kqNp_ne_lFls : kqNp ≠ lFls := by decide
@[simp] theorem kq_lFls_ne_kqNp : lFls ≠ kqNp := by decide
@[simp] theorem kq_kqNp_ne_lDir : kqNp ≠ lDir := by decide
@[simp] theorem kq_lDir_ne_kqNp : lDir ≠ kqNp := by decide
@[simp] theorem kq_kqNp_ne_lKb : kqNp ≠ lKb := by decide
@[simp] theorem kq_lKb_ne_kqNp : lKb ≠ kqNp := by decide
@[simp] theorem kq_kqNp_ne_kFu : kqNp ≠ kFu := by decide
@[simp] theorem kq_kFu_ne_kqNp : kFu ≠ kqNp := by decide
@[simp] theorem kq_kqNp_ne_kD : kqNp ≠ kD := by decide
@[simp] theorem kq_kD_ne_kqNp : kD ≠ kqNp := by decide
@[simp] theorem kq_kqNp_ne_rkR : kqNp ≠ rkR := by decide
@[simp] theorem kq_rkR_ne_kqNp : rkR ≠ kqNp := by decide
@[simp] theorem kq_kqNp_ne_rkJ : kqNp ≠ rkJ := by decide
@[simp] theorem kq_rkJ_ne_kqNp : rkJ ≠ kqNp := by decide
@[simp] theorem kq_kqNp_ne_rkT : kqNp ≠ rkT := by decide
@[simp] theorem kq_rkT_ne_kqNp : rkT ≠ kqNp := by decide
@[simp] theorem kq_kqNp_ne_rkM : kqNp ≠ rkM := by decide
@[simp] theorem kq_rkM_ne_kqNp : rkM ≠ kqNp := by decide
@[simp] theorem kq_kqRc_ne_kq1 : kqRc ≠ kq1 := by decide
@[simp] theorem kq_kqRc_ne_kqTm : kqRc ≠ kqTm := by decide
@[simp] theorem kq_kqRc_ne_kqHh : kqRc ≠ kqHh := by decide
@[simp] theorem kq_kqRc_ne_kqTp : kqRc ≠ kqTp := by decide
@[simp] theorem kq_kqRc_ne_kqUs : kqRc ≠ kqUs := by decide
@[simp] theorem kq_kqRc_ne_kqLp : kqRc ≠ kqLp := by decide
@[simp] theorem kq_kqRc_ne_kqLl : kqRc ≠ kqLl := by decide
@[simp] theorem kq_kqRc_ne_kqTa : kqRc ≠ kqTa := by decide
@[simp] theorem kq_kqRc_ne_kqTl : kqRc ≠ kqTl := by decide
@[simp] theorem kq_kqRc_ne_kqNp : kqRc ≠ kqNp := by decide
@[simp] theorem kq_kqRc_ne_kqHd : kqRc ≠ kqHd := by decide
@[simp] theorem kq_kqRc_ne_kqFab : kqRc ≠ kqFab := by decide
@[simp] theorem kq_kqRc_ne_kqFs : kqRc ≠ kqFs := by decide
@[simp] theorem kq_kqRc_ne_kqK2 : kqRc ≠ kqK2 := by decide
@[simp] theorem kq_kqRc_ne_kqDf : kqRc ≠ kqDf := by decide
@[simp] theorem kq_kqRc_ne_kqIr : kqRc ≠ kqIr := by decide
@[simp] theorem kq_kqRc_ne_lFl : kqRc ≠ lFl := by decide
@[simp] theorem kq_lFl_ne_kqRc : lFl ≠ kqRc := by decide
@[simp] theorem kq_kqRc_ne_lDh : kqRc ≠ lDh := by decide
@[simp] theorem kq_lDh_ne_kqRc : lDh ≠ kqRc := by decide
@[simp] theorem kq_kqRc_ne_lDt : kqRc ≠ lDt := by decide
@[simp] theorem kq_lDt_ne_kqRc : lDt ≠ kqRc := by decide
@[simp] theorem kq_kqRc_ne_lDg : kqRc ≠ lDg := by decide
@[simp] theorem kq_lDg_ne_kqRc : lDg ≠ kqRc := by decide
@[simp] theorem kq_kqRc_ne_lDi : kqRc ≠ lDi := by decide
@[simp] theorem kq_lDi_ne_kqRc : lDi ≠ kqRc := by decide
@[simp] theorem kq_kqRc_ne_lRp : kqRc ≠ lRp := by decide
@[simp] theorem kq_lRp_ne_kqRc : lRp ≠ kqRc := by decide
@[simp] theorem kq_kqRc_ne_lRn : kqRc ≠ lRn := by decide
@[simp] theorem kq_lRn_ne_kqRc : lRn ≠ kqRc := by decide
@[simp] theorem kq_kqRc_ne_lFle : kqRc ≠ lFle := by decide
@[simp] theorem kq_lFle_ne_kqRc : lFle ≠ kqRc := by decide
@[simp] theorem kq_kqRc_ne_lFls : kqRc ≠ lFls := by decide
@[simp] theorem kq_lFls_ne_kqRc : lFls ≠ kqRc := by decide
@[simp] theorem kq_kqRc_ne_lDir : kqRc ≠ lDir := by decide
@[simp] theorem kq_lDir_ne_kqRc : lDir ≠ kqRc := by decide
@[simp] theorem kq_kqRc_ne_lKb : kqRc ≠ lKb := by decide
@[simp] theorem kq_lKb_ne_kqRc : lKb ≠ kqRc := by decide
@[simp] theorem kq_kqRc_ne_kFu : kqRc ≠ kFu := by decide
@[simp] theorem kq_kFu_ne_kqRc : kFu ≠ kqRc := by decide
@[simp] theorem kq_kqRc_ne_kD : kqRc ≠ kD := by decide
@[simp] theorem kq_kD_ne_kqRc : kD ≠ kqRc := by decide
@[simp] theorem kq_kqRc_ne_rkR : kqRc ≠ rkR := by decide
@[simp] theorem kq_rkR_ne_kqRc : rkR ≠ kqRc := by decide
@[simp] theorem kq_kqRc_ne_rkJ : kqRc ≠ rkJ := by decide
@[simp] theorem kq_rkJ_ne_kqRc : rkJ ≠ kqRc := by decide
@[simp] theorem kq_kqRc_ne_rkT : kqRc ≠ rkT := by decide
@[simp] theorem kq_rkT_ne_kqRc : rkT ≠ kqRc := by decide
@[simp] theorem kq_kqRc_ne_rkM : kqRc ≠ rkM := by decide
@[simp] theorem kq_rkM_ne_kqRc : rkM ≠ kqRc := by decide
@[simp] theorem kq_kqHd_ne_kq1 : kqHd ≠ kq1 := by decide
@[simp] theorem kq_kqHd_ne_kqTm : kqHd ≠ kqTm := by decide
@[simp] theorem kq_kqHd_ne_kqHh : kqHd ≠ kqHh := by decide
@[simp] theorem kq_kqHd_ne_kqTp : kqHd ≠ kqTp := by decide
@[simp] theorem kq_kqHd_ne_kqUs : kqHd ≠ kqUs := by decide
@[simp] theorem kq_kqHd_ne_kqLp : kqHd ≠ kqLp := by decide
@[simp] theorem kq_kqHd_ne_kqLl : kqHd ≠ kqLl := by decide
@[simp] theorem kq_kqHd_ne_kqTa : kqHd ≠ kqTa := by decide
@[simp] theorem kq_kqHd_ne_kqTl : kqHd ≠ kqTl := by decide
@[simp] theorem kq_kqHd_ne_kqNp : kqHd ≠ kqNp := by decide
@[simp] theorem kq_kqHd_ne_kqRc : kqHd ≠ kqRc := by decide
@[simp] theorem kq_kqHd_ne_kqFab : kqHd ≠ kqFab := by decide
@[simp] theorem kq_kqHd_ne_kqFs : kqHd ≠ kqFs := by decide
@[simp] theorem kq_kqHd_ne_kqK2 : kqHd ≠ kqK2 := by decide
@[simp] theorem kq_kqHd_ne_kqDf : kqHd ≠ kqDf := by decide
@[simp] theorem kq_kqHd_ne_kqIr : kqHd ≠ kqIr := by decide
@[simp] theorem kq_kqHd_ne_lFl : kqHd ≠ lFl := by decide
@[simp] theorem kq_lFl_ne_kqHd : lFl ≠ kqHd := by decide
@[simp] theorem kq_kqHd_ne_lDh : kqHd ≠ lDh := by decide
@[simp] theorem kq_lDh_ne_kqHd : lDh ≠ kqHd := by decide
@[simp] theorem kq_kqHd_ne_lDt : kqHd ≠ lDt := by decide
@[simp] theorem kq_lDt_ne_kqHd : lDt ≠ kqHd := by decide
@[simp] theorem kq_kqHd_ne_lDg : kqHd ≠ lDg := by decide
@[simp] theorem kq_lDg_ne_kqHd : lDg ≠ kqHd := by decide
@[simp] theorem kq_kqHd_ne_lDi : kqHd ≠ lDi := by decide
@[simp] theorem kq_lDi_ne_kqHd : lDi ≠ kqHd := by decide
@[simp] theorem kq_kqHd_ne_lRp : kqHd ≠ lRp := by decide
@[simp] theorem kq_lRp_ne_kqHd : lRp ≠ kqHd := by decide
@[simp] theorem kq_kqHd_ne_lRn : kqHd ≠ lRn := by decide
@[simp] theorem kq_lRn_ne_kqHd : lRn ≠ kqHd := by decide
@[simp] theorem kq_kqHd_ne_lFle : kqHd ≠ lFle := by decide
@[simp] theorem kq_lFle_ne_kqHd : lFle ≠ kqHd := by decide
@[simp] theorem kq_kqHd_ne_lFls : kqHd ≠ lFls := by decide
@[simp] theorem kq_lFls_ne_kqHd : lFls ≠ kqHd := by decide
@[simp] theorem kq_kqHd_ne_lDir : kqHd ≠ lDir := by decide
@[simp] theorem kq_lDir_ne_kqHd : lDir ≠ kqHd := by decide
@[simp] theorem kq_kqHd_ne_lKb : kqHd ≠ lKb := by decide
@[simp] theorem kq_lKb_ne_kqHd : lKb ≠ kqHd := by decide
@[simp] theorem kq_kqHd_ne_kFu : kqHd ≠ kFu := by decide
@[simp] theorem kq_kFu_ne_kqHd : kFu ≠ kqHd := by decide
@[simp] theorem kq_kqHd_ne_kD : kqHd ≠ kD := by decide
@[simp] theorem kq_kD_ne_kqHd : kD ≠ kqHd := by decide
@[simp] theorem kq_kqHd_ne_rkR : kqHd ≠ rkR := by decide
@[simp] theorem kq_rkR_ne_kqHd : rkR ≠ kqHd := by decide
@[simp] theorem kq_kqHd_ne_rkJ : kqHd ≠ rkJ := by decide
@[simp] theorem kq_rkJ_ne_kqHd : rkJ ≠ kqHd := by decide
@[simp] theorem kq_kqHd_ne_rkT : kqHd ≠ rkT := by decide
@[simp] theorem kq_rkT_ne_kqHd : rkT ≠ kqHd := by decide
@[simp] theorem kq_kqHd_ne_rkM : kqHd ≠ rkM := by decide
@[simp] theorem kq_rkM_ne_kqHd : rkM ≠ kqHd := by decide
@[simp] theorem kq_kqFab_ne_kq1 : kqFab ≠ kq1 := by decide
@[simp] theorem kq_kqFab_ne_kqTm : kqFab ≠ kqTm := by decide
@[simp] theorem kq_kqFab_ne_kqHh : kqFab ≠ kqHh := by decide
@[simp] theorem kq_kqFab_ne_kqTp : kqFab ≠ kqTp := by decide
@[simp] theorem kq_kqFab_ne_kqUs : kqFab ≠ kqUs := by decide
@[simp] theorem kq_kqFab_ne_kqLp : kqFab ≠ kqLp := by decide
@[simp] theorem kq_kqFab_ne_kqLl : kqFab ≠ kqLl := by decide
@[simp] theorem kq_kqFab_ne_kqTa : kqFab ≠ kqTa := by decide
@[simp] theorem kq_kqFab_ne_kqTl : kqFab ≠ kqTl := by decide
@[simp] theorem kq_kqFab_ne_kqNp : kqFab ≠ kqNp := by decide
@[simp] theorem kq_kqFab_ne_kqRc : kqFab ≠ kqRc := by decide
@[simp] theorem kq_kqFab_ne_kqHd : kqFab ≠ kqHd := by decide
@[simp] theorem kq_kqFab_ne_kqFs : kqFab ≠ kqFs := by decide
@[simp] theorem kq_kqFab_ne_kqK2 : kqFab ≠ kqK2 := by decide
@[simp] theorem kq_kqFab_ne_kqDf : kqFab ≠ kqDf := by decide
@[simp] theorem kq_kqFab_ne_kqIr : kqFab ≠ kqIr := by decide
@[simp] theorem kq_kqFab_ne_lFl : kqFab ≠ lFl := by decide
@[simp] theorem kq_lFl_ne_kqFab : lFl ≠ kqFab := by decide
@[simp] theorem kq_kqFab_ne_lDh : kqFab ≠ lDh := by decide
@[simp] theorem kq_lDh_ne_kqFab : lDh ≠ kqFab := by decide
@[simp] theorem kq_kqFab_ne_lDt : kqFab ≠ lDt := by decide
@[simp] theorem kq_lDt_ne_kqFab : lDt ≠ kqFab := by decide
@[simp] theorem kq_kqFab_ne_lDg : kqFab ≠ lDg := by decide
@[simp] theorem kq_lDg_ne_kqFab : lDg ≠ kqFab := by decide
@[simp] theorem kq_kqFab_ne_lDi : kqFab ≠ lDi := by decide
@[simp] theorem kq_lDi_ne_kqFab : lDi ≠ kqFab := by decide
@[simp] theorem kq_kqFab_ne_lRp : kqFab ≠ lRp := by decide
@[simp] theorem kq_lRp_ne_kqFab : lRp ≠ kqFab := by decide
@[simp] theorem kq_kqFab_ne_lRn : kqFab ≠ lRn := by decide
@[simp] theorem kq_lRn_ne_kqFab : lRn ≠ kqFab := by decide
@[simp] theorem kq_kqFab_ne_lFle : kqFab ≠ lFle := by decide
@[simp] theorem kq_lFle_ne_kqFab : lFle ≠ kqFab := by decide
@[simp] theorem kq_kqFab_ne_lFls : kqFab ≠ lFls := by decide
@[simp] theorem kq_lFls_ne_kqFab : lFls ≠ kqFab := by decide
@[simp] theorem kq_kqFab_ne_lDir : kqFab ≠ lDir := by decide
@[simp] theorem kq_lDir_ne_kqFab : lDir ≠ kqFab := by decide
@[simp] theorem kq_kqFab_ne_lKb : kqFab ≠ lKb := by decide
@[simp] theorem kq_lKb_ne_kqFab : lKb ≠ kqFab := by decide
@[simp] theorem kq_kqFab_ne_kFu : kqFab ≠ kFu := by decide
@[simp] theorem kq_kFu_ne_kqFab : kFu ≠ kqFab := by decide
@[simp] theorem kq_kqFab_ne_kD : kqFab ≠ kD := by decide
@[simp] theorem kq_kD_ne_kqFab : kD ≠ kqFab := by decide
@[simp] theorem kq_kqFab_ne_rkR : kqFab ≠ rkR := by decide
@[simp] theorem kq_rkR_ne_kqFab : rkR ≠ kqFab := by decide
@[simp] theorem kq_kqFab_ne_rkJ : kqFab ≠ rkJ := by decide
@[simp] theorem kq_rkJ_ne_kqFab : rkJ ≠ kqFab := by decide
@[simp] theorem kq_kqFab_ne_rkT : kqFab ≠ rkT := by decide
@[simp] theorem kq_rkT_ne_kqFab : rkT ≠ kqFab := by decide
@[simp] theorem kq_kqFab_ne_rkM : kqFab ≠ rkM := by decide
@[simp] theorem kq_rkM_ne_kqFab : rkM ≠ kqFab := by decide
@[simp] theorem kq_kqFs_ne_kq1 : kqFs ≠ kq1 := by decide
@[simp] theorem kq_kqFs_ne_kqTm : kqFs ≠ kqTm := by decide
@[simp] theorem kq_kqFs_ne_kqHh : kqFs ≠ kqHh := by decide
@[simp] theorem kq_kqFs_ne_kqTp : kqFs ≠ kqTp := by decide
@[simp] theorem kq_kqFs_ne_kqUs : kqFs ≠ kqUs := by decide
@[simp] theorem kq_kqFs_ne_kqLp : kqFs ≠ kqLp := by decide
@[simp] theorem kq_kqFs_ne_kqLl : kqFs ≠ kqLl := by decide
@[simp] theorem kq_kqFs_ne_kqTa : kqFs ≠ kqTa := by decide
@[simp] theorem kq_kqFs_ne_kqTl : kqFs ≠ kqTl := by decide
@[simp] theorem kq_kqFs_ne_kqNp : kqFs ≠ kqNp := by decide
@[simp] theorem kq_kqFs_ne_kqRc : kqFs ≠ kqRc := by decide
@[simp] theorem kq_kqFs_ne_kqHd : kqFs ≠ kqHd := by decide
@[simp] theorem kq_kqFs_ne_kqFab : kqFs ≠ kqFab := by decide
@[simp] theorem kq_kqFs_ne_kqK2 : kqFs ≠ kqK2 := by decide
@[simp] theorem kq_kqFs_ne_kqDf : kqFs ≠ kqDf := by decide
@[simp] theorem kq_kqFs_ne_kqIr : kqFs ≠ kqIr := by decide
@[simp] theorem kq_kqFs_ne_lFl : kqFs ≠ lFl := by decide
@[simp] theorem kq_lFl_ne_kqFs : lFl ≠ kqFs := by decide
@[simp] theorem kq_kqFs_ne_lDh : kqFs ≠ lDh := by decide
@[simp] theorem kq_lDh_ne_kqFs : lDh ≠ kqFs := by decide
@[simp] theorem kq_kqFs_ne_lDt : kqFs ≠ lDt := by decide
@[simp] theorem kq_lDt_ne_kqFs : lDt ≠ kqFs := by decide
@[simp] theorem kq_kqFs_ne_lDg : kqFs ≠ lDg := by decide
@[simp] theorem kq_lDg_ne_kqFs : lDg ≠ kqFs := by decide
@[simp] theorem kq_kqFs_ne_lDi : kqFs ≠ lDi := by decide
@[simp] theorem kq_lDi_ne_kqFs : lDi ≠ kqFs := by decide
@[simp] theorem kq_kqFs_ne_lRp : kqFs ≠ lRp := by decide
@[simp] theorem kq_lRp_ne_kqFs : lRp ≠ kqFs := by decide
@[simp] theorem kq_kqFs_ne_lRn : kqFs ≠ lRn := by decide
@[simp] theorem kq_lRn_ne_kqFs : lRn ≠ kqFs := by decide
@[simp] theorem kq_kqFs_ne_lFle : kqFs ≠ lFle := by decide
@[simp] theorem kq_lFle_ne_kqFs : lFle ≠ kqFs := by decide
@[simp] theorem kq_kqFs_ne_lFls : kqFs ≠ lFls := by decide
@[simp] theorem kq_lFls_ne_kqFs : lFls ≠ kqFs := by decide
@[simp] theorem kq_kqFs_ne_lDir : kqFs ≠ lDir := by decide
@[simp] theorem kq_lDir_ne_kqFs : lDir ≠ kqFs := by decide
@[simp] theorem kq_kqFs_ne_lKb : kqFs ≠ lKb := by decide
@[simp] theorem kq_lKb_ne_kqFs : lKb ≠ kqFs := by decide
@[simp] theorem kq_kqFs_ne_kFu : kqFs ≠ kFu := by decide
@[simp] theorem kq_kFu_ne_kqFs : kFu ≠ kqFs := by decide
@[simp] theorem kq_kqFs_ne_kD : kqFs ≠ kD := by decide
@[simp] theorem kq_kD_ne_kqFs : kD ≠ kqFs := by decide
@[simp] theorem kq_kqFs_ne_rkR : kqFs ≠ rkR := by decide
@[simp] theorem kq_rkR_ne_kqFs : rkR ≠ kqFs := by decide
@[simp] theorem kq_kqFs_ne_rkJ : kqFs ≠ rkJ := by decide
@[simp] theorem kq_rkJ_ne_kqFs : rkJ ≠ kqFs := by decide
@[simp] theorem kq_kqFs_ne_rkT : kqFs ≠ rkT := by decide
@[simp] theorem kq_rkT_ne_kqFs : rkT ≠ kqFs := by decide
@[simp] theorem kq_kqFs_ne_rkM : kqFs ≠ rkM := by decide
@[simp] theorem kq_rkM_ne_kqFs : rkM ≠ kqFs := by decide
@[simp] theorem kq_kqK2_ne_kq1 : kqK2 ≠ kq1 := by decide
@[simp] theorem kq_kqK2_ne_kqTm : kqK2 ≠ kqTm := by decide
@[simp] theorem kq_kqK2_ne_kqHh : kqK2 ≠ kqHh := by decide
@[simp] theorem kq_kqK2_ne_kqTp : kqK2 ≠ kqTp := by decide
@[simp] theorem kq_kqK2_ne_kqUs : kqK2 ≠ kqUs := by decide
@[simp] theorem kq_kqK2_ne_kqLp : kqK2 ≠ kqLp := by decide
@[simp] theorem kq_kqK2_ne_kqLl : kqK2 ≠ kqLl := by decide
@[simp] theorem kq_kqK2_ne_kqTa : kqK2 ≠ kqTa := by decide
@[simp] theorem kq_kqK2_ne_kqTl : kqK2 ≠ kqTl := by decide
@[simp] theorem kq_kqK2_ne_kqNp : kqK2 ≠ kqNp := by decide
@[simp] theorem kq_kqK2_ne_kqRc : kqK2 ≠ kqRc := by decide
@[simp] theorem kq_kqK2_ne_kqHd : kqK2 ≠ kqHd := by decide
@[simp] theorem kq_kqK2_ne_kqFab : kqK2 ≠ kqFab := by decide
@[simp] theorem kq_kqK2_ne_kqFs : kqK2 ≠ kqFs := by decide
@[simp] theorem kq_kqK2_ne_kqDf : kqK2 ≠ kqDf := by decide
@[simp] theorem kq_kqK2_ne_kqIr : kqK2 ≠ kqIr := by decide
@[simp] theorem kq_kqK2_ne_lFl : kqK2 ≠ lFl := by decide
@[simp] theorem kq_lFl_ne_kqK2 : lFl ≠ kqK2 := by decide
@[simp] theorem kq_kqK2_ne_lDh : kqK2 ≠ lDh := by decide
@[simp] theorem kq_lDh_ne_kqK2 : lDh ≠ kqK2 := by decide
@[simp] theorem kq_kqK2_ne_lDt : kqK2 ≠ lDt := by decide
@[simp] theorem kq_lDt_ne_kqK2 : lDt ≠ kqK2 := by decide
@[simp] theorem kq_kqK2_ne_lDg : kqK2 ≠ lDg := by decide
@[simp] theorem kq_lDg_ne_kqK2 : lDg ≠ kqK2 := by decide
@[simp] theorem kq_kqK2_ne_lDi : kqK2 ≠ lDi := by decide
@[simp] theorem kq_lDi_ne_kqK2 : lDi ≠ kqK2 := by decide
@[simp] theorem kq_kqK2_ne_lRp : kqK2 ≠ lRp := by decide
@[simp] theorem kq_lRp_ne_kqK2 : lRp ≠ kqK2 := by decide
@[simp] theorem kq_kqK2_ne_lRn : kqK2 ≠ lRn := by decide
@[simp] theorem kq_lRn_ne_kqK2 : lRn ≠ kqK2 := by decide
@[simp] theorem kq_kqK2_ne_lFle : kqK2 ≠ lFle := by decide
@[simp] theorem kq_lFle_ne_kqK2 : lFle ≠ kqK2 := by decide
@[simp] theorem kq_kqK2_ne_lFls : kqK2 ≠ lFls := by decide
@[simp] theorem kq_lFls_ne_kqK2 : lFls ≠ kqK2 := by decide
@[simp] theorem kq_kqK2_ne_lDir : kqK2 ≠ lDir := by decide
@[simp] theorem kq_lDir_ne_kqK2 : lDir ≠ kqK2 := by decide
@[simp] theorem kq_kqK2_ne_lKb : kqK2 ≠ lKb := by decide
@[simp] theorem kq_lKb_ne_kqK2 : lKb ≠ kqK2 := by decide
@[simp] theorem kq_kqK2_ne_kFu : kqK2 ≠ kFu := by decide
@[simp] theorem kq_kFu_ne_kqK2 : kFu ≠ kqK2 := by decide
@[simp] theorem kq_kqK2_ne_kD : kqK2 ≠ kD := by decide
@[simp] theorem kq_kD_ne_kqK2 : kD ≠ kqK2 := by decide
@[simp] theorem kq_kqK2_ne_rkR : kqK2 ≠ rkR := by decide
@[simp] theorem kq_rkR_ne_kqK2 : rkR ≠ kqK2 := by decide
@[simp] theorem kq_kqK2_ne_rkJ : kqK2 ≠ rkJ := by decide
@[simp] theorem kq_rkJ_ne_kqK2 : rkJ ≠ kqK2 := by decide
@[simp] theorem kq_kqK2_ne_rkT : kqK2 ≠ rkT := by decide
@[simp] theorem kq_rkT_ne_kqK2 : rkT ≠ kqK2 := by decide
@[simp] theorem kq_kqK2_ne_rkM : kqK2 ≠ rkM := by decide
@[simp] theorem kq_rkM_ne_kqK2 : rkM ≠ kqK2 := by decide
@[simp] theorem kq_kqDf_ne_kq1 : kqDf ≠ kq1 := by decide
@[simp] theorem kq_kqDf_ne_kqTm : kqDf ≠ kqTm := by decide
@[simp] theorem kq_kqDf_ne_kqHh : kqDf ≠ kqHh := by decide
@[simp] theorem kq_kqDf_ne_kqTp : kqDf ≠ kqTp := by decide
@[simp] theorem kq_kqDf_ne_kqUs : kqDf ≠ kqUs := by decide
@[simp] theorem kq_kqDf_ne_kqLp : kqDf ≠ kqLp := by decide
@[simp] theorem kq_kqDf_ne_kqLl : kqDf ≠ kqLl := by decide
@[simp] theorem kq_kqDf_ne_kqTa : kqDf ≠ kqTa := by decide
@[simp] theorem kq_kqDf_ne_kqTl : kqDf ≠ kqTl := by decide
@[simp] theorem kq_kqDf_ne_kqNp : kqDf ≠ kqNp := by decide
@[simp] theorem kq_kqDf_ne_kqRc : kqDf ≠ kqRc := by decide
@[simp] theorem kq_kqDf_ne_kqHd : kqDf ≠ kqHd := by decide
@[simp] theorem kq_kqDf_ne_kqFab : kqDf ≠ kqFab := by decide
@[simp] theorem kq_kqDf_ne_kqFs : kqDf ≠ kqFs := by decide
@[simp] theorem kq_kqDf_ne_kqK2 : kqDf ≠ kqK2 := by decide
@[simp] theorem kq_kqDf_ne_kqIr : kqDf ≠ kqIr := by decide
@[simp] theorem kq_kqDf_ne_lFl : kqDf ≠ lFl := by decide
@[simp] theorem kq_lFl_ne_kqDf : lFl ≠ kqDf := by decide
@[simp] theorem kq_kqDf_ne_lDh : kqDf ≠ lDh := by decide
@[simp] theorem kq_lDh_ne_kqDf : lDh ≠ kqDf := by decide
@[simp] theorem kq_kqDf_ne_lDt : kqDf ≠ lDt := by decide
@[simp] theorem kq_lDt_ne_kqDf : lDt ≠ kqDf := by decide
@[simp] theorem kq_kqDf_ne_lDg : kqDf ≠ lDg := by decide
@[simp] theorem kq_lDg_ne_kqDf : lDg ≠ kqDf := by decide
@[simp] theorem kq_kqDf_ne_lDi : kqDf ≠ lDi := by decide
@[simp] theorem kq_lDi_ne_kqDf : lDi ≠ kqDf := by decide
@[simp] theorem kq_kqDf_ne_lRp : kqDf ≠ lRp := by decide
@[simp] theorem kq_lRp_ne_kqDf : lRp ≠ kqDf := by decide
@[simp] theorem kq_kqDf_ne_lRn : kqDf ≠ lRn := by decide
@[simp] theorem kq_lRn_ne_kqDf : lRn ≠ kqDf := by decide
@[simp] theorem kq_kqDf_ne_lFle : kqDf ≠ lFle := by decide
@[simp] theorem kq_lFle_ne_kqDf : lFle ≠ kqDf := by decide
@[simp] theorem kq_kqDf_ne_lFls : kqDf ≠ lFls := by decide
@[simp] theorem kq_lFls_ne_kqDf : lFls ≠ kqDf := by decide
@[simp] theorem kq_kqDf_ne_lDir : kqDf ≠ lDir := by decide
@[simp] theorem kq_lDir_ne_kqDf : lDir ≠ kqDf := by decide
@[simp] theorem kq_kqDf_ne_lKb : kqDf ≠ lKb := by decide
@[simp] theorem kq_lKb_ne_kqDf : lKb ≠ kqDf := by decide
@[simp] theorem kq_kqDf_ne_kFu : kqDf ≠ kFu := by decide
@[simp] theorem kq_kFu_ne_kqDf : kFu ≠ kqDf := by decide
@[simp] theorem kq_kqDf_ne_kD : kqDf ≠ kD := by decide
@[simp] theorem kq_kD_ne_kqDf : kD ≠ kqDf := by decide
@[simp] theorem kq_kqDf_ne_rkR : kqDf ≠ rkR := by decide
@[simp] theorem kq_rkR_ne_kqDf : rkR ≠ kqDf := by decide
@[simp] theorem kq_kqDf_ne_rkJ : kqDf ≠ rkJ := by decide
@[simp] theorem kq_rkJ_ne_kqDf : rkJ ≠ kqDf := by decide
@[simp] theorem kq_kqDf_ne_rkT : kqDf ≠ rkT := by decide
@[simp] theorem kq_rkT_ne_kqDf : rkT ≠ kqDf := by decide
@[simp] theorem kq_kqDf_ne_rkM : kqDf ≠ rkM := by decide
@[simp] theorem kq_rkM_ne_kqDf : rkM ≠ kqDf := by decide
@[simp] theorem kq_kqIr_ne_kq1 : kqIr ≠ kq1 := by decide
@[simp] theorem kq_kqIr_ne_kqTm : kqIr ≠ kqTm := by decide
@[simp] theorem kq_kqIr_ne_kqHh : kqIr ≠ kqHh := by decide
@[simp] theorem kq_kqIr_ne_kqTp : kqIr ≠ kqTp := by decide
@[simp] theorem kq_kqIr_ne_kqUs : kqIr ≠ kqUs := by decide
@[simp] theorem kq_kqIr_ne_kqLp : kqIr ≠ kqLp := by decide
@[simp] theorem kq_kqIr_ne_kqLl : kqIr ≠ kqLl := by decide
@[simp] theorem kq_kqIr_ne_kqTa : kqIr ≠ kqTa := by decide
@[simp] theorem kq_kqIr_ne_kqTl : kqIr ≠ kqTl := by decide
@[simp] theorem kq_kqIr_ne_kqNp : kqIr ≠ kqNp := by decide
@[simp] theorem kq_kqIr_ne_kqRc : kqIr ≠ kqRc := by decide
@[simp] theorem kq_kqIr_ne_kqHd : kqIr ≠ kqHd := by decide
@[simp] theorem kq_kqIr_ne_kqFab : kqIr ≠ kqFab := by decide
@[simp] theorem kq_kqIr_ne_kqFs : kqIr ≠ kqFs := by decide
@[simp] theorem kq_kqIr_ne_kqK2 : kqIr ≠ kqK2 := by decide
@[simp] theorem kq_kqIr_ne_kqDf : kqIr ≠ kqDf := by decide
@[simp] theorem kq_kqIr_ne_lFl : kqIr ≠ lFl := by decide
@[simp] theorem kq_lFl_ne_kqIr : lFl ≠ kqIr := by decide
@[simp] theorem kq_kqIr_ne_lDh : kqIr ≠ lDh := by decide
@[simp] theorem kq_lDh_ne_kqIr : lDh ≠ kqIr := by decide
@[simp] theorem kq_kqIr_ne_lDt : kqIr ≠ lDt := by decide
@[simp] theorem kq_lDt_ne_kqIr : lDt ≠ kqIr := by decide
@[simp] theorem kq_kqIr_ne_lDg : kqIr ≠ lDg := by decide
@[simp] theorem kq_lDg_ne_kqIr : lDg ≠ kqIr := by decide
@[simp] theorem kq_kqIr_ne_lDi : kqIr ≠ lDi := by decide
@[simp] theorem kq_lDi_ne_kqIr : lDi ≠ kqIr := by decide
@[simp] theorem kq_kqIr_ne_lRp : kqIr ≠ lRp := by decide
@[simp] theorem kq_lRp_ne_kqIr : lRp ≠ kqIr := by decide
@[simp] theorem kq_kqIr_ne_lRn : kqIr ≠ lRn := by decide
@[simp] theorem kq_lRn_ne_kqIr : lRn ≠ kqIr := by decide
@[simp] theorem kq_kqIr_ne_lFle : kqIr ≠ lFle := by decide
@[simp] theorem kq_lFle_ne_kqIr : lFle ≠ kqIr := by decide
@[simp] theorem kq_kqIr_ne_lFls : kqIr ≠ lFls := by decide
@[simp] theorem kq_lFls_ne_kqIr : lFls ≠ kqIr := by decide
@[simp] theorem kq_kqIr_ne_lDir : kqIr ≠ lDir := by decide
@[simp] theorem kq_lDir_ne_kqIr : lDir ≠ kqIr := by decide
@[simp] theorem kq_kqIr_ne_lKb : kqIr ≠ lKb := by decide
@[simp] theorem kq_lKb_ne_kqIr : lKb ≠ kqIr := by decide
@[simp] theorem kq_kqIr_ne_kFu : kqIr ≠ kFu := by decide
@[simp] theorem kq_kFu_ne_kqIr : kFu ≠ kqIr := by decide
@[simp] theorem kq_kqIr_ne_kD : kqIr ≠ kD := by decide
@[simp] theorem kq_kD_ne_kqIr : kD ≠ kqIr := by decide
@[simp] theorem kq_kqIr_ne_rkR : kqIr ≠ rkR := by decide
@[simp] theorem kq_rkR_ne_kqIr : rkR ≠ kqIr := by decide
@[simp] theorem kq_kqIr_ne_rkJ : kqIr ≠ rkJ := by decide
@[simp] theorem kq_rkJ_ne_kqIr : rkJ ≠ kqIr := by decide
@[simp] theorem kq_kqIr_ne_rkT : kqIr ≠ rkT := by decide
@[simp] theorem kq_rkT_ne_kqIr : rkT ≠ kqIr := by decide
@[simp] theorem kq_kqIr_ne_rkM : kqIr ≠ rkM := by decide
@[simp] theorem kq_rkM_ne_kqIr : rkM ≠ kqIr := by decide

def rkCert (v : Bool) : ProgHOL 64 :=
  if v then
    .seq (.call (some (some (.local, kqIr), none)) fPi [vv kFu, vv kD, vv kqFab, vv rkM])
      (.ite (.cmp .equal (vv kqIr) (.const 0)) (.return (vv rkM)) (.return (vv kqFab)))
  else .return (vv kqFab)

def rkLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, kq1, kqTm, kqHh, kqTp, kqUs, kqLp, kqLl, kqTa, kqTl, kqNp, kqRc, kqHd, kqFab, kqFs, kqK2, kqDf, kqIr]

def rkBody (v : Bool) : ProgHOL 64 := prologue rkLocals
  (.seq (.call (some (some (.local, kq1), none)) fIO [vv kFu, vv kD, vv rkM])
  (.seq (.call (some (some (.local, kqTm), none)) fW [vv kFu, vv kD, vv kq1])
  (.seq (.call (some (some (.local, kqHh), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv kqTm])
  (.ite (tagIsE kqHh 3)
  (.seq (.assign .local lFl (vv lFle))
  (.seq (.assign .local lDh (vv kqHh))
  (.seq eViewP
  (.seq (.assign .local kqTp (.load .one (vv lRp)))
  (.seq (.assign .local kqUs (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (.assign .local lFl (vv lFls))
  (.seq (.assign .local lDh (vv kqUs))
  (.seq lsViewP
  (.seq (.assign .local kqLp (.load .one (.op .add [vv rkJ, .const 16])))
  (.seq (.assign .local kqLl (.load .one (vv kqLp)))
  (.ite (.cmp .notEqual (vv kqTp) (vv rkT)) (.return (vv rkM))
  (.ite (.cmp .notEqual (vv kqLl) (vv lRn)) (.return (vv rkM))
  (.seq (.call (some (some (.local, kqTa), none)) ExG.fGaa [.const (BitVec.ofNat 64 coreWalkFuel), vv kqTm])
  (.seq (.assign .local kqTl (.load .one (vv kqTa)))
  (.seq (.assign .local kqNp (.load .one (.op .add [vv rkJ, .const 32])))
  (.ite (.cmp .lower (vv kqTl) (vv kqNp)) (.return (vv rkM))
  (.seq (.assign .local kqRc (.load .one (vv rkR)))
  (.seq (.call (some (some (.local, kqHd), none)) fInternConst [vv kqRc, vv kqUs])
  (.seq (.call (some (some (.local, kqFab), none)) ExK.fMka [vv kqHd, vv kqTa, .const 0, vv kqNp])
  (.seq (.call (some (some (.local, kqFs), none)) fFab [vv kD, vv kqFab, vv rkM])
  (.ite (.cmp .equal (vv kqFs) (.const 0)) (.return (vv rkM))
  (.seq (.call (some (some (.local, kqK2), none)) fIO [vv kFu, vv kD, vv kqFab])
  (.seq (.call (some (some (.local, kqDf), none)) fD [vv kFu, vv kD, vv kqTm, vv kqK2])
  (.ite (.cmp .equal (vv kqDf) (.const 0)) (.return (vv rkM))
  (rkCert v)))))))))))))))))))))))))
  (.return (vv rkM))))))

section
variable {σ : Type}

theorem rk_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rkLocals → (ctxEnv C ++ rkParams.zip vals).get x = none :=
  Knot.params_none C rkLocals rkParams vals (by decide) (by decide)

theorem viewLs_run (h : LsIdx) (s : AState) (v : LsNodeView) (hv : s.store.lss.view h = some v) :
    viewLs h s = .ok (v, s) := by
  show (match s.store.lss.view h with
    | some v => (pure v : AM LsNodeView)
    | none => fail (.internal "arena: dangling level-list handle")) s = _
  rw [hv]; rfl

structure RkCodes (C : Ctx) (Bfab : ProgHOL 64) : Prop where
  io : C.code.lookup fIO = some (pmap kParams, inferIOE C fIOB, .one)
  w : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one)
  d : C.code.lookup fD = some (pmap dParams, dE C, .one)
  af : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  gaa : C.code.lookup ExG.fGaa = some ([(pFu, .one), (pH, .one)], ExG.gaaBody C, .one)
  ic : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one)
  mka : C.code.lookup ExK.fMka = some ([(ExK.pF, .one), (ExK.pP, .one), (ExK.pI, .one), (ExK.pN, .one)],
    ExK.mkaBody, .one)
  ia : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)
  fab : C.code.lookup fFab = some (fbParams.map (fun p => (p, ShapeHOL.one)), Bfab, .one)
  pi : C.code.lookup fPi = some (piParams.map (fun p => (p, ShapeHOL.one)), piBody C, .one)
  eqv : C.code.lookup LLeq.fEqv = some ([(LEq.pLa, .one), (LEq.pLb, .one)], LLeq.eqvBody, .one)

theorem rk_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (Bfab : ProgHOL 64) (hc : RkCodes C Bfab)
    (s : AState) (d : Nat) (rl : IRecRule) (qr : Nat) (cvj : IConstantVal) (cnP nF : Nat) (T : NIdx) (qj : Nat)
    (m : EIdx) (hrule : RuleE C.EB C.EH qr rl) (hcij : CIE C.EB C.EH qj (.ctorInfo cvj cnP nF T))
    (hIO : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ e', Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e'] (inferIOE C fIOB) s1 ((knot mode C n).inferIO d e')
      (PostK (ctxH C H)))
    (hW : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ e', Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d e')
      (PostK (ctxH C H)))
    (hD : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ a b, Callee (σ := σ) (ctxH C H) dParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (dE C) s1 ((knot mode C n).defeq d a b)
      (PostB (ctxH C H)))
    (hFab : ∀ (H : List (BitVec 64)) s1 (f mj : EIdx), C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s1 (fbParams.zip [BitVec.ofNat 64 d, Enc.idxW f, Enc.idxW mj])) Bfab s1
        (fabScopeOk d f mj) (PostB (ctxH C H)))
    (hLE : ∀ (H : List (BitVec 64)) s1 (u v : LIdx), C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s1 [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s1 (lvlEq? u v)
        (LLeq.PostOB (ctxH C H))) :
    SpecR (σ := σ) (Pre C s (rkParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, ecell C qr, ecell C qj, Enc.idxW T,
      Enc.idxW m])) (rkBody mode.verifiedChecks) s (rescueK mode (knot mode C n) C.fe d rl cvj cnP T m) (PostK C) := by
  refine specR_prologue (Knot.postK_locals C) (rk_none C _) ?_
  unfold rescueK
  have hretM : ∀ {Γ : Env} {M : Mem} {H : List (BitVec 64)} {s2 : AState}, C.H <+: H → Γ.get rkM = some (Enc.idxW m) →
      SpecR (σ := σ) (Inv (ctxH C H) s2 Γ M (ctxLocals ++ rkLocals)) (.return (vv rkM)) s2 (pure m) (PostK C) :=
    fun hp hE => specR_returnI _ (Enc.idxW m) (by simpa using hE)
      (fun t ht => ⟨_, hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine Big.specR_callKC kq1 fIO kParams [vv kFu, vv kD, vv rkM] (inferIOE C fIOB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW m] (by decide) rfl (by decide) hc.io
    ⟨by simp +decide [Env.get, rkParams, ctxEnv], by simp +decide [Env.get, rkParams, ctxEnv],
      by simp +decide [Env.get, rkParams, ctxEnv], trivial⟩ (hIO C.H s (List.prefix_refl _) m)
    (fun k1 s1 H1 hp1 _ => ?_)
  refine Big.specR_callKC (C := ctxH C H1) kqTm fW kParams [vv kFu, vv kD, vv kq1] (whnfE C fWB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW k1] (by decide) rfl (by decide) hc.w
    ⟨by simp +decide [Env.get, rkParams, ctxEnv], by simp +decide [Env.get, rkParams, ctxEnv], by simp, trivial⟩
    (hW H1 s1 hp1 k1) (fun tm s2 H2 hp2 _ => ?_)
  have hp12 : C.H <+: H2 := hp1.trans hp2
  have hok2 := ctxOK_H hok H2
  refine specR_callNIM (C := ctxH C H2) kqHh fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv kqTm]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW tm] (by decide) rfl (by decide) hc.af
    ⟨rfl, by simp, trivial⟩
    (fun a w s' st => getAppFn coreWalkFuel tm s2 = .ok (a, s') ∧ Post (ctxH C H2) s2 a w s' st)
    (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec (ctxH C H2) hc.af coreWalkFuel tm s2 CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide),
        hlk 1 (by decide)⟩))
    (fun hh w s' st ⟨hrun2, hw, hs, _⟩ => ?_)
  subst hw
  have hs' : s2 = s' := hs.symm
  subst hs'
  refine Knot.specR_tagIteV kqHh hh 3 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
  swap
  · rw [if_neg (show ¬ (hh.tag == ETag.const) = true by simpa [ETag.const] using htg)]
    exact hretM hp12 (by simp +decide [Env.get, rkParams, ctxEnv])
  rw [if_pos (show (hh.tag == ETag.const) = true by simp [htg, ETag.const])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv kqHh) (Enc.idxW hh) (by decide) (by simp) ?_
  refine ILP.specR_viewIv (C := ctxH C H2) hh (by simp) (by simp +decide [Env.get, ctxEnv] <;> rfl)
    (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
  have h3 : v.tagN = 3 := by rw [htn, htg]; rfl
  obtain ⟨T', ust, rfl⟩ := UD.tagN_const h3
  dsimp only
  refine specR_loadI' kqTp (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW T') (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW T') [Enc.idxW ust] []) ?_
  refine specR_loadI' kqUs _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW ust) (by decide) (by simp +decide [sev]) rfl
    (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW T') (Enc.idxW ust) [] []) ?_
  refine specR_dropM ?_
  refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv kqUs) (Enc.idxW ust) (by decide) (by simp) ?_
  refine specR_lsviewPI (C := ctxH C H2) ust (by simp) (by simp +decide [Env.get, ctxEnv] <;> rfl)
    (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun vl Pl hvl _ hvll => ?_)
  refine specR_runBind (viewLs_run ust s2 vl hvl) ?_
  have hcij' := hcij
  obtain ⟨⟨_, ⟨wl, hwl, hlps⟩, _⟩, _, hnp, _, hind⟩ := hcij'
  simp only [IConstantInfo.toConstantVal] at hlps
  obtain ⟨ol, hwol, hblk⟩ := hlps
  refine specR_envLoadI (C := ctxH C H2) kqLp (.op .add [vv rkJ, .const 16]) (qj + 2) _ (by decide)
    (by simp +decide [sev, Env.get, rkParams, ctxEnv]; exact UD.ecell_add16 C qj)
    (by rw [show qj + 2 = qj + 1 + 1 by omega]; exact hwl) ?_
  refine specR_envLoadI (C := ctxH C H2) kqLl (vv kqLp) ol _ (by decide) (by simp [hwol]; rfl) hblk.1 ?_
  refine specR_atEntry fun t2 ht2 => ?_
  have hlpl : cvj.levelParams.length < 2 ^ 61 := by
    have h1 := blkAt_len (show BlkAt C.EH ol (cvj.levelParams.map Enc.idxW) from hblk)
    have h2 := ht2.sr.env.1.len; have h3 := hok.envLay
    simp only [List.length_map] at h1; simp only [ctxH] at h2; omega
  have hvl' : vl.length < 2 ^ 61 := by simpa using hvll
  by_cases hT : T' = T
  swap
  · have hne : Enc.idxW T' ≠ Enc.idxW T := fun e => hT (Enc.idxW_inj e)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, rkParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [if_neg (by simp [hT])]
    exact hretM hp12 (by simp +decide [Env.get, rkParams, ctxEnv])
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, rkParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hT])
    (fun h => absurd rfl h) (fun _ => ?_)
  by_cases hL : cvj.levelParams.length = vl.length
  swap
  · have hne : BitVec.ofNat 64 cvj.levelParams.length ≠ BitVec.ofNat 64 vl.length := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    rw [if_neg (by simp [hL])]
    exact hretM hp12 (by simp +decide [Env.get, rkParams, ctxEnv])
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hL]) (fun h => absurd rfl h)
    (fun _ => ?_)
  rw [if_pos ⟨hT, hL⟩]
  refine specR_callNIH (C := ctxH C H2) kqTa ExG.fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv kqTm]
    (ExG.gaaBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW tm] (by decide) rfl (by decide) hc.gaa
    ⟨rfl, by simp, trivial⟩
    (PostA (ctxH C H2)) (fun a w _ H3 => ∃ o3, w = cellA C o3 ∧ BlkAt H3 o3 (a.map Enc.idxW))
    (fun a w s' st ⟨H3, o3, hp, hw, hb, hsr⟩ => ⟨H3, hp, ⟨o3, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (ExG.gaa_spec (ctxH C H2) hok2 hc.gaa coreWalkFuel CV.coreWalkFuel_lt H2 tm s2))
    (fun targs w s3 H3 hp3 ⟨oa, hw, hba⟩ => ?_)
  subst hw
  have hp13 : C.H <+: H3 := hp12.trans hp3
  have hok3 := ctxOK_H hok H3
  refine UD.specR_heapLoadI' (C := ctxH C H3) kqTl (vv kqTa) oa _ hba.1 (by decide) (by simp; rfl) ?_
  refine specR_envLoadI (C := ctxH C H3) kqNp (.op .add [vv rkJ, .const 32]) (qj + 4) _ (by decide)
    (by simp +decide [sev, Env.get, rkParams, ctxEnv]; exact UD.ecell_add32 C qj) hnp.1 ?_
  refine specR_atEntry fun t3 ht3 => ?_
  have htl := blk_small0 hok3 ht3.sr hba
  simp only [List.length_map] at htl
  have hnp2 := hnp.2
  have hlw := word_lt_iff targs.length cnP (by unfold B; omega) (by unfold B; omega)
  by_cases hle : cnP ≤ targs.length
  swap
  · refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr (by omega)]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    rw [if_neg hle]
    exact hretM hp13 (by simp +decide [Env.get, rkParams, ctxEnv])
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega) (fun h => absurd rfl h)
    (fun _ => ?_)
  rw [if_pos hle]
  refine specR_envLoadI (C := ctxH C H3) kqRc (vv rkR) qr _ (by decide) (by simp +decide [Env.get, rkParams, ctxEnv]; rfl)
    hrule.1 ?_
  refine ILP.callE_spec (C := ctxH C H3) kqHd fInternConst [lEn, lEus] [vv kqRc, vv kqUs] constBody
    [Enc.idxW rl.ctor, Enc.idxW ust] (by decide) rfl (by decide) hc.ic ⟨by simp, by simp, trivial⟩
    (by exact const_body_spec ra (ctxH C H3) hok3 s3 _ _) (fun hd s4 => ?_)
  refine ILP.callE_spec (C := ctxH C H3) kqFab ExK.fMka [ExK.pF, ExK.pP, ExK.pI, ExK.pN]
    [vv kqHd, vv kqTa, .const 0, vv kqNp] ExK.mkaBody [Enc.idxW hd, cellA C oa, BitVec.ofNat 64 0, BitVec.ofNat 64 cnP]
    (by decide) rfl (by decide) hc.mka ⟨by simp, by simp, rfl, by simp, trivial⟩
    (ExK.mkAppN_take_spec ra (ctxH C H3) hok3 hc.mka hc.ia oa targs hba (by omega) cnP hle hd s4) (fun fab s5 => ?_)
  refine specR_callNIH (C := ctxH C H3) kqFs fFab fbParams [vv kD, vv kqFab, vv rkM] Bfab
    [BitVec.ofNat 64 d, Enc.idxW fab, Enc.idxW m] (by decide) rfl (by decide) hc.fab
    ⟨by simp +decide [Env.get, rkParams, ctxEnv], by simp, by simp +decide [Env.get, rkParams, ctxEnv], trivial⟩
    (PostB (ctxH C H3)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fbParams _ rfl hlk) (hFab H3 s5 fab m hp13))
    (fun fs w s6 H4 hp4 hw => ?_)
  subst hw
  have hp14 : C.H <+: H4 := hp13.trans hp4
  cases fs
  · refine specR_ifI _ 1 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [Bool.false_eq_true, ite_false]
    exact hretM hp14 (by simp +decide [Env.get, rkParams, ctxEnv])
  refine specR_ifI _ 0 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
  simp only [ite_true]
  refine Big.specR_callKC (C := ctxH C H4) kqK2 fIO kParams [vv kFu, vv kD, vv kqFab] (inferIOE C fIOB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW fab] (by decide) rfl (by decide) hc.io
    ⟨by simp +decide [Env.get, rkParams, ctxEnv], by simp +decide [Env.get, rkParams, ctxEnv], by simp, trivial⟩
    (hIO H4 s6 hp14 fab) (fun k2 s7 H5 hp5 _ => ?_)
  have hp15 : C.H <+: H5 := hp14.trans hp5
  refine specR_callNIH (C := ctxH C H5) kqDf fD dParams [vv kFu, vv kD, vv kqTm, vv kqK2] (dE C)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW tm, Enc.idxW k2] (by decide) rfl (by decide) hc.d
    ⟨by simp +decide [Env.get, rkParams, ctxEnv], by simp +decide [Env.get, rkParams, ctxEnv], by simp, by simp,
      trivial⟩
    (PostB (ctxH C H5)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
    (fun u hu _ hlk => hD H5 s7 hp15 tm k2 u hu (fun i hi _ => hlk i (by omega)))
    (fun df w s8 H6 hp6 hw => ?_)
  subst hw
  have hp16 : C.H <+: H6 := hp15.trans hp6
  cases df
  · refine specR_ifI _ 1 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [Bool.false_eq_true, ite_false]
    exact hretM hp16 (by simp +decide [Env.get, rkParams, ctxEnv])
  refine specR_ifI _ 0 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
  simp only [ite_true]
  cases hv : mode.verifiedChecks
  · simp only [rkCert, Bool.false_eq_true, ite_false, Bool.not_false, ite_true, pure_bind]
    exact specR_returnI _ (Enc.idxW fab) (by simp)
      (fun t ht => ⟨H6, hp16, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · simp only [rkCert, ite_true, Bool.not_true, Bool.false_eq_true, ite_false]
    refine specR_callNIH (C := ctxH C H6) kqIr fPi piParams [vv kFu, vv kD, vv kqFab, vv rkM] (piBody C)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW fab, Enc.idxW m] (by decide) rfl (by decide) hc.pi
      ⟨by simp +decide [Env.get, rkParams, ctxEnv], by simp +decide [Env.get, rkParams, ctxEnv], by simp,
        by simp +decide [Env.get, rkParams, ctxEnv], trivial⟩
      (PostB (ctxH C H6)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu piParams _ rfl hlk)
        (pi_spec mode n (ctxH C H6) (ctxOK_H hok H6) hc.io hc.w hc.eqv s8 d fab m
          (fun H s9 hp e' => hIO H s9 (hp16.trans hp) e') (fun H s9 hp e' => hW H s9 (hp16.trans hp) e')
          (fun H s9 u v hp => hLE H s9 u v (hp16.trans hp))))
      (fun ir w s9 H7 hp7 hw => ?_)
    subst hw
    have hp17 : C.H <+: H7 := hp16.trans hp7
    cases ir
    · refine specR_ifI _ 1 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [Bool.false_eq_true, ite_false]
      exact hretM hp17 (by simp +decide [Env.get, rkParams, ctxEnv])
    · refine specR_ifI _ 0 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      simp only [ite_true]
      exact specR_returnI _ (Enc.idxW fab) (by simp)
        (fun t ht => ⟨H7, hp17, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
