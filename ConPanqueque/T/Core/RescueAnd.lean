import ConPanqueque.T.Core.RescueEta
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# The rescue's `And` branch

At the pinned `And`: the major's type headed by `And` at the constructor's parameter count and level arity, the
`And` projection slots ready (`andRescueSlots`); the fabrication `And.intro targs (proj 0 major) (proj 1 major)`;
the scope guard, the type check, and at the verified mode the proof-irrelevance certificate.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def aqAn := ofString "aqan"
def aq1 := ofString "aq1"
def aqTm := ofString "aqtm"
def aqHh := ofString "aqhh"
def aqTp := ofString "aqtp"
def aqUs := ofString "aqus"
def aqTa := ofString "aqta"
def aqTl := ofString "aqtl"
def aqNp := ofString "aqnp"
def aqLp := ofString "aqlp"
def aqLl := ofString "aqll"
def aqAr := ofString "aqar"
def aqP0 := ofString "aqp0"
def aqP1 := ofString "aqp1"
def aqB1 := ofString "aqb1"
def aqB2 := ofString "aqb2"
def aqRc := ofString "aqrc"
def aqHd := ofString "aqhd"
def aqFl := ofString "aqfl"
def aqFab := ofString "aqfab"
def aqFs := ofString "aqfs"
def aqK2 := ofString "aqk2"
def aqDf := ofString "aqdf"
def aqIr := ofString "aqir"

@[simp] theorem aq_aqAn_ne_aq1 : aqAn ≠ aq1 := by decide
@[simp] theorem aq_aqAn_ne_aqTm : aqAn ≠ aqTm := by decide
@[simp] theorem aq_aqAn_ne_aqHh : aqAn ≠ aqHh := by decide
@[simp] theorem aq_aqAn_ne_aqTp : aqAn ≠ aqTp := by decide
@[simp] theorem aq_aqAn_ne_aqUs : aqAn ≠ aqUs := by decide
@[simp] theorem aq_aqAn_ne_aqTa : aqAn ≠ aqTa := by decide
@[simp] theorem aq_aqAn_ne_aqTl : aqAn ≠ aqTl := by decide
@[simp] theorem aq_aqAn_ne_aqNp : aqAn ≠ aqNp := by decide
@[simp] theorem aq_aqAn_ne_aqLp : aqAn ≠ aqLp := by decide
@[simp] theorem aq_aqAn_ne_aqLl : aqAn ≠ aqLl := by decide
@[simp] theorem aq_aqAn_ne_aqAr : aqAn ≠ aqAr := by decide
@[simp] theorem aq_aqAn_ne_aqP0 : aqAn ≠ aqP0 := by decide
@[simp] theorem aq_aqAn_ne_aqP1 : aqAn ≠ aqP1 := by decide
@[simp] theorem aq_aqAn_ne_aqB1 : aqAn ≠ aqB1 := by decide
@[simp] theorem aq_aqAn_ne_aqB2 : aqAn ≠ aqB2 := by decide
@[simp] theorem aq_aqAn_ne_aqRc : aqAn ≠ aqRc := by decide
@[simp] theorem aq_aqAn_ne_aqHd : aqAn ≠ aqHd := by decide
@[simp] theorem aq_aqAn_ne_aqFl : aqAn ≠ aqFl := by decide
@[simp] theorem aq_aqAn_ne_aqFab : aqAn ≠ aqFab := by decide
@[simp] theorem aq_aqAn_ne_aqFs : aqAn ≠ aqFs := by decide
@[simp] theorem aq_aqAn_ne_aqK2 : aqAn ≠ aqK2 := by decide
@[simp] theorem aq_aqAn_ne_aqDf : aqAn ≠ aqDf := by decide
@[simp] theorem aq_aqAn_ne_aqIr : aqAn ≠ aqIr := by decide
@[simp] theorem aq_aqAn_ne_lFl : aqAn ≠ lFl := by decide
@[simp] theorem aq_lFl_ne_aqAn : lFl ≠ aqAn := by decide
@[simp] theorem aq_aqAn_ne_lDh : aqAn ≠ lDh := by decide
@[simp] theorem aq_lDh_ne_aqAn : lDh ≠ aqAn := by decide
@[simp] theorem aq_aqAn_ne_lDt : aqAn ≠ lDt := by decide
@[simp] theorem aq_lDt_ne_aqAn : lDt ≠ aqAn := by decide
@[simp] theorem aq_aqAn_ne_lDg : aqAn ≠ lDg := by decide
@[simp] theorem aq_lDg_ne_aqAn : lDg ≠ aqAn := by decide
@[simp] theorem aq_aqAn_ne_lDi : aqAn ≠ lDi := by decide
@[simp] theorem aq_lDi_ne_aqAn : lDi ≠ aqAn := by decide
@[simp] theorem aq_aqAn_ne_lRp : aqAn ≠ lRp := by decide
@[simp] theorem aq_lRp_ne_aqAn : lRp ≠ aqAn := by decide
@[simp] theorem aq_aqAn_ne_lRn : aqAn ≠ lRn := by decide
@[simp] theorem aq_lRn_ne_aqAn : lRn ≠ aqAn := by decide
@[simp] theorem aq_aqAn_ne_lFle : aqAn ≠ lFle := by decide
@[simp] theorem aq_lFle_ne_aqAn : lFle ≠ aqAn := by decide
@[simp] theorem aq_aqAn_ne_lFls : aqAn ≠ lFls := by decide
@[simp] theorem aq_lFls_ne_aqAn : lFls ≠ aqAn := by decide
@[simp] theorem aq_aqAn_ne_lDir : aqAn ≠ lDir := by decide
@[simp] theorem aq_lDir_ne_aqAn : lDir ≠ aqAn := by decide
@[simp] theorem aq_aqAn_ne_lKb : aqAn ≠ lKb := by decide
@[simp] theorem aq_lKb_ne_aqAn : lKb ≠ aqAn := by decide
@[simp] theorem aq_aqAn_ne_kFu : aqAn ≠ kFu := by decide
@[simp] theorem aq_kFu_ne_aqAn : kFu ≠ aqAn := by decide
@[simp] theorem aq_aqAn_ne_kD : aqAn ≠ kD := by decide
@[simp] theorem aq_kD_ne_aqAn : kD ≠ aqAn := by decide
@[simp] theorem aq_aqAn_ne_rkR : aqAn ≠ rkR := by decide
@[simp] theorem aq_rkR_ne_aqAn : rkR ≠ aqAn := by decide
@[simp] theorem aq_aqAn_ne_rkJ : aqAn ≠ rkJ := by decide
@[simp] theorem aq_rkJ_ne_aqAn : rkJ ≠ aqAn := by decide
@[simp] theorem aq_aqAn_ne_rkT : aqAn ≠ rkT := by decide
@[simp] theorem aq_rkT_ne_aqAn : rkT ≠ aqAn := by decide
@[simp] theorem aq_aqAn_ne_rkM : aqAn ≠ rkM := by decide
@[simp] theorem aq_rkM_ne_aqAn : rkM ≠ aqAn := by decide
@[simp] theorem aq_aq1_ne_aqAn : aq1 ≠ aqAn := by decide
@[simp] theorem aq_aq1_ne_aqTm : aq1 ≠ aqTm := by decide
@[simp] theorem aq_aq1_ne_aqHh : aq1 ≠ aqHh := by decide
@[simp] theorem aq_aq1_ne_aqTp : aq1 ≠ aqTp := by decide
@[simp] theorem aq_aq1_ne_aqUs : aq1 ≠ aqUs := by decide
@[simp] theorem aq_aq1_ne_aqTa : aq1 ≠ aqTa := by decide
@[simp] theorem aq_aq1_ne_aqTl : aq1 ≠ aqTl := by decide
@[simp] theorem aq_aq1_ne_aqNp : aq1 ≠ aqNp := by decide
@[simp] theorem aq_aq1_ne_aqLp : aq1 ≠ aqLp := by decide
@[simp] theorem aq_aq1_ne_aqLl : aq1 ≠ aqLl := by decide
@[simp] theorem aq_aq1_ne_aqAr : aq1 ≠ aqAr := by decide
@[simp] theorem aq_aq1_ne_aqP0 : aq1 ≠ aqP0 := by decide
@[simp] theorem aq_aq1_ne_aqP1 : aq1 ≠ aqP1 := by decide
@[simp] theorem aq_aq1_ne_aqB1 : aq1 ≠ aqB1 := by decide
@[simp] theorem aq_aq1_ne_aqB2 : aq1 ≠ aqB2 := by decide
@[simp] theorem aq_aq1_ne_aqRc : aq1 ≠ aqRc := by decide
@[simp] theorem aq_aq1_ne_aqHd : aq1 ≠ aqHd := by decide
@[simp] theorem aq_aq1_ne_aqFl : aq1 ≠ aqFl := by decide
@[simp] theorem aq_aq1_ne_aqFab : aq1 ≠ aqFab := by decide
@[simp] theorem aq_aq1_ne_aqFs : aq1 ≠ aqFs := by decide
@[simp] theorem aq_aq1_ne_aqK2 : aq1 ≠ aqK2 := by decide
@[simp] theorem aq_aq1_ne_aqDf : aq1 ≠ aqDf := by decide
@[simp] theorem aq_aq1_ne_aqIr : aq1 ≠ aqIr := by decide
@[simp] theorem aq_aq1_ne_lFl : aq1 ≠ lFl := by decide
@[simp] theorem aq_lFl_ne_aq1 : lFl ≠ aq1 := by decide
@[simp] theorem aq_aq1_ne_lDh : aq1 ≠ lDh := by decide
@[simp] theorem aq_lDh_ne_aq1 : lDh ≠ aq1 := by decide
@[simp] theorem aq_aq1_ne_lDt : aq1 ≠ lDt := by decide
@[simp] theorem aq_lDt_ne_aq1 : lDt ≠ aq1 := by decide
@[simp] theorem aq_aq1_ne_lDg : aq1 ≠ lDg := by decide
@[simp] theorem aq_lDg_ne_aq1 : lDg ≠ aq1 := by decide
@[simp] theorem aq_aq1_ne_lDi : aq1 ≠ lDi := by decide
@[simp] theorem aq_lDi_ne_aq1 : lDi ≠ aq1 := by decide
@[simp] theorem aq_aq1_ne_lRp : aq1 ≠ lRp := by decide
@[simp] theorem aq_lRp_ne_aq1 : lRp ≠ aq1 := by decide
@[simp] theorem aq_aq1_ne_lRn : aq1 ≠ lRn := by decide
@[simp] theorem aq_lRn_ne_aq1 : lRn ≠ aq1 := by decide
@[simp] theorem aq_aq1_ne_lFle : aq1 ≠ lFle := by decide
@[simp] theorem aq_lFle_ne_aq1 : lFle ≠ aq1 := by decide
@[simp] theorem aq_aq1_ne_lFls : aq1 ≠ lFls := by decide
@[simp] theorem aq_lFls_ne_aq1 : lFls ≠ aq1 := by decide
@[simp] theorem aq_aq1_ne_lDir : aq1 ≠ lDir := by decide
@[simp] theorem aq_lDir_ne_aq1 : lDir ≠ aq1 := by decide
@[simp] theorem aq_aq1_ne_lKb : aq1 ≠ lKb := by decide
@[simp] theorem aq_lKb_ne_aq1 : lKb ≠ aq1 := by decide
@[simp] theorem aq_aq1_ne_kFu : aq1 ≠ kFu := by decide
@[simp] theorem aq_kFu_ne_aq1 : kFu ≠ aq1 := by decide
@[simp] theorem aq_aq1_ne_kD : aq1 ≠ kD := by decide
@[simp] theorem aq_kD_ne_aq1 : kD ≠ aq1 := by decide
@[simp] theorem aq_aq1_ne_rkR : aq1 ≠ rkR := by decide
@[simp] theorem aq_rkR_ne_aq1 : rkR ≠ aq1 := by decide
@[simp] theorem aq_aq1_ne_rkJ : aq1 ≠ rkJ := by decide
@[simp] theorem aq_rkJ_ne_aq1 : rkJ ≠ aq1 := by decide
@[simp] theorem aq_aq1_ne_rkT : aq1 ≠ rkT := by decide
@[simp] theorem aq_rkT_ne_aq1 : rkT ≠ aq1 := by decide
@[simp] theorem aq_aq1_ne_rkM : aq1 ≠ rkM := by decide
@[simp] theorem aq_rkM_ne_aq1 : rkM ≠ aq1 := by decide
@[simp] theorem aq_aqTm_ne_aqAn : aqTm ≠ aqAn := by decide
@[simp] theorem aq_aqTm_ne_aq1 : aqTm ≠ aq1 := by decide
@[simp] theorem aq_aqTm_ne_aqHh : aqTm ≠ aqHh := by decide
@[simp] theorem aq_aqTm_ne_aqTp : aqTm ≠ aqTp := by decide
@[simp] theorem aq_aqTm_ne_aqUs : aqTm ≠ aqUs := by decide
@[simp] theorem aq_aqTm_ne_aqTa : aqTm ≠ aqTa := by decide
@[simp] theorem aq_aqTm_ne_aqTl : aqTm ≠ aqTl := by decide
@[simp] theorem aq_aqTm_ne_aqNp : aqTm ≠ aqNp := by decide
@[simp] theorem aq_aqTm_ne_aqLp : aqTm ≠ aqLp := by decide
@[simp] theorem aq_aqTm_ne_aqLl : aqTm ≠ aqLl := by decide
@[simp] theorem aq_aqTm_ne_aqAr : aqTm ≠ aqAr := by decide
@[simp] theorem aq_aqTm_ne_aqP0 : aqTm ≠ aqP0 := by decide
@[simp] theorem aq_aqTm_ne_aqP1 : aqTm ≠ aqP1 := by decide
@[simp] theorem aq_aqTm_ne_aqB1 : aqTm ≠ aqB1 := by decide
@[simp] theorem aq_aqTm_ne_aqB2 : aqTm ≠ aqB2 := by decide
@[simp] theorem aq_aqTm_ne_aqRc : aqTm ≠ aqRc := by decide
@[simp] theorem aq_aqTm_ne_aqHd : aqTm ≠ aqHd := by decide
@[simp] theorem aq_aqTm_ne_aqFl : aqTm ≠ aqFl := by decide
@[simp] theorem aq_aqTm_ne_aqFab : aqTm ≠ aqFab := by decide
@[simp] theorem aq_aqTm_ne_aqFs : aqTm ≠ aqFs := by decide
@[simp] theorem aq_aqTm_ne_aqK2 : aqTm ≠ aqK2 := by decide
@[simp] theorem aq_aqTm_ne_aqDf : aqTm ≠ aqDf := by decide
@[simp] theorem aq_aqTm_ne_aqIr : aqTm ≠ aqIr := by decide
@[simp] theorem aq_aqTm_ne_lFl : aqTm ≠ lFl := by decide
@[simp] theorem aq_lFl_ne_aqTm : lFl ≠ aqTm := by decide
@[simp] theorem aq_aqTm_ne_lDh : aqTm ≠ lDh := by decide
@[simp] theorem aq_lDh_ne_aqTm : lDh ≠ aqTm := by decide
@[simp] theorem aq_aqTm_ne_lDt : aqTm ≠ lDt := by decide
@[simp] theorem aq_lDt_ne_aqTm : lDt ≠ aqTm := by decide
@[simp] theorem aq_aqTm_ne_lDg : aqTm ≠ lDg := by decide
@[simp] theorem aq_lDg_ne_aqTm : lDg ≠ aqTm := by decide
@[simp] theorem aq_aqTm_ne_lDi : aqTm ≠ lDi := by decide
@[simp] theorem aq_lDi_ne_aqTm : lDi ≠ aqTm := by decide
@[simp] theorem aq_aqTm_ne_lRp : aqTm ≠ lRp := by decide
@[simp] theorem aq_lRp_ne_aqTm : lRp ≠ aqTm := by decide
@[simp] theorem aq_aqTm_ne_lRn : aqTm ≠ lRn := by decide
@[simp] theorem aq_lRn_ne_aqTm : lRn ≠ aqTm := by decide
@[simp] theorem aq_aqTm_ne_lFle : aqTm ≠ lFle := by decide
@[simp] theorem aq_lFle_ne_aqTm : lFle ≠ aqTm := by decide
@[simp] theorem aq_aqTm_ne_lFls : aqTm ≠ lFls := by decide
@[simp] theorem aq_lFls_ne_aqTm : lFls ≠ aqTm := by decide
@[simp] theorem aq_aqTm_ne_lDir : aqTm ≠ lDir := by decide
@[simp] theorem aq_lDir_ne_aqTm : lDir ≠ aqTm := by decide
@[simp] theorem aq_aqTm_ne_lKb : aqTm ≠ lKb := by decide
@[simp] theorem aq_lKb_ne_aqTm : lKb ≠ aqTm := by decide
@[simp] theorem aq_aqTm_ne_kFu : aqTm ≠ kFu := by decide
@[simp] theorem aq_kFu_ne_aqTm : kFu ≠ aqTm := by decide
@[simp] theorem aq_aqTm_ne_kD : aqTm ≠ kD := by decide
@[simp] theorem aq_kD_ne_aqTm : kD ≠ aqTm := by decide
@[simp] theorem aq_aqTm_ne_rkR : aqTm ≠ rkR := by decide
@[simp] theorem aq_rkR_ne_aqTm : rkR ≠ aqTm := by decide
@[simp] theorem aq_aqTm_ne_rkJ : aqTm ≠ rkJ := by decide
@[simp] theorem aq_rkJ_ne_aqTm : rkJ ≠ aqTm := by decide
@[simp] theorem aq_aqTm_ne_rkT : aqTm ≠ rkT := by decide
@[simp] theorem aq_rkT_ne_aqTm : rkT ≠ aqTm := by decide
@[simp] theorem aq_aqTm_ne_rkM : aqTm ≠ rkM := by decide
@[simp] theorem aq_rkM_ne_aqTm : rkM ≠ aqTm := by decide
@[simp] theorem aq_aqHh_ne_aqAn : aqHh ≠ aqAn := by decide
@[simp] theorem aq_aqHh_ne_aq1 : aqHh ≠ aq1 := by decide
@[simp] theorem aq_aqHh_ne_aqTm : aqHh ≠ aqTm := by decide
@[simp] theorem aq_aqHh_ne_aqTp : aqHh ≠ aqTp := by decide
@[simp] theorem aq_aqHh_ne_aqUs : aqHh ≠ aqUs := by decide
@[simp] theorem aq_aqHh_ne_aqTa : aqHh ≠ aqTa := by decide
@[simp] theorem aq_aqHh_ne_aqTl : aqHh ≠ aqTl := by decide
@[simp] theorem aq_aqHh_ne_aqNp : aqHh ≠ aqNp := by decide
@[simp] theorem aq_aqHh_ne_aqLp : aqHh ≠ aqLp := by decide
@[simp] theorem aq_aqHh_ne_aqLl : aqHh ≠ aqLl := by decide
@[simp] theorem aq_aqHh_ne_aqAr : aqHh ≠ aqAr := by decide
@[simp] theorem aq_aqHh_ne_aqP0 : aqHh ≠ aqP0 := by decide
@[simp] theorem aq_aqHh_ne_aqP1 : aqHh ≠ aqP1 := by decide
@[simp] theorem aq_aqHh_ne_aqB1 : aqHh ≠ aqB1 := by decide
@[simp] theorem aq_aqHh_ne_aqB2 : aqHh ≠ aqB2 := by decide
@[simp] theorem aq_aqHh_ne_aqRc : aqHh ≠ aqRc := by decide
@[simp] theorem aq_aqHh_ne_aqHd : aqHh ≠ aqHd := by decide
@[simp] theorem aq_aqHh_ne_aqFl : aqHh ≠ aqFl := by decide
@[simp] theorem aq_aqHh_ne_aqFab : aqHh ≠ aqFab := by decide
@[simp] theorem aq_aqHh_ne_aqFs : aqHh ≠ aqFs := by decide
@[simp] theorem aq_aqHh_ne_aqK2 : aqHh ≠ aqK2 := by decide
@[simp] theorem aq_aqHh_ne_aqDf : aqHh ≠ aqDf := by decide
@[simp] theorem aq_aqHh_ne_aqIr : aqHh ≠ aqIr := by decide
@[simp] theorem aq_aqHh_ne_lFl : aqHh ≠ lFl := by decide
@[simp] theorem aq_lFl_ne_aqHh : lFl ≠ aqHh := by decide
@[simp] theorem aq_aqHh_ne_lDh : aqHh ≠ lDh := by decide
@[simp] theorem aq_lDh_ne_aqHh : lDh ≠ aqHh := by decide
@[simp] theorem aq_aqHh_ne_lDt : aqHh ≠ lDt := by decide
@[simp] theorem aq_lDt_ne_aqHh : lDt ≠ aqHh := by decide
@[simp] theorem aq_aqHh_ne_lDg : aqHh ≠ lDg := by decide
@[simp] theorem aq_lDg_ne_aqHh : lDg ≠ aqHh := by decide
@[simp] theorem aq_aqHh_ne_lDi : aqHh ≠ lDi := by decide
@[simp] theorem aq_lDi_ne_aqHh : lDi ≠ aqHh := by decide
@[simp] theorem aq_aqHh_ne_lRp : aqHh ≠ lRp := by decide
@[simp] theorem aq_lRp_ne_aqHh : lRp ≠ aqHh := by decide
@[simp] theorem aq_aqHh_ne_lRn : aqHh ≠ lRn := by decide
@[simp] theorem aq_lRn_ne_aqHh : lRn ≠ aqHh := by decide
@[simp] theorem aq_aqHh_ne_lFle : aqHh ≠ lFle := by decide
@[simp] theorem aq_lFle_ne_aqHh : lFle ≠ aqHh := by decide
@[simp] theorem aq_aqHh_ne_lFls : aqHh ≠ lFls := by decide
@[simp] theorem aq_lFls_ne_aqHh : lFls ≠ aqHh := by decide
@[simp] theorem aq_aqHh_ne_lDir : aqHh ≠ lDir := by decide
@[simp] theorem aq_lDir_ne_aqHh : lDir ≠ aqHh := by decide
@[simp] theorem aq_aqHh_ne_lKb : aqHh ≠ lKb := by decide
@[simp] theorem aq_lKb_ne_aqHh : lKb ≠ aqHh := by decide
@[simp] theorem aq_aqHh_ne_kFu : aqHh ≠ kFu := by decide
@[simp] theorem aq_kFu_ne_aqHh : kFu ≠ aqHh := by decide
@[simp] theorem aq_aqHh_ne_kD : aqHh ≠ kD := by decide
@[simp] theorem aq_kD_ne_aqHh : kD ≠ aqHh := by decide
@[simp] theorem aq_aqHh_ne_rkR : aqHh ≠ rkR := by decide
@[simp] theorem aq_rkR_ne_aqHh : rkR ≠ aqHh := by decide
@[simp] theorem aq_aqHh_ne_rkJ : aqHh ≠ rkJ := by decide
@[simp] theorem aq_rkJ_ne_aqHh : rkJ ≠ aqHh := by decide
@[simp] theorem aq_aqHh_ne_rkT : aqHh ≠ rkT := by decide
@[simp] theorem aq_rkT_ne_aqHh : rkT ≠ aqHh := by decide
@[simp] theorem aq_aqHh_ne_rkM : aqHh ≠ rkM := by decide
@[simp] theorem aq_rkM_ne_aqHh : rkM ≠ aqHh := by decide
@[simp] theorem aq_aqTp_ne_aqAn : aqTp ≠ aqAn := by decide
@[simp] theorem aq_aqTp_ne_aq1 : aqTp ≠ aq1 := by decide
@[simp] theorem aq_aqTp_ne_aqTm : aqTp ≠ aqTm := by decide
@[simp] theorem aq_aqTp_ne_aqHh : aqTp ≠ aqHh := by decide
@[simp] theorem aq_aqTp_ne_aqUs : aqTp ≠ aqUs := by decide
@[simp] theorem aq_aqTp_ne_aqTa : aqTp ≠ aqTa := by decide
@[simp] theorem aq_aqTp_ne_aqTl : aqTp ≠ aqTl := by decide
@[simp] theorem aq_aqTp_ne_aqNp : aqTp ≠ aqNp := by decide
@[simp] theorem aq_aqTp_ne_aqLp : aqTp ≠ aqLp := by decide
@[simp] theorem aq_aqTp_ne_aqLl : aqTp ≠ aqLl := by decide
@[simp] theorem aq_aqTp_ne_aqAr : aqTp ≠ aqAr := by decide
@[simp] theorem aq_aqTp_ne_aqP0 : aqTp ≠ aqP0 := by decide
@[simp] theorem aq_aqTp_ne_aqP1 : aqTp ≠ aqP1 := by decide
@[simp] theorem aq_aqTp_ne_aqB1 : aqTp ≠ aqB1 := by decide
@[simp] theorem aq_aqTp_ne_aqB2 : aqTp ≠ aqB2 := by decide
@[simp] theorem aq_aqTp_ne_aqRc : aqTp ≠ aqRc := by decide
@[simp] theorem aq_aqTp_ne_aqHd : aqTp ≠ aqHd := by decide
@[simp] theorem aq_aqTp_ne_aqFl : aqTp ≠ aqFl := by decide
@[simp] theorem aq_aqTp_ne_aqFab : aqTp ≠ aqFab := by decide
@[simp] theorem aq_aqTp_ne_aqFs : aqTp ≠ aqFs := by decide
@[simp] theorem aq_aqTp_ne_aqK2 : aqTp ≠ aqK2 := by decide
@[simp] theorem aq_aqTp_ne_aqDf : aqTp ≠ aqDf := by decide
@[simp] theorem aq_aqTp_ne_aqIr : aqTp ≠ aqIr := by decide
@[simp] theorem aq_aqTp_ne_lFl : aqTp ≠ lFl := by decide
@[simp] theorem aq_lFl_ne_aqTp : lFl ≠ aqTp := by decide
@[simp] theorem aq_aqTp_ne_lDh : aqTp ≠ lDh := by decide
@[simp] theorem aq_lDh_ne_aqTp : lDh ≠ aqTp := by decide
@[simp] theorem aq_aqTp_ne_lDt : aqTp ≠ lDt := by decide
@[simp] theorem aq_lDt_ne_aqTp : lDt ≠ aqTp := by decide
@[simp] theorem aq_aqTp_ne_lDg : aqTp ≠ lDg := by decide
@[simp] theorem aq_lDg_ne_aqTp : lDg ≠ aqTp := by decide
@[simp] theorem aq_aqTp_ne_lDi : aqTp ≠ lDi := by decide
@[simp] theorem aq_lDi_ne_aqTp : lDi ≠ aqTp := by decide
@[simp] theorem aq_aqTp_ne_lRp : aqTp ≠ lRp := by decide
@[simp] theorem aq_lRp_ne_aqTp : lRp ≠ aqTp := by decide
@[simp] theorem aq_aqTp_ne_lRn : aqTp ≠ lRn := by decide
@[simp] theorem aq_lRn_ne_aqTp : lRn ≠ aqTp := by decide
@[simp] theorem aq_aqTp_ne_lFle : aqTp ≠ lFle := by decide
@[simp] theorem aq_lFle_ne_aqTp : lFle ≠ aqTp := by decide
@[simp] theorem aq_aqTp_ne_lFls : aqTp ≠ lFls := by decide
@[simp] theorem aq_lFls_ne_aqTp : lFls ≠ aqTp := by decide
@[simp] theorem aq_aqTp_ne_lDir : aqTp ≠ lDir := by decide
@[simp] theorem aq_lDir_ne_aqTp : lDir ≠ aqTp := by decide
@[simp] theorem aq_aqTp_ne_lKb : aqTp ≠ lKb := by decide
@[simp] theorem aq_lKb_ne_aqTp : lKb ≠ aqTp := by decide
@[simp] theorem aq_aqTp_ne_kFu : aqTp ≠ kFu := by decide
@[simp] theorem aq_kFu_ne_aqTp : kFu ≠ aqTp := by decide
@[simp] theorem aq_aqTp_ne_kD : aqTp ≠ kD := by decide
@[simp] theorem aq_kD_ne_aqTp : kD ≠ aqTp := by decide
@[simp] theorem aq_aqTp_ne_rkR : aqTp ≠ rkR := by decide
@[simp] theorem aq_rkR_ne_aqTp : rkR ≠ aqTp := by decide
@[simp] theorem aq_aqTp_ne_rkJ : aqTp ≠ rkJ := by decide
@[simp] theorem aq_rkJ_ne_aqTp : rkJ ≠ aqTp := by decide
@[simp] theorem aq_aqTp_ne_rkT : aqTp ≠ rkT := by decide
@[simp] theorem aq_rkT_ne_aqTp : rkT ≠ aqTp := by decide
@[simp] theorem aq_aqTp_ne_rkM : aqTp ≠ rkM := by decide
@[simp] theorem aq_rkM_ne_aqTp : rkM ≠ aqTp := by decide
@[simp] theorem aq_aqUs_ne_aqAn : aqUs ≠ aqAn := by decide
@[simp] theorem aq_aqUs_ne_aq1 : aqUs ≠ aq1 := by decide
@[simp] theorem aq_aqUs_ne_aqTm : aqUs ≠ aqTm := by decide
@[simp] theorem aq_aqUs_ne_aqHh : aqUs ≠ aqHh := by decide
@[simp] theorem aq_aqUs_ne_aqTp : aqUs ≠ aqTp := by decide
@[simp] theorem aq_aqUs_ne_aqTa : aqUs ≠ aqTa := by decide
@[simp] theorem aq_aqUs_ne_aqTl : aqUs ≠ aqTl := by decide
@[simp] theorem aq_aqUs_ne_aqNp : aqUs ≠ aqNp := by decide
@[simp] theorem aq_aqUs_ne_aqLp : aqUs ≠ aqLp := by decide
@[simp] theorem aq_aqUs_ne_aqLl : aqUs ≠ aqLl := by decide
@[simp] theorem aq_aqUs_ne_aqAr : aqUs ≠ aqAr := by decide
@[simp] theorem aq_aqUs_ne_aqP0 : aqUs ≠ aqP0 := by decide
@[simp] theorem aq_aqUs_ne_aqP1 : aqUs ≠ aqP1 := by decide
@[simp] theorem aq_aqUs_ne_aqB1 : aqUs ≠ aqB1 := by decide
@[simp] theorem aq_aqUs_ne_aqB2 : aqUs ≠ aqB2 := by decide
@[simp] theorem aq_aqUs_ne_aqRc : aqUs ≠ aqRc := by decide
@[simp] theorem aq_aqUs_ne_aqHd : aqUs ≠ aqHd := by decide
@[simp] theorem aq_aqUs_ne_aqFl : aqUs ≠ aqFl := by decide
@[simp] theorem aq_aqUs_ne_aqFab : aqUs ≠ aqFab := by decide
@[simp] theorem aq_aqUs_ne_aqFs : aqUs ≠ aqFs := by decide
@[simp] theorem aq_aqUs_ne_aqK2 : aqUs ≠ aqK2 := by decide
@[simp] theorem aq_aqUs_ne_aqDf : aqUs ≠ aqDf := by decide
@[simp] theorem aq_aqUs_ne_aqIr : aqUs ≠ aqIr := by decide
@[simp] theorem aq_aqUs_ne_lFl : aqUs ≠ lFl := by decide
@[simp] theorem aq_lFl_ne_aqUs : lFl ≠ aqUs := by decide
@[simp] theorem aq_aqUs_ne_lDh : aqUs ≠ lDh := by decide
@[simp] theorem aq_lDh_ne_aqUs : lDh ≠ aqUs := by decide
@[simp] theorem aq_aqUs_ne_lDt : aqUs ≠ lDt := by decide
@[simp] theorem aq_lDt_ne_aqUs : lDt ≠ aqUs := by decide
@[simp] theorem aq_aqUs_ne_lDg : aqUs ≠ lDg := by decide
@[simp] theorem aq_lDg_ne_aqUs : lDg ≠ aqUs := by decide
@[simp] theorem aq_aqUs_ne_lDi : aqUs ≠ lDi := by decide
@[simp] theorem aq_lDi_ne_aqUs : lDi ≠ aqUs := by decide
@[simp] theorem aq_aqUs_ne_lRp : aqUs ≠ lRp := by decide
@[simp] theorem aq_lRp_ne_aqUs : lRp ≠ aqUs := by decide
@[simp] theorem aq_aqUs_ne_lRn : aqUs ≠ lRn := by decide
@[simp] theorem aq_lRn_ne_aqUs : lRn ≠ aqUs := by decide
@[simp] theorem aq_aqUs_ne_lFle : aqUs ≠ lFle := by decide
@[simp] theorem aq_lFle_ne_aqUs : lFle ≠ aqUs := by decide
@[simp] theorem aq_aqUs_ne_lFls : aqUs ≠ lFls := by decide
@[simp] theorem aq_lFls_ne_aqUs : lFls ≠ aqUs := by decide
@[simp] theorem aq_aqUs_ne_lDir : aqUs ≠ lDir := by decide
@[simp] theorem aq_lDir_ne_aqUs : lDir ≠ aqUs := by decide
@[simp] theorem aq_aqUs_ne_lKb : aqUs ≠ lKb := by decide
@[simp] theorem aq_lKb_ne_aqUs : lKb ≠ aqUs := by decide
@[simp] theorem aq_aqUs_ne_kFu : aqUs ≠ kFu := by decide
@[simp] theorem aq_kFu_ne_aqUs : kFu ≠ aqUs := by decide
@[simp] theorem aq_aqUs_ne_kD : aqUs ≠ kD := by decide
@[simp] theorem aq_kD_ne_aqUs : kD ≠ aqUs := by decide
@[simp] theorem aq_aqUs_ne_rkR : aqUs ≠ rkR := by decide
@[simp] theorem aq_rkR_ne_aqUs : rkR ≠ aqUs := by decide
@[simp] theorem aq_aqUs_ne_rkJ : aqUs ≠ rkJ := by decide
@[simp] theorem aq_rkJ_ne_aqUs : rkJ ≠ aqUs := by decide
@[simp] theorem aq_aqUs_ne_rkT : aqUs ≠ rkT := by decide
@[simp] theorem aq_rkT_ne_aqUs : rkT ≠ aqUs := by decide
@[simp] theorem aq_aqUs_ne_rkM : aqUs ≠ rkM := by decide
@[simp] theorem aq_rkM_ne_aqUs : rkM ≠ aqUs := by decide
@[simp] theorem aq_aqTa_ne_aqAn : aqTa ≠ aqAn := by decide
@[simp] theorem aq_aqTa_ne_aq1 : aqTa ≠ aq1 := by decide
@[simp] theorem aq_aqTa_ne_aqTm : aqTa ≠ aqTm := by decide
@[simp] theorem aq_aqTa_ne_aqHh : aqTa ≠ aqHh := by decide
@[simp] theorem aq_aqTa_ne_aqTp : aqTa ≠ aqTp := by decide
@[simp] theorem aq_aqTa_ne_aqUs : aqTa ≠ aqUs := by decide
@[simp] theorem aq_aqTa_ne_aqTl : aqTa ≠ aqTl := by decide
@[simp] theorem aq_aqTa_ne_aqNp : aqTa ≠ aqNp := by decide
@[simp] theorem aq_aqTa_ne_aqLp : aqTa ≠ aqLp := by decide
@[simp] theorem aq_aqTa_ne_aqLl : aqTa ≠ aqLl := by decide
@[simp] theorem aq_aqTa_ne_aqAr : aqTa ≠ aqAr := by decide
@[simp] theorem aq_aqTa_ne_aqP0 : aqTa ≠ aqP0 := by decide
@[simp] theorem aq_aqTa_ne_aqP1 : aqTa ≠ aqP1 := by decide
@[simp] theorem aq_aqTa_ne_aqB1 : aqTa ≠ aqB1 := by decide
@[simp] theorem aq_aqTa_ne_aqB2 : aqTa ≠ aqB2 := by decide
@[simp] theorem aq_aqTa_ne_aqRc : aqTa ≠ aqRc := by decide
@[simp] theorem aq_aqTa_ne_aqHd : aqTa ≠ aqHd := by decide
@[simp] theorem aq_aqTa_ne_aqFl : aqTa ≠ aqFl := by decide
@[simp] theorem aq_aqTa_ne_aqFab : aqTa ≠ aqFab := by decide
@[simp] theorem aq_aqTa_ne_aqFs : aqTa ≠ aqFs := by decide
@[simp] theorem aq_aqTa_ne_aqK2 : aqTa ≠ aqK2 := by decide
@[simp] theorem aq_aqTa_ne_aqDf : aqTa ≠ aqDf := by decide
@[simp] theorem aq_aqTa_ne_aqIr : aqTa ≠ aqIr := by decide
@[simp] theorem aq_aqTa_ne_lFl : aqTa ≠ lFl := by decide
@[simp] theorem aq_lFl_ne_aqTa : lFl ≠ aqTa := by decide
@[simp] theorem aq_aqTa_ne_lDh : aqTa ≠ lDh := by decide
@[simp] theorem aq_lDh_ne_aqTa : lDh ≠ aqTa := by decide
@[simp] theorem aq_aqTa_ne_lDt : aqTa ≠ lDt := by decide
@[simp] theorem aq_lDt_ne_aqTa : lDt ≠ aqTa := by decide
@[simp] theorem aq_aqTa_ne_lDg : aqTa ≠ lDg := by decide
@[simp] theorem aq_lDg_ne_aqTa : lDg ≠ aqTa := by decide
@[simp] theorem aq_aqTa_ne_lDi : aqTa ≠ lDi := by decide
@[simp] theorem aq_lDi_ne_aqTa : lDi ≠ aqTa := by decide
@[simp] theorem aq_aqTa_ne_lRp : aqTa ≠ lRp := by decide
@[simp] theorem aq_lRp_ne_aqTa : lRp ≠ aqTa := by decide
@[simp] theorem aq_aqTa_ne_lRn : aqTa ≠ lRn := by decide
@[simp] theorem aq_lRn_ne_aqTa : lRn ≠ aqTa := by decide
@[simp] theorem aq_aqTa_ne_lFle : aqTa ≠ lFle := by decide
@[simp] theorem aq_lFle_ne_aqTa : lFle ≠ aqTa := by decide
@[simp] theorem aq_aqTa_ne_lFls : aqTa ≠ lFls := by decide
@[simp] theorem aq_lFls_ne_aqTa : lFls ≠ aqTa := by decide
@[simp] theorem aq_aqTa_ne_lDir : aqTa ≠ lDir := by decide
@[simp] theorem aq_lDir_ne_aqTa : lDir ≠ aqTa := by decide
@[simp] theorem aq_aqTa_ne_lKb : aqTa ≠ lKb := by decide
@[simp] theorem aq_lKb_ne_aqTa : lKb ≠ aqTa := by decide
@[simp] theorem aq_aqTa_ne_kFu : aqTa ≠ kFu := by decide
@[simp] theorem aq_kFu_ne_aqTa : kFu ≠ aqTa := by decide
@[simp] theorem aq_aqTa_ne_kD : aqTa ≠ kD := by decide
@[simp] theorem aq_kD_ne_aqTa : kD ≠ aqTa := by decide
@[simp] theorem aq_aqTa_ne_rkR : aqTa ≠ rkR := by decide
@[simp] theorem aq_rkR_ne_aqTa : rkR ≠ aqTa := by decide
@[simp] theorem aq_aqTa_ne_rkJ : aqTa ≠ rkJ := by decide
@[simp] theorem aq_rkJ_ne_aqTa : rkJ ≠ aqTa := by decide
@[simp] theorem aq_aqTa_ne_rkT : aqTa ≠ rkT := by decide
@[simp] theorem aq_rkT_ne_aqTa : rkT ≠ aqTa := by decide
@[simp] theorem aq_aqTa_ne_rkM : aqTa ≠ rkM := by decide
@[simp] theorem aq_rkM_ne_aqTa : rkM ≠ aqTa := by decide
@[simp] theorem aq_aqTl_ne_aqAn : aqTl ≠ aqAn := by decide
@[simp] theorem aq_aqTl_ne_aq1 : aqTl ≠ aq1 := by decide
@[simp] theorem aq_aqTl_ne_aqTm : aqTl ≠ aqTm := by decide
@[simp] theorem aq_aqTl_ne_aqHh : aqTl ≠ aqHh := by decide
@[simp] theorem aq_aqTl_ne_aqTp : aqTl ≠ aqTp := by decide
@[simp] theorem aq_aqTl_ne_aqUs : aqTl ≠ aqUs := by decide
@[simp] theorem aq_aqTl_ne_aqTa : aqTl ≠ aqTa := by decide
@[simp] theorem aq_aqTl_ne_aqNp : aqTl ≠ aqNp := by decide
@[simp] theorem aq_aqTl_ne_aqLp : aqTl ≠ aqLp := by decide
@[simp] theorem aq_aqTl_ne_aqLl : aqTl ≠ aqLl := by decide
@[simp] theorem aq_aqTl_ne_aqAr : aqTl ≠ aqAr := by decide
@[simp] theorem aq_aqTl_ne_aqP0 : aqTl ≠ aqP0 := by decide
@[simp] theorem aq_aqTl_ne_aqP1 : aqTl ≠ aqP1 := by decide
@[simp] theorem aq_aqTl_ne_aqB1 : aqTl ≠ aqB1 := by decide
@[simp] theorem aq_aqTl_ne_aqB2 : aqTl ≠ aqB2 := by decide
@[simp] theorem aq_aqTl_ne_aqRc : aqTl ≠ aqRc := by decide
@[simp] theorem aq_aqTl_ne_aqHd : aqTl ≠ aqHd := by decide
@[simp] theorem aq_aqTl_ne_aqFl : aqTl ≠ aqFl := by decide
@[simp] theorem aq_aqTl_ne_aqFab : aqTl ≠ aqFab := by decide
@[simp] theorem aq_aqTl_ne_aqFs : aqTl ≠ aqFs := by decide
@[simp] theorem aq_aqTl_ne_aqK2 : aqTl ≠ aqK2 := by decide
@[simp] theorem aq_aqTl_ne_aqDf : aqTl ≠ aqDf := by decide
@[simp] theorem aq_aqTl_ne_aqIr : aqTl ≠ aqIr := by decide
@[simp] theorem aq_aqTl_ne_lFl : aqTl ≠ lFl := by decide
@[simp] theorem aq_lFl_ne_aqTl : lFl ≠ aqTl := by decide
@[simp] theorem aq_aqTl_ne_lDh : aqTl ≠ lDh := by decide
@[simp] theorem aq_lDh_ne_aqTl : lDh ≠ aqTl := by decide
@[simp] theorem aq_aqTl_ne_lDt : aqTl ≠ lDt := by decide
@[simp] theorem aq_lDt_ne_aqTl : lDt ≠ aqTl := by decide
@[simp] theorem aq_aqTl_ne_lDg : aqTl ≠ lDg := by decide
@[simp] theorem aq_lDg_ne_aqTl : lDg ≠ aqTl := by decide
@[simp] theorem aq_aqTl_ne_lDi : aqTl ≠ lDi := by decide
@[simp] theorem aq_lDi_ne_aqTl : lDi ≠ aqTl := by decide
@[simp] theorem aq_aqTl_ne_lRp : aqTl ≠ lRp := by decide
@[simp] theorem aq_lRp_ne_aqTl : lRp ≠ aqTl := by decide
@[simp] theorem aq_aqTl_ne_lRn : aqTl ≠ lRn := by decide
@[simp] theorem aq_lRn_ne_aqTl : lRn ≠ aqTl := by decide
@[simp] theorem aq_aqTl_ne_lFle : aqTl ≠ lFle := by decide
@[simp] theorem aq_lFle_ne_aqTl : lFle ≠ aqTl := by decide
@[simp] theorem aq_aqTl_ne_lFls : aqTl ≠ lFls := by decide
@[simp] theorem aq_lFls_ne_aqTl : lFls ≠ aqTl := by decide
@[simp] theorem aq_aqTl_ne_lDir : aqTl ≠ lDir := by decide
@[simp] theorem aq_lDir_ne_aqTl : lDir ≠ aqTl := by decide
@[simp] theorem aq_aqTl_ne_lKb : aqTl ≠ lKb := by decide
@[simp] theorem aq_lKb_ne_aqTl : lKb ≠ aqTl := by decide
@[simp] theorem aq_aqTl_ne_kFu : aqTl ≠ kFu := by decide
@[simp] theorem aq_kFu_ne_aqTl : kFu ≠ aqTl := by decide
@[simp] theorem aq_aqTl_ne_kD : aqTl ≠ kD := by decide
@[simp] theorem aq_kD_ne_aqTl : kD ≠ aqTl := by decide
@[simp] theorem aq_aqTl_ne_rkR : aqTl ≠ rkR := by decide
@[simp] theorem aq_rkR_ne_aqTl : rkR ≠ aqTl := by decide
@[simp] theorem aq_aqTl_ne_rkJ : aqTl ≠ rkJ := by decide
@[simp] theorem aq_rkJ_ne_aqTl : rkJ ≠ aqTl := by decide
@[simp] theorem aq_aqTl_ne_rkT : aqTl ≠ rkT := by decide
@[simp] theorem aq_rkT_ne_aqTl : rkT ≠ aqTl := by decide
@[simp] theorem aq_aqTl_ne_rkM : aqTl ≠ rkM := by decide
@[simp] theorem aq_rkM_ne_aqTl : rkM ≠ aqTl := by decide
@[simp] theorem aq_aqNp_ne_aqAn : aqNp ≠ aqAn := by decide
@[simp] theorem aq_aqNp_ne_aq1 : aqNp ≠ aq1 := by decide
@[simp] theorem aq_aqNp_ne_aqTm : aqNp ≠ aqTm := by decide
@[simp] theorem aq_aqNp_ne_aqHh : aqNp ≠ aqHh := by decide
@[simp] theorem aq_aqNp_ne_aqTp : aqNp ≠ aqTp := by decide
@[simp] theorem aq_aqNp_ne_aqUs : aqNp ≠ aqUs := by decide
@[simp] theorem aq_aqNp_ne_aqTa : aqNp ≠ aqTa := by decide
@[simp] theorem aq_aqNp_ne_aqTl : aqNp ≠ aqTl := by decide
@[simp] theorem aq_aqNp_ne_aqLp : aqNp ≠ aqLp := by decide
@[simp] theorem aq_aqNp_ne_aqLl : aqNp ≠ aqLl := by decide
@[simp] theorem aq_aqNp_ne_aqAr : aqNp ≠ aqAr := by decide
@[simp] theorem aq_aqNp_ne_aqP0 : aqNp ≠ aqP0 := by decide
@[simp] theorem aq_aqNp_ne_aqP1 : aqNp ≠ aqP1 := by decide
@[simp] theorem aq_aqNp_ne_aqB1 : aqNp ≠ aqB1 := by decide
@[simp] theorem aq_aqNp_ne_aqB2 : aqNp ≠ aqB2 := by decide
@[simp] theorem aq_aqNp_ne_aqRc : aqNp ≠ aqRc := by decide
@[simp] theorem aq_aqNp_ne_aqHd : aqNp ≠ aqHd := by decide
@[simp] theorem aq_aqNp_ne_aqFl : aqNp ≠ aqFl := by decide
@[simp] theorem aq_aqNp_ne_aqFab : aqNp ≠ aqFab := by decide
@[simp] theorem aq_aqNp_ne_aqFs : aqNp ≠ aqFs := by decide
@[simp] theorem aq_aqNp_ne_aqK2 : aqNp ≠ aqK2 := by decide
@[simp] theorem aq_aqNp_ne_aqDf : aqNp ≠ aqDf := by decide
@[simp] theorem aq_aqNp_ne_aqIr : aqNp ≠ aqIr := by decide
@[simp] theorem aq_aqNp_ne_lFl : aqNp ≠ lFl := by decide
@[simp] theorem aq_lFl_ne_aqNp : lFl ≠ aqNp := by decide
@[simp] theorem aq_aqNp_ne_lDh : aqNp ≠ lDh := by decide
@[simp] theorem aq_lDh_ne_aqNp : lDh ≠ aqNp := by decide
@[simp] theorem aq_aqNp_ne_lDt : aqNp ≠ lDt := by decide
@[simp] theorem aq_lDt_ne_aqNp : lDt ≠ aqNp := by decide
@[simp] theorem aq_aqNp_ne_lDg : aqNp ≠ lDg := by decide
@[simp] theorem aq_lDg_ne_aqNp : lDg ≠ aqNp := by decide
@[simp] theorem aq_aqNp_ne_lDi : aqNp ≠ lDi := by decide
@[simp] theorem aq_lDi_ne_aqNp : lDi ≠ aqNp := by decide
@[simp] theorem aq_aqNp_ne_lRp : aqNp ≠ lRp := by decide
@[simp] theorem aq_lRp_ne_aqNp : lRp ≠ aqNp := by decide
@[simp] theorem aq_aqNp_ne_lRn : aqNp ≠ lRn := by decide
@[simp] theorem aq_lRn_ne_aqNp : lRn ≠ aqNp := by decide
@[simp] theorem aq_aqNp_ne_lFle : aqNp ≠ lFle := by decide
@[simp] theorem aq_lFle_ne_aqNp : lFle ≠ aqNp := by decide
@[simp] theorem aq_aqNp_ne_lFls : aqNp ≠ lFls := by decide
@[simp] theorem aq_lFls_ne_aqNp : lFls ≠ aqNp := by decide
@[simp] theorem aq_aqNp_ne_lDir : aqNp ≠ lDir := by decide
@[simp] theorem aq_lDir_ne_aqNp : lDir ≠ aqNp := by decide
@[simp] theorem aq_aqNp_ne_lKb : aqNp ≠ lKb := by decide
@[simp] theorem aq_lKb_ne_aqNp : lKb ≠ aqNp := by decide
@[simp] theorem aq_aqNp_ne_kFu : aqNp ≠ kFu := by decide
@[simp] theorem aq_kFu_ne_aqNp : kFu ≠ aqNp := by decide
@[simp] theorem aq_aqNp_ne_kD : aqNp ≠ kD := by decide
@[simp] theorem aq_kD_ne_aqNp : kD ≠ aqNp := by decide
@[simp] theorem aq_aqNp_ne_rkR : aqNp ≠ rkR := by decide
@[simp] theorem aq_rkR_ne_aqNp : rkR ≠ aqNp := by decide
@[simp] theorem aq_aqNp_ne_rkJ : aqNp ≠ rkJ := by decide
@[simp] theorem aq_rkJ_ne_aqNp : rkJ ≠ aqNp := by decide
@[simp] theorem aq_aqNp_ne_rkT : aqNp ≠ rkT := by decide
@[simp] theorem aq_rkT_ne_aqNp : rkT ≠ aqNp := by decide
@[simp] theorem aq_aqNp_ne_rkM : aqNp ≠ rkM := by decide
@[simp] theorem aq_rkM_ne_aqNp : rkM ≠ aqNp := by decide
@[simp] theorem aq_aqLp_ne_aqAn : aqLp ≠ aqAn := by decide
@[simp] theorem aq_aqLp_ne_aq1 : aqLp ≠ aq1 := by decide
@[simp] theorem aq_aqLp_ne_aqTm : aqLp ≠ aqTm := by decide
@[simp] theorem aq_aqLp_ne_aqHh : aqLp ≠ aqHh := by decide
@[simp] theorem aq_aqLp_ne_aqTp : aqLp ≠ aqTp := by decide
@[simp] theorem aq_aqLp_ne_aqUs : aqLp ≠ aqUs := by decide
@[simp] theorem aq_aqLp_ne_aqTa : aqLp ≠ aqTa := by decide
@[simp] theorem aq_aqLp_ne_aqTl : aqLp ≠ aqTl := by decide
@[simp] theorem aq_aqLp_ne_aqNp : aqLp ≠ aqNp := by decide
@[simp] theorem aq_aqLp_ne_aqLl : aqLp ≠ aqLl := by decide
@[simp] theorem aq_aqLp_ne_aqAr : aqLp ≠ aqAr := by decide
@[simp] theorem aq_aqLp_ne_aqP0 : aqLp ≠ aqP0 := by decide
@[simp] theorem aq_aqLp_ne_aqP1 : aqLp ≠ aqP1 := by decide
@[simp] theorem aq_aqLp_ne_aqB1 : aqLp ≠ aqB1 := by decide
@[simp] theorem aq_aqLp_ne_aqB2 : aqLp ≠ aqB2 := by decide
@[simp] theorem aq_aqLp_ne_aqRc : aqLp ≠ aqRc := by decide
@[simp] theorem aq_aqLp_ne_aqHd : aqLp ≠ aqHd := by decide
@[simp] theorem aq_aqLp_ne_aqFl : aqLp ≠ aqFl := by decide
@[simp] theorem aq_aqLp_ne_aqFab : aqLp ≠ aqFab := by decide
@[simp] theorem aq_aqLp_ne_aqFs : aqLp ≠ aqFs := by decide
@[simp] theorem aq_aqLp_ne_aqK2 : aqLp ≠ aqK2 := by decide
@[simp] theorem aq_aqLp_ne_aqDf : aqLp ≠ aqDf := by decide
@[simp] theorem aq_aqLp_ne_aqIr : aqLp ≠ aqIr := by decide
@[simp] theorem aq_aqLp_ne_lFl : aqLp ≠ lFl := by decide
@[simp] theorem aq_lFl_ne_aqLp : lFl ≠ aqLp := by decide
@[simp] theorem aq_aqLp_ne_lDh : aqLp ≠ lDh := by decide
@[simp] theorem aq_lDh_ne_aqLp : lDh ≠ aqLp := by decide
@[simp] theorem aq_aqLp_ne_lDt : aqLp ≠ lDt := by decide
@[simp] theorem aq_lDt_ne_aqLp : lDt ≠ aqLp := by decide
@[simp] theorem aq_aqLp_ne_lDg : aqLp ≠ lDg := by decide
@[simp] theorem aq_lDg_ne_aqLp : lDg ≠ aqLp := by decide
@[simp] theorem aq_aqLp_ne_lDi : aqLp ≠ lDi := by decide
@[simp] theorem aq_lDi_ne_aqLp : lDi ≠ aqLp := by decide
@[simp] theorem aq_aqLp_ne_lRp : aqLp ≠ lRp := by decide
@[simp] theorem aq_lRp_ne_aqLp : lRp ≠ aqLp := by decide
@[simp] theorem aq_aqLp_ne_lRn : aqLp ≠ lRn := by decide
@[simp] theorem aq_lRn_ne_aqLp : lRn ≠ aqLp := by decide
@[simp] theorem aq_aqLp_ne_lFle : aqLp ≠ lFle := by decide
@[simp] theorem aq_lFle_ne_aqLp : lFle ≠ aqLp := by decide
@[simp] theorem aq_aqLp_ne_lFls : aqLp ≠ lFls := by decide
@[simp] theorem aq_lFls_ne_aqLp : lFls ≠ aqLp := by decide
@[simp] theorem aq_aqLp_ne_lDir : aqLp ≠ lDir := by decide
@[simp] theorem aq_lDir_ne_aqLp : lDir ≠ aqLp := by decide
@[simp] theorem aq_aqLp_ne_lKb : aqLp ≠ lKb := by decide
@[simp] theorem aq_lKb_ne_aqLp : lKb ≠ aqLp := by decide
@[simp] theorem aq_aqLp_ne_kFu : aqLp ≠ kFu := by decide
@[simp] theorem aq_kFu_ne_aqLp : kFu ≠ aqLp := by decide
@[simp] theorem aq_aqLp_ne_kD : aqLp ≠ kD := by decide
@[simp] theorem aq_kD_ne_aqLp : kD ≠ aqLp := by decide
@[simp] theorem aq_aqLp_ne_rkR : aqLp ≠ rkR := by decide
@[simp] theorem aq_rkR_ne_aqLp : rkR ≠ aqLp := by decide
@[simp] theorem aq_aqLp_ne_rkJ : aqLp ≠ rkJ := by decide
@[simp] theorem aq_rkJ_ne_aqLp : rkJ ≠ aqLp := by decide
@[simp] theorem aq_aqLp_ne_rkT : aqLp ≠ rkT := by decide
@[simp] theorem aq_rkT_ne_aqLp : rkT ≠ aqLp := by decide
@[simp] theorem aq_aqLp_ne_rkM : aqLp ≠ rkM := by decide
@[simp] theorem aq_rkM_ne_aqLp : rkM ≠ aqLp := by decide
@[simp] theorem aq_aqLl_ne_aqAn : aqLl ≠ aqAn := by decide
@[simp] theorem aq_aqLl_ne_aq1 : aqLl ≠ aq1 := by decide
@[simp] theorem aq_aqLl_ne_aqTm : aqLl ≠ aqTm := by decide
@[simp] theorem aq_aqLl_ne_aqHh : aqLl ≠ aqHh := by decide
@[simp] theorem aq_aqLl_ne_aqTp : aqLl ≠ aqTp := by decide
@[simp] theorem aq_aqLl_ne_aqUs : aqLl ≠ aqUs := by decide
@[simp] theorem aq_aqLl_ne_aqTa : aqLl ≠ aqTa := by decide
@[simp] theorem aq_aqLl_ne_aqTl : aqLl ≠ aqTl := by decide
@[simp] theorem aq_aqLl_ne_aqNp : aqLl ≠ aqNp := by decide
@[simp] theorem aq_aqLl_ne_aqLp : aqLl ≠ aqLp := by decide
@[simp] theorem aq_aqLl_ne_aqAr : aqLl ≠ aqAr := by decide
@[simp] theorem aq_aqLl_ne_aqP0 : aqLl ≠ aqP0 := by decide
@[simp] theorem aq_aqLl_ne_aqP1 : aqLl ≠ aqP1 := by decide
@[simp] theorem aq_aqLl_ne_aqB1 : aqLl ≠ aqB1 := by decide
@[simp] theorem aq_aqLl_ne_aqB2 : aqLl ≠ aqB2 := by decide
@[simp] theorem aq_aqLl_ne_aqRc : aqLl ≠ aqRc := by decide
@[simp] theorem aq_aqLl_ne_aqHd : aqLl ≠ aqHd := by decide
@[simp] theorem aq_aqLl_ne_aqFl : aqLl ≠ aqFl := by decide
@[simp] theorem aq_aqLl_ne_aqFab : aqLl ≠ aqFab := by decide
@[simp] theorem aq_aqLl_ne_aqFs : aqLl ≠ aqFs := by decide
@[simp] theorem aq_aqLl_ne_aqK2 : aqLl ≠ aqK2 := by decide
@[simp] theorem aq_aqLl_ne_aqDf : aqLl ≠ aqDf := by decide
@[simp] theorem aq_aqLl_ne_aqIr : aqLl ≠ aqIr := by decide
@[simp] theorem aq_aqLl_ne_lFl : aqLl ≠ lFl := by decide
@[simp] theorem aq_lFl_ne_aqLl : lFl ≠ aqLl := by decide
@[simp] theorem aq_aqLl_ne_lDh : aqLl ≠ lDh := by decide
@[simp] theorem aq_lDh_ne_aqLl : lDh ≠ aqLl := by decide
@[simp] theorem aq_aqLl_ne_lDt : aqLl ≠ lDt := by decide
@[simp] theorem aq_lDt_ne_aqLl : lDt ≠ aqLl := by decide
@[simp] theorem aq_aqLl_ne_lDg : aqLl ≠ lDg := by decide
@[simp] theorem aq_lDg_ne_aqLl : lDg ≠ aqLl := by decide
@[simp] theorem aq_aqLl_ne_lDi : aqLl ≠ lDi := by decide
@[simp] theorem aq_lDi_ne_aqLl : lDi ≠ aqLl := by decide
@[simp] theorem aq_aqLl_ne_lRp : aqLl ≠ lRp := by decide
@[simp] theorem aq_lRp_ne_aqLl : lRp ≠ aqLl := by decide
@[simp] theorem aq_aqLl_ne_lRn : aqLl ≠ lRn := by decide
@[simp] theorem aq_lRn_ne_aqLl : lRn ≠ aqLl := by decide
@[simp] theorem aq_aqLl_ne_lFle : aqLl ≠ lFle := by decide
@[simp] theorem aq_lFle_ne_aqLl : lFle ≠ aqLl := by decide
@[simp] theorem aq_aqLl_ne_lFls : aqLl ≠ lFls := by decide
@[simp] theorem aq_lFls_ne_aqLl : lFls ≠ aqLl := by decide
@[simp] theorem aq_aqLl_ne_lDir : aqLl ≠ lDir := by decide
@[simp] theorem aq_lDir_ne_aqLl : lDir ≠ aqLl := by decide
@[simp] theorem aq_aqLl_ne_lKb : aqLl ≠ lKb := by decide
@[simp] theorem aq_lKb_ne_aqLl : lKb ≠ aqLl := by decide
@[simp] theorem aq_aqLl_ne_kFu : aqLl ≠ kFu := by decide
@[simp] theorem aq_kFu_ne_aqLl : kFu ≠ aqLl := by decide
@[simp] theorem aq_aqLl_ne_kD : aqLl ≠ kD := by decide
@[simp] theorem aq_kD_ne_aqLl : kD ≠ aqLl := by decide
@[simp] theorem aq_aqLl_ne_rkR : aqLl ≠ rkR := by decide
@[simp] theorem aq_rkR_ne_aqLl : rkR ≠ aqLl := by decide
@[simp] theorem aq_aqLl_ne_rkJ : aqLl ≠ rkJ := by decide
@[simp] theorem aq_rkJ_ne_aqLl : rkJ ≠ aqLl := by decide
@[simp] theorem aq_aqLl_ne_rkT : aqLl ≠ rkT := by decide
@[simp] theorem aq_rkT_ne_aqLl : rkT ≠ aqLl := by decide
@[simp] theorem aq_aqLl_ne_rkM : aqLl ≠ rkM := by decide
@[simp] theorem aq_rkM_ne_aqLl : rkM ≠ aqLl := by decide
@[simp] theorem aq_aqAr_ne_aqAn : aqAr ≠ aqAn := by decide
@[simp] theorem aq_aqAr_ne_aq1 : aqAr ≠ aq1 := by decide
@[simp] theorem aq_aqAr_ne_aqTm : aqAr ≠ aqTm := by decide
@[simp] theorem aq_aqAr_ne_aqHh : aqAr ≠ aqHh := by decide
@[simp] theorem aq_aqAr_ne_aqTp : aqAr ≠ aqTp := by decide
@[simp] theorem aq_aqAr_ne_aqUs : aqAr ≠ aqUs := by decide
@[simp] theorem aq_aqAr_ne_aqTa : aqAr ≠ aqTa := by decide
@[simp] theorem aq_aqAr_ne_aqTl : aqAr ≠ aqTl := by decide
@[simp] theorem aq_aqAr_ne_aqNp : aqAr ≠ aqNp := by decide
@[simp] theorem aq_aqAr_ne_aqLp : aqAr ≠ aqLp := by decide
@[simp] theorem aq_aqAr_ne_aqLl : aqAr ≠ aqLl := by decide
@[simp] theorem aq_aqAr_ne_aqP0 : aqAr ≠ aqP0 := by decide
@[simp] theorem aq_aqAr_ne_aqP1 : aqAr ≠ aqP1 := by decide
@[simp] theorem aq_aqAr_ne_aqB1 : aqAr ≠ aqB1 := by decide
@[simp] theorem aq_aqAr_ne_aqB2 : aqAr ≠ aqB2 := by decide
@[simp] theorem aq_aqAr_ne_aqRc : aqAr ≠ aqRc := by decide
@[simp] theorem aq_aqAr_ne_aqHd : aqAr ≠ aqHd := by decide
@[simp] theorem aq_aqAr_ne_aqFl : aqAr ≠ aqFl := by decide
@[simp] theorem aq_aqAr_ne_aqFab : aqAr ≠ aqFab := by decide
@[simp] theorem aq_aqAr_ne_aqFs : aqAr ≠ aqFs := by decide
@[simp] theorem aq_aqAr_ne_aqK2 : aqAr ≠ aqK2 := by decide
@[simp] theorem aq_aqAr_ne_aqDf : aqAr ≠ aqDf := by decide
@[simp] theorem aq_aqAr_ne_aqIr : aqAr ≠ aqIr := by decide
@[simp] theorem aq_aqAr_ne_lFl : aqAr ≠ lFl := by decide
@[simp] theorem aq_lFl_ne_aqAr : lFl ≠ aqAr := by decide
@[simp] theorem aq_aqAr_ne_lDh : aqAr ≠ lDh := by decide
@[simp] theorem aq_lDh_ne_aqAr : lDh ≠ aqAr := by decide
@[simp] theorem aq_aqAr_ne_lDt : aqAr ≠ lDt := by decide
@[simp] theorem aq_lDt_ne_aqAr : lDt ≠ aqAr := by decide
@[simp] theorem aq_aqAr_ne_lDg : aqAr ≠ lDg := by decide
@[simp] theorem aq_lDg_ne_aqAr : lDg ≠ aqAr := by decide
@[simp] theorem aq_aqAr_ne_lDi : aqAr ≠ lDi := by decide
@[simp] theorem aq_lDi_ne_aqAr : lDi ≠ aqAr := by decide
@[simp] theorem aq_aqAr_ne_lRp : aqAr ≠ lRp := by decide
@[simp] theorem aq_lRp_ne_aqAr : lRp ≠ aqAr := by decide
@[simp] theorem aq_aqAr_ne_lRn : aqAr ≠ lRn := by decide
@[simp] theorem aq_lRn_ne_aqAr : lRn ≠ aqAr := by decide
@[simp] theorem aq_aqAr_ne_lFle : aqAr ≠ lFle := by decide
@[simp] theorem aq_lFle_ne_aqAr : lFle ≠ aqAr := by decide
@[simp] theorem aq_aqAr_ne_lFls : aqAr ≠ lFls := by decide
@[simp] theorem aq_lFls_ne_aqAr : lFls ≠ aqAr := by decide
@[simp] theorem aq_aqAr_ne_lDir : aqAr ≠ lDir := by decide
@[simp] theorem aq_lDir_ne_aqAr : lDir ≠ aqAr := by decide
@[simp] theorem aq_aqAr_ne_lKb : aqAr ≠ lKb := by decide
@[simp] theorem aq_lKb_ne_aqAr : lKb ≠ aqAr := by decide
@[simp] theorem aq_aqAr_ne_kFu : aqAr ≠ kFu := by decide
@[simp] theorem aq_kFu_ne_aqAr : kFu ≠ aqAr := by decide
@[simp] theorem aq_aqAr_ne_kD : aqAr ≠ kD := by decide
@[simp] theorem aq_kD_ne_aqAr : kD ≠ aqAr := by decide
@[simp] theorem aq_aqAr_ne_rkR : aqAr ≠ rkR := by decide
@[simp] theorem aq_rkR_ne_aqAr : rkR ≠ aqAr := by decide
@[simp] theorem aq_aqAr_ne_rkJ : aqAr ≠ rkJ := by decide
@[simp] theorem aq_rkJ_ne_aqAr : rkJ ≠ aqAr := by decide
@[simp] theorem aq_aqAr_ne_rkT : aqAr ≠ rkT := by decide
@[simp] theorem aq_rkT_ne_aqAr : rkT ≠ aqAr := by decide
@[simp] theorem aq_aqAr_ne_rkM : aqAr ≠ rkM := by decide
@[simp] theorem aq_rkM_ne_aqAr : rkM ≠ aqAr := by decide
@[simp] theorem aq_aqP0_ne_aqAn : aqP0 ≠ aqAn := by decide
@[simp] theorem aq_aqP0_ne_aq1 : aqP0 ≠ aq1 := by decide
@[simp] theorem aq_aqP0_ne_aqTm : aqP0 ≠ aqTm := by decide
@[simp] theorem aq_aqP0_ne_aqHh : aqP0 ≠ aqHh := by decide
@[simp] theorem aq_aqP0_ne_aqTp : aqP0 ≠ aqTp := by decide
@[simp] theorem aq_aqP0_ne_aqUs : aqP0 ≠ aqUs := by decide
@[simp] theorem aq_aqP0_ne_aqTa : aqP0 ≠ aqTa := by decide
@[simp] theorem aq_aqP0_ne_aqTl : aqP0 ≠ aqTl := by decide
@[simp] theorem aq_aqP0_ne_aqNp : aqP0 ≠ aqNp := by decide
@[simp] theorem aq_aqP0_ne_aqLp : aqP0 ≠ aqLp := by decide
@[simp] theorem aq_aqP0_ne_aqLl : aqP0 ≠ aqLl := by decide
@[simp] theorem aq_aqP0_ne_aqAr : aqP0 ≠ aqAr := by decide
@[simp] theorem aq_aqP0_ne_aqP1 : aqP0 ≠ aqP1 := by decide
@[simp] theorem aq_aqP0_ne_aqB1 : aqP0 ≠ aqB1 := by decide
@[simp] theorem aq_aqP0_ne_aqB2 : aqP0 ≠ aqB2 := by decide
@[simp] theorem aq_aqP0_ne_aqRc : aqP0 ≠ aqRc := by decide
@[simp] theorem aq_aqP0_ne_aqHd : aqP0 ≠ aqHd := by decide
@[simp] theorem aq_aqP0_ne_aqFl : aqP0 ≠ aqFl := by decide
@[simp] theorem aq_aqP0_ne_aqFab : aqP0 ≠ aqFab := by decide
@[simp] theorem aq_aqP0_ne_aqFs : aqP0 ≠ aqFs := by decide
@[simp] theorem aq_aqP0_ne_aqK2 : aqP0 ≠ aqK2 := by decide
@[simp] theorem aq_aqP0_ne_aqDf : aqP0 ≠ aqDf := by decide
@[simp] theorem aq_aqP0_ne_aqIr : aqP0 ≠ aqIr := by decide
@[simp] theorem aq_aqP0_ne_lFl : aqP0 ≠ lFl := by decide
@[simp] theorem aq_lFl_ne_aqP0 : lFl ≠ aqP0 := by decide
@[simp] theorem aq_aqP0_ne_lDh : aqP0 ≠ lDh := by decide
@[simp] theorem aq_lDh_ne_aqP0 : lDh ≠ aqP0 := by decide
@[simp] theorem aq_aqP0_ne_lDt : aqP0 ≠ lDt := by decide
@[simp] theorem aq_lDt_ne_aqP0 : lDt ≠ aqP0 := by decide
@[simp] theorem aq_aqP0_ne_lDg : aqP0 ≠ lDg := by decide
@[simp] theorem aq_lDg_ne_aqP0 : lDg ≠ aqP0 := by decide
@[simp] theorem aq_aqP0_ne_lDi : aqP0 ≠ lDi := by decide
@[simp] theorem aq_lDi_ne_aqP0 : lDi ≠ aqP0 := by decide
@[simp] theorem aq_aqP0_ne_lRp : aqP0 ≠ lRp := by decide
@[simp] theorem aq_lRp_ne_aqP0 : lRp ≠ aqP0 := by decide
@[simp] theorem aq_aqP0_ne_lRn : aqP0 ≠ lRn := by decide
@[simp] theorem aq_lRn_ne_aqP0 : lRn ≠ aqP0 := by decide
@[simp] theorem aq_aqP0_ne_lFle : aqP0 ≠ lFle := by decide
@[simp] theorem aq_lFle_ne_aqP0 : lFle ≠ aqP0 := by decide
@[simp] theorem aq_aqP0_ne_lFls : aqP0 ≠ lFls := by decide
@[simp] theorem aq_lFls_ne_aqP0 : lFls ≠ aqP0 := by decide
@[simp] theorem aq_aqP0_ne_lDir : aqP0 ≠ lDir := by decide
@[simp] theorem aq_lDir_ne_aqP0 : lDir ≠ aqP0 := by decide
@[simp] theorem aq_aqP0_ne_lKb : aqP0 ≠ lKb := by decide
@[simp] theorem aq_lKb_ne_aqP0 : lKb ≠ aqP0 := by decide
@[simp] theorem aq_aqP0_ne_kFu : aqP0 ≠ kFu := by decide
@[simp] theorem aq_kFu_ne_aqP0 : kFu ≠ aqP0 := by decide
@[simp] theorem aq_aqP0_ne_kD : aqP0 ≠ kD := by decide
@[simp] theorem aq_kD_ne_aqP0 : kD ≠ aqP0 := by decide
@[simp] theorem aq_aqP0_ne_rkR : aqP0 ≠ rkR := by decide
@[simp] theorem aq_rkR_ne_aqP0 : rkR ≠ aqP0 := by decide
@[simp] theorem aq_aqP0_ne_rkJ : aqP0 ≠ rkJ := by decide
@[simp] theorem aq_rkJ_ne_aqP0 : rkJ ≠ aqP0 := by decide
@[simp] theorem aq_aqP0_ne_rkT : aqP0 ≠ rkT := by decide
@[simp] theorem aq_rkT_ne_aqP0 : rkT ≠ aqP0 := by decide
@[simp] theorem aq_aqP0_ne_rkM : aqP0 ≠ rkM := by decide
@[simp] theorem aq_rkM_ne_aqP0 : rkM ≠ aqP0 := by decide
@[simp] theorem aq_aqP1_ne_aqAn : aqP1 ≠ aqAn := by decide
@[simp] theorem aq_aqP1_ne_aq1 : aqP1 ≠ aq1 := by decide
@[simp] theorem aq_aqP1_ne_aqTm : aqP1 ≠ aqTm := by decide
@[simp] theorem aq_aqP1_ne_aqHh : aqP1 ≠ aqHh := by decide
@[simp] theorem aq_aqP1_ne_aqTp : aqP1 ≠ aqTp := by decide
@[simp] theorem aq_aqP1_ne_aqUs : aqP1 ≠ aqUs := by decide
@[simp] theorem aq_aqP1_ne_aqTa : aqP1 ≠ aqTa := by decide
@[simp] theorem aq_aqP1_ne_aqTl : aqP1 ≠ aqTl := by decide
@[simp] theorem aq_aqP1_ne_aqNp : aqP1 ≠ aqNp := by decide
@[simp] theorem aq_aqP1_ne_aqLp : aqP1 ≠ aqLp := by decide
@[simp] theorem aq_aqP1_ne_aqLl : aqP1 ≠ aqLl := by decide
@[simp] theorem aq_aqP1_ne_aqAr : aqP1 ≠ aqAr := by decide
@[simp] theorem aq_aqP1_ne_aqP0 : aqP1 ≠ aqP0 := by decide
@[simp] theorem aq_aqP1_ne_aqB1 : aqP1 ≠ aqB1 := by decide
@[simp] theorem aq_aqP1_ne_aqB2 : aqP1 ≠ aqB2 := by decide
@[simp] theorem aq_aqP1_ne_aqRc : aqP1 ≠ aqRc := by decide
@[simp] theorem aq_aqP1_ne_aqHd : aqP1 ≠ aqHd := by decide
@[simp] theorem aq_aqP1_ne_aqFl : aqP1 ≠ aqFl := by decide
@[simp] theorem aq_aqP1_ne_aqFab : aqP1 ≠ aqFab := by decide
@[simp] theorem aq_aqP1_ne_aqFs : aqP1 ≠ aqFs := by decide
@[simp] theorem aq_aqP1_ne_aqK2 : aqP1 ≠ aqK2 := by decide
@[simp] theorem aq_aqP1_ne_aqDf : aqP1 ≠ aqDf := by decide
@[simp] theorem aq_aqP1_ne_aqIr : aqP1 ≠ aqIr := by decide
@[simp] theorem aq_aqP1_ne_lFl : aqP1 ≠ lFl := by decide
@[simp] theorem aq_lFl_ne_aqP1 : lFl ≠ aqP1 := by decide
@[simp] theorem aq_aqP1_ne_lDh : aqP1 ≠ lDh := by decide
@[simp] theorem aq_lDh_ne_aqP1 : lDh ≠ aqP1 := by decide
@[simp] theorem aq_aqP1_ne_lDt : aqP1 ≠ lDt := by decide
@[simp] theorem aq_lDt_ne_aqP1 : lDt ≠ aqP1 := by decide
@[simp] theorem aq_aqP1_ne_lDg : aqP1 ≠ lDg := by decide
@[simp] theorem aq_lDg_ne_aqP1 : lDg ≠ aqP1 := by decide
@[simp] theorem aq_aqP1_ne_lDi : aqP1 ≠ lDi := by decide
@[simp] theorem aq_lDi_ne_aqP1 : lDi ≠ aqP1 := by decide
@[simp] theorem aq_aqP1_ne_lRp : aqP1 ≠ lRp := by decide
@[simp] theorem aq_lRp_ne_aqP1 : lRp ≠ aqP1 := by decide
@[simp] theorem aq_aqP1_ne_lRn : aqP1 ≠ lRn := by decide
@[simp] theorem aq_lRn_ne_aqP1 : lRn ≠ aqP1 := by decide
@[simp] theorem aq_aqP1_ne_lFle : aqP1 ≠ lFle := by decide
@[simp] theorem aq_lFle_ne_aqP1 : lFle ≠ aqP1 := by decide
@[simp] theorem aq_aqP1_ne_lFls : aqP1 ≠ lFls := by decide
@[simp] theorem aq_lFls_ne_aqP1 : lFls ≠ aqP1 := by decide
@[simp] theorem aq_aqP1_ne_lDir : aqP1 ≠ lDir := by decide
@[simp] theorem aq_lDir_ne_aqP1 : lDir ≠ aqP1 := by decide
@[simp] theorem aq_aqP1_ne_lKb : aqP1 ≠ lKb := by decide
@[simp] theorem aq_lKb_ne_aqP1 : lKb ≠ aqP1 := by decide
@[simp] theorem aq_aqP1_ne_kFu : aqP1 ≠ kFu := by decide
@[simp] theorem aq_kFu_ne_aqP1 : kFu ≠ aqP1 := by decide
@[simp] theorem aq_aqP1_ne_kD : aqP1 ≠ kD := by decide
@[simp] theorem aq_kD_ne_aqP1 : kD ≠ aqP1 := by decide
@[simp] theorem aq_aqP1_ne_rkR : aqP1 ≠ rkR := by decide
@[simp] theorem aq_rkR_ne_aqP1 : rkR ≠ aqP1 := by decide
@[simp] theorem aq_aqP1_ne_rkJ : aqP1 ≠ rkJ := by decide
@[simp] theorem aq_rkJ_ne_aqP1 : rkJ ≠ aqP1 := by decide
@[simp] theorem aq_aqP1_ne_rkT : aqP1 ≠ rkT := by decide
@[simp] theorem aq_rkT_ne_aqP1 : rkT ≠ aqP1 := by decide
@[simp] theorem aq_aqP1_ne_rkM : aqP1 ≠ rkM := by decide
@[simp] theorem aq_rkM_ne_aqP1 : rkM ≠ aqP1 := by decide
@[simp] theorem aq_aqB1_ne_aqAn : aqB1 ≠ aqAn := by decide
@[simp] theorem aq_aqB1_ne_aq1 : aqB1 ≠ aq1 := by decide
@[simp] theorem aq_aqB1_ne_aqTm : aqB1 ≠ aqTm := by decide
@[simp] theorem aq_aqB1_ne_aqHh : aqB1 ≠ aqHh := by decide
@[simp] theorem aq_aqB1_ne_aqTp : aqB1 ≠ aqTp := by decide
@[simp] theorem aq_aqB1_ne_aqUs : aqB1 ≠ aqUs := by decide
@[simp] theorem aq_aqB1_ne_aqTa : aqB1 ≠ aqTa := by decide
@[simp] theorem aq_aqB1_ne_aqTl : aqB1 ≠ aqTl := by decide
@[simp] theorem aq_aqB1_ne_aqNp : aqB1 ≠ aqNp := by decide
@[simp] theorem aq_aqB1_ne_aqLp : aqB1 ≠ aqLp := by decide
@[simp] theorem aq_aqB1_ne_aqLl : aqB1 ≠ aqLl := by decide
@[simp] theorem aq_aqB1_ne_aqAr : aqB1 ≠ aqAr := by decide
@[simp] theorem aq_aqB1_ne_aqP0 : aqB1 ≠ aqP0 := by decide
@[simp] theorem aq_aqB1_ne_aqP1 : aqB1 ≠ aqP1 := by decide
@[simp] theorem aq_aqB1_ne_aqB2 : aqB1 ≠ aqB2 := by decide
@[simp] theorem aq_aqB1_ne_aqRc : aqB1 ≠ aqRc := by decide
@[simp] theorem aq_aqB1_ne_aqHd : aqB1 ≠ aqHd := by decide
@[simp] theorem aq_aqB1_ne_aqFl : aqB1 ≠ aqFl := by decide
@[simp] theorem aq_aqB1_ne_aqFab : aqB1 ≠ aqFab := by decide
@[simp] theorem aq_aqB1_ne_aqFs : aqB1 ≠ aqFs := by decide
@[simp] theorem aq_aqB1_ne_aqK2 : aqB1 ≠ aqK2 := by decide
@[simp] theorem aq_aqB1_ne_aqDf : aqB1 ≠ aqDf := by decide
@[simp] theorem aq_aqB1_ne_aqIr : aqB1 ≠ aqIr := by decide
@[simp] theorem aq_aqB1_ne_lFl : aqB1 ≠ lFl := by decide
@[simp] theorem aq_lFl_ne_aqB1 : lFl ≠ aqB1 := by decide
@[simp] theorem aq_aqB1_ne_lDh : aqB1 ≠ lDh := by decide
@[simp] theorem aq_lDh_ne_aqB1 : lDh ≠ aqB1 := by decide
@[simp] theorem aq_aqB1_ne_lDt : aqB1 ≠ lDt := by decide
@[simp] theorem aq_lDt_ne_aqB1 : lDt ≠ aqB1 := by decide
@[simp] theorem aq_aqB1_ne_lDg : aqB1 ≠ lDg := by decide
@[simp] theorem aq_lDg_ne_aqB1 : lDg ≠ aqB1 := by decide
@[simp] theorem aq_aqB1_ne_lDi : aqB1 ≠ lDi := by decide
@[simp] theorem aq_lDi_ne_aqB1 : lDi ≠ aqB1 := by decide
@[simp] theorem aq_aqB1_ne_lRp : aqB1 ≠ lRp := by decide
@[simp] theorem aq_lRp_ne_aqB1 : lRp ≠ aqB1 := by decide
@[simp] theorem aq_aqB1_ne_lRn : aqB1 ≠ lRn := by decide
@[simp] theorem aq_lRn_ne_aqB1 : lRn ≠ aqB1 := by decide
@[simp] theorem aq_aqB1_ne_lFle : aqB1 ≠ lFle := by decide
@[simp] theorem aq_lFle_ne_aqB1 : lFle ≠ aqB1 := by decide
@[simp] theorem aq_aqB1_ne_lFls : aqB1 ≠ lFls := by decide
@[simp] theorem aq_lFls_ne_aqB1 : lFls ≠ aqB1 := by decide
@[simp] theorem aq_aqB1_ne_lDir : aqB1 ≠ lDir := by decide
@[simp] theorem aq_lDir_ne_aqB1 : lDir ≠ aqB1 := by decide
@[simp] theorem aq_aqB1_ne_lKb : aqB1 ≠ lKb := by decide
@[simp] theorem aq_lKb_ne_aqB1 : lKb ≠ aqB1 := by decide
@[simp] theorem aq_aqB1_ne_kFu : aqB1 ≠ kFu := by decide
@[simp] theorem aq_kFu_ne_aqB1 : kFu ≠ aqB1 := by decide
@[simp] theorem aq_aqB1_ne_kD : aqB1 ≠ kD := by decide
@[simp] theorem aq_kD_ne_aqB1 : kD ≠ aqB1 := by decide
@[simp] theorem aq_aqB1_ne_rkR : aqB1 ≠ rkR := by decide
@[simp] theorem aq_rkR_ne_aqB1 : rkR ≠ aqB1 := by decide
@[simp] theorem aq_aqB1_ne_rkJ : aqB1 ≠ rkJ := by decide
@[simp] theorem aq_rkJ_ne_aqB1 : rkJ ≠ aqB1 := by decide
@[simp] theorem aq_aqB1_ne_rkT : aqB1 ≠ rkT := by decide
@[simp] theorem aq_rkT_ne_aqB1 : rkT ≠ aqB1 := by decide
@[simp] theorem aq_aqB1_ne_rkM : aqB1 ≠ rkM := by decide
@[simp] theorem aq_rkM_ne_aqB1 : rkM ≠ aqB1 := by decide
@[simp] theorem aq_aqB2_ne_aqAn : aqB2 ≠ aqAn := by decide
@[simp] theorem aq_aqB2_ne_aq1 : aqB2 ≠ aq1 := by decide
@[simp] theorem aq_aqB2_ne_aqTm : aqB2 ≠ aqTm := by decide
@[simp] theorem aq_aqB2_ne_aqHh : aqB2 ≠ aqHh := by decide
@[simp] theorem aq_aqB2_ne_aqTp : aqB2 ≠ aqTp := by decide
@[simp] theorem aq_aqB2_ne_aqUs : aqB2 ≠ aqUs := by decide
@[simp] theorem aq_aqB2_ne_aqTa : aqB2 ≠ aqTa := by decide
@[simp] theorem aq_aqB2_ne_aqTl : aqB2 ≠ aqTl := by decide
@[simp] theorem aq_aqB2_ne_aqNp : aqB2 ≠ aqNp := by decide
@[simp] theorem aq_aqB2_ne_aqLp : aqB2 ≠ aqLp := by decide
@[simp] theorem aq_aqB2_ne_aqLl : aqB2 ≠ aqLl := by decide
@[simp] theorem aq_aqB2_ne_aqAr : aqB2 ≠ aqAr := by decide
@[simp] theorem aq_aqB2_ne_aqP0 : aqB2 ≠ aqP0 := by decide
@[simp] theorem aq_aqB2_ne_aqP1 : aqB2 ≠ aqP1 := by decide
@[simp] theorem aq_aqB2_ne_aqB1 : aqB2 ≠ aqB1 := by decide
@[simp] theorem aq_aqB2_ne_aqRc : aqB2 ≠ aqRc := by decide
@[simp] theorem aq_aqB2_ne_aqHd : aqB2 ≠ aqHd := by decide
@[simp] theorem aq_aqB2_ne_aqFl : aqB2 ≠ aqFl := by decide
@[simp] theorem aq_aqB2_ne_aqFab : aqB2 ≠ aqFab := by decide
@[simp] theorem aq_aqB2_ne_aqFs : aqB2 ≠ aqFs := by decide
@[simp] theorem aq_aqB2_ne_aqK2 : aqB2 ≠ aqK2 := by decide
@[simp] theorem aq_aqB2_ne_aqDf : aqB2 ≠ aqDf := by decide
@[simp] theorem aq_aqB2_ne_aqIr : aqB2 ≠ aqIr := by decide
@[simp] theorem aq_aqB2_ne_lFl : aqB2 ≠ lFl := by decide
@[simp] theorem aq_lFl_ne_aqB2 : lFl ≠ aqB2 := by decide
@[simp] theorem aq_aqB2_ne_lDh : aqB2 ≠ lDh := by decide
@[simp] theorem aq_lDh_ne_aqB2 : lDh ≠ aqB2 := by decide
@[simp] theorem aq_aqB2_ne_lDt : aqB2 ≠ lDt := by decide
@[simp] theorem aq_lDt_ne_aqB2 : lDt ≠ aqB2 := by decide
@[simp] theorem aq_aqB2_ne_lDg : aqB2 ≠ lDg := by decide
@[simp] theorem aq_lDg_ne_aqB2 : lDg ≠ aqB2 := by decide
@[simp] theorem aq_aqB2_ne_lDi : aqB2 ≠ lDi := by decide
@[simp] theorem aq_lDi_ne_aqB2 : lDi ≠ aqB2 := by decide
@[simp] theorem aq_aqB2_ne_lRp : aqB2 ≠ lRp := by decide
@[simp] theorem aq_lRp_ne_aqB2 : lRp ≠ aqB2 := by decide
@[simp] theorem aq_aqB2_ne_lRn : aqB2 ≠ lRn := by decide
@[simp] theorem aq_lRn_ne_aqB2 : lRn ≠ aqB2 := by decide
@[simp] theorem aq_aqB2_ne_lFle : aqB2 ≠ lFle := by decide
@[simp] theorem aq_lFle_ne_aqB2 : lFle ≠ aqB2 := by decide
@[simp] theorem aq_aqB2_ne_lFls : aqB2 ≠ lFls := by decide
@[simp] theorem aq_lFls_ne_aqB2 : lFls ≠ aqB2 := by decide
@[simp] theorem aq_aqB2_ne_lDir : aqB2 ≠ lDir := by decide
@[simp] theorem aq_lDir_ne_aqB2 : lDir ≠ aqB2 := by decide
@[simp] theorem aq_aqB2_ne_lKb : aqB2 ≠ lKb := by decide
@[simp] theorem aq_lKb_ne_aqB2 : lKb ≠ aqB2 := by decide
@[simp] theorem aq_aqB2_ne_kFu : aqB2 ≠ kFu := by decide
@[simp] theorem aq_kFu_ne_aqB2 : kFu ≠ aqB2 := by decide
@[simp] theorem aq_aqB2_ne_kD : aqB2 ≠ kD := by decide
@[simp] theorem aq_kD_ne_aqB2 : kD ≠ aqB2 := by decide
@[simp] theorem aq_aqB2_ne_rkR : aqB2 ≠ rkR := by decide
@[simp] theorem aq_rkR_ne_aqB2 : rkR ≠ aqB2 := by decide
@[simp] theorem aq_aqB2_ne_rkJ : aqB2 ≠ rkJ := by decide
@[simp] theorem aq_rkJ_ne_aqB2 : rkJ ≠ aqB2 := by decide
@[simp] theorem aq_aqB2_ne_rkT : aqB2 ≠ rkT := by decide
@[simp] theorem aq_rkT_ne_aqB2 : rkT ≠ aqB2 := by decide
@[simp] theorem aq_aqB2_ne_rkM : aqB2 ≠ rkM := by decide
@[simp] theorem aq_rkM_ne_aqB2 : rkM ≠ aqB2 := by decide
@[simp] theorem aq_aqRc_ne_aqAn : aqRc ≠ aqAn := by decide
@[simp] theorem aq_aqRc_ne_aq1 : aqRc ≠ aq1 := by decide
@[simp] theorem aq_aqRc_ne_aqTm : aqRc ≠ aqTm := by decide
@[simp] theorem aq_aqRc_ne_aqHh : aqRc ≠ aqHh := by decide
@[simp] theorem aq_aqRc_ne_aqTp : aqRc ≠ aqTp := by decide
@[simp] theorem aq_aqRc_ne_aqUs : aqRc ≠ aqUs := by decide
@[simp] theorem aq_aqRc_ne_aqTa : aqRc ≠ aqTa := by decide
@[simp] theorem aq_aqRc_ne_aqTl : aqRc ≠ aqTl := by decide
@[simp] theorem aq_aqRc_ne_aqNp : aqRc ≠ aqNp := by decide
@[simp] theorem aq_aqRc_ne_aqLp : aqRc ≠ aqLp := by decide
@[simp] theorem aq_aqRc_ne_aqLl : aqRc ≠ aqLl := by decide
@[simp] theorem aq_aqRc_ne_aqAr : aqRc ≠ aqAr := by decide
@[simp] theorem aq_aqRc_ne_aqP0 : aqRc ≠ aqP0 := by decide
@[simp] theorem aq_aqRc_ne_aqP1 : aqRc ≠ aqP1 := by decide
@[simp] theorem aq_aqRc_ne_aqB1 : aqRc ≠ aqB1 := by decide
@[simp] theorem aq_aqRc_ne_aqB2 : aqRc ≠ aqB2 := by decide
@[simp] theorem aq_aqRc_ne_aqHd : aqRc ≠ aqHd := by decide
@[simp] theorem aq_aqRc_ne_aqFl : aqRc ≠ aqFl := by decide
@[simp] theorem aq_aqRc_ne_aqFab : aqRc ≠ aqFab := by decide
@[simp] theorem aq_aqRc_ne_aqFs : aqRc ≠ aqFs := by decide
@[simp] theorem aq_aqRc_ne_aqK2 : aqRc ≠ aqK2 := by decide
@[simp] theorem aq_aqRc_ne_aqDf : aqRc ≠ aqDf := by decide
@[simp] theorem aq_aqRc_ne_aqIr : aqRc ≠ aqIr := by decide
@[simp] theorem aq_aqRc_ne_lFl : aqRc ≠ lFl := by decide
@[simp] theorem aq_lFl_ne_aqRc : lFl ≠ aqRc := by decide
@[simp] theorem aq_aqRc_ne_lDh : aqRc ≠ lDh := by decide
@[simp] theorem aq_lDh_ne_aqRc : lDh ≠ aqRc := by decide
@[simp] theorem aq_aqRc_ne_lDt : aqRc ≠ lDt := by decide
@[simp] theorem aq_lDt_ne_aqRc : lDt ≠ aqRc := by decide
@[simp] theorem aq_aqRc_ne_lDg : aqRc ≠ lDg := by decide
@[simp] theorem aq_lDg_ne_aqRc : lDg ≠ aqRc := by decide
@[simp] theorem aq_aqRc_ne_lDi : aqRc ≠ lDi := by decide
@[simp] theorem aq_lDi_ne_aqRc : lDi ≠ aqRc := by decide
@[simp] theorem aq_aqRc_ne_lRp : aqRc ≠ lRp := by decide
@[simp] theorem aq_lRp_ne_aqRc : lRp ≠ aqRc := by decide
@[simp] theorem aq_aqRc_ne_lRn : aqRc ≠ lRn := by decide
@[simp] theorem aq_lRn_ne_aqRc : lRn ≠ aqRc := by decide
@[simp] theorem aq_aqRc_ne_lFle : aqRc ≠ lFle := by decide
@[simp] theorem aq_lFle_ne_aqRc : lFle ≠ aqRc := by decide
@[simp] theorem aq_aqRc_ne_lFls : aqRc ≠ lFls := by decide
@[simp] theorem aq_lFls_ne_aqRc : lFls ≠ aqRc := by decide
@[simp] theorem aq_aqRc_ne_lDir : aqRc ≠ lDir := by decide
@[simp] theorem aq_lDir_ne_aqRc : lDir ≠ aqRc := by decide
@[simp] theorem aq_aqRc_ne_lKb : aqRc ≠ lKb := by decide
@[simp] theorem aq_lKb_ne_aqRc : lKb ≠ aqRc := by decide
@[simp] theorem aq_aqRc_ne_kFu : aqRc ≠ kFu := by decide
@[simp] theorem aq_kFu_ne_aqRc : kFu ≠ aqRc := by decide
@[simp] theorem aq_aqRc_ne_kD : aqRc ≠ kD := by decide
@[simp] theorem aq_kD_ne_aqRc : kD ≠ aqRc := by decide
@[simp] theorem aq_aqRc_ne_rkR : aqRc ≠ rkR := by decide
@[simp] theorem aq_rkR_ne_aqRc : rkR ≠ aqRc := by decide
@[simp] theorem aq_aqRc_ne_rkJ : aqRc ≠ rkJ := by decide
@[simp] theorem aq_rkJ_ne_aqRc : rkJ ≠ aqRc := by decide
@[simp] theorem aq_aqRc_ne_rkT : aqRc ≠ rkT := by decide
@[simp] theorem aq_rkT_ne_aqRc : rkT ≠ aqRc := by decide
@[simp] theorem aq_aqRc_ne_rkM : aqRc ≠ rkM := by decide
@[simp] theorem aq_rkM_ne_aqRc : rkM ≠ aqRc := by decide
@[simp] theorem aq_aqHd_ne_aqAn : aqHd ≠ aqAn := by decide
@[simp] theorem aq_aqHd_ne_aq1 : aqHd ≠ aq1 := by decide
@[simp] theorem aq_aqHd_ne_aqTm : aqHd ≠ aqTm := by decide
@[simp] theorem aq_aqHd_ne_aqHh : aqHd ≠ aqHh := by decide
@[simp] theorem aq_aqHd_ne_aqTp : aqHd ≠ aqTp := by decide
@[simp] theorem aq_aqHd_ne_aqUs : aqHd ≠ aqUs := by decide
@[simp] theorem aq_aqHd_ne_aqTa : aqHd ≠ aqTa := by decide
@[simp] theorem aq_aqHd_ne_aqTl : aqHd ≠ aqTl := by decide
@[simp] theorem aq_aqHd_ne_aqNp : aqHd ≠ aqNp := by decide
@[simp] theorem aq_aqHd_ne_aqLp : aqHd ≠ aqLp := by decide
@[simp] theorem aq_aqHd_ne_aqLl : aqHd ≠ aqLl := by decide
@[simp] theorem aq_aqHd_ne_aqAr : aqHd ≠ aqAr := by decide
@[simp] theorem aq_aqHd_ne_aqP0 : aqHd ≠ aqP0 := by decide
@[simp] theorem aq_aqHd_ne_aqP1 : aqHd ≠ aqP1 := by decide
@[simp] theorem aq_aqHd_ne_aqB1 : aqHd ≠ aqB1 := by decide
@[simp] theorem aq_aqHd_ne_aqB2 : aqHd ≠ aqB2 := by decide
@[simp] theorem aq_aqHd_ne_aqRc : aqHd ≠ aqRc := by decide
@[simp] theorem aq_aqHd_ne_aqFl : aqHd ≠ aqFl := by decide
@[simp] theorem aq_aqHd_ne_aqFab : aqHd ≠ aqFab := by decide
@[simp] theorem aq_aqHd_ne_aqFs : aqHd ≠ aqFs := by decide
@[simp] theorem aq_aqHd_ne_aqK2 : aqHd ≠ aqK2 := by decide
@[simp] theorem aq_aqHd_ne_aqDf : aqHd ≠ aqDf := by decide
@[simp] theorem aq_aqHd_ne_aqIr : aqHd ≠ aqIr := by decide
@[simp] theorem aq_aqHd_ne_lFl : aqHd ≠ lFl := by decide
@[simp] theorem aq_lFl_ne_aqHd : lFl ≠ aqHd := by decide
@[simp] theorem aq_aqHd_ne_lDh : aqHd ≠ lDh := by decide
@[simp] theorem aq_lDh_ne_aqHd : lDh ≠ aqHd := by decide
@[simp] theorem aq_aqHd_ne_lDt : aqHd ≠ lDt := by decide
@[simp] theorem aq_lDt_ne_aqHd : lDt ≠ aqHd := by decide
@[simp] theorem aq_aqHd_ne_lDg : aqHd ≠ lDg := by decide
@[simp] theorem aq_lDg_ne_aqHd : lDg ≠ aqHd := by decide
@[simp] theorem aq_aqHd_ne_lDi : aqHd ≠ lDi := by decide
@[simp] theorem aq_lDi_ne_aqHd : lDi ≠ aqHd := by decide
@[simp] theorem aq_aqHd_ne_lRp : aqHd ≠ lRp := by decide
@[simp] theorem aq_lRp_ne_aqHd : lRp ≠ aqHd := by decide
@[simp] theorem aq_aqHd_ne_lRn : aqHd ≠ lRn := by decide
@[simp] theorem aq_lRn_ne_aqHd : lRn ≠ aqHd := by decide
@[simp] theorem aq_aqHd_ne_lFle : aqHd ≠ lFle := by decide
@[simp] theorem aq_lFle_ne_aqHd : lFle ≠ aqHd := by decide
@[simp] theorem aq_aqHd_ne_lFls : aqHd ≠ lFls := by decide
@[simp] theorem aq_lFls_ne_aqHd : lFls ≠ aqHd := by decide
@[simp] theorem aq_aqHd_ne_lDir : aqHd ≠ lDir := by decide
@[simp] theorem aq_lDir_ne_aqHd : lDir ≠ aqHd := by decide
@[simp] theorem aq_aqHd_ne_lKb : aqHd ≠ lKb := by decide
@[simp] theorem aq_lKb_ne_aqHd : lKb ≠ aqHd := by decide
@[simp] theorem aq_aqHd_ne_kFu : aqHd ≠ kFu := by decide
@[simp] theorem aq_kFu_ne_aqHd : kFu ≠ aqHd := by decide
@[simp] theorem aq_aqHd_ne_kD : aqHd ≠ kD := by decide
@[simp] theorem aq_kD_ne_aqHd : kD ≠ aqHd := by decide
@[simp] theorem aq_aqHd_ne_rkR : aqHd ≠ rkR := by decide
@[simp] theorem aq_rkR_ne_aqHd : rkR ≠ aqHd := by decide
@[simp] theorem aq_aqHd_ne_rkJ : aqHd ≠ rkJ := by decide
@[simp] theorem aq_rkJ_ne_aqHd : rkJ ≠ aqHd := by decide
@[simp] theorem aq_aqHd_ne_rkT : aqHd ≠ rkT := by decide
@[simp] theorem aq_rkT_ne_aqHd : rkT ≠ aqHd := by decide
@[simp] theorem aq_aqHd_ne_rkM : aqHd ≠ rkM := by decide
@[simp] theorem aq_rkM_ne_aqHd : rkM ≠ aqHd := by decide
@[simp] theorem aq_aqFl_ne_aqAn : aqFl ≠ aqAn := by decide
@[simp] theorem aq_aqFl_ne_aq1 : aqFl ≠ aq1 := by decide
@[simp] theorem aq_aqFl_ne_aqTm : aqFl ≠ aqTm := by decide
@[simp] theorem aq_aqFl_ne_aqHh : aqFl ≠ aqHh := by decide
@[simp] theorem aq_aqFl_ne_aqTp : aqFl ≠ aqTp := by decide
@[simp] theorem aq_aqFl_ne_aqUs : aqFl ≠ aqUs := by decide
@[simp] theorem aq_aqFl_ne_aqTa : aqFl ≠ aqTa := by decide
@[simp] theorem aq_aqFl_ne_aqTl : aqFl ≠ aqTl := by decide
@[simp] theorem aq_aqFl_ne_aqNp : aqFl ≠ aqNp := by decide
@[simp] theorem aq_aqFl_ne_aqLp : aqFl ≠ aqLp := by decide
@[simp] theorem aq_aqFl_ne_aqLl : aqFl ≠ aqLl := by decide
@[simp] theorem aq_aqFl_ne_aqAr : aqFl ≠ aqAr := by decide
@[simp] theorem aq_aqFl_ne_aqP0 : aqFl ≠ aqP0 := by decide
@[simp] theorem aq_aqFl_ne_aqP1 : aqFl ≠ aqP1 := by decide
@[simp] theorem aq_aqFl_ne_aqB1 : aqFl ≠ aqB1 := by decide
@[simp] theorem aq_aqFl_ne_aqB2 : aqFl ≠ aqB2 := by decide
@[simp] theorem aq_aqFl_ne_aqRc : aqFl ≠ aqRc := by decide
@[simp] theorem aq_aqFl_ne_aqHd : aqFl ≠ aqHd := by decide
@[simp] theorem aq_aqFl_ne_aqFab : aqFl ≠ aqFab := by decide
@[simp] theorem aq_aqFl_ne_aqFs : aqFl ≠ aqFs := by decide
@[simp] theorem aq_aqFl_ne_aqK2 : aqFl ≠ aqK2 := by decide
@[simp] theorem aq_aqFl_ne_aqDf : aqFl ≠ aqDf := by decide
@[simp] theorem aq_aqFl_ne_aqIr : aqFl ≠ aqIr := by decide
@[simp] theorem aq_aqFl_ne_lFl : aqFl ≠ lFl := by decide
@[simp] theorem aq_lFl_ne_aqFl : lFl ≠ aqFl := by decide
@[simp] theorem aq_aqFl_ne_lDh : aqFl ≠ lDh := by decide
@[simp] theorem aq_lDh_ne_aqFl : lDh ≠ aqFl := by decide
@[simp] theorem aq_aqFl_ne_lDt : aqFl ≠ lDt := by decide
@[simp] theorem aq_lDt_ne_aqFl : lDt ≠ aqFl := by decide
@[simp] theorem aq_aqFl_ne_lDg : aqFl ≠ lDg := by decide
@[simp] theorem aq_lDg_ne_aqFl : lDg ≠ aqFl := by decide
@[simp] theorem aq_aqFl_ne_lDi : aqFl ≠ lDi := by decide
@[simp] theorem aq_lDi_ne_aqFl : lDi ≠ aqFl := by decide
@[simp] theorem aq_aqFl_ne_lRp : aqFl ≠ lRp := by decide
@[simp] theorem aq_lRp_ne_aqFl : lRp ≠ aqFl := by decide
@[simp] theorem aq_aqFl_ne_lRn : aqFl ≠ lRn := by decide
@[simp] theorem aq_lRn_ne_aqFl : lRn ≠ aqFl := by decide
@[simp] theorem aq_aqFl_ne_lFle : aqFl ≠ lFle := by decide
@[simp] theorem aq_lFle_ne_aqFl : lFle ≠ aqFl := by decide
@[simp] theorem aq_aqFl_ne_lFls : aqFl ≠ lFls := by decide
@[simp] theorem aq_lFls_ne_aqFl : lFls ≠ aqFl := by decide
@[simp] theorem aq_aqFl_ne_lDir : aqFl ≠ lDir := by decide
@[simp] theorem aq_lDir_ne_aqFl : lDir ≠ aqFl := by decide
@[simp] theorem aq_aqFl_ne_lKb : aqFl ≠ lKb := by decide
@[simp] theorem aq_lKb_ne_aqFl : lKb ≠ aqFl := by decide
@[simp] theorem aq_aqFl_ne_kFu : aqFl ≠ kFu := by decide
@[simp] theorem aq_kFu_ne_aqFl : kFu ≠ aqFl := by decide
@[simp] theorem aq_aqFl_ne_kD : aqFl ≠ kD := by decide
@[simp] theorem aq_kD_ne_aqFl : kD ≠ aqFl := by decide
@[simp] theorem aq_aqFl_ne_rkR : aqFl ≠ rkR := by decide
@[simp] theorem aq_rkR_ne_aqFl : rkR ≠ aqFl := by decide
@[simp] theorem aq_aqFl_ne_rkJ : aqFl ≠ rkJ := by decide
@[simp] theorem aq_rkJ_ne_aqFl : rkJ ≠ aqFl := by decide
@[simp] theorem aq_aqFl_ne_rkT : aqFl ≠ rkT := by decide
@[simp] theorem aq_rkT_ne_aqFl : rkT ≠ aqFl := by decide
@[simp] theorem aq_aqFl_ne_rkM : aqFl ≠ rkM := by decide
@[simp] theorem aq_rkM_ne_aqFl : rkM ≠ aqFl := by decide
@[simp] theorem aq_aqFab_ne_aqAn : aqFab ≠ aqAn := by decide
@[simp] theorem aq_aqFab_ne_aq1 : aqFab ≠ aq1 := by decide
@[simp] theorem aq_aqFab_ne_aqTm : aqFab ≠ aqTm := by decide
@[simp] theorem aq_aqFab_ne_aqHh : aqFab ≠ aqHh := by decide
@[simp] theorem aq_aqFab_ne_aqTp : aqFab ≠ aqTp := by decide
@[simp] theorem aq_aqFab_ne_aqUs : aqFab ≠ aqUs := by decide
@[simp] theorem aq_aqFab_ne_aqTa : aqFab ≠ aqTa := by decide
@[simp] theorem aq_aqFab_ne_aqTl : aqFab ≠ aqTl := by decide
@[simp] theorem aq_aqFab_ne_aqNp : aqFab ≠ aqNp := by decide
@[simp] theorem aq_aqFab_ne_aqLp : aqFab ≠ aqLp := by decide
@[simp] theorem aq_aqFab_ne_aqLl : aqFab ≠ aqLl := by decide
@[simp] theorem aq_aqFab_ne_aqAr : aqFab ≠ aqAr := by decide
@[simp] theorem aq_aqFab_ne_aqP0 : aqFab ≠ aqP0 := by decide
@[simp] theorem aq_aqFab_ne_aqP1 : aqFab ≠ aqP1 := by decide
@[simp] theorem aq_aqFab_ne_aqB1 : aqFab ≠ aqB1 := by decide
@[simp] theorem aq_aqFab_ne_aqB2 : aqFab ≠ aqB2 := by decide
@[simp] theorem aq_aqFab_ne_aqRc : aqFab ≠ aqRc := by decide
@[simp] theorem aq_aqFab_ne_aqHd : aqFab ≠ aqHd := by decide
@[simp] theorem aq_aqFab_ne_aqFl : aqFab ≠ aqFl := by decide
@[simp] theorem aq_aqFab_ne_aqFs : aqFab ≠ aqFs := by decide
@[simp] theorem aq_aqFab_ne_aqK2 : aqFab ≠ aqK2 := by decide
@[simp] theorem aq_aqFab_ne_aqDf : aqFab ≠ aqDf := by decide
@[simp] theorem aq_aqFab_ne_aqIr : aqFab ≠ aqIr := by decide
@[simp] theorem aq_aqFab_ne_lFl : aqFab ≠ lFl := by decide
@[simp] theorem aq_lFl_ne_aqFab : lFl ≠ aqFab := by decide
@[simp] theorem aq_aqFab_ne_lDh : aqFab ≠ lDh := by decide
@[simp] theorem aq_lDh_ne_aqFab : lDh ≠ aqFab := by decide
@[simp] theorem aq_aqFab_ne_lDt : aqFab ≠ lDt := by decide
@[simp] theorem aq_lDt_ne_aqFab : lDt ≠ aqFab := by decide
@[simp] theorem aq_aqFab_ne_lDg : aqFab ≠ lDg := by decide
@[simp] theorem aq_lDg_ne_aqFab : lDg ≠ aqFab := by decide
@[simp] theorem aq_aqFab_ne_lDi : aqFab ≠ lDi := by decide
@[simp] theorem aq_lDi_ne_aqFab : lDi ≠ aqFab := by decide
@[simp] theorem aq_aqFab_ne_lRp : aqFab ≠ lRp := by decide
@[simp] theorem aq_lRp_ne_aqFab : lRp ≠ aqFab := by decide
@[simp] theorem aq_aqFab_ne_lRn : aqFab ≠ lRn := by decide
@[simp] theorem aq_lRn_ne_aqFab : lRn ≠ aqFab := by decide
@[simp] theorem aq_aqFab_ne_lFle : aqFab ≠ lFle := by decide
@[simp] theorem aq_lFle_ne_aqFab : lFle ≠ aqFab := by decide
@[simp] theorem aq_aqFab_ne_lFls : aqFab ≠ lFls := by decide
@[simp] theorem aq_lFls_ne_aqFab : lFls ≠ aqFab := by decide
@[simp] theorem aq_aqFab_ne_lDir : aqFab ≠ lDir := by decide
@[simp] theorem aq_lDir_ne_aqFab : lDir ≠ aqFab := by decide
@[simp] theorem aq_aqFab_ne_lKb : aqFab ≠ lKb := by decide
@[simp] theorem aq_lKb_ne_aqFab : lKb ≠ aqFab := by decide
@[simp] theorem aq_aqFab_ne_kFu : aqFab ≠ kFu := by decide
@[simp] theorem aq_kFu_ne_aqFab : kFu ≠ aqFab := by decide
@[simp] theorem aq_aqFab_ne_kD : aqFab ≠ kD := by decide
@[simp] theorem aq_kD_ne_aqFab : kD ≠ aqFab := by decide
@[simp] theorem aq_aqFab_ne_rkR : aqFab ≠ rkR := by decide
@[simp] theorem aq_rkR_ne_aqFab : rkR ≠ aqFab := by decide
@[simp] theorem aq_aqFab_ne_rkJ : aqFab ≠ rkJ := by decide
@[simp] theorem aq_rkJ_ne_aqFab : rkJ ≠ aqFab := by decide
@[simp] theorem aq_aqFab_ne_rkT : aqFab ≠ rkT := by decide
@[simp] theorem aq_rkT_ne_aqFab : rkT ≠ aqFab := by decide
@[simp] theorem aq_aqFab_ne_rkM : aqFab ≠ rkM := by decide
@[simp] theorem aq_rkM_ne_aqFab : rkM ≠ aqFab := by decide
@[simp] theorem aq_aqFs_ne_aqAn : aqFs ≠ aqAn := by decide
@[simp] theorem aq_aqFs_ne_aq1 : aqFs ≠ aq1 := by decide
@[simp] theorem aq_aqFs_ne_aqTm : aqFs ≠ aqTm := by decide
@[simp] theorem aq_aqFs_ne_aqHh : aqFs ≠ aqHh := by decide
@[simp] theorem aq_aqFs_ne_aqTp : aqFs ≠ aqTp := by decide
@[simp] theorem aq_aqFs_ne_aqUs : aqFs ≠ aqUs := by decide
@[simp] theorem aq_aqFs_ne_aqTa : aqFs ≠ aqTa := by decide
@[simp] theorem aq_aqFs_ne_aqTl : aqFs ≠ aqTl := by decide
@[simp] theorem aq_aqFs_ne_aqNp : aqFs ≠ aqNp := by decide
@[simp] theorem aq_aqFs_ne_aqLp : aqFs ≠ aqLp := by decide
@[simp] theorem aq_aqFs_ne_aqLl : aqFs ≠ aqLl := by decide
@[simp] theorem aq_aqFs_ne_aqAr : aqFs ≠ aqAr := by decide
@[simp] theorem aq_aqFs_ne_aqP0 : aqFs ≠ aqP0 := by decide
@[simp] theorem aq_aqFs_ne_aqP1 : aqFs ≠ aqP1 := by decide
@[simp] theorem aq_aqFs_ne_aqB1 : aqFs ≠ aqB1 := by decide
@[simp] theorem aq_aqFs_ne_aqB2 : aqFs ≠ aqB2 := by decide
@[simp] theorem aq_aqFs_ne_aqRc : aqFs ≠ aqRc := by decide
@[simp] theorem aq_aqFs_ne_aqHd : aqFs ≠ aqHd := by decide
@[simp] theorem aq_aqFs_ne_aqFl : aqFs ≠ aqFl := by decide
@[simp] theorem aq_aqFs_ne_aqFab : aqFs ≠ aqFab := by decide
@[simp] theorem aq_aqFs_ne_aqK2 : aqFs ≠ aqK2 := by decide
@[simp] theorem aq_aqFs_ne_aqDf : aqFs ≠ aqDf := by decide
@[simp] theorem aq_aqFs_ne_aqIr : aqFs ≠ aqIr := by decide
@[simp] theorem aq_aqFs_ne_lFl : aqFs ≠ lFl := by decide
@[simp] theorem aq_lFl_ne_aqFs : lFl ≠ aqFs := by decide
@[simp] theorem aq_aqFs_ne_lDh : aqFs ≠ lDh := by decide
@[simp] theorem aq_lDh_ne_aqFs : lDh ≠ aqFs := by decide
@[simp] theorem aq_aqFs_ne_lDt : aqFs ≠ lDt := by decide
@[simp] theorem aq_lDt_ne_aqFs : lDt ≠ aqFs := by decide
@[simp] theorem aq_aqFs_ne_lDg : aqFs ≠ lDg := by decide
@[simp] theorem aq_lDg_ne_aqFs : lDg ≠ aqFs := by decide
@[simp] theorem aq_aqFs_ne_lDi : aqFs ≠ lDi := by decide
@[simp] theorem aq_lDi_ne_aqFs : lDi ≠ aqFs := by decide
@[simp] theorem aq_aqFs_ne_lRp : aqFs ≠ lRp := by decide
@[simp] theorem aq_lRp_ne_aqFs : lRp ≠ aqFs := by decide
@[simp] theorem aq_aqFs_ne_lRn : aqFs ≠ lRn := by decide
@[simp] theorem aq_lRn_ne_aqFs : lRn ≠ aqFs := by decide
@[simp] theorem aq_aqFs_ne_lFle : aqFs ≠ lFle := by decide
@[simp] theorem aq_lFle_ne_aqFs : lFle ≠ aqFs := by decide
@[simp] theorem aq_aqFs_ne_lFls : aqFs ≠ lFls := by decide
@[simp] theorem aq_lFls_ne_aqFs : lFls ≠ aqFs := by decide
@[simp] theorem aq_aqFs_ne_lDir : aqFs ≠ lDir := by decide
@[simp] theorem aq_lDir_ne_aqFs : lDir ≠ aqFs := by decide
@[simp] theorem aq_aqFs_ne_lKb : aqFs ≠ lKb := by decide
@[simp] theorem aq_lKb_ne_aqFs : lKb ≠ aqFs := by decide
@[simp] theorem aq_aqFs_ne_kFu : aqFs ≠ kFu := by decide
@[simp] theorem aq_kFu_ne_aqFs : kFu ≠ aqFs := by decide
@[simp] theorem aq_aqFs_ne_kD : aqFs ≠ kD := by decide
@[simp] theorem aq_kD_ne_aqFs : kD ≠ aqFs := by decide
@[simp] theorem aq_aqFs_ne_rkR : aqFs ≠ rkR := by decide
@[simp] theorem aq_rkR_ne_aqFs : rkR ≠ aqFs := by decide
@[simp] theorem aq_aqFs_ne_rkJ : aqFs ≠ rkJ := by decide
@[simp] theorem aq_rkJ_ne_aqFs : rkJ ≠ aqFs := by decide
@[simp] theorem aq_aqFs_ne_rkT : aqFs ≠ rkT := by decide
@[simp] theorem aq_rkT_ne_aqFs : rkT ≠ aqFs := by decide
@[simp] theorem aq_aqFs_ne_rkM : aqFs ≠ rkM := by decide
@[simp] theorem aq_rkM_ne_aqFs : rkM ≠ aqFs := by decide
@[simp] theorem aq_aqK2_ne_aqAn : aqK2 ≠ aqAn := by decide
@[simp] theorem aq_aqK2_ne_aq1 : aqK2 ≠ aq1 := by decide
@[simp] theorem aq_aqK2_ne_aqTm : aqK2 ≠ aqTm := by decide
@[simp] theorem aq_aqK2_ne_aqHh : aqK2 ≠ aqHh := by decide
@[simp] theorem aq_aqK2_ne_aqTp : aqK2 ≠ aqTp := by decide
@[simp] theorem aq_aqK2_ne_aqUs : aqK2 ≠ aqUs := by decide
@[simp] theorem aq_aqK2_ne_aqTa : aqK2 ≠ aqTa := by decide
@[simp] theorem aq_aqK2_ne_aqTl : aqK2 ≠ aqTl := by decide
@[simp] theorem aq_aqK2_ne_aqNp : aqK2 ≠ aqNp := by decide
@[simp] theorem aq_aqK2_ne_aqLp : aqK2 ≠ aqLp := by decide
@[simp] theorem aq_aqK2_ne_aqLl : aqK2 ≠ aqLl := by decide
@[simp] theorem aq_aqK2_ne_aqAr : aqK2 ≠ aqAr := by decide
@[simp] theorem aq_aqK2_ne_aqP0 : aqK2 ≠ aqP0 := by decide
@[simp] theorem aq_aqK2_ne_aqP1 : aqK2 ≠ aqP1 := by decide
@[simp] theorem aq_aqK2_ne_aqB1 : aqK2 ≠ aqB1 := by decide
@[simp] theorem aq_aqK2_ne_aqB2 : aqK2 ≠ aqB2 := by decide
@[simp] theorem aq_aqK2_ne_aqRc : aqK2 ≠ aqRc := by decide
@[simp] theorem aq_aqK2_ne_aqHd : aqK2 ≠ aqHd := by decide
@[simp] theorem aq_aqK2_ne_aqFl : aqK2 ≠ aqFl := by decide
@[simp] theorem aq_aqK2_ne_aqFab : aqK2 ≠ aqFab := by decide
@[simp] theorem aq_aqK2_ne_aqFs : aqK2 ≠ aqFs := by decide
@[simp] theorem aq_aqK2_ne_aqDf : aqK2 ≠ aqDf := by decide
@[simp] theorem aq_aqK2_ne_aqIr : aqK2 ≠ aqIr := by decide
@[simp] theorem aq_aqK2_ne_lFl : aqK2 ≠ lFl := by decide
@[simp] theorem aq_lFl_ne_aqK2 : lFl ≠ aqK2 := by decide
@[simp] theorem aq_aqK2_ne_lDh : aqK2 ≠ lDh := by decide
@[simp] theorem aq_lDh_ne_aqK2 : lDh ≠ aqK2 := by decide
@[simp] theorem aq_aqK2_ne_lDt : aqK2 ≠ lDt := by decide
@[simp] theorem aq_lDt_ne_aqK2 : lDt ≠ aqK2 := by decide
@[simp] theorem aq_aqK2_ne_lDg : aqK2 ≠ lDg := by decide
@[simp] theorem aq_lDg_ne_aqK2 : lDg ≠ aqK2 := by decide
@[simp] theorem aq_aqK2_ne_lDi : aqK2 ≠ lDi := by decide
@[simp] theorem aq_lDi_ne_aqK2 : lDi ≠ aqK2 := by decide
@[simp] theorem aq_aqK2_ne_lRp : aqK2 ≠ lRp := by decide
@[simp] theorem aq_lRp_ne_aqK2 : lRp ≠ aqK2 := by decide
@[simp] theorem aq_aqK2_ne_lRn : aqK2 ≠ lRn := by decide
@[simp] theorem aq_lRn_ne_aqK2 : lRn ≠ aqK2 := by decide
@[simp] theorem aq_aqK2_ne_lFle : aqK2 ≠ lFle := by decide
@[simp] theorem aq_lFle_ne_aqK2 : lFle ≠ aqK2 := by decide
@[simp] theorem aq_aqK2_ne_lFls : aqK2 ≠ lFls := by decide
@[simp] theorem aq_lFls_ne_aqK2 : lFls ≠ aqK2 := by decide
@[simp] theorem aq_aqK2_ne_lDir : aqK2 ≠ lDir := by decide
@[simp] theorem aq_lDir_ne_aqK2 : lDir ≠ aqK2 := by decide
@[simp] theorem aq_aqK2_ne_lKb : aqK2 ≠ lKb := by decide
@[simp] theorem aq_lKb_ne_aqK2 : lKb ≠ aqK2 := by decide
@[simp] theorem aq_aqK2_ne_kFu : aqK2 ≠ kFu := by decide
@[simp] theorem aq_kFu_ne_aqK2 : kFu ≠ aqK2 := by decide
@[simp] theorem aq_aqK2_ne_kD : aqK2 ≠ kD := by decide
@[simp] theorem aq_kD_ne_aqK2 : kD ≠ aqK2 := by decide
@[simp] theorem aq_aqK2_ne_rkR : aqK2 ≠ rkR := by decide
@[simp] theorem aq_rkR_ne_aqK2 : rkR ≠ aqK2 := by decide
@[simp] theorem aq_aqK2_ne_rkJ : aqK2 ≠ rkJ := by decide
@[simp] theorem aq_rkJ_ne_aqK2 : rkJ ≠ aqK2 := by decide
@[simp] theorem aq_aqK2_ne_rkT : aqK2 ≠ rkT := by decide
@[simp] theorem aq_rkT_ne_aqK2 : rkT ≠ aqK2 := by decide
@[simp] theorem aq_aqK2_ne_rkM : aqK2 ≠ rkM := by decide
@[simp] theorem aq_rkM_ne_aqK2 : rkM ≠ aqK2 := by decide
@[simp] theorem aq_aqDf_ne_aqAn : aqDf ≠ aqAn := by decide
@[simp] theorem aq_aqDf_ne_aq1 : aqDf ≠ aq1 := by decide
@[simp] theorem aq_aqDf_ne_aqTm : aqDf ≠ aqTm := by decide
@[simp] theorem aq_aqDf_ne_aqHh : aqDf ≠ aqHh := by decide
@[simp] theorem aq_aqDf_ne_aqTp : aqDf ≠ aqTp := by decide
@[simp] theorem aq_aqDf_ne_aqUs : aqDf ≠ aqUs := by decide
@[simp] theorem aq_aqDf_ne_aqTa : aqDf ≠ aqTa := by decide
@[simp] theorem aq_aqDf_ne_aqTl : aqDf ≠ aqTl := by decide
@[simp] theorem aq_aqDf_ne_aqNp : aqDf ≠ aqNp := by decide
@[simp] theorem aq_aqDf_ne_aqLp : aqDf ≠ aqLp := by decide
@[simp] theorem aq_aqDf_ne_aqLl : aqDf ≠ aqLl := by decide
@[simp] theorem aq_aqDf_ne_aqAr : aqDf ≠ aqAr := by decide
@[simp] theorem aq_aqDf_ne_aqP0 : aqDf ≠ aqP0 := by decide
@[simp] theorem aq_aqDf_ne_aqP1 : aqDf ≠ aqP1 := by decide
@[simp] theorem aq_aqDf_ne_aqB1 : aqDf ≠ aqB1 := by decide
@[simp] theorem aq_aqDf_ne_aqB2 : aqDf ≠ aqB2 := by decide
@[simp] theorem aq_aqDf_ne_aqRc : aqDf ≠ aqRc := by decide
@[simp] theorem aq_aqDf_ne_aqHd : aqDf ≠ aqHd := by decide
@[simp] theorem aq_aqDf_ne_aqFl : aqDf ≠ aqFl := by decide
@[simp] theorem aq_aqDf_ne_aqFab : aqDf ≠ aqFab := by decide
@[simp] theorem aq_aqDf_ne_aqFs : aqDf ≠ aqFs := by decide
@[simp] theorem aq_aqDf_ne_aqK2 : aqDf ≠ aqK2 := by decide
@[simp] theorem aq_aqDf_ne_aqIr : aqDf ≠ aqIr := by decide
@[simp] theorem aq_aqDf_ne_lFl : aqDf ≠ lFl := by decide
@[simp] theorem aq_lFl_ne_aqDf : lFl ≠ aqDf := by decide
@[simp] theorem aq_aqDf_ne_lDh : aqDf ≠ lDh := by decide
@[simp] theorem aq_lDh_ne_aqDf : lDh ≠ aqDf := by decide
@[simp] theorem aq_aqDf_ne_lDt : aqDf ≠ lDt := by decide
@[simp] theorem aq_lDt_ne_aqDf : lDt ≠ aqDf := by decide
@[simp] theorem aq_aqDf_ne_lDg : aqDf ≠ lDg := by decide
@[simp] theorem aq_lDg_ne_aqDf : lDg ≠ aqDf := by decide
@[simp] theorem aq_aqDf_ne_lDi : aqDf ≠ lDi := by decide
@[simp] theorem aq_lDi_ne_aqDf : lDi ≠ aqDf := by decide
@[simp] theorem aq_aqDf_ne_lRp : aqDf ≠ lRp := by decide
@[simp] theorem aq_lRp_ne_aqDf : lRp ≠ aqDf := by decide
@[simp] theorem aq_aqDf_ne_lRn : aqDf ≠ lRn := by decide
@[simp] theorem aq_lRn_ne_aqDf : lRn ≠ aqDf := by decide
@[simp] theorem aq_aqDf_ne_lFle : aqDf ≠ lFle := by decide
@[simp] theorem aq_lFle_ne_aqDf : lFle ≠ aqDf := by decide
@[simp] theorem aq_aqDf_ne_lFls : aqDf ≠ lFls := by decide
@[simp] theorem aq_lFls_ne_aqDf : lFls ≠ aqDf := by decide
@[simp] theorem aq_aqDf_ne_lDir : aqDf ≠ lDir := by decide
@[simp] theorem aq_lDir_ne_aqDf : lDir ≠ aqDf := by decide
@[simp] theorem aq_aqDf_ne_lKb : aqDf ≠ lKb := by decide
@[simp] theorem aq_lKb_ne_aqDf : lKb ≠ aqDf := by decide
@[simp] theorem aq_aqDf_ne_kFu : aqDf ≠ kFu := by decide
@[simp] theorem aq_kFu_ne_aqDf : kFu ≠ aqDf := by decide
@[simp] theorem aq_aqDf_ne_kD : aqDf ≠ kD := by decide
@[simp] theorem aq_kD_ne_aqDf : kD ≠ aqDf := by decide
@[simp] theorem aq_aqDf_ne_rkR : aqDf ≠ rkR := by decide
@[simp] theorem aq_rkR_ne_aqDf : rkR ≠ aqDf := by decide
@[simp] theorem aq_aqDf_ne_rkJ : aqDf ≠ rkJ := by decide
@[simp] theorem aq_rkJ_ne_aqDf : rkJ ≠ aqDf := by decide
@[simp] theorem aq_aqDf_ne_rkT : aqDf ≠ rkT := by decide
@[simp] theorem aq_rkT_ne_aqDf : rkT ≠ aqDf := by decide
@[simp] theorem aq_aqDf_ne_rkM : aqDf ≠ rkM := by decide
@[simp] theorem aq_rkM_ne_aqDf : rkM ≠ aqDf := by decide
@[simp] theorem aq_aqIr_ne_aqAn : aqIr ≠ aqAn := by decide
@[simp] theorem aq_aqIr_ne_aq1 : aqIr ≠ aq1 := by decide
@[simp] theorem aq_aqIr_ne_aqTm : aqIr ≠ aqTm := by decide
@[simp] theorem aq_aqIr_ne_aqHh : aqIr ≠ aqHh := by decide
@[simp] theorem aq_aqIr_ne_aqTp : aqIr ≠ aqTp := by decide
@[simp] theorem aq_aqIr_ne_aqUs : aqIr ≠ aqUs := by decide
@[simp] theorem aq_aqIr_ne_aqTa : aqIr ≠ aqTa := by decide
@[simp] theorem aq_aqIr_ne_aqTl : aqIr ≠ aqTl := by decide
@[simp] theorem aq_aqIr_ne_aqNp : aqIr ≠ aqNp := by decide
@[simp] theorem aq_aqIr_ne_aqLp : aqIr ≠ aqLp := by decide
@[simp] theorem aq_aqIr_ne_aqLl : aqIr ≠ aqLl := by decide
@[simp] theorem aq_aqIr_ne_aqAr : aqIr ≠ aqAr := by decide
@[simp] theorem aq_aqIr_ne_aqP0 : aqIr ≠ aqP0 := by decide
@[simp] theorem aq_aqIr_ne_aqP1 : aqIr ≠ aqP1 := by decide
@[simp] theorem aq_aqIr_ne_aqB1 : aqIr ≠ aqB1 := by decide
@[simp] theorem aq_aqIr_ne_aqB2 : aqIr ≠ aqB2 := by decide
@[simp] theorem aq_aqIr_ne_aqRc : aqIr ≠ aqRc := by decide
@[simp] theorem aq_aqIr_ne_aqHd : aqIr ≠ aqHd := by decide
@[simp] theorem aq_aqIr_ne_aqFl : aqIr ≠ aqFl := by decide
@[simp] theorem aq_aqIr_ne_aqFab : aqIr ≠ aqFab := by decide
@[simp] theorem aq_aqIr_ne_aqFs : aqIr ≠ aqFs := by decide
@[simp] theorem aq_aqIr_ne_aqK2 : aqIr ≠ aqK2 := by decide
@[simp] theorem aq_aqIr_ne_aqDf : aqIr ≠ aqDf := by decide
@[simp] theorem aq_aqIr_ne_lFl : aqIr ≠ lFl := by decide
@[simp] theorem aq_lFl_ne_aqIr : lFl ≠ aqIr := by decide
@[simp] theorem aq_aqIr_ne_lDh : aqIr ≠ lDh := by decide
@[simp] theorem aq_lDh_ne_aqIr : lDh ≠ aqIr := by decide
@[simp] theorem aq_aqIr_ne_lDt : aqIr ≠ lDt := by decide
@[simp] theorem aq_lDt_ne_aqIr : lDt ≠ aqIr := by decide
@[simp] theorem aq_aqIr_ne_lDg : aqIr ≠ lDg := by decide
@[simp] theorem aq_lDg_ne_aqIr : lDg ≠ aqIr := by decide
@[simp] theorem aq_aqIr_ne_lDi : aqIr ≠ lDi := by decide
@[simp] theorem aq_lDi_ne_aqIr : lDi ≠ aqIr := by decide
@[simp] theorem aq_aqIr_ne_lRp : aqIr ≠ lRp := by decide
@[simp] theorem aq_lRp_ne_aqIr : lRp ≠ aqIr := by decide
@[simp] theorem aq_aqIr_ne_lRn : aqIr ≠ lRn := by decide
@[simp] theorem aq_lRn_ne_aqIr : lRn ≠ aqIr := by decide
@[simp] theorem aq_aqIr_ne_lFle : aqIr ≠ lFle := by decide
@[simp] theorem aq_lFle_ne_aqIr : lFle ≠ aqIr := by decide
@[simp] theorem aq_aqIr_ne_lFls : aqIr ≠ lFls := by decide
@[simp] theorem aq_lFls_ne_aqIr : lFls ≠ aqIr := by decide
@[simp] theorem aq_aqIr_ne_lDir : aqIr ≠ lDir := by decide
@[simp] theorem aq_lDir_ne_aqIr : lDir ≠ aqIr := by decide
@[simp] theorem aq_aqIr_ne_lKb : aqIr ≠ lKb := by decide
@[simp] theorem aq_lKb_ne_aqIr : lKb ≠ aqIr := by decide
@[simp] theorem aq_aqIr_ne_kFu : aqIr ≠ kFu := by decide
@[simp] theorem aq_kFu_ne_aqIr : kFu ≠ aqIr := by decide
@[simp] theorem aq_aqIr_ne_kD : aqIr ≠ kD := by decide
@[simp] theorem aq_kD_ne_aqIr : kD ≠ aqIr := by decide
@[simp] theorem aq_aqIr_ne_rkR : aqIr ≠ rkR := by decide
@[simp] theorem aq_rkR_ne_aqIr : rkR ≠ aqIr := by decide
@[simp] theorem aq_aqIr_ne_rkJ : aqIr ≠ rkJ := by decide
@[simp] theorem aq_rkJ_ne_aqIr : rkJ ≠ aqIr := by decide
@[simp] theorem aq_aqIr_ne_rkT : aqIr ≠ rkT := by decide
@[simp] theorem aq_rkT_ne_aqIr : rkT ≠ aqIr := by decide
@[simp] theorem aq_aqIr_ne_rkM : aqIr ≠ rkM := by decide
@[simp] theorem aq_rkM_ne_aqIr : rkM ≠ aqIr := by decide

def raCert (v : Bool) : ProgHOL 64 :=
  if v then
    .seq (.call (some (some (.local, aqIr), none)) fPi [vv kFu, vv kD, vv aqFab, vv rkM])
      (.ite (.cmp .equal (vv aqIr) (.const 0)) (.return (vv rkM)) (.return (vv aqFab)))
  else .return (vv aqFab)

def raLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, aqAn, aq1, aqTm, aqHh, aqTp, aqUs, aqTa, aqTl, aqNp, aqLp, aqLl, aqAr, aqP0, aqP1, aqB1, aqB2, aqRc, aqHd, aqFl, aqFab, aqFs, aqK2, aqDf, aqIr]

def raBody (v : Bool) (C : Ctx) : ProgHOL 64 := prologue raLocals
  (.seq (.assign .local aqAn (.load .one (.const (ecell C (C.PO + PIN_AND)))))
  (.ite (.cmp .notEqual (vv rkT) (vv aqAn)) (.return (vv rkM))
  (.seq (.call (some (some (.local, aq1), none)) fIO [vv kFu, vv kD, vv rkM])
  (.seq (.call (some (some (.local, aqTm), none)) fW [vv kFu, vv kD, vv aq1])
  (.seq (.call (some (some (.local, aqHh), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv aqTm])
  (.ite (tagIsE aqHh 3)
  (.seq (.assign .local lFl (vv lFle))
  (.seq (.assign .local lDh (vv aqHh))
  (.seq eViewP
  (.seq (.assign .local aqTp (.load .one (vv lRp)))
  (.seq (.assign .local aqUs (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (.assign .local lFl (vv lFls))
  (.seq (.assign .local lDh (vv aqUs))
  (.seq lsViewP
  (.seq (.call (some (some (.local, aqTa), none)) ExG.fGaa [.const (BitVec.ofNat 64 coreWalkFuel), vv aqTm])
  (.seq (.assign .local aqTl (.load .one (vv aqTa)))
  (.seq (.assign .local aqNp (.load .one (.op .add [vv rkJ, .const 32])))
  (.seq (.assign .local aqRc (.load .one (vv rkR)))
  (.seq (.call (some (some (.local, aqAr), none)) fAr [vv aqRc, vv aqNp])
  (.seq (.assign .local aqLp (.load .one (.op .add [vv rkJ, .const 16])))
  (.seq (.assign .local aqLl (.load .one (vv aqLp)))
  (.ite (.cmp .notEqual (vv aqTp) (vv rkT)) (.return (vv rkM))
  (.ite (.cmp .notEqual (vv aqTl) (vv aqNp)) (.return (vv rkM))
  (.ite (.cmp .notEqual (vv aqLl) (vv lRn)) (.return (vv rkM))
  (.ite (.cmp .equal (vv aqAr) (.const 0)) (.return (vv rkM))
  (.seq (.call (some (some (.local, aqP0), none)) fInternProj [vv rkT, vv rkM, .const 0])
  (.seq (.call (some (some (.local, aqP1), none)) fInternProj [vv rkT, vv rkM, .const 1])
  (.seq (.call (some (some (.local, aqB1), none)) ExPre.fAppend [vv aqTa, vv aqP0])
  (.seq (.call (some (some (.local, aqB2), none)) ExPre.fAppend [vv aqB1, vv aqP1])
  (.seq (.assign .local aqRc (.load .one (vv rkR)))
  (.seq (.call (some (some (.local, aqHd), none)) fInternConst [vv aqRc, vv aqUs])
  (.seq (.assign .local aqFl (.load .one (vv aqB2)))
  (.seq (.call (some (some (.local, aqFab), none)) ExK.fMka [vv aqHd, vv aqB2, .const 0, vv aqFl])
  (.seq (.call (some (some (.local, aqFs), none)) fFab [vv kD, vv aqFab, vv rkM])
  (.ite (.cmp .equal (vv aqFs) (.const 0)) (.return (vv rkM))
  (.seq (.call (some (some (.local, aqK2), none)) fIO [vv kFu, vv kD, vv aqFab])
  (.seq (.call (some (some (.local, aqDf), none)) fD [vv kFu, vv kD, vv aqTm, vv aqK2])
  (.ite (.cmp .equal (vv aqDf) (.const 0)) (.return (vv rkM))
  (raCert v)))))))))))))))))))))))))))))))))
  (.return (vv rkM))))))))

end ConPanqueque.T.WC

namespace ConPanqueque.T.WC
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

section
variable {σ : Type}

structure RaCodes (C : Ctx) (Bfab : ProgHOL 64) : Prop where
  io : C.code.lookup fIO = some (pmap kParams, inferIOE C fIOB, .one)
  w : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one)
  d : C.code.lookup fD = some (pmap dParams, dE C, .one)
  af : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  gaa : C.code.lookup ExG.fGaa = some ([(pFu, .one), (pH, .one)], ExG.gaaBody C, .one)
  ic : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one)
  mka : C.code.lookup ExK.fMka = some ([(ExK.pF, .one), (ExK.pP, .one), (ExK.pI, .one), (ExK.pN, .one)],
    ExK.mkaBody, .one)
  ia : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)
  ip : C.code.lookup fInternProj = some ([(lEp, .one), (lEe, .one), (lIw, .one)], projBody, .one)
  app : C.code.lookup ExPre.fAppend = some (ExPre.appParams.map (fun p => (p, ShapeHOL.one)), ExPre.appBody C, .one)
  ar : C.code.lookup fAr = some (arParams.map (fun p => (p, ShapeHOL.one)), arBody C, .one)
  mg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  mp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  fab : C.code.lookup fFab = some (fbParams.map (fun p => (p, ShapeHOL.one)), Bfab, .one)
  pi : C.code.lookup fPi = some (piParams.map (fun p => (p, ShapeHOL.one)), piBody C, .one)
  eqv : C.code.lookup LLeq.fEqv = some ([(LEq.pLa, .one), (LEq.pLb, .one)], LLeq.eqvBody, .one)

theorem ra_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ raLocals → (ctxEnv C ++ rkParams.zip vals).get x = none :=
  Knot.params_none C raLocals rkParams vals (by decide) (by decide)

theorem ra_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (Bfab : ProgHOL 64) (hc : RaCodes C Bfab)
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
    (hLE : ∀ (H : List (BitVec 64)) s1 (u v : LIdx), C.H <+: H → (denoteL s1.store.ls u).isSome = true →
      (denoteL s1.store.ls v).isSome = true →
      SpecR (σ := σ) (Pre (ctxH C H) s1 [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s1 (lvlEq? u v)
        (LLeq.PostOB (ctxH C H))) :
    SpecR (σ := σ) (Pre C s (rkParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, ecell C qr, ecell C qj, Enc.idxW T,
      Enc.idxW m])) (raBody mode.verifiedChecks C) s (rescueAnd mode (knot mode C n) C.fe d rl cvj cnP T m) (PostK C) := by
  refine specR_prologue (Knot.postK_locals C) (ra_none C _) ?_
  unfold rescueAnd
  show SpecR _ _ _ (pinAt PIN_AND >>= _) _
  have hretM : ∀ {Γ : Env} {M : Mem} {H : List (BitVec 64)} {s2 : AState}, C.H <+: H → Γ.get rkM = some (Enc.idxW m) →
      SpecR (σ := σ) (Inv (ctxH C H) s2 Γ M (ctxLocals ++ raLocals)) (.return (vv rkM)) s2 (pure m) (PostK C) :=
    fun hp hE => specR_returnI _ (Enc.idxW m) (by simpa using hE)
      (fun t ht => ⟨_, hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_pinAtI hok PIN_AND (by decide) aqAn (by decide) ?_
  by_cases hTa : T = C.pins.names[PIN_AND]'(by rw [hok.pinsRel.1]; decide)
  swap
  · have hne : Enc.idxW T ≠ Enc.idxW (C.pins.names[PIN_AND]'(by rw [hok.pinsRel.1]; decide)) :=
      fun e => hTa (Enc.idxW_inj e)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, rkParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [ite_eq_right hTa]
    exact hretM (List.prefix_refl _) (by simp +decide [Env.get, rkParams, ctxEnv])
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, rkParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hTa])
    (fun h => absurd rfl h) (fun _ => ?_)
  rw [ite_eq_left hTa]
  refine Big.specR_callKC aq1 fIO kParams [vv kFu, vv kD, vv rkM] (inferIOE C fIOB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW m] (by decide) rfl (by decide) hc.io
    ⟨by simp +decide [Env.get, rkParams, ctxEnv], by simp +decide [Env.get, rkParams, ctxEnv],
      by simp +decide [Env.get, rkParams, ctxEnv], trivial⟩ (hIO C.H s (List.prefix_refl _) m)
    (fun k1 s1 H1 hp1 _ => ?_)
  refine Big.specR_callKC (C := ctxH C H1) aqTm fW kParams [vv kFu, vv kD, vv aq1] (whnfE C fWB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW k1] (by decide) rfl (by decide) hc.w
    ⟨by simp +decide [Env.get, rkParams, ctxEnv], by simp +decide [Env.get, rkParams, ctxEnv], by simp, trivial⟩
    (hW H1 s1 hp1 k1) (fun tm s2 H2 hp2 _ => ?_)
  have hp12 : C.H <+: H2 := hp1.trans hp2
  have hok2 := ctxOK_H hok H2
  refine specR_callNIM (C := ctxH C H2) aqHh fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv aqTm]
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
  refine Knot.specR_tagIteV aqHh hh 3 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
  swap
  · rw [ite_eq_right (show ¬ (hh.tag == ETag.const) = true by simpa [ETag.const] using htg)]
    exact hretM hp12 (by simp +decide [Env.get, rkParams, ctxEnv])
  rw [ite_eq_left (show (hh.tag == ETag.const) = true by simp [htg, ETag.const])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv aqHh) (Enc.idxW hh) (by decide) (by simp) ?_
  refine ILP.specR_viewIv (C := ctxH C H2) hh (by simp) (by simp +decide [Env.get, ctxEnv] <;> rfl)
    (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
  have h3 : v.tagN = 3 := by rw [htn, htg]; rfl
  obtain ⟨T', ust, rfl⟩ := UD.tagN_const h3
  dsimp only
  refine specR_loadI' aqTp (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW T') (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW T') [Enc.idxW ust] []) ?_
  refine specR_loadI' aqUs _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW ust) (by decide) (by simp +decide [sev]) rfl
    (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW T') (Enc.idxW ust) [] []) ?_
  refine specR_dropM ?_
  refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv aqUs) (Enc.idxW ust) (by decide) (by simp) ?_
  refine specR_lsviewPI (C := ctxH C H2) ust (by simp) (by simp +decide [Env.get, ctxEnv] <;> rfl)
    (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun vl Pl hvl _ hvll => ?_)
  refine specR_runBind (viewLsLen_run ust s2 vl hvl) ?_
  dsimp only
  refine specR_callNIH (C := ctxH C H2) aqTa ExG.fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv aqTm]
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
  have hcij' := hcij
  obtain ⟨⟨_, ⟨wl, hwl, hlps⟩, _⟩, _, hnp, _, hind⟩ := hcij'
  simp only [IConstantInfo.toConstantVal] at hlps
  obtain ⟨ol, hwol, hblk⟩ := hlps
  refine UD.specR_heapLoadI' (C := ctxH C H3) aqTl (vv aqTa) oa _ hba.1 (by decide) (by simp; rfl) ?_
  refine specR_envLoadI (C := ctxH C H3) aqNp (.op .add [vv rkJ, .const 32]) (qj + 4) _ (by decide)
    (by simp +decide [sev, Env.get, rkParams, ctxEnv]; exact UD.ecell_add32 C qj) hnp.1 ?_
  refine specR_envLoadI (C := ctxH C H3) aqRc (vv rkR) qr _ (by decide) (by simp +decide [Env.get, rkParams, ctxEnv]; rfl)
    hrule.1 ?_
  refine specR_callNIH (C := ctxH C H3) aqAr fAr arParams [vv aqRc, vv aqNp] (arBody C)
    [Enc.idxW rl.ctor, BitVec.ofNat 64 cnP] (by decide) rfl (by decide) hc.ar ⟨by simp, by simp, trivial⟩
    (PostB (ctxH C H3)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu arParams _ rfl hlk)
      (ar_spec (ctxH C H3) hok3 hc.mg hc.mp s3 rl.ctor cnP hnp.2))
    (fun ars w s4 H4 hp4 hw => ?_)
  subst hw
  have hp14 : C.H <+: H4 := hp13.trans hp4
  have hok4 := ctxOK_H hok H4
  refine specR_envLoadI (C := ctxH C H4) aqLp (.op .add [vv rkJ, .const 16]) (qj + 2) _ (by decide)
    (by simp +decide [sev, Env.get, rkParams, ctxEnv]; exact UD.ecell_add16 C qj)
    (by rw [show qj + 2 = qj + 1 + 1 by omega]; exact hwl) ?_
  refine specR_envLoadI (C := ctxH C H4) aqLl (vv aqLp) ol _ (by decide) (by simp [hwol]; rfl) hblk.1 ?_
  refine specR_atEntry fun t4 ht4 => ?_
  have htl := blk_small0 hok4 ht4.sr (blkAt_mono hba hp4)
  simp only [List.length_map] at htl
  have hnp2 := hnp.2
  have hlpl : cvj.levelParams.length < 2 ^ 61 := by
    have h1 := blkAt_len (show BlkAt C.EH ol (cvj.levelParams.map Enc.idxW) from hblk)
    have h2 := ht4.sr.env.1.len; have h3 := hok.envLay
    simp only [List.length_map] at h1; simp only [ctxH] at h2; omega
  have hvl' : vl.length < 2 ^ 61 := by simpa using hvll
  by_cases hT : T' = T
  swap
  · have hne : Enc.idxW T' ≠ Enc.idxW T := fun e => hT (Enc.idxW_inj e)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, rkParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [ite_eq_right (by simp [hT])]
    exact hretM hp14 (by simp +decide [Env.get, rkParams, ctxEnv])
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, rkParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hT])
    (fun h => absurd rfl h) (fun _ => ?_)
  by_cases hA : targs.length = cnP
  swap
  · have hne : BitVec.ofNat 64 targs.length ≠ BitVec.ofNat 64 cnP := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    rw [ite_eq_right (by simp [hA])]
    exact hretM hp14 (by simp +decide [Env.get, rkParams, ctxEnv])
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hA]) (fun h => absurd rfl h)
    (fun _ => ?_)
  by_cases hL : cvj.levelParams.length = vl.length
  swap
  · have hne : BitVec.ofNat 64 cvj.levelParams.length ≠ BitVec.ofNat 64 vl.length := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    rw [ite_eq_right (by simp [hL])]
    exact hretM hp14 (by simp +decide [Env.get, rkParams, ctxEnv])
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hL]) (fun h => absurd rfl h)
    (fun _ => ?_)
  cases ars
  · refine specR_ifI _ 1 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    rw [ite_eq_right (by simp)]
    exact hretM hp14 (by simp +decide [Env.get, rkParams, ctxEnv])
  refine specR_ifI _ 0 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
    (fun _ => ?_)
  rw [ite_eq_left ⟨hT, hA, hL, rfl⟩]
  refine specR_internProjI (C := ctxH C H4) ra hok4 hc.ip aqP0 (vv rkT) (vv rkM) (.const 0) T 0 m (by decide)
    (by decide) (by simp +decide [Env.get, rkParams, ctxEnv]) (by simp +decide [Env.get, rkParams, ctxEnv]) rfl
    (fun p0 s5 => ?_)
  refine specR_internProjI (C := ctxH C H4) ra hok4 hc.ip aqP1 (vv rkT) (vv rkM) (.const 1) T 1 m (by decide)
    (by decide) (by simp +decide [Env.get, rkParams, ctxEnv]) (by simp +decide [Env.get, rkParams, ctxEnv]) rfl
    (fun p1 s6 => ?_)
  refine ExPre.specR_callApp (C := ctxH C H4) hok4 hc.app aqB1 (vv aqTa) (vv aqP0) oa (targs.map Enc.idxW)
    (Enc.idxW p0) (by decide) (blkAt_mono hba hp4) (by simp; rfl) (by simp) (fun H5 o5 hp5 hb5 => ?_)
  refine ExPre.specR_callApp (C := ctxH C H5) (ctxOK_H hok H5) hc.app aqB2 (vv aqB1) (vv aqP1) o5
    (targs.map Enc.idxW ++ [Enc.idxW p0]) (Enc.idxW p1) (by decide) hb5 (by simp; rfl) (by simp)
    (fun H6 o6 hp6 hb6 => ?_)
  have hp16 : C.H <+: H6 := hp14.trans (hp5.trans hp6)
  have hok6 := ctxOK_H hok H6
  have hb6' : BlkAt H6 o6 ((targs ++ [p0, p1]).map Enc.idxW) := by simpa using hb6
  refine specR_envLoadI (C := ctxH C H6) aqRc (vv rkR) qr _ (by decide) (by simp +decide [Env.get, rkParams, ctxEnv]; rfl)
    hrule.1 ?_
  refine ILP.callE_spec (C := ctxH C H6) aqHd fInternConst [lEn, lEus] [vv aqRc, vv aqUs] constBody
    [Enc.idxW rl.ctor, Enc.idxW ust] (by decide) rfl (by decide) hc.ic ⟨by simp, by simp, trivial⟩
    (by exact const_body_spec ra (ctxH C H6) hok6 s6 _ _) (fun hd s7 => ?_)
  refine UD.specR_heapLoadI' (C := ctxH C H6) aqFl (vv aqB2) o6 _ hb6'.1 (by decide) (by simp; rfl) ?_
  refine specR_atEntry fun t6 ht6 => ?_
  have hfl := blk_small0 hok6 ht6.sr hb6'
  simp only [List.length_map] at hfl
  refine ILP.callE_spec (C := ctxH C H6) aqFab ExK.fMka [ExK.pF, ExK.pP, ExK.pI, ExK.pN]
    [vv aqHd, vv aqB2, .const 0, vv aqFl] ExK.mkaBody [Enc.idxW hd, cellA C o6, BitVec.ofNat 64 0,
      BitVec.ofNat 64 (targs ++ [p0, p1]).length] (by decide) rfl (by decide) hc.mka ⟨by simp, by simp; rfl, rfl, by simp, trivial⟩
    (by have h := (ExK.mkAppN_spec (σ := σ) ra (ctxH C H6) hok6 hc.mka hc.ia o6 (targs ++ [p0, p1]) hb6' (by omega) 0 (Nat.zero_le _) hd s7); simp only [List.drop_zero] at h; exact h)
    (fun fab s8 => ?_)
  refine specR_callNIH (C := ctxH C H6) aqFs fFab fbParams [vv kD, vv aqFab, vv rkM] Bfab
    [BitVec.ofNat 64 d, Enc.idxW fab, Enc.idxW m] (by decide) rfl (by decide) hc.fab
    ⟨by simp +decide [Env.get, rkParams, ctxEnv], by simp, by simp +decide [Env.get, rkParams, ctxEnv], trivial⟩
    (PostB (ctxH C H6)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fbParams _ rfl hlk) (hFab H6 s8 fab m hp16))
    (fun fs w s6 H4 hp4 hw => ?_)
  subst hw
  have hp14 : C.H <+: H4 := hp16.trans hp4
  cases fs
  · refine specR_ifI _ 1 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [Bool.false_eq_true, ite_false]
    exact hretM hp14 (by simp +decide [Env.get, rkParams, ctxEnv])
  refine specR_ifI _ 0 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
  simp only [ite_true]
  refine Big.specR_callKC (C := ctxH C H4) aqK2 fIO kParams [vv kFu, vv kD, vv aqFab] (inferIOE C fIOB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW fab] (by decide) rfl (by decide) hc.io
    ⟨by simp +decide [Env.get, rkParams, ctxEnv], by simp +decide [Env.get, rkParams, ctxEnv], by simp, trivial⟩
    (hIO H4 s6 hp14 fab) (fun k2 s7 H5 hp5 _ => ?_)
  have hp15 : C.H <+: H5 := hp14.trans hp5
  refine specR_callNIH (C := ctxH C H5) aqDf fD dParams [vv kFu, vv kD, vv aqTm, vv aqK2] (dE C)
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
  · simp only [raCert, Bool.false_eq_true, ite_false, Bool.not_false, ite_true, pure_bind]
    exact specR_returnI _ (Enc.idxW fab) (by simp)
      (fun t ht => ⟨H6, hp16, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · simp only [raCert, ite_true, Bool.not_true, Bool.false_eq_true, ite_false]
    refine specR_callNIH (C := ctxH C H6) aqIr fPi piParams [vv kFu, vv kD, vv aqFab, vv rkM] (piBody C)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW fab, Enc.idxW m] (by decide) rfl (by decide) hc.pi
      ⟨by simp +decide [Env.get, rkParams, ctxEnv], by simp +decide [Env.get, rkParams, ctxEnv], by simp,
        by simp +decide [Env.get, rkParams, ctxEnv], trivial⟩
      (PostB (ctxH C H6)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu piParams _ rfl hlk)
        (pi_spec mode n (ctxH C H6) (ctxOK_H hok H6) hc.io hc.w hc.eqv s8 d fab m
          (fun H s9 hp e' => hIO H s9 (hp16.trans hp) e') (fun H s9 hp e' => hW H s9 (hp16.trans hp) e')
          (fun H s9 u v hp hu hv => hLE H s9 u v (hp16.trans hp) hu hv)))
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
