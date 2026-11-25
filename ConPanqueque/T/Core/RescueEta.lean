import ConPanqueque.T.Core.RescueK
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# The rescue's structure-η branch (`to_cnstr_when_structure`)

The major's type headed by the family at the table's parameter count and the family's level arity; the
family's sort never zero at the use (`familyNeverZeroAt`, a callee); the fabrication from the table's constructor
applied to the type's arguments and the major's projections (`etaFabArgsE`); the scope guard. No certificate.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def eq1 := ofString "eq1"
def eqTm := ofString "eqtm"
def eqHh := ofString "eqhh"
def eqTp := ofString "eqtp"
def eqUs := ofString "equs"
def eqTa := ofString "eqta"
def eqTl := ofString "eqtl"
def eqNp := ofString "eqnp"
def eqLp := ofString "eqlp"
def eqLn := ofString "eqln"
def eqFz := ofString "eqfz"
def eqNf := ofString "eqnf"
def eqFa := ofString "eqfa"
def eqTc := ofString "eqtc"
def eqHd := ofString "eqhd"
def eqFl := ofString "eqfl"
def eqFab := ofString "eqfab"
def eqFs := ofString "eqfs"
def fFz := ofString "familyNeverZeroAt"
def fzQ := ofString "fzq"
def fzU := ofString "fzu"
def fzParams : List MlS := [kFu, kD, fzQ, fzU]

@[simp] theorem eq_eq1_ne_eqTm : eq1 ≠ eqTm := by decide
@[simp] theorem eq_eq1_ne_eqHh : eq1 ≠ eqHh := by decide
@[simp] theorem eq_eq1_ne_eqTp : eq1 ≠ eqTp := by decide
@[simp] theorem eq_eq1_ne_eqUs : eq1 ≠ eqUs := by decide
@[simp] theorem eq_eq1_ne_eqTa : eq1 ≠ eqTa := by decide
@[simp] theorem eq_eq1_ne_eqTl : eq1 ≠ eqTl := by decide
@[simp] theorem eq_eq1_ne_eqNp : eq1 ≠ eqNp := by decide
@[simp] theorem eq_eq1_ne_eqLp : eq1 ≠ eqLp := by decide
@[simp] theorem eq_eq1_ne_eqLn : eq1 ≠ eqLn := by decide
@[simp] theorem eq_eq1_ne_eqFz : eq1 ≠ eqFz := by decide
@[simp] theorem eq_eq1_ne_eqNf : eq1 ≠ eqNf := by decide
@[simp] theorem eq_eq1_ne_eqFa : eq1 ≠ eqFa := by decide
@[simp] theorem eq_eq1_ne_eqTc : eq1 ≠ eqTc := by decide
@[simp] theorem eq_eq1_ne_eqHd : eq1 ≠ eqHd := by decide
@[simp] theorem eq_eq1_ne_eqFl : eq1 ≠ eqFl := by decide
@[simp] theorem eq_eq1_ne_eqFab : eq1 ≠ eqFab := by decide
@[simp] theorem eq_eq1_ne_eqFs : eq1 ≠ eqFs := by decide
@[simp] theorem eq_eq1_ne_lFl : eq1 ≠ lFl := by decide
@[simp] theorem eq_lFl_ne_eq1 : lFl ≠ eq1 := by decide
@[simp] theorem eq_eq1_ne_lDh : eq1 ≠ lDh := by decide
@[simp] theorem eq_lDh_ne_eq1 : lDh ≠ eq1 := by decide
@[simp] theorem eq_eq1_ne_lDt : eq1 ≠ lDt := by decide
@[simp] theorem eq_lDt_ne_eq1 : lDt ≠ eq1 := by decide
@[simp] theorem eq_eq1_ne_lDg : eq1 ≠ lDg := by decide
@[simp] theorem eq_lDg_ne_eq1 : lDg ≠ eq1 := by decide
@[simp] theorem eq_eq1_ne_lDi : eq1 ≠ lDi := by decide
@[simp] theorem eq_lDi_ne_eq1 : lDi ≠ eq1 := by decide
@[simp] theorem eq_eq1_ne_lRp : eq1 ≠ lRp := by decide
@[simp] theorem eq_lRp_ne_eq1 : lRp ≠ eq1 := by decide
@[simp] theorem eq_eq1_ne_lRn : eq1 ≠ lRn := by decide
@[simp] theorem eq_lRn_ne_eq1 : lRn ≠ eq1 := by decide
@[simp] theorem eq_eq1_ne_lFle : eq1 ≠ lFle := by decide
@[simp] theorem eq_lFle_ne_eq1 : lFle ≠ eq1 := by decide
@[simp] theorem eq_eq1_ne_lFls : eq1 ≠ lFls := by decide
@[simp] theorem eq_lFls_ne_eq1 : lFls ≠ eq1 := by decide
@[simp] theorem eq_eq1_ne_lDir : eq1 ≠ lDir := by decide
@[simp] theorem eq_lDir_ne_eq1 : lDir ≠ eq1 := by decide
@[simp] theorem eq_eq1_ne_lKb : eq1 ≠ lKb := by decide
@[simp] theorem eq_lKb_ne_eq1 : lKb ≠ eq1 := by decide
@[simp] theorem eq_eq1_ne_kFu : eq1 ≠ kFu := by decide
@[simp] theorem eq_kFu_ne_eq1 : kFu ≠ eq1 := by decide
@[simp] theorem eq_eq1_ne_kD : eq1 ≠ kD := by decide
@[simp] theorem eq_kD_ne_eq1 : kD ≠ eq1 := by decide
@[simp] theorem eq_eq1_ne_rkR : eq1 ≠ rkR := by decide
@[simp] theorem eq_rkR_ne_eq1 : rkR ≠ eq1 := by decide
@[simp] theorem eq_eq1_ne_rkJ : eq1 ≠ rkJ := by decide
@[simp] theorem eq_rkJ_ne_eq1 : rkJ ≠ eq1 := by decide
@[simp] theorem eq_eq1_ne_rkT : eq1 ≠ rkT := by decide
@[simp] theorem eq_rkT_ne_eq1 : rkT ≠ eq1 := by decide
@[simp] theorem eq_eq1_ne_rkM : eq1 ≠ rkM := by decide
@[simp] theorem eq_rkM_ne_eq1 : rkM ≠ eq1 := by decide
@[simp] theorem eq_eq1_ne_reF : eq1 ≠ reF := by decide
@[simp] theorem eq_reF_ne_eq1 : reF ≠ eq1 := by decide
@[simp] theorem eq_eq1_ne_reO : eq1 ≠ reO := by decide
@[simp] theorem eq_reO_ne_eq1 : reO ≠ eq1 := by decide
@[simp] theorem eq_eqTm_ne_eq1 : eqTm ≠ eq1 := by decide
@[simp] theorem eq_eqTm_ne_eqHh : eqTm ≠ eqHh := by decide
@[simp] theorem eq_eqTm_ne_eqTp : eqTm ≠ eqTp := by decide
@[simp] theorem eq_eqTm_ne_eqUs : eqTm ≠ eqUs := by decide
@[simp] theorem eq_eqTm_ne_eqTa : eqTm ≠ eqTa := by decide
@[simp] theorem eq_eqTm_ne_eqTl : eqTm ≠ eqTl := by decide
@[simp] theorem eq_eqTm_ne_eqNp : eqTm ≠ eqNp := by decide
@[simp] theorem eq_eqTm_ne_eqLp : eqTm ≠ eqLp := by decide
@[simp] theorem eq_eqTm_ne_eqLn : eqTm ≠ eqLn := by decide
@[simp] theorem eq_eqTm_ne_eqFz : eqTm ≠ eqFz := by decide
@[simp] theorem eq_eqTm_ne_eqNf : eqTm ≠ eqNf := by decide
@[simp] theorem eq_eqTm_ne_eqFa : eqTm ≠ eqFa := by decide
@[simp] theorem eq_eqTm_ne_eqTc : eqTm ≠ eqTc := by decide
@[simp] theorem eq_eqTm_ne_eqHd : eqTm ≠ eqHd := by decide
@[simp] theorem eq_eqTm_ne_eqFl : eqTm ≠ eqFl := by decide
@[simp] theorem eq_eqTm_ne_eqFab : eqTm ≠ eqFab := by decide
@[simp] theorem eq_eqTm_ne_eqFs : eqTm ≠ eqFs := by decide
@[simp] theorem eq_eqTm_ne_lFl : eqTm ≠ lFl := by decide
@[simp] theorem eq_lFl_ne_eqTm : lFl ≠ eqTm := by decide
@[simp] theorem eq_eqTm_ne_lDh : eqTm ≠ lDh := by decide
@[simp] theorem eq_lDh_ne_eqTm : lDh ≠ eqTm := by decide
@[simp] theorem eq_eqTm_ne_lDt : eqTm ≠ lDt := by decide
@[simp] theorem eq_lDt_ne_eqTm : lDt ≠ eqTm := by decide
@[simp] theorem eq_eqTm_ne_lDg : eqTm ≠ lDg := by decide
@[simp] theorem eq_lDg_ne_eqTm : lDg ≠ eqTm := by decide
@[simp] theorem eq_eqTm_ne_lDi : eqTm ≠ lDi := by decide
@[simp] theorem eq_lDi_ne_eqTm : lDi ≠ eqTm := by decide
@[simp] theorem eq_eqTm_ne_lRp : eqTm ≠ lRp := by decide
@[simp] theorem eq_lRp_ne_eqTm : lRp ≠ eqTm := by decide
@[simp] theorem eq_eqTm_ne_lRn : eqTm ≠ lRn := by decide
@[simp] theorem eq_lRn_ne_eqTm : lRn ≠ eqTm := by decide
@[simp] theorem eq_eqTm_ne_lFle : eqTm ≠ lFle := by decide
@[simp] theorem eq_lFle_ne_eqTm : lFle ≠ eqTm := by decide
@[simp] theorem eq_eqTm_ne_lFls : eqTm ≠ lFls := by decide
@[simp] theorem eq_lFls_ne_eqTm : lFls ≠ eqTm := by decide
@[simp] theorem eq_eqTm_ne_lDir : eqTm ≠ lDir := by decide
@[simp] theorem eq_lDir_ne_eqTm : lDir ≠ eqTm := by decide
@[simp] theorem eq_eqTm_ne_lKb : eqTm ≠ lKb := by decide
@[simp] theorem eq_lKb_ne_eqTm : lKb ≠ eqTm := by decide
@[simp] theorem eq_eqTm_ne_kFu : eqTm ≠ kFu := by decide
@[simp] theorem eq_kFu_ne_eqTm : kFu ≠ eqTm := by decide
@[simp] theorem eq_eqTm_ne_kD : eqTm ≠ kD := by decide
@[simp] theorem eq_kD_ne_eqTm : kD ≠ eqTm := by decide
@[simp] theorem eq_eqTm_ne_rkR : eqTm ≠ rkR := by decide
@[simp] theorem eq_rkR_ne_eqTm : rkR ≠ eqTm := by decide
@[simp] theorem eq_eqTm_ne_rkJ : eqTm ≠ rkJ := by decide
@[simp] theorem eq_rkJ_ne_eqTm : rkJ ≠ eqTm := by decide
@[simp] theorem eq_eqTm_ne_rkT : eqTm ≠ rkT := by decide
@[simp] theorem eq_rkT_ne_eqTm : rkT ≠ eqTm := by decide
@[simp] theorem eq_eqTm_ne_rkM : eqTm ≠ rkM := by decide
@[simp] theorem eq_rkM_ne_eqTm : rkM ≠ eqTm := by decide
@[simp] theorem eq_eqTm_ne_reF : eqTm ≠ reF := by decide
@[simp] theorem eq_reF_ne_eqTm : reF ≠ eqTm := by decide
@[simp] theorem eq_eqTm_ne_reO : eqTm ≠ reO := by decide
@[simp] theorem eq_reO_ne_eqTm : reO ≠ eqTm := by decide
@[simp] theorem eq_eqHh_ne_eq1 : eqHh ≠ eq1 := by decide
@[simp] theorem eq_eqHh_ne_eqTm : eqHh ≠ eqTm := by decide
@[simp] theorem eq_eqHh_ne_eqTp : eqHh ≠ eqTp := by decide
@[simp] theorem eq_eqHh_ne_eqUs : eqHh ≠ eqUs := by decide
@[simp] theorem eq_eqHh_ne_eqTa : eqHh ≠ eqTa := by decide
@[simp] theorem eq_eqHh_ne_eqTl : eqHh ≠ eqTl := by decide
@[simp] theorem eq_eqHh_ne_eqNp : eqHh ≠ eqNp := by decide
@[simp] theorem eq_eqHh_ne_eqLp : eqHh ≠ eqLp := by decide
@[simp] theorem eq_eqHh_ne_eqLn : eqHh ≠ eqLn := by decide
@[simp] theorem eq_eqHh_ne_eqFz : eqHh ≠ eqFz := by decide
@[simp] theorem eq_eqHh_ne_eqNf : eqHh ≠ eqNf := by decide
@[simp] theorem eq_eqHh_ne_eqFa : eqHh ≠ eqFa := by decide
@[simp] theorem eq_eqHh_ne_eqTc : eqHh ≠ eqTc := by decide
@[simp] theorem eq_eqHh_ne_eqHd : eqHh ≠ eqHd := by decide
@[simp] theorem eq_eqHh_ne_eqFl : eqHh ≠ eqFl := by decide
@[simp] theorem eq_eqHh_ne_eqFab : eqHh ≠ eqFab := by decide
@[simp] theorem eq_eqHh_ne_eqFs : eqHh ≠ eqFs := by decide
@[simp] theorem eq_eqHh_ne_lFl : eqHh ≠ lFl := by decide
@[simp] theorem eq_lFl_ne_eqHh : lFl ≠ eqHh := by decide
@[simp] theorem eq_eqHh_ne_lDh : eqHh ≠ lDh := by decide
@[simp] theorem eq_lDh_ne_eqHh : lDh ≠ eqHh := by decide
@[simp] theorem eq_eqHh_ne_lDt : eqHh ≠ lDt := by decide
@[simp] theorem eq_lDt_ne_eqHh : lDt ≠ eqHh := by decide
@[simp] theorem eq_eqHh_ne_lDg : eqHh ≠ lDg := by decide
@[simp] theorem eq_lDg_ne_eqHh : lDg ≠ eqHh := by decide
@[simp] theorem eq_eqHh_ne_lDi : eqHh ≠ lDi := by decide
@[simp] theorem eq_lDi_ne_eqHh : lDi ≠ eqHh := by decide
@[simp] theorem eq_eqHh_ne_lRp : eqHh ≠ lRp := by decide
@[simp] theorem eq_lRp_ne_eqHh : lRp ≠ eqHh := by decide
@[simp] theorem eq_eqHh_ne_lRn : eqHh ≠ lRn := by decide
@[simp] theorem eq_lRn_ne_eqHh : lRn ≠ eqHh := by decide
@[simp] theorem eq_eqHh_ne_lFle : eqHh ≠ lFle := by decide
@[simp] theorem eq_lFle_ne_eqHh : lFle ≠ eqHh := by decide
@[simp] theorem eq_eqHh_ne_lFls : eqHh ≠ lFls := by decide
@[simp] theorem eq_lFls_ne_eqHh : lFls ≠ eqHh := by decide
@[simp] theorem eq_eqHh_ne_lDir : eqHh ≠ lDir := by decide
@[simp] theorem eq_lDir_ne_eqHh : lDir ≠ eqHh := by decide
@[simp] theorem eq_eqHh_ne_lKb : eqHh ≠ lKb := by decide
@[simp] theorem eq_lKb_ne_eqHh : lKb ≠ eqHh := by decide
@[simp] theorem eq_eqHh_ne_kFu : eqHh ≠ kFu := by decide
@[simp] theorem eq_kFu_ne_eqHh : kFu ≠ eqHh := by decide
@[simp] theorem eq_eqHh_ne_kD : eqHh ≠ kD := by decide
@[simp] theorem eq_kD_ne_eqHh : kD ≠ eqHh := by decide
@[simp] theorem eq_eqHh_ne_rkR : eqHh ≠ rkR := by decide
@[simp] theorem eq_rkR_ne_eqHh : rkR ≠ eqHh := by decide
@[simp] theorem eq_eqHh_ne_rkJ : eqHh ≠ rkJ := by decide
@[simp] theorem eq_rkJ_ne_eqHh : rkJ ≠ eqHh := by decide
@[simp] theorem eq_eqHh_ne_rkT : eqHh ≠ rkT := by decide
@[simp] theorem eq_rkT_ne_eqHh : rkT ≠ eqHh := by decide
@[simp] theorem eq_eqHh_ne_rkM : eqHh ≠ rkM := by decide
@[simp] theorem eq_rkM_ne_eqHh : rkM ≠ eqHh := by decide
@[simp] theorem eq_eqHh_ne_reF : eqHh ≠ reF := by decide
@[simp] theorem eq_reF_ne_eqHh : reF ≠ eqHh := by decide
@[simp] theorem eq_eqHh_ne_reO : eqHh ≠ reO := by decide
@[simp] theorem eq_reO_ne_eqHh : reO ≠ eqHh := by decide
@[simp] theorem eq_eqTp_ne_eq1 : eqTp ≠ eq1 := by decide
@[simp] theorem eq_eqTp_ne_eqTm : eqTp ≠ eqTm := by decide
@[simp] theorem eq_eqTp_ne_eqHh : eqTp ≠ eqHh := by decide
@[simp] theorem eq_eqTp_ne_eqUs : eqTp ≠ eqUs := by decide
@[simp] theorem eq_eqTp_ne_eqTa : eqTp ≠ eqTa := by decide
@[simp] theorem eq_eqTp_ne_eqTl : eqTp ≠ eqTl := by decide
@[simp] theorem eq_eqTp_ne_eqNp : eqTp ≠ eqNp := by decide
@[simp] theorem eq_eqTp_ne_eqLp : eqTp ≠ eqLp := by decide
@[simp] theorem eq_eqTp_ne_eqLn : eqTp ≠ eqLn := by decide
@[simp] theorem eq_eqTp_ne_eqFz : eqTp ≠ eqFz := by decide
@[simp] theorem eq_eqTp_ne_eqNf : eqTp ≠ eqNf := by decide
@[simp] theorem eq_eqTp_ne_eqFa : eqTp ≠ eqFa := by decide
@[simp] theorem eq_eqTp_ne_eqTc : eqTp ≠ eqTc := by decide
@[simp] theorem eq_eqTp_ne_eqHd : eqTp ≠ eqHd := by decide
@[simp] theorem eq_eqTp_ne_eqFl : eqTp ≠ eqFl := by decide
@[simp] theorem eq_eqTp_ne_eqFab : eqTp ≠ eqFab := by decide
@[simp] theorem eq_eqTp_ne_eqFs : eqTp ≠ eqFs := by decide
@[simp] theorem eq_eqTp_ne_lFl : eqTp ≠ lFl := by decide
@[simp] theorem eq_lFl_ne_eqTp : lFl ≠ eqTp := by decide
@[simp] theorem eq_eqTp_ne_lDh : eqTp ≠ lDh := by decide
@[simp] theorem eq_lDh_ne_eqTp : lDh ≠ eqTp := by decide
@[simp] theorem eq_eqTp_ne_lDt : eqTp ≠ lDt := by decide
@[simp] theorem eq_lDt_ne_eqTp : lDt ≠ eqTp := by decide
@[simp] theorem eq_eqTp_ne_lDg : eqTp ≠ lDg := by decide
@[simp] theorem eq_lDg_ne_eqTp : lDg ≠ eqTp := by decide
@[simp] theorem eq_eqTp_ne_lDi : eqTp ≠ lDi := by decide
@[simp] theorem eq_lDi_ne_eqTp : lDi ≠ eqTp := by decide
@[simp] theorem eq_eqTp_ne_lRp : eqTp ≠ lRp := by decide
@[simp] theorem eq_lRp_ne_eqTp : lRp ≠ eqTp := by decide
@[simp] theorem eq_eqTp_ne_lRn : eqTp ≠ lRn := by decide
@[simp] theorem eq_lRn_ne_eqTp : lRn ≠ eqTp := by decide
@[simp] theorem eq_eqTp_ne_lFle : eqTp ≠ lFle := by decide
@[simp] theorem eq_lFle_ne_eqTp : lFle ≠ eqTp := by decide
@[simp] theorem eq_eqTp_ne_lFls : eqTp ≠ lFls := by decide
@[simp] theorem eq_lFls_ne_eqTp : lFls ≠ eqTp := by decide
@[simp] theorem eq_eqTp_ne_lDir : eqTp ≠ lDir := by decide
@[simp] theorem eq_lDir_ne_eqTp : lDir ≠ eqTp := by decide
@[simp] theorem eq_eqTp_ne_lKb : eqTp ≠ lKb := by decide
@[simp] theorem eq_lKb_ne_eqTp : lKb ≠ eqTp := by decide
@[simp] theorem eq_eqTp_ne_kFu : eqTp ≠ kFu := by decide
@[simp] theorem eq_kFu_ne_eqTp : kFu ≠ eqTp := by decide
@[simp] theorem eq_eqTp_ne_kD : eqTp ≠ kD := by decide
@[simp] theorem eq_kD_ne_eqTp : kD ≠ eqTp := by decide
@[simp] theorem eq_eqTp_ne_rkR : eqTp ≠ rkR := by decide
@[simp] theorem eq_rkR_ne_eqTp : rkR ≠ eqTp := by decide
@[simp] theorem eq_eqTp_ne_rkJ : eqTp ≠ rkJ := by decide
@[simp] theorem eq_rkJ_ne_eqTp : rkJ ≠ eqTp := by decide
@[simp] theorem eq_eqTp_ne_rkT : eqTp ≠ rkT := by decide
@[simp] theorem eq_rkT_ne_eqTp : rkT ≠ eqTp := by decide
@[simp] theorem eq_eqTp_ne_rkM : eqTp ≠ rkM := by decide
@[simp] theorem eq_rkM_ne_eqTp : rkM ≠ eqTp := by decide
@[simp] theorem eq_eqTp_ne_reF : eqTp ≠ reF := by decide
@[simp] theorem eq_reF_ne_eqTp : reF ≠ eqTp := by decide
@[simp] theorem eq_eqTp_ne_reO : eqTp ≠ reO := by decide
@[simp] theorem eq_reO_ne_eqTp : reO ≠ eqTp := by decide
@[simp] theorem eq_eqUs_ne_eq1 : eqUs ≠ eq1 := by decide
@[simp] theorem eq_eqUs_ne_eqTm : eqUs ≠ eqTm := by decide
@[simp] theorem eq_eqUs_ne_eqHh : eqUs ≠ eqHh := by decide
@[simp] theorem eq_eqUs_ne_eqTp : eqUs ≠ eqTp := by decide
@[simp] theorem eq_eqUs_ne_eqTa : eqUs ≠ eqTa := by decide
@[simp] theorem eq_eqUs_ne_eqTl : eqUs ≠ eqTl := by decide
@[simp] theorem eq_eqUs_ne_eqNp : eqUs ≠ eqNp := by decide
@[simp] theorem eq_eqUs_ne_eqLp : eqUs ≠ eqLp := by decide
@[simp] theorem eq_eqUs_ne_eqLn : eqUs ≠ eqLn := by decide
@[simp] theorem eq_eqUs_ne_eqFz : eqUs ≠ eqFz := by decide
@[simp] theorem eq_eqUs_ne_eqNf : eqUs ≠ eqNf := by decide
@[simp] theorem eq_eqUs_ne_eqFa : eqUs ≠ eqFa := by decide
@[simp] theorem eq_eqUs_ne_eqTc : eqUs ≠ eqTc := by decide
@[simp] theorem eq_eqUs_ne_eqHd : eqUs ≠ eqHd := by decide
@[simp] theorem eq_eqUs_ne_eqFl : eqUs ≠ eqFl := by decide
@[simp] theorem eq_eqUs_ne_eqFab : eqUs ≠ eqFab := by decide
@[simp] theorem eq_eqUs_ne_eqFs : eqUs ≠ eqFs := by decide
@[simp] theorem eq_eqUs_ne_lFl : eqUs ≠ lFl := by decide
@[simp] theorem eq_lFl_ne_eqUs : lFl ≠ eqUs := by decide
@[simp] theorem eq_eqUs_ne_lDh : eqUs ≠ lDh := by decide
@[simp] theorem eq_lDh_ne_eqUs : lDh ≠ eqUs := by decide
@[simp] theorem eq_eqUs_ne_lDt : eqUs ≠ lDt := by decide
@[simp] theorem eq_lDt_ne_eqUs : lDt ≠ eqUs := by decide
@[simp] theorem eq_eqUs_ne_lDg : eqUs ≠ lDg := by decide
@[simp] theorem eq_lDg_ne_eqUs : lDg ≠ eqUs := by decide
@[simp] theorem eq_eqUs_ne_lDi : eqUs ≠ lDi := by decide
@[simp] theorem eq_lDi_ne_eqUs : lDi ≠ eqUs := by decide
@[simp] theorem eq_eqUs_ne_lRp : eqUs ≠ lRp := by decide
@[simp] theorem eq_lRp_ne_eqUs : lRp ≠ eqUs := by decide
@[simp] theorem eq_eqUs_ne_lRn : eqUs ≠ lRn := by decide
@[simp] theorem eq_lRn_ne_eqUs : lRn ≠ eqUs := by decide
@[simp] theorem eq_eqUs_ne_lFle : eqUs ≠ lFle := by decide
@[simp] theorem eq_lFle_ne_eqUs : lFle ≠ eqUs := by decide
@[simp] theorem eq_eqUs_ne_lFls : eqUs ≠ lFls := by decide
@[simp] theorem eq_lFls_ne_eqUs : lFls ≠ eqUs := by decide
@[simp] theorem eq_eqUs_ne_lDir : eqUs ≠ lDir := by decide
@[simp] theorem eq_lDir_ne_eqUs : lDir ≠ eqUs := by decide
@[simp] theorem eq_eqUs_ne_lKb : eqUs ≠ lKb := by decide
@[simp] theorem eq_lKb_ne_eqUs : lKb ≠ eqUs := by decide
@[simp] theorem eq_eqUs_ne_kFu : eqUs ≠ kFu := by decide
@[simp] theorem eq_kFu_ne_eqUs : kFu ≠ eqUs := by decide
@[simp] theorem eq_eqUs_ne_kD : eqUs ≠ kD := by decide
@[simp] theorem eq_kD_ne_eqUs : kD ≠ eqUs := by decide
@[simp] theorem eq_eqUs_ne_rkR : eqUs ≠ rkR := by decide
@[simp] theorem eq_rkR_ne_eqUs : rkR ≠ eqUs := by decide
@[simp] theorem eq_eqUs_ne_rkJ : eqUs ≠ rkJ := by decide
@[simp] theorem eq_rkJ_ne_eqUs : rkJ ≠ eqUs := by decide
@[simp] theorem eq_eqUs_ne_rkT : eqUs ≠ rkT := by decide
@[simp] theorem eq_rkT_ne_eqUs : rkT ≠ eqUs := by decide
@[simp] theorem eq_eqUs_ne_rkM : eqUs ≠ rkM := by decide
@[simp] theorem eq_rkM_ne_eqUs : rkM ≠ eqUs := by decide
@[simp] theorem eq_eqUs_ne_reF : eqUs ≠ reF := by decide
@[simp] theorem eq_reF_ne_eqUs : reF ≠ eqUs := by decide
@[simp] theorem eq_eqUs_ne_reO : eqUs ≠ reO := by decide
@[simp] theorem eq_reO_ne_eqUs : reO ≠ eqUs := by decide
@[simp] theorem eq_eqTa_ne_eq1 : eqTa ≠ eq1 := by decide
@[simp] theorem eq_eqTa_ne_eqTm : eqTa ≠ eqTm := by decide
@[simp] theorem eq_eqTa_ne_eqHh : eqTa ≠ eqHh := by decide
@[simp] theorem eq_eqTa_ne_eqTp : eqTa ≠ eqTp := by decide
@[simp] theorem eq_eqTa_ne_eqUs : eqTa ≠ eqUs := by decide
@[simp] theorem eq_eqTa_ne_eqTl : eqTa ≠ eqTl := by decide
@[simp] theorem eq_eqTa_ne_eqNp : eqTa ≠ eqNp := by decide
@[simp] theorem eq_eqTa_ne_eqLp : eqTa ≠ eqLp := by decide
@[simp] theorem eq_eqTa_ne_eqLn : eqTa ≠ eqLn := by decide
@[simp] theorem eq_eqTa_ne_eqFz : eqTa ≠ eqFz := by decide
@[simp] theorem eq_eqTa_ne_eqNf : eqTa ≠ eqNf := by decide
@[simp] theorem eq_eqTa_ne_eqFa : eqTa ≠ eqFa := by decide
@[simp] theorem eq_eqTa_ne_eqTc : eqTa ≠ eqTc := by decide
@[simp] theorem eq_eqTa_ne_eqHd : eqTa ≠ eqHd := by decide
@[simp] theorem eq_eqTa_ne_eqFl : eqTa ≠ eqFl := by decide
@[simp] theorem eq_eqTa_ne_eqFab : eqTa ≠ eqFab := by decide
@[simp] theorem eq_eqTa_ne_eqFs : eqTa ≠ eqFs := by decide
@[simp] theorem eq_eqTa_ne_lFl : eqTa ≠ lFl := by decide
@[simp] theorem eq_lFl_ne_eqTa : lFl ≠ eqTa := by decide
@[simp] theorem eq_eqTa_ne_lDh : eqTa ≠ lDh := by decide
@[simp] theorem eq_lDh_ne_eqTa : lDh ≠ eqTa := by decide
@[simp] theorem eq_eqTa_ne_lDt : eqTa ≠ lDt := by decide
@[simp] theorem eq_lDt_ne_eqTa : lDt ≠ eqTa := by decide
@[simp] theorem eq_eqTa_ne_lDg : eqTa ≠ lDg := by decide
@[simp] theorem eq_lDg_ne_eqTa : lDg ≠ eqTa := by decide
@[simp] theorem eq_eqTa_ne_lDi : eqTa ≠ lDi := by decide
@[simp] theorem eq_lDi_ne_eqTa : lDi ≠ eqTa := by decide
@[simp] theorem eq_eqTa_ne_lRp : eqTa ≠ lRp := by decide
@[simp] theorem eq_lRp_ne_eqTa : lRp ≠ eqTa := by decide
@[simp] theorem eq_eqTa_ne_lRn : eqTa ≠ lRn := by decide
@[simp] theorem eq_lRn_ne_eqTa : lRn ≠ eqTa := by decide
@[simp] theorem eq_eqTa_ne_lFle : eqTa ≠ lFle := by decide
@[simp] theorem eq_lFle_ne_eqTa : lFle ≠ eqTa := by decide
@[simp] theorem eq_eqTa_ne_lFls : eqTa ≠ lFls := by decide
@[simp] theorem eq_lFls_ne_eqTa : lFls ≠ eqTa := by decide
@[simp] theorem eq_eqTa_ne_lDir : eqTa ≠ lDir := by decide
@[simp] theorem eq_lDir_ne_eqTa : lDir ≠ eqTa := by decide
@[simp] theorem eq_eqTa_ne_lKb : eqTa ≠ lKb := by decide
@[simp] theorem eq_lKb_ne_eqTa : lKb ≠ eqTa := by decide
@[simp] theorem eq_eqTa_ne_kFu : eqTa ≠ kFu := by decide
@[simp] theorem eq_kFu_ne_eqTa : kFu ≠ eqTa := by decide
@[simp] theorem eq_eqTa_ne_kD : eqTa ≠ kD := by decide
@[simp] theorem eq_kD_ne_eqTa : kD ≠ eqTa := by decide
@[simp] theorem eq_eqTa_ne_rkR : eqTa ≠ rkR := by decide
@[simp] theorem eq_rkR_ne_eqTa : rkR ≠ eqTa := by decide
@[simp] theorem eq_eqTa_ne_rkJ : eqTa ≠ rkJ := by decide
@[simp] theorem eq_rkJ_ne_eqTa : rkJ ≠ eqTa := by decide
@[simp] theorem eq_eqTa_ne_rkT : eqTa ≠ rkT := by decide
@[simp] theorem eq_rkT_ne_eqTa : rkT ≠ eqTa := by decide
@[simp] theorem eq_eqTa_ne_rkM : eqTa ≠ rkM := by decide
@[simp] theorem eq_rkM_ne_eqTa : rkM ≠ eqTa := by decide
@[simp] theorem eq_eqTa_ne_reF : eqTa ≠ reF := by decide
@[simp] theorem eq_reF_ne_eqTa : reF ≠ eqTa := by decide
@[simp] theorem eq_eqTa_ne_reO : eqTa ≠ reO := by decide
@[simp] theorem eq_reO_ne_eqTa : reO ≠ eqTa := by decide
@[simp] theorem eq_eqTl_ne_eq1 : eqTl ≠ eq1 := by decide
@[simp] theorem eq_eqTl_ne_eqTm : eqTl ≠ eqTm := by decide
@[simp] theorem eq_eqTl_ne_eqHh : eqTl ≠ eqHh := by decide
@[simp] theorem eq_eqTl_ne_eqTp : eqTl ≠ eqTp := by decide
@[simp] theorem eq_eqTl_ne_eqUs : eqTl ≠ eqUs := by decide
@[simp] theorem eq_eqTl_ne_eqTa : eqTl ≠ eqTa := by decide
@[simp] theorem eq_eqTl_ne_eqNp : eqTl ≠ eqNp := by decide
@[simp] theorem eq_eqTl_ne_eqLp : eqTl ≠ eqLp := by decide
@[simp] theorem eq_eqTl_ne_eqLn : eqTl ≠ eqLn := by decide
@[simp] theorem eq_eqTl_ne_eqFz : eqTl ≠ eqFz := by decide
@[simp] theorem eq_eqTl_ne_eqNf : eqTl ≠ eqNf := by decide
@[simp] theorem eq_eqTl_ne_eqFa : eqTl ≠ eqFa := by decide
@[simp] theorem eq_eqTl_ne_eqTc : eqTl ≠ eqTc := by decide
@[simp] theorem eq_eqTl_ne_eqHd : eqTl ≠ eqHd := by decide
@[simp] theorem eq_eqTl_ne_eqFl : eqTl ≠ eqFl := by decide
@[simp] theorem eq_eqTl_ne_eqFab : eqTl ≠ eqFab := by decide
@[simp] theorem eq_eqTl_ne_eqFs : eqTl ≠ eqFs := by decide
@[simp] theorem eq_eqTl_ne_lFl : eqTl ≠ lFl := by decide
@[simp] theorem eq_lFl_ne_eqTl : lFl ≠ eqTl := by decide
@[simp] theorem eq_eqTl_ne_lDh : eqTl ≠ lDh := by decide
@[simp] theorem eq_lDh_ne_eqTl : lDh ≠ eqTl := by decide
@[simp] theorem eq_eqTl_ne_lDt : eqTl ≠ lDt := by decide
@[simp] theorem eq_lDt_ne_eqTl : lDt ≠ eqTl := by decide
@[simp] theorem eq_eqTl_ne_lDg : eqTl ≠ lDg := by decide
@[simp] theorem eq_lDg_ne_eqTl : lDg ≠ eqTl := by decide
@[simp] theorem eq_eqTl_ne_lDi : eqTl ≠ lDi := by decide
@[simp] theorem eq_lDi_ne_eqTl : lDi ≠ eqTl := by decide
@[simp] theorem eq_eqTl_ne_lRp : eqTl ≠ lRp := by decide
@[simp] theorem eq_lRp_ne_eqTl : lRp ≠ eqTl := by decide
@[simp] theorem eq_eqTl_ne_lRn : eqTl ≠ lRn := by decide
@[simp] theorem eq_lRn_ne_eqTl : lRn ≠ eqTl := by decide
@[simp] theorem eq_eqTl_ne_lFle : eqTl ≠ lFle := by decide
@[simp] theorem eq_lFle_ne_eqTl : lFle ≠ eqTl := by decide
@[simp] theorem eq_eqTl_ne_lFls : eqTl ≠ lFls := by decide
@[simp] theorem eq_lFls_ne_eqTl : lFls ≠ eqTl := by decide
@[simp] theorem eq_eqTl_ne_lDir : eqTl ≠ lDir := by decide
@[simp] theorem eq_lDir_ne_eqTl : lDir ≠ eqTl := by decide
@[simp] theorem eq_eqTl_ne_lKb : eqTl ≠ lKb := by decide
@[simp] theorem eq_lKb_ne_eqTl : lKb ≠ eqTl := by decide
@[simp] theorem eq_eqTl_ne_kFu : eqTl ≠ kFu := by decide
@[simp] theorem eq_kFu_ne_eqTl : kFu ≠ eqTl := by decide
@[simp] theorem eq_eqTl_ne_kD : eqTl ≠ kD := by decide
@[simp] theorem eq_kD_ne_eqTl : kD ≠ eqTl := by decide
@[simp] theorem eq_eqTl_ne_rkR : eqTl ≠ rkR := by decide
@[simp] theorem eq_rkR_ne_eqTl : rkR ≠ eqTl := by decide
@[simp] theorem eq_eqTl_ne_rkJ : eqTl ≠ rkJ := by decide
@[simp] theorem eq_rkJ_ne_eqTl : rkJ ≠ eqTl := by decide
@[simp] theorem eq_eqTl_ne_rkT : eqTl ≠ rkT := by decide
@[simp] theorem eq_rkT_ne_eqTl : rkT ≠ eqTl := by decide
@[simp] theorem eq_eqTl_ne_rkM : eqTl ≠ rkM := by decide
@[simp] theorem eq_rkM_ne_eqTl : rkM ≠ eqTl := by decide
@[simp] theorem eq_eqTl_ne_reF : eqTl ≠ reF := by decide
@[simp] theorem eq_reF_ne_eqTl : reF ≠ eqTl := by decide
@[simp] theorem eq_eqTl_ne_reO : eqTl ≠ reO := by decide
@[simp] theorem eq_reO_ne_eqTl : reO ≠ eqTl := by decide
@[simp] theorem eq_eqNp_ne_eq1 : eqNp ≠ eq1 := by decide
@[simp] theorem eq_eqNp_ne_eqTm : eqNp ≠ eqTm := by decide
@[simp] theorem eq_eqNp_ne_eqHh : eqNp ≠ eqHh := by decide
@[simp] theorem eq_eqNp_ne_eqTp : eqNp ≠ eqTp := by decide
@[simp] theorem eq_eqNp_ne_eqUs : eqNp ≠ eqUs := by decide
@[simp] theorem eq_eqNp_ne_eqTa : eqNp ≠ eqTa := by decide
@[simp] theorem eq_eqNp_ne_eqTl : eqNp ≠ eqTl := by decide
@[simp] theorem eq_eqNp_ne_eqLp : eqNp ≠ eqLp := by decide
@[simp] theorem eq_eqNp_ne_eqLn : eqNp ≠ eqLn := by decide
@[simp] theorem eq_eqNp_ne_eqFz : eqNp ≠ eqFz := by decide
@[simp] theorem eq_eqNp_ne_eqNf : eqNp ≠ eqNf := by decide
@[simp] theorem eq_eqNp_ne_eqFa : eqNp ≠ eqFa := by decide
@[simp] theorem eq_eqNp_ne_eqTc : eqNp ≠ eqTc := by decide
@[simp] theorem eq_eqNp_ne_eqHd : eqNp ≠ eqHd := by decide
@[simp] theorem eq_eqNp_ne_eqFl : eqNp ≠ eqFl := by decide
@[simp] theorem eq_eqNp_ne_eqFab : eqNp ≠ eqFab := by decide
@[simp] theorem eq_eqNp_ne_eqFs : eqNp ≠ eqFs := by decide
@[simp] theorem eq_eqNp_ne_lFl : eqNp ≠ lFl := by decide
@[simp] theorem eq_lFl_ne_eqNp : lFl ≠ eqNp := by decide
@[simp] theorem eq_eqNp_ne_lDh : eqNp ≠ lDh := by decide
@[simp] theorem eq_lDh_ne_eqNp : lDh ≠ eqNp := by decide
@[simp] theorem eq_eqNp_ne_lDt : eqNp ≠ lDt := by decide
@[simp] theorem eq_lDt_ne_eqNp : lDt ≠ eqNp := by decide
@[simp] theorem eq_eqNp_ne_lDg : eqNp ≠ lDg := by decide
@[simp] theorem eq_lDg_ne_eqNp : lDg ≠ eqNp := by decide
@[simp] theorem eq_eqNp_ne_lDi : eqNp ≠ lDi := by decide
@[simp] theorem eq_lDi_ne_eqNp : lDi ≠ eqNp := by decide
@[simp] theorem eq_eqNp_ne_lRp : eqNp ≠ lRp := by decide
@[simp] theorem eq_lRp_ne_eqNp : lRp ≠ eqNp := by decide
@[simp] theorem eq_eqNp_ne_lRn : eqNp ≠ lRn := by decide
@[simp] theorem eq_lRn_ne_eqNp : lRn ≠ eqNp := by decide
@[simp] theorem eq_eqNp_ne_lFle : eqNp ≠ lFle := by decide
@[simp] theorem eq_lFle_ne_eqNp : lFle ≠ eqNp := by decide
@[simp] theorem eq_eqNp_ne_lFls : eqNp ≠ lFls := by decide
@[simp] theorem eq_lFls_ne_eqNp : lFls ≠ eqNp := by decide
@[simp] theorem eq_eqNp_ne_lDir : eqNp ≠ lDir := by decide
@[simp] theorem eq_lDir_ne_eqNp : lDir ≠ eqNp := by decide
@[simp] theorem eq_eqNp_ne_lKb : eqNp ≠ lKb := by decide
@[simp] theorem eq_lKb_ne_eqNp : lKb ≠ eqNp := by decide
@[simp] theorem eq_eqNp_ne_kFu : eqNp ≠ kFu := by decide
@[simp] theorem eq_kFu_ne_eqNp : kFu ≠ eqNp := by decide
@[simp] theorem eq_eqNp_ne_kD : eqNp ≠ kD := by decide
@[simp] theorem eq_kD_ne_eqNp : kD ≠ eqNp := by decide
@[simp] theorem eq_eqNp_ne_rkR : eqNp ≠ rkR := by decide
@[simp] theorem eq_rkR_ne_eqNp : rkR ≠ eqNp := by decide
@[simp] theorem eq_eqNp_ne_rkJ : eqNp ≠ rkJ := by decide
@[simp] theorem eq_rkJ_ne_eqNp : rkJ ≠ eqNp := by decide
@[simp] theorem eq_eqNp_ne_rkT : eqNp ≠ rkT := by decide
@[simp] theorem eq_rkT_ne_eqNp : rkT ≠ eqNp := by decide
@[simp] theorem eq_eqNp_ne_rkM : eqNp ≠ rkM := by decide
@[simp] theorem eq_rkM_ne_eqNp : rkM ≠ eqNp := by decide
@[simp] theorem eq_eqNp_ne_reF : eqNp ≠ reF := by decide
@[simp] theorem eq_reF_ne_eqNp : reF ≠ eqNp := by decide
@[simp] theorem eq_eqNp_ne_reO : eqNp ≠ reO := by decide
@[simp] theorem eq_reO_ne_eqNp : reO ≠ eqNp := by decide
@[simp] theorem eq_eqLp_ne_eq1 : eqLp ≠ eq1 := by decide
@[simp] theorem eq_eqLp_ne_eqTm : eqLp ≠ eqTm := by decide
@[simp] theorem eq_eqLp_ne_eqHh : eqLp ≠ eqHh := by decide
@[simp] theorem eq_eqLp_ne_eqTp : eqLp ≠ eqTp := by decide
@[simp] theorem eq_eqLp_ne_eqUs : eqLp ≠ eqUs := by decide
@[simp] theorem eq_eqLp_ne_eqTa : eqLp ≠ eqTa := by decide
@[simp] theorem eq_eqLp_ne_eqTl : eqLp ≠ eqTl := by decide
@[simp] theorem eq_eqLp_ne_eqNp : eqLp ≠ eqNp := by decide
@[simp] theorem eq_eqLp_ne_eqLn : eqLp ≠ eqLn := by decide
@[simp] theorem eq_eqLp_ne_eqFz : eqLp ≠ eqFz := by decide
@[simp] theorem eq_eqLp_ne_eqNf : eqLp ≠ eqNf := by decide
@[simp] theorem eq_eqLp_ne_eqFa : eqLp ≠ eqFa := by decide
@[simp] theorem eq_eqLp_ne_eqTc : eqLp ≠ eqTc := by decide
@[simp] theorem eq_eqLp_ne_eqHd : eqLp ≠ eqHd := by decide
@[simp] theorem eq_eqLp_ne_eqFl : eqLp ≠ eqFl := by decide
@[simp] theorem eq_eqLp_ne_eqFab : eqLp ≠ eqFab := by decide
@[simp] theorem eq_eqLp_ne_eqFs : eqLp ≠ eqFs := by decide
@[simp] theorem eq_eqLp_ne_lFl : eqLp ≠ lFl := by decide
@[simp] theorem eq_lFl_ne_eqLp : lFl ≠ eqLp := by decide
@[simp] theorem eq_eqLp_ne_lDh : eqLp ≠ lDh := by decide
@[simp] theorem eq_lDh_ne_eqLp : lDh ≠ eqLp := by decide
@[simp] theorem eq_eqLp_ne_lDt : eqLp ≠ lDt := by decide
@[simp] theorem eq_lDt_ne_eqLp : lDt ≠ eqLp := by decide
@[simp] theorem eq_eqLp_ne_lDg : eqLp ≠ lDg := by decide
@[simp] theorem eq_lDg_ne_eqLp : lDg ≠ eqLp := by decide
@[simp] theorem eq_eqLp_ne_lDi : eqLp ≠ lDi := by decide
@[simp] theorem eq_lDi_ne_eqLp : lDi ≠ eqLp := by decide
@[simp] theorem eq_eqLp_ne_lRp : eqLp ≠ lRp := by decide
@[simp] theorem eq_lRp_ne_eqLp : lRp ≠ eqLp := by decide
@[simp] theorem eq_eqLp_ne_lRn : eqLp ≠ lRn := by decide
@[simp] theorem eq_lRn_ne_eqLp : lRn ≠ eqLp := by decide
@[simp] theorem eq_eqLp_ne_lFle : eqLp ≠ lFle := by decide
@[simp] theorem eq_lFle_ne_eqLp : lFle ≠ eqLp := by decide
@[simp] theorem eq_eqLp_ne_lFls : eqLp ≠ lFls := by decide
@[simp] theorem eq_lFls_ne_eqLp : lFls ≠ eqLp := by decide
@[simp] theorem eq_eqLp_ne_lDir : eqLp ≠ lDir := by decide
@[simp] theorem eq_lDir_ne_eqLp : lDir ≠ eqLp := by decide
@[simp] theorem eq_eqLp_ne_lKb : eqLp ≠ lKb := by decide
@[simp] theorem eq_lKb_ne_eqLp : lKb ≠ eqLp := by decide
@[simp] theorem eq_eqLp_ne_kFu : eqLp ≠ kFu := by decide
@[simp] theorem eq_kFu_ne_eqLp : kFu ≠ eqLp := by decide
@[simp] theorem eq_eqLp_ne_kD : eqLp ≠ kD := by decide
@[simp] theorem eq_kD_ne_eqLp : kD ≠ eqLp := by decide
@[simp] theorem eq_eqLp_ne_rkR : eqLp ≠ rkR := by decide
@[simp] theorem eq_rkR_ne_eqLp : rkR ≠ eqLp := by decide
@[simp] theorem eq_eqLp_ne_rkJ : eqLp ≠ rkJ := by decide
@[simp] theorem eq_rkJ_ne_eqLp : rkJ ≠ eqLp := by decide
@[simp] theorem eq_eqLp_ne_rkT : eqLp ≠ rkT := by decide
@[simp] theorem eq_rkT_ne_eqLp : rkT ≠ eqLp := by decide
@[simp] theorem eq_eqLp_ne_rkM : eqLp ≠ rkM := by decide
@[simp] theorem eq_rkM_ne_eqLp : rkM ≠ eqLp := by decide
@[simp] theorem eq_eqLp_ne_reF : eqLp ≠ reF := by decide
@[simp] theorem eq_reF_ne_eqLp : reF ≠ eqLp := by decide
@[simp] theorem eq_eqLp_ne_reO : eqLp ≠ reO := by decide
@[simp] theorem eq_reO_ne_eqLp : reO ≠ eqLp := by decide
@[simp] theorem eq_eqLn_ne_eq1 : eqLn ≠ eq1 := by decide
@[simp] theorem eq_eqLn_ne_eqTm : eqLn ≠ eqTm := by decide
@[simp] theorem eq_eqLn_ne_eqHh : eqLn ≠ eqHh := by decide
@[simp] theorem eq_eqLn_ne_eqTp : eqLn ≠ eqTp := by decide
@[simp] theorem eq_eqLn_ne_eqUs : eqLn ≠ eqUs := by decide
@[simp] theorem eq_eqLn_ne_eqTa : eqLn ≠ eqTa := by decide
@[simp] theorem eq_eqLn_ne_eqTl : eqLn ≠ eqTl := by decide
@[simp] theorem eq_eqLn_ne_eqNp : eqLn ≠ eqNp := by decide
@[simp] theorem eq_eqLn_ne_eqLp : eqLn ≠ eqLp := by decide
@[simp] theorem eq_eqLn_ne_eqFz : eqLn ≠ eqFz := by decide
@[simp] theorem eq_eqLn_ne_eqNf : eqLn ≠ eqNf := by decide
@[simp] theorem eq_eqLn_ne_eqFa : eqLn ≠ eqFa := by decide
@[simp] theorem eq_eqLn_ne_eqTc : eqLn ≠ eqTc := by decide
@[simp] theorem eq_eqLn_ne_eqHd : eqLn ≠ eqHd := by decide
@[simp] theorem eq_eqLn_ne_eqFl : eqLn ≠ eqFl := by decide
@[simp] theorem eq_eqLn_ne_eqFab : eqLn ≠ eqFab := by decide
@[simp] theorem eq_eqLn_ne_eqFs : eqLn ≠ eqFs := by decide
@[simp] theorem eq_eqLn_ne_lFl : eqLn ≠ lFl := by decide
@[simp] theorem eq_lFl_ne_eqLn : lFl ≠ eqLn := by decide
@[simp] theorem eq_eqLn_ne_lDh : eqLn ≠ lDh := by decide
@[simp] theorem eq_lDh_ne_eqLn : lDh ≠ eqLn := by decide
@[simp] theorem eq_eqLn_ne_lDt : eqLn ≠ lDt := by decide
@[simp] theorem eq_lDt_ne_eqLn : lDt ≠ eqLn := by decide
@[simp] theorem eq_eqLn_ne_lDg : eqLn ≠ lDg := by decide
@[simp] theorem eq_lDg_ne_eqLn : lDg ≠ eqLn := by decide
@[simp] theorem eq_eqLn_ne_lDi : eqLn ≠ lDi := by decide
@[simp] theorem eq_lDi_ne_eqLn : lDi ≠ eqLn := by decide
@[simp] theorem eq_eqLn_ne_lRp : eqLn ≠ lRp := by decide
@[simp] theorem eq_lRp_ne_eqLn : lRp ≠ eqLn := by decide
@[simp] theorem eq_eqLn_ne_lRn : eqLn ≠ lRn := by decide
@[simp] theorem eq_lRn_ne_eqLn : lRn ≠ eqLn := by decide
@[simp] theorem eq_eqLn_ne_lFle : eqLn ≠ lFle := by decide
@[simp] theorem eq_lFle_ne_eqLn : lFle ≠ eqLn := by decide
@[simp] theorem eq_eqLn_ne_lFls : eqLn ≠ lFls := by decide
@[simp] theorem eq_lFls_ne_eqLn : lFls ≠ eqLn := by decide
@[simp] theorem eq_eqLn_ne_lDir : eqLn ≠ lDir := by decide
@[simp] theorem eq_lDir_ne_eqLn : lDir ≠ eqLn := by decide
@[simp] theorem eq_eqLn_ne_lKb : eqLn ≠ lKb := by decide
@[simp] theorem eq_lKb_ne_eqLn : lKb ≠ eqLn := by decide
@[simp] theorem eq_eqLn_ne_kFu : eqLn ≠ kFu := by decide
@[simp] theorem eq_kFu_ne_eqLn : kFu ≠ eqLn := by decide
@[simp] theorem eq_eqLn_ne_kD : eqLn ≠ kD := by decide
@[simp] theorem eq_kD_ne_eqLn : kD ≠ eqLn := by decide
@[simp] theorem eq_eqLn_ne_rkR : eqLn ≠ rkR := by decide
@[simp] theorem eq_rkR_ne_eqLn : rkR ≠ eqLn := by decide
@[simp] theorem eq_eqLn_ne_rkJ : eqLn ≠ rkJ := by decide
@[simp] theorem eq_rkJ_ne_eqLn : rkJ ≠ eqLn := by decide
@[simp] theorem eq_eqLn_ne_rkT : eqLn ≠ rkT := by decide
@[simp] theorem eq_rkT_ne_eqLn : rkT ≠ eqLn := by decide
@[simp] theorem eq_eqLn_ne_rkM : eqLn ≠ rkM := by decide
@[simp] theorem eq_rkM_ne_eqLn : rkM ≠ eqLn := by decide
@[simp] theorem eq_eqLn_ne_reF : eqLn ≠ reF := by decide
@[simp] theorem eq_reF_ne_eqLn : reF ≠ eqLn := by decide
@[simp] theorem eq_eqLn_ne_reO : eqLn ≠ reO := by decide
@[simp] theorem eq_reO_ne_eqLn : reO ≠ eqLn := by decide
@[simp] theorem eq_eqFz_ne_eq1 : eqFz ≠ eq1 := by decide
@[simp] theorem eq_eqFz_ne_eqTm : eqFz ≠ eqTm := by decide
@[simp] theorem eq_eqFz_ne_eqHh : eqFz ≠ eqHh := by decide
@[simp] theorem eq_eqFz_ne_eqTp : eqFz ≠ eqTp := by decide
@[simp] theorem eq_eqFz_ne_eqUs : eqFz ≠ eqUs := by decide
@[simp] theorem eq_eqFz_ne_eqTa : eqFz ≠ eqTa := by decide
@[simp] theorem eq_eqFz_ne_eqTl : eqFz ≠ eqTl := by decide
@[simp] theorem eq_eqFz_ne_eqNp : eqFz ≠ eqNp := by decide
@[simp] theorem eq_eqFz_ne_eqLp : eqFz ≠ eqLp := by decide
@[simp] theorem eq_eqFz_ne_eqLn : eqFz ≠ eqLn := by decide
@[simp] theorem eq_eqFz_ne_eqNf : eqFz ≠ eqNf := by decide
@[simp] theorem eq_eqFz_ne_eqFa : eqFz ≠ eqFa := by decide
@[simp] theorem eq_eqFz_ne_eqTc : eqFz ≠ eqTc := by decide
@[simp] theorem eq_eqFz_ne_eqHd : eqFz ≠ eqHd := by decide
@[simp] theorem eq_eqFz_ne_eqFl : eqFz ≠ eqFl := by decide
@[simp] theorem eq_eqFz_ne_eqFab : eqFz ≠ eqFab := by decide
@[simp] theorem eq_eqFz_ne_eqFs : eqFz ≠ eqFs := by decide
@[simp] theorem eq_eqFz_ne_lFl : eqFz ≠ lFl := by decide
@[simp] theorem eq_lFl_ne_eqFz : lFl ≠ eqFz := by decide
@[simp] theorem eq_eqFz_ne_lDh : eqFz ≠ lDh := by decide
@[simp] theorem eq_lDh_ne_eqFz : lDh ≠ eqFz := by decide
@[simp] theorem eq_eqFz_ne_lDt : eqFz ≠ lDt := by decide
@[simp] theorem eq_lDt_ne_eqFz : lDt ≠ eqFz := by decide
@[simp] theorem eq_eqFz_ne_lDg : eqFz ≠ lDg := by decide
@[simp] theorem eq_lDg_ne_eqFz : lDg ≠ eqFz := by decide
@[simp] theorem eq_eqFz_ne_lDi : eqFz ≠ lDi := by decide
@[simp] theorem eq_lDi_ne_eqFz : lDi ≠ eqFz := by decide
@[simp] theorem eq_eqFz_ne_lRp : eqFz ≠ lRp := by decide
@[simp] theorem eq_lRp_ne_eqFz : lRp ≠ eqFz := by decide
@[simp] theorem eq_eqFz_ne_lRn : eqFz ≠ lRn := by decide
@[simp] theorem eq_lRn_ne_eqFz : lRn ≠ eqFz := by decide
@[simp] theorem eq_eqFz_ne_lFle : eqFz ≠ lFle := by decide
@[simp] theorem eq_lFle_ne_eqFz : lFle ≠ eqFz := by decide
@[simp] theorem eq_eqFz_ne_lFls : eqFz ≠ lFls := by decide
@[simp] theorem eq_lFls_ne_eqFz : lFls ≠ eqFz := by decide
@[simp] theorem eq_eqFz_ne_lDir : eqFz ≠ lDir := by decide
@[simp] theorem eq_lDir_ne_eqFz : lDir ≠ eqFz := by decide
@[simp] theorem eq_eqFz_ne_lKb : eqFz ≠ lKb := by decide
@[simp] theorem eq_lKb_ne_eqFz : lKb ≠ eqFz := by decide
@[simp] theorem eq_eqFz_ne_kFu : eqFz ≠ kFu := by decide
@[simp] theorem eq_kFu_ne_eqFz : kFu ≠ eqFz := by decide
@[simp] theorem eq_eqFz_ne_kD : eqFz ≠ kD := by decide
@[simp] theorem eq_kD_ne_eqFz : kD ≠ eqFz := by decide
@[simp] theorem eq_eqFz_ne_rkR : eqFz ≠ rkR := by decide
@[simp] theorem eq_rkR_ne_eqFz : rkR ≠ eqFz := by decide
@[simp] theorem eq_eqFz_ne_rkJ : eqFz ≠ rkJ := by decide
@[simp] theorem eq_rkJ_ne_eqFz : rkJ ≠ eqFz := by decide
@[simp] theorem eq_eqFz_ne_rkT : eqFz ≠ rkT := by decide
@[simp] theorem eq_rkT_ne_eqFz : rkT ≠ eqFz := by decide
@[simp] theorem eq_eqFz_ne_rkM : eqFz ≠ rkM := by decide
@[simp] theorem eq_rkM_ne_eqFz : rkM ≠ eqFz := by decide
@[simp] theorem eq_eqFz_ne_reF : eqFz ≠ reF := by decide
@[simp] theorem eq_reF_ne_eqFz : reF ≠ eqFz := by decide
@[simp] theorem eq_eqFz_ne_reO : eqFz ≠ reO := by decide
@[simp] theorem eq_reO_ne_eqFz : reO ≠ eqFz := by decide
@[simp] theorem eq_eqNf_ne_eq1 : eqNf ≠ eq1 := by decide
@[simp] theorem eq_eqNf_ne_eqTm : eqNf ≠ eqTm := by decide
@[simp] theorem eq_eqNf_ne_eqHh : eqNf ≠ eqHh := by decide
@[simp] theorem eq_eqNf_ne_eqTp : eqNf ≠ eqTp := by decide
@[simp] theorem eq_eqNf_ne_eqUs : eqNf ≠ eqUs := by decide
@[simp] theorem eq_eqNf_ne_eqTa : eqNf ≠ eqTa := by decide
@[simp] theorem eq_eqNf_ne_eqTl : eqNf ≠ eqTl := by decide
@[simp] theorem eq_eqNf_ne_eqNp : eqNf ≠ eqNp := by decide
@[simp] theorem eq_eqNf_ne_eqLp : eqNf ≠ eqLp := by decide
@[simp] theorem eq_eqNf_ne_eqLn : eqNf ≠ eqLn := by decide
@[simp] theorem eq_eqNf_ne_eqFz : eqNf ≠ eqFz := by decide
@[simp] theorem eq_eqNf_ne_eqFa : eqNf ≠ eqFa := by decide
@[simp] theorem eq_eqNf_ne_eqTc : eqNf ≠ eqTc := by decide
@[simp] theorem eq_eqNf_ne_eqHd : eqNf ≠ eqHd := by decide
@[simp] theorem eq_eqNf_ne_eqFl : eqNf ≠ eqFl := by decide
@[simp] theorem eq_eqNf_ne_eqFab : eqNf ≠ eqFab := by decide
@[simp] theorem eq_eqNf_ne_eqFs : eqNf ≠ eqFs := by decide
@[simp] theorem eq_eqNf_ne_lFl : eqNf ≠ lFl := by decide
@[simp] theorem eq_lFl_ne_eqNf : lFl ≠ eqNf := by decide
@[simp] theorem eq_eqNf_ne_lDh : eqNf ≠ lDh := by decide
@[simp] theorem eq_lDh_ne_eqNf : lDh ≠ eqNf := by decide
@[simp] theorem eq_eqNf_ne_lDt : eqNf ≠ lDt := by decide
@[simp] theorem eq_lDt_ne_eqNf : lDt ≠ eqNf := by decide
@[simp] theorem eq_eqNf_ne_lDg : eqNf ≠ lDg := by decide
@[simp] theorem eq_lDg_ne_eqNf : lDg ≠ eqNf := by decide
@[simp] theorem eq_eqNf_ne_lDi : eqNf ≠ lDi := by decide
@[simp] theorem eq_lDi_ne_eqNf : lDi ≠ eqNf := by decide
@[simp] theorem eq_eqNf_ne_lRp : eqNf ≠ lRp := by decide
@[simp] theorem eq_lRp_ne_eqNf : lRp ≠ eqNf := by decide
@[simp] theorem eq_eqNf_ne_lRn : eqNf ≠ lRn := by decide
@[simp] theorem eq_lRn_ne_eqNf : lRn ≠ eqNf := by decide
@[simp] theorem eq_eqNf_ne_lFle : eqNf ≠ lFle := by decide
@[simp] theorem eq_lFle_ne_eqNf : lFle ≠ eqNf := by decide
@[simp] theorem eq_eqNf_ne_lFls : eqNf ≠ lFls := by decide
@[simp] theorem eq_lFls_ne_eqNf : lFls ≠ eqNf := by decide
@[simp] theorem eq_eqNf_ne_lDir : eqNf ≠ lDir := by decide
@[simp] theorem eq_lDir_ne_eqNf : lDir ≠ eqNf := by decide
@[simp] theorem eq_eqNf_ne_lKb : eqNf ≠ lKb := by decide
@[simp] theorem eq_lKb_ne_eqNf : lKb ≠ eqNf := by decide
@[simp] theorem eq_eqNf_ne_kFu : eqNf ≠ kFu := by decide
@[simp] theorem eq_kFu_ne_eqNf : kFu ≠ eqNf := by decide
@[simp] theorem eq_eqNf_ne_kD : eqNf ≠ kD := by decide
@[simp] theorem eq_kD_ne_eqNf : kD ≠ eqNf := by decide
@[simp] theorem eq_eqNf_ne_rkR : eqNf ≠ rkR := by decide
@[simp] theorem eq_rkR_ne_eqNf : rkR ≠ eqNf := by decide
@[simp] theorem eq_eqNf_ne_rkJ : eqNf ≠ rkJ := by decide
@[simp] theorem eq_rkJ_ne_eqNf : rkJ ≠ eqNf := by decide
@[simp] theorem eq_eqNf_ne_rkT : eqNf ≠ rkT := by decide
@[simp] theorem eq_rkT_ne_eqNf : rkT ≠ eqNf := by decide
@[simp] theorem eq_eqNf_ne_rkM : eqNf ≠ rkM := by decide
@[simp] theorem eq_rkM_ne_eqNf : rkM ≠ eqNf := by decide
@[simp] theorem eq_eqNf_ne_reF : eqNf ≠ reF := by decide
@[simp] theorem eq_reF_ne_eqNf : reF ≠ eqNf := by decide
@[simp] theorem eq_eqNf_ne_reO : eqNf ≠ reO := by decide
@[simp] theorem eq_reO_ne_eqNf : reO ≠ eqNf := by decide
@[simp] theorem eq_eqFa_ne_eq1 : eqFa ≠ eq1 := by decide
@[simp] theorem eq_eqFa_ne_eqTm : eqFa ≠ eqTm := by decide
@[simp] theorem eq_eqFa_ne_eqHh : eqFa ≠ eqHh := by decide
@[simp] theorem eq_eqFa_ne_eqTp : eqFa ≠ eqTp := by decide
@[simp] theorem eq_eqFa_ne_eqUs : eqFa ≠ eqUs := by decide
@[simp] theorem eq_eqFa_ne_eqTa : eqFa ≠ eqTa := by decide
@[simp] theorem eq_eqFa_ne_eqTl : eqFa ≠ eqTl := by decide
@[simp] theorem eq_eqFa_ne_eqNp : eqFa ≠ eqNp := by decide
@[simp] theorem eq_eqFa_ne_eqLp : eqFa ≠ eqLp := by decide
@[simp] theorem eq_eqFa_ne_eqLn : eqFa ≠ eqLn := by decide
@[simp] theorem eq_eqFa_ne_eqFz : eqFa ≠ eqFz := by decide
@[simp] theorem eq_eqFa_ne_eqNf : eqFa ≠ eqNf := by decide
@[simp] theorem eq_eqFa_ne_eqTc : eqFa ≠ eqTc := by decide
@[simp] theorem eq_eqFa_ne_eqHd : eqFa ≠ eqHd := by decide
@[simp] theorem eq_eqFa_ne_eqFl : eqFa ≠ eqFl := by decide
@[simp] theorem eq_eqFa_ne_eqFab : eqFa ≠ eqFab := by decide
@[simp] theorem eq_eqFa_ne_eqFs : eqFa ≠ eqFs := by decide
@[simp] theorem eq_eqFa_ne_lFl : eqFa ≠ lFl := by decide
@[simp] theorem eq_lFl_ne_eqFa : lFl ≠ eqFa := by decide
@[simp] theorem eq_eqFa_ne_lDh : eqFa ≠ lDh := by decide
@[simp] theorem eq_lDh_ne_eqFa : lDh ≠ eqFa := by decide
@[simp] theorem eq_eqFa_ne_lDt : eqFa ≠ lDt := by decide
@[simp] theorem eq_lDt_ne_eqFa : lDt ≠ eqFa := by decide
@[simp] theorem eq_eqFa_ne_lDg : eqFa ≠ lDg := by decide
@[simp] theorem eq_lDg_ne_eqFa : lDg ≠ eqFa := by decide
@[simp] theorem eq_eqFa_ne_lDi : eqFa ≠ lDi := by decide
@[simp] theorem eq_lDi_ne_eqFa : lDi ≠ eqFa := by decide
@[simp] theorem eq_eqFa_ne_lRp : eqFa ≠ lRp := by decide
@[simp] theorem eq_lRp_ne_eqFa : lRp ≠ eqFa := by decide
@[simp] theorem eq_eqFa_ne_lRn : eqFa ≠ lRn := by decide
@[simp] theorem eq_lRn_ne_eqFa : lRn ≠ eqFa := by decide
@[simp] theorem eq_eqFa_ne_lFle : eqFa ≠ lFle := by decide
@[simp] theorem eq_lFle_ne_eqFa : lFle ≠ eqFa := by decide
@[simp] theorem eq_eqFa_ne_lFls : eqFa ≠ lFls := by decide
@[simp] theorem eq_lFls_ne_eqFa : lFls ≠ eqFa := by decide
@[simp] theorem eq_eqFa_ne_lDir : eqFa ≠ lDir := by decide
@[simp] theorem eq_lDir_ne_eqFa : lDir ≠ eqFa := by decide
@[simp] theorem eq_eqFa_ne_lKb : eqFa ≠ lKb := by decide
@[simp] theorem eq_lKb_ne_eqFa : lKb ≠ eqFa := by decide
@[simp] theorem eq_eqFa_ne_kFu : eqFa ≠ kFu := by decide
@[simp] theorem eq_kFu_ne_eqFa : kFu ≠ eqFa := by decide
@[simp] theorem eq_eqFa_ne_kD : eqFa ≠ kD := by decide
@[simp] theorem eq_kD_ne_eqFa : kD ≠ eqFa := by decide
@[simp] theorem eq_eqFa_ne_rkR : eqFa ≠ rkR := by decide
@[simp] theorem eq_rkR_ne_eqFa : rkR ≠ eqFa := by decide
@[simp] theorem eq_eqFa_ne_rkJ : eqFa ≠ rkJ := by decide
@[simp] theorem eq_rkJ_ne_eqFa : rkJ ≠ eqFa := by decide
@[simp] theorem eq_eqFa_ne_rkT : eqFa ≠ rkT := by decide
@[simp] theorem eq_rkT_ne_eqFa : rkT ≠ eqFa := by decide
@[simp] theorem eq_eqFa_ne_rkM : eqFa ≠ rkM := by decide
@[simp] theorem eq_rkM_ne_eqFa : rkM ≠ eqFa := by decide
@[simp] theorem eq_eqFa_ne_reF : eqFa ≠ reF := by decide
@[simp] theorem eq_reF_ne_eqFa : reF ≠ eqFa := by decide
@[simp] theorem eq_eqFa_ne_reO : eqFa ≠ reO := by decide
@[simp] theorem eq_reO_ne_eqFa : reO ≠ eqFa := by decide
@[simp] theorem eq_eqTc_ne_eq1 : eqTc ≠ eq1 := by decide
@[simp] theorem eq_eqTc_ne_eqTm : eqTc ≠ eqTm := by decide
@[simp] theorem eq_eqTc_ne_eqHh : eqTc ≠ eqHh := by decide
@[simp] theorem eq_eqTc_ne_eqTp : eqTc ≠ eqTp := by decide
@[simp] theorem eq_eqTc_ne_eqUs : eqTc ≠ eqUs := by decide
@[simp] theorem eq_eqTc_ne_eqTa : eqTc ≠ eqTa := by decide
@[simp] theorem eq_eqTc_ne_eqTl : eqTc ≠ eqTl := by decide
@[simp] theorem eq_eqTc_ne_eqNp : eqTc ≠ eqNp := by decide
@[simp] theorem eq_eqTc_ne_eqLp : eqTc ≠ eqLp := by decide
@[simp] theorem eq_eqTc_ne_eqLn : eqTc ≠ eqLn := by decide
@[simp] theorem eq_eqTc_ne_eqFz : eqTc ≠ eqFz := by decide
@[simp] theorem eq_eqTc_ne_eqNf : eqTc ≠ eqNf := by decide
@[simp] theorem eq_eqTc_ne_eqFa : eqTc ≠ eqFa := by decide
@[simp] theorem eq_eqTc_ne_eqHd : eqTc ≠ eqHd := by decide
@[simp] theorem eq_eqTc_ne_eqFl : eqTc ≠ eqFl := by decide
@[simp] theorem eq_eqTc_ne_eqFab : eqTc ≠ eqFab := by decide
@[simp] theorem eq_eqTc_ne_eqFs : eqTc ≠ eqFs := by decide
@[simp] theorem eq_eqTc_ne_lFl : eqTc ≠ lFl := by decide
@[simp] theorem eq_lFl_ne_eqTc : lFl ≠ eqTc := by decide
@[simp] theorem eq_eqTc_ne_lDh : eqTc ≠ lDh := by decide
@[simp] theorem eq_lDh_ne_eqTc : lDh ≠ eqTc := by decide
@[simp] theorem eq_eqTc_ne_lDt : eqTc ≠ lDt := by decide
@[simp] theorem eq_lDt_ne_eqTc : lDt ≠ eqTc := by decide
@[simp] theorem eq_eqTc_ne_lDg : eqTc ≠ lDg := by decide
@[simp] theorem eq_lDg_ne_eqTc : lDg ≠ eqTc := by decide
@[simp] theorem eq_eqTc_ne_lDi : eqTc ≠ lDi := by decide
@[simp] theorem eq_lDi_ne_eqTc : lDi ≠ eqTc := by decide
@[simp] theorem eq_eqTc_ne_lRp : eqTc ≠ lRp := by decide
@[simp] theorem eq_lRp_ne_eqTc : lRp ≠ eqTc := by decide
@[simp] theorem eq_eqTc_ne_lRn : eqTc ≠ lRn := by decide
@[simp] theorem eq_lRn_ne_eqTc : lRn ≠ eqTc := by decide
@[simp] theorem eq_eqTc_ne_lFle : eqTc ≠ lFle := by decide
@[simp] theorem eq_lFle_ne_eqTc : lFle ≠ eqTc := by decide
@[simp] theorem eq_eqTc_ne_lFls : eqTc ≠ lFls := by decide
@[simp] theorem eq_lFls_ne_eqTc : lFls ≠ eqTc := by decide
@[simp] theorem eq_eqTc_ne_lDir : eqTc ≠ lDir := by decide
@[simp] theorem eq_lDir_ne_eqTc : lDir ≠ eqTc := by decide
@[simp] theorem eq_eqTc_ne_lKb : eqTc ≠ lKb := by decide
@[simp] theorem eq_lKb_ne_eqTc : lKb ≠ eqTc := by decide
@[simp] theorem eq_eqTc_ne_kFu : eqTc ≠ kFu := by decide
@[simp] theorem eq_kFu_ne_eqTc : kFu ≠ eqTc := by decide
@[simp] theorem eq_eqTc_ne_kD : eqTc ≠ kD := by decide
@[simp] theorem eq_kD_ne_eqTc : kD ≠ eqTc := by decide
@[simp] theorem eq_eqTc_ne_rkR : eqTc ≠ rkR := by decide
@[simp] theorem eq_rkR_ne_eqTc : rkR ≠ eqTc := by decide
@[simp] theorem eq_eqTc_ne_rkJ : eqTc ≠ rkJ := by decide
@[simp] theorem eq_rkJ_ne_eqTc : rkJ ≠ eqTc := by decide
@[simp] theorem eq_eqTc_ne_rkT : eqTc ≠ rkT := by decide
@[simp] theorem eq_rkT_ne_eqTc : rkT ≠ eqTc := by decide
@[simp] theorem eq_eqTc_ne_rkM : eqTc ≠ rkM := by decide
@[simp] theorem eq_rkM_ne_eqTc : rkM ≠ eqTc := by decide
@[simp] theorem eq_eqTc_ne_reF : eqTc ≠ reF := by decide
@[simp] theorem eq_reF_ne_eqTc : reF ≠ eqTc := by decide
@[simp] theorem eq_eqTc_ne_reO : eqTc ≠ reO := by decide
@[simp] theorem eq_reO_ne_eqTc : reO ≠ eqTc := by decide
@[simp] theorem eq_eqHd_ne_eq1 : eqHd ≠ eq1 := by decide
@[simp] theorem eq_eqHd_ne_eqTm : eqHd ≠ eqTm := by decide
@[simp] theorem eq_eqHd_ne_eqHh : eqHd ≠ eqHh := by decide
@[simp] theorem eq_eqHd_ne_eqTp : eqHd ≠ eqTp := by decide
@[simp] theorem eq_eqHd_ne_eqUs : eqHd ≠ eqUs := by decide
@[simp] theorem eq_eqHd_ne_eqTa : eqHd ≠ eqTa := by decide
@[simp] theorem eq_eqHd_ne_eqTl : eqHd ≠ eqTl := by decide
@[simp] theorem eq_eqHd_ne_eqNp : eqHd ≠ eqNp := by decide
@[simp] theorem eq_eqHd_ne_eqLp : eqHd ≠ eqLp := by decide
@[simp] theorem eq_eqHd_ne_eqLn : eqHd ≠ eqLn := by decide
@[simp] theorem eq_eqHd_ne_eqFz : eqHd ≠ eqFz := by decide
@[simp] theorem eq_eqHd_ne_eqNf : eqHd ≠ eqNf := by decide
@[simp] theorem eq_eqHd_ne_eqFa : eqHd ≠ eqFa := by decide
@[simp] theorem eq_eqHd_ne_eqTc : eqHd ≠ eqTc := by decide
@[simp] theorem eq_eqHd_ne_eqFl : eqHd ≠ eqFl := by decide
@[simp] theorem eq_eqHd_ne_eqFab : eqHd ≠ eqFab := by decide
@[simp] theorem eq_eqHd_ne_eqFs : eqHd ≠ eqFs := by decide
@[simp] theorem eq_eqHd_ne_lFl : eqHd ≠ lFl := by decide
@[simp] theorem eq_lFl_ne_eqHd : lFl ≠ eqHd := by decide
@[simp] theorem eq_eqHd_ne_lDh : eqHd ≠ lDh := by decide
@[simp] theorem eq_lDh_ne_eqHd : lDh ≠ eqHd := by decide
@[simp] theorem eq_eqHd_ne_lDt : eqHd ≠ lDt := by decide
@[simp] theorem eq_lDt_ne_eqHd : lDt ≠ eqHd := by decide
@[simp] theorem eq_eqHd_ne_lDg : eqHd ≠ lDg := by decide
@[simp] theorem eq_lDg_ne_eqHd : lDg ≠ eqHd := by decide
@[simp] theorem eq_eqHd_ne_lDi : eqHd ≠ lDi := by decide
@[simp] theorem eq_lDi_ne_eqHd : lDi ≠ eqHd := by decide
@[simp] theorem eq_eqHd_ne_lRp : eqHd ≠ lRp := by decide
@[simp] theorem eq_lRp_ne_eqHd : lRp ≠ eqHd := by decide
@[simp] theorem eq_eqHd_ne_lRn : eqHd ≠ lRn := by decide
@[simp] theorem eq_lRn_ne_eqHd : lRn ≠ eqHd := by decide
@[simp] theorem eq_eqHd_ne_lFle : eqHd ≠ lFle := by decide
@[simp] theorem eq_lFle_ne_eqHd : lFle ≠ eqHd := by decide
@[simp] theorem eq_eqHd_ne_lFls : eqHd ≠ lFls := by decide
@[simp] theorem eq_lFls_ne_eqHd : lFls ≠ eqHd := by decide
@[simp] theorem eq_eqHd_ne_lDir : eqHd ≠ lDir := by decide
@[simp] theorem eq_lDir_ne_eqHd : lDir ≠ eqHd := by decide
@[simp] theorem eq_eqHd_ne_lKb : eqHd ≠ lKb := by decide
@[simp] theorem eq_lKb_ne_eqHd : lKb ≠ eqHd := by decide
@[simp] theorem eq_eqHd_ne_kFu : eqHd ≠ kFu := by decide
@[simp] theorem eq_kFu_ne_eqHd : kFu ≠ eqHd := by decide
@[simp] theorem eq_eqHd_ne_kD : eqHd ≠ kD := by decide
@[simp] theorem eq_kD_ne_eqHd : kD ≠ eqHd := by decide
@[simp] theorem eq_eqHd_ne_rkR : eqHd ≠ rkR := by decide
@[simp] theorem eq_rkR_ne_eqHd : rkR ≠ eqHd := by decide
@[simp] theorem eq_eqHd_ne_rkJ : eqHd ≠ rkJ := by decide
@[simp] theorem eq_rkJ_ne_eqHd : rkJ ≠ eqHd := by decide
@[simp] theorem eq_eqHd_ne_rkT : eqHd ≠ rkT := by decide
@[simp] theorem eq_rkT_ne_eqHd : rkT ≠ eqHd := by decide
@[simp] theorem eq_eqHd_ne_rkM : eqHd ≠ rkM := by decide
@[simp] theorem eq_rkM_ne_eqHd : rkM ≠ eqHd := by decide
@[simp] theorem eq_eqHd_ne_reF : eqHd ≠ reF := by decide
@[simp] theorem eq_reF_ne_eqHd : reF ≠ eqHd := by decide
@[simp] theorem eq_eqHd_ne_reO : eqHd ≠ reO := by decide
@[simp] theorem eq_reO_ne_eqHd : reO ≠ eqHd := by decide
@[simp] theorem eq_eqFl_ne_eq1 : eqFl ≠ eq1 := by decide
@[simp] theorem eq_eqFl_ne_eqTm : eqFl ≠ eqTm := by decide
@[simp] theorem eq_eqFl_ne_eqHh : eqFl ≠ eqHh := by decide
@[simp] theorem eq_eqFl_ne_eqTp : eqFl ≠ eqTp := by decide
@[simp] theorem eq_eqFl_ne_eqUs : eqFl ≠ eqUs := by decide
@[simp] theorem eq_eqFl_ne_eqTa : eqFl ≠ eqTa := by decide
@[simp] theorem eq_eqFl_ne_eqTl : eqFl ≠ eqTl := by decide
@[simp] theorem eq_eqFl_ne_eqNp : eqFl ≠ eqNp := by decide
@[simp] theorem eq_eqFl_ne_eqLp : eqFl ≠ eqLp := by decide
@[simp] theorem eq_eqFl_ne_eqLn : eqFl ≠ eqLn := by decide
@[simp] theorem eq_eqFl_ne_eqFz : eqFl ≠ eqFz := by decide
@[simp] theorem eq_eqFl_ne_eqNf : eqFl ≠ eqNf := by decide
@[simp] theorem eq_eqFl_ne_eqFa : eqFl ≠ eqFa := by decide
@[simp] theorem eq_eqFl_ne_eqTc : eqFl ≠ eqTc := by decide
@[simp] theorem eq_eqFl_ne_eqHd : eqFl ≠ eqHd := by decide
@[simp] theorem eq_eqFl_ne_eqFab : eqFl ≠ eqFab := by decide
@[simp] theorem eq_eqFl_ne_eqFs : eqFl ≠ eqFs := by decide
@[simp] theorem eq_eqFl_ne_lFl : eqFl ≠ lFl := by decide
@[simp] theorem eq_lFl_ne_eqFl : lFl ≠ eqFl := by decide
@[simp] theorem eq_eqFl_ne_lDh : eqFl ≠ lDh := by decide
@[simp] theorem eq_lDh_ne_eqFl : lDh ≠ eqFl := by decide
@[simp] theorem eq_eqFl_ne_lDt : eqFl ≠ lDt := by decide
@[simp] theorem eq_lDt_ne_eqFl : lDt ≠ eqFl := by decide
@[simp] theorem eq_eqFl_ne_lDg : eqFl ≠ lDg := by decide
@[simp] theorem eq_lDg_ne_eqFl : lDg ≠ eqFl := by decide
@[simp] theorem eq_eqFl_ne_lDi : eqFl ≠ lDi := by decide
@[simp] theorem eq_lDi_ne_eqFl : lDi ≠ eqFl := by decide
@[simp] theorem eq_eqFl_ne_lRp : eqFl ≠ lRp := by decide
@[simp] theorem eq_lRp_ne_eqFl : lRp ≠ eqFl := by decide
@[simp] theorem eq_eqFl_ne_lRn : eqFl ≠ lRn := by decide
@[simp] theorem eq_lRn_ne_eqFl : lRn ≠ eqFl := by decide
@[simp] theorem eq_eqFl_ne_lFle : eqFl ≠ lFle := by decide
@[simp] theorem eq_lFle_ne_eqFl : lFle ≠ eqFl := by decide
@[simp] theorem eq_eqFl_ne_lFls : eqFl ≠ lFls := by decide
@[simp] theorem eq_lFls_ne_eqFl : lFls ≠ eqFl := by decide
@[simp] theorem eq_eqFl_ne_lDir : eqFl ≠ lDir := by decide
@[simp] theorem eq_lDir_ne_eqFl : lDir ≠ eqFl := by decide
@[simp] theorem eq_eqFl_ne_lKb : eqFl ≠ lKb := by decide
@[simp] theorem eq_lKb_ne_eqFl : lKb ≠ eqFl := by decide
@[simp] theorem eq_eqFl_ne_kFu : eqFl ≠ kFu := by decide
@[simp] theorem eq_kFu_ne_eqFl : kFu ≠ eqFl := by decide
@[simp] theorem eq_eqFl_ne_kD : eqFl ≠ kD := by decide
@[simp] theorem eq_kD_ne_eqFl : kD ≠ eqFl := by decide
@[simp] theorem eq_eqFl_ne_rkR : eqFl ≠ rkR := by decide
@[simp] theorem eq_rkR_ne_eqFl : rkR ≠ eqFl := by decide
@[simp] theorem eq_eqFl_ne_rkJ : eqFl ≠ rkJ := by decide
@[simp] theorem eq_rkJ_ne_eqFl : rkJ ≠ eqFl := by decide
@[simp] theorem eq_eqFl_ne_rkT : eqFl ≠ rkT := by decide
@[simp] theorem eq_rkT_ne_eqFl : rkT ≠ eqFl := by decide
@[simp] theorem eq_eqFl_ne_rkM : eqFl ≠ rkM := by decide
@[simp] theorem eq_rkM_ne_eqFl : rkM ≠ eqFl := by decide
@[simp] theorem eq_eqFl_ne_reF : eqFl ≠ reF := by decide
@[simp] theorem eq_reF_ne_eqFl : reF ≠ eqFl := by decide
@[simp] theorem eq_eqFl_ne_reO : eqFl ≠ reO := by decide
@[simp] theorem eq_reO_ne_eqFl : reO ≠ eqFl := by decide
@[simp] theorem eq_eqFab_ne_eq1 : eqFab ≠ eq1 := by decide
@[simp] theorem eq_eqFab_ne_eqTm : eqFab ≠ eqTm := by decide
@[simp] theorem eq_eqFab_ne_eqHh : eqFab ≠ eqHh := by decide
@[simp] theorem eq_eqFab_ne_eqTp : eqFab ≠ eqTp := by decide
@[simp] theorem eq_eqFab_ne_eqUs : eqFab ≠ eqUs := by decide
@[simp] theorem eq_eqFab_ne_eqTa : eqFab ≠ eqTa := by decide
@[simp] theorem eq_eqFab_ne_eqTl : eqFab ≠ eqTl := by decide
@[simp] theorem eq_eqFab_ne_eqNp : eqFab ≠ eqNp := by decide
@[simp] theorem eq_eqFab_ne_eqLp : eqFab ≠ eqLp := by decide
@[simp] theorem eq_eqFab_ne_eqLn : eqFab ≠ eqLn := by decide
@[simp] theorem eq_eqFab_ne_eqFz : eqFab ≠ eqFz := by decide
@[simp] theorem eq_eqFab_ne_eqNf : eqFab ≠ eqNf := by decide
@[simp] theorem eq_eqFab_ne_eqFa : eqFab ≠ eqFa := by decide
@[simp] theorem eq_eqFab_ne_eqTc : eqFab ≠ eqTc := by decide
@[simp] theorem eq_eqFab_ne_eqHd : eqFab ≠ eqHd := by decide
@[simp] theorem eq_eqFab_ne_eqFl : eqFab ≠ eqFl := by decide
@[simp] theorem eq_eqFab_ne_eqFs : eqFab ≠ eqFs := by decide
@[simp] theorem eq_eqFab_ne_lFl : eqFab ≠ lFl := by decide
@[simp] theorem eq_lFl_ne_eqFab : lFl ≠ eqFab := by decide
@[simp] theorem eq_eqFab_ne_lDh : eqFab ≠ lDh := by decide
@[simp] theorem eq_lDh_ne_eqFab : lDh ≠ eqFab := by decide
@[simp] theorem eq_eqFab_ne_lDt : eqFab ≠ lDt := by decide
@[simp] theorem eq_lDt_ne_eqFab : lDt ≠ eqFab := by decide
@[simp] theorem eq_eqFab_ne_lDg : eqFab ≠ lDg := by decide
@[simp] theorem eq_lDg_ne_eqFab : lDg ≠ eqFab := by decide
@[simp] theorem eq_eqFab_ne_lDi : eqFab ≠ lDi := by decide
@[simp] theorem eq_lDi_ne_eqFab : lDi ≠ eqFab := by decide
@[simp] theorem eq_eqFab_ne_lRp : eqFab ≠ lRp := by decide
@[simp] theorem eq_lRp_ne_eqFab : lRp ≠ eqFab := by decide
@[simp] theorem eq_eqFab_ne_lRn : eqFab ≠ lRn := by decide
@[simp] theorem eq_lRn_ne_eqFab : lRn ≠ eqFab := by decide
@[simp] theorem eq_eqFab_ne_lFle : eqFab ≠ lFle := by decide
@[simp] theorem eq_lFle_ne_eqFab : lFle ≠ eqFab := by decide
@[simp] theorem eq_eqFab_ne_lFls : eqFab ≠ lFls := by decide
@[simp] theorem eq_lFls_ne_eqFab : lFls ≠ eqFab := by decide
@[simp] theorem eq_eqFab_ne_lDir : eqFab ≠ lDir := by decide
@[simp] theorem eq_lDir_ne_eqFab : lDir ≠ eqFab := by decide
@[simp] theorem eq_eqFab_ne_lKb : eqFab ≠ lKb := by decide
@[simp] theorem eq_lKb_ne_eqFab : lKb ≠ eqFab := by decide
@[simp] theorem eq_eqFab_ne_kFu : eqFab ≠ kFu := by decide
@[simp] theorem eq_kFu_ne_eqFab : kFu ≠ eqFab := by decide
@[simp] theorem eq_eqFab_ne_kD : eqFab ≠ kD := by decide
@[simp] theorem eq_kD_ne_eqFab : kD ≠ eqFab := by decide
@[simp] theorem eq_eqFab_ne_rkR : eqFab ≠ rkR := by decide
@[simp] theorem eq_rkR_ne_eqFab : rkR ≠ eqFab := by decide
@[simp] theorem eq_eqFab_ne_rkJ : eqFab ≠ rkJ := by decide
@[simp] theorem eq_rkJ_ne_eqFab : rkJ ≠ eqFab := by decide
@[simp] theorem eq_eqFab_ne_rkT : eqFab ≠ rkT := by decide
@[simp] theorem eq_rkT_ne_eqFab : rkT ≠ eqFab := by decide
@[simp] theorem eq_eqFab_ne_rkM : eqFab ≠ rkM := by decide
@[simp] theorem eq_rkM_ne_eqFab : rkM ≠ eqFab := by decide
@[simp] theorem eq_eqFab_ne_reF : eqFab ≠ reF := by decide
@[simp] theorem eq_reF_ne_eqFab : reF ≠ eqFab := by decide
@[simp] theorem eq_eqFab_ne_reO : eqFab ≠ reO := by decide
@[simp] theorem eq_reO_ne_eqFab : reO ≠ eqFab := by decide
@[simp] theorem eq_eqFs_ne_eq1 : eqFs ≠ eq1 := by decide
@[simp] theorem eq_eqFs_ne_eqTm : eqFs ≠ eqTm := by decide
@[simp] theorem eq_eqFs_ne_eqHh : eqFs ≠ eqHh := by decide
@[simp] theorem eq_eqFs_ne_eqTp : eqFs ≠ eqTp := by decide
@[simp] theorem eq_eqFs_ne_eqUs : eqFs ≠ eqUs := by decide
@[simp] theorem eq_eqFs_ne_eqTa : eqFs ≠ eqTa := by decide
@[simp] theorem eq_eqFs_ne_eqTl : eqFs ≠ eqTl := by decide
@[simp] theorem eq_eqFs_ne_eqNp : eqFs ≠ eqNp := by decide
@[simp] theorem eq_eqFs_ne_eqLp : eqFs ≠ eqLp := by decide
@[simp] theorem eq_eqFs_ne_eqLn : eqFs ≠ eqLn := by decide
@[simp] theorem eq_eqFs_ne_eqFz : eqFs ≠ eqFz := by decide
@[simp] theorem eq_eqFs_ne_eqNf : eqFs ≠ eqNf := by decide
@[simp] theorem eq_eqFs_ne_eqFa : eqFs ≠ eqFa := by decide
@[simp] theorem eq_eqFs_ne_eqTc : eqFs ≠ eqTc := by decide
@[simp] theorem eq_eqFs_ne_eqHd : eqFs ≠ eqHd := by decide
@[simp] theorem eq_eqFs_ne_eqFl : eqFs ≠ eqFl := by decide
@[simp] theorem eq_eqFs_ne_eqFab : eqFs ≠ eqFab := by decide
@[simp] theorem eq_eqFs_ne_lFl : eqFs ≠ lFl := by decide
@[simp] theorem eq_lFl_ne_eqFs : lFl ≠ eqFs := by decide
@[simp] theorem eq_eqFs_ne_lDh : eqFs ≠ lDh := by decide
@[simp] theorem eq_lDh_ne_eqFs : lDh ≠ eqFs := by decide
@[simp] theorem eq_eqFs_ne_lDt : eqFs ≠ lDt := by decide
@[simp] theorem eq_lDt_ne_eqFs : lDt ≠ eqFs := by decide
@[simp] theorem eq_eqFs_ne_lDg : eqFs ≠ lDg := by decide
@[simp] theorem eq_lDg_ne_eqFs : lDg ≠ eqFs := by decide
@[simp] theorem eq_eqFs_ne_lDi : eqFs ≠ lDi := by decide
@[simp] theorem eq_lDi_ne_eqFs : lDi ≠ eqFs := by decide
@[simp] theorem eq_eqFs_ne_lRp : eqFs ≠ lRp := by decide
@[simp] theorem eq_lRp_ne_eqFs : lRp ≠ eqFs := by decide
@[simp] theorem eq_eqFs_ne_lRn : eqFs ≠ lRn := by decide
@[simp] theorem eq_lRn_ne_eqFs : lRn ≠ eqFs := by decide
@[simp] theorem eq_eqFs_ne_lFle : eqFs ≠ lFle := by decide
@[simp] theorem eq_lFle_ne_eqFs : lFle ≠ eqFs := by decide
@[simp] theorem eq_eqFs_ne_lFls : eqFs ≠ lFls := by decide
@[simp] theorem eq_lFls_ne_eqFs : lFls ≠ eqFs := by decide
@[simp] theorem eq_eqFs_ne_lDir : eqFs ≠ lDir := by decide
@[simp] theorem eq_lDir_ne_eqFs : lDir ≠ eqFs := by decide
@[simp] theorem eq_eqFs_ne_lKb : eqFs ≠ lKb := by decide
@[simp] theorem eq_lKb_ne_eqFs : lKb ≠ eqFs := by decide
@[simp] theorem eq_eqFs_ne_kFu : eqFs ≠ kFu := by decide
@[simp] theorem eq_kFu_ne_eqFs : kFu ≠ eqFs := by decide
@[simp] theorem eq_eqFs_ne_kD : eqFs ≠ kD := by decide
@[simp] theorem eq_kD_ne_eqFs : kD ≠ eqFs := by decide
@[simp] theorem eq_eqFs_ne_rkR : eqFs ≠ rkR := by decide
@[simp] theorem eq_rkR_ne_eqFs : rkR ≠ eqFs := by decide
@[simp] theorem eq_eqFs_ne_rkJ : eqFs ≠ rkJ := by decide
@[simp] theorem eq_rkJ_ne_eqFs : rkJ ≠ eqFs := by decide
@[simp] theorem eq_eqFs_ne_rkT : eqFs ≠ rkT := by decide
@[simp] theorem eq_rkT_ne_eqFs : rkT ≠ eqFs := by decide
@[simp] theorem eq_eqFs_ne_rkM : eqFs ≠ rkM := by decide
@[simp] theorem eq_rkM_ne_eqFs : rkM ≠ eqFs := by decide
@[simp] theorem eq_eqFs_ne_reF : eqFs ≠ reF := by decide
@[simp] theorem eq_reF_ne_eqFs : reF ≠ eqFs := by decide
@[simp] theorem eq_eqFs_ne_reO : eqFs ≠ reO := by decide
@[simp] theorem eq_reO_ne_eqFs : reO ≠ eqFs := by decide

def reLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, eq1, eqTm, eqHh, eqTp, eqUs, eqTa, eqTl, eqNp, eqLp, eqLn, eqFz, eqNf, eqFa, eqTc, eqHd, eqFl, eqFab, eqFs]

def reBody : ProgHOL 64 := prologue reLocals
  (.seq (.call (some (some (.local, eq1), none)) fIO [vv kFu, vv kD, vv rkM])
  (.seq (.call (some (some (.local, eqTm), none)) fW [vv kFu, vv kD, vv eq1])
  (.seq (.call (some (some (.local, eqHh), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv eqTm])
  (.ite (tagIsE eqHh 3)
  (.seq (.assign .local lFl (vv lFle))
  (.seq (.assign .local lDh (vv eqHh))
  (.seq eViewP
  (.seq (.assign .local eqTp (.load .one (vv lRp)))
  (.seq (.assign .local eqUs (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (.assign .local lFl (vv lFls))
  (.seq (.assign .local lDh (vv eqUs))
  (.seq lsViewP
  (.seq (.call (some (some (.local, eqTa), none)) ExG.fGaa [.const (BitVec.ofNat 64 coreWalkFuel), vv eqTm])
  (.seq (.assign .local eqTl (.load .one (vv eqTa)))
  (.seq (.assign .local eqNp (.load .one (.op .add [vv reO, .const 16])))
  (.seq (.assign .local eqLp (.load .one (.op .add [vv reF, .const 16])))
  (.seq (.assign .local eqLn (.load .one (vv eqLp)))
  (.ite (.cmp .notEqual (vv eqTp) (vv rkT)) (.return (vv rkM))
  (.ite (.cmp .notEqual (vv eqTl) (vv eqNp)) (.return (vv rkM))
  (.ite (.cmp .notEqual (vv lRn) (vv eqLn)) (.return (vv rkM))
  (.seq (.call (some (some (.local, eqFz), none)) fFz [vv kFu, vv kD, vv reF, vv eqUs])
  (.ite (.cmp .equal (vv eqFz) (.const 0)) (.return (vv rkM))
  (.seq (.assign .local eqNf (.load .one (.op .add [vv reO, .const 32])))
  (.seq (.call (some (some (.local, eqFa), none)) fEf [vv rkT, vv rkM, vv eqTa, .const 0, vv eqNf])
  (.seq (.assign .local eqTc (.load .one (.op .add [vv reO, .const 24])))
  (.seq (.call (some (some (.local, eqHd), none)) fInternConst [vv eqTc, vv eqUs])
  (.seq (.assign .local eqFl (.load .one (vv eqFa)))
  (.seq (.call (some (some (.local, eqFab), none)) ExK.fMka [vv eqHd, vv eqFa, .const 0, vv eqFl])
  (.seq (.call (some (some (.local, eqFs), none)) fFab [vv kD, vv eqFab, vv rkM])
  (.ite (.cmp .equal (vv eqFs) (.const 0)) (.return (vv rkM)) (.return (vv eqFab))))))))))))))))))))))))))))
  (.return (vv rkM))))))

section
variable {σ : Type}

theorem re_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ reLocals → (ctxEnv C ++ reParams.zip vals).get x = none :=
  Knot.params_none C reLocals reParams vals (by decide) (by decide)

structure ReCodes (C : Ctx) (Bfab Bfz : ProgHOL 64) : Prop where
  io : C.code.lookup fIO = some (pmap kParams, inferIOE C fIOB, .one)
  w : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one)
  af : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  gaa : C.code.lookup ExG.fGaa = some ([(pFu, .one), (pH, .one)], ExG.gaaBody C, .one)
  ic : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one)
  mka : C.code.lookup ExK.fMka = some ([(ExK.pF, .one), (ExK.pP, .one), (ExK.pI, .one), (ExK.pN, .one)],
    ExK.mkaBody, .one)
  ia : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)
  ip : C.code.lookup fInternProj = some ([(lEp, .one), (lEe, .one), (lIw, .one)], projBody, .one)
  app : C.code.lookup ExPre.fAppend = some (ExPre.appParams.map (fun p => (p, ShapeHOL.one)), ExPre.appBody C, .one)
  ef : C.code.lookup fEf = some (efParams.map (fun p => (p, ShapeHOL.one)), efBody, .one)
  fab : C.code.lookup fFab = some (fbParams.map (fun p => (p, ShapeHOL.one)), Bfab, .one)
  fz : C.code.lookup fFz = some (fzParams.map (fun p => (p, ShapeHOL.one)), Bfz, .one)

theorem re_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (Bfab Bfz : ProgHOL 64) (hc : ReCodes C Bfab Bfz)
    (s : AState) (d : Nat) (rl : IRecRule) (qr : Nat) (cvj : IConstantVal) (cnP nF : Nat) (T : NIdx) (qj : Nat)
    (m : EIdx) (cvT : IConstantVal) (caps : IIndCaps) (qT : Nat) (tbl : IProjTable) (o : Nat)
    (hcT : CIE C.EB C.EH qT (.indInfo cvT caps)) (htb : TblE C.EB C.EH o tbl)
    (hIO : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ e', Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e'] (inferIOE C fIOB) s1 ((knot mode C n).inferIO d e')
      (PostK (ctxH C H)))
    (hW : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ e', Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d e')
      (PostK (ctxH C H)))
    (hFab : ∀ (H : List (BitVec 64)) s1 (f mj : EIdx), C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s1 (fbParams.zip [BitVec.ofNat 64 d, Enc.idxW f, Enc.idxW mj])) Bfab s1
        (fabScopeOk d f mj) (PostB (ctxH C H)))
    (hFz : ∀ (H : List (BitVec 64)) s1 (us : LsIdx), C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s1 (fzParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, ecell C qT, Enc.idxW us]))
        Bfz s1 (familyNeverZeroAt (knot mode C n) cvT caps us) (PostB (ctxH C H))) :
    SpecR (σ := σ) (Pre C s (reParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, ecell C qr, ecell C qj, Enc.idxW T,
      Enc.idxW m, ecell C qT, ecell C o])) reBody s
      (rescueEta mode (knot mode C n) C.fe d rl cvj cnP T m cvT caps tbl) (PostK C) := by
  refine specR_prologue (Knot.postK_locals C) (re_none C _) ?_
  unfold rescueEta
  have hretM : ∀ {Γ : Env} {M : Mem} {H : List (BitVec 64)} {s2 : AState}, C.H <+: H → Γ.get rkM = some (Enc.idxW m) →
      SpecR (σ := σ) (Inv (ctxH C H) s2 Γ M (ctxLocals ++ reLocals)) (.return (vv rkM)) s2 (pure m) (PostK C) :=
    fun hp hE => specR_returnI _ (Enc.idxW m) (by simpa using hE)
      (fun t ht => ⟨_, hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine Big.specR_callKC eq1 fIO kParams [vv kFu, vv kD, vv rkM] (inferIOE C fIOB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW m] (by decide) rfl (by decide) hc.io
    ⟨by simp +decide [Env.get, reParams, ctxEnv], by simp +decide [Env.get, reParams, ctxEnv],
      by simp +decide [Env.get, reParams, ctxEnv], trivial⟩ (hIO C.H s (List.prefix_refl _) m)
    (fun k1 s1 H1 hp1 _ => ?_)
  refine Big.specR_callKC (C := ctxH C H1) eqTm fW kParams [vv kFu, vv kD, vv eq1] (whnfE C fWB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW k1] (by decide) rfl (by decide) hc.w
    ⟨by simp +decide [Env.get, reParams, ctxEnv], by simp +decide [Env.get, reParams, ctxEnv], by simp, trivial⟩
    (hW H1 s1 hp1 k1) (fun tm s2 H2 hp2 _ => ?_)
  have hp12 : C.H <+: H2 := hp1.trans hp2
  have hok2 := ctxOK_H hok H2
  refine specR_callNIM (C := ctxH C H2) eqHh fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv eqTm]
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
  refine Knot.specR_tagIteV eqHh hh 3 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
  swap
  · rw [ite_eq_right (show ¬ (hh.tag == ETag.const) = true by simpa [ETag.const] using htg)]
    exact hretM hp12 (by simp +decide [Env.get, reParams, ctxEnv])
  rw [ite_eq_left (show (hh.tag == ETag.const) = true by simp [htg, ETag.const])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv eqHh) (Enc.idxW hh) (by decide) (by simp) ?_
  refine ILP.specR_viewIv (C := ctxH C H2) hh (by simp) (by simp +decide [Env.get, ctxEnv] <;> rfl)
    (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
  have h3 : v.tagN = 3 := by rw [htn, htg]; rfl
  obtain ⟨T', ust, rfl⟩ := UD.tagN_const h3
  dsimp only
  refine specR_loadI' eqTp (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW T') (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW T') [Enc.idxW ust] []) ?_
  refine specR_loadI' eqUs _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW ust) (by decide) (by simp +decide [sev]) rfl
    (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW T') (Enc.idxW ust) [] []) ?_
  refine specR_dropM ?_
  refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv eqUs) (Enc.idxW ust) (by decide) (by simp) ?_
  refine specR_lsviewPI (C := ctxH C H2) ust (by simp) (by simp +decide [Env.get, ctxEnv] <;> rfl)
    (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun vl Pl hvl _ hvll => ?_)
  refine specR_runBind (viewLs_run ust s2 vl hvl) ?_
  refine specR_callNIH (C := ctxH C H2) eqTa ExG.fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv eqTm]
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
  have htb' := htb
  obtain ⟨_, _, hnp, hctor, hnf, _⟩ := htb'
  have hcT' := hcT
  obtain ⟨⟨_, ⟨wl, hwl, hlps⟩, _⟩, _⟩ := hcT'
  simp only [IConstantInfo.toConstantVal] at hlps
  obtain ⟨ol, hwol, hblk⟩ := hlps
  refine UD.specR_heapLoadI' (C := ctxH C H3) eqTl (vv eqTa) oa _ hba.1 (by decide) (by simp; rfl) ?_
  refine specR_envLoadI (C := ctxH C H3) eqNp (.op .add [vv reO, .const 16]) (o + 2) _ (by decide)
    (by simp +decide [sev, Env.get, reParams, ctxEnv]; exact UD.ecell_add16 C o) hnp.1 ?_
  refine specR_envLoadI (C := ctxH C H3) eqLp (.op .add [vv reF, .const 16]) (qT + 2) _ (by decide)
    (by simp +decide [sev, Env.get, reParams, ctxEnv]; exact UD.ecell_add16 C qT)
    (by rw [show qT + 2 = qT + 1 + 1 by omega]; exact hwl) ?_
  refine specR_envLoadI (C := ctxH C H3) eqLn (vv eqLp) ol _ (by decide) (by simp [hwol]; rfl) hblk.1 ?_
  refine specR_atEntry fun t3 ht3 => ?_
  have htl := blk_small0 hok3 ht3.sr hba
  simp only [List.length_map] at htl
  have hnp2 := hnp.2
  have hlpl : cvT.levelParams.length < 2 ^ 61 := by
    have h1 := blkAt_len (show BlkAt C.EH ol (cvT.levelParams.map Enc.idxW) from hblk)
    have h2 := ht3.sr.env.1.len; have h3 := hok.envLay
    simp only [List.length_map] at h1; simp only [ctxH] at h2; omega
  have hvl' : vl.length < 2 ^ 61 := by simpa using hvll
  by_cases hT : T' = T
  swap
  · have hne : Enc.idxW T' ≠ Enc.idxW T := fun e => hT (Enc.idxW_inj e)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, reParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [ite_eq_right (by simp [hT])]
    exact hretM hp13 (by simp +decide [Env.get, reParams, ctxEnv])
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, reParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hT])
    (fun h => absurd rfl h) (fun _ => ?_)
  by_cases hA : targs.length = tbl.numParams
  swap
  · have hne : BitVec.ofNat 64 targs.length ≠ BitVec.ofNat 64 tbl.numParams := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    rw [ite_eq_right (by simp [hA])]
    exact hretM hp13 (by simp +decide [Env.get, reParams, ctxEnv])
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hA]) (fun h => absurd rfl h)
    (fun _ => ?_)
  by_cases hL : vl.length = cvT.levelParams.length
  swap
  · have hne : BitVec.ofNat 64 vl.length ≠ BitVec.ofNat 64 cvT.levelParams.length := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    rw [ite_eq_right (by simp [hL])]
    exact hretM hp13 (by simp +decide [Env.get, reParams, ctxEnv])
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hL]) (fun h => absurd rfl h)
    (fun _ => ?_)
  rw [ite_eq_left ⟨hT, hA, hL⟩]
  refine specR_callNIH (C := ctxH C H3) eqFz fFz fzParams [vv kFu, vv kD, vv reF, vv eqUs] Bfz
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, ecell C qT, Enc.idxW ust] (by decide) rfl (by decide) hc.fz
    ⟨by simp +decide [Env.get, reParams, ctxEnv], by simp +decide [Env.get, reParams, ctxEnv],
      by simp +decide [Env.get, reParams, ctxEnv], by simp, trivial⟩
    (PostB (ctxH C H3)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fzParams _ rfl hlk) (hFz H3 s3 ust hp13))
    (fun fz w s4 H4 hp4 hw => ?_)
  subst hw
  have hp14 : C.H <+: H4 := hp13.trans hp4
  have hok4 := ctxOK_H hok H4
  cases fz
  · refine specR_ifI _ 1 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    simp only [Bool.false_eq_true, ite_false]
    exact hretM hp14 (by simp +decide [Env.get, reParams, ctxEnv])
  refine specR_ifI _ 0 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
    (fun _ => ?_)
  simp only [ite_true]
  refine specR_envLoadI (C := ctxH C H4) eqNf (.op .add [vv reO, .const 32]) (o + 4) _ (by decide)
    (by simp +decide [sev, Env.get, reParams, ctxEnv]; exact UD.ecell_add32 C o) hnf.1 ?_
  have hnf2 := hnf.2
  simp only [etaFabArgsE, etaProjs]
  refine specR_callNIH (C := ctxH C H4) eqFa fEf efParams [vv rkT, vv rkM, vv eqTa, .const 0, vv eqNf] efBody
    [Enc.idxW T, Enc.idxW m, cellA C oa, BitVec.ofNat 64 0, BitVec.ofNat 64 tbl.numFields] (by decide) rfl (by decide)
    hc.ef ⟨by simp +decide [Env.get, reParams, ctxEnv], by simp +decide [Env.get, reParams, ctxEnv], by simp, rfl,
      by simp, trivial⟩
    (PostA (ctxH C H4)) (fun a w _ H5 => ∃ o5, w = cellA C o5 ∧ BlkAt H5 o5 (a.map Enc.idxW))
    (fun a w s' st ⟨H5, o5, hp, hw, hb, hsr⟩ => ⟨H5, hp, ⟨o5, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu efParams _ rfl hlk)
      (ef_spec ra C hok hc.ip hc.app hc.ef T m tbl.numFields (by omega) _ 0 H4 targs oa s4 hp14 (by omega)
        (Nat.zero_le _) (blkAt_mono hba hp4)))
    (fun fa w s5 H5 hp5 ⟨ofa, hw, hbfa⟩ => ?_)
  subst hw
  have hp15 : C.H <+: H5 := hp14.trans hp5
  have hok5 := ctxOK_H hok H5
  refine specR_envLoadI (C := ctxH C H5) eqTc (.op .add [vv reO, .const 24]) (o + 3) _ (by decide)
    (by simp +decide [sev, Env.get, reParams, ctxEnv]; exact ecell_add24 C o) hctor ?_
  refine ILP.callE_spec (C := ctxH C H5) eqHd fInternConst [lEn, lEus] [vv eqTc, vv eqUs] constBody
    [Enc.idxW tbl.ctor, Enc.idxW ust] (by decide) rfl (by decide) hc.ic ⟨by simp, by simp, trivial⟩
    (by exact const_body_spec ra (ctxH C H5) hok5 s5 _ _) (fun hd s6 => ?_)
  refine UD.specR_heapLoadI' (C := ctxH C H5) eqFl (vv eqFa) ofa _ hbfa.1 (by decide) (by simp; rfl) ?_
  refine specR_atEntry fun t5 ht5 => ?_
  have hfl := blk_small0 hok5 ht5.sr hbfa
  simp only [List.length_map] at hfl
  refine ILP.callE_spec (C := ctxH C H5) eqFab ExK.fMka [ExK.pF, ExK.pP, ExK.pI, ExK.pN]
    [vv eqHd, vv eqFa, .const 0, vv eqFl] ExK.mkaBody [Enc.idxW hd, cellA C ofa, BitVec.ofNat 64 0,
      BitVec.ofNat 64 fa.length] (by decide) rfl (by decide) hc.mka ⟨by simp, by simp, rfl, by simp, trivial⟩
    (by have h := (ExK.mkAppN_spec (σ := σ) ra (ctxH C H5) hok5 hc.mka hc.ia ofa fa hbfa (by omega) 0 (Nat.zero_le _) hd s6); simp only [List.drop_zero] at h; exact h)
    (fun fab s7 => ?_)
  refine specR_callNIH (C := ctxH C H5) eqFs fFab fbParams [vv kD, vv eqFab, vv rkM] Bfab
    [BitVec.ofNat 64 d, Enc.idxW fab, Enc.idxW m] (by decide) rfl (by decide) hc.fab
    ⟨by simp +decide [Env.get, reParams, ctxEnv], by simp, by simp +decide [Env.get, reParams, ctxEnv], trivial⟩
    (PostB (ctxH C H5)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fbParams _ rfl hlk) (hFab H5 s7 fab m hp15))
    (fun fs w s8 H6 hp6 hw => ?_)
  subst hw
  have hp16 : C.H <+: H6 := hp15.trans hp6
  cases fs
  · refine specR_ifI _ 1 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    simp only [Bool.false_eq_true, ite_false]
    exact hretM hp16 (by simp +decide [Env.get, reParams, ctxEnv])
  refine specR_ifI _ 0 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
    (fun _ => ?_)
  simp only [ite_true]
  exact specR_returnI _ (Enc.idxW fab) (by simp) (fun t ht => ⟨H6, hp16, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
