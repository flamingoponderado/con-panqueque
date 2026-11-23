import ConPanqueque.T.Core.StuckIrrel
import ConPanqueque.T.Core.EtaCert
import ConPanqueque.T.Core.ProjLit
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `defeqStuck`: the stuck comparison

Both sides are viewed first; the pair's arm is chosen on the two tags. Each arm is its own lemma (`dk_*`), over
any environment holding the parameters and the rows' cells.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def dkA := ofString "dks_dka"
def dkB := ofString "dks_dkb"
def dkPa := ofString "dks_dkpa"
def dkGa := ofString "dks_dkga"
def dkLa := ofString "dks_dkla"
def dkPb := ofString "dks_dkpb"
def dkGb := ofString "dks_dkgb"
def dkLb := ofString "dks_dklb"
def dkR := ofString "dks_dkr"
def dkT := ofString "dks_dkt"
def dkBb := ofString "dks_dkbb"
def dkE := ofString "dks_dke"
def fDk := ofString "defeqStuck"

@[simp] theorem dks_dkA_ne_dkB : dkA ≠ dkB := by decide
@[simp] theorem dks_dkA_ne_dkPa : dkA ≠ dkPa := by decide
@[simp] theorem dks_dkA_ne_dkGa : dkA ≠ dkGa := by decide
@[simp] theorem dks_dkA_ne_dkLa : dkA ≠ dkLa := by decide
@[simp] theorem dks_dkA_ne_dkPb : dkA ≠ dkPb := by decide
@[simp] theorem dks_dkA_ne_dkGb : dkA ≠ dkGb := by decide
@[simp] theorem dks_dkA_ne_dkLb : dkA ≠ dkLb := by decide
@[simp] theorem dks_dkA_ne_dkR : dkA ≠ dkR := by decide
@[simp] theorem dks_dkA_ne_dkT : dkA ≠ dkT := by decide
@[simp] theorem dks_dkA_ne_dkBb : dkA ≠ dkBb := by decide
@[simp] theorem dks_dkA_ne_dkE : dkA ≠ dkE := by decide
@[simp] theorem dks_dkA_ne_lFl : dkA ≠ lFl := by decide
@[simp] theorem dks_lFl_ne_dkA : lFl ≠ dkA := by decide
@[simp] theorem dks_dkA_ne_lDh : dkA ≠ lDh := by decide
@[simp] theorem dks_lDh_ne_dkA : lDh ≠ dkA := by decide
@[simp] theorem dks_dkA_ne_lDt : dkA ≠ lDt := by decide
@[simp] theorem dks_lDt_ne_dkA : lDt ≠ dkA := by decide
@[simp] theorem dks_dkA_ne_lDg : dkA ≠ lDg := by decide
@[simp] theorem dks_lDg_ne_dkA : lDg ≠ dkA := by decide
@[simp] theorem dks_dkA_ne_lDi : dkA ≠ lDi := by decide
@[simp] theorem dks_lDi_ne_dkA : lDi ≠ dkA := by decide
@[simp] theorem dks_dkA_ne_lRp : dkA ≠ lRp := by decide
@[simp] theorem dks_lRp_ne_dkA : lRp ≠ dkA := by decide
@[simp] theorem dks_dkA_ne_lRn : dkA ≠ lRn := by decide
@[simp] theorem dks_lRn_ne_dkA : lRn ≠ dkA := by decide
@[simp] theorem dks_dkA_ne_lFle : dkA ≠ lFle := by decide
@[simp] theorem dks_lFle_ne_dkA : lFle ≠ dkA := by decide
@[simp] theorem dks_dkA_ne_lKb : dkA ≠ lKb := by decide
@[simp] theorem dks_lKb_ne_dkA : lKb ≠ dkA := by decide
@[simp] theorem dks_dkA_ne_lDir : dkA ≠ lDir := by decide
@[simp] theorem dks_lDir_ne_dkA : lDir ≠ dkA := by decide
@[simp] theorem dks_dkA_ne_lFln : dkA ≠ lFln := by decide
@[simp] theorem dks_lFln_ne_dkA : lFln ≠ dkA := by decide
@[simp] theorem dks_dkA_ne_lFll : dkA ≠ lFll := by decide
@[simp] theorem dks_lFll_ne_dkA : lFll ≠ dkA := by decide
@[simp] theorem dks_dkA_ne_lFls : dkA ≠ lFls := by decide
@[simp] theorem dks_lFls_ne_dkA : lFls ≠ dkA := by decide
@[simp] theorem dks_dkA_ne_kFu : dkA ≠ kFu := by decide
@[simp] theorem dks_kFu_ne_dkA : kFu ≠ dkA := by decide
@[simp] theorem dks_dkA_ne_kD : dkA ≠ kD := by decide
@[simp] theorem dks_kD_ne_dkA : kD ≠ dkA := by decide
@[simp] theorem dks_dkB_ne_dkA : dkB ≠ dkA := by decide
@[simp] theorem dks_dkB_ne_dkPa : dkB ≠ dkPa := by decide
@[simp] theorem dks_dkB_ne_dkGa : dkB ≠ dkGa := by decide
@[simp] theorem dks_dkB_ne_dkLa : dkB ≠ dkLa := by decide
@[simp] theorem dks_dkB_ne_dkPb : dkB ≠ dkPb := by decide
@[simp] theorem dks_dkB_ne_dkGb : dkB ≠ dkGb := by decide
@[simp] theorem dks_dkB_ne_dkLb : dkB ≠ dkLb := by decide
@[simp] theorem dks_dkB_ne_dkR : dkB ≠ dkR := by decide
@[simp] theorem dks_dkB_ne_dkT : dkB ≠ dkT := by decide
@[simp] theorem dks_dkB_ne_dkBb : dkB ≠ dkBb := by decide
@[simp] theorem dks_dkB_ne_dkE : dkB ≠ dkE := by decide
@[simp] theorem dks_dkB_ne_lFl : dkB ≠ lFl := by decide
@[simp] theorem dks_lFl_ne_dkB : lFl ≠ dkB := by decide
@[simp] theorem dks_dkB_ne_lDh : dkB ≠ lDh := by decide
@[simp] theorem dks_lDh_ne_dkB : lDh ≠ dkB := by decide
@[simp] theorem dks_dkB_ne_lDt : dkB ≠ lDt := by decide
@[simp] theorem dks_lDt_ne_dkB : lDt ≠ dkB := by decide
@[simp] theorem dks_dkB_ne_lDg : dkB ≠ lDg := by decide
@[simp] theorem dks_lDg_ne_dkB : lDg ≠ dkB := by decide
@[simp] theorem dks_dkB_ne_lDi : dkB ≠ lDi := by decide
@[simp] theorem dks_lDi_ne_dkB : lDi ≠ dkB := by decide
@[simp] theorem dks_dkB_ne_lRp : dkB ≠ lRp := by decide
@[simp] theorem dks_lRp_ne_dkB : lRp ≠ dkB := by decide
@[simp] theorem dks_dkB_ne_lRn : dkB ≠ lRn := by decide
@[simp] theorem dks_lRn_ne_dkB : lRn ≠ dkB := by decide
@[simp] theorem dks_dkB_ne_lFle : dkB ≠ lFle := by decide
@[simp] theorem dks_lFle_ne_dkB : lFle ≠ dkB := by decide
@[simp] theorem dks_dkB_ne_lKb : dkB ≠ lKb := by decide
@[simp] theorem dks_lKb_ne_dkB : lKb ≠ dkB := by decide
@[simp] theorem dks_dkB_ne_lDir : dkB ≠ lDir := by decide
@[simp] theorem dks_lDir_ne_dkB : lDir ≠ dkB := by decide
@[simp] theorem dks_dkB_ne_lFln : dkB ≠ lFln := by decide
@[simp] theorem dks_lFln_ne_dkB : lFln ≠ dkB := by decide
@[simp] theorem dks_dkB_ne_lFll : dkB ≠ lFll := by decide
@[simp] theorem dks_lFll_ne_dkB : lFll ≠ dkB := by decide
@[simp] theorem dks_dkB_ne_lFls : dkB ≠ lFls := by decide
@[simp] theorem dks_lFls_ne_dkB : lFls ≠ dkB := by decide
@[simp] theorem dks_dkB_ne_kFu : dkB ≠ kFu := by decide
@[simp] theorem dks_kFu_ne_dkB : kFu ≠ dkB := by decide
@[simp] theorem dks_dkB_ne_kD : dkB ≠ kD := by decide
@[simp] theorem dks_kD_ne_dkB : kD ≠ dkB := by decide
@[simp] theorem dks_dkPa_ne_dkA : dkPa ≠ dkA := by decide
@[simp] theorem dks_dkPa_ne_dkB : dkPa ≠ dkB := by decide
@[simp] theorem dks_dkPa_ne_dkGa : dkPa ≠ dkGa := by decide
@[simp] theorem dks_dkPa_ne_dkLa : dkPa ≠ dkLa := by decide
@[simp] theorem dks_dkPa_ne_dkPb : dkPa ≠ dkPb := by decide
@[simp] theorem dks_dkPa_ne_dkGb : dkPa ≠ dkGb := by decide
@[simp] theorem dks_dkPa_ne_dkLb : dkPa ≠ dkLb := by decide
@[simp] theorem dks_dkPa_ne_dkR : dkPa ≠ dkR := by decide
@[simp] theorem dks_dkPa_ne_dkT : dkPa ≠ dkT := by decide
@[simp] theorem dks_dkPa_ne_dkBb : dkPa ≠ dkBb := by decide
@[simp] theorem dks_dkPa_ne_dkE : dkPa ≠ dkE := by decide
@[simp] theorem dks_dkPa_ne_lFl : dkPa ≠ lFl := by decide
@[simp] theorem dks_lFl_ne_dkPa : lFl ≠ dkPa := by decide
@[simp] theorem dks_dkPa_ne_lDh : dkPa ≠ lDh := by decide
@[simp] theorem dks_lDh_ne_dkPa : lDh ≠ dkPa := by decide
@[simp] theorem dks_dkPa_ne_lDt : dkPa ≠ lDt := by decide
@[simp] theorem dks_lDt_ne_dkPa : lDt ≠ dkPa := by decide
@[simp] theorem dks_dkPa_ne_lDg : dkPa ≠ lDg := by decide
@[simp] theorem dks_lDg_ne_dkPa : lDg ≠ dkPa := by decide
@[simp] theorem dks_dkPa_ne_lDi : dkPa ≠ lDi := by decide
@[simp] theorem dks_lDi_ne_dkPa : lDi ≠ dkPa := by decide
@[simp] theorem dks_dkPa_ne_lRp : dkPa ≠ lRp := by decide
@[simp] theorem dks_lRp_ne_dkPa : lRp ≠ dkPa := by decide
@[simp] theorem dks_dkPa_ne_lRn : dkPa ≠ lRn := by decide
@[simp] theorem dks_lRn_ne_dkPa : lRn ≠ dkPa := by decide
@[simp] theorem dks_dkPa_ne_lFle : dkPa ≠ lFle := by decide
@[simp] theorem dks_lFle_ne_dkPa : lFle ≠ dkPa := by decide
@[simp] theorem dks_dkPa_ne_lKb : dkPa ≠ lKb := by decide
@[simp] theorem dks_lKb_ne_dkPa : lKb ≠ dkPa := by decide
@[simp] theorem dks_dkPa_ne_lDir : dkPa ≠ lDir := by decide
@[simp] theorem dks_lDir_ne_dkPa : lDir ≠ dkPa := by decide
@[simp] theorem dks_dkPa_ne_lFln : dkPa ≠ lFln := by decide
@[simp] theorem dks_lFln_ne_dkPa : lFln ≠ dkPa := by decide
@[simp] theorem dks_dkPa_ne_lFll : dkPa ≠ lFll := by decide
@[simp] theorem dks_lFll_ne_dkPa : lFll ≠ dkPa := by decide
@[simp] theorem dks_dkPa_ne_lFls : dkPa ≠ lFls := by decide
@[simp] theorem dks_lFls_ne_dkPa : lFls ≠ dkPa := by decide
@[simp] theorem dks_dkPa_ne_kFu : dkPa ≠ kFu := by decide
@[simp] theorem dks_kFu_ne_dkPa : kFu ≠ dkPa := by decide
@[simp] theorem dks_dkPa_ne_kD : dkPa ≠ kD := by decide
@[simp] theorem dks_kD_ne_dkPa : kD ≠ dkPa := by decide
@[simp] theorem dks_dkGa_ne_dkA : dkGa ≠ dkA := by decide
@[simp] theorem dks_dkGa_ne_dkB : dkGa ≠ dkB := by decide
@[simp] theorem dks_dkGa_ne_dkPa : dkGa ≠ dkPa := by decide
@[simp] theorem dks_dkGa_ne_dkLa : dkGa ≠ dkLa := by decide
@[simp] theorem dks_dkGa_ne_dkPb : dkGa ≠ dkPb := by decide
@[simp] theorem dks_dkGa_ne_dkGb : dkGa ≠ dkGb := by decide
@[simp] theorem dks_dkGa_ne_dkLb : dkGa ≠ dkLb := by decide
@[simp] theorem dks_dkGa_ne_dkR : dkGa ≠ dkR := by decide
@[simp] theorem dks_dkGa_ne_dkT : dkGa ≠ dkT := by decide
@[simp] theorem dks_dkGa_ne_dkBb : dkGa ≠ dkBb := by decide
@[simp] theorem dks_dkGa_ne_dkE : dkGa ≠ dkE := by decide
@[simp] theorem dks_dkGa_ne_lFl : dkGa ≠ lFl := by decide
@[simp] theorem dks_lFl_ne_dkGa : lFl ≠ dkGa := by decide
@[simp] theorem dks_dkGa_ne_lDh : dkGa ≠ lDh := by decide
@[simp] theorem dks_lDh_ne_dkGa : lDh ≠ dkGa := by decide
@[simp] theorem dks_dkGa_ne_lDt : dkGa ≠ lDt := by decide
@[simp] theorem dks_lDt_ne_dkGa : lDt ≠ dkGa := by decide
@[simp] theorem dks_dkGa_ne_lDg : dkGa ≠ lDg := by decide
@[simp] theorem dks_lDg_ne_dkGa : lDg ≠ dkGa := by decide
@[simp] theorem dks_dkGa_ne_lDi : dkGa ≠ lDi := by decide
@[simp] theorem dks_lDi_ne_dkGa : lDi ≠ dkGa := by decide
@[simp] theorem dks_dkGa_ne_lRp : dkGa ≠ lRp := by decide
@[simp] theorem dks_lRp_ne_dkGa : lRp ≠ dkGa := by decide
@[simp] theorem dks_dkGa_ne_lRn : dkGa ≠ lRn := by decide
@[simp] theorem dks_lRn_ne_dkGa : lRn ≠ dkGa := by decide
@[simp] theorem dks_dkGa_ne_lFle : dkGa ≠ lFle := by decide
@[simp] theorem dks_lFle_ne_dkGa : lFle ≠ dkGa := by decide
@[simp] theorem dks_dkGa_ne_lKb : dkGa ≠ lKb := by decide
@[simp] theorem dks_lKb_ne_dkGa : lKb ≠ dkGa := by decide
@[simp] theorem dks_dkGa_ne_lDir : dkGa ≠ lDir := by decide
@[simp] theorem dks_lDir_ne_dkGa : lDir ≠ dkGa := by decide
@[simp] theorem dks_dkGa_ne_lFln : dkGa ≠ lFln := by decide
@[simp] theorem dks_lFln_ne_dkGa : lFln ≠ dkGa := by decide
@[simp] theorem dks_dkGa_ne_lFll : dkGa ≠ lFll := by decide
@[simp] theorem dks_lFll_ne_dkGa : lFll ≠ dkGa := by decide
@[simp] theorem dks_dkGa_ne_lFls : dkGa ≠ lFls := by decide
@[simp] theorem dks_lFls_ne_dkGa : lFls ≠ dkGa := by decide
@[simp] theorem dks_dkGa_ne_kFu : dkGa ≠ kFu := by decide
@[simp] theorem dks_kFu_ne_dkGa : kFu ≠ dkGa := by decide
@[simp] theorem dks_dkGa_ne_kD : dkGa ≠ kD := by decide
@[simp] theorem dks_kD_ne_dkGa : kD ≠ dkGa := by decide
@[simp] theorem dks_dkLa_ne_dkA : dkLa ≠ dkA := by decide
@[simp] theorem dks_dkLa_ne_dkB : dkLa ≠ dkB := by decide
@[simp] theorem dks_dkLa_ne_dkPa : dkLa ≠ dkPa := by decide
@[simp] theorem dks_dkLa_ne_dkGa : dkLa ≠ dkGa := by decide
@[simp] theorem dks_dkLa_ne_dkPb : dkLa ≠ dkPb := by decide
@[simp] theorem dks_dkLa_ne_dkGb : dkLa ≠ dkGb := by decide
@[simp] theorem dks_dkLa_ne_dkLb : dkLa ≠ dkLb := by decide
@[simp] theorem dks_dkLa_ne_dkR : dkLa ≠ dkR := by decide
@[simp] theorem dks_dkLa_ne_dkT : dkLa ≠ dkT := by decide
@[simp] theorem dks_dkLa_ne_dkBb : dkLa ≠ dkBb := by decide
@[simp] theorem dks_dkLa_ne_dkE : dkLa ≠ dkE := by decide
@[simp] theorem dks_dkLa_ne_lFl : dkLa ≠ lFl := by decide
@[simp] theorem dks_lFl_ne_dkLa : lFl ≠ dkLa := by decide
@[simp] theorem dks_dkLa_ne_lDh : dkLa ≠ lDh := by decide
@[simp] theorem dks_lDh_ne_dkLa : lDh ≠ dkLa := by decide
@[simp] theorem dks_dkLa_ne_lDt : dkLa ≠ lDt := by decide
@[simp] theorem dks_lDt_ne_dkLa : lDt ≠ dkLa := by decide
@[simp] theorem dks_dkLa_ne_lDg : dkLa ≠ lDg := by decide
@[simp] theorem dks_lDg_ne_dkLa : lDg ≠ dkLa := by decide
@[simp] theorem dks_dkLa_ne_lDi : dkLa ≠ lDi := by decide
@[simp] theorem dks_lDi_ne_dkLa : lDi ≠ dkLa := by decide
@[simp] theorem dks_dkLa_ne_lRp : dkLa ≠ lRp := by decide
@[simp] theorem dks_lRp_ne_dkLa : lRp ≠ dkLa := by decide
@[simp] theorem dks_dkLa_ne_lRn : dkLa ≠ lRn := by decide
@[simp] theorem dks_lRn_ne_dkLa : lRn ≠ dkLa := by decide
@[simp] theorem dks_dkLa_ne_lFle : dkLa ≠ lFle := by decide
@[simp] theorem dks_lFle_ne_dkLa : lFle ≠ dkLa := by decide
@[simp] theorem dks_dkLa_ne_lKb : dkLa ≠ lKb := by decide
@[simp] theorem dks_lKb_ne_dkLa : lKb ≠ dkLa := by decide
@[simp] theorem dks_dkLa_ne_lDir : dkLa ≠ lDir := by decide
@[simp] theorem dks_lDir_ne_dkLa : lDir ≠ dkLa := by decide
@[simp] theorem dks_dkLa_ne_lFln : dkLa ≠ lFln := by decide
@[simp] theorem dks_lFln_ne_dkLa : lFln ≠ dkLa := by decide
@[simp] theorem dks_dkLa_ne_lFll : dkLa ≠ lFll := by decide
@[simp] theorem dks_lFll_ne_dkLa : lFll ≠ dkLa := by decide
@[simp] theorem dks_dkLa_ne_lFls : dkLa ≠ lFls := by decide
@[simp] theorem dks_lFls_ne_dkLa : lFls ≠ dkLa := by decide
@[simp] theorem dks_dkLa_ne_kFu : dkLa ≠ kFu := by decide
@[simp] theorem dks_kFu_ne_dkLa : kFu ≠ dkLa := by decide
@[simp] theorem dks_dkLa_ne_kD : dkLa ≠ kD := by decide
@[simp] theorem dks_kD_ne_dkLa : kD ≠ dkLa := by decide
@[simp] theorem dks_dkPb_ne_dkA : dkPb ≠ dkA := by decide
@[simp] theorem dks_dkPb_ne_dkB : dkPb ≠ dkB := by decide
@[simp] theorem dks_dkPb_ne_dkPa : dkPb ≠ dkPa := by decide
@[simp] theorem dks_dkPb_ne_dkGa : dkPb ≠ dkGa := by decide
@[simp] theorem dks_dkPb_ne_dkLa : dkPb ≠ dkLa := by decide
@[simp] theorem dks_dkPb_ne_dkGb : dkPb ≠ dkGb := by decide
@[simp] theorem dks_dkPb_ne_dkLb : dkPb ≠ dkLb := by decide
@[simp] theorem dks_dkPb_ne_dkR : dkPb ≠ dkR := by decide
@[simp] theorem dks_dkPb_ne_dkT : dkPb ≠ dkT := by decide
@[simp] theorem dks_dkPb_ne_dkBb : dkPb ≠ dkBb := by decide
@[simp] theorem dks_dkPb_ne_dkE : dkPb ≠ dkE := by decide
@[simp] theorem dks_dkPb_ne_lFl : dkPb ≠ lFl := by decide
@[simp] theorem dks_lFl_ne_dkPb : lFl ≠ dkPb := by decide
@[simp] theorem dks_dkPb_ne_lDh : dkPb ≠ lDh := by decide
@[simp] theorem dks_lDh_ne_dkPb : lDh ≠ dkPb := by decide
@[simp] theorem dks_dkPb_ne_lDt : dkPb ≠ lDt := by decide
@[simp] theorem dks_lDt_ne_dkPb : lDt ≠ dkPb := by decide
@[simp] theorem dks_dkPb_ne_lDg : dkPb ≠ lDg := by decide
@[simp] theorem dks_lDg_ne_dkPb : lDg ≠ dkPb := by decide
@[simp] theorem dks_dkPb_ne_lDi : dkPb ≠ lDi := by decide
@[simp] theorem dks_lDi_ne_dkPb : lDi ≠ dkPb := by decide
@[simp] theorem dks_dkPb_ne_lRp : dkPb ≠ lRp := by decide
@[simp] theorem dks_lRp_ne_dkPb : lRp ≠ dkPb := by decide
@[simp] theorem dks_dkPb_ne_lRn : dkPb ≠ lRn := by decide
@[simp] theorem dks_lRn_ne_dkPb : lRn ≠ dkPb := by decide
@[simp] theorem dks_dkPb_ne_lFle : dkPb ≠ lFle := by decide
@[simp] theorem dks_lFle_ne_dkPb : lFle ≠ dkPb := by decide
@[simp] theorem dks_dkPb_ne_lKb : dkPb ≠ lKb := by decide
@[simp] theorem dks_lKb_ne_dkPb : lKb ≠ dkPb := by decide
@[simp] theorem dks_dkPb_ne_lDir : dkPb ≠ lDir := by decide
@[simp] theorem dks_lDir_ne_dkPb : lDir ≠ dkPb := by decide
@[simp] theorem dks_dkPb_ne_lFln : dkPb ≠ lFln := by decide
@[simp] theorem dks_lFln_ne_dkPb : lFln ≠ dkPb := by decide
@[simp] theorem dks_dkPb_ne_lFll : dkPb ≠ lFll := by decide
@[simp] theorem dks_lFll_ne_dkPb : lFll ≠ dkPb := by decide
@[simp] theorem dks_dkPb_ne_lFls : dkPb ≠ lFls := by decide
@[simp] theorem dks_lFls_ne_dkPb : lFls ≠ dkPb := by decide
@[simp] theorem dks_dkPb_ne_kFu : dkPb ≠ kFu := by decide
@[simp] theorem dks_kFu_ne_dkPb : kFu ≠ dkPb := by decide
@[simp] theorem dks_dkPb_ne_kD : dkPb ≠ kD := by decide
@[simp] theorem dks_kD_ne_dkPb : kD ≠ dkPb := by decide
@[simp] theorem dks_dkGb_ne_dkA : dkGb ≠ dkA := by decide
@[simp] theorem dks_dkGb_ne_dkB : dkGb ≠ dkB := by decide
@[simp] theorem dks_dkGb_ne_dkPa : dkGb ≠ dkPa := by decide
@[simp] theorem dks_dkGb_ne_dkGa : dkGb ≠ dkGa := by decide
@[simp] theorem dks_dkGb_ne_dkLa : dkGb ≠ dkLa := by decide
@[simp] theorem dks_dkGb_ne_dkPb : dkGb ≠ dkPb := by decide
@[simp] theorem dks_dkGb_ne_dkLb : dkGb ≠ dkLb := by decide
@[simp] theorem dks_dkGb_ne_dkR : dkGb ≠ dkR := by decide
@[simp] theorem dks_dkGb_ne_dkT : dkGb ≠ dkT := by decide
@[simp] theorem dks_dkGb_ne_dkBb : dkGb ≠ dkBb := by decide
@[simp] theorem dks_dkGb_ne_dkE : dkGb ≠ dkE := by decide
@[simp] theorem dks_dkGb_ne_lFl : dkGb ≠ lFl := by decide
@[simp] theorem dks_lFl_ne_dkGb : lFl ≠ dkGb := by decide
@[simp] theorem dks_dkGb_ne_lDh : dkGb ≠ lDh := by decide
@[simp] theorem dks_lDh_ne_dkGb : lDh ≠ dkGb := by decide
@[simp] theorem dks_dkGb_ne_lDt : dkGb ≠ lDt := by decide
@[simp] theorem dks_lDt_ne_dkGb : lDt ≠ dkGb := by decide
@[simp] theorem dks_dkGb_ne_lDg : dkGb ≠ lDg := by decide
@[simp] theorem dks_lDg_ne_dkGb : lDg ≠ dkGb := by decide
@[simp] theorem dks_dkGb_ne_lDi : dkGb ≠ lDi := by decide
@[simp] theorem dks_lDi_ne_dkGb : lDi ≠ dkGb := by decide
@[simp] theorem dks_dkGb_ne_lRp : dkGb ≠ lRp := by decide
@[simp] theorem dks_lRp_ne_dkGb : lRp ≠ dkGb := by decide
@[simp] theorem dks_dkGb_ne_lRn : dkGb ≠ lRn := by decide
@[simp] theorem dks_lRn_ne_dkGb : lRn ≠ dkGb := by decide
@[simp] theorem dks_dkGb_ne_lFle : dkGb ≠ lFle := by decide
@[simp] theorem dks_lFle_ne_dkGb : lFle ≠ dkGb := by decide
@[simp] theorem dks_dkGb_ne_lKb : dkGb ≠ lKb := by decide
@[simp] theorem dks_lKb_ne_dkGb : lKb ≠ dkGb := by decide
@[simp] theorem dks_dkGb_ne_lDir : dkGb ≠ lDir := by decide
@[simp] theorem dks_lDir_ne_dkGb : lDir ≠ dkGb := by decide
@[simp] theorem dks_dkGb_ne_lFln : dkGb ≠ lFln := by decide
@[simp] theorem dks_lFln_ne_dkGb : lFln ≠ dkGb := by decide
@[simp] theorem dks_dkGb_ne_lFll : dkGb ≠ lFll := by decide
@[simp] theorem dks_lFll_ne_dkGb : lFll ≠ dkGb := by decide
@[simp] theorem dks_dkGb_ne_lFls : dkGb ≠ lFls := by decide
@[simp] theorem dks_lFls_ne_dkGb : lFls ≠ dkGb := by decide
@[simp] theorem dks_dkGb_ne_kFu : dkGb ≠ kFu := by decide
@[simp] theorem dks_kFu_ne_dkGb : kFu ≠ dkGb := by decide
@[simp] theorem dks_dkGb_ne_kD : dkGb ≠ kD := by decide
@[simp] theorem dks_kD_ne_dkGb : kD ≠ dkGb := by decide
@[simp] theorem dks_dkLb_ne_dkA : dkLb ≠ dkA := by decide
@[simp] theorem dks_dkLb_ne_dkB : dkLb ≠ dkB := by decide
@[simp] theorem dks_dkLb_ne_dkPa : dkLb ≠ dkPa := by decide
@[simp] theorem dks_dkLb_ne_dkGa : dkLb ≠ dkGa := by decide
@[simp] theorem dks_dkLb_ne_dkLa : dkLb ≠ dkLa := by decide
@[simp] theorem dks_dkLb_ne_dkPb : dkLb ≠ dkPb := by decide
@[simp] theorem dks_dkLb_ne_dkGb : dkLb ≠ dkGb := by decide
@[simp] theorem dks_dkLb_ne_dkR : dkLb ≠ dkR := by decide
@[simp] theorem dks_dkLb_ne_dkT : dkLb ≠ dkT := by decide
@[simp] theorem dks_dkLb_ne_dkBb : dkLb ≠ dkBb := by decide
@[simp] theorem dks_dkLb_ne_dkE : dkLb ≠ dkE := by decide
@[simp] theorem dks_dkLb_ne_lFl : dkLb ≠ lFl := by decide
@[simp] theorem dks_lFl_ne_dkLb : lFl ≠ dkLb := by decide
@[simp] theorem dks_dkLb_ne_lDh : dkLb ≠ lDh := by decide
@[simp] theorem dks_lDh_ne_dkLb : lDh ≠ dkLb := by decide
@[simp] theorem dks_dkLb_ne_lDt : dkLb ≠ lDt := by decide
@[simp] theorem dks_lDt_ne_dkLb : lDt ≠ dkLb := by decide
@[simp] theorem dks_dkLb_ne_lDg : dkLb ≠ lDg := by decide
@[simp] theorem dks_lDg_ne_dkLb : lDg ≠ dkLb := by decide
@[simp] theorem dks_dkLb_ne_lDi : dkLb ≠ lDi := by decide
@[simp] theorem dks_lDi_ne_dkLb : lDi ≠ dkLb := by decide
@[simp] theorem dks_dkLb_ne_lRp : dkLb ≠ lRp := by decide
@[simp] theorem dks_lRp_ne_dkLb : lRp ≠ dkLb := by decide
@[simp] theorem dks_dkLb_ne_lRn : dkLb ≠ lRn := by decide
@[simp] theorem dks_lRn_ne_dkLb : lRn ≠ dkLb := by decide
@[simp] theorem dks_dkLb_ne_lFle : dkLb ≠ lFle := by decide
@[simp] theorem dks_lFle_ne_dkLb : lFle ≠ dkLb := by decide
@[simp] theorem dks_dkLb_ne_lKb : dkLb ≠ lKb := by decide
@[simp] theorem dks_lKb_ne_dkLb : lKb ≠ dkLb := by decide
@[simp] theorem dks_dkLb_ne_lDir : dkLb ≠ lDir := by decide
@[simp] theorem dks_lDir_ne_dkLb : lDir ≠ dkLb := by decide
@[simp] theorem dks_dkLb_ne_lFln : dkLb ≠ lFln := by decide
@[simp] theorem dks_lFln_ne_dkLb : lFln ≠ dkLb := by decide
@[simp] theorem dks_dkLb_ne_lFll : dkLb ≠ lFll := by decide
@[simp] theorem dks_lFll_ne_dkLb : lFll ≠ dkLb := by decide
@[simp] theorem dks_dkLb_ne_lFls : dkLb ≠ lFls := by decide
@[simp] theorem dks_lFls_ne_dkLb : lFls ≠ dkLb := by decide
@[simp] theorem dks_dkLb_ne_kFu : dkLb ≠ kFu := by decide
@[simp] theorem dks_kFu_ne_dkLb : kFu ≠ dkLb := by decide
@[simp] theorem dks_dkLb_ne_kD : dkLb ≠ kD := by decide
@[simp] theorem dks_kD_ne_dkLb : kD ≠ dkLb := by decide
@[simp] theorem dks_dkR_ne_dkA : dkR ≠ dkA := by decide
@[simp] theorem dks_dkR_ne_dkB : dkR ≠ dkB := by decide
@[simp] theorem dks_dkR_ne_dkPa : dkR ≠ dkPa := by decide
@[simp] theorem dks_dkR_ne_dkGa : dkR ≠ dkGa := by decide
@[simp] theorem dks_dkR_ne_dkLa : dkR ≠ dkLa := by decide
@[simp] theorem dks_dkR_ne_dkPb : dkR ≠ dkPb := by decide
@[simp] theorem dks_dkR_ne_dkGb : dkR ≠ dkGb := by decide
@[simp] theorem dks_dkR_ne_dkLb : dkR ≠ dkLb := by decide
@[simp] theorem dks_dkR_ne_dkT : dkR ≠ dkT := by decide
@[simp] theorem dks_dkR_ne_dkBb : dkR ≠ dkBb := by decide
@[simp] theorem dks_dkR_ne_dkE : dkR ≠ dkE := by decide
@[simp] theorem dks_dkR_ne_lFl : dkR ≠ lFl := by decide
@[simp] theorem dks_lFl_ne_dkR : lFl ≠ dkR := by decide
@[simp] theorem dks_dkR_ne_lDh : dkR ≠ lDh := by decide
@[simp] theorem dks_lDh_ne_dkR : lDh ≠ dkR := by decide
@[simp] theorem dks_dkR_ne_lDt : dkR ≠ lDt := by decide
@[simp] theorem dks_lDt_ne_dkR : lDt ≠ dkR := by decide
@[simp] theorem dks_dkR_ne_lDg : dkR ≠ lDg := by decide
@[simp] theorem dks_lDg_ne_dkR : lDg ≠ dkR := by decide
@[simp] theorem dks_dkR_ne_lDi : dkR ≠ lDi := by decide
@[simp] theorem dks_lDi_ne_dkR : lDi ≠ dkR := by decide
@[simp] theorem dks_dkR_ne_lRp : dkR ≠ lRp := by decide
@[simp] theorem dks_lRp_ne_dkR : lRp ≠ dkR := by decide
@[simp] theorem dks_dkR_ne_lRn : dkR ≠ lRn := by decide
@[simp] theorem dks_lRn_ne_dkR : lRn ≠ dkR := by decide
@[simp] theorem dks_dkR_ne_lFle : dkR ≠ lFle := by decide
@[simp] theorem dks_lFle_ne_dkR : lFle ≠ dkR := by decide
@[simp] theorem dks_dkR_ne_lKb : dkR ≠ lKb := by decide
@[simp] theorem dks_lKb_ne_dkR : lKb ≠ dkR := by decide
@[simp] theorem dks_dkR_ne_lDir : dkR ≠ lDir := by decide
@[simp] theorem dks_lDir_ne_dkR : lDir ≠ dkR := by decide
@[simp] theorem dks_dkR_ne_lFln : dkR ≠ lFln := by decide
@[simp] theorem dks_lFln_ne_dkR : lFln ≠ dkR := by decide
@[simp] theorem dks_dkR_ne_lFll : dkR ≠ lFll := by decide
@[simp] theorem dks_lFll_ne_dkR : lFll ≠ dkR := by decide
@[simp] theorem dks_dkR_ne_lFls : dkR ≠ lFls := by decide
@[simp] theorem dks_lFls_ne_dkR : lFls ≠ dkR := by decide
@[simp] theorem dks_dkR_ne_kFu : dkR ≠ kFu := by decide
@[simp] theorem dks_kFu_ne_dkR : kFu ≠ dkR := by decide
@[simp] theorem dks_dkR_ne_kD : dkR ≠ kD := by decide
@[simp] theorem dks_kD_ne_dkR : kD ≠ dkR := by decide
@[simp] theorem dks_dkT_ne_dkA : dkT ≠ dkA := by decide
@[simp] theorem dks_dkT_ne_dkB : dkT ≠ dkB := by decide
@[simp] theorem dks_dkT_ne_dkPa : dkT ≠ dkPa := by decide
@[simp] theorem dks_dkT_ne_dkGa : dkT ≠ dkGa := by decide
@[simp] theorem dks_dkT_ne_dkLa : dkT ≠ dkLa := by decide
@[simp] theorem dks_dkT_ne_dkPb : dkT ≠ dkPb := by decide
@[simp] theorem dks_dkT_ne_dkGb : dkT ≠ dkGb := by decide
@[simp] theorem dks_dkT_ne_dkLb : dkT ≠ dkLb := by decide
@[simp] theorem dks_dkT_ne_dkR : dkT ≠ dkR := by decide
@[simp] theorem dks_dkT_ne_dkBb : dkT ≠ dkBb := by decide
@[simp] theorem dks_dkT_ne_dkE : dkT ≠ dkE := by decide
@[simp] theorem dks_dkT_ne_lFl : dkT ≠ lFl := by decide
@[simp] theorem dks_lFl_ne_dkT : lFl ≠ dkT := by decide
@[simp] theorem dks_dkT_ne_lDh : dkT ≠ lDh := by decide
@[simp] theorem dks_lDh_ne_dkT : lDh ≠ dkT := by decide
@[simp] theorem dks_dkT_ne_lDt : dkT ≠ lDt := by decide
@[simp] theorem dks_lDt_ne_dkT : lDt ≠ dkT := by decide
@[simp] theorem dks_dkT_ne_lDg : dkT ≠ lDg := by decide
@[simp] theorem dks_lDg_ne_dkT : lDg ≠ dkT := by decide
@[simp] theorem dks_dkT_ne_lDi : dkT ≠ lDi := by decide
@[simp] theorem dks_lDi_ne_dkT : lDi ≠ dkT := by decide
@[simp] theorem dks_dkT_ne_lRp : dkT ≠ lRp := by decide
@[simp] theorem dks_lRp_ne_dkT : lRp ≠ dkT := by decide
@[simp] theorem dks_dkT_ne_lRn : dkT ≠ lRn := by decide
@[simp] theorem dks_lRn_ne_dkT : lRn ≠ dkT := by decide
@[simp] theorem dks_dkT_ne_lFle : dkT ≠ lFle := by decide
@[simp] theorem dks_lFle_ne_dkT : lFle ≠ dkT := by decide
@[simp] theorem dks_dkT_ne_lKb : dkT ≠ lKb := by decide
@[simp] theorem dks_lKb_ne_dkT : lKb ≠ dkT := by decide
@[simp] theorem dks_dkT_ne_lDir : dkT ≠ lDir := by decide
@[simp] theorem dks_lDir_ne_dkT : lDir ≠ dkT := by decide
@[simp] theorem dks_dkT_ne_lFln : dkT ≠ lFln := by decide
@[simp] theorem dks_lFln_ne_dkT : lFln ≠ dkT := by decide
@[simp] theorem dks_dkT_ne_lFll : dkT ≠ lFll := by decide
@[simp] theorem dks_lFll_ne_dkT : lFll ≠ dkT := by decide
@[simp] theorem dks_dkT_ne_lFls : dkT ≠ lFls := by decide
@[simp] theorem dks_lFls_ne_dkT : lFls ≠ dkT := by decide
@[simp] theorem dks_dkT_ne_kFu : dkT ≠ kFu := by decide
@[simp] theorem dks_kFu_ne_dkT : kFu ≠ dkT := by decide
@[simp] theorem dks_dkT_ne_kD : dkT ≠ kD := by decide
@[simp] theorem dks_kD_ne_dkT : kD ≠ dkT := by decide
@[simp] theorem dks_dkBb_ne_dkA : dkBb ≠ dkA := by decide
@[simp] theorem dks_dkBb_ne_dkB : dkBb ≠ dkB := by decide
@[simp] theorem dks_dkBb_ne_dkPa : dkBb ≠ dkPa := by decide
@[simp] theorem dks_dkBb_ne_dkGa : dkBb ≠ dkGa := by decide
@[simp] theorem dks_dkBb_ne_dkLa : dkBb ≠ dkLa := by decide
@[simp] theorem dks_dkBb_ne_dkPb : dkBb ≠ dkPb := by decide
@[simp] theorem dks_dkBb_ne_dkGb : dkBb ≠ dkGb := by decide
@[simp] theorem dks_dkBb_ne_dkLb : dkBb ≠ dkLb := by decide
@[simp] theorem dks_dkBb_ne_dkR : dkBb ≠ dkR := by decide
@[simp] theorem dks_dkBb_ne_dkT : dkBb ≠ dkT := by decide
@[simp] theorem dks_dkBb_ne_dkE : dkBb ≠ dkE := by decide
@[simp] theorem dks_dkBb_ne_lFl : dkBb ≠ lFl := by decide
@[simp] theorem dks_lFl_ne_dkBb : lFl ≠ dkBb := by decide
@[simp] theorem dks_dkBb_ne_lDh : dkBb ≠ lDh := by decide
@[simp] theorem dks_lDh_ne_dkBb : lDh ≠ dkBb := by decide
@[simp] theorem dks_dkBb_ne_lDt : dkBb ≠ lDt := by decide
@[simp] theorem dks_lDt_ne_dkBb : lDt ≠ dkBb := by decide
@[simp] theorem dks_dkBb_ne_lDg : dkBb ≠ lDg := by decide
@[simp] theorem dks_lDg_ne_dkBb : lDg ≠ dkBb := by decide
@[simp] theorem dks_dkBb_ne_lDi : dkBb ≠ lDi := by decide
@[simp] theorem dks_lDi_ne_dkBb : lDi ≠ dkBb := by decide
@[simp] theorem dks_dkBb_ne_lRp : dkBb ≠ lRp := by decide
@[simp] theorem dks_lRp_ne_dkBb : lRp ≠ dkBb := by decide
@[simp] theorem dks_dkBb_ne_lRn : dkBb ≠ lRn := by decide
@[simp] theorem dks_lRn_ne_dkBb : lRn ≠ dkBb := by decide
@[simp] theorem dks_dkBb_ne_lFle : dkBb ≠ lFle := by decide
@[simp] theorem dks_lFle_ne_dkBb : lFle ≠ dkBb := by decide
@[simp] theorem dks_dkBb_ne_lKb : dkBb ≠ lKb := by decide
@[simp] theorem dks_lKb_ne_dkBb : lKb ≠ dkBb := by decide
@[simp] theorem dks_dkBb_ne_lDir : dkBb ≠ lDir := by decide
@[simp] theorem dks_lDir_ne_dkBb : lDir ≠ dkBb := by decide
@[simp] theorem dks_dkBb_ne_lFln : dkBb ≠ lFln := by decide
@[simp] theorem dks_lFln_ne_dkBb : lFln ≠ dkBb := by decide
@[simp] theorem dks_dkBb_ne_lFll : dkBb ≠ lFll := by decide
@[simp] theorem dks_lFll_ne_dkBb : lFll ≠ dkBb := by decide
@[simp] theorem dks_dkBb_ne_lFls : dkBb ≠ lFls := by decide
@[simp] theorem dks_lFls_ne_dkBb : lFls ≠ dkBb := by decide
@[simp] theorem dks_dkBb_ne_kFu : dkBb ≠ kFu := by decide
@[simp] theorem dks_kFu_ne_dkBb : kFu ≠ dkBb := by decide
@[simp] theorem dks_dkBb_ne_kD : dkBb ≠ kD := by decide
@[simp] theorem dks_kD_ne_dkBb : kD ≠ dkBb := by decide
@[simp] theorem dks_dkE_ne_dkA : dkE ≠ dkA := by decide
@[simp] theorem dks_dkE_ne_dkB : dkE ≠ dkB := by decide
@[simp] theorem dks_dkE_ne_dkPa : dkE ≠ dkPa := by decide
@[simp] theorem dks_dkE_ne_dkGa : dkE ≠ dkGa := by decide
@[simp] theorem dks_dkE_ne_dkLa : dkE ≠ dkLa := by decide
@[simp] theorem dks_dkE_ne_dkPb : dkE ≠ dkPb := by decide
@[simp] theorem dks_dkE_ne_dkGb : dkE ≠ dkGb := by decide
@[simp] theorem dks_dkE_ne_dkLb : dkE ≠ dkLb := by decide
@[simp] theorem dks_dkE_ne_dkR : dkE ≠ dkR := by decide
@[simp] theorem dks_dkE_ne_dkT : dkE ≠ dkT := by decide
@[simp] theorem dks_dkE_ne_dkBb : dkE ≠ dkBb := by decide
@[simp] theorem dks_dkE_ne_lFl : dkE ≠ lFl := by decide
@[simp] theorem dks_lFl_ne_dkE : lFl ≠ dkE := by decide
@[simp] theorem dks_dkE_ne_lDh : dkE ≠ lDh := by decide
@[simp] theorem dks_lDh_ne_dkE : lDh ≠ dkE := by decide
@[simp] theorem dks_dkE_ne_lDt : dkE ≠ lDt := by decide
@[simp] theorem dks_lDt_ne_dkE : lDt ≠ dkE := by decide
@[simp] theorem dks_dkE_ne_lDg : dkE ≠ lDg := by decide
@[simp] theorem dks_lDg_ne_dkE : lDg ≠ dkE := by decide
@[simp] theorem dks_dkE_ne_lDi : dkE ≠ lDi := by decide
@[simp] theorem dks_lDi_ne_dkE : lDi ≠ dkE := by decide
@[simp] theorem dks_dkE_ne_lRp : dkE ≠ lRp := by decide
@[simp] theorem dks_lRp_ne_dkE : lRp ≠ dkE := by decide
@[simp] theorem dks_dkE_ne_lRn : dkE ≠ lRn := by decide
@[simp] theorem dks_lRn_ne_dkE : lRn ≠ dkE := by decide
@[simp] theorem dks_dkE_ne_lFle : dkE ≠ lFle := by decide
@[simp] theorem dks_lFle_ne_dkE : lFle ≠ dkE := by decide
@[simp] theorem dks_dkE_ne_lKb : dkE ≠ lKb := by decide
@[simp] theorem dks_lKb_ne_dkE : lKb ≠ dkE := by decide
@[simp] theorem dks_dkE_ne_lDir : dkE ≠ lDir := by decide
@[simp] theorem dks_lDir_ne_dkE : lDir ≠ dkE := by decide
@[simp] theorem dks_dkE_ne_lFln : dkE ≠ lFln := by decide
@[simp] theorem dks_lFln_ne_dkE : lFln ≠ dkE := by decide
@[simp] theorem dks_dkE_ne_lFll : dkE ≠ lFll := by decide
@[simp] theorem dks_lFll_ne_dkE : lFll ≠ dkE := by decide
@[simp] theorem dks_dkE_ne_lFls : dkE ≠ lFls := by decide
@[simp] theorem dks_lFls_ne_dkE : lFls ≠ dkE := by decide
@[simp] theorem dks_dkE_ne_kFu : dkE ≠ kFu := by decide
@[simp] theorem dks_kFu_ne_dkE : kFu ≠ dkE := by decide
@[simp] theorem dks_dkE_ne_kD : dkE ≠ kD := by decide
@[simp] theorem dks_kD_ne_dkE : kD ≠ dkE := by decide


def dkI1 := ofString "dks2_dki1"
def dkI2 := ofString "dks2_dki2"
def dkN1 := ofString "dks2_dkn1"
def dkU1 := ofString "dks2_dku1"
def dkN2 := ofString "dks2_dkn2"
def dkU2 := ofString "dks2_dku2"
def dkL := ofString "dks2_dkl"
def dkXa := ofString "dks2_dkxa"
def dkXb := ofString "dks2_dkxb"
def dkLa2 := ofString "dks2_dkla2"
def dkLb2 := ofString "dks2_dklb2"
def dkFa := ofString "dks2_dkfa"
def dkFb := ofString "dks2_dkfb"
def dkQ := ofString "dks2_dkq"
def dkDl := ofString "dks2_dkdl"
def dkW0 := ofString "dks2_dkw0"
def dkFo := ofString "dks2_dkfo"
def dkCo := ofString "dks2_dkco"
def dkUo := ofString "dks2_dkuo"
def dkEl := ofString "dks2_dkel"
def dkSl := ofString "dks2_dksl"
def dkLt := ofString "dks2_dklt"
def dkC := ofString "dks2_dkc"
def dkR2 := ofString "dks2_dkr2"

@[simp] theorem dks2_dkI1_ne_dkI2 : dkI1 ≠ dkI2 := by decide
@[simp] theorem dks2_dkI1_ne_dkN1 : dkI1 ≠ dkN1 := by decide
@[simp] theorem dks2_dkI1_ne_dkU1 : dkI1 ≠ dkU1 := by decide
@[simp] theorem dks2_dkI1_ne_dkN2 : dkI1 ≠ dkN2 := by decide
@[simp] theorem dks2_dkI1_ne_dkU2 : dkI1 ≠ dkU2 := by decide
@[simp] theorem dks2_dkI1_ne_dkL : dkI1 ≠ dkL := by decide
@[simp] theorem dks2_dkI1_ne_dkXa : dkI1 ≠ dkXa := by decide
@[simp] theorem dks2_dkI1_ne_dkXb : dkI1 ≠ dkXb := by decide
@[simp] theorem dks2_dkI1_ne_dkLa2 : dkI1 ≠ dkLa2 := by decide
@[simp] theorem dks2_dkI1_ne_dkLb2 : dkI1 ≠ dkLb2 := by decide
@[simp] theorem dks2_dkI1_ne_dkFa : dkI1 ≠ dkFa := by decide
@[simp] theorem dks2_dkI1_ne_dkFb : dkI1 ≠ dkFb := by decide
@[simp] theorem dks2_dkI1_ne_dkQ : dkI1 ≠ dkQ := by decide
@[simp] theorem dks2_dkI1_ne_dkDl : dkI1 ≠ dkDl := by decide
@[simp] theorem dks2_dkI1_ne_dkW0 : dkI1 ≠ dkW0 := by decide
@[simp] theorem dks2_dkI1_ne_dkFo : dkI1 ≠ dkFo := by decide
@[simp] theorem dks2_dkI1_ne_dkCo : dkI1 ≠ dkCo := by decide
@[simp] theorem dks2_dkI1_ne_dkUo : dkI1 ≠ dkUo := by decide
@[simp] theorem dks2_dkI1_ne_dkEl : dkI1 ≠ dkEl := by decide
@[simp] theorem dks2_dkI1_ne_dkSl : dkI1 ≠ dkSl := by decide
@[simp] theorem dks2_dkI1_ne_dkLt : dkI1 ≠ dkLt := by decide
@[simp] theorem dks2_dkI1_ne_dkC : dkI1 ≠ dkC := by decide
@[simp] theorem dks2_dkI1_ne_dkR2 : dkI1 ≠ dkR2 := by decide
@[simp] theorem dks2_dkI1_ne_lFl : dkI1 ≠ lFl := by decide
@[simp] theorem dks2_lFl_ne_dkI1 : lFl ≠ dkI1 := by decide
@[simp] theorem dks2_dkI1_ne_lDh : dkI1 ≠ lDh := by decide
@[simp] theorem dks2_lDh_ne_dkI1 : lDh ≠ dkI1 := by decide
@[simp] theorem dks2_dkI1_ne_lDt : dkI1 ≠ lDt := by decide
@[simp] theorem dks2_lDt_ne_dkI1 : lDt ≠ dkI1 := by decide
@[simp] theorem dks2_dkI1_ne_lDg : dkI1 ≠ lDg := by decide
@[simp] theorem dks2_lDg_ne_dkI1 : lDg ≠ dkI1 := by decide
@[simp] theorem dks2_dkI1_ne_lDi : dkI1 ≠ lDi := by decide
@[simp] theorem dks2_lDi_ne_dkI1 : lDi ≠ dkI1 := by decide
@[simp] theorem dks2_dkI1_ne_lRp : dkI1 ≠ lRp := by decide
@[simp] theorem dks2_lRp_ne_dkI1 : lRp ≠ dkI1 := by decide
@[simp] theorem dks2_dkI1_ne_lRn : dkI1 ≠ lRn := by decide
@[simp] theorem dks2_lRn_ne_dkI1 : lRn ≠ dkI1 := by decide
@[simp] theorem dks2_dkI1_ne_lFle : dkI1 ≠ lFle := by decide
@[simp] theorem dks2_lFle_ne_dkI1 : lFle ≠ dkI1 := by decide
@[simp] theorem dks2_dkI1_ne_lKb : dkI1 ≠ lKb := by decide
@[simp] theorem dks2_lKb_ne_dkI1 : lKb ≠ dkI1 := by decide
@[simp] theorem dks2_dkI1_ne_lDir : dkI1 ≠ lDir := by decide
@[simp] theorem dks2_lDir_ne_dkI1 : lDir ≠ dkI1 := by decide
@[simp] theorem dks2_dkI1_ne_lFln : dkI1 ≠ lFln := by decide
@[simp] theorem dks2_lFln_ne_dkI1 : lFln ≠ dkI1 := by decide
@[simp] theorem dks2_dkI1_ne_lFll : dkI1 ≠ lFll := by decide
@[simp] theorem dks2_lFll_ne_dkI1 : lFll ≠ dkI1 := by decide
@[simp] theorem dks2_dkI1_ne_lFls : dkI1 ≠ lFls := by decide
@[simp] theorem dks2_lFls_ne_dkI1 : lFls ≠ dkI1 := by decide
@[simp] theorem dks2_dkI1_ne_kFu : dkI1 ≠ kFu := by decide
@[simp] theorem dks2_kFu_ne_dkI1 : kFu ≠ dkI1 := by decide
@[simp] theorem dks2_dkI1_ne_kD : dkI1 ≠ kD := by decide
@[simp] theorem dks2_kD_ne_dkI1 : kD ≠ dkI1 := by decide
@[simp] theorem dks2_dkI1_ne_dkA : dkI1 ≠ dkA := by decide
@[simp] theorem dks2_dkA_ne_dkI1 : dkA ≠ dkI1 := by decide
@[simp] theorem dks2_dkI1_ne_dkB : dkI1 ≠ dkB := by decide
@[simp] theorem dks2_dkB_ne_dkI1 : dkB ≠ dkI1 := by decide
@[simp] theorem dks2_dkI1_ne_dkPa : dkI1 ≠ dkPa := by decide
@[simp] theorem dks2_dkPa_ne_dkI1 : dkPa ≠ dkI1 := by decide
@[simp] theorem dks2_dkI1_ne_dkGa : dkI1 ≠ dkGa := by decide
@[simp] theorem dks2_dkGa_ne_dkI1 : dkGa ≠ dkI1 := by decide
@[simp] theorem dks2_dkI1_ne_dkLa : dkI1 ≠ dkLa := by decide
@[simp] theorem dks2_dkLa_ne_dkI1 : dkLa ≠ dkI1 := by decide
@[simp] theorem dks2_dkI1_ne_dkPb : dkI1 ≠ dkPb := by decide
@[simp] theorem dks2_dkPb_ne_dkI1 : dkPb ≠ dkI1 := by decide
@[simp] theorem dks2_dkI1_ne_dkGb : dkI1 ≠ dkGb := by decide
@[simp] theorem dks2_dkGb_ne_dkI1 : dkGb ≠ dkI1 := by decide
@[simp] theorem dks2_dkI1_ne_dkLb : dkI1 ≠ dkLb := by decide
@[simp] theorem dks2_dkLb_ne_dkI1 : dkLb ≠ dkI1 := by decide
@[simp] theorem dks2_dkI1_ne_dkR : dkI1 ≠ dkR := by decide
@[simp] theorem dks2_dkR_ne_dkI1 : dkR ≠ dkI1 := by decide
@[simp] theorem dks2_dkI1_ne_dkT : dkI1 ≠ dkT := by decide
@[simp] theorem dks2_dkT_ne_dkI1 : dkT ≠ dkI1 := by decide
@[simp] theorem dks2_dkI1_ne_dkBb : dkI1 ≠ dkBb := by decide
@[simp] theorem dks2_dkBb_ne_dkI1 : dkBb ≠ dkI1 := by decide
@[simp] theorem dks2_dkI1_ne_dkE : dkI1 ≠ dkE := by decide
@[simp] theorem dks2_dkE_ne_dkI1 : dkE ≠ dkI1 := by decide
@[simp] theorem dks2_dkI2_ne_dkI1 : dkI2 ≠ dkI1 := by decide
@[simp] theorem dks2_dkI2_ne_dkN1 : dkI2 ≠ dkN1 := by decide
@[simp] theorem dks2_dkI2_ne_dkU1 : dkI2 ≠ dkU1 := by decide
@[simp] theorem dks2_dkI2_ne_dkN2 : dkI2 ≠ dkN2 := by decide
@[simp] theorem dks2_dkI2_ne_dkU2 : dkI2 ≠ dkU2 := by decide
@[simp] theorem dks2_dkI2_ne_dkL : dkI2 ≠ dkL := by decide
@[simp] theorem dks2_dkI2_ne_dkXa : dkI2 ≠ dkXa := by decide
@[simp] theorem dks2_dkI2_ne_dkXb : dkI2 ≠ dkXb := by decide
@[simp] theorem dks2_dkI2_ne_dkLa2 : dkI2 ≠ dkLa2 := by decide
@[simp] theorem dks2_dkI2_ne_dkLb2 : dkI2 ≠ dkLb2 := by decide
@[simp] theorem dks2_dkI2_ne_dkFa : dkI2 ≠ dkFa := by decide
@[simp] theorem dks2_dkI2_ne_dkFb : dkI2 ≠ dkFb := by decide
@[simp] theorem dks2_dkI2_ne_dkQ : dkI2 ≠ dkQ := by decide
@[simp] theorem dks2_dkI2_ne_dkDl : dkI2 ≠ dkDl := by decide
@[simp] theorem dks2_dkI2_ne_dkW0 : dkI2 ≠ dkW0 := by decide
@[simp] theorem dks2_dkI2_ne_dkFo : dkI2 ≠ dkFo := by decide
@[simp] theorem dks2_dkI2_ne_dkCo : dkI2 ≠ dkCo := by decide
@[simp] theorem dks2_dkI2_ne_dkUo : dkI2 ≠ dkUo := by decide
@[simp] theorem dks2_dkI2_ne_dkEl : dkI2 ≠ dkEl := by decide
@[simp] theorem dks2_dkI2_ne_dkSl : dkI2 ≠ dkSl := by decide
@[simp] theorem dks2_dkI2_ne_dkLt : dkI2 ≠ dkLt := by decide
@[simp] theorem dks2_dkI2_ne_dkC : dkI2 ≠ dkC := by decide
@[simp] theorem dks2_dkI2_ne_dkR2 : dkI2 ≠ dkR2 := by decide
@[simp] theorem dks2_dkI2_ne_lFl : dkI2 ≠ lFl := by decide
@[simp] theorem dks2_lFl_ne_dkI2 : lFl ≠ dkI2 := by decide
@[simp] theorem dks2_dkI2_ne_lDh : dkI2 ≠ lDh := by decide
@[simp] theorem dks2_lDh_ne_dkI2 : lDh ≠ dkI2 := by decide
@[simp] theorem dks2_dkI2_ne_lDt : dkI2 ≠ lDt := by decide
@[simp] theorem dks2_lDt_ne_dkI2 : lDt ≠ dkI2 := by decide
@[simp] theorem dks2_dkI2_ne_lDg : dkI2 ≠ lDg := by decide
@[simp] theorem dks2_lDg_ne_dkI2 : lDg ≠ dkI2 := by decide
@[simp] theorem dks2_dkI2_ne_lDi : dkI2 ≠ lDi := by decide
@[simp] theorem dks2_lDi_ne_dkI2 : lDi ≠ dkI2 := by decide
@[simp] theorem dks2_dkI2_ne_lRp : dkI2 ≠ lRp := by decide
@[simp] theorem dks2_lRp_ne_dkI2 : lRp ≠ dkI2 := by decide
@[simp] theorem dks2_dkI2_ne_lRn : dkI2 ≠ lRn := by decide
@[simp] theorem dks2_lRn_ne_dkI2 : lRn ≠ dkI2 := by decide
@[simp] theorem dks2_dkI2_ne_lFle : dkI2 ≠ lFle := by decide
@[simp] theorem dks2_lFle_ne_dkI2 : lFle ≠ dkI2 := by decide
@[simp] theorem dks2_dkI2_ne_lKb : dkI2 ≠ lKb := by decide
@[simp] theorem dks2_lKb_ne_dkI2 : lKb ≠ dkI2 := by decide
@[simp] theorem dks2_dkI2_ne_lDir : dkI2 ≠ lDir := by decide
@[simp] theorem dks2_lDir_ne_dkI2 : lDir ≠ dkI2 := by decide
@[simp] theorem dks2_dkI2_ne_lFln : dkI2 ≠ lFln := by decide
@[simp] theorem dks2_lFln_ne_dkI2 : lFln ≠ dkI2 := by decide
@[simp] theorem dks2_dkI2_ne_lFll : dkI2 ≠ lFll := by decide
@[simp] theorem dks2_lFll_ne_dkI2 : lFll ≠ dkI2 := by decide
@[simp] theorem dks2_dkI2_ne_lFls : dkI2 ≠ lFls := by decide
@[simp] theorem dks2_lFls_ne_dkI2 : lFls ≠ dkI2 := by decide
@[simp] theorem dks2_dkI2_ne_kFu : dkI2 ≠ kFu := by decide
@[simp] theorem dks2_kFu_ne_dkI2 : kFu ≠ dkI2 := by decide
@[simp] theorem dks2_dkI2_ne_kD : dkI2 ≠ kD := by decide
@[simp] theorem dks2_kD_ne_dkI2 : kD ≠ dkI2 := by decide
@[simp] theorem dks2_dkI2_ne_dkA : dkI2 ≠ dkA := by decide
@[simp] theorem dks2_dkA_ne_dkI2 : dkA ≠ dkI2 := by decide
@[simp] theorem dks2_dkI2_ne_dkB : dkI2 ≠ dkB := by decide
@[simp] theorem dks2_dkB_ne_dkI2 : dkB ≠ dkI2 := by decide
@[simp] theorem dks2_dkI2_ne_dkPa : dkI2 ≠ dkPa := by decide
@[simp] theorem dks2_dkPa_ne_dkI2 : dkPa ≠ dkI2 := by decide
@[simp] theorem dks2_dkI2_ne_dkGa : dkI2 ≠ dkGa := by decide
@[simp] theorem dks2_dkGa_ne_dkI2 : dkGa ≠ dkI2 := by decide
@[simp] theorem dks2_dkI2_ne_dkLa : dkI2 ≠ dkLa := by decide
@[simp] theorem dks2_dkLa_ne_dkI2 : dkLa ≠ dkI2 := by decide
@[simp] theorem dks2_dkI2_ne_dkPb : dkI2 ≠ dkPb := by decide
@[simp] theorem dks2_dkPb_ne_dkI2 : dkPb ≠ dkI2 := by decide
@[simp] theorem dks2_dkI2_ne_dkGb : dkI2 ≠ dkGb := by decide
@[simp] theorem dks2_dkGb_ne_dkI2 : dkGb ≠ dkI2 := by decide
@[simp] theorem dks2_dkI2_ne_dkLb : dkI2 ≠ dkLb := by decide
@[simp] theorem dks2_dkLb_ne_dkI2 : dkLb ≠ dkI2 := by decide
@[simp] theorem dks2_dkI2_ne_dkR : dkI2 ≠ dkR := by decide
@[simp] theorem dks2_dkR_ne_dkI2 : dkR ≠ dkI2 := by decide
@[simp] theorem dks2_dkI2_ne_dkT : dkI2 ≠ dkT := by decide
@[simp] theorem dks2_dkT_ne_dkI2 : dkT ≠ dkI2 := by decide
@[simp] theorem dks2_dkI2_ne_dkBb : dkI2 ≠ dkBb := by decide
@[simp] theorem dks2_dkBb_ne_dkI2 : dkBb ≠ dkI2 := by decide
@[simp] theorem dks2_dkI2_ne_dkE : dkI2 ≠ dkE := by decide
@[simp] theorem dks2_dkE_ne_dkI2 : dkE ≠ dkI2 := by decide
@[simp] theorem dks2_dkN1_ne_dkI1 : dkN1 ≠ dkI1 := by decide
@[simp] theorem dks2_dkN1_ne_dkI2 : dkN1 ≠ dkI2 := by decide
@[simp] theorem dks2_dkN1_ne_dkU1 : dkN1 ≠ dkU1 := by decide
@[simp] theorem dks2_dkN1_ne_dkN2 : dkN1 ≠ dkN2 := by decide
@[simp] theorem dks2_dkN1_ne_dkU2 : dkN1 ≠ dkU2 := by decide
@[simp] theorem dks2_dkN1_ne_dkL : dkN1 ≠ dkL := by decide
@[simp] theorem dks2_dkN1_ne_dkXa : dkN1 ≠ dkXa := by decide
@[simp] theorem dks2_dkN1_ne_dkXb : dkN1 ≠ dkXb := by decide
@[simp] theorem dks2_dkN1_ne_dkLa2 : dkN1 ≠ dkLa2 := by decide
@[simp] theorem dks2_dkN1_ne_dkLb2 : dkN1 ≠ dkLb2 := by decide
@[simp] theorem dks2_dkN1_ne_dkFa : dkN1 ≠ dkFa := by decide
@[simp] theorem dks2_dkN1_ne_dkFb : dkN1 ≠ dkFb := by decide
@[simp] theorem dks2_dkN1_ne_dkQ : dkN1 ≠ dkQ := by decide
@[simp] theorem dks2_dkN1_ne_dkDl : dkN1 ≠ dkDl := by decide
@[simp] theorem dks2_dkN1_ne_dkW0 : dkN1 ≠ dkW0 := by decide
@[simp] theorem dks2_dkN1_ne_dkFo : dkN1 ≠ dkFo := by decide
@[simp] theorem dks2_dkN1_ne_dkCo : dkN1 ≠ dkCo := by decide
@[simp] theorem dks2_dkN1_ne_dkUo : dkN1 ≠ dkUo := by decide
@[simp] theorem dks2_dkN1_ne_dkEl : dkN1 ≠ dkEl := by decide
@[simp] theorem dks2_dkN1_ne_dkSl : dkN1 ≠ dkSl := by decide
@[simp] theorem dks2_dkN1_ne_dkLt : dkN1 ≠ dkLt := by decide
@[simp] theorem dks2_dkN1_ne_dkC : dkN1 ≠ dkC := by decide
@[simp] theorem dks2_dkN1_ne_dkR2 : dkN1 ≠ dkR2 := by decide
@[simp] theorem dks2_dkN1_ne_lFl : dkN1 ≠ lFl := by decide
@[simp] theorem dks2_lFl_ne_dkN1 : lFl ≠ dkN1 := by decide
@[simp] theorem dks2_dkN1_ne_lDh : dkN1 ≠ lDh := by decide
@[simp] theorem dks2_lDh_ne_dkN1 : lDh ≠ dkN1 := by decide
@[simp] theorem dks2_dkN1_ne_lDt : dkN1 ≠ lDt := by decide
@[simp] theorem dks2_lDt_ne_dkN1 : lDt ≠ dkN1 := by decide
@[simp] theorem dks2_dkN1_ne_lDg : dkN1 ≠ lDg := by decide
@[simp] theorem dks2_lDg_ne_dkN1 : lDg ≠ dkN1 := by decide
@[simp] theorem dks2_dkN1_ne_lDi : dkN1 ≠ lDi := by decide
@[simp] theorem dks2_lDi_ne_dkN1 : lDi ≠ dkN1 := by decide
@[simp] theorem dks2_dkN1_ne_lRp : dkN1 ≠ lRp := by decide
@[simp] theorem dks2_lRp_ne_dkN1 : lRp ≠ dkN1 := by decide
@[simp] theorem dks2_dkN1_ne_lRn : dkN1 ≠ lRn := by decide
@[simp] theorem dks2_lRn_ne_dkN1 : lRn ≠ dkN1 := by decide
@[simp] theorem dks2_dkN1_ne_lFle : dkN1 ≠ lFle := by decide
@[simp] theorem dks2_lFle_ne_dkN1 : lFle ≠ dkN1 := by decide
@[simp] theorem dks2_dkN1_ne_lKb : dkN1 ≠ lKb := by decide
@[simp] theorem dks2_lKb_ne_dkN1 : lKb ≠ dkN1 := by decide
@[simp] theorem dks2_dkN1_ne_lDir : dkN1 ≠ lDir := by decide
@[simp] theorem dks2_lDir_ne_dkN1 : lDir ≠ dkN1 := by decide
@[simp] theorem dks2_dkN1_ne_lFln : dkN1 ≠ lFln := by decide
@[simp] theorem dks2_lFln_ne_dkN1 : lFln ≠ dkN1 := by decide
@[simp] theorem dks2_dkN1_ne_lFll : dkN1 ≠ lFll := by decide
@[simp] theorem dks2_lFll_ne_dkN1 : lFll ≠ dkN1 := by decide
@[simp] theorem dks2_dkN1_ne_lFls : dkN1 ≠ lFls := by decide
@[simp] theorem dks2_lFls_ne_dkN1 : lFls ≠ dkN1 := by decide
@[simp] theorem dks2_dkN1_ne_kFu : dkN1 ≠ kFu := by decide
@[simp] theorem dks2_kFu_ne_dkN1 : kFu ≠ dkN1 := by decide
@[simp] theorem dks2_dkN1_ne_kD : dkN1 ≠ kD := by decide
@[simp] theorem dks2_kD_ne_dkN1 : kD ≠ dkN1 := by decide
@[simp] theorem dks2_dkN1_ne_dkA : dkN1 ≠ dkA := by decide
@[simp] theorem dks2_dkA_ne_dkN1 : dkA ≠ dkN1 := by decide
@[simp] theorem dks2_dkN1_ne_dkB : dkN1 ≠ dkB := by decide
@[simp] theorem dks2_dkB_ne_dkN1 : dkB ≠ dkN1 := by decide
@[simp] theorem dks2_dkN1_ne_dkPa : dkN1 ≠ dkPa := by decide
@[simp] theorem dks2_dkPa_ne_dkN1 : dkPa ≠ dkN1 := by decide
@[simp] theorem dks2_dkN1_ne_dkGa : dkN1 ≠ dkGa := by decide
@[simp] theorem dks2_dkGa_ne_dkN1 : dkGa ≠ dkN1 := by decide
@[simp] theorem dks2_dkN1_ne_dkLa : dkN1 ≠ dkLa := by decide
@[simp] theorem dks2_dkLa_ne_dkN1 : dkLa ≠ dkN1 := by decide
@[simp] theorem dks2_dkN1_ne_dkPb : dkN1 ≠ dkPb := by decide
@[simp] theorem dks2_dkPb_ne_dkN1 : dkPb ≠ dkN1 := by decide
@[simp] theorem dks2_dkN1_ne_dkGb : dkN1 ≠ dkGb := by decide
@[simp] theorem dks2_dkGb_ne_dkN1 : dkGb ≠ dkN1 := by decide
@[simp] theorem dks2_dkN1_ne_dkLb : dkN1 ≠ dkLb := by decide
@[simp] theorem dks2_dkLb_ne_dkN1 : dkLb ≠ dkN1 := by decide
@[simp] theorem dks2_dkN1_ne_dkR : dkN1 ≠ dkR := by decide
@[simp] theorem dks2_dkR_ne_dkN1 : dkR ≠ dkN1 := by decide
@[simp] theorem dks2_dkN1_ne_dkT : dkN1 ≠ dkT := by decide
@[simp] theorem dks2_dkT_ne_dkN1 : dkT ≠ dkN1 := by decide
@[simp] theorem dks2_dkN1_ne_dkBb : dkN1 ≠ dkBb := by decide
@[simp] theorem dks2_dkBb_ne_dkN1 : dkBb ≠ dkN1 := by decide
@[simp] theorem dks2_dkN1_ne_dkE : dkN1 ≠ dkE := by decide
@[simp] theorem dks2_dkE_ne_dkN1 : dkE ≠ dkN1 := by decide
@[simp] theorem dks2_dkU1_ne_dkI1 : dkU1 ≠ dkI1 := by decide
@[simp] theorem dks2_dkU1_ne_dkI2 : dkU1 ≠ dkI2 := by decide
@[simp] theorem dks2_dkU1_ne_dkN1 : dkU1 ≠ dkN1 := by decide
@[simp] theorem dks2_dkU1_ne_dkN2 : dkU1 ≠ dkN2 := by decide
@[simp] theorem dks2_dkU1_ne_dkU2 : dkU1 ≠ dkU2 := by decide
@[simp] theorem dks2_dkU1_ne_dkL : dkU1 ≠ dkL := by decide
@[simp] theorem dks2_dkU1_ne_dkXa : dkU1 ≠ dkXa := by decide
@[simp] theorem dks2_dkU1_ne_dkXb : dkU1 ≠ dkXb := by decide
@[simp] theorem dks2_dkU1_ne_dkLa2 : dkU1 ≠ dkLa2 := by decide
@[simp] theorem dks2_dkU1_ne_dkLb2 : dkU1 ≠ dkLb2 := by decide
@[simp] theorem dks2_dkU1_ne_dkFa : dkU1 ≠ dkFa := by decide
@[simp] theorem dks2_dkU1_ne_dkFb : dkU1 ≠ dkFb := by decide
@[simp] theorem dks2_dkU1_ne_dkQ : dkU1 ≠ dkQ := by decide
@[simp] theorem dks2_dkU1_ne_dkDl : dkU1 ≠ dkDl := by decide
@[simp] theorem dks2_dkU1_ne_dkW0 : dkU1 ≠ dkW0 := by decide
@[simp] theorem dks2_dkU1_ne_dkFo : dkU1 ≠ dkFo := by decide
@[simp] theorem dks2_dkU1_ne_dkCo : dkU1 ≠ dkCo := by decide
@[simp] theorem dks2_dkU1_ne_dkUo : dkU1 ≠ dkUo := by decide
@[simp] theorem dks2_dkU1_ne_dkEl : dkU1 ≠ dkEl := by decide
@[simp] theorem dks2_dkU1_ne_dkSl : dkU1 ≠ dkSl := by decide
@[simp] theorem dks2_dkU1_ne_dkLt : dkU1 ≠ dkLt := by decide
@[simp] theorem dks2_dkU1_ne_dkC : dkU1 ≠ dkC := by decide
@[simp] theorem dks2_dkU1_ne_dkR2 : dkU1 ≠ dkR2 := by decide
@[simp] theorem dks2_dkU1_ne_lFl : dkU1 ≠ lFl := by decide
@[simp] theorem dks2_lFl_ne_dkU1 : lFl ≠ dkU1 := by decide
@[simp] theorem dks2_dkU1_ne_lDh : dkU1 ≠ lDh := by decide
@[simp] theorem dks2_lDh_ne_dkU1 : lDh ≠ dkU1 := by decide
@[simp] theorem dks2_dkU1_ne_lDt : dkU1 ≠ lDt := by decide
@[simp] theorem dks2_lDt_ne_dkU1 : lDt ≠ dkU1 := by decide
@[simp] theorem dks2_dkU1_ne_lDg : dkU1 ≠ lDg := by decide
@[simp] theorem dks2_lDg_ne_dkU1 : lDg ≠ dkU1 := by decide
@[simp] theorem dks2_dkU1_ne_lDi : dkU1 ≠ lDi := by decide
@[simp] theorem dks2_lDi_ne_dkU1 : lDi ≠ dkU1 := by decide
@[simp] theorem dks2_dkU1_ne_lRp : dkU1 ≠ lRp := by decide
@[simp] theorem dks2_lRp_ne_dkU1 : lRp ≠ dkU1 := by decide
@[simp] theorem dks2_dkU1_ne_lRn : dkU1 ≠ lRn := by decide
@[simp] theorem dks2_lRn_ne_dkU1 : lRn ≠ dkU1 := by decide
@[simp] theorem dks2_dkU1_ne_lFle : dkU1 ≠ lFle := by decide
@[simp] theorem dks2_lFle_ne_dkU1 : lFle ≠ dkU1 := by decide
@[simp] theorem dks2_dkU1_ne_lKb : dkU1 ≠ lKb := by decide
@[simp] theorem dks2_lKb_ne_dkU1 : lKb ≠ dkU1 := by decide
@[simp] theorem dks2_dkU1_ne_lDir : dkU1 ≠ lDir := by decide
@[simp] theorem dks2_lDir_ne_dkU1 : lDir ≠ dkU1 := by decide
@[simp] theorem dks2_dkU1_ne_lFln : dkU1 ≠ lFln := by decide
@[simp] theorem dks2_lFln_ne_dkU1 : lFln ≠ dkU1 := by decide
@[simp] theorem dks2_dkU1_ne_lFll : dkU1 ≠ lFll := by decide
@[simp] theorem dks2_lFll_ne_dkU1 : lFll ≠ dkU1 := by decide
@[simp] theorem dks2_dkU1_ne_lFls : dkU1 ≠ lFls := by decide
@[simp] theorem dks2_lFls_ne_dkU1 : lFls ≠ dkU1 := by decide
@[simp] theorem dks2_dkU1_ne_kFu : dkU1 ≠ kFu := by decide
@[simp] theorem dks2_kFu_ne_dkU1 : kFu ≠ dkU1 := by decide
@[simp] theorem dks2_dkU1_ne_kD : dkU1 ≠ kD := by decide
@[simp] theorem dks2_kD_ne_dkU1 : kD ≠ dkU1 := by decide
@[simp] theorem dks2_dkU1_ne_dkA : dkU1 ≠ dkA := by decide
@[simp] theorem dks2_dkA_ne_dkU1 : dkA ≠ dkU1 := by decide
@[simp] theorem dks2_dkU1_ne_dkB : dkU1 ≠ dkB := by decide
@[simp] theorem dks2_dkB_ne_dkU1 : dkB ≠ dkU1 := by decide
@[simp] theorem dks2_dkU1_ne_dkPa : dkU1 ≠ dkPa := by decide
@[simp] theorem dks2_dkPa_ne_dkU1 : dkPa ≠ dkU1 := by decide
@[simp] theorem dks2_dkU1_ne_dkGa : dkU1 ≠ dkGa := by decide
@[simp] theorem dks2_dkGa_ne_dkU1 : dkGa ≠ dkU1 := by decide
@[simp] theorem dks2_dkU1_ne_dkLa : dkU1 ≠ dkLa := by decide
@[simp] theorem dks2_dkLa_ne_dkU1 : dkLa ≠ dkU1 := by decide
@[simp] theorem dks2_dkU1_ne_dkPb : dkU1 ≠ dkPb := by decide
@[simp] theorem dks2_dkPb_ne_dkU1 : dkPb ≠ dkU1 := by decide
@[simp] theorem dks2_dkU1_ne_dkGb : dkU1 ≠ dkGb := by decide
@[simp] theorem dks2_dkGb_ne_dkU1 : dkGb ≠ dkU1 := by decide
@[simp] theorem dks2_dkU1_ne_dkLb : dkU1 ≠ dkLb := by decide
@[simp] theorem dks2_dkLb_ne_dkU1 : dkLb ≠ dkU1 := by decide
@[simp] theorem dks2_dkU1_ne_dkR : dkU1 ≠ dkR := by decide
@[simp] theorem dks2_dkR_ne_dkU1 : dkR ≠ dkU1 := by decide
@[simp] theorem dks2_dkU1_ne_dkT : dkU1 ≠ dkT := by decide
@[simp] theorem dks2_dkT_ne_dkU1 : dkT ≠ dkU1 := by decide
@[simp] theorem dks2_dkU1_ne_dkBb : dkU1 ≠ dkBb := by decide
@[simp] theorem dks2_dkBb_ne_dkU1 : dkBb ≠ dkU1 := by decide
@[simp] theorem dks2_dkU1_ne_dkE : dkU1 ≠ dkE := by decide
@[simp] theorem dks2_dkE_ne_dkU1 : dkE ≠ dkU1 := by decide
@[simp] theorem dks2_dkN2_ne_dkI1 : dkN2 ≠ dkI1 := by decide
@[simp] theorem dks2_dkN2_ne_dkI2 : dkN2 ≠ dkI2 := by decide
@[simp] theorem dks2_dkN2_ne_dkN1 : dkN2 ≠ dkN1 := by decide
@[simp] theorem dks2_dkN2_ne_dkU1 : dkN2 ≠ dkU1 := by decide
@[simp] theorem dks2_dkN2_ne_dkU2 : dkN2 ≠ dkU2 := by decide
@[simp] theorem dks2_dkN2_ne_dkL : dkN2 ≠ dkL := by decide
@[simp] theorem dks2_dkN2_ne_dkXa : dkN2 ≠ dkXa := by decide
@[simp] theorem dks2_dkN2_ne_dkXb : dkN2 ≠ dkXb := by decide
@[simp] theorem dks2_dkN2_ne_dkLa2 : dkN2 ≠ dkLa2 := by decide
@[simp] theorem dks2_dkN2_ne_dkLb2 : dkN2 ≠ dkLb2 := by decide
@[simp] theorem dks2_dkN2_ne_dkFa : dkN2 ≠ dkFa := by decide
@[simp] theorem dks2_dkN2_ne_dkFb : dkN2 ≠ dkFb := by decide
@[simp] theorem dks2_dkN2_ne_dkQ : dkN2 ≠ dkQ := by decide
@[simp] theorem dks2_dkN2_ne_dkDl : dkN2 ≠ dkDl := by decide
@[simp] theorem dks2_dkN2_ne_dkW0 : dkN2 ≠ dkW0 := by decide
@[simp] theorem dks2_dkN2_ne_dkFo : dkN2 ≠ dkFo := by decide
@[simp] theorem dks2_dkN2_ne_dkCo : dkN2 ≠ dkCo := by decide
@[simp] theorem dks2_dkN2_ne_dkUo : dkN2 ≠ dkUo := by decide
@[simp] theorem dks2_dkN2_ne_dkEl : dkN2 ≠ dkEl := by decide
@[simp] theorem dks2_dkN2_ne_dkSl : dkN2 ≠ dkSl := by decide
@[simp] theorem dks2_dkN2_ne_dkLt : dkN2 ≠ dkLt := by decide
@[simp] theorem dks2_dkN2_ne_dkC : dkN2 ≠ dkC := by decide
@[simp] theorem dks2_dkN2_ne_dkR2 : dkN2 ≠ dkR2 := by decide
@[simp] theorem dks2_dkN2_ne_lFl : dkN2 ≠ lFl := by decide
@[simp] theorem dks2_lFl_ne_dkN2 : lFl ≠ dkN2 := by decide
@[simp] theorem dks2_dkN2_ne_lDh : dkN2 ≠ lDh := by decide
@[simp] theorem dks2_lDh_ne_dkN2 : lDh ≠ dkN2 := by decide
@[simp] theorem dks2_dkN2_ne_lDt : dkN2 ≠ lDt := by decide
@[simp] theorem dks2_lDt_ne_dkN2 : lDt ≠ dkN2 := by decide
@[simp] theorem dks2_dkN2_ne_lDg : dkN2 ≠ lDg := by decide
@[simp] theorem dks2_lDg_ne_dkN2 : lDg ≠ dkN2 := by decide
@[simp] theorem dks2_dkN2_ne_lDi : dkN2 ≠ lDi := by decide
@[simp] theorem dks2_lDi_ne_dkN2 : lDi ≠ dkN2 := by decide
@[simp] theorem dks2_dkN2_ne_lRp : dkN2 ≠ lRp := by decide
@[simp] theorem dks2_lRp_ne_dkN2 : lRp ≠ dkN2 := by decide
@[simp] theorem dks2_dkN2_ne_lRn : dkN2 ≠ lRn := by decide
@[simp] theorem dks2_lRn_ne_dkN2 : lRn ≠ dkN2 := by decide
@[simp] theorem dks2_dkN2_ne_lFle : dkN2 ≠ lFle := by decide
@[simp] theorem dks2_lFle_ne_dkN2 : lFle ≠ dkN2 := by decide
@[simp] theorem dks2_dkN2_ne_lKb : dkN2 ≠ lKb := by decide
@[simp] theorem dks2_lKb_ne_dkN2 : lKb ≠ dkN2 := by decide
@[simp] theorem dks2_dkN2_ne_lDir : dkN2 ≠ lDir := by decide
@[simp] theorem dks2_lDir_ne_dkN2 : lDir ≠ dkN2 := by decide
@[simp] theorem dks2_dkN2_ne_lFln : dkN2 ≠ lFln := by decide
@[simp] theorem dks2_lFln_ne_dkN2 : lFln ≠ dkN2 := by decide
@[simp] theorem dks2_dkN2_ne_lFll : dkN2 ≠ lFll := by decide
@[simp] theorem dks2_lFll_ne_dkN2 : lFll ≠ dkN2 := by decide
@[simp] theorem dks2_dkN2_ne_lFls : dkN2 ≠ lFls := by decide
@[simp] theorem dks2_lFls_ne_dkN2 : lFls ≠ dkN2 := by decide
@[simp] theorem dks2_dkN2_ne_kFu : dkN2 ≠ kFu := by decide
@[simp] theorem dks2_kFu_ne_dkN2 : kFu ≠ dkN2 := by decide
@[simp] theorem dks2_dkN2_ne_kD : dkN2 ≠ kD := by decide
@[simp] theorem dks2_kD_ne_dkN2 : kD ≠ dkN2 := by decide
@[simp] theorem dks2_dkN2_ne_dkA : dkN2 ≠ dkA := by decide
@[simp] theorem dks2_dkA_ne_dkN2 : dkA ≠ dkN2 := by decide
@[simp] theorem dks2_dkN2_ne_dkB : dkN2 ≠ dkB := by decide
@[simp] theorem dks2_dkB_ne_dkN2 : dkB ≠ dkN2 := by decide
@[simp] theorem dks2_dkN2_ne_dkPa : dkN2 ≠ dkPa := by decide
@[simp] theorem dks2_dkPa_ne_dkN2 : dkPa ≠ dkN2 := by decide
@[simp] theorem dks2_dkN2_ne_dkGa : dkN2 ≠ dkGa := by decide
@[simp] theorem dks2_dkGa_ne_dkN2 : dkGa ≠ dkN2 := by decide
@[simp] theorem dks2_dkN2_ne_dkLa : dkN2 ≠ dkLa := by decide
@[simp] theorem dks2_dkLa_ne_dkN2 : dkLa ≠ dkN2 := by decide
@[simp] theorem dks2_dkN2_ne_dkPb : dkN2 ≠ dkPb := by decide
@[simp] theorem dks2_dkPb_ne_dkN2 : dkPb ≠ dkN2 := by decide
@[simp] theorem dks2_dkN2_ne_dkGb : dkN2 ≠ dkGb := by decide
@[simp] theorem dks2_dkGb_ne_dkN2 : dkGb ≠ dkN2 := by decide
@[simp] theorem dks2_dkN2_ne_dkLb : dkN2 ≠ dkLb := by decide
@[simp] theorem dks2_dkLb_ne_dkN2 : dkLb ≠ dkN2 := by decide
@[simp] theorem dks2_dkN2_ne_dkR : dkN2 ≠ dkR := by decide
@[simp] theorem dks2_dkR_ne_dkN2 : dkR ≠ dkN2 := by decide
@[simp] theorem dks2_dkN2_ne_dkT : dkN2 ≠ dkT := by decide
@[simp] theorem dks2_dkT_ne_dkN2 : dkT ≠ dkN2 := by decide
@[simp] theorem dks2_dkN2_ne_dkBb : dkN2 ≠ dkBb := by decide
@[simp] theorem dks2_dkBb_ne_dkN2 : dkBb ≠ dkN2 := by decide
@[simp] theorem dks2_dkN2_ne_dkE : dkN2 ≠ dkE := by decide
@[simp] theorem dks2_dkE_ne_dkN2 : dkE ≠ dkN2 := by decide
@[simp] theorem dks2_dkU2_ne_dkI1 : dkU2 ≠ dkI1 := by decide
@[simp] theorem dks2_dkU2_ne_dkI2 : dkU2 ≠ dkI2 := by decide
@[simp] theorem dks2_dkU2_ne_dkN1 : dkU2 ≠ dkN1 := by decide
@[simp] theorem dks2_dkU2_ne_dkU1 : dkU2 ≠ dkU1 := by decide
@[simp] theorem dks2_dkU2_ne_dkN2 : dkU2 ≠ dkN2 := by decide
@[simp] theorem dks2_dkU2_ne_dkL : dkU2 ≠ dkL := by decide
@[simp] theorem dks2_dkU2_ne_dkXa : dkU2 ≠ dkXa := by decide
@[simp] theorem dks2_dkU2_ne_dkXb : dkU2 ≠ dkXb := by decide
@[simp] theorem dks2_dkU2_ne_dkLa2 : dkU2 ≠ dkLa2 := by decide
@[simp] theorem dks2_dkU2_ne_dkLb2 : dkU2 ≠ dkLb2 := by decide
@[simp] theorem dks2_dkU2_ne_dkFa : dkU2 ≠ dkFa := by decide
@[simp] theorem dks2_dkU2_ne_dkFb : dkU2 ≠ dkFb := by decide
@[simp] theorem dks2_dkU2_ne_dkQ : dkU2 ≠ dkQ := by decide
@[simp] theorem dks2_dkU2_ne_dkDl : dkU2 ≠ dkDl := by decide
@[simp] theorem dks2_dkU2_ne_dkW0 : dkU2 ≠ dkW0 := by decide
@[simp] theorem dks2_dkU2_ne_dkFo : dkU2 ≠ dkFo := by decide
@[simp] theorem dks2_dkU2_ne_dkCo : dkU2 ≠ dkCo := by decide
@[simp] theorem dks2_dkU2_ne_dkUo : dkU2 ≠ dkUo := by decide
@[simp] theorem dks2_dkU2_ne_dkEl : dkU2 ≠ dkEl := by decide
@[simp] theorem dks2_dkU2_ne_dkSl : dkU2 ≠ dkSl := by decide
@[simp] theorem dks2_dkU2_ne_dkLt : dkU2 ≠ dkLt := by decide
@[simp] theorem dks2_dkU2_ne_dkC : dkU2 ≠ dkC := by decide
@[simp] theorem dks2_dkU2_ne_dkR2 : dkU2 ≠ dkR2 := by decide
@[simp] theorem dks2_dkU2_ne_lFl : dkU2 ≠ lFl := by decide
@[simp] theorem dks2_lFl_ne_dkU2 : lFl ≠ dkU2 := by decide
@[simp] theorem dks2_dkU2_ne_lDh : dkU2 ≠ lDh := by decide
@[simp] theorem dks2_lDh_ne_dkU2 : lDh ≠ dkU2 := by decide
@[simp] theorem dks2_dkU2_ne_lDt : dkU2 ≠ lDt := by decide
@[simp] theorem dks2_lDt_ne_dkU2 : lDt ≠ dkU2 := by decide
@[simp] theorem dks2_dkU2_ne_lDg : dkU2 ≠ lDg := by decide
@[simp] theorem dks2_lDg_ne_dkU2 : lDg ≠ dkU2 := by decide
@[simp] theorem dks2_dkU2_ne_lDi : dkU2 ≠ lDi := by decide
@[simp] theorem dks2_lDi_ne_dkU2 : lDi ≠ dkU2 := by decide
@[simp] theorem dks2_dkU2_ne_lRp : dkU2 ≠ lRp := by decide
@[simp] theorem dks2_lRp_ne_dkU2 : lRp ≠ dkU2 := by decide
@[simp] theorem dks2_dkU2_ne_lRn : dkU2 ≠ lRn := by decide
@[simp] theorem dks2_lRn_ne_dkU2 : lRn ≠ dkU2 := by decide
@[simp] theorem dks2_dkU2_ne_lFle : dkU2 ≠ lFle := by decide
@[simp] theorem dks2_lFle_ne_dkU2 : lFle ≠ dkU2 := by decide
@[simp] theorem dks2_dkU2_ne_lKb : dkU2 ≠ lKb := by decide
@[simp] theorem dks2_lKb_ne_dkU2 : lKb ≠ dkU2 := by decide
@[simp] theorem dks2_dkU2_ne_lDir : dkU2 ≠ lDir := by decide
@[simp] theorem dks2_lDir_ne_dkU2 : lDir ≠ dkU2 := by decide
@[simp] theorem dks2_dkU2_ne_lFln : dkU2 ≠ lFln := by decide
@[simp] theorem dks2_lFln_ne_dkU2 : lFln ≠ dkU2 := by decide
@[simp] theorem dks2_dkU2_ne_lFll : dkU2 ≠ lFll := by decide
@[simp] theorem dks2_lFll_ne_dkU2 : lFll ≠ dkU2 := by decide
@[simp] theorem dks2_dkU2_ne_lFls : dkU2 ≠ lFls := by decide
@[simp] theorem dks2_lFls_ne_dkU2 : lFls ≠ dkU2 := by decide
@[simp] theorem dks2_dkU2_ne_kFu : dkU2 ≠ kFu := by decide
@[simp] theorem dks2_kFu_ne_dkU2 : kFu ≠ dkU2 := by decide
@[simp] theorem dks2_dkU2_ne_kD : dkU2 ≠ kD := by decide
@[simp] theorem dks2_kD_ne_dkU2 : kD ≠ dkU2 := by decide
@[simp] theorem dks2_dkU2_ne_dkA : dkU2 ≠ dkA := by decide
@[simp] theorem dks2_dkA_ne_dkU2 : dkA ≠ dkU2 := by decide
@[simp] theorem dks2_dkU2_ne_dkB : dkU2 ≠ dkB := by decide
@[simp] theorem dks2_dkB_ne_dkU2 : dkB ≠ dkU2 := by decide
@[simp] theorem dks2_dkU2_ne_dkPa : dkU2 ≠ dkPa := by decide
@[simp] theorem dks2_dkPa_ne_dkU2 : dkPa ≠ dkU2 := by decide
@[simp] theorem dks2_dkU2_ne_dkGa : dkU2 ≠ dkGa := by decide
@[simp] theorem dks2_dkGa_ne_dkU2 : dkGa ≠ dkU2 := by decide
@[simp] theorem dks2_dkU2_ne_dkLa : dkU2 ≠ dkLa := by decide
@[simp] theorem dks2_dkLa_ne_dkU2 : dkLa ≠ dkU2 := by decide
@[simp] theorem dks2_dkU2_ne_dkPb : dkU2 ≠ dkPb := by decide
@[simp] theorem dks2_dkPb_ne_dkU2 : dkPb ≠ dkU2 := by decide
@[simp] theorem dks2_dkU2_ne_dkGb : dkU2 ≠ dkGb := by decide
@[simp] theorem dks2_dkGb_ne_dkU2 : dkGb ≠ dkU2 := by decide
@[simp] theorem dks2_dkU2_ne_dkLb : dkU2 ≠ dkLb := by decide
@[simp] theorem dks2_dkLb_ne_dkU2 : dkLb ≠ dkU2 := by decide
@[simp] theorem dks2_dkU2_ne_dkR : dkU2 ≠ dkR := by decide
@[simp] theorem dks2_dkR_ne_dkU2 : dkR ≠ dkU2 := by decide
@[simp] theorem dks2_dkU2_ne_dkT : dkU2 ≠ dkT := by decide
@[simp] theorem dks2_dkT_ne_dkU2 : dkT ≠ dkU2 := by decide
@[simp] theorem dks2_dkU2_ne_dkBb : dkU2 ≠ dkBb := by decide
@[simp] theorem dks2_dkBb_ne_dkU2 : dkBb ≠ dkU2 := by decide
@[simp] theorem dks2_dkU2_ne_dkE : dkU2 ≠ dkE := by decide
@[simp] theorem dks2_dkE_ne_dkU2 : dkE ≠ dkU2 := by decide
@[simp] theorem dks2_dkL_ne_dkI1 : dkL ≠ dkI1 := by decide
@[simp] theorem dks2_dkL_ne_dkI2 : dkL ≠ dkI2 := by decide
@[simp] theorem dks2_dkL_ne_dkN1 : dkL ≠ dkN1 := by decide
@[simp] theorem dks2_dkL_ne_dkU1 : dkL ≠ dkU1 := by decide
@[simp] theorem dks2_dkL_ne_dkN2 : dkL ≠ dkN2 := by decide
@[simp] theorem dks2_dkL_ne_dkU2 : dkL ≠ dkU2 := by decide
@[simp] theorem dks2_dkL_ne_dkXa : dkL ≠ dkXa := by decide
@[simp] theorem dks2_dkL_ne_dkXb : dkL ≠ dkXb := by decide
@[simp] theorem dks2_dkL_ne_dkLa2 : dkL ≠ dkLa2 := by decide
@[simp] theorem dks2_dkL_ne_dkLb2 : dkL ≠ dkLb2 := by decide
@[simp] theorem dks2_dkL_ne_dkFa : dkL ≠ dkFa := by decide
@[simp] theorem dks2_dkL_ne_dkFb : dkL ≠ dkFb := by decide
@[simp] theorem dks2_dkL_ne_dkQ : dkL ≠ dkQ := by decide
@[simp] theorem dks2_dkL_ne_dkDl : dkL ≠ dkDl := by decide
@[simp] theorem dks2_dkL_ne_dkW0 : dkL ≠ dkW0 := by decide
@[simp] theorem dks2_dkL_ne_dkFo : dkL ≠ dkFo := by decide
@[simp] theorem dks2_dkL_ne_dkCo : dkL ≠ dkCo := by decide
@[simp] theorem dks2_dkL_ne_dkUo : dkL ≠ dkUo := by decide
@[simp] theorem dks2_dkL_ne_dkEl : dkL ≠ dkEl := by decide
@[simp] theorem dks2_dkL_ne_dkSl : dkL ≠ dkSl := by decide
@[simp] theorem dks2_dkL_ne_dkLt : dkL ≠ dkLt := by decide
@[simp] theorem dks2_dkL_ne_dkC : dkL ≠ dkC := by decide
@[simp] theorem dks2_dkL_ne_dkR2 : dkL ≠ dkR2 := by decide
@[simp] theorem dks2_dkL_ne_lFl : dkL ≠ lFl := by decide
@[simp] theorem dks2_lFl_ne_dkL : lFl ≠ dkL := by decide
@[simp] theorem dks2_dkL_ne_lDh : dkL ≠ lDh := by decide
@[simp] theorem dks2_lDh_ne_dkL : lDh ≠ dkL := by decide
@[simp] theorem dks2_dkL_ne_lDt : dkL ≠ lDt := by decide
@[simp] theorem dks2_lDt_ne_dkL : lDt ≠ dkL := by decide
@[simp] theorem dks2_dkL_ne_lDg : dkL ≠ lDg := by decide
@[simp] theorem dks2_lDg_ne_dkL : lDg ≠ dkL := by decide
@[simp] theorem dks2_dkL_ne_lDi : dkL ≠ lDi := by decide
@[simp] theorem dks2_lDi_ne_dkL : lDi ≠ dkL := by decide
@[simp] theorem dks2_dkL_ne_lRp : dkL ≠ lRp := by decide
@[simp] theorem dks2_lRp_ne_dkL : lRp ≠ dkL := by decide
@[simp] theorem dks2_dkL_ne_lRn : dkL ≠ lRn := by decide
@[simp] theorem dks2_lRn_ne_dkL : lRn ≠ dkL := by decide
@[simp] theorem dks2_dkL_ne_lFle : dkL ≠ lFle := by decide
@[simp] theorem dks2_lFle_ne_dkL : lFle ≠ dkL := by decide
@[simp] theorem dks2_dkL_ne_lKb : dkL ≠ lKb := by decide
@[simp] theorem dks2_lKb_ne_dkL : lKb ≠ dkL := by decide
@[simp] theorem dks2_dkL_ne_lDir : dkL ≠ lDir := by decide
@[simp] theorem dks2_lDir_ne_dkL : lDir ≠ dkL := by decide
@[simp] theorem dks2_dkL_ne_lFln : dkL ≠ lFln := by decide
@[simp] theorem dks2_lFln_ne_dkL : lFln ≠ dkL := by decide
@[simp] theorem dks2_dkL_ne_lFll : dkL ≠ lFll := by decide
@[simp] theorem dks2_lFll_ne_dkL : lFll ≠ dkL := by decide
@[simp] theorem dks2_dkL_ne_lFls : dkL ≠ lFls := by decide
@[simp] theorem dks2_lFls_ne_dkL : lFls ≠ dkL := by decide
@[simp] theorem dks2_dkL_ne_kFu : dkL ≠ kFu := by decide
@[simp] theorem dks2_kFu_ne_dkL : kFu ≠ dkL := by decide
@[simp] theorem dks2_dkL_ne_kD : dkL ≠ kD := by decide
@[simp] theorem dks2_kD_ne_dkL : kD ≠ dkL := by decide
@[simp] theorem dks2_dkL_ne_dkA : dkL ≠ dkA := by decide
@[simp] theorem dks2_dkA_ne_dkL : dkA ≠ dkL := by decide
@[simp] theorem dks2_dkL_ne_dkB : dkL ≠ dkB := by decide
@[simp] theorem dks2_dkB_ne_dkL : dkB ≠ dkL := by decide
@[simp] theorem dks2_dkL_ne_dkPa : dkL ≠ dkPa := by decide
@[simp] theorem dks2_dkPa_ne_dkL : dkPa ≠ dkL := by decide
@[simp] theorem dks2_dkL_ne_dkGa : dkL ≠ dkGa := by decide
@[simp] theorem dks2_dkGa_ne_dkL : dkGa ≠ dkL := by decide
@[simp] theorem dks2_dkL_ne_dkLa : dkL ≠ dkLa := by decide
@[simp] theorem dks2_dkLa_ne_dkL : dkLa ≠ dkL := by decide
@[simp] theorem dks2_dkL_ne_dkPb : dkL ≠ dkPb := by decide
@[simp] theorem dks2_dkPb_ne_dkL : dkPb ≠ dkL := by decide
@[simp] theorem dks2_dkL_ne_dkGb : dkL ≠ dkGb := by decide
@[simp] theorem dks2_dkGb_ne_dkL : dkGb ≠ dkL := by decide
@[simp] theorem dks2_dkL_ne_dkLb : dkL ≠ dkLb := by decide
@[simp] theorem dks2_dkLb_ne_dkL : dkLb ≠ dkL := by decide
@[simp] theorem dks2_dkL_ne_dkR : dkL ≠ dkR := by decide
@[simp] theorem dks2_dkR_ne_dkL : dkR ≠ dkL := by decide
@[simp] theorem dks2_dkL_ne_dkT : dkL ≠ dkT := by decide
@[simp] theorem dks2_dkT_ne_dkL : dkT ≠ dkL := by decide
@[simp] theorem dks2_dkL_ne_dkBb : dkL ≠ dkBb := by decide
@[simp] theorem dks2_dkBb_ne_dkL : dkBb ≠ dkL := by decide
@[simp] theorem dks2_dkL_ne_dkE : dkL ≠ dkE := by decide
@[simp] theorem dks2_dkE_ne_dkL : dkE ≠ dkL := by decide
@[simp] theorem dks2_dkXa_ne_dkI1 : dkXa ≠ dkI1 := by decide
@[simp] theorem dks2_dkXa_ne_dkI2 : dkXa ≠ dkI2 := by decide
@[simp] theorem dks2_dkXa_ne_dkN1 : dkXa ≠ dkN1 := by decide
@[simp] theorem dks2_dkXa_ne_dkU1 : dkXa ≠ dkU1 := by decide
@[simp] theorem dks2_dkXa_ne_dkN2 : dkXa ≠ dkN2 := by decide
@[simp] theorem dks2_dkXa_ne_dkU2 : dkXa ≠ dkU2 := by decide
@[simp] theorem dks2_dkXa_ne_dkL : dkXa ≠ dkL := by decide
@[simp] theorem dks2_dkXa_ne_dkXb : dkXa ≠ dkXb := by decide
@[simp] theorem dks2_dkXa_ne_dkLa2 : dkXa ≠ dkLa2 := by decide
@[simp] theorem dks2_dkXa_ne_dkLb2 : dkXa ≠ dkLb2 := by decide
@[simp] theorem dks2_dkXa_ne_dkFa : dkXa ≠ dkFa := by decide
@[simp] theorem dks2_dkXa_ne_dkFb : dkXa ≠ dkFb := by decide
@[simp] theorem dks2_dkXa_ne_dkQ : dkXa ≠ dkQ := by decide
@[simp] theorem dks2_dkXa_ne_dkDl : dkXa ≠ dkDl := by decide
@[simp] theorem dks2_dkXa_ne_dkW0 : dkXa ≠ dkW0 := by decide
@[simp] theorem dks2_dkXa_ne_dkFo : dkXa ≠ dkFo := by decide
@[simp] theorem dks2_dkXa_ne_dkCo : dkXa ≠ dkCo := by decide
@[simp] theorem dks2_dkXa_ne_dkUo : dkXa ≠ dkUo := by decide
@[simp] theorem dks2_dkXa_ne_dkEl : dkXa ≠ dkEl := by decide
@[simp] theorem dks2_dkXa_ne_dkSl : dkXa ≠ dkSl := by decide
@[simp] theorem dks2_dkXa_ne_dkLt : dkXa ≠ dkLt := by decide
@[simp] theorem dks2_dkXa_ne_dkC : dkXa ≠ dkC := by decide
@[simp] theorem dks2_dkXa_ne_dkR2 : dkXa ≠ dkR2 := by decide
@[simp] theorem dks2_dkXa_ne_lFl : dkXa ≠ lFl := by decide
@[simp] theorem dks2_lFl_ne_dkXa : lFl ≠ dkXa := by decide
@[simp] theorem dks2_dkXa_ne_lDh : dkXa ≠ lDh := by decide
@[simp] theorem dks2_lDh_ne_dkXa : lDh ≠ dkXa := by decide
@[simp] theorem dks2_dkXa_ne_lDt : dkXa ≠ lDt := by decide
@[simp] theorem dks2_lDt_ne_dkXa : lDt ≠ dkXa := by decide
@[simp] theorem dks2_dkXa_ne_lDg : dkXa ≠ lDg := by decide
@[simp] theorem dks2_lDg_ne_dkXa : lDg ≠ dkXa := by decide
@[simp] theorem dks2_dkXa_ne_lDi : dkXa ≠ lDi := by decide
@[simp] theorem dks2_lDi_ne_dkXa : lDi ≠ dkXa := by decide
@[simp] theorem dks2_dkXa_ne_lRp : dkXa ≠ lRp := by decide
@[simp] theorem dks2_lRp_ne_dkXa : lRp ≠ dkXa := by decide
@[simp] theorem dks2_dkXa_ne_lRn : dkXa ≠ lRn := by decide
@[simp] theorem dks2_lRn_ne_dkXa : lRn ≠ dkXa := by decide
@[simp] theorem dks2_dkXa_ne_lFle : dkXa ≠ lFle := by decide
@[simp] theorem dks2_lFle_ne_dkXa : lFle ≠ dkXa := by decide
@[simp] theorem dks2_dkXa_ne_lKb : dkXa ≠ lKb := by decide
@[simp] theorem dks2_lKb_ne_dkXa : lKb ≠ dkXa := by decide
@[simp] theorem dks2_dkXa_ne_lDir : dkXa ≠ lDir := by decide
@[simp] theorem dks2_lDir_ne_dkXa : lDir ≠ dkXa := by decide
@[simp] theorem dks2_dkXa_ne_lFln : dkXa ≠ lFln := by decide
@[simp] theorem dks2_lFln_ne_dkXa : lFln ≠ dkXa := by decide
@[simp] theorem dks2_dkXa_ne_lFll : dkXa ≠ lFll := by decide
@[simp] theorem dks2_lFll_ne_dkXa : lFll ≠ dkXa := by decide
@[simp] theorem dks2_dkXa_ne_lFls : dkXa ≠ lFls := by decide
@[simp] theorem dks2_lFls_ne_dkXa : lFls ≠ dkXa := by decide
@[simp] theorem dks2_dkXa_ne_kFu : dkXa ≠ kFu := by decide
@[simp] theorem dks2_kFu_ne_dkXa : kFu ≠ dkXa := by decide
@[simp] theorem dks2_dkXa_ne_kD : dkXa ≠ kD := by decide
@[simp] theorem dks2_kD_ne_dkXa : kD ≠ dkXa := by decide
@[simp] theorem dks2_dkXa_ne_dkA : dkXa ≠ dkA := by decide
@[simp] theorem dks2_dkA_ne_dkXa : dkA ≠ dkXa := by decide
@[simp] theorem dks2_dkXa_ne_dkB : dkXa ≠ dkB := by decide
@[simp] theorem dks2_dkB_ne_dkXa : dkB ≠ dkXa := by decide
@[simp] theorem dks2_dkXa_ne_dkPa : dkXa ≠ dkPa := by decide
@[simp] theorem dks2_dkPa_ne_dkXa : dkPa ≠ dkXa := by decide
@[simp] theorem dks2_dkXa_ne_dkGa : dkXa ≠ dkGa := by decide
@[simp] theorem dks2_dkGa_ne_dkXa : dkGa ≠ dkXa := by decide
@[simp] theorem dks2_dkXa_ne_dkLa : dkXa ≠ dkLa := by decide
@[simp] theorem dks2_dkLa_ne_dkXa : dkLa ≠ dkXa := by decide
@[simp] theorem dks2_dkXa_ne_dkPb : dkXa ≠ dkPb := by decide
@[simp] theorem dks2_dkPb_ne_dkXa : dkPb ≠ dkXa := by decide
@[simp] theorem dks2_dkXa_ne_dkGb : dkXa ≠ dkGb := by decide
@[simp] theorem dks2_dkGb_ne_dkXa : dkGb ≠ dkXa := by decide
@[simp] theorem dks2_dkXa_ne_dkLb : dkXa ≠ dkLb := by decide
@[simp] theorem dks2_dkLb_ne_dkXa : dkLb ≠ dkXa := by decide
@[simp] theorem dks2_dkXa_ne_dkR : dkXa ≠ dkR := by decide
@[simp] theorem dks2_dkR_ne_dkXa : dkR ≠ dkXa := by decide
@[simp] theorem dks2_dkXa_ne_dkT : dkXa ≠ dkT := by decide
@[simp] theorem dks2_dkT_ne_dkXa : dkT ≠ dkXa := by decide
@[simp] theorem dks2_dkXa_ne_dkBb : dkXa ≠ dkBb := by decide
@[simp] theorem dks2_dkBb_ne_dkXa : dkBb ≠ dkXa := by decide
@[simp] theorem dks2_dkXa_ne_dkE : dkXa ≠ dkE := by decide
@[simp] theorem dks2_dkE_ne_dkXa : dkE ≠ dkXa := by decide
@[simp] theorem dks2_dkXb_ne_dkI1 : dkXb ≠ dkI1 := by decide
@[simp] theorem dks2_dkXb_ne_dkI2 : dkXb ≠ dkI2 := by decide
@[simp] theorem dks2_dkXb_ne_dkN1 : dkXb ≠ dkN1 := by decide
@[simp] theorem dks2_dkXb_ne_dkU1 : dkXb ≠ dkU1 := by decide
@[simp] theorem dks2_dkXb_ne_dkN2 : dkXb ≠ dkN2 := by decide
@[simp] theorem dks2_dkXb_ne_dkU2 : dkXb ≠ dkU2 := by decide
@[simp] theorem dks2_dkXb_ne_dkL : dkXb ≠ dkL := by decide
@[simp] theorem dks2_dkXb_ne_dkXa : dkXb ≠ dkXa := by decide
@[simp] theorem dks2_dkXb_ne_dkLa2 : dkXb ≠ dkLa2 := by decide
@[simp] theorem dks2_dkXb_ne_dkLb2 : dkXb ≠ dkLb2 := by decide
@[simp] theorem dks2_dkXb_ne_dkFa : dkXb ≠ dkFa := by decide
@[simp] theorem dks2_dkXb_ne_dkFb : dkXb ≠ dkFb := by decide
@[simp] theorem dks2_dkXb_ne_dkQ : dkXb ≠ dkQ := by decide
@[simp] theorem dks2_dkXb_ne_dkDl : dkXb ≠ dkDl := by decide
@[simp] theorem dks2_dkXb_ne_dkW0 : dkXb ≠ dkW0 := by decide
@[simp] theorem dks2_dkXb_ne_dkFo : dkXb ≠ dkFo := by decide
@[simp] theorem dks2_dkXb_ne_dkCo : dkXb ≠ dkCo := by decide
@[simp] theorem dks2_dkXb_ne_dkUo : dkXb ≠ dkUo := by decide
@[simp] theorem dks2_dkXb_ne_dkEl : dkXb ≠ dkEl := by decide
@[simp] theorem dks2_dkXb_ne_dkSl : dkXb ≠ dkSl := by decide
@[simp] theorem dks2_dkXb_ne_dkLt : dkXb ≠ dkLt := by decide
@[simp] theorem dks2_dkXb_ne_dkC : dkXb ≠ dkC := by decide
@[simp] theorem dks2_dkXb_ne_dkR2 : dkXb ≠ dkR2 := by decide
@[simp] theorem dks2_dkXb_ne_lFl : dkXb ≠ lFl := by decide
@[simp] theorem dks2_lFl_ne_dkXb : lFl ≠ dkXb := by decide
@[simp] theorem dks2_dkXb_ne_lDh : dkXb ≠ lDh := by decide
@[simp] theorem dks2_lDh_ne_dkXb : lDh ≠ dkXb := by decide
@[simp] theorem dks2_dkXb_ne_lDt : dkXb ≠ lDt := by decide
@[simp] theorem dks2_lDt_ne_dkXb : lDt ≠ dkXb := by decide
@[simp] theorem dks2_dkXb_ne_lDg : dkXb ≠ lDg := by decide
@[simp] theorem dks2_lDg_ne_dkXb : lDg ≠ dkXb := by decide
@[simp] theorem dks2_dkXb_ne_lDi : dkXb ≠ lDi := by decide
@[simp] theorem dks2_lDi_ne_dkXb : lDi ≠ dkXb := by decide
@[simp] theorem dks2_dkXb_ne_lRp : dkXb ≠ lRp := by decide
@[simp] theorem dks2_lRp_ne_dkXb : lRp ≠ dkXb := by decide
@[simp] theorem dks2_dkXb_ne_lRn : dkXb ≠ lRn := by decide
@[simp] theorem dks2_lRn_ne_dkXb : lRn ≠ dkXb := by decide
@[simp] theorem dks2_dkXb_ne_lFle : dkXb ≠ lFle := by decide
@[simp] theorem dks2_lFle_ne_dkXb : lFle ≠ dkXb := by decide
@[simp] theorem dks2_dkXb_ne_lKb : dkXb ≠ lKb := by decide
@[simp] theorem dks2_lKb_ne_dkXb : lKb ≠ dkXb := by decide
@[simp] theorem dks2_dkXb_ne_lDir : dkXb ≠ lDir := by decide
@[simp] theorem dks2_lDir_ne_dkXb : lDir ≠ dkXb := by decide
@[simp] theorem dks2_dkXb_ne_lFln : dkXb ≠ lFln := by decide
@[simp] theorem dks2_lFln_ne_dkXb : lFln ≠ dkXb := by decide
@[simp] theorem dks2_dkXb_ne_lFll : dkXb ≠ lFll := by decide
@[simp] theorem dks2_lFll_ne_dkXb : lFll ≠ dkXb := by decide
@[simp] theorem dks2_dkXb_ne_lFls : dkXb ≠ lFls := by decide
@[simp] theorem dks2_lFls_ne_dkXb : lFls ≠ dkXb := by decide
@[simp] theorem dks2_dkXb_ne_kFu : dkXb ≠ kFu := by decide
@[simp] theorem dks2_kFu_ne_dkXb : kFu ≠ dkXb := by decide
@[simp] theorem dks2_dkXb_ne_kD : dkXb ≠ kD := by decide
@[simp] theorem dks2_kD_ne_dkXb : kD ≠ dkXb := by decide
@[simp] theorem dks2_dkXb_ne_dkA : dkXb ≠ dkA := by decide
@[simp] theorem dks2_dkA_ne_dkXb : dkA ≠ dkXb := by decide
@[simp] theorem dks2_dkXb_ne_dkB : dkXb ≠ dkB := by decide
@[simp] theorem dks2_dkB_ne_dkXb : dkB ≠ dkXb := by decide
@[simp] theorem dks2_dkXb_ne_dkPa : dkXb ≠ dkPa := by decide
@[simp] theorem dks2_dkPa_ne_dkXb : dkPa ≠ dkXb := by decide
@[simp] theorem dks2_dkXb_ne_dkGa : dkXb ≠ dkGa := by decide
@[simp] theorem dks2_dkGa_ne_dkXb : dkGa ≠ dkXb := by decide
@[simp] theorem dks2_dkXb_ne_dkLa : dkXb ≠ dkLa := by decide
@[simp] theorem dks2_dkLa_ne_dkXb : dkLa ≠ dkXb := by decide
@[simp] theorem dks2_dkXb_ne_dkPb : dkXb ≠ dkPb := by decide
@[simp] theorem dks2_dkPb_ne_dkXb : dkPb ≠ dkXb := by decide
@[simp] theorem dks2_dkXb_ne_dkGb : dkXb ≠ dkGb := by decide
@[simp] theorem dks2_dkGb_ne_dkXb : dkGb ≠ dkXb := by decide
@[simp] theorem dks2_dkXb_ne_dkLb : dkXb ≠ dkLb := by decide
@[simp] theorem dks2_dkLb_ne_dkXb : dkLb ≠ dkXb := by decide
@[simp] theorem dks2_dkXb_ne_dkR : dkXb ≠ dkR := by decide
@[simp] theorem dks2_dkR_ne_dkXb : dkR ≠ dkXb := by decide
@[simp] theorem dks2_dkXb_ne_dkT : dkXb ≠ dkT := by decide
@[simp] theorem dks2_dkT_ne_dkXb : dkT ≠ dkXb := by decide
@[simp] theorem dks2_dkXb_ne_dkBb : dkXb ≠ dkBb := by decide
@[simp] theorem dks2_dkBb_ne_dkXb : dkBb ≠ dkXb := by decide
@[simp] theorem dks2_dkXb_ne_dkE : dkXb ≠ dkE := by decide
@[simp] theorem dks2_dkE_ne_dkXb : dkE ≠ dkXb := by decide
@[simp] theorem dks2_dkLa2_ne_dkI1 : dkLa2 ≠ dkI1 := by decide
@[simp] theorem dks2_dkLa2_ne_dkI2 : dkLa2 ≠ dkI2 := by decide
@[simp] theorem dks2_dkLa2_ne_dkN1 : dkLa2 ≠ dkN1 := by decide
@[simp] theorem dks2_dkLa2_ne_dkU1 : dkLa2 ≠ dkU1 := by decide
@[simp] theorem dks2_dkLa2_ne_dkN2 : dkLa2 ≠ dkN2 := by decide
@[simp] theorem dks2_dkLa2_ne_dkU2 : dkLa2 ≠ dkU2 := by decide
@[simp] theorem dks2_dkLa2_ne_dkL : dkLa2 ≠ dkL := by decide
@[simp] theorem dks2_dkLa2_ne_dkXa : dkLa2 ≠ dkXa := by decide
@[simp] theorem dks2_dkLa2_ne_dkXb : dkLa2 ≠ dkXb := by decide
@[simp] theorem dks2_dkLa2_ne_dkLb2 : dkLa2 ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLa2_ne_dkFa : dkLa2 ≠ dkFa := by decide
@[simp] theorem dks2_dkLa2_ne_dkFb : dkLa2 ≠ dkFb := by decide
@[simp] theorem dks2_dkLa2_ne_dkQ : dkLa2 ≠ dkQ := by decide
@[simp] theorem dks2_dkLa2_ne_dkDl : dkLa2 ≠ dkDl := by decide
@[simp] theorem dks2_dkLa2_ne_dkW0 : dkLa2 ≠ dkW0 := by decide
@[simp] theorem dks2_dkLa2_ne_dkFo : dkLa2 ≠ dkFo := by decide
@[simp] theorem dks2_dkLa2_ne_dkCo : dkLa2 ≠ dkCo := by decide
@[simp] theorem dks2_dkLa2_ne_dkUo : dkLa2 ≠ dkUo := by decide
@[simp] theorem dks2_dkLa2_ne_dkEl : dkLa2 ≠ dkEl := by decide
@[simp] theorem dks2_dkLa2_ne_dkSl : dkLa2 ≠ dkSl := by decide
@[simp] theorem dks2_dkLa2_ne_dkLt : dkLa2 ≠ dkLt := by decide
@[simp] theorem dks2_dkLa2_ne_dkC : dkLa2 ≠ dkC := by decide
@[simp] theorem dks2_dkLa2_ne_dkR2 : dkLa2 ≠ dkR2 := by decide
@[simp] theorem dks2_dkLa2_ne_lFl : dkLa2 ≠ lFl := by decide
@[simp] theorem dks2_lFl_ne_dkLa2 : lFl ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLa2_ne_lDh : dkLa2 ≠ lDh := by decide
@[simp] theorem dks2_lDh_ne_dkLa2 : lDh ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLa2_ne_lDt : dkLa2 ≠ lDt := by decide
@[simp] theorem dks2_lDt_ne_dkLa2 : lDt ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLa2_ne_lDg : dkLa2 ≠ lDg := by decide
@[simp] theorem dks2_lDg_ne_dkLa2 : lDg ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLa2_ne_lDi : dkLa2 ≠ lDi := by decide
@[simp] theorem dks2_lDi_ne_dkLa2 : lDi ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLa2_ne_lRp : dkLa2 ≠ lRp := by decide
@[simp] theorem dks2_lRp_ne_dkLa2 : lRp ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLa2_ne_lRn : dkLa2 ≠ lRn := by decide
@[simp] theorem dks2_lRn_ne_dkLa2 : lRn ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLa2_ne_lFle : dkLa2 ≠ lFle := by decide
@[simp] theorem dks2_lFle_ne_dkLa2 : lFle ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLa2_ne_lKb : dkLa2 ≠ lKb := by decide
@[simp] theorem dks2_lKb_ne_dkLa2 : lKb ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLa2_ne_lDir : dkLa2 ≠ lDir := by decide
@[simp] theorem dks2_lDir_ne_dkLa2 : lDir ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLa2_ne_lFln : dkLa2 ≠ lFln := by decide
@[simp] theorem dks2_lFln_ne_dkLa2 : lFln ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLa2_ne_lFll : dkLa2 ≠ lFll := by decide
@[simp] theorem dks2_lFll_ne_dkLa2 : lFll ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLa2_ne_lFls : dkLa2 ≠ lFls := by decide
@[simp] theorem dks2_lFls_ne_dkLa2 : lFls ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLa2_ne_kFu : dkLa2 ≠ kFu := by decide
@[simp] theorem dks2_kFu_ne_dkLa2 : kFu ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLa2_ne_kD : dkLa2 ≠ kD := by decide
@[simp] theorem dks2_kD_ne_dkLa2 : kD ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLa2_ne_dkA : dkLa2 ≠ dkA := by decide
@[simp] theorem dks2_dkA_ne_dkLa2 : dkA ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLa2_ne_dkB : dkLa2 ≠ dkB := by decide
@[simp] theorem dks2_dkB_ne_dkLa2 : dkB ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLa2_ne_dkPa : dkLa2 ≠ dkPa := by decide
@[simp] theorem dks2_dkPa_ne_dkLa2 : dkPa ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLa2_ne_dkGa : dkLa2 ≠ dkGa := by decide
@[simp] theorem dks2_dkGa_ne_dkLa2 : dkGa ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLa2_ne_dkLa : dkLa2 ≠ dkLa := by decide
@[simp] theorem dks2_dkLa_ne_dkLa2 : dkLa ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLa2_ne_dkPb : dkLa2 ≠ dkPb := by decide
@[simp] theorem dks2_dkPb_ne_dkLa2 : dkPb ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLa2_ne_dkGb : dkLa2 ≠ dkGb := by decide
@[simp] theorem dks2_dkGb_ne_dkLa2 : dkGb ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLa2_ne_dkLb : dkLa2 ≠ dkLb := by decide
@[simp] theorem dks2_dkLb_ne_dkLa2 : dkLb ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLa2_ne_dkR : dkLa2 ≠ dkR := by decide
@[simp] theorem dks2_dkR_ne_dkLa2 : dkR ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLa2_ne_dkT : dkLa2 ≠ dkT := by decide
@[simp] theorem dks2_dkT_ne_dkLa2 : dkT ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLa2_ne_dkBb : dkLa2 ≠ dkBb := by decide
@[simp] theorem dks2_dkBb_ne_dkLa2 : dkBb ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLa2_ne_dkE : dkLa2 ≠ dkE := by decide
@[simp] theorem dks2_dkE_ne_dkLa2 : dkE ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLb2_ne_dkI1 : dkLb2 ≠ dkI1 := by decide
@[simp] theorem dks2_dkLb2_ne_dkI2 : dkLb2 ≠ dkI2 := by decide
@[simp] theorem dks2_dkLb2_ne_dkN1 : dkLb2 ≠ dkN1 := by decide
@[simp] theorem dks2_dkLb2_ne_dkU1 : dkLb2 ≠ dkU1 := by decide
@[simp] theorem dks2_dkLb2_ne_dkN2 : dkLb2 ≠ dkN2 := by decide
@[simp] theorem dks2_dkLb2_ne_dkU2 : dkLb2 ≠ dkU2 := by decide
@[simp] theorem dks2_dkLb2_ne_dkL : dkLb2 ≠ dkL := by decide
@[simp] theorem dks2_dkLb2_ne_dkXa : dkLb2 ≠ dkXa := by decide
@[simp] theorem dks2_dkLb2_ne_dkXb : dkLb2 ≠ dkXb := by decide
@[simp] theorem dks2_dkLb2_ne_dkLa2 : dkLb2 ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLb2_ne_dkFa : dkLb2 ≠ dkFa := by decide
@[simp] theorem dks2_dkLb2_ne_dkFb : dkLb2 ≠ dkFb := by decide
@[simp] theorem dks2_dkLb2_ne_dkQ : dkLb2 ≠ dkQ := by decide
@[simp] theorem dks2_dkLb2_ne_dkDl : dkLb2 ≠ dkDl := by decide
@[simp] theorem dks2_dkLb2_ne_dkW0 : dkLb2 ≠ dkW0 := by decide
@[simp] theorem dks2_dkLb2_ne_dkFo : dkLb2 ≠ dkFo := by decide
@[simp] theorem dks2_dkLb2_ne_dkCo : dkLb2 ≠ dkCo := by decide
@[simp] theorem dks2_dkLb2_ne_dkUo : dkLb2 ≠ dkUo := by decide
@[simp] theorem dks2_dkLb2_ne_dkEl : dkLb2 ≠ dkEl := by decide
@[simp] theorem dks2_dkLb2_ne_dkSl : dkLb2 ≠ dkSl := by decide
@[simp] theorem dks2_dkLb2_ne_dkLt : dkLb2 ≠ dkLt := by decide
@[simp] theorem dks2_dkLb2_ne_dkC : dkLb2 ≠ dkC := by decide
@[simp] theorem dks2_dkLb2_ne_dkR2 : dkLb2 ≠ dkR2 := by decide
@[simp] theorem dks2_dkLb2_ne_lFl : dkLb2 ≠ lFl := by decide
@[simp] theorem dks2_lFl_ne_dkLb2 : lFl ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLb2_ne_lDh : dkLb2 ≠ lDh := by decide
@[simp] theorem dks2_lDh_ne_dkLb2 : lDh ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLb2_ne_lDt : dkLb2 ≠ lDt := by decide
@[simp] theorem dks2_lDt_ne_dkLb2 : lDt ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLb2_ne_lDg : dkLb2 ≠ lDg := by decide
@[simp] theorem dks2_lDg_ne_dkLb2 : lDg ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLb2_ne_lDi : dkLb2 ≠ lDi := by decide
@[simp] theorem dks2_lDi_ne_dkLb2 : lDi ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLb2_ne_lRp : dkLb2 ≠ lRp := by decide
@[simp] theorem dks2_lRp_ne_dkLb2 : lRp ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLb2_ne_lRn : dkLb2 ≠ lRn := by decide
@[simp] theorem dks2_lRn_ne_dkLb2 : lRn ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLb2_ne_lFle : dkLb2 ≠ lFle := by decide
@[simp] theorem dks2_lFle_ne_dkLb2 : lFle ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLb2_ne_lKb : dkLb2 ≠ lKb := by decide
@[simp] theorem dks2_lKb_ne_dkLb2 : lKb ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLb2_ne_lDir : dkLb2 ≠ lDir := by decide
@[simp] theorem dks2_lDir_ne_dkLb2 : lDir ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLb2_ne_lFln : dkLb2 ≠ lFln := by decide
@[simp] theorem dks2_lFln_ne_dkLb2 : lFln ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLb2_ne_lFll : dkLb2 ≠ lFll := by decide
@[simp] theorem dks2_lFll_ne_dkLb2 : lFll ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLb2_ne_lFls : dkLb2 ≠ lFls := by decide
@[simp] theorem dks2_lFls_ne_dkLb2 : lFls ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLb2_ne_kFu : dkLb2 ≠ kFu := by decide
@[simp] theorem dks2_kFu_ne_dkLb2 : kFu ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLb2_ne_kD : dkLb2 ≠ kD := by decide
@[simp] theorem dks2_kD_ne_dkLb2 : kD ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLb2_ne_dkA : dkLb2 ≠ dkA := by decide
@[simp] theorem dks2_dkA_ne_dkLb2 : dkA ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLb2_ne_dkB : dkLb2 ≠ dkB := by decide
@[simp] theorem dks2_dkB_ne_dkLb2 : dkB ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLb2_ne_dkPa : dkLb2 ≠ dkPa := by decide
@[simp] theorem dks2_dkPa_ne_dkLb2 : dkPa ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLb2_ne_dkGa : dkLb2 ≠ dkGa := by decide
@[simp] theorem dks2_dkGa_ne_dkLb2 : dkGa ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLb2_ne_dkLa : dkLb2 ≠ dkLa := by decide
@[simp] theorem dks2_dkLa_ne_dkLb2 : dkLa ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLb2_ne_dkPb : dkLb2 ≠ dkPb := by decide
@[simp] theorem dks2_dkPb_ne_dkLb2 : dkPb ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLb2_ne_dkGb : dkLb2 ≠ dkGb := by decide
@[simp] theorem dks2_dkGb_ne_dkLb2 : dkGb ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLb2_ne_dkLb : dkLb2 ≠ dkLb := by decide
@[simp] theorem dks2_dkLb_ne_dkLb2 : dkLb ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLb2_ne_dkR : dkLb2 ≠ dkR := by decide
@[simp] theorem dks2_dkR_ne_dkLb2 : dkR ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLb2_ne_dkT : dkLb2 ≠ dkT := by decide
@[simp] theorem dks2_dkT_ne_dkLb2 : dkT ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLb2_ne_dkBb : dkLb2 ≠ dkBb := by decide
@[simp] theorem dks2_dkBb_ne_dkLb2 : dkBb ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLb2_ne_dkE : dkLb2 ≠ dkE := by decide
@[simp] theorem dks2_dkE_ne_dkLb2 : dkE ≠ dkLb2 := by decide
@[simp] theorem dks2_dkFa_ne_dkI1 : dkFa ≠ dkI1 := by decide
@[simp] theorem dks2_dkFa_ne_dkI2 : dkFa ≠ dkI2 := by decide
@[simp] theorem dks2_dkFa_ne_dkN1 : dkFa ≠ dkN1 := by decide
@[simp] theorem dks2_dkFa_ne_dkU1 : dkFa ≠ dkU1 := by decide
@[simp] theorem dks2_dkFa_ne_dkN2 : dkFa ≠ dkN2 := by decide
@[simp] theorem dks2_dkFa_ne_dkU2 : dkFa ≠ dkU2 := by decide
@[simp] theorem dks2_dkFa_ne_dkL : dkFa ≠ dkL := by decide
@[simp] theorem dks2_dkFa_ne_dkXa : dkFa ≠ dkXa := by decide
@[simp] theorem dks2_dkFa_ne_dkXb : dkFa ≠ dkXb := by decide
@[simp] theorem dks2_dkFa_ne_dkLa2 : dkFa ≠ dkLa2 := by decide
@[simp] theorem dks2_dkFa_ne_dkLb2 : dkFa ≠ dkLb2 := by decide
@[simp] theorem dks2_dkFa_ne_dkFb : dkFa ≠ dkFb := by decide
@[simp] theorem dks2_dkFa_ne_dkQ : dkFa ≠ dkQ := by decide
@[simp] theorem dks2_dkFa_ne_dkDl : dkFa ≠ dkDl := by decide
@[simp] theorem dks2_dkFa_ne_dkW0 : dkFa ≠ dkW0 := by decide
@[simp] theorem dks2_dkFa_ne_dkFo : dkFa ≠ dkFo := by decide
@[simp] theorem dks2_dkFa_ne_dkCo : dkFa ≠ dkCo := by decide
@[simp] theorem dks2_dkFa_ne_dkUo : dkFa ≠ dkUo := by decide
@[simp] theorem dks2_dkFa_ne_dkEl : dkFa ≠ dkEl := by decide
@[simp] theorem dks2_dkFa_ne_dkSl : dkFa ≠ dkSl := by decide
@[simp] theorem dks2_dkFa_ne_dkLt : dkFa ≠ dkLt := by decide
@[simp] theorem dks2_dkFa_ne_dkC : dkFa ≠ dkC := by decide
@[simp] theorem dks2_dkFa_ne_dkR2 : dkFa ≠ dkR2 := by decide
@[simp] theorem dks2_dkFa_ne_lFl : dkFa ≠ lFl := by decide
@[simp] theorem dks2_lFl_ne_dkFa : lFl ≠ dkFa := by decide
@[simp] theorem dks2_dkFa_ne_lDh : dkFa ≠ lDh := by decide
@[simp] theorem dks2_lDh_ne_dkFa : lDh ≠ dkFa := by decide
@[simp] theorem dks2_dkFa_ne_lDt : dkFa ≠ lDt := by decide
@[simp] theorem dks2_lDt_ne_dkFa : lDt ≠ dkFa := by decide
@[simp] theorem dks2_dkFa_ne_lDg : dkFa ≠ lDg := by decide
@[simp] theorem dks2_lDg_ne_dkFa : lDg ≠ dkFa := by decide
@[simp] theorem dks2_dkFa_ne_lDi : dkFa ≠ lDi := by decide
@[simp] theorem dks2_lDi_ne_dkFa : lDi ≠ dkFa := by decide
@[simp] theorem dks2_dkFa_ne_lRp : dkFa ≠ lRp := by decide
@[simp] theorem dks2_lRp_ne_dkFa : lRp ≠ dkFa := by decide
@[simp] theorem dks2_dkFa_ne_lRn : dkFa ≠ lRn := by decide
@[simp] theorem dks2_lRn_ne_dkFa : lRn ≠ dkFa := by decide
@[simp] theorem dks2_dkFa_ne_lFle : dkFa ≠ lFle := by decide
@[simp] theorem dks2_lFle_ne_dkFa : lFle ≠ dkFa := by decide
@[simp] theorem dks2_dkFa_ne_lKb : dkFa ≠ lKb := by decide
@[simp] theorem dks2_lKb_ne_dkFa : lKb ≠ dkFa := by decide
@[simp] theorem dks2_dkFa_ne_lDir : dkFa ≠ lDir := by decide
@[simp] theorem dks2_lDir_ne_dkFa : lDir ≠ dkFa := by decide
@[simp] theorem dks2_dkFa_ne_lFln : dkFa ≠ lFln := by decide
@[simp] theorem dks2_lFln_ne_dkFa : lFln ≠ dkFa := by decide
@[simp] theorem dks2_dkFa_ne_lFll : dkFa ≠ lFll := by decide
@[simp] theorem dks2_lFll_ne_dkFa : lFll ≠ dkFa := by decide
@[simp] theorem dks2_dkFa_ne_lFls : dkFa ≠ lFls := by decide
@[simp] theorem dks2_lFls_ne_dkFa : lFls ≠ dkFa := by decide
@[simp] theorem dks2_dkFa_ne_kFu : dkFa ≠ kFu := by decide
@[simp] theorem dks2_kFu_ne_dkFa : kFu ≠ dkFa := by decide
@[simp] theorem dks2_dkFa_ne_kD : dkFa ≠ kD := by decide
@[simp] theorem dks2_kD_ne_dkFa : kD ≠ dkFa := by decide
@[simp] theorem dks2_dkFa_ne_dkA : dkFa ≠ dkA := by decide
@[simp] theorem dks2_dkA_ne_dkFa : dkA ≠ dkFa := by decide
@[simp] theorem dks2_dkFa_ne_dkB : dkFa ≠ dkB := by decide
@[simp] theorem dks2_dkB_ne_dkFa : dkB ≠ dkFa := by decide
@[simp] theorem dks2_dkFa_ne_dkPa : dkFa ≠ dkPa := by decide
@[simp] theorem dks2_dkPa_ne_dkFa : dkPa ≠ dkFa := by decide
@[simp] theorem dks2_dkFa_ne_dkGa : dkFa ≠ dkGa := by decide
@[simp] theorem dks2_dkGa_ne_dkFa : dkGa ≠ dkFa := by decide
@[simp] theorem dks2_dkFa_ne_dkLa : dkFa ≠ dkLa := by decide
@[simp] theorem dks2_dkLa_ne_dkFa : dkLa ≠ dkFa := by decide
@[simp] theorem dks2_dkFa_ne_dkPb : dkFa ≠ dkPb := by decide
@[simp] theorem dks2_dkPb_ne_dkFa : dkPb ≠ dkFa := by decide
@[simp] theorem dks2_dkFa_ne_dkGb : dkFa ≠ dkGb := by decide
@[simp] theorem dks2_dkGb_ne_dkFa : dkGb ≠ dkFa := by decide
@[simp] theorem dks2_dkFa_ne_dkLb : dkFa ≠ dkLb := by decide
@[simp] theorem dks2_dkLb_ne_dkFa : dkLb ≠ dkFa := by decide
@[simp] theorem dks2_dkFa_ne_dkR : dkFa ≠ dkR := by decide
@[simp] theorem dks2_dkR_ne_dkFa : dkR ≠ dkFa := by decide
@[simp] theorem dks2_dkFa_ne_dkT : dkFa ≠ dkT := by decide
@[simp] theorem dks2_dkT_ne_dkFa : dkT ≠ dkFa := by decide
@[simp] theorem dks2_dkFa_ne_dkBb : dkFa ≠ dkBb := by decide
@[simp] theorem dks2_dkBb_ne_dkFa : dkBb ≠ dkFa := by decide
@[simp] theorem dks2_dkFa_ne_dkE : dkFa ≠ dkE := by decide
@[simp] theorem dks2_dkE_ne_dkFa : dkE ≠ dkFa := by decide
@[simp] theorem dks2_dkFb_ne_dkI1 : dkFb ≠ dkI1 := by decide
@[simp] theorem dks2_dkFb_ne_dkI2 : dkFb ≠ dkI2 := by decide
@[simp] theorem dks2_dkFb_ne_dkN1 : dkFb ≠ dkN1 := by decide
@[simp] theorem dks2_dkFb_ne_dkU1 : dkFb ≠ dkU1 := by decide
@[simp] theorem dks2_dkFb_ne_dkN2 : dkFb ≠ dkN2 := by decide
@[simp] theorem dks2_dkFb_ne_dkU2 : dkFb ≠ dkU2 := by decide
@[simp] theorem dks2_dkFb_ne_dkL : dkFb ≠ dkL := by decide
@[simp] theorem dks2_dkFb_ne_dkXa : dkFb ≠ dkXa := by decide
@[simp] theorem dks2_dkFb_ne_dkXb : dkFb ≠ dkXb := by decide
@[simp] theorem dks2_dkFb_ne_dkLa2 : dkFb ≠ dkLa2 := by decide
@[simp] theorem dks2_dkFb_ne_dkLb2 : dkFb ≠ dkLb2 := by decide
@[simp] theorem dks2_dkFb_ne_dkFa : dkFb ≠ dkFa := by decide
@[simp] theorem dks2_dkFb_ne_dkQ : dkFb ≠ dkQ := by decide
@[simp] theorem dks2_dkFb_ne_dkDl : dkFb ≠ dkDl := by decide
@[simp] theorem dks2_dkFb_ne_dkW0 : dkFb ≠ dkW0 := by decide
@[simp] theorem dks2_dkFb_ne_dkFo : dkFb ≠ dkFo := by decide
@[simp] theorem dks2_dkFb_ne_dkCo : dkFb ≠ dkCo := by decide
@[simp] theorem dks2_dkFb_ne_dkUo : dkFb ≠ dkUo := by decide
@[simp] theorem dks2_dkFb_ne_dkEl : dkFb ≠ dkEl := by decide
@[simp] theorem dks2_dkFb_ne_dkSl : dkFb ≠ dkSl := by decide
@[simp] theorem dks2_dkFb_ne_dkLt : dkFb ≠ dkLt := by decide
@[simp] theorem dks2_dkFb_ne_dkC : dkFb ≠ dkC := by decide
@[simp] theorem dks2_dkFb_ne_dkR2 : dkFb ≠ dkR2 := by decide
@[simp] theorem dks2_dkFb_ne_lFl : dkFb ≠ lFl := by decide
@[simp] theorem dks2_lFl_ne_dkFb : lFl ≠ dkFb := by decide
@[simp] theorem dks2_dkFb_ne_lDh : dkFb ≠ lDh := by decide
@[simp] theorem dks2_lDh_ne_dkFb : lDh ≠ dkFb := by decide
@[simp] theorem dks2_dkFb_ne_lDt : dkFb ≠ lDt := by decide
@[simp] theorem dks2_lDt_ne_dkFb : lDt ≠ dkFb := by decide
@[simp] theorem dks2_dkFb_ne_lDg : dkFb ≠ lDg := by decide
@[simp] theorem dks2_lDg_ne_dkFb : lDg ≠ dkFb := by decide
@[simp] theorem dks2_dkFb_ne_lDi : dkFb ≠ lDi := by decide
@[simp] theorem dks2_lDi_ne_dkFb : lDi ≠ dkFb := by decide
@[simp] theorem dks2_dkFb_ne_lRp : dkFb ≠ lRp := by decide
@[simp] theorem dks2_lRp_ne_dkFb : lRp ≠ dkFb := by decide
@[simp] theorem dks2_dkFb_ne_lRn : dkFb ≠ lRn := by decide
@[simp] theorem dks2_lRn_ne_dkFb : lRn ≠ dkFb := by decide
@[simp] theorem dks2_dkFb_ne_lFle : dkFb ≠ lFle := by decide
@[simp] theorem dks2_lFle_ne_dkFb : lFle ≠ dkFb := by decide
@[simp] theorem dks2_dkFb_ne_lKb : dkFb ≠ lKb := by decide
@[simp] theorem dks2_lKb_ne_dkFb : lKb ≠ dkFb := by decide
@[simp] theorem dks2_dkFb_ne_lDir : dkFb ≠ lDir := by decide
@[simp] theorem dks2_lDir_ne_dkFb : lDir ≠ dkFb := by decide
@[simp] theorem dks2_dkFb_ne_lFln : dkFb ≠ lFln := by decide
@[simp] theorem dks2_lFln_ne_dkFb : lFln ≠ dkFb := by decide
@[simp] theorem dks2_dkFb_ne_lFll : dkFb ≠ lFll := by decide
@[simp] theorem dks2_lFll_ne_dkFb : lFll ≠ dkFb := by decide
@[simp] theorem dks2_dkFb_ne_lFls : dkFb ≠ lFls := by decide
@[simp] theorem dks2_lFls_ne_dkFb : lFls ≠ dkFb := by decide
@[simp] theorem dks2_dkFb_ne_kFu : dkFb ≠ kFu := by decide
@[simp] theorem dks2_kFu_ne_dkFb : kFu ≠ dkFb := by decide
@[simp] theorem dks2_dkFb_ne_kD : dkFb ≠ kD := by decide
@[simp] theorem dks2_kD_ne_dkFb : kD ≠ dkFb := by decide
@[simp] theorem dks2_dkFb_ne_dkA : dkFb ≠ dkA := by decide
@[simp] theorem dks2_dkA_ne_dkFb : dkA ≠ dkFb := by decide
@[simp] theorem dks2_dkFb_ne_dkB : dkFb ≠ dkB := by decide
@[simp] theorem dks2_dkB_ne_dkFb : dkB ≠ dkFb := by decide
@[simp] theorem dks2_dkFb_ne_dkPa : dkFb ≠ dkPa := by decide
@[simp] theorem dks2_dkPa_ne_dkFb : dkPa ≠ dkFb := by decide
@[simp] theorem dks2_dkFb_ne_dkGa : dkFb ≠ dkGa := by decide
@[simp] theorem dks2_dkGa_ne_dkFb : dkGa ≠ dkFb := by decide
@[simp] theorem dks2_dkFb_ne_dkLa : dkFb ≠ dkLa := by decide
@[simp] theorem dks2_dkLa_ne_dkFb : dkLa ≠ dkFb := by decide
@[simp] theorem dks2_dkFb_ne_dkPb : dkFb ≠ dkPb := by decide
@[simp] theorem dks2_dkPb_ne_dkFb : dkPb ≠ dkFb := by decide
@[simp] theorem dks2_dkFb_ne_dkGb : dkFb ≠ dkGb := by decide
@[simp] theorem dks2_dkGb_ne_dkFb : dkGb ≠ dkFb := by decide
@[simp] theorem dks2_dkFb_ne_dkLb : dkFb ≠ dkLb := by decide
@[simp] theorem dks2_dkLb_ne_dkFb : dkLb ≠ dkFb := by decide
@[simp] theorem dks2_dkFb_ne_dkR : dkFb ≠ dkR := by decide
@[simp] theorem dks2_dkR_ne_dkFb : dkR ≠ dkFb := by decide
@[simp] theorem dks2_dkFb_ne_dkT : dkFb ≠ dkT := by decide
@[simp] theorem dks2_dkT_ne_dkFb : dkT ≠ dkFb := by decide
@[simp] theorem dks2_dkFb_ne_dkBb : dkFb ≠ dkBb := by decide
@[simp] theorem dks2_dkBb_ne_dkFb : dkBb ≠ dkFb := by decide
@[simp] theorem dks2_dkFb_ne_dkE : dkFb ≠ dkE := by decide
@[simp] theorem dks2_dkE_ne_dkFb : dkE ≠ dkFb := by decide
@[simp] theorem dks2_dkQ_ne_dkI1 : dkQ ≠ dkI1 := by decide
@[simp] theorem dks2_dkQ_ne_dkI2 : dkQ ≠ dkI2 := by decide
@[simp] theorem dks2_dkQ_ne_dkN1 : dkQ ≠ dkN1 := by decide
@[simp] theorem dks2_dkQ_ne_dkU1 : dkQ ≠ dkU1 := by decide
@[simp] theorem dks2_dkQ_ne_dkN2 : dkQ ≠ dkN2 := by decide
@[simp] theorem dks2_dkQ_ne_dkU2 : dkQ ≠ dkU2 := by decide
@[simp] theorem dks2_dkQ_ne_dkL : dkQ ≠ dkL := by decide
@[simp] theorem dks2_dkQ_ne_dkXa : dkQ ≠ dkXa := by decide
@[simp] theorem dks2_dkQ_ne_dkXb : dkQ ≠ dkXb := by decide
@[simp] theorem dks2_dkQ_ne_dkLa2 : dkQ ≠ dkLa2 := by decide
@[simp] theorem dks2_dkQ_ne_dkLb2 : dkQ ≠ dkLb2 := by decide
@[simp] theorem dks2_dkQ_ne_dkFa : dkQ ≠ dkFa := by decide
@[simp] theorem dks2_dkQ_ne_dkFb : dkQ ≠ dkFb := by decide
@[simp] theorem dks2_dkQ_ne_dkDl : dkQ ≠ dkDl := by decide
@[simp] theorem dks2_dkQ_ne_dkW0 : dkQ ≠ dkW0 := by decide
@[simp] theorem dks2_dkQ_ne_dkFo : dkQ ≠ dkFo := by decide
@[simp] theorem dks2_dkQ_ne_dkCo : dkQ ≠ dkCo := by decide
@[simp] theorem dks2_dkQ_ne_dkUo : dkQ ≠ dkUo := by decide
@[simp] theorem dks2_dkQ_ne_dkEl : dkQ ≠ dkEl := by decide
@[simp] theorem dks2_dkQ_ne_dkSl : dkQ ≠ dkSl := by decide
@[simp] theorem dks2_dkQ_ne_dkLt : dkQ ≠ dkLt := by decide
@[simp] theorem dks2_dkQ_ne_dkC : dkQ ≠ dkC := by decide
@[simp] theorem dks2_dkQ_ne_dkR2 : dkQ ≠ dkR2 := by decide
@[simp] theorem dks2_dkQ_ne_lFl : dkQ ≠ lFl := by decide
@[simp] theorem dks2_lFl_ne_dkQ : lFl ≠ dkQ := by decide
@[simp] theorem dks2_dkQ_ne_lDh : dkQ ≠ lDh := by decide
@[simp] theorem dks2_lDh_ne_dkQ : lDh ≠ dkQ := by decide
@[simp] theorem dks2_dkQ_ne_lDt : dkQ ≠ lDt := by decide
@[simp] theorem dks2_lDt_ne_dkQ : lDt ≠ dkQ := by decide
@[simp] theorem dks2_dkQ_ne_lDg : dkQ ≠ lDg := by decide
@[simp] theorem dks2_lDg_ne_dkQ : lDg ≠ dkQ := by decide
@[simp] theorem dks2_dkQ_ne_lDi : dkQ ≠ lDi := by decide
@[simp] theorem dks2_lDi_ne_dkQ : lDi ≠ dkQ := by decide
@[simp] theorem dks2_dkQ_ne_lRp : dkQ ≠ lRp := by decide
@[simp] theorem dks2_lRp_ne_dkQ : lRp ≠ dkQ := by decide
@[simp] theorem dks2_dkQ_ne_lRn : dkQ ≠ lRn := by decide
@[simp] theorem dks2_lRn_ne_dkQ : lRn ≠ dkQ := by decide
@[simp] theorem dks2_dkQ_ne_lFle : dkQ ≠ lFle := by decide
@[simp] theorem dks2_lFle_ne_dkQ : lFle ≠ dkQ := by decide
@[simp] theorem dks2_dkQ_ne_lKb : dkQ ≠ lKb := by decide
@[simp] theorem dks2_lKb_ne_dkQ : lKb ≠ dkQ := by decide
@[simp] theorem dks2_dkQ_ne_lDir : dkQ ≠ lDir := by decide
@[simp] theorem dks2_lDir_ne_dkQ : lDir ≠ dkQ := by decide
@[simp] theorem dks2_dkQ_ne_lFln : dkQ ≠ lFln := by decide
@[simp] theorem dks2_lFln_ne_dkQ : lFln ≠ dkQ := by decide
@[simp] theorem dks2_dkQ_ne_lFll : dkQ ≠ lFll := by decide
@[simp] theorem dks2_lFll_ne_dkQ : lFll ≠ dkQ := by decide
@[simp] theorem dks2_dkQ_ne_lFls : dkQ ≠ lFls := by decide
@[simp] theorem dks2_lFls_ne_dkQ : lFls ≠ dkQ := by decide
@[simp] theorem dks2_dkQ_ne_kFu : dkQ ≠ kFu := by decide
@[simp] theorem dks2_kFu_ne_dkQ : kFu ≠ dkQ := by decide
@[simp] theorem dks2_dkQ_ne_kD : dkQ ≠ kD := by decide
@[simp] theorem dks2_kD_ne_dkQ : kD ≠ dkQ := by decide
@[simp] theorem dks2_dkQ_ne_dkA : dkQ ≠ dkA := by decide
@[simp] theorem dks2_dkA_ne_dkQ : dkA ≠ dkQ := by decide
@[simp] theorem dks2_dkQ_ne_dkB : dkQ ≠ dkB := by decide
@[simp] theorem dks2_dkB_ne_dkQ : dkB ≠ dkQ := by decide
@[simp] theorem dks2_dkQ_ne_dkPa : dkQ ≠ dkPa := by decide
@[simp] theorem dks2_dkPa_ne_dkQ : dkPa ≠ dkQ := by decide
@[simp] theorem dks2_dkQ_ne_dkGa : dkQ ≠ dkGa := by decide
@[simp] theorem dks2_dkGa_ne_dkQ : dkGa ≠ dkQ := by decide
@[simp] theorem dks2_dkQ_ne_dkLa : dkQ ≠ dkLa := by decide
@[simp] theorem dks2_dkLa_ne_dkQ : dkLa ≠ dkQ := by decide
@[simp] theorem dks2_dkQ_ne_dkPb : dkQ ≠ dkPb := by decide
@[simp] theorem dks2_dkPb_ne_dkQ : dkPb ≠ dkQ := by decide
@[simp] theorem dks2_dkQ_ne_dkGb : dkQ ≠ dkGb := by decide
@[simp] theorem dks2_dkGb_ne_dkQ : dkGb ≠ dkQ := by decide
@[simp] theorem dks2_dkQ_ne_dkLb : dkQ ≠ dkLb := by decide
@[simp] theorem dks2_dkLb_ne_dkQ : dkLb ≠ dkQ := by decide
@[simp] theorem dks2_dkQ_ne_dkR : dkQ ≠ dkR := by decide
@[simp] theorem dks2_dkR_ne_dkQ : dkR ≠ dkQ := by decide
@[simp] theorem dks2_dkQ_ne_dkT : dkQ ≠ dkT := by decide
@[simp] theorem dks2_dkT_ne_dkQ : dkT ≠ dkQ := by decide
@[simp] theorem dks2_dkQ_ne_dkBb : dkQ ≠ dkBb := by decide
@[simp] theorem dks2_dkBb_ne_dkQ : dkBb ≠ dkQ := by decide
@[simp] theorem dks2_dkQ_ne_dkE : dkQ ≠ dkE := by decide
@[simp] theorem dks2_dkE_ne_dkQ : dkE ≠ dkQ := by decide
@[simp] theorem dks2_dkDl_ne_dkI1 : dkDl ≠ dkI1 := by decide
@[simp] theorem dks2_dkDl_ne_dkI2 : dkDl ≠ dkI2 := by decide
@[simp] theorem dks2_dkDl_ne_dkN1 : dkDl ≠ dkN1 := by decide
@[simp] theorem dks2_dkDl_ne_dkU1 : dkDl ≠ dkU1 := by decide
@[simp] theorem dks2_dkDl_ne_dkN2 : dkDl ≠ dkN2 := by decide
@[simp] theorem dks2_dkDl_ne_dkU2 : dkDl ≠ dkU2 := by decide
@[simp] theorem dks2_dkDl_ne_dkL : dkDl ≠ dkL := by decide
@[simp] theorem dks2_dkDl_ne_dkXa : dkDl ≠ dkXa := by decide
@[simp] theorem dks2_dkDl_ne_dkXb : dkDl ≠ dkXb := by decide
@[simp] theorem dks2_dkDl_ne_dkLa2 : dkDl ≠ dkLa2 := by decide
@[simp] theorem dks2_dkDl_ne_dkLb2 : dkDl ≠ dkLb2 := by decide
@[simp] theorem dks2_dkDl_ne_dkFa : dkDl ≠ dkFa := by decide
@[simp] theorem dks2_dkDl_ne_dkFb : dkDl ≠ dkFb := by decide
@[simp] theorem dks2_dkDl_ne_dkQ : dkDl ≠ dkQ := by decide
@[simp] theorem dks2_dkDl_ne_dkW0 : dkDl ≠ dkW0 := by decide
@[simp] theorem dks2_dkDl_ne_dkFo : dkDl ≠ dkFo := by decide
@[simp] theorem dks2_dkDl_ne_dkCo : dkDl ≠ dkCo := by decide
@[simp] theorem dks2_dkDl_ne_dkUo : dkDl ≠ dkUo := by decide
@[simp] theorem dks2_dkDl_ne_dkEl : dkDl ≠ dkEl := by decide
@[simp] theorem dks2_dkDl_ne_dkSl : dkDl ≠ dkSl := by decide
@[simp] theorem dks2_dkDl_ne_dkLt : dkDl ≠ dkLt := by decide
@[simp] theorem dks2_dkDl_ne_dkC : dkDl ≠ dkC := by decide
@[simp] theorem dks2_dkDl_ne_dkR2 : dkDl ≠ dkR2 := by decide
@[simp] theorem dks2_dkDl_ne_lFl : dkDl ≠ lFl := by decide
@[simp] theorem dks2_lFl_ne_dkDl : lFl ≠ dkDl := by decide
@[simp] theorem dks2_dkDl_ne_lDh : dkDl ≠ lDh := by decide
@[simp] theorem dks2_lDh_ne_dkDl : lDh ≠ dkDl := by decide
@[simp] theorem dks2_dkDl_ne_lDt : dkDl ≠ lDt := by decide
@[simp] theorem dks2_lDt_ne_dkDl : lDt ≠ dkDl := by decide
@[simp] theorem dks2_dkDl_ne_lDg : dkDl ≠ lDg := by decide
@[simp] theorem dks2_lDg_ne_dkDl : lDg ≠ dkDl := by decide
@[simp] theorem dks2_dkDl_ne_lDi : dkDl ≠ lDi := by decide
@[simp] theorem dks2_lDi_ne_dkDl : lDi ≠ dkDl := by decide
@[simp] theorem dks2_dkDl_ne_lRp : dkDl ≠ lRp := by decide
@[simp] theorem dks2_lRp_ne_dkDl : lRp ≠ dkDl := by decide
@[simp] theorem dks2_dkDl_ne_lRn : dkDl ≠ lRn := by decide
@[simp] theorem dks2_lRn_ne_dkDl : lRn ≠ dkDl := by decide
@[simp] theorem dks2_dkDl_ne_lFle : dkDl ≠ lFle := by decide
@[simp] theorem dks2_lFle_ne_dkDl : lFle ≠ dkDl := by decide
@[simp] theorem dks2_dkDl_ne_lKb : dkDl ≠ lKb := by decide
@[simp] theorem dks2_lKb_ne_dkDl : lKb ≠ dkDl := by decide
@[simp] theorem dks2_dkDl_ne_lDir : dkDl ≠ lDir := by decide
@[simp] theorem dks2_lDir_ne_dkDl : lDir ≠ dkDl := by decide
@[simp] theorem dks2_dkDl_ne_lFln : dkDl ≠ lFln := by decide
@[simp] theorem dks2_lFln_ne_dkDl : lFln ≠ dkDl := by decide
@[simp] theorem dks2_dkDl_ne_lFll : dkDl ≠ lFll := by decide
@[simp] theorem dks2_lFll_ne_dkDl : lFll ≠ dkDl := by decide
@[simp] theorem dks2_dkDl_ne_lFls : dkDl ≠ lFls := by decide
@[simp] theorem dks2_lFls_ne_dkDl : lFls ≠ dkDl := by decide
@[simp] theorem dks2_dkDl_ne_kFu : dkDl ≠ kFu := by decide
@[simp] theorem dks2_kFu_ne_dkDl : kFu ≠ dkDl := by decide
@[simp] theorem dks2_dkDl_ne_kD : dkDl ≠ kD := by decide
@[simp] theorem dks2_kD_ne_dkDl : kD ≠ dkDl := by decide
@[simp] theorem dks2_dkDl_ne_dkA : dkDl ≠ dkA := by decide
@[simp] theorem dks2_dkA_ne_dkDl : dkA ≠ dkDl := by decide
@[simp] theorem dks2_dkDl_ne_dkB : dkDl ≠ dkB := by decide
@[simp] theorem dks2_dkB_ne_dkDl : dkB ≠ dkDl := by decide
@[simp] theorem dks2_dkDl_ne_dkPa : dkDl ≠ dkPa := by decide
@[simp] theorem dks2_dkPa_ne_dkDl : dkPa ≠ dkDl := by decide
@[simp] theorem dks2_dkDl_ne_dkGa : dkDl ≠ dkGa := by decide
@[simp] theorem dks2_dkGa_ne_dkDl : dkGa ≠ dkDl := by decide
@[simp] theorem dks2_dkDl_ne_dkLa : dkDl ≠ dkLa := by decide
@[simp] theorem dks2_dkLa_ne_dkDl : dkLa ≠ dkDl := by decide
@[simp] theorem dks2_dkDl_ne_dkPb : dkDl ≠ dkPb := by decide
@[simp] theorem dks2_dkPb_ne_dkDl : dkPb ≠ dkDl := by decide
@[simp] theorem dks2_dkDl_ne_dkGb : dkDl ≠ dkGb := by decide
@[simp] theorem dks2_dkGb_ne_dkDl : dkGb ≠ dkDl := by decide
@[simp] theorem dks2_dkDl_ne_dkLb : dkDl ≠ dkLb := by decide
@[simp] theorem dks2_dkLb_ne_dkDl : dkLb ≠ dkDl := by decide
@[simp] theorem dks2_dkDl_ne_dkR : dkDl ≠ dkR := by decide
@[simp] theorem dks2_dkR_ne_dkDl : dkR ≠ dkDl := by decide
@[simp] theorem dks2_dkDl_ne_dkT : dkDl ≠ dkT := by decide
@[simp] theorem dks2_dkT_ne_dkDl : dkT ≠ dkDl := by decide
@[simp] theorem dks2_dkDl_ne_dkBb : dkDl ≠ dkBb := by decide
@[simp] theorem dks2_dkBb_ne_dkDl : dkBb ≠ dkDl := by decide
@[simp] theorem dks2_dkDl_ne_dkE : dkDl ≠ dkE := by decide
@[simp] theorem dks2_dkE_ne_dkDl : dkE ≠ dkDl := by decide
@[simp] theorem dks2_dkW0_ne_dkI1 : dkW0 ≠ dkI1 := by decide
@[simp] theorem dks2_dkW0_ne_dkI2 : dkW0 ≠ dkI2 := by decide
@[simp] theorem dks2_dkW0_ne_dkN1 : dkW0 ≠ dkN1 := by decide
@[simp] theorem dks2_dkW0_ne_dkU1 : dkW0 ≠ dkU1 := by decide
@[simp] theorem dks2_dkW0_ne_dkN2 : dkW0 ≠ dkN2 := by decide
@[simp] theorem dks2_dkW0_ne_dkU2 : dkW0 ≠ dkU2 := by decide
@[simp] theorem dks2_dkW0_ne_dkL : dkW0 ≠ dkL := by decide
@[simp] theorem dks2_dkW0_ne_dkXa : dkW0 ≠ dkXa := by decide
@[simp] theorem dks2_dkW0_ne_dkXb : dkW0 ≠ dkXb := by decide
@[simp] theorem dks2_dkW0_ne_dkLa2 : dkW0 ≠ dkLa2 := by decide
@[simp] theorem dks2_dkW0_ne_dkLb2 : dkW0 ≠ dkLb2 := by decide
@[simp] theorem dks2_dkW0_ne_dkFa : dkW0 ≠ dkFa := by decide
@[simp] theorem dks2_dkW0_ne_dkFb : dkW0 ≠ dkFb := by decide
@[simp] theorem dks2_dkW0_ne_dkQ : dkW0 ≠ dkQ := by decide
@[simp] theorem dks2_dkW0_ne_dkDl : dkW0 ≠ dkDl := by decide
@[simp] theorem dks2_dkW0_ne_dkFo : dkW0 ≠ dkFo := by decide
@[simp] theorem dks2_dkW0_ne_dkCo : dkW0 ≠ dkCo := by decide
@[simp] theorem dks2_dkW0_ne_dkUo : dkW0 ≠ dkUo := by decide
@[simp] theorem dks2_dkW0_ne_dkEl : dkW0 ≠ dkEl := by decide
@[simp] theorem dks2_dkW0_ne_dkSl : dkW0 ≠ dkSl := by decide
@[simp] theorem dks2_dkW0_ne_dkLt : dkW0 ≠ dkLt := by decide
@[simp] theorem dks2_dkW0_ne_dkC : dkW0 ≠ dkC := by decide
@[simp] theorem dks2_dkW0_ne_dkR2 : dkW0 ≠ dkR2 := by decide
@[simp] theorem dks2_dkW0_ne_lFl : dkW0 ≠ lFl := by decide
@[simp] theorem dks2_lFl_ne_dkW0 : lFl ≠ dkW0 := by decide
@[simp] theorem dks2_dkW0_ne_lDh : dkW0 ≠ lDh := by decide
@[simp] theorem dks2_lDh_ne_dkW0 : lDh ≠ dkW0 := by decide
@[simp] theorem dks2_dkW0_ne_lDt : dkW0 ≠ lDt := by decide
@[simp] theorem dks2_lDt_ne_dkW0 : lDt ≠ dkW0 := by decide
@[simp] theorem dks2_dkW0_ne_lDg : dkW0 ≠ lDg := by decide
@[simp] theorem dks2_lDg_ne_dkW0 : lDg ≠ dkW0 := by decide
@[simp] theorem dks2_dkW0_ne_lDi : dkW0 ≠ lDi := by decide
@[simp] theorem dks2_lDi_ne_dkW0 : lDi ≠ dkW0 := by decide
@[simp] theorem dks2_dkW0_ne_lRp : dkW0 ≠ lRp := by decide
@[simp] theorem dks2_lRp_ne_dkW0 : lRp ≠ dkW0 := by decide
@[simp] theorem dks2_dkW0_ne_lRn : dkW0 ≠ lRn := by decide
@[simp] theorem dks2_lRn_ne_dkW0 : lRn ≠ dkW0 := by decide
@[simp] theorem dks2_dkW0_ne_lFle : dkW0 ≠ lFle := by decide
@[simp] theorem dks2_lFle_ne_dkW0 : lFle ≠ dkW0 := by decide
@[simp] theorem dks2_dkW0_ne_lKb : dkW0 ≠ lKb := by decide
@[simp] theorem dks2_lKb_ne_dkW0 : lKb ≠ dkW0 := by decide
@[simp] theorem dks2_dkW0_ne_lDir : dkW0 ≠ lDir := by decide
@[simp] theorem dks2_lDir_ne_dkW0 : lDir ≠ dkW0 := by decide
@[simp] theorem dks2_dkW0_ne_lFln : dkW0 ≠ lFln := by decide
@[simp] theorem dks2_lFln_ne_dkW0 : lFln ≠ dkW0 := by decide
@[simp] theorem dks2_dkW0_ne_lFll : dkW0 ≠ lFll := by decide
@[simp] theorem dks2_lFll_ne_dkW0 : lFll ≠ dkW0 := by decide
@[simp] theorem dks2_dkW0_ne_lFls : dkW0 ≠ lFls := by decide
@[simp] theorem dks2_lFls_ne_dkW0 : lFls ≠ dkW0 := by decide
@[simp] theorem dks2_dkW0_ne_kFu : dkW0 ≠ kFu := by decide
@[simp] theorem dks2_kFu_ne_dkW0 : kFu ≠ dkW0 := by decide
@[simp] theorem dks2_dkW0_ne_kD : dkW0 ≠ kD := by decide
@[simp] theorem dks2_kD_ne_dkW0 : kD ≠ dkW0 := by decide
@[simp] theorem dks2_dkW0_ne_dkA : dkW0 ≠ dkA := by decide
@[simp] theorem dks2_dkA_ne_dkW0 : dkA ≠ dkW0 := by decide
@[simp] theorem dks2_dkW0_ne_dkB : dkW0 ≠ dkB := by decide
@[simp] theorem dks2_dkB_ne_dkW0 : dkB ≠ dkW0 := by decide
@[simp] theorem dks2_dkW0_ne_dkPa : dkW0 ≠ dkPa := by decide
@[simp] theorem dks2_dkPa_ne_dkW0 : dkPa ≠ dkW0 := by decide
@[simp] theorem dks2_dkW0_ne_dkGa : dkW0 ≠ dkGa := by decide
@[simp] theorem dks2_dkGa_ne_dkW0 : dkGa ≠ dkW0 := by decide
@[simp] theorem dks2_dkW0_ne_dkLa : dkW0 ≠ dkLa := by decide
@[simp] theorem dks2_dkLa_ne_dkW0 : dkLa ≠ dkW0 := by decide
@[simp] theorem dks2_dkW0_ne_dkPb : dkW0 ≠ dkPb := by decide
@[simp] theorem dks2_dkPb_ne_dkW0 : dkPb ≠ dkW0 := by decide
@[simp] theorem dks2_dkW0_ne_dkGb : dkW0 ≠ dkGb := by decide
@[simp] theorem dks2_dkGb_ne_dkW0 : dkGb ≠ dkW0 := by decide
@[simp] theorem dks2_dkW0_ne_dkLb : dkW0 ≠ dkLb := by decide
@[simp] theorem dks2_dkLb_ne_dkW0 : dkLb ≠ dkW0 := by decide
@[simp] theorem dks2_dkW0_ne_dkR : dkW0 ≠ dkR := by decide
@[simp] theorem dks2_dkR_ne_dkW0 : dkR ≠ dkW0 := by decide
@[simp] theorem dks2_dkW0_ne_dkT : dkW0 ≠ dkT := by decide
@[simp] theorem dks2_dkT_ne_dkW0 : dkT ≠ dkW0 := by decide
@[simp] theorem dks2_dkW0_ne_dkBb : dkW0 ≠ dkBb := by decide
@[simp] theorem dks2_dkBb_ne_dkW0 : dkBb ≠ dkW0 := by decide
@[simp] theorem dks2_dkW0_ne_dkE : dkW0 ≠ dkE := by decide
@[simp] theorem dks2_dkE_ne_dkW0 : dkE ≠ dkW0 := by decide
@[simp] theorem dks2_dkFo_ne_dkI1 : dkFo ≠ dkI1 := by decide
@[simp] theorem dks2_dkFo_ne_dkI2 : dkFo ≠ dkI2 := by decide
@[simp] theorem dks2_dkFo_ne_dkN1 : dkFo ≠ dkN1 := by decide
@[simp] theorem dks2_dkFo_ne_dkU1 : dkFo ≠ dkU1 := by decide
@[simp] theorem dks2_dkFo_ne_dkN2 : dkFo ≠ dkN2 := by decide
@[simp] theorem dks2_dkFo_ne_dkU2 : dkFo ≠ dkU2 := by decide
@[simp] theorem dks2_dkFo_ne_dkL : dkFo ≠ dkL := by decide
@[simp] theorem dks2_dkFo_ne_dkXa : dkFo ≠ dkXa := by decide
@[simp] theorem dks2_dkFo_ne_dkXb : dkFo ≠ dkXb := by decide
@[simp] theorem dks2_dkFo_ne_dkLa2 : dkFo ≠ dkLa2 := by decide
@[simp] theorem dks2_dkFo_ne_dkLb2 : dkFo ≠ dkLb2 := by decide
@[simp] theorem dks2_dkFo_ne_dkFa : dkFo ≠ dkFa := by decide
@[simp] theorem dks2_dkFo_ne_dkFb : dkFo ≠ dkFb := by decide
@[simp] theorem dks2_dkFo_ne_dkQ : dkFo ≠ dkQ := by decide
@[simp] theorem dks2_dkFo_ne_dkDl : dkFo ≠ dkDl := by decide
@[simp] theorem dks2_dkFo_ne_dkW0 : dkFo ≠ dkW0 := by decide
@[simp] theorem dks2_dkFo_ne_dkCo : dkFo ≠ dkCo := by decide
@[simp] theorem dks2_dkFo_ne_dkUo : dkFo ≠ dkUo := by decide
@[simp] theorem dks2_dkFo_ne_dkEl : dkFo ≠ dkEl := by decide
@[simp] theorem dks2_dkFo_ne_dkSl : dkFo ≠ dkSl := by decide
@[simp] theorem dks2_dkFo_ne_dkLt : dkFo ≠ dkLt := by decide
@[simp] theorem dks2_dkFo_ne_dkC : dkFo ≠ dkC := by decide
@[simp] theorem dks2_dkFo_ne_dkR2 : dkFo ≠ dkR2 := by decide
@[simp] theorem dks2_dkFo_ne_lFl : dkFo ≠ lFl := by decide
@[simp] theorem dks2_lFl_ne_dkFo : lFl ≠ dkFo := by decide
@[simp] theorem dks2_dkFo_ne_lDh : dkFo ≠ lDh := by decide
@[simp] theorem dks2_lDh_ne_dkFo : lDh ≠ dkFo := by decide
@[simp] theorem dks2_dkFo_ne_lDt : dkFo ≠ lDt := by decide
@[simp] theorem dks2_lDt_ne_dkFo : lDt ≠ dkFo := by decide
@[simp] theorem dks2_dkFo_ne_lDg : dkFo ≠ lDg := by decide
@[simp] theorem dks2_lDg_ne_dkFo : lDg ≠ dkFo := by decide
@[simp] theorem dks2_dkFo_ne_lDi : dkFo ≠ lDi := by decide
@[simp] theorem dks2_lDi_ne_dkFo : lDi ≠ dkFo := by decide
@[simp] theorem dks2_dkFo_ne_lRp : dkFo ≠ lRp := by decide
@[simp] theorem dks2_lRp_ne_dkFo : lRp ≠ dkFo := by decide
@[simp] theorem dks2_dkFo_ne_lRn : dkFo ≠ lRn := by decide
@[simp] theorem dks2_lRn_ne_dkFo : lRn ≠ dkFo := by decide
@[simp] theorem dks2_dkFo_ne_lFle : dkFo ≠ lFle := by decide
@[simp] theorem dks2_lFle_ne_dkFo : lFle ≠ dkFo := by decide
@[simp] theorem dks2_dkFo_ne_lKb : dkFo ≠ lKb := by decide
@[simp] theorem dks2_lKb_ne_dkFo : lKb ≠ dkFo := by decide
@[simp] theorem dks2_dkFo_ne_lDir : dkFo ≠ lDir := by decide
@[simp] theorem dks2_lDir_ne_dkFo : lDir ≠ dkFo := by decide
@[simp] theorem dks2_dkFo_ne_lFln : dkFo ≠ lFln := by decide
@[simp] theorem dks2_lFln_ne_dkFo : lFln ≠ dkFo := by decide
@[simp] theorem dks2_dkFo_ne_lFll : dkFo ≠ lFll := by decide
@[simp] theorem dks2_lFll_ne_dkFo : lFll ≠ dkFo := by decide
@[simp] theorem dks2_dkFo_ne_lFls : dkFo ≠ lFls := by decide
@[simp] theorem dks2_lFls_ne_dkFo : lFls ≠ dkFo := by decide
@[simp] theorem dks2_dkFo_ne_kFu : dkFo ≠ kFu := by decide
@[simp] theorem dks2_kFu_ne_dkFo : kFu ≠ dkFo := by decide
@[simp] theorem dks2_dkFo_ne_kD : dkFo ≠ kD := by decide
@[simp] theorem dks2_kD_ne_dkFo : kD ≠ dkFo := by decide
@[simp] theorem dks2_dkFo_ne_dkA : dkFo ≠ dkA := by decide
@[simp] theorem dks2_dkA_ne_dkFo : dkA ≠ dkFo := by decide
@[simp] theorem dks2_dkFo_ne_dkB : dkFo ≠ dkB := by decide
@[simp] theorem dks2_dkB_ne_dkFo : dkB ≠ dkFo := by decide
@[simp] theorem dks2_dkFo_ne_dkPa : dkFo ≠ dkPa := by decide
@[simp] theorem dks2_dkPa_ne_dkFo : dkPa ≠ dkFo := by decide
@[simp] theorem dks2_dkFo_ne_dkGa : dkFo ≠ dkGa := by decide
@[simp] theorem dks2_dkGa_ne_dkFo : dkGa ≠ dkFo := by decide
@[simp] theorem dks2_dkFo_ne_dkLa : dkFo ≠ dkLa := by decide
@[simp] theorem dks2_dkLa_ne_dkFo : dkLa ≠ dkFo := by decide
@[simp] theorem dks2_dkFo_ne_dkPb : dkFo ≠ dkPb := by decide
@[simp] theorem dks2_dkPb_ne_dkFo : dkPb ≠ dkFo := by decide
@[simp] theorem dks2_dkFo_ne_dkGb : dkFo ≠ dkGb := by decide
@[simp] theorem dks2_dkGb_ne_dkFo : dkGb ≠ dkFo := by decide
@[simp] theorem dks2_dkFo_ne_dkLb : dkFo ≠ dkLb := by decide
@[simp] theorem dks2_dkLb_ne_dkFo : dkLb ≠ dkFo := by decide
@[simp] theorem dks2_dkFo_ne_dkR : dkFo ≠ dkR := by decide
@[simp] theorem dks2_dkR_ne_dkFo : dkR ≠ dkFo := by decide
@[simp] theorem dks2_dkFo_ne_dkT : dkFo ≠ dkT := by decide
@[simp] theorem dks2_dkT_ne_dkFo : dkT ≠ dkFo := by decide
@[simp] theorem dks2_dkFo_ne_dkBb : dkFo ≠ dkBb := by decide
@[simp] theorem dks2_dkBb_ne_dkFo : dkBb ≠ dkFo := by decide
@[simp] theorem dks2_dkFo_ne_dkE : dkFo ≠ dkE := by decide
@[simp] theorem dks2_dkE_ne_dkFo : dkE ≠ dkFo := by decide
@[simp] theorem dks2_dkCo_ne_dkI1 : dkCo ≠ dkI1 := by decide
@[simp] theorem dks2_dkCo_ne_dkI2 : dkCo ≠ dkI2 := by decide
@[simp] theorem dks2_dkCo_ne_dkN1 : dkCo ≠ dkN1 := by decide
@[simp] theorem dks2_dkCo_ne_dkU1 : dkCo ≠ dkU1 := by decide
@[simp] theorem dks2_dkCo_ne_dkN2 : dkCo ≠ dkN2 := by decide
@[simp] theorem dks2_dkCo_ne_dkU2 : dkCo ≠ dkU2 := by decide
@[simp] theorem dks2_dkCo_ne_dkL : dkCo ≠ dkL := by decide
@[simp] theorem dks2_dkCo_ne_dkXa : dkCo ≠ dkXa := by decide
@[simp] theorem dks2_dkCo_ne_dkXb : dkCo ≠ dkXb := by decide
@[simp] theorem dks2_dkCo_ne_dkLa2 : dkCo ≠ dkLa2 := by decide
@[simp] theorem dks2_dkCo_ne_dkLb2 : dkCo ≠ dkLb2 := by decide
@[simp] theorem dks2_dkCo_ne_dkFa : dkCo ≠ dkFa := by decide
@[simp] theorem dks2_dkCo_ne_dkFb : dkCo ≠ dkFb := by decide
@[simp] theorem dks2_dkCo_ne_dkQ : dkCo ≠ dkQ := by decide
@[simp] theorem dks2_dkCo_ne_dkDl : dkCo ≠ dkDl := by decide
@[simp] theorem dks2_dkCo_ne_dkW0 : dkCo ≠ dkW0 := by decide
@[simp] theorem dks2_dkCo_ne_dkFo : dkCo ≠ dkFo := by decide
@[simp] theorem dks2_dkCo_ne_dkUo : dkCo ≠ dkUo := by decide
@[simp] theorem dks2_dkCo_ne_dkEl : dkCo ≠ dkEl := by decide
@[simp] theorem dks2_dkCo_ne_dkSl : dkCo ≠ dkSl := by decide
@[simp] theorem dks2_dkCo_ne_dkLt : dkCo ≠ dkLt := by decide
@[simp] theorem dks2_dkCo_ne_dkC : dkCo ≠ dkC := by decide
@[simp] theorem dks2_dkCo_ne_dkR2 : dkCo ≠ dkR2 := by decide
@[simp] theorem dks2_dkCo_ne_lFl : dkCo ≠ lFl := by decide
@[simp] theorem dks2_lFl_ne_dkCo : lFl ≠ dkCo := by decide
@[simp] theorem dks2_dkCo_ne_lDh : dkCo ≠ lDh := by decide
@[simp] theorem dks2_lDh_ne_dkCo : lDh ≠ dkCo := by decide
@[simp] theorem dks2_dkCo_ne_lDt : dkCo ≠ lDt := by decide
@[simp] theorem dks2_lDt_ne_dkCo : lDt ≠ dkCo := by decide
@[simp] theorem dks2_dkCo_ne_lDg : dkCo ≠ lDg := by decide
@[simp] theorem dks2_lDg_ne_dkCo : lDg ≠ dkCo := by decide
@[simp] theorem dks2_dkCo_ne_lDi : dkCo ≠ lDi := by decide
@[simp] theorem dks2_lDi_ne_dkCo : lDi ≠ dkCo := by decide
@[simp] theorem dks2_dkCo_ne_lRp : dkCo ≠ lRp := by decide
@[simp] theorem dks2_lRp_ne_dkCo : lRp ≠ dkCo := by decide
@[simp] theorem dks2_dkCo_ne_lRn : dkCo ≠ lRn := by decide
@[simp] theorem dks2_lRn_ne_dkCo : lRn ≠ dkCo := by decide
@[simp] theorem dks2_dkCo_ne_lFle : dkCo ≠ lFle := by decide
@[simp] theorem dks2_lFle_ne_dkCo : lFle ≠ dkCo := by decide
@[simp] theorem dks2_dkCo_ne_lKb : dkCo ≠ lKb := by decide
@[simp] theorem dks2_lKb_ne_dkCo : lKb ≠ dkCo := by decide
@[simp] theorem dks2_dkCo_ne_lDir : dkCo ≠ lDir := by decide
@[simp] theorem dks2_lDir_ne_dkCo : lDir ≠ dkCo := by decide
@[simp] theorem dks2_dkCo_ne_lFln : dkCo ≠ lFln := by decide
@[simp] theorem dks2_lFln_ne_dkCo : lFln ≠ dkCo := by decide
@[simp] theorem dks2_dkCo_ne_lFll : dkCo ≠ lFll := by decide
@[simp] theorem dks2_lFll_ne_dkCo : lFll ≠ dkCo := by decide
@[simp] theorem dks2_dkCo_ne_lFls : dkCo ≠ lFls := by decide
@[simp] theorem dks2_lFls_ne_dkCo : lFls ≠ dkCo := by decide
@[simp] theorem dks2_dkCo_ne_kFu : dkCo ≠ kFu := by decide
@[simp] theorem dks2_kFu_ne_dkCo : kFu ≠ dkCo := by decide
@[simp] theorem dks2_dkCo_ne_kD : dkCo ≠ kD := by decide
@[simp] theorem dks2_kD_ne_dkCo : kD ≠ dkCo := by decide
@[simp] theorem dks2_dkCo_ne_dkA : dkCo ≠ dkA := by decide
@[simp] theorem dks2_dkA_ne_dkCo : dkA ≠ dkCo := by decide
@[simp] theorem dks2_dkCo_ne_dkB : dkCo ≠ dkB := by decide
@[simp] theorem dks2_dkB_ne_dkCo : dkB ≠ dkCo := by decide
@[simp] theorem dks2_dkCo_ne_dkPa : dkCo ≠ dkPa := by decide
@[simp] theorem dks2_dkPa_ne_dkCo : dkPa ≠ dkCo := by decide
@[simp] theorem dks2_dkCo_ne_dkGa : dkCo ≠ dkGa := by decide
@[simp] theorem dks2_dkGa_ne_dkCo : dkGa ≠ dkCo := by decide
@[simp] theorem dks2_dkCo_ne_dkLa : dkCo ≠ dkLa := by decide
@[simp] theorem dks2_dkLa_ne_dkCo : dkLa ≠ dkCo := by decide
@[simp] theorem dks2_dkCo_ne_dkPb : dkCo ≠ dkPb := by decide
@[simp] theorem dks2_dkPb_ne_dkCo : dkPb ≠ dkCo := by decide
@[simp] theorem dks2_dkCo_ne_dkGb : dkCo ≠ dkGb := by decide
@[simp] theorem dks2_dkGb_ne_dkCo : dkGb ≠ dkCo := by decide
@[simp] theorem dks2_dkCo_ne_dkLb : dkCo ≠ dkLb := by decide
@[simp] theorem dks2_dkLb_ne_dkCo : dkLb ≠ dkCo := by decide
@[simp] theorem dks2_dkCo_ne_dkR : dkCo ≠ dkR := by decide
@[simp] theorem dks2_dkR_ne_dkCo : dkR ≠ dkCo := by decide
@[simp] theorem dks2_dkCo_ne_dkT : dkCo ≠ dkT := by decide
@[simp] theorem dks2_dkT_ne_dkCo : dkT ≠ dkCo := by decide
@[simp] theorem dks2_dkCo_ne_dkBb : dkCo ≠ dkBb := by decide
@[simp] theorem dks2_dkBb_ne_dkCo : dkBb ≠ dkCo := by decide
@[simp] theorem dks2_dkCo_ne_dkE : dkCo ≠ dkE := by decide
@[simp] theorem dks2_dkE_ne_dkCo : dkE ≠ dkCo := by decide
@[simp] theorem dks2_dkUo_ne_dkI1 : dkUo ≠ dkI1 := by decide
@[simp] theorem dks2_dkUo_ne_dkI2 : dkUo ≠ dkI2 := by decide
@[simp] theorem dks2_dkUo_ne_dkN1 : dkUo ≠ dkN1 := by decide
@[simp] theorem dks2_dkUo_ne_dkU1 : dkUo ≠ dkU1 := by decide
@[simp] theorem dks2_dkUo_ne_dkN2 : dkUo ≠ dkN2 := by decide
@[simp] theorem dks2_dkUo_ne_dkU2 : dkUo ≠ dkU2 := by decide
@[simp] theorem dks2_dkUo_ne_dkL : dkUo ≠ dkL := by decide
@[simp] theorem dks2_dkUo_ne_dkXa : dkUo ≠ dkXa := by decide
@[simp] theorem dks2_dkUo_ne_dkXb : dkUo ≠ dkXb := by decide
@[simp] theorem dks2_dkUo_ne_dkLa2 : dkUo ≠ dkLa2 := by decide
@[simp] theorem dks2_dkUo_ne_dkLb2 : dkUo ≠ dkLb2 := by decide
@[simp] theorem dks2_dkUo_ne_dkFa : dkUo ≠ dkFa := by decide
@[simp] theorem dks2_dkUo_ne_dkFb : dkUo ≠ dkFb := by decide
@[simp] theorem dks2_dkUo_ne_dkQ : dkUo ≠ dkQ := by decide
@[simp] theorem dks2_dkUo_ne_dkDl : dkUo ≠ dkDl := by decide
@[simp] theorem dks2_dkUo_ne_dkW0 : dkUo ≠ dkW0 := by decide
@[simp] theorem dks2_dkUo_ne_dkFo : dkUo ≠ dkFo := by decide
@[simp] theorem dks2_dkUo_ne_dkCo : dkUo ≠ dkCo := by decide
@[simp] theorem dks2_dkUo_ne_dkEl : dkUo ≠ dkEl := by decide
@[simp] theorem dks2_dkUo_ne_dkSl : dkUo ≠ dkSl := by decide
@[simp] theorem dks2_dkUo_ne_dkLt : dkUo ≠ dkLt := by decide
@[simp] theorem dks2_dkUo_ne_dkC : dkUo ≠ dkC := by decide
@[simp] theorem dks2_dkUo_ne_dkR2 : dkUo ≠ dkR2 := by decide
@[simp] theorem dks2_dkUo_ne_lFl : dkUo ≠ lFl := by decide
@[simp] theorem dks2_lFl_ne_dkUo : lFl ≠ dkUo := by decide
@[simp] theorem dks2_dkUo_ne_lDh : dkUo ≠ lDh := by decide
@[simp] theorem dks2_lDh_ne_dkUo : lDh ≠ dkUo := by decide
@[simp] theorem dks2_dkUo_ne_lDt : dkUo ≠ lDt := by decide
@[simp] theorem dks2_lDt_ne_dkUo : lDt ≠ dkUo := by decide
@[simp] theorem dks2_dkUo_ne_lDg : dkUo ≠ lDg := by decide
@[simp] theorem dks2_lDg_ne_dkUo : lDg ≠ dkUo := by decide
@[simp] theorem dks2_dkUo_ne_lDi : dkUo ≠ lDi := by decide
@[simp] theorem dks2_lDi_ne_dkUo : lDi ≠ dkUo := by decide
@[simp] theorem dks2_dkUo_ne_lRp : dkUo ≠ lRp := by decide
@[simp] theorem dks2_lRp_ne_dkUo : lRp ≠ dkUo := by decide
@[simp] theorem dks2_dkUo_ne_lRn : dkUo ≠ lRn := by decide
@[simp] theorem dks2_lRn_ne_dkUo : lRn ≠ dkUo := by decide
@[simp] theorem dks2_dkUo_ne_lFle : dkUo ≠ lFle := by decide
@[simp] theorem dks2_lFle_ne_dkUo : lFle ≠ dkUo := by decide
@[simp] theorem dks2_dkUo_ne_lKb : dkUo ≠ lKb := by decide
@[simp] theorem dks2_lKb_ne_dkUo : lKb ≠ dkUo := by decide
@[simp] theorem dks2_dkUo_ne_lDir : dkUo ≠ lDir := by decide
@[simp] theorem dks2_lDir_ne_dkUo : lDir ≠ dkUo := by decide
@[simp] theorem dks2_dkUo_ne_lFln : dkUo ≠ lFln := by decide
@[simp] theorem dks2_lFln_ne_dkUo : lFln ≠ dkUo := by decide
@[simp] theorem dks2_dkUo_ne_lFll : dkUo ≠ lFll := by decide
@[simp] theorem dks2_lFll_ne_dkUo : lFll ≠ dkUo := by decide
@[simp] theorem dks2_dkUo_ne_lFls : dkUo ≠ lFls := by decide
@[simp] theorem dks2_lFls_ne_dkUo : lFls ≠ dkUo := by decide
@[simp] theorem dks2_dkUo_ne_kFu : dkUo ≠ kFu := by decide
@[simp] theorem dks2_kFu_ne_dkUo : kFu ≠ dkUo := by decide
@[simp] theorem dks2_dkUo_ne_kD : dkUo ≠ kD := by decide
@[simp] theorem dks2_kD_ne_dkUo : kD ≠ dkUo := by decide
@[simp] theorem dks2_dkUo_ne_dkA : dkUo ≠ dkA := by decide
@[simp] theorem dks2_dkA_ne_dkUo : dkA ≠ dkUo := by decide
@[simp] theorem dks2_dkUo_ne_dkB : dkUo ≠ dkB := by decide
@[simp] theorem dks2_dkB_ne_dkUo : dkB ≠ dkUo := by decide
@[simp] theorem dks2_dkUo_ne_dkPa : dkUo ≠ dkPa := by decide
@[simp] theorem dks2_dkPa_ne_dkUo : dkPa ≠ dkUo := by decide
@[simp] theorem dks2_dkUo_ne_dkGa : dkUo ≠ dkGa := by decide
@[simp] theorem dks2_dkGa_ne_dkUo : dkGa ≠ dkUo := by decide
@[simp] theorem dks2_dkUo_ne_dkLa : dkUo ≠ dkLa := by decide
@[simp] theorem dks2_dkLa_ne_dkUo : dkLa ≠ dkUo := by decide
@[simp] theorem dks2_dkUo_ne_dkPb : dkUo ≠ dkPb := by decide
@[simp] theorem dks2_dkPb_ne_dkUo : dkPb ≠ dkUo := by decide
@[simp] theorem dks2_dkUo_ne_dkGb : dkUo ≠ dkGb := by decide
@[simp] theorem dks2_dkGb_ne_dkUo : dkGb ≠ dkUo := by decide
@[simp] theorem dks2_dkUo_ne_dkLb : dkUo ≠ dkLb := by decide
@[simp] theorem dks2_dkLb_ne_dkUo : dkLb ≠ dkUo := by decide
@[simp] theorem dks2_dkUo_ne_dkR : dkUo ≠ dkR := by decide
@[simp] theorem dks2_dkR_ne_dkUo : dkR ≠ dkUo := by decide
@[simp] theorem dks2_dkUo_ne_dkT : dkUo ≠ dkT := by decide
@[simp] theorem dks2_dkT_ne_dkUo : dkT ≠ dkUo := by decide
@[simp] theorem dks2_dkUo_ne_dkBb : dkUo ≠ dkBb := by decide
@[simp] theorem dks2_dkBb_ne_dkUo : dkBb ≠ dkUo := by decide
@[simp] theorem dks2_dkUo_ne_dkE : dkUo ≠ dkE := by decide
@[simp] theorem dks2_dkE_ne_dkUo : dkE ≠ dkUo := by decide
@[simp] theorem dks2_dkEl_ne_dkI1 : dkEl ≠ dkI1 := by decide
@[simp] theorem dks2_dkEl_ne_dkI2 : dkEl ≠ dkI2 := by decide
@[simp] theorem dks2_dkEl_ne_dkN1 : dkEl ≠ dkN1 := by decide
@[simp] theorem dks2_dkEl_ne_dkU1 : dkEl ≠ dkU1 := by decide
@[simp] theorem dks2_dkEl_ne_dkN2 : dkEl ≠ dkN2 := by decide
@[simp] theorem dks2_dkEl_ne_dkU2 : dkEl ≠ dkU2 := by decide
@[simp] theorem dks2_dkEl_ne_dkL : dkEl ≠ dkL := by decide
@[simp] theorem dks2_dkEl_ne_dkXa : dkEl ≠ dkXa := by decide
@[simp] theorem dks2_dkEl_ne_dkXb : dkEl ≠ dkXb := by decide
@[simp] theorem dks2_dkEl_ne_dkLa2 : dkEl ≠ dkLa2 := by decide
@[simp] theorem dks2_dkEl_ne_dkLb2 : dkEl ≠ dkLb2 := by decide
@[simp] theorem dks2_dkEl_ne_dkFa : dkEl ≠ dkFa := by decide
@[simp] theorem dks2_dkEl_ne_dkFb : dkEl ≠ dkFb := by decide
@[simp] theorem dks2_dkEl_ne_dkQ : dkEl ≠ dkQ := by decide
@[simp] theorem dks2_dkEl_ne_dkDl : dkEl ≠ dkDl := by decide
@[simp] theorem dks2_dkEl_ne_dkW0 : dkEl ≠ dkW0 := by decide
@[simp] theorem dks2_dkEl_ne_dkFo : dkEl ≠ dkFo := by decide
@[simp] theorem dks2_dkEl_ne_dkCo : dkEl ≠ dkCo := by decide
@[simp] theorem dks2_dkEl_ne_dkUo : dkEl ≠ dkUo := by decide
@[simp] theorem dks2_dkEl_ne_dkSl : dkEl ≠ dkSl := by decide
@[simp] theorem dks2_dkEl_ne_dkLt : dkEl ≠ dkLt := by decide
@[simp] theorem dks2_dkEl_ne_dkC : dkEl ≠ dkC := by decide
@[simp] theorem dks2_dkEl_ne_dkR2 : dkEl ≠ dkR2 := by decide
@[simp] theorem dks2_dkEl_ne_lFl : dkEl ≠ lFl := by decide
@[simp] theorem dks2_lFl_ne_dkEl : lFl ≠ dkEl := by decide
@[simp] theorem dks2_dkEl_ne_lDh : dkEl ≠ lDh := by decide
@[simp] theorem dks2_lDh_ne_dkEl : lDh ≠ dkEl := by decide
@[simp] theorem dks2_dkEl_ne_lDt : dkEl ≠ lDt := by decide
@[simp] theorem dks2_lDt_ne_dkEl : lDt ≠ dkEl := by decide
@[simp] theorem dks2_dkEl_ne_lDg : dkEl ≠ lDg := by decide
@[simp] theorem dks2_lDg_ne_dkEl : lDg ≠ dkEl := by decide
@[simp] theorem dks2_dkEl_ne_lDi : dkEl ≠ lDi := by decide
@[simp] theorem dks2_lDi_ne_dkEl : lDi ≠ dkEl := by decide
@[simp] theorem dks2_dkEl_ne_lRp : dkEl ≠ lRp := by decide
@[simp] theorem dks2_lRp_ne_dkEl : lRp ≠ dkEl := by decide
@[simp] theorem dks2_dkEl_ne_lRn : dkEl ≠ lRn := by decide
@[simp] theorem dks2_lRn_ne_dkEl : lRn ≠ dkEl := by decide
@[simp] theorem dks2_dkEl_ne_lFle : dkEl ≠ lFle := by decide
@[simp] theorem dks2_lFle_ne_dkEl : lFle ≠ dkEl := by decide
@[simp] theorem dks2_dkEl_ne_lKb : dkEl ≠ lKb := by decide
@[simp] theorem dks2_lKb_ne_dkEl : lKb ≠ dkEl := by decide
@[simp] theorem dks2_dkEl_ne_lDir : dkEl ≠ lDir := by decide
@[simp] theorem dks2_lDir_ne_dkEl : lDir ≠ dkEl := by decide
@[simp] theorem dks2_dkEl_ne_lFln : dkEl ≠ lFln := by decide
@[simp] theorem dks2_lFln_ne_dkEl : lFln ≠ dkEl := by decide
@[simp] theorem dks2_dkEl_ne_lFll : dkEl ≠ lFll := by decide
@[simp] theorem dks2_lFll_ne_dkEl : lFll ≠ dkEl := by decide
@[simp] theorem dks2_dkEl_ne_lFls : dkEl ≠ lFls := by decide
@[simp] theorem dks2_lFls_ne_dkEl : lFls ≠ dkEl := by decide
@[simp] theorem dks2_dkEl_ne_kFu : dkEl ≠ kFu := by decide
@[simp] theorem dks2_kFu_ne_dkEl : kFu ≠ dkEl := by decide
@[simp] theorem dks2_dkEl_ne_kD : dkEl ≠ kD := by decide
@[simp] theorem dks2_kD_ne_dkEl : kD ≠ dkEl := by decide
@[simp] theorem dks2_dkEl_ne_dkA : dkEl ≠ dkA := by decide
@[simp] theorem dks2_dkA_ne_dkEl : dkA ≠ dkEl := by decide
@[simp] theorem dks2_dkEl_ne_dkB : dkEl ≠ dkB := by decide
@[simp] theorem dks2_dkB_ne_dkEl : dkB ≠ dkEl := by decide
@[simp] theorem dks2_dkEl_ne_dkPa : dkEl ≠ dkPa := by decide
@[simp] theorem dks2_dkPa_ne_dkEl : dkPa ≠ dkEl := by decide
@[simp] theorem dks2_dkEl_ne_dkGa : dkEl ≠ dkGa := by decide
@[simp] theorem dks2_dkGa_ne_dkEl : dkGa ≠ dkEl := by decide
@[simp] theorem dks2_dkEl_ne_dkLa : dkEl ≠ dkLa := by decide
@[simp] theorem dks2_dkLa_ne_dkEl : dkLa ≠ dkEl := by decide
@[simp] theorem dks2_dkEl_ne_dkPb : dkEl ≠ dkPb := by decide
@[simp] theorem dks2_dkPb_ne_dkEl : dkPb ≠ dkEl := by decide
@[simp] theorem dks2_dkEl_ne_dkGb : dkEl ≠ dkGb := by decide
@[simp] theorem dks2_dkGb_ne_dkEl : dkGb ≠ dkEl := by decide
@[simp] theorem dks2_dkEl_ne_dkLb : dkEl ≠ dkLb := by decide
@[simp] theorem dks2_dkLb_ne_dkEl : dkLb ≠ dkEl := by decide
@[simp] theorem dks2_dkEl_ne_dkR : dkEl ≠ dkR := by decide
@[simp] theorem dks2_dkR_ne_dkEl : dkR ≠ dkEl := by decide
@[simp] theorem dks2_dkEl_ne_dkT : dkEl ≠ dkT := by decide
@[simp] theorem dks2_dkT_ne_dkEl : dkT ≠ dkEl := by decide
@[simp] theorem dks2_dkEl_ne_dkBb : dkEl ≠ dkBb := by decide
@[simp] theorem dks2_dkBb_ne_dkEl : dkBb ≠ dkEl := by decide
@[simp] theorem dks2_dkEl_ne_dkE : dkEl ≠ dkE := by decide
@[simp] theorem dks2_dkE_ne_dkEl : dkE ≠ dkEl := by decide
@[simp] theorem dks2_dkSl_ne_dkI1 : dkSl ≠ dkI1 := by decide
@[simp] theorem dks2_dkSl_ne_dkI2 : dkSl ≠ dkI2 := by decide
@[simp] theorem dks2_dkSl_ne_dkN1 : dkSl ≠ dkN1 := by decide
@[simp] theorem dks2_dkSl_ne_dkU1 : dkSl ≠ dkU1 := by decide
@[simp] theorem dks2_dkSl_ne_dkN2 : dkSl ≠ dkN2 := by decide
@[simp] theorem dks2_dkSl_ne_dkU2 : dkSl ≠ dkU2 := by decide
@[simp] theorem dks2_dkSl_ne_dkL : dkSl ≠ dkL := by decide
@[simp] theorem dks2_dkSl_ne_dkXa : dkSl ≠ dkXa := by decide
@[simp] theorem dks2_dkSl_ne_dkXb : dkSl ≠ dkXb := by decide
@[simp] theorem dks2_dkSl_ne_dkLa2 : dkSl ≠ dkLa2 := by decide
@[simp] theorem dks2_dkSl_ne_dkLb2 : dkSl ≠ dkLb2 := by decide
@[simp] theorem dks2_dkSl_ne_dkFa : dkSl ≠ dkFa := by decide
@[simp] theorem dks2_dkSl_ne_dkFb : dkSl ≠ dkFb := by decide
@[simp] theorem dks2_dkSl_ne_dkQ : dkSl ≠ dkQ := by decide
@[simp] theorem dks2_dkSl_ne_dkDl : dkSl ≠ dkDl := by decide
@[simp] theorem dks2_dkSl_ne_dkW0 : dkSl ≠ dkW0 := by decide
@[simp] theorem dks2_dkSl_ne_dkFo : dkSl ≠ dkFo := by decide
@[simp] theorem dks2_dkSl_ne_dkCo : dkSl ≠ dkCo := by decide
@[simp] theorem dks2_dkSl_ne_dkUo : dkSl ≠ dkUo := by decide
@[simp] theorem dks2_dkSl_ne_dkEl : dkSl ≠ dkEl := by decide
@[simp] theorem dks2_dkSl_ne_dkLt : dkSl ≠ dkLt := by decide
@[simp] theorem dks2_dkSl_ne_dkC : dkSl ≠ dkC := by decide
@[simp] theorem dks2_dkSl_ne_dkR2 : dkSl ≠ dkR2 := by decide
@[simp] theorem dks2_dkSl_ne_lFl : dkSl ≠ lFl := by decide
@[simp] theorem dks2_lFl_ne_dkSl : lFl ≠ dkSl := by decide
@[simp] theorem dks2_dkSl_ne_lDh : dkSl ≠ lDh := by decide
@[simp] theorem dks2_lDh_ne_dkSl : lDh ≠ dkSl := by decide
@[simp] theorem dks2_dkSl_ne_lDt : dkSl ≠ lDt := by decide
@[simp] theorem dks2_lDt_ne_dkSl : lDt ≠ dkSl := by decide
@[simp] theorem dks2_dkSl_ne_lDg : dkSl ≠ lDg := by decide
@[simp] theorem dks2_lDg_ne_dkSl : lDg ≠ dkSl := by decide
@[simp] theorem dks2_dkSl_ne_lDi : dkSl ≠ lDi := by decide
@[simp] theorem dks2_lDi_ne_dkSl : lDi ≠ dkSl := by decide
@[simp] theorem dks2_dkSl_ne_lRp : dkSl ≠ lRp := by decide
@[simp] theorem dks2_lRp_ne_dkSl : lRp ≠ dkSl := by decide
@[simp] theorem dks2_dkSl_ne_lRn : dkSl ≠ lRn := by decide
@[simp] theorem dks2_lRn_ne_dkSl : lRn ≠ dkSl := by decide
@[simp] theorem dks2_dkSl_ne_lFle : dkSl ≠ lFle := by decide
@[simp] theorem dks2_lFle_ne_dkSl : lFle ≠ dkSl := by decide
@[simp] theorem dks2_dkSl_ne_lKb : dkSl ≠ lKb := by decide
@[simp] theorem dks2_lKb_ne_dkSl : lKb ≠ dkSl := by decide
@[simp] theorem dks2_dkSl_ne_lDir : dkSl ≠ lDir := by decide
@[simp] theorem dks2_lDir_ne_dkSl : lDir ≠ dkSl := by decide
@[simp] theorem dks2_dkSl_ne_lFln : dkSl ≠ lFln := by decide
@[simp] theorem dks2_lFln_ne_dkSl : lFln ≠ dkSl := by decide
@[simp] theorem dks2_dkSl_ne_lFll : dkSl ≠ lFll := by decide
@[simp] theorem dks2_lFll_ne_dkSl : lFll ≠ dkSl := by decide
@[simp] theorem dks2_dkSl_ne_lFls : dkSl ≠ lFls := by decide
@[simp] theorem dks2_lFls_ne_dkSl : lFls ≠ dkSl := by decide
@[simp] theorem dks2_dkSl_ne_kFu : dkSl ≠ kFu := by decide
@[simp] theorem dks2_kFu_ne_dkSl : kFu ≠ dkSl := by decide
@[simp] theorem dks2_dkSl_ne_kD : dkSl ≠ kD := by decide
@[simp] theorem dks2_kD_ne_dkSl : kD ≠ dkSl := by decide
@[simp] theorem dks2_dkSl_ne_dkA : dkSl ≠ dkA := by decide
@[simp] theorem dks2_dkA_ne_dkSl : dkA ≠ dkSl := by decide
@[simp] theorem dks2_dkSl_ne_dkB : dkSl ≠ dkB := by decide
@[simp] theorem dks2_dkB_ne_dkSl : dkB ≠ dkSl := by decide
@[simp] theorem dks2_dkSl_ne_dkPa : dkSl ≠ dkPa := by decide
@[simp] theorem dks2_dkPa_ne_dkSl : dkPa ≠ dkSl := by decide
@[simp] theorem dks2_dkSl_ne_dkGa : dkSl ≠ dkGa := by decide
@[simp] theorem dks2_dkGa_ne_dkSl : dkGa ≠ dkSl := by decide
@[simp] theorem dks2_dkSl_ne_dkLa : dkSl ≠ dkLa := by decide
@[simp] theorem dks2_dkLa_ne_dkSl : dkLa ≠ dkSl := by decide
@[simp] theorem dks2_dkSl_ne_dkPb : dkSl ≠ dkPb := by decide
@[simp] theorem dks2_dkPb_ne_dkSl : dkPb ≠ dkSl := by decide
@[simp] theorem dks2_dkSl_ne_dkGb : dkSl ≠ dkGb := by decide
@[simp] theorem dks2_dkGb_ne_dkSl : dkGb ≠ dkSl := by decide
@[simp] theorem dks2_dkSl_ne_dkLb : dkSl ≠ dkLb := by decide
@[simp] theorem dks2_dkLb_ne_dkSl : dkLb ≠ dkSl := by decide
@[simp] theorem dks2_dkSl_ne_dkR : dkSl ≠ dkR := by decide
@[simp] theorem dks2_dkR_ne_dkSl : dkR ≠ dkSl := by decide
@[simp] theorem dks2_dkSl_ne_dkT : dkSl ≠ dkT := by decide
@[simp] theorem dks2_dkT_ne_dkSl : dkT ≠ dkSl := by decide
@[simp] theorem dks2_dkSl_ne_dkBb : dkSl ≠ dkBb := by decide
@[simp] theorem dks2_dkBb_ne_dkSl : dkBb ≠ dkSl := by decide
@[simp] theorem dks2_dkSl_ne_dkE : dkSl ≠ dkE := by decide
@[simp] theorem dks2_dkE_ne_dkSl : dkE ≠ dkSl := by decide
@[simp] theorem dks2_dkLt_ne_dkI1 : dkLt ≠ dkI1 := by decide
@[simp] theorem dks2_dkLt_ne_dkI2 : dkLt ≠ dkI2 := by decide
@[simp] theorem dks2_dkLt_ne_dkN1 : dkLt ≠ dkN1 := by decide
@[simp] theorem dks2_dkLt_ne_dkU1 : dkLt ≠ dkU1 := by decide
@[simp] theorem dks2_dkLt_ne_dkN2 : dkLt ≠ dkN2 := by decide
@[simp] theorem dks2_dkLt_ne_dkU2 : dkLt ≠ dkU2 := by decide
@[simp] theorem dks2_dkLt_ne_dkL : dkLt ≠ dkL := by decide
@[simp] theorem dks2_dkLt_ne_dkXa : dkLt ≠ dkXa := by decide
@[simp] theorem dks2_dkLt_ne_dkXb : dkLt ≠ dkXb := by decide
@[simp] theorem dks2_dkLt_ne_dkLa2 : dkLt ≠ dkLa2 := by decide
@[simp] theorem dks2_dkLt_ne_dkLb2 : dkLt ≠ dkLb2 := by decide
@[simp] theorem dks2_dkLt_ne_dkFa : dkLt ≠ dkFa := by decide
@[simp] theorem dks2_dkLt_ne_dkFb : dkLt ≠ dkFb := by decide
@[simp] theorem dks2_dkLt_ne_dkQ : dkLt ≠ dkQ := by decide
@[simp] theorem dks2_dkLt_ne_dkDl : dkLt ≠ dkDl := by decide
@[simp] theorem dks2_dkLt_ne_dkW0 : dkLt ≠ dkW0 := by decide
@[simp] theorem dks2_dkLt_ne_dkFo : dkLt ≠ dkFo := by decide
@[simp] theorem dks2_dkLt_ne_dkCo : dkLt ≠ dkCo := by decide
@[simp] theorem dks2_dkLt_ne_dkUo : dkLt ≠ dkUo := by decide
@[simp] theorem dks2_dkLt_ne_dkEl : dkLt ≠ dkEl := by decide
@[simp] theorem dks2_dkLt_ne_dkSl : dkLt ≠ dkSl := by decide
@[simp] theorem dks2_dkLt_ne_dkC : dkLt ≠ dkC := by decide
@[simp] theorem dks2_dkLt_ne_dkR2 : dkLt ≠ dkR2 := by decide
@[simp] theorem dks2_dkLt_ne_lFl : dkLt ≠ lFl := by decide
@[simp] theorem dks2_lFl_ne_dkLt : lFl ≠ dkLt := by decide
@[simp] theorem dks2_dkLt_ne_lDh : dkLt ≠ lDh := by decide
@[simp] theorem dks2_lDh_ne_dkLt : lDh ≠ dkLt := by decide
@[simp] theorem dks2_dkLt_ne_lDt : dkLt ≠ lDt := by decide
@[simp] theorem dks2_lDt_ne_dkLt : lDt ≠ dkLt := by decide
@[simp] theorem dks2_dkLt_ne_lDg : dkLt ≠ lDg := by decide
@[simp] theorem dks2_lDg_ne_dkLt : lDg ≠ dkLt := by decide
@[simp] theorem dks2_dkLt_ne_lDi : dkLt ≠ lDi := by decide
@[simp] theorem dks2_lDi_ne_dkLt : lDi ≠ dkLt := by decide
@[simp] theorem dks2_dkLt_ne_lRp : dkLt ≠ lRp := by decide
@[simp] theorem dks2_lRp_ne_dkLt : lRp ≠ dkLt := by decide
@[simp] theorem dks2_dkLt_ne_lRn : dkLt ≠ lRn := by decide
@[simp] theorem dks2_lRn_ne_dkLt : lRn ≠ dkLt := by decide
@[simp] theorem dks2_dkLt_ne_lFle : dkLt ≠ lFle := by decide
@[simp] theorem dks2_lFle_ne_dkLt : lFle ≠ dkLt := by decide
@[simp] theorem dks2_dkLt_ne_lKb : dkLt ≠ lKb := by decide
@[simp] theorem dks2_lKb_ne_dkLt : lKb ≠ dkLt := by decide
@[simp] theorem dks2_dkLt_ne_lDir : dkLt ≠ lDir := by decide
@[simp] theorem dks2_lDir_ne_dkLt : lDir ≠ dkLt := by decide
@[simp] theorem dks2_dkLt_ne_lFln : dkLt ≠ lFln := by decide
@[simp] theorem dks2_lFln_ne_dkLt : lFln ≠ dkLt := by decide
@[simp] theorem dks2_dkLt_ne_lFll : dkLt ≠ lFll := by decide
@[simp] theorem dks2_lFll_ne_dkLt : lFll ≠ dkLt := by decide
@[simp] theorem dks2_dkLt_ne_lFls : dkLt ≠ lFls := by decide
@[simp] theorem dks2_lFls_ne_dkLt : lFls ≠ dkLt := by decide
@[simp] theorem dks2_dkLt_ne_kFu : dkLt ≠ kFu := by decide
@[simp] theorem dks2_kFu_ne_dkLt : kFu ≠ dkLt := by decide
@[simp] theorem dks2_dkLt_ne_kD : dkLt ≠ kD := by decide
@[simp] theorem dks2_kD_ne_dkLt : kD ≠ dkLt := by decide
@[simp] theorem dks2_dkLt_ne_dkA : dkLt ≠ dkA := by decide
@[simp] theorem dks2_dkA_ne_dkLt : dkA ≠ dkLt := by decide
@[simp] theorem dks2_dkLt_ne_dkB : dkLt ≠ dkB := by decide
@[simp] theorem dks2_dkB_ne_dkLt : dkB ≠ dkLt := by decide
@[simp] theorem dks2_dkLt_ne_dkPa : dkLt ≠ dkPa := by decide
@[simp] theorem dks2_dkPa_ne_dkLt : dkPa ≠ dkLt := by decide
@[simp] theorem dks2_dkLt_ne_dkGa : dkLt ≠ dkGa := by decide
@[simp] theorem dks2_dkGa_ne_dkLt : dkGa ≠ dkLt := by decide
@[simp] theorem dks2_dkLt_ne_dkLa : dkLt ≠ dkLa := by decide
@[simp] theorem dks2_dkLa_ne_dkLt : dkLa ≠ dkLt := by decide
@[simp] theorem dks2_dkLt_ne_dkPb : dkLt ≠ dkPb := by decide
@[simp] theorem dks2_dkPb_ne_dkLt : dkPb ≠ dkLt := by decide
@[simp] theorem dks2_dkLt_ne_dkGb : dkLt ≠ dkGb := by decide
@[simp] theorem dks2_dkGb_ne_dkLt : dkGb ≠ dkLt := by decide
@[simp] theorem dks2_dkLt_ne_dkLb : dkLt ≠ dkLb := by decide
@[simp] theorem dks2_dkLb_ne_dkLt : dkLb ≠ dkLt := by decide
@[simp] theorem dks2_dkLt_ne_dkR : dkLt ≠ dkR := by decide
@[simp] theorem dks2_dkR_ne_dkLt : dkR ≠ dkLt := by decide
@[simp] theorem dks2_dkLt_ne_dkT : dkLt ≠ dkT := by decide
@[simp] theorem dks2_dkT_ne_dkLt : dkT ≠ dkLt := by decide
@[simp] theorem dks2_dkLt_ne_dkBb : dkLt ≠ dkBb := by decide
@[simp] theorem dks2_dkBb_ne_dkLt : dkBb ≠ dkLt := by decide
@[simp] theorem dks2_dkLt_ne_dkE : dkLt ≠ dkE := by decide
@[simp] theorem dks2_dkE_ne_dkLt : dkE ≠ dkLt := by decide
@[simp] theorem dks2_dkC_ne_dkI1 : dkC ≠ dkI1 := by decide
@[simp] theorem dks2_dkC_ne_dkI2 : dkC ≠ dkI2 := by decide
@[simp] theorem dks2_dkC_ne_dkN1 : dkC ≠ dkN1 := by decide
@[simp] theorem dks2_dkC_ne_dkU1 : dkC ≠ dkU1 := by decide
@[simp] theorem dks2_dkC_ne_dkN2 : dkC ≠ dkN2 := by decide
@[simp] theorem dks2_dkC_ne_dkU2 : dkC ≠ dkU2 := by decide
@[simp] theorem dks2_dkC_ne_dkL : dkC ≠ dkL := by decide
@[simp] theorem dks2_dkC_ne_dkXa : dkC ≠ dkXa := by decide
@[simp] theorem dks2_dkC_ne_dkXb : dkC ≠ dkXb := by decide
@[simp] theorem dks2_dkC_ne_dkLa2 : dkC ≠ dkLa2 := by decide
@[simp] theorem dks2_dkC_ne_dkLb2 : dkC ≠ dkLb2 := by decide
@[simp] theorem dks2_dkC_ne_dkFa : dkC ≠ dkFa := by decide
@[simp] theorem dks2_dkC_ne_dkFb : dkC ≠ dkFb := by decide
@[simp] theorem dks2_dkC_ne_dkQ : dkC ≠ dkQ := by decide
@[simp] theorem dks2_dkC_ne_dkDl : dkC ≠ dkDl := by decide
@[simp] theorem dks2_dkC_ne_dkW0 : dkC ≠ dkW0 := by decide
@[simp] theorem dks2_dkC_ne_dkFo : dkC ≠ dkFo := by decide
@[simp] theorem dks2_dkC_ne_dkCo : dkC ≠ dkCo := by decide
@[simp] theorem dks2_dkC_ne_dkUo : dkC ≠ dkUo := by decide
@[simp] theorem dks2_dkC_ne_dkEl : dkC ≠ dkEl := by decide
@[simp] theorem dks2_dkC_ne_dkSl : dkC ≠ dkSl := by decide
@[simp] theorem dks2_dkC_ne_dkLt : dkC ≠ dkLt := by decide
@[simp] theorem dks2_dkC_ne_dkR2 : dkC ≠ dkR2 := by decide
@[simp] theorem dks2_dkC_ne_lFl : dkC ≠ lFl := by decide
@[simp] theorem dks2_lFl_ne_dkC : lFl ≠ dkC := by decide
@[simp] theorem dks2_dkC_ne_lDh : dkC ≠ lDh := by decide
@[simp] theorem dks2_lDh_ne_dkC : lDh ≠ dkC := by decide
@[simp] theorem dks2_dkC_ne_lDt : dkC ≠ lDt := by decide
@[simp] theorem dks2_lDt_ne_dkC : lDt ≠ dkC := by decide
@[simp] theorem dks2_dkC_ne_lDg : dkC ≠ lDg := by decide
@[simp] theorem dks2_lDg_ne_dkC : lDg ≠ dkC := by decide
@[simp] theorem dks2_dkC_ne_lDi : dkC ≠ lDi := by decide
@[simp] theorem dks2_lDi_ne_dkC : lDi ≠ dkC := by decide
@[simp] theorem dks2_dkC_ne_lRp : dkC ≠ lRp := by decide
@[simp] theorem dks2_lRp_ne_dkC : lRp ≠ dkC := by decide
@[simp] theorem dks2_dkC_ne_lRn : dkC ≠ lRn := by decide
@[simp] theorem dks2_lRn_ne_dkC : lRn ≠ dkC := by decide
@[simp] theorem dks2_dkC_ne_lFle : dkC ≠ lFle := by decide
@[simp] theorem dks2_lFle_ne_dkC : lFle ≠ dkC := by decide
@[simp] theorem dks2_dkC_ne_lKb : dkC ≠ lKb := by decide
@[simp] theorem dks2_lKb_ne_dkC : lKb ≠ dkC := by decide
@[simp] theorem dks2_dkC_ne_lDir : dkC ≠ lDir := by decide
@[simp] theorem dks2_lDir_ne_dkC : lDir ≠ dkC := by decide
@[simp] theorem dks2_dkC_ne_lFln : dkC ≠ lFln := by decide
@[simp] theorem dks2_lFln_ne_dkC : lFln ≠ dkC := by decide
@[simp] theorem dks2_dkC_ne_lFll : dkC ≠ lFll := by decide
@[simp] theorem dks2_lFll_ne_dkC : lFll ≠ dkC := by decide
@[simp] theorem dks2_dkC_ne_lFls : dkC ≠ lFls := by decide
@[simp] theorem dks2_lFls_ne_dkC : lFls ≠ dkC := by decide
@[simp] theorem dks2_dkC_ne_kFu : dkC ≠ kFu := by decide
@[simp] theorem dks2_kFu_ne_dkC : kFu ≠ dkC := by decide
@[simp] theorem dks2_dkC_ne_kD : dkC ≠ kD := by decide
@[simp] theorem dks2_kD_ne_dkC : kD ≠ dkC := by decide
@[simp] theorem dks2_dkC_ne_dkA : dkC ≠ dkA := by decide
@[simp] theorem dks2_dkA_ne_dkC : dkA ≠ dkC := by decide
@[simp] theorem dks2_dkC_ne_dkB : dkC ≠ dkB := by decide
@[simp] theorem dks2_dkB_ne_dkC : dkB ≠ dkC := by decide
@[simp] theorem dks2_dkC_ne_dkPa : dkC ≠ dkPa := by decide
@[simp] theorem dks2_dkPa_ne_dkC : dkPa ≠ dkC := by decide
@[simp] theorem dks2_dkC_ne_dkGa : dkC ≠ dkGa := by decide
@[simp] theorem dks2_dkGa_ne_dkC : dkGa ≠ dkC := by decide
@[simp] theorem dks2_dkC_ne_dkLa : dkC ≠ dkLa := by decide
@[simp] theorem dks2_dkLa_ne_dkC : dkLa ≠ dkC := by decide
@[simp] theorem dks2_dkC_ne_dkPb : dkC ≠ dkPb := by decide
@[simp] theorem dks2_dkPb_ne_dkC : dkPb ≠ dkC := by decide
@[simp] theorem dks2_dkC_ne_dkGb : dkC ≠ dkGb := by decide
@[simp] theorem dks2_dkGb_ne_dkC : dkGb ≠ dkC := by decide
@[simp] theorem dks2_dkC_ne_dkLb : dkC ≠ dkLb := by decide
@[simp] theorem dks2_dkLb_ne_dkC : dkLb ≠ dkC := by decide
@[simp] theorem dks2_dkC_ne_dkR : dkC ≠ dkR := by decide
@[simp] theorem dks2_dkR_ne_dkC : dkR ≠ dkC := by decide
@[simp] theorem dks2_dkC_ne_dkT : dkC ≠ dkT := by decide
@[simp] theorem dks2_dkT_ne_dkC : dkT ≠ dkC := by decide
@[simp] theorem dks2_dkC_ne_dkBb : dkC ≠ dkBb := by decide
@[simp] theorem dks2_dkBb_ne_dkC : dkBb ≠ dkC := by decide
@[simp] theorem dks2_dkC_ne_dkE : dkC ≠ dkE := by decide
@[simp] theorem dks2_dkE_ne_dkC : dkE ≠ dkC := by decide
@[simp] theorem dks2_dkR2_ne_dkI1 : dkR2 ≠ dkI1 := by decide
@[simp] theorem dks2_dkR2_ne_dkI2 : dkR2 ≠ dkI2 := by decide
@[simp] theorem dks2_dkR2_ne_dkN1 : dkR2 ≠ dkN1 := by decide
@[simp] theorem dks2_dkR2_ne_dkU1 : dkR2 ≠ dkU1 := by decide
@[simp] theorem dks2_dkR2_ne_dkN2 : dkR2 ≠ dkN2 := by decide
@[simp] theorem dks2_dkR2_ne_dkU2 : dkR2 ≠ dkU2 := by decide
@[simp] theorem dks2_dkR2_ne_dkL : dkR2 ≠ dkL := by decide
@[simp] theorem dks2_dkR2_ne_dkXa : dkR2 ≠ dkXa := by decide
@[simp] theorem dks2_dkR2_ne_dkXb : dkR2 ≠ dkXb := by decide
@[simp] theorem dks2_dkR2_ne_dkLa2 : dkR2 ≠ dkLa2 := by decide
@[simp] theorem dks2_dkR2_ne_dkLb2 : dkR2 ≠ dkLb2 := by decide
@[simp] theorem dks2_dkR2_ne_dkFa : dkR2 ≠ dkFa := by decide
@[simp] theorem dks2_dkR2_ne_dkFb : dkR2 ≠ dkFb := by decide
@[simp] theorem dks2_dkR2_ne_dkQ : dkR2 ≠ dkQ := by decide
@[simp] theorem dks2_dkR2_ne_dkDl : dkR2 ≠ dkDl := by decide
@[simp] theorem dks2_dkR2_ne_dkW0 : dkR2 ≠ dkW0 := by decide
@[simp] theorem dks2_dkR2_ne_dkFo : dkR2 ≠ dkFo := by decide
@[simp] theorem dks2_dkR2_ne_dkCo : dkR2 ≠ dkCo := by decide
@[simp] theorem dks2_dkR2_ne_dkUo : dkR2 ≠ dkUo := by decide
@[simp] theorem dks2_dkR2_ne_dkEl : dkR2 ≠ dkEl := by decide
@[simp] theorem dks2_dkR2_ne_dkSl : dkR2 ≠ dkSl := by decide
@[simp] theorem dks2_dkR2_ne_dkLt : dkR2 ≠ dkLt := by decide
@[simp] theorem dks2_dkR2_ne_dkC : dkR2 ≠ dkC := by decide
@[simp] theorem dks2_dkR2_ne_lFl : dkR2 ≠ lFl := by decide
@[simp] theorem dks2_lFl_ne_dkR2 : lFl ≠ dkR2 := by decide
@[simp] theorem dks2_dkR2_ne_lDh : dkR2 ≠ lDh := by decide
@[simp] theorem dks2_lDh_ne_dkR2 : lDh ≠ dkR2 := by decide
@[simp] theorem dks2_dkR2_ne_lDt : dkR2 ≠ lDt := by decide
@[simp] theorem dks2_lDt_ne_dkR2 : lDt ≠ dkR2 := by decide
@[simp] theorem dks2_dkR2_ne_lDg : dkR2 ≠ lDg := by decide
@[simp] theorem dks2_lDg_ne_dkR2 : lDg ≠ dkR2 := by decide
@[simp] theorem dks2_dkR2_ne_lDi : dkR2 ≠ lDi := by decide
@[simp] theorem dks2_lDi_ne_dkR2 : lDi ≠ dkR2 := by decide
@[simp] theorem dks2_dkR2_ne_lRp : dkR2 ≠ lRp := by decide
@[simp] theorem dks2_lRp_ne_dkR2 : lRp ≠ dkR2 := by decide
@[simp] theorem dks2_dkR2_ne_lRn : dkR2 ≠ lRn := by decide
@[simp] theorem dks2_lRn_ne_dkR2 : lRn ≠ dkR2 := by decide
@[simp] theorem dks2_dkR2_ne_lFle : dkR2 ≠ lFle := by decide
@[simp] theorem dks2_lFle_ne_dkR2 : lFle ≠ dkR2 := by decide
@[simp] theorem dks2_dkR2_ne_lKb : dkR2 ≠ lKb := by decide
@[simp] theorem dks2_lKb_ne_dkR2 : lKb ≠ dkR2 := by decide
@[simp] theorem dks2_dkR2_ne_lDir : dkR2 ≠ lDir := by decide
@[simp] theorem dks2_lDir_ne_dkR2 : lDir ≠ dkR2 := by decide
@[simp] theorem dks2_dkR2_ne_lFln : dkR2 ≠ lFln := by decide
@[simp] theorem dks2_lFln_ne_dkR2 : lFln ≠ dkR2 := by decide
@[simp] theorem dks2_dkR2_ne_lFll : dkR2 ≠ lFll := by decide
@[simp] theorem dks2_lFll_ne_dkR2 : lFll ≠ dkR2 := by decide
@[simp] theorem dks2_dkR2_ne_lFls : dkR2 ≠ lFls := by decide
@[simp] theorem dks2_lFls_ne_dkR2 : lFls ≠ dkR2 := by decide
@[simp] theorem dks2_dkR2_ne_kFu : dkR2 ≠ kFu := by decide
@[simp] theorem dks2_kFu_ne_dkR2 : kFu ≠ dkR2 := by decide
@[simp] theorem dks2_dkR2_ne_kD : dkR2 ≠ kD := by decide
@[simp] theorem dks2_kD_ne_dkR2 : kD ≠ dkR2 := by decide
@[simp] theorem dks2_dkR2_ne_dkA : dkR2 ≠ dkA := by decide
@[simp] theorem dks2_dkA_ne_dkR2 : dkA ≠ dkR2 := by decide
@[simp] theorem dks2_dkR2_ne_dkB : dkR2 ≠ dkB := by decide
@[simp] theorem dks2_dkB_ne_dkR2 : dkB ≠ dkR2 := by decide
@[simp] theorem dks2_dkR2_ne_dkPa : dkR2 ≠ dkPa := by decide
@[simp] theorem dks2_dkPa_ne_dkR2 : dkPa ≠ dkR2 := by decide
@[simp] theorem dks2_dkR2_ne_dkGa : dkR2 ≠ dkGa := by decide
@[simp] theorem dks2_dkGa_ne_dkR2 : dkGa ≠ dkR2 := by decide
@[simp] theorem dks2_dkR2_ne_dkLa : dkR2 ≠ dkLa := by decide
@[simp] theorem dks2_dkLa_ne_dkR2 : dkLa ≠ dkR2 := by decide
@[simp] theorem dks2_dkR2_ne_dkPb : dkR2 ≠ dkPb := by decide
@[simp] theorem dks2_dkPb_ne_dkR2 : dkPb ≠ dkR2 := by decide
@[simp] theorem dks2_dkR2_ne_dkGb : dkR2 ≠ dkGb := by decide
@[simp] theorem dks2_dkGb_ne_dkR2 : dkGb ≠ dkR2 := by decide
@[simp] theorem dks2_dkR2_ne_dkLb : dkR2 ≠ dkLb := by decide
@[simp] theorem dks2_dkLb_ne_dkR2 : dkLb ≠ dkR2 := by decide
@[simp] theorem dks2_dkR2_ne_dkR : dkR2 ≠ dkR := by decide
@[simp] theorem dks2_dkR_ne_dkR2 : dkR ≠ dkR2 := by decide
@[simp] theorem dks2_dkR2_ne_dkT : dkR2 ≠ dkT := by decide
@[simp] theorem dks2_dkT_ne_dkR2 : dkT ≠ dkR2 := by decide
@[simp] theorem dks2_dkR2_ne_dkBb : dkR2 ≠ dkBb := by decide
@[simp] theorem dks2_dkBb_ne_dkR2 : dkBb ≠ dkR2 := by decide
@[simp] theorem dks2_dkR2_ne_dkE : dkR2 ≠ dkE := by decide
@[simp] theorem dks2_dkE_ne_dkR2 : dkE ≠ dkR2 := by decide


def dkParams : List MlS := [kFu, kD, dkA, dkB]
def dkLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, dkPa, dkGa, dkLa, dkPb, dkGb, dkLb, dkR, dkT, dkBb, dkE, dkI1, dkI2, dkN1, dkU1, dkN2, dkU2, dkL, dkXa, dkXb, dkLa2, dkLb2, dkFa, dkFb, dkQ, dkDl, dkW0, dkFo, dkCo, dkUo, dkEl, dkSl, dkLt, dkC, dkR2]
def dkSI : ProgHOL 64 := (.seq (.call (some (some (.local, dkR), none)) fSi [(vv kFu), (vv kD), (vv dkA), (vv dkB)]) (.return (vv dkR)))
def dkEtaA : ProgHOL 64 := (.seq (.assign .local dkT (.load .one (vv dkPa))) (.seq (.assign .local dkBb (.load .one (.op .add [(vv dkPa), (.const 8)]))) (.seq (.call (some (some (.local, dkE), none)) fEc [(vv kFu), (vv kD), (vv dkT), (vv dkBb), (vv dkB)]) (.ite (vv dkE) (.return (.const 1)) dkSI))))
def dkEtaB : ProgHOL 64 := (.seq (.assign .local dkT (.load .one (vv dkPb))) (.seq (.assign .local dkBb (.load .one (.op .add [(vv dkPb), (.const 8)]))) (.seq (.call (some (some (.local, dkE), none)) fEc [(vv kFu), (vv kD), (vv dkT), (vv dkBb), (vv dkA)]) (.ite (vv dkE) (.return (.const 1)) dkSI))))

def fvIdx (x L P : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  .ite (.cmp .equal (vv L) (.const 1)) (.seq (.assign .local x (.const 0)) rest)
    (.ite (.cmp .equal (vv L) (.const 2)) (.seq (.assign .local x (.load .one (.op .add [vv P, .const 8]))) rest) hang)
def dkFv : ProgHOL 64 := fvIdx dkI1 dkLa dkPa (fvIdx dkI2 dkLb dkPb (.ite (.cmp .equal (vv dkI1) (vv dkI2)) (.return (.const 1)) dkSI))
def dkCc : ProgHOL 64 := (.seq (.assign .local dkN1 (.load .one (vv dkPa))) (.seq (.assign .local dkU1 (.load .one (.op .add [(vv dkPa), (.const 8)]))) (.seq (.assign .local dkN2 (.load .one (vv dkPb))) (.seq (.assign .local dkU2 (.load .one (.op .add [(vv dkPb), (.const 8)]))) (.ite (.cmp .equal (vv dkN1) (vv dkN2)) (.seq (.call (some (some (.local, dkL), none)) LLeq.fLsGo [(vv dkU1), (vv dkU2), (.const 0)]) (.ite (.cmp .equal (vv dkL) (.const 0)) hang (.ite (.cmp .equal (vv dkL) (.const 2)) (.return (.const 1)) dkSI))) dkSI)))))
def dkAA : ProgHOL 64 := (.seq (.call (some (some (.local, dkXa), none)) ExG.fGaa [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv dkA)]) (.seq (.call (some (some (.local, dkXb), none)) ExG.fGaa [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv dkB)]) (.seq (.assign .local dkLa2 (.load .one (vv dkXa))) (.seq (.assign .local dkLb2 (.load .one (vv dkXb))) (.ite (.cmp .notEqual (vv dkLa2) (vv dkLb2)) dkSI (.seq (.call (some (some (.local, dkFa), none)) fGetAppFn [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv dkA)]) (.seq (.call (some (some (.local, dkFb), none)) fGetAppFn [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv dkB)]) (.seq (.call (some (some (.local, dkQ), none)) fD [(vv kFu), (vv kD), (vv dkFa), (vv dkFb)]) (.ite (vv dkQ) (.seq (.call (some (some (.local, dkDl), none)) fDl [(vv kFu), (vv kD), (.op .add [(vv dkXa), (.const 8)]), (vv dkLa2), (.op .add [(vv dkXb), (.const 8)]), (vv dkLb2)]) (.ite (vv dkDl) (.return (.const 1)) dkSI)) dkSI)))))))))
def dkLA (C : Ctx) : ProgHOL 64 := (.seq (.assign .local dkW0 (.load .one (vv dkPa))) (.ite (.cmp .equal (vv dkW0) (.const 1)) (.seq (.assign .local dkFo (.load .one (vv dkPb))) (.ite (tagIsE dkFo 3) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv dkFo)) (.seq eViewP (.seq (.assign .local dkCo (.load .one (vv lRp))) (.seq (.assign .local dkUo (.load .one (.op .add [(vv lRp), (.const 8)]))) (.seq (.assign .local dkEl (.load .one (.const (ecell C (C.PO + pinCount + 0))))) (.seq (.assign .local dkSl (.load .one (.const (ecell C (C.PO + PIN_STRING_OF_LIST))))) (.ite (.cmp .equal (vv dkCo) (vv dkSl)) (.ite (.cmp .equal (vv dkUo) (vv dkEl)) (.seq (.assign .local dkLt (.var .global gLit)) (.ite (.op .and [(vv dkLt), (.const 2)]) (.seq (.call (some (some (.local, dkC), none)) Str.fTc [(vv dkA)]) (.seq (.call (some (some (.local, dkR2), none)) fD [(vv kFu), (vv kD), (vv dkC), (vv dkB)]) (.return (vv dkR2)))) dkSI)) dkSI) dkSI)))))))) dkSI)) dkSI))
def dkAL (C : Ctx) : ProgHOL 64 := (.seq (.assign .local dkW0 (.load .one (vv dkPb))) (.ite (.cmp .equal (vv dkW0) (.const 1)) (.seq (.assign .local dkFo (.load .one (vv dkPa))) (.ite (tagIsE dkFo 3) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv dkFo)) (.seq eViewP (.seq (.assign .local dkCo (.load .one (vv lRp))) (.seq (.assign .local dkUo (.load .one (.op .add [(vv lRp), (.const 8)]))) (.seq (.assign .local dkEl (.load .one (.const (ecell C (C.PO + pinCount + 0))))) (.seq (.assign .local dkSl (.load .one (.const (ecell C (C.PO + PIN_STRING_OF_LIST))))) (.ite (.cmp .equal (vv dkCo) (vv dkSl)) (.ite (.cmp .equal (vv dkUo) (vv dkEl)) (.seq (.assign .local dkLt (.var .global gLit)) (.ite (.op .and [(vv dkLt), (.const 2)]) (.seq (.call (some (some (.local, dkC), none)) Str.fTc [(vv dkB)]) (.seq (.call (some (some (.local, dkR2), none)) fD [(vv kFu), (vv kD), (vv dkA), (vv dkC)]) (.return (vv dkR2)))) dkSI)) dkSI) dkSI)))))))) dkSI)) dkSI))



/-- `defeqStuck`'s string-literal arm, the literal on the left (`r.defeq depth c b`). -/
def strArmL (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) (l : ConLeche.Literal) (fo : EIdx) : AM Bool :=
  match l with
  | .strVal st =>
    if fo.tag == ETag.const then do
      match ← view fo with
      | .const cO usO => do
        let el ← emptyLevels
        let sl ← pinStringOfList
        if cO = sl ∧ usO = el ∧ fe.strLit = true then do
          let c ← strLitToConstructor st
          r.defeq depth c b
        else stuckIrrel r fe depth a b
      | _ => stuckIrrel r fe depth a b
    else stuckIrrel r fe depth a b
  | _ => stuckIrrel r fe depth a b

/-- The literal on the right (`r.defeq depth a c`). -/
def strArmR (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (a b : EIdx) (l : ConLeche.Literal) (fo : EIdx) : AM Bool :=
  match l with
  | .strVal st =>
    if fo.tag == ETag.const then do
      match ← view fo with
      | .const cO usO => do
        let el ← emptyLevels
        let sl ← pinStringOfList
        if cO = sl ∧ usO = el ∧ fe.strLit = true then do
          let c ← strLitToConstructor st
          r.defeq depth a c
        else stuckIrrel r fe depth a b
      | _ => stuckIrrel r fe depth a b
    else stuckIrrel r fe depth a b
  | _ => stuckIrrel r fe depth a b


structure DkCodes2 (C : Ctx) : Prop where
  gaf : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  gaa : C.code.lookup ExG.fGaa = some ([(pFu, .one), (pH, .one)], ExG.gaaBody C, .one)
  ls : C.code.lookup LLeq.fLsGo = some (LLeq.lsParams.map (fun p => (p, ShapeHOL.one)), LLeq.lsGoBody, .one)
  dl : DlCodes C
  d : C.code.lookup fD = some (pmap dParams, dE C, .one)
  tc : C.code.lookup Str.fTc = some ([(Str.tcH, ShapeHOL.one)], Str.tcBody C, .one)


structure DkCodes (C : Ctx) (v : Bool) : Prop where
  si : C.code.lookup fSi = some (siParams.map (fun p => (p, ShapeHOL.one)), siBody, .one)
  ec : C.code.lookup fEc = some (ecParams.map (fun p => (p, ShapeHOL.one)), ecBody v C, .one)

def dkBody (C : Ctx) : ProgHOL 64 := prologue dkLocals (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv dkA)) (.seq eViewP (.seq (.assign .local dkPa (vv lRp)) (.seq (.assign .local dkGa (vv lDg)) (.seq (.assign .local dkLa (vv lRn)) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv dkB)) (.seq eViewP (.seq (.assign .local dkPb (vv lRp)) (.seq (.assign .local dkGb (vv lDg)) (.seq (.assign .local dkLb (vv lRn)) (.ite (.cmp .equal (vv dkGa) (.const 8)) (.ite (.cmp .equal (vv dkGb) (.const 4)) (dkLA C) (.ite (.cmp .equal (vv dkGb) (.const 5)) dkEtaB dkSI)) (.ite (.cmp .equal (vv dkGa) (.const 4)) (.ite (.cmp .equal (vv dkGb) (.const 8)) (dkAL C) (.ite (.cmp .equal (vv dkGb) (.const 4)) dkAA (.ite (.cmp .equal (vv dkGb) (.const 5)) dkEtaB dkSI))) (.ite (.cmp .equal (vv dkGa) (.const 1)) (.ite (.cmp .equal (vv dkGb) (.const 1)) dkFv (.ite (.cmp .equal (vv dkGb) (.const 5)) dkEtaB dkSI)) (.ite (.cmp .equal (vv dkGa) (.const 3)) (.ite (.cmp .equal (vv dkGb) (.const 3)) dkCc (.ite (.cmp .equal (vv dkGb) (.const 5)) dkEtaB dkSI)) (.ite (.cmp .equal (vv dkGa) (.const 5)) dkEtaA (.ite (.cmp .equal (vv dkGb) (.const 5)) dkEtaB dkSI))))))))))))))))))

section
variable {σ : Type}

theorem specR_fvIdxI {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M0 : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x Lx Px : MlS) (ty : EIdx) (i : Nat) (P : BitVec 64)
    (hx : x ∈ D) (hL : Γ.get Lx = some (BitVec.ofNat 64 (encEView (.fvar i ty)).length)) (hP : Γ.get Px = some P)
    (hM : ∀ y ∈ wordsAt P (encEView (.fvar i ty)), y ∈ M0) (hl : (encEView (.fvar i ty)).length < 2 ^ 61)
    (hk : i < 2 ^ 64 → SpecR (Inv C s ((x, BitVec.ofNat 64 i) :: Γ) M0 D) rest s m R) :
    SpecR (Inv C s Γ M0 D) (fvIdx x Lx Px rest) s m R := by
  have er : encEView (.fvar i ty) = Enc.idxW ty :: limbs i := rfl
  unfold fvIdx
  have hlen : (encEView (.fvar i ty)).length = (limbs i).length + 1 := by rw [er]; simp
  have hl58 : (limbs i).length + 1 < 2 ^ 61 := by rw [← hlen]; exact hl
  rw [hlen] at hL
  rcases (by omega : (limbs i).length = 0 ∨ (limbs i).length = 1 ∨ 2 ≤ (limbs i).length) with h0 | h1 | h2
  · have hi0 : i = 0 := by have := (limbs_length_lt_iff i 0).mp (by omega); simpa using this
    subst hi0
    refine specR_ifI _ 1 (by simp [sev, hL, h0, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_assignI x (.const 0) (BitVec.ofNat 64 0) hx rfl ?_
    exact hk (by decide)
  · have hiB : i < B := by have := (limbs_length_lt_iff i 1).mp (by omega); simpa using this
    have h1w : BitVec.ofNat 64 ((limbs i).length + 1) ≠ 1#64 := by rw [h1]; decide
    refine specR_ifI _ 0 (by simp [sev, hL, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact h1w) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, hL, h1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    have hx1 : (Enc.idxW ty :: limbs i)[1]'(by simp; omega) = BitVec.ofNat 64 i := by
      show (limbs i)[0]'(by omega) = _
      rw [limbs_getElem i 0 (by omega)]; simp [Nat.mod_eq_of_lt hiB]
    refine specR_loadI' x _ (P + 8) (P + BitVec.ofNat 64 (8 * 1)) (BitVec.ofNat 64 i) hx
      (by simp [sev, hP]) rfl (hM _ (by
        have := wordsAt_get P (Enc.idxW ty :: limbs i) 1 (by simp; omega) []
        rw [hx1] at this; simpa [er] using this)) ?_
    exact hk hiB
  · have h1w : BitVec.ofNat 64 ((limbs i).length + 1) ≠ 1#64 := by
      intro h0; have := congrArg BitVec.toNat h0; simp at this; omega
    have h2w : BitVec.ofNat 64 ((limbs i).length + 1) ≠ 2#64 := by
      intro h0; have := congrArg BitVec.toNat h0; simp at this; omega
    refine specR_ifI _ 0 (by simp [sev, hL, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact h1w) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, hL, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact h2w) (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_hangI

end

section
variable {σ : Type}
variable (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) (hok : CtxOK C) (hc : DkCodes C mode.verifiedChecks)
  (hSI : ∀ (H : List (BitVec 64)) s1 d a b, C.H <+: H → SpecR (σ := σ) (Pre (ctxH C H) s1 (siParams.zip
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b])) siBody s1
    (stuckIrrel (knot mode C n) C.fe d a b) (PostB (ctxH C H)))
  (hEC : ∀ (H : List (BitVec 64)) s1 d ty bd e, C.H <+: H → SpecR (σ := σ) (Pre (ctxH C H) s1 (ecParams.zip
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty, Enc.idxW bd, Enc.idxW e])) (ecBody mode.verifiedChecks C) s1
    (etaCert mode (knot mode C n) C.fe d ty bd e) (PostB (ctxH C H)))
include hc hSI hEC


abbrev DK : List MlS := ctxLocals ++ dkLocals

theorem dk_si (d : Nat) (a b : EIdx) (Hb H : List (BitVec 64)) (hpb : C.H <+: Hb) (hbH : Hb <+: H) (s : AState)
    (Γ : Env) (M : Mem) (hFu : Γ.get kFu = some (BitVec.ofNat 64 n)) (hDd : Γ.get kD = some (BitVec.ofNat 64 d))
    (hA : Γ.get dkA = some (Enc.idxW a)) (hB : Γ.get dkB = some (Enc.idxW b)) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M DK) dkSI s (stuckIrrel (knot mode C n) C.fe d a b) (PostB (ctxH C Hb)) := by
  unfold dkSI
  refine specR_congr (m' := stuckIrrel (knot mode C n) C.fe d a b >>= fun r => pure r) (by simp) ?_
  refine specR_callNIH (C := ctxH C H) dkR fSi siParams [vv kFu, vv kD, vv dkA, vv dkB] siBody
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (by decide) rfl (by decide) hc.si
    ⟨by simp [hFu], by simp [hDd], by simp [hA], by simp [hB], trivial⟩
    (PostB (ctxH C H)) (fun r_ w _ _ => w = boolW r_) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu siParams _ rfl hlk) (hSI H s d a b (hpb.trans hbH)))
    (fun r w s1 H1 hp1 hw => ?_)
  subst hw
  exact specR_returnI _ (boolW r) (by simp) (fun t ht => ⟨H1, hbH.trans hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem dk_etaA (d : Nat) (a b ty bd : EIdx) (Hb H : List (BitVec 64)) (hpb : C.H <+: Hb) (hbH : Hb <+: H) (s : AState)
    (Γ : Env) (M : Mem) (P : BitVec 64) (hFu : Γ.get kFu = some (BitVec.ofNat 64 n))
    (hDd : Γ.get kD = some (BitVec.ofNat 64 d)) (hA : Γ.get dkA = some (Enc.idxW a))
    (hB : Γ.get dkB = some (Enc.idxW b)) (hP : Γ.get dkPa = some P)
    (hm0 : (P + BitVec.ofNat 64 0, Enc.idxW ty) ∈ M) (hm1 : (P + BitVec.ofNat 64 8, Enc.idxW bd) ∈ M) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M DK) dkEtaA s
      (do if ← etaCert mode (knot mode C n) C.fe d ty bd b then pure true else stuckIrrel (knot mode C n) C.fe d a b)
      (PostB (ctxH C Hb)) := by
  unfold dkEtaA
  refine specR_loadI' dkT (vv dkPa) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp [hP]) (by simp) hm0 ?_
  refine specR_loadI' dkBb _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW bd) (by decide) (by simp [sev, hP]) rfl hm1 ?_
  refine specR_dropM ?_
  refine specR_callNIH (C := ctxH C H) dkE fEc ecParams [vv kFu, vv kD, vv dkT, vv dkBb, vv dkB] (ecBody mode.verifiedChecks C)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty, Enc.idxW bd, Enc.idxW b] (by decide) rfl (by decide) hc.ec
    ⟨by simp [hFu], by simp [hDd], by simp, by simp, by simp [hB], trivial⟩
    (PostB (ctxH C H)) (fun r_ w _ _ => w = boolW r_) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ecParams _ rfl hlk) (hEC H s d ty bd b (hpb.trans hbH)))
    (fun r w s1 H1 hp1 hw => ?_)
  subst hw
  cases r
  · refine specR_ifI _ 0 (by simp [boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact dk_si mode n C hc hSI hEC d a b Hb H1 hpb (hbH.trans hp1) s1 _ _ (by simp [hFu]) (by simp [hDd]) (by simp [hA])
      (by simp [hB])
  refine specR_ifI _ 1 (by simp [boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
  simp only [↓reduceIte]
  exact specR_returnI _ 1 rfl (fun t ht => ⟨H1, hbH.trans hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem dk_etaB (d : Nat) (a b ty bd : EIdx) (Hb H : List (BitVec 64)) (hpb : C.H <+: Hb) (hbH : Hb <+: H) (s : AState)
    (Γ : Env) (M : Mem) (P : BitVec 64) (hFu : Γ.get kFu = some (BitVec.ofNat 64 n))
    (hDd : Γ.get kD = some (BitVec.ofNat 64 d)) (hA : Γ.get dkA = some (Enc.idxW a))
    (hB : Γ.get dkB = some (Enc.idxW b)) (hP : Γ.get dkPb = some P)
    (hm0 : (P + BitVec.ofNat 64 0, Enc.idxW ty) ∈ M) (hm1 : (P + BitVec.ofNat 64 8, Enc.idxW bd) ∈ M) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M DK) dkEtaB s
      (do if ← etaCert mode (knot mode C n) C.fe d ty bd a then pure true else stuckIrrel (knot mode C n) C.fe d a b)
      (PostB (ctxH C Hb)) := by
  unfold dkEtaB
  refine specR_loadI' dkT (vv dkPb) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp [hP]) (by simp) hm0 ?_
  refine specR_loadI' dkBb _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW bd) (by decide) (by simp [sev, hP]) rfl hm1 ?_
  refine specR_dropM ?_
  refine specR_callNIH (C := ctxH C H) dkE fEc ecParams [vv kFu, vv kD, vv dkT, vv dkBb, vv dkA] (ecBody mode.verifiedChecks C)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty, Enc.idxW bd, Enc.idxW a] (by decide) rfl (by decide) hc.ec
    ⟨by simp [hFu], by simp [hDd], by simp, by simp, by simp [hA], trivial⟩
    (PostB (ctxH C H)) (fun r_ w _ _ => w = boolW r_) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ecParams _ rfl hlk) (hEC H s d ty bd a (hpb.trans hbH)))
    (fun r w s1 H1 hp1 hw => ?_)
  subst hw
  cases r
  · refine specR_ifI _ 0 (by simp [boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact dk_si mode n C hc hSI hEC d a b Hb H1 hpb (hbH.trans hp1) s1 _ _ (by simp [hFu]) (by simp [hDd]) (by simp [hA])
      (by simp [hB])
  refine specR_ifI _ 1 (by simp [boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
  simp only [↓reduceIte]
  exact specR_returnI _ 1 rfl (fun t ht => ⟨H1, hbH.trans hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)


variable (hc2 : DkCodes2 C)
  (hD : ∀ (H : List (BitVec 64)) s1 d a b, C.H <+: H → Callee (σ := σ) (ctxH C H) dParams
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (dE C) s1 ((knot mode C n).defeq d a b)
    (PostB (ctxH C H)))
  (hLS : ∀ (H : List (BitVec 64)) s1 (u v : LsIdx), C.H <+: H →
    SpecR (σ := σ) (Pre (ctxH C H) s1 (LLeq.lsParams.zip [Enc.idxW u, Enc.idxW v, BitVec.ofNat 64 0])) LLeq.lsGoBody
      s1 (lvlsEq? u v) (LLeq.PostOB (ctxH C H)))
  (hTC : ∀ (H : List (BitVec 64)) s1 h str, C.H <+: H → s1.store.view h = some (.lit (.strVal str)) →
    SpecR (σ := σ) (Pre (ctxH C H) s1 [(Str.tcH, Enc.idxW h)]) (Str.tcBody C) s1 (strLitToConstructor str) (PostK (ctxH C H)))
include hok hc2 hD hLS hTC

theorem dk_fv (d : Nat) (a b : EIdx) (Hb H : List (BitVec 64)) (hpb : C.H <+: Hb) (hbH : Hb <+: H) (s : AState) (Γ : Env) (M : Mem)
    (hFu : Γ.get kFu = some (BitVec.ofNat 64 n)) (hDd : Γ.get kD = some (BitVec.ofNat 64 d))
    (hA : Γ.get dkA = some (Enc.idxW a)) (hB : Γ.get dkB = some (Enc.idxW b)) (i j : Nat) (ty1 ty2 : EIdx) (Pa Pb : BitVec 64)
    (hLa : Γ.get dkLa = some (BitVec.ofNat 64 (encEView (.fvar i ty1)).length)) (hPa : Γ.get dkPa = some Pa)
    (hMa : ∀ y ∈ wordsAt Pa (encEView (.fvar i ty1)), y ∈ M) (hla : (encEView (.fvar i ty1)).length < 2 ^ 61)
    (hLb : Γ.get dkLb = some (BitVec.ofNat 64 (encEView (.fvar j ty2)).length)) (hPb : Γ.get dkPb = some Pb)
    (hMb : ∀ y ∈ wordsAt Pb (encEView (.fvar j ty2)), y ∈ M) (hlb : (encEView (.fvar j ty2)).length < 2 ^ 61) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M DK) dkFv s
      (if i == j then pure true else stuckIrrel (knot mode C n) C.fe d a b) (PostB (ctxH C Hb)) := by
  unfold dkFv
  refine specR_fvIdxI dkI1 dkLa dkPa ty1 i Pa (by decide) hLa hPa hMa hla (fun hi => ?_)
  refine specR_fvIdxI dkI2 dkLb dkPb ty2 j Pb (by decide) (by simp [hLb]) (by simp [hPb]) hMb hlb (fun hj => ?_)
  by_cases hij : i = j
  · subst hij
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [beq_self_eq_true, ↓reduceIte]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H, hbH, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  have hw : BitVec.ofNat 64 i ≠ BitVec.ofNat 64 j := by
    intro x; apply hij
    have := congrArg BitVec.toNat x
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at this
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hw]) (fun h => absurd rfl h) (fun _ => ?_)
  simp only [show (i == j) = false by simpa using hij, Bool.false_eq_true, ↓reduceIte]
  exact dk_si mode n C hc hSI hEC d a b Hb H hpb (hbH) s _ _ (by simp [hFu]) (by simp [hDd]) (by simp [hA]) (by simp [hB])

theorem dk_cc (d : Nat) (a b : EIdx) (Hb H : List (BitVec 64)) (hpb : C.H <+: Hb) (hbH : Hb <+: H) (s : AState) (Γ : Env) (M : Mem)
    (hFu : Γ.get kFu = some (BitVec.ofNat 64 n)) (hDd : Γ.get kD = some (BitVec.ofNat 64 d))
    (hA : Γ.get dkA = some (Enc.idxW a)) (hB : Γ.get dkB = some (Enc.idxW b)) (n1 n2 : NIdx) (us1 us2 : LsIdx) (Pa Pb : BitVec 64)
    (hPa : Γ.get dkPa = some Pa) (hPb : Γ.get dkPb = some Pb)
    (hma0 : (Pa + BitVec.ofNat 64 0, Enc.idxW n1) ∈ M) (hma1 : (Pa + BitVec.ofNat 64 8, Enc.idxW us1) ∈ M)
    (hmb0 : (Pb + BitVec.ofNat 64 0, Enc.idxW n2) ∈ M) (hmb1 : (Pb + BitVec.ofNat 64 8, Enc.idxW us2) ∈ M) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M DK) dkCc s
      (do if n1 = n2 then do
            if ← liftFueled "level comparison" (← lvlsEq? us1 us2) then pure true
            else stuckIrrel (knot mode C n) C.fe d a b
          else stuckIrrel (knot mode C n) C.fe d a b) (PostB (ctxH C Hb)) := by
  unfold dkCc
  refine specR_loadI' dkN1 (vv dkPa) Pa (Pa + BitVec.ofNat 64 0) (Enc.idxW n1) (by decide) (by simp [hPa]) (by simp) hma0 ?_
  refine specR_loadI' dkU1 _ (Pa + 8) (Pa + BitVec.ofNat 64 8) (Enc.idxW us1) (by decide) (by simp [sev, hPa]) rfl hma1 ?_
  refine specR_loadI' dkN2 (vv dkPb) Pb (Pb + BitVec.ofNat 64 0) (Enc.idxW n2) (by decide) (by simp [hPb]) (by simp) hmb0 ?_
  refine specR_loadI' dkU2 _ (Pb + 8) (Pb + BitVec.ofNat 64 8) (Enc.idxW us2) (by decide) (by simp [sev, hPb]) rfl hmb1 ?_
  refine specR_dropM ?_
  by_cases hn : n1 = n2
  swap
  · have hne : Enc.idxW n1 ≠ Enc.idxW n2 := fun e => hn (Enc.idxW_inj e)
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [if_neg hn]
    exact dk_si mode n C hc hSI hEC d a b Hb H hpb (hbH) s _ _ (by simp [hFu]) (by simp [hDd]) (by simp [hA]) (by simp [hB])
  subst hn
  refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
  rw [if_pos rfl]
  refine specR_callNIH (C := ctxH C H) dkL LLeq.fLsGo LLeq.lsParams [vv dkU1, vv dkU2, .const 0] LLeq.lsGoBody
    [Enc.idxW us1, Enc.idxW us2, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc2.ls
    ⟨by simp, by simp, rfl, trivial⟩
    (LLeq.PostOB (ctxH C H)) (fun o w _ H' => H' = H ∧ w = LLeq.obW o)
    (fun o w s' st ⟨hw, hsr⟩ => ⟨H, List.prefix_refl _, ⟨rfl, hw⟩, hsr⟩)
    (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu LLeq.lsParams _ rfl hlk)
      (hLS H s us1 us2 (hpb.trans hbH))) (fun ol w s1 H1 _ ⟨eH, hw⟩ => ?_)
  subst H1; subst hw
  rcases ol with _ | ⟨_ | _⟩
  · exact specR_ifI _ 1 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
  · refine specR_ifI _ 0 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [liftFueled, pure_bind, Bool.false_eq_true, ↓reduceIte]
    exact dk_si mode n C hc hSI hEC d a b Hb H hpb (hbH) s1 _ _ (by simp [hFu]) (by simp [hDd]) (by simp [hA]) (by simp [hB])
  refine specR_ifI _ 0 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_ifI _ 1 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
  simp only [liftFueled, pure_bind, ↓reduceIte]
  exact specR_returnI _ 1 rfl (fun t ht => ⟨H, hbH, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem dk_aa (d : Nat) (a b : EIdx) (Hb H : List (BitVec 64)) (hpb : C.H <+: Hb) (hbH : Hb <+: H) (s : AState) (Γ : Env) (M : Mem)
    (hFu : Γ.get kFu = some (BitVec.ofNat 64 n)) (hDd : Γ.get kD = some (BitVec.ofNat 64 d))
    (hA : Γ.get dkA = some (Enc.idxW a)) (hB : Γ.get dkB = some (Enc.idxW b)) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M DK) dkAA s
      (do
        let aa ← getAppArgs coreWalkFuel a
        let bb ← getAppArgs coreWalkFuel b
        if aa.length = bb.length then do
          let fa ← getAppFn coreWalkFuel a
          let fb ← getAppFn coreWalkFuel b
          if ← (knot mode C n).defeq d fa fb then do
            if ← defEqList (knot mode C n) C.fe d aa bb then pure true
            else stuckIrrel (knot mode C n) C.fe d a b
          else stuckIrrel (knot mode C n) C.fe d a b
        else stuckIrrel (knot mode C n) C.fe d a b) (PostB (ctxH C Hb)) := by
  unfold dkAA
  refine specR_callNIH (C := ctxH C H) dkXa ExG.fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv dkA] (ExG.gaaBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW a] (by decide) rfl (by decide) hc2.gaa
    ⟨rfl, by simp [hA], trivial⟩
    (PostA (ctxH C H)) (fun xs w _ H1 => ∃ o1, w = cellA C o1 ∧ BlkAt H1 o1 (xs.map Enc.idxW))
    (fun xs w s' st ⟨H1, o1, hp, hw, hb, hsr⟩ => ⟨H1, hp, ⟨o1, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (ExG.gaa_spec C hok hc2.gaa coreWalkFuel CV.coreWalkFuel_lt H a s))
    (fun aa w s1 H1 hp1 ⟨o1, hw, hba⟩ => ?_)
  subst hw
  refine specR_callNIH (C := ctxH C H1) dkXb ExG.fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv dkB] (ExG.gaaBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW b] (by decide) rfl (by decide) hc2.gaa
    ⟨rfl, by simp [hB], trivial⟩
    (PostA (ctxH C H1)) (fun xs w _ H2 => ∃ o2, w = cellA C o2 ∧ BlkAt H2 o2 (xs.map Enc.idxW))
    (fun xs w s' st ⟨H2, o2, hp, hw, hb, hsr⟩ => ⟨H2, hp, ⟨o2, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (ExG.gaa_spec C hok hc2.gaa coreWalkFuel CV.coreWalkFuel_lt H1 b s1))
    (fun bb w s2 H2 hp2 ⟨o2, hw, hbb⟩ => ?_)
  subst hw
  have hba2 := blkAt_mono hba hp2
  have hbH2 : Hb <+: H2 := hbH.trans (hp1.trans hp2)
  have hpH2 : C.H <+: H2 := hpb.trans hbH2
  refine UD.specR_heapLoadI' (C := ctxH C H2) dkLa2 (vv dkXa) o1 _ (by have h := hba2.1; simp only [List.length_map] at h; exact h)
    (by decide) (by simp <;> rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H2) dkLb2 (vv dkXb) o2 _ (by have h := hbb.1; simp only [List.length_map] at h; exact h)
    (by decide) (by simp <;> rfl) ?_
  refine specR_atEntry fun t ht => ?_
  have hsza := blk_small0 (ctxOK_H hok H2) ht.sr hba2
  have hszb := blk_small0 (ctxOK_H hok H2) ht.sr hbb
  simp only [List.length_map] at hsza hszb
  by_cases hln : aa.length = bb.length
  swap
  · have hne : BitVec.ofNat 64 aa.length ≠ BitVec.ofNat 64 bb.length := by
      intro x; apply hln
      have := congrArg BitVec.toNat x
      simp only [BitVec.toNat_ofNat] at this
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun _ => ?_) (fun h => absurd h (by decide))
    rw [if_neg hln]
    exact dk_si mode n C hc hSI hEC d a b Hb H2 hpb (hbH2) s2 _ _ (by simp [hFu]) (by simp [hDd]) (by simp [hA]) (by simp [hB])
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hln]) (fun h => absurd rfl h) (fun _ => ?_)
  rw [if_pos hln]
  refine specR_callNIM (C := ctxH C H2) dkFa fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv dkA]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW a] (by decide) rfl (by decide) hc2.gaf
    ⟨rfl, by simp [hA], trivial⟩
    (fun x w' s' st => getAppFn coreWalkFuel a s2 = .ok (x, s') ∧ Post (ctxH C H2) s2 x w' s' st)
    (fun x w' s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec (ctxH C H2) hc2.gaf coreWalkFuel a s2 CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun fa w' s' st ⟨hrun, hw, hs, _⟩ => ?_)
  subst hw
  have hs' : s2 = s' := hs.symm
  subst hs'
  refine specR_callNIM (C := ctxH C H2) dkFb fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv dkB]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW b] (by decide) rfl (by decide) hc2.gaf
    ⟨rfl, by simp [hB], trivial⟩
    (fun x w' s' st => getAppFn coreWalkFuel b s2 = .ok (x, s') ∧ Post (ctxH C H2) s2 x w' s' st)
    (fun x w' s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec (ctxH C H2) hc2.gaf coreWalkFuel b s2 CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun fb w' s' st ⟨hrun, hw, hs, _⟩ => ?_)
  subst hw
  have hs' : s2 = s' := hs.symm
  subst hs'

  refine specR_callNIH (C := ctxH C H2) dkQ fD dParams [vv kFu, vv kD, vv dkFa, vv dkFb] (dE C)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW fa, Enc.idxW fb] (by decide) rfl (by decide) hc2.d
    ⟨by simp [hFu], by simp [hDd], by simp, by simp, trivial⟩
    (PostB (ctxH C H2)) (fun r_ w _ _ => w = boolW r_) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => hD H2 s2 d fa fb hpH2 u hu (fun i hi _ => hlk i (by omega)))
    (fun q w s3 H3 hp3 hw => ?_)
  subst hw
  have hbH3 : Hb <+: H3 := hbH2.trans hp3
  cases q
  · refine specR_ifI _ 0 (by simp [boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact dk_si mode n C hc hSI hEC d a b Hb H3 hpb (hbH3) s3 _ _ (by simp [hFu]) (by simp [hDd]) (by simp [hA]) (by simp [hB])
  refine specR_ifI _ 1 (by simp [boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
  simp only [↓reduceIte]
  have hba3 := blkAt_mono hba2 hp3
  have hbb3 := blkAt_mono hbb hp3
  refine specR_callNIH (C := ctxH C H3) dkDl fDl dlParams
    [vv kFu, vv kD, .op .add [vv dkXa, .const 8], vv dkLa2, .op .add [vv dkXb, .const 8], vv dkLb2] dlBody
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, cellA C (o1 + 1), BitVec.ofNat 64 aa.length, cellA C (o2 + 1),
      BitVec.ofNat 64 bb.length] (by decide) rfl (by decide) hc2.dl.self
    ⟨by simp [hFu], by simp [hDd], by simp [sev]; exact cellA_add8 C o1, by simp,
      by simp [sev]; exact cellA_add8 C o2, by simp, trivial⟩
    (PostB (ctxH C H3)) (fun r_ w _ _ => w = boolW r_) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu dlParams _ rfl hlk)
      (dl_spec mode n C hc2.dl d (fun H s1 hp a b => hD H s1 d a b hp) aa bb (o1 + 1) (o2 + 1) H3 s3 (hpH2.trans hp3)
        (fun j hj => by have h := hba3.2 j (by simpa using hj); rw [List.getElem_map] at h; exact h)
        (fun j hj => by have h := hbb3.2 j (by simpa using hj); rw [List.getElem_map] at h; exact h)
        (by omega) (by omega)))
    (fun r w s4 H4 hp4 hw => ?_)
  subst hw
  have hbH4 : Hb <+: H4 := hbH3.trans hp4
  cases r
  · refine specR_ifI _ 0 (by simp [boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact dk_si mode n C hc hSI hEC d a b Hb H4 hpb (hbH4) s4 _ _ (by simp [hFu]) (by simp [hDd]) (by simp [hA]) (by simp [hB])
  refine specR_ifI _ 1 (by simp [boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
  simp only [↓reduceIte]
  exact specR_returnI _ 1 rfl (fun t ht => ⟨H4, hbH4, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem dk_la (d : Nat) (a b : EIdx) (Hb H : List (BitVec 64)) (hpb : C.H <+: Hb) (hbH : Hb <+: H) (s : AState) (Γ : Env) (M : Mem)
    (hFu : Γ.get kFu = some (BitVec.ofNat 64 n)) (hDd : Γ.get kD = some (BitVec.ofNat 64 d))
    (hA : Γ.get dkA = some (Enc.idxW a)) (hB : Γ.get dkB = some (Enc.idxW b)) (l : ConLeche.Literal) (fo x : EIdx) (Pl Pp : BitVec 64)
    (hPl : Γ.get dkPa = some Pl) (hPp : Γ.get dkPb = some Pp)
    (hMl : ∀ y ∈ wordsAt Pl (encEView (.lit l)), y ∈ M) (hmp0 : (Pp + BitVec.ofNat 64 0, Enc.idxW fo) ∈ M)
    (hv : s.store.view a = some (.lit l))
    (hFle : Γ.get lFle = some C.FLe) (hDir : Γ.get lDir = some C.L.DIR) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M DK) (dkLA C) s (strArmL (knot mode C n) C.fe d a b l fo) (PostB (ctxH C Hb)) := by
  unfold dkLA strArmL
  have hpH : C.H <+: H := hpb.trans hbH
  cases l with
  | natVal m =>
    refine specR_loadI' dkW0 (vv dkPa) Pl (Pl + BitVec.ofNat 64 0) 0 (by decide) (by simp [hPl]) (by simp)
      (hMl _ (by simpa [encEView, Enc.encLit] using wordsAt_mem0 Pl 0 (limbs m) [])) ?_
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    dsimp only
    exact dk_si mode n C hc hSI hEC d a b Hb H hpb (hbH) s _ _ (by simp [hFu]) (by simp [hDd]) (by simp [hA]) (by simp [hB])
  | strVal st =>
    refine specR_loadI' dkW0 (vv dkPa) Pl (Pl + BitVec.ofNat 64 0) 1 (by decide) (by simp [hPl]) (by simp)
      (hMl _ (by simpa [encEView, Enc.encLit] using wordsAt_mem0 Pl 1 (strW st) [])) ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    dsimp only
    refine specR_loadI' dkFo (vv dkPb) Pp (Pp + BitVec.ofNat 64 0) (Enc.idxW fo) (by decide) (by simp [hPp]) (by simp) hmp0 ?_
    refine specR_dropM ?_
    refine Knot.specR_tagIteV dkFo fo 3 (by decide) (by decide) (by simp) (fun htc => ?_) (fun htc => ?_)
    swap
    · rw [if_neg (show ¬ (fo.tag == ETag.const) = true by simpa [ETag.const] using htc)]
      exact dk_si mode n C hc hSI hEC d a b Hb H hpb (hbH) s _ _ (by simp [hFu]) (by simp [hDd]) (by simp [hA]) (by simp [hB])
    rw [if_pos (show (fo.tag == ETag.const) = true by simp [htc, ETag.const])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp [hFle]) ?_
    refine specR_assignI lDh (vv dkFo) (Enc.idxW fo) (by decide) (by simp) ?_
    refine specR_viewP (C := ctxH C H) fo (by simp) (by simp; rfl)
      (by simp [hDir]; rfl) (by decide) (fun v P hv2 htn _ => ?_)
    refine specR_congr (Big.view_bind_eq fo v _ s hv2) ?_
    have h3 : v.tagN = 3 := by rw [htn, htc]; rfl
    obtain ⟨cO, usO, rfl⟩ := UD.tagN_const h3
    dsimp only
    refine specR_loadI' dkCo (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW cO) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW cO) [Enc.idxW usO] []) ?_
    refine specR_loadI' dkUo _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW usO) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW cO) (Enc.idxW usO) [] []) ?_
    refine specR_dropM ?_
    refine specR_pinXI (C := ctxH C H) (ctxOK_H hok H) emptyLevels 0 C.pins.emptyLevels _
      (fun s hp => pinEmptyLevels_run (ctxOK_H hok H) hp) (pin_emptyLevels_cell (ctxOK_H hok H)) dkEl (by decide) ?_
    unfold pinStringOfList
    refine specR_pinAtI (C := ctxH C H) (ctxOK_H hok H) PIN_STRING_OF_LIST (by decide) dkSl (by decide) ?_
    by_cases h1 : cO = (ctxH C H).pins.names[PIN_STRING_OF_LIST]'(by rw [(ctxOK_H hok H).pinsRel.1]; decide)
    swap
    · have hne : Enc.idxW cO ≠ Enc.idxW ((ctxH C H).pins.names[PIN_STRING_OF_LIST]'(by rw [(ctxOK_H hok H).pinsRel.1]; decide)) :=
        fun e => h1 (Enc.idxW_inj e)
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun h => absurd rfl h) (fun _ => ?_)
      rw [if_neg (fun h => h1 h.1)]
      exact dk_si mode n C hc hSI hEC d a b Hb H hpb (hbH) s _ _ (by simp [hFu]) (by simp [hDd]) (by simp [hA]) (by simp [hB])
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, h1]) (fun _ => ?_) (fun h => absurd h (by decide))
    by_cases h2 : usO = (ctxH C H).pins.emptyLevels
    swap
    · have hne : Enc.idxW usO ≠ Enc.idxW (ctxH C H).pins.emptyLevels := fun e => h2 (Enc.idxW_inj e)
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun h => absurd rfl h) (fun _ => ?_)
      rw [if_neg (fun h => h2 h.2.1)]
      exact dk_si mode n C hc hSI hEC d a b Hb H hpb (hbH) s _ _ (by simp [hFu]) (by simp [hDd]) (by simp [hA]) (by simp [hB])
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, h2]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_gLitI dkLt (by decide) ?_
    by_cases hsl : (ctxH C H).fe.strLit = true
    swap
    · have hf : (ctxH C H).fe.strLit = false := by simpa using hsl
      refine specR_ifI _ 0 (by simp [sev, litW_and2, hf, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
      rw [if_neg (fun h => hsl h.2.2)]
      exact dk_si mode n C hc hSI hEC d a b Hb H hpb (hbH) s _ _ (by simp [hFu]) (by simp [hDd]) (by simp [hA]) (by simp [hB])
    refine specR_ifI _ 2 (by simp [sev, litW_and2, hsl, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
    rw [if_pos ⟨h1, h2, hsl⟩]
    refine specR_callKH (C := ctxH C H) dkC Str.fTc [Str.tcH] [vv dkA] (Str.tcBody C) [Enc.idxW a] (by decide) rfl (by decide)
      hc2.tc ⟨by simp [hA], trivial⟩ (hTC H s a st hpH hv) (fun c s1 H1 hp1 => ?_)
    refine specR_congr (m' := (knot mode C n).defeq d c b >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H1) dkR2 fD dParams [vv kFu, vv kD, vv dkC, vv dkB] (dE C)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c, Enc.idxW b] (by decide) rfl (by decide) hc2.d
      ⟨by simp [hFu], by simp [hDd], by simp [hA, hB], by simp [hA, hB], trivial⟩
      (PostB (ctxH C H1)) (fun r_ w _ _ => w = boolW r_) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => hD H1 s1 d c b (hpH.trans hp1) u hu (fun i hi _ => hlk i (by omega)))
      (fun r w s2 H2 hp2 hw => ?_)
    subst hw
    exact specR_returnI _ (boolW r) (by simp) (fun t ht => ⟨H2, hbH.trans (hp1.trans hp2), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem dk_al (d : Nat) (a b : EIdx) (Hb H : List (BitVec 64)) (hpb : C.H <+: Hb) (hbH : Hb <+: H) (s : AState) (Γ : Env) (M : Mem)
    (hFu : Γ.get kFu = some (BitVec.ofNat 64 n)) (hDd : Γ.get kD = some (BitVec.ofNat 64 d))
    (hA : Γ.get dkA = some (Enc.idxW a)) (hB : Γ.get dkB = some (Enc.idxW b)) (l : ConLeche.Literal) (fo x : EIdx) (Pl Pp : BitVec 64)
    (hPl : Γ.get dkPb = some Pl) (hPp : Γ.get dkPa = some Pp)
    (hMl : ∀ y ∈ wordsAt Pl (encEView (.lit l)), y ∈ M) (hmp0 : (Pp + BitVec.ofNat 64 0, Enc.idxW fo) ∈ M)
    (hv : s.store.view b = some (.lit l))
    (hFle : Γ.get lFle = some C.FLe) (hDir : Γ.get lDir = some C.L.DIR) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M DK) (dkAL C) s (strArmR (knot mode C n) C.fe d a b l fo) (PostB (ctxH C Hb)) := by
  unfold dkAL strArmR
  have hpH : C.H <+: H := hpb.trans hbH
  cases l with
  | natVal m =>
    refine specR_loadI' dkW0 (vv dkPb) Pl (Pl + BitVec.ofNat 64 0) 0 (by decide) (by simp [hPl]) (by simp)
      (hMl _ (by simpa [encEView, Enc.encLit] using wordsAt_mem0 Pl 0 (limbs m) [])) ?_
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    dsimp only
    exact dk_si mode n C hc hSI hEC d a b Hb H hpb (hbH) s _ _ (by simp [hFu]) (by simp [hDd]) (by simp [hA]) (by simp [hB])
  | strVal st =>
    refine specR_loadI' dkW0 (vv dkPb) Pl (Pl + BitVec.ofNat 64 0) 1 (by decide) (by simp [hPl]) (by simp)
      (hMl _ (by simpa [encEView, Enc.encLit] using wordsAt_mem0 Pl 1 (strW st) [])) ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    dsimp only
    refine specR_loadI' dkFo (vv dkPa) Pp (Pp + BitVec.ofNat 64 0) (Enc.idxW fo) (by decide) (by simp [hPp]) (by simp) hmp0 ?_
    refine specR_dropM ?_
    refine Knot.specR_tagIteV dkFo fo 3 (by decide) (by decide) (by simp) (fun htc => ?_) (fun htc => ?_)
    swap
    · rw [if_neg (show ¬ (fo.tag == ETag.const) = true by simpa [ETag.const] using htc)]
      exact dk_si mode n C hc hSI hEC d a b Hb H hpb (hbH) s _ _ (by simp [hFu]) (by simp [hDd]) (by simp [hA]) (by simp [hB])
    rw [if_pos (show (fo.tag == ETag.const) = true by simp [htc, ETag.const])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp [hFle]) ?_
    refine specR_assignI lDh (vv dkFo) (Enc.idxW fo) (by decide) (by simp) ?_
    refine specR_viewP (C := ctxH C H) fo (by simp) (by simp; rfl)
      (by simp [hDir]; rfl) (by decide) (fun v P hv2 htn _ => ?_)
    refine specR_congr (Big.view_bind_eq fo v _ s hv2) ?_
    have h3 : v.tagN = 3 := by rw [htn, htc]; rfl
    obtain ⟨cO, usO, rfl⟩ := UD.tagN_const h3
    dsimp only
    refine specR_loadI' dkCo (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW cO) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW cO) [Enc.idxW usO] []) ?_
    refine specR_loadI' dkUo _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW usO) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW cO) (Enc.idxW usO) [] []) ?_
    refine specR_dropM ?_
    refine specR_pinXI (C := ctxH C H) (ctxOK_H hok H) emptyLevels 0 C.pins.emptyLevels _
      (fun s hp => pinEmptyLevels_run (ctxOK_H hok H) hp) (pin_emptyLevels_cell (ctxOK_H hok H)) dkEl (by decide) ?_
    unfold pinStringOfList
    refine specR_pinAtI (C := ctxH C H) (ctxOK_H hok H) PIN_STRING_OF_LIST (by decide) dkSl (by decide) ?_
    by_cases h1 : cO = (ctxH C H).pins.names[PIN_STRING_OF_LIST]'(by rw [(ctxOK_H hok H).pinsRel.1]; decide)
    swap
    · have hne : Enc.idxW cO ≠ Enc.idxW ((ctxH C H).pins.names[PIN_STRING_OF_LIST]'(by rw [(ctxOK_H hok H).pinsRel.1]; decide)) :=
        fun e => h1 (Enc.idxW_inj e)
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun h => absurd rfl h) (fun _ => ?_)
      rw [if_neg (fun h => h1 h.1)]
      exact dk_si mode n C hc hSI hEC d a b Hb H hpb (hbH) s _ _ (by simp [hFu]) (by simp [hDd]) (by simp [hA]) (by simp [hB])
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, h1]) (fun _ => ?_) (fun h => absurd h (by decide))
    by_cases h2 : usO = (ctxH C H).pins.emptyLevels
    swap
    · have hne : Enc.idxW usO ≠ Enc.idxW (ctxH C H).pins.emptyLevels := fun e => h2 (Enc.idxW_inj e)
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun h => absurd rfl h) (fun _ => ?_)
      rw [if_neg (fun h => h2 h.2.1)]
      exact dk_si mode n C hc hSI hEC d a b Hb H hpb (hbH) s _ _ (by simp [hFu]) (by simp [hDd]) (by simp [hA]) (by simp [hB])
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, h2]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_gLitI dkLt (by decide) ?_
    by_cases hsl : (ctxH C H).fe.strLit = true
    swap
    · have hf : (ctxH C H).fe.strLit = false := by simpa using hsl
      refine specR_ifI _ 0 (by simp [sev, litW_and2, hf, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
      rw [if_neg (fun h => hsl h.2.2)]
      exact dk_si mode n C hc hSI hEC d a b Hb H hpb (hbH) s _ _ (by simp [hFu]) (by simp [hDd]) (by simp [hA]) (by simp [hB])
    refine specR_ifI _ 2 (by simp [sev, litW_and2, hsl, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
    rw [if_pos ⟨h1, h2, hsl⟩]
    refine specR_callKH (C := ctxH C H) dkC Str.fTc [Str.tcH] [vv dkB] (Str.tcBody C) [Enc.idxW b] (by decide) rfl (by decide)
      hc2.tc ⟨by simp [hB], trivial⟩ (hTC H s b st hpH hv) (fun c s1 H1 hp1 => ?_)
    refine specR_congr (m' := (knot mode C n).defeq d a c >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H1) dkR2 fD dParams [vv kFu, vv kD, vv dkA, vv dkC] (dE C)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW c] (by decide) rfl (by decide) hc2.d
      ⟨by simp [hFu], by simp [hDd], by simp [hA, hB], by simp [hA, hB], trivial⟩
      (PostB (ctxH C H1)) (fun r_ w _ _ => w = boolW r_) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => hD H1 s1 d a c (hpH.trans hp1) u hu (fun i hi _ => hlk i (by omega)))
      (fun r w s2 H2 hp2 hw => ?_)
    subst hw
    exact specR_returnI _ (boolW r) (by simp) (fun t ht => ⟨H2, hbH.trans (hp1.trans hp2), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem dk_spec (s : AState) (d : Nat) (a b : EIdx) :
    SpecR (σ := σ) (Pre C s (dkParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b])) (dkBody C) s
      (defeqStuck mode (knot mode C n) C.fe d a b) (PostB C) := by
  refine specR_prologue (postB_locals C) (Knot.params_none C dkLocals dkParams _ (by decide) (by decide)) ?_
  unfold defeqStuck
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv dkA) (Enc.idxW a) (by decide) (by simp +decide [Env.get, dkParams, ctxEnv]) ?_
  refine specR_viewP a (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
    (fun va Pa hva htna hla => ?_)
  refine specR_congr (Big.view_bind_eq a va _ s hva) ?_
  refine specR_assignI dkPa (vv lRp) Pa (by decide) (by simp) ?_
  refine specR_assignI dkGa (vv lDg) (BitVec.ofNat 64 va.tagN) (by decide) (by simp) ?_
  refine specR_assignI dkLa (vv lRn) (BitVec.ofNat 64 (encEView va).length) (by decide) (by simp) ?_
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv dkB) (Enc.idxW b) (by decide) (by simp +decide [Env.get, dkParams, ctxEnv]) ?_
  refine specR_viewP b (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
    (fun vb Pb hvb htnb hlb => ?_)
  refine specR_congr (Big.view_bind_eq b vb _ s hvb) ?_
  refine specR_assignI dkPb (vv lRp) Pb (by decide) (by simp) ?_
  refine specR_assignI dkGb (vv lDg) (BitVec.ofNat 64 vb.tagN) (by decide) (by simp) ?_
  refine specR_assignI dkLb (vv lRn) (BitVec.ofNat 64 (encEView vb).length) (by decide) (by simp) ?_
  rcases va with i1 | ⟨i1, ty1⟩ | u1 | ⟨n1, us1⟩ | ⟨f1, x1⟩ | ⟨ty1, bd1⟩ | ⟨fty1, fbd1⟩ | ⟨lt1, lv1, lb1⟩ | l1 | ⟨sn1, pi1, pe1⟩ <;> rcases vb with i2 | ⟨i2, ty2⟩ | u2 | ⟨n2, us2⟩ | ⟨f2, x2⟩ | ⟨ty2, bd2⟩ | ⟨fty2, fbd2⟩ | ⟨lt2, lv2, lb2⟩ | l2 | ⟨sn2, pi2, pe2⟩
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact dk_etaB mode n C hc hSI hEC d a b ty2 bd2 C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ Pb (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 Pb (Enc.idxW ty2) [Enc.idxW bd2] _)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 Pb (Enc.idxW ty2) (Enc.idxW bd2) [] _)
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact dk_fv mode n C hok hc hSI hEC hc2 hD hLS hTC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) i1 i2 ty1 ty2 Pa Pb (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
      (fun y hy => List.mem_append_right _ (List.mem_append_left _ hy)) hla (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (fun y hy => List.mem_append_left _ hy) hlb
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact dk_etaB mode n C hc hSI hEC d a b ty2 bd2 C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ Pb (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 Pb (Enc.idxW ty2) [Enc.idxW bd2] _)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 Pb (Enc.idxW ty2) (Enc.idxW bd2) [] _)
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact dk_etaB mode n C hc hSI hEC d a b ty2 bd2 C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ Pb (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 Pb (Enc.idxW ty2) [Enc.idxW bd2] _)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 Pb (Enc.idxW ty2) (Enc.idxW bd2) [] _)
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact dk_cc mode n C hok hc hSI hEC hc2 hD hLS hTC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) n1 n2 us1 us2 Pa Pb (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
      (List.mem_append_right _ (by simpa [encEView, Enc.encConst] using wordsAt_mem0 Pa (Enc.idxW n1) [Enc.idxW us1] []))
      (List.mem_append_right _ (by simpa [encEView, Enc.encConst] using wordsAt_mem1 Pa (Enc.idxW n1) (Enc.idxW us1) [] []))
      (by simpa [encEView, Enc.encConst] using wordsAt_mem0 Pb (Enc.idxW n2) [Enc.idxW us2] _)
      (by simpa [encEView, Enc.encConst] using wordsAt_mem1 Pb (Enc.idxW n2) (Enc.idxW us2) [] _)
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact dk_etaB mode n C hc hSI hEC d a b ty2 bd2 C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ Pb (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 Pb (Enc.idxW ty2) [Enc.idxW bd2] _)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 Pb (Enc.idxW ty2) (Enc.idxW bd2) [] _)
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact dk_aa mode n C hok hc hSI hEC hc2 hD hLS hTC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact dk_etaB mode n C hc hSI hEC d a b ty2 bd2 C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ Pb (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 Pb (Enc.idxW ty2) [Enc.idxW bd2] _)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 Pb (Enc.idxW ty2) (Enc.idxW bd2) [] _)
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact dk_al mode n C hok hc hSI hEC hc2 hD hLS hTC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) l2 f1 x1 Pb Pa (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
      (fun y hy => List.mem_append_left _ hy)
      (List.mem_append_right _ (by simpa [encEView, Enc.encApp] using wordsAt_mem0 Pa (Enc.idxW f1) [Enc.idxW x1] [])) hvb (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact dk_etaA mode n C hc hSI hEC d a b ty1 bd1 C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ Pa (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
      (List.mem_append_right _ (by simpa [encEView, Enc.encBind] using wordsAt_mem0 Pa (Enc.idxW ty1) [Enc.idxW bd1] []))
      (List.mem_append_right _ (by simpa [encEView, Enc.encBind] using wordsAt_mem1 Pa (Enc.idxW ty1) (Enc.idxW bd1) [] []))
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact dk_etaA mode n C hc hSI hEC d a b ty1 bd1 C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ Pa (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
      (List.mem_append_right _ (by simpa [encEView, Enc.encBind] using wordsAt_mem0 Pa (Enc.idxW ty1) [Enc.idxW bd1] []))
      (List.mem_append_right _ (by simpa [encEView, Enc.encBind] using wordsAt_mem1 Pa (Enc.idxW ty1) (Enc.idxW bd1) [] []))
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact dk_etaA mode n C hc hSI hEC d a b ty1 bd1 C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ Pa (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
      (List.mem_append_right _ (by simpa [encEView, Enc.encBind] using wordsAt_mem0 Pa (Enc.idxW ty1) [Enc.idxW bd1] []))
      (List.mem_append_right _ (by simpa [encEView, Enc.encBind] using wordsAt_mem1 Pa (Enc.idxW ty1) (Enc.idxW bd1) [] []))
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact dk_etaA mode n C hc hSI hEC d a b ty1 bd1 C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ Pa (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
      (List.mem_append_right _ (by simpa [encEView, Enc.encBind] using wordsAt_mem0 Pa (Enc.idxW ty1) [Enc.idxW bd1] []))
      (List.mem_append_right _ (by simpa [encEView, Enc.encBind] using wordsAt_mem1 Pa (Enc.idxW ty1) (Enc.idxW bd1) [] []))
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact dk_etaA mode n C hc hSI hEC d a b ty1 bd1 C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ Pa (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
      (List.mem_append_right _ (by simpa [encEView, Enc.encBind] using wordsAt_mem0 Pa (Enc.idxW ty1) [Enc.idxW bd1] []))
      (List.mem_append_right _ (by simpa [encEView, Enc.encBind] using wordsAt_mem1 Pa (Enc.idxW ty1) (Enc.idxW bd1) [] []))
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact dk_etaA mode n C hc hSI hEC d a b ty1 bd1 C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ Pa (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
      (List.mem_append_right _ (by simpa [encEView, Enc.encBind] using wordsAt_mem0 Pa (Enc.idxW ty1) [Enc.idxW bd1] []))
      (List.mem_append_right _ (by simpa [encEView, Enc.encBind] using wordsAt_mem1 Pa (Enc.idxW ty1) (Enc.idxW bd1) [] []))
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact dk_etaA mode n C hc hSI hEC d a b ty1 bd1 C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ Pa (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
      (List.mem_append_right _ (by simpa [encEView, Enc.encBind] using wordsAt_mem0 Pa (Enc.idxW ty1) [Enc.idxW bd1] []))
      (List.mem_append_right _ (by simpa [encEView, Enc.encBind] using wordsAt_mem1 Pa (Enc.idxW ty1) (Enc.idxW bd1) [] []))
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact dk_etaA mode n C hc hSI hEC d a b ty1 bd1 C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ Pa (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
      (List.mem_append_right _ (by simpa [encEView, Enc.encBind] using wordsAt_mem0 Pa (Enc.idxW ty1) [Enc.idxW bd1] []))
      (List.mem_append_right _ (by simpa [encEView, Enc.encBind] using wordsAt_mem1 Pa (Enc.idxW ty1) (Enc.idxW bd1) [] []))
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact dk_etaA mode n C hc hSI hEC d a b ty1 bd1 C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ Pa (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
      (List.mem_append_right _ (by simpa [encEView, Enc.encBind] using wordsAt_mem0 Pa (Enc.idxW ty1) [Enc.idxW bd1] []))
      (List.mem_append_right _ (by simpa [encEView, Enc.encBind] using wordsAt_mem1 Pa (Enc.idxW ty1) (Enc.idxW bd1) [] []))
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact dk_etaA mode n C hc hSI hEC d a b ty1 bd1 C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ Pa (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
      (List.mem_append_right _ (by simpa [encEView, Enc.encBind] using wordsAt_mem0 Pa (Enc.idxW ty1) [Enc.idxW bd1] []))
      (List.mem_append_right _ (by simpa [encEView, Enc.encBind] using wordsAt_mem1 Pa (Enc.idxW ty1) (Enc.idxW bd1) [] []))
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact dk_etaB mode n C hc hSI hEC d a b ty2 bd2 C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ Pb (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 Pb (Enc.idxW ty2) [Enc.idxW bd2] _)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 Pb (Enc.idxW ty2) (Enc.idxW bd2) [] _)
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact dk_etaB mode n C hc hSI hEC d a b ty2 bd2 C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ Pb (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 Pb (Enc.idxW ty2) [Enc.idxW bd2] _)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 Pb (Enc.idxW ty2) (Enc.idxW bd2) [] _)
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact dk_la mode n C hok hc hSI hEC hc2 hD hLS hTC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) l1 f2 x2 Pa Pb (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
      (fun y hy => List.mem_append_right _ (List.mem_append_left _ hy))
      (by simpa [encEView, Enc.encApp] using wordsAt_mem0 Pb (Enc.idxW f2) [Enc.idxW x2] _) hva (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact dk_etaB mode n C hc hSI hEC d a b ty2 bd2 C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ Pb (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 Pb (Enc.idxW ty2) [Enc.idxW bd2] _)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 Pb (Enc.idxW ty2) (Enc.idxW bd2) [] _)
  · refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact dk_etaB mode n C hc hSI hEC d a b ty2 bd2 C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ Pb (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 Pb (Enc.idxW ty2) [Enc.idxW bd2] _)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 Pb (Enc.idxW ty2) (Enc.idxW bd2) [] _)
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact dk_si mode n C hc hSI hEC d a b C.H C.H (List.prefix_refl _) (List.prefix_refl _) s _ _ (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv]) (by simp +decide [Env.get, dkParams, ctxEnv])

end

end ConPanqueque.T.WC
