import ConPanqueque.T.Core.DefeqProj
import ConPanqueque.T.Core.InferIOArms
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `etaCert`: η for a one-sided λ against a stuck term

The depth must be below `2^62` (else halt). At the verified mode (static `v`) the λ body's full-grade type is
compared with the ∀'s codomain.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def ecT := ofString "etc_ect"
def ecB := ofString "etc_ecb"
def ecS := ofString "etc_ecs"
def ecN := ofString "etc_ecn"
def ecT1 := ofString "etc_ect1"
def ecH := ofString "etc_ech"
def ecT2 := ofString "etc_ect2"
def ecC2 := ofString "etc_ecc2"
def ecQ := ofString "etc_ecq"
def ecF := ofString "etc_ecf"
def ecL := ofString "etc_ecl"
def ecR2 := ofString "etc_ecr2"
def ecD1 := ofString "etc_ecd1"
def ecE := ofString "etc_ece"
def ecI := ofString "etc_eci"
def ecK := ofString "etc_eck"
def ecZ := ofString "etc_ecz"
def fEc := ofString "etaCert"

@[simp] theorem etc_ecT_ne_ecB : ecT ≠ ecB := by decide
@[simp] theorem etc_ecT_ne_ecS : ecT ≠ ecS := by decide
@[simp] theorem etc_ecT_ne_ecN : ecT ≠ ecN := by decide
@[simp] theorem etc_ecT_ne_ecT1 : ecT ≠ ecT1 := by decide
@[simp] theorem etc_ecT_ne_ecH : ecT ≠ ecH := by decide
@[simp] theorem etc_ecT_ne_ecT2 : ecT ≠ ecT2 := by decide
@[simp] theorem etc_ecT_ne_ecC2 : ecT ≠ ecC2 := by decide
@[simp] theorem etc_ecT_ne_ecQ : ecT ≠ ecQ := by decide
@[simp] theorem etc_ecT_ne_ecF : ecT ≠ ecF := by decide
@[simp] theorem etc_ecT_ne_ecL : ecT ≠ ecL := by decide
@[simp] theorem etc_ecT_ne_ecR2 : ecT ≠ ecR2 := by decide
@[simp] theorem etc_ecT_ne_ecD1 : ecT ≠ ecD1 := by decide
@[simp] theorem etc_ecT_ne_ecE : ecT ≠ ecE := by decide
@[simp] theorem etc_ecT_ne_ecI : ecT ≠ ecI := by decide
@[simp] theorem etc_ecT_ne_ecK : ecT ≠ ecK := by decide
@[simp] theorem etc_ecT_ne_ecZ : ecT ≠ ecZ := by decide
@[simp] theorem etc_ecT_ne_lFl : ecT ≠ lFl := by decide
@[simp] theorem etc_lFl_ne_ecT : lFl ≠ ecT := by decide
@[simp] theorem etc_ecT_ne_lDh : ecT ≠ lDh := by decide
@[simp] theorem etc_lDh_ne_ecT : lDh ≠ ecT := by decide
@[simp] theorem etc_ecT_ne_lDt : ecT ≠ lDt := by decide
@[simp] theorem etc_lDt_ne_ecT : lDt ≠ ecT := by decide
@[simp] theorem etc_ecT_ne_lDg : ecT ≠ lDg := by decide
@[simp] theorem etc_lDg_ne_ecT : lDg ≠ ecT := by decide
@[simp] theorem etc_ecT_ne_lDi : ecT ≠ lDi := by decide
@[simp] theorem etc_lDi_ne_ecT : lDi ≠ ecT := by decide
@[simp] theorem etc_ecT_ne_lRp : ecT ≠ lRp := by decide
@[simp] theorem etc_lRp_ne_ecT : lRp ≠ ecT := by decide
@[simp] theorem etc_ecT_ne_lRn : ecT ≠ lRn := by decide
@[simp] theorem etc_lRn_ne_ecT : lRn ≠ ecT := by decide
@[simp] theorem etc_ecT_ne_lFle : ecT ≠ lFle := by decide
@[simp] theorem etc_lFle_ne_ecT : lFle ≠ ecT := by decide
@[simp] theorem etc_ecT_ne_lKb : ecT ≠ lKb := by decide
@[simp] theorem etc_lKb_ne_ecT : lKb ≠ ecT := by decide
@[simp] theorem etc_ecT_ne_lDir : ecT ≠ lDir := by decide
@[simp] theorem etc_lDir_ne_ecT : lDir ≠ ecT := by decide
@[simp] theorem etc_ecT_ne_lFln : ecT ≠ lFln := by decide
@[simp] theorem etc_lFln_ne_ecT : lFln ≠ ecT := by decide
@[simp] theorem etc_ecT_ne_lFll : ecT ≠ lFll := by decide
@[simp] theorem etc_lFll_ne_ecT : lFll ≠ ecT := by decide
@[simp] theorem etc_ecT_ne_lFls : ecT ≠ lFls := by decide
@[simp] theorem etc_lFls_ne_ecT : lFls ≠ ecT := by decide
@[simp] theorem etc_ecT_ne_kFu : ecT ≠ kFu := by decide
@[simp] theorem etc_kFu_ne_ecT : kFu ≠ ecT := by decide
@[simp] theorem etc_ecT_ne_kD : ecT ≠ kD := by decide
@[simp] theorem etc_kD_ne_ecT : kD ≠ ecT := by decide
@[simp] theorem etc_ecB_ne_ecT : ecB ≠ ecT := by decide
@[simp] theorem etc_ecB_ne_ecS : ecB ≠ ecS := by decide
@[simp] theorem etc_ecB_ne_ecN : ecB ≠ ecN := by decide
@[simp] theorem etc_ecB_ne_ecT1 : ecB ≠ ecT1 := by decide
@[simp] theorem etc_ecB_ne_ecH : ecB ≠ ecH := by decide
@[simp] theorem etc_ecB_ne_ecT2 : ecB ≠ ecT2 := by decide
@[simp] theorem etc_ecB_ne_ecC2 : ecB ≠ ecC2 := by decide
@[simp] theorem etc_ecB_ne_ecQ : ecB ≠ ecQ := by decide
@[simp] theorem etc_ecB_ne_ecF : ecB ≠ ecF := by decide
@[simp] theorem etc_ecB_ne_ecL : ecB ≠ ecL := by decide
@[simp] theorem etc_ecB_ne_ecR2 : ecB ≠ ecR2 := by decide
@[simp] theorem etc_ecB_ne_ecD1 : ecB ≠ ecD1 := by decide
@[simp] theorem etc_ecB_ne_ecE : ecB ≠ ecE := by decide
@[simp] theorem etc_ecB_ne_ecI : ecB ≠ ecI := by decide
@[simp] theorem etc_ecB_ne_ecK : ecB ≠ ecK := by decide
@[simp] theorem etc_ecB_ne_ecZ : ecB ≠ ecZ := by decide
@[simp] theorem etc_ecB_ne_lFl : ecB ≠ lFl := by decide
@[simp] theorem etc_lFl_ne_ecB : lFl ≠ ecB := by decide
@[simp] theorem etc_ecB_ne_lDh : ecB ≠ lDh := by decide
@[simp] theorem etc_lDh_ne_ecB : lDh ≠ ecB := by decide
@[simp] theorem etc_ecB_ne_lDt : ecB ≠ lDt := by decide
@[simp] theorem etc_lDt_ne_ecB : lDt ≠ ecB := by decide
@[simp] theorem etc_ecB_ne_lDg : ecB ≠ lDg := by decide
@[simp] theorem etc_lDg_ne_ecB : lDg ≠ ecB := by decide
@[simp] theorem etc_ecB_ne_lDi : ecB ≠ lDi := by decide
@[simp] theorem etc_lDi_ne_ecB : lDi ≠ ecB := by decide
@[simp] theorem etc_ecB_ne_lRp : ecB ≠ lRp := by decide
@[simp] theorem etc_lRp_ne_ecB : lRp ≠ ecB := by decide
@[simp] theorem etc_ecB_ne_lRn : ecB ≠ lRn := by decide
@[simp] theorem etc_lRn_ne_ecB : lRn ≠ ecB := by decide
@[simp] theorem etc_ecB_ne_lFle : ecB ≠ lFle := by decide
@[simp] theorem etc_lFle_ne_ecB : lFle ≠ ecB := by decide
@[simp] theorem etc_ecB_ne_lKb : ecB ≠ lKb := by decide
@[simp] theorem etc_lKb_ne_ecB : lKb ≠ ecB := by decide
@[simp] theorem etc_ecB_ne_lDir : ecB ≠ lDir := by decide
@[simp] theorem etc_lDir_ne_ecB : lDir ≠ ecB := by decide
@[simp] theorem etc_ecB_ne_lFln : ecB ≠ lFln := by decide
@[simp] theorem etc_lFln_ne_ecB : lFln ≠ ecB := by decide
@[simp] theorem etc_ecB_ne_lFll : ecB ≠ lFll := by decide
@[simp] theorem etc_lFll_ne_ecB : lFll ≠ ecB := by decide
@[simp] theorem etc_ecB_ne_lFls : ecB ≠ lFls := by decide
@[simp] theorem etc_lFls_ne_ecB : lFls ≠ ecB := by decide
@[simp] theorem etc_ecB_ne_kFu : ecB ≠ kFu := by decide
@[simp] theorem etc_kFu_ne_ecB : kFu ≠ ecB := by decide
@[simp] theorem etc_ecB_ne_kD : ecB ≠ kD := by decide
@[simp] theorem etc_kD_ne_ecB : kD ≠ ecB := by decide
@[simp] theorem etc_ecS_ne_ecT : ecS ≠ ecT := by decide
@[simp] theorem etc_ecS_ne_ecB : ecS ≠ ecB := by decide
@[simp] theorem etc_ecS_ne_ecN : ecS ≠ ecN := by decide
@[simp] theorem etc_ecS_ne_ecT1 : ecS ≠ ecT1 := by decide
@[simp] theorem etc_ecS_ne_ecH : ecS ≠ ecH := by decide
@[simp] theorem etc_ecS_ne_ecT2 : ecS ≠ ecT2 := by decide
@[simp] theorem etc_ecS_ne_ecC2 : ecS ≠ ecC2 := by decide
@[simp] theorem etc_ecS_ne_ecQ : ecS ≠ ecQ := by decide
@[simp] theorem etc_ecS_ne_ecF : ecS ≠ ecF := by decide
@[simp] theorem etc_ecS_ne_ecL : ecS ≠ ecL := by decide
@[simp] theorem etc_ecS_ne_ecR2 : ecS ≠ ecR2 := by decide
@[simp] theorem etc_ecS_ne_ecD1 : ecS ≠ ecD1 := by decide
@[simp] theorem etc_ecS_ne_ecE : ecS ≠ ecE := by decide
@[simp] theorem etc_ecS_ne_ecI : ecS ≠ ecI := by decide
@[simp] theorem etc_ecS_ne_ecK : ecS ≠ ecK := by decide
@[simp] theorem etc_ecS_ne_ecZ : ecS ≠ ecZ := by decide
@[simp] theorem etc_ecS_ne_lFl : ecS ≠ lFl := by decide
@[simp] theorem etc_lFl_ne_ecS : lFl ≠ ecS := by decide
@[simp] theorem etc_ecS_ne_lDh : ecS ≠ lDh := by decide
@[simp] theorem etc_lDh_ne_ecS : lDh ≠ ecS := by decide
@[simp] theorem etc_ecS_ne_lDt : ecS ≠ lDt := by decide
@[simp] theorem etc_lDt_ne_ecS : lDt ≠ ecS := by decide
@[simp] theorem etc_ecS_ne_lDg : ecS ≠ lDg := by decide
@[simp] theorem etc_lDg_ne_ecS : lDg ≠ ecS := by decide
@[simp] theorem etc_ecS_ne_lDi : ecS ≠ lDi := by decide
@[simp] theorem etc_lDi_ne_ecS : lDi ≠ ecS := by decide
@[simp] theorem etc_ecS_ne_lRp : ecS ≠ lRp := by decide
@[simp] theorem etc_lRp_ne_ecS : lRp ≠ ecS := by decide
@[simp] theorem etc_ecS_ne_lRn : ecS ≠ lRn := by decide
@[simp] theorem etc_lRn_ne_ecS : lRn ≠ ecS := by decide
@[simp] theorem etc_ecS_ne_lFle : ecS ≠ lFle := by decide
@[simp] theorem etc_lFle_ne_ecS : lFle ≠ ecS := by decide
@[simp] theorem etc_ecS_ne_lKb : ecS ≠ lKb := by decide
@[simp] theorem etc_lKb_ne_ecS : lKb ≠ ecS := by decide
@[simp] theorem etc_ecS_ne_lDir : ecS ≠ lDir := by decide
@[simp] theorem etc_lDir_ne_ecS : lDir ≠ ecS := by decide
@[simp] theorem etc_ecS_ne_lFln : ecS ≠ lFln := by decide
@[simp] theorem etc_lFln_ne_ecS : lFln ≠ ecS := by decide
@[simp] theorem etc_ecS_ne_lFll : ecS ≠ lFll := by decide
@[simp] theorem etc_lFll_ne_ecS : lFll ≠ ecS := by decide
@[simp] theorem etc_ecS_ne_lFls : ecS ≠ lFls := by decide
@[simp] theorem etc_lFls_ne_ecS : lFls ≠ ecS := by decide
@[simp] theorem etc_ecS_ne_kFu : ecS ≠ kFu := by decide
@[simp] theorem etc_kFu_ne_ecS : kFu ≠ ecS := by decide
@[simp] theorem etc_ecS_ne_kD : ecS ≠ kD := by decide
@[simp] theorem etc_kD_ne_ecS : kD ≠ ecS := by decide
@[simp] theorem etc_ecN_ne_ecT : ecN ≠ ecT := by decide
@[simp] theorem etc_ecN_ne_ecB : ecN ≠ ecB := by decide
@[simp] theorem etc_ecN_ne_ecS : ecN ≠ ecS := by decide
@[simp] theorem etc_ecN_ne_ecT1 : ecN ≠ ecT1 := by decide
@[simp] theorem etc_ecN_ne_ecH : ecN ≠ ecH := by decide
@[simp] theorem etc_ecN_ne_ecT2 : ecN ≠ ecT2 := by decide
@[simp] theorem etc_ecN_ne_ecC2 : ecN ≠ ecC2 := by decide
@[simp] theorem etc_ecN_ne_ecQ : ecN ≠ ecQ := by decide
@[simp] theorem etc_ecN_ne_ecF : ecN ≠ ecF := by decide
@[simp] theorem etc_ecN_ne_ecL : ecN ≠ ecL := by decide
@[simp] theorem etc_ecN_ne_ecR2 : ecN ≠ ecR2 := by decide
@[simp] theorem etc_ecN_ne_ecD1 : ecN ≠ ecD1 := by decide
@[simp] theorem etc_ecN_ne_ecE : ecN ≠ ecE := by decide
@[simp] theorem etc_ecN_ne_ecI : ecN ≠ ecI := by decide
@[simp] theorem etc_ecN_ne_ecK : ecN ≠ ecK := by decide
@[simp] theorem etc_ecN_ne_ecZ : ecN ≠ ecZ := by decide
@[simp] theorem etc_ecN_ne_lFl : ecN ≠ lFl := by decide
@[simp] theorem etc_lFl_ne_ecN : lFl ≠ ecN := by decide
@[simp] theorem etc_ecN_ne_lDh : ecN ≠ lDh := by decide
@[simp] theorem etc_lDh_ne_ecN : lDh ≠ ecN := by decide
@[simp] theorem etc_ecN_ne_lDt : ecN ≠ lDt := by decide
@[simp] theorem etc_lDt_ne_ecN : lDt ≠ ecN := by decide
@[simp] theorem etc_ecN_ne_lDg : ecN ≠ lDg := by decide
@[simp] theorem etc_lDg_ne_ecN : lDg ≠ ecN := by decide
@[simp] theorem etc_ecN_ne_lDi : ecN ≠ lDi := by decide
@[simp] theorem etc_lDi_ne_ecN : lDi ≠ ecN := by decide
@[simp] theorem etc_ecN_ne_lRp : ecN ≠ lRp := by decide
@[simp] theorem etc_lRp_ne_ecN : lRp ≠ ecN := by decide
@[simp] theorem etc_ecN_ne_lRn : ecN ≠ lRn := by decide
@[simp] theorem etc_lRn_ne_ecN : lRn ≠ ecN := by decide
@[simp] theorem etc_ecN_ne_lFle : ecN ≠ lFle := by decide
@[simp] theorem etc_lFle_ne_ecN : lFle ≠ ecN := by decide
@[simp] theorem etc_ecN_ne_lKb : ecN ≠ lKb := by decide
@[simp] theorem etc_lKb_ne_ecN : lKb ≠ ecN := by decide
@[simp] theorem etc_ecN_ne_lDir : ecN ≠ lDir := by decide
@[simp] theorem etc_lDir_ne_ecN : lDir ≠ ecN := by decide
@[simp] theorem etc_ecN_ne_lFln : ecN ≠ lFln := by decide
@[simp] theorem etc_lFln_ne_ecN : lFln ≠ ecN := by decide
@[simp] theorem etc_ecN_ne_lFll : ecN ≠ lFll := by decide
@[simp] theorem etc_lFll_ne_ecN : lFll ≠ ecN := by decide
@[simp] theorem etc_ecN_ne_lFls : ecN ≠ lFls := by decide
@[simp] theorem etc_lFls_ne_ecN : lFls ≠ ecN := by decide
@[simp] theorem etc_ecN_ne_kFu : ecN ≠ kFu := by decide
@[simp] theorem etc_kFu_ne_ecN : kFu ≠ ecN := by decide
@[simp] theorem etc_ecN_ne_kD : ecN ≠ kD := by decide
@[simp] theorem etc_kD_ne_ecN : kD ≠ ecN := by decide
@[simp] theorem etc_ecT1_ne_ecT : ecT1 ≠ ecT := by decide
@[simp] theorem etc_ecT1_ne_ecB : ecT1 ≠ ecB := by decide
@[simp] theorem etc_ecT1_ne_ecS : ecT1 ≠ ecS := by decide
@[simp] theorem etc_ecT1_ne_ecN : ecT1 ≠ ecN := by decide
@[simp] theorem etc_ecT1_ne_ecH : ecT1 ≠ ecH := by decide
@[simp] theorem etc_ecT1_ne_ecT2 : ecT1 ≠ ecT2 := by decide
@[simp] theorem etc_ecT1_ne_ecC2 : ecT1 ≠ ecC2 := by decide
@[simp] theorem etc_ecT1_ne_ecQ : ecT1 ≠ ecQ := by decide
@[simp] theorem etc_ecT1_ne_ecF : ecT1 ≠ ecF := by decide
@[simp] theorem etc_ecT1_ne_ecL : ecT1 ≠ ecL := by decide
@[simp] theorem etc_ecT1_ne_ecR2 : ecT1 ≠ ecR2 := by decide
@[simp] theorem etc_ecT1_ne_ecD1 : ecT1 ≠ ecD1 := by decide
@[simp] theorem etc_ecT1_ne_ecE : ecT1 ≠ ecE := by decide
@[simp] theorem etc_ecT1_ne_ecI : ecT1 ≠ ecI := by decide
@[simp] theorem etc_ecT1_ne_ecK : ecT1 ≠ ecK := by decide
@[simp] theorem etc_ecT1_ne_ecZ : ecT1 ≠ ecZ := by decide
@[simp] theorem etc_ecT1_ne_lFl : ecT1 ≠ lFl := by decide
@[simp] theorem etc_lFl_ne_ecT1 : lFl ≠ ecT1 := by decide
@[simp] theorem etc_ecT1_ne_lDh : ecT1 ≠ lDh := by decide
@[simp] theorem etc_lDh_ne_ecT1 : lDh ≠ ecT1 := by decide
@[simp] theorem etc_ecT1_ne_lDt : ecT1 ≠ lDt := by decide
@[simp] theorem etc_lDt_ne_ecT1 : lDt ≠ ecT1 := by decide
@[simp] theorem etc_ecT1_ne_lDg : ecT1 ≠ lDg := by decide
@[simp] theorem etc_lDg_ne_ecT1 : lDg ≠ ecT1 := by decide
@[simp] theorem etc_ecT1_ne_lDi : ecT1 ≠ lDi := by decide
@[simp] theorem etc_lDi_ne_ecT1 : lDi ≠ ecT1 := by decide
@[simp] theorem etc_ecT1_ne_lRp : ecT1 ≠ lRp := by decide
@[simp] theorem etc_lRp_ne_ecT1 : lRp ≠ ecT1 := by decide
@[simp] theorem etc_ecT1_ne_lRn : ecT1 ≠ lRn := by decide
@[simp] theorem etc_lRn_ne_ecT1 : lRn ≠ ecT1 := by decide
@[simp] theorem etc_ecT1_ne_lFle : ecT1 ≠ lFle := by decide
@[simp] theorem etc_lFle_ne_ecT1 : lFle ≠ ecT1 := by decide
@[simp] theorem etc_ecT1_ne_lKb : ecT1 ≠ lKb := by decide
@[simp] theorem etc_lKb_ne_ecT1 : lKb ≠ ecT1 := by decide
@[simp] theorem etc_ecT1_ne_lDir : ecT1 ≠ lDir := by decide
@[simp] theorem etc_lDir_ne_ecT1 : lDir ≠ ecT1 := by decide
@[simp] theorem etc_ecT1_ne_lFln : ecT1 ≠ lFln := by decide
@[simp] theorem etc_lFln_ne_ecT1 : lFln ≠ ecT1 := by decide
@[simp] theorem etc_ecT1_ne_lFll : ecT1 ≠ lFll := by decide
@[simp] theorem etc_lFll_ne_ecT1 : lFll ≠ ecT1 := by decide
@[simp] theorem etc_ecT1_ne_lFls : ecT1 ≠ lFls := by decide
@[simp] theorem etc_lFls_ne_ecT1 : lFls ≠ ecT1 := by decide
@[simp] theorem etc_ecT1_ne_kFu : ecT1 ≠ kFu := by decide
@[simp] theorem etc_kFu_ne_ecT1 : kFu ≠ ecT1 := by decide
@[simp] theorem etc_ecT1_ne_kD : ecT1 ≠ kD := by decide
@[simp] theorem etc_kD_ne_ecT1 : kD ≠ ecT1 := by decide
@[simp] theorem etc_ecH_ne_ecT : ecH ≠ ecT := by decide
@[simp] theorem etc_ecH_ne_ecB : ecH ≠ ecB := by decide
@[simp] theorem etc_ecH_ne_ecS : ecH ≠ ecS := by decide
@[simp] theorem etc_ecH_ne_ecN : ecH ≠ ecN := by decide
@[simp] theorem etc_ecH_ne_ecT1 : ecH ≠ ecT1 := by decide
@[simp] theorem etc_ecH_ne_ecT2 : ecH ≠ ecT2 := by decide
@[simp] theorem etc_ecH_ne_ecC2 : ecH ≠ ecC2 := by decide
@[simp] theorem etc_ecH_ne_ecQ : ecH ≠ ecQ := by decide
@[simp] theorem etc_ecH_ne_ecF : ecH ≠ ecF := by decide
@[simp] theorem etc_ecH_ne_ecL : ecH ≠ ecL := by decide
@[simp] theorem etc_ecH_ne_ecR2 : ecH ≠ ecR2 := by decide
@[simp] theorem etc_ecH_ne_ecD1 : ecH ≠ ecD1 := by decide
@[simp] theorem etc_ecH_ne_ecE : ecH ≠ ecE := by decide
@[simp] theorem etc_ecH_ne_ecI : ecH ≠ ecI := by decide
@[simp] theorem etc_ecH_ne_ecK : ecH ≠ ecK := by decide
@[simp] theorem etc_ecH_ne_ecZ : ecH ≠ ecZ := by decide
@[simp] theorem etc_ecH_ne_lFl : ecH ≠ lFl := by decide
@[simp] theorem etc_lFl_ne_ecH : lFl ≠ ecH := by decide
@[simp] theorem etc_ecH_ne_lDh : ecH ≠ lDh := by decide
@[simp] theorem etc_lDh_ne_ecH : lDh ≠ ecH := by decide
@[simp] theorem etc_ecH_ne_lDt : ecH ≠ lDt := by decide
@[simp] theorem etc_lDt_ne_ecH : lDt ≠ ecH := by decide
@[simp] theorem etc_ecH_ne_lDg : ecH ≠ lDg := by decide
@[simp] theorem etc_lDg_ne_ecH : lDg ≠ ecH := by decide
@[simp] theorem etc_ecH_ne_lDi : ecH ≠ lDi := by decide
@[simp] theorem etc_lDi_ne_ecH : lDi ≠ ecH := by decide
@[simp] theorem etc_ecH_ne_lRp : ecH ≠ lRp := by decide
@[simp] theorem etc_lRp_ne_ecH : lRp ≠ ecH := by decide
@[simp] theorem etc_ecH_ne_lRn : ecH ≠ lRn := by decide
@[simp] theorem etc_lRn_ne_ecH : lRn ≠ ecH := by decide
@[simp] theorem etc_ecH_ne_lFle : ecH ≠ lFle := by decide
@[simp] theorem etc_lFle_ne_ecH : lFle ≠ ecH := by decide
@[simp] theorem etc_ecH_ne_lKb : ecH ≠ lKb := by decide
@[simp] theorem etc_lKb_ne_ecH : lKb ≠ ecH := by decide
@[simp] theorem etc_ecH_ne_lDir : ecH ≠ lDir := by decide
@[simp] theorem etc_lDir_ne_ecH : lDir ≠ ecH := by decide
@[simp] theorem etc_ecH_ne_lFln : ecH ≠ lFln := by decide
@[simp] theorem etc_lFln_ne_ecH : lFln ≠ ecH := by decide
@[simp] theorem etc_ecH_ne_lFll : ecH ≠ lFll := by decide
@[simp] theorem etc_lFll_ne_ecH : lFll ≠ ecH := by decide
@[simp] theorem etc_ecH_ne_lFls : ecH ≠ lFls := by decide
@[simp] theorem etc_lFls_ne_ecH : lFls ≠ ecH := by decide
@[simp] theorem etc_ecH_ne_kFu : ecH ≠ kFu := by decide
@[simp] theorem etc_kFu_ne_ecH : kFu ≠ ecH := by decide
@[simp] theorem etc_ecH_ne_kD : ecH ≠ kD := by decide
@[simp] theorem etc_kD_ne_ecH : kD ≠ ecH := by decide
@[simp] theorem etc_ecT2_ne_ecT : ecT2 ≠ ecT := by decide
@[simp] theorem etc_ecT2_ne_ecB : ecT2 ≠ ecB := by decide
@[simp] theorem etc_ecT2_ne_ecS : ecT2 ≠ ecS := by decide
@[simp] theorem etc_ecT2_ne_ecN : ecT2 ≠ ecN := by decide
@[simp] theorem etc_ecT2_ne_ecT1 : ecT2 ≠ ecT1 := by decide
@[simp] theorem etc_ecT2_ne_ecH : ecT2 ≠ ecH := by decide
@[simp] theorem etc_ecT2_ne_ecC2 : ecT2 ≠ ecC2 := by decide
@[simp] theorem etc_ecT2_ne_ecQ : ecT2 ≠ ecQ := by decide
@[simp] theorem etc_ecT2_ne_ecF : ecT2 ≠ ecF := by decide
@[simp] theorem etc_ecT2_ne_ecL : ecT2 ≠ ecL := by decide
@[simp] theorem etc_ecT2_ne_ecR2 : ecT2 ≠ ecR2 := by decide
@[simp] theorem etc_ecT2_ne_ecD1 : ecT2 ≠ ecD1 := by decide
@[simp] theorem etc_ecT2_ne_ecE : ecT2 ≠ ecE := by decide
@[simp] theorem etc_ecT2_ne_ecI : ecT2 ≠ ecI := by decide
@[simp] theorem etc_ecT2_ne_ecK : ecT2 ≠ ecK := by decide
@[simp] theorem etc_ecT2_ne_ecZ : ecT2 ≠ ecZ := by decide
@[simp] theorem etc_ecT2_ne_lFl : ecT2 ≠ lFl := by decide
@[simp] theorem etc_lFl_ne_ecT2 : lFl ≠ ecT2 := by decide
@[simp] theorem etc_ecT2_ne_lDh : ecT2 ≠ lDh := by decide
@[simp] theorem etc_lDh_ne_ecT2 : lDh ≠ ecT2 := by decide
@[simp] theorem etc_ecT2_ne_lDt : ecT2 ≠ lDt := by decide
@[simp] theorem etc_lDt_ne_ecT2 : lDt ≠ ecT2 := by decide
@[simp] theorem etc_ecT2_ne_lDg : ecT2 ≠ lDg := by decide
@[simp] theorem etc_lDg_ne_ecT2 : lDg ≠ ecT2 := by decide
@[simp] theorem etc_ecT2_ne_lDi : ecT2 ≠ lDi := by decide
@[simp] theorem etc_lDi_ne_ecT2 : lDi ≠ ecT2 := by decide
@[simp] theorem etc_ecT2_ne_lRp : ecT2 ≠ lRp := by decide
@[simp] theorem etc_lRp_ne_ecT2 : lRp ≠ ecT2 := by decide
@[simp] theorem etc_ecT2_ne_lRn : ecT2 ≠ lRn := by decide
@[simp] theorem etc_lRn_ne_ecT2 : lRn ≠ ecT2 := by decide
@[simp] theorem etc_ecT2_ne_lFle : ecT2 ≠ lFle := by decide
@[simp] theorem etc_lFle_ne_ecT2 : lFle ≠ ecT2 := by decide
@[simp] theorem etc_ecT2_ne_lKb : ecT2 ≠ lKb := by decide
@[simp] theorem etc_lKb_ne_ecT2 : lKb ≠ ecT2 := by decide
@[simp] theorem etc_ecT2_ne_lDir : ecT2 ≠ lDir := by decide
@[simp] theorem etc_lDir_ne_ecT2 : lDir ≠ ecT2 := by decide
@[simp] theorem etc_ecT2_ne_lFln : ecT2 ≠ lFln := by decide
@[simp] theorem etc_lFln_ne_ecT2 : lFln ≠ ecT2 := by decide
@[simp] theorem etc_ecT2_ne_lFll : ecT2 ≠ lFll := by decide
@[simp] theorem etc_lFll_ne_ecT2 : lFll ≠ ecT2 := by decide
@[simp] theorem etc_ecT2_ne_lFls : ecT2 ≠ lFls := by decide
@[simp] theorem etc_lFls_ne_ecT2 : lFls ≠ ecT2 := by decide
@[simp] theorem etc_ecT2_ne_kFu : ecT2 ≠ kFu := by decide
@[simp] theorem etc_kFu_ne_ecT2 : kFu ≠ ecT2 := by decide
@[simp] theorem etc_ecT2_ne_kD : ecT2 ≠ kD := by decide
@[simp] theorem etc_kD_ne_ecT2 : kD ≠ ecT2 := by decide
@[simp] theorem etc_ecC2_ne_ecT : ecC2 ≠ ecT := by decide
@[simp] theorem etc_ecC2_ne_ecB : ecC2 ≠ ecB := by decide
@[simp] theorem etc_ecC2_ne_ecS : ecC2 ≠ ecS := by decide
@[simp] theorem etc_ecC2_ne_ecN : ecC2 ≠ ecN := by decide
@[simp] theorem etc_ecC2_ne_ecT1 : ecC2 ≠ ecT1 := by decide
@[simp] theorem etc_ecC2_ne_ecH : ecC2 ≠ ecH := by decide
@[simp] theorem etc_ecC2_ne_ecT2 : ecC2 ≠ ecT2 := by decide
@[simp] theorem etc_ecC2_ne_ecQ : ecC2 ≠ ecQ := by decide
@[simp] theorem etc_ecC2_ne_ecF : ecC2 ≠ ecF := by decide
@[simp] theorem etc_ecC2_ne_ecL : ecC2 ≠ ecL := by decide
@[simp] theorem etc_ecC2_ne_ecR2 : ecC2 ≠ ecR2 := by decide
@[simp] theorem etc_ecC2_ne_ecD1 : ecC2 ≠ ecD1 := by decide
@[simp] theorem etc_ecC2_ne_ecE : ecC2 ≠ ecE := by decide
@[simp] theorem etc_ecC2_ne_ecI : ecC2 ≠ ecI := by decide
@[simp] theorem etc_ecC2_ne_ecK : ecC2 ≠ ecK := by decide
@[simp] theorem etc_ecC2_ne_ecZ : ecC2 ≠ ecZ := by decide
@[simp] theorem etc_ecC2_ne_lFl : ecC2 ≠ lFl := by decide
@[simp] theorem etc_lFl_ne_ecC2 : lFl ≠ ecC2 := by decide
@[simp] theorem etc_ecC2_ne_lDh : ecC2 ≠ lDh := by decide
@[simp] theorem etc_lDh_ne_ecC2 : lDh ≠ ecC2 := by decide
@[simp] theorem etc_ecC2_ne_lDt : ecC2 ≠ lDt := by decide
@[simp] theorem etc_lDt_ne_ecC2 : lDt ≠ ecC2 := by decide
@[simp] theorem etc_ecC2_ne_lDg : ecC2 ≠ lDg := by decide
@[simp] theorem etc_lDg_ne_ecC2 : lDg ≠ ecC2 := by decide
@[simp] theorem etc_ecC2_ne_lDi : ecC2 ≠ lDi := by decide
@[simp] theorem etc_lDi_ne_ecC2 : lDi ≠ ecC2 := by decide
@[simp] theorem etc_ecC2_ne_lRp : ecC2 ≠ lRp := by decide
@[simp] theorem etc_lRp_ne_ecC2 : lRp ≠ ecC2 := by decide
@[simp] theorem etc_ecC2_ne_lRn : ecC2 ≠ lRn := by decide
@[simp] theorem etc_lRn_ne_ecC2 : lRn ≠ ecC2 := by decide
@[simp] theorem etc_ecC2_ne_lFle : ecC2 ≠ lFle := by decide
@[simp] theorem etc_lFle_ne_ecC2 : lFle ≠ ecC2 := by decide
@[simp] theorem etc_ecC2_ne_lKb : ecC2 ≠ lKb := by decide
@[simp] theorem etc_lKb_ne_ecC2 : lKb ≠ ecC2 := by decide
@[simp] theorem etc_ecC2_ne_lDir : ecC2 ≠ lDir := by decide
@[simp] theorem etc_lDir_ne_ecC2 : lDir ≠ ecC2 := by decide
@[simp] theorem etc_ecC2_ne_lFln : ecC2 ≠ lFln := by decide
@[simp] theorem etc_lFln_ne_ecC2 : lFln ≠ ecC2 := by decide
@[simp] theorem etc_ecC2_ne_lFll : ecC2 ≠ lFll := by decide
@[simp] theorem etc_lFll_ne_ecC2 : lFll ≠ ecC2 := by decide
@[simp] theorem etc_ecC2_ne_lFls : ecC2 ≠ lFls := by decide
@[simp] theorem etc_lFls_ne_ecC2 : lFls ≠ ecC2 := by decide
@[simp] theorem etc_ecC2_ne_kFu : ecC2 ≠ kFu := by decide
@[simp] theorem etc_kFu_ne_ecC2 : kFu ≠ ecC2 := by decide
@[simp] theorem etc_ecC2_ne_kD : ecC2 ≠ kD := by decide
@[simp] theorem etc_kD_ne_ecC2 : kD ≠ ecC2 := by decide
@[simp] theorem etc_ecQ_ne_ecT : ecQ ≠ ecT := by decide
@[simp] theorem etc_ecQ_ne_ecB : ecQ ≠ ecB := by decide
@[simp] theorem etc_ecQ_ne_ecS : ecQ ≠ ecS := by decide
@[simp] theorem etc_ecQ_ne_ecN : ecQ ≠ ecN := by decide
@[simp] theorem etc_ecQ_ne_ecT1 : ecQ ≠ ecT1 := by decide
@[simp] theorem etc_ecQ_ne_ecH : ecQ ≠ ecH := by decide
@[simp] theorem etc_ecQ_ne_ecT2 : ecQ ≠ ecT2 := by decide
@[simp] theorem etc_ecQ_ne_ecC2 : ecQ ≠ ecC2 := by decide
@[simp] theorem etc_ecQ_ne_ecF : ecQ ≠ ecF := by decide
@[simp] theorem etc_ecQ_ne_ecL : ecQ ≠ ecL := by decide
@[simp] theorem etc_ecQ_ne_ecR2 : ecQ ≠ ecR2 := by decide
@[simp] theorem etc_ecQ_ne_ecD1 : ecQ ≠ ecD1 := by decide
@[simp] theorem etc_ecQ_ne_ecE : ecQ ≠ ecE := by decide
@[simp] theorem etc_ecQ_ne_ecI : ecQ ≠ ecI := by decide
@[simp] theorem etc_ecQ_ne_ecK : ecQ ≠ ecK := by decide
@[simp] theorem etc_ecQ_ne_ecZ : ecQ ≠ ecZ := by decide
@[simp] theorem etc_ecQ_ne_lFl : ecQ ≠ lFl := by decide
@[simp] theorem etc_lFl_ne_ecQ : lFl ≠ ecQ := by decide
@[simp] theorem etc_ecQ_ne_lDh : ecQ ≠ lDh := by decide
@[simp] theorem etc_lDh_ne_ecQ : lDh ≠ ecQ := by decide
@[simp] theorem etc_ecQ_ne_lDt : ecQ ≠ lDt := by decide
@[simp] theorem etc_lDt_ne_ecQ : lDt ≠ ecQ := by decide
@[simp] theorem etc_ecQ_ne_lDg : ecQ ≠ lDg := by decide
@[simp] theorem etc_lDg_ne_ecQ : lDg ≠ ecQ := by decide
@[simp] theorem etc_ecQ_ne_lDi : ecQ ≠ lDi := by decide
@[simp] theorem etc_lDi_ne_ecQ : lDi ≠ ecQ := by decide
@[simp] theorem etc_ecQ_ne_lRp : ecQ ≠ lRp := by decide
@[simp] theorem etc_lRp_ne_ecQ : lRp ≠ ecQ := by decide
@[simp] theorem etc_ecQ_ne_lRn : ecQ ≠ lRn := by decide
@[simp] theorem etc_lRn_ne_ecQ : lRn ≠ ecQ := by decide
@[simp] theorem etc_ecQ_ne_lFle : ecQ ≠ lFle := by decide
@[simp] theorem etc_lFle_ne_ecQ : lFle ≠ ecQ := by decide
@[simp] theorem etc_ecQ_ne_lKb : ecQ ≠ lKb := by decide
@[simp] theorem etc_lKb_ne_ecQ : lKb ≠ ecQ := by decide
@[simp] theorem etc_ecQ_ne_lDir : ecQ ≠ lDir := by decide
@[simp] theorem etc_lDir_ne_ecQ : lDir ≠ ecQ := by decide
@[simp] theorem etc_ecQ_ne_lFln : ecQ ≠ lFln := by decide
@[simp] theorem etc_lFln_ne_ecQ : lFln ≠ ecQ := by decide
@[simp] theorem etc_ecQ_ne_lFll : ecQ ≠ lFll := by decide
@[simp] theorem etc_lFll_ne_ecQ : lFll ≠ ecQ := by decide
@[simp] theorem etc_ecQ_ne_lFls : ecQ ≠ lFls := by decide
@[simp] theorem etc_lFls_ne_ecQ : lFls ≠ ecQ := by decide
@[simp] theorem etc_ecQ_ne_kFu : ecQ ≠ kFu := by decide
@[simp] theorem etc_kFu_ne_ecQ : kFu ≠ ecQ := by decide
@[simp] theorem etc_ecQ_ne_kD : ecQ ≠ kD := by decide
@[simp] theorem etc_kD_ne_ecQ : kD ≠ ecQ := by decide
@[simp] theorem etc_ecF_ne_ecT : ecF ≠ ecT := by decide
@[simp] theorem etc_ecF_ne_ecB : ecF ≠ ecB := by decide
@[simp] theorem etc_ecF_ne_ecS : ecF ≠ ecS := by decide
@[simp] theorem etc_ecF_ne_ecN : ecF ≠ ecN := by decide
@[simp] theorem etc_ecF_ne_ecT1 : ecF ≠ ecT1 := by decide
@[simp] theorem etc_ecF_ne_ecH : ecF ≠ ecH := by decide
@[simp] theorem etc_ecF_ne_ecT2 : ecF ≠ ecT2 := by decide
@[simp] theorem etc_ecF_ne_ecC2 : ecF ≠ ecC2 := by decide
@[simp] theorem etc_ecF_ne_ecQ : ecF ≠ ecQ := by decide
@[simp] theorem etc_ecF_ne_ecL : ecF ≠ ecL := by decide
@[simp] theorem etc_ecF_ne_ecR2 : ecF ≠ ecR2 := by decide
@[simp] theorem etc_ecF_ne_ecD1 : ecF ≠ ecD1 := by decide
@[simp] theorem etc_ecF_ne_ecE : ecF ≠ ecE := by decide
@[simp] theorem etc_ecF_ne_ecI : ecF ≠ ecI := by decide
@[simp] theorem etc_ecF_ne_ecK : ecF ≠ ecK := by decide
@[simp] theorem etc_ecF_ne_ecZ : ecF ≠ ecZ := by decide
@[simp] theorem etc_ecF_ne_lFl : ecF ≠ lFl := by decide
@[simp] theorem etc_lFl_ne_ecF : lFl ≠ ecF := by decide
@[simp] theorem etc_ecF_ne_lDh : ecF ≠ lDh := by decide
@[simp] theorem etc_lDh_ne_ecF : lDh ≠ ecF := by decide
@[simp] theorem etc_ecF_ne_lDt : ecF ≠ lDt := by decide
@[simp] theorem etc_lDt_ne_ecF : lDt ≠ ecF := by decide
@[simp] theorem etc_ecF_ne_lDg : ecF ≠ lDg := by decide
@[simp] theorem etc_lDg_ne_ecF : lDg ≠ ecF := by decide
@[simp] theorem etc_ecF_ne_lDi : ecF ≠ lDi := by decide
@[simp] theorem etc_lDi_ne_ecF : lDi ≠ ecF := by decide
@[simp] theorem etc_ecF_ne_lRp : ecF ≠ lRp := by decide
@[simp] theorem etc_lRp_ne_ecF : lRp ≠ ecF := by decide
@[simp] theorem etc_ecF_ne_lRn : ecF ≠ lRn := by decide
@[simp] theorem etc_lRn_ne_ecF : lRn ≠ ecF := by decide
@[simp] theorem etc_ecF_ne_lFle : ecF ≠ lFle := by decide
@[simp] theorem etc_lFle_ne_ecF : lFle ≠ ecF := by decide
@[simp] theorem etc_ecF_ne_lKb : ecF ≠ lKb := by decide
@[simp] theorem etc_lKb_ne_ecF : lKb ≠ ecF := by decide
@[simp] theorem etc_ecF_ne_lDir : ecF ≠ lDir := by decide
@[simp] theorem etc_lDir_ne_ecF : lDir ≠ ecF := by decide
@[simp] theorem etc_ecF_ne_lFln : ecF ≠ lFln := by decide
@[simp] theorem etc_lFln_ne_ecF : lFln ≠ ecF := by decide
@[simp] theorem etc_ecF_ne_lFll : ecF ≠ lFll := by decide
@[simp] theorem etc_lFll_ne_ecF : lFll ≠ ecF := by decide
@[simp] theorem etc_ecF_ne_lFls : ecF ≠ lFls := by decide
@[simp] theorem etc_lFls_ne_ecF : lFls ≠ ecF := by decide
@[simp] theorem etc_ecF_ne_kFu : ecF ≠ kFu := by decide
@[simp] theorem etc_kFu_ne_ecF : kFu ≠ ecF := by decide
@[simp] theorem etc_ecF_ne_kD : ecF ≠ kD := by decide
@[simp] theorem etc_kD_ne_ecF : kD ≠ ecF := by decide
@[simp] theorem etc_ecL_ne_ecT : ecL ≠ ecT := by decide
@[simp] theorem etc_ecL_ne_ecB : ecL ≠ ecB := by decide
@[simp] theorem etc_ecL_ne_ecS : ecL ≠ ecS := by decide
@[simp] theorem etc_ecL_ne_ecN : ecL ≠ ecN := by decide
@[simp] theorem etc_ecL_ne_ecT1 : ecL ≠ ecT1 := by decide
@[simp] theorem etc_ecL_ne_ecH : ecL ≠ ecH := by decide
@[simp] theorem etc_ecL_ne_ecT2 : ecL ≠ ecT2 := by decide
@[simp] theorem etc_ecL_ne_ecC2 : ecL ≠ ecC2 := by decide
@[simp] theorem etc_ecL_ne_ecQ : ecL ≠ ecQ := by decide
@[simp] theorem etc_ecL_ne_ecF : ecL ≠ ecF := by decide
@[simp] theorem etc_ecL_ne_ecR2 : ecL ≠ ecR2 := by decide
@[simp] theorem etc_ecL_ne_ecD1 : ecL ≠ ecD1 := by decide
@[simp] theorem etc_ecL_ne_ecE : ecL ≠ ecE := by decide
@[simp] theorem etc_ecL_ne_ecI : ecL ≠ ecI := by decide
@[simp] theorem etc_ecL_ne_ecK : ecL ≠ ecK := by decide
@[simp] theorem etc_ecL_ne_ecZ : ecL ≠ ecZ := by decide
@[simp] theorem etc_ecL_ne_lFl : ecL ≠ lFl := by decide
@[simp] theorem etc_lFl_ne_ecL : lFl ≠ ecL := by decide
@[simp] theorem etc_ecL_ne_lDh : ecL ≠ lDh := by decide
@[simp] theorem etc_lDh_ne_ecL : lDh ≠ ecL := by decide
@[simp] theorem etc_ecL_ne_lDt : ecL ≠ lDt := by decide
@[simp] theorem etc_lDt_ne_ecL : lDt ≠ ecL := by decide
@[simp] theorem etc_ecL_ne_lDg : ecL ≠ lDg := by decide
@[simp] theorem etc_lDg_ne_ecL : lDg ≠ ecL := by decide
@[simp] theorem etc_ecL_ne_lDi : ecL ≠ lDi := by decide
@[simp] theorem etc_lDi_ne_ecL : lDi ≠ ecL := by decide
@[simp] theorem etc_ecL_ne_lRp : ecL ≠ lRp := by decide
@[simp] theorem etc_lRp_ne_ecL : lRp ≠ ecL := by decide
@[simp] theorem etc_ecL_ne_lRn : ecL ≠ lRn := by decide
@[simp] theorem etc_lRn_ne_ecL : lRn ≠ ecL := by decide
@[simp] theorem etc_ecL_ne_lFle : ecL ≠ lFle := by decide
@[simp] theorem etc_lFle_ne_ecL : lFle ≠ ecL := by decide
@[simp] theorem etc_ecL_ne_lKb : ecL ≠ lKb := by decide
@[simp] theorem etc_lKb_ne_ecL : lKb ≠ ecL := by decide
@[simp] theorem etc_ecL_ne_lDir : ecL ≠ lDir := by decide
@[simp] theorem etc_lDir_ne_ecL : lDir ≠ ecL := by decide
@[simp] theorem etc_ecL_ne_lFln : ecL ≠ lFln := by decide
@[simp] theorem etc_lFln_ne_ecL : lFln ≠ ecL := by decide
@[simp] theorem etc_ecL_ne_lFll : ecL ≠ lFll := by decide
@[simp] theorem etc_lFll_ne_ecL : lFll ≠ ecL := by decide
@[simp] theorem etc_ecL_ne_lFls : ecL ≠ lFls := by decide
@[simp] theorem etc_lFls_ne_ecL : lFls ≠ ecL := by decide
@[simp] theorem etc_ecL_ne_kFu : ecL ≠ kFu := by decide
@[simp] theorem etc_kFu_ne_ecL : kFu ≠ ecL := by decide
@[simp] theorem etc_ecL_ne_kD : ecL ≠ kD := by decide
@[simp] theorem etc_kD_ne_ecL : kD ≠ ecL := by decide
@[simp] theorem etc_ecR2_ne_ecT : ecR2 ≠ ecT := by decide
@[simp] theorem etc_ecR2_ne_ecB : ecR2 ≠ ecB := by decide
@[simp] theorem etc_ecR2_ne_ecS : ecR2 ≠ ecS := by decide
@[simp] theorem etc_ecR2_ne_ecN : ecR2 ≠ ecN := by decide
@[simp] theorem etc_ecR2_ne_ecT1 : ecR2 ≠ ecT1 := by decide
@[simp] theorem etc_ecR2_ne_ecH : ecR2 ≠ ecH := by decide
@[simp] theorem etc_ecR2_ne_ecT2 : ecR2 ≠ ecT2 := by decide
@[simp] theorem etc_ecR2_ne_ecC2 : ecR2 ≠ ecC2 := by decide
@[simp] theorem etc_ecR2_ne_ecQ : ecR2 ≠ ecQ := by decide
@[simp] theorem etc_ecR2_ne_ecF : ecR2 ≠ ecF := by decide
@[simp] theorem etc_ecR2_ne_ecL : ecR2 ≠ ecL := by decide
@[simp] theorem etc_ecR2_ne_ecD1 : ecR2 ≠ ecD1 := by decide
@[simp] theorem etc_ecR2_ne_ecE : ecR2 ≠ ecE := by decide
@[simp] theorem etc_ecR2_ne_ecI : ecR2 ≠ ecI := by decide
@[simp] theorem etc_ecR2_ne_ecK : ecR2 ≠ ecK := by decide
@[simp] theorem etc_ecR2_ne_ecZ : ecR2 ≠ ecZ := by decide
@[simp] theorem etc_ecR2_ne_lFl : ecR2 ≠ lFl := by decide
@[simp] theorem etc_lFl_ne_ecR2 : lFl ≠ ecR2 := by decide
@[simp] theorem etc_ecR2_ne_lDh : ecR2 ≠ lDh := by decide
@[simp] theorem etc_lDh_ne_ecR2 : lDh ≠ ecR2 := by decide
@[simp] theorem etc_ecR2_ne_lDt : ecR2 ≠ lDt := by decide
@[simp] theorem etc_lDt_ne_ecR2 : lDt ≠ ecR2 := by decide
@[simp] theorem etc_ecR2_ne_lDg : ecR2 ≠ lDg := by decide
@[simp] theorem etc_lDg_ne_ecR2 : lDg ≠ ecR2 := by decide
@[simp] theorem etc_ecR2_ne_lDi : ecR2 ≠ lDi := by decide
@[simp] theorem etc_lDi_ne_ecR2 : lDi ≠ ecR2 := by decide
@[simp] theorem etc_ecR2_ne_lRp : ecR2 ≠ lRp := by decide
@[simp] theorem etc_lRp_ne_ecR2 : lRp ≠ ecR2 := by decide
@[simp] theorem etc_ecR2_ne_lRn : ecR2 ≠ lRn := by decide
@[simp] theorem etc_lRn_ne_ecR2 : lRn ≠ ecR2 := by decide
@[simp] theorem etc_ecR2_ne_lFle : ecR2 ≠ lFle := by decide
@[simp] theorem etc_lFle_ne_ecR2 : lFle ≠ ecR2 := by decide
@[simp] theorem etc_ecR2_ne_lKb : ecR2 ≠ lKb := by decide
@[simp] theorem etc_lKb_ne_ecR2 : lKb ≠ ecR2 := by decide
@[simp] theorem etc_ecR2_ne_lDir : ecR2 ≠ lDir := by decide
@[simp] theorem etc_lDir_ne_ecR2 : lDir ≠ ecR2 := by decide
@[simp] theorem etc_ecR2_ne_lFln : ecR2 ≠ lFln := by decide
@[simp] theorem etc_lFln_ne_ecR2 : lFln ≠ ecR2 := by decide
@[simp] theorem etc_ecR2_ne_lFll : ecR2 ≠ lFll := by decide
@[simp] theorem etc_lFll_ne_ecR2 : lFll ≠ ecR2 := by decide
@[simp] theorem etc_ecR2_ne_lFls : ecR2 ≠ lFls := by decide
@[simp] theorem etc_lFls_ne_ecR2 : lFls ≠ ecR2 := by decide
@[simp] theorem etc_ecR2_ne_kFu : ecR2 ≠ kFu := by decide
@[simp] theorem etc_kFu_ne_ecR2 : kFu ≠ ecR2 := by decide
@[simp] theorem etc_ecR2_ne_kD : ecR2 ≠ kD := by decide
@[simp] theorem etc_kD_ne_ecR2 : kD ≠ ecR2 := by decide
@[simp] theorem etc_ecD1_ne_ecT : ecD1 ≠ ecT := by decide
@[simp] theorem etc_ecD1_ne_ecB : ecD1 ≠ ecB := by decide
@[simp] theorem etc_ecD1_ne_ecS : ecD1 ≠ ecS := by decide
@[simp] theorem etc_ecD1_ne_ecN : ecD1 ≠ ecN := by decide
@[simp] theorem etc_ecD1_ne_ecT1 : ecD1 ≠ ecT1 := by decide
@[simp] theorem etc_ecD1_ne_ecH : ecD1 ≠ ecH := by decide
@[simp] theorem etc_ecD1_ne_ecT2 : ecD1 ≠ ecT2 := by decide
@[simp] theorem etc_ecD1_ne_ecC2 : ecD1 ≠ ecC2 := by decide
@[simp] theorem etc_ecD1_ne_ecQ : ecD1 ≠ ecQ := by decide
@[simp] theorem etc_ecD1_ne_ecF : ecD1 ≠ ecF := by decide
@[simp] theorem etc_ecD1_ne_ecL : ecD1 ≠ ecL := by decide
@[simp] theorem etc_ecD1_ne_ecR2 : ecD1 ≠ ecR2 := by decide
@[simp] theorem etc_ecD1_ne_ecE : ecD1 ≠ ecE := by decide
@[simp] theorem etc_ecD1_ne_ecI : ecD1 ≠ ecI := by decide
@[simp] theorem etc_ecD1_ne_ecK : ecD1 ≠ ecK := by decide
@[simp] theorem etc_ecD1_ne_ecZ : ecD1 ≠ ecZ := by decide
@[simp] theorem etc_ecD1_ne_lFl : ecD1 ≠ lFl := by decide
@[simp] theorem etc_lFl_ne_ecD1 : lFl ≠ ecD1 := by decide
@[simp] theorem etc_ecD1_ne_lDh : ecD1 ≠ lDh := by decide
@[simp] theorem etc_lDh_ne_ecD1 : lDh ≠ ecD1 := by decide
@[simp] theorem etc_ecD1_ne_lDt : ecD1 ≠ lDt := by decide
@[simp] theorem etc_lDt_ne_ecD1 : lDt ≠ ecD1 := by decide
@[simp] theorem etc_ecD1_ne_lDg : ecD1 ≠ lDg := by decide
@[simp] theorem etc_lDg_ne_ecD1 : lDg ≠ ecD1 := by decide
@[simp] theorem etc_ecD1_ne_lDi : ecD1 ≠ lDi := by decide
@[simp] theorem etc_lDi_ne_ecD1 : lDi ≠ ecD1 := by decide
@[simp] theorem etc_ecD1_ne_lRp : ecD1 ≠ lRp := by decide
@[simp] theorem etc_lRp_ne_ecD1 : lRp ≠ ecD1 := by decide
@[simp] theorem etc_ecD1_ne_lRn : ecD1 ≠ lRn := by decide
@[simp] theorem etc_lRn_ne_ecD1 : lRn ≠ ecD1 := by decide
@[simp] theorem etc_ecD1_ne_lFle : ecD1 ≠ lFle := by decide
@[simp] theorem etc_lFle_ne_ecD1 : lFle ≠ ecD1 := by decide
@[simp] theorem etc_ecD1_ne_lKb : ecD1 ≠ lKb := by decide
@[simp] theorem etc_lKb_ne_ecD1 : lKb ≠ ecD1 := by decide
@[simp] theorem etc_ecD1_ne_lDir : ecD1 ≠ lDir := by decide
@[simp] theorem etc_lDir_ne_ecD1 : lDir ≠ ecD1 := by decide
@[simp] theorem etc_ecD1_ne_lFln : ecD1 ≠ lFln := by decide
@[simp] theorem etc_lFln_ne_ecD1 : lFln ≠ ecD1 := by decide
@[simp] theorem etc_ecD1_ne_lFll : ecD1 ≠ lFll := by decide
@[simp] theorem etc_lFll_ne_ecD1 : lFll ≠ ecD1 := by decide
@[simp] theorem etc_ecD1_ne_lFls : ecD1 ≠ lFls := by decide
@[simp] theorem etc_lFls_ne_ecD1 : lFls ≠ ecD1 := by decide
@[simp] theorem etc_ecD1_ne_kFu : ecD1 ≠ kFu := by decide
@[simp] theorem etc_kFu_ne_ecD1 : kFu ≠ ecD1 := by decide
@[simp] theorem etc_ecD1_ne_kD : ecD1 ≠ kD := by decide
@[simp] theorem etc_kD_ne_ecD1 : kD ≠ ecD1 := by decide
@[simp] theorem etc_ecE_ne_ecT : ecE ≠ ecT := by decide
@[simp] theorem etc_ecE_ne_ecB : ecE ≠ ecB := by decide
@[simp] theorem etc_ecE_ne_ecS : ecE ≠ ecS := by decide
@[simp] theorem etc_ecE_ne_ecN : ecE ≠ ecN := by decide
@[simp] theorem etc_ecE_ne_ecT1 : ecE ≠ ecT1 := by decide
@[simp] theorem etc_ecE_ne_ecH : ecE ≠ ecH := by decide
@[simp] theorem etc_ecE_ne_ecT2 : ecE ≠ ecT2 := by decide
@[simp] theorem etc_ecE_ne_ecC2 : ecE ≠ ecC2 := by decide
@[simp] theorem etc_ecE_ne_ecQ : ecE ≠ ecQ := by decide
@[simp] theorem etc_ecE_ne_ecF : ecE ≠ ecF := by decide
@[simp] theorem etc_ecE_ne_ecL : ecE ≠ ecL := by decide
@[simp] theorem etc_ecE_ne_ecR2 : ecE ≠ ecR2 := by decide
@[simp] theorem etc_ecE_ne_ecD1 : ecE ≠ ecD1 := by decide
@[simp] theorem etc_ecE_ne_ecI : ecE ≠ ecI := by decide
@[simp] theorem etc_ecE_ne_ecK : ecE ≠ ecK := by decide
@[simp] theorem etc_ecE_ne_ecZ : ecE ≠ ecZ := by decide
@[simp] theorem etc_ecE_ne_lFl : ecE ≠ lFl := by decide
@[simp] theorem etc_lFl_ne_ecE : lFl ≠ ecE := by decide
@[simp] theorem etc_ecE_ne_lDh : ecE ≠ lDh := by decide
@[simp] theorem etc_lDh_ne_ecE : lDh ≠ ecE := by decide
@[simp] theorem etc_ecE_ne_lDt : ecE ≠ lDt := by decide
@[simp] theorem etc_lDt_ne_ecE : lDt ≠ ecE := by decide
@[simp] theorem etc_ecE_ne_lDg : ecE ≠ lDg := by decide
@[simp] theorem etc_lDg_ne_ecE : lDg ≠ ecE := by decide
@[simp] theorem etc_ecE_ne_lDi : ecE ≠ lDi := by decide
@[simp] theorem etc_lDi_ne_ecE : lDi ≠ ecE := by decide
@[simp] theorem etc_ecE_ne_lRp : ecE ≠ lRp := by decide
@[simp] theorem etc_lRp_ne_ecE : lRp ≠ ecE := by decide
@[simp] theorem etc_ecE_ne_lRn : ecE ≠ lRn := by decide
@[simp] theorem etc_lRn_ne_ecE : lRn ≠ ecE := by decide
@[simp] theorem etc_ecE_ne_lFle : ecE ≠ lFle := by decide
@[simp] theorem etc_lFle_ne_ecE : lFle ≠ ecE := by decide
@[simp] theorem etc_ecE_ne_lKb : ecE ≠ lKb := by decide
@[simp] theorem etc_lKb_ne_ecE : lKb ≠ ecE := by decide
@[simp] theorem etc_ecE_ne_lDir : ecE ≠ lDir := by decide
@[simp] theorem etc_lDir_ne_ecE : lDir ≠ ecE := by decide
@[simp] theorem etc_ecE_ne_lFln : ecE ≠ lFln := by decide
@[simp] theorem etc_lFln_ne_ecE : lFln ≠ ecE := by decide
@[simp] theorem etc_ecE_ne_lFll : ecE ≠ lFll := by decide
@[simp] theorem etc_lFll_ne_ecE : lFll ≠ ecE := by decide
@[simp] theorem etc_ecE_ne_lFls : ecE ≠ lFls := by decide
@[simp] theorem etc_lFls_ne_ecE : lFls ≠ ecE := by decide
@[simp] theorem etc_ecE_ne_kFu : ecE ≠ kFu := by decide
@[simp] theorem etc_kFu_ne_ecE : kFu ≠ ecE := by decide
@[simp] theorem etc_ecE_ne_kD : ecE ≠ kD := by decide
@[simp] theorem etc_kD_ne_ecE : kD ≠ ecE := by decide
@[simp] theorem etc_ecI_ne_ecT : ecI ≠ ecT := by decide
@[simp] theorem etc_ecI_ne_ecB : ecI ≠ ecB := by decide
@[simp] theorem etc_ecI_ne_ecS : ecI ≠ ecS := by decide
@[simp] theorem etc_ecI_ne_ecN : ecI ≠ ecN := by decide
@[simp] theorem etc_ecI_ne_ecT1 : ecI ≠ ecT1 := by decide
@[simp] theorem etc_ecI_ne_ecH : ecI ≠ ecH := by decide
@[simp] theorem etc_ecI_ne_ecT2 : ecI ≠ ecT2 := by decide
@[simp] theorem etc_ecI_ne_ecC2 : ecI ≠ ecC2 := by decide
@[simp] theorem etc_ecI_ne_ecQ : ecI ≠ ecQ := by decide
@[simp] theorem etc_ecI_ne_ecF : ecI ≠ ecF := by decide
@[simp] theorem etc_ecI_ne_ecL : ecI ≠ ecL := by decide
@[simp] theorem etc_ecI_ne_ecR2 : ecI ≠ ecR2 := by decide
@[simp] theorem etc_ecI_ne_ecD1 : ecI ≠ ecD1 := by decide
@[simp] theorem etc_ecI_ne_ecE : ecI ≠ ecE := by decide
@[simp] theorem etc_ecI_ne_ecK : ecI ≠ ecK := by decide
@[simp] theorem etc_ecI_ne_ecZ : ecI ≠ ecZ := by decide
@[simp] theorem etc_ecI_ne_lFl : ecI ≠ lFl := by decide
@[simp] theorem etc_lFl_ne_ecI : lFl ≠ ecI := by decide
@[simp] theorem etc_ecI_ne_lDh : ecI ≠ lDh := by decide
@[simp] theorem etc_lDh_ne_ecI : lDh ≠ ecI := by decide
@[simp] theorem etc_ecI_ne_lDt : ecI ≠ lDt := by decide
@[simp] theorem etc_lDt_ne_ecI : lDt ≠ ecI := by decide
@[simp] theorem etc_ecI_ne_lDg : ecI ≠ lDg := by decide
@[simp] theorem etc_lDg_ne_ecI : lDg ≠ ecI := by decide
@[simp] theorem etc_ecI_ne_lDi : ecI ≠ lDi := by decide
@[simp] theorem etc_lDi_ne_ecI : lDi ≠ ecI := by decide
@[simp] theorem etc_ecI_ne_lRp : ecI ≠ lRp := by decide
@[simp] theorem etc_lRp_ne_ecI : lRp ≠ ecI := by decide
@[simp] theorem etc_ecI_ne_lRn : ecI ≠ lRn := by decide
@[simp] theorem etc_lRn_ne_ecI : lRn ≠ ecI := by decide
@[simp] theorem etc_ecI_ne_lFle : ecI ≠ lFle := by decide
@[simp] theorem etc_lFle_ne_ecI : lFle ≠ ecI := by decide
@[simp] theorem etc_ecI_ne_lKb : ecI ≠ lKb := by decide
@[simp] theorem etc_lKb_ne_ecI : lKb ≠ ecI := by decide
@[simp] theorem etc_ecI_ne_lDir : ecI ≠ lDir := by decide
@[simp] theorem etc_lDir_ne_ecI : lDir ≠ ecI := by decide
@[simp] theorem etc_ecI_ne_lFln : ecI ≠ lFln := by decide
@[simp] theorem etc_lFln_ne_ecI : lFln ≠ ecI := by decide
@[simp] theorem etc_ecI_ne_lFll : ecI ≠ lFll := by decide
@[simp] theorem etc_lFll_ne_ecI : lFll ≠ ecI := by decide
@[simp] theorem etc_ecI_ne_lFls : ecI ≠ lFls := by decide
@[simp] theorem etc_lFls_ne_ecI : lFls ≠ ecI := by decide
@[simp] theorem etc_ecI_ne_kFu : ecI ≠ kFu := by decide
@[simp] theorem etc_kFu_ne_ecI : kFu ≠ ecI := by decide
@[simp] theorem etc_ecI_ne_kD : ecI ≠ kD := by decide
@[simp] theorem etc_kD_ne_ecI : kD ≠ ecI := by decide
@[simp] theorem etc_ecK_ne_ecT : ecK ≠ ecT := by decide
@[simp] theorem etc_ecK_ne_ecB : ecK ≠ ecB := by decide
@[simp] theorem etc_ecK_ne_ecS : ecK ≠ ecS := by decide
@[simp] theorem etc_ecK_ne_ecN : ecK ≠ ecN := by decide
@[simp] theorem etc_ecK_ne_ecT1 : ecK ≠ ecT1 := by decide
@[simp] theorem etc_ecK_ne_ecH : ecK ≠ ecH := by decide
@[simp] theorem etc_ecK_ne_ecT2 : ecK ≠ ecT2 := by decide
@[simp] theorem etc_ecK_ne_ecC2 : ecK ≠ ecC2 := by decide
@[simp] theorem etc_ecK_ne_ecQ : ecK ≠ ecQ := by decide
@[simp] theorem etc_ecK_ne_ecF : ecK ≠ ecF := by decide
@[simp] theorem etc_ecK_ne_ecL : ecK ≠ ecL := by decide
@[simp] theorem etc_ecK_ne_ecR2 : ecK ≠ ecR2 := by decide
@[simp] theorem etc_ecK_ne_ecD1 : ecK ≠ ecD1 := by decide
@[simp] theorem etc_ecK_ne_ecE : ecK ≠ ecE := by decide
@[simp] theorem etc_ecK_ne_ecI : ecK ≠ ecI := by decide
@[simp] theorem etc_ecK_ne_ecZ : ecK ≠ ecZ := by decide
@[simp] theorem etc_ecK_ne_lFl : ecK ≠ lFl := by decide
@[simp] theorem etc_lFl_ne_ecK : lFl ≠ ecK := by decide
@[simp] theorem etc_ecK_ne_lDh : ecK ≠ lDh := by decide
@[simp] theorem etc_lDh_ne_ecK : lDh ≠ ecK := by decide
@[simp] theorem etc_ecK_ne_lDt : ecK ≠ lDt := by decide
@[simp] theorem etc_lDt_ne_ecK : lDt ≠ ecK := by decide
@[simp] theorem etc_ecK_ne_lDg : ecK ≠ lDg := by decide
@[simp] theorem etc_lDg_ne_ecK : lDg ≠ ecK := by decide
@[simp] theorem etc_ecK_ne_lDi : ecK ≠ lDi := by decide
@[simp] theorem etc_lDi_ne_ecK : lDi ≠ ecK := by decide
@[simp] theorem etc_ecK_ne_lRp : ecK ≠ lRp := by decide
@[simp] theorem etc_lRp_ne_ecK : lRp ≠ ecK := by decide
@[simp] theorem etc_ecK_ne_lRn : ecK ≠ lRn := by decide
@[simp] theorem etc_lRn_ne_ecK : lRn ≠ ecK := by decide
@[simp] theorem etc_ecK_ne_lFle : ecK ≠ lFle := by decide
@[simp] theorem etc_lFle_ne_ecK : lFle ≠ ecK := by decide
@[simp] theorem etc_ecK_ne_lKb : ecK ≠ lKb := by decide
@[simp] theorem etc_lKb_ne_ecK : lKb ≠ ecK := by decide
@[simp] theorem etc_ecK_ne_lDir : ecK ≠ lDir := by decide
@[simp] theorem etc_lDir_ne_ecK : lDir ≠ ecK := by decide
@[simp] theorem etc_ecK_ne_lFln : ecK ≠ lFln := by decide
@[simp] theorem etc_lFln_ne_ecK : lFln ≠ ecK := by decide
@[simp] theorem etc_ecK_ne_lFll : ecK ≠ lFll := by decide
@[simp] theorem etc_lFll_ne_ecK : lFll ≠ ecK := by decide
@[simp] theorem etc_ecK_ne_lFls : ecK ≠ lFls := by decide
@[simp] theorem etc_lFls_ne_ecK : lFls ≠ ecK := by decide
@[simp] theorem etc_ecK_ne_kFu : ecK ≠ kFu := by decide
@[simp] theorem etc_kFu_ne_ecK : kFu ≠ ecK := by decide
@[simp] theorem etc_ecK_ne_kD : ecK ≠ kD := by decide
@[simp] theorem etc_kD_ne_ecK : kD ≠ ecK := by decide
@[simp] theorem etc_ecZ_ne_ecT : ecZ ≠ ecT := by decide
@[simp] theorem etc_ecZ_ne_ecB : ecZ ≠ ecB := by decide
@[simp] theorem etc_ecZ_ne_ecS : ecZ ≠ ecS := by decide
@[simp] theorem etc_ecZ_ne_ecN : ecZ ≠ ecN := by decide
@[simp] theorem etc_ecZ_ne_ecT1 : ecZ ≠ ecT1 := by decide
@[simp] theorem etc_ecZ_ne_ecH : ecZ ≠ ecH := by decide
@[simp] theorem etc_ecZ_ne_ecT2 : ecZ ≠ ecT2 := by decide
@[simp] theorem etc_ecZ_ne_ecC2 : ecZ ≠ ecC2 := by decide
@[simp] theorem etc_ecZ_ne_ecQ : ecZ ≠ ecQ := by decide
@[simp] theorem etc_ecZ_ne_ecF : ecZ ≠ ecF := by decide
@[simp] theorem etc_ecZ_ne_ecL : ecZ ≠ ecL := by decide
@[simp] theorem etc_ecZ_ne_ecR2 : ecZ ≠ ecR2 := by decide
@[simp] theorem etc_ecZ_ne_ecD1 : ecZ ≠ ecD1 := by decide
@[simp] theorem etc_ecZ_ne_ecE : ecZ ≠ ecE := by decide
@[simp] theorem etc_ecZ_ne_ecI : ecZ ≠ ecI := by decide
@[simp] theorem etc_ecZ_ne_ecK : ecZ ≠ ecK := by decide
@[simp] theorem etc_ecZ_ne_lFl : ecZ ≠ lFl := by decide
@[simp] theorem etc_lFl_ne_ecZ : lFl ≠ ecZ := by decide
@[simp] theorem etc_ecZ_ne_lDh : ecZ ≠ lDh := by decide
@[simp] theorem etc_lDh_ne_ecZ : lDh ≠ ecZ := by decide
@[simp] theorem etc_ecZ_ne_lDt : ecZ ≠ lDt := by decide
@[simp] theorem etc_lDt_ne_ecZ : lDt ≠ ecZ := by decide
@[simp] theorem etc_ecZ_ne_lDg : ecZ ≠ lDg := by decide
@[simp] theorem etc_lDg_ne_ecZ : lDg ≠ ecZ := by decide
@[simp] theorem etc_ecZ_ne_lDi : ecZ ≠ lDi := by decide
@[simp] theorem etc_lDi_ne_ecZ : lDi ≠ ecZ := by decide
@[simp] theorem etc_ecZ_ne_lRp : ecZ ≠ lRp := by decide
@[simp] theorem etc_lRp_ne_ecZ : lRp ≠ ecZ := by decide
@[simp] theorem etc_ecZ_ne_lRn : ecZ ≠ lRn := by decide
@[simp] theorem etc_lRn_ne_ecZ : lRn ≠ ecZ := by decide
@[simp] theorem etc_ecZ_ne_lFle : ecZ ≠ lFle := by decide
@[simp] theorem etc_lFle_ne_ecZ : lFle ≠ ecZ := by decide
@[simp] theorem etc_ecZ_ne_lKb : ecZ ≠ lKb := by decide
@[simp] theorem etc_lKb_ne_ecZ : lKb ≠ ecZ := by decide
@[simp] theorem etc_ecZ_ne_lDir : ecZ ≠ lDir := by decide
@[simp] theorem etc_lDir_ne_ecZ : lDir ≠ ecZ := by decide
@[simp] theorem etc_ecZ_ne_lFln : ecZ ≠ lFln := by decide
@[simp] theorem etc_lFln_ne_ecZ : lFln ≠ ecZ := by decide
@[simp] theorem etc_ecZ_ne_lFll : ecZ ≠ lFll := by decide
@[simp] theorem etc_lFll_ne_ecZ : lFll ≠ ecZ := by decide
@[simp] theorem etc_ecZ_ne_lFls : ecZ ≠ lFls := by decide
@[simp] theorem etc_lFls_ne_ecZ : lFls ≠ ecZ := by decide
@[simp] theorem etc_ecZ_ne_kFu : ecZ ≠ kFu := by decide
@[simp] theorem etc_kFu_ne_ecZ : kFu ≠ ecZ := by decide
@[simp] theorem etc_ecZ_ne_kD : ecZ ≠ kD := by decide
@[simp] theorem etc_kD_ne_ecZ : kD ≠ ecZ := by decide

def ecParams : List MlS := [kFu, kD, ecT, ecB, ecS]
def ecLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, ecN, ecT1, ecH, ecT2, ecC2, ecQ, ecF, ecL, ecR2, ecD1, ecE, ecI, ecK, ecZ]
def ecBody (v : Bool) (C : Ctx) : ProgHOL 64 := prologue ecLocals (.ite (.cmp .lower (vv kD) (.const (BitVec.ofNat 64 (2 ^ 62)))) (.seq (.call (some (some (.local, ecN), none)) fNu [(vv ecS)]) (.ite (vv ecN) (.seq (.call (some (some (.local, ecT1), none)) fIO [(vv kFu), (vv kD), (vv ecS)]) (.seq (.call (some (some (.local, ecH), none)) fW [(vv kFu), (vv kD), (vv ecT1)]) (.ite (tagIsE ecH 6) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv ecH)) (.seq eViewP (.seq (.assign .local ecT2 (.load .one (vv lRp))) (.seq (.assign .local ecC2 (.load .one (.op .add [(vv lRp), (.const 8)]))) (.seq (.call (some (some (.local, ecQ), none)) fD [(vv kFu), (vv kD), (vv ecT2), (vv ecT)]) (.ite (vv ecQ) (.seq (.call (some (some (.local, ecF), none)) fInternFVar [(vv ecT), (vv kD)]) (.seq (.call (some (some (.local, ecL), none)) ExI.fInst1F [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv ecB), (vv ecF), (.const 0)]) (.seq (.call (some (some (.local, ecR2), none)) fInternApp [(vv ecS), (vv ecF)]) (.seq (.assign .local ecD1 (.op .add [(vv kD), (.const 1)])) (.seq (.call (some (some (.local, ecE), none)) fD [(vv kFu), (vv ecD1), (vv ecL), (vv ecR2)]) (.ite (vv ecE) (if v then (.seq (.call (some (some (.local, ecI), none)) fI [(vv kFu), (vv ecD1), (vv ecL)]) (.seq (.call (some (some (.local, ecK), none)) ExI.fInst1F [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv ecC2), (vv ecF), (.const 0)]) (.seq (.call (some (some (.local, ecZ), none)) fD [(vv kFu), (vv ecD1), (vv ecI), (vv ecK)]) (.return (vv ecZ))))) else (.return (.const 1))) (.return (.const 0)))))))) (.return (.const 0))))))))) (.return (.const 0))))) (.return (.const 0)))) hang)

section
variable {σ : Type}

theorem ec_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (v : Bool) (hv : mode.verifiedChecks = v)
    (hcaf : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one))
    (hcnu : C.code.lookup fNu = some ([(nuE, .one)], nuBody, .one))
    (hcio : C.code.lookup fIO = some (pmap kParams, inferIOE C fIOB, .one))
    (hcw : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one))
    (hcd : C.code.lookup fD = some (pmap dParams, dE C, .one))
    (hci : C.code.lookup fI = some (pmap kParams, inferE C fIB, .one))
    (hcI : C.code.lookup ExI.fInst1F = some ([pFu, pH, ExI.pV, ExI.pD].map (fun p => (p, ShapeHOL.one)),
      ExI.fastBody C, .one)) (hcI' : ExI.Codes C (ExI.body C))
    (hcfv : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one))
    (hcap : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one))
    (hIO : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (inferIOE C fIOB) s1 ((knot mode C n).inferIO d' e')
      (PostK (ctxH C H)))
    (hW : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d' e')
      (PostK (ctxH C H)))
    (hI : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (inferE C fIB) s1 ((knot mode C n).infer d' e')
      (PostK (ctxH C H)))
    (hD : ∀ (H : List (BitVec 64)) s1 d' a b, C.H <+: H → Callee (σ := σ) (ctxH C H) dParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW a, Enc.idxW b] (dE C) s1 ((knot mode C n).defeq d' a b)
      (PostB (ctxH C H)))
    (s : AState) (d : Nat) (hd : d < 2 ^ 64) (ty1 body1 b : EIdx) :
    SpecR (σ := σ) (Pre C s (ecParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty1, Enc.idxW body1,
      Enc.idxW b])) (ecBody v C) s (etaCert mode (knot mode C n) C.fe d ty1 body1 b) (PostB C) := by
  refine specR_prologue (postB_locals C) (Knot.params_none C ecLocals ecParams _ (by decide) (by decide)) ?_
  by_cases hd2 : d < 2 ^ 62
  swap
  · have hl : ¬ (BitVec.ofNat 64 d < BitVec.ofNat 64 (2 ^ 62)) := by
      rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]; norm_num; omega
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get, ecParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; first | exact hl | (rw [Nat.mod_eq_of_lt (show d < 18446744073709551616 by omega)]; omega))
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  have hl : BitVec.ofNat 64 d < BitVec.ofNat 64 (2 ^ 62) := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]; norm_num; omega
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ecParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; first | exact hl | (rw [Nat.mod_eq_of_lt (show d < 18446744073709551616 by omega)]; omega))
    (fun _ => ?_) (fun h => absurd h (by decide))
  unfold etaCert
  refine specR_callNIH (C := C) ecN fNu [nuE] [vv ecS] nuBody [Enc.idxW b] (by decide) rfl (by decide) hcnu
    ⟨by simp +decide [Env.get, ecParams, ctxEnv], trivial⟩ (PostB C) (fun r_ w _ _ => w = boolW r_) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [nuE] _ rfl hlk) (nu_spec C hcaf s b))
    (fun g w s1 H1 hp1 hw => ?_)
  subst hw
  cases g
  · refine specR_ifI _ 0 (by simp [boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Bool.not_false, ↓reduceIte]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 1 (by simp [boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  refine Big.specR_callKC (C := ctxH C H1) ecT1 fIO kParams [vv kFu, vv kD, vv ecS] (inferIOE C fIOB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW b] (by decide) rfl (by decide) hcio
    ⟨by simp +decide [Env.get, ecParams, ctxEnv], by simp +decide [Env.get, ecParams, ctxEnv], by simp +decide [Env.get, ecParams, ctxEnv], trivial⟩ (hIO H1 s1 d b hp1) (fun tb s2 H2 hp2 _ => ?_)
  have hp12 : C.H <+: H2 := hp1.trans hp2
  refine Big.specR_callKC (C := ctxH C H2) ecH fW kParams [vv kFu, vv kD, vv ecT1] (whnfE C fWB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW tb] (by decide) rfl (by decide) hcw
    ⟨by simp +decide [Env.get, ecParams, ctxEnv], by simp +decide [Env.get, ecParams, ctxEnv], by simp, trivial⟩ (hW H2 s2 d tb hp12) (fun hh s3 H3 hp3 _ => ?_)
  have hp13 : C.H <+: H3 := hp12.trans hp3
  refine Knot.specR_tagIteV ecH hh 6 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
  swap
  · rw [if_neg (show ¬ (hh.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg)]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H3, hp13, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [if_pos (show (hh.tag == ETag.forallE) = true by simp [htg, ETag.forallE])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv ecH) (Enc.idxW hh) (by decide) (by simp) ?_
  refine specR_viewP (C := ctxH C H3) hh (by simp) (by simp +decide [Env.get] <;> rfl)
    (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun vw P2 hv2 htn2 _ => ?_)
  refine specR_congr (Big.view_bind_eq hh vw _ s3 hv2) ?_
  have h6 : vw.tagN = 6 := by rw [htn2, htg]; rfl
  obtain ⟨ty2, cod2, rfl⟩ : ∃ a c, vw = .forallE a c := by cases vw <;> simp [ENodeView.tagN] at h6 ⊢
  dsimp only
  refine specR_loadI' ecT2 (vv lRp) P2 (P2 + BitVec.ofNat 64 0) (Enc.idxW ty2) (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P2 (Enc.idxW ty2) [Enc.idxW cod2] []) ?_
  refine specR_loadI' ecC2 _ (P2 + 8) (P2 + BitVec.ofNat 64 8) (Enc.idxW cod2) (by decide) (by simp +decide [sev]) rfl
    (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P2 (Enc.idxW ty2) (Enc.idxW cod2) [] []) ?_
  refine specR_dropM ?_
  refine specR_callNIH (C := ctxH C H3) ecQ fD dParams [vv kFu, vv kD, vv ecT2, vv ecT] (dE C)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty2, Enc.idxW ty1] (by decide) rfl (by decide) hcd
    ⟨by simp +decide [Env.get, ecParams, ctxEnv], by simp +decide [Env.get, ecParams, ctxEnv], by simp +decide [Env.get, ecParams, ctxEnv], by simp +decide [Env.get, ecParams, ctxEnv], trivial⟩
    (PostB (ctxH C H3)) (fun r_ w _ _ => w = boolW r_) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => hD H3 s3 d ty2 ty1 hp13 u hu (fun i hi _ => hlk i (by omega)))
    (fun q w s4 H4 hp4 hw => ?_)
  subst hw
  have hp14 : C.H <+: H4 := hp13.trans hp4
  cases q
  · refine specR_ifI _ 0 (by simp [boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H4, hp14, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 1 (by simp [boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
  simp only [↓reduceIte]
  refine ILP.specR_internFVarI (C := ctxH C H4) ra (ctxOK_H hok H4) hcfv ecF (vv ecT) (vv kD) ty1 d (by omega)
    (by decide) (by simp +decide [Env.get, ecParams, ctxEnv]) (by simp +decide [Env.get, ecParams, ctxEnv]) (fun fv s5 => ?_)
  refine ILP.callE_spec (C := ctxH C H4) ecL ExI.fInst1F [pFu, pH, ExI.pV, ExI.pD]
    [.const (BitVec.ofNat 64 coreWalkFuel), vv ecB, vv ecF, .const 0] (ExI.fastBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW body1, Enc.idxW fv, BitVec.ofNat 64 0] (by decide) rfl (by decide) hcI
    ⟨rfl, by simp +decide [Env.get, ecParams, ctxEnv], by simp, rfl, trivial⟩
    (ExI.fast_spec ra (ctxH C H4) (ctxOK_H hok H4) (ExIS.codes_H C H4 hcI') s5 coreWalkFuel body1 fv 0
      CV.coreWalkFuel_lt (by decide)) (fun lhs s6 => ?_)
  refine specR_internAppI (C := ctxH C H4) ra (ctxOK_H hok H4) hcap ecR2 (vv ecS) (vv ecF) b fv (by decide)
    (by simp +decide [Env.get, ecParams, ctxEnv]) (by simp) (fun rhs s7 => ?_)
  refine specR_assignI ecD1 _ (BitVec.ofNat 64 (d + 1)) (by decide)
    (by simp +decide [sev, Env.get, ecParams, ctxEnv]; exact word_add1_eq d) ?_
  refine specR_callNIH (C := ctxH C H4) ecE fD dParams [vv kFu, vv ecD1, vv ecL, vv ecR2] (dE C)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 (d + 1), Enc.idxW lhs, Enc.idxW rhs] (by decide) rfl (by decide) hcd
    ⟨by simp +decide [Env.get, ecParams, ctxEnv], by simp, by simp, by simp, trivial⟩
    (PostB (ctxH C H4)) (fun r_ w _ _ => w = boolW r_) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => hD H4 s7 (d + 1) lhs rhs hp14 u hu (fun i hi _ => hlk i (by omega)))
    (fun e2 w s8 H8 hp8 hw => ?_)
  subst hw
  have hp18 : C.H <+: H8 := hp14.trans hp8
  cases e2
  · refine specR_ifI _ 0 (by simp [boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Bool.not_false, ↓reduceIte]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H8, hp18, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 1 (by simp [boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, hv]
  cases v
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H8, hp18, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  simp only [↓reduceIte]
  refine Big.specR_callKC (C := ctxH C H8) ecI fI kParams [vv kFu, vv ecD1, vv ecL] (inferE C fIB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 (d + 1), Enc.idxW lhs] (by decide) rfl (by decide) hci
    ⟨by simp +decide [Env.get, ecParams, ctxEnv], by simp, by simp, trivial⟩ (hI H8 s8 (d + 1) lhs hp18) (fun t1 s9 H9 hp9 _ => ?_)
  have hp19 : C.H <+: H9 := hp18.trans hp9
  refine ILP.callE_spec (C := ctxH C H9) ecK ExI.fInst1F [pFu, pH, ExI.pV, ExI.pD]
    [.const (BitVec.ofNat 64 coreWalkFuel), vv ecC2, vv ecF, .const 0] (ExI.fastBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW cod2, Enc.idxW fv, BitVec.ofNat 64 0] (by decide) rfl (by decide) hcI
    ⟨rfl, by simp, by simp, rfl, trivial⟩
    (ExI.fast_spec ra (ctxH C H9) (ctxOK_H hok H9) (ExIS.codes_H C H9 hcI') s9 coreWalkFuel cod2 fv 0
      CV.coreWalkFuel_lt (by decide)) (fun t2 s10 => ?_)
  refine specR_congr (m' := (knot mode C n).defeq (d + 1) t1 t2 >>= fun r => pure r) (by simp) ?_
  refine specR_callNIH (C := ctxH C H9) ecZ fD dParams [vv kFu, vv ecD1, vv ecI, vv ecK] (dE C)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 (d + 1), Enc.idxW t1, Enc.idxW t2] (by decide) rfl (by decide) hcd
    ⟨by simp +decide [Env.get, ecParams, ctxEnv], by simp, by simp, by simp, trivial⟩
    (PostB (ctxH C H9)) (fun r_ w _ _ => w = boolW r_) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => hD H9 s10 (d + 1) t1 t2 hp19 u hu (fun i hi _ => hlk i (by omega)))
    (fun z w s11 H11 hp11 hw => ?_)
  subst hw
  exact specR_returnI _ (boolW z) (by simp) (fun t ht => ⟨H11, hp19.trans hp11, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
