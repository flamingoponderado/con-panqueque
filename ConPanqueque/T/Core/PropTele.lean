import ConPanqueque.T.Core.DefeqBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# PropRead's telescope readers: `binderDom`

The domain of the `k`-th syntactic ∀ binder (`optW`).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def bdK := ofString "prd_bdk"
def bdH := ofString "prd_bdh"
def bdA := ofString "prd_bda"
def bdB := ofString "prd_bdb"
def bdR := ofString "prd_bdr"
def fBd := ofString "binderDom"

@[simp] theorem prd_bdK_ne_bdH : bdK ≠ bdH := by decide
@[simp] theorem prd_bdK_ne_bdA : bdK ≠ bdA := by decide
@[simp] theorem prd_bdK_ne_bdB : bdK ≠ bdB := by decide
@[simp] theorem prd_bdK_ne_bdR : bdK ≠ bdR := by decide
@[simp] theorem prd_bdK_ne_lFl : bdK ≠ lFl := by decide
@[simp] theorem prd_lFl_ne_bdK : lFl ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_lDh : bdK ≠ lDh := by decide
@[simp] theorem prd_lDh_ne_bdK : lDh ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_lDt : bdK ≠ lDt := by decide
@[simp] theorem prd_lDt_ne_bdK : lDt ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_lDg : bdK ≠ lDg := by decide
@[simp] theorem prd_lDg_ne_bdK : lDg ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_lDi : bdK ≠ lDi := by decide
@[simp] theorem prd_lDi_ne_bdK : lDi ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_lRp : bdK ≠ lRp := by decide
@[simp] theorem prd_lRp_ne_bdK : lRp ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_lRn : bdK ≠ lRn := by decide
@[simp] theorem prd_lRn_ne_bdK : lRn ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_lFle : bdK ≠ lFle := by decide
@[simp] theorem prd_lFle_ne_bdK : lFle ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_lKb : bdK ≠ lKb := by decide
@[simp] theorem prd_lKb_ne_bdK : lKb ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_lDir : bdK ≠ lDir := by decide
@[simp] theorem prd_lDir_ne_bdK : lDir ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_lFln : bdK ≠ lFln := by decide
@[simp] theorem prd_lFln_ne_bdK : lFln ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_lFll : bdK ≠ lFll := by decide
@[simp] theorem prd_lFll_ne_bdK : lFll ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_lFls : bdK ≠ lFls := by decide
@[simp] theorem prd_lFls_ne_bdK : lFls ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_kFu : bdK ≠ kFu := by decide
@[simp] theorem prd_kFu_ne_bdK : kFu ≠ bdK := by decide
@[simp] theorem prd_bdK_ne_kD : bdK ≠ kD := by decide
@[simp] theorem prd_kD_ne_bdK : kD ≠ bdK := by decide
@[simp] theorem prd_bdH_ne_bdK : bdH ≠ bdK := by decide
@[simp] theorem prd_bdH_ne_bdA : bdH ≠ bdA := by decide
@[simp] theorem prd_bdH_ne_bdB : bdH ≠ bdB := by decide
@[simp] theorem prd_bdH_ne_bdR : bdH ≠ bdR := by decide
@[simp] theorem prd_bdH_ne_lFl : bdH ≠ lFl := by decide
@[simp] theorem prd_lFl_ne_bdH : lFl ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_lDh : bdH ≠ lDh := by decide
@[simp] theorem prd_lDh_ne_bdH : lDh ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_lDt : bdH ≠ lDt := by decide
@[simp] theorem prd_lDt_ne_bdH : lDt ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_lDg : bdH ≠ lDg := by decide
@[simp] theorem prd_lDg_ne_bdH : lDg ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_lDi : bdH ≠ lDi := by decide
@[simp] theorem prd_lDi_ne_bdH : lDi ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_lRp : bdH ≠ lRp := by decide
@[simp] theorem prd_lRp_ne_bdH : lRp ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_lRn : bdH ≠ lRn := by decide
@[simp] theorem prd_lRn_ne_bdH : lRn ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_lFle : bdH ≠ lFle := by decide
@[simp] theorem prd_lFle_ne_bdH : lFle ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_lKb : bdH ≠ lKb := by decide
@[simp] theorem prd_lKb_ne_bdH : lKb ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_lDir : bdH ≠ lDir := by decide
@[simp] theorem prd_lDir_ne_bdH : lDir ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_lFln : bdH ≠ lFln := by decide
@[simp] theorem prd_lFln_ne_bdH : lFln ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_lFll : bdH ≠ lFll := by decide
@[simp] theorem prd_lFll_ne_bdH : lFll ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_lFls : bdH ≠ lFls := by decide
@[simp] theorem prd_lFls_ne_bdH : lFls ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_kFu : bdH ≠ kFu := by decide
@[simp] theorem prd_kFu_ne_bdH : kFu ≠ bdH := by decide
@[simp] theorem prd_bdH_ne_kD : bdH ≠ kD := by decide
@[simp] theorem prd_kD_ne_bdH : kD ≠ bdH := by decide
@[simp] theorem prd_bdA_ne_bdK : bdA ≠ bdK := by decide
@[simp] theorem prd_bdA_ne_bdH : bdA ≠ bdH := by decide
@[simp] theorem prd_bdA_ne_bdB : bdA ≠ bdB := by decide
@[simp] theorem prd_bdA_ne_bdR : bdA ≠ bdR := by decide
@[simp] theorem prd_bdA_ne_lFl : bdA ≠ lFl := by decide
@[simp] theorem prd_lFl_ne_bdA : lFl ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_lDh : bdA ≠ lDh := by decide
@[simp] theorem prd_lDh_ne_bdA : lDh ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_lDt : bdA ≠ lDt := by decide
@[simp] theorem prd_lDt_ne_bdA : lDt ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_lDg : bdA ≠ lDg := by decide
@[simp] theorem prd_lDg_ne_bdA : lDg ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_lDi : bdA ≠ lDi := by decide
@[simp] theorem prd_lDi_ne_bdA : lDi ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_lRp : bdA ≠ lRp := by decide
@[simp] theorem prd_lRp_ne_bdA : lRp ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_lRn : bdA ≠ lRn := by decide
@[simp] theorem prd_lRn_ne_bdA : lRn ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_lFle : bdA ≠ lFle := by decide
@[simp] theorem prd_lFle_ne_bdA : lFle ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_lKb : bdA ≠ lKb := by decide
@[simp] theorem prd_lKb_ne_bdA : lKb ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_lDir : bdA ≠ lDir := by decide
@[simp] theorem prd_lDir_ne_bdA : lDir ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_lFln : bdA ≠ lFln := by decide
@[simp] theorem prd_lFln_ne_bdA : lFln ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_lFll : bdA ≠ lFll := by decide
@[simp] theorem prd_lFll_ne_bdA : lFll ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_lFls : bdA ≠ lFls := by decide
@[simp] theorem prd_lFls_ne_bdA : lFls ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_kFu : bdA ≠ kFu := by decide
@[simp] theorem prd_kFu_ne_bdA : kFu ≠ bdA := by decide
@[simp] theorem prd_bdA_ne_kD : bdA ≠ kD := by decide
@[simp] theorem prd_kD_ne_bdA : kD ≠ bdA := by decide
@[simp] theorem prd_bdB_ne_bdK : bdB ≠ bdK := by decide
@[simp] theorem prd_bdB_ne_bdH : bdB ≠ bdH := by decide
@[simp] theorem prd_bdB_ne_bdA : bdB ≠ bdA := by decide
@[simp] theorem prd_bdB_ne_bdR : bdB ≠ bdR := by decide
@[simp] theorem prd_bdB_ne_lFl : bdB ≠ lFl := by decide
@[simp] theorem prd_lFl_ne_bdB : lFl ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_lDh : bdB ≠ lDh := by decide
@[simp] theorem prd_lDh_ne_bdB : lDh ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_lDt : bdB ≠ lDt := by decide
@[simp] theorem prd_lDt_ne_bdB : lDt ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_lDg : bdB ≠ lDg := by decide
@[simp] theorem prd_lDg_ne_bdB : lDg ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_lDi : bdB ≠ lDi := by decide
@[simp] theorem prd_lDi_ne_bdB : lDi ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_lRp : bdB ≠ lRp := by decide
@[simp] theorem prd_lRp_ne_bdB : lRp ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_lRn : bdB ≠ lRn := by decide
@[simp] theorem prd_lRn_ne_bdB : lRn ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_lFle : bdB ≠ lFle := by decide
@[simp] theorem prd_lFle_ne_bdB : lFle ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_lKb : bdB ≠ lKb := by decide
@[simp] theorem prd_lKb_ne_bdB : lKb ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_lDir : bdB ≠ lDir := by decide
@[simp] theorem prd_lDir_ne_bdB : lDir ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_lFln : bdB ≠ lFln := by decide
@[simp] theorem prd_lFln_ne_bdB : lFln ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_lFll : bdB ≠ lFll := by decide
@[simp] theorem prd_lFll_ne_bdB : lFll ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_lFls : bdB ≠ lFls := by decide
@[simp] theorem prd_lFls_ne_bdB : lFls ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_kFu : bdB ≠ kFu := by decide
@[simp] theorem prd_kFu_ne_bdB : kFu ≠ bdB := by decide
@[simp] theorem prd_bdB_ne_kD : bdB ≠ kD := by decide
@[simp] theorem prd_kD_ne_bdB : kD ≠ bdB := by decide
@[simp] theorem prd_bdR_ne_bdK : bdR ≠ bdK := by decide
@[simp] theorem prd_bdR_ne_bdH : bdR ≠ bdH := by decide
@[simp] theorem prd_bdR_ne_bdA : bdR ≠ bdA := by decide
@[simp] theorem prd_bdR_ne_bdB : bdR ≠ bdB := by decide
@[simp] theorem prd_bdR_ne_lFl : bdR ≠ lFl := by decide
@[simp] theorem prd_lFl_ne_bdR : lFl ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_lDh : bdR ≠ lDh := by decide
@[simp] theorem prd_lDh_ne_bdR : lDh ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_lDt : bdR ≠ lDt := by decide
@[simp] theorem prd_lDt_ne_bdR : lDt ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_lDg : bdR ≠ lDg := by decide
@[simp] theorem prd_lDg_ne_bdR : lDg ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_lDi : bdR ≠ lDi := by decide
@[simp] theorem prd_lDi_ne_bdR : lDi ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_lRp : bdR ≠ lRp := by decide
@[simp] theorem prd_lRp_ne_bdR : lRp ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_lRn : bdR ≠ lRn := by decide
@[simp] theorem prd_lRn_ne_bdR : lRn ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_lFle : bdR ≠ lFle := by decide
@[simp] theorem prd_lFle_ne_bdR : lFle ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_lKb : bdR ≠ lKb := by decide
@[simp] theorem prd_lKb_ne_bdR : lKb ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_lDir : bdR ≠ lDir := by decide
@[simp] theorem prd_lDir_ne_bdR : lDir ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_lFln : bdR ≠ lFln := by decide
@[simp] theorem prd_lFln_ne_bdR : lFln ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_lFll : bdR ≠ lFll := by decide
@[simp] theorem prd_lFll_ne_bdR : lFll ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_lFls : bdR ≠ lFls := by decide
@[simp] theorem prd_lFls_ne_bdR : lFls ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_kFu : bdR ≠ kFu := by decide
@[simp] theorem prd_kFu_ne_bdR : kFu ≠ bdR := by decide
@[simp] theorem prd_bdR_ne_kD : bdR ≠ kD := by decide
@[simp] theorem prd_kD_ne_bdR : kD ≠ bdR := by decide

def ljF := ofString "plj_ljf"
def ljK := ofString "plj_ljk"
def ljH := ofString "plj_ljh"
def ljB := ofString "plj_ljb"
def ljR := ofString "plj_ljr"
def ljJ := ofString "plj_ljj"
def ljW := ofString "plj_ljw"
def fLj := ofString "lamProj"

@[simp] theorem plj_ljF_ne_ljK : ljF ≠ ljK := by decide
@[simp] theorem plj_ljF_ne_ljH : ljF ≠ ljH := by decide
@[simp] theorem plj_ljF_ne_ljB : ljF ≠ ljB := by decide
@[simp] theorem plj_ljF_ne_ljR : ljF ≠ ljR := by decide
@[simp] theorem plj_ljF_ne_ljJ : ljF ≠ ljJ := by decide
@[simp] theorem plj_ljF_ne_ljW : ljF ≠ ljW := by decide
@[simp] theorem plj_ljF_ne_lFl : ljF ≠ lFl := by decide
@[simp] theorem plj_lFl_ne_ljF : lFl ≠ ljF := by decide
@[simp] theorem plj_ljF_ne_lDh : ljF ≠ lDh := by decide
@[simp] theorem plj_lDh_ne_ljF : lDh ≠ ljF := by decide
@[simp] theorem plj_ljF_ne_lDt : ljF ≠ lDt := by decide
@[simp] theorem plj_lDt_ne_ljF : lDt ≠ ljF := by decide
@[simp] theorem plj_ljF_ne_lDg : ljF ≠ lDg := by decide
@[simp] theorem plj_lDg_ne_ljF : lDg ≠ ljF := by decide
@[simp] theorem plj_ljF_ne_lDi : ljF ≠ lDi := by decide
@[simp] theorem plj_lDi_ne_ljF : lDi ≠ ljF := by decide
@[simp] theorem plj_ljF_ne_lRp : ljF ≠ lRp := by decide
@[simp] theorem plj_lRp_ne_ljF : lRp ≠ ljF := by decide
@[simp] theorem plj_ljF_ne_lRn : ljF ≠ lRn := by decide
@[simp] theorem plj_lRn_ne_ljF : lRn ≠ ljF := by decide
@[simp] theorem plj_ljF_ne_lFle : ljF ≠ lFle := by decide
@[simp] theorem plj_lFle_ne_ljF : lFle ≠ ljF := by decide
@[simp] theorem plj_ljF_ne_lKb : ljF ≠ lKb := by decide
@[simp] theorem plj_lKb_ne_ljF : lKb ≠ ljF := by decide
@[simp] theorem plj_ljF_ne_lDir : ljF ≠ lDir := by decide
@[simp] theorem plj_lDir_ne_ljF : lDir ≠ ljF := by decide
@[simp] theorem plj_ljF_ne_lFln : ljF ≠ lFln := by decide
@[simp] theorem plj_lFln_ne_ljF : lFln ≠ ljF := by decide
@[simp] theorem plj_ljF_ne_lFll : ljF ≠ lFll := by decide
@[simp] theorem plj_lFll_ne_ljF : lFll ≠ ljF := by decide
@[simp] theorem plj_ljF_ne_lFls : ljF ≠ lFls := by decide
@[simp] theorem plj_lFls_ne_ljF : lFls ≠ ljF := by decide
@[simp] theorem plj_ljF_ne_kFu : ljF ≠ kFu := by decide
@[simp] theorem plj_kFu_ne_ljF : kFu ≠ ljF := by decide
@[simp] theorem plj_ljF_ne_kD : ljF ≠ kD := by decide
@[simp] theorem plj_kD_ne_ljF : kD ≠ ljF := by decide
@[simp] theorem plj_ljK_ne_ljF : ljK ≠ ljF := by decide
@[simp] theorem plj_ljK_ne_ljH : ljK ≠ ljH := by decide
@[simp] theorem plj_ljK_ne_ljB : ljK ≠ ljB := by decide
@[simp] theorem plj_ljK_ne_ljR : ljK ≠ ljR := by decide
@[simp] theorem plj_ljK_ne_ljJ : ljK ≠ ljJ := by decide
@[simp] theorem plj_ljK_ne_ljW : ljK ≠ ljW := by decide
@[simp] theorem plj_ljK_ne_lFl : ljK ≠ lFl := by decide
@[simp] theorem plj_lFl_ne_ljK : lFl ≠ ljK := by decide
@[simp] theorem plj_ljK_ne_lDh : ljK ≠ lDh := by decide
@[simp] theorem plj_lDh_ne_ljK : lDh ≠ ljK := by decide
@[simp] theorem plj_ljK_ne_lDt : ljK ≠ lDt := by decide
@[simp] theorem plj_lDt_ne_ljK : lDt ≠ ljK := by decide
@[simp] theorem plj_ljK_ne_lDg : ljK ≠ lDg := by decide
@[simp] theorem plj_lDg_ne_ljK : lDg ≠ ljK := by decide
@[simp] theorem plj_ljK_ne_lDi : ljK ≠ lDi := by decide
@[simp] theorem plj_lDi_ne_ljK : lDi ≠ ljK := by decide
@[simp] theorem plj_ljK_ne_lRp : ljK ≠ lRp := by decide
@[simp] theorem plj_lRp_ne_ljK : lRp ≠ ljK := by decide
@[simp] theorem plj_ljK_ne_lRn : ljK ≠ lRn := by decide
@[simp] theorem plj_lRn_ne_ljK : lRn ≠ ljK := by decide
@[simp] theorem plj_ljK_ne_lFle : ljK ≠ lFle := by decide
@[simp] theorem plj_lFle_ne_ljK : lFle ≠ ljK := by decide
@[simp] theorem plj_ljK_ne_lKb : ljK ≠ lKb := by decide
@[simp] theorem plj_lKb_ne_ljK : lKb ≠ ljK := by decide
@[simp] theorem plj_ljK_ne_lDir : ljK ≠ lDir := by decide
@[simp] theorem plj_lDir_ne_ljK : lDir ≠ ljK := by decide
@[simp] theorem plj_ljK_ne_lFln : ljK ≠ lFln := by decide
@[simp] theorem plj_lFln_ne_ljK : lFln ≠ ljK := by decide
@[simp] theorem plj_ljK_ne_lFll : ljK ≠ lFll := by decide
@[simp] theorem plj_lFll_ne_ljK : lFll ≠ ljK := by decide
@[simp] theorem plj_ljK_ne_lFls : ljK ≠ lFls := by decide
@[simp] theorem plj_lFls_ne_ljK : lFls ≠ ljK := by decide
@[simp] theorem plj_ljK_ne_kFu : ljK ≠ kFu := by decide
@[simp] theorem plj_kFu_ne_ljK : kFu ≠ ljK := by decide
@[simp] theorem plj_ljK_ne_kD : ljK ≠ kD := by decide
@[simp] theorem plj_kD_ne_ljK : kD ≠ ljK := by decide
@[simp] theorem plj_ljH_ne_ljF : ljH ≠ ljF := by decide
@[simp] theorem plj_ljH_ne_ljK : ljH ≠ ljK := by decide
@[simp] theorem plj_ljH_ne_ljB : ljH ≠ ljB := by decide
@[simp] theorem plj_ljH_ne_ljR : ljH ≠ ljR := by decide
@[simp] theorem plj_ljH_ne_ljJ : ljH ≠ ljJ := by decide
@[simp] theorem plj_ljH_ne_ljW : ljH ≠ ljW := by decide
@[simp] theorem plj_ljH_ne_lFl : ljH ≠ lFl := by decide
@[simp] theorem plj_lFl_ne_ljH : lFl ≠ ljH := by decide
@[simp] theorem plj_ljH_ne_lDh : ljH ≠ lDh := by decide
@[simp] theorem plj_lDh_ne_ljH : lDh ≠ ljH := by decide
@[simp] theorem plj_ljH_ne_lDt : ljH ≠ lDt := by decide
@[simp] theorem plj_lDt_ne_ljH : lDt ≠ ljH := by decide
@[simp] theorem plj_ljH_ne_lDg : ljH ≠ lDg := by decide
@[simp] theorem plj_lDg_ne_ljH : lDg ≠ ljH := by decide
@[simp] theorem plj_ljH_ne_lDi : ljH ≠ lDi := by decide
@[simp] theorem plj_lDi_ne_ljH : lDi ≠ ljH := by decide
@[simp] theorem plj_ljH_ne_lRp : ljH ≠ lRp := by decide
@[simp] theorem plj_lRp_ne_ljH : lRp ≠ ljH := by decide
@[simp] theorem plj_ljH_ne_lRn : ljH ≠ lRn := by decide
@[simp] theorem plj_lRn_ne_ljH : lRn ≠ ljH := by decide
@[simp] theorem plj_ljH_ne_lFle : ljH ≠ lFle := by decide
@[simp] theorem plj_lFle_ne_ljH : lFle ≠ ljH := by decide
@[simp] theorem plj_ljH_ne_lKb : ljH ≠ lKb := by decide
@[simp] theorem plj_lKb_ne_ljH : lKb ≠ ljH := by decide
@[simp] theorem plj_ljH_ne_lDir : ljH ≠ lDir := by decide
@[simp] theorem plj_lDir_ne_ljH : lDir ≠ ljH := by decide
@[simp] theorem plj_ljH_ne_lFln : ljH ≠ lFln := by decide
@[simp] theorem plj_lFln_ne_ljH : lFln ≠ ljH := by decide
@[simp] theorem plj_ljH_ne_lFll : ljH ≠ lFll := by decide
@[simp] theorem plj_lFll_ne_ljH : lFll ≠ ljH := by decide
@[simp] theorem plj_ljH_ne_lFls : ljH ≠ lFls := by decide
@[simp] theorem plj_lFls_ne_ljH : lFls ≠ ljH := by decide
@[simp] theorem plj_ljH_ne_kFu : ljH ≠ kFu := by decide
@[simp] theorem plj_kFu_ne_ljH : kFu ≠ ljH := by decide
@[simp] theorem plj_ljH_ne_kD : ljH ≠ kD := by decide
@[simp] theorem plj_kD_ne_ljH : kD ≠ ljH := by decide
@[simp] theorem plj_ljB_ne_ljF : ljB ≠ ljF := by decide
@[simp] theorem plj_ljB_ne_ljK : ljB ≠ ljK := by decide
@[simp] theorem plj_ljB_ne_ljH : ljB ≠ ljH := by decide
@[simp] theorem plj_ljB_ne_ljR : ljB ≠ ljR := by decide
@[simp] theorem plj_ljB_ne_ljJ : ljB ≠ ljJ := by decide
@[simp] theorem plj_ljB_ne_ljW : ljB ≠ ljW := by decide
@[simp] theorem plj_ljB_ne_lFl : ljB ≠ lFl := by decide
@[simp] theorem plj_lFl_ne_ljB : lFl ≠ ljB := by decide
@[simp] theorem plj_ljB_ne_lDh : ljB ≠ lDh := by decide
@[simp] theorem plj_lDh_ne_ljB : lDh ≠ ljB := by decide
@[simp] theorem plj_ljB_ne_lDt : ljB ≠ lDt := by decide
@[simp] theorem plj_lDt_ne_ljB : lDt ≠ ljB := by decide
@[simp] theorem plj_ljB_ne_lDg : ljB ≠ lDg := by decide
@[simp] theorem plj_lDg_ne_ljB : lDg ≠ ljB := by decide
@[simp] theorem plj_ljB_ne_lDi : ljB ≠ lDi := by decide
@[simp] theorem plj_lDi_ne_ljB : lDi ≠ ljB := by decide
@[simp] theorem plj_ljB_ne_lRp : ljB ≠ lRp := by decide
@[simp] theorem plj_lRp_ne_ljB : lRp ≠ ljB := by decide
@[simp] theorem plj_ljB_ne_lRn : ljB ≠ lRn := by decide
@[simp] theorem plj_lRn_ne_ljB : lRn ≠ ljB := by decide
@[simp] theorem plj_ljB_ne_lFle : ljB ≠ lFle := by decide
@[simp] theorem plj_lFle_ne_ljB : lFle ≠ ljB := by decide
@[simp] theorem plj_ljB_ne_lKb : ljB ≠ lKb := by decide
@[simp] theorem plj_lKb_ne_ljB : lKb ≠ ljB := by decide
@[simp] theorem plj_ljB_ne_lDir : ljB ≠ lDir := by decide
@[simp] theorem plj_lDir_ne_ljB : lDir ≠ ljB := by decide
@[simp] theorem plj_ljB_ne_lFln : ljB ≠ lFln := by decide
@[simp] theorem plj_lFln_ne_ljB : lFln ≠ ljB := by decide
@[simp] theorem plj_ljB_ne_lFll : ljB ≠ lFll := by decide
@[simp] theorem plj_lFll_ne_ljB : lFll ≠ ljB := by decide
@[simp] theorem plj_ljB_ne_lFls : ljB ≠ lFls := by decide
@[simp] theorem plj_lFls_ne_ljB : lFls ≠ ljB := by decide
@[simp] theorem plj_ljB_ne_kFu : ljB ≠ kFu := by decide
@[simp] theorem plj_kFu_ne_ljB : kFu ≠ ljB := by decide
@[simp] theorem plj_ljB_ne_kD : ljB ≠ kD := by decide
@[simp] theorem plj_kD_ne_ljB : kD ≠ ljB := by decide
@[simp] theorem plj_ljR_ne_ljF : ljR ≠ ljF := by decide
@[simp] theorem plj_ljR_ne_ljK : ljR ≠ ljK := by decide
@[simp] theorem plj_ljR_ne_ljH : ljR ≠ ljH := by decide
@[simp] theorem plj_ljR_ne_ljB : ljR ≠ ljB := by decide
@[simp] theorem plj_ljR_ne_ljJ : ljR ≠ ljJ := by decide
@[simp] theorem plj_ljR_ne_ljW : ljR ≠ ljW := by decide
@[simp] theorem plj_ljR_ne_lFl : ljR ≠ lFl := by decide
@[simp] theorem plj_lFl_ne_ljR : lFl ≠ ljR := by decide
@[simp] theorem plj_ljR_ne_lDh : ljR ≠ lDh := by decide
@[simp] theorem plj_lDh_ne_ljR : lDh ≠ ljR := by decide
@[simp] theorem plj_ljR_ne_lDt : ljR ≠ lDt := by decide
@[simp] theorem plj_lDt_ne_ljR : lDt ≠ ljR := by decide
@[simp] theorem plj_ljR_ne_lDg : ljR ≠ lDg := by decide
@[simp] theorem plj_lDg_ne_ljR : lDg ≠ ljR := by decide
@[simp] theorem plj_ljR_ne_lDi : ljR ≠ lDi := by decide
@[simp] theorem plj_lDi_ne_ljR : lDi ≠ ljR := by decide
@[simp] theorem plj_ljR_ne_lRp : ljR ≠ lRp := by decide
@[simp] theorem plj_lRp_ne_ljR : lRp ≠ ljR := by decide
@[simp] theorem plj_ljR_ne_lRn : ljR ≠ lRn := by decide
@[simp] theorem plj_lRn_ne_ljR : lRn ≠ ljR := by decide
@[simp] theorem plj_ljR_ne_lFle : ljR ≠ lFle := by decide
@[simp] theorem plj_lFle_ne_ljR : lFle ≠ ljR := by decide
@[simp] theorem plj_ljR_ne_lKb : ljR ≠ lKb := by decide
@[simp] theorem plj_lKb_ne_ljR : lKb ≠ ljR := by decide
@[simp] theorem plj_ljR_ne_lDir : ljR ≠ lDir := by decide
@[simp] theorem plj_lDir_ne_ljR : lDir ≠ ljR := by decide
@[simp] theorem plj_ljR_ne_lFln : ljR ≠ lFln := by decide
@[simp] theorem plj_lFln_ne_ljR : lFln ≠ ljR := by decide
@[simp] theorem plj_ljR_ne_lFll : ljR ≠ lFll := by decide
@[simp] theorem plj_lFll_ne_ljR : lFll ≠ ljR := by decide
@[simp] theorem plj_ljR_ne_lFls : ljR ≠ lFls := by decide
@[simp] theorem plj_lFls_ne_ljR : lFls ≠ ljR := by decide
@[simp] theorem plj_ljR_ne_kFu : ljR ≠ kFu := by decide
@[simp] theorem plj_kFu_ne_ljR : kFu ≠ ljR := by decide
@[simp] theorem plj_ljR_ne_kD : ljR ≠ kD := by decide
@[simp] theorem plj_kD_ne_ljR : kD ≠ ljR := by decide
@[simp] theorem plj_ljJ_ne_ljF : ljJ ≠ ljF := by decide
@[simp] theorem plj_ljJ_ne_ljK : ljJ ≠ ljK := by decide
@[simp] theorem plj_ljJ_ne_ljH : ljJ ≠ ljH := by decide
@[simp] theorem plj_ljJ_ne_ljB : ljJ ≠ ljB := by decide
@[simp] theorem plj_ljJ_ne_ljR : ljJ ≠ ljR := by decide
@[simp] theorem plj_ljJ_ne_ljW : ljJ ≠ ljW := by decide
@[simp] theorem plj_ljJ_ne_lFl : ljJ ≠ lFl := by decide
@[simp] theorem plj_lFl_ne_ljJ : lFl ≠ ljJ := by decide
@[simp] theorem plj_ljJ_ne_lDh : ljJ ≠ lDh := by decide
@[simp] theorem plj_lDh_ne_ljJ : lDh ≠ ljJ := by decide
@[simp] theorem plj_ljJ_ne_lDt : ljJ ≠ lDt := by decide
@[simp] theorem plj_lDt_ne_ljJ : lDt ≠ ljJ := by decide
@[simp] theorem plj_ljJ_ne_lDg : ljJ ≠ lDg := by decide
@[simp] theorem plj_lDg_ne_ljJ : lDg ≠ ljJ := by decide
@[simp] theorem plj_ljJ_ne_lDi : ljJ ≠ lDi := by decide
@[simp] theorem plj_lDi_ne_ljJ : lDi ≠ ljJ := by decide
@[simp] theorem plj_ljJ_ne_lRp : ljJ ≠ lRp := by decide
@[simp] theorem plj_lRp_ne_ljJ : lRp ≠ ljJ := by decide
@[simp] theorem plj_ljJ_ne_lRn : ljJ ≠ lRn := by decide
@[simp] theorem plj_lRn_ne_ljJ : lRn ≠ ljJ := by decide
@[simp] theorem plj_ljJ_ne_lFle : ljJ ≠ lFle := by decide
@[simp] theorem plj_lFle_ne_ljJ : lFle ≠ ljJ := by decide
@[simp] theorem plj_ljJ_ne_lKb : ljJ ≠ lKb := by decide
@[simp] theorem plj_lKb_ne_ljJ : lKb ≠ ljJ := by decide
@[simp] theorem plj_ljJ_ne_lDir : ljJ ≠ lDir := by decide
@[simp] theorem plj_lDir_ne_ljJ : lDir ≠ ljJ := by decide
@[simp] theorem plj_ljJ_ne_lFln : ljJ ≠ lFln := by decide
@[simp] theorem plj_lFln_ne_ljJ : lFln ≠ ljJ := by decide
@[simp] theorem plj_ljJ_ne_lFll : ljJ ≠ lFll := by decide
@[simp] theorem plj_lFll_ne_ljJ : lFll ≠ ljJ := by decide
@[simp] theorem plj_ljJ_ne_lFls : ljJ ≠ lFls := by decide
@[simp] theorem plj_lFls_ne_ljJ : lFls ≠ ljJ := by decide
@[simp] theorem plj_ljJ_ne_kFu : ljJ ≠ kFu := by decide
@[simp] theorem plj_kFu_ne_ljJ : kFu ≠ ljJ := by decide
@[simp] theorem plj_ljJ_ne_kD : ljJ ≠ kD := by decide
@[simp] theorem plj_kD_ne_ljJ : kD ≠ ljJ := by decide
@[simp] theorem plj_ljW_ne_ljF : ljW ≠ ljF := by decide
@[simp] theorem plj_ljW_ne_ljK : ljW ≠ ljK := by decide
@[simp] theorem plj_ljW_ne_ljH : ljW ≠ ljH := by decide
@[simp] theorem plj_ljW_ne_ljB : ljW ≠ ljB := by decide
@[simp] theorem plj_ljW_ne_ljR : ljW ≠ ljR := by decide
@[simp] theorem plj_ljW_ne_ljJ : ljW ≠ ljJ := by decide
@[simp] theorem plj_ljW_ne_lFl : ljW ≠ lFl := by decide
@[simp] theorem plj_lFl_ne_ljW : lFl ≠ ljW := by decide
@[simp] theorem plj_ljW_ne_lDh : ljW ≠ lDh := by decide
@[simp] theorem plj_lDh_ne_ljW : lDh ≠ ljW := by decide
@[simp] theorem plj_ljW_ne_lDt : ljW ≠ lDt := by decide
@[simp] theorem plj_lDt_ne_ljW : lDt ≠ ljW := by decide
@[simp] theorem plj_ljW_ne_lDg : ljW ≠ lDg := by decide
@[simp] theorem plj_lDg_ne_ljW : lDg ≠ ljW := by decide
@[simp] theorem plj_ljW_ne_lDi : ljW ≠ lDi := by decide
@[simp] theorem plj_lDi_ne_ljW : lDi ≠ ljW := by decide
@[simp] theorem plj_ljW_ne_lRp : ljW ≠ lRp := by decide
@[simp] theorem plj_lRp_ne_ljW : lRp ≠ ljW := by decide
@[simp] theorem plj_ljW_ne_lRn : ljW ≠ lRn := by decide
@[simp] theorem plj_lRn_ne_ljW : lRn ≠ ljW := by decide
@[simp] theorem plj_ljW_ne_lFle : ljW ≠ lFle := by decide
@[simp] theorem plj_lFle_ne_ljW : lFle ≠ ljW := by decide
@[simp] theorem plj_ljW_ne_lKb : ljW ≠ lKb := by decide
@[simp] theorem plj_lKb_ne_ljW : lKb ≠ ljW := by decide
@[simp] theorem plj_ljW_ne_lDir : ljW ≠ lDir := by decide
@[simp] theorem plj_lDir_ne_ljW : lDir ≠ ljW := by decide
@[simp] theorem plj_ljW_ne_lFln : ljW ≠ lFln := by decide
@[simp] theorem plj_lFln_ne_ljW : lFln ≠ ljW := by decide
@[simp] theorem plj_ljW_ne_lFll : ljW ≠ lFll := by decide
@[simp] theorem plj_lFll_ne_ljW : lFll ≠ ljW := by decide
@[simp] theorem plj_ljW_ne_lFls : ljW ≠ lFls := by decide
@[simp] theorem plj_lFls_ne_ljW : lFls ≠ ljW := by decide
@[simp] theorem plj_ljW_ne_kFu : ljW ≠ kFu := by decide
@[simp] theorem plj_kFu_ne_ljW : kFu ≠ ljW := by decide
@[simp] theorem plj_ljW_ne_kD : ljW ≠ kD := by decide
@[simp] theorem plj_kD_ne_ljW : kD ≠ ljW := by decide

def ljParams : List MlS := [ljF, ljK, ljH]
def ljLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, ljB, ljR, ljJ, ljW]
def ljBody (C : Ctx) : ProgHOL 64 := prologue ljLocals (.ite (.cmp .equal (vv ljF) (.const 0)) hang (.ite (tagIsE ljH 5) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv ljH)) (.seq eViewP (.seq (.assign .local ljB (.load .one (.op .add [(vv lRp), (.const 8)]))) (.seq (.call (some (some (.local, ljR), none)) fLj [(.op .sub [(vv ljF), (.const 1)]), (.op .add [(vv ljK), (.const 1)]), (vv ljB)]) (.return (vv ljR))))))) (.ite (tagIsE ljH 0) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv ljH)) (.seq eViewP (.ite (.cmp .equal (vv lRn) (.const 0)) (.seq (.assign .local ljJ (.const 0)) (.ite (.cmp .lower (vv ljJ) (vv ljK)) (alloc2 C ljW (vv ljK) (vv ljJ) (.return (vv ljW))) (.return (.const 0)))) (.ite (.cmp .equal (vv lRn) (.const 1)) (.seq (.assign .local ljJ (.load .one (vv lRp))) (.ite (.cmp .lower (vv ljJ) (vv ljK)) (alloc2 C ljW (vv ljK) (vv ljJ) (.return (vv ljW))) (.return (.const 0)))) hang))))) (.return (.const 0)))))

def bdParams : List MlS := [bdK, bdH]
def bdLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, bdA, bdB, bdR]
def bdBody : ProgHOL 64 := prologue bdLocals (.ite (tagIsE bdH 6) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv bdH)) (.seq eViewP (.seq (.assign .local bdA (.load .one (vv lRp))) (.seq (.assign .local bdB (.load .one (.op .add [(vv lRp), (.const 8)]))) (.ite (.cmp .equal (vv bdK) (.const 0)) (.return (.op .add [(vv bdA), (.const 1)])) (.seq (.call (some (some (.local, bdR), none)) fBd [(.op .sub [(vv bdK), (.const 1)]), (vv bdB)]) (.return (vv bdR))))))))) (.return (.const 0)))

section
variable {σ : Type}

theorem bd_spec (C : Ctx) (hcb : C.code.lookup fBd = some (bdParams.map (fun p => (p, ShapeHOL.one)), bdBody, .one)) :
    ∀ k (h : EIdx) (s : AState), k < 2 ^ 64 →
      SpecR (σ := σ) (Pre C s (bdParams.zip [BitVec.ofNat 64 k, Enc.idxW h])) bdBody s (binderDom k h) (UD.PostO C) := by
  intro k
  induction k with
  | zero =>
    intro h s _
    refine specR_prologue (UD.postO_locals C) (Knot.params_none C bdLocals bdParams _ (by decide) (by decide)) ?_
    rw [binderDom]
    refine Knot.specR_tagIteV bdH h 6 (by decide) (by decide) (by simp +decide [Env.get, bdParams, ctxEnv])
      (fun htg => ?_) (fun htg => ?_)
    swap
    · rw [if_neg (show ¬ (h.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg)]
      exact specR_returnI _ (optW none) (by simp [optWG]; rfl)
        (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    rw [if_pos (show (h.tag == ETag.forallE) = true by simp [htg, ETag.forallE])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv bdH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, bdParams, ctxEnv]) ?_
    refine specR_viewP h (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
      (fun v P hv htn _ => ?_)
    have h6 : v.tagN = 6 := by rw [htn, htg]; rfl
    obtain ⟨ty, b, rfl⟩ : ∃ ty b, v = .forallE ty b := by
      cases v <;> simp [ENodeView.tagN] at h6 ⊢
    have hvb : s.store.viewBind h = some (ty, b) := viewBind_of_view_forallE (by rw [htg]; rfl) hv
    refine specR_runBind (by rw [viewBind_run, hvb]) ?_
    dsimp only
    refine specR_loadI' bdA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW ty) [Enc.idxW b] []) ?_
    refine specR_loadI' bdB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW b) [] []) ?_
    refine specR_dropM ?_

    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, bdParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ (optW (some ty)) (by simp [sev, optWG])
      (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro h s hk
    refine specR_prologue (UD.postO_locals C) (Knot.params_none C bdLocals bdParams _ (by decide) (by decide)) ?_
    rw [binderDom]
    refine Knot.specR_tagIteV bdH h 6 (by decide) (by decide) (by simp +decide [Env.get, bdParams, ctxEnv])
      (fun htg => ?_) (fun htg => ?_)
    swap
    · rw [if_neg (show ¬ (h.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg)]
      exact specR_returnI _ (optW none) (by simp [optWG]; rfl)
        (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    rw [if_pos (show (h.tag == ETag.forallE) = true by simp [htg, ETag.forallE])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv bdH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, bdParams, ctxEnv]) ?_
    refine specR_viewP h (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
      (fun v P hv htn _ => ?_)
    have h6 : v.tagN = 6 := by rw [htn, htg]; rfl
    obtain ⟨ty, b, rfl⟩ : ∃ ty b, v = .forallE ty b := by
      cases v <;> simp [ENodeView.tagN] at h6 ⊢
    have hvb : s.store.viewBind h = some (ty, b) := viewBind_of_view_forallE (by rw [htg]; rfl) hv
    refine specR_runBind (by rw [viewBind_run, hvb]) ?_
    dsimp only
    refine specR_loadI' bdA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW ty) [Enc.idxW b] []) ?_
    refine specR_loadI' bdB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW b) [] []) ?_
    refine specR_dropM ?_

    have hne : BitVec.ofNat 64 (k + 1) ≠ 0 := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, bdParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_callO bdR fBd bdParams [.op .sub [vv bdK, .const 1], vv bdB] bdBody
      [BitVec.ofNat 64 k, Enc.idxW b] (by decide) rfl (by decide) hcb
      ⟨by simp +decide [sev, Env.get, bdParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, by simp, trivial⟩
      (ih b s (by omega))


def ljRel (C : Ctx) (H : List (BitVec 64)) : Option (Nat × Nat) → BitVec 64 → Prop
  | none, w => w = 0
  | some (k, j), w => ∃ o, w = cellA C o ∧ H[o]? = some (BitVec.ofNat 64 k) ∧ H[o + 1]? = some (BitVec.ofNat 64 j) ∧
      j < k ∧ k < 2 ^ 63

def PostLJ (C : Ctx) (r : Option (Nat × Nat)) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ ljRel C H' r w ∧ SR (ctxH C H') s' st

theorem postLJ_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostLJ C a w s' st → PostLJ C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', h1, h2, h3⟩ => ⟨H', h1, h2, sr_of_eq h3 rfl rfl rfl rfl⟩

theorem lj_spec (C : Ctx) (hok : CtxOK C)
    (hcl : C.code.lookup fLj = some (ljParams.map (fun p => (p, ShapeHOL.one)), ljBody C, .one)) :
    ∀ F k (h : EIdx) (s : AState), k + F < 2 ^ 63 →
      SpecR (σ := σ) (Pre C s (ljParams.zip [BitVec.ofNat 64 F, BitVec.ofNat 64 k, Enc.idxW h])) (ljBody C) s
        (lamProj? F k h) (PostLJ C) := by
  intro F
  induction F with
  | zero =>
    intro k h s _
    refine specR_prologue (postLJ_locals C) (Knot.params_none C ljLocals ljParams _ (by decide) (by decide)) ?_
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get, ljParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
  | succ F ih =>
    intro k h s hk
    refine specR_prologue (postLJ_locals C) (Knot.params_none C ljLocals ljParams _ (by decide) (by decide)) ?_
    have hne : BitVec.ofNat 64 (F + 1) ≠ 0 := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ljParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
    rw [lamProj?]
    refine Knot.specR_tagIteV ljH h 5 (by decide) (by decide) (by simp +decide [Env.get, ljParams, ctxEnv])
      (fun htg => ?_) (fun htg => ?_)
    · rw [if_pos (show (h.tag == ETag.lam) = true by simp [htg, ETag.lam])]
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
      refine specR_assignI lDh (vv ljH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, ljParams, ctxEnv]) ?_
      refine specR_viewP h (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
        (fun v P hv htn _ => ?_)
      have h5 : v.tagN = 5 := by rw [htn, htg]; rfl
      obtain ⟨ty, b, rfl⟩ : ∃ ty b, v = .lam ty b := by cases v <;> simp [ENodeView.tagN] at h5 ⊢
      have hvb : s.store.viewBind h = some (ty, b) := viewBind_of_view_lam (by rw [htg]; rfl) hv
      refine specR_runBind (by rw [viewBind_run, hvb]) ?_
      dsimp only
      refine specR_loadI' ljB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      refine specR_congr (m' := lamProj? F (k + 1) b >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH ljR fLj ljParams [.op .sub [vv ljF, .const 1], .op .add [vv ljK, .const 1], vv ljB] (ljBody C)
        [BitVec.ofNat 64 F, BitVec.ofNat 64 (k + 1), Enc.idxW b] (by decide) rfl (by decide) hcl
        ⟨by simp +decide [sev, Env.get, ljParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _,
          by simp +decide [sev, Env.get, ljParams, ctxEnv]; exact word_add1_eq k, by simp, trivial⟩
        (PostLJ C) (fun r_ w _ H' => ljRel C H' r_ w) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ljParams _ rfl hlk) (ih (k + 1) b s (by omega)))
        (fun r w s1 H1 hp1 hw => ?_)
      exact specR_returnI _ w (by simp) (fun t ht => ⟨H1, hp1, hw, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    rw [if_neg (show ¬ (h.tag == ETag.lam) = true by simpa [ETag.lam] using htg)]
    refine Knot.specR_tagIteV ljH h 0 (by decide) (by decide) (by simp +decide [Env.get, ljParams, ctxEnv])
      (fun htb => ?_) (fun htb => ?_)
    swap
    · rw [if_neg (show ¬ (h.tag == ETag.bvar) = true by simpa [ETag.bvar] using htb)]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    rw [if_pos (show (h.tag == ETag.bvar) = true by simp [htb, ETag.bvar])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv ljH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, ljParams, ctxEnv]) ?_
    refine specR_viewP h (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
      (fun v P hv htn hl => ?_)
    have h0 : v.tagN = 0 := by rw [htn, htb]; rfl
    obtain ⟨i, rfl⟩ : ∃ i, v = .bvar i := by cases v <;> simp [ENodeView.tagN] at h0 ⊢
    have hvb : s.store.viewBVar h = some i := by rw [viewBVar_bind _ _ (by rw [htb]; rfl), hv]; rfl
    refine specR_runBind (show ConRon.Arena.viewBVar h s = .ok (some i, s) by
      show Except.ok (s.store.viewBVar h, s) = _; rw [hvb]) ?_
    dsimp only
    have er : encEView (.bvar i) = limbs i := rfl
    have hl58 : (limbs i).length < 2 ^ 61 := by rw [← er]; exact hl
    rcases (by omega : (limbs i).length = 0 ∨ (limbs i).length = 1 ∨ 2 ≤ (limbs i).length) with hz | h1 | h2
    · have hi0 : i = 0 := by have := (limbs_length_lt_iff i 0).mp (by omega); simpa using this
      subst hi0
      have hi64 : (0 : Nat) < 2 ^ 64 := by decide
      refine specR_ifI _ 1 (by simp [sev, er, hz, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_assignI ljJ (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
      have hkw : BitVec.ofNat 64 0 < BitVec.ofNat 64 k ↔ 0 < k := by
        rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt (by omega)]
      by_cases hjk : 0 < k
      · refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ljParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hkw, hjk]) (fun _ => ?_) (fun h => absurd h (by decide))
        simp only [hjk, ↓reduceIte]
        refine specR_alloc2I hok ljW (vv ljK) (vv ljJ) (BitVec.ofNat 64 k) (BitVec.ofNat 64 0) (by decide)
          (fun _ => by simp +decide [Env.get, ljParams, ctxEnv]) (fun _ => by simp) (fun H2 ws hp2 hws => ?_)
        refine specR_returnI (vv ljW) (cellA C H2.length) (by simp +decide <;> rfl) (fun t ht => ?_)
        exact ⟨_, hp2.trans (img2_prefix H2 ws _ _ hws), ⟨H2.length, rfl, (img2_get H2 ws _ _ hws).1, (img2_get H2 ws _ _ hws).2, hjk, by omega⟩,
          sr_of_eq ht.sr rfl rfl rfl rfl⟩
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ljParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hkw, hjk]) (fun h => absurd rfl h) (fun _ => ?_)
      simp only [hjk, ↓reduceIte]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    · have hi64 : i < 2 ^ 64 := by have := (limbs_length_lt_iff i 1).mp (by omega); simpa using this
      have h1w : BitVec.ofNat 64 (limbs i).length ≠ 0#64 := by rw [h1]; decide
      refine specR_ifI _ 0 (by simp [sev, er, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact h1w) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp [sev, er, h1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      have hx0 : (limbs i)[0]'(by omega) = BitVec.ofNat 64 i := by
        rw [limbs_getElem i 0 (by omega)]; simp [Nat.mod_eq_of_lt hi64]
      refine specR_loadI' ljJ (vv lRp) P (P + BitVec.ofNat 64 (8 * 0)) (BitVec.ofNat 64 i) (by decide) (by simp) (by simp)
        (by have := wordsAt_get P (limbs i) 0 (by omega) []; rw [hx0] at this; simpa [er] using this) ?_
      have hkw : BitVec.ofNat 64 i < BitVec.ofNat 64 k ↔ i < k := by
        rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt (by omega)]
      by_cases hjk : i < k
      · refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ljParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hkw, hjk]) (fun _ => ?_) (fun h => absurd h (by decide))
        simp only [hjk, ↓reduceIte]
        refine specR_alloc2I hok ljW (vv ljK) (vv ljJ) (BitVec.ofNat 64 k) (BitVec.ofNat 64 i) (by decide)
          (fun _ => by simp +decide [Env.get, ljParams, ctxEnv]) (fun _ => by simp) (fun H2 ws hp2 hws => ?_)
        refine specR_returnI (vv ljW) (cellA C H2.length) (by simp +decide <;> rfl) (fun t ht => ?_)
        exact ⟨_, hp2.trans (img2_prefix H2 ws _ _ hws), ⟨H2.length, rfl, (img2_get H2 ws _ _ hws).1, (img2_get H2 ws _ _ hws).2, hjk, by omega⟩,
          sr_of_eq ht.sr rfl rfl rfl rfl⟩
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ljParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hkw, hjk]) (fun h => absurd rfl h) (fun _ => ?_)
      simp only [hjk, ↓reduceIte]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    · have h1w : BitVec.ofNat 64 (limbs i).length ≠ 0#64 := by
        intro h0; have := congrArg BitVec.toNat h0; simp at this; omega
      have h2w : BitVec.ofNat 64 (limbs i).length ≠ 1#64 := by
        intro h0; have := congrArg BitVec.toNat h0; simp at this; omega
      refine specR_ifI _ 0 (by simp [sev, er, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact h1w) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp [sev, er, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact h2w) (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_hangI


end

end ConPanqueque.T.WC
