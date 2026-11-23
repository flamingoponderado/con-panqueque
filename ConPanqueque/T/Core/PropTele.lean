import ConPanqueque.T.Core.DefeqBody
import ConPanqueque.T.Core.StructEta
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

def uwF := ofString "puw_uwf"
def uwN := ofString "puw_uwn"
def uwE := ofString "puw_uwe"
def uwH := ofString "puw_uwh"
def uwC := ofString "puw_uwc"
def uwP := ofString "puw_uwp"
def uwQ := ofString "puw_uwq"
def uwK := ofString "puw_uwk"
def uwV := ofString "puw_uwv"
def uwL := ofString "puw_uwl"
def uwKk := ofString "puw_uwkk"
def uwJ := ofString "puw_uwj"
def uwX := ofString "puw_uwx"
def uwLa := ofString "puw_uwla"
def uwA := ofString "puw_uwa"
def uwR := ofString "puw_uwr"
def fUw := ofString "unwrapIdDefs"

@[simp] theorem puw_uwF_ne_uwN : uwF ≠ uwN := by decide
@[simp] theorem puw_uwF_ne_uwE : uwF ≠ uwE := by decide
@[simp] theorem puw_uwF_ne_uwH : uwF ≠ uwH := by decide
@[simp] theorem puw_uwF_ne_uwC : uwF ≠ uwC := by decide
@[simp] theorem puw_uwF_ne_uwP : uwF ≠ uwP := by decide
@[simp] theorem puw_uwF_ne_uwQ : uwF ≠ uwQ := by decide
@[simp] theorem puw_uwF_ne_uwK : uwF ≠ uwK := by decide
@[simp] theorem puw_uwF_ne_uwV : uwF ≠ uwV := by decide
@[simp] theorem puw_uwF_ne_uwL : uwF ≠ uwL := by decide
@[simp] theorem puw_uwF_ne_uwKk : uwF ≠ uwKk := by decide
@[simp] theorem puw_uwF_ne_uwJ : uwF ≠ uwJ := by decide
@[simp] theorem puw_uwF_ne_uwX : uwF ≠ uwX := by decide
@[simp] theorem puw_uwF_ne_uwLa : uwF ≠ uwLa := by decide
@[simp] theorem puw_uwF_ne_uwA : uwF ≠ uwA := by decide
@[simp] theorem puw_uwF_ne_uwR : uwF ≠ uwR := by decide
@[simp] theorem puw_uwF_ne_lFl : uwF ≠ lFl := by decide
@[simp] theorem puw_lFl_ne_uwF : lFl ≠ uwF := by decide
@[simp] theorem puw_uwF_ne_lDh : uwF ≠ lDh := by decide
@[simp] theorem puw_lDh_ne_uwF : lDh ≠ uwF := by decide
@[simp] theorem puw_uwF_ne_lDt : uwF ≠ lDt := by decide
@[simp] theorem puw_lDt_ne_uwF : lDt ≠ uwF := by decide
@[simp] theorem puw_uwF_ne_lDg : uwF ≠ lDg := by decide
@[simp] theorem puw_lDg_ne_uwF : lDg ≠ uwF := by decide
@[simp] theorem puw_uwF_ne_lDi : uwF ≠ lDi := by decide
@[simp] theorem puw_lDi_ne_uwF : lDi ≠ uwF := by decide
@[simp] theorem puw_uwF_ne_lRp : uwF ≠ lRp := by decide
@[simp] theorem puw_lRp_ne_uwF : lRp ≠ uwF := by decide
@[simp] theorem puw_uwF_ne_lRn : uwF ≠ lRn := by decide
@[simp] theorem puw_lRn_ne_uwF : lRn ≠ uwF := by decide
@[simp] theorem puw_uwF_ne_lFle : uwF ≠ lFle := by decide
@[simp] theorem puw_lFle_ne_uwF : lFle ≠ uwF := by decide
@[simp] theorem puw_uwF_ne_lKb : uwF ≠ lKb := by decide
@[simp] theorem puw_lKb_ne_uwF : lKb ≠ uwF := by decide
@[simp] theorem puw_uwF_ne_lDir : uwF ≠ lDir := by decide
@[simp] theorem puw_lDir_ne_uwF : lDir ≠ uwF := by decide
@[simp] theorem puw_uwF_ne_lFln : uwF ≠ lFln := by decide
@[simp] theorem puw_lFln_ne_uwF : lFln ≠ uwF := by decide
@[simp] theorem puw_uwF_ne_lFll : uwF ≠ lFll := by decide
@[simp] theorem puw_lFll_ne_uwF : lFll ≠ uwF := by decide
@[simp] theorem puw_uwF_ne_lFls : uwF ≠ lFls := by decide
@[simp] theorem puw_lFls_ne_uwF : lFls ≠ uwF := by decide
@[simp] theorem puw_uwF_ne_kFu : uwF ≠ kFu := by decide
@[simp] theorem puw_kFu_ne_uwF : kFu ≠ uwF := by decide
@[simp] theorem puw_uwF_ne_kD : uwF ≠ kD := by decide
@[simp] theorem puw_kD_ne_uwF : kD ≠ uwF := by decide
@[simp] theorem puw_uwN_ne_uwF : uwN ≠ uwF := by decide
@[simp] theorem puw_uwN_ne_uwE : uwN ≠ uwE := by decide
@[simp] theorem puw_uwN_ne_uwH : uwN ≠ uwH := by decide
@[simp] theorem puw_uwN_ne_uwC : uwN ≠ uwC := by decide
@[simp] theorem puw_uwN_ne_uwP : uwN ≠ uwP := by decide
@[simp] theorem puw_uwN_ne_uwQ : uwN ≠ uwQ := by decide
@[simp] theorem puw_uwN_ne_uwK : uwN ≠ uwK := by decide
@[simp] theorem puw_uwN_ne_uwV : uwN ≠ uwV := by decide
@[simp] theorem puw_uwN_ne_uwL : uwN ≠ uwL := by decide
@[simp] theorem puw_uwN_ne_uwKk : uwN ≠ uwKk := by decide
@[simp] theorem puw_uwN_ne_uwJ : uwN ≠ uwJ := by decide
@[simp] theorem puw_uwN_ne_uwX : uwN ≠ uwX := by decide
@[simp] theorem puw_uwN_ne_uwLa : uwN ≠ uwLa := by decide
@[simp] theorem puw_uwN_ne_uwA : uwN ≠ uwA := by decide
@[simp] theorem puw_uwN_ne_uwR : uwN ≠ uwR := by decide
@[simp] theorem puw_uwN_ne_lFl : uwN ≠ lFl := by decide
@[simp] theorem puw_lFl_ne_uwN : lFl ≠ uwN := by decide
@[simp] theorem puw_uwN_ne_lDh : uwN ≠ lDh := by decide
@[simp] theorem puw_lDh_ne_uwN : lDh ≠ uwN := by decide
@[simp] theorem puw_uwN_ne_lDt : uwN ≠ lDt := by decide
@[simp] theorem puw_lDt_ne_uwN : lDt ≠ uwN := by decide
@[simp] theorem puw_uwN_ne_lDg : uwN ≠ lDg := by decide
@[simp] theorem puw_lDg_ne_uwN : lDg ≠ uwN := by decide
@[simp] theorem puw_uwN_ne_lDi : uwN ≠ lDi := by decide
@[simp] theorem puw_lDi_ne_uwN : lDi ≠ uwN := by decide
@[simp] theorem puw_uwN_ne_lRp : uwN ≠ lRp := by decide
@[simp] theorem puw_lRp_ne_uwN : lRp ≠ uwN := by decide
@[simp] theorem puw_uwN_ne_lRn : uwN ≠ lRn := by decide
@[simp] theorem puw_lRn_ne_uwN : lRn ≠ uwN := by decide
@[simp] theorem puw_uwN_ne_lFle : uwN ≠ lFle := by decide
@[simp] theorem puw_lFle_ne_uwN : lFle ≠ uwN := by decide
@[simp] theorem puw_uwN_ne_lKb : uwN ≠ lKb := by decide
@[simp] theorem puw_lKb_ne_uwN : lKb ≠ uwN := by decide
@[simp] theorem puw_uwN_ne_lDir : uwN ≠ lDir := by decide
@[simp] theorem puw_lDir_ne_uwN : lDir ≠ uwN := by decide
@[simp] theorem puw_uwN_ne_lFln : uwN ≠ lFln := by decide
@[simp] theorem puw_lFln_ne_uwN : lFln ≠ uwN := by decide
@[simp] theorem puw_uwN_ne_lFll : uwN ≠ lFll := by decide
@[simp] theorem puw_lFll_ne_uwN : lFll ≠ uwN := by decide
@[simp] theorem puw_uwN_ne_lFls : uwN ≠ lFls := by decide
@[simp] theorem puw_lFls_ne_uwN : lFls ≠ uwN := by decide
@[simp] theorem puw_uwN_ne_kFu : uwN ≠ kFu := by decide
@[simp] theorem puw_kFu_ne_uwN : kFu ≠ uwN := by decide
@[simp] theorem puw_uwN_ne_kD : uwN ≠ kD := by decide
@[simp] theorem puw_kD_ne_uwN : kD ≠ uwN := by decide
@[simp] theorem puw_uwE_ne_uwF : uwE ≠ uwF := by decide
@[simp] theorem puw_uwE_ne_uwN : uwE ≠ uwN := by decide
@[simp] theorem puw_uwE_ne_uwH : uwE ≠ uwH := by decide
@[simp] theorem puw_uwE_ne_uwC : uwE ≠ uwC := by decide
@[simp] theorem puw_uwE_ne_uwP : uwE ≠ uwP := by decide
@[simp] theorem puw_uwE_ne_uwQ : uwE ≠ uwQ := by decide
@[simp] theorem puw_uwE_ne_uwK : uwE ≠ uwK := by decide
@[simp] theorem puw_uwE_ne_uwV : uwE ≠ uwV := by decide
@[simp] theorem puw_uwE_ne_uwL : uwE ≠ uwL := by decide
@[simp] theorem puw_uwE_ne_uwKk : uwE ≠ uwKk := by decide
@[simp] theorem puw_uwE_ne_uwJ : uwE ≠ uwJ := by decide
@[simp] theorem puw_uwE_ne_uwX : uwE ≠ uwX := by decide
@[simp] theorem puw_uwE_ne_uwLa : uwE ≠ uwLa := by decide
@[simp] theorem puw_uwE_ne_uwA : uwE ≠ uwA := by decide
@[simp] theorem puw_uwE_ne_uwR : uwE ≠ uwR := by decide
@[simp] theorem puw_uwE_ne_lFl : uwE ≠ lFl := by decide
@[simp] theorem puw_lFl_ne_uwE : lFl ≠ uwE := by decide
@[simp] theorem puw_uwE_ne_lDh : uwE ≠ lDh := by decide
@[simp] theorem puw_lDh_ne_uwE : lDh ≠ uwE := by decide
@[simp] theorem puw_uwE_ne_lDt : uwE ≠ lDt := by decide
@[simp] theorem puw_lDt_ne_uwE : lDt ≠ uwE := by decide
@[simp] theorem puw_uwE_ne_lDg : uwE ≠ lDg := by decide
@[simp] theorem puw_lDg_ne_uwE : lDg ≠ uwE := by decide
@[simp] theorem puw_uwE_ne_lDi : uwE ≠ lDi := by decide
@[simp] theorem puw_lDi_ne_uwE : lDi ≠ uwE := by decide
@[simp] theorem puw_uwE_ne_lRp : uwE ≠ lRp := by decide
@[simp] theorem puw_lRp_ne_uwE : lRp ≠ uwE := by decide
@[simp] theorem puw_uwE_ne_lRn : uwE ≠ lRn := by decide
@[simp] theorem puw_lRn_ne_uwE : lRn ≠ uwE := by decide
@[simp] theorem puw_uwE_ne_lFle : uwE ≠ lFle := by decide
@[simp] theorem puw_lFle_ne_uwE : lFle ≠ uwE := by decide
@[simp] theorem puw_uwE_ne_lKb : uwE ≠ lKb := by decide
@[simp] theorem puw_lKb_ne_uwE : lKb ≠ uwE := by decide
@[simp] theorem puw_uwE_ne_lDir : uwE ≠ lDir := by decide
@[simp] theorem puw_lDir_ne_uwE : lDir ≠ uwE := by decide
@[simp] theorem puw_uwE_ne_lFln : uwE ≠ lFln := by decide
@[simp] theorem puw_lFln_ne_uwE : lFln ≠ uwE := by decide
@[simp] theorem puw_uwE_ne_lFll : uwE ≠ lFll := by decide
@[simp] theorem puw_lFll_ne_uwE : lFll ≠ uwE := by decide
@[simp] theorem puw_uwE_ne_lFls : uwE ≠ lFls := by decide
@[simp] theorem puw_lFls_ne_uwE : lFls ≠ uwE := by decide
@[simp] theorem puw_uwE_ne_kFu : uwE ≠ kFu := by decide
@[simp] theorem puw_kFu_ne_uwE : kFu ≠ uwE := by decide
@[simp] theorem puw_uwE_ne_kD : uwE ≠ kD := by decide
@[simp] theorem puw_kD_ne_uwE : kD ≠ uwE := by decide
@[simp] theorem puw_uwH_ne_uwF : uwH ≠ uwF := by decide
@[simp] theorem puw_uwH_ne_uwN : uwH ≠ uwN := by decide
@[simp] theorem puw_uwH_ne_uwE : uwH ≠ uwE := by decide
@[simp] theorem puw_uwH_ne_uwC : uwH ≠ uwC := by decide
@[simp] theorem puw_uwH_ne_uwP : uwH ≠ uwP := by decide
@[simp] theorem puw_uwH_ne_uwQ : uwH ≠ uwQ := by decide
@[simp] theorem puw_uwH_ne_uwK : uwH ≠ uwK := by decide
@[simp] theorem puw_uwH_ne_uwV : uwH ≠ uwV := by decide
@[simp] theorem puw_uwH_ne_uwL : uwH ≠ uwL := by decide
@[simp] theorem puw_uwH_ne_uwKk : uwH ≠ uwKk := by decide
@[simp] theorem puw_uwH_ne_uwJ : uwH ≠ uwJ := by decide
@[simp] theorem puw_uwH_ne_uwX : uwH ≠ uwX := by decide
@[simp] theorem puw_uwH_ne_uwLa : uwH ≠ uwLa := by decide
@[simp] theorem puw_uwH_ne_uwA : uwH ≠ uwA := by decide
@[simp] theorem puw_uwH_ne_uwR : uwH ≠ uwR := by decide
@[simp] theorem puw_uwH_ne_lFl : uwH ≠ lFl := by decide
@[simp] theorem puw_lFl_ne_uwH : lFl ≠ uwH := by decide
@[simp] theorem puw_uwH_ne_lDh : uwH ≠ lDh := by decide
@[simp] theorem puw_lDh_ne_uwH : lDh ≠ uwH := by decide
@[simp] theorem puw_uwH_ne_lDt : uwH ≠ lDt := by decide
@[simp] theorem puw_lDt_ne_uwH : lDt ≠ uwH := by decide
@[simp] theorem puw_uwH_ne_lDg : uwH ≠ lDg := by decide
@[simp] theorem puw_lDg_ne_uwH : lDg ≠ uwH := by decide
@[simp] theorem puw_uwH_ne_lDi : uwH ≠ lDi := by decide
@[simp] theorem puw_lDi_ne_uwH : lDi ≠ uwH := by decide
@[simp] theorem puw_uwH_ne_lRp : uwH ≠ lRp := by decide
@[simp] theorem puw_lRp_ne_uwH : lRp ≠ uwH := by decide
@[simp] theorem puw_uwH_ne_lRn : uwH ≠ lRn := by decide
@[simp] theorem puw_lRn_ne_uwH : lRn ≠ uwH := by decide
@[simp] theorem puw_uwH_ne_lFle : uwH ≠ lFle := by decide
@[simp] theorem puw_lFle_ne_uwH : lFle ≠ uwH := by decide
@[simp] theorem puw_uwH_ne_lKb : uwH ≠ lKb := by decide
@[simp] theorem puw_lKb_ne_uwH : lKb ≠ uwH := by decide
@[simp] theorem puw_uwH_ne_lDir : uwH ≠ lDir := by decide
@[simp] theorem puw_lDir_ne_uwH : lDir ≠ uwH := by decide
@[simp] theorem puw_uwH_ne_lFln : uwH ≠ lFln := by decide
@[simp] theorem puw_lFln_ne_uwH : lFln ≠ uwH := by decide
@[simp] theorem puw_uwH_ne_lFll : uwH ≠ lFll := by decide
@[simp] theorem puw_lFll_ne_uwH : lFll ≠ uwH := by decide
@[simp] theorem puw_uwH_ne_lFls : uwH ≠ lFls := by decide
@[simp] theorem puw_lFls_ne_uwH : lFls ≠ uwH := by decide
@[simp] theorem puw_uwH_ne_kFu : uwH ≠ kFu := by decide
@[simp] theorem puw_kFu_ne_uwH : kFu ≠ uwH := by decide
@[simp] theorem puw_uwH_ne_kD : uwH ≠ kD := by decide
@[simp] theorem puw_kD_ne_uwH : kD ≠ uwH := by decide
@[simp] theorem puw_uwC_ne_uwF : uwC ≠ uwF := by decide
@[simp] theorem puw_uwC_ne_uwN : uwC ≠ uwN := by decide
@[simp] theorem puw_uwC_ne_uwE : uwC ≠ uwE := by decide
@[simp] theorem puw_uwC_ne_uwH : uwC ≠ uwH := by decide
@[simp] theorem puw_uwC_ne_uwP : uwC ≠ uwP := by decide
@[simp] theorem puw_uwC_ne_uwQ : uwC ≠ uwQ := by decide
@[simp] theorem puw_uwC_ne_uwK : uwC ≠ uwK := by decide
@[simp] theorem puw_uwC_ne_uwV : uwC ≠ uwV := by decide
@[simp] theorem puw_uwC_ne_uwL : uwC ≠ uwL := by decide
@[simp] theorem puw_uwC_ne_uwKk : uwC ≠ uwKk := by decide
@[simp] theorem puw_uwC_ne_uwJ : uwC ≠ uwJ := by decide
@[simp] theorem puw_uwC_ne_uwX : uwC ≠ uwX := by decide
@[simp] theorem puw_uwC_ne_uwLa : uwC ≠ uwLa := by decide
@[simp] theorem puw_uwC_ne_uwA : uwC ≠ uwA := by decide
@[simp] theorem puw_uwC_ne_uwR : uwC ≠ uwR := by decide
@[simp] theorem puw_uwC_ne_lFl : uwC ≠ lFl := by decide
@[simp] theorem puw_lFl_ne_uwC : lFl ≠ uwC := by decide
@[simp] theorem puw_uwC_ne_lDh : uwC ≠ lDh := by decide
@[simp] theorem puw_lDh_ne_uwC : lDh ≠ uwC := by decide
@[simp] theorem puw_uwC_ne_lDt : uwC ≠ lDt := by decide
@[simp] theorem puw_lDt_ne_uwC : lDt ≠ uwC := by decide
@[simp] theorem puw_uwC_ne_lDg : uwC ≠ lDg := by decide
@[simp] theorem puw_lDg_ne_uwC : lDg ≠ uwC := by decide
@[simp] theorem puw_uwC_ne_lDi : uwC ≠ lDi := by decide
@[simp] theorem puw_lDi_ne_uwC : lDi ≠ uwC := by decide
@[simp] theorem puw_uwC_ne_lRp : uwC ≠ lRp := by decide
@[simp] theorem puw_lRp_ne_uwC : lRp ≠ uwC := by decide
@[simp] theorem puw_uwC_ne_lRn : uwC ≠ lRn := by decide
@[simp] theorem puw_lRn_ne_uwC : lRn ≠ uwC := by decide
@[simp] theorem puw_uwC_ne_lFle : uwC ≠ lFle := by decide
@[simp] theorem puw_lFle_ne_uwC : lFle ≠ uwC := by decide
@[simp] theorem puw_uwC_ne_lKb : uwC ≠ lKb := by decide
@[simp] theorem puw_lKb_ne_uwC : lKb ≠ uwC := by decide
@[simp] theorem puw_uwC_ne_lDir : uwC ≠ lDir := by decide
@[simp] theorem puw_lDir_ne_uwC : lDir ≠ uwC := by decide
@[simp] theorem puw_uwC_ne_lFln : uwC ≠ lFln := by decide
@[simp] theorem puw_lFln_ne_uwC : lFln ≠ uwC := by decide
@[simp] theorem puw_uwC_ne_lFll : uwC ≠ lFll := by decide
@[simp] theorem puw_lFll_ne_uwC : lFll ≠ uwC := by decide
@[simp] theorem puw_uwC_ne_lFls : uwC ≠ lFls := by decide
@[simp] theorem puw_lFls_ne_uwC : lFls ≠ uwC := by decide
@[simp] theorem puw_uwC_ne_kFu : uwC ≠ kFu := by decide
@[simp] theorem puw_kFu_ne_uwC : kFu ≠ uwC := by decide
@[simp] theorem puw_uwC_ne_kD : uwC ≠ kD := by decide
@[simp] theorem puw_kD_ne_uwC : kD ≠ uwC := by decide
@[simp] theorem puw_uwP_ne_uwF : uwP ≠ uwF := by decide
@[simp] theorem puw_uwP_ne_uwN : uwP ≠ uwN := by decide
@[simp] theorem puw_uwP_ne_uwE : uwP ≠ uwE := by decide
@[simp] theorem puw_uwP_ne_uwH : uwP ≠ uwH := by decide
@[simp] theorem puw_uwP_ne_uwC : uwP ≠ uwC := by decide
@[simp] theorem puw_uwP_ne_uwQ : uwP ≠ uwQ := by decide
@[simp] theorem puw_uwP_ne_uwK : uwP ≠ uwK := by decide
@[simp] theorem puw_uwP_ne_uwV : uwP ≠ uwV := by decide
@[simp] theorem puw_uwP_ne_uwL : uwP ≠ uwL := by decide
@[simp] theorem puw_uwP_ne_uwKk : uwP ≠ uwKk := by decide
@[simp] theorem puw_uwP_ne_uwJ : uwP ≠ uwJ := by decide
@[simp] theorem puw_uwP_ne_uwX : uwP ≠ uwX := by decide
@[simp] theorem puw_uwP_ne_uwLa : uwP ≠ uwLa := by decide
@[simp] theorem puw_uwP_ne_uwA : uwP ≠ uwA := by decide
@[simp] theorem puw_uwP_ne_uwR : uwP ≠ uwR := by decide
@[simp] theorem puw_uwP_ne_lFl : uwP ≠ lFl := by decide
@[simp] theorem puw_lFl_ne_uwP : lFl ≠ uwP := by decide
@[simp] theorem puw_uwP_ne_lDh : uwP ≠ lDh := by decide
@[simp] theorem puw_lDh_ne_uwP : lDh ≠ uwP := by decide
@[simp] theorem puw_uwP_ne_lDt : uwP ≠ lDt := by decide
@[simp] theorem puw_lDt_ne_uwP : lDt ≠ uwP := by decide
@[simp] theorem puw_uwP_ne_lDg : uwP ≠ lDg := by decide
@[simp] theorem puw_lDg_ne_uwP : lDg ≠ uwP := by decide
@[simp] theorem puw_uwP_ne_lDi : uwP ≠ lDi := by decide
@[simp] theorem puw_lDi_ne_uwP : lDi ≠ uwP := by decide
@[simp] theorem puw_uwP_ne_lRp : uwP ≠ lRp := by decide
@[simp] theorem puw_lRp_ne_uwP : lRp ≠ uwP := by decide
@[simp] theorem puw_uwP_ne_lRn : uwP ≠ lRn := by decide
@[simp] theorem puw_lRn_ne_uwP : lRn ≠ uwP := by decide
@[simp] theorem puw_uwP_ne_lFle : uwP ≠ lFle := by decide
@[simp] theorem puw_lFle_ne_uwP : lFle ≠ uwP := by decide
@[simp] theorem puw_uwP_ne_lKb : uwP ≠ lKb := by decide
@[simp] theorem puw_lKb_ne_uwP : lKb ≠ uwP := by decide
@[simp] theorem puw_uwP_ne_lDir : uwP ≠ lDir := by decide
@[simp] theorem puw_lDir_ne_uwP : lDir ≠ uwP := by decide
@[simp] theorem puw_uwP_ne_lFln : uwP ≠ lFln := by decide
@[simp] theorem puw_lFln_ne_uwP : lFln ≠ uwP := by decide
@[simp] theorem puw_uwP_ne_lFll : uwP ≠ lFll := by decide
@[simp] theorem puw_lFll_ne_uwP : lFll ≠ uwP := by decide
@[simp] theorem puw_uwP_ne_lFls : uwP ≠ lFls := by decide
@[simp] theorem puw_lFls_ne_uwP : lFls ≠ uwP := by decide
@[simp] theorem puw_uwP_ne_kFu : uwP ≠ kFu := by decide
@[simp] theorem puw_kFu_ne_uwP : kFu ≠ uwP := by decide
@[simp] theorem puw_uwP_ne_kD : uwP ≠ kD := by decide
@[simp] theorem puw_kD_ne_uwP : kD ≠ uwP := by decide
@[simp] theorem puw_uwQ_ne_uwF : uwQ ≠ uwF := by decide
@[simp] theorem puw_uwQ_ne_uwN : uwQ ≠ uwN := by decide
@[simp] theorem puw_uwQ_ne_uwE : uwQ ≠ uwE := by decide
@[simp] theorem puw_uwQ_ne_uwH : uwQ ≠ uwH := by decide
@[simp] theorem puw_uwQ_ne_uwC : uwQ ≠ uwC := by decide
@[simp] theorem puw_uwQ_ne_uwP : uwQ ≠ uwP := by decide
@[simp] theorem puw_uwQ_ne_uwK : uwQ ≠ uwK := by decide
@[simp] theorem puw_uwQ_ne_uwV : uwQ ≠ uwV := by decide
@[simp] theorem puw_uwQ_ne_uwL : uwQ ≠ uwL := by decide
@[simp] theorem puw_uwQ_ne_uwKk : uwQ ≠ uwKk := by decide
@[simp] theorem puw_uwQ_ne_uwJ : uwQ ≠ uwJ := by decide
@[simp] theorem puw_uwQ_ne_uwX : uwQ ≠ uwX := by decide
@[simp] theorem puw_uwQ_ne_uwLa : uwQ ≠ uwLa := by decide
@[simp] theorem puw_uwQ_ne_uwA : uwQ ≠ uwA := by decide
@[simp] theorem puw_uwQ_ne_uwR : uwQ ≠ uwR := by decide
@[simp] theorem puw_uwQ_ne_lFl : uwQ ≠ lFl := by decide
@[simp] theorem puw_lFl_ne_uwQ : lFl ≠ uwQ := by decide
@[simp] theorem puw_uwQ_ne_lDh : uwQ ≠ lDh := by decide
@[simp] theorem puw_lDh_ne_uwQ : lDh ≠ uwQ := by decide
@[simp] theorem puw_uwQ_ne_lDt : uwQ ≠ lDt := by decide
@[simp] theorem puw_lDt_ne_uwQ : lDt ≠ uwQ := by decide
@[simp] theorem puw_uwQ_ne_lDg : uwQ ≠ lDg := by decide
@[simp] theorem puw_lDg_ne_uwQ : lDg ≠ uwQ := by decide
@[simp] theorem puw_uwQ_ne_lDi : uwQ ≠ lDi := by decide
@[simp] theorem puw_lDi_ne_uwQ : lDi ≠ uwQ := by decide
@[simp] theorem puw_uwQ_ne_lRp : uwQ ≠ lRp := by decide
@[simp] theorem puw_lRp_ne_uwQ : lRp ≠ uwQ := by decide
@[simp] theorem puw_uwQ_ne_lRn : uwQ ≠ lRn := by decide
@[simp] theorem puw_lRn_ne_uwQ : lRn ≠ uwQ := by decide
@[simp] theorem puw_uwQ_ne_lFle : uwQ ≠ lFle := by decide
@[simp] theorem puw_lFle_ne_uwQ : lFle ≠ uwQ := by decide
@[simp] theorem puw_uwQ_ne_lKb : uwQ ≠ lKb := by decide
@[simp] theorem puw_lKb_ne_uwQ : lKb ≠ uwQ := by decide
@[simp] theorem puw_uwQ_ne_lDir : uwQ ≠ lDir := by decide
@[simp] theorem puw_lDir_ne_uwQ : lDir ≠ uwQ := by decide
@[simp] theorem puw_uwQ_ne_lFln : uwQ ≠ lFln := by decide
@[simp] theorem puw_lFln_ne_uwQ : lFln ≠ uwQ := by decide
@[simp] theorem puw_uwQ_ne_lFll : uwQ ≠ lFll := by decide
@[simp] theorem puw_lFll_ne_uwQ : lFll ≠ uwQ := by decide
@[simp] theorem puw_uwQ_ne_lFls : uwQ ≠ lFls := by decide
@[simp] theorem puw_lFls_ne_uwQ : lFls ≠ uwQ := by decide
@[simp] theorem puw_uwQ_ne_kFu : uwQ ≠ kFu := by decide
@[simp] theorem puw_kFu_ne_uwQ : kFu ≠ uwQ := by decide
@[simp] theorem puw_uwQ_ne_kD : uwQ ≠ kD := by decide
@[simp] theorem puw_kD_ne_uwQ : kD ≠ uwQ := by decide
@[simp] theorem puw_uwK_ne_uwF : uwK ≠ uwF := by decide
@[simp] theorem puw_uwK_ne_uwN : uwK ≠ uwN := by decide
@[simp] theorem puw_uwK_ne_uwE : uwK ≠ uwE := by decide
@[simp] theorem puw_uwK_ne_uwH : uwK ≠ uwH := by decide
@[simp] theorem puw_uwK_ne_uwC : uwK ≠ uwC := by decide
@[simp] theorem puw_uwK_ne_uwP : uwK ≠ uwP := by decide
@[simp] theorem puw_uwK_ne_uwQ : uwK ≠ uwQ := by decide
@[simp] theorem puw_uwK_ne_uwV : uwK ≠ uwV := by decide
@[simp] theorem puw_uwK_ne_uwL : uwK ≠ uwL := by decide
@[simp] theorem puw_uwK_ne_uwKk : uwK ≠ uwKk := by decide
@[simp] theorem puw_uwK_ne_uwJ : uwK ≠ uwJ := by decide
@[simp] theorem puw_uwK_ne_uwX : uwK ≠ uwX := by decide
@[simp] theorem puw_uwK_ne_uwLa : uwK ≠ uwLa := by decide
@[simp] theorem puw_uwK_ne_uwA : uwK ≠ uwA := by decide
@[simp] theorem puw_uwK_ne_uwR : uwK ≠ uwR := by decide
@[simp] theorem puw_uwK_ne_lFl : uwK ≠ lFl := by decide
@[simp] theorem puw_lFl_ne_uwK : lFl ≠ uwK := by decide
@[simp] theorem puw_uwK_ne_lDh : uwK ≠ lDh := by decide
@[simp] theorem puw_lDh_ne_uwK : lDh ≠ uwK := by decide
@[simp] theorem puw_uwK_ne_lDt : uwK ≠ lDt := by decide
@[simp] theorem puw_lDt_ne_uwK : lDt ≠ uwK := by decide
@[simp] theorem puw_uwK_ne_lDg : uwK ≠ lDg := by decide
@[simp] theorem puw_lDg_ne_uwK : lDg ≠ uwK := by decide
@[simp] theorem puw_uwK_ne_lDi : uwK ≠ lDi := by decide
@[simp] theorem puw_lDi_ne_uwK : lDi ≠ uwK := by decide
@[simp] theorem puw_uwK_ne_lRp : uwK ≠ lRp := by decide
@[simp] theorem puw_lRp_ne_uwK : lRp ≠ uwK := by decide
@[simp] theorem puw_uwK_ne_lRn : uwK ≠ lRn := by decide
@[simp] theorem puw_lRn_ne_uwK : lRn ≠ uwK := by decide
@[simp] theorem puw_uwK_ne_lFle : uwK ≠ lFle := by decide
@[simp] theorem puw_lFle_ne_uwK : lFle ≠ uwK := by decide
@[simp] theorem puw_uwK_ne_lKb : uwK ≠ lKb := by decide
@[simp] theorem puw_lKb_ne_uwK : lKb ≠ uwK := by decide
@[simp] theorem puw_uwK_ne_lDir : uwK ≠ lDir := by decide
@[simp] theorem puw_lDir_ne_uwK : lDir ≠ uwK := by decide
@[simp] theorem puw_uwK_ne_lFln : uwK ≠ lFln := by decide
@[simp] theorem puw_lFln_ne_uwK : lFln ≠ uwK := by decide
@[simp] theorem puw_uwK_ne_lFll : uwK ≠ lFll := by decide
@[simp] theorem puw_lFll_ne_uwK : lFll ≠ uwK := by decide
@[simp] theorem puw_uwK_ne_lFls : uwK ≠ lFls := by decide
@[simp] theorem puw_lFls_ne_uwK : lFls ≠ uwK := by decide
@[simp] theorem puw_uwK_ne_kFu : uwK ≠ kFu := by decide
@[simp] theorem puw_kFu_ne_uwK : kFu ≠ uwK := by decide
@[simp] theorem puw_uwK_ne_kD : uwK ≠ kD := by decide
@[simp] theorem puw_kD_ne_uwK : kD ≠ uwK := by decide
@[simp] theorem puw_uwV_ne_uwF : uwV ≠ uwF := by decide
@[simp] theorem puw_uwV_ne_uwN : uwV ≠ uwN := by decide
@[simp] theorem puw_uwV_ne_uwE : uwV ≠ uwE := by decide
@[simp] theorem puw_uwV_ne_uwH : uwV ≠ uwH := by decide
@[simp] theorem puw_uwV_ne_uwC : uwV ≠ uwC := by decide
@[simp] theorem puw_uwV_ne_uwP : uwV ≠ uwP := by decide
@[simp] theorem puw_uwV_ne_uwQ : uwV ≠ uwQ := by decide
@[simp] theorem puw_uwV_ne_uwK : uwV ≠ uwK := by decide
@[simp] theorem puw_uwV_ne_uwL : uwV ≠ uwL := by decide
@[simp] theorem puw_uwV_ne_uwKk : uwV ≠ uwKk := by decide
@[simp] theorem puw_uwV_ne_uwJ : uwV ≠ uwJ := by decide
@[simp] theorem puw_uwV_ne_uwX : uwV ≠ uwX := by decide
@[simp] theorem puw_uwV_ne_uwLa : uwV ≠ uwLa := by decide
@[simp] theorem puw_uwV_ne_uwA : uwV ≠ uwA := by decide
@[simp] theorem puw_uwV_ne_uwR : uwV ≠ uwR := by decide
@[simp] theorem puw_uwV_ne_lFl : uwV ≠ lFl := by decide
@[simp] theorem puw_lFl_ne_uwV : lFl ≠ uwV := by decide
@[simp] theorem puw_uwV_ne_lDh : uwV ≠ lDh := by decide
@[simp] theorem puw_lDh_ne_uwV : lDh ≠ uwV := by decide
@[simp] theorem puw_uwV_ne_lDt : uwV ≠ lDt := by decide
@[simp] theorem puw_lDt_ne_uwV : lDt ≠ uwV := by decide
@[simp] theorem puw_uwV_ne_lDg : uwV ≠ lDg := by decide
@[simp] theorem puw_lDg_ne_uwV : lDg ≠ uwV := by decide
@[simp] theorem puw_uwV_ne_lDi : uwV ≠ lDi := by decide
@[simp] theorem puw_lDi_ne_uwV : lDi ≠ uwV := by decide
@[simp] theorem puw_uwV_ne_lRp : uwV ≠ lRp := by decide
@[simp] theorem puw_lRp_ne_uwV : lRp ≠ uwV := by decide
@[simp] theorem puw_uwV_ne_lRn : uwV ≠ lRn := by decide
@[simp] theorem puw_lRn_ne_uwV : lRn ≠ uwV := by decide
@[simp] theorem puw_uwV_ne_lFle : uwV ≠ lFle := by decide
@[simp] theorem puw_lFle_ne_uwV : lFle ≠ uwV := by decide
@[simp] theorem puw_uwV_ne_lKb : uwV ≠ lKb := by decide
@[simp] theorem puw_lKb_ne_uwV : lKb ≠ uwV := by decide
@[simp] theorem puw_uwV_ne_lDir : uwV ≠ lDir := by decide
@[simp] theorem puw_lDir_ne_uwV : lDir ≠ uwV := by decide
@[simp] theorem puw_uwV_ne_lFln : uwV ≠ lFln := by decide
@[simp] theorem puw_lFln_ne_uwV : lFln ≠ uwV := by decide
@[simp] theorem puw_uwV_ne_lFll : uwV ≠ lFll := by decide
@[simp] theorem puw_lFll_ne_uwV : lFll ≠ uwV := by decide
@[simp] theorem puw_uwV_ne_lFls : uwV ≠ lFls := by decide
@[simp] theorem puw_lFls_ne_uwV : lFls ≠ uwV := by decide
@[simp] theorem puw_uwV_ne_kFu : uwV ≠ kFu := by decide
@[simp] theorem puw_kFu_ne_uwV : kFu ≠ uwV := by decide
@[simp] theorem puw_uwV_ne_kD : uwV ≠ kD := by decide
@[simp] theorem puw_kD_ne_uwV : kD ≠ uwV := by decide
@[simp] theorem puw_uwL_ne_uwF : uwL ≠ uwF := by decide
@[simp] theorem puw_uwL_ne_uwN : uwL ≠ uwN := by decide
@[simp] theorem puw_uwL_ne_uwE : uwL ≠ uwE := by decide
@[simp] theorem puw_uwL_ne_uwH : uwL ≠ uwH := by decide
@[simp] theorem puw_uwL_ne_uwC : uwL ≠ uwC := by decide
@[simp] theorem puw_uwL_ne_uwP : uwL ≠ uwP := by decide
@[simp] theorem puw_uwL_ne_uwQ : uwL ≠ uwQ := by decide
@[simp] theorem puw_uwL_ne_uwK : uwL ≠ uwK := by decide
@[simp] theorem puw_uwL_ne_uwV : uwL ≠ uwV := by decide
@[simp] theorem puw_uwL_ne_uwKk : uwL ≠ uwKk := by decide
@[simp] theorem puw_uwL_ne_uwJ : uwL ≠ uwJ := by decide
@[simp] theorem puw_uwL_ne_uwX : uwL ≠ uwX := by decide
@[simp] theorem puw_uwL_ne_uwLa : uwL ≠ uwLa := by decide
@[simp] theorem puw_uwL_ne_uwA : uwL ≠ uwA := by decide
@[simp] theorem puw_uwL_ne_uwR : uwL ≠ uwR := by decide
@[simp] theorem puw_uwL_ne_lFl : uwL ≠ lFl := by decide
@[simp] theorem puw_lFl_ne_uwL : lFl ≠ uwL := by decide
@[simp] theorem puw_uwL_ne_lDh : uwL ≠ lDh := by decide
@[simp] theorem puw_lDh_ne_uwL : lDh ≠ uwL := by decide
@[simp] theorem puw_uwL_ne_lDt : uwL ≠ lDt := by decide
@[simp] theorem puw_lDt_ne_uwL : lDt ≠ uwL := by decide
@[simp] theorem puw_uwL_ne_lDg : uwL ≠ lDg := by decide
@[simp] theorem puw_lDg_ne_uwL : lDg ≠ uwL := by decide
@[simp] theorem puw_uwL_ne_lDi : uwL ≠ lDi := by decide
@[simp] theorem puw_lDi_ne_uwL : lDi ≠ uwL := by decide
@[simp] theorem puw_uwL_ne_lRp : uwL ≠ lRp := by decide
@[simp] theorem puw_lRp_ne_uwL : lRp ≠ uwL := by decide
@[simp] theorem puw_uwL_ne_lRn : uwL ≠ lRn := by decide
@[simp] theorem puw_lRn_ne_uwL : lRn ≠ uwL := by decide
@[simp] theorem puw_uwL_ne_lFle : uwL ≠ lFle := by decide
@[simp] theorem puw_lFle_ne_uwL : lFle ≠ uwL := by decide
@[simp] theorem puw_uwL_ne_lKb : uwL ≠ lKb := by decide
@[simp] theorem puw_lKb_ne_uwL : lKb ≠ uwL := by decide
@[simp] theorem puw_uwL_ne_lDir : uwL ≠ lDir := by decide
@[simp] theorem puw_lDir_ne_uwL : lDir ≠ uwL := by decide
@[simp] theorem puw_uwL_ne_lFln : uwL ≠ lFln := by decide
@[simp] theorem puw_lFln_ne_uwL : lFln ≠ uwL := by decide
@[simp] theorem puw_uwL_ne_lFll : uwL ≠ lFll := by decide
@[simp] theorem puw_lFll_ne_uwL : lFll ≠ uwL := by decide
@[simp] theorem puw_uwL_ne_lFls : uwL ≠ lFls := by decide
@[simp] theorem puw_lFls_ne_uwL : lFls ≠ uwL := by decide
@[simp] theorem puw_uwL_ne_kFu : uwL ≠ kFu := by decide
@[simp] theorem puw_kFu_ne_uwL : kFu ≠ uwL := by decide
@[simp] theorem puw_uwL_ne_kD : uwL ≠ kD := by decide
@[simp] theorem puw_kD_ne_uwL : kD ≠ uwL := by decide
@[simp] theorem puw_uwKk_ne_uwF : uwKk ≠ uwF := by decide
@[simp] theorem puw_uwKk_ne_uwN : uwKk ≠ uwN := by decide
@[simp] theorem puw_uwKk_ne_uwE : uwKk ≠ uwE := by decide
@[simp] theorem puw_uwKk_ne_uwH : uwKk ≠ uwH := by decide
@[simp] theorem puw_uwKk_ne_uwC : uwKk ≠ uwC := by decide
@[simp] theorem puw_uwKk_ne_uwP : uwKk ≠ uwP := by decide
@[simp] theorem puw_uwKk_ne_uwQ : uwKk ≠ uwQ := by decide
@[simp] theorem puw_uwKk_ne_uwK : uwKk ≠ uwK := by decide
@[simp] theorem puw_uwKk_ne_uwV : uwKk ≠ uwV := by decide
@[simp] theorem puw_uwKk_ne_uwL : uwKk ≠ uwL := by decide
@[simp] theorem puw_uwKk_ne_uwJ : uwKk ≠ uwJ := by decide
@[simp] theorem puw_uwKk_ne_uwX : uwKk ≠ uwX := by decide
@[simp] theorem puw_uwKk_ne_uwLa : uwKk ≠ uwLa := by decide
@[simp] theorem puw_uwKk_ne_uwA : uwKk ≠ uwA := by decide
@[simp] theorem puw_uwKk_ne_uwR : uwKk ≠ uwR := by decide
@[simp] theorem puw_uwKk_ne_lFl : uwKk ≠ lFl := by decide
@[simp] theorem puw_lFl_ne_uwKk : lFl ≠ uwKk := by decide
@[simp] theorem puw_uwKk_ne_lDh : uwKk ≠ lDh := by decide
@[simp] theorem puw_lDh_ne_uwKk : lDh ≠ uwKk := by decide
@[simp] theorem puw_uwKk_ne_lDt : uwKk ≠ lDt := by decide
@[simp] theorem puw_lDt_ne_uwKk : lDt ≠ uwKk := by decide
@[simp] theorem puw_uwKk_ne_lDg : uwKk ≠ lDg := by decide
@[simp] theorem puw_lDg_ne_uwKk : lDg ≠ uwKk := by decide
@[simp] theorem puw_uwKk_ne_lDi : uwKk ≠ lDi := by decide
@[simp] theorem puw_lDi_ne_uwKk : lDi ≠ uwKk := by decide
@[simp] theorem puw_uwKk_ne_lRp : uwKk ≠ lRp := by decide
@[simp] theorem puw_lRp_ne_uwKk : lRp ≠ uwKk := by decide
@[simp] theorem puw_uwKk_ne_lRn : uwKk ≠ lRn := by decide
@[simp] theorem puw_lRn_ne_uwKk : lRn ≠ uwKk := by decide
@[simp] theorem puw_uwKk_ne_lFle : uwKk ≠ lFle := by decide
@[simp] theorem puw_lFle_ne_uwKk : lFle ≠ uwKk := by decide
@[simp] theorem puw_uwKk_ne_lKb : uwKk ≠ lKb := by decide
@[simp] theorem puw_lKb_ne_uwKk : lKb ≠ uwKk := by decide
@[simp] theorem puw_uwKk_ne_lDir : uwKk ≠ lDir := by decide
@[simp] theorem puw_lDir_ne_uwKk : lDir ≠ uwKk := by decide
@[simp] theorem puw_uwKk_ne_lFln : uwKk ≠ lFln := by decide
@[simp] theorem puw_lFln_ne_uwKk : lFln ≠ uwKk := by decide
@[simp] theorem puw_uwKk_ne_lFll : uwKk ≠ lFll := by decide
@[simp] theorem puw_lFll_ne_uwKk : lFll ≠ uwKk := by decide
@[simp] theorem puw_uwKk_ne_lFls : uwKk ≠ lFls := by decide
@[simp] theorem puw_lFls_ne_uwKk : lFls ≠ uwKk := by decide
@[simp] theorem puw_uwKk_ne_kFu : uwKk ≠ kFu := by decide
@[simp] theorem puw_kFu_ne_uwKk : kFu ≠ uwKk := by decide
@[simp] theorem puw_uwKk_ne_kD : uwKk ≠ kD := by decide
@[simp] theorem puw_kD_ne_uwKk : kD ≠ uwKk := by decide
@[simp] theorem puw_uwJ_ne_uwF : uwJ ≠ uwF := by decide
@[simp] theorem puw_uwJ_ne_uwN : uwJ ≠ uwN := by decide
@[simp] theorem puw_uwJ_ne_uwE : uwJ ≠ uwE := by decide
@[simp] theorem puw_uwJ_ne_uwH : uwJ ≠ uwH := by decide
@[simp] theorem puw_uwJ_ne_uwC : uwJ ≠ uwC := by decide
@[simp] theorem puw_uwJ_ne_uwP : uwJ ≠ uwP := by decide
@[simp] theorem puw_uwJ_ne_uwQ : uwJ ≠ uwQ := by decide
@[simp] theorem puw_uwJ_ne_uwK : uwJ ≠ uwK := by decide
@[simp] theorem puw_uwJ_ne_uwV : uwJ ≠ uwV := by decide
@[simp] theorem puw_uwJ_ne_uwL : uwJ ≠ uwL := by decide
@[simp] theorem puw_uwJ_ne_uwKk : uwJ ≠ uwKk := by decide
@[simp] theorem puw_uwJ_ne_uwX : uwJ ≠ uwX := by decide
@[simp] theorem puw_uwJ_ne_uwLa : uwJ ≠ uwLa := by decide
@[simp] theorem puw_uwJ_ne_uwA : uwJ ≠ uwA := by decide
@[simp] theorem puw_uwJ_ne_uwR : uwJ ≠ uwR := by decide
@[simp] theorem puw_uwJ_ne_lFl : uwJ ≠ lFl := by decide
@[simp] theorem puw_lFl_ne_uwJ : lFl ≠ uwJ := by decide
@[simp] theorem puw_uwJ_ne_lDh : uwJ ≠ lDh := by decide
@[simp] theorem puw_lDh_ne_uwJ : lDh ≠ uwJ := by decide
@[simp] theorem puw_uwJ_ne_lDt : uwJ ≠ lDt := by decide
@[simp] theorem puw_lDt_ne_uwJ : lDt ≠ uwJ := by decide
@[simp] theorem puw_uwJ_ne_lDg : uwJ ≠ lDg := by decide
@[simp] theorem puw_lDg_ne_uwJ : lDg ≠ uwJ := by decide
@[simp] theorem puw_uwJ_ne_lDi : uwJ ≠ lDi := by decide
@[simp] theorem puw_lDi_ne_uwJ : lDi ≠ uwJ := by decide
@[simp] theorem puw_uwJ_ne_lRp : uwJ ≠ lRp := by decide
@[simp] theorem puw_lRp_ne_uwJ : lRp ≠ uwJ := by decide
@[simp] theorem puw_uwJ_ne_lRn : uwJ ≠ lRn := by decide
@[simp] theorem puw_lRn_ne_uwJ : lRn ≠ uwJ := by decide
@[simp] theorem puw_uwJ_ne_lFle : uwJ ≠ lFle := by decide
@[simp] theorem puw_lFle_ne_uwJ : lFle ≠ uwJ := by decide
@[simp] theorem puw_uwJ_ne_lKb : uwJ ≠ lKb := by decide
@[simp] theorem puw_lKb_ne_uwJ : lKb ≠ uwJ := by decide
@[simp] theorem puw_uwJ_ne_lDir : uwJ ≠ lDir := by decide
@[simp] theorem puw_lDir_ne_uwJ : lDir ≠ uwJ := by decide
@[simp] theorem puw_uwJ_ne_lFln : uwJ ≠ lFln := by decide
@[simp] theorem puw_lFln_ne_uwJ : lFln ≠ uwJ := by decide
@[simp] theorem puw_uwJ_ne_lFll : uwJ ≠ lFll := by decide
@[simp] theorem puw_lFll_ne_uwJ : lFll ≠ uwJ := by decide
@[simp] theorem puw_uwJ_ne_lFls : uwJ ≠ lFls := by decide
@[simp] theorem puw_lFls_ne_uwJ : lFls ≠ uwJ := by decide
@[simp] theorem puw_uwJ_ne_kFu : uwJ ≠ kFu := by decide
@[simp] theorem puw_kFu_ne_uwJ : kFu ≠ uwJ := by decide
@[simp] theorem puw_uwJ_ne_kD : uwJ ≠ kD := by decide
@[simp] theorem puw_kD_ne_uwJ : kD ≠ uwJ := by decide
@[simp] theorem puw_uwX_ne_uwF : uwX ≠ uwF := by decide
@[simp] theorem puw_uwX_ne_uwN : uwX ≠ uwN := by decide
@[simp] theorem puw_uwX_ne_uwE : uwX ≠ uwE := by decide
@[simp] theorem puw_uwX_ne_uwH : uwX ≠ uwH := by decide
@[simp] theorem puw_uwX_ne_uwC : uwX ≠ uwC := by decide
@[simp] theorem puw_uwX_ne_uwP : uwX ≠ uwP := by decide
@[simp] theorem puw_uwX_ne_uwQ : uwX ≠ uwQ := by decide
@[simp] theorem puw_uwX_ne_uwK : uwX ≠ uwK := by decide
@[simp] theorem puw_uwX_ne_uwV : uwX ≠ uwV := by decide
@[simp] theorem puw_uwX_ne_uwL : uwX ≠ uwL := by decide
@[simp] theorem puw_uwX_ne_uwKk : uwX ≠ uwKk := by decide
@[simp] theorem puw_uwX_ne_uwJ : uwX ≠ uwJ := by decide
@[simp] theorem puw_uwX_ne_uwLa : uwX ≠ uwLa := by decide
@[simp] theorem puw_uwX_ne_uwA : uwX ≠ uwA := by decide
@[simp] theorem puw_uwX_ne_uwR : uwX ≠ uwR := by decide
@[simp] theorem puw_uwX_ne_lFl : uwX ≠ lFl := by decide
@[simp] theorem puw_lFl_ne_uwX : lFl ≠ uwX := by decide
@[simp] theorem puw_uwX_ne_lDh : uwX ≠ lDh := by decide
@[simp] theorem puw_lDh_ne_uwX : lDh ≠ uwX := by decide
@[simp] theorem puw_uwX_ne_lDt : uwX ≠ lDt := by decide
@[simp] theorem puw_lDt_ne_uwX : lDt ≠ uwX := by decide
@[simp] theorem puw_uwX_ne_lDg : uwX ≠ lDg := by decide
@[simp] theorem puw_lDg_ne_uwX : lDg ≠ uwX := by decide
@[simp] theorem puw_uwX_ne_lDi : uwX ≠ lDi := by decide
@[simp] theorem puw_lDi_ne_uwX : lDi ≠ uwX := by decide
@[simp] theorem puw_uwX_ne_lRp : uwX ≠ lRp := by decide
@[simp] theorem puw_lRp_ne_uwX : lRp ≠ uwX := by decide
@[simp] theorem puw_uwX_ne_lRn : uwX ≠ lRn := by decide
@[simp] theorem puw_lRn_ne_uwX : lRn ≠ uwX := by decide
@[simp] theorem puw_uwX_ne_lFle : uwX ≠ lFle := by decide
@[simp] theorem puw_lFle_ne_uwX : lFle ≠ uwX := by decide
@[simp] theorem puw_uwX_ne_lKb : uwX ≠ lKb := by decide
@[simp] theorem puw_lKb_ne_uwX : lKb ≠ uwX := by decide
@[simp] theorem puw_uwX_ne_lDir : uwX ≠ lDir := by decide
@[simp] theorem puw_lDir_ne_uwX : lDir ≠ uwX := by decide
@[simp] theorem puw_uwX_ne_lFln : uwX ≠ lFln := by decide
@[simp] theorem puw_lFln_ne_uwX : lFln ≠ uwX := by decide
@[simp] theorem puw_uwX_ne_lFll : uwX ≠ lFll := by decide
@[simp] theorem puw_lFll_ne_uwX : lFll ≠ uwX := by decide
@[simp] theorem puw_uwX_ne_lFls : uwX ≠ lFls := by decide
@[simp] theorem puw_lFls_ne_uwX : lFls ≠ uwX := by decide
@[simp] theorem puw_uwX_ne_kFu : uwX ≠ kFu := by decide
@[simp] theorem puw_kFu_ne_uwX : kFu ≠ uwX := by decide
@[simp] theorem puw_uwX_ne_kD : uwX ≠ kD := by decide
@[simp] theorem puw_kD_ne_uwX : kD ≠ uwX := by decide
@[simp] theorem puw_uwLa_ne_uwF : uwLa ≠ uwF := by decide
@[simp] theorem puw_uwLa_ne_uwN : uwLa ≠ uwN := by decide
@[simp] theorem puw_uwLa_ne_uwE : uwLa ≠ uwE := by decide
@[simp] theorem puw_uwLa_ne_uwH : uwLa ≠ uwH := by decide
@[simp] theorem puw_uwLa_ne_uwC : uwLa ≠ uwC := by decide
@[simp] theorem puw_uwLa_ne_uwP : uwLa ≠ uwP := by decide
@[simp] theorem puw_uwLa_ne_uwQ : uwLa ≠ uwQ := by decide
@[simp] theorem puw_uwLa_ne_uwK : uwLa ≠ uwK := by decide
@[simp] theorem puw_uwLa_ne_uwV : uwLa ≠ uwV := by decide
@[simp] theorem puw_uwLa_ne_uwL : uwLa ≠ uwL := by decide
@[simp] theorem puw_uwLa_ne_uwKk : uwLa ≠ uwKk := by decide
@[simp] theorem puw_uwLa_ne_uwJ : uwLa ≠ uwJ := by decide
@[simp] theorem puw_uwLa_ne_uwX : uwLa ≠ uwX := by decide
@[simp] theorem puw_uwLa_ne_uwA : uwLa ≠ uwA := by decide
@[simp] theorem puw_uwLa_ne_uwR : uwLa ≠ uwR := by decide
@[simp] theorem puw_uwLa_ne_lFl : uwLa ≠ lFl := by decide
@[simp] theorem puw_lFl_ne_uwLa : lFl ≠ uwLa := by decide
@[simp] theorem puw_uwLa_ne_lDh : uwLa ≠ lDh := by decide
@[simp] theorem puw_lDh_ne_uwLa : lDh ≠ uwLa := by decide
@[simp] theorem puw_uwLa_ne_lDt : uwLa ≠ lDt := by decide
@[simp] theorem puw_lDt_ne_uwLa : lDt ≠ uwLa := by decide
@[simp] theorem puw_uwLa_ne_lDg : uwLa ≠ lDg := by decide
@[simp] theorem puw_lDg_ne_uwLa : lDg ≠ uwLa := by decide
@[simp] theorem puw_uwLa_ne_lDi : uwLa ≠ lDi := by decide
@[simp] theorem puw_lDi_ne_uwLa : lDi ≠ uwLa := by decide
@[simp] theorem puw_uwLa_ne_lRp : uwLa ≠ lRp := by decide
@[simp] theorem puw_lRp_ne_uwLa : lRp ≠ uwLa := by decide
@[simp] theorem puw_uwLa_ne_lRn : uwLa ≠ lRn := by decide
@[simp] theorem puw_lRn_ne_uwLa : lRn ≠ uwLa := by decide
@[simp] theorem puw_uwLa_ne_lFle : uwLa ≠ lFle := by decide
@[simp] theorem puw_lFle_ne_uwLa : lFle ≠ uwLa := by decide
@[simp] theorem puw_uwLa_ne_lKb : uwLa ≠ lKb := by decide
@[simp] theorem puw_lKb_ne_uwLa : lKb ≠ uwLa := by decide
@[simp] theorem puw_uwLa_ne_lDir : uwLa ≠ lDir := by decide
@[simp] theorem puw_lDir_ne_uwLa : lDir ≠ uwLa := by decide
@[simp] theorem puw_uwLa_ne_lFln : uwLa ≠ lFln := by decide
@[simp] theorem puw_lFln_ne_uwLa : lFln ≠ uwLa := by decide
@[simp] theorem puw_uwLa_ne_lFll : uwLa ≠ lFll := by decide
@[simp] theorem puw_lFll_ne_uwLa : lFll ≠ uwLa := by decide
@[simp] theorem puw_uwLa_ne_lFls : uwLa ≠ lFls := by decide
@[simp] theorem puw_lFls_ne_uwLa : lFls ≠ uwLa := by decide
@[simp] theorem puw_uwLa_ne_kFu : uwLa ≠ kFu := by decide
@[simp] theorem puw_kFu_ne_uwLa : kFu ≠ uwLa := by decide
@[simp] theorem puw_uwLa_ne_kD : uwLa ≠ kD := by decide
@[simp] theorem puw_kD_ne_uwLa : kD ≠ uwLa := by decide
@[simp] theorem puw_uwA_ne_uwF : uwA ≠ uwF := by decide
@[simp] theorem puw_uwA_ne_uwN : uwA ≠ uwN := by decide
@[simp] theorem puw_uwA_ne_uwE : uwA ≠ uwE := by decide
@[simp] theorem puw_uwA_ne_uwH : uwA ≠ uwH := by decide
@[simp] theorem puw_uwA_ne_uwC : uwA ≠ uwC := by decide
@[simp] theorem puw_uwA_ne_uwP : uwA ≠ uwP := by decide
@[simp] theorem puw_uwA_ne_uwQ : uwA ≠ uwQ := by decide
@[simp] theorem puw_uwA_ne_uwK : uwA ≠ uwK := by decide
@[simp] theorem puw_uwA_ne_uwV : uwA ≠ uwV := by decide
@[simp] theorem puw_uwA_ne_uwL : uwA ≠ uwL := by decide
@[simp] theorem puw_uwA_ne_uwKk : uwA ≠ uwKk := by decide
@[simp] theorem puw_uwA_ne_uwJ : uwA ≠ uwJ := by decide
@[simp] theorem puw_uwA_ne_uwX : uwA ≠ uwX := by decide
@[simp] theorem puw_uwA_ne_uwLa : uwA ≠ uwLa := by decide
@[simp] theorem puw_uwA_ne_uwR : uwA ≠ uwR := by decide
@[simp] theorem puw_uwA_ne_lFl : uwA ≠ lFl := by decide
@[simp] theorem puw_lFl_ne_uwA : lFl ≠ uwA := by decide
@[simp] theorem puw_uwA_ne_lDh : uwA ≠ lDh := by decide
@[simp] theorem puw_lDh_ne_uwA : lDh ≠ uwA := by decide
@[simp] theorem puw_uwA_ne_lDt : uwA ≠ lDt := by decide
@[simp] theorem puw_lDt_ne_uwA : lDt ≠ uwA := by decide
@[simp] theorem puw_uwA_ne_lDg : uwA ≠ lDg := by decide
@[simp] theorem puw_lDg_ne_uwA : lDg ≠ uwA := by decide
@[simp] theorem puw_uwA_ne_lDi : uwA ≠ lDi := by decide
@[simp] theorem puw_lDi_ne_uwA : lDi ≠ uwA := by decide
@[simp] theorem puw_uwA_ne_lRp : uwA ≠ lRp := by decide
@[simp] theorem puw_lRp_ne_uwA : lRp ≠ uwA := by decide
@[simp] theorem puw_uwA_ne_lRn : uwA ≠ lRn := by decide
@[simp] theorem puw_lRn_ne_uwA : lRn ≠ uwA := by decide
@[simp] theorem puw_uwA_ne_lFle : uwA ≠ lFle := by decide
@[simp] theorem puw_lFle_ne_uwA : lFle ≠ uwA := by decide
@[simp] theorem puw_uwA_ne_lKb : uwA ≠ lKb := by decide
@[simp] theorem puw_lKb_ne_uwA : lKb ≠ uwA := by decide
@[simp] theorem puw_uwA_ne_lDir : uwA ≠ lDir := by decide
@[simp] theorem puw_lDir_ne_uwA : lDir ≠ uwA := by decide
@[simp] theorem puw_uwA_ne_lFln : uwA ≠ lFln := by decide
@[simp] theorem puw_lFln_ne_uwA : lFln ≠ uwA := by decide
@[simp] theorem puw_uwA_ne_lFll : uwA ≠ lFll := by decide
@[simp] theorem puw_lFll_ne_uwA : lFll ≠ uwA := by decide
@[simp] theorem puw_uwA_ne_lFls : uwA ≠ lFls := by decide
@[simp] theorem puw_lFls_ne_uwA : lFls ≠ uwA := by decide
@[simp] theorem puw_uwA_ne_kFu : uwA ≠ kFu := by decide
@[simp] theorem puw_kFu_ne_uwA : kFu ≠ uwA := by decide
@[simp] theorem puw_uwA_ne_kD : uwA ≠ kD := by decide
@[simp] theorem puw_kD_ne_uwA : kD ≠ uwA := by decide
@[simp] theorem puw_uwR_ne_uwF : uwR ≠ uwF := by decide
@[simp] theorem puw_uwR_ne_uwN : uwR ≠ uwN := by decide
@[simp] theorem puw_uwR_ne_uwE : uwR ≠ uwE := by decide
@[simp] theorem puw_uwR_ne_uwH : uwR ≠ uwH := by decide
@[simp] theorem puw_uwR_ne_uwC : uwR ≠ uwC := by decide
@[simp] theorem puw_uwR_ne_uwP : uwR ≠ uwP := by decide
@[simp] theorem puw_uwR_ne_uwQ : uwR ≠ uwQ := by decide
@[simp] theorem puw_uwR_ne_uwK : uwR ≠ uwK := by decide
@[simp] theorem puw_uwR_ne_uwV : uwR ≠ uwV := by decide
@[simp] theorem puw_uwR_ne_uwL : uwR ≠ uwL := by decide
@[simp] theorem puw_uwR_ne_uwKk : uwR ≠ uwKk := by decide
@[simp] theorem puw_uwR_ne_uwJ : uwR ≠ uwJ := by decide
@[simp] theorem puw_uwR_ne_uwX : uwR ≠ uwX := by decide
@[simp] theorem puw_uwR_ne_uwLa : uwR ≠ uwLa := by decide
@[simp] theorem puw_uwR_ne_uwA : uwR ≠ uwA := by decide
@[simp] theorem puw_uwR_ne_lFl : uwR ≠ lFl := by decide
@[simp] theorem puw_lFl_ne_uwR : lFl ≠ uwR := by decide
@[simp] theorem puw_uwR_ne_lDh : uwR ≠ lDh := by decide
@[simp] theorem puw_lDh_ne_uwR : lDh ≠ uwR := by decide
@[simp] theorem puw_uwR_ne_lDt : uwR ≠ lDt := by decide
@[simp] theorem puw_lDt_ne_uwR : lDt ≠ uwR := by decide
@[simp] theorem puw_uwR_ne_lDg : uwR ≠ lDg := by decide
@[simp] theorem puw_lDg_ne_uwR : lDg ≠ uwR := by decide
@[simp] theorem puw_uwR_ne_lDi : uwR ≠ lDi := by decide
@[simp] theorem puw_lDi_ne_uwR : lDi ≠ uwR := by decide
@[simp] theorem puw_uwR_ne_lRp : uwR ≠ lRp := by decide
@[simp] theorem puw_lRp_ne_uwR : lRp ≠ uwR := by decide
@[simp] theorem puw_uwR_ne_lRn : uwR ≠ lRn := by decide
@[simp] theorem puw_lRn_ne_uwR : lRn ≠ uwR := by decide
@[simp] theorem puw_uwR_ne_lFle : uwR ≠ lFle := by decide
@[simp] theorem puw_lFle_ne_uwR : lFle ≠ uwR := by decide
@[simp] theorem puw_uwR_ne_lKb : uwR ≠ lKb := by decide
@[simp] theorem puw_lKb_ne_uwR : lKb ≠ uwR := by decide
@[simp] theorem puw_uwR_ne_lDir : uwR ≠ lDir := by decide
@[simp] theorem puw_lDir_ne_uwR : lDir ≠ uwR := by decide
@[simp] theorem puw_uwR_ne_lFln : uwR ≠ lFln := by decide
@[simp] theorem puw_lFln_ne_uwR : lFln ≠ uwR := by decide
@[simp] theorem puw_uwR_ne_lFll : uwR ≠ lFll := by decide
@[simp] theorem puw_lFll_ne_uwR : lFll ≠ uwR := by decide
@[simp] theorem puw_uwR_ne_lFls : uwR ≠ lFls := by decide
@[simp] theorem puw_lFls_ne_uwR : lFls ≠ uwR := by decide
@[simp] theorem puw_uwR_ne_kFu : uwR ≠ kFu := by decide
@[simp] theorem puw_kFu_ne_uwR : kFu ≠ uwR := by decide
@[simp] theorem puw_uwR_ne_kD : uwR ≠ kD := by decide
@[simp] theorem puw_kD_ne_uwR : kD ≠ uwR := by decide

def uwParams : List MlS := [uwF, uwN, uwE]
def uwLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, uwH, uwC, uwP, uwQ, uwK, uwV, uwL, uwKk, uwJ, uwX, uwLa, uwA, uwR]
def uwBody (C : Ctx) : ProgHOL 64 := prologue uwLocals (.ite (.cmp .equal (vv uwN) (.const 0)) (.return (vv uwE)) (.seq (.call (some (some (.local, uwH), none)) fGetAppFn [(vv uwF), (vv uwE)]) (.ite (tagIsE uwH 3) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv uwH)) (.seq eViewP (.seq (.assign .local uwC (.load .one (vv lRp))) (envFindP C uwP (vv uwC) (.ite (.cmp .equal (vv uwP) (.const 0)) (.return (vv uwE)) (.seq (.assign .local uwQ (.op .sub [(vv uwP), (.const 1)])) (.seq (.assign .local uwK (.load .one (vv uwQ))) (.ite (.cmp .notEqual (vv uwK) (.const 1)) (.return (vv uwE)) (.seq (.assign .local uwV (.load .one (.op .add [(vv uwQ), (.const 32)]))) (.seq (.call (some (some (.local, uwL), none)) fLj [(vv uwF), (.const 0), (vv uwV)]) (.ite (.cmp .equal (vv uwL) (.const 0)) (.return (vv uwE)) (.seq (.assign .local uwKk (.load .one (vv uwL))) (.seq (.assign .local uwJ (.load .one (.op .add [(vv uwL), (.const 8)]))) (.seq (.call (some (some (.local, uwX), none)) ExG.fGaa [(vv uwF), (vv uwE)]) (.seq (.assign .local uwLa (.load .one (vv uwX))) (.ite (.cmp .notEqual (vv uwLa) (vv uwKk)) (.return (vv uwE)) (.seq (.assign .local uwA (.load .one (.op .add [(.op .add [(vv uwX), (.const 8)]), (.shift .lsl (.op .sub [(.op .sub [(vv uwKk), (.const 1)]), (vv uwJ)]) (.const 3))]))) (.seq (.call (some (some (.local, uwR), none)) fUw [(vv uwF), (.op .sub [(vv uwN), (.const 1)]), (vv uwA)]) (.return (vv uwR))))))))))))))))))))) (.return (vv uwE)))))

def pvF := ofString "ppv_pvf"
def pvK := ofString "ppv_pvk"
def pvE := ofString "ppv_pve"
def pvU := ofString "ppv_pvu"
def pvB := ofString "ppv_pvb"
def pvR := ofString "ppv_pvr"
def fPv := ofString "peelPisW"

@[simp] theorem ppv_pvF_ne_pvK : pvF ≠ pvK := by decide
@[simp] theorem ppv_pvF_ne_pvE : pvF ≠ pvE := by decide
@[simp] theorem ppv_pvF_ne_pvU : pvF ≠ pvU := by decide
@[simp] theorem ppv_pvF_ne_pvB : pvF ≠ pvB := by decide
@[simp] theorem ppv_pvF_ne_pvR : pvF ≠ pvR := by decide
@[simp] theorem ppv_pvF_ne_lFl : pvF ≠ lFl := by decide
@[simp] theorem ppv_lFl_ne_pvF : lFl ≠ pvF := by decide
@[simp] theorem ppv_pvF_ne_lDh : pvF ≠ lDh := by decide
@[simp] theorem ppv_lDh_ne_pvF : lDh ≠ pvF := by decide
@[simp] theorem ppv_pvF_ne_lDt : pvF ≠ lDt := by decide
@[simp] theorem ppv_lDt_ne_pvF : lDt ≠ pvF := by decide
@[simp] theorem ppv_pvF_ne_lDg : pvF ≠ lDg := by decide
@[simp] theorem ppv_lDg_ne_pvF : lDg ≠ pvF := by decide
@[simp] theorem ppv_pvF_ne_lDi : pvF ≠ lDi := by decide
@[simp] theorem ppv_lDi_ne_pvF : lDi ≠ pvF := by decide
@[simp] theorem ppv_pvF_ne_lRp : pvF ≠ lRp := by decide
@[simp] theorem ppv_lRp_ne_pvF : lRp ≠ pvF := by decide
@[simp] theorem ppv_pvF_ne_lRn : pvF ≠ lRn := by decide
@[simp] theorem ppv_lRn_ne_pvF : lRn ≠ pvF := by decide
@[simp] theorem ppv_pvF_ne_lFle : pvF ≠ lFle := by decide
@[simp] theorem ppv_lFle_ne_pvF : lFle ≠ pvF := by decide
@[simp] theorem ppv_pvF_ne_lKb : pvF ≠ lKb := by decide
@[simp] theorem ppv_lKb_ne_pvF : lKb ≠ pvF := by decide
@[simp] theorem ppv_pvF_ne_lDir : pvF ≠ lDir := by decide
@[simp] theorem ppv_lDir_ne_pvF : lDir ≠ pvF := by decide
@[simp] theorem ppv_pvF_ne_lFln : pvF ≠ lFln := by decide
@[simp] theorem ppv_lFln_ne_pvF : lFln ≠ pvF := by decide
@[simp] theorem ppv_pvF_ne_lFll : pvF ≠ lFll := by decide
@[simp] theorem ppv_lFll_ne_pvF : lFll ≠ pvF := by decide
@[simp] theorem ppv_pvF_ne_lFls : pvF ≠ lFls := by decide
@[simp] theorem ppv_lFls_ne_pvF : lFls ≠ pvF := by decide
@[simp] theorem ppv_pvF_ne_kFu : pvF ≠ kFu := by decide
@[simp] theorem ppv_kFu_ne_pvF : kFu ≠ pvF := by decide
@[simp] theorem ppv_pvF_ne_kD : pvF ≠ kD := by decide
@[simp] theorem ppv_kD_ne_pvF : kD ≠ pvF := by decide
@[simp] theorem ppv_pvK_ne_pvF : pvK ≠ pvF := by decide
@[simp] theorem ppv_pvK_ne_pvE : pvK ≠ pvE := by decide
@[simp] theorem ppv_pvK_ne_pvU : pvK ≠ pvU := by decide
@[simp] theorem ppv_pvK_ne_pvB : pvK ≠ pvB := by decide
@[simp] theorem ppv_pvK_ne_pvR : pvK ≠ pvR := by decide
@[simp] theorem ppv_pvK_ne_lFl : pvK ≠ lFl := by decide
@[simp] theorem ppv_lFl_ne_pvK : lFl ≠ pvK := by decide
@[simp] theorem ppv_pvK_ne_lDh : pvK ≠ lDh := by decide
@[simp] theorem ppv_lDh_ne_pvK : lDh ≠ pvK := by decide
@[simp] theorem ppv_pvK_ne_lDt : pvK ≠ lDt := by decide
@[simp] theorem ppv_lDt_ne_pvK : lDt ≠ pvK := by decide
@[simp] theorem ppv_pvK_ne_lDg : pvK ≠ lDg := by decide
@[simp] theorem ppv_lDg_ne_pvK : lDg ≠ pvK := by decide
@[simp] theorem ppv_pvK_ne_lDi : pvK ≠ lDi := by decide
@[simp] theorem ppv_lDi_ne_pvK : lDi ≠ pvK := by decide
@[simp] theorem ppv_pvK_ne_lRp : pvK ≠ lRp := by decide
@[simp] theorem ppv_lRp_ne_pvK : lRp ≠ pvK := by decide
@[simp] theorem ppv_pvK_ne_lRn : pvK ≠ lRn := by decide
@[simp] theorem ppv_lRn_ne_pvK : lRn ≠ pvK := by decide
@[simp] theorem ppv_pvK_ne_lFle : pvK ≠ lFle := by decide
@[simp] theorem ppv_lFle_ne_pvK : lFle ≠ pvK := by decide
@[simp] theorem ppv_pvK_ne_lKb : pvK ≠ lKb := by decide
@[simp] theorem ppv_lKb_ne_pvK : lKb ≠ pvK := by decide
@[simp] theorem ppv_pvK_ne_lDir : pvK ≠ lDir := by decide
@[simp] theorem ppv_lDir_ne_pvK : lDir ≠ pvK := by decide
@[simp] theorem ppv_pvK_ne_lFln : pvK ≠ lFln := by decide
@[simp] theorem ppv_lFln_ne_pvK : lFln ≠ pvK := by decide
@[simp] theorem ppv_pvK_ne_lFll : pvK ≠ lFll := by decide
@[simp] theorem ppv_lFll_ne_pvK : lFll ≠ pvK := by decide
@[simp] theorem ppv_pvK_ne_lFls : pvK ≠ lFls := by decide
@[simp] theorem ppv_lFls_ne_pvK : lFls ≠ pvK := by decide
@[simp] theorem ppv_pvK_ne_kFu : pvK ≠ kFu := by decide
@[simp] theorem ppv_kFu_ne_pvK : kFu ≠ pvK := by decide
@[simp] theorem ppv_pvK_ne_kD : pvK ≠ kD := by decide
@[simp] theorem ppv_kD_ne_pvK : kD ≠ pvK := by decide
@[simp] theorem ppv_pvE_ne_pvF : pvE ≠ pvF := by decide
@[simp] theorem ppv_pvE_ne_pvK : pvE ≠ pvK := by decide
@[simp] theorem ppv_pvE_ne_pvU : pvE ≠ pvU := by decide
@[simp] theorem ppv_pvE_ne_pvB : pvE ≠ pvB := by decide
@[simp] theorem ppv_pvE_ne_pvR : pvE ≠ pvR := by decide
@[simp] theorem ppv_pvE_ne_lFl : pvE ≠ lFl := by decide
@[simp] theorem ppv_lFl_ne_pvE : lFl ≠ pvE := by decide
@[simp] theorem ppv_pvE_ne_lDh : pvE ≠ lDh := by decide
@[simp] theorem ppv_lDh_ne_pvE : lDh ≠ pvE := by decide
@[simp] theorem ppv_pvE_ne_lDt : pvE ≠ lDt := by decide
@[simp] theorem ppv_lDt_ne_pvE : lDt ≠ pvE := by decide
@[simp] theorem ppv_pvE_ne_lDg : pvE ≠ lDg := by decide
@[simp] theorem ppv_lDg_ne_pvE : lDg ≠ pvE := by decide
@[simp] theorem ppv_pvE_ne_lDi : pvE ≠ lDi := by decide
@[simp] theorem ppv_lDi_ne_pvE : lDi ≠ pvE := by decide
@[simp] theorem ppv_pvE_ne_lRp : pvE ≠ lRp := by decide
@[simp] theorem ppv_lRp_ne_pvE : lRp ≠ pvE := by decide
@[simp] theorem ppv_pvE_ne_lRn : pvE ≠ lRn := by decide
@[simp] theorem ppv_lRn_ne_pvE : lRn ≠ pvE := by decide
@[simp] theorem ppv_pvE_ne_lFle : pvE ≠ lFle := by decide
@[simp] theorem ppv_lFle_ne_pvE : lFle ≠ pvE := by decide
@[simp] theorem ppv_pvE_ne_lKb : pvE ≠ lKb := by decide
@[simp] theorem ppv_lKb_ne_pvE : lKb ≠ pvE := by decide
@[simp] theorem ppv_pvE_ne_lDir : pvE ≠ lDir := by decide
@[simp] theorem ppv_lDir_ne_pvE : lDir ≠ pvE := by decide
@[simp] theorem ppv_pvE_ne_lFln : pvE ≠ lFln := by decide
@[simp] theorem ppv_lFln_ne_pvE : lFln ≠ pvE := by decide
@[simp] theorem ppv_pvE_ne_lFll : pvE ≠ lFll := by decide
@[simp] theorem ppv_lFll_ne_pvE : lFll ≠ pvE := by decide
@[simp] theorem ppv_pvE_ne_lFls : pvE ≠ lFls := by decide
@[simp] theorem ppv_lFls_ne_pvE : lFls ≠ pvE := by decide
@[simp] theorem ppv_pvE_ne_kFu : pvE ≠ kFu := by decide
@[simp] theorem ppv_kFu_ne_pvE : kFu ≠ pvE := by decide
@[simp] theorem ppv_pvE_ne_kD : pvE ≠ kD := by decide
@[simp] theorem ppv_kD_ne_pvE : kD ≠ pvE := by decide
@[simp] theorem ppv_pvU_ne_pvF : pvU ≠ pvF := by decide
@[simp] theorem ppv_pvU_ne_pvK : pvU ≠ pvK := by decide
@[simp] theorem ppv_pvU_ne_pvE : pvU ≠ pvE := by decide
@[simp] theorem ppv_pvU_ne_pvB : pvU ≠ pvB := by decide
@[simp] theorem ppv_pvU_ne_pvR : pvU ≠ pvR := by decide
@[simp] theorem ppv_pvU_ne_lFl : pvU ≠ lFl := by decide
@[simp] theorem ppv_lFl_ne_pvU : lFl ≠ pvU := by decide
@[simp] theorem ppv_pvU_ne_lDh : pvU ≠ lDh := by decide
@[simp] theorem ppv_lDh_ne_pvU : lDh ≠ pvU := by decide
@[simp] theorem ppv_pvU_ne_lDt : pvU ≠ lDt := by decide
@[simp] theorem ppv_lDt_ne_pvU : lDt ≠ pvU := by decide
@[simp] theorem ppv_pvU_ne_lDg : pvU ≠ lDg := by decide
@[simp] theorem ppv_lDg_ne_pvU : lDg ≠ pvU := by decide
@[simp] theorem ppv_pvU_ne_lDi : pvU ≠ lDi := by decide
@[simp] theorem ppv_lDi_ne_pvU : lDi ≠ pvU := by decide
@[simp] theorem ppv_pvU_ne_lRp : pvU ≠ lRp := by decide
@[simp] theorem ppv_lRp_ne_pvU : lRp ≠ pvU := by decide
@[simp] theorem ppv_pvU_ne_lRn : pvU ≠ lRn := by decide
@[simp] theorem ppv_lRn_ne_pvU : lRn ≠ pvU := by decide
@[simp] theorem ppv_pvU_ne_lFle : pvU ≠ lFle := by decide
@[simp] theorem ppv_lFle_ne_pvU : lFle ≠ pvU := by decide
@[simp] theorem ppv_pvU_ne_lKb : pvU ≠ lKb := by decide
@[simp] theorem ppv_lKb_ne_pvU : lKb ≠ pvU := by decide
@[simp] theorem ppv_pvU_ne_lDir : pvU ≠ lDir := by decide
@[simp] theorem ppv_lDir_ne_pvU : lDir ≠ pvU := by decide
@[simp] theorem ppv_pvU_ne_lFln : pvU ≠ lFln := by decide
@[simp] theorem ppv_lFln_ne_pvU : lFln ≠ pvU := by decide
@[simp] theorem ppv_pvU_ne_lFll : pvU ≠ lFll := by decide
@[simp] theorem ppv_lFll_ne_pvU : lFll ≠ pvU := by decide
@[simp] theorem ppv_pvU_ne_lFls : pvU ≠ lFls := by decide
@[simp] theorem ppv_lFls_ne_pvU : lFls ≠ pvU := by decide
@[simp] theorem ppv_pvU_ne_kFu : pvU ≠ kFu := by decide
@[simp] theorem ppv_kFu_ne_pvU : kFu ≠ pvU := by decide
@[simp] theorem ppv_pvU_ne_kD : pvU ≠ kD := by decide
@[simp] theorem ppv_kD_ne_pvU : kD ≠ pvU := by decide
@[simp] theorem ppv_pvB_ne_pvF : pvB ≠ pvF := by decide
@[simp] theorem ppv_pvB_ne_pvK : pvB ≠ pvK := by decide
@[simp] theorem ppv_pvB_ne_pvE : pvB ≠ pvE := by decide
@[simp] theorem ppv_pvB_ne_pvU : pvB ≠ pvU := by decide
@[simp] theorem ppv_pvB_ne_pvR : pvB ≠ pvR := by decide
@[simp] theorem ppv_pvB_ne_lFl : pvB ≠ lFl := by decide
@[simp] theorem ppv_lFl_ne_pvB : lFl ≠ pvB := by decide
@[simp] theorem ppv_pvB_ne_lDh : pvB ≠ lDh := by decide
@[simp] theorem ppv_lDh_ne_pvB : lDh ≠ pvB := by decide
@[simp] theorem ppv_pvB_ne_lDt : pvB ≠ lDt := by decide
@[simp] theorem ppv_lDt_ne_pvB : lDt ≠ pvB := by decide
@[simp] theorem ppv_pvB_ne_lDg : pvB ≠ lDg := by decide
@[simp] theorem ppv_lDg_ne_pvB : lDg ≠ pvB := by decide
@[simp] theorem ppv_pvB_ne_lDi : pvB ≠ lDi := by decide
@[simp] theorem ppv_lDi_ne_pvB : lDi ≠ pvB := by decide
@[simp] theorem ppv_pvB_ne_lRp : pvB ≠ lRp := by decide
@[simp] theorem ppv_lRp_ne_pvB : lRp ≠ pvB := by decide
@[simp] theorem ppv_pvB_ne_lRn : pvB ≠ lRn := by decide
@[simp] theorem ppv_lRn_ne_pvB : lRn ≠ pvB := by decide
@[simp] theorem ppv_pvB_ne_lFle : pvB ≠ lFle := by decide
@[simp] theorem ppv_lFle_ne_pvB : lFle ≠ pvB := by decide
@[simp] theorem ppv_pvB_ne_lKb : pvB ≠ lKb := by decide
@[simp] theorem ppv_lKb_ne_pvB : lKb ≠ pvB := by decide
@[simp] theorem ppv_pvB_ne_lDir : pvB ≠ lDir := by decide
@[simp] theorem ppv_lDir_ne_pvB : lDir ≠ pvB := by decide
@[simp] theorem ppv_pvB_ne_lFln : pvB ≠ lFln := by decide
@[simp] theorem ppv_lFln_ne_pvB : lFln ≠ pvB := by decide
@[simp] theorem ppv_pvB_ne_lFll : pvB ≠ lFll := by decide
@[simp] theorem ppv_lFll_ne_pvB : lFll ≠ pvB := by decide
@[simp] theorem ppv_pvB_ne_lFls : pvB ≠ lFls := by decide
@[simp] theorem ppv_lFls_ne_pvB : lFls ≠ pvB := by decide
@[simp] theorem ppv_pvB_ne_kFu : pvB ≠ kFu := by decide
@[simp] theorem ppv_kFu_ne_pvB : kFu ≠ pvB := by decide
@[simp] theorem ppv_pvB_ne_kD : pvB ≠ kD := by decide
@[simp] theorem ppv_kD_ne_pvB : kD ≠ pvB := by decide
@[simp] theorem ppv_pvR_ne_pvF : pvR ≠ pvF := by decide
@[simp] theorem ppv_pvR_ne_pvK : pvR ≠ pvK := by decide
@[simp] theorem ppv_pvR_ne_pvE : pvR ≠ pvE := by decide
@[simp] theorem ppv_pvR_ne_pvU : pvR ≠ pvU := by decide
@[simp] theorem ppv_pvR_ne_pvB : pvR ≠ pvB := by decide
@[simp] theorem ppv_pvR_ne_lFl : pvR ≠ lFl := by decide
@[simp] theorem ppv_lFl_ne_pvR : lFl ≠ pvR := by decide
@[simp] theorem ppv_pvR_ne_lDh : pvR ≠ lDh := by decide
@[simp] theorem ppv_lDh_ne_pvR : lDh ≠ pvR := by decide
@[simp] theorem ppv_pvR_ne_lDt : pvR ≠ lDt := by decide
@[simp] theorem ppv_lDt_ne_pvR : lDt ≠ pvR := by decide
@[simp] theorem ppv_pvR_ne_lDg : pvR ≠ lDg := by decide
@[simp] theorem ppv_lDg_ne_pvR : lDg ≠ pvR := by decide
@[simp] theorem ppv_pvR_ne_lDi : pvR ≠ lDi := by decide
@[simp] theorem ppv_lDi_ne_pvR : lDi ≠ pvR := by decide
@[simp] theorem ppv_pvR_ne_lRp : pvR ≠ lRp := by decide
@[simp] theorem ppv_lRp_ne_pvR : lRp ≠ pvR := by decide
@[simp] theorem ppv_pvR_ne_lRn : pvR ≠ lRn := by decide
@[simp] theorem ppv_lRn_ne_pvR : lRn ≠ pvR := by decide
@[simp] theorem ppv_pvR_ne_lFle : pvR ≠ lFle := by decide
@[simp] theorem ppv_lFle_ne_pvR : lFle ≠ pvR := by decide
@[simp] theorem ppv_pvR_ne_lKb : pvR ≠ lKb := by decide
@[simp] theorem ppv_lKb_ne_pvR : lKb ≠ pvR := by decide
@[simp] theorem ppv_pvR_ne_lDir : pvR ≠ lDir := by decide
@[simp] theorem ppv_lDir_ne_pvR : lDir ≠ pvR := by decide
@[simp] theorem ppv_pvR_ne_lFln : pvR ≠ lFln := by decide
@[simp] theorem ppv_lFln_ne_pvR : lFln ≠ pvR := by decide
@[simp] theorem ppv_pvR_ne_lFll : pvR ≠ lFll := by decide
@[simp] theorem ppv_lFll_ne_pvR : lFll ≠ pvR := by decide
@[simp] theorem ppv_pvR_ne_lFls : pvR ≠ lFls := by decide
@[simp] theorem ppv_lFls_ne_pvR : lFls ≠ pvR := by decide
@[simp] theorem ppv_pvR_ne_kFu : pvR ≠ kFu := by decide
@[simp] theorem ppv_kFu_ne_pvR : kFu ≠ pvR := by decide
@[simp] theorem ppv_pvR_ne_kD : pvR ≠ kD := by decide
@[simp] theorem ppv_kD_ne_pvR : kD ≠ pvR := by decide

def pvParams : List MlS := [pvF, pvK, pvE]
def pvLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, pvU, pvB, pvR]
def pvBody (C : Ctx) : ProgHOL 64 := prologue pvLocals (.ite (.cmp .equal (vv pvK) (.const 0)) (.seq (.call (some (some (.local, pvU), none)) fUw [(vv pvF), (.const 4), (vv pvE)]) (.return (.op .add [(vv pvU), (.const 1)]))) (.ite (tagIsE pvE 6) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pvE)) (.seq eViewP (.seq (.assign .local pvB (.load .one (.op .add [(vv lRp), (.const 8)]))) (.seq (.call (some (some (.local, pvR), none)) fPv [(vv pvF), (.op .sub [(vv pvK), (.const 1)]), (vv pvB)]) (.return (vv pvR))))))) (.seq (.call (some (some (.local, pvU), none)) fUw [(vv pvF), (.const 4), (vv pvE)]) (.ite (tagIsE pvU 6) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pvU)) (.seq eViewP (.seq (.assign .local pvB (.load .one (.op .add [(vv lRp), (.const 8)]))) (.seq (.call (some (some (.local, pvR), none)) fPv [(vv pvF), (.op .sub [(vv pvK), (.const 1)]), (vv pvB)]) (.return (vv pvR))))))) (.return (.const 0))))))

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



theorem viewConstName_bind (st : EStore) (h : EIdx) (h3 : h.tag = 3) :
    st.viewConstName h = (st.view h).bind (fun v => match v with | .const n _ => some n | _ => none) := by
  simp only [EStore.view, EStore.viewConstName, EStore.persGetConstName]
  split
  · simp only [ETables.get, ETables.getConstName, h3, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj]
    cases st.pers.consts.node? h.idxNat <;> rfl
  · split
    · simp only [ETables.get, ETables.getConstName, h3, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj]
      cases st.scr.consts.node? h.idxNat <;> rfl
    · rfl

structure UwCodes (C : Ctx) : Prop where
  gaf : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  mg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  mp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  gaa : C.code.lookup ExG.fGaa = some ([(pFu, .one), (pH, .one)], ExG.gaaBody C, .one)
  lj : C.code.lookup fLj = some (ljParams.map (fun p => (p, ShapeHOL.one)), ljBody C, .one)
  self : C.code.lookup fUw = some (uwParams.map (fun p => (p, ShapeHOL.one)), uwBody C, .one)

theorem uw_spec (C : Ctx) (hok : CtxOK C) (hc : UwCodes C) (fuel : Nat) (hf : fuel < 2 ^ 62) :
    ∀ n (H : List (BitVec 64)) (e : EIdx) (s : AState), C.H <+: H → n < 2 ^ 64 →
      SpecR (σ := σ) (Pre (ctxH C H) s (uwParams.zip [BitVec.ofNat 64 fuel, BitVec.ofNat 64 n, Enc.idxW e])) (uwBody C) s
        (unwrapIdDefs C.fe fuel n e) (PostK (ctxH C H)) := by
  have hf64 : fuel < 2 ^ 64 := by omega
  intro n
  induction n with
  | zero =>
    intro H e s hpH _
    refine specR_prologue (postK_locals _) (Knot.params_none _ uwLocals uwParams _ (by decide) (by decide)) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, uwParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    rw [unwrapIdDefs]
    exact specR_returnI _ (Enc.idxW e) (by simp +decide [Env.get, uwParams, ctxEnv]) (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ n ih =>
    intro H e s hpH hn
    refine specR_prologue (postK_locals _) (Knot.params_none _ uwLocals uwParams _ (by decide) (by decide)) ?_
    have hne : BitVec.ofNat 64 (n + 1) ≠ 0 := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, uwParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
    rw [unwrapIdDefs]
    refine specR_callNIM (C := ctxH C H) uwH fGetAppFn [pFu, pH] [vv uwF, vv uwE]
      getAppFnBody [BitVec.ofNat 64 fuel, Enc.idxW e] (by decide) rfl (by decide) hc.gaf
      ⟨by simp +decide [Env.get, uwParams, ctxEnv], by simp +decide [Env.get, uwParams, ctxEnv], trivial⟩
      (fun x w' s' st => getAppFn fuel e s = .ok (x, s') ∧ Post (ctxH C H) s x w' s' st)
      (fun x w' s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
      (fun u hu _ hlk => specR_run (fun t ht => by
        subst ht
        exact getAppFn_spec (ctxH C H) hc.gaf fuel e s hf64 t ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
      (fun hh w' s' st ⟨hrun, hw, hs, _⟩ => ?_)
    subst hw
    have hs' : s = s' := hs.symm
    subst hs'
    refine Knot.specR_tagIteV uwH hh 3 (by decide) (by decide) (by simp) (fun htc => ?_) (fun htc => ?_)
    swap
    · rw [if_neg (show ¬ (hh.tag == ETag.const) = true by simpa [ETag.const] using htc)]
      exact specR_returnI _ (Enc.idxW e) (by simp +decide [Env.get, uwParams, ctxEnv]) (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    rw [if_pos (show (hh.tag == ETag.const) = true by simp [htc, ETag.const])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv uwH) (Enc.idxW hh) (by decide) (by simp) ?_
    refine specR_viewP (C := ctxH C H) hh (by simp) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
      (fun v P hv htn _ => ?_)
    have h3 : v.tagN = 3 := by rw [htn, htc]; rfl
    obtain ⟨c, us, rfl⟩ := UD.tagN_const h3
    have hvn : s.store.viewConstName hh = some c := by rw [viewConstName_bind _ _ (by rw [htc]; rfl), hv]; rfl
    refine specR_runBind (show ConRon.Arena.viewConstName hh s = .ok (some c, s) by
      show Except.ok (s.store.viewConstName hh, s) = _; rw [hvn]) ?_
    dsimp only
    refine specR_loadI' uwC (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW c) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW c) [Enc.idxW us] []) ?_
    refine specR_envFindI (C := ctxH C H) (ctxOK_H hok H) hc.mg hc.mp uwP (vv uwC) c (by decide) (by simp) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    have hrel := find_rel hok c
    try rw [show (ctxH C H).envM = C.envM from rfl]
    revert hrel
    rcases hfind : C.fe.find? c with _ | ci
    · intro hrel; simp only at hrel; rw [hrel]
      refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ (Enc.idxW e) (by simp +decide [Env.get, uwParams, ctxEnv]) (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    intro ⟨o, hm, hci⟩
    rw [hm]
    refine specR_atEntry fun t ht => ?_
    have hoE : o < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
    refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI uwQ _ (ecell C o) (by decide) (by simp [sev, optWG]; exact BitVec.add_sub_cancel _ _) ?_
    rcases ci with cv | ⟨cv, val, hint⟩ | cv | ⟨cv, caps⟩ | ⟨cv, np, nf, ind⟩ | ⟨cv, mi, rp, isK, rules⟩
    · refine specR_envLoadI uwK (vv uwQ) o 0 (by decide) (by simp [ecell_ctxH]) hci.2 ?_
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ (Enc.idxW e) (by simp +decide [Env.get, uwParams, ctxEnv]) (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_envLoadI uwK (vv uwQ) o 1 (by decide) (by simp [ecell_ctxH]) hci.2.1 ?_
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      obtain ⟨_, _, hval, _⟩ := hci
      dsimp only
      refine specR_envLoadI uwV (.op .add [vv uwQ, .const 32]) (o + 4) _ (by decide)
        (by simp [sev, vv, ecell_ctxH]; simpa using ecell_add C o 4) hval ?_
      refine specR_callNIH (C := ctxH C H) uwL fLj ljParams [vv uwF, .const 0, vv uwV] (ljBody C)
        [BitVec.ofNat 64 fuel, BitVec.ofNat 64 0, Enc.idxW val] (by decide) rfl (by decide) hc.lj
        ⟨by simp +decide [Env.get, uwParams, ctxEnv], rfl, by simp, trivial⟩
        (PostLJ (ctxH C H)) (fun r_ w _ H' => ljRel C H' r_ w) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ljParams _ rfl hlk)
          (lj_spec (ctxH C H) (ctxOK_H hok H) hc.lj fuel 0 val s (by omega)))
        (fun lr w s1 H1 hp1 hw => ?_)
      have hp1a : C.H <+: H1 := hpH.trans hp1
      rcases lr with _ | ⟨kk, j⟩
      · simp only [ljRel] at hw; subst hw
        refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
        try dsimp only
        exact specR_returnI _ (Enc.idxW e) (by simp +decide [Env.get, uwParams, ctxEnv]) (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      obtain ⟨ol, rfl, hok1, hoj, hjk, hk63⟩ := hw
      refine specR_atEntry fun t ht => ?_
      have hbig := cellA_big hok ht.sr (List.getElem?_eq_some_iff.mp hok1).1
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hbig.1) (fun h => absurd rfl h) (fun _ => ?_)
      try dsimp only
      refine UD.specR_heapLoadI' (C := ctxH C H1) uwKk (vv uwL) ol _ hok1 (by decide) (by simp <;> rfl) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H1) uwJ (.op .add [vv uwL, .const 8]) (ol + 1) _ hoj (by decide)
        (by simp [sev]; exact cellA_add8 C ol) ?_
      refine specR_callNIH (C := ctxH C H1) uwX ExG.fGaa [pFu, pH] [vv uwF, vv uwE] (ExG.gaaBody C)
        [BitVec.ofNat 64 fuel, Enc.idxW e] (by decide) rfl (by decide) hc.gaa
        ⟨by simp +decide [Env.get, uwParams, ctxEnv], by simp +decide [Env.get, uwParams, ctxEnv], trivial⟩
        (PostA (ctxH C H1)) (fun xs w _ H2 => ∃ o2, w = cellA C o2 ∧ BlkAt H2 o2 (xs.map Enc.idxW))
        (fun xs w s' st ⟨H2, o2, hp, hw, hb, hsr⟩ => ⟨H2, hp, ⟨o2, hw, hb⟩, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
          (ExG.gaa_spec C hok hc.gaa fuel hf64 H1 e s1))
        (fun args w s2 H2 hp2 ⟨o2, hw, hba⟩ => ?_)
      subst hw
      have hp2a : C.H <+: H2 := hp1a.trans hp2
      refine UD.specR_heapLoadI' (C := ctxH C H2) uwLa (vv uwX) o2 _ (by have h := hba.1; simp only [List.length_map] at h; exact h)
        (by decide) (by simp <;> rfl) ?_
      refine specR_atEntry fun t ht => ?_
      have hsza := blk_small0 (ctxOK_H hok H2) ht.sr hba
      simp only [List.length_map] at hsza
      have hkeq : (decide (kk ≤ args.length) && args.length == kk) = (args.length == kk) := by
        by_cases h : args.length = kk <;> simp [h]
      by_cases hln : args.length = kk
      swap
      · have hne : BitVec.ofNat 64 args.length ≠ BitVec.ofNat 64 kk := by
          intro x; apply hln
          have := congrArg BitVec.toNat x
          simp only [BitVec.toNat_ofNat] at this
          rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
        refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun _ => ?_) (fun h => absurd h (by decide))
        rw [if_neg (by simp [hln])]
        exact specR_returnI _ (Enc.idxW e) (by simp +decide [Env.get, uwParams, ctxEnv]) (fun t ht => ⟨H2, hp1.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hln]) (fun h => absurd rfl h) (fun _ => ?_)
      rw [if_pos (by simp [hln])]
      have hidx : kk - 1 - j < args.length := by omega
      have hget : args.getD (kk - 1 - j) e = args[kk - 1 - j] := by simp [List.getD, hidx]
      rw [hget]
      have hel := hba.2 (kk - 1 - j) (by simpa using hidx)
      rw [List.getElem_map] at hel
      have hsubw : BitVec.ofNat 64 kk - 1#64 - BitVec.ofNat 64 j = BitVec.ofNat 64 (kk - 1 - j) := by
        rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ix_wsub kk 1 (by omega) (by omega), ix_wsub (kk - 1) j (by omega) (by omega)]
      refine UD.specR_heapLoadI' (C := ctxH C H2) uwA _ (o2 + 1 + (kk - 1 - j)) _ hel (by decide)
        (by simp [sev]; rw [hsubw]; show _ = cellA C (o2 + 1 + (kk - 1 - j)); rw [← cellA_shl C (o2 + 1) (kk - 1 - j) (by omega), ← cellA_add8]; rfl) ?_
      refine specR_congr (m' := unwrapIdDefs C.fe fuel n args[kk - 1 - j] >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H2) uwR fUw uwParams [vv uwF, .op .sub [vv uwN, .const 1], vv uwA] (uwBody C)
        [BitVec.ofNat 64 fuel, BitVec.ofNat 64 n, Enc.idxW args[kk - 1 - j]] (by decide) rfl (by decide) hc.self
        ⟨by simp +decide [Env.get, uwParams, ctxEnv], by simp +decide [sev, Env.get, uwParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, by simp, trivial⟩
        (PostK (ctxH C H2)) (fun r_ w _ _ => w = Enc.idxW r_) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu uwParams _ rfl hlk) (ih H2 _ s2 hp2a (by omega)))
        (fun r w s3 H3 hp3 hw => ?_)
      subst hw
      exact specR_returnI _ (Enc.idxW r) (by simp) (fun t ht => ⟨H3, hp1.trans (hp2.trans hp3), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    · refine specR_envLoadI uwK (vv uwQ) o 2 (by decide) (by simp [ecell_ctxH]) hci.2 ?_
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ (Enc.idxW e) (by simp +decide [Env.get, uwParams, ctxEnv]) (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_envLoadI uwK (vv uwQ) o 3 (by decide) (by simp [ecell_ctxH]) hci.2.1 ?_
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ (Enc.idxW e) (by simp +decide [Env.get, uwParams, ctxEnv]) (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_envLoadI uwK (vv uwQ) o 4 (by decide) (by simp [ecell_ctxH]) hci.2.1 ?_
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ (Enc.idxW e) (by simp +decide [Env.get, uwParams, ctxEnv]) (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_envLoadI uwK (vv uwQ) o 5 (by decide) (by simp [ecell_ctxH]) hci.2.1 ?_
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ (Enc.idxW e) (by simp +decide [Env.get, uwParams, ctxEnv]) (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)



structure PvCodes (C : Ctx) : Prop where
  uw : UwCodes C
  self : C.code.lookup fPv = some (pvParams.map (fun p => (p, ShapeHOL.one)), pvBody C, .one)

theorem pv_spec (C : Ctx) (hok : CtxOK C) (hc : PvCodes C) (fuel : Nat) (hf : fuel < 2 ^ 62) :
    ∀ k (H : List (BitVec 64)) (e : EIdx) (s : AState), C.H <+: H → k < 2 ^ 64 →
      SpecR (σ := σ) (Pre (ctxH C H) s (pvParams.zip [BitVec.ofNat 64 fuel, BitVec.ofNat 64 k, Enc.idxW e])) (pvBody C) s
        (peelPisW C.fe fuel k e) (UD.PostO (ctxH C H)) := by
  intro k
  induction k with
  | zero =>
    intro H e s hpH _
    refine specR_prologue (UD.postO_locals _) (Knot.params_none _ pvLocals pvParams _ (by decide) (by decide)) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, pvParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    rw [peelPisW]
    refine specR_callNIH (C := ctxH C H) pvU fUw uwParams [vv pvF, .const 4, vv pvE] (uwBody C) [BitVec.ofNat 64 fuel, BitVec.ofNat 64 4, Enc.idxW e]
      (by decide) rfl (by decide) hc.uw.self ⟨by simp +decide [Env.get, pvParams, ctxEnv], rfl, by simp +decide [Env.get, pvParams, ctxEnv], trivial⟩
      (PostK (ctxH C H)) (fun r_ w _ _ => w = Enc.idxW r_) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu uwParams _ rfl hlk) (uw_spec C hok hc.uw fuel hf 4 H e s hpH (by decide)))
      (fun u w1 s1 H1 hp1 hw1 => ?_)
    subst hw1

    exact specR_returnI _ (optW (some u)) (by simp [sev, optWG]) (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro H e s hpH hk
    refine specR_prologue (UD.postO_locals _) (Knot.params_none _ pvLocals pvParams _ (by decide) (by decide)) ?_
    have hne : BitVec.ofNat 64 (k + 1) ≠ 0 := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, pvParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
    rw [peelPisW]
    refine Knot.specR_tagIteV pvE e 6 (by decide) (by decide) (by simp +decide [Env.get, pvParams, ctxEnv]) (fun htg => ?_) (fun htg => ?_)
    · rw [if_pos (show (e.tag == ETag.forallE) = true by simp [htg, ETag.forallE])]
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv pvE) (Enc.idxW e) (by decide) (by simp +decide [Env.get, pvParams, ctxEnv]) ?_
      refine specR_viewP (C := ctxH C H) e (by simp) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
        (fun v P hv' htn _ => ?_)
      have h6 : v.tagN = 6 := by rw [htn, htg]; rfl
      obtain ⟨ty, b, rfl⟩ : ∃ ty b, v = .forallE ty b := by cases v <;> simp [ENodeView.tagN] at h6 ⊢
      have hvb : s.store.viewBind e = some (ty, b) := viewBind_of_view_forallE (by rw [htg]; rfl) hv'
      refine specR_runBind (by rw [viewBind_run, hvb]) ?_
      dsimp only
      refine specR_loadI' pvB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      refine specR_congr (m' := peelPisW C.fe fuel k b >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H) pvR fPv pvParams [vv pvF, .op .sub [vv pvK, .const 1], vv pvB] (pvBody C)
        [BitVec.ofNat 64 fuel, BitVec.ofNat 64 k, Enc.idxW b] (by decide) rfl (by decide) hc.self
        ⟨by simp +decide [Env.get, pvParams, ctxEnv], by simp +decide [sev, Env.get, pvParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, by simp, trivial⟩
        (UD.PostO (ctxH C H)) (fun r_ w _ _ => w = optW r_) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pvParams _ rfl hlk) (ih H b s hpH (by omega)))
        (fun r w s2 H2 hp2 hw => ?_)
      subst hw
      exact specR_returnI _ (optW r) (by simp) (fun t ht => ⟨H2, hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    rw [if_neg (show ¬ (e.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg)]
    refine specR_callNIH (C := ctxH C H) pvU fUw uwParams [vv pvF, .const 4, vv pvE] (uwBody C) [BitVec.ofNat 64 fuel, BitVec.ofNat 64 4, Enc.idxW e]
      (by decide) rfl (by decide) hc.uw.self ⟨by simp +decide [Env.get, pvParams, ctxEnv], rfl, by simp +decide [Env.get, pvParams, ctxEnv], trivial⟩
      (PostK (ctxH C H)) (fun r_ w _ _ => w = Enc.idxW r_) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu uwParams _ rfl hlk) (uw_spec C hok hc.uw fuel hf 4 H e s hpH (by decide)))
      (fun u w1 s1 H1 hp1 hw1 => ?_)
    subst hw1

    refine Knot.specR_tagIteV pvU u 6 (by decide) (by decide) (by simp) (fun htu => ?_) (fun htu => ?_)
    · rw [if_pos (show (u.tag == ETag.forallE) = true by simp [htu, ETag.forallE])]
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv pvU) (Enc.idxW u) (by decide) (by simp +decide [Env.get, pvParams, ctxEnv]) ?_
      refine specR_viewP (C := ctxH C H1) u (by simp) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
        (fun v P hv' htn _ => ?_)
      have h6 : v.tagN = 6 := by rw [htn, htu]; rfl
      obtain ⟨ty, b, rfl⟩ : ∃ ty b, v = .forallE ty b := by cases v <;> simp [ENodeView.tagN] at h6 ⊢
      have hvb : s1.store.viewBind u = some (ty, b) := viewBind_of_view_forallE (by rw [htu]; rfl) hv'
      refine specR_runBind (by rw [viewBind_run, hvb]) ?_
      dsimp only
      refine specR_loadI' pvB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      refine specR_congr (m' := peelPisW C.fe fuel k b >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H1) pvR fPv pvParams [vv pvF, .op .sub [vv pvK, .const 1], vv pvB] (pvBody C)
        [BitVec.ofNat 64 fuel, BitVec.ofNat 64 k, Enc.idxW b] (by decide) rfl (by decide) hc.self
        ⟨by simp +decide [Env.get, pvParams, ctxEnv], by simp +decide [sev, Env.get, pvParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, by simp, trivial⟩
        (UD.PostO (ctxH C H1)) (fun r_ w _ _ => w = optW r_) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pvParams _ rfl hlk) (ih H1 b s1 (hpH.trans hp1) (by omega)))
        (fun r w s2 H2 hp2 hw => ?_)
      subst hw
      exact specR_returnI _ (optW r) (by simp) (fun t ht => ⟨H2, hp1.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    rw [if_neg (show ¬ (u.tag == ETag.forallE) = true by simpa [ETag.forallE] using htu)]
    exact specR_returnI _ (optW none) (by simp [optWG]; rfl) (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)


end

end ConPanqueque.T.WC
