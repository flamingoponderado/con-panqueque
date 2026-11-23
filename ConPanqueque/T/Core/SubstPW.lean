import ConPanqueque.T.Core.ZpsCollect
import ConPanqueque.T.Core.ArgFind
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `substPW` over a parameter-name block

A `PropWhen` datum in the port (`pwEnc`): `never` the word `1`, `ifAllZero ps` a block of the parameters' name
handles. `sb` walks the datum's names: each is looked up among the level parameters (`argFind`); a missing one
stays, a found one's argument is `never` (answer `1`) or contributes its own parameters (`zc`).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc
open ConLeche (Level Name)

def sbP := ofString "spw_sbp"
def sbI := ofString "spw_sbi"
def sbN := ofString "spw_sbn"
def sbK := ofString "spw_sbk"
def sbL := ofString "spw_sbl"
def sbU := ofString "spw_sbu"
def sbA := ofString "spw_sba"
def sbX := ofString "spw_sbx"
def sbJ := ofString "spw_sbj"
def sbV := ofString "spw_sbv"
def sbZ := ofString "spw_sbz"
def sbA2 := ofString "spw_sba2"
def sbR := ofString "spw_sbr"
def fSb := ofString "substPWGo"

@[simp] theorem spw_sbP_ne_sbI : sbP ≠ sbI := by decide
@[simp] theorem spw_sbP_ne_sbN : sbP ≠ sbN := by decide
@[simp] theorem spw_sbP_ne_sbK : sbP ≠ sbK := by decide
@[simp] theorem spw_sbP_ne_sbL : sbP ≠ sbL := by decide
@[simp] theorem spw_sbP_ne_sbU : sbP ≠ sbU := by decide
@[simp] theorem spw_sbP_ne_sbA : sbP ≠ sbA := by decide
@[simp] theorem spw_sbP_ne_sbX : sbP ≠ sbX := by decide
@[simp] theorem spw_sbP_ne_sbJ : sbP ≠ sbJ := by decide
@[simp] theorem spw_sbP_ne_sbV : sbP ≠ sbV := by decide
@[simp] theorem spw_sbP_ne_sbZ : sbP ≠ sbZ := by decide
@[simp] theorem spw_sbP_ne_sbA2 : sbP ≠ sbA2 := by decide
@[simp] theorem spw_sbP_ne_sbR : sbP ≠ sbR := by decide
@[simp] theorem spw_sbP_ne_lFl : sbP ≠ lFl := by decide
@[simp] theorem spw_lFl_ne_sbP : lFl ≠ sbP := by decide
@[simp] theorem spw_sbP_ne_lDh : sbP ≠ lDh := by decide
@[simp] theorem spw_lDh_ne_sbP : lDh ≠ sbP := by decide
@[simp] theorem spw_sbP_ne_lDt : sbP ≠ lDt := by decide
@[simp] theorem spw_lDt_ne_sbP : lDt ≠ sbP := by decide
@[simp] theorem spw_sbP_ne_lDg : sbP ≠ lDg := by decide
@[simp] theorem spw_lDg_ne_sbP : lDg ≠ sbP := by decide
@[simp] theorem spw_sbP_ne_lDi : sbP ≠ lDi := by decide
@[simp] theorem spw_lDi_ne_sbP : lDi ≠ sbP := by decide
@[simp] theorem spw_sbP_ne_lRp : sbP ≠ lRp := by decide
@[simp] theorem spw_lRp_ne_sbP : lRp ≠ sbP := by decide
@[simp] theorem spw_sbP_ne_lRn : sbP ≠ lRn := by decide
@[simp] theorem spw_lRn_ne_sbP : lRn ≠ sbP := by decide
@[simp] theorem spw_sbP_ne_lFle : sbP ≠ lFle := by decide
@[simp] theorem spw_lFle_ne_sbP : lFle ≠ sbP := by decide
@[simp] theorem spw_sbP_ne_lKb : sbP ≠ lKb := by decide
@[simp] theorem spw_lKb_ne_sbP : lKb ≠ sbP := by decide
@[simp] theorem spw_sbP_ne_lDir : sbP ≠ lDir := by decide
@[simp] theorem spw_lDir_ne_sbP : lDir ≠ sbP := by decide
@[simp] theorem spw_sbP_ne_lFln : sbP ≠ lFln := by decide
@[simp] theorem spw_lFln_ne_sbP : lFln ≠ sbP := by decide
@[simp] theorem spw_sbP_ne_lFll : sbP ≠ lFll := by decide
@[simp] theorem spw_lFll_ne_sbP : lFll ≠ sbP := by decide
@[simp] theorem spw_sbP_ne_lFls : sbP ≠ lFls := by decide
@[simp] theorem spw_lFls_ne_sbP : lFls ≠ sbP := by decide
@[simp] theorem spw_sbP_ne_kFu : sbP ≠ kFu := by decide
@[simp] theorem spw_kFu_ne_sbP : kFu ≠ sbP := by decide
@[simp] theorem spw_sbP_ne_kD : sbP ≠ kD := by decide
@[simp] theorem spw_kD_ne_sbP : kD ≠ sbP := by decide
@[simp] theorem spw_sbI_ne_sbP : sbI ≠ sbP := by decide
@[simp] theorem spw_sbI_ne_sbN : sbI ≠ sbN := by decide
@[simp] theorem spw_sbI_ne_sbK : sbI ≠ sbK := by decide
@[simp] theorem spw_sbI_ne_sbL : sbI ≠ sbL := by decide
@[simp] theorem spw_sbI_ne_sbU : sbI ≠ sbU := by decide
@[simp] theorem spw_sbI_ne_sbA : sbI ≠ sbA := by decide
@[simp] theorem spw_sbI_ne_sbX : sbI ≠ sbX := by decide
@[simp] theorem spw_sbI_ne_sbJ : sbI ≠ sbJ := by decide
@[simp] theorem spw_sbI_ne_sbV : sbI ≠ sbV := by decide
@[simp] theorem spw_sbI_ne_sbZ : sbI ≠ sbZ := by decide
@[simp] theorem spw_sbI_ne_sbA2 : sbI ≠ sbA2 := by decide
@[simp] theorem spw_sbI_ne_sbR : sbI ≠ sbR := by decide
@[simp] theorem spw_sbI_ne_lFl : sbI ≠ lFl := by decide
@[simp] theorem spw_lFl_ne_sbI : lFl ≠ sbI := by decide
@[simp] theorem spw_sbI_ne_lDh : sbI ≠ lDh := by decide
@[simp] theorem spw_lDh_ne_sbI : lDh ≠ sbI := by decide
@[simp] theorem spw_sbI_ne_lDt : sbI ≠ lDt := by decide
@[simp] theorem spw_lDt_ne_sbI : lDt ≠ sbI := by decide
@[simp] theorem spw_sbI_ne_lDg : sbI ≠ lDg := by decide
@[simp] theorem spw_lDg_ne_sbI : lDg ≠ sbI := by decide
@[simp] theorem spw_sbI_ne_lDi : sbI ≠ lDi := by decide
@[simp] theorem spw_lDi_ne_sbI : lDi ≠ sbI := by decide
@[simp] theorem spw_sbI_ne_lRp : sbI ≠ lRp := by decide
@[simp] theorem spw_lRp_ne_sbI : lRp ≠ sbI := by decide
@[simp] theorem spw_sbI_ne_lRn : sbI ≠ lRn := by decide
@[simp] theorem spw_lRn_ne_sbI : lRn ≠ sbI := by decide
@[simp] theorem spw_sbI_ne_lFle : sbI ≠ lFle := by decide
@[simp] theorem spw_lFle_ne_sbI : lFle ≠ sbI := by decide
@[simp] theorem spw_sbI_ne_lKb : sbI ≠ lKb := by decide
@[simp] theorem spw_lKb_ne_sbI : lKb ≠ sbI := by decide
@[simp] theorem spw_sbI_ne_lDir : sbI ≠ lDir := by decide
@[simp] theorem spw_lDir_ne_sbI : lDir ≠ sbI := by decide
@[simp] theorem spw_sbI_ne_lFln : sbI ≠ lFln := by decide
@[simp] theorem spw_lFln_ne_sbI : lFln ≠ sbI := by decide
@[simp] theorem spw_sbI_ne_lFll : sbI ≠ lFll := by decide
@[simp] theorem spw_lFll_ne_sbI : lFll ≠ sbI := by decide
@[simp] theorem spw_sbI_ne_lFls : sbI ≠ lFls := by decide
@[simp] theorem spw_lFls_ne_sbI : lFls ≠ sbI := by decide
@[simp] theorem spw_sbI_ne_kFu : sbI ≠ kFu := by decide
@[simp] theorem spw_kFu_ne_sbI : kFu ≠ sbI := by decide
@[simp] theorem spw_sbI_ne_kD : sbI ≠ kD := by decide
@[simp] theorem spw_kD_ne_sbI : kD ≠ sbI := by decide
@[simp] theorem spw_sbN_ne_sbP : sbN ≠ sbP := by decide
@[simp] theorem spw_sbN_ne_sbI : sbN ≠ sbI := by decide
@[simp] theorem spw_sbN_ne_sbK : sbN ≠ sbK := by decide
@[simp] theorem spw_sbN_ne_sbL : sbN ≠ sbL := by decide
@[simp] theorem spw_sbN_ne_sbU : sbN ≠ sbU := by decide
@[simp] theorem spw_sbN_ne_sbA : sbN ≠ sbA := by decide
@[simp] theorem spw_sbN_ne_sbX : sbN ≠ sbX := by decide
@[simp] theorem spw_sbN_ne_sbJ : sbN ≠ sbJ := by decide
@[simp] theorem spw_sbN_ne_sbV : sbN ≠ sbV := by decide
@[simp] theorem spw_sbN_ne_sbZ : sbN ≠ sbZ := by decide
@[simp] theorem spw_sbN_ne_sbA2 : sbN ≠ sbA2 := by decide
@[simp] theorem spw_sbN_ne_sbR : sbN ≠ sbR := by decide
@[simp] theorem spw_sbN_ne_lFl : sbN ≠ lFl := by decide
@[simp] theorem spw_lFl_ne_sbN : lFl ≠ sbN := by decide
@[simp] theorem spw_sbN_ne_lDh : sbN ≠ lDh := by decide
@[simp] theorem spw_lDh_ne_sbN : lDh ≠ sbN := by decide
@[simp] theorem spw_sbN_ne_lDt : sbN ≠ lDt := by decide
@[simp] theorem spw_lDt_ne_sbN : lDt ≠ sbN := by decide
@[simp] theorem spw_sbN_ne_lDg : sbN ≠ lDg := by decide
@[simp] theorem spw_lDg_ne_sbN : lDg ≠ sbN := by decide
@[simp] theorem spw_sbN_ne_lDi : sbN ≠ lDi := by decide
@[simp] theorem spw_lDi_ne_sbN : lDi ≠ sbN := by decide
@[simp] theorem spw_sbN_ne_lRp : sbN ≠ lRp := by decide
@[simp] theorem spw_lRp_ne_sbN : lRp ≠ sbN := by decide
@[simp] theorem spw_sbN_ne_lRn : sbN ≠ lRn := by decide
@[simp] theorem spw_lRn_ne_sbN : lRn ≠ sbN := by decide
@[simp] theorem spw_sbN_ne_lFle : sbN ≠ lFle := by decide
@[simp] theorem spw_lFle_ne_sbN : lFle ≠ sbN := by decide
@[simp] theorem spw_sbN_ne_lKb : sbN ≠ lKb := by decide
@[simp] theorem spw_lKb_ne_sbN : lKb ≠ sbN := by decide
@[simp] theorem spw_sbN_ne_lDir : sbN ≠ lDir := by decide
@[simp] theorem spw_lDir_ne_sbN : lDir ≠ sbN := by decide
@[simp] theorem spw_sbN_ne_lFln : sbN ≠ lFln := by decide
@[simp] theorem spw_lFln_ne_sbN : lFln ≠ sbN := by decide
@[simp] theorem spw_sbN_ne_lFll : sbN ≠ lFll := by decide
@[simp] theorem spw_lFll_ne_sbN : lFll ≠ sbN := by decide
@[simp] theorem spw_sbN_ne_lFls : sbN ≠ lFls := by decide
@[simp] theorem spw_lFls_ne_sbN : lFls ≠ sbN := by decide
@[simp] theorem spw_sbN_ne_kFu : sbN ≠ kFu := by decide
@[simp] theorem spw_kFu_ne_sbN : kFu ≠ sbN := by decide
@[simp] theorem spw_sbN_ne_kD : sbN ≠ kD := by decide
@[simp] theorem spw_kD_ne_sbN : kD ≠ sbN := by decide
@[simp] theorem spw_sbK_ne_sbP : sbK ≠ sbP := by decide
@[simp] theorem spw_sbK_ne_sbI : sbK ≠ sbI := by decide
@[simp] theorem spw_sbK_ne_sbN : sbK ≠ sbN := by decide
@[simp] theorem spw_sbK_ne_sbL : sbK ≠ sbL := by decide
@[simp] theorem spw_sbK_ne_sbU : sbK ≠ sbU := by decide
@[simp] theorem spw_sbK_ne_sbA : sbK ≠ sbA := by decide
@[simp] theorem spw_sbK_ne_sbX : sbK ≠ sbX := by decide
@[simp] theorem spw_sbK_ne_sbJ : sbK ≠ sbJ := by decide
@[simp] theorem spw_sbK_ne_sbV : sbK ≠ sbV := by decide
@[simp] theorem spw_sbK_ne_sbZ : sbK ≠ sbZ := by decide
@[simp] theorem spw_sbK_ne_sbA2 : sbK ≠ sbA2 := by decide
@[simp] theorem spw_sbK_ne_sbR : sbK ≠ sbR := by decide
@[simp] theorem spw_sbK_ne_lFl : sbK ≠ lFl := by decide
@[simp] theorem spw_lFl_ne_sbK : lFl ≠ sbK := by decide
@[simp] theorem spw_sbK_ne_lDh : sbK ≠ lDh := by decide
@[simp] theorem spw_lDh_ne_sbK : lDh ≠ sbK := by decide
@[simp] theorem spw_sbK_ne_lDt : sbK ≠ lDt := by decide
@[simp] theorem spw_lDt_ne_sbK : lDt ≠ sbK := by decide
@[simp] theorem spw_sbK_ne_lDg : sbK ≠ lDg := by decide
@[simp] theorem spw_lDg_ne_sbK : lDg ≠ sbK := by decide
@[simp] theorem spw_sbK_ne_lDi : sbK ≠ lDi := by decide
@[simp] theorem spw_lDi_ne_sbK : lDi ≠ sbK := by decide
@[simp] theorem spw_sbK_ne_lRp : sbK ≠ lRp := by decide
@[simp] theorem spw_lRp_ne_sbK : lRp ≠ sbK := by decide
@[simp] theorem spw_sbK_ne_lRn : sbK ≠ lRn := by decide
@[simp] theorem spw_lRn_ne_sbK : lRn ≠ sbK := by decide
@[simp] theorem spw_sbK_ne_lFle : sbK ≠ lFle := by decide
@[simp] theorem spw_lFle_ne_sbK : lFle ≠ sbK := by decide
@[simp] theorem spw_sbK_ne_lKb : sbK ≠ lKb := by decide
@[simp] theorem spw_lKb_ne_sbK : lKb ≠ sbK := by decide
@[simp] theorem spw_sbK_ne_lDir : sbK ≠ lDir := by decide
@[simp] theorem spw_lDir_ne_sbK : lDir ≠ sbK := by decide
@[simp] theorem spw_sbK_ne_lFln : sbK ≠ lFln := by decide
@[simp] theorem spw_lFln_ne_sbK : lFln ≠ sbK := by decide
@[simp] theorem spw_sbK_ne_lFll : sbK ≠ lFll := by decide
@[simp] theorem spw_lFll_ne_sbK : lFll ≠ sbK := by decide
@[simp] theorem spw_sbK_ne_lFls : sbK ≠ lFls := by decide
@[simp] theorem spw_lFls_ne_sbK : lFls ≠ sbK := by decide
@[simp] theorem spw_sbK_ne_kFu : sbK ≠ kFu := by decide
@[simp] theorem spw_kFu_ne_sbK : kFu ≠ sbK := by decide
@[simp] theorem spw_sbK_ne_kD : sbK ≠ kD := by decide
@[simp] theorem spw_kD_ne_sbK : kD ≠ sbK := by decide
@[simp] theorem spw_sbL_ne_sbP : sbL ≠ sbP := by decide
@[simp] theorem spw_sbL_ne_sbI : sbL ≠ sbI := by decide
@[simp] theorem spw_sbL_ne_sbN : sbL ≠ sbN := by decide
@[simp] theorem spw_sbL_ne_sbK : sbL ≠ sbK := by decide
@[simp] theorem spw_sbL_ne_sbU : sbL ≠ sbU := by decide
@[simp] theorem spw_sbL_ne_sbA : sbL ≠ sbA := by decide
@[simp] theorem spw_sbL_ne_sbX : sbL ≠ sbX := by decide
@[simp] theorem spw_sbL_ne_sbJ : sbL ≠ sbJ := by decide
@[simp] theorem spw_sbL_ne_sbV : sbL ≠ sbV := by decide
@[simp] theorem spw_sbL_ne_sbZ : sbL ≠ sbZ := by decide
@[simp] theorem spw_sbL_ne_sbA2 : sbL ≠ sbA2 := by decide
@[simp] theorem spw_sbL_ne_sbR : sbL ≠ sbR := by decide
@[simp] theorem spw_sbL_ne_lFl : sbL ≠ lFl := by decide
@[simp] theorem spw_lFl_ne_sbL : lFl ≠ sbL := by decide
@[simp] theorem spw_sbL_ne_lDh : sbL ≠ lDh := by decide
@[simp] theorem spw_lDh_ne_sbL : lDh ≠ sbL := by decide
@[simp] theorem spw_sbL_ne_lDt : sbL ≠ lDt := by decide
@[simp] theorem spw_lDt_ne_sbL : lDt ≠ sbL := by decide
@[simp] theorem spw_sbL_ne_lDg : sbL ≠ lDg := by decide
@[simp] theorem spw_lDg_ne_sbL : lDg ≠ sbL := by decide
@[simp] theorem spw_sbL_ne_lDi : sbL ≠ lDi := by decide
@[simp] theorem spw_lDi_ne_sbL : lDi ≠ sbL := by decide
@[simp] theorem spw_sbL_ne_lRp : sbL ≠ lRp := by decide
@[simp] theorem spw_lRp_ne_sbL : lRp ≠ sbL := by decide
@[simp] theorem spw_sbL_ne_lRn : sbL ≠ lRn := by decide
@[simp] theorem spw_lRn_ne_sbL : lRn ≠ sbL := by decide
@[simp] theorem spw_sbL_ne_lFle : sbL ≠ lFle := by decide
@[simp] theorem spw_lFle_ne_sbL : lFle ≠ sbL := by decide
@[simp] theorem spw_sbL_ne_lKb : sbL ≠ lKb := by decide
@[simp] theorem spw_lKb_ne_sbL : lKb ≠ sbL := by decide
@[simp] theorem spw_sbL_ne_lDir : sbL ≠ lDir := by decide
@[simp] theorem spw_lDir_ne_sbL : lDir ≠ sbL := by decide
@[simp] theorem spw_sbL_ne_lFln : sbL ≠ lFln := by decide
@[simp] theorem spw_lFln_ne_sbL : lFln ≠ sbL := by decide
@[simp] theorem spw_sbL_ne_lFll : sbL ≠ lFll := by decide
@[simp] theorem spw_lFll_ne_sbL : lFll ≠ sbL := by decide
@[simp] theorem spw_sbL_ne_lFls : sbL ≠ lFls := by decide
@[simp] theorem spw_lFls_ne_sbL : lFls ≠ sbL := by decide
@[simp] theorem spw_sbL_ne_kFu : sbL ≠ kFu := by decide
@[simp] theorem spw_kFu_ne_sbL : kFu ≠ sbL := by decide
@[simp] theorem spw_sbL_ne_kD : sbL ≠ kD := by decide
@[simp] theorem spw_kD_ne_sbL : kD ≠ sbL := by decide
@[simp] theorem spw_sbU_ne_sbP : sbU ≠ sbP := by decide
@[simp] theorem spw_sbU_ne_sbI : sbU ≠ sbI := by decide
@[simp] theorem spw_sbU_ne_sbN : sbU ≠ sbN := by decide
@[simp] theorem spw_sbU_ne_sbK : sbU ≠ sbK := by decide
@[simp] theorem spw_sbU_ne_sbL : sbU ≠ sbL := by decide
@[simp] theorem spw_sbU_ne_sbA : sbU ≠ sbA := by decide
@[simp] theorem spw_sbU_ne_sbX : sbU ≠ sbX := by decide
@[simp] theorem spw_sbU_ne_sbJ : sbU ≠ sbJ := by decide
@[simp] theorem spw_sbU_ne_sbV : sbU ≠ sbV := by decide
@[simp] theorem spw_sbU_ne_sbZ : sbU ≠ sbZ := by decide
@[simp] theorem spw_sbU_ne_sbA2 : sbU ≠ sbA2 := by decide
@[simp] theorem spw_sbU_ne_sbR : sbU ≠ sbR := by decide
@[simp] theorem spw_sbU_ne_lFl : sbU ≠ lFl := by decide
@[simp] theorem spw_lFl_ne_sbU : lFl ≠ sbU := by decide
@[simp] theorem spw_sbU_ne_lDh : sbU ≠ lDh := by decide
@[simp] theorem spw_lDh_ne_sbU : lDh ≠ sbU := by decide
@[simp] theorem spw_sbU_ne_lDt : sbU ≠ lDt := by decide
@[simp] theorem spw_lDt_ne_sbU : lDt ≠ sbU := by decide
@[simp] theorem spw_sbU_ne_lDg : sbU ≠ lDg := by decide
@[simp] theorem spw_lDg_ne_sbU : lDg ≠ sbU := by decide
@[simp] theorem spw_sbU_ne_lDi : sbU ≠ lDi := by decide
@[simp] theorem spw_lDi_ne_sbU : lDi ≠ sbU := by decide
@[simp] theorem spw_sbU_ne_lRp : sbU ≠ lRp := by decide
@[simp] theorem spw_lRp_ne_sbU : lRp ≠ sbU := by decide
@[simp] theorem spw_sbU_ne_lRn : sbU ≠ lRn := by decide
@[simp] theorem spw_lRn_ne_sbU : lRn ≠ sbU := by decide
@[simp] theorem spw_sbU_ne_lFle : sbU ≠ lFle := by decide
@[simp] theorem spw_lFle_ne_sbU : lFle ≠ sbU := by decide
@[simp] theorem spw_sbU_ne_lKb : sbU ≠ lKb := by decide
@[simp] theorem spw_lKb_ne_sbU : lKb ≠ sbU := by decide
@[simp] theorem spw_sbU_ne_lDir : sbU ≠ lDir := by decide
@[simp] theorem spw_lDir_ne_sbU : lDir ≠ sbU := by decide
@[simp] theorem spw_sbU_ne_lFln : sbU ≠ lFln := by decide
@[simp] theorem spw_lFln_ne_sbU : lFln ≠ sbU := by decide
@[simp] theorem spw_sbU_ne_lFll : sbU ≠ lFll := by decide
@[simp] theorem spw_lFll_ne_sbU : lFll ≠ sbU := by decide
@[simp] theorem spw_sbU_ne_lFls : sbU ≠ lFls := by decide
@[simp] theorem spw_lFls_ne_sbU : lFls ≠ sbU := by decide
@[simp] theorem spw_sbU_ne_kFu : sbU ≠ kFu := by decide
@[simp] theorem spw_kFu_ne_sbU : kFu ≠ sbU := by decide
@[simp] theorem spw_sbU_ne_kD : sbU ≠ kD := by decide
@[simp] theorem spw_kD_ne_sbU : kD ≠ sbU := by decide
@[simp] theorem spw_sbA_ne_sbP : sbA ≠ sbP := by decide
@[simp] theorem spw_sbA_ne_sbI : sbA ≠ sbI := by decide
@[simp] theorem spw_sbA_ne_sbN : sbA ≠ sbN := by decide
@[simp] theorem spw_sbA_ne_sbK : sbA ≠ sbK := by decide
@[simp] theorem spw_sbA_ne_sbL : sbA ≠ sbL := by decide
@[simp] theorem spw_sbA_ne_sbU : sbA ≠ sbU := by decide
@[simp] theorem spw_sbA_ne_sbX : sbA ≠ sbX := by decide
@[simp] theorem spw_sbA_ne_sbJ : sbA ≠ sbJ := by decide
@[simp] theorem spw_sbA_ne_sbV : sbA ≠ sbV := by decide
@[simp] theorem spw_sbA_ne_sbZ : sbA ≠ sbZ := by decide
@[simp] theorem spw_sbA_ne_sbA2 : sbA ≠ sbA2 := by decide
@[simp] theorem spw_sbA_ne_sbR : sbA ≠ sbR := by decide
@[simp] theorem spw_sbA_ne_lFl : sbA ≠ lFl := by decide
@[simp] theorem spw_lFl_ne_sbA : lFl ≠ sbA := by decide
@[simp] theorem spw_sbA_ne_lDh : sbA ≠ lDh := by decide
@[simp] theorem spw_lDh_ne_sbA : lDh ≠ sbA := by decide
@[simp] theorem spw_sbA_ne_lDt : sbA ≠ lDt := by decide
@[simp] theorem spw_lDt_ne_sbA : lDt ≠ sbA := by decide
@[simp] theorem spw_sbA_ne_lDg : sbA ≠ lDg := by decide
@[simp] theorem spw_lDg_ne_sbA : lDg ≠ sbA := by decide
@[simp] theorem spw_sbA_ne_lDi : sbA ≠ lDi := by decide
@[simp] theorem spw_lDi_ne_sbA : lDi ≠ sbA := by decide
@[simp] theorem spw_sbA_ne_lRp : sbA ≠ lRp := by decide
@[simp] theorem spw_lRp_ne_sbA : lRp ≠ sbA := by decide
@[simp] theorem spw_sbA_ne_lRn : sbA ≠ lRn := by decide
@[simp] theorem spw_lRn_ne_sbA : lRn ≠ sbA := by decide
@[simp] theorem spw_sbA_ne_lFle : sbA ≠ lFle := by decide
@[simp] theorem spw_lFle_ne_sbA : lFle ≠ sbA := by decide
@[simp] theorem spw_sbA_ne_lKb : sbA ≠ lKb := by decide
@[simp] theorem spw_lKb_ne_sbA : lKb ≠ sbA := by decide
@[simp] theorem spw_sbA_ne_lDir : sbA ≠ lDir := by decide
@[simp] theorem spw_lDir_ne_sbA : lDir ≠ sbA := by decide
@[simp] theorem spw_sbA_ne_lFln : sbA ≠ lFln := by decide
@[simp] theorem spw_lFln_ne_sbA : lFln ≠ sbA := by decide
@[simp] theorem spw_sbA_ne_lFll : sbA ≠ lFll := by decide
@[simp] theorem spw_lFll_ne_sbA : lFll ≠ sbA := by decide
@[simp] theorem spw_sbA_ne_lFls : sbA ≠ lFls := by decide
@[simp] theorem spw_lFls_ne_sbA : lFls ≠ sbA := by decide
@[simp] theorem spw_sbA_ne_kFu : sbA ≠ kFu := by decide
@[simp] theorem spw_kFu_ne_sbA : kFu ≠ sbA := by decide
@[simp] theorem spw_sbA_ne_kD : sbA ≠ kD := by decide
@[simp] theorem spw_kD_ne_sbA : kD ≠ sbA := by decide
@[simp] theorem spw_sbX_ne_sbP : sbX ≠ sbP := by decide
@[simp] theorem spw_sbX_ne_sbI : sbX ≠ sbI := by decide
@[simp] theorem spw_sbX_ne_sbN : sbX ≠ sbN := by decide
@[simp] theorem spw_sbX_ne_sbK : sbX ≠ sbK := by decide
@[simp] theorem spw_sbX_ne_sbL : sbX ≠ sbL := by decide
@[simp] theorem spw_sbX_ne_sbU : sbX ≠ sbU := by decide
@[simp] theorem spw_sbX_ne_sbA : sbX ≠ sbA := by decide
@[simp] theorem spw_sbX_ne_sbJ : sbX ≠ sbJ := by decide
@[simp] theorem spw_sbX_ne_sbV : sbX ≠ sbV := by decide
@[simp] theorem spw_sbX_ne_sbZ : sbX ≠ sbZ := by decide
@[simp] theorem spw_sbX_ne_sbA2 : sbX ≠ sbA2 := by decide
@[simp] theorem spw_sbX_ne_sbR : sbX ≠ sbR := by decide
@[simp] theorem spw_sbX_ne_lFl : sbX ≠ lFl := by decide
@[simp] theorem spw_lFl_ne_sbX : lFl ≠ sbX := by decide
@[simp] theorem spw_sbX_ne_lDh : sbX ≠ lDh := by decide
@[simp] theorem spw_lDh_ne_sbX : lDh ≠ sbX := by decide
@[simp] theorem spw_sbX_ne_lDt : sbX ≠ lDt := by decide
@[simp] theorem spw_lDt_ne_sbX : lDt ≠ sbX := by decide
@[simp] theorem spw_sbX_ne_lDg : sbX ≠ lDg := by decide
@[simp] theorem spw_lDg_ne_sbX : lDg ≠ sbX := by decide
@[simp] theorem spw_sbX_ne_lDi : sbX ≠ lDi := by decide
@[simp] theorem spw_lDi_ne_sbX : lDi ≠ sbX := by decide
@[simp] theorem spw_sbX_ne_lRp : sbX ≠ lRp := by decide
@[simp] theorem spw_lRp_ne_sbX : lRp ≠ sbX := by decide
@[simp] theorem spw_sbX_ne_lRn : sbX ≠ lRn := by decide
@[simp] theorem spw_lRn_ne_sbX : lRn ≠ sbX := by decide
@[simp] theorem spw_sbX_ne_lFle : sbX ≠ lFle := by decide
@[simp] theorem spw_lFle_ne_sbX : lFle ≠ sbX := by decide
@[simp] theorem spw_sbX_ne_lKb : sbX ≠ lKb := by decide
@[simp] theorem spw_lKb_ne_sbX : lKb ≠ sbX := by decide
@[simp] theorem spw_sbX_ne_lDir : sbX ≠ lDir := by decide
@[simp] theorem spw_lDir_ne_sbX : lDir ≠ sbX := by decide
@[simp] theorem spw_sbX_ne_lFln : sbX ≠ lFln := by decide
@[simp] theorem spw_lFln_ne_sbX : lFln ≠ sbX := by decide
@[simp] theorem spw_sbX_ne_lFll : sbX ≠ lFll := by decide
@[simp] theorem spw_lFll_ne_sbX : lFll ≠ sbX := by decide
@[simp] theorem spw_sbX_ne_lFls : sbX ≠ lFls := by decide
@[simp] theorem spw_lFls_ne_sbX : lFls ≠ sbX := by decide
@[simp] theorem spw_sbX_ne_kFu : sbX ≠ kFu := by decide
@[simp] theorem spw_kFu_ne_sbX : kFu ≠ sbX := by decide
@[simp] theorem spw_sbX_ne_kD : sbX ≠ kD := by decide
@[simp] theorem spw_kD_ne_sbX : kD ≠ sbX := by decide
@[simp] theorem spw_sbJ_ne_sbP : sbJ ≠ sbP := by decide
@[simp] theorem spw_sbJ_ne_sbI : sbJ ≠ sbI := by decide
@[simp] theorem spw_sbJ_ne_sbN : sbJ ≠ sbN := by decide
@[simp] theorem spw_sbJ_ne_sbK : sbJ ≠ sbK := by decide
@[simp] theorem spw_sbJ_ne_sbL : sbJ ≠ sbL := by decide
@[simp] theorem spw_sbJ_ne_sbU : sbJ ≠ sbU := by decide
@[simp] theorem spw_sbJ_ne_sbA : sbJ ≠ sbA := by decide
@[simp] theorem spw_sbJ_ne_sbX : sbJ ≠ sbX := by decide
@[simp] theorem spw_sbJ_ne_sbV : sbJ ≠ sbV := by decide
@[simp] theorem spw_sbJ_ne_sbZ : sbJ ≠ sbZ := by decide
@[simp] theorem spw_sbJ_ne_sbA2 : sbJ ≠ sbA2 := by decide
@[simp] theorem spw_sbJ_ne_sbR : sbJ ≠ sbR := by decide
@[simp] theorem spw_sbJ_ne_lFl : sbJ ≠ lFl := by decide
@[simp] theorem spw_lFl_ne_sbJ : lFl ≠ sbJ := by decide
@[simp] theorem spw_sbJ_ne_lDh : sbJ ≠ lDh := by decide
@[simp] theorem spw_lDh_ne_sbJ : lDh ≠ sbJ := by decide
@[simp] theorem spw_sbJ_ne_lDt : sbJ ≠ lDt := by decide
@[simp] theorem spw_lDt_ne_sbJ : lDt ≠ sbJ := by decide
@[simp] theorem spw_sbJ_ne_lDg : sbJ ≠ lDg := by decide
@[simp] theorem spw_lDg_ne_sbJ : lDg ≠ sbJ := by decide
@[simp] theorem spw_sbJ_ne_lDi : sbJ ≠ lDi := by decide
@[simp] theorem spw_lDi_ne_sbJ : lDi ≠ sbJ := by decide
@[simp] theorem spw_sbJ_ne_lRp : sbJ ≠ lRp := by decide
@[simp] theorem spw_lRp_ne_sbJ : lRp ≠ sbJ := by decide
@[simp] theorem spw_sbJ_ne_lRn : sbJ ≠ lRn := by decide
@[simp] theorem spw_lRn_ne_sbJ : lRn ≠ sbJ := by decide
@[simp] theorem spw_sbJ_ne_lFle : sbJ ≠ lFle := by decide
@[simp] theorem spw_lFle_ne_sbJ : lFle ≠ sbJ := by decide
@[simp] theorem spw_sbJ_ne_lKb : sbJ ≠ lKb := by decide
@[simp] theorem spw_lKb_ne_sbJ : lKb ≠ sbJ := by decide
@[simp] theorem spw_sbJ_ne_lDir : sbJ ≠ lDir := by decide
@[simp] theorem spw_lDir_ne_sbJ : lDir ≠ sbJ := by decide
@[simp] theorem spw_sbJ_ne_lFln : sbJ ≠ lFln := by decide
@[simp] theorem spw_lFln_ne_sbJ : lFln ≠ sbJ := by decide
@[simp] theorem spw_sbJ_ne_lFll : sbJ ≠ lFll := by decide
@[simp] theorem spw_lFll_ne_sbJ : lFll ≠ sbJ := by decide
@[simp] theorem spw_sbJ_ne_lFls : sbJ ≠ lFls := by decide
@[simp] theorem spw_lFls_ne_sbJ : lFls ≠ sbJ := by decide
@[simp] theorem spw_sbJ_ne_kFu : sbJ ≠ kFu := by decide
@[simp] theorem spw_kFu_ne_sbJ : kFu ≠ sbJ := by decide
@[simp] theorem spw_sbJ_ne_kD : sbJ ≠ kD := by decide
@[simp] theorem spw_kD_ne_sbJ : kD ≠ sbJ := by decide
@[simp] theorem spw_sbV_ne_sbP : sbV ≠ sbP := by decide
@[simp] theorem spw_sbV_ne_sbI : sbV ≠ sbI := by decide
@[simp] theorem spw_sbV_ne_sbN : sbV ≠ sbN := by decide
@[simp] theorem spw_sbV_ne_sbK : sbV ≠ sbK := by decide
@[simp] theorem spw_sbV_ne_sbL : sbV ≠ sbL := by decide
@[simp] theorem spw_sbV_ne_sbU : sbV ≠ sbU := by decide
@[simp] theorem spw_sbV_ne_sbA : sbV ≠ sbA := by decide
@[simp] theorem spw_sbV_ne_sbX : sbV ≠ sbX := by decide
@[simp] theorem spw_sbV_ne_sbJ : sbV ≠ sbJ := by decide
@[simp] theorem spw_sbV_ne_sbZ : sbV ≠ sbZ := by decide
@[simp] theorem spw_sbV_ne_sbA2 : sbV ≠ sbA2 := by decide
@[simp] theorem spw_sbV_ne_sbR : sbV ≠ sbR := by decide
@[simp] theorem spw_sbV_ne_lFl : sbV ≠ lFl := by decide
@[simp] theorem spw_lFl_ne_sbV : lFl ≠ sbV := by decide
@[simp] theorem spw_sbV_ne_lDh : sbV ≠ lDh := by decide
@[simp] theorem spw_lDh_ne_sbV : lDh ≠ sbV := by decide
@[simp] theorem spw_sbV_ne_lDt : sbV ≠ lDt := by decide
@[simp] theorem spw_lDt_ne_sbV : lDt ≠ sbV := by decide
@[simp] theorem spw_sbV_ne_lDg : sbV ≠ lDg := by decide
@[simp] theorem spw_lDg_ne_sbV : lDg ≠ sbV := by decide
@[simp] theorem spw_sbV_ne_lDi : sbV ≠ lDi := by decide
@[simp] theorem spw_lDi_ne_sbV : lDi ≠ sbV := by decide
@[simp] theorem spw_sbV_ne_lRp : sbV ≠ lRp := by decide
@[simp] theorem spw_lRp_ne_sbV : lRp ≠ sbV := by decide
@[simp] theorem spw_sbV_ne_lRn : sbV ≠ lRn := by decide
@[simp] theorem spw_lRn_ne_sbV : lRn ≠ sbV := by decide
@[simp] theorem spw_sbV_ne_lFle : sbV ≠ lFle := by decide
@[simp] theorem spw_lFle_ne_sbV : lFle ≠ sbV := by decide
@[simp] theorem spw_sbV_ne_lKb : sbV ≠ lKb := by decide
@[simp] theorem spw_lKb_ne_sbV : lKb ≠ sbV := by decide
@[simp] theorem spw_sbV_ne_lDir : sbV ≠ lDir := by decide
@[simp] theorem spw_lDir_ne_sbV : lDir ≠ sbV := by decide
@[simp] theorem spw_sbV_ne_lFln : sbV ≠ lFln := by decide
@[simp] theorem spw_lFln_ne_sbV : lFln ≠ sbV := by decide
@[simp] theorem spw_sbV_ne_lFll : sbV ≠ lFll := by decide
@[simp] theorem spw_lFll_ne_sbV : lFll ≠ sbV := by decide
@[simp] theorem spw_sbV_ne_lFls : sbV ≠ lFls := by decide
@[simp] theorem spw_lFls_ne_sbV : lFls ≠ sbV := by decide
@[simp] theorem spw_sbV_ne_kFu : sbV ≠ kFu := by decide
@[simp] theorem spw_kFu_ne_sbV : kFu ≠ sbV := by decide
@[simp] theorem spw_sbV_ne_kD : sbV ≠ kD := by decide
@[simp] theorem spw_kD_ne_sbV : kD ≠ sbV := by decide
@[simp] theorem spw_sbZ_ne_sbP : sbZ ≠ sbP := by decide
@[simp] theorem spw_sbZ_ne_sbI : sbZ ≠ sbI := by decide
@[simp] theorem spw_sbZ_ne_sbN : sbZ ≠ sbN := by decide
@[simp] theorem spw_sbZ_ne_sbK : sbZ ≠ sbK := by decide
@[simp] theorem spw_sbZ_ne_sbL : sbZ ≠ sbL := by decide
@[simp] theorem spw_sbZ_ne_sbU : sbZ ≠ sbU := by decide
@[simp] theorem spw_sbZ_ne_sbA : sbZ ≠ sbA := by decide
@[simp] theorem spw_sbZ_ne_sbX : sbZ ≠ sbX := by decide
@[simp] theorem spw_sbZ_ne_sbJ : sbZ ≠ sbJ := by decide
@[simp] theorem spw_sbZ_ne_sbV : sbZ ≠ sbV := by decide
@[simp] theorem spw_sbZ_ne_sbA2 : sbZ ≠ sbA2 := by decide
@[simp] theorem spw_sbZ_ne_sbR : sbZ ≠ sbR := by decide
@[simp] theorem spw_sbZ_ne_lFl : sbZ ≠ lFl := by decide
@[simp] theorem spw_lFl_ne_sbZ : lFl ≠ sbZ := by decide
@[simp] theorem spw_sbZ_ne_lDh : sbZ ≠ lDh := by decide
@[simp] theorem spw_lDh_ne_sbZ : lDh ≠ sbZ := by decide
@[simp] theorem spw_sbZ_ne_lDt : sbZ ≠ lDt := by decide
@[simp] theorem spw_lDt_ne_sbZ : lDt ≠ sbZ := by decide
@[simp] theorem spw_sbZ_ne_lDg : sbZ ≠ lDg := by decide
@[simp] theorem spw_lDg_ne_sbZ : lDg ≠ sbZ := by decide
@[simp] theorem spw_sbZ_ne_lDi : sbZ ≠ lDi := by decide
@[simp] theorem spw_lDi_ne_sbZ : lDi ≠ sbZ := by decide
@[simp] theorem spw_sbZ_ne_lRp : sbZ ≠ lRp := by decide
@[simp] theorem spw_lRp_ne_sbZ : lRp ≠ sbZ := by decide
@[simp] theorem spw_sbZ_ne_lRn : sbZ ≠ lRn := by decide
@[simp] theorem spw_lRn_ne_sbZ : lRn ≠ sbZ := by decide
@[simp] theorem spw_sbZ_ne_lFle : sbZ ≠ lFle := by decide
@[simp] theorem spw_lFle_ne_sbZ : lFle ≠ sbZ := by decide
@[simp] theorem spw_sbZ_ne_lKb : sbZ ≠ lKb := by decide
@[simp] theorem spw_lKb_ne_sbZ : lKb ≠ sbZ := by decide
@[simp] theorem spw_sbZ_ne_lDir : sbZ ≠ lDir := by decide
@[simp] theorem spw_lDir_ne_sbZ : lDir ≠ sbZ := by decide
@[simp] theorem spw_sbZ_ne_lFln : sbZ ≠ lFln := by decide
@[simp] theorem spw_lFln_ne_sbZ : lFln ≠ sbZ := by decide
@[simp] theorem spw_sbZ_ne_lFll : sbZ ≠ lFll := by decide
@[simp] theorem spw_lFll_ne_sbZ : lFll ≠ sbZ := by decide
@[simp] theorem spw_sbZ_ne_lFls : sbZ ≠ lFls := by decide
@[simp] theorem spw_lFls_ne_sbZ : lFls ≠ sbZ := by decide
@[simp] theorem spw_sbZ_ne_kFu : sbZ ≠ kFu := by decide
@[simp] theorem spw_kFu_ne_sbZ : kFu ≠ sbZ := by decide
@[simp] theorem spw_sbZ_ne_kD : sbZ ≠ kD := by decide
@[simp] theorem spw_kD_ne_sbZ : kD ≠ sbZ := by decide
@[simp] theorem spw_sbA2_ne_sbP : sbA2 ≠ sbP := by decide
@[simp] theorem spw_sbA2_ne_sbI : sbA2 ≠ sbI := by decide
@[simp] theorem spw_sbA2_ne_sbN : sbA2 ≠ sbN := by decide
@[simp] theorem spw_sbA2_ne_sbK : sbA2 ≠ sbK := by decide
@[simp] theorem spw_sbA2_ne_sbL : sbA2 ≠ sbL := by decide
@[simp] theorem spw_sbA2_ne_sbU : sbA2 ≠ sbU := by decide
@[simp] theorem spw_sbA2_ne_sbA : sbA2 ≠ sbA := by decide
@[simp] theorem spw_sbA2_ne_sbX : sbA2 ≠ sbX := by decide
@[simp] theorem spw_sbA2_ne_sbJ : sbA2 ≠ sbJ := by decide
@[simp] theorem spw_sbA2_ne_sbV : sbA2 ≠ sbV := by decide
@[simp] theorem spw_sbA2_ne_sbZ : sbA2 ≠ sbZ := by decide
@[simp] theorem spw_sbA2_ne_sbR : sbA2 ≠ sbR := by decide
@[simp] theorem spw_sbA2_ne_lFl : sbA2 ≠ lFl := by decide
@[simp] theorem spw_lFl_ne_sbA2 : lFl ≠ sbA2 := by decide
@[simp] theorem spw_sbA2_ne_lDh : sbA2 ≠ lDh := by decide
@[simp] theorem spw_lDh_ne_sbA2 : lDh ≠ sbA2 := by decide
@[simp] theorem spw_sbA2_ne_lDt : sbA2 ≠ lDt := by decide
@[simp] theorem spw_lDt_ne_sbA2 : lDt ≠ sbA2 := by decide
@[simp] theorem spw_sbA2_ne_lDg : sbA2 ≠ lDg := by decide
@[simp] theorem spw_lDg_ne_sbA2 : lDg ≠ sbA2 := by decide
@[simp] theorem spw_sbA2_ne_lDi : sbA2 ≠ lDi := by decide
@[simp] theorem spw_lDi_ne_sbA2 : lDi ≠ sbA2 := by decide
@[simp] theorem spw_sbA2_ne_lRp : sbA2 ≠ lRp := by decide
@[simp] theorem spw_lRp_ne_sbA2 : lRp ≠ sbA2 := by decide
@[simp] theorem spw_sbA2_ne_lRn : sbA2 ≠ lRn := by decide
@[simp] theorem spw_lRn_ne_sbA2 : lRn ≠ sbA2 := by decide
@[simp] theorem spw_sbA2_ne_lFle : sbA2 ≠ lFle := by decide
@[simp] theorem spw_lFle_ne_sbA2 : lFle ≠ sbA2 := by decide
@[simp] theorem spw_sbA2_ne_lKb : sbA2 ≠ lKb := by decide
@[simp] theorem spw_lKb_ne_sbA2 : lKb ≠ sbA2 := by decide
@[simp] theorem spw_sbA2_ne_lDir : sbA2 ≠ lDir := by decide
@[simp] theorem spw_lDir_ne_sbA2 : lDir ≠ sbA2 := by decide
@[simp] theorem spw_sbA2_ne_lFln : sbA2 ≠ lFln := by decide
@[simp] theorem spw_lFln_ne_sbA2 : lFln ≠ sbA2 := by decide
@[simp] theorem spw_sbA2_ne_lFll : sbA2 ≠ lFll := by decide
@[simp] theorem spw_lFll_ne_sbA2 : lFll ≠ sbA2 := by decide
@[simp] theorem spw_sbA2_ne_lFls : sbA2 ≠ lFls := by decide
@[simp] theorem spw_lFls_ne_sbA2 : lFls ≠ sbA2 := by decide
@[simp] theorem spw_sbA2_ne_kFu : sbA2 ≠ kFu := by decide
@[simp] theorem spw_kFu_ne_sbA2 : kFu ≠ sbA2 := by decide
@[simp] theorem spw_sbA2_ne_kD : sbA2 ≠ kD := by decide
@[simp] theorem spw_kD_ne_sbA2 : kD ≠ sbA2 := by decide
@[simp] theorem spw_sbR_ne_sbP : sbR ≠ sbP := by decide
@[simp] theorem spw_sbR_ne_sbI : sbR ≠ sbI := by decide
@[simp] theorem spw_sbR_ne_sbN : sbR ≠ sbN := by decide
@[simp] theorem spw_sbR_ne_sbK : sbR ≠ sbK := by decide
@[simp] theorem spw_sbR_ne_sbL : sbR ≠ sbL := by decide
@[simp] theorem spw_sbR_ne_sbU : sbR ≠ sbU := by decide
@[simp] theorem spw_sbR_ne_sbA : sbR ≠ sbA := by decide
@[simp] theorem spw_sbR_ne_sbX : sbR ≠ sbX := by decide
@[simp] theorem spw_sbR_ne_sbJ : sbR ≠ sbJ := by decide
@[simp] theorem spw_sbR_ne_sbV : sbR ≠ sbV := by decide
@[simp] theorem spw_sbR_ne_sbZ : sbR ≠ sbZ := by decide
@[simp] theorem spw_sbR_ne_sbA2 : sbR ≠ sbA2 := by decide
@[simp] theorem spw_sbR_ne_lFl : sbR ≠ lFl := by decide
@[simp] theorem spw_lFl_ne_sbR : lFl ≠ sbR := by decide
@[simp] theorem spw_sbR_ne_lDh : sbR ≠ lDh := by decide
@[simp] theorem spw_lDh_ne_sbR : lDh ≠ sbR := by decide
@[simp] theorem spw_sbR_ne_lDt : sbR ≠ lDt := by decide
@[simp] theorem spw_lDt_ne_sbR : lDt ≠ sbR := by decide
@[simp] theorem spw_sbR_ne_lDg : sbR ≠ lDg := by decide
@[simp] theorem spw_lDg_ne_sbR : lDg ≠ sbR := by decide
@[simp] theorem spw_sbR_ne_lDi : sbR ≠ lDi := by decide
@[simp] theorem spw_lDi_ne_sbR : lDi ≠ sbR := by decide
@[simp] theorem spw_sbR_ne_lRp : sbR ≠ lRp := by decide
@[simp] theorem spw_lRp_ne_sbR : lRp ≠ sbR := by decide
@[simp] theorem spw_sbR_ne_lRn : sbR ≠ lRn := by decide
@[simp] theorem spw_lRn_ne_sbR : lRn ≠ sbR := by decide
@[simp] theorem spw_sbR_ne_lFle : sbR ≠ lFle := by decide
@[simp] theorem spw_lFle_ne_sbR : lFle ≠ sbR := by decide
@[simp] theorem spw_sbR_ne_lKb : sbR ≠ lKb := by decide
@[simp] theorem spw_lKb_ne_sbR : lKb ≠ sbR := by decide
@[simp] theorem spw_sbR_ne_lDir : sbR ≠ lDir := by decide
@[simp] theorem spw_lDir_ne_sbR : lDir ≠ sbR := by decide
@[simp] theorem spw_sbR_ne_lFln : sbR ≠ lFln := by decide
@[simp] theorem spw_lFln_ne_sbR : lFln ≠ sbR := by decide
@[simp] theorem spw_sbR_ne_lFll : sbR ≠ lFll := by decide
@[simp] theorem spw_lFll_ne_sbR : lFll ≠ sbR := by decide
@[simp] theorem spw_sbR_ne_lFls : sbR ≠ lFls := by decide
@[simp] theorem spw_lFls_ne_sbR : lFls ≠ sbR := by decide
@[simp] theorem spw_sbR_ne_kFu : sbR ≠ kFu := by decide
@[simp] theorem spw_kFu_ne_sbR : kFu ≠ sbR := by decide
@[simp] theorem spw_sbR_ne_kD : sbR ≠ kD := by decide
@[simp] theorem spw_kD_ne_sbR : kD ≠ sbR := by decide

def sbParams : List MlS := [sbP, sbI, sbN, sbK, sbL, sbU, sbA]
def sbLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, sbX, sbJ, sbV, sbZ, sbA2, sbR]
def sbBody : ProgHOL 64 := prologue sbLocals (.ite (.cmp .equal (vv sbI) (vv sbN)) (.return (vv sbA)) (.seq (.assign .local sbX (.load .one (.op .add [(.op .add [(vv sbP), (.const 8)]), (.shift .lsl (vv sbI) (.const 3))]))) (.seq (.call (some (some (.local, sbJ), none)) fAf [(vv sbX), (vv sbK), (vv sbL), (vv sbU), (.const 0)]) (.ite (.cmp .equal (vv sbJ) (.const 0)) (.seq (.call (some (some (.local, sbA2), none)) ExPre.fAppend [(vv sbA), (vv sbX)]) (.seq (.call (some (some (.local, sbR), none)) fSb [(vv sbP), (.op .add [(vv sbI), (.const 1)]), (vv sbN), (vv sbK), (vv sbL), (vv sbU), (vv sbA2)]) (.return (vv sbR)))) (.seq (.assign .local lFl (vv lFls)) (.seq (.assign .local lDh (vv sbU)) (.seq lsViewP (.seq (.assign .local sbV (.load .one (.op .add [(vv lRp), (.shift .lsl (.op .sub [(vv sbJ), (.const 1)]) (.const 3))]))) (.seq (.call (some (some (.local, sbZ), none)) fNz0 [(vv sbV)]) (.ite (vv sbZ) (.return (.const 1)) (.seq (.call (some (some (.local, sbA2), none)) fZc [(vv sbV), (vv sbA)]) (.seq (.call (some (some (.local, sbR), none)) fSb [(vv sbP), (.op .add [(vv sbI), (.const 1)]), (vv sbN), (vv sbK), (vv sbL), (vv sbU), (vv sbA2)]) (.return (vv sbR))))))))))))))

structure SbCodes (C : Ctx) : Prop where
  app : C.code.lookup ExPre.fAppend = some (ExPre.appParams.map (fun p => (p, ShapeHOL.one)), ExPre.appBody C, .one)
  af : C.code.lookup fAf = some (afParams.map (fun p => (p, ShapeHOL.one)), afBody, .one)
  neq : C.code.lookup NEq.fNeq = some ([(NEq.pNa, .one), (NEq.pNb, .one)], NEq.neqBody, .one)
  nz : C.code.lookup fNz0 = some ([(nzU, ShapeHOL.one)], nzBody, .one)
  zc : ZcCodes C
  self : C.code.lookup fSb = some (sbParams.map (fun p => (p, ShapeHOL.one)), sbBody, .one)

/-- One step of the fold: a `never` contribution absorbs; parameters concatenate. -/
theorem sb_step (a : List Name) (f : Name → ConLeche.PropWhen) (n : Name) (rest : List Name) :
    (ConLeche.PropWhen.ifAllZero a).inter (ConLeche.PropWhen.bindZ.go f (n :: rest)) =
      match f n with
      | .never => .never
      | .ifAllZero b => (ConLeche.PropWhen.ifAllZero (a ++ b)).inter (ConLeche.PropWhen.bindZ.go f rest) := by
  simp only [ConLeche.PropWhen.bindZ.go]
  rw [← ConLeche.PropWhen.inter_assoc]
  cases f n <;> simp [ConLeche.PropWhen.inter]

section
variable {σ : Type}

/-- A datum in the port: `never` is `1`; `ifAllZero ps` a block of parameter-name handles denoting `ps`. -/
def pwEnc (C : Ctx) (H : List (BitVec 64)) (s : AState) : ConLeche.PropWhen → BitVec 64 → Prop
  | .never, w => w = 1
  | .ifAllZero ps, w => ∃ o ns, w = cellA C o ∧ BlkAt H o (ns.map Enc.idxW) ∧ Frontend.denoteNList s.store.ls.ns ns = some ps

def PostSB (C : Ctx) (s : AState) (r : ConLeche.PropWhen) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ ∃ H', C.H <+: H' ∧ pwEnc C H' s r w ∧ SR (ctxH C H') s st

theorem postSB_locals (C : Ctx) (s : AState) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostSB C s a w s' st → PostSB C s a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, H', h2, h3, h4⟩ => ⟨h1, H', h2, h3, sr_of_eq h4 rfl rfl rfl rfl⟩

theorem sb_spec (C : Ctx) (hok : CtxOK C) (hc : SbCodes C) (s : AState) (hwf : LStoreWF s.store.ls)
    (khs : List NIdx) (ks : List Name) (ok : Nat)
    (hks : ∀ j (hj : j < khs.length), C.EH[ok + j]? = some (Enc.idxW khs[j])) (hkl : ks.length = khs.length)
    (hkd : ∀ j (hj : j < khs.length), ∃ f, denoteNAux s.store.ns f khs[j] = some (ks[j]'(by omega)))
    (hklen : khs.length < 2 ^ 60)
    (us : LsIdx) (uh : List LIdx) (vs : List Level) (huv : s.store.lss.view us = some uh)
    (hvl : vs.length = uh.length) (hvd : ∀ j (hj : j < uh.length), denoteL s.store.ls uh[j] = some (vs[j]'(by omega)))
    (hul0 : uh.length < 2 ^ 61) (ob : Nat) (psH : List NIdx) (psN : List Name) (hbp : BlkAt C.H ob (psH.map Enc.idxW))
    (hdP : Frontend.denoteNList s.store.ls.ns psH = some psN) (hpsl : psN.length = psH.length) (hpl : psH.length < 2 ^ 60) :
    ∀ k i (H : List (BitVec 64)) (accH : List NIdx) (accN : List Name) (oa : Nat), C.H <+: H →
      psH.length - i = k → i ≤ psH.length → BlkAt H oa (accH.map Enc.idxW) →
      Frontend.denoteNList s.store.ls.ns accH = some accN →
      SpecR (σ := σ) (Pre (ctxH C H) s (sbParams.zip [cellA C ob, BitVec.ofNat 64 i, BitVec.ofNat 64 psH.length, ecell C ok,
        BitVec.ofNat 64 khs.length, Enc.idxW us, cellA C oa])) sbBody s
        (pure ((ConLeche.PropWhen.ifAllZero accN).inter
          (ConLeche.PropWhen.bindZ.go (fun n => ConLeche.Level.zeronessOf (ConLeche.Level.subst.go ks vs n)) (psN.drop i))) :
          AM ConLeche.PropWhen)
        (PostSB (ctxH C H) s) := by
  intro k
  induction k with
  | zero =>
    intro i H accH accN oa hpH hk hi hba hdA
    have hi' : i = psH.length := by omega
    subst hi'
    refine specR_prologue (postSB_locals _ s) (Knot.params_none _ sbLocals sbParams _ (by decide) (by decide)) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, sbParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_of_length_le (by rw [hpsl])]
    exact specR_returnI _ (cellA C oa) (by simp +decide [Env.get, sbParams, ctxEnv])
      (fun t ht => ⟨rfl, H, List.prefix_refl _, by simp only [ConLeche.PropWhen.bindZ.go, ConLeche.PropWhen.inter_nil]; exact ⟨oa, accH, rfl, hba, hdA⟩,
        sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro i H accH accN oa hpH hk hi hba hdA
    have hil : i < psH.length := by omega
    refine specR_prologue (postSB_locals _ s) (Knot.params_none _ sbLocals sbParams _ (by decide) (by decide)) ?_
    have hne : BitVec.ofNat 64 i ≠ BitVec.ofNat 64 psH.length := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, sbParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
    have hbp' := blkAt_mono hbp hpH
    have hx := hbp'.2 i (by simpa using hil)
    rw [List.getElem_map] at hx
    refine UD.specR_heapLoadI' (C := ctxH C H) sbX _ (ob + 1 + i) _ hx (by decide)
      (by simp +decide [sev, Env.get, sbParams, ctxEnv]; show _ = cellA C (ob + 1 + i); rw [← cellA_shl C (ob + 1) i (by omega), ← cellA_add8]; rfl) ?_
    obtain ⟨hlen, hget⟩ := LSub.denoteNList_get _ psH psN hdP
    have hnm := hget i hil
    rw [List.drop_eq_getElem_cons (show i < psN.length by omega), sb_step]
    refine specR_callPure (C := ctxH C H) sbJ fAf afParams [vv sbX, vv sbK, vv sbL, vv sbU, .const 0] afBody
      [Enc.idxW psH[i], ecell C ok, BitVec.ofNat 64 khs.length, Enc.idxW us, BitVec.ofNat 64 0]
      (ConLeche.Level.subst.go (ks.drop 0) (vs.drop 0) (psN[i]'(by omega))) (by decide) rfl (by decide) hc.af
      ⟨by simp, by simp +decide [Env.get, sbParams, ctxEnv] <;> rfl, by simp +decide [Env.get, sbParams, ctxEnv],
        by simp +decide [Env.get, sbParams, ctxEnv], rfl, trivial⟩
      (PostAF (ctxH C H) s vs uh (psN[i]'(by omega)))
      (fun r w _ H' => H' = H ∧ ((w = 0 ∧ r = .param (psN[i]'(by omega))) ∨
        ∃ j, ∃ (hj : j < uh.length) (hjv : j < vs.length), w = BitVec.ofNat 64 (j + 1) ∧ r = vs[j]))
      (fun r w s' st ⟨hs, hsr, hw⟩ => ⟨H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu afParams _ rfl hlk)
        (af_spec (ctxH C H) hc.af hc.neq s hwf khs ks ok hks hkl hkd hklen us uh vs huv hvl hvd psH[i] (psN[i]'(by omega))
          _ hnm _ 0 rfl (Nat.zero_le _)))
      (fun w H1 hp1 ⟨eH, hw⟩ => ?_)
    subst H1
    simp only [List.drop_zero] at hw ⊢
    rcases hw with ⟨rfl, hr⟩ | ⟨j, hj, hjv, rfl, hr⟩
    · rw [hr]
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [ConLeche.Level.zeronessOf]
      refine ExPre.specR_callApp (C := ctxH C H) (ctxOK_H hok H) hc.app sbA2 (vv sbA) (vv sbX) oa (accH.map Enc.idxW) (Enc.idxW psH[i])
        (by decide) hba (by simp +decide [Env.get, sbParams, ctxEnv] <;> rfl) (by simp) (fun H2 o2 hp2 hb2 => ?_)
      refine specR_congr (m' := (pure ((ConLeche.PropWhen.ifAllZero (accN ++ [psN[i]'(by omega)])).inter
        (ConLeche.PropWhen.bindZ.go (fun n => ConLeche.Level.zeronessOf (ConLeche.Level.subst.go ks vs n)) (psN.drop (i + 1)))) : AM _) >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H2) sbR fSb sbParams [vv sbP, .op .add [vv sbI, .const 1], vv sbN, vv sbK, vv sbL, vv sbU, vv sbA2] sbBody
        [cellA C ob, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 psH.length, ecell C ok, BitVec.ofNat 64 khs.length, Enc.idxW us, cellA C o2]
        (by decide) rfl (by decide) hc.self
        ⟨by simp +decide [Env.get, sbParams, ctxEnv] <;> rfl, by simp +decide [sev, Env.get, sbParams, ctxEnv]; exact word_add1_eq i, by simp +decide [Env.get, sbParams, ctxEnv], by simp +decide [Env.get, sbParams, ctxEnv] <;> rfl, by simp +decide [Env.get, sbParams, ctxEnv], by simp +decide [Env.get, sbParams, ctxEnv], by simp <;> rfl, trivial⟩
        (PostSB (ctxH C H2) s) (fun r w s' H' => s' = s ∧ pwEnc C H' s r w) (fun r w s' st ⟨hs, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hs, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu sbParams _ rfl hlk)
          (ih (i + 1) H2 (accH ++ [psH[i]]) (accN ++ [psN[i]'(by omega)]) o2 (hpH.trans hp2) (by omega) (by omega)
            (by simpa using hb2) (dnl_append hdA (by simp [Frontend.denoteNList, hnm]))))
        (fun r w s3 H3 hp3 ⟨hs3, hw⟩ => ?_)
      subst hs3
      exact specR_returnI _ w (by simp) (fun t ht => ⟨rfl, H3, hp2.trans hp3, hw, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · rw [hr]
      have hne1 : BitVec.ofNat 64 (j + 1) ≠ 0 := by
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne1) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv sbU) (Enc.idxW us) (by decide) (by simp +decide [Env.get, sbParams, ctxEnv]) ?_
      refine specR_lsviewPI (C := ctxH C H) us (by simp) (by simp <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
        (fun vl Pl hvl _ hvll => ?_)
      rw [huv] at hvl
      cases hvl
      have hul : uh.length < 2 ^ 61 := by simpa using hvll
      refine specR_loadI' sbV _ (Pl + BitVec.ofNat 64 (8 * j)) (Pl + BitVec.ofNat 64 (8 * j)) (Enc.idxW uh[j])
        (by decide) (by simp +decide [sev, Env.get, sbParams, ctxEnv]; rw [show BitVec.ofNat 64 (j + 1) - 1#64 = BitVec.ofNat 64 j from Ex.ofNat_succ_sub_one j, Str.w_shl j 3 (by omega), show j * 2 ^ 3 = 8 * j by omega]) rfl
        (by have h := wordsAt_get Pl (uh.map Enc.idxW) j (by simpa using hj) []; simp only [List.getElem_map] at h; exact h) ?_
      refine specR_dropM ?_
      refine specR_callPure (C := ctxH C H) sbZ fNz0 [nzU] [vv sbV] nzBody [Enc.idxW uh[j]] (nz (vs[j]'hjv))
        (by decide) rfl (by decide) hc.nz ⟨by simp, trivial⟩ (PostBS (ctxH C H) s) (fun b w _ H' => H' = H ∧ w = boolW b)
        (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨H, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [nzU] _ rfl hlk)
          (nz0_spec (ctxH C H) hc.nz s hwf _ uh[j] (hvd j hj)))
        (fun w H2 hp2 ⟨eH, hw⟩ => ?_)
      subst H2; subst hw
      cases hz : nz (vs[j]'hjv)
      swap
      · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
        rw [zof_never _ hz]
        exact specR_returnI _ 1 rfl (fun t ht => ⟨rfl, H, List.prefix_refl _, by simp [ConLeche.PropWhen.inter, pwEnc], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
      rw [zof_eq _ hz]
      refine specR_callPure (C := ctxH C H) sbA2 fZc zcParams [vv sbV, vv sbA] zcBody [Enc.idxW uh[j], cellA C oa] (zps (vs[j]'hjv))
        (by decide) rfl (by decide) hc.zc.self ⟨by simp, by simp +decide [Env.get, sbParams, ctxEnv] <;> rfl, trivial⟩ (PostZc (ctxH C H) s accH)
        (fun r w _ H' => ∃ o ns, w = cellA C o ∧ BlkAt H' o ((accH ++ ns).map Enc.idxW) ∧ Frontend.denoteNList s.store.ls.ns ns = some r)
        (fun r w s' st ⟨hs, H', o, ns, hp, hw, hb, hdn, hsr⟩ => ⟨H', hp, ⟨o, ns, hw, hb, hdn⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu zcParams _ rfl hlk)
          (zc_spec C hok hc.zc s hwf _ uh[j] H accH oa hpH (hvd j hj) hba))
        (fun w H2 hp2 ⟨o2, ns2, hw, hb2, hdn2⟩ => ?_)
      subst hw
      refine specR_congr (m' := (pure ((ConLeche.PropWhen.ifAllZero (accN ++ zps (vs[j]'hjv))).inter
        (ConLeche.PropWhen.bindZ.go (fun n => ConLeche.Level.zeronessOf (ConLeche.Level.subst.go ks vs n)) (psN.drop (i + 1)))) : AM _) >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H2) sbR fSb sbParams [vv sbP, .op .add [vv sbI, .const 1], vv sbN, vv sbK, vv sbL, vv sbU, vv sbA2] sbBody
        [cellA C ob, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 psH.length, ecell C ok, BitVec.ofNat 64 khs.length, Enc.idxW us, cellA C o2]
        (by decide) rfl (by decide) hc.self
        ⟨by simp +decide [Env.get, sbParams, ctxEnv] <;> rfl, by simp +decide [sev, Env.get, sbParams, ctxEnv]; exact word_add1_eq i, by simp +decide [Env.get, sbParams, ctxEnv], by simp +decide [Env.get, sbParams, ctxEnv] <;> rfl, by simp +decide [Env.get, sbParams, ctxEnv], by simp +decide [Env.get, sbParams, ctxEnv], by simp <;> rfl, trivial⟩
        (PostSB (ctxH C H2) s) (fun r w s' H' => s' = s ∧ pwEnc C H' s r w) (fun r w s' st ⟨hs, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hs, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu sbParams _ rfl hlk)
          (ih (i + 1) H2 (accH ++ ns2) (accN ++ zps (vs[j]'hjv)) o2 (hpH.trans hp2) (by omega) (by omega)
            hb2 (dnl_append hdA hdn2)))
        (fun r w s3 H3 hp3 ⟨hs3, hw⟩ => ?_)
      subst hs3
      exact specR_returnI _ w (by simp) (fun t ht => ⟨rfl, H3, hp2.trans hp3, hw, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
