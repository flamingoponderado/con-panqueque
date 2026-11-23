import ConPanqueque.T.Core.SubstPWAt
import ConPanqueque.T.Core.PropRO
import ConPanqueque.T.Core.WcStuck
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# PropRead's `headTypePW`

The datum of a type-former application's head at `n` arguments: a constant's stored type (at the use's levels),
an fvar's declared type, a `bvar`'s binder domain inside the root telescope; the residual after `n` binders.
A `bvar` index at or above `2^64` halts.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc
open ConLeche (Level Name)

def htF := ofString "phtp_htf"
def htR := ofString "phtp_htr"
def htD := ofString "phtp_htd"
def htH := ofString "phtp_hth"
def htN := ofString "phtp_htn"
def htI := ofString "phtp_hti"
def htU := ofString "phtp_htu"
def htP := ofString "phtp_htp"
def htQ := ofString "phtp_htq"
def htLp := ofString "phtp_htlp"
def htLl := ofString "phtp_htll"
def htT := ofString "phtp_htt"
def htV := ofString "phtp_htv"
def htW := ofString "phtp_htw"
def htS := ofString "phtp_hts"
def htJ := ofString "phtp_htj"
def htX := ofString "phtp_htx"
def fHtp := ofString "headTypePW"

@[simp] theorem phtp_htF_ne_htR : htF ≠ htR := by decide
@[simp] theorem phtp_htF_ne_htD : htF ≠ htD := by decide
@[simp] theorem phtp_htF_ne_htH : htF ≠ htH := by decide
@[simp] theorem phtp_htF_ne_htN : htF ≠ htN := by decide
@[simp] theorem phtp_htF_ne_htI : htF ≠ htI := by decide
@[simp] theorem phtp_htF_ne_htU : htF ≠ htU := by decide
@[simp] theorem phtp_htF_ne_htP : htF ≠ htP := by decide
@[simp] theorem phtp_htF_ne_htQ : htF ≠ htQ := by decide
@[simp] theorem phtp_htF_ne_htLp : htF ≠ htLp := by decide
@[simp] theorem phtp_htF_ne_htLl : htF ≠ htLl := by decide
@[simp] theorem phtp_htF_ne_htT : htF ≠ htT := by decide
@[simp] theorem phtp_htF_ne_htV : htF ≠ htV := by decide
@[simp] theorem phtp_htF_ne_htW : htF ≠ htW := by decide
@[simp] theorem phtp_htF_ne_htS : htF ≠ htS := by decide
@[simp] theorem phtp_htF_ne_htJ : htF ≠ htJ := by decide
@[simp] theorem phtp_htF_ne_htX : htF ≠ htX := by decide
@[simp] theorem phtp_htF_ne_lFl : htF ≠ lFl := by decide
@[simp] theorem phtp_lFl_ne_htF : lFl ≠ htF := by decide
@[simp] theorem phtp_htF_ne_lDh : htF ≠ lDh := by decide
@[simp] theorem phtp_lDh_ne_htF : lDh ≠ htF := by decide
@[simp] theorem phtp_htF_ne_lDt : htF ≠ lDt := by decide
@[simp] theorem phtp_lDt_ne_htF : lDt ≠ htF := by decide
@[simp] theorem phtp_htF_ne_lDg : htF ≠ lDg := by decide
@[simp] theorem phtp_lDg_ne_htF : lDg ≠ htF := by decide
@[simp] theorem phtp_htF_ne_lDi : htF ≠ lDi := by decide
@[simp] theorem phtp_lDi_ne_htF : lDi ≠ htF := by decide
@[simp] theorem phtp_htF_ne_lRp : htF ≠ lRp := by decide
@[simp] theorem phtp_lRp_ne_htF : lRp ≠ htF := by decide
@[simp] theorem phtp_htF_ne_lRn : htF ≠ lRn := by decide
@[simp] theorem phtp_lRn_ne_htF : lRn ≠ htF := by decide
@[simp] theorem phtp_htF_ne_lFle : htF ≠ lFle := by decide
@[simp] theorem phtp_lFle_ne_htF : lFle ≠ htF := by decide
@[simp] theorem phtp_htF_ne_lKb : htF ≠ lKb := by decide
@[simp] theorem phtp_lKb_ne_htF : lKb ≠ htF := by decide
@[simp] theorem phtp_htF_ne_lDir : htF ≠ lDir := by decide
@[simp] theorem phtp_lDir_ne_htF : lDir ≠ htF := by decide
@[simp] theorem phtp_htF_ne_lFln : htF ≠ lFln := by decide
@[simp] theorem phtp_lFln_ne_htF : lFln ≠ htF := by decide
@[simp] theorem phtp_htF_ne_lFll : htF ≠ lFll := by decide
@[simp] theorem phtp_lFll_ne_htF : lFll ≠ htF := by decide
@[simp] theorem phtp_htF_ne_lFls : htF ≠ lFls := by decide
@[simp] theorem phtp_lFls_ne_htF : lFls ≠ htF := by decide
@[simp] theorem phtp_htF_ne_kFu : htF ≠ kFu := by decide
@[simp] theorem phtp_kFu_ne_htF : kFu ≠ htF := by decide
@[simp] theorem phtp_htF_ne_kD : htF ≠ kD := by decide
@[simp] theorem phtp_kD_ne_htF : kD ≠ htF := by decide
@[simp] theorem phtp_htR_ne_htF : htR ≠ htF := by decide
@[simp] theorem phtp_htR_ne_htD : htR ≠ htD := by decide
@[simp] theorem phtp_htR_ne_htH : htR ≠ htH := by decide
@[simp] theorem phtp_htR_ne_htN : htR ≠ htN := by decide
@[simp] theorem phtp_htR_ne_htI : htR ≠ htI := by decide
@[simp] theorem phtp_htR_ne_htU : htR ≠ htU := by decide
@[simp] theorem phtp_htR_ne_htP : htR ≠ htP := by decide
@[simp] theorem phtp_htR_ne_htQ : htR ≠ htQ := by decide
@[simp] theorem phtp_htR_ne_htLp : htR ≠ htLp := by decide
@[simp] theorem phtp_htR_ne_htLl : htR ≠ htLl := by decide
@[simp] theorem phtp_htR_ne_htT : htR ≠ htT := by decide
@[simp] theorem phtp_htR_ne_htV : htR ≠ htV := by decide
@[simp] theorem phtp_htR_ne_htW : htR ≠ htW := by decide
@[simp] theorem phtp_htR_ne_htS : htR ≠ htS := by decide
@[simp] theorem phtp_htR_ne_htJ : htR ≠ htJ := by decide
@[simp] theorem phtp_htR_ne_htX : htR ≠ htX := by decide
@[simp] theorem phtp_htR_ne_lFl : htR ≠ lFl := by decide
@[simp] theorem phtp_lFl_ne_htR : lFl ≠ htR := by decide
@[simp] theorem phtp_htR_ne_lDh : htR ≠ lDh := by decide
@[simp] theorem phtp_lDh_ne_htR : lDh ≠ htR := by decide
@[simp] theorem phtp_htR_ne_lDt : htR ≠ lDt := by decide
@[simp] theorem phtp_lDt_ne_htR : lDt ≠ htR := by decide
@[simp] theorem phtp_htR_ne_lDg : htR ≠ lDg := by decide
@[simp] theorem phtp_lDg_ne_htR : lDg ≠ htR := by decide
@[simp] theorem phtp_htR_ne_lDi : htR ≠ lDi := by decide
@[simp] theorem phtp_lDi_ne_htR : lDi ≠ htR := by decide
@[simp] theorem phtp_htR_ne_lRp : htR ≠ lRp := by decide
@[simp] theorem phtp_lRp_ne_htR : lRp ≠ htR := by decide
@[simp] theorem phtp_htR_ne_lRn : htR ≠ lRn := by decide
@[simp] theorem phtp_lRn_ne_htR : lRn ≠ htR := by decide
@[simp] theorem phtp_htR_ne_lFle : htR ≠ lFle := by decide
@[simp] theorem phtp_lFle_ne_htR : lFle ≠ htR := by decide
@[simp] theorem phtp_htR_ne_lKb : htR ≠ lKb := by decide
@[simp] theorem phtp_lKb_ne_htR : lKb ≠ htR := by decide
@[simp] theorem phtp_htR_ne_lDir : htR ≠ lDir := by decide
@[simp] theorem phtp_lDir_ne_htR : lDir ≠ htR := by decide
@[simp] theorem phtp_htR_ne_lFln : htR ≠ lFln := by decide
@[simp] theorem phtp_lFln_ne_htR : lFln ≠ htR := by decide
@[simp] theorem phtp_htR_ne_lFll : htR ≠ lFll := by decide
@[simp] theorem phtp_lFll_ne_htR : lFll ≠ htR := by decide
@[simp] theorem phtp_htR_ne_lFls : htR ≠ lFls := by decide
@[simp] theorem phtp_lFls_ne_htR : lFls ≠ htR := by decide
@[simp] theorem phtp_htR_ne_kFu : htR ≠ kFu := by decide
@[simp] theorem phtp_kFu_ne_htR : kFu ≠ htR := by decide
@[simp] theorem phtp_htR_ne_kD : htR ≠ kD := by decide
@[simp] theorem phtp_kD_ne_htR : kD ≠ htR := by decide
@[simp] theorem phtp_htD_ne_htF : htD ≠ htF := by decide
@[simp] theorem phtp_htD_ne_htR : htD ≠ htR := by decide
@[simp] theorem phtp_htD_ne_htH : htD ≠ htH := by decide
@[simp] theorem phtp_htD_ne_htN : htD ≠ htN := by decide
@[simp] theorem phtp_htD_ne_htI : htD ≠ htI := by decide
@[simp] theorem phtp_htD_ne_htU : htD ≠ htU := by decide
@[simp] theorem phtp_htD_ne_htP : htD ≠ htP := by decide
@[simp] theorem phtp_htD_ne_htQ : htD ≠ htQ := by decide
@[simp] theorem phtp_htD_ne_htLp : htD ≠ htLp := by decide
@[simp] theorem phtp_htD_ne_htLl : htD ≠ htLl := by decide
@[simp] theorem phtp_htD_ne_htT : htD ≠ htT := by decide
@[simp] theorem phtp_htD_ne_htV : htD ≠ htV := by decide
@[simp] theorem phtp_htD_ne_htW : htD ≠ htW := by decide
@[simp] theorem phtp_htD_ne_htS : htD ≠ htS := by decide
@[simp] theorem phtp_htD_ne_htJ : htD ≠ htJ := by decide
@[simp] theorem phtp_htD_ne_htX : htD ≠ htX := by decide
@[simp] theorem phtp_htD_ne_lFl : htD ≠ lFl := by decide
@[simp] theorem phtp_lFl_ne_htD : lFl ≠ htD := by decide
@[simp] theorem phtp_htD_ne_lDh : htD ≠ lDh := by decide
@[simp] theorem phtp_lDh_ne_htD : lDh ≠ htD := by decide
@[simp] theorem phtp_htD_ne_lDt : htD ≠ lDt := by decide
@[simp] theorem phtp_lDt_ne_htD : lDt ≠ htD := by decide
@[simp] theorem phtp_htD_ne_lDg : htD ≠ lDg := by decide
@[simp] theorem phtp_lDg_ne_htD : lDg ≠ htD := by decide
@[simp] theorem phtp_htD_ne_lDi : htD ≠ lDi := by decide
@[simp] theorem phtp_lDi_ne_htD : lDi ≠ htD := by decide
@[simp] theorem phtp_htD_ne_lRp : htD ≠ lRp := by decide
@[simp] theorem phtp_lRp_ne_htD : lRp ≠ htD := by decide
@[simp] theorem phtp_htD_ne_lRn : htD ≠ lRn := by decide
@[simp] theorem phtp_lRn_ne_htD : lRn ≠ htD := by decide
@[simp] theorem phtp_htD_ne_lFle : htD ≠ lFle := by decide
@[simp] theorem phtp_lFle_ne_htD : lFle ≠ htD := by decide
@[simp] theorem phtp_htD_ne_lKb : htD ≠ lKb := by decide
@[simp] theorem phtp_lKb_ne_htD : lKb ≠ htD := by decide
@[simp] theorem phtp_htD_ne_lDir : htD ≠ lDir := by decide
@[simp] theorem phtp_lDir_ne_htD : lDir ≠ htD := by decide
@[simp] theorem phtp_htD_ne_lFln : htD ≠ lFln := by decide
@[simp] theorem phtp_lFln_ne_htD : lFln ≠ htD := by decide
@[simp] theorem phtp_htD_ne_lFll : htD ≠ lFll := by decide
@[simp] theorem phtp_lFll_ne_htD : lFll ≠ htD := by decide
@[simp] theorem phtp_htD_ne_lFls : htD ≠ lFls := by decide
@[simp] theorem phtp_lFls_ne_htD : lFls ≠ htD := by decide
@[simp] theorem phtp_htD_ne_kFu : htD ≠ kFu := by decide
@[simp] theorem phtp_kFu_ne_htD : kFu ≠ htD := by decide
@[simp] theorem phtp_htD_ne_kD : htD ≠ kD := by decide
@[simp] theorem phtp_kD_ne_htD : kD ≠ htD := by decide
@[simp] theorem phtp_htH_ne_htF : htH ≠ htF := by decide
@[simp] theorem phtp_htH_ne_htR : htH ≠ htR := by decide
@[simp] theorem phtp_htH_ne_htD : htH ≠ htD := by decide
@[simp] theorem phtp_htH_ne_htN : htH ≠ htN := by decide
@[simp] theorem phtp_htH_ne_htI : htH ≠ htI := by decide
@[simp] theorem phtp_htH_ne_htU : htH ≠ htU := by decide
@[simp] theorem phtp_htH_ne_htP : htH ≠ htP := by decide
@[simp] theorem phtp_htH_ne_htQ : htH ≠ htQ := by decide
@[simp] theorem phtp_htH_ne_htLp : htH ≠ htLp := by decide
@[simp] theorem phtp_htH_ne_htLl : htH ≠ htLl := by decide
@[simp] theorem phtp_htH_ne_htT : htH ≠ htT := by decide
@[simp] theorem phtp_htH_ne_htV : htH ≠ htV := by decide
@[simp] theorem phtp_htH_ne_htW : htH ≠ htW := by decide
@[simp] theorem phtp_htH_ne_htS : htH ≠ htS := by decide
@[simp] theorem phtp_htH_ne_htJ : htH ≠ htJ := by decide
@[simp] theorem phtp_htH_ne_htX : htH ≠ htX := by decide
@[simp] theorem phtp_htH_ne_lFl : htH ≠ lFl := by decide
@[simp] theorem phtp_lFl_ne_htH : lFl ≠ htH := by decide
@[simp] theorem phtp_htH_ne_lDh : htH ≠ lDh := by decide
@[simp] theorem phtp_lDh_ne_htH : lDh ≠ htH := by decide
@[simp] theorem phtp_htH_ne_lDt : htH ≠ lDt := by decide
@[simp] theorem phtp_lDt_ne_htH : lDt ≠ htH := by decide
@[simp] theorem phtp_htH_ne_lDg : htH ≠ lDg := by decide
@[simp] theorem phtp_lDg_ne_htH : lDg ≠ htH := by decide
@[simp] theorem phtp_htH_ne_lDi : htH ≠ lDi := by decide
@[simp] theorem phtp_lDi_ne_htH : lDi ≠ htH := by decide
@[simp] theorem phtp_htH_ne_lRp : htH ≠ lRp := by decide
@[simp] theorem phtp_lRp_ne_htH : lRp ≠ htH := by decide
@[simp] theorem phtp_htH_ne_lRn : htH ≠ lRn := by decide
@[simp] theorem phtp_lRn_ne_htH : lRn ≠ htH := by decide
@[simp] theorem phtp_htH_ne_lFle : htH ≠ lFle := by decide
@[simp] theorem phtp_lFle_ne_htH : lFle ≠ htH := by decide
@[simp] theorem phtp_htH_ne_lKb : htH ≠ lKb := by decide
@[simp] theorem phtp_lKb_ne_htH : lKb ≠ htH := by decide
@[simp] theorem phtp_htH_ne_lDir : htH ≠ lDir := by decide
@[simp] theorem phtp_lDir_ne_htH : lDir ≠ htH := by decide
@[simp] theorem phtp_htH_ne_lFln : htH ≠ lFln := by decide
@[simp] theorem phtp_lFln_ne_htH : lFln ≠ htH := by decide
@[simp] theorem phtp_htH_ne_lFll : htH ≠ lFll := by decide
@[simp] theorem phtp_lFll_ne_htH : lFll ≠ htH := by decide
@[simp] theorem phtp_htH_ne_lFls : htH ≠ lFls := by decide
@[simp] theorem phtp_lFls_ne_htH : lFls ≠ htH := by decide
@[simp] theorem phtp_htH_ne_kFu : htH ≠ kFu := by decide
@[simp] theorem phtp_kFu_ne_htH : kFu ≠ htH := by decide
@[simp] theorem phtp_htH_ne_kD : htH ≠ kD := by decide
@[simp] theorem phtp_kD_ne_htH : kD ≠ htH := by decide
@[simp] theorem phtp_htN_ne_htF : htN ≠ htF := by decide
@[simp] theorem phtp_htN_ne_htR : htN ≠ htR := by decide
@[simp] theorem phtp_htN_ne_htD : htN ≠ htD := by decide
@[simp] theorem phtp_htN_ne_htH : htN ≠ htH := by decide
@[simp] theorem phtp_htN_ne_htI : htN ≠ htI := by decide
@[simp] theorem phtp_htN_ne_htU : htN ≠ htU := by decide
@[simp] theorem phtp_htN_ne_htP : htN ≠ htP := by decide
@[simp] theorem phtp_htN_ne_htQ : htN ≠ htQ := by decide
@[simp] theorem phtp_htN_ne_htLp : htN ≠ htLp := by decide
@[simp] theorem phtp_htN_ne_htLl : htN ≠ htLl := by decide
@[simp] theorem phtp_htN_ne_htT : htN ≠ htT := by decide
@[simp] theorem phtp_htN_ne_htV : htN ≠ htV := by decide
@[simp] theorem phtp_htN_ne_htW : htN ≠ htW := by decide
@[simp] theorem phtp_htN_ne_htS : htN ≠ htS := by decide
@[simp] theorem phtp_htN_ne_htJ : htN ≠ htJ := by decide
@[simp] theorem phtp_htN_ne_htX : htN ≠ htX := by decide
@[simp] theorem phtp_htN_ne_lFl : htN ≠ lFl := by decide
@[simp] theorem phtp_lFl_ne_htN : lFl ≠ htN := by decide
@[simp] theorem phtp_htN_ne_lDh : htN ≠ lDh := by decide
@[simp] theorem phtp_lDh_ne_htN : lDh ≠ htN := by decide
@[simp] theorem phtp_htN_ne_lDt : htN ≠ lDt := by decide
@[simp] theorem phtp_lDt_ne_htN : lDt ≠ htN := by decide
@[simp] theorem phtp_htN_ne_lDg : htN ≠ lDg := by decide
@[simp] theorem phtp_lDg_ne_htN : lDg ≠ htN := by decide
@[simp] theorem phtp_htN_ne_lDi : htN ≠ lDi := by decide
@[simp] theorem phtp_lDi_ne_htN : lDi ≠ htN := by decide
@[simp] theorem phtp_htN_ne_lRp : htN ≠ lRp := by decide
@[simp] theorem phtp_lRp_ne_htN : lRp ≠ htN := by decide
@[simp] theorem phtp_htN_ne_lRn : htN ≠ lRn := by decide
@[simp] theorem phtp_lRn_ne_htN : lRn ≠ htN := by decide
@[simp] theorem phtp_htN_ne_lFle : htN ≠ lFle := by decide
@[simp] theorem phtp_lFle_ne_htN : lFle ≠ htN := by decide
@[simp] theorem phtp_htN_ne_lKb : htN ≠ lKb := by decide
@[simp] theorem phtp_lKb_ne_htN : lKb ≠ htN := by decide
@[simp] theorem phtp_htN_ne_lDir : htN ≠ lDir := by decide
@[simp] theorem phtp_lDir_ne_htN : lDir ≠ htN := by decide
@[simp] theorem phtp_htN_ne_lFln : htN ≠ lFln := by decide
@[simp] theorem phtp_lFln_ne_htN : lFln ≠ htN := by decide
@[simp] theorem phtp_htN_ne_lFll : htN ≠ lFll := by decide
@[simp] theorem phtp_lFll_ne_htN : lFll ≠ htN := by decide
@[simp] theorem phtp_htN_ne_lFls : htN ≠ lFls := by decide
@[simp] theorem phtp_lFls_ne_htN : lFls ≠ htN := by decide
@[simp] theorem phtp_htN_ne_kFu : htN ≠ kFu := by decide
@[simp] theorem phtp_kFu_ne_htN : kFu ≠ htN := by decide
@[simp] theorem phtp_htN_ne_kD : htN ≠ kD := by decide
@[simp] theorem phtp_kD_ne_htN : kD ≠ htN := by decide
@[simp] theorem phtp_htI_ne_htF : htI ≠ htF := by decide
@[simp] theorem phtp_htI_ne_htR : htI ≠ htR := by decide
@[simp] theorem phtp_htI_ne_htD : htI ≠ htD := by decide
@[simp] theorem phtp_htI_ne_htH : htI ≠ htH := by decide
@[simp] theorem phtp_htI_ne_htN : htI ≠ htN := by decide
@[simp] theorem phtp_htI_ne_htU : htI ≠ htU := by decide
@[simp] theorem phtp_htI_ne_htP : htI ≠ htP := by decide
@[simp] theorem phtp_htI_ne_htQ : htI ≠ htQ := by decide
@[simp] theorem phtp_htI_ne_htLp : htI ≠ htLp := by decide
@[simp] theorem phtp_htI_ne_htLl : htI ≠ htLl := by decide
@[simp] theorem phtp_htI_ne_htT : htI ≠ htT := by decide
@[simp] theorem phtp_htI_ne_htV : htI ≠ htV := by decide
@[simp] theorem phtp_htI_ne_htW : htI ≠ htW := by decide
@[simp] theorem phtp_htI_ne_htS : htI ≠ htS := by decide
@[simp] theorem phtp_htI_ne_htJ : htI ≠ htJ := by decide
@[simp] theorem phtp_htI_ne_htX : htI ≠ htX := by decide
@[simp] theorem phtp_htI_ne_lFl : htI ≠ lFl := by decide
@[simp] theorem phtp_lFl_ne_htI : lFl ≠ htI := by decide
@[simp] theorem phtp_htI_ne_lDh : htI ≠ lDh := by decide
@[simp] theorem phtp_lDh_ne_htI : lDh ≠ htI := by decide
@[simp] theorem phtp_htI_ne_lDt : htI ≠ lDt := by decide
@[simp] theorem phtp_lDt_ne_htI : lDt ≠ htI := by decide
@[simp] theorem phtp_htI_ne_lDg : htI ≠ lDg := by decide
@[simp] theorem phtp_lDg_ne_htI : lDg ≠ htI := by decide
@[simp] theorem phtp_htI_ne_lDi : htI ≠ lDi := by decide
@[simp] theorem phtp_lDi_ne_htI : lDi ≠ htI := by decide
@[simp] theorem phtp_htI_ne_lRp : htI ≠ lRp := by decide
@[simp] theorem phtp_lRp_ne_htI : lRp ≠ htI := by decide
@[simp] theorem phtp_htI_ne_lRn : htI ≠ lRn := by decide
@[simp] theorem phtp_lRn_ne_htI : lRn ≠ htI := by decide
@[simp] theorem phtp_htI_ne_lFle : htI ≠ lFle := by decide
@[simp] theorem phtp_lFle_ne_htI : lFle ≠ htI := by decide
@[simp] theorem phtp_htI_ne_lKb : htI ≠ lKb := by decide
@[simp] theorem phtp_lKb_ne_htI : lKb ≠ htI := by decide
@[simp] theorem phtp_htI_ne_lDir : htI ≠ lDir := by decide
@[simp] theorem phtp_lDir_ne_htI : lDir ≠ htI := by decide
@[simp] theorem phtp_htI_ne_lFln : htI ≠ lFln := by decide
@[simp] theorem phtp_lFln_ne_htI : lFln ≠ htI := by decide
@[simp] theorem phtp_htI_ne_lFll : htI ≠ lFll := by decide
@[simp] theorem phtp_lFll_ne_htI : lFll ≠ htI := by decide
@[simp] theorem phtp_htI_ne_lFls : htI ≠ lFls := by decide
@[simp] theorem phtp_lFls_ne_htI : lFls ≠ htI := by decide
@[simp] theorem phtp_htI_ne_kFu : htI ≠ kFu := by decide
@[simp] theorem phtp_kFu_ne_htI : kFu ≠ htI := by decide
@[simp] theorem phtp_htI_ne_kD : htI ≠ kD := by decide
@[simp] theorem phtp_kD_ne_htI : kD ≠ htI := by decide
@[simp] theorem phtp_htU_ne_htF : htU ≠ htF := by decide
@[simp] theorem phtp_htU_ne_htR : htU ≠ htR := by decide
@[simp] theorem phtp_htU_ne_htD : htU ≠ htD := by decide
@[simp] theorem phtp_htU_ne_htH : htU ≠ htH := by decide
@[simp] theorem phtp_htU_ne_htN : htU ≠ htN := by decide
@[simp] theorem phtp_htU_ne_htI : htU ≠ htI := by decide
@[simp] theorem phtp_htU_ne_htP : htU ≠ htP := by decide
@[simp] theorem phtp_htU_ne_htQ : htU ≠ htQ := by decide
@[simp] theorem phtp_htU_ne_htLp : htU ≠ htLp := by decide
@[simp] theorem phtp_htU_ne_htLl : htU ≠ htLl := by decide
@[simp] theorem phtp_htU_ne_htT : htU ≠ htT := by decide
@[simp] theorem phtp_htU_ne_htV : htU ≠ htV := by decide
@[simp] theorem phtp_htU_ne_htW : htU ≠ htW := by decide
@[simp] theorem phtp_htU_ne_htS : htU ≠ htS := by decide
@[simp] theorem phtp_htU_ne_htJ : htU ≠ htJ := by decide
@[simp] theorem phtp_htU_ne_htX : htU ≠ htX := by decide
@[simp] theorem phtp_htU_ne_lFl : htU ≠ lFl := by decide
@[simp] theorem phtp_lFl_ne_htU : lFl ≠ htU := by decide
@[simp] theorem phtp_htU_ne_lDh : htU ≠ lDh := by decide
@[simp] theorem phtp_lDh_ne_htU : lDh ≠ htU := by decide
@[simp] theorem phtp_htU_ne_lDt : htU ≠ lDt := by decide
@[simp] theorem phtp_lDt_ne_htU : lDt ≠ htU := by decide
@[simp] theorem phtp_htU_ne_lDg : htU ≠ lDg := by decide
@[simp] theorem phtp_lDg_ne_htU : lDg ≠ htU := by decide
@[simp] theorem phtp_htU_ne_lDi : htU ≠ lDi := by decide
@[simp] theorem phtp_lDi_ne_htU : lDi ≠ htU := by decide
@[simp] theorem phtp_htU_ne_lRp : htU ≠ lRp := by decide
@[simp] theorem phtp_lRp_ne_htU : lRp ≠ htU := by decide
@[simp] theorem phtp_htU_ne_lRn : htU ≠ lRn := by decide
@[simp] theorem phtp_lRn_ne_htU : lRn ≠ htU := by decide
@[simp] theorem phtp_htU_ne_lFle : htU ≠ lFle := by decide
@[simp] theorem phtp_lFle_ne_htU : lFle ≠ htU := by decide
@[simp] theorem phtp_htU_ne_lKb : htU ≠ lKb := by decide
@[simp] theorem phtp_lKb_ne_htU : lKb ≠ htU := by decide
@[simp] theorem phtp_htU_ne_lDir : htU ≠ lDir := by decide
@[simp] theorem phtp_lDir_ne_htU : lDir ≠ htU := by decide
@[simp] theorem phtp_htU_ne_lFln : htU ≠ lFln := by decide
@[simp] theorem phtp_lFln_ne_htU : lFln ≠ htU := by decide
@[simp] theorem phtp_htU_ne_lFll : htU ≠ lFll := by decide
@[simp] theorem phtp_lFll_ne_htU : lFll ≠ htU := by decide
@[simp] theorem phtp_htU_ne_lFls : htU ≠ lFls := by decide
@[simp] theorem phtp_lFls_ne_htU : lFls ≠ htU := by decide
@[simp] theorem phtp_htU_ne_kFu : htU ≠ kFu := by decide
@[simp] theorem phtp_kFu_ne_htU : kFu ≠ htU := by decide
@[simp] theorem phtp_htU_ne_kD : htU ≠ kD := by decide
@[simp] theorem phtp_kD_ne_htU : kD ≠ htU := by decide
@[simp] theorem phtp_htP_ne_htF : htP ≠ htF := by decide
@[simp] theorem phtp_htP_ne_htR : htP ≠ htR := by decide
@[simp] theorem phtp_htP_ne_htD : htP ≠ htD := by decide
@[simp] theorem phtp_htP_ne_htH : htP ≠ htH := by decide
@[simp] theorem phtp_htP_ne_htN : htP ≠ htN := by decide
@[simp] theorem phtp_htP_ne_htI : htP ≠ htI := by decide
@[simp] theorem phtp_htP_ne_htU : htP ≠ htU := by decide
@[simp] theorem phtp_htP_ne_htQ : htP ≠ htQ := by decide
@[simp] theorem phtp_htP_ne_htLp : htP ≠ htLp := by decide
@[simp] theorem phtp_htP_ne_htLl : htP ≠ htLl := by decide
@[simp] theorem phtp_htP_ne_htT : htP ≠ htT := by decide
@[simp] theorem phtp_htP_ne_htV : htP ≠ htV := by decide
@[simp] theorem phtp_htP_ne_htW : htP ≠ htW := by decide
@[simp] theorem phtp_htP_ne_htS : htP ≠ htS := by decide
@[simp] theorem phtp_htP_ne_htJ : htP ≠ htJ := by decide
@[simp] theorem phtp_htP_ne_htX : htP ≠ htX := by decide
@[simp] theorem phtp_htP_ne_lFl : htP ≠ lFl := by decide
@[simp] theorem phtp_lFl_ne_htP : lFl ≠ htP := by decide
@[simp] theorem phtp_htP_ne_lDh : htP ≠ lDh := by decide
@[simp] theorem phtp_lDh_ne_htP : lDh ≠ htP := by decide
@[simp] theorem phtp_htP_ne_lDt : htP ≠ lDt := by decide
@[simp] theorem phtp_lDt_ne_htP : lDt ≠ htP := by decide
@[simp] theorem phtp_htP_ne_lDg : htP ≠ lDg := by decide
@[simp] theorem phtp_lDg_ne_htP : lDg ≠ htP := by decide
@[simp] theorem phtp_htP_ne_lDi : htP ≠ lDi := by decide
@[simp] theorem phtp_lDi_ne_htP : lDi ≠ htP := by decide
@[simp] theorem phtp_htP_ne_lRp : htP ≠ lRp := by decide
@[simp] theorem phtp_lRp_ne_htP : lRp ≠ htP := by decide
@[simp] theorem phtp_htP_ne_lRn : htP ≠ lRn := by decide
@[simp] theorem phtp_lRn_ne_htP : lRn ≠ htP := by decide
@[simp] theorem phtp_htP_ne_lFle : htP ≠ lFle := by decide
@[simp] theorem phtp_lFle_ne_htP : lFle ≠ htP := by decide
@[simp] theorem phtp_htP_ne_lKb : htP ≠ lKb := by decide
@[simp] theorem phtp_lKb_ne_htP : lKb ≠ htP := by decide
@[simp] theorem phtp_htP_ne_lDir : htP ≠ lDir := by decide
@[simp] theorem phtp_lDir_ne_htP : lDir ≠ htP := by decide
@[simp] theorem phtp_htP_ne_lFln : htP ≠ lFln := by decide
@[simp] theorem phtp_lFln_ne_htP : lFln ≠ htP := by decide
@[simp] theorem phtp_htP_ne_lFll : htP ≠ lFll := by decide
@[simp] theorem phtp_lFll_ne_htP : lFll ≠ htP := by decide
@[simp] theorem phtp_htP_ne_lFls : htP ≠ lFls := by decide
@[simp] theorem phtp_lFls_ne_htP : lFls ≠ htP := by decide
@[simp] theorem phtp_htP_ne_kFu : htP ≠ kFu := by decide
@[simp] theorem phtp_kFu_ne_htP : kFu ≠ htP := by decide
@[simp] theorem phtp_htP_ne_kD : htP ≠ kD := by decide
@[simp] theorem phtp_kD_ne_htP : kD ≠ htP := by decide
@[simp] theorem phtp_htQ_ne_htF : htQ ≠ htF := by decide
@[simp] theorem phtp_htQ_ne_htR : htQ ≠ htR := by decide
@[simp] theorem phtp_htQ_ne_htD : htQ ≠ htD := by decide
@[simp] theorem phtp_htQ_ne_htH : htQ ≠ htH := by decide
@[simp] theorem phtp_htQ_ne_htN : htQ ≠ htN := by decide
@[simp] theorem phtp_htQ_ne_htI : htQ ≠ htI := by decide
@[simp] theorem phtp_htQ_ne_htU : htQ ≠ htU := by decide
@[simp] theorem phtp_htQ_ne_htP : htQ ≠ htP := by decide
@[simp] theorem phtp_htQ_ne_htLp : htQ ≠ htLp := by decide
@[simp] theorem phtp_htQ_ne_htLl : htQ ≠ htLl := by decide
@[simp] theorem phtp_htQ_ne_htT : htQ ≠ htT := by decide
@[simp] theorem phtp_htQ_ne_htV : htQ ≠ htV := by decide
@[simp] theorem phtp_htQ_ne_htW : htQ ≠ htW := by decide
@[simp] theorem phtp_htQ_ne_htS : htQ ≠ htS := by decide
@[simp] theorem phtp_htQ_ne_htJ : htQ ≠ htJ := by decide
@[simp] theorem phtp_htQ_ne_htX : htQ ≠ htX := by decide
@[simp] theorem phtp_htQ_ne_lFl : htQ ≠ lFl := by decide
@[simp] theorem phtp_lFl_ne_htQ : lFl ≠ htQ := by decide
@[simp] theorem phtp_htQ_ne_lDh : htQ ≠ lDh := by decide
@[simp] theorem phtp_lDh_ne_htQ : lDh ≠ htQ := by decide
@[simp] theorem phtp_htQ_ne_lDt : htQ ≠ lDt := by decide
@[simp] theorem phtp_lDt_ne_htQ : lDt ≠ htQ := by decide
@[simp] theorem phtp_htQ_ne_lDg : htQ ≠ lDg := by decide
@[simp] theorem phtp_lDg_ne_htQ : lDg ≠ htQ := by decide
@[simp] theorem phtp_htQ_ne_lDi : htQ ≠ lDi := by decide
@[simp] theorem phtp_lDi_ne_htQ : lDi ≠ htQ := by decide
@[simp] theorem phtp_htQ_ne_lRp : htQ ≠ lRp := by decide
@[simp] theorem phtp_lRp_ne_htQ : lRp ≠ htQ := by decide
@[simp] theorem phtp_htQ_ne_lRn : htQ ≠ lRn := by decide
@[simp] theorem phtp_lRn_ne_htQ : lRn ≠ htQ := by decide
@[simp] theorem phtp_htQ_ne_lFle : htQ ≠ lFle := by decide
@[simp] theorem phtp_lFle_ne_htQ : lFle ≠ htQ := by decide
@[simp] theorem phtp_htQ_ne_lKb : htQ ≠ lKb := by decide
@[simp] theorem phtp_lKb_ne_htQ : lKb ≠ htQ := by decide
@[simp] theorem phtp_htQ_ne_lDir : htQ ≠ lDir := by decide
@[simp] theorem phtp_lDir_ne_htQ : lDir ≠ htQ := by decide
@[simp] theorem phtp_htQ_ne_lFln : htQ ≠ lFln := by decide
@[simp] theorem phtp_lFln_ne_htQ : lFln ≠ htQ := by decide
@[simp] theorem phtp_htQ_ne_lFll : htQ ≠ lFll := by decide
@[simp] theorem phtp_lFll_ne_htQ : lFll ≠ htQ := by decide
@[simp] theorem phtp_htQ_ne_lFls : htQ ≠ lFls := by decide
@[simp] theorem phtp_lFls_ne_htQ : lFls ≠ htQ := by decide
@[simp] theorem phtp_htQ_ne_kFu : htQ ≠ kFu := by decide
@[simp] theorem phtp_kFu_ne_htQ : kFu ≠ htQ := by decide
@[simp] theorem phtp_htQ_ne_kD : htQ ≠ kD := by decide
@[simp] theorem phtp_kD_ne_htQ : kD ≠ htQ := by decide
@[simp] theorem phtp_htLp_ne_htF : htLp ≠ htF := by decide
@[simp] theorem phtp_htLp_ne_htR : htLp ≠ htR := by decide
@[simp] theorem phtp_htLp_ne_htD : htLp ≠ htD := by decide
@[simp] theorem phtp_htLp_ne_htH : htLp ≠ htH := by decide
@[simp] theorem phtp_htLp_ne_htN : htLp ≠ htN := by decide
@[simp] theorem phtp_htLp_ne_htI : htLp ≠ htI := by decide
@[simp] theorem phtp_htLp_ne_htU : htLp ≠ htU := by decide
@[simp] theorem phtp_htLp_ne_htP : htLp ≠ htP := by decide
@[simp] theorem phtp_htLp_ne_htQ : htLp ≠ htQ := by decide
@[simp] theorem phtp_htLp_ne_htLl : htLp ≠ htLl := by decide
@[simp] theorem phtp_htLp_ne_htT : htLp ≠ htT := by decide
@[simp] theorem phtp_htLp_ne_htV : htLp ≠ htV := by decide
@[simp] theorem phtp_htLp_ne_htW : htLp ≠ htW := by decide
@[simp] theorem phtp_htLp_ne_htS : htLp ≠ htS := by decide
@[simp] theorem phtp_htLp_ne_htJ : htLp ≠ htJ := by decide
@[simp] theorem phtp_htLp_ne_htX : htLp ≠ htX := by decide
@[simp] theorem phtp_htLp_ne_lFl : htLp ≠ lFl := by decide
@[simp] theorem phtp_lFl_ne_htLp : lFl ≠ htLp := by decide
@[simp] theorem phtp_htLp_ne_lDh : htLp ≠ lDh := by decide
@[simp] theorem phtp_lDh_ne_htLp : lDh ≠ htLp := by decide
@[simp] theorem phtp_htLp_ne_lDt : htLp ≠ lDt := by decide
@[simp] theorem phtp_lDt_ne_htLp : lDt ≠ htLp := by decide
@[simp] theorem phtp_htLp_ne_lDg : htLp ≠ lDg := by decide
@[simp] theorem phtp_lDg_ne_htLp : lDg ≠ htLp := by decide
@[simp] theorem phtp_htLp_ne_lDi : htLp ≠ lDi := by decide
@[simp] theorem phtp_lDi_ne_htLp : lDi ≠ htLp := by decide
@[simp] theorem phtp_htLp_ne_lRp : htLp ≠ lRp := by decide
@[simp] theorem phtp_lRp_ne_htLp : lRp ≠ htLp := by decide
@[simp] theorem phtp_htLp_ne_lRn : htLp ≠ lRn := by decide
@[simp] theorem phtp_lRn_ne_htLp : lRn ≠ htLp := by decide
@[simp] theorem phtp_htLp_ne_lFle : htLp ≠ lFle := by decide
@[simp] theorem phtp_lFle_ne_htLp : lFle ≠ htLp := by decide
@[simp] theorem phtp_htLp_ne_lKb : htLp ≠ lKb := by decide
@[simp] theorem phtp_lKb_ne_htLp : lKb ≠ htLp := by decide
@[simp] theorem phtp_htLp_ne_lDir : htLp ≠ lDir := by decide
@[simp] theorem phtp_lDir_ne_htLp : lDir ≠ htLp := by decide
@[simp] theorem phtp_htLp_ne_lFln : htLp ≠ lFln := by decide
@[simp] theorem phtp_lFln_ne_htLp : lFln ≠ htLp := by decide
@[simp] theorem phtp_htLp_ne_lFll : htLp ≠ lFll := by decide
@[simp] theorem phtp_lFll_ne_htLp : lFll ≠ htLp := by decide
@[simp] theorem phtp_htLp_ne_lFls : htLp ≠ lFls := by decide
@[simp] theorem phtp_lFls_ne_htLp : lFls ≠ htLp := by decide
@[simp] theorem phtp_htLp_ne_kFu : htLp ≠ kFu := by decide
@[simp] theorem phtp_kFu_ne_htLp : kFu ≠ htLp := by decide
@[simp] theorem phtp_htLp_ne_kD : htLp ≠ kD := by decide
@[simp] theorem phtp_kD_ne_htLp : kD ≠ htLp := by decide
@[simp] theorem phtp_htLl_ne_htF : htLl ≠ htF := by decide
@[simp] theorem phtp_htLl_ne_htR : htLl ≠ htR := by decide
@[simp] theorem phtp_htLl_ne_htD : htLl ≠ htD := by decide
@[simp] theorem phtp_htLl_ne_htH : htLl ≠ htH := by decide
@[simp] theorem phtp_htLl_ne_htN : htLl ≠ htN := by decide
@[simp] theorem phtp_htLl_ne_htI : htLl ≠ htI := by decide
@[simp] theorem phtp_htLl_ne_htU : htLl ≠ htU := by decide
@[simp] theorem phtp_htLl_ne_htP : htLl ≠ htP := by decide
@[simp] theorem phtp_htLl_ne_htQ : htLl ≠ htQ := by decide
@[simp] theorem phtp_htLl_ne_htLp : htLl ≠ htLp := by decide
@[simp] theorem phtp_htLl_ne_htT : htLl ≠ htT := by decide
@[simp] theorem phtp_htLl_ne_htV : htLl ≠ htV := by decide
@[simp] theorem phtp_htLl_ne_htW : htLl ≠ htW := by decide
@[simp] theorem phtp_htLl_ne_htS : htLl ≠ htS := by decide
@[simp] theorem phtp_htLl_ne_htJ : htLl ≠ htJ := by decide
@[simp] theorem phtp_htLl_ne_htX : htLl ≠ htX := by decide
@[simp] theorem phtp_htLl_ne_lFl : htLl ≠ lFl := by decide
@[simp] theorem phtp_lFl_ne_htLl : lFl ≠ htLl := by decide
@[simp] theorem phtp_htLl_ne_lDh : htLl ≠ lDh := by decide
@[simp] theorem phtp_lDh_ne_htLl : lDh ≠ htLl := by decide
@[simp] theorem phtp_htLl_ne_lDt : htLl ≠ lDt := by decide
@[simp] theorem phtp_lDt_ne_htLl : lDt ≠ htLl := by decide
@[simp] theorem phtp_htLl_ne_lDg : htLl ≠ lDg := by decide
@[simp] theorem phtp_lDg_ne_htLl : lDg ≠ htLl := by decide
@[simp] theorem phtp_htLl_ne_lDi : htLl ≠ lDi := by decide
@[simp] theorem phtp_lDi_ne_htLl : lDi ≠ htLl := by decide
@[simp] theorem phtp_htLl_ne_lRp : htLl ≠ lRp := by decide
@[simp] theorem phtp_lRp_ne_htLl : lRp ≠ htLl := by decide
@[simp] theorem phtp_htLl_ne_lRn : htLl ≠ lRn := by decide
@[simp] theorem phtp_lRn_ne_htLl : lRn ≠ htLl := by decide
@[simp] theorem phtp_htLl_ne_lFle : htLl ≠ lFle := by decide
@[simp] theorem phtp_lFle_ne_htLl : lFle ≠ htLl := by decide
@[simp] theorem phtp_htLl_ne_lKb : htLl ≠ lKb := by decide
@[simp] theorem phtp_lKb_ne_htLl : lKb ≠ htLl := by decide
@[simp] theorem phtp_htLl_ne_lDir : htLl ≠ lDir := by decide
@[simp] theorem phtp_lDir_ne_htLl : lDir ≠ htLl := by decide
@[simp] theorem phtp_htLl_ne_lFln : htLl ≠ lFln := by decide
@[simp] theorem phtp_lFln_ne_htLl : lFln ≠ htLl := by decide
@[simp] theorem phtp_htLl_ne_lFll : htLl ≠ lFll := by decide
@[simp] theorem phtp_lFll_ne_htLl : lFll ≠ htLl := by decide
@[simp] theorem phtp_htLl_ne_lFls : htLl ≠ lFls := by decide
@[simp] theorem phtp_lFls_ne_htLl : lFls ≠ htLl := by decide
@[simp] theorem phtp_htLl_ne_kFu : htLl ≠ kFu := by decide
@[simp] theorem phtp_kFu_ne_htLl : kFu ≠ htLl := by decide
@[simp] theorem phtp_htLl_ne_kD : htLl ≠ kD := by decide
@[simp] theorem phtp_kD_ne_htLl : kD ≠ htLl := by decide
@[simp] theorem phtp_htT_ne_htF : htT ≠ htF := by decide
@[simp] theorem phtp_htT_ne_htR : htT ≠ htR := by decide
@[simp] theorem phtp_htT_ne_htD : htT ≠ htD := by decide
@[simp] theorem phtp_htT_ne_htH : htT ≠ htH := by decide
@[simp] theorem phtp_htT_ne_htN : htT ≠ htN := by decide
@[simp] theorem phtp_htT_ne_htI : htT ≠ htI := by decide
@[simp] theorem phtp_htT_ne_htU : htT ≠ htU := by decide
@[simp] theorem phtp_htT_ne_htP : htT ≠ htP := by decide
@[simp] theorem phtp_htT_ne_htQ : htT ≠ htQ := by decide
@[simp] theorem phtp_htT_ne_htLp : htT ≠ htLp := by decide
@[simp] theorem phtp_htT_ne_htLl : htT ≠ htLl := by decide
@[simp] theorem phtp_htT_ne_htV : htT ≠ htV := by decide
@[simp] theorem phtp_htT_ne_htW : htT ≠ htW := by decide
@[simp] theorem phtp_htT_ne_htS : htT ≠ htS := by decide
@[simp] theorem phtp_htT_ne_htJ : htT ≠ htJ := by decide
@[simp] theorem phtp_htT_ne_htX : htT ≠ htX := by decide
@[simp] theorem phtp_htT_ne_lFl : htT ≠ lFl := by decide
@[simp] theorem phtp_lFl_ne_htT : lFl ≠ htT := by decide
@[simp] theorem phtp_htT_ne_lDh : htT ≠ lDh := by decide
@[simp] theorem phtp_lDh_ne_htT : lDh ≠ htT := by decide
@[simp] theorem phtp_htT_ne_lDt : htT ≠ lDt := by decide
@[simp] theorem phtp_lDt_ne_htT : lDt ≠ htT := by decide
@[simp] theorem phtp_htT_ne_lDg : htT ≠ lDg := by decide
@[simp] theorem phtp_lDg_ne_htT : lDg ≠ htT := by decide
@[simp] theorem phtp_htT_ne_lDi : htT ≠ lDi := by decide
@[simp] theorem phtp_lDi_ne_htT : lDi ≠ htT := by decide
@[simp] theorem phtp_htT_ne_lRp : htT ≠ lRp := by decide
@[simp] theorem phtp_lRp_ne_htT : lRp ≠ htT := by decide
@[simp] theorem phtp_htT_ne_lRn : htT ≠ lRn := by decide
@[simp] theorem phtp_lRn_ne_htT : lRn ≠ htT := by decide
@[simp] theorem phtp_htT_ne_lFle : htT ≠ lFle := by decide
@[simp] theorem phtp_lFle_ne_htT : lFle ≠ htT := by decide
@[simp] theorem phtp_htT_ne_lKb : htT ≠ lKb := by decide
@[simp] theorem phtp_lKb_ne_htT : lKb ≠ htT := by decide
@[simp] theorem phtp_htT_ne_lDir : htT ≠ lDir := by decide
@[simp] theorem phtp_lDir_ne_htT : lDir ≠ htT := by decide
@[simp] theorem phtp_htT_ne_lFln : htT ≠ lFln := by decide
@[simp] theorem phtp_lFln_ne_htT : lFln ≠ htT := by decide
@[simp] theorem phtp_htT_ne_lFll : htT ≠ lFll := by decide
@[simp] theorem phtp_lFll_ne_htT : lFll ≠ htT := by decide
@[simp] theorem phtp_htT_ne_lFls : htT ≠ lFls := by decide
@[simp] theorem phtp_lFls_ne_htT : lFls ≠ htT := by decide
@[simp] theorem phtp_htT_ne_kFu : htT ≠ kFu := by decide
@[simp] theorem phtp_kFu_ne_htT : kFu ≠ htT := by decide
@[simp] theorem phtp_htT_ne_kD : htT ≠ kD := by decide
@[simp] theorem phtp_kD_ne_htT : kD ≠ htT := by decide
@[simp] theorem phtp_htV_ne_htF : htV ≠ htF := by decide
@[simp] theorem phtp_htV_ne_htR : htV ≠ htR := by decide
@[simp] theorem phtp_htV_ne_htD : htV ≠ htD := by decide
@[simp] theorem phtp_htV_ne_htH : htV ≠ htH := by decide
@[simp] theorem phtp_htV_ne_htN : htV ≠ htN := by decide
@[simp] theorem phtp_htV_ne_htI : htV ≠ htI := by decide
@[simp] theorem phtp_htV_ne_htU : htV ≠ htU := by decide
@[simp] theorem phtp_htV_ne_htP : htV ≠ htP := by decide
@[simp] theorem phtp_htV_ne_htQ : htV ≠ htQ := by decide
@[simp] theorem phtp_htV_ne_htLp : htV ≠ htLp := by decide
@[simp] theorem phtp_htV_ne_htLl : htV ≠ htLl := by decide
@[simp] theorem phtp_htV_ne_htT : htV ≠ htT := by decide
@[simp] theorem phtp_htV_ne_htW : htV ≠ htW := by decide
@[simp] theorem phtp_htV_ne_htS : htV ≠ htS := by decide
@[simp] theorem phtp_htV_ne_htJ : htV ≠ htJ := by decide
@[simp] theorem phtp_htV_ne_htX : htV ≠ htX := by decide
@[simp] theorem phtp_htV_ne_lFl : htV ≠ lFl := by decide
@[simp] theorem phtp_lFl_ne_htV : lFl ≠ htV := by decide
@[simp] theorem phtp_htV_ne_lDh : htV ≠ lDh := by decide
@[simp] theorem phtp_lDh_ne_htV : lDh ≠ htV := by decide
@[simp] theorem phtp_htV_ne_lDt : htV ≠ lDt := by decide
@[simp] theorem phtp_lDt_ne_htV : lDt ≠ htV := by decide
@[simp] theorem phtp_htV_ne_lDg : htV ≠ lDg := by decide
@[simp] theorem phtp_lDg_ne_htV : lDg ≠ htV := by decide
@[simp] theorem phtp_htV_ne_lDi : htV ≠ lDi := by decide
@[simp] theorem phtp_lDi_ne_htV : lDi ≠ htV := by decide
@[simp] theorem phtp_htV_ne_lRp : htV ≠ lRp := by decide
@[simp] theorem phtp_lRp_ne_htV : lRp ≠ htV := by decide
@[simp] theorem phtp_htV_ne_lRn : htV ≠ lRn := by decide
@[simp] theorem phtp_lRn_ne_htV : lRn ≠ htV := by decide
@[simp] theorem phtp_htV_ne_lFle : htV ≠ lFle := by decide
@[simp] theorem phtp_lFle_ne_htV : lFle ≠ htV := by decide
@[simp] theorem phtp_htV_ne_lKb : htV ≠ lKb := by decide
@[simp] theorem phtp_lKb_ne_htV : lKb ≠ htV := by decide
@[simp] theorem phtp_htV_ne_lDir : htV ≠ lDir := by decide
@[simp] theorem phtp_lDir_ne_htV : lDir ≠ htV := by decide
@[simp] theorem phtp_htV_ne_lFln : htV ≠ lFln := by decide
@[simp] theorem phtp_lFln_ne_htV : lFln ≠ htV := by decide
@[simp] theorem phtp_htV_ne_lFll : htV ≠ lFll := by decide
@[simp] theorem phtp_lFll_ne_htV : lFll ≠ htV := by decide
@[simp] theorem phtp_htV_ne_lFls : htV ≠ lFls := by decide
@[simp] theorem phtp_lFls_ne_htV : lFls ≠ htV := by decide
@[simp] theorem phtp_htV_ne_kFu : htV ≠ kFu := by decide
@[simp] theorem phtp_kFu_ne_htV : kFu ≠ htV := by decide
@[simp] theorem phtp_htV_ne_kD : htV ≠ kD := by decide
@[simp] theorem phtp_kD_ne_htV : kD ≠ htV := by decide
@[simp] theorem phtp_htW_ne_htF : htW ≠ htF := by decide
@[simp] theorem phtp_htW_ne_htR : htW ≠ htR := by decide
@[simp] theorem phtp_htW_ne_htD : htW ≠ htD := by decide
@[simp] theorem phtp_htW_ne_htH : htW ≠ htH := by decide
@[simp] theorem phtp_htW_ne_htN : htW ≠ htN := by decide
@[simp] theorem phtp_htW_ne_htI : htW ≠ htI := by decide
@[simp] theorem phtp_htW_ne_htU : htW ≠ htU := by decide
@[simp] theorem phtp_htW_ne_htP : htW ≠ htP := by decide
@[simp] theorem phtp_htW_ne_htQ : htW ≠ htQ := by decide
@[simp] theorem phtp_htW_ne_htLp : htW ≠ htLp := by decide
@[simp] theorem phtp_htW_ne_htLl : htW ≠ htLl := by decide
@[simp] theorem phtp_htW_ne_htT : htW ≠ htT := by decide
@[simp] theorem phtp_htW_ne_htV : htW ≠ htV := by decide
@[simp] theorem phtp_htW_ne_htS : htW ≠ htS := by decide
@[simp] theorem phtp_htW_ne_htJ : htW ≠ htJ := by decide
@[simp] theorem phtp_htW_ne_htX : htW ≠ htX := by decide
@[simp] theorem phtp_htW_ne_lFl : htW ≠ lFl := by decide
@[simp] theorem phtp_lFl_ne_htW : lFl ≠ htW := by decide
@[simp] theorem phtp_htW_ne_lDh : htW ≠ lDh := by decide
@[simp] theorem phtp_lDh_ne_htW : lDh ≠ htW := by decide
@[simp] theorem phtp_htW_ne_lDt : htW ≠ lDt := by decide
@[simp] theorem phtp_lDt_ne_htW : lDt ≠ htW := by decide
@[simp] theorem phtp_htW_ne_lDg : htW ≠ lDg := by decide
@[simp] theorem phtp_lDg_ne_htW : lDg ≠ htW := by decide
@[simp] theorem phtp_htW_ne_lDi : htW ≠ lDi := by decide
@[simp] theorem phtp_lDi_ne_htW : lDi ≠ htW := by decide
@[simp] theorem phtp_htW_ne_lRp : htW ≠ lRp := by decide
@[simp] theorem phtp_lRp_ne_htW : lRp ≠ htW := by decide
@[simp] theorem phtp_htW_ne_lRn : htW ≠ lRn := by decide
@[simp] theorem phtp_lRn_ne_htW : lRn ≠ htW := by decide
@[simp] theorem phtp_htW_ne_lFle : htW ≠ lFle := by decide
@[simp] theorem phtp_lFle_ne_htW : lFle ≠ htW := by decide
@[simp] theorem phtp_htW_ne_lKb : htW ≠ lKb := by decide
@[simp] theorem phtp_lKb_ne_htW : lKb ≠ htW := by decide
@[simp] theorem phtp_htW_ne_lDir : htW ≠ lDir := by decide
@[simp] theorem phtp_lDir_ne_htW : lDir ≠ htW := by decide
@[simp] theorem phtp_htW_ne_lFln : htW ≠ lFln := by decide
@[simp] theorem phtp_lFln_ne_htW : lFln ≠ htW := by decide
@[simp] theorem phtp_htW_ne_lFll : htW ≠ lFll := by decide
@[simp] theorem phtp_lFll_ne_htW : lFll ≠ htW := by decide
@[simp] theorem phtp_htW_ne_lFls : htW ≠ lFls := by decide
@[simp] theorem phtp_lFls_ne_htW : lFls ≠ htW := by decide
@[simp] theorem phtp_htW_ne_kFu : htW ≠ kFu := by decide
@[simp] theorem phtp_kFu_ne_htW : kFu ≠ htW := by decide
@[simp] theorem phtp_htW_ne_kD : htW ≠ kD := by decide
@[simp] theorem phtp_kD_ne_htW : kD ≠ htW := by decide
@[simp] theorem phtp_htS_ne_htF : htS ≠ htF := by decide
@[simp] theorem phtp_htS_ne_htR : htS ≠ htR := by decide
@[simp] theorem phtp_htS_ne_htD : htS ≠ htD := by decide
@[simp] theorem phtp_htS_ne_htH : htS ≠ htH := by decide
@[simp] theorem phtp_htS_ne_htN : htS ≠ htN := by decide
@[simp] theorem phtp_htS_ne_htI : htS ≠ htI := by decide
@[simp] theorem phtp_htS_ne_htU : htS ≠ htU := by decide
@[simp] theorem phtp_htS_ne_htP : htS ≠ htP := by decide
@[simp] theorem phtp_htS_ne_htQ : htS ≠ htQ := by decide
@[simp] theorem phtp_htS_ne_htLp : htS ≠ htLp := by decide
@[simp] theorem phtp_htS_ne_htLl : htS ≠ htLl := by decide
@[simp] theorem phtp_htS_ne_htT : htS ≠ htT := by decide
@[simp] theorem phtp_htS_ne_htV : htS ≠ htV := by decide
@[simp] theorem phtp_htS_ne_htW : htS ≠ htW := by decide
@[simp] theorem phtp_htS_ne_htJ : htS ≠ htJ := by decide
@[simp] theorem phtp_htS_ne_htX : htS ≠ htX := by decide
@[simp] theorem phtp_htS_ne_lFl : htS ≠ lFl := by decide
@[simp] theorem phtp_lFl_ne_htS : lFl ≠ htS := by decide
@[simp] theorem phtp_htS_ne_lDh : htS ≠ lDh := by decide
@[simp] theorem phtp_lDh_ne_htS : lDh ≠ htS := by decide
@[simp] theorem phtp_htS_ne_lDt : htS ≠ lDt := by decide
@[simp] theorem phtp_lDt_ne_htS : lDt ≠ htS := by decide
@[simp] theorem phtp_htS_ne_lDg : htS ≠ lDg := by decide
@[simp] theorem phtp_lDg_ne_htS : lDg ≠ htS := by decide
@[simp] theorem phtp_htS_ne_lDi : htS ≠ lDi := by decide
@[simp] theorem phtp_lDi_ne_htS : lDi ≠ htS := by decide
@[simp] theorem phtp_htS_ne_lRp : htS ≠ lRp := by decide
@[simp] theorem phtp_lRp_ne_htS : lRp ≠ htS := by decide
@[simp] theorem phtp_htS_ne_lRn : htS ≠ lRn := by decide
@[simp] theorem phtp_lRn_ne_htS : lRn ≠ htS := by decide
@[simp] theorem phtp_htS_ne_lFle : htS ≠ lFle := by decide
@[simp] theorem phtp_lFle_ne_htS : lFle ≠ htS := by decide
@[simp] theorem phtp_htS_ne_lKb : htS ≠ lKb := by decide
@[simp] theorem phtp_lKb_ne_htS : lKb ≠ htS := by decide
@[simp] theorem phtp_htS_ne_lDir : htS ≠ lDir := by decide
@[simp] theorem phtp_lDir_ne_htS : lDir ≠ htS := by decide
@[simp] theorem phtp_htS_ne_lFln : htS ≠ lFln := by decide
@[simp] theorem phtp_lFln_ne_htS : lFln ≠ htS := by decide
@[simp] theorem phtp_htS_ne_lFll : htS ≠ lFll := by decide
@[simp] theorem phtp_lFll_ne_htS : lFll ≠ htS := by decide
@[simp] theorem phtp_htS_ne_lFls : htS ≠ lFls := by decide
@[simp] theorem phtp_lFls_ne_htS : lFls ≠ htS := by decide
@[simp] theorem phtp_htS_ne_kFu : htS ≠ kFu := by decide
@[simp] theorem phtp_kFu_ne_htS : kFu ≠ htS := by decide
@[simp] theorem phtp_htS_ne_kD : htS ≠ kD := by decide
@[simp] theorem phtp_kD_ne_htS : kD ≠ htS := by decide
@[simp] theorem phtp_htJ_ne_htF : htJ ≠ htF := by decide
@[simp] theorem phtp_htJ_ne_htR : htJ ≠ htR := by decide
@[simp] theorem phtp_htJ_ne_htD : htJ ≠ htD := by decide
@[simp] theorem phtp_htJ_ne_htH : htJ ≠ htH := by decide
@[simp] theorem phtp_htJ_ne_htN : htJ ≠ htN := by decide
@[simp] theorem phtp_htJ_ne_htI : htJ ≠ htI := by decide
@[simp] theorem phtp_htJ_ne_htU : htJ ≠ htU := by decide
@[simp] theorem phtp_htJ_ne_htP : htJ ≠ htP := by decide
@[simp] theorem phtp_htJ_ne_htQ : htJ ≠ htQ := by decide
@[simp] theorem phtp_htJ_ne_htLp : htJ ≠ htLp := by decide
@[simp] theorem phtp_htJ_ne_htLl : htJ ≠ htLl := by decide
@[simp] theorem phtp_htJ_ne_htT : htJ ≠ htT := by decide
@[simp] theorem phtp_htJ_ne_htV : htJ ≠ htV := by decide
@[simp] theorem phtp_htJ_ne_htW : htJ ≠ htW := by decide
@[simp] theorem phtp_htJ_ne_htS : htJ ≠ htS := by decide
@[simp] theorem phtp_htJ_ne_htX : htJ ≠ htX := by decide
@[simp] theorem phtp_htJ_ne_lFl : htJ ≠ lFl := by decide
@[simp] theorem phtp_lFl_ne_htJ : lFl ≠ htJ := by decide
@[simp] theorem phtp_htJ_ne_lDh : htJ ≠ lDh := by decide
@[simp] theorem phtp_lDh_ne_htJ : lDh ≠ htJ := by decide
@[simp] theorem phtp_htJ_ne_lDt : htJ ≠ lDt := by decide
@[simp] theorem phtp_lDt_ne_htJ : lDt ≠ htJ := by decide
@[simp] theorem phtp_htJ_ne_lDg : htJ ≠ lDg := by decide
@[simp] theorem phtp_lDg_ne_htJ : lDg ≠ htJ := by decide
@[simp] theorem phtp_htJ_ne_lDi : htJ ≠ lDi := by decide
@[simp] theorem phtp_lDi_ne_htJ : lDi ≠ htJ := by decide
@[simp] theorem phtp_htJ_ne_lRp : htJ ≠ lRp := by decide
@[simp] theorem phtp_lRp_ne_htJ : lRp ≠ htJ := by decide
@[simp] theorem phtp_htJ_ne_lRn : htJ ≠ lRn := by decide
@[simp] theorem phtp_lRn_ne_htJ : lRn ≠ htJ := by decide
@[simp] theorem phtp_htJ_ne_lFle : htJ ≠ lFle := by decide
@[simp] theorem phtp_lFle_ne_htJ : lFle ≠ htJ := by decide
@[simp] theorem phtp_htJ_ne_lKb : htJ ≠ lKb := by decide
@[simp] theorem phtp_lKb_ne_htJ : lKb ≠ htJ := by decide
@[simp] theorem phtp_htJ_ne_lDir : htJ ≠ lDir := by decide
@[simp] theorem phtp_lDir_ne_htJ : lDir ≠ htJ := by decide
@[simp] theorem phtp_htJ_ne_lFln : htJ ≠ lFln := by decide
@[simp] theorem phtp_lFln_ne_htJ : lFln ≠ htJ := by decide
@[simp] theorem phtp_htJ_ne_lFll : htJ ≠ lFll := by decide
@[simp] theorem phtp_lFll_ne_htJ : lFll ≠ htJ := by decide
@[simp] theorem phtp_htJ_ne_lFls : htJ ≠ lFls := by decide
@[simp] theorem phtp_lFls_ne_htJ : lFls ≠ htJ := by decide
@[simp] theorem phtp_htJ_ne_kFu : htJ ≠ kFu := by decide
@[simp] theorem phtp_kFu_ne_htJ : kFu ≠ htJ := by decide
@[simp] theorem phtp_htJ_ne_kD : htJ ≠ kD := by decide
@[simp] theorem phtp_kD_ne_htJ : kD ≠ htJ := by decide
@[simp] theorem phtp_htX_ne_htF : htX ≠ htF := by decide
@[simp] theorem phtp_htX_ne_htR : htX ≠ htR := by decide
@[simp] theorem phtp_htX_ne_htD : htX ≠ htD := by decide
@[simp] theorem phtp_htX_ne_htH : htX ≠ htH := by decide
@[simp] theorem phtp_htX_ne_htN : htX ≠ htN := by decide
@[simp] theorem phtp_htX_ne_htI : htX ≠ htI := by decide
@[simp] theorem phtp_htX_ne_htU : htX ≠ htU := by decide
@[simp] theorem phtp_htX_ne_htP : htX ≠ htP := by decide
@[simp] theorem phtp_htX_ne_htQ : htX ≠ htQ := by decide
@[simp] theorem phtp_htX_ne_htLp : htX ≠ htLp := by decide
@[simp] theorem phtp_htX_ne_htLl : htX ≠ htLl := by decide
@[simp] theorem phtp_htX_ne_htT : htX ≠ htT := by decide
@[simp] theorem phtp_htX_ne_htV : htX ≠ htV := by decide
@[simp] theorem phtp_htX_ne_htW : htX ≠ htW := by decide
@[simp] theorem phtp_htX_ne_htS : htX ≠ htS := by decide
@[simp] theorem phtp_htX_ne_htJ : htX ≠ htJ := by decide
@[simp] theorem phtp_htX_ne_lFl : htX ≠ lFl := by decide
@[simp] theorem phtp_lFl_ne_htX : lFl ≠ htX := by decide
@[simp] theorem phtp_htX_ne_lDh : htX ≠ lDh := by decide
@[simp] theorem phtp_lDh_ne_htX : lDh ≠ htX := by decide
@[simp] theorem phtp_htX_ne_lDt : htX ≠ lDt := by decide
@[simp] theorem phtp_lDt_ne_htX : lDt ≠ htX := by decide
@[simp] theorem phtp_htX_ne_lDg : htX ≠ lDg := by decide
@[simp] theorem phtp_lDg_ne_htX : lDg ≠ htX := by decide
@[simp] theorem phtp_htX_ne_lDi : htX ≠ lDi := by decide
@[simp] theorem phtp_lDi_ne_htX : lDi ≠ htX := by decide
@[simp] theorem phtp_htX_ne_lRp : htX ≠ lRp := by decide
@[simp] theorem phtp_lRp_ne_htX : lRp ≠ htX := by decide
@[simp] theorem phtp_htX_ne_lRn : htX ≠ lRn := by decide
@[simp] theorem phtp_lRn_ne_htX : lRn ≠ htX := by decide
@[simp] theorem phtp_htX_ne_lFle : htX ≠ lFle := by decide
@[simp] theorem phtp_lFle_ne_htX : lFle ≠ htX := by decide
@[simp] theorem phtp_htX_ne_lKb : htX ≠ lKb := by decide
@[simp] theorem phtp_lKb_ne_htX : lKb ≠ htX := by decide
@[simp] theorem phtp_htX_ne_lDir : htX ≠ lDir := by decide
@[simp] theorem phtp_lDir_ne_htX : lDir ≠ htX := by decide
@[simp] theorem phtp_htX_ne_lFln : htX ≠ lFln := by decide
@[simp] theorem phtp_lFln_ne_htX : lFln ≠ htX := by decide
@[simp] theorem phtp_htX_ne_lFll : htX ≠ lFll := by decide
@[simp] theorem phtp_lFll_ne_htX : lFll ≠ htX := by decide
@[simp] theorem phtp_htX_ne_lFls : htX ≠ lFls := by decide
@[simp] theorem phtp_lFls_ne_htX : lFls ≠ htX := by decide
@[simp] theorem phtp_htX_ne_kFu : htX ≠ kFu := by decide
@[simp] theorem phtp_kFu_ne_htX : kFu ≠ htX := by decide
@[simp] theorem phtp_htX_ne_kD : htX ≠ kD := by decide
@[simp] theorem phtp_kD_ne_htX : kD ≠ htX := by decide

def htParams : List MlS := [htF, htR, htD, htH, htN]
def htLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, htI, htU, htP, htQ, htLp, htLl, htT, htV, htW, htS, htJ, htX]
def htBody (C : Ctx) : ProgHOL 64 := prologue htLocals (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv htH)) (.seq eViewP (.ite (.cmp .equal (vv lDg) (.const 3)) (.seq (.assign .local htI (.load .one (vv lRp))) (.seq (.assign .local htU (.load .one (.op .add [(vv lRp), (.const 8)]))) (envFindP C htP (vv htI) (.ite (.cmp .equal (vv htP) (.const 0)) (.return (.const 0)) (.seq (.assign .local htQ (.op .sub [(vv htP), (.const 1)])) (.seq (.assign .local htLp (.load .one (.op .add [(vv htQ), (.const 16)]))) (.seq (.assign .local htLl (.load .one (vv htLp))) (.seq (.assign .local htT (.load .one (.op .add [(vv htQ), (.const 24)]))) (.seq (.assign .local lFl (vv lFls)) (.seq (.assign .local lDh (vv htU)) (.seq lsViewP (.ite (.cmp .notEqual (vv lRn) (vv htLl)) (.return (.const 0)) (.seq (.call (some (some (.local, htV), none)) fPv [(vv htF), (vv htN), (vv htT)]) (.seq (.call (some (some (.local, htW), none)) fRw [(vv htV)]) (.ite (.cmp .equal (vv htW) (.const 0)) (.return (.const 0)) (.seq (.call (some (some (.local, htS), none)) fSa [(.op .add [(vv htLp), (.const 8)]), (vv htLl), (vv htU), (vv htW)]) (.return (vv htS)))))))))))))))))) (.ite (.cmp .equal (vv lDg) (.const 1)) (.seq (.assign .local htT (.load .one (vv lRp))) (.seq (.call (some (some (.local, htV), none)) fPv [(vv htF), (vv htN), (vv htT)]) (.seq (.call (some (some (.local, htW), none)) fRw [(vv htV)]) (.return (vv htW))))) (.ite (.cmp .equal (vv lDg) (.const 0)) (.ite (.cmp .equal (vv lRn) (.const 0)) (.seq (.assign .local htJ (.const 0)) (.ite (.cmp .lower (vv htJ) (vv htD)) (.seq (.call (some (some (.local, htX), none)) fBd [(.op .sub [(.op .sub [(vv htD), (.const 1)]), (vv htJ)]), (vv htR)]) (.ite (.cmp .equal (vv htX) (.const 0)) (.return (.const 0)) (.seq (.call (some (some (.local, htV), none)) fPv [(vv htF), (vv htN), (.op .sub [(vv htX), (.const 1)])]) (.seq (.call (some (some (.local, htW), none)) fRw [(vv htV)]) (.return (vv htW)))))) (.return (.const 0)))) (.ite (.cmp .equal (vv lRn) (.const 1)) (.seq (.assign .local htJ (.load .one (vv lRp))) (.ite (.cmp .lower (vv htJ) (vv htD)) (.seq (.call (some (some (.local, htX), none)) fBd [(.op .sub [(.op .sub [(vv htD), (.const 1)]), (vv htJ)]), (vv htR)]) (.ite (.cmp .equal (vv htX) (.const 0)) (.return (.const 0)) (.seq (.call (some (some (.local, htV), none)) fPv [(vv htF), (vv htN), (.op .sub [(vv htX), (.const 1)])]) (.seq (.call (some (some (.local, htW), none)) fRw [(vv htV)]) (.return (vv htW)))))) (.return (.const 0)))) hang)) (.return (.const 0))))))))

structure SaCodesFull (C : Ctx) : Prop where
  self : C.code.lookup fSa = some (saParams.map (fun p => (p, ShapeHOL.one)), saBody C, .one)
  codes : SaCodes C

structure HtCodes (C : Ctx) : Prop where
  mg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  mp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  pv : PvCodes C
  rw : C.code.lookup fRw = some (rwParams.map (fun p => (p, ShapeHOL.one)), rwBody C, .one)
  rwc : RwCodes C
  bd : C.code.lookup fBd = some (bdParams.map (fun p => (p, ShapeHOL.one)), bdBody, .one)
  sa : SaCodesFull C

section
variable {σ : Type}

theorem ht_spec (C : Ctx) (hok : CtxOK C) (hc : HtCodes C) (fuel : Nat) (hf : fuel < 2 ^ 62) (s : AState) (hwf : LStoreWF s.store.ls) (hrd : RdOK s)
    (hSD : ∀ h u, s.store.view h = some (.sort u) → ∃ l, denoteL s.store.ls u = some l)
    (hLP : ∀ c ci, C.fe.find? c = some ci → ∃ ks, Frontend.denoteNList s.store.ns ci.toConstantVal.levelParams = some ks)
    (hLPl : ∀ c ci, C.fe.find? c = some ci → ci.toConstantVal.levelParams.length < 2 ^ 60)
    (hLS : ∀ us uh, s.store.lss.view us = some uh → ∃ vs, denoteLs s.store.lss us = some vs ∧ ∃ hl : vs.length = uh.length,
      ∀ j (hj : j < uh.length), denoteL s.store.ls uh[j] = some (vs[j]'(by rw [hl]; exact hj))) :
    ∀ (H : List (BitVec 64)) (root : EIdx) (d : Nat) (h : EIdx) (n : Nat), C.H <+: H → d < 2 ^ 63 → n < 2 ^ 64 →
      SpecR (σ := σ) (Pre (ctxH C H) s (htParams.zip [BitVec.ofNat 64 fuel, Enc.idxW root, BitVec.ofNat 64 d, Enc.idxW h, BitVec.ofNat 64 n]))
        (htBody C) s (headTypePW C.fe fuel root d h n) (PostSA (ctxH C H) s) := by
  intro H root d h n hpH hd hn
  refine specR_prologue (postSA_locals _ s) (Knot.params_none _ htLocals htParams _ (by decide) (by decide)) ?_
  unfold headTypePW
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv htH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, htParams, ctxEnv]) ?_
  refine specR_viewP (C := ctxH C H) h (by simp) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
    (fun v P hv htn hl => ?_)
  refine specR_congr (Big.view_bind_eq h v _ s hv) ?_
  rcases v with i | ⟨i, ty⟩ | u1 | ⟨I, us⟩ | ⟨f1, x1⟩ | ⟨t1, b1⟩ | ⟨t1, b1⟩ | ⟨t1, v1, b1⟩ | l1 | ⟨sn1, pi1, pe1⟩
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    have er : encEView (.bvar i) = limbs i := rfl
    have hl58 : (limbs i).length < 2 ^ 61 := by rw [← er]; exact hl
    rcases (by omega : (limbs i).length = 0 ∨ (limbs i).length = 1 ∨ 2 ≤ (limbs i).length) with hz | h1 | h2
    · have hi0 : i = 0 := by have := (limbs_length_lt_iff i 0).mp (by omega); simpa using this
      have hi64 : i < 2 ^ 64 := by omega
      refine specR_ifI _ 1 (by simp [sev, er, hz, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_assignI htJ (.const 0) (BitVec.ofNat 64 i) (by decide) (by rw [hi0]; rfl) ?_
      have hdw : BitVec.ofNat 64 i < BitVec.ofNat 64 d ↔ i < d := by
        rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt (by omega)]
      by_cases hid : i < d
      swap
      · refine specR_ifI _ 0 (by simp +decide [sev, Env.get, htParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hdw, hid]) (fun h => absurd rfl h) (fun _ => ?_)
        rw [if_neg hid]
        exact specR_returnI _ 0 rfl (fun t ht => ⟨rdStep_refl hrd, H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, htParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hdw, hid]) (fun _ => ?_) (fun h => absurd h (by decide))
      rw [if_pos hid]
      have hsubw : BitVec.ofNat 64 d - 1#64 - BitVec.ofNat 64 i = BitVec.ofNat 64 (d - 1 - i) := by
        rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ix_wsub d 1 (by omega) (by omega), ix_wsub (d - 1) i (by omega) (by omega)]
      refine specR_callNIH (C := ctxH C H) htX fBd bdParams [.op .sub [.op .sub [vv htD, .const 1], vv htJ], vv htR] bdBody
        [BitVec.ofNat 64 (d - 1 - i), Enc.idxW root] (by decide) rfl (by decide) hc.bd
        ⟨by simp +decide [sev, Env.get, htParams, ctxEnv]; first | exact hsubw | (rw [← hsubw]; simp) | (rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ix_wsub d 1 (by omega) (by omega)]), by simp +decide [Env.get, htParams, ctxEnv], trivial⟩
        (fun r_ w s' st => binderDom (d - 1 - i) root s = .ok (r_, s') ∧ UD.PostO (ctxH C H) r_ w s' st)
        (fun r_ w s' H' => w = optW r_ ∧ binderDom (d - 1 - i) root s = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu bdParams _ rfl hlk) (bd_spec (ctxH C H) hc.bd (d - 1 - i) root s (by omega))))
        (fun od w0 s0 H0 hp0 ⟨hw0, hrun0⟩ => ?_)
      have hs0 := RO.binderDom _ _ s od s0 hrun0
      subst s0; subst hw0
      rcases od with _ | D
      · refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
        try dsimp only
        exact specR_returnI _ 0 rfl (fun t ht => ⟨rdStep_refl hrd, H0, hp0, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne D) (fun h => absurd rfl h) (fun _ => ?_)
      show SpecR _ _ _ (peelPisW C.fe fuel n D >>= fun res => residualPW res) _
      refine specR_callNIH (C := ctxH C H0) htV fPv pvParams [vv htF, vv htN, .op .sub [vv htX, .const 1]] (pvBody C) [BitVec.ofNat 64 fuel, BitVec.ofNat 64 n, Enc.idxW D]
        (by decide) rfl (by decide) hc.pv.self ⟨by simp +decide [Env.get, htParams, ctxEnv], by simp +decide [Env.get, htParams, ctxEnv], by simp +decide [sev, Env.get, htParams, ctxEnv, optWG] <;> first | rfl | exact BitVec.add_sub_cancel _ _, trivial⟩
        (fun r_ w s' st => peelPisW C.fe fuel n D s = .ok (r_, s') ∧ UD.PostO (ctxH C H0) r_ w s' st)
        (fun r_ w s' H' => w = optW r_ ∧ peelPisW C.fe fuel n D s = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu pvParams _ rfl hlk) (pv_spec C hok hc.pv fuel hf n H0 D s (hpH.trans hp0) hn)))
        (fun res w1 s1 H1 hp1 ⟨hw1, hrun1⟩ => ?_)
      have hs1 := RO.peelPisW _ _ _ _ s res s1 hrun1
      subst s1; subst hw1
      refine specR_congr (m' := residualPW res >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H1) htW fRw rwParams [vv htV] (rwBody C) [optW res] (by decide) rfl (by decide) hc.rw
        ⟨by simp, trivial⟩ (PostOPW (ctxH C H1) s) (fun r_ w s' H' => s' = s ∧ optPW C H' s r_ w)
        (fun r_ w s' st ⟨hs, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hs, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rwParams _ rfl hlk)
          (rw_spec C hok hc.rwc s hwf H1 res ((hpH.trans hp0).trans hp1) (fun h u _ hv => hSD h u hv)))
        (fun pw' w2 s2 H2 hp2 ⟨hs2, hw2⟩ => ?_)
      subst s2
      exact specR_returnI _ w2 (by simp) (fun t ht => ⟨rdStep_refl hrd, H2, hp0.trans (hp1.trans hp2), hw2, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    · have hi64 : i < 2 ^ 64 := by have := (limbs_length_lt_iff i 1).mp (by omega); simpa using this
      have h1w : BitVec.ofNat 64 (limbs i).length ≠ 0#64 := by rw [h1]; decide
      refine specR_ifI _ 0 (by simp [sev, er, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact h1w) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp [sev, er, h1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      have hx0 : (limbs i)[0]'(by omega) = BitVec.ofNat 64 i := by
        rw [limbs_getElem i 0 (by omega)]; simp [Nat.mod_eq_of_lt hi64]
      refine specR_loadI' htJ (vv lRp) P (P + BitVec.ofNat 64 (8 * 0)) (BitVec.ofNat 64 i) (by decide) (by simp) (by simp)
        (by have := wordsAt_get P (limbs i) 0 (by omega) []; rw [hx0] at this; simpa [er] using this) ?_
      have hdw : BitVec.ofNat 64 i < BitVec.ofNat 64 d ↔ i < d := by
        rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi64, Nat.mod_eq_of_lt (by omega)]
      by_cases hid : i < d
      swap
      · refine specR_ifI _ 0 (by simp +decide [sev, Env.get, htParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hdw, hid]) (fun h => absurd rfl h) (fun _ => ?_)
        rw [if_neg hid]
        exact specR_returnI _ 0 rfl (fun t ht => ⟨rdStep_refl hrd, H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, htParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hdw, hid]) (fun _ => ?_) (fun h => absurd h (by decide))
      rw [if_pos hid]
      have hsubw : BitVec.ofNat 64 d - 1#64 - BitVec.ofNat 64 i = BitVec.ofNat 64 (d - 1 - i) := by
        rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ix_wsub d 1 (by omega) (by omega), ix_wsub (d - 1) i (by omega) (by omega)]
      refine specR_callNIH (C := ctxH C H) htX fBd bdParams [.op .sub [.op .sub [vv htD, .const 1], vv htJ], vv htR] bdBody
        [BitVec.ofNat 64 (d - 1 - i), Enc.idxW root] (by decide) rfl (by decide) hc.bd
        ⟨by simp +decide [sev, Env.get, htParams, ctxEnv]; first | exact hsubw | (rw [← hsubw]; simp) | (rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ix_wsub d 1 (by omega) (by omega)]), by simp +decide [Env.get, htParams, ctxEnv], trivial⟩
        (fun r_ w s' st => binderDom (d - 1 - i) root s = .ok (r_, s') ∧ UD.PostO (ctxH C H) r_ w s' st)
        (fun r_ w s' H' => w = optW r_ ∧ binderDom (d - 1 - i) root s = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu bdParams _ rfl hlk) (bd_spec (ctxH C H) hc.bd (d - 1 - i) root s (by omega))))
        (fun od w0 s0 H0 hp0 ⟨hw0, hrun0⟩ => ?_)
      have hs0 := RO.binderDom _ _ s od s0 hrun0
      subst s0; subst hw0
      rcases od with _ | D
      · refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
        try dsimp only
        exact specR_returnI _ 0 rfl (fun t ht => ⟨rdStep_refl hrd, H0, hp0, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne D) (fun h => absurd rfl h) (fun _ => ?_)
      show SpecR _ _ _ (peelPisW C.fe fuel n D >>= fun res => residualPW res) _
      refine specR_callNIH (C := ctxH C H0) htV fPv pvParams [vv htF, vv htN, .op .sub [vv htX, .const 1]] (pvBody C) [BitVec.ofNat 64 fuel, BitVec.ofNat 64 n, Enc.idxW D]
        (by decide) rfl (by decide) hc.pv.self ⟨by simp +decide [Env.get, htParams, ctxEnv], by simp +decide [Env.get, htParams, ctxEnv], by simp +decide [sev, Env.get, htParams, ctxEnv, optWG] <;> first | rfl | exact BitVec.add_sub_cancel _ _, trivial⟩
        (fun r_ w s' st => peelPisW C.fe fuel n D s = .ok (r_, s') ∧ UD.PostO (ctxH C H0) r_ w s' st)
        (fun r_ w s' H' => w = optW r_ ∧ peelPisW C.fe fuel n D s = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu pvParams _ rfl hlk) (pv_spec C hok hc.pv fuel hf n H0 D s (hpH.trans hp0) hn)))
        (fun res w1 s1 H1 hp1 ⟨hw1, hrun1⟩ => ?_)
      have hs1 := RO.peelPisW _ _ _ _ s res s1 hrun1
      subst s1; subst hw1
      refine specR_congr (m' := residualPW res >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H1) htW fRw rwParams [vv htV] (rwBody C) [optW res] (by decide) rfl (by decide) hc.rw
        ⟨by simp, trivial⟩ (PostOPW (ctxH C H1) s) (fun r_ w s' H' => s' = s ∧ optPW C H' s r_ w)
        (fun r_ w s' st ⟨hs, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hs, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rwParams _ rfl hlk)
          (rw_spec C hok hc.rwc s hwf H1 res ((hpH.trans hp0).trans hp1) (fun h u _ hv => hSD h u hv)))
        (fun pw' w2 s2 H2 hp2 ⟨hs2, hw2⟩ => ?_)
      subst s2
      exact specR_returnI _ w2 (by simp) (fun t ht => ⟨rdStep_refl hrd, H2, hp0.trans (hp1.trans hp2), hw2, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    · have h1w : BitVec.ofNat 64 (limbs i).length ≠ 0#64 := by
        intro h0; have := congrArg BitVec.toNat h0; simp at this; omega
      have h2w : BitVec.ofNat 64 (limbs i).length ≠ 1#64 := by
        intro h0; have := congrArg BitVec.toNat h0; simp at this; omega
      refine specR_ifI _ 0 (by simp [sev, er, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact h1w) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp [sev, er, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact h2w) (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_hangI

  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    refine specR_loadI' htT (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encFVar] using wordsAt_mem0 P (Enc.idxW ty) (limbs i) []) ?_
    refine specR_dropM ?_
    refine specR_callNIH (C := ctxH C H) htV fPv pvParams [vv htF, vv htN, vv htT] (pvBody C) [BitVec.ofNat 64 fuel, BitVec.ofNat 64 n, Enc.idxW ty]
      (by decide) rfl (by decide) hc.pv.self ⟨by simp +decide [Env.get, htParams, ctxEnv], by simp +decide [Env.get, htParams, ctxEnv], by simp +decide [sev, Env.get, htParams, ctxEnv, optWG] <;> first | rfl | exact BitVec.add_sub_cancel _ _, trivial⟩
      (fun r_ w s' st => peelPisW C.fe fuel n ty s = .ok (r_, s') ∧ UD.PostO (ctxH C H) r_ w s' st)
      (fun r_ w s' H' => w = optW r_ ∧ peelPisW C.fe fuel n ty s = .ok (r_, s'))
      (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu pvParams _ rfl hlk) (pv_spec C hok hc.pv fuel hf n H ty s hpH hn)))
      (fun res w1 s1 H1 hp1 ⟨hw1, hrun1⟩ => ?_)
    have hs1 := RO.peelPisW _ _ _ _ s res s1 hrun1
    subst s1; subst hw1
    refine specR_congr (m' := residualPW res >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H1) htW fRw rwParams [vv htV] (rwBody C) [optW res] (by decide) rfl (by decide) hc.rw
      ⟨by simp, trivial⟩ (PostOPW (ctxH C H1) s) (fun r_ w s' H' => s' = s ∧ optPW C H' s r_ w)
      (fun r_ w s' st ⟨hs, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hs, hw⟩, by rw [hs]; exact hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rwParams _ rfl hlk)
        (rw_spec C hok hc.rwc s hwf H1 res (hpH.trans hp1) (fun h u _ hv => hSD h u hv)))
      (fun pw' w2 s2 H2 hp2 ⟨hs2, hw2⟩ => ?_)
    subst s2
    exact specR_returnI _ w2 (by simp) (fun t ht => ⟨rdStep_refl hrd, H2, hp1.trans hp2, hw2, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rdStep_refl hrd, H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

  · refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    refine specR_loadI' htI (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW I) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW I) [Enc.idxW us] []) ?_
    refine specR_loadI' htU _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW us) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW I) (Enc.idxW us) [] []) ?_
    refine specR_envFindI (C := ctxH C H) (ctxOK_H hok H) hc.mg hc.mp htP (vv htI) I (by decide) (by simp) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    have hrel := find_rel hok I
    try rw [show (ctxH C H).envM = C.envM from rfl]
    revert hrel
    rcases hfind : C.fe.find? I with _ | ci
    · intro hrel; simp only at hrel; rw [hrel]
      refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ 0 rfl (fun t ht => ⟨rdStep_refl hrd, H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    intro ⟨o, hm, hci⟩
    rw [hm]
    refine specR_atEntry fun t ht => ?_
    have hoE : o < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
    have hEN : C.EH.length ≤ C.EN := ht.sr.env.1.len
    have hEL := hok.envLay
    refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI htQ _ (ecell C o) (by decide) (by simp [sev, optWG]; exact BitVec.add_sub_cancel _ _) ?_
    obtain ⟨_, ⟨wl, hwl, ol, hwl', hbl⟩, hty⟩ := hci.1
    refine specR_envLoadI htLp (.op .add [vv htQ, .const 16]) (o + 2) _ (by decide)
      (by simp +decide [sev, Env.get, htParams, ctxEnv, ecell_ctxH]; exact UD.ecell_add16 C o)
      (by rw [show o + 2 = o + 1 + 1 by omega]; exact hwl) ?_
    refine specR_envLoadI htLl (vv htLp) ol _ (by decide) (by simp [hwl']; rfl) hbl.1 ?_
    refine specR_envLoadI htT (.op .add [vv htQ, .const 24]) (o + 3) _ (by decide)
      (by simp +decide [sev, Env.get, htParams, ctxEnv, ecell_ctxH]; simpa using ecell_add C o 3)
      (by rw [show o + 3 = o + 1 + 2 by omega]; exact hty) ?_
    have hlp : ci.toConstantVal.levelParams.length < 2 ^ 60 := hLPl I ci hfind
    refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv htU) (Enc.idxW us) (by decide) (by simp) ?_
    refine specR_lsviewPI (C := ctxH C H) us (by simp) (by simp <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
      (fun vl Pl hvl _ hvll => ?_)
    refine specR_runBind (viewLsLen_run us s vl hvl) ?_
    dsimp only
    have hvl' : vl.length < 2 ^ 61 := by simpa using hvll
    simp only [List.length_map]
    by_cases hlen : vl.length = ci.toConstantVal.levelParams.length
    swap
    · have hne : BitVec.ofNat 64 vl.length ≠ BitVec.ofNat 64 ci.toConstantVal.levelParams.length := by
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun _ => ?_) (fun h => absurd h (by decide))
      rw [if_neg hlen]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨rdStep_refl hrd, H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlen]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [if_pos hlen]
    refine specR_callNIH (C := ctxH C H) htV fPv pvParams [vv htF, vv htN, vv htT] (pvBody C) [BitVec.ofNat 64 fuel, BitVec.ofNat 64 n, Enc.idxW ci.toConstantVal.type]
      (by decide) rfl (by decide) hc.pv.self ⟨by simp +decide [Env.get, htParams, ctxEnv], by simp +decide [Env.get, htParams, ctxEnv], by simp +decide [sev, Env.get, htParams, ctxEnv, optWG] <;> first | rfl | exact BitVec.add_sub_cancel _ _, trivial⟩
      (fun r_ w s' st => peelPisW C.fe fuel n ci.toConstantVal.type s = .ok (r_, s') ∧ UD.PostO (ctxH C H) r_ w s' st)
      (fun r_ w s' H' => w = optW r_ ∧ peelPisW C.fe fuel n ci.toConstantVal.type s = .ok (r_, s'))
      (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu pvParams _ rfl hlk) (pv_spec C hok hc.pv fuel hf n H ci.toConstantVal.type s hpH hn)))
      (fun res w1 s1 H1 hp1 ⟨hw1, hrun1⟩ => ?_)
    have hs1 := RO.peelPisW _ _ _ _ s res s1 hrun1
    subst s1; subst hw1
    refine specR_callNIH (C := ctxH C H1) htW fRw rwParams [vv htV] (rwBody C) [optW res] (by decide) rfl (by decide) hc.rw
      ⟨by simp, trivial⟩ (PostOPW (ctxH C H1) s) (fun r_ w s' H' => s' = s ∧ optPW C H' s r_ w)
      (fun r_ w s' st ⟨hs, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hs, hw⟩, by rw [hs]; exact hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rwParams _ rfl hlk)
        (rw_spec C hok hc.rwc s hwf H1 res (hpH.trans hp1) (fun h u _ hv => hSD h u hv)))
      (fun pw' w2 s2 H2 hp2 ⟨hs2, hw2⟩ => ?_)
    subst s2
    rcases pw' with _ | pw
    · simp only [optPW] at hw2; subst hw2
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      try dsimp only
      exact specR_returnI _ 0 rfl (fun t ht => ⟨rdStep_refl hrd, H2, hp1.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    simp only [optPW] at hw2
    refine specR_atEntry fun t ht => ?_
    have hw0 : w2 ≠ 0 := by
      cases pw with
      | never => simp only [pwEnc] at hw2; subst hw2; decide
      | ifAllZero ps => obtain ⟨o', ns, rfl, hb', _⟩ := hw2; exact (cellA_big hok ht.sr (blkAt_lt hb')).1
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hw0) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    obtain ⟨ks, hks⟩ := hLP I ci hfind
    obtain ⟨vs, hdl, hvl2, hvd⟩ := hLS us vl hvl
    refine specR_congr (m' := substPWAt ci.toConstantVal.levelParams us pw >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H2) htS fSa saParams [.op .add [vv htLp, .const 8], vv htLl, vv htU, vv htW] (saBody C)
      [ecell C (ol + 1), BitVec.ofNat 64 ci.toConstantVal.levelParams.length, Enc.idxW us, w2] (by decide) rfl (by decide) hc.sa.self
      ⟨by simp [sev, hwl']; show ecell C ol + BitVec.ofNat 64 (8 * 1) = _; exact ecell_add C ol 1, by simp, by simp, by simp, trivial⟩
      (PostSA (ctxH C H2) s) (fun r_ w s' H' => RdStep s s' ∧ optPW C H' s r_ w)
      (fun r_ w s' st ⟨hst, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hst, hw⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu saParams _ rfl hlk)
        (sa_spec C hok hc.sa.codes s hwf hrd ci.toConstantVal.levelParams ks (ol + 1)
          (fun j hj => by have := hbl.2 j (by simpa using hj); simp only [List.getElem_map] at this; exact this)
          (LSub.denoteNList_get _ _ _ hks).1 hks hlp us vl vs hvl hvl2 hvd (by simpa using hvll) hdl H2 pw w2
          (hpH.trans (hp1.trans hp2)) hw2))
      (fun r w3 s3 H3 hp3 ⟨hst, hw3⟩ => ?_)
    exact specR_returnI _ w3 (by simp) (fun t ht => ⟨hst, H3, hp1.trans (hp2.trans hp3), hw3, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rdStep_refl hrd, H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rdStep_refl hrd, H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rdStep_refl hrd, H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rdStep_refl hrd, H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rdStep_refl hrd, H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rdStep_refl hrd, H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)


end

end ConPanqueque.T.WC
