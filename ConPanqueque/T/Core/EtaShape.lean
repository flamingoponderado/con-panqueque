import ConPanqueque.T.Core.StructEta
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `etaCtorShape` and `etaCtorPartial`

A stored constructor applied to exactly (`boolW`), or fewer than (`optWG ofNat` of the missing count, the family
η with a table naming it), its parameters and fields.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def esA := ofString "ece_esa"
def esH := ofString "ece_esh"
def esC := ofString "ece_esc"
def esU := ofString "ece_esu"
def esP := ofString "ece_esp"
def esQ := ofString "ece_esq"
def esK := ofString "ece_esk"
def esNp := ofString "ece_esnp"
def esNf := ofString "ece_esnf"
def esX := ofString "ece_esx"
def esL := ofString "ece_esl"
def epA := ofString "ece_epa"
def epH := ofString "ece_eph"
def epC := ofString "ece_epc"
def epU := ofString "ece_epu"
def epP := ofString "ece_epp"
def epQ := ofString "ece_epq"
def epK := ofString "ece_epk"
def epNp := ofString "ece_epnp"
def epNf := ofString "ece_epnf"
def epT := ofString "ece_ept"
def epX := ofString "ece_epx"
def epL := ofString "ece_epl"
def epP2 := ofString "ece_epp2"
def epQ2 := ofString "ece_epq2"
def epK2 := ofString "ece_epk2"
def epEt := ofString "ece_epet"
def epTb := ofString "ece_eptb"
def epTq := ofString "ece_eptq"
def epTc := ofString "ece_eptc"
def fEs := ofString "etaCtorShape"
def fEp := ofString "etaCtorPartial"

@[simp] theorem ece_esA_ne_esH : esA ≠ esH := by decide
@[simp] theorem ece_esA_ne_esC : esA ≠ esC := by decide
@[simp] theorem ece_esA_ne_esU : esA ≠ esU := by decide
@[simp] theorem ece_esA_ne_esP : esA ≠ esP := by decide
@[simp] theorem ece_esA_ne_esQ : esA ≠ esQ := by decide
@[simp] theorem ece_esA_ne_esK : esA ≠ esK := by decide
@[simp] theorem ece_esA_ne_esNp : esA ≠ esNp := by decide
@[simp] theorem ece_esA_ne_esNf : esA ≠ esNf := by decide
@[simp] theorem ece_esA_ne_esX : esA ≠ esX := by decide
@[simp] theorem ece_esA_ne_esL : esA ≠ esL := by decide
@[simp] theorem ece_esA_ne_epA : esA ≠ epA := by decide
@[simp] theorem ece_esA_ne_epH : esA ≠ epH := by decide
@[simp] theorem ece_esA_ne_epC : esA ≠ epC := by decide
@[simp] theorem ece_esA_ne_epU : esA ≠ epU := by decide
@[simp] theorem ece_esA_ne_epP : esA ≠ epP := by decide
@[simp] theorem ece_esA_ne_epQ : esA ≠ epQ := by decide
@[simp] theorem ece_esA_ne_epK : esA ≠ epK := by decide
@[simp] theorem ece_esA_ne_epNp : esA ≠ epNp := by decide
@[simp] theorem ece_esA_ne_epNf : esA ≠ epNf := by decide
@[simp] theorem ece_esA_ne_epT : esA ≠ epT := by decide
@[simp] theorem ece_esA_ne_epX : esA ≠ epX := by decide
@[simp] theorem ece_esA_ne_epL : esA ≠ epL := by decide
@[simp] theorem ece_esA_ne_epP2 : esA ≠ epP2 := by decide
@[simp] theorem ece_esA_ne_epQ2 : esA ≠ epQ2 := by decide
@[simp] theorem ece_esA_ne_epK2 : esA ≠ epK2 := by decide
@[simp] theorem ece_esA_ne_epEt : esA ≠ epEt := by decide
@[simp] theorem ece_esA_ne_epTb : esA ≠ epTb := by decide
@[simp] theorem ece_esA_ne_epTq : esA ≠ epTq := by decide
@[simp] theorem ece_esA_ne_epTc : esA ≠ epTc := by decide
@[simp] theorem ece_esA_ne_lFl : esA ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_esA : lFl ≠ esA := by decide
@[simp] theorem ece_esA_ne_lDh : esA ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_esA : lDh ≠ esA := by decide
@[simp] theorem ece_esA_ne_lDt : esA ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_esA : lDt ≠ esA := by decide
@[simp] theorem ece_esA_ne_lDg : esA ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_esA : lDg ≠ esA := by decide
@[simp] theorem ece_esA_ne_lDi : esA ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_esA : lDi ≠ esA := by decide
@[simp] theorem ece_esA_ne_lRp : esA ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_esA : lRp ≠ esA := by decide
@[simp] theorem ece_esA_ne_lRn : esA ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_esA : lRn ≠ esA := by decide
@[simp] theorem ece_esA_ne_lFle : esA ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_esA : lFle ≠ esA := by decide
@[simp] theorem ece_esA_ne_lKb : esA ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_esA : lKb ≠ esA := by decide
@[simp] theorem ece_esA_ne_lDir : esA ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_esA : lDir ≠ esA := by decide
@[simp] theorem ece_esA_ne_lFln : esA ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_esA : lFln ≠ esA := by decide
@[simp] theorem ece_esA_ne_lFll : esA ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_esA : lFll ≠ esA := by decide
@[simp] theorem ece_esA_ne_lFls : esA ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_esA : lFls ≠ esA := by decide
@[simp] theorem ece_esA_ne_kFu : esA ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_esA : kFu ≠ esA := by decide
@[simp] theorem ece_esA_ne_kD : esA ≠ kD := by decide
@[simp] theorem ece_kD_ne_esA : kD ≠ esA := by decide
@[simp] theorem ece_esH_ne_esA : esH ≠ esA := by decide
@[simp] theorem ece_esH_ne_esC : esH ≠ esC := by decide
@[simp] theorem ece_esH_ne_esU : esH ≠ esU := by decide
@[simp] theorem ece_esH_ne_esP : esH ≠ esP := by decide
@[simp] theorem ece_esH_ne_esQ : esH ≠ esQ := by decide
@[simp] theorem ece_esH_ne_esK : esH ≠ esK := by decide
@[simp] theorem ece_esH_ne_esNp : esH ≠ esNp := by decide
@[simp] theorem ece_esH_ne_esNf : esH ≠ esNf := by decide
@[simp] theorem ece_esH_ne_esX : esH ≠ esX := by decide
@[simp] theorem ece_esH_ne_esL : esH ≠ esL := by decide
@[simp] theorem ece_esH_ne_epA : esH ≠ epA := by decide
@[simp] theorem ece_esH_ne_epH : esH ≠ epH := by decide
@[simp] theorem ece_esH_ne_epC : esH ≠ epC := by decide
@[simp] theorem ece_esH_ne_epU : esH ≠ epU := by decide
@[simp] theorem ece_esH_ne_epP : esH ≠ epP := by decide
@[simp] theorem ece_esH_ne_epQ : esH ≠ epQ := by decide
@[simp] theorem ece_esH_ne_epK : esH ≠ epK := by decide
@[simp] theorem ece_esH_ne_epNp : esH ≠ epNp := by decide
@[simp] theorem ece_esH_ne_epNf : esH ≠ epNf := by decide
@[simp] theorem ece_esH_ne_epT : esH ≠ epT := by decide
@[simp] theorem ece_esH_ne_epX : esH ≠ epX := by decide
@[simp] theorem ece_esH_ne_epL : esH ≠ epL := by decide
@[simp] theorem ece_esH_ne_epP2 : esH ≠ epP2 := by decide
@[simp] theorem ece_esH_ne_epQ2 : esH ≠ epQ2 := by decide
@[simp] theorem ece_esH_ne_epK2 : esH ≠ epK2 := by decide
@[simp] theorem ece_esH_ne_epEt : esH ≠ epEt := by decide
@[simp] theorem ece_esH_ne_epTb : esH ≠ epTb := by decide
@[simp] theorem ece_esH_ne_epTq : esH ≠ epTq := by decide
@[simp] theorem ece_esH_ne_epTc : esH ≠ epTc := by decide
@[simp] theorem ece_esH_ne_lFl : esH ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_esH : lFl ≠ esH := by decide
@[simp] theorem ece_esH_ne_lDh : esH ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_esH : lDh ≠ esH := by decide
@[simp] theorem ece_esH_ne_lDt : esH ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_esH : lDt ≠ esH := by decide
@[simp] theorem ece_esH_ne_lDg : esH ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_esH : lDg ≠ esH := by decide
@[simp] theorem ece_esH_ne_lDi : esH ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_esH : lDi ≠ esH := by decide
@[simp] theorem ece_esH_ne_lRp : esH ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_esH : lRp ≠ esH := by decide
@[simp] theorem ece_esH_ne_lRn : esH ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_esH : lRn ≠ esH := by decide
@[simp] theorem ece_esH_ne_lFle : esH ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_esH : lFle ≠ esH := by decide
@[simp] theorem ece_esH_ne_lKb : esH ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_esH : lKb ≠ esH := by decide
@[simp] theorem ece_esH_ne_lDir : esH ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_esH : lDir ≠ esH := by decide
@[simp] theorem ece_esH_ne_lFln : esH ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_esH : lFln ≠ esH := by decide
@[simp] theorem ece_esH_ne_lFll : esH ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_esH : lFll ≠ esH := by decide
@[simp] theorem ece_esH_ne_lFls : esH ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_esH : lFls ≠ esH := by decide
@[simp] theorem ece_esH_ne_kFu : esH ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_esH : kFu ≠ esH := by decide
@[simp] theorem ece_esH_ne_kD : esH ≠ kD := by decide
@[simp] theorem ece_kD_ne_esH : kD ≠ esH := by decide
@[simp] theorem ece_esC_ne_esA : esC ≠ esA := by decide
@[simp] theorem ece_esC_ne_esH : esC ≠ esH := by decide
@[simp] theorem ece_esC_ne_esU : esC ≠ esU := by decide
@[simp] theorem ece_esC_ne_esP : esC ≠ esP := by decide
@[simp] theorem ece_esC_ne_esQ : esC ≠ esQ := by decide
@[simp] theorem ece_esC_ne_esK : esC ≠ esK := by decide
@[simp] theorem ece_esC_ne_esNp : esC ≠ esNp := by decide
@[simp] theorem ece_esC_ne_esNf : esC ≠ esNf := by decide
@[simp] theorem ece_esC_ne_esX : esC ≠ esX := by decide
@[simp] theorem ece_esC_ne_esL : esC ≠ esL := by decide
@[simp] theorem ece_esC_ne_epA : esC ≠ epA := by decide
@[simp] theorem ece_esC_ne_epH : esC ≠ epH := by decide
@[simp] theorem ece_esC_ne_epC : esC ≠ epC := by decide
@[simp] theorem ece_esC_ne_epU : esC ≠ epU := by decide
@[simp] theorem ece_esC_ne_epP : esC ≠ epP := by decide
@[simp] theorem ece_esC_ne_epQ : esC ≠ epQ := by decide
@[simp] theorem ece_esC_ne_epK : esC ≠ epK := by decide
@[simp] theorem ece_esC_ne_epNp : esC ≠ epNp := by decide
@[simp] theorem ece_esC_ne_epNf : esC ≠ epNf := by decide
@[simp] theorem ece_esC_ne_epT : esC ≠ epT := by decide
@[simp] theorem ece_esC_ne_epX : esC ≠ epX := by decide
@[simp] theorem ece_esC_ne_epL : esC ≠ epL := by decide
@[simp] theorem ece_esC_ne_epP2 : esC ≠ epP2 := by decide
@[simp] theorem ece_esC_ne_epQ2 : esC ≠ epQ2 := by decide
@[simp] theorem ece_esC_ne_epK2 : esC ≠ epK2 := by decide
@[simp] theorem ece_esC_ne_epEt : esC ≠ epEt := by decide
@[simp] theorem ece_esC_ne_epTb : esC ≠ epTb := by decide
@[simp] theorem ece_esC_ne_epTq : esC ≠ epTq := by decide
@[simp] theorem ece_esC_ne_epTc : esC ≠ epTc := by decide
@[simp] theorem ece_esC_ne_lFl : esC ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_esC : lFl ≠ esC := by decide
@[simp] theorem ece_esC_ne_lDh : esC ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_esC : lDh ≠ esC := by decide
@[simp] theorem ece_esC_ne_lDt : esC ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_esC : lDt ≠ esC := by decide
@[simp] theorem ece_esC_ne_lDg : esC ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_esC : lDg ≠ esC := by decide
@[simp] theorem ece_esC_ne_lDi : esC ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_esC : lDi ≠ esC := by decide
@[simp] theorem ece_esC_ne_lRp : esC ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_esC : lRp ≠ esC := by decide
@[simp] theorem ece_esC_ne_lRn : esC ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_esC : lRn ≠ esC := by decide
@[simp] theorem ece_esC_ne_lFle : esC ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_esC : lFle ≠ esC := by decide
@[simp] theorem ece_esC_ne_lKb : esC ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_esC : lKb ≠ esC := by decide
@[simp] theorem ece_esC_ne_lDir : esC ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_esC : lDir ≠ esC := by decide
@[simp] theorem ece_esC_ne_lFln : esC ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_esC : lFln ≠ esC := by decide
@[simp] theorem ece_esC_ne_lFll : esC ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_esC : lFll ≠ esC := by decide
@[simp] theorem ece_esC_ne_lFls : esC ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_esC : lFls ≠ esC := by decide
@[simp] theorem ece_esC_ne_kFu : esC ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_esC : kFu ≠ esC := by decide
@[simp] theorem ece_esC_ne_kD : esC ≠ kD := by decide
@[simp] theorem ece_kD_ne_esC : kD ≠ esC := by decide
@[simp] theorem ece_esU_ne_esA : esU ≠ esA := by decide
@[simp] theorem ece_esU_ne_esH : esU ≠ esH := by decide
@[simp] theorem ece_esU_ne_esC : esU ≠ esC := by decide
@[simp] theorem ece_esU_ne_esP : esU ≠ esP := by decide
@[simp] theorem ece_esU_ne_esQ : esU ≠ esQ := by decide
@[simp] theorem ece_esU_ne_esK : esU ≠ esK := by decide
@[simp] theorem ece_esU_ne_esNp : esU ≠ esNp := by decide
@[simp] theorem ece_esU_ne_esNf : esU ≠ esNf := by decide
@[simp] theorem ece_esU_ne_esX : esU ≠ esX := by decide
@[simp] theorem ece_esU_ne_esL : esU ≠ esL := by decide
@[simp] theorem ece_esU_ne_epA : esU ≠ epA := by decide
@[simp] theorem ece_esU_ne_epH : esU ≠ epH := by decide
@[simp] theorem ece_esU_ne_epC : esU ≠ epC := by decide
@[simp] theorem ece_esU_ne_epU : esU ≠ epU := by decide
@[simp] theorem ece_esU_ne_epP : esU ≠ epP := by decide
@[simp] theorem ece_esU_ne_epQ : esU ≠ epQ := by decide
@[simp] theorem ece_esU_ne_epK : esU ≠ epK := by decide
@[simp] theorem ece_esU_ne_epNp : esU ≠ epNp := by decide
@[simp] theorem ece_esU_ne_epNf : esU ≠ epNf := by decide
@[simp] theorem ece_esU_ne_epT : esU ≠ epT := by decide
@[simp] theorem ece_esU_ne_epX : esU ≠ epX := by decide
@[simp] theorem ece_esU_ne_epL : esU ≠ epL := by decide
@[simp] theorem ece_esU_ne_epP2 : esU ≠ epP2 := by decide
@[simp] theorem ece_esU_ne_epQ2 : esU ≠ epQ2 := by decide
@[simp] theorem ece_esU_ne_epK2 : esU ≠ epK2 := by decide
@[simp] theorem ece_esU_ne_epEt : esU ≠ epEt := by decide
@[simp] theorem ece_esU_ne_epTb : esU ≠ epTb := by decide
@[simp] theorem ece_esU_ne_epTq : esU ≠ epTq := by decide
@[simp] theorem ece_esU_ne_epTc : esU ≠ epTc := by decide
@[simp] theorem ece_esU_ne_lFl : esU ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_esU : lFl ≠ esU := by decide
@[simp] theorem ece_esU_ne_lDh : esU ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_esU : lDh ≠ esU := by decide
@[simp] theorem ece_esU_ne_lDt : esU ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_esU : lDt ≠ esU := by decide
@[simp] theorem ece_esU_ne_lDg : esU ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_esU : lDg ≠ esU := by decide
@[simp] theorem ece_esU_ne_lDi : esU ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_esU : lDi ≠ esU := by decide
@[simp] theorem ece_esU_ne_lRp : esU ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_esU : lRp ≠ esU := by decide
@[simp] theorem ece_esU_ne_lRn : esU ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_esU : lRn ≠ esU := by decide
@[simp] theorem ece_esU_ne_lFle : esU ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_esU : lFle ≠ esU := by decide
@[simp] theorem ece_esU_ne_lKb : esU ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_esU : lKb ≠ esU := by decide
@[simp] theorem ece_esU_ne_lDir : esU ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_esU : lDir ≠ esU := by decide
@[simp] theorem ece_esU_ne_lFln : esU ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_esU : lFln ≠ esU := by decide
@[simp] theorem ece_esU_ne_lFll : esU ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_esU : lFll ≠ esU := by decide
@[simp] theorem ece_esU_ne_lFls : esU ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_esU : lFls ≠ esU := by decide
@[simp] theorem ece_esU_ne_kFu : esU ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_esU : kFu ≠ esU := by decide
@[simp] theorem ece_esU_ne_kD : esU ≠ kD := by decide
@[simp] theorem ece_kD_ne_esU : kD ≠ esU := by decide
@[simp] theorem ece_esP_ne_esA : esP ≠ esA := by decide
@[simp] theorem ece_esP_ne_esH : esP ≠ esH := by decide
@[simp] theorem ece_esP_ne_esC : esP ≠ esC := by decide
@[simp] theorem ece_esP_ne_esU : esP ≠ esU := by decide
@[simp] theorem ece_esP_ne_esQ : esP ≠ esQ := by decide
@[simp] theorem ece_esP_ne_esK : esP ≠ esK := by decide
@[simp] theorem ece_esP_ne_esNp : esP ≠ esNp := by decide
@[simp] theorem ece_esP_ne_esNf : esP ≠ esNf := by decide
@[simp] theorem ece_esP_ne_esX : esP ≠ esX := by decide
@[simp] theorem ece_esP_ne_esL : esP ≠ esL := by decide
@[simp] theorem ece_esP_ne_epA : esP ≠ epA := by decide
@[simp] theorem ece_esP_ne_epH : esP ≠ epH := by decide
@[simp] theorem ece_esP_ne_epC : esP ≠ epC := by decide
@[simp] theorem ece_esP_ne_epU : esP ≠ epU := by decide
@[simp] theorem ece_esP_ne_epP : esP ≠ epP := by decide
@[simp] theorem ece_esP_ne_epQ : esP ≠ epQ := by decide
@[simp] theorem ece_esP_ne_epK : esP ≠ epK := by decide
@[simp] theorem ece_esP_ne_epNp : esP ≠ epNp := by decide
@[simp] theorem ece_esP_ne_epNf : esP ≠ epNf := by decide
@[simp] theorem ece_esP_ne_epT : esP ≠ epT := by decide
@[simp] theorem ece_esP_ne_epX : esP ≠ epX := by decide
@[simp] theorem ece_esP_ne_epL : esP ≠ epL := by decide
@[simp] theorem ece_esP_ne_epP2 : esP ≠ epP2 := by decide
@[simp] theorem ece_esP_ne_epQ2 : esP ≠ epQ2 := by decide
@[simp] theorem ece_esP_ne_epK2 : esP ≠ epK2 := by decide
@[simp] theorem ece_esP_ne_epEt : esP ≠ epEt := by decide
@[simp] theorem ece_esP_ne_epTb : esP ≠ epTb := by decide
@[simp] theorem ece_esP_ne_epTq : esP ≠ epTq := by decide
@[simp] theorem ece_esP_ne_epTc : esP ≠ epTc := by decide
@[simp] theorem ece_esP_ne_lFl : esP ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_esP : lFl ≠ esP := by decide
@[simp] theorem ece_esP_ne_lDh : esP ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_esP : lDh ≠ esP := by decide
@[simp] theorem ece_esP_ne_lDt : esP ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_esP : lDt ≠ esP := by decide
@[simp] theorem ece_esP_ne_lDg : esP ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_esP : lDg ≠ esP := by decide
@[simp] theorem ece_esP_ne_lDi : esP ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_esP : lDi ≠ esP := by decide
@[simp] theorem ece_esP_ne_lRp : esP ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_esP : lRp ≠ esP := by decide
@[simp] theorem ece_esP_ne_lRn : esP ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_esP : lRn ≠ esP := by decide
@[simp] theorem ece_esP_ne_lFle : esP ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_esP : lFle ≠ esP := by decide
@[simp] theorem ece_esP_ne_lKb : esP ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_esP : lKb ≠ esP := by decide
@[simp] theorem ece_esP_ne_lDir : esP ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_esP : lDir ≠ esP := by decide
@[simp] theorem ece_esP_ne_lFln : esP ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_esP : lFln ≠ esP := by decide
@[simp] theorem ece_esP_ne_lFll : esP ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_esP : lFll ≠ esP := by decide
@[simp] theorem ece_esP_ne_lFls : esP ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_esP : lFls ≠ esP := by decide
@[simp] theorem ece_esP_ne_kFu : esP ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_esP : kFu ≠ esP := by decide
@[simp] theorem ece_esP_ne_kD : esP ≠ kD := by decide
@[simp] theorem ece_kD_ne_esP : kD ≠ esP := by decide
@[simp] theorem ece_esQ_ne_esA : esQ ≠ esA := by decide
@[simp] theorem ece_esQ_ne_esH : esQ ≠ esH := by decide
@[simp] theorem ece_esQ_ne_esC : esQ ≠ esC := by decide
@[simp] theorem ece_esQ_ne_esU : esQ ≠ esU := by decide
@[simp] theorem ece_esQ_ne_esP : esQ ≠ esP := by decide
@[simp] theorem ece_esQ_ne_esK : esQ ≠ esK := by decide
@[simp] theorem ece_esQ_ne_esNp : esQ ≠ esNp := by decide
@[simp] theorem ece_esQ_ne_esNf : esQ ≠ esNf := by decide
@[simp] theorem ece_esQ_ne_esX : esQ ≠ esX := by decide
@[simp] theorem ece_esQ_ne_esL : esQ ≠ esL := by decide
@[simp] theorem ece_esQ_ne_epA : esQ ≠ epA := by decide
@[simp] theorem ece_esQ_ne_epH : esQ ≠ epH := by decide
@[simp] theorem ece_esQ_ne_epC : esQ ≠ epC := by decide
@[simp] theorem ece_esQ_ne_epU : esQ ≠ epU := by decide
@[simp] theorem ece_esQ_ne_epP : esQ ≠ epP := by decide
@[simp] theorem ece_esQ_ne_epQ : esQ ≠ epQ := by decide
@[simp] theorem ece_esQ_ne_epK : esQ ≠ epK := by decide
@[simp] theorem ece_esQ_ne_epNp : esQ ≠ epNp := by decide
@[simp] theorem ece_esQ_ne_epNf : esQ ≠ epNf := by decide
@[simp] theorem ece_esQ_ne_epT : esQ ≠ epT := by decide
@[simp] theorem ece_esQ_ne_epX : esQ ≠ epX := by decide
@[simp] theorem ece_esQ_ne_epL : esQ ≠ epL := by decide
@[simp] theorem ece_esQ_ne_epP2 : esQ ≠ epP2 := by decide
@[simp] theorem ece_esQ_ne_epQ2 : esQ ≠ epQ2 := by decide
@[simp] theorem ece_esQ_ne_epK2 : esQ ≠ epK2 := by decide
@[simp] theorem ece_esQ_ne_epEt : esQ ≠ epEt := by decide
@[simp] theorem ece_esQ_ne_epTb : esQ ≠ epTb := by decide
@[simp] theorem ece_esQ_ne_epTq : esQ ≠ epTq := by decide
@[simp] theorem ece_esQ_ne_epTc : esQ ≠ epTc := by decide
@[simp] theorem ece_esQ_ne_lFl : esQ ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_esQ : lFl ≠ esQ := by decide
@[simp] theorem ece_esQ_ne_lDh : esQ ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_esQ : lDh ≠ esQ := by decide
@[simp] theorem ece_esQ_ne_lDt : esQ ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_esQ : lDt ≠ esQ := by decide
@[simp] theorem ece_esQ_ne_lDg : esQ ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_esQ : lDg ≠ esQ := by decide
@[simp] theorem ece_esQ_ne_lDi : esQ ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_esQ : lDi ≠ esQ := by decide
@[simp] theorem ece_esQ_ne_lRp : esQ ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_esQ : lRp ≠ esQ := by decide
@[simp] theorem ece_esQ_ne_lRn : esQ ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_esQ : lRn ≠ esQ := by decide
@[simp] theorem ece_esQ_ne_lFle : esQ ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_esQ : lFle ≠ esQ := by decide
@[simp] theorem ece_esQ_ne_lKb : esQ ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_esQ : lKb ≠ esQ := by decide
@[simp] theorem ece_esQ_ne_lDir : esQ ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_esQ : lDir ≠ esQ := by decide
@[simp] theorem ece_esQ_ne_lFln : esQ ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_esQ : lFln ≠ esQ := by decide
@[simp] theorem ece_esQ_ne_lFll : esQ ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_esQ : lFll ≠ esQ := by decide
@[simp] theorem ece_esQ_ne_lFls : esQ ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_esQ : lFls ≠ esQ := by decide
@[simp] theorem ece_esQ_ne_kFu : esQ ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_esQ : kFu ≠ esQ := by decide
@[simp] theorem ece_esQ_ne_kD : esQ ≠ kD := by decide
@[simp] theorem ece_kD_ne_esQ : kD ≠ esQ := by decide
@[simp] theorem ece_esK_ne_esA : esK ≠ esA := by decide
@[simp] theorem ece_esK_ne_esH : esK ≠ esH := by decide
@[simp] theorem ece_esK_ne_esC : esK ≠ esC := by decide
@[simp] theorem ece_esK_ne_esU : esK ≠ esU := by decide
@[simp] theorem ece_esK_ne_esP : esK ≠ esP := by decide
@[simp] theorem ece_esK_ne_esQ : esK ≠ esQ := by decide
@[simp] theorem ece_esK_ne_esNp : esK ≠ esNp := by decide
@[simp] theorem ece_esK_ne_esNf : esK ≠ esNf := by decide
@[simp] theorem ece_esK_ne_esX : esK ≠ esX := by decide
@[simp] theorem ece_esK_ne_esL : esK ≠ esL := by decide
@[simp] theorem ece_esK_ne_epA : esK ≠ epA := by decide
@[simp] theorem ece_esK_ne_epH : esK ≠ epH := by decide
@[simp] theorem ece_esK_ne_epC : esK ≠ epC := by decide
@[simp] theorem ece_esK_ne_epU : esK ≠ epU := by decide
@[simp] theorem ece_esK_ne_epP : esK ≠ epP := by decide
@[simp] theorem ece_esK_ne_epQ : esK ≠ epQ := by decide
@[simp] theorem ece_esK_ne_epK : esK ≠ epK := by decide
@[simp] theorem ece_esK_ne_epNp : esK ≠ epNp := by decide
@[simp] theorem ece_esK_ne_epNf : esK ≠ epNf := by decide
@[simp] theorem ece_esK_ne_epT : esK ≠ epT := by decide
@[simp] theorem ece_esK_ne_epX : esK ≠ epX := by decide
@[simp] theorem ece_esK_ne_epL : esK ≠ epL := by decide
@[simp] theorem ece_esK_ne_epP2 : esK ≠ epP2 := by decide
@[simp] theorem ece_esK_ne_epQ2 : esK ≠ epQ2 := by decide
@[simp] theorem ece_esK_ne_epK2 : esK ≠ epK2 := by decide
@[simp] theorem ece_esK_ne_epEt : esK ≠ epEt := by decide
@[simp] theorem ece_esK_ne_epTb : esK ≠ epTb := by decide
@[simp] theorem ece_esK_ne_epTq : esK ≠ epTq := by decide
@[simp] theorem ece_esK_ne_epTc : esK ≠ epTc := by decide
@[simp] theorem ece_esK_ne_lFl : esK ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_esK : lFl ≠ esK := by decide
@[simp] theorem ece_esK_ne_lDh : esK ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_esK : lDh ≠ esK := by decide
@[simp] theorem ece_esK_ne_lDt : esK ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_esK : lDt ≠ esK := by decide
@[simp] theorem ece_esK_ne_lDg : esK ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_esK : lDg ≠ esK := by decide
@[simp] theorem ece_esK_ne_lDi : esK ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_esK : lDi ≠ esK := by decide
@[simp] theorem ece_esK_ne_lRp : esK ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_esK : lRp ≠ esK := by decide
@[simp] theorem ece_esK_ne_lRn : esK ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_esK : lRn ≠ esK := by decide
@[simp] theorem ece_esK_ne_lFle : esK ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_esK : lFle ≠ esK := by decide
@[simp] theorem ece_esK_ne_lKb : esK ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_esK : lKb ≠ esK := by decide
@[simp] theorem ece_esK_ne_lDir : esK ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_esK : lDir ≠ esK := by decide
@[simp] theorem ece_esK_ne_lFln : esK ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_esK : lFln ≠ esK := by decide
@[simp] theorem ece_esK_ne_lFll : esK ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_esK : lFll ≠ esK := by decide
@[simp] theorem ece_esK_ne_lFls : esK ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_esK : lFls ≠ esK := by decide
@[simp] theorem ece_esK_ne_kFu : esK ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_esK : kFu ≠ esK := by decide
@[simp] theorem ece_esK_ne_kD : esK ≠ kD := by decide
@[simp] theorem ece_kD_ne_esK : kD ≠ esK := by decide
@[simp] theorem ece_esNp_ne_esA : esNp ≠ esA := by decide
@[simp] theorem ece_esNp_ne_esH : esNp ≠ esH := by decide
@[simp] theorem ece_esNp_ne_esC : esNp ≠ esC := by decide
@[simp] theorem ece_esNp_ne_esU : esNp ≠ esU := by decide
@[simp] theorem ece_esNp_ne_esP : esNp ≠ esP := by decide
@[simp] theorem ece_esNp_ne_esQ : esNp ≠ esQ := by decide
@[simp] theorem ece_esNp_ne_esK : esNp ≠ esK := by decide
@[simp] theorem ece_esNp_ne_esNf : esNp ≠ esNf := by decide
@[simp] theorem ece_esNp_ne_esX : esNp ≠ esX := by decide
@[simp] theorem ece_esNp_ne_esL : esNp ≠ esL := by decide
@[simp] theorem ece_esNp_ne_epA : esNp ≠ epA := by decide
@[simp] theorem ece_esNp_ne_epH : esNp ≠ epH := by decide
@[simp] theorem ece_esNp_ne_epC : esNp ≠ epC := by decide
@[simp] theorem ece_esNp_ne_epU : esNp ≠ epU := by decide
@[simp] theorem ece_esNp_ne_epP : esNp ≠ epP := by decide
@[simp] theorem ece_esNp_ne_epQ : esNp ≠ epQ := by decide
@[simp] theorem ece_esNp_ne_epK : esNp ≠ epK := by decide
@[simp] theorem ece_esNp_ne_epNp : esNp ≠ epNp := by decide
@[simp] theorem ece_esNp_ne_epNf : esNp ≠ epNf := by decide
@[simp] theorem ece_esNp_ne_epT : esNp ≠ epT := by decide
@[simp] theorem ece_esNp_ne_epX : esNp ≠ epX := by decide
@[simp] theorem ece_esNp_ne_epL : esNp ≠ epL := by decide
@[simp] theorem ece_esNp_ne_epP2 : esNp ≠ epP2 := by decide
@[simp] theorem ece_esNp_ne_epQ2 : esNp ≠ epQ2 := by decide
@[simp] theorem ece_esNp_ne_epK2 : esNp ≠ epK2 := by decide
@[simp] theorem ece_esNp_ne_epEt : esNp ≠ epEt := by decide
@[simp] theorem ece_esNp_ne_epTb : esNp ≠ epTb := by decide
@[simp] theorem ece_esNp_ne_epTq : esNp ≠ epTq := by decide
@[simp] theorem ece_esNp_ne_epTc : esNp ≠ epTc := by decide
@[simp] theorem ece_esNp_ne_lFl : esNp ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_esNp : lFl ≠ esNp := by decide
@[simp] theorem ece_esNp_ne_lDh : esNp ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_esNp : lDh ≠ esNp := by decide
@[simp] theorem ece_esNp_ne_lDt : esNp ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_esNp : lDt ≠ esNp := by decide
@[simp] theorem ece_esNp_ne_lDg : esNp ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_esNp : lDg ≠ esNp := by decide
@[simp] theorem ece_esNp_ne_lDi : esNp ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_esNp : lDi ≠ esNp := by decide
@[simp] theorem ece_esNp_ne_lRp : esNp ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_esNp : lRp ≠ esNp := by decide
@[simp] theorem ece_esNp_ne_lRn : esNp ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_esNp : lRn ≠ esNp := by decide
@[simp] theorem ece_esNp_ne_lFle : esNp ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_esNp : lFle ≠ esNp := by decide
@[simp] theorem ece_esNp_ne_lKb : esNp ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_esNp : lKb ≠ esNp := by decide
@[simp] theorem ece_esNp_ne_lDir : esNp ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_esNp : lDir ≠ esNp := by decide
@[simp] theorem ece_esNp_ne_lFln : esNp ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_esNp : lFln ≠ esNp := by decide
@[simp] theorem ece_esNp_ne_lFll : esNp ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_esNp : lFll ≠ esNp := by decide
@[simp] theorem ece_esNp_ne_lFls : esNp ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_esNp : lFls ≠ esNp := by decide
@[simp] theorem ece_esNp_ne_kFu : esNp ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_esNp : kFu ≠ esNp := by decide
@[simp] theorem ece_esNp_ne_kD : esNp ≠ kD := by decide
@[simp] theorem ece_kD_ne_esNp : kD ≠ esNp := by decide
@[simp] theorem ece_esNf_ne_esA : esNf ≠ esA := by decide
@[simp] theorem ece_esNf_ne_esH : esNf ≠ esH := by decide
@[simp] theorem ece_esNf_ne_esC : esNf ≠ esC := by decide
@[simp] theorem ece_esNf_ne_esU : esNf ≠ esU := by decide
@[simp] theorem ece_esNf_ne_esP : esNf ≠ esP := by decide
@[simp] theorem ece_esNf_ne_esQ : esNf ≠ esQ := by decide
@[simp] theorem ece_esNf_ne_esK : esNf ≠ esK := by decide
@[simp] theorem ece_esNf_ne_esNp : esNf ≠ esNp := by decide
@[simp] theorem ece_esNf_ne_esX : esNf ≠ esX := by decide
@[simp] theorem ece_esNf_ne_esL : esNf ≠ esL := by decide
@[simp] theorem ece_esNf_ne_epA : esNf ≠ epA := by decide
@[simp] theorem ece_esNf_ne_epH : esNf ≠ epH := by decide
@[simp] theorem ece_esNf_ne_epC : esNf ≠ epC := by decide
@[simp] theorem ece_esNf_ne_epU : esNf ≠ epU := by decide
@[simp] theorem ece_esNf_ne_epP : esNf ≠ epP := by decide
@[simp] theorem ece_esNf_ne_epQ : esNf ≠ epQ := by decide
@[simp] theorem ece_esNf_ne_epK : esNf ≠ epK := by decide
@[simp] theorem ece_esNf_ne_epNp : esNf ≠ epNp := by decide
@[simp] theorem ece_esNf_ne_epNf : esNf ≠ epNf := by decide
@[simp] theorem ece_esNf_ne_epT : esNf ≠ epT := by decide
@[simp] theorem ece_esNf_ne_epX : esNf ≠ epX := by decide
@[simp] theorem ece_esNf_ne_epL : esNf ≠ epL := by decide
@[simp] theorem ece_esNf_ne_epP2 : esNf ≠ epP2 := by decide
@[simp] theorem ece_esNf_ne_epQ2 : esNf ≠ epQ2 := by decide
@[simp] theorem ece_esNf_ne_epK2 : esNf ≠ epK2 := by decide
@[simp] theorem ece_esNf_ne_epEt : esNf ≠ epEt := by decide
@[simp] theorem ece_esNf_ne_epTb : esNf ≠ epTb := by decide
@[simp] theorem ece_esNf_ne_epTq : esNf ≠ epTq := by decide
@[simp] theorem ece_esNf_ne_epTc : esNf ≠ epTc := by decide
@[simp] theorem ece_esNf_ne_lFl : esNf ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_esNf : lFl ≠ esNf := by decide
@[simp] theorem ece_esNf_ne_lDh : esNf ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_esNf : lDh ≠ esNf := by decide
@[simp] theorem ece_esNf_ne_lDt : esNf ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_esNf : lDt ≠ esNf := by decide
@[simp] theorem ece_esNf_ne_lDg : esNf ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_esNf : lDg ≠ esNf := by decide
@[simp] theorem ece_esNf_ne_lDi : esNf ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_esNf : lDi ≠ esNf := by decide
@[simp] theorem ece_esNf_ne_lRp : esNf ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_esNf : lRp ≠ esNf := by decide
@[simp] theorem ece_esNf_ne_lRn : esNf ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_esNf : lRn ≠ esNf := by decide
@[simp] theorem ece_esNf_ne_lFle : esNf ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_esNf : lFle ≠ esNf := by decide
@[simp] theorem ece_esNf_ne_lKb : esNf ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_esNf : lKb ≠ esNf := by decide
@[simp] theorem ece_esNf_ne_lDir : esNf ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_esNf : lDir ≠ esNf := by decide
@[simp] theorem ece_esNf_ne_lFln : esNf ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_esNf : lFln ≠ esNf := by decide
@[simp] theorem ece_esNf_ne_lFll : esNf ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_esNf : lFll ≠ esNf := by decide
@[simp] theorem ece_esNf_ne_lFls : esNf ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_esNf : lFls ≠ esNf := by decide
@[simp] theorem ece_esNf_ne_kFu : esNf ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_esNf : kFu ≠ esNf := by decide
@[simp] theorem ece_esNf_ne_kD : esNf ≠ kD := by decide
@[simp] theorem ece_kD_ne_esNf : kD ≠ esNf := by decide
@[simp] theorem ece_esX_ne_esA : esX ≠ esA := by decide
@[simp] theorem ece_esX_ne_esH : esX ≠ esH := by decide
@[simp] theorem ece_esX_ne_esC : esX ≠ esC := by decide
@[simp] theorem ece_esX_ne_esU : esX ≠ esU := by decide
@[simp] theorem ece_esX_ne_esP : esX ≠ esP := by decide
@[simp] theorem ece_esX_ne_esQ : esX ≠ esQ := by decide
@[simp] theorem ece_esX_ne_esK : esX ≠ esK := by decide
@[simp] theorem ece_esX_ne_esNp : esX ≠ esNp := by decide
@[simp] theorem ece_esX_ne_esNf : esX ≠ esNf := by decide
@[simp] theorem ece_esX_ne_esL : esX ≠ esL := by decide
@[simp] theorem ece_esX_ne_epA : esX ≠ epA := by decide
@[simp] theorem ece_esX_ne_epH : esX ≠ epH := by decide
@[simp] theorem ece_esX_ne_epC : esX ≠ epC := by decide
@[simp] theorem ece_esX_ne_epU : esX ≠ epU := by decide
@[simp] theorem ece_esX_ne_epP : esX ≠ epP := by decide
@[simp] theorem ece_esX_ne_epQ : esX ≠ epQ := by decide
@[simp] theorem ece_esX_ne_epK : esX ≠ epK := by decide
@[simp] theorem ece_esX_ne_epNp : esX ≠ epNp := by decide
@[simp] theorem ece_esX_ne_epNf : esX ≠ epNf := by decide
@[simp] theorem ece_esX_ne_epT : esX ≠ epT := by decide
@[simp] theorem ece_esX_ne_epX : esX ≠ epX := by decide
@[simp] theorem ece_esX_ne_epL : esX ≠ epL := by decide
@[simp] theorem ece_esX_ne_epP2 : esX ≠ epP2 := by decide
@[simp] theorem ece_esX_ne_epQ2 : esX ≠ epQ2 := by decide
@[simp] theorem ece_esX_ne_epK2 : esX ≠ epK2 := by decide
@[simp] theorem ece_esX_ne_epEt : esX ≠ epEt := by decide
@[simp] theorem ece_esX_ne_epTb : esX ≠ epTb := by decide
@[simp] theorem ece_esX_ne_epTq : esX ≠ epTq := by decide
@[simp] theorem ece_esX_ne_epTc : esX ≠ epTc := by decide
@[simp] theorem ece_esX_ne_lFl : esX ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_esX : lFl ≠ esX := by decide
@[simp] theorem ece_esX_ne_lDh : esX ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_esX : lDh ≠ esX := by decide
@[simp] theorem ece_esX_ne_lDt : esX ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_esX : lDt ≠ esX := by decide
@[simp] theorem ece_esX_ne_lDg : esX ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_esX : lDg ≠ esX := by decide
@[simp] theorem ece_esX_ne_lDi : esX ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_esX : lDi ≠ esX := by decide
@[simp] theorem ece_esX_ne_lRp : esX ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_esX : lRp ≠ esX := by decide
@[simp] theorem ece_esX_ne_lRn : esX ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_esX : lRn ≠ esX := by decide
@[simp] theorem ece_esX_ne_lFle : esX ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_esX : lFle ≠ esX := by decide
@[simp] theorem ece_esX_ne_lKb : esX ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_esX : lKb ≠ esX := by decide
@[simp] theorem ece_esX_ne_lDir : esX ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_esX : lDir ≠ esX := by decide
@[simp] theorem ece_esX_ne_lFln : esX ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_esX : lFln ≠ esX := by decide
@[simp] theorem ece_esX_ne_lFll : esX ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_esX : lFll ≠ esX := by decide
@[simp] theorem ece_esX_ne_lFls : esX ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_esX : lFls ≠ esX := by decide
@[simp] theorem ece_esX_ne_kFu : esX ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_esX : kFu ≠ esX := by decide
@[simp] theorem ece_esX_ne_kD : esX ≠ kD := by decide
@[simp] theorem ece_kD_ne_esX : kD ≠ esX := by decide
@[simp] theorem ece_esL_ne_esA : esL ≠ esA := by decide
@[simp] theorem ece_esL_ne_esH : esL ≠ esH := by decide
@[simp] theorem ece_esL_ne_esC : esL ≠ esC := by decide
@[simp] theorem ece_esL_ne_esU : esL ≠ esU := by decide
@[simp] theorem ece_esL_ne_esP : esL ≠ esP := by decide
@[simp] theorem ece_esL_ne_esQ : esL ≠ esQ := by decide
@[simp] theorem ece_esL_ne_esK : esL ≠ esK := by decide
@[simp] theorem ece_esL_ne_esNp : esL ≠ esNp := by decide
@[simp] theorem ece_esL_ne_esNf : esL ≠ esNf := by decide
@[simp] theorem ece_esL_ne_esX : esL ≠ esX := by decide
@[simp] theorem ece_esL_ne_epA : esL ≠ epA := by decide
@[simp] theorem ece_esL_ne_epH : esL ≠ epH := by decide
@[simp] theorem ece_esL_ne_epC : esL ≠ epC := by decide
@[simp] theorem ece_esL_ne_epU : esL ≠ epU := by decide
@[simp] theorem ece_esL_ne_epP : esL ≠ epP := by decide
@[simp] theorem ece_esL_ne_epQ : esL ≠ epQ := by decide
@[simp] theorem ece_esL_ne_epK : esL ≠ epK := by decide
@[simp] theorem ece_esL_ne_epNp : esL ≠ epNp := by decide
@[simp] theorem ece_esL_ne_epNf : esL ≠ epNf := by decide
@[simp] theorem ece_esL_ne_epT : esL ≠ epT := by decide
@[simp] theorem ece_esL_ne_epX : esL ≠ epX := by decide
@[simp] theorem ece_esL_ne_epL : esL ≠ epL := by decide
@[simp] theorem ece_esL_ne_epP2 : esL ≠ epP2 := by decide
@[simp] theorem ece_esL_ne_epQ2 : esL ≠ epQ2 := by decide
@[simp] theorem ece_esL_ne_epK2 : esL ≠ epK2 := by decide
@[simp] theorem ece_esL_ne_epEt : esL ≠ epEt := by decide
@[simp] theorem ece_esL_ne_epTb : esL ≠ epTb := by decide
@[simp] theorem ece_esL_ne_epTq : esL ≠ epTq := by decide
@[simp] theorem ece_esL_ne_epTc : esL ≠ epTc := by decide
@[simp] theorem ece_esL_ne_lFl : esL ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_esL : lFl ≠ esL := by decide
@[simp] theorem ece_esL_ne_lDh : esL ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_esL : lDh ≠ esL := by decide
@[simp] theorem ece_esL_ne_lDt : esL ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_esL : lDt ≠ esL := by decide
@[simp] theorem ece_esL_ne_lDg : esL ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_esL : lDg ≠ esL := by decide
@[simp] theorem ece_esL_ne_lDi : esL ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_esL : lDi ≠ esL := by decide
@[simp] theorem ece_esL_ne_lRp : esL ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_esL : lRp ≠ esL := by decide
@[simp] theorem ece_esL_ne_lRn : esL ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_esL : lRn ≠ esL := by decide
@[simp] theorem ece_esL_ne_lFle : esL ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_esL : lFle ≠ esL := by decide
@[simp] theorem ece_esL_ne_lKb : esL ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_esL : lKb ≠ esL := by decide
@[simp] theorem ece_esL_ne_lDir : esL ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_esL : lDir ≠ esL := by decide
@[simp] theorem ece_esL_ne_lFln : esL ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_esL : lFln ≠ esL := by decide
@[simp] theorem ece_esL_ne_lFll : esL ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_esL : lFll ≠ esL := by decide
@[simp] theorem ece_esL_ne_lFls : esL ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_esL : lFls ≠ esL := by decide
@[simp] theorem ece_esL_ne_kFu : esL ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_esL : kFu ≠ esL := by decide
@[simp] theorem ece_esL_ne_kD : esL ≠ kD := by decide
@[simp] theorem ece_kD_ne_esL : kD ≠ esL := by decide
@[simp] theorem ece_epA_ne_esA : epA ≠ esA := by decide
@[simp] theorem ece_epA_ne_esH : epA ≠ esH := by decide
@[simp] theorem ece_epA_ne_esC : epA ≠ esC := by decide
@[simp] theorem ece_epA_ne_esU : epA ≠ esU := by decide
@[simp] theorem ece_epA_ne_esP : epA ≠ esP := by decide
@[simp] theorem ece_epA_ne_esQ : epA ≠ esQ := by decide
@[simp] theorem ece_epA_ne_esK : epA ≠ esK := by decide
@[simp] theorem ece_epA_ne_esNp : epA ≠ esNp := by decide
@[simp] theorem ece_epA_ne_esNf : epA ≠ esNf := by decide
@[simp] theorem ece_epA_ne_esX : epA ≠ esX := by decide
@[simp] theorem ece_epA_ne_esL : epA ≠ esL := by decide
@[simp] theorem ece_epA_ne_epH : epA ≠ epH := by decide
@[simp] theorem ece_epA_ne_epC : epA ≠ epC := by decide
@[simp] theorem ece_epA_ne_epU : epA ≠ epU := by decide
@[simp] theorem ece_epA_ne_epP : epA ≠ epP := by decide
@[simp] theorem ece_epA_ne_epQ : epA ≠ epQ := by decide
@[simp] theorem ece_epA_ne_epK : epA ≠ epK := by decide
@[simp] theorem ece_epA_ne_epNp : epA ≠ epNp := by decide
@[simp] theorem ece_epA_ne_epNf : epA ≠ epNf := by decide
@[simp] theorem ece_epA_ne_epT : epA ≠ epT := by decide
@[simp] theorem ece_epA_ne_epX : epA ≠ epX := by decide
@[simp] theorem ece_epA_ne_epL : epA ≠ epL := by decide
@[simp] theorem ece_epA_ne_epP2 : epA ≠ epP2 := by decide
@[simp] theorem ece_epA_ne_epQ2 : epA ≠ epQ2 := by decide
@[simp] theorem ece_epA_ne_epK2 : epA ≠ epK2 := by decide
@[simp] theorem ece_epA_ne_epEt : epA ≠ epEt := by decide
@[simp] theorem ece_epA_ne_epTb : epA ≠ epTb := by decide
@[simp] theorem ece_epA_ne_epTq : epA ≠ epTq := by decide
@[simp] theorem ece_epA_ne_epTc : epA ≠ epTc := by decide
@[simp] theorem ece_epA_ne_lFl : epA ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_epA : lFl ≠ epA := by decide
@[simp] theorem ece_epA_ne_lDh : epA ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_epA : lDh ≠ epA := by decide
@[simp] theorem ece_epA_ne_lDt : epA ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_epA : lDt ≠ epA := by decide
@[simp] theorem ece_epA_ne_lDg : epA ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_epA : lDg ≠ epA := by decide
@[simp] theorem ece_epA_ne_lDi : epA ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_epA : lDi ≠ epA := by decide
@[simp] theorem ece_epA_ne_lRp : epA ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_epA : lRp ≠ epA := by decide
@[simp] theorem ece_epA_ne_lRn : epA ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_epA : lRn ≠ epA := by decide
@[simp] theorem ece_epA_ne_lFle : epA ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_epA : lFle ≠ epA := by decide
@[simp] theorem ece_epA_ne_lKb : epA ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_epA : lKb ≠ epA := by decide
@[simp] theorem ece_epA_ne_lDir : epA ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_epA : lDir ≠ epA := by decide
@[simp] theorem ece_epA_ne_lFln : epA ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_epA : lFln ≠ epA := by decide
@[simp] theorem ece_epA_ne_lFll : epA ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_epA : lFll ≠ epA := by decide
@[simp] theorem ece_epA_ne_lFls : epA ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_epA : lFls ≠ epA := by decide
@[simp] theorem ece_epA_ne_kFu : epA ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_epA : kFu ≠ epA := by decide
@[simp] theorem ece_epA_ne_kD : epA ≠ kD := by decide
@[simp] theorem ece_kD_ne_epA : kD ≠ epA := by decide
@[simp] theorem ece_epH_ne_esA : epH ≠ esA := by decide
@[simp] theorem ece_epH_ne_esH : epH ≠ esH := by decide
@[simp] theorem ece_epH_ne_esC : epH ≠ esC := by decide
@[simp] theorem ece_epH_ne_esU : epH ≠ esU := by decide
@[simp] theorem ece_epH_ne_esP : epH ≠ esP := by decide
@[simp] theorem ece_epH_ne_esQ : epH ≠ esQ := by decide
@[simp] theorem ece_epH_ne_esK : epH ≠ esK := by decide
@[simp] theorem ece_epH_ne_esNp : epH ≠ esNp := by decide
@[simp] theorem ece_epH_ne_esNf : epH ≠ esNf := by decide
@[simp] theorem ece_epH_ne_esX : epH ≠ esX := by decide
@[simp] theorem ece_epH_ne_esL : epH ≠ esL := by decide
@[simp] theorem ece_epH_ne_epA : epH ≠ epA := by decide
@[simp] theorem ece_epH_ne_epC : epH ≠ epC := by decide
@[simp] theorem ece_epH_ne_epU : epH ≠ epU := by decide
@[simp] theorem ece_epH_ne_epP : epH ≠ epP := by decide
@[simp] theorem ece_epH_ne_epQ : epH ≠ epQ := by decide
@[simp] theorem ece_epH_ne_epK : epH ≠ epK := by decide
@[simp] theorem ece_epH_ne_epNp : epH ≠ epNp := by decide
@[simp] theorem ece_epH_ne_epNf : epH ≠ epNf := by decide
@[simp] theorem ece_epH_ne_epT : epH ≠ epT := by decide
@[simp] theorem ece_epH_ne_epX : epH ≠ epX := by decide
@[simp] theorem ece_epH_ne_epL : epH ≠ epL := by decide
@[simp] theorem ece_epH_ne_epP2 : epH ≠ epP2 := by decide
@[simp] theorem ece_epH_ne_epQ2 : epH ≠ epQ2 := by decide
@[simp] theorem ece_epH_ne_epK2 : epH ≠ epK2 := by decide
@[simp] theorem ece_epH_ne_epEt : epH ≠ epEt := by decide
@[simp] theorem ece_epH_ne_epTb : epH ≠ epTb := by decide
@[simp] theorem ece_epH_ne_epTq : epH ≠ epTq := by decide
@[simp] theorem ece_epH_ne_epTc : epH ≠ epTc := by decide
@[simp] theorem ece_epH_ne_lFl : epH ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_epH : lFl ≠ epH := by decide
@[simp] theorem ece_epH_ne_lDh : epH ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_epH : lDh ≠ epH := by decide
@[simp] theorem ece_epH_ne_lDt : epH ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_epH : lDt ≠ epH := by decide
@[simp] theorem ece_epH_ne_lDg : epH ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_epH : lDg ≠ epH := by decide
@[simp] theorem ece_epH_ne_lDi : epH ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_epH : lDi ≠ epH := by decide
@[simp] theorem ece_epH_ne_lRp : epH ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_epH : lRp ≠ epH := by decide
@[simp] theorem ece_epH_ne_lRn : epH ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_epH : lRn ≠ epH := by decide
@[simp] theorem ece_epH_ne_lFle : epH ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_epH : lFle ≠ epH := by decide
@[simp] theorem ece_epH_ne_lKb : epH ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_epH : lKb ≠ epH := by decide
@[simp] theorem ece_epH_ne_lDir : epH ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_epH : lDir ≠ epH := by decide
@[simp] theorem ece_epH_ne_lFln : epH ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_epH : lFln ≠ epH := by decide
@[simp] theorem ece_epH_ne_lFll : epH ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_epH : lFll ≠ epH := by decide
@[simp] theorem ece_epH_ne_lFls : epH ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_epH : lFls ≠ epH := by decide
@[simp] theorem ece_epH_ne_kFu : epH ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_epH : kFu ≠ epH := by decide
@[simp] theorem ece_epH_ne_kD : epH ≠ kD := by decide
@[simp] theorem ece_kD_ne_epH : kD ≠ epH := by decide
@[simp] theorem ece_epC_ne_esA : epC ≠ esA := by decide
@[simp] theorem ece_epC_ne_esH : epC ≠ esH := by decide
@[simp] theorem ece_epC_ne_esC : epC ≠ esC := by decide
@[simp] theorem ece_epC_ne_esU : epC ≠ esU := by decide
@[simp] theorem ece_epC_ne_esP : epC ≠ esP := by decide
@[simp] theorem ece_epC_ne_esQ : epC ≠ esQ := by decide
@[simp] theorem ece_epC_ne_esK : epC ≠ esK := by decide
@[simp] theorem ece_epC_ne_esNp : epC ≠ esNp := by decide
@[simp] theorem ece_epC_ne_esNf : epC ≠ esNf := by decide
@[simp] theorem ece_epC_ne_esX : epC ≠ esX := by decide
@[simp] theorem ece_epC_ne_esL : epC ≠ esL := by decide
@[simp] theorem ece_epC_ne_epA : epC ≠ epA := by decide
@[simp] theorem ece_epC_ne_epH : epC ≠ epH := by decide
@[simp] theorem ece_epC_ne_epU : epC ≠ epU := by decide
@[simp] theorem ece_epC_ne_epP : epC ≠ epP := by decide
@[simp] theorem ece_epC_ne_epQ : epC ≠ epQ := by decide
@[simp] theorem ece_epC_ne_epK : epC ≠ epK := by decide
@[simp] theorem ece_epC_ne_epNp : epC ≠ epNp := by decide
@[simp] theorem ece_epC_ne_epNf : epC ≠ epNf := by decide
@[simp] theorem ece_epC_ne_epT : epC ≠ epT := by decide
@[simp] theorem ece_epC_ne_epX : epC ≠ epX := by decide
@[simp] theorem ece_epC_ne_epL : epC ≠ epL := by decide
@[simp] theorem ece_epC_ne_epP2 : epC ≠ epP2 := by decide
@[simp] theorem ece_epC_ne_epQ2 : epC ≠ epQ2 := by decide
@[simp] theorem ece_epC_ne_epK2 : epC ≠ epK2 := by decide
@[simp] theorem ece_epC_ne_epEt : epC ≠ epEt := by decide
@[simp] theorem ece_epC_ne_epTb : epC ≠ epTb := by decide
@[simp] theorem ece_epC_ne_epTq : epC ≠ epTq := by decide
@[simp] theorem ece_epC_ne_epTc : epC ≠ epTc := by decide
@[simp] theorem ece_epC_ne_lFl : epC ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_epC : lFl ≠ epC := by decide
@[simp] theorem ece_epC_ne_lDh : epC ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_epC : lDh ≠ epC := by decide
@[simp] theorem ece_epC_ne_lDt : epC ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_epC : lDt ≠ epC := by decide
@[simp] theorem ece_epC_ne_lDg : epC ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_epC : lDg ≠ epC := by decide
@[simp] theorem ece_epC_ne_lDi : epC ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_epC : lDi ≠ epC := by decide
@[simp] theorem ece_epC_ne_lRp : epC ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_epC : lRp ≠ epC := by decide
@[simp] theorem ece_epC_ne_lRn : epC ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_epC : lRn ≠ epC := by decide
@[simp] theorem ece_epC_ne_lFle : epC ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_epC : lFle ≠ epC := by decide
@[simp] theorem ece_epC_ne_lKb : epC ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_epC : lKb ≠ epC := by decide
@[simp] theorem ece_epC_ne_lDir : epC ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_epC : lDir ≠ epC := by decide
@[simp] theorem ece_epC_ne_lFln : epC ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_epC : lFln ≠ epC := by decide
@[simp] theorem ece_epC_ne_lFll : epC ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_epC : lFll ≠ epC := by decide
@[simp] theorem ece_epC_ne_lFls : epC ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_epC : lFls ≠ epC := by decide
@[simp] theorem ece_epC_ne_kFu : epC ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_epC : kFu ≠ epC := by decide
@[simp] theorem ece_epC_ne_kD : epC ≠ kD := by decide
@[simp] theorem ece_kD_ne_epC : kD ≠ epC := by decide
@[simp] theorem ece_epU_ne_esA : epU ≠ esA := by decide
@[simp] theorem ece_epU_ne_esH : epU ≠ esH := by decide
@[simp] theorem ece_epU_ne_esC : epU ≠ esC := by decide
@[simp] theorem ece_epU_ne_esU : epU ≠ esU := by decide
@[simp] theorem ece_epU_ne_esP : epU ≠ esP := by decide
@[simp] theorem ece_epU_ne_esQ : epU ≠ esQ := by decide
@[simp] theorem ece_epU_ne_esK : epU ≠ esK := by decide
@[simp] theorem ece_epU_ne_esNp : epU ≠ esNp := by decide
@[simp] theorem ece_epU_ne_esNf : epU ≠ esNf := by decide
@[simp] theorem ece_epU_ne_esX : epU ≠ esX := by decide
@[simp] theorem ece_epU_ne_esL : epU ≠ esL := by decide
@[simp] theorem ece_epU_ne_epA : epU ≠ epA := by decide
@[simp] theorem ece_epU_ne_epH : epU ≠ epH := by decide
@[simp] theorem ece_epU_ne_epC : epU ≠ epC := by decide
@[simp] theorem ece_epU_ne_epP : epU ≠ epP := by decide
@[simp] theorem ece_epU_ne_epQ : epU ≠ epQ := by decide
@[simp] theorem ece_epU_ne_epK : epU ≠ epK := by decide
@[simp] theorem ece_epU_ne_epNp : epU ≠ epNp := by decide
@[simp] theorem ece_epU_ne_epNf : epU ≠ epNf := by decide
@[simp] theorem ece_epU_ne_epT : epU ≠ epT := by decide
@[simp] theorem ece_epU_ne_epX : epU ≠ epX := by decide
@[simp] theorem ece_epU_ne_epL : epU ≠ epL := by decide
@[simp] theorem ece_epU_ne_epP2 : epU ≠ epP2 := by decide
@[simp] theorem ece_epU_ne_epQ2 : epU ≠ epQ2 := by decide
@[simp] theorem ece_epU_ne_epK2 : epU ≠ epK2 := by decide
@[simp] theorem ece_epU_ne_epEt : epU ≠ epEt := by decide
@[simp] theorem ece_epU_ne_epTb : epU ≠ epTb := by decide
@[simp] theorem ece_epU_ne_epTq : epU ≠ epTq := by decide
@[simp] theorem ece_epU_ne_epTc : epU ≠ epTc := by decide
@[simp] theorem ece_epU_ne_lFl : epU ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_epU : lFl ≠ epU := by decide
@[simp] theorem ece_epU_ne_lDh : epU ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_epU : lDh ≠ epU := by decide
@[simp] theorem ece_epU_ne_lDt : epU ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_epU : lDt ≠ epU := by decide
@[simp] theorem ece_epU_ne_lDg : epU ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_epU : lDg ≠ epU := by decide
@[simp] theorem ece_epU_ne_lDi : epU ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_epU : lDi ≠ epU := by decide
@[simp] theorem ece_epU_ne_lRp : epU ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_epU : lRp ≠ epU := by decide
@[simp] theorem ece_epU_ne_lRn : epU ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_epU : lRn ≠ epU := by decide
@[simp] theorem ece_epU_ne_lFle : epU ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_epU : lFle ≠ epU := by decide
@[simp] theorem ece_epU_ne_lKb : epU ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_epU : lKb ≠ epU := by decide
@[simp] theorem ece_epU_ne_lDir : epU ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_epU : lDir ≠ epU := by decide
@[simp] theorem ece_epU_ne_lFln : epU ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_epU : lFln ≠ epU := by decide
@[simp] theorem ece_epU_ne_lFll : epU ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_epU : lFll ≠ epU := by decide
@[simp] theorem ece_epU_ne_lFls : epU ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_epU : lFls ≠ epU := by decide
@[simp] theorem ece_epU_ne_kFu : epU ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_epU : kFu ≠ epU := by decide
@[simp] theorem ece_epU_ne_kD : epU ≠ kD := by decide
@[simp] theorem ece_kD_ne_epU : kD ≠ epU := by decide
@[simp] theorem ece_epP_ne_esA : epP ≠ esA := by decide
@[simp] theorem ece_epP_ne_esH : epP ≠ esH := by decide
@[simp] theorem ece_epP_ne_esC : epP ≠ esC := by decide
@[simp] theorem ece_epP_ne_esU : epP ≠ esU := by decide
@[simp] theorem ece_epP_ne_esP : epP ≠ esP := by decide
@[simp] theorem ece_epP_ne_esQ : epP ≠ esQ := by decide
@[simp] theorem ece_epP_ne_esK : epP ≠ esK := by decide
@[simp] theorem ece_epP_ne_esNp : epP ≠ esNp := by decide
@[simp] theorem ece_epP_ne_esNf : epP ≠ esNf := by decide
@[simp] theorem ece_epP_ne_esX : epP ≠ esX := by decide
@[simp] theorem ece_epP_ne_esL : epP ≠ esL := by decide
@[simp] theorem ece_epP_ne_epA : epP ≠ epA := by decide
@[simp] theorem ece_epP_ne_epH : epP ≠ epH := by decide
@[simp] theorem ece_epP_ne_epC : epP ≠ epC := by decide
@[simp] theorem ece_epP_ne_epU : epP ≠ epU := by decide
@[simp] theorem ece_epP_ne_epQ : epP ≠ epQ := by decide
@[simp] theorem ece_epP_ne_epK : epP ≠ epK := by decide
@[simp] theorem ece_epP_ne_epNp : epP ≠ epNp := by decide
@[simp] theorem ece_epP_ne_epNf : epP ≠ epNf := by decide
@[simp] theorem ece_epP_ne_epT : epP ≠ epT := by decide
@[simp] theorem ece_epP_ne_epX : epP ≠ epX := by decide
@[simp] theorem ece_epP_ne_epL : epP ≠ epL := by decide
@[simp] theorem ece_epP_ne_epP2 : epP ≠ epP2 := by decide
@[simp] theorem ece_epP_ne_epQ2 : epP ≠ epQ2 := by decide
@[simp] theorem ece_epP_ne_epK2 : epP ≠ epK2 := by decide
@[simp] theorem ece_epP_ne_epEt : epP ≠ epEt := by decide
@[simp] theorem ece_epP_ne_epTb : epP ≠ epTb := by decide
@[simp] theorem ece_epP_ne_epTq : epP ≠ epTq := by decide
@[simp] theorem ece_epP_ne_epTc : epP ≠ epTc := by decide
@[simp] theorem ece_epP_ne_lFl : epP ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_epP : lFl ≠ epP := by decide
@[simp] theorem ece_epP_ne_lDh : epP ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_epP : lDh ≠ epP := by decide
@[simp] theorem ece_epP_ne_lDt : epP ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_epP : lDt ≠ epP := by decide
@[simp] theorem ece_epP_ne_lDg : epP ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_epP : lDg ≠ epP := by decide
@[simp] theorem ece_epP_ne_lDi : epP ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_epP : lDi ≠ epP := by decide
@[simp] theorem ece_epP_ne_lRp : epP ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_epP : lRp ≠ epP := by decide
@[simp] theorem ece_epP_ne_lRn : epP ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_epP : lRn ≠ epP := by decide
@[simp] theorem ece_epP_ne_lFle : epP ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_epP : lFle ≠ epP := by decide
@[simp] theorem ece_epP_ne_lKb : epP ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_epP : lKb ≠ epP := by decide
@[simp] theorem ece_epP_ne_lDir : epP ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_epP : lDir ≠ epP := by decide
@[simp] theorem ece_epP_ne_lFln : epP ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_epP : lFln ≠ epP := by decide
@[simp] theorem ece_epP_ne_lFll : epP ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_epP : lFll ≠ epP := by decide
@[simp] theorem ece_epP_ne_lFls : epP ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_epP : lFls ≠ epP := by decide
@[simp] theorem ece_epP_ne_kFu : epP ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_epP : kFu ≠ epP := by decide
@[simp] theorem ece_epP_ne_kD : epP ≠ kD := by decide
@[simp] theorem ece_kD_ne_epP : kD ≠ epP := by decide
@[simp] theorem ece_epQ_ne_esA : epQ ≠ esA := by decide
@[simp] theorem ece_epQ_ne_esH : epQ ≠ esH := by decide
@[simp] theorem ece_epQ_ne_esC : epQ ≠ esC := by decide
@[simp] theorem ece_epQ_ne_esU : epQ ≠ esU := by decide
@[simp] theorem ece_epQ_ne_esP : epQ ≠ esP := by decide
@[simp] theorem ece_epQ_ne_esQ : epQ ≠ esQ := by decide
@[simp] theorem ece_epQ_ne_esK : epQ ≠ esK := by decide
@[simp] theorem ece_epQ_ne_esNp : epQ ≠ esNp := by decide
@[simp] theorem ece_epQ_ne_esNf : epQ ≠ esNf := by decide
@[simp] theorem ece_epQ_ne_esX : epQ ≠ esX := by decide
@[simp] theorem ece_epQ_ne_esL : epQ ≠ esL := by decide
@[simp] theorem ece_epQ_ne_epA : epQ ≠ epA := by decide
@[simp] theorem ece_epQ_ne_epH : epQ ≠ epH := by decide
@[simp] theorem ece_epQ_ne_epC : epQ ≠ epC := by decide
@[simp] theorem ece_epQ_ne_epU : epQ ≠ epU := by decide
@[simp] theorem ece_epQ_ne_epP : epQ ≠ epP := by decide
@[simp] theorem ece_epQ_ne_epK : epQ ≠ epK := by decide
@[simp] theorem ece_epQ_ne_epNp : epQ ≠ epNp := by decide
@[simp] theorem ece_epQ_ne_epNf : epQ ≠ epNf := by decide
@[simp] theorem ece_epQ_ne_epT : epQ ≠ epT := by decide
@[simp] theorem ece_epQ_ne_epX : epQ ≠ epX := by decide
@[simp] theorem ece_epQ_ne_epL : epQ ≠ epL := by decide
@[simp] theorem ece_epQ_ne_epP2 : epQ ≠ epP2 := by decide
@[simp] theorem ece_epQ_ne_epQ2 : epQ ≠ epQ2 := by decide
@[simp] theorem ece_epQ_ne_epK2 : epQ ≠ epK2 := by decide
@[simp] theorem ece_epQ_ne_epEt : epQ ≠ epEt := by decide
@[simp] theorem ece_epQ_ne_epTb : epQ ≠ epTb := by decide
@[simp] theorem ece_epQ_ne_epTq : epQ ≠ epTq := by decide
@[simp] theorem ece_epQ_ne_epTc : epQ ≠ epTc := by decide
@[simp] theorem ece_epQ_ne_lFl : epQ ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_epQ : lFl ≠ epQ := by decide
@[simp] theorem ece_epQ_ne_lDh : epQ ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_epQ : lDh ≠ epQ := by decide
@[simp] theorem ece_epQ_ne_lDt : epQ ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_epQ : lDt ≠ epQ := by decide
@[simp] theorem ece_epQ_ne_lDg : epQ ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_epQ : lDg ≠ epQ := by decide
@[simp] theorem ece_epQ_ne_lDi : epQ ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_epQ : lDi ≠ epQ := by decide
@[simp] theorem ece_epQ_ne_lRp : epQ ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_epQ : lRp ≠ epQ := by decide
@[simp] theorem ece_epQ_ne_lRn : epQ ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_epQ : lRn ≠ epQ := by decide
@[simp] theorem ece_epQ_ne_lFle : epQ ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_epQ : lFle ≠ epQ := by decide
@[simp] theorem ece_epQ_ne_lKb : epQ ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_epQ : lKb ≠ epQ := by decide
@[simp] theorem ece_epQ_ne_lDir : epQ ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_epQ : lDir ≠ epQ := by decide
@[simp] theorem ece_epQ_ne_lFln : epQ ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_epQ : lFln ≠ epQ := by decide
@[simp] theorem ece_epQ_ne_lFll : epQ ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_epQ : lFll ≠ epQ := by decide
@[simp] theorem ece_epQ_ne_lFls : epQ ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_epQ : lFls ≠ epQ := by decide
@[simp] theorem ece_epQ_ne_kFu : epQ ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_epQ : kFu ≠ epQ := by decide
@[simp] theorem ece_epQ_ne_kD : epQ ≠ kD := by decide
@[simp] theorem ece_kD_ne_epQ : kD ≠ epQ := by decide
@[simp] theorem ece_epK_ne_esA : epK ≠ esA := by decide
@[simp] theorem ece_epK_ne_esH : epK ≠ esH := by decide
@[simp] theorem ece_epK_ne_esC : epK ≠ esC := by decide
@[simp] theorem ece_epK_ne_esU : epK ≠ esU := by decide
@[simp] theorem ece_epK_ne_esP : epK ≠ esP := by decide
@[simp] theorem ece_epK_ne_esQ : epK ≠ esQ := by decide
@[simp] theorem ece_epK_ne_esK : epK ≠ esK := by decide
@[simp] theorem ece_epK_ne_esNp : epK ≠ esNp := by decide
@[simp] theorem ece_epK_ne_esNf : epK ≠ esNf := by decide
@[simp] theorem ece_epK_ne_esX : epK ≠ esX := by decide
@[simp] theorem ece_epK_ne_esL : epK ≠ esL := by decide
@[simp] theorem ece_epK_ne_epA : epK ≠ epA := by decide
@[simp] theorem ece_epK_ne_epH : epK ≠ epH := by decide
@[simp] theorem ece_epK_ne_epC : epK ≠ epC := by decide
@[simp] theorem ece_epK_ne_epU : epK ≠ epU := by decide
@[simp] theorem ece_epK_ne_epP : epK ≠ epP := by decide
@[simp] theorem ece_epK_ne_epQ : epK ≠ epQ := by decide
@[simp] theorem ece_epK_ne_epNp : epK ≠ epNp := by decide
@[simp] theorem ece_epK_ne_epNf : epK ≠ epNf := by decide
@[simp] theorem ece_epK_ne_epT : epK ≠ epT := by decide
@[simp] theorem ece_epK_ne_epX : epK ≠ epX := by decide
@[simp] theorem ece_epK_ne_epL : epK ≠ epL := by decide
@[simp] theorem ece_epK_ne_epP2 : epK ≠ epP2 := by decide
@[simp] theorem ece_epK_ne_epQ2 : epK ≠ epQ2 := by decide
@[simp] theorem ece_epK_ne_epK2 : epK ≠ epK2 := by decide
@[simp] theorem ece_epK_ne_epEt : epK ≠ epEt := by decide
@[simp] theorem ece_epK_ne_epTb : epK ≠ epTb := by decide
@[simp] theorem ece_epK_ne_epTq : epK ≠ epTq := by decide
@[simp] theorem ece_epK_ne_epTc : epK ≠ epTc := by decide
@[simp] theorem ece_epK_ne_lFl : epK ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_epK : lFl ≠ epK := by decide
@[simp] theorem ece_epK_ne_lDh : epK ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_epK : lDh ≠ epK := by decide
@[simp] theorem ece_epK_ne_lDt : epK ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_epK : lDt ≠ epK := by decide
@[simp] theorem ece_epK_ne_lDg : epK ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_epK : lDg ≠ epK := by decide
@[simp] theorem ece_epK_ne_lDi : epK ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_epK : lDi ≠ epK := by decide
@[simp] theorem ece_epK_ne_lRp : epK ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_epK : lRp ≠ epK := by decide
@[simp] theorem ece_epK_ne_lRn : epK ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_epK : lRn ≠ epK := by decide
@[simp] theorem ece_epK_ne_lFle : epK ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_epK : lFle ≠ epK := by decide
@[simp] theorem ece_epK_ne_lKb : epK ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_epK : lKb ≠ epK := by decide
@[simp] theorem ece_epK_ne_lDir : epK ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_epK : lDir ≠ epK := by decide
@[simp] theorem ece_epK_ne_lFln : epK ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_epK : lFln ≠ epK := by decide
@[simp] theorem ece_epK_ne_lFll : epK ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_epK : lFll ≠ epK := by decide
@[simp] theorem ece_epK_ne_lFls : epK ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_epK : lFls ≠ epK := by decide
@[simp] theorem ece_epK_ne_kFu : epK ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_epK : kFu ≠ epK := by decide
@[simp] theorem ece_epK_ne_kD : epK ≠ kD := by decide
@[simp] theorem ece_kD_ne_epK : kD ≠ epK := by decide
@[simp] theorem ece_epNp_ne_esA : epNp ≠ esA := by decide
@[simp] theorem ece_epNp_ne_esH : epNp ≠ esH := by decide
@[simp] theorem ece_epNp_ne_esC : epNp ≠ esC := by decide
@[simp] theorem ece_epNp_ne_esU : epNp ≠ esU := by decide
@[simp] theorem ece_epNp_ne_esP : epNp ≠ esP := by decide
@[simp] theorem ece_epNp_ne_esQ : epNp ≠ esQ := by decide
@[simp] theorem ece_epNp_ne_esK : epNp ≠ esK := by decide
@[simp] theorem ece_epNp_ne_esNp : epNp ≠ esNp := by decide
@[simp] theorem ece_epNp_ne_esNf : epNp ≠ esNf := by decide
@[simp] theorem ece_epNp_ne_esX : epNp ≠ esX := by decide
@[simp] theorem ece_epNp_ne_esL : epNp ≠ esL := by decide
@[simp] theorem ece_epNp_ne_epA : epNp ≠ epA := by decide
@[simp] theorem ece_epNp_ne_epH : epNp ≠ epH := by decide
@[simp] theorem ece_epNp_ne_epC : epNp ≠ epC := by decide
@[simp] theorem ece_epNp_ne_epU : epNp ≠ epU := by decide
@[simp] theorem ece_epNp_ne_epP : epNp ≠ epP := by decide
@[simp] theorem ece_epNp_ne_epQ : epNp ≠ epQ := by decide
@[simp] theorem ece_epNp_ne_epK : epNp ≠ epK := by decide
@[simp] theorem ece_epNp_ne_epNf : epNp ≠ epNf := by decide
@[simp] theorem ece_epNp_ne_epT : epNp ≠ epT := by decide
@[simp] theorem ece_epNp_ne_epX : epNp ≠ epX := by decide
@[simp] theorem ece_epNp_ne_epL : epNp ≠ epL := by decide
@[simp] theorem ece_epNp_ne_epP2 : epNp ≠ epP2 := by decide
@[simp] theorem ece_epNp_ne_epQ2 : epNp ≠ epQ2 := by decide
@[simp] theorem ece_epNp_ne_epK2 : epNp ≠ epK2 := by decide
@[simp] theorem ece_epNp_ne_epEt : epNp ≠ epEt := by decide
@[simp] theorem ece_epNp_ne_epTb : epNp ≠ epTb := by decide
@[simp] theorem ece_epNp_ne_epTq : epNp ≠ epTq := by decide
@[simp] theorem ece_epNp_ne_epTc : epNp ≠ epTc := by decide
@[simp] theorem ece_epNp_ne_lFl : epNp ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_epNp : lFl ≠ epNp := by decide
@[simp] theorem ece_epNp_ne_lDh : epNp ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_epNp : lDh ≠ epNp := by decide
@[simp] theorem ece_epNp_ne_lDt : epNp ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_epNp : lDt ≠ epNp := by decide
@[simp] theorem ece_epNp_ne_lDg : epNp ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_epNp : lDg ≠ epNp := by decide
@[simp] theorem ece_epNp_ne_lDi : epNp ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_epNp : lDi ≠ epNp := by decide
@[simp] theorem ece_epNp_ne_lRp : epNp ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_epNp : lRp ≠ epNp := by decide
@[simp] theorem ece_epNp_ne_lRn : epNp ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_epNp : lRn ≠ epNp := by decide
@[simp] theorem ece_epNp_ne_lFle : epNp ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_epNp : lFle ≠ epNp := by decide
@[simp] theorem ece_epNp_ne_lKb : epNp ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_epNp : lKb ≠ epNp := by decide
@[simp] theorem ece_epNp_ne_lDir : epNp ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_epNp : lDir ≠ epNp := by decide
@[simp] theorem ece_epNp_ne_lFln : epNp ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_epNp : lFln ≠ epNp := by decide
@[simp] theorem ece_epNp_ne_lFll : epNp ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_epNp : lFll ≠ epNp := by decide
@[simp] theorem ece_epNp_ne_lFls : epNp ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_epNp : lFls ≠ epNp := by decide
@[simp] theorem ece_epNp_ne_kFu : epNp ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_epNp : kFu ≠ epNp := by decide
@[simp] theorem ece_epNp_ne_kD : epNp ≠ kD := by decide
@[simp] theorem ece_kD_ne_epNp : kD ≠ epNp := by decide
@[simp] theorem ece_epNf_ne_esA : epNf ≠ esA := by decide
@[simp] theorem ece_epNf_ne_esH : epNf ≠ esH := by decide
@[simp] theorem ece_epNf_ne_esC : epNf ≠ esC := by decide
@[simp] theorem ece_epNf_ne_esU : epNf ≠ esU := by decide
@[simp] theorem ece_epNf_ne_esP : epNf ≠ esP := by decide
@[simp] theorem ece_epNf_ne_esQ : epNf ≠ esQ := by decide
@[simp] theorem ece_epNf_ne_esK : epNf ≠ esK := by decide
@[simp] theorem ece_epNf_ne_esNp : epNf ≠ esNp := by decide
@[simp] theorem ece_epNf_ne_esNf : epNf ≠ esNf := by decide
@[simp] theorem ece_epNf_ne_esX : epNf ≠ esX := by decide
@[simp] theorem ece_epNf_ne_esL : epNf ≠ esL := by decide
@[simp] theorem ece_epNf_ne_epA : epNf ≠ epA := by decide
@[simp] theorem ece_epNf_ne_epH : epNf ≠ epH := by decide
@[simp] theorem ece_epNf_ne_epC : epNf ≠ epC := by decide
@[simp] theorem ece_epNf_ne_epU : epNf ≠ epU := by decide
@[simp] theorem ece_epNf_ne_epP : epNf ≠ epP := by decide
@[simp] theorem ece_epNf_ne_epQ : epNf ≠ epQ := by decide
@[simp] theorem ece_epNf_ne_epK : epNf ≠ epK := by decide
@[simp] theorem ece_epNf_ne_epNp : epNf ≠ epNp := by decide
@[simp] theorem ece_epNf_ne_epT : epNf ≠ epT := by decide
@[simp] theorem ece_epNf_ne_epX : epNf ≠ epX := by decide
@[simp] theorem ece_epNf_ne_epL : epNf ≠ epL := by decide
@[simp] theorem ece_epNf_ne_epP2 : epNf ≠ epP2 := by decide
@[simp] theorem ece_epNf_ne_epQ2 : epNf ≠ epQ2 := by decide
@[simp] theorem ece_epNf_ne_epK2 : epNf ≠ epK2 := by decide
@[simp] theorem ece_epNf_ne_epEt : epNf ≠ epEt := by decide
@[simp] theorem ece_epNf_ne_epTb : epNf ≠ epTb := by decide
@[simp] theorem ece_epNf_ne_epTq : epNf ≠ epTq := by decide
@[simp] theorem ece_epNf_ne_epTc : epNf ≠ epTc := by decide
@[simp] theorem ece_epNf_ne_lFl : epNf ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_epNf : lFl ≠ epNf := by decide
@[simp] theorem ece_epNf_ne_lDh : epNf ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_epNf : lDh ≠ epNf := by decide
@[simp] theorem ece_epNf_ne_lDt : epNf ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_epNf : lDt ≠ epNf := by decide
@[simp] theorem ece_epNf_ne_lDg : epNf ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_epNf : lDg ≠ epNf := by decide
@[simp] theorem ece_epNf_ne_lDi : epNf ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_epNf : lDi ≠ epNf := by decide
@[simp] theorem ece_epNf_ne_lRp : epNf ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_epNf : lRp ≠ epNf := by decide
@[simp] theorem ece_epNf_ne_lRn : epNf ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_epNf : lRn ≠ epNf := by decide
@[simp] theorem ece_epNf_ne_lFle : epNf ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_epNf : lFle ≠ epNf := by decide
@[simp] theorem ece_epNf_ne_lKb : epNf ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_epNf : lKb ≠ epNf := by decide
@[simp] theorem ece_epNf_ne_lDir : epNf ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_epNf : lDir ≠ epNf := by decide
@[simp] theorem ece_epNf_ne_lFln : epNf ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_epNf : lFln ≠ epNf := by decide
@[simp] theorem ece_epNf_ne_lFll : epNf ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_epNf : lFll ≠ epNf := by decide
@[simp] theorem ece_epNf_ne_lFls : epNf ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_epNf : lFls ≠ epNf := by decide
@[simp] theorem ece_epNf_ne_kFu : epNf ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_epNf : kFu ≠ epNf := by decide
@[simp] theorem ece_epNf_ne_kD : epNf ≠ kD := by decide
@[simp] theorem ece_kD_ne_epNf : kD ≠ epNf := by decide
@[simp] theorem ece_epT_ne_esA : epT ≠ esA := by decide
@[simp] theorem ece_epT_ne_esH : epT ≠ esH := by decide
@[simp] theorem ece_epT_ne_esC : epT ≠ esC := by decide
@[simp] theorem ece_epT_ne_esU : epT ≠ esU := by decide
@[simp] theorem ece_epT_ne_esP : epT ≠ esP := by decide
@[simp] theorem ece_epT_ne_esQ : epT ≠ esQ := by decide
@[simp] theorem ece_epT_ne_esK : epT ≠ esK := by decide
@[simp] theorem ece_epT_ne_esNp : epT ≠ esNp := by decide
@[simp] theorem ece_epT_ne_esNf : epT ≠ esNf := by decide
@[simp] theorem ece_epT_ne_esX : epT ≠ esX := by decide
@[simp] theorem ece_epT_ne_esL : epT ≠ esL := by decide
@[simp] theorem ece_epT_ne_epA : epT ≠ epA := by decide
@[simp] theorem ece_epT_ne_epH : epT ≠ epH := by decide
@[simp] theorem ece_epT_ne_epC : epT ≠ epC := by decide
@[simp] theorem ece_epT_ne_epU : epT ≠ epU := by decide
@[simp] theorem ece_epT_ne_epP : epT ≠ epP := by decide
@[simp] theorem ece_epT_ne_epQ : epT ≠ epQ := by decide
@[simp] theorem ece_epT_ne_epK : epT ≠ epK := by decide
@[simp] theorem ece_epT_ne_epNp : epT ≠ epNp := by decide
@[simp] theorem ece_epT_ne_epNf : epT ≠ epNf := by decide
@[simp] theorem ece_epT_ne_epX : epT ≠ epX := by decide
@[simp] theorem ece_epT_ne_epL : epT ≠ epL := by decide
@[simp] theorem ece_epT_ne_epP2 : epT ≠ epP2 := by decide
@[simp] theorem ece_epT_ne_epQ2 : epT ≠ epQ2 := by decide
@[simp] theorem ece_epT_ne_epK2 : epT ≠ epK2 := by decide
@[simp] theorem ece_epT_ne_epEt : epT ≠ epEt := by decide
@[simp] theorem ece_epT_ne_epTb : epT ≠ epTb := by decide
@[simp] theorem ece_epT_ne_epTq : epT ≠ epTq := by decide
@[simp] theorem ece_epT_ne_epTc : epT ≠ epTc := by decide
@[simp] theorem ece_epT_ne_lFl : epT ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_epT : lFl ≠ epT := by decide
@[simp] theorem ece_epT_ne_lDh : epT ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_epT : lDh ≠ epT := by decide
@[simp] theorem ece_epT_ne_lDt : epT ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_epT : lDt ≠ epT := by decide
@[simp] theorem ece_epT_ne_lDg : epT ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_epT : lDg ≠ epT := by decide
@[simp] theorem ece_epT_ne_lDi : epT ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_epT : lDi ≠ epT := by decide
@[simp] theorem ece_epT_ne_lRp : epT ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_epT : lRp ≠ epT := by decide
@[simp] theorem ece_epT_ne_lRn : epT ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_epT : lRn ≠ epT := by decide
@[simp] theorem ece_epT_ne_lFle : epT ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_epT : lFle ≠ epT := by decide
@[simp] theorem ece_epT_ne_lKb : epT ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_epT : lKb ≠ epT := by decide
@[simp] theorem ece_epT_ne_lDir : epT ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_epT : lDir ≠ epT := by decide
@[simp] theorem ece_epT_ne_lFln : epT ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_epT : lFln ≠ epT := by decide
@[simp] theorem ece_epT_ne_lFll : epT ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_epT : lFll ≠ epT := by decide
@[simp] theorem ece_epT_ne_lFls : epT ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_epT : lFls ≠ epT := by decide
@[simp] theorem ece_epT_ne_kFu : epT ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_epT : kFu ≠ epT := by decide
@[simp] theorem ece_epT_ne_kD : epT ≠ kD := by decide
@[simp] theorem ece_kD_ne_epT : kD ≠ epT := by decide
@[simp] theorem ece_epX_ne_esA : epX ≠ esA := by decide
@[simp] theorem ece_epX_ne_esH : epX ≠ esH := by decide
@[simp] theorem ece_epX_ne_esC : epX ≠ esC := by decide
@[simp] theorem ece_epX_ne_esU : epX ≠ esU := by decide
@[simp] theorem ece_epX_ne_esP : epX ≠ esP := by decide
@[simp] theorem ece_epX_ne_esQ : epX ≠ esQ := by decide
@[simp] theorem ece_epX_ne_esK : epX ≠ esK := by decide
@[simp] theorem ece_epX_ne_esNp : epX ≠ esNp := by decide
@[simp] theorem ece_epX_ne_esNf : epX ≠ esNf := by decide
@[simp] theorem ece_epX_ne_esX : epX ≠ esX := by decide
@[simp] theorem ece_epX_ne_esL : epX ≠ esL := by decide
@[simp] theorem ece_epX_ne_epA : epX ≠ epA := by decide
@[simp] theorem ece_epX_ne_epH : epX ≠ epH := by decide
@[simp] theorem ece_epX_ne_epC : epX ≠ epC := by decide
@[simp] theorem ece_epX_ne_epU : epX ≠ epU := by decide
@[simp] theorem ece_epX_ne_epP : epX ≠ epP := by decide
@[simp] theorem ece_epX_ne_epQ : epX ≠ epQ := by decide
@[simp] theorem ece_epX_ne_epK : epX ≠ epK := by decide
@[simp] theorem ece_epX_ne_epNp : epX ≠ epNp := by decide
@[simp] theorem ece_epX_ne_epNf : epX ≠ epNf := by decide
@[simp] theorem ece_epX_ne_epT : epX ≠ epT := by decide
@[simp] theorem ece_epX_ne_epL : epX ≠ epL := by decide
@[simp] theorem ece_epX_ne_epP2 : epX ≠ epP2 := by decide
@[simp] theorem ece_epX_ne_epQ2 : epX ≠ epQ2 := by decide
@[simp] theorem ece_epX_ne_epK2 : epX ≠ epK2 := by decide
@[simp] theorem ece_epX_ne_epEt : epX ≠ epEt := by decide
@[simp] theorem ece_epX_ne_epTb : epX ≠ epTb := by decide
@[simp] theorem ece_epX_ne_epTq : epX ≠ epTq := by decide
@[simp] theorem ece_epX_ne_epTc : epX ≠ epTc := by decide
@[simp] theorem ece_epX_ne_lFl : epX ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_epX : lFl ≠ epX := by decide
@[simp] theorem ece_epX_ne_lDh : epX ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_epX : lDh ≠ epX := by decide
@[simp] theorem ece_epX_ne_lDt : epX ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_epX : lDt ≠ epX := by decide
@[simp] theorem ece_epX_ne_lDg : epX ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_epX : lDg ≠ epX := by decide
@[simp] theorem ece_epX_ne_lDi : epX ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_epX : lDi ≠ epX := by decide
@[simp] theorem ece_epX_ne_lRp : epX ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_epX : lRp ≠ epX := by decide
@[simp] theorem ece_epX_ne_lRn : epX ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_epX : lRn ≠ epX := by decide
@[simp] theorem ece_epX_ne_lFle : epX ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_epX : lFle ≠ epX := by decide
@[simp] theorem ece_epX_ne_lKb : epX ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_epX : lKb ≠ epX := by decide
@[simp] theorem ece_epX_ne_lDir : epX ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_epX : lDir ≠ epX := by decide
@[simp] theorem ece_epX_ne_lFln : epX ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_epX : lFln ≠ epX := by decide
@[simp] theorem ece_epX_ne_lFll : epX ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_epX : lFll ≠ epX := by decide
@[simp] theorem ece_epX_ne_lFls : epX ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_epX : lFls ≠ epX := by decide
@[simp] theorem ece_epX_ne_kFu : epX ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_epX : kFu ≠ epX := by decide
@[simp] theorem ece_epX_ne_kD : epX ≠ kD := by decide
@[simp] theorem ece_kD_ne_epX : kD ≠ epX := by decide
@[simp] theorem ece_epL_ne_esA : epL ≠ esA := by decide
@[simp] theorem ece_epL_ne_esH : epL ≠ esH := by decide
@[simp] theorem ece_epL_ne_esC : epL ≠ esC := by decide
@[simp] theorem ece_epL_ne_esU : epL ≠ esU := by decide
@[simp] theorem ece_epL_ne_esP : epL ≠ esP := by decide
@[simp] theorem ece_epL_ne_esQ : epL ≠ esQ := by decide
@[simp] theorem ece_epL_ne_esK : epL ≠ esK := by decide
@[simp] theorem ece_epL_ne_esNp : epL ≠ esNp := by decide
@[simp] theorem ece_epL_ne_esNf : epL ≠ esNf := by decide
@[simp] theorem ece_epL_ne_esX : epL ≠ esX := by decide
@[simp] theorem ece_epL_ne_esL : epL ≠ esL := by decide
@[simp] theorem ece_epL_ne_epA : epL ≠ epA := by decide
@[simp] theorem ece_epL_ne_epH : epL ≠ epH := by decide
@[simp] theorem ece_epL_ne_epC : epL ≠ epC := by decide
@[simp] theorem ece_epL_ne_epU : epL ≠ epU := by decide
@[simp] theorem ece_epL_ne_epP : epL ≠ epP := by decide
@[simp] theorem ece_epL_ne_epQ : epL ≠ epQ := by decide
@[simp] theorem ece_epL_ne_epK : epL ≠ epK := by decide
@[simp] theorem ece_epL_ne_epNp : epL ≠ epNp := by decide
@[simp] theorem ece_epL_ne_epNf : epL ≠ epNf := by decide
@[simp] theorem ece_epL_ne_epT : epL ≠ epT := by decide
@[simp] theorem ece_epL_ne_epX : epL ≠ epX := by decide
@[simp] theorem ece_epL_ne_epP2 : epL ≠ epP2 := by decide
@[simp] theorem ece_epL_ne_epQ2 : epL ≠ epQ2 := by decide
@[simp] theorem ece_epL_ne_epK2 : epL ≠ epK2 := by decide
@[simp] theorem ece_epL_ne_epEt : epL ≠ epEt := by decide
@[simp] theorem ece_epL_ne_epTb : epL ≠ epTb := by decide
@[simp] theorem ece_epL_ne_epTq : epL ≠ epTq := by decide
@[simp] theorem ece_epL_ne_epTc : epL ≠ epTc := by decide
@[simp] theorem ece_epL_ne_lFl : epL ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_epL : lFl ≠ epL := by decide
@[simp] theorem ece_epL_ne_lDh : epL ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_epL : lDh ≠ epL := by decide
@[simp] theorem ece_epL_ne_lDt : epL ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_epL : lDt ≠ epL := by decide
@[simp] theorem ece_epL_ne_lDg : epL ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_epL : lDg ≠ epL := by decide
@[simp] theorem ece_epL_ne_lDi : epL ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_epL : lDi ≠ epL := by decide
@[simp] theorem ece_epL_ne_lRp : epL ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_epL : lRp ≠ epL := by decide
@[simp] theorem ece_epL_ne_lRn : epL ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_epL : lRn ≠ epL := by decide
@[simp] theorem ece_epL_ne_lFle : epL ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_epL : lFle ≠ epL := by decide
@[simp] theorem ece_epL_ne_lKb : epL ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_epL : lKb ≠ epL := by decide
@[simp] theorem ece_epL_ne_lDir : epL ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_epL : lDir ≠ epL := by decide
@[simp] theorem ece_epL_ne_lFln : epL ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_epL : lFln ≠ epL := by decide
@[simp] theorem ece_epL_ne_lFll : epL ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_epL : lFll ≠ epL := by decide
@[simp] theorem ece_epL_ne_lFls : epL ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_epL : lFls ≠ epL := by decide
@[simp] theorem ece_epL_ne_kFu : epL ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_epL : kFu ≠ epL := by decide
@[simp] theorem ece_epL_ne_kD : epL ≠ kD := by decide
@[simp] theorem ece_kD_ne_epL : kD ≠ epL := by decide
@[simp] theorem ece_epP2_ne_esA : epP2 ≠ esA := by decide
@[simp] theorem ece_epP2_ne_esH : epP2 ≠ esH := by decide
@[simp] theorem ece_epP2_ne_esC : epP2 ≠ esC := by decide
@[simp] theorem ece_epP2_ne_esU : epP2 ≠ esU := by decide
@[simp] theorem ece_epP2_ne_esP : epP2 ≠ esP := by decide
@[simp] theorem ece_epP2_ne_esQ : epP2 ≠ esQ := by decide
@[simp] theorem ece_epP2_ne_esK : epP2 ≠ esK := by decide
@[simp] theorem ece_epP2_ne_esNp : epP2 ≠ esNp := by decide
@[simp] theorem ece_epP2_ne_esNf : epP2 ≠ esNf := by decide
@[simp] theorem ece_epP2_ne_esX : epP2 ≠ esX := by decide
@[simp] theorem ece_epP2_ne_esL : epP2 ≠ esL := by decide
@[simp] theorem ece_epP2_ne_epA : epP2 ≠ epA := by decide
@[simp] theorem ece_epP2_ne_epH : epP2 ≠ epH := by decide
@[simp] theorem ece_epP2_ne_epC : epP2 ≠ epC := by decide
@[simp] theorem ece_epP2_ne_epU : epP2 ≠ epU := by decide
@[simp] theorem ece_epP2_ne_epP : epP2 ≠ epP := by decide
@[simp] theorem ece_epP2_ne_epQ : epP2 ≠ epQ := by decide
@[simp] theorem ece_epP2_ne_epK : epP2 ≠ epK := by decide
@[simp] theorem ece_epP2_ne_epNp : epP2 ≠ epNp := by decide
@[simp] theorem ece_epP2_ne_epNf : epP2 ≠ epNf := by decide
@[simp] theorem ece_epP2_ne_epT : epP2 ≠ epT := by decide
@[simp] theorem ece_epP2_ne_epX : epP2 ≠ epX := by decide
@[simp] theorem ece_epP2_ne_epL : epP2 ≠ epL := by decide
@[simp] theorem ece_epP2_ne_epQ2 : epP2 ≠ epQ2 := by decide
@[simp] theorem ece_epP2_ne_epK2 : epP2 ≠ epK2 := by decide
@[simp] theorem ece_epP2_ne_epEt : epP2 ≠ epEt := by decide
@[simp] theorem ece_epP2_ne_epTb : epP2 ≠ epTb := by decide
@[simp] theorem ece_epP2_ne_epTq : epP2 ≠ epTq := by decide
@[simp] theorem ece_epP2_ne_epTc : epP2 ≠ epTc := by decide
@[simp] theorem ece_epP2_ne_lFl : epP2 ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_epP2 : lFl ≠ epP2 := by decide
@[simp] theorem ece_epP2_ne_lDh : epP2 ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_epP2 : lDh ≠ epP2 := by decide
@[simp] theorem ece_epP2_ne_lDt : epP2 ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_epP2 : lDt ≠ epP2 := by decide
@[simp] theorem ece_epP2_ne_lDg : epP2 ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_epP2 : lDg ≠ epP2 := by decide
@[simp] theorem ece_epP2_ne_lDi : epP2 ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_epP2 : lDi ≠ epP2 := by decide
@[simp] theorem ece_epP2_ne_lRp : epP2 ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_epP2 : lRp ≠ epP2 := by decide
@[simp] theorem ece_epP2_ne_lRn : epP2 ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_epP2 : lRn ≠ epP2 := by decide
@[simp] theorem ece_epP2_ne_lFle : epP2 ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_epP2 : lFle ≠ epP2 := by decide
@[simp] theorem ece_epP2_ne_lKb : epP2 ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_epP2 : lKb ≠ epP2 := by decide
@[simp] theorem ece_epP2_ne_lDir : epP2 ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_epP2 : lDir ≠ epP2 := by decide
@[simp] theorem ece_epP2_ne_lFln : epP2 ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_epP2 : lFln ≠ epP2 := by decide
@[simp] theorem ece_epP2_ne_lFll : epP2 ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_epP2 : lFll ≠ epP2 := by decide
@[simp] theorem ece_epP2_ne_lFls : epP2 ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_epP2 : lFls ≠ epP2 := by decide
@[simp] theorem ece_epP2_ne_kFu : epP2 ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_epP2 : kFu ≠ epP2 := by decide
@[simp] theorem ece_epP2_ne_kD : epP2 ≠ kD := by decide
@[simp] theorem ece_kD_ne_epP2 : kD ≠ epP2 := by decide
@[simp] theorem ece_epQ2_ne_esA : epQ2 ≠ esA := by decide
@[simp] theorem ece_epQ2_ne_esH : epQ2 ≠ esH := by decide
@[simp] theorem ece_epQ2_ne_esC : epQ2 ≠ esC := by decide
@[simp] theorem ece_epQ2_ne_esU : epQ2 ≠ esU := by decide
@[simp] theorem ece_epQ2_ne_esP : epQ2 ≠ esP := by decide
@[simp] theorem ece_epQ2_ne_esQ : epQ2 ≠ esQ := by decide
@[simp] theorem ece_epQ2_ne_esK : epQ2 ≠ esK := by decide
@[simp] theorem ece_epQ2_ne_esNp : epQ2 ≠ esNp := by decide
@[simp] theorem ece_epQ2_ne_esNf : epQ2 ≠ esNf := by decide
@[simp] theorem ece_epQ2_ne_esX : epQ2 ≠ esX := by decide
@[simp] theorem ece_epQ2_ne_esL : epQ2 ≠ esL := by decide
@[simp] theorem ece_epQ2_ne_epA : epQ2 ≠ epA := by decide
@[simp] theorem ece_epQ2_ne_epH : epQ2 ≠ epH := by decide
@[simp] theorem ece_epQ2_ne_epC : epQ2 ≠ epC := by decide
@[simp] theorem ece_epQ2_ne_epU : epQ2 ≠ epU := by decide
@[simp] theorem ece_epQ2_ne_epP : epQ2 ≠ epP := by decide
@[simp] theorem ece_epQ2_ne_epQ : epQ2 ≠ epQ := by decide
@[simp] theorem ece_epQ2_ne_epK : epQ2 ≠ epK := by decide
@[simp] theorem ece_epQ2_ne_epNp : epQ2 ≠ epNp := by decide
@[simp] theorem ece_epQ2_ne_epNf : epQ2 ≠ epNf := by decide
@[simp] theorem ece_epQ2_ne_epT : epQ2 ≠ epT := by decide
@[simp] theorem ece_epQ2_ne_epX : epQ2 ≠ epX := by decide
@[simp] theorem ece_epQ2_ne_epL : epQ2 ≠ epL := by decide
@[simp] theorem ece_epQ2_ne_epP2 : epQ2 ≠ epP2 := by decide
@[simp] theorem ece_epQ2_ne_epK2 : epQ2 ≠ epK2 := by decide
@[simp] theorem ece_epQ2_ne_epEt : epQ2 ≠ epEt := by decide
@[simp] theorem ece_epQ2_ne_epTb : epQ2 ≠ epTb := by decide
@[simp] theorem ece_epQ2_ne_epTq : epQ2 ≠ epTq := by decide
@[simp] theorem ece_epQ2_ne_epTc : epQ2 ≠ epTc := by decide
@[simp] theorem ece_epQ2_ne_lFl : epQ2 ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_epQ2 : lFl ≠ epQ2 := by decide
@[simp] theorem ece_epQ2_ne_lDh : epQ2 ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_epQ2 : lDh ≠ epQ2 := by decide
@[simp] theorem ece_epQ2_ne_lDt : epQ2 ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_epQ2 : lDt ≠ epQ2 := by decide
@[simp] theorem ece_epQ2_ne_lDg : epQ2 ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_epQ2 : lDg ≠ epQ2 := by decide
@[simp] theorem ece_epQ2_ne_lDi : epQ2 ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_epQ2 : lDi ≠ epQ2 := by decide
@[simp] theorem ece_epQ2_ne_lRp : epQ2 ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_epQ2 : lRp ≠ epQ2 := by decide
@[simp] theorem ece_epQ2_ne_lRn : epQ2 ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_epQ2 : lRn ≠ epQ2 := by decide
@[simp] theorem ece_epQ2_ne_lFle : epQ2 ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_epQ2 : lFle ≠ epQ2 := by decide
@[simp] theorem ece_epQ2_ne_lKb : epQ2 ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_epQ2 : lKb ≠ epQ2 := by decide
@[simp] theorem ece_epQ2_ne_lDir : epQ2 ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_epQ2 : lDir ≠ epQ2 := by decide
@[simp] theorem ece_epQ2_ne_lFln : epQ2 ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_epQ2 : lFln ≠ epQ2 := by decide
@[simp] theorem ece_epQ2_ne_lFll : epQ2 ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_epQ2 : lFll ≠ epQ2 := by decide
@[simp] theorem ece_epQ2_ne_lFls : epQ2 ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_epQ2 : lFls ≠ epQ2 := by decide
@[simp] theorem ece_epQ2_ne_kFu : epQ2 ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_epQ2 : kFu ≠ epQ2 := by decide
@[simp] theorem ece_epQ2_ne_kD : epQ2 ≠ kD := by decide
@[simp] theorem ece_kD_ne_epQ2 : kD ≠ epQ2 := by decide
@[simp] theorem ece_epK2_ne_esA : epK2 ≠ esA := by decide
@[simp] theorem ece_epK2_ne_esH : epK2 ≠ esH := by decide
@[simp] theorem ece_epK2_ne_esC : epK2 ≠ esC := by decide
@[simp] theorem ece_epK2_ne_esU : epK2 ≠ esU := by decide
@[simp] theorem ece_epK2_ne_esP : epK2 ≠ esP := by decide
@[simp] theorem ece_epK2_ne_esQ : epK2 ≠ esQ := by decide
@[simp] theorem ece_epK2_ne_esK : epK2 ≠ esK := by decide
@[simp] theorem ece_epK2_ne_esNp : epK2 ≠ esNp := by decide
@[simp] theorem ece_epK2_ne_esNf : epK2 ≠ esNf := by decide
@[simp] theorem ece_epK2_ne_esX : epK2 ≠ esX := by decide
@[simp] theorem ece_epK2_ne_esL : epK2 ≠ esL := by decide
@[simp] theorem ece_epK2_ne_epA : epK2 ≠ epA := by decide
@[simp] theorem ece_epK2_ne_epH : epK2 ≠ epH := by decide
@[simp] theorem ece_epK2_ne_epC : epK2 ≠ epC := by decide
@[simp] theorem ece_epK2_ne_epU : epK2 ≠ epU := by decide
@[simp] theorem ece_epK2_ne_epP : epK2 ≠ epP := by decide
@[simp] theorem ece_epK2_ne_epQ : epK2 ≠ epQ := by decide
@[simp] theorem ece_epK2_ne_epK : epK2 ≠ epK := by decide
@[simp] theorem ece_epK2_ne_epNp : epK2 ≠ epNp := by decide
@[simp] theorem ece_epK2_ne_epNf : epK2 ≠ epNf := by decide
@[simp] theorem ece_epK2_ne_epT : epK2 ≠ epT := by decide
@[simp] theorem ece_epK2_ne_epX : epK2 ≠ epX := by decide
@[simp] theorem ece_epK2_ne_epL : epK2 ≠ epL := by decide
@[simp] theorem ece_epK2_ne_epP2 : epK2 ≠ epP2 := by decide
@[simp] theorem ece_epK2_ne_epQ2 : epK2 ≠ epQ2 := by decide
@[simp] theorem ece_epK2_ne_epEt : epK2 ≠ epEt := by decide
@[simp] theorem ece_epK2_ne_epTb : epK2 ≠ epTb := by decide
@[simp] theorem ece_epK2_ne_epTq : epK2 ≠ epTq := by decide
@[simp] theorem ece_epK2_ne_epTc : epK2 ≠ epTc := by decide
@[simp] theorem ece_epK2_ne_lFl : epK2 ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_epK2 : lFl ≠ epK2 := by decide
@[simp] theorem ece_epK2_ne_lDh : epK2 ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_epK2 : lDh ≠ epK2 := by decide
@[simp] theorem ece_epK2_ne_lDt : epK2 ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_epK2 : lDt ≠ epK2 := by decide
@[simp] theorem ece_epK2_ne_lDg : epK2 ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_epK2 : lDg ≠ epK2 := by decide
@[simp] theorem ece_epK2_ne_lDi : epK2 ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_epK2 : lDi ≠ epK2 := by decide
@[simp] theorem ece_epK2_ne_lRp : epK2 ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_epK2 : lRp ≠ epK2 := by decide
@[simp] theorem ece_epK2_ne_lRn : epK2 ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_epK2 : lRn ≠ epK2 := by decide
@[simp] theorem ece_epK2_ne_lFle : epK2 ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_epK2 : lFle ≠ epK2 := by decide
@[simp] theorem ece_epK2_ne_lKb : epK2 ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_epK2 : lKb ≠ epK2 := by decide
@[simp] theorem ece_epK2_ne_lDir : epK2 ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_epK2 : lDir ≠ epK2 := by decide
@[simp] theorem ece_epK2_ne_lFln : epK2 ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_epK2 : lFln ≠ epK2 := by decide
@[simp] theorem ece_epK2_ne_lFll : epK2 ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_epK2 : lFll ≠ epK2 := by decide
@[simp] theorem ece_epK2_ne_lFls : epK2 ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_epK2 : lFls ≠ epK2 := by decide
@[simp] theorem ece_epK2_ne_kFu : epK2 ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_epK2 : kFu ≠ epK2 := by decide
@[simp] theorem ece_epK2_ne_kD : epK2 ≠ kD := by decide
@[simp] theorem ece_kD_ne_epK2 : kD ≠ epK2 := by decide
@[simp] theorem ece_epEt_ne_esA : epEt ≠ esA := by decide
@[simp] theorem ece_epEt_ne_esH : epEt ≠ esH := by decide
@[simp] theorem ece_epEt_ne_esC : epEt ≠ esC := by decide
@[simp] theorem ece_epEt_ne_esU : epEt ≠ esU := by decide
@[simp] theorem ece_epEt_ne_esP : epEt ≠ esP := by decide
@[simp] theorem ece_epEt_ne_esQ : epEt ≠ esQ := by decide
@[simp] theorem ece_epEt_ne_esK : epEt ≠ esK := by decide
@[simp] theorem ece_epEt_ne_esNp : epEt ≠ esNp := by decide
@[simp] theorem ece_epEt_ne_esNf : epEt ≠ esNf := by decide
@[simp] theorem ece_epEt_ne_esX : epEt ≠ esX := by decide
@[simp] theorem ece_epEt_ne_esL : epEt ≠ esL := by decide
@[simp] theorem ece_epEt_ne_epA : epEt ≠ epA := by decide
@[simp] theorem ece_epEt_ne_epH : epEt ≠ epH := by decide
@[simp] theorem ece_epEt_ne_epC : epEt ≠ epC := by decide
@[simp] theorem ece_epEt_ne_epU : epEt ≠ epU := by decide
@[simp] theorem ece_epEt_ne_epP : epEt ≠ epP := by decide
@[simp] theorem ece_epEt_ne_epQ : epEt ≠ epQ := by decide
@[simp] theorem ece_epEt_ne_epK : epEt ≠ epK := by decide
@[simp] theorem ece_epEt_ne_epNp : epEt ≠ epNp := by decide
@[simp] theorem ece_epEt_ne_epNf : epEt ≠ epNf := by decide
@[simp] theorem ece_epEt_ne_epT : epEt ≠ epT := by decide
@[simp] theorem ece_epEt_ne_epX : epEt ≠ epX := by decide
@[simp] theorem ece_epEt_ne_epL : epEt ≠ epL := by decide
@[simp] theorem ece_epEt_ne_epP2 : epEt ≠ epP2 := by decide
@[simp] theorem ece_epEt_ne_epQ2 : epEt ≠ epQ2 := by decide
@[simp] theorem ece_epEt_ne_epK2 : epEt ≠ epK2 := by decide
@[simp] theorem ece_epEt_ne_epTb : epEt ≠ epTb := by decide
@[simp] theorem ece_epEt_ne_epTq : epEt ≠ epTq := by decide
@[simp] theorem ece_epEt_ne_epTc : epEt ≠ epTc := by decide
@[simp] theorem ece_epEt_ne_lFl : epEt ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_epEt : lFl ≠ epEt := by decide
@[simp] theorem ece_epEt_ne_lDh : epEt ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_epEt : lDh ≠ epEt := by decide
@[simp] theorem ece_epEt_ne_lDt : epEt ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_epEt : lDt ≠ epEt := by decide
@[simp] theorem ece_epEt_ne_lDg : epEt ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_epEt : lDg ≠ epEt := by decide
@[simp] theorem ece_epEt_ne_lDi : epEt ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_epEt : lDi ≠ epEt := by decide
@[simp] theorem ece_epEt_ne_lRp : epEt ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_epEt : lRp ≠ epEt := by decide
@[simp] theorem ece_epEt_ne_lRn : epEt ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_epEt : lRn ≠ epEt := by decide
@[simp] theorem ece_epEt_ne_lFle : epEt ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_epEt : lFle ≠ epEt := by decide
@[simp] theorem ece_epEt_ne_lKb : epEt ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_epEt : lKb ≠ epEt := by decide
@[simp] theorem ece_epEt_ne_lDir : epEt ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_epEt : lDir ≠ epEt := by decide
@[simp] theorem ece_epEt_ne_lFln : epEt ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_epEt : lFln ≠ epEt := by decide
@[simp] theorem ece_epEt_ne_lFll : epEt ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_epEt : lFll ≠ epEt := by decide
@[simp] theorem ece_epEt_ne_lFls : epEt ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_epEt : lFls ≠ epEt := by decide
@[simp] theorem ece_epEt_ne_kFu : epEt ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_epEt : kFu ≠ epEt := by decide
@[simp] theorem ece_epEt_ne_kD : epEt ≠ kD := by decide
@[simp] theorem ece_kD_ne_epEt : kD ≠ epEt := by decide
@[simp] theorem ece_epTb_ne_esA : epTb ≠ esA := by decide
@[simp] theorem ece_epTb_ne_esH : epTb ≠ esH := by decide
@[simp] theorem ece_epTb_ne_esC : epTb ≠ esC := by decide
@[simp] theorem ece_epTb_ne_esU : epTb ≠ esU := by decide
@[simp] theorem ece_epTb_ne_esP : epTb ≠ esP := by decide
@[simp] theorem ece_epTb_ne_esQ : epTb ≠ esQ := by decide
@[simp] theorem ece_epTb_ne_esK : epTb ≠ esK := by decide
@[simp] theorem ece_epTb_ne_esNp : epTb ≠ esNp := by decide
@[simp] theorem ece_epTb_ne_esNf : epTb ≠ esNf := by decide
@[simp] theorem ece_epTb_ne_esX : epTb ≠ esX := by decide
@[simp] theorem ece_epTb_ne_esL : epTb ≠ esL := by decide
@[simp] theorem ece_epTb_ne_epA : epTb ≠ epA := by decide
@[simp] theorem ece_epTb_ne_epH : epTb ≠ epH := by decide
@[simp] theorem ece_epTb_ne_epC : epTb ≠ epC := by decide
@[simp] theorem ece_epTb_ne_epU : epTb ≠ epU := by decide
@[simp] theorem ece_epTb_ne_epP : epTb ≠ epP := by decide
@[simp] theorem ece_epTb_ne_epQ : epTb ≠ epQ := by decide
@[simp] theorem ece_epTb_ne_epK : epTb ≠ epK := by decide
@[simp] theorem ece_epTb_ne_epNp : epTb ≠ epNp := by decide
@[simp] theorem ece_epTb_ne_epNf : epTb ≠ epNf := by decide
@[simp] theorem ece_epTb_ne_epT : epTb ≠ epT := by decide
@[simp] theorem ece_epTb_ne_epX : epTb ≠ epX := by decide
@[simp] theorem ece_epTb_ne_epL : epTb ≠ epL := by decide
@[simp] theorem ece_epTb_ne_epP2 : epTb ≠ epP2 := by decide
@[simp] theorem ece_epTb_ne_epQ2 : epTb ≠ epQ2 := by decide
@[simp] theorem ece_epTb_ne_epK2 : epTb ≠ epK2 := by decide
@[simp] theorem ece_epTb_ne_epEt : epTb ≠ epEt := by decide
@[simp] theorem ece_epTb_ne_epTq : epTb ≠ epTq := by decide
@[simp] theorem ece_epTb_ne_epTc : epTb ≠ epTc := by decide
@[simp] theorem ece_epTb_ne_lFl : epTb ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_epTb : lFl ≠ epTb := by decide
@[simp] theorem ece_epTb_ne_lDh : epTb ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_epTb : lDh ≠ epTb := by decide
@[simp] theorem ece_epTb_ne_lDt : epTb ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_epTb : lDt ≠ epTb := by decide
@[simp] theorem ece_epTb_ne_lDg : epTb ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_epTb : lDg ≠ epTb := by decide
@[simp] theorem ece_epTb_ne_lDi : epTb ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_epTb : lDi ≠ epTb := by decide
@[simp] theorem ece_epTb_ne_lRp : epTb ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_epTb : lRp ≠ epTb := by decide
@[simp] theorem ece_epTb_ne_lRn : epTb ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_epTb : lRn ≠ epTb := by decide
@[simp] theorem ece_epTb_ne_lFle : epTb ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_epTb : lFle ≠ epTb := by decide
@[simp] theorem ece_epTb_ne_lKb : epTb ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_epTb : lKb ≠ epTb := by decide
@[simp] theorem ece_epTb_ne_lDir : epTb ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_epTb : lDir ≠ epTb := by decide
@[simp] theorem ece_epTb_ne_lFln : epTb ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_epTb : lFln ≠ epTb := by decide
@[simp] theorem ece_epTb_ne_lFll : epTb ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_epTb : lFll ≠ epTb := by decide
@[simp] theorem ece_epTb_ne_lFls : epTb ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_epTb : lFls ≠ epTb := by decide
@[simp] theorem ece_epTb_ne_kFu : epTb ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_epTb : kFu ≠ epTb := by decide
@[simp] theorem ece_epTb_ne_kD : epTb ≠ kD := by decide
@[simp] theorem ece_kD_ne_epTb : kD ≠ epTb := by decide
@[simp] theorem ece_epTq_ne_esA : epTq ≠ esA := by decide
@[simp] theorem ece_epTq_ne_esH : epTq ≠ esH := by decide
@[simp] theorem ece_epTq_ne_esC : epTq ≠ esC := by decide
@[simp] theorem ece_epTq_ne_esU : epTq ≠ esU := by decide
@[simp] theorem ece_epTq_ne_esP : epTq ≠ esP := by decide
@[simp] theorem ece_epTq_ne_esQ : epTq ≠ esQ := by decide
@[simp] theorem ece_epTq_ne_esK : epTq ≠ esK := by decide
@[simp] theorem ece_epTq_ne_esNp : epTq ≠ esNp := by decide
@[simp] theorem ece_epTq_ne_esNf : epTq ≠ esNf := by decide
@[simp] theorem ece_epTq_ne_esX : epTq ≠ esX := by decide
@[simp] theorem ece_epTq_ne_esL : epTq ≠ esL := by decide
@[simp] theorem ece_epTq_ne_epA : epTq ≠ epA := by decide
@[simp] theorem ece_epTq_ne_epH : epTq ≠ epH := by decide
@[simp] theorem ece_epTq_ne_epC : epTq ≠ epC := by decide
@[simp] theorem ece_epTq_ne_epU : epTq ≠ epU := by decide
@[simp] theorem ece_epTq_ne_epP : epTq ≠ epP := by decide
@[simp] theorem ece_epTq_ne_epQ : epTq ≠ epQ := by decide
@[simp] theorem ece_epTq_ne_epK : epTq ≠ epK := by decide
@[simp] theorem ece_epTq_ne_epNp : epTq ≠ epNp := by decide
@[simp] theorem ece_epTq_ne_epNf : epTq ≠ epNf := by decide
@[simp] theorem ece_epTq_ne_epT : epTq ≠ epT := by decide
@[simp] theorem ece_epTq_ne_epX : epTq ≠ epX := by decide
@[simp] theorem ece_epTq_ne_epL : epTq ≠ epL := by decide
@[simp] theorem ece_epTq_ne_epP2 : epTq ≠ epP2 := by decide
@[simp] theorem ece_epTq_ne_epQ2 : epTq ≠ epQ2 := by decide
@[simp] theorem ece_epTq_ne_epK2 : epTq ≠ epK2 := by decide
@[simp] theorem ece_epTq_ne_epEt : epTq ≠ epEt := by decide
@[simp] theorem ece_epTq_ne_epTb : epTq ≠ epTb := by decide
@[simp] theorem ece_epTq_ne_epTc : epTq ≠ epTc := by decide
@[simp] theorem ece_epTq_ne_lFl : epTq ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_epTq : lFl ≠ epTq := by decide
@[simp] theorem ece_epTq_ne_lDh : epTq ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_epTq : lDh ≠ epTq := by decide
@[simp] theorem ece_epTq_ne_lDt : epTq ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_epTq : lDt ≠ epTq := by decide
@[simp] theorem ece_epTq_ne_lDg : epTq ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_epTq : lDg ≠ epTq := by decide
@[simp] theorem ece_epTq_ne_lDi : epTq ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_epTq : lDi ≠ epTq := by decide
@[simp] theorem ece_epTq_ne_lRp : epTq ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_epTq : lRp ≠ epTq := by decide
@[simp] theorem ece_epTq_ne_lRn : epTq ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_epTq : lRn ≠ epTq := by decide
@[simp] theorem ece_epTq_ne_lFle : epTq ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_epTq : lFle ≠ epTq := by decide
@[simp] theorem ece_epTq_ne_lKb : epTq ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_epTq : lKb ≠ epTq := by decide
@[simp] theorem ece_epTq_ne_lDir : epTq ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_epTq : lDir ≠ epTq := by decide
@[simp] theorem ece_epTq_ne_lFln : epTq ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_epTq : lFln ≠ epTq := by decide
@[simp] theorem ece_epTq_ne_lFll : epTq ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_epTq : lFll ≠ epTq := by decide
@[simp] theorem ece_epTq_ne_lFls : epTq ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_epTq : lFls ≠ epTq := by decide
@[simp] theorem ece_epTq_ne_kFu : epTq ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_epTq : kFu ≠ epTq := by decide
@[simp] theorem ece_epTq_ne_kD : epTq ≠ kD := by decide
@[simp] theorem ece_kD_ne_epTq : kD ≠ epTq := by decide
@[simp] theorem ece_epTc_ne_esA : epTc ≠ esA := by decide
@[simp] theorem ece_epTc_ne_esH : epTc ≠ esH := by decide
@[simp] theorem ece_epTc_ne_esC : epTc ≠ esC := by decide
@[simp] theorem ece_epTc_ne_esU : epTc ≠ esU := by decide
@[simp] theorem ece_epTc_ne_esP : epTc ≠ esP := by decide
@[simp] theorem ece_epTc_ne_esQ : epTc ≠ esQ := by decide
@[simp] theorem ece_epTc_ne_esK : epTc ≠ esK := by decide
@[simp] theorem ece_epTc_ne_esNp : epTc ≠ esNp := by decide
@[simp] theorem ece_epTc_ne_esNf : epTc ≠ esNf := by decide
@[simp] theorem ece_epTc_ne_esX : epTc ≠ esX := by decide
@[simp] theorem ece_epTc_ne_esL : epTc ≠ esL := by decide
@[simp] theorem ece_epTc_ne_epA : epTc ≠ epA := by decide
@[simp] theorem ece_epTc_ne_epH : epTc ≠ epH := by decide
@[simp] theorem ece_epTc_ne_epC : epTc ≠ epC := by decide
@[simp] theorem ece_epTc_ne_epU : epTc ≠ epU := by decide
@[simp] theorem ece_epTc_ne_epP : epTc ≠ epP := by decide
@[simp] theorem ece_epTc_ne_epQ : epTc ≠ epQ := by decide
@[simp] theorem ece_epTc_ne_epK : epTc ≠ epK := by decide
@[simp] theorem ece_epTc_ne_epNp : epTc ≠ epNp := by decide
@[simp] theorem ece_epTc_ne_epNf : epTc ≠ epNf := by decide
@[simp] theorem ece_epTc_ne_epT : epTc ≠ epT := by decide
@[simp] theorem ece_epTc_ne_epX : epTc ≠ epX := by decide
@[simp] theorem ece_epTc_ne_epL : epTc ≠ epL := by decide
@[simp] theorem ece_epTc_ne_epP2 : epTc ≠ epP2 := by decide
@[simp] theorem ece_epTc_ne_epQ2 : epTc ≠ epQ2 := by decide
@[simp] theorem ece_epTc_ne_epK2 : epTc ≠ epK2 := by decide
@[simp] theorem ece_epTc_ne_epEt : epTc ≠ epEt := by decide
@[simp] theorem ece_epTc_ne_epTb : epTc ≠ epTb := by decide
@[simp] theorem ece_epTc_ne_epTq : epTc ≠ epTq := by decide
@[simp] theorem ece_epTc_ne_lFl : epTc ≠ lFl := by decide
@[simp] theorem ece_lFl_ne_epTc : lFl ≠ epTc := by decide
@[simp] theorem ece_epTc_ne_lDh : epTc ≠ lDh := by decide
@[simp] theorem ece_lDh_ne_epTc : lDh ≠ epTc := by decide
@[simp] theorem ece_epTc_ne_lDt : epTc ≠ lDt := by decide
@[simp] theorem ece_lDt_ne_epTc : lDt ≠ epTc := by decide
@[simp] theorem ece_epTc_ne_lDg : epTc ≠ lDg := by decide
@[simp] theorem ece_lDg_ne_epTc : lDg ≠ epTc := by decide
@[simp] theorem ece_epTc_ne_lDi : epTc ≠ lDi := by decide
@[simp] theorem ece_lDi_ne_epTc : lDi ≠ epTc := by decide
@[simp] theorem ece_epTc_ne_lRp : epTc ≠ lRp := by decide
@[simp] theorem ece_lRp_ne_epTc : lRp ≠ epTc := by decide
@[simp] theorem ece_epTc_ne_lRn : epTc ≠ lRn := by decide
@[simp] theorem ece_lRn_ne_epTc : lRn ≠ epTc := by decide
@[simp] theorem ece_epTc_ne_lFle : epTc ≠ lFle := by decide
@[simp] theorem ece_lFle_ne_epTc : lFle ≠ epTc := by decide
@[simp] theorem ece_epTc_ne_lKb : epTc ≠ lKb := by decide
@[simp] theorem ece_lKb_ne_epTc : lKb ≠ epTc := by decide
@[simp] theorem ece_epTc_ne_lDir : epTc ≠ lDir := by decide
@[simp] theorem ece_lDir_ne_epTc : lDir ≠ epTc := by decide
@[simp] theorem ece_epTc_ne_lFln : epTc ≠ lFln := by decide
@[simp] theorem ece_lFln_ne_epTc : lFln ≠ epTc := by decide
@[simp] theorem ece_epTc_ne_lFll : epTc ≠ lFll := by decide
@[simp] theorem ece_lFll_ne_epTc : lFll ≠ epTc := by decide
@[simp] theorem ece_epTc_ne_lFls : epTc ≠ lFls := by decide
@[simp] theorem ece_lFls_ne_epTc : lFls ≠ epTc := by decide
@[simp] theorem ece_epTc_ne_kFu : epTc ≠ kFu := by decide
@[simp] theorem ece_kFu_ne_epTc : kFu ≠ epTc := by decide
@[simp] theorem ece_epTc_ne_kD : epTc ≠ kD := by decide
@[simp] theorem ece_kD_ne_epTc : kD ≠ epTc := by decide

def esParams : List MlS := [esA]
def esLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, esH, esC, esU, esP, esQ, esK, esNp, esNf, esX, esL]
def esBody (C : Ctx) : ProgHOL 64 := prologue esLocals (.seq (.call (some (some (.local, esH), none)) fGetAppFn [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv esA)]) (.ite (tagIsE esH 3) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv esH)) (.seq eViewP (.seq (.assign .local esC (.load .one (vv lRp))) (.seq (.assign .local esU (.load .one (.op .add [(vv lRp), (.const 8)]))) (envFindP C esP (vv esC) (.ite (.cmp .equal (vv esP) (.const 0)) (.return (.const 0)) (.seq (.assign .local esQ (.op .sub [(vv esP), (.const 1)])) (.seq (.assign .local esK (.load .one (vv esQ))) (.ite (.cmp .notEqual (vv esK) (.const 4)) (.return (.const 0)) (.seq (.assign .local esNp (.load .one (.op .add [(vv esQ), (.const 32)]))) (.seq (.assign .local esNf (.load .one (.op .add [(vv esQ), (.const 40)]))) (.seq (.call (some (some (.local, esX), none)) ExG.fGaa [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv esA)]) (.seq (.assign .local esL (.load .one (vv esX))) (.return (.cmp .equal (vv esL) (.op .add [(vv esNp), (vv esNf)]))))))))))))))))) (.return (.const 0))))
def epParams : List MlS := [epA]
def epLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, epH, epC, epU, epP, epQ, epK, epNp, epNf, epT, epX, epL, epP2, epQ2, epK2, epEt, epTb, epTq, epTc]
def epBody (C : Ctx) : ProgHOL 64 := prologue epLocals (.seq (.call (some (some (.local, epH), none)) fGetAppFn [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv epA)]) (.ite (tagIsE epH 3) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv epH)) (.seq eViewP (.seq (.assign .local epC (.load .one (vv lRp))) (.seq (.assign .local epU (.load .one (.op .add [(vv lRp), (.const 8)]))) (envFindP C epP (vv epC) (.ite (.cmp .equal (vv epP) (.const 0)) (.return (.const 0)) (.seq (.assign .local epQ (.op .sub [(vv epP), (.const 1)])) (.seq (.assign .local epK (.load .one (vv epQ))) (.ite (.cmp .notEqual (vv epK) (.const 4)) (.return (.const 0)) (.seq (.assign .local epNp (.load .one (.op .add [(vv epQ), (.const 32)]))) (.seq (.assign .local epNf (.load .one (.op .add [(vv epQ), (.const 40)]))) (.seq (.assign .local epT (.load .one (.op .add [(vv epQ), (.const 48)]))) (.seq (.call (some (some (.local, epX), none)) ExG.fGaa [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv epA)]) (.seq (.assign .local epL (.load .one (vv epX))) (.ite (.cmp .lower (vv epL) (.op .add [(vv epNp), (vv epNf)])) (envFindP C epP2 (vv epT) (.ite (.cmp .equal (vv epP2) (.const 0)) (.return (.const 0)) (.seq (.assign .local epQ2 (.op .sub [(vv epP2), (.const 1)])) (.seq (.assign .local epK2 (.load .one (vv epQ2))) (.ite (.cmp .notEqual (vv epK2) (.const 3)) (.return (.const 0)) (.seq (.assign .local epEt (.load .one (.op .add [(vv epQ2), (.const 32)]))) (tblFindP C epTb (vv epT) (.ite (.cmp .equal (vv epTb) (.const 0)) (.return (.const 0)) (.seq (.assign .local epTq (.op .sub [(vv epTb), (.const 1)])) (.seq (.assign .local epTc (.load .one (.op .add [(vv epTq), (.const 24)]))) (.ite (.cmp .equal (vv epEt) (.const 0)) (.return (.const 0)) (.ite (.cmp .notEqual (vv epTc) (vv epC)) (.return (.const 0)) (.return (.op .add [(.op .sub [(.op .add [(vv epNp), (vv epNf)]), (vv epL)]), (.const 1)])))))))))))))) (.return (.const 0)))))))))))))))))) (.return (.const 0))))

structure EsCodes (C : Ctx) : Prop where
  gaf : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  mg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  mp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  gaa : C.code.lookup ExG.fGaa = some ([(pFu, .one), (pH, .one)], ExG.gaaBody C, .one)

section
variable {σ : Type}

def PostONat (C : Ctx) (o : Option Nat) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ w = optWG (BitVec.ofNat 64) o ∧ (∀ k, o = some k → k + 1 < 2 ^ 64) ∧ SR (ctxH C H') s' st

theorem postONat_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostONat C a w s' st → PostONat C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', h1, h2, h4, h3⟩ => ⟨H', h1, h2, h4, sr_of_eq h3 rfl rfl rfl rfl⟩

theorem es_spec (C : Ctx) (hok : CtxOK C) (hc : EsCodes C) (s : AState) (a : EIdx) :
    SpecR (σ := σ) (Pre C s (esParams.zip [Enc.idxW a])) (esBody C) s (etaCtorShape C.fe a) (PostB C) := by
  refine specR_prologue (postB_locals C) (Knot.params_none C esLocals esParams _ (by decide) (by decide)) ?_
  unfold etaCtorShape
  refine specR_callNIM (C := C) esH fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv esA]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW a] (by decide) rfl (by decide) hc.gaf
    ⟨rfl, by simp +decide [Env.get, esParams, ctxEnv], trivial⟩
    (fun x w' s' st => getAppFn coreWalkFuel a s = .ok (x, s') ∧ Post (C) s x w' s' st)
    (fun x w' s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec (C) hc.gaf coreWalkFuel a s CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun h w' s' st ⟨hrun, hw, hs, _⟩ => ?_)
  subst hw
  have hs' : s = s' := hs.symm
  subst hs'
  refine Knot.specR_tagIteV esH h 3 (by decide) (by decide) (by simp) (fun htc => ?_) (fun htc => ?_)
  swap
  · rw [if_neg (show ¬ (h.tag == ETag.const) = true by simpa [ETag.const] using htc)]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, (List.prefix_refl _), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [if_pos (show (h.tag == ETag.const) = true by simp [htc, ETag.const])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv esH) (Enc.idxW h) (by decide) (by simp) ?_
  refine specR_viewP (C := C) h (by simp) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
    (fun v P hv htn _ => ?_)
  refine specR_congr (Big.view_bind_eq h v _ s hv) ?_
  have h3 : v.tagN = 3 := by rw [htn, htc]; rfl
  obtain ⟨c, us, rfl⟩ := UD.tagN_const h3
  dsimp only
  refine specR_loadI' esC (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW c) (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW c) [Enc.idxW us] []) ?_
  refine specR_loadI' esU _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW us) (by decide) (by simp +decide [sev]) rfl
    (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW c) (Enc.idxW us) [] []) ?_
  refine specR_envFindI (C := C) hok hc.mg hc.mp esP (vv esC) c (by decide) (by simp) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  have hrel := find_rel hok c
  try rw [show (C).envM = C.envM from rfl]
  revert hrel
  rcases hfind : C.fe.find? c with _ | ci
  · intro hrel; simp only at hrel; rw [hrel]
    refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, (List.prefix_refl _), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  intro ⟨o, hm, hci⟩
  rw [hm]
  refine specR_atEntry fun t ht => ?_
  have hoE : o < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI esQ _ (ecell C o) (by decide) (by simp [sev, optWG]; exact BitVec.add_sub_cancel _ _) ?_
  rcases ci with cv | ⟨cv, val, hint⟩ | cv | ⟨cv, caps⟩ | ⟨cv, np, nf, ind⟩ | ⟨cv, mi, rp, isK, rules⟩
  · refine specR_envLoadI esK (vv esQ) o 0 (by decide) (by simp [ecell_ctxH]) hci.2 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, (List.prefix_refl _), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_envLoadI esK (vv esQ) o 1 (by decide) (by simp [ecell_ctxH]) hci.2.1 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, (List.prefix_refl _), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_envLoadI esK (vv esQ) o 2 (by decide) (by simp [ecell_ctxH]) hci.2 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, (List.prefix_refl _), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_envLoadI esK (vv esQ) o 3 (by decide) (by simp [ecell_ctxH]) hci.2.1 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, (List.prefix_refl _), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_envLoadI esK (vv esQ) o 4 (by decide) (by simp) hci.2.1 ?_
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    obtain ⟨_, _, ⟨hnp, hnpl⟩, ⟨hnf, hnfl⟩, hT⟩ := hci
    dsimp only
    refine specR_envLoadI esNp (.op .add [vv esQ, .const 32]) (o + 4) _ (by decide)
      (by simp [sev, vv]; simpa using ecell_add C o 4) hnp ?_
    refine specR_envLoadI esNf (.op .add [vv esQ, .const 40]) (o + 5) _ (by decide)
      (by simp [sev, vv]; simpa using ecell_add C o 5) hnf ?_
    refine specR_callNIH (C := C) esX ExG.fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv esA] (ExG.gaaBody C)
      [BitVec.ofNat 64 coreWalkFuel, Enc.idxW a] (by decide) rfl (by decide) hc.gaa
      ⟨rfl, by simp +decide [Env.get, esParams, ctxEnv], trivial⟩
      (PostA C) (fun xs w _ H1 => ∃ o1, w = cellA C o1 ∧ BlkAt H1 o1 (xs.map Enc.idxW))
      (fun xs w s' st ⟨H1, o1, hp, hw, hb, hsr⟩ => ⟨H1, hp, ⟨o1, hw, hb⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
        (ExG.gaa_spec C hok hc.gaa coreWalkFuel CV.coreWalkFuel_lt C.H a s))
      (fun aargs w s1 H1 hp1 ⟨o1, hw, hba⟩ => ?_)
    subst hw
    refine UD.specR_heapLoadI' (C := ctxH C H1) esL (vv esX) o1 _ (by have h := hba.1; simp only [List.length_map] at h; exact h) (by decide)
      (by simp +decide [sev, Env.get]; rfl) ?_
    refine specR_atEntry fun t ht => ?_
    have hsza := blk_small0 (ctxOK_H hok H1) ht.sr hba
    simp only [List.length_map] at hsza
    have hsum : BitVec.ofNat 64 np + BitVec.ofNat 64 nf = BitVec.ofNat 64 (np + nf) := BitVec.ofNat_add_ofNat ..
    refine specR_returnI _ (boolW (aargs.length == np + nf)) ?_
      (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    by_cases hln : aargs.length = np + nf
    · simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hsum, hln, boolW]
    · have hw : BitVec.ofNat 64 aargs.length ≠ BitVec.ofNat 64 (np + nf) := by
        intro x; apply hln
        have := congrArg BitVec.toNat x
        simp only [BitVec.toNat_ofNat] at this
        rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hsum, hln, hw, boolW]

  · refine specR_envLoadI esK (vv esQ) o 5 (by decide) (by simp [ecell_ctxH]) hci.2.1 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, (List.prefix_refl _), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem ep_spec (C : Ctx) (hok : CtxOK C) (hc : EsCodes C) (s : AState) (a : EIdx) :
    SpecR (σ := σ) (Pre C s (epParams.zip [Enc.idxW a])) (epBody C) s (etaCtorPartial C.fe a) (PostONat C) := by
  refine specR_prologue (postONat_locals C) (Knot.params_none C epLocals epParams _ (by decide) (by decide)) ?_
  unfold etaCtorPartial
  refine specR_callNIM (C := C) epH fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv epA]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW a] (by decide) rfl (by decide) hc.gaf
    ⟨rfl, by simp +decide [Env.get, epParams, ctxEnv], trivial⟩
    (fun x w' s' st => getAppFn coreWalkFuel a s = .ok (x, s') ∧ Post (C) s x w' s' st)
    (fun x w' s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec (C) hc.gaf coreWalkFuel a s CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun h w' s' st ⟨hrun, hw, hs, _⟩ => ?_)
  subst hw
  have hs' : s = s' := hs.symm
  subst hs'
  refine Knot.specR_tagIteV epH h 3 (by decide) (by decide) (by simp) (fun htc => ?_) (fun htc => ?_)
  swap
  · rw [if_neg (show ¬ (h.tag == ETag.const) = true by simpa [ETag.const] using htc)]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, (List.prefix_refl _), rfl, (fun _ h => by cases h), sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [if_pos (show (h.tag == ETag.const) = true by simp [htc, ETag.const])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv epH) (Enc.idxW h) (by decide) (by simp) ?_
  refine specR_viewP (C := C) h (by simp) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
    (fun v P hv htn _ => ?_)
  refine specR_congr (Big.view_bind_eq h v _ s hv) ?_
  have h3 : v.tagN = 3 := by rw [htn, htc]; rfl
  obtain ⟨c, us, rfl⟩ := UD.tagN_const h3
  dsimp only
  refine specR_loadI' epC (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW c) (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW c) [Enc.idxW us] []) ?_
  refine specR_loadI' epU _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW us) (by decide) (by simp +decide [sev]) rfl
    (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW c) (Enc.idxW us) [] []) ?_
  refine specR_envFindI (C := C) hok hc.mg hc.mp epP (vv epC) c (by decide) (by simp) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  have hrel := find_rel hok c
  try rw [show (C).envM = C.envM from rfl]
  revert hrel
  rcases hfind : C.fe.find? c with _ | ci
  · intro hrel; simp only at hrel; rw [hrel]
    refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, (List.prefix_refl _), rfl, (fun _ h => by cases h), sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  intro ⟨o, hm, hci⟩
  rw [hm]
  refine specR_atEntry fun t ht => ?_
  have hoE : o < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI epQ _ (ecell C o) (by decide) (by simp [sev, optWG]; exact BitVec.add_sub_cancel _ _) ?_
  rcases ci with cv | ⟨cv, val, hint⟩ | cv | ⟨cv, caps⟩ | ⟨cv, np, nf, ind⟩ | ⟨cv, mi, rp, isK, rules⟩
  · refine specR_envLoadI epK (vv epQ) o 0 (by decide) (by simp [ecell_ctxH]) hci.2 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, (List.prefix_refl _), rfl, (fun _ h => by cases h), sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_envLoadI epK (vv epQ) o 1 (by decide) (by simp [ecell_ctxH]) hci.2.1 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, (List.prefix_refl _), rfl, (fun _ h => by cases h), sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_envLoadI epK (vv epQ) o 2 (by decide) (by simp [ecell_ctxH]) hci.2 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, (List.prefix_refl _), rfl, (fun _ h => by cases h), sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_envLoadI epK (vv epQ) o 3 (by decide) (by simp [ecell_ctxH]) hci.2.1 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, (List.prefix_refl _), rfl, (fun _ h => by cases h), sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_envLoadI epK (vv epQ) o 4 (by decide) (by simp) hci.2.1 ?_
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    obtain ⟨_, _, ⟨hnp, hnpl⟩, ⟨hnf, hnfl⟩, hT⟩ := hci
    dsimp only
    refine specR_envLoadI epNp (.op .add [vv epQ, .const 32]) (o + 4) _ (by decide)
      (by simp [sev, vv]; simpa using ecell_add C o 4) hnp ?_
    refine specR_envLoadI epNf (.op .add [vv epQ, .const 40]) (o + 5) _ (by decide)
      (by simp [sev, vv]; simpa using ecell_add C o 5) hnf ?_
    refine specR_envLoadI epT (.op .add [vv epQ, .const 48]) (o + 6) _ (by decide)
      (by simp [sev, vv]; simpa using ecell_add C o 6) hT ?_
    refine specR_callNIH (C := C) epX ExG.fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv epA] (ExG.gaaBody C)
      [BitVec.ofNat 64 coreWalkFuel, Enc.idxW a] (by decide) rfl (by decide) hc.gaa
      ⟨rfl, by simp +decide [Env.get, epParams, ctxEnv], trivial⟩
      (PostA C) (fun xs w _ H1 => ∃ o1, w = cellA C o1 ∧ BlkAt H1 o1 (xs.map Enc.idxW))
      (fun xs w s' st ⟨H1, o1, hp, hw, hb, hsr⟩ => ⟨H1, hp, ⟨o1, hw, hb⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
        (ExG.gaa_spec C hok hc.gaa coreWalkFuel CV.coreWalkFuel_lt C.H a s))
      (fun aargs w s1 H1 hp1 ⟨o1, hw, hba⟩ => ?_)
    subst hw
    refine UD.specR_heapLoadI' (C := ctxH C H1) epL (vv epX) o1 _ (by have h := hba.1; simp only [List.length_map] at h; exact h) (by decide)
      (by simp +decide [sev, Env.get]; rfl) ?_
    refine specR_atEntry fun t ht => ?_
    have hsza := blk_small0 (ctxOK_H hok H1) ht.sr hba
    simp only [List.length_map] at hsza
    have hsum : BitVec.ofNat 64 np + BitVec.ofNat 64 nf = BitVec.ofNat 64 (np + nf) := BitVec.ofNat_add_ofNat ..
    have hltw : (BitVec.ofNat 64 aargs.length < BitVec.ofNat 64 (np + nf)) ↔ aargs.length < np + nf := by
      rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
    by_cases hlt : aargs.length < np + nf
    swap
    · refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hsum, hltw, hlt]) (fun h => absurd rfl h) (fun _ => ?_)
      rw [if_neg hlt]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, rfl, (fun _ h => by cases h), sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hsum, hltw, hlt]) (fun _ => ?_) (fun h => absurd h (by decide))
    rw [if_pos hlt]
    unfold etaCtorPartialFam
    refine specR_envFindI (C := ctxH C H1) (ctxOK_H hok H1) hc.mg hc.mp epP2 (vv epT) ind (by decide) (by simp) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    have hrel := find_rel hok ind
    try rw [show (ctxH C H1).envM = C.envM from rfl]
    revert hrel
    rcases hfind2 : C.fe.find? ind with _ | ci2
    · intro hrel; simp only at hrel; rw [hrel]
      refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, rfl, (fun _ h => by cases h), sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    intro ⟨o2, hm2, hci⟩
    rw [hm2]
    refine specR_atEntry fun t ht => ?_
    have hoE2 : o2 < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
    refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE2) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI epQ2 _ (ecell C o2) (by decide) (by simp [sev, optWG]; exact BitVec.add_sub_cancel _ _) ?_
    rcases ci2 with cvT | ⟨cvT, val2, hint2⟩ | cvT | ⟨cvT, caps⟩ | ⟨cvT, np2, nf2, ind2⟩ | ⟨cvT, mi2, rp2, isK2, rules2⟩
    · refine specR_envLoadI epK2 (vv epQ2) o2 0 (by decide) (by simp [ecell_ctxH]) hci.2 ?_
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, rfl, (fun _ h => by cases h), sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_envLoadI epK2 (vv epQ2) o2 1 (by decide) (by simp [ecell_ctxH]) hci.2.1 ?_
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, rfl, (fun _ h => by cases h), sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_envLoadI epK2 (vv epQ2) o2 2 (by decide) (by simp [ecell_ctxH]) hci.2 ?_
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, rfl, (fun _ h => by cases h), sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_envLoadI epK2 (vv epQ2) o2 3 (by decide) (by simp [ecell_ctxH]) hci.2.1 ?_
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      obtain ⟨_, _, het, _⟩ := hci
      dsimp only
      refine specR_envLoadI epEt (.op .add [vv epQ2, .const 32]) (o2 + 4) _ (by decide)
        (by simp [sev, vv, ecell_ctxH]; simpa using ecell_add C o2 4) het ?_
      refine specR_tblFindI (C := ctxH C H1) (ctxOK_H hok H1) hc.mg hc.mp epTb (vv epT) ind (by decide)
        (by simp +decide [Env.get, epParams, ctxEnv]) (by simp +decide [Env.get, epParams, ctxEnv] <;> rfl) ?_
      have hrel := tbl_rel hok ind
      try rw [show (ctxH C H1).tblM = C.tblM from rfl]
      revert hrel
      rcases hft : C.fe.findTable? ind with _ | tb
      · intro hrel; simp only at hrel; rw [hrel]
        refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
        exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, rfl, (fun _ h => by cases h), sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      intro ⟨ot, hmt, htb⟩
      rw [hmt]
      refine specR_atEntry fun t ht => ?_
      have hoT : ot < C.EN := Nat.lt_of_lt_of_le (tblE_lt htb) ht.sr.env.1.len
      refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoT) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_assignI epTq _ (ecell C ot) (by decide) (by simp [sev, optWG]; exact BitVec.add_sub_cancel _ _) ?_
      obtain ⟨_, _, _, hctor, _⟩ := htb
      refine specR_envLoadI epTc (.op .add [vv epTq, .const 24]) (ot + 3) _ (by decide)
        (by simp [sev, vv, ecell_ctxH]; simpa using ecell_add C ot 3) hctor ?_
      dsimp only
      rcases Bool.eq_false_or_eq_true caps.eta with he | he
      swap
      · refine specR_ifI _ 1 (by simp [sev, boolW, he, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
        simp only [he, Bool.false_eq_true, ↓reduceIte]
        exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, rfl, (fun _ h => by cases h), sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      refine specR_ifI _ 0 (by simp [sev, boolW, he, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      simp only [he, ↓reduceIte]
      by_cases hk : tb.ctor = c
      swap
      · have hne : Enc.idxW tb.ctor ≠ Enc.idxW c := fun e => hk (Enc.idxW_inj e)
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get, epParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun _ => ?_)
          (fun h => absurd h (by decide))
        simp only [show (tb.ctor == c) = false by simpa using hk, Bool.false_eq_true, ↓reduceIte]
        exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, rfl, (fun _ h => by cases h), sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, epParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hk]) (fun h => absurd rfl h) (fun _ => ?_)
      simp only [hk, beq_self_eq_true, ↓reduceIte]
      refine specR_returnI _ (optWG (BitVec.ofNat 64) (some (np + nf - aargs.length))) ?_
        (fun t ht => ⟨H1, hp1, rfl, (fun k hk => by cases hk; omega), sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      simp only [sev, Env.get_cons, optWG]
      simp +decide [Env.get, epParams, ctxEnv, hsum]
      rw [ix_wsub _ _ (by omega) (by omega)]

    · refine specR_envLoadI epK2 (vv epQ2) o2 4 (by decide) (by simp [ecell_ctxH]) hci.2.1 ?_
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, rfl, (fun _ h => by cases h), sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_envLoadI epK2 (vv epQ2) o2 5 (by decide) (by simp [ecell_ctxH]) hci.2.1 ?_
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, rfl, (fun _ h => by cases h), sr_of_eq ht.sr rfl rfl rfl rfl⟩)

  · refine specR_envLoadI epK (vv epQ) o 5 (by decide) (by simp [ecell_ctxH]) hci.2.1 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, (List.prefix_refl _), rfl, (fun _ h => by cases h), sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
