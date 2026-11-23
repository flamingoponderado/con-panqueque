import ConPanqueque.T.Core.EagerRed
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# The application arm: `defeqArg` and the `inferSpine` walk

`da`: `defeqArg` — the `defeqE` knot entry on an `eagerReduce _ _` argument, `defeq` otherwise.
`sp`: walk the head's type down the argument vector (a heap block, with its size passed along), keeping the
pending substitutions in an accumulator block; each domain is opened in one `instantiateListFast`.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def daA := ofString "dan_a"
def daT := ofString "dan_t"
def daY := ofString "dan_y"
def daE := ofString "dan_e"
def daQ := ofString "dan_q"
def spT := ofString "spn_t"
def spA := ofString "spn_a"
def spG := ofString "spn_g"
def spI := ofString "spn_i"
def spN := ofString "spn_n"
def spX := ofString "spn_x"
def spDm := ofString "spn_dm"
def spB := ofString "spn_b"
def spL := ofString "spn_l"
def spO := ofString "spn_o"
def spTa := ofString "spn_ta"
def spQ := ofString "spn_q"
def spA2 := ofString "spn_a2"
def spW := ofString "spn_w"
def spE0 := ofString "spn_e0"
def spR := ofString "spn_r"
def fDa := ofString "defeqArg"
def fSp := ofString "inferSpine"

@[simp] theorem sp_daA_ne_daT : daA ≠ daT := by decide
@[simp] theorem sp_daA_ne_daY : daA ≠ daY := by decide
@[simp] theorem sp_daA_ne_daE : daA ≠ daE := by decide
@[simp] theorem sp_daA_ne_daQ : daA ≠ daQ := by decide
@[simp] theorem sp_daA_ne_kFu : daA ≠ kFu := by decide
@[simp] theorem sp_kFu_ne_daA : kFu ≠ daA := by decide
@[simp] theorem sp_daA_ne_kD : daA ≠ kD := by decide
@[simp] theorem sp_kD_ne_daA : kD ≠ daA := by decide
@[simp] theorem sp_daA_ne_lFl : daA ≠ lFl := by decide
@[simp] theorem sp_lFl_ne_daA : lFl ≠ daA := by decide
@[simp] theorem sp_daA_ne_lDh : daA ≠ lDh := by decide
@[simp] theorem sp_lDh_ne_daA : lDh ≠ daA := by decide
@[simp] theorem sp_daA_ne_lDt : daA ≠ lDt := by decide
@[simp] theorem sp_lDt_ne_daA : lDt ≠ daA := by decide
@[simp] theorem sp_daA_ne_lDg : daA ≠ lDg := by decide
@[simp] theorem sp_lDg_ne_daA : lDg ≠ daA := by decide
@[simp] theorem sp_daA_ne_lDi : daA ≠ lDi := by decide
@[simp] theorem sp_lDi_ne_daA : lDi ≠ daA := by decide
@[simp] theorem sp_daA_ne_lRp : daA ≠ lRp := by decide
@[simp] theorem sp_lRp_ne_daA : lRp ≠ daA := by decide
@[simp] theorem sp_daA_ne_lRn : daA ≠ lRn := by decide
@[simp] theorem sp_lRn_ne_daA : lRn ≠ daA := by decide
@[simp] theorem sp_daA_ne_lDir : daA ≠ lDir := by decide
@[simp] theorem sp_lDir_ne_daA : lDir ≠ daA := by decide
@[simp] theorem sp_daA_ne_lFle : daA ≠ lFle := by decide
@[simp] theorem sp_lFle_ne_daA : lFle ≠ daA := by decide
@[simp] theorem sp_daA_ne_lKb : daA ≠ lKb := by decide
@[simp] theorem sp_lKb_ne_daA : lKb ≠ daA := by decide
@[simp] theorem sp_daT_ne_daA : daT ≠ daA := by decide
@[simp] theorem sp_daT_ne_daY : daT ≠ daY := by decide
@[simp] theorem sp_daT_ne_daE : daT ≠ daE := by decide
@[simp] theorem sp_daT_ne_daQ : daT ≠ daQ := by decide
@[simp] theorem sp_daT_ne_kFu : daT ≠ kFu := by decide
@[simp] theorem sp_kFu_ne_daT : kFu ≠ daT := by decide
@[simp] theorem sp_daT_ne_kD : daT ≠ kD := by decide
@[simp] theorem sp_kD_ne_daT : kD ≠ daT := by decide
@[simp] theorem sp_daT_ne_lFl : daT ≠ lFl := by decide
@[simp] theorem sp_lFl_ne_daT : lFl ≠ daT := by decide
@[simp] theorem sp_daT_ne_lDh : daT ≠ lDh := by decide
@[simp] theorem sp_lDh_ne_daT : lDh ≠ daT := by decide
@[simp] theorem sp_daT_ne_lDt : daT ≠ lDt := by decide
@[simp] theorem sp_lDt_ne_daT : lDt ≠ daT := by decide
@[simp] theorem sp_daT_ne_lDg : daT ≠ lDg := by decide
@[simp] theorem sp_lDg_ne_daT : lDg ≠ daT := by decide
@[simp] theorem sp_daT_ne_lDi : daT ≠ lDi := by decide
@[simp] theorem sp_lDi_ne_daT : lDi ≠ daT := by decide
@[simp] theorem sp_daT_ne_lRp : daT ≠ lRp := by decide
@[simp] theorem sp_lRp_ne_daT : lRp ≠ daT := by decide
@[simp] theorem sp_daT_ne_lRn : daT ≠ lRn := by decide
@[simp] theorem sp_lRn_ne_daT : lRn ≠ daT := by decide
@[simp] theorem sp_daT_ne_lDir : daT ≠ lDir := by decide
@[simp] theorem sp_lDir_ne_daT : lDir ≠ daT := by decide
@[simp] theorem sp_daT_ne_lFle : daT ≠ lFle := by decide
@[simp] theorem sp_lFle_ne_daT : lFle ≠ daT := by decide
@[simp] theorem sp_daT_ne_lKb : daT ≠ lKb := by decide
@[simp] theorem sp_lKb_ne_daT : lKb ≠ daT := by decide
@[simp] theorem sp_daY_ne_daA : daY ≠ daA := by decide
@[simp] theorem sp_daY_ne_daT : daY ≠ daT := by decide
@[simp] theorem sp_daY_ne_daE : daY ≠ daE := by decide
@[simp] theorem sp_daY_ne_daQ : daY ≠ daQ := by decide
@[simp] theorem sp_daY_ne_kFu : daY ≠ kFu := by decide
@[simp] theorem sp_kFu_ne_daY : kFu ≠ daY := by decide
@[simp] theorem sp_daY_ne_kD : daY ≠ kD := by decide
@[simp] theorem sp_kD_ne_daY : kD ≠ daY := by decide
@[simp] theorem sp_daY_ne_lFl : daY ≠ lFl := by decide
@[simp] theorem sp_lFl_ne_daY : lFl ≠ daY := by decide
@[simp] theorem sp_daY_ne_lDh : daY ≠ lDh := by decide
@[simp] theorem sp_lDh_ne_daY : lDh ≠ daY := by decide
@[simp] theorem sp_daY_ne_lDt : daY ≠ lDt := by decide
@[simp] theorem sp_lDt_ne_daY : lDt ≠ daY := by decide
@[simp] theorem sp_daY_ne_lDg : daY ≠ lDg := by decide
@[simp] theorem sp_lDg_ne_daY : lDg ≠ daY := by decide
@[simp] theorem sp_daY_ne_lDi : daY ≠ lDi := by decide
@[simp] theorem sp_lDi_ne_daY : lDi ≠ daY := by decide
@[simp] theorem sp_daY_ne_lRp : daY ≠ lRp := by decide
@[simp] theorem sp_lRp_ne_daY : lRp ≠ daY := by decide
@[simp] theorem sp_daY_ne_lRn : daY ≠ lRn := by decide
@[simp] theorem sp_lRn_ne_daY : lRn ≠ daY := by decide
@[simp] theorem sp_daY_ne_lDir : daY ≠ lDir := by decide
@[simp] theorem sp_lDir_ne_daY : lDir ≠ daY := by decide
@[simp] theorem sp_daY_ne_lFle : daY ≠ lFle := by decide
@[simp] theorem sp_lFle_ne_daY : lFle ≠ daY := by decide
@[simp] theorem sp_daY_ne_lKb : daY ≠ lKb := by decide
@[simp] theorem sp_lKb_ne_daY : lKb ≠ daY := by decide
@[simp] theorem sp_daE_ne_daA : daE ≠ daA := by decide
@[simp] theorem sp_daE_ne_daT : daE ≠ daT := by decide
@[simp] theorem sp_daE_ne_daY : daE ≠ daY := by decide
@[simp] theorem sp_daE_ne_daQ : daE ≠ daQ := by decide
@[simp] theorem sp_daE_ne_kFu : daE ≠ kFu := by decide
@[simp] theorem sp_kFu_ne_daE : kFu ≠ daE := by decide
@[simp] theorem sp_daE_ne_kD : daE ≠ kD := by decide
@[simp] theorem sp_kD_ne_daE : kD ≠ daE := by decide
@[simp] theorem sp_daE_ne_lFl : daE ≠ lFl := by decide
@[simp] theorem sp_lFl_ne_daE : lFl ≠ daE := by decide
@[simp] theorem sp_daE_ne_lDh : daE ≠ lDh := by decide
@[simp] theorem sp_lDh_ne_daE : lDh ≠ daE := by decide
@[simp] theorem sp_daE_ne_lDt : daE ≠ lDt := by decide
@[simp] theorem sp_lDt_ne_daE : lDt ≠ daE := by decide
@[simp] theorem sp_daE_ne_lDg : daE ≠ lDg := by decide
@[simp] theorem sp_lDg_ne_daE : lDg ≠ daE := by decide
@[simp] theorem sp_daE_ne_lDi : daE ≠ lDi := by decide
@[simp] theorem sp_lDi_ne_daE : lDi ≠ daE := by decide
@[simp] theorem sp_daE_ne_lRp : daE ≠ lRp := by decide
@[simp] theorem sp_lRp_ne_daE : lRp ≠ daE := by decide
@[simp] theorem sp_daE_ne_lRn : daE ≠ lRn := by decide
@[simp] theorem sp_lRn_ne_daE : lRn ≠ daE := by decide
@[simp] theorem sp_daE_ne_lDir : daE ≠ lDir := by decide
@[simp] theorem sp_lDir_ne_daE : lDir ≠ daE := by decide
@[simp] theorem sp_daE_ne_lFle : daE ≠ lFle := by decide
@[simp] theorem sp_lFle_ne_daE : lFle ≠ daE := by decide
@[simp] theorem sp_daE_ne_lKb : daE ≠ lKb := by decide
@[simp] theorem sp_lKb_ne_daE : lKb ≠ daE := by decide
@[simp] theorem sp_daQ_ne_daA : daQ ≠ daA := by decide
@[simp] theorem sp_daQ_ne_daT : daQ ≠ daT := by decide
@[simp] theorem sp_daQ_ne_daY : daQ ≠ daY := by decide
@[simp] theorem sp_daQ_ne_daE : daQ ≠ daE := by decide
@[simp] theorem sp_daQ_ne_kFu : daQ ≠ kFu := by decide
@[simp] theorem sp_kFu_ne_daQ : kFu ≠ daQ := by decide
@[simp] theorem sp_daQ_ne_kD : daQ ≠ kD := by decide
@[simp] theorem sp_kD_ne_daQ : kD ≠ daQ := by decide
@[simp] theorem sp_daQ_ne_lFl : daQ ≠ lFl := by decide
@[simp] theorem sp_lFl_ne_daQ : lFl ≠ daQ := by decide
@[simp] theorem sp_daQ_ne_lDh : daQ ≠ lDh := by decide
@[simp] theorem sp_lDh_ne_daQ : lDh ≠ daQ := by decide
@[simp] theorem sp_daQ_ne_lDt : daQ ≠ lDt := by decide
@[simp] theorem sp_lDt_ne_daQ : lDt ≠ daQ := by decide
@[simp] theorem sp_daQ_ne_lDg : daQ ≠ lDg := by decide
@[simp] theorem sp_lDg_ne_daQ : lDg ≠ daQ := by decide
@[simp] theorem sp_daQ_ne_lDi : daQ ≠ lDi := by decide
@[simp] theorem sp_lDi_ne_daQ : lDi ≠ daQ := by decide
@[simp] theorem sp_daQ_ne_lRp : daQ ≠ lRp := by decide
@[simp] theorem sp_lRp_ne_daQ : lRp ≠ daQ := by decide
@[simp] theorem sp_daQ_ne_lRn : daQ ≠ lRn := by decide
@[simp] theorem sp_lRn_ne_daQ : lRn ≠ daQ := by decide
@[simp] theorem sp_daQ_ne_lDir : daQ ≠ lDir := by decide
@[simp] theorem sp_lDir_ne_daQ : lDir ≠ daQ := by decide
@[simp] theorem sp_daQ_ne_lFle : daQ ≠ lFle := by decide
@[simp] theorem sp_lFle_ne_daQ : lFle ≠ daQ := by decide
@[simp] theorem sp_daQ_ne_lKb : daQ ≠ lKb := by decide
@[simp] theorem sp_lKb_ne_daQ : lKb ≠ daQ := by decide
@[simp] theorem sp_spT_ne_spA : spT ≠ spA := by decide
@[simp] theorem sp_spT_ne_spG : spT ≠ spG := by decide
@[simp] theorem sp_spT_ne_spI : spT ≠ spI := by decide
@[simp] theorem sp_spT_ne_spN : spT ≠ spN := by decide
@[simp] theorem sp_spT_ne_spX : spT ≠ spX := by decide
@[simp] theorem sp_spT_ne_spDm : spT ≠ spDm := by decide
@[simp] theorem sp_spT_ne_spB : spT ≠ spB := by decide
@[simp] theorem sp_spT_ne_spL : spT ≠ spL := by decide
@[simp] theorem sp_spT_ne_spO : spT ≠ spO := by decide
@[simp] theorem sp_spT_ne_spTa : spT ≠ spTa := by decide
@[simp] theorem sp_spT_ne_spQ : spT ≠ spQ := by decide
@[simp] theorem sp_spT_ne_spA2 : spT ≠ spA2 := by decide
@[simp] theorem sp_spT_ne_spW : spT ≠ spW := by decide
@[simp] theorem sp_spT_ne_spE0 : spT ≠ spE0 := by decide
@[simp] theorem sp_spT_ne_spR : spT ≠ spR := by decide
@[simp] theorem sp_spT_ne_kFu : spT ≠ kFu := by decide
@[simp] theorem sp_kFu_ne_spT : kFu ≠ spT := by decide
@[simp] theorem sp_spT_ne_kD : spT ≠ kD := by decide
@[simp] theorem sp_kD_ne_spT : kD ≠ spT := by decide
@[simp] theorem sp_spT_ne_lFl : spT ≠ lFl := by decide
@[simp] theorem sp_lFl_ne_spT : lFl ≠ spT := by decide
@[simp] theorem sp_spT_ne_lDh : spT ≠ lDh := by decide
@[simp] theorem sp_lDh_ne_spT : lDh ≠ spT := by decide
@[simp] theorem sp_spT_ne_lDt : spT ≠ lDt := by decide
@[simp] theorem sp_lDt_ne_spT : lDt ≠ spT := by decide
@[simp] theorem sp_spT_ne_lDg : spT ≠ lDg := by decide
@[simp] theorem sp_lDg_ne_spT : lDg ≠ spT := by decide
@[simp] theorem sp_spT_ne_lDi : spT ≠ lDi := by decide
@[simp] theorem sp_lDi_ne_spT : lDi ≠ spT := by decide
@[simp] theorem sp_spT_ne_lRp : spT ≠ lRp := by decide
@[simp] theorem sp_lRp_ne_spT : lRp ≠ spT := by decide
@[simp] theorem sp_spT_ne_lRn : spT ≠ lRn := by decide
@[simp] theorem sp_lRn_ne_spT : lRn ≠ spT := by decide
@[simp] theorem sp_spT_ne_lDir : spT ≠ lDir := by decide
@[simp] theorem sp_lDir_ne_spT : lDir ≠ spT := by decide
@[simp] theorem sp_spT_ne_lFle : spT ≠ lFle := by decide
@[simp] theorem sp_lFle_ne_spT : lFle ≠ spT := by decide
@[simp] theorem sp_spT_ne_lKb : spT ≠ lKb := by decide
@[simp] theorem sp_lKb_ne_spT : lKb ≠ spT := by decide
@[simp] theorem sp_spA_ne_spT : spA ≠ spT := by decide
@[simp] theorem sp_spA_ne_spG : spA ≠ spG := by decide
@[simp] theorem sp_spA_ne_spI : spA ≠ spI := by decide
@[simp] theorem sp_spA_ne_spN : spA ≠ spN := by decide
@[simp] theorem sp_spA_ne_spX : spA ≠ spX := by decide
@[simp] theorem sp_spA_ne_spDm : spA ≠ spDm := by decide
@[simp] theorem sp_spA_ne_spB : spA ≠ spB := by decide
@[simp] theorem sp_spA_ne_spL : spA ≠ spL := by decide
@[simp] theorem sp_spA_ne_spO : spA ≠ spO := by decide
@[simp] theorem sp_spA_ne_spTa : spA ≠ spTa := by decide
@[simp] theorem sp_spA_ne_spQ : spA ≠ spQ := by decide
@[simp] theorem sp_spA_ne_spA2 : spA ≠ spA2 := by decide
@[simp] theorem sp_spA_ne_spW : spA ≠ spW := by decide
@[simp] theorem sp_spA_ne_spE0 : spA ≠ spE0 := by decide
@[simp] theorem sp_spA_ne_spR : spA ≠ spR := by decide
@[simp] theorem sp_spA_ne_kFu : spA ≠ kFu := by decide
@[simp] theorem sp_kFu_ne_spA : kFu ≠ spA := by decide
@[simp] theorem sp_spA_ne_kD : spA ≠ kD := by decide
@[simp] theorem sp_kD_ne_spA : kD ≠ spA := by decide
@[simp] theorem sp_spA_ne_lFl : spA ≠ lFl := by decide
@[simp] theorem sp_lFl_ne_spA : lFl ≠ spA := by decide
@[simp] theorem sp_spA_ne_lDh : spA ≠ lDh := by decide
@[simp] theorem sp_lDh_ne_spA : lDh ≠ spA := by decide
@[simp] theorem sp_spA_ne_lDt : spA ≠ lDt := by decide
@[simp] theorem sp_lDt_ne_spA : lDt ≠ spA := by decide
@[simp] theorem sp_spA_ne_lDg : spA ≠ lDg := by decide
@[simp] theorem sp_lDg_ne_spA : lDg ≠ spA := by decide
@[simp] theorem sp_spA_ne_lDi : spA ≠ lDi := by decide
@[simp] theorem sp_lDi_ne_spA : lDi ≠ spA := by decide
@[simp] theorem sp_spA_ne_lRp : spA ≠ lRp := by decide
@[simp] theorem sp_lRp_ne_spA : lRp ≠ spA := by decide
@[simp] theorem sp_spA_ne_lRn : spA ≠ lRn := by decide
@[simp] theorem sp_lRn_ne_spA : lRn ≠ spA := by decide
@[simp] theorem sp_spA_ne_lDir : spA ≠ lDir := by decide
@[simp] theorem sp_lDir_ne_spA : lDir ≠ spA := by decide
@[simp] theorem sp_spA_ne_lFle : spA ≠ lFle := by decide
@[simp] theorem sp_lFle_ne_spA : lFle ≠ spA := by decide
@[simp] theorem sp_spA_ne_lKb : spA ≠ lKb := by decide
@[simp] theorem sp_lKb_ne_spA : lKb ≠ spA := by decide
@[simp] theorem sp_spG_ne_spT : spG ≠ spT := by decide
@[simp] theorem sp_spG_ne_spA : spG ≠ spA := by decide
@[simp] theorem sp_spG_ne_spI : spG ≠ spI := by decide
@[simp] theorem sp_spG_ne_spN : spG ≠ spN := by decide
@[simp] theorem sp_spG_ne_spX : spG ≠ spX := by decide
@[simp] theorem sp_spG_ne_spDm : spG ≠ spDm := by decide
@[simp] theorem sp_spG_ne_spB : spG ≠ spB := by decide
@[simp] theorem sp_spG_ne_spL : spG ≠ spL := by decide
@[simp] theorem sp_spG_ne_spO : spG ≠ spO := by decide
@[simp] theorem sp_spG_ne_spTa : spG ≠ spTa := by decide
@[simp] theorem sp_spG_ne_spQ : spG ≠ spQ := by decide
@[simp] theorem sp_spG_ne_spA2 : spG ≠ spA2 := by decide
@[simp] theorem sp_spG_ne_spW : spG ≠ spW := by decide
@[simp] theorem sp_spG_ne_spE0 : spG ≠ spE0 := by decide
@[simp] theorem sp_spG_ne_spR : spG ≠ spR := by decide
@[simp] theorem sp_spG_ne_kFu : spG ≠ kFu := by decide
@[simp] theorem sp_kFu_ne_spG : kFu ≠ spG := by decide
@[simp] theorem sp_spG_ne_kD : spG ≠ kD := by decide
@[simp] theorem sp_kD_ne_spG : kD ≠ spG := by decide
@[simp] theorem sp_spG_ne_lFl : spG ≠ lFl := by decide
@[simp] theorem sp_lFl_ne_spG : lFl ≠ spG := by decide
@[simp] theorem sp_spG_ne_lDh : spG ≠ lDh := by decide
@[simp] theorem sp_lDh_ne_spG : lDh ≠ spG := by decide
@[simp] theorem sp_spG_ne_lDt : spG ≠ lDt := by decide
@[simp] theorem sp_lDt_ne_spG : lDt ≠ spG := by decide
@[simp] theorem sp_spG_ne_lDg : spG ≠ lDg := by decide
@[simp] theorem sp_lDg_ne_spG : lDg ≠ spG := by decide
@[simp] theorem sp_spG_ne_lDi : spG ≠ lDi := by decide
@[simp] theorem sp_lDi_ne_spG : lDi ≠ spG := by decide
@[simp] theorem sp_spG_ne_lRp : spG ≠ lRp := by decide
@[simp] theorem sp_lRp_ne_spG : lRp ≠ spG := by decide
@[simp] theorem sp_spG_ne_lRn : spG ≠ lRn := by decide
@[simp] theorem sp_lRn_ne_spG : lRn ≠ spG := by decide
@[simp] theorem sp_spG_ne_lDir : spG ≠ lDir := by decide
@[simp] theorem sp_lDir_ne_spG : lDir ≠ spG := by decide
@[simp] theorem sp_spG_ne_lFle : spG ≠ lFle := by decide
@[simp] theorem sp_lFle_ne_spG : lFle ≠ spG := by decide
@[simp] theorem sp_spG_ne_lKb : spG ≠ lKb := by decide
@[simp] theorem sp_lKb_ne_spG : lKb ≠ spG := by decide
@[simp] theorem sp_spI_ne_spT : spI ≠ spT := by decide
@[simp] theorem sp_spI_ne_spA : spI ≠ spA := by decide
@[simp] theorem sp_spI_ne_spG : spI ≠ spG := by decide
@[simp] theorem sp_spI_ne_spN : spI ≠ spN := by decide
@[simp] theorem sp_spI_ne_spX : spI ≠ spX := by decide
@[simp] theorem sp_spI_ne_spDm : spI ≠ spDm := by decide
@[simp] theorem sp_spI_ne_spB : spI ≠ spB := by decide
@[simp] theorem sp_spI_ne_spL : spI ≠ spL := by decide
@[simp] theorem sp_spI_ne_spO : spI ≠ spO := by decide
@[simp] theorem sp_spI_ne_spTa : spI ≠ spTa := by decide
@[simp] theorem sp_spI_ne_spQ : spI ≠ spQ := by decide
@[simp] theorem sp_spI_ne_spA2 : spI ≠ spA2 := by decide
@[simp] theorem sp_spI_ne_spW : spI ≠ spW := by decide
@[simp] theorem sp_spI_ne_spE0 : spI ≠ spE0 := by decide
@[simp] theorem sp_spI_ne_spR : spI ≠ spR := by decide
@[simp] theorem sp_spI_ne_kFu : spI ≠ kFu := by decide
@[simp] theorem sp_kFu_ne_spI : kFu ≠ spI := by decide
@[simp] theorem sp_spI_ne_kD : spI ≠ kD := by decide
@[simp] theorem sp_kD_ne_spI : kD ≠ spI := by decide
@[simp] theorem sp_spI_ne_lFl : spI ≠ lFl := by decide
@[simp] theorem sp_lFl_ne_spI : lFl ≠ spI := by decide
@[simp] theorem sp_spI_ne_lDh : spI ≠ lDh := by decide
@[simp] theorem sp_lDh_ne_spI : lDh ≠ spI := by decide
@[simp] theorem sp_spI_ne_lDt : spI ≠ lDt := by decide
@[simp] theorem sp_lDt_ne_spI : lDt ≠ spI := by decide
@[simp] theorem sp_spI_ne_lDg : spI ≠ lDg := by decide
@[simp] theorem sp_lDg_ne_spI : lDg ≠ spI := by decide
@[simp] theorem sp_spI_ne_lDi : spI ≠ lDi := by decide
@[simp] theorem sp_lDi_ne_spI : lDi ≠ spI := by decide
@[simp] theorem sp_spI_ne_lRp : spI ≠ lRp := by decide
@[simp] theorem sp_lRp_ne_spI : lRp ≠ spI := by decide
@[simp] theorem sp_spI_ne_lRn : spI ≠ lRn := by decide
@[simp] theorem sp_lRn_ne_spI : lRn ≠ spI := by decide
@[simp] theorem sp_spI_ne_lDir : spI ≠ lDir := by decide
@[simp] theorem sp_lDir_ne_spI : lDir ≠ spI := by decide
@[simp] theorem sp_spI_ne_lFle : spI ≠ lFle := by decide
@[simp] theorem sp_lFle_ne_spI : lFle ≠ spI := by decide
@[simp] theorem sp_spI_ne_lKb : spI ≠ lKb := by decide
@[simp] theorem sp_lKb_ne_spI : lKb ≠ spI := by decide
@[simp] theorem sp_spN_ne_spT : spN ≠ spT := by decide
@[simp] theorem sp_spN_ne_spA : spN ≠ spA := by decide
@[simp] theorem sp_spN_ne_spG : spN ≠ spG := by decide
@[simp] theorem sp_spN_ne_spI : spN ≠ spI := by decide
@[simp] theorem sp_spN_ne_spX : spN ≠ spX := by decide
@[simp] theorem sp_spN_ne_spDm : spN ≠ spDm := by decide
@[simp] theorem sp_spN_ne_spB : spN ≠ spB := by decide
@[simp] theorem sp_spN_ne_spL : spN ≠ spL := by decide
@[simp] theorem sp_spN_ne_spO : spN ≠ spO := by decide
@[simp] theorem sp_spN_ne_spTa : spN ≠ spTa := by decide
@[simp] theorem sp_spN_ne_spQ : spN ≠ spQ := by decide
@[simp] theorem sp_spN_ne_spA2 : spN ≠ spA2 := by decide
@[simp] theorem sp_spN_ne_spW : spN ≠ spW := by decide
@[simp] theorem sp_spN_ne_spE0 : spN ≠ spE0 := by decide
@[simp] theorem sp_spN_ne_spR : spN ≠ spR := by decide
@[simp] theorem sp_spN_ne_kFu : spN ≠ kFu := by decide
@[simp] theorem sp_kFu_ne_spN : kFu ≠ spN := by decide
@[simp] theorem sp_spN_ne_kD : spN ≠ kD := by decide
@[simp] theorem sp_kD_ne_spN : kD ≠ spN := by decide
@[simp] theorem sp_spN_ne_lFl : spN ≠ lFl := by decide
@[simp] theorem sp_lFl_ne_spN : lFl ≠ spN := by decide
@[simp] theorem sp_spN_ne_lDh : spN ≠ lDh := by decide
@[simp] theorem sp_lDh_ne_spN : lDh ≠ spN := by decide
@[simp] theorem sp_spN_ne_lDt : spN ≠ lDt := by decide
@[simp] theorem sp_lDt_ne_spN : lDt ≠ spN := by decide
@[simp] theorem sp_spN_ne_lDg : spN ≠ lDg := by decide
@[simp] theorem sp_lDg_ne_spN : lDg ≠ spN := by decide
@[simp] theorem sp_spN_ne_lDi : spN ≠ lDi := by decide
@[simp] theorem sp_lDi_ne_spN : lDi ≠ spN := by decide
@[simp] theorem sp_spN_ne_lRp : spN ≠ lRp := by decide
@[simp] theorem sp_lRp_ne_spN : lRp ≠ spN := by decide
@[simp] theorem sp_spN_ne_lRn : spN ≠ lRn := by decide
@[simp] theorem sp_lRn_ne_spN : lRn ≠ spN := by decide
@[simp] theorem sp_spN_ne_lDir : spN ≠ lDir := by decide
@[simp] theorem sp_lDir_ne_spN : lDir ≠ spN := by decide
@[simp] theorem sp_spN_ne_lFle : spN ≠ lFle := by decide
@[simp] theorem sp_lFle_ne_spN : lFle ≠ spN := by decide
@[simp] theorem sp_spN_ne_lKb : spN ≠ lKb := by decide
@[simp] theorem sp_lKb_ne_spN : lKb ≠ spN := by decide
@[simp] theorem sp_spX_ne_spT : spX ≠ spT := by decide
@[simp] theorem sp_spX_ne_spA : spX ≠ spA := by decide
@[simp] theorem sp_spX_ne_spG : spX ≠ spG := by decide
@[simp] theorem sp_spX_ne_spI : spX ≠ spI := by decide
@[simp] theorem sp_spX_ne_spN : spX ≠ spN := by decide
@[simp] theorem sp_spX_ne_spDm : spX ≠ spDm := by decide
@[simp] theorem sp_spX_ne_spB : spX ≠ spB := by decide
@[simp] theorem sp_spX_ne_spL : spX ≠ spL := by decide
@[simp] theorem sp_spX_ne_spO : spX ≠ spO := by decide
@[simp] theorem sp_spX_ne_spTa : spX ≠ spTa := by decide
@[simp] theorem sp_spX_ne_spQ : spX ≠ spQ := by decide
@[simp] theorem sp_spX_ne_spA2 : spX ≠ spA2 := by decide
@[simp] theorem sp_spX_ne_spW : spX ≠ spW := by decide
@[simp] theorem sp_spX_ne_spE0 : spX ≠ spE0 := by decide
@[simp] theorem sp_spX_ne_spR : spX ≠ spR := by decide
@[simp] theorem sp_spX_ne_kFu : spX ≠ kFu := by decide
@[simp] theorem sp_kFu_ne_spX : kFu ≠ spX := by decide
@[simp] theorem sp_spX_ne_kD : spX ≠ kD := by decide
@[simp] theorem sp_kD_ne_spX : kD ≠ spX := by decide
@[simp] theorem sp_spX_ne_lFl : spX ≠ lFl := by decide
@[simp] theorem sp_lFl_ne_spX : lFl ≠ spX := by decide
@[simp] theorem sp_spX_ne_lDh : spX ≠ lDh := by decide
@[simp] theorem sp_lDh_ne_spX : lDh ≠ spX := by decide
@[simp] theorem sp_spX_ne_lDt : spX ≠ lDt := by decide
@[simp] theorem sp_lDt_ne_spX : lDt ≠ spX := by decide
@[simp] theorem sp_spX_ne_lDg : spX ≠ lDg := by decide
@[simp] theorem sp_lDg_ne_spX : lDg ≠ spX := by decide
@[simp] theorem sp_spX_ne_lDi : spX ≠ lDi := by decide
@[simp] theorem sp_lDi_ne_spX : lDi ≠ spX := by decide
@[simp] theorem sp_spX_ne_lRp : spX ≠ lRp := by decide
@[simp] theorem sp_lRp_ne_spX : lRp ≠ spX := by decide
@[simp] theorem sp_spX_ne_lRn : spX ≠ lRn := by decide
@[simp] theorem sp_lRn_ne_spX : lRn ≠ spX := by decide
@[simp] theorem sp_spX_ne_lDir : spX ≠ lDir := by decide
@[simp] theorem sp_lDir_ne_spX : lDir ≠ spX := by decide
@[simp] theorem sp_spX_ne_lFle : spX ≠ lFle := by decide
@[simp] theorem sp_lFle_ne_spX : lFle ≠ spX := by decide
@[simp] theorem sp_spX_ne_lKb : spX ≠ lKb := by decide
@[simp] theorem sp_lKb_ne_spX : lKb ≠ spX := by decide
@[simp] theorem sp_spDm_ne_spT : spDm ≠ spT := by decide
@[simp] theorem sp_spDm_ne_spA : spDm ≠ spA := by decide
@[simp] theorem sp_spDm_ne_spG : spDm ≠ spG := by decide
@[simp] theorem sp_spDm_ne_spI : spDm ≠ spI := by decide
@[simp] theorem sp_spDm_ne_spN : spDm ≠ spN := by decide
@[simp] theorem sp_spDm_ne_spX : spDm ≠ spX := by decide
@[simp] theorem sp_spDm_ne_spB : spDm ≠ spB := by decide
@[simp] theorem sp_spDm_ne_spL : spDm ≠ spL := by decide
@[simp] theorem sp_spDm_ne_spO : spDm ≠ spO := by decide
@[simp] theorem sp_spDm_ne_spTa : spDm ≠ spTa := by decide
@[simp] theorem sp_spDm_ne_spQ : spDm ≠ spQ := by decide
@[simp] theorem sp_spDm_ne_spA2 : spDm ≠ spA2 := by decide
@[simp] theorem sp_spDm_ne_spW : spDm ≠ spW := by decide
@[simp] theorem sp_spDm_ne_spE0 : spDm ≠ spE0 := by decide
@[simp] theorem sp_spDm_ne_spR : spDm ≠ spR := by decide
@[simp] theorem sp_spDm_ne_kFu : spDm ≠ kFu := by decide
@[simp] theorem sp_kFu_ne_spDm : kFu ≠ spDm := by decide
@[simp] theorem sp_spDm_ne_kD : spDm ≠ kD := by decide
@[simp] theorem sp_kD_ne_spDm : kD ≠ spDm := by decide
@[simp] theorem sp_spDm_ne_lFl : spDm ≠ lFl := by decide
@[simp] theorem sp_lFl_ne_spDm : lFl ≠ spDm := by decide
@[simp] theorem sp_spDm_ne_lDh : spDm ≠ lDh := by decide
@[simp] theorem sp_lDh_ne_spDm : lDh ≠ spDm := by decide
@[simp] theorem sp_spDm_ne_lDt : spDm ≠ lDt := by decide
@[simp] theorem sp_lDt_ne_spDm : lDt ≠ spDm := by decide
@[simp] theorem sp_spDm_ne_lDg : spDm ≠ lDg := by decide
@[simp] theorem sp_lDg_ne_spDm : lDg ≠ spDm := by decide
@[simp] theorem sp_spDm_ne_lDi : spDm ≠ lDi := by decide
@[simp] theorem sp_lDi_ne_spDm : lDi ≠ spDm := by decide
@[simp] theorem sp_spDm_ne_lRp : spDm ≠ lRp := by decide
@[simp] theorem sp_lRp_ne_spDm : lRp ≠ spDm := by decide
@[simp] theorem sp_spDm_ne_lRn : spDm ≠ lRn := by decide
@[simp] theorem sp_lRn_ne_spDm : lRn ≠ spDm := by decide
@[simp] theorem sp_spDm_ne_lDir : spDm ≠ lDir := by decide
@[simp] theorem sp_lDir_ne_spDm : lDir ≠ spDm := by decide
@[simp] theorem sp_spDm_ne_lFle : spDm ≠ lFle := by decide
@[simp] theorem sp_lFle_ne_spDm : lFle ≠ spDm := by decide
@[simp] theorem sp_spDm_ne_lKb : spDm ≠ lKb := by decide
@[simp] theorem sp_lKb_ne_spDm : lKb ≠ spDm := by decide
@[simp] theorem sp_spB_ne_spT : spB ≠ spT := by decide
@[simp] theorem sp_spB_ne_spA : spB ≠ spA := by decide
@[simp] theorem sp_spB_ne_spG : spB ≠ spG := by decide
@[simp] theorem sp_spB_ne_spI : spB ≠ spI := by decide
@[simp] theorem sp_spB_ne_spN : spB ≠ spN := by decide
@[simp] theorem sp_spB_ne_spX : spB ≠ spX := by decide
@[simp] theorem sp_spB_ne_spDm : spB ≠ spDm := by decide
@[simp] theorem sp_spB_ne_spL : spB ≠ spL := by decide
@[simp] theorem sp_spB_ne_spO : spB ≠ spO := by decide
@[simp] theorem sp_spB_ne_spTa : spB ≠ spTa := by decide
@[simp] theorem sp_spB_ne_spQ : spB ≠ spQ := by decide
@[simp] theorem sp_spB_ne_spA2 : spB ≠ spA2 := by decide
@[simp] theorem sp_spB_ne_spW : spB ≠ spW := by decide
@[simp] theorem sp_spB_ne_spE0 : spB ≠ spE0 := by decide
@[simp] theorem sp_spB_ne_spR : spB ≠ spR := by decide
@[simp] theorem sp_spB_ne_kFu : spB ≠ kFu := by decide
@[simp] theorem sp_kFu_ne_spB : kFu ≠ spB := by decide
@[simp] theorem sp_spB_ne_kD : spB ≠ kD := by decide
@[simp] theorem sp_kD_ne_spB : kD ≠ spB := by decide
@[simp] theorem sp_spB_ne_lFl : spB ≠ lFl := by decide
@[simp] theorem sp_lFl_ne_spB : lFl ≠ spB := by decide
@[simp] theorem sp_spB_ne_lDh : spB ≠ lDh := by decide
@[simp] theorem sp_lDh_ne_spB : lDh ≠ spB := by decide
@[simp] theorem sp_spB_ne_lDt : spB ≠ lDt := by decide
@[simp] theorem sp_lDt_ne_spB : lDt ≠ spB := by decide
@[simp] theorem sp_spB_ne_lDg : spB ≠ lDg := by decide
@[simp] theorem sp_lDg_ne_spB : lDg ≠ spB := by decide
@[simp] theorem sp_spB_ne_lDi : spB ≠ lDi := by decide
@[simp] theorem sp_lDi_ne_spB : lDi ≠ spB := by decide
@[simp] theorem sp_spB_ne_lRp : spB ≠ lRp := by decide
@[simp] theorem sp_lRp_ne_spB : lRp ≠ spB := by decide
@[simp] theorem sp_spB_ne_lRn : spB ≠ lRn := by decide
@[simp] theorem sp_lRn_ne_spB : lRn ≠ spB := by decide
@[simp] theorem sp_spB_ne_lDir : spB ≠ lDir := by decide
@[simp] theorem sp_lDir_ne_spB : lDir ≠ spB := by decide
@[simp] theorem sp_spB_ne_lFle : spB ≠ lFle := by decide
@[simp] theorem sp_lFle_ne_spB : lFle ≠ spB := by decide
@[simp] theorem sp_spB_ne_lKb : spB ≠ lKb := by decide
@[simp] theorem sp_lKb_ne_spB : lKb ≠ spB := by decide
@[simp] theorem sp_spL_ne_spT : spL ≠ spT := by decide
@[simp] theorem sp_spL_ne_spA : spL ≠ spA := by decide
@[simp] theorem sp_spL_ne_spG : spL ≠ spG := by decide
@[simp] theorem sp_spL_ne_spI : spL ≠ spI := by decide
@[simp] theorem sp_spL_ne_spN : spL ≠ spN := by decide
@[simp] theorem sp_spL_ne_spX : spL ≠ spX := by decide
@[simp] theorem sp_spL_ne_spDm : spL ≠ spDm := by decide
@[simp] theorem sp_spL_ne_spB : spL ≠ spB := by decide
@[simp] theorem sp_spL_ne_spO : spL ≠ spO := by decide
@[simp] theorem sp_spL_ne_spTa : spL ≠ spTa := by decide
@[simp] theorem sp_spL_ne_spQ : spL ≠ spQ := by decide
@[simp] theorem sp_spL_ne_spA2 : spL ≠ spA2 := by decide
@[simp] theorem sp_spL_ne_spW : spL ≠ spW := by decide
@[simp] theorem sp_spL_ne_spE0 : spL ≠ spE0 := by decide
@[simp] theorem sp_spL_ne_spR : spL ≠ spR := by decide
@[simp] theorem sp_spL_ne_kFu : spL ≠ kFu := by decide
@[simp] theorem sp_kFu_ne_spL : kFu ≠ spL := by decide
@[simp] theorem sp_spL_ne_kD : spL ≠ kD := by decide
@[simp] theorem sp_kD_ne_spL : kD ≠ spL := by decide
@[simp] theorem sp_spL_ne_lFl : spL ≠ lFl := by decide
@[simp] theorem sp_lFl_ne_spL : lFl ≠ spL := by decide
@[simp] theorem sp_spL_ne_lDh : spL ≠ lDh := by decide
@[simp] theorem sp_lDh_ne_spL : lDh ≠ spL := by decide
@[simp] theorem sp_spL_ne_lDt : spL ≠ lDt := by decide
@[simp] theorem sp_lDt_ne_spL : lDt ≠ spL := by decide
@[simp] theorem sp_spL_ne_lDg : spL ≠ lDg := by decide
@[simp] theorem sp_lDg_ne_spL : lDg ≠ spL := by decide
@[simp] theorem sp_spL_ne_lDi : spL ≠ lDi := by decide
@[simp] theorem sp_lDi_ne_spL : lDi ≠ spL := by decide
@[simp] theorem sp_spL_ne_lRp : spL ≠ lRp := by decide
@[simp] theorem sp_lRp_ne_spL : lRp ≠ spL := by decide
@[simp] theorem sp_spL_ne_lRn : spL ≠ lRn := by decide
@[simp] theorem sp_lRn_ne_spL : lRn ≠ spL := by decide
@[simp] theorem sp_spL_ne_lDir : spL ≠ lDir := by decide
@[simp] theorem sp_lDir_ne_spL : lDir ≠ spL := by decide
@[simp] theorem sp_spL_ne_lFle : spL ≠ lFle := by decide
@[simp] theorem sp_lFle_ne_spL : lFle ≠ spL := by decide
@[simp] theorem sp_spL_ne_lKb : spL ≠ lKb := by decide
@[simp] theorem sp_lKb_ne_spL : lKb ≠ spL := by decide
@[simp] theorem sp_spO_ne_spT : spO ≠ spT := by decide
@[simp] theorem sp_spO_ne_spA : spO ≠ spA := by decide
@[simp] theorem sp_spO_ne_spG : spO ≠ spG := by decide
@[simp] theorem sp_spO_ne_spI : spO ≠ spI := by decide
@[simp] theorem sp_spO_ne_spN : spO ≠ spN := by decide
@[simp] theorem sp_spO_ne_spX : spO ≠ spX := by decide
@[simp] theorem sp_spO_ne_spDm : spO ≠ spDm := by decide
@[simp] theorem sp_spO_ne_spB : spO ≠ spB := by decide
@[simp] theorem sp_spO_ne_spL : spO ≠ spL := by decide
@[simp] theorem sp_spO_ne_spTa : spO ≠ spTa := by decide
@[simp] theorem sp_spO_ne_spQ : spO ≠ spQ := by decide
@[simp] theorem sp_spO_ne_spA2 : spO ≠ spA2 := by decide
@[simp] theorem sp_spO_ne_spW : spO ≠ spW := by decide
@[simp] theorem sp_spO_ne_spE0 : spO ≠ spE0 := by decide
@[simp] theorem sp_spO_ne_spR : spO ≠ spR := by decide
@[simp] theorem sp_spO_ne_kFu : spO ≠ kFu := by decide
@[simp] theorem sp_kFu_ne_spO : kFu ≠ spO := by decide
@[simp] theorem sp_spO_ne_kD : spO ≠ kD := by decide
@[simp] theorem sp_kD_ne_spO : kD ≠ spO := by decide
@[simp] theorem sp_spO_ne_lFl : spO ≠ lFl := by decide
@[simp] theorem sp_lFl_ne_spO : lFl ≠ spO := by decide
@[simp] theorem sp_spO_ne_lDh : spO ≠ lDh := by decide
@[simp] theorem sp_lDh_ne_spO : lDh ≠ spO := by decide
@[simp] theorem sp_spO_ne_lDt : spO ≠ lDt := by decide
@[simp] theorem sp_lDt_ne_spO : lDt ≠ spO := by decide
@[simp] theorem sp_spO_ne_lDg : spO ≠ lDg := by decide
@[simp] theorem sp_lDg_ne_spO : lDg ≠ spO := by decide
@[simp] theorem sp_spO_ne_lDi : spO ≠ lDi := by decide
@[simp] theorem sp_lDi_ne_spO : lDi ≠ spO := by decide
@[simp] theorem sp_spO_ne_lRp : spO ≠ lRp := by decide
@[simp] theorem sp_lRp_ne_spO : lRp ≠ spO := by decide
@[simp] theorem sp_spO_ne_lRn : spO ≠ lRn := by decide
@[simp] theorem sp_lRn_ne_spO : lRn ≠ spO := by decide
@[simp] theorem sp_spO_ne_lDir : spO ≠ lDir := by decide
@[simp] theorem sp_lDir_ne_spO : lDir ≠ spO := by decide
@[simp] theorem sp_spO_ne_lFle : spO ≠ lFle := by decide
@[simp] theorem sp_lFle_ne_spO : lFle ≠ spO := by decide
@[simp] theorem sp_spO_ne_lKb : spO ≠ lKb := by decide
@[simp] theorem sp_lKb_ne_spO : lKb ≠ spO := by decide
@[simp] theorem sp_spTa_ne_spT : spTa ≠ spT := by decide
@[simp] theorem sp_spTa_ne_spA : spTa ≠ spA := by decide
@[simp] theorem sp_spTa_ne_spG : spTa ≠ spG := by decide
@[simp] theorem sp_spTa_ne_spI : spTa ≠ spI := by decide
@[simp] theorem sp_spTa_ne_spN : spTa ≠ spN := by decide
@[simp] theorem sp_spTa_ne_spX : spTa ≠ spX := by decide
@[simp] theorem sp_spTa_ne_spDm : spTa ≠ spDm := by decide
@[simp] theorem sp_spTa_ne_spB : spTa ≠ spB := by decide
@[simp] theorem sp_spTa_ne_spL : spTa ≠ spL := by decide
@[simp] theorem sp_spTa_ne_spO : spTa ≠ spO := by decide
@[simp] theorem sp_spTa_ne_spQ : spTa ≠ spQ := by decide
@[simp] theorem sp_spTa_ne_spA2 : spTa ≠ spA2 := by decide
@[simp] theorem sp_spTa_ne_spW : spTa ≠ spW := by decide
@[simp] theorem sp_spTa_ne_spE0 : spTa ≠ spE0 := by decide
@[simp] theorem sp_spTa_ne_spR : spTa ≠ spR := by decide
@[simp] theorem sp_spTa_ne_kFu : spTa ≠ kFu := by decide
@[simp] theorem sp_kFu_ne_spTa : kFu ≠ spTa := by decide
@[simp] theorem sp_spTa_ne_kD : spTa ≠ kD := by decide
@[simp] theorem sp_kD_ne_spTa : kD ≠ spTa := by decide
@[simp] theorem sp_spTa_ne_lFl : spTa ≠ lFl := by decide
@[simp] theorem sp_lFl_ne_spTa : lFl ≠ spTa := by decide
@[simp] theorem sp_spTa_ne_lDh : spTa ≠ lDh := by decide
@[simp] theorem sp_lDh_ne_spTa : lDh ≠ spTa := by decide
@[simp] theorem sp_spTa_ne_lDt : spTa ≠ lDt := by decide
@[simp] theorem sp_lDt_ne_spTa : lDt ≠ spTa := by decide
@[simp] theorem sp_spTa_ne_lDg : spTa ≠ lDg := by decide
@[simp] theorem sp_lDg_ne_spTa : lDg ≠ spTa := by decide
@[simp] theorem sp_spTa_ne_lDi : spTa ≠ lDi := by decide
@[simp] theorem sp_lDi_ne_spTa : lDi ≠ spTa := by decide
@[simp] theorem sp_spTa_ne_lRp : spTa ≠ lRp := by decide
@[simp] theorem sp_lRp_ne_spTa : lRp ≠ spTa := by decide
@[simp] theorem sp_spTa_ne_lRn : spTa ≠ lRn := by decide
@[simp] theorem sp_lRn_ne_spTa : lRn ≠ spTa := by decide
@[simp] theorem sp_spTa_ne_lDir : spTa ≠ lDir := by decide
@[simp] theorem sp_lDir_ne_spTa : lDir ≠ spTa := by decide
@[simp] theorem sp_spTa_ne_lFle : spTa ≠ lFle := by decide
@[simp] theorem sp_lFle_ne_spTa : lFle ≠ spTa := by decide
@[simp] theorem sp_spTa_ne_lKb : spTa ≠ lKb := by decide
@[simp] theorem sp_lKb_ne_spTa : lKb ≠ spTa := by decide
@[simp] theorem sp_spQ_ne_spT : spQ ≠ spT := by decide
@[simp] theorem sp_spQ_ne_spA : spQ ≠ spA := by decide
@[simp] theorem sp_spQ_ne_spG : spQ ≠ spG := by decide
@[simp] theorem sp_spQ_ne_spI : spQ ≠ spI := by decide
@[simp] theorem sp_spQ_ne_spN : spQ ≠ spN := by decide
@[simp] theorem sp_spQ_ne_spX : spQ ≠ spX := by decide
@[simp] theorem sp_spQ_ne_spDm : spQ ≠ spDm := by decide
@[simp] theorem sp_spQ_ne_spB : spQ ≠ spB := by decide
@[simp] theorem sp_spQ_ne_spL : spQ ≠ spL := by decide
@[simp] theorem sp_spQ_ne_spO : spQ ≠ spO := by decide
@[simp] theorem sp_spQ_ne_spTa : spQ ≠ spTa := by decide
@[simp] theorem sp_spQ_ne_spA2 : spQ ≠ spA2 := by decide
@[simp] theorem sp_spQ_ne_spW : spQ ≠ spW := by decide
@[simp] theorem sp_spQ_ne_spE0 : spQ ≠ spE0 := by decide
@[simp] theorem sp_spQ_ne_spR : spQ ≠ spR := by decide
@[simp] theorem sp_spQ_ne_kFu : spQ ≠ kFu := by decide
@[simp] theorem sp_kFu_ne_spQ : kFu ≠ spQ := by decide
@[simp] theorem sp_spQ_ne_kD : spQ ≠ kD := by decide
@[simp] theorem sp_kD_ne_spQ : kD ≠ spQ := by decide
@[simp] theorem sp_spQ_ne_lFl : spQ ≠ lFl := by decide
@[simp] theorem sp_lFl_ne_spQ : lFl ≠ spQ := by decide
@[simp] theorem sp_spQ_ne_lDh : spQ ≠ lDh := by decide
@[simp] theorem sp_lDh_ne_spQ : lDh ≠ spQ := by decide
@[simp] theorem sp_spQ_ne_lDt : spQ ≠ lDt := by decide
@[simp] theorem sp_lDt_ne_spQ : lDt ≠ spQ := by decide
@[simp] theorem sp_spQ_ne_lDg : spQ ≠ lDg := by decide
@[simp] theorem sp_lDg_ne_spQ : lDg ≠ spQ := by decide
@[simp] theorem sp_spQ_ne_lDi : spQ ≠ lDi := by decide
@[simp] theorem sp_lDi_ne_spQ : lDi ≠ spQ := by decide
@[simp] theorem sp_spQ_ne_lRp : spQ ≠ lRp := by decide
@[simp] theorem sp_lRp_ne_spQ : lRp ≠ spQ := by decide
@[simp] theorem sp_spQ_ne_lRn : spQ ≠ lRn := by decide
@[simp] theorem sp_lRn_ne_spQ : lRn ≠ spQ := by decide
@[simp] theorem sp_spQ_ne_lDir : spQ ≠ lDir := by decide
@[simp] theorem sp_lDir_ne_spQ : lDir ≠ spQ := by decide
@[simp] theorem sp_spQ_ne_lFle : spQ ≠ lFle := by decide
@[simp] theorem sp_lFle_ne_spQ : lFle ≠ spQ := by decide
@[simp] theorem sp_spQ_ne_lKb : spQ ≠ lKb := by decide
@[simp] theorem sp_lKb_ne_spQ : lKb ≠ spQ := by decide
@[simp] theorem sp_spA2_ne_spT : spA2 ≠ spT := by decide
@[simp] theorem sp_spA2_ne_spA : spA2 ≠ spA := by decide
@[simp] theorem sp_spA2_ne_spG : spA2 ≠ spG := by decide
@[simp] theorem sp_spA2_ne_spI : spA2 ≠ spI := by decide
@[simp] theorem sp_spA2_ne_spN : spA2 ≠ spN := by decide
@[simp] theorem sp_spA2_ne_spX : spA2 ≠ spX := by decide
@[simp] theorem sp_spA2_ne_spDm : spA2 ≠ spDm := by decide
@[simp] theorem sp_spA2_ne_spB : spA2 ≠ spB := by decide
@[simp] theorem sp_spA2_ne_spL : spA2 ≠ spL := by decide
@[simp] theorem sp_spA2_ne_spO : spA2 ≠ spO := by decide
@[simp] theorem sp_spA2_ne_spTa : spA2 ≠ spTa := by decide
@[simp] theorem sp_spA2_ne_spQ : spA2 ≠ spQ := by decide
@[simp] theorem sp_spA2_ne_spW : spA2 ≠ spW := by decide
@[simp] theorem sp_spA2_ne_spE0 : spA2 ≠ spE0 := by decide
@[simp] theorem sp_spA2_ne_spR : spA2 ≠ spR := by decide
@[simp] theorem sp_spA2_ne_kFu : spA2 ≠ kFu := by decide
@[simp] theorem sp_kFu_ne_spA2 : kFu ≠ spA2 := by decide
@[simp] theorem sp_spA2_ne_kD : spA2 ≠ kD := by decide
@[simp] theorem sp_kD_ne_spA2 : kD ≠ spA2 := by decide
@[simp] theorem sp_spA2_ne_lFl : spA2 ≠ lFl := by decide
@[simp] theorem sp_lFl_ne_spA2 : lFl ≠ spA2 := by decide
@[simp] theorem sp_spA2_ne_lDh : spA2 ≠ lDh := by decide
@[simp] theorem sp_lDh_ne_spA2 : lDh ≠ spA2 := by decide
@[simp] theorem sp_spA2_ne_lDt : spA2 ≠ lDt := by decide
@[simp] theorem sp_lDt_ne_spA2 : lDt ≠ spA2 := by decide
@[simp] theorem sp_spA2_ne_lDg : spA2 ≠ lDg := by decide
@[simp] theorem sp_lDg_ne_spA2 : lDg ≠ spA2 := by decide
@[simp] theorem sp_spA2_ne_lDi : spA2 ≠ lDi := by decide
@[simp] theorem sp_lDi_ne_spA2 : lDi ≠ spA2 := by decide
@[simp] theorem sp_spA2_ne_lRp : spA2 ≠ lRp := by decide
@[simp] theorem sp_lRp_ne_spA2 : lRp ≠ spA2 := by decide
@[simp] theorem sp_spA2_ne_lRn : spA2 ≠ lRn := by decide
@[simp] theorem sp_lRn_ne_spA2 : lRn ≠ spA2 := by decide
@[simp] theorem sp_spA2_ne_lDir : spA2 ≠ lDir := by decide
@[simp] theorem sp_lDir_ne_spA2 : lDir ≠ spA2 := by decide
@[simp] theorem sp_spA2_ne_lFle : spA2 ≠ lFle := by decide
@[simp] theorem sp_lFle_ne_spA2 : lFle ≠ spA2 := by decide
@[simp] theorem sp_spA2_ne_lKb : spA2 ≠ lKb := by decide
@[simp] theorem sp_lKb_ne_spA2 : lKb ≠ spA2 := by decide
@[simp] theorem sp_spW_ne_spT : spW ≠ spT := by decide
@[simp] theorem sp_spW_ne_spA : spW ≠ spA := by decide
@[simp] theorem sp_spW_ne_spG : spW ≠ spG := by decide
@[simp] theorem sp_spW_ne_spI : spW ≠ spI := by decide
@[simp] theorem sp_spW_ne_spN : spW ≠ spN := by decide
@[simp] theorem sp_spW_ne_spX : spW ≠ spX := by decide
@[simp] theorem sp_spW_ne_spDm : spW ≠ spDm := by decide
@[simp] theorem sp_spW_ne_spB : spW ≠ spB := by decide
@[simp] theorem sp_spW_ne_spL : spW ≠ spL := by decide
@[simp] theorem sp_spW_ne_spO : spW ≠ spO := by decide
@[simp] theorem sp_spW_ne_spTa : spW ≠ spTa := by decide
@[simp] theorem sp_spW_ne_spQ : spW ≠ spQ := by decide
@[simp] theorem sp_spW_ne_spA2 : spW ≠ spA2 := by decide
@[simp] theorem sp_spW_ne_spE0 : spW ≠ spE0 := by decide
@[simp] theorem sp_spW_ne_spR : spW ≠ spR := by decide
@[simp] theorem sp_spW_ne_kFu : spW ≠ kFu := by decide
@[simp] theorem sp_kFu_ne_spW : kFu ≠ spW := by decide
@[simp] theorem sp_spW_ne_kD : spW ≠ kD := by decide
@[simp] theorem sp_kD_ne_spW : kD ≠ spW := by decide
@[simp] theorem sp_spW_ne_lFl : spW ≠ lFl := by decide
@[simp] theorem sp_lFl_ne_spW : lFl ≠ spW := by decide
@[simp] theorem sp_spW_ne_lDh : spW ≠ lDh := by decide
@[simp] theorem sp_lDh_ne_spW : lDh ≠ spW := by decide
@[simp] theorem sp_spW_ne_lDt : spW ≠ lDt := by decide
@[simp] theorem sp_lDt_ne_spW : lDt ≠ spW := by decide
@[simp] theorem sp_spW_ne_lDg : spW ≠ lDg := by decide
@[simp] theorem sp_lDg_ne_spW : lDg ≠ spW := by decide
@[simp] theorem sp_spW_ne_lDi : spW ≠ lDi := by decide
@[simp] theorem sp_lDi_ne_spW : lDi ≠ spW := by decide
@[simp] theorem sp_spW_ne_lRp : spW ≠ lRp := by decide
@[simp] theorem sp_lRp_ne_spW : lRp ≠ spW := by decide
@[simp] theorem sp_spW_ne_lRn : spW ≠ lRn := by decide
@[simp] theorem sp_lRn_ne_spW : lRn ≠ spW := by decide
@[simp] theorem sp_spW_ne_lDir : spW ≠ lDir := by decide
@[simp] theorem sp_lDir_ne_spW : lDir ≠ spW := by decide
@[simp] theorem sp_spW_ne_lFle : spW ≠ lFle := by decide
@[simp] theorem sp_lFle_ne_spW : lFle ≠ spW := by decide
@[simp] theorem sp_spW_ne_lKb : spW ≠ lKb := by decide
@[simp] theorem sp_lKb_ne_spW : lKb ≠ spW := by decide
@[simp] theorem sp_spE0_ne_spT : spE0 ≠ spT := by decide
@[simp] theorem sp_spE0_ne_spA : spE0 ≠ spA := by decide
@[simp] theorem sp_spE0_ne_spG : spE0 ≠ spG := by decide
@[simp] theorem sp_spE0_ne_spI : spE0 ≠ spI := by decide
@[simp] theorem sp_spE0_ne_spN : spE0 ≠ spN := by decide
@[simp] theorem sp_spE0_ne_spX : spE0 ≠ spX := by decide
@[simp] theorem sp_spE0_ne_spDm : spE0 ≠ spDm := by decide
@[simp] theorem sp_spE0_ne_spB : spE0 ≠ spB := by decide
@[simp] theorem sp_spE0_ne_spL : spE0 ≠ spL := by decide
@[simp] theorem sp_spE0_ne_spO : spE0 ≠ spO := by decide
@[simp] theorem sp_spE0_ne_spTa : spE0 ≠ spTa := by decide
@[simp] theorem sp_spE0_ne_spQ : spE0 ≠ spQ := by decide
@[simp] theorem sp_spE0_ne_spA2 : spE0 ≠ spA2 := by decide
@[simp] theorem sp_spE0_ne_spW : spE0 ≠ spW := by decide
@[simp] theorem sp_spE0_ne_spR : spE0 ≠ spR := by decide
@[simp] theorem sp_spE0_ne_kFu : spE0 ≠ kFu := by decide
@[simp] theorem sp_kFu_ne_spE0 : kFu ≠ spE0 := by decide
@[simp] theorem sp_spE0_ne_kD : spE0 ≠ kD := by decide
@[simp] theorem sp_kD_ne_spE0 : kD ≠ spE0 := by decide
@[simp] theorem sp_spE0_ne_lFl : spE0 ≠ lFl := by decide
@[simp] theorem sp_lFl_ne_spE0 : lFl ≠ spE0 := by decide
@[simp] theorem sp_spE0_ne_lDh : spE0 ≠ lDh := by decide
@[simp] theorem sp_lDh_ne_spE0 : lDh ≠ spE0 := by decide
@[simp] theorem sp_spE0_ne_lDt : spE0 ≠ lDt := by decide
@[simp] theorem sp_lDt_ne_spE0 : lDt ≠ spE0 := by decide
@[simp] theorem sp_spE0_ne_lDg : spE0 ≠ lDg := by decide
@[simp] theorem sp_lDg_ne_spE0 : lDg ≠ spE0 := by decide
@[simp] theorem sp_spE0_ne_lDi : spE0 ≠ lDi := by decide
@[simp] theorem sp_lDi_ne_spE0 : lDi ≠ spE0 := by decide
@[simp] theorem sp_spE0_ne_lRp : spE0 ≠ lRp := by decide
@[simp] theorem sp_lRp_ne_spE0 : lRp ≠ spE0 := by decide
@[simp] theorem sp_spE0_ne_lRn : spE0 ≠ lRn := by decide
@[simp] theorem sp_lRn_ne_spE0 : lRn ≠ spE0 := by decide
@[simp] theorem sp_spE0_ne_lDir : spE0 ≠ lDir := by decide
@[simp] theorem sp_lDir_ne_spE0 : lDir ≠ spE0 := by decide
@[simp] theorem sp_spE0_ne_lFle : spE0 ≠ lFle := by decide
@[simp] theorem sp_lFle_ne_spE0 : lFle ≠ spE0 := by decide
@[simp] theorem sp_spE0_ne_lKb : spE0 ≠ lKb := by decide
@[simp] theorem sp_lKb_ne_spE0 : lKb ≠ spE0 := by decide
@[simp] theorem sp_spR_ne_spT : spR ≠ spT := by decide
@[simp] theorem sp_spR_ne_spA : spR ≠ spA := by decide
@[simp] theorem sp_spR_ne_spG : spR ≠ spG := by decide
@[simp] theorem sp_spR_ne_spI : spR ≠ spI := by decide
@[simp] theorem sp_spR_ne_spN : spR ≠ spN := by decide
@[simp] theorem sp_spR_ne_spX : spR ≠ spX := by decide
@[simp] theorem sp_spR_ne_spDm : spR ≠ spDm := by decide
@[simp] theorem sp_spR_ne_spB : spR ≠ spB := by decide
@[simp] theorem sp_spR_ne_spL : spR ≠ spL := by decide
@[simp] theorem sp_spR_ne_spO : spR ≠ spO := by decide
@[simp] theorem sp_spR_ne_spTa : spR ≠ spTa := by decide
@[simp] theorem sp_spR_ne_spQ : spR ≠ spQ := by decide
@[simp] theorem sp_spR_ne_spA2 : spR ≠ spA2 := by decide
@[simp] theorem sp_spR_ne_spW : spR ≠ spW := by decide
@[simp] theorem sp_spR_ne_spE0 : spR ≠ spE0 := by decide
@[simp] theorem sp_spR_ne_kFu : spR ≠ kFu := by decide
@[simp] theorem sp_kFu_ne_spR : kFu ≠ spR := by decide
@[simp] theorem sp_spR_ne_kD : spR ≠ kD := by decide
@[simp] theorem sp_kD_ne_spR : kD ≠ spR := by decide
@[simp] theorem sp_spR_ne_lFl : spR ≠ lFl := by decide
@[simp] theorem sp_lFl_ne_spR : lFl ≠ spR := by decide
@[simp] theorem sp_spR_ne_lDh : spR ≠ lDh := by decide
@[simp] theorem sp_lDh_ne_spR : lDh ≠ spR := by decide
@[simp] theorem sp_spR_ne_lDt : spR ≠ lDt := by decide
@[simp] theorem sp_lDt_ne_spR : lDt ≠ spR := by decide
@[simp] theorem sp_spR_ne_lDg : spR ≠ lDg := by decide
@[simp] theorem sp_lDg_ne_spR : lDg ≠ spR := by decide
@[simp] theorem sp_spR_ne_lDi : spR ≠ lDi := by decide
@[simp] theorem sp_lDi_ne_spR : lDi ≠ spR := by decide
@[simp] theorem sp_spR_ne_lRp : spR ≠ lRp := by decide
@[simp] theorem sp_lRp_ne_spR : lRp ≠ spR := by decide
@[simp] theorem sp_spR_ne_lRn : spR ≠ lRn := by decide
@[simp] theorem sp_lRn_ne_spR : lRn ≠ spR := by decide
@[simp] theorem sp_spR_ne_lDir : spR ≠ lDir := by decide
@[simp] theorem sp_lDir_ne_spR : lDir ≠ spR := by decide
@[simp] theorem sp_spR_ne_lFle : spR ≠ lFle := by decide
@[simp] theorem sp_lFle_ne_spR : lFle ≠ spR := by decide
@[simp] theorem sp_spR_ne_lKb : spR ≠ lKb := by decide
@[simp] theorem sp_lKb_ne_spR : lKb ≠ spR := by decide

def daParams : List MlS := [kFu, kD, daA, daT, daY]
def daLocals : List MlS := [daE, daQ]

def daBody : ProgHOL 64 := prologue daLocals
  (.seq (.call (some (some (.local, daE), none)) fIe [vv daA])
  (.ite (vv daE)
    (.seq (.call (some (some (.local, daQ), none)) fDE [vv kFu, vv kD, vv daT, vv daY]) (.return (vv daQ)))
    (.seq (.call (some (some (.local, daQ), none)) fD [vv kFu, vv kD, vv daT, vv daY]) (.return (vv daQ)))))

def spParams : List MlS := [kFu, kD, spT, spA, spG, spI, spN]
def spLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, spX, spDm, spB, spL, spO, spTa, spQ, spA2, spW, spE0,
  spR]

def spRec : ProgHOL 64 :=
  .seq (.call (some (some (.local, spR), none)) fSp
    [vv kFu, vv kD, vv spB, vv spA2, vv spG, .op .add [vv spI, .const 1], vv spN]) (.return (vv spR))

def spCore (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .lower (vv spI) (vv spN))
  (.seq (.assign .local spX (.load .one (.op .add [vv spG, .op .add [.panop .mul [vv spI, .const 8], .const 8]])))
  (.ite (tagIsE spT 6)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv spT)) (.seq eViewP
    (.seq (.assign .local spDm (.load .one (vv lRp)))
    (.seq (.assign .local spB (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.assign .local spL (.load .one (vv spA)))
    (.seq (.call (some (some (.local, spO), none)) ExQ.fIrr
        [vv spA, .const 0, vv spL, .const (BitVec.ofNat 64 coreWalkFuel), vv spDm, .const 0])
    (.seq (.call (some (some (.local, spTa), none)) fI [vv kFu, vv kD, vv spX])
    (.seq (.call (some (some (.local, spQ), none)) fDa [vv kFu, vv kD, vv spX, vv spTa, vv spO])
    (.ite (.cmp .equal (vv spQ) (.const 0)) hang
    (.seq (.call (some (some (.local, spA2), none)) ExPre.fAppend [vv spA, vv spX]) spRec)))))))))))
    (.seq (.assign .local spL (.load .one (vv spA)))
    (.seq (.call (some (some (.local, spO), none)) ExQ.fIrr
        [vv spA, .const 0, vv spL, .const (BitVec.ofNat 64 coreWalkFuel), vv spT, .const 0])
    (.seq (.call (some (some (.local, spW), none)) fW [vv kFu, vv kD, vv spO])
    (.ite (tagIsE spW 6)
      (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv spW)) (.seq eViewP
      (.seq (.assign .local spDm (.load .one (vv lRp)))
      (.seq (.assign .local spB (.load .one (.op .add [vv lRp, .const 8])))
      (.seq (.call (some (some (.local, spTa), none)) fI [vv kFu, vv kD, vv spX])
      (.seq (.call (some (some (.local, spQ), none)) fDa [vv kFu, vv kD, vv spX, vv spTa, vv spDm])
      (.ite (.cmp .equal (vv spQ) (.const 0)) hang
      (allocP C spE0 (.const 8) (.seq (.store (vv spE0) (.const 0))
      (.seq (.call (some (some (.local, spA2), none)) ExPre.fAppend [vv spE0, vv spX]) spRec)))))))))))
      hang))))))
  (.seq (.assign .local spL (.load .one (vv spA)))
  (.seq (.call (some (some (.local, spO), none)) ExQ.fIrr
      [vv spA, .const 0, vv spL, .const (BitVec.ofNat 64 coreWalkFuel), vv spT, .const 0])
    (.return (vv spO))))

def spBody (C : Ctx) : ProgHOL 64 := prologue spLocals (spCore C)

section
variable {σ : Type}

theorem da_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ daLocals → (ctxEnv C ++ daParams.zip vals).get x = none :=
  Knot.params_none C daLocals daParams vals (by decide) (by decide)

theorem da_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) (hok : CtxOK C)
    (hcie : C.code.lookup fIe = some (ieParams.map (fun p => (p, ShapeHOL.one)), ieBody C, .one))
    (hcd : C.code.lookup fD = some (pmap dParams, dE C, .one))
    (hcde : C.code.lookup fDE = some (pmap dParams, dEE C, .one))
    (hD : ∀ (H : List (BitVec 64)) s1 d' a b, C.H <+: H → Callee (σ := σ) (ctxH C H) dParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW a, Enc.idxW b] (dE C) s1 ((knot mode C n).defeq d' a b)
      (PostB (ctxH C H)))
    (hDE : ∀ (H : List (BitVec 64)) s1 d' a b, C.H <+: H → Callee (σ := σ) (ctxH C H) dParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW a, Enc.idxW b] (dEE C) s1 ((knot mode C n).defeqE d' a b)
      (PostB (ctxH C H)))
    (s : AState) (d : Nat) (a ta ty : EIdx) :
    SpecR (σ := σ) (Pre C s (daParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW ta,
      Enc.idxW ty])) daBody s (defeqArg (knot mode C n) d a ta ty) (PostB C) := by
  refine specR_prologue (postB_locals C) (da_none C _) ?_
  unfold defeqArg
  refine specR_callNIH (C := C) daE fIe ieParams [vv daA] (ieBody C) [Enc.idxW a] (by decide) rfl (by decide) hcie
    ⟨by simp +decide [Env.get, daParams, ctxEnv], trivial⟩ (PostB C) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ieParams _ rfl hlk) (ie_spec C hok s a))
    (fun b w s1 H1 hp1 hw => ?_)
  subst hw
  cases b
  · refine specR_ifI _ 0 (by simp [boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine specR_congr (m' := (knot mode C n).defeq d ta ty >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H1) daQ fD dParams [vv kFu, vv kD, vv daT, vv daY] (dE C)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ta, Enc.idxW ty] (by decide) rfl (by decide) hcd
      ⟨by simp +decide [Env.get, daParams, ctxEnv], by simp +decide [Env.get, daParams, ctxEnv], by simp +decide [Env.get, daParams, ctxEnv], by simp +decide [Env.get, daParams, ctxEnv], trivial⟩
      (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => hD H1 s1 d ta ty hp1 u hu (fun i hi _ => hlk i (by omega)))
      (fun q w s2 H2 hp2 hw => ?_)
    subst hw
    exact specR_returnI _ (boolW q) (by simp) (fun t ht => ⟨H2, hp1.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_ifI _ 1 (by simp [boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [↓reduceIte]
    refine specR_congr (m' := (knot mode C n).defeqE d ta ty >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H1) daQ fDE dParams [vv kFu, vv kD, vv daT, vv daY] (dEE C)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ta, Enc.idxW ty] (by decide) rfl (by decide) hcde
      ⟨by simp +decide [Env.get, daParams, ctxEnv], by simp +decide [Env.get, daParams, ctxEnv], by simp +decide [Env.get, daParams, ctxEnv], by simp +decide [Env.get, daParams, ctxEnv], trivial⟩
      (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => hDE H1 s1 d ta ty hp1 u hu (fun i hi _ => hlk i (by omega)))
      (fun q w s2 H2 hp2 hw => ?_)
    subst hw
    exact specR_returnI _ (boolW q) (by simp) (fun t ht => ⟨H2, hp1.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem sp_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ spLocals → (ctxEnv C ++ spParams.zip vals).get x = none :=
  Knot.params_none C spLocals spParams vals (by decide) (by decide)

structure SpCodes (C : Ctx) : Prop where
  i : C.code.lookup fI = some (pmap kParams, inferE C fIB, .one)
  w : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one)
  irr : C.code.lookup ExQ.fIrr = some (ExQ.irrParams.map (fun p => (p, ShapeHOL.one)), ExQ.irrBody C, .one)
  q : ExQ.CodesQ C
  ie : C.code.lookup fIe = some (ieParams.map (fun p => (p, ShapeHOL.one)), ieBody C, .one)
  d : C.code.lookup fD = some (pmap dParams, dE C, .one)
  de : C.code.lookup fDE = some (pmap dParams, dEE C, .one)
  da : C.code.lookup fDa = some (daParams.map (fun p => (p, ShapeHOL.one)), daBody, .one)
  app : C.code.lookup ExPre.fAppend = some (ExPre.appParams.map (fun p => (p, ShapeHOL.one)), ExPre.appBody C, .one)
  self : C.code.lookup fSp = some (spParams.map (fun p => (p, ShapeHOL.one)), spBody C, .one)

theorem sp_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (hc : SpCodes C)
    (hI : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (inferE C fIB) s1 ((knot mode C n).infer d' e')
      (PostK (ctxH C H)))
    (hW : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d' e')
      (PostK (ctxH C H)))
    (hD : ∀ (H : List (BitVec 64)) s1 d' a b, C.H <+: H → Callee (σ := σ) (ctxH C H) dParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW a, Enc.idxW b] (dE C) s1 ((knot mode C n).defeq d' a b)
      (PostB (ctxH C H)))
    (hDE : ∀ (H : List (BitVec 64)) s1 d' a b, C.H <+: H → Callee (σ := σ) (ctxH C H) dParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW a, Enc.idxW b] (dEE C) s1 ((knot mode C n).defeqE d' a b)
      (PostB (ctxH C H)))
    (d : Nat) (args : List EIdx) (og : Nat) (H0 : List (BitVec 64)) (hp0 : C.H <+: H0)
    (hga : BlkAt H0 og (args.map Enc.idxW)) (hsz : args.length < 2 ^ 58) :
    ∀ m (ty : EIdx) (acc : List EIdx) (oa i : Nat) (H : List (BitVec 64)) (s : AState), H0 <+: H →
      BlkAt H oa (acc.map Enc.idxW) → acc.length ≤ i → args.length - i = m → i ≤ args.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (spParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty, cellA C oa,
        cellA C og, BitVec.ofNat 64 i, BitVec.ofNat 64 args.length])) (spBody C) s
        (inferSpine (knot mode C n) C.fe d ty acc.toArray args.toArray i) (PostK (ctxH C H)) := by
  intro m
  induction m with
  | zero =>
    intro ty acc oa i H s hp hba hai hk hi
    refine specR_prologue (postK_locals _) (sp_none _ _) ?_
    unfold spCore
    rw [inferSpine, dif_neg (by simp; omega)]
    have hlw := word_lt_iff i args.length (by unfold B; omega) (by unfold B; omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, spParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
      (not_congr hlw).mpr (by omega)]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_congr (m' := instantiateListFast coreWalkFuel ty acc.toArray 0 >>= fun r => pure r) (by simp) ?_
    obtain ⟨hlo, hlv0⟩ := blkAt_get0 hba
    refine UD.specR_heapLoadI' (C := ctxH C H) spL (vv spA) oa (BitVec.ofNat 64 acc.length)
      (by show H[oa]? = _; rw [List.getElem?_eq_getElem hlo, hlv0]; simp) (by decide) (by simp +decide [Env.get, spParams, ctxEnv] <;> rfl) ?_
    simp only [instantiateListFast, List.size_toArray, bind_assoc]
    refine ILP.callE_spec (C := ctxH C H) spO ExQ.fIrr ExQ.irrParams
      [vv spA, .const 0, vv spL, .const (BitVec.ofNat 64 coreWalkFuel), vv spT, .const 0] (ExQ.irrBody C)
      [cellA C oa, BitVec.ofNat 64 0, BitVec.ofNat 64 acc.length, BitVec.ofNat 64 coreWalkFuel, Enc.idxW ty,
        BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.irr
      ⟨by simp +decide [Env.get, spParams, ctxEnv] <;> rfl, rfl, by simp, rfl, by simp +decide [Env.get, spParams, ctxEnv], rfl, trivial⟩
      (ExQ.irr_spec ra (ctxH C H) (ctxOK_H hok H) (codesQ_H hc.q H) acc.toArray oa
        (show BlkAt H oa (acc.toArray.toList.map Enc.idxW) by simpa using hba) (by simp; omega) s
        coreWalkFuel 0 acc.length 0 ty CV.coreWalkFuel_lt (by decide) (by omega) (by decide)) (fun r s1 => ?_)
    exact specR_returnI _ (Enc.idxW r) (by simp)
      (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ m ih =>
    intro ty acc oa i H s hp hba hai hk hi
    have hlt : i < args.length := by omega
    refine specR_prologue (postK_locals _) (sp_none _ _) ?_
    unfold spCore
    rw [inferSpine, dif_pos (by simpa using hlt)]
    have hlw := word_lt_iff i args.length (by unfold B; omega) (by unfold B; omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, spParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
      hlw.mpr hlt]) (fun _ => ?_) (fun h => absurd h (by decide))
    have hga' := blkAt_mono hga hp
    have hxi : (ctxH C H).H[og + 1 + i]? = some (Enc.idxW args[i]) := by
      have := hga'.2 i (by simp; omega); simp at this; exact this
    refine UD.specR_heapLoadI' (C := ctxH C H) spX _ (og + 1 + i) _ hxi (by decide)
      (by simp +decide [sev, Env.get, spParams, ctxEnv]; exact cellA_idx C og i) ?_
    simp only [List.getElem_toArray]
    refine Knot.specR_tagIteV spT ty 6 (by decide) (by decide) (by simp +decide [Env.get, spParams, ctxEnv]) (fun htg => ?_) (fun htg => ?_)
    · rw [if_pos (show (ty.tag == ETag.forallE) = true by simp [htg, ETag.forallE])]
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv spT) (Enc.idxW ty) (by decide) (by simp +decide [Env.get, spParams, ctxEnv]) ?_
      refine specR_viewP (C := ctxH C H) ty (by simp) (by simp +decide [Env.get] <;> rfl)
        (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
      have h6 : v.tagN = 6 := by rw [htn, htg]; rfl
      obtain ⟨dom, b, rfl⟩ : ∃ dom b, v = .forallE dom b := by cases v <;> simp [ENodeView.tagN] at h6 ⊢
      have hvb : s.store.viewBind ty = some (dom, b) := viewBind_of_view_forallE (by rw [htg]; rfl) hv
      refine specR_runBind (by rw [viewBind_run, hvb]) ?_
      dsimp only
      refine specR_loadI' spDm (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW dom) (by decide) (by simp) (by simp)
        (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW dom) [Enc.idxW b] []) ?_
      refine specR_loadI' spB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW dom) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      obtain ⟨hlo, hlv0⟩ := blkAt_get0 hba
      refine UD.specR_heapLoadI' (C := ctxH C H) spL (vv spA) oa (BitVec.ofNat 64 acc.length)
        (by show H[oa]? = _; rw [List.getElem?_eq_getElem hlo, hlv0]; simp) (by decide) (by simp +decide [Env.get, spParams, ctxEnv] <;> rfl) ?_
      simp only [instantiateListFast, List.size_toArray, bind_assoc]
      refine ILP.callE_spec (C := ctxH C H) spO ExQ.fIrr ExQ.irrParams
        [vv spA, .const 0, vv spL, .const (BitVec.ofNat 64 coreWalkFuel), vv spDm, .const 0] (ExQ.irrBody C)
        [cellA C oa, BitVec.ofNat 64 0, BitVec.ofNat 64 acc.length, BitVec.ofNat 64 coreWalkFuel, Enc.idxW dom,
          BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.irr
        ⟨by simp +decide [Env.get, spParams, ctxEnv] <;> rfl, rfl, by simp, rfl, by simp +decide [Env.get, spParams, ctxEnv], rfl, trivial⟩
        (ExQ.irr_spec ra (ctxH C H) (ctxOK_H hok H) (codesQ_H hc.q H) acc.toArray oa
          (show BlkAt H oa (acc.toArray.toList.map Enc.idxW) by simpa using hba) (by simp; omega) s
          coreWalkFuel 0 acc.length 0 dom CV.coreWalkFuel_lt (by decide) (by omega) (by decide)) (fun dom2 s1 => ?_)
      refine Big.specR_callKC (C := ctxH C H) spTa fI kParams [vv kFu, vv kD, vv spX] (inferE C fIB)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW args[i]] (by decide) rfl (by decide) hc.i
        ⟨by simp +decide [Env.get, spParams, ctxEnv], by simp +decide [Env.get, spParams, ctxEnv], by simp, trivial⟩ (hI H s1 d args[i] (hp0.trans hp)) (fun ta s2 H2 hp2 _ => ?_)
      refine specR_callNIH (C := ctxH C H2) spQ fDa daParams [vv kFu, vv kD, vv spX, vv spTa, vv spO] daBody
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW args[i], Enc.idxW ta, Enc.idxW dom2] (by decide) rfl
        (by decide) hc.da ⟨by simp +decide [Env.get, spParams, ctxEnv], by simp +decide [Env.get, spParams, ctxEnv], by simp, by simp, by simp, trivial⟩
        (PostB (ctxH C H2)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu daParams _ rfl hlk)
          (da_spec mode n (ctxH C H2) (ctxOK_H hok H2) hc.ie hc.d hc.de
            (fun H' s1 d' a b hp' => hD H' s1 d' a b ((hp0.trans (hp.trans hp2)).trans hp'))
            (fun H' s1 d' a b hp' => hDE H' s1 d' a b ((hp0.trans (hp.trans hp2)).trans hp')) s2 d args[i] ta dom2))
        (fun q w s3 H3 hp3 hw => ?_)
      subst hw
      cases q
      · simp only [Bool.not_false, ↓reduceIte]
        exact specR_ifI _ 1 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI)
          (fun h => absurd h (by decide))
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine specR_ifI _ 0 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
        (fun _ => ?_)
      have hp03 : H <+: H3 := hp2.trans hp3
      refine ExPre.specR_callApp (C := ctxH C H3) (ctxOK_H hok H3) hc.app spA2 (vv spA) (vv spX) oa
        (acc.map Enc.idxW) (Enc.idxW args[i]) (by decide) (blkAt_mono hba hp03) (by simp +decide [Env.get, spParams, ctxEnv] <;> rfl) (by simp)
        (fun H4 o4 hp4 hb4 => ?_)
      have hb4' : BlkAt H4 o4 ((acc ++ [args[i]]).map Enc.idxW) := by simpa using hb4
      have hpall : H <+: H4 := hp03.trans hp4
      rw [show acc.toArray.push args[i] = (acc ++ [args[i]]).toArray by simp]
      unfold spRec
      refine specR_congr (m' := inferSpine (knot mode C n) C.fe d b (acc ++ [args[i]]).toArray args.toArray (i + 1)
        >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H4) spR fSp spParams
        [vv kFu, vv kD, vv spB, vv spA2, vv spG, .op .add [vv spI, .const 1], vv spN] (spBody C)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW b, cellA C o4, cellA C og, BitVec.ofNat 64 (i + 1),
          BitVec.ofNat 64 args.length] (by decide) rfl (by decide) hc.self
        ⟨by simp +decide [Env.get, spParams, ctxEnv], by simp +decide [Env.get, spParams, ctxEnv], by simp, by simp <;> rfl, by simp +decide [Env.get, spParams, ctxEnv] <;> rfl,
          by simp +decide [sev, Env.get, spParams, ctxEnv]; exact word_add1_eq i, by simp +decide [Env.get, spParams, ctxEnv], trivial⟩
        (PostK (ctxH C H4)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu spParams _ rfl hlk)
          (ih b (acc ++ [args[i]]) o4 (i + 1) H4 s3 (hp.trans hpall) hb4' (by simp; omega) (by omega) (by omega)))
        (fun r w s9 H9 hp9 hw => ?_)
      subst hw
      exact specR_returnI _ (Enc.idxW r) (by simp)
        (fun t ht => ⟨H9, hpall.trans hp9, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · rw [if_neg (show ¬ (ty.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg)]
      obtain ⟨hlo, hlv0⟩ := blkAt_get0 hba
      refine UD.specR_heapLoadI' (C := ctxH C H) spL (vv spA) oa (BitVec.ofNat 64 acc.length)
        (by show H[oa]? = _; rw [List.getElem?_eq_getElem hlo, hlv0]; simp) (by decide) (by simp +decide [Env.get, spParams, ctxEnv] <;> rfl) ?_
      simp only [instantiateListFast, List.size_toArray, bind_assoc]
      refine ILP.callE_spec (C := ctxH C H) spO ExQ.fIrr ExQ.irrParams
        [vv spA, .const 0, vv spL, .const (BitVec.ofNat 64 coreWalkFuel), vv spT, .const 0] (ExQ.irrBody C)
        [cellA C oa, BitVec.ofNat 64 0, BitVec.ofNat 64 acc.length, BitVec.ofNat 64 coreWalkFuel, Enc.idxW ty,
          BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.irr
        ⟨by simp +decide [Env.get, spParams, ctxEnv] <;> rfl, rfl, by simp, rfl, by simp +decide [Env.get, spParams, ctxEnv], rfl, trivial⟩
        (ExQ.irr_spec ra (ctxH C H) (ctxOK_H hok H) (codesQ_H hc.q H) acc.toArray oa
          (show BlkAt H oa (acc.toArray.toList.map Enc.idxW) by simpa using hba) (by simp; omega) s
          coreWalkFuel 0 acc.length 0 ty CV.coreWalkFuel_lt (by decide) (by omega) (by decide)) (fun ty2 s1 => ?_)
      refine Big.specR_callKC (C := ctxH C H) spW fW kParams [vv kFu, vv kD, vv spO] (whnfE C fWB)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty2] (by decide) rfl (by decide) hc.w
        ⟨by simp +decide [Env.get, spParams, ctxEnv], by simp +decide [Env.get, spParams, ctxEnv], by simp, trivial⟩ (hW H s1 d ty2 (hp0.trans hp)) (fun w s2 H2 hp2 _ => ?_)
      refine Knot.specR_tagIteV spW w 6 (by decide) (by decide) (by simp) (fun htg2 => ?_) (fun htg2 => ?_)
      swap
      · rw [if_neg (show ¬ (w.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg2)]
        exact specR_hangI
      rw [if_pos (show (w.tag == ETag.forallE) = true by simp [htg2, ETag.forallE])]
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv spW) (Enc.idxW w) (by decide) (by simp) ?_
      refine specR_viewP (C := ctxH C H2) w (by simp) (by simp +decide [Env.get] <;> rfl)
        (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
      have h6 : v.tagN = 6 := by rw [htn, htg2]; rfl
      obtain ⟨dom, b, rfl⟩ : ∃ dom b, v = .forallE dom b := by cases v <;> simp [ENodeView.tagN] at h6 ⊢
      have hvb : s2.store.viewBind w = some (dom, b) := viewBind_of_view_forallE (by rw [htg2]; rfl) hv
      refine specR_runBind (by rw [viewBind_run, hvb]) ?_
      dsimp only
      refine specR_loadI' spDm (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW dom) (by decide) (by simp) (by simp)
        (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW dom) [Enc.idxW b] []) ?_
      refine specR_loadI' spB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW dom) (Enc.idxW b) [] []) ?_
      refine specR_dropM ?_
      refine Big.specR_callKC (C := ctxH C H2) spTa fI kParams [vv kFu, vv kD, vv spX] (inferE C fIB)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW args[i]] (by decide) rfl (by decide) hc.i
        ⟨by simp +decide [Env.get, spParams, ctxEnv], by simp +decide [Env.get, spParams, ctxEnv], by simp, trivial⟩ (hI H2 s2 d args[i] (hp0.trans (hp.trans hp2))) (fun ta s3 H3 hp3 _ => ?_)
      refine specR_callNIH (C := ctxH C H3) spQ fDa daParams [vv kFu, vv kD, vv spX, vv spTa, vv spDm] daBody
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW args[i], Enc.idxW ta, Enc.idxW dom] (by decide) rfl
        (by decide) hc.da ⟨by simp +decide [Env.get, spParams, ctxEnv], by simp +decide [Env.get, spParams, ctxEnv], by simp, by simp, by simp, trivial⟩
        (PostB (ctxH C H3)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu daParams _ rfl hlk)
          (da_spec mode n (ctxH C H3) (ctxOK_H hok H3) hc.ie hc.d hc.de
            (fun H' s1 d' a b hp' => hD H' s1 d' a b ((hp0.trans (hp.trans (hp2.trans hp3))).trans hp'))
            (fun H' s1 d' a b hp' => hDE H' s1 d' a b ((hp0.trans (hp.trans (hp2.trans hp3))).trans hp')) s3 d args[i] ta dom))
        (fun q w s4 H4 hp4 hw => ?_)
      subst hw
      cases q
      · simp only [Bool.not_false, ↓reduceIte]
        exact specR_ifI _ 1 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI)
          (fun h => absurd h (by decide))
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      refine specR_ifI _ 0 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
        (fun _ => ?_)
      refine specR_emptyBlk (C0 := C) hok (H := H4) spE0 (by decide) (fun H5 oe hp5 hbe => ?_)
      refine ExPre.specR_callApp (C := ctxH C H5) (ctxOK_H hok H5) hc.app spA2 (vv spE0) (vv spX) oe
        [] (Enc.idxW args[i]) (by decide) hbe (by simp <;> rfl) (by simp) (fun H6 o6 hp6 hb6 => ?_)
      have hb6' : BlkAt H6 o6 ([args[i]].map Enc.idxW) := by simpa using hb6
      have hpall : H <+: H6 := hp2.trans (hp3.trans (hp4.trans (hp5.trans hp6)))
      unfold spRec
      refine specR_congr (m' := inferSpine (knot mode C n) C.fe d b [args[i]].toArray args.toArray (i + 1)
        >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H6) spR fSp spParams
        [vv kFu, vv kD, vv spB, vv spA2, vv spG, .op .add [vv spI, .const 1], vv spN] (spBody C)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW b, cellA C o6, cellA C og, BitVec.ofNat 64 (i + 1),
          BitVec.ofNat 64 args.length] (by decide) rfl (by decide) hc.self
        ⟨by simp +decide [Env.get, spParams, ctxEnv], by simp +decide [Env.get, spParams, ctxEnv], by simp, by simp <;> rfl, by simp +decide [Env.get, spParams, ctxEnv] <;> rfl,
          by simp +decide [sev, Env.get, spParams, ctxEnv]; exact word_add1_eq i, by simp +decide [Env.get, spParams, ctxEnv], trivial⟩
        (PostK (ctxH C H6)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu spParams _ rfl hlk)
          (ih b [args[i]] o6 (i + 1) H6 s4 (hp.trans hpall) hb6' (by simp <;> omega) (by omega) (by omega)))
        (fun r w s9 H9 hp9 hw => ?_)
      subst hw
      exact specR_returnI _ (Enc.idxW r) (by simp)
        (fun t ht => ⟨H9, hpall.trans hp9, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
