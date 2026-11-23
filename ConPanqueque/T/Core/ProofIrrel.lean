import ConPanqueque.T.Core.PrepMajor
import ConPanqueque.T.LvlEqQ
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `proofIrrel`: are two terms proofs (their types' types are `Prop`)

Each side's type's type, head-normalized, must be a sort whose level is equal to zero (`lvlEq?`, a fuel decline
when it runs out). The inferences are the knot's io-grade entry.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def piA := ofString "pia"
def piB := ofString "pib"
def piTa := ofString "pita"
def piT2 := ofString "pit2"
def piH := ofString "pih"
def piU := ofString "piu"
def piZ := ofString "piz"
def piQ := ofString "piq"
def piOa := ofString "pioa"
def piTb := ofString "pitb"
def piT3 := ofString "pit3"
def piH2 := ofString "pih2"
def piV := ofString "piv"
def piQ2 := ofString "piq2"
def fPi := ofString "proofIrrel"

@[simp] theorem pi_piA_ne_piB : piA ≠ piB := by decide
@[simp] theorem pi_piA_ne_piTa : piA ≠ piTa := by decide
@[simp] theorem pi_piA_ne_piT2 : piA ≠ piT2 := by decide
@[simp] theorem pi_piA_ne_piH : piA ≠ piH := by decide
@[simp] theorem pi_piA_ne_piU : piA ≠ piU := by decide
@[simp] theorem pi_piA_ne_piZ : piA ≠ piZ := by decide
@[simp] theorem pi_piA_ne_piQ : piA ≠ piQ := by decide
@[simp] theorem pi_piA_ne_piOa : piA ≠ piOa := by decide
@[simp] theorem pi_piA_ne_piTb : piA ≠ piTb := by decide
@[simp] theorem pi_piA_ne_piT3 : piA ≠ piT3 := by decide
@[simp] theorem pi_piA_ne_piH2 : piA ≠ piH2 := by decide
@[simp] theorem pi_piA_ne_piV : piA ≠ piV := by decide
@[simp] theorem pi_piA_ne_piQ2 : piA ≠ piQ2 := by decide
@[simp] theorem pi_piA_ne_lFl : piA ≠ lFl := by decide
@[simp] theorem pi_lFl_ne_piA : lFl ≠ piA := by decide
@[simp] theorem pi_piA_ne_lDh : piA ≠ lDh := by decide
@[simp] theorem pi_lDh_ne_piA : lDh ≠ piA := by decide
@[simp] theorem pi_piA_ne_lDt : piA ≠ lDt := by decide
@[simp] theorem pi_lDt_ne_piA : lDt ≠ piA := by decide
@[simp] theorem pi_piA_ne_lDg : piA ≠ lDg := by decide
@[simp] theorem pi_lDg_ne_piA : lDg ≠ piA := by decide
@[simp] theorem pi_piA_ne_lDi : piA ≠ lDi := by decide
@[simp] theorem pi_lDi_ne_piA : lDi ≠ piA := by decide
@[simp] theorem pi_piA_ne_lRp : piA ≠ lRp := by decide
@[simp] theorem pi_lRp_ne_piA : lRp ≠ piA := by decide
@[simp] theorem pi_piA_ne_lRn : piA ≠ lRn := by decide
@[simp] theorem pi_lRn_ne_piA : lRn ≠ piA := by decide
@[simp] theorem pi_piA_ne_lFle : piA ≠ lFle := by decide
@[simp] theorem pi_lFle_ne_piA : lFle ≠ piA := by decide
@[simp] theorem pi_piA_ne_lDir : piA ≠ lDir := by decide
@[simp] theorem pi_lDir_ne_piA : lDir ≠ piA := by decide
@[simp] theorem pi_piA_ne_lKb : piA ≠ lKb := by decide
@[simp] theorem pi_lKb_ne_piA : lKb ≠ piA := by decide
@[simp] theorem pi_piA_ne_kFu : piA ≠ kFu := by decide
@[simp] theorem pi_kFu_ne_piA : kFu ≠ piA := by decide
@[simp] theorem pi_piA_ne_kD : piA ≠ kD := by decide
@[simp] theorem pi_kD_ne_piA : kD ≠ piA := by decide
@[simp] theorem pi_piB_ne_piA : piB ≠ piA := by decide
@[simp] theorem pi_piB_ne_piTa : piB ≠ piTa := by decide
@[simp] theorem pi_piB_ne_piT2 : piB ≠ piT2 := by decide
@[simp] theorem pi_piB_ne_piH : piB ≠ piH := by decide
@[simp] theorem pi_piB_ne_piU : piB ≠ piU := by decide
@[simp] theorem pi_piB_ne_piZ : piB ≠ piZ := by decide
@[simp] theorem pi_piB_ne_piQ : piB ≠ piQ := by decide
@[simp] theorem pi_piB_ne_piOa : piB ≠ piOa := by decide
@[simp] theorem pi_piB_ne_piTb : piB ≠ piTb := by decide
@[simp] theorem pi_piB_ne_piT3 : piB ≠ piT3 := by decide
@[simp] theorem pi_piB_ne_piH2 : piB ≠ piH2 := by decide
@[simp] theorem pi_piB_ne_piV : piB ≠ piV := by decide
@[simp] theorem pi_piB_ne_piQ2 : piB ≠ piQ2 := by decide
@[simp] theorem pi_piB_ne_lFl : piB ≠ lFl := by decide
@[simp] theorem pi_lFl_ne_piB : lFl ≠ piB := by decide
@[simp] theorem pi_piB_ne_lDh : piB ≠ lDh := by decide
@[simp] theorem pi_lDh_ne_piB : lDh ≠ piB := by decide
@[simp] theorem pi_piB_ne_lDt : piB ≠ lDt := by decide
@[simp] theorem pi_lDt_ne_piB : lDt ≠ piB := by decide
@[simp] theorem pi_piB_ne_lDg : piB ≠ lDg := by decide
@[simp] theorem pi_lDg_ne_piB : lDg ≠ piB := by decide
@[simp] theorem pi_piB_ne_lDi : piB ≠ lDi := by decide
@[simp] theorem pi_lDi_ne_piB : lDi ≠ piB := by decide
@[simp] theorem pi_piB_ne_lRp : piB ≠ lRp := by decide
@[simp] theorem pi_lRp_ne_piB : lRp ≠ piB := by decide
@[simp] theorem pi_piB_ne_lRn : piB ≠ lRn := by decide
@[simp] theorem pi_lRn_ne_piB : lRn ≠ piB := by decide
@[simp] theorem pi_piB_ne_lFle : piB ≠ lFle := by decide
@[simp] theorem pi_lFle_ne_piB : lFle ≠ piB := by decide
@[simp] theorem pi_piB_ne_lDir : piB ≠ lDir := by decide
@[simp] theorem pi_lDir_ne_piB : lDir ≠ piB := by decide
@[simp] theorem pi_piB_ne_lKb : piB ≠ lKb := by decide
@[simp] theorem pi_lKb_ne_piB : lKb ≠ piB := by decide
@[simp] theorem pi_piB_ne_kFu : piB ≠ kFu := by decide
@[simp] theorem pi_kFu_ne_piB : kFu ≠ piB := by decide
@[simp] theorem pi_piB_ne_kD : piB ≠ kD := by decide
@[simp] theorem pi_kD_ne_piB : kD ≠ piB := by decide
@[simp] theorem pi_piTa_ne_piA : piTa ≠ piA := by decide
@[simp] theorem pi_piTa_ne_piB : piTa ≠ piB := by decide
@[simp] theorem pi_piTa_ne_piT2 : piTa ≠ piT2 := by decide
@[simp] theorem pi_piTa_ne_piH : piTa ≠ piH := by decide
@[simp] theorem pi_piTa_ne_piU : piTa ≠ piU := by decide
@[simp] theorem pi_piTa_ne_piZ : piTa ≠ piZ := by decide
@[simp] theorem pi_piTa_ne_piQ : piTa ≠ piQ := by decide
@[simp] theorem pi_piTa_ne_piOa : piTa ≠ piOa := by decide
@[simp] theorem pi_piTa_ne_piTb : piTa ≠ piTb := by decide
@[simp] theorem pi_piTa_ne_piT3 : piTa ≠ piT3 := by decide
@[simp] theorem pi_piTa_ne_piH2 : piTa ≠ piH2 := by decide
@[simp] theorem pi_piTa_ne_piV : piTa ≠ piV := by decide
@[simp] theorem pi_piTa_ne_piQ2 : piTa ≠ piQ2 := by decide
@[simp] theorem pi_piTa_ne_lFl : piTa ≠ lFl := by decide
@[simp] theorem pi_lFl_ne_piTa : lFl ≠ piTa := by decide
@[simp] theorem pi_piTa_ne_lDh : piTa ≠ lDh := by decide
@[simp] theorem pi_lDh_ne_piTa : lDh ≠ piTa := by decide
@[simp] theorem pi_piTa_ne_lDt : piTa ≠ lDt := by decide
@[simp] theorem pi_lDt_ne_piTa : lDt ≠ piTa := by decide
@[simp] theorem pi_piTa_ne_lDg : piTa ≠ lDg := by decide
@[simp] theorem pi_lDg_ne_piTa : lDg ≠ piTa := by decide
@[simp] theorem pi_piTa_ne_lDi : piTa ≠ lDi := by decide
@[simp] theorem pi_lDi_ne_piTa : lDi ≠ piTa := by decide
@[simp] theorem pi_piTa_ne_lRp : piTa ≠ lRp := by decide
@[simp] theorem pi_lRp_ne_piTa : lRp ≠ piTa := by decide
@[simp] theorem pi_piTa_ne_lRn : piTa ≠ lRn := by decide
@[simp] theorem pi_lRn_ne_piTa : lRn ≠ piTa := by decide
@[simp] theorem pi_piTa_ne_lFle : piTa ≠ lFle := by decide
@[simp] theorem pi_lFle_ne_piTa : lFle ≠ piTa := by decide
@[simp] theorem pi_piTa_ne_lDir : piTa ≠ lDir := by decide
@[simp] theorem pi_lDir_ne_piTa : lDir ≠ piTa := by decide
@[simp] theorem pi_piTa_ne_lKb : piTa ≠ lKb := by decide
@[simp] theorem pi_lKb_ne_piTa : lKb ≠ piTa := by decide
@[simp] theorem pi_piTa_ne_kFu : piTa ≠ kFu := by decide
@[simp] theorem pi_kFu_ne_piTa : kFu ≠ piTa := by decide
@[simp] theorem pi_piTa_ne_kD : piTa ≠ kD := by decide
@[simp] theorem pi_kD_ne_piTa : kD ≠ piTa := by decide
@[simp] theorem pi_piT2_ne_piA : piT2 ≠ piA := by decide
@[simp] theorem pi_piT2_ne_piB : piT2 ≠ piB := by decide
@[simp] theorem pi_piT2_ne_piTa : piT2 ≠ piTa := by decide
@[simp] theorem pi_piT2_ne_piH : piT2 ≠ piH := by decide
@[simp] theorem pi_piT2_ne_piU : piT2 ≠ piU := by decide
@[simp] theorem pi_piT2_ne_piZ : piT2 ≠ piZ := by decide
@[simp] theorem pi_piT2_ne_piQ : piT2 ≠ piQ := by decide
@[simp] theorem pi_piT2_ne_piOa : piT2 ≠ piOa := by decide
@[simp] theorem pi_piT2_ne_piTb : piT2 ≠ piTb := by decide
@[simp] theorem pi_piT2_ne_piT3 : piT2 ≠ piT3 := by decide
@[simp] theorem pi_piT2_ne_piH2 : piT2 ≠ piH2 := by decide
@[simp] theorem pi_piT2_ne_piV : piT2 ≠ piV := by decide
@[simp] theorem pi_piT2_ne_piQ2 : piT2 ≠ piQ2 := by decide
@[simp] theorem pi_piT2_ne_lFl : piT2 ≠ lFl := by decide
@[simp] theorem pi_lFl_ne_piT2 : lFl ≠ piT2 := by decide
@[simp] theorem pi_piT2_ne_lDh : piT2 ≠ lDh := by decide
@[simp] theorem pi_lDh_ne_piT2 : lDh ≠ piT2 := by decide
@[simp] theorem pi_piT2_ne_lDt : piT2 ≠ lDt := by decide
@[simp] theorem pi_lDt_ne_piT2 : lDt ≠ piT2 := by decide
@[simp] theorem pi_piT2_ne_lDg : piT2 ≠ lDg := by decide
@[simp] theorem pi_lDg_ne_piT2 : lDg ≠ piT2 := by decide
@[simp] theorem pi_piT2_ne_lDi : piT2 ≠ lDi := by decide
@[simp] theorem pi_lDi_ne_piT2 : lDi ≠ piT2 := by decide
@[simp] theorem pi_piT2_ne_lRp : piT2 ≠ lRp := by decide
@[simp] theorem pi_lRp_ne_piT2 : lRp ≠ piT2 := by decide
@[simp] theorem pi_piT2_ne_lRn : piT2 ≠ lRn := by decide
@[simp] theorem pi_lRn_ne_piT2 : lRn ≠ piT2 := by decide
@[simp] theorem pi_piT2_ne_lFle : piT2 ≠ lFle := by decide
@[simp] theorem pi_lFle_ne_piT2 : lFle ≠ piT2 := by decide
@[simp] theorem pi_piT2_ne_lDir : piT2 ≠ lDir := by decide
@[simp] theorem pi_lDir_ne_piT2 : lDir ≠ piT2 := by decide
@[simp] theorem pi_piT2_ne_lKb : piT2 ≠ lKb := by decide
@[simp] theorem pi_lKb_ne_piT2 : lKb ≠ piT2 := by decide
@[simp] theorem pi_piT2_ne_kFu : piT2 ≠ kFu := by decide
@[simp] theorem pi_kFu_ne_piT2 : kFu ≠ piT2 := by decide
@[simp] theorem pi_piT2_ne_kD : piT2 ≠ kD := by decide
@[simp] theorem pi_kD_ne_piT2 : kD ≠ piT2 := by decide
@[simp] theorem pi_piH_ne_piA : piH ≠ piA := by decide
@[simp] theorem pi_piH_ne_piB : piH ≠ piB := by decide
@[simp] theorem pi_piH_ne_piTa : piH ≠ piTa := by decide
@[simp] theorem pi_piH_ne_piT2 : piH ≠ piT2 := by decide
@[simp] theorem pi_piH_ne_piU : piH ≠ piU := by decide
@[simp] theorem pi_piH_ne_piZ : piH ≠ piZ := by decide
@[simp] theorem pi_piH_ne_piQ : piH ≠ piQ := by decide
@[simp] theorem pi_piH_ne_piOa : piH ≠ piOa := by decide
@[simp] theorem pi_piH_ne_piTb : piH ≠ piTb := by decide
@[simp] theorem pi_piH_ne_piT3 : piH ≠ piT3 := by decide
@[simp] theorem pi_piH_ne_piH2 : piH ≠ piH2 := by decide
@[simp] theorem pi_piH_ne_piV : piH ≠ piV := by decide
@[simp] theorem pi_piH_ne_piQ2 : piH ≠ piQ2 := by decide
@[simp] theorem pi_piH_ne_lFl : piH ≠ lFl := by decide
@[simp] theorem pi_lFl_ne_piH : lFl ≠ piH := by decide
@[simp] theorem pi_piH_ne_lDh : piH ≠ lDh := by decide
@[simp] theorem pi_lDh_ne_piH : lDh ≠ piH := by decide
@[simp] theorem pi_piH_ne_lDt : piH ≠ lDt := by decide
@[simp] theorem pi_lDt_ne_piH : lDt ≠ piH := by decide
@[simp] theorem pi_piH_ne_lDg : piH ≠ lDg := by decide
@[simp] theorem pi_lDg_ne_piH : lDg ≠ piH := by decide
@[simp] theorem pi_piH_ne_lDi : piH ≠ lDi := by decide
@[simp] theorem pi_lDi_ne_piH : lDi ≠ piH := by decide
@[simp] theorem pi_piH_ne_lRp : piH ≠ lRp := by decide
@[simp] theorem pi_lRp_ne_piH : lRp ≠ piH := by decide
@[simp] theorem pi_piH_ne_lRn : piH ≠ lRn := by decide
@[simp] theorem pi_lRn_ne_piH : lRn ≠ piH := by decide
@[simp] theorem pi_piH_ne_lFle : piH ≠ lFle := by decide
@[simp] theorem pi_lFle_ne_piH : lFle ≠ piH := by decide
@[simp] theorem pi_piH_ne_lDir : piH ≠ lDir := by decide
@[simp] theorem pi_lDir_ne_piH : lDir ≠ piH := by decide
@[simp] theorem pi_piH_ne_lKb : piH ≠ lKb := by decide
@[simp] theorem pi_lKb_ne_piH : lKb ≠ piH := by decide
@[simp] theorem pi_piH_ne_kFu : piH ≠ kFu := by decide
@[simp] theorem pi_kFu_ne_piH : kFu ≠ piH := by decide
@[simp] theorem pi_piH_ne_kD : piH ≠ kD := by decide
@[simp] theorem pi_kD_ne_piH : kD ≠ piH := by decide
@[simp] theorem pi_piU_ne_piA : piU ≠ piA := by decide
@[simp] theorem pi_piU_ne_piB : piU ≠ piB := by decide
@[simp] theorem pi_piU_ne_piTa : piU ≠ piTa := by decide
@[simp] theorem pi_piU_ne_piT2 : piU ≠ piT2 := by decide
@[simp] theorem pi_piU_ne_piH : piU ≠ piH := by decide
@[simp] theorem pi_piU_ne_piZ : piU ≠ piZ := by decide
@[simp] theorem pi_piU_ne_piQ : piU ≠ piQ := by decide
@[simp] theorem pi_piU_ne_piOa : piU ≠ piOa := by decide
@[simp] theorem pi_piU_ne_piTb : piU ≠ piTb := by decide
@[simp] theorem pi_piU_ne_piT3 : piU ≠ piT3 := by decide
@[simp] theorem pi_piU_ne_piH2 : piU ≠ piH2 := by decide
@[simp] theorem pi_piU_ne_piV : piU ≠ piV := by decide
@[simp] theorem pi_piU_ne_piQ2 : piU ≠ piQ2 := by decide
@[simp] theorem pi_piU_ne_lFl : piU ≠ lFl := by decide
@[simp] theorem pi_lFl_ne_piU : lFl ≠ piU := by decide
@[simp] theorem pi_piU_ne_lDh : piU ≠ lDh := by decide
@[simp] theorem pi_lDh_ne_piU : lDh ≠ piU := by decide
@[simp] theorem pi_piU_ne_lDt : piU ≠ lDt := by decide
@[simp] theorem pi_lDt_ne_piU : lDt ≠ piU := by decide
@[simp] theorem pi_piU_ne_lDg : piU ≠ lDg := by decide
@[simp] theorem pi_lDg_ne_piU : lDg ≠ piU := by decide
@[simp] theorem pi_piU_ne_lDi : piU ≠ lDi := by decide
@[simp] theorem pi_lDi_ne_piU : lDi ≠ piU := by decide
@[simp] theorem pi_piU_ne_lRp : piU ≠ lRp := by decide
@[simp] theorem pi_lRp_ne_piU : lRp ≠ piU := by decide
@[simp] theorem pi_piU_ne_lRn : piU ≠ lRn := by decide
@[simp] theorem pi_lRn_ne_piU : lRn ≠ piU := by decide
@[simp] theorem pi_piU_ne_lFle : piU ≠ lFle := by decide
@[simp] theorem pi_lFle_ne_piU : lFle ≠ piU := by decide
@[simp] theorem pi_piU_ne_lDir : piU ≠ lDir := by decide
@[simp] theorem pi_lDir_ne_piU : lDir ≠ piU := by decide
@[simp] theorem pi_piU_ne_lKb : piU ≠ lKb := by decide
@[simp] theorem pi_lKb_ne_piU : lKb ≠ piU := by decide
@[simp] theorem pi_piU_ne_kFu : piU ≠ kFu := by decide
@[simp] theorem pi_kFu_ne_piU : kFu ≠ piU := by decide
@[simp] theorem pi_piU_ne_kD : piU ≠ kD := by decide
@[simp] theorem pi_kD_ne_piU : kD ≠ piU := by decide
@[simp] theorem pi_piZ_ne_piA : piZ ≠ piA := by decide
@[simp] theorem pi_piZ_ne_piB : piZ ≠ piB := by decide
@[simp] theorem pi_piZ_ne_piTa : piZ ≠ piTa := by decide
@[simp] theorem pi_piZ_ne_piT2 : piZ ≠ piT2 := by decide
@[simp] theorem pi_piZ_ne_piH : piZ ≠ piH := by decide
@[simp] theorem pi_piZ_ne_piU : piZ ≠ piU := by decide
@[simp] theorem pi_piZ_ne_piQ : piZ ≠ piQ := by decide
@[simp] theorem pi_piZ_ne_piOa : piZ ≠ piOa := by decide
@[simp] theorem pi_piZ_ne_piTb : piZ ≠ piTb := by decide
@[simp] theorem pi_piZ_ne_piT3 : piZ ≠ piT3 := by decide
@[simp] theorem pi_piZ_ne_piH2 : piZ ≠ piH2 := by decide
@[simp] theorem pi_piZ_ne_piV : piZ ≠ piV := by decide
@[simp] theorem pi_piZ_ne_piQ2 : piZ ≠ piQ2 := by decide
@[simp] theorem pi_piZ_ne_lFl : piZ ≠ lFl := by decide
@[simp] theorem pi_lFl_ne_piZ : lFl ≠ piZ := by decide
@[simp] theorem pi_piZ_ne_lDh : piZ ≠ lDh := by decide
@[simp] theorem pi_lDh_ne_piZ : lDh ≠ piZ := by decide
@[simp] theorem pi_piZ_ne_lDt : piZ ≠ lDt := by decide
@[simp] theorem pi_lDt_ne_piZ : lDt ≠ piZ := by decide
@[simp] theorem pi_piZ_ne_lDg : piZ ≠ lDg := by decide
@[simp] theorem pi_lDg_ne_piZ : lDg ≠ piZ := by decide
@[simp] theorem pi_piZ_ne_lDi : piZ ≠ lDi := by decide
@[simp] theorem pi_lDi_ne_piZ : lDi ≠ piZ := by decide
@[simp] theorem pi_piZ_ne_lRp : piZ ≠ lRp := by decide
@[simp] theorem pi_lRp_ne_piZ : lRp ≠ piZ := by decide
@[simp] theorem pi_piZ_ne_lRn : piZ ≠ lRn := by decide
@[simp] theorem pi_lRn_ne_piZ : lRn ≠ piZ := by decide
@[simp] theorem pi_piZ_ne_lFle : piZ ≠ lFle := by decide
@[simp] theorem pi_lFle_ne_piZ : lFle ≠ piZ := by decide
@[simp] theorem pi_piZ_ne_lDir : piZ ≠ lDir := by decide
@[simp] theorem pi_lDir_ne_piZ : lDir ≠ piZ := by decide
@[simp] theorem pi_piZ_ne_lKb : piZ ≠ lKb := by decide
@[simp] theorem pi_lKb_ne_piZ : lKb ≠ piZ := by decide
@[simp] theorem pi_piZ_ne_kFu : piZ ≠ kFu := by decide
@[simp] theorem pi_kFu_ne_piZ : kFu ≠ piZ := by decide
@[simp] theorem pi_piZ_ne_kD : piZ ≠ kD := by decide
@[simp] theorem pi_kD_ne_piZ : kD ≠ piZ := by decide
@[simp] theorem pi_piQ_ne_piA : piQ ≠ piA := by decide
@[simp] theorem pi_piQ_ne_piB : piQ ≠ piB := by decide
@[simp] theorem pi_piQ_ne_piTa : piQ ≠ piTa := by decide
@[simp] theorem pi_piQ_ne_piT2 : piQ ≠ piT2 := by decide
@[simp] theorem pi_piQ_ne_piH : piQ ≠ piH := by decide
@[simp] theorem pi_piQ_ne_piU : piQ ≠ piU := by decide
@[simp] theorem pi_piQ_ne_piZ : piQ ≠ piZ := by decide
@[simp] theorem pi_piQ_ne_piOa : piQ ≠ piOa := by decide
@[simp] theorem pi_piQ_ne_piTb : piQ ≠ piTb := by decide
@[simp] theorem pi_piQ_ne_piT3 : piQ ≠ piT3 := by decide
@[simp] theorem pi_piQ_ne_piH2 : piQ ≠ piH2 := by decide
@[simp] theorem pi_piQ_ne_piV : piQ ≠ piV := by decide
@[simp] theorem pi_piQ_ne_piQ2 : piQ ≠ piQ2 := by decide
@[simp] theorem pi_piQ_ne_lFl : piQ ≠ lFl := by decide
@[simp] theorem pi_lFl_ne_piQ : lFl ≠ piQ := by decide
@[simp] theorem pi_piQ_ne_lDh : piQ ≠ lDh := by decide
@[simp] theorem pi_lDh_ne_piQ : lDh ≠ piQ := by decide
@[simp] theorem pi_piQ_ne_lDt : piQ ≠ lDt := by decide
@[simp] theorem pi_lDt_ne_piQ : lDt ≠ piQ := by decide
@[simp] theorem pi_piQ_ne_lDg : piQ ≠ lDg := by decide
@[simp] theorem pi_lDg_ne_piQ : lDg ≠ piQ := by decide
@[simp] theorem pi_piQ_ne_lDi : piQ ≠ lDi := by decide
@[simp] theorem pi_lDi_ne_piQ : lDi ≠ piQ := by decide
@[simp] theorem pi_piQ_ne_lRp : piQ ≠ lRp := by decide
@[simp] theorem pi_lRp_ne_piQ : lRp ≠ piQ := by decide
@[simp] theorem pi_piQ_ne_lRn : piQ ≠ lRn := by decide
@[simp] theorem pi_lRn_ne_piQ : lRn ≠ piQ := by decide
@[simp] theorem pi_piQ_ne_lFle : piQ ≠ lFle := by decide
@[simp] theorem pi_lFle_ne_piQ : lFle ≠ piQ := by decide
@[simp] theorem pi_piQ_ne_lDir : piQ ≠ lDir := by decide
@[simp] theorem pi_lDir_ne_piQ : lDir ≠ piQ := by decide
@[simp] theorem pi_piQ_ne_lKb : piQ ≠ lKb := by decide
@[simp] theorem pi_lKb_ne_piQ : lKb ≠ piQ := by decide
@[simp] theorem pi_piQ_ne_kFu : piQ ≠ kFu := by decide
@[simp] theorem pi_kFu_ne_piQ : kFu ≠ piQ := by decide
@[simp] theorem pi_piQ_ne_kD : piQ ≠ kD := by decide
@[simp] theorem pi_kD_ne_piQ : kD ≠ piQ := by decide
@[simp] theorem pi_piOa_ne_piA : piOa ≠ piA := by decide
@[simp] theorem pi_piOa_ne_piB : piOa ≠ piB := by decide
@[simp] theorem pi_piOa_ne_piTa : piOa ≠ piTa := by decide
@[simp] theorem pi_piOa_ne_piT2 : piOa ≠ piT2 := by decide
@[simp] theorem pi_piOa_ne_piH : piOa ≠ piH := by decide
@[simp] theorem pi_piOa_ne_piU : piOa ≠ piU := by decide
@[simp] theorem pi_piOa_ne_piZ : piOa ≠ piZ := by decide
@[simp] theorem pi_piOa_ne_piQ : piOa ≠ piQ := by decide
@[simp] theorem pi_piOa_ne_piTb : piOa ≠ piTb := by decide
@[simp] theorem pi_piOa_ne_piT3 : piOa ≠ piT3 := by decide
@[simp] theorem pi_piOa_ne_piH2 : piOa ≠ piH2 := by decide
@[simp] theorem pi_piOa_ne_piV : piOa ≠ piV := by decide
@[simp] theorem pi_piOa_ne_piQ2 : piOa ≠ piQ2 := by decide
@[simp] theorem pi_piOa_ne_lFl : piOa ≠ lFl := by decide
@[simp] theorem pi_lFl_ne_piOa : lFl ≠ piOa := by decide
@[simp] theorem pi_piOa_ne_lDh : piOa ≠ lDh := by decide
@[simp] theorem pi_lDh_ne_piOa : lDh ≠ piOa := by decide
@[simp] theorem pi_piOa_ne_lDt : piOa ≠ lDt := by decide
@[simp] theorem pi_lDt_ne_piOa : lDt ≠ piOa := by decide
@[simp] theorem pi_piOa_ne_lDg : piOa ≠ lDg := by decide
@[simp] theorem pi_lDg_ne_piOa : lDg ≠ piOa := by decide
@[simp] theorem pi_piOa_ne_lDi : piOa ≠ lDi := by decide
@[simp] theorem pi_lDi_ne_piOa : lDi ≠ piOa := by decide
@[simp] theorem pi_piOa_ne_lRp : piOa ≠ lRp := by decide
@[simp] theorem pi_lRp_ne_piOa : lRp ≠ piOa := by decide
@[simp] theorem pi_piOa_ne_lRn : piOa ≠ lRn := by decide
@[simp] theorem pi_lRn_ne_piOa : lRn ≠ piOa := by decide
@[simp] theorem pi_piOa_ne_lFle : piOa ≠ lFle := by decide
@[simp] theorem pi_lFle_ne_piOa : lFle ≠ piOa := by decide
@[simp] theorem pi_piOa_ne_lDir : piOa ≠ lDir := by decide
@[simp] theorem pi_lDir_ne_piOa : lDir ≠ piOa := by decide
@[simp] theorem pi_piOa_ne_lKb : piOa ≠ lKb := by decide
@[simp] theorem pi_lKb_ne_piOa : lKb ≠ piOa := by decide
@[simp] theorem pi_piOa_ne_kFu : piOa ≠ kFu := by decide
@[simp] theorem pi_kFu_ne_piOa : kFu ≠ piOa := by decide
@[simp] theorem pi_piOa_ne_kD : piOa ≠ kD := by decide
@[simp] theorem pi_kD_ne_piOa : kD ≠ piOa := by decide
@[simp] theorem pi_piTb_ne_piA : piTb ≠ piA := by decide
@[simp] theorem pi_piTb_ne_piB : piTb ≠ piB := by decide
@[simp] theorem pi_piTb_ne_piTa : piTb ≠ piTa := by decide
@[simp] theorem pi_piTb_ne_piT2 : piTb ≠ piT2 := by decide
@[simp] theorem pi_piTb_ne_piH : piTb ≠ piH := by decide
@[simp] theorem pi_piTb_ne_piU : piTb ≠ piU := by decide
@[simp] theorem pi_piTb_ne_piZ : piTb ≠ piZ := by decide
@[simp] theorem pi_piTb_ne_piQ : piTb ≠ piQ := by decide
@[simp] theorem pi_piTb_ne_piOa : piTb ≠ piOa := by decide
@[simp] theorem pi_piTb_ne_piT3 : piTb ≠ piT3 := by decide
@[simp] theorem pi_piTb_ne_piH2 : piTb ≠ piH2 := by decide
@[simp] theorem pi_piTb_ne_piV : piTb ≠ piV := by decide
@[simp] theorem pi_piTb_ne_piQ2 : piTb ≠ piQ2 := by decide
@[simp] theorem pi_piTb_ne_lFl : piTb ≠ lFl := by decide
@[simp] theorem pi_lFl_ne_piTb : lFl ≠ piTb := by decide
@[simp] theorem pi_piTb_ne_lDh : piTb ≠ lDh := by decide
@[simp] theorem pi_lDh_ne_piTb : lDh ≠ piTb := by decide
@[simp] theorem pi_piTb_ne_lDt : piTb ≠ lDt := by decide
@[simp] theorem pi_lDt_ne_piTb : lDt ≠ piTb := by decide
@[simp] theorem pi_piTb_ne_lDg : piTb ≠ lDg := by decide
@[simp] theorem pi_lDg_ne_piTb : lDg ≠ piTb := by decide
@[simp] theorem pi_piTb_ne_lDi : piTb ≠ lDi := by decide
@[simp] theorem pi_lDi_ne_piTb : lDi ≠ piTb := by decide
@[simp] theorem pi_piTb_ne_lRp : piTb ≠ lRp := by decide
@[simp] theorem pi_lRp_ne_piTb : lRp ≠ piTb := by decide
@[simp] theorem pi_piTb_ne_lRn : piTb ≠ lRn := by decide
@[simp] theorem pi_lRn_ne_piTb : lRn ≠ piTb := by decide
@[simp] theorem pi_piTb_ne_lFle : piTb ≠ lFle := by decide
@[simp] theorem pi_lFle_ne_piTb : lFle ≠ piTb := by decide
@[simp] theorem pi_piTb_ne_lDir : piTb ≠ lDir := by decide
@[simp] theorem pi_lDir_ne_piTb : lDir ≠ piTb := by decide
@[simp] theorem pi_piTb_ne_lKb : piTb ≠ lKb := by decide
@[simp] theorem pi_lKb_ne_piTb : lKb ≠ piTb := by decide
@[simp] theorem pi_piTb_ne_kFu : piTb ≠ kFu := by decide
@[simp] theorem pi_kFu_ne_piTb : kFu ≠ piTb := by decide
@[simp] theorem pi_piTb_ne_kD : piTb ≠ kD := by decide
@[simp] theorem pi_kD_ne_piTb : kD ≠ piTb := by decide
@[simp] theorem pi_piT3_ne_piA : piT3 ≠ piA := by decide
@[simp] theorem pi_piT3_ne_piB : piT3 ≠ piB := by decide
@[simp] theorem pi_piT3_ne_piTa : piT3 ≠ piTa := by decide
@[simp] theorem pi_piT3_ne_piT2 : piT3 ≠ piT2 := by decide
@[simp] theorem pi_piT3_ne_piH : piT3 ≠ piH := by decide
@[simp] theorem pi_piT3_ne_piU : piT3 ≠ piU := by decide
@[simp] theorem pi_piT3_ne_piZ : piT3 ≠ piZ := by decide
@[simp] theorem pi_piT3_ne_piQ : piT3 ≠ piQ := by decide
@[simp] theorem pi_piT3_ne_piOa : piT3 ≠ piOa := by decide
@[simp] theorem pi_piT3_ne_piTb : piT3 ≠ piTb := by decide
@[simp] theorem pi_piT3_ne_piH2 : piT3 ≠ piH2 := by decide
@[simp] theorem pi_piT3_ne_piV : piT3 ≠ piV := by decide
@[simp] theorem pi_piT3_ne_piQ2 : piT3 ≠ piQ2 := by decide
@[simp] theorem pi_piT3_ne_lFl : piT3 ≠ lFl := by decide
@[simp] theorem pi_lFl_ne_piT3 : lFl ≠ piT3 := by decide
@[simp] theorem pi_piT3_ne_lDh : piT3 ≠ lDh := by decide
@[simp] theorem pi_lDh_ne_piT3 : lDh ≠ piT3 := by decide
@[simp] theorem pi_piT3_ne_lDt : piT3 ≠ lDt := by decide
@[simp] theorem pi_lDt_ne_piT3 : lDt ≠ piT3 := by decide
@[simp] theorem pi_piT3_ne_lDg : piT3 ≠ lDg := by decide
@[simp] theorem pi_lDg_ne_piT3 : lDg ≠ piT3 := by decide
@[simp] theorem pi_piT3_ne_lDi : piT3 ≠ lDi := by decide
@[simp] theorem pi_lDi_ne_piT3 : lDi ≠ piT3 := by decide
@[simp] theorem pi_piT3_ne_lRp : piT3 ≠ lRp := by decide
@[simp] theorem pi_lRp_ne_piT3 : lRp ≠ piT3 := by decide
@[simp] theorem pi_piT3_ne_lRn : piT3 ≠ lRn := by decide
@[simp] theorem pi_lRn_ne_piT3 : lRn ≠ piT3 := by decide
@[simp] theorem pi_piT3_ne_lFle : piT3 ≠ lFle := by decide
@[simp] theorem pi_lFle_ne_piT3 : lFle ≠ piT3 := by decide
@[simp] theorem pi_piT3_ne_lDir : piT3 ≠ lDir := by decide
@[simp] theorem pi_lDir_ne_piT3 : lDir ≠ piT3 := by decide
@[simp] theorem pi_piT3_ne_lKb : piT3 ≠ lKb := by decide
@[simp] theorem pi_lKb_ne_piT3 : lKb ≠ piT3 := by decide
@[simp] theorem pi_piT3_ne_kFu : piT3 ≠ kFu := by decide
@[simp] theorem pi_kFu_ne_piT3 : kFu ≠ piT3 := by decide
@[simp] theorem pi_piT3_ne_kD : piT3 ≠ kD := by decide
@[simp] theorem pi_kD_ne_piT3 : kD ≠ piT3 := by decide
@[simp] theorem pi_piH2_ne_piA : piH2 ≠ piA := by decide
@[simp] theorem pi_piH2_ne_piB : piH2 ≠ piB := by decide
@[simp] theorem pi_piH2_ne_piTa : piH2 ≠ piTa := by decide
@[simp] theorem pi_piH2_ne_piT2 : piH2 ≠ piT2 := by decide
@[simp] theorem pi_piH2_ne_piH : piH2 ≠ piH := by decide
@[simp] theorem pi_piH2_ne_piU : piH2 ≠ piU := by decide
@[simp] theorem pi_piH2_ne_piZ : piH2 ≠ piZ := by decide
@[simp] theorem pi_piH2_ne_piQ : piH2 ≠ piQ := by decide
@[simp] theorem pi_piH2_ne_piOa : piH2 ≠ piOa := by decide
@[simp] theorem pi_piH2_ne_piTb : piH2 ≠ piTb := by decide
@[simp] theorem pi_piH2_ne_piT3 : piH2 ≠ piT3 := by decide
@[simp] theorem pi_piH2_ne_piV : piH2 ≠ piV := by decide
@[simp] theorem pi_piH2_ne_piQ2 : piH2 ≠ piQ2 := by decide
@[simp] theorem pi_piH2_ne_lFl : piH2 ≠ lFl := by decide
@[simp] theorem pi_lFl_ne_piH2 : lFl ≠ piH2 := by decide
@[simp] theorem pi_piH2_ne_lDh : piH2 ≠ lDh := by decide
@[simp] theorem pi_lDh_ne_piH2 : lDh ≠ piH2 := by decide
@[simp] theorem pi_piH2_ne_lDt : piH2 ≠ lDt := by decide
@[simp] theorem pi_lDt_ne_piH2 : lDt ≠ piH2 := by decide
@[simp] theorem pi_piH2_ne_lDg : piH2 ≠ lDg := by decide
@[simp] theorem pi_lDg_ne_piH2 : lDg ≠ piH2 := by decide
@[simp] theorem pi_piH2_ne_lDi : piH2 ≠ lDi := by decide
@[simp] theorem pi_lDi_ne_piH2 : lDi ≠ piH2 := by decide
@[simp] theorem pi_piH2_ne_lRp : piH2 ≠ lRp := by decide
@[simp] theorem pi_lRp_ne_piH2 : lRp ≠ piH2 := by decide
@[simp] theorem pi_piH2_ne_lRn : piH2 ≠ lRn := by decide
@[simp] theorem pi_lRn_ne_piH2 : lRn ≠ piH2 := by decide
@[simp] theorem pi_piH2_ne_lFle : piH2 ≠ lFle := by decide
@[simp] theorem pi_lFle_ne_piH2 : lFle ≠ piH2 := by decide
@[simp] theorem pi_piH2_ne_lDir : piH2 ≠ lDir := by decide
@[simp] theorem pi_lDir_ne_piH2 : lDir ≠ piH2 := by decide
@[simp] theorem pi_piH2_ne_lKb : piH2 ≠ lKb := by decide
@[simp] theorem pi_lKb_ne_piH2 : lKb ≠ piH2 := by decide
@[simp] theorem pi_piH2_ne_kFu : piH2 ≠ kFu := by decide
@[simp] theorem pi_kFu_ne_piH2 : kFu ≠ piH2 := by decide
@[simp] theorem pi_piH2_ne_kD : piH2 ≠ kD := by decide
@[simp] theorem pi_kD_ne_piH2 : kD ≠ piH2 := by decide
@[simp] theorem pi_piV_ne_piA : piV ≠ piA := by decide
@[simp] theorem pi_piV_ne_piB : piV ≠ piB := by decide
@[simp] theorem pi_piV_ne_piTa : piV ≠ piTa := by decide
@[simp] theorem pi_piV_ne_piT2 : piV ≠ piT2 := by decide
@[simp] theorem pi_piV_ne_piH : piV ≠ piH := by decide
@[simp] theorem pi_piV_ne_piU : piV ≠ piU := by decide
@[simp] theorem pi_piV_ne_piZ : piV ≠ piZ := by decide
@[simp] theorem pi_piV_ne_piQ : piV ≠ piQ := by decide
@[simp] theorem pi_piV_ne_piOa : piV ≠ piOa := by decide
@[simp] theorem pi_piV_ne_piTb : piV ≠ piTb := by decide
@[simp] theorem pi_piV_ne_piT3 : piV ≠ piT3 := by decide
@[simp] theorem pi_piV_ne_piH2 : piV ≠ piH2 := by decide
@[simp] theorem pi_piV_ne_piQ2 : piV ≠ piQ2 := by decide
@[simp] theorem pi_piV_ne_lFl : piV ≠ lFl := by decide
@[simp] theorem pi_lFl_ne_piV : lFl ≠ piV := by decide
@[simp] theorem pi_piV_ne_lDh : piV ≠ lDh := by decide
@[simp] theorem pi_lDh_ne_piV : lDh ≠ piV := by decide
@[simp] theorem pi_piV_ne_lDt : piV ≠ lDt := by decide
@[simp] theorem pi_lDt_ne_piV : lDt ≠ piV := by decide
@[simp] theorem pi_piV_ne_lDg : piV ≠ lDg := by decide
@[simp] theorem pi_lDg_ne_piV : lDg ≠ piV := by decide
@[simp] theorem pi_piV_ne_lDi : piV ≠ lDi := by decide
@[simp] theorem pi_lDi_ne_piV : lDi ≠ piV := by decide
@[simp] theorem pi_piV_ne_lRp : piV ≠ lRp := by decide
@[simp] theorem pi_lRp_ne_piV : lRp ≠ piV := by decide
@[simp] theorem pi_piV_ne_lRn : piV ≠ lRn := by decide
@[simp] theorem pi_lRn_ne_piV : lRn ≠ piV := by decide
@[simp] theorem pi_piV_ne_lFle : piV ≠ lFle := by decide
@[simp] theorem pi_lFle_ne_piV : lFle ≠ piV := by decide
@[simp] theorem pi_piV_ne_lDir : piV ≠ lDir := by decide
@[simp] theorem pi_lDir_ne_piV : lDir ≠ piV := by decide
@[simp] theorem pi_piV_ne_lKb : piV ≠ lKb := by decide
@[simp] theorem pi_lKb_ne_piV : lKb ≠ piV := by decide
@[simp] theorem pi_piV_ne_kFu : piV ≠ kFu := by decide
@[simp] theorem pi_kFu_ne_piV : kFu ≠ piV := by decide
@[simp] theorem pi_piV_ne_kD : piV ≠ kD := by decide
@[simp] theorem pi_kD_ne_piV : kD ≠ piV := by decide
@[simp] theorem pi_piQ2_ne_piA : piQ2 ≠ piA := by decide
@[simp] theorem pi_piQ2_ne_piB : piQ2 ≠ piB := by decide
@[simp] theorem pi_piQ2_ne_piTa : piQ2 ≠ piTa := by decide
@[simp] theorem pi_piQ2_ne_piT2 : piQ2 ≠ piT2 := by decide
@[simp] theorem pi_piQ2_ne_piH : piQ2 ≠ piH := by decide
@[simp] theorem pi_piQ2_ne_piU : piQ2 ≠ piU := by decide
@[simp] theorem pi_piQ2_ne_piZ : piQ2 ≠ piZ := by decide
@[simp] theorem pi_piQ2_ne_piQ : piQ2 ≠ piQ := by decide
@[simp] theorem pi_piQ2_ne_piOa : piQ2 ≠ piOa := by decide
@[simp] theorem pi_piQ2_ne_piTb : piQ2 ≠ piTb := by decide
@[simp] theorem pi_piQ2_ne_piT3 : piQ2 ≠ piT3 := by decide
@[simp] theorem pi_piQ2_ne_piH2 : piQ2 ≠ piH2 := by decide
@[simp] theorem pi_piQ2_ne_piV : piQ2 ≠ piV := by decide
@[simp] theorem pi_piQ2_ne_lFl : piQ2 ≠ lFl := by decide
@[simp] theorem pi_lFl_ne_piQ2 : lFl ≠ piQ2 := by decide
@[simp] theorem pi_piQ2_ne_lDh : piQ2 ≠ lDh := by decide
@[simp] theorem pi_lDh_ne_piQ2 : lDh ≠ piQ2 := by decide
@[simp] theorem pi_piQ2_ne_lDt : piQ2 ≠ lDt := by decide
@[simp] theorem pi_lDt_ne_piQ2 : lDt ≠ piQ2 := by decide
@[simp] theorem pi_piQ2_ne_lDg : piQ2 ≠ lDg := by decide
@[simp] theorem pi_lDg_ne_piQ2 : lDg ≠ piQ2 := by decide
@[simp] theorem pi_piQ2_ne_lDi : piQ2 ≠ lDi := by decide
@[simp] theorem pi_lDi_ne_piQ2 : lDi ≠ piQ2 := by decide
@[simp] theorem pi_piQ2_ne_lRp : piQ2 ≠ lRp := by decide
@[simp] theorem pi_lRp_ne_piQ2 : lRp ≠ piQ2 := by decide
@[simp] theorem pi_piQ2_ne_lRn : piQ2 ≠ lRn := by decide
@[simp] theorem pi_lRn_ne_piQ2 : lRn ≠ piQ2 := by decide
@[simp] theorem pi_piQ2_ne_lFle : piQ2 ≠ lFle := by decide
@[simp] theorem pi_lFle_ne_piQ2 : lFle ≠ piQ2 := by decide
@[simp] theorem pi_piQ2_ne_lDir : piQ2 ≠ lDir := by decide
@[simp] theorem pi_lDir_ne_piQ2 : lDir ≠ piQ2 := by decide
@[simp] theorem pi_piQ2_ne_lKb : piQ2 ≠ lKb := by decide
@[simp] theorem pi_lKb_ne_piQ2 : lKb ≠ piQ2 := by decide
@[simp] theorem pi_piQ2_ne_kFu : piQ2 ≠ kFu := by decide
@[simp] theorem pi_kFu_ne_piQ2 : kFu ≠ piQ2 := by decide
@[simp] theorem pi_piQ2_ne_kD : piQ2 ≠ kD := by decide
@[simp] theorem pi_kD_ne_piQ2 : kD ≠ piQ2 := by decide


def piParams : List MlS := [kFu, kD, piA, piB]
def piLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, piTa, piT2, piH, piU, piZ, piQ, piOa, piTb, piT3, piH2, piV,
  piQ2]

def piCore (C : Ctx) : ProgHOL 64 :=
  (.seq (.call (some (some (.local, piTa), none)) fIO [vv kFu, vv kD, vv piA])
    (.seq (.call (some (some (.local, piT2), none)) fIO [vv kFu, vv kD, vv piTa])
    (.seq (.call (some (some (.local, piH), none)) fW [vv kFu, vv kD, vv piT2])
    (.ite (tagIsE piH 2)
    (.seq (.assign .local lFl (vv lFle))
    (.seq (.assign .local lDh (vv piH))
    (.seq eViewP
    (.seq (.assign .local piU (.load .one (vv lRp)))
    (.seq (.assign .local piZ (.load .one (.const (ecell C (C.PO + pinCount + 1)))))
    (.seq (.call (some (some (.local, piQ), none)) LLeq.fEqv [vv piU, vv piZ])
    (.ite (.cmp .equal (vv piQ) (.const 0)) hang
    (.seq (.assign .local piOa (.op .sub [vv piQ, .const 1]))
    (.seq (.call (some (some (.local, piTb), none)) fIO [vv kFu, vv kD, vv piB])
    (.seq (.call (some (some (.local, piT3), none)) fIO [vv kFu, vv kD, vv piTb])
    (.seq (.call (some (some (.local, piH2), none)) fW [vv kFu, vv kD, vv piT3])
    (.ite (tagIsE piH2 2)
    (.seq (.assign .local lDh (vv piH2))
    (.seq eViewP
    (.seq (.assign .local piV (.load .one (vv lRp)))
    (.seq (.assign .local piZ (.load .one (.const (ecell C (C.PO + pinCount + 1)))))
    (.seq (.call (some (some (.local, piQ2), none)) LLeq.fEqv [vv piV, vv piZ])
    (.ite (.cmp .equal (vv piQ2) (.const 0)) hang
    (.return (andE (vv piOa) (.op .sub [vv piQ2, .const 1])))))))))
    (.return (.const 0))))))))))))))
    (.return (.const 0))))))

def piBody (C : Ctx) : ProgHOL 64 := prologue piLocals (piCore C)

section
variable {σ : Type}

theorem pi_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ piLocals → (ctxEnv C ++ piParams.zip vals).get x = none :=
  Knot.params_none C piLocals piParams vals (by decide) (by decide)

theorem obW_sub1 (b : Bool) : LLeq.obW (some b) - 1 = boolW b := by cases b <;> decide

theorem pi_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) (hok : CtxOK C)
    (hcio : C.code.lookup fIO = some (pmap kParams, inferIOE C fIOB, .one))
    (hcw : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one))
    (hce : C.code.lookup LLeq.fEqv = some ([(LEq.pLa, .one), (LEq.pLb, .one)], LLeq.eqvBody, .one))
    (s : AState) (d : Nat) (a b : EIdx)
    (hIO : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ e', Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e'] (inferIOE C fIOB) s1 ((knot mode C n).inferIO d e')
      (PostK (ctxH C H)))
    (hW : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ e', Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d e')
      (PostK (ctxH C H)))
    (hLE : ∀ (H : List (BitVec 64)) s1 (u v : LIdx), C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s1 [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s1 (lvlEq? u v)
        (LLeq.PostOB (ctxH C H))) :
    SpecR (σ := σ) (Pre C s (piParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b]))
      (piBody C) s (proofIrrel (knot mode C n) C.fe d a b) (PostB C) := by
  refine specR_prologue (Knot.postB_locals C) (pi_none C _) ?_
  unfold piCore proofIrrel
  refine Big.specR_callKC piTa fIO kParams [vv kFu, vv kD, vv piA] (inferIOE C fIOB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a] (by decide) rfl (by decide) hcio
    ⟨by simp +decide [Env.get, piParams, ctxEnv], by simp +decide [Env.get, piParams, ctxEnv],
      by simp +decide [Env.get, piParams, ctxEnv], trivial⟩ (hIO C.H s (List.prefix_refl _) a)
    (fun ta s1 H1 hp1 _ => ?_)
  refine Big.specR_callKC (C := ctxH C H1) piT2 fIO kParams [vv kFu, vv kD, vv piTa] (inferIOE C fIOB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ta] (by decide) rfl (by decide) hcio
    ⟨by simp +decide [Env.get, piParams, ctxEnv], by simp +decide [Env.get, piParams, ctxEnv], by simp, trivial⟩
    (hIO H1 s1 hp1 ta) (fun t2 s2 H2 hp2 _ => ?_)
  have hp12 : C.H <+: H2 := hp1.trans hp2
  refine Big.specR_callKC (C := ctxH C H2) piH fW kParams [vv kFu, vv kD, vv piT2] (whnfE C fWB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW t2] (by decide) rfl (by decide) hcw
    ⟨by simp +decide [Env.get, piParams, ctxEnv], by simp +decide [Env.get, piParams, ctxEnv], by simp, trivial⟩
    (hW H2 s2 hp12 t2) (fun hh s3 H3 hp3 _ => ?_)
  have hpX : C.H <+: H3 := hp12.trans hp3
  refine Knot.specR_tagIteV piH hh 2 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
  swap
  · rw [if_neg (show ¬ (hh.tag == ETag.sort) = true by simpa [ETag.sort] using htg)]
    exact specR_returnI _ (boolW false) (by simp [boolW]; rfl)
      (fun t ht => ⟨H3, hpX, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [if_pos (show (hh.tag == ETag.sort) = true by simp [htg, ETag.sort])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv piH) (Enc.idxW hh) (by decide) (by simp) ?_
  refine ILP.specR_viewIv (C := ctxH C H3) hh (by simp) (by simp +decide [Env.get, ctxEnv] <;> rfl)
    (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
  have h2 : v.tagN = 2 := by rw [htn, htg]; rfl
  obtain ⟨uT, rfl⟩ : ∃ u, v = .sort u := by cases v <;> simp [ENodeView.tagN] at h2 ⊢
  dsimp only
  refine specR_loadI' piU (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW uT) (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encSort] using wordsAt_mem0 P (Enc.idxW uT) [] []) ?_
  refine specR_dropM ?_
  have hokX := ctxOK_H hok H3
  refine specR_pinXI (C := ctxH C H3) hokX pinZeroLevel 1 C.pins.zeroLevel _
    (fun s hp => pinZeroLevel_run (C := ctxH C H3) hokX hp) (pin_zeroLevel_cell hokX) piZ (by decide) ?_
  show SpecR _ _ _ (lvlEq? uT C.pins.zeroLevel >>= fun o => liftFueled "level comparison" o >>= _) _
  refine specR_callNIH (C := ctxH C H3) piQ LLeq.fEqv [LEq.pLa, LEq.pLb] [vv piU, vv piZ] LLeq.eqvBody
    [Enc.idxW uT, Enc.idxW C.pins.zeroLevel] (by decide) rfl (by decide) hce ⟨by simp, by simp <;> rfl, trivial⟩
    (LLeq.PostOB (ctxH C H3)) (fun o w _ H' => H' = H3 ∧ w = LLeq.obW o)
    (fun o w s' st ⟨hw, hsr⟩ => ⟨H3, List.prefix_refl _, ⟨rfl, hw⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [LEq.pLa, LEq.pLb] _ rfl hlk)
      (hLE H3 s3 uT C.pins.zeroLevel hpX)) (fun o w s4 H4 _ ⟨eH, hw⟩ => ?_)
  subst H4; subst hw
  rcases o with _ | okA
  · refine specR_ifI _ 1 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI)
      (fun h => absurd h (by decide))
  have hne : LLeq.obW (some okA) ≠ 0 := by cases okA <;> decide
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only [liftFueled, pure_bind]
  refine specR_assignI piOa _ (boolW okA) (by decide) (by simp [sev]; exact obW_sub1 okA) ?_
  refine Big.specR_callKC (C := ctxH C H3) piTb fIO kParams [vv kFu, vv kD, vv piB] (inferIOE C fIOB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW b] (by decide) rfl (by decide) hcio
    ⟨by simp +decide [Env.get, piParams, ctxEnv], by simp +decide [Env.get, piParams, ctxEnv],
      by simp +decide [Env.get, piParams, ctxEnv], trivial⟩ (hIO H3 s4 hpX b) (fun tb s5 H5 hp5 _ => ?_)
  refine Big.specR_callKC (C := ctxH C H5) piT3 fIO kParams [vv kFu, vv kD, vv piTb] (inferIOE C fIOB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW tb] (by decide) rfl (by decide) hcio
    ⟨by simp +decide [Env.get, piParams, ctxEnv], by simp +decide [Env.get, piParams, ctxEnv], by simp, trivial⟩
    (hIO H5 s5 (hpX.trans hp5) tb) (fun t3 s6 H6 hp6 _ => ?_)
  have hp56 : C.H <+: H6 := (hpX.trans hp5).trans hp6
  refine Big.specR_callKC (C := ctxH C H6) piH2 fW kParams [vv kFu, vv kD, vv piT3] (whnfE C fWB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW t3] (by decide) rfl (by decide) hcw
    ⟨by simp +decide [Env.get, piParams, ctxEnv], by simp +decide [Env.get, piParams, ctxEnv], by simp, trivial⟩
    (hW H6 s6 hp56 t3) (fun hh s7 H7 hp7 _ => ?_)
  have hpY : C.H <+: H7 := hp56.trans hp7
  refine Knot.specR_tagIteV piH2 hh 2 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
  swap
  · rw [if_neg (show ¬ (hh.tag == ETag.sort) = true by simpa [ETag.sort] using htg)]
    exact specR_returnI _ (boolW false) (by simp [boolW]; rfl)
      (fun t ht => ⟨H7, hpY, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [if_pos (show (hh.tag == ETag.sort) = true by simp [htg, ETag.sort])]
  skip
  refine specR_assignI lDh (vv piH2) (Enc.idxW hh) (by decide) (by simp) ?_
  refine ILP.specR_viewIv (C := ctxH C H7) hh (by simp) (by simp +decide [Env.get, ctxEnv] <;> rfl)
    (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
  have h2 : v.tagN = 2 := by rw [htn, htg]; rfl
  obtain ⟨uT, rfl⟩ : ∃ u, v = .sort u := by cases v <;> simp [ENodeView.tagN] at h2 ⊢
  dsimp only
  refine specR_loadI' piV (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW uT) (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encSort] using wordsAt_mem0 P (Enc.idxW uT) [] []) ?_
  refine specR_dropM ?_
  have hokX := ctxOK_H hok H7
  refine specR_pinXI (C := ctxH C H7) hokX pinZeroLevel 1 C.pins.zeroLevel _
    (fun s hp => pinZeroLevel_run (C := ctxH C H7) hokX hp) (pin_zeroLevel_cell hokX) piZ (by decide) ?_
  show SpecR _ _ _ (lvlEq? uT C.pins.zeroLevel >>= fun o => liftFueled "level comparison" o >>= _) _
  refine specR_callNIH (C := ctxH C H7) piQ2 LLeq.fEqv [LEq.pLa, LEq.pLb] [vv piV, vv piZ] LLeq.eqvBody
    [Enc.idxW uT, Enc.idxW C.pins.zeroLevel] (by decide) rfl (by decide) hce ⟨by simp, by simp <;> rfl, trivial⟩
    (LLeq.PostOB (ctxH C H7)) (fun o w _ H' => H' = H7 ∧ w = LLeq.obW o)
    (fun o w s' st ⟨hw, hsr⟩ => ⟨H7, List.prefix_refl _, ⟨rfl, hw⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [LEq.pLa, LEq.pLb] _ rfl hlk)
      (hLE H7 s7 uT C.pins.zeroLevel hpY)) (fun o w s8 H8 _ ⟨eH, hw⟩ => ?_)
  subst H8; subst hw
  rcases o with _ | okB
  · refine specR_ifI _ 1 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI)
      (fun h => absurd h (by decide))
  have hne : LLeq.obW (some okB) ≠ 0 := by cases okB <;> decide
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only [liftFueled, pure_bind]
  exact specR_returnI _ (boolW (okA && okB)) (sev_andE (by simp) (by simp [sev]; exact obW_sub1 okB))
    (fun t ht => ⟨H7, hpY, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
