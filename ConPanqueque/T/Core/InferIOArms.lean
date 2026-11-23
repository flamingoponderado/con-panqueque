import ConPanqueque.T.Core.InferProj
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `inferBodyIO`'s own arms: `let` and `λ`

At the io grade a `let` is its body at its value (no check), and a `λ` opens its body at a fresh `fvar`,
infers it, and closes the result over the binder (`inferLamResult`); a depth of `2 ^ 62` or more declines.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def ltoO := ofString "lton_o"
def ltoR := ofString "lton_r"
def qmoV := ofString "qmon_v"
def qmoO := ofString "qmon_o"
def qmoD1 := ofString "qmon_d1"
def qmoB := ofString "qmon_b"
def qmoA := ofString "qmon_a"
def qmoR := ofString "qmon_r"
def fIltIO := ofString "inferLetIO"
def fIlaIO := ofString "inferLamIO"

@[simp] theorem io1_ltoO_ne_ltoR : ltoO ≠ ltoR := by decide
@[simp] theorem io1_ltoO_ne_kFu : ltoO ≠ kFu := by decide
@[simp] theorem io1_kFu_ne_ltoO : kFu ≠ ltoO := by decide
@[simp] theorem io1_ltoO_ne_kD : ltoO ≠ kD := by decide
@[simp] theorem io1_kD_ne_ltoO : kD ≠ ltoO := by decide
@[simp] theorem io1_ltoO_ne_ibT1 : ltoO ≠ ibT1 := by decide
@[simp] theorem io1_ibT1_ne_ltoO : ibT1 ≠ ltoO := by decide
@[simp] theorem io1_ltoO_ne_ibT2 : ltoO ≠ ibT2 := by decide
@[simp] theorem io1_ibT2_ne_ltoO : ibT2 ≠ ltoO := by decide
@[simp] theorem io1_ltoO_ne_ibV1 : ltoO ≠ ibV1 := by decide
@[simp] theorem io1_ibV1_ne_ltoO : ibV1 ≠ ltoO := by decide
@[simp] theorem io1_ltoO_ne_ibB1 : ltoO ≠ ibB1 := by decide
@[simp] theorem io1_ibB1_ne_ltoO : ibB1 ≠ ltoO := by decide
@[simp] theorem io1_ltoO_ne_lFl : ltoO ≠ lFl := by decide
@[simp] theorem io1_lFl_ne_ltoO : lFl ≠ ltoO := by decide
@[simp] theorem io1_ltoO_ne_lDh : ltoO ≠ lDh := by decide
@[simp] theorem io1_lDh_ne_ltoO : lDh ≠ ltoO := by decide
@[simp] theorem io1_ltoO_ne_lDt : ltoO ≠ lDt := by decide
@[simp] theorem io1_lDt_ne_ltoO : lDt ≠ ltoO := by decide
@[simp] theorem io1_ltoO_ne_lDg : ltoO ≠ lDg := by decide
@[simp] theorem io1_lDg_ne_ltoO : lDg ≠ ltoO := by decide
@[simp] theorem io1_ltoO_ne_lDi : ltoO ≠ lDi := by decide
@[simp] theorem io1_lDi_ne_ltoO : lDi ≠ ltoO := by decide
@[simp] theorem io1_ltoO_ne_lRp : ltoO ≠ lRp := by decide
@[simp] theorem io1_lRp_ne_ltoO : lRp ≠ ltoO := by decide
@[simp] theorem io1_ltoO_ne_lRn : ltoO ≠ lRn := by decide
@[simp] theorem io1_lRn_ne_ltoO : lRn ≠ ltoO := by decide
@[simp] theorem io1_ltoO_ne_lDir : ltoO ≠ lDir := by decide
@[simp] theorem io1_lDir_ne_ltoO : lDir ≠ ltoO := by decide
@[simp] theorem io1_ltoO_ne_lFle : ltoO ≠ lFle := by decide
@[simp] theorem io1_lFle_ne_ltoO : lFle ≠ ltoO := by decide
@[simp] theorem io1_ltoO_ne_lKb : ltoO ≠ lKb := by decide
@[simp] theorem io1_lKb_ne_ltoO : lKb ≠ ltoO := by decide
@[simp] theorem io1_ltoR_ne_ltoO : ltoR ≠ ltoO := by decide
@[simp] theorem io1_ltoR_ne_kFu : ltoR ≠ kFu := by decide
@[simp] theorem io1_kFu_ne_ltoR : kFu ≠ ltoR := by decide
@[simp] theorem io1_ltoR_ne_kD : ltoR ≠ kD := by decide
@[simp] theorem io1_kD_ne_ltoR : kD ≠ ltoR := by decide
@[simp] theorem io1_ltoR_ne_ibT1 : ltoR ≠ ibT1 := by decide
@[simp] theorem io1_ibT1_ne_ltoR : ibT1 ≠ ltoR := by decide
@[simp] theorem io1_ltoR_ne_ibT2 : ltoR ≠ ibT2 := by decide
@[simp] theorem io1_ibT2_ne_ltoR : ibT2 ≠ ltoR := by decide
@[simp] theorem io1_ltoR_ne_ibV1 : ltoR ≠ ibV1 := by decide
@[simp] theorem io1_ibV1_ne_ltoR : ibV1 ≠ ltoR := by decide
@[simp] theorem io1_ltoR_ne_ibB1 : ltoR ≠ ibB1 := by decide
@[simp] theorem io1_ibB1_ne_ltoR : ibB1 ≠ ltoR := by decide
@[simp] theorem io1_ltoR_ne_lFl : ltoR ≠ lFl := by decide
@[simp] theorem io1_lFl_ne_ltoR : lFl ≠ ltoR := by decide
@[simp] theorem io1_ltoR_ne_lDh : ltoR ≠ lDh := by decide
@[simp] theorem io1_lDh_ne_ltoR : lDh ≠ ltoR := by decide
@[simp] theorem io1_ltoR_ne_lDt : ltoR ≠ lDt := by decide
@[simp] theorem io1_lDt_ne_ltoR : lDt ≠ ltoR := by decide
@[simp] theorem io1_ltoR_ne_lDg : ltoR ≠ lDg := by decide
@[simp] theorem io1_lDg_ne_ltoR : lDg ≠ ltoR := by decide
@[simp] theorem io1_ltoR_ne_lDi : ltoR ≠ lDi := by decide
@[simp] theorem io1_lDi_ne_ltoR : lDi ≠ ltoR := by decide
@[simp] theorem io1_ltoR_ne_lRp : ltoR ≠ lRp := by decide
@[simp] theorem io1_lRp_ne_ltoR : lRp ≠ ltoR := by decide
@[simp] theorem io1_ltoR_ne_lRn : ltoR ≠ lRn := by decide
@[simp] theorem io1_lRn_ne_ltoR : lRn ≠ ltoR := by decide
@[simp] theorem io1_ltoR_ne_lDir : ltoR ≠ lDir := by decide
@[simp] theorem io1_lDir_ne_ltoR : lDir ≠ ltoR := by decide
@[simp] theorem io1_ltoR_ne_lFle : ltoR ≠ lFle := by decide
@[simp] theorem io1_lFle_ne_ltoR : lFle ≠ ltoR := by decide
@[simp] theorem io1_ltoR_ne_lKb : ltoR ≠ lKb := by decide
@[simp] theorem io1_lKb_ne_ltoR : lKb ≠ ltoR := by decide
@[simp] theorem io1_qmoV_ne_qmoO : qmoV ≠ qmoO := by decide
@[simp] theorem io1_qmoV_ne_qmoD1 : qmoV ≠ qmoD1 := by decide
@[simp] theorem io1_qmoV_ne_qmoB : qmoV ≠ qmoB := by decide
@[simp] theorem io1_qmoV_ne_qmoA : qmoV ≠ qmoA := by decide
@[simp] theorem io1_qmoV_ne_qmoR : qmoV ≠ qmoR := by decide
@[simp] theorem io1_qmoV_ne_kFu : qmoV ≠ kFu := by decide
@[simp] theorem io1_kFu_ne_qmoV : kFu ≠ qmoV := by decide
@[simp] theorem io1_qmoV_ne_kD : qmoV ≠ kD := by decide
@[simp] theorem io1_kD_ne_qmoV : kD ≠ qmoV := by decide
@[simp] theorem io1_qmoV_ne_ibT1 : qmoV ≠ ibT1 := by decide
@[simp] theorem io1_ibT1_ne_qmoV : ibT1 ≠ qmoV := by decide
@[simp] theorem io1_qmoV_ne_ibT2 : qmoV ≠ ibT2 := by decide
@[simp] theorem io1_ibT2_ne_qmoV : ibT2 ≠ qmoV := by decide
@[simp] theorem io1_qmoV_ne_ibV1 : qmoV ≠ ibV1 := by decide
@[simp] theorem io1_ibV1_ne_qmoV : ibV1 ≠ qmoV := by decide
@[simp] theorem io1_qmoV_ne_ibB1 : qmoV ≠ ibB1 := by decide
@[simp] theorem io1_ibB1_ne_qmoV : ibB1 ≠ qmoV := by decide
@[simp] theorem io1_qmoV_ne_lFl : qmoV ≠ lFl := by decide
@[simp] theorem io1_lFl_ne_qmoV : lFl ≠ qmoV := by decide
@[simp] theorem io1_qmoV_ne_lDh : qmoV ≠ lDh := by decide
@[simp] theorem io1_lDh_ne_qmoV : lDh ≠ qmoV := by decide
@[simp] theorem io1_qmoV_ne_lDt : qmoV ≠ lDt := by decide
@[simp] theorem io1_lDt_ne_qmoV : lDt ≠ qmoV := by decide
@[simp] theorem io1_qmoV_ne_lDg : qmoV ≠ lDg := by decide
@[simp] theorem io1_lDg_ne_qmoV : lDg ≠ qmoV := by decide
@[simp] theorem io1_qmoV_ne_lDi : qmoV ≠ lDi := by decide
@[simp] theorem io1_lDi_ne_qmoV : lDi ≠ qmoV := by decide
@[simp] theorem io1_qmoV_ne_lRp : qmoV ≠ lRp := by decide
@[simp] theorem io1_lRp_ne_qmoV : lRp ≠ qmoV := by decide
@[simp] theorem io1_qmoV_ne_lRn : qmoV ≠ lRn := by decide
@[simp] theorem io1_lRn_ne_qmoV : lRn ≠ qmoV := by decide
@[simp] theorem io1_qmoV_ne_lDir : qmoV ≠ lDir := by decide
@[simp] theorem io1_lDir_ne_qmoV : lDir ≠ qmoV := by decide
@[simp] theorem io1_qmoV_ne_lFle : qmoV ≠ lFle := by decide
@[simp] theorem io1_lFle_ne_qmoV : lFle ≠ qmoV := by decide
@[simp] theorem io1_qmoV_ne_lKb : qmoV ≠ lKb := by decide
@[simp] theorem io1_lKb_ne_qmoV : lKb ≠ qmoV := by decide
@[simp] theorem io1_qmoO_ne_qmoV : qmoO ≠ qmoV := by decide
@[simp] theorem io1_qmoO_ne_qmoD1 : qmoO ≠ qmoD1 := by decide
@[simp] theorem io1_qmoO_ne_qmoB : qmoO ≠ qmoB := by decide
@[simp] theorem io1_qmoO_ne_qmoA : qmoO ≠ qmoA := by decide
@[simp] theorem io1_qmoO_ne_qmoR : qmoO ≠ qmoR := by decide
@[simp] theorem io1_qmoO_ne_kFu : qmoO ≠ kFu := by decide
@[simp] theorem io1_kFu_ne_qmoO : kFu ≠ qmoO := by decide
@[simp] theorem io1_qmoO_ne_kD : qmoO ≠ kD := by decide
@[simp] theorem io1_kD_ne_qmoO : kD ≠ qmoO := by decide
@[simp] theorem io1_qmoO_ne_ibT1 : qmoO ≠ ibT1 := by decide
@[simp] theorem io1_ibT1_ne_qmoO : ibT1 ≠ qmoO := by decide
@[simp] theorem io1_qmoO_ne_ibT2 : qmoO ≠ ibT2 := by decide
@[simp] theorem io1_ibT2_ne_qmoO : ibT2 ≠ qmoO := by decide
@[simp] theorem io1_qmoO_ne_ibV1 : qmoO ≠ ibV1 := by decide
@[simp] theorem io1_ibV1_ne_qmoO : ibV1 ≠ qmoO := by decide
@[simp] theorem io1_qmoO_ne_ibB1 : qmoO ≠ ibB1 := by decide
@[simp] theorem io1_ibB1_ne_qmoO : ibB1 ≠ qmoO := by decide
@[simp] theorem io1_qmoO_ne_lFl : qmoO ≠ lFl := by decide
@[simp] theorem io1_lFl_ne_qmoO : lFl ≠ qmoO := by decide
@[simp] theorem io1_qmoO_ne_lDh : qmoO ≠ lDh := by decide
@[simp] theorem io1_lDh_ne_qmoO : lDh ≠ qmoO := by decide
@[simp] theorem io1_qmoO_ne_lDt : qmoO ≠ lDt := by decide
@[simp] theorem io1_lDt_ne_qmoO : lDt ≠ qmoO := by decide
@[simp] theorem io1_qmoO_ne_lDg : qmoO ≠ lDg := by decide
@[simp] theorem io1_lDg_ne_qmoO : lDg ≠ qmoO := by decide
@[simp] theorem io1_qmoO_ne_lDi : qmoO ≠ lDi := by decide
@[simp] theorem io1_lDi_ne_qmoO : lDi ≠ qmoO := by decide
@[simp] theorem io1_qmoO_ne_lRp : qmoO ≠ lRp := by decide
@[simp] theorem io1_lRp_ne_qmoO : lRp ≠ qmoO := by decide
@[simp] theorem io1_qmoO_ne_lRn : qmoO ≠ lRn := by decide
@[simp] theorem io1_lRn_ne_qmoO : lRn ≠ qmoO := by decide
@[simp] theorem io1_qmoO_ne_lDir : qmoO ≠ lDir := by decide
@[simp] theorem io1_lDir_ne_qmoO : lDir ≠ qmoO := by decide
@[simp] theorem io1_qmoO_ne_lFle : qmoO ≠ lFle := by decide
@[simp] theorem io1_lFle_ne_qmoO : lFle ≠ qmoO := by decide
@[simp] theorem io1_qmoO_ne_lKb : qmoO ≠ lKb := by decide
@[simp] theorem io1_lKb_ne_qmoO : lKb ≠ qmoO := by decide
@[simp] theorem io1_qmoD1_ne_qmoV : qmoD1 ≠ qmoV := by decide
@[simp] theorem io1_qmoD1_ne_qmoO : qmoD1 ≠ qmoO := by decide
@[simp] theorem io1_qmoD1_ne_qmoB : qmoD1 ≠ qmoB := by decide
@[simp] theorem io1_qmoD1_ne_qmoA : qmoD1 ≠ qmoA := by decide
@[simp] theorem io1_qmoD1_ne_qmoR : qmoD1 ≠ qmoR := by decide
@[simp] theorem io1_qmoD1_ne_kFu : qmoD1 ≠ kFu := by decide
@[simp] theorem io1_kFu_ne_qmoD1 : kFu ≠ qmoD1 := by decide
@[simp] theorem io1_qmoD1_ne_kD : qmoD1 ≠ kD := by decide
@[simp] theorem io1_kD_ne_qmoD1 : kD ≠ qmoD1 := by decide
@[simp] theorem io1_qmoD1_ne_ibT1 : qmoD1 ≠ ibT1 := by decide
@[simp] theorem io1_ibT1_ne_qmoD1 : ibT1 ≠ qmoD1 := by decide
@[simp] theorem io1_qmoD1_ne_ibT2 : qmoD1 ≠ ibT2 := by decide
@[simp] theorem io1_ibT2_ne_qmoD1 : ibT2 ≠ qmoD1 := by decide
@[simp] theorem io1_qmoD1_ne_ibV1 : qmoD1 ≠ ibV1 := by decide
@[simp] theorem io1_ibV1_ne_qmoD1 : ibV1 ≠ qmoD1 := by decide
@[simp] theorem io1_qmoD1_ne_ibB1 : qmoD1 ≠ ibB1 := by decide
@[simp] theorem io1_ibB1_ne_qmoD1 : ibB1 ≠ qmoD1 := by decide
@[simp] theorem io1_qmoD1_ne_lFl : qmoD1 ≠ lFl := by decide
@[simp] theorem io1_lFl_ne_qmoD1 : lFl ≠ qmoD1 := by decide
@[simp] theorem io1_qmoD1_ne_lDh : qmoD1 ≠ lDh := by decide
@[simp] theorem io1_lDh_ne_qmoD1 : lDh ≠ qmoD1 := by decide
@[simp] theorem io1_qmoD1_ne_lDt : qmoD1 ≠ lDt := by decide
@[simp] theorem io1_lDt_ne_qmoD1 : lDt ≠ qmoD1 := by decide
@[simp] theorem io1_qmoD1_ne_lDg : qmoD1 ≠ lDg := by decide
@[simp] theorem io1_lDg_ne_qmoD1 : lDg ≠ qmoD1 := by decide
@[simp] theorem io1_qmoD1_ne_lDi : qmoD1 ≠ lDi := by decide
@[simp] theorem io1_lDi_ne_qmoD1 : lDi ≠ qmoD1 := by decide
@[simp] theorem io1_qmoD1_ne_lRp : qmoD1 ≠ lRp := by decide
@[simp] theorem io1_lRp_ne_qmoD1 : lRp ≠ qmoD1 := by decide
@[simp] theorem io1_qmoD1_ne_lRn : qmoD1 ≠ lRn := by decide
@[simp] theorem io1_lRn_ne_qmoD1 : lRn ≠ qmoD1 := by decide
@[simp] theorem io1_qmoD1_ne_lDir : qmoD1 ≠ lDir := by decide
@[simp] theorem io1_lDir_ne_qmoD1 : lDir ≠ qmoD1 := by decide
@[simp] theorem io1_qmoD1_ne_lFle : qmoD1 ≠ lFle := by decide
@[simp] theorem io1_lFle_ne_qmoD1 : lFle ≠ qmoD1 := by decide
@[simp] theorem io1_qmoD1_ne_lKb : qmoD1 ≠ lKb := by decide
@[simp] theorem io1_lKb_ne_qmoD1 : lKb ≠ qmoD1 := by decide
@[simp] theorem io1_qmoB_ne_qmoV : qmoB ≠ qmoV := by decide
@[simp] theorem io1_qmoB_ne_qmoO : qmoB ≠ qmoO := by decide
@[simp] theorem io1_qmoB_ne_qmoD1 : qmoB ≠ qmoD1 := by decide
@[simp] theorem io1_qmoB_ne_qmoA : qmoB ≠ qmoA := by decide
@[simp] theorem io1_qmoB_ne_qmoR : qmoB ≠ qmoR := by decide
@[simp] theorem io1_qmoB_ne_kFu : qmoB ≠ kFu := by decide
@[simp] theorem io1_kFu_ne_qmoB : kFu ≠ qmoB := by decide
@[simp] theorem io1_qmoB_ne_kD : qmoB ≠ kD := by decide
@[simp] theorem io1_kD_ne_qmoB : kD ≠ qmoB := by decide
@[simp] theorem io1_qmoB_ne_ibT1 : qmoB ≠ ibT1 := by decide
@[simp] theorem io1_ibT1_ne_qmoB : ibT1 ≠ qmoB := by decide
@[simp] theorem io1_qmoB_ne_ibT2 : qmoB ≠ ibT2 := by decide
@[simp] theorem io1_ibT2_ne_qmoB : ibT2 ≠ qmoB := by decide
@[simp] theorem io1_qmoB_ne_ibV1 : qmoB ≠ ibV1 := by decide
@[simp] theorem io1_ibV1_ne_qmoB : ibV1 ≠ qmoB := by decide
@[simp] theorem io1_qmoB_ne_ibB1 : qmoB ≠ ibB1 := by decide
@[simp] theorem io1_ibB1_ne_qmoB : ibB1 ≠ qmoB := by decide
@[simp] theorem io1_qmoB_ne_lFl : qmoB ≠ lFl := by decide
@[simp] theorem io1_lFl_ne_qmoB : lFl ≠ qmoB := by decide
@[simp] theorem io1_qmoB_ne_lDh : qmoB ≠ lDh := by decide
@[simp] theorem io1_lDh_ne_qmoB : lDh ≠ qmoB := by decide
@[simp] theorem io1_qmoB_ne_lDt : qmoB ≠ lDt := by decide
@[simp] theorem io1_lDt_ne_qmoB : lDt ≠ qmoB := by decide
@[simp] theorem io1_qmoB_ne_lDg : qmoB ≠ lDg := by decide
@[simp] theorem io1_lDg_ne_qmoB : lDg ≠ qmoB := by decide
@[simp] theorem io1_qmoB_ne_lDi : qmoB ≠ lDi := by decide
@[simp] theorem io1_lDi_ne_qmoB : lDi ≠ qmoB := by decide
@[simp] theorem io1_qmoB_ne_lRp : qmoB ≠ lRp := by decide
@[simp] theorem io1_lRp_ne_qmoB : lRp ≠ qmoB := by decide
@[simp] theorem io1_qmoB_ne_lRn : qmoB ≠ lRn := by decide
@[simp] theorem io1_lRn_ne_qmoB : lRn ≠ qmoB := by decide
@[simp] theorem io1_qmoB_ne_lDir : qmoB ≠ lDir := by decide
@[simp] theorem io1_lDir_ne_qmoB : lDir ≠ qmoB := by decide
@[simp] theorem io1_qmoB_ne_lFle : qmoB ≠ lFle := by decide
@[simp] theorem io1_lFle_ne_qmoB : lFle ≠ qmoB := by decide
@[simp] theorem io1_qmoB_ne_lKb : qmoB ≠ lKb := by decide
@[simp] theorem io1_lKb_ne_qmoB : lKb ≠ qmoB := by decide
@[simp] theorem io1_qmoA_ne_qmoV : qmoA ≠ qmoV := by decide
@[simp] theorem io1_qmoA_ne_qmoO : qmoA ≠ qmoO := by decide
@[simp] theorem io1_qmoA_ne_qmoD1 : qmoA ≠ qmoD1 := by decide
@[simp] theorem io1_qmoA_ne_qmoB : qmoA ≠ qmoB := by decide
@[simp] theorem io1_qmoA_ne_qmoR : qmoA ≠ qmoR := by decide
@[simp] theorem io1_qmoA_ne_kFu : qmoA ≠ kFu := by decide
@[simp] theorem io1_kFu_ne_qmoA : kFu ≠ qmoA := by decide
@[simp] theorem io1_qmoA_ne_kD : qmoA ≠ kD := by decide
@[simp] theorem io1_kD_ne_qmoA : kD ≠ qmoA := by decide
@[simp] theorem io1_qmoA_ne_ibT1 : qmoA ≠ ibT1 := by decide
@[simp] theorem io1_ibT1_ne_qmoA : ibT1 ≠ qmoA := by decide
@[simp] theorem io1_qmoA_ne_ibT2 : qmoA ≠ ibT2 := by decide
@[simp] theorem io1_ibT2_ne_qmoA : ibT2 ≠ qmoA := by decide
@[simp] theorem io1_qmoA_ne_ibV1 : qmoA ≠ ibV1 := by decide
@[simp] theorem io1_ibV1_ne_qmoA : ibV1 ≠ qmoA := by decide
@[simp] theorem io1_qmoA_ne_ibB1 : qmoA ≠ ibB1 := by decide
@[simp] theorem io1_ibB1_ne_qmoA : ibB1 ≠ qmoA := by decide
@[simp] theorem io1_qmoA_ne_lFl : qmoA ≠ lFl := by decide
@[simp] theorem io1_lFl_ne_qmoA : lFl ≠ qmoA := by decide
@[simp] theorem io1_qmoA_ne_lDh : qmoA ≠ lDh := by decide
@[simp] theorem io1_lDh_ne_qmoA : lDh ≠ qmoA := by decide
@[simp] theorem io1_qmoA_ne_lDt : qmoA ≠ lDt := by decide
@[simp] theorem io1_lDt_ne_qmoA : lDt ≠ qmoA := by decide
@[simp] theorem io1_qmoA_ne_lDg : qmoA ≠ lDg := by decide
@[simp] theorem io1_lDg_ne_qmoA : lDg ≠ qmoA := by decide
@[simp] theorem io1_qmoA_ne_lDi : qmoA ≠ lDi := by decide
@[simp] theorem io1_lDi_ne_qmoA : lDi ≠ qmoA := by decide
@[simp] theorem io1_qmoA_ne_lRp : qmoA ≠ lRp := by decide
@[simp] theorem io1_lRp_ne_qmoA : lRp ≠ qmoA := by decide
@[simp] theorem io1_qmoA_ne_lRn : qmoA ≠ lRn := by decide
@[simp] theorem io1_lRn_ne_qmoA : lRn ≠ qmoA := by decide
@[simp] theorem io1_qmoA_ne_lDir : qmoA ≠ lDir := by decide
@[simp] theorem io1_lDir_ne_qmoA : lDir ≠ qmoA := by decide
@[simp] theorem io1_qmoA_ne_lFle : qmoA ≠ lFle := by decide
@[simp] theorem io1_lFle_ne_qmoA : lFle ≠ qmoA := by decide
@[simp] theorem io1_qmoA_ne_lKb : qmoA ≠ lKb := by decide
@[simp] theorem io1_lKb_ne_qmoA : lKb ≠ qmoA := by decide
@[simp] theorem io1_qmoR_ne_qmoV : qmoR ≠ qmoV := by decide
@[simp] theorem io1_qmoR_ne_qmoO : qmoR ≠ qmoO := by decide
@[simp] theorem io1_qmoR_ne_qmoD1 : qmoR ≠ qmoD1 := by decide
@[simp] theorem io1_qmoR_ne_qmoB : qmoR ≠ qmoB := by decide
@[simp] theorem io1_qmoR_ne_qmoA : qmoR ≠ qmoA := by decide
@[simp] theorem io1_qmoR_ne_kFu : qmoR ≠ kFu := by decide
@[simp] theorem io1_kFu_ne_qmoR : kFu ≠ qmoR := by decide
@[simp] theorem io1_qmoR_ne_kD : qmoR ≠ kD := by decide
@[simp] theorem io1_kD_ne_qmoR : kD ≠ qmoR := by decide
@[simp] theorem io1_qmoR_ne_ibT1 : qmoR ≠ ibT1 := by decide
@[simp] theorem io1_ibT1_ne_qmoR : ibT1 ≠ qmoR := by decide
@[simp] theorem io1_qmoR_ne_ibT2 : qmoR ≠ ibT2 := by decide
@[simp] theorem io1_ibT2_ne_qmoR : ibT2 ≠ qmoR := by decide
@[simp] theorem io1_qmoR_ne_ibV1 : qmoR ≠ ibV1 := by decide
@[simp] theorem io1_ibV1_ne_qmoR : ibV1 ≠ qmoR := by decide
@[simp] theorem io1_qmoR_ne_ibB1 : qmoR ≠ ibB1 := by decide
@[simp] theorem io1_ibB1_ne_qmoR : ibB1 ≠ qmoR := by decide
@[simp] theorem io1_qmoR_ne_lFl : qmoR ≠ lFl := by decide
@[simp] theorem io1_lFl_ne_qmoR : lFl ≠ qmoR := by decide
@[simp] theorem io1_qmoR_ne_lDh : qmoR ≠ lDh := by decide
@[simp] theorem io1_lDh_ne_qmoR : lDh ≠ qmoR := by decide
@[simp] theorem io1_qmoR_ne_lDt : qmoR ≠ lDt := by decide
@[simp] theorem io1_lDt_ne_qmoR : lDt ≠ qmoR := by decide
@[simp] theorem io1_qmoR_ne_lDg : qmoR ≠ lDg := by decide
@[simp] theorem io1_lDg_ne_qmoR : lDg ≠ qmoR := by decide
@[simp] theorem io1_qmoR_ne_lDi : qmoR ≠ lDi := by decide
@[simp] theorem io1_lDi_ne_qmoR : lDi ≠ qmoR := by decide
@[simp] theorem io1_qmoR_ne_lRp : qmoR ≠ lRp := by decide
@[simp] theorem io1_lRp_ne_qmoR : lRp ≠ qmoR := by decide
@[simp] theorem io1_qmoR_ne_lRn : qmoR ≠ lRn := by decide
@[simp] theorem io1_lRn_ne_qmoR : lRn ≠ qmoR := by decide
@[simp] theorem io1_qmoR_ne_lDir : qmoR ≠ lDir := by decide
@[simp] theorem io1_lDir_ne_qmoR : lDir ≠ qmoR := by decide
@[simp] theorem io1_qmoR_ne_lFle : qmoR ≠ lFle := by decide
@[simp] theorem io1_lFle_ne_qmoR : lFle ≠ qmoR := by decide
@[simp] theorem io1_qmoR_ne_lKb : qmoR ≠ lKb := by decide
@[simp] theorem io1_lKb_ne_qmoR : lKb ≠ qmoR := by decide

def ibLetIOT (r : CoreFnsA) (depth : Nat) (v b : EIdx) : AM EIdx := do
  let ob ← instantiate1Fast coreWalkFuel b v 0
  r.infer depth ob

def ibLamIOT (r : CoreFnsA) (depth : Nat) (ty body : EIdx) : AM EIdx := do
  let fv ← internE (.fvar depth ty)
  let ob ← instantiate1Fast coreWalkFuel body fv 0
  let bt ← r.infer (depth + 1) ob
  inferLamResult ty bt depth

def ltoLocals : List MlS := [ltoO, ltoR]
def ltoBody : ProgHOL 64 := prologue ltoLocals (.seq (.call (some (some (.local, ltoO), none)) ExI.fInst1F [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv ibB1), (vv ibV1), (.const 0)]) (.seq (.call (some (some (.local, ltoR), none)) fI [(vv kFu), (vv kD), (vv ltoO)]) (.return (vv ltoR))))

def qmoLocals : List MlS := [qmoV, qmoO, qmoD1, qmoB, qmoA, qmoR]
def qmoBody : ProgHOL 64 := prologue qmoLocals (.ite (.cmp .lower (vv kD) (.const (BitVec.ofNat 64 (2 ^ 62)))) (.seq (.call (some (some (.local, qmoV), none)) fInternFVar [(vv ibT1), (vv kD)]) (.seq (.call (some (some (.local, qmoO), none)) ExI.fInst1F [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv ibT2), (vv qmoV), (.const 0)]) (.seq (.assign .local qmoD1 (.op .add [(vv kD), (.const 1)])) (.seq (.call (some (some (.local, qmoB), none)) fI [(vv kFu), (vv qmoD1), (vv qmoO)]) (.seq (.call (some (some (.local, qmoA), none)) ExA.fAbs1F [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv kD), (.const 0), (vv qmoB)]) (.seq (.call (some (some (.local, qmoR), none)) fInternForallE [(vv ibT1), (vv qmoA)]) (.return (vv qmoR)))))))) hang)

section
variable {σ : Type}

theorem lto_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ltoLocals → (ctxEnv C ++ iltParams.zip vals).get x = none :=
  Knot.params_none C ltoLocals iltParams vals (by decide) (by decide)
theorem qmo_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ qmoLocals → (ctxEnv C ++ ifaParams.zip vals).get x = none :=
  Knot.params_none C qmoLocals ifaParams vals (by decide) (by decide)

theorem lto_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C)
    (hci : C.code.lookup fI = some (pmap kParams, inferE C fIB, .one))
    (hcI : C.code.lookup ExI.fInst1F = some ([pFu, pH, ExI.pV, ExI.pD].map (fun p => (p, ShapeHOL.one)),
      ExI.fastBody C, .one)) (hcI' : ExI.Codes C (ExI.body C))
    (hI : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (inferE C fIB) s1 ((knot mode C n).infer d' e')
      (PostK (ctxH C H)))
    (s : AState) (d : Nat) (ty v b : EIdx) :
    SpecR (σ := σ) (Pre C s (iltParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty, Enc.idxW v,
      Enc.idxW b])) ltoBody s (ibLetIOT (knot mode C n) d v b) (PostK C) := by
  refine specR_prologue (postK_locals C) (lto_none C _) ?_
  unfold ibLetIOT
  refine ILP.callE_spec ltoO ExI.fInst1F [pFu, pH, ExI.pV, ExI.pD]
    [.const (BitVec.ofNat 64 coreWalkFuel), vv ibB1, vv ibV1, .const 0] (ExI.fastBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW b, Enc.idxW v, BitVec.ofNat 64 0] (by decide) rfl (by decide) hcI
    ⟨rfl, by simp +decide [Env.get, iltParams, ctxEnv], by simp +decide [Env.get, iltParams, ctxEnv], rfl, trivial⟩
    (ExI.fast_spec ra C hok hcI' s coreWalkFuel b v 0 CV.coreWalkFuel_lt (by decide)) (fun ob s1 => ?_)
  refine specR_congr (m' := (knot mode C n).infer d ob >>= fun r => pure r) (by simp) ?_
  refine Big.specR_callKC ltoR fI kParams [vv kFu, vv kD, vv ltoO] (inferE C fIB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ob] (by decide) rfl (by decide) hci
    ⟨by simp +decide [Env.get, iltParams, ctxEnv], by simp +decide [Env.get, iltParams, ctxEnv], by simp, trivial⟩ (hI C.H s1 d ob (List.prefix_refl _)) (fun r s2 H2 hp2 _ => ?_)
  exact specR_returnI _ (Enc.idxW r) (by simp) (fun t ht => ⟨H2, hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem codesA_H {C : Ctx} (hc : ExA.CodesA C (ExA.bodyA C)) (H : List (BitVec 64)) :
    ExA.CodesA (ctxH C H) (ExA.bodyA (ctxH C H)) :=
  ⟨hc.abs1, hc.fvarB, ⟨hc.fvr.fvr, hc.fvr.memoGet, hc.fvr.memoProbe, hc.fvr.memoSet, hc.fvr.memoIns⟩, hc.internApp,
    hc.internLam, hc.internForallE, hc.internLet, hc.internBVar, hc.internProj⟩

theorem qmo_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C)
    (hci : C.code.lookup fI = some (pmap kParams, inferE C fIB, .one))
    (hcI : C.code.lookup ExI.fInst1F = some ([pFu, pH, ExI.pV, ExI.pD].map (fun p => (p, ShapeHOL.one)),
      ExI.fastBody C, .one)) (hcI' : ExI.Codes C (ExI.body C))
    (hcfv : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one))
    (hcA : C.code.lookup ExA.fAbs1F = some ([pFu, ExA.pAd, ExI.pD, pH].map (fun p => (p, ShapeHOL.one)),
      ExA.fastBodyA C, .one)) (hcA' : ExA.CodesA C (ExA.bodyA C))
    (hI : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (inferE C fIB) s1 ((knot mode C n).infer d' e')
      (PostK (ctxH C H)))
    (s : AState) (d : Nat) (hd : d < 2 ^ 64) (ty b : EIdx) :
    SpecR (σ := σ) (Pre C s (ifaParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty, Enc.idxW b]))
      qmoBody s (ibLamIOT (knot mode C n) d ty b) (PostK C) := by
  refine specR_prologue (postK_locals C) (qmo_none C _) ?_
  by_cases hd2 : d < 2 ^ 62
  swap
  · have hl : ¬ (BitVec.ofNat 64 d < BitVec.ofNat 64 (2 ^ 62)) := by
      rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]; norm_num; omega
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get, ifaParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; first | exact hl | (rw [Nat.mod_eq_of_lt (show d < 18446744073709551616 by omega)]; omega))
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  have hl : BitVec.ofNat 64 d < BitVec.ofNat 64 (2 ^ 62) := by
    rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]; norm_num; omega
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ifaParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; first | exact hl | (rw [Nat.mod_eq_of_lt (show d < 18446744073709551616 by omega)]; omega))
    (fun _ => ?_) (fun h => absurd h (by decide))
  unfold ibLamIOT inferLamResult
  refine ILP.specR_internFVarI ra hok hcfv qmoV (vv ibT1) (vv kD) ty d (by omega) (by decide) (by simp +decide [Env.get, ifaParams, ctxEnv]) (by simp +decide [Env.get, ifaParams, ctxEnv])
    (fun fv s1 => ?_)
  refine ILP.callE_spec qmoO ExI.fInst1F [pFu, pH, ExI.pV, ExI.pD]
    [.const (BitVec.ofNat 64 coreWalkFuel), vv ibT2, vv qmoV, .const 0] (ExI.fastBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW b, Enc.idxW fv, BitVec.ofNat 64 0] (by decide) rfl (by decide) hcI
    ⟨rfl, by simp +decide [Env.get, ifaParams, ctxEnv], by simp, rfl, trivial⟩
    (ExI.fast_spec ra C hok hcI' s1 coreWalkFuel b fv 0 CV.coreWalkFuel_lt (by decide)) (fun ob s2 => ?_)
  refine specR_assignI qmoD1 _ (BitVec.ofNat 64 (d + 1)) (by decide)
    (by simp +decide [sev, Env.get, ifaParams, ctxEnv]; exact word_add1_eq d) ?_
  refine Big.specR_callKC qmoB fI kParams [vv kFu, vv qmoD1, vv qmoO] (inferE C fIB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 (d + 1), Enc.idxW ob] (by decide) rfl (by decide) hci
    ⟨by simp +decide [Env.get, ifaParams, ctxEnv], by simp, by simp, trivial⟩ (hI C.H s2 (d + 1) ob (List.prefix_refl _)) (fun bt s3 H3 hp3 _ => ?_)
  refine ILP.callE_spec (C := ctxH C H3) qmoA ExA.fAbs1F [pFu, ExA.pAd, ExI.pD, pH]
    [.const (BitVec.ofNat 64 coreWalkFuel), vv kD, .const 0, vv qmoB] (ExA.fastBodyA C)
    [BitVec.ofNat 64 coreWalkFuel, BitVec.ofNat 64 d, BitVec.ofNat 64 0, Enc.idxW bt] (by decide) rfl (by decide) hcA
    ⟨rfl, by simp +decide [Env.get, ifaParams, ctxEnv], rfl, by simp, trivial⟩
    (ExA.fastA_spec ra (ctxH C H3) (ctxOK_H hok H3) (codesA_H hcA' H3) s3 coreWalkFuel d 0 bt CV.coreWalkFuel_lt
      (by omega) (by decide)) (fun ab s4 => ?_)
  refine specR_congr (m' := internForallEE ty ab >>= fun r => pure r) (by simp) ?_
  refine specR_internForallEI ra (ctxOK_H hok H3) hcA'.internForallE qmoR (vv ibT1) (vv qmoA) ty ab (by decide)
    (by simp +decide [Env.get, ifaParams, ctxEnv]) (by simp) (fun r s5 => ?_)
  exact specR_returnI _ (Enc.idxW r) (by simp) (fun t ht => ⟨H3, hp3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
