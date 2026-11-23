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
def fIfaIO := ofString "inferForallIO"
def qfoA := ofString "qfon_a"
def qfoH := ofString "qfon_h"
def qfoU := ofString "qfon_u"
def qfoV := ofString "qfon_v"
def qfoO := ofString "qfon_o"
def qfoD1 := ofString "qfon_d1"
def qfoT := ofString "qfon_t"
def qfoW := ofString "qfon_w"
def qfoX := ofString "qfon_x"
def qfoI := ofString "qfon_i"
def qfoR := ofString "qfon_r"

@[simp] theorem qfo_qfoA_ne_qfoH : qfoA ≠ qfoH := by decide
@[simp] theorem qfo_qfoA_ne_qfoU : qfoA ≠ qfoU := by decide
@[simp] theorem qfo_qfoA_ne_qfoV : qfoA ≠ qfoV := by decide
@[simp] theorem qfo_qfoA_ne_qfoO : qfoA ≠ qfoO := by decide
@[simp] theorem qfo_qfoA_ne_qfoD1 : qfoA ≠ qfoD1 := by decide
@[simp] theorem qfo_qfoA_ne_qfoT : qfoA ≠ qfoT := by decide
@[simp] theorem qfo_qfoA_ne_qfoW : qfoA ≠ qfoW := by decide
@[simp] theorem qfo_qfoA_ne_qfoX : qfoA ≠ qfoX := by decide
@[simp] theorem qfo_qfoA_ne_qfoI : qfoA ≠ qfoI := by decide
@[simp] theorem qfo_qfoA_ne_qfoR : qfoA ≠ qfoR := by decide
@[simp] theorem qfo_qfoA_ne_kFu : qfoA ≠ kFu := by decide
@[simp] theorem qfo_kFu_ne_qfoA : kFu ≠ qfoA := by decide
@[simp] theorem qfo_qfoA_ne_kD : qfoA ≠ kD := by decide
@[simp] theorem qfo_kD_ne_qfoA : kD ≠ qfoA := by decide
@[simp] theorem qfo_qfoA_ne_ibT1 : qfoA ≠ ibT1 := by decide
@[simp] theorem qfo_ibT1_ne_qfoA : ibT1 ≠ qfoA := by decide
@[simp] theorem qfo_qfoA_ne_ibT2 : qfoA ≠ ibT2 := by decide
@[simp] theorem qfo_ibT2_ne_qfoA : ibT2 ≠ qfoA := by decide
@[simp] theorem qfo_qfoA_ne_lFl : qfoA ≠ lFl := by decide
@[simp] theorem qfo_lFl_ne_qfoA : lFl ≠ qfoA := by decide
@[simp] theorem qfo_qfoA_ne_lDh : qfoA ≠ lDh := by decide
@[simp] theorem qfo_lDh_ne_qfoA : lDh ≠ qfoA := by decide
@[simp] theorem qfo_qfoA_ne_lDt : qfoA ≠ lDt := by decide
@[simp] theorem qfo_lDt_ne_qfoA : lDt ≠ qfoA := by decide
@[simp] theorem qfo_qfoA_ne_lDg : qfoA ≠ lDg := by decide
@[simp] theorem qfo_lDg_ne_qfoA : lDg ≠ qfoA := by decide
@[simp] theorem qfo_qfoA_ne_lDi : qfoA ≠ lDi := by decide
@[simp] theorem qfo_lDi_ne_qfoA : lDi ≠ qfoA := by decide
@[simp] theorem qfo_qfoA_ne_lRp : qfoA ≠ lRp := by decide
@[simp] theorem qfo_lRp_ne_qfoA : lRp ≠ qfoA := by decide
@[simp] theorem qfo_qfoA_ne_lRn : qfoA ≠ lRn := by decide
@[simp] theorem qfo_lRn_ne_qfoA : lRn ≠ qfoA := by decide
@[simp] theorem qfo_qfoA_ne_lDir : qfoA ≠ lDir := by decide
@[simp] theorem qfo_lDir_ne_qfoA : lDir ≠ qfoA := by decide
@[simp] theorem qfo_qfoA_ne_lFle : qfoA ≠ lFle := by decide
@[simp] theorem qfo_lFle_ne_qfoA : lFle ≠ qfoA := by decide
@[simp] theorem qfo_qfoA_ne_lKb : qfoA ≠ lKb := by decide
@[simp] theorem qfo_lKb_ne_qfoA : lKb ≠ qfoA := by decide
@[simp] theorem qfo_qfoH_ne_qfoA : qfoH ≠ qfoA := by decide
@[simp] theorem qfo_qfoH_ne_qfoU : qfoH ≠ qfoU := by decide
@[simp] theorem qfo_qfoH_ne_qfoV : qfoH ≠ qfoV := by decide
@[simp] theorem qfo_qfoH_ne_qfoO : qfoH ≠ qfoO := by decide
@[simp] theorem qfo_qfoH_ne_qfoD1 : qfoH ≠ qfoD1 := by decide
@[simp] theorem qfo_qfoH_ne_qfoT : qfoH ≠ qfoT := by decide
@[simp] theorem qfo_qfoH_ne_qfoW : qfoH ≠ qfoW := by decide
@[simp] theorem qfo_qfoH_ne_qfoX : qfoH ≠ qfoX := by decide
@[simp] theorem qfo_qfoH_ne_qfoI : qfoH ≠ qfoI := by decide
@[simp] theorem qfo_qfoH_ne_qfoR : qfoH ≠ qfoR := by decide
@[simp] theorem qfo_qfoH_ne_kFu : qfoH ≠ kFu := by decide
@[simp] theorem qfo_kFu_ne_qfoH : kFu ≠ qfoH := by decide
@[simp] theorem qfo_qfoH_ne_kD : qfoH ≠ kD := by decide
@[simp] theorem qfo_kD_ne_qfoH : kD ≠ qfoH := by decide
@[simp] theorem qfo_qfoH_ne_ibT1 : qfoH ≠ ibT1 := by decide
@[simp] theorem qfo_ibT1_ne_qfoH : ibT1 ≠ qfoH := by decide
@[simp] theorem qfo_qfoH_ne_ibT2 : qfoH ≠ ibT2 := by decide
@[simp] theorem qfo_ibT2_ne_qfoH : ibT2 ≠ qfoH := by decide
@[simp] theorem qfo_qfoH_ne_lFl : qfoH ≠ lFl := by decide
@[simp] theorem qfo_lFl_ne_qfoH : lFl ≠ qfoH := by decide
@[simp] theorem qfo_qfoH_ne_lDh : qfoH ≠ lDh := by decide
@[simp] theorem qfo_lDh_ne_qfoH : lDh ≠ qfoH := by decide
@[simp] theorem qfo_qfoH_ne_lDt : qfoH ≠ lDt := by decide
@[simp] theorem qfo_lDt_ne_qfoH : lDt ≠ qfoH := by decide
@[simp] theorem qfo_qfoH_ne_lDg : qfoH ≠ lDg := by decide
@[simp] theorem qfo_lDg_ne_qfoH : lDg ≠ qfoH := by decide
@[simp] theorem qfo_qfoH_ne_lDi : qfoH ≠ lDi := by decide
@[simp] theorem qfo_lDi_ne_qfoH : lDi ≠ qfoH := by decide
@[simp] theorem qfo_qfoH_ne_lRp : qfoH ≠ lRp := by decide
@[simp] theorem qfo_lRp_ne_qfoH : lRp ≠ qfoH := by decide
@[simp] theorem qfo_qfoH_ne_lRn : qfoH ≠ lRn := by decide
@[simp] theorem qfo_lRn_ne_qfoH : lRn ≠ qfoH := by decide
@[simp] theorem qfo_qfoH_ne_lDir : qfoH ≠ lDir := by decide
@[simp] theorem qfo_lDir_ne_qfoH : lDir ≠ qfoH := by decide
@[simp] theorem qfo_qfoH_ne_lFle : qfoH ≠ lFle := by decide
@[simp] theorem qfo_lFle_ne_qfoH : lFle ≠ qfoH := by decide
@[simp] theorem qfo_qfoH_ne_lKb : qfoH ≠ lKb := by decide
@[simp] theorem qfo_lKb_ne_qfoH : lKb ≠ qfoH := by decide
@[simp] theorem qfo_qfoU_ne_qfoA : qfoU ≠ qfoA := by decide
@[simp] theorem qfo_qfoU_ne_qfoH : qfoU ≠ qfoH := by decide
@[simp] theorem qfo_qfoU_ne_qfoV : qfoU ≠ qfoV := by decide
@[simp] theorem qfo_qfoU_ne_qfoO : qfoU ≠ qfoO := by decide
@[simp] theorem qfo_qfoU_ne_qfoD1 : qfoU ≠ qfoD1 := by decide
@[simp] theorem qfo_qfoU_ne_qfoT : qfoU ≠ qfoT := by decide
@[simp] theorem qfo_qfoU_ne_qfoW : qfoU ≠ qfoW := by decide
@[simp] theorem qfo_qfoU_ne_qfoX : qfoU ≠ qfoX := by decide
@[simp] theorem qfo_qfoU_ne_qfoI : qfoU ≠ qfoI := by decide
@[simp] theorem qfo_qfoU_ne_qfoR : qfoU ≠ qfoR := by decide
@[simp] theorem qfo_qfoU_ne_kFu : qfoU ≠ kFu := by decide
@[simp] theorem qfo_kFu_ne_qfoU : kFu ≠ qfoU := by decide
@[simp] theorem qfo_qfoU_ne_kD : qfoU ≠ kD := by decide
@[simp] theorem qfo_kD_ne_qfoU : kD ≠ qfoU := by decide
@[simp] theorem qfo_qfoU_ne_ibT1 : qfoU ≠ ibT1 := by decide
@[simp] theorem qfo_ibT1_ne_qfoU : ibT1 ≠ qfoU := by decide
@[simp] theorem qfo_qfoU_ne_ibT2 : qfoU ≠ ibT2 := by decide
@[simp] theorem qfo_ibT2_ne_qfoU : ibT2 ≠ qfoU := by decide
@[simp] theorem qfo_qfoU_ne_lFl : qfoU ≠ lFl := by decide
@[simp] theorem qfo_lFl_ne_qfoU : lFl ≠ qfoU := by decide
@[simp] theorem qfo_qfoU_ne_lDh : qfoU ≠ lDh := by decide
@[simp] theorem qfo_lDh_ne_qfoU : lDh ≠ qfoU := by decide
@[simp] theorem qfo_qfoU_ne_lDt : qfoU ≠ lDt := by decide
@[simp] theorem qfo_lDt_ne_qfoU : lDt ≠ qfoU := by decide
@[simp] theorem qfo_qfoU_ne_lDg : qfoU ≠ lDg := by decide
@[simp] theorem qfo_lDg_ne_qfoU : lDg ≠ qfoU := by decide
@[simp] theorem qfo_qfoU_ne_lDi : qfoU ≠ lDi := by decide
@[simp] theorem qfo_lDi_ne_qfoU : lDi ≠ qfoU := by decide
@[simp] theorem qfo_qfoU_ne_lRp : qfoU ≠ lRp := by decide
@[simp] theorem qfo_lRp_ne_qfoU : lRp ≠ qfoU := by decide
@[simp] theorem qfo_qfoU_ne_lRn : qfoU ≠ lRn := by decide
@[simp] theorem qfo_lRn_ne_qfoU : lRn ≠ qfoU := by decide
@[simp] theorem qfo_qfoU_ne_lDir : qfoU ≠ lDir := by decide
@[simp] theorem qfo_lDir_ne_qfoU : lDir ≠ qfoU := by decide
@[simp] theorem qfo_qfoU_ne_lFle : qfoU ≠ lFle := by decide
@[simp] theorem qfo_lFle_ne_qfoU : lFle ≠ qfoU := by decide
@[simp] theorem qfo_qfoU_ne_lKb : qfoU ≠ lKb := by decide
@[simp] theorem qfo_lKb_ne_qfoU : lKb ≠ qfoU := by decide
@[simp] theorem qfo_qfoV_ne_qfoA : qfoV ≠ qfoA := by decide
@[simp] theorem qfo_qfoV_ne_qfoH : qfoV ≠ qfoH := by decide
@[simp] theorem qfo_qfoV_ne_qfoU : qfoV ≠ qfoU := by decide
@[simp] theorem qfo_qfoV_ne_qfoO : qfoV ≠ qfoO := by decide
@[simp] theorem qfo_qfoV_ne_qfoD1 : qfoV ≠ qfoD1 := by decide
@[simp] theorem qfo_qfoV_ne_qfoT : qfoV ≠ qfoT := by decide
@[simp] theorem qfo_qfoV_ne_qfoW : qfoV ≠ qfoW := by decide
@[simp] theorem qfo_qfoV_ne_qfoX : qfoV ≠ qfoX := by decide
@[simp] theorem qfo_qfoV_ne_qfoI : qfoV ≠ qfoI := by decide
@[simp] theorem qfo_qfoV_ne_qfoR : qfoV ≠ qfoR := by decide
@[simp] theorem qfo_qfoV_ne_kFu : qfoV ≠ kFu := by decide
@[simp] theorem qfo_kFu_ne_qfoV : kFu ≠ qfoV := by decide
@[simp] theorem qfo_qfoV_ne_kD : qfoV ≠ kD := by decide
@[simp] theorem qfo_kD_ne_qfoV : kD ≠ qfoV := by decide
@[simp] theorem qfo_qfoV_ne_ibT1 : qfoV ≠ ibT1 := by decide
@[simp] theorem qfo_ibT1_ne_qfoV : ibT1 ≠ qfoV := by decide
@[simp] theorem qfo_qfoV_ne_ibT2 : qfoV ≠ ibT2 := by decide
@[simp] theorem qfo_ibT2_ne_qfoV : ibT2 ≠ qfoV := by decide
@[simp] theorem qfo_qfoV_ne_lFl : qfoV ≠ lFl := by decide
@[simp] theorem qfo_lFl_ne_qfoV : lFl ≠ qfoV := by decide
@[simp] theorem qfo_qfoV_ne_lDh : qfoV ≠ lDh := by decide
@[simp] theorem qfo_lDh_ne_qfoV : lDh ≠ qfoV := by decide
@[simp] theorem qfo_qfoV_ne_lDt : qfoV ≠ lDt := by decide
@[simp] theorem qfo_lDt_ne_qfoV : lDt ≠ qfoV := by decide
@[simp] theorem qfo_qfoV_ne_lDg : qfoV ≠ lDg := by decide
@[simp] theorem qfo_lDg_ne_qfoV : lDg ≠ qfoV := by decide
@[simp] theorem qfo_qfoV_ne_lDi : qfoV ≠ lDi := by decide
@[simp] theorem qfo_lDi_ne_qfoV : lDi ≠ qfoV := by decide
@[simp] theorem qfo_qfoV_ne_lRp : qfoV ≠ lRp := by decide
@[simp] theorem qfo_lRp_ne_qfoV : lRp ≠ qfoV := by decide
@[simp] theorem qfo_qfoV_ne_lRn : qfoV ≠ lRn := by decide
@[simp] theorem qfo_lRn_ne_qfoV : lRn ≠ qfoV := by decide
@[simp] theorem qfo_qfoV_ne_lDir : qfoV ≠ lDir := by decide
@[simp] theorem qfo_lDir_ne_qfoV : lDir ≠ qfoV := by decide
@[simp] theorem qfo_qfoV_ne_lFle : qfoV ≠ lFle := by decide
@[simp] theorem qfo_lFle_ne_qfoV : lFle ≠ qfoV := by decide
@[simp] theorem qfo_qfoV_ne_lKb : qfoV ≠ lKb := by decide
@[simp] theorem qfo_lKb_ne_qfoV : lKb ≠ qfoV := by decide
@[simp] theorem qfo_qfoO_ne_qfoA : qfoO ≠ qfoA := by decide
@[simp] theorem qfo_qfoO_ne_qfoH : qfoO ≠ qfoH := by decide
@[simp] theorem qfo_qfoO_ne_qfoU : qfoO ≠ qfoU := by decide
@[simp] theorem qfo_qfoO_ne_qfoV : qfoO ≠ qfoV := by decide
@[simp] theorem qfo_qfoO_ne_qfoD1 : qfoO ≠ qfoD1 := by decide
@[simp] theorem qfo_qfoO_ne_qfoT : qfoO ≠ qfoT := by decide
@[simp] theorem qfo_qfoO_ne_qfoW : qfoO ≠ qfoW := by decide
@[simp] theorem qfo_qfoO_ne_qfoX : qfoO ≠ qfoX := by decide
@[simp] theorem qfo_qfoO_ne_qfoI : qfoO ≠ qfoI := by decide
@[simp] theorem qfo_qfoO_ne_qfoR : qfoO ≠ qfoR := by decide
@[simp] theorem qfo_qfoO_ne_kFu : qfoO ≠ kFu := by decide
@[simp] theorem qfo_kFu_ne_qfoO : kFu ≠ qfoO := by decide
@[simp] theorem qfo_qfoO_ne_kD : qfoO ≠ kD := by decide
@[simp] theorem qfo_kD_ne_qfoO : kD ≠ qfoO := by decide
@[simp] theorem qfo_qfoO_ne_ibT1 : qfoO ≠ ibT1 := by decide
@[simp] theorem qfo_ibT1_ne_qfoO : ibT1 ≠ qfoO := by decide
@[simp] theorem qfo_qfoO_ne_ibT2 : qfoO ≠ ibT2 := by decide
@[simp] theorem qfo_ibT2_ne_qfoO : ibT2 ≠ qfoO := by decide
@[simp] theorem qfo_qfoO_ne_lFl : qfoO ≠ lFl := by decide
@[simp] theorem qfo_lFl_ne_qfoO : lFl ≠ qfoO := by decide
@[simp] theorem qfo_qfoO_ne_lDh : qfoO ≠ lDh := by decide
@[simp] theorem qfo_lDh_ne_qfoO : lDh ≠ qfoO := by decide
@[simp] theorem qfo_qfoO_ne_lDt : qfoO ≠ lDt := by decide
@[simp] theorem qfo_lDt_ne_qfoO : lDt ≠ qfoO := by decide
@[simp] theorem qfo_qfoO_ne_lDg : qfoO ≠ lDg := by decide
@[simp] theorem qfo_lDg_ne_qfoO : lDg ≠ qfoO := by decide
@[simp] theorem qfo_qfoO_ne_lDi : qfoO ≠ lDi := by decide
@[simp] theorem qfo_lDi_ne_qfoO : lDi ≠ qfoO := by decide
@[simp] theorem qfo_qfoO_ne_lRp : qfoO ≠ lRp := by decide
@[simp] theorem qfo_lRp_ne_qfoO : lRp ≠ qfoO := by decide
@[simp] theorem qfo_qfoO_ne_lRn : qfoO ≠ lRn := by decide
@[simp] theorem qfo_lRn_ne_qfoO : lRn ≠ qfoO := by decide
@[simp] theorem qfo_qfoO_ne_lDir : qfoO ≠ lDir := by decide
@[simp] theorem qfo_lDir_ne_qfoO : lDir ≠ qfoO := by decide
@[simp] theorem qfo_qfoO_ne_lFle : qfoO ≠ lFle := by decide
@[simp] theorem qfo_lFle_ne_qfoO : lFle ≠ qfoO := by decide
@[simp] theorem qfo_qfoO_ne_lKb : qfoO ≠ lKb := by decide
@[simp] theorem qfo_lKb_ne_qfoO : lKb ≠ qfoO := by decide
@[simp] theorem qfo_qfoD1_ne_qfoA : qfoD1 ≠ qfoA := by decide
@[simp] theorem qfo_qfoD1_ne_qfoH : qfoD1 ≠ qfoH := by decide
@[simp] theorem qfo_qfoD1_ne_qfoU : qfoD1 ≠ qfoU := by decide
@[simp] theorem qfo_qfoD1_ne_qfoV : qfoD1 ≠ qfoV := by decide
@[simp] theorem qfo_qfoD1_ne_qfoO : qfoD1 ≠ qfoO := by decide
@[simp] theorem qfo_qfoD1_ne_qfoT : qfoD1 ≠ qfoT := by decide
@[simp] theorem qfo_qfoD1_ne_qfoW : qfoD1 ≠ qfoW := by decide
@[simp] theorem qfo_qfoD1_ne_qfoX : qfoD1 ≠ qfoX := by decide
@[simp] theorem qfo_qfoD1_ne_qfoI : qfoD1 ≠ qfoI := by decide
@[simp] theorem qfo_qfoD1_ne_qfoR : qfoD1 ≠ qfoR := by decide
@[simp] theorem qfo_qfoD1_ne_kFu : qfoD1 ≠ kFu := by decide
@[simp] theorem qfo_kFu_ne_qfoD1 : kFu ≠ qfoD1 := by decide
@[simp] theorem qfo_qfoD1_ne_kD : qfoD1 ≠ kD := by decide
@[simp] theorem qfo_kD_ne_qfoD1 : kD ≠ qfoD1 := by decide
@[simp] theorem qfo_qfoD1_ne_ibT1 : qfoD1 ≠ ibT1 := by decide
@[simp] theorem qfo_ibT1_ne_qfoD1 : ibT1 ≠ qfoD1 := by decide
@[simp] theorem qfo_qfoD1_ne_ibT2 : qfoD1 ≠ ibT2 := by decide
@[simp] theorem qfo_ibT2_ne_qfoD1 : ibT2 ≠ qfoD1 := by decide
@[simp] theorem qfo_qfoD1_ne_lFl : qfoD1 ≠ lFl := by decide
@[simp] theorem qfo_lFl_ne_qfoD1 : lFl ≠ qfoD1 := by decide
@[simp] theorem qfo_qfoD1_ne_lDh : qfoD1 ≠ lDh := by decide
@[simp] theorem qfo_lDh_ne_qfoD1 : lDh ≠ qfoD1 := by decide
@[simp] theorem qfo_qfoD1_ne_lDt : qfoD1 ≠ lDt := by decide
@[simp] theorem qfo_lDt_ne_qfoD1 : lDt ≠ qfoD1 := by decide
@[simp] theorem qfo_qfoD1_ne_lDg : qfoD1 ≠ lDg := by decide
@[simp] theorem qfo_lDg_ne_qfoD1 : lDg ≠ qfoD1 := by decide
@[simp] theorem qfo_qfoD1_ne_lDi : qfoD1 ≠ lDi := by decide
@[simp] theorem qfo_lDi_ne_qfoD1 : lDi ≠ qfoD1 := by decide
@[simp] theorem qfo_qfoD1_ne_lRp : qfoD1 ≠ lRp := by decide
@[simp] theorem qfo_lRp_ne_qfoD1 : lRp ≠ qfoD1 := by decide
@[simp] theorem qfo_qfoD1_ne_lRn : qfoD1 ≠ lRn := by decide
@[simp] theorem qfo_lRn_ne_qfoD1 : lRn ≠ qfoD1 := by decide
@[simp] theorem qfo_qfoD1_ne_lDir : qfoD1 ≠ lDir := by decide
@[simp] theorem qfo_lDir_ne_qfoD1 : lDir ≠ qfoD1 := by decide
@[simp] theorem qfo_qfoD1_ne_lFle : qfoD1 ≠ lFle := by decide
@[simp] theorem qfo_lFle_ne_qfoD1 : lFle ≠ qfoD1 := by decide
@[simp] theorem qfo_qfoD1_ne_lKb : qfoD1 ≠ lKb := by decide
@[simp] theorem qfo_lKb_ne_qfoD1 : lKb ≠ qfoD1 := by decide
@[simp] theorem qfo_qfoT_ne_qfoA : qfoT ≠ qfoA := by decide
@[simp] theorem qfo_qfoT_ne_qfoH : qfoT ≠ qfoH := by decide
@[simp] theorem qfo_qfoT_ne_qfoU : qfoT ≠ qfoU := by decide
@[simp] theorem qfo_qfoT_ne_qfoV : qfoT ≠ qfoV := by decide
@[simp] theorem qfo_qfoT_ne_qfoO : qfoT ≠ qfoO := by decide
@[simp] theorem qfo_qfoT_ne_qfoD1 : qfoT ≠ qfoD1 := by decide
@[simp] theorem qfo_qfoT_ne_qfoW : qfoT ≠ qfoW := by decide
@[simp] theorem qfo_qfoT_ne_qfoX : qfoT ≠ qfoX := by decide
@[simp] theorem qfo_qfoT_ne_qfoI : qfoT ≠ qfoI := by decide
@[simp] theorem qfo_qfoT_ne_qfoR : qfoT ≠ qfoR := by decide
@[simp] theorem qfo_qfoT_ne_kFu : qfoT ≠ kFu := by decide
@[simp] theorem qfo_kFu_ne_qfoT : kFu ≠ qfoT := by decide
@[simp] theorem qfo_qfoT_ne_kD : qfoT ≠ kD := by decide
@[simp] theorem qfo_kD_ne_qfoT : kD ≠ qfoT := by decide
@[simp] theorem qfo_qfoT_ne_ibT1 : qfoT ≠ ibT1 := by decide
@[simp] theorem qfo_ibT1_ne_qfoT : ibT1 ≠ qfoT := by decide
@[simp] theorem qfo_qfoT_ne_ibT2 : qfoT ≠ ibT2 := by decide
@[simp] theorem qfo_ibT2_ne_qfoT : ibT2 ≠ qfoT := by decide
@[simp] theorem qfo_qfoT_ne_lFl : qfoT ≠ lFl := by decide
@[simp] theorem qfo_lFl_ne_qfoT : lFl ≠ qfoT := by decide
@[simp] theorem qfo_qfoT_ne_lDh : qfoT ≠ lDh := by decide
@[simp] theorem qfo_lDh_ne_qfoT : lDh ≠ qfoT := by decide
@[simp] theorem qfo_qfoT_ne_lDt : qfoT ≠ lDt := by decide
@[simp] theorem qfo_lDt_ne_qfoT : lDt ≠ qfoT := by decide
@[simp] theorem qfo_qfoT_ne_lDg : qfoT ≠ lDg := by decide
@[simp] theorem qfo_lDg_ne_qfoT : lDg ≠ qfoT := by decide
@[simp] theorem qfo_qfoT_ne_lDi : qfoT ≠ lDi := by decide
@[simp] theorem qfo_lDi_ne_qfoT : lDi ≠ qfoT := by decide
@[simp] theorem qfo_qfoT_ne_lRp : qfoT ≠ lRp := by decide
@[simp] theorem qfo_lRp_ne_qfoT : lRp ≠ qfoT := by decide
@[simp] theorem qfo_qfoT_ne_lRn : qfoT ≠ lRn := by decide
@[simp] theorem qfo_lRn_ne_qfoT : lRn ≠ qfoT := by decide
@[simp] theorem qfo_qfoT_ne_lDir : qfoT ≠ lDir := by decide
@[simp] theorem qfo_lDir_ne_qfoT : lDir ≠ qfoT := by decide
@[simp] theorem qfo_qfoT_ne_lFle : qfoT ≠ lFle := by decide
@[simp] theorem qfo_lFle_ne_qfoT : lFle ≠ qfoT := by decide
@[simp] theorem qfo_qfoT_ne_lKb : qfoT ≠ lKb := by decide
@[simp] theorem qfo_lKb_ne_qfoT : lKb ≠ qfoT := by decide
@[simp] theorem qfo_qfoW_ne_qfoA : qfoW ≠ qfoA := by decide
@[simp] theorem qfo_qfoW_ne_qfoH : qfoW ≠ qfoH := by decide
@[simp] theorem qfo_qfoW_ne_qfoU : qfoW ≠ qfoU := by decide
@[simp] theorem qfo_qfoW_ne_qfoV : qfoW ≠ qfoV := by decide
@[simp] theorem qfo_qfoW_ne_qfoO : qfoW ≠ qfoO := by decide
@[simp] theorem qfo_qfoW_ne_qfoD1 : qfoW ≠ qfoD1 := by decide
@[simp] theorem qfo_qfoW_ne_qfoT : qfoW ≠ qfoT := by decide
@[simp] theorem qfo_qfoW_ne_qfoX : qfoW ≠ qfoX := by decide
@[simp] theorem qfo_qfoW_ne_qfoI : qfoW ≠ qfoI := by decide
@[simp] theorem qfo_qfoW_ne_qfoR : qfoW ≠ qfoR := by decide
@[simp] theorem qfo_qfoW_ne_kFu : qfoW ≠ kFu := by decide
@[simp] theorem qfo_kFu_ne_qfoW : kFu ≠ qfoW := by decide
@[simp] theorem qfo_qfoW_ne_kD : qfoW ≠ kD := by decide
@[simp] theorem qfo_kD_ne_qfoW : kD ≠ qfoW := by decide
@[simp] theorem qfo_qfoW_ne_ibT1 : qfoW ≠ ibT1 := by decide
@[simp] theorem qfo_ibT1_ne_qfoW : ibT1 ≠ qfoW := by decide
@[simp] theorem qfo_qfoW_ne_ibT2 : qfoW ≠ ibT2 := by decide
@[simp] theorem qfo_ibT2_ne_qfoW : ibT2 ≠ qfoW := by decide
@[simp] theorem qfo_qfoW_ne_lFl : qfoW ≠ lFl := by decide
@[simp] theorem qfo_lFl_ne_qfoW : lFl ≠ qfoW := by decide
@[simp] theorem qfo_qfoW_ne_lDh : qfoW ≠ lDh := by decide
@[simp] theorem qfo_lDh_ne_qfoW : lDh ≠ qfoW := by decide
@[simp] theorem qfo_qfoW_ne_lDt : qfoW ≠ lDt := by decide
@[simp] theorem qfo_lDt_ne_qfoW : lDt ≠ qfoW := by decide
@[simp] theorem qfo_qfoW_ne_lDg : qfoW ≠ lDg := by decide
@[simp] theorem qfo_lDg_ne_qfoW : lDg ≠ qfoW := by decide
@[simp] theorem qfo_qfoW_ne_lDi : qfoW ≠ lDi := by decide
@[simp] theorem qfo_lDi_ne_qfoW : lDi ≠ qfoW := by decide
@[simp] theorem qfo_qfoW_ne_lRp : qfoW ≠ lRp := by decide
@[simp] theorem qfo_lRp_ne_qfoW : lRp ≠ qfoW := by decide
@[simp] theorem qfo_qfoW_ne_lRn : qfoW ≠ lRn := by decide
@[simp] theorem qfo_lRn_ne_qfoW : lRn ≠ qfoW := by decide
@[simp] theorem qfo_qfoW_ne_lDir : qfoW ≠ lDir := by decide
@[simp] theorem qfo_lDir_ne_qfoW : lDir ≠ qfoW := by decide
@[simp] theorem qfo_qfoW_ne_lFle : qfoW ≠ lFle := by decide
@[simp] theorem qfo_lFle_ne_qfoW : lFle ≠ qfoW := by decide
@[simp] theorem qfo_qfoW_ne_lKb : qfoW ≠ lKb := by decide
@[simp] theorem qfo_lKb_ne_qfoW : lKb ≠ qfoW := by decide
@[simp] theorem qfo_qfoX_ne_qfoA : qfoX ≠ qfoA := by decide
@[simp] theorem qfo_qfoX_ne_qfoH : qfoX ≠ qfoH := by decide
@[simp] theorem qfo_qfoX_ne_qfoU : qfoX ≠ qfoU := by decide
@[simp] theorem qfo_qfoX_ne_qfoV : qfoX ≠ qfoV := by decide
@[simp] theorem qfo_qfoX_ne_qfoO : qfoX ≠ qfoO := by decide
@[simp] theorem qfo_qfoX_ne_qfoD1 : qfoX ≠ qfoD1 := by decide
@[simp] theorem qfo_qfoX_ne_qfoT : qfoX ≠ qfoT := by decide
@[simp] theorem qfo_qfoX_ne_qfoW : qfoX ≠ qfoW := by decide
@[simp] theorem qfo_qfoX_ne_qfoI : qfoX ≠ qfoI := by decide
@[simp] theorem qfo_qfoX_ne_qfoR : qfoX ≠ qfoR := by decide
@[simp] theorem qfo_qfoX_ne_kFu : qfoX ≠ kFu := by decide
@[simp] theorem qfo_kFu_ne_qfoX : kFu ≠ qfoX := by decide
@[simp] theorem qfo_qfoX_ne_kD : qfoX ≠ kD := by decide
@[simp] theorem qfo_kD_ne_qfoX : kD ≠ qfoX := by decide
@[simp] theorem qfo_qfoX_ne_ibT1 : qfoX ≠ ibT1 := by decide
@[simp] theorem qfo_ibT1_ne_qfoX : ibT1 ≠ qfoX := by decide
@[simp] theorem qfo_qfoX_ne_ibT2 : qfoX ≠ ibT2 := by decide
@[simp] theorem qfo_ibT2_ne_qfoX : ibT2 ≠ qfoX := by decide
@[simp] theorem qfo_qfoX_ne_lFl : qfoX ≠ lFl := by decide
@[simp] theorem qfo_lFl_ne_qfoX : lFl ≠ qfoX := by decide
@[simp] theorem qfo_qfoX_ne_lDh : qfoX ≠ lDh := by decide
@[simp] theorem qfo_lDh_ne_qfoX : lDh ≠ qfoX := by decide
@[simp] theorem qfo_qfoX_ne_lDt : qfoX ≠ lDt := by decide
@[simp] theorem qfo_lDt_ne_qfoX : lDt ≠ qfoX := by decide
@[simp] theorem qfo_qfoX_ne_lDg : qfoX ≠ lDg := by decide
@[simp] theorem qfo_lDg_ne_qfoX : lDg ≠ qfoX := by decide
@[simp] theorem qfo_qfoX_ne_lDi : qfoX ≠ lDi := by decide
@[simp] theorem qfo_lDi_ne_qfoX : lDi ≠ qfoX := by decide
@[simp] theorem qfo_qfoX_ne_lRp : qfoX ≠ lRp := by decide
@[simp] theorem qfo_lRp_ne_qfoX : lRp ≠ qfoX := by decide
@[simp] theorem qfo_qfoX_ne_lRn : qfoX ≠ lRn := by decide
@[simp] theorem qfo_lRn_ne_qfoX : lRn ≠ qfoX := by decide
@[simp] theorem qfo_qfoX_ne_lDir : qfoX ≠ lDir := by decide
@[simp] theorem qfo_lDir_ne_qfoX : lDir ≠ qfoX := by decide
@[simp] theorem qfo_qfoX_ne_lFle : qfoX ≠ lFle := by decide
@[simp] theorem qfo_lFle_ne_qfoX : lFle ≠ qfoX := by decide
@[simp] theorem qfo_qfoX_ne_lKb : qfoX ≠ lKb := by decide
@[simp] theorem qfo_lKb_ne_qfoX : lKb ≠ qfoX := by decide
@[simp] theorem qfo_qfoI_ne_qfoA : qfoI ≠ qfoA := by decide
@[simp] theorem qfo_qfoI_ne_qfoH : qfoI ≠ qfoH := by decide
@[simp] theorem qfo_qfoI_ne_qfoU : qfoI ≠ qfoU := by decide
@[simp] theorem qfo_qfoI_ne_qfoV : qfoI ≠ qfoV := by decide
@[simp] theorem qfo_qfoI_ne_qfoO : qfoI ≠ qfoO := by decide
@[simp] theorem qfo_qfoI_ne_qfoD1 : qfoI ≠ qfoD1 := by decide
@[simp] theorem qfo_qfoI_ne_qfoT : qfoI ≠ qfoT := by decide
@[simp] theorem qfo_qfoI_ne_qfoW : qfoI ≠ qfoW := by decide
@[simp] theorem qfo_qfoI_ne_qfoX : qfoI ≠ qfoX := by decide
@[simp] theorem qfo_qfoI_ne_qfoR : qfoI ≠ qfoR := by decide
@[simp] theorem qfo_qfoI_ne_kFu : qfoI ≠ kFu := by decide
@[simp] theorem qfo_kFu_ne_qfoI : kFu ≠ qfoI := by decide
@[simp] theorem qfo_qfoI_ne_kD : qfoI ≠ kD := by decide
@[simp] theorem qfo_kD_ne_qfoI : kD ≠ qfoI := by decide
@[simp] theorem qfo_qfoI_ne_ibT1 : qfoI ≠ ibT1 := by decide
@[simp] theorem qfo_ibT1_ne_qfoI : ibT1 ≠ qfoI := by decide
@[simp] theorem qfo_qfoI_ne_ibT2 : qfoI ≠ ibT2 := by decide
@[simp] theorem qfo_ibT2_ne_qfoI : ibT2 ≠ qfoI := by decide
@[simp] theorem qfo_qfoI_ne_lFl : qfoI ≠ lFl := by decide
@[simp] theorem qfo_lFl_ne_qfoI : lFl ≠ qfoI := by decide
@[simp] theorem qfo_qfoI_ne_lDh : qfoI ≠ lDh := by decide
@[simp] theorem qfo_lDh_ne_qfoI : lDh ≠ qfoI := by decide
@[simp] theorem qfo_qfoI_ne_lDt : qfoI ≠ lDt := by decide
@[simp] theorem qfo_lDt_ne_qfoI : lDt ≠ qfoI := by decide
@[simp] theorem qfo_qfoI_ne_lDg : qfoI ≠ lDg := by decide
@[simp] theorem qfo_lDg_ne_qfoI : lDg ≠ qfoI := by decide
@[simp] theorem qfo_qfoI_ne_lDi : qfoI ≠ lDi := by decide
@[simp] theorem qfo_lDi_ne_qfoI : lDi ≠ qfoI := by decide
@[simp] theorem qfo_qfoI_ne_lRp : qfoI ≠ lRp := by decide
@[simp] theorem qfo_lRp_ne_qfoI : lRp ≠ qfoI := by decide
@[simp] theorem qfo_qfoI_ne_lRn : qfoI ≠ lRn := by decide
@[simp] theorem qfo_lRn_ne_qfoI : lRn ≠ qfoI := by decide
@[simp] theorem qfo_qfoI_ne_lDir : qfoI ≠ lDir := by decide
@[simp] theorem qfo_lDir_ne_qfoI : lDir ≠ qfoI := by decide
@[simp] theorem qfo_qfoI_ne_lFle : qfoI ≠ lFle := by decide
@[simp] theorem qfo_lFle_ne_qfoI : lFle ≠ qfoI := by decide
@[simp] theorem qfo_qfoI_ne_lKb : qfoI ≠ lKb := by decide
@[simp] theorem qfo_lKb_ne_qfoI : lKb ≠ qfoI := by decide
@[simp] theorem qfo_qfoR_ne_qfoA : qfoR ≠ qfoA := by decide
@[simp] theorem qfo_qfoR_ne_qfoH : qfoR ≠ qfoH := by decide
@[simp] theorem qfo_qfoR_ne_qfoU : qfoR ≠ qfoU := by decide
@[simp] theorem qfo_qfoR_ne_qfoV : qfoR ≠ qfoV := by decide
@[simp] theorem qfo_qfoR_ne_qfoO : qfoR ≠ qfoO := by decide
@[simp] theorem qfo_qfoR_ne_qfoD1 : qfoR ≠ qfoD1 := by decide
@[simp] theorem qfo_qfoR_ne_qfoT : qfoR ≠ qfoT := by decide
@[simp] theorem qfo_qfoR_ne_qfoW : qfoR ≠ qfoW := by decide
@[simp] theorem qfo_qfoR_ne_qfoX : qfoR ≠ qfoX := by decide
@[simp] theorem qfo_qfoR_ne_qfoI : qfoR ≠ qfoI := by decide
@[simp] theorem qfo_qfoR_ne_kFu : qfoR ≠ kFu := by decide
@[simp] theorem qfo_kFu_ne_qfoR : kFu ≠ qfoR := by decide
@[simp] theorem qfo_qfoR_ne_kD : qfoR ≠ kD := by decide
@[simp] theorem qfo_kD_ne_qfoR : kD ≠ qfoR := by decide
@[simp] theorem qfo_qfoR_ne_ibT1 : qfoR ≠ ibT1 := by decide
@[simp] theorem qfo_ibT1_ne_qfoR : ibT1 ≠ qfoR := by decide
@[simp] theorem qfo_qfoR_ne_ibT2 : qfoR ≠ ibT2 := by decide
@[simp] theorem qfo_ibT2_ne_qfoR : ibT2 ≠ qfoR := by decide
@[simp] theorem qfo_qfoR_ne_lFl : qfoR ≠ lFl := by decide
@[simp] theorem qfo_lFl_ne_qfoR : lFl ≠ qfoR := by decide
@[simp] theorem qfo_qfoR_ne_lDh : qfoR ≠ lDh := by decide
@[simp] theorem qfo_lDh_ne_qfoR : lDh ≠ qfoR := by decide
@[simp] theorem qfo_qfoR_ne_lDt : qfoR ≠ lDt := by decide
@[simp] theorem qfo_lDt_ne_qfoR : lDt ≠ qfoR := by decide
@[simp] theorem qfo_qfoR_ne_lDg : qfoR ≠ lDg := by decide
@[simp] theorem qfo_lDg_ne_qfoR : lDg ≠ qfoR := by decide
@[simp] theorem qfo_qfoR_ne_lDi : qfoR ≠ lDi := by decide
@[simp] theorem qfo_lDi_ne_qfoR : lDi ≠ qfoR := by decide
@[simp] theorem qfo_qfoR_ne_lRp : qfoR ≠ lRp := by decide
@[simp] theorem qfo_lRp_ne_qfoR : lRp ≠ qfoR := by decide
@[simp] theorem qfo_qfoR_ne_lRn : qfoR ≠ lRn := by decide
@[simp] theorem qfo_lRn_ne_qfoR : lRn ≠ qfoR := by decide
@[simp] theorem qfo_qfoR_ne_lDir : qfoR ≠ lDir := by decide
@[simp] theorem qfo_lDir_ne_qfoR : lDir ≠ qfoR := by decide
@[simp] theorem qfo_qfoR_ne_lFle : qfoR ≠ lFle := by decide
@[simp] theorem qfo_lFle_ne_qfoR : lFle ≠ qfoR := by decide
@[simp] theorem qfo_qfoR_ne_lKb : qfoR ≠ lKb := by decide
@[simp] theorem qfo_lKb_ne_qfoR : lKb ≠ qfoR := by decide

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
def ltoBody : ProgHOL 64 := prologue ltoLocals (.seq (.call (some (some (.local, ltoO), none)) ExI.fInst1F [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv ibB1), (vv ibV1), (.const 0)]) (.seq (.call (some (some (.local, ltoR), none)) fIO [(vv kFu), (vv kD), (vv ltoO)]) (.return (vv ltoR))))

def qmoLocals : List MlS := [qmoV, qmoO, qmoD1, qmoB, qmoA, qmoR]
def qmoBody : ProgHOL 64 := prologue qmoLocals (.ite (.cmp .lower (vv kD) (.const (BitVec.ofNat 64 (2 ^ 62)))) (.seq (.call (some (some (.local, qmoV), none)) fInternFVar [(vv ibT1), (vv kD)]) (.seq (.call (some (some (.local, qmoO), none)) ExI.fInst1F [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv ibT2), (vv qmoV), (.const 0)]) (.seq (.assign .local qmoD1 (.op .add [(vv kD), (.const 1)])) (.seq (.call (some (some (.local, qmoB), none)) fIO [(vv kFu), (vv qmoD1), (vv qmoO)]) (.seq (.call (some (some (.local, qmoA), none)) ExA.fAbs1F [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv kD), (.const 0), (vv qmoB)]) (.seq (.call (some (some (.local, qmoR), none)) fInternForallE [(vv ibT1), (vv qmoA)]) (.return (vv qmoR)))))))) hang)

def ibForallIOT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (ty body : EIdx) : AM EIdx := do
  let hh ← r.whnf depth (← r.infer depth ty)
  if hh.tag == ETag.sort then
    match ← view hh with
    | .sort u => do
      let fv ← internE (.fvar depth ty)
      let ob ← instantiate1Fast coreWalkFuel body fv 0
      let v ← ensureSort r fe (depth + 1) (← r.infer (depth + 1) ob)
      let iu ← internLNode (.imax u v)
      internE (.sort iu)
    | _ => fail (.invalid "expected a sort")
  else fail (.invalid "expected a sort")

def qfoLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, qfoA, qfoH, qfoU, qfoV, qfoO, qfoD1, qfoT, qfoW, qfoX, qfoI, qfoR]
def qfoBody : ProgHOL 64 := prologue qfoLocals (.ite (.cmp .lower (vv kD) (.const (BitVec.ofNat 64 (2 ^ 62)))) (.seq (.call (some (some (.local, qfoA), none)) fIO [(vv kFu), (vv kD), (vv ibT1)]) (.seq (.call (some (some (.local, qfoH), none)) fW [(vv kFu), (vv kD), (vv qfoA)]) (.ite (tagIsE qfoH 2) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv qfoH)) (.seq eViewP (.seq (.assign .local qfoU (.load .one (vv lRp))) (.seq (.call (some (some (.local, qfoV), none)) fInternFVar [(vv ibT1), (vv kD)]) (.seq (.call (some (some (.local, qfoO), none)) ExI.fInst1F [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv ibT2), (vv qfoV), (.const 0)]) (.seq (.assign .local qfoD1 (.op .add [(vv kD), (.const 1)])) (.seq (.call (some (some (.local, qfoT), none)) fIO [(vv kFu), (vv qfoD1), (vv qfoO)]) (.seq (.call (some (some (.local, qfoW), none)) fW [(vv kFu), (vv qfoD1), (vv qfoT)]) (.ite (tagIsE qfoW 2) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv qfoW)) (.seq eViewP (.seq (.assign .local qfoX (.load .one (vv lRp))) (.seq (.call (some (some (.local, qfoI), none)) fInternLImax [(vv qfoU), (vv qfoX)]) (.seq (.call (some (some (.local, qfoR), none)) fInternSort [(vv qfoI)]) (.return (vv qfoR)))))))) hang)))))))))) hang))) hang)

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
    (hci : C.code.lookup fIO = some (pmap kParams, inferIOE C fIOB, .one))
    (hcI : C.code.lookup ExI.fInst1F = some ([pFu, pH, ExI.pV, ExI.pD].map (fun p => (p, ShapeHOL.one)),
      ExI.fastBody C, .one)) (hcI' : ExI.Codes C (ExI.body C))
    (hI : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (inferIOE C fIOB) s1 ((knot mode C n).inferIO d' e')
      (PostK (ctxH C H)))
    (s : AState) (d : Nat) (ty v b : EIdx) :
    SpecR (σ := σ) (Pre C s (iltParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty, Enc.idxW v,
      Enc.idxW b])) ltoBody s (ibLetIOT (CoreFnsA.ioView (knot mode C n)) d v b) (PostK C) := by
  refine specR_prologue (postK_locals C) (lto_none C _) ?_
  unfold ibLetIOT
  refine ILP.callE_spec ltoO ExI.fInst1F [pFu, pH, ExI.pV, ExI.pD]
    [.const (BitVec.ofNat 64 coreWalkFuel), vv ibB1, vv ibV1, .const 0] (ExI.fastBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW b, Enc.idxW v, BitVec.ofNat 64 0] (by decide) rfl (by decide) hcI
    ⟨rfl, by simp +decide [Env.get, iltParams, ctxEnv], by simp +decide [Env.get, iltParams, ctxEnv], rfl, trivial⟩
    (ExI.fast_spec ra C hok hcI' s coreWalkFuel b v 0 CV.coreWalkFuel_lt (by decide)) (fun ob s1 => ?_)
  refine specR_congr (m' := (knot mode C n).inferIO d ob >>= fun r => pure r) (by simp; rfl) ?_
  refine Big.specR_callKC ltoR fIO kParams [vv kFu, vv kD, vv ltoO] (inferIOE C fIOB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ob] (by decide) rfl (by decide) hci
    ⟨by simp +decide [Env.get, iltParams, ctxEnv], by simp +decide [Env.get, iltParams, ctxEnv], by simp, trivial⟩ (hI C.H s1 d ob (List.prefix_refl _)) (fun r s2 H2 hp2 _ => ?_)
  exact specR_returnI _ (Enc.idxW r) (by simp) (fun t ht => ⟨H2, hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem codesA_H {C : Ctx} (hc : ExA.CodesA C (ExA.bodyA C)) (H : List (BitVec 64)) :
    ExA.CodesA (ctxH C H) (ExA.bodyA (ctxH C H)) :=
  ⟨hc.abs1, hc.fvarB, ⟨hc.fvr.fvr, hc.fvr.memoGet, hc.fvr.memoProbe, hc.fvr.memoSet, hc.fvr.memoIns⟩, hc.internApp,
    hc.internLam, hc.internForallE, hc.internLet, hc.internBVar, hc.internProj⟩

theorem qmo_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C)
    (hci : C.code.lookup fIO = some (pmap kParams, inferIOE C fIOB, .one))
    (hcI : C.code.lookup ExI.fInst1F = some ([pFu, pH, ExI.pV, ExI.pD].map (fun p => (p, ShapeHOL.one)),
      ExI.fastBody C, .one)) (hcI' : ExI.Codes C (ExI.body C))
    (hcfv : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one))
    (hcA : C.code.lookup ExA.fAbs1F = some ([pFu, ExA.pAd, ExI.pD, pH].map (fun p => (p, ShapeHOL.one)),
      ExA.fastBodyA C, .one)) (hcA' : ExA.CodesA C (ExA.bodyA C))
    (hI : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (inferIOE C fIOB) s1 ((knot mode C n).inferIO d' e')
      (PostK (ctxH C H)))
    (s : AState) (d : Nat) (hd : d < 2 ^ 64) (ty b : EIdx) :
    SpecR (σ := σ) (Pre C s (ifaParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty, Enc.idxW b]))
      qmoBody s (ibLamIOT (CoreFnsA.ioView (knot mode C n)) d ty b) (PostK C) := by
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
  refine Big.specR_callKC qmoB fIO kParams [vv kFu, vv qmoD1, vv qmoO] (inferIOE C fIOB)
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

theorem qfo_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ qfoLocals → (ctxEnv C ++ ifaParams.zip vals).get x = none :=
  Knot.params_none C qfoLocals ifaParams vals (by decide) (by decide)

theorem qfo_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C)
    (hci : C.code.lookup fIO = some (pmap kParams, inferIOE C fIOB, .one))
    (hcw : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one))
    (hcI : C.code.lookup ExI.fInst1F = some ([pFu, pH, ExI.pV, ExI.pD].map (fun p => (p, ShapeHOL.one)),
      ExI.fastBody C, .one)) (hcI' : ExI.Codes C (ExI.body C))
    (hcfv : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one))
    (hcim : C.code.lookup fInternLImax = some ([(lEu, .one), (lEv, .one)], internLImaxBody, .one))
    (hcs : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one))
    (hI : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (inferIOE C fIOB) s1 ((knot mode C n).inferIO d' e')
      (PostK (ctxH C H)))
    (hW : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d' e')
      (PostK (ctxH C H)))
    (s : AState) (d : Nat) (hd : d < 2 ^ 64) (ty b : EIdx) :
    SpecR (σ := σ) (Pre C s (ifaParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty, Enc.idxW b]))
      qfoBody s (ibForallIOT (CoreFnsA.ioView (knot mode C n)) C.fe d ty b) (PostK C) := by
  refine specR_prologue (postK_locals C) (qfo_none C _) ?_
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
  unfold ibForallIOT ensureSort
  simp only [bind_assoc]
  refine Big.specR_callKC qfoA fIO kParams [vv kFu, vv kD, vv ibT1] (inferIOE C fIOB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty] (by decide) rfl (by decide) hci
    ⟨by simp +decide [Env.get, ifaParams, ctxEnv], by simp +decide [Env.get, ifaParams, ctxEnv], by simp +decide [Env.get, ifaParams, ctxEnv], trivial⟩ (hI C.H s d ty (List.prefix_refl _)) (fun tty s1 H1 hp1 _ => ?_)
  refine Big.specR_callKC (C := ctxH C H1) qfoH fW kParams [vv kFu, vv kD, vv qfoA] (whnfE C fWB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW tty] (by decide) rfl (by decide) hcw
    ⟨by simp +decide [Env.get, ifaParams, ctxEnv], by simp +decide [Env.get, ifaParams, ctxEnv], by simp, trivial⟩ (hW H1 s1 d tty hp1) (fun hh s2 H2 hp2 _ => ?_)
  have hp12 : C.H <+: H2 := hp1.trans hp2
  refine Knot.specR_tagIteV qfoH hh 2 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
  swap
  · rw [if_neg (show ¬ (hh.tag == ETag.sort) = true by simpa [ETag.sort] using htg)]
    exact specR_hangI
  rw [if_pos (show (hh.tag == ETag.sort) = true by simp [htg, ETag.sort])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv qfoH) (Enc.idxW hh) (by decide) (by simp) ?_
  refine specR_viewP (C := ctxH C H2) hh (by simp) (by simp +decide [Env.get] <;> rfl)
    (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun vw P hv htn _ => ?_)
  refine specR_congr (view_bind_eq hh vw _ s2 hv) ?_
  have h2 : vw.tagN = 2 := by rw [htn, htg]; rfl
  obtain ⟨u, rfl⟩ : ∃ u, vw = .sort u := by cases vw <;> simp [ENodeView.tagN] at h2 ⊢
  dsimp only
  refine specR_loadI' qfoU (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW u) (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encSort] using wordsAt_mem0 P (Enc.idxW u) [] []) ?_
  refine specR_dropM ?_
  refine ILP.specR_internFVarI (C := ctxH C H2) ra (ctxOK_H hok H2) hcfv qfoV (vv ibT1) (vv kD) ty d (by omega)
    (by decide) (by simp +decide [Env.get, ifaParams, ctxEnv]) (by simp +decide [Env.get, ifaParams, ctxEnv]) (fun fv s3 => ?_)
  refine ILP.callE_spec (C := ctxH C H2) qfoO ExI.fInst1F [pFu, pH, ExI.pV, ExI.pD]
    [.const (BitVec.ofNat 64 coreWalkFuel), vv ibT2, vv qfoV, .const 0] (ExI.fastBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW b, Enc.idxW fv, BitVec.ofNat 64 0] (by decide) rfl (by decide) hcI
    ⟨rfl, by simp +decide [Env.get, ifaParams, ctxEnv], by simp, rfl, trivial⟩
    (ExI.fast_spec ra (ctxH C H2) (ctxOK_H hok H2) (ExIS.codes_H C H2 hcI') s3 coreWalkFuel b fv 0
      CV.coreWalkFuel_lt (by decide)) (fun ob s4 => ?_)
  refine specR_assignI qfoD1 _ (BitVec.ofNat 64 (d + 1)) (by decide)
    (by simp +decide [sev, Env.get, ifaParams, ctxEnv]; exact word_add1_eq d) ?_
  refine Big.specR_callKC (C := ctxH C H2) qfoT fIO kParams [vv kFu, vv qfoD1, vv qfoO] (inferIOE C fIOB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 (d + 1), Enc.idxW ob] (by decide) rfl (by decide) hci
    ⟨by simp +decide [Env.get, ifaParams, ctxEnv], by simp, by simp, trivial⟩ (hI H2 s4 (d + 1) ob hp12) (fun t s5 H3 hp3 _ => ?_)
  refine Big.specR_callKC (C := ctxH C H3) qfoW fW kParams [vv kFu, vv qfoD1, vv qfoT] (whnfE C fWB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 (d + 1), Enc.idxW t] (by decide) rfl (by decide) hcw
    ⟨by simp +decide [Env.get, ifaParams, ctxEnv], by simp, by simp, trivial⟩ (hW H3 s5 (d + 1) t (hp12.trans hp3)) (fun w s6 H4 hp4 _ => ?_)
  have hp14 : C.H <+: H4 := hp12.trans (hp3.trans hp4)
  refine Knot.specR_tagIteV qfoW w 2 (by decide) (by decide) (by simp) (fun htg2 => ?_) (fun htg2 => ?_)
  swap
  · rw [if_neg (show ¬ (w.tag == ETag.sort) = true by simpa [ETag.sort] using htg2)]
    exact specR_hangI
  rw [if_pos (show (w.tag == ETag.sort) = true by simp [htg2, ETag.sort])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv qfoW) (Enc.idxW w) (by decide) (by simp) ?_
  refine specR_viewP (C := ctxH C H4) w (by simp) (by simp +decide [Env.get] <;> rfl)
    (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun vw2 P2 hv2 htn2 _ => ?_)
  simp only [bind_assoc]
  refine specR_congr (view_bind_eq w vw2 _ s6 hv2) ?_
  have h2' : vw2.tagN = 2 := by rw [htn2, htg2]; rfl
  obtain ⟨v, rfl⟩ : ∃ v, vw2 = .sort v := by cases vw2 <;> simp [ENodeView.tagN] at h2' ⊢
  dsimp only
  simp only [pure_bind]
  refine specR_loadI' qfoX (vv lRp) P2 (P2 + BitVec.ofNat 64 0) (Enc.idxW v) (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encSort] using wordsAt_mem0 P2 (Enc.idxW v) [] []) ?_
  refine specR_dropM ?_
  refine callLN (C := ctxH C H4) qfoI fInternLImax [lEu, lEv] [vv qfoU, vv qfoX] internLImaxBody
    [Enc.idxW u, Enc.idxW v] (by decide) rfl (by decide) hcim ⟨by simp, by simp, trivial⟩ (.imax u v)
    (internLImax_body_spec ra (ctxH C H4) (ctxOK_H hok H4) s6 u v) (fun iu s7 _ => ?_)
  refine specR_bindPure ?_
  refine ILP.callE_spec (C := ctxH C H4) qfoR fInternSort [lEu] [vv qfoI] sortBody [Enc.idxW iu] (by decide) rfl
    (by decide) hcs ⟨by simp, trivial⟩ (sort_body_spec ra (ctxH C H4) (ctxOK_H hok H4) s7 iu) (fun r s8 => ?_)
  exact specR_returnI _ (Enc.idxW r) (by simp) (fun t ht => ⟨H4, hp14, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
