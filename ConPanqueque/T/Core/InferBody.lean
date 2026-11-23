import ConPanqueque.T.Core.InferTwin
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `inferBody`: the dispatcher

One `view`, then the node's arm: a bound free variable's annotation; the sort, constant, literal, binder,
application, projection and `let` arms as callees (`inferBody_eq`); a loose `bvar` declines (halts).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def ibA := ofString "ib_a"
def ibB := ofString "ib_b"
def ibC := ofString "ib_c"
def ibI := ofString "ib_i"
def ibX := ofString "ib_x"
def ibU := ofString "ib_u"
def ibN := ofString "ib_n"
def ibUs := ofString "ib_us"
def ibE := ofString "ib_e"
def ibT1 := ofString "ib_t1"
def ibT2 := ofString "ib_t2"
def ibSn := ofString "ib_sn"
def ibIx := ofString "ib_ix"
def ibPe := ofString "ib_pe"
def ibV1 := ofString "ib_v1"
def ibB1 := ofString "ib_b1"
def fIbs := ofString "inferSort"
def fIbc := ofString "inferConst"
def fIbl := ofString "inferLit"
def fIfa := ofString "inferForall"
def fIla := ofString "inferLam"
def fIap := ofString "inferApp"
def fIpr := ofString "inferProj"
def fIlt := ofString "inferLet"

@[simp] theorem ib_ibA_ne_ibB : ibA ≠ ibB := by decide
@[simp] theorem ib_ibA_ne_ibC : ibA ≠ ibC := by decide
@[simp] theorem ib_ibA_ne_ibI : ibA ≠ ibI := by decide
@[simp] theorem ib_ibA_ne_ibX : ibA ≠ ibX := by decide
@[simp] theorem ib_ibA_ne_ibU : ibA ≠ ibU := by decide
@[simp] theorem ib_ibA_ne_ibN : ibA ≠ ibN := by decide
@[simp] theorem ib_ibA_ne_ibUs : ibA ≠ ibUs := by decide
@[simp] theorem ib_ibA_ne_ibE : ibA ≠ ibE := by decide
@[simp] theorem ib_ibA_ne_ibT1 : ibA ≠ ibT1 := by decide
@[simp] theorem ib_ibA_ne_ibT2 : ibA ≠ ibT2 := by decide
@[simp] theorem ib_ibA_ne_ibSn : ibA ≠ ibSn := by decide
@[simp] theorem ib_ibA_ne_ibIx : ibA ≠ ibIx := by decide
@[simp] theorem ib_ibA_ne_ibPe : ibA ≠ ibPe := by decide
@[simp] theorem ib_ibA_ne_ibV1 : ibA ≠ ibV1 := by decide
@[simp] theorem ib_ibA_ne_ibB1 : ibA ≠ ibB1 := by decide
@[simp] theorem ib_ibA_ne_lKb : ibA ≠ lKb := by decide
@[simp] theorem ib_ibA_ne_lFl : ibA ≠ lFl := by decide
@[simp] theorem ib_ibA_ne_lDh : ibA ≠ lDh := by decide
@[simp] theorem ib_ibA_ne_lDt : ibA ≠ lDt := by decide
@[simp] theorem ib_ibA_ne_lDg : ibA ≠ lDg := by decide
@[simp] theorem ib_ibA_ne_lDi : ibA ≠ lDi := by decide
@[simp] theorem ib_ibA_ne_lRp : ibA ≠ lRp := by decide
@[simp] theorem ib_ibA_ne_lRn : ibA ≠ lRn := by decide
@[simp] theorem ib_ibA_ne_lFle : ibA ≠ lFle := by decide
@[simp] theorem ib_ibA_ne_lDir : ibA ≠ lDir := by decide
@[simp] theorem ib_ibA_ne_kFu : ibA ≠ kFu := by decide
@[simp] theorem ib_ibA_ne_kD : ibA ≠ kD := by decide
@[simp] theorem ib_ibA_ne_kE : ibA ≠ kE := by decide
@[simp] theorem ib_ibB_ne_ibA : ibB ≠ ibA := by decide
@[simp] theorem ib_ibB_ne_ibC : ibB ≠ ibC := by decide
@[simp] theorem ib_ibB_ne_ibI : ibB ≠ ibI := by decide
@[simp] theorem ib_ibB_ne_ibX : ibB ≠ ibX := by decide
@[simp] theorem ib_ibB_ne_ibU : ibB ≠ ibU := by decide
@[simp] theorem ib_ibB_ne_ibN : ibB ≠ ibN := by decide
@[simp] theorem ib_ibB_ne_ibUs : ibB ≠ ibUs := by decide
@[simp] theorem ib_ibB_ne_ibE : ibB ≠ ibE := by decide
@[simp] theorem ib_ibB_ne_ibT1 : ibB ≠ ibT1 := by decide
@[simp] theorem ib_ibB_ne_ibT2 : ibB ≠ ibT2 := by decide
@[simp] theorem ib_ibB_ne_ibSn : ibB ≠ ibSn := by decide
@[simp] theorem ib_ibB_ne_ibIx : ibB ≠ ibIx := by decide
@[simp] theorem ib_ibB_ne_ibPe : ibB ≠ ibPe := by decide
@[simp] theorem ib_ibB_ne_ibV1 : ibB ≠ ibV1 := by decide
@[simp] theorem ib_ibB_ne_ibB1 : ibB ≠ ibB1 := by decide
@[simp] theorem ib_ibB_ne_lKb : ibB ≠ lKb := by decide
@[simp] theorem ib_ibB_ne_lFl : ibB ≠ lFl := by decide
@[simp] theorem ib_ibB_ne_lDh : ibB ≠ lDh := by decide
@[simp] theorem ib_ibB_ne_lDt : ibB ≠ lDt := by decide
@[simp] theorem ib_ibB_ne_lDg : ibB ≠ lDg := by decide
@[simp] theorem ib_ibB_ne_lDi : ibB ≠ lDi := by decide
@[simp] theorem ib_ibB_ne_lRp : ibB ≠ lRp := by decide
@[simp] theorem ib_ibB_ne_lRn : ibB ≠ lRn := by decide
@[simp] theorem ib_ibB_ne_lFle : ibB ≠ lFle := by decide
@[simp] theorem ib_ibB_ne_lDir : ibB ≠ lDir := by decide
@[simp] theorem ib_ibB_ne_kFu : ibB ≠ kFu := by decide
@[simp] theorem ib_ibB_ne_kD : ibB ≠ kD := by decide
@[simp] theorem ib_ibB_ne_kE : ibB ≠ kE := by decide
@[simp] theorem ib_ibC_ne_ibA : ibC ≠ ibA := by decide
@[simp] theorem ib_ibC_ne_ibB : ibC ≠ ibB := by decide
@[simp] theorem ib_ibC_ne_ibI : ibC ≠ ibI := by decide
@[simp] theorem ib_ibC_ne_ibX : ibC ≠ ibX := by decide
@[simp] theorem ib_ibC_ne_ibU : ibC ≠ ibU := by decide
@[simp] theorem ib_ibC_ne_ibN : ibC ≠ ibN := by decide
@[simp] theorem ib_ibC_ne_ibUs : ibC ≠ ibUs := by decide
@[simp] theorem ib_ibC_ne_ibE : ibC ≠ ibE := by decide
@[simp] theorem ib_ibC_ne_ibT1 : ibC ≠ ibT1 := by decide
@[simp] theorem ib_ibC_ne_ibT2 : ibC ≠ ibT2 := by decide
@[simp] theorem ib_ibC_ne_ibSn : ibC ≠ ibSn := by decide
@[simp] theorem ib_ibC_ne_ibIx : ibC ≠ ibIx := by decide
@[simp] theorem ib_ibC_ne_ibPe : ibC ≠ ibPe := by decide
@[simp] theorem ib_ibC_ne_ibV1 : ibC ≠ ibV1 := by decide
@[simp] theorem ib_ibC_ne_ibB1 : ibC ≠ ibB1 := by decide
@[simp] theorem ib_ibC_ne_lKb : ibC ≠ lKb := by decide
@[simp] theorem ib_ibC_ne_lFl : ibC ≠ lFl := by decide
@[simp] theorem ib_ibC_ne_lDh : ibC ≠ lDh := by decide
@[simp] theorem ib_ibC_ne_lDt : ibC ≠ lDt := by decide
@[simp] theorem ib_ibC_ne_lDg : ibC ≠ lDg := by decide
@[simp] theorem ib_ibC_ne_lDi : ibC ≠ lDi := by decide
@[simp] theorem ib_ibC_ne_lRp : ibC ≠ lRp := by decide
@[simp] theorem ib_ibC_ne_lRn : ibC ≠ lRn := by decide
@[simp] theorem ib_ibC_ne_lFle : ibC ≠ lFle := by decide
@[simp] theorem ib_ibC_ne_lDir : ibC ≠ lDir := by decide
@[simp] theorem ib_ibC_ne_kFu : ibC ≠ kFu := by decide
@[simp] theorem ib_ibC_ne_kD : ibC ≠ kD := by decide
@[simp] theorem ib_ibC_ne_kE : ibC ≠ kE := by decide
@[simp] theorem ib_ibI_ne_ibA : ibI ≠ ibA := by decide
@[simp] theorem ib_ibI_ne_ibB : ibI ≠ ibB := by decide
@[simp] theorem ib_ibI_ne_ibC : ibI ≠ ibC := by decide
@[simp] theorem ib_ibI_ne_ibX : ibI ≠ ibX := by decide
@[simp] theorem ib_ibI_ne_ibU : ibI ≠ ibU := by decide
@[simp] theorem ib_ibI_ne_ibN : ibI ≠ ibN := by decide
@[simp] theorem ib_ibI_ne_ibUs : ibI ≠ ibUs := by decide
@[simp] theorem ib_ibI_ne_ibE : ibI ≠ ibE := by decide
@[simp] theorem ib_ibI_ne_ibT1 : ibI ≠ ibT1 := by decide
@[simp] theorem ib_ibI_ne_ibT2 : ibI ≠ ibT2 := by decide
@[simp] theorem ib_ibI_ne_ibSn : ibI ≠ ibSn := by decide
@[simp] theorem ib_ibI_ne_ibIx : ibI ≠ ibIx := by decide
@[simp] theorem ib_ibI_ne_ibPe : ibI ≠ ibPe := by decide
@[simp] theorem ib_ibI_ne_ibV1 : ibI ≠ ibV1 := by decide
@[simp] theorem ib_ibI_ne_ibB1 : ibI ≠ ibB1 := by decide
@[simp] theorem ib_ibI_ne_lKb : ibI ≠ lKb := by decide
@[simp] theorem ib_ibI_ne_lFl : ibI ≠ lFl := by decide
@[simp] theorem ib_ibI_ne_lDh : ibI ≠ lDh := by decide
@[simp] theorem ib_ibI_ne_lDt : ibI ≠ lDt := by decide
@[simp] theorem ib_ibI_ne_lDg : ibI ≠ lDg := by decide
@[simp] theorem ib_ibI_ne_lDi : ibI ≠ lDi := by decide
@[simp] theorem ib_ibI_ne_lRp : ibI ≠ lRp := by decide
@[simp] theorem ib_ibI_ne_lRn : ibI ≠ lRn := by decide
@[simp] theorem ib_ibI_ne_lFle : ibI ≠ lFle := by decide
@[simp] theorem ib_ibI_ne_lDir : ibI ≠ lDir := by decide
@[simp] theorem ib_ibI_ne_kFu : ibI ≠ kFu := by decide
@[simp] theorem ib_ibI_ne_kD : ibI ≠ kD := by decide
@[simp] theorem ib_ibI_ne_kE : ibI ≠ kE := by decide
@[simp] theorem ib_ibX_ne_ibA : ibX ≠ ibA := by decide
@[simp] theorem ib_ibX_ne_ibB : ibX ≠ ibB := by decide
@[simp] theorem ib_ibX_ne_ibC : ibX ≠ ibC := by decide
@[simp] theorem ib_ibX_ne_ibI : ibX ≠ ibI := by decide
@[simp] theorem ib_ibX_ne_ibU : ibX ≠ ibU := by decide
@[simp] theorem ib_ibX_ne_ibN : ibX ≠ ibN := by decide
@[simp] theorem ib_ibX_ne_ibUs : ibX ≠ ibUs := by decide
@[simp] theorem ib_ibX_ne_ibE : ibX ≠ ibE := by decide
@[simp] theorem ib_ibX_ne_ibT1 : ibX ≠ ibT1 := by decide
@[simp] theorem ib_ibX_ne_ibT2 : ibX ≠ ibT2 := by decide
@[simp] theorem ib_ibX_ne_ibSn : ibX ≠ ibSn := by decide
@[simp] theorem ib_ibX_ne_ibIx : ibX ≠ ibIx := by decide
@[simp] theorem ib_ibX_ne_ibPe : ibX ≠ ibPe := by decide
@[simp] theorem ib_ibX_ne_ibV1 : ibX ≠ ibV1 := by decide
@[simp] theorem ib_ibX_ne_ibB1 : ibX ≠ ibB1 := by decide
@[simp] theorem ib_ibX_ne_lKb : ibX ≠ lKb := by decide
@[simp] theorem ib_ibX_ne_lFl : ibX ≠ lFl := by decide
@[simp] theorem ib_ibX_ne_lDh : ibX ≠ lDh := by decide
@[simp] theorem ib_ibX_ne_lDt : ibX ≠ lDt := by decide
@[simp] theorem ib_ibX_ne_lDg : ibX ≠ lDg := by decide
@[simp] theorem ib_ibX_ne_lDi : ibX ≠ lDi := by decide
@[simp] theorem ib_ibX_ne_lRp : ibX ≠ lRp := by decide
@[simp] theorem ib_ibX_ne_lRn : ibX ≠ lRn := by decide
@[simp] theorem ib_ibX_ne_lFle : ibX ≠ lFle := by decide
@[simp] theorem ib_ibX_ne_lDir : ibX ≠ lDir := by decide
@[simp] theorem ib_ibX_ne_kFu : ibX ≠ kFu := by decide
@[simp] theorem ib_ibX_ne_kD : ibX ≠ kD := by decide
@[simp] theorem ib_ibX_ne_kE : ibX ≠ kE := by decide
@[simp] theorem ib_ibU_ne_ibA : ibU ≠ ibA := by decide
@[simp] theorem ib_ibU_ne_ibB : ibU ≠ ibB := by decide
@[simp] theorem ib_ibU_ne_ibC : ibU ≠ ibC := by decide
@[simp] theorem ib_ibU_ne_ibI : ibU ≠ ibI := by decide
@[simp] theorem ib_ibU_ne_ibX : ibU ≠ ibX := by decide
@[simp] theorem ib_ibU_ne_ibN : ibU ≠ ibN := by decide
@[simp] theorem ib_ibU_ne_ibUs : ibU ≠ ibUs := by decide
@[simp] theorem ib_ibU_ne_ibE : ibU ≠ ibE := by decide
@[simp] theorem ib_ibU_ne_ibT1 : ibU ≠ ibT1 := by decide
@[simp] theorem ib_ibU_ne_ibT2 : ibU ≠ ibT2 := by decide
@[simp] theorem ib_ibU_ne_ibSn : ibU ≠ ibSn := by decide
@[simp] theorem ib_ibU_ne_ibIx : ibU ≠ ibIx := by decide
@[simp] theorem ib_ibU_ne_ibPe : ibU ≠ ibPe := by decide
@[simp] theorem ib_ibU_ne_ibV1 : ibU ≠ ibV1 := by decide
@[simp] theorem ib_ibU_ne_ibB1 : ibU ≠ ibB1 := by decide
@[simp] theorem ib_ibU_ne_lKb : ibU ≠ lKb := by decide
@[simp] theorem ib_ibU_ne_lFl : ibU ≠ lFl := by decide
@[simp] theorem ib_ibU_ne_lDh : ibU ≠ lDh := by decide
@[simp] theorem ib_ibU_ne_lDt : ibU ≠ lDt := by decide
@[simp] theorem ib_ibU_ne_lDg : ibU ≠ lDg := by decide
@[simp] theorem ib_ibU_ne_lDi : ibU ≠ lDi := by decide
@[simp] theorem ib_ibU_ne_lRp : ibU ≠ lRp := by decide
@[simp] theorem ib_ibU_ne_lRn : ibU ≠ lRn := by decide
@[simp] theorem ib_ibU_ne_lFle : ibU ≠ lFle := by decide
@[simp] theorem ib_ibU_ne_lDir : ibU ≠ lDir := by decide
@[simp] theorem ib_ibU_ne_kFu : ibU ≠ kFu := by decide
@[simp] theorem ib_ibU_ne_kD : ibU ≠ kD := by decide
@[simp] theorem ib_ibU_ne_kE : ibU ≠ kE := by decide
@[simp] theorem ib_ibN_ne_ibA : ibN ≠ ibA := by decide
@[simp] theorem ib_ibN_ne_ibB : ibN ≠ ibB := by decide
@[simp] theorem ib_ibN_ne_ibC : ibN ≠ ibC := by decide
@[simp] theorem ib_ibN_ne_ibI : ibN ≠ ibI := by decide
@[simp] theorem ib_ibN_ne_ibX : ibN ≠ ibX := by decide
@[simp] theorem ib_ibN_ne_ibU : ibN ≠ ibU := by decide
@[simp] theorem ib_ibN_ne_ibUs : ibN ≠ ibUs := by decide
@[simp] theorem ib_ibN_ne_ibE : ibN ≠ ibE := by decide
@[simp] theorem ib_ibN_ne_ibT1 : ibN ≠ ibT1 := by decide
@[simp] theorem ib_ibN_ne_ibT2 : ibN ≠ ibT2 := by decide
@[simp] theorem ib_ibN_ne_ibSn : ibN ≠ ibSn := by decide
@[simp] theorem ib_ibN_ne_ibIx : ibN ≠ ibIx := by decide
@[simp] theorem ib_ibN_ne_ibPe : ibN ≠ ibPe := by decide
@[simp] theorem ib_ibN_ne_ibV1 : ibN ≠ ibV1 := by decide
@[simp] theorem ib_ibN_ne_ibB1 : ibN ≠ ibB1 := by decide
@[simp] theorem ib_ibN_ne_lKb : ibN ≠ lKb := by decide
@[simp] theorem ib_ibN_ne_lFl : ibN ≠ lFl := by decide
@[simp] theorem ib_ibN_ne_lDh : ibN ≠ lDh := by decide
@[simp] theorem ib_ibN_ne_lDt : ibN ≠ lDt := by decide
@[simp] theorem ib_ibN_ne_lDg : ibN ≠ lDg := by decide
@[simp] theorem ib_ibN_ne_lDi : ibN ≠ lDi := by decide
@[simp] theorem ib_ibN_ne_lRp : ibN ≠ lRp := by decide
@[simp] theorem ib_ibN_ne_lRn : ibN ≠ lRn := by decide
@[simp] theorem ib_ibN_ne_lFle : ibN ≠ lFle := by decide
@[simp] theorem ib_ibN_ne_lDir : ibN ≠ lDir := by decide
@[simp] theorem ib_ibN_ne_kFu : ibN ≠ kFu := by decide
@[simp] theorem ib_ibN_ne_kD : ibN ≠ kD := by decide
@[simp] theorem ib_ibN_ne_kE : ibN ≠ kE := by decide
@[simp] theorem ib_ibUs_ne_ibA : ibUs ≠ ibA := by decide
@[simp] theorem ib_ibUs_ne_ibB : ibUs ≠ ibB := by decide
@[simp] theorem ib_ibUs_ne_ibC : ibUs ≠ ibC := by decide
@[simp] theorem ib_ibUs_ne_ibI : ibUs ≠ ibI := by decide
@[simp] theorem ib_ibUs_ne_ibX : ibUs ≠ ibX := by decide
@[simp] theorem ib_ibUs_ne_ibU : ibUs ≠ ibU := by decide
@[simp] theorem ib_ibUs_ne_ibN : ibUs ≠ ibN := by decide
@[simp] theorem ib_ibUs_ne_ibE : ibUs ≠ ibE := by decide
@[simp] theorem ib_ibUs_ne_ibT1 : ibUs ≠ ibT1 := by decide
@[simp] theorem ib_ibUs_ne_ibT2 : ibUs ≠ ibT2 := by decide
@[simp] theorem ib_ibUs_ne_ibSn : ibUs ≠ ibSn := by decide
@[simp] theorem ib_ibUs_ne_ibIx : ibUs ≠ ibIx := by decide
@[simp] theorem ib_ibUs_ne_ibPe : ibUs ≠ ibPe := by decide
@[simp] theorem ib_ibUs_ne_ibV1 : ibUs ≠ ibV1 := by decide
@[simp] theorem ib_ibUs_ne_ibB1 : ibUs ≠ ibB1 := by decide
@[simp] theorem ib_ibUs_ne_lKb : ibUs ≠ lKb := by decide
@[simp] theorem ib_ibUs_ne_lFl : ibUs ≠ lFl := by decide
@[simp] theorem ib_ibUs_ne_lDh : ibUs ≠ lDh := by decide
@[simp] theorem ib_ibUs_ne_lDt : ibUs ≠ lDt := by decide
@[simp] theorem ib_ibUs_ne_lDg : ibUs ≠ lDg := by decide
@[simp] theorem ib_ibUs_ne_lDi : ibUs ≠ lDi := by decide
@[simp] theorem ib_ibUs_ne_lRp : ibUs ≠ lRp := by decide
@[simp] theorem ib_ibUs_ne_lRn : ibUs ≠ lRn := by decide
@[simp] theorem ib_ibUs_ne_lFle : ibUs ≠ lFle := by decide
@[simp] theorem ib_ibUs_ne_lDir : ibUs ≠ lDir := by decide
@[simp] theorem ib_ibUs_ne_kFu : ibUs ≠ kFu := by decide
@[simp] theorem ib_ibUs_ne_kD : ibUs ≠ kD := by decide
@[simp] theorem ib_ibUs_ne_kE : ibUs ≠ kE := by decide
@[simp] theorem ib_ibE_ne_ibA : ibE ≠ ibA := by decide
@[simp] theorem ib_ibE_ne_ibB : ibE ≠ ibB := by decide
@[simp] theorem ib_ibE_ne_ibC : ibE ≠ ibC := by decide
@[simp] theorem ib_ibE_ne_ibI : ibE ≠ ibI := by decide
@[simp] theorem ib_ibE_ne_ibX : ibE ≠ ibX := by decide
@[simp] theorem ib_ibE_ne_ibU : ibE ≠ ibU := by decide
@[simp] theorem ib_ibE_ne_ibN : ibE ≠ ibN := by decide
@[simp] theorem ib_ibE_ne_ibUs : ibE ≠ ibUs := by decide
@[simp] theorem ib_ibE_ne_ibT1 : ibE ≠ ibT1 := by decide
@[simp] theorem ib_ibE_ne_ibT2 : ibE ≠ ibT2 := by decide
@[simp] theorem ib_ibE_ne_ibSn : ibE ≠ ibSn := by decide
@[simp] theorem ib_ibE_ne_ibIx : ibE ≠ ibIx := by decide
@[simp] theorem ib_ibE_ne_ibPe : ibE ≠ ibPe := by decide
@[simp] theorem ib_ibE_ne_ibV1 : ibE ≠ ibV1 := by decide
@[simp] theorem ib_ibE_ne_ibB1 : ibE ≠ ibB1 := by decide
@[simp] theorem ib_ibE_ne_lKb : ibE ≠ lKb := by decide
@[simp] theorem ib_ibE_ne_lFl : ibE ≠ lFl := by decide
@[simp] theorem ib_ibE_ne_lDh : ibE ≠ lDh := by decide
@[simp] theorem ib_ibE_ne_lDt : ibE ≠ lDt := by decide
@[simp] theorem ib_ibE_ne_lDg : ibE ≠ lDg := by decide
@[simp] theorem ib_ibE_ne_lDi : ibE ≠ lDi := by decide
@[simp] theorem ib_ibE_ne_lRp : ibE ≠ lRp := by decide
@[simp] theorem ib_ibE_ne_lRn : ibE ≠ lRn := by decide
@[simp] theorem ib_ibE_ne_lFle : ibE ≠ lFle := by decide
@[simp] theorem ib_ibE_ne_lDir : ibE ≠ lDir := by decide
@[simp] theorem ib_ibE_ne_kFu : ibE ≠ kFu := by decide
@[simp] theorem ib_ibE_ne_kD : ibE ≠ kD := by decide
@[simp] theorem ib_ibE_ne_kE : ibE ≠ kE := by decide
@[simp] theorem ib_ibT1_ne_ibA : ibT1 ≠ ibA := by decide
@[simp] theorem ib_ibT1_ne_ibB : ibT1 ≠ ibB := by decide
@[simp] theorem ib_ibT1_ne_ibC : ibT1 ≠ ibC := by decide
@[simp] theorem ib_ibT1_ne_ibI : ibT1 ≠ ibI := by decide
@[simp] theorem ib_ibT1_ne_ibX : ibT1 ≠ ibX := by decide
@[simp] theorem ib_ibT1_ne_ibU : ibT1 ≠ ibU := by decide
@[simp] theorem ib_ibT1_ne_ibN : ibT1 ≠ ibN := by decide
@[simp] theorem ib_ibT1_ne_ibUs : ibT1 ≠ ibUs := by decide
@[simp] theorem ib_ibT1_ne_ibE : ibT1 ≠ ibE := by decide
@[simp] theorem ib_ibT1_ne_ibT2 : ibT1 ≠ ibT2 := by decide
@[simp] theorem ib_ibT1_ne_ibSn : ibT1 ≠ ibSn := by decide
@[simp] theorem ib_ibT1_ne_ibIx : ibT1 ≠ ibIx := by decide
@[simp] theorem ib_ibT1_ne_ibPe : ibT1 ≠ ibPe := by decide
@[simp] theorem ib_ibT1_ne_ibV1 : ibT1 ≠ ibV1 := by decide
@[simp] theorem ib_ibT1_ne_ibB1 : ibT1 ≠ ibB1 := by decide
@[simp] theorem ib_ibT1_ne_lKb : ibT1 ≠ lKb := by decide
@[simp] theorem ib_ibT1_ne_lFl : ibT1 ≠ lFl := by decide
@[simp] theorem ib_ibT1_ne_lDh : ibT1 ≠ lDh := by decide
@[simp] theorem ib_ibT1_ne_lDt : ibT1 ≠ lDt := by decide
@[simp] theorem ib_ibT1_ne_lDg : ibT1 ≠ lDg := by decide
@[simp] theorem ib_ibT1_ne_lDi : ibT1 ≠ lDi := by decide
@[simp] theorem ib_ibT1_ne_lRp : ibT1 ≠ lRp := by decide
@[simp] theorem ib_ibT1_ne_lRn : ibT1 ≠ lRn := by decide
@[simp] theorem ib_ibT1_ne_lFle : ibT1 ≠ lFle := by decide
@[simp] theorem ib_ibT1_ne_lDir : ibT1 ≠ lDir := by decide
@[simp] theorem ib_ibT1_ne_kFu : ibT1 ≠ kFu := by decide
@[simp] theorem ib_ibT1_ne_kD : ibT1 ≠ kD := by decide
@[simp] theorem ib_ibT1_ne_kE : ibT1 ≠ kE := by decide
@[simp] theorem ib_ibT2_ne_ibA : ibT2 ≠ ibA := by decide
@[simp] theorem ib_ibT2_ne_ibB : ibT2 ≠ ibB := by decide
@[simp] theorem ib_ibT2_ne_ibC : ibT2 ≠ ibC := by decide
@[simp] theorem ib_ibT2_ne_ibI : ibT2 ≠ ibI := by decide
@[simp] theorem ib_ibT2_ne_ibX : ibT2 ≠ ibX := by decide
@[simp] theorem ib_ibT2_ne_ibU : ibT2 ≠ ibU := by decide
@[simp] theorem ib_ibT2_ne_ibN : ibT2 ≠ ibN := by decide
@[simp] theorem ib_ibT2_ne_ibUs : ibT2 ≠ ibUs := by decide
@[simp] theorem ib_ibT2_ne_ibE : ibT2 ≠ ibE := by decide
@[simp] theorem ib_ibT2_ne_ibT1 : ibT2 ≠ ibT1 := by decide
@[simp] theorem ib_ibT2_ne_ibSn : ibT2 ≠ ibSn := by decide
@[simp] theorem ib_ibT2_ne_ibIx : ibT2 ≠ ibIx := by decide
@[simp] theorem ib_ibT2_ne_ibPe : ibT2 ≠ ibPe := by decide
@[simp] theorem ib_ibT2_ne_ibV1 : ibT2 ≠ ibV1 := by decide
@[simp] theorem ib_ibT2_ne_ibB1 : ibT2 ≠ ibB1 := by decide
@[simp] theorem ib_ibT2_ne_lKb : ibT2 ≠ lKb := by decide
@[simp] theorem ib_ibT2_ne_lFl : ibT2 ≠ lFl := by decide
@[simp] theorem ib_ibT2_ne_lDh : ibT2 ≠ lDh := by decide
@[simp] theorem ib_ibT2_ne_lDt : ibT2 ≠ lDt := by decide
@[simp] theorem ib_ibT2_ne_lDg : ibT2 ≠ lDg := by decide
@[simp] theorem ib_ibT2_ne_lDi : ibT2 ≠ lDi := by decide
@[simp] theorem ib_ibT2_ne_lRp : ibT2 ≠ lRp := by decide
@[simp] theorem ib_ibT2_ne_lRn : ibT2 ≠ lRn := by decide
@[simp] theorem ib_ibT2_ne_lFle : ibT2 ≠ lFle := by decide
@[simp] theorem ib_ibT2_ne_lDir : ibT2 ≠ lDir := by decide
@[simp] theorem ib_ibT2_ne_kFu : ibT2 ≠ kFu := by decide
@[simp] theorem ib_ibT2_ne_kD : ibT2 ≠ kD := by decide
@[simp] theorem ib_ibT2_ne_kE : ibT2 ≠ kE := by decide
@[simp] theorem ib_ibSn_ne_ibA : ibSn ≠ ibA := by decide
@[simp] theorem ib_ibSn_ne_ibB : ibSn ≠ ibB := by decide
@[simp] theorem ib_ibSn_ne_ibC : ibSn ≠ ibC := by decide
@[simp] theorem ib_ibSn_ne_ibI : ibSn ≠ ibI := by decide
@[simp] theorem ib_ibSn_ne_ibX : ibSn ≠ ibX := by decide
@[simp] theorem ib_ibSn_ne_ibU : ibSn ≠ ibU := by decide
@[simp] theorem ib_ibSn_ne_ibN : ibSn ≠ ibN := by decide
@[simp] theorem ib_ibSn_ne_ibUs : ibSn ≠ ibUs := by decide
@[simp] theorem ib_ibSn_ne_ibE : ibSn ≠ ibE := by decide
@[simp] theorem ib_ibSn_ne_ibT1 : ibSn ≠ ibT1 := by decide
@[simp] theorem ib_ibSn_ne_ibT2 : ibSn ≠ ibT2 := by decide
@[simp] theorem ib_ibSn_ne_ibIx : ibSn ≠ ibIx := by decide
@[simp] theorem ib_ibSn_ne_ibPe : ibSn ≠ ibPe := by decide
@[simp] theorem ib_ibSn_ne_ibV1 : ibSn ≠ ibV1 := by decide
@[simp] theorem ib_ibSn_ne_ibB1 : ibSn ≠ ibB1 := by decide
@[simp] theorem ib_ibSn_ne_lKb : ibSn ≠ lKb := by decide
@[simp] theorem ib_ibSn_ne_lFl : ibSn ≠ lFl := by decide
@[simp] theorem ib_ibSn_ne_lDh : ibSn ≠ lDh := by decide
@[simp] theorem ib_ibSn_ne_lDt : ibSn ≠ lDt := by decide
@[simp] theorem ib_ibSn_ne_lDg : ibSn ≠ lDg := by decide
@[simp] theorem ib_ibSn_ne_lDi : ibSn ≠ lDi := by decide
@[simp] theorem ib_ibSn_ne_lRp : ibSn ≠ lRp := by decide
@[simp] theorem ib_ibSn_ne_lRn : ibSn ≠ lRn := by decide
@[simp] theorem ib_ibSn_ne_lFle : ibSn ≠ lFle := by decide
@[simp] theorem ib_ibSn_ne_lDir : ibSn ≠ lDir := by decide
@[simp] theorem ib_ibSn_ne_kFu : ibSn ≠ kFu := by decide
@[simp] theorem ib_ibSn_ne_kD : ibSn ≠ kD := by decide
@[simp] theorem ib_ibSn_ne_kE : ibSn ≠ kE := by decide
@[simp] theorem ib_ibIx_ne_ibA : ibIx ≠ ibA := by decide
@[simp] theorem ib_ibIx_ne_ibB : ibIx ≠ ibB := by decide
@[simp] theorem ib_ibIx_ne_ibC : ibIx ≠ ibC := by decide
@[simp] theorem ib_ibIx_ne_ibI : ibIx ≠ ibI := by decide
@[simp] theorem ib_ibIx_ne_ibX : ibIx ≠ ibX := by decide
@[simp] theorem ib_ibIx_ne_ibU : ibIx ≠ ibU := by decide
@[simp] theorem ib_ibIx_ne_ibN : ibIx ≠ ibN := by decide
@[simp] theorem ib_ibIx_ne_ibUs : ibIx ≠ ibUs := by decide
@[simp] theorem ib_ibIx_ne_ibE : ibIx ≠ ibE := by decide
@[simp] theorem ib_ibIx_ne_ibT1 : ibIx ≠ ibT1 := by decide
@[simp] theorem ib_ibIx_ne_ibT2 : ibIx ≠ ibT2 := by decide
@[simp] theorem ib_ibIx_ne_ibSn : ibIx ≠ ibSn := by decide
@[simp] theorem ib_ibIx_ne_ibPe : ibIx ≠ ibPe := by decide
@[simp] theorem ib_ibIx_ne_ibV1 : ibIx ≠ ibV1 := by decide
@[simp] theorem ib_ibIx_ne_ibB1 : ibIx ≠ ibB1 := by decide
@[simp] theorem ib_ibIx_ne_lKb : ibIx ≠ lKb := by decide
@[simp] theorem ib_ibIx_ne_lFl : ibIx ≠ lFl := by decide
@[simp] theorem ib_ibIx_ne_lDh : ibIx ≠ lDh := by decide
@[simp] theorem ib_ibIx_ne_lDt : ibIx ≠ lDt := by decide
@[simp] theorem ib_ibIx_ne_lDg : ibIx ≠ lDg := by decide
@[simp] theorem ib_ibIx_ne_lDi : ibIx ≠ lDi := by decide
@[simp] theorem ib_ibIx_ne_lRp : ibIx ≠ lRp := by decide
@[simp] theorem ib_ibIx_ne_lRn : ibIx ≠ lRn := by decide
@[simp] theorem ib_ibIx_ne_lFle : ibIx ≠ lFle := by decide
@[simp] theorem ib_ibIx_ne_lDir : ibIx ≠ lDir := by decide
@[simp] theorem ib_ibIx_ne_kFu : ibIx ≠ kFu := by decide
@[simp] theorem ib_ibIx_ne_kD : ibIx ≠ kD := by decide
@[simp] theorem ib_ibIx_ne_kE : ibIx ≠ kE := by decide
@[simp] theorem ib_ibPe_ne_ibA : ibPe ≠ ibA := by decide
@[simp] theorem ib_ibPe_ne_ibB : ibPe ≠ ibB := by decide
@[simp] theorem ib_ibPe_ne_ibC : ibPe ≠ ibC := by decide
@[simp] theorem ib_ibPe_ne_ibI : ibPe ≠ ibI := by decide
@[simp] theorem ib_ibPe_ne_ibX : ibPe ≠ ibX := by decide
@[simp] theorem ib_ibPe_ne_ibU : ibPe ≠ ibU := by decide
@[simp] theorem ib_ibPe_ne_ibN : ibPe ≠ ibN := by decide
@[simp] theorem ib_ibPe_ne_ibUs : ibPe ≠ ibUs := by decide
@[simp] theorem ib_ibPe_ne_ibE : ibPe ≠ ibE := by decide
@[simp] theorem ib_ibPe_ne_ibT1 : ibPe ≠ ibT1 := by decide
@[simp] theorem ib_ibPe_ne_ibT2 : ibPe ≠ ibT2 := by decide
@[simp] theorem ib_ibPe_ne_ibSn : ibPe ≠ ibSn := by decide
@[simp] theorem ib_ibPe_ne_ibIx : ibPe ≠ ibIx := by decide
@[simp] theorem ib_ibPe_ne_ibV1 : ibPe ≠ ibV1 := by decide
@[simp] theorem ib_ibPe_ne_ibB1 : ibPe ≠ ibB1 := by decide
@[simp] theorem ib_ibPe_ne_lKb : ibPe ≠ lKb := by decide
@[simp] theorem ib_ibPe_ne_lFl : ibPe ≠ lFl := by decide
@[simp] theorem ib_ibPe_ne_lDh : ibPe ≠ lDh := by decide
@[simp] theorem ib_ibPe_ne_lDt : ibPe ≠ lDt := by decide
@[simp] theorem ib_ibPe_ne_lDg : ibPe ≠ lDg := by decide
@[simp] theorem ib_ibPe_ne_lDi : ibPe ≠ lDi := by decide
@[simp] theorem ib_ibPe_ne_lRp : ibPe ≠ lRp := by decide
@[simp] theorem ib_ibPe_ne_lRn : ibPe ≠ lRn := by decide
@[simp] theorem ib_ibPe_ne_lFle : ibPe ≠ lFle := by decide
@[simp] theorem ib_ibPe_ne_lDir : ibPe ≠ lDir := by decide
@[simp] theorem ib_ibPe_ne_kFu : ibPe ≠ kFu := by decide
@[simp] theorem ib_ibPe_ne_kD : ibPe ≠ kD := by decide
@[simp] theorem ib_ibPe_ne_kE : ibPe ≠ kE := by decide
@[simp] theorem ib_ibV1_ne_ibA : ibV1 ≠ ibA := by decide
@[simp] theorem ib_ibV1_ne_ibB : ibV1 ≠ ibB := by decide
@[simp] theorem ib_ibV1_ne_ibC : ibV1 ≠ ibC := by decide
@[simp] theorem ib_ibV1_ne_ibI : ibV1 ≠ ibI := by decide
@[simp] theorem ib_ibV1_ne_ibX : ibV1 ≠ ibX := by decide
@[simp] theorem ib_ibV1_ne_ibU : ibV1 ≠ ibU := by decide
@[simp] theorem ib_ibV1_ne_ibN : ibV1 ≠ ibN := by decide
@[simp] theorem ib_ibV1_ne_ibUs : ibV1 ≠ ibUs := by decide
@[simp] theorem ib_ibV1_ne_ibE : ibV1 ≠ ibE := by decide
@[simp] theorem ib_ibV1_ne_ibT1 : ibV1 ≠ ibT1 := by decide
@[simp] theorem ib_ibV1_ne_ibT2 : ibV1 ≠ ibT2 := by decide
@[simp] theorem ib_ibV1_ne_ibSn : ibV1 ≠ ibSn := by decide
@[simp] theorem ib_ibV1_ne_ibIx : ibV1 ≠ ibIx := by decide
@[simp] theorem ib_ibV1_ne_ibPe : ibV1 ≠ ibPe := by decide
@[simp] theorem ib_ibV1_ne_ibB1 : ibV1 ≠ ibB1 := by decide
@[simp] theorem ib_ibV1_ne_lKb : ibV1 ≠ lKb := by decide
@[simp] theorem ib_ibV1_ne_lFl : ibV1 ≠ lFl := by decide
@[simp] theorem ib_ibV1_ne_lDh : ibV1 ≠ lDh := by decide
@[simp] theorem ib_ibV1_ne_lDt : ibV1 ≠ lDt := by decide
@[simp] theorem ib_ibV1_ne_lDg : ibV1 ≠ lDg := by decide
@[simp] theorem ib_ibV1_ne_lDi : ibV1 ≠ lDi := by decide
@[simp] theorem ib_ibV1_ne_lRp : ibV1 ≠ lRp := by decide
@[simp] theorem ib_ibV1_ne_lRn : ibV1 ≠ lRn := by decide
@[simp] theorem ib_ibV1_ne_lFle : ibV1 ≠ lFle := by decide
@[simp] theorem ib_ibV1_ne_lDir : ibV1 ≠ lDir := by decide
@[simp] theorem ib_ibV1_ne_kFu : ibV1 ≠ kFu := by decide
@[simp] theorem ib_ibV1_ne_kD : ibV1 ≠ kD := by decide
@[simp] theorem ib_ibV1_ne_kE : ibV1 ≠ kE := by decide
@[simp] theorem ib_ibB1_ne_ibA : ibB1 ≠ ibA := by decide
@[simp] theorem ib_ibB1_ne_ibB : ibB1 ≠ ibB := by decide
@[simp] theorem ib_ibB1_ne_ibC : ibB1 ≠ ibC := by decide
@[simp] theorem ib_ibB1_ne_ibI : ibB1 ≠ ibI := by decide
@[simp] theorem ib_ibB1_ne_ibX : ibB1 ≠ ibX := by decide
@[simp] theorem ib_ibB1_ne_ibU : ibB1 ≠ ibU := by decide
@[simp] theorem ib_ibB1_ne_ibN : ibB1 ≠ ibN := by decide
@[simp] theorem ib_ibB1_ne_ibUs : ibB1 ≠ ibUs := by decide
@[simp] theorem ib_ibB1_ne_ibE : ibB1 ≠ ibE := by decide
@[simp] theorem ib_ibB1_ne_ibT1 : ibB1 ≠ ibT1 := by decide
@[simp] theorem ib_ibB1_ne_ibT2 : ibB1 ≠ ibT2 := by decide
@[simp] theorem ib_ibB1_ne_ibSn : ibB1 ≠ ibSn := by decide
@[simp] theorem ib_ibB1_ne_ibIx : ibB1 ≠ ibIx := by decide
@[simp] theorem ib_ibB1_ne_ibPe : ibB1 ≠ ibPe := by decide
@[simp] theorem ib_ibB1_ne_ibV1 : ibB1 ≠ ibV1 := by decide
@[simp] theorem ib_ibB1_ne_lKb : ibB1 ≠ lKb := by decide
@[simp] theorem ib_ibB1_ne_lFl : ibB1 ≠ lFl := by decide
@[simp] theorem ib_ibB1_ne_lDh : ibB1 ≠ lDh := by decide
@[simp] theorem ib_ibB1_ne_lDt : ibB1 ≠ lDt := by decide
@[simp] theorem ib_ibB1_ne_lDg : ibB1 ≠ lDg := by decide
@[simp] theorem ib_ibB1_ne_lDi : ibB1 ≠ lDi := by decide
@[simp] theorem ib_ibB1_ne_lRp : ibB1 ≠ lRp := by decide
@[simp] theorem ib_ibB1_ne_lRn : ibB1 ≠ lRn := by decide
@[simp] theorem ib_ibB1_ne_lFle : ibB1 ≠ lFle := by decide
@[simp] theorem ib_ibB1_ne_lDir : ibB1 ≠ lDir := by decide
@[simp] theorem ib_ibB1_ne_kFu : ibB1 ≠ kFu := by decide
@[simp] theorem ib_ibB1_ne_kD : ibB1 ≠ kD := by decide
@[simp] theorem ib_ibB1_ne_kE : ibB1 ≠ kE := by decide
@[simp] theorem ib_lKb_ne_ibA : lKb ≠ ibA := by decide
@[simp] theorem ib_lKb_ne_ibB : lKb ≠ ibB := by decide
@[simp] theorem ib_lKb_ne_ibC : lKb ≠ ibC := by decide
@[simp] theorem ib_lKb_ne_ibI : lKb ≠ ibI := by decide
@[simp] theorem ib_lKb_ne_ibX : lKb ≠ ibX := by decide
@[simp] theorem ib_lKb_ne_ibU : lKb ≠ ibU := by decide
@[simp] theorem ib_lKb_ne_ibN : lKb ≠ ibN := by decide
@[simp] theorem ib_lKb_ne_ibUs : lKb ≠ ibUs := by decide
@[simp] theorem ib_lKb_ne_ibE : lKb ≠ ibE := by decide
@[simp] theorem ib_lKb_ne_ibT1 : lKb ≠ ibT1 := by decide
@[simp] theorem ib_lKb_ne_ibT2 : lKb ≠ ibT2 := by decide
@[simp] theorem ib_lKb_ne_ibSn : lKb ≠ ibSn := by decide
@[simp] theorem ib_lKb_ne_ibIx : lKb ≠ ibIx := by decide
@[simp] theorem ib_lKb_ne_ibPe : lKb ≠ ibPe := by decide
@[simp] theorem ib_lKb_ne_ibV1 : lKb ≠ ibV1 := by decide
@[simp] theorem ib_lKb_ne_ibB1 : lKb ≠ ibB1 := by decide
@[simp] theorem ib_lFl_ne_ibA : lFl ≠ ibA := by decide
@[simp] theorem ib_lFl_ne_ibB : lFl ≠ ibB := by decide
@[simp] theorem ib_lFl_ne_ibC : lFl ≠ ibC := by decide
@[simp] theorem ib_lFl_ne_ibI : lFl ≠ ibI := by decide
@[simp] theorem ib_lFl_ne_ibX : lFl ≠ ibX := by decide
@[simp] theorem ib_lFl_ne_ibU : lFl ≠ ibU := by decide
@[simp] theorem ib_lFl_ne_ibN : lFl ≠ ibN := by decide
@[simp] theorem ib_lFl_ne_ibUs : lFl ≠ ibUs := by decide
@[simp] theorem ib_lFl_ne_ibE : lFl ≠ ibE := by decide
@[simp] theorem ib_lFl_ne_ibT1 : lFl ≠ ibT1 := by decide
@[simp] theorem ib_lFl_ne_ibT2 : lFl ≠ ibT2 := by decide
@[simp] theorem ib_lFl_ne_ibSn : lFl ≠ ibSn := by decide
@[simp] theorem ib_lFl_ne_ibIx : lFl ≠ ibIx := by decide
@[simp] theorem ib_lFl_ne_ibPe : lFl ≠ ibPe := by decide
@[simp] theorem ib_lFl_ne_ibV1 : lFl ≠ ibV1 := by decide
@[simp] theorem ib_lFl_ne_ibB1 : lFl ≠ ibB1 := by decide
@[simp] theorem ib_lDh_ne_ibA : lDh ≠ ibA := by decide
@[simp] theorem ib_lDh_ne_ibB : lDh ≠ ibB := by decide
@[simp] theorem ib_lDh_ne_ibC : lDh ≠ ibC := by decide
@[simp] theorem ib_lDh_ne_ibI : lDh ≠ ibI := by decide
@[simp] theorem ib_lDh_ne_ibX : lDh ≠ ibX := by decide
@[simp] theorem ib_lDh_ne_ibU : lDh ≠ ibU := by decide
@[simp] theorem ib_lDh_ne_ibN : lDh ≠ ibN := by decide
@[simp] theorem ib_lDh_ne_ibUs : lDh ≠ ibUs := by decide
@[simp] theorem ib_lDh_ne_ibE : lDh ≠ ibE := by decide
@[simp] theorem ib_lDh_ne_ibT1 : lDh ≠ ibT1 := by decide
@[simp] theorem ib_lDh_ne_ibT2 : lDh ≠ ibT2 := by decide
@[simp] theorem ib_lDh_ne_ibSn : lDh ≠ ibSn := by decide
@[simp] theorem ib_lDh_ne_ibIx : lDh ≠ ibIx := by decide
@[simp] theorem ib_lDh_ne_ibPe : lDh ≠ ibPe := by decide
@[simp] theorem ib_lDh_ne_ibV1 : lDh ≠ ibV1 := by decide
@[simp] theorem ib_lDh_ne_ibB1 : lDh ≠ ibB1 := by decide
@[simp] theorem ib_lDt_ne_ibA : lDt ≠ ibA := by decide
@[simp] theorem ib_lDt_ne_ibB : lDt ≠ ibB := by decide
@[simp] theorem ib_lDt_ne_ibC : lDt ≠ ibC := by decide
@[simp] theorem ib_lDt_ne_ibI : lDt ≠ ibI := by decide
@[simp] theorem ib_lDt_ne_ibX : lDt ≠ ibX := by decide
@[simp] theorem ib_lDt_ne_ibU : lDt ≠ ibU := by decide
@[simp] theorem ib_lDt_ne_ibN : lDt ≠ ibN := by decide
@[simp] theorem ib_lDt_ne_ibUs : lDt ≠ ibUs := by decide
@[simp] theorem ib_lDt_ne_ibE : lDt ≠ ibE := by decide
@[simp] theorem ib_lDt_ne_ibT1 : lDt ≠ ibT1 := by decide
@[simp] theorem ib_lDt_ne_ibT2 : lDt ≠ ibT2 := by decide
@[simp] theorem ib_lDt_ne_ibSn : lDt ≠ ibSn := by decide
@[simp] theorem ib_lDt_ne_ibIx : lDt ≠ ibIx := by decide
@[simp] theorem ib_lDt_ne_ibPe : lDt ≠ ibPe := by decide
@[simp] theorem ib_lDt_ne_ibV1 : lDt ≠ ibV1 := by decide
@[simp] theorem ib_lDt_ne_ibB1 : lDt ≠ ibB1 := by decide
@[simp] theorem ib_lDg_ne_ibA : lDg ≠ ibA := by decide
@[simp] theorem ib_lDg_ne_ibB : lDg ≠ ibB := by decide
@[simp] theorem ib_lDg_ne_ibC : lDg ≠ ibC := by decide
@[simp] theorem ib_lDg_ne_ibI : lDg ≠ ibI := by decide
@[simp] theorem ib_lDg_ne_ibX : lDg ≠ ibX := by decide
@[simp] theorem ib_lDg_ne_ibU : lDg ≠ ibU := by decide
@[simp] theorem ib_lDg_ne_ibN : lDg ≠ ibN := by decide
@[simp] theorem ib_lDg_ne_ibUs : lDg ≠ ibUs := by decide
@[simp] theorem ib_lDg_ne_ibE : lDg ≠ ibE := by decide
@[simp] theorem ib_lDg_ne_ibT1 : lDg ≠ ibT1 := by decide
@[simp] theorem ib_lDg_ne_ibT2 : lDg ≠ ibT2 := by decide
@[simp] theorem ib_lDg_ne_ibSn : lDg ≠ ibSn := by decide
@[simp] theorem ib_lDg_ne_ibIx : lDg ≠ ibIx := by decide
@[simp] theorem ib_lDg_ne_ibPe : lDg ≠ ibPe := by decide
@[simp] theorem ib_lDg_ne_ibV1 : lDg ≠ ibV1 := by decide
@[simp] theorem ib_lDg_ne_ibB1 : lDg ≠ ibB1 := by decide
@[simp] theorem ib_lDi_ne_ibA : lDi ≠ ibA := by decide
@[simp] theorem ib_lDi_ne_ibB : lDi ≠ ibB := by decide
@[simp] theorem ib_lDi_ne_ibC : lDi ≠ ibC := by decide
@[simp] theorem ib_lDi_ne_ibI : lDi ≠ ibI := by decide
@[simp] theorem ib_lDi_ne_ibX : lDi ≠ ibX := by decide
@[simp] theorem ib_lDi_ne_ibU : lDi ≠ ibU := by decide
@[simp] theorem ib_lDi_ne_ibN : lDi ≠ ibN := by decide
@[simp] theorem ib_lDi_ne_ibUs : lDi ≠ ibUs := by decide
@[simp] theorem ib_lDi_ne_ibE : lDi ≠ ibE := by decide
@[simp] theorem ib_lDi_ne_ibT1 : lDi ≠ ibT1 := by decide
@[simp] theorem ib_lDi_ne_ibT2 : lDi ≠ ibT2 := by decide
@[simp] theorem ib_lDi_ne_ibSn : lDi ≠ ibSn := by decide
@[simp] theorem ib_lDi_ne_ibIx : lDi ≠ ibIx := by decide
@[simp] theorem ib_lDi_ne_ibPe : lDi ≠ ibPe := by decide
@[simp] theorem ib_lDi_ne_ibV1 : lDi ≠ ibV1 := by decide
@[simp] theorem ib_lDi_ne_ibB1 : lDi ≠ ibB1 := by decide
@[simp] theorem ib_lRp_ne_ibA : lRp ≠ ibA := by decide
@[simp] theorem ib_lRp_ne_ibB : lRp ≠ ibB := by decide
@[simp] theorem ib_lRp_ne_ibC : lRp ≠ ibC := by decide
@[simp] theorem ib_lRp_ne_ibI : lRp ≠ ibI := by decide
@[simp] theorem ib_lRp_ne_ibX : lRp ≠ ibX := by decide
@[simp] theorem ib_lRp_ne_ibU : lRp ≠ ibU := by decide
@[simp] theorem ib_lRp_ne_ibN : lRp ≠ ibN := by decide
@[simp] theorem ib_lRp_ne_ibUs : lRp ≠ ibUs := by decide
@[simp] theorem ib_lRp_ne_ibE : lRp ≠ ibE := by decide
@[simp] theorem ib_lRp_ne_ibT1 : lRp ≠ ibT1 := by decide
@[simp] theorem ib_lRp_ne_ibT2 : lRp ≠ ibT2 := by decide
@[simp] theorem ib_lRp_ne_ibSn : lRp ≠ ibSn := by decide
@[simp] theorem ib_lRp_ne_ibIx : lRp ≠ ibIx := by decide
@[simp] theorem ib_lRp_ne_ibPe : lRp ≠ ibPe := by decide
@[simp] theorem ib_lRp_ne_ibV1 : lRp ≠ ibV1 := by decide
@[simp] theorem ib_lRp_ne_ibB1 : lRp ≠ ibB1 := by decide
@[simp] theorem ib_lRn_ne_ibA : lRn ≠ ibA := by decide
@[simp] theorem ib_lRn_ne_ibB : lRn ≠ ibB := by decide
@[simp] theorem ib_lRn_ne_ibC : lRn ≠ ibC := by decide
@[simp] theorem ib_lRn_ne_ibI : lRn ≠ ibI := by decide
@[simp] theorem ib_lRn_ne_ibX : lRn ≠ ibX := by decide
@[simp] theorem ib_lRn_ne_ibU : lRn ≠ ibU := by decide
@[simp] theorem ib_lRn_ne_ibN : lRn ≠ ibN := by decide
@[simp] theorem ib_lRn_ne_ibUs : lRn ≠ ibUs := by decide
@[simp] theorem ib_lRn_ne_ibE : lRn ≠ ibE := by decide
@[simp] theorem ib_lRn_ne_ibT1 : lRn ≠ ibT1 := by decide
@[simp] theorem ib_lRn_ne_ibT2 : lRn ≠ ibT2 := by decide
@[simp] theorem ib_lRn_ne_ibSn : lRn ≠ ibSn := by decide
@[simp] theorem ib_lRn_ne_ibIx : lRn ≠ ibIx := by decide
@[simp] theorem ib_lRn_ne_ibPe : lRn ≠ ibPe := by decide
@[simp] theorem ib_lRn_ne_ibV1 : lRn ≠ ibV1 := by decide
@[simp] theorem ib_lRn_ne_ibB1 : lRn ≠ ibB1 := by decide
@[simp] theorem ib_lFle_ne_ibA : lFle ≠ ibA := by decide
@[simp] theorem ib_lFle_ne_ibB : lFle ≠ ibB := by decide
@[simp] theorem ib_lFle_ne_ibC : lFle ≠ ibC := by decide
@[simp] theorem ib_lFle_ne_ibI : lFle ≠ ibI := by decide
@[simp] theorem ib_lFle_ne_ibX : lFle ≠ ibX := by decide
@[simp] theorem ib_lFle_ne_ibU : lFle ≠ ibU := by decide
@[simp] theorem ib_lFle_ne_ibN : lFle ≠ ibN := by decide
@[simp] theorem ib_lFle_ne_ibUs : lFle ≠ ibUs := by decide
@[simp] theorem ib_lFle_ne_ibE : lFle ≠ ibE := by decide
@[simp] theorem ib_lFle_ne_ibT1 : lFle ≠ ibT1 := by decide
@[simp] theorem ib_lFle_ne_ibT2 : lFle ≠ ibT2 := by decide
@[simp] theorem ib_lFle_ne_ibSn : lFle ≠ ibSn := by decide
@[simp] theorem ib_lFle_ne_ibIx : lFle ≠ ibIx := by decide
@[simp] theorem ib_lFle_ne_ibPe : lFle ≠ ibPe := by decide
@[simp] theorem ib_lFle_ne_ibV1 : lFle ≠ ibV1 := by decide
@[simp] theorem ib_lFle_ne_ibB1 : lFle ≠ ibB1 := by decide
@[simp] theorem ib_lDir_ne_ibA : lDir ≠ ibA := by decide
@[simp] theorem ib_lDir_ne_ibB : lDir ≠ ibB := by decide
@[simp] theorem ib_lDir_ne_ibC : lDir ≠ ibC := by decide
@[simp] theorem ib_lDir_ne_ibI : lDir ≠ ibI := by decide
@[simp] theorem ib_lDir_ne_ibX : lDir ≠ ibX := by decide
@[simp] theorem ib_lDir_ne_ibU : lDir ≠ ibU := by decide
@[simp] theorem ib_lDir_ne_ibN : lDir ≠ ibN := by decide
@[simp] theorem ib_lDir_ne_ibUs : lDir ≠ ibUs := by decide
@[simp] theorem ib_lDir_ne_ibE : lDir ≠ ibE := by decide
@[simp] theorem ib_lDir_ne_ibT1 : lDir ≠ ibT1 := by decide
@[simp] theorem ib_lDir_ne_ibT2 : lDir ≠ ibT2 := by decide
@[simp] theorem ib_lDir_ne_ibSn : lDir ≠ ibSn := by decide
@[simp] theorem ib_lDir_ne_ibIx : lDir ≠ ibIx := by decide
@[simp] theorem ib_lDir_ne_ibPe : lDir ≠ ibPe := by decide
@[simp] theorem ib_lDir_ne_ibV1 : lDir ≠ ibV1 := by decide
@[simp] theorem ib_lDir_ne_ibB1 : lDir ≠ ibB1 := by decide
@[simp] theorem ib_kFu_ne_ibA : kFu ≠ ibA := by decide
@[simp] theorem ib_kFu_ne_ibB : kFu ≠ ibB := by decide
@[simp] theorem ib_kFu_ne_ibC : kFu ≠ ibC := by decide
@[simp] theorem ib_kFu_ne_ibI : kFu ≠ ibI := by decide
@[simp] theorem ib_kFu_ne_ibX : kFu ≠ ibX := by decide
@[simp] theorem ib_kFu_ne_ibU : kFu ≠ ibU := by decide
@[simp] theorem ib_kFu_ne_ibN : kFu ≠ ibN := by decide
@[simp] theorem ib_kFu_ne_ibUs : kFu ≠ ibUs := by decide
@[simp] theorem ib_kFu_ne_ibE : kFu ≠ ibE := by decide
@[simp] theorem ib_kFu_ne_ibT1 : kFu ≠ ibT1 := by decide
@[simp] theorem ib_kFu_ne_ibT2 : kFu ≠ ibT2 := by decide
@[simp] theorem ib_kFu_ne_ibSn : kFu ≠ ibSn := by decide
@[simp] theorem ib_kFu_ne_ibIx : kFu ≠ ibIx := by decide
@[simp] theorem ib_kFu_ne_ibPe : kFu ≠ ibPe := by decide
@[simp] theorem ib_kFu_ne_ibV1 : kFu ≠ ibV1 := by decide
@[simp] theorem ib_kFu_ne_ibB1 : kFu ≠ ibB1 := by decide
@[simp] theorem ib_kD_ne_ibA : kD ≠ ibA := by decide
@[simp] theorem ib_kD_ne_ibB : kD ≠ ibB := by decide
@[simp] theorem ib_kD_ne_ibC : kD ≠ ibC := by decide
@[simp] theorem ib_kD_ne_ibI : kD ≠ ibI := by decide
@[simp] theorem ib_kD_ne_ibX : kD ≠ ibX := by decide
@[simp] theorem ib_kD_ne_ibU : kD ≠ ibU := by decide
@[simp] theorem ib_kD_ne_ibN : kD ≠ ibN := by decide
@[simp] theorem ib_kD_ne_ibUs : kD ≠ ibUs := by decide
@[simp] theorem ib_kD_ne_ibE : kD ≠ ibE := by decide
@[simp] theorem ib_kD_ne_ibT1 : kD ≠ ibT1 := by decide
@[simp] theorem ib_kD_ne_ibT2 : kD ≠ ibT2 := by decide
@[simp] theorem ib_kD_ne_ibSn : kD ≠ ibSn := by decide
@[simp] theorem ib_kD_ne_ibIx : kD ≠ ibIx := by decide
@[simp] theorem ib_kD_ne_ibPe : kD ≠ ibPe := by decide
@[simp] theorem ib_kD_ne_ibV1 : kD ≠ ibV1 := by decide
@[simp] theorem ib_kD_ne_ibB1 : kD ≠ ibB1 := by decide
@[simp] theorem ib_kE_ne_ibA : kE ≠ ibA := by decide
@[simp] theorem ib_kE_ne_ibB : kE ≠ ibB := by decide
@[simp] theorem ib_kE_ne_ibC : kE ≠ ibC := by decide
@[simp] theorem ib_kE_ne_ibI : kE ≠ ibI := by decide
@[simp] theorem ib_kE_ne_ibX : kE ≠ ibX := by decide
@[simp] theorem ib_kE_ne_ibU : kE ≠ ibU := by decide
@[simp] theorem ib_kE_ne_ibN : kE ≠ ibN := by decide
@[simp] theorem ib_kE_ne_ibUs : kE ≠ ibUs := by decide
@[simp] theorem ib_kE_ne_ibE : kE ≠ ibE := by decide
@[simp] theorem ib_kE_ne_ibT1 : kE ≠ ibT1 := by decide
@[simp] theorem ib_kE_ne_ibT2 : kE ≠ ibT2 := by decide
@[simp] theorem ib_kE_ne_ibSn : kE ≠ ibSn := by decide
@[simp] theorem ib_kE_ne_ibIx : kE ≠ ibIx := by decide
@[simp] theorem ib_kE_ne_ibPe : kE ≠ ibPe := by decide
@[simp] theorem ib_kE_ne_ibV1 : kE ≠ ibV1 := by decide
@[simp] theorem ib_kE_ne_ibB1 : kE ≠ ibB1 := by decide

def ibsParams : List MlS := [ibU]
def ibcParams : List MlS := [ibN, ibUs]
def iblParams : List MlS := [ibE]
def ifaParams : List MlS := [kFu, kD, ibT1, ibT2]
def iprParams : List MlS := [kFu, kD, ibSn, ibIx, ibPe]
def iltParams : List MlS := [kFu, kD, ibT1, ibV1, ibB1]

def ibLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, ibA, ibB, ibC, ibI, ibX]

def ibFvK : ProgHOL 64 := .ite (.cmp .lower (vv ibI) (vv kD)) (.return (vv ibA)) hang

def ibPrK : ProgHOL 64 :=
  .seq (.call (some (some (.local, ibX), none)) fIpr [vv kFu, vv kD, vv ibA, vv ibI, vv ibB]) (.return (vv ibX))

def ibCore : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv kE)) (.seq eViewP
  (.ite (.cmp .equal (vv lDg) (.const 2))
    (.seq (.assign .local ibA (.load .one (vv lRp)))
      (.seq (.call (some (some (.local, ibX), none)) fIbs [vv ibA]) (.return (vv ibX))))
  (.ite (.cmp .equal (vv lDg) (.const 1))
    (.seq (.assign .local ibA (.load .one (vv lRp)))
    (.ite (.cmp .equal (vv lRn) (.const 1)) (.seq (.assign .local ibI (.const 0)) ibFvK)
      (.ite (.cmp .equal (vv lRn) (.const 2))
        (.seq (.assign .local ibI (.load .one (.op .add [vv lRp, .const 8]))) ibFvK) hang)))
  (.ite (.cmp .equal (vv lDg) (.const 3))
    (.seq (.assign .local ibA (.load .one (vv lRp))) (.seq (.assign .local ibB (.load .one (.op .add [vv lRp, .const 8])))
      (.seq (.call (some (some (.local, ibX), none)) fIbc [vv ibA, vv ibB]) (.return (vv ibX)))))
  (.ite (.cmp .equal (vv lDg) (.const 8))
    (.seq (.call (some (some (.local, ibX), none)) fIbl [vv kE]) (.return (vv ibX)))
  (.ite (.cmp .equal (vv lDg) (.const 6))
    (.seq (.assign .local ibA (.load .one (vv lRp))) (.seq (.assign .local ibB (.load .one (.op .add [vv lRp, .const 8])))
      (.seq (.call (some (some (.local, ibX), none)) fIfa [vv kFu, vv kD, vv ibA, vv ibB]) (.return (vv ibX)))))
  (.ite (.cmp .equal (vv lDg) (.const 5))
    (.seq (.assign .local ibA (.load .one (vv lRp))) (.seq (.assign .local ibB (.load .one (.op .add [vv lRp, .const 8])))
      (.seq (.call (some (some (.local, ibX), none)) fIla [vv kFu, vv kD, vv ibA, vv ibB]) (.return (vv ibX)))))
  (.ite (.cmp .equal (vv lDg) (.const 4))
    (.seq (.call (some (some (.local, ibX), none)) fIap [vv kFu, vv kD, vv kE]) (.return (vv ibX)))
  (.ite (.cmp .equal (vv lDg) (.const 9))
    (.seq (.assign .local ibA (.load .one (vv lRp))) (.seq (.assign .local ibB (.load .one (.op .add [vv lRp, .const 8])))
    (.ite (.cmp .equal (vv lRn) (.const 2)) (.seq (.assign .local ibI (.const 0)) ibPrK)
      (.ite (.cmp .equal (vv lRn) (.const 3))
        (.seq (.assign .local ibI (.load .one (.op .add [vv lRp, .const 16]))) ibPrK) hang))))
  (.ite (.cmp .equal (vv lDg) (.const 7))
    (.seq (.assign .local ibA (.load .one (vv lRp))) (.seq (.assign .local ibB (.load .one (.op .add [vv lRp, .const 8])))
      (.seq (.assign .local ibC (.load .one (.op .add [vv lRp, .const 16])))
        (.seq (.call (some (some (.local, ibX), none)) fIlt [vv kFu, vv kD, vv ibA, vv ibB, vv ibC]) (.return (vv ibX))))))
    hang)))))))))))

def ibBody : ProgHOL 64 := prologue ibLocals ibCore

section
variable {σ : Type}

theorem ib_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ibLocals → (ctxEnv C ++ kParams.zip vals).get x = none :=
  Knot.params_none C ibLocals kParams vals (by decide) (by decide)

/-- Call an entry-shaped callee (`PostK`), then return its answer. -/
theorem specR_callKR {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {m : AM EIdx}
    (x f : MlS) (ps : List MlS) (es : List (ExpHOL 64)) (Bd : ProgHOL 64) (vs : List (BitVec 64))
    (hnd : ps.Nodup) (hl : vs.length = ps.length) (hx : x ∈ D)
    (hC : C.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), Bd, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs)
    (hspec : SpecR (σ := σ) (Pre C s (ps.zip vs)) Bd s m (PostK C)) :
    SpecR (σ := σ) (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f es) (.return (vv x))) s m (PostK C) := by
  refine specR_congr (m' := m >>= fun r => pure r) (by simp) ?_
  refine specR_callNIH x f ps es Bd vs hnd hl hx hC hes (PostK C) (fun a w _ _ => w = Enc.idxW a)
    (fun a w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ps vs hl hlk) hspec) (fun a w s' H' hp hw => ?_)
  subst hw
  exact specR_returnI _ (Enc.idxW a) (by simp) (fun t ht => ⟨H', hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

structure IbCodes (C : Ctx) (Bs Bc Bl Bfa Bla Bap Bpr Blt : ProgHOL 64) : Prop where
  s : C.code.lookup fIbs = some (ibsParams.map (fun p => (p, ShapeHOL.one)), Bs, .one)
  c : C.code.lookup fIbc = some (ibcParams.map (fun p => (p, ShapeHOL.one)), Bc, .one)
  l : C.code.lookup fIbl = some (iblParams.map (fun p => (p, ShapeHOL.one)), Bl, .one)
  fa : C.code.lookup fIfa = some (ifaParams.map (fun p => (p, ShapeHOL.one)), Bfa, .one)
  la : C.code.lookup fIla = some (ifaParams.map (fun p => (p, ShapeHOL.one)), Bla, .one)
  ap : C.code.lookup fIap = some (kParams.map (fun p => (p, ShapeHOL.one)), Bap, .one)
  pr : C.code.lookup fIpr = some (iprParams.map (fun p => (p, ShapeHOL.one)), Bpr, .one)
  lt : C.code.lookup fIlt = some (iltParams.map (fun p => (p, ShapeHOL.one)), Blt, .one)

theorem ib_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) (Bs Bc Bl Bfa Bla Bap Bpr Blt : ProgHOL 64)
    (hc : IbCodes C Bs Bc Bl Bfa Bla Bap Bpr Blt) (s : AState) (d : Nat) (e : EIdx) (hd : d < 2 ^ 64)
    (hSort : ∀ u, SpecR (σ := σ) (Pre C s (ibsParams.zip [Enc.idxW u])) Bs s (ibSortT u) (PostK C))
    (hConst : ∀ c us, SpecR (σ := σ) (Pre C s (ibcParams.zip [Enc.idxW c, Enc.idxW us])) Bc s (ibConstT C.fe c us)
      (PostK C))
    (hLit : ∀ l, s.store.view e = some (.lit l) →
      SpecR (σ := σ) (Pre C s (iblParams.zip [Enc.idxW e])) Bl s (ibLitT C.fe l) (PostK C))
    (hFa : ∀ ty b, SpecR (σ := σ) (Pre C s (ifaParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty,
      Enc.idxW b])) Bfa s (inferForall (knot mode C n) C.fe d ty b) (PostK C))
    (hLa : ∀ ty b, SpecR (σ := σ) (Pre C s (ifaParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty,
      Enc.idxW b])) Bla s (inferLam (knot mode C n) d ty b) (PostK C))
    (hAp : SpecR (σ := σ) (Pre C s (kParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e])) Bap s
      (inferApp (knot mode C n) C.fe d e) (PostK C))
    (hPr : ∀ sn i pe, i < 2 ^ 64 → SpecR (σ := σ) (Pre C s (iprParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d,
      Enc.idxW sn, BitVec.ofNat 64 i, Enc.idxW pe])) Bpr s (inferProj (knot mode C n) C.fe d sn i pe) (PostK C))
    (hLet : ∀ ty v b, SpecR (σ := σ) (Pre C s (iltParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty,
      Enc.idxW v, Enc.idxW b])) Blt s (ibLetT (knot mode C n) C.fe d ty v b) (PostK C)) :
    SpecR (σ := σ) (Pre C s (kParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e])) ibBody s
      (ConRon.Arena.inferBody (knot mode C n) C.fe d e) (PostK C) := by
  refine specR_prologue (postK_locals C) (ib_none C _) ?_
  rw [inferBody_eq]
  unfold ibCore
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv kE) (Enc.idxW e) (by decide) (by simp +decide [Env.get, kParams, ctxEnv]) ?_
  refine specR_viewP e (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
    (fun v P hv htn hsh => ?_)
  refine specR_congr (view_bind_eq e v _ s hv) ?_
  rcases v with i | ⟨idx, ty⟩ | u | ⟨c, us⟩ | ⟨f, a⟩ | ⟨ty, b⟩ | ⟨ty, b⟩ | ⟨ty, v, b⟩ | l | ⟨sn, i, pe⟩
  · -- bvar
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_hangI
  · -- fvar
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' ibA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encFVar] using wordsAt_mem0 P _ _ []) ?_
    have hK : ∀ (Γ' : Env) (M' : Mem), idx < 2 ^ 64 → Γ'.get ibI = some (BitVec.ofNat 64 idx) →
        Γ'.get ibA = some (Enc.idxW ty) → Γ'.get kD = some (BitVec.ofNat 64 d) →
        SpecR (σ := σ) (Inv C s Γ' M' (ctxLocals ++ ibLocals)) ibFvK s
          (if idx < d then pure ty else fail (.invalid "free variable out of scope")) (PostK C) := by
      intro Γ' M' hib hI hA hD
      unfold ibFvK
      have hlt := Big.word_lt_iff idx d (by unfold B; omega) (by unfold B; omega)
      by_cases hid : idx < d
      · rw [if_pos hid]
        refine specR_ifI _ 1 (by simp [sev, hI, hD, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlt.mpr hid]) (fun _ => ?_)
          (fun h => absurd h (by decide))
        exact specR_returnI _ (Enc.idxW ty) (by simp [hA]) (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      · refine specR_ifI _ 0 (by simp [sev, hI, hD, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
          (fun h => absurd rfl h) (fun _ => specR_hangI)
    have hlen : (encEView (.fvar idx ty)).length = 1 + (Enc.limbs idx).length := by
      simp [encEView, Enc.encFVar]; omega
    by_cases i0 : idx = 0
    · subst i0
      refine specR_ifI _ 1 (by simp +decide [sev, hlen, Enc.limbs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun hw => absurd hw (by decide))
      refine specR_assignI ibI (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
      refine hK _ _ (by decide) ?_ ?_ ?_ <;> simp +decide [Env.get, kParams, ctxEnv]
    · by_cases ib : idx < 2 ^ 64
      · have hl : Enc.limbs idx = [BitVec.ofNat 64 idx] := by rw [limbs_small idx ib]; simp [i0]
        refine specR_ifI _ 0 (by simp +decide [sev, hlen, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
        refine specR_ifI _ 1 (by simp +decide [sev, hlen, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_loadI' ibI _ (P + 8) (P + BitVec.ofNat 64 8) (BitVec.ofNat 64 idx) (by decide)
          (by simp +decide [sev]) rfl
          (by have := wordsAt_mem1 P (Enc.idxW ty) (BitVec.ofNat 64 idx) [] (M := []); simpa [encEView, Enc.encFVar, hl] using this) ?_
        refine hK _ _ ib ?_ ?_ ?_ <;> simp +decide [Env.get, kParams, ctxEnv]
      · have hl := ExI.limbs_len_ge2 idx (by omega)
        have hlt : 1 + (Enc.limbs idx).length < 2 ^ 61 := by rw [← hlen]; exact hsh
        have hn1 : BitVec.ofNat 64 (1 + (Enc.limbs idx).length) ≠ 1#64 := by
          intro e; have := congrArg BitVec.toNat e; simp at this; omega
        have hn2 : BitVec.ofNat 64 (1 + (Enc.limbs idx).length) ≠ 2#64 := by
          intro e; have := congrArg BitVec.toNat e; simp at this; omega
        refine specR_ifI _ 0 (by simp +decide [sev, hlen, hn1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
        exact specR_ifI _ 0 (by simp +decide [sev, hlen, hn2, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => specR_hangI)
  · -- sort
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' ibA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW u) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encSort] using wordsAt_mem0 P _ _ []) ?_
    exact specR_callKR ibX fIbs ibsParams [vv ibA] Bs [Enc.idxW u] (by decide) rfl (by decide) hc.s
      ⟨by simp, trivial⟩ (hSort u)
  · -- const
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' ibA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW c) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P _ _ []) ?_
    refine specR_loadI' ibB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW us) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P _ _ [] []) ?_
    exact specR_callKR ibX fIbc ibcParams [vv ibA, vv ibB] Bc [Enc.idxW c, Enc.idxW us] (by decide) rfl (by decide) hc.c
      ⟨by simp, by simp, trivial⟩ (hConst c us)
  · -- app
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_callKR ibX fIap kParams [vv kFu, vv kD, vv kE] Bap [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e]
      (by decide) rfl (by decide) hc.ap ⟨by simp +decide [Env.get, kParams, ctxEnv], by simp +decide [Env.get, kParams, ctxEnv], by simp +decide [Env.get, kParams, ctxEnv], trivial⟩ hAp
  · -- la
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' ibA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P _ _ []) ?_
    refine specR_loadI' ibB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P _ _ [] []) ?_
    exact specR_callKR ibX fIla ifaParams [vv kFu, vv kD, vv ibA, vv ibB] Bla
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty, Enc.idxW b] (by decide) rfl (by decide) hc.la
      ⟨by simp +decide [Env.get, kParams, ctxEnv], by simp +decide [Env.get, kParams, ctxEnv], by simp, by simp, trivial⟩ (hLa ty b)
  · -- fa
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' ibA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P _ _ []) ?_
    refine specR_loadI' ibB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P _ _ [] []) ?_
    exact specR_callKR ibX fIfa ifaParams [vv kFu, vv kD, vv ibA, vv ibB] Bfa
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty, Enc.idxW b] (by decide) rfl (by decide) hc.fa
      ⟨by simp +decide [Env.get, kParams, ctxEnv], by simp +decide [Env.get, kParams, ctxEnv], by simp, by simp, trivial⟩ (hFa ty b)
  · -- letE
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' ibA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encLet] using wordsAt_mem0 P _ _ []) ?_
    refine specR_loadI' ibB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW v) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encLet] using wordsAt_mem1 P _ _ [Enc.idxW b] []) ?_
    refine specR_loadI' ibC _ (P + 16) (P + BitVec.ofNat 64 (8 * 2)) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encLet] using (wordsAt_get P [Enc.idxW ty, Enc.idxW v, Enc.idxW b] 2 (by simp) [] : (P + BitVec.ofNat 64 (8 * 2), Enc.idxW b) ∈ _)) ?_
    exact specR_callKR ibX fIlt iltParams [vv kFu, vv kD, vv ibA, vv ibB, vv ibC] Blt
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty, Enc.idxW v, Enc.idxW b] (by decide) rfl (by decide) hc.lt
      ⟨by simp +decide [Env.get, kParams, ctxEnv], by simp +decide [Env.get, kParams, ctxEnv], by simp, by simp, by simp, trivial⟩ (hLet ty v b)
  · -- lit
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_callKR ibX fIbl iblParams [vv kE] Bl [Enc.idxW e] (by decide) rfl (by decide) hc.l
      ⟨by simp +decide [Env.get, kParams, ctxEnv], trivial⟩ (hLit l hv)
  · -- proj
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    have er : encEView (.proj sn i pe) = Enc.idxW sn :: Enc.idxW pe :: Enc.limbs i := rfl
    refine specR_loadI' ibA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW sn) (by decide) (by simp) (by simp)
      (by simpa [er] using wordsAt_mem0 P (Enc.idxW sn) (Enc.idxW pe :: Enc.limbs i) []) ?_
    refine specR_loadI' ibB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW pe) (by decide) (by simp +decide [sev]) rfl
      (by simpa [er] using wordsAt_mem1 P (Enc.idxW sn) (Enc.idxW pe) (Enc.limbs i) []) ?_
    have hlen : (encEView (.proj sn i pe)).length = (Enc.limbs i).length + 2 := by rw [er]; simp
    have hl58 : (Enc.limbs i).length + 2 < 2 ^ 61 := by rw [← hlen]; exact hsh
    rcases (by omega : (Enc.limbs i).length = 0 ∨ (Enc.limbs i).length = 1 ∨ 2 ≤ (Enc.limbs i).length) with h0 | h1 | h2
    · have hi0 : i = 0 := by have := (limbs_length_lt_iff i 0).mp (by omega); simpa using this
      subst hi0
      refine specR_ifI _ 1 (by simp [sev, hlen, h0, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      refine specR_assignI ibI (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
      exact specR_callKR ibX fIpr iprParams [vv kFu, vv kD, vv ibA, vv ibI, vv ibB] Bpr
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW sn, BitVec.ofNat 64 0, Enc.idxW pe] (by decide) rfl (by decide) hc.pr
        ⟨by simp +decide [Env.get, kParams, ctxEnv], by simp +decide [Env.get, kParams, ctxEnv], by simp, by simp, by simp, trivial⟩ (hPr sn 0 pe (by decide))
    · have hiB : i < B := by have := (limbs_length_lt_iff i 1).mp (by omega); simpa using this
      have h2w : BitVec.ofNat 64 ((Enc.limbs i).length + 2) ≠ 2#64 := by rw [h1]; decide
      refine specR_ifI _ 0 (by simp [sev, hlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact h2w)
        (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp [sev, hlen, h1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      have hx2 : (Enc.idxW sn :: Enc.idxW pe :: Enc.limbs i)[2]'(by simp; omega) = BitVec.ofNat 64 i := by
        show (Enc.limbs i)[0]'(by omega) = _
        rw [limbs_getElem i 0 (by omega)]; simp [Nat.mod_eq_of_lt hiB]
      refine specR_loadI' ibI _ (P + 16) (P + BitVec.ofNat 64 (8 * 2)) (BitVec.ofNat 64 i) (by decide)
        (by simp +decide [sev]) rfl (by
          have := wordsAt_get P (Enc.idxW sn :: Enc.idxW pe :: Enc.limbs i) 2 (by simp; omega) []
          rw [hx2] at this; simpa [er] using this) ?_
      exact specR_callKR ibX fIpr iprParams [vv kFu, vv kD, vv ibA, vv ibI, vv ibB] Bpr
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW sn, BitVec.ofNat 64 i, Enc.idxW pe] (by decide) rfl (by decide) hc.pr
        ⟨by simp +decide [Env.get, kParams, ctxEnv], by simp +decide [Env.get, kParams, ctxEnv], by simp, by simp, by simp, trivial⟩ (hPr sn i pe hiB)
    · have h2w : BitVec.ofNat 64 ((Enc.limbs i).length + 2) ≠ 2#64 := by
        intro h0; have := congrArg BitVec.toNat h0; simp at this; omega
      have h3w : BitVec.ofNat 64 ((Enc.limbs i).length + 2) ≠ 3#64 := by
        intro h0; have := congrArg BitVec.toNat h0; simp at this; omega
      refine specR_ifI _ 0 (by simp [sev, hlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact h2w)
        (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_ifI _ 0 (by simp [sev, hlen, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact h3w)
        (fun h => absurd rfl h) (fun _ => specR_hangI)

end

end ConPanqueque.T.WC
