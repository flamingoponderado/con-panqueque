import ConPanqueque.T.Core.IotaIndex
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `iotaCertsFull`: the constructor type's telescope against the major's arguments

`iotaCertsFullAux`: at a `∀`, the domain instantiated at the pending substitutions (`instantiateListFast` =
`instantiateRevRange` over the accumulator block), the argument's inferred type compared with it (`defeq`), the
argument appended to the accumulator, then the body at the next argument; at a `bvar` with a nonempty
accumulator, the flushed term with a fresh empty accumulator. The accumulator is a heap block, grown by
`appendWord`. The proof is a strong induction on `2·(remaining arguments) + [accumulator nonempty]`.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def icH := ofString "ich"
def icA := ofString "ica"
def icN := ofString "icn"
def icAc := ofString "icac"
def icI := ofString "ici"
def icT := ofString "ict"
def icB := ofString "icb"
def icX := ofString "icx"
def icL := ofString "icl"
def icT2 := ofString "ict2"
def icTa := ofString "icta"
def icD := ofString "icd"
def icAc2 := ofString "icac2"
def icR := ofString "icr"
def icE := ofString "ice"
def fIc := ofString "iotaCertsFullAux"

@[simp] theorem ic_icH_ne_icA : icH ≠ icA := by decide
@[simp] theorem ic_icH_ne_icN : icH ≠ icN := by decide
@[simp] theorem ic_icH_ne_icAc : icH ≠ icAc := by decide
@[simp] theorem ic_icH_ne_icI : icH ≠ icI := by decide
@[simp] theorem ic_icH_ne_icT : icH ≠ icT := by decide
@[simp] theorem ic_icH_ne_icB : icH ≠ icB := by decide
@[simp] theorem ic_icH_ne_icX : icH ≠ icX := by decide
@[simp] theorem ic_icH_ne_icL : icH ≠ icL := by decide
@[simp] theorem ic_icH_ne_icT2 : icH ≠ icT2 := by decide
@[simp] theorem ic_icH_ne_icTa : icH ≠ icTa := by decide
@[simp] theorem ic_icH_ne_icD : icH ≠ icD := by decide
@[simp] theorem ic_icH_ne_icAc2 : icH ≠ icAc2 := by decide
@[simp] theorem ic_icH_ne_icR : icH ≠ icR := by decide
@[simp] theorem ic_icH_ne_icE : icH ≠ icE := by decide
@[simp] theorem ic_icH_ne_kFu : icH ≠ kFu := by decide
@[simp] theorem ic_icH_ne_kD : icH ≠ kD := by decide
@[simp] theorem ic_icH_ne_lFl : icH ≠ lFl := by decide
@[simp] theorem ic_icH_ne_lDh : icH ≠ lDh := by decide
@[simp] theorem ic_icH_ne_lDt : icH ≠ lDt := by decide
@[simp] theorem ic_icH_ne_lDg : icH ≠ lDg := by decide
@[simp] theorem ic_icH_ne_lDi : icH ≠ lDi := by decide
@[simp] theorem ic_icH_ne_lRp : icH ≠ lRp := by decide
@[simp] theorem ic_icH_ne_lRn : icH ≠ lRn := by decide
@[simp] theorem ic_icH_ne_lKb : icH ≠ lKb := by decide
@[simp] theorem ic_icH_ne_lFle : icH ≠ lFle := by decide
@[simp] theorem ic_icH_ne_lDir : icH ≠ lDir := by decide
@[simp] theorem ic_icA_ne_icH : icA ≠ icH := by decide
@[simp] theorem ic_icA_ne_icN : icA ≠ icN := by decide
@[simp] theorem ic_icA_ne_icAc : icA ≠ icAc := by decide
@[simp] theorem ic_icA_ne_icI : icA ≠ icI := by decide
@[simp] theorem ic_icA_ne_icT : icA ≠ icT := by decide
@[simp] theorem ic_icA_ne_icB : icA ≠ icB := by decide
@[simp] theorem ic_icA_ne_icX : icA ≠ icX := by decide
@[simp] theorem ic_icA_ne_icL : icA ≠ icL := by decide
@[simp] theorem ic_icA_ne_icT2 : icA ≠ icT2 := by decide
@[simp] theorem ic_icA_ne_icTa : icA ≠ icTa := by decide
@[simp] theorem ic_icA_ne_icD : icA ≠ icD := by decide
@[simp] theorem ic_icA_ne_icAc2 : icA ≠ icAc2 := by decide
@[simp] theorem ic_icA_ne_icR : icA ≠ icR := by decide
@[simp] theorem ic_icA_ne_icE : icA ≠ icE := by decide
@[simp] theorem ic_icA_ne_kFu : icA ≠ kFu := by decide
@[simp] theorem ic_icA_ne_kD : icA ≠ kD := by decide
@[simp] theorem ic_icA_ne_lFl : icA ≠ lFl := by decide
@[simp] theorem ic_icA_ne_lDh : icA ≠ lDh := by decide
@[simp] theorem ic_icA_ne_lDt : icA ≠ lDt := by decide
@[simp] theorem ic_icA_ne_lDg : icA ≠ lDg := by decide
@[simp] theorem ic_icA_ne_lDi : icA ≠ lDi := by decide
@[simp] theorem ic_icA_ne_lRp : icA ≠ lRp := by decide
@[simp] theorem ic_icA_ne_lRn : icA ≠ lRn := by decide
@[simp] theorem ic_icA_ne_lKb : icA ≠ lKb := by decide
@[simp] theorem ic_icA_ne_lFle : icA ≠ lFle := by decide
@[simp] theorem ic_icA_ne_lDir : icA ≠ lDir := by decide
@[simp] theorem ic_icN_ne_icH : icN ≠ icH := by decide
@[simp] theorem ic_icN_ne_icA : icN ≠ icA := by decide
@[simp] theorem ic_icN_ne_icAc : icN ≠ icAc := by decide
@[simp] theorem ic_icN_ne_icI : icN ≠ icI := by decide
@[simp] theorem ic_icN_ne_icT : icN ≠ icT := by decide
@[simp] theorem ic_icN_ne_icB : icN ≠ icB := by decide
@[simp] theorem ic_icN_ne_icX : icN ≠ icX := by decide
@[simp] theorem ic_icN_ne_icL : icN ≠ icL := by decide
@[simp] theorem ic_icN_ne_icT2 : icN ≠ icT2 := by decide
@[simp] theorem ic_icN_ne_icTa : icN ≠ icTa := by decide
@[simp] theorem ic_icN_ne_icD : icN ≠ icD := by decide
@[simp] theorem ic_icN_ne_icAc2 : icN ≠ icAc2 := by decide
@[simp] theorem ic_icN_ne_icR : icN ≠ icR := by decide
@[simp] theorem ic_icN_ne_icE : icN ≠ icE := by decide
@[simp] theorem ic_icN_ne_kFu : icN ≠ kFu := by decide
@[simp] theorem ic_icN_ne_kD : icN ≠ kD := by decide
@[simp] theorem ic_icN_ne_lFl : icN ≠ lFl := by decide
@[simp] theorem ic_icN_ne_lDh : icN ≠ lDh := by decide
@[simp] theorem ic_icN_ne_lDt : icN ≠ lDt := by decide
@[simp] theorem ic_icN_ne_lDg : icN ≠ lDg := by decide
@[simp] theorem ic_icN_ne_lDi : icN ≠ lDi := by decide
@[simp] theorem ic_icN_ne_lRp : icN ≠ lRp := by decide
@[simp] theorem ic_icN_ne_lRn : icN ≠ lRn := by decide
@[simp] theorem ic_icN_ne_lKb : icN ≠ lKb := by decide
@[simp] theorem ic_icN_ne_lFle : icN ≠ lFle := by decide
@[simp] theorem ic_icN_ne_lDir : icN ≠ lDir := by decide
@[simp] theorem ic_icAc_ne_icH : icAc ≠ icH := by decide
@[simp] theorem ic_icAc_ne_icA : icAc ≠ icA := by decide
@[simp] theorem ic_icAc_ne_icN : icAc ≠ icN := by decide
@[simp] theorem ic_icAc_ne_icI : icAc ≠ icI := by decide
@[simp] theorem ic_icAc_ne_icT : icAc ≠ icT := by decide
@[simp] theorem ic_icAc_ne_icB : icAc ≠ icB := by decide
@[simp] theorem ic_icAc_ne_icX : icAc ≠ icX := by decide
@[simp] theorem ic_icAc_ne_icL : icAc ≠ icL := by decide
@[simp] theorem ic_icAc_ne_icT2 : icAc ≠ icT2 := by decide
@[simp] theorem ic_icAc_ne_icTa : icAc ≠ icTa := by decide
@[simp] theorem ic_icAc_ne_icD : icAc ≠ icD := by decide
@[simp] theorem ic_icAc_ne_icAc2 : icAc ≠ icAc2 := by decide
@[simp] theorem ic_icAc_ne_icR : icAc ≠ icR := by decide
@[simp] theorem ic_icAc_ne_icE : icAc ≠ icE := by decide
@[simp] theorem ic_icAc_ne_kFu : icAc ≠ kFu := by decide
@[simp] theorem ic_icAc_ne_kD : icAc ≠ kD := by decide
@[simp] theorem ic_icAc_ne_lFl : icAc ≠ lFl := by decide
@[simp] theorem ic_icAc_ne_lDh : icAc ≠ lDh := by decide
@[simp] theorem ic_icAc_ne_lDt : icAc ≠ lDt := by decide
@[simp] theorem ic_icAc_ne_lDg : icAc ≠ lDg := by decide
@[simp] theorem ic_icAc_ne_lDi : icAc ≠ lDi := by decide
@[simp] theorem ic_icAc_ne_lRp : icAc ≠ lRp := by decide
@[simp] theorem ic_icAc_ne_lRn : icAc ≠ lRn := by decide
@[simp] theorem ic_icAc_ne_lKb : icAc ≠ lKb := by decide
@[simp] theorem ic_icAc_ne_lFle : icAc ≠ lFle := by decide
@[simp] theorem ic_icAc_ne_lDir : icAc ≠ lDir := by decide
@[simp] theorem ic_icI_ne_icH : icI ≠ icH := by decide
@[simp] theorem ic_icI_ne_icA : icI ≠ icA := by decide
@[simp] theorem ic_icI_ne_icN : icI ≠ icN := by decide
@[simp] theorem ic_icI_ne_icAc : icI ≠ icAc := by decide
@[simp] theorem ic_icI_ne_icT : icI ≠ icT := by decide
@[simp] theorem ic_icI_ne_icB : icI ≠ icB := by decide
@[simp] theorem ic_icI_ne_icX : icI ≠ icX := by decide
@[simp] theorem ic_icI_ne_icL : icI ≠ icL := by decide
@[simp] theorem ic_icI_ne_icT2 : icI ≠ icT2 := by decide
@[simp] theorem ic_icI_ne_icTa : icI ≠ icTa := by decide
@[simp] theorem ic_icI_ne_icD : icI ≠ icD := by decide
@[simp] theorem ic_icI_ne_icAc2 : icI ≠ icAc2 := by decide
@[simp] theorem ic_icI_ne_icR : icI ≠ icR := by decide
@[simp] theorem ic_icI_ne_icE : icI ≠ icE := by decide
@[simp] theorem ic_icI_ne_kFu : icI ≠ kFu := by decide
@[simp] theorem ic_icI_ne_kD : icI ≠ kD := by decide
@[simp] theorem ic_icI_ne_lFl : icI ≠ lFl := by decide
@[simp] theorem ic_icI_ne_lDh : icI ≠ lDh := by decide
@[simp] theorem ic_icI_ne_lDt : icI ≠ lDt := by decide
@[simp] theorem ic_icI_ne_lDg : icI ≠ lDg := by decide
@[simp] theorem ic_icI_ne_lDi : icI ≠ lDi := by decide
@[simp] theorem ic_icI_ne_lRp : icI ≠ lRp := by decide
@[simp] theorem ic_icI_ne_lRn : icI ≠ lRn := by decide
@[simp] theorem ic_icI_ne_lKb : icI ≠ lKb := by decide
@[simp] theorem ic_icI_ne_lFle : icI ≠ lFle := by decide
@[simp] theorem ic_icI_ne_lDir : icI ≠ lDir := by decide
@[simp] theorem ic_icT_ne_icH : icT ≠ icH := by decide
@[simp] theorem ic_icT_ne_icA : icT ≠ icA := by decide
@[simp] theorem ic_icT_ne_icN : icT ≠ icN := by decide
@[simp] theorem ic_icT_ne_icAc : icT ≠ icAc := by decide
@[simp] theorem ic_icT_ne_icI : icT ≠ icI := by decide
@[simp] theorem ic_icT_ne_icB : icT ≠ icB := by decide
@[simp] theorem ic_icT_ne_icX : icT ≠ icX := by decide
@[simp] theorem ic_icT_ne_icL : icT ≠ icL := by decide
@[simp] theorem ic_icT_ne_icT2 : icT ≠ icT2 := by decide
@[simp] theorem ic_icT_ne_icTa : icT ≠ icTa := by decide
@[simp] theorem ic_icT_ne_icD : icT ≠ icD := by decide
@[simp] theorem ic_icT_ne_icAc2 : icT ≠ icAc2 := by decide
@[simp] theorem ic_icT_ne_icR : icT ≠ icR := by decide
@[simp] theorem ic_icT_ne_icE : icT ≠ icE := by decide
@[simp] theorem ic_icT_ne_kFu : icT ≠ kFu := by decide
@[simp] theorem ic_icT_ne_kD : icT ≠ kD := by decide
@[simp] theorem ic_icT_ne_lFl : icT ≠ lFl := by decide
@[simp] theorem ic_icT_ne_lDh : icT ≠ lDh := by decide
@[simp] theorem ic_icT_ne_lDt : icT ≠ lDt := by decide
@[simp] theorem ic_icT_ne_lDg : icT ≠ lDg := by decide
@[simp] theorem ic_icT_ne_lDi : icT ≠ lDi := by decide
@[simp] theorem ic_icT_ne_lRp : icT ≠ lRp := by decide
@[simp] theorem ic_icT_ne_lRn : icT ≠ lRn := by decide
@[simp] theorem ic_icT_ne_lKb : icT ≠ lKb := by decide
@[simp] theorem ic_icT_ne_lFle : icT ≠ lFle := by decide
@[simp] theorem ic_icT_ne_lDir : icT ≠ lDir := by decide
@[simp] theorem ic_icB_ne_icH : icB ≠ icH := by decide
@[simp] theorem ic_icB_ne_icA : icB ≠ icA := by decide
@[simp] theorem ic_icB_ne_icN : icB ≠ icN := by decide
@[simp] theorem ic_icB_ne_icAc : icB ≠ icAc := by decide
@[simp] theorem ic_icB_ne_icI : icB ≠ icI := by decide
@[simp] theorem ic_icB_ne_icT : icB ≠ icT := by decide
@[simp] theorem ic_icB_ne_icX : icB ≠ icX := by decide
@[simp] theorem ic_icB_ne_icL : icB ≠ icL := by decide
@[simp] theorem ic_icB_ne_icT2 : icB ≠ icT2 := by decide
@[simp] theorem ic_icB_ne_icTa : icB ≠ icTa := by decide
@[simp] theorem ic_icB_ne_icD : icB ≠ icD := by decide
@[simp] theorem ic_icB_ne_icAc2 : icB ≠ icAc2 := by decide
@[simp] theorem ic_icB_ne_icR : icB ≠ icR := by decide
@[simp] theorem ic_icB_ne_icE : icB ≠ icE := by decide
@[simp] theorem ic_icB_ne_kFu : icB ≠ kFu := by decide
@[simp] theorem ic_icB_ne_kD : icB ≠ kD := by decide
@[simp] theorem ic_icB_ne_lFl : icB ≠ lFl := by decide
@[simp] theorem ic_icB_ne_lDh : icB ≠ lDh := by decide
@[simp] theorem ic_icB_ne_lDt : icB ≠ lDt := by decide
@[simp] theorem ic_icB_ne_lDg : icB ≠ lDg := by decide
@[simp] theorem ic_icB_ne_lDi : icB ≠ lDi := by decide
@[simp] theorem ic_icB_ne_lRp : icB ≠ lRp := by decide
@[simp] theorem ic_icB_ne_lRn : icB ≠ lRn := by decide
@[simp] theorem ic_icB_ne_lKb : icB ≠ lKb := by decide
@[simp] theorem ic_icB_ne_lFle : icB ≠ lFle := by decide
@[simp] theorem ic_icB_ne_lDir : icB ≠ lDir := by decide
@[simp] theorem ic_icX_ne_icH : icX ≠ icH := by decide
@[simp] theorem ic_icX_ne_icA : icX ≠ icA := by decide
@[simp] theorem ic_icX_ne_icN : icX ≠ icN := by decide
@[simp] theorem ic_icX_ne_icAc : icX ≠ icAc := by decide
@[simp] theorem ic_icX_ne_icI : icX ≠ icI := by decide
@[simp] theorem ic_icX_ne_icT : icX ≠ icT := by decide
@[simp] theorem ic_icX_ne_icB : icX ≠ icB := by decide
@[simp] theorem ic_icX_ne_icL : icX ≠ icL := by decide
@[simp] theorem ic_icX_ne_icT2 : icX ≠ icT2 := by decide
@[simp] theorem ic_icX_ne_icTa : icX ≠ icTa := by decide
@[simp] theorem ic_icX_ne_icD : icX ≠ icD := by decide
@[simp] theorem ic_icX_ne_icAc2 : icX ≠ icAc2 := by decide
@[simp] theorem ic_icX_ne_icR : icX ≠ icR := by decide
@[simp] theorem ic_icX_ne_icE : icX ≠ icE := by decide
@[simp] theorem ic_icX_ne_kFu : icX ≠ kFu := by decide
@[simp] theorem ic_icX_ne_kD : icX ≠ kD := by decide
@[simp] theorem ic_icX_ne_lFl : icX ≠ lFl := by decide
@[simp] theorem ic_icX_ne_lDh : icX ≠ lDh := by decide
@[simp] theorem ic_icX_ne_lDt : icX ≠ lDt := by decide
@[simp] theorem ic_icX_ne_lDg : icX ≠ lDg := by decide
@[simp] theorem ic_icX_ne_lDi : icX ≠ lDi := by decide
@[simp] theorem ic_icX_ne_lRp : icX ≠ lRp := by decide
@[simp] theorem ic_icX_ne_lRn : icX ≠ lRn := by decide
@[simp] theorem ic_icX_ne_lKb : icX ≠ lKb := by decide
@[simp] theorem ic_icX_ne_lFle : icX ≠ lFle := by decide
@[simp] theorem ic_icX_ne_lDir : icX ≠ lDir := by decide
@[simp] theorem ic_icL_ne_icH : icL ≠ icH := by decide
@[simp] theorem ic_icL_ne_icA : icL ≠ icA := by decide
@[simp] theorem ic_icL_ne_icN : icL ≠ icN := by decide
@[simp] theorem ic_icL_ne_icAc : icL ≠ icAc := by decide
@[simp] theorem ic_icL_ne_icI : icL ≠ icI := by decide
@[simp] theorem ic_icL_ne_icT : icL ≠ icT := by decide
@[simp] theorem ic_icL_ne_icB : icL ≠ icB := by decide
@[simp] theorem ic_icL_ne_icX : icL ≠ icX := by decide
@[simp] theorem ic_icL_ne_icT2 : icL ≠ icT2 := by decide
@[simp] theorem ic_icL_ne_icTa : icL ≠ icTa := by decide
@[simp] theorem ic_icL_ne_icD : icL ≠ icD := by decide
@[simp] theorem ic_icL_ne_icAc2 : icL ≠ icAc2 := by decide
@[simp] theorem ic_icL_ne_icR : icL ≠ icR := by decide
@[simp] theorem ic_icL_ne_icE : icL ≠ icE := by decide
@[simp] theorem ic_icL_ne_kFu : icL ≠ kFu := by decide
@[simp] theorem ic_icL_ne_kD : icL ≠ kD := by decide
@[simp] theorem ic_icL_ne_lFl : icL ≠ lFl := by decide
@[simp] theorem ic_icL_ne_lDh : icL ≠ lDh := by decide
@[simp] theorem ic_icL_ne_lDt : icL ≠ lDt := by decide
@[simp] theorem ic_icL_ne_lDg : icL ≠ lDg := by decide
@[simp] theorem ic_icL_ne_lDi : icL ≠ lDi := by decide
@[simp] theorem ic_icL_ne_lRp : icL ≠ lRp := by decide
@[simp] theorem ic_icL_ne_lRn : icL ≠ lRn := by decide
@[simp] theorem ic_icL_ne_lKb : icL ≠ lKb := by decide
@[simp] theorem ic_icL_ne_lFle : icL ≠ lFle := by decide
@[simp] theorem ic_icL_ne_lDir : icL ≠ lDir := by decide
@[simp] theorem ic_icT2_ne_icH : icT2 ≠ icH := by decide
@[simp] theorem ic_icT2_ne_icA : icT2 ≠ icA := by decide
@[simp] theorem ic_icT2_ne_icN : icT2 ≠ icN := by decide
@[simp] theorem ic_icT2_ne_icAc : icT2 ≠ icAc := by decide
@[simp] theorem ic_icT2_ne_icI : icT2 ≠ icI := by decide
@[simp] theorem ic_icT2_ne_icT : icT2 ≠ icT := by decide
@[simp] theorem ic_icT2_ne_icB : icT2 ≠ icB := by decide
@[simp] theorem ic_icT2_ne_icX : icT2 ≠ icX := by decide
@[simp] theorem ic_icT2_ne_icL : icT2 ≠ icL := by decide
@[simp] theorem ic_icT2_ne_icTa : icT2 ≠ icTa := by decide
@[simp] theorem ic_icT2_ne_icD : icT2 ≠ icD := by decide
@[simp] theorem ic_icT2_ne_icAc2 : icT2 ≠ icAc2 := by decide
@[simp] theorem ic_icT2_ne_icR : icT2 ≠ icR := by decide
@[simp] theorem ic_icT2_ne_icE : icT2 ≠ icE := by decide
@[simp] theorem ic_icT2_ne_kFu : icT2 ≠ kFu := by decide
@[simp] theorem ic_icT2_ne_kD : icT2 ≠ kD := by decide
@[simp] theorem ic_icT2_ne_lFl : icT2 ≠ lFl := by decide
@[simp] theorem ic_icT2_ne_lDh : icT2 ≠ lDh := by decide
@[simp] theorem ic_icT2_ne_lDt : icT2 ≠ lDt := by decide
@[simp] theorem ic_icT2_ne_lDg : icT2 ≠ lDg := by decide
@[simp] theorem ic_icT2_ne_lDi : icT2 ≠ lDi := by decide
@[simp] theorem ic_icT2_ne_lRp : icT2 ≠ lRp := by decide
@[simp] theorem ic_icT2_ne_lRn : icT2 ≠ lRn := by decide
@[simp] theorem ic_icT2_ne_lKb : icT2 ≠ lKb := by decide
@[simp] theorem ic_icT2_ne_lFle : icT2 ≠ lFle := by decide
@[simp] theorem ic_icT2_ne_lDir : icT2 ≠ lDir := by decide
@[simp] theorem ic_icTa_ne_icH : icTa ≠ icH := by decide
@[simp] theorem ic_icTa_ne_icA : icTa ≠ icA := by decide
@[simp] theorem ic_icTa_ne_icN : icTa ≠ icN := by decide
@[simp] theorem ic_icTa_ne_icAc : icTa ≠ icAc := by decide
@[simp] theorem ic_icTa_ne_icI : icTa ≠ icI := by decide
@[simp] theorem ic_icTa_ne_icT : icTa ≠ icT := by decide
@[simp] theorem ic_icTa_ne_icB : icTa ≠ icB := by decide
@[simp] theorem ic_icTa_ne_icX : icTa ≠ icX := by decide
@[simp] theorem ic_icTa_ne_icL : icTa ≠ icL := by decide
@[simp] theorem ic_icTa_ne_icT2 : icTa ≠ icT2 := by decide
@[simp] theorem ic_icTa_ne_icD : icTa ≠ icD := by decide
@[simp] theorem ic_icTa_ne_icAc2 : icTa ≠ icAc2 := by decide
@[simp] theorem ic_icTa_ne_icR : icTa ≠ icR := by decide
@[simp] theorem ic_icTa_ne_icE : icTa ≠ icE := by decide
@[simp] theorem ic_icTa_ne_kFu : icTa ≠ kFu := by decide
@[simp] theorem ic_icTa_ne_kD : icTa ≠ kD := by decide
@[simp] theorem ic_icTa_ne_lFl : icTa ≠ lFl := by decide
@[simp] theorem ic_icTa_ne_lDh : icTa ≠ lDh := by decide
@[simp] theorem ic_icTa_ne_lDt : icTa ≠ lDt := by decide
@[simp] theorem ic_icTa_ne_lDg : icTa ≠ lDg := by decide
@[simp] theorem ic_icTa_ne_lDi : icTa ≠ lDi := by decide
@[simp] theorem ic_icTa_ne_lRp : icTa ≠ lRp := by decide
@[simp] theorem ic_icTa_ne_lRn : icTa ≠ lRn := by decide
@[simp] theorem ic_icTa_ne_lKb : icTa ≠ lKb := by decide
@[simp] theorem ic_icTa_ne_lFle : icTa ≠ lFle := by decide
@[simp] theorem ic_icTa_ne_lDir : icTa ≠ lDir := by decide
@[simp] theorem ic_icD_ne_icH : icD ≠ icH := by decide
@[simp] theorem ic_icD_ne_icA : icD ≠ icA := by decide
@[simp] theorem ic_icD_ne_icN : icD ≠ icN := by decide
@[simp] theorem ic_icD_ne_icAc : icD ≠ icAc := by decide
@[simp] theorem ic_icD_ne_icI : icD ≠ icI := by decide
@[simp] theorem ic_icD_ne_icT : icD ≠ icT := by decide
@[simp] theorem ic_icD_ne_icB : icD ≠ icB := by decide
@[simp] theorem ic_icD_ne_icX : icD ≠ icX := by decide
@[simp] theorem ic_icD_ne_icL : icD ≠ icL := by decide
@[simp] theorem ic_icD_ne_icT2 : icD ≠ icT2 := by decide
@[simp] theorem ic_icD_ne_icTa : icD ≠ icTa := by decide
@[simp] theorem ic_icD_ne_icAc2 : icD ≠ icAc2 := by decide
@[simp] theorem ic_icD_ne_icR : icD ≠ icR := by decide
@[simp] theorem ic_icD_ne_icE : icD ≠ icE := by decide
@[simp] theorem ic_icD_ne_kFu : icD ≠ kFu := by decide
@[simp] theorem ic_icD_ne_kD : icD ≠ kD := by decide
@[simp] theorem ic_icD_ne_lFl : icD ≠ lFl := by decide
@[simp] theorem ic_icD_ne_lDh : icD ≠ lDh := by decide
@[simp] theorem ic_icD_ne_lDt : icD ≠ lDt := by decide
@[simp] theorem ic_icD_ne_lDg : icD ≠ lDg := by decide
@[simp] theorem ic_icD_ne_lDi : icD ≠ lDi := by decide
@[simp] theorem ic_icD_ne_lRp : icD ≠ lRp := by decide
@[simp] theorem ic_icD_ne_lRn : icD ≠ lRn := by decide
@[simp] theorem ic_icD_ne_lKb : icD ≠ lKb := by decide
@[simp] theorem ic_icD_ne_lFle : icD ≠ lFle := by decide
@[simp] theorem ic_icD_ne_lDir : icD ≠ lDir := by decide
@[simp] theorem ic_icAc2_ne_icH : icAc2 ≠ icH := by decide
@[simp] theorem ic_icAc2_ne_icA : icAc2 ≠ icA := by decide
@[simp] theorem ic_icAc2_ne_icN : icAc2 ≠ icN := by decide
@[simp] theorem ic_icAc2_ne_icAc : icAc2 ≠ icAc := by decide
@[simp] theorem ic_icAc2_ne_icI : icAc2 ≠ icI := by decide
@[simp] theorem ic_icAc2_ne_icT : icAc2 ≠ icT := by decide
@[simp] theorem ic_icAc2_ne_icB : icAc2 ≠ icB := by decide
@[simp] theorem ic_icAc2_ne_icX : icAc2 ≠ icX := by decide
@[simp] theorem ic_icAc2_ne_icL : icAc2 ≠ icL := by decide
@[simp] theorem ic_icAc2_ne_icT2 : icAc2 ≠ icT2 := by decide
@[simp] theorem ic_icAc2_ne_icTa : icAc2 ≠ icTa := by decide
@[simp] theorem ic_icAc2_ne_icD : icAc2 ≠ icD := by decide
@[simp] theorem ic_icAc2_ne_icR : icAc2 ≠ icR := by decide
@[simp] theorem ic_icAc2_ne_icE : icAc2 ≠ icE := by decide
@[simp] theorem ic_icAc2_ne_kFu : icAc2 ≠ kFu := by decide
@[simp] theorem ic_icAc2_ne_kD : icAc2 ≠ kD := by decide
@[simp] theorem ic_icAc2_ne_lFl : icAc2 ≠ lFl := by decide
@[simp] theorem ic_icAc2_ne_lDh : icAc2 ≠ lDh := by decide
@[simp] theorem ic_icAc2_ne_lDt : icAc2 ≠ lDt := by decide
@[simp] theorem ic_icAc2_ne_lDg : icAc2 ≠ lDg := by decide
@[simp] theorem ic_icAc2_ne_lDi : icAc2 ≠ lDi := by decide
@[simp] theorem ic_icAc2_ne_lRp : icAc2 ≠ lRp := by decide
@[simp] theorem ic_icAc2_ne_lRn : icAc2 ≠ lRn := by decide
@[simp] theorem ic_icAc2_ne_lKb : icAc2 ≠ lKb := by decide
@[simp] theorem ic_icAc2_ne_lFle : icAc2 ≠ lFle := by decide
@[simp] theorem ic_icAc2_ne_lDir : icAc2 ≠ lDir := by decide
@[simp] theorem ic_icR_ne_icH : icR ≠ icH := by decide
@[simp] theorem ic_icR_ne_icA : icR ≠ icA := by decide
@[simp] theorem ic_icR_ne_icN : icR ≠ icN := by decide
@[simp] theorem ic_icR_ne_icAc : icR ≠ icAc := by decide
@[simp] theorem ic_icR_ne_icI : icR ≠ icI := by decide
@[simp] theorem ic_icR_ne_icT : icR ≠ icT := by decide
@[simp] theorem ic_icR_ne_icB : icR ≠ icB := by decide
@[simp] theorem ic_icR_ne_icX : icR ≠ icX := by decide
@[simp] theorem ic_icR_ne_icL : icR ≠ icL := by decide
@[simp] theorem ic_icR_ne_icT2 : icR ≠ icT2 := by decide
@[simp] theorem ic_icR_ne_icTa : icR ≠ icTa := by decide
@[simp] theorem ic_icR_ne_icD : icR ≠ icD := by decide
@[simp] theorem ic_icR_ne_icAc2 : icR ≠ icAc2 := by decide
@[simp] theorem ic_icR_ne_icE : icR ≠ icE := by decide
@[simp] theorem ic_icR_ne_kFu : icR ≠ kFu := by decide
@[simp] theorem ic_icR_ne_kD : icR ≠ kD := by decide
@[simp] theorem ic_icR_ne_lFl : icR ≠ lFl := by decide
@[simp] theorem ic_icR_ne_lDh : icR ≠ lDh := by decide
@[simp] theorem ic_icR_ne_lDt : icR ≠ lDt := by decide
@[simp] theorem ic_icR_ne_lDg : icR ≠ lDg := by decide
@[simp] theorem ic_icR_ne_lDi : icR ≠ lDi := by decide
@[simp] theorem ic_icR_ne_lRp : icR ≠ lRp := by decide
@[simp] theorem ic_icR_ne_lRn : icR ≠ lRn := by decide
@[simp] theorem ic_icR_ne_lKb : icR ≠ lKb := by decide
@[simp] theorem ic_icR_ne_lFle : icR ≠ lFle := by decide
@[simp] theorem ic_icR_ne_lDir : icR ≠ lDir := by decide
@[simp] theorem ic_icE_ne_icH : icE ≠ icH := by decide
@[simp] theorem ic_icE_ne_icA : icE ≠ icA := by decide
@[simp] theorem ic_icE_ne_icN : icE ≠ icN := by decide
@[simp] theorem ic_icE_ne_icAc : icE ≠ icAc := by decide
@[simp] theorem ic_icE_ne_icI : icE ≠ icI := by decide
@[simp] theorem ic_icE_ne_icT : icE ≠ icT := by decide
@[simp] theorem ic_icE_ne_icB : icE ≠ icB := by decide
@[simp] theorem ic_icE_ne_icX : icE ≠ icX := by decide
@[simp] theorem ic_icE_ne_icL : icE ≠ icL := by decide
@[simp] theorem ic_icE_ne_icT2 : icE ≠ icT2 := by decide
@[simp] theorem ic_icE_ne_icTa : icE ≠ icTa := by decide
@[simp] theorem ic_icE_ne_icD : icE ≠ icD := by decide
@[simp] theorem ic_icE_ne_icAc2 : icE ≠ icAc2 := by decide
@[simp] theorem ic_icE_ne_icR : icE ≠ icR := by decide
@[simp] theorem ic_icE_ne_kFu : icE ≠ kFu := by decide
@[simp] theorem ic_icE_ne_kD : icE ≠ kD := by decide
@[simp] theorem ic_icE_ne_lFl : icE ≠ lFl := by decide
@[simp] theorem ic_icE_ne_lDh : icE ≠ lDh := by decide
@[simp] theorem ic_icE_ne_lDt : icE ≠ lDt := by decide
@[simp] theorem ic_icE_ne_lDg : icE ≠ lDg := by decide
@[simp] theorem ic_icE_ne_lDi : icE ≠ lDi := by decide
@[simp] theorem ic_icE_ne_lRp : icE ≠ lRp := by decide
@[simp] theorem ic_icE_ne_lRn : icE ≠ lRn := by decide
@[simp] theorem ic_icE_ne_lKb : icE ≠ lKb := by decide
@[simp] theorem ic_icE_ne_lFle : icE ≠ lFle := by decide
@[simp] theorem ic_icE_ne_lDir : icE ≠ lDir := by decide
@[simp] theorem ic_kFu_ne_icH : kFu ≠ icH := by decide
@[simp] theorem ic_kFu_ne_icA : kFu ≠ icA := by decide
@[simp] theorem ic_kFu_ne_icN : kFu ≠ icN := by decide
@[simp] theorem ic_kFu_ne_icAc : kFu ≠ icAc := by decide
@[simp] theorem ic_kFu_ne_icI : kFu ≠ icI := by decide
@[simp] theorem ic_kFu_ne_icT : kFu ≠ icT := by decide
@[simp] theorem ic_kFu_ne_icB : kFu ≠ icB := by decide
@[simp] theorem ic_kFu_ne_icX : kFu ≠ icX := by decide
@[simp] theorem ic_kFu_ne_icL : kFu ≠ icL := by decide
@[simp] theorem ic_kFu_ne_icT2 : kFu ≠ icT2 := by decide
@[simp] theorem ic_kFu_ne_icTa : kFu ≠ icTa := by decide
@[simp] theorem ic_kFu_ne_icD : kFu ≠ icD := by decide
@[simp] theorem ic_kFu_ne_icAc2 : kFu ≠ icAc2 := by decide
@[simp] theorem ic_kFu_ne_icR : kFu ≠ icR := by decide
@[simp] theorem ic_kFu_ne_icE : kFu ≠ icE := by decide
@[simp] theorem ic_kD_ne_icH : kD ≠ icH := by decide
@[simp] theorem ic_kD_ne_icA : kD ≠ icA := by decide
@[simp] theorem ic_kD_ne_icN : kD ≠ icN := by decide
@[simp] theorem ic_kD_ne_icAc : kD ≠ icAc := by decide
@[simp] theorem ic_kD_ne_icI : kD ≠ icI := by decide
@[simp] theorem ic_kD_ne_icT : kD ≠ icT := by decide
@[simp] theorem ic_kD_ne_icB : kD ≠ icB := by decide
@[simp] theorem ic_kD_ne_icX : kD ≠ icX := by decide
@[simp] theorem ic_kD_ne_icL : kD ≠ icL := by decide
@[simp] theorem ic_kD_ne_icT2 : kD ≠ icT2 := by decide
@[simp] theorem ic_kD_ne_icTa : kD ≠ icTa := by decide
@[simp] theorem ic_kD_ne_icD : kD ≠ icD := by decide
@[simp] theorem ic_kD_ne_icAc2 : kD ≠ icAc2 := by decide
@[simp] theorem ic_kD_ne_icR : kD ≠ icR := by decide
@[simp] theorem ic_kD_ne_icE : kD ≠ icE := by decide
@[simp] theorem ic_lFl_ne_icH : lFl ≠ icH := by decide
@[simp] theorem ic_lFl_ne_icA : lFl ≠ icA := by decide
@[simp] theorem ic_lFl_ne_icN : lFl ≠ icN := by decide
@[simp] theorem ic_lFl_ne_icAc : lFl ≠ icAc := by decide
@[simp] theorem ic_lFl_ne_icI : lFl ≠ icI := by decide
@[simp] theorem ic_lFl_ne_icT : lFl ≠ icT := by decide
@[simp] theorem ic_lFl_ne_icB : lFl ≠ icB := by decide
@[simp] theorem ic_lFl_ne_icX : lFl ≠ icX := by decide
@[simp] theorem ic_lFl_ne_icL : lFl ≠ icL := by decide
@[simp] theorem ic_lFl_ne_icT2 : lFl ≠ icT2 := by decide
@[simp] theorem ic_lFl_ne_icTa : lFl ≠ icTa := by decide
@[simp] theorem ic_lFl_ne_icD : lFl ≠ icD := by decide
@[simp] theorem ic_lFl_ne_icAc2 : lFl ≠ icAc2 := by decide
@[simp] theorem ic_lFl_ne_icR : lFl ≠ icR := by decide
@[simp] theorem ic_lFl_ne_icE : lFl ≠ icE := by decide
@[simp] theorem ic_lDh_ne_icH : lDh ≠ icH := by decide
@[simp] theorem ic_lDh_ne_icA : lDh ≠ icA := by decide
@[simp] theorem ic_lDh_ne_icN : lDh ≠ icN := by decide
@[simp] theorem ic_lDh_ne_icAc : lDh ≠ icAc := by decide
@[simp] theorem ic_lDh_ne_icI : lDh ≠ icI := by decide
@[simp] theorem ic_lDh_ne_icT : lDh ≠ icT := by decide
@[simp] theorem ic_lDh_ne_icB : lDh ≠ icB := by decide
@[simp] theorem ic_lDh_ne_icX : lDh ≠ icX := by decide
@[simp] theorem ic_lDh_ne_icL : lDh ≠ icL := by decide
@[simp] theorem ic_lDh_ne_icT2 : lDh ≠ icT2 := by decide
@[simp] theorem ic_lDh_ne_icTa : lDh ≠ icTa := by decide
@[simp] theorem ic_lDh_ne_icD : lDh ≠ icD := by decide
@[simp] theorem ic_lDh_ne_icAc2 : lDh ≠ icAc2 := by decide
@[simp] theorem ic_lDh_ne_icR : lDh ≠ icR := by decide
@[simp] theorem ic_lDh_ne_icE : lDh ≠ icE := by decide
@[simp] theorem ic_lDt_ne_icH : lDt ≠ icH := by decide
@[simp] theorem ic_lDt_ne_icA : lDt ≠ icA := by decide
@[simp] theorem ic_lDt_ne_icN : lDt ≠ icN := by decide
@[simp] theorem ic_lDt_ne_icAc : lDt ≠ icAc := by decide
@[simp] theorem ic_lDt_ne_icI : lDt ≠ icI := by decide
@[simp] theorem ic_lDt_ne_icT : lDt ≠ icT := by decide
@[simp] theorem ic_lDt_ne_icB : lDt ≠ icB := by decide
@[simp] theorem ic_lDt_ne_icX : lDt ≠ icX := by decide
@[simp] theorem ic_lDt_ne_icL : lDt ≠ icL := by decide
@[simp] theorem ic_lDt_ne_icT2 : lDt ≠ icT2 := by decide
@[simp] theorem ic_lDt_ne_icTa : lDt ≠ icTa := by decide
@[simp] theorem ic_lDt_ne_icD : lDt ≠ icD := by decide
@[simp] theorem ic_lDt_ne_icAc2 : lDt ≠ icAc2 := by decide
@[simp] theorem ic_lDt_ne_icR : lDt ≠ icR := by decide
@[simp] theorem ic_lDt_ne_icE : lDt ≠ icE := by decide
@[simp] theorem ic_lDg_ne_icH : lDg ≠ icH := by decide
@[simp] theorem ic_lDg_ne_icA : lDg ≠ icA := by decide
@[simp] theorem ic_lDg_ne_icN : lDg ≠ icN := by decide
@[simp] theorem ic_lDg_ne_icAc : lDg ≠ icAc := by decide
@[simp] theorem ic_lDg_ne_icI : lDg ≠ icI := by decide
@[simp] theorem ic_lDg_ne_icT : lDg ≠ icT := by decide
@[simp] theorem ic_lDg_ne_icB : lDg ≠ icB := by decide
@[simp] theorem ic_lDg_ne_icX : lDg ≠ icX := by decide
@[simp] theorem ic_lDg_ne_icL : lDg ≠ icL := by decide
@[simp] theorem ic_lDg_ne_icT2 : lDg ≠ icT2 := by decide
@[simp] theorem ic_lDg_ne_icTa : lDg ≠ icTa := by decide
@[simp] theorem ic_lDg_ne_icD : lDg ≠ icD := by decide
@[simp] theorem ic_lDg_ne_icAc2 : lDg ≠ icAc2 := by decide
@[simp] theorem ic_lDg_ne_icR : lDg ≠ icR := by decide
@[simp] theorem ic_lDg_ne_icE : lDg ≠ icE := by decide
@[simp] theorem ic_lDi_ne_icH : lDi ≠ icH := by decide
@[simp] theorem ic_lDi_ne_icA : lDi ≠ icA := by decide
@[simp] theorem ic_lDi_ne_icN : lDi ≠ icN := by decide
@[simp] theorem ic_lDi_ne_icAc : lDi ≠ icAc := by decide
@[simp] theorem ic_lDi_ne_icI : lDi ≠ icI := by decide
@[simp] theorem ic_lDi_ne_icT : lDi ≠ icT := by decide
@[simp] theorem ic_lDi_ne_icB : lDi ≠ icB := by decide
@[simp] theorem ic_lDi_ne_icX : lDi ≠ icX := by decide
@[simp] theorem ic_lDi_ne_icL : lDi ≠ icL := by decide
@[simp] theorem ic_lDi_ne_icT2 : lDi ≠ icT2 := by decide
@[simp] theorem ic_lDi_ne_icTa : lDi ≠ icTa := by decide
@[simp] theorem ic_lDi_ne_icD : lDi ≠ icD := by decide
@[simp] theorem ic_lDi_ne_icAc2 : lDi ≠ icAc2 := by decide
@[simp] theorem ic_lDi_ne_icR : lDi ≠ icR := by decide
@[simp] theorem ic_lDi_ne_icE : lDi ≠ icE := by decide
@[simp] theorem ic_lRp_ne_icH : lRp ≠ icH := by decide
@[simp] theorem ic_lRp_ne_icA : lRp ≠ icA := by decide
@[simp] theorem ic_lRp_ne_icN : lRp ≠ icN := by decide
@[simp] theorem ic_lRp_ne_icAc : lRp ≠ icAc := by decide
@[simp] theorem ic_lRp_ne_icI : lRp ≠ icI := by decide
@[simp] theorem ic_lRp_ne_icT : lRp ≠ icT := by decide
@[simp] theorem ic_lRp_ne_icB : lRp ≠ icB := by decide
@[simp] theorem ic_lRp_ne_icX : lRp ≠ icX := by decide
@[simp] theorem ic_lRp_ne_icL : lRp ≠ icL := by decide
@[simp] theorem ic_lRp_ne_icT2 : lRp ≠ icT2 := by decide
@[simp] theorem ic_lRp_ne_icTa : lRp ≠ icTa := by decide
@[simp] theorem ic_lRp_ne_icD : lRp ≠ icD := by decide
@[simp] theorem ic_lRp_ne_icAc2 : lRp ≠ icAc2 := by decide
@[simp] theorem ic_lRp_ne_icR : lRp ≠ icR := by decide
@[simp] theorem ic_lRp_ne_icE : lRp ≠ icE := by decide
@[simp] theorem ic_lRn_ne_icH : lRn ≠ icH := by decide
@[simp] theorem ic_lRn_ne_icA : lRn ≠ icA := by decide
@[simp] theorem ic_lRn_ne_icN : lRn ≠ icN := by decide
@[simp] theorem ic_lRn_ne_icAc : lRn ≠ icAc := by decide
@[simp] theorem ic_lRn_ne_icI : lRn ≠ icI := by decide
@[simp] theorem ic_lRn_ne_icT : lRn ≠ icT := by decide
@[simp] theorem ic_lRn_ne_icB : lRn ≠ icB := by decide
@[simp] theorem ic_lRn_ne_icX : lRn ≠ icX := by decide
@[simp] theorem ic_lRn_ne_icL : lRn ≠ icL := by decide
@[simp] theorem ic_lRn_ne_icT2 : lRn ≠ icT2 := by decide
@[simp] theorem ic_lRn_ne_icTa : lRn ≠ icTa := by decide
@[simp] theorem ic_lRn_ne_icD : lRn ≠ icD := by decide
@[simp] theorem ic_lRn_ne_icAc2 : lRn ≠ icAc2 := by decide
@[simp] theorem ic_lRn_ne_icR : lRn ≠ icR := by decide
@[simp] theorem ic_lRn_ne_icE : lRn ≠ icE := by decide
@[simp] theorem ic_lKb_ne_icH : lKb ≠ icH := by decide
@[simp] theorem ic_lKb_ne_icA : lKb ≠ icA := by decide
@[simp] theorem ic_lKb_ne_icN : lKb ≠ icN := by decide
@[simp] theorem ic_lKb_ne_icAc : lKb ≠ icAc := by decide
@[simp] theorem ic_lKb_ne_icI : lKb ≠ icI := by decide
@[simp] theorem ic_lKb_ne_icT : lKb ≠ icT := by decide
@[simp] theorem ic_lKb_ne_icB : lKb ≠ icB := by decide
@[simp] theorem ic_lKb_ne_icX : lKb ≠ icX := by decide
@[simp] theorem ic_lKb_ne_icL : lKb ≠ icL := by decide
@[simp] theorem ic_lKb_ne_icT2 : lKb ≠ icT2 := by decide
@[simp] theorem ic_lKb_ne_icTa : lKb ≠ icTa := by decide
@[simp] theorem ic_lKb_ne_icD : lKb ≠ icD := by decide
@[simp] theorem ic_lKb_ne_icAc2 : lKb ≠ icAc2 := by decide
@[simp] theorem ic_lKb_ne_icR : lKb ≠ icR := by decide
@[simp] theorem ic_lKb_ne_icE : lKb ≠ icE := by decide
@[simp] theorem ic_lFle_ne_icH : lFle ≠ icH := by decide
@[simp] theorem ic_lFle_ne_icA : lFle ≠ icA := by decide
@[simp] theorem ic_lFle_ne_icN : lFle ≠ icN := by decide
@[simp] theorem ic_lFle_ne_icAc : lFle ≠ icAc := by decide
@[simp] theorem ic_lFle_ne_icI : lFle ≠ icI := by decide
@[simp] theorem ic_lFle_ne_icT : lFle ≠ icT := by decide
@[simp] theorem ic_lFle_ne_icB : lFle ≠ icB := by decide
@[simp] theorem ic_lFle_ne_icX : lFle ≠ icX := by decide
@[simp] theorem ic_lFle_ne_icL : lFle ≠ icL := by decide
@[simp] theorem ic_lFle_ne_icT2 : lFle ≠ icT2 := by decide
@[simp] theorem ic_lFle_ne_icTa : lFle ≠ icTa := by decide
@[simp] theorem ic_lFle_ne_icD : lFle ≠ icD := by decide
@[simp] theorem ic_lFle_ne_icAc2 : lFle ≠ icAc2 := by decide
@[simp] theorem ic_lFle_ne_icR : lFle ≠ icR := by decide
@[simp] theorem ic_lFle_ne_icE : lFle ≠ icE := by decide
@[simp] theorem ic_lDir_ne_icH : lDir ≠ icH := by decide
@[simp] theorem ic_lDir_ne_icA : lDir ≠ icA := by decide
@[simp] theorem ic_lDir_ne_icN : lDir ≠ icN := by decide
@[simp] theorem ic_lDir_ne_icAc : lDir ≠ icAc := by decide
@[simp] theorem ic_lDir_ne_icI : lDir ≠ icI := by decide
@[simp] theorem ic_lDir_ne_icT : lDir ≠ icT := by decide
@[simp] theorem ic_lDir_ne_icB : lDir ≠ icB := by decide
@[simp] theorem ic_lDir_ne_icX : lDir ≠ icX := by decide
@[simp] theorem ic_lDir_ne_icL : lDir ≠ icL := by decide
@[simp] theorem ic_lDir_ne_icT2 : lDir ≠ icT2 := by decide
@[simp] theorem ic_lDir_ne_icTa : lDir ≠ icTa := by decide
@[simp] theorem ic_lDir_ne_icD : lDir ≠ icD := by decide
@[simp] theorem ic_lDir_ne_icAc2 : lDir ≠ icAc2 := by decide
@[simp] theorem ic_lDir_ne_icR : lDir ≠ icR := by decide
@[simp] theorem ic_lDir_ne_icE : lDir ≠ icE := by decide

def icParams : List MlS := [kFu, kD, icH, icA, icN, icAc, icI]
def icLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, icT, icB, icX, icL, icT2, icTa, icD, icAc2, icR, icE]

def icCore (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .lower (vv icI) (vv icN))
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv icH)) (.seq eViewP
  (.ite (tagIsE icH 6)
    (.seq (.assign .local icT (.load .one (vv lRp)))
    (.seq (.assign .local icB (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.assign .local icX (.load .one (.op .add [vv icA, .shift .lsl (vv icI) (.const 3)])))
    (.seq (.assign .local icL (.load .one (vv icAc)))
    (.seq (.call (some (some (.local, icT2), none)) ExQ.fIrr
        [vv icAc, .const 0, vv icL, .const (BitVec.ofNat 64 coreWalkFuel), vv icT, .const 0])
    (.seq (.call (some (some (.local, icTa), none)) fI [vv kFu, vv kD, vv icX])
    (.seq (.call (some (some (.local, icD), none)) fD [vv kFu, vv kD, vv icTa, vv icT2])
    (.ite (.cmp .equal (vv icD) (.const 0)) (.return (.const 0))
    (.seq (.call (some (some (.local, icAc2), none)) ExPre.fAppend [vv icAc, vv icX])
    (.seq (.call (some (some (.local, icR), none)) fIc
        [vv kFu, vv kD, vv icB, vv icA, vv icN, vv icAc2, .op .add [vv icI, .const 1]])
      (.return (vv icR))))))))))))
  (.ite (tagIsE icH 0)
    (.seq (.assign .local icL (.load .one (vv icAc)))
    (.ite (.cmp .equal (vv icL) (.const 0)) (.return (.const 0))
    (.seq (.call (some (some (.local, icT2), none)) ExQ.fIrr
        [vv icAc, .const 0, vv icL, .const (BitVec.ofNat 64 coreWalkFuel), vv icH, .const 0])
    (allocP C icE (.const 8) (.seq (.store (vv icE) (.const 0))
    (.seq (.call (some (some (.local, icR), none)) fIc [vv kFu, vv kD, vv icT2, vv icA, vv icN, vv icE, vv icI])
      (.return (vv icR))))))))
    (.return (.const 0)))))))
  (.return (.const 1))

def icBody (C : Ctx) : ProgHOL 64 := prologue icLocals (icCore C)

structure IcCodes (C : Ctx) : Prop where
  i : C.code.lookup fI = some (pmap kParams, inferE C fIB, .one)
  d : C.code.lookup fD = some (pmap dParams, dE C, .one)
  irr : C.code.lookup ExQ.fIrr = some (ExQ.irrParams.map (fun p => (p, ShapeHOL.one)), ExQ.irrBody C, .one)
  q : ExQ.CodesQ C
  app : C.code.lookup ExPre.fAppend = some (ExPre.appParams.map (fun p => (p, ShapeHOL.one)), ExPre.appBody C, .one)
  self : C.code.lookup fIc = some (icParams.map (fun p => (p, ShapeHOL.one)), icBody C, .one)

section
variable {σ : Type}

theorem ic_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ icLocals → (ctxEnv C ++ icParams.zip vals).get x = none :=
  Knot.params_none C icLocals icParams vals (by decide) (by decide)

theorem ic_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (hc : IcCodes C) (d : Nat)
    (hI : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ e', Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e'] (inferE C fIB) s1 ((knot mode C n).infer d e')
      (PostK (ctxH C H)))
    (hD : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ a b, Callee (σ := σ) (ctxH C H) dParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (dE C) s1 ((knot mode C n).defeq d a b)
      (PostB (ctxH C H)))
    (args : List EIdx) (qa : Nat) (hargs : args.length < 2 ^ 58) :
    ∀ m (i : Nat) (acc : List EIdx) (h : EIdx) (oac : Nat) (H : List (BitVec 64)) (s : AState),
      2 * (args.length - i) + (if acc = [] then 0 else 1) = m → C.H <+: H →
      (∀ j (hj : j < args.length), H[qa + j]? = some (Enc.idxW args[j])) →
      BlkAt H oac (acc.map Enc.idxW) → acc.length ≤ i → i ≤ args.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (icParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW h, cellA C qa,
        BitVec.ofNat 64 args.length, cellA C oac, BitVec.ofNat 64 i])) (icBody C) s
        (iotaCertsFullAux (knot mode C n) C.fe d h acc.toArray args.toArray i) (PostB (ctxH C H)) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro i acc h oac H s hm hp ha hb hacc hi
  refine specR_prologue (postB_locals _) (ic_none _ _) ?_
  unfold icCore
  rw [iotaCertsFullAux]
  have hok1 := ctxOK_H hok H
  obtain ⟨hlo, hlv⟩ := blkAt_get0 hb
  have hw0 : (ctxH C H).H[oac]? = some (BitVec.ofNat 64 acc.length) := by
    show H[oac]? = _; rw [List.getElem?_eq_getElem hlo, hlv]; simp
  by_cases hlt : i < args.length
  · have hlt' : i < args.toArray.size := by simpa using hlt
    rw [dif_pos hlt']
    have hw : BitVec.ofNat 64 i < BitVec.ofNat 64 args.length :=
      (Big.word_lt_iff i args.length (by unfold B; omega) (by unfold B; omega)).mpr hlt
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, icParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hw])
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv icH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, icParams, ctxEnv]) ?_
    refine specR_viewP (C := ctxH C H) h (by simp) (by simp +decide [Env.get] <;> rfl)
      (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
    refine specR_congr (view_bind_eq h v _ s hv) ?_
    refine Knot.specR_tagIteV icH h 6 (by decide) (by decide) (by simp +decide [Env.get, icParams, ctxEnv])
      (fun htg => ?_) (fun htg => ?_)
    · have h6 : v.tagN = 6 := by rw [htn, htg]; rfl
      obtain ⟨ty, b, rfl⟩ : ∃ ty b, v = .forallE ty b := by cases v <;> simp [ENodeView.tagN] at h6 ⊢
      dsimp only
      refine specR_loadI' icT (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
        (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW ty) [Enc.idxW b] []) ?_
      refine specR_loadI' icB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW b) [] []) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H) icX (.op .add [vv icA, .shift .lsl (vv icI) (.const 3)]) (qa + i)
        (Enc.idxW args[i]) (ha i hlt : H[qa + i]? = _) (by decide)
        (by simp +decide [sev, Env.get, icParams, ctxEnv]; rw [cellA_shl C qa i (by omega)]; rfl) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H) icL (vv icAc) oac _ hw0 (by decide)
        (by simp +decide [Env.get, icParams, ctxEnv]; rfl) ?_
      simp only [instantiateListFast, List.size_toArray, List.getElem_toArray]
      refine ILP.callE_spec (C := ctxH C H) icT2 ExQ.fIrr ExQ.irrParams
        [vv icAc, .const 0, vv icL, .const (BitVec.ofNat 64 coreWalkFuel), vv icT, .const 0] (ExQ.irrBody C)
        [cellA C oac, BitVec.ofNat 64 0, BitVec.ofNat 64 acc.length, BitVec.ofNat 64 coreWalkFuel, Enc.idxW ty,
          BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.irr
        ⟨by simp +decide [Env.get, icParams, ctxEnv] <;> rfl, rfl, by simp, rfl, by simp, rfl, trivial⟩
        (ExQ.irr_spec ra (ctxH C H) hok1 (codesQ_H hc.q H) acc.toArray oac (show BlkAt H oac (acc.toArray.toList.map Enc.idxW) by simpa using hb) (by simp; omega) s
          coreWalkFuel 0 acc.length 0 ty CV.coreWalkFuel_lt (by decide) (by omega) (by decide)) (fun ty2 s1 => ?_)
      refine Big.specR_callKC (C := ctxH C H) icTa fI kParams [vv kFu, vv kD, vv icX] (inferE C fIB)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW args[i]] (by decide) rfl (by decide) hc.i
        ⟨by simp +decide [Env.get, icParams, ctxEnv], by simp +decide [Env.get, icParams, ctxEnv], by simp, trivial⟩
        (hI H s1 hp args[i]) (fun ta s2 H2 hp2 _ => ?_)
      refine specR_callNIH (C := ctxH C H2) icD fD dParams [vv kFu, vv kD, vv icTa, vv icT2] (dE C)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ta, Enc.idxW ty2] (by decide) rfl (by decide) hc.d
        ⟨by simp +decide [Env.get, icParams, ctxEnv], by simp +decide [Env.get, icParams, ctxEnv], by simp, by simp,
          trivial⟩
        (PostB (ctxH C H2)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => hD H2 s2 (hp.trans hp2) ta ty2 u hu (fun i hi _ => hlk i (by omega)))
        (fun df w s3 H3 hp3 hw => ?_)
      subst hw
      cases df
      · refine specR_ifI _ 1 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
          (fun h => absurd h (by decide))
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact specR_returnI _ 0 rfl (fun t ht => ⟨H3, hp2.trans hp3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      · refine specR_ifI _ 0 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
          (fun _ => ?_)
        simp only [↓reduceIte]
        refine ExPre.specR_callApp (C := ctxH C H3) (ctxOK_H hok H3) hc.app icAc2 (vv icAc) (vv icX) oac
          (acc.map Enc.idxW) (Enc.idxW args[i]) (by decide) (blkAt_mono hb (hp2.trans hp3))
          (by simp +decide [Env.get, icParams, ctxEnv]; rfl) (by simp) (fun H4 o4 hp4 hb4 => ?_)
        have hb4' : BlkAt H4 o4 ((acc ++ [args[i]]).map Enc.idxW) := by simpa using hb4
        rw [show acc.toArray.push args[i] = (acc ++ [args[i]]).toArray by simp]
        refine specR_congr (m' := iotaCertsFullAux (knot mode C n) C.fe d b (acc ++ [args[i]]).toArray args.toArray
          (i + 1) >>= fun r => pure r) (by simp) ?_
        refine specR_callNIH (C := ctxH C H4) icR fIc icParams
          [vv kFu, vv kD, vv icB, vv icA, vv icN, vv icAc2, .op .add [vv icI, .const 1]] (icBody C)
          [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW b, cellA C qa, BitVec.ofNat 64 args.length, cellA C o4,
            BitVec.ofNat 64 (i + 1)] (by decide) rfl (by decide) hc.self
          ⟨by simp +decide [Env.get, icParams, ctxEnv], by simp +decide [Env.get, icParams, ctxEnv], by simp,
            by simp +decide [Env.get, icParams, ctxEnv], by simp +decide [Env.get, icParams, ctxEnv], by simp <;> rfl,
            by simp +decide [sev, Env.get, icParams, ctxEnv]; exact word_add1_eq i, trivial⟩
          (PostB (ctxH C H4)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
          (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu icParams _ rfl hlk)
            (ih (2 * (args.length - (i + 1)) + 1) (by rw [← hm]; split <;> omega) (i + 1) (acc ++ [args[i]]) b o4 H4 s3
              (by simp) (hp.trans (hp2.trans (hp3.trans hp4)))
              (fun j hj => pfx_get (hp2.trans (hp3.trans hp4)) (ha j hj)) hb4' (by simp; omega) (by omega)))
          (fun r w s5 H5 hp5 hw => ?_)
        subst hw
        exact specR_returnI _ (boolW r) (by simp)
          (fun t ht => ⟨H5, hp2.trans (hp3.trans (hp4.trans hp5)), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · have hn6 : v.tagN ≠ 6 := by
        rw [htn]; intro e; apply htg; apply UInt32.toNat_inj.mp; rw [e]; rfl
      refine Knot.specR_tagIteV icH h 0 (by decide) (by decide) (by simp +decide [Env.get, icParams, ctxEnv])
        (fun htg0 => ?_) (fun htg0 => ?_)
      · have h0 : v.tagN = 0 := by rw [htn, htg0]; rfl
        obtain ⟨k, rfl⟩ : ∃ k, v = .bvar k := by cases v <;> simp [ENodeView.tagN] at h0 ⊢
        dsimp only
        refine UD.specR_heapLoadI' (C := ctxH C H) icL (vv icAc) oac _ hw0 (by decide)
          (by simp +decide [Env.get, icParams, ctxEnv]; rfl) ?_
        by_cases hae : acc = []
        · subst hae
          refine specR_ifI _ 1 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
            (fun _ => ?_) (fun h => absurd h (by decide))
          simp only [List.size_toArray, List.length_nil, ↓reduceIte]
          exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
        have hal : acc.length ≠ 0 := fun e => hae (List.length_eq_zero_iff.mp e)
        have hne := ofNat_succ_ne (acc.length - 1) (by omega)
        rw [show acc.length - 1 + 1 = acc.length by omega] at hne
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
          (fun h => absurd rfl h) (fun _ => ?_)
        rw [if_neg (by simpa using hal)]
        simp only [instantiateListFast, List.size_toArray]
        refine ILP.callE_spec (C := ctxH C H) icT2 ExQ.fIrr ExQ.irrParams
          [vv icAc, .const 0, vv icL, .const (BitVec.ofNat 64 coreWalkFuel), vv icH, .const 0] (ExQ.irrBody C)
          [cellA C oac, BitVec.ofNat 64 0, BitVec.ofNat 64 acc.length, BitVec.ofNat 64 coreWalkFuel, Enc.idxW h,
            BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.irr
          ⟨by simp +decide [Env.get, icParams, ctxEnv] <;> rfl, rfl, by simp, rfl,
            by simp +decide [Env.get, icParams, ctxEnv], rfl, trivial⟩
          (ExQ.irr_spec ra (ctxH C H) hok1 (codesQ_H hc.q H) acc.toArray oac (show BlkAt H oac (acc.toArray.toList.map Enc.idxW) by simpa using hb) (by simp; omega) s
            coreWalkFuel 0 acc.length 0 h CV.coreWalkFuel_lt (by decide) (by omega) (by decide)) (fun ty2 s1 => ?_)
        refine specR_emptyBlk (C0 := C) hok icE (by decide) (fun H' o hp' hb' => ?_)
        refine specR_congr (m' := iotaCertsFullAux (knot mode C n) C.fe d ty2 ([] : List EIdx).toArray args.toArray i
          >>= fun r => pure r) (by simp) ?_
        refine specR_callNIH (C := ctxH C H') icR fIc icParams
          [vv kFu, vv kD, vv icT2, vv icA, vv icN, vv icE, vv icI] (icBody C)
          [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ty2, cellA C qa, BitVec.ofNat 64 args.length, cellA C o,
            BitVec.ofNat 64 i] (by decide) rfl (by decide) hc.self
          ⟨by simp +decide [Env.get, icParams, ctxEnv], by simp +decide [Env.get, icParams, ctxEnv], by simp,
            by simp +decide [Env.get, icParams, ctxEnv], by simp +decide [Env.get, icParams, ctxEnv], by simp <;> rfl,
            by simp +decide [Env.get, icParams, ctxEnv], trivial⟩
          (PostB (ctxH C H')) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H'', hp'', hw, hsr⟩ => ⟨H'', hp'', hw, hsr⟩)
          (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu icParams _ rfl hlk)
            (ih (2 * (args.length - i)) (by rw [← hm, if_neg hae]; omega) i [] ty2 o H' s1
              (by simp) (hp.trans hp') (fun j hj => pfx_get hp' (ha j hj)) (by simpa using hb') (by simp) hi))
          (fun r w s5 H5 hp5 hw => ?_)
        subst hw
        exact specR_returnI _ (boolW r) (by simp)
          (fun t ht => ⟨H5, hp'.trans hp5, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      · have hn0 : v.tagN ≠ 0 := by
          rw [htn]; intro e; apply htg0; apply UInt32.toNat_inj.mp; rw [e]; rfl
        cases v <;> (try simp [ENodeView.tagN] at hn6 hn0) <;>
          exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · have hlt' : ¬ i < args.toArray.size := by simpa using hlt
    rw [dif_neg hlt']
    have hw : ¬ BitVec.ofNat 64 i < BitVec.ofNat 64 args.length := fun x =>
      hlt ((Big.word_lt_iff i args.length (by unfold B; omega) (by unfold B; omega)).mp x)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, icParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hw])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
