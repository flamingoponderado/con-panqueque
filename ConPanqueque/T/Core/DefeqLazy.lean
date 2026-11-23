import ConPanqueque.T.Core.DefeqStuck
import ConPanqueque.T.Core.LazyDelta
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `defeqLazy`: the lazy comparison

`quickDefEq` and proof irrelevance on the unreduced pair; the cheap `whnfCore` of both sides; `quickDefEq`; the
lazy-delta loop; then on the stuck pair the projection pair check, the full `whnfCore` (projection heads only), the
stuck comparison. Callees are hypotheses restricted to an invariant `Q`. `propIrrel`'s body `pB` is abstract.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def yzA := ofString "dlz_yza"
def yzB := ofString "dlz_yzb"
def yzQ := ofString "dlz_yzq"
def yzP := ofString "dlz_yzp"
def yzA1 := ofString "dlz_yza1"
def yzB1 := ofString "dlz_yzb1"
def yzQ2 := ofString "dlz_yzq2"
def yzL := ofString "dlz_yzl"
def yzX := ofString "dlz_yzx"
def yzY := ofString "dlz_yzy"
def yzJ := ofString "dlz_yzj"
def yzPa := ofString "dlz_yzpa"
def yzPb := ofString "dlz_yzpb"
def yzA2 := ofString "dlz_yza2"
def yzB2 := ofString "dlz_yzb2"
def yzK := ofString "dlz_yzk"
def yzV := ofString "dlz_yzv"
def fYz := ofString "defeqLazy"
def fPri := ofString "propIrrel"
def priParams : List MlS := [kFu, kD, ofString "pri_a", ofString "pri_b"]

@[simp] theorem dlz_yzA_ne_yzB : yzA ≠ yzB := by decide
@[simp] theorem dlz_yzA_ne_yzQ : yzA ≠ yzQ := by decide
@[simp] theorem dlz_yzA_ne_yzP : yzA ≠ yzP := by decide
@[simp] theorem dlz_yzA_ne_yzA1 : yzA ≠ yzA1 := by decide
@[simp] theorem dlz_yzA_ne_yzB1 : yzA ≠ yzB1 := by decide
@[simp] theorem dlz_yzA_ne_yzQ2 : yzA ≠ yzQ2 := by decide
@[simp] theorem dlz_yzA_ne_yzL : yzA ≠ yzL := by decide
@[simp] theorem dlz_yzA_ne_yzX : yzA ≠ yzX := by decide
@[simp] theorem dlz_yzA_ne_yzY : yzA ≠ yzY := by decide
@[simp] theorem dlz_yzA_ne_yzJ : yzA ≠ yzJ := by decide
@[simp] theorem dlz_yzA_ne_yzPa : yzA ≠ yzPa := by decide
@[simp] theorem dlz_yzA_ne_yzPb : yzA ≠ yzPb := by decide
@[simp] theorem dlz_yzA_ne_yzA2 : yzA ≠ yzA2 := by decide
@[simp] theorem dlz_yzA_ne_yzB2 : yzA ≠ yzB2 := by decide
@[simp] theorem dlz_yzA_ne_yzK : yzA ≠ yzK := by decide
@[simp] theorem dlz_yzA_ne_yzV : yzA ≠ yzV := by decide
@[simp] theorem dlz_yzA_ne_lFl : yzA ≠ lFl := by decide
@[simp] theorem dlz_lFl_ne_yzA : lFl ≠ yzA := by decide
@[simp] theorem dlz_yzA_ne_lDh : yzA ≠ lDh := by decide
@[simp] theorem dlz_lDh_ne_yzA : lDh ≠ yzA := by decide
@[simp] theorem dlz_yzA_ne_lDt : yzA ≠ lDt := by decide
@[simp] theorem dlz_lDt_ne_yzA : lDt ≠ yzA := by decide
@[simp] theorem dlz_yzA_ne_lDg : yzA ≠ lDg := by decide
@[simp] theorem dlz_lDg_ne_yzA : lDg ≠ yzA := by decide
@[simp] theorem dlz_yzA_ne_lDi : yzA ≠ lDi := by decide
@[simp] theorem dlz_lDi_ne_yzA : lDi ≠ yzA := by decide
@[simp] theorem dlz_yzA_ne_lRp : yzA ≠ lRp := by decide
@[simp] theorem dlz_lRp_ne_yzA : lRp ≠ yzA := by decide
@[simp] theorem dlz_yzA_ne_lRn : yzA ≠ lRn := by decide
@[simp] theorem dlz_lRn_ne_yzA : lRn ≠ yzA := by decide
@[simp] theorem dlz_yzA_ne_lFle : yzA ≠ lFle := by decide
@[simp] theorem dlz_lFle_ne_yzA : lFle ≠ yzA := by decide
@[simp] theorem dlz_yzA_ne_lKb : yzA ≠ lKb := by decide
@[simp] theorem dlz_lKb_ne_yzA : lKb ≠ yzA := by decide
@[simp] theorem dlz_yzA_ne_lDir : yzA ≠ lDir := by decide
@[simp] theorem dlz_lDir_ne_yzA : lDir ≠ yzA := by decide
@[simp] theorem dlz_yzA_ne_lFln : yzA ≠ lFln := by decide
@[simp] theorem dlz_lFln_ne_yzA : lFln ≠ yzA := by decide
@[simp] theorem dlz_yzA_ne_lFll : yzA ≠ lFll := by decide
@[simp] theorem dlz_lFll_ne_yzA : lFll ≠ yzA := by decide
@[simp] theorem dlz_yzA_ne_lFls : yzA ≠ lFls := by decide
@[simp] theorem dlz_lFls_ne_yzA : lFls ≠ yzA := by decide
@[simp] theorem dlz_yzA_ne_kFu : yzA ≠ kFu := by decide
@[simp] theorem dlz_kFu_ne_yzA : kFu ≠ yzA := by decide
@[simp] theorem dlz_yzA_ne_kD : yzA ≠ kD := by decide
@[simp] theorem dlz_kD_ne_yzA : kD ≠ yzA := by decide
@[simp] theorem dlz_yzB_ne_yzA : yzB ≠ yzA := by decide
@[simp] theorem dlz_yzB_ne_yzQ : yzB ≠ yzQ := by decide
@[simp] theorem dlz_yzB_ne_yzP : yzB ≠ yzP := by decide
@[simp] theorem dlz_yzB_ne_yzA1 : yzB ≠ yzA1 := by decide
@[simp] theorem dlz_yzB_ne_yzB1 : yzB ≠ yzB1 := by decide
@[simp] theorem dlz_yzB_ne_yzQ2 : yzB ≠ yzQ2 := by decide
@[simp] theorem dlz_yzB_ne_yzL : yzB ≠ yzL := by decide
@[simp] theorem dlz_yzB_ne_yzX : yzB ≠ yzX := by decide
@[simp] theorem dlz_yzB_ne_yzY : yzB ≠ yzY := by decide
@[simp] theorem dlz_yzB_ne_yzJ : yzB ≠ yzJ := by decide
@[simp] theorem dlz_yzB_ne_yzPa : yzB ≠ yzPa := by decide
@[simp] theorem dlz_yzB_ne_yzPb : yzB ≠ yzPb := by decide
@[simp] theorem dlz_yzB_ne_yzA2 : yzB ≠ yzA2 := by decide
@[simp] theorem dlz_yzB_ne_yzB2 : yzB ≠ yzB2 := by decide
@[simp] theorem dlz_yzB_ne_yzK : yzB ≠ yzK := by decide
@[simp] theorem dlz_yzB_ne_yzV : yzB ≠ yzV := by decide
@[simp] theorem dlz_yzB_ne_lFl : yzB ≠ lFl := by decide
@[simp] theorem dlz_lFl_ne_yzB : lFl ≠ yzB := by decide
@[simp] theorem dlz_yzB_ne_lDh : yzB ≠ lDh := by decide
@[simp] theorem dlz_lDh_ne_yzB : lDh ≠ yzB := by decide
@[simp] theorem dlz_yzB_ne_lDt : yzB ≠ lDt := by decide
@[simp] theorem dlz_lDt_ne_yzB : lDt ≠ yzB := by decide
@[simp] theorem dlz_yzB_ne_lDg : yzB ≠ lDg := by decide
@[simp] theorem dlz_lDg_ne_yzB : lDg ≠ yzB := by decide
@[simp] theorem dlz_yzB_ne_lDi : yzB ≠ lDi := by decide
@[simp] theorem dlz_lDi_ne_yzB : lDi ≠ yzB := by decide
@[simp] theorem dlz_yzB_ne_lRp : yzB ≠ lRp := by decide
@[simp] theorem dlz_lRp_ne_yzB : lRp ≠ yzB := by decide
@[simp] theorem dlz_yzB_ne_lRn : yzB ≠ lRn := by decide
@[simp] theorem dlz_lRn_ne_yzB : lRn ≠ yzB := by decide
@[simp] theorem dlz_yzB_ne_lFle : yzB ≠ lFle := by decide
@[simp] theorem dlz_lFle_ne_yzB : lFle ≠ yzB := by decide
@[simp] theorem dlz_yzB_ne_lKb : yzB ≠ lKb := by decide
@[simp] theorem dlz_lKb_ne_yzB : lKb ≠ yzB := by decide
@[simp] theorem dlz_yzB_ne_lDir : yzB ≠ lDir := by decide
@[simp] theorem dlz_lDir_ne_yzB : lDir ≠ yzB := by decide
@[simp] theorem dlz_yzB_ne_lFln : yzB ≠ lFln := by decide
@[simp] theorem dlz_lFln_ne_yzB : lFln ≠ yzB := by decide
@[simp] theorem dlz_yzB_ne_lFll : yzB ≠ lFll := by decide
@[simp] theorem dlz_lFll_ne_yzB : lFll ≠ yzB := by decide
@[simp] theorem dlz_yzB_ne_lFls : yzB ≠ lFls := by decide
@[simp] theorem dlz_lFls_ne_yzB : lFls ≠ yzB := by decide
@[simp] theorem dlz_yzB_ne_kFu : yzB ≠ kFu := by decide
@[simp] theorem dlz_kFu_ne_yzB : kFu ≠ yzB := by decide
@[simp] theorem dlz_yzB_ne_kD : yzB ≠ kD := by decide
@[simp] theorem dlz_kD_ne_yzB : kD ≠ yzB := by decide
@[simp] theorem dlz_yzQ_ne_yzA : yzQ ≠ yzA := by decide
@[simp] theorem dlz_yzQ_ne_yzB : yzQ ≠ yzB := by decide
@[simp] theorem dlz_yzQ_ne_yzP : yzQ ≠ yzP := by decide
@[simp] theorem dlz_yzQ_ne_yzA1 : yzQ ≠ yzA1 := by decide
@[simp] theorem dlz_yzQ_ne_yzB1 : yzQ ≠ yzB1 := by decide
@[simp] theorem dlz_yzQ_ne_yzQ2 : yzQ ≠ yzQ2 := by decide
@[simp] theorem dlz_yzQ_ne_yzL : yzQ ≠ yzL := by decide
@[simp] theorem dlz_yzQ_ne_yzX : yzQ ≠ yzX := by decide
@[simp] theorem dlz_yzQ_ne_yzY : yzQ ≠ yzY := by decide
@[simp] theorem dlz_yzQ_ne_yzJ : yzQ ≠ yzJ := by decide
@[simp] theorem dlz_yzQ_ne_yzPa : yzQ ≠ yzPa := by decide
@[simp] theorem dlz_yzQ_ne_yzPb : yzQ ≠ yzPb := by decide
@[simp] theorem dlz_yzQ_ne_yzA2 : yzQ ≠ yzA2 := by decide
@[simp] theorem dlz_yzQ_ne_yzB2 : yzQ ≠ yzB2 := by decide
@[simp] theorem dlz_yzQ_ne_yzK : yzQ ≠ yzK := by decide
@[simp] theorem dlz_yzQ_ne_yzV : yzQ ≠ yzV := by decide
@[simp] theorem dlz_yzQ_ne_lFl : yzQ ≠ lFl := by decide
@[simp] theorem dlz_lFl_ne_yzQ : lFl ≠ yzQ := by decide
@[simp] theorem dlz_yzQ_ne_lDh : yzQ ≠ lDh := by decide
@[simp] theorem dlz_lDh_ne_yzQ : lDh ≠ yzQ := by decide
@[simp] theorem dlz_yzQ_ne_lDt : yzQ ≠ lDt := by decide
@[simp] theorem dlz_lDt_ne_yzQ : lDt ≠ yzQ := by decide
@[simp] theorem dlz_yzQ_ne_lDg : yzQ ≠ lDg := by decide
@[simp] theorem dlz_lDg_ne_yzQ : lDg ≠ yzQ := by decide
@[simp] theorem dlz_yzQ_ne_lDi : yzQ ≠ lDi := by decide
@[simp] theorem dlz_lDi_ne_yzQ : lDi ≠ yzQ := by decide
@[simp] theorem dlz_yzQ_ne_lRp : yzQ ≠ lRp := by decide
@[simp] theorem dlz_lRp_ne_yzQ : lRp ≠ yzQ := by decide
@[simp] theorem dlz_yzQ_ne_lRn : yzQ ≠ lRn := by decide
@[simp] theorem dlz_lRn_ne_yzQ : lRn ≠ yzQ := by decide
@[simp] theorem dlz_yzQ_ne_lFle : yzQ ≠ lFle := by decide
@[simp] theorem dlz_lFle_ne_yzQ : lFle ≠ yzQ := by decide
@[simp] theorem dlz_yzQ_ne_lKb : yzQ ≠ lKb := by decide
@[simp] theorem dlz_lKb_ne_yzQ : lKb ≠ yzQ := by decide
@[simp] theorem dlz_yzQ_ne_lDir : yzQ ≠ lDir := by decide
@[simp] theorem dlz_lDir_ne_yzQ : lDir ≠ yzQ := by decide
@[simp] theorem dlz_yzQ_ne_lFln : yzQ ≠ lFln := by decide
@[simp] theorem dlz_lFln_ne_yzQ : lFln ≠ yzQ := by decide
@[simp] theorem dlz_yzQ_ne_lFll : yzQ ≠ lFll := by decide
@[simp] theorem dlz_lFll_ne_yzQ : lFll ≠ yzQ := by decide
@[simp] theorem dlz_yzQ_ne_lFls : yzQ ≠ lFls := by decide
@[simp] theorem dlz_lFls_ne_yzQ : lFls ≠ yzQ := by decide
@[simp] theorem dlz_yzQ_ne_kFu : yzQ ≠ kFu := by decide
@[simp] theorem dlz_kFu_ne_yzQ : kFu ≠ yzQ := by decide
@[simp] theorem dlz_yzQ_ne_kD : yzQ ≠ kD := by decide
@[simp] theorem dlz_kD_ne_yzQ : kD ≠ yzQ := by decide
@[simp] theorem dlz_yzP_ne_yzA : yzP ≠ yzA := by decide
@[simp] theorem dlz_yzP_ne_yzB : yzP ≠ yzB := by decide
@[simp] theorem dlz_yzP_ne_yzQ : yzP ≠ yzQ := by decide
@[simp] theorem dlz_yzP_ne_yzA1 : yzP ≠ yzA1 := by decide
@[simp] theorem dlz_yzP_ne_yzB1 : yzP ≠ yzB1 := by decide
@[simp] theorem dlz_yzP_ne_yzQ2 : yzP ≠ yzQ2 := by decide
@[simp] theorem dlz_yzP_ne_yzL : yzP ≠ yzL := by decide
@[simp] theorem dlz_yzP_ne_yzX : yzP ≠ yzX := by decide
@[simp] theorem dlz_yzP_ne_yzY : yzP ≠ yzY := by decide
@[simp] theorem dlz_yzP_ne_yzJ : yzP ≠ yzJ := by decide
@[simp] theorem dlz_yzP_ne_yzPa : yzP ≠ yzPa := by decide
@[simp] theorem dlz_yzP_ne_yzPb : yzP ≠ yzPb := by decide
@[simp] theorem dlz_yzP_ne_yzA2 : yzP ≠ yzA2 := by decide
@[simp] theorem dlz_yzP_ne_yzB2 : yzP ≠ yzB2 := by decide
@[simp] theorem dlz_yzP_ne_yzK : yzP ≠ yzK := by decide
@[simp] theorem dlz_yzP_ne_yzV : yzP ≠ yzV := by decide
@[simp] theorem dlz_yzP_ne_lFl : yzP ≠ lFl := by decide
@[simp] theorem dlz_lFl_ne_yzP : lFl ≠ yzP := by decide
@[simp] theorem dlz_yzP_ne_lDh : yzP ≠ lDh := by decide
@[simp] theorem dlz_lDh_ne_yzP : lDh ≠ yzP := by decide
@[simp] theorem dlz_yzP_ne_lDt : yzP ≠ lDt := by decide
@[simp] theorem dlz_lDt_ne_yzP : lDt ≠ yzP := by decide
@[simp] theorem dlz_yzP_ne_lDg : yzP ≠ lDg := by decide
@[simp] theorem dlz_lDg_ne_yzP : lDg ≠ yzP := by decide
@[simp] theorem dlz_yzP_ne_lDi : yzP ≠ lDi := by decide
@[simp] theorem dlz_lDi_ne_yzP : lDi ≠ yzP := by decide
@[simp] theorem dlz_yzP_ne_lRp : yzP ≠ lRp := by decide
@[simp] theorem dlz_lRp_ne_yzP : lRp ≠ yzP := by decide
@[simp] theorem dlz_yzP_ne_lRn : yzP ≠ lRn := by decide
@[simp] theorem dlz_lRn_ne_yzP : lRn ≠ yzP := by decide
@[simp] theorem dlz_yzP_ne_lFle : yzP ≠ lFle := by decide
@[simp] theorem dlz_lFle_ne_yzP : lFle ≠ yzP := by decide
@[simp] theorem dlz_yzP_ne_lKb : yzP ≠ lKb := by decide
@[simp] theorem dlz_lKb_ne_yzP : lKb ≠ yzP := by decide
@[simp] theorem dlz_yzP_ne_lDir : yzP ≠ lDir := by decide
@[simp] theorem dlz_lDir_ne_yzP : lDir ≠ yzP := by decide
@[simp] theorem dlz_yzP_ne_lFln : yzP ≠ lFln := by decide
@[simp] theorem dlz_lFln_ne_yzP : lFln ≠ yzP := by decide
@[simp] theorem dlz_yzP_ne_lFll : yzP ≠ lFll := by decide
@[simp] theorem dlz_lFll_ne_yzP : lFll ≠ yzP := by decide
@[simp] theorem dlz_yzP_ne_lFls : yzP ≠ lFls := by decide
@[simp] theorem dlz_lFls_ne_yzP : lFls ≠ yzP := by decide
@[simp] theorem dlz_yzP_ne_kFu : yzP ≠ kFu := by decide
@[simp] theorem dlz_kFu_ne_yzP : kFu ≠ yzP := by decide
@[simp] theorem dlz_yzP_ne_kD : yzP ≠ kD := by decide
@[simp] theorem dlz_kD_ne_yzP : kD ≠ yzP := by decide
@[simp] theorem dlz_yzA1_ne_yzA : yzA1 ≠ yzA := by decide
@[simp] theorem dlz_yzA1_ne_yzB : yzA1 ≠ yzB := by decide
@[simp] theorem dlz_yzA1_ne_yzQ : yzA1 ≠ yzQ := by decide
@[simp] theorem dlz_yzA1_ne_yzP : yzA1 ≠ yzP := by decide
@[simp] theorem dlz_yzA1_ne_yzB1 : yzA1 ≠ yzB1 := by decide
@[simp] theorem dlz_yzA1_ne_yzQ2 : yzA1 ≠ yzQ2 := by decide
@[simp] theorem dlz_yzA1_ne_yzL : yzA1 ≠ yzL := by decide
@[simp] theorem dlz_yzA1_ne_yzX : yzA1 ≠ yzX := by decide
@[simp] theorem dlz_yzA1_ne_yzY : yzA1 ≠ yzY := by decide
@[simp] theorem dlz_yzA1_ne_yzJ : yzA1 ≠ yzJ := by decide
@[simp] theorem dlz_yzA1_ne_yzPa : yzA1 ≠ yzPa := by decide
@[simp] theorem dlz_yzA1_ne_yzPb : yzA1 ≠ yzPb := by decide
@[simp] theorem dlz_yzA1_ne_yzA2 : yzA1 ≠ yzA2 := by decide
@[simp] theorem dlz_yzA1_ne_yzB2 : yzA1 ≠ yzB2 := by decide
@[simp] theorem dlz_yzA1_ne_yzK : yzA1 ≠ yzK := by decide
@[simp] theorem dlz_yzA1_ne_yzV : yzA1 ≠ yzV := by decide
@[simp] theorem dlz_yzA1_ne_lFl : yzA1 ≠ lFl := by decide
@[simp] theorem dlz_lFl_ne_yzA1 : lFl ≠ yzA1 := by decide
@[simp] theorem dlz_yzA1_ne_lDh : yzA1 ≠ lDh := by decide
@[simp] theorem dlz_lDh_ne_yzA1 : lDh ≠ yzA1 := by decide
@[simp] theorem dlz_yzA1_ne_lDt : yzA1 ≠ lDt := by decide
@[simp] theorem dlz_lDt_ne_yzA1 : lDt ≠ yzA1 := by decide
@[simp] theorem dlz_yzA1_ne_lDg : yzA1 ≠ lDg := by decide
@[simp] theorem dlz_lDg_ne_yzA1 : lDg ≠ yzA1 := by decide
@[simp] theorem dlz_yzA1_ne_lDi : yzA1 ≠ lDi := by decide
@[simp] theorem dlz_lDi_ne_yzA1 : lDi ≠ yzA1 := by decide
@[simp] theorem dlz_yzA1_ne_lRp : yzA1 ≠ lRp := by decide
@[simp] theorem dlz_lRp_ne_yzA1 : lRp ≠ yzA1 := by decide
@[simp] theorem dlz_yzA1_ne_lRn : yzA1 ≠ lRn := by decide
@[simp] theorem dlz_lRn_ne_yzA1 : lRn ≠ yzA1 := by decide
@[simp] theorem dlz_yzA1_ne_lFle : yzA1 ≠ lFle := by decide
@[simp] theorem dlz_lFle_ne_yzA1 : lFle ≠ yzA1 := by decide
@[simp] theorem dlz_yzA1_ne_lKb : yzA1 ≠ lKb := by decide
@[simp] theorem dlz_lKb_ne_yzA1 : lKb ≠ yzA1 := by decide
@[simp] theorem dlz_yzA1_ne_lDir : yzA1 ≠ lDir := by decide
@[simp] theorem dlz_lDir_ne_yzA1 : lDir ≠ yzA1 := by decide
@[simp] theorem dlz_yzA1_ne_lFln : yzA1 ≠ lFln := by decide
@[simp] theorem dlz_lFln_ne_yzA1 : lFln ≠ yzA1 := by decide
@[simp] theorem dlz_yzA1_ne_lFll : yzA1 ≠ lFll := by decide
@[simp] theorem dlz_lFll_ne_yzA1 : lFll ≠ yzA1 := by decide
@[simp] theorem dlz_yzA1_ne_lFls : yzA1 ≠ lFls := by decide
@[simp] theorem dlz_lFls_ne_yzA1 : lFls ≠ yzA1 := by decide
@[simp] theorem dlz_yzA1_ne_kFu : yzA1 ≠ kFu := by decide
@[simp] theorem dlz_kFu_ne_yzA1 : kFu ≠ yzA1 := by decide
@[simp] theorem dlz_yzA1_ne_kD : yzA1 ≠ kD := by decide
@[simp] theorem dlz_kD_ne_yzA1 : kD ≠ yzA1 := by decide
@[simp] theorem dlz_yzB1_ne_yzA : yzB1 ≠ yzA := by decide
@[simp] theorem dlz_yzB1_ne_yzB : yzB1 ≠ yzB := by decide
@[simp] theorem dlz_yzB1_ne_yzQ : yzB1 ≠ yzQ := by decide
@[simp] theorem dlz_yzB1_ne_yzP : yzB1 ≠ yzP := by decide
@[simp] theorem dlz_yzB1_ne_yzA1 : yzB1 ≠ yzA1 := by decide
@[simp] theorem dlz_yzB1_ne_yzQ2 : yzB1 ≠ yzQ2 := by decide
@[simp] theorem dlz_yzB1_ne_yzL : yzB1 ≠ yzL := by decide
@[simp] theorem dlz_yzB1_ne_yzX : yzB1 ≠ yzX := by decide
@[simp] theorem dlz_yzB1_ne_yzY : yzB1 ≠ yzY := by decide
@[simp] theorem dlz_yzB1_ne_yzJ : yzB1 ≠ yzJ := by decide
@[simp] theorem dlz_yzB1_ne_yzPa : yzB1 ≠ yzPa := by decide
@[simp] theorem dlz_yzB1_ne_yzPb : yzB1 ≠ yzPb := by decide
@[simp] theorem dlz_yzB1_ne_yzA2 : yzB1 ≠ yzA2 := by decide
@[simp] theorem dlz_yzB1_ne_yzB2 : yzB1 ≠ yzB2 := by decide
@[simp] theorem dlz_yzB1_ne_yzK : yzB1 ≠ yzK := by decide
@[simp] theorem dlz_yzB1_ne_yzV : yzB1 ≠ yzV := by decide
@[simp] theorem dlz_yzB1_ne_lFl : yzB1 ≠ lFl := by decide
@[simp] theorem dlz_lFl_ne_yzB1 : lFl ≠ yzB1 := by decide
@[simp] theorem dlz_yzB1_ne_lDh : yzB1 ≠ lDh := by decide
@[simp] theorem dlz_lDh_ne_yzB1 : lDh ≠ yzB1 := by decide
@[simp] theorem dlz_yzB1_ne_lDt : yzB1 ≠ lDt := by decide
@[simp] theorem dlz_lDt_ne_yzB1 : lDt ≠ yzB1 := by decide
@[simp] theorem dlz_yzB1_ne_lDg : yzB1 ≠ lDg := by decide
@[simp] theorem dlz_lDg_ne_yzB1 : lDg ≠ yzB1 := by decide
@[simp] theorem dlz_yzB1_ne_lDi : yzB1 ≠ lDi := by decide
@[simp] theorem dlz_lDi_ne_yzB1 : lDi ≠ yzB1 := by decide
@[simp] theorem dlz_yzB1_ne_lRp : yzB1 ≠ lRp := by decide
@[simp] theorem dlz_lRp_ne_yzB1 : lRp ≠ yzB1 := by decide
@[simp] theorem dlz_yzB1_ne_lRn : yzB1 ≠ lRn := by decide
@[simp] theorem dlz_lRn_ne_yzB1 : lRn ≠ yzB1 := by decide
@[simp] theorem dlz_yzB1_ne_lFle : yzB1 ≠ lFle := by decide
@[simp] theorem dlz_lFle_ne_yzB1 : lFle ≠ yzB1 := by decide
@[simp] theorem dlz_yzB1_ne_lKb : yzB1 ≠ lKb := by decide
@[simp] theorem dlz_lKb_ne_yzB1 : lKb ≠ yzB1 := by decide
@[simp] theorem dlz_yzB1_ne_lDir : yzB1 ≠ lDir := by decide
@[simp] theorem dlz_lDir_ne_yzB1 : lDir ≠ yzB1 := by decide
@[simp] theorem dlz_yzB1_ne_lFln : yzB1 ≠ lFln := by decide
@[simp] theorem dlz_lFln_ne_yzB1 : lFln ≠ yzB1 := by decide
@[simp] theorem dlz_yzB1_ne_lFll : yzB1 ≠ lFll := by decide
@[simp] theorem dlz_lFll_ne_yzB1 : lFll ≠ yzB1 := by decide
@[simp] theorem dlz_yzB1_ne_lFls : yzB1 ≠ lFls := by decide
@[simp] theorem dlz_lFls_ne_yzB1 : lFls ≠ yzB1 := by decide
@[simp] theorem dlz_yzB1_ne_kFu : yzB1 ≠ kFu := by decide
@[simp] theorem dlz_kFu_ne_yzB1 : kFu ≠ yzB1 := by decide
@[simp] theorem dlz_yzB1_ne_kD : yzB1 ≠ kD := by decide
@[simp] theorem dlz_kD_ne_yzB1 : kD ≠ yzB1 := by decide
@[simp] theorem dlz_yzQ2_ne_yzA : yzQ2 ≠ yzA := by decide
@[simp] theorem dlz_yzQ2_ne_yzB : yzQ2 ≠ yzB := by decide
@[simp] theorem dlz_yzQ2_ne_yzQ : yzQ2 ≠ yzQ := by decide
@[simp] theorem dlz_yzQ2_ne_yzP : yzQ2 ≠ yzP := by decide
@[simp] theorem dlz_yzQ2_ne_yzA1 : yzQ2 ≠ yzA1 := by decide
@[simp] theorem dlz_yzQ2_ne_yzB1 : yzQ2 ≠ yzB1 := by decide
@[simp] theorem dlz_yzQ2_ne_yzL : yzQ2 ≠ yzL := by decide
@[simp] theorem dlz_yzQ2_ne_yzX : yzQ2 ≠ yzX := by decide
@[simp] theorem dlz_yzQ2_ne_yzY : yzQ2 ≠ yzY := by decide
@[simp] theorem dlz_yzQ2_ne_yzJ : yzQ2 ≠ yzJ := by decide
@[simp] theorem dlz_yzQ2_ne_yzPa : yzQ2 ≠ yzPa := by decide
@[simp] theorem dlz_yzQ2_ne_yzPb : yzQ2 ≠ yzPb := by decide
@[simp] theorem dlz_yzQ2_ne_yzA2 : yzQ2 ≠ yzA2 := by decide
@[simp] theorem dlz_yzQ2_ne_yzB2 : yzQ2 ≠ yzB2 := by decide
@[simp] theorem dlz_yzQ2_ne_yzK : yzQ2 ≠ yzK := by decide
@[simp] theorem dlz_yzQ2_ne_yzV : yzQ2 ≠ yzV := by decide
@[simp] theorem dlz_yzQ2_ne_lFl : yzQ2 ≠ lFl := by decide
@[simp] theorem dlz_lFl_ne_yzQ2 : lFl ≠ yzQ2 := by decide
@[simp] theorem dlz_yzQ2_ne_lDh : yzQ2 ≠ lDh := by decide
@[simp] theorem dlz_lDh_ne_yzQ2 : lDh ≠ yzQ2 := by decide
@[simp] theorem dlz_yzQ2_ne_lDt : yzQ2 ≠ lDt := by decide
@[simp] theorem dlz_lDt_ne_yzQ2 : lDt ≠ yzQ2 := by decide
@[simp] theorem dlz_yzQ2_ne_lDg : yzQ2 ≠ lDg := by decide
@[simp] theorem dlz_lDg_ne_yzQ2 : lDg ≠ yzQ2 := by decide
@[simp] theorem dlz_yzQ2_ne_lDi : yzQ2 ≠ lDi := by decide
@[simp] theorem dlz_lDi_ne_yzQ2 : lDi ≠ yzQ2 := by decide
@[simp] theorem dlz_yzQ2_ne_lRp : yzQ2 ≠ lRp := by decide
@[simp] theorem dlz_lRp_ne_yzQ2 : lRp ≠ yzQ2 := by decide
@[simp] theorem dlz_yzQ2_ne_lRn : yzQ2 ≠ lRn := by decide
@[simp] theorem dlz_lRn_ne_yzQ2 : lRn ≠ yzQ2 := by decide
@[simp] theorem dlz_yzQ2_ne_lFle : yzQ2 ≠ lFle := by decide
@[simp] theorem dlz_lFle_ne_yzQ2 : lFle ≠ yzQ2 := by decide
@[simp] theorem dlz_yzQ2_ne_lKb : yzQ2 ≠ lKb := by decide
@[simp] theorem dlz_lKb_ne_yzQ2 : lKb ≠ yzQ2 := by decide
@[simp] theorem dlz_yzQ2_ne_lDir : yzQ2 ≠ lDir := by decide
@[simp] theorem dlz_lDir_ne_yzQ2 : lDir ≠ yzQ2 := by decide
@[simp] theorem dlz_yzQ2_ne_lFln : yzQ2 ≠ lFln := by decide
@[simp] theorem dlz_lFln_ne_yzQ2 : lFln ≠ yzQ2 := by decide
@[simp] theorem dlz_yzQ2_ne_lFll : yzQ2 ≠ lFll := by decide
@[simp] theorem dlz_lFll_ne_yzQ2 : lFll ≠ yzQ2 := by decide
@[simp] theorem dlz_yzQ2_ne_lFls : yzQ2 ≠ lFls := by decide
@[simp] theorem dlz_lFls_ne_yzQ2 : lFls ≠ yzQ2 := by decide
@[simp] theorem dlz_yzQ2_ne_kFu : yzQ2 ≠ kFu := by decide
@[simp] theorem dlz_kFu_ne_yzQ2 : kFu ≠ yzQ2 := by decide
@[simp] theorem dlz_yzQ2_ne_kD : yzQ2 ≠ kD := by decide
@[simp] theorem dlz_kD_ne_yzQ2 : kD ≠ yzQ2 := by decide
@[simp] theorem dlz_yzL_ne_yzA : yzL ≠ yzA := by decide
@[simp] theorem dlz_yzL_ne_yzB : yzL ≠ yzB := by decide
@[simp] theorem dlz_yzL_ne_yzQ : yzL ≠ yzQ := by decide
@[simp] theorem dlz_yzL_ne_yzP : yzL ≠ yzP := by decide
@[simp] theorem dlz_yzL_ne_yzA1 : yzL ≠ yzA1 := by decide
@[simp] theorem dlz_yzL_ne_yzB1 : yzL ≠ yzB1 := by decide
@[simp] theorem dlz_yzL_ne_yzQ2 : yzL ≠ yzQ2 := by decide
@[simp] theorem dlz_yzL_ne_yzX : yzL ≠ yzX := by decide
@[simp] theorem dlz_yzL_ne_yzY : yzL ≠ yzY := by decide
@[simp] theorem dlz_yzL_ne_yzJ : yzL ≠ yzJ := by decide
@[simp] theorem dlz_yzL_ne_yzPa : yzL ≠ yzPa := by decide
@[simp] theorem dlz_yzL_ne_yzPb : yzL ≠ yzPb := by decide
@[simp] theorem dlz_yzL_ne_yzA2 : yzL ≠ yzA2 := by decide
@[simp] theorem dlz_yzL_ne_yzB2 : yzL ≠ yzB2 := by decide
@[simp] theorem dlz_yzL_ne_yzK : yzL ≠ yzK := by decide
@[simp] theorem dlz_yzL_ne_yzV : yzL ≠ yzV := by decide
@[simp] theorem dlz_yzL_ne_lFl : yzL ≠ lFl := by decide
@[simp] theorem dlz_lFl_ne_yzL : lFl ≠ yzL := by decide
@[simp] theorem dlz_yzL_ne_lDh : yzL ≠ lDh := by decide
@[simp] theorem dlz_lDh_ne_yzL : lDh ≠ yzL := by decide
@[simp] theorem dlz_yzL_ne_lDt : yzL ≠ lDt := by decide
@[simp] theorem dlz_lDt_ne_yzL : lDt ≠ yzL := by decide
@[simp] theorem dlz_yzL_ne_lDg : yzL ≠ lDg := by decide
@[simp] theorem dlz_lDg_ne_yzL : lDg ≠ yzL := by decide
@[simp] theorem dlz_yzL_ne_lDi : yzL ≠ lDi := by decide
@[simp] theorem dlz_lDi_ne_yzL : lDi ≠ yzL := by decide
@[simp] theorem dlz_yzL_ne_lRp : yzL ≠ lRp := by decide
@[simp] theorem dlz_lRp_ne_yzL : lRp ≠ yzL := by decide
@[simp] theorem dlz_yzL_ne_lRn : yzL ≠ lRn := by decide
@[simp] theorem dlz_lRn_ne_yzL : lRn ≠ yzL := by decide
@[simp] theorem dlz_yzL_ne_lFle : yzL ≠ lFle := by decide
@[simp] theorem dlz_lFle_ne_yzL : lFle ≠ yzL := by decide
@[simp] theorem dlz_yzL_ne_lKb : yzL ≠ lKb := by decide
@[simp] theorem dlz_lKb_ne_yzL : lKb ≠ yzL := by decide
@[simp] theorem dlz_yzL_ne_lDir : yzL ≠ lDir := by decide
@[simp] theorem dlz_lDir_ne_yzL : lDir ≠ yzL := by decide
@[simp] theorem dlz_yzL_ne_lFln : yzL ≠ lFln := by decide
@[simp] theorem dlz_lFln_ne_yzL : lFln ≠ yzL := by decide
@[simp] theorem dlz_yzL_ne_lFll : yzL ≠ lFll := by decide
@[simp] theorem dlz_lFll_ne_yzL : lFll ≠ yzL := by decide
@[simp] theorem dlz_yzL_ne_lFls : yzL ≠ lFls := by decide
@[simp] theorem dlz_lFls_ne_yzL : lFls ≠ yzL := by decide
@[simp] theorem dlz_yzL_ne_kFu : yzL ≠ kFu := by decide
@[simp] theorem dlz_kFu_ne_yzL : kFu ≠ yzL := by decide
@[simp] theorem dlz_yzL_ne_kD : yzL ≠ kD := by decide
@[simp] theorem dlz_kD_ne_yzL : kD ≠ yzL := by decide
@[simp] theorem dlz_yzX_ne_yzA : yzX ≠ yzA := by decide
@[simp] theorem dlz_yzX_ne_yzB : yzX ≠ yzB := by decide
@[simp] theorem dlz_yzX_ne_yzQ : yzX ≠ yzQ := by decide
@[simp] theorem dlz_yzX_ne_yzP : yzX ≠ yzP := by decide
@[simp] theorem dlz_yzX_ne_yzA1 : yzX ≠ yzA1 := by decide
@[simp] theorem dlz_yzX_ne_yzB1 : yzX ≠ yzB1 := by decide
@[simp] theorem dlz_yzX_ne_yzQ2 : yzX ≠ yzQ2 := by decide
@[simp] theorem dlz_yzX_ne_yzL : yzX ≠ yzL := by decide
@[simp] theorem dlz_yzX_ne_yzY : yzX ≠ yzY := by decide
@[simp] theorem dlz_yzX_ne_yzJ : yzX ≠ yzJ := by decide
@[simp] theorem dlz_yzX_ne_yzPa : yzX ≠ yzPa := by decide
@[simp] theorem dlz_yzX_ne_yzPb : yzX ≠ yzPb := by decide
@[simp] theorem dlz_yzX_ne_yzA2 : yzX ≠ yzA2 := by decide
@[simp] theorem dlz_yzX_ne_yzB2 : yzX ≠ yzB2 := by decide
@[simp] theorem dlz_yzX_ne_yzK : yzX ≠ yzK := by decide
@[simp] theorem dlz_yzX_ne_yzV : yzX ≠ yzV := by decide
@[simp] theorem dlz_yzX_ne_lFl : yzX ≠ lFl := by decide
@[simp] theorem dlz_lFl_ne_yzX : lFl ≠ yzX := by decide
@[simp] theorem dlz_yzX_ne_lDh : yzX ≠ lDh := by decide
@[simp] theorem dlz_lDh_ne_yzX : lDh ≠ yzX := by decide
@[simp] theorem dlz_yzX_ne_lDt : yzX ≠ lDt := by decide
@[simp] theorem dlz_lDt_ne_yzX : lDt ≠ yzX := by decide
@[simp] theorem dlz_yzX_ne_lDg : yzX ≠ lDg := by decide
@[simp] theorem dlz_lDg_ne_yzX : lDg ≠ yzX := by decide
@[simp] theorem dlz_yzX_ne_lDi : yzX ≠ lDi := by decide
@[simp] theorem dlz_lDi_ne_yzX : lDi ≠ yzX := by decide
@[simp] theorem dlz_yzX_ne_lRp : yzX ≠ lRp := by decide
@[simp] theorem dlz_lRp_ne_yzX : lRp ≠ yzX := by decide
@[simp] theorem dlz_yzX_ne_lRn : yzX ≠ lRn := by decide
@[simp] theorem dlz_lRn_ne_yzX : lRn ≠ yzX := by decide
@[simp] theorem dlz_yzX_ne_lFle : yzX ≠ lFle := by decide
@[simp] theorem dlz_lFle_ne_yzX : lFle ≠ yzX := by decide
@[simp] theorem dlz_yzX_ne_lKb : yzX ≠ lKb := by decide
@[simp] theorem dlz_lKb_ne_yzX : lKb ≠ yzX := by decide
@[simp] theorem dlz_yzX_ne_lDir : yzX ≠ lDir := by decide
@[simp] theorem dlz_lDir_ne_yzX : lDir ≠ yzX := by decide
@[simp] theorem dlz_yzX_ne_lFln : yzX ≠ lFln := by decide
@[simp] theorem dlz_lFln_ne_yzX : lFln ≠ yzX := by decide
@[simp] theorem dlz_yzX_ne_lFll : yzX ≠ lFll := by decide
@[simp] theorem dlz_lFll_ne_yzX : lFll ≠ yzX := by decide
@[simp] theorem dlz_yzX_ne_lFls : yzX ≠ lFls := by decide
@[simp] theorem dlz_lFls_ne_yzX : lFls ≠ yzX := by decide
@[simp] theorem dlz_yzX_ne_kFu : yzX ≠ kFu := by decide
@[simp] theorem dlz_kFu_ne_yzX : kFu ≠ yzX := by decide
@[simp] theorem dlz_yzX_ne_kD : yzX ≠ kD := by decide
@[simp] theorem dlz_kD_ne_yzX : kD ≠ yzX := by decide
@[simp] theorem dlz_yzY_ne_yzA : yzY ≠ yzA := by decide
@[simp] theorem dlz_yzY_ne_yzB : yzY ≠ yzB := by decide
@[simp] theorem dlz_yzY_ne_yzQ : yzY ≠ yzQ := by decide
@[simp] theorem dlz_yzY_ne_yzP : yzY ≠ yzP := by decide
@[simp] theorem dlz_yzY_ne_yzA1 : yzY ≠ yzA1 := by decide
@[simp] theorem dlz_yzY_ne_yzB1 : yzY ≠ yzB1 := by decide
@[simp] theorem dlz_yzY_ne_yzQ2 : yzY ≠ yzQ2 := by decide
@[simp] theorem dlz_yzY_ne_yzL : yzY ≠ yzL := by decide
@[simp] theorem dlz_yzY_ne_yzX : yzY ≠ yzX := by decide
@[simp] theorem dlz_yzY_ne_yzJ : yzY ≠ yzJ := by decide
@[simp] theorem dlz_yzY_ne_yzPa : yzY ≠ yzPa := by decide
@[simp] theorem dlz_yzY_ne_yzPb : yzY ≠ yzPb := by decide
@[simp] theorem dlz_yzY_ne_yzA2 : yzY ≠ yzA2 := by decide
@[simp] theorem dlz_yzY_ne_yzB2 : yzY ≠ yzB2 := by decide
@[simp] theorem dlz_yzY_ne_yzK : yzY ≠ yzK := by decide
@[simp] theorem dlz_yzY_ne_yzV : yzY ≠ yzV := by decide
@[simp] theorem dlz_yzY_ne_lFl : yzY ≠ lFl := by decide
@[simp] theorem dlz_lFl_ne_yzY : lFl ≠ yzY := by decide
@[simp] theorem dlz_yzY_ne_lDh : yzY ≠ lDh := by decide
@[simp] theorem dlz_lDh_ne_yzY : lDh ≠ yzY := by decide
@[simp] theorem dlz_yzY_ne_lDt : yzY ≠ lDt := by decide
@[simp] theorem dlz_lDt_ne_yzY : lDt ≠ yzY := by decide
@[simp] theorem dlz_yzY_ne_lDg : yzY ≠ lDg := by decide
@[simp] theorem dlz_lDg_ne_yzY : lDg ≠ yzY := by decide
@[simp] theorem dlz_yzY_ne_lDi : yzY ≠ lDi := by decide
@[simp] theorem dlz_lDi_ne_yzY : lDi ≠ yzY := by decide
@[simp] theorem dlz_yzY_ne_lRp : yzY ≠ lRp := by decide
@[simp] theorem dlz_lRp_ne_yzY : lRp ≠ yzY := by decide
@[simp] theorem dlz_yzY_ne_lRn : yzY ≠ lRn := by decide
@[simp] theorem dlz_lRn_ne_yzY : lRn ≠ yzY := by decide
@[simp] theorem dlz_yzY_ne_lFle : yzY ≠ lFle := by decide
@[simp] theorem dlz_lFle_ne_yzY : lFle ≠ yzY := by decide
@[simp] theorem dlz_yzY_ne_lKb : yzY ≠ lKb := by decide
@[simp] theorem dlz_lKb_ne_yzY : lKb ≠ yzY := by decide
@[simp] theorem dlz_yzY_ne_lDir : yzY ≠ lDir := by decide
@[simp] theorem dlz_lDir_ne_yzY : lDir ≠ yzY := by decide
@[simp] theorem dlz_yzY_ne_lFln : yzY ≠ lFln := by decide
@[simp] theorem dlz_lFln_ne_yzY : lFln ≠ yzY := by decide
@[simp] theorem dlz_yzY_ne_lFll : yzY ≠ lFll := by decide
@[simp] theorem dlz_lFll_ne_yzY : lFll ≠ yzY := by decide
@[simp] theorem dlz_yzY_ne_lFls : yzY ≠ lFls := by decide
@[simp] theorem dlz_lFls_ne_yzY : lFls ≠ yzY := by decide
@[simp] theorem dlz_yzY_ne_kFu : yzY ≠ kFu := by decide
@[simp] theorem dlz_kFu_ne_yzY : kFu ≠ yzY := by decide
@[simp] theorem dlz_yzY_ne_kD : yzY ≠ kD := by decide
@[simp] theorem dlz_kD_ne_yzY : kD ≠ yzY := by decide
@[simp] theorem dlz_yzJ_ne_yzA : yzJ ≠ yzA := by decide
@[simp] theorem dlz_yzJ_ne_yzB : yzJ ≠ yzB := by decide
@[simp] theorem dlz_yzJ_ne_yzQ : yzJ ≠ yzQ := by decide
@[simp] theorem dlz_yzJ_ne_yzP : yzJ ≠ yzP := by decide
@[simp] theorem dlz_yzJ_ne_yzA1 : yzJ ≠ yzA1 := by decide
@[simp] theorem dlz_yzJ_ne_yzB1 : yzJ ≠ yzB1 := by decide
@[simp] theorem dlz_yzJ_ne_yzQ2 : yzJ ≠ yzQ2 := by decide
@[simp] theorem dlz_yzJ_ne_yzL : yzJ ≠ yzL := by decide
@[simp] theorem dlz_yzJ_ne_yzX : yzJ ≠ yzX := by decide
@[simp] theorem dlz_yzJ_ne_yzY : yzJ ≠ yzY := by decide
@[simp] theorem dlz_yzJ_ne_yzPa : yzJ ≠ yzPa := by decide
@[simp] theorem dlz_yzJ_ne_yzPb : yzJ ≠ yzPb := by decide
@[simp] theorem dlz_yzJ_ne_yzA2 : yzJ ≠ yzA2 := by decide
@[simp] theorem dlz_yzJ_ne_yzB2 : yzJ ≠ yzB2 := by decide
@[simp] theorem dlz_yzJ_ne_yzK : yzJ ≠ yzK := by decide
@[simp] theorem dlz_yzJ_ne_yzV : yzJ ≠ yzV := by decide
@[simp] theorem dlz_yzJ_ne_lFl : yzJ ≠ lFl := by decide
@[simp] theorem dlz_lFl_ne_yzJ : lFl ≠ yzJ := by decide
@[simp] theorem dlz_yzJ_ne_lDh : yzJ ≠ lDh := by decide
@[simp] theorem dlz_lDh_ne_yzJ : lDh ≠ yzJ := by decide
@[simp] theorem dlz_yzJ_ne_lDt : yzJ ≠ lDt := by decide
@[simp] theorem dlz_lDt_ne_yzJ : lDt ≠ yzJ := by decide
@[simp] theorem dlz_yzJ_ne_lDg : yzJ ≠ lDg := by decide
@[simp] theorem dlz_lDg_ne_yzJ : lDg ≠ yzJ := by decide
@[simp] theorem dlz_yzJ_ne_lDi : yzJ ≠ lDi := by decide
@[simp] theorem dlz_lDi_ne_yzJ : lDi ≠ yzJ := by decide
@[simp] theorem dlz_yzJ_ne_lRp : yzJ ≠ lRp := by decide
@[simp] theorem dlz_lRp_ne_yzJ : lRp ≠ yzJ := by decide
@[simp] theorem dlz_yzJ_ne_lRn : yzJ ≠ lRn := by decide
@[simp] theorem dlz_lRn_ne_yzJ : lRn ≠ yzJ := by decide
@[simp] theorem dlz_yzJ_ne_lFle : yzJ ≠ lFle := by decide
@[simp] theorem dlz_lFle_ne_yzJ : lFle ≠ yzJ := by decide
@[simp] theorem dlz_yzJ_ne_lKb : yzJ ≠ lKb := by decide
@[simp] theorem dlz_lKb_ne_yzJ : lKb ≠ yzJ := by decide
@[simp] theorem dlz_yzJ_ne_lDir : yzJ ≠ lDir := by decide
@[simp] theorem dlz_lDir_ne_yzJ : lDir ≠ yzJ := by decide
@[simp] theorem dlz_yzJ_ne_lFln : yzJ ≠ lFln := by decide
@[simp] theorem dlz_lFln_ne_yzJ : lFln ≠ yzJ := by decide
@[simp] theorem dlz_yzJ_ne_lFll : yzJ ≠ lFll := by decide
@[simp] theorem dlz_lFll_ne_yzJ : lFll ≠ yzJ := by decide
@[simp] theorem dlz_yzJ_ne_lFls : yzJ ≠ lFls := by decide
@[simp] theorem dlz_lFls_ne_yzJ : lFls ≠ yzJ := by decide
@[simp] theorem dlz_yzJ_ne_kFu : yzJ ≠ kFu := by decide
@[simp] theorem dlz_kFu_ne_yzJ : kFu ≠ yzJ := by decide
@[simp] theorem dlz_yzJ_ne_kD : yzJ ≠ kD := by decide
@[simp] theorem dlz_kD_ne_yzJ : kD ≠ yzJ := by decide
@[simp] theorem dlz_yzPa_ne_yzA : yzPa ≠ yzA := by decide
@[simp] theorem dlz_yzPa_ne_yzB : yzPa ≠ yzB := by decide
@[simp] theorem dlz_yzPa_ne_yzQ : yzPa ≠ yzQ := by decide
@[simp] theorem dlz_yzPa_ne_yzP : yzPa ≠ yzP := by decide
@[simp] theorem dlz_yzPa_ne_yzA1 : yzPa ≠ yzA1 := by decide
@[simp] theorem dlz_yzPa_ne_yzB1 : yzPa ≠ yzB1 := by decide
@[simp] theorem dlz_yzPa_ne_yzQ2 : yzPa ≠ yzQ2 := by decide
@[simp] theorem dlz_yzPa_ne_yzL : yzPa ≠ yzL := by decide
@[simp] theorem dlz_yzPa_ne_yzX : yzPa ≠ yzX := by decide
@[simp] theorem dlz_yzPa_ne_yzY : yzPa ≠ yzY := by decide
@[simp] theorem dlz_yzPa_ne_yzJ : yzPa ≠ yzJ := by decide
@[simp] theorem dlz_yzPa_ne_yzPb : yzPa ≠ yzPb := by decide
@[simp] theorem dlz_yzPa_ne_yzA2 : yzPa ≠ yzA2 := by decide
@[simp] theorem dlz_yzPa_ne_yzB2 : yzPa ≠ yzB2 := by decide
@[simp] theorem dlz_yzPa_ne_yzK : yzPa ≠ yzK := by decide
@[simp] theorem dlz_yzPa_ne_yzV : yzPa ≠ yzV := by decide
@[simp] theorem dlz_yzPa_ne_lFl : yzPa ≠ lFl := by decide
@[simp] theorem dlz_lFl_ne_yzPa : lFl ≠ yzPa := by decide
@[simp] theorem dlz_yzPa_ne_lDh : yzPa ≠ lDh := by decide
@[simp] theorem dlz_lDh_ne_yzPa : lDh ≠ yzPa := by decide
@[simp] theorem dlz_yzPa_ne_lDt : yzPa ≠ lDt := by decide
@[simp] theorem dlz_lDt_ne_yzPa : lDt ≠ yzPa := by decide
@[simp] theorem dlz_yzPa_ne_lDg : yzPa ≠ lDg := by decide
@[simp] theorem dlz_lDg_ne_yzPa : lDg ≠ yzPa := by decide
@[simp] theorem dlz_yzPa_ne_lDi : yzPa ≠ lDi := by decide
@[simp] theorem dlz_lDi_ne_yzPa : lDi ≠ yzPa := by decide
@[simp] theorem dlz_yzPa_ne_lRp : yzPa ≠ lRp := by decide
@[simp] theorem dlz_lRp_ne_yzPa : lRp ≠ yzPa := by decide
@[simp] theorem dlz_yzPa_ne_lRn : yzPa ≠ lRn := by decide
@[simp] theorem dlz_lRn_ne_yzPa : lRn ≠ yzPa := by decide
@[simp] theorem dlz_yzPa_ne_lFle : yzPa ≠ lFle := by decide
@[simp] theorem dlz_lFle_ne_yzPa : lFle ≠ yzPa := by decide
@[simp] theorem dlz_yzPa_ne_lKb : yzPa ≠ lKb := by decide
@[simp] theorem dlz_lKb_ne_yzPa : lKb ≠ yzPa := by decide
@[simp] theorem dlz_yzPa_ne_lDir : yzPa ≠ lDir := by decide
@[simp] theorem dlz_lDir_ne_yzPa : lDir ≠ yzPa := by decide
@[simp] theorem dlz_yzPa_ne_lFln : yzPa ≠ lFln := by decide
@[simp] theorem dlz_lFln_ne_yzPa : lFln ≠ yzPa := by decide
@[simp] theorem dlz_yzPa_ne_lFll : yzPa ≠ lFll := by decide
@[simp] theorem dlz_lFll_ne_yzPa : lFll ≠ yzPa := by decide
@[simp] theorem dlz_yzPa_ne_lFls : yzPa ≠ lFls := by decide
@[simp] theorem dlz_lFls_ne_yzPa : lFls ≠ yzPa := by decide
@[simp] theorem dlz_yzPa_ne_kFu : yzPa ≠ kFu := by decide
@[simp] theorem dlz_kFu_ne_yzPa : kFu ≠ yzPa := by decide
@[simp] theorem dlz_yzPa_ne_kD : yzPa ≠ kD := by decide
@[simp] theorem dlz_kD_ne_yzPa : kD ≠ yzPa := by decide
@[simp] theorem dlz_yzPb_ne_yzA : yzPb ≠ yzA := by decide
@[simp] theorem dlz_yzPb_ne_yzB : yzPb ≠ yzB := by decide
@[simp] theorem dlz_yzPb_ne_yzQ : yzPb ≠ yzQ := by decide
@[simp] theorem dlz_yzPb_ne_yzP : yzPb ≠ yzP := by decide
@[simp] theorem dlz_yzPb_ne_yzA1 : yzPb ≠ yzA1 := by decide
@[simp] theorem dlz_yzPb_ne_yzB1 : yzPb ≠ yzB1 := by decide
@[simp] theorem dlz_yzPb_ne_yzQ2 : yzPb ≠ yzQ2 := by decide
@[simp] theorem dlz_yzPb_ne_yzL : yzPb ≠ yzL := by decide
@[simp] theorem dlz_yzPb_ne_yzX : yzPb ≠ yzX := by decide
@[simp] theorem dlz_yzPb_ne_yzY : yzPb ≠ yzY := by decide
@[simp] theorem dlz_yzPb_ne_yzJ : yzPb ≠ yzJ := by decide
@[simp] theorem dlz_yzPb_ne_yzPa : yzPb ≠ yzPa := by decide
@[simp] theorem dlz_yzPb_ne_yzA2 : yzPb ≠ yzA2 := by decide
@[simp] theorem dlz_yzPb_ne_yzB2 : yzPb ≠ yzB2 := by decide
@[simp] theorem dlz_yzPb_ne_yzK : yzPb ≠ yzK := by decide
@[simp] theorem dlz_yzPb_ne_yzV : yzPb ≠ yzV := by decide
@[simp] theorem dlz_yzPb_ne_lFl : yzPb ≠ lFl := by decide
@[simp] theorem dlz_lFl_ne_yzPb : lFl ≠ yzPb := by decide
@[simp] theorem dlz_yzPb_ne_lDh : yzPb ≠ lDh := by decide
@[simp] theorem dlz_lDh_ne_yzPb : lDh ≠ yzPb := by decide
@[simp] theorem dlz_yzPb_ne_lDt : yzPb ≠ lDt := by decide
@[simp] theorem dlz_lDt_ne_yzPb : lDt ≠ yzPb := by decide
@[simp] theorem dlz_yzPb_ne_lDg : yzPb ≠ lDg := by decide
@[simp] theorem dlz_lDg_ne_yzPb : lDg ≠ yzPb := by decide
@[simp] theorem dlz_yzPb_ne_lDi : yzPb ≠ lDi := by decide
@[simp] theorem dlz_lDi_ne_yzPb : lDi ≠ yzPb := by decide
@[simp] theorem dlz_yzPb_ne_lRp : yzPb ≠ lRp := by decide
@[simp] theorem dlz_lRp_ne_yzPb : lRp ≠ yzPb := by decide
@[simp] theorem dlz_yzPb_ne_lRn : yzPb ≠ lRn := by decide
@[simp] theorem dlz_lRn_ne_yzPb : lRn ≠ yzPb := by decide
@[simp] theorem dlz_yzPb_ne_lFle : yzPb ≠ lFle := by decide
@[simp] theorem dlz_lFle_ne_yzPb : lFle ≠ yzPb := by decide
@[simp] theorem dlz_yzPb_ne_lKb : yzPb ≠ lKb := by decide
@[simp] theorem dlz_lKb_ne_yzPb : lKb ≠ yzPb := by decide
@[simp] theorem dlz_yzPb_ne_lDir : yzPb ≠ lDir := by decide
@[simp] theorem dlz_lDir_ne_yzPb : lDir ≠ yzPb := by decide
@[simp] theorem dlz_yzPb_ne_lFln : yzPb ≠ lFln := by decide
@[simp] theorem dlz_lFln_ne_yzPb : lFln ≠ yzPb := by decide
@[simp] theorem dlz_yzPb_ne_lFll : yzPb ≠ lFll := by decide
@[simp] theorem dlz_lFll_ne_yzPb : lFll ≠ yzPb := by decide
@[simp] theorem dlz_yzPb_ne_lFls : yzPb ≠ lFls := by decide
@[simp] theorem dlz_lFls_ne_yzPb : lFls ≠ yzPb := by decide
@[simp] theorem dlz_yzPb_ne_kFu : yzPb ≠ kFu := by decide
@[simp] theorem dlz_kFu_ne_yzPb : kFu ≠ yzPb := by decide
@[simp] theorem dlz_yzPb_ne_kD : yzPb ≠ kD := by decide
@[simp] theorem dlz_kD_ne_yzPb : kD ≠ yzPb := by decide
@[simp] theorem dlz_yzA2_ne_yzA : yzA2 ≠ yzA := by decide
@[simp] theorem dlz_yzA2_ne_yzB : yzA2 ≠ yzB := by decide
@[simp] theorem dlz_yzA2_ne_yzQ : yzA2 ≠ yzQ := by decide
@[simp] theorem dlz_yzA2_ne_yzP : yzA2 ≠ yzP := by decide
@[simp] theorem dlz_yzA2_ne_yzA1 : yzA2 ≠ yzA1 := by decide
@[simp] theorem dlz_yzA2_ne_yzB1 : yzA2 ≠ yzB1 := by decide
@[simp] theorem dlz_yzA2_ne_yzQ2 : yzA2 ≠ yzQ2 := by decide
@[simp] theorem dlz_yzA2_ne_yzL : yzA2 ≠ yzL := by decide
@[simp] theorem dlz_yzA2_ne_yzX : yzA2 ≠ yzX := by decide
@[simp] theorem dlz_yzA2_ne_yzY : yzA2 ≠ yzY := by decide
@[simp] theorem dlz_yzA2_ne_yzJ : yzA2 ≠ yzJ := by decide
@[simp] theorem dlz_yzA2_ne_yzPa : yzA2 ≠ yzPa := by decide
@[simp] theorem dlz_yzA2_ne_yzPb : yzA2 ≠ yzPb := by decide
@[simp] theorem dlz_yzA2_ne_yzB2 : yzA2 ≠ yzB2 := by decide
@[simp] theorem dlz_yzA2_ne_yzK : yzA2 ≠ yzK := by decide
@[simp] theorem dlz_yzA2_ne_yzV : yzA2 ≠ yzV := by decide
@[simp] theorem dlz_yzA2_ne_lFl : yzA2 ≠ lFl := by decide
@[simp] theorem dlz_lFl_ne_yzA2 : lFl ≠ yzA2 := by decide
@[simp] theorem dlz_yzA2_ne_lDh : yzA2 ≠ lDh := by decide
@[simp] theorem dlz_lDh_ne_yzA2 : lDh ≠ yzA2 := by decide
@[simp] theorem dlz_yzA2_ne_lDt : yzA2 ≠ lDt := by decide
@[simp] theorem dlz_lDt_ne_yzA2 : lDt ≠ yzA2 := by decide
@[simp] theorem dlz_yzA2_ne_lDg : yzA2 ≠ lDg := by decide
@[simp] theorem dlz_lDg_ne_yzA2 : lDg ≠ yzA2 := by decide
@[simp] theorem dlz_yzA2_ne_lDi : yzA2 ≠ lDi := by decide
@[simp] theorem dlz_lDi_ne_yzA2 : lDi ≠ yzA2 := by decide
@[simp] theorem dlz_yzA2_ne_lRp : yzA2 ≠ lRp := by decide
@[simp] theorem dlz_lRp_ne_yzA2 : lRp ≠ yzA2 := by decide
@[simp] theorem dlz_yzA2_ne_lRn : yzA2 ≠ lRn := by decide
@[simp] theorem dlz_lRn_ne_yzA2 : lRn ≠ yzA2 := by decide
@[simp] theorem dlz_yzA2_ne_lFle : yzA2 ≠ lFle := by decide
@[simp] theorem dlz_lFle_ne_yzA2 : lFle ≠ yzA2 := by decide
@[simp] theorem dlz_yzA2_ne_lKb : yzA2 ≠ lKb := by decide
@[simp] theorem dlz_lKb_ne_yzA2 : lKb ≠ yzA2 := by decide
@[simp] theorem dlz_yzA2_ne_lDir : yzA2 ≠ lDir := by decide
@[simp] theorem dlz_lDir_ne_yzA2 : lDir ≠ yzA2 := by decide
@[simp] theorem dlz_yzA2_ne_lFln : yzA2 ≠ lFln := by decide
@[simp] theorem dlz_lFln_ne_yzA2 : lFln ≠ yzA2 := by decide
@[simp] theorem dlz_yzA2_ne_lFll : yzA2 ≠ lFll := by decide
@[simp] theorem dlz_lFll_ne_yzA2 : lFll ≠ yzA2 := by decide
@[simp] theorem dlz_yzA2_ne_lFls : yzA2 ≠ lFls := by decide
@[simp] theorem dlz_lFls_ne_yzA2 : lFls ≠ yzA2 := by decide
@[simp] theorem dlz_yzA2_ne_kFu : yzA2 ≠ kFu := by decide
@[simp] theorem dlz_kFu_ne_yzA2 : kFu ≠ yzA2 := by decide
@[simp] theorem dlz_yzA2_ne_kD : yzA2 ≠ kD := by decide
@[simp] theorem dlz_kD_ne_yzA2 : kD ≠ yzA2 := by decide
@[simp] theorem dlz_yzB2_ne_yzA : yzB2 ≠ yzA := by decide
@[simp] theorem dlz_yzB2_ne_yzB : yzB2 ≠ yzB := by decide
@[simp] theorem dlz_yzB2_ne_yzQ : yzB2 ≠ yzQ := by decide
@[simp] theorem dlz_yzB2_ne_yzP : yzB2 ≠ yzP := by decide
@[simp] theorem dlz_yzB2_ne_yzA1 : yzB2 ≠ yzA1 := by decide
@[simp] theorem dlz_yzB2_ne_yzB1 : yzB2 ≠ yzB1 := by decide
@[simp] theorem dlz_yzB2_ne_yzQ2 : yzB2 ≠ yzQ2 := by decide
@[simp] theorem dlz_yzB2_ne_yzL : yzB2 ≠ yzL := by decide
@[simp] theorem dlz_yzB2_ne_yzX : yzB2 ≠ yzX := by decide
@[simp] theorem dlz_yzB2_ne_yzY : yzB2 ≠ yzY := by decide
@[simp] theorem dlz_yzB2_ne_yzJ : yzB2 ≠ yzJ := by decide
@[simp] theorem dlz_yzB2_ne_yzPa : yzB2 ≠ yzPa := by decide
@[simp] theorem dlz_yzB2_ne_yzPb : yzB2 ≠ yzPb := by decide
@[simp] theorem dlz_yzB2_ne_yzA2 : yzB2 ≠ yzA2 := by decide
@[simp] theorem dlz_yzB2_ne_yzK : yzB2 ≠ yzK := by decide
@[simp] theorem dlz_yzB2_ne_yzV : yzB2 ≠ yzV := by decide
@[simp] theorem dlz_yzB2_ne_lFl : yzB2 ≠ lFl := by decide
@[simp] theorem dlz_lFl_ne_yzB2 : lFl ≠ yzB2 := by decide
@[simp] theorem dlz_yzB2_ne_lDh : yzB2 ≠ lDh := by decide
@[simp] theorem dlz_lDh_ne_yzB2 : lDh ≠ yzB2 := by decide
@[simp] theorem dlz_yzB2_ne_lDt : yzB2 ≠ lDt := by decide
@[simp] theorem dlz_lDt_ne_yzB2 : lDt ≠ yzB2 := by decide
@[simp] theorem dlz_yzB2_ne_lDg : yzB2 ≠ lDg := by decide
@[simp] theorem dlz_lDg_ne_yzB2 : lDg ≠ yzB2 := by decide
@[simp] theorem dlz_yzB2_ne_lDi : yzB2 ≠ lDi := by decide
@[simp] theorem dlz_lDi_ne_yzB2 : lDi ≠ yzB2 := by decide
@[simp] theorem dlz_yzB2_ne_lRp : yzB2 ≠ lRp := by decide
@[simp] theorem dlz_lRp_ne_yzB2 : lRp ≠ yzB2 := by decide
@[simp] theorem dlz_yzB2_ne_lRn : yzB2 ≠ lRn := by decide
@[simp] theorem dlz_lRn_ne_yzB2 : lRn ≠ yzB2 := by decide
@[simp] theorem dlz_yzB2_ne_lFle : yzB2 ≠ lFle := by decide
@[simp] theorem dlz_lFle_ne_yzB2 : lFle ≠ yzB2 := by decide
@[simp] theorem dlz_yzB2_ne_lKb : yzB2 ≠ lKb := by decide
@[simp] theorem dlz_lKb_ne_yzB2 : lKb ≠ yzB2 := by decide
@[simp] theorem dlz_yzB2_ne_lDir : yzB2 ≠ lDir := by decide
@[simp] theorem dlz_lDir_ne_yzB2 : lDir ≠ yzB2 := by decide
@[simp] theorem dlz_yzB2_ne_lFln : yzB2 ≠ lFln := by decide
@[simp] theorem dlz_lFln_ne_yzB2 : lFln ≠ yzB2 := by decide
@[simp] theorem dlz_yzB2_ne_lFll : yzB2 ≠ lFll := by decide
@[simp] theorem dlz_lFll_ne_yzB2 : lFll ≠ yzB2 := by decide
@[simp] theorem dlz_yzB2_ne_lFls : yzB2 ≠ lFls := by decide
@[simp] theorem dlz_lFls_ne_yzB2 : lFls ≠ yzB2 := by decide
@[simp] theorem dlz_yzB2_ne_kFu : yzB2 ≠ kFu := by decide
@[simp] theorem dlz_kFu_ne_yzB2 : kFu ≠ yzB2 := by decide
@[simp] theorem dlz_yzB2_ne_kD : yzB2 ≠ kD := by decide
@[simp] theorem dlz_kD_ne_yzB2 : kD ≠ yzB2 := by decide
@[simp] theorem dlz_yzK_ne_yzA : yzK ≠ yzA := by decide
@[simp] theorem dlz_yzK_ne_yzB : yzK ≠ yzB := by decide
@[simp] theorem dlz_yzK_ne_yzQ : yzK ≠ yzQ := by decide
@[simp] theorem dlz_yzK_ne_yzP : yzK ≠ yzP := by decide
@[simp] theorem dlz_yzK_ne_yzA1 : yzK ≠ yzA1 := by decide
@[simp] theorem dlz_yzK_ne_yzB1 : yzK ≠ yzB1 := by decide
@[simp] theorem dlz_yzK_ne_yzQ2 : yzK ≠ yzQ2 := by decide
@[simp] theorem dlz_yzK_ne_yzL : yzK ≠ yzL := by decide
@[simp] theorem dlz_yzK_ne_yzX : yzK ≠ yzX := by decide
@[simp] theorem dlz_yzK_ne_yzY : yzK ≠ yzY := by decide
@[simp] theorem dlz_yzK_ne_yzJ : yzK ≠ yzJ := by decide
@[simp] theorem dlz_yzK_ne_yzPa : yzK ≠ yzPa := by decide
@[simp] theorem dlz_yzK_ne_yzPb : yzK ≠ yzPb := by decide
@[simp] theorem dlz_yzK_ne_yzA2 : yzK ≠ yzA2 := by decide
@[simp] theorem dlz_yzK_ne_yzB2 : yzK ≠ yzB2 := by decide
@[simp] theorem dlz_yzK_ne_yzV : yzK ≠ yzV := by decide
@[simp] theorem dlz_yzK_ne_lFl : yzK ≠ lFl := by decide
@[simp] theorem dlz_lFl_ne_yzK : lFl ≠ yzK := by decide
@[simp] theorem dlz_yzK_ne_lDh : yzK ≠ lDh := by decide
@[simp] theorem dlz_lDh_ne_yzK : lDh ≠ yzK := by decide
@[simp] theorem dlz_yzK_ne_lDt : yzK ≠ lDt := by decide
@[simp] theorem dlz_lDt_ne_yzK : lDt ≠ yzK := by decide
@[simp] theorem dlz_yzK_ne_lDg : yzK ≠ lDg := by decide
@[simp] theorem dlz_lDg_ne_yzK : lDg ≠ yzK := by decide
@[simp] theorem dlz_yzK_ne_lDi : yzK ≠ lDi := by decide
@[simp] theorem dlz_lDi_ne_yzK : lDi ≠ yzK := by decide
@[simp] theorem dlz_yzK_ne_lRp : yzK ≠ lRp := by decide
@[simp] theorem dlz_lRp_ne_yzK : lRp ≠ yzK := by decide
@[simp] theorem dlz_yzK_ne_lRn : yzK ≠ lRn := by decide
@[simp] theorem dlz_lRn_ne_yzK : lRn ≠ yzK := by decide
@[simp] theorem dlz_yzK_ne_lFle : yzK ≠ lFle := by decide
@[simp] theorem dlz_lFle_ne_yzK : lFle ≠ yzK := by decide
@[simp] theorem dlz_yzK_ne_lKb : yzK ≠ lKb := by decide
@[simp] theorem dlz_lKb_ne_yzK : lKb ≠ yzK := by decide
@[simp] theorem dlz_yzK_ne_lDir : yzK ≠ lDir := by decide
@[simp] theorem dlz_lDir_ne_yzK : lDir ≠ yzK := by decide
@[simp] theorem dlz_yzK_ne_lFln : yzK ≠ lFln := by decide
@[simp] theorem dlz_lFln_ne_yzK : lFln ≠ yzK := by decide
@[simp] theorem dlz_yzK_ne_lFll : yzK ≠ lFll := by decide
@[simp] theorem dlz_lFll_ne_yzK : lFll ≠ yzK := by decide
@[simp] theorem dlz_yzK_ne_lFls : yzK ≠ lFls := by decide
@[simp] theorem dlz_lFls_ne_yzK : lFls ≠ yzK := by decide
@[simp] theorem dlz_yzK_ne_kFu : yzK ≠ kFu := by decide
@[simp] theorem dlz_kFu_ne_yzK : kFu ≠ yzK := by decide
@[simp] theorem dlz_yzK_ne_kD : yzK ≠ kD := by decide
@[simp] theorem dlz_kD_ne_yzK : kD ≠ yzK := by decide
@[simp] theorem dlz_yzV_ne_yzA : yzV ≠ yzA := by decide
@[simp] theorem dlz_yzV_ne_yzB : yzV ≠ yzB := by decide
@[simp] theorem dlz_yzV_ne_yzQ : yzV ≠ yzQ := by decide
@[simp] theorem dlz_yzV_ne_yzP : yzV ≠ yzP := by decide
@[simp] theorem dlz_yzV_ne_yzA1 : yzV ≠ yzA1 := by decide
@[simp] theorem dlz_yzV_ne_yzB1 : yzV ≠ yzB1 := by decide
@[simp] theorem dlz_yzV_ne_yzQ2 : yzV ≠ yzQ2 := by decide
@[simp] theorem dlz_yzV_ne_yzL : yzV ≠ yzL := by decide
@[simp] theorem dlz_yzV_ne_yzX : yzV ≠ yzX := by decide
@[simp] theorem dlz_yzV_ne_yzY : yzV ≠ yzY := by decide
@[simp] theorem dlz_yzV_ne_yzJ : yzV ≠ yzJ := by decide
@[simp] theorem dlz_yzV_ne_yzPa : yzV ≠ yzPa := by decide
@[simp] theorem dlz_yzV_ne_yzPb : yzV ≠ yzPb := by decide
@[simp] theorem dlz_yzV_ne_yzA2 : yzV ≠ yzA2 := by decide
@[simp] theorem dlz_yzV_ne_yzB2 : yzV ≠ yzB2 := by decide
@[simp] theorem dlz_yzV_ne_yzK : yzV ≠ yzK := by decide
@[simp] theorem dlz_yzV_ne_lFl : yzV ≠ lFl := by decide
@[simp] theorem dlz_lFl_ne_yzV : lFl ≠ yzV := by decide
@[simp] theorem dlz_yzV_ne_lDh : yzV ≠ lDh := by decide
@[simp] theorem dlz_lDh_ne_yzV : lDh ≠ yzV := by decide
@[simp] theorem dlz_yzV_ne_lDt : yzV ≠ lDt := by decide
@[simp] theorem dlz_lDt_ne_yzV : lDt ≠ yzV := by decide
@[simp] theorem dlz_yzV_ne_lDg : yzV ≠ lDg := by decide
@[simp] theorem dlz_lDg_ne_yzV : lDg ≠ yzV := by decide
@[simp] theorem dlz_yzV_ne_lDi : yzV ≠ lDi := by decide
@[simp] theorem dlz_lDi_ne_yzV : lDi ≠ yzV := by decide
@[simp] theorem dlz_yzV_ne_lRp : yzV ≠ lRp := by decide
@[simp] theorem dlz_lRp_ne_yzV : lRp ≠ yzV := by decide
@[simp] theorem dlz_yzV_ne_lRn : yzV ≠ lRn := by decide
@[simp] theorem dlz_lRn_ne_yzV : lRn ≠ yzV := by decide
@[simp] theorem dlz_yzV_ne_lFle : yzV ≠ lFle := by decide
@[simp] theorem dlz_lFle_ne_yzV : lFle ≠ yzV := by decide
@[simp] theorem dlz_yzV_ne_lKb : yzV ≠ lKb := by decide
@[simp] theorem dlz_lKb_ne_yzV : lKb ≠ yzV := by decide
@[simp] theorem dlz_yzV_ne_lDir : yzV ≠ lDir := by decide
@[simp] theorem dlz_lDir_ne_yzV : lDir ≠ yzV := by decide
@[simp] theorem dlz_yzV_ne_lFln : yzV ≠ lFln := by decide
@[simp] theorem dlz_lFln_ne_yzV : lFln ≠ yzV := by decide
@[simp] theorem dlz_yzV_ne_lFll : yzV ≠ lFll := by decide
@[simp] theorem dlz_lFll_ne_yzV : lFll ≠ yzV := by decide
@[simp] theorem dlz_yzV_ne_lFls : yzV ≠ lFls := by decide
@[simp] theorem dlz_lFls_ne_yzV : lFls ≠ yzV := by decide
@[simp] theorem dlz_yzV_ne_kFu : yzV ≠ kFu := by decide
@[simp] theorem dlz_kFu_ne_yzV : kFu ≠ yzV := by decide
@[simp] theorem dlz_yzV_ne_kD : yzV ≠ kD := by decide
@[simp] theorem dlz_kD_ne_yzV : kD ≠ yzV := by decide

def yzParams : List MlS := [kFu, kD, yzA, yzB]
def yzLocals : List MlS := [yzQ, yzP, yzA1, yzB1, yzQ2, yzL, yzX, yzY, yzJ, yzPa, yzPb, yzA2, yzB2, yzK, yzV]
def yzBody (v : Bool) (C : Ctx) : ProgHOL 64 := prologue yzLocals (.seq (.call (some (some (.local, yzQ), none)) fQd [(vv kFu), (vv kD), (vv yzA), (vv yzB)]) (.ite (.cmp .notEqual (vv yzQ) (.const 0)) (.return (.op .sub [(vv yzQ), (.const 1)])) (.seq (.call (some (some (.local, yzP), none)) fPri [(vv kFu), (vv kD), (vv yzA), (vv yzB)]) (.ite (vv yzP) (.return (.const 1)) (.seq (.call (some (some (.local, yzA1), none)) fWC [(vv kFu), (.const 1), (vv kD), (vv yzA)]) (.seq (.call (some (some (.local, yzB1), none)) fWC [(vv kFu), (.const 1), (vv kD), (vv yzB)]) (.seq (.call (some (some (.local, yzQ2), none)) fQd [(vv kFu), (vv kD), (vv yzA1), (vv yzB1)]) (.ite (.cmp .notEqual (vv yzQ2) (.const 0)) (.return (.op .sub [(vv yzQ2), (.const 1)])) (.seq (.call (some (some (.local, yzL), none)) fLdr [(vv kFu), (vv kD), (.const (BitVec.ofNat 64 defeqLoopFuel)), (vv yzA1), (vv yzB1)]) (.ite (.cmp .equal (vv yzL) (.const 0)) (.return (.const 0)) (.ite (.cmp .equal (vv yzL) (.const 1)) (.return (.const 1)) (.seq (.assign .local yzX (.load .one (vv yzL))) (.seq (.assign .local yzY (.load .one (.op .add [(vv yzL), (.const 8)]))) (.seq (.call (some (some (.local, yzJ), none)) fPpr [(vv kFu), (vv kD), (vv yzX), (vv yzY)]) (.ite (vv yzJ) (.return (.const 1)) (.seq (.call (some (some (.local, yzPa), none)) fHp [(vv yzX)]) (.seq (.call (some (some (.local, yzPb), none)) fHp [(vv yzY)]) (.ite (.op .or [(vv yzPa), (vv yzPb)]) (.seq (.call (some (some (.local, yzA2), none)) fWC [(vv kFu), (.const 0), (vv kD), (vv yzX)]) (.seq (.call (some (some (.local, yzB2), none)) fWC [(vv kFu), (.const 0), (vv kD), (vv yzY)]) (.ite (.op .and [(.cmp .equal (vv yzA2) (vv yzX)), (.cmp .equal (vv yzB2) (vv yzY))]) (.seq (.call (some (some (.local, yzK), none)) fDk [(vv kFu), (vv kD), (vv yzX), (vv yzY)]) (.return (vv yzK))) (.seq (.call (some (some (.local, yzV), none)) fD [(vv kFu), (vv kD), (vv yzA2), (vv yzB2)]) (.return (vv yzV)))))) (.seq (.call (some (some (.local, yzK), none)) fDk [(vv kFu), (vv kD), (vv yzX), (vv yzY)]) (.return (vv yzK)))))))))))))))))))))

structure YzCodes (C : Ctx) (v : Bool) (pB : ProgHOL 64) (vv : Bool) : Prop where
  qd : C.code.lookup fQd = some (qdParams.map (fun p => (p, ShapeHOL.one)), qdBody C, .one)
  pri : C.code.lookup fPri = some (priParams.map (fun p => (p, ShapeHOL.one)), pB, .one)
  wc : C.code.lookup fWC = some (wcParams.map (fun p => (p, ShapeHOL.one)), wcE, .one)
  ldr : C.code.lookup fLdr = some (ldrParams.map (fun p => (p, ShapeHOL.one)), ldrBody v C, .one)
  dj : C.code.lookup fPpr = some (djParams.map (fun p => (p, ShapeHOL.one)), djBody vv C, .one)
  hp : C.code.lookup fHp = some ([hpE].map (fun p => (p, ShapeHOL.one)), hpBody, .one)
  dk : C.code.lookup fDk = some (dkParams.map (fun p => (p, ShapeHOL.one)), dkBody C, .one)
  d : C.code.lookup fD = some (dParams.map (fun p => (p, ShapeHOL.one)), dE C, .one)

section
variable {σ : Type}

theorem yz_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) (hok : CtxOK C) (v : Bool) (pB : ProgHOL 64)
    (hc : YzCodes C v pB mode.verifiedChecks) (Q : AState → Prop) (d : Nat)
    (hQqd : ∀ s1 a b r s2, Q s1 → quickDefEq mode (knot mode C n) d a b s1 = .ok (r, s2) → Q s2)
    (hQpri : ∀ s1 a b r s2, Q s1 → propIrrel (knot mode C n) C.fe d a b s1 = .ok (r, s2) → Q s2)
    (hQwc : ∀ s1 c e r s2, Q s1 → (knot mode C n).whnfCore c d e s1 = .ok (r, s2) → Q s2)
    (hQldr : ∀ s1 a b r s2, Q s1 → lazyDeltaReduction mode v (knot mode C n) C.fe d defeqLoopFuel a b s1 = .ok (r, s2) → Q s2)
    (hQdj : ∀ s1 a b r s2, Q s1 → defeqProjPair mode (knot mode C n) C.fe d a b s1 = .ok (r, s2) → Q s2)
    (hQhp : ∀ s1 e r s2, Q s1 → headIsProj e s1 = .ok (r, s2) → Q s2)
    (hQdk : ∀ s1 a b r s2, Q s1 → defeqStuck mode (knot mode C n) C.fe d a b s1 = .ok (r, s2) → Q s2)
    (hQd : ∀ s1 a b r s2, Q s1 → (knot mode C n).defeq d a b s1 = .ok (r, s2) → Q s2)
    (hQD : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ a b, SpecR (σ := σ) (Pre (ctxH C H) s1 (qdParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d,
      Enc.idxW a, Enc.idxW b])) (qdBody C) s1 (quickDefEq mode (knot mode C n) d a b) (PostOBH (ctxH C H)))
    (hPRI : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ a b, SpecR (σ := σ) (Pre (ctxH C H) s1 (priParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d,
      Enc.idxW a, Enc.idxW b])) pB s1 (propIrrel (knot mode C n) C.fe d a b) (PostB (ctxH C H)))
    (hWC : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ c e, Callee (σ := σ) (ctxH C H) wcParams
      [BitVec.ofNat 64 n, boolW c, BitVec.ofNat 64 d, Enc.idxW e] wcE s1 ((knot mode C n).whnfCore c d e)
      (PostK (ctxH C H)))
    (hLDR : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ a b, SpecR (σ := σ) (Pre (ctxH C H) s1 (ldrParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d,
      BitVec.ofNat 64 defeqLoopFuel, Enc.idxW a, Enc.idxW b])) (ldrBody v C) s1
      (lazyDeltaReduction mode v (knot mode C n) C.fe d defeqLoopFuel a b) (PostLR (ctxH C H)))
    (hDJ : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ a b, SpecR (σ := σ) (Pre (ctxH C H) s1 (djParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d,
      Enc.idxW a, Enc.idxW b])) (djBody mode.verifiedChecks C) s1 (defeqProjPair mode (knot mode C n) C.fe d a b)
      (PostB (ctxH C H)))
    (hHP : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ e, SpecR (σ := σ) (Pre (ctxH C H) s1 ([hpE].zip [Enc.idxW e])) hpBody s1 (headIsProj e)
      (PostB (ctxH C H)))
    (hDK : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ a b, SpecR (σ := σ) (Pre (ctxH C H) s1 (dkParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d,
      Enc.idxW a, Enc.idxW b])) (dkBody C) s1 (defeqStuck mode (knot mode C n) C.fe d a b) (PostB (ctxH C H)))
    (hD : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ a b, Callee (σ := σ) (ctxH C H) dParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (dE C) s1 ((knot mode C n).defeq d a b)
      (PostB (ctxH C H))) :
    ∀ (H : List (BitVec 64)) (s : AState) (a b : EIdx), C.H <+: H → Q s →
      SpecR (σ := σ) (Pre (ctxH C H) s (yzParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b]))
        (yzBody v C) s (defeqLazy mode v (knot mode C n) C.fe d a b) (PostB (ctxH C H)) := by
  intro H s a b hpH hq
  refine specR_prologue (postB_locals _) (Knot.params_none _ yzLocals yzParams _ (by decide) (by decide)) ?_
  unfold defeqLazy
  refine specR_callNIH (C := ctxH C H) yzQ fQd qdParams [vv kFu, vv kD, vv yzA, vv yzB] (qdBody C)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (by decide) rfl (by decide) hc.qd
    ⟨by simp +decide [Env.get, yzParams, ctxEnv], by simp +decide [Env.get, yzParams, ctxEnv], by simp +decide [Env.get, yzParams, ctxEnv], by simp +decide [Env.get, yzParams, ctxEnv], trivial⟩
    (fun r_ w s' st => quickDefEq mode (knot mode C n) d a b s = .ok (r_, s') ∧ PostOBH (ctxH C H) r_ w s' st) (fun r_ w s' H' => w = LLeq.obW r_ ∧ quickDefEq mode (knot mode C n) d a b s = .ok (r_, s'))
    (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu qdParams _ rfl hlk) (hQD H s hpH hq a b)))
    (fun o w1 s1 H1 hp1 ⟨hw1, hrun1⟩ => ?_)
  have hq1 := hQqd s a b o s1 hq hrun1
  have hpa1 : C.H <+: H1 := hpH.trans hp1
  have hb1 : H <+: H1 := (List.prefix_refl _).trans hp1
  subst hw1
  rcases o with _ | vo
  swap
  · have hne : LLeq.obW (some vo) ≠ 0 := by cases vo <;> decide
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact specR_returnI _ (boolW vo) (by simp [sev]; exact obW_sub1 vo) (fun t ht => ⟨H1, hb1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 0 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
  try dsimp only
  refine specR_callNIH (C := ctxH C H1) yzP fPri priParams [vv kFu, vv kD, vv yzA, vv yzB] pB
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (by decide) rfl (by decide) hc.pri
    ⟨by simp +decide [Env.get, yzParams, ctxEnv], by simp +decide [Env.get, yzParams, ctxEnv], by simp +decide [Env.get, yzParams, ctxEnv], by simp +decide [Env.get, yzParams, ctxEnv], trivial⟩
    (fun r_ w s' st => propIrrel (knot mode C n) C.fe d a b s1 = .ok (r_, s') ∧ PostB (ctxH C H1) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ propIrrel (knot mode C n) C.fe d a b s1 = .ok (r_, s'))
    (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu priParams _ rfl hlk) (hPRI H1 s1 hpa1 hq1 a b)))
    (fun pp w2 s2 H2 hp2 ⟨hw2, hrun2⟩ => ?_)
  have hq2 := hQpri s1 a b pp s2 hq1 hrun2
  have hpa2 : C.H <+: H2 := hpa1.trans hp2
  have hb2 : H <+: H2 := hb1.trans hp2
  subst hw2
  cases pp
  swap
  · refine specR_ifI _ 1 (by simp [boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [↓reduceIte]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H2, hb2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 0 (by simp [boolW]) (fun h => absurd rfl h) (fun _ => ?_)
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine specR_callNIH (C := ctxH C H2) yzA1 fWC wcParams [vv kFu, .const 1, vv kD, vv yzA] wcE
    [BitVec.ofNat 64 n, boolW true, BitVec.ofNat 64 d, Enc.idxW a] (by decide) rfl (by decide) hc.wc
    ⟨by simp +decide [Env.get, yzParams, ctxEnv], rfl, by simp +decide [Env.get, yzParams, ctxEnv], by simp +decide [Env.get, yzParams, ctxEnv], trivial⟩
    (fun r_ w s' st => (knot mode C n).whnfCore true d a s2 = .ok (r_, s') ∧ PostK (ctxH C H2) r_ w s' st) (fun r_ w s' H' => w = Enc.idxW r_ ∧ (knot mode C n).whnfCore true d a s2 = .ok (r_, s'))
    (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (hWC H2 s2 hpa2 hq2 true a u hu (fun i hi _ => hlk i (by omega))))
    (fun a1 w3 s3 H3 hp3 ⟨hw3, hrun3⟩ => ?_)
  have hq3 := hQwc s2 true a a1 s3 hq2 hrun3
  have hpa3 : C.H <+: H3 := hpa2.trans hp3
  have hb3 : H <+: H3 := hb2.trans hp3
  subst hw3
  refine specR_callNIH (C := ctxH C H3) yzB1 fWC wcParams [vv kFu, .const 1, vv kD, vv yzB] wcE
    [BitVec.ofNat 64 n, boolW true, BitVec.ofNat 64 d, Enc.idxW b] (by decide) rfl (by decide) hc.wc
    ⟨by simp +decide [Env.get, yzParams, ctxEnv], rfl, by simp +decide [Env.get, yzParams, ctxEnv], by simp +decide [Env.get, yzParams, ctxEnv], trivial⟩
    (fun r_ w s' st => (knot mode C n).whnfCore true d b s3 = .ok (r_, s') ∧ PostK (ctxH C H3) r_ w s' st) (fun r_ w s' H' => w = Enc.idxW r_ ∧ (knot mode C n).whnfCore true d b s3 = .ok (r_, s'))
    (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (hWC H3 s3 hpa3 hq3 true b u hu (fun i hi _ => hlk i (by omega))))
    (fun b1 w4 s4 H4 hp4 ⟨hw4, hrun4⟩ => ?_)
  have hq4 := hQwc s3 true b b1 s4 hq3 hrun4
  have hpa4 : C.H <+: H4 := hpa3.trans hp4
  have hb4 : H <+: H4 := hb3.trans hp4
  subst hw4
  refine specR_callNIH (C := ctxH C H4) yzQ2 fQd qdParams [vv kFu, vv kD, vv yzA1, vv yzB1] (qdBody C)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a1, Enc.idxW b1] (by decide) rfl (by decide) hc.qd
    ⟨by simp +decide [Env.get, yzParams, ctxEnv], by simp +decide [Env.get, yzParams, ctxEnv], by simp, by simp, trivial⟩
    (fun r_ w s' st => quickDefEq mode (knot mode C n) d a1 b1 s4 = .ok (r_, s') ∧ PostOBH (ctxH C H4) r_ w s' st) (fun r_ w s' H' => w = LLeq.obW r_ ∧ quickDefEq mode (knot mode C n) d a1 b1 s4 = .ok (r_, s'))
    (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu qdParams _ rfl hlk) (hQD H4 s4 hpa4 hq4 a1 b1)))
    (fun o w5 s5 H5 hp5 ⟨hw5, hrun5⟩ => ?_)
  have hq5 := hQqd s4 a1 b1 o s5 hq4 hrun5
  have hpa5 : C.H <+: H5 := hpa4.trans hp5
  have hb5 : H <+: H5 := hb4.trans hp5
  subst hw5
  rcases o with _ | vo
  swap
  · have hne : LLeq.obW (some vo) ≠ 0 := by cases vo <;> decide
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact specR_returnI _ (boolW vo) (by simp [sev]; exact obW_sub1 vo) (fun t ht => ⟨H5, hb5, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 0 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
  try dsimp only
  refine specR_callNIH (C := ctxH C H5) yzL fLdr ldrParams [vv kFu, vv kD, (.const (BitVec.ofNat 64 defeqLoopFuel)), vv yzA1, vv yzB1] (ldrBody v C)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, BitVec.ofNat 64 defeqLoopFuel, Enc.idxW a1, Enc.idxW b1] (by decide) rfl (by decide) hc.ldr
    ⟨by simp +decide [Env.get, yzParams, ctxEnv], by simp +decide [Env.get, yzParams, ctxEnv], rfl, by simp, by simp, trivial⟩
    (fun r_ w s' st => lazyDeltaReduction mode v (knot mode C n) C.fe d defeqLoopFuel a1 b1 s5 = .ok (r_, s') ∧ PostLR (ctxH C H5) r_ w s' st) (fun r_ w s' H' => lrsW C H' r_ w ∧ lazyDeltaReduction mode v (knot mode C n) C.fe d defeqLoopFuel a1 b1 s5 = .ok (r_, s'))
    (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu ldrParams _ rfl hlk) (hLDR H5 s5 hpa5 hq5 a1 b1)))
    (fun lr w6 s6 H6 hp6 ⟨hw6, hrun6⟩ => ?_)
  have hq6 := hQldr s5 a1 b1 lr s6 hq5 hrun6
  have hpa6 : C.H <+: H6 := hpa5.trans hp6
  have hb6 : H <+: H6 := hb5.trans hp6
  rcases lr with ⟨_ | _⟩ | ⟨x, y⟩
  · simp only [lrsW] at hw6; subst hw6
    refine specR_ifI _ 1 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H6, hb6, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · simp only [lrsW] at hw6; subst hw6
    refine specR_ifI _ 0 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H6, hb6, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · obtain ⟨o, rfl, hox, hoy⟩ := hw6
    refine specR_atEntry fun t ht => ?_
    have hbig := cellA_big hok ht.sr (List.getElem?_eq_some_iff.mp hox).1
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hbig.1) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hbig.2.1) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    refine UD.specR_heapLoadI' (C := ctxH C H6) yzX (vv yzL) o (Enc.idxW x) hox (by decide) (by simp <;> rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H6) yzY (.op .add [vv yzL, .const 8]) (o + 1) (Enc.idxW y) hoy (by decide)
      (by simp [sev]; exact cellA_add8 C o) ?_
    refine specR_callNIH (C := ctxH C H6) yzJ fPpr djParams [vv kFu, vv kD, vv yzX, vv yzY] (djBody mode.verifiedChecks C)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW x, Enc.idxW y] (by decide) rfl (by decide) hc.dj
      ⟨by simp +decide [Env.get, yzParams, ctxEnv], by simp +decide [Env.get, yzParams, ctxEnv], by simp, by simp, trivial⟩
      (fun r_ w s' st => defeqProjPair mode (knot mode C n) C.fe d x y s6 = .ok (r_, s') ∧ PostB (ctxH C H6) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ defeqProjPair mode (knot mode C n) C.fe d x y s6 = .ok (r_, s'))
      (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu djParams _ rfl hlk) (hDJ H6 s6 hpa6 hq6 x y)))
      (fun pj w7 s7 H7 hp7 ⟨hw7, hrun7⟩ => ?_)
    have hq7 := hQdj s6 x y pj s7 hq6 hrun7
    have hpa7 : C.H <+: H7 := hpa6.trans hp7
    have hb7 : H <+: H7 := hb6.trans hp7
    subst hw7
    cases pj
    swap
    · refine specR_ifI _ 1 (by simp [boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [↓reduceIte]
      exact specR_returnI _ 1 rfl (fun t ht => ⟨H7, hb7, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine specR_ifI _ 0 (by simp [boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine specR_callNIH (C := ctxH C H7) yzPa fHp [hpE] [vv yzX] hpBody
      [Enc.idxW x] (by decide) rfl (by decide) hc.hp
      ⟨by simp, trivial⟩
      (fun r_ w s' st => headIsProj x s7 = .ok (r_, s') ∧ PostB (ctxH C H7) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ headIsProj x s7 = .ok (r_, s'))
      (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [hpE] _ rfl hlk) (hHP H7 s7 hpa7 hq7 x)))
      (fun pa w8 s8 H8 hp8 ⟨hw8, hrun8⟩ => ?_)
    have hq8 := hQhp s7 x pa s8 hq7 hrun8
    have hpa8 : C.H <+: H8 := hpa7.trans hp8
    have hb8 : H <+: H8 := hb7.trans hp8
    subst hw8
    refine specR_callNIH (C := ctxH C H8) yzPb fHp [hpE] [vv yzY] hpBody
      [Enc.idxW y] (by decide) rfl (by decide) hc.hp
      ⟨by simp, trivial⟩
      (fun r_ w s' st => headIsProj y s8 = .ok (r_, s') ∧ PostB (ctxH C H8) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ headIsProj y s8 = .ok (r_, s'))
      (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [hpE] _ rfl hlk) (hHP H8 s8 hpa8 hq8 y)))
      (fun pb w9 s9 H9 hp9 ⟨hw9, hrun9⟩ => ?_)
    have hq9 := hQhp s8 y pb s9 hq8 hrun9
    have hpa9 : C.H <+: H9 := hpa8.trans hp9
    have hb9 : H <+: H9 := hb8.trans hp9
    subst hw9
    cases pa <;> cases pb
    · refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
      simp only [Bool.not_false, Bool.and_self, ↓reduceIte]
      refine specR_congr (m' := defeqStuck mode (knot mode C n) C.fe d x y >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H9) yzK fDk dkParams [vv kFu, vv kD, vv yzX, vv yzY] (dkBody C)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW x, Enc.idxW y] (by decide) rfl (by decide) hc.dk
        ⟨by simp +decide [Env.get, yzParams, ctxEnv], by simp +decide [Env.get, yzParams, ctxEnv], by simp, by simp, trivial⟩
        (fun r_ w s' st => defeqStuck mode (knot mode C n) C.fe d x y s9 = .ok (r_, s') ∧ PostB (ctxH C H9) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ defeqStuck mode (knot mode C n) C.fe d x y s9 = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu dkParams _ rfl hlk) (hDK H9 s9 hpa9 hq9 x y)))
        (fun rr w10 s10 H10 hp10 ⟨hw10, hrun10⟩ => ?_)
      have hq10 := hQdk s9 x y rr s10 hq9 hrun10
      have hpa10 : C.H <+: H10 := hpa9.trans hp10
      have hb10 : H <+: H10 := hb9.trans hp10
      subst hw10
      exact specR_returnI _ (boolW rr) (by simp) (fun t ht => ⟨H10, hb10, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [Bool.not_true, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      refine specR_callNIH (C := ctxH C H9) yzA2 fWC wcParams [vv kFu, .const 0, vv kD, vv yzX] wcE
        [BitVec.ofNat 64 n, boolW false, BitVec.ofNat 64 d, Enc.idxW x] (by decide) rfl (by decide) hc.wc
        ⟨by simp +decide [Env.get, yzParams, ctxEnv], rfl, by simp +decide [Env.get, yzParams, ctxEnv], by simp, trivial⟩
        (fun r_ w s' st => (knot mode C n).whnfCore false d x s9 = .ok (r_, s') ∧ PostK (ctxH C H9) r_ w s' st) (fun r_ w s' H' => w = Enc.idxW r_ ∧ (knot mode C n).whnfCore false d x s9 = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (hWC H9 s9 hpa9 hq9 false x u hu (fun i hi _ => hlk i (by omega))))
        (fun a2 w11 s11 H11 hp11 ⟨hw11, hrun11⟩ => ?_)
      have hq11 := hQwc s9 false x a2 s11 hq9 hrun11
      have hpa11 : C.H <+: H11 := hpa9.trans hp11
      have hb11 : H <+: H11 := hb9.trans hp11
      subst hw11
      refine specR_callNIH (C := ctxH C H11) yzB2 fWC wcParams [vv kFu, .const 0, vv kD, vv yzY] wcE
        [BitVec.ofNat 64 n, boolW false, BitVec.ofNat 64 d, Enc.idxW y] (by decide) rfl (by decide) hc.wc
        ⟨by simp +decide [Env.get, yzParams, ctxEnv], rfl, by simp +decide [Env.get, yzParams, ctxEnv], by simp, trivial⟩
        (fun r_ w s' st => (knot mode C n).whnfCore false d y s11 = .ok (r_, s') ∧ PostK (ctxH C H11) r_ w s' st) (fun r_ w s' H' => w = Enc.idxW r_ ∧ (knot mode C n).whnfCore false d y s11 = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (hWC H11 s11 hpa11 hq11 false y u hu (fun i hi _ => hlk i (by omega))))
        (fun b2 w12 s12 H12 hp12 ⟨hw12, hrun12⟩ => ?_)
      have hq12 := hQwc s11 false y b2 s12 hq11 hrun12
      have hpa12 : C.H <+: H12 := hpa11.trans hp12
      have hb12 : H <+: H12 := hb11.trans hp12
      subst hw12
      by_cases hab : x = a2 ∧ y = b2
      · obtain ⟨rfl, rfl⟩ := hab
        refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
        simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte]
        refine specR_congr (m' := defeqStuck mode (knot mode C n) C.fe d x y >>= fun r => pure r) (by simp) ?_
        refine specR_callNIH (C := ctxH C H12) yzK fDk dkParams [vv kFu, vv kD, vv yzX, vv yzY] (dkBody C)
          [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW x, Enc.idxW y] (by decide) rfl (by decide) hc.dk
          ⟨by simp +decide [Env.get, yzParams, ctxEnv], by simp +decide [Env.get, yzParams, ctxEnv], by simp, by simp, trivial⟩
          (fun r_ w s' st => defeqStuck mode (knot mode C n) C.fe d x y s12 = .ok (r_, s') ∧ PostB (ctxH C H12) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ defeqStuck mode (knot mode C n) C.fe d x y s12 = .ok (r_, s'))
          (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
          (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu dkParams _ rfl hlk) (hDK H12 s12 hpa12 hq12 x y)))
          (fun rr w13 s13 H13 hp13 ⟨hw13, hrun13⟩ => ?_)
        have hq13 := hQdk s12 x y rr s13 hq12 hrun13
        have hpa13 : C.H <+: H13 := hpa12.trans hp13
        have hb13 : H <+: H13 := hb12.trans hp13
        subst hw13
        exact specR_returnI _ (boolW rr) (by simp) (fun t ht => ⟨H13, hb13, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

      have hw' : (if Enc.idxW a2 = Enc.idxW x then (1 : BitVec 64) else 0) &&& (if Enc.idxW b2 = Enc.idxW y then 1 else 0) = 0 := by
        by_cases h1 : x = a2
        · have h2 : y ≠ b2 := fun h2 => hab ⟨h1, h2⟩
          have : Enc.idxW b2 ≠ Enc.idxW y := fun e => h2 (Enc.idxW_inj e).symm
          simp [h1, this]
        · have : Enc.idxW a2 ≠ Enc.idxW x := fun e => h1 (Enc.idxW_inj e).symm
          simp [this]
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hw') (fun h => absurd rfl h) (fun _ => ?_)
      have hb : (a2 == x && b2 == y) = false := by
        simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]; by_cases h1 : x = a2
        · exact Or.inr (fun h2 => hab ⟨h1, h2.symm⟩)
        · exact Or.inl (fun h => h1 h.symm)
      rw [hb]; simp only [Bool.false_eq_true, ↓reduceIte]
      refine specR_congr (m' := (knot mode C n).defeq d a2 b2 >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H12) yzV fD dParams [vv kFu, vv kD, vv yzA2, vv yzB2] (dE C)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a2, Enc.idxW b2] (by decide) rfl (by decide) hc.d
        ⟨by simp +decide [Env.get, yzParams, ctxEnv], by simp +decide [Env.get, yzParams, ctxEnv], by simp, by simp, trivial⟩
        (fun r_ w s' st => (knot mode C n).defeq d a2 b2 s12 = .ok (r_, s') ∧ PostB (ctxH C H12) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ (knot mode C n).defeq d a2 b2 s12 = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (hD H12 s12 hpa12 hq12 a2 b2 u hu (fun i hi _ => hlk i (by omega))))
        (fun rr w14 s14 H14 hp14 ⟨hw14, hrun14⟩ => ?_)
      have hq14 := hQd s12 a2 b2 rr s14 hq12 hrun14
      have hpa14 : C.H <+: H14 := hpa12.trans hp14
      have hb14 : H <+: H14 := hb12.trans hp14
      subst hw14
      exact specR_returnI _ (boolW rr) (by simp) (fun t ht => ⟨H14, hb14, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [Bool.not_true, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      refine specR_callNIH (C := ctxH C H9) yzA2 fWC wcParams [vv kFu, .const 0, vv kD, vv yzX] wcE
        [BitVec.ofNat 64 n, boolW false, BitVec.ofNat 64 d, Enc.idxW x] (by decide) rfl (by decide) hc.wc
        ⟨by simp +decide [Env.get, yzParams, ctxEnv], rfl, by simp +decide [Env.get, yzParams, ctxEnv], by simp, trivial⟩
        (fun r_ w s' st => (knot mode C n).whnfCore false d x s9 = .ok (r_, s') ∧ PostK (ctxH C H9) r_ w s' st) (fun r_ w s' H' => w = Enc.idxW r_ ∧ (knot mode C n).whnfCore false d x s9 = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (hWC H9 s9 hpa9 hq9 false x u hu (fun i hi _ => hlk i (by omega))))
        (fun a2 w11 s11 H11 hp11 ⟨hw11, hrun11⟩ => ?_)
      have hq11 := hQwc s9 false x a2 s11 hq9 hrun11
      have hpa11 : C.H <+: H11 := hpa9.trans hp11
      have hb11 : H <+: H11 := hb9.trans hp11
      subst hw11
      refine specR_callNIH (C := ctxH C H11) yzB2 fWC wcParams [vv kFu, .const 0, vv kD, vv yzY] wcE
        [BitVec.ofNat 64 n, boolW false, BitVec.ofNat 64 d, Enc.idxW y] (by decide) rfl (by decide) hc.wc
        ⟨by simp +decide [Env.get, yzParams, ctxEnv], rfl, by simp +decide [Env.get, yzParams, ctxEnv], by simp, trivial⟩
        (fun r_ w s' st => (knot mode C n).whnfCore false d y s11 = .ok (r_, s') ∧ PostK (ctxH C H11) r_ w s' st) (fun r_ w s' H' => w = Enc.idxW r_ ∧ (knot mode C n).whnfCore false d y s11 = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (hWC H11 s11 hpa11 hq11 false y u hu (fun i hi _ => hlk i (by omega))))
        (fun b2 w12 s12 H12 hp12 ⟨hw12, hrun12⟩ => ?_)
      have hq12 := hQwc s11 false y b2 s12 hq11 hrun12
      have hpa12 : C.H <+: H12 := hpa11.trans hp12
      have hb12 : H <+: H12 := hb11.trans hp12
      subst hw12
      by_cases hab : x = a2 ∧ y = b2
      · obtain ⟨rfl, rfl⟩ := hab
        refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
        simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte]
        refine specR_congr (m' := defeqStuck mode (knot mode C n) C.fe d x y >>= fun r => pure r) (by simp) ?_
        refine specR_callNIH (C := ctxH C H12) yzK fDk dkParams [vv kFu, vv kD, vv yzX, vv yzY] (dkBody C)
          [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW x, Enc.idxW y] (by decide) rfl (by decide) hc.dk
          ⟨by simp +decide [Env.get, yzParams, ctxEnv], by simp +decide [Env.get, yzParams, ctxEnv], by simp, by simp, trivial⟩
          (fun r_ w s' st => defeqStuck mode (knot mode C n) C.fe d x y s12 = .ok (r_, s') ∧ PostB (ctxH C H12) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ defeqStuck mode (knot mode C n) C.fe d x y s12 = .ok (r_, s'))
          (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
          (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu dkParams _ rfl hlk) (hDK H12 s12 hpa12 hq12 x y)))
          (fun rr w13 s13 H13 hp13 ⟨hw13, hrun13⟩ => ?_)
        have hq13 := hQdk s12 x y rr s13 hq12 hrun13
        have hpa13 : C.H <+: H13 := hpa12.trans hp13
        have hb13 : H <+: H13 := hb12.trans hp13
        subst hw13
        exact specR_returnI _ (boolW rr) (by simp) (fun t ht => ⟨H13, hb13, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

      have hw' : (if Enc.idxW a2 = Enc.idxW x then (1 : BitVec 64) else 0) &&& (if Enc.idxW b2 = Enc.idxW y then 1 else 0) = 0 := by
        by_cases h1 : x = a2
        · have h2 : y ≠ b2 := fun h2 => hab ⟨h1, h2⟩
          have : Enc.idxW b2 ≠ Enc.idxW y := fun e => h2 (Enc.idxW_inj e).symm
          simp [h1, this]
        · have : Enc.idxW a2 ≠ Enc.idxW x := fun e => h1 (Enc.idxW_inj e).symm
          simp [this]
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hw') (fun h => absurd rfl h) (fun _ => ?_)
      have hb : (a2 == x && b2 == y) = false := by
        simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]; by_cases h1 : x = a2
        · exact Or.inr (fun h2 => hab ⟨h1, h2.symm⟩)
        · exact Or.inl (fun h => h1 h.symm)
      rw [hb]; simp only [Bool.false_eq_true, ↓reduceIte]
      refine specR_congr (m' := (knot mode C n).defeq d a2 b2 >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H12) yzV fD dParams [vv kFu, vv kD, vv yzA2, vv yzB2] (dE C)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a2, Enc.idxW b2] (by decide) rfl (by decide) hc.d
        ⟨by simp +decide [Env.get, yzParams, ctxEnv], by simp +decide [Env.get, yzParams, ctxEnv], by simp, by simp, trivial⟩
        (fun r_ w s' st => (knot mode C n).defeq d a2 b2 s12 = .ok (r_, s') ∧ PostB (ctxH C H12) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ (knot mode C n).defeq d a2 b2 s12 = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (hD H12 s12 hpa12 hq12 a2 b2 u hu (fun i hi _ => hlk i (by omega))))
        (fun rr w14 s14 H14 hp14 ⟨hw14, hrun14⟩ => ?_)
      have hq14 := hQd s12 a2 b2 rr s14 hq12 hrun14
      have hpa14 : C.H <+: H14 := hpa12.trans hp14
      have hb14 : H <+: H14 := hb12.trans hp14
      subst hw14
      exact specR_returnI _ (boolW rr) (by simp) (fun t ht => ⟨H14, hb14, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [Bool.not_true, Bool.false_and, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      refine specR_callNIH (C := ctxH C H9) yzA2 fWC wcParams [vv kFu, .const 0, vv kD, vv yzX] wcE
        [BitVec.ofNat 64 n, boolW false, BitVec.ofNat 64 d, Enc.idxW x] (by decide) rfl (by decide) hc.wc
        ⟨by simp +decide [Env.get, yzParams, ctxEnv], rfl, by simp +decide [Env.get, yzParams, ctxEnv], by simp, trivial⟩
        (fun r_ w s' st => (knot mode C n).whnfCore false d x s9 = .ok (r_, s') ∧ PostK (ctxH C H9) r_ w s' st) (fun r_ w s' H' => w = Enc.idxW r_ ∧ (knot mode C n).whnfCore false d x s9 = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (hWC H9 s9 hpa9 hq9 false x u hu (fun i hi _ => hlk i (by omega))))
        (fun a2 w11 s11 H11 hp11 ⟨hw11, hrun11⟩ => ?_)
      have hq11 := hQwc s9 false x a2 s11 hq9 hrun11
      have hpa11 : C.H <+: H11 := hpa9.trans hp11
      have hb11 : H <+: H11 := hb9.trans hp11
      subst hw11
      refine specR_callNIH (C := ctxH C H11) yzB2 fWC wcParams [vv kFu, .const 0, vv kD, vv yzY] wcE
        [BitVec.ofNat 64 n, boolW false, BitVec.ofNat 64 d, Enc.idxW y] (by decide) rfl (by decide) hc.wc
        ⟨by simp +decide [Env.get, yzParams, ctxEnv], rfl, by simp +decide [Env.get, yzParams, ctxEnv], by simp, trivial⟩
        (fun r_ w s' st => (knot mode C n).whnfCore false d y s11 = .ok (r_, s') ∧ PostK (ctxH C H11) r_ w s' st) (fun r_ w s' H' => w = Enc.idxW r_ ∧ (knot mode C n).whnfCore false d y s11 = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (hWC H11 s11 hpa11 hq11 false y u hu (fun i hi _ => hlk i (by omega))))
        (fun b2 w12 s12 H12 hp12 ⟨hw12, hrun12⟩ => ?_)
      have hq12 := hQwc s11 false y b2 s12 hq11 hrun12
      have hpa12 : C.H <+: H12 := hpa11.trans hp12
      have hb12 : H <+: H12 := hb11.trans hp12
      subst hw12
      by_cases hab : x = a2 ∧ y = b2
      · obtain ⟨rfl, rfl⟩ := hab
        refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
        simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte]
        refine specR_congr (m' := defeqStuck mode (knot mode C n) C.fe d x y >>= fun r => pure r) (by simp) ?_
        refine specR_callNIH (C := ctxH C H12) yzK fDk dkParams [vv kFu, vv kD, vv yzX, vv yzY] (dkBody C)
          [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW x, Enc.idxW y] (by decide) rfl (by decide) hc.dk
          ⟨by simp +decide [Env.get, yzParams, ctxEnv], by simp +decide [Env.get, yzParams, ctxEnv], by simp, by simp, trivial⟩
          (fun r_ w s' st => defeqStuck mode (knot mode C n) C.fe d x y s12 = .ok (r_, s') ∧ PostB (ctxH C H12) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ defeqStuck mode (knot mode C n) C.fe d x y s12 = .ok (r_, s'))
          (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
          (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu dkParams _ rfl hlk) (hDK H12 s12 hpa12 hq12 x y)))
          (fun rr w13 s13 H13 hp13 ⟨hw13, hrun13⟩ => ?_)
        have hq13 := hQdk s12 x y rr s13 hq12 hrun13
        have hpa13 : C.H <+: H13 := hpa12.trans hp13
        have hb13 : H <+: H13 := hb12.trans hp13
        subst hw13
        exact specR_returnI _ (boolW rr) (by simp) (fun t ht => ⟨H13, hb13, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

      have hw' : (if Enc.idxW a2 = Enc.idxW x then (1 : BitVec 64) else 0) &&& (if Enc.idxW b2 = Enc.idxW y then 1 else 0) = 0 := by
        by_cases h1 : x = a2
        · have h2 : y ≠ b2 := fun h2 => hab ⟨h1, h2⟩
          have : Enc.idxW b2 ≠ Enc.idxW y := fun e => h2 (Enc.idxW_inj e).symm
          simp [h1, this]
        · have : Enc.idxW a2 ≠ Enc.idxW x := fun e => h1 (Enc.idxW_inj e).symm
          simp [this]
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hw') (fun h => absurd rfl h) (fun _ => ?_)
      have hb : (a2 == x && b2 == y) = false := by
        simp only [Bool.and_eq_false_iff, beq_eq_false_iff_ne]; by_cases h1 : x = a2
        · exact Or.inr (fun h2 => hab ⟨h1, h2.symm⟩)
        · exact Or.inl (fun h => h1 h.symm)
      rw [hb]; simp only [Bool.false_eq_true, ↓reduceIte]
      refine specR_congr (m' := (knot mode C n).defeq d a2 b2 >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H12) yzV fD dParams [vv kFu, vv kD, vv yzA2, vv yzB2] (dE C)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a2, Enc.idxW b2] (by decide) rfl (by decide) hc.d
        ⟨by simp +decide [Env.get, yzParams, ctxEnv], by simp +decide [Env.get, yzParams, ctxEnv], by simp, by simp, trivial⟩
        (fun r_ w s' st => (knot mode C n).defeq d a2 b2 s12 = .ok (r_, s') ∧ PostB (ctxH C H12) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ (knot mode C n).defeq d a2 b2 s12 = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (hD H12 s12 hpa12 hq12 a2 b2 u hu (fun i hi _ => hlk i (by omega))))
        (fun rr w14 s14 H14 hp14 ⟨hw14, hrun14⟩ => ?_)
      have hq14 := hQd s12 a2 b2 rr s14 hq12 hrun14
      have hpa14 : C.H <+: H14 := hpa12.trans hp14
      have hb14 : H <+: H14 := hb12.trans hp14
      subst hw14
      exact specR_returnI _ (boolW rr) (by simp) (fun t ht => ⟨H14, hb14, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)



end

end ConPanqueque.T.WC
