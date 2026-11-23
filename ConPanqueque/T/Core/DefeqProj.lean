import ConPanqueque.T.Core.LazyDelta
import ConPanqueque.T.Core.ReduceProj
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `lazyDeltaProjReduction` and `defeqProjPair`

The projections' scrutinees through lazy-delta steps, then the projected fields. A projection index at or above
`2^64` halts (a resource decline, as in `whnfCore`'s projection arm).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def lpN := ofString "dpj_lpn"
def lpI := ofString "dpj_lpi"
def lpF := ofString "dpj_lpf"
def lpA := ofString "dpj_lpa"
def lpB := ofString "dpj_lpb"
def lpS := ofString "dpj_lps"
def lpX := ofString "dpj_lpx"
def lpY := ofString "dpj_lpy"
def lpV := ofString "dpj_lpv"
def lpA2 := ofString "dpj_lpa2"
def lpB2 := ofString "dpj_lpb2"
def lpR := ofString "dpj_lpr"
def djA := ofString "dpj_dja"
def djB := ofString "dpj_djb"
def djN1 := ofString "dpj_djn1"
def djP1 := ofString "dpj_djp1"
def djI1 := ofString "dpj_dji1"
def djN2 := ofString "dpj_djn2"
def djP2 := ofString "dpj_djp2"
def djI2 := ofString "dpj_dji2"
def djR := ofString "dpj_djr"
def fLpr := ofString "lazyDeltaProjReduction"
def fPpr := ofString "defeqProjPair"

@[simp] theorem dpj_lpN_ne_lpI : lpN ≠ lpI := by decide
@[simp] theorem dpj_lpN_ne_lpF : lpN ≠ lpF := by decide
@[simp] theorem dpj_lpN_ne_lpA : lpN ≠ lpA := by decide
@[simp] theorem dpj_lpN_ne_lpB : lpN ≠ lpB := by decide
@[simp] theorem dpj_lpN_ne_lpS : lpN ≠ lpS := by decide
@[simp] theorem dpj_lpN_ne_lpX : lpN ≠ lpX := by decide
@[simp] theorem dpj_lpN_ne_lpY : lpN ≠ lpY := by decide
@[simp] theorem dpj_lpN_ne_lpV : lpN ≠ lpV := by decide
@[simp] theorem dpj_lpN_ne_lpA2 : lpN ≠ lpA2 := by decide
@[simp] theorem dpj_lpN_ne_lpB2 : lpN ≠ lpB2 := by decide
@[simp] theorem dpj_lpN_ne_lpR : lpN ≠ lpR := by decide
@[simp] theorem dpj_lpN_ne_djA : lpN ≠ djA := by decide
@[simp] theorem dpj_lpN_ne_djB : lpN ≠ djB := by decide
@[simp] theorem dpj_lpN_ne_djN1 : lpN ≠ djN1 := by decide
@[simp] theorem dpj_lpN_ne_djP1 : lpN ≠ djP1 := by decide
@[simp] theorem dpj_lpN_ne_djI1 : lpN ≠ djI1 := by decide
@[simp] theorem dpj_lpN_ne_djN2 : lpN ≠ djN2 := by decide
@[simp] theorem dpj_lpN_ne_djP2 : lpN ≠ djP2 := by decide
@[simp] theorem dpj_lpN_ne_djI2 : lpN ≠ djI2 := by decide
@[simp] theorem dpj_lpN_ne_djR : lpN ≠ djR := by decide
@[simp] theorem dpj_lpN_ne_lFl : lpN ≠ lFl := by decide
@[simp] theorem dpj_lFl_ne_lpN : lFl ≠ lpN := by decide
@[simp] theorem dpj_lpN_ne_lDh : lpN ≠ lDh := by decide
@[simp] theorem dpj_lDh_ne_lpN : lDh ≠ lpN := by decide
@[simp] theorem dpj_lpN_ne_lDt : lpN ≠ lDt := by decide
@[simp] theorem dpj_lDt_ne_lpN : lDt ≠ lpN := by decide
@[simp] theorem dpj_lpN_ne_lDg : lpN ≠ lDg := by decide
@[simp] theorem dpj_lDg_ne_lpN : lDg ≠ lpN := by decide
@[simp] theorem dpj_lpN_ne_lDi : lpN ≠ lDi := by decide
@[simp] theorem dpj_lDi_ne_lpN : lDi ≠ lpN := by decide
@[simp] theorem dpj_lpN_ne_lRp : lpN ≠ lRp := by decide
@[simp] theorem dpj_lRp_ne_lpN : lRp ≠ lpN := by decide
@[simp] theorem dpj_lpN_ne_lRn : lpN ≠ lRn := by decide
@[simp] theorem dpj_lRn_ne_lpN : lRn ≠ lpN := by decide
@[simp] theorem dpj_lpN_ne_lFle : lpN ≠ lFle := by decide
@[simp] theorem dpj_lFle_ne_lpN : lFle ≠ lpN := by decide
@[simp] theorem dpj_lpN_ne_lKb : lpN ≠ lKb := by decide
@[simp] theorem dpj_lKb_ne_lpN : lKb ≠ lpN := by decide
@[simp] theorem dpj_lpN_ne_lDir : lpN ≠ lDir := by decide
@[simp] theorem dpj_lDir_ne_lpN : lDir ≠ lpN := by decide
@[simp] theorem dpj_lpN_ne_lFln : lpN ≠ lFln := by decide
@[simp] theorem dpj_lFln_ne_lpN : lFln ≠ lpN := by decide
@[simp] theorem dpj_lpN_ne_lFll : lpN ≠ lFll := by decide
@[simp] theorem dpj_lFll_ne_lpN : lFll ≠ lpN := by decide
@[simp] theorem dpj_lpN_ne_lFls : lpN ≠ lFls := by decide
@[simp] theorem dpj_lFls_ne_lpN : lFls ≠ lpN := by decide
@[simp] theorem dpj_lpN_ne_kFu : lpN ≠ kFu := by decide
@[simp] theorem dpj_kFu_ne_lpN : kFu ≠ lpN := by decide
@[simp] theorem dpj_lpN_ne_kD : lpN ≠ kD := by decide
@[simp] theorem dpj_kD_ne_lpN : kD ≠ lpN := by decide
@[simp] theorem dpj_lpI_ne_lpN : lpI ≠ lpN := by decide
@[simp] theorem dpj_lpI_ne_lpF : lpI ≠ lpF := by decide
@[simp] theorem dpj_lpI_ne_lpA : lpI ≠ lpA := by decide
@[simp] theorem dpj_lpI_ne_lpB : lpI ≠ lpB := by decide
@[simp] theorem dpj_lpI_ne_lpS : lpI ≠ lpS := by decide
@[simp] theorem dpj_lpI_ne_lpX : lpI ≠ lpX := by decide
@[simp] theorem dpj_lpI_ne_lpY : lpI ≠ lpY := by decide
@[simp] theorem dpj_lpI_ne_lpV : lpI ≠ lpV := by decide
@[simp] theorem dpj_lpI_ne_lpA2 : lpI ≠ lpA2 := by decide
@[simp] theorem dpj_lpI_ne_lpB2 : lpI ≠ lpB2 := by decide
@[simp] theorem dpj_lpI_ne_lpR : lpI ≠ lpR := by decide
@[simp] theorem dpj_lpI_ne_djA : lpI ≠ djA := by decide
@[simp] theorem dpj_lpI_ne_djB : lpI ≠ djB := by decide
@[simp] theorem dpj_lpI_ne_djN1 : lpI ≠ djN1 := by decide
@[simp] theorem dpj_lpI_ne_djP1 : lpI ≠ djP1 := by decide
@[simp] theorem dpj_lpI_ne_djI1 : lpI ≠ djI1 := by decide
@[simp] theorem dpj_lpI_ne_djN2 : lpI ≠ djN2 := by decide
@[simp] theorem dpj_lpI_ne_djP2 : lpI ≠ djP2 := by decide
@[simp] theorem dpj_lpI_ne_djI2 : lpI ≠ djI2 := by decide
@[simp] theorem dpj_lpI_ne_djR : lpI ≠ djR := by decide
@[simp] theorem dpj_lpI_ne_lFl : lpI ≠ lFl := by decide
@[simp] theorem dpj_lFl_ne_lpI : lFl ≠ lpI := by decide
@[simp] theorem dpj_lpI_ne_lDh : lpI ≠ lDh := by decide
@[simp] theorem dpj_lDh_ne_lpI : lDh ≠ lpI := by decide
@[simp] theorem dpj_lpI_ne_lDt : lpI ≠ lDt := by decide
@[simp] theorem dpj_lDt_ne_lpI : lDt ≠ lpI := by decide
@[simp] theorem dpj_lpI_ne_lDg : lpI ≠ lDg := by decide
@[simp] theorem dpj_lDg_ne_lpI : lDg ≠ lpI := by decide
@[simp] theorem dpj_lpI_ne_lDi : lpI ≠ lDi := by decide
@[simp] theorem dpj_lDi_ne_lpI : lDi ≠ lpI := by decide
@[simp] theorem dpj_lpI_ne_lRp : lpI ≠ lRp := by decide
@[simp] theorem dpj_lRp_ne_lpI : lRp ≠ lpI := by decide
@[simp] theorem dpj_lpI_ne_lRn : lpI ≠ lRn := by decide
@[simp] theorem dpj_lRn_ne_lpI : lRn ≠ lpI := by decide
@[simp] theorem dpj_lpI_ne_lFle : lpI ≠ lFle := by decide
@[simp] theorem dpj_lFle_ne_lpI : lFle ≠ lpI := by decide
@[simp] theorem dpj_lpI_ne_lKb : lpI ≠ lKb := by decide
@[simp] theorem dpj_lKb_ne_lpI : lKb ≠ lpI := by decide
@[simp] theorem dpj_lpI_ne_lDir : lpI ≠ lDir := by decide
@[simp] theorem dpj_lDir_ne_lpI : lDir ≠ lpI := by decide
@[simp] theorem dpj_lpI_ne_lFln : lpI ≠ lFln := by decide
@[simp] theorem dpj_lFln_ne_lpI : lFln ≠ lpI := by decide
@[simp] theorem dpj_lpI_ne_lFll : lpI ≠ lFll := by decide
@[simp] theorem dpj_lFll_ne_lpI : lFll ≠ lpI := by decide
@[simp] theorem dpj_lpI_ne_lFls : lpI ≠ lFls := by decide
@[simp] theorem dpj_lFls_ne_lpI : lFls ≠ lpI := by decide
@[simp] theorem dpj_lpI_ne_kFu : lpI ≠ kFu := by decide
@[simp] theorem dpj_kFu_ne_lpI : kFu ≠ lpI := by decide
@[simp] theorem dpj_lpI_ne_kD : lpI ≠ kD := by decide
@[simp] theorem dpj_kD_ne_lpI : kD ≠ lpI := by decide
@[simp] theorem dpj_lpF_ne_lpN : lpF ≠ lpN := by decide
@[simp] theorem dpj_lpF_ne_lpI : lpF ≠ lpI := by decide
@[simp] theorem dpj_lpF_ne_lpA : lpF ≠ lpA := by decide
@[simp] theorem dpj_lpF_ne_lpB : lpF ≠ lpB := by decide
@[simp] theorem dpj_lpF_ne_lpS : lpF ≠ lpS := by decide
@[simp] theorem dpj_lpF_ne_lpX : lpF ≠ lpX := by decide
@[simp] theorem dpj_lpF_ne_lpY : lpF ≠ lpY := by decide
@[simp] theorem dpj_lpF_ne_lpV : lpF ≠ lpV := by decide
@[simp] theorem dpj_lpF_ne_lpA2 : lpF ≠ lpA2 := by decide
@[simp] theorem dpj_lpF_ne_lpB2 : lpF ≠ lpB2 := by decide
@[simp] theorem dpj_lpF_ne_lpR : lpF ≠ lpR := by decide
@[simp] theorem dpj_lpF_ne_djA : lpF ≠ djA := by decide
@[simp] theorem dpj_lpF_ne_djB : lpF ≠ djB := by decide
@[simp] theorem dpj_lpF_ne_djN1 : lpF ≠ djN1 := by decide
@[simp] theorem dpj_lpF_ne_djP1 : lpF ≠ djP1 := by decide
@[simp] theorem dpj_lpF_ne_djI1 : lpF ≠ djI1 := by decide
@[simp] theorem dpj_lpF_ne_djN2 : lpF ≠ djN2 := by decide
@[simp] theorem dpj_lpF_ne_djP2 : lpF ≠ djP2 := by decide
@[simp] theorem dpj_lpF_ne_djI2 : lpF ≠ djI2 := by decide
@[simp] theorem dpj_lpF_ne_djR : lpF ≠ djR := by decide
@[simp] theorem dpj_lpF_ne_lFl : lpF ≠ lFl := by decide
@[simp] theorem dpj_lFl_ne_lpF : lFl ≠ lpF := by decide
@[simp] theorem dpj_lpF_ne_lDh : lpF ≠ lDh := by decide
@[simp] theorem dpj_lDh_ne_lpF : lDh ≠ lpF := by decide
@[simp] theorem dpj_lpF_ne_lDt : lpF ≠ lDt := by decide
@[simp] theorem dpj_lDt_ne_lpF : lDt ≠ lpF := by decide
@[simp] theorem dpj_lpF_ne_lDg : lpF ≠ lDg := by decide
@[simp] theorem dpj_lDg_ne_lpF : lDg ≠ lpF := by decide
@[simp] theorem dpj_lpF_ne_lDi : lpF ≠ lDi := by decide
@[simp] theorem dpj_lDi_ne_lpF : lDi ≠ lpF := by decide
@[simp] theorem dpj_lpF_ne_lRp : lpF ≠ lRp := by decide
@[simp] theorem dpj_lRp_ne_lpF : lRp ≠ lpF := by decide
@[simp] theorem dpj_lpF_ne_lRn : lpF ≠ lRn := by decide
@[simp] theorem dpj_lRn_ne_lpF : lRn ≠ lpF := by decide
@[simp] theorem dpj_lpF_ne_lFle : lpF ≠ lFle := by decide
@[simp] theorem dpj_lFle_ne_lpF : lFle ≠ lpF := by decide
@[simp] theorem dpj_lpF_ne_lKb : lpF ≠ lKb := by decide
@[simp] theorem dpj_lKb_ne_lpF : lKb ≠ lpF := by decide
@[simp] theorem dpj_lpF_ne_lDir : lpF ≠ lDir := by decide
@[simp] theorem dpj_lDir_ne_lpF : lDir ≠ lpF := by decide
@[simp] theorem dpj_lpF_ne_lFln : lpF ≠ lFln := by decide
@[simp] theorem dpj_lFln_ne_lpF : lFln ≠ lpF := by decide
@[simp] theorem dpj_lpF_ne_lFll : lpF ≠ lFll := by decide
@[simp] theorem dpj_lFll_ne_lpF : lFll ≠ lpF := by decide
@[simp] theorem dpj_lpF_ne_lFls : lpF ≠ lFls := by decide
@[simp] theorem dpj_lFls_ne_lpF : lFls ≠ lpF := by decide
@[simp] theorem dpj_lpF_ne_kFu : lpF ≠ kFu := by decide
@[simp] theorem dpj_kFu_ne_lpF : kFu ≠ lpF := by decide
@[simp] theorem dpj_lpF_ne_kD : lpF ≠ kD := by decide
@[simp] theorem dpj_kD_ne_lpF : kD ≠ lpF := by decide
@[simp] theorem dpj_lpA_ne_lpN : lpA ≠ lpN := by decide
@[simp] theorem dpj_lpA_ne_lpI : lpA ≠ lpI := by decide
@[simp] theorem dpj_lpA_ne_lpF : lpA ≠ lpF := by decide
@[simp] theorem dpj_lpA_ne_lpB : lpA ≠ lpB := by decide
@[simp] theorem dpj_lpA_ne_lpS : lpA ≠ lpS := by decide
@[simp] theorem dpj_lpA_ne_lpX : lpA ≠ lpX := by decide
@[simp] theorem dpj_lpA_ne_lpY : lpA ≠ lpY := by decide
@[simp] theorem dpj_lpA_ne_lpV : lpA ≠ lpV := by decide
@[simp] theorem dpj_lpA_ne_lpA2 : lpA ≠ lpA2 := by decide
@[simp] theorem dpj_lpA_ne_lpB2 : lpA ≠ lpB2 := by decide
@[simp] theorem dpj_lpA_ne_lpR : lpA ≠ lpR := by decide
@[simp] theorem dpj_lpA_ne_djA : lpA ≠ djA := by decide
@[simp] theorem dpj_lpA_ne_djB : lpA ≠ djB := by decide
@[simp] theorem dpj_lpA_ne_djN1 : lpA ≠ djN1 := by decide
@[simp] theorem dpj_lpA_ne_djP1 : lpA ≠ djP1 := by decide
@[simp] theorem dpj_lpA_ne_djI1 : lpA ≠ djI1 := by decide
@[simp] theorem dpj_lpA_ne_djN2 : lpA ≠ djN2 := by decide
@[simp] theorem dpj_lpA_ne_djP2 : lpA ≠ djP2 := by decide
@[simp] theorem dpj_lpA_ne_djI2 : lpA ≠ djI2 := by decide
@[simp] theorem dpj_lpA_ne_djR : lpA ≠ djR := by decide
@[simp] theorem dpj_lpA_ne_lFl : lpA ≠ lFl := by decide
@[simp] theorem dpj_lFl_ne_lpA : lFl ≠ lpA := by decide
@[simp] theorem dpj_lpA_ne_lDh : lpA ≠ lDh := by decide
@[simp] theorem dpj_lDh_ne_lpA : lDh ≠ lpA := by decide
@[simp] theorem dpj_lpA_ne_lDt : lpA ≠ lDt := by decide
@[simp] theorem dpj_lDt_ne_lpA : lDt ≠ lpA := by decide
@[simp] theorem dpj_lpA_ne_lDg : lpA ≠ lDg := by decide
@[simp] theorem dpj_lDg_ne_lpA : lDg ≠ lpA := by decide
@[simp] theorem dpj_lpA_ne_lDi : lpA ≠ lDi := by decide
@[simp] theorem dpj_lDi_ne_lpA : lDi ≠ lpA := by decide
@[simp] theorem dpj_lpA_ne_lRp : lpA ≠ lRp := by decide
@[simp] theorem dpj_lRp_ne_lpA : lRp ≠ lpA := by decide
@[simp] theorem dpj_lpA_ne_lRn : lpA ≠ lRn := by decide
@[simp] theorem dpj_lRn_ne_lpA : lRn ≠ lpA := by decide
@[simp] theorem dpj_lpA_ne_lFle : lpA ≠ lFle := by decide
@[simp] theorem dpj_lFle_ne_lpA : lFle ≠ lpA := by decide
@[simp] theorem dpj_lpA_ne_lKb : lpA ≠ lKb := by decide
@[simp] theorem dpj_lKb_ne_lpA : lKb ≠ lpA := by decide
@[simp] theorem dpj_lpA_ne_lDir : lpA ≠ lDir := by decide
@[simp] theorem dpj_lDir_ne_lpA : lDir ≠ lpA := by decide
@[simp] theorem dpj_lpA_ne_lFln : lpA ≠ lFln := by decide
@[simp] theorem dpj_lFln_ne_lpA : lFln ≠ lpA := by decide
@[simp] theorem dpj_lpA_ne_lFll : lpA ≠ lFll := by decide
@[simp] theorem dpj_lFll_ne_lpA : lFll ≠ lpA := by decide
@[simp] theorem dpj_lpA_ne_lFls : lpA ≠ lFls := by decide
@[simp] theorem dpj_lFls_ne_lpA : lFls ≠ lpA := by decide
@[simp] theorem dpj_lpA_ne_kFu : lpA ≠ kFu := by decide
@[simp] theorem dpj_kFu_ne_lpA : kFu ≠ lpA := by decide
@[simp] theorem dpj_lpA_ne_kD : lpA ≠ kD := by decide
@[simp] theorem dpj_kD_ne_lpA : kD ≠ lpA := by decide
@[simp] theorem dpj_lpB_ne_lpN : lpB ≠ lpN := by decide
@[simp] theorem dpj_lpB_ne_lpI : lpB ≠ lpI := by decide
@[simp] theorem dpj_lpB_ne_lpF : lpB ≠ lpF := by decide
@[simp] theorem dpj_lpB_ne_lpA : lpB ≠ lpA := by decide
@[simp] theorem dpj_lpB_ne_lpS : lpB ≠ lpS := by decide
@[simp] theorem dpj_lpB_ne_lpX : lpB ≠ lpX := by decide
@[simp] theorem dpj_lpB_ne_lpY : lpB ≠ lpY := by decide
@[simp] theorem dpj_lpB_ne_lpV : lpB ≠ lpV := by decide
@[simp] theorem dpj_lpB_ne_lpA2 : lpB ≠ lpA2 := by decide
@[simp] theorem dpj_lpB_ne_lpB2 : lpB ≠ lpB2 := by decide
@[simp] theorem dpj_lpB_ne_lpR : lpB ≠ lpR := by decide
@[simp] theorem dpj_lpB_ne_djA : lpB ≠ djA := by decide
@[simp] theorem dpj_lpB_ne_djB : lpB ≠ djB := by decide
@[simp] theorem dpj_lpB_ne_djN1 : lpB ≠ djN1 := by decide
@[simp] theorem dpj_lpB_ne_djP1 : lpB ≠ djP1 := by decide
@[simp] theorem dpj_lpB_ne_djI1 : lpB ≠ djI1 := by decide
@[simp] theorem dpj_lpB_ne_djN2 : lpB ≠ djN2 := by decide
@[simp] theorem dpj_lpB_ne_djP2 : lpB ≠ djP2 := by decide
@[simp] theorem dpj_lpB_ne_djI2 : lpB ≠ djI2 := by decide
@[simp] theorem dpj_lpB_ne_djR : lpB ≠ djR := by decide
@[simp] theorem dpj_lpB_ne_lFl : lpB ≠ lFl := by decide
@[simp] theorem dpj_lFl_ne_lpB : lFl ≠ lpB := by decide
@[simp] theorem dpj_lpB_ne_lDh : lpB ≠ lDh := by decide
@[simp] theorem dpj_lDh_ne_lpB : lDh ≠ lpB := by decide
@[simp] theorem dpj_lpB_ne_lDt : lpB ≠ lDt := by decide
@[simp] theorem dpj_lDt_ne_lpB : lDt ≠ lpB := by decide
@[simp] theorem dpj_lpB_ne_lDg : lpB ≠ lDg := by decide
@[simp] theorem dpj_lDg_ne_lpB : lDg ≠ lpB := by decide
@[simp] theorem dpj_lpB_ne_lDi : lpB ≠ lDi := by decide
@[simp] theorem dpj_lDi_ne_lpB : lDi ≠ lpB := by decide
@[simp] theorem dpj_lpB_ne_lRp : lpB ≠ lRp := by decide
@[simp] theorem dpj_lRp_ne_lpB : lRp ≠ lpB := by decide
@[simp] theorem dpj_lpB_ne_lRn : lpB ≠ lRn := by decide
@[simp] theorem dpj_lRn_ne_lpB : lRn ≠ lpB := by decide
@[simp] theorem dpj_lpB_ne_lFle : lpB ≠ lFle := by decide
@[simp] theorem dpj_lFle_ne_lpB : lFle ≠ lpB := by decide
@[simp] theorem dpj_lpB_ne_lKb : lpB ≠ lKb := by decide
@[simp] theorem dpj_lKb_ne_lpB : lKb ≠ lpB := by decide
@[simp] theorem dpj_lpB_ne_lDir : lpB ≠ lDir := by decide
@[simp] theorem dpj_lDir_ne_lpB : lDir ≠ lpB := by decide
@[simp] theorem dpj_lpB_ne_lFln : lpB ≠ lFln := by decide
@[simp] theorem dpj_lFln_ne_lpB : lFln ≠ lpB := by decide
@[simp] theorem dpj_lpB_ne_lFll : lpB ≠ lFll := by decide
@[simp] theorem dpj_lFll_ne_lpB : lFll ≠ lpB := by decide
@[simp] theorem dpj_lpB_ne_lFls : lpB ≠ lFls := by decide
@[simp] theorem dpj_lFls_ne_lpB : lFls ≠ lpB := by decide
@[simp] theorem dpj_lpB_ne_kFu : lpB ≠ kFu := by decide
@[simp] theorem dpj_kFu_ne_lpB : kFu ≠ lpB := by decide
@[simp] theorem dpj_lpB_ne_kD : lpB ≠ kD := by decide
@[simp] theorem dpj_kD_ne_lpB : kD ≠ lpB := by decide
@[simp] theorem dpj_lpS_ne_lpN : lpS ≠ lpN := by decide
@[simp] theorem dpj_lpS_ne_lpI : lpS ≠ lpI := by decide
@[simp] theorem dpj_lpS_ne_lpF : lpS ≠ lpF := by decide
@[simp] theorem dpj_lpS_ne_lpA : lpS ≠ lpA := by decide
@[simp] theorem dpj_lpS_ne_lpB : lpS ≠ lpB := by decide
@[simp] theorem dpj_lpS_ne_lpX : lpS ≠ lpX := by decide
@[simp] theorem dpj_lpS_ne_lpY : lpS ≠ lpY := by decide
@[simp] theorem dpj_lpS_ne_lpV : lpS ≠ lpV := by decide
@[simp] theorem dpj_lpS_ne_lpA2 : lpS ≠ lpA2 := by decide
@[simp] theorem dpj_lpS_ne_lpB2 : lpS ≠ lpB2 := by decide
@[simp] theorem dpj_lpS_ne_lpR : lpS ≠ lpR := by decide
@[simp] theorem dpj_lpS_ne_djA : lpS ≠ djA := by decide
@[simp] theorem dpj_lpS_ne_djB : lpS ≠ djB := by decide
@[simp] theorem dpj_lpS_ne_djN1 : lpS ≠ djN1 := by decide
@[simp] theorem dpj_lpS_ne_djP1 : lpS ≠ djP1 := by decide
@[simp] theorem dpj_lpS_ne_djI1 : lpS ≠ djI1 := by decide
@[simp] theorem dpj_lpS_ne_djN2 : lpS ≠ djN2 := by decide
@[simp] theorem dpj_lpS_ne_djP2 : lpS ≠ djP2 := by decide
@[simp] theorem dpj_lpS_ne_djI2 : lpS ≠ djI2 := by decide
@[simp] theorem dpj_lpS_ne_djR : lpS ≠ djR := by decide
@[simp] theorem dpj_lpS_ne_lFl : lpS ≠ lFl := by decide
@[simp] theorem dpj_lFl_ne_lpS : lFl ≠ lpS := by decide
@[simp] theorem dpj_lpS_ne_lDh : lpS ≠ lDh := by decide
@[simp] theorem dpj_lDh_ne_lpS : lDh ≠ lpS := by decide
@[simp] theorem dpj_lpS_ne_lDt : lpS ≠ lDt := by decide
@[simp] theorem dpj_lDt_ne_lpS : lDt ≠ lpS := by decide
@[simp] theorem dpj_lpS_ne_lDg : lpS ≠ lDg := by decide
@[simp] theorem dpj_lDg_ne_lpS : lDg ≠ lpS := by decide
@[simp] theorem dpj_lpS_ne_lDi : lpS ≠ lDi := by decide
@[simp] theorem dpj_lDi_ne_lpS : lDi ≠ lpS := by decide
@[simp] theorem dpj_lpS_ne_lRp : lpS ≠ lRp := by decide
@[simp] theorem dpj_lRp_ne_lpS : lRp ≠ lpS := by decide
@[simp] theorem dpj_lpS_ne_lRn : lpS ≠ lRn := by decide
@[simp] theorem dpj_lRn_ne_lpS : lRn ≠ lpS := by decide
@[simp] theorem dpj_lpS_ne_lFle : lpS ≠ lFle := by decide
@[simp] theorem dpj_lFle_ne_lpS : lFle ≠ lpS := by decide
@[simp] theorem dpj_lpS_ne_lKb : lpS ≠ lKb := by decide
@[simp] theorem dpj_lKb_ne_lpS : lKb ≠ lpS := by decide
@[simp] theorem dpj_lpS_ne_lDir : lpS ≠ lDir := by decide
@[simp] theorem dpj_lDir_ne_lpS : lDir ≠ lpS := by decide
@[simp] theorem dpj_lpS_ne_lFln : lpS ≠ lFln := by decide
@[simp] theorem dpj_lFln_ne_lpS : lFln ≠ lpS := by decide
@[simp] theorem dpj_lpS_ne_lFll : lpS ≠ lFll := by decide
@[simp] theorem dpj_lFll_ne_lpS : lFll ≠ lpS := by decide
@[simp] theorem dpj_lpS_ne_lFls : lpS ≠ lFls := by decide
@[simp] theorem dpj_lFls_ne_lpS : lFls ≠ lpS := by decide
@[simp] theorem dpj_lpS_ne_kFu : lpS ≠ kFu := by decide
@[simp] theorem dpj_kFu_ne_lpS : kFu ≠ lpS := by decide
@[simp] theorem dpj_lpS_ne_kD : lpS ≠ kD := by decide
@[simp] theorem dpj_kD_ne_lpS : kD ≠ lpS := by decide
@[simp] theorem dpj_lpX_ne_lpN : lpX ≠ lpN := by decide
@[simp] theorem dpj_lpX_ne_lpI : lpX ≠ lpI := by decide
@[simp] theorem dpj_lpX_ne_lpF : lpX ≠ lpF := by decide
@[simp] theorem dpj_lpX_ne_lpA : lpX ≠ lpA := by decide
@[simp] theorem dpj_lpX_ne_lpB : lpX ≠ lpB := by decide
@[simp] theorem dpj_lpX_ne_lpS : lpX ≠ lpS := by decide
@[simp] theorem dpj_lpX_ne_lpY : lpX ≠ lpY := by decide
@[simp] theorem dpj_lpX_ne_lpV : lpX ≠ lpV := by decide
@[simp] theorem dpj_lpX_ne_lpA2 : lpX ≠ lpA2 := by decide
@[simp] theorem dpj_lpX_ne_lpB2 : lpX ≠ lpB2 := by decide
@[simp] theorem dpj_lpX_ne_lpR : lpX ≠ lpR := by decide
@[simp] theorem dpj_lpX_ne_djA : lpX ≠ djA := by decide
@[simp] theorem dpj_lpX_ne_djB : lpX ≠ djB := by decide
@[simp] theorem dpj_lpX_ne_djN1 : lpX ≠ djN1 := by decide
@[simp] theorem dpj_lpX_ne_djP1 : lpX ≠ djP1 := by decide
@[simp] theorem dpj_lpX_ne_djI1 : lpX ≠ djI1 := by decide
@[simp] theorem dpj_lpX_ne_djN2 : lpX ≠ djN2 := by decide
@[simp] theorem dpj_lpX_ne_djP2 : lpX ≠ djP2 := by decide
@[simp] theorem dpj_lpX_ne_djI2 : lpX ≠ djI2 := by decide
@[simp] theorem dpj_lpX_ne_djR : lpX ≠ djR := by decide
@[simp] theorem dpj_lpX_ne_lFl : lpX ≠ lFl := by decide
@[simp] theorem dpj_lFl_ne_lpX : lFl ≠ lpX := by decide
@[simp] theorem dpj_lpX_ne_lDh : lpX ≠ lDh := by decide
@[simp] theorem dpj_lDh_ne_lpX : lDh ≠ lpX := by decide
@[simp] theorem dpj_lpX_ne_lDt : lpX ≠ lDt := by decide
@[simp] theorem dpj_lDt_ne_lpX : lDt ≠ lpX := by decide
@[simp] theorem dpj_lpX_ne_lDg : lpX ≠ lDg := by decide
@[simp] theorem dpj_lDg_ne_lpX : lDg ≠ lpX := by decide
@[simp] theorem dpj_lpX_ne_lDi : lpX ≠ lDi := by decide
@[simp] theorem dpj_lDi_ne_lpX : lDi ≠ lpX := by decide
@[simp] theorem dpj_lpX_ne_lRp : lpX ≠ lRp := by decide
@[simp] theorem dpj_lRp_ne_lpX : lRp ≠ lpX := by decide
@[simp] theorem dpj_lpX_ne_lRn : lpX ≠ lRn := by decide
@[simp] theorem dpj_lRn_ne_lpX : lRn ≠ lpX := by decide
@[simp] theorem dpj_lpX_ne_lFle : lpX ≠ lFle := by decide
@[simp] theorem dpj_lFle_ne_lpX : lFle ≠ lpX := by decide
@[simp] theorem dpj_lpX_ne_lKb : lpX ≠ lKb := by decide
@[simp] theorem dpj_lKb_ne_lpX : lKb ≠ lpX := by decide
@[simp] theorem dpj_lpX_ne_lDir : lpX ≠ lDir := by decide
@[simp] theorem dpj_lDir_ne_lpX : lDir ≠ lpX := by decide
@[simp] theorem dpj_lpX_ne_lFln : lpX ≠ lFln := by decide
@[simp] theorem dpj_lFln_ne_lpX : lFln ≠ lpX := by decide
@[simp] theorem dpj_lpX_ne_lFll : lpX ≠ lFll := by decide
@[simp] theorem dpj_lFll_ne_lpX : lFll ≠ lpX := by decide
@[simp] theorem dpj_lpX_ne_lFls : lpX ≠ lFls := by decide
@[simp] theorem dpj_lFls_ne_lpX : lFls ≠ lpX := by decide
@[simp] theorem dpj_lpX_ne_kFu : lpX ≠ kFu := by decide
@[simp] theorem dpj_kFu_ne_lpX : kFu ≠ lpX := by decide
@[simp] theorem dpj_lpX_ne_kD : lpX ≠ kD := by decide
@[simp] theorem dpj_kD_ne_lpX : kD ≠ lpX := by decide
@[simp] theorem dpj_lpY_ne_lpN : lpY ≠ lpN := by decide
@[simp] theorem dpj_lpY_ne_lpI : lpY ≠ lpI := by decide
@[simp] theorem dpj_lpY_ne_lpF : lpY ≠ lpF := by decide
@[simp] theorem dpj_lpY_ne_lpA : lpY ≠ lpA := by decide
@[simp] theorem dpj_lpY_ne_lpB : lpY ≠ lpB := by decide
@[simp] theorem dpj_lpY_ne_lpS : lpY ≠ lpS := by decide
@[simp] theorem dpj_lpY_ne_lpX : lpY ≠ lpX := by decide
@[simp] theorem dpj_lpY_ne_lpV : lpY ≠ lpV := by decide
@[simp] theorem dpj_lpY_ne_lpA2 : lpY ≠ lpA2 := by decide
@[simp] theorem dpj_lpY_ne_lpB2 : lpY ≠ lpB2 := by decide
@[simp] theorem dpj_lpY_ne_lpR : lpY ≠ lpR := by decide
@[simp] theorem dpj_lpY_ne_djA : lpY ≠ djA := by decide
@[simp] theorem dpj_lpY_ne_djB : lpY ≠ djB := by decide
@[simp] theorem dpj_lpY_ne_djN1 : lpY ≠ djN1 := by decide
@[simp] theorem dpj_lpY_ne_djP1 : lpY ≠ djP1 := by decide
@[simp] theorem dpj_lpY_ne_djI1 : lpY ≠ djI1 := by decide
@[simp] theorem dpj_lpY_ne_djN2 : lpY ≠ djN2 := by decide
@[simp] theorem dpj_lpY_ne_djP2 : lpY ≠ djP2 := by decide
@[simp] theorem dpj_lpY_ne_djI2 : lpY ≠ djI2 := by decide
@[simp] theorem dpj_lpY_ne_djR : lpY ≠ djR := by decide
@[simp] theorem dpj_lpY_ne_lFl : lpY ≠ lFl := by decide
@[simp] theorem dpj_lFl_ne_lpY : lFl ≠ lpY := by decide
@[simp] theorem dpj_lpY_ne_lDh : lpY ≠ lDh := by decide
@[simp] theorem dpj_lDh_ne_lpY : lDh ≠ lpY := by decide
@[simp] theorem dpj_lpY_ne_lDt : lpY ≠ lDt := by decide
@[simp] theorem dpj_lDt_ne_lpY : lDt ≠ lpY := by decide
@[simp] theorem dpj_lpY_ne_lDg : lpY ≠ lDg := by decide
@[simp] theorem dpj_lDg_ne_lpY : lDg ≠ lpY := by decide
@[simp] theorem dpj_lpY_ne_lDi : lpY ≠ lDi := by decide
@[simp] theorem dpj_lDi_ne_lpY : lDi ≠ lpY := by decide
@[simp] theorem dpj_lpY_ne_lRp : lpY ≠ lRp := by decide
@[simp] theorem dpj_lRp_ne_lpY : lRp ≠ lpY := by decide
@[simp] theorem dpj_lpY_ne_lRn : lpY ≠ lRn := by decide
@[simp] theorem dpj_lRn_ne_lpY : lRn ≠ lpY := by decide
@[simp] theorem dpj_lpY_ne_lFle : lpY ≠ lFle := by decide
@[simp] theorem dpj_lFle_ne_lpY : lFle ≠ lpY := by decide
@[simp] theorem dpj_lpY_ne_lKb : lpY ≠ lKb := by decide
@[simp] theorem dpj_lKb_ne_lpY : lKb ≠ lpY := by decide
@[simp] theorem dpj_lpY_ne_lDir : lpY ≠ lDir := by decide
@[simp] theorem dpj_lDir_ne_lpY : lDir ≠ lpY := by decide
@[simp] theorem dpj_lpY_ne_lFln : lpY ≠ lFln := by decide
@[simp] theorem dpj_lFln_ne_lpY : lFln ≠ lpY := by decide
@[simp] theorem dpj_lpY_ne_lFll : lpY ≠ lFll := by decide
@[simp] theorem dpj_lFll_ne_lpY : lFll ≠ lpY := by decide
@[simp] theorem dpj_lpY_ne_lFls : lpY ≠ lFls := by decide
@[simp] theorem dpj_lFls_ne_lpY : lFls ≠ lpY := by decide
@[simp] theorem dpj_lpY_ne_kFu : lpY ≠ kFu := by decide
@[simp] theorem dpj_kFu_ne_lpY : kFu ≠ lpY := by decide
@[simp] theorem dpj_lpY_ne_kD : lpY ≠ kD := by decide
@[simp] theorem dpj_kD_ne_lpY : kD ≠ lpY := by decide
@[simp] theorem dpj_lpV_ne_lpN : lpV ≠ lpN := by decide
@[simp] theorem dpj_lpV_ne_lpI : lpV ≠ lpI := by decide
@[simp] theorem dpj_lpV_ne_lpF : lpV ≠ lpF := by decide
@[simp] theorem dpj_lpV_ne_lpA : lpV ≠ lpA := by decide
@[simp] theorem dpj_lpV_ne_lpB : lpV ≠ lpB := by decide
@[simp] theorem dpj_lpV_ne_lpS : lpV ≠ lpS := by decide
@[simp] theorem dpj_lpV_ne_lpX : lpV ≠ lpX := by decide
@[simp] theorem dpj_lpV_ne_lpY : lpV ≠ lpY := by decide
@[simp] theorem dpj_lpV_ne_lpA2 : lpV ≠ lpA2 := by decide
@[simp] theorem dpj_lpV_ne_lpB2 : lpV ≠ lpB2 := by decide
@[simp] theorem dpj_lpV_ne_lpR : lpV ≠ lpR := by decide
@[simp] theorem dpj_lpV_ne_djA : lpV ≠ djA := by decide
@[simp] theorem dpj_lpV_ne_djB : lpV ≠ djB := by decide
@[simp] theorem dpj_lpV_ne_djN1 : lpV ≠ djN1 := by decide
@[simp] theorem dpj_lpV_ne_djP1 : lpV ≠ djP1 := by decide
@[simp] theorem dpj_lpV_ne_djI1 : lpV ≠ djI1 := by decide
@[simp] theorem dpj_lpV_ne_djN2 : lpV ≠ djN2 := by decide
@[simp] theorem dpj_lpV_ne_djP2 : lpV ≠ djP2 := by decide
@[simp] theorem dpj_lpV_ne_djI2 : lpV ≠ djI2 := by decide
@[simp] theorem dpj_lpV_ne_djR : lpV ≠ djR := by decide
@[simp] theorem dpj_lpV_ne_lFl : lpV ≠ lFl := by decide
@[simp] theorem dpj_lFl_ne_lpV : lFl ≠ lpV := by decide
@[simp] theorem dpj_lpV_ne_lDh : lpV ≠ lDh := by decide
@[simp] theorem dpj_lDh_ne_lpV : lDh ≠ lpV := by decide
@[simp] theorem dpj_lpV_ne_lDt : lpV ≠ lDt := by decide
@[simp] theorem dpj_lDt_ne_lpV : lDt ≠ lpV := by decide
@[simp] theorem dpj_lpV_ne_lDg : lpV ≠ lDg := by decide
@[simp] theorem dpj_lDg_ne_lpV : lDg ≠ lpV := by decide
@[simp] theorem dpj_lpV_ne_lDi : lpV ≠ lDi := by decide
@[simp] theorem dpj_lDi_ne_lpV : lDi ≠ lpV := by decide
@[simp] theorem dpj_lpV_ne_lRp : lpV ≠ lRp := by decide
@[simp] theorem dpj_lRp_ne_lpV : lRp ≠ lpV := by decide
@[simp] theorem dpj_lpV_ne_lRn : lpV ≠ lRn := by decide
@[simp] theorem dpj_lRn_ne_lpV : lRn ≠ lpV := by decide
@[simp] theorem dpj_lpV_ne_lFle : lpV ≠ lFle := by decide
@[simp] theorem dpj_lFle_ne_lpV : lFle ≠ lpV := by decide
@[simp] theorem dpj_lpV_ne_lKb : lpV ≠ lKb := by decide
@[simp] theorem dpj_lKb_ne_lpV : lKb ≠ lpV := by decide
@[simp] theorem dpj_lpV_ne_lDir : lpV ≠ lDir := by decide
@[simp] theorem dpj_lDir_ne_lpV : lDir ≠ lpV := by decide
@[simp] theorem dpj_lpV_ne_lFln : lpV ≠ lFln := by decide
@[simp] theorem dpj_lFln_ne_lpV : lFln ≠ lpV := by decide
@[simp] theorem dpj_lpV_ne_lFll : lpV ≠ lFll := by decide
@[simp] theorem dpj_lFll_ne_lpV : lFll ≠ lpV := by decide
@[simp] theorem dpj_lpV_ne_lFls : lpV ≠ lFls := by decide
@[simp] theorem dpj_lFls_ne_lpV : lFls ≠ lpV := by decide
@[simp] theorem dpj_lpV_ne_kFu : lpV ≠ kFu := by decide
@[simp] theorem dpj_kFu_ne_lpV : kFu ≠ lpV := by decide
@[simp] theorem dpj_lpV_ne_kD : lpV ≠ kD := by decide
@[simp] theorem dpj_kD_ne_lpV : kD ≠ lpV := by decide
@[simp] theorem dpj_lpA2_ne_lpN : lpA2 ≠ lpN := by decide
@[simp] theorem dpj_lpA2_ne_lpI : lpA2 ≠ lpI := by decide
@[simp] theorem dpj_lpA2_ne_lpF : lpA2 ≠ lpF := by decide
@[simp] theorem dpj_lpA2_ne_lpA : lpA2 ≠ lpA := by decide
@[simp] theorem dpj_lpA2_ne_lpB : lpA2 ≠ lpB := by decide
@[simp] theorem dpj_lpA2_ne_lpS : lpA2 ≠ lpS := by decide
@[simp] theorem dpj_lpA2_ne_lpX : lpA2 ≠ lpX := by decide
@[simp] theorem dpj_lpA2_ne_lpY : lpA2 ≠ lpY := by decide
@[simp] theorem dpj_lpA2_ne_lpV : lpA2 ≠ lpV := by decide
@[simp] theorem dpj_lpA2_ne_lpB2 : lpA2 ≠ lpB2 := by decide
@[simp] theorem dpj_lpA2_ne_lpR : lpA2 ≠ lpR := by decide
@[simp] theorem dpj_lpA2_ne_djA : lpA2 ≠ djA := by decide
@[simp] theorem dpj_lpA2_ne_djB : lpA2 ≠ djB := by decide
@[simp] theorem dpj_lpA2_ne_djN1 : lpA2 ≠ djN1 := by decide
@[simp] theorem dpj_lpA2_ne_djP1 : lpA2 ≠ djP1 := by decide
@[simp] theorem dpj_lpA2_ne_djI1 : lpA2 ≠ djI1 := by decide
@[simp] theorem dpj_lpA2_ne_djN2 : lpA2 ≠ djN2 := by decide
@[simp] theorem dpj_lpA2_ne_djP2 : lpA2 ≠ djP2 := by decide
@[simp] theorem dpj_lpA2_ne_djI2 : lpA2 ≠ djI2 := by decide
@[simp] theorem dpj_lpA2_ne_djR : lpA2 ≠ djR := by decide
@[simp] theorem dpj_lpA2_ne_lFl : lpA2 ≠ lFl := by decide
@[simp] theorem dpj_lFl_ne_lpA2 : lFl ≠ lpA2 := by decide
@[simp] theorem dpj_lpA2_ne_lDh : lpA2 ≠ lDh := by decide
@[simp] theorem dpj_lDh_ne_lpA2 : lDh ≠ lpA2 := by decide
@[simp] theorem dpj_lpA2_ne_lDt : lpA2 ≠ lDt := by decide
@[simp] theorem dpj_lDt_ne_lpA2 : lDt ≠ lpA2 := by decide
@[simp] theorem dpj_lpA2_ne_lDg : lpA2 ≠ lDg := by decide
@[simp] theorem dpj_lDg_ne_lpA2 : lDg ≠ lpA2 := by decide
@[simp] theorem dpj_lpA2_ne_lDi : lpA2 ≠ lDi := by decide
@[simp] theorem dpj_lDi_ne_lpA2 : lDi ≠ lpA2 := by decide
@[simp] theorem dpj_lpA2_ne_lRp : lpA2 ≠ lRp := by decide
@[simp] theorem dpj_lRp_ne_lpA2 : lRp ≠ lpA2 := by decide
@[simp] theorem dpj_lpA2_ne_lRn : lpA2 ≠ lRn := by decide
@[simp] theorem dpj_lRn_ne_lpA2 : lRn ≠ lpA2 := by decide
@[simp] theorem dpj_lpA2_ne_lFle : lpA2 ≠ lFle := by decide
@[simp] theorem dpj_lFle_ne_lpA2 : lFle ≠ lpA2 := by decide
@[simp] theorem dpj_lpA2_ne_lKb : lpA2 ≠ lKb := by decide
@[simp] theorem dpj_lKb_ne_lpA2 : lKb ≠ lpA2 := by decide
@[simp] theorem dpj_lpA2_ne_lDir : lpA2 ≠ lDir := by decide
@[simp] theorem dpj_lDir_ne_lpA2 : lDir ≠ lpA2 := by decide
@[simp] theorem dpj_lpA2_ne_lFln : lpA2 ≠ lFln := by decide
@[simp] theorem dpj_lFln_ne_lpA2 : lFln ≠ lpA2 := by decide
@[simp] theorem dpj_lpA2_ne_lFll : lpA2 ≠ lFll := by decide
@[simp] theorem dpj_lFll_ne_lpA2 : lFll ≠ lpA2 := by decide
@[simp] theorem dpj_lpA2_ne_lFls : lpA2 ≠ lFls := by decide
@[simp] theorem dpj_lFls_ne_lpA2 : lFls ≠ lpA2 := by decide
@[simp] theorem dpj_lpA2_ne_kFu : lpA2 ≠ kFu := by decide
@[simp] theorem dpj_kFu_ne_lpA2 : kFu ≠ lpA2 := by decide
@[simp] theorem dpj_lpA2_ne_kD : lpA2 ≠ kD := by decide
@[simp] theorem dpj_kD_ne_lpA2 : kD ≠ lpA2 := by decide
@[simp] theorem dpj_lpB2_ne_lpN : lpB2 ≠ lpN := by decide
@[simp] theorem dpj_lpB2_ne_lpI : lpB2 ≠ lpI := by decide
@[simp] theorem dpj_lpB2_ne_lpF : lpB2 ≠ lpF := by decide
@[simp] theorem dpj_lpB2_ne_lpA : lpB2 ≠ lpA := by decide
@[simp] theorem dpj_lpB2_ne_lpB : lpB2 ≠ lpB := by decide
@[simp] theorem dpj_lpB2_ne_lpS : lpB2 ≠ lpS := by decide
@[simp] theorem dpj_lpB2_ne_lpX : lpB2 ≠ lpX := by decide
@[simp] theorem dpj_lpB2_ne_lpY : lpB2 ≠ lpY := by decide
@[simp] theorem dpj_lpB2_ne_lpV : lpB2 ≠ lpV := by decide
@[simp] theorem dpj_lpB2_ne_lpA2 : lpB2 ≠ lpA2 := by decide
@[simp] theorem dpj_lpB2_ne_lpR : lpB2 ≠ lpR := by decide
@[simp] theorem dpj_lpB2_ne_djA : lpB2 ≠ djA := by decide
@[simp] theorem dpj_lpB2_ne_djB : lpB2 ≠ djB := by decide
@[simp] theorem dpj_lpB2_ne_djN1 : lpB2 ≠ djN1 := by decide
@[simp] theorem dpj_lpB2_ne_djP1 : lpB2 ≠ djP1 := by decide
@[simp] theorem dpj_lpB2_ne_djI1 : lpB2 ≠ djI1 := by decide
@[simp] theorem dpj_lpB2_ne_djN2 : lpB2 ≠ djN2 := by decide
@[simp] theorem dpj_lpB2_ne_djP2 : lpB2 ≠ djP2 := by decide
@[simp] theorem dpj_lpB2_ne_djI2 : lpB2 ≠ djI2 := by decide
@[simp] theorem dpj_lpB2_ne_djR : lpB2 ≠ djR := by decide
@[simp] theorem dpj_lpB2_ne_lFl : lpB2 ≠ lFl := by decide
@[simp] theorem dpj_lFl_ne_lpB2 : lFl ≠ lpB2 := by decide
@[simp] theorem dpj_lpB2_ne_lDh : lpB2 ≠ lDh := by decide
@[simp] theorem dpj_lDh_ne_lpB2 : lDh ≠ lpB2 := by decide
@[simp] theorem dpj_lpB2_ne_lDt : lpB2 ≠ lDt := by decide
@[simp] theorem dpj_lDt_ne_lpB2 : lDt ≠ lpB2 := by decide
@[simp] theorem dpj_lpB2_ne_lDg : lpB2 ≠ lDg := by decide
@[simp] theorem dpj_lDg_ne_lpB2 : lDg ≠ lpB2 := by decide
@[simp] theorem dpj_lpB2_ne_lDi : lpB2 ≠ lDi := by decide
@[simp] theorem dpj_lDi_ne_lpB2 : lDi ≠ lpB2 := by decide
@[simp] theorem dpj_lpB2_ne_lRp : lpB2 ≠ lRp := by decide
@[simp] theorem dpj_lRp_ne_lpB2 : lRp ≠ lpB2 := by decide
@[simp] theorem dpj_lpB2_ne_lRn : lpB2 ≠ lRn := by decide
@[simp] theorem dpj_lRn_ne_lpB2 : lRn ≠ lpB2 := by decide
@[simp] theorem dpj_lpB2_ne_lFle : lpB2 ≠ lFle := by decide
@[simp] theorem dpj_lFle_ne_lpB2 : lFle ≠ lpB2 := by decide
@[simp] theorem dpj_lpB2_ne_lKb : lpB2 ≠ lKb := by decide
@[simp] theorem dpj_lKb_ne_lpB2 : lKb ≠ lpB2 := by decide
@[simp] theorem dpj_lpB2_ne_lDir : lpB2 ≠ lDir := by decide
@[simp] theorem dpj_lDir_ne_lpB2 : lDir ≠ lpB2 := by decide
@[simp] theorem dpj_lpB2_ne_lFln : lpB2 ≠ lFln := by decide
@[simp] theorem dpj_lFln_ne_lpB2 : lFln ≠ lpB2 := by decide
@[simp] theorem dpj_lpB2_ne_lFll : lpB2 ≠ lFll := by decide
@[simp] theorem dpj_lFll_ne_lpB2 : lFll ≠ lpB2 := by decide
@[simp] theorem dpj_lpB2_ne_lFls : lpB2 ≠ lFls := by decide
@[simp] theorem dpj_lFls_ne_lpB2 : lFls ≠ lpB2 := by decide
@[simp] theorem dpj_lpB2_ne_kFu : lpB2 ≠ kFu := by decide
@[simp] theorem dpj_kFu_ne_lpB2 : kFu ≠ lpB2 := by decide
@[simp] theorem dpj_lpB2_ne_kD : lpB2 ≠ kD := by decide
@[simp] theorem dpj_kD_ne_lpB2 : kD ≠ lpB2 := by decide
@[simp] theorem dpj_lpR_ne_lpN : lpR ≠ lpN := by decide
@[simp] theorem dpj_lpR_ne_lpI : lpR ≠ lpI := by decide
@[simp] theorem dpj_lpR_ne_lpF : lpR ≠ lpF := by decide
@[simp] theorem dpj_lpR_ne_lpA : lpR ≠ lpA := by decide
@[simp] theorem dpj_lpR_ne_lpB : lpR ≠ lpB := by decide
@[simp] theorem dpj_lpR_ne_lpS : lpR ≠ lpS := by decide
@[simp] theorem dpj_lpR_ne_lpX : lpR ≠ lpX := by decide
@[simp] theorem dpj_lpR_ne_lpY : lpR ≠ lpY := by decide
@[simp] theorem dpj_lpR_ne_lpV : lpR ≠ lpV := by decide
@[simp] theorem dpj_lpR_ne_lpA2 : lpR ≠ lpA2 := by decide
@[simp] theorem dpj_lpR_ne_lpB2 : lpR ≠ lpB2 := by decide
@[simp] theorem dpj_lpR_ne_djA : lpR ≠ djA := by decide
@[simp] theorem dpj_lpR_ne_djB : lpR ≠ djB := by decide
@[simp] theorem dpj_lpR_ne_djN1 : lpR ≠ djN1 := by decide
@[simp] theorem dpj_lpR_ne_djP1 : lpR ≠ djP1 := by decide
@[simp] theorem dpj_lpR_ne_djI1 : lpR ≠ djI1 := by decide
@[simp] theorem dpj_lpR_ne_djN2 : lpR ≠ djN2 := by decide
@[simp] theorem dpj_lpR_ne_djP2 : lpR ≠ djP2 := by decide
@[simp] theorem dpj_lpR_ne_djI2 : lpR ≠ djI2 := by decide
@[simp] theorem dpj_lpR_ne_djR : lpR ≠ djR := by decide
@[simp] theorem dpj_lpR_ne_lFl : lpR ≠ lFl := by decide
@[simp] theorem dpj_lFl_ne_lpR : lFl ≠ lpR := by decide
@[simp] theorem dpj_lpR_ne_lDh : lpR ≠ lDh := by decide
@[simp] theorem dpj_lDh_ne_lpR : lDh ≠ lpR := by decide
@[simp] theorem dpj_lpR_ne_lDt : lpR ≠ lDt := by decide
@[simp] theorem dpj_lDt_ne_lpR : lDt ≠ lpR := by decide
@[simp] theorem dpj_lpR_ne_lDg : lpR ≠ lDg := by decide
@[simp] theorem dpj_lDg_ne_lpR : lDg ≠ lpR := by decide
@[simp] theorem dpj_lpR_ne_lDi : lpR ≠ lDi := by decide
@[simp] theorem dpj_lDi_ne_lpR : lDi ≠ lpR := by decide
@[simp] theorem dpj_lpR_ne_lRp : lpR ≠ lRp := by decide
@[simp] theorem dpj_lRp_ne_lpR : lRp ≠ lpR := by decide
@[simp] theorem dpj_lpR_ne_lRn : lpR ≠ lRn := by decide
@[simp] theorem dpj_lRn_ne_lpR : lRn ≠ lpR := by decide
@[simp] theorem dpj_lpR_ne_lFle : lpR ≠ lFle := by decide
@[simp] theorem dpj_lFle_ne_lpR : lFle ≠ lpR := by decide
@[simp] theorem dpj_lpR_ne_lKb : lpR ≠ lKb := by decide
@[simp] theorem dpj_lKb_ne_lpR : lKb ≠ lpR := by decide
@[simp] theorem dpj_lpR_ne_lDir : lpR ≠ lDir := by decide
@[simp] theorem dpj_lDir_ne_lpR : lDir ≠ lpR := by decide
@[simp] theorem dpj_lpR_ne_lFln : lpR ≠ lFln := by decide
@[simp] theorem dpj_lFln_ne_lpR : lFln ≠ lpR := by decide
@[simp] theorem dpj_lpR_ne_lFll : lpR ≠ lFll := by decide
@[simp] theorem dpj_lFll_ne_lpR : lFll ≠ lpR := by decide
@[simp] theorem dpj_lpR_ne_lFls : lpR ≠ lFls := by decide
@[simp] theorem dpj_lFls_ne_lpR : lFls ≠ lpR := by decide
@[simp] theorem dpj_lpR_ne_kFu : lpR ≠ kFu := by decide
@[simp] theorem dpj_kFu_ne_lpR : kFu ≠ lpR := by decide
@[simp] theorem dpj_lpR_ne_kD : lpR ≠ kD := by decide
@[simp] theorem dpj_kD_ne_lpR : kD ≠ lpR := by decide
@[simp] theorem dpj_djA_ne_lpN : djA ≠ lpN := by decide
@[simp] theorem dpj_djA_ne_lpI : djA ≠ lpI := by decide
@[simp] theorem dpj_djA_ne_lpF : djA ≠ lpF := by decide
@[simp] theorem dpj_djA_ne_lpA : djA ≠ lpA := by decide
@[simp] theorem dpj_djA_ne_lpB : djA ≠ lpB := by decide
@[simp] theorem dpj_djA_ne_lpS : djA ≠ lpS := by decide
@[simp] theorem dpj_djA_ne_lpX : djA ≠ lpX := by decide
@[simp] theorem dpj_djA_ne_lpY : djA ≠ lpY := by decide
@[simp] theorem dpj_djA_ne_lpV : djA ≠ lpV := by decide
@[simp] theorem dpj_djA_ne_lpA2 : djA ≠ lpA2 := by decide
@[simp] theorem dpj_djA_ne_lpB2 : djA ≠ lpB2 := by decide
@[simp] theorem dpj_djA_ne_lpR : djA ≠ lpR := by decide
@[simp] theorem dpj_djA_ne_djB : djA ≠ djB := by decide
@[simp] theorem dpj_djA_ne_djN1 : djA ≠ djN1 := by decide
@[simp] theorem dpj_djA_ne_djP1 : djA ≠ djP1 := by decide
@[simp] theorem dpj_djA_ne_djI1 : djA ≠ djI1 := by decide
@[simp] theorem dpj_djA_ne_djN2 : djA ≠ djN2 := by decide
@[simp] theorem dpj_djA_ne_djP2 : djA ≠ djP2 := by decide
@[simp] theorem dpj_djA_ne_djI2 : djA ≠ djI2 := by decide
@[simp] theorem dpj_djA_ne_djR : djA ≠ djR := by decide
@[simp] theorem dpj_djA_ne_lFl : djA ≠ lFl := by decide
@[simp] theorem dpj_lFl_ne_djA : lFl ≠ djA := by decide
@[simp] theorem dpj_djA_ne_lDh : djA ≠ lDh := by decide
@[simp] theorem dpj_lDh_ne_djA : lDh ≠ djA := by decide
@[simp] theorem dpj_djA_ne_lDt : djA ≠ lDt := by decide
@[simp] theorem dpj_lDt_ne_djA : lDt ≠ djA := by decide
@[simp] theorem dpj_djA_ne_lDg : djA ≠ lDg := by decide
@[simp] theorem dpj_lDg_ne_djA : lDg ≠ djA := by decide
@[simp] theorem dpj_djA_ne_lDi : djA ≠ lDi := by decide
@[simp] theorem dpj_lDi_ne_djA : lDi ≠ djA := by decide
@[simp] theorem dpj_djA_ne_lRp : djA ≠ lRp := by decide
@[simp] theorem dpj_lRp_ne_djA : lRp ≠ djA := by decide
@[simp] theorem dpj_djA_ne_lRn : djA ≠ lRn := by decide
@[simp] theorem dpj_lRn_ne_djA : lRn ≠ djA := by decide
@[simp] theorem dpj_djA_ne_lFle : djA ≠ lFle := by decide
@[simp] theorem dpj_lFle_ne_djA : lFle ≠ djA := by decide
@[simp] theorem dpj_djA_ne_lKb : djA ≠ lKb := by decide
@[simp] theorem dpj_lKb_ne_djA : lKb ≠ djA := by decide
@[simp] theorem dpj_djA_ne_lDir : djA ≠ lDir := by decide
@[simp] theorem dpj_lDir_ne_djA : lDir ≠ djA := by decide
@[simp] theorem dpj_djA_ne_lFln : djA ≠ lFln := by decide
@[simp] theorem dpj_lFln_ne_djA : lFln ≠ djA := by decide
@[simp] theorem dpj_djA_ne_lFll : djA ≠ lFll := by decide
@[simp] theorem dpj_lFll_ne_djA : lFll ≠ djA := by decide
@[simp] theorem dpj_djA_ne_lFls : djA ≠ lFls := by decide
@[simp] theorem dpj_lFls_ne_djA : lFls ≠ djA := by decide
@[simp] theorem dpj_djA_ne_kFu : djA ≠ kFu := by decide
@[simp] theorem dpj_kFu_ne_djA : kFu ≠ djA := by decide
@[simp] theorem dpj_djA_ne_kD : djA ≠ kD := by decide
@[simp] theorem dpj_kD_ne_djA : kD ≠ djA := by decide
@[simp] theorem dpj_djB_ne_lpN : djB ≠ lpN := by decide
@[simp] theorem dpj_djB_ne_lpI : djB ≠ lpI := by decide
@[simp] theorem dpj_djB_ne_lpF : djB ≠ lpF := by decide
@[simp] theorem dpj_djB_ne_lpA : djB ≠ lpA := by decide
@[simp] theorem dpj_djB_ne_lpB : djB ≠ lpB := by decide
@[simp] theorem dpj_djB_ne_lpS : djB ≠ lpS := by decide
@[simp] theorem dpj_djB_ne_lpX : djB ≠ lpX := by decide
@[simp] theorem dpj_djB_ne_lpY : djB ≠ lpY := by decide
@[simp] theorem dpj_djB_ne_lpV : djB ≠ lpV := by decide
@[simp] theorem dpj_djB_ne_lpA2 : djB ≠ lpA2 := by decide
@[simp] theorem dpj_djB_ne_lpB2 : djB ≠ lpB2 := by decide
@[simp] theorem dpj_djB_ne_lpR : djB ≠ lpR := by decide
@[simp] theorem dpj_djB_ne_djA : djB ≠ djA := by decide
@[simp] theorem dpj_djB_ne_djN1 : djB ≠ djN1 := by decide
@[simp] theorem dpj_djB_ne_djP1 : djB ≠ djP1 := by decide
@[simp] theorem dpj_djB_ne_djI1 : djB ≠ djI1 := by decide
@[simp] theorem dpj_djB_ne_djN2 : djB ≠ djN2 := by decide
@[simp] theorem dpj_djB_ne_djP2 : djB ≠ djP2 := by decide
@[simp] theorem dpj_djB_ne_djI2 : djB ≠ djI2 := by decide
@[simp] theorem dpj_djB_ne_djR : djB ≠ djR := by decide
@[simp] theorem dpj_djB_ne_lFl : djB ≠ lFl := by decide
@[simp] theorem dpj_lFl_ne_djB : lFl ≠ djB := by decide
@[simp] theorem dpj_djB_ne_lDh : djB ≠ lDh := by decide
@[simp] theorem dpj_lDh_ne_djB : lDh ≠ djB := by decide
@[simp] theorem dpj_djB_ne_lDt : djB ≠ lDt := by decide
@[simp] theorem dpj_lDt_ne_djB : lDt ≠ djB := by decide
@[simp] theorem dpj_djB_ne_lDg : djB ≠ lDg := by decide
@[simp] theorem dpj_lDg_ne_djB : lDg ≠ djB := by decide
@[simp] theorem dpj_djB_ne_lDi : djB ≠ lDi := by decide
@[simp] theorem dpj_lDi_ne_djB : lDi ≠ djB := by decide
@[simp] theorem dpj_djB_ne_lRp : djB ≠ lRp := by decide
@[simp] theorem dpj_lRp_ne_djB : lRp ≠ djB := by decide
@[simp] theorem dpj_djB_ne_lRn : djB ≠ lRn := by decide
@[simp] theorem dpj_lRn_ne_djB : lRn ≠ djB := by decide
@[simp] theorem dpj_djB_ne_lFle : djB ≠ lFle := by decide
@[simp] theorem dpj_lFle_ne_djB : lFle ≠ djB := by decide
@[simp] theorem dpj_djB_ne_lKb : djB ≠ lKb := by decide
@[simp] theorem dpj_lKb_ne_djB : lKb ≠ djB := by decide
@[simp] theorem dpj_djB_ne_lDir : djB ≠ lDir := by decide
@[simp] theorem dpj_lDir_ne_djB : lDir ≠ djB := by decide
@[simp] theorem dpj_djB_ne_lFln : djB ≠ lFln := by decide
@[simp] theorem dpj_lFln_ne_djB : lFln ≠ djB := by decide
@[simp] theorem dpj_djB_ne_lFll : djB ≠ lFll := by decide
@[simp] theorem dpj_lFll_ne_djB : lFll ≠ djB := by decide
@[simp] theorem dpj_djB_ne_lFls : djB ≠ lFls := by decide
@[simp] theorem dpj_lFls_ne_djB : lFls ≠ djB := by decide
@[simp] theorem dpj_djB_ne_kFu : djB ≠ kFu := by decide
@[simp] theorem dpj_kFu_ne_djB : kFu ≠ djB := by decide
@[simp] theorem dpj_djB_ne_kD : djB ≠ kD := by decide
@[simp] theorem dpj_kD_ne_djB : kD ≠ djB := by decide
@[simp] theorem dpj_djN1_ne_lpN : djN1 ≠ lpN := by decide
@[simp] theorem dpj_djN1_ne_lpI : djN1 ≠ lpI := by decide
@[simp] theorem dpj_djN1_ne_lpF : djN1 ≠ lpF := by decide
@[simp] theorem dpj_djN1_ne_lpA : djN1 ≠ lpA := by decide
@[simp] theorem dpj_djN1_ne_lpB : djN1 ≠ lpB := by decide
@[simp] theorem dpj_djN1_ne_lpS : djN1 ≠ lpS := by decide
@[simp] theorem dpj_djN1_ne_lpX : djN1 ≠ lpX := by decide
@[simp] theorem dpj_djN1_ne_lpY : djN1 ≠ lpY := by decide
@[simp] theorem dpj_djN1_ne_lpV : djN1 ≠ lpV := by decide
@[simp] theorem dpj_djN1_ne_lpA2 : djN1 ≠ lpA2 := by decide
@[simp] theorem dpj_djN1_ne_lpB2 : djN1 ≠ lpB2 := by decide
@[simp] theorem dpj_djN1_ne_lpR : djN1 ≠ lpR := by decide
@[simp] theorem dpj_djN1_ne_djA : djN1 ≠ djA := by decide
@[simp] theorem dpj_djN1_ne_djB : djN1 ≠ djB := by decide
@[simp] theorem dpj_djN1_ne_djP1 : djN1 ≠ djP1 := by decide
@[simp] theorem dpj_djN1_ne_djI1 : djN1 ≠ djI1 := by decide
@[simp] theorem dpj_djN1_ne_djN2 : djN1 ≠ djN2 := by decide
@[simp] theorem dpj_djN1_ne_djP2 : djN1 ≠ djP2 := by decide
@[simp] theorem dpj_djN1_ne_djI2 : djN1 ≠ djI2 := by decide
@[simp] theorem dpj_djN1_ne_djR : djN1 ≠ djR := by decide
@[simp] theorem dpj_djN1_ne_lFl : djN1 ≠ lFl := by decide
@[simp] theorem dpj_lFl_ne_djN1 : lFl ≠ djN1 := by decide
@[simp] theorem dpj_djN1_ne_lDh : djN1 ≠ lDh := by decide
@[simp] theorem dpj_lDh_ne_djN1 : lDh ≠ djN1 := by decide
@[simp] theorem dpj_djN1_ne_lDt : djN1 ≠ lDt := by decide
@[simp] theorem dpj_lDt_ne_djN1 : lDt ≠ djN1 := by decide
@[simp] theorem dpj_djN1_ne_lDg : djN1 ≠ lDg := by decide
@[simp] theorem dpj_lDg_ne_djN1 : lDg ≠ djN1 := by decide
@[simp] theorem dpj_djN1_ne_lDi : djN1 ≠ lDi := by decide
@[simp] theorem dpj_lDi_ne_djN1 : lDi ≠ djN1 := by decide
@[simp] theorem dpj_djN1_ne_lRp : djN1 ≠ lRp := by decide
@[simp] theorem dpj_lRp_ne_djN1 : lRp ≠ djN1 := by decide
@[simp] theorem dpj_djN1_ne_lRn : djN1 ≠ lRn := by decide
@[simp] theorem dpj_lRn_ne_djN1 : lRn ≠ djN1 := by decide
@[simp] theorem dpj_djN1_ne_lFle : djN1 ≠ lFle := by decide
@[simp] theorem dpj_lFle_ne_djN1 : lFle ≠ djN1 := by decide
@[simp] theorem dpj_djN1_ne_lKb : djN1 ≠ lKb := by decide
@[simp] theorem dpj_lKb_ne_djN1 : lKb ≠ djN1 := by decide
@[simp] theorem dpj_djN1_ne_lDir : djN1 ≠ lDir := by decide
@[simp] theorem dpj_lDir_ne_djN1 : lDir ≠ djN1 := by decide
@[simp] theorem dpj_djN1_ne_lFln : djN1 ≠ lFln := by decide
@[simp] theorem dpj_lFln_ne_djN1 : lFln ≠ djN1 := by decide
@[simp] theorem dpj_djN1_ne_lFll : djN1 ≠ lFll := by decide
@[simp] theorem dpj_lFll_ne_djN1 : lFll ≠ djN1 := by decide
@[simp] theorem dpj_djN1_ne_lFls : djN1 ≠ lFls := by decide
@[simp] theorem dpj_lFls_ne_djN1 : lFls ≠ djN1 := by decide
@[simp] theorem dpj_djN1_ne_kFu : djN1 ≠ kFu := by decide
@[simp] theorem dpj_kFu_ne_djN1 : kFu ≠ djN1 := by decide
@[simp] theorem dpj_djN1_ne_kD : djN1 ≠ kD := by decide
@[simp] theorem dpj_kD_ne_djN1 : kD ≠ djN1 := by decide
@[simp] theorem dpj_djP1_ne_lpN : djP1 ≠ lpN := by decide
@[simp] theorem dpj_djP1_ne_lpI : djP1 ≠ lpI := by decide
@[simp] theorem dpj_djP1_ne_lpF : djP1 ≠ lpF := by decide
@[simp] theorem dpj_djP1_ne_lpA : djP1 ≠ lpA := by decide
@[simp] theorem dpj_djP1_ne_lpB : djP1 ≠ lpB := by decide
@[simp] theorem dpj_djP1_ne_lpS : djP1 ≠ lpS := by decide
@[simp] theorem dpj_djP1_ne_lpX : djP1 ≠ lpX := by decide
@[simp] theorem dpj_djP1_ne_lpY : djP1 ≠ lpY := by decide
@[simp] theorem dpj_djP1_ne_lpV : djP1 ≠ lpV := by decide
@[simp] theorem dpj_djP1_ne_lpA2 : djP1 ≠ lpA2 := by decide
@[simp] theorem dpj_djP1_ne_lpB2 : djP1 ≠ lpB2 := by decide
@[simp] theorem dpj_djP1_ne_lpR : djP1 ≠ lpR := by decide
@[simp] theorem dpj_djP1_ne_djA : djP1 ≠ djA := by decide
@[simp] theorem dpj_djP1_ne_djB : djP1 ≠ djB := by decide
@[simp] theorem dpj_djP1_ne_djN1 : djP1 ≠ djN1 := by decide
@[simp] theorem dpj_djP1_ne_djI1 : djP1 ≠ djI1 := by decide
@[simp] theorem dpj_djP1_ne_djN2 : djP1 ≠ djN2 := by decide
@[simp] theorem dpj_djP1_ne_djP2 : djP1 ≠ djP2 := by decide
@[simp] theorem dpj_djP1_ne_djI2 : djP1 ≠ djI2 := by decide
@[simp] theorem dpj_djP1_ne_djR : djP1 ≠ djR := by decide
@[simp] theorem dpj_djP1_ne_lFl : djP1 ≠ lFl := by decide
@[simp] theorem dpj_lFl_ne_djP1 : lFl ≠ djP1 := by decide
@[simp] theorem dpj_djP1_ne_lDh : djP1 ≠ lDh := by decide
@[simp] theorem dpj_lDh_ne_djP1 : lDh ≠ djP1 := by decide
@[simp] theorem dpj_djP1_ne_lDt : djP1 ≠ lDt := by decide
@[simp] theorem dpj_lDt_ne_djP1 : lDt ≠ djP1 := by decide
@[simp] theorem dpj_djP1_ne_lDg : djP1 ≠ lDg := by decide
@[simp] theorem dpj_lDg_ne_djP1 : lDg ≠ djP1 := by decide
@[simp] theorem dpj_djP1_ne_lDi : djP1 ≠ lDi := by decide
@[simp] theorem dpj_lDi_ne_djP1 : lDi ≠ djP1 := by decide
@[simp] theorem dpj_djP1_ne_lRp : djP1 ≠ lRp := by decide
@[simp] theorem dpj_lRp_ne_djP1 : lRp ≠ djP1 := by decide
@[simp] theorem dpj_djP1_ne_lRn : djP1 ≠ lRn := by decide
@[simp] theorem dpj_lRn_ne_djP1 : lRn ≠ djP1 := by decide
@[simp] theorem dpj_djP1_ne_lFle : djP1 ≠ lFle := by decide
@[simp] theorem dpj_lFle_ne_djP1 : lFle ≠ djP1 := by decide
@[simp] theorem dpj_djP1_ne_lKb : djP1 ≠ lKb := by decide
@[simp] theorem dpj_lKb_ne_djP1 : lKb ≠ djP1 := by decide
@[simp] theorem dpj_djP1_ne_lDir : djP1 ≠ lDir := by decide
@[simp] theorem dpj_lDir_ne_djP1 : lDir ≠ djP1 := by decide
@[simp] theorem dpj_djP1_ne_lFln : djP1 ≠ lFln := by decide
@[simp] theorem dpj_lFln_ne_djP1 : lFln ≠ djP1 := by decide
@[simp] theorem dpj_djP1_ne_lFll : djP1 ≠ lFll := by decide
@[simp] theorem dpj_lFll_ne_djP1 : lFll ≠ djP1 := by decide
@[simp] theorem dpj_djP1_ne_lFls : djP1 ≠ lFls := by decide
@[simp] theorem dpj_lFls_ne_djP1 : lFls ≠ djP1 := by decide
@[simp] theorem dpj_djP1_ne_kFu : djP1 ≠ kFu := by decide
@[simp] theorem dpj_kFu_ne_djP1 : kFu ≠ djP1 := by decide
@[simp] theorem dpj_djP1_ne_kD : djP1 ≠ kD := by decide
@[simp] theorem dpj_kD_ne_djP1 : kD ≠ djP1 := by decide
@[simp] theorem dpj_djI1_ne_lpN : djI1 ≠ lpN := by decide
@[simp] theorem dpj_djI1_ne_lpI : djI1 ≠ lpI := by decide
@[simp] theorem dpj_djI1_ne_lpF : djI1 ≠ lpF := by decide
@[simp] theorem dpj_djI1_ne_lpA : djI1 ≠ lpA := by decide
@[simp] theorem dpj_djI1_ne_lpB : djI1 ≠ lpB := by decide
@[simp] theorem dpj_djI1_ne_lpS : djI1 ≠ lpS := by decide
@[simp] theorem dpj_djI1_ne_lpX : djI1 ≠ lpX := by decide
@[simp] theorem dpj_djI1_ne_lpY : djI1 ≠ lpY := by decide
@[simp] theorem dpj_djI1_ne_lpV : djI1 ≠ lpV := by decide
@[simp] theorem dpj_djI1_ne_lpA2 : djI1 ≠ lpA2 := by decide
@[simp] theorem dpj_djI1_ne_lpB2 : djI1 ≠ lpB2 := by decide
@[simp] theorem dpj_djI1_ne_lpR : djI1 ≠ lpR := by decide
@[simp] theorem dpj_djI1_ne_djA : djI1 ≠ djA := by decide
@[simp] theorem dpj_djI1_ne_djB : djI1 ≠ djB := by decide
@[simp] theorem dpj_djI1_ne_djN1 : djI1 ≠ djN1 := by decide
@[simp] theorem dpj_djI1_ne_djP1 : djI1 ≠ djP1 := by decide
@[simp] theorem dpj_djI1_ne_djN2 : djI1 ≠ djN2 := by decide
@[simp] theorem dpj_djI1_ne_djP2 : djI1 ≠ djP2 := by decide
@[simp] theorem dpj_djI1_ne_djI2 : djI1 ≠ djI2 := by decide
@[simp] theorem dpj_djI1_ne_djR : djI1 ≠ djR := by decide
@[simp] theorem dpj_djI1_ne_lFl : djI1 ≠ lFl := by decide
@[simp] theorem dpj_lFl_ne_djI1 : lFl ≠ djI1 := by decide
@[simp] theorem dpj_djI1_ne_lDh : djI1 ≠ lDh := by decide
@[simp] theorem dpj_lDh_ne_djI1 : lDh ≠ djI1 := by decide
@[simp] theorem dpj_djI1_ne_lDt : djI1 ≠ lDt := by decide
@[simp] theorem dpj_lDt_ne_djI1 : lDt ≠ djI1 := by decide
@[simp] theorem dpj_djI1_ne_lDg : djI1 ≠ lDg := by decide
@[simp] theorem dpj_lDg_ne_djI1 : lDg ≠ djI1 := by decide
@[simp] theorem dpj_djI1_ne_lDi : djI1 ≠ lDi := by decide
@[simp] theorem dpj_lDi_ne_djI1 : lDi ≠ djI1 := by decide
@[simp] theorem dpj_djI1_ne_lRp : djI1 ≠ lRp := by decide
@[simp] theorem dpj_lRp_ne_djI1 : lRp ≠ djI1 := by decide
@[simp] theorem dpj_djI1_ne_lRn : djI1 ≠ lRn := by decide
@[simp] theorem dpj_lRn_ne_djI1 : lRn ≠ djI1 := by decide
@[simp] theorem dpj_djI1_ne_lFle : djI1 ≠ lFle := by decide
@[simp] theorem dpj_lFle_ne_djI1 : lFle ≠ djI1 := by decide
@[simp] theorem dpj_djI1_ne_lKb : djI1 ≠ lKb := by decide
@[simp] theorem dpj_lKb_ne_djI1 : lKb ≠ djI1 := by decide
@[simp] theorem dpj_djI1_ne_lDir : djI1 ≠ lDir := by decide
@[simp] theorem dpj_lDir_ne_djI1 : lDir ≠ djI1 := by decide
@[simp] theorem dpj_djI1_ne_lFln : djI1 ≠ lFln := by decide
@[simp] theorem dpj_lFln_ne_djI1 : lFln ≠ djI1 := by decide
@[simp] theorem dpj_djI1_ne_lFll : djI1 ≠ lFll := by decide
@[simp] theorem dpj_lFll_ne_djI1 : lFll ≠ djI1 := by decide
@[simp] theorem dpj_djI1_ne_lFls : djI1 ≠ lFls := by decide
@[simp] theorem dpj_lFls_ne_djI1 : lFls ≠ djI1 := by decide
@[simp] theorem dpj_djI1_ne_kFu : djI1 ≠ kFu := by decide
@[simp] theorem dpj_kFu_ne_djI1 : kFu ≠ djI1 := by decide
@[simp] theorem dpj_djI1_ne_kD : djI1 ≠ kD := by decide
@[simp] theorem dpj_kD_ne_djI1 : kD ≠ djI1 := by decide
@[simp] theorem dpj_djN2_ne_lpN : djN2 ≠ lpN := by decide
@[simp] theorem dpj_djN2_ne_lpI : djN2 ≠ lpI := by decide
@[simp] theorem dpj_djN2_ne_lpF : djN2 ≠ lpF := by decide
@[simp] theorem dpj_djN2_ne_lpA : djN2 ≠ lpA := by decide
@[simp] theorem dpj_djN2_ne_lpB : djN2 ≠ lpB := by decide
@[simp] theorem dpj_djN2_ne_lpS : djN2 ≠ lpS := by decide
@[simp] theorem dpj_djN2_ne_lpX : djN2 ≠ lpX := by decide
@[simp] theorem dpj_djN2_ne_lpY : djN2 ≠ lpY := by decide
@[simp] theorem dpj_djN2_ne_lpV : djN2 ≠ lpV := by decide
@[simp] theorem dpj_djN2_ne_lpA2 : djN2 ≠ lpA2 := by decide
@[simp] theorem dpj_djN2_ne_lpB2 : djN2 ≠ lpB2 := by decide
@[simp] theorem dpj_djN2_ne_lpR : djN2 ≠ lpR := by decide
@[simp] theorem dpj_djN2_ne_djA : djN2 ≠ djA := by decide
@[simp] theorem dpj_djN2_ne_djB : djN2 ≠ djB := by decide
@[simp] theorem dpj_djN2_ne_djN1 : djN2 ≠ djN1 := by decide
@[simp] theorem dpj_djN2_ne_djP1 : djN2 ≠ djP1 := by decide
@[simp] theorem dpj_djN2_ne_djI1 : djN2 ≠ djI1 := by decide
@[simp] theorem dpj_djN2_ne_djP2 : djN2 ≠ djP2 := by decide
@[simp] theorem dpj_djN2_ne_djI2 : djN2 ≠ djI2 := by decide
@[simp] theorem dpj_djN2_ne_djR : djN2 ≠ djR := by decide
@[simp] theorem dpj_djN2_ne_lFl : djN2 ≠ lFl := by decide
@[simp] theorem dpj_lFl_ne_djN2 : lFl ≠ djN2 := by decide
@[simp] theorem dpj_djN2_ne_lDh : djN2 ≠ lDh := by decide
@[simp] theorem dpj_lDh_ne_djN2 : lDh ≠ djN2 := by decide
@[simp] theorem dpj_djN2_ne_lDt : djN2 ≠ lDt := by decide
@[simp] theorem dpj_lDt_ne_djN2 : lDt ≠ djN2 := by decide
@[simp] theorem dpj_djN2_ne_lDg : djN2 ≠ lDg := by decide
@[simp] theorem dpj_lDg_ne_djN2 : lDg ≠ djN2 := by decide
@[simp] theorem dpj_djN2_ne_lDi : djN2 ≠ lDi := by decide
@[simp] theorem dpj_lDi_ne_djN2 : lDi ≠ djN2 := by decide
@[simp] theorem dpj_djN2_ne_lRp : djN2 ≠ lRp := by decide
@[simp] theorem dpj_lRp_ne_djN2 : lRp ≠ djN2 := by decide
@[simp] theorem dpj_djN2_ne_lRn : djN2 ≠ lRn := by decide
@[simp] theorem dpj_lRn_ne_djN2 : lRn ≠ djN2 := by decide
@[simp] theorem dpj_djN2_ne_lFle : djN2 ≠ lFle := by decide
@[simp] theorem dpj_lFle_ne_djN2 : lFle ≠ djN2 := by decide
@[simp] theorem dpj_djN2_ne_lKb : djN2 ≠ lKb := by decide
@[simp] theorem dpj_lKb_ne_djN2 : lKb ≠ djN2 := by decide
@[simp] theorem dpj_djN2_ne_lDir : djN2 ≠ lDir := by decide
@[simp] theorem dpj_lDir_ne_djN2 : lDir ≠ djN2 := by decide
@[simp] theorem dpj_djN2_ne_lFln : djN2 ≠ lFln := by decide
@[simp] theorem dpj_lFln_ne_djN2 : lFln ≠ djN2 := by decide
@[simp] theorem dpj_djN2_ne_lFll : djN2 ≠ lFll := by decide
@[simp] theorem dpj_lFll_ne_djN2 : lFll ≠ djN2 := by decide
@[simp] theorem dpj_djN2_ne_lFls : djN2 ≠ lFls := by decide
@[simp] theorem dpj_lFls_ne_djN2 : lFls ≠ djN2 := by decide
@[simp] theorem dpj_djN2_ne_kFu : djN2 ≠ kFu := by decide
@[simp] theorem dpj_kFu_ne_djN2 : kFu ≠ djN2 := by decide
@[simp] theorem dpj_djN2_ne_kD : djN2 ≠ kD := by decide
@[simp] theorem dpj_kD_ne_djN2 : kD ≠ djN2 := by decide
@[simp] theorem dpj_djP2_ne_lpN : djP2 ≠ lpN := by decide
@[simp] theorem dpj_djP2_ne_lpI : djP2 ≠ lpI := by decide
@[simp] theorem dpj_djP2_ne_lpF : djP2 ≠ lpF := by decide
@[simp] theorem dpj_djP2_ne_lpA : djP2 ≠ lpA := by decide
@[simp] theorem dpj_djP2_ne_lpB : djP2 ≠ lpB := by decide
@[simp] theorem dpj_djP2_ne_lpS : djP2 ≠ lpS := by decide
@[simp] theorem dpj_djP2_ne_lpX : djP2 ≠ lpX := by decide
@[simp] theorem dpj_djP2_ne_lpY : djP2 ≠ lpY := by decide
@[simp] theorem dpj_djP2_ne_lpV : djP2 ≠ lpV := by decide
@[simp] theorem dpj_djP2_ne_lpA2 : djP2 ≠ lpA2 := by decide
@[simp] theorem dpj_djP2_ne_lpB2 : djP2 ≠ lpB2 := by decide
@[simp] theorem dpj_djP2_ne_lpR : djP2 ≠ lpR := by decide
@[simp] theorem dpj_djP2_ne_djA : djP2 ≠ djA := by decide
@[simp] theorem dpj_djP2_ne_djB : djP2 ≠ djB := by decide
@[simp] theorem dpj_djP2_ne_djN1 : djP2 ≠ djN1 := by decide
@[simp] theorem dpj_djP2_ne_djP1 : djP2 ≠ djP1 := by decide
@[simp] theorem dpj_djP2_ne_djI1 : djP2 ≠ djI1 := by decide
@[simp] theorem dpj_djP2_ne_djN2 : djP2 ≠ djN2 := by decide
@[simp] theorem dpj_djP2_ne_djI2 : djP2 ≠ djI2 := by decide
@[simp] theorem dpj_djP2_ne_djR : djP2 ≠ djR := by decide
@[simp] theorem dpj_djP2_ne_lFl : djP2 ≠ lFl := by decide
@[simp] theorem dpj_lFl_ne_djP2 : lFl ≠ djP2 := by decide
@[simp] theorem dpj_djP2_ne_lDh : djP2 ≠ lDh := by decide
@[simp] theorem dpj_lDh_ne_djP2 : lDh ≠ djP2 := by decide
@[simp] theorem dpj_djP2_ne_lDt : djP2 ≠ lDt := by decide
@[simp] theorem dpj_lDt_ne_djP2 : lDt ≠ djP2 := by decide
@[simp] theorem dpj_djP2_ne_lDg : djP2 ≠ lDg := by decide
@[simp] theorem dpj_lDg_ne_djP2 : lDg ≠ djP2 := by decide
@[simp] theorem dpj_djP2_ne_lDi : djP2 ≠ lDi := by decide
@[simp] theorem dpj_lDi_ne_djP2 : lDi ≠ djP2 := by decide
@[simp] theorem dpj_djP2_ne_lRp : djP2 ≠ lRp := by decide
@[simp] theorem dpj_lRp_ne_djP2 : lRp ≠ djP2 := by decide
@[simp] theorem dpj_djP2_ne_lRn : djP2 ≠ lRn := by decide
@[simp] theorem dpj_lRn_ne_djP2 : lRn ≠ djP2 := by decide
@[simp] theorem dpj_djP2_ne_lFle : djP2 ≠ lFle := by decide
@[simp] theorem dpj_lFle_ne_djP2 : lFle ≠ djP2 := by decide
@[simp] theorem dpj_djP2_ne_lKb : djP2 ≠ lKb := by decide
@[simp] theorem dpj_lKb_ne_djP2 : lKb ≠ djP2 := by decide
@[simp] theorem dpj_djP2_ne_lDir : djP2 ≠ lDir := by decide
@[simp] theorem dpj_lDir_ne_djP2 : lDir ≠ djP2 := by decide
@[simp] theorem dpj_djP2_ne_lFln : djP2 ≠ lFln := by decide
@[simp] theorem dpj_lFln_ne_djP2 : lFln ≠ djP2 := by decide
@[simp] theorem dpj_djP2_ne_lFll : djP2 ≠ lFll := by decide
@[simp] theorem dpj_lFll_ne_djP2 : lFll ≠ djP2 := by decide
@[simp] theorem dpj_djP2_ne_lFls : djP2 ≠ lFls := by decide
@[simp] theorem dpj_lFls_ne_djP2 : lFls ≠ djP2 := by decide
@[simp] theorem dpj_djP2_ne_kFu : djP2 ≠ kFu := by decide
@[simp] theorem dpj_kFu_ne_djP2 : kFu ≠ djP2 := by decide
@[simp] theorem dpj_djP2_ne_kD : djP2 ≠ kD := by decide
@[simp] theorem dpj_kD_ne_djP2 : kD ≠ djP2 := by decide
@[simp] theorem dpj_djI2_ne_lpN : djI2 ≠ lpN := by decide
@[simp] theorem dpj_djI2_ne_lpI : djI2 ≠ lpI := by decide
@[simp] theorem dpj_djI2_ne_lpF : djI2 ≠ lpF := by decide
@[simp] theorem dpj_djI2_ne_lpA : djI2 ≠ lpA := by decide
@[simp] theorem dpj_djI2_ne_lpB : djI2 ≠ lpB := by decide
@[simp] theorem dpj_djI2_ne_lpS : djI2 ≠ lpS := by decide
@[simp] theorem dpj_djI2_ne_lpX : djI2 ≠ lpX := by decide
@[simp] theorem dpj_djI2_ne_lpY : djI2 ≠ lpY := by decide
@[simp] theorem dpj_djI2_ne_lpV : djI2 ≠ lpV := by decide
@[simp] theorem dpj_djI2_ne_lpA2 : djI2 ≠ lpA2 := by decide
@[simp] theorem dpj_djI2_ne_lpB2 : djI2 ≠ lpB2 := by decide
@[simp] theorem dpj_djI2_ne_lpR : djI2 ≠ lpR := by decide
@[simp] theorem dpj_djI2_ne_djA : djI2 ≠ djA := by decide
@[simp] theorem dpj_djI2_ne_djB : djI2 ≠ djB := by decide
@[simp] theorem dpj_djI2_ne_djN1 : djI2 ≠ djN1 := by decide
@[simp] theorem dpj_djI2_ne_djP1 : djI2 ≠ djP1 := by decide
@[simp] theorem dpj_djI2_ne_djI1 : djI2 ≠ djI1 := by decide
@[simp] theorem dpj_djI2_ne_djN2 : djI2 ≠ djN2 := by decide
@[simp] theorem dpj_djI2_ne_djP2 : djI2 ≠ djP2 := by decide
@[simp] theorem dpj_djI2_ne_djR : djI2 ≠ djR := by decide
@[simp] theorem dpj_djI2_ne_lFl : djI2 ≠ lFl := by decide
@[simp] theorem dpj_lFl_ne_djI2 : lFl ≠ djI2 := by decide
@[simp] theorem dpj_djI2_ne_lDh : djI2 ≠ lDh := by decide
@[simp] theorem dpj_lDh_ne_djI2 : lDh ≠ djI2 := by decide
@[simp] theorem dpj_djI2_ne_lDt : djI2 ≠ lDt := by decide
@[simp] theorem dpj_lDt_ne_djI2 : lDt ≠ djI2 := by decide
@[simp] theorem dpj_djI2_ne_lDg : djI2 ≠ lDg := by decide
@[simp] theorem dpj_lDg_ne_djI2 : lDg ≠ djI2 := by decide
@[simp] theorem dpj_djI2_ne_lDi : djI2 ≠ lDi := by decide
@[simp] theorem dpj_lDi_ne_djI2 : lDi ≠ djI2 := by decide
@[simp] theorem dpj_djI2_ne_lRp : djI2 ≠ lRp := by decide
@[simp] theorem dpj_lRp_ne_djI2 : lRp ≠ djI2 := by decide
@[simp] theorem dpj_djI2_ne_lRn : djI2 ≠ lRn := by decide
@[simp] theorem dpj_lRn_ne_djI2 : lRn ≠ djI2 := by decide
@[simp] theorem dpj_djI2_ne_lFle : djI2 ≠ lFle := by decide
@[simp] theorem dpj_lFle_ne_djI2 : lFle ≠ djI2 := by decide
@[simp] theorem dpj_djI2_ne_lKb : djI2 ≠ lKb := by decide
@[simp] theorem dpj_lKb_ne_djI2 : lKb ≠ djI2 := by decide
@[simp] theorem dpj_djI2_ne_lDir : djI2 ≠ lDir := by decide
@[simp] theorem dpj_lDir_ne_djI2 : lDir ≠ djI2 := by decide
@[simp] theorem dpj_djI2_ne_lFln : djI2 ≠ lFln := by decide
@[simp] theorem dpj_lFln_ne_djI2 : lFln ≠ djI2 := by decide
@[simp] theorem dpj_djI2_ne_lFll : djI2 ≠ lFll := by decide
@[simp] theorem dpj_lFll_ne_djI2 : lFll ≠ djI2 := by decide
@[simp] theorem dpj_djI2_ne_lFls : djI2 ≠ lFls := by decide
@[simp] theorem dpj_lFls_ne_djI2 : lFls ≠ djI2 := by decide
@[simp] theorem dpj_djI2_ne_kFu : djI2 ≠ kFu := by decide
@[simp] theorem dpj_kFu_ne_djI2 : kFu ≠ djI2 := by decide
@[simp] theorem dpj_djI2_ne_kD : djI2 ≠ kD := by decide
@[simp] theorem dpj_kD_ne_djI2 : kD ≠ djI2 := by decide
@[simp] theorem dpj_djR_ne_lpN : djR ≠ lpN := by decide
@[simp] theorem dpj_djR_ne_lpI : djR ≠ lpI := by decide
@[simp] theorem dpj_djR_ne_lpF : djR ≠ lpF := by decide
@[simp] theorem dpj_djR_ne_lpA : djR ≠ lpA := by decide
@[simp] theorem dpj_djR_ne_lpB : djR ≠ lpB := by decide
@[simp] theorem dpj_djR_ne_lpS : djR ≠ lpS := by decide
@[simp] theorem dpj_djR_ne_lpX : djR ≠ lpX := by decide
@[simp] theorem dpj_djR_ne_lpY : djR ≠ lpY := by decide
@[simp] theorem dpj_djR_ne_lpV : djR ≠ lpV := by decide
@[simp] theorem dpj_djR_ne_lpA2 : djR ≠ lpA2 := by decide
@[simp] theorem dpj_djR_ne_lpB2 : djR ≠ lpB2 := by decide
@[simp] theorem dpj_djR_ne_lpR : djR ≠ lpR := by decide
@[simp] theorem dpj_djR_ne_djA : djR ≠ djA := by decide
@[simp] theorem dpj_djR_ne_djB : djR ≠ djB := by decide
@[simp] theorem dpj_djR_ne_djN1 : djR ≠ djN1 := by decide
@[simp] theorem dpj_djR_ne_djP1 : djR ≠ djP1 := by decide
@[simp] theorem dpj_djR_ne_djI1 : djR ≠ djI1 := by decide
@[simp] theorem dpj_djR_ne_djN2 : djR ≠ djN2 := by decide
@[simp] theorem dpj_djR_ne_djP2 : djR ≠ djP2 := by decide
@[simp] theorem dpj_djR_ne_djI2 : djR ≠ djI2 := by decide
@[simp] theorem dpj_djR_ne_lFl : djR ≠ lFl := by decide
@[simp] theorem dpj_lFl_ne_djR : lFl ≠ djR := by decide
@[simp] theorem dpj_djR_ne_lDh : djR ≠ lDh := by decide
@[simp] theorem dpj_lDh_ne_djR : lDh ≠ djR := by decide
@[simp] theorem dpj_djR_ne_lDt : djR ≠ lDt := by decide
@[simp] theorem dpj_lDt_ne_djR : lDt ≠ djR := by decide
@[simp] theorem dpj_djR_ne_lDg : djR ≠ lDg := by decide
@[simp] theorem dpj_lDg_ne_djR : lDg ≠ djR := by decide
@[simp] theorem dpj_djR_ne_lDi : djR ≠ lDi := by decide
@[simp] theorem dpj_lDi_ne_djR : lDi ≠ djR := by decide
@[simp] theorem dpj_djR_ne_lRp : djR ≠ lRp := by decide
@[simp] theorem dpj_lRp_ne_djR : lRp ≠ djR := by decide
@[simp] theorem dpj_djR_ne_lRn : djR ≠ lRn := by decide
@[simp] theorem dpj_lRn_ne_djR : lRn ≠ djR := by decide
@[simp] theorem dpj_djR_ne_lFle : djR ≠ lFle := by decide
@[simp] theorem dpj_lFle_ne_djR : lFle ≠ djR := by decide
@[simp] theorem dpj_djR_ne_lKb : djR ≠ lKb := by decide
@[simp] theorem dpj_lKb_ne_djR : lKb ≠ djR := by decide
@[simp] theorem dpj_djR_ne_lDir : djR ≠ lDir := by decide
@[simp] theorem dpj_lDir_ne_djR : lDir ≠ djR := by decide
@[simp] theorem dpj_djR_ne_lFln : djR ≠ lFln := by decide
@[simp] theorem dpj_lFln_ne_djR : lFln ≠ djR := by decide
@[simp] theorem dpj_djR_ne_lFll : djR ≠ lFll := by decide
@[simp] theorem dpj_lFll_ne_djR : lFll ≠ djR := by decide
@[simp] theorem dpj_djR_ne_lFls : djR ≠ lFls := by decide
@[simp] theorem dpj_lFls_ne_djR : lFls ≠ djR := by decide
@[simp] theorem dpj_djR_ne_kFu : djR ≠ kFu := by decide
@[simp] theorem dpj_kFu_ne_djR : kFu ≠ djR := by decide
@[simp] theorem dpj_djR_ne_kD : djR ≠ kD := by decide
@[simp] theorem dpj_kD_ne_djR : kD ≠ djR := by decide

/-- Read a projection row `[sn, pe] ++ limbs i` (the index one limb at most; else halt). -/
def projRead (xN xP xI : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  (.seq (.assign .local xN (.load .one (vv lRp))) (.seq (.assign .local xP (.load .one (.op .add [(vv lRp), (.const 8)]))) (.ite (.cmp .equal (vv lRn) (.const 2)) (.seq (.assign .local xI (.const 0)) rest) (.ite (.cmp .equal (vv lRn) (.const 3)) (.seq (.assign .local xI (.load .one (.op .add [(vv lRp), (.const 16)]))) rest) hang))))

def lprParams : List MlS := [kFu, kD, lpN, lpI, lpF, lpA, lpB]
def lprLocals : List MlS := [lpS, lpX, lpY, lpV, lpA2, lpB2, lpR]
def lprBody (v : Bool) (C : Ctx) : ProgHOL 64 := prologue lprLocals (.ite (.cmp .equal (vv lpF) (.const 0)) hang (.seq (.call (some (some (.local, lpS), none)) fLds [(vv kFu), (vv kD), (vv lpA), (vv lpB)]) (.ite (.cmp .equal (vv lpS) (.const 0)) (.seq (.call (some (some (.local, lpX), none)) fRPC [(vv kFu), (vv kD), (vv lpN), (vv lpI), (vv lpA)]) (.ite (.cmp .equal (vv lpX) (.const 0)) (.seq (.call (some (some (.local, lpV), none)) fD [(vv kFu), (vv kD), (vv lpA), (vv lpB)]) (.return (vv lpV))) (.seq (.call (some (some (.local, lpY), none)) fRPC [(vv kFu), (vv kD), (vv lpN), (vv lpI), (vv lpB)]) (.ite (.cmp .equal (vv lpY) (.const 0)) (.seq (.call (some (some (.local, lpV), none)) fD [(vv kFu), (vv kD), (vv lpA), (vv lpB)]) (.return (vv lpV))) (.seq (.call (some (some (.local, lpV), none)) fD [(vv kFu), (vv kD), (.op .sub [(vv lpX), (.const 1)]), (.op .sub [(vv lpY), (.const 1)])]) (.return (vv lpV))))))) (.ite (.cmp .equal (vv lpS) (.const 1)) (.return (.const 1)) (.ite (.cmp .equal (vv lpS) (.const 2)) (.seq (.call (some (some (.local, lpX), none)) fRPC [(vv kFu), (vv kD), (vv lpN), (vv lpI), (vv lpA)]) (.ite (.cmp .equal (vv lpX) (.const 0)) (.seq (.call (some (some (.local, lpV), none)) fD [(vv kFu), (vv kD), (vv lpA), (vv lpB)]) (.return (vv lpV))) (.seq (.call (some (some (.local, lpY), none)) fRPC [(vv kFu), (vv kD), (vv lpN), (vv lpI), (vv lpB)]) (.ite (.cmp .equal (vv lpY) (.const 0)) (.seq (.call (some (some (.local, lpV), none)) fD [(vv kFu), (vv kD), (vv lpA), (vv lpB)]) (.return (vv lpV))) (.seq (.call (some (some (.local, lpV), none)) fD [(vv kFu), (vv kD), (.op .sub [(vv lpX), (.const 1)]), (.op .sub [(vv lpY), (.const 1)])]) (.return (vv lpV))))))) (.seq (.assign .local lpA2 (.load .one (vv lpS))) (.seq (.assign .local lpB2 (.load .one (.op .add [(vv lpS), (.const 8)]))) (.seq (.call (some (some (.local, lpR), none)) fLpr [(vv kFu), (vv kD), (vv lpN), (vv lpI), (.op .sub [(vv lpF), (.const 1)]), (vv lpA2), (vv lpB2)]) (.return (vv lpR))))))))))
def djParams : List MlS := [kFu, kD, djA, djB]
def djLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, djN1, djP1, djI1, djN2, djP2, djI2, djR]
def djBody (v : Bool) (C : Ctx) : ProgHOL 64 := prologue djLocals (.ite (tagIsE djA 9) (.ite (tagIsE djB 9) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv djA)) (.seq eViewP (projRead djN1 djP1 djI1 (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv djB)) (.seq eViewP (projRead djN2 djP2 djI2 (.ite (.op .and [(.cmp .equal (vv djN1) (vv djN2)), (.cmp .equal (vv djI1) (vv djI2))]) (.seq (.call (some (some (.local, djR), none)) fLpr [(vv kFu), (vv kD), (vv djN1), (vv djI1), (.const (BitVec.ofNat 64 defeqLoopFuel)), (vv djP1), (vv djP2)]) (.return (vv djR))) (.return (.const 0))))))))))) (.return (.const 0))) (.return (.const 0)))

structure LprCodes (C : Ctx) (v : Bool) : Prop where
  ld : C.code.lookup fLds = some (ldParams.map (fun p => (p, ShapeHOL.one)), ldBody, .one)
  rp : C.code.lookup fRPC = some (rpcParams.map (fun p => (p, ShapeHOL.one)), rpcBody v C, .one)
  d : C.code.lookup fD = some (dParams.map (fun p => (p, ShapeHOL.one)), dE C, .one)
  self : C.code.lookup fLpr = some (lprParams.map (fun p => (p, ShapeHOL.one)), lprBody v C, .one)

section
variable {σ : Type}

theorem envGet_ne {Γ : Env} {x y : MlS} {v : BitVec 64} (h : y ≠ x) : Env.get ((y, v) :: Γ) x = Env.get Γ x := by
  simp [Env.get, Ne.symm h]

theorem specR_projReadI {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M0 : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (xN xP xI : MlS) (sn : NIdx) (i : Nat) (pe : EIdx)
    (P : BitVec 64) (hxN : xN ∈ D) (hxP : xP ∈ D) (hxI : xI ∈ D)
    (d1 : xN ≠ lRp) (d2 : xP ≠ lRp) (d3 : xN ≠ lRn) (d4 : xP ≠ lRn) (d5 : xP ≠ xN)
    (hP : Γ.get lRp = some P) (hRn : Γ.get lRn = some (BitVec.ofNat 64 (encEView (.proj sn i pe)).length))
    (hl : (encEView (.proj sn i pe)).length < 2 ^ 61)
    (hk : i < 2 ^ 64 → SpecR (Inv C s ((xI, BitVec.ofNat 64 i) :: (xP, Enc.idxW pe) :: (xN, Enc.idxW sn) :: Γ)
      (wordsAt P (encEView (.proj sn i pe)) ++ M0) D) rest s m R) :
    SpecR (Inv C s Γ (wordsAt P (encEView (.proj sn i pe)) ++ M0) D) (projRead xN xP xI rest) s m R := by
  have er : encEView (.proj sn i pe) = Enc.idxW sn :: Enc.idxW pe :: limbs i := rfl
  unfold projRead
  refine specR_loadI' xN (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW sn) hxN (by simp [hP]) (by simp)
    (by simpa [er] using wordsAt_mem0 P (Enc.idxW sn) (Enc.idxW pe :: limbs i) M0) ?_
  refine specR_loadI' xP _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW pe) hxP (by simp [sev, envGet_ne d1, hP]) rfl
    (by simpa [er] using wordsAt_mem1 P (Enc.idxW sn) (Enc.idxW pe) (limbs i) M0) ?_
  have hlen : (encEView (.proj sn i pe)).length = (limbs i).length + 2 := by rw [er]; simp
  have hl58 : (limbs i).length + 2 < 2 ^ 61 := by rw [← hlen]; exact hl
  have hRn' : Env.get ((xP, Enc.idxW pe) :: (xN, Enc.idxW sn) :: Γ) lRn =
      some (BitVec.ofNat 64 ((limbs i).length + 2)) := by
    rw [envGet_ne d4, envGet_ne d3, hRn, hlen]
  rcases (by omega : (limbs i).length = 0 ∨ (limbs i).length = 1 ∨ 2 ≤ (limbs i).length) with h0 | h1 | h2
  · have hi0 : i = 0 := by have := (limbs_length_lt_iff i 0).mp (by omega); simpa using this
    subst hi0
    refine specR_ifI _ 1 (by simp [sev, hRn', h0, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_assignI xI (.const 0) (BitVec.ofNat 64 0) hxI rfl ?_
    exact hk (by decide)
  · have hiB : i < B := by have := (limbs_length_lt_iff i 1).mp (by omega); simpa using this
    have h2w : BitVec.ofNat 64 ((limbs i).length + 2) ≠ 2#64 := by rw [h1]; decide
    refine specR_ifI _ 0 (by simp [sev, hRn', Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact h2w) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, hRn', h1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    have hx2 : (Enc.idxW sn :: Enc.idxW pe :: limbs i)[2]'(by simp; omega) = BitVec.ofNat 64 i := by
      show (limbs i)[0]'(by omega) = _
      rw [limbs_getElem i 0 (by omega)]; simp [Nat.mod_eq_of_lt hiB]
    refine specR_loadI' xI _ (P + 16) (P + BitVec.ofNat 64 (8 * 2)) (BitVec.ofNat 64 i) hxI
      (by simp [sev, envGet_ne d2, envGet_ne d1, hP]) rfl (by
        have := wordsAt_get P (Enc.idxW sn :: Enc.idxW pe :: limbs i) 2 (by simp; omega) M0
        rw [hx2] at this; simpa [er] using this) ?_
    exact hk hiB
  · have h2w : BitVec.ofNat 64 ((limbs i).length + 2) ≠ 2#64 := by
      intro h0; have := congrArg BitVec.toNat h0; simp at this; omega
    have h3w : BitVec.ofNat 64 ((limbs i).length + 2) ≠ 3#64 := by
      intro h0; have := congrArg BitVec.toNat h0; simp at this; omega
    refine specR_ifI _ 0 (by simp [sev, hRn', Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact h2w) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, hRn', Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact h3w) (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_hangI

theorem lpr_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) (hok : CtxOK C) (hc : LprCodes C mode.verifiedChecks)
    (Q : AState → Prop) (d : Nat) (sn : NIdx) (i : Nat)
    (hQld : ∀ s1 a b r s2, Q s1 → lazyDeltaStep mode (knot mode C n) C.fe d a b s1 = .ok (r, s2) → Q s2)
    (hQrp : ∀ s1 e r s2, Q s1 → reduceProjCore mode (knot mode C n) C.fe d sn i e s1 = .ok (r, s2) → Q s2)
    (hQd : ∀ s1 a b r s2, Q s1 → (knot mode C n).defeq d a b s1 = .ok (r, s2) → Q s2)
    (hLD : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ a b, SpecR (σ := σ) (Pre (ctxH C H) s1 (ldParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d,
      Enc.idxW a, Enc.idxW b])) ldBody s1 (lazyDeltaStep mode (knot mode C n) C.fe d a b) (PostDS (ctxH C H)))
    (hRP : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ e, SpecR (σ := σ) (Pre (ctxH C H) s1 (rpcParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d,
      Enc.idxW sn, BitVec.ofNat 64 i, Enc.idxW e])) (rpcBody mode.verifiedChecks C) s1
      (reduceProjCore mode (knot mode C n) C.fe d sn i e) (UD.PostO (ctxH C H)))
    (hD : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ a b, Callee (σ := σ) (ctxH C H) dParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (dE C) s1 ((knot mode C n).defeq d a b)
      (PostB (ctxH C H))) :
    ∀ F, F < 2 ^ 63 → ∀ (H : List (BitVec 64)) (s : AState) (a b : EIdx), C.H <+: H → Q s →
      SpecR (σ := σ) (Pre (ctxH C H) s (lprParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW sn,
        BitVec.ofNat 64 i, BitVec.ofNat 64 F, Enc.idxW a, Enc.idxW b])) (lprBody mode.verifiedChecks C) s
        (lazyDeltaProjReduction mode (knot mode C n) C.fe d sn i F a b) (PostB (ctxH C H)) := by
  intro F
  induction F with
  | zero =>
    intro _ H s a b hpH hq
    refine specR_prologue (postB_locals _) (Knot.params_none _ lprLocals lprParams _ (by decide) (by decide)) ?_
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get, lprParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI)
      (fun h => absurd h (by decide))
  | succ F ih =>
    intro hF H s a b hpH hq
    refine specR_prologue (postB_locals _) (Knot.params_none _ lprLocals lprParams _ (by decide) (by decide)) ?_
    have hne := ofNat_succ_ne F (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, lprParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h)
      (fun _ => ?_)
    rw [lazyDeltaProjReduction]
    refine specR_callNIH (C := ctxH C H) lpS fLds ldParams [(vv kFu), (vv kD), (vv lpA), (vv lpB)] ldBody
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (by decide) rfl (by decide) hc.ld
      ⟨by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], trivial⟩
      (fun r_ w s' st => lazyDeltaStep mode (knot mode C n) C.fe d a b s = .ok (r_, s') ∧ PostDS (ctxH C H) r_ w s' st) (fun r_ w s' H' => dsW C H' r_ w ∧ lazyDeltaStep mode (knot mode C n) C.fe d a b s = .ok (r_, s'))
      (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu ldParams _ rfl hlk) (hLD H s hpH hq a b)))
      (fun dr w1 s1 H1 hp1 ⟨hw1, hrun1⟩ => ?_)
    have hq1 := hQld s a b dr s1 hq hrun1
    have hpa1 : C.H <+: H1 := hpH.trans hp1
    have hb1 : H <+: H1 := (List.prefix_refl _).trans hp1
    rcases dr with ⟨a', b'⟩ | _ | _ | _
    · obtain ⟨o, rfl, hoa, hob⟩ := hw1
      refine specR_atEntry fun t ht => ?_
      have hbig := cellA_big hok ht.sr (List.getElem?_eq_some_iff.mp hoa).1
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hbig.1) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hbig.2.1) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hbig.2.2) (fun h => absurd rfl h) (fun _ => ?_)
      try dsimp only
      refine UD.specR_heapLoadI' (C := ctxH C H1) lpA2 (vv lpS) o (Enc.idxW a') hoa (by decide) (by simp <;> rfl) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H1) lpB2 (.op .add [vv lpS, .const 8]) (o + 1) (Enc.idxW b') hob (by decide)
        (by simp [sev]; exact cellA_add8 C o) ?_
      refine specR_congr (m' := lazyDeltaProjReduction mode (knot mode C n) C.fe d sn i F a' b' >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H1) lpR fLpr lprParams [vv kFu, vv kD, vv lpN, vv lpI, .op .sub [vv lpF, .const 1], vv lpA2, vv lpB2] (lprBody mode.verifiedChecks C)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW sn, BitVec.ofNat 64 i, BitVec.ofNat 64 F, Enc.idxW a', Enc.idxW b'] (by decide) rfl (by decide) hc.self
        ⟨by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [sev, Env.get, lprParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, by simp, by simp, trivial⟩
        (PostB (ctxH C H1)) (fun r_ w _ _ => w = boolW r_) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu lprParams _ rfl hlk) (ih (by omega) H1 s1 a' b' hpa1 hq1))
        (fun rr wr sr' Hr hpr hwr => ?_)
      subst hwr
      exact specR_returnI _ (boolW rr) (by simp) (fun t ht => ⟨Hr, hb1.trans hpr, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    · simp only [dsW] at hw1; subst hw1
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      try dsimp only
      exact specR_returnI _ 1 rfl (fun t ht => ⟨H1, hb1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · simp only [dsW] at hw1; subst hw1
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      try dsimp only
      refine specR_callNIH (C := ctxH C H1) lpX fRPC rpcParams [(vv kFu), (vv kD), (vv lpN), (vv lpI), (vv lpA)] (rpcBody mode.verifiedChecks C)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW sn, BitVec.ofNat 64 i, Enc.idxW a] (by decide) rfl (by decide) hc.rp
        ⟨by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], trivial⟩
        (fun r_ w s' st => reduceProjCore mode (knot mode C n) C.fe d sn i a s1 = .ok (r_, s') ∧ UD.PostO (ctxH C H1) r_ w s' st) (fun r_ w s' H' => w = optW r_ ∧ reduceProjCore mode (knot mode C n) C.fe d sn i a s1 = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu rpcParams _ rfl hlk) (hRP H1 s1 hpa1 hq1 a)))
        (fun ox w2 s2 H2 hp2 ⟨hw2, hrun2⟩ => ?_)
      have hq2 := hQrp s1 a ox s2 hq1 hrun2
      have hpa2 : C.H <+: H2 := hpa1.trans hp2
      have hb2 : H <+: H2 := hb1.trans hp2
      subst hw2
      rcases ox with _ | x
      · refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
        try dsimp only
        refine specR_congr (m' := (knot mode C n).defeq d a b >>= fun r => pure r) (by simp) ?_
        refine specR_callNIH (C := ctxH C H2) lpV fD dParams [vv kFu, vv kD, vv lpA, vv lpB] (dE C)
          [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (by decide) rfl (by decide) hc.d
          ⟨by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], trivial⟩
          (fun r_ w s' st => (knot mode C n).defeq d a b s2 = .ok (r_, s') ∧ PostB (ctxH C H2) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ (knot mode C n).defeq d a b s2 = .ok (r_, s'))
          (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
          (fun u hu _ hlk => specR_run (hD H2 s2 hpa2 hq2 a b u hu (fun i hi _ => hlk i (by omega))))
          (fun vv_ w3 s3 H3 hp3 ⟨hw3, hrun3⟩ => ?_)
        have hq3 := hQd s2 a b vv_ s3 hq2 hrun3
        have hpa3 : C.H <+: H3 := hpa2.trans hp3
        have hb3 : H <+: H3 := hb2.trans hp3
        subst hw3
        exact specR_returnI _ (boolW vv_) (by simp) (fun t ht => ⟨H3, hb3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

      refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne x) (fun h => absurd rfl h) (fun _ => ?_)
      try dsimp only
      refine specR_callNIH (C := ctxH C H2) lpY fRPC rpcParams [(vv kFu), (vv kD), (vv lpN), (vv lpI), (vv lpB)] (rpcBody mode.verifiedChecks C)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW sn, BitVec.ofNat 64 i, Enc.idxW b] (by decide) rfl (by decide) hc.rp
        ⟨by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], trivial⟩
        (fun r_ w s' st => reduceProjCore mode (knot mode C n) C.fe d sn i b s2 = .ok (r_, s') ∧ UD.PostO (ctxH C H2) r_ w s' st) (fun r_ w s' H' => w = optW r_ ∧ reduceProjCore mode (knot mode C n) C.fe d sn i b s2 = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu rpcParams _ rfl hlk) (hRP H2 s2 hpa2 hq2 b)))
        (fun oy w4 s4 H4 hp4 ⟨hw4, hrun4⟩ => ?_)
      have hq4 := hQrp s2 b oy s4 hq2 hrun4
      have hpa4 : C.H <+: H4 := hpa2.trans hp4
      have hb4 : H <+: H4 := hb2.trans hp4
      subst hw4
      rcases oy with _ | y
      · refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
        try dsimp only
        refine specR_congr (m' := (knot mode C n).defeq d a b >>= fun r => pure r) (by simp) ?_
        refine specR_callNIH (C := ctxH C H4) lpV fD dParams [vv kFu, vv kD, vv lpA, vv lpB] (dE C)
          [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (by decide) rfl (by decide) hc.d
          ⟨by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], trivial⟩
          (fun r_ w s' st => (knot mode C n).defeq d a b s4 = .ok (r_, s') ∧ PostB (ctxH C H4) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ (knot mode C n).defeq d a b s4 = .ok (r_, s'))
          (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
          (fun u hu _ hlk => specR_run (hD H4 s4 hpa4 hq4 a b u hu (fun i hi _ => hlk i (by omega))))
          (fun vv_ w5 s5 H5 hp5 ⟨hw5, hrun5⟩ => ?_)
        have hq5 := hQd s4 a b vv_ s5 hq4 hrun5
        have hpa5 : C.H <+: H5 := hpa4.trans hp5
        have hb5 : H <+: H5 := hb4.trans hp5
        subst hw5
        exact specR_returnI _ (boolW vv_) (by simp) (fun t ht => ⟨H5, hb5, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

      refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne y) (fun h => absurd rfl h) (fun _ => ?_)
      try dsimp only
      refine specR_congr (m' := (knot mode C n).defeq d x y >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H4) lpV fD dParams [vv kFu, vv kD, .op .sub [vv lpX, .const 1], .op .sub [vv lpY, .const 1]] (dE C)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW x, Enc.idxW y] (by decide) rfl (by decide) hc.d
        ⟨by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [sev, Env.get, lprParams, ctxEnv, optWG]; exact BitVec.add_sub_cancel _ _, by simp +decide [sev, Env.get, lprParams, ctxEnv, optWG]; exact BitVec.add_sub_cancel _ _, trivial⟩
        (fun r_ w s' st => (knot mode C n).defeq d x y s4 = .ok (r_, s') ∧ PostB (ctxH C H4) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ (knot mode C n).defeq d x y s4 = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (hD H4 s4 hpa4 hq4 x y u hu (fun i hi _ => hlk i (by omega))))
        (fun vv_ w6 s6 H6 hp6 ⟨hw6, hrun6⟩ => ?_)
      have hq6 := hQd s4 x y vv_ s6 hq4 hrun6
      have hpa6 : C.H <+: H6 := hpa4.trans hp6
      have hb6 : H <+: H6 := hb4.trans hp6
      subst hw6
      exact specR_returnI _ (boolW vv_) (by simp) (fun t ht => ⟨H6, hb6, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    · simp only [dsW] at hw1; subst hw1
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      try dsimp only
      refine specR_callNIH (C := ctxH C H1) lpX fRPC rpcParams [(vv kFu), (vv kD), (vv lpN), (vv lpI), (vv lpA)] (rpcBody mode.verifiedChecks C)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW sn, BitVec.ofNat 64 i, Enc.idxW a] (by decide) rfl (by decide) hc.rp
        ⟨by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], trivial⟩
        (fun r_ w s' st => reduceProjCore mode (knot mode C n) C.fe d sn i a s1 = .ok (r_, s') ∧ UD.PostO (ctxH C H1) r_ w s' st) (fun r_ w s' H' => w = optW r_ ∧ reduceProjCore mode (knot mode C n) C.fe d sn i a s1 = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu rpcParams _ rfl hlk) (hRP H1 s1 hpa1 hq1 a)))
        (fun ox w7 s7 H7 hp7 ⟨hw7, hrun7⟩ => ?_)
      have hq7 := hQrp s1 a ox s7 hq1 hrun7
      have hpa7 : C.H <+: H7 := hpa1.trans hp7
      have hb7 : H <+: H7 := hb1.trans hp7
      subst hw7
      rcases ox with _ | x
      · refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
        try dsimp only
        refine specR_congr (m' := (knot mode C n).defeq d a b >>= fun r => pure r) (by simp) ?_
        refine specR_callNIH (C := ctxH C H7) lpV fD dParams [vv kFu, vv kD, vv lpA, vv lpB] (dE C)
          [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (by decide) rfl (by decide) hc.d
          ⟨by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], trivial⟩
          (fun r_ w s' st => (knot mode C n).defeq d a b s7 = .ok (r_, s') ∧ PostB (ctxH C H7) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ (knot mode C n).defeq d a b s7 = .ok (r_, s'))
          (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
          (fun u hu _ hlk => specR_run (hD H7 s7 hpa7 hq7 a b u hu (fun i hi _ => hlk i (by omega))))
          (fun vv_ w8 s8 H8 hp8 ⟨hw8, hrun8⟩ => ?_)
        have hq8 := hQd s7 a b vv_ s8 hq7 hrun8
        have hpa8 : C.H <+: H8 := hpa7.trans hp8
        have hb8 : H <+: H8 := hb7.trans hp8
        subst hw8
        exact specR_returnI _ (boolW vv_) (by simp) (fun t ht => ⟨H8, hb8, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

      refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne x) (fun h => absurd rfl h) (fun _ => ?_)
      try dsimp only
      refine specR_callNIH (C := ctxH C H7) lpY fRPC rpcParams [(vv kFu), (vv kD), (vv lpN), (vv lpI), (vv lpB)] (rpcBody mode.verifiedChecks C)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW sn, BitVec.ofNat 64 i, Enc.idxW b] (by decide) rfl (by decide) hc.rp
        ⟨by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], trivial⟩
        (fun r_ w s' st => reduceProjCore mode (knot mode C n) C.fe d sn i b s7 = .ok (r_, s') ∧ UD.PostO (ctxH C H7) r_ w s' st) (fun r_ w s' H' => w = optW r_ ∧ reduceProjCore mode (knot mode C n) C.fe d sn i b s7 = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu rpcParams _ rfl hlk) (hRP H7 s7 hpa7 hq7 b)))
        (fun oy w9 s9 H9 hp9 ⟨hw9, hrun9⟩ => ?_)
      have hq9 := hQrp s7 b oy s9 hq7 hrun9
      have hpa9 : C.H <+: H9 := hpa7.trans hp9
      have hb9 : H <+: H9 := hb7.trans hp9
      subst hw9
      rcases oy with _ | y
      · refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
        try dsimp only
        refine specR_congr (m' := (knot mode C n).defeq d a b >>= fun r => pure r) (by simp) ?_
        refine specR_callNIH (C := ctxH C H9) lpV fD dParams [vv kFu, vv kD, vv lpA, vv lpB] (dE C)
          [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (by decide) rfl (by decide) hc.d
          ⟨by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], trivial⟩
          (fun r_ w s' st => (knot mode C n).defeq d a b s9 = .ok (r_, s') ∧ PostB (ctxH C H9) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ (knot mode C n).defeq d a b s9 = .ok (r_, s'))
          (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
          (fun u hu _ hlk => specR_run (hD H9 s9 hpa9 hq9 a b u hu (fun i hi _ => hlk i (by omega))))
          (fun vv_ w10 s10 H10 hp10 ⟨hw10, hrun10⟩ => ?_)
        have hq10 := hQd s9 a b vv_ s10 hq9 hrun10
        have hpa10 : C.H <+: H10 := hpa9.trans hp10
        have hb10 : H <+: H10 := hb9.trans hp10
        subst hw10
        exact specR_returnI _ (boolW vv_) (by simp) (fun t ht => ⟨H10, hb10, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

      refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne y) (fun h => absurd rfl h) (fun _ => ?_)
      try dsimp only
      refine specR_congr (m' := (knot mode C n).defeq d x y >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H9) lpV fD dParams [vv kFu, vv kD, .op .sub [vv lpX, .const 1], .op .sub [vv lpY, .const 1]] (dE C)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW x, Enc.idxW y] (by decide) rfl (by decide) hc.d
        ⟨by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [Env.get, lprParams, ctxEnv], by simp +decide [sev, Env.get, lprParams, ctxEnv, optWG]; exact BitVec.add_sub_cancel _ _, by simp +decide [sev, Env.get, lprParams, ctxEnv, optWG]; exact BitVec.add_sub_cancel _ _, trivial⟩
        (fun r_ w s' st => (knot mode C n).defeq d x y s9 = .ok (r_, s') ∧ PostB (ctxH C H9) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ (knot mode C n).defeq d x y s9 = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (hD H9 s9 hpa9 hq9 x y u hu (fun i hi _ => hlk i (by omega))))
        (fun vv_ w11 s11 H11 hp11 ⟨hw11, hrun11⟩ => ?_)
      have hq11 := hQd s9 x y vv_ s11 hq9 hrun11
      have hpa11 : C.H <+: H11 := hpa9.trans hp11
      have hb11 : H <+: H11 := hb9.trans hp11
      subst hw11
      exact specR_returnI _ (boolW vv_) (by simp) (fun t ht => ⟨H11, hb11, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)



theorem dj_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hcl : C.code.lookup fLpr = some (lprParams.map (fun p => (p, ShapeHOL.one)), lprBody mode.verifiedChecks C, .one))
    (Q : AState → Prop) (d : Nat)
    (hLP : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ sn i a b, i < 2 ^ 64 →
      SpecR (σ := σ) (Pre (ctxH C H) s1 (lprParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW sn,
        BitVec.ofNat 64 i, BitVec.ofNat 64 defeqLoopFuel, Enc.idxW a, Enc.idxW b])) (lprBody mode.verifiedChecks C) s1
        (lazyDeltaProjReduction mode (knot mode C n) C.fe d sn i defeqLoopFuel a b) (PostB (ctxH C H)))
    (s : AState) (hq : Q s) (a b : EIdx) :
    SpecR (σ := σ) (Pre C s (djParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b]))
      (djBody mode.verifiedChecks C) s (defeqProjPair mode (knot mode C n) C.fe d a b) (PostB C) := by
  refine specR_prologue (postB_locals C) (Knot.params_none C djLocals djParams _ (by decide) (by decide)) ?_
  unfold defeqProjPair
  have ret0 : ∀ {Γ : Env} {M : Mem} {D : List MlS},
      SpecR (σ := σ) (Inv C s Γ M D) (.return (.const 0)) s (pure false) (PostB C) := fun {Γ M D} =>
    specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine Knot.specR_tagIteV djA a 9 (by decide) (by decide) (by simp +decide [Env.get, djParams, ctxEnv])
    (fun hA => ?_) (fun hA => ?_)
  swap
  · rw [if_neg (by simp only [Bool.and_eq_true, beq_iff_eq]; exact fun h => hA (by rw [h.1]; rfl))]
    exact ret0
  refine Knot.specR_tagIteV djB b 9 (by decide) (by decide) (by simp +decide [Env.get, djParams, ctxEnv])
    (fun hB => ?_) (fun hB => ?_)
  swap
  · rw [if_neg (by simp only [Bool.and_eq_true, beq_iff_eq]; exact fun h => hB (by rw [h.2]; rfl))]
    exact ret0
  rw [if_pos (by simp only [Bool.and_eq_true, beq_iff_eq]; exact ⟨by rw [hA]; rfl, by rw [hB]; rfl⟩)]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv djA) (Enc.idxW a) (by decide) (by simp +decide [Env.get, djParams, ctxEnv]) ?_
  refine specR_viewP a (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
    (fun va P hv htn hl => ?_)
  refine specR_congr (Big.view_bind_eq a va _ s hv) ?_
  have h9 : va.tagN = 9 := by rw [htn, hA]; rfl
  obtain ⟨sn1, i1, e1, rfl⟩ : ∃ sn i e, va = .proj sn i e := by cases va <;> simp [ENodeView.tagN] at h9 ⊢
  refine specR_projReadI djN1 djP1 djI1 sn1 i1 e1 P (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by simp) (by simp) hl (fun hi1 => ?_)
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv djB) (Enc.idxW b) (by decide) (by simp +decide [Env.get, djParams, ctxEnv]) ?_
  refine specR_viewP b (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
    (fun vb P2 hv htn hl => ?_)
  refine specR_congr (Big.view_bind_eq b vb _ s hv) ?_
  have h9 : vb.tagN = 9 := by rw [htn, hB]; rfl
  obtain ⟨sn2, i2, e2, rfl⟩ : ∃ sn i e, vb = .proj sn i e := by cases vb <;> simp [ENodeView.tagN] at h9 ⊢
  refine specR_projReadI djN2 djP2 djI2 sn2 i2 e2 P2 (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by simp) (by simp) hl (fun hi2 => ?_)

  dsimp only
  by_cases hs : sn1 = sn2
  · by_cases hii : i1 = i2
    · subst hs hii
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, djParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      simp only [beq_self_eq_true, Bool.and_self, ↓reduceIte]
      refine specR_congr (m' := lazyDeltaProjReduction mode (knot mode C n) C.fe d sn1 i1 defeqLoopFuel e1 e2 >>=
        fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := C) djR fLpr lprParams [vv kFu, vv kD, vv djN1, vv djI1,
        .const (BitVec.ofNat 64 defeqLoopFuel), vv djP1, vv djP2] (lprBody mode.verifiedChecks C)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW sn1, BitVec.ofNat 64 i1, BitVec.ofNat 64 defeqLoopFuel,
          Enc.idxW e1, Enc.idxW e2] (by decide) rfl (by decide) hcl
        ⟨by simp +decide [Env.get, djParams, ctxEnv], by simp +decide [Env.get, djParams, ctxEnv], by simp +decide [Env.get, djParams, ctxEnv], by simp +decide [Env.get, djParams, ctxEnv], rfl, by simp +decide [Env.get, djParams, ctxEnv], by simp +decide [Env.get, djParams, ctxEnv], trivial⟩
        (PostB C) (fun r_ w _ _ => w = boolW r_) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu lprParams _ rfl hlk)
          (hLP C.H s (List.prefix_refl _) hq sn1 i1 e1 e2 hi1))
        (fun rr wr sr' Hr hpr hwr => ?_)
      subst hwr
      exact specR_returnI _ (boolW rr) (by simp) (fun t ht => ⟨Hr, hpr, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · have hw : BitVec.ofNat 64 i1 ≠ BitVec.ofNat 64 i2 := by
        intro x; apply hii
        have := congrArg BitVec.toNat x
        simp only [BitVec.toNat_ofNat] at this
        rwa [Nat.mod_eq_of_lt hi1, Nat.mod_eq_of_lt hi2] at this
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, djParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hw]) (fun h => absurd rfl h)
        (fun _ => ?_)
      simp only [show (i1 == i2) = false by simpa using hii, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      exact ret0
  · have hw : Enc.idxW sn1 ≠ Enc.idxW sn2 := fun x => hs (Enc.idxW_inj x)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, djParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hw]) (fun h => absurd rfl h)
      (fun _ => ?_)
    simp only [show (sn1 == sn2) = false by simpa using hs, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    exact ret0

end

end ConPanqueque.T.WC
