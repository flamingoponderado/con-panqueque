import ConPanqueque.T.Core.LazyDeltaStep
import ConPanqueque.T.Core.Whnf
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `lazyDeltaReduction`: the lazy-delta loop

The outcome as `lrW`: `verdict v` the word `boolW v`, `unknown a b` a fresh block `[a, b]`. The loop's fuel is
a parameter (`0` halts, as the twin fails). The eager flag `v` is static: `lazyFoldOk` is chosen at meta level.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def lrF := ofString "ldr_f"
def lrA := ofString "ldr_a"
def lrB := ofString "ldr_b"
def lrO := ofString "ldr_o"
def lrN := ofString "ldr_n"
def lrX := ofString "ldr_x"
def lrV := ofString "ldr_v"
def lrY := ofString "ldr_y"
def lrS := ofString "ldr_s"
def lrA2 := ofString "ldr_a2"
def lrB2 := ofString "ldr_b2"
def lrW := ofString "ldr_w"
def lrR := ofString "ldr_r"
def fLdr := ofString "lazyDeltaReduction"

@[simp] theorem ldr_lrF_ne_lrA : lrF ≠ lrA := by decide
@[simp] theorem ldr_lrF_ne_lrB : lrF ≠ lrB := by decide
@[simp] theorem ldr_lrF_ne_lrO : lrF ≠ lrO := by decide
@[simp] theorem ldr_lrF_ne_lrN : lrF ≠ lrN := by decide
@[simp] theorem ldr_lrF_ne_lrX : lrF ≠ lrX := by decide
@[simp] theorem ldr_lrF_ne_lrV : lrF ≠ lrV := by decide
@[simp] theorem ldr_lrF_ne_lrY : lrF ≠ lrY := by decide
@[simp] theorem ldr_lrF_ne_lrS : lrF ≠ lrS := by decide
@[simp] theorem ldr_lrF_ne_lrA2 : lrF ≠ lrA2 := by decide
@[simp] theorem ldr_lrF_ne_lrB2 : lrF ≠ lrB2 := by decide
@[simp] theorem ldr_lrF_ne_lrW : lrF ≠ lrW := by decide
@[simp] theorem ldr_lrF_ne_lrR : lrF ≠ lrR := by decide
@[simp] theorem ldr_lrF_ne_lFl : lrF ≠ lFl := by decide
@[simp] theorem ldr_lFl_ne_lrF : lFl ≠ lrF := by decide
@[simp] theorem ldr_lrF_ne_lDh : lrF ≠ lDh := by decide
@[simp] theorem ldr_lDh_ne_lrF : lDh ≠ lrF := by decide
@[simp] theorem ldr_lrF_ne_lDt : lrF ≠ lDt := by decide
@[simp] theorem ldr_lDt_ne_lrF : lDt ≠ lrF := by decide
@[simp] theorem ldr_lrF_ne_lDg : lrF ≠ lDg := by decide
@[simp] theorem ldr_lDg_ne_lrF : lDg ≠ lrF := by decide
@[simp] theorem ldr_lrF_ne_lDi : lrF ≠ lDi := by decide
@[simp] theorem ldr_lDi_ne_lrF : lDi ≠ lrF := by decide
@[simp] theorem ldr_lrF_ne_lRp : lrF ≠ lRp := by decide
@[simp] theorem ldr_lRp_ne_lrF : lRp ≠ lrF := by decide
@[simp] theorem ldr_lrF_ne_lRn : lrF ≠ lRn := by decide
@[simp] theorem ldr_lRn_ne_lrF : lRn ≠ lrF := by decide
@[simp] theorem ldr_lrF_ne_lFle : lrF ≠ lFle := by decide
@[simp] theorem ldr_lFle_ne_lrF : lFle ≠ lrF := by decide
@[simp] theorem ldr_lrF_ne_lKb : lrF ≠ lKb := by decide
@[simp] theorem ldr_lKb_ne_lrF : lKb ≠ lrF := by decide
@[simp] theorem ldr_lrF_ne_lDir : lrF ≠ lDir := by decide
@[simp] theorem ldr_lDir_ne_lrF : lDir ≠ lrF := by decide
@[simp] theorem ldr_lrF_ne_lFln : lrF ≠ lFln := by decide
@[simp] theorem ldr_lFln_ne_lrF : lFln ≠ lrF := by decide
@[simp] theorem ldr_lrF_ne_lFll : lrF ≠ lFll := by decide
@[simp] theorem ldr_lFll_ne_lrF : lFll ≠ lrF := by decide
@[simp] theorem ldr_lrF_ne_lFls : lrF ≠ lFls := by decide
@[simp] theorem ldr_lFls_ne_lrF : lFls ≠ lrF := by decide
@[simp] theorem ldr_lrF_ne_kFu : lrF ≠ kFu := by decide
@[simp] theorem ldr_kFu_ne_lrF : kFu ≠ lrF := by decide
@[simp] theorem ldr_lrF_ne_kD : lrF ≠ kD := by decide
@[simp] theorem ldr_kD_ne_lrF : kD ≠ lrF := by decide
@[simp] theorem ldr_lrA_ne_lrF : lrA ≠ lrF := by decide
@[simp] theorem ldr_lrA_ne_lrB : lrA ≠ lrB := by decide
@[simp] theorem ldr_lrA_ne_lrO : lrA ≠ lrO := by decide
@[simp] theorem ldr_lrA_ne_lrN : lrA ≠ lrN := by decide
@[simp] theorem ldr_lrA_ne_lrX : lrA ≠ lrX := by decide
@[simp] theorem ldr_lrA_ne_lrV : lrA ≠ lrV := by decide
@[simp] theorem ldr_lrA_ne_lrY : lrA ≠ lrY := by decide
@[simp] theorem ldr_lrA_ne_lrS : lrA ≠ lrS := by decide
@[simp] theorem ldr_lrA_ne_lrA2 : lrA ≠ lrA2 := by decide
@[simp] theorem ldr_lrA_ne_lrB2 : lrA ≠ lrB2 := by decide
@[simp] theorem ldr_lrA_ne_lrW : lrA ≠ lrW := by decide
@[simp] theorem ldr_lrA_ne_lrR : lrA ≠ lrR := by decide
@[simp] theorem ldr_lrA_ne_lFl : lrA ≠ lFl := by decide
@[simp] theorem ldr_lFl_ne_lrA : lFl ≠ lrA := by decide
@[simp] theorem ldr_lrA_ne_lDh : lrA ≠ lDh := by decide
@[simp] theorem ldr_lDh_ne_lrA : lDh ≠ lrA := by decide
@[simp] theorem ldr_lrA_ne_lDt : lrA ≠ lDt := by decide
@[simp] theorem ldr_lDt_ne_lrA : lDt ≠ lrA := by decide
@[simp] theorem ldr_lrA_ne_lDg : lrA ≠ lDg := by decide
@[simp] theorem ldr_lDg_ne_lrA : lDg ≠ lrA := by decide
@[simp] theorem ldr_lrA_ne_lDi : lrA ≠ lDi := by decide
@[simp] theorem ldr_lDi_ne_lrA : lDi ≠ lrA := by decide
@[simp] theorem ldr_lrA_ne_lRp : lrA ≠ lRp := by decide
@[simp] theorem ldr_lRp_ne_lrA : lRp ≠ lrA := by decide
@[simp] theorem ldr_lrA_ne_lRn : lrA ≠ lRn := by decide
@[simp] theorem ldr_lRn_ne_lrA : lRn ≠ lrA := by decide
@[simp] theorem ldr_lrA_ne_lFle : lrA ≠ lFle := by decide
@[simp] theorem ldr_lFle_ne_lrA : lFle ≠ lrA := by decide
@[simp] theorem ldr_lrA_ne_lKb : lrA ≠ lKb := by decide
@[simp] theorem ldr_lKb_ne_lrA : lKb ≠ lrA := by decide
@[simp] theorem ldr_lrA_ne_lDir : lrA ≠ lDir := by decide
@[simp] theorem ldr_lDir_ne_lrA : lDir ≠ lrA := by decide
@[simp] theorem ldr_lrA_ne_lFln : lrA ≠ lFln := by decide
@[simp] theorem ldr_lFln_ne_lrA : lFln ≠ lrA := by decide
@[simp] theorem ldr_lrA_ne_lFll : lrA ≠ lFll := by decide
@[simp] theorem ldr_lFll_ne_lrA : lFll ≠ lrA := by decide
@[simp] theorem ldr_lrA_ne_lFls : lrA ≠ lFls := by decide
@[simp] theorem ldr_lFls_ne_lrA : lFls ≠ lrA := by decide
@[simp] theorem ldr_lrA_ne_kFu : lrA ≠ kFu := by decide
@[simp] theorem ldr_kFu_ne_lrA : kFu ≠ lrA := by decide
@[simp] theorem ldr_lrA_ne_kD : lrA ≠ kD := by decide
@[simp] theorem ldr_kD_ne_lrA : kD ≠ lrA := by decide
@[simp] theorem ldr_lrB_ne_lrF : lrB ≠ lrF := by decide
@[simp] theorem ldr_lrB_ne_lrA : lrB ≠ lrA := by decide
@[simp] theorem ldr_lrB_ne_lrO : lrB ≠ lrO := by decide
@[simp] theorem ldr_lrB_ne_lrN : lrB ≠ lrN := by decide
@[simp] theorem ldr_lrB_ne_lrX : lrB ≠ lrX := by decide
@[simp] theorem ldr_lrB_ne_lrV : lrB ≠ lrV := by decide
@[simp] theorem ldr_lrB_ne_lrY : lrB ≠ lrY := by decide
@[simp] theorem ldr_lrB_ne_lrS : lrB ≠ lrS := by decide
@[simp] theorem ldr_lrB_ne_lrA2 : lrB ≠ lrA2 := by decide
@[simp] theorem ldr_lrB_ne_lrB2 : lrB ≠ lrB2 := by decide
@[simp] theorem ldr_lrB_ne_lrW : lrB ≠ lrW := by decide
@[simp] theorem ldr_lrB_ne_lrR : lrB ≠ lrR := by decide
@[simp] theorem ldr_lrB_ne_lFl : lrB ≠ lFl := by decide
@[simp] theorem ldr_lFl_ne_lrB : lFl ≠ lrB := by decide
@[simp] theorem ldr_lrB_ne_lDh : lrB ≠ lDh := by decide
@[simp] theorem ldr_lDh_ne_lrB : lDh ≠ lrB := by decide
@[simp] theorem ldr_lrB_ne_lDt : lrB ≠ lDt := by decide
@[simp] theorem ldr_lDt_ne_lrB : lDt ≠ lrB := by decide
@[simp] theorem ldr_lrB_ne_lDg : lrB ≠ lDg := by decide
@[simp] theorem ldr_lDg_ne_lrB : lDg ≠ lrB := by decide
@[simp] theorem ldr_lrB_ne_lDi : lrB ≠ lDi := by decide
@[simp] theorem ldr_lDi_ne_lrB : lDi ≠ lrB := by decide
@[simp] theorem ldr_lrB_ne_lRp : lrB ≠ lRp := by decide
@[simp] theorem ldr_lRp_ne_lrB : lRp ≠ lrB := by decide
@[simp] theorem ldr_lrB_ne_lRn : lrB ≠ lRn := by decide
@[simp] theorem ldr_lRn_ne_lrB : lRn ≠ lrB := by decide
@[simp] theorem ldr_lrB_ne_lFle : lrB ≠ lFle := by decide
@[simp] theorem ldr_lFle_ne_lrB : lFle ≠ lrB := by decide
@[simp] theorem ldr_lrB_ne_lKb : lrB ≠ lKb := by decide
@[simp] theorem ldr_lKb_ne_lrB : lKb ≠ lrB := by decide
@[simp] theorem ldr_lrB_ne_lDir : lrB ≠ lDir := by decide
@[simp] theorem ldr_lDir_ne_lrB : lDir ≠ lrB := by decide
@[simp] theorem ldr_lrB_ne_lFln : lrB ≠ lFln := by decide
@[simp] theorem ldr_lFln_ne_lrB : lFln ≠ lrB := by decide
@[simp] theorem ldr_lrB_ne_lFll : lrB ≠ lFll := by decide
@[simp] theorem ldr_lFll_ne_lrB : lFll ≠ lrB := by decide
@[simp] theorem ldr_lrB_ne_lFls : lrB ≠ lFls := by decide
@[simp] theorem ldr_lFls_ne_lrB : lFls ≠ lrB := by decide
@[simp] theorem ldr_lrB_ne_kFu : lrB ≠ kFu := by decide
@[simp] theorem ldr_kFu_ne_lrB : kFu ≠ lrB := by decide
@[simp] theorem ldr_lrB_ne_kD : lrB ≠ kD := by decide
@[simp] theorem ldr_kD_ne_lrB : kD ≠ lrB := by decide
@[simp] theorem ldr_lrO_ne_lrF : lrO ≠ lrF := by decide
@[simp] theorem ldr_lrO_ne_lrA : lrO ≠ lrA := by decide
@[simp] theorem ldr_lrO_ne_lrB : lrO ≠ lrB := by decide
@[simp] theorem ldr_lrO_ne_lrN : lrO ≠ lrN := by decide
@[simp] theorem ldr_lrO_ne_lrX : lrO ≠ lrX := by decide
@[simp] theorem ldr_lrO_ne_lrV : lrO ≠ lrV := by decide
@[simp] theorem ldr_lrO_ne_lrY : lrO ≠ lrY := by decide
@[simp] theorem ldr_lrO_ne_lrS : lrO ≠ lrS := by decide
@[simp] theorem ldr_lrO_ne_lrA2 : lrO ≠ lrA2 := by decide
@[simp] theorem ldr_lrO_ne_lrB2 : lrO ≠ lrB2 := by decide
@[simp] theorem ldr_lrO_ne_lrW : lrO ≠ lrW := by decide
@[simp] theorem ldr_lrO_ne_lrR : lrO ≠ lrR := by decide
@[simp] theorem ldr_lrO_ne_lFl : lrO ≠ lFl := by decide
@[simp] theorem ldr_lFl_ne_lrO : lFl ≠ lrO := by decide
@[simp] theorem ldr_lrO_ne_lDh : lrO ≠ lDh := by decide
@[simp] theorem ldr_lDh_ne_lrO : lDh ≠ lrO := by decide
@[simp] theorem ldr_lrO_ne_lDt : lrO ≠ lDt := by decide
@[simp] theorem ldr_lDt_ne_lrO : lDt ≠ lrO := by decide
@[simp] theorem ldr_lrO_ne_lDg : lrO ≠ lDg := by decide
@[simp] theorem ldr_lDg_ne_lrO : lDg ≠ lrO := by decide
@[simp] theorem ldr_lrO_ne_lDi : lrO ≠ lDi := by decide
@[simp] theorem ldr_lDi_ne_lrO : lDi ≠ lrO := by decide
@[simp] theorem ldr_lrO_ne_lRp : lrO ≠ lRp := by decide
@[simp] theorem ldr_lRp_ne_lrO : lRp ≠ lrO := by decide
@[simp] theorem ldr_lrO_ne_lRn : lrO ≠ lRn := by decide
@[simp] theorem ldr_lRn_ne_lrO : lRn ≠ lrO := by decide
@[simp] theorem ldr_lrO_ne_lFle : lrO ≠ lFle := by decide
@[simp] theorem ldr_lFle_ne_lrO : lFle ≠ lrO := by decide
@[simp] theorem ldr_lrO_ne_lKb : lrO ≠ lKb := by decide
@[simp] theorem ldr_lKb_ne_lrO : lKb ≠ lrO := by decide
@[simp] theorem ldr_lrO_ne_lDir : lrO ≠ lDir := by decide
@[simp] theorem ldr_lDir_ne_lrO : lDir ≠ lrO := by decide
@[simp] theorem ldr_lrO_ne_lFln : lrO ≠ lFln := by decide
@[simp] theorem ldr_lFln_ne_lrO : lFln ≠ lrO := by decide
@[simp] theorem ldr_lrO_ne_lFll : lrO ≠ lFll := by decide
@[simp] theorem ldr_lFll_ne_lrO : lFll ≠ lrO := by decide
@[simp] theorem ldr_lrO_ne_lFls : lrO ≠ lFls := by decide
@[simp] theorem ldr_lFls_ne_lrO : lFls ≠ lrO := by decide
@[simp] theorem ldr_lrO_ne_kFu : lrO ≠ kFu := by decide
@[simp] theorem ldr_kFu_ne_lrO : kFu ≠ lrO := by decide
@[simp] theorem ldr_lrO_ne_kD : lrO ≠ kD := by decide
@[simp] theorem ldr_kD_ne_lrO : kD ≠ lrO := by decide
@[simp] theorem ldr_lrN_ne_lrF : lrN ≠ lrF := by decide
@[simp] theorem ldr_lrN_ne_lrA : lrN ≠ lrA := by decide
@[simp] theorem ldr_lrN_ne_lrB : lrN ≠ lrB := by decide
@[simp] theorem ldr_lrN_ne_lrO : lrN ≠ lrO := by decide
@[simp] theorem ldr_lrN_ne_lrX : lrN ≠ lrX := by decide
@[simp] theorem ldr_lrN_ne_lrV : lrN ≠ lrV := by decide
@[simp] theorem ldr_lrN_ne_lrY : lrN ≠ lrY := by decide
@[simp] theorem ldr_lrN_ne_lrS : lrN ≠ lrS := by decide
@[simp] theorem ldr_lrN_ne_lrA2 : lrN ≠ lrA2 := by decide
@[simp] theorem ldr_lrN_ne_lrB2 : lrN ≠ lrB2 := by decide
@[simp] theorem ldr_lrN_ne_lrW : lrN ≠ lrW := by decide
@[simp] theorem ldr_lrN_ne_lrR : lrN ≠ lrR := by decide
@[simp] theorem ldr_lrN_ne_lFl : lrN ≠ lFl := by decide
@[simp] theorem ldr_lFl_ne_lrN : lFl ≠ lrN := by decide
@[simp] theorem ldr_lrN_ne_lDh : lrN ≠ lDh := by decide
@[simp] theorem ldr_lDh_ne_lrN : lDh ≠ lrN := by decide
@[simp] theorem ldr_lrN_ne_lDt : lrN ≠ lDt := by decide
@[simp] theorem ldr_lDt_ne_lrN : lDt ≠ lrN := by decide
@[simp] theorem ldr_lrN_ne_lDg : lrN ≠ lDg := by decide
@[simp] theorem ldr_lDg_ne_lrN : lDg ≠ lrN := by decide
@[simp] theorem ldr_lrN_ne_lDi : lrN ≠ lDi := by decide
@[simp] theorem ldr_lDi_ne_lrN : lDi ≠ lrN := by decide
@[simp] theorem ldr_lrN_ne_lRp : lrN ≠ lRp := by decide
@[simp] theorem ldr_lRp_ne_lrN : lRp ≠ lrN := by decide
@[simp] theorem ldr_lrN_ne_lRn : lrN ≠ lRn := by decide
@[simp] theorem ldr_lRn_ne_lrN : lRn ≠ lrN := by decide
@[simp] theorem ldr_lrN_ne_lFle : lrN ≠ lFle := by decide
@[simp] theorem ldr_lFle_ne_lrN : lFle ≠ lrN := by decide
@[simp] theorem ldr_lrN_ne_lKb : lrN ≠ lKb := by decide
@[simp] theorem ldr_lKb_ne_lrN : lKb ≠ lrN := by decide
@[simp] theorem ldr_lrN_ne_lDir : lrN ≠ lDir := by decide
@[simp] theorem ldr_lDir_ne_lrN : lDir ≠ lrN := by decide
@[simp] theorem ldr_lrN_ne_lFln : lrN ≠ lFln := by decide
@[simp] theorem ldr_lFln_ne_lrN : lFln ≠ lrN := by decide
@[simp] theorem ldr_lrN_ne_lFll : lrN ≠ lFll := by decide
@[simp] theorem ldr_lFll_ne_lrN : lFll ≠ lrN := by decide
@[simp] theorem ldr_lrN_ne_lFls : lrN ≠ lFls := by decide
@[simp] theorem ldr_lFls_ne_lrN : lFls ≠ lrN := by decide
@[simp] theorem ldr_lrN_ne_kFu : lrN ≠ kFu := by decide
@[simp] theorem ldr_kFu_ne_lrN : kFu ≠ lrN := by decide
@[simp] theorem ldr_lrN_ne_kD : lrN ≠ kD := by decide
@[simp] theorem ldr_kD_ne_lrN : kD ≠ lrN := by decide
@[simp] theorem ldr_lrX_ne_lrF : lrX ≠ lrF := by decide
@[simp] theorem ldr_lrX_ne_lrA : lrX ≠ lrA := by decide
@[simp] theorem ldr_lrX_ne_lrB : lrX ≠ lrB := by decide
@[simp] theorem ldr_lrX_ne_lrO : lrX ≠ lrO := by decide
@[simp] theorem ldr_lrX_ne_lrN : lrX ≠ lrN := by decide
@[simp] theorem ldr_lrX_ne_lrV : lrX ≠ lrV := by decide
@[simp] theorem ldr_lrX_ne_lrY : lrX ≠ lrY := by decide
@[simp] theorem ldr_lrX_ne_lrS : lrX ≠ lrS := by decide
@[simp] theorem ldr_lrX_ne_lrA2 : lrX ≠ lrA2 := by decide
@[simp] theorem ldr_lrX_ne_lrB2 : lrX ≠ lrB2 := by decide
@[simp] theorem ldr_lrX_ne_lrW : lrX ≠ lrW := by decide
@[simp] theorem ldr_lrX_ne_lrR : lrX ≠ lrR := by decide
@[simp] theorem ldr_lrX_ne_lFl : lrX ≠ lFl := by decide
@[simp] theorem ldr_lFl_ne_lrX : lFl ≠ lrX := by decide
@[simp] theorem ldr_lrX_ne_lDh : lrX ≠ lDh := by decide
@[simp] theorem ldr_lDh_ne_lrX : lDh ≠ lrX := by decide
@[simp] theorem ldr_lrX_ne_lDt : lrX ≠ lDt := by decide
@[simp] theorem ldr_lDt_ne_lrX : lDt ≠ lrX := by decide
@[simp] theorem ldr_lrX_ne_lDg : lrX ≠ lDg := by decide
@[simp] theorem ldr_lDg_ne_lrX : lDg ≠ lrX := by decide
@[simp] theorem ldr_lrX_ne_lDi : lrX ≠ lDi := by decide
@[simp] theorem ldr_lDi_ne_lrX : lDi ≠ lrX := by decide
@[simp] theorem ldr_lrX_ne_lRp : lrX ≠ lRp := by decide
@[simp] theorem ldr_lRp_ne_lrX : lRp ≠ lrX := by decide
@[simp] theorem ldr_lrX_ne_lRn : lrX ≠ lRn := by decide
@[simp] theorem ldr_lRn_ne_lrX : lRn ≠ lrX := by decide
@[simp] theorem ldr_lrX_ne_lFle : lrX ≠ lFle := by decide
@[simp] theorem ldr_lFle_ne_lrX : lFle ≠ lrX := by decide
@[simp] theorem ldr_lrX_ne_lKb : lrX ≠ lKb := by decide
@[simp] theorem ldr_lKb_ne_lrX : lKb ≠ lrX := by decide
@[simp] theorem ldr_lrX_ne_lDir : lrX ≠ lDir := by decide
@[simp] theorem ldr_lDir_ne_lrX : lDir ≠ lrX := by decide
@[simp] theorem ldr_lrX_ne_lFln : lrX ≠ lFln := by decide
@[simp] theorem ldr_lFln_ne_lrX : lFln ≠ lrX := by decide
@[simp] theorem ldr_lrX_ne_lFll : lrX ≠ lFll := by decide
@[simp] theorem ldr_lFll_ne_lrX : lFll ≠ lrX := by decide
@[simp] theorem ldr_lrX_ne_lFls : lrX ≠ lFls := by decide
@[simp] theorem ldr_lFls_ne_lrX : lFls ≠ lrX := by decide
@[simp] theorem ldr_lrX_ne_kFu : lrX ≠ kFu := by decide
@[simp] theorem ldr_kFu_ne_lrX : kFu ≠ lrX := by decide
@[simp] theorem ldr_lrX_ne_kD : lrX ≠ kD := by decide
@[simp] theorem ldr_kD_ne_lrX : kD ≠ lrX := by decide
@[simp] theorem ldr_lrV_ne_lrF : lrV ≠ lrF := by decide
@[simp] theorem ldr_lrV_ne_lrA : lrV ≠ lrA := by decide
@[simp] theorem ldr_lrV_ne_lrB : lrV ≠ lrB := by decide
@[simp] theorem ldr_lrV_ne_lrO : lrV ≠ lrO := by decide
@[simp] theorem ldr_lrV_ne_lrN : lrV ≠ lrN := by decide
@[simp] theorem ldr_lrV_ne_lrX : lrV ≠ lrX := by decide
@[simp] theorem ldr_lrV_ne_lrY : lrV ≠ lrY := by decide
@[simp] theorem ldr_lrV_ne_lrS : lrV ≠ lrS := by decide
@[simp] theorem ldr_lrV_ne_lrA2 : lrV ≠ lrA2 := by decide
@[simp] theorem ldr_lrV_ne_lrB2 : lrV ≠ lrB2 := by decide
@[simp] theorem ldr_lrV_ne_lrW : lrV ≠ lrW := by decide
@[simp] theorem ldr_lrV_ne_lrR : lrV ≠ lrR := by decide
@[simp] theorem ldr_lrV_ne_lFl : lrV ≠ lFl := by decide
@[simp] theorem ldr_lFl_ne_lrV : lFl ≠ lrV := by decide
@[simp] theorem ldr_lrV_ne_lDh : lrV ≠ lDh := by decide
@[simp] theorem ldr_lDh_ne_lrV : lDh ≠ lrV := by decide
@[simp] theorem ldr_lrV_ne_lDt : lrV ≠ lDt := by decide
@[simp] theorem ldr_lDt_ne_lrV : lDt ≠ lrV := by decide
@[simp] theorem ldr_lrV_ne_lDg : lrV ≠ lDg := by decide
@[simp] theorem ldr_lDg_ne_lrV : lDg ≠ lrV := by decide
@[simp] theorem ldr_lrV_ne_lDi : lrV ≠ lDi := by decide
@[simp] theorem ldr_lDi_ne_lrV : lDi ≠ lrV := by decide
@[simp] theorem ldr_lrV_ne_lRp : lrV ≠ lRp := by decide
@[simp] theorem ldr_lRp_ne_lrV : lRp ≠ lrV := by decide
@[simp] theorem ldr_lrV_ne_lRn : lrV ≠ lRn := by decide
@[simp] theorem ldr_lRn_ne_lrV : lRn ≠ lrV := by decide
@[simp] theorem ldr_lrV_ne_lFle : lrV ≠ lFle := by decide
@[simp] theorem ldr_lFle_ne_lrV : lFle ≠ lrV := by decide
@[simp] theorem ldr_lrV_ne_lKb : lrV ≠ lKb := by decide
@[simp] theorem ldr_lKb_ne_lrV : lKb ≠ lrV := by decide
@[simp] theorem ldr_lrV_ne_lDir : lrV ≠ lDir := by decide
@[simp] theorem ldr_lDir_ne_lrV : lDir ≠ lrV := by decide
@[simp] theorem ldr_lrV_ne_lFln : lrV ≠ lFln := by decide
@[simp] theorem ldr_lFln_ne_lrV : lFln ≠ lrV := by decide
@[simp] theorem ldr_lrV_ne_lFll : lrV ≠ lFll := by decide
@[simp] theorem ldr_lFll_ne_lrV : lFll ≠ lrV := by decide
@[simp] theorem ldr_lrV_ne_lFls : lrV ≠ lFls := by decide
@[simp] theorem ldr_lFls_ne_lrV : lFls ≠ lrV := by decide
@[simp] theorem ldr_lrV_ne_kFu : lrV ≠ kFu := by decide
@[simp] theorem ldr_kFu_ne_lrV : kFu ≠ lrV := by decide
@[simp] theorem ldr_lrV_ne_kD : lrV ≠ kD := by decide
@[simp] theorem ldr_kD_ne_lrV : kD ≠ lrV := by decide
@[simp] theorem ldr_lrY_ne_lrF : lrY ≠ lrF := by decide
@[simp] theorem ldr_lrY_ne_lrA : lrY ≠ lrA := by decide
@[simp] theorem ldr_lrY_ne_lrB : lrY ≠ lrB := by decide
@[simp] theorem ldr_lrY_ne_lrO : lrY ≠ lrO := by decide
@[simp] theorem ldr_lrY_ne_lrN : lrY ≠ lrN := by decide
@[simp] theorem ldr_lrY_ne_lrX : lrY ≠ lrX := by decide
@[simp] theorem ldr_lrY_ne_lrV : lrY ≠ lrV := by decide
@[simp] theorem ldr_lrY_ne_lrS : lrY ≠ lrS := by decide
@[simp] theorem ldr_lrY_ne_lrA2 : lrY ≠ lrA2 := by decide
@[simp] theorem ldr_lrY_ne_lrB2 : lrY ≠ lrB2 := by decide
@[simp] theorem ldr_lrY_ne_lrW : lrY ≠ lrW := by decide
@[simp] theorem ldr_lrY_ne_lrR : lrY ≠ lrR := by decide
@[simp] theorem ldr_lrY_ne_lFl : lrY ≠ lFl := by decide
@[simp] theorem ldr_lFl_ne_lrY : lFl ≠ lrY := by decide
@[simp] theorem ldr_lrY_ne_lDh : lrY ≠ lDh := by decide
@[simp] theorem ldr_lDh_ne_lrY : lDh ≠ lrY := by decide
@[simp] theorem ldr_lrY_ne_lDt : lrY ≠ lDt := by decide
@[simp] theorem ldr_lDt_ne_lrY : lDt ≠ lrY := by decide
@[simp] theorem ldr_lrY_ne_lDg : lrY ≠ lDg := by decide
@[simp] theorem ldr_lDg_ne_lrY : lDg ≠ lrY := by decide
@[simp] theorem ldr_lrY_ne_lDi : lrY ≠ lDi := by decide
@[simp] theorem ldr_lDi_ne_lrY : lDi ≠ lrY := by decide
@[simp] theorem ldr_lrY_ne_lRp : lrY ≠ lRp := by decide
@[simp] theorem ldr_lRp_ne_lrY : lRp ≠ lrY := by decide
@[simp] theorem ldr_lrY_ne_lRn : lrY ≠ lRn := by decide
@[simp] theorem ldr_lRn_ne_lrY : lRn ≠ lrY := by decide
@[simp] theorem ldr_lrY_ne_lFle : lrY ≠ lFle := by decide
@[simp] theorem ldr_lFle_ne_lrY : lFle ≠ lrY := by decide
@[simp] theorem ldr_lrY_ne_lKb : lrY ≠ lKb := by decide
@[simp] theorem ldr_lKb_ne_lrY : lKb ≠ lrY := by decide
@[simp] theorem ldr_lrY_ne_lDir : lrY ≠ lDir := by decide
@[simp] theorem ldr_lDir_ne_lrY : lDir ≠ lrY := by decide
@[simp] theorem ldr_lrY_ne_lFln : lrY ≠ lFln := by decide
@[simp] theorem ldr_lFln_ne_lrY : lFln ≠ lrY := by decide
@[simp] theorem ldr_lrY_ne_lFll : lrY ≠ lFll := by decide
@[simp] theorem ldr_lFll_ne_lrY : lFll ≠ lrY := by decide
@[simp] theorem ldr_lrY_ne_lFls : lrY ≠ lFls := by decide
@[simp] theorem ldr_lFls_ne_lrY : lFls ≠ lrY := by decide
@[simp] theorem ldr_lrY_ne_kFu : lrY ≠ kFu := by decide
@[simp] theorem ldr_kFu_ne_lrY : kFu ≠ lrY := by decide
@[simp] theorem ldr_lrY_ne_kD : lrY ≠ kD := by decide
@[simp] theorem ldr_kD_ne_lrY : kD ≠ lrY := by decide
@[simp] theorem ldr_lrS_ne_lrF : lrS ≠ lrF := by decide
@[simp] theorem ldr_lrS_ne_lrA : lrS ≠ lrA := by decide
@[simp] theorem ldr_lrS_ne_lrB : lrS ≠ lrB := by decide
@[simp] theorem ldr_lrS_ne_lrO : lrS ≠ lrO := by decide
@[simp] theorem ldr_lrS_ne_lrN : lrS ≠ lrN := by decide
@[simp] theorem ldr_lrS_ne_lrX : lrS ≠ lrX := by decide
@[simp] theorem ldr_lrS_ne_lrV : lrS ≠ lrV := by decide
@[simp] theorem ldr_lrS_ne_lrY : lrS ≠ lrY := by decide
@[simp] theorem ldr_lrS_ne_lrA2 : lrS ≠ lrA2 := by decide
@[simp] theorem ldr_lrS_ne_lrB2 : lrS ≠ lrB2 := by decide
@[simp] theorem ldr_lrS_ne_lrW : lrS ≠ lrW := by decide
@[simp] theorem ldr_lrS_ne_lrR : lrS ≠ lrR := by decide
@[simp] theorem ldr_lrS_ne_lFl : lrS ≠ lFl := by decide
@[simp] theorem ldr_lFl_ne_lrS : lFl ≠ lrS := by decide
@[simp] theorem ldr_lrS_ne_lDh : lrS ≠ lDh := by decide
@[simp] theorem ldr_lDh_ne_lrS : lDh ≠ lrS := by decide
@[simp] theorem ldr_lrS_ne_lDt : lrS ≠ lDt := by decide
@[simp] theorem ldr_lDt_ne_lrS : lDt ≠ lrS := by decide
@[simp] theorem ldr_lrS_ne_lDg : lrS ≠ lDg := by decide
@[simp] theorem ldr_lDg_ne_lrS : lDg ≠ lrS := by decide
@[simp] theorem ldr_lrS_ne_lDi : lrS ≠ lDi := by decide
@[simp] theorem ldr_lDi_ne_lrS : lDi ≠ lrS := by decide
@[simp] theorem ldr_lrS_ne_lRp : lrS ≠ lRp := by decide
@[simp] theorem ldr_lRp_ne_lrS : lRp ≠ lrS := by decide
@[simp] theorem ldr_lrS_ne_lRn : lrS ≠ lRn := by decide
@[simp] theorem ldr_lRn_ne_lrS : lRn ≠ lrS := by decide
@[simp] theorem ldr_lrS_ne_lFle : lrS ≠ lFle := by decide
@[simp] theorem ldr_lFle_ne_lrS : lFle ≠ lrS := by decide
@[simp] theorem ldr_lrS_ne_lKb : lrS ≠ lKb := by decide
@[simp] theorem ldr_lKb_ne_lrS : lKb ≠ lrS := by decide
@[simp] theorem ldr_lrS_ne_lDir : lrS ≠ lDir := by decide
@[simp] theorem ldr_lDir_ne_lrS : lDir ≠ lrS := by decide
@[simp] theorem ldr_lrS_ne_lFln : lrS ≠ lFln := by decide
@[simp] theorem ldr_lFln_ne_lrS : lFln ≠ lrS := by decide
@[simp] theorem ldr_lrS_ne_lFll : lrS ≠ lFll := by decide
@[simp] theorem ldr_lFll_ne_lrS : lFll ≠ lrS := by decide
@[simp] theorem ldr_lrS_ne_lFls : lrS ≠ lFls := by decide
@[simp] theorem ldr_lFls_ne_lrS : lFls ≠ lrS := by decide
@[simp] theorem ldr_lrS_ne_kFu : lrS ≠ kFu := by decide
@[simp] theorem ldr_kFu_ne_lrS : kFu ≠ lrS := by decide
@[simp] theorem ldr_lrS_ne_kD : lrS ≠ kD := by decide
@[simp] theorem ldr_kD_ne_lrS : kD ≠ lrS := by decide
@[simp] theorem ldr_lrA2_ne_lrF : lrA2 ≠ lrF := by decide
@[simp] theorem ldr_lrA2_ne_lrA : lrA2 ≠ lrA := by decide
@[simp] theorem ldr_lrA2_ne_lrB : lrA2 ≠ lrB := by decide
@[simp] theorem ldr_lrA2_ne_lrO : lrA2 ≠ lrO := by decide
@[simp] theorem ldr_lrA2_ne_lrN : lrA2 ≠ lrN := by decide
@[simp] theorem ldr_lrA2_ne_lrX : lrA2 ≠ lrX := by decide
@[simp] theorem ldr_lrA2_ne_lrV : lrA2 ≠ lrV := by decide
@[simp] theorem ldr_lrA2_ne_lrY : lrA2 ≠ lrY := by decide
@[simp] theorem ldr_lrA2_ne_lrS : lrA2 ≠ lrS := by decide
@[simp] theorem ldr_lrA2_ne_lrB2 : lrA2 ≠ lrB2 := by decide
@[simp] theorem ldr_lrA2_ne_lrW : lrA2 ≠ lrW := by decide
@[simp] theorem ldr_lrA2_ne_lrR : lrA2 ≠ lrR := by decide
@[simp] theorem ldr_lrA2_ne_lFl : lrA2 ≠ lFl := by decide
@[simp] theorem ldr_lFl_ne_lrA2 : lFl ≠ lrA2 := by decide
@[simp] theorem ldr_lrA2_ne_lDh : lrA2 ≠ lDh := by decide
@[simp] theorem ldr_lDh_ne_lrA2 : lDh ≠ lrA2 := by decide
@[simp] theorem ldr_lrA2_ne_lDt : lrA2 ≠ lDt := by decide
@[simp] theorem ldr_lDt_ne_lrA2 : lDt ≠ lrA2 := by decide
@[simp] theorem ldr_lrA2_ne_lDg : lrA2 ≠ lDg := by decide
@[simp] theorem ldr_lDg_ne_lrA2 : lDg ≠ lrA2 := by decide
@[simp] theorem ldr_lrA2_ne_lDi : lrA2 ≠ lDi := by decide
@[simp] theorem ldr_lDi_ne_lrA2 : lDi ≠ lrA2 := by decide
@[simp] theorem ldr_lrA2_ne_lRp : lrA2 ≠ lRp := by decide
@[simp] theorem ldr_lRp_ne_lrA2 : lRp ≠ lrA2 := by decide
@[simp] theorem ldr_lrA2_ne_lRn : lrA2 ≠ lRn := by decide
@[simp] theorem ldr_lRn_ne_lrA2 : lRn ≠ lrA2 := by decide
@[simp] theorem ldr_lrA2_ne_lFle : lrA2 ≠ lFle := by decide
@[simp] theorem ldr_lFle_ne_lrA2 : lFle ≠ lrA2 := by decide
@[simp] theorem ldr_lrA2_ne_lKb : lrA2 ≠ lKb := by decide
@[simp] theorem ldr_lKb_ne_lrA2 : lKb ≠ lrA2 := by decide
@[simp] theorem ldr_lrA2_ne_lDir : lrA2 ≠ lDir := by decide
@[simp] theorem ldr_lDir_ne_lrA2 : lDir ≠ lrA2 := by decide
@[simp] theorem ldr_lrA2_ne_lFln : lrA2 ≠ lFln := by decide
@[simp] theorem ldr_lFln_ne_lrA2 : lFln ≠ lrA2 := by decide
@[simp] theorem ldr_lrA2_ne_lFll : lrA2 ≠ lFll := by decide
@[simp] theorem ldr_lFll_ne_lrA2 : lFll ≠ lrA2 := by decide
@[simp] theorem ldr_lrA2_ne_lFls : lrA2 ≠ lFls := by decide
@[simp] theorem ldr_lFls_ne_lrA2 : lFls ≠ lrA2 := by decide
@[simp] theorem ldr_lrA2_ne_kFu : lrA2 ≠ kFu := by decide
@[simp] theorem ldr_kFu_ne_lrA2 : kFu ≠ lrA2 := by decide
@[simp] theorem ldr_lrA2_ne_kD : lrA2 ≠ kD := by decide
@[simp] theorem ldr_kD_ne_lrA2 : kD ≠ lrA2 := by decide
@[simp] theorem ldr_lrB2_ne_lrF : lrB2 ≠ lrF := by decide
@[simp] theorem ldr_lrB2_ne_lrA : lrB2 ≠ lrA := by decide
@[simp] theorem ldr_lrB2_ne_lrB : lrB2 ≠ lrB := by decide
@[simp] theorem ldr_lrB2_ne_lrO : lrB2 ≠ lrO := by decide
@[simp] theorem ldr_lrB2_ne_lrN : lrB2 ≠ lrN := by decide
@[simp] theorem ldr_lrB2_ne_lrX : lrB2 ≠ lrX := by decide
@[simp] theorem ldr_lrB2_ne_lrV : lrB2 ≠ lrV := by decide
@[simp] theorem ldr_lrB2_ne_lrY : lrB2 ≠ lrY := by decide
@[simp] theorem ldr_lrB2_ne_lrS : lrB2 ≠ lrS := by decide
@[simp] theorem ldr_lrB2_ne_lrA2 : lrB2 ≠ lrA2 := by decide
@[simp] theorem ldr_lrB2_ne_lrW : lrB2 ≠ lrW := by decide
@[simp] theorem ldr_lrB2_ne_lrR : lrB2 ≠ lrR := by decide
@[simp] theorem ldr_lrB2_ne_lFl : lrB2 ≠ lFl := by decide
@[simp] theorem ldr_lFl_ne_lrB2 : lFl ≠ lrB2 := by decide
@[simp] theorem ldr_lrB2_ne_lDh : lrB2 ≠ lDh := by decide
@[simp] theorem ldr_lDh_ne_lrB2 : lDh ≠ lrB2 := by decide
@[simp] theorem ldr_lrB2_ne_lDt : lrB2 ≠ lDt := by decide
@[simp] theorem ldr_lDt_ne_lrB2 : lDt ≠ lrB2 := by decide
@[simp] theorem ldr_lrB2_ne_lDg : lrB2 ≠ lDg := by decide
@[simp] theorem ldr_lDg_ne_lrB2 : lDg ≠ lrB2 := by decide
@[simp] theorem ldr_lrB2_ne_lDi : lrB2 ≠ lDi := by decide
@[simp] theorem ldr_lDi_ne_lrB2 : lDi ≠ lrB2 := by decide
@[simp] theorem ldr_lrB2_ne_lRp : lrB2 ≠ lRp := by decide
@[simp] theorem ldr_lRp_ne_lrB2 : lRp ≠ lrB2 := by decide
@[simp] theorem ldr_lrB2_ne_lRn : lrB2 ≠ lRn := by decide
@[simp] theorem ldr_lRn_ne_lrB2 : lRn ≠ lrB2 := by decide
@[simp] theorem ldr_lrB2_ne_lFle : lrB2 ≠ lFle := by decide
@[simp] theorem ldr_lFle_ne_lrB2 : lFle ≠ lrB2 := by decide
@[simp] theorem ldr_lrB2_ne_lKb : lrB2 ≠ lKb := by decide
@[simp] theorem ldr_lKb_ne_lrB2 : lKb ≠ lrB2 := by decide
@[simp] theorem ldr_lrB2_ne_lDir : lrB2 ≠ lDir := by decide
@[simp] theorem ldr_lDir_ne_lrB2 : lDir ≠ lrB2 := by decide
@[simp] theorem ldr_lrB2_ne_lFln : lrB2 ≠ lFln := by decide
@[simp] theorem ldr_lFln_ne_lrB2 : lFln ≠ lrB2 := by decide
@[simp] theorem ldr_lrB2_ne_lFll : lrB2 ≠ lFll := by decide
@[simp] theorem ldr_lFll_ne_lrB2 : lFll ≠ lrB2 := by decide
@[simp] theorem ldr_lrB2_ne_lFls : lrB2 ≠ lFls := by decide
@[simp] theorem ldr_lFls_ne_lrB2 : lFls ≠ lrB2 := by decide
@[simp] theorem ldr_lrB2_ne_kFu : lrB2 ≠ kFu := by decide
@[simp] theorem ldr_kFu_ne_lrB2 : kFu ≠ lrB2 := by decide
@[simp] theorem ldr_lrB2_ne_kD : lrB2 ≠ kD := by decide
@[simp] theorem ldr_kD_ne_lrB2 : kD ≠ lrB2 := by decide
@[simp] theorem ldr_lrW_ne_lrF : lrW ≠ lrF := by decide
@[simp] theorem ldr_lrW_ne_lrA : lrW ≠ lrA := by decide
@[simp] theorem ldr_lrW_ne_lrB : lrW ≠ lrB := by decide
@[simp] theorem ldr_lrW_ne_lrO : lrW ≠ lrO := by decide
@[simp] theorem ldr_lrW_ne_lrN : lrW ≠ lrN := by decide
@[simp] theorem ldr_lrW_ne_lrX : lrW ≠ lrX := by decide
@[simp] theorem ldr_lrW_ne_lrV : lrW ≠ lrV := by decide
@[simp] theorem ldr_lrW_ne_lrY : lrW ≠ lrY := by decide
@[simp] theorem ldr_lrW_ne_lrS : lrW ≠ lrS := by decide
@[simp] theorem ldr_lrW_ne_lrA2 : lrW ≠ lrA2 := by decide
@[simp] theorem ldr_lrW_ne_lrB2 : lrW ≠ lrB2 := by decide
@[simp] theorem ldr_lrW_ne_lrR : lrW ≠ lrR := by decide
@[simp] theorem ldr_lrW_ne_lFl : lrW ≠ lFl := by decide
@[simp] theorem ldr_lFl_ne_lrW : lFl ≠ lrW := by decide
@[simp] theorem ldr_lrW_ne_lDh : lrW ≠ lDh := by decide
@[simp] theorem ldr_lDh_ne_lrW : lDh ≠ lrW := by decide
@[simp] theorem ldr_lrW_ne_lDt : lrW ≠ lDt := by decide
@[simp] theorem ldr_lDt_ne_lrW : lDt ≠ lrW := by decide
@[simp] theorem ldr_lrW_ne_lDg : lrW ≠ lDg := by decide
@[simp] theorem ldr_lDg_ne_lrW : lDg ≠ lrW := by decide
@[simp] theorem ldr_lrW_ne_lDi : lrW ≠ lDi := by decide
@[simp] theorem ldr_lDi_ne_lrW : lDi ≠ lrW := by decide
@[simp] theorem ldr_lrW_ne_lRp : lrW ≠ lRp := by decide
@[simp] theorem ldr_lRp_ne_lrW : lRp ≠ lrW := by decide
@[simp] theorem ldr_lrW_ne_lRn : lrW ≠ lRn := by decide
@[simp] theorem ldr_lRn_ne_lrW : lRn ≠ lrW := by decide
@[simp] theorem ldr_lrW_ne_lFle : lrW ≠ lFle := by decide
@[simp] theorem ldr_lFle_ne_lrW : lFle ≠ lrW := by decide
@[simp] theorem ldr_lrW_ne_lKb : lrW ≠ lKb := by decide
@[simp] theorem ldr_lKb_ne_lrW : lKb ≠ lrW := by decide
@[simp] theorem ldr_lrW_ne_lDir : lrW ≠ lDir := by decide
@[simp] theorem ldr_lDir_ne_lrW : lDir ≠ lrW := by decide
@[simp] theorem ldr_lrW_ne_lFln : lrW ≠ lFln := by decide
@[simp] theorem ldr_lFln_ne_lrW : lFln ≠ lrW := by decide
@[simp] theorem ldr_lrW_ne_lFll : lrW ≠ lFll := by decide
@[simp] theorem ldr_lFll_ne_lrW : lFll ≠ lrW := by decide
@[simp] theorem ldr_lrW_ne_lFls : lrW ≠ lFls := by decide
@[simp] theorem ldr_lFls_ne_lrW : lFls ≠ lrW := by decide
@[simp] theorem ldr_lrW_ne_kFu : lrW ≠ kFu := by decide
@[simp] theorem ldr_kFu_ne_lrW : kFu ≠ lrW := by decide
@[simp] theorem ldr_lrW_ne_kD : lrW ≠ kD := by decide
@[simp] theorem ldr_kD_ne_lrW : kD ≠ lrW := by decide
@[simp] theorem ldr_lrR_ne_lrF : lrR ≠ lrF := by decide
@[simp] theorem ldr_lrR_ne_lrA : lrR ≠ lrA := by decide
@[simp] theorem ldr_lrR_ne_lrB : lrR ≠ lrB := by decide
@[simp] theorem ldr_lrR_ne_lrO : lrR ≠ lrO := by decide
@[simp] theorem ldr_lrR_ne_lrN : lrR ≠ lrN := by decide
@[simp] theorem ldr_lrR_ne_lrX : lrR ≠ lrX := by decide
@[simp] theorem ldr_lrR_ne_lrV : lrR ≠ lrV := by decide
@[simp] theorem ldr_lrR_ne_lrY : lrR ≠ lrY := by decide
@[simp] theorem ldr_lrR_ne_lrS : lrR ≠ lrS := by decide
@[simp] theorem ldr_lrR_ne_lrA2 : lrR ≠ lrA2 := by decide
@[simp] theorem ldr_lrR_ne_lrB2 : lrR ≠ lrB2 := by decide
@[simp] theorem ldr_lrR_ne_lrW : lrR ≠ lrW := by decide
@[simp] theorem ldr_lrR_ne_lFl : lrR ≠ lFl := by decide
@[simp] theorem ldr_lFl_ne_lrR : lFl ≠ lrR := by decide
@[simp] theorem ldr_lrR_ne_lDh : lrR ≠ lDh := by decide
@[simp] theorem ldr_lDh_ne_lrR : lDh ≠ lrR := by decide
@[simp] theorem ldr_lrR_ne_lDt : lrR ≠ lDt := by decide
@[simp] theorem ldr_lDt_ne_lrR : lDt ≠ lrR := by decide
@[simp] theorem ldr_lrR_ne_lDg : lrR ≠ lDg := by decide
@[simp] theorem ldr_lDg_ne_lrR : lDg ≠ lrR := by decide
@[simp] theorem ldr_lrR_ne_lDi : lrR ≠ lDi := by decide
@[simp] theorem ldr_lDi_ne_lrR : lDi ≠ lrR := by decide
@[simp] theorem ldr_lrR_ne_lRp : lrR ≠ lRp := by decide
@[simp] theorem ldr_lRp_ne_lrR : lRp ≠ lrR := by decide
@[simp] theorem ldr_lrR_ne_lRn : lrR ≠ lRn := by decide
@[simp] theorem ldr_lRn_ne_lrR : lRn ≠ lrR := by decide
@[simp] theorem ldr_lrR_ne_lFle : lrR ≠ lFle := by decide
@[simp] theorem ldr_lFle_ne_lrR : lFle ≠ lrR := by decide
@[simp] theorem ldr_lrR_ne_lKb : lrR ≠ lKb := by decide
@[simp] theorem ldr_lKb_ne_lrR : lKb ≠ lrR := by decide
@[simp] theorem ldr_lrR_ne_lDir : lrR ≠ lDir := by decide
@[simp] theorem ldr_lDir_ne_lrR : lDir ≠ lrR := by decide
@[simp] theorem ldr_lrR_ne_lFln : lrR ≠ lFln := by decide
@[simp] theorem ldr_lFln_ne_lrR : lFln ≠ lrR := by decide
@[simp] theorem ldr_lrR_ne_lFll : lrR ≠ lFll := by decide
@[simp] theorem ldr_lFll_ne_lrR : lFll ≠ lrR := by decide
@[simp] theorem ldr_lrR_ne_lFls : lrR ≠ lFls := by decide
@[simp] theorem ldr_lFls_ne_lrR : lFls ≠ lrR := by decide
@[simp] theorem ldr_lrR_ne_kFu : lrR ≠ kFu := by decide
@[simp] theorem ldr_kFu_ne_lrR : kFu ≠ lrR := by decide
@[simp] theorem ldr_lrR_ne_kD : lrR ≠ kD := by decide
@[simp] theorem ldr_kD_ne_lrR : kD ≠ lrR := by decide

def ldrParams : List MlS := [kFu, kD, lrF, lrA, lrB]
def ldrLocals : List MlS := [lrO, lrN, lrX, lrV, lrY, lrS, lrA2, lrB2, lrW, lrR]
def ldrBody (_v : Bool) (C : Ctx) : ProgHOL 64 := prologue ldrLocals (.ite (.cmp .equal (vv lrF) (.const 0)) hang (.seq (.call (some (some (.local, lrO), none)) fOf [(vv kFu), (vv kD), (vv lrA), (vv lrB)]) (.ite (.cmp .notEqual (vv lrO) (.const 0)) (.return (.op .sub [(vv lrO), (.const 1)])) (.ite (.var .global gEo) (.seq (.assign .local lrN (.const 1)) (.ite (vv lrN) (.seq (.call (some (some (.local, lrX), none)) WB.fRN [(vv kFu), (vv kD), (vv lrA)]) (.ite (.cmp .notEqual (vv lrX) (.const 0)) (.seq (.call (some (some (.local, lrV), none)) fD [(vv kFu), (vv kD), (.op .sub [(vv lrX), (.const 1)]), (vv lrB)]) (.return (vv lrV))) (.seq (.call (some (some (.local, lrY), none)) WB.fRN [(vv kFu), (vv kD), (vv lrB)]) (.ite (.cmp .notEqual (vv lrY) (.const 0)) (.seq (.call (some (some (.local, lrV), none)) fD [(vv kFu), (vv kD), (vv lrA), (.op .sub [(vv lrY), (.const 1)])]) (.return (vv lrV))) (.seq (.call (some (some (.local, lrS), none)) fLds [(vv kFu), (vv kD), (vv lrA), (vv lrB)]) (.ite (.cmp .equal (vv lrS) (.const 0)) (alloc2 C lrW (vv lrA) (vv lrB) (.return (vv lrW))) (.ite (.cmp .equal (vv lrS) (.const 1)) (.return (.const 1)) (.ite (.cmp .equal (vv lrS) (.const 2)) (.return (.const 0)) (.seq (.assign .local lrA2 (.load .one (vv lrS))) (.seq (.assign .local lrB2 (.load .one (.op .add [(vv lrS), (.const 8)]))) (.seq (.call (some (some (.local, lrR), none)) fLdr [(vv kFu), (vv kD), (.op .sub [(vv lrF), (.const 1)]), (vv lrA2), (vv lrB2)]) (.return (vv lrR))))))))))))) (.seq (.call (some (some (.local, lrS), none)) fLds [(vv kFu), (vv kD), (vv lrA), (vv lrB)]) (.ite (.cmp .equal (vv lrS) (.const 0)) (alloc2 C lrW (vv lrA) (vv lrB) (.return (vv lrW))) (.ite (.cmp .equal (vv lrS) (.const 1)) (.return (.const 1)) (.ite (.cmp .equal (vv lrS) (.const 2)) (.return (.const 0)) (.seq (.assign .local lrA2 (.load .one (vv lrS))) (.seq (.assign .local lrB2 (.load .one (.op .add [(vv lrS), (.const 8)]))) (.seq (.call (some (some (.local, lrR), none)) fLdr [(vv kFu), (vv kD), (.op .sub [(vv lrF), (.const 1)]), (vv lrA2), (vv lrB2)]) (.return (vv lrR))))))))))) (.seq (.call (some (some (.local, lrN), none)) fDn [(vv lrA), (vv lrB)]) (.ite (vv lrN) (.seq (.call (some (some (.local, lrX), none)) WB.fRN [(vv kFu), (vv kD), (vv lrA)]) (.ite (.cmp .notEqual (vv lrX) (.const 0)) (.seq (.call (some (some (.local, lrV), none)) fD [(vv kFu), (vv kD), (.op .sub [(vv lrX), (.const 1)]), (vv lrB)]) (.return (vv lrV))) (.seq (.call (some (some (.local, lrY), none)) WB.fRN [(vv kFu), (vv kD), (vv lrB)]) (.ite (.cmp .notEqual (vv lrY) (.const 0)) (.seq (.call (some (some (.local, lrV), none)) fD [(vv kFu), (vv kD), (vv lrA), (.op .sub [(vv lrY), (.const 1)])]) (.return (vv lrV))) (.seq (.call (some (some (.local, lrS), none)) fLds [(vv kFu), (vv kD), (vv lrA), (vv lrB)]) (.ite (.cmp .equal (vv lrS) (.const 0)) (alloc2 C lrW (vv lrA) (vv lrB) (.return (vv lrW))) (.ite (.cmp .equal (vv lrS) (.const 1)) (.return (.const 1)) (.ite (.cmp .equal (vv lrS) (.const 2)) (.return (.const 0)) (.seq (.assign .local lrA2 (.load .one (vv lrS))) (.seq (.assign .local lrB2 (.load .one (.op .add [(vv lrS), (.const 8)]))) (.seq (.call (some (some (.local, lrR), none)) fLdr [(vv kFu), (vv kD), (.op .sub [(vv lrF), (.const 1)]), (vv lrA2), (vv lrB2)]) (.return (vv lrR))))))))))))) (.seq (.call (some (some (.local, lrS), none)) fLds [(vv kFu), (vv kD), (vv lrA), (vv lrB)]) (.ite (.cmp .equal (vv lrS) (.const 0)) (alloc2 C lrW (vv lrA) (vv lrB) (.return (vv lrW))) (.ite (.cmp .equal (vv lrS) (.const 1)) (.return (.const 1)) (.ite (.cmp .equal (vv lrS) (.const 2)) (.return (.const 0)) (.seq (.assign .local lrA2 (.load .one (vv lrS))) (.seq (.assign .local lrB2 (.load .one (.op .add [(vv lrS), (.const 8)]))) (.seq (.call (some (some (.local, lrR), none)) fLdr [(vv kFu), (vv kD), (.op .sub [(vv lrF), (.const 1)]), (vv lrA2), (vv lrB2)]) (.return (vv lrR)))))))))))))))

structure LdrCodes (C : Ctx) (v : Bool) : Prop where
  of : C.code.lookup fOf = some (ofParams.map (fun p => (p, ShapeHOL.one)), ofBody, .one)
  dn : C.code.lookup fDn = some ([dnA, dnB].map (fun p => (p, ShapeHOL.one)), dnBody, .one)
  rn : C.code.lookup WB.fRN = some (kParams.map (fun p => (p, ShapeHOL.one)), rdBody C, .one)
  d : C.code.lookup fD = some (dParams.map (fun p => (p, ShapeHOL.one)), dE C, .one)
  ld : C.code.lookup fLds = some (ldParams.map (fun p => (p, ShapeHOL.one)), ldBody, .one)
  self : C.code.lookup fLdr = some (ldrParams.map (fun p => (p, ShapeHOL.one)), ldrBody v C, .one)

section
variable {σ : Type}

def lrsW (C : Ctx) (H : List (BitVec 64)) : LazyResA → BitVec 64 → Prop
  | .verdict v, w => w = boolW v
  | .unknown a b, w => ∃ o, w = cellA C o ∧ H[o]? = some (Enc.idxW a) ∧ H[o + 1]? = some (Enc.idxW b)

def PostLR (C : Ctx) (r : LazyResA) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ lrsW C H' r w ∧ SR (ctxH C H') s' st

theorem postLR_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostLR C a w s' st → PostLR C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', h1, h2, h3⟩ => ⟨H', h1, h2, sr_of_eq h3 rfl rfl rfl rfl⟩

/-- A cell of the heap image is a heap address, at least `2^32`: never `0`, `1` or `2`. -/
theorem cellA_big {C : Ctx} (hok : CtxOK C) {H : List (BitVec 64)} {s : AState} {t : PState σ}
    (hsr : SR (ctxH C H) s t) {o : Nat} (ho : o < H.length) :
    ¬ cellA C o = 0 ∧ ¬ cellA C o = 1 ∧ ¬ cellA C o = 2 := by
  obtain ⟨H0, hp0, ha0⟩ := hsr.heap
  have h1 := ha0.len
  have h2 := hp0.length_le
  have hlay := hok.heapLay
  have hhi := hok.heapHigh
  have e1 : (ctxH C H).HN = C.HN := rfl
  have e2 : (ctxH C H).H = H := rfl
  rw [e1] at h1; rw [e2] at h2
  have hlen : H.length ≤ C.HN := by omega
  refine ⟨?_, ?_, ?_⟩ <;> intro e <;> have := congrArg BitVec.toNat e <;>
    simp [cellA, BitVec.toNat_add] at this <;> omega

theorem ldr_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) (hok : CtxOK C) (v : Bool) (hv : C.side = v) (hc : LdrCodes C v)
    (Q : AState → Prop) (d : Nat)
    (hQof : ∀ s1 a b r s2, Q s1 → defeqOffset (knot mode C n) d a b s1 = .ok (r, s2) → Q s2)
    (hQdn : ∀ s1 a b r s2, Q s1 → defeqNoFvars a b s1 = .ok (r, s2) → Q s2)
    (hQrn : ∀ s1 e r s2, Q s1 → reduceNat (knot mode C n) C.fe d e s1 = .ok (r, s2) → Q s2)
    (hQd : ∀ s1 a b r s2, Q s1 → (knot mode C n).defeq d a b s1 = .ok (r, s2) → Q s2)
    (hQld : ∀ s1 a b r s2, Q s1 → lazyDeltaStep mode (knot mode C n) C.fe d a b s1 = .ok (r, s2) → Q s2)
    (hOF : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ a b, SpecR (σ := σ) (Pre (ctxH C H) s1 (ofParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d,
      Enc.idxW a, Enc.idxW b])) ofBody s1 (defeqOffset (knot mode C n) d a b) (PostOBH (ctxH C H)))
    (hDN : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ a b, SpecR (σ := σ) (Pre (ctxH C H) s1 ([dnA, dnB].zip [Enc.idxW a, Enc.idxW b])) dnBody s1
      (defeqNoFvars a b) (PostB (ctxH C H)))
    (hRN : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ e, SpecR (σ := σ) (Pre (ctxH C H) s1 (kParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d,
      Enc.idxW e])) (rdBody C) s1 (reduceNat (knot mode C n) C.fe d e) (UD.PostO (ctxH C H)))
    (hD : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ a b, Callee (σ := σ) (ctxH C H) dParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (dE C) s1 ((knot mode C n).defeq d a b)
      (PostB (ctxH C H)))
    (hLD : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ a b, SpecR (σ := σ) (Pre (ctxH C H) s1 (ldParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d,
      Enc.idxW a, Enc.idxW b])) ldBody s1 (lazyDeltaStep mode (knot mode C n) C.fe d a b) (PostDS (ctxH C H))) :
    ∀ F, F < 2 ^ 63 → ∀ (H : List (BitVec 64)) (s : AState) (a b : EIdx), C.H <+: H → Q s →
      SpecR (σ := σ) (Pre (ctxH C H) s (ldrParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, BitVec.ofNat 64 F,
        Enc.idxW a, Enc.idxW b])) (ldrBody v C) s
        (lazyDeltaReduction mode v (knot mode C n) C.fe d F a b) (PostLR (ctxH C H)) := by
  intro F
  induction F with
  | zero =>
    intro _ H s a b hpH hq
    refine specR_prologue (postLR_locals _) (Knot.params_none _ ldrLocals ldrParams _ (by decide) (by decide)) ?_
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get, ldrParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI)
      (fun h => absurd h (by decide))
  | succ F ih =>
    intro hF H s a b hpH hq
    refine specR_prologue (postLR_locals _) (Knot.params_none _ ldrLocals ldrParams _ (by decide) (by decide)) ?_
    have hne := ofNat_succ_ne F (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ldrParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h)
      (fun _ => ?_)
    rw [lazyDeltaReduction]
    refine specR_callNIH (C := ctxH C H) lrO fOf ofParams [(vv kFu), (vv kD), (vv lrA), (vv lrB)] ofBody
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (by decide) rfl (by decide) hc.of
      ⟨by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], trivial⟩
      (fun r_ w s' st => defeqOffset (knot mode C n) d a b s = .ok (r_, s') ∧ PostOBH (ctxH C H) r_ w s' st) (fun r_ w s' H' => w = LLeq.obW r_ ∧ defeqOffset (knot mode C n) d a b s = .ok (r_, s'))
      (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu ofParams _ rfl hlk) (hOF H s hpH hq a b)))
      (fun ro w1 s1 H1 hp1 ⟨hw1, hrun1⟩ => ?_)
    have hq1 := hQof s a b ro s1 hq hrun1
    have hpa1 : C.H <+: H1 := hpH.trans hp1
    have hb1 : H <+: H1 := (List.prefix_refl _).trans hp1
    subst hw1
    rcases ro with _ | vo
    · refine specR_ifI _ 0 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      try dsimp only
      unfold lazyFoldOk
      refine specR_iteSide hok.eoNe (fun hs => ?_) (fun hs => ?_)
      rotate_left
      · have hv' : v = false := by rw [← hv]; exact hs
        subst hv'
        simp only [Bool.false_eq_true, ↓reduceIte]
        refine specR_callNIH (C := ctxH C H1) lrN fDn [dnA, dnB] [(vv lrA), (vv lrB)] dnBody
          [Enc.idxW a, Enc.idxW b] (by decide) rfl (by decide) hc.dn
          ⟨by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], trivial⟩
          (fun r_ w s' st => defeqNoFvars a b s1 = .ok (r_, s') ∧ PostB (ctxH C H1) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ defeqNoFvars a b s1 = .ok (r_, s'))
          (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
          (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [dnA, dnB] _ rfl hlk) (hDN H1 s1 hpa1 hq1 a b)))
          (fun nf w2 s2 H2 hp2 ⟨hw2, hrun2⟩ => ?_)
        have hq2 := hQdn s1 a b nf s2 hq1 hrun2
        have hpa2 : C.H <+: H2 := hpa1.trans hp2
        have hb2 : H <+: H2 := hb1.trans hp2
        subst hw2
        cases nf
        · refine specR_ifI _ 0 (by simp [boolW]) (fun h => absurd rfl h) (fun _ => ?_)
          simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
          refine specR_callNIH (C := ctxH C H2) lrS fLds ldParams [(vv kFu), (vv kD), (vv lrA), (vv lrB)] ldBody
            [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (by decide) rfl (by decide) hc.ld
            ⟨by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], trivial⟩
            (fun r_ w s' st => lazyDeltaStep mode (knot mode C n) C.fe d a b s2 = .ok (r_, s') ∧ PostDS (ctxH C H2) r_ w s' st) (fun r_ w s' H' => dsW C H' r_ w ∧ lazyDeltaStep mode (knot mode C n) C.fe d a b s2 = .ok (r_, s'))
            (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
            (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu ldParams _ rfl hlk) (hLD H2 s2 hpa2 hq2 a b)))
            (fun dr w3 s3 H3 hp3 ⟨hw3, hrun3⟩ => ?_)
          have hq3 := hQld s2 a b dr s3 hq2 hrun3
          have hpa3 : C.H <+: H3 := hpa2.trans hp3
          have hb3 : H <+: H3 := hb2.trans hp3
          rcases dr with ⟨a', b'⟩ | _ | _ | _
          · obtain ⟨o, rfl, hoa, hob⟩ := hw3
            refine specR_atEntry fun t ht => ?_
            have hbig := cellA_big hok ht.sr (List.getElem?_eq_some_iff.mp hoa).1
            refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hbig.1) (fun h => absurd rfl h) (fun _ => ?_)
            refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hbig.2.1) (fun h => absurd rfl h) (fun _ => ?_)
            refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hbig.2.2) (fun h => absurd rfl h) (fun _ => ?_)
            try dsimp only
            refine UD.specR_heapLoadI' (C := ctxH C H3) lrA2 (vv lrS) o (Enc.idxW a') hoa (by decide) (by simp <;> rfl) ?_
            refine UD.specR_heapLoadI' (C := ctxH C H3) lrB2 (.op .add [vv lrS, .const 8]) (o + 1) (Enc.idxW b') hob (by decide)
              (by simp [sev]; exact cellA_add8 C o) ?_
            refine specR_congr (m' := lazyDeltaReduction mode false (knot mode C n) C.fe d F a' b' >>= fun r => pure r) (by simp) ?_
            refine specR_callNIH (C := ctxH C H3) lrR fLdr ldrParams [vv kFu, vv kD, .op .sub [vv lrF, .const 1], vv lrA2, vv lrB2] (ldrBody false C)
              [BitVec.ofNat 64 n, BitVec.ofNat 64 d, BitVec.ofNat 64 F, Enc.idxW a', Enc.idxW b'] (by decide) rfl (by decide) hc.self
              ⟨by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [sev, Env.get, ldrParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, by simp, by simp, trivial⟩
              (PostLR (ctxH C H3)) (fun r_ w _ H' => lrsW C H' r_ w) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
              (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ldrParams _ rfl hlk) (ih (by omega) H3 s3 a' b' hpa3 hq3))
              (fun rr wr sr' Hr hpr hwr => ?_)
            exact specR_returnI _ wr (by simp) (fun t ht => ⟨Hr, hb3.trans hpr, hwr, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

          · simp only [dsW] at hw3; subst hw3
            refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
            refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
            try dsimp only
            exact specR_returnI _ 1 rfl (fun t ht => ⟨H3, hb3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
          · simp only [dsW] at hw3; subst hw3
            refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
            refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
            refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
            try dsimp only
            exact specR_returnI _ 0 rfl (fun t ht => ⟨H3, hb3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
          · simp only [dsW] at hw3; subst hw3
            refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
            try dsimp only
            refine specR_alloc2I (C := ctxH C H3) (ctxOK_H hok H3) lrW (vv lrA) (vv lrB) (Enc.idxW a) (Enc.idxW b) (by decide)
              (fun _ => by simp +decide [Env.get, ldrParams, ctxEnv]) (fun _ => by simp +decide [Env.get, ldrParams, ctxEnv])
              (fun H2 ws hp2 hws => ?_)
            refine specR_returnI (vv lrW) (cellA C H2.length) (by simp +decide <;> rfl) (fun t ht => ?_)
            have hp2' : H3 <+: H2 := hp2
            exact ⟨_, hb3.trans (hp2'.trans (img2_prefix H2 ws _ _ hws)), ⟨H2.length, rfl, (img2_get H2 ws _ _ hws).1, (img2_get H2 ws _ _ hws).2⟩,
              sr_of_eq ht.sr rfl rfl rfl rfl⟩


        refine specR_ifI _ 1 (by simp [boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
        simp only [↓reduceIte]
        refine specR_callNIH (C := ctxH C H2) lrX WB.fRN kParams [(vv kFu), (vv kD), (vv lrA)] (rdBody C)
          [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a] (by decide) rfl (by decide) hc.rn
          ⟨by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], trivial⟩
          (fun r_ w s' st => reduceNat (knot mode C n) C.fe d a s2 = .ok (r_, s') ∧ UD.PostO (ctxH C H2) r_ w s' st) (fun r_ w s' H' => w = optW r_ ∧ reduceNat (knot mode C n) C.fe d a s2 = .ok (r_, s'))
          (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
          (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu kParams _ rfl hlk) (hRN H2 s2 hpa2 hq2 a)))
          (fun ra w4 s4 H4 hp4 ⟨hw4, hrun4⟩ => ?_)
        have hq4 := hQrn s2 a ra s4 hq2 hrun4
        have hpa4 : C.H <+: H4 := hpa2.trans hp4
        have hb4 : H <+: H4 := hb2.trans hp4
        subst hw4
        rcases ra with _ | a2
        · refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
          try dsimp only
          refine specR_callNIH (C := ctxH C H4) lrY WB.fRN kParams [(vv kFu), (vv kD), (vv lrB)] (rdBody C)
            [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW b] (by decide) rfl (by decide) hc.rn
            ⟨by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], trivial⟩
            (fun r_ w s' st => reduceNat (knot mode C n) C.fe d b s4 = .ok (r_, s') ∧ UD.PostO (ctxH C H4) r_ w s' st) (fun r_ w s' H' => w = optW r_ ∧ reduceNat (knot mode C n) C.fe d b s4 = .ok (r_, s'))
            (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
            (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu kParams _ rfl hlk) (hRN H4 s4 hpa4 hq4 b)))
            (fun rb w5 s5 H5 hp5 ⟨hw5, hrun5⟩ => ?_)
          have hq5 := hQrn s4 b rb s5 hq4 hrun5
          have hpa5 : C.H <+: H5 := hpa4.trans hp5
          have hb5 : H <+: H5 := hb4.trans hp5
          subst hw5
          rcases rb with _ | b2
          · refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
            try dsimp only
            refine specR_callNIH (C := ctxH C H5) lrS fLds ldParams [(vv kFu), (vv kD), (vv lrA), (vv lrB)] ldBody
              [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (by decide) rfl (by decide) hc.ld
              ⟨by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], trivial⟩
              (fun r_ w s' st => lazyDeltaStep mode (knot mode C n) C.fe d a b s5 = .ok (r_, s') ∧ PostDS (ctxH C H5) r_ w s' st) (fun r_ w s' H' => dsW C H' r_ w ∧ lazyDeltaStep mode (knot mode C n) C.fe d a b s5 = .ok (r_, s'))
              (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
              (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu ldParams _ rfl hlk) (hLD H5 s5 hpa5 hq5 a b)))
              (fun dr w6 s6 H6 hp6 ⟨hw6, hrun6⟩ => ?_)
            have hq6 := hQld s5 a b dr s6 hq5 hrun6
            have hpa6 : C.H <+: H6 := hpa5.trans hp6
            have hb6 : H <+: H6 := hb5.trans hp6
            rcases dr with ⟨a', b'⟩ | _ | _ | _
            · obtain ⟨o, rfl, hoa, hob⟩ := hw6
              refine specR_atEntry fun t ht => ?_
              have hbig := cellA_big hok ht.sr (List.getElem?_eq_some_iff.mp hoa).1
              refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hbig.1) (fun h => absurd rfl h) (fun _ => ?_)
              refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hbig.2.1) (fun h => absurd rfl h) (fun _ => ?_)
              refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hbig.2.2) (fun h => absurd rfl h) (fun _ => ?_)
              try dsimp only
              refine UD.specR_heapLoadI' (C := ctxH C H6) lrA2 (vv lrS) o (Enc.idxW a') hoa (by decide) (by simp <;> rfl) ?_
              refine UD.specR_heapLoadI' (C := ctxH C H6) lrB2 (.op .add [vv lrS, .const 8]) (o + 1) (Enc.idxW b') hob (by decide)
                (by simp [sev]; exact cellA_add8 C o) ?_
              refine specR_congr (m' := lazyDeltaReduction mode false (knot mode C n) C.fe d F a' b' >>= fun r => pure r) (by simp) ?_
              refine specR_callNIH (C := ctxH C H6) lrR fLdr ldrParams [vv kFu, vv kD, .op .sub [vv lrF, .const 1], vv lrA2, vv lrB2] (ldrBody false C)
                [BitVec.ofNat 64 n, BitVec.ofNat 64 d, BitVec.ofNat 64 F, Enc.idxW a', Enc.idxW b'] (by decide) rfl (by decide) hc.self
                ⟨by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [sev, Env.get, ldrParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, by simp, by simp, trivial⟩
                (PostLR (ctxH C H6)) (fun r_ w _ H' => lrsW C H' r_ w) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
                (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ldrParams _ rfl hlk) (ih (by omega) H6 s6 a' b' hpa6 hq6))
                (fun rr wr sr' Hr hpr hwr => ?_)
              exact specR_returnI _ wr (by simp) (fun t ht => ⟨Hr, hb6.trans hpr, hwr, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

            · simp only [dsW] at hw6; subst hw6
              refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
              refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
              try dsimp only
              exact specR_returnI _ 1 rfl (fun t ht => ⟨H6, hb6, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
            · simp only [dsW] at hw6; subst hw6
              refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
              refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
              refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
              try dsimp only
              exact specR_returnI _ 0 rfl (fun t ht => ⟨H6, hb6, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
            · simp only [dsW] at hw6; subst hw6
              refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
              try dsimp only
              refine specR_alloc2I (C := ctxH C H6) (ctxOK_H hok H6) lrW (vv lrA) (vv lrB) (Enc.idxW a) (Enc.idxW b) (by decide)
                (fun _ => by simp +decide [Env.get, ldrParams, ctxEnv]) (fun _ => by simp +decide [Env.get, ldrParams, ctxEnv])
                (fun H2 ws hp2 hws => ?_)
              refine specR_returnI (vv lrW) (cellA C H2.length) (by simp +decide <;> rfl) (fun t ht => ?_)
              have hp2' : H6 <+: H2 := hp2
              exact ⟨_, hb6.trans (hp2'.trans (img2_prefix H2 ws _ _ hws)), ⟨H2.length, rfl, (img2_get H2 ws _ _ hws).1, (img2_get H2 ws _ _ hws).2⟩,
                sr_of_eq ht.sr rfl rfl rfl rfl⟩


          refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne b2) (fun _ => ?_) (fun h => absurd h (by decide))
          try dsimp only
          refine specR_callNIH (C := ctxH C H5) lrV fD dParams [vv kFu, vv kD, vv lrA, .op .sub [vv lrY, .const 1]] (dE C)
            [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b2] (by decide) rfl (by decide) hc.d
            ⟨by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [sev, Env.get, ldrParams, ctxEnv, optWG]; exact BitVec.add_sub_cancel _ _, trivial⟩
            (fun r_ w s' st => (knot mode C n).defeq d a b2 s5 = .ok (r_, s') ∧ PostB (ctxH C H5) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ (knot mode C n).defeq d a b2 s5 = .ok (r_, s'))
            (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
            (fun u hu _ hlk => specR_run (hD H5 s5 hpa5 hq5 a b2 u hu (fun i hi _ => hlk i (by omega))))
            (fun vv_ w7 s7 H7 hp7 ⟨hw7, hrun7⟩ => ?_)
          have hq7 := hQd s5 a b2 vv_ s7 hq5 hrun7
          have hpa7 : C.H <+: H7 := hpa5.trans hp7
          have hb7 : H <+: H7 := hb5.trans hp7
          subst hw7
          exact specR_returnI _ (boolW vv_) (by simp) (fun t ht => ⟨H7, hb7, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

        refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne a2) (fun _ => ?_) (fun h => absurd h (by decide))
        try dsimp only
        refine specR_callNIH (C := ctxH C H4) lrV fD dParams [vv kFu, vv kD, .op .sub [vv lrX, .const 1], vv lrB] (dE C)
          [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a2, Enc.idxW b] (by decide) rfl (by decide) hc.d
          ⟨by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [sev, Env.get, ldrParams, ctxEnv, optWG]; exact BitVec.add_sub_cancel _ _, by simp +decide [Env.get, ldrParams, ctxEnv], trivial⟩
          (fun r_ w s' st => (knot mode C n).defeq d a2 b s4 = .ok (r_, s') ∧ PostB (ctxH C H4) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ (knot mode C n).defeq d a2 b s4 = .ok (r_, s'))
          (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
          (fun u hu _ hlk => specR_run (hD H4 s4 hpa4 hq4 a2 b u hu (fun i hi _ => hlk i (by omega))))
          (fun vv_ w8 s8 H8 hp8 ⟨hw8, hrun8⟩ => ?_)
        have hq8 := hQd s4 a2 b vv_ s8 hq4 hrun8
        have hpa8 : C.H <+: H8 := hpa4.trans hp8
        have hb8 : H <+: H8 := hb4.trans hp8
        subst hw8
        exact specR_returnI _ (boolW vv_) (by simp) (fun t ht => ⟨H8, hb8, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

      have hv' : v = true := by rw [← hv]; exact hs
      subst hv'
      simp only [↓reduceIte, pure_bind]
      refine specR_assignI lrN (.const 1) 1 (by decide) rfl ?_
      refine specR_ifI _ 1 (by simp) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_callNIH (C := ctxH C H1) lrX WB.fRN kParams [(vv kFu), (vv kD), (vv lrA)] (rdBody C)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a] (by decide) rfl (by decide) hc.rn
        ⟨by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], trivial⟩
        (fun r_ w s' st => reduceNat (knot mode C n) C.fe d a s1 = .ok (r_, s') ∧ UD.PostO (ctxH C H1) r_ w s' st) (fun r_ w s' H' => w = optW r_ ∧ reduceNat (knot mode C n) C.fe d a s1 = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu kParams _ rfl hlk) (hRN H1 s1 hpa1 hq1 a)))
        (fun ra w9 s9 H9 hp9 ⟨hw9, hrun9⟩ => ?_)
      have hq9 := hQrn s1 a ra s9 hq1 hrun9
      have hpa9 : C.H <+: H9 := hpa1.trans hp9
      have hb9 : H <+: H9 := hb1.trans hp9
      subst hw9
      rcases ra with _ | a2
      · refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
        try dsimp only
        refine specR_callNIH (C := ctxH C H9) lrY WB.fRN kParams [(vv kFu), (vv kD), (vv lrB)] (rdBody C)
          [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW b] (by decide) rfl (by decide) hc.rn
          ⟨by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], trivial⟩
          (fun r_ w s' st => reduceNat (knot mode C n) C.fe d b s9 = .ok (r_, s') ∧ UD.PostO (ctxH C H9) r_ w s' st) (fun r_ w s' H' => w = optW r_ ∧ reduceNat (knot mode C n) C.fe d b s9 = .ok (r_, s'))
          (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
          (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu kParams _ rfl hlk) (hRN H9 s9 hpa9 hq9 b)))
          (fun rb w10 s10 H10 hp10 ⟨hw10, hrun10⟩ => ?_)
        have hq10 := hQrn s9 b rb s10 hq9 hrun10
        have hpa10 : C.H <+: H10 := hpa9.trans hp10
        have hb10 : H <+: H10 := hb9.trans hp10
        subst hw10
        rcases rb with _ | b2
        · refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
          try dsimp only
          refine specR_callNIH (C := ctxH C H10) lrS fLds ldParams [(vv kFu), (vv kD), (vv lrA), (vv lrB)] ldBody
            [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (by decide) rfl (by decide) hc.ld
            ⟨by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], trivial⟩
            (fun r_ w s' st => lazyDeltaStep mode (knot mode C n) C.fe d a b s10 = .ok (r_, s') ∧ PostDS (ctxH C H10) r_ w s' st) (fun r_ w s' H' => dsW C H' r_ w ∧ lazyDeltaStep mode (knot mode C n) C.fe d a b s10 = .ok (r_, s'))
            (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
            (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu ldParams _ rfl hlk) (hLD H10 s10 hpa10 hq10 a b)))
            (fun dr w11 s11 H11 hp11 ⟨hw11, hrun11⟩ => ?_)
          have hq11 := hQld s10 a b dr s11 hq10 hrun11
          have hpa11 : C.H <+: H11 := hpa10.trans hp11
          have hb11 : H <+: H11 := hb10.trans hp11
          rcases dr with ⟨a', b'⟩ | _ | _ | _
          · obtain ⟨o, rfl, hoa, hob⟩ := hw11
            refine specR_atEntry fun t ht => ?_
            have hbig := cellA_big hok ht.sr (List.getElem?_eq_some_iff.mp hoa).1
            refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hbig.1) (fun h => absurd rfl h) (fun _ => ?_)
            refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hbig.2.1) (fun h => absurd rfl h) (fun _ => ?_)
            refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hbig.2.2) (fun h => absurd rfl h) (fun _ => ?_)
            try dsimp only
            refine UD.specR_heapLoadI' (C := ctxH C H11) lrA2 (vv lrS) o (Enc.idxW a') hoa (by decide) (by simp <;> rfl) ?_
            refine UD.specR_heapLoadI' (C := ctxH C H11) lrB2 (.op .add [vv lrS, .const 8]) (o + 1) (Enc.idxW b') hob (by decide)
              (by simp [sev]; exact cellA_add8 C o) ?_
            refine specR_congr (m' := lazyDeltaReduction mode true (knot mode C n) C.fe d F a' b' >>= fun r => pure r) (by simp) ?_
            refine specR_callNIH (C := ctxH C H11) lrR fLdr ldrParams [vv kFu, vv kD, .op .sub [vv lrF, .const 1], vv lrA2, vv lrB2] (ldrBody true C)
              [BitVec.ofNat 64 n, BitVec.ofNat 64 d, BitVec.ofNat 64 F, Enc.idxW a', Enc.idxW b'] (by decide) rfl (by decide) hc.self
              ⟨by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [sev, Env.get, ldrParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, by simp, by simp, trivial⟩
              (PostLR (ctxH C H11)) (fun r_ w _ H' => lrsW C H' r_ w) (fun r_ w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
              (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ldrParams _ rfl hlk) (ih (by omega) H11 s11 a' b' hpa11 hq11))
              (fun rr wr sr' Hr hpr hwr => ?_)
            exact specR_returnI _ wr (by simp) (fun t ht => ⟨Hr, hb11.trans hpr, hwr, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

          · simp only [dsW] at hw11; subst hw11
            refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
            refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
            try dsimp only
            exact specR_returnI _ 1 rfl (fun t ht => ⟨H11, hb11, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
          · simp only [dsW] at hw11; subst hw11
            refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
            refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
            refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
            try dsimp only
            exact specR_returnI _ 0 rfl (fun t ht => ⟨H11, hb11, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
          · simp only [dsW] at hw11; subst hw11
            refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
            try dsimp only
            refine specR_alloc2I (C := ctxH C H11) (ctxOK_H hok H11) lrW (vv lrA) (vv lrB) (Enc.idxW a) (Enc.idxW b) (by decide)
              (fun _ => by simp +decide [Env.get, ldrParams, ctxEnv]) (fun _ => by simp +decide [Env.get, ldrParams, ctxEnv])
              (fun H2 ws hp2 hws => ?_)
            refine specR_returnI (vv lrW) (cellA C H2.length) (by simp +decide <;> rfl) (fun t ht => ?_)
            have hp2' : H11 <+: H2 := hp2
            exact ⟨_, hb11.trans (hp2'.trans (img2_prefix H2 ws _ _ hws)), ⟨H2.length, rfl, (img2_get H2 ws _ _ hws).1, (img2_get H2 ws _ _ hws).2⟩,
              sr_of_eq ht.sr rfl rfl rfl rfl⟩


        refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne b2) (fun _ => ?_) (fun h => absurd h (by decide))
        try dsimp only
        refine specR_callNIH (C := ctxH C H10) lrV fD dParams [vv kFu, vv kD, vv lrA, .op .sub [vv lrY, .const 1]] (dE C)
          [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b2] (by decide) rfl (by decide) hc.d
          ⟨by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [sev, Env.get, ldrParams, ctxEnv, optWG]; exact BitVec.add_sub_cancel _ _, trivial⟩
          (fun r_ w s' st => (knot mode C n).defeq d a b2 s10 = .ok (r_, s') ∧ PostB (ctxH C H10) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ (knot mode C n).defeq d a b2 s10 = .ok (r_, s'))
          (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
          (fun u hu _ hlk => specR_run (hD H10 s10 hpa10 hq10 a b2 u hu (fun i hi _ => hlk i (by omega))))
          (fun vv_ w12 s12 H12 hp12 ⟨hw12, hrun12⟩ => ?_)
        have hq12 := hQd s10 a b2 vv_ s12 hq10 hrun12
        have hpa12 : C.H <+: H12 := hpa10.trans hp12
        have hb12 : H <+: H12 := hb10.trans hp12
        subst hw12
        exact specR_returnI _ (boolW vv_) (by simp) (fun t ht => ⟨H12, hb12, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

      refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne a2) (fun _ => ?_) (fun h => absurd h (by decide))
      try dsimp only
      refine specR_callNIH (C := ctxH C H9) lrV fD dParams [vv kFu, vv kD, .op .sub [vv lrX, .const 1], vv lrB] (dE C)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a2, Enc.idxW b] (by decide) rfl (by decide) hc.d
        ⟨by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [Env.get, ldrParams, ctxEnv], by simp +decide [sev, Env.get, ldrParams, ctxEnv, optWG]; exact BitVec.add_sub_cancel _ _, by simp +decide [Env.get, ldrParams, ctxEnv], trivial⟩
        (fun r_ w s' st => (knot mode C n).defeq d a2 b s9 = .ok (r_, s') ∧ PostB (ctxH C H9) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ (knot mode C n).defeq d a2 b s9 = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (hD H9 s9 hpa9 hq9 a2 b u hu (fun i hi _ => hlk i (by omega))))
        (fun vv_ w13 s13 H13 hp13 ⟨hw13, hrun13⟩ => ?_)
      have hq13 := hQd s9 a2 b vv_ s13 hq9 hrun13
      have hpa13 : C.H <+: H13 := hpa9.trans hp13
      have hb13 : H <+: H13 := hb9.trans hp13
      subst hw13
      exact specR_returnI _ (boolW vv_) (by simp) (fun t ht => ⟨H13, hb13, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    have hne : LLeq.obW (some vo) ≠ 0 := by cases vo <;> decide
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ (boolW vo) (by simp [sev]; exact obW_sub1 vo) (fun t ht => ⟨H1, hb1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
