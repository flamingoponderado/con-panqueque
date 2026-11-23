import ConPanqueque.T.Core.FormerLoop
import ConPanqueque.T.Core.FormerNZ
import ConPanqueque.T.Core.ConstVal
import ConPanqueque.T.LsView
import ConPanqueque.T.SRFacts
import ConPanqueque.T.PinRead
import ConPanqueque.T.Comp.TwinFacts
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `familyNeverZeroAt`: is a family's sort never zero at the use's levels

The stored `neverZero` bit first; otherwise `formerNeverZeroAt`: a stored type ending in a sort is read off
(`formerNeverZero`); any other is instantiated at the use's levels (`instLPFast`, its level parameters copied
from the environment to a fresh block) and walked by `formerSortLoop`; no sort answers `false`.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc
open ConPanqueque.T.ILP (fInstLPF ilpfBody ilpf_spec CodesILP ilpParams ilpBody PostILP)
open ConPanqueque.T.CV (prefix_fillI blk_of_fillI mul8_eq)
open ConRon.Bridge

def fzN := ofString "fzn"
def fzT := ofString "fzt"
def fzR := ofString "fzr"
def fzX := ofString "fzx"
def fzP := ofString "fzp"
def fzL := ofString "fzl"
def fzB := ofString "fzb"
def fzY := ofString "fzy"
def fzA := ofString "fza"
def fzI := ofString "fzi"
def fzS := ofString "fzs"
def fzZ := ofString "fzz"

@[simp] theorem fz_fzN_ne_fzT : fzN ≠ fzT := by decide
@[simp] theorem fz_fzN_ne_fzR : fzN ≠ fzR := by decide
@[simp] theorem fz_fzN_ne_fzX : fzN ≠ fzX := by decide
@[simp] theorem fz_fzN_ne_fzP : fzN ≠ fzP := by decide
@[simp] theorem fz_fzN_ne_fzL : fzN ≠ fzL := by decide
@[simp] theorem fz_fzN_ne_fzB : fzN ≠ fzB := by decide
@[simp] theorem fz_fzN_ne_fzY : fzN ≠ fzY := by decide
@[simp] theorem fz_fzN_ne_fzA : fzN ≠ fzA := by decide
@[simp] theorem fz_fzN_ne_fzI : fzN ≠ fzI := by decide
@[simp] theorem fz_fzN_ne_fzS : fzN ≠ fzS := by decide
@[simp] theorem fz_fzN_ne_fzZ : fzN ≠ fzZ := by decide
@[simp] theorem fz_fzN_ne_kFu : fzN ≠ kFu := by decide
@[simp] theorem fz_fzN_ne_kD : fzN ≠ kD := by decide
@[simp] theorem fz_fzN_ne_fzQ : fzN ≠ fzQ := by decide
@[simp] theorem fz_fzN_ne_fzU : fzN ≠ fzU := by decide
@[simp] theorem fz_fzN_ne_lCn : fzN ≠ lCn := by decide
@[simp] theorem fz_fzN_ne_lSrc : fzN ≠ lSrc := by decide
@[simp] theorem fz_fzN_ne_lDst : fzN ≠ lDst := by decide
@[simp] theorem fz_fzN_ne_lCi : fzN ≠ lCi := by decide
@[simp] theorem fz_fzN_ne_lCz : fzN ≠ lCz := by decide
@[simp] theorem fz_fzN_ne_lKb : fzN ≠ lKb := by decide
@[simp] theorem fz_fzT_ne_fzN : fzT ≠ fzN := by decide
@[simp] theorem fz_fzT_ne_fzR : fzT ≠ fzR := by decide
@[simp] theorem fz_fzT_ne_fzX : fzT ≠ fzX := by decide
@[simp] theorem fz_fzT_ne_fzP : fzT ≠ fzP := by decide
@[simp] theorem fz_fzT_ne_fzL : fzT ≠ fzL := by decide
@[simp] theorem fz_fzT_ne_fzB : fzT ≠ fzB := by decide
@[simp] theorem fz_fzT_ne_fzY : fzT ≠ fzY := by decide
@[simp] theorem fz_fzT_ne_fzA : fzT ≠ fzA := by decide
@[simp] theorem fz_fzT_ne_fzI : fzT ≠ fzI := by decide
@[simp] theorem fz_fzT_ne_fzS : fzT ≠ fzS := by decide
@[simp] theorem fz_fzT_ne_fzZ : fzT ≠ fzZ := by decide
@[simp] theorem fz_fzT_ne_kFu : fzT ≠ kFu := by decide
@[simp] theorem fz_fzT_ne_kD : fzT ≠ kD := by decide
@[simp] theorem fz_fzT_ne_fzQ : fzT ≠ fzQ := by decide
@[simp] theorem fz_fzT_ne_fzU : fzT ≠ fzU := by decide
@[simp] theorem fz_fzT_ne_lCn : fzT ≠ lCn := by decide
@[simp] theorem fz_fzT_ne_lSrc : fzT ≠ lSrc := by decide
@[simp] theorem fz_fzT_ne_lDst : fzT ≠ lDst := by decide
@[simp] theorem fz_fzT_ne_lCi : fzT ≠ lCi := by decide
@[simp] theorem fz_fzT_ne_lCz : fzT ≠ lCz := by decide
@[simp] theorem fz_fzT_ne_lKb : fzT ≠ lKb := by decide
@[simp] theorem fz_fzR_ne_fzN : fzR ≠ fzN := by decide
@[simp] theorem fz_fzR_ne_fzT : fzR ≠ fzT := by decide
@[simp] theorem fz_fzR_ne_fzX : fzR ≠ fzX := by decide
@[simp] theorem fz_fzR_ne_fzP : fzR ≠ fzP := by decide
@[simp] theorem fz_fzR_ne_fzL : fzR ≠ fzL := by decide
@[simp] theorem fz_fzR_ne_fzB : fzR ≠ fzB := by decide
@[simp] theorem fz_fzR_ne_fzY : fzR ≠ fzY := by decide
@[simp] theorem fz_fzR_ne_fzA : fzR ≠ fzA := by decide
@[simp] theorem fz_fzR_ne_fzI : fzR ≠ fzI := by decide
@[simp] theorem fz_fzR_ne_fzS : fzR ≠ fzS := by decide
@[simp] theorem fz_fzR_ne_fzZ : fzR ≠ fzZ := by decide
@[simp] theorem fz_fzR_ne_kFu : fzR ≠ kFu := by decide
@[simp] theorem fz_fzR_ne_kD : fzR ≠ kD := by decide
@[simp] theorem fz_fzR_ne_fzQ : fzR ≠ fzQ := by decide
@[simp] theorem fz_fzR_ne_fzU : fzR ≠ fzU := by decide
@[simp] theorem fz_fzR_ne_lCn : fzR ≠ lCn := by decide
@[simp] theorem fz_fzR_ne_lSrc : fzR ≠ lSrc := by decide
@[simp] theorem fz_fzR_ne_lDst : fzR ≠ lDst := by decide
@[simp] theorem fz_fzR_ne_lCi : fzR ≠ lCi := by decide
@[simp] theorem fz_fzR_ne_lCz : fzR ≠ lCz := by decide
@[simp] theorem fz_fzR_ne_lKb : fzR ≠ lKb := by decide
@[simp] theorem fz_fzX_ne_fzN : fzX ≠ fzN := by decide
@[simp] theorem fz_fzX_ne_fzT : fzX ≠ fzT := by decide
@[simp] theorem fz_fzX_ne_fzR : fzX ≠ fzR := by decide
@[simp] theorem fz_fzX_ne_fzP : fzX ≠ fzP := by decide
@[simp] theorem fz_fzX_ne_fzL : fzX ≠ fzL := by decide
@[simp] theorem fz_fzX_ne_fzB : fzX ≠ fzB := by decide
@[simp] theorem fz_fzX_ne_fzY : fzX ≠ fzY := by decide
@[simp] theorem fz_fzX_ne_fzA : fzX ≠ fzA := by decide
@[simp] theorem fz_fzX_ne_fzI : fzX ≠ fzI := by decide
@[simp] theorem fz_fzX_ne_fzS : fzX ≠ fzS := by decide
@[simp] theorem fz_fzX_ne_fzZ : fzX ≠ fzZ := by decide
@[simp] theorem fz_fzX_ne_kFu : fzX ≠ kFu := by decide
@[simp] theorem fz_fzX_ne_kD : fzX ≠ kD := by decide
@[simp] theorem fz_fzX_ne_fzQ : fzX ≠ fzQ := by decide
@[simp] theorem fz_fzX_ne_fzU : fzX ≠ fzU := by decide
@[simp] theorem fz_fzX_ne_lCn : fzX ≠ lCn := by decide
@[simp] theorem fz_fzX_ne_lSrc : fzX ≠ lSrc := by decide
@[simp] theorem fz_fzX_ne_lDst : fzX ≠ lDst := by decide
@[simp] theorem fz_fzX_ne_lCi : fzX ≠ lCi := by decide
@[simp] theorem fz_fzX_ne_lCz : fzX ≠ lCz := by decide
@[simp] theorem fz_fzX_ne_lKb : fzX ≠ lKb := by decide
@[simp] theorem fz_fzP_ne_fzN : fzP ≠ fzN := by decide
@[simp] theorem fz_fzP_ne_fzT : fzP ≠ fzT := by decide
@[simp] theorem fz_fzP_ne_fzR : fzP ≠ fzR := by decide
@[simp] theorem fz_fzP_ne_fzX : fzP ≠ fzX := by decide
@[simp] theorem fz_fzP_ne_fzL : fzP ≠ fzL := by decide
@[simp] theorem fz_fzP_ne_fzB : fzP ≠ fzB := by decide
@[simp] theorem fz_fzP_ne_fzY : fzP ≠ fzY := by decide
@[simp] theorem fz_fzP_ne_fzA : fzP ≠ fzA := by decide
@[simp] theorem fz_fzP_ne_fzI : fzP ≠ fzI := by decide
@[simp] theorem fz_fzP_ne_fzS : fzP ≠ fzS := by decide
@[simp] theorem fz_fzP_ne_fzZ : fzP ≠ fzZ := by decide
@[simp] theorem fz_fzP_ne_kFu : fzP ≠ kFu := by decide
@[simp] theorem fz_fzP_ne_kD : fzP ≠ kD := by decide
@[simp] theorem fz_fzP_ne_fzQ : fzP ≠ fzQ := by decide
@[simp] theorem fz_fzP_ne_fzU : fzP ≠ fzU := by decide
@[simp] theorem fz_fzP_ne_lCn : fzP ≠ lCn := by decide
@[simp] theorem fz_fzP_ne_lSrc : fzP ≠ lSrc := by decide
@[simp] theorem fz_fzP_ne_lDst : fzP ≠ lDst := by decide
@[simp] theorem fz_fzP_ne_lCi : fzP ≠ lCi := by decide
@[simp] theorem fz_fzP_ne_lCz : fzP ≠ lCz := by decide
@[simp] theorem fz_fzP_ne_lKb : fzP ≠ lKb := by decide
@[simp] theorem fz_fzL_ne_fzN : fzL ≠ fzN := by decide
@[simp] theorem fz_fzL_ne_fzT : fzL ≠ fzT := by decide
@[simp] theorem fz_fzL_ne_fzR : fzL ≠ fzR := by decide
@[simp] theorem fz_fzL_ne_fzX : fzL ≠ fzX := by decide
@[simp] theorem fz_fzL_ne_fzP : fzL ≠ fzP := by decide
@[simp] theorem fz_fzL_ne_fzB : fzL ≠ fzB := by decide
@[simp] theorem fz_fzL_ne_fzY : fzL ≠ fzY := by decide
@[simp] theorem fz_fzL_ne_fzA : fzL ≠ fzA := by decide
@[simp] theorem fz_fzL_ne_fzI : fzL ≠ fzI := by decide
@[simp] theorem fz_fzL_ne_fzS : fzL ≠ fzS := by decide
@[simp] theorem fz_fzL_ne_fzZ : fzL ≠ fzZ := by decide
@[simp] theorem fz_fzL_ne_kFu : fzL ≠ kFu := by decide
@[simp] theorem fz_fzL_ne_kD : fzL ≠ kD := by decide
@[simp] theorem fz_fzL_ne_fzQ : fzL ≠ fzQ := by decide
@[simp] theorem fz_fzL_ne_fzU : fzL ≠ fzU := by decide
@[simp] theorem fz_fzL_ne_lCn : fzL ≠ lCn := by decide
@[simp] theorem fz_fzL_ne_lSrc : fzL ≠ lSrc := by decide
@[simp] theorem fz_fzL_ne_lDst : fzL ≠ lDst := by decide
@[simp] theorem fz_fzL_ne_lCi : fzL ≠ lCi := by decide
@[simp] theorem fz_fzL_ne_lCz : fzL ≠ lCz := by decide
@[simp] theorem fz_fzL_ne_lKb : fzL ≠ lKb := by decide
@[simp] theorem fz_fzB_ne_fzN : fzB ≠ fzN := by decide
@[simp] theorem fz_fzB_ne_fzT : fzB ≠ fzT := by decide
@[simp] theorem fz_fzB_ne_fzR : fzB ≠ fzR := by decide
@[simp] theorem fz_fzB_ne_fzX : fzB ≠ fzX := by decide
@[simp] theorem fz_fzB_ne_fzP : fzB ≠ fzP := by decide
@[simp] theorem fz_fzB_ne_fzL : fzB ≠ fzL := by decide
@[simp] theorem fz_fzB_ne_fzY : fzB ≠ fzY := by decide
@[simp] theorem fz_fzB_ne_fzA : fzB ≠ fzA := by decide
@[simp] theorem fz_fzB_ne_fzI : fzB ≠ fzI := by decide
@[simp] theorem fz_fzB_ne_fzS : fzB ≠ fzS := by decide
@[simp] theorem fz_fzB_ne_fzZ : fzB ≠ fzZ := by decide
@[simp] theorem fz_fzB_ne_kFu : fzB ≠ kFu := by decide
@[simp] theorem fz_fzB_ne_kD : fzB ≠ kD := by decide
@[simp] theorem fz_fzB_ne_fzQ : fzB ≠ fzQ := by decide
@[simp] theorem fz_fzB_ne_fzU : fzB ≠ fzU := by decide
@[simp] theorem fz_fzB_ne_lCn : fzB ≠ lCn := by decide
@[simp] theorem fz_fzB_ne_lSrc : fzB ≠ lSrc := by decide
@[simp] theorem fz_fzB_ne_lDst : fzB ≠ lDst := by decide
@[simp] theorem fz_fzB_ne_lCi : fzB ≠ lCi := by decide
@[simp] theorem fz_fzB_ne_lCz : fzB ≠ lCz := by decide
@[simp] theorem fz_fzB_ne_lKb : fzB ≠ lKb := by decide
@[simp] theorem fz_fzY_ne_fzN : fzY ≠ fzN := by decide
@[simp] theorem fz_fzY_ne_fzT : fzY ≠ fzT := by decide
@[simp] theorem fz_fzY_ne_fzR : fzY ≠ fzR := by decide
@[simp] theorem fz_fzY_ne_fzX : fzY ≠ fzX := by decide
@[simp] theorem fz_fzY_ne_fzP : fzY ≠ fzP := by decide
@[simp] theorem fz_fzY_ne_fzL : fzY ≠ fzL := by decide
@[simp] theorem fz_fzY_ne_fzB : fzY ≠ fzB := by decide
@[simp] theorem fz_fzY_ne_fzA : fzY ≠ fzA := by decide
@[simp] theorem fz_fzY_ne_fzI : fzY ≠ fzI := by decide
@[simp] theorem fz_fzY_ne_fzS : fzY ≠ fzS := by decide
@[simp] theorem fz_fzY_ne_fzZ : fzY ≠ fzZ := by decide
@[simp] theorem fz_fzY_ne_kFu : fzY ≠ kFu := by decide
@[simp] theorem fz_fzY_ne_kD : fzY ≠ kD := by decide
@[simp] theorem fz_fzY_ne_fzQ : fzY ≠ fzQ := by decide
@[simp] theorem fz_fzY_ne_fzU : fzY ≠ fzU := by decide
@[simp] theorem fz_fzY_ne_lCn : fzY ≠ lCn := by decide
@[simp] theorem fz_fzY_ne_lSrc : fzY ≠ lSrc := by decide
@[simp] theorem fz_fzY_ne_lDst : fzY ≠ lDst := by decide
@[simp] theorem fz_fzY_ne_lCi : fzY ≠ lCi := by decide
@[simp] theorem fz_fzY_ne_lCz : fzY ≠ lCz := by decide
@[simp] theorem fz_fzY_ne_lKb : fzY ≠ lKb := by decide
@[simp] theorem fz_fzA_ne_fzN : fzA ≠ fzN := by decide
@[simp] theorem fz_fzA_ne_fzT : fzA ≠ fzT := by decide
@[simp] theorem fz_fzA_ne_fzR : fzA ≠ fzR := by decide
@[simp] theorem fz_fzA_ne_fzX : fzA ≠ fzX := by decide
@[simp] theorem fz_fzA_ne_fzP : fzA ≠ fzP := by decide
@[simp] theorem fz_fzA_ne_fzL : fzA ≠ fzL := by decide
@[simp] theorem fz_fzA_ne_fzB : fzA ≠ fzB := by decide
@[simp] theorem fz_fzA_ne_fzY : fzA ≠ fzY := by decide
@[simp] theorem fz_fzA_ne_fzI : fzA ≠ fzI := by decide
@[simp] theorem fz_fzA_ne_fzS : fzA ≠ fzS := by decide
@[simp] theorem fz_fzA_ne_fzZ : fzA ≠ fzZ := by decide
@[simp] theorem fz_fzA_ne_kFu : fzA ≠ kFu := by decide
@[simp] theorem fz_fzA_ne_kD : fzA ≠ kD := by decide
@[simp] theorem fz_fzA_ne_fzQ : fzA ≠ fzQ := by decide
@[simp] theorem fz_fzA_ne_fzU : fzA ≠ fzU := by decide
@[simp] theorem fz_fzA_ne_lCn : fzA ≠ lCn := by decide
@[simp] theorem fz_fzA_ne_lSrc : fzA ≠ lSrc := by decide
@[simp] theorem fz_fzA_ne_lDst : fzA ≠ lDst := by decide
@[simp] theorem fz_fzA_ne_lCi : fzA ≠ lCi := by decide
@[simp] theorem fz_fzA_ne_lCz : fzA ≠ lCz := by decide
@[simp] theorem fz_fzA_ne_lKb : fzA ≠ lKb := by decide
@[simp] theorem fz_fzI_ne_fzN : fzI ≠ fzN := by decide
@[simp] theorem fz_fzI_ne_fzT : fzI ≠ fzT := by decide
@[simp] theorem fz_fzI_ne_fzR : fzI ≠ fzR := by decide
@[simp] theorem fz_fzI_ne_fzX : fzI ≠ fzX := by decide
@[simp] theorem fz_fzI_ne_fzP : fzI ≠ fzP := by decide
@[simp] theorem fz_fzI_ne_fzL : fzI ≠ fzL := by decide
@[simp] theorem fz_fzI_ne_fzB : fzI ≠ fzB := by decide
@[simp] theorem fz_fzI_ne_fzY : fzI ≠ fzY := by decide
@[simp] theorem fz_fzI_ne_fzA : fzI ≠ fzA := by decide
@[simp] theorem fz_fzI_ne_fzS : fzI ≠ fzS := by decide
@[simp] theorem fz_fzI_ne_fzZ : fzI ≠ fzZ := by decide
@[simp] theorem fz_fzI_ne_kFu : fzI ≠ kFu := by decide
@[simp] theorem fz_fzI_ne_kD : fzI ≠ kD := by decide
@[simp] theorem fz_fzI_ne_fzQ : fzI ≠ fzQ := by decide
@[simp] theorem fz_fzI_ne_fzU : fzI ≠ fzU := by decide
@[simp] theorem fz_fzI_ne_lCn : fzI ≠ lCn := by decide
@[simp] theorem fz_fzI_ne_lSrc : fzI ≠ lSrc := by decide
@[simp] theorem fz_fzI_ne_lDst : fzI ≠ lDst := by decide
@[simp] theorem fz_fzI_ne_lCi : fzI ≠ lCi := by decide
@[simp] theorem fz_fzI_ne_lCz : fzI ≠ lCz := by decide
@[simp] theorem fz_fzI_ne_lKb : fzI ≠ lKb := by decide
@[simp] theorem fz_fzS_ne_fzN : fzS ≠ fzN := by decide
@[simp] theorem fz_fzS_ne_fzT : fzS ≠ fzT := by decide
@[simp] theorem fz_fzS_ne_fzR : fzS ≠ fzR := by decide
@[simp] theorem fz_fzS_ne_fzX : fzS ≠ fzX := by decide
@[simp] theorem fz_fzS_ne_fzP : fzS ≠ fzP := by decide
@[simp] theorem fz_fzS_ne_fzL : fzS ≠ fzL := by decide
@[simp] theorem fz_fzS_ne_fzB : fzS ≠ fzB := by decide
@[simp] theorem fz_fzS_ne_fzY : fzS ≠ fzY := by decide
@[simp] theorem fz_fzS_ne_fzA : fzS ≠ fzA := by decide
@[simp] theorem fz_fzS_ne_fzI : fzS ≠ fzI := by decide
@[simp] theorem fz_fzS_ne_fzZ : fzS ≠ fzZ := by decide
@[simp] theorem fz_fzS_ne_kFu : fzS ≠ kFu := by decide
@[simp] theorem fz_fzS_ne_kD : fzS ≠ kD := by decide
@[simp] theorem fz_fzS_ne_fzQ : fzS ≠ fzQ := by decide
@[simp] theorem fz_fzS_ne_fzU : fzS ≠ fzU := by decide
@[simp] theorem fz_fzS_ne_lCn : fzS ≠ lCn := by decide
@[simp] theorem fz_fzS_ne_lSrc : fzS ≠ lSrc := by decide
@[simp] theorem fz_fzS_ne_lDst : fzS ≠ lDst := by decide
@[simp] theorem fz_fzS_ne_lCi : fzS ≠ lCi := by decide
@[simp] theorem fz_fzS_ne_lCz : fzS ≠ lCz := by decide
@[simp] theorem fz_fzS_ne_lKb : fzS ≠ lKb := by decide
@[simp] theorem fz_fzZ_ne_fzN : fzZ ≠ fzN := by decide
@[simp] theorem fz_fzZ_ne_fzT : fzZ ≠ fzT := by decide
@[simp] theorem fz_fzZ_ne_fzR : fzZ ≠ fzR := by decide
@[simp] theorem fz_fzZ_ne_fzX : fzZ ≠ fzX := by decide
@[simp] theorem fz_fzZ_ne_fzP : fzZ ≠ fzP := by decide
@[simp] theorem fz_fzZ_ne_fzL : fzZ ≠ fzL := by decide
@[simp] theorem fz_fzZ_ne_fzB : fzZ ≠ fzB := by decide
@[simp] theorem fz_fzZ_ne_fzY : fzZ ≠ fzY := by decide
@[simp] theorem fz_fzZ_ne_fzA : fzZ ≠ fzA := by decide
@[simp] theorem fz_fzZ_ne_fzI : fzZ ≠ fzI := by decide
@[simp] theorem fz_fzZ_ne_fzS : fzZ ≠ fzS := by decide
@[simp] theorem fz_fzZ_ne_kFu : fzZ ≠ kFu := by decide
@[simp] theorem fz_fzZ_ne_kD : fzZ ≠ kD := by decide
@[simp] theorem fz_fzZ_ne_fzQ : fzZ ≠ fzQ := by decide
@[simp] theorem fz_fzZ_ne_fzU : fzZ ≠ fzU := by decide
@[simp] theorem fz_fzZ_ne_lCn : fzZ ≠ lCn := by decide
@[simp] theorem fz_fzZ_ne_lSrc : fzZ ≠ lSrc := by decide
@[simp] theorem fz_fzZ_ne_lDst : fzZ ≠ lDst := by decide
@[simp] theorem fz_fzZ_ne_lCi : fzZ ≠ lCi := by decide
@[simp] theorem fz_fzZ_ne_lCz : fzZ ≠ lCz := by decide
@[simp] theorem fz_fzZ_ne_lKb : fzZ ≠ lKb := by decide
@[simp] theorem fz_kFu_ne_fzN : kFu ≠ fzN := by decide
@[simp] theorem fz_kFu_ne_fzT : kFu ≠ fzT := by decide
@[simp] theorem fz_kFu_ne_fzR : kFu ≠ fzR := by decide
@[simp] theorem fz_kFu_ne_fzX : kFu ≠ fzX := by decide
@[simp] theorem fz_kFu_ne_fzP : kFu ≠ fzP := by decide
@[simp] theorem fz_kFu_ne_fzL : kFu ≠ fzL := by decide
@[simp] theorem fz_kFu_ne_fzB : kFu ≠ fzB := by decide
@[simp] theorem fz_kFu_ne_fzY : kFu ≠ fzY := by decide
@[simp] theorem fz_kFu_ne_fzA : kFu ≠ fzA := by decide
@[simp] theorem fz_kFu_ne_fzI : kFu ≠ fzI := by decide
@[simp] theorem fz_kFu_ne_fzS : kFu ≠ fzS := by decide
@[simp] theorem fz_kFu_ne_fzZ : kFu ≠ fzZ := by decide
@[simp] theorem fz_kD_ne_fzN : kD ≠ fzN := by decide
@[simp] theorem fz_kD_ne_fzT : kD ≠ fzT := by decide
@[simp] theorem fz_kD_ne_fzR : kD ≠ fzR := by decide
@[simp] theorem fz_kD_ne_fzX : kD ≠ fzX := by decide
@[simp] theorem fz_kD_ne_fzP : kD ≠ fzP := by decide
@[simp] theorem fz_kD_ne_fzL : kD ≠ fzL := by decide
@[simp] theorem fz_kD_ne_fzB : kD ≠ fzB := by decide
@[simp] theorem fz_kD_ne_fzY : kD ≠ fzY := by decide
@[simp] theorem fz_kD_ne_fzA : kD ≠ fzA := by decide
@[simp] theorem fz_kD_ne_fzI : kD ≠ fzI := by decide
@[simp] theorem fz_kD_ne_fzS : kD ≠ fzS := by decide
@[simp] theorem fz_kD_ne_fzZ : kD ≠ fzZ := by decide
@[simp] theorem fz_fzQ_ne_fzN : fzQ ≠ fzN := by decide
@[simp] theorem fz_fzQ_ne_fzT : fzQ ≠ fzT := by decide
@[simp] theorem fz_fzQ_ne_fzR : fzQ ≠ fzR := by decide
@[simp] theorem fz_fzQ_ne_fzX : fzQ ≠ fzX := by decide
@[simp] theorem fz_fzQ_ne_fzP : fzQ ≠ fzP := by decide
@[simp] theorem fz_fzQ_ne_fzL : fzQ ≠ fzL := by decide
@[simp] theorem fz_fzQ_ne_fzB : fzQ ≠ fzB := by decide
@[simp] theorem fz_fzQ_ne_fzY : fzQ ≠ fzY := by decide
@[simp] theorem fz_fzQ_ne_fzA : fzQ ≠ fzA := by decide
@[simp] theorem fz_fzQ_ne_fzI : fzQ ≠ fzI := by decide
@[simp] theorem fz_fzQ_ne_fzS : fzQ ≠ fzS := by decide
@[simp] theorem fz_fzQ_ne_fzZ : fzQ ≠ fzZ := by decide
@[simp] theorem fz_fzU_ne_fzN : fzU ≠ fzN := by decide
@[simp] theorem fz_fzU_ne_fzT : fzU ≠ fzT := by decide
@[simp] theorem fz_fzU_ne_fzR : fzU ≠ fzR := by decide
@[simp] theorem fz_fzU_ne_fzX : fzU ≠ fzX := by decide
@[simp] theorem fz_fzU_ne_fzP : fzU ≠ fzP := by decide
@[simp] theorem fz_fzU_ne_fzL : fzU ≠ fzL := by decide
@[simp] theorem fz_fzU_ne_fzB : fzU ≠ fzB := by decide
@[simp] theorem fz_fzU_ne_fzY : fzU ≠ fzY := by decide
@[simp] theorem fz_fzU_ne_fzA : fzU ≠ fzA := by decide
@[simp] theorem fz_fzU_ne_fzI : fzU ≠ fzI := by decide
@[simp] theorem fz_fzU_ne_fzS : fzU ≠ fzS := by decide
@[simp] theorem fz_fzU_ne_fzZ : fzU ≠ fzZ := by decide
@[simp] theorem fz_lCn_ne_fzN : lCn ≠ fzN := by decide
@[simp] theorem fz_lCn_ne_fzT : lCn ≠ fzT := by decide
@[simp] theorem fz_lCn_ne_fzR : lCn ≠ fzR := by decide
@[simp] theorem fz_lCn_ne_fzX : lCn ≠ fzX := by decide
@[simp] theorem fz_lCn_ne_fzP : lCn ≠ fzP := by decide
@[simp] theorem fz_lCn_ne_fzL : lCn ≠ fzL := by decide
@[simp] theorem fz_lCn_ne_fzB : lCn ≠ fzB := by decide
@[simp] theorem fz_lCn_ne_fzY : lCn ≠ fzY := by decide
@[simp] theorem fz_lCn_ne_fzA : lCn ≠ fzA := by decide
@[simp] theorem fz_lCn_ne_fzI : lCn ≠ fzI := by decide
@[simp] theorem fz_lCn_ne_fzS : lCn ≠ fzS := by decide
@[simp] theorem fz_lCn_ne_fzZ : lCn ≠ fzZ := by decide
@[simp] theorem fz_lSrc_ne_fzN : lSrc ≠ fzN := by decide
@[simp] theorem fz_lSrc_ne_fzT : lSrc ≠ fzT := by decide
@[simp] theorem fz_lSrc_ne_fzR : lSrc ≠ fzR := by decide
@[simp] theorem fz_lSrc_ne_fzX : lSrc ≠ fzX := by decide
@[simp] theorem fz_lSrc_ne_fzP : lSrc ≠ fzP := by decide
@[simp] theorem fz_lSrc_ne_fzL : lSrc ≠ fzL := by decide
@[simp] theorem fz_lSrc_ne_fzB : lSrc ≠ fzB := by decide
@[simp] theorem fz_lSrc_ne_fzY : lSrc ≠ fzY := by decide
@[simp] theorem fz_lSrc_ne_fzA : lSrc ≠ fzA := by decide
@[simp] theorem fz_lSrc_ne_fzI : lSrc ≠ fzI := by decide
@[simp] theorem fz_lSrc_ne_fzS : lSrc ≠ fzS := by decide
@[simp] theorem fz_lSrc_ne_fzZ : lSrc ≠ fzZ := by decide
@[simp] theorem fz_lDst_ne_fzN : lDst ≠ fzN := by decide
@[simp] theorem fz_lDst_ne_fzT : lDst ≠ fzT := by decide
@[simp] theorem fz_lDst_ne_fzR : lDst ≠ fzR := by decide
@[simp] theorem fz_lDst_ne_fzX : lDst ≠ fzX := by decide
@[simp] theorem fz_lDst_ne_fzP : lDst ≠ fzP := by decide
@[simp] theorem fz_lDst_ne_fzL : lDst ≠ fzL := by decide
@[simp] theorem fz_lDst_ne_fzB : lDst ≠ fzB := by decide
@[simp] theorem fz_lDst_ne_fzY : lDst ≠ fzY := by decide
@[simp] theorem fz_lDst_ne_fzA : lDst ≠ fzA := by decide
@[simp] theorem fz_lDst_ne_fzI : lDst ≠ fzI := by decide
@[simp] theorem fz_lDst_ne_fzS : lDst ≠ fzS := by decide
@[simp] theorem fz_lDst_ne_fzZ : lDst ≠ fzZ := by decide
@[simp] theorem fz_lCi_ne_fzN : lCi ≠ fzN := by decide
@[simp] theorem fz_lCi_ne_fzT : lCi ≠ fzT := by decide
@[simp] theorem fz_lCi_ne_fzR : lCi ≠ fzR := by decide
@[simp] theorem fz_lCi_ne_fzX : lCi ≠ fzX := by decide
@[simp] theorem fz_lCi_ne_fzP : lCi ≠ fzP := by decide
@[simp] theorem fz_lCi_ne_fzL : lCi ≠ fzL := by decide
@[simp] theorem fz_lCi_ne_fzB : lCi ≠ fzB := by decide
@[simp] theorem fz_lCi_ne_fzY : lCi ≠ fzY := by decide
@[simp] theorem fz_lCi_ne_fzA : lCi ≠ fzA := by decide
@[simp] theorem fz_lCi_ne_fzI : lCi ≠ fzI := by decide
@[simp] theorem fz_lCi_ne_fzS : lCi ≠ fzS := by decide
@[simp] theorem fz_lCi_ne_fzZ : lCi ≠ fzZ := by decide
@[simp] theorem fz_lCz_ne_fzN : lCz ≠ fzN := by decide
@[simp] theorem fz_lCz_ne_fzT : lCz ≠ fzT := by decide
@[simp] theorem fz_lCz_ne_fzR : lCz ≠ fzR := by decide
@[simp] theorem fz_lCz_ne_fzX : lCz ≠ fzX := by decide
@[simp] theorem fz_lCz_ne_fzP : lCz ≠ fzP := by decide
@[simp] theorem fz_lCz_ne_fzL : lCz ≠ fzL := by decide
@[simp] theorem fz_lCz_ne_fzB : lCz ≠ fzB := by decide
@[simp] theorem fz_lCz_ne_fzY : lCz ≠ fzY := by decide
@[simp] theorem fz_lCz_ne_fzA : lCz ≠ fzA := by decide
@[simp] theorem fz_lCz_ne_fzI : lCz ≠ fzI := by decide
@[simp] theorem fz_lCz_ne_fzS : lCz ≠ fzS := by decide
@[simp] theorem fz_lCz_ne_fzZ : lCz ≠ fzZ := by decide
@[simp] theorem fz_lKb_ne_fzN : lKb ≠ fzN := by decide
@[simp] theorem fz_lKb_ne_fzT : lKb ≠ fzT := by decide
@[simp] theorem fz_lKb_ne_fzR : lKb ≠ fzR := by decide
@[simp] theorem fz_lKb_ne_fzX : lKb ≠ fzX := by decide
@[simp] theorem fz_lKb_ne_fzP : lKb ≠ fzP := by decide
@[simp] theorem fz_lKb_ne_fzL : lKb ≠ fzL := by decide
@[simp] theorem fz_lKb_ne_fzB : lKb ≠ fzB := by decide
@[simp] theorem fz_lKb_ne_fzY : lKb ≠ fzY := by decide
@[simp] theorem fz_lKb_ne_fzA : lKb ≠ fzA := by decide
@[simp] theorem fz_lKb_ne_fzI : lKb ≠ fzI := by decide
@[simp] theorem fz_lKb_ne_fzS : lKb ≠ fzS := by decide
@[simp] theorem fz_lKb_ne_fzZ : lKb ≠ fzZ := by decide

def fzLocals : List MlS := [fzN, fzT, fzR, fzX, fzP, fzL, fzB, fzY, fzA, fzI, fzS, fzZ, lCn, lSrc, lDst, lCi, lCz]

def fFza := ofString "formerNeverZeroAt"

def fzaCore (C : Ctx) : ProgHOL 64 :=
  (.seq (.assign .local fzT (.load .one (.op .add [vv fzQ, .const 24])))
  (.seq (.call (some (some (.local, fzR), none)) fFs [vv fzT])
  (.ite (.cmp .notEqual (vv fzR) (.const 0))
    (.seq (.call (some (some (.local, fzX), none)) fFnz [vv fzQ, vv fzU]) (.return (vv fzX)))
  (.seq (.assign .local fzP (.load .one (.op .add [vv fzQ, .const 16])))
  (.seq (.assign .local fzL (.load .one (vv fzP)))
  (.seq (.assign .local lCn (.op .add [vv fzL, .const 1]))
  (allocP C fzB (.panop .mul [vv lCn, .const 8])
  (.seq (.assign .local lSrc (vv fzP))
  (.seq (.assign .local lDst (vv fzB))
  (.seq (.assign .local lCi (.const 0))
  (.seq copyLoop
  (.seq (.call (some (some (.local, fzY), none)) fInstLPF
      [.const (BitVec.ofNat 64 coreWalkFuel), vv fzT, vv fzB, vv fzU])
  (.seq (.assign .local fzA (.load .one (.op .add [vv fzQ, .const 48])))
  (.seq (.assign .local fzI (.load .one (.op .add [vv fzQ, .const 56])))
  (.seq (.call (some (some (.local, fzS), none)) fFsl [vv kFu, .const 0, .op .add [vv fzA, vv fzI], vv fzY])
  (.ite (.cmp .equal (vv fzS) (.const 0)) (.return (.const 0))
  (.seq (.call (some (some (.local, fzZ), none)) fNz0 [.op .sub [vv fzS, .const 1]])
    (.return (vv fzZ)))))))))))))))))))

def fzaLocals : List MlS := fzLocals ++ [lDh, lFl, lDt, lDg, lDi, lRp, lRn]

/-- `formerNeverZeroAt`, after checking its level list's view (halting on an invalid handle). -/
def fzaBody (C : Ctx) : ProgHOL 64 :=
  prologue fzaLocals (.seq (.assign .local lDh (vv fzU)) (.seq (.assign .local lFl (vv lFls)) (.seq lsViewP (fzaCore C))))

def fzCore : ProgHOL 64 :=
  .seq (.assign .local fzN (.load .one (.op .add [vv fzQ, .const 72])))
  (.ite (vv fzN) (.return (.const 1))
  (.seq (.call (some (some (.local, fzX), none)) fFza [vv kFu, vv kD, vv fzQ, vv fzU]) (.return (vv fzX))))

def fzBody : ProgHOL 64 := prologue fzLocals fzCore

structure FzCodes (C : Ctx) : Prop where
  fs : C.code.lookup fFs = some ([(fsT, ShapeHOL.one)], fsBody, .one)
  pir : C.code.lookup ExM.fPir = some ([(pFu, .one), (pH, .one)], ExM.pirBody, .one)
  fn : C.code.lookup fFnz = some (fnParams.map (fun p => (p, ShapeHOL.one)), fnBody, .one)
  zs : C.code.lookup fZs = some (zsParams.map (fun p => (p, ShapeHOL.one)), zsBody, .one)
  zp : C.code.lookup fZp = some (zpParams.map (fun p => (p, ShapeHOL.one)), zpBody, .one)
  neq : C.code.lookup NEq.fNeq = some ([(NEq.pNa, .one), (NEq.pNb, .one)], NEq.neqBody, .one)
  nz : C.code.lookup fNz0 = some ([(nzU, ShapeHOL.one)], nzBody, .one)
  ilpf : C.code.lookup fInstLPF = some (ilpParams.map (fun p => (p, ShapeHOL.one)), ilpfBody C, .one)
  ilp : CodesILP C (ilpBody C)
  fq : FqCodes C
  fza : C.code.lookup fFza = some (fzParams.map (fun p => (p, ShapeHOL.one)), fzaBody C, .one)

section
variable {σ : Type}

theorem fz_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ fzLocals → (ctxEnv C ++ fzParams.zip vals).get x = none :=
  Knot.params_none C fzLocals fzParams vals (by decide) (by decide)

theorem fz_ecell72 (C : Ctx) (o : Nat) : ecell C o + 72 = ecell C (o + 9) := by simpa using ecell_add C o 9
theorem fz_ecell48 (C : Ctx) (o : Nat) : ecell C o + 48 = ecell C (o + 6) := by simpa using ecell_add C o 6
theorem fz_ecell56 (C : Ctx) (o : Nat) : ecell C o + 56 = ecell C (o + 7) := by simpa using ecell_add C o 7

theorem fza_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ fzaLocals → (ctxEnv C ++ fzParams.zip vals).get x = none :=
  Knot.params_none C fzaLocals fzParams vals (by decide) (by decide)

theorem fza_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (hc : FzCodes C) (hn : n < 2 ^ 64)
    (hW : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ d e', d < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d e')
      (PostK (ctxH C H)))
    (s : AState) (d : Nat) (cvT : IConstantVal) (caps : IIndCaps) (o : Nat)
    (hci : CIE C.EB C.EH o (.indInfo cvT caps)) (us : LsIdx)
    (hwf : LStoreWF s.store.ls) (hst : StateOK s)
    (ks : List ConLeche.Name) (hks : Frontend.denoteNList s.store.ns cvT.levelParams = some ks)
    (hrn : ReadNCacheOK s.caches.readNC s.store) (hrl : ReadLCacheOK s.caches.readLC s.store)
    (hrls : ReadLsCacheOK s.caches.readLsC s.store) (hden : (denoteE s.store cvT.type).isSome = true)
    (hlen : cvT.levelParams.length + 1 < 2 ^ 60) (hK : caps.nparams + caps.nIdx < 2 ^ 63) :
    SpecR (σ := σ) (Pre C s (fzParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, ecell C o, Enc.idxW us]))
      (fzaBody C) s (formerNeverZeroAt (knot mode C n) cvT caps us) (PostB C) := by
  obtain ⟨hcv, -, -, -, ⟨hnpW, -⟩, ⟨hniW, -⟩, -, -⟩ := hci
  have hcv' : CVE C.EB C.EH (o + 1) cvT := hcv
  obtain ⟨_, ⟨wl, hwl, o', hwl', hblk⟩, hty⟩ := id hcv'
  subst hwl'
  refine specR_prologue (postB_locals C) (fza_none C _) ?_
  refine specR_assignI lDh (vv fzU) (Enc.idxW us) (by decide) (by simp +decide [Env.get, fzParams, ctxEnv]) ?_
  refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [Env.get, fzParams, ctxEnv] <;> rfl) ?_
  refine specR_lsviewPI us (by simp +decide) (by simp +decide <;> rfl)
    (by simp +decide [Env.get, fzParams, ctxEnv] <;> rfl) ⟨by decide, by decide, by decide, by decide, by decide⟩
    (fun v0 P0 hv0 _ _ => ?_)
  refine specR_atEntry fun t0 ht0 => ?_
  obtain ⟨vs, hus⟩ := Option.isSome_iff_exists.mp (denoteLs_total' (sr_lswf ht0.sr) (by rw [hv0]; rfl))
  have hsd : ∀ u, formerResSort cvT.type s = .ok (some u, s) → (denoteL s.store.ls u).isSome = true :=
    fun u hrun => by
      obtain ⟨w0, hw0⟩ := Comp.formerResSort_sort _ _ _ _ hrun
      obtain ⟨l, hl⟩ := sr_sortDen ht0.sr w0 u hw0
      rw [hl]; rfl
  refine specR_dropMem ?_
  unfold fzaCore
  refine specR_envLoadI fzT (.op .add [vv fzQ, .const 24]) (o + 3) _ (by decide)
    (by simp +decide [sev, Env.get, fzParams, ctxEnv]; exact fn_ecell24 C o) (by simpa [Nat.add_assoc] using hty) ?_
  refine specR_congr (m' := formerResSort cvT.type >>= fun r =>
      match r with
      | some _ => formerNeverZero cvT us
      | none => instLPFast coreWalkFuel cvT.levelParams us cvT.type >>= fun ty =>
          formerSortLoop (knot mode C n) 0 (caps.nparams + caps.nIdx) ty >>= fun o =>
          match o with
          | some s => readLevelM s >>= fun l => pure (ConLeche.Level.zeronessOf l).isNever
          | none => pure false)
    (by simp only [formerNeverZeroAt, bind_assoc] <;> rfl) ?_
  refine specR_callNIH fzR fFs [fsT] [vv fzT] fsBody [Enc.idxW cvT.type] (by decide) rfl (by decide) hc.fs
    ⟨by simp +decide [sev, Env.get], trivial⟩
    (fun a w s' st => formerResSort cvT.type s = .ok (a, s') ∧ PostOL C s a w s' st)
    (fun a w s' _ => formerResSort cvT.type s = .ok (a, s') ∧ s' = s ∧ w = optWG Enc.idxW a)
    (fun a w s' st ⟨hrun, h1, h2, H', hp, h3⟩ => ⟨H', hp, ⟨hrun, h1, h2⟩, by subst h1; exact h3⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [fsT] _ rfl hlk) (fs_spec C hc.pir s cvT.type)))
    (fun r w s1 H1 hp1 ⟨hrun, hs1, hw⟩ => ?_)
  subst s1 hw
  rcases r with _ | u
  · refine specR_ifI _ 0 (by simp +decide [sev, Env.get, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    dsimp only
    have hl0 : C.EH[o']? = some (BitVec.ofNat 64 cvT.levelParams.length) := by simpa using hblk.1
    refine specR_envLoadI (C := ctxH C H1) fzP (.op .add [vv fzQ, .const 16]) (o + 2) _ (by decide)
      (by simp +decide [sev, Env.get, fzParams, ctxEnv]; exact fn_ecell16 C o)
      (by simpa [Nat.add_assoc] using hwl : C.EH[o + 2]? = _) ?_
    refine specR_envLoadI (C := ctxH C H1) fzL (vv fzP) o' _ (by decide) (by simp +decide [Env.get]; rfl) hl0 ?_
    refine specR_assignI lCn _ (BitVec.ofNat 64 (cvT.levelParams.length + 1)) (by decide)
      (by simp +decide [sev, Env.get]; exact word_add1_eq _) ?_
    refine specR_allocI (C := ctxH C H1) fzB (.panop .mul [vv lCn, .const 8]) (cvT.levelParams.length + 1)
      (by omega) (by decide) (fun v => by simp +decide [sev, Env.get]; exact mul8_eq _)
      (fun H' wsN hpre hwl2 hcap => ?_)
    refine specR_assignI lSrc (vv fzP) (ecell C o') (by decide) (by simp +decide [sev, Env.get]; rfl) ?_
    refine specR_assignI lDst (vv fzB) (cellA C H'.length) (by decide) (by simp +decide [sev, Env.get]; rfl) ?_
    refine specR_assignI lCi (.const 0) 0 (by decide) rfl ?_
    have hws : (BitVec.ofNat 64 cvT.levelParams.length :: cvT.levelParams.map Enc.idxW).length =
        cvT.levelParams.length + 1 := by simp
    refine specR_copyEI (C := C) hok (H' ++ wsN) (BitVec.ofNat 64 cvT.levelParams.length :: cvT.levelParams.map Enc.idxW)
      o' H'.length (by decide) (fun j hj => ?_) (by simp [hwl2]) (by rw [hws]; omega)
      (by rw [hws]; simp +decide [Env.get]) (by decide) (by simp +decide [Env.get, fzParams, ctxEnv]) ?_
    · rcases j with _ | j
      · simpa using hl0
      · have := hblk.2 j (by simp at hj ⊢; omega)
        simp only [List.getElem_cons_succ]
        rw [show o' + (j + 1) = o' + 1 + j by omega]; simpa using this
    have hblk2 := blk_of_fillI (H' ++ wsN) (BitVec.ofNat 64 cvT.levelParams.length :: cvT.levelParams.map Enc.idxW)
      H'.length (cvT.levelParams.map Enc.idxW) (by simp) (by simp [hwl2])
    have hPF0 : C.H <+: fillI (H' ++ wsN) (BitVec.ofNat 64 cvT.levelParams.length :: cvT.levelParams.map Enc.idxW)
        H'.length (BitVec.ofNat 64 cvT.levelParams.length :: cvT.levelParams.map Enc.idxW).length :=
      prefix_fillI _ _ _ C.H ((hp1.trans hpre).length_le) ((hp1.trans hpre).trans (List.prefix_append _ _)) _
    refine specR_callNIH fzY fInstLPF ilpParams [.const (BitVec.ofNat 64 coreWalkFuel), vv fzT, vv fzB, vv fzU]
      (ilpfBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW cvT.type, cellA C H'.length, Enc.idxW us] (by decide) rfl
      (by decide) hc.ilpf
      ⟨rfl, by simp +decide [sev, Env.get], by simp +decide [sev, Env.get]; rfl,
        by simp +decide [sev, Env.get, fzParams, ctxEnv], trivial⟩
      (fun a w s' st => instLPFast coreWalkFuel cvT.levelParams us cvT.type s = .ok (a, s') ∧
        PostILP (ctxH C _) a w s' st)
      (fun a w s' _ => instLPFast coreWalkFuel cvT.levelParams us cvT.type s = .ok (a, s') ∧ w = Enc.idxW a)
      (fun a w s' st ⟨hrun, H'', hp, hw, hsr⟩ => ⟨H'', hp, ⟨hrun, hw⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu ilpParams _ rfl hlk)
        (ilpf_spec ra C hok hc.ilp coreWalkFuel CV.coreWalkFuel_lt H'.length cvT.levelParams ks us vs _ s cvT.type
          hks hus hst hrn hrl hrls hden hblk2)))
      (fun ty w s2 H2 hp2 ⟨hrun2, hw⟩ => ?_)
    subst hw
    have hPF : C.H <+: H2 := hPF0.trans hp2
    refine specR_envLoadI (C := ctxH C H2) fzA (.op .add [vv fzQ, .const 48]) (o + 6) _ (by decide)
      (by simp +decide [sev, Env.get, fzParams, ctxEnv]; exact fz_ecell48 C o) hnpW ?_
    refine specR_envLoadI (C := ctxH C H2) fzI (.op .add [vv fzQ, .const 56]) (o + 7) _ (by decide)
      (by simp +decide [sev, Env.get, fzParams, ctxEnv]; exact fz_ecell56 C o) hniW ?_
    refine specR_callNIH (C := ctxH C H2) fzS fFsl fqParams [vv kFu, .const 0, .op .add [vv fzA, vv fzI], vv fzY]
      fqBody [BitVec.ofNat 64 n, BitVec.ofNat 64 0, BitVec.ofNat 64 (caps.nparams + caps.nIdx), Enc.idxW ty]
      (by decide) rfl (by decide) hc.fq.self
      ⟨by simp +decide [Env.get, fzParams, ctxEnv], rfl,
        by simp +decide [sev, Env.get]; exact BitVec.ofNat_add_ofNat .., by simp +decide [sev, Env.get], trivial⟩
      (fun a w s' st => formerSortLoop (knot mode C n) 0 (caps.nparams + caps.nIdx) ty s2 = .ok (a, s') ∧
        PostOK (ctxH C H2) a w s' st)
      (fun a w s' _ => formerSortLoop (knot mode C n) 0 (caps.nparams + caps.nIdx) ty s2 = .ok (a, s') ∧
        w = optWG Enc.idxW a)
      (fun a w s' st ⟨hrun, H'', hp, hw, hsr⟩ => ⟨H'', hp, ⟨hrun, hw⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu fqParams _ rfl hlk)
        (fq_spec ra mode n C hok hc.fq hW (caps.nparams + caps.nIdx) 0 ty s2 H2 hPF (by omega))))
      (fun r w s3 H3 hp3 ⟨hrun3, hw⟩ => ?_)
    subst hw
    rcases r with _ | u
    · refine specR_ifI _ 1 (by simp +decide [sev, Env.get, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H3, hPF.trans hp3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_atEntry fun t3 ht3 => ?_
      obtain ⟨w3, hw3⟩ := Comp.formerSortLoop_sort _ _ _ _ _ _ _ hrun3
      have hwf3 := sr_lwf ht3.sr
      have hrl3 := ht3.sr.cok.rl
      obtain ⟨l, hl⟩ := sr_sortDen ht3.sr w3 u hw3
      obtain ⟨X, hx, hX⟩ := readLevelM_runC u s3 l hrl3 hl
      refine LLeq.specR_ofRun (R' := PostB C) (am_run_bind hx rfl) ?_
        (fun w st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, LLeq.sr_congrS hsr rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl
          (cachesOK_readLC hsr.cok X hX)⟩)
      have hne : ¬ Enc.idxW u + 1 = 0 := lidxW_add_one_ne u
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
        (fun h => absurd rfl h) (fun _ => ?_)
      rw [isNever_zeronessOf]
      refine specR_bindPure ?_
      refine specR_callNIH (C := ctxH C H3) fzZ fNz0 [nzU] [.op .sub [vv fzS, .const 1]] nzBody [Enc.idxW u]
        (by decide) rfl (by decide) hc.nz
        ⟨by simp +decide [sev, Env.get, optWG]; exact BitVec.add_sub_cancel _ _, trivial⟩
        (PostBS (ctxH C H3) s3) (fun a w s' _ => s' = s3 ∧ w = boolW a)
        (fun a w s' st ⟨h1, h2, h3⟩ => ⟨H3, List.prefix_refl _, ⟨h1, h2⟩, by subst h1; exact h3⟩)
        (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu [nzU] _ rfl hlk)
          (nz0_spec (ctxH C H3) hc.nz s3 hwf3 l u hl))
        (fun b w s4 H4 hp4 ⟨hs4, hw⟩ => ?_)
      subst hs4 hw
      exact specR_returnI _ (boolW b) (by simp [Env.get])
        (fun t ht => ⟨H4, (hPF.trans hp3).trans hp4, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · have hne : ¬ Enc.idxW u + 1 = 0 := lidxW_add_one_ne u
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_bindPure ?_
    refine specR_callNIH (C := ctxH C H1) fzX fFnz fnParams [vv fzQ, vv fzU] fnBody [ecell C o, Enc.idxW us]
      (by decide) rfl (by decide) hc.fn
      ⟨by simp +decide [sev, Env.get, fzParams, ctxEnv], by simp +decide [sev, Env.get, fzParams, ctxEnv], trivial⟩
      (PostB (ctxH C H1)) (fun a w _ _ => w = boolW a)
      (fun a w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
      (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu fnParams _ rfl hlk)
        (fn_spec (ctxH C H1) hc.fs hc.pir hc.zs hc.zp hc.neq hc.nz s hwf cvT o hcv' ks hks us vs hus hrn hrl hrls hsd
          (by omega)))
      (fun b w s2 H2 hp2 hw => ?_)
    subst hw
    exact specR_returnI _ (boolW b) (by simp [Env.get])
      (fun t ht => ⟨H2, hp1.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem fz_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (hc : FzCodes C) (hn : n < 2 ^ 64)
    (hW : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ d e', d < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d e')
      (PostK (ctxH C H)))
    (s : AState) (d : Nat) (cvT : IConstantVal) (caps : IIndCaps) (o : Nat)
    (hci : CIE C.EB C.EH o (.indInfo cvT caps)) (us : LsIdx)
    (hwf : LStoreWF s.store.ls) (hst : StateOK s)
    (ks : List ConLeche.Name) (hks : Frontend.denoteNList s.store.ns cvT.levelParams = some ks)
    (hrn : ReadNCacheOK s.caches.readNC s.store) (hrl : ReadLCacheOK s.caches.readLC s.store)
    (hrls : ReadLsCacheOK s.caches.readLsC s.store) (hden : (denoteE s.store cvT.type).isSome = true)
    (hlen : cvT.levelParams.length + 1 < 2 ^ 60) (hK : caps.nparams + caps.nIdx < 2 ^ 63) :
    SpecR (σ := σ) (Pre C s (fzParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, ecell C o, Enc.idxW us]))
      fzBody s (familyNeverZeroAt (knot mode C n) cvT caps us) (PostB C) := by
  have hnz : C.EH[o + 9]? = some (boolW caps.neverZero) := hci.2.2.2.2.2.2.2
  refine specR_prologue (postB_locals C) (fz_none C _) ?_
  unfold fzCore
  refine specR_envLoadI fzN (.op .add [vv fzQ, .const 72]) (o + 9) _ (by decide)
    (by simp +decide [sev, Env.get, fzParams, ctxEnv]; exact fz_ecell72 C o) hnz ?_
  unfold familyNeverZeroAt
  by_cases hz : caps.neverZero = true
  · rw [if_pos hz]
    refine specR_ifI _ (boolW caps.neverZero) (by simp +decide [sev, Env.get]) (fun _ => ?_)
      (fun h => absurd h (by simp [boolW, hz]))
    exact specR_returnI _ 1 rfl (fun t ht => ⟨C.H, List.prefix_refl _, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [if_neg hz]
  refine specR_ifI _ (boolW caps.neverZero) (by simp +decide [sev, Env.get])
    (fun h => absurd h (by simp [boolW, hz])) (fun _ => ?_)
  refine specR_bindPure ?_
  refine specR_callNIH fzX fFza fzParams [vv kFu, vv kD, vv fzQ, vv fzU] (fzaBody C)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, ecell C o, Enc.idxW us] (by decide) rfl (by decide) hc.fza
    ⟨by simp +decide [Env.get, fzParams, ctxEnv], by simp +decide [Env.get, fzParams, ctxEnv],
      by simp +decide [Env.get, fzParams, ctxEnv], by simp +decide [Env.get, fzParams, ctxEnv], trivial⟩
    (PostB C) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fzParams _ rfl hlk)
      (fza_spec ra mode n C hok hc hn hW s d cvT caps o hci us hwf hst ks hks hrn hrl hrls hden hlen hK))
    (fun b w s1 H1 hp1 hw => ?_)
  subst hw
  exact specR_returnI _ (boolW b) (by simp) (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
