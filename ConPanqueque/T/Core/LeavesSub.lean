import ConPanqueque.T.Core.Wscoped
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `leavesSubGo`: every reachable free-variable leaf is in the base list, memoized on the node

`wscopedBGo`'s port with the memo keyed by the handle alone, the base leaf list (`AccRep`) in the depth's
slot, and the `fvar` arm's test a lookup of `(idx, ty)` in that list (`leafMem`).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def lzF := ofString "lzf"
def lzBl := ofString "lzbl"
def lzH := ofString "lzh"
def lzM := ofString "lzm"
def lzB := ofString "lzb"
def lzL := ofString "lzl"
def lzT := ofString "lzt"
def lzI := ofString "lzi"
def lzC1 := ofString "lzc1"
def lzC2 := ofString "lzc2"
def lzC3 := ofString "lzc3"
def lzR := ofString "lzr"
def lzM2 := ofString "lzm2"
def lzK1 := ofString "lzk1"
def lzK2 := ofString "lzk2"
def lzK3 := ofString "lzk3"
def lzN := ofString "lzn"
def lzO := ofString "lzo"
def lzQ := ofString "lzq"
def fLz := ofString "leavesSubGo"

@[simp] theorem lz_lbF_ne_lbBl : lzF ≠ lzBl := by decide
@[simp] theorem lz_lbF_ne_lbH : lzF ≠ lzH := by decide
@[simp] theorem lz_lbF_ne_lbM : lzF ≠ lzM := by decide
@[simp] theorem lz_lbF_ne_lbB : lzF ≠ lzB := by decide
@[simp] theorem lz_lbF_ne_lbL : lzF ≠ lzL := by decide
@[simp] theorem lz_lbF_ne_lbT : lzF ≠ lzT := by decide
@[simp] theorem lz_lbF_ne_lbI : lzF ≠ lzI := by decide
@[simp] theorem lz_lbF_ne_lbC1 : lzF ≠ lzC1 := by decide
@[simp] theorem lz_lbF_ne_lbC2 : lzF ≠ lzC2 := by decide
@[simp] theorem lz_lbF_ne_lbC3 : lzF ≠ lzC3 := by decide
@[simp] theorem lz_lbF_ne_lbR : lzF ≠ lzR := by decide
@[simp] theorem lz_lbF_ne_lbM2 : lzF ≠ lzM2 := by decide
@[simp] theorem lz_lbF_ne_lbK1 : lzF ≠ lzK1 := by decide
@[simp] theorem lz_lbF_ne_lbK2 : lzF ≠ lzK2 := by decide
@[simp] theorem lz_lbF_ne_lbK3 : lzF ≠ lzK3 := by decide
@[simp] theorem lz_lbF_ne_lbN : lzF ≠ lzN := by decide
@[simp] theorem lz_lbF_ne_lbO : lzF ≠ lzO := by decide
@[simp] theorem lz_lbF_ne_lbQ : lzF ≠ lzQ := by decide
@[simp] theorem lz_lbF_ne_lKb : lzF ≠ lKb := by decide
@[simp] theorem lz_lbF_ne_lFl : lzF ≠ lFl := by decide
@[simp] theorem lz_lbF_ne_lDh : lzF ≠ lDh := by decide
@[simp] theorem lz_lbF_ne_lDt : lzF ≠ lDt := by decide
@[simp] theorem lz_lbF_ne_lDg : lzF ≠ lDg := by decide
@[simp] theorem lz_lbF_ne_lDi : lzF ≠ lDi := by decide
@[simp] theorem lz_lbF_ne_lDo1 : lzF ≠ lDo1 := by decide
@[simp] theorem lz_lbF_ne_lDo2 : lzF ≠ lDo2 := by decide
@[simp] theorem lz_lbF_ne_lRp : lzF ≠ lRp := by decide
@[simp] theorem lz_lbF_ne_lRn : lzF ≠ lRn := by decide
@[simp] theorem lz_lbF_ne_lFle : lzF ≠ lFle := by decide
@[simp] theorem lz_lbF_ne_lDir : lzF ≠ lDir := by decide
@[simp] theorem lz_lbBl_ne_lbF : lzBl ≠ lzF := by decide
@[simp] theorem lz_lbBl_ne_lbH : lzBl ≠ lzH := by decide
@[simp] theorem lz_lbBl_ne_lbM : lzBl ≠ lzM := by decide
@[simp] theorem lz_lbBl_ne_lbB : lzBl ≠ lzB := by decide
@[simp] theorem lz_lbBl_ne_lbL : lzBl ≠ lzL := by decide
@[simp] theorem lz_lbBl_ne_lbT : lzBl ≠ lzT := by decide
@[simp] theorem lz_lbBl_ne_lbI : lzBl ≠ lzI := by decide
@[simp] theorem lz_lbBl_ne_lbC1 : lzBl ≠ lzC1 := by decide
@[simp] theorem lz_lbBl_ne_lbC2 : lzBl ≠ lzC2 := by decide
@[simp] theorem lz_lbBl_ne_lbC3 : lzBl ≠ lzC3 := by decide
@[simp] theorem lz_lbBl_ne_lbR : lzBl ≠ lzR := by decide
@[simp] theorem lz_lbBl_ne_lbM2 : lzBl ≠ lzM2 := by decide
@[simp] theorem lz_lbBl_ne_lbK1 : lzBl ≠ lzK1 := by decide
@[simp] theorem lz_lbBl_ne_lbK2 : lzBl ≠ lzK2 := by decide
@[simp] theorem lz_lbBl_ne_lbK3 : lzBl ≠ lzK3 := by decide
@[simp] theorem lz_lbBl_ne_lbN : lzBl ≠ lzN := by decide
@[simp] theorem lz_lbBl_ne_lbO : lzBl ≠ lzO := by decide
@[simp] theorem lz_lbBl_ne_lbQ : lzBl ≠ lzQ := by decide
@[simp] theorem lz_lbBl_ne_lKb : lzBl ≠ lKb := by decide
@[simp] theorem lz_lbBl_ne_lFl : lzBl ≠ lFl := by decide
@[simp] theorem lz_lbBl_ne_lDh : lzBl ≠ lDh := by decide
@[simp] theorem lz_lbBl_ne_lDt : lzBl ≠ lDt := by decide
@[simp] theorem lz_lbBl_ne_lDg : lzBl ≠ lDg := by decide
@[simp] theorem lz_lbBl_ne_lDi : lzBl ≠ lDi := by decide
@[simp] theorem lz_lbBl_ne_lDo1 : lzBl ≠ lDo1 := by decide
@[simp] theorem lz_lbBl_ne_lDo2 : lzBl ≠ lDo2 := by decide
@[simp] theorem lz_lbBl_ne_lRp : lzBl ≠ lRp := by decide
@[simp] theorem lz_lbBl_ne_lRn : lzBl ≠ lRn := by decide
@[simp] theorem lz_lbBl_ne_lFle : lzBl ≠ lFle := by decide
@[simp] theorem lz_lbBl_ne_lDir : lzBl ≠ lDir := by decide
@[simp] theorem lz_lbH_ne_lbF : lzH ≠ lzF := by decide
@[simp] theorem lz_lbH_ne_lbBl : lzH ≠ lzBl := by decide
@[simp] theorem lz_lbH_ne_lbM : lzH ≠ lzM := by decide
@[simp] theorem lz_lbH_ne_lbB : lzH ≠ lzB := by decide
@[simp] theorem lz_lbH_ne_lbL : lzH ≠ lzL := by decide
@[simp] theorem lz_lbH_ne_lbT : lzH ≠ lzT := by decide
@[simp] theorem lz_lbH_ne_lbI : lzH ≠ lzI := by decide
@[simp] theorem lz_lbH_ne_lbC1 : lzH ≠ lzC1 := by decide
@[simp] theorem lz_lbH_ne_lbC2 : lzH ≠ lzC2 := by decide
@[simp] theorem lz_lbH_ne_lbC3 : lzH ≠ lzC3 := by decide
@[simp] theorem lz_lbH_ne_lbR : lzH ≠ lzR := by decide
@[simp] theorem lz_lbH_ne_lbM2 : lzH ≠ lzM2 := by decide
@[simp] theorem lz_lbH_ne_lbK1 : lzH ≠ lzK1 := by decide
@[simp] theorem lz_lbH_ne_lbK2 : lzH ≠ lzK2 := by decide
@[simp] theorem lz_lbH_ne_lbK3 : lzH ≠ lzK3 := by decide
@[simp] theorem lz_lbH_ne_lbN : lzH ≠ lzN := by decide
@[simp] theorem lz_lbH_ne_lbO : lzH ≠ lzO := by decide
@[simp] theorem lz_lbH_ne_lbQ : lzH ≠ lzQ := by decide
@[simp] theorem lz_lbH_ne_lKb : lzH ≠ lKb := by decide
@[simp] theorem lz_lbH_ne_lFl : lzH ≠ lFl := by decide
@[simp] theorem lz_lbH_ne_lDh : lzH ≠ lDh := by decide
@[simp] theorem lz_lbH_ne_lDt : lzH ≠ lDt := by decide
@[simp] theorem lz_lbH_ne_lDg : lzH ≠ lDg := by decide
@[simp] theorem lz_lbH_ne_lDi : lzH ≠ lDi := by decide
@[simp] theorem lz_lbH_ne_lDo1 : lzH ≠ lDo1 := by decide
@[simp] theorem lz_lbH_ne_lDo2 : lzH ≠ lDo2 := by decide
@[simp] theorem lz_lbH_ne_lRp : lzH ≠ lRp := by decide
@[simp] theorem lz_lbH_ne_lRn : lzH ≠ lRn := by decide
@[simp] theorem lz_lbH_ne_lFle : lzH ≠ lFle := by decide
@[simp] theorem lz_lbH_ne_lDir : lzH ≠ lDir := by decide
@[simp] theorem lz_lbM_ne_lbF : lzM ≠ lzF := by decide
@[simp] theorem lz_lbM_ne_lbBl : lzM ≠ lzBl := by decide
@[simp] theorem lz_lbM_ne_lbH : lzM ≠ lzH := by decide
@[simp] theorem lz_lbM_ne_lbB : lzM ≠ lzB := by decide
@[simp] theorem lz_lbM_ne_lbL : lzM ≠ lzL := by decide
@[simp] theorem lz_lbM_ne_lbT : lzM ≠ lzT := by decide
@[simp] theorem lz_lbM_ne_lbI : lzM ≠ lzI := by decide
@[simp] theorem lz_lbM_ne_lbC1 : lzM ≠ lzC1 := by decide
@[simp] theorem lz_lbM_ne_lbC2 : lzM ≠ lzC2 := by decide
@[simp] theorem lz_lbM_ne_lbC3 : lzM ≠ lzC3 := by decide
@[simp] theorem lz_lbM_ne_lbR : lzM ≠ lzR := by decide
@[simp] theorem lz_lbM_ne_lbM2 : lzM ≠ lzM2 := by decide
@[simp] theorem lz_lbM_ne_lbK1 : lzM ≠ lzK1 := by decide
@[simp] theorem lz_lbM_ne_lbK2 : lzM ≠ lzK2 := by decide
@[simp] theorem lz_lbM_ne_lbK3 : lzM ≠ lzK3 := by decide
@[simp] theorem lz_lbM_ne_lbN : lzM ≠ lzN := by decide
@[simp] theorem lz_lbM_ne_lbO : lzM ≠ lzO := by decide
@[simp] theorem lz_lbM_ne_lbQ : lzM ≠ lzQ := by decide
@[simp] theorem lz_lbM_ne_lKb : lzM ≠ lKb := by decide
@[simp] theorem lz_lbM_ne_lFl : lzM ≠ lFl := by decide
@[simp] theorem lz_lbM_ne_lDh : lzM ≠ lDh := by decide
@[simp] theorem lz_lbM_ne_lDt : lzM ≠ lDt := by decide
@[simp] theorem lz_lbM_ne_lDg : lzM ≠ lDg := by decide
@[simp] theorem lz_lbM_ne_lDi : lzM ≠ lDi := by decide
@[simp] theorem lz_lbM_ne_lDo1 : lzM ≠ lDo1 := by decide
@[simp] theorem lz_lbM_ne_lDo2 : lzM ≠ lDo2 := by decide
@[simp] theorem lz_lbM_ne_lRp : lzM ≠ lRp := by decide
@[simp] theorem lz_lbM_ne_lRn : lzM ≠ lRn := by decide
@[simp] theorem lz_lbM_ne_lFle : lzM ≠ lFle := by decide
@[simp] theorem lz_lbM_ne_lDir : lzM ≠ lDir := by decide
@[simp] theorem lz_lbB_ne_lbF : lzB ≠ lzF := by decide
@[simp] theorem lz_lbB_ne_lbBl : lzB ≠ lzBl := by decide
@[simp] theorem lz_lbB_ne_lbH : lzB ≠ lzH := by decide
@[simp] theorem lz_lbB_ne_lbM : lzB ≠ lzM := by decide
@[simp] theorem lz_lbB_ne_lbL : lzB ≠ lzL := by decide
@[simp] theorem lz_lbB_ne_lbT : lzB ≠ lzT := by decide
@[simp] theorem lz_lbB_ne_lbI : lzB ≠ lzI := by decide
@[simp] theorem lz_lbB_ne_lbC1 : lzB ≠ lzC1 := by decide
@[simp] theorem lz_lbB_ne_lbC2 : lzB ≠ lzC2 := by decide
@[simp] theorem lz_lbB_ne_lbC3 : lzB ≠ lzC3 := by decide
@[simp] theorem lz_lbB_ne_lbR : lzB ≠ lzR := by decide
@[simp] theorem lz_lbB_ne_lbM2 : lzB ≠ lzM2 := by decide
@[simp] theorem lz_lbB_ne_lbK1 : lzB ≠ lzK1 := by decide
@[simp] theorem lz_lbB_ne_lbK2 : lzB ≠ lzK2 := by decide
@[simp] theorem lz_lbB_ne_lbK3 : lzB ≠ lzK3 := by decide
@[simp] theorem lz_lbB_ne_lbN : lzB ≠ lzN := by decide
@[simp] theorem lz_lbB_ne_lbO : lzB ≠ lzO := by decide
@[simp] theorem lz_lbB_ne_lbQ : lzB ≠ lzQ := by decide
@[simp] theorem lz_lbB_ne_lKb : lzB ≠ lKb := by decide
@[simp] theorem lz_lbB_ne_lFl : lzB ≠ lFl := by decide
@[simp] theorem lz_lbB_ne_lDh : lzB ≠ lDh := by decide
@[simp] theorem lz_lbB_ne_lDt : lzB ≠ lDt := by decide
@[simp] theorem lz_lbB_ne_lDg : lzB ≠ lDg := by decide
@[simp] theorem lz_lbB_ne_lDi : lzB ≠ lDi := by decide
@[simp] theorem lz_lbB_ne_lDo1 : lzB ≠ lDo1 := by decide
@[simp] theorem lz_lbB_ne_lDo2 : lzB ≠ lDo2 := by decide
@[simp] theorem lz_lbB_ne_lRp : lzB ≠ lRp := by decide
@[simp] theorem lz_lbB_ne_lRn : lzB ≠ lRn := by decide
@[simp] theorem lz_lbB_ne_lFle : lzB ≠ lFle := by decide
@[simp] theorem lz_lbB_ne_lDir : lzB ≠ lDir := by decide
@[simp] theorem lz_lbL_ne_lbF : lzL ≠ lzF := by decide
@[simp] theorem lz_lbL_ne_lbBl : lzL ≠ lzBl := by decide
@[simp] theorem lz_lbL_ne_lbH : lzL ≠ lzH := by decide
@[simp] theorem lz_lbL_ne_lbM : lzL ≠ lzM := by decide
@[simp] theorem lz_lbL_ne_lbB : lzL ≠ lzB := by decide
@[simp] theorem lz_lbL_ne_lbT : lzL ≠ lzT := by decide
@[simp] theorem lz_lbL_ne_lbI : lzL ≠ lzI := by decide
@[simp] theorem lz_lbL_ne_lbC1 : lzL ≠ lzC1 := by decide
@[simp] theorem lz_lbL_ne_lbC2 : lzL ≠ lzC2 := by decide
@[simp] theorem lz_lbL_ne_lbC3 : lzL ≠ lzC3 := by decide
@[simp] theorem lz_lbL_ne_lbR : lzL ≠ lzR := by decide
@[simp] theorem lz_lbL_ne_lbM2 : lzL ≠ lzM2 := by decide
@[simp] theorem lz_lbL_ne_lbK1 : lzL ≠ lzK1 := by decide
@[simp] theorem lz_lbL_ne_lbK2 : lzL ≠ lzK2 := by decide
@[simp] theorem lz_lbL_ne_lbK3 : lzL ≠ lzK3 := by decide
@[simp] theorem lz_lbL_ne_lbN : lzL ≠ lzN := by decide
@[simp] theorem lz_lbL_ne_lbO : lzL ≠ lzO := by decide
@[simp] theorem lz_lbL_ne_lbQ : lzL ≠ lzQ := by decide
@[simp] theorem lz_lbL_ne_lKb : lzL ≠ lKb := by decide
@[simp] theorem lz_lbL_ne_lFl : lzL ≠ lFl := by decide
@[simp] theorem lz_lbL_ne_lDh : lzL ≠ lDh := by decide
@[simp] theorem lz_lbL_ne_lDt : lzL ≠ lDt := by decide
@[simp] theorem lz_lbL_ne_lDg : lzL ≠ lDg := by decide
@[simp] theorem lz_lbL_ne_lDi : lzL ≠ lDi := by decide
@[simp] theorem lz_lbL_ne_lDo1 : lzL ≠ lDo1 := by decide
@[simp] theorem lz_lbL_ne_lDo2 : lzL ≠ lDo2 := by decide
@[simp] theorem lz_lbL_ne_lRp : lzL ≠ lRp := by decide
@[simp] theorem lz_lbL_ne_lRn : lzL ≠ lRn := by decide
@[simp] theorem lz_lbL_ne_lFle : lzL ≠ lFle := by decide
@[simp] theorem lz_lbL_ne_lDir : lzL ≠ lDir := by decide
@[simp] theorem lz_lbT_ne_lbF : lzT ≠ lzF := by decide
@[simp] theorem lz_lbT_ne_lbBl : lzT ≠ lzBl := by decide
@[simp] theorem lz_lbT_ne_lbH : lzT ≠ lzH := by decide
@[simp] theorem lz_lbT_ne_lbM : lzT ≠ lzM := by decide
@[simp] theorem lz_lbT_ne_lbB : lzT ≠ lzB := by decide
@[simp] theorem lz_lbT_ne_lbL : lzT ≠ lzL := by decide
@[simp] theorem lz_lbT_ne_lbI : lzT ≠ lzI := by decide
@[simp] theorem lz_lbT_ne_lbC1 : lzT ≠ lzC1 := by decide
@[simp] theorem lz_lbT_ne_lbC2 : lzT ≠ lzC2 := by decide
@[simp] theorem lz_lbT_ne_lbC3 : lzT ≠ lzC3 := by decide
@[simp] theorem lz_lbT_ne_lbR : lzT ≠ lzR := by decide
@[simp] theorem lz_lbT_ne_lbM2 : lzT ≠ lzM2 := by decide
@[simp] theorem lz_lbT_ne_lbK1 : lzT ≠ lzK1 := by decide
@[simp] theorem lz_lbT_ne_lbK2 : lzT ≠ lzK2 := by decide
@[simp] theorem lz_lbT_ne_lbK3 : lzT ≠ lzK3 := by decide
@[simp] theorem lz_lbT_ne_lbN : lzT ≠ lzN := by decide
@[simp] theorem lz_lbT_ne_lbO : lzT ≠ lzO := by decide
@[simp] theorem lz_lbT_ne_lbQ : lzT ≠ lzQ := by decide
@[simp] theorem lz_lbT_ne_lKb : lzT ≠ lKb := by decide
@[simp] theorem lz_lbT_ne_lFl : lzT ≠ lFl := by decide
@[simp] theorem lz_lbT_ne_lDh : lzT ≠ lDh := by decide
@[simp] theorem lz_lbT_ne_lDt : lzT ≠ lDt := by decide
@[simp] theorem lz_lbT_ne_lDg : lzT ≠ lDg := by decide
@[simp] theorem lz_lbT_ne_lDi : lzT ≠ lDi := by decide
@[simp] theorem lz_lbT_ne_lDo1 : lzT ≠ lDo1 := by decide
@[simp] theorem lz_lbT_ne_lDo2 : lzT ≠ lDo2 := by decide
@[simp] theorem lz_lbT_ne_lRp : lzT ≠ lRp := by decide
@[simp] theorem lz_lbT_ne_lRn : lzT ≠ lRn := by decide
@[simp] theorem lz_lbT_ne_lFle : lzT ≠ lFle := by decide
@[simp] theorem lz_lbT_ne_lDir : lzT ≠ lDir := by decide
@[simp] theorem lz_lbI_ne_lbF : lzI ≠ lzF := by decide
@[simp] theorem lz_lbI_ne_lbBl : lzI ≠ lzBl := by decide
@[simp] theorem lz_lbI_ne_lbH : lzI ≠ lzH := by decide
@[simp] theorem lz_lbI_ne_lbM : lzI ≠ lzM := by decide
@[simp] theorem lz_lbI_ne_lbB : lzI ≠ lzB := by decide
@[simp] theorem lz_lbI_ne_lbL : lzI ≠ lzL := by decide
@[simp] theorem lz_lbI_ne_lbT : lzI ≠ lzT := by decide
@[simp] theorem lz_lbI_ne_lbC1 : lzI ≠ lzC1 := by decide
@[simp] theorem lz_lbI_ne_lbC2 : lzI ≠ lzC2 := by decide
@[simp] theorem lz_lbI_ne_lbC3 : lzI ≠ lzC3 := by decide
@[simp] theorem lz_lbI_ne_lbR : lzI ≠ lzR := by decide
@[simp] theorem lz_lbI_ne_lbM2 : lzI ≠ lzM2 := by decide
@[simp] theorem lz_lbI_ne_lbK1 : lzI ≠ lzK1 := by decide
@[simp] theorem lz_lbI_ne_lbK2 : lzI ≠ lzK2 := by decide
@[simp] theorem lz_lbI_ne_lbK3 : lzI ≠ lzK3 := by decide
@[simp] theorem lz_lbI_ne_lbN : lzI ≠ lzN := by decide
@[simp] theorem lz_lbI_ne_lbO : lzI ≠ lzO := by decide
@[simp] theorem lz_lbI_ne_lbQ : lzI ≠ lzQ := by decide
@[simp] theorem lz_lbI_ne_lKb : lzI ≠ lKb := by decide
@[simp] theorem lz_lbI_ne_lFl : lzI ≠ lFl := by decide
@[simp] theorem lz_lbI_ne_lDh : lzI ≠ lDh := by decide
@[simp] theorem lz_lbI_ne_lDt : lzI ≠ lDt := by decide
@[simp] theorem lz_lbI_ne_lDg : lzI ≠ lDg := by decide
@[simp] theorem lz_lbI_ne_lDi : lzI ≠ lDi := by decide
@[simp] theorem lz_lbI_ne_lDo1 : lzI ≠ lDo1 := by decide
@[simp] theorem lz_lbI_ne_lDo2 : lzI ≠ lDo2 := by decide
@[simp] theorem lz_lbI_ne_lRp : lzI ≠ lRp := by decide
@[simp] theorem lz_lbI_ne_lRn : lzI ≠ lRn := by decide
@[simp] theorem lz_lbI_ne_lFle : lzI ≠ lFle := by decide
@[simp] theorem lz_lbI_ne_lDir : lzI ≠ lDir := by decide
@[simp] theorem lz_lbC1_ne_lbF : lzC1 ≠ lzF := by decide
@[simp] theorem lz_lbC1_ne_lbBl : lzC1 ≠ lzBl := by decide
@[simp] theorem lz_lbC1_ne_lbH : lzC1 ≠ lzH := by decide
@[simp] theorem lz_lbC1_ne_lbM : lzC1 ≠ lzM := by decide
@[simp] theorem lz_lbC1_ne_lbB : lzC1 ≠ lzB := by decide
@[simp] theorem lz_lbC1_ne_lbL : lzC1 ≠ lzL := by decide
@[simp] theorem lz_lbC1_ne_lbT : lzC1 ≠ lzT := by decide
@[simp] theorem lz_lbC1_ne_lbI : lzC1 ≠ lzI := by decide
@[simp] theorem lz_lbC1_ne_lbC2 : lzC1 ≠ lzC2 := by decide
@[simp] theorem lz_lbC1_ne_lbC3 : lzC1 ≠ lzC3 := by decide
@[simp] theorem lz_lbC1_ne_lbR : lzC1 ≠ lzR := by decide
@[simp] theorem lz_lbC1_ne_lbM2 : lzC1 ≠ lzM2 := by decide
@[simp] theorem lz_lbC1_ne_lbK1 : lzC1 ≠ lzK1 := by decide
@[simp] theorem lz_lbC1_ne_lbK2 : lzC1 ≠ lzK2 := by decide
@[simp] theorem lz_lbC1_ne_lbK3 : lzC1 ≠ lzK3 := by decide
@[simp] theorem lz_lbC1_ne_lbN : lzC1 ≠ lzN := by decide
@[simp] theorem lz_lbC1_ne_lbO : lzC1 ≠ lzO := by decide
@[simp] theorem lz_lbC1_ne_lbQ : lzC1 ≠ lzQ := by decide
@[simp] theorem lz_lbC1_ne_lKb : lzC1 ≠ lKb := by decide
@[simp] theorem lz_lbC1_ne_lFl : lzC1 ≠ lFl := by decide
@[simp] theorem lz_lbC1_ne_lDh : lzC1 ≠ lDh := by decide
@[simp] theorem lz_lbC1_ne_lDt : lzC1 ≠ lDt := by decide
@[simp] theorem lz_lbC1_ne_lDg : lzC1 ≠ lDg := by decide
@[simp] theorem lz_lbC1_ne_lDi : lzC1 ≠ lDi := by decide
@[simp] theorem lz_lbC1_ne_lDo1 : lzC1 ≠ lDo1 := by decide
@[simp] theorem lz_lbC1_ne_lDo2 : lzC1 ≠ lDo2 := by decide
@[simp] theorem lz_lbC1_ne_lRp : lzC1 ≠ lRp := by decide
@[simp] theorem lz_lbC1_ne_lRn : lzC1 ≠ lRn := by decide
@[simp] theorem lz_lbC1_ne_lFle : lzC1 ≠ lFle := by decide
@[simp] theorem lz_lbC1_ne_lDir : lzC1 ≠ lDir := by decide
@[simp] theorem lz_lbC2_ne_lbF : lzC2 ≠ lzF := by decide
@[simp] theorem lz_lbC2_ne_lbBl : lzC2 ≠ lzBl := by decide
@[simp] theorem lz_lbC2_ne_lbH : lzC2 ≠ lzH := by decide
@[simp] theorem lz_lbC2_ne_lbM : lzC2 ≠ lzM := by decide
@[simp] theorem lz_lbC2_ne_lbB : lzC2 ≠ lzB := by decide
@[simp] theorem lz_lbC2_ne_lbL : lzC2 ≠ lzL := by decide
@[simp] theorem lz_lbC2_ne_lbT : lzC2 ≠ lzT := by decide
@[simp] theorem lz_lbC2_ne_lbI : lzC2 ≠ lzI := by decide
@[simp] theorem lz_lbC2_ne_lbC1 : lzC2 ≠ lzC1 := by decide
@[simp] theorem lz_lbC2_ne_lbC3 : lzC2 ≠ lzC3 := by decide
@[simp] theorem lz_lbC2_ne_lbR : lzC2 ≠ lzR := by decide
@[simp] theorem lz_lbC2_ne_lbM2 : lzC2 ≠ lzM2 := by decide
@[simp] theorem lz_lbC2_ne_lbK1 : lzC2 ≠ lzK1 := by decide
@[simp] theorem lz_lbC2_ne_lbK2 : lzC2 ≠ lzK2 := by decide
@[simp] theorem lz_lbC2_ne_lbK3 : lzC2 ≠ lzK3 := by decide
@[simp] theorem lz_lbC2_ne_lbN : lzC2 ≠ lzN := by decide
@[simp] theorem lz_lbC2_ne_lbO : lzC2 ≠ lzO := by decide
@[simp] theorem lz_lbC2_ne_lbQ : lzC2 ≠ lzQ := by decide
@[simp] theorem lz_lbC2_ne_lKb : lzC2 ≠ lKb := by decide
@[simp] theorem lz_lbC2_ne_lFl : lzC2 ≠ lFl := by decide
@[simp] theorem lz_lbC2_ne_lDh : lzC2 ≠ lDh := by decide
@[simp] theorem lz_lbC2_ne_lDt : lzC2 ≠ lDt := by decide
@[simp] theorem lz_lbC2_ne_lDg : lzC2 ≠ lDg := by decide
@[simp] theorem lz_lbC2_ne_lDi : lzC2 ≠ lDi := by decide
@[simp] theorem lz_lbC2_ne_lDo1 : lzC2 ≠ lDo1 := by decide
@[simp] theorem lz_lbC2_ne_lDo2 : lzC2 ≠ lDo2 := by decide
@[simp] theorem lz_lbC2_ne_lRp : lzC2 ≠ lRp := by decide
@[simp] theorem lz_lbC2_ne_lRn : lzC2 ≠ lRn := by decide
@[simp] theorem lz_lbC2_ne_lFle : lzC2 ≠ lFle := by decide
@[simp] theorem lz_lbC2_ne_lDir : lzC2 ≠ lDir := by decide
@[simp] theorem lz_lbC3_ne_lbF : lzC3 ≠ lzF := by decide
@[simp] theorem lz_lbC3_ne_lbBl : lzC3 ≠ lzBl := by decide
@[simp] theorem lz_lbC3_ne_lbH : lzC3 ≠ lzH := by decide
@[simp] theorem lz_lbC3_ne_lbM : lzC3 ≠ lzM := by decide
@[simp] theorem lz_lbC3_ne_lbB : lzC3 ≠ lzB := by decide
@[simp] theorem lz_lbC3_ne_lbL : lzC3 ≠ lzL := by decide
@[simp] theorem lz_lbC3_ne_lbT : lzC3 ≠ lzT := by decide
@[simp] theorem lz_lbC3_ne_lbI : lzC3 ≠ lzI := by decide
@[simp] theorem lz_lbC3_ne_lbC1 : lzC3 ≠ lzC1 := by decide
@[simp] theorem lz_lbC3_ne_lbC2 : lzC3 ≠ lzC2 := by decide
@[simp] theorem lz_lbC3_ne_lbR : lzC3 ≠ lzR := by decide
@[simp] theorem lz_lbC3_ne_lbM2 : lzC3 ≠ lzM2 := by decide
@[simp] theorem lz_lbC3_ne_lbK1 : lzC3 ≠ lzK1 := by decide
@[simp] theorem lz_lbC3_ne_lbK2 : lzC3 ≠ lzK2 := by decide
@[simp] theorem lz_lbC3_ne_lbK3 : lzC3 ≠ lzK3 := by decide
@[simp] theorem lz_lbC3_ne_lbN : lzC3 ≠ lzN := by decide
@[simp] theorem lz_lbC3_ne_lbO : lzC3 ≠ lzO := by decide
@[simp] theorem lz_lbC3_ne_lbQ : lzC3 ≠ lzQ := by decide
@[simp] theorem lz_lbC3_ne_lKb : lzC3 ≠ lKb := by decide
@[simp] theorem lz_lbC3_ne_lFl : lzC3 ≠ lFl := by decide
@[simp] theorem lz_lbC3_ne_lDh : lzC3 ≠ lDh := by decide
@[simp] theorem lz_lbC3_ne_lDt : lzC3 ≠ lDt := by decide
@[simp] theorem lz_lbC3_ne_lDg : lzC3 ≠ lDg := by decide
@[simp] theorem lz_lbC3_ne_lDi : lzC3 ≠ lDi := by decide
@[simp] theorem lz_lbC3_ne_lDo1 : lzC3 ≠ lDo1 := by decide
@[simp] theorem lz_lbC3_ne_lDo2 : lzC3 ≠ lDo2 := by decide
@[simp] theorem lz_lbC3_ne_lRp : lzC3 ≠ lRp := by decide
@[simp] theorem lz_lbC3_ne_lRn : lzC3 ≠ lRn := by decide
@[simp] theorem lz_lbC3_ne_lFle : lzC3 ≠ lFle := by decide
@[simp] theorem lz_lbC3_ne_lDir : lzC3 ≠ lDir := by decide
@[simp] theorem lz_lbR_ne_lbF : lzR ≠ lzF := by decide
@[simp] theorem lz_lbR_ne_lbBl : lzR ≠ lzBl := by decide
@[simp] theorem lz_lbR_ne_lbH : lzR ≠ lzH := by decide
@[simp] theorem lz_lbR_ne_lbM : lzR ≠ lzM := by decide
@[simp] theorem lz_lbR_ne_lbB : lzR ≠ lzB := by decide
@[simp] theorem lz_lbR_ne_lbL : lzR ≠ lzL := by decide
@[simp] theorem lz_lbR_ne_lbT : lzR ≠ lzT := by decide
@[simp] theorem lz_lbR_ne_lbI : lzR ≠ lzI := by decide
@[simp] theorem lz_lbR_ne_lbC1 : lzR ≠ lzC1 := by decide
@[simp] theorem lz_lbR_ne_lbC2 : lzR ≠ lzC2 := by decide
@[simp] theorem lz_lbR_ne_lbC3 : lzR ≠ lzC3 := by decide
@[simp] theorem lz_lbR_ne_lbM2 : lzR ≠ lzM2 := by decide
@[simp] theorem lz_lbR_ne_lbK1 : lzR ≠ lzK1 := by decide
@[simp] theorem lz_lbR_ne_lbK2 : lzR ≠ lzK2 := by decide
@[simp] theorem lz_lbR_ne_lbK3 : lzR ≠ lzK3 := by decide
@[simp] theorem lz_lbR_ne_lbN : lzR ≠ lzN := by decide
@[simp] theorem lz_lbR_ne_lbO : lzR ≠ lzO := by decide
@[simp] theorem lz_lbR_ne_lbQ : lzR ≠ lzQ := by decide
@[simp] theorem lz_lbR_ne_lKb : lzR ≠ lKb := by decide
@[simp] theorem lz_lbR_ne_lFl : lzR ≠ lFl := by decide
@[simp] theorem lz_lbR_ne_lDh : lzR ≠ lDh := by decide
@[simp] theorem lz_lbR_ne_lDt : lzR ≠ lDt := by decide
@[simp] theorem lz_lbR_ne_lDg : lzR ≠ lDg := by decide
@[simp] theorem lz_lbR_ne_lDi : lzR ≠ lDi := by decide
@[simp] theorem lz_lbR_ne_lDo1 : lzR ≠ lDo1 := by decide
@[simp] theorem lz_lbR_ne_lDo2 : lzR ≠ lDo2 := by decide
@[simp] theorem lz_lbR_ne_lRp : lzR ≠ lRp := by decide
@[simp] theorem lz_lbR_ne_lRn : lzR ≠ lRn := by decide
@[simp] theorem lz_lbR_ne_lFle : lzR ≠ lFle := by decide
@[simp] theorem lz_lbR_ne_lDir : lzR ≠ lDir := by decide
@[simp] theorem lz_lbM2_ne_lbF : lzM2 ≠ lzF := by decide
@[simp] theorem lz_lbM2_ne_lbBl : lzM2 ≠ lzBl := by decide
@[simp] theorem lz_lbM2_ne_lbH : lzM2 ≠ lzH := by decide
@[simp] theorem lz_lbM2_ne_lbM : lzM2 ≠ lzM := by decide
@[simp] theorem lz_lbM2_ne_lbB : lzM2 ≠ lzB := by decide
@[simp] theorem lz_lbM2_ne_lbL : lzM2 ≠ lzL := by decide
@[simp] theorem lz_lbM2_ne_lbT : lzM2 ≠ lzT := by decide
@[simp] theorem lz_lbM2_ne_lbI : lzM2 ≠ lzI := by decide
@[simp] theorem lz_lbM2_ne_lbC1 : lzM2 ≠ lzC1 := by decide
@[simp] theorem lz_lbM2_ne_lbC2 : lzM2 ≠ lzC2 := by decide
@[simp] theorem lz_lbM2_ne_lbC3 : lzM2 ≠ lzC3 := by decide
@[simp] theorem lz_lbM2_ne_lbR : lzM2 ≠ lzR := by decide
@[simp] theorem lz_lbM2_ne_lbK1 : lzM2 ≠ lzK1 := by decide
@[simp] theorem lz_lbM2_ne_lbK2 : lzM2 ≠ lzK2 := by decide
@[simp] theorem lz_lbM2_ne_lbK3 : lzM2 ≠ lzK3 := by decide
@[simp] theorem lz_lbM2_ne_lbN : lzM2 ≠ lzN := by decide
@[simp] theorem lz_lbM2_ne_lbO : lzM2 ≠ lzO := by decide
@[simp] theorem lz_lbM2_ne_lbQ : lzM2 ≠ lzQ := by decide
@[simp] theorem lz_lbM2_ne_lKb : lzM2 ≠ lKb := by decide
@[simp] theorem lz_lbM2_ne_lFl : lzM2 ≠ lFl := by decide
@[simp] theorem lz_lbM2_ne_lDh : lzM2 ≠ lDh := by decide
@[simp] theorem lz_lbM2_ne_lDt : lzM2 ≠ lDt := by decide
@[simp] theorem lz_lbM2_ne_lDg : lzM2 ≠ lDg := by decide
@[simp] theorem lz_lbM2_ne_lDi : lzM2 ≠ lDi := by decide
@[simp] theorem lz_lbM2_ne_lDo1 : lzM2 ≠ lDo1 := by decide
@[simp] theorem lz_lbM2_ne_lDo2 : lzM2 ≠ lDo2 := by decide
@[simp] theorem lz_lbM2_ne_lRp : lzM2 ≠ lRp := by decide
@[simp] theorem lz_lbM2_ne_lRn : lzM2 ≠ lRn := by decide
@[simp] theorem lz_lbM2_ne_lFle : lzM2 ≠ lFle := by decide
@[simp] theorem lz_lbM2_ne_lDir : lzM2 ≠ lDir := by decide
@[simp] theorem lz_lbK1_ne_lbF : lzK1 ≠ lzF := by decide
@[simp] theorem lz_lbK1_ne_lbBl : lzK1 ≠ lzBl := by decide
@[simp] theorem lz_lbK1_ne_lbH : lzK1 ≠ lzH := by decide
@[simp] theorem lz_lbK1_ne_lbM : lzK1 ≠ lzM := by decide
@[simp] theorem lz_lbK1_ne_lbB : lzK1 ≠ lzB := by decide
@[simp] theorem lz_lbK1_ne_lbL : lzK1 ≠ lzL := by decide
@[simp] theorem lz_lbK1_ne_lbT : lzK1 ≠ lzT := by decide
@[simp] theorem lz_lbK1_ne_lbI : lzK1 ≠ lzI := by decide
@[simp] theorem lz_lbK1_ne_lbC1 : lzK1 ≠ lzC1 := by decide
@[simp] theorem lz_lbK1_ne_lbC2 : lzK1 ≠ lzC2 := by decide
@[simp] theorem lz_lbK1_ne_lbC3 : lzK1 ≠ lzC3 := by decide
@[simp] theorem lz_lbK1_ne_lbR : lzK1 ≠ lzR := by decide
@[simp] theorem lz_lbK1_ne_lbM2 : lzK1 ≠ lzM2 := by decide
@[simp] theorem lz_lbK1_ne_lbK2 : lzK1 ≠ lzK2 := by decide
@[simp] theorem lz_lbK1_ne_lbK3 : lzK1 ≠ lzK3 := by decide
@[simp] theorem lz_lbK1_ne_lbN : lzK1 ≠ lzN := by decide
@[simp] theorem lz_lbK1_ne_lbO : lzK1 ≠ lzO := by decide
@[simp] theorem lz_lbK1_ne_lbQ : lzK1 ≠ lzQ := by decide
@[simp] theorem lz_lbK1_ne_lKb : lzK1 ≠ lKb := by decide
@[simp] theorem lz_lbK1_ne_lFl : lzK1 ≠ lFl := by decide
@[simp] theorem lz_lbK1_ne_lDh : lzK1 ≠ lDh := by decide
@[simp] theorem lz_lbK1_ne_lDt : lzK1 ≠ lDt := by decide
@[simp] theorem lz_lbK1_ne_lDg : lzK1 ≠ lDg := by decide
@[simp] theorem lz_lbK1_ne_lDi : lzK1 ≠ lDi := by decide
@[simp] theorem lz_lbK1_ne_lDo1 : lzK1 ≠ lDo1 := by decide
@[simp] theorem lz_lbK1_ne_lDo2 : lzK1 ≠ lDo2 := by decide
@[simp] theorem lz_lbK1_ne_lRp : lzK1 ≠ lRp := by decide
@[simp] theorem lz_lbK1_ne_lRn : lzK1 ≠ lRn := by decide
@[simp] theorem lz_lbK1_ne_lFle : lzK1 ≠ lFle := by decide
@[simp] theorem lz_lbK1_ne_lDir : lzK1 ≠ lDir := by decide
@[simp] theorem lz_lbK2_ne_lbF : lzK2 ≠ lzF := by decide
@[simp] theorem lz_lbK2_ne_lbBl : lzK2 ≠ lzBl := by decide
@[simp] theorem lz_lbK2_ne_lbH : lzK2 ≠ lzH := by decide
@[simp] theorem lz_lbK2_ne_lbM : lzK2 ≠ lzM := by decide
@[simp] theorem lz_lbK2_ne_lbB : lzK2 ≠ lzB := by decide
@[simp] theorem lz_lbK2_ne_lbL : lzK2 ≠ lzL := by decide
@[simp] theorem lz_lbK2_ne_lbT : lzK2 ≠ lzT := by decide
@[simp] theorem lz_lbK2_ne_lbI : lzK2 ≠ lzI := by decide
@[simp] theorem lz_lbK2_ne_lbC1 : lzK2 ≠ lzC1 := by decide
@[simp] theorem lz_lbK2_ne_lbC2 : lzK2 ≠ lzC2 := by decide
@[simp] theorem lz_lbK2_ne_lbC3 : lzK2 ≠ lzC3 := by decide
@[simp] theorem lz_lbK2_ne_lbR : lzK2 ≠ lzR := by decide
@[simp] theorem lz_lbK2_ne_lbM2 : lzK2 ≠ lzM2 := by decide
@[simp] theorem lz_lbK2_ne_lbK1 : lzK2 ≠ lzK1 := by decide
@[simp] theorem lz_lbK2_ne_lbK3 : lzK2 ≠ lzK3 := by decide
@[simp] theorem lz_lbK2_ne_lbN : lzK2 ≠ lzN := by decide
@[simp] theorem lz_lbK2_ne_lbO : lzK2 ≠ lzO := by decide
@[simp] theorem lz_lbK2_ne_lbQ : lzK2 ≠ lzQ := by decide
@[simp] theorem lz_lbK2_ne_lKb : lzK2 ≠ lKb := by decide
@[simp] theorem lz_lbK2_ne_lFl : lzK2 ≠ lFl := by decide
@[simp] theorem lz_lbK2_ne_lDh : lzK2 ≠ lDh := by decide
@[simp] theorem lz_lbK2_ne_lDt : lzK2 ≠ lDt := by decide
@[simp] theorem lz_lbK2_ne_lDg : lzK2 ≠ lDg := by decide
@[simp] theorem lz_lbK2_ne_lDi : lzK2 ≠ lDi := by decide
@[simp] theorem lz_lbK2_ne_lDo1 : lzK2 ≠ lDo1 := by decide
@[simp] theorem lz_lbK2_ne_lDo2 : lzK2 ≠ lDo2 := by decide
@[simp] theorem lz_lbK2_ne_lRp : lzK2 ≠ lRp := by decide
@[simp] theorem lz_lbK2_ne_lRn : lzK2 ≠ lRn := by decide
@[simp] theorem lz_lbK2_ne_lFle : lzK2 ≠ lFle := by decide
@[simp] theorem lz_lbK2_ne_lDir : lzK2 ≠ lDir := by decide
@[simp] theorem lz_lbK3_ne_lbF : lzK3 ≠ lzF := by decide
@[simp] theorem lz_lbK3_ne_lbBl : lzK3 ≠ lzBl := by decide
@[simp] theorem lz_lbK3_ne_lbH : lzK3 ≠ lzH := by decide
@[simp] theorem lz_lbK3_ne_lbM : lzK3 ≠ lzM := by decide
@[simp] theorem lz_lbK3_ne_lbB : lzK3 ≠ lzB := by decide
@[simp] theorem lz_lbK3_ne_lbL : lzK3 ≠ lzL := by decide
@[simp] theorem lz_lbK3_ne_lbT : lzK3 ≠ lzT := by decide
@[simp] theorem lz_lbK3_ne_lbI : lzK3 ≠ lzI := by decide
@[simp] theorem lz_lbK3_ne_lbC1 : lzK3 ≠ lzC1 := by decide
@[simp] theorem lz_lbK3_ne_lbC2 : lzK3 ≠ lzC2 := by decide
@[simp] theorem lz_lbK3_ne_lbC3 : lzK3 ≠ lzC3 := by decide
@[simp] theorem lz_lbK3_ne_lbR : lzK3 ≠ lzR := by decide
@[simp] theorem lz_lbK3_ne_lbM2 : lzK3 ≠ lzM2 := by decide
@[simp] theorem lz_lbK3_ne_lbK1 : lzK3 ≠ lzK1 := by decide
@[simp] theorem lz_lbK3_ne_lbK2 : lzK3 ≠ lzK2 := by decide
@[simp] theorem lz_lbK3_ne_lbN : lzK3 ≠ lzN := by decide
@[simp] theorem lz_lbK3_ne_lbO : lzK3 ≠ lzO := by decide
@[simp] theorem lz_lbK3_ne_lbQ : lzK3 ≠ lzQ := by decide
@[simp] theorem lz_lbK3_ne_lKb : lzK3 ≠ lKb := by decide
@[simp] theorem lz_lbK3_ne_lFl : lzK3 ≠ lFl := by decide
@[simp] theorem lz_lbK3_ne_lDh : lzK3 ≠ lDh := by decide
@[simp] theorem lz_lbK3_ne_lDt : lzK3 ≠ lDt := by decide
@[simp] theorem lz_lbK3_ne_lDg : lzK3 ≠ lDg := by decide
@[simp] theorem lz_lbK3_ne_lDi : lzK3 ≠ lDi := by decide
@[simp] theorem lz_lbK3_ne_lDo1 : lzK3 ≠ lDo1 := by decide
@[simp] theorem lz_lbK3_ne_lDo2 : lzK3 ≠ lDo2 := by decide
@[simp] theorem lz_lbK3_ne_lRp : lzK3 ≠ lRp := by decide
@[simp] theorem lz_lbK3_ne_lRn : lzK3 ≠ lRn := by decide
@[simp] theorem lz_lbK3_ne_lFle : lzK3 ≠ lFle := by decide
@[simp] theorem lz_lbK3_ne_lDir : lzK3 ≠ lDir := by decide
@[simp] theorem lz_lbN_ne_lbF : lzN ≠ lzF := by decide
@[simp] theorem lz_lbN_ne_lbBl : lzN ≠ lzBl := by decide
@[simp] theorem lz_lbN_ne_lbH : lzN ≠ lzH := by decide
@[simp] theorem lz_lbN_ne_lbM : lzN ≠ lzM := by decide
@[simp] theorem lz_lbN_ne_lbB : lzN ≠ lzB := by decide
@[simp] theorem lz_lbN_ne_lbL : lzN ≠ lzL := by decide
@[simp] theorem lz_lbN_ne_lbT : lzN ≠ lzT := by decide
@[simp] theorem lz_lbN_ne_lbI : lzN ≠ lzI := by decide
@[simp] theorem lz_lbN_ne_lbC1 : lzN ≠ lzC1 := by decide
@[simp] theorem lz_lbN_ne_lbC2 : lzN ≠ lzC2 := by decide
@[simp] theorem lz_lbN_ne_lbC3 : lzN ≠ lzC3 := by decide
@[simp] theorem lz_lbN_ne_lbR : lzN ≠ lzR := by decide
@[simp] theorem lz_lbN_ne_lbM2 : lzN ≠ lzM2 := by decide
@[simp] theorem lz_lbN_ne_lbK1 : lzN ≠ lzK1 := by decide
@[simp] theorem lz_lbN_ne_lbK2 : lzN ≠ lzK2 := by decide
@[simp] theorem lz_lbN_ne_lbK3 : lzN ≠ lzK3 := by decide
@[simp] theorem lz_lbN_ne_lbO : lzN ≠ lzO := by decide
@[simp] theorem lz_lbN_ne_lbQ : lzN ≠ lzQ := by decide
@[simp] theorem lz_lbN_ne_lKb : lzN ≠ lKb := by decide
@[simp] theorem lz_lbN_ne_lFl : lzN ≠ lFl := by decide
@[simp] theorem lz_lbN_ne_lDh : lzN ≠ lDh := by decide
@[simp] theorem lz_lbN_ne_lDt : lzN ≠ lDt := by decide
@[simp] theorem lz_lbN_ne_lDg : lzN ≠ lDg := by decide
@[simp] theorem lz_lbN_ne_lDi : lzN ≠ lDi := by decide
@[simp] theorem lz_lbN_ne_lDo1 : lzN ≠ lDo1 := by decide
@[simp] theorem lz_lbN_ne_lDo2 : lzN ≠ lDo2 := by decide
@[simp] theorem lz_lbN_ne_lRp : lzN ≠ lRp := by decide
@[simp] theorem lz_lbN_ne_lRn : lzN ≠ lRn := by decide
@[simp] theorem lz_lbN_ne_lFle : lzN ≠ lFle := by decide
@[simp] theorem lz_lbN_ne_lDir : lzN ≠ lDir := by decide
@[simp] theorem lz_lbO_ne_lbF : lzO ≠ lzF := by decide
@[simp] theorem lz_lbO_ne_lbBl : lzO ≠ lzBl := by decide
@[simp] theorem lz_lbO_ne_lbH : lzO ≠ lzH := by decide
@[simp] theorem lz_lbO_ne_lbM : lzO ≠ lzM := by decide
@[simp] theorem lz_lbO_ne_lbB : lzO ≠ lzB := by decide
@[simp] theorem lz_lbO_ne_lbL : lzO ≠ lzL := by decide
@[simp] theorem lz_lbO_ne_lbT : lzO ≠ lzT := by decide
@[simp] theorem lz_lbO_ne_lbI : lzO ≠ lzI := by decide
@[simp] theorem lz_lbO_ne_lbC1 : lzO ≠ lzC1 := by decide
@[simp] theorem lz_lbO_ne_lbC2 : lzO ≠ lzC2 := by decide
@[simp] theorem lz_lbO_ne_lbC3 : lzO ≠ lzC3 := by decide
@[simp] theorem lz_lbO_ne_lbR : lzO ≠ lzR := by decide
@[simp] theorem lz_lbO_ne_lbM2 : lzO ≠ lzM2 := by decide
@[simp] theorem lz_lbO_ne_lbK1 : lzO ≠ lzK1 := by decide
@[simp] theorem lz_lbO_ne_lbK2 : lzO ≠ lzK2 := by decide
@[simp] theorem lz_lbO_ne_lbK3 : lzO ≠ lzK3 := by decide
@[simp] theorem lz_lbO_ne_lbN : lzO ≠ lzN := by decide
@[simp] theorem lz_lbO_ne_lbQ : lzO ≠ lzQ := by decide
@[simp] theorem lz_lbO_ne_lKb : lzO ≠ lKb := by decide
@[simp] theorem lz_lbO_ne_lFl : lzO ≠ lFl := by decide
@[simp] theorem lz_lbO_ne_lDh : lzO ≠ lDh := by decide
@[simp] theorem lz_lbO_ne_lDt : lzO ≠ lDt := by decide
@[simp] theorem lz_lbO_ne_lDg : lzO ≠ lDg := by decide
@[simp] theorem lz_lbO_ne_lDi : lzO ≠ lDi := by decide
@[simp] theorem lz_lbO_ne_lDo1 : lzO ≠ lDo1 := by decide
@[simp] theorem lz_lbO_ne_lDo2 : lzO ≠ lDo2 := by decide
@[simp] theorem lz_lbO_ne_lRp : lzO ≠ lRp := by decide
@[simp] theorem lz_lbO_ne_lRn : lzO ≠ lRn := by decide
@[simp] theorem lz_lbO_ne_lFle : lzO ≠ lFle := by decide
@[simp] theorem lz_lbO_ne_lDir : lzO ≠ lDir := by decide
@[simp] theorem lz_lbQ_ne_lbF : lzQ ≠ lzF := by decide
@[simp] theorem lz_lbQ_ne_lbBl : lzQ ≠ lzBl := by decide
@[simp] theorem lz_lbQ_ne_lbH : lzQ ≠ lzH := by decide
@[simp] theorem lz_lbQ_ne_lbM : lzQ ≠ lzM := by decide
@[simp] theorem lz_lbQ_ne_lbB : lzQ ≠ lzB := by decide
@[simp] theorem lz_lbQ_ne_lbL : lzQ ≠ lzL := by decide
@[simp] theorem lz_lbQ_ne_lbT : lzQ ≠ lzT := by decide
@[simp] theorem lz_lbQ_ne_lbI : lzQ ≠ lzI := by decide
@[simp] theorem lz_lbQ_ne_lbC1 : lzQ ≠ lzC1 := by decide
@[simp] theorem lz_lbQ_ne_lbC2 : lzQ ≠ lzC2 := by decide
@[simp] theorem lz_lbQ_ne_lbC3 : lzQ ≠ lzC3 := by decide
@[simp] theorem lz_lbQ_ne_lbR : lzQ ≠ lzR := by decide
@[simp] theorem lz_lbQ_ne_lbM2 : lzQ ≠ lzM2 := by decide
@[simp] theorem lz_lbQ_ne_lbK1 : lzQ ≠ lzK1 := by decide
@[simp] theorem lz_lbQ_ne_lbK2 : lzQ ≠ lzK2 := by decide
@[simp] theorem lz_lbQ_ne_lbK3 : lzQ ≠ lzK3 := by decide
@[simp] theorem lz_lbQ_ne_lbN : lzQ ≠ lzN := by decide
@[simp] theorem lz_lbQ_ne_lbO : lzQ ≠ lzO := by decide
@[simp] theorem lz_lbQ_ne_lKb : lzQ ≠ lKb := by decide
@[simp] theorem lz_lbQ_ne_lFl : lzQ ≠ lFl := by decide
@[simp] theorem lz_lbQ_ne_lDh : lzQ ≠ lDh := by decide
@[simp] theorem lz_lbQ_ne_lDt : lzQ ≠ lDt := by decide
@[simp] theorem lz_lbQ_ne_lDg : lzQ ≠ lDg := by decide
@[simp] theorem lz_lbQ_ne_lDi : lzQ ≠ lDi := by decide
@[simp] theorem lz_lbQ_ne_lDo1 : lzQ ≠ lDo1 := by decide
@[simp] theorem lz_lbQ_ne_lDo2 : lzQ ≠ lDo2 := by decide
@[simp] theorem lz_lbQ_ne_lRp : lzQ ≠ lRp := by decide
@[simp] theorem lz_lbQ_ne_lRn : lzQ ≠ lRn := by decide
@[simp] theorem lz_lbQ_ne_lFle : lzQ ≠ lFle := by decide
@[simp] theorem lz_lbQ_ne_lDir : lzQ ≠ lDir := by decide
@[simp] theorem lz_lKb_ne_lbF : lKb ≠ lzF := by decide
@[simp] theorem lz_lKb_ne_lbBl : lKb ≠ lzBl := by decide
@[simp] theorem lz_lKb_ne_lbH : lKb ≠ lzH := by decide
@[simp] theorem lz_lKb_ne_lbM : lKb ≠ lzM := by decide
@[simp] theorem lz_lKb_ne_lbB : lKb ≠ lzB := by decide
@[simp] theorem lz_lKb_ne_lbL : lKb ≠ lzL := by decide
@[simp] theorem lz_lKb_ne_lbT : lKb ≠ lzT := by decide
@[simp] theorem lz_lKb_ne_lbI : lKb ≠ lzI := by decide
@[simp] theorem lz_lKb_ne_lbC1 : lKb ≠ lzC1 := by decide
@[simp] theorem lz_lKb_ne_lbC2 : lKb ≠ lzC2 := by decide
@[simp] theorem lz_lKb_ne_lbC3 : lKb ≠ lzC3 := by decide
@[simp] theorem lz_lKb_ne_lbR : lKb ≠ lzR := by decide
@[simp] theorem lz_lKb_ne_lbM2 : lKb ≠ lzM2 := by decide
@[simp] theorem lz_lKb_ne_lbK1 : lKb ≠ lzK1 := by decide
@[simp] theorem lz_lKb_ne_lbK2 : lKb ≠ lzK2 := by decide
@[simp] theorem lz_lKb_ne_lbK3 : lKb ≠ lzK3 := by decide
@[simp] theorem lz_lKb_ne_lbN : lKb ≠ lzN := by decide
@[simp] theorem lz_lKb_ne_lbO : lKb ≠ lzO := by decide
@[simp] theorem lz_lKb_ne_lbQ : lKb ≠ lzQ := by decide
@[simp] theorem lz_lFl_ne_lbF : lFl ≠ lzF := by decide
@[simp] theorem lz_lFl_ne_lbBl : lFl ≠ lzBl := by decide
@[simp] theorem lz_lFl_ne_lbH : lFl ≠ lzH := by decide
@[simp] theorem lz_lFl_ne_lbM : lFl ≠ lzM := by decide
@[simp] theorem lz_lFl_ne_lbB : lFl ≠ lzB := by decide
@[simp] theorem lz_lFl_ne_lbL : lFl ≠ lzL := by decide
@[simp] theorem lz_lFl_ne_lbT : lFl ≠ lzT := by decide
@[simp] theorem lz_lFl_ne_lbI : lFl ≠ lzI := by decide
@[simp] theorem lz_lFl_ne_lbC1 : lFl ≠ lzC1 := by decide
@[simp] theorem lz_lFl_ne_lbC2 : lFl ≠ lzC2 := by decide
@[simp] theorem lz_lFl_ne_lbC3 : lFl ≠ lzC3 := by decide
@[simp] theorem lz_lFl_ne_lbR : lFl ≠ lzR := by decide
@[simp] theorem lz_lFl_ne_lbM2 : lFl ≠ lzM2 := by decide
@[simp] theorem lz_lFl_ne_lbK1 : lFl ≠ lzK1 := by decide
@[simp] theorem lz_lFl_ne_lbK2 : lFl ≠ lzK2 := by decide
@[simp] theorem lz_lFl_ne_lbK3 : lFl ≠ lzK3 := by decide
@[simp] theorem lz_lFl_ne_lbN : lFl ≠ lzN := by decide
@[simp] theorem lz_lFl_ne_lbO : lFl ≠ lzO := by decide
@[simp] theorem lz_lFl_ne_lbQ : lFl ≠ lzQ := by decide
@[simp] theorem lz_lDh_ne_lbF : lDh ≠ lzF := by decide
@[simp] theorem lz_lDh_ne_lbBl : lDh ≠ lzBl := by decide
@[simp] theorem lz_lDh_ne_lbH : lDh ≠ lzH := by decide
@[simp] theorem lz_lDh_ne_lbM : lDh ≠ lzM := by decide
@[simp] theorem lz_lDh_ne_lbB : lDh ≠ lzB := by decide
@[simp] theorem lz_lDh_ne_lbL : lDh ≠ lzL := by decide
@[simp] theorem lz_lDh_ne_lbT : lDh ≠ lzT := by decide
@[simp] theorem lz_lDh_ne_lbI : lDh ≠ lzI := by decide
@[simp] theorem lz_lDh_ne_lbC1 : lDh ≠ lzC1 := by decide
@[simp] theorem lz_lDh_ne_lbC2 : lDh ≠ lzC2 := by decide
@[simp] theorem lz_lDh_ne_lbC3 : lDh ≠ lzC3 := by decide
@[simp] theorem lz_lDh_ne_lbR : lDh ≠ lzR := by decide
@[simp] theorem lz_lDh_ne_lbM2 : lDh ≠ lzM2 := by decide
@[simp] theorem lz_lDh_ne_lbK1 : lDh ≠ lzK1 := by decide
@[simp] theorem lz_lDh_ne_lbK2 : lDh ≠ lzK2 := by decide
@[simp] theorem lz_lDh_ne_lbK3 : lDh ≠ lzK3 := by decide
@[simp] theorem lz_lDh_ne_lbN : lDh ≠ lzN := by decide
@[simp] theorem lz_lDh_ne_lbO : lDh ≠ lzO := by decide
@[simp] theorem lz_lDh_ne_lbQ : lDh ≠ lzQ := by decide
@[simp] theorem lz_lDt_ne_lbF : lDt ≠ lzF := by decide
@[simp] theorem lz_lDt_ne_lbBl : lDt ≠ lzBl := by decide
@[simp] theorem lz_lDt_ne_lbH : lDt ≠ lzH := by decide
@[simp] theorem lz_lDt_ne_lbM : lDt ≠ lzM := by decide
@[simp] theorem lz_lDt_ne_lbB : lDt ≠ lzB := by decide
@[simp] theorem lz_lDt_ne_lbL : lDt ≠ lzL := by decide
@[simp] theorem lz_lDt_ne_lbT : lDt ≠ lzT := by decide
@[simp] theorem lz_lDt_ne_lbI : lDt ≠ lzI := by decide
@[simp] theorem lz_lDt_ne_lbC1 : lDt ≠ lzC1 := by decide
@[simp] theorem lz_lDt_ne_lbC2 : lDt ≠ lzC2 := by decide
@[simp] theorem lz_lDt_ne_lbC3 : lDt ≠ lzC3 := by decide
@[simp] theorem lz_lDt_ne_lbR : lDt ≠ lzR := by decide
@[simp] theorem lz_lDt_ne_lbM2 : lDt ≠ lzM2 := by decide
@[simp] theorem lz_lDt_ne_lbK1 : lDt ≠ lzK1 := by decide
@[simp] theorem lz_lDt_ne_lbK2 : lDt ≠ lzK2 := by decide
@[simp] theorem lz_lDt_ne_lbK3 : lDt ≠ lzK3 := by decide
@[simp] theorem lz_lDt_ne_lbN : lDt ≠ lzN := by decide
@[simp] theorem lz_lDt_ne_lbO : lDt ≠ lzO := by decide
@[simp] theorem lz_lDt_ne_lbQ : lDt ≠ lzQ := by decide
@[simp] theorem lz_lDg_ne_lbF : lDg ≠ lzF := by decide
@[simp] theorem lz_lDg_ne_lbBl : lDg ≠ lzBl := by decide
@[simp] theorem lz_lDg_ne_lbH : lDg ≠ lzH := by decide
@[simp] theorem lz_lDg_ne_lbM : lDg ≠ lzM := by decide
@[simp] theorem lz_lDg_ne_lbB : lDg ≠ lzB := by decide
@[simp] theorem lz_lDg_ne_lbL : lDg ≠ lzL := by decide
@[simp] theorem lz_lDg_ne_lbT : lDg ≠ lzT := by decide
@[simp] theorem lz_lDg_ne_lbI : lDg ≠ lzI := by decide
@[simp] theorem lz_lDg_ne_lbC1 : lDg ≠ lzC1 := by decide
@[simp] theorem lz_lDg_ne_lbC2 : lDg ≠ lzC2 := by decide
@[simp] theorem lz_lDg_ne_lbC3 : lDg ≠ lzC3 := by decide
@[simp] theorem lz_lDg_ne_lbR : lDg ≠ lzR := by decide
@[simp] theorem lz_lDg_ne_lbM2 : lDg ≠ lzM2 := by decide
@[simp] theorem lz_lDg_ne_lbK1 : lDg ≠ lzK1 := by decide
@[simp] theorem lz_lDg_ne_lbK2 : lDg ≠ lzK2 := by decide
@[simp] theorem lz_lDg_ne_lbK3 : lDg ≠ lzK3 := by decide
@[simp] theorem lz_lDg_ne_lbN : lDg ≠ lzN := by decide
@[simp] theorem lz_lDg_ne_lbO : lDg ≠ lzO := by decide
@[simp] theorem lz_lDg_ne_lbQ : lDg ≠ lzQ := by decide
@[simp] theorem lz_lDi_ne_lbF : lDi ≠ lzF := by decide
@[simp] theorem lz_lDi_ne_lbBl : lDi ≠ lzBl := by decide
@[simp] theorem lz_lDi_ne_lbH : lDi ≠ lzH := by decide
@[simp] theorem lz_lDi_ne_lbM : lDi ≠ lzM := by decide
@[simp] theorem lz_lDi_ne_lbB : lDi ≠ lzB := by decide
@[simp] theorem lz_lDi_ne_lbL : lDi ≠ lzL := by decide
@[simp] theorem lz_lDi_ne_lbT : lDi ≠ lzT := by decide
@[simp] theorem lz_lDi_ne_lbI : lDi ≠ lzI := by decide
@[simp] theorem lz_lDi_ne_lbC1 : lDi ≠ lzC1 := by decide
@[simp] theorem lz_lDi_ne_lbC2 : lDi ≠ lzC2 := by decide
@[simp] theorem lz_lDi_ne_lbC3 : lDi ≠ lzC3 := by decide
@[simp] theorem lz_lDi_ne_lbR : lDi ≠ lzR := by decide
@[simp] theorem lz_lDi_ne_lbM2 : lDi ≠ lzM2 := by decide
@[simp] theorem lz_lDi_ne_lbK1 : lDi ≠ lzK1 := by decide
@[simp] theorem lz_lDi_ne_lbK2 : lDi ≠ lzK2 := by decide
@[simp] theorem lz_lDi_ne_lbK3 : lDi ≠ lzK3 := by decide
@[simp] theorem lz_lDi_ne_lbN : lDi ≠ lzN := by decide
@[simp] theorem lz_lDi_ne_lbO : lDi ≠ lzO := by decide
@[simp] theorem lz_lDi_ne_lbQ : lDi ≠ lzQ := by decide
@[simp] theorem lz_lDo1_ne_lbF : lDo1 ≠ lzF := by decide
@[simp] theorem lz_lDo1_ne_lbBl : lDo1 ≠ lzBl := by decide
@[simp] theorem lz_lDo1_ne_lbH : lDo1 ≠ lzH := by decide
@[simp] theorem lz_lDo1_ne_lbM : lDo1 ≠ lzM := by decide
@[simp] theorem lz_lDo1_ne_lbB : lDo1 ≠ lzB := by decide
@[simp] theorem lz_lDo1_ne_lbL : lDo1 ≠ lzL := by decide
@[simp] theorem lz_lDo1_ne_lbT : lDo1 ≠ lzT := by decide
@[simp] theorem lz_lDo1_ne_lbI : lDo1 ≠ lzI := by decide
@[simp] theorem lz_lDo1_ne_lbC1 : lDo1 ≠ lzC1 := by decide
@[simp] theorem lz_lDo1_ne_lbC2 : lDo1 ≠ lzC2 := by decide
@[simp] theorem lz_lDo1_ne_lbC3 : lDo1 ≠ lzC3 := by decide
@[simp] theorem lz_lDo1_ne_lbR : lDo1 ≠ lzR := by decide
@[simp] theorem lz_lDo1_ne_lbM2 : lDo1 ≠ lzM2 := by decide
@[simp] theorem lz_lDo1_ne_lbK1 : lDo1 ≠ lzK1 := by decide
@[simp] theorem lz_lDo1_ne_lbK2 : lDo1 ≠ lzK2 := by decide
@[simp] theorem lz_lDo1_ne_lbK3 : lDo1 ≠ lzK3 := by decide
@[simp] theorem lz_lDo1_ne_lbN : lDo1 ≠ lzN := by decide
@[simp] theorem lz_lDo1_ne_lbO : lDo1 ≠ lzO := by decide
@[simp] theorem lz_lDo1_ne_lbQ : lDo1 ≠ lzQ := by decide
@[simp] theorem lz_lDo2_ne_lbF : lDo2 ≠ lzF := by decide
@[simp] theorem lz_lDo2_ne_lbBl : lDo2 ≠ lzBl := by decide
@[simp] theorem lz_lDo2_ne_lbH : lDo2 ≠ lzH := by decide
@[simp] theorem lz_lDo2_ne_lbM : lDo2 ≠ lzM := by decide
@[simp] theorem lz_lDo2_ne_lbB : lDo2 ≠ lzB := by decide
@[simp] theorem lz_lDo2_ne_lbL : lDo2 ≠ lzL := by decide
@[simp] theorem lz_lDo2_ne_lbT : lDo2 ≠ lzT := by decide
@[simp] theorem lz_lDo2_ne_lbI : lDo2 ≠ lzI := by decide
@[simp] theorem lz_lDo2_ne_lbC1 : lDo2 ≠ lzC1 := by decide
@[simp] theorem lz_lDo2_ne_lbC2 : lDo2 ≠ lzC2 := by decide
@[simp] theorem lz_lDo2_ne_lbC3 : lDo2 ≠ lzC3 := by decide
@[simp] theorem lz_lDo2_ne_lbR : lDo2 ≠ lzR := by decide
@[simp] theorem lz_lDo2_ne_lbM2 : lDo2 ≠ lzM2 := by decide
@[simp] theorem lz_lDo2_ne_lbK1 : lDo2 ≠ lzK1 := by decide
@[simp] theorem lz_lDo2_ne_lbK2 : lDo2 ≠ lzK2 := by decide
@[simp] theorem lz_lDo2_ne_lbK3 : lDo2 ≠ lzK3 := by decide
@[simp] theorem lz_lDo2_ne_lbN : lDo2 ≠ lzN := by decide
@[simp] theorem lz_lDo2_ne_lbO : lDo2 ≠ lzO := by decide
@[simp] theorem lz_lDo2_ne_lbQ : lDo2 ≠ lzQ := by decide
@[simp] theorem lz_lRp_ne_lbF : lRp ≠ lzF := by decide
@[simp] theorem lz_lRp_ne_lbBl : lRp ≠ lzBl := by decide
@[simp] theorem lz_lRp_ne_lbH : lRp ≠ lzH := by decide
@[simp] theorem lz_lRp_ne_lbM : lRp ≠ lzM := by decide
@[simp] theorem lz_lRp_ne_lbB : lRp ≠ lzB := by decide
@[simp] theorem lz_lRp_ne_lbL : lRp ≠ lzL := by decide
@[simp] theorem lz_lRp_ne_lbT : lRp ≠ lzT := by decide
@[simp] theorem lz_lRp_ne_lbI : lRp ≠ lzI := by decide
@[simp] theorem lz_lRp_ne_lbC1 : lRp ≠ lzC1 := by decide
@[simp] theorem lz_lRp_ne_lbC2 : lRp ≠ lzC2 := by decide
@[simp] theorem lz_lRp_ne_lbC3 : lRp ≠ lzC3 := by decide
@[simp] theorem lz_lRp_ne_lbR : lRp ≠ lzR := by decide
@[simp] theorem lz_lRp_ne_lbM2 : lRp ≠ lzM2 := by decide
@[simp] theorem lz_lRp_ne_lbK1 : lRp ≠ lzK1 := by decide
@[simp] theorem lz_lRp_ne_lbK2 : lRp ≠ lzK2 := by decide
@[simp] theorem lz_lRp_ne_lbK3 : lRp ≠ lzK3 := by decide
@[simp] theorem lz_lRp_ne_lbN : lRp ≠ lzN := by decide
@[simp] theorem lz_lRp_ne_lbO : lRp ≠ lzO := by decide
@[simp] theorem lz_lRp_ne_lbQ : lRp ≠ lzQ := by decide
@[simp] theorem lz_lRn_ne_lbF : lRn ≠ lzF := by decide
@[simp] theorem lz_lRn_ne_lbBl : lRn ≠ lzBl := by decide
@[simp] theorem lz_lRn_ne_lbH : lRn ≠ lzH := by decide
@[simp] theorem lz_lRn_ne_lbM : lRn ≠ lzM := by decide
@[simp] theorem lz_lRn_ne_lbB : lRn ≠ lzB := by decide
@[simp] theorem lz_lRn_ne_lbL : lRn ≠ lzL := by decide
@[simp] theorem lz_lRn_ne_lbT : lRn ≠ lzT := by decide
@[simp] theorem lz_lRn_ne_lbI : lRn ≠ lzI := by decide
@[simp] theorem lz_lRn_ne_lbC1 : lRn ≠ lzC1 := by decide
@[simp] theorem lz_lRn_ne_lbC2 : lRn ≠ lzC2 := by decide
@[simp] theorem lz_lRn_ne_lbC3 : lRn ≠ lzC3 := by decide
@[simp] theorem lz_lRn_ne_lbR : lRn ≠ lzR := by decide
@[simp] theorem lz_lRn_ne_lbM2 : lRn ≠ lzM2 := by decide
@[simp] theorem lz_lRn_ne_lbK1 : lRn ≠ lzK1 := by decide
@[simp] theorem lz_lRn_ne_lbK2 : lRn ≠ lzK2 := by decide
@[simp] theorem lz_lRn_ne_lbK3 : lRn ≠ lzK3 := by decide
@[simp] theorem lz_lRn_ne_lbN : lRn ≠ lzN := by decide
@[simp] theorem lz_lRn_ne_lbO : lRn ≠ lzO := by decide
@[simp] theorem lz_lRn_ne_lbQ : lRn ≠ lzQ := by decide
@[simp] theorem lz_lFle_ne_lbF : lFle ≠ lzF := by decide
@[simp] theorem lz_lFle_ne_lbBl : lFle ≠ lzBl := by decide
@[simp] theorem lz_lFle_ne_lbH : lFle ≠ lzH := by decide
@[simp] theorem lz_lFle_ne_lbM : lFle ≠ lzM := by decide
@[simp] theorem lz_lFle_ne_lbB : lFle ≠ lzB := by decide
@[simp] theorem lz_lFle_ne_lbL : lFle ≠ lzL := by decide
@[simp] theorem lz_lFle_ne_lbT : lFle ≠ lzT := by decide
@[simp] theorem lz_lFle_ne_lbI : lFle ≠ lzI := by decide
@[simp] theorem lz_lFle_ne_lbC1 : lFle ≠ lzC1 := by decide
@[simp] theorem lz_lFle_ne_lbC2 : lFle ≠ lzC2 := by decide
@[simp] theorem lz_lFle_ne_lbC3 : lFle ≠ lzC3 := by decide
@[simp] theorem lz_lFle_ne_lbR : lFle ≠ lzR := by decide
@[simp] theorem lz_lFle_ne_lbM2 : lFle ≠ lzM2 := by decide
@[simp] theorem lz_lFle_ne_lbK1 : lFle ≠ lzK1 := by decide
@[simp] theorem lz_lFle_ne_lbK2 : lFle ≠ lzK2 := by decide
@[simp] theorem lz_lFle_ne_lbK3 : lFle ≠ lzK3 := by decide
@[simp] theorem lz_lFle_ne_lbN : lFle ≠ lzN := by decide
@[simp] theorem lz_lFle_ne_lbO : lFle ≠ lzO := by decide
@[simp] theorem lz_lFle_ne_lbQ : lFle ≠ lzQ := by decide
@[simp] theorem lz_lDir_ne_lbF : lDir ≠ lzF := by decide
@[simp] theorem lz_lDir_ne_lbBl : lDir ≠ lzBl := by decide
@[simp] theorem lz_lDir_ne_lbH : lDir ≠ lzH := by decide
@[simp] theorem lz_lDir_ne_lbM : lDir ≠ lzM := by decide
@[simp] theorem lz_lDir_ne_lbB : lDir ≠ lzB := by decide
@[simp] theorem lz_lDir_ne_lbL : lDir ≠ lzL := by decide
@[simp] theorem lz_lDir_ne_lbT : lDir ≠ lzT := by decide
@[simp] theorem lz_lDir_ne_lbI : lDir ≠ lzI := by decide
@[simp] theorem lz_lDir_ne_lbC1 : lDir ≠ lzC1 := by decide
@[simp] theorem lz_lDir_ne_lbC2 : lDir ≠ lzC2 := by decide
@[simp] theorem lz_lDir_ne_lbC3 : lDir ≠ lzC3 := by decide
@[simp] theorem lz_lDir_ne_lbR : lDir ≠ lzR := by decide
@[simp] theorem lz_lDir_ne_lbM2 : lDir ≠ lzM2 := by decide
@[simp] theorem lz_lDir_ne_lbK1 : lDir ≠ lzK1 := by decide
@[simp] theorem lz_lDir_ne_lbK2 : lDir ≠ lzK2 := by decide
@[simp] theorem lz_lDir_ne_lbK3 : lDir ≠ lzK3 := by decide
@[simp] theorem lz_lDir_ne_lbN : lDir ≠ lzN := by decide
@[simp] theorem lz_lDir_ne_lbO : lDir ≠ lzO := by decide
@[simp] theorem lz_lDir_ne_lbQ : lDir ≠ lzQ := by decide

def lzParams : List MlS := [lzF, lzBl, lzH, lzM]
def lzLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lDo1, lDo2, lRp, lRn, lzB, lzL, lzT, lzI, lzC1, lzC2, lzC3, lzR,
  lzM2, lzK1, lzK2, lzK3, lzN, lzO, lzQ]

def lzRet (C : Ctx) (er em : ExpHOL 64) : ProgHOL 64 :=
  allocP C lzO (.const 16) (.seq (.store (vv lzO) er) (.seq (.store (.op .add [vv lzO, .const 8]) em)
    (.return (vv lzO))))

def lzIns (C : Ctx) : ProgHOL 64 := mlInsP C lzN (vv lzH) (.const 0) (vv lzR) (vv lzM2) (lzRet C (vv lzR) (vv lzN))

def lzCall (k : MlS) (eD eH eM : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.local, k), none)) fLz [.op .sub [vv lzF, .const 1], eD, eH, eM])
  (.seq (.assign .local lzR (.load .one (vv k))) (.seq (.assign .local lzM2 (.load .one (.op .add [vv k, .const 8])))
    rest))

def lzArm2 (C : Ctx) : ProgHOL 64 :=
  lzCall lzK1 (vv lzBl) (vv lzC1) (vv lzM)
    (.ite (vv lzR) (lzCall lzK2 (vv lzBl) (vv lzC2) (vv lzM2) (lzIns C)) (lzIns C))

def lzArm3 (C : Ctx) : ProgHOL 64 :=
  lzCall lzK1 (vv lzBl) (vv lzC1) (vv lzM)
    (.ite (vv lzR) (lzCall lzK2 (vv lzBl) (vv lzC2) (vv lzM2)
      (.ite (vv lzR) (lzCall lzK3 (vv lzBl) (vv lzC3) (vv lzM2) (lzIns C)) (lzIns C))) (lzIns C))

def lzFvarK (C : Ctx) : ProgHOL 64 :=
  .seq (.call (some (some (.local, lzQ), none)) fMl [vv lzBl, vv lzI, vv lzT])
  (.ite (.cmp .notEqual (vv lzQ) (.const 0)) (lzCall lzK1 (vv lzBl) (vv lzT) (vv lzM) (lzIns C))
    (.seq (.assign .local lzR (.const 0)) (.seq (.assign .local lzM2 (vv lzM)) (lzIns C))))

def lzFvar (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local lzT (.load .one (vv lRp)))
  (.ite (.cmp .equal (vv lRn) (.const 1)) (.seq (.assign .local lzI (.const 0)) (lzFvarK C))
    (.ite (.cmp .equal (vv lRn) (.const 2))
      (.seq (.assign .local lzI (.load .one (.op .add [vv lRp, .const 8]))) (lzFvarK C)) hang))

def lzCore (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .equal (vv lzF) (.const 0)) hang
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv lzH)) (.seq (storeDerived 9 10)
  (.seq (.assign .local lzB (.op .and [.shift .lsr (vv lDo1) (.const 1), .const 32767]))
  (.ite (.cmp .equal (vv lzB) (.const 0)) (lzRet C (.const 1) (vv lzM))
  (.seq (.call (some (some (.local, lzL), none)) fMl [vv lzM, vv lzH, .const 0])
  (.ite (.cmp .notEqual (vv lzL) (.const 0)) (lzRet C (.op .sub [vv lzL, .const 1]) (vv lzM))
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv lzH)) (.seq eViewP
  (.ite (.cmp .equal (vv lDg) (.const 1)) (lzFvar C)
  (.ite (.cmp .equal (vv lDg) (.const 4))
    (.seq (.assign .local lzC1 (.load .one (vv lRp)))
      (.seq (.assign .local lzC2 (.load .one (.op .add [vv lRp, .const 8]))) (lzArm2 C)))
  (.ite (.cmp .equal (vv lDg) (.const 5))
    (.seq (.assign .local lzC1 (.load .one (vv lRp)))
      (.seq (.assign .local lzC2 (.load .one (.op .add [vv lRp, .const 8]))) (lzArm2 C)))
  (.ite (.cmp .equal (vv lDg) (.const 6))
    (.seq (.assign .local lzC1 (.load .one (vv lRp)))
      (.seq (.assign .local lzC2 (.load .one (.op .add [vv lRp, .const 8]))) (lzArm2 C)))
  (.ite (.cmp .equal (vv lDg) (.const 7))
    (.seq (.assign .local lzC1 (.load .one (vv lRp)))
      (.seq (.assign .local lzC2 (.load .one (.op .add [vv lRp, .const 8])))
        (.seq (.assign .local lzC3 (.load .one (.op .add [vv lRp, .const 16]))) (lzArm3 C))))
  (.ite (.cmp .equal (vv lDg) (.const 9))
    (.seq (.assign .local lzC1 (.load .one (.op .add [vv lRp, .const 8]))) (lzCall lzK1 (vv lzBl) (vv lzC1) (vv lzM) (lzIns C)))
    (.seq (.assign .local lzR (.const 1)) (.seq (.assign .local lzM2 (vv lzM)) (lzIns C)))))))))))))))))))

def lzBody (C : Ctx) : ProgHOL 64 := prologue lzLocals (lzCore C)

structure LzCodes (C : Ctx) : Prop where
  ml : C.code.lookup fMl = some (mlParams.map (fun p => (p, ShapeHOL.one)), mlBody, .one)
  self : C.code.lookup fLz = some (lzParams.map (fun p => (p, ShapeHOL.one)), lzBody C, .one)

section
variable {σ : Type}

/-- The answer and memo as a fresh pair block, nothing else changes. -/
def PostLb (C : Ctx) (s : AState) (rm : Bool × Std.HashMap EIdx Bool) (w : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  s' = s ∧ ∃ H' o pm, C.H <+: H' ∧ w = cellA C o ∧ H'[o]? = some (boolW rm.1) ∧ H'[o + 1]? = some pm ∧
    LbRep C H' pm rm.2 ∧ SR (ctxH C H') s st

theorem postLz_locals (C : Ctx) (s : AState) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostLb C s a w s' st → PostLb C s a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, H', o, pm, h2, h3, h4, h5, h6, h7⟩ => ⟨h1, H', o, pm, h2, h3, h4, h5, h6, sr_of_eq h7 rfl rfl rfl rfl⟩

theorem specR_lzRetI {C : Ctx} (hok : CtxOK C) {H0 H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem}
    {D : List MlS} (er em : ExpHOL 64) (r : Bool) (pm : BitVec 64) (memo : Std.HashMap EIdx Bool)
    (hD : lzO ∈ D) (her : ∀ w, sev ((lzO, w) :: Γ) er = some (boolW r)) (hem : ∀ w, sev ((lzO, w) :: Γ) em = some pm)
    (hrep : LbRep C H pm memo) (h0 : H0 <+: H) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (lzRet C er em) s (pure (r, memo)) (PostLb (ctxH C H0) s) := by
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hlay := hok.heapLay
  refine specR_allocI (C := ctxH C H) lzO (.const 16) 2 (by omega) hD (fun _ => rfl) (fun H1 ws hp1 hws hroom => ?_)
  have hp1' : H <+: H1 := hp1
  have hL := hp1'.length_le
  change SpecR (Inv (ctxH C (H1 ++ ws)) s ((lzO, cellA C H1.length) :: Γ) _ _) _ _ _ _
  refine specR_heapStoreI (ctxOK_H hok _) (vv lzO) er H1.length (by show _ < (H1 ++ ws).length; simp; omega)
    (boolW r) (by simp <;> rfl) (her _) ?_
  change SpecR (Inv (ctxH C ((H1 ++ ws).set H1.length (boolW r))) _ _ _ _) _ _ _ _
  refine specR_heapStoreI (ctxOK_H hok _) (.op .add [vv lzO, .const 8]) em (H1.length + 1)
    (by show _ < ((H1 ++ ws).set _ _).length; simp; omega) pm (by simp +decide [sev]; exact cellA_add8 C _) (hem _) ?_
  have g0 : (((H1 ++ ws).set H1.length (boolW r)).set (H1.length + 1) pm)[H1.length]? = some (boolW r) := by
    simp [List.getElem?_set, hws]
  have g1 : (((H1 ++ ws).set H1.length (boolW r)).set (H1.length + 1) pm)[H1.length + 1]? = some pm := by
    simp [List.getElem?_set, hws]
  have hpre : H <+: ((H1 ++ ws).set H1.length (boolW r)).set (H1.length + 1) pm :=
    prefix_set_ge (prefix_set_ge (hp1'.trans (List.prefix_append _ _)) _ (by omega) _) _ (by omega) _
  exact specR_returnI _ (cellA C H1.length) (by simp +decide [Env.get] <;> rfl)
    (fun t ht => ⟨rfl, _, H1.length, pm, h0.trans hpre, rfl, g0, g1, lbRep_toH (lbRep_mono hpre hrep), sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem specR_lzInsI {C : Ctx} (hok : CtxOK C) {H0 H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem}
    {D : List MlS} (h : EIdx) (pb : BitVec 64) (r : Bool) (pm : BitVec 64)
    (memo : Std.HashMap EIdx Bool) (hD : lzN ∈ D ∧ lzO ∈ D) (hH : Γ.get lzH = some (Enc.idxW h))
    (hDv : Γ.get lzBl = some pb) (hR : Γ.get lzR = some (boolW r)) (hM : Γ.get lzM2 = some pm)
    (hrep : LbRep C H pm memo) (h0 : H0 <+: H) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (lzIns C) s (pure (r, memo.insert h r)) (PostLb (ctxH C H0) s) := by
  obtain ⟨xs, hm, he⟩ := hrep
  unfold lzIns
  refine specR_mlInsI hok lzN (vv lzH) (.const 0) (vv lzR) (vv lzM2) (Enc.idxW h) 0 pm r xs hD.1
    (fun w => by simp [Env.get, hH]) (fun w => rfl) (fun w => by simp [Env.get, hR])
    (fun w => by simp [Env.get, hM]) hm (fun H' o hp' hm' => ?_)
  exact specR_lzRetI hok (vv lzR) (vv lzN) r (cellA C o) (memo.insert h r) hD.2
    (fun w => by simp [Env.get, hR]) (fun w => by simp [Env.get]) (lbRep_insert he h r hm') (h0.trans hp')

theorem lz_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ lzLocals → (ctxEnv C ++ lzParams.zip vals).get x = none :=
  Knot.params_none C lzLocals lzParams vals (by decide) (by decide)

/-- The walk's spec at fuel `n`, for every argument (the induction hypothesis the arms use). -/
def LzRec (C : Ctx) (bl : List (Nat × EIdx)) (pb : BitVec 64) (n : Nat) : Prop :=
  ∀ (h : EIdx) (memo : Std.HashMap EIdx Bool) (H : List (BitVec 64)) (s : AState) (pm : BitVec 64),
    C.H <+: H → LbRep C H pm memo →
    SpecR (σ := σ) (Pre (ctxH C H) s (lzParams.zip [BitVec.ofNat 64 n, pb, Enc.idxW h, pm]))
      (lzBody C) s (leavesSubGo bl memo n h) (PostLb (ctxH C H) s)

/-- One recursive call, then the pair block read back. -/
theorem specR_lzCallI {α : Type} {C : Ctx} (hok : CtxOK C) (hc : LzCodes C) {n : Nat} (bl : List (Nat × EIdx)) (pb : BitVec 64) (ih : LzRec (σ := σ) C bl pb n)
    {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {k : Bool × Std.HashMap EIdx Bool → AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (eD eH eM : ExpHOL 64) (h : EIdx) (pm : BitVec 64) (memo : Std.HashMap EIdx Bool)
    (hx : x ∈ D ∧ lzR ∈ D ∧ lzM2 ∈ D) (hxn : x ≠ lzR ∧ lzM2 ≠ x) (hp : C.H <+: H) (hrep : LbRep C H pm memo)
    (hF : Γ.get lzF = some (BitVec.ofNat 64 (n + 1))) (heD : sev Γ eD = some pb)
    (heH : sev Γ eH = some (Enc.idxW h)) (heM : sev Γ eM = some pm)
    (hk : ∀ (rm : Bool × Std.HashMap EIdx Bool) H' pm' w, H <+: H' → LbRep C H' pm' rm.2 →
      SpecR (Inv (ctxH C H') s ((lzM2, pm') :: (lzR, boolW rm.1) :: (x, w) :: Γ) [] D) rest s (k rm) R) :
    SpecR (Inv (ctxH C H) s Γ M D) (lzCall x eD eH eM rest) s (leavesSubGo bl memo n h >>= k) R := by
  unfold lzCall
  refine specR_callNIH (C := ctxH C H) x fLz lzParams [.op .sub [vv lzF, .const 1], eD, eH, eM] (lzBody C)
    [BitVec.ofNat 64 n, pb, Enc.idxW h, pm] (by decide) rfl hx.1 hc.self
    ⟨by simp [sev, hF]; exact Ex.ofNat_succ_sub_one _, heD, heH, heM, trivial⟩
    (PostLb (ctxH C H) s)
    (fun rm w s' H' => s' = s ∧ ∃ o pm', w = cellA C o ∧ H'[o]? = some (boolW rm.1) ∧ H'[o + 1]? = some pm' ∧
      LbRep C H' pm' rm.2)
    (fun rm w s' st ⟨h1, H', o, pm', hp', hw, h0, h1', hrep', hsr⟩ =>
      ⟨H', hp', ⟨h1, o, pm', hw, h0, h1', lbRep_ofH hrep'⟩, by subst h1; exact hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu lzParams _ rfl hlk) (ih h memo H s pm hp hrep))
    (fun rm w s' H' hp' ⟨hs', o, pm', hw, h0, h1', hrep'⟩ => ?_)
  subst hs' hw
  refine UD.specR_heapLoadI' (C := ctxH C H') lzR (vv x) o (boolW rm.1) h0 hx.2.1 (by simp [Env.get]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H') lzM2 (.op .add [vv x, .const 8]) (o + 1) pm' h1' hx.2.2
    (by simp [sev, Env.get, hxn.1]; exact (cellA_add8 C o : _)) ?_
  exact hk rm H' pm' (cellA C o) hp' hrep'


end

theorem specR_lzArm2I {C : Ctx} (hok : CtxOK C) (hc : LzCodes C) {n : Nat} (bl : List (Nat × EIdx)) (pb : BitVec 64) (ih : LzRec (σ := σ) C bl pb n)
    {H0 H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (h : EIdx)
    (c1 c2 : EIdx) (pm : BitVec 64) (memo : Std.HashMap EIdx Bool)
    (hD : lzK1 ∈ D ∧ lzK2 ∈ D ∧ lzR ∈ D ∧ lzM2 ∈ D ∧ lzN ∈ D ∧ lzO ∈ D) (hp : C.H <+: H) (h0 : H0 <+: H)
    (hrep : LbRep C H pm memo) (hF : Γ.get lzF = some (BitVec.ofNat 64 (n + 1)))
    (hDv : Γ.get lzBl = some pb) (hH : Γ.get lzH = some (Enc.idxW h)) (hM : Γ.get lzM = some pm)
    (hC1 : Γ.get lzC1 = some (Enc.idxW c1)) (hC2 : Γ.get lzC2 = some (Enc.idxW c2)) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (lzArm2 C) s
      ((leavesSubGo bl memo n c1 >>= fun x => match x with
        | (rf, m) => if rf = true then leavesSubGo bl m n c2 else pure (false, m)) >>= fun x => match x with
        | (r, m') => pure (r, m'.insert h r)) (PostLb (ctxH C H0) s) := by
  unfold lzArm2
  rw [bind_assoc]
  refine specR_lzCallI hok hc bl pb ih lzK1 (vv lzBl) (vv lzC1) (vv lzM) c1 pm memo ⟨hD.1, hD.2.2.1, hD.2.2.2.1⟩
    ⟨by decide, by decide⟩ hp hrep hF (by simp [hDv]) (by simp [hC1]) (by simp [hM])
    (fun rm H1 pm1 w1 hp1 hrep1 => ?_)
  obtain ⟨rf, m1⟩ := rm
  dsimp only
  cases rf
  · refine specR_ifI _ 0 (by simp [Env.get, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
    exact specR_lzInsI hok h pb false pm1 m1 ⟨hD.2.2.2.2.1, hD.2.2.2.2.2⟩ (by simp [Env.get, hH])
      (by simp [Env.get, hDv]) (by simp [Env.get]) (by simp [Env.get]) hrep1 (h0.trans hp1)
  · refine specR_ifI _ 1 (by simp [Env.get, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [↓reduceIte]
    refine specR_lzCallI hok hc bl pb ih lzK2 (vv lzBl) (vv lzC2) (vv lzM2) c2 pm1 m1 ⟨hD.2.1, hD.2.2.1, hD.2.2.2.1⟩
      ⟨by decide, by decide⟩ (hp.trans hp1) hrep1 (by simp [Env.get, hF]) (by simp [Env.get, hDv])
      (by simp [Env.get, hC2]) (by simp [Env.get]) (fun rm H2 pm2 w2 hp2 hrep2 => ?_)
    obtain ⟨r2, m2⟩ := rm
    dsimp only
    exact specR_lzInsI hok h pb r2 pm2 m2 ⟨hD.2.2.2.2.1, hD.2.2.2.2.2⟩ (by simp [Env.get, hH])
      (by simp [Env.get, hDv]) (by simp [Env.get]) (by simp [Env.get]) hrep2 (h0.trans (hp1.trans hp2))

theorem specR_lzArm3I {C : Ctx} (hok : CtxOK C) (hc : LzCodes C) {n : Nat} (bl : List (Nat × EIdx)) (pb : BitVec 64) (ih : LzRec (σ := σ) C bl pb n)
    {H0 H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (h : EIdx)
    (c1 c2 c3 : EIdx) (pm : BitVec 64) (memo : Std.HashMap EIdx Bool)
    (hD : lzK1 ∈ D ∧ lzK2 ∈ D ∧ lzK3 ∈ D ∧ lzR ∈ D ∧ lzM2 ∈ D ∧ lzN ∈ D ∧ lzO ∈ D) (hp : C.H <+: H)
    (h0 : H0 <+: H) (hrep : LbRep C H pm memo) (hF : Γ.get lzF = some (BitVec.ofNat 64 (n + 1)))
    (hDv : Γ.get lzBl = some pb) (hH : Γ.get lzH = some (Enc.idxW h)) (hM : Γ.get lzM = some pm)
    (hC1 : Γ.get lzC1 = some (Enc.idxW c1)) (hC2 : Γ.get lzC2 = some (Enc.idxW c2))
    (hC3 : Γ.get lzC3 = some (Enc.idxW c3)) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (lzArm3 C) s
      ((leavesSubGo bl memo n c1 >>= fun x => match x with
        | (rt, m) => if rt = true then (leavesSubGo bl m n c2 >>= fun y => match y with
          | (rv, m2) => if rv = true then leavesSubGo bl m2 n c3 else pure (false, m2)) else pure (false, m)) >>=
        fun x => match x with | (r, m') => pure (r, m'.insert h r)) (PostLb (ctxH C H0) s) := by
  unfold lzArm3
  rw [bind_assoc]
  refine specR_lzCallI hok hc bl pb ih lzK1 (vv lzBl) (vv lzC1) (vv lzM) c1 pm memo ⟨hD.1, hD.2.2.2.1, hD.2.2.2.2.1⟩
    ⟨by decide, by decide⟩ hp hrep hF (by simp [hDv]) (by simp [hC1]) (by simp [hM])
    (fun rm H1 pm1 w1 hp1 hrep1 => ?_)
  obtain ⟨rt, m1⟩ := rm
  dsimp only
  cases rt
  · refine specR_ifI _ 0 (by simp [Env.get, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
    exact specR_lzInsI hok h pb false pm1 m1 ⟨hD.2.2.2.2.2.1, hD.2.2.2.2.2.2⟩ (by simp [Env.get, hH])
      (by simp [Env.get, hDv]) (by simp [Env.get]) (by simp [Env.get]) hrep1 (h0.trans hp1)
  refine specR_ifI _ 1 (by simp [Env.get, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
  simp only [↓reduceIte, bind_assoc]
  refine specR_lzCallI hok hc bl pb ih lzK2 (vv lzBl) (vv lzC2) (vv lzM2) c2 pm1 m1 ⟨hD.2.1, hD.2.2.2.1, hD.2.2.2.2.1⟩
    ⟨by decide, by decide⟩ (hp.trans hp1) hrep1 (by simp [Env.get, hF]) (by simp [Env.get, hDv])
    (by simp [Env.get, hC2]) (by simp [Env.get]) (fun rm H2 pm2 w2 hp2 hrep2 => ?_)
  obtain ⟨rv, m2⟩ := rm
  dsimp only
  cases rv
  · refine specR_ifI _ 0 (by simp [Env.get, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
    exact specR_lzInsI hok h pb false pm2 m2 ⟨hD.2.2.2.2.2.1, hD.2.2.2.2.2.2⟩ (by simp [Env.get, hH])
      (by simp [Env.get, hDv]) (by simp [Env.get]) (by simp [Env.get]) hrep2 (h0.trans (hp1.trans hp2))
  refine specR_ifI _ 1 (by simp [Env.get, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
  simp only [↓reduceIte]
  refine specR_lzCallI hok hc bl pb ih lzK3 (vv lzBl) (vv lzC3) (vv lzM2) c3 pm2 m2 ⟨hD.2.2.1, hD.2.2.2.1, hD.2.2.2.2.1⟩
    ⟨by decide, by decide⟩ ((hp.trans hp1).trans hp2) hrep2 (by simp [Env.get, hF]) (by simp [Env.get, hDv])
    (by simp [Env.get, hC3]) (by simp [Env.get]) (fun rm H3 pm3 w3 hp3 hrep3 => ?_)
  obtain ⟨r3, m3⟩ := rm
  dsimp only
  exact specR_lzInsI hok h pb r3 pm3 m3 ⟨hD.2.2.2.2.2.1, hD.2.2.2.2.2.2⟩ (by simp [Env.get, hH])
    (by simp [Env.get, hDv]) (by simp [Env.get]) (by simp [Env.get]) hrep3 (h0.trans (hp1.trans (hp2.trans hp3)))

theorem lz_spec (C : Ctx) (hok : CtxOK C) (hc : LzCodes C) (bl : List (Nat × EIdx)) (pb : BitVec 64)
    (hacc : AccRep C C.H pb bl) : ∀ n, n < 2 ^ 64 → LzRec (σ := σ) C bl pb n := by
  intro n
  induction n with
  | zero =>
    intro _ h memo H s pm hp hrep
    refine specR_prologue (postLz_locals _ _) (lz_none _ _) ?_
    unfold lzCore
    rw [leavesSubGo_zero]
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get, lzParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  | succ n ih =>
  intro hn h memo H s pm hp hrep
  have ih' := ih (by omega)
  obtain ⟨xs, hm, he⟩ := id hrep
  refine specR_prologue (postLz_locals _ _) (lz_none _ _) ?_
  unfold lzCore
  rw [leavesSubGo_succ]
  have hne := ofNat_succ_ne n (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, lzParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv lzH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]) ?_
  refine specR_derivedEI (C := ctxH C H) h (by simp) (by simp <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) ?_
  have hb15 : (ConLeche.fvarOfData (s.store.derived h)).toNat < 2 ^ 15 := by
    simp only [ConLeche.fvarOfData, UInt64.toNat_mod]; simp; omega
  have hbt : (ConLeche.fvarOfData (s.store.derived h)).toBitVec =
      BitVec.ofNat 64 (ConLeche.fvarOfData (s.store.derived h)).toNat := by
    apply BitVec.eq_of_toNat_eq; simp
  refine specR_assignI lzB _ (ConLeche.fvarOfData (s.store.derived h)).toBitVec (by decide)
    (by simp [sev]; exact ExF.fvarOfData_word _) ?_
  generalize hbdef : (ConLeche.fvarOfData (s.store.derived h)).toNat = b at hb15 hbt
  rw [hbt]
  by_cases hb0 : b = 0
  · subst hb0
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    simp only [beq_self_eq_true, ↓reduceIte]
    exact specR_lzRetI hok (.const 1) (vv lzM) true pm memo (by decide) (fun w => rfl)
      (fun w => by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]) hrep (List.prefix_refl _)
  have hbne : BitVec.ofNat 64 b ≠ 0 := by intro e; have := congrArg BitVec.toNat e; simp at this; omega
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hbne) (fun h => absurd rfl h)
    (fun _ => ?_)
  simp only [show (b == 0) = false by simpa using hb0, Bool.false_eq_true, ↓reduceIte]
  refine specR_callPure (C := ctxH C H) lzL fMl mlParams [vv lzM, vv lzH, .const 0] mlBody
    [pm, Enc.idxW h, 0] (xs.lookup (Enc.idxW h, 0)) (by decide) rfl (by decide) hc.ml
    ⟨by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv],
      by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv],
      rfl, trivial⟩
    (PostWV (ctxH C H) s) (fun o w s' H' => w = optWG boolW o ∧ H' = H)
    (fun o w s' st ⟨h1, h2, h3⟩ => ⟨H, List.prefix_refl _, ⟨h2, rfl⟩, by subst h1; exact h3⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mlParams _ rfl hlk)
      (ml_spec C hok hc.ml (Enc.idxW h) 0 xs pm H s (mnodes_toH hm)))
    (fun w H' _ ⟨hw, hH'⟩ => ?_)
  subst hw; subst H'
  rw [he h]
  cases hlk : xs.lookup (Enc.idxW h, 0) with
  | some r =>
    have hne1 : boolW r + 1 ≠ 0 := by cases r <;> decide
    refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne1) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact specR_lzRetI hok _ (vv lzM) r pm memo (by decide) (fun w => by simp [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, optWG]; exact BitVec.add_sub_cancel _ _)
      (fun w => by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]) hrep (List.prefix_refl _)
  | none =>
  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
    (fun _ => ?_)
  dsimp only
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv lzH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]) ?_
  refine specR_viewP (C := ctxH C H) h (by simp) (by simp +decide [Env.get] <;> rfl)
    (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn hsh => ?_)
  refine specR_congr (view_bind_eq h v _ s hv) ?_
  rcases v with i | ⟨idx, ty⟩ | u | ⟨cn, cus⟩ | ⟨f, a⟩ | ⟨ty, b⟩ | ⟨ty, b⟩ | ⟨ty, v, b⟩ | l | ⟨pn, pi, sub⟩
  · -- bvar
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI lzR (.const 1) (boolW true) (by decide) rfl ?_
    refine specR_assignI lzM2 (vv lzM) pm (by decide) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]) ?_
    simp only [pure_bind]
    exact specR_lzInsI hok h pb true pm memo ⟨by decide, by decide⟩ (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv])
      (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem]) hrep (List.prefix_refl _)
  · -- fvar
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    have hK : ∀ (Γ' : Env) (M' : Mem), idx < 2 ^ 64 → Γ'.get lzI = some (BitVec.ofNat 64 idx) →
        Γ'.get lzT = some (Enc.idxW ty) → Γ'.get lzBl = some pb → Γ'.get lzH = some (Enc.idxW h) →
        Γ'.get lzM = some pm → Γ'.get lzF = some (BitVec.ofNat 64 (n + 1)) →
        SpecR (σ := σ) (Inv (ctxH C H) s Γ' M' (ctxLocals ++ lzLocals)) (lzFvarK C) s
          (if leafMem bl idx ty = true then (leavesSubGo bl memo n ty >>= fun y => pure (y.1, y.2.insert h y.1))
            else ((pure (false, memo) : AM (Bool × Std.HashMap EIdx Bool)) >>= fun y =>
              pure (y.1, y.2.insert h y.1))) (PostLb (ctxH C H) s) := by
      intro Γ' M' hib hI hT hDv hH hM hF
      unfold lzFvarK
      obtain ⟨hacm, hacs⟩ := accRep_mono hp hacc
      have hlm := leafMem_lookup bl hacs idx ty hib
      refine specR_callPure (C := ctxH C H) lzQ fMl mlParams [vv lzBl, vv lzI, vv lzT] mlBody
        [pb, BitVec.ofNat 64 idx, Enc.idxW ty] ((bl.map accEnc).lookup (BitVec.ofNat 64 idx, Enc.idxW ty))
        (by decide) rfl (by decide) hc.ml ⟨by simp [hDv], by simp [hI], by simp [hT], trivial⟩
        (PostWV (ctxH C H) s) (fun o w s' H' => w = optWG boolW o ∧ H' = H)
        (fun o w s' st ⟨h1, h2, h3⟩ => ⟨H, List.prefix_refl _, ⟨h2, rfl⟩, by subst h1; exact h3⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mlParams _ rfl hlk)
          (ml_spec C hok hc.ml (BitVec.ofNat 64 idx) (Enc.idxW ty) (bl.map accEnc) pb H s hacm))
        (fun w H' _ ⟨hw, hH'⟩ => ?_)
      subst hw; subst H'
      rw [hlm]
      cases hq : (bl.map accEnc).lookup (BitVec.ofNat 64 idx, Enc.idxW ty) with
      | some v =>
        simp only [Option.isSome_some, ↓reduceIte]
        have hne1 : boolW v + 1 ≠ 0 := by cases v <;> decide
        refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne1) (fun _ => ?_)
          (fun h => absurd h (by decide))
        refine specR_lzCallI hok hc bl pb ih' lzK1 (vv lzBl) (vv lzT) (vv lzM) ty pm memo ⟨by decide, by decide, by decide⟩
          ⟨by decide, by decide⟩ hp hrep (by simp [Env.get, hF]) (by simp [Env.get, hDv]) (by simp [Env.get, hT])
          (by simp [Env.get, hM]) (fun rm H1 pm1 w1 hp1 hrep1 => ?_)
        obtain ⟨r1, m1⟩ := rm
        dsimp only
        exact specR_lzInsI hok h pb r1 pm1 m1 ⟨by decide, by decide⟩ (by simp [Env.get, hH]) (by simp [Env.get, hDv])
          (by simp [Env.get]) (by simp [Env.get]) hrep1 hp1
      | none =>
        simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
        refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
        refine specR_assignI lzR (.const 0) (boolW false) (by decide) rfl ?_
        refine specR_assignI lzM2 (vv lzM) pm (by decide) (by simp [Env.get, hM]) ?_
        simp only [pure_bind]
        exact specR_lzInsI hok h pb false pm memo ⟨by decide, by decide⟩ (by simp [Env.get, hH])
          (by simp [Env.get, hDv]) (by simp [Env.get]) (by simp [Env.get]) hrep (List.prefix_refl _)
    unfold lzFvar
    refine specR_loadI' lzT (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encFVar] using wordsAt_mem0 P _ _ []) ?_
    have hlen : (encEView (.fvar idx ty)).length = 1 + (Enc.limbs idx).length := by
      simp [encEView, Enc.encFVar]; omega
    by_cases i0 : idx = 0
    · subst i0
      refine specR_ifI _ 1 (by simp +decide [sev, hlen, Enc.limbs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun hw => absurd hw (by decide))
      refine specR_assignI lzI (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
      refine hK _ _ (by decide) ?_ ?_ ?_ ?_ ?_ ?_ <;> simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]
    · by_cases ib : idx < 2 ^ 64
      · have hl : Enc.limbs idx = [BitVec.ofNat 64 idx] := by rw [limbs_small idx ib]; simp [i0]
        refine specR_ifI _ 0 (by simp +decide [sev, hlen, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
        refine specR_ifI _ 1 (by simp +decide [sev, hlen, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_loadI' lzI _ (P + 8) (P + BitVec.ofNat 64 8) (BitVec.ofNat 64 idx) (by decide)
          (by simp +decide [sev]) rfl
          (by have := wordsAt_mem1 P (Enc.idxW ty) (BitVec.ofNat 64 idx) [] (M := []); simpa [encEView, Enc.encFVar, hl] using this) ?_
        refine hK _ _ ib ?_ ?_ ?_ ?_ ?_ ?_ <;> simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]
      · have hl := ExI.limbs_len_ge2 idx (by omega)
        have hlt : 1 + (Enc.limbs idx).length < 2 ^ 61 := by rw [← hlen]; exact hsh
        have hn1 : BitVec.ofNat 64 (1 + (Enc.limbs idx).length) ≠ 1#64 := by
          intro e; have := congrArg BitVec.toNat e; simp at this; omega
        have hn2 : BitVec.ofNat 64 (1 + (Enc.limbs idx).length) ≠ 2#64 := by
          intro e; have := congrArg BitVec.toNat e; simp at this; omega
        refine specR_ifI _ 0 (by simp +decide [sev, hlen, hn1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
        exact specR_ifI _ 0 (by simp +decide [sev, hlen, hn2, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => specR_hangI)
  · -- sort
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI lzR (.const 1) (boolW true) (by decide) rfl ?_
    refine specR_assignI lzM2 (vv lzM) pm (by decide) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]) ?_
    simp only [pure_bind]
    exact specR_lzInsI hok h pb true pm memo ⟨by decide, by decide⟩ (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv])
      (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem]) hrep (List.prefix_refl _)
  · -- const
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI lzR (.const 1) (boolW true) (by decide) rfl ?_
    refine specR_assignI lzM2 (vv lzM) pm (by decide) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]) ?_
    simp only [pure_bind]
    exact specR_lzInsI hok h pb true pm memo ⟨by decide, by decide⟩ (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv])
      (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem]) hrep (List.prefix_refl _)
  · -- app
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' lzC1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW f) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encApp] using wordsAt_mem0 P _ _ []) ?_
    refine specR_loadI' lzC2 _ (P + 8) (P + BitVec.ofNat 64 (8 * 1)) (Enc.idxW a) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encApp] using wordsAt_mem1 P _ _ [] []) ?_
    simp only [leavesSubArmApp]
    exact specR_lzArm2I hok hc bl pb ih' h _ _ pm memo ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
      hp (List.prefix_refl _) hrep (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv])
      (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem])
      (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem])
  · -- lam
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' lzC1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P _ _ []) ?_
    refine specR_loadI' lzC2 _ (P + 8) (P + BitVec.ofNat 64 (8 * 1)) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P _ _ [] []) ?_
    simp only [leavesSubArmBind]
    exact specR_lzArm2I hok hc bl pb ih' h _ _ pm memo ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
      hp (List.prefix_refl _) hrep (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv])
      (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem])
      (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem])
  · -- forallE
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' lzC1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P _ _ []) ?_
    refine specR_loadI' lzC2 _ (P + 8) (P + BitVec.ofNat 64 (8 * 1)) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P _ _ [] []) ?_
    simp only [leavesSubArmBind]
    exact specR_lzArm2I hok hc bl pb ih' h _ _ pm memo ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
      hp (List.prefix_refl _) hrep (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv])
      (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem])
      (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem])
  · -- letE
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' lzC1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encLet] using wordsAt_mem0 P _ _ []) ?_
    refine specR_loadI' lzC2 _ (P + 8) (P + BitVec.ofNat 64 (8 * 1)) (Enc.idxW v) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encLet] using wordsAt_mem1 P _ _ [Enc.idxW b] []) ?_
    refine specR_loadI' lzC3 _ (P + 16) (P + BitVec.ofNat 64 (8 * 2)) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encLet] using (wordsAt_get P [Enc.idxW ty, Enc.idxW v, Enc.idxW b] 2 (by simp) [] : (P + BitVec.ofNat 64 (8 * 2), Enc.idxW b) ∈ _)) ?_
    simp only [leavesSubArmLet]
    exact specR_lzArm3I hok hc bl pb ih' h _ _ _ pm memo ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
      hp (List.prefix_refl _) hrep (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv])
      (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem])
      (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem])
  · -- lit
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI lzR (.const 1) (boolW true) (by decide) rfl ?_
    refine specR_assignI lzM2 (vv lzM) pm (by decide) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]) ?_
    simp only [pure_bind]
    exact specR_lzInsI hok h pb true pm memo ⟨by decide, by decide⟩ (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv])
      (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem]) hrep (List.prefix_refl _)
  · -- proj
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' lzC1 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW sub) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encProj] using wordsAt_mem1 P (Enc.idxW pn) (Enc.idxW sub) (Enc.limbs pi) []) ?_
    refine specR_lzCallI hok hc bl pb ih' lzK1 (vv lzBl) (vv lzC1) (vv lzM) sub pm memo ⟨by decide, by decide, by decide⟩
      ⟨by decide, by decide⟩ hp hrep (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv])
      (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]) (by simp +decide [Env.get])
      (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]) (fun rm H1 pm1 w1 hp1 hrep1 => ?_)
    obtain ⟨r1, m1⟩ := rm
    dsimp only
    exact specR_lzInsI hok h pb r1 pm1 m1 ⟨by decide, by decide⟩ (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv])
      (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, lzParams, ctxEnv]) (by simp [Env.get]) (by simp [Env.get]) hrep1 hp1

end ConPanqueque.T.WC
