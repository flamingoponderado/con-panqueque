import ConPanqueque.T.Core.MemoList
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `wscopedBGo`: every free variable below the depth, memoized on `(handle, depth)`

The twin threads its memo through results; the port keeps it as a heap memo list (`WsRep`) and returns a fresh
two-cell block `[r, memo]`. The fvar-range cut reads the derived word; a memo hit returns at once; otherwise the
node's arm runs and its answer is inserted.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def wsF := ofString "wsf"
def wsD := ofString "wsd"
def wsH := ofString "wsh"
def wsM := ofString "wsm"
def wsB := ofString "wsb"
def wsL := ofString "wsl"
def wsT := ofString "wst"
def wsI := ofString "wsi"
def wsC1 := ofString "wsc1"
def wsC2 := ofString "wsc2"
def wsC3 := ofString "wsc3"
def wsR := ofString "wsr"
def wsM2 := ofString "wsm2"
def wsK1 := ofString "wsk1"
def wsK2 := ofString "wsk2"
def wsK3 := ofString "wsk3"
def wsN := ofString "wsn"
def wsO := ofString "wso"
def fWs := ofString "wscopedBGo"

@[simp] theorem ws_wsF_ne_wsD : wsF ≠ wsD := by decide
@[simp] theorem ws_wsF_ne_wsH : wsF ≠ wsH := by decide
@[simp] theorem ws_wsF_ne_wsM : wsF ≠ wsM := by decide
@[simp] theorem ws_wsF_ne_wsB : wsF ≠ wsB := by decide
@[simp] theorem ws_wsF_ne_wsL : wsF ≠ wsL := by decide
@[simp] theorem ws_wsF_ne_wsT : wsF ≠ wsT := by decide
@[simp] theorem ws_wsF_ne_wsI : wsF ≠ wsI := by decide
@[simp] theorem ws_wsF_ne_wsC1 : wsF ≠ wsC1 := by decide
@[simp] theorem ws_wsF_ne_wsC2 : wsF ≠ wsC2 := by decide
@[simp] theorem ws_wsF_ne_wsC3 : wsF ≠ wsC3 := by decide
@[simp] theorem ws_wsF_ne_wsR : wsF ≠ wsR := by decide
@[simp] theorem ws_wsF_ne_wsM2 : wsF ≠ wsM2 := by decide
@[simp] theorem ws_wsF_ne_wsK1 : wsF ≠ wsK1 := by decide
@[simp] theorem ws_wsF_ne_wsK2 : wsF ≠ wsK2 := by decide
@[simp] theorem ws_wsF_ne_wsK3 : wsF ≠ wsK3 := by decide
@[simp] theorem ws_wsF_ne_wsN : wsF ≠ wsN := by decide
@[simp] theorem ws_wsF_ne_wsO : wsF ≠ wsO := by decide
@[simp] theorem ws_wsF_ne_lKb : wsF ≠ lKb := by decide
@[simp] theorem ws_wsF_ne_lFl : wsF ≠ lFl := by decide
@[simp] theorem ws_wsF_ne_lDh : wsF ≠ lDh := by decide
@[simp] theorem ws_wsF_ne_lDt : wsF ≠ lDt := by decide
@[simp] theorem ws_wsF_ne_lDg : wsF ≠ lDg := by decide
@[simp] theorem ws_wsF_ne_lDi : wsF ≠ lDi := by decide
@[simp] theorem ws_wsF_ne_lDo1 : wsF ≠ lDo1 := by decide
@[simp] theorem ws_wsF_ne_lDo2 : wsF ≠ lDo2 := by decide
@[simp] theorem ws_wsF_ne_lRp : wsF ≠ lRp := by decide
@[simp] theorem ws_wsF_ne_lRn : wsF ≠ lRn := by decide
@[simp] theorem ws_wsF_ne_lFle : wsF ≠ lFle := by decide
@[simp] theorem ws_wsF_ne_lDir : wsF ≠ lDir := by decide
@[simp] theorem ws_wsD_ne_wsF : wsD ≠ wsF := by decide
@[simp] theorem ws_wsD_ne_wsH : wsD ≠ wsH := by decide
@[simp] theorem ws_wsD_ne_wsM : wsD ≠ wsM := by decide
@[simp] theorem ws_wsD_ne_wsB : wsD ≠ wsB := by decide
@[simp] theorem ws_wsD_ne_wsL : wsD ≠ wsL := by decide
@[simp] theorem ws_wsD_ne_wsT : wsD ≠ wsT := by decide
@[simp] theorem ws_wsD_ne_wsI : wsD ≠ wsI := by decide
@[simp] theorem ws_wsD_ne_wsC1 : wsD ≠ wsC1 := by decide
@[simp] theorem ws_wsD_ne_wsC2 : wsD ≠ wsC2 := by decide
@[simp] theorem ws_wsD_ne_wsC3 : wsD ≠ wsC3 := by decide
@[simp] theorem ws_wsD_ne_wsR : wsD ≠ wsR := by decide
@[simp] theorem ws_wsD_ne_wsM2 : wsD ≠ wsM2 := by decide
@[simp] theorem ws_wsD_ne_wsK1 : wsD ≠ wsK1 := by decide
@[simp] theorem ws_wsD_ne_wsK2 : wsD ≠ wsK2 := by decide
@[simp] theorem ws_wsD_ne_wsK3 : wsD ≠ wsK3 := by decide
@[simp] theorem ws_wsD_ne_wsN : wsD ≠ wsN := by decide
@[simp] theorem ws_wsD_ne_wsO : wsD ≠ wsO := by decide
@[simp] theorem ws_wsD_ne_lKb : wsD ≠ lKb := by decide
@[simp] theorem ws_wsD_ne_lFl : wsD ≠ lFl := by decide
@[simp] theorem ws_wsD_ne_lDh : wsD ≠ lDh := by decide
@[simp] theorem ws_wsD_ne_lDt : wsD ≠ lDt := by decide
@[simp] theorem ws_wsD_ne_lDg : wsD ≠ lDg := by decide
@[simp] theorem ws_wsD_ne_lDi : wsD ≠ lDi := by decide
@[simp] theorem ws_wsD_ne_lDo1 : wsD ≠ lDo1 := by decide
@[simp] theorem ws_wsD_ne_lDo2 : wsD ≠ lDo2 := by decide
@[simp] theorem ws_wsD_ne_lRp : wsD ≠ lRp := by decide
@[simp] theorem ws_wsD_ne_lRn : wsD ≠ lRn := by decide
@[simp] theorem ws_wsD_ne_lFle : wsD ≠ lFle := by decide
@[simp] theorem ws_wsD_ne_lDir : wsD ≠ lDir := by decide
@[simp] theorem ws_wsH_ne_wsF : wsH ≠ wsF := by decide
@[simp] theorem ws_wsH_ne_wsD : wsH ≠ wsD := by decide
@[simp] theorem ws_wsH_ne_wsM : wsH ≠ wsM := by decide
@[simp] theorem ws_wsH_ne_wsB : wsH ≠ wsB := by decide
@[simp] theorem ws_wsH_ne_wsL : wsH ≠ wsL := by decide
@[simp] theorem ws_wsH_ne_wsT : wsH ≠ wsT := by decide
@[simp] theorem ws_wsH_ne_wsI : wsH ≠ wsI := by decide
@[simp] theorem ws_wsH_ne_wsC1 : wsH ≠ wsC1 := by decide
@[simp] theorem ws_wsH_ne_wsC2 : wsH ≠ wsC2 := by decide
@[simp] theorem ws_wsH_ne_wsC3 : wsH ≠ wsC3 := by decide
@[simp] theorem ws_wsH_ne_wsR : wsH ≠ wsR := by decide
@[simp] theorem ws_wsH_ne_wsM2 : wsH ≠ wsM2 := by decide
@[simp] theorem ws_wsH_ne_wsK1 : wsH ≠ wsK1 := by decide
@[simp] theorem ws_wsH_ne_wsK2 : wsH ≠ wsK2 := by decide
@[simp] theorem ws_wsH_ne_wsK3 : wsH ≠ wsK3 := by decide
@[simp] theorem ws_wsH_ne_wsN : wsH ≠ wsN := by decide
@[simp] theorem ws_wsH_ne_wsO : wsH ≠ wsO := by decide
@[simp] theorem ws_wsH_ne_lKb : wsH ≠ lKb := by decide
@[simp] theorem ws_wsH_ne_lFl : wsH ≠ lFl := by decide
@[simp] theorem ws_wsH_ne_lDh : wsH ≠ lDh := by decide
@[simp] theorem ws_wsH_ne_lDt : wsH ≠ lDt := by decide
@[simp] theorem ws_wsH_ne_lDg : wsH ≠ lDg := by decide
@[simp] theorem ws_wsH_ne_lDi : wsH ≠ lDi := by decide
@[simp] theorem ws_wsH_ne_lDo1 : wsH ≠ lDo1 := by decide
@[simp] theorem ws_wsH_ne_lDo2 : wsH ≠ lDo2 := by decide
@[simp] theorem ws_wsH_ne_lRp : wsH ≠ lRp := by decide
@[simp] theorem ws_wsH_ne_lRn : wsH ≠ lRn := by decide
@[simp] theorem ws_wsH_ne_lFle : wsH ≠ lFle := by decide
@[simp] theorem ws_wsH_ne_lDir : wsH ≠ lDir := by decide
@[simp] theorem ws_wsM_ne_wsF : wsM ≠ wsF := by decide
@[simp] theorem ws_wsM_ne_wsD : wsM ≠ wsD := by decide
@[simp] theorem ws_wsM_ne_wsH : wsM ≠ wsH := by decide
@[simp] theorem ws_wsM_ne_wsB : wsM ≠ wsB := by decide
@[simp] theorem ws_wsM_ne_wsL : wsM ≠ wsL := by decide
@[simp] theorem ws_wsM_ne_wsT : wsM ≠ wsT := by decide
@[simp] theorem ws_wsM_ne_wsI : wsM ≠ wsI := by decide
@[simp] theorem ws_wsM_ne_wsC1 : wsM ≠ wsC1 := by decide
@[simp] theorem ws_wsM_ne_wsC2 : wsM ≠ wsC2 := by decide
@[simp] theorem ws_wsM_ne_wsC3 : wsM ≠ wsC3 := by decide
@[simp] theorem ws_wsM_ne_wsR : wsM ≠ wsR := by decide
@[simp] theorem ws_wsM_ne_wsM2 : wsM ≠ wsM2 := by decide
@[simp] theorem ws_wsM_ne_wsK1 : wsM ≠ wsK1 := by decide
@[simp] theorem ws_wsM_ne_wsK2 : wsM ≠ wsK2 := by decide
@[simp] theorem ws_wsM_ne_wsK3 : wsM ≠ wsK3 := by decide
@[simp] theorem ws_wsM_ne_wsN : wsM ≠ wsN := by decide
@[simp] theorem ws_wsM_ne_wsO : wsM ≠ wsO := by decide
@[simp] theorem ws_wsM_ne_lKb : wsM ≠ lKb := by decide
@[simp] theorem ws_wsM_ne_lFl : wsM ≠ lFl := by decide
@[simp] theorem ws_wsM_ne_lDh : wsM ≠ lDh := by decide
@[simp] theorem ws_wsM_ne_lDt : wsM ≠ lDt := by decide
@[simp] theorem ws_wsM_ne_lDg : wsM ≠ lDg := by decide
@[simp] theorem ws_wsM_ne_lDi : wsM ≠ lDi := by decide
@[simp] theorem ws_wsM_ne_lDo1 : wsM ≠ lDo1 := by decide
@[simp] theorem ws_wsM_ne_lDo2 : wsM ≠ lDo2 := by decide
@[simp] theorem ws_wsM_ne_lRp : wsM ≠ lRp := by decide
@[simp] theorem ws_wsM_ne_lRn : wsM ≠ lRn := by decide
@[simp] theorem ws_wsM_ne_lFle : wsM ≠ lFle := by decide
@[simp] theorem ws_wsM_ne_lDir : wsM ≠ lDir := by decide
@[simp] theorem ws_wsB_ne_wsF : wsB ≠ wsF := by decide
@[simp] theorem ws_wsB_ne_wsD : wsB ≠ wsD := by decide
@[simp] theorem ws_wsB_ne_wsH : wsB ≠ wsH := by decide
@[simp] theorem ws_wsB_ne_wsM : wsB ≠ wsM := by decide
@[simp] theorem ws_wsB_ne_wsL : wsB ≠ wsL := by decide
@[simp] theorem ws_wsB_ne_wsT : wsB ≠ wsT := by decide
@[simp] theorem ws_wsB_ne_wsI : wsB ≠ wsI := by decide
@[simp] theorem ws_wsB_ne_wsC1 : wsB ≠ wsC1 := by decide
@[simp] theorem ws_wsB_ne_wsC2 : wsB ≠ wsC2 := by decide
@[simp] theorem ws_wsB_ne_wsC3 : wsB ≠ wsC3 := by decide
@[simp] theorem ws_wsB_ne_wsR : wsB ≠ wsR := by decide
@[simp] theorem ws_wsB_ne_wsM2 : wsB ≠ wsM2 := by decide
@[simp] theorem ws_wsB_ne_wsK1 : wsB ≠ wsK1 := by decide
@[simp] theorem ws_wsB_ne_wsK2 : wsB ≠ wsK2 := by decide
@[simp] theorem ws_wsB_ne_wsK3 : wsB ≠ wsK3 := by decide
@[simp] theorem ws_wsB_ne_wsN : wsB ≠ wsN := by decide
@[simp] theorem ws_wsB_ne_wsO : wsB ≠ wsO := by decide
@[simp] theorem ws_wsB_ne_lKb : wsB ≠ lKb := by decide
@[simp] theorem ws_wsB_ne_lFl : wsB ≠ lFl := by decide
@[simp] theorem ws_wsB_ne_lDh : wsB ≠ lDh := by decide
@[simp] theorem ws_wsB_ne_lDt : wsB ≠ lDt := by decide
@[simp] theorem ws_wsB_ne_lDg : wsB ≠ lDg := by decide
@[simp] theorem ws_wsB_ne_lDi : wsB ≠ lDi := by decide
@[simp] theorem ws_wsB_ne_lDo1 : wsB ≠ lDo1 := by decide
@[simp] theorem ws_wsB_ne_lDo2 : wsB ≠ lDo2 := by decide
@[simp] theorem ws_wsB_ne_lRp : wsB ≠ lRp := by decide
@[simp] theorem ws_wsB_ne_lRn : wsB ≠ lRn := by decide
@[simp] theorem ws_wsB_ne_lFle : wsB ≠ lFle := by decide
@[simp] theorem ws_wsB_ne_lDir : wsB ≠ lDir := by decide
@[simp] theorem ws_wsL_ne_wsF : wsL ≠ wsF := by decide
@[simp] theorem ws_wsL_ne_wsD : wsL ≠ wsD := by decide
@[simp] theorem ws_wsL_ne_wsH : wsL ≠ wsH := by decide
@[simp] theorem ws_wsL_ne_wsM : wsL ≠ wsM := by decide
@[simp] theorem ws_wsL_ne_wsB : wsL ≠ wsB := by decide
@[simp] theorem ws_wsL_ne_wsT : wsL ≠ wsT := by decide
@[simp] theorem ws_wsL_ne_wsI : wsL ≠ wsI := by decide
@[simp] theorem ws_wsL_ne_wsC1 : wsL ≠ wsC1 := by decide
@[simp] theorem ws_wsL_ne_wsC2 : wsL ≠ wsC2 := by decide
@[simp] theorem ws_wsL_ne_wsC3 : wsL ≠ wsC3 := by decide
@[simp] theorem ws_wsL_ne_wsR : wsL ≠ wsR := by decide
@[simp] theorem ws_wsL_ne_wsM2 : wsL ≠ wsM2 := by decide
@[simp] theorem ws_wsL_ne_wsK1 : wsL ≠ wsK1 := by decide
@[simp] theorem ws_wsL_ne_wsK2 : wsL ≠ wsK2 := by decide
@[simp] theorem ws_wsL_ne_wsK3 : wsL ≠ wsK3 := by decide
@[simp] theorem ws_wsL_ne_wsN : wsL ≠ wsN := by decide
@[simp] theorem ws_wsL_ne_wsO : wsL ≠ wsO := by decide
@[simp] theorem ws_wsL_ne_lKb : wsL ≠ lKb := by decide
@[simp] theorem ws_wsL_ne_lFl : wsL ≠ lFl := by decide
@[simp] theorem ws_wsL_ne_lDh : wsL ≠ lDh := by decide
@[simp] theorem ws_wsL_ne_lDt : wsL ≠ lDt := by decide
@[simp] theorem ws_wsL_ne_lDg : wsL ≠ lDg := by decide
@[simp] theorem ws_wsL_ne_lDi : wsL ≠ lDi := by decide
@[simp] theorem ws_wsL_ne_lDo1 : wsL ≠ lDo1 := by decide
@[simp] theorem ws_wsL_ne_lDo2 : wsL ≠ lDo2 := by decide
@[simp] theorem ws_wsL_ne_lRp : wsL ≠ lRp := by decide
@[simp] theorem ws_wsL_ne_lRn : wsL ≠ lRn := by decide
@[simp] theorem ws_wsL_ne_lFle : wsL ≠ lFle := by decide
@[simp] theorem ws_wsL_ne_lDir : wsL ≠ lDir := by decide
@[simp] theorem ws_wsT_ne_wsF : wsT ≠ wsF := by decide
@[simp] theorem ws_wsT_ne_wsD : wsT ≠ wsD := by decide
@[simp] theorem ws_wsT_ne_wsH : wsT ≠ wsH := by decide
@[simp] theorem ws_wsT_ne_wsM : wsT ≠ wsM := by decide
@[simp] theorem ws_wsT_ne_wsB : wsT ≠ wsB := by decide
@[simp] theorem ws_wsT_ne_wsL : wsT ≠ wsL := by decide
@[simp] theorem ws_wsT_ne_wsI : wsT ≠ wsI := by decide
@[simp] theorem ws_wsT_ne_wsC1 : wsT ≠ wsC1 := by decide
@[simp] theorem ws_wsT_ne_wsC2 : wsT ≠ wsC2 := by decide
@[simp] theorem ws_wsT_ne_wsC3 : wsT ≠ wsC3 := by decide
@[simp] theorem ws_wsT_ne_wsR : wsT ≠ wsR := by decide
@[simp] theorem ws_wsT_ne_wsM2 : wsT ≠ wsM2 := by decide
@[simp] theorem ws_wsT_ne_wsK1 : wsT ≠ wsK1 := by decide
@[simp] theorem ws_wsT_ne_wsK2 : wsT ≠ wsK2 := by decide
@[simp] theorem ws_wsT_ne_wsK3 : wsT ≠ wsK3 := by decide
@[simp] theorem ws_wsT_ne_wsN : wsT ≠ wsN := by decide
@[simp] theorem ws_wsT_ne_wsO : wsT ≠ wsO := by decide
@[simp] theorem ws_wsT_ne_lKb : wsT ≠ lKb := by decide
@[simp] theorem ws_wsT_ne_lFl : wsT ≠ lFl := by decide
@[simp] theorem ws_wsT_ne_lDh : wsT ≠ lDh := by decide
@[simp] theorem ws_wsT_ne_lDt : wsT ≠ lDt := by decide
@[simp] theorem ws_wsT_ne_lDg : wsT ≠ lDg := by decide
@[simp] theorem ws_wsT_ne_lDi : wsT ≠ lDi := by decide
@[simp] theorem ws_wsT_ne_lDo1 : wsT ≠ lDo1 := by decide
@[simp] theorem ws_wsT_ne_lDo2 : wsT ≠ lDo2 := by decide
@[simp] theorem ws_wsT_ne_lRp : wsT ≠ lRp := by decide
@[simp] theorem ws_wsT_ne_lRn : wsT ≠ lRn := by decide
@[simp] theorem ws_wsT_ne_lFle : wsT ≠ lFle := by decide
@[simp] theorem ws_wsT_ne_lDir : wsT ≠ lDir := by decide
@[simp] theorem ws_wsI_ne_wsF : wsI ≠ wsF := by decide
@[simp] theorem ws_wsI_ne_wsD : wsI ≠ wsD := by decide
@[simp] theorem ws_wsI_ne_wsH : wsI ≠ wsH := by decide
@[simp] theorem ws_wsI_ne_wsM : wsI ≠ wsM := by decide
@[simp] theorem ws_wsI_ne_wsB : wsI ≠ wsB := by decide
@[simp] theorem ws_wsI_ne_wsL : wsI ≠ wsL := by decide
@[simp] theorem ws_wsI_ne_wsT : wsI ≠ wsT := by decide
@[simp] theorem ws_wsI_ne_wsC1 : wsI ≠ wsC1 := by decide
@[simp] theorem ws_wsI_ne_wsC2 : wsI ≠ wsC2 := by decide
@[simp] theorem ws_wsI_ne_wsC3 : wsI ≠ wsC3 := by decide
@[simp] theorem ws_wsI_ne_wsR : wsI ≠ wsR := by decide
@[simp] theorem ws_wsI_ne_wsM2 : wsI ≠ wsM2 := by decide
@[simp] theorem ws_wsI_ne_wsK1 : wsI ≠ wsK1 := by decide
@[simp] theorem ws_wsI_ne_wsK2 : wsI ≠ wsK2 := by decide
@[simp] theorem ws_wsI_ne_wsK3 : wsI ≠ wsK3 := by decide
@[simp] theorem ws_wsI_ne_wsN : wsI ≠ wsN := by decide
@[simp] theorem ws_wsI_ne_wsO : wsI ≠ wsO := by decide
@[simp] theorem ws_wsI_ne_lKb : wsI ≠ lKb := by decide
@[simp] theorem ws_wsI_ne_lFl : wsI ≠ lFl := by decide
@[simp] theorem ws_wsI_ne_lDh : wsI ≠ lDh := by decide
@[simp] theorem ws_wsI_ne_lDt : wsI ≠ lDt := by decide
@[simp] theorem ws_wsI_ne_lDg : wsI ≠ lDg := by decide
@[simp] theorem ws_wsI_ne_lDi : wsI ≠ lDi := by decide
@[simp] theorem ws_wsI_ne_lDo1 : wsI ≠ lDo1 := by decide
@[simp] theorem ws_wsI_ne_lDo2 : wsI ≠ lDo2 := by decide
@[simp] theorem ws_wsI_ne_lRp : wsI ≠ lRp := by decide
@[simp] theorem ws_wsI_ne_lRn : wsI ≠ lRn := by decide
@[simp] theorem ws_wsI_ne_lFle : wsI ≠ lFle := by decide
@[simp] theorem ws_wsI_ne_lDir : wsI ≠ lDir := by decide
@[simp] theorem ws_wsC1_ne_wsF : wsC1 ≠ wsF := by decide
@[simp] theorem ws_wsC1_ne_wsD : wsC1 ≠ wsD := by decide
@[simp] theorem ws_wsC1_ne_wsH : wsC1 ≠ wsH := by decide
@[simp] theorem ws_wsC1_ne_wsM : wsC1 ≠ wsM := by decide
@[simp] theorem ws_wsC1_ne_wsB : wsC1 ≠ wsB := by decide
@[simp] theorem ws_wsC1_ne_wsL : wsC1 ≠ wsL := by decide
@[simp] theorem ws_wsC1_ne_wsT : wsC1 ≠ wsT := by decide
@[simp] theorem ws_wsC1_ne_wsI : wsC1 ≠ wsI := by decide
@[simp] theorem ws_wsC1_ne_wsC2 : wsC1 ≠ wsC2 := by decide
@[simp] theorem ws_wsC1_ne_wsC3 : wsC1 ≠ wsC3 := by decide
@[simp] theorem ws_wsC1_ne_wsR : wsC1 ≠ wsR := by decide
@[simp] theorem ws_wsC1_ne_wsM2 : wsC1 ≠ wsM2 := by decide
@[simp] theorem ws_wsC1_ne_wsK1 : wsC1 ≠ wsK1 := by decide
@[simp] theorem ws_wsC1_ne_wsK2 : wsC1 ≠ wsK2 := by decide
@[simp] theorem ws_wsC1_ne_wsK3 : wsC1 ≠ wsK3 := by decide
@[simp] theorem ws_wsC1_ne_wsN : wsC1 ≠ wsN := by decide
@[simp] theorem ws_wsC1_ne_wsO : wsC1 ≠ wsO := by decide
@[simp] theorem ws_wsC1_ne_lKb : wsC1 ≠ lKb := by decide
@[simp] theorem ws_wsC1_ne_lFl : wsC1 ≠ lFl := by decide
@[simp] theorem ws_wsC1_ne_lDh : wsC1 ≠ lDh := by decide
@[simp] theorem ws_wsC1_ne_lDt : wsC1 ≠ lDt := by decide
@[simp] theorem ws_wsC1_ne_lDg : wsC1 ≠ lDg := by decide
@[simp] theorem ws_wsC1_ne_lDi : wsC1 ≠ lDi := by decide
@[simp] theorem ws_wsC1_ne_lDo1 : wsC1 ≠ lDo1 := by decide
@[simp] theorem ws_wsC1_ne_lDo2 : wsC1 ≠ lDo2 := by decide
@[simp] theorem ws_wsC1_ne_lRp : wsC1 ≠ lRp := by decide
@[simp] theorem ws_wsC1_ne_lRn : wsC1 ≠ lRn := by decide
@[simp] theorem ws_wsC1_ne_lFle : wsC1 ≠ lFle := by decide
@[simp] theorem ws_wsC1_ne_lDir : wsC1 ≠ lDir := by decide
@[simp] theorem ws_wsC2_ne_wsF : wsC2 ≠ wsF := by decide
@[simp] theorem ws_wsC2_ne_wsD : wsC2 ≠ wsD := by decide
@[simp] theorem ws_wsC2_ne_wsH : wsC2 ≠ wsH := by decide
@[simp] theorem ws_wsC2_ne_wsM : wsC2 ≠ wsM := by decide
@[simp] theorem ws_wsC2_ne_wsB : wsC2 ≠ wsB := by decide
@[simp] theorem ws_wsC2_ne_wsL : wsC2 ≠ wsL := by decide
@[simp] theorem ws_wsC2_ne_wsT : wsC2 ≠ wsT := by decide
@[simp] theorem ws_wsC2_ne_wsI : wsC2 ≠ wsI := by decide
@[simp] theorem ws_wsC2_ne_wsC1 : wsC2 ≠ wsC1 := by decide
@[simp] theorem ws_wsC2_ne_wsC3 : wsC2 ≠ wsC3 := by decide
@[simp] theorem ws_wsC2_ne_wsR : wsC2 ≠ wsR := by decide
@[simp] theorem ws_wsC2_ne_wsM2 : wsC2 ≠ wsM2 := by decide
@[simp] theorem ws_wsC2_ne_wsK1 : wsC2 ≠ wsK1 := by decide
@[simp] theorem ws_wsC2_ne_wsK2 : wsC2 ≠ wsK2 := by decide
@[simp] theorem ws_wsC2_ne_wsK3 : wsC2 ≠ wsK3 := by decide
@[simp] theorem ws_wsC2_ne_wsN : wsC2 ≠ wsN := by decide
@[simp] theorem ws_wsC2_ne_wsO : wsC2 ≠ wsO := by decide
@[simp] theorem ws_wsC2_ne_lKb : wsC2 ≠ lKb := by decide
@[simp] theorem ws_wsC2_ne_lFl : wsC2 ≠ lFl := by decide
@[simp] theorem ws_wsC2_ne_lDh : wsC2 ≠ lDh := by decide
@[simp] theorem ws_wsC2_ne_lDt : wsC2 ≠ lDt := by decide
@[simp] theorem ws_wsC2_ne_lDg : wsC2 ≠ lDg := by decide
@[simp] theorem ws_wsC2_ne_lDi : wsC2 ≠ lDi := by decide
@[simp] theorem ws_wsC2_ne_lDo1 : wsC2 ≠ lDo1 := by decide
@[simp] theorem ws_wsC2_ne_lDo2 : wsC2 ≠ lDo2 := by decide
@[simp] theorem ws_wsC2_ne_lRp : wsC2 ≠ lRp := by decide
@[simp] theorem ws_wsC2_ne_lRn : wsC2 ≠ lRn := by decide
@[simp] theorem ws_wsC2_ne_lFle : wsC2 ≠ lFle := by decide
@[simp] theorem ws_wsC2_ne_lDir : wsC2 ≠ lDir := by decide
@[simp] theorem ws_wsC3_ne_wsF : wsC3 ≠ wsF := by decide
@[simp] theorem ws_wsC3_ne_wsD : wsC3 ≠ wsD := by decide
@[simp] theorem ws_wsC3_ne_wsH : wsC3 ≠ wsH := by decide
@[simp] theorem ws_wsC3_ne_wsM : wsC3 ≠ wsM := by decide
@[simp] theorem ws_wsC3_ne_wsB : wsC3 ≠ wsB := by decide
@[simp] theorem ws_wsC3_ne_wsL : wsC3 ≠ wsL := by decide
@[simp] theorem ws_wsC3_ne_wsT : wsC3 ≠ wsT := by decide
@[simp] theorem ws_wsC3_ne_wsI : wsC3 ≠ wsI := by decide
@[simp] theorem ws_wsC3_ne_wsC1 : wsC3 ≠ wsC1 := by decide
@[simp] theorem ws_wsC3_ne_wsC2 : wsC3 ≠ wsC2 := by decide
@[simp] theorem ws_wsC3_ne_wsR : wsC3 ≠ wsR := by decide
@[simp] theorem ws_wsC3_ne_wsM2 : wsC3 ≠ wsM2 := by decide
@[simp] theorem ws_wsC3_ne_wsK1 : wsC3 ≠ wsK1 := by decide
@[simp] theorem ws_wsC3_ne_wsK2 : wsC3 ≠ wsK2 := by decide
@[simp] theorem ws_wsC3_ne_wsK3 : wsC3 ≠ wsK3 := by decide
@[simp] theorem ws_wsC3_ne_wsN : wsC3 ≠ wsN := by decide
@[simp] theorem ws_wsC3_ne_wsO : wsC3 ≠ wsO := by decide
@[simp] theorem ws_wsC3_ne_lKb : wsC3 ≠ lKb := by decide
@[simp] theorem ws_wsC3_ne_lFl : wsC3 ≠ lFl := by decide
@[simp] theorem ws_wsC3_ne_lDh : wsC3 ≠ lDh := by decide
@[simp] theorem ws_wsC3_ne_lDt : wsC3 ≠ lDt := by decide
@[simp] theorem ws_wsC3_ne_lDg : wsC3 ≠ lDg := by decide
@[simp] theorem ws_wsC3_ne_lDi : wsC3 ≠ lDi := by decide
@[simp] theorem ws_wsC3_ne_lDo1 : wsC3 ≠ lDo1 := by decide
@[simp] theorem ws_wsC3_ne_lDo2 : wsC3 ≠ lDo2 := by decide
@[simp] theorem ws_wsC3_ne_lRp : wsC3 ≠ lRp := by decide
@[simp] theorem ws_wsC3_ne_lRn : wsC3 ≠ lRn := by decide
@[simp] theorem ws_wsC3_ne_lFle : wsC3 ≠ lFle := by decide
@[simp] theorem ws_wsC3_ne_lDir : wsC3 ≠ lDir := by decide
@[simp] theorem ws_wsR_ne_wsF : wsR ≠ wsF := by decide
@[simp] theorem ws_wsR_ne_wsD : wsR ≠ wsD := by decide
@[simp] theorem ws_wsR_ne_wsH : wsR ≠ wsH := by decide
@[simp] theorem ws_wsR_ne_wsM : wsR ≠ wsM := by decide
@[simp] theorem ws_wsR_ne_wsB : wsR ≠ wsB := by decide
@[simp] theorem ws_wsR_ne_wsL : wsR ≠ wsL := by decide
@[simp] theorem ws_wsR_ne_wsT : wsR ≠ wsT := by decide
@[simp] theorem ws_wsR_ne_wsI : wsR ≠ wsI := by decide
@[simp] theorem ws_wsR_ne_wsC1 : wsR ≠ wsC1 := by decide
@[simp] theorem ws_wsR_ne_wsC2 : wsR ≠ wsC2 := by decide
@[simp] theorem ws_wsR_ne_wsC3 : wsR ≠ wsC3 := by decide
@[simp] theorem ws_wsR_ne_wsM2 : wsR ≠ wsM2 := by decide
@[simp] theorem ws_wsR_ne_wsK1 : wsR ≠ wsK1 := by decide
@[simp] theorem ws_wsR_ne_wsK2 : wsR ≠ wsK2 := by decide
@[simp] theorem ws_wsR_ne_wsK3 : wsR ≠ wsK3 := by decide
@[simp] theorem ws_wsR_ne_wsN : wsR ≠ wsN := by decide
@[simp] theorem ws_wsR_ne_wsO : wsR ≠ wsO := by decide
@[simp] theorem ws_wsR_ne_lKb : wsR ≠ lKb := by decide
@[simp] theorem ws_wsR_ne_lFl : wsR ≠ lFl := by decide
@[simp] theorem ws_wsR_ne_lDh : wsR ≠ lDh := by decide
@[simp] theorem ws_wsR_ne_lDt : wsR ≠ lDt := by decide
@[simp] theorem ws_wsR_ne_lDg : wsR ≠ lDg := by decide
@[simp] theorem ws_wsR_ne_lDi : wsR ≠ lDi := by decide
@[simp] theorem ws_wsR_ne_lDo1 : wsR ≠ lDo1 := by decide
@[simp] theorem ws_wsR_ne_lDo2 : wsR ≠ lDo2 := by decide
@[simp] theorem ws_wsR_ne_lRp : wsR ≠ lRp := by decide
@[simp] theorem ws_wsR_ne_lRn : wsR ≠ lRn := by decide
@[simp] theorem ws_wsR_ne_lFle : wsR ≠ lFle := by decide
@[simp] theorem ws_wsR_ne_lDir : wsR ≠ lDir := by decide
@[simp] theorem ws_wsM2_ne_wsF : wsM2 ≠ wsF := by decide
@[simp] theorem ws_wsM2_ne_wsD : wsM2 ≠ wsD := by decide
@[simp] theorem ws_wsM2_ne_wsH : wsM2 ≠ wsH := by decide
@[simp] theorem ws_wsM2_ne_wsM : wsM2 ≠ wsM := by decide
@[simp] theorem ws_wsM2_ne_wsB : wsM2 ≠ wsB := by decide
@[simp] theorem ws_wsM2_ne_wsL : wsM2 ≠ wsL := by decide
@[simp] theorem ws_wsM2_ne_wsT : wsM2 ≠ wsT := by decide
@[simp] theorem ws_wsM2_ne_wsI : wsM2 ≠ wsI := by decide
@[simp] theorem ws_wsM2_ne_wsC1 : wsM2 ≠ wsC1 := by decide
@[simp] theorem ws_wsM2_ne_wsC2 : wsM2 ≠ wsC2 := by decide
@[simp] theorem ws_wsM2_ne_wsC3 : wsM2 ≠ wsC3 := by decide
@[simp] theorem ws_wsM2_ne_wsR : wsM2 ≠ wsR := by decide
@[simp] theorem ws_wsM2_ne_wsK1 : wsM2 ≠ wsK1 := by decide
@[simp] theorem ws_wsM2_ne_wsK2 : wsM2 ≠ wsK2 := by decide
@[simp] theorem ws_wsM2_ne_wsK3 : wsM2 ≠ wsK3 := by decide
@[simp] theorem ws_wsM2_ne_wsN : wsM2 ≠ wsN := by decide
@[simp] theorem ws_wsM2_ne_wsO : wsM2 ≠ wsO := by decide
@[simp] theorem ws_wsM2_ne_lKb : wsM2 ≠ lKb := by decide
@[simp] theorem ws_wsM2_ne_lFl : wsM2 ≠ lFl := by decide
@[simp] theorem ws_wsM2_ne_lDh : wsM2 ≠ lDh := by decide
@[simp] theorem ws_wsM2_ne_lDt : wsM2 ≠ lDt := by decide
@[simp] theorem ws_wsM2_ne_lDg : wsM2 ≠ lDg := by decide
@[simp] theorem ws_wsM2_ne_lDi : wsM2 ≠ lDi := by decide
@[simp] theorem ws_wsM2_ne_lDo1 : wsM2 ≠ lDo1 := by decide
@[simp] theorem ws_wsM2_ne_lDo2 : wsM2 ≠ lDo2 := by decide
@[simp] theorem ws_wsM2_ne_lRp : wsM2 ≠ lRp := by decide
@[simp] theorem ws_wsM2_ne_lRn : wsM2 ≠ lRn := by decide
@[simp] theorem ws_wsM2_ne_lFle : wsM2 ≠ lFle := by decide
@[simp] theorem ws_wsM2_ne_lDir : wsM2 ≠ lDir := by decide
@[simp] theorem ws_wsK1_ne_wsF : wsK1 ≠ wsF := by decide
@[simp] theorem ws_wsK1_ne_wsD : wsK1 ≠ wsD := by decide
@[simp] theorem ws_wsK1_ne_wsH : wsK1 ≠ wsH := by decide
@[simp] theorem ws_wsK1_ne_wsM : wsK1 ≠ wsM := by decide
@[simp] theorem ws_wsK1_ne_wsB : wsK1 ≠ wsB := by decide
@[simp] theorem ws_wsK1_ne_wsL : wsK1 ≠ wsL := by decide
@[simp] theorem ws_wsK1_ne_wsT : wsK1 ≠ wsT := by decide
@[simp] theorem ws_wsK1_ne_wsI : wsK1 ≠ wsI := by decide
@[simp] theorem ws_wsK1_ne_wsC1 : wsK1 ≠ wsC1 := by decide
@[simp] theorem ws_wsK1_ne_wsC2 : wsK1 ≠ wsC2 := by decide
@[simp] theorem ws_wsK1_ne_wsC3 : wsK1 ≠ wsC3 := by decide
@[simp] theorem ws_wsK1_ne_wsR : wsK1 ≠ wsR := by decide
@[simp] theorem ws_wsK1_ne_wsM2 : wsK1 ≠ wsM2 := by decide
@[simp] theorem ws_wsK1_ne_wsK2 : wsK1 ≠ wsK2 := by decide
@[simp] theorem ws_wsK1_ne_wsK3 : wsK1 ≠ wsK3 := by decide
@[simp] theorem ws_wsK1_ne_wsN : wsK1 ≠ wsN := by decide
@[simp] theorem ws_wsK1_ne_wsO : wsK1 ≠ wsO := by decide
@[simp] theorem ws_wsK1_ne_lKb : wsK1 ≠ lKb := by decide
@[simp] theorem ws_wsK1_ne_lFl : wsK1 ≠ lFl := by decide
@[simp] theorem ws_wsK1_ne_lDh : wsK1 ≠ lDh := by decide
@[simp] theorem ws_wsK1_ne_lDt : wsK1 ≠ lDt := by decide
@[simp] theorem ws_wsK1_ne_lDg : wsK1 ≠ lDg := by decide
@[simp] theorem ws_wsK1_ne_lDi : wsK1 ≠ lDi := by decide
@[simp] theorem ws_wsK1_ne_lDo1 : wsK1 ≠ lDo1 := by decide
@[simp] theorem ws_wsK1_ne_lDo2 : wsK1 ≠ lDo2 := by decide
@[simp] theorem ws_wsK1_ne_lRp : wsK1 ≠ lRp := by decide
@[simp] theorem ws_wsK1_ne_lRn : wsK1 ≠ lRn := by decide
@[simp] theorem ws_wsK1_ne_lFle : wsK1 ≠ lFle := by decide
@[simp] theorem ws_wsK1_ne_lDir : wsK1 ≠ lDir := by decide
@[simp] theorem ws_wsK2_ne_wsF : wsK2 ≠ wsF := by decide
@[simp] theorem ws_wsK2_ne_wsD : wsK2 ≠ wsD := by decide
@[simp] theorem ws_wsK2_ne_wsH : wsK2 ≠ wsH := by decide
@[simp] theorem ws_wsK2_ne_wsM : wsK2 ≠ wsM := by decide
@[simp] theorem ws_wsK2_ne_wsB : wsK2 ≠ wsB := by decide
@[simp] theorem ws_wsK2_ne_wsL : wsK2 ≠ wsL := by decide
@[simp] theorem ws_wsK2_ne_wsT : wsK2 ≠ wsT := by decide
@[simp] theorem ws_wsK2_ne_wsI : wsK2 ≠ wsI := by decide
@[simp] theorem ws_wsK2_ne_wsC1 : wsK2 ≠ wsC1 := by decide
@[simp] theorem ws_wsK2_ne_wsC2 : wsK2 ≠ wsC2 := by decide
@[simp] theorem ws_wsK2_ne_wsC3 : wsK2 ≠ wsC3 := by decide
@[simp] theorem ws_wsK2_ne_wsR : wsK2 ≠ wsR := by decide
@[simp] theorem ws_wsK2_ne_wsM2 : wsK2 ≠ wsM2 := by decide
@[simp] theorem ws_wsK2_ne_wsK1 : wsK2 ≠ wsK1 := by decide
@[simp] theorem ws_wsK2_ne_wsK3 : wsK2 ≠ wsK3 := by decide
@[simp] theorem ws_wsK2_ne_wsN : wsK2 ≠ wsN := by decide
@[simp] theorem ws_wsK2_ne_wsO : wsK2 ≠ wsO := by decide
@[simp] theorem ws_wsK2_ne_lKb : wsK2 ≠ lKb := by decide
@[simp] theorem ws_wsK2_ne_lFl : wsK2 ≠ lFl := by decide
@[simp] theorem ws_wsK2_ne_lDh : wsK2 ≠ lDh := by decide
@[simp] theorem ws_wsK2_ne_lDt : wsK2 ≠ lDt := by decide
@[simp] theorem ws_wsK2_ne_lDg : wsK2 ≠ lDg := by decide
@[simp] theorem ws_wsK2_ne_lDi : wsK2 ≠ lDi := by decide
@[simp] theorem ws_wsK2_ne_lDo1 : wsK2 ≠ lDo1 := by decide
@[simp] theorem ws_wsK2_ne_lDo2 : wsK2 ≠ lDo2 := by decide
@[simp] theorem ws_wsK2_ne_lRp : wsK2 ≠ lRp := by decide
@[simp] theorem ws_wsK2_ne_lRn : wsK2 ≠ lRn := by decide
@[simp] theorem ws_wsK2_ne_lFle : wsK2 ≠ lFle := by decide
@[simp] theorem ws_wsK2_ne_lDir : wsK2 ≠ lDir := by decide
@[simp] theorem ws_wsK3_ne_wsF : wsK3 ≠ wsF := by decide
@[simp] theorem ws_wsK3_ne_wsD : wsK3 ≠ wsD := by decide
@[simp] theorem ws_wsK3_ne_wsH : wsK3 ≠ wsH := by decide
@[simp] theorem ws_wsK3_ne_wsM : wsK3 ≠ wsM := by decide
@[simp] theorem ws_wsK3_ne_wsB : wsK3 ≠ wsB := by decide
@[simp] theorem ws_wsK3_ne_wsL : wsK3 ≠ wsL := by decide
@[simp] theorem ws_wsK3_ne_wsT : wsK3 ≠ wsT := by decide
@[simp] theorem ws_wsK3_ne_wsI : wsK3 ≠ wsI := by decide
@[simp] theorem ws_wsK3_ne_wsC1 : wsK3 ≠ wsC1 := by decide
@[simp] theorem ws_wsK3_ne_wsC2 : wsK3 ≠ wsC2 := by decide
@[simp] theorem ws_wsK3_ne_wsC3 : wsK3 ≠ wsC3 := by decide
@[simp] theorem ws_wsK3_ne_wsR : wsK3 ≠ wsR := by decide
@[simp] theorem ws_wsK3_ne_wsM2 : wsK3 ≠ wsM2 := by decide
@[simp] theorem ws_wsK3_ne_wsK1 : wsK3 ≠ wsK1 := by decide
@[simp] theorem ws_wsK3_ne_wsK2 : wsK3 ≠ wsK2 := by decide
@[simp] theorem ws_wsK3_ne_wsN : wsK3 ≠ wsN := by decide
@[simp] theorem ws_wsK3_ne_wsO : wsK3 ≠ wsO := by decide
@[simp] theorem ws_wsK3_ne_lKb : wsK3 ≠ lKb := by decide
@[simp] theorem ws_wsK3_ne_lFl : wsK3 ≠ lFl := by decide
@[simp] theorem ws_wsK3_ne_lDh : wsK3 ≠ lDh := by decide
@[simp] theorem ws_wsK3_ne_lDt : wsK3 ≠ lDt := by decide
@[simp] theorem ws_wsK3_ne_lDg : wsK3 ≠ lDg := by decide
@[simp] theorem ws_wsK3_ne_lDi : wsK3 ≠ lDi := by decide
@[simp] theorem ws_wsK3_ne_lDo1 : wsK3 ≠ lDo1 := by decide
@[simp] theorem ws_wsK3_ne_lDo2 : wsK3 ≠ lDo2 := by decide
@[simp] theorem ws_wsK3_ne_lRp : wsK3 ≠ lRp := by decide
@[simp] theorem ws_wsK3_ne_lRn : wsK3 ≠ lRn := by decide
@[simp] theorem ws_wsK3_ne_lFle : wsK3 ≠ lFle := by decide
@[simp] theorem ws_wsK3_ne_lDir : wsK3 ≠ lDir := by decide
@[simp] theorem ws_wsN_ne_wsF : wsN ≠ wsF := by decide
@[simp] theorem ws_wsN_ne_wsD : wsN ≠ wsD := by decide
@[simp] theorem ws_wsN_ne_wsH : wsN ≠ wsH := by decide
@[simp] theorem ws_wsN_ne_wsM : wsN ≠ wsM := by decide
@[simp] theorem ws_wsN_ne_wsB : wsN ≠ wsB := by decide
@[simp] theorem ws_wsN_ne_wsL : wsN ≠ wsL := by decide
@[simp] theorem ws_wsN_ne_wsT : wsN ≠ wsT := by decide
@[simp] theorem ws_wsN_ne_wsI : wsN ≠ wsI := by decide
@[simp] theorem ws_wsN_ne_wsC1 : wsN ≠ wsC1 := by decide
@[simp] theorem ws_wsN_ne_wsC2 : wsN ≠ wsC2 := by decide
@[simp] theorem ws_wsN_ne_wsC3 : wsN ≠ wsC3 := by decide
@[simp] theorem ws_wsN_ne_wsR : wsN ≠ wsR := by decide
@[simp] theorem ws_wsN_ne_wsM2 : wsN ≠ wsM2 := by decide
@[simp] theorem ws_wsN_ne_wsK1 : wsN ≠ wsK1 := by decide
@[simp] theorem ws_wsN_ne_wsK2 : wsN ≠ wsK2 := by decide
@[simp] theorem ws_wsN_ne_wsK3 : wsN ≠ wsK3 := by decide
@[simp] theorem ws_wsN_ne_wsO : wsN ≠ wsO := by decide
@[simp] theorem ws_wsN_ne_lKb : wsN ≠ lKb := by decide
@[simp] theorem ws_wsN_ne_lFl : wsN ≠ lFl := by decide
@[simp] theorem ws_wsN_ne_lDh : wsN ≠ lDh := by decide
@[simp] theorem ws_wsN_ne_lDt : wsN ≠ lDt := by decide
@[simp] theorem ws_wsN_ne_lDg : wsN ≠ lDg := by decide
@[simp] theorem ws_wsN_ne_lDi : wsN ≠ lDi := by decide
@[simp] theorem ws_wsN_ne_lDo1 : wsN ≠ lDo1 := by decide
@[simp] theorem ws_wsN_ne_lDo2 : wsN ≠ lDo2 := by decide
@[simp] theorem ws_wsN_ne_lRp : wsN ≠ lRp := by decide
@[simp] theorem ws_wsN_ne_lRn : wsN ≠ lRn := by decide
@[simp] theorem ws_wsN_ne_lFle : wsN ≠ lFle := by decide
@[simp] theorem ws_wsN_ne_lDir : wsN ≠ lDir := by decide
@[simp] theorem ws_wsO_ne_wsF : wsO ≠ wsF := by decide
@[simp] theorem ws_wsO_ne_wsD : wsO ≠ wsD := by decide
@[simp] theorem ws_wsO_ne_wsH : wsO ≠ wsH := by decide
@[simp] theorem ws_wsO_ne_wsM : wsO ≠ wsM := by decide
@[simp] theorem ws_wsO_ne_wsB : wsO ≠ wsB := by decide
@[simp] theorem ws_wsO_ne_wsL : wsO ≠ wsL := by decide
@[simp] theorem ws_wsO_ne_wsT : wsO ≠ wsT := by decide
@[simp] theorem ws_wsO_ne_wsI : wsO ≠ wsI := by decide
@[simp] theorem ws_wsO_ne_wsC1 : wsO ≠ wsC1 := by decide
@[simp] theorem ws_wsO_ne_wsC2 : wsO ≠ wsC2 := by decide
@[simp] theorem ws_wsO_ne_wsC3 : wsO ≠ wsC3 := by decide
@[simp] theorem ws_wsO_ne_wsR : wsO ≠ wsR := by decide
@[simp] theorem ws_wsO_ne_wsM2 : wsO ≠ wsM2 := by decide
@[simp] theorem ws_wsO_ne_wsK1 : wsO ≠ wsK1 := by decide
@[simp] theorem ws_wsO_ne_wsK2 : wsO ≠ wsK2 := by decide
@[simp] theorem ws_wsO_ne_wsK3 : wsO ≠ wsK3 := by decide
@[simp] theorem ws_wsO_ne_wsN : wsO ≠ wsN := by decide
@[simp] theorem ws_wsO_ne_lKb : wsO ≠ lKb := by decide
@[simp] theorem ws_wsO_ne_lFl : wsO ≠ lFl := by decide
@[simp] theorem ws_wsO_ne_lDh : wsO ≠ lDh := by decide
@[simp] theorem ws_wsO_ne_lDt : wsO ≠ lDt := by decide
@[simp] theorem ws_wsO_ne_lDg : wsO ≠ lDg := by decide
@[simp] theorem ws_wsO_ne_lDi : wsO ≠ lDi := by decide
@[simp] theorem ws_wsO_ne_lDo1 : wsO ≠ lDo1 := by decide
@[simp] theorem ws_wsO_ne_lDo2 : wsO ≠ lDo2 := by decide
@[simp] theorem ws_wsO_ne_lRp : wsO ≠ lRp := by decide
@[simp] theorem ws_wsO_ne_lRn : wsO ≠ lRn := by decide
@[simp] theorem ws_wsO_ne_lFle : wsO ≠ lFle := by decide
@[simp] theorem ws_wsO_ne_lDir : wsO ≠ lDir := by decide
@[simp] theorem ws_lKb_ne_wsF : lKb ≠ wsF := by decide
@[simp] theorem ws_lKb_ne_wsD : lKb ≠ wsD := by decide
@[simp] theorem ws_lKb_ne_wsH : lKb ≠ wsH := by decide
@[simp] theorem ws_lKb_ne_wsM : lKb ≠ wsM := by decide
@[simp] theorem ws_lKb_ne_wsB : lKb ≠ wsB := by decide
@[simp] theorem ws_lKb_ne_wsL : lKb ≠ wsL := by decide
@[simp] theorem ws_lKb_ne_wsT : lKb ≠ wsT := by decide
@[simp] theorem ws_lKb_ne_wsI : lKb ≠ wsI := by decide
@[simp] theorem ws_lKb_ne_wsC1 : lKb ≠ wsC1 := by decide
@[simp] theorem ws_lKb_ne_wsC2 : lKb ≠ wsC2 := by decide
@[simp] theorem ws_lKb_ne_wsC3 : lKb ≠ wsC3 := by decide
@[simp] theorem ws_lKb_ne_wsR : lKb ≠ wsR := by decide
@[simp] theorem ws_lKb_ne_wsM2 : lKb ≠ wsM2 := by decide
@[simp] theorem ws_lKb_ne_wsK1 : lKb ≠ wsK1 := by decide
@[simp] theorem ws_lKb_ne_wsK2 : lKb ≠ wsK2 := by decide
@[simp] theorem ws_lKb_ne_wsK3 : lKb ≠ wsK3 := by decide
@[simp] theorem ws_lKb_ne_wsN : lKb ≠ wsN := by decide
@[simp] theorem ws_lKb_ne_wsO : lKb ≠ wsO := by decide
@[simp] theorem ws_lFl_ne_wsF : lFl ≠ wsF := by decide
@[simp] theorem ws_lFl_ne_wsD : lFl ≠ wsD := by decide
@[simp] theorem ws_lFl_ne_wsH : lFl ≠ wsH := by decide
@[simp] theorem ws_lFl_ne_wsM : lFl ≠ wsM := by decide
@[simp] theorem ws_lFl_ne_wsB : lFl ≠ wsB := by decide
@[simp] theorem ws_lFl_ne_wsL : lFl ≠ wsL := by decide
@[simp] theorem ws_lFl_ne_wsT : lFl ≠ wsT := by decide
@[simp] theorem ws_lFl_ne_wsI : lFl ≠ wsI := by decide
@[simp] theorem ws_lFl_ne_wsC1 : lFl ≠ wsC1 := by decide
@[simp] theorem ws_lFl_ne_wsC2 : lFl ≠ wsC2 := by decide
@[simp] theorem ws_lFl_ne_wsC3 : lFl ≠ wsC3 := by decide
@[simp] theorem ws_lFl_ne_wsR : lFl ≠ wsR := by decide
@[simp] theorem ws_lFl_ne_wsM2 : lFl ≠ wsM2 := by decide
@[simp] theorem ws_lFl_ne_wsK1 : lFl ≠ wsK1 := by decide
@[simp] theorem ws_lFl_ne_wsK2 : lFl ≠ wsK2 := by decide
@[simp] theorem ws_lFl_ne_wsK3 : lFl ≠ wsK3 := by decide
@[simp] theorem ws_lFl_ne_wsN : lFl ≠ wsN := by decide
@[simp] theorem ws_lFl_ne_wsO : lFl ≠ wsO := by decide
@[simp] theorem ws_lDh_ne_wsF : lDh ≠ wsF := by decide
@[simp] theorem ws_lDh_ne_wsD : lDh ≠ wsD := by decide
@[simp] theorem ws_lDh_ne_wsH : lDh ≠ wsH := by decide
@[simp] theorem ws_lDh_ne_wsM : lDh ≠ wsM := by decide
@[simp] theorem ws_lDh_ne_wsB : lDh ≠ wsB := by decide
@[simp] theorem ws_lDh_ne_wsL : lDh ≠ wsL := by decide
@[simp] theorem ws_lDh_ne_wsT : lDh ≠ wsT := by decide
@[simp] theorem ws_lDh_ne_wsI : lDh ≠ wsI := by decide
@[simp] theorem ws_lDh_ne_wsC1 : lDh ≠ wsC1 := by decide
@[simp] theorem ws_lDh_ne_wsC2 : lDh ≠ wsC2 := by decide
@[simp] theorem ws_lDh_ne_wsC3 : lDh ≠ wsC3 := by decide
@[simp] theorem ws_lDh_ne_wsR : lDh ≠ wsR := by decide
@[simp] theorem ws_lDh_ne_wsM2 : lDh ≠ wsM2 := by decide
@[simp] theorem ws_lDh_ne_wsK1 : lDh ≠ wsK1 := by decide
@[simp] theorem ws_lDh_ne_wsK2 : lDh ≠ wsK2 := by decide
@[simp] theorem ws_lDh_ne_wsK3 : lDh ≠ wsK3 := by decide
@[simp] theorem ws_lDh_ne_wsN : lDh ≠ wsN := by decide
@[simp] theorem ws_lDh_ne_wsO : lDh ≠ wsO := by decide
@[simp] theorem ws_lDt_ne_wsF : lDt ≠ wsF := by decide
@[simp] theorem ws_lDt_ne_wsD : lDt ≠ wsD := by decide
@[simp] theorem ws_lDt_ne_wsH : lDt ≠ wsH := by decide
@[simp] theorem ws_lDt_ne_wsM : lDt ≠ wsM := by decide
@[simp] theorem ws_lDt_ne_wsB : lDt ≠ wsB := by decide
@[simp] theorem ws_lDt_ne_wsL : lDt ≠ wsL := by decide
@[simp] theorem ws_lDt_ne_wsT : lDt ≠ wsT := by decide
@[simp] theorem ws_lDt_ne_wsI : lDt ≠ wsI := by decide
@[simp] theorem ws_lDt_ne_wsC1 : lDt ≠ wsC1 := by decide
@[simp] theorem ws_lDt_ne_wsC2 : lDt ≠ wsC2 := by decide
@[simp] theorem ws_lDt_ne_wsC3 : lDt ≠ wsC3 := by decide
@[simp] theorem ws_lDt_ne_wsR : lDt ≠ wsR := by decide
@[simp] theorem ws_lDt_ne_wsM2 : lDt ≠ wsM2 := by decide
@[simp] theorem ws_lDt_ne_wsK1 : lDt ≠ wsK1 := by decide
@[simp] theorem ws_lDt_ne_wsK2 : lDt ≠ wsK2 := by decide
@[simp] theorem ws_lDt_ne_wsK3 : lDt ≠ wsK3 := by decide
@[simp] theorem ws_lDt_ne_wsN : lDt ≠ wsN := by decide
@[simp] theorem ws_lDt_ne_wsO : lDt ≠ wsO := by decide
@[simp] theorem ws_lDg_ne_wsF : lDg ≠ wsF := by decide
@[simp] theorem ws_lDg_ne_wsD : lDg ≠ wsD := by decide
@[simp] theorem ws_lDg_ne_wsH : lDg ≠ wsH := by decide
@[simp] theorem ws_lDg_ne_wsM : lDg ≠ wsM := by decide
@[simp] theorem ws_lDg_ne_wsB : lDg ≠ wsB := by decide
@[simp] theorem ws_lDg_ne_wsL : lDg ≠ wsL := by decide
@[simp] theorem ws_lDg_ne_wsT : lDg ≠ wsT := by decide
@[simp] theorem ws_lDg_ne_wsI : lDg ≠ wsI := by decide
@[simp] theorem ws_lDg_ne_wsC1 : lDg ≠ wsC1 := by decide
@[simp] theorem ws_lDg_ne_wsC2 : lDg ≠ wsC2 := by decide
@[simp] theorem ws_lDg_ne_wsC3 : lDg ≠ wsC3 := by decide
@[simp] theorem ws_lDg_ne_wsR : lDg ≠ wsR := by decide
@[simp] theorem ws_lDg_ne_wsM2 : lDg ≠ wsM2 := by decide
@[simp] theorem ws_lDg_ne_wsK1 : lDg ≠ wsK1 := by decide
@[simp] theorem ws_lDg_ne_wsK2 : lDg ≠ wsK2 := by decide
@[simp] theorem ws_lDg_ne_wsK3 : lDg ≠ wsK3 := by decide
@[simp] theorem ws_lDg_ne_wsN : lDg ≠ wsN := by decide
@[simp] theorem ws_lDg_ne_wsO : lDg ≠ wsO := by decide
@[simp] theorem ws_lDi_ne_wsF : lDi ≠ wsF := by decide
@[simp] theorem ws_lDi_ne_wsD : lDi ≠ wsD := by decide
@[simp] theorem ws_lDi_ne_wsH : lDi ≠ wsH := by decide
@[simp] theorem ws_lDi_ne_wsM : lDi ≠ wsM := by decide
@[simp] theorem ws_lDi_ne_wsB : lDi ≠ wsB := by decide
@[simp] theorem ws_lDi_ne_wsL : lDi ≠ wsL := by decide
@[simp] theorem ws_lDi_ne_wsT : lDi ≠ wsT := by decide
@[simp] theorem ws_lDi_ne_wsI : lDi ≠ wsI := by decide
@[simp] theorem ws_lDi_ne_wsC1 : lDi ≠ wsC1 := by decide
@[simp] theorem ws_lDi_ne_wsC2 : lDi ≠ wsC2 := by decide
@[simp] theorem ws_lDi_ne_wsC3 : lDi ≠ wsC3 := by decide
@[simp] theorem ws_lDi_ne_wsR : lDi ≠ wsR := by decide
@[simp] theorem ws_lDi_ne_wsM2 : lDi ≠ wsM2 := by decide
@[simp] theorem ws_lDi_ne_wsK1 : lDi ≠ wsK1 := by decide
@[simp] theorem ws_lDi_ne_wsK2 : lDi ≠ wsK2 := by decide
@[simp] theorem ws_lDi_ne_wsK3 : lDi ≠ wsK3 := by decide
@[simp] theorem ws_lDi_ne_wsN : lDi ≠ wsN := by decide
@[simp] theorem ws_lDi_ne_wsO : lDi ≠ wsO := by decide
@[simp] theorem ws_lDo1_ne_wsF : lDo1 ≠ wsF := by decide
@[simp] theorem ws_lDo1_ne_wsD : lDo1 ≠ wsD := by decide
@[simp] theorem ws_lDo1_ne_wsH : lDo1 ≠ wsH := by decide
@[simp] theorem ws_lDo1_ne_wsM : lDo1 ≠ wsM := by decide
@[simp] theorem ws_lDo1_ne_wsB : lDo1 ≠ wsB := by decide
@[simp] theorem ws_lDo1_ne_wsL : lDo1 ≠ wsL := by decide
@[simp] theorem ws_lDo1_ne_wsT : lDo1 ≠ wsT := by decide
@[simp] theorem ws_lDo1_ne_wsI : lDo1 ≠ wsI := by decide
@[simp] theorem ws_lDo1_ne_wsC1 : lDo1 ≠ wsC1 := by decide
@[simp] theorem ws_lDo1_ne_wsC2 : lDo1 ≠ wsC2 := by decide
@[simp] theorem ws_lDo1_ne_wsC3 : lDo1 ≠ wsC3 := by decide
@[simp] theorem ws_lDo1_ne_wsR : lDo1 ≠ wsR := by decide
@[simp] theorem ws_lDo1_ne_wsM2 : lDo1 ≠ wsM2 := by decide
@[simp] theorem ws_lDo1_ne_wsK1 : lDo1 ≠ wsK1 := by decide
@[simp] theorem ws_lDo1_ne_wsK2 : lDo1 ≠ wsK2 := by decide
@[simp] theorem ws_lDo1_ne_wsK3 : lDo1 ≠ wsK3 := by decide
@[simp] theorem ws_lDo1_ne_wsN : lDo1 ≠ wsN := by decide
@[simp] theorem ws_lDo1_ne_wsO : lDo1 ≠ wsO := by decide
@[simp] theorem ws_lDo2_ne_wsF : lDo2 ≠ wsF := by decide
@[simp] theorem ws_lDo2_ne_wsD : lDo2 ≠ wsD := by decide
@[simp] theorem ws_lDo2_ne_wsH : lDo2 ≠ wsH := by decide
@[simp] theorem ws_lDo2_ne_wsM : lDo2 ≠ wsM := by decide
@[simp] theorem ws_lDo2_ne_wsB : lDo2 ≠ wsB := by decide
@[simp] theorem ws_lDo2_ne_wsL : lDo2 ≠ wsL := by decide
@[simp] theorem ws_lDo2_ne_wsT : lDo2 ≠ wsT := by decide
@[simp] theorem ws_lDo2_ne_wsI : lDo2 ≠ wsI := by decide
@[simp] theorem ws_lDo2_ne_wsC1 : lDo2 ≠ wsC1 := by decide
@[simp] theorem ws_lDo2_ne_wsC2 : lDo2 ≠ wsC2 := by decide
@[simp] theorem ws_lDo2_ne_wsC3 : lDo2 ≠ wsC3 := by decide
@[simp] theorem ws_lDo2_ne_wsR : lDo2 ≠ wsR := by decide
@[simp] theorem ws_lDo2_ne_wsM2 : lDo2 ≠ wsM2 := by decide
@[simp] theorem ws_lDo2_ne_wsK1 : lDo2 ≠ wsK1 := by decide
@[simp] theorem ws_lDo2_ne_wsK2 : lDo2 ≠ wsK2 := by decide
@[simp] theorem ws_lDo2_ne_wsK3 : lDo2 ≠ wsK3 := by decide
@[simp] theorem ws_lDo2_ne_wsN : lDo2 ≠ wsN := by decide
@[simp] theorem ws_lDo2_ne_wsO : lDo2 ≠ wsO := by decide
@[simp] theorem ws_lRp_ne_wsF : lRp ≠ wsF := by decide
@[simp] theorem ws_lRp_ne_wsD : lRp ≠ wsD := by decide
@[simp] theorem ws_lRp_ne_wsH : lRp ≠ wsH := by decide
@[simp] theorem ws_lRp_ne_wsM : lRp ≠ wsM := by decide
@[simp] theorem ws_lRp_ne_wsB : lRp ≠ wsB := by decide
@[simp] theorem ws_lRp_ne_wsL : lRp ≠ wsL := by decide
@[simp] theorem ws_lRp_ne_wsT : lRp ≠ wsT := by decide
@[simp] theorem ws_lRp_ne_wsI : lRp ≠ wsI := by decide
@[simp] theorem ws_lRp_ne_wsC1 : lRp ≠ wsC1 := by decide
@[simp] theorem ws_lRp_ne_wsC2 : lRp ≠ wsC2 := by decide
@[simp] theorem ws_lRp_ne_wsC3 : lRp ≠ wsC3 := by decide
@[simp] theorem ws_lRp_ne_wsR : lRp ≠ wsR := by decide
@[simp] theorem ws_lRp_ne_wsM2 : lRp ≠ wsM2 := by decide
@[simp] theorem ws_lRp_ne_wsK1 : lRp ≠ wsK1 := by decide
@[simp] theorem ws_lRp_ne_wsK2 : lRp ≠ wsK2 := by decide
@[simp] theorem ws_lRp_ne_wsK3 : lRp ≠ wsK3 := by decide
@[simp] theorem ws_lRp_ne_wsN : lRp ≠ wsN := by decide
@[simp] theorem ws_lRp_ne_wsO : lRp ≠ wsO := by decide
@[simp] theorem ws_lRn_ne_wsF : lRn ≠ wsF := by decide
@[simp] theorem ws_lRn_ne_wsD : lRn ≠ wsD := by decide
@[simp] theorem ws_lRn_ne_wsH : lRn ≠ wsH := by decide
@[simp] theorem ws_lRn_ne_wsM : lRn ≠ wsM := by decide
@[simp] theorem ws_lRn_ne_wsB : lRn ≠ wsB := by decide
@[simp] theorem ws_lRn_ne_wsL : lRn ≠ wsL := by decide
@[simp] theorem ws_lRn_ne_wsT : lRn ≠ wsT := by decide
@[simp] theorem ws_lRn_ne_wsI : lRn ≠ wsI := by decide
@[simp] theorem ws_lRn_ne_wsC1 : lRn ≠ wsC1 := by decide
@[simp] theorem ws_lRn_ne_wsC2 : lRn ≠ wsC2 := by decide
@[simp] theorem ws_lRn_ne_wsC3 : lRn ≠ wsC3 := by decide
@[simp] theorem ws_lRn_ne_wsR : lRn ≠ wsR := by decide
@[simp] theorem ws_lRn_ne_wsM2 : lRn ≠ wsM2 := by decide
@[simp] theorem ws_lRn_ne_wsK1 : lRn ≠ wsK1 := by decide
@[simp] theorem ws_lRn_ne_wsK2 : lRn ≠ wsK2 := by decide
@[simp] theorem ws_lRn_ne_wsK3 : lRn ≠ wsK3 := by decide
@[simp] theorem ws_lRn_ne_wsN : lRn ≠ wsN := by decide
@[simp] theorem ws_lRn_ne_wsO : lRn ≠ wsO := by decide
@[simp] theorem ws_lFle_ne_wsF : lFle ≠ wsF := by decide
@[simp] theorem ws_lFle_ne_wsD : lFle ≠ wsD := by decide
@[simp] theorem ws_lFle_ne_wsH : lFle ≠ wsH := by decide
@[simp] theorem ws_lFle_ne_wsM : lFle ≠ wsM := by decide
@[simp] theorem ws_lFle_ne_wsB : lFle ≠ wsB := by decide
@[simp] theorem ws_lFle_ne_wsL : lFle ≠ wsL := by decide
@[simp] theorem ws_lFle_ne_wsT : lFle ≠ wsT := by decide
@[simp] theorem ws_lFle_ne_wsI : lFle ≠ wsI := by decide
@[simp] theorem ws_lFle_ne_wsC1 : lFle ≠ wsC1 := by decide
@[simp] theorem ws_lFle_ne_wsC2 : lFle ≠ wsC2 := by decide
@[simp] theorem ws_lFle_ne_wsC3 : lFle ≠ wsC3 := by decide
@[simp] theorem ws_lFle_ne_wsR : lFle ≠ wsR := by decide
@[simp] theorem ws_lFle_ne_wsM2 : lFle ≠ wsM2 := by decide
@[simp] theorem ws_lFle_ne_wsK1 : lFle ≠ wsK1 := by decide
@[simp] theorem ws_lFle_ne_wsK2 : lFle ≠ wsK2 := by decide
@[simp] theorem ws_lFle_ne_wsK3 : lFle ≠ wsK3 := by decide
@[simp] theorem ws_lFle_ne_wsN : lFle ≠ wsN := by decide
@[simp] theorem ws_lFle_ne_wsO : lFle ≠ wsO := by decide
@[simp] theorem ws_lDir_ne_wsF : lDir ≠ wsF := by decide
@[simp] theorem ws_lDir_ne_wsD : lDir ≠ wsD := by decide
@[simp] theorem ws_lDir_ne_wsH : lDir ≠ wsH := by decide
@[simp] theorem ws_lDir_ne_wsM : lDir ≠ wsM := by decide
@[simp] theorem ws_lDir_ne_wsB : lDir ≠ wsB := by decide
@[simp] theorem ws_lDir_ne_wsL : lDir ≠ wsL := by decide
@[simp] theorem ws_lDir_ne_wsT : lDir ≠ wsT := by decide
@[simp] theorem ws_lDir_ne_wsI : lDir ≠ wsI := by decide
@[simp] theorem ws_lDir_ne_wsC1 : lDir ≠ wsC1 := by decide
@[simp] theorem ws_lDir_ne_wsC2 : lDir ≠ wsC2 := by decide
@[simp] theorem ws_lDir_ne_wsC3 : lDir ≠ wsC3 := by decide
@[simp] theorem ws_lDir_ne_wsR : lDir ≠ wsR := by decide
@[simp] theorem ws_lDir_ne_wsM2 : lDir ≠ wsM2 := by decide
@[simp] theorem ws_lDir_ne_wsK1 : lDir ≠ wsK1 := by decide
@[simp] theorem ws_lDir_ne_wsK2 : lDir ≠ wsK2 := by decide
@[simp] theorem ws_lDir_ne_wsK3 : lDir ≠ wsK3 := by decide
@[simp] theorem ws_lDir_ne_wsN : lDir ≠ wsN := by decide
@[simp] theorem ws_lDir_ne_wsO : lDir ≠ wsO := by decide

def wsParams : List MlS := [wsF, wsD, wsH, wsM]
def wsLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lDo1, lDo2, lRp, lRn, wsB, wsL, wsT, wsI, wsC1, wsC2, wsC3, wsR,
  wsM2, wsK1, wsK2, wsK3, wsN, wsO]

def wsRet (C : Ctx) (er em : ExpHOL 64) : ProgHOL 64 :=
  allocP C wsO (.const 16) (.seq (.store (vv wsO) er) (.seq (.store (.op .add [vv wsO, .const 8]) em)
    (.return (vv wsO))))

def wsIns (C : Ctx) : ProgHOL 64 := mlInsP C wsN (vv wsH) (vv wsD) (vv wsR) (vv wsM2) (wsRet C (vv wsR) (vv wsN))

def wsCall (k : MlS) (eD eH eM : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.local, k), none)) fWs [.op .sub [vv wsF, .const 1], eD, eH, eM])
  (.seq (.assign .local wsR (.load .one (vv k))) (.seq (.assign .local wsM2 (.load .one (.op .add [vv k, .const 8])))
    rest))

def wsArm2 (C : Ctx) : ProgHOL 64 :=
  wsCall wsK1 (vv wsD) (vv wsC1) (vv wsM)
    (.ite (vv wsR) (wsCall wsK2 (vv wsD) (vv wsC2) (vv wsM2) (wsIns C)) (wsIns C))

def wsArm3 (C : Ctx) : ProgHOL 64 :=
  wsCall wsK1 (vv wsD) (vv wsC1) (vv wsM)
    (.ite (vv wsR) (wsCall wsK2 (vv wsD) (vv wsC2) (vv wsM2)
      (.ite (vv wsR) (wsCall wsK3 (vv wsD) (vv wsC3) (vv wsM2) (wsIns C)) (wsIns C))) (wsIns C))

def wsFvarK (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .lower (vv wsI) (vv wsD)) (wsCall wsK1 (vv wsI) (vv wsT) (vv wsM) (wsIns C))
    (.seq (.assign .local wsR (.const 0)) (.seq (.assign .local wsM2 (vv wsM)) (wsIns C)))

def wsFvar (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local wsT (.load .one (vv lRp)))
  (.ite (.cmp .equal (vv lRn) (.const 1)) (.seq (.assign .local wsI (.const 0)) (wsFvarK C))
    (.ite (.cmp .equal (vv lRn) (.const 2))
      (.seq (.assign .local wsI (.load .one (.op .add [vv lRp, .const 8]))) (wsFvarK C)) hang))

def wsCore (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .equal (vv wsF) (.const 0)) hang
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv wsH)) (.seq (storeDerived 9 10)
  (.seq (.assign .local wsB (.op .and [.shift .lsr (vv lDo1) (.const 1), .const 32767]))
  (.ite (.cmp .equal (vv wsB) (.const 0)) (wsRet C (.const 1) (vv wsM))
  (.seq (.call (some (some (.local, wsL), none)) fMl [vv wsM, vv wsH, vv wsD])
  (.ite (.cmp .notEqual (vv wsL) (.const 0)) (wsRet C (.op .sub [vv wsL, .const 1]) (vv wsM))
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv wsH)) (.seq eViewP
  (.ite (.cmp .equal (vv lDg) (.const 1)) (wsFvar C)
  (.ite (.cmp .equal (vv lDg) (.const 4))
    (.seq (.assign .local wsC1 (.load .one (vv lRp)))
      (.seq (.assign .local wsC2 (.load .one (.op .add [vv lRp, .const 8]))) (wsArm2 C)))
  (.ite (.cmp .equal (vv lDg) (.const 5))
    (.seq (.assign .local wsC1 (.load .one (vv lRp)))
      (.seq (.assign .local wsC2 (.load .one (.op .add [vv lRp, .const 8]))) (wsArm2 C)))
  (.ite (.cmp .equal (vv lDg) (.const 6))
    (.seq (.assign .local wsC1 (.load .one (vv lRp)))
      (.seq (.assign .local wsC2 (.load .one (.op .add [vv lRp, .const 8]))) (wsArm2 C)))
  (.ite (.cmp .equal (vv lDg) (.const 7))
    (.seq (.assign .local wsC1 (.load .one (vv lRp)))
      (.seq (.assign .local wsC2 (.load .one (.op .add [vv lRp, .const 8])))
        (.seq (.assign .local wsC3 (.load .one (.op .add [vv lRp, .const 16]))) (wsArm3 C))))
  (.ite (.cmp .equal (vv lDg) (.const 9))
    (.seq (.assign .local wsC1 (.load .one (.op .add [vv lRp, .const 8]))) (wsCall wsK1 (vv wsD) (vv wsC1) (vv wsM) (wsIns C)))
    (.seq (.assign .local wsR (.const 1)) (.seq (.assign .local wsM2 (vv wsM)) (wsIns C)))))))))))))))))))

def wsBody (C : Ctx) : ProgHOL 64 := prologue wsLocals (wsCore C)

structure WsCodes (C : Ctx) : Prop where
  ml : C.code.lookup fMl = some (mlParams.map (fun p => (p, ShapeHOL.one)), mlBody, .one)
  self : C.code.lookup fWs = some (wsParams.map (fun p => (p, ShapeHOL.one)), wsBody C, .one)

section
variable {σ : Type}

/-- The answer and memo as a fresh pair block, nothing else changes. -/
def PostWs (C : Ctx) (s : AState) (rm : Bool × Std.HashMap (EIdx × Nat) Bool) (w : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  s' = s ∧ ∃ H' o pm, C.H <+: H' ∧ w = cellA C o ∧ H'[o]? = some (boolW rm.1) ∧ H'[o + 1]? = some pm ∧
    WsRep C H' pm rm.2 ∧ SR (ctxH C H') s st

theorem postWs_locals (C : Ctx) (s : AState) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostWs C s a w s' st → PostWs C s a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, H', o, pm, h2, h3, h4, h5, h6, h7⟩ => ⟨h1, H', o, pm, h2, h3, h4, h5, h6, sr_of_eq h7 rfl rfl rfl rfl⟩

theorem specR_wsRetI {C : Ctx} (hok : CtxOK C) {H0 H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem}
    {D : List MlS} (er em : ExpHOL 64) (r : Bool) (pm : BitVec 64) (memo : Std.HashMap (EIdx × Nat) Bool)
    (hD : wsO ∈ D) (her : ∀ w, sev ((wsO, w) :: Γ) er = some (boolW r)) (hem : ∀ w, sev ((wsO, w) :: Γ) em = some pm)
    (hrep : WsRep C H pm memo) (h0 : H0 <+: H) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (wsRet C er em) s (pure (r, memo)) (PostWs (ctxH C H0) s) := by
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hlay := hok.heapLay
  refine specR_allocI (C := ctxH C H) wsO (.const 16) 2 (by omega) hD (fun _ => rfl) (fun H1 ws hp1 hws hroom => ?_)
  have hp1' : H <+: H1 := hp1
  have hL := hp1'.length_le
  change SpecR (Inv (ctxH C (H1 ++ ws)) s ((wsO, cellA C H1.length) :: Γ) _ _) _ _ _ _
  refine specR_heapStoreI (ctxOK_H hok _) (vv wsO) er H1.length (by show _ < (H1 ++ ws).length; simp; omega)
    (boolW r) (by simp <;> rfl) (her _) ?_
  change SpecR (Inv (ctxH C ((H1 ++ ws).set H1.length (boolW r))) _ _ _ _) _ _ _ _
  refine specR_heapStoreI (ctxOK_H hok _) (.op .add [vv wsO, .const 8]) em (H1.length + 1)
    (by show _ < ((H1 ++ ws).set _ _).length; simp; omega) pm (by simp +decide [sev]; exact cellA_add8 C _) (hem _) ?_
  have g0 : (((H1 ++ ws).set H1.length (boolW r)).set (H1.length + 1) pm)[H1.length]? = some (boolW r) := by
    simp [List.getElem?_set, hws]
  have g1 : (((H1 ++ ws).set H1.length (boolW r)).set (H1.length + 1) pm)[H1.length + 1]? = some pm := by
    simp [List.getElem?_set, hws]
  have hpre : H <+: ((H1 ++ ws).set H1.length (boolW r)).set (H1.length + 1) pm :=
    prefix_set_ge (prefix_set_ge (hp1'.trans (List.prefix_append _ _)) _ (by omega) _) _ (by omega) _
  exact specR_returnI _ (cellA C H1.length) (by simp +decide [Env.get] <;> rfl)
    (fun t ht => ⟨rfl, _, H1.length, pm, h0.trans hpre, rfl, g0, g1, wsRep_toH (wsRep_mono hpre hrep), sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem specR_wsInsI {C : Ctx} (hok : CtxOK C) {H0 H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem}
    {D : List MlS} (h : EIdx) (d : Nat) (hd : d < 2 ^ 63) (r : Bool) (pm : BitVec 64)
    (memo : Std.HashMap (EIdx × Nat) Bool) (hD : wsN ∈ D ∧ wsO ∈ D) (hH : Γ.get wsH = some (Enc.idxW h))
    (hDv : Γ.get wsD = some (BitVec.ofNat 64 d)) (hR : Γ.get wsR = some (boolW r)) (hM : Γ.get wsM2 = some pm)
    (hrep : WsRep C H pm memo) (h0 : H0 <+: H) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (wsIns C) s (pure (r, memo.insert (h, d) r)) (PostWs (ctxH C H0) s) := by
  obtain ⟨xs, hm, he⟩ := hrep
  unfold wsIns
  refine specR_mlInsI hok wsN (vv wsH) (vv wsD) (vv wsR) (vv wsM2) (Enc.idxW h) (BitVec.ofNat 64 d) pm r xs hD.1
    (fun w => by simp [Env.get, hH]) (fun w => by simp [Env.get, hDv]) (fun w => by simp [Env.get, hR])
    (fun w => by simp [Env.get, hM]) hm (fun H' o hp' hm' => ?_)
  exact specR_wsRetI hok (vv wsR) (vv wsN) r (cellA C o) (memo.insert (h, d) r) hD.2
    (fun w => by simp [Env.get, hR]) (fun w => by simp [Env.get]) (wsRep_insert (p := pm) he h d hd r hm') (h0.trans hp')

theorem ws_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ wsLocals → (ctxEnv C ++ wsParams.zip vals).get x = none :=
  Knot.params_none C wsLocals wsParams vals (by decide) (by decide)

/-- The walk's spec at fuel `n`, for every argument (the induction hypothesis the arms use). -/
def WsRec (C : Ctx) (n : Nat) : Prop :=
  ∀ (d : Nat) (h : EIdx) (memo : Std.HashMap (EIdx × Nat) Bool) (H : List (BitVec 64)) (s : AState) (pm : BitVec 64),
    C.H <+: H → d < 2 ^ 63 → WsRep C H pm memo →
    SpecR (σ := σ) (Pre (ctxH C H) s (wsParams.zip [BitVec.ofNat 64 (n + 1), BitVec.ofNat 64 d, Enc.idxW h, pm]))
      (wsBody C) s (wscopedBGo memo n d h) (PostWs (ctxH C H) s)

/-- One recursive call, then the pair block read back. -/
theorem specR_wsCallI {α : Type} {C : Ctx} (hok : CtxOK C) (hc : WsCodes C) {n : Nat} (ih : WsRec (σ := σ) C n)
    {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {k : Bool × Std.HashMap (EIdx × Nat) Bool → AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (eD eH eM : ExpHOL 64) (d : Nat) (h : EIdx) (pm : BitVec 64) (memo : Std.HashMap (EIdx × Nat) Bool)
    (hx : x ∈ D ∧ wsR ∈ D ∧ wsM2 ∈ D) (hxn : x ≠ wsR ∧ wsM2 ≠ x) (hp : C.H <+: H) (hd : d < 2 ^ 63) (hrep : WsRep C H pm memo)
    (hF : Γ.get wsF = some (BitVec.ofNat 64 (n + 1 + 1))) (heD : sev Γ eD = some (BitVec.ofNat 64 d))
    (heH : sev Γ eH = some (Enc.idxW h)) (heM : sev Γ eM = some pm)
    (hk : ∀ (rm : Bool × Std.HashMap (EIdx × Nat) Bool) H' pm' w, H <+: H' → WsRep C H' pm' rm.2 →
      SpecR (Inv (ctxH C H') s ((wsM2, pm') :: (wsR, boolW rm.1) :: (x, w) :: Γ) [] D) rest s (k rm) R) :
    SpecR (Inv (ctxH C H) s Γ M D) (wsCall x eD eH eM rest) s (wscopedBGo memo n d h >>= k) R := by
  unfold wsCall
  refine specR_callNIH (C := ctxH C H) x fWs wsParams [.op .sub [vv wsF, .const 1], eD, eH, eM] (wsBody C)
    [BitVec.ofNat 64 (n + 1), BitVec.ofNat 64 d, Enc.idxW h, pm] (by decide) rfl hx.1 hc.self
    ⟨by simp [sev, hF]; exact Ex.ofNat_succ_sub_one _, heD, heH, heM, trivial⟩
    (PostWs (ctxH C H) s)
    (fun rm w s' H' => s' = s ∧ ∃ o pm', w = cellA C o ∧ H'[o]? = some (boolW rm.1) ∧ H'[o + 1]? = some pm' ∧
      WsRep C H' pm' rm.2)
    (fun rm w s' st ⟨h1, H', o, pm', hp', hw, h0, h1', hrep', hsr⟩ =>
      ⟨H', hp', ⟨h1, o, pm', hw, h0, h1', wsRep_ofH hrep'⟩, by subst h1; exact hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu wsParams _ rfl hlk) (ih d h memo H s pm hp hd hrep))
    (fun rm w s' H' hp' ⟨hs', o, pm', hw, h0, h1', hrep'⟩ => ?_)
  subst hs' hw
  refine UD.specR_heapLoadI' (C := ctxH C H') wsR (vv x) o (boolW rm.1) h0 hx.2.1 (by simp [Env.get]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H') wsM2 (.op .add [vv x, .const 8]) (o + 1) pm' h1' hx.2.2
    (by simp [sev, Env.get, hxn.1]; exact (cellA_add8 C o : _)) ?_
  exact hk rm H' pm' (cellA C o) hp' hrep'


end

end ConPanqueque.T.WC
