import ConPanqueque.T.Core.InferArms
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# The ∀ arm: `inferPis` and its pieces

`inferPisOut`: the outward `imax` fold over the stacked binder sorts (a heap block), innermost first.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def poS := ofString "pon_s"
def poN := ofString "pon_n"
def poV := ofString "pon_v"
def poJ := ofString "pon_j"
def poA := ofString "pon_a"
def poW := ofString "pon_w"
def poR := ofString "pon_r"
def fPo := ofString "inferPisOut"

@[simp] theorem po_poS_ne_poN : poS ≠ poN := by decide
@[simp] theorem po_poS_ne_poV : poS ≠ poV := by decide
@[simp] theorem po_poS_ne_poJ : poS ≠ poJ := by decide
@[simp] theorem po_poS_ne_poA : poS ≠ poA := by decide
@[simp] theorem po_poS_ne_poW : poS ≠ poW := by decide
@[simp] theorem po_poS_ne_poR : poS ≠ poR := by decide
@[simp] theorem po_poS_ne_lKb : poS ≠ lKb := by decide
@[simp] theorem po_poN_ne_poS : poN ≠ poS := by decide
@[simp] theorem po_poN_ne_poV : poN ≠ poV := by decide
@[simp] theorem po_poN_ne_poJ : poN ≠ poJ := by decide
@[simp] theorem po_poN_ne_poA : poN ≠ poA := by decide
@[simp] theorem po_poN_ne_poW : poN ≠ poW := by decide
@[simp] theorem po_poN_ne_poR : poN ≠ poR := by decide
@[simp] theorem po_poN_ne_lKb : poN ≠ lKb := by decide
@[simp] theorem po_poV_ne_poS : poV ≠ poS := by decide
@[simp] theorem po_poV_ne_poN : poV ≠ poN := by decide
@[simp] theorem po_poV_ne_poJ : poV ≠ poJ := by decide
@[simp] theorem po_poV_ne_poA : poV ≠ poA := by decide
@[simp] theorem po_poV_ne_poW : poV ≠ poW := by decide
@[simp] theorem po_poV_ne_poR : poV ≠ poR := by decide
@[simp] theorem po_poV_ne_lKb : poV ≠ lKb := by decide
@[simp] theorem po_poJ_ne_poS : poJ ≠ poS := by decide
@[simp] theorem po_poJ_ne_poN : poJ ≠ poN := by decide
@[simp] theorem po_poJ_ne_poV : poJ ≠ poV := by decide
@[simp] theorem po_poJ_ne_poA : poJ ≠ poA := by decide
@[simp] theorem po_poJ_ne_poW : poJ ≠ poW := by decide
@[simp] theorem po_poJ_ne_poR : poJ ≠ poR := by decide
@[simp] theorem po_poJ_ne_lKb : poJ ≠ lKb := by decide
@[simp] theorem po_poA_ne_poS : poA ≠ poS := by decide
@[simp] theorem po_poA_ne_poN : poA ≠ poN := by decide
@[simp] theorem po_poA_ne_poV : poA ≠ poV := by decide
@[simp] theorem po_poA_ne_poJ : poA ≠ poJ := by decide
@[simp] theorem po_poA_ne_poW : poA ≠ poW := by decide
@[simp] theorem po_poA_ne_poR : poA ≠ poR := by decide
@[simp] theorem po_poA_ne_lKb : poA ≠ lKb := by decide
@[simp] theorem po_poW_ne_poS : poW ≠ poS := by decide
@[simp] theorem po_poW_ne_poN : poW ≠ poN := by decide
@[simp] theorem po_poW_ne_poV : poW ≠ poV := by decide
@[simp] theorem po_poW_ne_poJ : poW ≠ poJ := by decide
@[simp] theorem po_poW_ne_poA : poW ≠ poA := by decide
@[simp] theorem po_poW_ne_poR : poW ≠ poR := by decide
@[simp] theorem po_poW_ne_lKb : poW ≠ lKb := by decide
@[simp] theorem po_poR_ne_poS : poR ≠ poS := by decide
@[simp] theorem po_poR_ne_poN : poR ≠ poN := by decide
@[simp] theorem po_poR_ne_poV : poR ≠ poV := by decide
@[simp] theorem po_poR_ne_poJ : poR ≠ poJ := by decide
@[simp] theorem po_poR_ne_poA : poR ≠ poA := by decide
@[simp] theorem po_poR_ne_poW : poR ≠ poW := by decide
@[simp] theorem po_poR_ne_lKb : poR ≠ lKb := by decide
@[simp] theorem po_lKb_ne_poS : lKb ≠ poS := by decide
@[simp] theorem po_lKb_ne_poN : lKb ≠ poN := by decide
@[simp] theorem po_lKb_ne_poV : lKb ≠ poV := by decide
@[simp] theorem po_lKb_ne_poJ : lKb ≠ poJ := by decide
@[simp] theorem po_lKb_ne_poA : lKb ≠ poA := by decide
@[simp] theorem po_lKb_ne_poW : lKb ≠ poW := by decide
@[simp] theorem po_lKb_ne_poR : lKb ≠ poR := by decide

def poParams : List MlS := [poS, poN, poV]
def poLocals : List MlS := [poJ, poA, poW, poR]

def poBody : ProgHOL 64 := prologue poLocals
  (.ite (.cmp .equal (vv poN) (.const 0)) (.return (vv poV))
  (.seq (.assign .local poJ (.op .sub [vv poN, .const 1]))
  (.seq (.assign .local poA (.load .one (.op .add [.op .add [vv poS, .const 8], .shift .lsl (vv poJ) (.const 3)])))
  (.seq (.call (some (some (.local, poW), none)) fInternLImax [vv poA, vv poV])
  (.seq (.call (some (some (.local, poR), none)) fPo [vv poS, vv poJ, vv poW]) (.return (vv poR)))))))

def pzT := ofString "pzn_t"
def pzK := ofString "pzn_k"
def pzF := ofString "pzn_f"
def pzS := ofString "pzn_s"
def pzL := ofString "pzn_l"
def pzO := ofString "pzn_o"
def pzDk := ofString "pzn_dk"
def pzB := ofString "pzn_b"
def pzH := ofString "pzn_h"
def pzV := ofString "pzn_v"
def pzSl := ofString "pzn_sl"
def pzI := ofString "pzn_i"
def pzR := ofString "pzn_r"
def fPz := ofString "inferPisLeaf"

@[simp] theorem pz_plT_ne_plK : pzT ≠ pzK := by decide
@[simp] theorem pz_plT_ne_plF : pzT ≠ pzF := by decide
@[simp] theorem pz_plT_ne_plS : pzT ≠ pzS := by decide
@[simp] theorem pz_plT_ne_plL : pzT ≠ pzL := by decide
@[simp] theorem pz_plT_ne_plO : pzT ≠ pzO := by decide
@[simp] theorem pz_plT_ne_plDk : pzT ≠ pzDk := by decide
@[simp] theorem pz_plT_ne_plB : pzT ≠ pzB := by decide
@[simp] theorem pz_plT_ne_plH : pzT ≠ pzH := by decide
@[simp] theorem pz_plT_ne_plV : pzT ≠ pzV := by decide
@[simp] theorem pz_plT_ne_plSl : pzT ≠ pzSl := by decide
@[simp] theorem pz_plT_ne_plI : pzT ≠ pzI := by decide
@[simp] theorem pz_plT_ne_plR : pzT ≠ pzR := by decide
@[simp] theorem pz_plT_ne_lKb : pzT ≠ lKb := by decide
@[simp] theorem pz_plT_ne_kFu : pzT ≠ kFu := by decide
@[simp] theorem pz_plT_ne_kD : pzT ≠ kD := by decide
@[simp] theorem pz_plT_ne_lFl : pzT ≠ lFl := by decide
@[simp] theorem pz_plT_ne_lDh : pzT ≠ lDh := by decide
@[simp] theorem pz_plT_ne_lDt : pzT ≠ lDt := by decide
@[simp] theorem pz_plT_ne_lDg : pzT ≠ lDg := by decide
@[simp] theorem pz_plT_ne_lDi : pzT ≠ lDi := by decide
@[simp] theorem pz_plT_ne_lRp : pzT ≠ lRp := by decide
@[simp] theorem pz_plT_ne_lRn : pzT ≠ lRn := by decide
@[simp] theorem pz_plT_ne_lFle : pzT ≠ lFle := by decide
@[simp] theorem pz_plT_ne_lDir : pzT ≠ lDir := by decide
@[simp] theorem pz_plK_ne_plT : pzK ≠ pzT := by decide
@[simp] theorem pz_plK_ne_plF : pzK ≠ pzF := by decide
@[simp] theorem pz_plK_ne_plS : pzK ≠ pzS := by decide
@[simp] theorem pz_plK_ne_plL : pzK ≠ pzL := by decide
@[simp] theorem pz_plK_ne_plO : pzK ≠ pzO := by decide
@[simp] theorem pz_plK_ne_plDk : pzK ≠ pzDk := by decide
@[simp] theorem pz_plK_ne_plB : pzK ≠ pzB := by decide
@[simp] theorem pz_plK_ne_plH : pzK ≠ pzH := by decide
@[simp] theorem pz_plK_ne_plV : pzK ≠ pzV := by decide
@[simp] theorem pz_plK_ne_plSl : pzK ≠ pzSl := by decide
@[simp] theorem pz_plK_ne_plI : pzK ≠ pzI := by decide
@[simp] theorem pz_plK_ne_plR : pzK ≠ pzR := by decide
@[simp] theorem pz_plK_ne_lKb : pzK ≠ lKb := by decide
@[simp] theorem pz_plK_ne_kFu : pzK ≠ kFu := by decide
@[simp] theorem pz_plK_ne_kD : pzK ≠ kD := by decide
@[simp] theorem pz_plK_ne_lFl : pzK ≠ lFl := by decide
@[simp] theorem pz_plK_ne_lDh : pzK ≠ lDh := by decide
@[simp] theorem pz_plK_ne_lDt : pzK ≠ lDt := by decide
@[simp] theorem pz_plK_ne_lDg : pzK ≠ lDg := by decide
@[simp] theorem pz_plK_ne_lDi : pzK ≠ lDi := by decide
@[simp] theorem pz_plK_ne_lRp : pzK ≠ lRp := by decide
@[simp] theorem pz_plK_ne_lRn : pzK ≠ lRn := by decide
@[simp] theorem pz_plK_ne_lFle : pzK ≠ lFle := by decide
@[simp] theorem pz_plK_ne_lDir : pzK ≠ lDir := by decide
@[simp] theorem pz_plF_ne_plT : pzF ≠ pzT := by decide
@[simp] theorem pz_plF_ne_plK : pzF ≠ pzK := by decide
@[simp] theorem pz_plF_ne_plS : pzF ≠ pzS := by decide
@[simp] theorem pz_plF_ne_plL : pzF ≠ pzL := by decide
@[simp] theorem pz_plF_ne_plO : pzF ≠ pzO := by decide
@[simp] theorem pz_plF_ne_plDk : pzF ≠ pzDk := by decide
@[simp] theorem pz_plF_ne_plB : pzF ≠ pzB := by decide
@[simp] theorem pz_plF_ne_plH : pzF ≠ pzH := by decide
@[simp] theorem pz_plF_ne_plV : pzF ≠ pzV := by decide
@[simp] theorem pz_plF_ne_plSl : pzF ≠ pzSl := by decide
@[simp] theorem pz_plF_ne_plI : pzF ≠ pzI := by decide
@[simp] theorem pz_plF_ne_plR : pzF ≠ pzR := by decide
@[simp] theorem pz_plF_ne_lKb : pzF ≠ lKb := by decide
@[simp] theorem pz_plF_ne_kFu : pzF ≠ kFu := by decide
@[simp] theorem pz_plF_ne_kD : pzF ≠ kD := by decide
@[simp] theorem pz_plF_ne_lFl : pzF ≠ lFl := by decide
@[simp] theorem pz_plF_ne_lDh : pzF ≠ lDh := by decide
@[simp] theorem pz_plF_ne_lDt : pzF ≠ lDt := by decide
@[simp] theorem pz_plF_ne_lDg : pzF ≠ lDg := by decide
@[simp] theorem pz_plF_ne_lDi : pzF ≠ lDi := by decide
@[simp] theorem pz_plF_ne_lRp : pzF ≠ lRp := by decide
@[simp] theorem pz_plF_ne_lRn : pzF ≠ lRn := by decide
@[simp] theorem pz_plF_ne_lFle : pzF ≠ lFle := by decide
@[simp] theorem pz_plF_ne_lDir : pzF ≠ lDir := by decide
@[simp] theorem pz_plS_ne_plT : pzS ≠ pzT := by decide
@[simp] theorem pz_plS_ne_plK : pzS ≠ pzK := by decide
@[simp] theorem pz_plS_ne_plF : pzS ≠ pzF := by decide
@[simp] theorem pz_plS_ne_plL : pzS ≠ pzL := by decide
@[simp] theorem pz_plS_ne_plO : pzS ≠ pzO := by decide
@[simp] theorem pz_plS_ne_plDk : pzS ≠ pzDk := by decide
@[simp] theorem pz_plS_ne_plB : pzS ≠ pzB := by decide
@[simp] theorem pz_plS_ne_plH : pzS ≠ pzH := by decide
@[simp] theorem pz_plS_ne_plV : pzS ≠ pzV := by decide
@[simp] theorem pz_plS_ne_plSl : pzS ≠ pzSl := by decide
@[simp] theorem pz_plS_ne_plI : pzS ≠ pzI := by decide
@[simp] theorem pz_plS_ne_plR : pzS ≠ pzR := by decide
@[simp] theorem pz_plS_ne_lKb : pzS ≠ lKb := by decide
@[simp] theorem pz_plS_ne_kFu : pzS ≠ kFu := by decide
@[simp] theorem pz_plS_ne_kD : pzS ≠ kD := by decide
@[simp] theorem pz_plS_ne_lFl : pzS ≠ lFl := by decide
@[simp] theorem pz_plS_ne_lDh : pzS ≠ lDh := by decide
@[simp] theorem pz_plS_ne_lDt : pzS ≠ lDt := by decide
@[simp] theorem pz_plS_ne_lDg : pzS ≠ lDg := by decide
@[simp] theorem pz_plS_ne_lDi : pzS ≠ lDi := by decide
@[simp] theorem pz_plS_ne_lRp : pzS ≠ lRp := by decide
@[simp] theorem pz_plS_ne_lRn : pzS ≠ lRn := by decide
@[simp] theorem pz_plS_ne_lFle : pzS ≠ lFle := by decide
@[simp] theorem pz_plS_ne_lDir : pzS ≠ lDir := by decide
@[simp] theorem pz_plL_ne_plT : pzL ≠ pzT := by decide
@[simp] theorem pz_plL_ne_plK : pzL ≠ pzK := by decide
@[simp] theorem pz_plL_ne_plF : pzL ≠ pzF := by decide
@[simp] theorem pz_plL_ne_plS : pzL ≠ pzS := by decide
@[simp] theorem pz_plL_ne_plO : pzL ≠ pzO := by decide
@[simp] theorem pz_plL_ne_plDk : pzL ≠ pzDk := by decide
@[simp] theorem pz_plL_ne_plB : pzL ≠ pzB := by decide
@[simp] theorem pz_plL_ne_plH : pzL ≠ pzH := by decide
@[simp] theorem pz_plL_ne_plV : pzL ≠ pzV := by decide
@[simp] theorem pz_plL_ne_plSl : pzL ≠ pzSl := by decide
@[simp] theorem pz_plL_ne_plI : pzL ≠ pzI := by decide
@[simp] theorem pz_plL_ne_plR : pzL ≠ pzR := by decide
@[simp] theorem pz_plL_ne_lKb : pzL ≠ lKb := by decide
@[simp] theorem pz_plL_ne_kFu : pzL ≠ kFu := by decide
@[simp] theorem pz_plL_ne_kD : pzL ≠ kD := by decide
@[simp] theorem pz_plL_ne_lFl : pzL ≠ lFl := by decide
@[simp] theorem pz_plL_ne_lDh : pzL ≠ lDh := by decide
@[simp] theorem pz_plL_ne_lDt : pzL ≠ lDt := by decide
@[simp] theorem pz_plL_ne_lDg : pzL ≠ lDg := by decide
@[simp] theorem pz_plL_ne_lDi : pzL ≠ lDi := by decide
@[simp] theorem pz_plL_ne_lRp : pzL ≠ lRp := by decide
@[simp] theorem pz_plL_ne_lRn : pzL ≠ lRn := by decide
@[simp] theorem pz_plL_ne_lFle : pzL ≠ lFle := by decide
@[simp] theorem pz_plL_ne_lDir : pzL ≠ lDir := by decide
@[simp] theorem pz_plO_ne_plT : pzO ≠ pzT := by decide
@[simp] theorem pz_plO_ne_plK : pzO ≠ pzK := by decide
@[simp] theorem pz_plO_ne_plF : pzO ≠ pzF := by decide
@[simp] theorem pz_plO_ne_plS : pzO ≠ pzS := by decide
@[simp] theorem pz_plO_ne_plL : pzO ≠ pzL := by decide
@[simp] theorem pz_plO_ne_plDk : pzO ≠ pzDk := by decide
@[simp] theorem pz_plO_ne_plB : pzO ≠ pzB := by decide
@[simp] theorem pz_plO_ne_plH : pzO ≠ pzH := by decide
@[simp] theorem pz_plO_ne_plV : pzO ≠ pzV := by decide
@[simp] theorem pz_plO_ne_plSl : pzO ≠ pzSl := by decide
@[simp] theorem pz_plO_ne_plI : pzO ≠ pzI := by decide
@[simp] theorem pz_plO_ne_plR : pzO ≠ pzR := by decide
@[simp] theorem pz_plO_ne_lKb : pzO ≠ lKb := by decide
@[simp] theorem pz_plO_ne_kFu : pzO ≠ kFu := by decide
@[simp] theorem pz_plO_ne_kD : pzO ≠ kD := by decide
@[simp] theorem pz_plO_ne_lFl : pzO ≠ lFl := by decide
@[simp] theorem pz_plO_ne_lDh : pzO ≠ lDh := by decide
@[simp] theorem pz_plO_ne_lDt : pzO ≠ lDt := by decide
@[simp] theorem pz_plO_ne_lDg : pzO ≠ lDg := by decide
@[simp] theorem pz_plO_ne_lDi : pzO ≠ lDi := by decide
@[simp] theorem pz_plO_ne_lRp : pzO ≠ lRp := by decide
@[simp] theorem pz_plO_ne_lRn : pzO ≠ lRn := by decide
@[simp] theorem pz_plO_ne_lFle : pzO ≠ lFle := by decide
@[simp] theorem pz_plO_ne_lDir : pzO ≠ lDir := by decide
@[simp] theorem pz_plDk_ne_plT : pzDk ≠ pzT := by decide
@[simp] theorem pz_plDk_ne_plK : pzDk ≠ pzK := by decide
@[simp] theorem pz_plDk_ne_plF : pzDk ≠ pzF := by decide
@[simp] theorem pz_plDk_ne_plS : pzDk ≠ pzS := by decide
@[simp] theorem pz_plDk_ne_plL : pzDk ≠ pzL := by decide
@[simp] theorem pz_plDk_ne_plO : pzDk ≠ pzO := by decide
@[simp] theorem pz_plDk_ne_plB : pzDk ≠ pzB := by decide
@[simp] theorem pz_plDk_ne_plH : pzDk ≠ pzH := by decide
@[simp] theorem pz_plDk_ne_plV : pzDk ≠ pzV := by decide
@[simp] theorem pz_plDk_ne_plSl : pzDk ≠ pzSl := by decide
@[simp] theorem pz_plDk_ne_plI : pzDk ≠ pzI := by decide
@[simp] theorem pz_plDk_ne_plR : pzDk ≠ pzR := by decide
@[simp] theorem pz_plDk_ne_lKb : pzDk ≠ lKb := by decide
@[simp] theorem pz_plDk_ne_kFu : pzDk ≠ kFu := by decide
@[simp] theorem pz_plDk_ne_kD : pzDk ≠ kD := by decide
@[simp] theorem pz_plDk_ne_lFl : pzDk ≠ lFl := by decide
@[simp] theorem pz_plDk_ne_lDh : pzDk ≠ lDh := by decide
@[simp] theorem pz_plDk_ne_lDt : pzDk ≠ lDt := by decide
@[simp] theorem pz_plDk_ne_lDg : pzDk ≠ lDg := by decide
@[simp] theorem pz_plDk_ne_lDi : pzDk ≠ lDi := by decide
@[simp] theorem pz_plDk_ne_lRp : pzDk ≠ lRp := by decide
@[simp] theorem pz_plDk_ne_lRn : pzDk ≠ lRn := by decide
@[simp] theorem pz_plDk_ne_lFle : pzDk ≠ lFle := by decide
@[simp] theorem pz_plDk_ne_lDir : pzDk ≠ lDir := by decide
@[simp] theorem pz_plB_ne_plT : pzB ≠ pzT := by decide
@[simp] theorem pz_plB_ne_plK : pzB ≠ pzK := by decide
@[simp] theorem pz_plB_ne_plF : pzB ≠ pzF := by decide
@[simp] theorem pz_plB_ne_plS : pzB ≠ pzS := by decide
@[simp] theorem pz_plB_ne_plL : pzB ≠ pzL := by decide
@[simp] theorem pz_plB_ne_plO : pzB ≠ pzO := by decide
@[simp] theorem pz_plB_ne_plDk : pzB ≠ pzDk := by decide
@[simp] theorem pz_plB_ne_plH : pzB ≠ pzH := by decide
@[simp] theorem pz_plB_ne_plV : pzB ≠ pzV := by decide
@[simp] theorem pz_plB_ne_plSl : pzB ≠ pzSl := by decide
@[simp] theorem pz_plB_ne_plI : pzB ≠ pzI := by decide
@[simp] theorem pz_plB_ne_plR : pzB ≠ pzR := by decide
@[simp] theorem pz_plB_ne_lKb : pzB ≠ lKb := by decide
@[simp] theorem pz_plB_ne_kFu : pzB ≠ kFu := by decide
@[simp] theorem pz_plB_ne_kD : pzB ≠ kD := by decide
@[simp] theorem pz_plB_ne_lFl : pzB ≠ lFl := by decide
@[simp] theorem pz_plB_ne_lDh : pzB ≠ lDh := by decide
@[simp] theorem pz_plB_ne_lDt : pzB ≠ lDt := by decide
@[simp] theorem pz_plB_ne_lDg : pzB ≠ lDg := by decide
@[simp] theorem pz_plB_ne_lDi : pzB ≠ lDi := by decide
@[simp] theorem pz_plB_ne_lRp : pzB ≠ lRp := by decide
@[simp] theorem pz_plB_ne_lRn : pzB ≠ lRn := by decide
@[simp] theorem pz_plB_ne_lFle : pzB ≠ lFle := by decide
@[simp] theorem pz_plB_ne_lDir : pzB ≠ lDir := by decide
@[simp] theorem pz_plH_ne_plT : pzH ≠ pzT := by decide
@[simp] theorem pz_plH_ne_plK : pzH ≠ pzK := by decide
@[simp] theorem pz_plH_ne_plF : pzH ≠ pzF := by decide
@[simp] theorem pz_plH_ne_plS : pzH ≠ pzS := by decide
@[simp] theorem pz_plH_ne_plL : pzH ≠ pzL := by decide
@[simp] theorem pz_plH_ne_plO : pzH ≠ pzO := by decide
@[simp] theorem pz_plH_ne_plDk : pzH ≠ pzDk := by decide
@[simp] theorem pz_plH_ne_plB : pzH ≠ pzB := by decide
@[simp] theorem pz_plH_ne_plV : pzH ≠ pzV := by decide
@[simp] theorem pz_plH_ne_plSl : pzH ≠ pzSl := by decide
@[simp] theorem pz_plH_ne_plI : pzH ≠ pzI := by decide
@[simp] theorem pz_plH_ne_plR : pzH ≠ pzR := by decide
@[simp] theorem pz_plH_ne_lKb : pzH ≠ lKb := by decide
@[simp] theorem pz_plH_ne_kFu : pzH ≠ kFu := by decide
@[simp] theorem pz_plH_ne_kD : pzH ≠ kD := by decide
@[simp] theorem pz_plH_ne_lFl : pzH ≠ lFl := by decide
@[simp] theorem pz_plH_ne_lDh : pzH ≠ lDh := by decide
@[simp] theorem pz_plH_ne_lDt : pzH ≠ lDt := by decide
@[simp] theorem pz_plH_ne_lDg : pzH ≠ lDg := by decide
@[simp] theorem pz_plH_ne_lDi : pzH ≠ lDi := by decide
@[simp] theorem pz_plH_ne_lRp : pzH ≠ lRp := by decide
@[simp] theorem pz_plH_ne_lRn : pzH ≠ lRn := by decide
@[simp] theorem pz_plH_ne_lFle : pzH ≠ lFle := by decide
@[simp] theorem pz_plH_ne_lDir : pzH ≠ lDir := by decide
@[simp] theorem pz_plV_ne_plT : pzV ≠ pzT := by decide
@[simp] theorem pz_plV_ne_plK : pzV ≠ pzK := by decide
@[simp] theorem pz_plV_ne_plF : pzV ≠ pzF := by decide
@[simp] theorem pz_plV_ne_plS : pzV ≠ pzS := by decide
@[simp] theorem pz_plV_ne_plL : pzV ≠ pzL := by decide
@[simp] theorem pz_plV_ne_plO : pzV ≠ pzO := by decide
@[simp] theorem pz_plV_ne_plDk : pzV ≠ pzDk := by decide
@[simp] theorem pz_plV_ne_plB : pzV ≠ pzB := by decide
@[simp] theorem pz_plV_ne_plH : pzV ≠ pzH := by decide
@[simp] theorem pz_plV_ne_plSl : pzV ≠ pzSl := by decide
@[simp] theorem pz_plV_ne_plI : pzV ≠ pzI := by decide
@[simp] theorem pz_plV_ne_plR : pzV ≠ pzR := by decide
@[simp] theorem pz_plV_ne_lKb : pzV ≠ lKb := by decide
@[simp] theorem pz_plV_ne_kFu : pzV ≠ kFu := by decide
@[simp] theorem pz_plV_ne_kD : pzV ≠ kD := by decide
@[simp] theorem pz_plV_ne_lFl : pzV ≠ lFl := by decide
@[simp] theorem pz_plV_ne_lDh : pzV ≠ lDh := by decide
@[simp] theorem pz_plV_ne_lDt : pzV ≠ lDt := by decide
@[simp] theorem pz_plV_ne_lDg : pzV ≠ lDg := by decide
@[simp] theorem pz_plV_ne_lDi : pzV ≠ lDi := by decide
@[simp] theorem pz_plV_ne_lRp : pzV ≠ lRp := by decide
@[simp] theorem pz_plV_ne_lRn : pzV ≠ lRn := by decide
@[simp] theorem pz_plV_ne_lFle : pzV ≠ lFle := by decide
@[simp] theorem pz_plV_ne_lDir : pzV ≠ lDir := by decide
@[simp] theorem pz_plSl_ne_plT : pzSl ≠ pzT := by decide
@[simp] theorem pz_plSl_ne_plK : pzSl ≠ pzK := by decide
@[simp] theorem pz_plSl_ne_plF : pzSl ≠ pzF := by decide
@[simp] theorem pz_plSl_ne_plS : pzSl ≠ pzS := by decide
@[simp] theorem pz_plSl_ne_plL : pzSl ≠ pzL := by decide
@[simp] theorem pz_plSl_ne_plO : pzSl ≠ pzO := by decide
@[simp] theorem pz_plSl_ne_plDk : pzSl ≠ pzDk := by decide
@[simp] theorem pz_plSl_ne_plB : pzSl ≠ pzB := by decide
@[simp] theorem pz_plSl_ne_plH : pzSl ≠ pzH := by decide
@[simp] theorem pz_plSl_ne_plV : pzSl ≠ pzV := by decide
@[simp] theorem pz_plSl_ne_plI : pzSl ≠ pzI := by decide
@[simp] theorem pz_plSl_ne_plR : pzSl ≠ pzR := by decide
@[simp] theorem pz_plSl_ne_lKb : pzSl ≠ lKb := by decide
@[simp] theorem pz_plSl_ne_kFu : pzSl ≠ kFu := by decide
@[simp] theorem pz_plSl_ne_kD : pzSl ≠ kD := by decide
@[simp] theorem pz_plSl_ne_lFl : pzSl ≠ lFl := by decide
@[simp] theorem pz_plSl_ne_lDh : pzSl ≠ lDh := by decide
@[simp] theorem pz_plSl_ne_lDt : pzSl ≠ lDt := by decide
@[simp] theorem pz_plSl_ne_lDg : pzSl ≠ lDg := by decide
@[simp] theorem pz_plSl_ne_lDi : pzSl ≠ lDi := by decide
@[simp] theorem pz_plSl_ne_lRp : pzSl ≠ lRp := by decide
@[simp] theorem pz_plSl_ne_lRn : pzSl ≠ lRn := by decide
@[simp] theorem pz_plSl_ne_lFle : pzSl ≠ lFle := by decide
@[simp] theorem pz_plSl_ne_lDir : pzSl ≠ lDir := by decide
@[simp] theorem pz_plI_ne_plT : pzI ≠ pzT := by decide
@[simp] theorem pz_plI_ne_plK : pzI ≠ pzK := by decide
@[simp] theorem pz_plI_ne_plF : pzI ≠ pzF := by decide
@[simp] theorem pz_plI_ne_plS : pzI ≠ pzS := by decide
@[simp] theorem pz_plI_ne_plL : pzI ≠ pzL := by decide
@[simp] theorem pz_plI_ne_plO : pzI ≠ pzO := by decide
@[simp] theorem pz_plI_ne_plDk : pzI ≠ pzDk := by decide
@[simp] theorem pz_plI_ne_plB : pzI ≠ pzB := by decide
@[simp] theorem pz_plI_ne_plH : pzI ≠ pzH := by decide
@[simp] theorem pz_plI_ne_plV : pzI ≠ pzV := by decide
@[simp] theorem pz_plI_ne_plSl : pzI ≠ pzSl := by decide
@[simp] theorem pz_plI_ne_plR : pzI ≠ pzR := by decide
@[simp] theorem pz_plI_ne_lKb : pzI ≠ lKb := by decide
@[simp] theorem pz_plI_ne_kFu : pzI ≠ kFu := by decide
@[simp] theorem pz_plI_ne_kD : pzI ≠ kD := by decide
@[simp] theorem pz_plI_ne_lFl : pzI ≠ lFl := by decide
@[simp] theorem pz_plI_ne_lDh : pzI ≠ lDh := by decide
@[simp] theorem pz_plI_ne_lDt : pzI ≠ lDt := by decide
@[simp] theorem pz_plI_ne_lDg : pzI ≠ lDg := by decide
@[simp] theorem pz_plI_ne_lDi : pzI ≠ lDi := by decide
@[simp] theorem pz_plI_ne_lRp : pzI ≠ lRp := by decide
@[simp] theorem pz_plI_ne_lRn : pzI ≠ lRn := by decide
@[simp] theorem pz_plI_ne_lFle : pzI ≠ lFle := by decide
@[simp] theorem pz_plI_ne_lDir : pzI ≠ lDir := by decide
@[simp] theorem pz_plR_ne_plT : pzR ≠ pzT := by decide
@[simp] theorem pz_plR_ne_plK : pzR ≠ pzK := by decide
@[simp] theorem pz_plR_ne_plF : pzR ≠ pzF := by decide
@[simp] theorem pz_plR_ne_plS : pzR ≠ pzS := by decide
@[simp] theorem pz_plR_ne_plL : pzR ≠ pzL := by decide
@[simp] theorem pz_plR_ne_plO : pzR ≠ pzO := by decide
@[simp] theorem pz_plR_ne_plDk : pzR ≠ pzDk := by decide
@[simp] theorem pz_plR_ne_plB : pzR ≠ pzB := by decide
@[simp] theorem pz_plR_ne_plH : pzR ≠ pzH := by decide
@[simp] theorem pz_plR_ne_plV : pzR ≠ pzV := by decide
@[simp] theorem pz_plR_ne_plSl : pzR ≠ pzSl := by decide
@[simp] theorem pz_plR_ne_plI : pzR ≠ pzI := by decide
@[simp] theorem pz_plR_ne_lKb : pzR ≠ lKb := by decide
@[simp] theorem pz_plR_ne_kFu : pzR ≠ kFu := by decide
@[simp] theorem pz_plR_ne_kD : pzR ≠ kD := by decide
@[simp] theorem pz_plR_ne_lFl : pzR ≠ lFl := by decide
@[simp] theorem pz_plR_ne_lDh : pzR ≠ lDh := by decide
@[simp] theorem pz_plR_ne_lDt : pzR ≠ lDt := by decide
@[simp] theorem pz_plR_ne_lDg : pzR ≠ lDg := by decide
@[simp] theorem pz_plR_ne_lDi : pzR ≠ lDi := by decide
@[simp] theorem pz_plR_ne_lRp : pzR ≠ lRp := by decide
@[simp] theorem pz_plR_ne_lRn : pzR ≠ lRn := by decide
@[simp] theorem pz_plR_ne_lFle : pzR ≠ lFle := by decide
@[simp] theorem pz_plR_ne_lDir : pzR ≠ lDir := by decide
@[simp] theorem pz_lKb_ne_plT : lKb ≠ pzT := by decide
@[simp] theorem pz_lKb_ne_plK : lKb ≠ pzK := by decide
@[simp] theorem pz_lKb_ne_plF : lKb ≠ pzF := by decide
@[simp] theorem pz_lKb_ne_plS : lKb ≠ pzS := by decide
@[simp] theorem pz_lKb_ne_plL : lKb ≠ pzL := by decide
@[simp] theorem pz_lKb_ne_plO : lKb ≠ pzO := by decide
@[simp] theorem pz_lKb_ne_plDk : lKb ≠ pzDk := by decide
@[simp] theorem pz_lKb_ne_plB : lKb ≠ pzB := by decide
@[simp] theorem pz_lKb_ne_plH : lKb ≠ pzH := by decide
@[simp] theorem pz_lKb_ne_plV : lKb ≠ pzV := by decide
@[simp] theorem pz_lKb_ne_plSl : lKb ≠ pzSl := by decide
@[simp] theorem pz_lKb_ne_plI : lKb ≠ pzI := by decide
@[simp] theorem pz_lKb_ne_plR : lKb ≠ pzR := by decide
@[simp] theorem pz_kFu_ne_plT : kFu ≠ pzT := by decide
@[simp] theorem pz_kFu_ne_plK : kFu ≠ pzK := by decide
@[simp] theorem pz_kFu_ne_plF : kFu ≠ pzF := by decide
@[simp] theorem pz_kFu_ne_plS : kFu ≠ pzS := by decide
@[simp] theorem pz_kFu_ne_plL : kFu ≠ pzL := by decide
@[simp] theorem pz_kFu_ne_plO : kFu ≠ pzO := by decide
@[simp] theorem pz_kFu_ne_plDk : kFu ≠ pzDk := by decide
@[simp] theorem pz_kFu_ne_plB : kFu ≠ pzB := by decide
@[simp] theorem pz_kFu_ne_plH : kFu ≠ pzH := by decide
@[simp] theorem pz_kFu_ne_plV : kFu ≠ pzV := by decide
@[simp] theorem pz_kFu_ne_plSl : kFu ≠ pzSl := by decide
@[simp] theorem pz_kFu_ne_plI : kFu ≠ pzI := by decide
@[simp] theorem pz_kFu_ne_plR : kFu ≠ pzR := by decide
@[simp] theorem pz_kD_ne_plT : kD ≠ pzT := by decide
@[simp] theorem pz_kD_ne_plK : kD ≠ pzK := by decide
@[simp] theorem pz_kD_ne_plF : kD ≠ pzF := by decide
@[simp] theorem pz_kD_ne_plS : kD ≠ pzS := by decide
@[simp] theorem pz_kD_ne_plL : kD ≠ pzL := by decide
@[simp] theorem pz_kD_ne_plO : kD ≠ pzO := by decide
@[simp] theorem pz_kD_ne_plDk : kD ≠ pzDk := by decide
@[simp] theorem pz_kD_ne_plB : kD ≠ pzB := by decide
@[simp] theorem pz_kD_ne_plH : kD ≠ pzH := by decide
@[simp] theorem pz_kD_ne_plV : kD ≠ pzV := by decide
@[simp] theorem pz_kD_ne_plSl : kD ≠ pzSl := by decide
@[simp] theorem pz_kD_ne_plI : kD ≠ pzI := by decide
@[simp] theorem pz_kD_ne_plR : kD ≠ pzR := by decide
@[simp] theorem pz_lFl_ne_plT : lFl ≠ pzT := by decide
@[simp] theorem pz_lFl_ne_plK : lFl ≠ pzK := by decide
@[simp] theorem pz_lFl_ne_plF : lFl ≠ pzF := by decide
@[simp] theorem pz_lFl_ne_plS : lFl ≠ pzS := by decide
@[simp] theorem pz_lFl_ne_plL : lFl ≠ pzL := by decide
@[simp] theorem pz_lFl_ne_plO : lFl ≠ pzO := by decide
@[simp] theorem pz_lFl_ne_plDk : lFl ≠ pzDk := by decide
@[simp] theorem pz_lFl_ne_plB : lFl ≠ pzB := by decide
@[simp] theorem pz_lFl_ne_plH : lFl ≠ pzH := by decide
@[simp] theorem pz_lFl_ne_plV : lFl ≠ pzV := by decide
@[simp] theorem pz_lFl_ne_plSl : lFl ≠ pzSl := by decide
@[simp] theorem pz_lFl_ne_plI : lFl ≠ pzI := by decide
@[simp] theorem pz_lFl_ne_plR : lFl ≠ pzR := by decide
@[simp] theorem pz_lDh_ne_plT : lDh ≠ pzT := by decide
@[simp] theorem pz_lDh_ne_plK : lDh ≠ pzK := by decide
@[simp] theorem pz_lDh_ne_plF : lDh ≠ pzF := by decide
@[simp] theorem pz_lDh_ne_plS : lDh ≠ pzS := by decide
@[simp] theorem pz_lDh_ne_plL : lDh ≠ pzL := by decide
@[simp] theorem pz_lDh_ne_plO : lDh ≠ pzO := by decide
@[simp] theorem pz_lDh_ne_plDk : lDh ≠ pzDk := by decide
@[simp] theorem pz_lDh_ne_plB : lDh ≠ pzB := by decide
@[simp] theorem pz_lDh_ne_plH : lDh ≠ pzH := by decide
@[simp] theorem pz_lDh_ne_plV : lDh ≠ pzV := by decide
@[simp] theorem pz_lDh_ne_plSl : lDh ≠ pzSl := by decide
@[simp] theorem pz_lDh_ne_plI : lDh ≠ pzI := by decide
@[simp] theorem pz_lDh_ne_plR : lDh ≠ pzR := by decide
@[simp] theorem pz_lDt_ne_plT : lDt ≠ pzT := by decide
@[simp] theorem pz_lDt_ne_plK : lDt ≠ pzK := by decide
@[simp] theorem pz_lDt_ne_plF : lDt ≠ pzF := by decide
@[simp] theorem pz_lDt_ne_plS : lDt ≠ pzS := by decide
@[simp] theorem pz_lDt_ne_plL : lDt ≠ pzL := by decide
@[simp] theorem pz_lDt_ne_plO : lDt ≠ pzO := by decide
@[simp] theorem pz_lDt_ne_plDk : lDt ≠ pzDk := by decide
@[simp] theorem pz_lDt_ne_plB : lDt ≠ pzB := by decide
@[simp] theorem pz_lDt_ne_plH : lDt ≠ pzH := by decide
@[simp] theorem pz_lDt_ne_plV : lDt ≠ pzV := by decide
@[simp] theorem pz_lDt_ne_plSl : lDt ≠ pzSl := by decide
@[simp] theorem pz_lDt_ne_plI : lDt ≠ pzI := by decide
@[simp] theorem pz_lDt_ne_plR : lDt ≠ pzR := by decide
@[simp] theorem pz_lDg_ne_plT : lDg ≠ pzT := by decide
@[simp] theorem pz_lDg_ne_plK : lDg ≠ pzK := by decide
@[simp] theorem pz_lDg_ne_plF : lDg ≠ pzF := by decide
@[simp] theorem pz_lDg_ne_plS : lDg ≠ pzS := by decide
@[simp] theorem pz_lDg_ne_plL : lDg ≠ pzL := by decide
@[simp] theorem pz_lDg_ne_plO : lDg ≠ pzO := by decide
@[simp] theorem pz_lDg_ne_plDk : lDg ≠ pzDk := by decide
@[simp] theorem pz_lDg_ne_plB : lDg ≠ pzB := by decide
@[simp] theorem pz_lDg_ne_plH : lDg ≠ pzH := by decide
@[simp] theorem pz_lDg_ne_plV : lDg ≠ pzV := by decide
@[simp] theorem pz_lDg_ne_plSl : lDg ≠ pzSl := by decide
@[simp] theorem pz_lDg_ne_plI : lDg ≠ pzI := by decide
@[simp] theorem pz_lDg_ne_plR : lDg ≠ pzR := by decide
@[simp] theorem pz_lDi_ne_plT : lDi ≠ pzT := by decide
@[simp] theorem pz_lDi_ne_plK : lDi ≠ pzK := by decide
@[simp] theorem pz_lDi_ne_plF : lDi ≠ pzF := by decide
@[simp] theorem pz_lDi_ne_plS : lDi ≠ pzS := by decide
@[simp] theorem pz_lDi_ne_plL : lDi ≠ pzL := by decide
@[simp] theorem pz_lDi_ne_plO : lDi ≠ pzO := by decide
@[simp] theorem pz_lDi_ne_plDk : lDi ≠ pzDk := by decide
@[simp] theorem pz_lDi_ne_plB : lDi ≠ pzB := by decide
@[simp] theorem pz_lDi_ne_plH : lDi ≠ pzH := by decide
@[simp] theorem pz_lDi_ne_plV : lDi ≠ pzV := by decide
@[simp] theorem pz_lDi_ne_plSl : lDi ≠ pzSl := by decide
@[simp] theorem pz_lDi_ne_plI : lDi ≠ pzI := by decide
@[simp] theorem pz_lDi_ne_plR : lDi ≠ pzR := by decide
@[simp] theorem pz_lRp_ne_plT : lRp ≠ pzT := by decide
@[simp] theorem pz_lRp_ne_plK : lRp ≠ pzK := by decide
@[simp] theorem pz_lRp_ne_plF : lRp ≠ pzF := by decide
@[simp] theorem pz_lRp_ne_plS : lRp ≠ pzS := by decide
@[simp] theorem pz_lRp_ne_plL : lRp ≠ pzL := by decide
@[simp] theorem pz_lRp_ne_plO : lRp ≠ pzO := by decide
@[simp] theorem pz_lRp_ne_plDk : lRp ≠ pzDk := by decide
@[simp] theorem pz_lRp_ne_plB : lRp ≠ pzB := by decide
@[simp] theorem pz_lRp_ne_plH : lRp ≠ pzH := by decide
@[simp] theorem pz_lRp_ne_plV : lRp ≠ pzV := by decide
@[simp] theorem pz_lRp_ne_plSl : lRp ≠ pzSl := by decide
@[simp] theorem pz_lRp_ne_plI : lRp ≠ pzI := by decide
@[simp] theorem pz_lRp_ne_plR : lRp ≠ pzR := by decide
@[simp] theorem pz_lRn_ne_plT : lRn ≠ pzT := by decide
@[simp] theorem pz_lRn_ne_plK : lRn ≠ pzK := by decide
@[simp] theorem pz_lRn_ne_plF : lRn ≠ pzF := by decide
@[simp] theorem pz_lRn_ne_plS : lRn ≠ pzS := by decide
@[simp] theorem pz_lRn_ne_plL : lRn ≠ pzL := by decide
@[simp] theorem pz_lRn_ne_plO : lRn ≠ pzO := by decide
@[simp] theorem pz_lRn_ne_plDk : lRn ≠ pzDk := by decide
@[simp] theorem pz_lRn_ne_plB : lRn ≠ pzB := by decide
@[simp] theorem pz_lRn_ne_plH : lRn ≠ pzH := by decide
@[simp] theorem pz_lRn_ne_plV : lRn ≠ pzV := by decide
@[simp] theorem pz_lRn_ne_plSl : lRn ≠ pzSl := by decide
@[simp] theorem pz_lRn_ne_plI : lRn ≠ pzI := by decide
@[simp] theorem pz_lRn_ne_plR : lRn ≠ pzR := by decide
@[simp] theorem pz_lFle_ne_plT : lFle ≠ pzT := by decide
@[simp] theorem pz_lFle_ne_plK : lFle ≠ pzK := by decide
@[simp] theorem pz_lFle_ne_plF : lFle ≠ pzF := by decide
@[simp] theorem pz_lFle_ne_plS : lFle ≠ pzS := by decide
@[simp] theorem pz_lFle_ne_plL : lFle ≠ pzL := by decide
@[simp] theorem pz_lFle_ne_plO : lFle ≠ pzO := by decide
@[simp] theorem pz_lFle_ne_plDk : lFle ≠ pzDk := by decide
@[simp] theorem pz_lFle_ne_plB : lFle ≠ pzB := by decide
@[simp] theorem pz_lFle_ne_plH : lFle ≠ pzH := by decide
@[simp] theorem pz_lFle_ne_plV : lFle ≠ pzV := by decide
@[simp] theorem pz_lFle_ne_plSl : lFle ≠ pzSl := by decide
@[simp] theorem pz_lFle_ne_plI : lFle ≠ pzI := by decide
@[simp] theorem pz_lFle_ne_plR : lFle ≠ pzR := by decide
@[simp] theorem pz_lDir_ne_plT : lDir ≠ pzT := by decide
@[simp] theorem pz_lDir_ne_plK : lDir ≠ pzK := by decide
@[simp] theorem pz_lDir_ne_plF : lDir ≠ pzF := by decide
@[simp] theorem pz_lDir_ne_plS : lDir ≠ pzS := by decide
@[simp] theorem pz_lDir_ne_plL : lDir ≠ pzL := by decide
@[simp] theorem pz_lDir_ne_plO : lDir ≠ pzO := by decide
@[simp] theorem pz_lDir_ne_plDk : lDir ≠ pzDk := by decide
@[simp] theorem pz_lDir_ne_plB : lDir ≠ pzB := by decide
@[simp] theorem pz_lDir_ne_plH : lDir ≠ pzH := by decide
@[simp] theorem pz_lDir_ne_plV : lDir ≠ pzV := by decide
@[simp] theorem pz_lDir_ne_plSl : lDir ≠ pzSl := by decide
@[simp] theorem pz_lDir_ne_plI : lDir ≠ pzI := by decide
@[simp] theorem pz_lDir_ne_plR : lDir ≠ pzR := by decide

def pzParams : List MlS := [kFu, kD, pzT, pzK, pzF, pzS]
def pzLocals : List MlS := [pzL, pzO, pzDk, pzB, pzH, lFl, lDh, lDt, lDg, lDi, lRp, lRn, pzV, pzSl, pzI, pzR]

def pzBody : ProgHOL 64 := prologue pzLocals
  (.seq (.assign .local pzL (.load .one (vv pzF)))
  (.seq (.call (some (some (.local, pzO), none)) ExQ.fIrr
      [vv pzF, .const 0, vv pzL, .const (BitVec.ofNat 64 coreWalkFuel), vv pzT, .const 0])
  (.seq (.assign .local pzDk (.op .add [vv kD, vv pzK]))
  (.seq (.call (some (some (.local, pzB), none)) fI [vv kFu, vv pzDk, vv pzO])
  (.seq (.call (some (some (.local, pzH), none)) fW [vv kFu, vv pzDk, vv pzB])
  (.ite (tagIsE pzH 2)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pzH)) (.seq eViewP
    (.seq (.assign .local pzV (.load .one (vv lRp)))
    (.seq (.assign .local pzSl (.load .one (vv pzS)))
    (.seq (.call (some (some (.local, pzI), none)) fPo [vv pzS, vv pzSl, vv pzV])
    (.seq (.call (some (some (.local, pzR), none)) fInternSort [vv pzI]) (.return (vv pzR)))))))))
    hang))))))

section
variable {σ : Type}

theorem po_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ poLocals → (ctxEnv C ++ poParams.zip vals).get x = none :=
  Knot.params_none C poLocals poParams vals (by decide) (by decide)

/-- A level handle, the heap extended, any final state. -/
def PostLX (C : Ctx) (r : LIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ w = Enc.idxW r ∧ SR (ctxH C H') s' st

theorem postLX_locals (C : Ctx) : ∀ (a : LIdx) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostLX C a w s' st → PostLX C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, sr_of_eq hsr rfl rfl rfl rfl⟩

theorem po_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hci : C.code.lookup fInternLImax = some ([(lEu, .one), (lEv, .one)], internLImaxBody, .one))
    (hcp : C.code.lookup fPo = some (poParams.map (fun p => (p, ShapeHOL.one)), poBody, .one))
    (stk : List LIdx) (o : Nat) (hsl : stk.length < 2 ^ 58) :
    ∀ n (v : LIdx) (H : List (BitVec 64)) (s : AState), C.H <+: H → BlkAt H o (stk.map Enc.idxW) → n ≤ stk.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (poParams.zip [cellA C o, BitVec.ofNat 64 n, Enc.idxW v])) poBody s
        (inferPisOut stk.toArray n v) (PostLX (ctxH C H)) := by
  intro n
  induction n with
  | zero =>
    intro v H s hp hb hn
    refine specR_prologue (postLX_locals _) (po_none _ _) ?_
    rw [inferPisOut]
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, poParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [↓reduceIte]
    exact specR_returnI _ (Enc.idxW v) (by simp +decide [Env.get, poParams, ctxEnv])
      (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ n ih =>
    intro v H s hp hb hn
    refine specR_prologue (postLX_locals _) (po_none _ _) ?_
    rw [inferPisOut]
    have hne := ofNat_succ_ne n (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, poParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [show ¬ (n + 1 = 0) from by omega, ↓reduceIte, Nat.add_sub_cancel]
    refine specR_assignI poJ _ (BitVec.ofNat 64 n) (by decide)
      (by simp +decide [sev, Env.get, poParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _) ?_
    have hn' : n < stk.length := by omega
    have h1 := hb.2 n (by simpa using hn')
    rw [List.getElem_map] at h1
    refine UD.specR_heapLoadI' (C := ctxH C H) poA _ (o + 1 + n) (Enc.idxW stk[n]) h1 (by decide)
      (by simp +decide [sev, Env.get, poParams, ctxEnv]; show _ = cellA C (o + 1 + n); rw [← cellA_shl C (o + 1) n (by omega), ← cellA_add8]; rfl) ?_
    have hgx : stk.toArray[n]! = stk[n] := by simp [hn']
    rw [hgx]
    refine callLN (C := ctxH C H) poW fInternLImax [lEu, lEv] [vv poA, vv poV] internLImaxBody
      [Enc.idxW stk[n], Enc.idxW v] (by decide) rfl (by decide) hci
      ⟨by simp, by simp +decide [Env.get, poParams, ctxEnv], trivial⟩ (.imax stk[n] v)
      (internLImax_body_spec ra (ctxH C H) (ctxOK_H hok H) s stk[n] v) (fun v2 s1 _ => ?_)
    refine specR_congr (m' := inferPisOut stk.toArray n v2 >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H) poR fPo poParams [vv poS, vv poJ, vv poW] poBody
      [cellA C o, BitVec.ofNat 64 n, Enc.idxW v2] (by decide) rfl (by decide) hcp
      ⟨by simp +decide [Env.get, poParams, ctxEnv] <;> rfl, by simp, by simp, trivial⟩
      (PostLX (ctxH C H)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu poParams _ rfl hlk) (ih v2 H s1 hp hb (by omega)))
      (fun r w s2 H2 hp2 hw => ?_)
    subst hw
    exact specR_returnI _ (Enc.idxW r) (by simp) (fun t ht => ⟨H2, hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem pz_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ pzLocals → (ctxEnv C ++ pzParams.zip vals).get x = none :=
  Knot.params_none C pzLocals pzParams vals (by decide) (by decide)

structure PzCodes (C : Ctx) : Prop where
  i : C.code.lookup fI = some (pmap kParams, inferE C fIB, .one)
  w : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one)
  irr : C.code.lookup ExQ.fIrr = some (ExQ.irrParams.map (fun p => (p, ShapeHOL.one)), ExQ.irrBody C, .one)
  q : ExQ.CodesQ C
  po : C.code.lookup fPo = some (poParams.map (fun p => (p, ShapeHOL.one)), poBody, .one)
  lim : C.code.lookup fInternLImax = some ([(lEu, .one), (lEv, .one)], internLImaxBody, .one)
  srt : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one)

theorem pz_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (hc : PzCodes C)
    (hI : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (inferE C fIB) s1 ((knot mode C n).infer d' e')
      (PostK (ctxH C H)))
    (hW : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d' e')
      (PostK (ctxH C H)))
    (s : AState) (d k : Nat) (t : EIdx) (fvs : List EIdx) (stk : List LIdx) (ofv ost : Nat)
    (H : List (BitVec 64)) (hp : C.H <+: H) (hbf : BlkAt H ofv (fvs.map Enc.idxW))
    (hbs : BlkAt H ost (stk.map Enc.idxW)) (hfl : fvs.length < 2 ^ 58) (hsl : stk.length < 2 ^ 58)
    (hdk : d + k < 2 ^ 63) :
    SpecR (σ := σ) (Pre (ctxH C H) s (pzParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW t,
      BitVec.ofNat 64 k, cellA C ofv, cellA C ost])) pzBody s
      (inferPisLeaf (knot mode C n) C.fe d t k fvs.toArray stk.toArray) (PostK (ctxH C H)) := by
  refine specR_prologue (postK_locals _) (pz_none _ _) ?_
  unfold inferPisLeaf ensureSort
  simp only [bind_assoc, instantiateListFast, List.size_toArray]
  obtain ⟨hlo, hlv0⟩ := blkAt_get0 hbf
  refine UD.specR_heapLoadI' (C := ctxH C H) pzL (vv pzF) ofv (BitVec.ofNat 64 fvs.length)
    (by show H[ofv]? = _; rw [List.getElem?_eq_getElem hlo, hlv0]; simp) (by decide)
    (by simp +decide [Env.get, pzParams, ctxEnv]; rfl) ?_
  refine ILP.callE_spec (C := ctxH C H) pzO ExQ.fIrr ExQ.irrParams
    [vv pzF, .const 0, vv pzL, .const (BitVec.ofNat 64 coreWalkFuel), vv pzT, .const 0] (ExQ.irrBody C)
    [cellA C ofv, BitVec.ofNat 64 0, BitVec.ofNat 64 fvs.length, BitVec.ofNat 64 coreWalkFuel, Enc.idxW t,
      BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.irr
    ⟨by simp +decide [Env.get, pzParams, ctxEnv] <;> rfl, rfl, by simp, rfl, by simp +decide [Env.get, pzParams, ctxEnv],
      rfl, trivial⟩
    (ExQ.irr_spec ra (ctxH C H) (ctxOK_H hok H) (codesQ_H hc.q H) fvs.toArray ofv
      (show BlkAt H ofv (fvs.toArray.toList.map Enc.idxW) by simpa using hbf) (by simp; omega) s
      coreWalkFuel 0 fvs.length 0 t CV.coreWalkFuel_lt (by decide) (by omega) (by decide)) (fun ob s1 => ?_)
  refine specR_assignI pzDk _ (BitVec.ofNat 64 (d + k)) (by decide)
    (by simp +decide [sev, Env.get, pzParams, ctxEnv]; exact BitVec.ofNat_add_ofNat ..) ?_
  refine Big.specR_callKC (C := ctxH C H) pzB fI kParams [vv kFu, vv pzDk, vv pzO] (inferE C fIB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 (d + k), Enc.idxW ob] (by decide) rfl (by decide) hc.i
    ⟨by simp +decide [Env.get, pzParams, ctxEnv], by simp, by simp, trivial⟩ (hI H s1 (d + k) ob hp)
    (fun bt s2 H2 hp2 _ => ?_)
  refine Big.specR_callKC (C := ctxH C H2) pzH fW kParams [vv kFu, vv pzDk, vv pzB] (whnfE C fWB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 (d + k), Enc.idxW bt] (by decide) rfl (by decide) hc.w
    ⟨by simp +decide [Env.get, pzParams, ctxEnv], by simp, by simp, trivial⟩ (hW H2 s2 (d + k) bt (hp.trans hp2))
    (fun hh s3 H3 hp3 _ => ?_)
  have hp13 : H <+: H3 := hp2.trans hp3
  refine Knot.specR_tagIteV pzH hh 2 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
  · rw [if_pos (show (hh.tag == ETag.sort) = true by simp [htg, ETag.sort])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv pzH) (Enc.idxW hh) (by decide) (by simp) ?_
    refine specR_viewP (C := ctxH C H3) hh (by simp) (by simp +decide [Env.get] <;> rfl)
      (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun vw P hv htn _ => ?_)
    simp only [bind_assoc]
    refine specR_congr (view_bind_eq hh vw _ s3 hv) ?_
    have h2 : vw.tagN = 2 := by rw [htn, htg]; rfl
    obtain ⟨u, rfl⟩ : ∃ u, vw = .sort u := by cases vw <;> simp [ENodeView.tagN] at h2 ⊢
    simp only [pure_bind]
    refine specR_loadI' pzV (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW u) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encSort] using wordsAt_mem0 P (Enc.idxW u) [] []) ?_
    refine specR_dropM ?_
    have hbs3 := blkAt_mono hbs hp13
    obtain ⟨hlo2, hlv2⟩ := blkAt_get0 hbs3
    refine UD.specR_heapLoadI' (C := ctxH C H3) pzSl (vv pzS) ost (BitVec.ofNat 64 stk.length)
      (by show H3[ost]? = _; rw [List.getElem?_eq_getElem hlo2, hlv2]; simp) (by decide)
      (by simp +decide [Env.get, pzParams, ctxEnv]; rfl) ?_
    refine specR_callNIH (C := ctxH C H3) pzI fPo poParams [vv pzS, vv pzSl, vv pzV] poBody
      [cellA C ost, BitVec.ofNat 64 stk.length, Enc.idxW u] (by decide) rfl (by decide) hc.po
      ⟨by simp +decide [Env.get, pzParams, ctxEnv] <;> rfl, by simp, by simp, trivial⟩
      (PostLX (ctxH C H3)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu poParams _ rfl hlk)
        (po_spec ra C hok hc.lim hc.po stk ost hsl stk.length u H3 s3 (hp.trans hp13) hbs3 (le_refl _)))
      (fun iv w s4 H4 hp4 hw => ?_)
    subst hw
    refine specR_bindPure ?_
    refine ILP.callE_spec (C := ctxH C H4) pzR fInternSort [lEu] [vv pzI] sortBody [Enc.idxW iv] (by decide) rfl
      (by decide) hc.srt ⟨by simp, trivial⟩ (sort_body_spec ra (ctxH C H4) (ctxOK_H hok H4) s4 iv) (fun r s5 => ?_)
    exact specR_returnI _ (Enc.idxW r) (by simp)
      (fun t ht => ⟨H4, hp13.trans hp4, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · rw [if_neg (show ¬ (hh.tag == ETag.sort) = true by simpa [ETag.sort] using htg)]
    exact specR_hangI

end

end ConPanqueque.T.WC
