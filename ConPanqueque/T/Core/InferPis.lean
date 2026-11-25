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

def tqP := ofString "tqn_p"
def tqT := ofString "tqn_t"
def tqK := ofString "tqn_k"
def tqF := ofString "tqn_f"
def tqS := ofString "tqn_s"
def tqTy := ofString "tqn_ty"
def tqB := ofString "tqn_b"
def tqL := ofString "tqn_l"
def tqO := ofString "tqn_o"
def tqDk := ofString "tqn_dk"
def tqA := ofString "tqn_a"
def tqH := ofString "tqn_h"
def tqU := ofString "tqn_u"
def tqV := ofString "tqn_v"
def tqF2 := ofString "tqn_f2"
def tqS2 := ofString "tqn_s2"
def tqR := ofString "tqn_r"
def fTq := ofString "inferPis"

@[simp] theorem tq_tqP_ne_tqT : tqP ≠ tqT := by decide
@[simp] theorem tq_tqP_ne_tqK : tqP ≠ tqK := by decide
@[simp] theorem tq_tqP_ne_tqF : tqP ≠ tqF := by decide
@[simp] theorem tq_tqP_ne_tqS : tqP ≠ tqS := by decide
@[simp] theorem tq_tqP_ne_tqTy : tqP ≠ tqTy := by decide
@[simp] theorem tq_tqP_ne_tqB : tqP ≠ tqB := by decide
@[simp] theorem tq_tqP_ne_tqL : tqP ≠ tqL := by decide
@[simp] theorem tq_tqP_ne_tqO : tqP ≠ tqO := by decide
@[simp] theorem tq_tqP_ne_tqDk : tqP ≠ tqDk := by decide
@[simp] theorem tq_tqP_ne_tqA : tqP ≠ tqA := by decide
@[simp] theorem tq_tqP_ne_tqH : tqP ≠ tqH := by decide
@[simp] theorem tq_tqP_ne_tqU : tqP ≠ tqU := by decide
@[simp] theorem tq_tqP_ne_tqV : tqP ≠ tqV := by decide
@[simp] theorem tq_tqP_ne_tqF2 : tqP ≠ tqF2 := by decide
@[simp] theorem tq_tqP_ne_tqS2 : tqP ≠ tqS2 := by decide
@[simp] theorem tq_tqP_ne_tqR : tqP ≠ tqR := by decide
@[simp] theorem tq_tqP_ne_lKb : tqP ≠ lKb := by decide
@[simp] theorem tq_tqP_ne_kFu : tqP ≠ kFu := by decide
@[simp] theorem tq_tqP_ne_kD : tqP ≠ kD := by decide
@[simp] theorem tq_tqP_ne_lFl : tqP ≠ lFl := by decide
@[simp] theorem tq_tqP_ne_lDh : tqP ≠ lDh := by decide
@[simp] theorem tq_tqP_ne_lDt : tqP ≠ lDt := by decide
@[simp] theorem tq_tqP_ne_lDg : tqP ≠ lDg := by decide
@[simp] theorem tq_tqP_ne_lDi : tqP ≠ lDi := by decide
@[simp] theorem tq_tqP_ne_lRp : tqP ≠ lRp := by decide
@[simp] theorem tq_tqP_ne_lRn : tqP ≠ lRn := by decide
@[simp] theorem tq_tqP_ne_lFle : tqP ≠ lFle := by decide
@[simp] theorem tq_tqP_ne_lDir : tqP ≠ lDir := by decide
@[simp] theorem tq_tqT_ne_tqP : tqT ≠ tqP := by decide
@[simp] theorem tq_tqT_ne_tqK : tqT ≠ tqK := by decide
@[simp] theorem tq_tqT_ne_tqF : tqT ≠ tqF := by decide
@[simp] theorem tq_tqT_ne_tqS : tqT ≠ tqS := by decide
@[simp] theorem tq_tqT_ne_tqTy : tqT ≠ tqTy := by decide
@[simp] theorem tq_tqT_ne_tqB : tqT ≠ tqB := by decide
@[simp] theorem tq_tqT_ne_tqL : tqT ≠ tqL := by decide
@[simp] theorem tq_tqT_ne_tqO : tqT ≠ tqO := by decide
@[simp] theorem tq_tqT_ne_tqDk : tqT ≠ tqDk := by decide
@[simp] theorem tq_tqT_ne_tqA : tqT ≠ tqA := by decide
@[simp] theorem tq_tqT_ne_tqH : tqT ≠ tqH := by decide
@[simp] theorem tq_tqT_ne_tqU : tqT ≠ tqU := by decide
@[simp] theorem tq_tqT_ne_tqV : tqT ≠ tqV := by decide
@[simp] theorem tq_tqT_ne_tqF2 : tqT ≠ tqF2 := by decide
@[simp] theorem tq_tqT_ne_tqS2 : tqT ≠ tqS2 := by decide
@[simp] theorem tq_tqT_ne_tqR : tqT ≠ tqR := by decide
@[simp] theorem tq_tqT_ne_lKb : tqT ≠ lKb := by decide
@[simp] theorem tq_tqT_ne_kFu : tqT ≠ kFu := by decide
@[simp] theorem tq_tqT_ne_kD : tqT ≠ kD := by decide
@[simp] theorem tq_tqT_ne_lFl : tqT ≠ lFl := by decide
@[simp] theorem tq_tqT_ne_lDh : tqT ≠ lDh := by decide
@[simp] theorem tq_tqT_ne_lDt : tqT ≠ lDt := by decide
@[simp] theorem tq_tqT_ne_lDg : tqT ≠ lDg := by decide
@[simp] theorem tq_tqT_ne_lDi : tqT ≠ lDi := by decide
@[simp] theorem tq_tqT_ne_lRp : tqT ≠ lRp := by decide
@[simp] theorem tq_tqT_ne_lRn : tqT ≠ lRn := by decide
@[simp] theorem tq_tqT_ne_lFle : tqT ≠ lFle := by decide
@[simp] theorem tq_tqT_ne_lDir : tqT ≠ lDir := by decide
@[simp] theorem tq_tqK_ne_tqP : tqK ≠ tqP := by decide
@[simp] theorem tq_tqK_ne_tqT : tqK ≠ tqT := by decide
@[simp] theorem tq_tqK_ne_tqF : tqK ≠ tqF := by decide
@[simp] theorem tq_tqK_ne_tqS : tqK ≠ tqS := by decide
@[simp] theorem tq_tqK_ne_tqTy : tqK ≠ tqTy := by decide
@[simp] theorem tq_tqK_ne_tqB : tqK ≠ tqB := by decide
@[simp] theorem tq_tqK_ne_tqL : tqK ≠ tqL := by decide
@[simp] theorem tq_tqK_ne_tqO : tqK ≠ tqO := by decide
@[simp] theorem tq_tqK_ne_tqDk : tqK ≠ tqDk := by decide
@[simp] theorem tq_tqK_ne_tqA : tqK ≠ tqA := by decide
@[simp] theorem tq_tqK_ne_tqH : tqK ≠ tqH := by decide
@[simp] theorem tq_tqK_ne_tqU : tqK ≠ tqU := by decide
@[simp] theorem tq_tqK_ne_tqV : tqK ≠ tqV := by decide
@[simp] theorem tq_tqK_ne_tqF2 : tqK ≠ tqF2 := by decide
@[simp] theorem tq_tqK_ne_tqS2 : tqK ≠ tqS2 := by decide
@[simp] theorem tq_tqK_ne_tqR : tqK ≠ tqR := by decide
@[simp] theorem tq_tqK_ne_lKb : tqK ≠ lKb := by decide
@[simp] theorem tq_tqK_ne_kFu : tqK ≠ kFu := by decide
@[simp] theorem tq_tqK_ne_kD : tqK ≠ kD := by decide
@[simp] theorem tq_tqK_ne_lFl : tqK ≠ lFl := by decide
@[simp] theorem tq_tqK_ne_lDh : tqK ≠ lDh := by decide
@[simp] theorem tq_tqK_ne_lDt : tqK ≠ lDt := by decide
@[simp] theorem tq_tqK_ne_lDg : tqK ≠ lDg := by decide
@[simp] theorem tq_tqK_ne_lDi : tqK ≠ lDi := by decide
@[simp] theorem tq_tqK_ne_lRp : tqK ≠ lRp := by decide
@[simp] theorem tq_tqK_ne_lRn : tqK ≠ lRn := by decide
@[simp] theorem tq_tqK_ne_lFle : tqK ≠ lFle := by decide
@[simp] theorem tq_tqK_ne_lDir : tqK ≠ lDir := by decide
@[simp] theorem tq_tqF_ne_tqP : tqF ≠ tqP := by decide
@[simp] theorem tq_tqF_ne_tqT : tqF ≠ tqT := by decide
@[simp] theorem tq_tqF_ne_tqK : tqF ≠ tqK := by decide
@[simp] theorem tq_tqF_ne_tqS : tqF ≠ tqS := by decide
@[simp] theorem tq_tqF_ne_tqTy : tqF ≠ tqTy := by decide
@[simp] theorem tq_tqF_ne_tqB : tqF ≠ tqB := by decide
@[simp] theorem tq_tqF_ne_tqL : tqF ≠ tqL := by decide
@[simp] theorem tq_tqF_ne_tqO : tqF ≠ tqO := by decide
@[simp] theorem tq_tqF_ne_tqDk : tqF ≠ tqDk := by decide
@[simp] theorem tq_tqF_ne_tqA : tqF ≠ tqA := by decide
@[simp] theorem tq_tqF_ne_tqH : tqF ≠ tqH := by decide
@[simp] theorem tq_tqF_ne_tqU : tqF ≠ tqU := by decide
@[simp] theorem tq_tqF_ne_tqV : tqF ≠ tqV := by decide
@[simp] theorem tq_tqF_ne_tqF2 : tqF ≠ tqF2 := by decide
@[simp] theorem tq_tqF_ne_tqS2 : tqF ≠ tqS2 := by decide
@[simp] theorem tq_tqF_ne_tqR : tqF ≠ tqR := by decide
@[simp] theorem tq_tqF_ne_lKb : tqF ≠ lKb := by decide
@[simp] theorem tq_tqF_ne_kFu : tqF ≠ kFu := by decide
@[simp] theorem tq_tqF_ne_kD : tqF ≠ kD := by decide
@[simp] theorem tq_tqF_ne_lFl : tqF ≠ lFl := by decide
@[simp] theorem tq_tqF_ne_lDh : tqF ≠ lDh := by decide
@[simp] theorem tq_tqF_ne_lDt : tqF ≠ lDt := by decide
@[simp] theorem tq_tqF_ne_lDg : tqF ≠ lDg := by decide
@[simp] theorem tq_tqF_ne_lDi : tqF ≠ lDi := by decide
@[simp] theorem tq_tqF_ne_lRp : tqF ≠ lRp := by decide
@[simp] theorem tq_tqF_ne_lRn : tqF ≠ lRn := by decide
@[simp] theorem tq_tqF_ne_lFle : tqF ≠ lFle := by decide
@[simp] theorem tq_tqF_ne_lDir : tqF ≠ lDir := by decide
@[simp] theorem tq_tqS_ne_tqP : tqS ≠ tqP := by decide
@[simp] theorem tq_tqS_ne_tqT : tqS ≠ tqT := by decide
@[simp] theorem tq_tqS_ne_tqK : tqS ≠ tqK := by decide
@[simp] theorem tq_tqS_ne_tqF : tqS ≠ tqF := by decide
@[simp] theorem tq_tqS_ne_tqTy : tqS ≠ tqTy := by decide
@[simp] theorem tq_tqS_ne_tqB : tqS ≠ tqB := by decide
@[simp] theorem tq_tqS_ne_tqL : tqS ≠ tqL := by decide
@[simp] theorem tq_tqS_ne_tqO : tqS ≠ tqO := by decide
@[simp] theorem tq_tqS_ne_tqDk : tqS ≠ tqDk := by decide
@[simp] theorem tq_tqS_ne_tqA : tqS ≠ tqA := by decide
@[simp] theorem tq_tqS_ne_tqH : tqS ≠ tqH := by decide
@[simp] theorem tq_tqS_ne_tqU : tqS ≠ tqU := by decide
@[simp] theorem tq_tqS_ne_tqV : tqS ≠ tqV := by decide
@[simp] theorem tq_tqS_ne_tqF2 : tqS ≠ tqF2 := by decide
@[simp] theorem tq_tqS_ne_tqS2 : tqS ≠ tqS2 := by decide
@[simp] theorem tq_tqS_ne_tqR : tqS ≠ tqR := by decide
@[simp] theorem tq_tqS_ne_lKb : tqS ≠ lKb := by decide
@[simp] theorem tq_tqS_ne_kFu : tqS ≠ kFu := by decide
@[simp] theorem tq_tqS_ne_kD : tqS ≠ kD := by decide
@[simp] theorem tq_tqS_ne_lFl : tqS ≠ lFl := by decide
@[simp] theorem tq_tqS_ne_lDh : tqS ≠ lDh := by decide
@[simp] theorem tq_tqS_ne_lDt : tqS ≠ lDt := by decide
@[simp] theorem tq_tqS_ne_lDg : tqS ≠ lDg := by decide
@[simp] theorem tq_tqS_ne_lDi : tqS ≠ lDi := by decide
@[simp] theorem tq_tqS_ne_lRp : tqS ≠ lRp := by decide
@[simp] theorem tq_tqS_ne_lRn : tqS ≠ lRn := by decide
@[simp] theorem tq_tqS_ne_lFle : tqS ≠ lFle := by decide
@[simp] theorem tq_tqS_ne_lDir : tqS ≠ lDir := by decide
@[simp] theorem tq_tqTy_ne_tqP : tqTy ≠ tqP := by decide
@[simp] theorem tq_tqTy_ne_tqT : tqTy ≠ tqT := by decide
@[simp] theorem tq_tqTy_ne_tqK : tqTy ≠ tqK := by decide
@[simp] theorem tq_tqTy_ne_tqF : tqTy ≠ tqF := by decide
@[simp] theorem tq_tqTy_ne_tqS : tqTy ≠ tqS := by decide
@[simp] theorem tq_tqTy_ne_tqB : tqTy ≠ tqB := by decide
@[simp] theorem tq_tqTy_ne_tqL : tqTy ≠ tqL := by decide
@[simp] theorem tq_tqTy_ne_tqO : tqTy ≠ tqO := by decide
@[simp] theorem tq_tqTy_ne_tqDk : tqTy ≠ tqDk := by decide
@[simp] theorem tq_tqTy_ne_tqA : tqTy ≠ tqA := by decide
@[simp] theorem tq_tqTy_ne_tqH : tqTy ≠ tqH := by decide
@[simp] theorem tq_tqTy_ne_tqU : tqTy ≠ tqU := by decide
@[simp] theorem tq_tqTy_ne_tqV : tqTy ≠ tqV := by decide
@[simp] theorem tq_tqTy_ne_tqF2 : tqTy ≠ tqF2 := by decide
@[simp] theorem tq_tqTy_ne_tqS2 : tqTy ≠ tqS2 := by decide
@[simp] theorem tq_tqTy_ne_tqR : tqTy ≠ tqR := by decide
@[simp] theorem tq_tqTy_ne_lKb : tqTy ≠ lKb := by decide
@[simp] theorem tq_tqTy_ne_kFu : tqTy ≠ kFu := by decide
@[simp] theorem tq_tqTy_ne_kD : tqTy ≠ kD := by decide
@[simp] theorem tq_tqTy_ne_lFl : tqTy ≠ lFl := by decide
@[simp] theorem tq_tqTy_ne_lDh : tqTy ≠ lDh := by decide
@[simp] theorem tq_tqTy_ne_lDt : tqTy ≠ lDt := by decide
@[simp] theorem tq_tqTy_ne_lDg : tqTy ≠ lDg := by decide
@[simp] theorem tq_tqTy_ne_lDi : tqTy ≠ lDi := by decide
@[simp] theorem tq_tqTy_ne_lRp : tqTy ≠ lRp := by decide
@[simp] theorem tq_tqTy_ne_lRn : tqTy ≠ lRn := by decide
@[simp] theorem tq_tqTy_ne_lFle : tqTy ≠ lFle := by decide
@[simp] theorem tq_tqTy_ne_lDir : tqTy ≠ lDir := by decide
@[simp] theorem tq_tqB_ne_tqP : tqB ≠ tqP := by decide
@[simp] theorem tq_tqB_ne_tqT : tqB ≠ tqT := by decide
@[simp] theorem tq_tqB_ne_tqK : tqB ≠ tqK := by decide
@[simp] theorem tq_tqB_ne_tqF : tqB ≠ tqF := by decide
@[simp] theorem tq_tqB_ne_tqS : tqB ≠ tqS := by decide
@[simp] theorem tq_tqB_ne_tqTy : tqB ≠ tqTy := by decide
@[simp] theorem tq_tqB_ne_tqL : tqB ≠ tqL := by decide
@[simp] theorem tq_tqB_ne_tqO : tqB ≠ tqO := by decide
@[simp] theorem tq_tqB_ne_tqDk : tqB ≠ tqDk := by decide
@[simp] theorem tq_tqB_ne_tqA : tqB ≠ tqA := by decide
@[simp] theorem tq_tqB_ne_tqH : tqB ≠ tqH := by decide
@[simp] theorem tq_tqB_ne_tqU : tqB ≠ tqU := by decide
@[simp] theorem tq_tqB_ne_tqV : tqB ≠ tqV := by decide
@[simp] theorem tq_tqB_ne_tqF2 : tqB ≠ tqF2 := by decide
@[simp] theorem tq_tqB_ne_tqS2 : tqB ≠ tqS2 := by decide
@[simp] theorem tq_tqB_ne_tqR : tqB ≠ tqR := by decide
@[simp] theorem tq_tqB_ne_lKb : tqB ≠ lKb := by decide
@[simp] theorem tq_tqB_ne_kFu : tqB ≠ kFu := by decide
@[simp] theorem tq_tqB_ne_kD : tqB ≠ kD := by decide
@[simp] theorem tq_tqB_ne_lFl : tqB ≠ lFl := by decide
@[simp] theorem tq_tqB_ne_lDh : tqB ≠ lDh := by decide
@[simp] theorem tq_tqB_ne_lDt : tqB ≠ lDt := by decide
@[simp] theorem tq_tqB_ne_lDg : tqB ≠ lDg := by decide
@[simp] theorem tq_tqB_ne_lDi : tqB ≠ lDi := by decide
@[simp] theorem tq_tqB_ne_lRp : tqB ≠ lRp := by decide
@[simp] theorem tq_tqB_ne_lRn : tqB ≠ lRn := by decide
@[simp] theorem tq_tqB_ne_lFle : tqB ≠ lFle := by decide
@[simp] theorem tq_tqB_ne_lDir : tqB ≠ lDir := by decide
@[simp] theorem tq_tqL_ne_tqP : tqL ≠ tqP := by decide
@[simp] theorem tq_tqL_ne_tqT : tqL ≠ tqT := by decide
@[simp] theorem tq_tqL_ne_tqK : tqL ≠ tqK := by decide
@[simp] theorem tq_tqL_ne_tqF : tqL ≠ tqF := by decide
@[simp] theorem tq_tqL_ne_tqS : tqL ≠ tqS := by decide
@[simp] theorem tq_tqL_ne_tqTy : tqL ≠ tqTy := by decide
@[simp] theorem tq_tqL_ne_tqB : tqL ≠ tqB := by decide
@[simp] theorem tq_tqL_ne_tqO : tqL ≠ tqO := by decide
@[simp] theorem tq_tqL_ne_tqDk : tqL ≠ tqDk := by decide
@[simp] theorem tq_tqL_ne_tqA : tqL ≠ tqA := by decide
@[simp] theorem tq_tqL_ne_tqH : tqL ≠ tqH := by decide
@[simp] theorem tq_tqL_ne_tqU : tqL ≠ tqU := by decide
@[simp] theorem tq_tqL_ne_tqV : tqL ≠ tqV := by decide
@[simp] theorem tq_tqL_ne_tqF2 : tqL ≠ tqF2 := by decide
@[simp] theorem tq_tqL_ne_tqS2 : tqL ≠ tqS2 := by decide
@[simp] theorem tq_tqL_ne_tqR : tqL ≠ tqR := by decide
@[simp] theorem tq_tqL_ne_lKb : tqL ≠ lKb := by decide
@[simp] theorem tq_tqL_ne_kFu : tqL ≠ kFu := by decide
@[simp] theorem tq_tqL_ne_kD : tqL ≠ kD := by decide
@[simp] theorem tq_tqL_ne_lFl : tqL ≠ lFl := by decide
@[simp] theorem tq_tqL_ne_lDh : tqL ≠ lDh := by decide
@[simp] theorem tq_tqL_ne_lDt : tqL ≠ lDt := by decide
@[simp] theorem tq_tqL_ne_lDg : tqL ≠ lDg := by decide
@[simp] theorem tq_tqL_ne_lDi : tqL ≠ lDi := by decide
@[simp] theorem tq_tqL_ne_lRp : tqL ≠ lRp := by decide
@[simp] theorem tq_tqL_ne_lRn : tqL ≠ lRn := by decide
@[simp] theorem tq_tqL_ne_lFle : tqL ≠ lFle := by decide
@[simp] theorem tq_tqL_ne_lDir : tqL ≠ lDir := by decide
@[simp] theorem tq_tqO_ne_tqP : tqO ≠ tqP := by decide
@[simp] theorem tq_tqO_ne_tqT : tqO ≠ tqT := by decide
@[simp] theorem tq_tqO_ne_tqK : tqO ≠ tqK := by decide
@[simp] theorem tq_tqO_ne_tqF : tqO ≠ tqF := by decide
@[simp] theorem tq_tqO_ne_tqS : tqO ≠ tqS := by decide
@[simp] theorem tq_tqO_ne_tqTy : tqO ≠ tqTy := by decide
@[simp] theorem tq_tqO_ne_tqB : tqO ≠ tqB := by decide
@[simp] theorem tq_tqO_ne_tqL : tqO ≠ tqL := by decide
@[simp] theorem tq_tqO_ne_tqDk : tqO ≠ tqDk := by decide
@[simp] theorem tq_tqO_ne_tqA : tqO ≠ tqA := by decide
@[simp] theorem tq_tqO_ne_tqH : tqO ≠ tqH := by decide
@[simp] theorem tq_tqO_ne_tqU : tqO ≠ tqU := by decide
@[simp] theorem tq_tqO_ne_tqV : tqO ≠ tqV := by decide
@[simp] theorem tq_tqO_ne_tqF2 : tqO ≠ tqF2 := by decide
@[simp] theorem tq_tqO_ne_tqS2 : tqO ≠ tqS2 := by decide
@[simp] theorem tq_tqO_ne_tqR : tqO ≠ tqR := by decide
@[simp] theorem tq_tqO_ne_lKb : tqO ≠ lKb := by decide
@[simp] theorem tq_tqO_ne_kFu : tqO ≠ kFu := by decide
@[simp] theorem tq_tqO_ne_kD : tqO ≠ kD := by decide
@[simp] theorem tq_tqO_ne_lFl : tqO ≠ lFl := by decide
@[simp] theorem tq_tqO_ne_lDh : tqO ≠ lDh := by decide
@[simp] theorem tq_tqO_ne_lDt : tqO ≠ lDt := by decide
@[simp] theorem tq_tqO_ne_lDg : tqO ≠ lDg := by decide
@[simp] theorem tq_tqO_ne_lDi : tqO ≠ lDi := by decide
@[simp] theorem tq_tqO_ne_lRp : tqO ≠ lRp := by decide
@[simp] theorem tq_tqO_ne_lRn : tqO ≠ lRn := by decide
@[simp] theorem tq_tqO_ne_lFle : tqO ≠ lFle := by decide
@[simp] theorem tq_tqO_ne_lDir : tqO ≠ lDir := by decide
@[simp] theorem tq_tqDk_ne_tqP : tqDk ≠ tqP := by decide
@[simp] theorem tq_tqDk_ne_tqT : tqDk ≠ tqT := by decide
@[simp] theorem tq_tqDk_ne_tqK : tqDk ≠ tqK := by decide
@[simp] theorem tq_tqDk_ne_tqF : tqDk ≠ tqF := by decide
@[simp] theorem tq_tqDk_ne_tqS : tqDk ≠ tqS := by decide
@[simp] theorem tq_tqDk_ne_tqTy : tqDk ≠ tqTy := by decide
@[simp] theorem tq_tqDk_ne_tqB : tqDk ≠ tqB := by decide
@[simp] theorem tq_tqDk_ne_tqL : tqDk ≠ tqL := by decide
@[simp] theorem tq_tqDk_ne_tqO : tqDk ≠ tqO := by decide
@[simp] theorem tq_tqDk_ne_tqA : tqDk ≠ tqA := by decide
@[simp] theorem tq_tqDk_ne_tqH : tqDk ≠ tqH := by decide
@[simp] theorem tq_tqDk_ne_tqU : tqDk ≠ tqU := by decide
@[simp] theorem tq_tqDk_ne_tqV : tqDk ≠ tqV := by decide
@[simp] theorem tq_tqDk_ne_tqF2 : tqDk ≠ tqF2 := by decide
@[simp] theorem tq_tqDk_ne_tqS2 : tqDk ≠ tqS2 := by decide
@[simp] theorem tq_tqDk_ne_tqR : tqDk ≠ tqR := by decide
@[simp] theorem tq_tqDk_ne_lKb : tqDk ≠ lKb := by decide
@[simp] theorem tq_tqDk_ne_kFu : tqDk ≠ kFu := by decide
@[simp] theorem tq_tqDk_ne_kD : tqDk ≠ kD := by decide
@[simp] theorem tq_tqDk_ne_lFl : tqDk ≠ lFl := by decide
@[simp] theorem tq_tqDk_ne_lDh : tqDk ≠ lDh := by decide
@[simp] theorem tq_tqDk_ne_lDt : tqDk ≠ lDt := by decide
@[simp] theorem tq_tqDk_ne_lDg : tqDk ≠ lDg := by decide
@[simp] theorem tq_tqDk_ne_lDi : tqDk ≠ lDi := by decide
@[simp] theorem tq_tqDk_ne_lRp : tqDk ≠ lRp := by decide
@[simp] theorem tq_tqDk_ne_lRn : tqDk ≠ lRn := by decide
@[simp] theorem tq_tqDk_ne_lFle : tqDk ≠ lFle := by decide
@[simp] theorem tq_tqDk_ne_lDir : tqDk ≠ lDir := by decide
@[simp] theorem tq_tqA_ne_tqP : tqA ≠ tqP := by decide
@[simp] theorem tq_tqA_ne_tqT : tqA ≠ tqT := by decide
@[simp] theorem tq_tqA_ne_tqK : tqA ≠ tqK := by decide
@[simp] theorem tq_tqA_ne_tqF : tqA ≠ tqF := by decide
@[simp] theorem tq_tqA_ne_tqS : tqA ≠ tqS := by decide
@[simp] theorem tq_tqA_ne_tqTy : tqA ≠ tqTy := by decide
@[simp] theorem tq_tqA_ne_tqB : tqA ≠ tqB := by decide
@[simp] theorem tq_tqA_ne_tqL : tqA ≠ tqL := by decide
@[simp] theorem tq_tqA_ne_tqO : tqA ≠ tqO := by decide
@[simp] theorem tq_tqA_ne_tqDk : tqA ≠ tqDk := by decide
@[simp] theorem tq_tqA_ne_tqH : tqA ≠ tqH := by decide
@[simp] theorem tq_tqA_ne_tqU : tqA ≠ tqU := by decide
@[simp] theorem tq_tqA_ne_tqV : tqA ≠ tqV := by decide
@[simp] theorem tq_tqA_ne_tqF2 : tqA ≠ tqF2 := by decide
@[simp] theorem tq_tqA_ne_tqS2 : tqA ≠ tqS2 := by decide
@[simp] theorem tq_tqA_ne_tqR : tqA ≠ tqR := by decide
@[simp] theorem tq_tqA_ne_lKb : tqA ≠ lKb := by decide
@[simp] theorem tq_tqA_ne_kFu : tqA ≠ kFu := by decide
@[simp] theorem tq_tqA_ne_kD : tqA ≠ kD := by decide
@[simp] theorem tq_tqA_ne_lFl : tqA ≠ lFl := by decide
@[simp] theorem tq_tqA_ne_lDh : tqA ≠ lDh := by decide
@[simp] theorem tq_tqA_ne_lDt : tqA ≠ lDt := by decide
@[simp] theorem tq_tqA_ne_lDg : tqA ≠ lDg := by decide
@[simp] theorem tq_tqA_ne_lDi : tqA ≠ lDi := by decide
@[simp] theorem tq_tqA_ne_lRp : tqA ≠ lRp := by decide
@[simp] theorem tq_tqA_ne_lRn : tqA ≠ lRn := by decide
@[simp] theorem tq_tqA_ne_lFle : tqA ≠ lFle := by decide
@[simp] theorem tq_tqA_ne_lDir : tqA ≠ lDir := by decide
@[simp] theorem tq_tqH_ne_tqP : tqH ≠ tqP := by decide
@[simp] theorem tq_tqH_ne_tqT : tqH ≠ tqT := by decide
@[simp] theorem tq_tqH_ne_tqK : tqH ≠ tqK := by decide
@[simp] theorem tq_tqH_ne_tqF : tqH ≠ tqF := by decide
@[simp] theorem tq_tqH_ne_tqS : tqH ≠ tqS := by decide
@[simp] theorem tq_tqH_ne_tqTy : tqH ≠ tqTy := by decide
@[simp] theorem tq_tqH_ne_tqB : tqH ≠ tqB := by decide
@[simp] theorem tq_tqH_ne_tqL : tqH ≠ tqL := by decide
@[simp] theorem tq_tqH_ne_tqO : tqH ≠ tqO := by decide
@[simp] theorem tq_tqH_ne_tqDk : tqH ≠ tqDk := by decide
@[simp] theorem tq_tqH_ne_tqA : tqH ≠ tqA := by decide
@[simp] theorem tq_tqH_ne_tqU : tqH ≠ tqU := by decide
@[simp] theorem tq_tqH_ne_tqV : tqH ≠ tqV := by decide
@[simp] theorem tq_tqH_ne_tqF2 : tqH ≠ tqF2 := by decide
@[simp] theorem tq_tqH_ne_tqS2 : tqH ≠ tqS2 := by decide
@[simp] theorem tq_tqH_ne_tqR : tqH ≠ tqR := by decide
@[simp] theorem tq_tqH_ne_lKb : tqH ≠ lKb := by decide
@[simp] theorem tq_tqH_ne_kFu : tqH ≠ kFu := by decide
@[simp] theorem tq_tqH_ne_kD : tqH ≠ kD := by decide
@[simp] theorem tq_tqH_ne_lFl : tqH ≠ lFl := by decide
@[simp] theorem tq_tqH_ne_lDh : tqH ≠ lDh := by decide
@[simp] theorem tq_tqH_ne_lDt : tqH ≠ lDt := by decide
@[simp] theorem tq_tqH_ne_lDg : tqH ≠ lDg := by decide
@[simp] theorem tq_tqH_ne_lDi : tqH ≠ lDi := by decide
@[simp] theorem tq_tqH_ne_lRp : tqH ≠ lRp := by decide
@[simp] theorem tq_tqH_ne_lRn : tqH ≠ lRn := by decide
@[simp] theorem tq_tqH_ne_lFle : tqH ≠ lFle := by decide
@[simp] theorem tq_tqH_ne_lDir : tqH ≠ lDir := by decide
@[simp] theorem tq_tqU_ne_tqP : tqU ≠ tqP := by decide
@[simp] theorem tq_tqU_ne_tqT : tqU ≠ tqT := by decide
@[simp] theorem tq_tqU_ne_tqK : tqU ≠ tqK := by decide
@[simp] theorem tq_tqU_ne_tqF : tqU ≠ tqF := by decide
@[simp] theorem tq_tqU_ne_tqS : tqU ≠ tqS := by decide
@[simp] theorem tq_tqU_ne_tqTy : tqU ≠ tqTy := by decide
@[simp] theorem tq_tqU_ne_tqB : tqU ≠ tqB := by decide
@[simp] theorem tq_tqU_ne_tqL : tqU ≠ tqL := by decide
@[simp] theorem tq_tqU_ne_tqO : tqU ≠ tqO := by decide
@[simp] theorem tq_tqU_ne_tqDk : tqU ≠ tqDk := by decide
@[simp] theorem tq_tqU_ne_tqA : tqU ≠ tqA := by decide
@[simp] theorem tq_tqU_ne_tqH : tqU ≠ tqH := by decide
@[simp] theorem tq_tqU_ne_tqV : tqU ≠ tqV := by decide
@[simp] theorem tq_tqU_ne_tqF2 : tqU ≠ tqF2 := by decide
@[simp] theorem tq_tqU_ne_tqS2 : tqU ≠ tqS2 := by decide
@[simp] theorem tq_tqU_ne_tqR : tqU ≠ tqR := by decide
@[simp] theorem tq_tqU_ne_lKb : tqU ≠ lKb := by decide
@[simp] theorem tq_tqU_ne_kFu : tqU ≠ kFu := by decide
@[simp] theorem tq_tqU_ne_kD : tqU ≠ kD := by decide
@[simp] theorem tq_tqU_ne_lFl : tqU ≠ lFl := by decide
@[simp] theorem tq_tqU_ne_lDh : tqU ≠ lDh := by decide
@[simp] theorem tq_tqU_ne_lDt : tqU ≠ lDt := by decide
@[simp] theorem tq_tqU_ne_lDg : tqU ≠ lDg := by decide
@[simp] theorem tq_tqU_ne_lDi : tqU ≠ lDi := by decide
@[simp] theorem tq_tqU_ne_lRp : tqU ≠ lRp := by decide
@[simp] theorem tq_tqU_ne_lRn : tqU ≠ lRn := by decide
@[simp] theorem tq_tqU_ne_lFle : tqU ≠ lFle := by decide
@[simp] theorem tq_tqU_ne_lDir : tqU ≠ lDir := by decide
@[simp] theorem tq_tqV_ne_tqP : tqV ≠ tqP := by decide
@[simp] theorem tq_tqV_ne_tqT : tqV ≠ tqT := by decide
@[simp] theorem tq_tqV_ne_tqK : tqV ≠ tqK := by decide
@[simp] theorem tq_tqV_ne_tqF : tqV ≠ tqF := by decide
@[simp] theorem tq_tqV_ne_tqS : tqV ≠ tqS := by decide
@[simp] theorem tq_tqV_ne_tqTy : tqV ≠ tqTy := by decide
@[simp] theorem tq_tqV_ne_tqB : tqV ≠ tqB := by decide
@[simp] theorem tq_tqV_ne_tqL : tqV ≠ tqL := by decide
@[simp] theorem tq_tqV_ne_tqO : tqV ≠ tqO := by decide
@[simp] theorem tq_tqV_ne_tqDk : tqV ≠ tqDk := by decide
@[simp] theorem tq_tqV_ne_tqA : tqV ≠ tqA := by decide
@[simp] theorem tq_tqV_ne_tqH : tqV ≠ tqH := by decide
@[simp] theorem tq_tqV_ne_tqU : tqV ≠ tqU := by decide
@[simp] theorem tq_tqV_ne_tqF2 : tqV ≠ tqF2 := by decide
@[simp] theorem tq_tqV_ne_tqS2 : tqV ≠ tqS2 := by decide
@[simp] theorem tq_tqV_ne_tqR : tqV ≠ tqR := by decide
@[simp] theorem tq_tqV_ne_lKb : tqV ≠ lKb := by decide
@[simp] theorem tq_tqV_ne_kFu : tqV ≠ kFu := by decide
@[simp] theorem tq_tqV_ne_kD : tqV ≠ kD := by decide
@[simp] theorem tq_tqV_ne_lFl : tqV ≠ lFl := by decide
@[simp] theorem tq_tqV_ne_lDh : tqV ≠ lDh := by decide
@[simp] theorem tq_tqV_ne_lDt : tqV ≠ lDt := by decide
@[simp] theorem tq_tqV_ne_lDg : tqV ≠ lDg := by decide
@[simp] theorem tq_tqV_ne_lDi : tqV ≠ lDi := by decide
@[simp] theorem tq_tqV_ne_lRp : tqV ≠ lRp := by decide
@[simp] theorem tq_tqV_ne_lRn : tqV ≠ lRn := by decide
@[simp] theorem tq_tqV_ne_lFle : tqV ≠ lFle := by decide
@[simp] theorem tq_tqV_ne_lDir : tqV ≠ lDir := by decide
@[simp] theorem tq_tqF2_ne_tqP : tqF2 ≠ tqP := by decide
@[simp] theorem tq_tqF2_ne_tqT : tqF2 ≠ tqT := by decide
@[simp] theorem tq_tqF2_ne_tqK : tqF2 ≠ tqK := by decide
@[simp] theorem tq_tqF2_ne_tqF : tqF2 ≠ tqF := by decide
@[simp] theorem tq_tqF2_ne_tqS : tqF2 ≠ tqS := by decide
@[simp] theorem tq_tqF2_ne_tqTy : tqF2 ≠ tqTy := by decide
@[simp] theorem tq_tqF2_ne_tqB : tqF2 ≠ tqB := by decide
@[simp] theorem tq_tqF2_ne_tqL : tqF2 ≠ tqL := by decide
@[simp] theorem tq_tqF2_ne_tqO : tqF2 ≠ tqO := by decide
@[simp] theorem tq_tqF2_ne_tqDk : tqF2 ≠ tqDk := by decide
@[simp] theorem tq_tqF2_ne_tqA : tqF2 ≠ tqA := by decide
@[simp] theorem tq_tqF2_ne_tqH : tqF2 ≠ tqH := by decide
@[simp] theorem tq_tqF2_ne_tqU : tqF2 ≠ tqU := by decide
@[simp] theorem tq_tqF2_ne_tqV : tqF2 ≠ tqV := by decide
@[simp] theorem tq_tqF2_ne_tqS2 : tqF2 ≠ tqS2 := by decide
@[simp] theorem tq_tqF2_ne_tqR : tqF2 ≠ tqR := by decide
@[simp] theorem tq_tqF2_ne_lKb : tqF2 ≠ lKb := by decide
@[simp] theorem tq_tqF2_ne_kFu : tqF2 ≠ kFu := by decide
@[simp] theorem tq_tqF2_ne_kD : tqF2 ≠ kD := by decide
@[simp] theorem tq_tqF2_ne_lFl : tqF2 ≠ lFl := by decide
@[simp] theorem tq_tqF2_ne_lDh : tqF2 ≠ lDh := by decide
@[simp] theorem tq_tqF2_ne_lDt : tqF2 ≠ lDt := by decide
@[simp] theorem tq_tqF2_ne_lDg : tqF2 ≠ lDg := by decide
@[simp] theorem tq_tqF2_ne_lDi : tqF2 ≠ lDi := by decide
@[simp] theorem tq_tqF2_ne_lRp : tqF2 ≠ lRp := by decide
@[simp] theorem tq_tqF2_ne_lRn : tqF2 ≠ lRn := by decide
@[simp] theorem tq_tqF2_ne_lFle : tqF2 ≠ lFle := by decide
@[simp] theorem tq_tqF2_ne_lDir : tqF2 ≠ lDir := by decide
@[simp] theorem tq_tqS2_ne_tqP : tqS2 ≠ tqP := by decide
@[simp] theorem tq_tqS2_ne_tqT : tqS2 ≠ tqT := by decide
@[simp] theorem tq_tqS2_ne_tqK : tqS2 ≠ tqK := by decide
@[simp] theorem tq_tqS2_ne_tqF : tqS2 ≠ tqF := by decide
@[simp] theorem tq_tqS2_ne_tqS : tqS2 ≠ tqS := by decide
@[simp] theorem tq_tqS2_ne_tqTy : tqS2 ≠ tqTy := by decide
@[simp] theorem tq_tqS2_ne_tqB : tqS2 ≠ tqB := by decide
@[simp] theorem tq_tqS2_ne_tqL : tqS2 ≠ tqL := by decide
@[simp] theorem tq_tqS2_ne_tqO : tqS2 ≠ tqO := by decide
@[simp] theorem tq_tqS2_ne_tqDk : tqS2 ≠ tqDk := by decide
@[simp] theorem tq_tqS2_ne_tqA : tqS2 ≠ tqA := by decide
@[simp] theorem tq_tqS2_ne_tqH : tqS2 ≠ tqH := by decide
@[simp] theorem tq_tqS2_ne_tqU : tqS2 ≠ tqU := by decide
@[simp] theorem tq_tqS2_ne_tqV : tqS2 ≠ tqV := by decide
@[simp] theorem tq_tqS2_ne_tqF2 : tqS2 ≠ tqF2 := by decide
@[simp] theorem tq_tqS2_ne_tqR : tqS2 ≠ tqR := by decide
@[simp] theorem tq_tqS2_ne_lKb : tqS2 ≠ lKb := by decide
@[simp] theorem tq_tqS2_ne_kFu : tqS2 ≠ kFu := by decide
@[simp] theorem tq_tqS2_ne_kD : tqS2 ≠ kD := by decide
@[simp] theorem tq_tqS2_ne_lFl : tqS2 ≠ lFl := by decide
@[simp] theorem tq_tqS2_ne_lDh : tqS2 ≠ lDh := by decide
@[simp] theorem tq_tqS2_ne_lDt : tqS2 ≠ lDt := by decide
@[simp] theorem tq_tqS2_ne_lDg : tqS2 ≠ lDg := by decide
@[simp] theorem tq_tqS2_ne_lDi : tqS2 ≠ lDi := by decide
@[simp] theorem tq_tqS2_ne_lRp : tqS2 ≠ lRp := by decide
@[simp] theorem tq_tqS2_ne_lRn : tqS2 ≠ lRn := by decide
@[simp] theorem tq_tqS2_ne_lFle : tqS2 ≠ lFle := by decide
@[simp] theorem tq_tqS2_ne_lDir : tqS2 ≠ lDir := by decide
@[simp] theorem tq_tqR_ne_tqP : tqR ≠ tqP := by decide
@[simp] theorem tq_tqR_ne_tqT : tqR ≠ tqT := by decide
@[simp] theorem tq_tqR_ne_tqK : tqR ≠ tqK := by decide
@[simp] theorem tq_tqR_ne_tqF : tqR ≠ tqF := by decide
@[simp] theorem tq_tqR_ne_tqS : tqR ≠ tqS := by decide
@[simp] theorem tq_tqR_ne_tqTy : tqR ≠ tqTy := by decide
@[simp] theorem tq_tqR_ne_tqB : tqR ≠ tqB := by decide
@[simp] theorem tq_tqR_ne_tqL : tqR ≠ tqL := by decide
@[simp] theorem tq_tqR_ne_tqO : tqR ≠ tqO := by decide
@[simp] theorem tq_tqR_ne_tqDk : tqR ≠ tqDk := by decide
@[simp] theorem tq_tqR_ne_tqA : tqR ≠ tqA := by decide
@[simp] theorem tq_tqR_ne_tqH : tqR ≠ tqH := by decide
@[simp] theorem tq_tqR_ne_tqU : tqR ≠ tqU := by decide
@[simp] theorem tq_tqR_ne_tqV : tqR ≠ tqV := by decide
@[simp] theorem tq_tqR_ne_tqF2 : tqR ≠ tqF2 := by decide
@[simp] theorem tq_tqR_ne_tqS2 : tqR ≠ tqS2 := by decide
@[simp] theorem tq_tqR_ne_lKb : tqR ≠ lKb := by decide
@[simp] theorem tq_tqR_ne_kFu : tqR ≠ kFu := by decide
@[simp] theorem tq_tqR_ne_kD : tqR ≠ kD := by decide
@[simp] theorem tq_tqR_ne_lFl : tqR ≠ lFl := by decide
@[simp] theorem tq_tqR_ne_lDh : tqR ≠ lDh := by decide
@[simp] theorem tq_tqR_ne_lDt : tqR ≠ lDt := by decide
@[simp] theorem tq_tqR_ne_lDg : tqR ≠ lDg := by decide
@[simp] theorem tq_tqR_ne_lDi : tqR ≠ lDi := by decide
@[simp] theorem tq_tqR_ne_lRp : tqR ≠ lRp := by decide
@[simp] theorem tq_tqR_ne_lRn : tqR ≠ lRn := by decide
@[simp] theorem tq_tqR_ne_lFle : tqR ≠ lFle := by decide
@[simp] theorem tq_tqR_ne_lDir : tqR ≠ lDir := by decide
@[simp] theorem tq_lKb_ne_tqP : lKb ≠ tqP := by decide
@[simp] theorem tq_lKb_ne_tqT : lKb ≠ tqT := by decide
@[simp] theorem tq_lKb_ne_tqK : lKb ≠ tqK := by decide
@[simp] theorem tq_lKb_ne_tqF : lKb ≠ tqF := by decide
@[simp] theorem tq_lKb_ne_tqS : lKb ≠ tqS := by decide
@[simp] theorem tq_lKb_ne_tqTy : lKb ≠ tqTy := by decide
@[simp] theorem tq_lKb_ne_tqB : lKb ≠ tqB := by decide
@[simp] theorem tq_lKb_ne_tqL : lKb ≠ tqL := by decide
@[simp] theorem tq_lKb_ne_tqO : lKb ≠ tqO := by decide
@[simp] theorem tq_lKb_ne_tqDk : lKb ≠ tqDk := by decide
@[simp] theorem tq_lKb_ne_tqA : lKb ≠ tqA := by decide
@[simp] theorem tq_lKb_ne_tqH : lKb ≠ tqH := by decide
@[simp] theorem tq_lKb_ne_tqU : lKb ≠ tqU := by decide
@[simp] theorem tq_lKb_ne_tqV : lKb ≠ tqV := by decide
@[simp] theorem tq_lKb_ne_tqF2 : lKb ≠ tqF2 := by decide
@[simp] theorem tq_lKb_ne_tqS2 : lKb ≠ tqS2 := by decide
@[simp] theorem tq_lKb_ne_tqR : lKb ≠ tqR := by decide
@[simp] theorem tq_kFu_ne_tqP : kFu ≠ tqP := by decide
@[simp] theorem tq_kFu_ne_tqT : kFu ≠ tqT := by decide
@[simp] theorem tq_kFu_ne_tqK : kFu ≠ tqK := by decide
@[simp] theorem tq_kFu_ne_tqF : kFu ≠ tqF := by decide
@[simp] theorem tq_kFu_ne_tqS : kFu ≠ tqS := by decide
@[simp] theorem tq_kFu_ne_tqTy : kFu ≠ tqTy := by decide
@[simp] theorem tq_kFu_ne_tqB : kFu ≠ tqB := by decide
@[simp] theorem tq_kFu_ne_tqL : kFu ≠ tqL := by decide
@[simp] theorem tq_kFu_ne_tqO : kFu ≠ tqO := by decide
@[simp] theorem tq_kFu_ne_tqDk : kFu ≠ tqDk := by decide
@[simp] theorem tq_kFu_ne_tqA : kFu ≠ tqA := by decide
@[simp] theorem tq_kFu_ne_tqH : kFu ≠ tqH := by decide
@[simp] theorem tq_kFu_ne_tqU : kFu ≠ tqU := by decide
@[simp] theorem tq_kFu_ne_tqV : kFu ≠ tqV := by decide
@[simp] theorem tq_kFu_ne_tqF2 : kFu ≠ tqF2 := by decide
@[simp] theorem tq_kFu_ne_tqS2 : kFu ≠ tqS2 := by decide
@[simp] theorem tq_kFu_ne_tqR : kFu ≠ tqR := by decide
@[simp] theorem tq_kD_ne_tqP : kD ≠ tqP := by decide
@[simp] theorem tq_kD_ne_tqT : kD ≠ tqT := by decide
@[simp] theorem tq_kD_ne_tqK : kD ≠ tqK := by decide
@[simp] theorem tq_kD_ne_tqF : kD ≠ tqF := by decide
@[simp] theorem tq_kD_ne_tqS : kD ≠ tqS := by decide
@[simp] theorem tq_kD_ne_tqTy : kD ≠ tqTy := by decide
@[simp] theorem tq_kD_ne_tqB : kD ≠ tqB := by decide
@[simp] theorem tq_kD_ne_tqL : kD ≠ tqL := by decide
@[simp] theorem tq_kD_ne_tqO : kD ≠ tqO := by decide
@[simp] theorem tq_kD_ne_tqDk : kD ≠ tqDk := by decide
@[simp] theorem tq_kD_ne_tqA : kD ≠ tqA := by decide
@[simp] theorem tq_kD_ne_tqH : kD ≠ tqH := by decide
@[simp] theorem tq_kD_ne_tqU : kD ≠ tqU := by decide
@[simp] theorem tq_kD_ne_tqV : kD ≠ tqV := by decide
@[simp] theorem tq_kD_ne_tqF2 : kD ≠ tqF2 := by decide
@[simp] theorem tq_kD_ne_tqS2 : kD ≠ tqS2 := by decide
@[simp] theorem tq_kD_ne_tqR : kD ≠ tqR := by decide
@[simp] theorem tq_lFl_ne_tqP : lFl ≠ tqP := by decide
@[simp] theorem tq_lFl_ne_tqT : lFl ≠ tqT := by decide
@[simp] theorem tq_lFl_ne_tqK : lFl ≠ tqK := by decide
@[simp] theorem tq_lFl_ne_tqF : lFl ≠ tqF := by decide
@[simp] theorem tq_lFl_ne_tqS : lFl ≠ tqS := by decide
@[simp] theorem tq_lFl_ne_tqTy : lFl ≠ tqTy := by decide
@[simp] theorem tq_lFl_ne_tqB : lFl ≠ tqB := by decide
@[simp] theorem tq_lFl_ne_tqL : lFl ≠ tqL := by decide
@[simp] theorem tq_lFl_ne_tqO : lFl ≠ tqO := by decide
@[simp] theorem tq_lFl_ne_tqDk : lFl ≠ tqDk := by decide
@[simp] theorem tq_lFl_ne_tqA : lFl ≠ tqA := by decide
@[simp] theorem tq_lFl_ne_tqH : lFl ≠ tqH := by decide
@[simp] theorem tq_lFl_ne_tqU : lFl ≠ tqU := by decide
@[simp] theorem tq_lFl_ne_tqV : lFl ≠ tqV := by decide
@[simp] theorem tq_lFl_ne_tqF2 : lFl ≠ tqF2 := by decide
@[simp] theorem tq_lFl_ne_tqS2 : lFl ≠ tqS2 := by decide
@[simp] theorem tq_lFl_ne_tqR : lFl ≠ tqR := by decide
@[simp] theorem tq_lDh_ne_tqP : lDh ≠ tqP := by decide
@[simp] theorem tq_lDh_ne_tqT : lDh ≠ tqT := by decide
@[simp] theorem tq_lDh_ne_tqK : lDh ≠ tqK := by decide
@[simp] theorem tq_lDh_ne_tqF : lDh ≠ tqF := by decide
@[simp] theorem tq_lDh_ne_tqS : lDh ≠ tqS := by decide
@[simp] theorem tq_lDh_ne_tqTy : lDh ≠ tqTy := by decide
@[simp] theorem tq_lDh_ne_tqB : lDh ≠ tqB := by decide
@[simp] theorem tq_lDh_ne_tqL : lDh ≠ tqL := by decide
@[simp] theorem tq_lDh_ne_tqO : lDh ≠ tqO := by decide
@[simp] theorem tq_lDh_ne_tqDk : lDh ≠ tqDk := by decide
@[simp] theorem tq_lDh_ne_tqA : lDh ≠ tqA := by decide
@[simp] theorem tq_lDh_ne_tqH : lDh ≠ tqH := by decide
@[simp] theorem tq_lDh_ne_tqU : lDh ≠ tqU := by decide
@[simp] theorem tq_lDh_ne_tqV : lDh ≠ tqV := by decide
@[simp] theorem tq_lDh_ne_tqF2 : lDh ≠ tqF2 := by decide
@[simp] theorem tq_lDh_ne_tqS2 : lDh ≠ tqS2 := by decide
@[simp] theorem tq_lDh_ne_tqR : lDh ≠ tqR := by decide
@[simp] theorem tq_lDt_ne_tqP : lDt ≠ tqP := by decide
@[simp] theorem tq_lDt_ne_tqT : lDt ≠ tqT := by decide
@[simp] theorem tq_lDt_ne_tqK : lDt ≠ tqK := by decide
@[simp] theorem tq_lDt_ne_tqF : lDt ≠ tqF := by decide
@[simp] theorem tq_lDt_ne_tqS : lDt ≠ tqS := by decide
@[simp] theorem tq_lDt_ne_tqTy : lDt ≠ tqTy := by decide
@[simp] theorem tq_lDt_ne_tqB : lDt ≠ tqB := by decide
@[simp] theorem tq_lDt_ne_tqL : lDt ≠ tqL := by decide
@[simp] theorem tq_lDt_ne_tqO : lDt ≠ tqO := by decide
@[simp] theorem tq_lDt_ne_tqDk : lDt ≠ tqDk := by decide
@[simp] theorem tq_lDt_ne_tqA : lDt ≠ tqA := by decide
@[simp] theorem tq_lDt_ne_tqH : lDt ≠ tqH := by decide
@[simp] theorem tq_lDt_ne_tqU : lDt ≠ tqU := by decide
@[simp] theorem tq_lDt_ne_tqV : lDt ≠ tqV := by decide
@[simp] theorem tq_lDt_ne_tqF2 : lDt ≠ tqF2 := by decide
@[simp] theorem tq_lDt_ne_tqS2 : lDt ≠ tqS2 := by decide
@[simp] theorem tq_lDt_ne_tqR : lDt ≠ tqR := by decide
@[simp] theorem tq_lDg_ne_tqP : lDg ≠ tqP := by decide
@[simp] theorem tq_lDg_ne_tqT : lDg ≠ tqT := by decide
@[simp] theorem tq_lDg_ne_tqK : lDg ≠ tqK := by decide
@[simp] theorem tq_lDg_ne_tqF : lDg ≠ tqF := by decide
@[simp] theorem tq_lDg_ne_tqS : lDg ≠ tqS := by decide
@[simp] theorem tq_lDg_ne_tqTy : lDg ≠ tqTy := by decide
@[simp] theorem tq_lDg_ne_tqB : lDg ≠ tqB := by decide
@[simp] theorem tq_lDg_ne_tqL : lDg ≠ tqL := by decide
@[simp] theorem tq_lDg_ne_tqO : lDg ≠ tqO := by decide
@[simp] theorem tq_lDg_ne_tqDk : lDg ≠ tqDk := by decide
@[simp] theorem tq_lDg_ne_tqA : lDg ≠ tqA := by decide
@[simp] theorem tq_lDg_ne_tqH : lDg ≠ tqH := by decide
@[simp] theorem tq_lDg_ne_tqU : lDg ≠ tqU := by decide
@[simp] theorem tq_lDg_ne_tqV : lDg ≠ tqV := by decide
@[simp] theorem tq_lDg_ne_tqF2 : lDg ≠ tqF2 := by decide
@[simp] theorem tq_lDg_ne_tqS2 : lDg ≠ tqS2 := by decide
@[simp] theorem tq_lDg_ne_tqR : lDg ≠ tqR := by decide
@[simp] theorem tq_lDi_ne_tqP : lDi ≠ tqP := by decide
@[simp] theorem tq_lDi_ne_tqT : lDi ≠ tqT := by decide
@[simp] theorem tq_lDi_ne_tqK : lDi ≠ tqK := by decide
@[simp] theorem tq_lDi_ne_tqF : lDi ≠ tqF := by decide
@[simp] theorem tq_lDi_ne_tqS : lDi ≠ tqS := by decide
@[simp] theorem tq_lDi_ne_tqTy : lDi ≠ tqTy := by decide
@[simp] theorem tq_lDi_ne_tqB : lDi ≠ tqB := by decide
@[simp] theorem tq_lDi_ne_tqL : lDi ≠ tqL := by decide
@[simp] theorem tq_lDi_ne_tqO : lDi ≠ tqO := by decide
@[simp] theorem tq_lDi_ne_tqDk : lDi ≠ tqDk := by decide
@[simp] theorem tq_lDi_ne_tqA : lDi ≠ tqA := by decide
@[simp] theorem tq_lDi_ne_tqH : lDi ≠ tqH := by decide
@[simp] theorem tq_lDi_ne_tqU : lDi ≠ tqU := by decide
@[simp] theorem tq_lDi_ne_tqV : lDi ≠ tqV := by decide
@[simp] theorem tq_lDi_ne_tqF2 : lDi ≠ tqF2 := by decide
@[simp] theorem tq_lDi_ne_tqS2 : lDi ≠ tqS2 := by decide
@[simp] theorem tq_lDi_ne_tqR : lDi ≠ tqR := by decide
@[simp] theorem tq_lRp_ne_tqP : lRp ≠ tqP := by decide
@[simp] theorem tq_lRp_ne_tqT : lRp ≠ tqT := by decide
@[simp] theorem tq_lRp_ne_tqK : lRp ≠ tqK := by decide
@[simp] theorem tq_lRp_ne_tqF : lRp ≠ tqF := by decide
@[simp] theorem tq_lRp_ne_tqS : lRp ≠ tqS := by decide
@[simp] theorem tq_lRp_ne_tqTy : lRp ≠ tqTy := by decide
@[simp] theorem tq_lRp_ne_tqB : lRp ≠ tqB := by decide
@[simp] theorem tq_lRp_ne_tqL : lRp ≠ tqL := by decide
@[simp] theorem tq_lRp_ne_tqO : lRp ≠ tqO := by decide
@[simp] theorem tq_lRp_ne_tqDk : lRp ≠ tqDk := by decide
@[simp] theorem tq_lRp_ne_tqA : lRp ≠ tqA := by decide
@[simp] theorem tq_lRp_ne_tqH : lRp ≠ tqH := by decide
@[simp] theorem tq_lRp_ne_tqU : lRp ≠ tqU := by decide
@[simp] theorem tq_lRp_ne_tqV : lRp ≠ tqV := by decide
@[simp] theorem tq_lRp_ne_tqF2 : lRp ≠ tqF2 := by decide
@[simp] theorem tq_lRp_ne_tqS2 : lRp ≠ tqS2 := by decide
@[simp] theorem tq_lRp_ne_tqR : lRp ≠ tqR := by decide
@[simp] theorem tq_lRn_ne_tqP : lRn ≠ tqP := by decide
@[simp] theorem tq_lRn_ne_tqT : lRn ≠ tqT := by decide
@[simp] theorem tq_lRn_ne_tqK : lRn ≠ tqK := by decide
@[simp] theorem tq_lRn_ne_tqF : lRn ≠ tqF := by decide
@[simp] theorem tq_lRn_ne_tqS : lRn ≠ tqS := by decide
@[simp] theorem tq_lRn_ne_tqTy : lRn ≠ tqTy := by decide
@[simp] theorem tq_lRn_ne_tqB : lRn ≠ tqB := by decide
@[simp] theorem tq_lRn_ne_tqL : lRn ≠ tqL := by decide
@[simp] theorem tq_lRn_ne_tqO : lRn ≠ tqO := by decide
@[simp] theorem tq_lRn_ne_tqDk : lRn ≠ tqDk := by decide
@[simp] theorem tq_lRn_ne_tqA : lRn ≠ tqA := by decide
@[simp] theorem tq_lRn_ne_tqH : lRn ≠ tqH := by decide
@[simp] theorem tq_lRn_ne_tqU : lRn ≠ tqU := by decide
@[simp] theorem tq_lRn_ne_tqV : lRn ≠ tqV := by decide
@[simp] theorem tq_lRn_ne_tqF2 : lRn ≠ tqF2 := by decide
@[simp] theorem tq_lRn_ne_tqS2 : lRn ≠ tqS2 := by decide
@[simp] theorem tq_lRn_ne_tqR : lRn ≠ tqR := by decide
@[simp] theorem tq_lFle_ne_tqP : lFle ≠ tqP := by decide
@[simp] theorem tq_lFle_ne_tqT : lFle ≠ tqT := by decide
@[simp] theorem tq_lFle_ne_tqK : lFle ≠ tqK := by decide
@[simp] theorem tq_lFle_ne_tqF : lFle ≠ tqF := by decide
@[simp] theorem tq_lFle_ne_tqS : lFle ≠ tqS := by decide
@[simp] theorem tq_lFle_ne_tqTy : lFle ≠ tqTy := by decide
@[simp] theorem tq_lFle_ne_tqB : lFle ≠ tqB := by decide
@[simp] theorem tq_lFle_ne_tqL : lFle ≠ tqL := by decide
@[simp] theorem tq_lFle_ne_tqO : lFle ≠ tqO := by decide
@[simp] theorem tq_lFle_ne_tqDk : lFle ≠ tqDk := by decide
@[simp] theorem tq_lFle_ne_tqA : lFle ≠ tqA := by decide
@[simp] theorem tq_lFle_ne_tqH : lFle ≠ tqH := by decide
@[simp] theorem tq_lFle_ne_tqU : lFle ≠ tqU := by decide
@[simp] theorem tq_lFle_ne_tqV : lFle ≠ tqV := by decide
@[simp] theorem tq_lFle_ne_tqF2 : lFle ≠ tqF2 := by decide
@[simp] theorem tq_lFle_ne_tqS2 : lFle ≠ tqS2 := by decide
@[simp] theorem tq_lFle_ne_tqR : lFle ≠ tqR := by decide
@[simp] theorem tq_lDir_ne_tqP : lDir ≠ tqP := by decide
@[simp] theorem tq_lDir_ne_tqT : lDir ≠ tqT := by decide
@[simp] theorem tq_lDir_ne_tqK : lDir ≠ tqK := by decide
@[simp] theorem tq_lDir_ne_tqF : lDir ≠ tqF := by decide
@[simp] theorem tq_lDir_ne_tqS : lDir ≠ tqS := by decide
@[simp] theorem tq_lDir_ne_tqTy : lDir ≠ tqTy := by decide
@[simp] theorem tq_lDir_ne_tqB : lDir ≠ tqB := by decide
@[simp] theorem tq_lDir_ne_tqL : lDir ≠ tqL := by decide
@[simp] theorem tq_lDir_ne_tqO : lDir ≠ tqO := by decide
@[simp] theorem tq_lDir_ne_tqDk : lDir ≠ tqDk := by decide
@[simp] theorem tq_lDir_ne_tqA : lDir ≠ tqA := by decide
@[simp] theorem tq_lDir_ne_tqH : lDir ≠ tqH := by decide
@[simp] theorem tq_lDir_ne_tqU : lDir ≠ tqU := by decide
@[simp] theorem tq_lDir_ne_tqV : lDir ≠ tqV := by decide
@[simp] theorem tq_lDir_ne_tqF2 : lDir ≠ tqF2 := by decide
@[simp] theorem tq_lDir_ne_tqS2 : lDir ≠ tqS2 := by decide
@[simp] theorem tq_lDir_ne_tqR : lDir ≠ tqR := by decide

def tqParams : List MlS := [kFu, kD, tqP, tqT, tqK, tqF, tqS]
def tqLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, tqTy, tqB, tqL, tqO, tqDk, tqA, tqH, tqU, tqV, tqF2, tqS2,
  tqR]

def tqLeaf : ProgHOL 64 :=
  .seq (.call (some (some (.local, tqR), none)) fPz [vv kFu, vv kD, vv tqT, vv tqK, vv tqF, vv tqS]) (.return (vv tqR))

def tqCore : ProgHOL 64 :=
  .ite (.cmp .equal (vv tqP) (.const 0)) tqLeaf
  (.ite (tagIsE tqT 6)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv tqT)) (.seq eViewP
    (.seq (.assign .local tqTy (.load .one (vv lRp)))
    (.seq (.assign .local tqB (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.assign .local tqL (.load .one (vv tqF)))
    (.seq (.call (some (some (.local, tqO), none)) ExQ.fIrr
        [vv tqF, .const 0, vv tqL, .const (BitVec.ofNat 64 coreWalkFuel), vv tqTy, .const 0])
    (.seq (.assign .local tqDk (.op .add [vv kD, vv tqK]))
    (.seq (.call (some (some (.local, tqA), none)) fI [vv kFu, vv tqDk, vv tqO])
    (.seq (.call (some (some (.local, tqH), none)) fW [vv kFu, vv tqDk, vv tqA])
    (.ite (tagIsE tqH 2)
      (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv tqH)) (.seq eViewP
      (.seq (.assign .local tqU (.load .one (vv lRp)))
      (.seq (.call (some (some (.local, tqV), none)) fInternFVar [vv tqO, vv tqDk])
      (.seq (.call (some (some (.local, tqF2), none)) ExPre.fAppend [vv tqF, vv tqV])
      (.seq (.call (some (some (.local, tqS2), none)) ExPre.fAppend [vv tqS, vv tqU])
      (.seq (.call (some (some (.local, tqR), none)) fTq
          [vv kFu, vv kD, .op .sub [vv tqP, .const 1], vv tqB, .op .add [vv tqK, .const 1], vv tqF2, vv tqS2])
        (.return (vv tqR))))))))))
      hang)))))))))))
    tqLeaf)

def tqBody : ProgHOL 64 := prologue tqLocals tqCore

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
    (hI : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → d' < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (inferE C fIB) s1 ((knot mode C n).infer d' e')
      (PostK (ctxH C H)))
    (hW : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → d' < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
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
    ⟨by simp +decide [Env.get, pzParams, ctxEnv], by simp, by simp, trivial⟩ (hI H s1 (d + k) ob hp (by omega))
    (fun bt s2 H2 hp2 _ => ?_)
  refine Big.specR_callKC (C := ctxH C H2) pzH fW kParams [vv kFu, vv pzDk, vv pzB] (whnfE C fWB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 (d + k), Enc.idxW bt] (by decide) rfl (by decide) hc.w
    ⟨by simp +decide [Env.get, pzParams, ctxEnv], by simp, by simp, trivial⟩ (hW H2 s2 (d + k) bt (hp.trans hp2) (by omega))
    (fun hh s3 H3 hp3 _ => ?_)
  have hp13 : H <+: H3 := hp2.trans hp3
  refine Knot.specR_tagIteV pzH hh 2 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
  · rw [ite_eq_left (show (hh.tag == ETag.sort) = true by simp [htg, ETag.sort])]
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
  · rw [ite_eq_right (show ¬ (hh.tag == ETag.sort) = true by simpa [ETag.sort] using htg)]
    exact specR_hangI

theorem tq_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ tqLocals → (ctxEnv C ++ tqParams.zip vals).get x = none :=
  Knot.params_none C tqLocals tqParams vals (by decide) (by decide)

structure TqCodes (C : Ctx) : Prop where
  pz : PzCodes C
  pzf : C.code.lookup fPz = some (pzParams.map (fun p => (p, ShapeHOL.one)), pzBody, .one)
  fv : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one)
  app : C.code.lookup ExPre.fAppend = some (ExPre.appParams.map (fun p => (p, ShapeHOL.one)), ExPre.appBody C, .one)
  self : C.code.lookup fTq = some (tqParams.map (fun p => (p, ShapeHOL.one)), tqBody, .one)

theorem tq_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (hc : TqCodes C)
    (hI : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → d' < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (inferE C fIB) s1 ((knot mode C n).infer d' e')
      (PostK (ctxH C H)))
    (hW : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → d' < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d' e')
      (PostK (ctxH C H)))
    (d : Nat) :
    ∀ peel (t : EIdx) (k : Nat) (fvs : List EIdx) (stk : List LIdx) (ofv ost : Nat) (H : List (BitVec 64))
      (s : AState), C.H <+: H → BlkAt H ofv (fvs.map Enc.idxW) → BlkAt H ost (stk.map Enc.idxW) →
      fvs.length = k → stk.length = k → k + peel < 2 ^ 57 → d + k + peel < 2 ^ 63 →
      SpecR (σ := σ) (Pre (ctxH C H) s (tqParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, BitVec.ofNat 64 peel,
        Enc.idxW t, BitVec.ofNat 64 k, cellA C ofv, cellA C ost])) tqBody s
        (inferPis (knot mode C n) C.fe d peel t k fvs.toArray stk.toArray) (PostK (ctxH C H)) := by
  have leaf : ∀ (t : EIdx) (k : Nat) (fvs : List EIdx) (stk : List LIdx) (ofv ost : Nat) (H : List (BitVec 64))
      (s : AState) (Γ : Env) (M : Mem), C.H <+: H → BlkAt H ofv (fvs.map Enc.idxW) →
      BlkAt H ost (stk.map Enc.idxW) → fvs.length < 2 ^ 58 → stk.length < 2 ^ 58 → d + k < 2 ^ 63 →
      Γ.get kFu = some (BitVec.ofNat 64 n) → Γ.get kD = some (BitVec.ofNat 64 d) → Γ.get tqT = some (Enc.idxW t) →
      Γ.get tqK = some (BitVec.ofNat 64 k) → Γ.get tqF = some (cellA C ofv) → Γ.get tqS = some (cellA C ost) →
      SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ tqLocals)) tqLeaf s
        (inferPisLeaf (knot mode C n) C.fe d t k fvs.toArray stk.toArray) (PostK (ctxH C H)) :=
    fun t k fvs stk ofv ost H s Γ M hp hbf hbs hfl hsl hdk h1 h2 h3 h4 h5 h6 =>
      specR_callKR tqR fPz pzParams [vv kFu, vv kD, vv tqT, vv tqK, vv tqF, vv tqS] pzBody
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW t, BitVec.ofNat 64 k, cellA C ofv, cellA C ost]
        (by decide) rfl (by decide) hc.pzf
        ⟨by simp [h1], by simp [h2], by simp [h3], by simp [h4], by simp [h5], by simp [h6], trivial⟩
        (pz_spec ra mode n C hok hc.pz hI hW s d k t fvs stk ofv ost H hp hbf hbs hfl hsl hdk)
  intro peel
  induction peel with
  | zero =>
    intro t k fvs stk ofv ost H s hp hbf hbs hfl hsl hkp hdk
    refine specR_prologue (postK_locals _) (tq_none _ _) ?_
    unfold tqCore
    rw [inferPis]
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, tqParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact leaf t k fvs stk ofv ost H s _ _ hp hbf hbs (by omega) (by omega) (by omega)
      (by simp +decide [Env.get, tqParams, ctxEnv]) (by simp +decide [Env.get, tqParams, ctxEnv]) (by simp +decide [Env.get, tqParams, ctxEnv]) (by simp +decide [Env.get, tqParams, ctxEnv]) (by simp +decide [Env.get, tqParams, ctxEnv] <;> rfl) (by simp +decide [Env.get, tqParams, ctxEnv] <;> rfl)
  | succ peel ih =>
    intro t k fvs stk ofv ost H s hp hbf hbs hfl hsl hkp hdk
    refine specR_prologue (postK_locals _) (tq_none _ _) ?_
    unfold tqCore
    rw [inferPis]
    have hne := ofNat_succ_ne peel (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, tqParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine Knot.specR_tagIteV tqT t 6 (by decide) (by decide) (by simp +decide [Env.get, tqParams, ctxEnv]) (fun htg => ?_) (fun htg => ?_)
    swap
    · rw [ite_eq_left (show (t.tag != ETag.forallE) = true by simpa [ETag.forallE] using htg)]
      exact leaf t k fvs stk ofv ost H s _ _ hp hbf hbs (by omega) (by omega) (by omega)
        (by simp +decide [Env.get, tqParams, ctxEnv]) (by simp +decide [Env.get, tqParams, ctxEnv]) (by simp +decide [Env.get, tqParams, ctxEnv]) (by simp +decide [Env.get, tqParams, ctxEnv]) (by simp +decide [Env.get, tqParams, ctxEnv] <;> rfl) (by simp +decide [Env.get, tqParams, ctxEnv] <;> rfl)
    rw [ite_eq_right (show ¬ (t.tag != ETag.forallE) = true by simp [htg, ETag.forallE])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv tqT) (Enc.idxW t) (by decide) (by simp +decide [Env.get, tqParams, ctxEnv]) ?_
    refine specR_viewP (C := ctxH C H) t (by simp) (by simp +decide [Env.get] <;> rfl)
      (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
    have h6 : v.tagN = 6 := by rw [htn, htg]; rfl
    obtain ⟨ty, b, rfl⟩ : ∃ ty b, v = .forallE ty b := by cases v <;> simp [ENodeView.tagN] at h6 ⊢
    have hvb : s.store.viewBind t = some (ty, b) := viewBind_of_view_forallE (by rw [htg]; rfl) hv
    refine specR_runBind (by rw [viewBind_run, hvb]) ?_
    dsimp only
    refine specR_loadI' tqTy (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW ty) [Enc.idxW b] []) ?_
    refine specR_loadI' tqB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW b) [] []) ?_
    refine specR_dropM ?_
    obtain ⟨hlo, hlv0⟩ := blkAt_get0 hbf
    refine UD.specR_heapLoadI' (C := ctxH C H) tqL (vv tqF) ofv (BitVec.ofNat 64 fvs.length)
      (by show H[ofv]? = _; rw [List.getElem?_eq_getElem hlo, hlv0]; simp) (by decide) (by simp +decide [Env.get, tqParams, ctxEnv] <;> rfl) ?_
    simp only [instantiateListFast, List.size_toArray, bind_assoc]
    refine ILP.callE_spec (C := ctxH C H) tqO ExQ.fIrr ExQ.irrParams
      [vv tqF, .const 0, vv tqL, .const (BitVec.ofNat 64 coreWalkFuel), vv tqTy, .const 0] (ExQ.irrBody C)
      [cellA C ofv, BitVec.ofNat 64 0, BitVec.ofNat 64 fvs.length, BitVec.ofNat 64 coreWalkFuel, Enc.idxW ty,
        BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.pz.irr
      ⟨by simp +decide [Env.get, tqParams, ctxEnv] <;> rfl, rfl, by simp, rfl, by simp, rfl, trivial⟩
      (ExQ.irr_spec ra (ctxH C H) (ctxOK_H hok H) (codesQ_H hc.pz.q H) fvs.toArray ofv
        (show BlkAt H ofv (fvs.toArray.toList.map Enc.idxW) by simpa using hbf) (by simp; omega) s
        coreWalkFuel 0 fvs.length 0 ty CV.coreWalkFuel_lt (by decide) (by omega) (by decide)) (fun tyo s1 => ?_)
    refine specR_assignI tqDk _ (BitVec.ofNat 64 (d + k)) (by decide)
      (by simp +decide [sev, Env.get, tqParams, ctxEnv]; exact BitVec.ofNat_add_ofNat ..) ?_
    refine Big.specR_callKC (C := ctxH C H) tqA fI kParams [vv kFu, vv tqDk, vv tqO] (inferE C fIB)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 (d + k), Enc.idxW tyo] (by decide) rfl (by decide) hc.pz.i
      ⟨by simp +decide [Env.get, tqParams, ctxEnv], by simp, by simp, trivial⟩ (hI H s1 (d + k) tyo hp (by omega)) (fun tty s2 H2 hp2 _ => ?_)
    refine Big.specR_callKC (C := ctxH C H2) tqH fW kParams [vv kFu, vv tqDk, vv tqA] (whnfE C fWB)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 (d + k), Enc.idxW tty] (by decide) rfl (by decide) hc.pz.w
      ⟨by simp +decide [Env.get, tqParams, ctxEnv], by simp, by simp, trivial⟩ (hW H2 s2 (d + k) tty (hp.trans hp2) (by omega)) (fun w s3 H3 hp3 _ => ?_)
    have hp13 : H <+: H3 := hp2.trans hp3
    refine Knot.specR_tagIteV tqH w 2 (by decide) (by decide) (by simp) (fun htg2 => ?_) (fun htg2 => ?_)
    · rw [ite_eq_left (show (w.tag == ETag.sort) = true by simp [htg2, ETag.sort])]
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv tqH) (Enc.idxW w) (by decide) (by simp) ?_
      refine specR_viewP (C := ctxH C H3) w (by simp) (by simp +decide [Env.get] <;> rfl)
        (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun vw P2 hv2 htn2 _ => ?_)
      have h2 : vw.tagN = 2 := by rw [htn2, htg2]; rfl
      obtain ⟨u, rfl⟩ : ∃ u, vw = .sort u := by cases vw <;> simp [ENodeView.tagN] at h2 ⊢
      have hvs : s3.store.viewSort w = some u := viewSort_of_view (by rw [htg2]; rfl) hv2
      refine specR_runBind (show ConRon.Arena.viewSort w s3 = .ok (some u, s3) by
        show Except.ok (s3.store.viewSort w, s3) = _; rw [hvs]) ?_
      dsimp only
      refine specR_loadI' tqU (vv lRp) P2 (P2 + BitVec.ofNat 64 0) (Enc.idxW u) (by decide) (by simp) (by simp)
        (by simpa [encEView, Enc.encSort] using wordsAt_mem0 P2 (Enc.idxW u) [] []) ?_
      refine specR_dropM ?_
      refine ILP.specR_internFVarI (C := ctxH C H3) ra (ctxOK_H hok H3) hc.fv tqV (vv tqO) (vv tqDk) tyo (d + k)
        (by omega) (by decide) (by simp) (by simp) (fun fv s4 => ?_)
      refine ExPre.specR_callApp (C := ctxH C H3) (ctxOK_H hok H3) hc.app tqF2 (vv tqF) (vv tqV) ofv
        (fvs.map Enc.idxW) (Enc.idxW fv) (by decide) (blkAt_mono hbf hp13) (by simp +decide [Env.get, tqParams, ctxEnv] <;> rfl) (by simp)
        (fun H4 o4 hp4 hb4 => ?_)
      refine ExPre.specR_callApp (C := ctxH C H4) (ctxOK_H hok H4) hc.app tqS2 (vv tqS) (vv tqU) ost
        (stk.map Enc.idxW) (Enc.idxW u) (by decide) (blkAt_mono hbs (hp13.trans hp4)) (by simp +decide [Env.get, tqParams, ctxEnv] <;> rfl) (by simp)
        (fun H5 o5 hp5 hb5 => ?_)
      have hb4' : BlkAt H5 o4 ((fvs ++ [fv]).map Enc.idxW) := by simpa using blkAt_mono hb4 hp5
      have hb5' : BlkAt H5 o5 ((stk ++ [u]).map Enc.idxW) := by simpa using hb5
      rw [show fvs.toArray.push fv = (fvs ++ [fv]).toArray by simp, show stk.toArray.push u = (stk ++ [u]).toArray by simp]
      refine specR_congr (m' := inferPis (knot mode C n) C.fe d peel b (k + 1) (fvs ++ [fv]).toArray (stk ++ [u]).toArray
        >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H5) tqR fTq tqParams
        [vv kFu, vv kD, .op .sub [vv tqP, .const 1], vv tqB, .op .add [vv tqK, .const 1], vv tqF2, vv tqS2] tqBody
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, BitVec.ofNat 64 peel, Enc.idxW b, BitVec.ofNat 64 (k + 1), cellA C o4,
          cellA C o5] (by decide) rfl (by decide) hc.self
        ⟨by simp +decide [Env.get, tqParams, ctxEnv], by simp +decide [Env.get, tqParams, ctxEnv], by simp +decide [sev, Env.get, tqParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _,
          by simp, by simp +decide [sev, Env.get, tqParams, ctxEnv]; exact word_add1_eq k, by simp <;> rfl,
          by simp <;> rfl, trivial⟩
        (PostK (ctxH C H5)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu tqParams _ rfl hlk)
          (ih b (k + 1) (fvs ++ [fv]) (stk ++ [u]) o4 o5 H5 s4 (hp.trans (hp13.trans (hp4.trans hp5))) hb4' hb5'
            (by simp; omega) (by simp; omega) (by omega) (by omega)))
        (fun r w s6 H6 hp6 hw => ?_)
      subst hw
      exact specR_returnI _ (Enc.idxW r) (by simp)
        (fun t ht => ⟨H6, hp13.trans (hp4.trans (hp5.trans hp6)), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · rw [ite_eq_right (show ¬ (w.tag == ETag.sort) = true by simpa [ETag.sort] using htg2)]
      exact specR_hangI

end

end ConPanqueque.T.WC
