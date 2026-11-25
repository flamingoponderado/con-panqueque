import ConPanqueque.T.Core.DefeqA
import ConPanqueque.T.Core.EagerRed
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `natPred?`

The predecessor of a successor form: a nonzero literal (its predecessor literal interned, by the block
subtraction as in `natLitToConstructor`), or `Nat.succ x`. Answers `optW`.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def npE := ofString "npn_e"
def npW := ofString "npn_w"
def npB := ofString "npn_b"
def npL := ofString "npn_l"
def npO := ofString "npn_o"
def npD := ofString "npn_d"
def npT := ofString "npn_t"
def npF := ofString "npn_f"
def npX := ofString "npn_x"
def npC := ofString "npn_c"
def npU := ofString "npn_u"
def npS := ofString "npn_s"
def npEl := ofString "npn_el"
def fNp := ofString "natPred"

@[simp] theorem np_npE_ne_npW : npE ≠ npW := by decide
@[simp] theorem np_npE_ne_npB : npE ≠ npB := by decide
@[simp] theorem np_npE_ne_npL : npE ≠ npL := by decide
@[simp] theorem np_npE_ne_npO : npE ≠ npO := by decide
@[simp] theorem np_npE_ne_npD : npE ≠ npD := by decide
@[simp] theorem np_npE_ne_npT : npE ≠ npT := by decide
@[simp] theorem np_npE_ne_npF : npE ≠ npF := by decide
@[simp] theorem np_npE_ne_npX : npE ≠ npX := by decide
@[simp] theorem np_npE_ne_npC : npE ≠ npC := by decide
@[simp] theorem np_npE_ne_npU : npE ≠ npU := by decide
@[simp] theorem np_npE_ne_npS : npE ≠ npS := by decide
@[simp] theorem np_npE_ne_npEl : npE ≠ npEl := by decide
@[simp] theorem np_npE_ne_lFl : npE ≠ lFl := by decide
@[simp] theorem np_lFl_ne_npE : lFl ≠ npE := by decide
@[simp] theorem np_npE_ne_lDh : npE ≠ lDh := by decide
@[simp] theorem np_lDh_ne_npE : lDh ≠ npE := by decide
@[simp] theorem np_npE_ne_lDt : npE ≠ lDt := by decide
@[simp] theorem np_lDt_ne_npE : lDt ≠ npE := by decide
@[simp] theorem np_npE_ne_lDg : npE ≠ lDg := by decide
@[simp] theorem np_lDg_ne_npE : lDg ≠ npE := by decide
@[simp] theorem np_npE_ne_lDi : npE ≠ lDi := by decide
@[simp] theorem np_lDi_ne_npE : lDi ≠ npE := by decide
@[simp] theorem np_npE_ne_lRp : npE ≠ lRp := by decide
@[simp] theorem np_lRp_ne_npE : lRp ≠ npE := by decide
@[simp] theorem np_npE_ne_lRn : npE ≠ lRn := by decide
@[simp] theorem np_lRn_ne_npE : lRn ≠ npE := by decide
@[simp] theorem np_npE_ne_lDir : npE ≠ lDir := by decide
@[simp] theorem np_lDir_ne_npE : lDir ≠ npE := by decide
@[simp] theorem np_npE_ne_lFle : npE ≠ lFle := by decide
@[simp] theorem np_lFle_ne_npE : lFle ≠ npE := by decide
@[simp] theorem np_npE_ne_lKb : npE ≠ lKb := by decide
@[simp] theorem np_lKb_ne_npE : lKb ≠ npE := by decide
@[simp] theorem np_npW_ne_npE : npW ≠ npE := by decide
@[simp] theorem np_npW_ne_npB : npW ≠ npB := by decide
@[simp] theorem np_npW_ne_npL : npW ≠ npL := by decide
@[simp] theorem np_npW_ne_npO : npW ≠ npO := by decide
@[simp] theorem np_npW_ne_npD : npW ≠ npD := by decide
@[simp] theorem np_npW_ne_npT : npW ≠ npT := by decide
@[simp] theorem np_npW_ne_npF : npW ≠ npF := by decide
@[simp] theorem np_npW_ne_npX : npW ≠ npX := by decide
@[simp] theorem np_npW_ne_npC : npW ≠ npC := by decide
@[simp] theorem np_npW_ne_npU : npW ≠ npU := by decide
@[simp] theorem np_npW_ne_npS : npW ≠ npS := by decide
@[simp] theorem np_npW_ne_npEl : npW ≠ npEl := by decide
@[simp] theorem np_npW_ne_lFl : npW ≠ lFl := by decide
@[simp] theorem np_lFl_ne_npW : lFl ≠ npW := by decide
@[simp] theorem np_npW_ne_lDh : npW ≠ lDh := by decide
@[simp] theorem np_lDh_ne_npW : lDh ≠ npW := by decide
@[simp] theorem np_npW_ne_lDt : npW ≠ lDt := by decide
@[simp] theorem np_lDt_ne_npW : lDt ≠ npW := by decide
@[simp] theorem np_npW_ne_lDg : npW ≠ lDg := by decide
@[simp] theorem np_lDg_ne_npW : lDg ≠ npW := by decide
@[simp] theorem np_npW_ne_lDi : npW ≠ lDi := by decide
@[simp] theorem np_lDi_ne_npW : lDi ≠ npW := by decide
@[simp] theorem np_npW_ne_lRp : npW ≠ lRp := by decide
@[simp] theorem np_lRp_ne_npW : lRp ≠ npW := by decide
@[simp] theorem np_npW_ne_lRn : npW ≠ lRn := by decide
@[simp] theorem np_lRn_ne_npW : lRn ≠ npW := by decide
@[simp] theorem np_npW_ne_lDir : npW ≠ lDir := by decide
@[simp] theorem np_lDir_ne_npW : lDir ≠ npW := by decide
@[simp] theorem np_npW_ne_lFle : npW ≠ lFle := by decide
@[simp] theorem np_lFle_ne_npW : lFle ≠ npW := by decide
@[simp] theorem np_npW_ne_lKb : npW ≠ lKb := by decide
@[simp] theorem np_lKb_ne_npW : lKb ≠ npW := by decide
@[simp] theorem np_npB_ne_npE : npB ≠ npE := by decide
@[simp] theorem np_npB_ne_npW : npB ≠ npW := by decide
@[simp] theorem np_npB_ne_npL : npB ≠ npL := by decide
@[simp] theorem np_npB_ne_npO : npB ≠ npO := by decide
@[simp] theorem np_npB_ne_npD : npB ≠ npD := by decide
@[simp] theorem np_npB_ne_npT : npB ≠ npT := by decide
@[simp] theorem np_npB_ne_npF : npB ≠ npF := by decide
@[simp] theorem np_npB_ne_npX : npB ≠ npX := by decide
@[simp] theorem np_npB_ne_npC : npB ≠ npC := by decide
@[simp] theorem np_npB_ne_npU : npB ≠ npU := by decide
@[simp] theorem np_npB_ne_npS : npB ≠ npS := by decide
@[simp] theorem np_npB_ne_npEl : npB ≠ npEl := by decide
@[simp] theorem np_npB_ne_lFl : npB ≠ lFl := by decide
@[simp] theorem np_lFl_ne_npB : lFl ≠ npB := by decide
@[simp] theorem np_npB_ne_lDh : npB ≠ lDh := by decide
@[simp] theorem np_lDh_ne_npB : lDh ≠ npB := by decide
@[simp] theorem np_npB_ne_lDt : npB ≠ lDt := by decide
@[simp] theorem np_lDt_ne_npB : lDt ≠ npB := by decide
@[simp] theorem np_npB_ne_lDg : npB ≠ lDg := by decide
@[simp] theorem np_lDg_ne_npB : lDg ≠ npB := by decide
@[simp] theorem np_npB_ne_lDi : npB ≠ lDi := by decide
@[simp] theorem np_lDi_ne_npB : lDi ≠ npB := by decide
@[simp] theorem np_npB_ne_lRp : npB ≠ lRp := by decide
@[simp] theorem np_lRp_ne_npB : lRp ≠ npB := by decide
@[simp] theorem np_npB_ne_lRn : npB ≠ lRn := by decide
@[simp] theorem np_lRn_ne_npB : lRn ≠ npB := by decide
@[simp] theorem np_npB_ne_lDir : npB ≠ lDir := by decide
@[simp] theorem np_lDir_ne_npB : lDir ≠ npB := by decide
@[simp] theorem np_npB_ne_lFle : npB ≠ lFle := by decide
@[simp] theorem np_lFle_ne_npB : lFle ≠ npB := by decide
@[simp] theorem np_npB_ne_lKb : npB ≠ lKb := by decide
@[simp] theorem np_lKb_ne_npB : lKb ≠ npB := by decide
@[simp] theorem np_npL_ne_npE : npL ≠ npE := by decide
@[simp] theorem np_npL_ne_npW : npL ≠ npW := by decide
@[simp] theorem np_npL_ne_npB : npL ≠ npB := by decide
@[simp] theorem np_npL_ne_npO : npL ≠ npO := by decide
@[simp] theorem np_npL_ne_npD : npL ≠ npD := by decide
@[simp] theorem np_npL_ne_npT : npL ≠ npT := by decide
@[simp] theorem np_npL_ne_npF : npL ≠ npF := by decide
@[simp] theorem np_npL_ne_npX : npL ≠ npX := by decide
@[simp] theorem np_npL_ne_npC : npL ≠ npC := by decide
@[simp] theorem np_npL_ne_npU : npL ≠ npU := by decide
@[simp] theorem np_npL_ne_npS : npL ≠ npS := by decide
@[simp] theorem np_npL_ne_npEl : npL ≠ npEl := by decide
@[simp] theorem np_npL_ne_lFl : npL ≠ lFl := by decide
@[simp] theorem np_lFl_ne_npL : lFl ≠ npL := by decide
@[simp] theorem np_npL_ne_lDh : npL ≠ lDh := by decide
@[simp] theorem np_lDh_ne_npL : lDh ≠ npL := by decide
@[simp] theorem np_npL_ne_lDt : npL ≠ lDt := by decide
@[simp] theorem np_lDt_ne_npL : lDt ≠ npL := by decide
@[simp] theorem np_npL_ne_lDg : npL ≠ lDg := by decide
@[simp] theorem np_lDg_ne_npL : lDg ≠ npL := by decide
@[simp] theorem np_npL_ne_lDi : npL ≠ lDi := by decide
@[simp] theorem np_lDi_ne_npL : lDi ≠ npL := by decide
@[simp] theorem np_npL_ne_lRp : npL ≠ lRp := by decide
@[simp] theorem np_lRp_ne_npL : lRp ≠ npL := by decide
@[simp] theorem np_npL_ne_lRn : npL ≠ lRn := by decide
@[simp] theorem np_lRn_ne_npL : lRn ≠ npL := by decide
@[simp] theorem np_npL_ne_lDir : npL ≠ lDir := by decide
@[simp] theorem np_lDir_ne_npL : lDir ≠ npL := by decide
@[simp] theorem np_npL_ne_lFle : npL ≠ lFle := by decide
@[simp] theorem np_lFle_ne_npL : lFle ≠ npL := by decide
@[simp] theorem np_npL_ne_lKb : npL ≠ lKb := by decide
@[simp] theorem np_lKb_ne_npL : lKb ≠ npL := by decide
@[simp] theorem np_npO_ne_npE : npO ≠ npE := by decide
@[simp] theorem np_npO_ne_npW : npO ≠ npW := by decide
@[simp] theorem np_npO_ne_npB : npO ≠ npB := by decide
@[simp] theorem np_npO_ne_npL : npO ≠ npL := by decide
@[simp] theorem np_npO_ne_npD : npO ≠ npD := by decide
@[simp] theorem np_npO_ne_npT : npO ≠ npT := by decide
@[simp] theorem np_npO_ne_npF : npO ≠ npF := by decide
@[simp] theorem np_npO_ne_npX : npO ≠ npX := by decide
@[simp] theorem np_npO_ne_npC : npO ≠ npC := by decide
@[simp] theorem np_npO_ne_npU : npO ≠ npU := by decide
@[simp] theorem np_npO_ne_npS : npO ≠ npS := by decide
@[simp] theorem np_npO_ne_npEl : npO ≠ npEl := by decide
@[simp] theorem np_npO_ne_lFl : npO ≠ lFl := by decide
@[simp] theorem np_lFl_ne_npO : lFl ≠ npO := by decide
@[simp] theorem np_npO_ne_lDh : npO ≠ lDh := by decide
@[simp] theorem np_lDh_ne_npO : lDh ≠ npO := by decide
@[simp] theorem np_npO_ne_lDt : npO ≠ lDt := by decide
@[simp] theorem np_lDt_ne_npO : lDt ≠ npO := by decide
@[simp] theorem np_npO_ne_lDg : npO ≠ lDg := by decide
@[simp] theorem np_lDg_ne_npO : lDg ≠ npO := by decide
@[simp] theorem np_npO_ne_lDi : npO ≠ lDi := by decide
@[simp] theorem np_lDi_ne_npO : lDi ≠ npO := by decide
@[simp] theorem np_npO_ne_lRp : npO ≠ lRp := by decide
@[simp] theorem np_lRp_ne_npO : lRp ≠ npO := by decide
@[simp] theorem np_npO_ne_lRn : npO ≠ lRn := by decide
@[simp] theorem np_lRn_ne_npO : lRn ≠ npO := by decide
@[simp] theorem np_npO_ne_lDir : npO ≠ lDir := by decide
@[simp] theorem np_lDir_ne_npO : lDir ≠ npO := by decide
@[simp] theorem np_npO_ne_lFle : npO ≠ lFle := by decide
@[simp] theorem np_lFle_ne_npO : lFle ≠ npO := by decide
@[simp] theorem np_npO_ne_lKb : npO ≠ lKb := by decide
@[simp] theorem np_lKb_ne_npO : lKb ≠ npO := by decide
@[simp] theorem np_npD_ne_npE : npD ≠ npE := by decide
@[simp] theorem np_npD_ne_npW : npD ≠ npW := by decide
@[simp] theorem np_npD_ne_npB : npD ≠ npB := by decide
@[simp] theorem np_npD_ne_npL : npD ≠ npL := by decide
@[simp] theorem np_npD_ne_npO : npD ≠ npO := by decide
@[simp] theorem np_npD_ne_npT : npD ≠ npT := by decide
@[simp] theorem np_npD_ne_npF : npD ≠ npF := by decide
@[simp] theorem np_npD_ne_npX : npD ≠ npX := by decide
@[simp] theorem np_npD_ne_npC : npD ≠ npC := by decide
@[simp] theorem np_npD_ne_npU : npD ≠ npU := by decide
@[simp] theorem np_npD_ne_npS : npD ≠ npS := by decide
@[simp] theorem np_npD_ne_npEl : npD ≠ npEl := by decide
@[simp] theorem np_npD_ne_lFl : npD ≠ lFl := by decide
@[simp] theorem np_lFl_ne_npD : lFl ≠ npD := by decide
@[simp] theorem np_npD_ne_lDh : npD ≠ lDh := by decide
@[simp] theorem np_lDh_ne_npD : lDh ≠ npD := by decide
@[simp] theorem np_npD_ne_lDt : npD ≠ lDt := by decide
@[simp] theorem np_lDt_ne_npD : lDt ≠ npD := by decide
@[simp] theorem np_npD_ne_lDg : npD ≠ lDg := by decide
@[simp] theorem np_lDg_ne_npD : lDg ≠ npD := by decide
@[simp] theorem np_npD_ne_lDi : npD ≠ lDi := by decide
@[simp] theorem np_lDi_ne_npD : lDi ≠ npD := by decide
@[simp] theorem np_npD_ne_lRp : npD ≠ lRp := by decide
@[simp] theorem np_lRp_ne_npD : lRp ≠ npD := by decide
@[simp] theorem np_npD_ne_lRn : npD ≠ lRn := by decide
@[simp] theorem np_lRn_ne_npD : lRn ≠ npD := by decide
@[simp] theorem np_npD_ne_lDir : npD ≠ lDir := by decide
@[simp] theorem np_lDir_ne_npD : lDir ≠ npD := by decide
@[simp] theorem np_npD_ne_lFle : npD ≠ lFle := by decide
@[simp] theorem np_lFle_ne_npD : lFle ≠ npD := by decide
@[simp] theorem np_npD_ne_lKb : npD ≠ lKb := by decide
@[simp] theorem np_lKb_ne_npD : lKb ≠ npD := by decide
@[simp] theorem np_npT_ne_npE : npT ≠ npE := by decide
@[simp] theorem np_npT_ne_npW : npT ≠ npW := by decide
@[simp] theorem np_npT_ne_npB : npT ≠ npB := by decide
@[simp] theorem np_npT_ne_npL : npT ≠ npL := by decide
@[simp] theorem np_npT_ne_npO : npT ≠ npO := by decide
@[simp] theorem np_npT_ne_npD : npT ≠ npD := by decide
@[simp] theorem np_npT_ne_npF : npT ≠ npF := by decide
@[simp] theorem np_npT_ne_npX : npT ≠ npX := by decide
@[simp] theorem np_npT_ne_npC : npT ≠ npC := by decide
@[simp] theorem np_npT_ne_npU : npT ≠ npU := by decide
@[simp] theorem np_npT_ne_npS : npT ≠ npS := by decide
@[simp] theorem np_npT_ne_npEl : npT ≠ npEl := by decide
@[simp] theorem np_npT_ne_lFl : npT ≠ lFl := by decide
@[simp] theorem np_lFl_ne_npT : lFl ≠ npT := by decide
@[simp] theorem np_npT_ne_lDh : npT ≠ lDh := by decide
@[simp] theorem np_lDh_ne_npT : lDh ≠ npT := by decide
@[simp] theorem np_npT_ne_lDt : npT ≠ lDt := by decide
@[simp] theorem np_lDt_ne_npT : lDt ≠ npT := by decide
@[simp] theorem np_npT_ne_lDg : npT ≠ lDg := by decide
@[simp] theorem np_lDg_ne_npT : lDg ≠ npT := by decide
@[simp] theorem np_npT_ne_lDi : npT ≠ lDi := by decide
@[simp] theorem np_lDi_ne_npT : lDi ≠ npT := by decide
@[simp] theorem np_npT_ne_lRp : npT ≠ lRp := by decide
@[simp] theorem np_lRp_ne_npT : lRp ≠ npT := by decide
@[simp] theorem np_npT_ne_lRn : npT ≠ lRn := by decide
@[simp] theorem np_lRn_ne_npT : lRn ≠ npT := by decide
@[simp] theorem np_npT_ne_lDir : npT ≠ lDir := by decide
@[simp] theorem np_lDir_ne_npT : lDir ≠ npT := by decide
@[simp] theorem np_npT_ne_lFle : npT ≠ lFle := by decide
@[simp] theorem np_lFle_ne_npT : lFle ≠ npT := by decide
@[simp] theorem np_npT_ne_lKb : npT ≠ lKb := by decide
@[simp] theorem np_lKb_ne_npT : lKb ≠ npT := by decide
@[simp] theorem np_npF_ne_npE : npF ≠ npE := by decide
@[simp] theorem np_npF_ne_npW : npF ≠ npW := by decide
@[simp] theorem np_npF_ne_npB : npF ≠ npB := by decide
@[simp] theorem np_npF_ne_npL : npF ≠ npL := by decide
@[simp] theorem np_npF_ne_npO : npF ≠ npO := by decide
@[simp] theorem np_npF_ne_npD : npF ≠ npD := by decide
@[simp] theorem np_npF_ne_npT : npF ≠ npT := by decide
@[simp] theorem np_npF_ne_npX : npF ≠ npX := by decide
@[simp] theorem np_npF_ne_npC : npF ≠ npC := by decide
@[simp] theorem np_npF_ne_npU : npF ≠ npU := by decide
@[simp] theorem np_npF_ne_npS : npF ≠ npS := by decide
@[simp] theorem np_npF_ne_npEl : npF ≠ npEl := by decide
@[simp] theorem np_npF_ne_lFl : npF ≠ lFl := by decide
@[simp] theorem np_lFl_ne_npF : lFl ≠ npF := by decide
@[simp] theorem np_npF_ne_lDh : npF ≠ lDh := by decide
@[simp] theorem np_lDh_ne_npF : lDh ≠ npF := by decide
@[simp] theorem np_npF_ne_lDt : npF ≠ lDt := by decide
@[simp] theorem np_lDt_ne_npF : lDt ≠ npF := by decide
@[simp] theorem np_npF_ne_lDg : npF ≠ lDg := by decide
@[simp] theorem np_lDg_ne_npF : lDg ≠ npF := by decide
@[simp] theorem np_npF_ne_lDi : npF ≠ lDi := by decide
@[simp] theorem np_lDi_ne_npF : lDi ≠ npF := by decide
@[simp] theorem np_npF_ne_lRp : npF ≠ lRp := by decide
@[simp] theorem np_lRp_ne_npF : lRp ≠ npF := by decide
@[simp] theorem np_npF_ne_lRn : npF ≠ lRn := by decide
@[simp] theorem np_lRn_ne_npF : lRn ≠ npF := by decide
@[simp] theorem np_npF_ne_lDir : npF ≠ lDir := by decide
@[simp] theorem np_lDir_ne_npF : lDir ≠ npF := by decide
@[simp] theorem np_npF_ne_lFle : npF ≠ lFle := by decide
@[simp] theorem np_lFle_ne_npF : lFle ≠ npF := by decide
@[simp] theorem np_npF_ne_lKb : npF ≠ lKb := by decide
@[simp] theorem np_lKb_ne_npF : lKb ≠ npF := by decide
@[simp] theorem np_npX_ne_npE : npX ≠ npE := by decide
@[simp] theorem np_npX_ne_npW : npX ≠ npW := by decide
@[simp] theorem np_npX_ne_npB : npX ≠ npB := by decide
@[simp] theorem np_npX_ne_npL : npX ≠ npL := by decide
@[simp] theorem np_npX_ne_npO : npX ≠ npO := by decide
@[simp] theorem np_npX_ne_npD : npX ≠ npD := by decide
@[simp] theorem np_npX_ne_npT : npX ≠ npT := by decide
@[simp] theorem np_npX_ne_npF : npX ≠ npF := by decide
@[simp] theorem np_npX_ne_npC : npX ≠ npC := by decide
@[simp] theorem np_npX_ne_npU : npX ≠ npU := by decide
@[simp] theorem np_npX_ne_npS : npX ≠ npS := by decide
@[simp] theorem np_npX_ne_npEl : npX ≠ npEl := by decide
@[simp] theorem np_npX_ne_lFl : npX ≠ lFl := by decide
@[simp] theorem np_lFl_ne_npX : lFl ≠ npX := by decide
@[simp] theorem np_npX_ne_lDh : npX ≠ lDh := by decide
@[simp] theorem np_lDh_ne_npX : lDh ≠ npX := by decide
@[simp] theorem np_npX_ne_lDt : npX ≠ lDt := by decide
@[simp] theorem np_lDt_ne_npX : lDt ≠ npX := by decide
@[simp] theorem np_npX_ne_lDg : npX ≠ lDg := by decide
@[simp] theorem np_lDg_ne_npX : lDg ≠ npX := by decide
@[simp] theorem np_npX_ne_lDi : npX ≠ lDi := by decide
@[simp] theorem np_lDi_ne_npX : lDi ≠ npX := by decide
@[simp] theorem np_npX_ne_lRp : npX ≠ lRp := by decide
@[simp] theorem np_lRp_ne_npX : lRp ≠ npX := by decide
@[simp] theorem np_npX_ne_lRn : npX ≠ lRn := by decide
@[simp] theorem np_lRn_ne_npX : lRn ≠ npX := by decide
@[simp] theorem np_npX_ne_lDir : npX ≠ lDir := by decide
@[simp] theorem np_lDir_ne_npX : lDir ≠ npX := by decide
@[simp] theorem np_npX_ne_lFle : npX ≠ lFle := by decide
@[simp] theorem np_lFle_ne_npX : lFle ≠ npX := by decide
@[simp] theorem np_npX_ne_lKb : npX ≠ lKb := by decide
@[simp] theorem np_lKb_ne_npX : lKb ≠ npX := by decide
@[simp] theorem np_npC_ne_npE : npC ≠ npE := by decide
@[simp] theorem np_npC_ne_npW : npC ≠ npW := by decide
@[simp] theorem np_npC_ne_npB : npC ≠ npB := by decide
@[simp] theorem np_npC_ne_npL : npC ≠ npL := by decide
@[simp] theorem np_npC_ne_npO : npC ≠ npO := by decide
@[simp] theorem np_npC_ne_npD : npC ≠ npD := by decide
@[simp] theorem np_npC_ne_npT : npC ≠ npT := by decide
@[simp] theorem np_npC_ne_npF : npC ≠ npF := by decide
@[simp] theorem np_npC_ne_npX : npC ≠ npX := by decide
@[simp] theorem np_npC_ne_npU : npC ≠ npU := by decide
@[simp] theorem np_npC_ne_npS : npC ≠ npS := by decide
@[simp] theorem np_npC_ne_npEl : npC ≠ npEl := by decide
@[simp] theorem np_npC_ne_lFl : npC ≠ lFl := by decide
@[simp] theorem np_lFl_ne_npC : lFl ≠ npC := by decide
@[simp] theorem np_npC_ne_lDh : npC ≠ lDh := by decide
@[simp] theorem np_lDh_ne_npC : lDh ≠ npC := by decide
@[simp] theorem np_npC_ne_lDt : npC ≠ lDt := by decide
@[simp] theorem np_lDt_ne_npC : lDt ≠ npC := by decide
@[simp] theorem np_npC_ne_lDg : npC ≠ lDg := by decide
@[simp] theorem np_lDg_ne_npC : lDg ≠ npC := by decide
@[simp] theorem np_npC_ne_lDi : npC ≠ lDi := by decide
@[simp] theorem np_lDi_ne_npC : lDi ≠ npC := by decide
@[simp] theorem np_npC_ne_lRp : npC ≠ lRp := by decide
@[simp] theorem np_lRp_ne_npC : lRp ≠ npC := by decide
@[simp] theorem np_npC_ne_lRn : npC ≠ lRn := by decide
@[simp] theorem np_lRn_ne_npC : lRn ≠ npC := by decide
@[simp] theorem np_npC_ne_lDir : npC ≠ lDir := by decide
@[simp] theorem np_lDir_ne_npC : lDir ≠ npC := by decide
@[simp] theorem np_npC_ne_lFle : npC ≠ lFle := by decide
@[simp] theorem np_lFle_ne_npC : lFle ≠ npC := by decide
@[simp] theorem np_npC_ne_lKb : npC ≠ lKb := by decide
@[simp] theorem np_lKb_ne_npC : lKb ≠ npC := by decide
@[simp] theorem np_npU_ne_npE : npU ≠ npE := by decide
@[simp] theorem np_npU_ne_npW : npU ≠ npW := by decide
@[simp] theorem np_npU_ne_npB : npU ≠ npB := by decide
@[simp] theorem np_npU_ne_npL : npU ≠ npL := by decide
@[simp] theorem np_npU_ne_npO : npU ≠ npO := by decide
@[simp] theorem np_npU_ne_npD : npU ≠ npD := by decide
@[simp] theorem np_npU_ne_npT : npU ≠ npT := by decide
@[simp] theorem np_npU_ne_npF : npU ≠ npF := by decide
@[simp] theorem np_npU_ne_npX : npU ≠ npX := by decide
@[simp] theorem np_npU_ne_npC : npU ≠ npC := by decide
@[simp] theorem np_npU_ne_npS : npU ≠ npS := by decide
@[simp] theorem np_npU_ne_npEl : npU ≠ npEl := by decide
@[simp] theorem np_npU_ne_lFl : npU ≠ lFl := by decide
@[simp] theorem np_lFl_ne_npU : lFl ≠ npU := by decide
@[simp] theorem np_npU_ne_lDh : npU ≠ lDh := by decide
@[simp] theorem np_lDh_ne_npU : lDh ≠ npU := by decide
@[simp] theorem np_npU_ne_lDt : npU ≠ lDt := by decide
@[simp] theorem np_lDt_ne_npU : lDt ≠ npU := by decide
@[simp] theorem np_npU_ne_lDg : npU ≠ lDg := by decide
@[simp] theorem np_lDg_ne_npU : lDg ≠ npU := by decide
@[simp] theorem np_npU_ne_lDi : npU ≠ lDi := by decide
@[simp] theorem np_lDi_ne_npU : lDi ≠ npU := by decide
@[simp] theorem np_npU_ne_lRp : npU ≠ lRp := by decide
@[simp] theorem np_lRp_ne_npU : lRp ≠ npU := by decide
@[simp] theorem np_npU_ne_lRn : npU ≠ lRn := by decide
@[simp] theorem np_lRn_ne_npU : lRn ≠ npU := by decide
@[simp] theorem np_npU_ne_lDir : npU ≠ lDir := by decide
@[simp] theorem np_lDir_ne_npU : lDir ≠ npU := by decide
@[simp] theorem np_npU_ne_lFle : npU ≠ lFle := by decide
@[simp] theorem np_lFle_ne_npU : lFle ≠ npU := by decide
@[simp] theorem np_npU_ne_lKb : npU ≠ lKb := by decide
@[simp] theorem np_lKb_ne_npU : lKb ≠ npU := by decide
@[simp] theorem np_npS_ne_npE : npS ≠ npE := by decide
@[simp] theorem np_npS_ne_npW : npS ≠ npW := by decide
@[simp] theorem np_npS_ne_npB : npS ≠ npB := by decide
@[simp] theorem np_npS_ne_npL : npS ≠ npL := by decide
@[simp] theorem np_npS_ne_npO : npS ≠ npO := by decide
@[simp] theorem np_npS_ne_npD : npS ≠ npD := by decide
@[simp] theorem np_npS_ne_npT : npS ≠ npT := by decide
@[simp] theorem np_npS_ne_npF : npS ≠ npF := by decide
@[simp] theorem np_npS_ne_npX : npS ≠ npX := by decide
@[simp] theorem np_npS_ne_npC : npS ≠ npC := by decide
@[simp] theorem np_npS_ne_npU : npS ≠ npU := by decide
@[simp] theorem np_npS_ne_npEl : npS ≠ npEl := by decide
@[simp] theorem np_npS_ne_lFl : npS ≠ lFl := by decide
@[simp] theorem np_lFl_ne_npS : lFl ≠ npS := by decide
@[simp] theorem np_npS_ne_lDh : npS ≠ lDh := by decide
@[simp] theorem np_lDh_ne_npS : lDh ≠ npS := by decide
@[simp] theorem np_npS_ne_lDt : npS ≠ lDt := by decide
@[simp] theorem np_lDt_ne_npS : lDt ≠ npS := by decide
@[simp] theorem np_npS_ne_lDg : npS ≠ lDg := by decide
@[simp] theorem np_lDg_ne_npS : lDg ≠ npS := by decide
@[simp] theorem np_npS_ne_lDi : npS ≠ lDi := by decide
@[simp] theorem np_lDi_ne_npS : lDi ≠ npS := by decide
@[simp] theorem np_npS_ne_lRp : npS ≠ lRp := by decide
@[simp] theorem np_lRp_ne_npS : lRp ≠ npS := by decide
@[simp] theorem np_npS_ne_lRn : npS ≠ lRn := by decide
@[simp] theorem np_lRn_ne_npS : lRn ≠ npS := by decide
@[simp] theorem np_npS_ne_lDir : npS ≠ lDir := by decide
@[simp] theorem np_lDir_ne_npS : lDir ≠ npS := by decide
@[simp] theorem np_npS_ne_lFle : npS ≠ lFle := by decide
@[simp] theorem np_lFle_ne_npS : lFle ≠ npS := by decide
@[simp] theorem np_npS_ne_lKb : npS ≠ lKb := by decide
@[simp] theorem np_lKb_ne_npS : lKb ≠ npS := by decide
@[simp] theorem np_npEl_ne_npE : npEl ≠ npE := by decide
@[simp] theorem np_npEl_ne_npW : npEl ≠ npW := by decide
@[simp] theorem np_npEl_ne_npB : npEl ≠ npB := by decide
@[simp] theorem np_npEl_ne_npL : npEl ≠ npL := by decide
@[simp] theorem np_npEl_ne_npO : npEl ≠ npO := by decide
@[simp] theorem np_npEl_ne_npD : npEl ≠ npD := by decide
@[simp] theorem np_npEl_ne_npT : npEl ≠ npT := by decide
@[simp] theorem np_npEl_ne_npF : npEl ≠ npF := by decide
@[simp] theorem np_npEl_ne_npX : npEl ≠ npX := by decide
@[simp] theorem np_npEl_ne_npC : npEl ≠ npC := by decide
@[simp] theorem np_npEl_ne_npU : npEl ≠ npU := by decide
@[simp] theorem np_npEl_ne_npS : npEl ≠ npS := by decide
@[simp] theorem np_npEl_ne_lFl : npEl ≠ lFl := by decide
@[simp] theorem np_lFl_ne_npEl : lFl ≠ npEl := by decide
@[simp] theorem np_npEl_ne_lDh : npEl ≠ lDh := by decide
@[simp] theorem np_lDh_ne_npEl : lDh ≠ npEl := by decide
@[simp] theorem np_npEl_ne_lDt : npEl ≠ lDt := by decide
@[simp] theorem np_lDt_ne_npEl : lDt ≠ npEl := by decide
@[simp] theorem np_npEl_ne_lDg : npEl ≠ lDg := by decide
@[simp] theorem np_lDg_ne_npEl : lDg ≠ npEl := by decide
@[simp] theorem np_npEl_ne_lDi : npEl ≠ lDi := by decide
@[simp] theorem np_lDi_ne_npEl : lDi ≠ npEl := by decide
@[simp] theorem np_npEl_ne_lRp : npEl ≠ lRp := by decide
@[simp] theorem np_lRp_ne_npEl : lRp ≠ npEl := by decide
@[simp] theorem np_npEl_ne_lRn : npEl ≠ lRn := by decide
@[simp] theorem np_lRn_ne_npEl : lRn ≠ npEl := by decide
@[simp] theorem np_npEl_ne_lDir : npEl ≠ lDir := by decide
@[simp] theorem np_lDir_ne_npEl : lDir ≠ npEl := by decide
@[simp] theorem np_npEl_ne_lFle : npEl ≠ lFle := by decide
@[simp] theorem np_lFle_ne_npEl : lFle ≠ npEl := by decide
@[simp] theorem np_npEl_ne_lKb : npEl ≠ lKb := by decide
@[simp] theorem np_lKb_ne_npEl : lKb ≠ npEl := by decide

def npLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, npW, npB, npL, npO, npD, npT, npF, npX, npC, npU, npS, npEl]
def npBody (C : Ctx) : ProgHOL 64 := prologue npLocals (.ite (tagIsE npE 8) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv npE)) (.seq eViewP (.seq (.assign .local npW (.load .one (vv lRp))) (.ite (.cmp .equal (vv npW) (.const 0)) (.seq (.call (some (some (.local, npB), none)) fLitH [(vv npE)]) (.seq (.assign .local npL (.load .one (vv npB))) (.ite (.cmp .equal (vv npL) (.const 0)) (.return (.const 0)) (allocP C npO (.const 16) (.seq (.store (vv npO) (.const 1)) (.seq (.store (.op .add [(vv npO), (.const 8)]) (.const 1)) (.seq (.call (some (some (.local, npD), none)) fSub [(vv npB), (vv npO)]) (.seq (.call (some (some (.local, npT), none)) fLitB [(vv npD)]) (.return (.op .add [(vv npT), (.const 1)])))))))))) (.return (.const 0))))))) (.ite (tagIs4E npE) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv npE)) (.seq eViewP (.seq (.assign .local npF (.load .one (vv lRp))) (.seq (.assign .local npX (.load .one (.op .add [(vv lRp), (.const 8)]))) (.ite (tagIsE npF 3) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv npF)) (.seq eViewP (.seq (.assign .local npC (.load .one (vv lRp))) (.seq (.assign .local npU (.load .one (.op .add [(vv lRp), (.const 8)]))) (.seq (.assign .local npEl (.load .one (.const (ecell C (C.PO + pinCount + 0))))) (.seq (.assign .local npS (.load .one (.const (ecell C (C.PO + PIN_NAT_SUCC))))) (.ite (.op .and [.cmp .equal (vv npC) (vv npS), .cmp .equal (vv npU) (vv npEl)]) (.return (.op .add [(vv npX), (.const 1)])) (.return (.const 0)))))))))) (.return (.const 0)))))))) (.return (.const 0))))

section
variable {σ : Type}

theorem np_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : NlCodes C)
    (s : AState) (e : EIdx) :
    SpecR (σ := σ) (Pre C s ([npE].zip [Enc.idxW e])) (npBody C) s (natPred? e) (UD.PostO C) := by
  refine specR_prologue (UD.postO_locals C) (Knot.params_none C npLocals [npE] _ (by decide) (by decide)) ?_
  unfold natPred?
  have hno : ∀ {H : List (BitVec 64)} {s' : AState} {Γ : Env} {M : Mem} {D : List MlS}, C.H <+: H →
      SpecR (σ := σ) (Inv (ctxH C H) s' Γ M D) (.return (.const 0)) s' (pure none) (UD.PostO C) :=
    fun {H s' Γ M D} hp => specR_returnI _ (optW none) (by simp [optW, optWG]; rfl)
      (fun t ht => ⟨H, hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine Knot.specR_tagIteV npE e 8 (by decide) (by decide) (by simp +decide [Env.get, ctxEnv]) (fun htg => ?_)
    (fun htg => ?_)
  · rw [ite_eq_left (show (e.tag == ETag.lit) = true by simp [htg, ETag.lit])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv npE) (Enc.idxW e) (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine ILP.specR_viewIv e (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
      (fun v P hv htn _ => ?_)
    have h8 : v.tagN = 8 := by rw [htn, htg]; rfl
    obtain ⟨l, rfl⟩ := tagN_lit h8
    rcases l with m | str
    swap
    · refine specR_loadI' npW (vv lRp) P (P + BitVec.ofNat 64 0) 1 (by decide) (by simp) (by simp)
        (by simpa [encEView, Enc.encLit] using wordsAt_mem0 P 1 (strW str) []) ?_
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
        (fun _ => ?_)
      dsimp only
      exact hno (H := C.H) (List.prefix_refl _)
    refine specR_loadI' npW (vv lRp) P (P + BitVec.ofNat 64 0) 0 (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encLit] using wordsAt_mem0 P 0 (limbs m) []) ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    refine specR_dropM ?_
    refine specR_congr (m' := (pure m : AM Nat) >>= fun m => (match ENodeView.lit (.natVal m) with
      | .lit (.natVal (n + 1)) => do
        let l ← internE (.lit (.natVal n))
        pure (some l)
      | _ => pure none)) rfl ?_
    refine specR_callPH (C := C) (k := fun m => (match ENodeView.lit (.natVal m) with
      | .lit (.natVal (n + 1)) => do
        let l ← internE (.lit (.natVal n))
        pure (some l)
      | _ => pure none)) npB fLitH [Big.cH] [vv npE] (litBody C) [Enc.idxW e] m (by decide) rfl (by decide) hc.lit
      ⟨by simp +decide [Env.get, ctxEnv], trivial⟩ (lit_spec C hok s e m hv) (fun H1 o hp1 hb => ?_)
    refine UD.specR_heapLoadI' (C := ctxH C H1) npL (vv npB) o _ hb.1 (by decide) (by simp; rfl) ?_
    refine specR_atEntry fun t0 ht0 => ?_
    have hsl := blk_small0 (ctxOK_H hok H1) ht0.sr hb
    have hok1 := ctxOK_H hok H1
    cases m with
    | zero =>
      rw [limbs_zero] at hb hsl ⊢
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      exact hno hp1
    | succ k =>
      have hpos : (limbs (k + 1)).length ≠ 0 := by rw [limbs_pos (by omega)]; simp
      have hne : BitVec.ofNat 64 (limbs (k + 1)).length ≠ 0 := by
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
        (fun h => absurd rfl h) (fun _ => ?_)
      dsimp only
      refine specR_allocI (C := ctxH C H1) npO (.const 16) 2 (by norm_num) (by decide) (fun v => by simp [sev])
        (fun H3 ws hpre hwl hcap => ?_)
      have hpl : H1.length ≤ H3.length := hpre.length_le
      have hj : H3.length < (ctxH (ctxH C H1) (H3 ++ ws)).H.length := by show _ < (H3 ++ ws).length; simp; omega
      refine specR_heapStoreI (ctxOK_H hok _) (vv npO) (.const 1) _ hj 1 (by simp; rfl) rfl ?_
      have hj2 : H3.length + 1 < (ctxH (ctxH C H1) ((H3 ++ ws).set H3.length 1)).H.length := by
        show _ < ((H3 ++ ws).set _ _).length; simp; omega
      refine specR_heapStoreI (ctxOK_H hok _) _ (.const 1) _ hj2 1 (by simp [sev]; exact cellA_add8 C _) rfl ?_
      let H4 := ((H3 ++ ws).set H3.length 1).set (H3.length + 1) 1
      have hp1' := prefix_set_ge ((show H1 <+: H3 from hpre).trans (List.prefix_append _ ws)) _ hpl (1 : BitVec 64)
      have hp4 : H1 <+: H4 := prefix_set_ge hp1' (H3.length + 1) (by omega) (1 : BitVec 64)
      have hbo : BlkAt H4 H3.length (limbs 1) := by
        rw [show limbs 1 = [BitVec.ofNat 64 1] by rw [limbs_word 1 (by decide)]; rfl]
        refine ⟨?_, fun i hi => ?_⟩
        · show (((H3 ++ ws).set H3.length 1).set (H3.length + 1) 1)[H3.length]? = _
          rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]; rfl
        · have : i = 0 := by simpa using hi
          subst this
          show (((H3 ++ ws).set H3.length 1).set (H3.length + 1) 1)[H3.length + 1 + 0]? = _
          rw [List.getElem?_set_self (by simp; omega)]; rfl
      have hb4 : BlkAt H4 o (limbs (k + 1)) := blkAt_mono hb hp4
      have hok4 := ctxOK_H hok H4
      refine specR_callPH (C := ctxH C H4) (k := fun m => internE (.lit (.natVal m)) >>= fun l => pure (some l))
        npD fSub subParams [vv npB, vv npO] (subBody C) [cellA C o, cellA C H3.length] (k + 1 - 1) (by decide) rfl
        (by decide) hc.sub ⟨by simp, by simp; rfl, trivial⟩
        (sub_spec (ctxH C H4) hok4 s (k + 1) 1 o H3.length hb4 hbo (by omega)
          (by rw [show limbs 1 = [BitVec.ofNat 64 1] by rw [limbs_word 1 (by decide)]; rfl]; simp; omega)
          (by omega)) (fun H5 od hp5 hbd => ?_)
      have hok5 := ctxOK_H hok H5
      simp only [Nat.add_sub_cancel] at hbd ⊢
      refine specR_callKH (C := ctxH C H5) npT fLitB [iLx] [vv npD] (litBlkBody C) [cellA C od] (by decide) rfl
        (by decide) hc.litb ⟨by simp; rfl, trivial⟩ (litBlk_spec ra (ctxH C H5) hok5 s k od hbd)
        (fun l s2 H6 hp6 => ?_)
      exact specR_returnI _ (optW (some l)) (by simp [sev, optW, optWG])
        (fun t ht => ⟨H6, hp1.trans (hp4.trans (hp5.trans hp6)), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · rw [ite_eq_right (show ¬ (e.tag == ETag.lit) = true by simpa [ETag.lit] using htg)]
    refine specR_tag4IteE npE e (by simp +decide [Env.get, ctxEnv]) (fun ht4 => ?_) (fun ht4 => ?_)
    swap
    · rw [ite_eq_right (show ¬ (e.tag == ETag.app) = true by simpa [ETag.app] using ht4)]
      exact hno (H := C.H) (List.prefix_refl _)
    rw [ite_eq_left (show (e.tag == ETag.app) = true by simp [ht4, ETag.app])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv npE) (Enc.idxW e) (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_viewAppI e ht4 (by simp) (by simp +decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
      (fun f x P => ?_)
    dsimp only
    refine specR_loadI' npF _ (P + 0) P (Enc.idxW f) (by decide) (by simp [sev]) (by simp) (List.mem_cons_self ..) ?_
    refine specR_loadI' npX _ (P + 8) (P + 8) (Enc.idxW x) (by decide) (by simp +decide [sev]) rfl
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ?_
    refine specR_dropM ?_
    refine Knot.specR_tagIteV npF f 3 (by decide) (by decide) (by simp) (fun htc => ?_) (fun htc => ?_)
    swap
    · rw [ite_eq_right (show ¬ (f.tag == ETag.const) = true by simpa [ETag.const] using htc)]
      exact hno (H := C.H) (List.prefix_refl _)
    rw [ite_eq_left (show (f.tag == ETag.const) = true by simp [htc, ETag.const])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv npF) (Enc.idxW f) (by decide) (by simp) ?_
    refine specR_viewP f (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
      (fun v P2 hv htn _ => ?_)
    refine specR_congr (view_bind_eq f v _ s hv) ?_
    have h3 : v.tagN = 3 := by rw [htn, htc]; rfl
    obtain ⟨c, us, rfl⟩ := UD.tagN_const h3
    dsimp only
    refine specR_loadI' npC (vv lRp) P2 (P2 + BitVec.ofNat 64 0) (Enc.idxW c) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P2 (Enc.idxW c) [Enc.idxW us] []) ?_
    refine specR_loadI' npU _ (P2 + 8) (P2 + BitVec.ofNat 64 8) (Enc.idxW us) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P2 (Enc.idxW c) (Enc.idxW us) [] []) ?_
    refine specR_dropM ?_
    refine specR_pinXI hok pinEmptyLevels 0 C.pins.emptyLevels _ (fun s hp => pinEmptyLevels_run hok hp)
      (pin_emptyLevels_cell hok) npEl (by decide) ?_
    unfold pinNatSucc
    refine specR_pinAtI hok PIN_NAT_SUCC (by decide) npS (by decide) ?_
    by_cases e1 : c = C.pins.names[PIN_NAT_SUCC]'(by rw [hok.pinsRel.1]; decide)
    · by_cases e2 : us = C.pins.emptyLevels
      · refine specR_ifI _ 1 (by simp [sev, e1, e2, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
          (fun h => absurd h (by decide))
        simp only [e1, e2, beq_self_eq_true, Bool.and_self, ↓reduceIte]
        exact specR_returnI _ (optW (some x)) (by simp [sev, optW, optWG])
          (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      · have : Enc.idxW us ≠ Enc.idxW C.pins.emptyLevels := fun x => e2 (Enc.idxW_inj x)
        refine specR_ifI _ 0 (by simp [sev, e1, this, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
          (fun _ => ?_)
        rw [ite_eq_right (by simp [e2])]
        exact hno (H := C.H) (List.prefix_refl _)
    · have : Enc.idxW c ≠ Enc.idxW (C.pins.names[PIN_NAT_SUCC]'(by rw [hok.pinsRel.1]; decide)) :=
        fun x => e1 (Enc.idxW_inj x)
      refine specR_ifI _ 0 (by simp [sev, this, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
        (fun _ => ?_)
      rw [ite_eq_right (by simp [e1])]
      exact hno (H := C.H) (List.prefix_refl _)

end

end ConPanqueque.T.WC
