import ConPanqueque.T.Core.LeavesSub
import ConPanqueque.T.Ind.Large
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `mentionsAnyGo`: does any of the block's names occur, memoized on the node

The positivity walk's question at `k` names (`blockIsRec`'s `piDomsMentionAny`). `leavesSubGo`'s port shape:
the memo a heap memo list keyed by the handle (`LbRep`), each answer a fresh pair block `[answer, memo]`. The
twin views first; the leaves (`bvar`, `sort`, `lit`, `const`) answer without the memo, a `const` by a scan of
the names block (`lpsHas`). Every other node consults the memo, then walks every child (no short circuit) and
joins the answers with `or`; a `proj` also tests its structure name.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.Ind
open ConPanqueque.V.Enc

def mxF := ofString "mxf"
def mxNs := ofString "mxns"
def mxNn := ofString "mxnn"
def mxH := ofString "mxh"
def mxM := ofString "mxm"
def mxL := ofString "mxl"
def mxC1 := ofString "mxc1"
def mxC2 := ofString "mxc2"
def mxC3 := ofString "mxc3"
def mxS := ofString "mxs"
def mxR := ofString "mxr"
def mxM2 := ofString "mxm2"
def mxK1 := ofString "mxk1"
def mxK2 := ofString "mxk2"
def mxK3 := ofString "mxk3"
def mxB1 := ofString "mxb1"
def mxB2 := ofString "mxb2"
def mxQ := ofString "mxq"
def mxN := ofString "mxn"
def mxO := ofString "mxo"
def fMx := ofString "mentionsAnyGo"

@[simp] theorem mx_mxF_ne_mxNs : mxF ≠ mxNs := by decide
@[simp] theorem mx_mxF_ne_mxNn : mxF ≠ mxNn := by decide
@[simp] theorem mx_mxF_ne_mxH : mxF ≠ mxH := by decide
@[simp] theorem mx_mxF_ne_mxM : mxF ≠ mxM := by decide
@[simp] theorem mx_mxF_ne_mxL : mxF ≠ mxL := by decide
@[simp] theorem mx_mxF_ne_mxC1 : mxF ≠ mxC1 := by decide
@[simp] theorem mx_mxF_ne_mxC2 : mxF ≠ mxC2 := by decide
@[simp] theorem mx_mxF_ne_mxC3 : mxF ≠ mxC3 := by decide
@[simp] theorem mx_mxF_ne_mxS : mxF ≠ mxS := by decide
@[simp] theorem mx_mxF_ne_mxR : mxF ≠ mxR := by decide
@[simp] theorem mx_mxF_ne_mxM2 : mxF ≠ mxM2 := by decide
@[simp] theorem mx_mxF_ne_mxK1 : mxF ≠ mxK1 := by decide
@[simp] theorem mx_mxF_ne_mxK2 : mxF ≠ mxK2 := by decide
@[simp] theorem mx_mxF_ne_mxK3 : mxF ≠ mxK3 := by decide
@[simp] theorem mx_mxF_ne_mxB1 : mxF ≠ mxB1 := by decide
@[simp] theorem mx_mxF_ne_mxB2 : mxF ≠ mxB2 := by decide
@[simp] theorem mx_mxF_ne_mxQ : mxF ≠ mxQ := by decide
@[simp] theorem mx_mxF_ne_mxN : mxF ≠ mxN := by decide
@[simp] theorem mx_mxF_ne_mxO : mxF ≠ mxO := by decide
@[simp] theorem mx_mxF_ne_lKb : mxF ≠ lKb := by decide
@[simp] theorem mx_lKb_ne_mxF : lKb ≠ mxF := by decide
@[simp] theorem mx_mxF_ne_lFl : mxF ≠ lFl := by decide
@[simp] theorem mx_lFl_ne_mxF : lFl ≠ mxF := by decide
@[simp] theorem mx_mxF_ne_lDh : mxF ≠ lDh := by decide
@[simp] theorem mx_lDh_ne_mxF : lDh ≠ mxF := by decide
@[simp] theorem mx_mxF_ne_lDt : mxF ≠ lDt := by decide
@[simp] theorem mx_lDt_ne_mxF : lDt ≠ mxF := by decide
@[simp] theorem mx_mxF_ne_lDg : mxF ≠ lDg := by decide
@[simp] theorem mx_lDg_ne_mxF : lDg ≠ mxF := by decide
@[simp] theorem mx_mxF_ne_lDi : mxF ≠ lDi := by decide
@[simp] theorem mx_lDi_ne_mxF : lDi ≠ mxF := by decide
@[simp] theorem mx_mxF_ne_lDo1 : mxF ≠ lDo1 := by decide
@[simp] theorem mx_lDo1_ne_mxF : lDo1 ≠ mxF := by decide
@[simp] theorem mx_mxF_ne_lDo2 : mxF ≠ lDo2 := by decide
@[simp] theorem mx_lDo2_ne_mxF : lDo2 ≠ mxF := by decide
@[simp] theorem mx_mxF_ne_lRp : mxF ≠ lRp := by decide
@[simp] theorem mx_lRp_ne_mxF : lRp ≠ mxF := by decide
@[simp] theorem mx_mxF_ne_lRn : mxF ≠ lRn := by decide
@[simp] theorem mx_lRn_ne_mxF : lRn ≠ mxF := by decide
@[simp] theorem mx_mxF_ne_lFle : mxF ≠ lFle := by decide
@[simp] theorem mx_lFle_ne_mxF : lFle ≠ mxF := by decide
@[simp] theorem mx_mxF_ne_lDir : mxF ≠ lDir := by decide
@[simp] theorem mx_lDir_ne_mxF : lDir ≠ mxF := by decide
@[simp] theorem mx_mxNs_ne_mxF : mxNs ≠ mxF := by decide
@[simp] theorem mx_mxNs_ne_mxNn : mxNs ≠ mxNn := by decide
@[simp] theorem mx_mxNs_ne_mxH : mxNs ≠ mxH := by decide
@[simp] theorem mx_mxNs_ne_mxM : mxNs ≠ mxM := by decide
@[simp] theorem mx_mxNs_ne_mxL : mxNs ≠ mxL := by decide
@[simp] theorem mx_mxNs_ne_mxC1 : mxNs ≠ mxC1 := by decide
@[simp] theorem mx_mxNs_ne_mxC2 : mxNs ≠ mxC2 := by decide
@[simp] theorem mx_mxNs_ne_mxC3 : mxNs ≠ mxC3 := by decide
@[simp] theorem mx_mxNs_ne_mxS : mxNs ≠ mxS := by decide
@[simp] theorem mx_mxNs_ne_mxR : mxNs ≠ mxR := by decide
@[simp] theorem mx_mxNs_ne_mxM2 : mxNs ≠ mxM2 := by decide
@[simp] theorem mx_mxNs_ne_mxK1 : mxNs ≠ mxK1 := by decide
@[simp] theorem mx_mxNs_ne_mxK2 : mxNs ≠ mxK2 := by decide
@[simp] theorem mx_mxNs_ne_mxK3 : mxNs ≠ mxK3 := by decide
@[simp] theorem mx_mxNs_ne_mxB1 : mxNs ≠ mxB1 := by decide
@[simp] theorem mx_mxNs_ne_mxB2 : mxNs ≠ mxB2 := by decide
@[simp] theorem mx_mxNs_ne_mxQ : mxNs ≠ mxQ := by decide
@[simp] theorem mx_mxNs_ne_mxN : mxNs ≠ mxN := by decide
@[simp] theorem mx_mxNs_ne_mxO : mxNs ≠ mxO := by decide
@[simp] theorem mx_mxNs_ne_lKb : mxNs ≠ lKb := by decide
@[simp] theorem mx_lKb_ne_mxNs : lKb ≠ mxNs := by decide
@[simp] theorem mx_mxNs_ne_lFl : mxNs ≠ lFl := by decide
@[simp] theorem mx_lFl_ne_mxNs : lFl ≠ mxNs := by decide
@[simp] theorem mx_mxNs_ne_lDh : mxNs ≠ lDh := by decide
@[simp] theorem mx_lDh_ne_mxNs : lDh ≠ mxNs := by decide
@[simp] theorem mx_mxNs_ne_lDt : mxNs ≠ lDt := by decide
@[simp] theorem mx_lDt_ne_mxNs : lDt ≠ mxNs := by decide
@[simp] theorem mx_mxNs_ne_lDg : mxNs ≠ lDg := by decide
@[simp] theorem mx_lDg_ne_mxNs : lDg ≠ mxNs := by decide
@[simp] theorem mx_mxNs_ne_lDi : mxNs ≠ lDi := by decide
@[simp] theorem mx_lDi_ne_mxNs : lDi ≠ mxNs := by decide
@[simp] theorem mx_mxNs_ne_lDo1 : mxNs ≠ lDo1 := by decide
@[simp] theorem mx_lDo1_ne_mxNs : lDo1 ≠ mxNs := by decide
@[simp] theorem mx_mxNs_ne_lDo2 : mxNs ≠ lDo2 := by decide
@[simp] theorem mx_lDo2_ne_mxNs : lDo2 ≠ mxNs := by decide
@[simp] theorem mx_mxNs_ne_lRp : mxNs ≠ lRp := by decide
@[simp] theorem mx_lRp_ne_mxNs : lRp ≠ mxNs := by decide
@[simp] theorem mx_mxNs_ne_lRn : mxNs ≠ lRn := by decide
@[simp] theorem mx_lRn_ne_mxNs : lRn ≠ mxNs := by decide
@[simp] theorem mx_mxNs_ne_lFle : mxNs ≠ lFle := by decide
@[simp] theorem mx_lFle_ne_mxNs : lFle ≠ mxNs := by decide
@[simp] theorem mx_mxNs_ne_lDir : mxNs ≠ lDir := by decide
@[simp] theorem mx_lDir_ne_mxNs : lDir ≠ mxNs := by decide
@[simp] theorem mx_mxNn_ne_mxF : mxNn ≠ mxF := by decide
@[simp] theorem mx_mxNn_ne_mxNs : mxNn ≠ mxNs := by decide
@[simp] theorem mx_mxNn_ne_mxH : mxNn ≠ mxH := by decide
@[simp] theorem mx_mxNn_ne_mxM : mxNn ≠ mxM := by decide
@[simp] theorem mx_mxNn_ne_mxL : mxNn ≠ mxL := by decide
@[simp] theorem mx_mxNn_ne_mxC1 : mxNn ≠ mxC1 := by decide
@[simp] theorem mx_mxNn_ne_mxC2 : mxNn ≠ mxC2 := by decide
@[simp] theorem mx_mxNn_ne_mxC3 : mxNn ≠ mxC3 := by decide
@[simp] theorem mx_mxNn_ne_mxS : mxNn ≠ mxS := by decide
@[simp] theorem mx_mxNn_ne_mxR : mxNn ≠ mxR := by decide
@[simp] theorem mx_mxNn_ne_mxM2 : mxNn ≠ mxM2 := by decide
@[simp] theorem mx_mxNn_ne_mxK1 : mxNn ≠ mxK1 := by decide
@[simp] theorem mx_mxNn_ne_mxK2 : mxNn ≠ mxK2 := by decide
@[simp] theorem mx_mxNn_ne_mxK3 : mxNn ≠ mxK3 := by decide
@[simp] theorem mx_mxNn_ne_mxB1 : mxNn ≠ mxB1 := by decide
@[simp] theorem mx_mxNn_ne_mxB2 : mxNn ≠ mxB2 := by decide
@[simp] theorem mx_mxNn_ne_mxQ : mxNn ≠ mxQ := by decide
@[simp] theorem mx_mxNn_ne_mxN : mxNn ≠ mxN := by decide
@[simp] theorem mx_mxNn_ne_mxO : mxNn ≠ mxO := by decide
@[simp] theorem mx_mxNn_ne_lKb : mxNn ≠ lKb := by decide
@[simp] theorem mx_lKb_ne_mxNn : lKb ≠ mxNn := by decide
@[simp] theorem mx_mxNn_ne_lFl : mxNn ≠ lFl := by decide
@[simp] theorem mx_lFl_ne_mxNn : lFl ≠ mxNn := by decide
@[simp] theorem mx_mxNn_ne_lDh : mxNn ≠ lDh := by decide
@[simp] theorem mx_lDh_ne_mxNn : lDh ≠ mxNn := by decide
@[simp] theorem mx_mxNn_ne_lDt : mxNn ≠ lDt := by decide
@[simp] theorem mx_lDt_ne_mxNn : lDt ≠ mxNn := by decide
@[simp] theorem mx_mxNn_ne_lDg : mxNn ≠ lDg := by decide
@[simp] theorem mx_lDg_ne_mxNn : lDg ≠ mxNn := by decide
@[simp] theorem mx_mxNn_ne_lDi : mxNn ≠ lDi := by decide
@[simp] theorem mx_lDi_ne_mxNn : lDi ≠ mxNn := by decide
@[simp] theorem mx_mxNn_ne_lDo1 : mxNn ≠ lDo1 := by decide
@[simp] theorem mx_lDo1_ne_mxNn : lDo1 ≠ mxNn := by decide
@[simp] theorem mx_mxNn_ne_lDo2 : mxNn ≠ lDo2 := by decide
@[simp] theorem mx_lDo2_ne_mxNn : lDo2 ≠ mxNn := by decide
@[simp] theorem mx_mxNn_ne_lRp : mxNn ≠ lRp := by decide
@[simp] theorem mx_lRp_ne_mxNn : lRp ≠ mxNn := by decide
@[simp] theorem mx_mxNn_ne_lRn : mxNn ≠ lRn := by decide
@[simp] theorem mx_lRn_ne_mxNn : lRn ≠ mxNn := by decide
@[simp] theorem mx_mxNn_ne_lFle : mxNn ≠ lFle := by decide
@[simp] theorem mx_lFle_ne_mxNn : lFle ≠ mxNn := by decide
@[simp] theorem mx_mxNn_ne_lDir : mxNn ≠ lDir := by decide
@[simp] theorem mx_lDir_ne_mxNn : lDir ≠ mxNn := by decide
@[simp] theorem mx_mxH_ne_mxF : mxH ≠ mxF := by decide
@[simp] theorem mx_mxH_ne_mxNs : mxH ≠ mxNs := by decide
@[simp] theorem mx_mxH_ne_mxNn : mxH ≠ mxNn := by decide
@[simp] theorem mx_mxH_ne_mxM : mxH ≠ mxM := by decide
@[simp] theorem mx_mxH_ne_mxL : mxH ≠ mxL := by decide
@[simp] theorem mx_mxH_ne_mxC1 : mxH ≠ mxC1 := by decide
@[simp] theorem mx_mxH_ne_mxC2 : mxH ≠ mxC2 := by decide
@[simp] theorem mx_mxH_ne_mxC3 : mxH ≠ mxC3 := by decide
@[simp] theorem mx_mxH_ne_mxS : mxH ≠ mxS := by decide
@[simp] theorem mx_mxH_ne_mxR : mxH ≠ mxR := by decide
@[simp] theorem mx_mxH_ne_mxM2 : mxH ≠ mxM2 := by decide
@[simp] theorem mx_mxH_ne_mxK1 : mxH ≠ mxK1 := by decide
@[simp] theorem mx_mxH_ne_mxK2 : mxH ≠ mxK2 := by decide
@[simp] theorem mx_mxH_ne_mxK3 : mxH ≠ mxK3 := by decide
@[simp] theorem mx_mxH_ne_mxB1 : mxH ≠ mxB1 := by decide
@[simp] theorem mx_mxH_ne_mxB2 : mxH ≠ mxB2 := by decide
@[simp] theorem mx_mxH_ne_mxQ : mxH ≠ mxQ := by decide
@[simp] theorem mx_mxH_ne_mxN : mxH ≠ mxN := by decide
@[simp] theorem mx_mxH_ne_mxO : mxH ≠ mxO := by decide
@[simp] theorem mx_mxH_ne_lKb : mxH ≠ lKb := by decide
@[simp] theorem mx_lKb_ne_mxH : lKb ≠ mxH := by decide
@[simp] theorem mx_mxH_ne_lFl : mxH ≠ lFl := by decide
@[simp] theorem mx_lFl_ne_mxH : lFl ≠ mxH := by decide
@[simp] theorem mx_mxH_ne_lDh : mxH ≠ lDh := by decide
@[simp] theorem mx_lDh_ne_mxH : lDh ≠ mxH := by decide
@[simp] theorem mx_mxH_ne_lDt : mxH ≠ lDt := by decide
@[simp] theorem mx_lDt_ne_mxH : lDt ≠ mxH := by decide
@[simp] theorem mx_mxH_ne_lDg : mxH ≠ lDg := by decide
@[simp] theorem mx_lDg_ne_mxH : lDg ≠ mxH := by decide
@[simp] theorem mx_mxH_ne_lDi : mxH ≠ lDi := by decide
@[simp] theorem mx_lDi_ne_mxH : lDi ≠ mxH := by decide
@[simp] theorem mx_mxH_ne_lDo1 : mxH ≠ lDo1 := by decide
@[simp] theorem mx_lDo1_ne_mxH : lDo1 ≠ mxH := by decide
@[simp] theorem mx_mxH_ne_lDo2 : mxH ≠ lDo2 := by decide
@[simp] theorem mx_lDo2_ne_mxH : lDo2 ≠ mxH := by decide
@[simp] theorem mx_mxH_ne_lRp : mxH ≠ lRp := by decide
@[simp] theorem mx_lRp_ne_mxH : lRp ≠ mxH := by decide
@[simp] theorem mx_mxH_ne_lRn : mxH ≠ lRn := by decide
@[simp] theorem mx_lRn_ne_mxH : lRn ≠ mxH := by decide
@[simp] theorem mx_mxH_ne_lFle : mxH ≠ lFle := by decide
@[simp] theorem mx_lFle_ne_mxH : lFle ≠ mxH := by decide
@[simp] theorem mx_mxH_ne_lDir : mxH ≠ lDir := by decide
@[simp] theorem mx_lDir_ne_mxH : lDir ≠ mxH := by decide
@[simp] theorem mx_mxM_ne_mxF : mxM ≠ mxF := by decide
@[simp] theorem mx_mxM_ne_mxNs : mxM ≠ mxNs := by decide
@[simp] theorem mx_mxM_ne_mxNn : mxM ≠ mxNn := by decide
@[simp] theorem mx_mxM_ne_mxH : mxM ≠ mxH := by decide
@[simp] theorem mx_mxM_ne_mxL : mxM ≠ mxL := by decide
@[simp] theorem mx_mxM_ne_mxC1 : mxM ≠ mxC1 := by decide
@[simp] theorem mx_mxM_ne_mxC2 : mxM ≠ mxC2 := by decide
@[simp] theorem mx_mxM_ne_mxC3 : mxM ≠ mxC3 := by decide
@[simp] theorem mx_mxM_ne_mxS : mxM ≠ mxS := by decide
@[simp] theorem mx_mxM_ne_mxR : mxM ≠ mxR := by decide
@[simp] theorem mx_mxM_ne_mxM2 : mxM ≠ mxM2 := by decide
@[simp] theorem mx_mxM_ne_mxK1 : mxM ≠ mxK1 := by decide
@[simp] theorem mx_mxM_ne_mxK2 : mxM ≠ mxK2 := by decide
@[simp] theorem mx_mxM_ne_mxK3 : mxM ≠ mxK3 := by decide
@[simp] theorem mx_mxM_ne_mxB1 : mxM ≠ mxB1 := by decide
@[simp] theorem mx_mxM_ne_mxB2 : mxM ≠ mxB2 := by decide
@[simp] theorem mx_mxM_ne_mxQ : mxM ≠ mxQ := by decide
@[simp] theorem mx_mxM_ne_mxN : mxM ≠ mxN := by decide
@[simp] theorem mx_mxM_ne_mxO : mxM ≠ mxO := by decide
@[simp] theorem mx_mxM_ne_lKb : mxM ≠ lKb := by decide
@[simp] theorem mx_lKb_ne_mxM : lKb ≠ mxM := by decide
@[simp] theorem mx_mxM_ne_lFl : mxM ≠ lFl := by decide
@[simp] theorem mx_lFl_ne_mxM : lFl ≠ mxM := by decide
@[simp] theorem mx_mxM_ne_lDh : mxM ≠ lDh := by decide
@[simp] theorem mx_lDh_ne_mxM : lDh ≠ mxM := by decide
@[simp] theorem mx_mxM_ne_lDt : mxM ≠ lDt := by decide
@[simp] theorem mx_lDt_ne_mxM : lDt ≠ mxM := by decide
@[simp] theorem mx_mxM_ne_lDg : mxM ≠ lDg := by decide
@[simp] theorem mx_lDg_ne_mxM : lDg ≠ mxM := by decide
@[simp] theorem mx_mxM_ne_lDi : mxM ≠ lDi := by decide
@[simp] theorem mx_lDi_ne_mxM : lDi ≠ mxM := by decide
@[simp] theorem mx_mxM_ne_lDo1 : mxM ≠ lDo1 := by decide
@[simp] theorem mx_lDo1_ne_mxM : lDo1 ≠ mxM := by decide
@[simp] theorem mx_mxM_ne_lDo2 : mxM ≠ lDo2 := by decide
@[simp] theorem mx_lDo2_ne_mxM : lDo2 ≠ mxM := by decide
@[simp] theorem mx_mxM_ne_lRp : mxM ≠ lRp := by decide
@[simp] theorem mx_lRp_ne_mxM : lRp ≠ mxM := by decide
@[simp] theorem mx_mxM_ne_lRn : mxM ≠ lRn := by decide
@[simp] theorem mx_lRn_ne_mxM : lRn ≠ mxM := by decide
@[simp] theorem mx_mxM_ne_lFle : mxM ≠ lFle := by decide
@[simp] theorem mx_lFle_ne_mxM : lFle ≠ mxM := by decide
@[simp] theorem mx_mxM_ne_lDir : mxM ≠ lDir := by decide
@[simp] theorem mx_lDir_ne_mxM : lDir ≠ mxM := by decide
@[simp] theorem mx_mxL_ne_mxF : mxL ≠ mxF := by decide
@[simp] theorem mx_mxL_ne_mxNs : mxL ≠ mxNs := by decide
@[simp] theorem mx_mxL_ne_mxNn : mxL ≠ mxNn := by decide
@[simp] theorem mx_mxL_ne_mxH : mxL ≠ mxH := by decide
@[simp] theorem mx_mxL_ne_mxM : mxL ≠ mxM := by decide
@[simp] theorem mx_mxL_ne_mxC1 : mxL ≠ mxC1 := by decide
@[simp] theorem mx_mxL_ne_mxC2 : mxL ≠ mxC2 := by decide
@[simp] theorem mx_mxL_ne_mxC3 : mxL ≠ mxC3 := by decide
@[simp] theorem mx_mxL_ne_mxS : mxL ≠ mxS := by decide
@[simp] theorem mx_mxL_ne_mxR : mxL ≠ mxR := by decide
@[simp] theorem mx_mxL_ne_mxM2 : mxL ≠ mxM2 := by decide
@[simp] theorem mx_mxL_ne_mxK1 : mxL ≠ mxK1 := by decide
@[simp] theorem mx_mxL_ne_mxK2 : mxL ≠ mxK2 := by decide
@[simp] theorem mx_mxL_ne_mxK3 : mxL ≠ mxK3 := by decide
@[simp] theorem mx_mxL_ne_mxB1 : mxL ≠ mxB1 := by decide
@[simp] theorem mx_mxL_ne_mxB2 : mxL ≠ mxB2 := by decide
@[simp] theorem mx_mxL_ne_mxQ : mxL ≠ mxQ := by decide
@[simp] theorem mx_mxL_ne_mxN : mxL ≠ mxN := by decide
@[simp] theorem mx_mxL_ne_mxO : mxL ≠ mxO := by decide
@[simp] theorem mx_mxL_ne_lKb : mxL ≠ lKb := by decide
@[simp] theorem mx_lKb_ne_mxL : lKb ≠ mxL := by decide
@[simp] theorem mx_mxL_ne_lFl : mxL ≠ lFl := by decide
@[simp] theorem mx_lFl_ne_mxL : lFl ≠ mxL := by decide
@[simp] theorem mx_mxL_ne_lDh : mxL ≠ lDh := by decide
@[simp] theorem mx_lDh_ne_mxL : lDh ≠ mxL := by decide
@[simp] theorem mx_mxL_ne_lDt : mxL ≠ lDt := by decide
@[simp] theorem mx_lDt_ne_mxL : lDt ≠ mxL := by decide
@[simp] theorem mx_mxL_ne_lDg : mxL ≠ lDg := by decide
@[simp] theorem mx_lDg_ne_mxL : lDg ≠ mxL := by decide
@[simp] theorem mx_mxL_ne_lDi : mxL ≠ lDi := by decide
@[simp] theorem mx_lDi_ne_mxL : lDi ≠ mxL := by decide
@[simp] theorem mx_mxL_ne_lDo1 : mxL ≠ lDo1 := by decide
@[simp] theorem mx_lDo1_ne_mxL : lDo1 ≠ mxL := by decide
@[simp] theorem mx_mxL_ne_lDo2 : mxL ≠ lDo2 := by decide
@[simp] theorem mx_lDo2_ne_mxL : lDo2 ≠ mxL := by decide
@[simp] theorem mx_mxL_ne_lRp : mxL ≠ lRp := by decide
@[simp] theorem mx_lRp_ne_mxL : lRp ≠ mxL := by decide
@[simp] theorem mx_mxL_ne_lRn : mxL ≠ lRn := by decide
@[simp] theorem mx_lRn_ne_mxL : lRn ≠ mxL := by decide
@[simp] theorem mx_mxL_ne_lFle : mxL ≠ lFle := by decide
@[simp] theorem mx_lFle_ne_mxL : lFle ≠ mxL := by decide
@[simp] theorem mx_mxL_ne_lDir : mxL ≠ lDir := by decide
@[simp] theorem mx_lDir_ne_mxL : lDir ≠ mxL := by decide
@[simp] theorem mx_mxC1_ne_mxF : mxC1 ≠ mxF := by decide
@[simp] theorem mx_mxC1_ne_mxNs : mxC1 ≠ mxNs := by decide
@[simp] theorem mx_mxC1_ne_mxNn : mxC1 ≠ mxNn := by decide
@[simp] theorem mx_mxC1_ne_mxH : mxC1 ≠ mxH := by decide
@[simp] theorem mx_mxC1_ne_mxM : mxC1 ≠ mxM := by decide
@[simp] theorem mx_mxC1_ne_mxL : mxC1 ≠ mxL := by decide
@[simp] theorem mx_mxC1_ne_mxC2 : mxC1 ≠ mxC2 := by decide
@[simp] theorem mx_mxC1_ne_mxC3 : mxC1 ≠ mxC3 := by decide
@[simp] theorem mx_mxC1_ne_mxS : mxC1 ≠ mxS := by decide
@[simp] theorem mx_mxC1_ne_mxR : mxC1 ≠ mxR := by decide
@[simp] theorem mx_mxC1_ne_mxM2 : mxC1 ≠ mxM2 := by decide
@[simp] theorem mx_mxC1_ne_mxK1 : mxC1 ≠ mxK1 := by decide
@[simp] theorem mx_mxC1_ne_mxK2 : mxC1 ≠ mxK2 := by decide
@[simp] theorem mx_mxC1_ne_mxK3 : mxC1 ≠ mxK3 := by decide
@[simp] theorem mx_mxC1_ne_mxB1 : mxC1 ≠ mxB1 := by decide
@[simp] theorem mx_mxC1_ne_mxB2 : mxC1 ≠ mxB2 := by decide
@[simp] theorem mx_mxC1_ne_mxQ : mxC1 ≠ mxQ := by decide
@[simp] theorem mx_mxC1_ne_mxN : mxC1 ≠ mxN := by decide
@[simp] theorem mx_mxC1_ne_mxO : mxC1 ≠ mxO := by decide
@[simp] theorem mx_mxC1_ne_lKb : mxC1 ≠ lKb := by decide
@[simp] theorem mx_lKb_ne_mxC1 : lKb ≠ mxC1 := by decide
@[simp] theorem mx_mxC1_ne_lFl : mxC1 ≠ lFl := by decide
@[simp] theorem mx_lFl_ne_mxC1 : lFl ≠ mxC1 := by decide
@[simp] theorem mx_mxC1_ne_lDh : mxC1 ≠ lDh := by decide
@[simp] theorem mx_lDh_ne_mxC1 : lDh ≠ mxC1 := by decide
@[simp] theorem mx_mxC1_ne_lDt : mxC1 ≠ lDt := by decide
@[simp] theorem mx_lDt_ne_mxC1 : lDt ≠ mxC1 := by decide
@[simp] theorem mx_mxC1_ne_lDg : mxC1 ≠ lDg := by decide
@[simp] theorem mx_lDg_ne_mxC1 : lDg ≠ mxC1 := by decide
@[simp] theorem mx_mxC1_ne_lDi : mxC1 ≠ lDi := by decide
@[simp] theorem mx_lDi_ne_mxC1 : lDi ≠ mxC1 := by decide
@[simp] theorem mx_mxC1_ne_lDo1 : mxC1 ≠ lDo1 := by decide
@[simp] theorem mx_lDo1_ne_mxC1 : lDo1 ≠ mxC1 := by decide
@[simp] theorem mx_mxC1_ne_lDo2 : mxC1 ≠ lDo2 := by decide
@[simp] theorem mx_lDo2_ne_mxC1 : lDo2 ≠ mxC1 := by decide
@[simp] theorem mx_mxC1_ne_lRp : mxC1 ≠ lRp := by decide
@[simp] theorem mx_lRp_ne_mxC1 : lRp ≠ mxC1 := by decide
@[simp] theorem mx_mxC1_ne_lRn : mxC1 ≠ lRn := by decide
@[simp] theorem mx_lRn_ne_mxC1 : lRn ≠ mxC1 := by decide
@[simp] theorem mx_mxC1_ne_lFle : mxC1 ≠ lFle := by decide
@[simp] theorem mx_lFle_ne_mxC1 : lFle ≠ mxC1 := by decide
@[simp] theorem mx_mxC1_ne_lDir : mxC1 ≠ lDir := by decide
@[simp] theorem mx_lDir_ne_mxC1 : lDir ≠ mxC1 := by decide
@[simp] theorem mx_mxC2_ne_mxF : mxC2 ≠ mxF := by decide
@[simp] theorem mx_mxC2_ne_mxNs : mxC2 ≠ mxNs := by decide
@[simp] theorem mx_mxC2_ne_mxNn : mxC2 ≠ mxNn := by decide
@[simp] theorem mx_mxC2_ne_mxH : mxC2 ≠ mxH := by decide
@[simp] theorem mx_mxC2_ne_mxM : mxC2 ≠ mxM := by decide
@[simp] theorem mx_mxC2_ne_mxL : mxC2 ≠ mxL := by decide
@[simp] theorem mx_mxC2_ne_mxC1 : mxC2 ≠ mxC1 := by decide
@[simp] theorem mx_mxC2_ne_mxC3 : mxC2 ≠ mxC3 := by decide
@[simp] theorem mx_mxC2_ne_mxS : mxC2 ≠ mxS := by decide
@[simp] theorem mx_mxC2_ne_mxR : mxC2 ≠ mxR := by decide
@[simp] theorem mx_mxC2_ne_mxM2 : mxC2 ≠ mxM2 := by decide
@[simp] theorem mx_mxC2_ne_mxK1 : mxC2 ≠ mxK1 := by decide
@[simp] theorem mx_mxC2_ne_mxK2 : mxC2 ≠ mxK2 := by decide
@[simp] theorem mx_mxC2_ne_mxK3 : mxC2 ≠ mxK3 := by decide
@[simp] theorem mx_mxC2_ne_mxB1 : mxC2 ≠ mxB1 := by decide
@[simp] theorem mx_mxC2_ne_mxB2 : mxC2 ≠ mxB2 := by decide
@[simp] theorem mx_mxC2_ne_mxQ : mxC2 ≠ mxQ := by decide
@[simp] theorem mx_mxC2_ne_mxN : mxC2 ≠ mxN := by decide
@[simp] theorem mx_mxC2_ne_mxO : mxC2 ≠ mxO := by decide
@[simp] theorem mx_mxC2_ne_lKb : mxC2 ≠ lKb := by decide
@[simp] theorem mx_lKb_ne_mxC2 : lKb ≠ mxC2 := by decide
@[simp] theorem mx_mxC2_ne_lFl : mxC2 ≠ lFl := by decide
@[simp] theorem mx_lFl_ne_mxC2 : lFl ≠ mxC2 := by decide
@[simp] theorem mx_mxC2_ne_lDh : mxC2 ≠ lDh := by decide
@[simp] theorem mx_lDh_ne_mxC2 : lDh ≠ mxC2 := by decide
@[simp] theorem mx_mxC2_ne_lDt : mxC2 ≠ lDt := by decide
@[simp] theorem mx_lDt_ne_mxC2 : lDt ≠ mxC2 := by decide
@[simp] theorem mx_mxC2_ne_lDg : mxC2 ≠ lDg := by decide
@[simp] theorem mx_lDg_ne_mxC2 : lDg ≠ mxC2 := by decide
@[simp] theorem mx_mxC2_ne_lDi : mxC2 ≠ lDi := by decide
@[simp] theorem mx_lDi_ne_mxC2 : lDi ≠ mxC2 := by decide
@[simp] theorem mx_mxC2_ne_lDo1 : mxC2 ≠ lDo1 := by decide
@[simp] theorem mx_lDo1_ne_mxC2 : lDo1 ≠ mxC2 := by decide
@[simp] theorem mx_mxC2_ne_lDo2 : mxC2 ≠ lDo2 := by decide
@[simp] theorem mx_lDo2_ne_mxC2 : lDo2 ≠ mxC2 := by decide
@[simp] theorem mx_mxC2_ne_lRp : mxC2 ≠ lRp := by decide
@[simp] theorem mx_lRp_ne_mxC2 : lRp ≠ mxC2 := by decide
@[simp] theorem mx_mxC2_ne_lRn : mxC2 ≠ lRn := by decide
@[simp] theorem mx_lRn_ne_mxC2 : lRn ≠ mxC2 := by decide
@[simp] theorem mx_mxC2_ne_lFle : mxC2 ≠ lFle := by decide
@[simp] theorem mx_lFle_ne_mxC2 : lFle ≠ mxC2 := by decide
@[simp] theorem mx_mxC2_ne_lDir : mxC2 ≠ lDir := by decide
@[simp] theorem mx_lDir_ne_mxC2 : lDir ≠ mxC2 := by decide
@[simp] theorem mx_mxC3_ne_mxF : mxC3 ≠ mxF := by decide
@[simp] theorem mx_mxC3_ne_mxNs : mxC3 ≠ mxNs := by decide
@[simp] theorem mx_mxC3_ne_mxNn : mxC3 ≠ mxNn := by decide
@[simp] theorem mx_mxC3_ne_mxH : mxC3 ≠ mxH := by decide
@[simp] theorem mx_mxC3_ne_mxM : mxC3 ≠ mxM := by decide
@[simp] theorem mx_mxC3_ne_mxL : mxC3 ≠ mxL := by decide
@[simp] theorem mx_mxC3_ne_mxC1 : mxC3 ≠ mxC1 := by decide
@[simp] theorem mx_mxC3_ne_mxC2 : mxC3 ≠ mxC2 := by decide
@[simp] theorem mx_mxC3_ne_mxS : mxC3 ≠ mxS := by decide
@[simp] theorem mx_mxC3_ne_mxR : mxC3 ≠ mxR := by decide
@[simp] theorem mx_mxC3_ne_mxM2 : mxC3 ≠ mxM2 := by decide
@[simp] theorem mx_mxC3_ne_mxK1 : mxC3 ≠ mxK1 := by decide
@[simp] theorem mx_mxC3_ne_mxK2 : mxC3 ≠ mxK2 := by decide
@[simp] theorem mx_mxC3_ne_mxK3 : mxC3 ≠ mxK3 := by decide
@[simp] theorem mx_mxC3_ne_mxB1 : mxC3 ≠ mxB1 := by decide
@[simp] theorem mx_mxC3_ne_mxB2 : mxC3 ≠ mxB2 := by decide
@[simp] theorem mx_mxC3_ne_mxQ : mxC3 ≠ mxQ := by decide
@[simp] theorem mx_mxC3_ne_mxN : mxC3 ≠ mxN := by decide
@[simp] theorem mx_mxC3_ne_mxO : mxC3 ≠ mxO := by decide
@[simp] theorem mx_mxC3_ne_lKb : mxC3 ≠ lKb := by decide
@[simp] theorem mx_lKb_ne_mxC3 : lKb ≠ mxC3 := by decide
@[simp] theorem mx_mxC3_ne_lFl : mxC3 ≠ lFl := by decide
@[simp] theorem mx_lFl_ne_mxC3 : lFl ≠ mxC3 := by decide
@[simp] theorem mx_mxC3_ne_lDh : mxC3 ≠ lDh := by decide
@[simp] theorem mx_lDh_ne_mxC3 : lDh ≠ mxC3 := by decide
@[simp] theorem mx_mxC3_ne_lDt : mxC3 ≠ lDt := by decide
@[simp] theorem mx_lDt_ne_mxC3 : lDt ≠ mxC3 := by decide
@[simp] theorem mx_mxC3_ne_lDg : mxC3 ≠ lDg := by decide
@[simp] theorem mx_lDg_ne_mxC3 : lDg ≠ mxC3 := by decide
@[simp] theorem mx_mxC3_ne_lDi : mxC3 ≠ lDi := by decide
@[simp] theorem mx_lDi_ne_mxC3 : lDi ≠ mxC3 := by decide
@[simp] theorem mx_mxC3_ne_lDo1 : mxC3 ≠ lDo1 := by decide
@[simp] theorem mx_lDo1_ne_mxC3 : lDo1 ≠ mxC3 := by decide
@[simp] theorem mx_mxC3_ne_lDo2 : mxC3 ≠ lDo2 := by decide
@[simp] theorem mx_lDo2_ne_mxC3 : lDo2 ≠ mxC3 := by decide
@[simp] theorem mx_mxC3_ne_lRp : mxC3 ≠ lRp := by decide
@[simp] theorem mx_lRp_ne_mxC3 : lRp ≠ mxC3 := by decide
@[simp] theorem mx_mxC3_ne_lRn : mxC3 ≠ lRn := by decide
@[simp] theorem mx_lRn_ne_mxC3 : lRn ≠ mxC3 := by decide
@[simp] theorem mx_mxC3_ne_lFle : mxC3 ≠ lFle := by decide
@[simp] theorem mx_lFle_ne_mxC3 : lFle ≠ mxC3 := by decide
@[simp] theorem mx_mxC3_ne_lDir : mxC3 ≠ lDir := by decide
@[simp] theorem mx_lDir_ne_mxC3 : lDir ≠ mxC3 := by decide
@[simp] theorem mx_mxS_ne_mxF : mxS ≠ mxF := by decide
@[simp] theorem mx_mxS_ne_mxNs : mxS ≠ mxNs := by decide
@[simp] theorem mx_mxS_ne_mxNn : mxS ≠ mxNn := by decide
@[simp] theorem mx_mxS_ne_mxH : mxS ≠ mxH := by decide
@[simp] theorem mx_mxS_ne_mxM : mxS ≠ mxM := by decide
@[simp] theorem mx_mxS_ne_mxL : mxS ≠ mxL := by decide
@[simp] theorem mx_mxS_ne_mxC1 : mxS ≠ mxC1 := by decide
@[simp] theorem mx_mxS_ne_mxC2 : mxS ≠ mxC2 := by decide
@[simp] theorem mx_mxS_ne_mxC3 : mxS ≠ mxC3 := by decide
@[simp] theorem mx_mxS_ne_mxR : mxS ≠ mxR := by decide
@[simp] theorem mx_mxS_ne_mxM2 : mxS ≠ mxM2 := by decide
@[simp] theorem mx_mxS_ne_mxK1 : mxS ≠ mxK1 := by decide
@[simp] theorem mx_mxS_ne_mxK2 : mxS ≠ mxK2 := by decide
@[simp] theorem mx_mxS_ne_mxK3 : mxS ≠ mxK3 := by decide
@[simp] theorem mx_mxS_ne_mxB1 : mxS ≠ mxB1 := by decide
@[simp] theorem mx_mxS_ne_mxB2 : mxS ≠ mxB2 := by decide
@[simp] theorem mx_mxS_ne_mxQ : mxS ≠ mxQ := by decide
@[simp] theorem mx_mxS_ne_mxN : mxS ≠ mxN := by decide
@[simp] theorem mx_mxS_ne_mxO : mxS ≠ mxO := by decide
@[simp] theorem mx_mxS_ne_lKb : mxS ≠ lKb := by decide
@[simp] theorem mx_lKb_ne_mxS : lKb ≠ mxS := by decide
@[simp] theorem mx_mxS_ne_lFl : mxS ≠ lFl := by decide
@[simp] theorem mx_lFl_ne_mxS : lFl ≠ mxS := by decide
@[simp] theorem mx_mxS_ne_lDh : mxS ≠ lDh := by decide
@[simp] theorem mx_lDh_ne_mxS : lDh ≠ mxS := by decide
@[simp] theorem mx_mxS_ne_lDt : mxS ≠ lDt := by decide
@[simp] theorem mx_lDt_ne_mxS : lDt ≠ mxS := by decide
@[simp] theorem mx_mxS_ne_lDg : mxS ≠ lDg := by decide
@[simp] theorem mx_lDg_ne_mxS : lDg ≠ mxS := by decide
@[simp] theorem mx_mxS_ne_lDi : mxS ≠ lDi := by decide
@[simp] theorem mx_lDi_ne_mxS : lDi ≠ mxS := by decide
@[simp] theorem mx_mxS_ne_lDo1 : mxS ≠ lDo1 := by decide
@[simp] theorem mx_lDo1_ne_mxS : lDo1 ≠ mxS := by decide
@[simp] theorem mx_mxS_ne_lDo2 : mxS ≠ lDo2 := by decide
@[simp] theorem mx_lDo2_ne_mxS : lDo2 ≠ mxS := by decide
@[simp] theorem mx_mxS_ne_lRp : mxS ≠ lRp := by decide
@[simp] theorem mx_lRp_ne_mxS : lRp ≠ mxS := by decide
@[simp] theorem mx_mxS_ne_lRn : mxS ≠ lRn := by decide
@[simp] theorem mx_lRn_ne_mxS : lRn ≠ mxS := by decide
@[simp] theorem mx_mxS_ne_lFle : mxS ≠ lFle := by decide
@[simp] theorem mx_lFle_ne_mxS : lFle ≠ mxS := by decide
@[simp] theorem mx_mxS_ne_lDir : mxS ≠ lDir := by decide
@[simp] theorem mx_lDir_ne_mxS : lDir ≠ mxS := by decide
@[simp] theorem mx_mxR_ne_mxF : mxR ≠ mxF := by decide
@[simp] theorem mx_mxR_ne_mxNs : mxR ≠ mxNs := by decide
@[simp] theorem mx_mxR_ne_mxNn : mxR ≠ mxNn := by decide
@[simp] theorem mx_mxR_ne_mxH : mxR ≠ mxH := by decide
@[simp] theorem mx_mxR_ne_mxM : mxR ≠ mxM := by decide
@[simp] theorem mx_mxR_ne_mxL : mxR ≠ mxL := by decide
@[simp] theorem mx_mxR_ne_mxC1 : mxR ≠ mxC1 := by decide
@[simp] theorem mx_mxR_ne_mxC2 : mxR ≠ mxC2 := by decide
@[simp] theorem mx_mxR_ne_mxC3 : mxR ≠ mxC3 := by decide
@[simp] theorem mx_mxR_ne_mxS : mxR ≠ mxS := by decide
@[simp] theorem mx_mxR_ne_mxM2 : mxR ≠ mxM2 := by decide
@[simp] theorem mx_mxR_ne_mxK1 : mxR ≠ mxK1 := by decide
@[simp] theorem mx_mxR_ne_mxK2 : mxR ≠ mxK2 := by decide
@[simp] theorem mx_mxR_ne_mxK3 : mxR ≠ mxK3 := by decide
@[simp] theorem mx_mxR_ne_mxB1 : mxR ≠ mxB1 := by decide
@[simp] theorem mx_mxR_ne_mxB2 : mxR ≠ mxB2 := by decide
@[simp] theorem mx_mxR_ne_mxQ : mxR ≠ mxQ := by decide
@[simp] theorem mx_mxR_ne_mxN : mxR ≠ mxN := by decide
@[simp] theorem mx_mxR_ne_mxO : mxR ≠ mxO := by decide
@[simp] theorem mx_mxR_ne_lKb : mxR ≠ lKb := by decide
@[simp] theorem mx_lKb_ne_mxR : lKb ≠ mxR := by decide
@[simp] theorem mx_mxR_ne_lFl : mxR ≠ lFl := by decide
@[simp] theorem mx_lFl_ne_mxR : lFl ≠ mxR := by decide
@[simp] theorem mx_mxR_ne_lDh : mxR ≠ lDh := by decide
@[simp] theorem mx_lDh_ne_mxR : lDh ≠ mxR := by decide
@[simp] theorem mx_mxR_ne_lDt : mxR ≠ lDt := by decide
@[simp] theorem mx_lDt_ne_mxR : lDt ≠ mxR := by decide
@[simp] theorem mx_mxR_ne_lDg : mxR ≠ lDg := by decide
@[simp] theorem mx_lDg_ne_mxR : lDg ≠ mxR := by decide
@[simp] theorem mx_mxR_ne_lDi : mxR ≠ lDi := by decide
@[simp] theorem mx_lDi_ne_mxR : lDi ≠ mxR := by decide
@[simp] theorem mx_mxR_ne_lDo1 : mxR ≠ lDo1 := by decide
@[simp] theorem mx_lDo1_ne_mxR : lDo1 ≠ mxR := by decide
@[simp] theorem mx_mxR_ne_lDo2 : mxR ≠ lDo2 := by decide
@[simp] theorem mx_lDo2_ne_mxR : lDo2 ≠ mxR := by decide
@[simp] theorem mx_mxR_ne_lRp : mxR ≠ lRp := by decide
@[simp] theorem mx_lRp_ne_mxR : lRp ≠ mxR := by decide
@[simp] theorem mx_mxR_ne_lRn : mxR ≠ lRn := by decide
@[simp] theorem mx_lRn_ne_mxR : lRn ≠ mxR := by decide
@[simp] theorem mx_mxR_ne_lFle : mxR ≠ lFle := by decide
@[simp] theorem mx_lFle_ne_mxR : lFle ≠ mxR := by decide
@[simp] theorem mx_mxR_ne_lDir : mxR ≠ lDir := by decide
@[simp] theorem mx_lDir_ne_mxR : lDir ≠ mxR := by decide
@[simp] theorem mx_mxM2_ne_mxF : mxM2 ≠ mxF := by decide
@[simp] theorem mx_mxM2_ne_mxNs : mxM2 ≠ mxNs := by decide
@[simp] theorem mx_mxM2_ne_mxNn : mxM2 ≠ mxNn := by decide
@[simp] theorem mx_mxM2_ne_mxH : mxM2 ≠ mxH := by decide
@[simp] theorem mx_mxM2_ne_mxM : mxM2 ≠ mxM := by decide
@[simp] theorem mx_mxM2_ne_mxL : mxM2 ≠ mxL := by decide
@[simp] theorem mx_mxM2_ne_mxC1 : mxM2 ≠ mxC1 := by decide
@[simp] theorem mx_mxM2_ne_mxC2 : mxM2 ≠ mxC2 := by decide
@[simp] theorem mx_mxM2_ne_mxC3 : mxM2 ≠ mxC3 := by decide
@[simp] theorem mx_mxM2_ne_mxS : mxM2 ≠ mxS := by decide
@[simp] theorem mx_mxM2_ne_mxR : mxM2 ≠ mxR := by decide
@[simp] theorem mx_mxM2_ne_mxK1 : mxM2 ≠ mxK1 := by decide
@[simp] theorem mx_mxM2_ne_mxK2 : mxM2 ≠ mxK2 := by decide
@[simp] theorem mx_mxM2_ne_mxK3 : mxM2 ≠ mxK3 := by decide
@[simp] theorem mx_mxM2_ne_mxB1 : mxM2 ≠ mxB1 := by decide
@[simp] theorem mx_mxM2_ne_mxB2 : mxM2 ≠ mxB2 := by decide
@[simp] theorem mx_mxM2_ne_mxQ : mxM2 ≠ mxQ := by decide
@[simp] theorem mx_mxM2_ne_mxN : mxM2 ≠ mxN := by decide
@[simp] theorem mx_mxM2_ne_mxO : mxM2 ≠ mxO := by decide
@[simp] theorem mx_mxM2_ne_lKb : mxM2 ≠ lKb := by decide
@[simp] theorem mx_lKb_ne_mxM2 : lKb ≠ mxM2 := by decide
@[simp] theorem mx_mxM2_ne_lFl : mxM2 ≠ lFl := by decide
@[simp] theorem mx_lFl_ne_mxM2 : lFl ≠ mxM2 := by decide
@[simp] theorem mx_mxM2_ne_lDh : mxM2 ≠ lDh := by decide
@[simp] theorem mx_lDh_ne_mxM2 : lDh ≠ mxM2 := by decide
@[simp] theorem mx_mxM2_ne_lDt : mxM2 ≠ lDt := by decide
@[simp] theorem mx_lDt_ne_mxM2 : lDt ≠ mxM2 := by decide
@[simp] theorem mx_mxM2_ne_lDg : mxM2 ≠ lDg := by decide
@[simp] theorem mx_lDg_ne_mxM2 : lDg ≠ mxM2 := by decide
@[simp] theorem mx_mxM2_ne_lDi : mxM2 ≠ lDi := by decide
@[simp] theorem mx_lDi_ne_mxM2 : lDi ≠ mxM2 := by decide
@[simp] theorem mx_mxM2_ne_lDo1 : mxM2 ≠ lDo1 := by decide
@[simp] theorem mx_lDo1_ne_mxM2 : lDo1 ≠ mxM2 := by decide
@[simp] theorem mx_mxM2_ne_lDo2 : mxM2 ≠ lDo2 := by decide
@[simp] theorem mx_lDo2_ne_mxM2 : lDo2 ≠ mxM2 := by decide
@[simp] theorem mx_mxM2_ne_lRp : mxM2 ≠ lRp := by decide
@[simp] theorem mx_lRp_ne_mxM2 : lRp ≠ mxM2 := by decide
@[simp] theorem mx_mxM2_ne_lRn : mxM2 ≠ lRn := by decide
@[simp] theorem mx_lRn_ne_mxM2 : lRn ≠ mxM2 := by decide
@[simp] theorem mx_mxM2_ne_lFle : mxM2 ≠ lFle := by decide
@[simp] theorem mx_lFle_ne_mxM2 : lFle ≠ mxM2 := by decide
@[simp] theorem mx_mxM2_ne_lDir : mxM2 ≠ lDir := by decide
@[simp] theorem mx_lDir_ne_mxM2 : lDir ≠ mxM2 := by decide
@[simp] theorem mx_mxK1_ne_mxF : mxK1 ≠ mxF := by decide
@[simp] theorem mx_mxK1_ne_mxNs : mxK1 ≠ mxNs := by decide
@[simp] theorem mx_mxK1_ne_mxNn : mxK1 ≠ mxNn := by decide
@[simp] theorem mx_mxK1_ne_mxH : mxK1 ≠ mxH := by decide
@[simp] theorem mx_mxK1_ne_mxM : mxK1 ≠ mxM := by decide
@[simp] theorem mx_mxK1_ne_mxL : mxK1 ≠ mxL := by decide
@[simp] theorem mx_mxK1_ne_mxC1 : mxK1 ≠ mxC1 := by decide
@[simp] theorem mx_mxK1_ne_mxC2 : mxK1 ≠ mxC2 := by decide
@[simp] theorem mx_mxK1_ne_mxC3 : mxK1 ≠ mxC3 := by decide
@[simp] theorem mx_mxK1_ne_mxS : mxK1 ≠ mxS := by decide
@[simp] theorem mx_mxK1_ne_mxR : mxK1 ≠ mxR := by decide
@[simp] theorem mx_mxK1_ne_mxM2 : mxK1 ≠ mxM2 := by decide
@[simp] theorem mx_mxK1_ne_mxK2 : mxK1 ≠ mxK2 := by decide
@[simp] theorem mx_mxK1_ne_mxK3 : mxK1 ≠ mxK3 := by decide
@[simp] theorem mx_mxK1_ne_mxB1 : mxK1 ≠ mxB1 := by decide
@[simp] theorem mx_mxK1_ne_mxB2 : mxK1 ≠ mxB2 := by decide
@[simp] theorem mx_mxK1_ne_mxQ : mxK1 ≠ mxQ := by decide
@[simp] theorem mx_mxK1_ne_mxN : mxK1 ≠ mxN := by decide
@[simp] theorem mx_mxK1_ne_mxO : mxK1 ≠ mxO := by decide
@[simp] theorem mx_mxK1_ne_lKb : mxK1 ≠ lKb := by decide
@[simp] theorem mx_lKb_ne_mxK1 : lKb ≠ mxK1 := by decide
@[simp] theorem mx_mxK1_ne_lFl : mxK1 ≠ lFl := by decide
@[simp] theorem mx_lFl_ne_mxK1 : lFl ≠ mxK1 := by decide
@[simp] theorem mx_mxK1_ne_lDh : mxK1 ≠ lDh := by decide
@[simp] theorem mx_lDh_ne_mxK1 : lDh ≠ mxK1 := by decide
@[simp] theorem mx_mxK1_ne_lDt : mxK1 ≠ lDt := by decide
@[simp] theorem mx_lDt_ne_mxK1 : lDt ≠ mxK1 := by decide
@[simp] theorem mx_mxK1_ne_lDg : mxK1 ≠ lDg := by decide
@[simp] theorem mx_lDg_ne_mxK1 : lDg ≠ mxK1 := by decide
@[simp] theorem mx_mxK1_ne_lDi : mxK1 ≠ lDi := by decide
@[simp] theorem mx_lDi_ne_mxK1 : lDi ≠ mxK1 := by decide
@[simp] theorem mx_mxK1_ne_lDo1 : mxK1 ≠ lDo1 := by decide
@[simp] theorem mx_lDo1_ne_mxK1 : lDo1 ≠ mxK1 := by decide
@[simp] theorem mx_mxK1_ne_lDo2 : mxK1 ≠ lDo2 := by decide
@[simp] theorem mx_lDo2_ne_mxK1 : lDo2 ≠ mxK1 := by decide
@[simp] theorem mx_mxK1_ne_lRp : mxK1 ≠ lRp := by decide
@[simp] theorem mx_lRp_ne_mxK1 : lRp ≠ mxK1 := by decide
@[simp] theorem mx_mxK1_ne_lRn : mxK1 ≠ lRn := by decide
@[simp] theorem mx_lRn_ne_mxK1 : lRn ≠ mxK1 := by decide
@[simp] theorem mx_mxK1_ne_lFle : mxK1 ≠ lFle := by decide
@[simp] theorem mx_lFle_ne_mxK1 : lFle ≠ mxK1 := by decide
@[simp] theorem mx_mxK1_ne_lDir : mxK1 ≠ lDir := by decide
@[simp] theorem mx_lDir_ne_mxK1 : lDir ≠ mxK1 := by decide
@[simp] theorem mx_mxK2_ne_mxF : mxK2 ≠ mxF := by decide
@[simp] theorem mx_mxK2_ne_mxNs : mxK2 ≠ mxNs := by decide
@[simp] theorem mx_mxK2_ne_mxNn : mxK2 ≠ mxNn := by decide
@[simp] theorem mx_mxK2_ne_mxH : mxK2 ≠ mxH := by decide
@[simp] theorem mx_mxK2_ne_mxM : mxK2 ≠ mxM := by decide
@[simp] theorem mx_mxK2_ne_mxL : mxK2 ≠ mxL := by decide
@[simp] theorem mx_mxK2_ne_mxC1 : mxK2 ≠ mxC1 := by decide
@[simp] theorem mx_mxK2_ne_mxC2 : mxK2 ≠ mxC2 := by decide
@[simp] theorem mx_mxK2_ne_mxC3 : mxK2 ≠ mxC3 := by decide
@[simp] theorem mx_mxK2_ne_mxS : mxK2 ≠ mxS := by decide
@[simp] theorem mx_mxK2_ne_mxR : mxK2 ≠ mxR := by decide
@[simp] theorem mx_mxK2_ne_mxM2 : mxK2 ≠ mxM2 := by decide
@[simp] theorem mx_mxK2_ne_mxK1 : mxK2 ≠ mxK1 := by decide
@[simp] theorem mx_mxK2_ne_mxK3 : mxK2 ≠ mxK3 := by decide
@[simp] theorem mx_mxK2_ne_mxB1 : mxK2 ≠ mxB1 := by decide
@[simp] theorem mx_mxK2_ne_mxB2 : mxK2 ≠ mxB2 := by decide
@[simp] theorem mx_mxK2_ne_mxQ : mxK2 ≠ mxQ := by decide
@[simp] theorem mx_mxK2_ne_mxN : mxK2 ≠ mxN := by decide
@[simp] theorem mx_mxK2_ne_mxO : mxK2 ≠ mxO := by decide
@[simp] theorem mx_mxK2_ne_lKb : mxK2 ≠ lKb := by decide
@[simp] theorem mx_lKb_ne_mxK2 : lKb ≠ mxK2 := by decide
@[simp] theorem mx_mxK2_ne_lFl : mxK2 ≠ lFl := by decide
@[simp] theorem mx_lFl_ne_mxK2 : lFl ≠ mxK2 := by decide
@[simp] theorem mx_mxK2_ne_lDh : mxK2 ≠ lDh := by decide
@[simp] theorem mx_lDh_ne_mxK2 : lDh ≠ mxK2 := by decide
@[simp] theorem mx_mxK2_ne_lDt : mxK2 ≠ lDt := by decide
@[simp] theorem mx_lDt_ne_mxK2 : lDt ≠ mxK2 := by decide
@[simp] theorem mx_mxK2_ne_lDg : mxK2 ≠ lDg := by decide
@[simp] theorem mx_lDg_ne_mxK2 : lDg ≠ mxK2 := by decide
@[simp] theorem mx_mxK2_ne_lDi : mxK2 ≠ lDi := by decide
@[simp] theorem mx_lDi_ne_mxK2 : lDi ≠ mxK2 := by decide
@[simp] theorem mx_mxK2_ne_lDo1 : mxK2 ≠ lDo1 := by decide
@[simp] theorem mx_lDo1_ne_mxK2 : lDo1 ≠ mxK2 := by decide
@[simp] theorem mx_mxK2_ne_lDo2 : mxK2 ≠ lDo2 := by decide
@[simp] theorem mx_lDo2_ne_mxK2 : lDo2 ≠ mxK2 := by decide
@[simp] theorem mx_mxK2_ne_lRp : mxK2 ≠ lRp := by decide
@[simp] theorem mx_lRp_ne_mxK2 : lRp ≠ mxK2 := by decide
@[simp] theorem mx_mxK2_ne_lRn : mxK2 ≠ lRn := by decide
@[simp] theorem mx_lRn_ne_mxK2 : lRn ≠ mxK2 := by decide
@[simp] theorem mx_mxK2_ne_lFle : mxK2 ≠ lFle := by decide
@[simp] theorem mx_lFle_ne_mxK2 : lFle ≠ mxK2 := by decide
@[simp] theorem mx_mxK2_ne_lDir : mxK2 ≠ lDir := by decide
@[simp] theorem mx_lDir_ne_mxK2 : lDir ≠ mxK2 := by decide
@[simp] theorem mx_mxK3_ne_mxF : mxK3 ≠ mxF := by decide
@[simp] theorem mx_mxK3_ne_mxNs : mxK3 ≠ mxNs := by decide
@[simp] theorem mx_mxK3_ne_mxNn : mxK3 ≠ mxNn := by decide
@[simp] theorem mx_mxK3_ne_mxH : mxK3 ≠ mxH := by decide
@[simp] theorem mx_mxK3_ne_mxM : mxK3 ≠ mxM := by decide
@[simp] theorem mx_mxK3_ne_mxL : mxK3 ≠ mxL := by decide
@[simp] theorem mx_mxK3_ne_mxC1 : mxK3 ≠ mxC1 := by decide
@[simp] theorem mx_mxK3_ne_mxC2 : mxK3 ≠ mxC2 := by decide
@[simp] theorem mx_mxK3_ne_mxC3 : mxK3 ≠ mxC3 := by decide
@[simp] theorem mx_mxK3_ne_mxS : mxK3 ≠ mxS := by decide
@[simp] theorem mx_mxK3_ne_mxR : mxK3 ≠ mxR := by decide
@[simp] theorem mx_mxK3_ne_mxM2 : mxK3 ≠ mxM2 := by decide
@[simp] theorem mx_mxK3_ne_mxK1 : mxK3 ≠ mxK1 := by decide
@[simp] theorem mx_mxK3_ne_mxK2 : mxK3 ≠ mxK2 := by decide
@[simp] theorem mx_mxK3_ne_mxB1 : mxK3 ≠ mxB1 := by decide
@[simp] theorem mx_mxK3_ne_mxB2 : mxK3 ≠ mxB2 := by decide
@[simp] theorem mx_mxK3_ne_mxQ : mxK3 ≠ mxQ := by decide
@[simp] theorem mx_mxK3_ne_mxN : mxK3 ≠ mxN := by decide
@[simp] theorem mx_mxK3_ne_mxO : mxK3 ≠ mxO := by decide
@[simp] theorem mx_mxK3_ne_lKb : mxK3 ≠ lKb := by decide
@[simp] theorem mx_lKb_ne_mxK3 : lKb ≠ mxK3 := by decide
@[simp] theorem mx_mxK3_ne_lFl : mxK3 ≠ lFl := by decide
@[simp] theorem mx_lFl_ne_mxK3 : lFl ≠ mxK3 := by decide
@[simp] theorem mx_mxK3_ne_lDh : mxK3 ≠ lDh := by decide
@[simp] theorem mx_lDh_ne_mxK3 : lDh ≠ mxK3 := by decide
@[simp] theorem mx_mxK3_ne_lDt : mxK3 ≠ lDt := by decide
@[simp] theorem mx_lDt_ne_mxK3 : lDt ≠ mxK3 := by decide
@[simp] theorem mx_mxK3_ne_lDg : mxK3 ≠ lDg := by decide
@[simp] theorem mx_lDg_ne_mxK3 : lDg ≠ mxK3 := by decide
@[simp] theorem mx_mxK3_ne_lDi : mxK3 ≠ lDi := by decide
@[simp] theorem mx_lDi_ne_mxK3 : lDi ≠ mxK3 := by decide
@[simp] theorem mx_mxK3_ne_lDo1 : mxK3 ≠ lDo1 := by decide
@[simp] theorem mx_lDo1_ne_mxK3 : lDo1 ≠ mxK3 := by decide
@[simp] theorem mx_mxK3_ne_lDo2 : mxK3 ≠ lDo2 := by decide
@[simp] theorem mx_lDo2_ne_mxK3 : lDo2 ≠ mxK3 := by decide
@[simp] theorem mx_mxK3_ne_lRp : mxK3 ≠ lRp := by decide
@[simp] theorem mx_lRp_ne_mxK3 : lRp ≠ mxK3 := by decide
@[simp] theorem mx_mxK3_ne_lRn : mxK3 ≠ lRn := by decide
@[simp] theorem mx_lRn_ne_mxK3 : lRn ≠ mxK3 := by decide
@[simp] theorem mx_mxK3_ne_lFle : mxK3 ≠ lFle := by decide
@[simp] theorem mx_lFle_ne_mxK3 : lFle ≠ mxK3 := by decide
@[simp] theorem mx_mxK3_ne_lDir : mxK3 ≠ lDir := by decide
@[simp] theorem mx_lDir_ne_mxK3 : lDir ≠ mxK3 := by decide
@[simp] theorem mx_mxB1_ne_mxF : mxB1 ≠ mxF := by decide
@[simp] theorem mx_mxB1_ne_mxNs : mxB1 ≠ mxNs := by decide
@[simp] theorem mx_mxB1_ne_mxNn : mxB1 ≠ mxNn := by decide
@[simp] theorem mx_mxB1_ne_mxH : mxB1 ≠ mxH := by decide
@[simp] theorem mx_mxB1_ne_mxM : mxB1 ≠ mxM := by decide
@[simp] theorem mx_mxB1_ne_mxL : mxB1 ≠ mxL := by decide
@[simp] theorem mx_mxB1_ne_mxC1 : mxB1 ≠ mxC1 := by decide
@[simp] theorem mx_mxB1_ne_mxC2 : mxB1 ≠ mxC2 := by decide
@[simp] theorem mx_mxB1_ne_mxC3 : mxB1 ≠ mxC3 := by decide
@[simp] theorem mx_mxB1_ne_mxS : mxB1 ≠ mxS := by decide
@[simp] theorem mx_mxB1_ne_mxR : mxB1 ≠ mxR := by decide
@[simp] theorem mx_mxB1_ne_mxM2 : mxB1 ≠ mxM2 := by decide
@[simp] theorem mx_mxB1_ne_mxK1 : mxB1 ≠ mxK1 := by decide
@[simp] theorem mx_mxB1_ne_mxK2 : mxB1 ≠ mxK2 := by decide
@[simp] theorem mx_mxB1_ne_mxK3 : mxB1 ≠ mxK3 := by decide
@[simp] theorem mx_mxB1_ne_mxB2 : mxB1 ≠ mxB2 := by decide
@[simp] theorem mx_mxB1_ne_mxQ : mxB1 ≠ mxQ := by decide
@[simp] theorem mx_mxB1_ne_mxN : mxB1 ≠ mxN := by decide
@[simp] theorem mx_mxB1_ne_mxO : mxB1 ≠ mxO := by decide
@[simp] theorem mx_mxB1_ne_lKb : mxB1 ≠ lKb := by decide
@[simp] theorem mx_lKb_ne_mxB1 : lKb ≠ mxB1 := by decide
@[simp] theorem mx_mxB1_ne_lFl : mxB1 ≠ lFl := by decide
@[simp] theorem mx_lFl_ne_mxB1 : lFl ≠ mxB1 := by decide
@[simp] theorem mx_mxB1_ne_lDh : mxB1 ≠ lDh := by decide
@[simp] theorem mx_lDh_ne_mxB1 : lDh ≠ mxB1 := by decide
@[simp] theorem mx_mxB1_ne_lDt : mxB1 ≠ lDt := by decide
@[simp] theorem mx_lDt_ne_mxB1 : lDt ≠ mxB1 := by decide
@[simp] theorem mx_mxB1_ne_lDg : mxB1 ≠ lDg := by decide
@[simp] theorem mx_lDg_ne_mxB1 : lDg ≠ mxB1 := by decide
@[simp] theorem mx_mxB1_ne_lDi : mxB1 ≠ lDi := by decide
@[simp] theorem mx_lDi_ne_mxB1 : lDi ≠ mxB1 := by decide
@[simp] theorem mx_mxB1_ne_lDo1 : mxB1 ≠ lDo1 := by decide
@[simp] theorem mx_lDo1_ne_mxB1 : lDo1 ≠ mxB1 := by decide
@[simp] theorem mx_mxB1_ne_lDo2 : mxB1 ≠ lDo2 := by decide
@[simp] theorem mx_lDo2_ne_mxB1 : lDo2 ≠ mxB1 := by decide
@[simp] theorem mx_mxB1_ne_lRp : mxB1 ≠ lRp := by decide
@[simp] theorem mx_lRp_ne_mxB1 : lRp ≠ mxB1 := by decide
@[simp] theorem mx_mxB1_ne_lRn : mxB1 ≠ lRn := by decide
@[simp] theorem mx_lRn_ne_mxB1 : lRn ≠ mxB1 := by decide
@[simp] theorem mx_mxB1_ne_lFle : mxB1 ≠ lFle := by decide
@[simp] theorem mx_lFle_ne_mxB1 : lFle ≠ mxB1 := by decide
@[simp] theorem mx_mxB1_ne_lDir : mxB1 ≠ lDir := by decide
@[simp] theorem mx_lDir_ne_mxB1 : lDir ≠ mxB1 := by decide
@[simp] theorem mx_mxB2_ne_mxF : mxB2 ≠ mxF := by decide
@[simp] theorem mx_mxB2_ne_mxNs : mxB2 ≠ mxNs := by decide
@[simp] theorem mx_mxB2_ne_mxNn : mxB2 ≠ mxNn := by decide
@[simp] theorem mx_mxB2_ne_mxH : mxB2 ≠ mxH := by decide
@[simp] theorem mx_mxB2_ne_mxM : mxB2 ≠ mxM := by decide
@[simp] theorem mx_mxB2_ne_mxL : mxB2 ≠ mxL := by decide
@[simp] theorem mx_mxB2_ne_mxC1 : mxB2 ≠ mxC1 := by decide
@[simp] theorem mx_mxB2_ne_mxC2 : mxB2 ≠ mxC2 := by decide
@[simp] theorem mx_mxB2_ne_mxC3 : mxB2 ≠ mxC3 := by decide
@[simp] theorem mx_mxB2_ne_mxS : mxB2 ≠ mxS := by decide
@[simp] theorem mx_mxB2_ne_mxR : mxB2 ≠ mxR := by decide
@[simp] theorem mx_mxB2_ne_mxM2 : mxB2 ≠ mxM2 := by decide
@[simp] theorem mx_mxB2_ne_mxK1 : mxB2 ≠ mxK1 := by decide
@[simp] theorem mx_mxB2_ne_mxK2 : mxB2 ≠ mxK2 := by decide
@[simp] theorem mx_mxB2_ne_mxK3 : mxB2 ≠ mxK3 := by decide
@[simp] theorem mx_mxB2_ne_mxB1 : mxB2 ≠ mxB1 := by decide
@[simp] theorem mx_mxB2_ne_mxQ : mxB2 ≠ mxQ := by decide
@[simp] theorem mx_mxB2_ne_mxN : mxB2 ≠ mxN := by decide
@[simp] theorem mx_mxB2_ne_mxO : mxB2 ≠ mxO := by decide
@[simp] theorem mx_mxB2_ne_lKb : mxB2 ≠ lKb := by decide
@[simp] theorem mx_lKb_ne_mxB2 : lKb ≠ mxB2 := by decide
@[simp] theorem mx_mxB2_ne_lFl : mxB2 ≠ lFl := by decide
@[simp] theorem mx_lFl_ne_mxB2 : lFl ≠ mxB2 := by decide
@[simp] theorem mx_mxB2_ne_lDh : mxB2 ≠ lDh := by decide
@[simp] theorem mx_lDh_ne_mxB2 : lDh ≠ mxB2 := by decide
@[simp] theorem mx_mxB2_ne_lDt : mxB2 ≠ lDt := by decide
@[simp] theorem mx_lDt_ne_mxB2 : lDt ≠ mxB2 := by decide
@[simp] theorem mx_mxB2_ne_lDg : mxB2 ≠ lDg := by decide
@[simp] theorem mx_lDg_ne_mxB2 : lDg ≠ mxB2 := by decide
@[simp] theorem mx_mxB2_ne_lDi : mxB2 ≠ lDi := by decide
@[simp] theorem mx_lDi_ne_mxB2 : lDi ≠ mxB2 := by decide
@[simp] theorem mx_mxB2_ne_lDo1 : mxB2 ≠ lDo1 := by decide
@[simp] theorem mx_lDo1_ne_mxB2 : lDo1 ≠ mxB2 := by decide
@[simp] theorem mx_mxB2_ne_lDo2 : mxB2 ≠ lDo2 := by decide
@[simp] theorem mx_lDo2_ne_mxB2 : lDo2 ≠ mxB2 := by decide
@[simp] theorem mx_mxB2_ne_lRp : mxB2 ≠ lRp := by decide
@[simp] theorem mx_lRp_ne_mxB2 : lRp ≠ mxB2 := by decide
@[simp] theorem mx_mxB2_ne_lRn : mxB2 ≠ lRn := by decide
@[simp] theorem mx_lRn_ne_mxB2 : lRn ≠ mxB2 := by decide
@[simp] theorem mx_mxB2_ne_lFle : mxB2 ≠ lFle := by decide
@[simp] theorem mx_lFle_ne_mxB2 : lFle ≠ mxB2 := by decide
@[simp] theorem mx_mxB2_ne_lDir : mxB2 ≠ lDir := by decide
@[simp] theorem mx_lDir_ne_mxB2 : lDir ≠ mxB2 := by decide
@[simp] theorem mx_mxQ_ne_mxF : mxQ ≠ mxF := by decide
@[simp] theorem mx_mxQ_ne_mxNs : mxQ ≠ mxNs := by decide
@[simp] theorem mx_mxQ_ne_mxNn : mxQ ≠ mxNn := by decide
@[simp] theorem mx_mxQ_ne_mxH : mxQ ≠ mxH := by decide
@[simp] theorem mx_mxQ_ne_mxM : mxQ ≠ mxM := by decide
@[simp] theorem mx_mxQ_ne_mxL : mxQ ≠ mxL := by decide
@[simp] theorem mx_mxQ_ne_mxC1 : mxQ ≠ mxC1 := by decide
@[simp] theorem mx_mxQ_ne_mxC2 : mxQ ≠ mxC2 := by decide
@[simp] theorem mx_mxQ_ne_mxC3 : mxQ ≠ mxC3 := by decide
@[simp] theorem mx_mxQ_ne_mxS : mxQ ≠ mxS := by decide
@[simp] theorem mx_mxQ_ne_mxR : mxQ ≠ mxR := by decide
@[simp] theorem mx_mxQ_ne_mxM2 : mxQ ≠ mxM2 := by decide
@[simp] theorem mx_mxQ_ne_mxK1 : mxQ ≠ mxK1 := by decide
@[simp] theorem mx_mxQ_ne_mxK2 : mxQ ≠ mxK2 := by decide
@[simp] theorem mx_mxQ_ne_mxK3 : mxQ ≠ mxK3 := by decide
@[simp] theorem mx_mxQ_ne_mxB1 : mxQ ≠ mxB1 := by decide
@[simp] theorem mx_mxQ_ne_mxB2 : mxQ ≠ mxB2 := by decide
@[simp] theorem mx_mxQ_ne_mxN : mxQ ≠ mxN := by decide
@[simp] theorem mx_mxQ_ne_mxO : mxQ ≠ mxO := by decide
@[simp] theorem mx_mxQ_ne_lKb : mxQ ≠ lKb := by decide
@[simp] theorem mx_lKb_ne_mxQ : lKb ≠ mxQ := by decide
@[simp] theorem mx_mxQ_ne_lFl : mxQ ≠ lFl := by decide
@[simp] theorem mx_lFl_ne_mxQ : lFl ≠ mxQ := by decide
@[simp] theorem mx_mxQ_ne_lDh : mxQ ≠ lDh := by decide
@[simp] theorem mx_lDh_ne_mxQ : lDh ≠ mxQ := by decide
@[simp] theorem mx_mxQ_ne_lDt : mxQ ≠ lDt := by decide
@[simp] theorem mx_lDt_ne_mxQ : lDt ≠ mxQ := by decide
@[simp] theorem mx_mxQ_ne_lDg : mxQ ≠ lDg := by decide
@[simp] theorem mx_lDg_ne_mxQ : lDg ≠ mxQ := by decide
@[simp] theorem mx_mxQ_ne_lDi : mxQ ≠ lDi := by decide
@[simp] theorem mx_lDi_ne_mxQ : lDi ≠ mxQ := by decide
@[simp] theorem mx_mxQ_ne_lDo1 : mxQ ≠ lDo1 := by decide
@[simp] theorem mx_lDo1_ne_mxQ : lDo1 ≠ mxQ := by decide
@[simp] theorem mx_mxQ_ne_lDo2 : mxQ ≠ lDo2 := by decide
@[simp] theorem mx_lDo2_ne_mxQ : lDo2 ≠ mxQ := by decide
@[simp] theorem mx_mxQ_ne_lRp : mxQ ≠ lRp := by decide
@[simp] theorem mx_lRp_ne_mxQ : lRp ≠ mxQ := by decide
@[simp] theorem mx_mxQ_ne_lRn : mxQ ≠ lRn := by decide
@[simp] theorem mx_lRn_ne_mxQ : lRn ≠ mxQ := by decide
@[simp] theorem mx_mxQ_ne_lFle : mxQ ≠ lFle := by decide
@[simp] theorem mx_lFle_ne_mxQ : lFle ≠ mxQ := by decide
@[simp] theorem mx_mxQ_ne_lDir : mxQ ≠ lDir := by decide
@[simp] theorem mx_lDir_ne_mxQ : lDir ≠ mxQ := by decide
@[simp] theorem mx_mxN_ne_mxF : mxN ≠ mxF := by decide
@[simp] theorem mx_mxN_ne_mxNs : mxN ≠ mxNs := by decide
@[simp] theorem mx_mxN_ne_mxNn : mxN ≠ mxNn := by decide
@[simp] theorem mx_mxN_ne_mxH : mxN ≠ mxH := by decide
@[simp] theorem mx_mxN_ne_mxM : mxN ≠ mxM := by decide
@[simp] theorem mx_mxN_ne_mxL : mxN ≠ mxL := by decide
@[simp] theorem mx_mxN_ne_mxC1 : mxN ≠ mxC1 := by decide
@[simp] theorem mx_mxN_ne_mxC2 : mxN ≠ mxC2 := by decide
@[simp] theorem mx_mxN_ne_mxC3 : mxN ≠ mxC3 := by decide
@[simp] theorem mx_mxN_ne_mxS : mxN ≠ mxS := by decide
@[simp] theorem mx_mxN_ne_mxR : mxN ≠ mxR := by decide
@[simp] theorem mx_mxN_ne_mxM2 : mxN ≠ mxM2 := by decide
@[simp] theorem mx_mxN_ne_mxK1 : mxN ≠ mxK1 := by decide
@[simp] theorem mx_mxN_ne_mxK2 : mxN ≠ mxK2 := by decide
@[simp] theorem mx_mxN_ne_mxK3 : mxN ≠ mxK3 := by decide
@[simp] theorem mx_mxN_ne_mxB1 : mxN ≠ mxB1 := by decide
@[simp] theorem mx_mxN_ne_mxB2 : mxN ≠ mxB2 := by decide
@[simp] theorem mx_mxN_ne_mxQ : mxN ≠ mxQ := by decide
@[simp] theorem mx_mxN_ne_mxO : mxN ≠ mxO := by decide
@[simp] theorem mx_mxN_ne_lKb : mxN ≠ lKb := by decide
@[simp] theorem mx_lKb_ne_mxN : lKb ≠ mxN := by decide
@[simp] theorem mx_mxN_ne_lFl : mxN ≠ lFl := by decide
@[simp] theorem mx_lFl_ne_mxN : lFl ≠ mxN := by decide
@[simp] theorem mx_mxN_ne_lDh : mxN ≠ lDh := by decide
@[simp] theorem mx_lDh_ne_mxN : lDh ≠ mxN := by decide
@[simp] theorem mx_mxN_ne_lDt : mxN ≠ lDt := by decide
@[simp] theorem mx_lDt_ne_mxN : lDt ≠ mxN := by decide
@[simp] theorem mx_mxN_ne_lDg : mxN ≠ lDg := by decide
@[simp] theorem mx_lDg_ne_mxN : lDg ≠ mxN := by decide
@[simp] theorem mx_mxN_ne_lDi : mxN ≠ lDi := by decide
@[simp] theorem mx_lDi_ne_mxN : lDi ≠ mxN := by decide
@[simp] theorem mx_mxN_ne_lDo1 : mxN ≠ lDo1 := by decide
@[simp] theorem mx_lDo1_ne_mxN : lDo1 ≠ mxN := by decide
@[simp] theorem mx_mxN_ne_lDo2 : mxN ≠ lDo2 := by decide
@[simp] theorem mx_lDo2_ne_mxN : lDo2 ≠ mxN := by decide
@[simp] theorem mx_mxN_ne_lRp : mxN ≠ lRp := by decide
@[simp] theorem mx_lRp_ne_mxN : lRp ≠ mxN := by decide
@[simp] theorem mx_mxN_ne_lRn : mxN ≠ lRn := by decide
@[simp] theorem mx_lRn_ne_mxN : lRn ≠ mxN := by decide
@[simp] theorem mx_mxN_ne_lFle : mxN ≠ lFle := by decide
@[simp] theorem mx_lFle_ne_mxN : lFle ≠ mxN := by decide
@[simp] theorem mx_mxN_ne_lDir : mxN ≠ lDir := by decide
@[simp] theorem mx_lDir_ne_mxN : lDir ≠ mxN := by decide
@[simp] theorem mx_mxO_ne_mxF : mxO ≠ mxF := by decide
@[simp] theorem mx_mxO_ne_mxNs : mxO ≠ mxNs := by decide
@[simp] theorem mx_mxO_ne_mxNn : mxO ≠ mxNn := by decide
@[simp] theorem mx_mxO_ne_mxH : mxO ≠ mxH := by decide
@[simp] theorem mx_mxO_ne_mxM : mxO ≠ mxM := by decide
@[simp] theorem mx_mxO_ne_mxL : mxO ≠ mxL := by decide
@[simp] theorem mx_mxO_ne_mxC1 : mxO ≠ mxC1 := by decide
@[simp] theorem mx_mxO_ne_mxC2 : mxO ≠ mxC2 := by decide
@[simp] theorem mx_mxO_ne_mxC3 : mxO ≠ mxC3 := by decide
@[simp] theorem mx_mxO_ne_mxS : mxO ≠ mxS := by decide
@[simp] theorem mx_mxO_ne_mxR : mxO ≠ mxR := by decide
@[simp] theorem mx_mxO_ne_mxM2 : mxO ≠ mxM2 := by decide
@[simp] theorem mx_mxO_ne_mxK1 : mxO ≠ mxK1 := by decide
@[simp] theorem mx_mxO_ne_mxK2 : mxO ≠ mxK2 := by decide
@[simp] theorem mx_mxO_ne_mxK3 : mxO ≠ mxK3 := by decide
@[simp] theorem mx_mxO_ne_mxB1 : mxO ≠ mxB1 := by decide
@[simp] theorem mx_mxO_ne_mxB2 : mxO ≠ mxB2 := by decide
@[simp] theorem mx_mxO_ne_mxQ : mxO ≠ mxQ := by decide
@[simp] theorem mx_mxO_ne_mxN : mxO ≠ mxN := by decide
@[simp] theorem mx_mxO_ne_lKb : mxO ≠ lKb := by decide
@[simp] theorem mx_lKb_ne_mxO : lKb ≠ mxO := by decide
@[simp] theorem mx_mxO_ne_lFl : mxO ≠ lFl := by decide
@[simp] theorem mx_lFl_ne_mxO : lFl ≠ mxO := by decide
@[simp] theorem mx_mxO_ne_lDh : mxO ≠ lDh := by decide
@[simp] theorem mx_lDh_ne_mxO : lDh ≠ mxO := by decide
@[simp] theorem mx_mxO_ne_lDt : mxO ≠ lDt := by decide
@[simp] theorem mx_lDt_ne_mxO : lDt ≠ mxO := by decide
@[simp] theorem mx_mxO_ne_lDg : mxO ≠ lDg := by decide
@[simp] theorem mx_lDg_ne_mxO : lDg ≠ mxO := by decide
@[simp] theorem mx_mxO_ne_lDi : mxO ≠ lDi := by decide
@[simp] theorem mx_lDi_ne_mxO : lDi ≠ mxO := by decide
@[simp] theorem mx_mxO_ne_lDo1 : mxO ≠ lDo1 := by decide
@[simp] theorem mx_lDo1_ne_mxO : lDo1 ≠ mxO := by decide
@[simp] theorem mx_mxO_ne_lDo2 : mxO ≠ lDo2 := by decide
@[simp] theorem mx_lDo2_ne_mxO : lDo2 ≠ mxO := by decide
@[simp] theorem mx_mxO_ne_lRp : mxO ≠ lRp := by decide
@[simp] theorem mx_lRp_ne_mxO : lRp ≠ mxO := by decide
@[simp] theorem mx_mxO_ne_lRn : mxO ≠ lRn := by decide
@[simp] theorem mx_lRn_ne_mxO : lRn ≠ mxO := by decide
@[simp] theorem mx_mxO_ne_lFle : mxO ≠ lFle := by decide
@[simp] theorem mx_lFle_ne_mxO : lFle ≠ mxO := by decide
@[simp] theorem mx_mxO_ne_lDir : mxO ≠ lDir := by decide
@[simp] theorem mx_lDir_ne_mxO : lDir ≠ mxO := by decide

def mxParams : List MlS := [mxF, mxNs, mxNn, mxH, mxM]
def mxLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lDo1, lDo2, lRp, lRn, mxL, mxC1, mxC2, mxC3, mxS, mxR, mxM2,
  mxK1, mxK2, mxK3, mxB1, mxB2, mxQ, mxN, mxO]

def mxRet (C : Ctx) (er em : ExpHOL 64) : ProgHOL 64 :=
  allocP C mxO (.const 16) (.seq (.store (vv mxO) er) (.seq (.store (.op .add [vv mxO, .const 8]) em)
    (.return (vv mxO))))

def mxIns (C : Ctx) : ProgHOL 64 := mlInsP C mxN (vv mxH) (.const 0) (vv mxR) (vv mxM2) (mxRet C (vv mxR) (vv mxN))

def mxCall (k : MlS) (eH eM : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.local, k), none)) fMx [.op .sub [vv mxF, .const 1], vv mxNs, vv mxNn, eH, eM])
  (.seq (.assign .local mxR (.load .one (vv k))) (.seq (.assign .local mxM2 (.load .one (.op .add [vv k, .const 8])))
    rest))

/-- The names-block scan of `x` into `q`. -/
def mxHas (q : MlS) (ex : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.local, q), none)) fLpsHas [vv mxNs, ex, .const 0, vv mxNn]) rest

/-- A memo hit answers; a miss runs the arm. -/
def mxMemo (C : Ctx) (arm : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.local, mxL), none)) fMl [vv mxM, vv mxH, .const 0])
  (.ite (.cmp .notEqual (vv mxL) (.const 0)) (mxRet C (.op .sub [vv mxL, .const 1]) (vv mxM)) arm)

def mxArm1 (C : Ctx) : ProgHOL 64 := mxCall mxK1 (vv mxC1) (vv mxM) (mxIns C)

def mxArm2 (C : Ctx) : ProgHOL 64 :=
  mxCall mxK1 (vv mxC1) (vv mxM) (.seq (.assign .local mxB1 (vv mxR))
    (mxCall mxK2 (vv mxC2) (vv mxM2) (.seq (.assign .local mxR (.op .or [vv mxB1, vv mxR])) (mxIns C))))

def mxArm3 (C : Ctx) : ProgHOL 64 :=
  mxCall mxK1 (vv mxC1) (vv mxM) (.seq (.assign .local mxB1 (vv mxR))
    (mxCall mxK2 (vv mxC2) (vv mxM2) (.seq (.assign .local mxB2 (vv mxR))
      (mxCall mxK3 (vv mxC3) (vv mxM2)
        (.seq (.assign .local mxR (.op .or [.op .or [vv mxB1, vv mxB2], vv mxR])) (mxIns C))))))

def mxArmP (C : Ctx) : ProgHOL 64 :=
  mxCall mxK1 (vv mxC1) (vv mxM) (mxHas mxQ (vv mxS)
    (.seq (.assign .local mxR (.op .or [vv mxQ, vv mxR])) (mxIns C)))

def mxCore (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .equal (vv mxF) (.const 0)) hang
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv mxH)) (.seq eViewP
  (.ite (.cmp .equal (vv lDg) (.const 1))
    (.seq (.assign .local mxC1 (.load .one (vv lRp))) (mxMemo C (mxArm1 C)))
  (.ite (.cmp .equal (vv lDg) (.const 3))
    (.seq (.assign .local mxS (.load .one (vv lRp))) (mxHas mxQ (vv mxS) (mxRet C (vv mxQ) (vv mxM))))
  (.ite (.cmp .equal (vv lDg) (.const 4))
    (.seq (.assign .local mxC1 (.load .one (vv lRp)))
      (.seq (.assign .local mxC2 (.load .one (.op .add [vv lRp, .const 8]))) (mxMemo C (mxArm2 C))))
  (.ite (.cmp .equal (vv lDg) (.const 5))
    (.seq (.assign .local mxC1 (.load .one (vv lRp)))
      (.seq (.assign .local mxC2 (.load .one (.op .add [vv lRp, .const 8]))) (mxMemo C (mxArm2 C))))
  (.ite (.cmp .equal (vv lDg) (.const 6))
    (.seq (.assign .local mxC1 (.load .one (vv lRp)))
      (.seq (.assign .local mxC2 (.load .one (.op .add [vv lRp, .const 8]))) (mxMemo C (mxArm2 C))))
  (.ite (.cmp .equal (vv lDg) (.const 7))
    (.seq (.assign .local mxC1 (.load .one (vv lRp)))
      (.seq (.assign .local mxC2 (.load .one (.op .add [vv lRp, .const 8])))
        (.seq (.assign .local mxC3 (.load .one (.op .add [vv lRp, .const 16]))) (mxMemo C (mxArm3 C)))))
  (.ite (.cmp .equal (vv lDg) (.const 9))
    (.seq (.assign .local mxS (.load .one (vv lRp)))
      (.seq (.assign .local mxC1 (.load .one (.op .add [vv lRp, .const 8]))) (mxMemo C (mxArmP C))))
    (mxRet C (.const 0) (vv mxM))))))))))))

def mxBody (C : Ctx) : ProgHOL 64 := prologue mxLocals (mxCore C)

structure MxCodes (C : Ctx) : Prop where
  ml : C.code.lookup fMl = some (mlParams.map (fun p => (p, ShapeHOL.one)), mlBody, .one)
  lh : C.code.lookup fLpsHas = some (lhParams.map (fun p => (p, ShapeHOL.one)), lhBody, .one)
  self : C.code.lookup fMx = some (mxParams.map (fun p => (p, ShapeHOL.one)), mxBody C, .one)

section
variable {σ : Type}

theorem specR_mxRetI {C : Ctx} (hok : CtxOK C) {H0 H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem}
    {D : List MlS} (er em : ExpHOL 64) (r : Bool) (pm : BitVec 64) (memo : Std.HashMap EIdx Bool)
    (hD : mxO ∈ D) (her : ∀ w, sev ((mxO, w) :: Γ) er = some (boolW r)) (hem : ∀ w, sev ((mxO, w) :: Γ) em = some pm)
    (hrep : LbRep C H pm memo) (h0 : H0 <+: H) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (mxRet C er em) s (pure (r, memo)) (PostLb (ctxH C H0) s) := by
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hlay := hok.heapLay
  refine specR_allocI (C := ctxH C H) mxO (.const 16) 2 (by omega) hD (fun _ => rfl) (fun H1 ws hp1 hws hroom => ?_)
  have hp1' : H <+: H1 := hp1
  have hL := hp1'.length_le
  change SpecR (Inv (ctxH C (H1 ++ ws)) s ((mxO, cellA C H1.length) :: Γ) _ _) _ _ _ _
  refine specR_heapStoreI (ctxOK_H hok _) (vv mxO) er H1.length (by show _ < (H1 ++ ws).length; simp; omega)
    (boolW r) (by simp <;> rfl) (her _) ?_
  change SpecR (Inv (ctxH C ((H1 ++ ws).set H1.length (boolW r))) _ _ _ _) _ _ _ _
  refine specR_heapStoreI (ctxOK_H hok _) (.op .add [vv mxO, .const 8]) em (H1.length + 1)
    (by show _ < ((H1 ++ ws).set _ _).length; simp; omega) pm (by simp +decide [sev]; exact cellA_add8 C _) (hem _) ?_
  have g0 : (((H1 ++ ws).set H1.length (boolW r)).set (H1.length + 1) pm)[H1.length]? = some (boolW r) := by
    simp [List.getElem?_set, hws]
  have g1 : (((H1 ++ ws).set H1.length (boolW r)).set (H1.length + 1) pm)[H1.length + 1]? = some pm := by
    simp [List.getElem?_set, hws]
  have hpre : H <+: ((H1 ++ ws).set H1.length (boolW r)).set (H1.length + 1) pm :=
    prefix_set_ge (prefix_set_ge (hp1'.trans (List.prefix_append _ _)) _ (by omega) _) _ (by omega) _
  exact specR_returnI _ (cellA C H1.length) (by simp +decide [Env.get] <;> rfl)
    (fun t ht => ⟨rfl, _, H1.length, pm, h0.trans hpre, rfl, g0, g1, lbRep_toH (lbRep_mono hpre hrep), sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem specR_mxInsI {C : Ctx} (hok : CtxOK C) {H0 H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem}
    {D : List MlS} (h : EIdx) (r : Bool) (pm : BitVec 64)
    (memo : Std.HashMap EIdx Bool) (hD : mxN ∈ D ∧ mxO ∈ D) (hH : Γ.get mxH = some (Enc.idxW h))
    (hR : Γ.get mxR = some (boolW r)) (hM : Γ.get mxM2 = some pm)
    (hrep : LbRep C H pm memo) (h0 : H0 <+: H) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (mxIns C) s (pure (r, memo.insert h r)) (PostLb (ctxH C H0) s) := by
  obtain ⟨xs, hm, he⟩ := hrep
  unfold mxIns
  refine specR_mlInsI hok mxN (vv mxH) (.const 0) (vv mxR) (vv mxM2) (Enc.idxW h) 0 pm r xs hD.1
    (fun w => by simp [Env.get, hH]) (fun w => rfl) (fun w => by simp [Env.get, hR])
    (fun w => by simp [Env.get, hM]) hm (fun H' o hp' hm' => ?_)
  exact specR_mxRetI hok (vv mxR) (vv mxN) r (cellA C o) (memo.insert h r) hD.2
    (fun w => by simp [Env.get, hR]) (fun w => by simp [Env.get]) (lbRep_insert he h r hm') (h0.trans hp')

theorem mx_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ mxLocals → (ctxEnv C ++ mxParams.zip vals).get x = none :=
  Knot.params_none C mxLocals mxParams vals (by decide) (by decide)

/-- The walk's spec at fuel `n`, for every argument (the induction hypothesis the arms use). -/
def MxRec (C : Ctx) (names : List NIdx) (pn : Nat) (n : Nat) : Prop :=
  ∀ (h : EIdx) (memo : Std.HashMap EIdx Bool) (H : List (BitVec 64)) (s : AState) (pm : BitVec 64),
    C.H <+: H → LbRep C H pm memo →
    SpecR (σ := σ) (Pre (ctxH C H) s (mxParams.zip [BitVec.ofNat 64 n, cellA C pn, BitVec.ofNat 64 names.length,
      Enc.idxW h, pm])) (mxBody C) s (mentionsAnyGo names memo n h) (PostLb (ctxH C H) s)

/-- One recursive call, then the pair block read back. -/
theorem specR_mxCallI {α : Type} {C : Ctx} (hc : MxCodes C) {n : Nat} (names : List NIdx) (pn : Nat)
    (ih : MxRec (σ := σ) C names pn n)
    {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {k : Bool × Std.HashMap EIdx Bool → AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (eH eM : ExpHOL 64) (h : EIdx) (pm : BitVec 64) (memo : Std.HashMap EIdx Bool)
    (hx : x ∈ D ∧ mxR ∈ D ∧ mxM2 ∈ D) (hxn : x ≠ mxR ∧ mxM2 ≠ x) (hp : C.H <+: H) (hrep : LbRep C H pm memo)
    (hF : Γ.get mxF = some (BitVec.ofNat 64 (n + 1))) (hNs : Γ.get mxNs = some (cellA C pn))
    (hNn : Γ.get mxNn = some (BitVec.ofNat 64 names.length))
    (heH : sev Γ eH = some (Enc.idxW h)) (heM : sev Γ eM = some pm)
    (hk : ∀ (rm : Bool × Std.HashMap EIdx Bool) H' pm' w, H <+: H' → LbRep C H' pm' rm.2 →
      SpecR (Inv (ctxH C H') s ((mxM2, pm') :: (mxR, boolW rm.1) :: (x, w) :: Γ) [] D) rest s (k rm) R) :
    SpecR (Inv (ctxH C H) s Γ M D) (mxCall x eH eM rest) s (mentionsAnyGo names memo n h >>= k) R := by
  unfold mxCall
  refine specR_callNIH (C := ctxH C H) x fMx mxParams [.op .sub [vv mxF, .const 1], vv mxNs, vv mxNn, eH, eM]
    (mxBody C) [BitVec.ofNat 64 n, cellA C pn, BitVec.ofNat 64 names.length, Enc.idxW h, pm] (by decide) rfl hx.1
    hc.self
    ⟨by simp [sev, hF]; exact Ex.ofNat_succ_sub_one _, by simp [hNs], by simp [hNn], heH, heM, trivial⟩
    (PostLb (ctxH C H) s)
    (fun rm w s' H' => s' = s ∧ ∃ o pm', w = cellA C o ∧ H'[o]? = some (boolW rm.1) ∧ H'[o + 1]? = some pm' ∧
      LbRep C H' pm' rm.2)
    (fun rm w s' st ⟨h1, H', o, pm', hp', hw, h0, h1', hrep', hsr⟩ =>
      ⟨H', hp', ⟨h1, o, pm', hw, h0, h1', lbRep_ofH hrep'⟩, by subst h1; exact hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mxParams _ rfl hlk) (ih h memo H s pm hp hrep))
    (fun rm w s' H' hp' ⟨hs', o, pm', hw, h0, h1', hrep'⟩ => ?_)
  subst hs' hw
  refine UD.specR_heapLoadI' (C := ctxH C H') mxR (vv x) o (boolW rm.1) h0 hx.2.1 (by simp [Env.get]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H') mxM2 (.op .add [vv x, .const 8]) (o + 1) pm' h1' hx.2.2
    (by simp [sev, Env.get, hxn.1]; exact (cellA_add8 C o : _)) ?_
  exact hk rm H' pm' (cellA C o) hp' hrep'

/-- The names-block scan: the twin's `names.contains x`, the state and heap prefix unchanged. -/
theorem specR_mxHasI {α : Type} {C : Ctx} (hc : MxCodes C) (names : List NIdx) (pn : Nat)
    (hl : names.length < 2 ^ 59) (hns : Elems C.H pn names)
    {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (q : MlS) (ex : ExpHOL 64) (x : NIdx) (hq : q ∈ D) (hp : C.H <+: H)
    (hNs : Γ.get mxNs = some (cellA C pn)) (hNn : Γ.get mxNn = some (BitVec.ofNat 64 names.length))
    (hex : sev Γ ex = some (Enc.idxW x))
    (hk : ∀ H', H <+: H' → SpecR (Inv (ctxH C H') s ((q, boolW (names.contains x)) :: Γ) [] D) rest s m R) :
    SpecR (Inv (ctxH C H) s Γ M D) (mxHas q ex rest) s m R := by
  unfold mxHas
  refine specR_callPure (C := ctxH C H) q fLpsHas lhParams [vv mxNs, ex, .const 0, vv mxNn] lhBody
    [cellA C pn, Enc.idxW x, BitVec.ofNat 64 0, BitVec.ofNat 64 names.length] ((names.drop 0).contains x)
    (by decide) rfl hq hc.lh ⟨by simp [hNs], hex, rfl, by simp [hNn], trivial⟩
    (PostB (ctxH C H)) (fun b w s' H' => w = boolW b)
    (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu lhParams _ rfl hlk)
      (lh_spec (ctxH C H) hc.lh names pn x hl names.length 0 H s (List.prefix_refl _)
        (fun j hj => ConPanqueque.T.Decl.get_prefix (hns j hj) hp) (by omega) (by omega)))
    (fun w H' hp' hw => ?_)
  subst hw
  simp only [List.drop_zero]
  exact hk H' hp'

theorem mx_sev_or2 (Γ : Env) (e1 e2 : ExpHOL 64) (a b : BitVec 64)
    (h1 : sev Γ e1 = some a) (h2 : sev Γ e2 = some b) : sev Γ (.op .or [e1, e2]) = some (a ||| b) := by
  simp [sev, h1, h2]

theorem mx_boolW_or (a b : Bool) : boolW a ||| boolW b = boolW (a || b) := by
  cases a <;> cases b <;> rfl

/-- A memo hit answers from the memo. -/
theorem specR_mxHitI {C : Ctx} (hok : CtxOK C) (hc : MxCodes C) {H : List (BitVec 64)} {s : AState} {Γ : Env}
    {M : Mem} {D : List MlS} (arm : ProgHOL 64) (h : EIdx) (pm : BitVec 64) (memo : Std.HashMap EIdx Bool) (r : Bool)
    (hD : mxL ∈ D ∧ mxO ∈ D) (hH : Γ.get mxH = some (Enc.idxW h)) (hM : Γ.get mxM = some pm)
    (hrep : LbRep C H pm memo) (hmh : memo[h]? = some r) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (mxMemo C arm) s (pure (r, memo)) (PostLb (ctxH C H) s) := by
  obtain ⟨xs, hm, he⟩ := id hrep
  unfold mxMemo
  refine specR_callPure (C := ctxH C H) mxL fMl mlParams [vv mxM, vv mxH, .const 0] mlBody
    [pm, Enc.idxW h, 0] (xs.lookup (Enc.idxW h, 0)) (by decide) rfl hD.1 hc.ml
    ⟨by simp [hM], by simp [hH], rfl, trivial⟩
    (PostWV (ctxH C H) s) (fun o w s' H' => w = optWG boolW o ∧ H' = H)
    (fun o w s' st ⟨h1, h2, h3⟩ => ⟨H, List.prefix_refl _, ⟨h2, rfl⟩, by subst h1; exact h3⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mlParams _ rfl hlk)
      (ml_spec C hok hc.ml (Enc.idxW h) 0 xs pm H s (mnodes_toH hm)))
    (fun w H' _ ⟨hw, hH'⟩ => ?_)
  subst hw; subst H'
  rw [← he h, hmh]
  have hne1 : boolW r + 1 ≠ 0 := by cases r <;> decide
  refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne1) (fun _ => ?_)
    (fun h => absurd h (by decide))
  exact specR_mxRetI hok _ (vv mxM) r pm memo hD.2
    (fun w => by simp [sev, Env.get, optWG]; exact BitVec.add_sub_cancel _ _)
    (fun w => by simp [Env.get, hM]) hrep (List.prefix_refl _)

/-- A memo miss runs the arm. -/
theorem specR_mxMissI {α : Type} {C : Ctx} (hok : CtxOK C) (hc : MxCodes C) {H : List (BitVec 64)} {s : AState}
    {Γ : Env} {M : Mem} {D : List MlS} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (arm : ProgHOL 64) (h : EIdx) (pm : BitVec 64) (memo : Std.HashMap EIdx Bool)
    (hD : mxL ∈ D) (hH : Γ.get mxH = some (Enc.idxW h)) (hM : Γ.get mxM = some pm)
    (hrep : LbRep C H pm memo) (hmh : memo[h]? = none)
    (harm : SpecR (Inv (ctxH C H) s ((mxL, 0) :: Γ) [] D) arm s m R) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (mxMemo C arm) s m R := by
  obtain ⟨xs, hm, he⟩ := id hrep
  unfold mxMemo
  refine specR_callPure (C := ctxH C H) mxL fMl mlParams [vv mxM, vv mxH, .const 0] mlBody
    [pm, Enc.idxW h, 0] (xs.lookup (Enc.idxW h, 0)) (by decide) rfl hD hc.ml
    ⟨by simp [hM], by simp [hH], rfl, trivial⟩
    (PostWV (ctxH C H) s) (fun o w s' H' => w = optWG boolW o ∧ H' = H)
    (fun o w s' st ⟨h1, h2, h3⟩ => ⟨H, List.prefix_refl _, ⟨h2, rfl⟩, by subst h1; exact h3⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mlParams _ rfl hlk)
      (ml_spec C hok hc.ml (Enc.idxW h) 0 xs pm H s (mnodes_toH hm)))
    (fun w H' _ ⟨hw, hH'⟩ => ?_)
  subst hw; subst H'
  rw [← he h, hmh]
  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
    (fun _ => ?_)
  exact harm

theorem specR_mxArm1I {C : Ctx} (hok : CtxOK C) (hc : MxCodes C) {n : Nat} (names : List NIdx) (pn : Nat)
    (ih : MxRec (σ := σ) C names pn n)
    {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (h c1 : EIdx) (pm : BitVec 64)
    (memo : Std.HashMap EIdx Bool)
    (hD : mxK1 ∈ D ∧ mxR ∈ D ∧ mxM2 ∈ D ∧ mxN ∈ D ∧ mxO ∈ D) (hp : C.H <+: H)
    (hrep : LbRep C H pm memo) (hF : Γ.get mxF = some (BitVec.ofNat 64 (n + 1)))
    (hNs : Γ.get mxNs = some (cellA C pn)) (hNn : Γ.get mxNn = some (BitVec.ofNat 64 names.length))
    (hH : Γ.get mxH = some (Enc.idxW h)) (hM : Γ.get mxM = some pm) (hC1 : Γ.get mxC1 = some (Enc.idxW c1)) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (mxArm1 C) s
      (mentionsAnyGo names memo n c1 >>= fun x => match x with
        | (r, m) => pure (r, m.insert h r)) (PostLb (ctxH C H) s) := by
  unfold mxArm1
  refine specR_mxCallI hc names pn ih mxK1 (vv mxC1) (vv mxM) c1 pm memo ⟨hD.1, hD.2.1, hD.2.2.1⟩
    ⟨by decide, by decide⟩ hp hrep hF hNs hNn (by simp [hC1]) (by simp [hM]) (fun rm H1 pm1 w1 hp1 hrep1 => ?_)
  obtain ⟨r1, m1⟩ := rm
  dsimp only
  exact specR_mxInsI hok h r1 pm1 m1 ⟨hD.2.2.2.1, hD.2.2.2.2⟩ (by simp [Env.get, hH]) (by simp [Env.get])
    (by simp [Env.get]) hrep1 hp1

theorem specR_mxArm2I {C : Ctx} (hok : CtxOK C) (hc : MxCodes C) {n : Nat} (names : List NIdx) (pn : Nat)
    (ih : MxRec (σ := σ) C names pn n)
    {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (h c1 c2 : EIdx) (pm : BitVec 64)
    (memo : Std.HashMap EIdx Bool)
    (hD : mxK1 ∈ D ∧ mxK2 ∈ D ∧ mxR ∈ D ∧ mxM2 ∈ D ∧ mxN ∈ D ∧ mxO ∈ D ∧ mxB1 ∈ D) (hp : C.H <+: H)
    (hrep : LbRep C H pm memo) (hF : Γ.get mxF = some (BitVec.ofNat 64 (n + 1)))
    (hNs : Γ.get mxNs = some (cellA C pn)) (hNn : Γ.get mxNn = some (BitVec.ofNat 64 names.length))
    (hH : Γ.get mxH = some (Enc.idxW h)) (hM : Γ.get mxM = some pm) (hC1 : Γ.get mxC1 = some (Enc.idxW c1))
    (hC2 : Γ.get mxC2 = some (Enc.idxW c2)) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (mxArm2 C) s
      (mentionsAnyGo names memo n c1 >>= fun d => mentionsAnyGo names d.2 n c2 >>= fun d1 =>
        (pure (d.1 || d1.1, d1.2) : AM (Bool × Std.HashMap EIdx Bool)) >>= fun y => pure (y.1, y.2.insert h y.1))
      (PostLb (ctxH C H) s) := by
  unfold mxArm2
  refine specR_mxCallI hc names pn ih mxK1 (vv mxC1) (vv mxM) c1 pm memo ⟨hD.1, hD.2.2.1, hD.2.2.2.1⟩
    ⟨by decide, by decide⟩ hp hrep hF hNs hNn (by simp [hC1]) (by simp [hM]) (fun rm H1 pm1 w1 hp1 hrep1 => ?_)
  obtain ⟨b1, m1⟩ := rm
  dsimp only
  refine specR_assignI mxB1 (vv mxR) (boolW b1) hD.2.2.2.2.2.2 (by simp [Env.get]) ?_
  refine specR_mxCallI hc names pn ih mxK2 (vv mxC2) (vv mxM2) c2 pm1 m1 ⟨hD.2.1, hD.2.2.1, hD.2.2.2.1⟩
    ⟨by decide, by decide⟩ (hp.trans hp1) hrep1 (by simp [Env.get, hF]) (by simp [Env.get, hNs])
    (by simp [Env.get, hNn]) (by simp [Env.get, hC2]) (by simp [Env.get]) (fun rm H2 pm2 w2 hp2 hrep2 => ?_)
  obtain ⟨b2, m2⟩ := rm
  dsimp only
  simp only [pure_bind]
  refine specR_assignI mxR (.op .or [vv mxB1, vv mxR]) (boolW (b1 || b2)) hD.2.2.1
    (by rw [mx_sev_or2 _ _ _ (boolW b1) (boolW b2) (by simp [Env.get]) (by simp [Env.get]), mx_boolW_or]) ?_
  exact specR_mxInsI hok h (b1 || b2) pm2 m2 ⟨hD.2.2.2.2.1, hD.2.2.2.2.2.1⟩ (by simp [Env.get, hH])
    (by simp [Env.get]) (by simp [Env.get]) hrep2 (hp1.trans hp2)

theorem specR_mxArm3I {C : Ctx} (hok : CtxOK C) (hc : MxCodes C) {n : Nat} (names : List NIdx) (pn : Nat)
    (ih : MxRec (σ := σ) C names pn n)
    {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (h c1 c2 c3 : EIdx) (pm : BitVec 64)
    (memo : Std.HashMap EIdx Bool)
    (hD : mxK1 ∈ D ∧ mxK2 ∈ D ∧ mxK3 ∈ D ∧ mxR ∈ D ∧ mxM2 ∈ D ∧ mxN ∈ D ∧ mxO ∈ D ∧ mxB1 ∈ D ∧ mxB2 ∈ D)
    (hp : C.H <+: H) (hrep : LbRep C H pm memo) (hF : Γ.get mxF = some (BitVec.ofNat 64 (n + 1)))
    (hNs : Γ.get mxNs = some (cellA C pn)) (hNn : Γ.get mxNn = some (BitVec.ofNat 64 names.length))
    (hH : Γ.get mxH = some (Enc.idxW h)) (hM : Γ.get mxM = some pm) (hC1 : Γ.get mxC1 = some (Enc.idxW c1))
    (hC2 : Γ.get mxC2 = some (Enc.idxW c2)) (hC3 : Γ.get mxC3 = some (Enc.idxW c3)) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (mxArm3 C) s
      (mentionsAnyGo names memo n c1 >>= fun d => mentionsAnyGo names d.2 n c2 >>= fun d1 =>
        mentionsAnyGo names d1.2 n c3 >>= fun d2 =>
        (pure (d.1 || d1.1 || d2.1, d2.2) : AM (Bool × Std.HashMap EIdx Bool)) >>= fun y =>
          pure (y.1, y.2.insert h y.1))
      (PostLb (ctxH C H) s) := by
  unfold mxArm3
  refine specR_mxCallI hc names pn ih mxK1 (vv mxC1) (vv mxM) c1 pm memo ⟨hD.1, hD.2.2.2.1, hD.2.2.2.2.1⟩
    ⟨by decide, by decide⟩ hp hrep hF hNs hNn (by simp [hC1]) (by simp [hM]) (fun rm H1 pm1 w1 hp1 hrep1 => ?_)
  obtain ⟨b1, m1⟩ := rm
  dsimp only
  refine specR_assignI mxB1 (vv mxR) (boolW b1) hD.2.2.2.2.2.2.2.1 (by simp [Env.get]) ?_
  refine specR_mxCallI hc names pn ih mxK2 (vv mxC2) (vv mxM2) c2 pm1 m1 ⟨hD.2.1, hD.2.2.2.1, hD.2.2.2.2.1⟩
    ⟨by decide, by decide⟩ (hp.trans hp1) hrep1 (by simp [Env.get, hF]) (by simp [Env.get, hNs])
    (by simp [Env.get, hNn]) (by simp [Env.get, hC2]) (by simp [Env.get]) (fun rm H2 pm2 w2 hp2 hrep2 => ?_)
  obtain ⟨b2, m2⟩ := rm
  dsimp only
  refine specR_assignI mxB2 (vv mxR) (boolW b2) hD.2.2.2.2.2.2.2.2 (by simp [Env.get]) ?_
  refine specR_mxCallI hc names pn ih mxK3 (vv mxC3) (vv mxM2) c3 pm2 m2 ⟨hD.2.2.1, hD.2.2.2.1, hD.2.2.2.2.1⟩
    ⟨by decide, by decide⟩ ((hp.trans hp1).trans hp2) hrep2 (by simp [Env.get, hF]) (by simp [Env.get, hNs])
    (by simp [Env.get, hNn]) (by simp [Env.get, hC3]) (by simp [Env.get]) (fun rm H3 pm3 w3 hp3 hrep3 => ?_)
  obtain ⟨b3, m3⟩ := rm
  dsimp only
  simp only [pure_bind]
  refine specR_assignI mxR (.op .or [.op .or [vv mxB1, vv mxB2], vv mxR]) (boolW (b1 || b2 || b3)) hD.2.2.2.1
    (by
      rw [mx_sev_or2 _ _ _ (boolW (b1 || b2)) (boolW b3)
        (by rw [mx_sev_or2 _ _ _ (boolW b1) (boolW b2) (by simp [Env.get]) (by simp [Env.get]), mx_boolW_or])
        (by simp [Env.get]), mx_boolW_or]) ?_
  exact specR_mxInsI hok h (b1 || b2 || b3) pm3 m3 ⟨hD.2.2.2.2.2.1, hD.2.2.2.2.2.2.1⟩ (by simp [Env.get, hH])
    (by simp [Env.get]) (by simp [Env.get]) hrep3 (hp1.trans (hp2.trans hp3))

theorem specR_mxArmPI {C : Ctx} (hok : CtxOK C) (hc : MxCodes C) {n : Nat} (names : List NIdx) (pn : Nat)
    (hl : names.length < 2 ^ 59) (hns : Elems C.H pn names) (ih : MxRec (σ := σ) C names pn n)
    {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (h c1 : EIdx) (sn : NIdx)
    (pm : BitVec 64) (memo : Std.HashMap EIdx Bool)
    (hD : mxK1 ∈ D ∧ mxR ∈ D ∧ mxM2 ∈ D ∧ mxN ∈ D ∧ mxO ∈ D ∧ mxQ ∈ D) (hp : C.H <+: H)
    (hrep : LbRep C H pm memo) (hF : Γ.get mxF = some (BitVec.ofNat 64 (n + 1)))
    (hNs : Γ.get mxNs = some (cellA C pn)) (hNn : Γ.get mxNn = some (BitVec.ofNat 64 names.length))
    (hH : Γ.get mxH = some (Enc.idxW h)) (hM : Γ.get mxM = some pm) (hC1 : Γ.get mxC1 = some (Enc.idxW c1))
    (hS : Γ.get mxS = some (Enc.idxW sn)) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (mxArmP C) s
      (mentionsAnyGo names memo n c1 >>= fun d =>
        (pure (names.contains sn || d.1, d.2) : AM (Bool × Std.HashMap EIdx Bool)) >>= fun y =>
          pure (y.1, y.2.insert h y.1))
      (PostLb (ctxH C H) s) := by
  unfold mxArmP
  refine specR_mxCallI hc names pn ih mxK1 (vv mxC1) (vv mxM) c1 pm memo ⟨hD.1, hD.2.1, hD.2.2.1⟩
    ⟨by decide, by decide⟩ hp hrep hF hNs hNn (by simp [hC1]) (by simp [hM]) (fun rm H1 pm1 w1 hp1 hrep1 => ?_)
  obtain ⟨b, m1⟩ := rm
  dsimp only
  simp only [pure_bind]
  refine specR_mxHasI hc names pn hl hns mxQ (vv mxS) sn hD.2.2.2.2.2 (hp.trans hp1) (by simp [Env.get, hNs])
    (by simp [Env.get, hNn]) (by simp [Env.get, hS]) (fun H2 hp2 => ?_)
  refine specR_assignI mxR (.op .or [vv mxQ, vv mxR]) (boolW (names.contains sn || b)) hD.2.1
    (by rw [mx_sev_or2 _ _ _ (boolW (names.contains sn)) (boolW b) (by simp [Env.get]) (by simp [Env.get]), mx_boolW_or])
    ?_
  exact specR_mxInsI hok h (names.contains sn || b) pm1 m1 ⟨hD.2.2.2.1, hD.2.2.2.2.1⟩ (by simp [Env.get, hH])
    (by simp [Env.get]) (by simp [Env.get]) (lbRep_mono hp2 hrep1) (hp1.trans hp2)

theorem mx_spec (C : Ctx) (hok : CtxOK C) (hc : MxCodes C) (names : List NIdx) (pn : Nat)
    (hl : names.length < 2 ^ 59) (hns : Elems C.H pn names) : ∀ n, n < 2 ^ 64 → MxRec (σ := σ) C names pn n := by
  intro n
  induction n with
  | zero =>
    intro _ h memo H s pm hp hrep
    refine specR_prologue (postLz_locals _ _) (mx_none _ _) ?_
    unfold mxCore
    rw [mentionsAnyGo]
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get, mxParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  | succ n ih =>
  intro hn h memo H s pm hp hrep
  have ih' := ih (by omega)
  refine specR_prologue (postLz_locals _ _) (mx_none _ _) ?_
  unfold mxCore
  rw [mentionsAnyGo]
  have hne := ofNat_succ_ne n (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, mxParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv mxH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]) ?_
  refine specR_viewP (C := ctxH C H) h (by simp) (by simp +decide [Env.get] <;> rfl)
    (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn hsh => ?_)
  refine specR_congr (view_bind_eq h v _ s hv) ?_
  rcases v with i | ⟨idx, ty⟩ | u | ⟨cn, cus⟩ | ⟨f, a⟩ | ⟨ty, b⟩ | ⟨ty, b⟩ | ⟨ty, v, b⟩ | l | ⟨pn', pi, sub⟩
  · -- bvar
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_mxRetI hok (.const 0) (vv mxM) false pm memo (by decide) (fun w => rfl)
      (fun w => (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv])) hrep (List.prefix_refl _)
  · -- fvar
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' mxC1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encFVar] using wordsAt_mem0 P _ _ []) ?_
    cases hmh : memo[h]? with
    | some r =>
      exact specR_mxHitI (D := ctxLocals ++ mxLocals) hok hc _ h pm memo r ⟨by decide, by decide⟩ (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]) hrep hmh
    | none =>
    refine specR_mxMissI (D := ctxLocals ++ mxLocals) hok hc _ h pm memo (by decide) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]) hrep hmh ?_
    dsimp only
    refine specR_mxArm1I (D := ctxLocals ++ mxLocals) hok hc names pn ih' h _ pm memo ⟨by decide, by decide, by decide, by decide, by decide⟩
      hp hrep ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]
  · -- sort
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_mxRetI hok (.const 0) (vv mxM) false pm memo (by decide) (fun w => rfl)
      (fun w => (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv])) hrep (List.prefix_refl _)
  · -- const
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' mxS (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW cn) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P _ _ []) ?_
    refine specR_mxHasI hc names pn hl hns mxQ (vv mxS) cn (by decide) hp (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem]) (fun H2 hp2 => ?_)
    exact specR_mxRetI hok (vv mxQ) (vv mxM) (names.contains cn) pm memo (by decide) (fun w => by simp [Env.get])
      (fun w => (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv])) (lbRep_mono hp2 hrep) hp2
  · -- app
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' mxC1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW f) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encApp] using wordsAt_mem0 P _ _ []) ?_
    refine specR_loadI' mxC2 _ (P + 8) (P + BitVec.ofNat 64 (8 * 1)) (Enc.idxW a) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encApp] using wordsAt_mem1 P _ _ [] []) ?_
    cases hmh : memo[h]? with
    | some r =>
      exact specR_mxHitI (D := ctxLocals ++ mxLocals) hok hc _ h pm memo r ⟨by decide, by decide⟩ (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]) hrep hmh
    | none =>
    refine specR_mxMissI (D := ctxLocals ++ mxLocals) hok hc _ h pm memo (by decide) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]) hrep hmh ?_
    dsimp only
    refine specR_mxArm2I (D := ctxLocals ++ mxLocals) hok hc names pn ih' h _ _ pm memo ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
      hp hrep ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]
  · -- lam
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' mxC1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P _ _ []) ?_
    refine specR_loadI' mxC2 _ (P + 8) (P + BitVec.ofNat 64 (8 * 1)) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P _ _ [] []) ?_
    cases hmh : memo[h]? with
    | some r =>
      exact specR_mxHitI (D := ctxLocals ++ mxLocals) hok hc _ h pm memo r ⟨by decide, by decide⟩ (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]) hrep hmh
    | none =>
    refine specR_mxMissI (D := ctxLocals ++ mxLocals) hok hc _ h pm memo (by decide) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]) hrep hmh ?_
    dsimp only
    refine specR_mxArm2I (D := ctxLocals ++ mxLocals) hok hc names pn ih' h _ _ pm memo ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
      hp hrep ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]
  · -- forallE
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' mxC1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P _ _ []) ?_
    refine specR_loadI' mxC2 _ (P + 8) (P + BitVec.ofNat 64 (8 * 1)) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P _ _ [] []) ?_
    cases hmh : memo[h]? with
    | some r =>
      exact specR_mxHitI (D := ctxLocals ++ mxLocals) hok hc _ h pm memo r ⟨by decide, by decide⟩ (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]) hrep hmh
    | none =>
    refine specR_mxMissI (D := ctxLocals ++ mxLocals) hok hc _ h pm memo (by decide) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]) hrep hmh ?_
    dsimp only
    refine specR_mxArm2I (D := ctxLocals ++ mxLocals) hok hc names pn ih' h _ _ pm memo ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
      hp hrep ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]
  · -- letE
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' mxC1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encLet] using wordsAt_mem0 P _ _ []) ?_
    refine specR_loadI' mxC2 _ (P + 8) (P + BitVec.ofNat 64 (8 * 1)) (Enc.idxW v) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encLet] using wordsAt_mem1 P _ _ [Enc.idxW b] []) ?_
    refine specR_loadI' mxC3 _ (P + 16) (P + BitVec.ofNat 64 (8 * 2)) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encLet] using (wordsAt_get P [Enc.idxW ty, Enc.idxW v, Enc.idxW b] 2 (by simp) [] : (P + BitVec.ofNat 64 (8 * 2), Enc.idxW b) ∈ _)) ?_
    cases hmh : memo[h]? with
    | some r =>
      exact specR_mxHitI (D := ctxLocals ++ mxLocals) hok hc _ h pm memo r ⟨by decide, by decide⟩ (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]) hrep hmh
    | none =>
    refine specR_mxMissI (D := ctxLocals ++ mxLocals) hok hc _ h pm memo (by decide) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]) hrep hmh ?_
    dsimp only
    refine specR_mxArm3I (D := ctxLocals ++ mxLocals) hok hc names pn ih' h _ _ _ pm memo ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
      hp hrep ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]
  · -- lit
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_mxRetI hok (.const 0) (vv mxM) false pm memo (by decide) (fun w => rfl)
      (fun w => (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv])) hrep (List.prefix_refl _)
  · -- proj
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' mxS (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW pn') (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encProj] using wordsAt_mem0 P _ _ []) ?_
    refine specR_loadI' mxC1 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW sub) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encProj] using wordsAt_mem1 P (Enc.idxW pn') (Enc.idxW sub) (Enc.limbs pi) []) ?_
    cases hmh : memo[h]? with
    | some r =>
      exact specR_mxHitI (D := ctxLocals ++ mxLocals) hok hc _ h pm memo r ⟨by decide, by decide⟩ (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]) hrep hmh
    | none =>
    refine specR_mxMissI (D := ctxLocals ++ mxLocals) hok hc _ h pm memo (by decide) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]) (by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]) hrep hmh ?_
    dsimp only
    refine specR_mxArmPI (D := ctxLocals ++ mxLocals) hok hc names pn hl hns ih' h _ pn' pm memo ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩
      hp hrep ?_ ?_ ?_ ?_ ?_ ?_ ?_
    all_goals simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, mxParams, ctxEnv]

end

end ConPanqueque.T.WC
