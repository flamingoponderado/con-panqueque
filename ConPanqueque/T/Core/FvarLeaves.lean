import ConPanqueque.T.Core.LeavesSub
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `fvarLeavesGo`: the reachable free-variable leaves, with a seen set

The twin threads the leaf list and the seen set through results; the port keeps both as heap memo lists
(`AccRep`, `SeenRep`) and returns a fresh pair block `[leaves, seen]`. The node is marked seen before its arm.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def flF := ofString "flv_f"
def flA := ofString "flv_a"
def flH := ofString "flv_h"
def flS := ofString "flv_s"
def flB := ofString "flv_b"
def flL := ofString "flv_l"
def flT := ofString "flv_t"
def flI := ofString "flv_i"
def flC1 := ofString "flv_c1"
def flC2 := ofString "flv_c2"
def flC3 := ofString "flv_c3"
def flA2 := ofString "flv_a2"
def flS2 := ofString "flv_s2"
def flK1 := ofString "flv_k1"
def flK2 := ofString "flv_k2"
def flK3 := ofString "flv_k3"
def flN := ofString "flv_n"
def flO := ofString "flv_o"
def flP := ofString "flv_p"
def fFl := ofString "fvarLeavesGo"

@[simp] theorem fl_flF_ne_flA : flF ≠ flA := by decide
@[simp] theorem fl_flF_ne_flH : flF ≠ flH := by decide
@[simp] theorem fl_flF_ne_flS : flF ≠ flS := by decide
@[simp] theorem fl_flF_ne_flB : flF ≠ flB := by decide
@[simp] theorem fl_flF_ne_flL : flF ≠ flL := by decide
@[simp] theorem fl_flF_ne_flT : flF ≠ flT := by decide
@[simp] theorem fl_flF_ne_flI : flF ≠ flI := by decide
@[simp] theorem fl_flF_ne_flC1 : flF ≠ flC1 := by decide
@[simp] theorem fl_flF_ne_flC2 : flF ≠ flC2 := by decide
@[simp] theorem fl_flF_ne_flC3 : flF ≠ flC3 := by decide
@[simp] theorem fl_flF_ne_flA2 : flF ≠ flA2 := by decide
@[simp] theorem fl_flF_ne_flS2 : flF ≠ flS2 := by decide
@[simp] theorem fl_flF_ne_flK1 : flF ≠ flK1 := by decide
@[simp] theorem fl_flF_ne_flK2 : flF ≠ flK2 := by decide
@[simp] theorem fl_flF_ne_flK3 : flF ≠ flK3 := by decide
@[simp] theorem fl_flF_ne_flN : flF ≠ flN := by decide
@[simp] theorem fl_flF_ne_flO : flF ≠ flO := by decide
@[simp] theorem fl_flF_ne_flP : flF ≠ flP := by decide
@[simp] theorem fl_flF_ne_lKb : flF ≠ lKb := by decide
@[simp] theorem fl_flF_ne_lFl : flF ≠ lFl := by decide
@[simp] theorem fl_flF_ne_lDh : flF ≠ lDh := by decide
@[simp] theorem fl_flF_ne_lDt : flF ≠ lDt := by decide
@[simp] theorem fl_flF_ne_lDg : flF ≠ lDg := by decide
@[simp] theorem fl_flF_ne_lDi : flF ≠ lDi := by decide
@[simp] theorem fl_flF_ne_lDo1 : flF ≠ lDo1 := by decide
@[simp] theorem fl_flF_ne_lDo2 : flF ≠ lDo2 := by decide
@[simp] theorem fl_flF_ne_lRp : flF ≠ lRp := by decide
@[simp] theorem fl_flF_ne_lRn : flF ≠ lRn := by decide
@[simp] theorem fl_flF_ne_lFle : flF ≠ lFle := by decide
@[simp] theorem fl_flF_ne_lDir : flF ≠ lDir := by decide
@[simp] theorem fl_flA_ne_flF : flA ≠ flF := by decide
@[simp] theorem fl_flA_ne_flH : flA ≠ flH := by decide
@[simp] theorem fl_flA_ne_flS : flA ≠ flS := by decide
@[simp] theorem fl_flA_ne_flB : flA ≠ flB := by decide
@[simp] theorem fl_flA_ne_flL : flA ≠ flL := by decide
@[simp] theorem fl_flA_ne_flT : flA ≠ flT := by decide
@[simp] theorem fl_flA_ne_flI : flA ≠ flI := by decide
@[simp] theorem fl_flA_ne_flC1 : flA ≠ flC1 := by decide
@[simp] theorem fl_flA_ne_flC2 : flA ≠ flC2 := by decide
@[simp] theorem fl_flA_ne_flC3 : flA ≠ flC3 := by decide
@[simp] theorem fl_flA_ne_flA2 : flA ≠ flA2 := by decide
@[simp] theorem fl_flA_ne_flS2 : flA ≠ flS2 := by decide
@[simp] theorem fl_flA_ne_flK1 : flA ≠ flK1 := by decide
@[simp] theorem fl_flA_ne_flK2 : flA ≠ flK2 := by decide
@[simp] theorem fl_flA_ne_flK3 : flA ≠ flK3 := by decide
@[simp] theorem fl_flA_ne_flN : flA ≠ flN := by decide
@[simp] theorem fl_flA_ne_flO : flA ≠ flO := by decide
@[simp] theorem fl_flA_ne_flP : flA ≠ flP := by decide
@[simp] theorem fl_flA_ne_lKb : flA ≠ lKb := by decide
@[simp] theorem fl_flA_ne_lFl : flA ≠ lFl := by decide
@[simp] theorem fl_flA_ne_lDh : flA ≠ lDh := by decide
@[simp] theorem fl_flA_ne_lDt : flA ≠ lDt := by decide
@[simp] theorem fl_flA_ne_lDg : flA ≠ lDg := by decide
@[simp] theorem fl_flA_ne_lDi : flA ≠ lDi := by decide
@[simp] theorem fl_flA_ne_lDo1 : flA ≠ lDo1 := by decide
@[simp] theorem fl_flA_ne_lDo2 : flA ≠ lDo2 := by decide
@[simp] theorem fl_flA_ne_lRp : flA ≠ lRp := by decide
@[simp] theorem fl_flA_ne_lRn : flA ≠ lRn := by decide
@[simp] theorem fl_flA_ne_lFle : flA ≠ lFle := by decide
@[simp] theorem fl_flA_ne_lDir : flA ≠ lDir := by decide
@[simp] theorem fl_flH_ne_flF : flH ≠ flF := by decide
@[simp] theorem fl_flH_ne_flA : flH ≠ flA := by decide
@[simp] theorem fl_flH_ne_flS : flH ≠ flS := by decide
@[simp] theorem fl_flH_ne_flB : flH ≠ flB := by decide
@[simp] theorem fl_flH_ne_flL : flH ≠ flL := by decide
@[simp] theorem fl_flH_ne_flT : flH ≠ flT := by decide
@[simp] theorem fl_flH_ne_flI : flH ≠ flI := by decide
@[simp] theorem fl_flH_ne_flC1 : flH ≠ flC1 := by decide
@[simp] theorem fl_flH_ne_flC2 : flH ≠ flC2 := by decide
@[simp] theorem fl_flH_ne_flC3 : flH ≠ flC3 := by decide
@[simp] theorem fl_flH_ne_flA2 : flH ≠ flA2 := by decide
@[simp] theorem fl_flH_ne_flS2 : flH ≠ flS2 := by decide
@[simp] theorem fl_flH_ne_flK1 : flH ≠ flK1 := by decide
@[simp] theorem fl_flH_ne_flK2 : flH ≠ flK2 := by decide
@[simp] theorem fl_flH_ne_flK3 : flH ≠ flK3 := by decide
@[simp] theorem fl_flH_ne_flN : flH ≠ flN := by decide
@[simp] theorem fl_flH_ne_flO : flH ≠ flO := by decide
@[simp] theorem fl_flH_ne_flP : flH ≠ flP := by decide
@[simp] theorem fl_flH_ne_lKb : flH ≠ lKb := by decide
@[simp] theorem fl_flH_ne_lFl : flH ≠ lFl := by decide
@[simp] theorem fl_flH_ne_lDh : flH ≠ lDh := by decide
@[simp] theorem fl_flH_ne_lDt : flH ≠ lDt := by decide
@[simp] theorem fl_flH_ne_lDg : flH ≠ lDg := by decide
@[simp] theorem fl_flH_ne_lDi : flH ≠ lDi := by decide
@[simp] theorem fl_flH_ne_lDo1 : flH ≠ lDo1 := by decide
@[simp] theorem fl_flH_ne_lDo2 : flH ≠ lDo2 := by decide
@[simp] theorem fl_flH_ne_lRp : flH ≠ lRp := by decide
@[simp] theorem fl_flH_ne_lRn : flH ≠ lRn := by decide
@[simp] theorem fl_flH_ne_lFle : flH ≠ lFle := by decide
@[simp] theorem fl_flH_ne_lDir : flH ≠ lDir := by decide
@[simp] theorem fl_flS_ne_flF : flS ≠ flF := by decide
@[simp] theorem fl_flS_ne_flA : flS ≠ flA := by decide
@[simp] theorem fl_flS_ne_flH : flS ≠ flH := by decide
@[simp] theorem fl_flS_ne_flB : flS ≠ flB := by decide
@[simp] theorem fl_flS_ne_flL : flS ≠ flL := by decide
@[simp] theorem fl_flS_ne_flT : flS ≠ flT := by decide
@[simp] theorem fl_flS_ne_flI : flS ≠ flI := by decide
@[simp] theorem fl_flS_ne_flC1 : flS ≠ flC1 := by decide
@[simp] theorem fl_flS_ne_flC2 : flS ≠ flC2 := by decide
@[simp] theorem fl_flS_ne_flC3 : flS ≠ flC3 := by decide
@[simp] theorem fl_flS_ne_flA2 : flS ≠ flA2 := by decide
@[simp] theorem fl_flS_ne_flS2 : flS ≠ flS2 := by decide
@[simp] theorem fl_flS_ne_flK1 : flS ≠ flK1 := by decide
@[simp] theorem fl_flS_ne_flK2 : flS ≠ flK2 := by decide
@[simp] theorem fl_flS_ne_flK3 : flS ≠ flK3 := by decide
@[simp] theorem fl_flS_ne_flN : flS ≠ flN := by decide
@[simp] theorem fl_flS_ne_flO : flS ≠ flO := by decide
@[simp] theorem fl_flS_ne_flP : flS ≠ flP := by decide
@[simp] theorem fl_flS_ne_lKb : flS ≠ lKb := by decide
@[simp] theorem fl_flS_ne_lFl : flS ≠ lFl := by decide
@[simp] theorem fl_flS_ne_lDh : flS ≠ lDh := by decide
@[simp] theorem fl_flS_ne_lDt : flS ≠ lDt := by decide
@[simp] theorem fl_flS_ne_lDg : flS ≠ lDg := by decide
@[simp] theorem fl_flS_ne_lDi : flS ≠ lDi := by decide
@[simp] theorem fl_flS_ne_lDo1 : flS ≠ lDo1 := by decide
@[simp] theorem fl_flS_ne_lDo2 : flS ≠ lDo2 := by decide
@[simp] theorem fl_flS_ne_lRp : flS ≠ lRp := by decide
@[simp] theorem fl_flS_ne_lRn : flS ≠ lRn := by decide
@[simp] theorem fl_flS_ne_lFle : flS ≠ lFle := by decide
@[simp] theorem fl_flS_ne_lDir : flS ≠ lDir := by decide
@[simp] theorem fl_flB_ne_flF : flB ≠ flF := by decide
@[simp] theorem fl_flB_ne_flA : flB ≠ flA := by decide
@[simp] theorem fl_flB_ne_flH : flB ≠ flH := by decide
@[simp] theorem fl_flB_ne_flS : flB ≠ flS := by decide
@[simp] theorem fl_flB_ne_flL : flB ≠ flL := by decide
@[simp] theorem fl_flB_ne_flT : flB ≠ flT := by decide
@[simp] theorem fl_flB_ne_flI : flB ≠ flI := by decide
@[simp] theorem fl_flB_ne_flC1 : flB ≠ flC1 := by decide
@[simp] theorem fl_flB_ne_flC2 : flB ≠ flC2 := by decide
@[simp] theorem fl_flB_ne_flC3 : flB ≠ flC3 := by decide
@[simp] theorem fl_flB_ne_flA2 : flB ≠ flA2 := by decide
@[simp] theorem fl_flB_ne_flS2 : flB ≠ flS2 := by decide
@[simp] theorem fl_flB_ne_flK1 : flB ≠ flK1 := by decide
@[simp] theorem fl_flB_ne_flK2 : flB ≠ flK2 := by decide
@[simp] theorem fl_flB_ne_flK3 : flB ≠ flK3 := by decide
@[simp] theorem fl_flB_ne_flN : flB ≠ flN := by decide
@[simp] theorem fl_flB_ne_flO : flB ≠ flO := by decide
@[simp] theorem fl_flB_ne_flP : flB ≠ flP := by decide
@[simp] theorem fl_flB_ne_lKb : flB ≠ lKb := by decide
@[simp] theorem fl_flB_ne_lFl : flB ≠ lFl := by decide
@[simp] theorem fl_flB_ne_lDh : flB ≠ lDh := by decide
@[simp] theorem fl_flB_ne_lDt : flB ≠ lDt := by decide
@[simp] theorem fl_flB_ne_lDg : flB ≠ lDg := by decide
@[simp] theorem fl_flB_ne_lDi : flB ≠ lDi := by decide
@[simp] theorem fl_flB_ne_lDo1 : flB ≠ lDo1 := by decide
@[simp] theorem fl_flB_ne_lDo2 : flB ≠ lDo2 := by decide
@[simp] theorem fl_flB_ne_lRp : flB ≠ lRp := by decide
@[simp] theorem fl_flB_ne_lRn : flB ≠ lRn := by decide
@[simp] theorem fl_flB_ne_lFle : flB ≠ lFle := by decide
@[simp] theorem fl_flB_ne_lDir : flB ≠ lDir := by decide
@[simp] theorem fl_flL_ne_flF : flL ≠ flF := by decide
@[simp] theorem fl_flL_ne_flA : flL ≠ flA := by decide
@[simp] theorem fl_flL_ne_flH : flL ≠ flH := by decide
@[simp] theorem fl_flL_ne_flS : flL ≠ flS := by decide
@[simp] theorem fl_flL_ne_flB : flL ≠ flB := by decide
@[simp] theorem fl_flL_ne_flT : flL ≠ flT := by decide
@[simp] theorem fl_flL_ne_flI : flL ≠ flI := by decide
@[simp] theorem fl_flL_ne_flC1 : flL ≠ flC1 := by decide
@[simp] theorem fl_flL_ne_flC2 : flL ≠ flC2 := by decide
@[simp] theorem fl_flL_ne_flC3 : flL ≠ flC3 := by decide
@[simp] theorem fl_flL_ne_flA2 : flL ≠ flA2 := by decide
@[simp] theorem fl_flL_ne_flS2 : flL ≠ flS2 := by decide
@[simp] theorem fl_flL_ne_flK1 : flL ≠ flK1 := by decide
@[simp] theorem fl_flL_ne_flK2 : flL ≠ flK2 := by decide
@[simp] theorem fl_flL_ne_flK3 : flL ≠ flK3 := by decide
@[simp] theorem fl_flL_ne_flN : flL ≠ flN := by decide
@[simp] theorem fl_flL_ne_flO : flL ≠ flO := by decide
@[simp] theorem fl_flL_ne_flP : flL ≠ flP := by decide
@[simp] theorem fl_flL_ne_lKb : flL ≠ lKb := by decide
@[simp] theorem fl_flL_ne_lFl : flL ≠ lFl := by decide
@[simp] theorem fl_flL_ne_lDh : flL ≠ lDh := by decide
@[simp] theorem fl_flL_ne_lDt : flL ≠ lDt := by decide
@[simp] theorem fl_flL_ne_lDg : flL ≠ lDg := by decide
@[simp] theorem fl_flL_ne_lDi : flL ≠ lDi := by decide
@[simp] theorem fl_flL_ne_lDo1 : flL ≠ lDo1 := by decide
@[simp] theorem fl_flL_ne_lDo2 : flL ≠ lDo2 := by decide
@[simp] theorem fl_flL_ne_lRp : flL ≠ lRp := by decide
@[simp] theorem fl_flL_ne_lRn : flL ≠ lRn := by decide
@[simp] theorem fl_flL_ne_lFle : flL ≠ lFle := by decide
@[simp] theorem fl_flL_ne_lDir : flL ≠ lDir := by decide
@[simp] theorem fl_flT_ne_flF : flT ≠ flF := by decide
@[simp] theorem fl_flT_ne_flA : flT ≠ flA := by decide
@[simp] theorem fl_flT_ne_flH : flT ≠ flH := by decide
@[simp] theorem fl_flT_ne_flS : flT ≠ flS := by decide
@[simp] theorem fl_flT_ne_flB : flT ≠ flB := by decide
@[simp] theorem fl_flT_ne_flL : flT ≠ flL := by decide
@[simp] theorem fl_flT_ne_flI : flT ≠ flI := by decide
@[simp] theorem fl_flT_ne_flC1 : flT ≠ flC1 := by decide
@[simp] theorem fl_flT_ne_flC2 : flT ≠ flC2 := by decide
@[simp] theorem fl_flT_ne_flC3 : flT ≠ flC3 := by decide
@[simp] theorem fl_flT_ne_flA2 : flT ≠ flA2 := by decide
@[simp] theorem fl_flT_ne_flS2 : flT ≠ flS2 := by decide
@[simp] theorem fl_flT_ne_flK1 : flT ≠ flK1 := by decide
@[simp] theorem fl_flT_ne_flK2 : flT ≠ flK2 := by decide
@[simp] theorem fl_flT_ne_flK3 : flT ≠ flK3 := by decide
@[simp] theorem fl_flT_ne_flN : flT ≠ flN := by decide
@[simp] theorem fl_flT_ne_flO : flT ≠ flO := by decide
@[simp] theorem fl_flT_ne_flP : flT ≠ flP := by decide
@[simp] theorem fl_flT_ne_lKb : flT ≠ lKb := by decide
@[simp] theorem fl_flT_ne_lFl : flT ≠ lFl := by decide
@[simp] theorem fl_flT_ne_lDh : flT ≠ lDh := by decide
@[simp] theorem fl_flT_ne_lDt : flT ≠ lDt := by decide
@[simp] theorem fl_flT_ne_lDg : flT ≠ lDg := by decide
@[simp] theorem fl_flT_ne_lDi : flT ≠ lDi := by decide
@[simp] theorem fl_flT_ne_lDo1 : flT ≠ lDo1 := by decide
@[simp] theorem fl_flT_ne_lDo2 : flT ≠ lDo2 := by decide
@[simp] theorem fl_flT_ne_lRp : flT ≠ lRp := by decide
@[simp] theorem fl_flT_ne_lRn : flT ≠ lRn := by decide
@[simp] theorem fl_flT_ne_lFle : flT ≠ lFle := by decide
@[simp] theorem fl_flT_ne_lDir : flT ≠ lDir := by decide
@[simp] theorem fl_flI_ne_flF : flI ≠ flF := by decide
@[simp] theorem fl_flI_ne_flA : flI ≠ flA := by decide
@[simp] theorem fl_flI_ne_flH : flI ≠ flH := by decide
@[simp] theorem fl_flI_ne_flS : flI ≠ flS := by decide
@[simp] theorem fl_flI_ne_flB : flI ≠ flB := by decide
@[simp] theorem fl_flI_ne_flL : flI ≠ flL := by decide
@[simp] theorem fl_flI_ne_flT : flI ≠ flT := by decide
@[simp] theorem fl_flI_ne_flC1 : flI ≠ flC1 := by decide
@[simp] theorem fl_flI_ne_flC2 : flI ≠ flC2 := by decide
@[simp] theorem fl_flI_ne_flC3 : flI ≠ flC3 := by decide
@[simp] theorem fl_flI_ne_flA2 : flI ≠ flA2 := by decide
@[simp] theorem fl_flI_ne_flS2 : flI ≠ flS2 := by decide
@[simp] theorem fl_flI_ne_flK1 : flI ≠ flK1 := by decide
@[simp] theorem fl_flI_ne_flK2 : flI ≠ flK2 := by decide
@[simp] theorem fl_flI_ne_flK3 : flI ≠ flK3 := by decide
@[simp] theorem fl_flI_ne_flN : flI ≠ flN := by decide
@[simp] theorem fl_flI_ne_flO : flI ≠ flO := by decide
@[simp] theorem fl_flI_ne_flP : flI ≠ flP := by decide
@[simp] theorem fl_flI_ne_lKb : flI ≠ lKb := by decide
@[simp] theorem fl_flI_ne_lFl : flI ≠ lFl := by decide
@[simp] theorem fl_flI_ne_lDh : flI ≠ lDh := by decide
@[simp] theorem fl_flI_ne_lDt : flI ≠ lDt := by decide
@[simp] theorem fl_flI_ne_lDg : flI ≠ lDg := by decide
@[simp] theorem fl_flI_ne_lDi : flI ≠ lDi := by decide
@[simp] theorem fl_flI_ne_lDo1 : flI ≠ lDo1 := by decide
@[simp] theorem fl_flI_ne_lDo2 : flI ≠ lDo2 := by decide
@[simp] theorem fl_flI_ne_lRp : flI ≠ lRp := by decide
@[simp] theorem fl_flI_ne_lRn : flI ≠ lRn := by decide
@[simp] theorem fl_flI_ne_lFle : flI ≠ lFle := by decide
@[simp] theorem fl_flI_ne_lDir : flI ≠ lDir := by decide
@[simp] theorem fl_flC1_ne_flF : flC1 ≠ flF := by decide
@[simp] theorem fl_flC1_ne_flA : flC1 ≠ flA := by decide
@[simp] theorem fl_flC1_ne_flH : flC1 ≠ flH := by decide
@[simp] theorem fl_flC1_ne_flS : flC1 ≠ flS := by decide
@[simp] theorem fl_flC1_ne_flB : flC1 ≠ flB := by decide
@[simp] theorem fl_flC1_ne_flL : flC1 ≠ flL := by decide
@[simp] theorem fl_flC1_ne_flT : flC1 ≠ flT := by decide
@[simp] theorem fl_flC1_ne_flI : flC1 ≠ flI := by decide
@[simp] theorem fl_flC1_ne_flC2 : flC1 ≠ flC2 := by decide
@[simp] theorem fl_flC1_ne_flC3 : flC1 ≠ flC3 := by decide
@[simp] theorem fl_flC1_ne_flA2 : flC1 ≠ flA2 := by decide
@[simp] theorem fl_flC1_ne_flS2 : flC1 ≠ flS2 := by decide
@[simp] theorem fl_flC1_ne_flK1 : flC1 ≠ flK1 := by decide
@[simp] theorem fl_flC1_ne_flK2 : flC1 ≠ flK2 := by decide
@[simp] theorem fl_flC1_ne_flK3 : flC1 ≠ flK3 := by decide
@[simp] theorem fl_flC1_ne_flN : flC1 ≠ flN := by decide
@[simp] theorem fl_flC1_ne_flO : flC1 ≠ flO := by decide
@[simp] theorem fl_flC1_ne_flP : flC1 ≠ flP := by decide
@[simp] theorem fl_flC1_ne_lKb : flC1 ≠ lKb := by decide
@[simp] theorem fl_flC1_ne_lFl : flC1 ≠ lFl := by decide
@[simp] theorem fl_flC1_ne_lDh : flC1 ≠ lDh := by decide
@[simp] theorem fl_flC1_ne_lDt : flC1 ≠ lDt := by decide
@[simp] theorem fl_flC1_ne_lDg : flC1 ≠ lDg := by decide
@[simp] theorem fl_flC1_ne_lDi : flC1 ≠ lDi := by decide
@[simp] theorem fl_flC1_ne_lDo1 : flC1 ≠ lDo1 := by decide
@[simp] theorem fl_flC1_ne_lDo2 : flC1 ≠ lDo2 := by decide
@[simp] theorem fl_flC1_ne_lRp : flC1 ≠ lRp := by decide
@[simp] theorem fl_flC1_ne_lRn : flC1 ≠ lRn := by decide
@[simp] theorem fl_flC1_ne_lFle : flC1 ≠ lFle := by decide
@[simp] theorem fl_flC1_ne_lDir : flC1 ≠ lDir := by decide
@[simp] theorem fl_flC2_ne_flF : flC2 ≠ flF := by decide
@[simp] theorem fl_flC2_ne_flA : flC2 ≠ flA := by decide
@[simp] theorem fl_flC2_ne_flH : flC2 ≠ flH := by decide
@[simp] theorem fl_flC2_ne_flS : flC2 ≠ flS := by decide
@[simp] theorem fl_flC2_ne_flB : flC2 ≠ flB := by decide
@[simp] theorem fl_flC2_ne_flL : flC2 ≠ flL := by decide
@[simp] theorem fl_flC2_ne_flT : flC2 ≠ flT := by decide
@[simp] theorem fl_flC2_ne_flI : flC2 ≠ flI := by decide
@[simp] theorem fl_flC2_ne_flC1 : flC2 ≠ flC1 := by decide
@[simp] theorem fl_flC2_ne_flC3 : flC2 ≠ flC3 := by decide
@[simp] theorem fl_flC2_ne_flA2 : flC2 ≠ flA2 := by decide
@[simp] theorem fl_flC2_ne_flS2 : flC2 ≠ flS2 := by decide
@[simp] theorem fl_flC2_ne_flK1 : flC2 ≠ flK1 := by decide
@[simp] theorem fl_flC2_ne_flK2 : flC2 ≠ flK2 := by decide
@[simp] theorem fl_flC2_ne_flK3 : flC2 ≠ flK3 := by decide
@[simp] theorem fl_flC2_ne_flN : flC2 ≠ flN := by decide
@[simp] theorem fl_flC2_ne_flO : flC2 ≠ flO := by decide
@[simp] theorem fl_flC2_ne_flP : flC2 ≠ flP := by decide
@[simp] theorem fl_flC2_ne_lKb : flC2 ≠ lKb := by decide
@[simp] theorem fl_flC2_ne_lFl : flC2 ≠ lFl := by decide
@[simp] theorem fl_flC2_ne_lDh : flC2 ≠ lDh := by decide
@[simp] theorem fl_flC2_ne_lDt : flC2 ≠ lDt := by decide
@[simp] theorem fl_flC2_ne_lDg : flC2 ≠ lDg := by decide
@[simp] theorem fl_flC2_ne_lDi : flC2 ≠ lDi := by decide
@[simp] theorem fl_flC2_ne_lDo1 : flC2 ≠ lDo1 := by decide
@[simp] theorem fl_flC2_ne_lDo2 : flC2 ≠ lDo2 := by decide
@[simp] theorem fl_flC2_ne_lRp : flC2 ≠ lRp := by decide
@[simp] theorem fl_flC2_ne_lRn : flC2 ≠ lRn := by decide
@[simp] theorem fl_flC2_ne_lFle : flC2 ≠ lFle := by decide
@[simp] theorem fl_flC2_ne_lDir : flC2 ≠ lDir := by decide
@[simp] theorem fl_flC3_ne_flF : flC3 ≠ flF := by decide
@[simp] theorem fl_flC3_ne_flA : flC3 ≠ flA := by decide
@[simp] theorem fl_flC3_ne_flH : flC3 ≠ flH := by decide
@[simp] theorem fl_flC3_ne_flS : flC3 ≠ flS := by decide
@[simp] theorem fl_flC3_ne_flB : flC3 ≠ flB := by decide
@[simp] theorem fl_flC3_ne_flL : flC3 ≠ flL := by decide
@[simp] theorem fl_flC3_ne_flT : flC3 ≠ flT := by decide
@[simp] theorem fl_flC3_ne_flI : flC3 ≠ flI := by decide
@[simp] theorem fl_flC3_ne_flC1 : flC3 ≠ flC1 := by decide
@[simp] theorem fl_flC3_ne_flC2 : flC3 ≠ flC2 := by decide
@[simp] theorem fl_flC3_ne_flA2 : flC3 ≠ flA2 := by decide
@[simp] theorem fl_flC3_ne_flS2 : flC3 ≠ flS2 := by decide
@[simp] theorem fl_flC3_ne_flK1 : flC3 ≠ flK1 := by decide
@[simp] theorem fl_flC3_ne_flK2 : flC3 ≠ flK2 := by decide
@[simp] theorem fl_flC3_ne_flK3 : flC3 ≠ flK3 := by decide
@[simp] theorem fl_flC3_ne_flN : flC3 ≠ flN := by decide
@[simp] theorem fl_flC3_ne_flO : flC3 ≠ flO := by decide
@[simp] theorem fl_flC3_ne_flP : flC3 ≠ flP := by decide
@[simp] theorem fl_flC3_ne_lKb : flC3 ≠ lKb := by decide
@[simp] theorem fl_flC3_ne_lFl : flC3 ≠ lFl := by decide
@[simp] theorem fl_flC3_ne_lDh : flC3 ≠ lDh := by decide
@[simp] theorem fl_flC3_ne_lDt : flC3 ≠ lDt := by decide
@[simp] theorem fl_flC3_ne_lDg : flC3 ≠ lDg := by decide
@[simp] theorem fl_flC3_ne_lDi : flC3 ≠ lDi := by decide
@[simp] theorem fl_flC3_ne_lDo1 : flC3 ≠ lDo1 := by decide
@[simp] theorem fl_flC3_ne_lDo2 : flC3 ≠ lDo2 := by decide
@[simp] theorem fl_flC3_ne_lRp : flC3 ≠ lRp := by decide
@[simp] theorem fl_flC3_ne_lRn : flC3 ≠ lRn := by decide
@[simp] theorem fl_flC3_ne_lFle : flC3 ≠ lFle := by decide
@[simp] theorem fl_flC3_ne_lDir : flC3 ≠ lDir := by decide
@[simp] theorem fl_flA2_ne_flF : flA2 ≠ flF := by decide
@[simp] theorem fl_flA2_ne_flA : flA2 ≠ flA := by decide
@[simp] theorem fl_flA2_ne_flH : flA2 ≠ flH := by decide
@[simp] theorem fl_flA2_ne_flS : flA2 ≠ flS := by decide
@[simp] theorem fl_flA2_ne_flB : flA2 ≠ flB := by decide
@[simp] theorem fl_flA2_ne_flL : flA2 ≠ flL := by decide
@[simp] theorem fl_flA2_ne_flT : flA2 ≠ flT := by decide
@[simp] theorem fl_flA2_ne_flI : flA2 ≠ flI := by decide
@[simp] theorem fl_flA2_ne_flC1 : flA2 ≠ flC1 := by decide
@[simp] theorem fl_flA2_ne_flC2 : flA2 ≠ flC2 := by decide
@[simp] theorem fl_flA2_ne_flC3 : flA2 ≠ flC3 := by decide
@[simp] theorem fl_flA2_ne_flS2 : flA2 ≠ flS2 := by decide
@[simp] theorem fl_flA2_ne_flK1 : flA2 ≠ flK1 := by decide
@[simp] theorem fl_flA2_ne_flK2 : flA2 ≠ flK2 := by decide
@[simp] theorem fl_flA2_ne_flK3 : flA2 ≠ flK3 := by decide
@[simp] theorem fl_flA2_ne_flN : flA2 ≠ flN := by decide
@[simp] theorem fl_flA2_ne_flO : flA2 ≠ flO := by decide
@[simp] theorem fl_flA2_ne_flP : flA2 ≠ flP := by decide
@[simp] theorem fl_flA2_ne_lKb : flA2 ≠ lKb := by decide
@[simp] theorem fl_flA2_ne_lFl : flA2 ≠ lFl := by decide
@[simp] theorem fl_flA2_ne_lDh : flA2 ≠ lDh := by decide
@[simp] theorem fl_flA2_ne_lDt : flA2 ≠ lDt := by decide
@[simp] theorem fl_flA2_ne_lDg : flA2 ≠ lDg := by decide
@[simp] theorem fl_flA2_ne_lDi : flA2 ≠ lDi := by decide
@[simp] theorem fl_flA2_ne_lDo1 : flA2 ≠ lDo1 := by decide
@[simp] theorem fl_flA2_ne_lDo2 : flA2 ≠ lDo2 := by decide
@[simp] theorem fl_flA2_ne_lRp : flA2 ≠ lRp := by decide
@[simp] theorem fl_flA2_ne_lRn : flA2 ≠ lRn := by decide
@[simp] theorem fl_flA2_ne_lFle : flA2 ≠ lFle := by decide
@[simp] theorem fl_flA2_ne_lDir : flA2 ≠ lDir := by decide
@[simp] theorem fl_flS2_ne_flF : flS2 ≠ flF := by decide
@[simp] theorem fl_flS2_ne_flA : flS2 ≠ flA := by decide
@[simp] theorem fl_flS2_ne_flH : flS2 ≠ flH := by decide
@[simp] theorem fl_flS2_ne_flS : flS2 ≠ flS := by decide
@[simp] theorem fl_flS2_ne_flB : flS2 ≠ flB := by decide
@[simp] theorem fl_flS2_ne_flL : flS2 ≠ flL := by decide
@[simp] theorem fl_flS2_ne_flT : flS2 ≠ flT := by decide
@[simp] theorem fl_flS2_ne_flI : flS2 ≠ flI := by decide
@[simp] theorem fl_flS2_ne_flC1 : flS2 ≠ flC1 := by decide
@[simp] theorem fl_flS2_ne_flC2 : flS2 ≠ flC2 := by decide
@[simp] theorem fl_flS2_ne_flC3 : flS2 ≠ flC3 := by decide
@[simp] theorem fl_flS2_ne_flA2 : flS2 ≠ flA2 := by decide
@[simp] theorem fl_flS2_ne_flK1 : flS2 ≠ flK1 := by decide
@[simp] theorem fl_flS2_ne_flK2 : flS2 ≠ flK2 := by decide
@[simp] theorem fl_flS2_ne_flK3 : flS2 ≠ flK3 := by decide
@[simp] theorem fl_flS2_ne_flN : flS2 ≠ flN := by decide
@[simp] theorem fl_flS2_ne_flO : flS2 ≠ flO := by decide
@[simp] theorem fl_flS2_ne_flP : flS2 ≠ flP := by decide
@[simp] theorem fl_flS2_ne_lKb : flS2 ≠ lKb := by decide
@[simp] theorem fl_flS2_ne_lFl : flS2 ≠ lFl := by decide
@[simp] theorem fl_flS2_ne_lDh : flS2 ≠ lDh := by decide
@[simp] theorem fl_flS2_ne_lDt : flS2 ≠ lDt := by decide
@[simp] theorem fl_flS2_ne_lDg : flS2 ≠ lDg := by decide
@[simp] theorem fl_flS2_ne_lDi : flS2 ≠ lDi := by decide
@[simp] theorem fl_flS2_ne_lDo1 : flS2 ≠ lDo1 := by decide
@[simp] theorem fl_flS2_ne_lDo2 : flS2 ≠ lDo2 := by decide
@[simp] theorem fl_flS2_ne_lRp : flS2 ≠ lRp := by decide
@[simp] theorem fl_flS2_ne_lRn : flS2 ≠ lRn := by decide
@[simp] theorem fl_flS2_ne_lFle : flS2 ≠ lFle := by decide
@[simp] theorem fl_flS2_ne_lDir : flS2 ≠ lDir := by decide
@[simp] theorem fl_flK1_ne_flF : flK1 ≠ flF := by decide
@[simp] theorem fl_flK1_ne_flA : flK1 ≠ flA := by decide
@[simp] theorem fl_flK1_ne_flH : flK1 ≠ flH := by decide
@[simp] theorem fl_flK1_ne_flS : flK1 ≠ flS := by decide
@[simp] theorem fl_flK1_ne_flB : flK1 ≠ flB := by decide
@[simp] theorem fl_flK1_ne_flL : flK1 ≠ flL := by decide
@[simp] theorem fl_flK1_ne_flT : flK1 ≠ flT := by decide
@[simp] theorem fl_flK1_ne_flI : flK1 ≠ flI := by decide
@[simp] theorem fl_flK1_ne_flC1 : flK1 ≠ flC1 := by decide
@[simp] theorem fl_flK1_ne_flC2 : flK1 ≠ flC2 := by decide
@[simp] theorem fl_flK1_ne_flC3 : flK1 ≠ flC3 := by decide
@[simp] theorem fl_flK1_ne_flA2 : flK1 ≠ flA2 := by decide
@[simp] theorem fl_flK1_ne_flS2 : flK1 ≠ flS2 := by decide
@[simp] theorem fl_flK1_ne_flK2 : flK1 ≠ flK2 := by decide
@[simp] theorem fl_flK1_ne_flK3 : flK1 ≠ flK3 := by decide
@[simp] theorem fl_flK1_ne_flN : flK1 ≠ flN := by decide
@[simp] theorem fl_flK1_ne_flO : flK1 ≠ flO := by decide
@[simp] theorem fl_flK1_ne_flP : flK1 ≠ flP := by decide
@[simp] theorem fl_flK1_ne_lKb : flK1 ≠ lKb := by decide
@[simp] theorem fl_flK1_ne_lFl : flK1 ≠ lFl := by decide
@[simp] theorem fl_flK1_ne_lDh : flK1 ≠ lDh := by decide
@[simp] theorem fl_flK1_ne_lDt : flK1 ≠ lDt := by decide
@[simp] theorem fl_flK1_ne_lDg : flK1 ≠ lDg := by decide
@[simp] theorem fl_flK1_ne_lDi : flK1 ≠ lDi := by decide
@[simp] theorem fl_flK1_ne_lDo1 : flK1 ≠ lDo1 := by decide
@[simp] theorem fl_flK1_ne_lDo2 : flK1 ≠ lDo2 := by decide
@[simp] theorem fl_flK1_ne_lRp : flK1 ≠ lRp := by decide
@[simp] theorem fl_flK1_ne_lRn : flK1 ≠ lRn := by decide
@[simp] theorem fl_flK1_ne_lFle : flK1 ≠ lFle := by decide
@[simp] theorem fl_flK1_ne_lDir : flK1 ≠ lDir := by decide
@[simp] theorem fl_flK2_ne_flF : flK2 ≠ flF := by decide
@[simp] theorem fl_flK2_ne_flA : flK2 ≠ flA := by decide
@[simp] theorem fl_flK2_ne_flH : flK2 ≠ flH := by decide
@[simp] theorem fl_flK2_ne_flS : flK2 ≠ flS := by decide
@[simp] theorem fl_flK2_ne_flB : flK2 ≠ flB := by decide
@[simp] theorem fl_flK2_ne_flL : flK2 ≠ flL := by decide
@[simp] theorem fl_flK2_ne_flT : flK2 ≠ flT := by decide
@[simp] theorem fl_flK2_ne_flI : flK2 ≠ flI := by decide
@[simp] theorem fl_flK2_ne_flC1 : flK2 ≠ flC1 := by decide
@[simp] theorem fl_flK2_ne_flC2 : flK2 ≠ flC2 := by decide
@[simp] theorem fl_flK2_ne_flC3 : flK2 ≠ flC3 := by decide
@[simp] theorem fl_flK2_ne_flA2 : flK2 ≠ flA2 := by decide
@[simp] theorem fl_flK2_ne_flS2 : flK2 ≠ flS2 := by decide
@[simp] theorem fl_flK2_ne_flK1 : flK2 ≠ flK1 := by decide
@[simp] theorem fl_flK2_ne_flK3 : flK2 ≠ flK3 := by decide
@[simp] theorem fl_flK2_ne_flN : flK2 ≠ flN := by decide
@[simp] theorem fl_flK2_ne_flO : flK2 ≠ flO := by decide
@[simp] theorem fl_flK2_ne_flP : flK2 ≠ flP := by decide
@[simp] theorem fl_flK2_ne_lKb : flK2 ≠ lKb := by decide
@[simp] theorem fl_flK2_ne_lFl : flK2 ≠ lFl := by decide
@[simp] theorem fl_flK2_ne_lDh : flK2 ≠ lDh := by decide
@[simp] theorem fl_flK2_ne_lDt : flK2 ≠ lDt := by decide
@[simp] theorem fl_flK2_ne_lDg : flK2 ≠ lDg := by decide
@[simp] theorem fl_flK2_ne_lDi : flK2 ≠ lDi := by decide
@[simp] theorem fl_flK2_ne_lDo1 : flK2 ≠ lDo1 := by decide
@[simp] theorem fl_flK2_ne_lDo2 : flK2 ≠ lDo2 := by decide
@[simp] theorem fl_flK2_ne_lRp : flK2 ≠ lRp := by decide
@[simp] theorem fl_flK2_ne_lRn : flK2 ≠ lRn := by decide
@[simp] theorem fl_flK2_ne_lFle : flK2 ≠ lFle := by decide
@[simp] theorem fl_flK2_ne_lDir : flK2 ≠ lDir := by decide
@[simp] theorem fl_flK3_ne_flF : flK3 ≠ flF := by decide
@[simp] theorem fl_flK3_ne_flA : flK3 ≠ flA := by decide
@[simp] theorem fl_flK3_ne_flH : flK3 ≠ flH := by decide
@[simp] theorem fl_flK3_ne_flS : flK3 ≠ flS := by decide
@[simp] theorem fl_flK3_ne_flB : flK3 ≠ flB := by decide
@[simp] theorem fl_flK3_ne_flL : flK3 ≠ flL := by decide
@[simp] theorem fl_flK3_ne_flT : flK3 ≠ flT := by decide
@[simp] theorem fl_flK3_ne_flI : flK3 ≠ flI := by decide
@[simp] theorem fl_flK3_ne_flC1 : flK3 ≠ flC1 := by decide
@[simp] theorem fl_flK3_ne_flC2 : flK3 ≠ flC2 := by decide
@[simp] theorem fl_flK3_ne_flC3 : flK3 ≠ flC3 := by decide
@[simp] theorem fl_flK3_ne_flA2 : flK3 ≠ flA2 := by decide
@[simp] theorem fl_flK3_ne_flS2 : flK3 ≠ flS2 := by decide
@[simp] theorem fl_flK3_ne_flK1 : flK3 ≠ flK1 := by decide
@[simp] theorem fl_flK3_ne_flK2 : flK3 ≠ flK2 := by decide
@[simp] theorem fl_flK3_ne_flN : flK3 ≠ flN := by decide
@[simp] theorem fl_flK3_ne_flO : flK3 ≠ flO := by decide
@[simp] theorem fl_flK3_ne_flP : flK3 ≠ flP := by decide
@[simp] theorem fl_flK3_ne_lKb : flK3 ≠ lKb := by decide
@[simp] theorem fl_flK3_ne_lFl : flK3 ≠ lFl := by decide
@[simp] theorem fl_flK3_ne_lDh : flK3 ≠ lDh := by decide
@[simp] theorem fl_flK3_ne_lDt : flK3 ≠ lDt := by decide
@[simp] theorem fl_flK3_ne_lDg : flK3 ≠ lDg := by decide
@[simp] theorem fl_flK3_ne_lDi : flK3 ≠ lDi := by decide
@[simp] theorem fl_flK3_ne_lDo1 : flK3 ≠ lDo1 := by decide
@[simp] theorem fl_flK3_ne_lDo2 : flK3 ≠ lDo2 := by decide
@[simp] theorem fl_flK3_ne_lRp : flK3 ≠ lRp := by decide
@[simp] theorem fl_flK3_ne_lRn : flK3 ≠ lRn := by decide
@[simp] theorem fl_flK3_ne_lFle : flK3 ≠ lFle := by decide
@[simp] theorem fl_flK3_ne_lDir : flK3 ≠ lDir := by decide
@[simp] theorem fl_flN_ne_flF : flN ≠ flF := by decide
@[simp] theorem fl_flN_ne_flA : flN ≠ flA := by decide
@[simp] theorem fl_flN_ne_flH : flN ≠ flH := by decide
@[simp] theorem fl_flN_ne_flS : flN ≠ flS := by decide
@[simp] theorem fl_flN_ne_flB : flN ≠ flB := by decide
@[simp] theorem fl_flN_ne_flL : flN ≠ flL := by decide
@[simp] theorem fl_flN_ne_flT : flN ≠ flT := by decide
@[simp] theorem fl_flN_ne_flI : flN ≠ flI := by decide
@[simp] theorem fl_flN_ne_flC1 : flN ≠ flC1 := by decide
@[simp] theorem fl_flN_ne_flC2 : flN ≠ flC2 := by decide
@[simp] theorem fl_flN_ne_flC3 : flN ≠ flC3 := by decide
@[simp] theorem fl_flN_ne_flA2 : flN ≠ flA2 := by decide
@[simp] theorem fl_flN_ne_flS2 : flN ≠ flS2 := by decide
@[simp] theorem fl_flN_ne_flK1 : flN ≠ flK1 := by decide
@[simp] theorem fl_flN_ne_flK2 : flN ≠ flK2 := by decide
@[simp] theorem fl_flN_ne_flK3 : flN ≠ flK3 := by decide
@[simp] theorem fl_flN_ne_flO : flN ≠ flO := by decide
@[simp] theorem fl_flN_ne_flP : flN ≠ flP := by decide
@[simp] theorem fl_flN_ne_lKb : flN ≠ lKb := by decide
@[simp] theorem fl_flN_ne_lFl : flN ≠ lFl := by decide
@[simp] theorem fl_flN_ne_lDh : flN ≠ lDh := by decide
@[simp] theorem fl_flN_ne_lDt : flN ≠ lDt := by decide
@[simp] theorem fl_flN_ne_lDg : flN ≠ lDg := by decide
@[simp] theorem fl_flN_ne_lDi : flN ≠ lDi := by decide
@[simp] theorem fl_flN_ne_lDo1 : flN ≠ lDo1 := by decide
@[simp] theorem fl_flN_ne_lDo2 : flN ≠ lDo2 := by decide
@[simp] theorem fl_flN_ne_lRp : flN ≠ lRp := by decide
@[simp] theorem fl_flN_ne_lRn : flN ≠ lRn := by decide
@[simp] theorem fl_flN_ne_lFle : flN ≠ lFle := by decide
@[simp] theorem fl_flN_ne_lDir : flN ≠ lDir := by decide
@[simp] theorem fl_flO_ne_flF : flO ≠ flF := by decide
@[simp] theorem fl_flO_ne_flA : flO ≠ flA := by decide
@[simp] theorem fl_flO_ne_flH : flO ≠ flH := by decide
@[simp] theorem fl_flO_ne_flS : flO ≠ flS := by decide
@[simp] theorem fl_flO_ne_flB : flO ≠ flB := by decide
@[simp] theorem fl_flO_ne_flL : flO ≠ flL := by decide
@[simp] theorem fl_flO_ne_flT : flO ≠ flT := by decide
@[simp] theorem fl_flO_ne_flI : flO ≠ flI := by decide
@[simp] theorem fl_flO_ne_flC1 : flO ≠ flC1 := by decide
@[simp] theorem fl_flO_ne_flC2 : flO ≠ flC2 := by decide
@[simp] theorem fl_flO_ne_flC3 : flO ≠ flC3 := by decide
@[simp] theorem fl_flO_ne_flA2 : flO ≠ flA2 := by decide
@[simp] theorem fl_flO_ne_flS2 : flO ≠ flS2 := by decide
@[simp] theorem fl_flO_ne_flK1 : flO ≠ flK1 := by decide
@[simp] theorem fl_flO_ne_flK2 : flO ≠ flK2 := by decide
@[simp] theorem fl_flO_ne_flK3 : flO ≠ flK3 := by decide
@[simp] theorem fl_flO_ne_flN : flO ≠ flN := by decide
@[simp] theorem fl_flO_ne_flP : flO ≠ flP := by decide
@[simp] theorem fl_flO_ne_lKb : flO ≠ lKb := by decide
@[simp] theorem fl_flO_ne_lFl : flO ≠ lFl := by decide
@[simp] theorem fl_flO_ne_lDh : flO ≠ lDh := by decide
@[simp] theorem fl_flO_ne_lDt : flO ≠ lDt := by decide
@[simp] theorem fl_flO_ne_lDg : flO ≠ lDg := by decide
@[simp] theorem fl_flO_ne_lDi : flO ≠ lDi := by decide
@[simp] theorem fl_flO_ne_lDo1 : flO ≠ lDo1 := by decide
@[simp] theorem fl_flO_ne_lDo2 : flO ≠ lDo2 := by decide
@[simp] theorem fl_flO_ne_lRp : flO ≠ lRp := by decide
@[simp] theorem fl_flO_ne_lRn : flO ≠ lRn := by decide
@[simp] theorem fl_flO_ne_lFle : flO ≠ lFle := by decide
@[simp] theorem fl_flO_ne_lDir : flO ≠ lDir := by decide
@[simp] theorem fl_flP_ne_flF : flP ≠ flF := by decide
@[simp] theorem fl_flP_ne_flA : flP ≠ flA := by decide
@[simp] theorem fl_flP_ne_flH : flP ≠ flH := by decide
@[simp] theorem fl_flP_ne_flS : flP ≠ flS := by decide
@[simp] theorem fl_flP_ne_flB : flP ≠ flB := by decide
@[simp] theorem fl_flP_ne_flL : flP ≠ flL := by decide
@[simp] theorem fl_flP_ne_flT : flP ≠ flT := by decide
@[simp] theorem fl_flP_ne_flI : flP ≠ flI := by decide
@[simp] theorem fl_flP_ne_flC1 : flP ≠ flC1 := by decide
@[simp] theorem fl_flP_ne_flC2 : flP ≠ flC2 := by decide
@[simp] theorem fl_flP_ne_flC3 : flP ≠ flC3 := by decide
@[simp] theorem fl_flP_ne_flA2 : flP ≠ flA2 := by decide
@[simp] theorem fl_flP_ne_flS2 : flP ≠ flS2 := by decide
@[simp] theorem fl_flP_ne_flK1 : flP ≠ flK1 := by decide
@[simp] theorem fl_flP_ne_flK2 : flP ≠ flK2 := by decide
@[simp] theorem fl_flP_ne_flK3 : flP ≠ flK3 := by decide
@[simp] theorem fl_flP_ne_flN : flP ≠ flN := by decide
@[simp] theorem fl_flP_ne_flO : flP ≠ flO := by decide
@[simp] theorem fl_flP_ne_lKb : flP ≠ lKb := by decide
@[simp] theorem fl_flP_ne_lFl : flP ≠ lFl := by decide
@[simp] theorem fl_flP_ne_lDh : flP ≠ lDh := by decide
@[simp] theorem fl_flP_ne_lDt : flP ≠ lDt := by decide
@[simp] theorem fl_flP_ne_lDg : flP ≠ lDg := by decide
@[simp] theorem fl_flP_ne_lDi : flP ≠ lDi := by decide
@[simp] theorem fl_flP_ne_lDo1 : flP ≠ lDo1 := by decide
@[simp] theorem fl_flP_ne_lDo2 : flP ≠ lDo2 := by decide
@[simp] theorem fl_flP_ne_lRp : flP ≠ lRp := by decide
@[simp] theorem fl_flP_ne_lRn : flP ≠ lRn := by decide
@[simp] theorem fl_flP_ne_lFle : flP ≠ lFle := by decide
@[simp] theorem fl_flP_ne_lDir : flP ≠ lDir := by decide
@[simp] theorem fl_lKb_ne_flF : lKb ≠ flF := by decide
@[simp] theorem fl_lKb_ne_flA : lKb ≠ flA := by decide
@[simp] theorem fl_lKb_ne_flH : lKb ≠ flH := by decide
@[simp] theorem fl_lKb_ne_flS : lKb ≠ flS := by decide
@[simp] theorem fl_lKb_ne_flB : lKb ≠ flB := by decide
@[simp] theorem fl_lKb_ne_flL : lKb ≠ flL := by decide
@[simp] theorem fl_lKb_ne_flT : lKb ≠ flT := by decide
@[simp] theorem fl_lKb_ne_flI : lKb ≠ flI := by decide
@[simp] theorem fl_lKb_ne_flC1 : lKb ≠ flC1 := by decide
@[simp] theorem fl_lKb_ne_flC2 : lKb ≠ flC2 := by decide
@[simp] theorem fl_lKb_ne_flC3 : lKb ≠ flC3 := by decide
@[simp] theorem fl_lKb_ne_flA2 : lKb ≠ flA2 := by decide
@[simp] theorem fl_lKb_ne_flS2 : lKb ≠ flS2 := by decide
@[simp] theorem fl_lKb_ne_flK1 : lKb ≠ flK1 := by decide
@[simp] theorem fl_lKb_ne_flK2 : lKb ≠ flK2 := by decide
@[simp] theorem fl_lKb_ne_flK3 : lKb ≠ flK3 := by decide
@[simp] theorem fl_lKb_ne_flN : lKb ≠ flN := by decide
@[simp] theorem fl_lKb_ne_flO : lKb ≠ flO := by decide
@[simp] theorem fl_lKb_ne_flP : lKb ≠ flP := by decide
@[simp] theorem fl_lFl_ne_flF : lFl ≠ flF := by decide
@[simp] theorem fl_lFl_ne_flA : lFl ≠ flA := by decide
@[simp] theorem fl_lFl_ne_flH : lFl ≠ flH := by decide
@[simp] theorem fl_lFl_ne_flS : lFl ≠ flS := by decide
@[simp] theorem fl_lFl_ne_flB : lFl ≠ flB := by decide
@[simp] theorem fl_lFl_ne_flL : lFl ≠ flL := by decide
@[simp] theorem fl_lFl_ne_flT : lFl ≠ flT := by decide
@[simp] theorem fl_lFl_ne_flI : lFl ≠ flI := by decide
@[simp] theorem fl_lFl_ne_flC1 : lFl ≠ flC1 := by decide
@[simp] theorem fl_lFl_ne_flC2 : lFl ≠ flC2 := by decide
@[simp] theorem fl_lFl_ne_flC3 : lFl ≠ flC3 := by decide
@[simp] theorem fl_lFl_ne_flA2 : lFl ≠ flA2 := by decide
@[simp] theorem fl_lFl_ne_flS2 : lFl ≠ flS2 := by decide
@[simp] theorem fl_lFl_ne_flK1 : lFl ≠ flK1 := by decide
@[simp] theorem fl_lFl_ne_flK2 : lFl ≠ flK2 := by decide
@[simp] theorem fl_lFl_ne_flK3 : lFl ≠ flK3 := by decide
@[simp] theorem fl_lFl_ne_flN : lFl ≠ flN := by decide
@[simp] theorem fl_lFl_ne_flO : lFl ≠ flO := by decide
@[simp] theorem fl_lFl_ne_flP : lFl ≠ flP := by decide
@[simp] theorem fl_lDh_ne_flF : lDh ≠ flF := by decide
@[simp] theorem fl_lDh_ne_flA : lDh ≠ flA := by decide
@[simp] theorem fl_lDh_ne_flH : lDh ≠ flH := by decide
@[simp] theorem fl_lDh_ne_flS : lDh ≠ flS := by decide
@[simp] theorem fl_lDh_ne_flB : lDh ≠ flB := by decide
@[simp] theorem fl_lDh_ne_flL : lDh ≠ flL := by decide
@[simp] theorem fl_lDh_ne_flT : lDh ≠ flT := by decide
@[simp] theorem fl_lDh_ne_flI : lDh ≠ flI := by decide
@[simp] theorem fl_lDh_ne_flC1 : lDh ≠ flC1 := by decide
@[simp] theorem fl_lDh_ne_flC2 : lDh ≠ flC2 := by decide
@[simp] theorem fl_lDh_ne_flC3 : lDh ≠ flC3 := by decide
@[simp] theorem fl_lDh_ne_flA2 : lDh ≠ flA2 := by decide
@[simp] theorem fl_lDh_ne_flS2 : lDh ≠ flS2 := by decide
@[simp] theorem fl_lDh_ne_flK1 : lDh ≠ flK1 := by decide
@[simp] theorem fl_lDh_ne_flK2 : lDh ≠ flK2 := by decide
@[simp] theorem fl_lDh_ne_flK3 : lDh ≠ flK3 := by decide
@[simp] theorem fl_lDh_ne_flN : lDh ≠ flN := by decide
@[simp] theorem fl_lDh_ne_flO : lDh ≠ flO := by decide
@[simp] theorem fl_lDh_ne_flP : lDh ≠ flP := by decide
@[simp] theorem fl_lDt_ne_flF : lDt ≠ flF := by decide
@[simp] theorem fl_lDt_ne_flA : lDt ≠ flA := by decide
@[simp] theorem fl_lDt_ne_flH : lDt ≠ flH := by decide
@[simp] theorem fl_lDt_ne_flS : lDt ≠ flS := by decide
@[simp] theorem fl_lDt_ne_flB : lDt ≠ flB := by decide
@[simp] theorem fl_lDt_ne_flL : lDt ≠ flL := by decide
@[simp] theorem fl_lDt_ne_flT : lDt ≠ flT := by decide
@[simp] theorem fl_lDt_ne_flI : lDt ≠ flI := by decide
@[simp] theorem fl_lDt_ne_flC1 : lDt ≠ flC1 := by decide
@[simp] theorem fl_lDt_ne_flC2 : lDt ≠ flC2 := by decide
@[simp] theorem fl_lDt_ne_flC3 : lDt ≠ flC3 := by decide
@[simp] theorem fl_lDt_ne_flA2 : lDt ≠ flA2 := by decide
@[simp] theorem fl_lDt_ne_flS2 : lDt ≠ flS2 := by decide
@[simp] theorem fl_lDt_ne_flK1 : lDt ≠ flK1 := by decide
@[simp] theorem fl_lDt_ne_flK2 : lDt ≠ flK2 := by decide
@[simp] theorem fl_lDt_ne_flK3 : lDt ≠ flK3 := by decide
@[simp] theorem fl_lDt_ne_flN : lDt ≠ flN := by decide
@[simp] theorem fl_lDt_ne_flO : lDt ≠ flO := by decide
@[simp] theorem fl_lDt_ne_flP : lDt ≠ flP := by decide
@[simp] theorem fl_lDg_ne_flF : lDg ≠ flF := by decide
@[simp] theorem fl_lDg_ne_flA : lDg ≠ flA := by decide
@[simp] theorem fl_lDg_ne_flH : lDg ≠ flH := by decide
@[simp] theorem fl_lDg_ne_flS : lDg ≠ flS := by decide
@[simp] theorem fl_lDg_ne_flB : lDg ≠ flB := by decide
@[simp] theorem fl_lDg_ne_flL : lDg ≠ flL := by decide
@[simp] theorem fl_lDg_ne_flT : lDg ≠ flT := by decide
@[simp] theorem fl_lDg_ne_flI : lDg ≠ flI := by decide
@[simp] theorem fl_lDg_ne_flC1 : lDg ≠ flC1 := by decide
@[simp] theorem fl_lDg_ne_flC2 : lDg ≠ flC2 := by decide
@[simp] theorem fl_lDg_ne_flC3 : lDg ≠ flC3 := by decide
@[simp] theorem fl_lDg_ne_flA2 : lDg ≠ flA2 := by decide
@[simp] theorem fl_lDg_ne_flS2 : lDg ≠ flS2 := by decide
@[simp] theorem fl_lDg_ne_flK1 : lDg ≠ flK1 := by decide
@[simp] theorem fl_lDg_ne_flK2 : lDg ≠ flK2 := by decide
@[simp] theorem fl_lDg_ne_flK3 : lDg ≠ flK3 := by decide
@[simp] theorem fl_lDg_ne_flN : lDg ≠ flN := by decide
@[simp] theorem fl_lDg_ne_flO : lDg ≠ flO := by decide
@[simp] theorem fl_lDg_ne_flP : lDg ≠ flP := by decide
@[simp] theorem fl_lDi_ne_flF : lDi ≠ flF := by decide
@[simp] theorem fl_lDi_ne_flA : lDi ≠ flA := by decide
@[simp] theorem fl_lDi_ne_flH : lDi ≠ flH := by decide
@[simp] theorem fl_lDi_ne_flS : lDi ≠ flS := by decide
@[simp] theorem fl_lDi_ne_flB : lDi ≠ flB := by decide
@[simp] theorem fl_lDi_ne_flL : lDi ≠ flL := by decide
@[simp] theorem fl_lDi_ne_flT : lDi ≠ flT := by decide
@[simp] theorem fl_lDi_ne_flI : lDi ≠ flI := by decide
@[simp] theorem fl_lDi_ne_flC1 : lDi ≠ flC1 := by decide
@[simp] theorem fl_lDi_ne_flC2 : lDi ≠ flC2 := by decide
@[simp] theorem fl_lDi_ne_flC3 : lDi ≠ flC3 := by decide
@[simp] theorem fl_lDi_ne_flA2 : lDi ≠ flA2 := by decide
@[simp] theorem fl_lDi_ne_flS2 : lDi ≠ flS2 := by decide
@[simp] theorem fl_lDi_ne_flK1 : lDi ≠ flK1 := by decide
@[simp] theorem fl_lDi_ne_flK2 : lDi ≠ flK2 := by decide
@[simp] theorem fl_lDi_ne_flK3 : lDi ≠ flK3 := by decide
@[simp] theorem fl_lDi_ne_flN : lDi ≠ flN := by decide
@[simp] theorem fl_lDi_ne_flO : lDi ≠ flO := by decide
@[simp] theorem fl_lDi_ne_flP : lDi ≠ flP := by decide
@[simp] theorem fl_lDo1_ne_flF : lDo1 ≠ flF := by decide
@[simp] theorem fl_lDo1_ne_flA : lDo1 ≠ flA := by decide
@[simp] theorem fl_lDo1_ne_flH : lDo1 ≠ flH := by decide
@[simp] theorem fl_lDo1_ne_flS : lDo1 ≠ flS := by decide
@[simp] theorem fl_lDo1_ne_flB : lDo1 ≠ flB := by decide
@[simp] theorem fl_lDo1_ne_flL : lDo1 ≠ flL := by decide
@[simp] theorem fl_lDo1_ne_flT : lDo1 ≠ flT := by decide
@[simp] theorem fl_lDo1_ne_flI : lDo1 ≠ flI := by decide
@[simp] theorem fl_lDo1_ne_flC1 : lDo1 ≠ flC1 := by decide
@[simp] theorem fl_lDo1_ne_flC2 : lDo1 ≠ flC2 := by decide
@[simp] theorem fl_lDo1_ne_flC3 : lDo1 ≠ flC3 := by decide
@[simp] theorem fl_lDo1_ne_flA2 : lDo1 ≠ flA2 := by decide
@[simp] theorem fl_lDo1_ne_flS2 : lDo1 ≠ flS2 := by decide
@[simp] theorem fl_lDo1_ne_flK1 : lDo1 ≠ flK1 := by decide
@[simp] theorem fl_lDo1_ne_flK2 : lDo1 ≠ flK2 := by decide
@[simp] theorem fl_lDo1_ne_flK3 : lDo1 ≠ flK3 := by decide
@[simp] theorem fl_lDo1_ne_flN : lDo1 ≠ flN := by decide
@[simp] theorem fl_lDo1_ne_flO : lDo1 ≠ flO := by decide
@[simp] theorem fl_lDo1_ne_flP : lDo1 ≠ flP := by decide
@[simp] theorem fl_lDo2_ne_flF : lDo2 ≠ flF := by decide
@[simp] theorem fl_lDo2_ne_flA : lDo2 ≠ flA := by decide
@[simp] theorem fl_lDo2_ne_flH : lDo2 ≠ flH := by decide
@[simp] theorem fl_lDo2_ne_flS : lDo2 ≠ flS := by decide
@[simp] theorem fl_lDo2_ne_flB : lDo2 ≠ flB := by decide
@[simp] theorem fl_lDo2_ne_flL : lDo2 ≠ flL := by decide
@[simp] theorem fl_lDo2_ne_flT : lDo2 ≠ flT := by decide
@[simp] theorem fl_lDo2_ne_flI : lDo2 ≠ flI := by decide
@[simp] theorem fl_lDo2_ne_flC1 : lDo2 ≠ flC1 := by decide
@[simp] theorem fl_lDo2_ne_flC2 : lDo2 ≠ flC2 := by decide
@[simp] theorem fl_lDo2_ne_flC3 : lDo2 ≠ flC3 := by decide
@[simp] theorem fl_lDo2_ne_flA2 : lDo2 ≠ flA2 := by decide
@[simp] theorem fl_lDo2_ne_flS2 : lDo2 ≠ flS2 := by decide
@[simp] theorem fl_lDo2_ne_flK1 : lDo2 ≠ flK1 := by decide
@[simp] theorem fl_lDo2_ne_flK2 : lDo2 ≠ flK2 := by decide
@[simp] theorem fl_lDo2_ne_flK3 : lDo2 ≠ flK3 := by decide
@[simp] theorem fl_lDo2_ne_flN : lDo2 ≠ flN := by decide
@[simp] theorem fl_lDo2_ne_flO : lDo2 ≠ flO := by decide
@[simp] theorem fl_lDo2_ne_flP : lDo2 ≠ flP := by decide
@[simp] theorem fl_lRp_ne_flF : lRp ≠ flF := by decide
@[simp] theorem fl_lRp_ne_flA : lRp ≠ flA := by decide
@[simp] theorem fl_lRp_ne_flH : lRp ≠ flH := by decide
@[simp] theorem fl_lRp_ne_flS : lRp ≠ flS := by decide
@[simp] theorem fl_lRp_ne_flB : lRp ≠ flB := by decide
@[simp] theorem fl_lRp_ne_flL : lRp ≠ flL := by decide
@[simp] theorem fl_lRp_ne_flT : lRp ≠ flT := by decide
@[simp] theorem fl_lRp_ne_flI : lRp ≠ flI := by decide
@[simp] theorem fl_lRp_ne_flC1 : lRp ≠ flC1 := by decide
@[simp] theorem fl_lRp_ne_flC2 : lRp ≠ flC2 := by decide
@[simp] theorem fl_lRp_ne_flC3 : lRp ≠ flC3 := by decide
@[simp] theorem fl_lRp_ne_flA2 : lRp ≠ flA2 := by decide
@[simp] theorem fl_lRp_ne_flS2 : lRp ≠ flS2 := by decide
@[simp] theorem fl_lRp_ne_flK1 : lRp ≠ flK1 := by decide
@[simp] theorem fl_lRp_ne_flK2 : lRp ≠ flK2 := by decide
@[simp] theorem fl_lRp_ne_flK3 : lRp ≠ flK3 := by decide
@[simp] theorem fl_lRp_ne_flN : lRp ≠ flN := by decide
@[simp] theorem fl_lRp_ne_flO : lRp ≠ flO := by decide
@[simp] theorem fl_lRp_ne_flP : lRp ≠ flP := by decide
@[simp] theorem fl_lRn_ne_flF : lRn ≠ flF := by decide
@[simp] theorem fl_lRn_ne_flA : lRn ≠ flA := by decide
@[simp] theorem fl_lRn_ne_flH : lRn ≠ flH := by decide
@[simp] theorem fl_lRn_ne_flS : lRn ≠ flS := by decide
@[simp] theorem fl_lRn_ne_flB : lRn ≠ flB := by decide
@[simp] theorem fl_lRn_ne_flL : lRn ≠ flL := by decide
@[simp] theorem fl_lRn_ne_flT : lRn ≠ flT := by decide
@[simp] theorem fl_lRn_ne_flI : lRn ≠ flI := by decide
@[simp] theorem fl_lRn_ne_flC1 : lRn ≠ flC1 := by decide
@[simp] theorem fl_lRn_ne_flC2 : lRn ≠ flC2 := by decide
@[simp] theorem fl_lRn_ne_flC3 : lRn ≠ flC3 := by decide
@[simp] theorem fl_lRn_ne_flA2 : lRn ≠ flA2 := by decide
@[simp] theorem fl_lRn_ne_flS2 : lRn ≠ flS2 := by decide
@[simp] theorem fl_lRn_ne_flK1 : lRn ≠ flK1 := by decide
@[simp] theorem fl_lRn_ne_flK2 : lRn ≠ flK2 := by decide
@[simp] theorem fl_lRn_ne_flK3 : lRn ≠ flK3 := by decide
@[simp] theorem fl_lRn_ne_flN : lRn ≠ flN := by decide
@[simp] theorem fl_lRn_ne_flO : lRn ≠ flO := by decide
@[simp] theorem fl_lRn_ne_flP : lRn ≠ flP := by decide
@[simp] theorem fl_lFle_ne_flF : lFle ≠ flF := by decide
@[simp] theorem fl_lFle_ne_flA : lFle ≠ flA := by decide
@[simp] theorem fl_lFle_ne_flH : lFle ≠ flH := by decide
@[simp] theorem fl_lFle_ne_flS : lFle ≠ flS := by decide
@[simp] theorem fl_lFle_ne_flB : lFle ≠ flB := by decide
@[simp] theorem fl_lFle_ne_flL : lFle ≠ flL := by decide
@[simp] theorem fl_lFle_ne_flT : lFle ≠ flT := by decide
@[simp] theorem fl_lFle_ne_flI : lFle ≠ flI := by decide
@[simp] theorem fl_lFle_ne_flC1 : lFle ≠ flC1 := by decide
@[simp] theorem fl_lFle_ne_flC2 : lFle ≠ flC2 := by decide
@[simp] theorem fl_lFle_ne_flC3 : lFle ≠ flC3 := by decide
@[simp] theorem fl_lFle_ne_flA2 : lFle ≠ flA2 := by decide
@[simp] theorem fl_lFle_ne_flS2 : lFle ≠ flS2 := by decide
@[simp] theorem fl_lFle_ne_flK1 : lFle ≠ flK1 := by decide
@[simp] theorem fl_lFle_ne_flK2 : lFle ≠ flK2 := by decide
@[simp] theorem fl_lFle_ne_flK3 : lFle ≠ flK3 := by decide
@[simp] theorem fl_lFle_ne_flN : lFle ≠ flN := by decide
@[simp] theorem fl_lFle_ne_flO : lFle ≠ flO := by decide
@[simp] theorem fl_lFle_ne_flP : lFle ≠ flP := by decide
@[simp] theorem fl_lDir_ne_flF : lDir ≠ flF := by decide
@[simp] theorem fl_lDir_ne_flA : lDir ≠ flA := by decide
@[simp] theorem fl_lDir_ne_flH : lDir ≠ flH := by decide
@[simp] theorem fl_lDir_ne_flS : lDir ≠ flS := by decide
@[simp] theorem fl_lDir_ne_flB : lDir ≠ flB := by decide
@[simp] theorem fl_lDir_ne_flL : lDir ≠ flL := by decide
@[simp] theorem fl_lDir_ne_flT : lDir ≠ flT := by decide
@[simp] theorem fl_lDir_ne_flI : lDir ≠ flI := by decide
@[simp] theorem fl_lDir_ne_flC1 : lDir ≠ flC1 := by decide
@[simp] theorem fl_lDir_ne_flC2 : lDir ≠ flC2 := by decide
@[simp] theorem fl_lDir_ne_flC3 : lDir ≠ flC3 := by decide
@[simp] theorem fl_lDir_ne_flA2 : lDir ≠ flA2 := by decide
@[simp] theorem fl_lDir_ne_flS2 : lDir ≠ flS2 := by decide
@[simp] theorem fl_lDir_ne_flK1 : lDir ≠ flK1 := by decide
@[simp] theorem fl_lDir_ne_flK2 : lDir ≠ flK2 := by decide
@[simp] theorem fl_lDir_ne_flK3 : lDir ≠ flK3 := by decide
@[simp] theorem fl_lDir_ne_flN : lDir ≠ flN := by decide
@[simp] theorem fl_lDir_ne_flO : lDir ≠ flO := by decide
@[simp] theorem fl_lDir_ne_flP : lDir ≠ flP := by decide

def flParams : List MlS := [flF, flA, flH, flS]
def flLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lDo1, lDo2, lRp, lRn, flB, flL, flT, flI, flC1, flC2, flC3, flA2,
  flS2, flK1, flK2, flK3, flN, flO, flP]

def flRet (C : Ctx) (ea es : ExpHOL 64) : ProgHOL 64 :=
  allocP C flO (.const 16) (.seq (.store (vv flO) ea) (.seq (.store (.op .add [vv flO, .const 8]) es)
    (.return (vv flO))))

def flCall (k : MlS) (eA eH eS : ExpHOL 64) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.local, k), none)) fFl [.op .sub [vv flF, .const 1], eA, eH, eS])
  (.seq (.assign .local flA2 (.load .one (vv k))) (.seq (.assign .local flS2 (.load .one (.op .add [vv k, .const 8])))
    rest))

def flRetK (C : Ctx) : ProgHOL 64 := flRet C (vv flA2) (vv flS2)

def flArm2 (C : Ctx) : ProgHOL 64 :=
  flCall flK1 (vv flA) (vv flC1) (vv flN) (flCall flK2 (vv flA2) (vv flC2) (vv flS2) (flRetK C))

def flArm3 (C : Ctx) : ProgHOL 64 :=
  flCall flK1 (vv flA) (vv flC1) (vv flN) (flCall flK2 (vv flA2) (vv flC2) (vv flS2)
    (flCall flK3 (vv flA2) (vv flC3) (vv flS2) (flRetK C)))

def flFvarK (C : Ctx) : ProgHOL 64 :=
  mlInsP C flP (vv flI) (vv flT) (.const 0) (vv flA) (flCall flK1 (vv flP) (vv flT) (vv flN) (flRetK C))

def flFvar (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local flT (.load .one (vv lRp)))
  (.ite (.cmp .equal (vv lRn) (.const 1)) (.seq (.assign .local flI (.const 0)) (flFvarK C))
    (.ite (.cmp .equal (vv lRn) (.const 2))
      (.seq (.assign .local flI (.load .one (.op .add [vv lRp, .const 8]))) (flFvarK C)) hang))

def flCore (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .equal (vv flF) (.const 0)) hang
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv flH)) (.seq (storeDerived 9 10)
  (.seq (.assign .local flB (.op .and [.shift .lsr (vv lDo1) (.const 1), .const 32767]))
  (.ite (.cmp .equal (vv flB) (.const 0)) (flRet C (vv flA) (vv flS))
  (.seq (.call (some (some (.local, flL), none)) fMl [vv flS, vv flH, .const 0])
  (.ite (.cmp .notEqual (vv flL) (.const 0)) (flRet C (vv flA) (vv flS))
  (mlInsP C flN (vv flH) (.const 0) (.const 1) (vv flS)
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv flH)) (.seq eViewP
  (.ite (.cmp .equal (vv lDg) (.const 1)) (flFvar C)
  (.ite (.cmp .equal (vv lDg) (.const 4))
    (.seq (.assign .local flC1 (.load .one (vv lRp)))
      (.seq (.assign .local flC2 (.load .one (.op .add [vv lRp, .const 8]))) (flArm2 C)))
  (.ite (.cmp .equal (vv lDg) (.const 5))
    (.seq (.assign .local flC1 (.load .one (vv lRp)))
      (.seq (.assign .local flC2 (.load .one (.op .add [vv lRp, .const 8]))) (flArm2 C)))
  (.ite (.cmp .equal (vv lDg) (.const 6))
    (.seq (.assign .local flC1 (.load .one (vv lRp)))
      (.seq (.assign .local flC2 (.load .one (.op .add [vv lRp, .const 8]))) (flArm2 C)))
  (.ite (.cmp .equal (vv lDg) (.const 7))
    (.seq (.assign .local flC1 (.load .one (vv lRp)))
      (.seq (.assign .local flC2 (.load .one (.op .add [vv lRp, .const 8])))
        (.seq (.assign .local flC3 (.load .one (.op .add [vv lRp, .const 16]))) (flArm3 C))))
  (.ite (.cmp .equal (vv lDg) (.const 9))
    (.seq (.assign .local flC1 (.load .one (.op .add [vv lRp, .const 8]))) (flCall flK1 (vv flA) (vv flC1) (vv flN) (flRetK C)))
    (flRet C (vv flA) (vv flN)))))))))))))))))))

def flBody (C : Ctx) : ProgHOL 64 := prologue flLocals (flCore C)

structure FlCodes (C : Ctx) : Prop where
  ml : C.code.lookup fMl = some (mlParams.map (fun p => (p, ShapeHOL.one)), mlBody, .one)
  self : C.code.lookup fFl = some (flParams.map (fun p => (p, ShapeHOL.one)), flBody C, .one)

section
variable {σ : Type}

theorem accRep_toH {C : Ctx} {H H' : List (BitVec 64)} {p : BitVec 64} {acc : List (Nat × EIdx)}
    (h : AccRep C H p acc) : AccRep (ctxH C H') H p acc := ⟨mnodes_toH h.1, h.2⟩
theorem accRep_ofH {C : Ctx} {H H' : List (BitVec 64)} {p : BitVec 64} {acc : List (Nat × EIdx)}
    (h : AccRep (ctxH C H') H p acc) : AccRep C H p acc := ⟨mnodes_H h.1, h.2⟩
theorem seenRep_toH {C : Ctx} {H H' : List (BitVec 64)} {p : BitVec 64} {seen : Std.HashMap EIdx Unit}
    (h : SeenRep C H p seen) : SeenRep (ctxH C H') H p seen := let ⟨xs, hm, he⟩ := h; ⟨xs, mnodes_toH hm, he⟩
theorem seenRep_ofH {C : Ctx} {H H' : List (BitVec 64)} {p : BitVec 64} {seen : Std.HashMap EIdx Unit}
    (h : SeenRep (ctxH C H') H p seen) : SeenRep C H p seen := let ⟨xs, hm, he⟩ := h; ⟨xs, mnodes_H hm, he⟩

/-- The leaves and the seen set as a fresh pair block, nothing else changes. -/
def PostFl (C : Ctx) (s : AState) (as : List (Nat × EIdx) × Std.HashMap EIdx Unit) (w : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  s' = s ∧ ∃ H' o pa ps, C.H <+: H' ∧ w = cellA C o ∧ H'[o]? = some pa ∧ H'[o + 1]? = some ps ∧
    AccRep C H' pa as.1 ∧ SeenRep C H' ps as.2 ∧ SR (ctxH C H') s st

theorem postFl_locals (C : Ctx) (s : AState) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostFl C s a w s' st → PostFl C s a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, H', o, pa, ps, h2, h3, h4, h5, h6, h7, h8⟩ =>
    ⟨h1, H', o, pa, ps, h2, h3, h4, h5, h6, h7, sr_of_eq h8 rfl rfl rfl rfl⟩

theorem fl_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ flLocals → (ctxEnv C ++ flParams.zip vals).get x = none :=
  Knot.params_none C flLocals flParams vals (by decide) (by decide)

theorem specR_flRetI {C : Ctx} (hok : CtxOK C) {H0 H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem}
    {D : List MlS} (ea es : ExpHOL 64) (as : List (Nat × EIdx) × Std.HashMap EIdx Unit) (pa ps : BitVec 64)
    (hD : flO ∈ D) (hea : ∀ w, sev ((flO, w) :: Γ) ea = some pa) (hes : ∀ w, sev ((flO, w) :: Γ) es = some ps)
    (hacc : AccRep C H pa as.1) (hseen : SeenRep C H ps as.2) (h0 : H0 <+: H) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (flRet C ea es) s (pure as) (PostFl (ctxH C H0) s) := by
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hlay := hok.heapLay
  refine specR_allocI (C := ctxH C H) flO (.const 16) 2 (by omega) hD (fun _ => rfl) (fun H1 ws hp1 hws hroom => ?_)
  have hp1' : H <+: H1 := hp1
  have hL := hp1'.length_le
  change SpecR (Inv (ctxH C (H1 ++ ws)) s ((flO, cellA C H1.length) :: Γ) _ _) _ _ _ _
  refine specR_heapStoreI (ctxOK_H hok _) (vv flO) ea H1.length (by show _ < (H1 ++ ws).length; simp; omega)
    pa (by simp <;> rfl) (hea _) ?_
  change SpecR (Inv (ctxH C ((H1 ++ ws).set H1.length pa)) _ _ _ _) _ _ _ _
  refine specR_heapStoreI (ctxOK_H hok _) (.op .add [vv flO, .const 8]) es (H1.length + 1)
    (by show _ < ((H1 ++ ws).set _ _).length; simp; omega) ps (by simp +decide [sev]; exact cellA_add8 C _) (hes _) ?_
  have g0 : (((H1 ++ ws).set H1.length pa).set (H1.length + 1) ps)[H1.length]? = some pa := by
    simp [List.getElem?_set, hws]
  have g1 : (((H1 ++ ws).set H1.length pa).set (H1.length + 1) ps)[H1.length + 1]? = some ps := by
    simp [List.getElem?_set, hws]
  have hpre : H <+: ((H1 ++ ws).set H1.length pa).set (H1.length + 1) ps :=
    prefix_set_ge (prefix_set_ge (hp1'.trans (List.prefix_append _ _)) _ (by omega) _) _ (by omega) _
  exact specR_returnI _ (cellA C H1.length) (by simp +decide [Env.get] <;> rfl)
    (fun t ht => ⟨rfl, _, H1.length, pa, ps, h0.trans hpre, rfl, g0, g1, accRep_toH (accRep_mono hpre hacc),
      seenRep_toH (seenRep_mono hpre hseen), sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- The walk's spec at fuel `n`, for every argument. -/
def FlRec (C : Ctx) (n : Nat) : Prop :=
  ∀ (acc : List (Nat × EIdx)) (seen : Std.HashMap EIdx Unit) (h : EIdx) (H : List (BitVec 64)) (s : AState)
    (pa ps : BitVec 64), C.H <+: H → AccRep C H pa acc → SeenRep C H ps seen →
    SpecR (σ := σ) (Pre (ctxH C H) s (flParams.zip [BitVec.ofNat 64 n, pa, Enc.idxW h, ps])) (flBody C) s
      (fvarLeavesGo acc seen n h) (PostFl (ctxH C H) s)

theorem specR_flCallI {α : Type} {C : Ctx} (hok : CtxOK C) (hc : FlCodes C) {n : Nat} (ih : FlRec (σ := σ) C n)
    {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {k : List (Nat × EIdx) × Std.HashMap EIdx Unit → AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (eA eH eS : ExpHOL 64) (acc : List (Nat × EIdx)) (seen : Std.HashMap EIdx Unit) (h : EIdx)
    (pa ps : BitVec 64) (hx : x ∈ D ∧ flA2 ∈ D ∧ flS2 ∈ D) (hxn : x ≠ flA2 ∧ flS2 ≠ x) (hp : C.H <+: H)
    (hacc : AccRep C H pa acc) (hseen : SeenRep C H ps seen) (hF : Γ.get flF = some (BitVec.ofNat 64 (n + 1)))
    (heA : sev Γ eA = some pa) (heH : sev Γ eH = some (Enc.idxW h)) (heS : sev Γ eS = some ps)
    (hk : ∀ (as : List (Nat × EIdx) × Std.HashMap EIdx Unit) H' pa' ps' w, H <+: H' → AccRep C H' pa' as.1 →
      SeenRep C H' ps' as.2 →
      SpecR (Inv (ctxH C H') s ((flS2, ps') :: (flA2, pa') :: (x, w) :: Γ) [] D) rest s (k as) R) :
    SpecR (Inv (ctxH C H) s Γ M D) (flCall x eA eH eS rest) s (fvarLeavesGo acc seen n h >>= k) R := by
  unfold flCall
  refine specR_callNIH (C := ctxH C H) x fFl flParams [.op .sub [vv flF, .const 1], eA, eH, eS] (flBody C)
    [BitVec.ofNat 64 n, pa, Enc.idxW h, ps] (by decide) rfl hx.1 hc.self
    ⟨by simp [sev, hF]; exact Ex.ofNat_succ_sub_one _, heA, heH, heS, trivial⟩
    (PostFl (ctxH C H) s)
    (fun as w s' H' => s' = s ∧ ∃ o pa' ps', w = cellA C o ∧ H'[o]? = some pa' ∧ H'[o + 1]? = some ps' ∧
      AccRep C H' pa' as.1 ∧ SeenRep C H' ps' as.2)
    (fun as w s' st ⟨h1, H', o, pa', ps', hp', hw, h0, h1', ha', hs', hsr⟩ =>
      ⟨H', hp', ⟨h1, o, pa', ps', hw, h0, h1', accRep_ofH ha', seenRep_ofH hs'⟩, by subst h1; exact hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu flParams _ rfl hlk) (ih acc seen h H s pa ps hp hacc hseen))
    (fun as w s' H' hp' ⟨hs', o, pa', ps', hw, h0, h1', ha', hsn'⟩ => ?_)
  subst hs' hw
  refine UD.specR_heapLoadI' (C := ctxH C H') flA2 (vv x) o pa' h0 hx.2.1 (by simp [Env.get]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H') flS2 (.op .add [vv x, .const 8]) (o + 1) ps' h1' hx.2.2
    (by simp [sev, Env.get, hxn.1]; exact (cellA_add8 C o : _)) ?_
  exact hk as H' pa' ps' (cellA C o) hp' ha' hsn'

end

end ConPanqueque.T.WC
