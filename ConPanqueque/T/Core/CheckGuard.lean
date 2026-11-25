import ConPanqueque.T.Core.LvlZero
import ConPanqueque.T.Core.FormerNZ
import ConPanqueque.T.SRFacts
import ConPanqueque.T.PinRead
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `checkGuardRows`

The projection guard's rows `(d, dom)` (a heap block `[d₀, dom₀, d₁, dom₁, …]`): each domain's type at the io
grade, `whnf`ed to a sort whose level must be zero wherever the guard sort is (`zw`). The guard sort is a level
handle. The twin's state facts (store well-formedness, the read cache) are a family `Q` closed under the steps.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc
open ConLeche (Level)

def cgG := ofString "cgn_g"
def cgR := ofString "cgn_r"
def cgN := ofString "cgn_n"
def cgI := ofString "cgn_i"
def cgD := ofString "cgn_d"
def cgE := ofString "cgn_e"
def cgT := ofString "cgn_t"
def cgW := ofString "cgn_w"
def cgU := ofString "cgn_u"
def cgZ := ofString "cgn_z"
def cgX := ofString "cgn_x"
def fCg := ofString "checkGuardRows"

@[simp] theorem cg_cgG_ne_cgR : cgG ≠ cgR := by decide
@[simp] theorem cg_cgG_ne_cgN : cgG ≠ cgN := by decide
@[simp] theorem cg_cgG_ne_cgI : cgG ≠ cgI := by decide
@[simp] theorem cg_cgG_ne_cgD : cgG ≠ cgD := by decide
@[simp] theorem cg_cgG_ne_cgE : cgG ≠ cgE := by decide
@[simp] theorem cg_cgG_ne_cgT : cgG ≠ cgT := by decide
@[simp] theorem cg_cgG_ne_cgW : cgG ≠ cgW := by decide
@[simp] theorem cg_cgG_ne_cgU : cgG ≠ cgU := by decide
@[simp] theorem cg_cgG_ne_cgZ : cgG ≠ cgZ := by decide
@[simp] theorem cg_cgG_ne_cgX : cgG ≠ cgX := by decide
@[simp] theorem cg_cgG_ne_kFu : cgG ≠ kFu := by decide
@[simp] theorem cg_kFu_ne_cgG : kFu ≠ cgG := by decide
@[simp] theorem cg_cgG_ne_lFl : cgG ≠ lFl := by decide
@[simp] theorem cg_lFl_ne_cgG : lFl ≠ cgG := by decide
@[simp] theorem cg_cgG_ne_lDh : cgG ≠ lDh := by decide
@[simp] theorem cg_lDh_ne_cgG : lDh ≠ cgG := by decide
@[simp] theorem cg_cgG_ne_lDt : cgG ≠ lDt := by decide
@[simp] theorem cg_lDt_ne_cgG : lDt ≠ cgG := by decide
@[simp] theorem cg_cgG_ne_lDg : cgG ≠ lDg := by decide
@[simp] theorem cg_lDg_ne_cgG : lDg ≠ cgG := by decide
@[simp] theorem cg_cgG_ne_lDi : cgG ≠ lDi := by decide
@[simp] theorem cg_lDi_ne_cgG : lDi ≠ cgG := by decide
@[simp] theorem cg_cgG_ne_lRp : cgG ≠ lRp := by decide
@[simp] theorem cg_lRp_ne_cgG : lRp ≠ cgG := by decide
@[simp] theorem cg_cgG_ne_lRn : cgG ≠ lRn := by decide
@[simp] theorem cg_lRn_ne_cgG : lRn ≠ cgG := by decide
@[simp] theorem cg_cgG_ne_lDir : cgG ≠ lDir := by decide
@[simp] theorem cg_lDir_ne_cgG : lDir ≠ cgG := by decide
@[simp] theorem cg_cgG_ne_lFle : cgG ≠ lFle := by decide
@[simp] theorem cg_lFle_ne_cgG : lFle ≠ cgG := by decide
@[simp] theorem cg_cgG_ne_lKb : cgG ≠ lKb := by decide
@[simp] theorem cg_lKb_ne_cgG : lKb ≠ cgG := by decide
@[simp] theorem cg_cgR_ne_cgG : cgR ≠ cgG := by decide
@[simp] theorem cg_cgR_ne_cgN : cgR ≠ cgN := by decide
@[simp] theorem cg_cgR_ne_cgI : cgR ≠ cgI := by decide
@[simp] theorem cg_cgR_ne_cgD : cgR ≠ cgD := by decide
@[simp] theorem cg_cgR_ne_cgE : cgR ≠ cgE := by decide
@[simp] theorem cg_cgR_ne_cgT : cgR ≠ cgT := by decide
@[simp] theorem cg_cgR_ne_cgW : cgR ≠ cgW := by decide
@[simp] theorem cg_cgR_ne_cgU : cgR ≠ cgU := by decide
@[simp] theorem cg_cgR_ne_cgZ : cgR ≠ cgZ := by decide
@[simp] theorem cg_cgR_ne_cgX : cgR ≠ cgX := by decide
@[simp] theorem cg_cgR_ne_kFu : cgR ≠ kFu := by decide
@[simp] theorem cg_kFu_ne_cgR : kFu ≠ cgR := by decide
@[simp] theorem cg_cgR_ne_lFl : cgR ≠ lFl := by decide
@[simp] theorem cg_lFl_ne_cgR : lFl ≠ cgR := by decide
@[simp] theorem cg_cgR_ne_lDh : cgR ≠ lDh := by decide
@[simp] theorem cg_lDh_ne_cgR : lDh ≠ cgR := by decide
@[simp] theorem cg_cgR_ne_lDt : cgR ≠ lDt := by decide
@[simp] theorem cg_lDt_ne_cgR : lDt ≠ cgR := by decide
@[simp] theorem cg_cgR_ne_lDg : cgR ≠ lDg := by decide
@[simp] theorem cg_lDg_ne_cgR : lDg ≠ cgR := by decide
@[simp] theorem cg_cgR_ne_lDi : cgR ≠ lDi := by decide
@[simp] theorem cg_lDi_ne_cgR : lDi ≠ cgR := by decide
@[simp] theorem cg_cgR_ne_lRp : cgR ≠ lRp := by decide
@[simp] theorem cg_lRp_ne_cgR : lRp ≠ cgR := by decide
@[simp] theorem cg_cgR_ne_lRn : cgR ≠ lRn := by decide
@[simp] theorem cg_lRn_ne_cgR : lRn ≠ cgR := by decide
@[simp] theorem cg_cgR_ne_lDir : cgR ≠ lDir := by decide
@[simp] theorem cg_lDir_ne_cgR : lDir ≠ cgR := by decide
@[simp] theorem cg_cgR_ne_lFle : cgR ≠ lFle := by decide
@[simp] theorem cg_lFle_ne_cgR : lFle ≠ cgR := by decide
@[simp] theorem cg_cgR_ne_lKb : cgR ≠ lKb := by decide
@[simp] theorem cg_lKb_ne_cgR : lKb ≠ cgR := by decide
@[simp] theorem cg_cgN_ne_cgG : cgN ≠ cgG := by decide
@[simp] theorem cg_cgN_ne_cgR : cgN ≠ cgR := by decide
@[simp] theorem cg_cgN_ne_cgI : cgN ≠ cgI := by decide
@[simp] theorem cg_cgN_ne_cgD : cgN ≠ cgD := by decide
@[simp] theorem cg_cgN_ne_cgE : cgN ≠ cgE := by decide
@[simp] theorem cg_cgN_ne_cgT : cgN ≠ cgT := by decide
@[simp] theorem cg_cgN_ne_cgW : cgN ≠ cgW := by decide
@[simp] theorem cg_cgN_ne_cgU : cgN ≠ cgU := by decide
@[simp] theorem cg_cgN_ne_cgZ : cgN ≠ cgZ := by decide
@[simp] theorem cg_cgN_ne_cgX : cgN ≠ cgX := by decide
@[simp] theorem cg_cgN_ne_kFu : cgN ≠ kFu := by decide
@[simp] theorem cg_kFu_ne_cgN : kFu ≠ cgN := by decide
@[simp] theorem cg_cgN_ne_lFl : cgN ≠ lFl := by decide
@[simp] theorem cg_lFl_ne_cgN : lFl ≠ cgN := by decide
@[simp] theorem cg_cgN_ne_lDh : cgN ≠ lDh := by decide
@[simp] theorem cg_lDh_ne_cgN : lDh ≠ cgN := by decide
@[simp] theorem cg_cgN_ne_lDt : cgN ≠ lDt := by decide
@[simp] theorem cg_lDt_ne_cgN : lDt ≠ cgN := by decide
@[simp] theorem cg_cgN_ne_lDg : cgN ≠ lDg := by decide
@[simp] theorem cg_lDg_ne_cgN : lDg ≠ cgN := by decide
@[simp] theorem cg_cgN_ne_lDi : cgN ≠ lDi := by decide
@[simp] theorem cg_lDi_ne_cgN : lDi ≠ cgN := by decide
@[simp] theorem cg_cgN_ne_lRp : cgN ≠ lRp := by decide
@[simp] theorem cg_lRp_ne_cgN : lRp ≠ cgN := by decide
@[simp] theorem cg_cgN_ne_lRn : cgN ≠ lRn := by decide
@[simp] theorem cg_lRn_ne_cgN : lRn ≠ cgN := by decide
@[simp] theorem cg_cgN_ne_lDir : cgN ≠ lDir := by decide
@[simp] theorem cg_lDir_ne_cgN : lDir ≠ cgN := by decide
@[simp] theorem cg_cgN_ne_lFle : cgN ≠ lFle := by decide
@[simp] theorem cg_lFle_ne_cgN : lFle ≠ cgN := by decide
@[simp] theorem cg_cgN_ne_lKb : cgN ≠ lKb := by decide
@[simp] theorem cg_lKb_ne_cgN : lKb ≠ cgN := by decide
@[simp] theorem cg_cgI_ne_cgG : cgI ≠ cgG := by decide
@[simp] theorem cg_cgI_ne_cgR : cgI ≠ cgR := by decide
@[simp] theorem cg_cgI_ne_cgN : cgI ≠ cgN := by decide
@[simp] theorem cg_cgI_ne_cgD : cgI ≠ cgD := by decide
@[simp] theorem cg_cgI_ne_cgE : cgI ≠ cgE := by decide
@[simp] theorem cg_cgI_ne_cgT : cgI ≠ cgT := by decide
@[simp] theorem cg_cgI_ne_cgW : cgI ≠ cgW := by decide
@[simp] theorem cg_cgI_ne_cgU : cgI ≠ cgU := by decide
@[simp] theorem cg_cgI_ne_cgZ : cgI ≠ cgZ := by decide
@[simp] theorem cg_cgI_ne_cgX : cgI ≠ cgX := by decide
@[simp] theorem cg_cgI_ne_kFu : cgI ≠ kFu := by decide
@[simp] theorem cg_kFu_ne_cgI : kFu ≠ cgI := by decide
@[simp] theorem cg_cgI_ne_lFl : cgI ≠ lFl := by decide
@[simp] theorem cg_lFl_ne_cgI : lFl ≠ cgI := by decide
@[simp] theorem cg_cgI_ne_lDh : cgI ≠ lDh := by decide
@[simp] theorem cg_lDh_ne_cgI : lDh ≠ cgI := by decide
@[simp] theorem cg_cgI_ne_lDt : cgI ≠ lDt := by decide
@[simp] theorem cg_lDt_ne_cgI : lDt ≠ cgI := by decide
@[simp] theorem cg_cgI_ne_lDg : cgI ≠ lDg := by decide
@[simp] theorem cg_lDg_ne_cgI : lDg ≠ cgI := by decide
@[simp] theorem cg_cgI_ne_lDi : cgI ≠ lDi := by decide
@[simp] theorem cg_lDi_ne_cgI : lDi ≠ cgI := by decide
@[simp] theorem cg_cgI_ne_lRp : cgI ≠ lRp := by decide
@[simp] theorem cg_lRp_ne_cgI : lRp ≠ cgI := by decide
@[simp] theorem cg_cgI_ne_lRn : cgI ≠ lRn := by decide
@[simp] theorem cg_lRn_ne_cgI : lRn ≠ cgI := by decide
@[simp] theorem cg_cgI_ne_lDir : cgI ≠ lDir := by decide
@[simp] theorem cg_lDir_ne_cgI : lDir ≠ cgI := by decide
@[simp] theorem cg_cgI_ne_lFle : cgI ≠ lFle := by decide
@[simp] theorem cg_lFle_ne_cgI : lFle ≠ cgI := by decide
@[simp] theorem cg_cgI_ne_lKb : cgI ≠ lKb := by decide
@[simp] theorem cg_lKb_ne_cgI : lKb ≠ cgI := by decide
@[simp] theorem cg_cgD_ne_cgG : cgD ≠ cgG := by decide
@[simp] theorem cg_cgD_ne_cgR : cgD ≠ cgR := by decide
@[simp] theorem cg_cgD_ne_cgN : cgD ≠ cgN := by decide
@[simp] theorem cg_cgD_ne_cgI : cgD ≠ cgI := by decide
@[simp] theorem cg_cgD_ne_cgE : cgD ≠ cgE := by decide
@[simp] theorem cg_cgD_ne_cgT : cgD ≠ cgT := by decide
@[simp] theorem cg_cgD_ne_cgW : cgD ≠ cgW := by decide
@[simp] theorem cg_cgD_ne_cgU : cgD ≠ cgU := by decide
@[simp] theorem cg_cgD_ne_cgZ : cgD ≠ cgZ := by decide
@[simp] theorem cg_cgD_ne_cgX : cgD ≠ cgX := by decide
@[simp] theorem cg_cgD_ne_kFu : cgD ≠ kFu := by decide
@[simp] theorem cg_kFu_ne_cgD : kFu ≠ cgD := by decide
@[simp] theorem cg_cgD_ne_lFl : cgD ≠ lFl := by decide
@[simp] theorem cg_lFl_ne_cgD : lFl ≠ cgD := by decide
@[simp] theorem cg_cgD_ne_lDh : cgD ≠ lDh := by decide
@[simp] theorem cg_lDh_ne_cgD : lDh ≠ cgD := by decide
@[simp] theorem cg_cgD_ne_lDt : cgD ≠ lDt := by decide
@[simp] theorem cg_lDt_ne_cgD : lDt ≠ cgD := by decide
@[simp] theorem cg_cgD_ne_lDg : cgD ≠ lDg := by decide
@[simp] theorem cg_lDg_ne_cgD : lDg ≠ cgD := by decide
@[simp] theorem cg_cgD_ne_lDi : cgD ≠ lDi := by decide
@[simp] theorem cg_lDi_ne_cgD : lDi ≠ cgD := by decide
@[simp] theorem cg_cgD_ne_lRp : cgD ≠ lRp := by decide
@[simp] theorem cg_lRp_ne_cgD : lRp ≠ cgD := by decide
@[simp] theorem cg_cgD_ne_lRn : cgD ≠ lRn := by decide
@[simp] theorem cg_lRn_ne_cgD : lRn ≠ cgD := by decide
@[simp] theorem cg_cgD_ne_lDir : cgD ≠ lDir := by decide
@[simp] theorem cg_lDir_ne_cgD : lDir ≠ cgD := by decide
@[simp] theorem cg_cgD_ne_lFle : cgD ≠ lFle := by decide
@[simp] theorem cg_lFle_ne_cgD : lFle ≠ cgD := by decide
@[simp] theorem cg_cgD_ne_lKb : cgD ≠ lKb := by decide
@[simp] theorem cg_lKb_ne_cgD : lKb ≠ cgD := by decide
@[simp] theorem cg_cgE_ne_cgG : cgE ≠ cgG := by decide
@[simp] theorem cg_cgE_ne_cgR : cgE ≠ cgR := by decide
@[simp] theorem cg_cgE_ne_cgN : cgE ≠ cgN := by decide
@[simp] theorem cg_cgE_ne_cgI : cgE ≠ cgI := by decide
@[simp] theorem cg_cgE_ne_cgD : cgE ≠ cgD := by decide
@[simp] theorem cg_cgE_ne_cgT : cgE ≠ cgT := by decide
@[simp] theorem cg_cgE_ne_cgW : cgE ≠ cgW := by decide
@[simp] theorem cg_cgE_ne_cgU : cgE ≠ cgU := by decide
@[simp] theorem cg_cgE_ne_cgZ : cgE ≠ cgZ := by decide
@[simp] theorem cg_cgE_ne_cgX : cgE ≠ cgX := by decide
@[simp] theorem cg_cgE_ne_kFu : cgE ≠ kFu := by decide
@[simp] theorem cg_kFu_ne_cgE : kFu ≠ cgE := by decide
@[simp] theorem cg_cgE_ne_lFl : cgE ≠ lFl := by decide
@[simp] theorem cg_lFl_ne_cgE : lFl ≠ cgE := by decide
@[simp] theorem cg_cgE_ne_lDh : cgE ≠ lDh := by decide
@[simp] theorem cg_lDh_ne_cgE : lDh ≠ cgE := by decide
@[simp] theorem cg_cgE_ne_lDt : cgE ≠ lDt := by decide
@[simp] theorem cg_lDt_ne_cgE : lDt ≠ cgE := by decide
@[simp] theorem cg_cgE_ne_lDg : cgE ≠ lDg := by decide
@[simp] theorem cg_lDg_ne_cgE : lDg ≠ cgE := by decide
@[simp] theorem cg_cgE_ne_lDi : cgE ≠ lDi := by decide
@[simp] theorem cg_lDi_ne_cgE : lDi ≠ cgE := by decide
@[simp] theorem cg_cgE_ne_lRp : cgE ≠ lRp := by decide
@[simp] theorem cg_lRp_ne_cgE : lRp ≠ cgE := by decide
@[simp] theorem cg_cgE_ne_lRn : cgE ≠ lRn := by decide
@[simp] theorem cg_lRn_ne_cgE : lRn ≠ cgE := by decide
@[simp] theorem cg_cgE_ne_lDir : cgE ≠ lDir := by decide
@[simp] theorem cg_lDir_ne_cgE : lDir ≠ cgE := by decide
@[simp] theorem cg_cgE_ne_lFle : cgE ≠ lFle := by decide
@[simp] theorem cg_lFle_ne_cgE : lFle ≠ cgE := by decide
@[simp] theorem cg_cgE_ne_lKb : cgE ≠ lKb := by decide
@[simp] theorem cg_lKb_ne_cgE : lKb ≠ cgE := by decide
@[simp] theorem cg_cgT_ne_cgG : cgT ≠ cgG := by decide
@[simp] theorem cg_cgT_ne_cgR : cgT ≠ cgR := by decide
@[simp] theorem cg_cgT_ne_cgN : cgT ≠ cgN := by decide
@[simp] theorem cg_cgT_ne_cgI : cgT ≠ cgI := by decide
@[simp] theorem cg_cgT_ne_cgD : cgT ≠ cgD := by decide
@[simp] theorem cg_cgT_ne_cgE : cgT ≠ cgE := by decide
@[simp] theorem cg_cgT_ne_cgW : cgT ≠ cgW := by decide
@[simp] theorem cg_cgT_ne_cgU : cgT ≠ cgU := by decide
@[simp] theorem cg_cgT_ne_cgZ : cgT ≠ cgZ := by decide
@[simp] theorem cg_cgT_ne_cgX : cgT ≠ cgX := by decide
@[simp] theorem cg_cgT_ne_kFu : cgT ≠ kFu := by decide
@[simp] theorem cg_kFu_ne_cgT : kFu ≠ cgT := by decide
@[simp] theorem cg_cgT_ne_lFl : cgT ≠ lFl := by decide
@[simp] theorem cg_lFl_ne_cgT : lFl ≠ cgT := by decide
@[simp] theorem cg_cgT_ne_lDh : cgT ≠ lDh := by decide
@[simp] theorem cg_lDh_ne_cgT : lDh ≠ cgT := by decide
@[simp] theorem cg_cgT_ne_lDt : cgT ≠ lDt := by decide
@[simp] theorem cg_lDt_ne_cgT : lDt ≠ cgT := by decide
@[simp] theorem cg_cgT_ne_lDg : cgT ≠ lDg := by decide
@[simp] theorem cg_lDg_ne_cgT : lDg ≠ cgT := by decide
@[simp] theorem cg_cgT_ne_lDi : cgT ≠ lDi := by decide
@[simp] theorem cg_lDi_ne_cgT : lDi ≠ cgT := by decide
@[simp] theorem cg_cgT_ne_lRp : cgT ≠ lRp := by decide
@[simp] theorem cg_lRp_ne_cgT : lRp ≠ cgT := by decide
@[simp] theorem cg_cgT_ne_lRn : cgT ≠ lRn := by decide
@[simp] theorem cg_lRn_ne_cgT : lRn ≠ cgT := by decide
@[simp] theorem cg_cgT_ne_lDir : cgT ≠ lDir := by decide
@[simp] theorem cg_lDir_ne_cgT : lDir ≠ cgT := by decide
@[simp] theorem cg_cgT_ne_lFle : cgT ≠ lFle := by decide
@[simp] theorem cg_lFle_ne_cgT : lFle ≠ cgT := by decide
@[simp] theorem cg_cgT_ne_lKb : cgT ≠ lKb := by decide
@[simp] theorem cg_lKb_ne_cgT : lKb ≠ cgT := by decide
@[simp] theorem cg_cgW_ne_cgG : cgW ≠ cgG := by decide
@[simp] theorem cg_cgW_ne_cgR : cgW ≠ cgR := by decide
@[simp] theorem cg_cgW_ne_cgN : cgW ≠ cgN := by decide
@[simp] theorem cg_cgW_ne_cgI : cgW ≠ cgI := by decide
@[simp] theorem cg_cgW_ne_cgD : cgW ≠ cgD := by decide
@[simp] theorem cg_cgW_ne_cgE : cgW ≠ cgE := by decide
@[simp] theorem cg_cgW_ne_cgT : cgW ≠ cgT := by decide
@[simp] theorem cg_cgW_ne_cgU : cgW ≠ cgU := by decide
@[simp] theorem cg_cgW_ne_cgZ : cgW ≠ cgZ := by decide
@[simp] theorem cg_cgW_ne_cgX : cgW ≠ cgX := by decide
@[simp] theorem cg_cgW_ne_kFu : cgW ≠ kFu := by decide
@[simp] theorem cg_kFu_ne_cgW : kFu ≠ cgW := by decide
@[simp] theorem cg_cgW_ne_lFl : cgW ≠ lFl := by decide
@[simp] theorem cg_lFl_ne_cgW : lFl ≠ cgW := by decide
@[simp] theorem cg_cgW_ne_lDh : cgW ≠ lDh := by decide
@[simp] theorem cg_lDh_ne_cgW : lDh ≠ cgW := by decide
@[simp] theorem cg_cgW_ne_lDt : cgW ≠ lDt := by decide
@[simp] theorem cg_lDt_ne_cgW : lDt ≠ cgW := by decide
@[simp] theorem cg_cgW_ne_lDg : cgW ≠ lDg := by decide
@[simp] theorem cg_lDg_ne_cgW : lDg ≠ cgW := by decide
@[simp] theorem cg_cgW_ne_lDi : cgW ≠ lDi := by decide
@[simp] theorem cg_lDi_ne_cgW : lDi ≠ cgW := by decide
@[simp] theorem cg_cgW_ne_lRp : cgW ≠ lRp := by decide
@[simp] theorem cg_lRp_ne_cgW : lRp ≠ cgW := by decide
@[simp] theorem cg_cgW_ne_lRn : cgW ≠ lRn := by decide
@[simp] theorem cg_lRn_ne_cgW : lRn ≠ cgW := by decide
@[simp] theorem cg_cgW_ne_lDir : cgW ≠ lDir := by decide
@[simp] theorem cg_lDir_ne_cgW : lDir ≠ cgW := by decide
@[simp] theorem cg_cgW_ne_lFle : cgW ≠ lFle := by decide
@[simp] theorem cg_lFle_ne_cgW : lFle ≠ cgW := by decide
@[simp] theorem cg_cgW_ne_lKb : cgW ≠ lKb := by decide
@[simp] theorem cg_lKb_ne_cgW : lKb ≠ cgW := by decide
@[simp] theorem cg_cgU_ne_cgG : cgU ≠ cgG := by decide
@[simp] theorem cg_cgU_ne_cgR : cgU ≠ cgR := by decide
@[simp] theorem cg_cgU_ne_cgN : cgU ≠ cgN := by decide
@[simp] theorem cg_cgU_ne_cgI : cgU ≠ cgI := by decide
@[simp] theorem cg_cgU_ne_cgD : cgU ≠ cgD := by decide
@[simp] theorem cg_cgU_ne_cgE : cgU ≠ cgE := by decide
@[simp] theorem cg_cgU_ne_cgT : cgU ≠ cgT := by decide
@[simp] theorem cg_cgU_ne_cgW : cgU ≠ cgW := by decide
@[simp] theorem cg_cgU_ne_cgZ : cgU ≠ cgZ := by decide
@[simp] theorem cg_cgU_ne_cgX : cgU ≠ cgX := by decide
@[simp] theorem cg_cgU_ne_kFu : cgU ≠ kFu := by decide
@[simp] theorem cg_kFu_ne_cgU : kFu ≠ cgU := by decide
@[simp] theorem cg_cgU_ne_lFl : cgU ≠ lFl := by decide
@[simp] theorem cg_lFl_ne_cgU : lFl ≠ cgU := by decide
@[simp] theorem cg_cgU_ne_lDh : cgU ≠ lDh := by decide
@[simp] theorem cg_lDh_ne_cgU : lDh ≠ cgU := by decide
@[simp] theorem cg_cgU_ne_lDt : cgU ≠ lDt := by decide
@[simp] theorem cg_lDt_ne_cgU : lDt ≠ cgU := by decide
@[simp] theorem cg_cgU_ne_lDg : cgU ≠ lDg := by decide
@[simp] theorem cg_lDg_ne_cgU : lDg ≠ cgU := by decide
@[simp] theorem cg_cgU_ne_lDi : cgU ≠ lDi := by decide
@[simp] theorem cg_lDi_ne_cgU : lDi ≠ cgU := by decide
@[simp] theorem cg_cgU_ne_lRp : cgU ≠ lRp := by decide
@[simp] theorem cg_lRp_ne_cgU : lRp ≠ cgU := by decide
@[simp] theorem cg_cgU_ne_lRn : cgU ≠ lRn := by decide
@[simp] theorem cg_lRn_ne_cgU : lRn ≠ cgU := by decide
@[simp] theorem cg_cgU_ne_lDir : cgU ≠ lDir := by decide
@[simp] theorem cg_lDir_ne_cgU : lDir ≠ cgU := by decide
@[simp] theorem cg_cgU_ne_lFle : cgU ≠ lFle := by decide
@[simp] theorem cg_lFle_ne_cgU : lFle ≠ cgU := by decide
@[simp] theorem cg_cgU_ne_lKb : cgU ≠ lKb := by decide
@[simp] theorem cg_lKb_ne_cgU : lKb ≠ cgU := by decide
@[simp] theorem cg_cgZ_ne_cgG : cgZ ≠ cgG := by decide
@[simp] theorem cg_cgZ_ne_cgR : cgZ ≠ cgR := by decide
@[simp] theorem cg_cgZ_ne_cgN : cgZ ≠ cgN := by decide
@[simp] theorem cg_cgZ_ne_cgI : cgZ ≠ cgI := by decide
@[simp] theorem cg_cgZ_ne_cgD : cgZ ≠ cgD := by decide
@[simp] theorem cg_cgZ_ne_cgE : cgZ ≠ cgE := by decide
@[simp] theorem cg_cgZ_ne_cgT : cgZ ≠ cgT := by decide
@[simp] theorem cg_cgZ_ne_cgW : cgZ ≠ cgW := by decide
@[simp] theorem cg_cgZ_ne_cgU : cgZ ≠ cgU := by decide
@[simp] theorem cg_cgZ_ne_cgX : cgZ ≠ cgX := by decide
@[simp] theorem cg_cgZ_ne_kFu : cgZ ≠ kFu := by decide
@[simp] theorem cg_kFu_ne_cgZ : kFu ≠ cgZ := by decide
@[simp] theorem cg_cgZ_ne_lFl : cgZ ≠ lFl := by decide
@[simp] theorem cg_lFl_ne_cgZ : lFl ≠ cgZ := by decide
@[simp] theorem cg_cgZ_ne_lDh : cgZ ≠ lDh := by decide
@[simp] theorem cg_lDh_ne_cgZ : lDh ≠ cgZ := by decide
@[simp] theorem cg_cgZ_ne_lDt : cgZ ≠ lDt := by decide
@[simp] theorem cg_lDt_ne_cgZ : lDt ≠ cgZ := by decide
@[simp] theorem cg_cgZ_ne_lDg : cgZ ≠ lDg := by decide
@[simp] theorem cg_lDg_ne_cgZ : lDg ≠ cgZ := by decide
@[simp] theorem cg_cgZ_ne_lDi : cgZ ≠ lDi := by decide
@[simp] theorem cg_lDi_ne_cgZ : lDi ≠ cgZ := by decide
@[simp] theorem cg_cgZ_ne_lRp : cgZ ≠ lRp := by decide
@[simp] theorem cg_lRp_ne_cgZ : lRp ≠ cgZ := by decide
@[simp] theorem cg_cgZ_ne_lRn : cgZ ≠ lRn := by decide
@[simp] theorem cg_lRn_ne_cgZ : lRn ≠ cgZ := by decide
@[simp] theorem cg_cgZ_ne_lDir : cgZ ≠ lDir := by decide
@[simp] theorem cg_lDir_ne_cgZ : lDir ≠ cgZ := by decide
@[simp] theorem cg_cgZ_ne_lFle : cgZ ≠ lFle := by decide
@[simp] theorem cg_lFle_ne_cgZ : lFle ≠ cgZ := by decide
@[simp] theorem cg_cgZ_ne_lKb : cgZ ≠ lKb := by decide
@[simp] theorem cg_lKb_ne_cgZ : lKb ≠ cgZ := by decide
@[simp] theorem cg_cgX_ne_cgG : cgX ≠ cgG := by decide
@[simp] theorem cg_cgX_ne_cgR : cgX ≠ cgR := by decide
@[simp] theorem cg_cgX_ne_cgN : cgX ≠ cgN := by decide
@[simp] theorem cg_cgX_ne_cgI : cgX ≠ cgI := by decide
@[simp] theorem cg_cgX_ne_cgD : cgX ≠ cgD := by decide
@[simp] theorem cg_cgX_ne_cgE : cgX ≠ cgE := by decide
@[simp] theorem cg_cgX_ne_cgT : cgX ≠ cgT := by decide
@[simp] theorem cg_cgX_ne_cgW : cgX ≠ cgW := by decide
@[simp] theorem cg_cgX_ne_cgU : cgX ≠ cgU := by decide
@[simp] theorem cg_cgX_ne_cgZ : cgX ≠ cgZ := by decide
@[simp] theorem cg_cgX_ne_kFu : cgX ≠ kFu := by decide
@[simp] theorem cg_kFu_ne_cgX : kFu ≠ cgX := by decide
@[simp] theorem cg_cgX_ne_lFl : cgX ≠ lFl := by decide
@[simp] theorem cg_lFl_ne_cgX : lFl ≠ cgX := by decide
@[simp] theorem cg_cgX_ne_lDh : cgX ≠ lDh := by decide
@[simp] theorem cg_lDh_ne_cgX : lDh ≠ cgX := by decide
@[simp] theorem cg_cgX_ne_lDt : cgX ≠ lDt := by decide
@[simp] theorem cg_lDt_ne_cgX : lDt ≠ cgX := by decide
@[simp] theorem cg_cgX_ne_lDg : cgX ≠ lDg := by decide
@[simp] theorem cg_lDg_ne_cgX : lDg ≠ cgX := by decide
@[simp] theorem cg_cgX_ne_lDi : cgX ≠ lDi := by decide
@[simp] theorem cg_lDi_ne_cgX : lDi ≠ cgX := by decide
@[simp] theorem cg_cgX_ne_lRp : cgX ≠ lRp := by decide
@[simp] theorem cg_lRp_ne_cgX : lRp ≠ cgX := by decide
@[simp] theorem cg_cgX_ne_lRn : cgX ≠ lRn := by decide
@[simp] theorem cg_lRn_ne_cgX : lRn ≠ cgX := by decide
@[simp] theorem cg_cgX_ne_lDir : cgX ≠ lDir := by decide
@[simp] theorem cg_lDir_ne_cgX : lDir ≠ cgX := by decide
@[simp] theorem cg_cgX_ne_lFle : cgX ≠ lFle := by decide
@[simp] theorem cg_lFle_ne_cgX : lFle ≠ cgX := by decide
@[simp] theorem cg_cgX_ne_lKb : cgX ≠ lKb := by decide
@[simp] theorem cg_lKb_ne_cgX : lKb ≠ cgX := by decide

/-- The rows as words. -/
def rowsW : List (Nat × EIdx) → List (BitVec 64)
  | [] => []
  | p :: ps => BitVec.ofNat 64 p.1 :: Enc.idxW p.2 :: rowsW ps

theorem rowsW_length : ∀ rows : List (Nat × EIdx), (rowsW rows).length = 2 * rows.length
  | [] => rfl
  | _ :: ps => by simp [rowsW, rowsW_length ps]; omega

theorem rowsW_get : ∀ (rows : List (Nat × EIdx)) (i : Nat) (hi : i < rows.length),
    (rowsW rows)[2 * i]? = some (BitVec.ofNat 64 rows[i].1) ∧ (rowsW rows)[2 * i + 1]? = some (Enc.idxW rows[i].2)
  | [], _, hi => absurd hi (by simp)
  | p :: ps, 0, _ => by simp [rowsW]
  | p :: ps, i + 1, hi => by
    have := rowsW_get ps i (by simpa using hi)
    simp only [rowsW, List.getElem_cons_succ]
    rw [show 2 * (i + 1) = 2 * i + 2 by omega, show 2 * i + 2 + 1 = 2 * i + 1 + 2 by omega]
    simpa using this

theorem cellA_idx16 (C : Ctx) (o i : Nat) :
    cellA C o + (BitVec.ofNat 64 i * 16#64 + 8#64) = cellA C (o + 1 + 2 * i) := by
  have e : BitVec.ofNat 64 i * 16#64 + 8#64 = BitVec.ofNat 64 (8 * (1 + 2 * i)) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul]; omega
  rw [e]; unfold cellA; rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega

theorem cellA_idx16' (C : Ctx) (o i : Nat) :
    cellA C o + (BitVec.ofNat 64 i * 16#64 + 16#64) = cellA C (o + 1 + (2 * i + 1)) := by
  have e : BitVec.ofNat 64 i * 16#64 + 16#64 = BitVec.ofNat 64 (8 * (1 + (2 * i + 1))) := by
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_mul]; omega
  rw [e]; unfold cellA; rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega

def cgParams : List MlS := [kFu, cgG, cgR, cgN, cgI]
def cgLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, cgD, cgE, cgT, cgW, cgU, cgZ, cgX]

def cgBody : ProgHOL 64 := prologue cgLocals
  (.ite (.cmp .lower (vv cgI) (vv cgN))
    (.seq (.assign .local cgD (.load .one (.op .add [vv cgR, .op .add [.panop .mul [vv cgI, .const 16], .const 8]])))
    (.seq (.assign .local cgE (.load .one (.op .add [vv cgR, .op .add [.panop .mul [vv cgI, .const 16], .const 16]])))
    (.seq (.call (some (some (.local, cgT), none)) fIO [vv kFu, vv cgD, vv cgE])
    (.seq (.call (some (some (.local, cgW), none)) fW [vv kFu, vv cgD, vv cgT])
    (.ite (tagIsE cgW 2)
      (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv cgW)) (.seq eViewP
      (.seq (.assign .local cgU (.load .one (vv lRp)))
      (.seq (.call (some (some (.local, cgZ), none)) fZw [vv cgG, vv cgU])
      (.ite (vv cgZ)
        (.seq (.call (some (some (.local, cgX), none)) fCg [vv kFu, vv cgG, vv cgR, vv cgN, .op .add [vv cgI, .const 1]])
          (.return (vv cgX)))
        hang))))))
      hang)))))
    (.return (.const 0)))

section
variable {σ : Type}

/-- A `Unit` answer; the heap may have grown. -/
def PostU (C : Ctx) (a : Unit) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st

theorem postU_locals (C : Ctx) : ∀ (a : Unit) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostU C a w s' st → PostU C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hsr⟩ => ⟨H', hp, sr_of_eq hsr rfl rfl rfl rfl⟩

theorem cg_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cgLocals → (ctxEnv C ++ cgParams.zip vals).get x = none :=
  Knot.params_none C cgLocals cgParams vals (by decide) (by decide)

theorem zwCodes_H {C : Ctx} (hc : ZwCodes C) (H : List (BitVec 64)) : ZwCodes (ctxH C H) :=
  ⟨hc.neq, hc.nz0, hc.zq, hc.za, hc.zw⟩

structure CgCodes (C : Ctx) : Prop where
  io : C.code.lookup fIO = some (pmap kParams, inferIOE C fIOB, .one)
  w : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one)
  zw : ZwCodes C
  self : C.code.lookup fCg = some (cgParams.map (fun p => (p, ShapeHOL.one)), cgBody, .one)

theorem cg_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) (hok : CtxOK C) (hc : CgCodes C)
    (gs : Level) (gh : LIdx) (hfl : denoteL C.St.ls gh = some gs)
    (hIO : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → d' < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (inferIOE C fIOB) s1 ((knot mode C n).inferIO d' e')
      (PostK (ctxH C H)))
    (hW : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → d' < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d' e')
      (PostK (ctxH C H)))
    (rows : List (Nat × EIdx)) (o : Nat) (H0 : List (BitVec 64)) (hp0 : C.H <+: H0)
    (hb : BlkAt H0 o (rowsW rows)) (hrl : rows.length < 2 ^ 58) (hrd : ∀ p ∈ rows, p.1 < 2 ^ 63) :
    ∀ m i (H : List (BitVec 64)) (s : AState), H0 <+: H → rows.length - i = m → i ≤ rows.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (cgParams.zip [BitVec.ofNat 64 n, Enc.idxW gh, cellA C o,
        BitVec.ofNat 64 rows.length, BitVec.ofNat 64 i])) cgBody s
        (checkGuardRows (knot mode C n) gs rows.toArray i) (PostU (ctxH C H)) := by
  intro m
  induction m with
  | zero =>
    intro i H s hp hk hi
    refine specR_prologue (postU_locals _) (cg_none _ _) ?_
    rw [checkGuardRows, dite_eq_right (by simp; omega)]
    have hlw := word_lt_iff i rows.length (by unfold B; omega) (by unfold B; omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, cgParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
      (not_congr hlw).mpr (by omega)]) (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ m ih =>
    intro i H s hp hk hi
    have hlt : i < rows.length := by omega
    refine specR_prologue (postU_locals _) (cg_none _ _) ?_
    rw [checkGuardRows, dite_eq_left (by simpa using hlt)]
    have hlw := word_lt_iff i rows.length (by unfold B; omega) (by unfold B; omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, cgParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
      hlw.mpr hlt]) (fun _ => ?_) (fun h => absurd h (by decide))
    have hb' := blkAt_mono hb hp
    have hrw := rowsW_get rows i hlt
    have hrlen := rowsW_length rows
    have h1 : (ctxH C H).H[o + 1 + 2 * i]? = some (BitVec.ofNat 64 rows[i].1) := by
      show H[o + 1 + 2 * i]? = _
      have := hb'.2 (2 * i) (by omega); rw [this]; exact (List.getElem?_eq_getElem _).symm.trans hrw.1
    have h2 : (ctxH C H).H[o + 1 + (2 * i + 1)]? = some (Enc.idxW rows[i].2) := by
      show H[o + 1 + (2 * i + 1)]? = _
      have := hb'.2 (2 * i + 1) (by omega); rw [this]; exact (List.getElem?_eq_getElem _).symm.trans hrw.2
    refine UD.specR_heapLoadI' (C := ctxH C H) cgD _ (o + 1 + 2 * i) _ h1 (by decide)
      (by simp +decide [sev, Env.get, cgParams, ctxEnv]; exact cellA_idx16 C o i) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) cgE _ (o + 1 + (2 * i + 1)) _ h2 (by decide)
      (by simp +decide [sev, Env.get, cgParams, ctxEnv]; exact cellA_idx16' C o i) ?_
    simp only [List.getElem_toArray]
    rcases hri : rows[i] with ⟨d, dom⟩
    have hd63 : d < 2 ^ 63 := by have := hrd rows[i] (List.getElem_mem hlt); rw [hri] at this; exact this
    simp only [hri] at h1 h2 ⊢
    refine Big.specR_callKC (C := ctxH C H) cgT fIO kParams [vv kFu, vv cgD, vv cgE] (inferIOE C fIOB)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW dom] (by decide) rfl (by decide) hc.io
      ⟨by simp +decide [Env.get, cgParams, ctxEnv], by simp, by simp, trivial⟩ (hIO H s d dom (hp0.trans hp) hd63) (fun t s2 H2 hp2 hrun2 => ?_)
    refine Big.specR_callKC (C := ctxH C H2) cgW fW kParams [vv kFu, vv cgD, vv cgT] (whnfE C fWB)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW t] (by decide) rfl (by decide) hc.w
      ⟨by simp +decide [Env.get, cgParams, ctxEnv], by simp, by simp, trivial⟩ (hW H2 s2 d t (hp0.trans (hp.trans hp2)) hd63) (fun w s3 H3 hp3 hrun3 => ?_)
    refine Knot.specR_tagIteV cgW w 2 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
    swap
    · rw [ite_eq_right (show ¬ (w.tag == ETag.sort) = true by simpa [ETag.sort] using htg)]
      exact specR_hangI
    rw [ite_eq_left (show (w.tag == ETag.sort) = true by simp [htg, ETag.sort])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv cgW) (Enc.idxW w) (by decide) (by simp) ?_
    refine specR_viewP (C := ctxH C H3) w (by simp) (by simp +decide [Env.get] <;> rfl)
      (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun vw P hv htn _ => ?_)
    have h2' : vw.tagN = 2 := by rw [htn, htg]; rfl
    obtain ⟨u, rfl⟩ : ∃ u, vw = .sort u := by cases vw <;> simp [ENodeView.tagN] at h2' ⊢
    have hvs : s3.store.viewSort w = some u := viewSort_of_view (by rw [htg]; rfl) hv
    refine specR_runBind (show ConRon.Arena.viewSort w s3 = .ok (some u, s3) by
      show Except.ok (s3.store.viewSort w, s3) = _; rw [hvs]) ?_
    dsimp only
    refine specR_loadI' cgU (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW u) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encSort] using wordsAt_mem0 P (Enc.idxW u) [] []) ?_
    refine specR_dropM ?_
    refine specR_atEntry fun t3 ht3 => ?_
    obtain ⟨ul, hul⟩ := sr_sortDen ht3.sr w u hv
    obtain ⟨X, hx, hX⟩ := readLevelM_runC u s3 ul ht3.sr.cok.rl hul
    refine specR_quiet hx rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl (fun hc => cachesOK_readLC hc X hX) ?_
    refine specR_callPure (C := ctxH C H3) cgZ fZw zwParams [vv cgG, vv cgU] zwBody [Enc.idxW gh, Enc.idxW u]
      (ConLeche.Level.zeroWhereZero gs ul) (by decide) rfl (by decide) hc.zw.zw
      ⟨by simp +decide [Env.get, cgParams, ctxEnv], by simp, trivial⟩ (PostBS (ctxH C H3) _) (fun b w _ H' => H' = H3 ∧ w = boolW b)
      (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨H3, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
      (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu zwParams _ rfl hlk)
        (zw_spec (ctxH C H3) (zwCodes_H hc.zw H3) { s3 with caches := { s3.caches with readLC := X } } (sr_lwf ht3.sr : LStoreWF s3.store.ls) gs ul gh u (denoteL_ext hfl ht3.sr.floor : denoteL s3.store.ls gh = some gs) hul))
      (fun wz H4 _ ⟨eH, hwz⟩ => ?_)
    subst H4; subst hwz
    cases hz : ConLeche.Level.zeroWhereZero gs ul
    · refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_hangI
    refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [↓reduceIte]
    refine specR_congr (m' := checkGuardRows (knot mode C n) gs rows.toArray (i + 1) >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H3) cgX fCg cgParams
      [vv kFu, vv cgG, vv cgR, vv cgN, .op .add [vv cgI, .const 1]] cgBody
      [BitVec.ofNat 64 n, Enc.idxW gh, cellA C o, BitVec.ofNat 64 rows.length, BitVec.ofNat 64 (i + 1)]
      (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [Env.get, cgParams, ctxEnv], by simp +decide [Env.get, cgParams, ctxEnv], by simp +decide [Env.get, cgParams, ctxEnv] <;> rfl, by simp +decide [Env.get, cgParams, ctxEnv], by simp +decide [sev, Env.get, cgParams, ctxEnv]; exact word_add1_eq i,
        trivial⟩
      (PostU (ctxH C H3)) (fun a w _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
      (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu cgParams _ rfl hlk)
        (ih (i + 1) H3 _ (hp.trans (hp2.trans hp3)) (by omega) (by omega)))
      (fun r w s5 H5 hp5 _ => ?_)
    exact specR_returnI _ w (by simp) (fun t ht => ⟨H5, hp2.trans (hp3.trans hp5), sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
