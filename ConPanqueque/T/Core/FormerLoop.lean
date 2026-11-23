import ConPanqueque.T.Core.RescueEta
import ConPanqueque.T.Ex.InstSpine
import ConPanqueque.T.Core.FormerSort
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `formerSortLoop`: the sort a family's type reaches after its binders

`whnf` (the knot's), then at `n = 0` a sort's level (`optW`-style, `0` for none), at `n + 1` a `∀` opened with a
fresh free variable at the depth (`internFVar`, `instantiate1Fast`) and the loop again at depth `d + 1`.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def fqN := ofString "fqn"
def fqE := ofString "fqe"
def fqW := ofString "fqw"
def fqU := ofString "fqu"
def fqT := ofString "fqt"
def fqB := ofString "fqb"
def fqF := ofString "fqf"
def fqB2 := ofString "fqb2"
def fqR := ofString "fqr"
def fFsl := ofString "formerSortLoop"

@[simp] theorem fq_fqN_ne_fqE : fqN ≠ fqE := by decide
@[simp] theorem fq_fqN_ne_fqW : fqN ≠ fqW := by decide
@[simp] theorem fq_fqN_ne_fqU : fqN ≠ fqU := by decide
@[simp] theorem fq_fqN_ne_fqT : fqN ≠ fqT := by decide
@[simp] theorem fq_fqN_ne_fqB : fqN ≠ fqB := by decide
@[simp] theorem fq_fqN_ne_fqF : fqN ≠ fqF := by decide
@[simp] theorem fq_fqN_ne_fqB2 : fqN ≠ fqB2 := by decide
@[simp] theorem fq_fqN_ne_fqR : fqN ≠ fqR := by decide
@[simp] theorem fq_fqN_ne_kFu : fqN ≠ kFu := by decide
@[simp] theorem fq_fqN_ne_kD : fqN ≠ kD := by decide
@[simp] theorem fq_fqN_ne_lFl : fqN ≠ lFl := by decide
@[simp] theorem fq_fqN_ne_lDh : fqN ≠ lDh := by decide
@[simp] theorem fq_fqN_ne_lDt : fqN ≠ lDt := by decide
@[simp] theorem fq_fqN_ne_lDg : fqN ≠ lDg := by decide
@[simp] theorem fq_fqN_ne_lDi : fqN ≠ lDi := by decide
@[simp] theorem fq_fqN_ne_lRp : fqN ≠ lRp := by decide
@[simp] theorem fq_fqN_ne_lRn : fqN ≠ lRn := by decide
@[simp] theorem fq_fqN_ne_lKb : fqN ≠ lKb := by decide
@[simp] theorem fq_fqN_ne_lFle : fqN ≠ lFle := by decide
@[simp] theorem fq_fqN_ne_lDir : fqN ≠ lDir := by decide
@[simp] theorem fq_fqE_ne_fqN : fqE ≠ fqN := by decide
@[simp] theorem fq_fqE_ne_fqW : fqE ≠ fqW := by decide
@[simp] theorem fq_fqE_ne_fqU : fqE ≠ fqU := by decide
@[simp] theorem fq_fqE_ne_fqT : fqE ≠ fqT := by decide
@[simp] theorem fq_fqE_ne_fqB : fqE ≠ fqB := by decide
@[simp] theorem fq_fqE_ne_fqF : fqE ≠ fqF := by decide
@[simp] theorem fq_fqE_ne_fqB2 : fqE ≠ fqB2 := by decide
@[simp] theorem fq_fqE_ne_fqR : fqE ≠ fqR := by decide
@[simp] theorem fq_fqE_ne_kFu : fqE ≠ kFu := by decide
@[simp] theorem fq_fqE_ne_kD : fqE ≠ kD := by decide
@[simp] theorem fq_fqE_ne_lFl : fqE ≠ lFl := by decide
@[simp] theorem fq_fqE_ne_lDh : fqE ≠ lDh := by decide
@[simp] theorem fq_fqE_ne_lDt : fqE ≠ lDt := by decide
@[simp] theorem fq_fqE_ne_lDg : fqE ≠ lDg := by decide
@[simp] theorem fq_fqE_ne_lDi : fqE ≠ lDi := by decide
@[simp] theorem fq_fqE_ne_lRp : fqE ≠ lRp := by decide
@[simp] theorem fq_fqE_ne_lRn : fqE ≠ lRn := by decide
@[simp] theorem fq_fqE_ne_lKb : fqE ≠ lKb := by decide
@[simp] theorem fq_fqE_ne_lFle : fqE ≠ lFle := by decide
@[simp] theorem fq_fqE_ne_lDir : fqE ≠ lDir := by decide
@[simp] theorem fq_fqW_ne_fqN : fqW ≠ fqN := by decide
@[simp] theorem fq_fqW_ne_fqE : fqW ≠ fqE := by decide
@[simp] theorem fq_fqW_ne_fqU : fqW ≠ fqU := by decide
@[simp] theorem fq_fqW_ne_fqT : fqW ≠ fqT := by decide
@[simp] theorem fq_fqW_ne_fqB : fqW ≠ fqB := by decide
@[simp] theorem fq_fqW_ne_fqF : fqW ≠ fqF := by decide
@[simp] theorem fq_fqW_ne_fqB2 : fqW ≠ fqB2 := by decide
@[simp] theorem fq_fqW_ne_fqR : fqW ≠ fqR := by decide
@[simp] theorem fq_fqW_ne_kFu : fqW ≠ kFu := by decide
@[simp] theorem fq_fqW_ne_kD : fqW ≠ kD := by decide
@[simp] theorem fq_fqW_ne_lFl : fqW ≠ lFl := by decide
@[simp] theorem fq_fqW_ne_lDh : fqW ≠ lDh := by decide
@[simp] theorem fq_fqW_ne_lDt : fqW ≠ lDt := by decide
@[simp] theorem fq_fqW_ne_lDg : fqW ≠ lDg := by decide
@[simp] theorem fq_fqW_ne_lDi : fqW ≠ lDi := by decide
@[simp] theorem fq_fqW_ne_lRp : fqW ≠ lRp := by decide
@[simp] theorem fq_fqW_ne_lRn : fqW ≠ lRn := by decide
@[simp] theorem fq_fqW_ne_lKb : fqW ≠ lKb := by decide
@[simp] theorem fq_fqW_ne_lFle : fqW ≠ lFle := by decide
@[simp] theorem fq_fqW_ne_lDir : fqW ≠ lDir := by decide
@[simp] theorem fq_fqU_ne_fqN : fqU ≠ fqN := by decide
@[simp] theorem fq_fqU_ne_fqE : fqU ≠ fqE := by decide
@[simp] theorem fq_fqU_ne_fqW : fqU ≠ fqW := by decide
@[simp] theorem fq_fqU_ne_fqT : fqU ≠ fqT := by decide
@[simp] theorem fq_fqU_ne_fqB : fqU ≠ fqB := by decide
@[simp] theorem fq_fqU_ne_fqF : fqU ≠ fqF := by decide
@[simp] theorem fq_fqU_ne_fqB2 : fqU ≠ fqB2 := by decide
@[simp] theorem fq_fqU_ne_fqR : fqU ≠ fqR := by decide
@[simp] theorem fq_fqU_ne_kFu : fqU ≠ kFu := by decide
@[simp] theorem fq_fqU_ne_kD : fqU ≠ kD := by decide
@[simp] theorem fq_fqU_ne_lFl : fqU ≠ lFl := by decide
@[simp] theorem fq_fqU_ne_lDh : fqU ≠ lDh := by decide
@[simp] theorem fq_fqU_ne_lDt : fqU ≠ lDt := by decide
@[simp] theorem fq_fqU_ne_lDg : fqU ≠ lDg := by decide
@[simp] theorem fq_fqU_ne_lDi : fqU ≠ lDi := by decide
@[simp] theorem fq_fqU_ne_lRp : fqU ≠ lRp := by decide
@[simp] theorem fq_fqU_ne_lRn : fqU ≠ lRn := by decide
@[simp] theorem fq_fqU_ne_lKb : fqU ≠ lKb := by decide
@[simp] theorem fq_fqU_ne_lFle : fqU ≠ lFle := by decide
@[simp] theorem fq_fqU_ne_lDir : fqU ≠ lDir := by decide
@[simp] theorem fq_fqT_ne_fqN : fqT ≠ fqN := by decide
@[simp] theorem fq_fqT_ne_fqE : fqT ≠ fqE := by decide
@[simp] theorem fq_fqT_ne_fqW : fqT ≠ fqW := by decide
@[simp] theorem fq_fqT_ne_fqU : fqT ≠ fqU := by decide
@[simp] theorem fq_fqT_ne_fqB : fqT ≠ fqB := by decide
@[simp] theorem fq_fqT_ne_fqF : fqT ≠ fqF := by decide
@[simp] theorem fq_fqT_ne_fqB2 : fqT ≠ fqB2 := by decide
@[simp] theorem fq_fqT_ne_fqR : fqT ≠ fqR := by decide
@[simp] theorem fq_fqT_ne_kFu : fqT ≠ kFu := by decide
@[simp] theorem fq_fqT_ne_kD : fqT ≠ kD := by decide
@[simp] theorem fq_fqT_ne_lFl : fqT ≠ lFl := by decide
@[simp] theorem fq_fqT_ne_lDh : fqT ≠ lDh := by decide
@[simp] theorem fq_fqT_ne_lDt : fqT ≠ lDt := by decide
@[simp] theorem fq_fqT_ne_lDg : fqT ≠ lDg := by decide
@[simp] theorem fq_fqT_ne_lDi : fqT ≠ lDi := by decide
@[simp] theorem fq_fqT_ne_lRp : fqT ≠ lRp := by decide
@[simp] theorem fq_fqT_ne_lRn : fqT ≠ lRn := by decide
@[simp] theorem fq_fqT_ne_lKb : fqT ≠ lKb := by decide
@[simp] theorem fq_fqT_ne_lFle : fqT ≠ lFle := by decide
@[simp] theorem fq_fqT_ne_lDir : fqT ≠ lDir := by decide
@[simp] theorem fq_fqB_ne_fqN : fqB ≠ fqN := by decide
@[simp] theorem fq_fqB_ne_fqE : fqB ≠ fqE := by decide
@[simp] theorem fq_fqB_ne_fqW : fqB ≠ fqW := by decide
@[simp] theorem fq_fqB_ne_fqU : fqB ≠ fqU := by decide
@[simp] theorem fq_fqB_ne_fqT : fqB ≠ fqT := by decide
@[simp] theorem fq_fqB_ne_fqF : fqB ≠ fqF := by decide
@[simp] theorem fq_fqB_ne_fqB2 : fqB ≠ fqB2 := by decide
@[simp] theorem fq_fqB_ne_fqR : fqB ≠ fqR := by decide
@[simp] theorem fq_fqB_ne_kFu : fqB ≠ kFu := by decide
@[simp] theorem fq_fqB_ne_kD : fqB ≠ kD := by decide
@[simp] theorem fq_fqB_ne_lFl : fqB ≠ lFl := by decide
@[simp] theorem fq_fqB_ne_lDh : fqB ≠ lDh := by decide
@[simp] theorem fq_fqB_ne_lDt : fqB ≠ lDt := by decide
@[simp] theorem fq_fqB_ne_lDg : fqB ≠ lDg := by decide
@[simp] theorem fq_fqB_ne_lDi : fqB ≠ lDi := by decide
@[simp] theorem fq_fqB_ne_lRp : fqB ≠ lRp := by decide
@[simp] theorem fq_fqB_ne_lRn : fqB ≠ lRn := by decide
@[simp] theorem fq_fqB_ne_lKb : fqB ≠ lKb := by decide
@[simp] theorem fq_fqB_ne_lFle : fqB ≠ lFle := by decide
@[simp] theorem fq_fqB_ne_lDir : fqB ≠ lDir := by decide
@[simp] theorem fq_fqF_ne_fqN : fqF ≠ fqN := by decide
@[simp] theorem fq_fqF_ne_fqE : fqF ≠ fqE := by decide
@[simp] theorem fq_fqF_ne_fqW : fqF ≠ fqW := by decide
@[simp] theorem fq_fqF_ne_fqU : fqF ≠ fqU := by decide
@[simp] theorem fq_fqF_ne_fqT : fqF ≠ fqT := by decide
@[simp] theorem fq_fqF_ne_fqB : fqF ≠ fqB := by decide
@[simp] theorem fq_fqF_ne_fqB2 : fqF ≠ fqB2 := by decide
@[simp] theorem fq_fqF_ne_fqR : fqF ≠ fqR := by decide
@[simp] theorem fq_fqF_ne_kFu : fqF ≠ kFu := by decide
@[simp] theorem fq_fqF_ne_kD : fqF ≠ kD := by decide
@[simp] theorem fq_fqF_ne_lFl : fqF ≠ lFl := by decide
@[simp] theorem fq_fqF_ne_lDh : fqF ≠ lDh := by decide
@[simp] theorem fq_fqF_ne_lDt : fqF ≠ lDt := by decide
@[simp] theorem fq_fqF_ne_lDg : fqF ≠ lDg := by decide
@[simp] theorem fq_fqF_ne_lDi : fqF ≠ lDi := by decide
@[simp] theorem fq_fqF_ne_lRp : fqF ≠ lRp := by decide
@[simp] theorem fq_fqF_ne_lRn : fqF ≠ lRn := by decide
@[simp] theorem fq_fqF_ne_lKb : fqF ≠ lKb := by decide
@[simp] theorem fq_fqF_ne_lFle : fqF ≠ lFle := by decide
@[simp] theorem fq_fqF_ne_lDir : fqF ≠ lDir := by decide
@[simp] theorem fq_fqB2_ne_fqN : fqB2 ≠ fqN := by decide
@[simp] theorem fq_fqB2_ne_fqE : fqB2 ≠ fqE := by decide
@[simp] theorem fq_fqB2_ne_fqW : fqB2 ≠ fqW := by decide
@[simp] theorem fq_fqB2_ne_fqU : fqB2 ≠ fqU := by decide
@[simp] theorem fq_fqB2_ne_fqT : fqB2 ≠ fqT := by decide
@[simp] theorem fq_fqB2_ne_fqB : fqB2 ≠ fqB := by decide
@[simp] theorem fq_fqB2_ne_fqF : fqB2 ≠ fqF := by decide
@[simp] theorem fq_fqB2_ne_fqR : fqB2 ≠ fqR := by decide
@[simp] theorem fq_fqB2_ne_kFu : fqB2 ≠ kFu := by decide
@[simp] theorem fq_fqB2_ne_kD : fqB2 ≠ kD := by decide
@[simp] theorem fq_fqB2_ne_lFl : fqB2 ≠ lFl := by decide
@[simp] theorem fq_fqB2_ne_lDh : fqB2 ≠ lDh := by decide
@[simp] theorem fq_fqB2_ne_lDt : fqB2 ≠ lDt := by decide
@[simp] theorem fq_fqB2_ne_lDg : fqB2 ≠ lDg := by decide
@[simp] theorem fq_fqB2_ne_lDi : fqB2 ≠ lDi := by decide
@[simp] theorem fq_fqB2_ne_lRp : fqB2 ≠ lRp := by decide
@[simp] theorem fq_fqB2_ne_lRn : fqB2 ≠ lRn := by decide
@[simp] theorem fq_fqB2_ne_lKb : fqB2 ≠ lKb := by decide
@[simp] theorem fq_fqB2_ne_lFle : fqB2 ≠ lFle := by decide
@[simp] theorem fq_fqB2_ne_lDir : fqB2 ≠ lDir := by decide
@[simp] theorem fq_fqR_ne_fqN : fqR ≠ fqN := by decide
@[simp] theorem fq_fqR_ne_fqE : fqR ≠ fqE := by decide
@[simp] theorem fq_fqR_ne_fqW : fqR ≠ fqW := by decide
@[simp] theorem fq_fqR_ne_fqU : fqR ≠ fqU := by decide
@[simp] theorem fq_fqR_ne_fqT : fqR ≠ fqT := by decide
@[simp] theorem fq_fqR_ne_fqB : fqR ≠ fqB := by decide
@[simp] theorem fq_fqR_ne_fqF : fqR ≠ fqF := by decide
@[simp] theorem fq_fqR_ne_fqB2 : fqR ≠ fqB2 := by decide
@[simp] theorem fq_fqR_ne_kFu : fqR ≠ kFu := by decide
@[simp] theorem fq_fqR_ne_kD : fqR ≠ kD := by decide
@[simp] theorem fq_fqR_ne_lFl : fqR ≠ lFl := by decide
@[simp] theorem fq_fqR_ne_lDh : fqR ≠ lDh := by decide
@[simp] theorem fq_fqR_ne_lDt : fqR ≠ lDt := by decide
@[simp] theorem fq_fqR_ne_lDg : fqR ≠ lDg := by decide
@[simp] theorem fq_fqR_ne_lDi : fqR ≠ lDi := by decide
@[simp] theorem fq_fqR_ne_lRp : fqR ≠ lRp := by decide
@[simp] theorem fq_fqR_ne_lRn : fqR ≠ lRn := by decide
@[simp] theorem fq_fqR_ne_lKb : fqR ≠ lKb := by decide
@[simp] theorem fq_fqR_ne_lFle : fqR ≠ lFle := by decide
@[simp] theorem fq_fqR_ne_lDir : fqR ≠ lDir := by decide
@[simp] theorem fq_kFu_ne_fqN : kFu ≠ fqN := by decide
@[simp] theorem fq_kFu_ne_fqE : kFu ≠ fqE := by decide
@[simp] theorem fq_kFu_ne_fqW : kFu ≠ fqW := by decide
@[simp] theorem fq_kFu_ne_fqU : kFu ≠ fqU := by decide
@[simp] theorem fq_kFu_ne_fqT : kFu ≠ fqT := by decide
@[simp] theorem fq_kFu_ne_fqB : kFu ≠ fqB := by decide
@[simp] theorem fq_kFu_ne_fqF : kFu ≠ fqF := by decide
@[simp] theorem fq_kFu_ne_fqB2 : kFu ≠ fqB2 := by decide
@[simp] theorem fq_kFu_ne_fqR : kFu ≠ fqR := by decide
@[simp] theorem fq_kD_ne_fqN : kD ≠ fqN := by decide
@[simp] theorem fq_kD_ne_fqE : kD ≠ fqE := by decide
@[simp] theorem fq_kD_ne_fqW : kD ≠ fqW := by decide
@[simp] theorem fq_kD_ne_fqU : kD ≠ fqU := by decide
@[simp] theorem fq_kD_ne_fqT : kD ≠ fqT := by decide
@[simp] theorem fq_kD_ne_fqB : kD ≠ fqB := by decide
@[simp] theorem fq_kD_ne_fqF : kD ≠ fqF := by decide
@[simp] theorem fq_kD_ne_fqB2 : kD ≠ fqB2 := by decide
@[simp] theorem fq_kD_ne_fqR : kD ≠ fqR := by decide
@[simp] theorem fq_lFl_ne_fqN : lFl ≠ fqN := by decide
@[simp] theorem fq_lFl_ne_fqE : lFl ≠ fqE := by decide
@[simp] theorem fq_lFl_ne_fqW : lFl ≠ fqW := by decide
@[simp] theorem fq_lFl_ne_fqU : lFl ≠ fqU := by decide
@[simp] theorem fq_lFl_ne_fqT : lFl ≠ fqT := by decide
@[simp] theorem fq_lFl_ne_fqB : lFl ≠ fqB := by decide
@[simp] theorem fq_lFl_ne_fqF : lFl ≠ fqF := by decide
@[simp] theorem fq_lFl_ne_fqB2 : lFl ≠ fqB2 := by decide
@[simp] theorem fq_lFl_ne_fqR : lFl ≠ fqR := by decide
@[simp] theorem fq_lDh_ne_fqN : lDh ≠ fqN := by decide
@[simp] theorem fq_lDh_ne_fqE : lDh ≠ fqE := by decide
@[simp] theorem fq_lDh_ne_fqW : lDh ≠ fqW := by decide
@[simp] theorem fq_lDh_ne_fqU : lDh ≠ fqU := by decide
@[simp] theorem fq_lDh_ne_fqT : lDh ≠ fqT := by decide
@[simp] theorem fq_lDh_ne_fqB : lDh ≠ fqB := by decide
@[simp] theorem fq_lDh_ne_fqF : lDh ≠ fqF := by decide
@[simp] theorem fq_lDh_ne_fqB2 : lDh ≠ fqB2 := by decide
@[simp] theorem fq_lDh_ne_fqR : lDh ≠ fqR := by decide
@[simp] theorem fq_lDt_ne_fqN : lDt ≠ fqN := by decide
@[simp] theorem fq_lDt_ne_fqE : lDt ≠ fqE := by decide
@[simp] theorem fq_lDt_ne_fqW : lDt ≠ fqW := by decide
@[simp] theorem fq_lDt_ne_fqU : lDt ≠ fqU := by decide
@[simp] theorem fq_lDt_ne_fqT : lDt ≠ fqT := by decide
@[simp] theorem fq_lDt_ne_fqB : lDt ≠ fqB := by decide
@[simp] theorem fq_lDt_ne_fqF : lDt ≠ fqF := by decide
@[simp] theorem fq_lDt_ne_fqB2 : lDt ≠ fqB2 := by decide
@[simp] theorem fq_lDt_ne_fqR : lDt ≠ fqR := by decide
@[simp] theorem fq_lDg_ne_fqN : lDg ≠ fqN := by decide
@[simp] theorem fq_lDg_ne_fqE : lDg ≠ fqE := by decide
@[simp] theorem fq_lDg_ne_fqW : lDg ≠ fqW := by decide
@[simp] theorem fq_lDg_ne_fqU : lDg ≠ fqU := by decide
@[simp] theorem fq_lDg_ne_fqT : lDg ≠ fqT := by decide
@[simp] theorem fq_lDg_ne_fqB : lDg ≠ fqB := by decide
@[simp] theorem fq_lDg_ne_fqF : lDg ≠ fqF := by decide
@[simp] theorem fq_lDg_ne_fqB2 : lDg ≠ fqB2 := by decide
@[simp] theorem fq_lDg_ne_fqR : lDg ≠ fqR := by decide
@[simp] theorem fq_lDi_ne_fqN : lDi ≠ fqN := by decide
@[simp] theorem fq_lDi_ne_fqE : lDi ≠ fqE := by decide
@[simp] theorem fq_lDi_ne_fqW : lDi ≠ fqW := by decide
@[simp] theorem fq_lDi_ne_fqU : lDi ≠ fqU := by decide
@[simp] theorem fq_lDi_ne_fqT : lDi ≠ fqT := by decide
@[simp] theorem fq_lDi_ne_fqB : lDi ≠ fqB := by decide
@[simp] theorem fq_lDi_ne_fqF : lDi ≠ fqF := by decide
@[simp] theorem fq_lDi_ne_fqB2 : lDi ≠ fqB2 := by decide
@[simp] theorem fq_lDi_ne_fqR : lDi ≠ fqR := by decide
@[simp] theorem fq_lRp_ne_fqN : lRp ≠ fqN := by decide
@[simp] theorem fq_lRp_ne_fqE : lRp ≠ fqE := by decide
@[simp] theorem fq_lRp_ne_fqW : lRp ≠ fqW := by decide
@[simp] theorem fq_lRp_ne_fqU : lRp ≠ fqU := by decide
@[simp] theorem fq_lRp_ne_fqT : lRp ≠ fqT := by decide
@[simp] theorem fq_lRp_ne_fqB : lRp ≠ fqB := by decide
@[simp] theorem fq_lRp_ne_fqF : lRp ≠ fqF := by decide
@[simp] theorem fq_lRp_ne_fqB2 : lRp ≠ fqB2 := by decide
@[simp] theorem fq_lRp_ne_fqR : lRp ≠ fqR := by decide
@[simp] theorem fq_lRn_ne_fqN : lRn ≠ fqN := by decide
@[simp] theorem fq_lRn_ne_fqE : lRn ≠ fqE := by decide
@[simp] theorem fq_lRn_ne_fqW : lRn ≠ fqW := by decide
@[simp] theorem fq_lRn_ne_fqU : lRn ≠ fqU := by decide
@[simp] theorem fq_lRn_ne_fqT : lRn ≠ fqT := by decide
@[simp] theorem fq_lRn_ne_fqB : lRn ≠ fqB := by decide
@[simp] theorem fq_lRn_ne_fqF : lRn ≠ fqF := by decide
@[simp] theorem fq_lRn_ne_fqB2 : lRn ≠ fqB2 := by decide
@[simp] theorem fq_lRn_ne_fqR : lRn ≠ fqR := by decide
@[simp] theorem fq_lKb_ne_fqN : lKb ≠ fqN := by decide
@[simp] theorem fq_lKb_ne_fqE : lKb ≠ fqE := by decide
@[simp] theorem fq_lKb_ne_fqW : lKb ≠ fqW := by decide
@[simp] theorem fq_lKb_ne_fqU : lKb ≠ fqU := by decide
@[simp] theorem fq_lKb_ne_fqT : lKb ≠ fqT := by decide
@[simp] theorem fq_lKb_ne_fqB : lKb ≠ fqB := by decide
@[simp] theorem fq_lKb_ne_fqF : lKb ≠ fqF := by decide
@[simp] theorem fq_lKb_ne_fqB2 : lKb ≠ fqB2 := by decide
@[simp] theorem fq_lKb_ne_fqR : lKb ≠ fqR := by decide
@[simp] theorem fq_lFle_ne_fqN : lFle ≠ fqN := by decide
@[simp] theorem fq_lFle_ne_fqE : lFle ≠ fqE := by decide
@[simp] theorem fq_lFle_ne_fqW : lFle ≠ fqW := by decide
@[simp] theorem fq_lFle_ne_fqU : lFle ≠ fqU := by decide
@[simp] theorem fq_lFle_ne_fqT : lFle ≠ fqT := by decide
@[simp] theorem fq_lFle_ne_fqB : lFle ≠ fqB := by decide
@[simp] theorem fq_lFle_ne_fqF : lFle ≠ fqF := by decide
@[simp] theorem fq_lFle_ne_fqB2 : lFle ≠ fqB2 := by decide
@[simp] theorem fq_lFle_ne_fqR : lFle ≠ fqR := by decide
@[simp] theorem fq_lDir_ne_fqN : lDir ≠ fqN := by decide
@[simp] theorem fq_lDir_ne_fqE : lDir ≠ fqE := by decide
@[simp] theorem fq_lDir_ne_fqW : lDir ≠ fqW := by decide
@[simp] theorem fq_lDir_ne_fqU : lDir ≠ fqU := by decide
@[simp] theorem fq_lDir_ne_fqT : lDir ≠ fqT := by decide
@[simp] theorem fq_lDir_ne_fqB : lDir ≠ fqB := by decide
@[simp] theorem fq_lDir_ne_fqF : lDir ≠ fqF := by decide
@[simp] theorem fq_lDir_ne_fqB2 : lDir ≠ fqB2 := by decide
@[simp] theorem fq_lDir_ne_fqR : lDir ≠ fqR := by decide

def fqParams : List MlS := [kFu, kD, fqN, fqE]
def fqLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, fqW, fqU, fqT, fqB, fqF, fqB2, fqR]

def fqCore : ProgHOL 64 :=
  .seq (.call (some (some (.local, fqW), none)) fW [vv kFu, vv kD, vv fqE])
  (.ite (.cmp .equal (vv fqN) (.const 0))
    (.ite (tagIsE fqW 2)
      (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv fqW)) (.seq eViewP
      (.seq (.assign .local fqU (.load .one (vv lRp)))
        (.return (.op .add [vv fqU, .const 1]))))))
      (.return (.const 0)))
    (.ite (tagIsE fqW 6)
      (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv fqW)) (.seq eViewP
      (.seq (.assign .local fqT (.load .one (vv lRp)))
      (.seq (.assign .local fqB (.load .one (.op .add [vv lRp, .const 8])))
      (.seq (.call (some (some (.local, fqF), none)) fInternFVar [vv fqT, vv kD])
      (.seq (.call (some (some (.local, fqB2), none)) ExI.fInst1F
          [.const (BitVec.ofNat 64 coreWalkFuel), vv fqB, vv fqF, .const 0])
      (.seq (.call (some (some (.local, fqR), none)) fFsl
          [vv kFu, .op .add [vv kD, .const 1], .op .sub [vv fqN, .const 1], vv fqB2])
        (.return (vv fqR))))))))))
      (.return (.const 0))))

def fqBody : ProgHOL 64 := prologue fqLocals fqCore

structure FqCodes (C : Ctx) : Prop where
  w : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one)
  fv : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one)
  i1 : C.code.lookup ExI.fInst1F = some ([pFu, pH, ExI.pV, ExI.pD].map (fun p => (p, ShapeHOL.one)),
    ExI.fastBody C, .one)
  i1c : ExI.Codes C (ExI.body C)
  self : C.code.lookup fFsl = some (fqParams.map (fun p => (p, ShapeHOL.one)), fqBody, .one)

section
variable {σ : Type}

theorem fq_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ fqLocals → (ctxEnv C ++ fqParams.zip vals).get x = none :=
  Knot.params_none C fqLocals fqParams vals (by decide) (by decide)

/-- An optional level answer, the heap extended, any final state. -/
def PostOK (C : Ctx) (o : Option LIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ w = optWG Enc.idxW o ∧ SR (ctxH C H') s' st

theorem postOK_locals (C : Ctx) : ∀ (a : Option LIdx) w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostOK C a w s' st → PostOK C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, sr_of_eq hsr rfl rfl rfl rfl⟩

theorem fq_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (hc : FqCodes C)
    (hW : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ d e', Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d e')
      (PostK (ctxH C H))) :
    ∀ k d (e : EIdx) (s : AState) (H : List (BitVec 64)), C.H <+: H → d + k < 2 ^ 63 →
      SpecR (σ := σ) (Pre (ctxH C H) s (fqParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, BitVec.ofNat 64 k,
        Enc.idxW e])) fqBody s (formerSortLoop (knot mode C n) d k e) (PostOK (ctxH C H)) := by
  intro k
  induction k with
  | zero =>
    intro d e s H hp hd
    refine specR_prologue (postOK_locals _) (fq_none _ _) ?_
    unfold fqCore
    rw [formerSortLoop]
    refine Big.specR_callKC (C := ctxH C H) fqW fW kParams [vv kFu, vv kD, vv fqE] (whnfE C fWB)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e] (by decide) rfl (by decide) hc.w
      ⟨by simp +decide [Env.get, fqParams, ctxEnv], by simp +decide [Env.get, fqParams, ctxEnv],
        by simp +decide [Env.get, fqParams, ctxEnv], trivial⟩
      (hW H s hp d e) (fun w s1 H1 hp1 _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, fqParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine Knot.specR_tagIteV fqW w 2 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
    · rw [if_pos (show (w.tag == ETag.sort) = true by simp [htg, ETag.sort])]
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv fqW) (Enc.idxW w) (by decide) (by simp) ?_
      refine specR_viewP (C := ctxH C H1) w (by simp) (by simp +decide [Env.get] <;> rfl)
        (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
      have h2 : v.tagN = 2 := by rw [htn, htg]; rfl
      obtain ⟨u, rfl⟩ : ∃ u, v = .sort u := by cases v <;> simp [ENodeView.tagN] at h2 ⊢
      have hvs : s1.store.viewSort w = some u := viewSort_of_view (by rw [htg]; rfl) hv
      refine specR_runBind (show ConRon.Arena.viewSort w s1 = .ok (some u, s1) by
        show Except.ok (s1.store.viewSort w, s1) = _; rw [hvs]) ?_
      dsimp only
      refine specR_loadI' fqU (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW u) (by decide) (by simp) (by simp)
        (by simpa [encEView, Enc.encSort] using wordsAt_mem0 P (Enc.idxW u) [] []) ?_
      exact specR_returnI _ (optWG Enc.idxW (some u)) (by simp [sev, optWG])
        (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · rw [if_neg (show ¬ (w.tag == ETag.sort) = true by simpa [ETag.sort] using htg)]
      exact specR_returnI _ (optWG Enc.idxW none) (by simp [optWG]; rfl)
        (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro d e s H hp hd
    refine specR_prologue (postOK_locals _) (fq_none _ _) ?_
    unfold fqCore
    rw [formerSortLoop]
    refine Big.specR_callKC (C := ctxH C H) fqW fW kParams [vv kFu, vv kD, vv fqE] (whnfE C fWB)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e] (by decide) rfl (by decide) hc.w
      ⟨by simp +decide [Env.get, fqParams, ctxEnv], by simp +decide [Env.get, fqParams, ctxEnv],
        by simp +decide [Env.get, fqParams, ctxEnv], trivial⟩
      (hW H s hp d e) (fun w s1 H1 hp1 _ => ?_)
    have hne : BitVec.ofNat 64 (k + 1) ≠ 0 := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, fqParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine Knot.specR_tagIteV fqW w 6 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
    · rw [if_pos (show (w.tag == ETag.forallE) = true by simp [htg, ETag.forallE])]
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv fqW) (Enc.idxW w) (by decide) (by simp) ?_
      refine specR_viewP (C := ctxH C H1) w (by simp) (by simp +decide [Env.get] <;> rfl)
        (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
      have h6 : v.tagN = 6 := by rw [htn, htg]; rfl
      obtain ⟨ty, b, rfl⟩ : ∃ ty b, v = .forallE ty b := by
        cases v <;> simp [ENodeView.tagN] at h6 ⊢
      have hvb : s1.store.viewBind w = some (ty, b) := viewBind_of_view_forallE (by rw [htg]; rfl) hv
      refine specR_runBind (by rw [viewBind_run, hvb]) ?_
      dsimp only
      refine specR_loadI' fqT (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
        (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW ty) [Enc.idxW b] []) ?_
      refine specR_loadI' fqB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW b) [] []) ?_
      refine ILP.specR_internFVarI ra (ctxOK_H hok H1) hc.fv fqF (vv fqT) (vv kD) ty d (by omega) (by decide)
        (by simp) (by simp +decide [Env.get, fqParams, ctxEnv]) (fun fv s2 => ?_)
      refine ILP.callE_spec (C := ctxH C H1) fqB2 ExI.fInst1F [pFu, pH, ExI.pV, ExI.pD]
        [.const (BitVec.ofNat 64 coreWalkFuel), vv fqB, vv fqF, .const 0] (ExI.fastBody C)
        [BitVec.ofNat 64 coreWalkFuel, Enc.idxW b, Enc.idxW fv, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.i1
        ⟨rfl, by simp, by simp, rfl, trivial⟩
        (ExI.fast_spec ra (ctxH C H1) (ctxOK_H hok H1) (ExIS.codes_H C H1 hc.i1c) s2 coreWalkFuel b fv 0
          CV.coreWalkFuel_lt (by decide)) (fun b2 s3 => ?_)
      refine specR_congr (m' := formerSortLoop (knot mode C n) (d + 1) k b2 >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H1) fqR fFsl fqParams
        [vv kFu, .op .add [vv kD, .const 1], .op .sub [vv fqN, .const 1], vv fqB2] fqBody
        [BitVec.ofNat 64 n, BitVec.ofNat 64 (d + 1), BitVec.ofNat 64 k, Enc.idxW b2] (by decide) rfl (by decide) hc.self
        ⟨by simp +decide [Env.get, fqParams, ctxEnv],
          by simp +decide [sev, Env.get, fqParams, ctxEnv]; exact word_add1_eq d,
          by simp +decide [sev, Env.get, fqParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, by simp, trivial⟩
        (PostOK (ctxH C H1)) (fun o w _ _ => w = optWG Enc.idxW o)
        (fun o w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fqParams _ rfl hlk)
          (ih (d + 1) b2 s3 H1 (hp.trans hp1) (by omega)))
        (fun o w s4 H4 hp4 hw => ?_)
      subst hw
      exact specR_returnI _ (optWG Enc.idxW o) (by simp)
        (fun t ht => ⟨H4, hp1.trans hp4, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · rw [if_neg (show ¬ (w.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg)]
      exact specR_returnI _ (optWG Enc.idxW none) (by simp [optWG]; rfl)
        (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
