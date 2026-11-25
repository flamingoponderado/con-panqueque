import ConPanqueque.T.Core.TypeAt
import ConPanqueque.T.Core.InferBody
import ConPanqueque.T.Core.ReduceProj
import ConPanqueque.T.Core.WcStuck
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# The projection arm: `inferProj`

The subject's type `whnf`ed, its head a constant `T` with a projection table entry for the index; the arguments'
count must be the table's parameter count, `T` the node's structure, the level arity the table's; then the guard
(`checkProjGuard`) and the field's type (`typeAt`), both callees on a family `Q`. Every twin failure halts.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def pjA := ofString "pjn_a"
def pjTe := ofString "pjn_te"
def pjHh := ofString "pjn_hh"
def pjT := ofString "pjn_t"
def pjUs := ofString "pjn_us"
def pjTb := ofString "pjn_tb"
def pjTq := ofString "pjn_tq"
def pjNf := ofString "pjn_nf"
def pjVa := ofString "pjn_va"
def pjNa := ofString "pjn_na"
def pjNp := ofString "pjn_np"
def pjLp := ofString "pjn_lp"
def pjLl := ofString "pjn_ll"
def pjG := ofString "pjn_g"
def pjR := ofString "pjn_r"

@[simp] theorem pj_pjA_ne_pjTe : pjA ≠ pjTe := by decide
@[simp] theorem pj_pjA_ne_pjHh : pjA ≠ pjHh := by decide
@[simp] theorem pj_pjA_ne_pjT : pjA ≠ pjT := by decide
@[simp] theorem pj_pjA_ne_pjUs : pjA ≠ pjUs := by decide
@[simp] theorem pj_pjA_ne_pjTb : pjA ≠ pjTb := by decide
@[simp] theorem pj_pjA_ne_pjTq : pjA ≠ pjTq := by decide
@[simp] theorem pj_pjA_ne_pjNf : pjA ≠ pjNf := by decide
@[simp] theorem pj_pjA_ne_pjVa : pjA ≠ pjVa := by decide
@[simp] theorem pj_pjA_ne_pjNa : pjA ≠ pjNa := by decide
@[simp] theorem pj_pjA_ne_pjNp : pjA ≠ pjNp := by decide
@[simp] theorem pj_pjA_ne_pjLp : pjA ≠ pjLp := by decide
@[simp] theorem pj_pjA_ne_pjLl : pjA ≠ pjLl := by decide
@[simp] theorem pj_pjA_ne_pjG : pjA ≠ pjG := by decide
@[simp] theorem pj_pjA_ne_pjR : pjA ≠ pjR := by decide
@[simp] theorem pj_pjA_ne_kFu : pjA ≠ kFu := by decide
@[simp] theorem pj_kFu_ne_pjA : kFu ≠ pjA := by decide
@[simp] theorem pj_pjA_ne_kD : pjA ≠ kD := by decide
@[simp] theorem pj_kD_ne_pjA : kD ≠ pjA := by decide
@[simp] theorem pj_pjA_ne_ibSn : pjA ≠ ibSn := by decide
@[simp] theorem pj_ibSn_ne_pjA : ibSn ≠ pjA := by decide
@[simp] theorem pj_pjA_ne_ibIx : pjA ≠ ibIx := by decide
@[simp] theorem pj_ibIx_ne_pjA : ibIx ≠ pjA := by decide
@[simp] theorem pj_pjA_ne_ibPe : pjA ≠ ibPe := by decide
@[simp] theorem pj_ibPe_ne_pjA : ibPe ≠ pjA := by decide
@[simp] theorem pj_pjA_ne_lFl : pjA ≠ lFl := by decide
@[simp] theorem pj_lFl_ne_pjA : lFl ≠ pjA := by decide
@[simp] theorem pj_pjA_ne_lDh : pjA ≠ lDh := by decide
@[simp] theorem pj_lDh_ne_pjA : lDh ≠ pjA := by decide
@[simp] theorem pj_pjA_ne_lDt : pjA ≠ lDt := by decide
@[simp] theorem pj_lDt_ne_pjA : lDt ≠ pjA := by decide
@[simp] theorem pj_pjA_ne_lDg : pjA ≠ lDg := by decide
@[simp] theorem pj_lDg_ne_pjA : lDg ≠ pjA := by decide
@[simp] theorem pj_pjA_ne_lDi : pjA ≠ lDi := by decide
@[simp] theorem pj_lDi_ne_pjA : lDi ≠ pjA := by decide
@[simp] theorem pj_pjA_ne_lRp : pjA ≠ lRp := by decide
@[simp] theorem pj_lRp_ne_pjA : lRp ≠ pjA := by decide
@[simp] theorem pj_pjA_ne_lRn : pjA ≠ lRn := by decide
@[simp] theorem pj_lRn_ne_pjA : lRn ≠ pjA := by decide
@[simp] theorem pj_pjA_ne_lDir : pjA ≠ lDir := by decide
@[simp] theorem pj_lDir_ne_pjA : lDir ≠ pjA := by decide
@[simp] theorem pj_pjA_ne_lFle : pjA ≠ lFle := by decide
@[simp] theorem pj_lFle_ne_pjA : lFle ≠ pjA := by decide
@[simp] theorem pj_pjA_ne_lFls : pjA ≠ lFls := by decide
@[simp] theorem pj_lFls_ne_pjA : lFls ≠ pjA := by decide
@[simp] theorem pj_pjA_ne_lKb : pjA ≠ lKb := by decide
@[simp] theorem pj_lKb_ne_pjA : lKb ≠ pjA := by decide
@[simp] theorem pj_pjTe_ne_pjA : pjTe ≠ pjA := by decide
@[simp] theorem pj_pjTe_ne_pjHh : pjTe ≠ pjHh := by decide
@[simp] theorem pj_pjTe_ne_pjT : pjTe ≠ pjT := by decide
@[simp] theorem pj_pjTe_ne_pjUs : pjTe ≠ pjUs := by decide
@[simp] theorem pj_pjTe_ne_pjTb : pjTe ≠ pjTb := by decide
@[simp] theorem pj_pjTe_ne_pjTq : pjTe ≠ pjTq := by decide
@[simp] theorem pj_pjTe_ne_pjNf : pjTe ≠ pjNf := by decide
@[simp] theorem pj_pjTe_ne_pjVa : pjTe ≠ pjVa := by decide
@[simp] theorem pj_pjTe_ne_pjNa : pjTe ≠ pjNa := by decide
@[simp] theorem pj_pjTe_ne_pjNp : pjTe ≠ pjNp := by decide
@[simp] theorem pj_pjTe_ne_pjLp : pjTe ≠ pjLp := by decide
@[simp] theorem pj_pjTe_ne_pjLl : pjTe ≠ pjLl := by decide
@[simp] theorem pj_pjTe_ne_pjG : pjTe ≠ pjG := by decide
@[simp] theorem pj_pjTe_ne_pjR : pjTe ≠ pjR := by decide
@[simp] theorem pj_pjTe_ne_kFu : pjTe ≠ kFu := by decide
@[simp] theorem pj_kFu_ne_pjTe : kFu ≠ pjTe := by decide
@[simp] theorem pj_pjTe_ne_kD : pjTe ≠ kD := by decide
@[simp] theorem pj_kD_ne_pjTe : kD ≠ pjTe := by decide
@[simp] theorem pj_pjTe_ne_ibSn : pjTe ≠ ibSn := by decide
@[simp] theorem pj_ibSn_ne_pjTe : ibSn ≠ pjTe := by decide
@[simp] theorem pj_pjTe_ne_ibIx : pjTe ≠ ibIx := by decide
@[simp] theorem pj_ibIx_ne_pjTe : ibIx ≠ pjTe := by decide
@[simp] theorem pj_pjTe_ne_ibPe : pjTe ≠ ibPe := by decide
@[simp] theorem pj_ibPe_ne_pjTe : ibPe ≠ pjTe := by decide
@[simp] theorem pj_pjTe_ne_lFl : pjTe ≠ lFl := by decide
@[simp] theorem pj_lFl_ne_pjTe : lFl ≠ pjTe := by decide
@[simp] theorem pj_pjTe_ne_lDh : pjTe ≠ lDh := by decide
@[simp] theorem pj_lDh_ne_pjTe : lDh ≠ pjTe := by decide
@[simp] theorem pj_pjTe_ne_lDt : pjTe ≠ lDt := by decide
@[simp] theorem pj_lDt_ne_pjTe : lDt ≠ pjTe := by decide
@[simp] theorem pj_pjTe_ne_lDg : pjTe ≠ lDg := by decide
@[simp] theorem pj_lDg_ne_pjTe : lDg ≠ pjTe := by decide
@[simp] theorem pj_pjTe_ne_lDi : pjTe ≠ lDi := by decide
@[simp] theorem pj_lDi_ne_pjTe : lDi ≠ pjTe := by decide
@[simp] theorem pj_pjTe_ne_lRp : pjTe ≠ lRp := by decide
@[simp] theorem pj_lRp_ne_pjTe : lRp ≠ pjTe := by decide
@[simp] theorem pj_pjTe_ne_lRn : pjTe ≠ lRn := by decide
@[simp] theorem pj_lRn_ne_pjTe : lRn ≠ pjTe := by decide
@[simp] theorem pj_pjTe_ne_lDir : pjTe ≠ lDir := by decide
@[simp] theorem pj_lDir_ne_pjTe : lDir ≠ pjTe := by decide
@[simp] theorem pj_pjTe_ne_lFle : pjTe ≠ lFle := by decide
@[simp] theorem pj_lFle_ne_pjTe : lFle ≠ pjTe := by decide
@[simp] theorem pj_pjTe_ne_lFls : pjTe ≠ lFls := by decide
@[simp] theorem pj_lFls_ne_pjTe : lFls ≠ pjTe := by decide
@[simp] theorem pj_pjTe_ne_lKb : pjTe ≠ lKb := by decide
@[simp] theorem pj_lKb_ne_pjTe : lKb ≠ pjTe := by decide
@[simp] theorem pj_pjHh_ne_pjA : pjHh ≠ pjA := by decide
@[simp] theorem pj_pjHh_ne_pjTe : pjHh ≠ pjTe := by decide
@[simp] theorem pj_pjHh_ne_pjT : pjHh ≠ pjT := by decide
@[simp] theorem pj_pjHh_ne_pjUs : pjHh ≠ pjUs := by decide
@[simp] theorem pj_pjHh_ne_pjTb : pjHh ≠ pjTb := by decide
@[simp] theorem pj_pjHh_ne_pjTq : pjHh ≠ pjTq := by decide
@[simp] theorem pj_pjHh_ne_pjNf : pjHh ≠ pjNf := by decide
@[simp] theorem pj_pjHh_ne_pjVa : pjHh ≠ pjVa := by decide
@[simp] theorem pj_pjHh_ne_pjNa : pjHh ≠ pjNa := by decide
@[simp] theorem pj_pjHh_ne_pjNp : pjHh ≠ pjNp := by decide
@[simp] theorem pj_pjHh_ne_pjLp : pjHh ≠ pjLp := by decide
@[simp] theorem pj_pjHh_ne_pjLl : pjHh ≠ pjLl := by decide
@[simp] theorem pj_pjHh_ne_pjG : pjHh ≠ pjG := by decide
@[simp] theorem pj_pjHh_ne_pjR : pjHh ≠ pjR := by decide
@[simp] theorem pj_pjHh_ne_kFu : pjHh ≠ kFu := by decide
@[simp] theorem pj_kFu_ne_pjHh : kFu ≠ pjHh := by decide
@[simp] theorem pj_pjHh_ne_kD : pjHh ≠ kD := by decide
@[simp] theorem pj_kD_ne_pjHh : kD ≠ pjHh := by decide
@[simp] theorem pj_pjHh_ne_ibSn : pjHh ≠ ibSn := by decide
@[simp] theorem pj_ibSn_ne_pjHh : ibSn ≠ pjHh := by decide
@[simp] theorem pj_pjHh_ne_ibIx : pjHh ≠ ibIx := by decide
@[simp] theorem pj_ibIx_ne_pjHh : ibIx ≠ pjHh := by decide
@[simp] theorem pj_pjHh_ne_ibPe : pjHh ≠ ibPe := by decide
@[simp] theorem pj_ibPe_ne_pjHh : ibPe ≠ pjHh := by decide
@[simp] theorem pj_pjHh_ne_lFl : pjHh ≠ lFl := by decide
@[simp] theorem pj_lFl_ne_pjHh : lFl ≠ pjHh := by decide
@[simp] theorem pj_pjHh_ne_lDh : pjHh ≠ lDh := by decide
@[simp] theorem pj_lDh_ne_pjHh : lDh ≠ pjHh := by decide
@[simp] theorem pj_pjHh_ne_lDt : pjHh ≠ lDt := by decide
@[simp] theorem pj_lDt_ne_pjHh : lDt ≠ pjHh := by decide
@[simp] theorem pj_pjHh_ne_lDg : pjHh ≠ lDg := by decide
@[simp] theorem pj_lDg_ne_pjHh : lDg ≠ pjHh := by decide
@[simp] theorem pj_pjHh_ne_lDi : pjHh ≠ lDi := by decide
@[simp] theorem pj_lDi_ne_pjHh : lDi ≠ pjHh := by decide
@[simp] theorem pj_pjHh_ne_lRp : pjHh ≠ lRp := by decide
@[simp] theorem pj_lRp_ne_pjHh : lRp ≠ pjHh := by decide
@[simp] theorem pj_pjHh_ne_lRn : pjHh ≠ lRn := by decide
@[simp] theorem pj_lRn_ne_pjHh : lRn ≠ pjHh := by decide
@[simp] theorem pj_pjHh_ne_lDir : pjHh ≠ lDir := by decide
@[simp] theorem pj_lDir_ne_pjHh : lDir ≠ pjHh := by decide
@[simp] theorem pj_pjHh_ne_lFle : pjHh ≠ lFle := by decide
@[simp] theorem pj_lFle_ne_pjHh : lFle ≠ pjHh := by decide
@[simp] theorem pj_pjHh_ne_lFls : pjHh ≠ lFls := by decide
@[simp] theorem pj_lFls_ne_pjHh : lFls ≠ pjHh := by decide
@[simp] theorem pj_pjHh_ne_lKb : pjHh ≠ lKb := by decide
@[simp] theorem pj_lKb_ne_pjHh : lKb ≠ pjHh := by decide
@[simp] theorem pj_pjT_ne_pjA : pjT ≠ pjA := by decide
@[simp] theorem pj_pjT_ne_pjTe : pjT ≠ pjTe := by decide
@[simp] theorem pj_pjT_ne_pjHh : pjT ≠ pjHh := by decide
@[simp] theorem pj_pjT_ne_pjUs : pjT ≠ pjUs := by decide
@[simp] theorem pj_pjT_ne_pjTb : pjT ≠ pjTb := by decide
@[simp] theorem pj_pjT_ne_pjTq : pjT ≠ pjTq := by decide
@[simp] theorem pj_pjT_ne_pjNf : pjT ≠ pjNf := by decide
@[simp] theorem pj_pjT_ne_pjVa : pjT ≠ pjVa := by decide
@[simp] theorem pj_pjT_ne_pjNa : pjT ≠ pjNa := by decide
@[simp] theorem pj_pjT_ne_pjNp : pjT ≠ pjNp := by decide
@[simp] theorem pj_pjT_ne_pjLp : pjT ≠ pjLp := by decide
@[simp] theorem pj_pjT_ne_pjLl : pjT ≠ pjLl := by decide
@[simp] theorem pj_pjT_ne_pjG : pjT ≠ pjG := by decide
@[simp] theorem pj_pjT_ne_pjR : pjT ≠ pjR := by decide
@[simp] theorem pj_pjT_ne_kFu : pjT ≠ kFu := by decide
@[simp] theorem pj_kFu_ne_pjT : kFu ≠ pjT := by decide
@[simp] theorem pj_pjT_ne_kD : pjT ≠ kD := by decide
@[simp] theorem pj_kD_ne_pjT : kD ≠ pjT := by decide
@[simp] theorem pj_pjT_ne_ibSn : pjT ≠ ibSn := by decide
@[simp] theorem pj_ibSn_ne_pjT : ibSn ≠ pjT := by decide
@[simp] theorem pj_pjT_ne_ibIx : pjT ≠ ibIx := by decide
@[simp] theorem pj_ibIx_ne_pjT : ibIx ≠ pjT := by decide
@[simp] theorem pj_pjT_ne_ibPe : pjT ≠ ibPe := by decide
@[simp] theorem pj_ibPe_ne_pjT : ibPe ≠ pjT := by decide
@[simp] theorem pj_pjT_ne_lFl : pjT ≠ lFl := by decide
@[simp] theorem pj_lFl_ne_pjT : lFl ≠ pjT := by decide
@[simp] theorem pj_pjT_ne_lDh : pjT ≠ lDh := by decide
@[simp] theorem pj_lDh_ne_pjT : lDh ≠ pjT := by decide
@[simp] theorem pj_pjT_ne_lDt : pjT ≠ lDt := by decide
@[simp] theorem pj_lDt_ne_pjT : lDt ≠ pjT := by decide
@[simp] theorem pj_pjT_ne_lDg : pjT ≠ lDg := by decide
@[simp] theorem pj_lDg_ne_pjT : lDg ≠ pjT := by decide
@[simp] theorem pj_pjT_ne_lDi : pjT ≠ lDi := by decide
@[simp] theorem pj_lDi_ne_pjT : lDi ≠ pjT := by decide
@[simp] theorem pj_pjT_ne_lRp : pjT ≠ lRp := by decide
@[simp] theorem pj_lRp_ne_pjT : lRp ≠ pjT := by decide
@[simp] theorem pj_pjT_ne_lRn : pjT ≠ lRn := by decide
@[simp] theorem pj_lRn_ne_pjT : lRn ≠ pjT := by decide
@[simp] theorem pj_pjT_ne_lDir : pjT ≠ lDir := by decide
@[simp] theorem pj_lDir_ne_pjT : lDir ≠ pjT := by decide
@[simp] theorem pj_pjT_ne_lFle : pjT ≠ lFle := by decide
@[simp] theorem pj_lFle_ne_pjT : lFle ≠ pjT := by decide
@[simp] theorem pj_pjT_ne_lFls : pjT ≠ lFls := by decide
@[simp] theorem pj_lFls_ne_pjT : lFls ≠ pjT := by decide
@[simp] theorem pj_pjT_ne_lKb : pjT ≠ lKb := by decide
@[simp] theorem pj_lKb_ne_pjT : lKb ≠ pjT := by decide
@[simp] theorem pj_pjUs_ne_pjA : pjUs ≠ pjA := by decide
@[simp] theorem pj_pjUs_ne_pjTe : pjUs ≠ pjTe := by decide
@[simp] theorem pj_pjUs_ne_pjHh : pjUs ≠ pjHh := by decide
@[simp] theorem pj_pjUs_ne_pjT : pjUs ≠ pjT := by decide
@[simp] theorem pj_pjUs_ne_pjTb : pjUs ≠ pjTb := by decide
@[simp] theorem pj_pjUs_ne_pjTq : pjUs ≠ pjTq := by decide
@[simp] theorem pj_pjUs_ne_pjNf : pjUs ≠ pjNf := by decide
@[simp] theorem pj_pjUs_ne_pjVa : pjUs ≠ pjVa := by decide
@[simp] theorem pj_pjUs_ne_pjNa : pjUs ≠ pjNa := by decide
@[simp] theorem pj_pjUs_ne_pjNp : pjUs ≠ pjNp := by decide
@[simp] theorem pj_pjUs_ne_pjLp : pjUs ≠ pjLp := by decide
@[simp] theorem pj_pjUs_ne_pjLl : pjUs ≠ pjLl := by decide
@[simp] theorem pj_pjUs_ne_pjG : pjUs ≠ pjG := by decide
@[simp] theorem pj_pjUs_ne_pjR : pjUs ≠ pjR := by decide
@[simp] theorem pj_pjUs_ne_kFu : pjUs ≠ kFu := by decide
@[simp] theorem pj_kFu_ne_pjUs : kFu ≠ pjUs := by decide
@[simp] theorem pj_pjUs_ne_kD : pjUs ≠ kD := by decide
@[simp] theorem pj_kD_ne_pjUs : kD ≠ pjUs := by decide
@[simp] theorem pj_pjUs_ne_ibSn : pjUs ≠ ibSn := by decide
@[simp] theorem pj_ibSn_ne_pjUs : ibSn ≠ pjUs := by decide
@[simp] theorem pj_pjUs_ne_ibIx : pjUs ≠ ibIx := by decide
@[simp] theorem pj_ibIx_ne_pjUs : ibIx ≠ pjUs := by decide
@[simp] theorem pj_pjUs_ne_ibPe : pjUs ≠ ibPe := by decide
@[simp] theorem pj_ibPe_ne_pjUs : ibPe ≠ pjUs := by decide
@[simp] theorem pj_pjUs_ne_lFl : pjUs ≠ lFl := by decide
@[simp] theorem pj_lFl_ne_pjUs : lFl ≠ pjUs := by decide
@[simp] theorem pj_pjUs_ne_lDh : pjUs ≠ lDh := by decide
@[simp] theorem pj_lDh_ne_pjUs : lDh ≠ pjUs := by decide
@[simp] theorem pj_pjUs_ne_lDt : pjUs ≠ lDt := by decide
@[simp] theorem pj_lDt_ne_pjUs : lDt ≠ pjUs := by decide
@[simp] theorem pj_pjUs_ne_lDg : pjUs ≠ lDg := by decide
@[simp] theorem pj_lDg_ne_pjUs : lDg ≠ pjUs := by decide
@[simp] theorem pj_pjUs_ne_lDi : pjUs ≠ lDi := by decide
@[simp] theorem pj_lDi_ne_pjUs : lDi ≠ pjUs := by decide
@[simp] theorem pj_pjUs_ne_lRp : pjUs ≠ lRp := by decide
@[simp] theorem pj_lRp_ne_pjUs : lRp ≠ pjUs := by decide
@[simp] theorem pj_pjUs_ne_lRn : pjUs ≠ lRn := by decide
@[simp] theorem pj_lRn_ne_pjUs : lRn ≠ pjUs := by decide
@[simp] theorem pj_pjUs_ne_lDir : pjUs ≠ lDir := by decide
@[simp] theorem pj_lDir_ne_pjUs : lDir ≠ pjUs := by decide
@[simp] theorem pj_pjUs_ne_lFle : pjUs ≠ lFle := by decide
@[simp] theorem pj_lFle_ne_pjUs : lFle ≠ pjUs := by decide
@[simp] theorem pj_pjUs_ne_lFls : pjUs ≠ lFls := by decide
@[simp] theorem pj_lFls_ne_pjUs : lFls ≠ pjUs := by decide
@[simp] theorem pj_pjUs_ne_lKb : pjUs ≠ lKb := by decide
@[simp] theorem pj_lKb_ne_pjUs : lKb ≠ pjUs := by decide
@[simp] theorem pj_pjTb_ne_pjA : pjTb ≠ pjA := by decide
@[simp] theorem pj_pjTb_ne_pjTe : pjTb ≠ pjTe := by decide
@[simp] theorem pj_pjTb_ne_pjHh : pjTb ≠ pjHh := by decide
@[simp] theorem pj_pjTb_ne_pjT : pjTb ≠ pjT := by decide
@[simp] theorem pj_pjTb_ne_pjUs : pjTb ≠ pjUs := by decide
@[simp] theorem pj_pjTb_ne_pjTq : pjTb ≠ pjTq := by decide
@[simp] theorem pj_pjTb_ne_pjNf : pjTb ≠ pjNf := by decide
@[simp] theorem pj_pjTb_ne_pjVa : pjTb ≠ pjVa := by decide
@[simp] theorem pj_pjTb_ne_pjNa : pjTb ≠ pjNa := by decide
@[simp] theorem pj_pjTb_ne_pjNp : pjTb ≠ pjNp := by decide
@[simp] theorem pj_pjTb_ne_pjLp : pjTb ≠ pjLp := by decide
@[simp] theorem pj_pjTb_ne_pjLl : pjTb ≠ pjLl := by decide
@[simp] theorem pj_pjTb_ne_pjG : pjTb ≠ pjG := by decide
@[simp] theorem pj_pjTb_ne_pjR : pjTb ≠ pjR := by decide
@[simp] theorem pj_pjTb_ne_kFu : pjTb ≠ kFu := by decide
@[simp] theorem pj_kFu_ne_pjTb : kFu ≠ pjTb := by decide
@[simp] theorem pj_pjTb_ne_kD : pjTb ≠ kD := by decide
@[simp] theorem pj_kD_ne_pjTb : kD ≠ pjTb := by decide
@[simp] theorem pj_pjTb_ne_ibSn : pjTb ≠ ibSn := by decide
@[simp] theorem pj_ibSn_ne_pjTb : ibSn ≠ pjTb := by decide
@[simp] theorem pj_pjTb_ne_ibIx : pjTb ≠ ibIx := by decide
@[simp] theorem pj_ibIx_ne_pjTb : ibIx ≠ pjTb := by decide
@[simp] theorem pj_pjTb_ne_ibPe : pjTb ≠ ibPe := by decide
@[simp] theorem pj_ibPe_ne_pjTb : ibPe ≠ pjTb := by decide
@[simp] theorem pj_pjTb_ne_lFl : pjTb ≠ lFl := by decide
@[simp] theorem pj_lFl_ne_pjTb : lFl ≠ pjTb := by decide
@[simp] theorem pj_pjTb_ne_lDh : pjTb ≠ lDh := by decide
@[simp] theorem pj_lDh_ne_pjTb : lDh ≠ pjTb := by decide
@[simp] theorem pj_pjTb_ne_lDt : pjTb ≠ lDt := by decide
@[simp] theorem pj_lDt_ne_pjTb : lDt ≠ pjTb := by decide
@[simp] theorem pj_pjTb_ne_lDg : pjTb ≠ lDg := by decide
@[simp] theorem pj_lDg_ne_pjTb : lDg ≠ pjTb := by decide
@[simp] theorem pj_pjTb_ne_lDi : pjTb ≠ lDi := by decide
@[simp] theorem pj_lDi_ne_pjTb : lDi ≠ pjTb := by decide
@[simp] theorem pj_pjTb_ne_lRp : pjTb ≠ lRp := by decide
@[simp] theorem pj_lRp_ne_pjTb : lRp ≠ pjTb := by decide
@[simp] theorem pj_pjTb_ne_lRn : pjTb ≠ lRn := by decide
@[simp] theorem pj_lRn_ne_pjTb : lRn ≠ pjTb := by decide
@[simp] theorem pj_pjTb_ne_lDir : pjTb ≠ lDir := by decide
@[simp] theorem pj_lDir_ne_pjTb : lDir ≠ pjTb := by decide
@[simp] theorem pj_pjTb_ne_lFle : pjTb ≠ lFle := by decide
@[simp] theorem pj_lFle_ne_pjTb : lFle ≠ pjTb := by decide
@[simp] theorem pj_pjTb_ne_lFls : pjTb ≠ lFls := by decide
@[simp] theorem pj_lFls_ne_pjTb : lFls ≠ pjTb := by decide
@[simp] theorem pj_pjTb_ne_lKb : pjTb ≠ lKb := by decide
@[simp] theorem pj_lKb_ne_pjTb : lKb ≠ pjTb := by decide
@[simp] theorem pj_pjTq_ne_pjA : pjTq ≠ pjA := by decide
@[simp] theorem pj_pjTq_ne_pjTe : pjTq ≠ pjTe := by decide
@[simp] theorem pj_pjTq_ne_pjHh : pjTq ≠ pjHh := by decide
@[simp] theorem pj_pjTq_ne_pjT : pjTq ≠ pjT := by decide
@[simp] theorem pj_pjTq_ne_pjUs : pjTq ≠ pjUs := by decide
@[simp] theorem pj_pjTq_ne_pjTb : pjTq ≠ pjTb := by decide
@[simp] theorem pj_pjTq_ne_pjNf : pjTq ≠ pjNf := by decide
@[simp] theorem pj_pjTq_ne_pjVa : pjTq ≠ pjVa := by decide
@[simp] theorem pj_pjTq_ne_pjNa : pjTq ≠ pjNa := by decide
@[simp] theorem pj_pjTq_ne_pjNp : pjTq ≠ pjNp := by decide
@[simp] theorem pj_pjTq_ne_pjLp : pjTq ≠ pjLp := by decide
@[simp] theorem pj_pjTq_ne_pjLl : pjTq ≠ pjLl := by decide
@[simp] theorem pj_pjTq_ne_pjG : pjTq ≠ pjG := by decide
@[simp] theorem pj_pjTq_ne_pjR : pjTq ≠ pjR := by decide
@[simp] theorem pj_pjTq_ne_kFu : pjTq ≠ kFu := by decide
@[simp] theorem pj_kFu_ne_pjTq : kFu ≠ pjTq := by decide
@[simp] theorem pj_pjTq_ne_kD : pjTq ≠ kD := by decide
@[simp] theorem pj_kD_ne_pjTq : kD ≠ pjTq := by decide
@[simp] theorem pj_pjTq_ne_ibSn : pjTq ≠ ibSn := by decide
@[simp] theorem pj_ibSn_ne_pjTq : ibSn ≠ pjTq := by decide
@[simp] theorem pj_pjTq_ne_ibIx : pjTq ≠ ibIx := by decide
@[simp] theorem pj_ibIx_ne_pjTq : ibIx ≠ pjTq := by decide
@[simp] theorem pj_pjTq_ne_ibPe : pjTq ≠ ibPe := by decide
@[simp] theorem pj_ibPe_ne_pjTq : ibPe ≠ pjTq := by decide
@[simp] theorem pj_pjTq_ne_lFl : pjTq ≠ lFl := by decide
@[simp] theorem pj_lFl_ne_pjTq : lFl ≠ pjTq := by decide
@[simp] theorem pj_pjTq_ne_lDh : pjTq ≠ lDh := by decide
@[simp] theorem pj_lDh_ne_pjTq : lDh ≠ pjTq := by decide
@[simp] theorem pj_pjTq_ne_lDt : pjTq ≠ lDt := by decide
@[simp] theorem pj_lDt_ne_pjTq : lDt ≠ pjTq := by decide
@[simp] theorem pj_pjTq_ne_lDg : pjTq ≠ lDg := by decide
@[simp] theorem pj_lDg_ne_pjTq : lDg ≠ pjTq := by decide
@[simp] theorem pj_pjTq_ne_lDi : pjTq ≠ lDi := by decide
@[simp] theorem pj_lDi_ne_pjTq : lDi ≠ pjTq := by decide
@[simp] theorem pj_pjTq_ne_lRp : pjTq ≠ lRp := by decide
@[simp] theorem pj_lRp_ne_pjTq : lRp ≠ pjTq := by decide
@[simp] theorem pj_pjTq_ne_lRn : pjTq ≠ lRn := by decide
@[simp] theorem pj_lRn_ne_pjTq : lRn ≠ pjTq := by decide
@[simp] theorem pj_pjTq_ne_lDir : pjTq ≠ lDir := by decide
@[simp] theorem pj_lDir_ne_pjTq : lDir ≠ pjTq := by decide
@[simp] theorem pj_pjTq_ne_lFle : pjTq ≠ lFle := by decide
@[simp] theorem pj_lFle_ne_pjTq : lFle ≠ pjTq := by decide
@[simp] theorem pj_pjTq_ne_lFls : pjTq ≠ lFls := by decide
@[simp] theorem pj_lFls_ne_pjTq : lFls ≠ pjTq := by decide
@[simp] theorem pj_pjTq_ne_lKb : pjTq ≠ lKb := by decide
@[simp] theorem pj_lKb_ne_pjTq : lKb ≠ pjTq := by decide
@[simp] theorem pj_pjNf_ne_pjA : pjNf ≠ pjA := by decide
@[simp] theorem pj_pjNf_ne_pjTe : pjNf ≠ pjTe := by decide
@[simp] theorem pj_pjNf_ne_pjHh : pjNf ≠ pjHh := by decide
@[simp] theorem pj_pjNf_ne_pjT : pjNf ≠ pjT := by decide
@[simp] theorem pj_pjNf_ne_pjUs : pjNf ≠ pjUs := by decide
@[simp] theorem pj_pjNf_ne_pjTb : pjNf ≠ pjTb := by decide
@[simp] theorem pj_pjNf_ne_pjTq : pjNf ≠ pjTq := by decide
@[simp] theorem pj_pjNf_ne_pjVa : pjNf ≠ pjVa := by decide
@[simp] theorem pj_pjNf_ne_pjNa : pjNf ≠ pjNa := by decide
@[simp] theorem pj_pjNf_ne_pjNp : pjNf ≠ pjNp := by decide
@[simp] theorem pj_pjNf_ne_pjLp : pjNf ≠ pjLp := by decide
@[simp] theorem pj_pjNf_ne_pjLl : pjNf ≠ pjLl := by decide
@[simp] theorem pj_pjNf_ne_pjG : pjNf ≠ pjG := by decide
@[simp] theorem pj_pjNf_ne_pjR : pjNf ≠ pjR := by decide
@[simp] theorem pj_pjNf_ne_kFu : pjNf ≠ kFu := by decide
@[simp] theorem pj_kFu_ne_pjNf : kFu ≠ pjNf := by decide
@[simp] theorem pj_pjNf_ne_kD : pjNf ≠ kD := by decide
@[simp] theorem pj_kD_ne_pjNf : kD ≠ pjNf := by decide
@[simp] theorem pj_pjNf_ne_ibSn : pjNf ≠ ibSn := by decide
@[simp] theorem pj_ibSn_ne_pjNf : ibSn ≠ pjNf := by decide
@[simp] theorem pj_pjNf_ne_ibIx : pjNf ≠ ibIx := by decide
@[simp] theorem pj_ibIx_ne_pjNf : ibIx ≠ pjNf := by decide
@[simp] theorem pj_pjNf_ne_ibPe : pjNf ≠ ibPe := by decide
@[simp] theorem pj_ibPe_ne_pjNf : ibPe ≠ pjNf := by decide
@[simp] theorem pj_pjNf_ne_lFl : pjNf ≠ lFl := by decide
@[simp] theorem pj_lFl_ne_pjNf : lFl ≠ pjNf := by decide
@[simp] theorem pj_pjNf_ne_lDh : pjNf ≠ lDh := by decide
@[simp] theorem pj_lDh_ne_pjNf : lDh ≠ pjNf := by decide
@[simp] theorem pj_pjNf_ne_lDt : pjNf ≠ lDt := by decide
@[simp] theorem pj_lDt_ne_pjNf : lDt ≠ pjNf := by decide
@[simp] theorem pj_pjNf_ne_lDg : pjNf ≠ lDg := by decide
@[simp] theorem pj_lDg_ne_pjNf : lDg ≠ pjNf := by decide
@[simp] theorem pj_pjNf_ne_lDi : pjNf ≠ lDi := by decide
@[simp] theorem pj_lDi_ne_pjNf : lDi ≠ pjNf := by decide
@[simp] theorem pj_pjNf_ne_lRp : pjNf ≠ lRp := by decide
@[simp] theorem pj_lRp_ne_pjNf : lRp ≠ pjNf := by decide
@[simp] theorem pj_pjNf_ne_lRn : pjNf ≠ lRn := by decide
@[simp] theorem pj_lRn_ne_pjNf : lRn ≠ pjNf := by decide
@[simp] theorem pj_pjNf_ne_lDir : pjNf ≠ lDir := by decide
@[simp] theorem pj_lDir_ne_pjNf : lDir ≠ pjNf := by decide
@[simp] theorem pj_pjNf_ne_lFle : pjNf ≠ lFle := by decide
@[simp] theorem pj_lFle_ne_pjNf : lFle ≠ pjNf := by decide
@[simp] theorem pj_pjNf_ne_lFls : pjNf ≠ lFls := by decide
@[simp] theorem pj_lFls_ne_pjNf : lFls ≠ pjNf := by decide
@[simp] theorem pj_pjNf_ne_lKb : pjNf ≠ lKb := by decide
@[simp] theorem pj_lKb_ne_pjNf : lKb ≠ pjNf := by decide
@[simp] theorem pj_pjVa_ne_pjA : pjVa ≠ pjA := by decide
@[simp] theorem pj_pjVa_ne_pjTe : pjVa ≠ pjTe := by decide
@[simp] theorem pj_pjVa_ne_pjHh : pjVa ≠ pjHh := by decide
@[simp] theorem pj_pjVa_ne_pjT : pjVa ≠ pjT := by decide
@[simp] theorem pj_pjVa_ne_pjUs : pjVa ≠ pjUs := by decide
@[simp] theorem pj_pjVa_ne_pjTb : pjVa ≠ pjTb := by decide
@[simp] theorem pj_pjVa_ne_pjTq : pjVa ≠ pjTq := by decide
@[simp] theorem pj_pjVa_ne_pjNf : pjVa ≠ pjNf := by decide
@[simp] theorem pj_pjVa_ne_pjNa : pjVa ≠ pjNa := by decide
@[simp] theorem pj_pjVa_ne_pjNp : pjVa ≠ pjNp := by decide
@[simp] theorem pj_pjVa_ne_pjLp : pjVa ≠ pjLp := by decide
@[simp] theorem pj_pjVa_ne_pjLl : pjVa ≠ pjLl := by decide
@[simp] theorem pj_pjVa_ne_pjG : pjVa ≠ pjG := by decide
@[simp] theorem pj_pjVa_ne_pjR : pjVa ≠ pjR := by decide
@[simp] theorem pj_pjVa_ne_kFu : pjVa ≠ kFu := by decide
@[simp] theorem pj_kFu_ne_pjVa : kFu ≠ pjVa := by decide
@[simp] theorem pj_pjVa_ne_kD : pjVa ≠ kD := by decide
@[simp] theorem pj_kD_ne_pjVa : kD ≠ pjVa := by decide
@[simp] theorem pj_pjVa_ne_ibSn : pjVa ≠ ibSn := by decide
@[simp] theorem pj_ibSn_ne_pjVa : ibSn ≠ pjVa := by decide
@[simp] theorem pj_pjVa_ne_ibIx : pjVa ≠ ibIx := by decide
@[simp] theorem pj_ibIx_ne_pjVa : ibIx ≠ pjVa := by decide
@[simp] theorem pj_pjVa_ne_ibPe : pjVa ≠ ibPe := by decide
@[simp] theorem pj_ibPe_ne_pjVa : ibPe ≠ pjVa := by decide
@[simp] theorem pj_pjVa_ne_lFl : pjVa ≠ lFl := by decide
@[simp] theorem pj_lFl_ne_pjVa : lFl ≠ pjVa := by decide
@[simp] theorem pj_pjVa_ne_lDh : pjVa ≠ lDh := by decide
@[simp] theorem pj_lDh_ne_pjVa : lDh ≠ pjVa := by decide
@[simp] theorem pj_pjVa_ne_lDt : pjVa ≠ lDt := by decide
@[simp] theorem pj_lDt_ne_pjVa : lDt ≠ pjVa := by decide
@[simp] theorem pj_pjVa_ne_lDg : pjVa ≠ lDg := by decide
@[simp] theorem pj_lDg_ne_pjVa : lDg ≠ pjVa := by decide
@[simp] theorem pj_pjVa_ne_lDi : pjVa ≠ lDi := by decide
@[simp] theorem pj_lDi_ne_pjVa : lDi ≠ pjVa := by decide
@[simp] theorem pj_pjVa_ne_lRp : pjVa ≠ lRp := by decide
@[simp] theorem pj_lRp_ne_pjVa : lRp ≠ pjVa := by decide
@[simp] theorem pj_pjVa_ne_lRn : pjVa ≠ lRn := by decide
@[simp] theorem pj_lRn_ne_pjVa : lRn ≠ pjVa := by decide
@[simp] theorem pj_pjVa_ne_lDir : pjVa ≠ lDir := by decide
@[simp] theorem pj_lDir_ne_pjVa : lDir ≠ pjVa := by decide
@[simp] theorem pj_pjVa_ne_lFle : pjVa ≠ lFle := by decide
@[simp] theorem pj_lFle_ne_pjVa : lFle ≠ pjVa := by decide
@[simp] theorem pj_pjVa_ne_lFls : pjVa ≠ lFls := by decide
@[simp] theorem pj_lFls_ne_pjVa : lFls ≠ pjVa := by decide
@[simp] theorem pj_pjVa_ne_lKb : pjVa ≠ lKb := by decide
@[simp] theorem pj_lKb_ne_pjVa : lKb ≠ pjVa := by decide
@[simp] theorem pj_pjNa_ne_pjA : pjNa ≠ pjA := by decide
@[simp] theorem pj_pjNa_ne_pjTe : pjNa ≠ pjTe := by decide
@[simp] theorem pj_pjNa_ne_pjHh : pjNa ≠ pjHh := by decide
@[simp] theorem pj_pjNa_ne_pjT : pjNa ≠ pjT := by decide
@[simp] theorem pj_pjNa_ne_pjUs : pjNa ≠ pjUs := by decide
@[simp] theorem pj_pjNa_ne_pjTb : pjNa ≠ pjTb := by decide
@[simp] theorem pj_pjNa_ne_pjTq : pjNa ≠ pjTq := by decide
@[simp] theorem pj_pjNa_ne_pjNf : pjNa ≠ pjNf := by decide
@[simp] theorem pj_pjNa_ne_pjVa : pjNa ≠ pjVa := by decide
@[simp] theorem pj_pjNa_ne_pjNp : pjNa ≠ pjNp := by decide
@[simp] theorem pj_pjNa_ne_pjLp : pjNa ≠ pjLp := by decide
@[simp] theorem pj_pjNa_ne_pjLl : pjNa ≠ pjLl := by decide
@[simp] theorem pj_pjNa_ne_pjG : pjNa ≠ pjG := by decide
@[simp] theorem pj_pjNa_ne_pjR : pjNa ≠ pjR := by decide
@[simp] theorem pj_pjNa_ne_kFu : pjNa ≠ kFu := by decide
@[simp] theorem pj_kFu_ne_pjNa : kFu ≠ pjNa := by decide
@[simp] theorem pj_pjNa_ne_kD : pjNa ≠ kD := by decide
@[simp] theorem pj_kD_ne_pjNa : kD ≠ pjNa := by decide
@[simp] theorem pj_pjNa_ne_ibSn : pjNa ≠ ibSn := by decide
@[simp] theorem pj_ibSn_ne_pjNa : ibSn ≠ pjNa := by decide
@[simp] theorem pj_pjNa_ne_ibIx : pjNa ≠ ibIx := by decide
@[simp] theorem pj_ibIx_ne_pjNa : ibIx ≠ pjNa := by decide
@[simp] theorem pj_pjNa_ne_ibPe : pjNa ≠ ibPe := by decide
@[simp] theorem pj_ibPe_ne_pjNa : ibPe ≠ pjNa := by decide
@[simp] theorem pj_pjNa_ne_lFl : pjNa ≠ lFl := by decide
@[simp] theorem pj_lFl_ne_pjNa : lFl ≠ pjNa := by decide
@[simp] theorem pj_pjNa_ne_lDh : pjNa ≠ lDh := by decide
@[simp] theorem pj_lDh_ne_pjNa : lDh ≠ pjNa := by decide
@[simp] theorem pj_pjNa_ne_lDt : pjNa ≠ lDt := by decide
@[simp] theorem pj_lDt_ne_pjNa : lDt ≠ pjNa := by decide
@[simp] theorem pj_pjNa_ne_lDg : pjNa ≠ lDg := by decide
@[simp] theorem pj_lDg_ne_pjNa : lDg ≠ pjNa := by decide
@[simp] theorem pj_pjNa_ne_lDi : pjNa ≠ lDi := by decide
@[simp] theorem pj_lDi_ne_pjNa : lDi ≠ pjNa := by decide
@[simp] theorem pj_pjNa_ne_lRp : pjNa ≠ lRp := by decide
@[simp] theorem pj_lRp_ne_pjNa : lRp ≠ pjNa := by decide
@[simp] theorem pj_pjNa_ne_lRn : pjNa ≠ lRn := by decide
@[simp] theorem pj_lRn_ne_pjNa : lRn ≠ pjNa := by decide
@[simp] theorem pj_pjNa_ne_lDir : pjNa ≠ lDir := by decide
@[simp] theorem pj_lDir_ne_pjNa : lDir ≠ pjNa := by decide
@[simp] theorem pj_pjNa_ne_lFle : pjNa ≠ lFle := by decide
@[simp] theorem pj_lFle_ne_pjNa : lFle ≠ pjNa := by decide
@[simp] theorem pj_pjNa_ne_lFls : pjNa ≠ lFls := by decide
@[simp] theorem pj_lFls_ne_pjNa : lFls ≠ pjNa := by decide
@[simp] theorem pj_pjNa_ne_lKb : pjNa ≠ lKb := by decide
@[simp] theorem pj_lKb_ne_pjNa : lKb ≠ pjNa := by decide
@[simp] theorem pj_pjNp_ne_pjA : pjNp ≠ pjA := by decide
@[simp] theorem pj_pjNp_ne_pjTe : pjNp ≠ pjTe := by decide
@[simp] theorem pj_pjNp_ne_pjHh : pjNp ≠ pjHh := by decide
@[simp] theorem pj_pjNp_ne_pjT : pjNp ≠ pjT := by decide
@[simp] theorem pj_pjNp_ne_pjUs : pjNp ≠ pjUs := by decide
@[simp] theorem pj_pjNp_ne_pjTb : pjNp ≠ pjTb := by decide
@[simp] theorem pj_pjNp_ne_pjTq : pjNp ≠ pjTq := by decide
@[simp] theorem pj_pjNp_ne_pjNf : pjNp ≠ pjNf := by decide
@[simp] theorem pj_pjNp_ne_pjVa : pjNp ≠ pjVa := by decide
@[simp] theorem pj_pjNp_ne_pjNa : pjNp ≠ pjNa := by decide
@[simp] theorem pj_pjNp_ne_pjLp : pjNp ≠ pjLp := by decide
@[simp] theorem pj_pjNp_ne_pjLl : pjNp ≠ pjLl := by decide
@[simp] theorem pj_pjNp_ne_pjG : pjNp ≠ pjG := by decide
@[simp] theorem pj_pjNp_ne_pjR : pjNp ≠ pjR := by decide
@[simp] theorem pj_pjNp_ne_kFu : pjNp ≠ kFu := by decide
@[simp] theorem pj_kFu_ne_pjNp : kFu ≠ pjNp := by decide
@[simp] theorem pj_pjNp_ne_kD : pjNp ≠ kD := by decide
@[simp] theorem pj_kD_ne_pjNp : kD ≠ pjNp := by decide
@[simp] theorem pj_pjNp_ne_ibSn : pjNp ≠ ibSn := by decide
@[simp] theorem pj_ibSn_ne_pjNp : ibSn ≠ pjNp := by decide
@[simp] theorem pj_pjNp_ne_ibIx : pjNp ≠ ibIx := by decide
@[simp] theorem pj_ibIx_ne_pjNp : ibIx ≠ pjNp := by decide
@[simp] theorem pj_pjNp_ne_ibPe : pjNp ≠ ibPe := by decide
@[simp] theorem pj_ibPe_ne_pjNp : ibPe ≠ pjNp := by decide
@[simp] theorem pj_pjNp_ne_lFl : pjNp ≠ lFl := by decide
@[simp] theorem pj_lFl_ne_pjNp : lFl ≠ pjNp := by decide
@[simp] theorem pj_pjNp_ne_lDh : pjNp ≠ lDh := by decide
@[simp] theorem pj_lDh_ne_pjNp : lDh ≠ pjNp := by decide
@[simp] theorem pj_pjNp_ne_lDt : pjNp ≠ lDt := by decide
@[simp] theorem pj_lDt_ne_pjNp : lDt ≠ pjNp := by decide
@[simp] theorem pj_pjNp_ne_lDg : pjNp ≠ lDg := by decide
@[simp] theorem pj_lDg_ne_pjNp : lDg ≠ pjNp := by decide
@[simp] theorem pj_pjNp_ne_lDi : pjNp ≠ lDi := by decide
@[simp] theorem pj_lDi_ne_pjNp : lDi ≠ pjNp := by decide
@[simp] theorem pj_pjNp_ne_lRp : pjNp ≠ lRp := by decide
@[simp] theorem pj_lRp_ne_pjNp : lRp ≠ pjNp := by decide
@[simp] theorem pj_pjNp_ne_lRn : pjNp ≠ lRn := by decide
@[simp] theorem pj_lRn_ne_pjNp : lRn ≠ pjNp := by decide
@[simp] theorem pj_pjNp_ne_lDir : pjNp ≠ lDir := by decide
@[simp] theorem pj_lDir_ne_pjNp : lDir ≠ pjNp := by decide
@[simp] theorem pj_pjNp_ne_lFle : pjNp ≠ lFle := by decide
@[simp] theorem pj_lFle_ne_pjNp : lFle ≠ pjNp := by decide
@[simp] theorem pj_pjNp_ne_lFls : pjNp ≠ lFls := by decide
@[simp] theorem pj_lFls_ne_pjNp : lFls ≠ pjNp := by decide
@[simp] theorem pj_pjNp_ne_lKb : pjNp ≠ lKb := by decide
@[simp] theorem pj_lKb_ne_pjNp : lKb ≠ pjNp := by decide
@[simp] theorem pj_pjLp_ne_pjA : pjLp ≠ pjA := by decide
@[simp] theorem pj_pjLp_ne_pjTe : pjLp ≠ pjTe := by decide
@[simp] theorem pj_pjLp_ne_pjHh : pjLp ≠ pjHh := by decide
@[simp] theorem pj_pjLp_ne_pjT : pjLp ≠ pjT := by decide
@[simp] theorem pj_pjLp_ne_pjUs : pjLp ≠ pjUs := by decide
@[simp] theorem pj_pjLp_ne_pjTb : pjLp ≠ pjTb := by decide
@[simp] theorem pj_pjLp_ne_pjTq : pjLp ≠ pjTq := by decide
@[simp] theorem pj_pjLp_ne_pjNf : pjLp ≠ pjNf := by decide
@[simp] theorem pj_pjLp_ne_pjVa : pjLp ≠ pjVa := by decide
@[simp] theorem pj_pjLp_ne_pjNa : pjLp ≠ pjNa := by decide
@[simp] theorem pj_pjLp_ne_pjNp : pjLp ≠ pjNp := by decide
@[simp] theorem pj_pjLp_ne_pjLl : pjLp ≠ pjLl := by decide
@[simp] theorem pj_pjLp_ne_pjG : pjLp ≠ pjG := by decide
@[simp] theorem pj_pjLp_ne_pjR : pjLp ≠ pjR := by decide
@[simp] theorem pj_pjLp_ne_kFu : pjLp ≠ kFu := by decide
@[simp] theorem pj_kFu_ne_pjLp : kFu ≠ pjLp := by decide
@[simp] theorem pj_pjLp_ne_kD : pjLp ≠ kD := by decide
@[simp] theorem pj_kD_ne_pjLp : kD ≠ pjLp := by decide
@[simp] theorem pj_pjLp_ne_ibSn : pjLp ≠ ibSn := by decide
@[simp] theorem pj_ibSn_ne_pjLp : ibSn ≠ pjLp := by decide
@[simp] theorem pj_pjLp_ne_ibIx : pjLp ≠ ibIx := by decide
@[simp] theorem pj_ibIx_ne_pjLp : ibIx ≠ pjLp := by decide
@[simp] theorem pj_pjLp_ne_ibPe : pjLp ≠ ibPe := by decide
@[simp] theorem pj_ibPe_ne_pjLp : ibPe ≠ pjLp := by decide
@[simp] theorem pj_pjLp_ne_lFl : pjLp ≠ lFl := by decide
@[simp] theorem pj_lFl_ne_pjLp : lFl ≠ pjLp := by decide
@[simp] theorem pj_pjLp_ne_lDh : pjLp ≠ lDh := by decide
@[simp] theorem pj_lDh_ne_pjLp : lDh ≠ pjLp := by decide
@[simp] theorem pj_pjLp_ne_lDt : pjLp ≠ lDt := by decide
@[simp] theorem pj_lDt_ne_pjLp : lDt ≠ pjLp := by decide
@[simp] theorem pj_pjLp_ne_lDg : pjLp ≠ lDg := by decide
@[simp] theorem pj_lDg_ne_pjLp : lDg ≠ pjLp := by decide
@[simp] theorem pj_pjLp_ne_lDi : pjLp ≠ lDi := by decide
@[simp] theorem pj_lDi_ne_pjLp : lDi ≠ pjLp := by decide
@[simp] theorem pj_pjLp_ne_lRp : pjLp ≠ lRp := by decide
@[simp] theorem pj_lRp_ne_pjLp : lRp ≠ pjLp := by decide
@[simp] theorem pj_pjLp_ne_lRn : pjLp ≠ lRn := by decide
@[simp] theorem pj_lRn_ne_pjLp : lRn ≠ pjLp := by decide
@[simp] theorem pj_pjLp_ne_lDir : pjLp ≠ lDir := by decide
@[simp] theorem pj_lDir_ne_pjLp : lDir ≠ pjLp := by decide
@[simp] theorem pj_pjLp_ne_lFle : pjLp ≠ lFle := by decide
@[simp] theorem pj_lFle_ne_pjLp : lFle ≠ pjLp := by decide
@[simp] theorem pj_pjLp_ne_lFls : pjLp ≠ lFls := by decide
@[simp] theorem pj_lFls_ne_pjLp : lFls ≠ pjLp := by decide
@[simp] theorem pj_pjLp_ne_lKb : pjLp ≠ lKb := by decide
@[simp] theorem pj_lKb_ne_pjLp : lKb ≠ pjLp := by decide
@[simp] theorem pj_pjLl_ne_pjA : pjLl ≠ pjA := by decide
@[simp] theorem pj_pjLl_ne_pjTe : pjLl ≠ pjTe := by decide
@[simp] theorem pj_pjLl_ne_pjHh : pjLl ≠ pjHh := by decide
@[simp] theorem pj_pjLl_ne_pjT : pjLl ≠ pjT := by decide
@[simp] theorem pj_pjLl_ne_pjUs : pjLl ≠ pjUs := by decide
@[simp] theorem pj_pjLl_ne_pjTb : pjLl ≠ pjTb := by decide
@[simp] theorem pj_pjLl_ne_pjTq : pjLl ≠ pjTq := by decide
@[simp] theorem pj_pjLl_ne_pjNf : pjLl ≠ pjNf := by decide
@[simp] theorem pj_pjLl_ne_pjVa : pjLl ≠ pjVa := by decide
@[simp] theorem pj_pjLl_ne_pjNa : pjLl ≠ pjNa := by decide
@[simp] theorem pj_pjLl_ne_pjNp : pjLl ≠ pjNp := by decide
@[simp] theorem pj_pjLl_ne_pjLp : pjLl ≠ pjLp := by decide
@[simp] theorem pj_pjLl_ne_pjG : pjLl ≠ pjG := by decide
@[simp] theorem pj_pjLl_ne_pjR : pjLl ≠ pjR := by decide
@[simp] theorem pj_pjLl_ne_kFu : pjLl ≠ kFu := by decide
@[simp] theorem pj_kFu_ne_pjLl : kFu ≠ pjLl := by decide
@[simp] theorem pj_pjLl_ne_kD : pjLl ≠ kD := by decide
@[simp] theorem pj_kD_ne_pjLl : kD ≠ pjLl := by decide
@[simp] theorem pj_pjLl_ne_ibSn : pjLl ≠ ibSn := by decide
@[simp] theorem pj_ibSn_ne_pjLl : ibSn ≠ pjLl := by decide
@[simp] theorem pj_pjLl_ne_ibIx : pjLl ≠ ibIx := by decide
@[simp] theorem pj_ibIx_ne_pjLl : ibIx ≠ pjLl := by decide
@[simp] theorem pj_pjLl_ne_ibPe : pjLl ≠ ibPe := by decide
@[simp] theorem pj_ibPe_ne_pjLl : ibPe ≠ pjLl := by decide
@[simp] theorem pj_pjLl_ne_lFl : pjLl ≠ lFl := by decide
@[simp] theorem pj_lFl_ne_pjLl : lFl ≠ pjLl := by decide
@[simp] theorem pj_pjLl_ne_lDh : pjLl ≠ lDh := by decide
@[simp] theorem pj_lDh_ne_pjLl : lDh ≠ pjLl := by decide
@[simp] theorem pj_pjLl_ne_lDt : pjLl ≠ lDt := by decide
@[simp] theorem pj_lDt_ne_pjLl : lDt ≠ pjLl := by decide
@[simp] theorem pj_pjLl_ne_lDg : pjLl ≠ lDg := by decide
@[simp] theorem pj_lDg_ne_pjLl : lDg ≠ pjLl := by decide
@[simp] theorem pj_pjLl_ne_lDi : pjLl ≠ lDi := by decide
@[simp] theorem pj_lDi_ne_pjLl : lDi ≠ pjLl := by decide
@[simp] theorem pj_pjLl_ne_lRp : pjLl ≠ lRp := by decide
@[simp] theorem pj_lRp_ne_pjLl : lRp ≠ pjLl := by decide
@[simp] theorem pj_pjLl_ne_lRn : pjLl ≠ lRn := by decide
@[simp] theorem pj_lRn_ne_pjLl : lRn ≠ pjLl := by decide
@[simp] theorem pj_pjLl_ne_lDir : pjLl ≠ lDir := by decide
@[simp] theorem pj_lDir_ne_pjLl : lDir ≠ pjLl := by decide
@[simp] theorem pj_pjLl_ne_lFle : pjLl ≠ lFle := by decide
@[simp] theorem pj_lFle_ne_pjLl : lFle ≠ pjLl := by decide
@[simp] theorem pj_pjLl_ne_lFls : pjLl ≠ lFls := by decide
@[simp] theorem pj_lFls_ne_pjLl : lFls ≠ pjLl := by decide
@[simp] theorem pj_pjLl_ne_lKb : pjLl ≠ lKb := by decide
@[simp] theorem pj_lKb_ne_pjLl : lKb ≠ pjLl := by decide
@[simp] theorem pj_pjG_ne_pjA : pjG ≠ pjA := by decide
@[simp] theorem pj_pjG_ne_pjTe : pjG ≠ pjTe := by decide
@[simp] theorem pj_pjG_ne_pjHh : pjG ≠ pjHh := by decide
@[simp] theorem pj_pjG_ne_pjT : pjG ≠ pjT := by decide
@[simp] theorem pj_pjG_ne_pjUs : pjG ≠ pjUs := by decide
@[simp] theorem pj_pjG_ne_pjTb : pjG ≠ pjTb := by decide
@[simp] theorem pj_pjG_ne_pjTq : pjG ≠ pjTq := by decide
@[simp] theorem pj_pjG_ne_pjNf : pjG ≠ pjNf := by decide
@[simp] theorem pj_pjG_ne_pjVa : pjG ≠ pjVa := by decide
@[simp] theorem pj_pjG_ne_pjNa : pjG ≠ pjNa := by decide
@[simp] theorem pj_pjG_ne_pjNp : pjG ≠ pjNp := by decide
@[simp] theorem pj_pjG_ne_pjLp : pjG ≠ pjLp := by decide
@[simp] theorem pj_pjG_ne_pjLl : pjG ≠ pjLl := by decide
@[simp] theorem pj_pjG_ne_pjR : pjG ≠ pjR := by decide
@[simp] theorem pj_pjG_ne_kFu : pjG ≠ kFu := by decide
@[simp] theorem pj_kFu_ne_pjG : kFu ≠ pjG := by decide
@[simp] theorem pj_pjG_ne_kD : pjG ≠ kD := by decide
@[simp] theorem pj_kD_ne_pjG : kD ≠ pjG := by decide
@[simp] theorem pj_pjG_ne_ibSn : pjG ≠ ibSn := by decide
@[simp] theorem pj_ibSn_ne_pjG : ibSn ≠ pjG := by decide
@[simp] theorem pj_pjG_ne_ibIx : pjG ≠ ibIx := by decide
@[simp] theorem pj_ibIx_ne_pjG : ibIx ≠ pjG := by decide
@[simp] theorem pj_pjG_ne_ibPe : pjG ≠ ibPe := by decide
@[simp] theorem pj_ibPe_ne_pjG : ibPe ≠ pjG := by decide
@[simp] theorem pj_pjG_ne_lFl : pjG ≠ lFl := by decide
@[simp] theorem pj_lFl_ne_pjG : lFl ≠ pjG := by decide
@[simp] theorem pj_pjG_ne_lDh : pjG ≠ lDh := by decide
@[simp] theorem pj_lDh_ne_pjG : lDh ≠ pjG := by decide
@[simp] theorem pj_pjG_ne_lDt : pjG ≠ lDt := by decide
@[simp] theorem pj_lDt_ne_pjG : lDt ≠ pjG := by decide
@[simp] theorem pj_pjG_ne_lDg : pjG ≠ lDg := by decide
@[simp] theorem pj_lDg_ne_pjG : lDg ≠ pjG := by decide
@[simp] theorem pj_pjG_ne_lDi : pjG ≠ lDi := by decide
@[simp] theorem pj_lDi_ne_pjG : lDi ≠ pjG := by decide
@[simp] theorem pj_pjG_ne_lRp : pjG ≠ lRp := by decide
@[simp] theorem pj_lRp_ne_pjG : lRp ≠ pjG := by decide
@[simp] theorem pj_pjG_ne_lRn : pjG ≠ lRn := by decide
@[simp] theorem pj_lRn_ne_pjG : lRn ≠ pjG := by decide
@[simp] theorem pj_pjG_ne_lDir : pjG ≠ lDir := by decide
@[simp] theorem pj_lDir_ne_pjG : lDir ≠ pjG := by decide
@[simp] theorem pj_pjG_ne_lFle : pjG ≠ lFle := by decide
@[simp] theorem pj_lFle_ne_pjG : lFle ≠ pjG := by decide
@[simp] theorem pj_pjG_ne_lFls : pjG ≠ lFls := by decide
@[simp] theorem pj_lFls_ne_pjG : lFls ≠ pjG := by decide
@[simp] theorem pj_pjG_ne_lKb : pjG ≠ lKb := by decide
@[simp] theorem pj_lKb_ne_pjG : lKb ≠ pjG := by decide
@[simp] theorem pj_pjR_ne_pjA : pjR ≠ pjA := by decide
@[simp] theorem pj_pjR_ne_pjTe : pjR ≠ pjTe := by decide
@[simp] theorem pj_pjR_ne_pjHh : pjR ≠ pjHh := by decide
@[simp] theorem pj_pjR_ne_pjT : pjR ≠ pjT := by decide
@[simp] theorem pj_pjR_ne_pjUs : pjR ≠ pjUs := by decide
@[simp] theorem pj_pjR_ne_pjTb : pjR ≠ pjTb := by decide
@[simp] theorem pj_pjR_ne_pjTq : pjR ≠ pjTq := by decide
@[simp] theorem pj_pjR_ne_pjNf : pjR ≠ pjNf := by decide
@[simp] theorem pj_pjR_ne_pjVa : pjR ≠ pjVa := by decide
@[simp] theorem pj_pjR_ne_pjNa : pjR ≠ pjNa := by decide
@[simp] theorem pj_pjR_ne_pjNp : pjR ≠ pjNp := by decide
@[simp] theorem pj_pjR_ne_pjLp : pjR ≠ pjLp := by decide
@[simp] theorem pj_pjR_ne_pjLl : pjR ≠ pjLl := by decide
@[simp] theorem pj_pjR_ne_pjG : pjR ≠ pjG := by decide
@[simp] theorem pj_pjR_ne_kFu : pjR ≠ kFu := by decide
@[simp] theorem pj_kFu_ne_pjR : kFu ≠ pjR := by decide
@[simp] theorem pj_pjR_ne_kD : pjR ≠ kD := by decide
@[simp] theorem pj_kD_ne_pjR : kD ≠ pjR := by decide
@[simp] theorem pj_pjR_ne_ibSn : pjR ≠ ibSn := by decide
@[simp] theorem pj_ibSn_ne_pjR : ibSn ≠ pjR := by decide
@[simp] theorem pj_pjR_ne_ibIx : pjR ≠ ibIx := by decide
@[simp] theorem pj_ibIx_ne_pjR : ibIx ≠ pjR := by decide
@[simp] theorem pj_pjR_ne_ibPe : pjR ≠ ibPe := by decide
@[simp] theorem pj_ibPe_ne_pjR : ibPe ≠ pjR := by decide
@[simp] theorem pj_pjR_ne_lFl : pjR ≠ lFl := by decide
@[simp] theorem pj_lFl_ne_pjR : lFl ≠ pjR := by decide
@[simp] theorem pj_pjR_ne_lDh : pjR ≠ lDh := by decide
@[simp] theorem pj_lDh_ne_pjR : lDh ≠ pjR := by decide
@[simp] theorem pj_pjR_ne_lDt : pjR ≠ lDt := by decide
@[simp] theorem pj_lDt_ne_pjR : lDt ≠ pjR := by decide
@[simp] theorem pj_pjR_ne_lDg : pjR ≠ lDg := by decide
@[simp] theorem pj_lDg_ne_pjR : lDg ≠ pjR := by decide
@[simp] theorem pj_pjR_ne_lDi : pjR ≠ lDi := by decide
@[simp] theorem pj_lDi_ne_pjR : lDi ≠ pjR := by decide
@[simp] theorem pj_pjR_ne_lRp : pjR ≠ lRp := by decide
@[simp] theorem pj_lRp_ne_pjR : lRp ≠ pjR := by decide
@[simp] theorem pj_pjR_ne_lRn : pjR ≠ lRn := by decide
@[simp] theorem pj_lRn_ne_pjR : lRn ≠ pjR := by decide
@[simp] theorem pj_pjR_ne_lDir : pjR ≠ lDir := by decide
@[simp] theorem pj_lDir_ne_pjR : lDir ≠ pjR := by decide
@[simp] theorem pj_pjR_ne_lFle : pjR ≠ lFle := by decide
@[simp] theorem pj_lFle_ne_pjR : lFle ≠ pjR := by decide
@[simp] theorem pj_pjR_ne_lFls : pjR ≠ lFls := by decide
@[simp] theorem pj_lFls_ne_pjR : lFls ≠ pjR := by decide
@[simp] theorem pj_pjR_ne_lKb : pjR ≠ lKb := by decide
@[simp] theorem pj_lKb_ne_pjR : lKb ≠ pjR := by decide

def pjLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, pjA, pjTe, pjHh, pjT, pjUs, pjTb, pjTq, pjNf, pjVa, pjNa, pjNp, pjLp, pjLl, pjG, pjR]

def pjBody (C : Ctx) : ProgHOL 64 := prologue pjLocals
  (.seq (.call (some (some (.local, pjA), none)) fI [(vv kFu), (vv kD), (vv ibPe)]) (.seq (.call (some (some (.local, pjTe), none)) fW [(vv kFu), (vv kD), (vv pjA)]) (.seq (.call (some (some (.local, pjHh), none)) fGetAppFn [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv pjTe)]) (.ite (tagIsE pjHh 3) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pjHh)) (.seq eViewP (.seq (.assign .local pjT (.load .one (vv lRp))) (.seq (.assign .local pjUs (.load .one (.op .add [(vv lRp), (.const 8)]))) (tblFindP C pjTb (vv pjT) (.ite (.cmp .equal (vv pjTb) (.const 0)) hang (.seq (.assign .local pjTq (.op .sub [(vv pjTb), (.const 1)])) (.seq (.assign .local pjNf (.load .one (.op .add [(vv pjTq), (.const 32)]))) (.ite (.cmp .lower (vv ibIx) (vv pjNf)) (.seq (.call (some (some (.local, pjVa), none)) ExG.fGaa [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv pjTe)]) (.ite (.cmp .notEqual (vv pjT) (vv ibSn)) hang (.seq (.assign .local pjNa (.load .one (vv pjVa))) (.seq (.assign .local pjNp (.load .one (.op .add [(vv pjTq), (.const 16)]))) (.ite (.cmp .notEqual (vv pjNa) (vv pjNp)) hang (.seq (.assign .local pjLp (.load .one (.op .add [(vv pjTq), (.const 8)]))) (.seq (.assign .local pjLl (.load .one (vv pjLp))) (.seq (.assign .local lFl (vv lFls)) (.seq (.assign .local lDh (vv pjUs)) (.seq lsViewP (.ite (.cmp .notEqual (vv lRn) (vv pjLl)) hang (.seq (.call (some (some (.local, pjG), none)) fGd [(vv kFu), (vv pjTq), (vv ibIx), (vv pjUs)]) (.seq (.call (some (some (.local, pjR), none)) fTa [(vv pjTq), (vv ibIx), (vv pjUs), (vv pjVa), (vv ibPe)]) (.return (vv pjR))))))))))))))) hang)))))))))) hang))))

section
variable {σ : Type}

theorem pj_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ pjLocals → (ctxEnv C ++ iprParams.zip vals).get x = none :=
  Knot.params_none C pjLocals iprParams vals (by decide) (by decide)

structure PjCodes (C : Ctx) : Prop where
  i : C.code.lookup fI = some (pmap kParams, inferE C fIB, .one)
  w : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one)
  af : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  gaa : C.code.lookup ExG.fGaa = some ([(pFu, .one), (pH, .one)], ExG.gaaBody C, .one)
  mg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  mp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  gd : C.code.lookup fGd = some (gdParams.map (fun p => (p, ShapeHOL.one)), gdBody C, .one)
  ta : C.code.lookup fTa = some (taParams.map (fun p => (p, ShapeHOL.one)), taBody C, .one)

theorem pj_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) (hok : CtxOK C) (hc : PjCodes C)
    (Q : AState → Prop)
    (hI : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → d' < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (inferE C fIB) s1 ((knot mode C n).infer d' e')
      (PostK (ctxH C H)))
    (hW : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → d' < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d' e')
      (PostK (ctxH C H)))
    (hQi : ∀ s1 d' e' a s2, Q s1 → (knot mode C n).infer d' e' s1 = .ok (a, s2) → Q s2)
    (hQw : ∀ s1 d' e' a s2, Q s1 → (knot mode C n).whnf d' e' s1 = .ok (a, s2) → Q s2)
    (hQgaa : ∀ s1 e' a s2, Q s1 → getAppArgs coreWalkFuel e' s1 = .ok (a, s2) → Q s2)
    (hGd : ∀ (H : List (BitVec 64)) s1 (tbl : IProjTable) ot i us, C.H <+: H → Q s1 → TblE C.EB C.EH ot tbl →
      (∃ T, C.fe.findTable? T = some tbl) → i < 2 ^ 63 →
      SpecR (σ := σ) (Pre (ctxH C H) s1 (gdParams.zip [BitVec.ofNat 64 n, ecell C ot, BitVec.ofNat 64 i,
        Enc.idxW us])) (gdBody C) s1 (checkProjGuard (knot mode C n) C.fe (tbl.entry i) us) (PostU (ctxH C H)))
    (hQgd : ∀ s1 (tbl : IProjTable) i us a s2, Q s1 → checkProjGuard (knot mode C n) C.fe (tbl.entry i) us s1 = .ok (a, s2) → Q s2)
    (hTa : ∀ (H : List (BitVec 64)) s1 (tbl : IProjTable) ot i us (targs : List EIdx) oa pe, C.H <+: H → Q s1 →
      TblE C.EB C.EH ot tbl → (∃ T, C.fe.findTable? T = some tbl) → BlkAt H oa (targs.map Enc.idxW) → i < 2 ^ 63 →
      SpecR (σ := σ) (Pre (ctxH C H) s1 (taParams.zip [ecell C ot, BitVec.ofNat 64 i, Enc.idxW us, cellA C oa,
        Enc.idxW pe])) (taBody C) s1 ((tbl.entry i).typeAt us targs pe) (PostK (ctxH C H)))
    (s : AState) (hq : Q s) (d : Nat) (hd : d < 2 ^ 63) (sn : NIdx) (i : Nat) (pe : EIdx) (hi : i < 2 ^ 64) :
    SpecR (σ := σ) (Pre C s (iprParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW sn, BitVec.ofNat 64 i,
      Enc.idxW pe])) (pjBody C) s (inferProj (knot mode C n) C.fe d sn i pe) (PostK C) := by
  refine specR_prologue (postK_locals C) (pj_none C _) ?_
  unfold inferProj
  simp only [bind_assoc]
  refine Big.specR_callKC (C := C) pjA fI kParams [vv kFu, vv kD, vv ibPe] (inferE C fIB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW pe] (by decide) rfl (by decide) hc.i
    ⟨by simp +decide [Env.get, iprParams, ctxEnv], by simp +decide [Env.get, iprParams, ctxEnv], by simp +decide [Env.get, iprParams, ctxEnv], trivial⟩ (hI C.H s d pe (List.prefix_refl _) hd) (fun a s1 H1 hp1 hrun1 => ?_)
  have hq1 := hQi s d pe a s1 hq hrun1
  refine Big.specR_callKC (C := ctxH C H1) pjTe fW kParams [vv kFu, vv kD, vv pjA] (whnfE C fWB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a] (by decide) rfl (by decide) hc.w
    ⟨by simp +decide [Env.get, iprParams, ctxEnv], by simp +decide [Env.get, iprParams, ctxEnv], by simp, trivial⟩ (hW H1 s1 d a hp1 hd) (fun te s2 H2 hp2 hrun2 => ?_)
  have hq2 := hQw s1 d a te s2 hq1 hrun2
  have hp12 : C.H <+: H2 := hp1.trans hp2
  refine specR_callNIM (C := ctxH C H2) pjHh fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv pjTe]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW te] (by decide) rfl (by decide) hc.af
    ⟨rfl, by simp, trivial⟩
    (fun a w s' st => getAppFn coreWalkFuel te s2 = .ok (a, s') ∧ Post (ctxH C H2) s2 a w s' st)
    (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec (ctxH C H2) hc.af coreWalkFuel te s2 CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide),
        hlk 1 (by decide)⟩))
    (fun hh w s' st ⟨hrun3, hw, hs, _⟩ => ?_)
  subst hw
  have hs' : s2 = s' := hs.symm
  subst hs'
  refine Knot.specR_tagIteV pjHh hh 3 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
  swap
  · rw [ite_eq_right (show ¬ (hh.tag == ETag.const) = true by simpa [ETag.const] using htg)]
    exact specR_hangI
  rw [ite_eq_left (show (hh.tag == ETag.const) = true by simp [htg, ETag.const])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv pjHh) (Enc.idxW hh) (by decide) (by simp) ?_
  refine specR_viewP (C := ctxH C H2) hh (by simp) (by simp +decide [Env.get] <;> rfl)
    (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
  refine specR_congr (view_bind_eq hh v _ s2 hv) ?_
  have h3 : v.tagN = 3 := by rw [htn, htg]; rfl
  obtain ⟨T, us, rfl⟩ := UD.tagN_const h3
  dsimp only
  refine specR_loadI' pjT (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW T) (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW T) [Enc.idxW us] []) ?_
  refine specR_loadI' pjUs _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW us) (by decide) (by simp +decide [sev]) rfl
    (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW T) (Enc.idxW us) [] []) ?_
  refine specR_dropM ?_
  refine specR_tblFindI (C := ctxH C H2) (ctxOK_H hok H2) hc.mg hc.mp pjTb (vv pjT) T (by decide) (by simp)
    (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  have hrel := tbl_rel hok T
  revert hrel
  unfold IFEnv.findProj?
  rcases hft : C.fe.findTable? T with _ | tbl
  · intro hrel; simp only at hrel
    rw [show (ctxH C H2).tblM[T]? = none from hrel]
    exact specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI)
      (fun h => absurd h (by decide))
  intro ⟨ot, hm, htb⟩
  rw [show (ctxH C H2).tblM[T]? = some (ecell C ot) from hm]
  refine specR_atEntry fun t ht => ?_
  have hoE : ot < C.EN := Nat.lt_of_lt_of_le (tblE_lt htb) ht.sr.env.1.len
  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI pjTq _ (ecell C ot) (by decide) (by simp [sev, optWG]; exact BitVec.add_sub_cancel _ _) ?_
  obtain ⟨hsn, ⟨wl, hwl, oL, hwL, hblk⟩, ⟨hnp, hnp63⟩, hcto, ⟨hnf, hnf63⟩, _⟩ := id htb
  refine specR_envLoadI (C := ctxH C H2) pjNf (.op .add [vv pjTq, .const 32]) (ot + 4) _ (by decide)
    (by simp +decide [sev, Env.get]; exact UD.ecell_add32 C ot) hnf ?_
  have hlw := word_lt_iff i tbl.numFields (by unfold B; omega) (by unfold B; omega)
  dsimp only
  by_cases hi2 : i < tbl.numFields
  swap
  · simp only [hi2, ↓reduceIte]
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get, iprParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
      (not_congr hlw).mpr hi2]) (fun h => absurd rfl h) (fun _ => specR_hangI)
  simp only [hi2, ↓reduceIte]
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get, iprParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    hlw.mpr hi2]) (fun _ => ?_) (fun h => absurd h (by decide))
  try dsimp only
  refine specR_callNIH (C := ctxH C H2) pjVa ExG.fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv pjTe]
    (ExG.gaaBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW te] (by decide) rfl (by decide) hc.gaa
    ⟨rfl, by simp, trivial⟩
    (fun a w s' st => getAppArgs coreWalkFuel te s2 = .ok (a, s') ∧ PostA (ctxH C H2) a w s' st)
    (fun a w s' H' => getAppArgs coreWalkFuel te s2 = .ok (a, s') ∧ ∃ o3, w = cellA C o3 ∧
      BlkAt H' o3 (a.map Enc.idxW))
    (fun a w s' st ⟨hrun, H3, o3, hp, hw, hb, hsr⟩ => ⟨H3, hp, ⟨hrun, o3, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (ExG.gaa_spec (ctxH C H2) (ctxOK_H hok _) hc.gaa coreWalkFuel CV.coreWalkFuel_lt H2 te s2)))
    (fun targs w s3 H3 hp3 ⟨hrun3, o3, hw, hb3⟩ => ?_)
  subst hw
  have hq3 := hQgaa s2 te targs s3 hq2 hrun3
  have hp13 : C.H <+: H3 := hp12.trans hp3
  by_cases hT : T = sn
  swap
  · have hne : Enc.idxW T ≠ Enc.idxW sn := fun e => hT (Enc.idxW_inj e)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, iprParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_hangI
  subst hT
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, iprParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  refine specR_atEntry fun t3 ht3 => ?_
  have hsm := blk_small0 (C := ctxH C H3) (ctxOK_H hok _) ht3.sr hb3
  simp only [List.length_map] at hsm
  obtain ⟨hlo3, hlv3⟩ := blkAt_get0 hb3
  refine UD.specR_heapLoadI' (C := ctxH C H3) pjNa (vv pjVa) o3 (BitVec.ofNat 64 targs.length)
    (by show H3[o3]? = _; rw [List.getElem?_eq_getElem hlo3, hlv3]; simp) (by decide) (by simp; rfl) ?_
  refine specR_envLoadI (C := ctxH C H3) pjNp (.op .add [vv pjTq, .const 16]) (ot + 2) _ (by decide)
    (by simp +decide [sev, Env.get]; exact UD.ecell_add16 C ot) hnp ?_
  simp only [IProjTable.entry]
  by_cases hna : targs.length = tbl.numParams
  swap
  · have hne : BitVec.ofNat 64 targs.length ≠ BitVec.ofNat 64 tbl.numParams := by
      intro e; have := congrArg BitVec.toNat e; simp at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; exact hna this
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_hangI
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hna])
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only [hna, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  subst hwL
  refine specR_envLoadI (C := ctxH C H3) pjLp (.op .add [vv pjTq, .const 8]) (ot + 1) _ (by decide)
    (by simp +decide [sev, Env.get]; exact ecell_add8 C ot) hwl ?_
  have hl0 : C.EH[oL]? = some (BitVec.ofNat 64 tbl.levelParams.length) := by simpa using hblk.1
  refine specR_envLoadI (C := ctxH C H3) pjLl (vv pjLp) oL _ (by decide) (by simp; rfl) hl0 ?_
  refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [Env.get, iprParams, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv pjUs) (Enc.idxW us) (by decide) (by simp) ?_
  refine specR_lsviewPI us (by simp) (by simp; rfl) (by simp +decide [Env.get, iprParams, ctxEnv] <;> rfl) (by decide)
    (fun vl Pl hvl _ hvll => ?_)
  refine specR_runBind (viewLsLen_run us s3 vl hvl) ?_
  dsimp only
  have hvl' : vl.length < 2 ^ 61 := by simpa using hvll
  have hlp : tbl.levelParams.length < 2 ^ 61 := by
    have h1 := blkAt_len (show BlkAt C.EH oL (tbl.levelParams.map Enc.idxW) from hblk)
    have h2 : C.EH.length ≤ C.EN := ht3.sr.env.1.len
    have h3 := hok.envLay
    simp only [List.length_map] at h1; omega
  by_cases hl : vl.length = tbl.levelParams.length
  swap
  · have hne : BitVec.ofNat 64 (vl.map Enc.idxW).length ≠ BitVec.ofNat 64 tbl.levelParams.length := by
      intro e; have := congrArg BitVec.toNat e; simp at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; exact hl this
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; simpa using hne)
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_hangI
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hl])
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only [hl, ↓reduceIte]
  refine specR_dropM ?_
  refine specR_callNIH (C := ctxH C H3) pjG fGd gdParams [vv kFu, vv pjTq, vv ibIx, vv pjUs] (gdBody C)
    [BitVec.ofNat 64 n, ecell C ot, BitVec.ofNat 64 i, Enc.idxW us] (by decide) rfl (by decide) hc.gd
    ⟨by simp +decide [Env.get, iprParams, ctxEnv], by simp <;> rfl, by simp +decide [Env.get, iprParams, ctxEnv], by simp, trivial⟩
    (fun a w s' st => checkProjGuard (knot mode C n) C.fe (tbl.entry i) us s3 = .ok (a, s') ∧
      PostU (ctxH C H3) a w s' st)
    (fun a w s' _ => checkProjGuard (knot mode C n) C.fe (tbl.entry i) us s3 = .ok (a, s'))
    (fun a w s' st ⟨hrun, H', hp, hsr⟩ => ⟨H', hp, hrun, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu gdParams _ rfl hlk)
      (hGd H3 s3 tbl ot i us hp13 hq3 htb ⟨_, hft⟩ (by omega))))
    (fun g w s4 H4 hp4 hrun4 => ?_)
  have hq4 := hQgd s3 tbl i us g s4 hq3 hrun4
  refine specR_congr (m' := (tbl.entry i).typeAt us targs pe >>= fun r => pure r) (by simp [IProjTable.entry]) ?_
  refine specR_callNIH (C := ctxH C H4) pjR fTa taParams [vv pjTq, vv ibIx, vv pjUs, vv pjVa, vv ibPe] (taBody C)
    [ecell C ot, BitVec.ofNat 64 i, Enc.idxW us, cellA C o3, Enc.idxW pe] (by decide) rfl (by decide) hc.ta
    ⟨by simp <;> rfl, by simp +decide [Env.get, iprParams, ctxEnv], by simp, by simp <;> rfl, by simp +decide [Env.get, iprParams, ctxEnv], trivial⟩
    (PostK (ctxH C H4)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu taParams _ rfl hlk)
      (hTa H4 s4 tbl ot i us targs o3 pe (hp13.trans hp4) hq4 htb ⟨_, hft⟩ (blkAt_mono hb3 hp4) (by omega)))
    (fun r w s5 H5 hp5 hw => ?_)
  subst hw
  exact specR_returnI _ (Enc.idxW r) (by simp)
    (fun t ht => ⟨H5, hp12.trans (hp3.trans (hp4.trans hp5)), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
