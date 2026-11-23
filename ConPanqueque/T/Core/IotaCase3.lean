import ConPanqueque.T.Core.FamilyNZ
import ConPanqueque.T.Core.WcStuck
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `iotaCase3At`: case 3 of the ι split

A K recursor answers `false`. Otherwise the constructor's family stored at `induct` (an `indInfo` record); none
answers `true`. If its level-parameter count equals the comparand list's length, the answer is the negation of
`formerNeverZeroAt` (a callee); otherwise `true`.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def c3K := ofString "c3k"
def c3I := ofString "c3i"
def c3U := ofString "c3u"
def c3W := ofString "c3w"
def c3Q := ofString "c3q"
def c3T := ofString "c3t"
def c3Lp := ofString "c3lp"
def c3Ll := ofString "c3ll"
def c3X := ofString "c3x"
def fC3 := ofString "iotaCase3At"

@[simp] theorem c3_c3K_ne_c3I : c3K ≠ c3I := by decide
@[simp] theorem c3_c3K_ne_c3U : c3K ≠ c3U := by decide
@[simp] theorem c3_c3K_ne_c3W : c3K ≠ c3W := by decide
@[simp] theorem c3_c3K_ne_c3Q : c3K ≠ c3Q := by decide
@[simp] theorem c3_c3K_ne_c3T : c3K ≠ c3T := by decide
@[simp] theorem c3_c3K_ne_c3Lp : c3K ≠ c3Lp := by decide
@[simp] theorem c3_c3K_ne_c3Ll : c3K ≠ c3Ll := by decide
@[simp] theorem c3_c3K_ne_c3X : c3K ≠ c3X := by decide
@[simp] theorem c3_c3K_ne_kFu : c3K ≠ kFu := by decide
@[simp] theorem c3_c3K_ne_kD : c3K ≠ kD := by decide
@[simp] theorem c3_c3K_ne_lFl : c3K ≠ lFl := by decide
@[simp] theorem c3_c3K_ne_lDh : c3K ≠ lDh := by decide
@[simp] theorem c3_c3K_ne_lDt : c3K ≠ lDt := by decide
@[simp] theorem c3_c3K_ne_lDg : c3K ≠ lDg := by decide
@[simp] theorem c3_c3K_ne_lDi : c3K ≠ lDi := by decide
@[simp] theorem c3_c3K_ne_lRp : c3K ≠ lRp := by decide
@[simp] theorem c3_c3K_ne_lRn : c3K ≠ lRn := by decide
@[simp] theorem c3_c3K_ne_lKb : c3K ≠ lKb := by decide
@[simp] theorem c3_c3K_ne_lFls : c3K ≠ lFls := by decide
@[simp] theorem c3_c3K_ne_lDir : c3K ≠ lDir := by decide
@[simp] theorem c3_c3I_ne_c3K : c3I ≠ c3K := by decide
@[simp] theorem c3_c3I_ne_c3U : c3I ≠ c3U := by decide
@[simp] theorem c3_c3I_ne_c3W : c3I ≠ c3W := by decide
@[simp] theorem c3_c3I_ne_c3Q : c3I ≠ c3Q := by decide
@[simp] theorem c3_c3I_ne_c3T : c3I ≠ c3T := by decide
@[simp] theorem c3_c3I_ne_c3Lp : c3I ≠ c3Lp := by decide
@[simp] theorem c3_c3I_ne_c3Ll : c3I ≠ c3Ll := by decide
@[simp] theorem c3_c3I_ne_c3X : c3I ≠ c3X := by decide
@[simp] theorem c3_c3I_ne_kFu : c3I ≠ kFu := by decide
@[simp] theorem c3_c3I_ne_kD : c3I ≠ kD := by decide
@[simp] theorem c3_c3I_ne_lFl : c3I ≠ lFl := by decide
@[simp] theorem c3_c3I_ne_lDh : c3I ≠ lDh := by decide
@[simp] theorem c3_c3I_ne_lDt : c3I ≠ lDt := by decide
@[simp] theorem c3_c3I_ne_lDg : c3I ≠ lDg := by decide
@[simp] theorem c3_c3I_ne_lDi : c3I ≠ lDi := by decide
@[simp] theorem c3_c3I_ne_lRp : c3I ≠ lRp := by decide
@[simp] theorem c3_c3I_ne_lRn : c3I ≠ lRn := by decide
@[simp] theorem c3_c3I_ne_lKb : c3I ≠ lKb := by decide
@[simp] theorem c3_c3I_ne_lFls : c3I ≠ lFls := by decide
@[simp] theorem c3_c3I_ne_lDir : c3I ≠ lDir := by decide
@[simp] theorem c3_c3U_ne_c3K : c3U ≠ c3K := by decide
@[simp] theorem c3_c3U_ne_c3I : c3U ≠ c3I := by decide
@[simp] theorem c3_c3U_ne_c3W : c3U ≠ c3W := by decide
@[simp] theorem c3_c3U_ne_c3Q : c3U ≠ c3Q := by decide
@[simp] theorem c3_c3U_ne_c3T : c3U ≠ c3T := by decide
@[simp] theorem c3_c3U_ne_c3Lp : c3U ≠ c3Lp := by decide
@[simp] theorem c3_c3U_ne_c3Ll : c3U ≠ c3Ll := by decide
@[simp] theorem c3_c3U_ne_c3X : c3U ≠ c3X := by decide
@[simp] theorem c3_c3U_ne_kFu : c3U ≠ kFu := by decide
@[simp] theorem c3_c3U_ne_kD : c3U ≠ kD := by decide
@[simp] theorem c3_c3U_ne_lFl : c3U ≠ lFl := by decide
@[simp] theorem c3_c3U_ne_lDh : c3U ≠ lDh := by decide
@[simp] theorem c3_c3U_ne_lDt : c3U ≠ lDt := by decide
@[simp] theorem c3_c3U_ne_lDg : c3U ≠ lDg := by decide
@[simp] theorem c3_c3U_ne_lDi : c3U ≠ lDi := by decide
@[simp] theorem c3_c3U_ne_lRp : c3U ≠ lRp := by decide
@[simp] theorem c3_c3U_ne_lRn : c3U ≠ lRn := by decide
@[simp] theorem c3_c3U_ne_lKb : c3U ≠ lKb := by decide
@[simp] theorem c3_c3U_ne_lFls : c3U ≠ lFls := by decide
@[simp] theorem c3_c3U_ne_lDir : c3U ≠ lDir := by decide
@[simp] theorem c3_c3W_ne_c3K : c3W ≠ c3K := by decide
@[simp] theorem c3_c3W_ne_c3I : c3W ≠ c3I := by decide
@[simp] theorem c3_c3W_ne_c3U : c3W ≠ c3U := by decide
@[simp] theorem c3_c3W_ne_c3Q : c3W ≠ c3Q := by decide
@[simp] theorem c3_c3W_ne_c3T : c3W ≠ c3T := by decide
@[simp] theorem c3_c3W_ne_c3Lp : c3W ≠ c3Lp := by decide
@[simp] theorem c3_c3W_ne_c3Ll : c3W ≠ c3Ll := by decide
@[simp] theorem c3_c3W_ne_c3X : c3W ≠ c3X := by decide
@[simp] theorem c3_c3W_ne_kFu : c3W ≠ kFu := by decide
@[simp] theorem c3_c3W_ne_kD : c3W ≠ kD := by decide
@[simp] theorem c3_c3W_ne_lFl : c3W ≠ lFl := by decide
@[simp] theorem c3_c3W_ne_lDh : c3W ≠ lDh := by decide
@[simp] theorem c3_c3W_ne_lDt : c3W ≠ lDt := by decide
@[simp] theorem c3_c3W_ne_lDg : c3W ≠ lDg := by decide
@[simp] theorem c3_c3W_ne_lDi : c3W ≠ lDi := by decide
@[simp] theorem c3_c3W_ne_lRp : c3W ≠ lRp := by decide
@[simp] theorem c3_c3W_ne_lRn : c3W ≠ lRn := by decide
@[simp] theorem c3_c3W_ne_lKb : c3W ≠ lKb := by decide
@[simp] theorem c3_c3W_ne_lFls : c3W ≠ lFls := by decide
@[simp] theorem c3_c3W_ne_lDir : c3W ≠ lDir := by decide
@[simp] theorem c3_c3Q_ne_c3K : c3Q ≠ c3K := by decide
@[simp] theorem c3_c3Q_ne_c3I : c3Q ≠ c3I := by decide
@[simp] theorem c3_c3Q_ne_c3U : c3Q ≠ c3U := by decide
@[simp] theorem c3_c3Q_ne_c3W : c3Q ≠ c3W := by decide
@[simp] theorem c3_c3Q_ne_c3T : c3Q ≠ c3T := by decide
@[simp] theorem c3_c3Q_ne_c3Lp : c3Q ≠ c3Lp := by decide
@[simp] theorem c3_c3Q_ne_c3Ll : c3Q ≠ c3Ll := by decide
@[simp] theorem c3_c3Q_ne_c3X : c3Q ≠ c3X := by decide
@[simp] theorem c3_c3Q_ne_kFu : c3Q ≠ kFu := by decide
@[simp] theorem c3_c3Q_ne_kD : c3Q ≠ kD := by decide
@[simp] theorem c3_c3Q_ne_lFl : c3Q ≠ lFl := by decide
@[simp] theorem c3_c3Q_ne_lDh : c3Q ≠ lDh := by decide
@[simp] theorem c3_c3Q_ne_lDt : c3Q ≠ lDt := by decide
@[simp] theorem c3_c3Q_ne_lDg : c3Q ≠ lDg := by decide
@[simp] theorem c3_c3Q_ne_lDi : c3Q ≠ lDi := by decide
@[simp] theorem c3_c3Q_ne_lRp : c3Q ≠ lRp := by decide
@[simp] theorem c3_c3Q_ne_lRn : c3Q ≠ lRn := by decide
@[simp] theorem c3_c3Q_ne_lKb : c3Q ≠ lKb := by decide
@[simp] theorem c3_c3Q_ne_lFls : c3Q ≠ lFls := by decide
@[simp] theorem c3_c3Q_ne_lDir : c3Q ≠ lDir := by decide
@[simp] theorem c3_c3T_ne_c3K : c3T ≠ c3K := by decide
@[simp] theorem c3_c3T_ne_c3I : c3T ≠ c3I := by decide
@[simp] theorem c3_c3T_ne_c3U : c3T ≠ c3U := by decide
@[simp] theorem c3_c3T_ne_c3W : c3T ≠ c3W := by decide
@[simp] theorem c3_c3T_ne_c3Q : c3T ≠ c3Q := by decide
@[simp] theorem c3_c3T_ne_c3Lp : c3T ≠ c3Lp := by decide
@[simp] theorem c3_c3T_ne_c3Ll : c3T ≠ c3Ll := by decide
@[simp] theorem c3_c3T_ne_c3X : c3T ≠ c3X := by decide
@[simp] theorem c3_c3T_ne_kFu : c3T ≠ kFu := by decide
@[simp] theorem c3_c3T_ne_kD : c3T ≠ kD := by decide
@[simp] theorem c3_c3T_ne_lFl : c3T ≠ lFl := by decide
@[simp] theorem c3_c3T_ne_lDh : c3T ≠ lDh := by decide
@[simp] theorem c3_c3T_ne_lDt : c3T ≠ lDt := by decide
@[simp] theorem c3_c3T_ne_lDg : c3T ≠ lDg := by decide
@[simp] theorem c3_c3T_ne_lDi : c3T ≠ lDi := by decide
@[simp] theorem c3_c3T_ne_lRp : c3T ≠ lRp := by decide
@[simp] theorem c3_c3T_ne_lRn : c3T ≠ lRn := by decide
@[simp] theorem c3_c3T_ne_lKb : c3T ≠ lKb := by decide
@[simp] theorem c3_c3T_ne_lFls : c3T ≠ lFls := by decide
@[simp] theorem c3_c3T_ne_lDir : c3T ≠ lDir := by decide
@[simp] theorem c3_c3Lp_ne_c3K : c3Lp ≠ c3K := by decide
@[simp] theorem c3_c3Lp_ne_c3I : c3Lp ≠ c3I := by decide
@[simp] theorem c3_c3Lp_ne_c3U : c3Lp ≠ c3U := by decide
@[simp] theorem c3_c3Lp_ne_c3W : c3Lp ≠ c3W := by decide
@[simp] theorem c3_c3Lp_ne_c3Q : c3Lp ≠ c3Q := by decide
@[simp] theorem c3_c3Lp_ne_c3T : c3Lp ≠ c3T := by decide
@[simp] theorem c3_c3Lp_ne_c3Ll : c3Lp ≠ c3Ll := by decide
@[simp] theorem c3_c3Lp_ne_c3X : c3Lp ≠ c3X := by decide
@[simp] theorem c3_c3Lp_ne_kFu : c3Lp ≠ kFu := by decide
@[simp] theorem c3_c3Lp_ne_kD : c3Lp ≠ kD := by decide
@[simp] theorem c3_c3Lp_ne_lFl : c3Lp ≠ lFl := by decide
@[simp] theorem c3_c3Lp_ne_lDh : c3Lp ≠ lDh := by decide
@[simp] theorem c3_c3Lp_ne_lDt : c3Lp ≠ lDt := by decide
@[simp] theorem c3_c3Lp_ne_lDg : c3Lp ≠ lDg := by decide
@[simp] theorem c3_c3Lp_ne_lDi : c3Lp ≠ lDi := by decide
@[simp] theorem c3_c3Lp_ne_lRp : c3Lp ≠ lRp := by decide
@[simp] theorem c3_c3Lp_ne_lRn : c3Lp ≠ lRn := by decide
@[simp] theorem c3_c3Lp_ne_lKb : c3Lp ≠ lKb := by decide
@[simp] theorem c3_c3Lp_ne_lFls : c3Lp ≠ lFls := by decide
@[simp] theorem c3_c3Lp_ne_lDir : c3Lp ≠ lDir := by decide
@[simp] theorem c3_c3Ll_ne_c3K : c3Ll ≠ c3K := by decide
@[simp] theorem c3_c3Ll_ne_c3I : c3Ll ≠ c3I := by decide
@[simp] theorem c3_c3Ll_ne_c3U : c3Ll ≠ c3U := by decide
@[simp] theorem c3_c3Ll_ne_c3W : c3Ll ≠ c3W := by decide
@[simp] theorem c3_c3Ll_ne_c3Q : c3Ll ≠ c3Q := by decide
@[simp] theorem c3_c3Ll_ne_c3T : c3Ll ≠ c3T := by decide
@[simp] theorem c3_c3Ll_ne_c3Lp : c3Ll ≠ c3Lp := by decide
@[simp] theorem c3_c3Ll_ne_c3X : c3Ll ≠ c3X := by decide
@[simp] theorem c3_c3Ll_ne_kFu : c3Ll ≠ kFu := by decide
@[simp] theorem c3_c3Ll_ne_kD : c3Ll ≠ kD := by decide
@[simp] theorem c3_c3Ll_ne_lFl : c3Ll ≠ lFl := by decide
@[simp] theorem c3_c3Ll_ne_lDh : c3Ll ≠ lDh := by decide
@[simp] theorem c3_c3Ll_ne_lDt : c3Ll ≠ lDt := by decide
@[simp] theorem c3_c3Ll_ne_lDg : c3Ll ≠ lDg := by decide
@[simp] theorem c3_c3Ll_ne_lDi : c3Ll ≠ lDi := by decide
@[simp] theorem c3_c3Ll_ne_lRp : c3Ll ≠ lRp := by decide
@[simp] theorem c3_c3Ll_ne_lRn : c3Ll ≠ lRn := by decide
@[simp] theorem c3_c3Ll_ne_lKb : c3Ll ≠ lKb := by decide
@[simp] theorem c3_c3Ll_ne_lFls : c3Ll ≠ lFls := by decide
@[simp] theorem c3_c3Ll_ne_lDir : c3Ll ≠ lDir := by decide
@[simp] theorem c3_c3X_ne_c3K : c3X ≠ c3K := by decide
@[simp] theorem c3_c3X_ne_c3I : c3X ≠ c3I := by decide
@[simp] theorem c3_c3X_ne_c3U : c3X ≠ c3U := by decide
@[simp] theorem c3_c3X_ne_c3W : c3X ≠ c3W := by decide
@[simp] theorem c3_c3X_ne_c3Q : c3X ≠ c3Q := by decide
@[simp] theorem c3_c3X_ne_c3T : c3X ≠ c3T := by decide
@[simp] theorem c3_c3X_ne_c3Lp : c3X ≠ c3Lp := by decide
@[simp] theorem c3_c3X_ne_c3Ll : c3X ≠ c3Ll := by decide
@[simp] theorem c3_c3X_ne_kFu : c3X ≠ kFu := by decide
@[simp] theorem c3_c3X_ne_kD : c3X ≠ kD := by decide
@[simp] theorem c3_c3X_ne_lFl : c3X ≠ lFl := by decide
@[simp] theorem c3_c3X_ne_lDh : c3X ≠ lDh := by decide
@[simp] theorem c3_c3X_ne_lDt : c3X ≠ lDt := by decide
@[simp] theorem c3_c3X_ne_lDg : c3X ≠ lDg := by decide
@[simp] theorem c3_c3X_ne_lDi : c3X ≠ lDi := by decide
@[simp] theorem c3_c3X_ne_lRp : c3X ≠ lRp := by decide
@[simp] theorem c3_c3X_ne_lRn : c3X ≠ lRn := by decide
@[simp] theorem c3_c3X_ne_lKb : c3X ≠ lKb := by decide
@[simp] theorem c3_c3X_ne_lFls : c3X ≠ lFls := by decide
@[simp] theorem c3_c3X_ne_lDir : c3X ≠ lDir := by decide
@[simp] theorem c3_kFu_ne_c3K : kFu ≠ c3K := by decide
@[simp] theorem c3_kFu_ne_c3I : kFu ≠ c3I := by decide
@[simp] theorem c3_kFu_ne_c3U : kFu ≠ c3U := by decide
@[simp] theorem c3_kFu_ne_c3W : kFu ≠ c3W := by decide
@[simp] theorem c3_kFu_ne_c3Q : kFu ≠ c3Q := by decide
@[simp] theorem c3_kFu_ne_c3T : kFu ≠ c3T := by decide
@[simp] theorem c3_kFu_ne_c3Lp : kFu ≠ c3Lp := by decide
@[simp] theorem c3_kFu_ne_c3Ll : kFu ≠ c3Ll := by decide
@[simp] theorem c3_kFu_ne_c3X : kFu ≠ c3X := by decide
@[simp] theorem c3_kD_ne_c3K : kD ≠ c3K := by decide
@[simp] theorem c3_kD_ne_c3I : kD ≠ c3I := by decide
@[simp] theorem c3_kD_ne_c3U : kD ≠ c3U := by decide
@[simp] theorem c3_kD_ne_c3W : kD ≠ c3W := by decide
@[simp] theorem c3_kD_ne_c3Q : kD ≠ c3Q := by decide
@[simp] theorem c3_kD_ne_c3T : kD ≠ c3T := by decide
@[simp] theorem c3_kD_ne_c3Lp : kD ≠ c3Lp := by decide
@[simp] theorem c3_kD_ne_c3Ll : kD ≠ c3Ll := by decide
@[simp] theorem c3_kD_ne_c3X : kD ≠ c3X := by decide
@[simp] theorem c3_lFl_ne_c3K : lFl ≠ c3K := by decide
@[simp] theorem c3_lFl_ne_c3I : lFl ≠ c3I := by decide
@[simp] theorem c3_lFl_ne_c3U : lFl ≠ c3U := by decide
@[simp] theorem c3_lFl_ne_c3W : lFl ≠ c3W := by decide
@[simp] theorem c3_lFl_ne_c3Q : lFl ≠ c3Q := by decide
@[simp] theorem c3_lFl_ne_c3T : lFl ≠ c3T := by decide
@[simp] theorem c3_lFl_ne_c3Lp : lFl ≠ c3Lp := by decide
@[simp] theorem c3_lFl_ne_c3Ll : lFl ≠ c3Ll := by decide
@[simp] theorem c3_lFl_ne_c3X : lFl ≠ c3X := by decide
@[simp] theorem c3_lDh_ne_c3K : lDh ≠ c3K := by decide
@[simp] theorem c3_lDh_ne_c3I : lDh ≠ c3I := by decide
@[simp] theorem c3_lDh_ne_c3U : lDh ≠ c3U := by decide
@[simp] theorem c3_lDh_ne_c3W : lDh ≠ c3W := by decide
@[simp] theorem c3_lDh_ne_c3Q : lDh ≠ c3Q := by decide
@[simp] theorem c3_lDh_ne_c3T : lDh ≠ c3T := by decide
@[simp] theorem c3_lDh_ne_c3Lp : lDh ≠ c3Lp := by decide
@[simp] theorem c3_lDh_ne_c3Ll : lDh ≠ c3Ll := by decide
@[simp] theorem c3_lDh_ne_c3X : lDh ≠ c3X := by decide
@[simp] theorem c3_lDt_ne_c3K : lDt ≠ c3K := by decide
@[simp] theorem c3_lDt_ne_c3I : lDt ≠ c3I := by decide
@[simp] theorem c3_lDt_ne_c3U : lDt ≠ c3U := by decide
@[simp] theorem c3_lDt_ne_c3W : lDt ≠ c3W := by decide
@[simp] theorem c3_lDt_ne_c3Q : lDt ≠ c3Q := by decide
@[simp] theorem c3_lDt_ne_c3T : lDt ≠ c3T := by decide
@[simp] theorem c3_lDt_ne_c3Lp : lDt ≠ c3Lp := by decide
@[simp] theorem c3_lDt_ne_c3Ll : lDt ≠ c3Ll := by decide
@[simp] theorem c3_lDt_ne_c3X : lDt ≠ c3X := by decide
@[simp] theorem c3_lDg_ne_c3K : lDg ≠ c3K := by decide
@[simp] theorem c3_lDg_ne_c3I : lDg ≠ c3I := by decide
@[simp] theorem c3_lDg_ne_c3U : lDg ≠ c3U := by decide
@[simp] theorem c3_lDg_ne_c3W : lDg ≠ c3W := by decide
@[simp] theorem c3_lDg_ne_c3Q : lDg ≠ c3Q := by decide
@[simp] theorem c3_lDg_ne_c3T : lDg ≠ c3T := by decide
@[simp] theorem c3_lDg_ne_c3Lp : lDg ≠ c3Lp := by decide
@[simp] theorem c3_lDg_ne_c3Ll : lDg ≠ c3Ll := by decide
@[simp] theorem c3_lDg_ne_c3X : lDg ≠ c3X := by decide
@[simp] theorem c3_lDi_ne_c3K : lDi ≠ c3K := by decide
@[simp] theorem c3_lDi_ne_c3I : lDi ≠ c3I := by decide
@[simp] theorem c3_lDi_ne_c3U : lDi ≠ c3U := by decide
@[simp] theorem c3_lDi_ne_c3W : lDi ≠ c3W := by decide
@[simp] theorem c3_lDi_ne_c3Q : lDi ≠ c3Q := by decide
@[simp] theorem c3_lDi_ne_c3T : lDi ≠ c3T := by decide
@[simp] theorem c3_lDi_ne_c3Lp : lDi ≠ c3Lp := by decide
@[simp] theorem c3_lDi_ne_c3Ll : lDi ≠ c3Ll := by decide
@[simp] theorem c3_lDi_ne_c3X : lDi ≠ c3X := by decide
@[simp] theorem c3_lRp_ne_c3K : lRp ≠ c3K := by decide
@[simp] theorem c3_lRp_ne_c3I : lRp ≠ c3I := by decide
@[simp] theorem c3_lRp_ne_c3U : lRp ≠ c3U := by decide
@[simp] theorem c3_lRp_ne_c3W : lRp ≠ c3W := by decide
@[simp] theorem c3_lRp_ne_c3Q : lRp ≠ c3Q := by decide
@[simp] theorem c3_lRp_ne_c3T : lRp ≠ c3T := by decide
@[simp] theorem c3_lRp_ne_c3Lp : lRp ≠ c3Lp := by decide
@[simp] theorem c3_lRp_ne_c3Ll : lRp ≠ c3Ll := by decide
@[simp] theorem c3_lRp_ne_c3X : lRp ≠ c3X := by decide
@[simp] theorem c3_lRn_ne_c3K : lRn ≠ c3K := by decide
@[simp] theorem c3_lRn_ne_c3I : lRn ≠ c3I := by decide
@[simp] theorem c3_lRn_ne_c3U : lRn ≠ c3U := by decide
@[simp] theorem c3_lRn_ne_c3W : lRn ≠ c3W := by decide
@[simp] theorem c3_lRn_ne_c3Q : lRn ≠ c3Q := by decide
@[simp] theorem c3_lRn_ne_c3T : lRn ≠ c3T := by decide
@[simp] theorem c3_lRn_ne_c3Lp : lRn ≠ c3Lp := by decide
@[simp] theorem c3_lRn_ne_c3Ll : lRn ≠ c3Ll := by decide
@[simp] theorem c3_lRn_ne_c3X : lRn ≠ c3X := by decide
@[simp] theorem c3_lKb_ne_c3K : lKb ≠ c3K := by decide
@[simp] theorem c3_lKb_ne_c3I : lKb ≠ c3I := by decide
@[simp] theorem c3_lKb_ne_c3U : lKb ≠ c3U := by decide
@[simp] theorem c3_lKb_ne_c3W : lKb ≠ c3W := by decide
@[simp] theorem c3_lKb_ne_c3Q : lKb ≠ c3Q := by decide
@[simp] theorem c3_lKb_ne_c3T : lKb ≠ c3T := by decide
@[simp] theorem c3_lKb_ne_c3Lp : lKb ≠ c3Lp := by decide
@[simp] theorem c3_lKb_ne_c3Ll : lKb ≠ c3Ll := by decide
@[simp] theorem c3_lKb_ne_c3X : lKb ≠ c3X := by decide
@[simp] theorem c3_lFls_ne_c3K : lFls ≠ c3K := by decide
@[simp] theorem c3_lFls_ne_c3I : lFls ≠ c3I := by decide
@[simp] theorem c3_lFls_ne_c3U : lFls ≠ c3U := by decide
@[simp] theorem c3_lFls_ne_c3W : lFls ≠ c3W := by decide
@[simp] theorem c3_lFls_ne_c3Q : lFls ≠ c3Q := by decide
@[simp] theorem c3_lFls_ne_c3T : lFls ≠ c3T := by decide
@[simp] theorem c3_lFls_ne_c3Lp : lFls ≠ c3Lp := by decide
@[simp] theorem c3_lFls_ne_c3Ll : lFls ≠ c3Ll := by decide
@[simp] theorem c3_lFls_ne_c3X : lFls ≠ c3X := by decide
@[simp] theorem c3_lDir_ne_c3K : lDir ≠ c3K := by decide
@[simp] theorem c3_lDir_ne_c3I : lDir ≠ c3I := by decide
@[simp] theorem c3_lDir_ne_c3U : lDir ≠ c3U := by decide
@[simp] theorem c3_lDir_ne_c3W : lDir ≠ c3W := by decide
@[simp] theorem c3_lDir_ne_c3Q : lDir ≠ c3Q := by decide
@[simp] theorem c3_lDir_ne_c3T : lDir ≠ c3T := by decide
@[simp] theorem c3_lDir_ne_c3Lp : lDir ≠ c3Lp := by decide
@[simp] theorem c3_lDir_ne_c3Ll : lDir ≠ c3Ll := by decide
@[simp] theorem c3_lDir_ne_c3X : lDir ≠ c3X := by decide

def c3Params : List MlS := [kFu, kD, c3K, c3I, c3U]
def c3Locals : List MlS := [c3W, c3Q, c3T, c3Lp, c3Ll, lFl, lDh, lDt, lDg, lDi, lRp, lRn, c3X]

def c3Core (C : Ctx) : ProgHOL 64 :=
  .ite (vv c3K) (.return (.const 0))
  (envFindP C c3W (vv c3I)
  (.ite (.cmp .equal (vv c3W) (.const 0)) (.return (.const 1))
  (.seq (.assign .local c3Q (.op .sub [vv c3W, .const 1])) (.seq (.assign .local c3T (.load .one (vv c3Q)))
  (.ite (.cmp .notEqual (vv c3T) (.const 3)) (.return (.const 1))
  (.seq (.assign .local c3Lp (.load .one (.op .add [vv c3Q, .const 16])))
  (.seq (.assign .local c3Ll (.load .one (vv c3Lp)))
  (.seq (.assign .local lFl (vv lFls)) (.seq (.assign .local lDh (vv c3U)) (.seq lsViewP
  (.ite (.cmp .notEqual (vv lRn) (vv c3Ll)) (.return (.const 1))
  (.seq (.call (some (some (.local, c3X), none)) fFza [vv kFu, vv kD, vv c3Q, vv c3U])
    (.return (.cmp .equal (vv c3X) (.const 0)))))))))))))))

def c3Body (C : Ctx) : ProgHOL 64 := prologue c3Locals (c3Core C)

structure C3Codes (C : Ctx) : Prop where
  mg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  mp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  fza : C.code.lookup fFza = some (fzParams.map (fun p => (p, ShapeHOL.one)), fzaBody C, .one)

section
variable {σ : Type}

theorem c3_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ c3Locals → (ctxEnv C ++ c3Params.zip vals).get x = none :=
  Knot.params_none C c3Locals c3Params vals (by decide) (by decide)

theorem c3_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) (hok : CtxOK C) (hc : C3Codes C) (s : AState)
    (d : Nat) (isK : Bool) (induct : NIdx) (us : LsIdx)
    (hFza : ∀ cvT caps o, C.fe.find? induct = some (.indInfo cvT caps) → CIE C.EB C.EH o (.indInfo cvT caps) →
      ∀ H, C.H <+: H → SpecR (σ := σ) (Pre (ctxH C H) s (fzParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, ecell C o,
        Enc.idxW us])) (fzaBody C) s (formerNeverZeroAt (knot mode C n) cvT caps us) (PostB (ctxH C H)))
    (H : List (BitVec 64)) (hp : C.H <+: H) :
    SpecR (σ := σ) (Pre (ctxH C H) s (c3Params.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, boolW isK, Enc.idxW induct,
      Enc.idxW us])) (c3Body C) s (iotaCase3At (knot mode C n) C.fe isK induct us) (PostB (ctxH C H)) := by
  have hok1 := ctxOK_H hok H
  refine specR_prologue (postB_locals _) (c3_none _ _) ?_
  unfold c3Core iotaCase3At
  cases isK
  · refine specR_ifI _ (boolW false) (by simp +decide [sev, Env.get, c3Params, ctxEnv])
      (fun h => absurd h (by decide)) (fun _ => ?_)
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine specR_envFindI (C := ctxH C H) hok1 hc.mg hc.mp c3W (vv c3I) induct (by decide)
      (by simp +decide [Env.get, c3Params, ctxEnv]) (by simp +decide [Env.get, c3Params, ctxEnv] <;> rfl) ?_
    have hrel : (match C.fe.find? induct with
        | none => (ctxH C H).envM[induct]? = none
        | some ci => ∃ o, (ctxH C H).envM[induct]? = some (ecell (ctxH C H) o) ∧
            CIE (ctxH C H).EB (ctxH C H).EH o ci) := find_rel hok1 induct
    revert hrel
    unfold ctorFamily
    rcases hfind : C.fe.find? induct with _ | ci
    · intro hrel; simp only at hrel
      rw [hrel]
      refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    intro ⟨o, hm, hci⟩
    rw [hm]
    refine specR_atEntry fun t ht => ?_
    have hoE : o < (ctxH C H).EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
    refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok1 hoE)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI c3Q _ (ecell C o) (by decide) (by simp [sev, optWG]; exact ecell_succ_sub C o) ?_
    refine specR_envLoadI c3T (vv c3Q) o _ (by decide) (by simp; rfl) (UD.cie_tag hci) ?_
    cases ci
    case indInfo cvT caps =>
      dsimp only
      refine specR_ifI _ 0 (by simp +decide [sev, UD.ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      have hci' := hci
      obtain ⟨⟨_, ⟨w, hw, o', hw', hblk⟩, _⟩, _⟩ := hci
      subst hw'
      refine specR_envLoadI c3Lp (.op .add [vv c3Q, .const 16]) (o + 2) _ (by decide)
        (by simp [sev, vv]; exact UD.ecell_add16 C o) (by simpa using hw) ?_
      have hl0 : (ctxH C H).EH[o']? = some (BitVec.ofNat 64 cvT.levelParams.length) := by
        have := hblk.1; simpa [IConstantInfo.toConstantVal] using this
      refine specR_envLoadI c3Ll (vv c3Lp) o' _ (by decide) (by simp; rfl) hl0 ?_
      refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [Env.get, c3Params, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv c3U) (Enc.idxW us) (by decide) (by simp +decide [Env.get, c3Params, ctxEnv]) ?_
      refine specR_lsviewPI (C := ctxH C H) us (by simp) (by simp +decide [Env.get] <;> rfl)
        (by simp +decide [Env.get, c3Params, ctxEnv] <;> rfl) (by decide) (fun vl Pl hvl _ hvll => ?_)
      refine specR_runBind (viewLsLen_run us s vl hvl) ?_
      dsimp only
      have hvl' : vl.length < 2 ^ 61 := by simpa using hvll
      have hlp : cvT.levelParams.length < 2 ^ 61 := by
        have h1 := blkAt_len (show BlkAt (ctxH C H).EH o' (cvT.levelParams.map Enc.idxW) from hblk)
        have h2 := ht.sr.env.1.len; have h3 := hok1.envLay
        simp only [List.length_map, ctxH] at h1 h2 h3; omega
      by_cases hl : vl.length = cvT.levelParams.length
      · rw [if_pos (by simpa using hl.symm)]
        refine specR_ifI _ 0 (by simp [sev, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
          (fun _ => ?_)
        refine specR_callNIH (C := ctxH C H) c3X fFza fzParams [vv kFu, vv kD, vv c3Q, vv c3U] (fzaBody C)
          [BitVec.ofNat 64 n, BitVec.ofNat 64 d, ecell C o, Enc.idxW us] (by decide) rfl (by decide) hc.fza
          ⟨by simp +decide [Env.get, c3Params, ctxEnv], by simp +decide [Env.get, c3Params, ctxEnv], by simp,
            by simp +decide [Env.get, c3Params, ctxEnv], trivial⟩
          (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
          (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fzParams _ rfl hlk)
            (hFza cvT caps o hfind hci' H hp))
          (fun b w s1 H1 hp1 hw => ?_)
        subst hw
        exact specR_returnI _ (boolW !b) (by cases b <;> simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      · rw [if_neg (by simpa using fun e => hl e.symm)]
        have hne : BitVec.ofNat 64 vl.length ≠ BitVec.ofNat 64 cvT.levelParams.length := fun x =>
          hl ((UD.ofNat_eq_iff_small _ _ (by omega) (by omega)).mp x)
        refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun _ => ?_)
          (fun h => absurd h (by decide))
        exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    all_goals
      dsimp only
      refine specR_ifI _ 1 (by simp +decide [sev, UD.ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_ifI _ (boolW true) (by simp +decide [sev, Env.get, c3Params, ctxEnv]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
