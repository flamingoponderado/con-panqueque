import ConPanqueque.T.Core.TypeSortPW
import ConPanqueque.T.Core.DefeqProj
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# PropRead's `headProofPW`

The datum of a term's head: a constant answers from its stored type (at the use's levels), an fvar from its declared
type; sorts, ∀s and literals are never proofs; a projection answers `never` off its field's stored type, or nothing.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc
open ConLeche (Level Name)

def hqF := ofString "phq_hqf"
def hqH := ofString "phq_hqh"
def hqN := ofString "phq_hqn"
def hqU := ofString "phq_hqu"
def hqP := ofString "phq_hqp"
def hqQ := ofString "phq_hqq"
def hqLp := ofString "phq_hqlp"
def hqLl := ofString "phq_hqll"
def hqT := ofString "phq_hqt"
def hqW := ofString "phq_hqw"
def hqS := ofString "phq_hqs"
def hqN2 := ofString "phq_hqn2"
def hqP2 := ofString "phq_hqp2"
def hqI2 := ofString "phq_hqi2"
def hqTb := ofString "phq_hqtb"
def hqTq := ofString "phq_hqtq"
def hqNf := ofString "phq_hqnf"
def hqBp := ofString "phq_hqbp"
def hqBd := ofString "phq_hqbd"
def fHq := ofString "headProofPW"

@[simp] theorem phq_hqF_ne_hqH : hqF ≠ hqH := by decide
@[simp] theorem phq_hqF_ne_hqN : hqF ≠ hqN := by decide
@[simp] theorem phq_hqF_ne_hqU : hqF ≠ hqU := by decide
@[simp] theorem phq_hqF_ne_hqP : hqF ≠ hqP := by decide
@[simp] theorem phq_hqF_ne_hqQ : hqF ≠ hqQ := by decide
@[simp] theorem phq_hqF_ne_hqLp : hqF ≠ hqLp := by decide
@[simp] theorem phq_hqF_ne_hqLl : hqF ≠ hqLl := by decide
@[simp] theorem phq_hqF_ne_hqT : hqF ≠ hqT := by decide
@[simp] theorem phq_hqF_ne_hqW : hqF ≠ hqW := by decide
@[simp] theorem phq_hqF_ne_hqS : hqF ≠ hqS := by decide
@[simp] theorem phq_hqF_ne_hqN2 : hqF ≠ hqN2 := by decide
@[simp] theorem phq_hqF_ne_hqP2 : hqF ≠ hqP2 := by decide
@[simp] theorem phq_hqF_ne_hqI2 : hqF ≠ hqI2 := by decide
@[simp] theorem phq_hqF_ne_hqTb : hqF ≠ hqTb := by decide
@[simp] theorem phq_hqF_ne_hqTq : hqF ≠ hqTq := by decide
@[simp] theorem phq_hqF_ne_hqNf : hqF ≠ hqNf := by decide
@[simp] theorem phq_hqF_ne_hqBp : hqF ≠ hqBp := by decide
@[simp] theorem phq_hqF_ne_hqBd : hqF ≠ hqBd := by decide
@[simp] theorem phq_hqF_ne_lFl : hqF ≠ lFl := by decide
@[simp] theorem phq_lFl_ne_hqF : lFl ≠ hqF := by decide
@[simp] theorem phq_hqF_ne_lDh : hqF ≠ lDh := by decide
@[simp] theorem phq_lDh_ne_hqF : lDh ≠ hqF := by decide
@[simp] theorem phq_hqF_ne_lDt : hqF ≠ lDt := by decide
@[simp] theorem phq_lDt_ne_hqF : lDt ≠ hqF := by decide
@[simp] theorem phq_hqF_ne_lDg : hqF ≠ lDg := by decide
@[simp] theorem phq_lDg_ne_hqF : lDg ≠ hqF := by decide
@[simp] theorem phq_hqF_ne_lDi : hqF ≠ lDi := by decide
@[simp] theorem phq_lDi_ne_hqF : lDi ≠ hqF := by decide
@[simp] theorem phq_hqF_ne_lRp : hqF ≠ lRp := by decide
@[simp] theorem phq_lRp_ne_hqF : lRp ≠ hqF := by decide
@[simp] theorem phq_hqF_ne_lRn : hqF ≠ lRn := by decide
@[simp] theorem phq_lRn_ne_hqF : lRn ≠ hqF := by decide
@[simp] theorem phq_hqF_ne_lFle : hqF ≠ lFle := by decide
@[simp] theorem phq_lFle_ne_hqF : lFle ≠ hqF := by decide
@[simp] theorem phq_hqF_ne_lKb : hqF ≠ lKb := by decide
@[simp] theorem phq_lKb_ne_hqF : lKb ≠ hqF := by decide
@[simp] theorem phq_hqF_ne_lDir : hqF ≠ lDir := by decide
@[simp] theorem phq_lDir_ne_hqF : lDir ≠ hqF := by decide
@[simp] theorem phq_hqF_ne_lFln : hqF ≠ lFln := by decide
@[simp] theorem phq_lFln_ne_hqF : lFln ≠ hqF := by decide
@[simp] theorem phq_hqF_ne_lFll : hqF ≠ lFll := by decide
@[simp] theorem phq_lFll_ne_hqF : lFll ≠ hqF := by decide
@[simp] theorem phq_hqF_ne_lFls : hqF ≠ lFls := by decide
@[simp] theorem phq_lFls_ne_hqF : lFls ≠ hqF := by decide
@[simp] theorem phq_hqF_ne_kFu : hqF ≠ kFu := by decide
@[simp] theorem phq_kFu_ne_hqF : kFu ≠ hqF := by decide
@[simp] theorem phq_hqF_ne_kD : hqF ≠ kD := by decide
@[simp] theorem phq_kD_ne_hqF : kD ≠ hqF := by decide
@[simp] theorem phq_hqH_ne_hqF : hqH ≠ hqF := by decide
@[simp] theorem phq_hqH_ne_hqN : hqH ≠ hqN := by decide
@[simp] theorem phq_hqH_ne_hqU : hqH ≠ hqU := by decide
@[simp] theorem phq_hqH_ne_hqP : hqH ≠ hqP := by decide
@[simp] theorem phq_hqH_ne_hqQ : hqH ≠ hqQ := by decide
@[simp] theorem phq_hqH_ne_hqLp : hqH ≠ hqLp := by decide
@[simp] theorem phq_hqH_ne_hqLl : hqH ≠ hqLl := by decide
@[simp] theorem phq_hqH_ne_hqT : hqH ≠ hqT := by decide
@[simp] theorem phq_hqH_ne_hqW : hqH ≠ hqW := by decide
@[simp] theorem phq_hqH_ne_hqS : hqH ≠ hqS := by decide
@[simp] theorem phq_hqH_ne_hqN2 : hqH ≠ hqN2 := by decide
@[simp] theorem phq_hqH_ne_hqP2 : hqH ≠ hqP2 := by decide
@[simp] theorem phq_hqH_ne_hqI2 : hqH ≠ hqI2 := by decide
@[simp] theorem phq_hqH_ne_hqTb : hqH ≠ hqTb := by decide
@[simp] theorem phq_hqH_ne_hqTq : hqH ≠ hqTq := by decide
@[simp] theorem phq_hqH_ne_hqNf : hqH ≠ hqNf := by decide
@[simp] theorem phq_hqH_ne_hqBp : hqH ≠ hqBp := by decide
@[simp] theorem phq_hqH_ne_hqBd : hqH ≠ hqBd := by decide
@[simp] theorem phq_hqH_ne_lFl : hqH ≠ lFl := by decide
@[simp] theorem phq_lFl_ne_hqH : lFl ≠ hqH := by decide
@[simp] theorem phq_hqH_ne_lDh : hqH ≠ lDh := by decide
@[simp] theorem phq_lDh_ne_hqH : lDh ≠ hqH := by decide
@[simp] theorem phq_hqH_ne_lDt : hqH ≠ lDt := by decide
@[simp] theorem phq_lDt_ne_hqH : lDt ≠ hqH := by decide
@[simp] theorem phq_hqH_ne_lDg : hqH ≠ lDg := by decide
@[simp] theorem phq_lDg_ne_hqH : lDg ≠ hqH := by decide
@[simp] theorem phq_hqH_ne_lDi : hqH ≠ lDi := by decide
@[simp] theorem phq_lDi_ne_hqH : lDi ≠ hqH := by decide
@[simp] theorem phq_hqH_ne_lRp : hqH ≠ lRp := by decide
@[simp] theorem phq_lRp_ne_hqH : lRp ≠ hqH := by decide
@[simp] theorem phq_hqH_ne_lRn : hqH ≠ lRn := by decide
@[simp] theorem phq_lRn_ne_hqH : lRn ≠ hqH := by decide
@[simp] theorem phq_hqH_ne_lFle : hqH ≠ lFle := by decide
@[simp] theorem phq_lFle_ne_hqH : lFle ≠ hqH := by decide
@[simp] theorem phq_hqH_ne_lKb : hqH ≠ lKb := by decide
@[simp] theorem phq_lKb_ne_hqH : lKb ≠ hqH := by decide
@[simp] theorem phq_hqH_ne_lDir : hqH ≠ lDir := by decide
@[simp] theorem phq_lDir_ne_hqH : lDir ≠ hqH := by decide
@[simp] theorem phq_hqH_ne_lFln : hqH ≠ lFln := by decide
@[simp] theorem phq_lFln_ne_hqH : lFln ≠ hqH := by decide
@[simp] theorem phq_hqH_ne_lFll : hqH ≠ lFll := by decide
@[simp] theorem phq_lFll_ne_hqH : lFll ≠ hqH := by decide
@[simp] theorem phq_hqH_ne_lFls : hqH ≠ lFls := by decide
@[simp] theorem phq_lFls_ne_hqH : lFls ≠ hqH := by decide
@[simp] theorem phq_hqH_ne_kFu : hqH ≠ kFu := by decide
@[simp] theorem phq_kFu_ne_hqH : kFu ≠ hqH := by decide
@[simp] theorem phq_hqH_ne_kD : hqH ≠ kD := by decide
@[simp] theorem phq_kD_ne_hqH : kD ≠ hqH := by decide
@[simp] theorem phq_hqN_ne_hqF : hqN ≠ hqF := by decide
@[simp] theorem phq_hqN_ne_hqH : hqN ≠ hqH := by decide
@[simp] theorem phq_hqN_ne_hqU : hqN ≠ hqU := by decide
@[simp] theorem phq_hqN_ne_hqP : hqN ≠ hqP := by decide
@[simp] theorem phq_hqN_ne_hqQ : hqN ≠ hqQ := by decide
@[simp] theorem phq_hqN_ne_hqLp : hqN ≠ hqLp := by decide
@[simp] theorem phq_hqN_ne_hqLl : hqN ≠ hqLl := by decide
@[simp] theorem phq_hqN_ne_hqT : hqN ≠ hqT := by decide
@[simp] theorem phq_hqN_ne_hqW : hqN ≠ hqW := by decide
@[simp] theorem phq_hqN_ne_hqS : hqN ≠ hqS := by decide
@[simp] theorem phq_hqN_ne_hqN2 : hqN ≠ hqN2 := by decide
@[simp] theorem phq_hqN_ne_hqP2 : hqN ≠ hqP2 := by decide
@[simp] theorem phq_hqN_ne_hqI2 : hqN ≠ hqI2 := by decide
@[simp] theorem phq_hqN_ne_hqTb : hqN ≠ hqTb := by decide
@[simp] theorem phq_hqN_ne_hqTq : hqN ≠ hqTq := by decide
@[simp] theorem phq_hqN_ne_hqNf : hqN ≠ hqNf := by decide
@[simp] theorem phq_hqN_ne_hqBp : hqN ≠ hqBp := by decide
@[simp] theorem phq_hqN_ne_hqBd : hqN ≠ hqBd := by decide
@[simp] theorem phq_hqN_ne_lFl : hqN ≠ lFl := by decide
@[simp] theorem phq_lFl_ne_hqN : lFl ≠ hqN := by decide
@[simp] theorem phq_hqN_ne_lDh : hqN ≠ lDh := by decide
@[simp] theorem phq_lDh_ne_hqN : lDh ≠ hqN := by decide
@[simp] theorem phq_hqN_ne_lDt : hqN ≠ lDt := by decide
@[simp] theorem phq_lDt_ne_hqN : lDt ≠ hqN := by decide
@[simp] theorem phq_hqN_ne_lDg : hqN ≠ lDg := by decide
@[simp] theorem phq_lDg_ne_hqN : lDg ≠ hqN := by decide
@[simp] theorem phq_hqN_ne_lDi : hqN ≠ lDi := by decide
@[simp] theorem phq_lDi_ne_hqN : lDi ≠ hqN := by decide
@[simp] theorem phq_hqN_ne_lRp : hqN ≠ lRp := by decide
@[simp] theorem phq_lRp_ne_hqN : lRp ≠ hqN := by decide
@[simp] theorem phq_hqN_ne_lRn : hqN ≠ lRn := by decide
@[simp] theorem phq_lRn_ne_hqN : lRn ≠ hqN := by decide
@[simp] theorem phq_hqN_ne_lFle : hqN ≠ lFle := by decide
@[simp] theorem phq_lFle_ne_hqN : lFle ≠ hqN := by decide
@[simp] theorem phq_hqN_ne_lKb : hqN ≠ lKb := by decide
@[simp] theorem phq_lKb_ne_hqN : lKb ≠ hqN := by decide
@[simp] theorem phq_hqN_ne_lDir : hqN ≠ lDir := by decide
@[simp] theorem phq_lDir_ne_hqN : lDir ≠ hqN := by decide
@[simp] theorem phq_hqN_ne_lFln : hqN ≠ lFln := by decide
@[simp] theorem phq_lFln_ne_hqN : lFln ≠ hqN := by decide
@[simp] theorem phq_hqN_ne_lFll : hqN ≠ lFll := by decide
@[simp] theorem phq_lFll_ne_hqN : lFll ≠ hqN := by decide
@[simp] theorem phq_hqN_ne_lFls : hqN ≠ lFls := by decide
@[simp] theorem phq_lFls_ne_hqN : lFls ≠ hqN := by decide
@[simp] theorem phq_hqN_ne_kFu : hqN ≠ kFu := by decide
@[simp] theorem phq_kFu_ne_hqN : kFu ≠ hqN := by decide
@[simp] theorem phq_hqN_ne_kD : hqN ≠ kD := by decide
@[simp] theorem phq_kD_ne_hqN : kD ≠ hqN := by decide
@[simp] theorem phq_hqU_ne_hqF : hqU ≠ hqF := by decide
@[simp] theorem phq_hqU_ne_hqH : hqU ≠ hqH := by decide
@[simp] theorem phq_hqU_ne_hqN : hqU ≠ hqN := by decide
@[simp] theorem phq_hqU_ne_hqP : hqU ≠ hqP := by decide
@[simp] theorem phq_hqU_ne_hqQ : hqU ≠ hqQ := by decide
@[simp] theorem phq_hqU_ne_hqLp : hqU ≠ hqLp := by decide
@[simp] theorem phq_hqU_ne_hqLl : hqU ≠ hqLl := by decide
@[simp] theorem phq_hqU_ne_hqT : hqU ≠ hqT := by decide
@[simp] theorem phq_hqU_ne_hqW : hqU ≠ hqW := by decide
@[simp] theorem phq_hqU_ne_hqS : hqU ≠ hqS := by decide
@[simp] theorem phq_hqU_ne_hqN2 : hqU ≠ hqN2 := by decide
@[simp] theorem phq_hqU_ne_hqP2 : hqU ≠ hqP2 := by decide
@[simp] theorem phq_hqU_ne_hqI2 : hqU ≠ hqI2 := by decide
@[simp] theorem phq_hqU_ne_hqTb : hqU ≠ hqTb := by decide
@[simp] theorem phq_hqU_ne_hqTq : hqU ≠ hqTq := by decide
@[simp] theorem phq_hqU_ne_hqNf : hqU ≠ hqNf := by decide
@[simp] theorem phq_hqU_ne_hqBp : hqU ≠ hqBp := by decide
@[simp] theorem phq_hqU_ne_hqBd : hqU ≠ hqBd := by decide
@[simp] theorem phq_hqU_ne_lFl : hqU ≠ lFl := by decide
@[simp] theorem phq_lFl_ne_hqU : lFl ≠ hqU := by decide
@[simp] theorem phq_hqU_ne_lDh : hqU ≠ lDh := by decide
@[simp] theorem phq_lDh_ne_hqU : lDh ≠ hqU := by decide
@[simp] theorem phq_hqU_ne_lDt : hqU ≠ lDt := by decide
@[simp] theorem phq_lDt_ne_hqU : lDt ≠ hqU := by decide
@[simp] theorem phq_hqU_ne_lDg : hqU ≠ lDg := by decide
@[simp] theorem phq_lDg_ne_hqU : lDg ≠ hqU := by decide
@[simp] theorem phq_hqU_ne_lDi : hqU ≠ lDi := by decide
@[simp] theorem phq_lDi_ne_hqU : lDi ≠ hqU := by decide
@[simp] theorem phq_hqU_ne_lRp : hqU ≠ lRp := by decide
@[simp] theorem phq_lRp_ne_hqU : lRp ≠ hqU := by decide
@[simp] theorem phq_hqU_ne_lRn : hqU ≠ lRn := by decide
@[simp] theorem phq_lRn_ne_hqU : lRn ≠ hqU := by decide
@[simp] theorem phq_hqU_ne_lFle : hqU ≠ lFle := by decide
@[simp] theorem phq_lFle_ne_hqU : lFle ≠ hqU := by decide
@[simp] theorem phq_hqU_ne_lKb : hqU ≠ lKb := by decide
@[simp] theorem phq_lKb_ne_hqU : lKb ≠ hqU := by decide
@[simp] theorem phq_hqU_ne_lDir : hqU ≠ lDir := by decide
@[simp] theorem phq_lDir_ne_hqU : lDir ≠ hqU := by decide
@[simp] theorem phq_hqU_ne_lFln : hqU ≠ lFln := by decide
@[simp] theorem phq_lFln_ne_hqU : lFln ≠ hqU := by decide
@[simp] theorem phq_hqU_ne_lFll : hqU ≠ lFll := by decide
@[simp] theorem phq_lFll_ne_hqU : lFll ≠ hqU := by decide
@[simp] theorem phq_hqU_ne_lFls : hqU ≠ lFls := by decide
@[simp] theorem phq_lFls_ne_hqU : lFls ≠ hqU := by decide
@[simp] theorem phq_hqU_ne_kFu : hqU ≠ kFu := by decide
@[simp] theorem phq_kFu_ne_hqU : kFu ≠ hqU := by decide
@[simp] theorem phq_hqU_ne_kD : hqU ≠ kD := by decide
@[simp] theorem phq_kD_ne_hqU : kD ≠ hqU := by decide
@[simp] theorem phq_hqP_ne_hqF : hqP ≠ hqF := by decide
@[simp] theorem phq_hqP_ne_hqH : hqP ≠ hqH := by decide
@[simp] theorem phq_hqP_ne_hqN : hqP ≠ hqN := by decide
@[simp] theorem phq_hqP_ne_hqU : hqP ≠ hqU := by decide
@[simp] theorem phq_hqP_ne_hqQ : hqP ≠ hqQ := by decide
@[simp] theorem phq_hqP_ne_hqLp : hqP ≠ hqLp := by decide
@[simp] theorem phq_hqP_ne_hqLl : hqP ≠ hqLl := by decide
@[simp] theorem phq_hqP_ne_hqT : hqP ≠ hqT := by decide
@[simp] theorem phq_hqP_ne_hqW : hqP ≠ hqW := by decide
@[simp] theorem phq_hqP_ne_hqS : hqP ≠ hqS := by decide
@[simp] theorem phq_hqP_ne_hqN2 : hqP ≠ hqN2 := by decide
@[simp] theorem phq_hqP_ne_hqP2 : hqP ≠ hqP2 := by decide
@[simp] theorem phq_hqP_ne_hqI2 : hqP ≠ hqI2 := by decide
@[simp] theorem phq_hqP_ne_hqTb : hqP ≠ hqTb := by decide
@[simp] theorem phq_hqP_ne_hqTq : hqP ≠ hqTq := by decide
@[simp] theorem phq_hqP_ne_hqNf : hqP ≠ hqNf := by decide
@[simp] theorem phq_hqP_ne_hqBp : hqP ≠ hqBp := by decide
@[simp] theorem phq_hqP_ne_hqBd : hqP ≠ hqBd := by decide
@[simp] theorem phq_hqP_ne_lFl : hqP ≠ lFl := by decide
@[simp] theorem phq_lFl_ne_hqP : lFl ≠ hqP := by decide
@[simp] theorem phq_hqP_ne_lDh : hqP ≠ lDh := by decide
@[simp] theorem phq_lDh_ne_hqP : lDh ≠ hqP := by decide
@[simp] theorem phq_hqP_ne_lDt : hqP ≠ lDt := by decide
@[simp] theorem phq_lDt_ne_hqP : lDt ≠ hqP := by decide
@[simp] theorem phq_hqP_ne_lDg : hqP ≠ lDg := by decide
@[simp] theorem phq_lDg_ne_hqP : lDg ≠ hqP := by decide
@[simp] theorem phq_hqP_ne_lDi : hqP ≠ lDi := by decide
@[simp] theorem phq_lDi_ne_hqP : lDi ≠ hqP := by decide
@[simp] theorem phq_hqP_ne_lRp : hqP ≠ lRp := by decide
@[simp] theorem phq_lRp_ne_hqP : lRp ≠ hqP := by decide
@[simp] theorem phq_hqP_ne_lRn : hqP ≠ lRn := by decide
@[simp] theorem phq_lRn_ne_hqP : lRn ≠ hqP := by decide
@[simp] theorem phq_hqP_ne_lFle : hqP ≠ lFle := by decide
@[simp] theorem phq_lFle_ne_hqP : lFle ≠ hqP := by decide
@[simp] theorem phq_hqP_ne_lKb : hqP ≠ lKb := by decide
@[simp] theorem phq_lKb_ne_hqP : lKb ≠ hqP := by decide
@[simp] theorem phq_hqP_ne_lDir : hqP ≠ lDir := by decide
@[simp] theorem phq_lDir_ne_hqP : lDir ≠ hqP := by decide
@[simp] theorem phq_hqP_ne_lFln : hqP ≠ lFln := by decide
@[simp] theorem phq_lFln_ne_hqP : lFln ≠ hqP := by decide
@[simp] theorem phq_hqP_ne_lFll : hqP ≠ lFll := by decide
@[simp] theorem phq_lFll_ne_hqP : lFll ≠ hqP := by decide
@[simp] theorem phq_hqP_ne_lFls : hqP ≠ lFls := by decide
@[simp] theorem phq_lFls_ne_hqP : lFls ≠ hqP := by decide
@[simp] theorem phq_hqP_ne_kFu : hqP ≠ kFu := by decide
@[simp] theorem phq_kFu_ne_hqP : kFu ≠ hqP := by decide
@[simp] theorem phq_hqP_ne_kD : hqP ≠ kD := by decide
@[simp] theorem phq_kD_ne_hqP : kD ≠ hqP := by decide
@[simp] theorem phq_hqQ_ne_hqF : hqQ ≠ hqF := by decide
@[simp] theorem phq_hqQ_ne_hqH : hqQ ≠ hqH := by decide
@[simp] theorem phq_hqQ_ne_hqN : hqQ ≠ hqN := by decide
@[simp] theorem phq_hqQ_ne_hqU : hqQ ≠ hqU := by decide
@[simp] theorem phq_hqQ_ne_hqP : hqQ ≠ hqP := by decide
@[simp] theorem phq_hqQ_ne_hqLp : hqQ ≠ hqLp := by decide
@[simp] theorem phq_hqQ_ne_hqLl : hqQ ≠ hqLl := by decide
@[simp] theorem phq_hqQ_ne_hqT : hqQ ≠ hqT := by decide
@[simp] theorem phq_hqQ_ne_hqW : hqQ ≠ hqW := by decide
@[simp] theorem phq_hqQ_ne_hqS : hqQ ≠ hqS := by decide
@[simp] theorem phq_hqQ_ne_hqN2 : hqQ ≠ hqN2 := by decide
@[simp] theorem phq_hqQ_ne_hqP2 : hqQ ≠ hqP2 := by decide
@[simp] theorem phq_hqQ_ne_hqI2 : hqQ ≠ hqI2 := by decide
@[simp] theorem phq_hqQ_ne_hqTb : hqQ ≠ hqTb := by decide
@[simp] theorem phq_hqQ_ne_hqTq : hqQ ≠ hqTq := by decide
@[simp] theorem phq_hqQ_ne_hqNf : hqQ ≠ hqNf := by decide
@[simp] theorem phq_hqQ_ne_hqBp : hqQ ≠ hqBp := by decide
@[simp] theorem phq_hqQ_ne_hqBd : hqQ ≠ hqBd := by decide
@[simp] theorem phq_hqQ_ne_lFl : hqQ ≠ lFl := by decide
@[simp] theorem phq_lFl_ne_hqQ : lFl ≠ hqQ := by decide
@[simp] theorem phq_hqQ_ne_lDh : hqQ ≠ lDh := by decide
@[simp] theorem phq_lDh_ne_hqQ : lDh ≠ hqQ := by decide
@[simp] theorem phq_hqQ_ne_lDt : hqQ ≠ lDt := by decide
@[simp] theorem phq_lDt_ne_hqQ : lDt ≠ hqQ := by decide
@[simp] theorem phq_hqQ_ne_lDg : hqQ ≠ lDg := by decide
@[simp] theorem phq_lDg_ne_hqQ : lDg ≠ hqQ := by decide
@[simp] theorem phq_hqQ_ne_lDi : hqQ ≠ lDi := by decide
@[simp] theorem phq_lDi_ne_hqQ : lDi ≠ hqQ := by decide
@[simp] theorem phq_hqQ_ne_lRp : hqQ ≠ lRp := by decide
@[simp] theorem phq_lRp_ne_hqQ : lRp ≠ hqQ := by decide
@[simp] theorem phq_hqQ_ne_lRn : hqQ ≠ lRn := by decide
@[simp] theorem phq_lRn_ne_hqQ : lRn ≠ hqQ := by decide
@[simp] theorem phq_hqQ_ne_lFle : hqQ ≠ lFle := by decide
@[simp] theorem phq_lFle_ne_hqQ : lFle ≠ hqQ := by decide
@[simp] theorem phq_hqQ_ne_lKb : hqQ ≠ lKb := by decide
@[simp] theorem phq_lKb_ne_hqQ : lKb ≠ hqQ := by decide
@[simp] theorem phq_hqQ_ne_lDir : hqQ ≠ lDir := by decide
@[simp] theorem phq_lDir_ne_hqQ : lDir ≠ hqQ := by decide
@[simp] theorem phq_hqQ_ne_lFln : hqQ ≠ lFln := by decide
@[simp] theorem phq_lFln_ne_hqQ : lFln ≠ hqQ := by decide
@[simp] theorem phq_hqQ_ne_lFll : hqQ ≠ lFll := by decide
@[simp] theorem phq_lFll_ne_hqQ : lFll ≠ hqQ := by decide
@[simp] theorem phq_hqQ_ne_lFls : hqQ ≠ lFls := by decide
@[simp] theorem phq_lFls_ne_hqQ : lFls ≠ hqQ := by decide
@[simp] theorem phq_hqQ_ne_kFu : hqQ ≠ kFu := by decide
@[simp] theorem phq_kFu_ne_hqQ : kFu ≠ hqQ := by decide
@[simp] theorem phq_hqQ_ne_kD : hqQ ≠ kD := by decide
@[simp] theorem phq_kD_ne_hqQ : kD ≠ hqQ := by decide
@[simp] theorem phq_hqLp_ne_hqF : hqLp ≠ hqF := by decide
@[simp] theorem phq_hqLp_ne_hqH : hqLp ≠ hqH := by decide
@[simp] theorem phq_hqLp_ne_hqN : hqLp ≠ hqN := by decide
@[simp] theorem phq_hqLp_ne_hqU : hqLp ≠ hqU := by decide
@[simp] theorem phq_hqLp_ne_hqP : hqLp ≠ hqP := by decide
@[simp] theorem phq_hqLp_ne_hqQ : hqLp ≠ hqQ := by decide
@[simp] theorem phq_hqLp_ne_hqLl : hqLp ≠ hqLl := by decide
@[simp] theorem phq_hqLp_ne_hqT : hqLp ≠ hqT := by decide
@[simp] theorem phq_hqLp_ne_hqW : hqLp ≠ hqW := by decide
@[simp] theorem phq_hqLp_ne_hqS : hqLp ≠ hqS := by decide
@[simp] theorem phq_hqLp_ne_hqN2 : hqLp ≠ hqN2 := by decide
@[simp] theorem phq_hqLp_ne_hqP2 : hqLp ≠ hqP2 := by decide
@[simp] theorem phq_hqLp_ne_hqI2 : hqLp ≠ hqI2 := by decide
@[simp] theorem phq_hqLp_ne_hqTb : hqLp ≠ hqTb := by decide
@[simp] theorem phq_hqLp_ne_hqTq : hqLp ≠ hqTq := by decide
@[simp] theorem phq_hqLp_ne_hqNf : hqLp ≠ hqNf := by decide
@[simp] theorem phq_hqLp_ne_hqBp : hqLp ≠ hqBp := by decide
@[simp] theorem phq_hqLp_ne_hqBd : hqLp ≠ hqBd := by decide
@[simp] theorem phq_hqLp_ne_lFl : hqLp ≠ lFl := by decide
@[simp] theorem phq_lFl_ne_hqLp : lFl ≠ hqLp := by decide
@[simp] theorem phq_hqLp_ne_lDh : hqLp ≠ lDh := by decide
@[simp] theorem phq_lDh_ne_hqLp : lDh ≠ hqLp := by decide
@[simp] theorem phq_hqLp_ne_lDt : hqLp ≠ lDt := by decide
@[simp] theorem phq_lDt_ne_hqLp : lDt ≠ hqLp := by decide
@[simp] theorem phq_hqLp_ne_lDg : hqLp ≠ lDg := by decide
@[simp] theorem phq_lDg_ne_hqLp : lDg ≠ hqLp := by decide
@[simp] theorem phq_hqLp_ne_lDi : hqLp ≠ lDi := by decide
@[simp] theorem phq_lDi_ne_hqLp : lDi ≠ hqLp := by decide
@[simp] theorem phq_hqLp_ne_lRp : hqLp ≠ lRp := by decide
@[simp] theorem phq_lRp_ne_hqLp : lRp ≠ hqLp := by decide
@[simp] theorem phq_hqLp_ne_lRn : hqLp ≠ lRn := by decide
@[simp] theorem phq_lRn_ne_hqLp : lRn ≠ hqLp := by decide
@[simp] theorem phq_hqLp_ne_lFle : hqLp ≠ lFle := by decide
@[simp] theorem phq_lFle_ne_hqLp : lFle ≠ hqLp := by decide
@[simp] theorem phq_hqLp_ne_lKb : hqLp ≠ lKb := by decide
@[simp] theorem phq_lKb_ne_hqLp : lKb ≠ hqLp := by decide
@[simp] theorem phq_hqLp_ne_lDir : hqLp ≠ lDir := by decide
@[simp] theorem phq_lDir_ne_hqLp : lDir ≠ hqLp := by decide
@[simp] theorem phq_hqLp_ne_lFln : hqLp ≠ lFln := by decide
@[simp] theorem phq_lFln_ne_hqLp : lFln ≠ hqLp := by decide
@[simp] theorem phq_hqLp_ne_lFll : hqLp ≠ lFll := by decide
@[simp] theorem phq_lFll_ne_hqLp : lFll ≠ hqLp := by decide
@[simp] theorem phq_hqLp_ne_lFls : hqLp ≠ lFls := by decide
@[simp] theorem phq_lFls_ne_hqLp : lFls ≠ hqLp := by decide
@[simp] theorem phq_hqLp_ne_kFu : hqLp ≠ kFu := by decide
@[simp] theorem phq_kFu_ne_hqLp : kFu ≠ hqLp := by decide
@[simp] theorem phq_hqLp_ne_kD : hqLp ≠ kD := by decide
@[simp] theorem phq_kD_ne_hqLp : kD ≠ hqLp := by decide
@[simp] theorem phq_hqLl_ne_hqF : hqLl ≠ hqF := by decide
@[simp] theorem phq_hqLl_ne_hqH : hqLl ≠ hqH := by decide
@[simp] theorem phq_hqLl_ne_hqN : hqLl ≠ hqN := by decide
@[simp] theorem phq_hqLl_ne_hqU : hqLl ≠ hqU := by decide
@[simp] theorem phq_hqLl_ne_hqP : hqLl ≠ hqP := by decide
@[simp] theorem phq_hqLl_ne_hqQ : hqLl ≠ hqQ := by decide
@[simp] theorem phq_hqLl_ne_hqLp : hqLl ≠ hqLp := by decide
@[simp] theorem phq_hqLl_ne_hqT : hqLl ≠ hqT := by decide
@[simp] theorem phq_hqLl_ne_hqW : hqLl ≠ hqW := by decide
@[simp] theorem phq_hqLl_ne_hqS : hqLl ≠ hqS := by decide
@[simp] theorem phq_hqLl_ne_hqN2 : hqLl ≠ hqN2 := by decide
@[simp] theorem phq_hqLl_ne_hqP2 : hqLl ≠ hqP2 := by decide
@[simp] theorem phq_hqLl_ne_hqI2 : hqLl ≠ hqI2 := by decide
@[simp] theorem phq_hqLl_ne_hqTb : hqLl ≠ hqTb := by decide
@[simp] theorem phq_hqLl_ne_hqTq : hqLl ≠ hqTq := by decide
@[simp] theorem phq_hqLl_ne_hqNf : hqLl ≠ hqNf := by decide
@[simp] theorem phq_hqLl_ne_hqBp : hqLl ≠ hqBp := by decide
@[simp] theorem phq_hqLl_ne_hqBd : hqLl ≠ hqBd := by decide
@[simp] theorem phq_hqLl_ne_lFl : hqLl ≠ lFl := by decide
@[simp] theorem phq_lFl_ne_hqLl : lFl ≠ hqLl := by decide
@[simp] theorem phq_hqLl_ne_lDh : hqLl ≠ lDh := by decide
@[simp] theorem phq_lDh_ne_hqLl : lDh ≠ hqLl := by decide
@[simp] theorem phq_hqLl_ne_lDt : hqLl ≠ lDt := by decide
@[simp] theorem phq_lDt_ne_hqLl : lDt ≠ hqLl := by decide
@[simp] theorem phq_hqLl_ne_lDg : hqLl ≠ lDg := by decide
@[simp] theorem phq_lDg_ne_hqLl : lDg ≠ hqLl := by decide
@[simp] theorem phq_hqLl_ne_lDi : hqLl ≠ lDi := by decide
@[simp] theorem phq_lDi_ne_hqLl : lDi ≠ hqLl := by decide
@[simp] theorem phq_hqLl_ne_lRp : hqLl ≠ lRp := by decide
@[simp] theorem phq_lRp_ne_hqLl : lRp ≠ hqLl := by decide
@[simp] theorem phq_hqLl_ne_lRn : hqLl ≠ lRn := by decide
@[simp] theorem phq_lRn_ne_hqLl : lRn ≠ hqLl := by decide
@[simp] theorem phq_hqLl_ne_lFle : hqLl ≠ lFle := by decide
@[simp] theorem phq_lFle_ne_hqLl : lFle ≠ hqLl := by decide
@[simp] theorem phq_hqLl_ne_lKb : hqLl ≠ lKb := by decide
@[simp] theorem phq_lKb_ne_hqLl : lKb ≠ hqLl := by decide
@[simp] theorem phq_hqLl_ne_lDir : hqLl ≠ lDir := by decide
@[simp] theorem phq_lDir_ne_hqLl : lDir ≠ hqLl := by decide
@[simp] theorem phq_hqLl_ne_lFln : hqLl ≠ lFln := by decide
@[simp] theorem phq_lFln_ne_hqLl : lFln ≠ hqLl := by decide
@[simp] theorem phq_hqLl_ne_lFll : hqLl ≠ lFll := by decide
@[simp] theorem phq_lFll_ne_hqLl : lFll ≠ hqLl := by decide
@[simp] theorem phq_hqLl_ne_lFls : hqLl ≠ lFls := by decide
@[simp] theorem phq_lFls_ne_hqLl : lFls ≠ hqLl := by decide
@[simp] theorem phq_hqLl_ne_kFu : hqLl ≠ kFu := by decide
@[simp] theorem phq_kFu_ne_hqLl : kFu ≠ hqLl := by decide
@[simp] theorem phq_hqLl_ne_kD : hqLl ≠ kD := by decide
@[simp] theorem phq_kD_ne_hqLl : kD ≠ hqLl := by decide
@[simp] theorem phq_hqT_ne_hqF : hqT ≠ hqF := by decide
@[simp] theorem phq_hqT_ne_hqH : hqT ≠ hqH := by decide
@[simp] theorem phq_hqT_ne_hqN : hqT ≠ hqN := by decide
@[simp] theorem phq_hqT_ne_hqU : hqT ≠ hqU := by decide
@[simp] theorem phq_hqT_ne_hqP : hqT ≠ hqP := by decide
@[simp] theorem phq_hqT_ne_hqQ : hqT ≠ hqQ := by decide
@[simp] theorem phq_hqT_ne_hqLp : hqT ≠ hqLp := by decide
@[simp] theorem phq_hqT_ne_hqLl : hqT ≠ hqLl := by decide
@[simp] theorem phq_hqT_ne_hqW : hqT ≠ hqW := by decide
@[simp] theorem phq_hqT_ne_hqS : hqT ≠ hqS := by decide
@[simp] theorem phq_hqT_ne_hqN2 : hqT ≠ hqN2 := by decide
@[simp] theorem phq_hqT_ne_hqP2 : hqT ≠ hqP2 := by decide
@[simp] theorem phq_hqT_ne_hqI2 : hqT ≠ hqI2 := by decide
@[simp] theorem phq_hqT_ne_hqTb : hqT ≠ hqTb := by decide
@[simp] theorem phq_hqT_ne_hqTq : hqT ≠ hqTq := by decide
@[simp] theorem phq_hqT_ne_hqNf : hqT ≠ hqNf := by decide
@[simp] theorem phq_hqT_ne_hqBp : hqT ≠ hqBp := by decide
@[simp] theorem phq_hqT_ne_hqBd : hqT ≠ hqBd := by decide
@[simp] theorem phq_hqT_ne_lFl : hqT ≠ lFl := by decide
@[simp] theorem phq_lFl_ne_hqT : lFl ≠ hqT := by decide
@[simp] theorem phq_hqT_ne_lDh : hqT ≠ lDh := by decide
@[simp] theorem phq_lDh_ne_hqT : lDh ≠ hqT := by decide
@[simp] theorem phq_hqT_ne_lDt : hqT ≠ lDt := by decide
@[simp] theorem phq_lDt_ne_hqT : lDt ≠ hqT := by decide
@[simp] theorem phq_hqT_ne_lDg : hqT ≠ lDg := by decide
@[simp] theorem phq_lDg_ne_hqT : lDg ≠ hqT := by decide
@[simp] theorem phq_hqT_ne_lDi : hqT ≠ lDi := by decide
@[simp] theorem phq_lDi_ne_hqT : lDi ≠ hqT := by decide
@[simp] theorem phq_hqT_ne_lRp : hqT ≠ lRp := by decide
@[simp] theorem phq_lRp_ne_hqT : lRp ≠ hqT := by decide
@[simp] theorem phq_hqT_ne_lRn : hqT ≠ lRn := by decide
@[simp] theorem phq_lRn_ne_hqT : lRn ≠ hqT := by decide
@[simp] theorem phq_hqT_ne_lFle : hqT ≠ lFle := by decide
@[simp] theorem phq_lFle_ne_hqT : lFle ≠ hqT := by decide
@[simp] theorem phq_hqT_ne_lKb : hqT ≠ lKb := by decide
@[simp] theorem phq_lKb_ne_hqT : lKb ≠ hqT := by decide
@[simp] theorem phq_hqT_ne_lDir : hqT ≠ lDir := by decide
@[simp] theorem phq_lDir_ne_hqT : lDir ≠ hqT := by decide
@[simp] theorem phq_hqT_ne_lFln : hqT ≠ lFln := by decide
@[simp] theorem phq_lFln_ne_hqT : lFln ≠ hqT := by decide
@[simp] theorem phq_hqT_ne_lFll : hqT ≠ lFll := by decide
@[simp] theorem phq_lFll_ne_hqT : lFll ≠ hqT := by decide
@[simp] theorem phq_hqT_ne_lFls : hqT ≠ lFls := by decide
@[simp] theorem phq_lFls_ne_hqT : lFls ≠ hqT := by decide
@[simp] theorem phq_hqT_ne_kFu : hqT ≠ kFu := by decide
@[simp] theorem phq_kFu_ne_hqT : kFu ≠ hqT := by decide
@[simp] theorem phq_hqT_ne_kD : hqT ≠ kD := by decide
@[simp] theorem phq_kD_ne_hqT : kD ≠ hqT := by decide
@[simp] theorem phq_hqW_ne_hqF : hqW ≠ hqF := by decide
@[simp] theorem phq_hqW_ne_hqH : hqW ≠ hqH := by decide
@[simp] theorem phq_hqW_ne_hqN : hqW ≠ hqN := by decide
@[simp] theorem phq_hqW_ne_hqU : hqW ≠ hqU := by decide
@[simp] theorem phq_hqW_ne_hqP : hqW ≠ hqP := by decide
@[simp] theorem phq_hqW_ne_hqQ : hqW ≠ hqQ := by decide
@[simp] theorem phq_hqW_ne_hqLp : hqW ≠ hqLp := by decide
@[simp] theorem phq_hqW_ne_hqLl : hqW ≠ hqLl := by decide
@[simp] theorem phq_hqW_ne_hqT : hqW ≠ hqT := by decide
@[simp] theorem phq_hqW_ne_hqS : hqW ≠ hqS := by decide
@[simp] theorem phq_hqW_ne_hqN2 : hqW ≠ hqN2 := by decide
@[simp] theorem phq_hqW_ne_hqP2 : hqW ≠ hqP2 := by decide
@[simp] theorem phq_hqW_ne_hqI2 : hqW ≠ hqI2 := by decide
@[simp] theorem phq_hqW_ne_hqTb : hqW ≠ hqTb := by decide
@[simp] theorem phq_hqW_ne_hqTq : hqW ≠ hqTq := by decide
@[simp] theorem phq_hqW_ne_hqNf : hqW ≠ hqNf := by decide
@[simp] theorem phq_hqW_ne_hqBp : hqW ≠ hqBp := by decide
@[simp] theorem phq_hqW_ne_hqBd : hqW ≠ hqBd := by decide
@[simp] theorem phq_hqW_ne_lFl : hqW ≠ lFl := by decide
@[simp] theorem phq_lFl_ne_hqW : lFl ≠ hqW := by decide
@[simp] theorem phq_hqW_ne_lDh : hqW ≠ lDh := by decide
@[simp] theorem phq_lDh_ne_hqW : lDh ≠ hqW := by decide
@[simp] theorem phq_hqW_ne_lDt : hqW ≠ lDt := by decide
@[simp] theorem phq_lDt_ne_hqW : lDt ≠ hqW := by decide
@[simp] theorem phq_hqW_ne_lDg : hqW ≠ lDg := by decide
@[simp] theorem phq_lDg_ne_hqW : lDg ≠ hqW := by decide
@[simp] theorem phq_hqW_ne_lDi : hqW ≠ lDi := by decide
@[simp] theorem phq_lDi_ne_hqW : lDi ≠ hqW := by decide
@[simp] theorem phq_hqW_ne_lRp : hqW ≠ lRp := by decide
@[simp] theorem phq_lRp_ne_hqW : lRp ≠ hqW := by decide
@[simp] theorem phq_hqW_ne_lRn : hqW ≠ lRn := by decide
@[simp] theorem phq_lRn_ne_hqW : lRn ≠ hqW := by decide
@[simp] theorem phq_hqW_ne_lFle : hqW ≠ lFle := by decide
@[simp] theorem phq_lFle_ne_hqW : lFle ≠ hqW := by decide
@[simp] theorem phq_hqW_ne_lKb : hqW ≠ lKb := by decide
@[simp] theorem phq_lKb_ne_hqW : lKb ≠ hqW := by decide
@[simp] theorem phq_hqW_ne_lDir : hqW ≠ lDir := by decide
@[simp] theorem phq_lDir_ne_hqW : lDir ≠ hqW := by decide
@[simp] theorem phq_hqW_ne_lFln : hqW ≠ lFln := by decide
@[simp] theorem phq_lFln_ne_hqW : lFln ≠ hqW := by decide
@[simp] theorem phq_hqW_ne_lFll : hqW ≠ lFll := by decide
@[simp] theorem phq_lFll_ne_hqW : lFll ≠ hqW := by decide
@[simp] theorem phq_hqW_ne_lFls : hqW ≠ lFls := by decide
@[simp] theorem phq_lFls_ne_hqW : lFls ≠ hqW := by decide
@[simp] theorem phq_hqW_ne_kFu : hqW ≠ kFu := by decide
@[simp] theorem phq_kFu_ne_hqW : kFu ≠ hqW := by decide
@[simp] theorem phq_hqW_ne_kD : hqW ≠ kD := by decide
@[simp] theorem phq_kD_ne_hqW : kD ≠ hqW := by decide
@[simp] theorem phq_hqS_ne_hqF : hqS ≠ hqF := by decide
@[simp] theorem phq_hqS_ne_hqH : hqS ≠ hqH := by decide
@[simp] theorem phq_hqS_ne_hqN : hqS ≠ hqN := by decide
@[simp] theorem phq_hqS_ne_hqU : hqS ≠ hqU := by decide
@[simp] theorem phq_hqS_ne_hqP : hqS ≠ hqP := by decide
@[simp] theorem phq_hqS_ne_hqQ : hqS ≠ hqQ := by decide
@[simp] theorem phq_hqS_ne_hqLp : hqS ≠ hqLp := by decide
@[simp] theorem phq_hqS_ne_hqLl : hqS ≠ hqLl := by decide
@[simp] theorem phq_hqS_ne_hqT : hqS ≠ hqT := by decide
@[simp] theorem phq_hqS_ne_hqW : hqS ≠ hqW := by decide
@[simp] theorem phq_hqS_ne_hqN2 : hqS ≠ hqN2 := by decide
@[simp] theorem phq_hqS_ne_hqP2 : hqS ≠ hqP2 := by decide
@[simp] theorem phq_hqS_ne_hqI2 : hqS ≠ hqI2 := by decide
@[simp] theorem phq_hqS_ne_hqTb : hqS ≠ hqTb := by decide
@[simp] theorem phq_hqS_ne_hqTq : hqS ≠ hqTq := by decide
@[simp] theorem phq_hqS_ne_hqNf : hqS ≠ hqNf := by decide
@[simp] theorem phq_hqS_ne_hqBp : hqS ≠ hqBp := by decide
@[simp] theorem phq_hqS_ne_hqBd : hqS ≠ hqBd := by decide
@[simp] theorem phq_hqS_ne_lFl : hqS ≠ lFl := by decide
@[simp] theorem phq_lFl_ne_hqS : lFl ≠ hqS := by decide
@[simp] theorem phq_hqS_ne_lDh : hqS ≠ lDh := by decide
@[simp] theorem phq_lDh_ne_hqS : lDh ≠ hqS := by decide
@[simp] theorem phq_hqS_ne_lDt : hqS ≠ lDt := by decide
@[simp] theorem phq_lDt_ne_hqS : lDt ≠ hqS := by decide
@[simp] theorem phq_hqS_ne_lDg : hqS ≠ lDg := by decide
@[simp] theorem phq_lDg_ne_hqS : lDg ≠ hqS := by decide
@[simp] theorem phq_hqS_ne_lDi : hqS ≠ lDi := by decide
@[simp] theorem phq_lDi_ne_hqS : lDi ≠ hqS := by decide
@[simp] theorem phq_hqS_ne_lRp : hqS ≠ lRp := by decide
@[simp] theorem phq_lRp_ne_hqS : lRp ≠ hqS := by decide
@[simp] theorem phq_hqS_ne_lRn : hqS ≠ lRn := by decide
@[simp] theorem phq_lRn_ne_hqS : lRn ≠ hqS := by decide
@[simp] theorem phq_hqS_ne_lFle : hqS ≠ lFle := by decide
@[simp] theorem phq_lFle_ne_hqS : lFle ≠ hqS := by decide
@[simp] theorem phq_hqS_ne_lKb : hqS ≠ lKb := by decide
@[simp] theorem phq_lKb_ne_hqS : lKb ≠ hqS := by decide
@[simp] theorem phq_hqS_ne_lDir : hqS ≠ lDir := by decide
@[simp] theorem phq_lDir_ne_hqS : lDir ≠ hqS := by decide
@[simp] theorem phq_hqS_ne_lFln : hqS ≠ lFln := by decide
@[simp] theorem phq_lFln_ne_hqS : lFln ≠ hqS := by decide
@[simp] theorem phq_hqS_ne_lFll : hqS ≠ lFll := by decide
@[simp] theorem phq_lFll_ne_hqS : lFll ≠ hqS := by decide
@[simp] theorem phq_hqS_ne_lFls : hqS ≠ lFls := by decide
@[simp] theorem phq_lFls_ne_hqS : lFls ≠ hqS := by decide
@[simp] theorem phq_hqS_ne_kFu : hqS ≠ kFu := by decide
@[simp] theorem phq_kFu_ne_hqS : kFu ≠ hqS := by decide
@[simp] theorem phq_hqS_ne_kD : hqS ≠ kD := by decide
@[simp] theorem phq_kD_ne_hqS : kD ≠ hqS := by decide
@[simp] theorem phq_hqN2_ne_hqF : hqN2 ≠ hqF := by decide
@[simp] theorem phq_hqN2_ne_hqH : hqN2 ≠ hqH := by decide
@[simp] theorem phq_hqN2_ne_hqN : hqN2 ≠ hqN := by decide
@[simp] theorem phq_hqN2_ne_hqU : hqN2 ≠ hqU := by decide
@[simp] theorem phq_hqN2_ne_hqP : hqN2 ≠ hqP := by decide
@[simp] theorem phq_hqN2_ne_hqQ : hqN2 ≠ hqQ := by decide
@[simp] theorem phq_hqN2_ne_hqLp : hqN2 ≠ hqLp := by decide
@[simp] theorem phq_hqN2_ne_hqLl : hqN2 ≠ hqLl := by decide
@[simp] theorem phq_hqN2_ne_hqT : hqN2 ≠ hqT := by decide
@[simp] theorem phq_hqN2_ne_hqW : hqN2 ≠ hqW := by decide
@[simp] theorem phq_hqN2_ne_hqS : hqN2 ≠ hqS := by decide
@[simp] theorem phq_hqN2_ne_hqP2 : hqN2 ≠ hqP2 := by decide
@[simp] theorem phq_hqN2_ne_hqI2 : hqN2 ≠ hqI2 := by decide
@[simp] theorem phq_hqN2_ne_hqTb : hqN2 ≠ hqTb := by decide
@[simp] theorem phq_hqN2_ne_hqTq : hqN2 ≠ hqTq := by decide
@[simp] theorem phq_hqN2_ne_hqNf : hqN2 ≠ hqNf := by decide
@[simp] theorem phq_hqN2_ne_hqBp : hqN2 ≠ hqBp := by decide
@[simp] theorem phq_hqN2_ne_hqBd : hqN2 ≠ hqBd := by decide
@[simp] theorem phq_hqN2_ne_lFl : hqN2 ≠ lFl := by decide
@[simp] theorem phq_lFl_ne_hqN2 : lFl ≠ hqN2 := by decide
@[simp] theorem phq_hqN2_ne_lDh : hqN2 ≠ lDh := by decide
@[simp] theorem phq_lDh_ne_hqN2 : lDh ≠ hqN2 := by decide
@[simp] theorem phq_hqN2_ne_lDt : hqN2 ≠ lDt := by decide
@[simp] theorem phq_lDt_ne_hqN2 : lDt ≠ hqN2 := by decide
@[simp] theorem phq_hqN2_ne_lDg : hqN2 ≠ lDg := by decide
@[simp] theorem phq_lDg_ne_hqN2 : lDg ≠ hqN2 := by decide
@[simp] theorem phq_hqN2_ne_lDi : hqN2 ≠ lDi := by decide
@[simp] theorem phq_lDi_ne_hqN2 : lDi ≠ hqN2 := by decide
@[simp] theorem phq_hqN2_ne_lRp : hqN2 ≠ lRp := by decide
@[simp] theorem phq_lRp_ne_hqN2 : lRp ≠ hqN2 := by decide
@[simp] theorem phq_hqN2_ne_lRn : hqN2 ≠ lRn := by decide
@[simp] theorem phq_lRn_ne_hqN2 : lRn ≠ hqN2 := by decide
@[simp] theorem phq_hqN2_ne_lFle : hqN2 ≠ lFle := by decide
@[simp] theorem phq_lFle_ne_hqN2 : lFle ≠ hqN2 := by decide
@[simp] theorem phq_hqN2_ne_lKb : hqN2 ≠ lKb := by decide
@[simp] theorem phq_lKb_ne_hqN2 : lKb ≠ hqN2 := by decide
@[simp] theorem phq_hqN2_ne_lDir : hqN2 ≠ lDir := by decide
@[simp] theorem phq_lDir_ne_hqN2 : lDir ≠ hqN2 := by decide
@[simp] theorem phq_hqN2_ne_lFln : hqN2 ≠ lFln := by decide
@[simp] theorem phq_lFln_ne_hqN2 : lFln ≠ hqN2 := by decide
@[simp] theorem phq_hqN2_ne_lFll : hqN2 ≠ lFll := by decide
@[simp] theorem phq_lFll_ne_hqN2 : lFll ≠ hqN2 := by decide
@[simp] theorem phq_hqN2_ne_lFls : hqN2 ≠ lFls := by decide
@[simp] theorem phq_lFls_ne_hqN2 : lFls ≠ hqN2 := by decide
@[simp] theorem phq_hqN2_ne_kFu : hqN2 ≠ kFu := by decide
@[simp] theorem phq_kFu_ne_hqN2 : kFu ≠ hqN2 := by decide
@[simp] theorem phq_hqN2_ne_kD : hqN2 ≠ kD := by decide
@[simp] theorem phq_kD_ne_hqN2 : kD ≠ hqN2 := by decide
@[simp] theorem phq_hqP2_ne_hqF : hqP2 ≠ hqF := by decide
@[simp] theorem phq_hqP2_ne_hqH : hqP2 ≠ hqH := by decide
@[simp] theorem phq_hqP2_ne_hqN : hqP2 ≠ hqN := by decide
@[simp] theorem phq_hqP2_ne_hqU : hqP2 ≠ hqU := by decide
@[simp] theorem phq_hqP2_ne_hqP : hqP2 ≠ hqP := by decide
@[simp] theorem phq_hqP2_ne_hqQ : hqP2 ≠ hqQ := by decide
@[simp] theorem phq_hqP2_ne_hqLp : hqP2 ≠ hqLp := by decide
@[simp] theorem phq_hqP2_ne_hqLl : hqP2 ≠ hqLl := by decide
@[simp] theorem phq_hqP2_ne_hqT : hqP2 ≠ hqT := by decide
@[simp] theorem phq_hqP2_ne_hqW : hqP2 ≠ hqW := by decide
@[simp] theorem phq_hqP2_ne_hqS : hqP2 ≠ hqS := by decide
@[simp] theorem phq_hqP2_ne_hqN2 : hqP2 ≠ hqN2 := by decide
@[simp] theorem phq_hqP2_ne_hqI2 : hqP2 ≠ hqI2 := by decide
@[simp] theorem phq_hqP2_ne_hqTb : hqP2 ≠ hqTb := by decide
@[simp] theorem phq_hqP2_ne_hqTq : hqP2 ≠ hqTq := by decide
@[simp] theorem phq_hqP2_ne_hqNf : hqP2 ≠ hqNf := by decide
@[simp] theorem phq_hqP2_ne_hqBp : hqP2 ≠ hqBp := by decide
@[simp] theorem phq_hqP2_ne_hqBd : hqP2 ≠ hqBd := by decide
@[simp] theorem phq_hqP2_ne_lFl : hqP2 ≠ lFl := by decide
@[simp] theorem phq_lFl_ne_hqP2 : lFl ≠ hqP2 := by decide
@[simp] theorem phq_hqP2_ne_lDh : hqP2 ≠ lDh := by decide
@[simp] theorem phq_lDh_ne_hqP2 : lDh ≠ hqP2 := by decide
@[simp] theorem phq_hqP2_ne_lDt : hqP2 ≠ lDt := by decide
@[simp] theorem phq_lDt_ne_hqP2 : lDt ≠ hqP2 := by decide
@[simp] theorem phq_hqP2_ne_lDg : hqP2 ≠ lDg := by decide
@[simp] theorem phq_lDg_ne_hqP2 : lDg ≠ hqP2 := by decide
@[simp] theorem phq_hqP2_ne_lDi : hqP2 ≠ lDi := by decide
@[simp] theorem phq_lDi_ne_hqP2 : lDi ≠ hqP2 := by decide
@[simp] theorem phq_hqP2_ne_lRp : hqP2 ≠ lRp := by decide
@[simp] theorem phq_lRp_ne_hqP2 : lRp ≠ hqP2 := by decide
@[simp] theorem phq_hqP2_ne_lRn : hqP2 ≠ lRn := by decide
@[simp] theorem phq_lRn_ne_hqP2 : lRn ≠ hqP2 := by decide
@[simp] theorem phq_hqP2_ne_lFle : hqP2 ≠ lFle := by decide
@[simp] theorem phq_lFle_ne_hqP2 : lFle ≠ hqP2 := by decide
@[simp] theorem phq_hqP2_ne_lKb : hqP2 ≠ lKb := by decide
@[simp] theorem phq_lKb_ne_hqP2 : lKb ≠ hqP2 := by decide
@[simp] theorem phq_hqP2_ne_lDir : hqP2 ≠ lDir := by decide
@[simp] theorem phq_lDir_ne_hqP2 : lDir ≠ hqP2 := by decide
@[simp] theorem phq_hqP2_ne_lFln : hqP2 ≠ lFln := by decide
@[simp] theorem phq_lFln_ne_hqP2 : lFln ≠ hqP2 := by decide
@[simp] theorem phq_hqP2_ne_lFll : hqP2 ≠ lFll := by decide
@[simp] theorem phq_lFll_ne_hqP2 : lFll ≠ hqP2 := by decide
@[simp] theorem phq_hqP2_ne_lFls : hqP2 ≠ lFls := by decide
@[simp] theorem phq_lFls_ne_hqP2 : lFls ≠ hqP2 := by decide
@[simp] theorem phq_hqP2_ne_kFu : hqP2 ≠ kFu := by decide
@[simp] theorem phq_kFu_ne_hqP2 : kFu ≠ hqP2 := by decide
@[simp] theorem phq_hqP2_ne_kD : hqP2 ≠ kD := by decide
@[simp] theorem phq_kD_ne_hqP2 : kD ≠ hqP2 := by decide
@[simp] theorem phq_hqI2_ne_hqF : hqI2 ≠ hqF := by decide
@[simp] theorem phq_hqI2_ne_hqH : hqI2 ≠ hqH := by decide
@[simp] theorem phq_hqI2_ne_hqN : hqI2 ≠ hqN := by decide
@[simp] theorem phq_hqI2_ne_hqU : hqI2 ≠ hqU := by decide
@[simp] theorem phq_hqI2_ne_hqP : hqI2 ≠ hqP := by decide
@[simp] theorem phq_hqI2_ne_hqQ : hqI2 ≠ hqQ := by decide
@[simp] theorem phq_hqI2_ne_hqLp : hqI2 ≠ hqLp := by decide
@[simp] theorem phq_hqI2_ne_hqLl : hqI2 ≠ hqLl := by decide
@[simp] theorem phq_hqI2_ne_hqT : hqI2 ≠ hqT := by decide
@[simp] theorem phq_hqI2_ne_hqW : hqI2 ≠ hqW := by decide
@[simp] theorem phq_hqI2_ne_hqS : hqI2 ≠ hqS := by decide
@[simp] theorem phq_hqI2_ne_hqN2 : hqI2 ≠ hqN2 := by decide
@[simp] theorem phq_hqI2_ne_hqP2 : hqI2 ≠ hqP2 := by decide
@[simp] theorem phq_hqI2_ne_hqTb : hqI2 ≠ hqTb := by decide
@[simp] theorem phq_hqI2_ne_hqTq : hqI2 ≠ hqTq := by decide
@[simp] theorem phq_hqI2_ne_hqNf : hqI2 ≠ hqNf := by decide
@[simp] theorem phq_hqI2_ne_hqBp : hqI2 ≠ hqBp := by decide
@[simp] theorem phq_hqI2_ne_hqBd : hqI2 ≠ hqBd := by decide
@[simp] theorem phq_hqI2_ne_lFl : hqI2 ≠ lFl := by decide
@[simp] theorem phq_lFl_ne_hqI2 : lFl ≠ hqI2 := by decide
@[simp] theorem phq_hqI2_ne_lDh : hqI2 ≠ lDh := by decide
@[simp] theorem phq_lDh_ne_hqI2 : lDh ≠ hqI2 := by decide
@[simp] theorem phq_hqI2_ne_lDt : hqI2 ≠ lDt := by decide
@[simp] theorem phq_lDt_ne_hqI2 : lDt ≠ hqI2 := by decide
@[simp] theorem phq_hqI2_ne_lDg : hqI2 ≠ lDg := by decide
@[simp] theorem phq_lDg_ne_hqI2 : lDg ≠ hqI2 := by decide
@[simp] theorem phq_hqI2_ne_lDi : hqI2 ≠ lDi := by decide
@[simp] theorem phq_lDi_ne_hqI2 : lDi ≠ hqI2 := by decide
@[simp] theorem phq_hqI2_ne_lRp : hqI2 ≠ lRp := by decide
@[simp] theorem phq_lRp_ne_hqI2 : lRp ≠ hqI2 := by decide
@[simp] theorem phq_hqI2_ne_lRn : hqI2 ≠ lRn := by decide
@[simp] theorem phq_lRn_ne_hqI2 : lRn ≠ hqI2 := by decide
@[simp] theorem phq_hqI2_ne_lFle : hqI2 ≠ lFle := by decide
@[simp] theorem phq_lFle_ne_hqI2 : lFle ≠ hqI2 := by decide
@[simp] theorem phq_hqI2_ne_lKb : hqI2 ≠ lKb := by decide
@[simp] theorem phq_lKb_ne_hqI2 : lKb ≠ hqI2 := by decide
@[simp] theorem phq_hqI2_ne_lDir : hqI2 ≠ lDir := by decide
@[simp] theorem phq_lDir_ne_hqI2 : lDir ≠ hqI2 := by decide
@[simp] theorem phq_hqI2_ne_lFln : hqI2 ≠ lFln := by decide
@[simp] theorem phq_lFln_ne_hqI2 : lFln ≠ hqI2 := by decide
@[simp] theorem phq_hqI2_ne_lFll : hqI2 ≠ lFll := by decide
@[simp] theorem phq_lFll_ne_hqI2 : lFll ≠ hqI2 := by decide
@[simp] theorem phq_hqI2_ne_lFls : hqI2 ≠ lFls := by decide
@[simp] theorem phq_lFls_ne_hqI2 : lFls ≠ hqI2 := by decide
@[simp] theorem phq_hqI2_ne_kFu : hqI2 ≠ kFu := by decide
@[simp] theorem phq_kFu_ne_hqI2 : kFu ≠ hqI2 := by decide
@[simp] theorem phq_hqI2_ne_kD : hqI2 ≠ kD := by decide
@[simp] theorem phq_kD_ne_hqI2 : kD ≠ hqI2 := by decide
@[simp] theorem phq_hqTb_ne_hqF : hqTb ≠ hqF := by decide
@[simp] theorem phq_hqTb_ne_hqH : hqTb ≠ hqH := by decide
@[simp] theorem phq_hqTb_ne_hqN : hqTb ≠ hqN := by decide
@[simp] theorem phq_hqTb_ne_hqU : hqTb ≠ hqU := by decide
@[simp] theorem phq_hqTb_ne_hqP : hqTb ≠ hqP := by decide
@[simp] theorem phq_hqTb_ne_hqQ : hqTb ≠ hqQ := by decide
@[simp] theorem phq_hqTb_ne_hqLp : hqTb ≠ hqLp := by decide
@[simp] theorem phq_hqTb_ne_hqLl : hqTb ≠ hqLl := by decide
@[simp] theorem phq_hqTb_ne_hqT : hqTb ≠ hqT := by decide
@[simp] theorem phq_hqTb_ne_hqW : hqTb ≠ hqW := by decide
@[simp] theorem phq_hqTb_ne_hqS : hqTb ≠ hqS := by decide
@[simp] theorem phq_hqTb_ne_hqN2 : hqTb ≠ hqN2 := by decide
@[simp] theorem phq_hqTb_ne_hqP2 : hqTb ≠ hqP2 := by decide
@[simp] theorem phq_hqTb_ne_hqI2 : hqTb ≠ hqI2 := by decide
@[simp] theorem phq_hqTb_ne_hqTq : hqTb ≠ hqTq := by decide
@[simp] theorem phq_hqTb_ne_hqNf : hqTb ≠ hqNf := by decide
@[simp] theorem phq_hqTb_ne_hqBp : hqTb ≠ hqBp := by decide
@[simp] theorem phq_hqTb_ne_hqBd : hqTb ≠ hqBd := by decide
@[simp] theorem phq_hqTb_ne_lFl : hqTb ≠ lFl := by decide
@[simp] theorem phq_lFl_ne_hqTb : lFl ≠ hqTb := by decide
@[simp] theorem phq_hqTb_ne_lDh : hqTb ≠ lDh := by decide
@[simp] theorem phq_lDh_ne_hqTb : lDh ≠ hqTb := by decide
@[simp] theorem phq_hqTb_ne_lDt : hqTb ≠ lDt := by decide
@[simp] theorem phq_lDt_ne_hqTb : lDt ≠ hqTb := by decide
@[simp] theorem phq_hqTb_ne_lDg : hqTb ≠ lDg := by decide
@[simp] theorem phq_lDg_ne_hqTb : lDg ≠ hqTb := by decide
@[simp] theorem phq_hqTb_ne_lDi : hqTb ≠ lDi := by decide
@[simp] theorem phq_lDi_ne_hqTb : lDi ≠ hqTb := by decide
@[simp] theorem phq_hqTb_ne_lRp : hqTb ≠ lRp := by decide
@[simp] theorem phq_lRp_ne_hqTb : lRp ≠ hqTb := by decide
@[simp] theorem phq_hqTb_ne_lRn : hqTb ≠ lRn := by decide
@[simp] theorem phq_lRn_ne_hqTb : lRn ≠ hqTb := by decide
@[simp] theorem phq_hqTb_ne_lFle : hqTb ≠ lFle := by decide
@[simp] theorem phq_lFle_ne_hqTb : lFle ≠ hqTb := by decide
@[simp] theorem phq_hqTb_ne_lKb : hqTb ≠ lKb := by decide
@[simp] theorem phq_lKb_ne_hqTb : lKb ≠ hqTb := by decide
@[simp] theorem phq_hqTb_ne_lDir : hqTb ≠ lDir := by decide
@[simp] theorem phq_lDir_ne_hqTb : lDir ≠ hqTb := by decide
@[simp] theorem phq_hqTb_ne_lFln : hqTb ≠ lFln := by decide
@[simp] theorem phq_lFln_ne_hqTb : lFln ≠ hqTb := by decide
@[simp] theorem phq_hqTb_ne_lFll : hqTb ≠ lFll := by decide
@[simp] theorem phq_lFll_ne_hqTb : lFll ≠ hqTb := by decide
@[simp] theorem phq_hqTb_ne_lFls : hqTb ≠ lFls := by decide
@[simp] theorem phq_lFls_ne_hqTb : lFls ≠ hqTb := by decide
@[simp] theorem phq_hqTb_ne_kFu : hqTb ≠ kFu := by decide
@[simp] theorem phq_kFu_ne_hqTb : kFu ≠ hqTb := by decide
@[simp] theorem phq_hqTb_ne_kD : hqTb ≠ kD := by decide
@[simp] theorem phq_kD_ne_hqTb : kD ≠ hqTb := by decide
@[simp] theorem phq_hqTq_ne_hqF : hqTq ≠ hqF := by decide
@[simp] theorem phq_hqTq_ne_hqH : hqTq ≠ hqH := by decide
@[simp] theorem phq_hqTq_ne_hqN : hqTq ≠ hqN := by decide
@[simp] theorem phq_hqTq_ne_hqU : hqTq ≠ hqU := by decide
@[simp] theorem phq_hqTq_ne_hqP : hqTq ≠ hqP := by decide
@[simp] theorem phq_hqTq_ne_hqQ : hqTq ≠ hqQ := by decide
@[simp] theorem phq_hqTq_ne_hqLp : hqTq ≠ hqLp := by decide
@[simp] theorem phq_hqTq_ne_hqLl : hqTq ≠ hqLl := by decide
@[simp] theorem phq_hqTq_ne_hqT : hqTq ≠ hqT := by decide
@[simp] theorem phq_hqTq_ne_hqW : hqTq ≠ hqW := by decide
@[simp] theorem phq_hqTq_ne_hqS : hqTq ≠ hqS := by decide
@[simp] theorem phq_hqTq_ne_hqN2 : hqTq ≠ hqN2 := by decide
@[simp] theorem phq_hqTq_ne_hqP2 : hqTq ≠ hqP2 := by decide
@[simp] theorem phq_hqTq_ne_hqI2 : hqTq ≠ hqI2 := by decide
@[simp] theorem phq_hqTq_ne_hqTb : hqTq ≠ hqTb := by decide
@[simp] theorem phq_hqTq_ne_hqNf : hqTq ≠ hqNf := by decide
@[simp] theorem phq_hqTq_ne_hqBp : hqTq ≠ hqBp := by decide
@[simp] theorem phq_hqTq_ne_hqBd : hqTq ≠ hqBd := by decide
@[simp] theorem phq_hqTq_ne_lFl : hqTq ≠ lFl := by decide
@[simp] theorem phq_lFl_ne_hqTq : lFl ≠ hqTq := by decide
@[simp] theorem phq_hqTq_ne_lDh : hqTq ≠ lDh := by decide
@[simp] theorem phq_lDh_ne_hqTq : lDh ≠ hqTq := by decide
@[simp] theorem phq_hqTq_ne_lDt : hqTq ≠ lDt := by decide
@[simp] theorem phq_lDt_ne_hqTq : lDt ≠ hqTq := by decide
@[simp] theorem phq_hqTq_ne_lDg : hqTq ≠ lDg := by decide
@[simp] theorem phq_lDg_ne_hqTq : lDg ≠ hqTq := by decide
@[simp] theorem phq_hqTq_ne_lDi : hqTq ≠ lDi := by decide
@[simp] theorem phq_lDi_ne_hqTq : lDi ≠ hqTq := by decide
@[simp] theorem phq_hqTq_ne_lRp : hqTq ≠ lRp := by decide
@[simp] theorem phq_lRp_ne_hqTq : lRp ≠ hqTq := by decide
@[simp] theorem phq_hqTq_ne_lRn : hqTq ≠ lRn := by decide
@[simp] theorem phq_lRn_ne_hqTq : lRn ≠ hqTq := by decide
@[simp] theorem phq_hqTq_ne_lFle : hqTq ≠ lFle := by decide
@[simp] theorem phq_lFle_ne_hqTq : lFle ≠ hqTq := by decide
@[simp] theorem phq_hqTq_ne_lKb : hqTq ≠ lKb := by decide
@[simp] theorem phq_lKb_ne_hqTq : lKb ≠ hqTq := by decide
@[simp] theorem phq_hqTq_ne_lDir : hqTq ≠ lDir := by decide
@[simp] theorem phq_lDir_ne_hqTq : lDir ≠ hqTq := by decide
@[simp] theorem phq_hqTq_ne_lFln : hqTq ≠ lFln := by decide
@[simp] theorem phq_lFln_ne_hqTq : lFln ≠ hqTq := by decide
@[simp] theorem phq_hqTq_ne_lFll : hqTq ≠ lFll := by decide
@[simp] theorem phq_lFll_ne_hqTq : lFll ≠ hqTq := by decide
@[simp] theorem phq_hqTq_ne_lFls : hqTq ≠ lFls := by decide
@[simp] theorem phq_lFls_ne_hqTq : lFls ≠ hqTq := by decide
@[simp] theorem phq_hqTq_ne_kFu : hqTq ≠ kFu := by decide
@[simp] theorem phq_kFu_ne_hqTq : kFu ≠ hqTq := by decide
@[simp] theorem phq_hqTq_ne_kD : hqTq ≠ kD := by decide
@[simp] theorem phq_kD_ne_hqTq : kD ≠ hqTq := by decide
@[simp] theorem phq_hqNf_ne_hqF : hqNf ≠ hqF := by decide
@[simp] theorem phq_hqNf_ne_hqH : hqNf ≠ hqH := by decide
@[simp] theorem phq_hqNf_ne_hqN : hqNf ≠ hqN := by decide
@[simp] theorem phq_hqNf_ne_hqU : hqNf ≠ hqU := by decide
@[simp] theorem phq_hqNf_ne_hqP : hqNf ≠ hqP := by decide
@[simp] theorem phq_hqNf_ne_hqQ : hqNf ≠ hqQ := by decide
@[simp] theorem phq_hqNf_ne_hqLp : hqNf ≠ hqLp := by decide
@[simp] theorem phq_hqNf_ne_hqLl : hqNf ≠ hqLl := by decide
@[simp] theorem phq_hqNf_ne_hqT : hqNf ≠ hqT := by decide
@[simp] theorem phq_hqNf_ne_hqW : hqNf ≠ hqW := by decide
@[simp] theorem phq_hqNf_ne_hqS : hqNf ≠ hqS := by decide
@[simp] theorem phq_hqNf_ne_hqN2 : hqNf ≠ hqN2 := by decide
@[simp] theorem phq_hqNf_ne_hqP2 : hqNf ≠ hqP2 := by decide
@[simp] theorem phq_hqNf_ne_hqI2 : hqNf ≠ hqI2 := by decide
@[simp] theorem phq_hqNf_ne_hqTb : hqNf ≠ hqTb := by decide
@[simp] theorem phq_hqNf_ne_hqTq : hqNf ≠ hqTq := by decide
@[simp] theorem phq_hqNf_ne_hqBp : hqNf ≠ hqBp := by decide
@[simp] theorem phq_hqNf_ne_hqBd : hqNf ≠ hqBd := by decide
@[simp] theorem phq_hqNf_ne_lFl : hqNf ≠ lFl := by decide
@[simp] theorem phq_lFl_ne_hqNf : lFl ≠ hqNf := by decide
@[simp] theorem phq_hqNf_ne_lDh : hqNf ≠ lDh := by decide
@[simp] theorem phq_lDh_ne_hqNf : lDh ≠ hqNf := by decide
@[simp] theorem phq_hqNf_ne_lDt : hqNf ≠ lDt := by decide
@[simp] theorem phq_lDt_ne_hqNf : lDt ≠ hqNf := by decide
@[simp] theorem phq_hqNf_ne_lDg : hqNf ≠ lDg := by decide
@[simp] theorem phq_lDg_ne_hqNf : lDg ≠ hqNf := by decide
@[simp] theorem phq_hqNf_ne_lDi : hqNf ≠ lDi := by decide
@[simp] theorem phq_lDi_ne_hqNf : lDi ≠ hqNf := by decide
@[simp] theorem phq_hqNf_ne_lRp : hqNf ≠ lRp := by decide
@[simp] theorem phq_lRp_ne_hqNf : lRp ≠ hqNf := by decide
@[simp] theorem phq_hqNf_ne_lRn : hqNf ≠ lRn := by decide
@[simp] theorem phq_lRn_ne_hqNf : lRn ≠ hqNf := by decide
@[simp] theorem phq_hqNf_ne_lFle : hqNf ≠ lFle := by decide
@[simp] theorem phq_lFle_ne_hqNf : lFle ≠ hqNf := by decide
@[simp] theorem phq_hqNf_ne_lKb : hqNf ≠ lKb := by decide
@[simp] theorem phq_lKb_ne_hqNf : lKb ≠ hqNf := by decide
@[simp] theorem phq_hqNf_ne_lDir : hqNf ≠ lDir := by decide
@[simp] theorem phq_lDir_ne_hqNf : lDir ≠ hqNf := by decide
@[simp] theorem phq_hqNf_ne_lFln : hqNf ≠ lFln := by decide
@[simp] theorem phq_lFln_ne_hqNf : lFln ≠ hqNf := by decide
@[simp] theorem phq_hqNf_ne_lFll : hqNf ≠ lFll := by decide
@[simp] theorem phq_lFll_ne_hqNf : lFll ≠ hqNf := by decide
@[simp] theorem phq_hqNf_ne_lFls : hqNf ≠ lFls := by decide
@[simp] theorem phq_lFls_ne_hqNf : lFls ≠ hqNf := by decide
@[simp] theorem phq_hqNf_ne_kFu : hqNf ≠ kFu := by decide
@[simp] theorem phq_kFu_ne_hqNf : kFu ≠ hqNf := by decide
@[simp] theorem phq_hqNf_ne_kD : hqNf ≠ kD := by decide
@[simp] theorem phq_kD_ne_hqNf : kD ≠ hqNf := by decide
@[simp] theorem phq_hqBp_ne_hqF : hqBp ≠ hqF := by decide
@[simp] theorem phq_hqBp_ne_hqH : hqBp ≠ hqH := by decide
@[simp] theorem phq_hqBp_ne_hqN : hqBp ≠ hqN := by decide
@[simp] theorem phq_hqBp_ne_hqU : hqBp ≠ hqU := by decide
@[simp] theorem phq_hqBp_ne_hqP : hqBp ≠ hqP := by decide
@[simp] theorem phq_hqBp_ne_hqQ : hqBp ≠ hqQ := by decide
@[simp] theorem phq_hqBp_ne_hqLp : hqBp ≠ hqLp := by decide
@[simp] theorem phq_hqBp_ne_hqLl : hqBp ≠ hqLl := by decide
@[simp] theorem phq_hqBp_ne_hqT : hqBp ≠ hqT := by decide
@[simp] theorem phq_hqBp_ne_hqW : hqBp ≠ hqW := by decide
@[simp] theorem phq_hqBp_ne_hqS : hqBp ≠ hqS := by decide
@[simp] theorem phq_hqBp_ne_hqN2 : hqBp ≠ hqN2 := by decide
@[simp] theorem phq_hqBp_ne_hqP2 : hqBp ≠ hqP2 := by decide
@[simp] theorem phq_hqBp_ne_hqI2 : hqBp ≠ hqI2 := by decide
@[simp] theorem phq_hqBp_ne_hqTb : hqBp ≠ hqTb := by decide
@[simp] theorem phq_hqBp_ne_hqTq : hqBp ≠ hqTq := by decide
@[simp] theorem phq_hqBp_ne_hqNf : hqBp ≠ hqNf := by decide
@[simp] theorem phq_hqBp_ne_hqBd : hqBp ≠ hqBd := by decide
@[simp] theorem phq_hqBp_ne_lFl : hqBp ≠ lFl := by decide
@[simp] theorem phq_lFl_ne_hqBp : lFl ≠ hqBp := by decide
@[simp] theorem phq_hqBp_ne_lDh : hqBp ≠ lDh := by decide
@[simp] theorem phq_lDh_ne_hqBp : lDh ≠ hqBp := by decide
@[simp] theorem phq_hqBp_ne_lDt : hqBp ≠ lDt := by decide
@[simp] theorem phq_lDt_ne_hqBp : lDt ≠ hqBp := by decide
@[simp] theorem phq_hqBp_ne_lDg : hqBp ≠ lDg := by decide
@[simp] theorem phq_lDg_ne_hqBp : lDg ≠ hqBp := by decide
@[simp] theorem phq_hqBp_ne_lDi : hqBp ≠ lDi := by decide
@[simp] theorem phq_lDi_ne_hqBp : lDi ≠ hqBp := by decide
@[simp] theorem phq_hqBp_ne_lRp : hqBp ≠ lRp := by decide
@[simp] theorem phq_lRp_ne_hqBp : lRp ≠ hqBp := by decide
@[simp] theorem phq_hqBp_ne_lRn : hqBp ≠ lRn := by decide
@[simp] theorem phq_lRn_ne_hqBp : lRn ≠ hqBp := by decide
@[simp] theorem phq_hqBp_ne_lFle : hqBp ≠ lFle := by decide
@[simp] theorem phq_lFle_ne_hqBp : lFle ≠ hqBp := by decide
@[simp] theorem phq_hqBp_ne_lKb : hqBp ≠ lKb := by decide
@[simp] theorem phq_lKb_ne_hqBp : lKb ≠ hqBp := by decide
@[simp] theorem phq_hqBp_ne_lDir : hqBp ≠ lDir := by decide
@[simp] theorem phq_lDir_ne_hqBp : lDir ≠ hqBp := by decide
@[simp] theorem phq_hqBp_ne_lFln : hqBp ≠ lFln := by decide
@[simp] theorem phq_lFln_ne_hqBp : lFln ≠ hqBp := by decide
@[simp] theorem phq_hqBp_ne_lFll : hqBp ≠ lFll := by decide
@[simp] theorem phq_lFll_ne_hqBp : lFll ≠ hqBp := by decide
@[simp] theorem phq_hqBp_ne_lFls : hqBp ≠ lFls := by decide
@[simp] theorem phq_lFls_ne_hqBp : lFls ≠ hqBp := by decide
@[simp] theorem phq_hqBp_ne_kFu : hqBp ≠ kFu := by decide
@[simp] theorem phq_kFu_ne_hqBp : kFu ≠ hqBp := by decide
@[simp] theorem phq_hqBp_ne_kD : hqBp ≠ kD := by decide
@[simp] theorem phq_kD_ne_hqBp : kD ≠ hqBp := by decide
@[simp] theorem phq_hqBd_ne_hqF : hqBd ≠ hqF := by decide
@[simp] theorem phq_hqBd_ne_hqH : hqBd ≠ hqH := by decide
@[simp] theorem phq_hqBd_ne_hqN : hqBd ≠ hqN := by decide
@[simp] theorem phq_hqBd_ne_hqU : hqBd ≠ hqU := by decide
@[simp] theorem phq_hqBd_ne_hqP : hqBd ≠ hqP := by decide
@[simp] theorem phq_hqBd_ne_hqQ : hqBd ≠ hqQ := by decide
@[simp] theorem phq_hqBd_ne_hqLp : hqBd ≠ hqLp := by decide
@[simp] theorem phq_hqBd_ne_hqLl : hqBd ≠ hqLl := by decide
@[simp] theorem phq_hqBd_ne_hqT : hqBd ≠ hqT := by decide
@[simp] theorem phq_hqBd_ne_hqW : hqBd ≠ hqW := by decide
@[simp] theorem phq_hqBd_ne_hqS : hqBd ≠ hqS := by decide
@[simp] theorem phq_hqBd_ne_hqN2 : hqBd ≠ hqN2 := by decide
@[simp] theorem phq_hqBd_ne_hqP2 : hqBd ≠ hqP2 := by decide
@[simp] theorem phq_hqBd_ne_hqI2 : hqBd ≠ hqI2 := by decide
@[simp] theorem phq_hqBd_ne_hqTb : hqBd ≠ hqTb := by decide
@[simp] theorem phq_hqBd_ne_hqTq : hqBd ≠ hqTq := by decide
@[simp] theorem phq_hqBd_ne_hqNf : hqBd ≠ hqNf := by decide
@[simp] theorem phq_hqBd_ne_hqBp : hqBd ≠ hqBp := by decide
@[simp] theorem phq_hqBd_ne_lFl : hqBd ≠ lFl := by decide
@[simp] theorem phq_lFl_ne_hqBd : lFl ≠ hqBd := by decide
@[simp] theorem phq_hqBd_ne_lDh : hqBd ≠ lDh := by decide
@[simp] theorem phq_lDh_ne_hqBd : lDh ≠ hqBd := by decide
@[simp] theorem phq_hqBd_ne_lDt : hqBd ≠ lDt := by decide
@[simp] theorem phq_lDt_ne_hqBd : lDt ≠ hqBd := by decide
@[simp] theorem phq_hqBd_ne_lDg : hqBd ≠ lDg := by decide
@[simp] theorem phq_lDg_ne_hqBd : lDg ≠ hqBd := by decide
@[simp] theorem phq_hqBd_ne_lDi : hqBd ≠ lDi := by decide
@[simp] theorem phq_lDi_ne_hqBd : lDi ≠ hqBd := by decide
@[simp] theorem phq_hqBd_ne_lRp : hqBd ≠ lRp := by decide
@[simp] theorem phq_lRp_ne_hqBd : lRp ≠ hqBd := by decide
@[simp] theorem phq_hqBd_ne_lRn : hqBd ≠ lRn := by decide
@[simp] theorem phq_lRn_ne_hqBd : lRn ≠ hqBd := by decide
@[simp] theorem phq_hqBd_ne_lFle : hqBd ≠ lFle := by decide
@[simp] theorem phq_lFle_ne_hqBd : lFle ≠ hqBd := by decide
@[simp] theorem phq_hqBd_ne_lKb : hqBd ≠ lKb := by decide
@[simp] theorem phq_lKb_ne_hqBd : lKb ≠ hqBd := by decide
@[simp] theorem phq_hqBd_ne_lDir : hqBd ≠ lDir := by decide
@[simp] theorem phq_lDir_ne_hqBd : lDir ≠ hqBd := by decide
@[simp] theorem phq_hqBd_ne_lFln : hqBd ≠ lFln := by decide
@[simp] theorem phq_lFln_ne_hqBd : lFln ≠ hqBd := by decide
@[simp] theorem phq_hqBd_ne_lFll : hqBd ≠ lFll := by decide
@[simp] theorem phq_lFll_ne_hqBd : lFll ≠ hqBd := by decide
@[simp] theorem phq_hqBd_ne_lFls : hqBd ≠ lFls := by decide
@[simp] theorem phq_lFls_ne_hqBd : lFls ≠ hqBd := by decide
@[simp] theorem phq_hqBd_ne_kFu : hqBd ≠ kFu := by decide
@[simp] theorem phq_kFu_ne_hqBd : kFu ≠ hqBd := by decide
@[simp] theorem phq_hqBd_ne_kD : hqBd ≠ kD := by decide
@[simp] theorem phq_kD_ne_hqBd : kD ≠ hqBd := by decide

def hqParams : List MlS := [hqF, hqH]
def hqLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, hqN, hqU, hqP, hqQ, hqLp, hqLl, hqT, hqW, hqS, hqN2, hqP2, hqI2, hqTb, hqTq, hqNf, hqBp, hqBd]
def hqBody (C : Ctx) : ProgHOL 64 := prologue hqLocals (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv hqH)) (.seq eViewP (.ite (.cmp .equal (vv lDg) (.const 3)) (.seq (.assign .local hqN (.load .one (vv lRp))) (.seq (.assign .local hqU (.load .one (.op .add [(vv lRp), (.const 8)]))) (envFindP C hqP (vv hqN) (.ite (.cmp .equal (vv hqP) (.const 0)) (.return (.const 0)) (.seq (.assign .local hqQ (.op .sub [(vv hqP), (.const 1)])) (.seq (.assign .local hqLp (.load .one (.op .add [(vv hqQ), (.const 16)]))) (.seq (.assign .local hqLl (.load .one (vv hqLp))) (.seq (.assign .local hqT (.load .one (.op .add [(vv hqQ), (.const 24)]))) (.seq (.assign .local lFl (vv lFls)) (.seq (.assign .local lDh (vv hqU)) (.seq lsViewP (.ite (.cmp .notEqual (vv lRn) (vv hqLl)) (.return (.const 0)) (.seq (.call (some (some (.local, hqW), none)) fTg [(vv hqF), (vv hqT), (vv hqT), (.const 0)]) (.ite (.cmp .equal (vv hqW) (.const 0)) (.return (.const 0)) (.seq (.call (some (some (.local, hqS), none)) fSa [(.op .add [(vv hqLp), (.const 8)]), (vv hqLl), (vv hqU), (vv hqW)]) (.return (vv hqS))))))))))))))))) (.ite (.cmp .equal (vv lDg) (.const 1)) (.seq (.assign .local hqT (.load .one (vv lRp))) (.seq (.call (some (some (.local, hqW), none)) fTg [(vv hqF), (vv hqT), (vv hqT), (.const 0)]) (.return (vv hqW)))) (.ite (.cmp .equal (vv lDg) (.const 2)) (.return (.const 1)) (.ite (.cmp .equal (vv lDg) (.const 6)) (.return (.const 1)) (.ite (.cmp .equal (vv lDg) (.const 8)) (.return (.const 1)) (.ite (.cmp .equal (vv lDg) (.const 9)) (projRead hqN2 hqP2 hqI2 (tblFindP C hqTb (vv hqN2) (.ite (.cmp .equal (vv hqTb) (.const 0)) (.return (.const 0)) (.seq (.assign .local hqTq (.op .sub [(vv hqTb), (.const 1)])) (.seq (.assign .local hqNf (.load .one (.op .add [(vv hqTq), (.const 32)]))) (.ite (.cmp .lower (vv hqI2) (vv hqNf)) (.seq (.assign .local hqBp (.load .one (.op .add [(vv hqTq), (.const 40)]))) (.seq (.assign .local hqBd (.load .one (.op .add [(.op .add [(vv hqBp), (.const 8)]), (.shift .lsl (vv hqI2) (.const 3))]))) (.seq (.call (some (some (.local, hqW), none)) fTg [(vv hqF), (vv hqBd), (vv hqBd), (.const 0)]) (.ite (.cmp .equal (vv hqW) (.const 1)) (.return (.const 1)) (.return (.const 0)))))) (.return (.const 0)))))))) (.return (.const 0)))))))))))

structure HqCodes (C : Ctx) : Prop where
  mg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  mp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  tg : C.code.lookup fTg = some (tgParams.map (fun p => (p, ShapeHOL.one)), tgBody C, .one)
  tgc : TgCodes C
  sa : SaCodesFull C

theorem pwEnc_store {C : Ctx} {H : List (BitVec 64)} {s s' : AState} (e : s'.store = s.store) {pw w} :
    pwEnc C H s pw w → pwEnc C H s' pw w := by
  cases pw <;> simp [pwEnc, e]

theorem optPW_store {C : Ctx} {H : List (BitVec 64)} {s s' : AState} (e : s'.store = s.store) {r w} :
    optPW C H s' r w → optPW C H s r w := by
  cases r with
  | none => exact id
  | some pw => exact pwEnc_store e.symm

theorem rdStep_trans {s1 s2 s3 : AState} (h1 : RdStep s1 s2) (h2 : RdStep s2 s3) : RdStep s1 s3 :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, mirrorEq_trans h2.2.2.2.1 h1.2.2.2.1, h2.2.2.2.2⟩

section
variable {σ : Type}

theorem hq_spec (C : Ctx) (hok : CtxOK C) (hc : HqCodes C) (fuel : Nat) (hf : fuel < 2 ^ 61) (s : AState)
    (hwf : LStoreWF s.store.ls) (hrd : RdOK s)
    (hSD : ∀ h u, s.store.view h = some (.sort u) → ∃ l, denoteL s.store.ls u = some l)
    (hLP : ∀ c ci, C.fe.find? c = some ci → ∃ ks, Frontend.denoteNList s.store.ns ci.toConstantVal.levelParams = some ks)
    (hLPl : ∀ c ci, C.fe.find? c = some ci → ci.toConstantVal.levelParams.length < 2 ^ 60)
    (hLS : ∀ us uh, s.store.lss.view us = some uh → ∃ vs, denoteLs s.store.lss us = some vs ∧ ∃ hl : vs.length = uh.length,
      ∀ j (hj : j < uh.length), denoteL s.store.ls uh[j] = some (vs[j]'(by rw [hl]; exact hj)))
    (hTB : ∀ T tb, C.fe.findTable? T = some tb → tb.bodies.size = tb.numFields) :
    ∀ (H : List (BitVec 64)) (h : EIdx), C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (hqParams.zip [BitVec.ofNat 64 fuel, Enc.idxW h])) (hqBody C) s
        (headProofPW C.fe fuel h) (PostSA (ctxH C H) s) := by
  intro H h hpH
  refine specR_prologue (postSA_locals _ s) (Knot.params_none _ hqLocals hqParams _ (by decide) (by decide)) ?_
  unfold headProofPW
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv hqH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, hqParams, ctxEnv]) ?_
  refine specR_viewP (C := ctxH C H) h (by simp) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
    (fun v P hv htn hl => ?_)
  refine specR_congr (Big.view_bind_eq h v _ s hv) ?_
  rcases v with i | ⟨i, ty⟩ | u1 | ⟨c, us⟩ | ⟨f1, x1⟩ | ⟨t1, b1⟩ | ⟨t1, b1⟩ | ⟨t1, v1, b1⟩ | l1 | ⟨sn, pi, pe⟩
  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rdStep_refl hrd, H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    refine specR_loadI' hqT (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encFVar] using wordsAt_mem0 P (Enc.idxW ty) (limbs i) []) ?_
    refine specR_dropM ?_
    unfold typeSortPW
    refine specR_congr (m' := typeSortPWGo C.fe ty fuel ty 0 >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H) hqW fTg tgParams [vv hqF, vv hqT, vv hqT, .const 0] (tgBody C)
      [BitVec.ofNat 64 fuel, Enc.idxW ty, Enc.idxW ty, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.tg
      ⟨by simp +decide [Env.get, hqParams, ctxEnv], by simp, by simp, rfl, trivial⟩
      (PostSA (ctxH C H) s) (fun r_ w s' H' => RdStep s s' ∧ optPW C H' s r_ w)
      (fun r_ w s' st ⟨hst, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hst, hw⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tgParams _ rfl hlk)
        (tg_spec C hok hc.tgc s hwf hrd hSD hLP hLPl hLS fuel ty ty 0 H hpH (by omega) (by omega)))
      (fun r w1 s1 H1 hp1 ⟨hst1, hw1⟩ => ?_)
    exact specR_returnI _ w1 (by simp) (fun t ht => ⟨hst1, H1, hp1, hw1, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact specR_returnI _ 1 rfl (fun t ht => ⟨rdStep_refl hrd, H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

  · refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    refine specR_loadI' hqN (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW c) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW c) [Enc.idxW us] []) ?_
    refine specR_loadI' hqU _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW us) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW c) (Enc.idxW us) [] []) ?_
    refine specR_envFindI (C := ctxH C H) (ctxOK_H hok H) hc.mg hc.mp hqP (vv hqN) c (by decide) (by simp) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    have hrel := find_rel hok c
    try rw [show (ctxH C H).envM = C.envM from rfl]
    revert hrel
    rcases hfind : C.fe.find? c with _ | ci
    · intro hrel; simp only at hrel; rw [hrel]
      refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ 0 rfl (fun t ht => ⟨rdStep_refl hrd, H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    intro ⟨o, hm, hci⟩
    rw [hm]
    refine specR_atEntry fun t ht => ?_
    have hoE : o < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
    refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI hqQ _ (ecell C o) (by decide) (by simp [sev, optWG]; exact BitVec.add_sub_cancel _ _) ?_
    obtain ⟨_, ⟨wl, hwl, ol, hwl', hbl⟩, hty⟩ := hci.1
    refine specR_envLoadI hqLp (.op .add [vv hqQ, .const 16]) (o + 2) _ (by decide)
      (by simp +decide [sev, Env.get, hqParams, ctxEnv, ecell_ctxH]; exact UD.ecell_add16 C o)
      (by rw [show o + 2 = o + 1 + 1 by omega]; exact hwl) ?_
    refine specR_envLoadI hqLl (vv hqLp) ol _ (by decide) (by simp [hwl']; rfl) hbl.1 ?_
    refine specR_envLoadI hqT (.op .add [vv hqQ, .const 24]) (o + 3) _ (by decide)
      (by simp +decide [sev, Env.get, hqParams, ctxEnv, ecell_ctxH]; simpa using ecell_add C o 3)
      (by rw [show o + 3 = o + 1 + 2 by omega]; exact hty) ?_
    have hlp : ci.toConstantVal.levelParams.length < 2 ^ 60 := hLPl c ci hfind
    refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv hqU) (Enc.idxW us) (by decide) (by simp) ?_
    refine specR_lsviewPI (C := ctxH C H) us (by simp) (by simp <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
      (fun vl Pl hvl _ hvll => ?_)
    refine specR_runBind (viewLsLen_run us s vl hvl) ?_
    dsimp only
    simp only [List.length_map]
    by_cases hlen : vl.length = ci.toConstantVal.levelParams.length
    swap
    · have hne : BitVec.ofNat 64 vl.length ≠ BitVec.ofNat 64 ci.toConstantVal.levelParams.length := by
        have : vl.length < 2 ^ 61 := by simpa using hvll
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun _ => ?_) (fun h => absurd h (by decide))
      rw [if_neg hlen]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨rdStep_refl hrd, H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlen]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [if_pos hlen]
    unfold typeSortPW
    refine specR_callNIH (C := ctxH C H) hqW fTg tgParams [vv hqF, vv hqT, vv hqT, .const 0] (tgBody C)
      [BitVec.ofNat 64 fuel, Enc.idxW ci.toConstantVal.type, Enc.idxW ci.toConstantVal.type, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.tg
      ⟨by simp +decide [Env.get, hqParams, ctxEnv], by simp, by simp, rfl, trivial⟩
      (PostSA (ctxH C H) s) (fun r_ w s' H' => RdStep s s' ∧ optPW C H' s r_ w)
      (fun r_ w s' st ⟨hst, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hst, hw⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tgParams _ rfl hlk)
        (tg_spec C hok hc.tgc s hwf hrd hSD hLP hLPl hLS fuel ci.toConstantVal.type ci.toConstantVal.type 0 H hpH (by omega) (by omega)))
      (fun r w1 s1 H1 hp1 ⟨hst1, hw1⟩ => ?_)
    rcases r with _ | pw
    · simp only [optPW] at hw1; subst hw1
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      try dsimp only
      exact specR_returnI _ 0 rfl (fun t ht => ⟨hst1, H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    simp only [optPW] at hw1
    refine specR_atEntry fun t ht => ?_
    have hw0 : w1 ≠ 0 := by
      cases pw with
      | never => simp only [pwEnc] at hw1; subst hw1; decide
      | ifAllZero ps => obtain ⟨o', ns, rfl, hb', _⟩ := hw1; exact (cellA_big hok ht.sr (blkAt_lt hb')).1
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hw0) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    have e1 : s1.store = s.store := hst1.1
    obtain ⟨ks, hks⟩ := hLP c ci hfind
    obtain ⟨vs, hdl, hvl2, hvd⟩ := hLS us vl hvl
    refine specR_congr (m' := substPWAt ci.toConstantVal.levelParams us pw >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H1) hqS fSa saParams [.op .add [vv hqLp, .const 8], vv hqLl, vv hqU, vv hqW] (saBody C)
      [ecell C (ol + 1), BitVec.ofNat 64 ci.toConstantVal.levelParams.length, Enc.idxW us, w1] (by decide) rfl (by decide) hc.sa.self
      ⟨by simp [sev, hwl']; show ecell C ol + BitVec.ofNat 64 (8 * 1) = _; exact ecell_add C ol 1, by simp, by simp, by simp, trivial⟩
      (PostSA (ctxH C H1) s1) (fun r_ w s' H' => RdStep s1 s' ∧ optPW C H' s1 r_ w)
      (fun r_ w s' st ⟨hst, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hst, hw⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu saParams _ rfl hlk)
        (sa_spec C hok hc.sa.codes s1 (by rw [e1]; exact hwf) hst1.2.2.2.2 ci.toConstantVal.levelParams ks (ol + 1)
          (fun j hj => by have := hbl.2 j (by simpa using hj); simp only [List.getElem_map] at this; exact this)
          (LSub.denoteNList_get _ _ _ hks).1 (by rw [e1]; exact hks) hlp us vl vs (by rw [e1]; exact hvl) hvl2
          (by rw [e1]; exact hvd) (by simpa using hvll) (by rw [e1]; exact hdl) H1 pw w1
          (hpH.trans hp1) (pwEnc_store e1 hw1)))
      (fun r w3 s3 H3 hp3 ⟨hst3, hw3⟩ => ?_)
    exact specR_returnI _ w3 (by simp) (fun t ht => ⟨rdStep_trans hst1 hst3, H3, hp1.trans hp3, optPW_store hst1.1 hw3,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)

  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rdStep_refl hrd, H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rdStep_refl hrd, H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact specR_returnI _ 1 rfl (fun t ht => ⟨rdStep_refl hrd, H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    try dsimp only
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rdStep_refl hrd, H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    exact specR_returnI _ 1 rfl (fun t ht => ⟨rdStep_refl hrd, H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

  · refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp [sev, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    refine specR_projReadI hqN2 hqP2 hqI2 sn pi pe P (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by simp) (by simp) hl (fun hi => ?_)
    refine specR_dropM ?_
    refine specR_tblFindI (C := ctxH C H) (ctxOK_H hok H) hc.mg hc.mp hqTb (vv hqN2) sn (by decide)
      (by simp) (by simp +decide [Env.get, hqParams, ctxEnv] <;> rfl) ?_
    have hrel := tbl_rel hok sn
    unfold IFEnv.findProj?
    try rw [show (ctxH C H).tblM = C.tblM from rfl]
    revert hrel
    rcases hft : C.fe.findTable? sn with _ | tb
    · intro hrel; simp only at hrel; rw [hrel]
      refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ 0 rfl (fun t ht => ⟨rdStep_refl hrd, H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    intro ⟨ot, hmt, htb⟩
    rw [hmt]
    dsimp only
    refine specR_atEntry fun t ht => ?_
    have hoT : ot < C.EN := Nat.lt_of_lt_of_le (tblE_lt htb) ht.sr.env.1.len
    have hEN : C.EH.length ≤ C.EN := ht.sr.env.1.len
    have hEL := hok.envLay
    refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoT) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI hqTq _ (ecell C ot) (by decide) (by simp [sev, optWG]; exact BitVec.add_sub_cancel _ _) ?_
    obtain ⟨_, _, _, _, ⟨hnf, hnfl⟩, ⟨wb, hwb, ob, hwb', hbb⟩⟩ := htb
    refine specR_envLoadI hqNf (.op .add [vv hqTq, .const 32]) (ot + 4) _ (by decide)
      (by simp [sev, vv, ecell_ctxH]; simpa using ecell_add C ot 4) hnf ?_
    have hlw : BitVec.ofNat 64 pi < BitVec.ofNat 64 tb.numFields ↔ pi < tb.numFields := by
      rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt (by omega)]
    by_cases hin : pi < tb.numFields
    swap
    · refine specR_ifI _ 0 (by simp +decide [sev, Env.get, hqParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw, hin]) (fun h => absurd rfl h) (fun _ => ?_)
      rw [if_neg hin]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨rdStep_refl hrd, H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, hqParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw, hin]) (fun _ => ?_) (fun h => absurd h (by decide))
    rw [if_pos hin]
    dsimp only
    refine specR_envLoadI hqBp (.op .add [vv hqTq, .const 40]) (ot + 5) _ (by decide)
      (by simp [sev, vv, ecell_ctxH]; simpa using ecell_add C ot 5) hwb ?_
    have hbs : pi < tb.bodies.toList.length := by rw [Array.length_toList, hTB sn tb hft]; exact hin
    have hel := hbb.2 pi (by simpa using hbs)
    simp only [List.getElem_map] at hel
    have hlb : tb.bodies.toList.length < 2 ^ 61 := by
      have h1 := blkAt_len (show BlkAt C.EH ob (tb.bodies.toList.map Enc.idxW) from hbb)
      simp only [List.length_map] at h1; omega
    refine specR_envLoadI hqBd _ (ob + 1 + pi) _ (by decide)
      (by simp +decide [sev, Env.get, hqParams, ctxEnv, hwb']; show _ = ecell C (ob + 1 + pi)
          rw [← ecell_shl3 C (ob + 1) pi (by omega), ← ecell_add C ob 1]; simp [ecell]) hel ?_
    have hget : (tb.entry pi).body = tb.bodies.toList[pi] := by
      have hbs' : pi < tb.bodies.size := by simpa using hbs
      simp only [IProjTable.entry, Array.getD]; rw [dif_pos hbs']; simp
    rw [hget]
    unfold typeSortPW
    refine specR_callNIH (C := ctxH C H) hqW fTg tgParams [vv hqF, vv hqBd, vv hqBd, .const 0] (tgBody C)
      [BitVec.ofNat 64 fuel, Enc.idxW tb.bodies.toList[pi], Enc.idxW tb.bodies.toList[pi], BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.tg
      ⟨by simp +decide [Env.get, hqParams, ctxEnv], by simp, by simp, rfl, trivial⟩
      (PostSA (ctxH C H) s) (fun r_ w s' H' => RdStep s s' ∧ optPW C H' s r_ w)
      (fun r_ w s' st ⟨hst, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hst, hw⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tgParams _ rfl hlk)
        (tg_spec C hok hc.tgc s hwf hrd hSD hLP hLPl hLS fuel tb.bodies.toList[pi] tb.bodies.toList[pi] 0 H hpH (by omega) (by omega)))
      (fun r w1 s1 H1 hp1 ⟨hst1, hw1⟩ => ?_)
    refine specR_atEntry fun t ht => ?_
    rcases r with _ | pw
    · simp only [optPW] at hw1; subst hw1
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      try dsimp only
      exact specR_returnI _ 0 rfl (fun t ht => ⟨hst1, H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    simp only [optPW] at hw1
    cases pw with
    | never =>
      simp only [pwEnc] at hw1; subst hw1
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      try dsimp only
      exact specR_returnI _ 1 rfl (fun t ht => ⟨hst1, H1, hp1, by simp [ConLeche.PropWhen.isNever, optPW, pwEnc], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | ifAllZero ps =>
      obtain ⟨o', ns, rfl, hb', _⟩ := hw1
      have hbig := cellA_big hok ht.sr (blkAt_lt hb')
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hbig.2.1) (fun h => absurd rfl h) (fun _ => ?_)
      try dsimp only
      exact specR_returnI _ 0 rfl (fun t ht => ⟨hst1, H1, hp1, by simp [ConLeche.PropWhen.isNever, optPW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)


end

end ConPanqueque.T.WC
