import ConPanqueque.T.Core.NumArgs
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# The constructor shortcut's readers and `nuNeutral`

`nuNeutral` (the spine head neither a λ, a `let` nor a bound variable), `ctorHeadAgainst` (a head normal form
against a constructor: `obW`), `ctorTarget` (a closed, fully applied constructor of a never-`Prop`, η-less,
non-`Nat` family: `optWG idxW`), `ctorTargetFor` (its gate; the eager flag is static).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def nuE := ofString "nun_e"
def nuH := ofString "nun_h"
def chC := ofString "chn_c"
def chW := ofString "chn_w"
def chH := ofString "chn_h"
def chD := ofString "chn_d"
def chP := ofString "chn_p"
def chQ := ofString "chn_q"
def chK := ofString "chn_k"
def cqE := ofString "cqn_e"
def cqX := ofString "cqn_x"
def cqH := ofString "cqn_h"
def cqC := ofString "cqn_c"
def cqP := ofString "cqn_p"
def cqQ := ofString "cqn_q"
def cqK := ofString "cqn_k"
def cqNp := ofString "cqn_np"
def cqNf := ofString "cqn_nf"
def cqT := ofString "cqn_t"
def cqNn := ofString "cqn_nn"
def cqN := ofString "cqn_n"
def cqP2 := ofString "cqn_p2"
def cqQ2 := ofString "cqn_q2"
def cqK2 := ofString "cqn_k2"
def cqZ := ofString "cqn_z"
def cqEt := ofString "cqn_et"
def cfO := ofString "cfn_o"
def cfE := ofString "cfn_e"
def cfX := ofString "cfn_x"
def cfR := ofString "cfn_r"
def fNu := ofString "nuNeutral"
def fCh := ofString "ctorHeadAgainst"
def fCq := ofString "ctorTarget"
def fCf := ofString "ctorTargetFor"

@[simp] theorem ctg_nuE_ne_ioH : nuE ≠ nuH := by decide
@[simp] theorem ctg_nuE_ne_lFl : nuE ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_ioE : lFl ≠ nuE := by decide
@[simp] theorem ctg_nuE_ne_lDh : nuE ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_ioE : lDh ≠ nuE := by decide
@[simp] theorem ctg_nuE_ne_lDt : nuE ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_ioE : lDt ≠ nuE := by decide
@[simp] theorem ctg_nuE_ne_lDg : nuE ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_ioE : lDg ≠ nuE := by decide
@[simp] theorem ctg_nuE_ne_lDi : nuE ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_ioE : lDi ≠ nuE := by decide
@[simp] theorem ctg_nuE_ne_lRp : nuE ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_ioE : lRp ≠ nuE := by decide
@[simp] theorem ctg_nuE_ne_lRn : nuE ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_ioE : lRn ≠ nuE := by decide
@[simp] theorem ctg_nuE_ne_lDir : nuE ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_ioE : lDir ≠ nuE := by decide
@[simp] theorem ctg_nuE_ne_lFle : nuE ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_ioE : lFle ≠ nuE := by decide
@[simp] theorem ctg_nuE_ne_lKb : nuE ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_ioE : lKb ≠ nuE := by decide
@[simp] theorem ctg_nuH_ne_ioE : nuH ≠ nuE := by decide
@[simp] theorem ctg_nuH_ne_lFl : nuH ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_ioH : lFl ≠ nuH := by decide
@[simp] theorem ctg_nuH_ne_lDh : nuH ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_ioH : lDh ≠ nuH := by decide
@[simp] theorem ctg_nuH_ne_lDt : nuH ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_ioH : lDt ≠ nuH := by decide
@[simp] theorem ctg_nuH_ne_lDg : nuH ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_ioH : lDg ≠ nuH := by decide
@[simp] theorem ctg_nuH_ne_lDi : nuH ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_ioH : lDi ≠ nuH := by decide
@[simp] theorem ctg_nuH_ne_lRp : nuH ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_ioH : lRp ≠ nuH := by decide
@[simp] theorem ctg_nuH_ne_lRn : nuH ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_ioH : lRn ≠ nuH := by decide
@[simp] theorem ctg_nuH_ne_lDir : nuH ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_ioH : lDir ≠ nuH := by decide
@[simp] theorem ctg_nuH_ne_lFle : nuH ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_ioH : lFle ≠ nuH := by decide
@[simp] theorem ctg_nuH_ne_lKb : nuH ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_ioH : lKb ≠ nuH := by decide
@[simp] theorem ctg_chC_ne_chW : chC ≠ chW := by decide
@[simp] theorem ctg_chC_ne_chH : chC ≠ chH := by decide
@[simp] theorem ctg_chC_ne_chD : chC ≠ chD := by decide
@[simp] theorem ctg_chC_ne_chP : chC ≠ chP := by decide
@[simp] theorem ctg_chC_ne_chQ : chC ≠ chQ := by decide
@[simp] theorem ctg_chC_ne_chK : chC ≠ chK := by decide
@[simp] theorem ctg_chC_ne_lFl : chC ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_chC : lFl ≠ chC := by decide
@[simp] theorem ctg_chC_ne_lDh : chC ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_chC : lDh ≠ chC := by decide
@[simp] theorem ctg_chC_ne_lDt : chC ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_chC : lDt ≠ chC := by decide
@[simp] theorem ctg_chC_ne_lDg : chC ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_chC : lDg ≠ chC := by decide
@[simp] theorem ctg_chC_ne_lDi : chC ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_chC : lDi ≠ chC := by decide
@[simp] theorem ctg_chC_ne_lRp : chC ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_chC : lRp ≠ chC := by decide
@[simp] theorem ctg_chC_ne_lRn : chC ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_chC : lRn ≠ chC := by decide
@[simp] theorem ctg_chC_ne_lDir : chC ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_chC : lDir ≠ chC := by decide
@[simp] theorem ctg_chC_ne_lFle : chC ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_chC : lFle ≠ chC := by decide
@[simp] theorem ctg_chC_ne_lKb : chC ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_chC : lKb ≠ chC := by decide
@[simp] theorem ctg_chW_ne_chC : chW ≠ chC := by decide
@[simp] theorem ctg_chW_ne_chH : chW ≠ chH := by decide
@[simp] theorem ctg_chW_ne_chD : chW ≠ chD := by decide
@[simp] theorem ctg_chW_ne_chP : chW ≠ chP := by decide
@[simp] theorem ctg_chW_ne_chQ : chW ≠ chQ := by decide
@[simp] theorem ctg_chW_ne_chK : chW ≠ chK := by decide
@[simp] theorem ctg_chW_ne_lFl : chW ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_chW : lFl ≠ chW := by decide
@[simp] theorem ctg_chW_ne_lDh : chW ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_chW : lDh ≠ chW := by decide
@[simp] theorem ctg_chW_ne_lDt : chW ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_chW : lDt ≠ chW := by decide
@[simp] theorem ctg_chW_ne_lDg : chW ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_chW : lDg ≠ chW := by decide
@[simp] theorem ctg_chW_ne_lDi : chW ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_chW : lDi ≠ chW := by decide
@[simp] theorem ctg_chW_ne_lRp : chW ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_chW : lRp ≠ chW := by decide
@[simp] theorem ctg_chW_ne_lRn : chW ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_chW : lRn ≠ chW := by decide
@[simp] theorem ctg_chW_ne_lDir : chW ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_chW : lDir ≠ chW := by decide
@[simp] theorem ctg_chW_ne_lFle : chW ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_chW : lFle ≠ chW := by decide
@[simp] theorem ctg_chW_ne_lKb : chW ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_chW : lKb ≠ chW := by decide
@[simp] theorem ctg_chH_ne_chC : chH ≠ chC := by decide
@[simp] theorem ctg_chH_ne_chW : chH ≠ chW := by decide
@[simp] theorem ctg_chH_ne_chD : chH ≠ chD := by decide
@[simp] theorem ctg_chH_ne_chP : chH ≠ chP := by decide
@[simp] theorem ctg_chH_ne_chQ : chH ≠ chQ := by decide
@[simp] theorem ctg_chH_ne_chK : chH ≠ chK := by decide
@[simp] theorem ctg_chH_ne_lFl : chH ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_chH : lFl ≠ chH := by decide
@[simp] theorem ctg_chH_ne_lDh : chH ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_chH : lDh ≠ chH := by decide
@[simp] theorem ctg_chH_ne_lDt : chH ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_chH : lDt ≠ chH := by decide
@[simp] theorem ctg_chH_ne_lDg : chH ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_chH : lDg ≠ chH := by decide
@[simp] theorem ctg_chH_ne_lDi : chH ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_chH : lDi ≠ chH := by decide
@[simp] theorem ctg_chH_ne_lRp : chH ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_chH : lRp ≠ chH := by decide
@[simp] theorem ctg_chH_ne_lRn : chH ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_chH : lRn ≠ chH := by decide
@[simp] theorem ctg_chH_ne_lDir : chH ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_chH : lDir ≠ chH := by decide
@[simp] theorem ctg_chH_ne_lFle : chH ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_chH : lFle ≠ chH := by decide
@[simp] theorem ctg_chH_ne_lKb : chH ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_chH : lKb ≠ chH := by decide
@[simp] theorem ctg_chD_ne_chC : chD ≠ chC := by decide
@[simp] theorem ctg_chD_ne_chW : chD ≠ chW := by decide
@[simp] theorem ctg_chD_ne_chH : chD ≠ chH := by decide
@[simp] theorem ctg_chD_ne_chP : chD ≠ chP := by decide
@[simp] theorem ctg_chD_ne_chQ : chD ≠ chQ := by decide
@[simp] theorem ctg_chD_ne_chK : chD ≠ chK := by decide
@[simp] theorem ctg_chD_ne_lFl : chD ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_chD : lFl ≠ chD := by decide
@[simp] theorem ctg_chD_ne_lDh : chD ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_chD : lDh ≠ chD := by decide
@[simp] theorem ctg_chD_ne_lDt : chD ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_chD : lDt ≠ chD := by decide
@[simp] theorem ctg_chD_ne_lDg : chD ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_chD : lDg ≠ chD := by decide
@[simp] theorem ctg_chD_ne_lDi : chD ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_chD : lDi ≠ chD := by decide
@[simp] theorem ctg_chD_ne_lRp : chD ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_chD : lRp ≠ chD := by decide
@[simp] theorem ctg_chD_ne_lRn : chD ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_chD : lRn ≠ chD := by decide
@[simp] theorem ctg_chD_ne_lDir : chD ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_chD : lDir ≠ chD := by decide
@[simp] theorem ctg_chD_ne_lFle : chD ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_chD : lFle ≠ chD := by decide
@[simp] theorem ctg_chD_ne_lKb : chD ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_chD : lKb ≠ chD := by decide
@[simp] theorem ctg_chP_ne_chC : chP ≠ chC := by decide
@[simp] theorem ctg_chP_ne_chW : chP ≠ chW := by decide
@[simp] theorem ctg_chP_ne_chH : chP ≠ chH := by decide
@[simp] theorem ctg_chP_ne_chD : chP ≠ chD := by decide
@[simp] theorem ctg_chP_ne_chQ : chP ≠ chQ := by decide
@[simp] theorem ctg_chP_ne_chK : chP ≠ chK := by decide
@[simp] theorem ctg_chP_ne_lFl : chP ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_chP : lFl ≠ chP := by decide
@[simp] theorem ctg_chP_ne_lDh : chP ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_chP : lDh ≠ chP := by decide
@[simp] theorem ctg_chP_ne_lDt : chP ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_chP : lDt ≠ chP := by decide
@[simp] theorem ctg_chP_ne_lDg : chP ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_chP : lDg ≠ chP := by decide
@[simp] theorem ctg_chP_ne_lDi : chP ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_chP : lDi ≠ chP := by decide
@[simp] theorem ctg_chP_ne_lRp : chP ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_chP : lRp ≠ chP := by decide
@[simp] theorem ctg_chP_ne_lRn : chP ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_chP : lRn ≠ chP := by decide
@[simp] theorem ctg_chP_ne_lDir : chP ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_chP : lDir ≠ chP := by decide
@[simp] theorem ctg_chP_ne_lFle : chP ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_chP : lFle ≠ chP := by decide
@[simp] theorem ctg_chP_ne_lKb : chP ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_chP : lKb ≠ chP := by decide
@[simp] theorem ctg_chQ_ne_chC : chQ ≠ chC := by decide
@[simp] theorem ctg_chQ_ne_chW : chQ ≠ chW := by decide
@[simp] theorem ctg_chQ_ne_chH : chQ ≠ chH := by decide
@[simp] theorem ctg_chQ_ne_chD : chQ ≠ chD := by decide
@[simp] theorem ctg_chQ_ne_chP : chQ ≠ chP := by decide
@[simp] theorem ctg_chQ_ne_chK : chQ ≠ chK := by decide
@[simp] theorem ctg_chQ_ne_lFl : chQ ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_chQ : lFl ≠ chQ := by decide
@[simp] theorem ctg_chQ_ne_lDh : chQ ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_chQ : lDh ≠ chQ := by decide
@[simp] theorem ctg_chQ_ne_lDt : chQ ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_chQ : lDt ≠ chQ := by decide
@[simp] theorem ctg_chQ_ne_lDg : chQ ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_chQ : lDg ≠ chQ := by decide
@[simp] theorem ctg_chQ_ne_lDi : chQ ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_chQ : lDi ≠ chQ := by decide
@[simp] theorem ctg_chQ_ne_lRp : chQ ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_chQ : lRp ≠ chQ := by decide
@[simp] theorem ctg_chQ_ne_lRn : chQ ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_chQ : lRn ≠ chQ := by decide
@[simp] theorem ctg_chQ_ne_lDir : chQ ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_chQ : lDir ≠ chQ := by decide
@[simp] theorem ctg_chQ_ne_lFle : chQ ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_chQ : lFle ≠ chQ := by decide
@[simp] theorem ctg_chQ_ne_lKb : chQ ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_chQ : lKb ≠ chQ := by decide
@[simp] theorem ctg_chK_ne_chC : chK ≠ chC := by decide
@[simp] theorem ctg_chK_ne_chW : chK ≠ chW := by decide
@[simp] theorem ctg_chK_ne_chH : chK ≠ chH := by decide
@[simp] theorem ctg_chK_ne_chD : chK ≠ chD := by decide
@[simp] theorem ctg_chK_ne_chP : chK ≠ chP := by decide
@[simp] theorem ctg_chK_ne_chQ : chK ≠ chQ := by decide
@[simp] theorem ctg_chK_ne_lFl : chK ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_chK : lFl ≠ chK := by decide
@[simp] theorem ctg_chK_ne_lDh : chK ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_chK : lDh ≠ chK := by decide
@[simp] theorem ctg_chK_ne_lDt : chK ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_chK : lDt ≠ chK := by decide
@[simp] theorem ctg_chK_ne_lDg : chK ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_chK : lDg ≠ chK := by decide
@[simp] theorem ctg_chK_ne_lDi : chK ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_chK : lDi ≠ chK := by decide
@[simp] theorem ctg_chK_ne_lRp : chK ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_chK : lRp ≠ chK := by decide
@[simp] theorem ctg_chK_ne_lRn : chK ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_chK : lRn ≠ chK := by decide
@[simp] theorem ctg_chK_ne_lDir : chK ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_chK : lDir ≠ chK := by decide
@[simp] theorem ctg_chK_ne_lFle : chK ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_chK : lFle ≠ chK := by decide
@[simp] theorem ctg_chK_ne_lKb : chK ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_chK : lKb ≠ chK := by decide
@[simp] theorem ctg_cqE_ne_cqX : cqE ≠ cqX := by decide
@[simp] theorem ctg_cqE_ne_cqH : cqE ≠ cqH := by decide
@[simp] theorem ctg_cqE_ne_cqC : cqE ≠ cqC := by decide
@[simp] theorem ctg_cqE_ne_cqP : cqE ≠ cqP := by decide
@[simp] theorem ctg_cqE_ne_cqQ : cqE ≠ cqQ := by decide
@[simp] theorem ctg_cqE_ne_cqK : cqE ≠ cqK := by decide
@[simp] theorem ctg_cqE_ne_cqNp : cqE ≠ cqNp := by decide
@[simp] theorem ctg_cqE_ne_cqNf : cqE ≠ cqNf := by decide
@[simp] theorem ctg_cqE_ne_cqT : cqE ≠ cqT := by decide
@[simp] theorem ctg_cqE_ne_cqNn : cqE ≠ cqNn := by decide
@[simp] theorem ctg_cqE_ne_cqN : cqE ≠ cqN := by decide
@[simp] theorem ctg_cqE_ne_cqP2 : cqE ≠ cqP2 := by decide
@[simp] theorem ctg_cqE_ne_cqQ2 : cqE ≠ cqQ2 := by decide
@[simp] theorem ctg_cqE_ne_cqK2 : cqE ≠ cqK2 := by decide
@[simp] theorem ctg_cqE_ne_cqZ : cqE ≠ cqZ := by decide
@[simp] theorem ctg_cqE_ne_cqEt : cqE ≠ cqEt := by decide
@[simp] theorem ctg_cqE_ne_lFl : cqE ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_cqE : lFl ≠ cqE := by decide
@[simp] theorem ctg_cqE_ne_lDh : cqE ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_cqE : lDh ≠ cqE := by decide
@[simp] theorem ctg_cqE_ne_lDt : cqE ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_cqE : lDt ≠ cqE := by decide
@[simp] theorem ctg_cqE_ne_lDg : cqE ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_cqE : lDg ≠ cqE := by decide
@[simp] theorem ctg_cqE_ne_lDi : cqE ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_cqE : lDi ≠ cqE := by decide
@[simp] theorem ctg_cqE_ne_lRp : cqE ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_cqE : lRp ≠ cqE := by decide
@[simp] theorem ctg_cqE_ne_lRn : cqE ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_cqE : lRn ≠ cqE := by decide
@[simp] theorem ctg_cqE_ne_lDir : cqE ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_cqE : lDir ≠ cqE := by decide
@[simp] theorem ctg_cqE_ne_lFle : cqE ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_cqE : lFle ≠ cqE := by decide
@[simp] theorem ctg_cqE_ne_lKb : cqE ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_cqE : lKb ≠ cqE := by decide
@[simp] theorem ctg_cqX_ne_cqE : cqX ≠ cqE := by decide
@[simp] theorem ctg_cqX_ne_cqH : cqX ≠ cqH := by decide
@[simp] theorem ctg_cqX_ne_cqC : cqX ≠ cqC := by decide
@[simp] theorem ctg_cqX_ne_cqP : cqX ≠ cqP := by decide
@[simp] theorem ctg_cqX_ne_cqQ : cqX ≠ cqQ := by decide
@[simp] theorem ctg_cqX_ne_cqK : cqX ≠ cqK := by decide
@[simp] theorem ctg_cqX_ne_cqNp : cqX ≠ cqNp := by decide
@[simp] theorem ctg_cqX_ne_cqNf : cqX ≠ cqNf := by decide
@[simp] theorem ctg_cqX_ne_cqT : cqX ≠ cqT := by decide
@[simp] theorem ctg_cqX_ne_cqNn : cqX ≠ cqNn := by decide
@[simp] theorem ctg_cqX_ne_cqN : cqX ≠ cqN := by decide
@[simp] theorem ctg_cqX_ne_cqP2 : cqX ≠ cqP2 := by decide
@[simp] theorem ctg_cqX_ne_cqQ2 : cqX ≠ cqQ2 := by decide
@[simp] theorem ctg_cqX_ne_cqK2 : cqX ≠ cqK2 := by decide
@[simp] theorem ctg_cqX_ne_cqZ : cqX ≠ cqZ := by decide
@[simp] theorem ctg_cqX_ne_cqEt : cqX ≠ cqEt := by decide
@[simp] theorem ctg_cqX_ne_lFl : cqX ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_cqX : lFl ≠ cqX := by decide
@[simp] theorem ctg_cqX_ne_lDh : cqX ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_cqX : lDh ≠ cqX := by decide
@[simp] theorem ctg_cqX_ne_lDt : cqX ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_cqX : lDt ≠ cqX := by decide
@[simp] theorem ctg_cqX_ne_lDg : cqX ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_cqX : lDg ≠ cqX := by decide
@[simp] theorem ctg_cqX_ne_lDi : cqX ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_cqX : lDi ≠ cqX := by decide
@[simp] theorem ctg_cqX_ne_lRp : cqX ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_cqX : lRp ≠ cqX := by decide
@[simp] theorem ctg_cqX_ne_lRn : cqX ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_cqX : lRn ≠ cqX := by decide
@[simp] theorem ctg_cqX_ne_lDir : cqX ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_cqX : lDir ≠ cqX := by decide
@[simp] theorem ctg_cqX_ne_lFle : cqX ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_cqX : lFle ≠ cqX := by decide
@[simp] theorem ctg_cqX_ne_lKb : cqX ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_cqX : lKb ≠ cqX := by decide
@[simp] theorem ctg_cqH_ne_cqE : cqH ≠ cqE := by decide
@[simp] theorem ctg_cqH_ne_cqX : cqH ≠ cqX := by decide
@[simp] theorem ctg_cqH_ne_cqC : cqH ≠ cqC := by decide
@[simp] theorem ctg_cqH_ne_cqP : cqH ≠ cqP := by decide
@[simp] theorem ctg_cqH_ne_cqQ : cqH ≠ cqQ := by decide
@[simp] theorem ctg_cqH_ne_cqK : cqH ≠ cqK := by decide
@[simp] theorem ctg_cqH_ne_cqNp : cqH ≠ cqNp := by decide
@[simp] theorem ctg_cqH_ne_cqNf : cqH ≠ cqNf := by decide
@[simp] theorem ctg_cqH_ne_cqT : cqH ≠ cqT := by decide
@[simp] theorem ctg_cqH_ne_cqNn : cqH ≠ cqNn := by decide
@[simp] theorem ctg_cqH_ne_cqN : cqH ≠ cqN := by decide
@[simp] theorem ctg_cqH_ne_cqP2 : cqH ≠ cqP2 := by decide
@[simp] theorem ctg_cqH_ne_cqQ2 : cqH ≠ cqQ2 := by decide
@[simp] theorem ctg_cqH_ne_cqK2 : cqH ≠ cqK2 := by decide
@[simp] theorem ctg_cqH_ne_cqZ : cqH ≠ cqZ := by decide
@[simp] theorem ctg_cqH_ne_cqEt : cqH ≠ cqEt := by decide
@[simp] theorem ctg_cqH_ne_lFl : cqH ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_cqH : lFl ≠ cqH := by decide
@[simp] theorem ctg_cqH_ne_lDh : cqH ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_cqH : lDh ≠ cqH := by decide
@[simp] theorem ctg_cqH_ne_lDt : cqH ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_cqH : lDt ≠ cqH := by decide
@[simp] theorem ctg_cqH_ne_lDg : cqH ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_cqH : lDg ≠ cqH := by decide
@[simp] theorem ctg_cqH_ne_lDi : cqH ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_cqH : lDi ≠ cqH := by decide
@[simp] theorem ctg_cqH_ne_lRp : cqH ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_cqH : lRp ≠ cqH := by decide
@[simp] theorem ctg_cqH_ne_lRn : cqH ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_cqH : lRn ≠ cqH := by decide
@[simp] theorem ctg_cqH_ne_lDir : cqH ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_cqH : lDir ≠ cqH := by decide
@[simp] theorem ctg_cqH_ne_lFle : cqH ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_cqH : lFle ≠ cqH := by decide
@[simp] theorem ctg_cqH_ne_lKb : cqH ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_cqH : lKb ≠ cqH := by decide
@[simp] theorem ctg_cqC_ne_cqE : cqC ≠ cqE := by decide
@[simp] theorem ctg_cqC_ne_cqX : cqC ≠ cqX := by decide
@[simp] theorem ctg_cqC_ne_cqH : cqC ≠ cqH := by decide
@[simp] theorem ctg_cqC_ne_cqP : cqC ≠ cqP := by decide
@[simp] theorem ctg_cqC_ne_cqQ : cqC ≠ cqQ := by decide
@[simp] theorem ctg_cqC_ne_cqK : cqC ≠ cqK := by decide
@[simp] theorem ctg_cqC_ne_cqNp : cqC ≠ cqNp := by decide
@[simp] theorem ctg_cqC_ne_cqNf : cqC ≠ cqNf := by decide
@[simp] theorem ctg_cqC_ne_cqT : cqC ≠ cqT := by decide
@[simp] theorem ctg_cqC_ne_cqNn : cqC ≠ cqNn := by decide
@[simp] theorem ctg_cqC_ne_cqN : cqC ≠ cqN := by decide
@[simp] theorem ctg_cqC_ne_cqP2 : cqC ≠ cqP2 := by decide
@[simp] theorem ctg_cqC_ne_cqQ2 : cqC ≠ cqQ2 := by decide
@[simp] theorem ctg_cqC_ne_cqK2 : cqC ≠ cqK2 := by decide
@[simp] theorem ctg_cqC_ne_cqZ : cqC ≠ cqZ := by decide
@[simp] theorem ctg_cqC_ne_cqEt : cqC ≠ cqEt := by decide
@[simp] theorem ctg_cqC_ne_lFl : cqC ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_cqC : lFl ≠ cqC := by decide
@[simp] theorem ctg_cqC_ne_lDh : cqC ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_cqC : lDh ≠ cqC := by decide
@[simp] theorem ctg_cqC_ne_lDt : cqC ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_cqC : lDt ≠ cqC := by decide
@[simp] theorem ctg_cqC_ne_lDg : cqC ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_cqC : lDg ≠ cqC := by decide
@[simp] theorem ctg_cqC_ne_lDi : cqC ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_cqC : lDi ≠ cqC := by decide
@[simp] theorem ctg_cqC_ne_lRp : cqC ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_cqC : lRp ≠ cqC := by decide
@[simp] theorem ctg_cqC_ne_lRn : cqC ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_cqC : lRn ≠ cqC := by decide
@[simp] theorem ctg_cqC_ne_lDir : cqC ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_cqC : lDir ≠ cqC := by decide
@[simp] theorem ctg_cqC_ne_lFle : cqC ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_cqC : lFle ≠ cqC := by decide
@[simp] theorem ctg_cqC_ne_lKb : cqC ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_cqC : lKb ≠ cqC := by decide
@[simp] theorem ctg_cqP_ne_cqE : cqP ≠ cqE := by decide
@[simp] theorem ctg_cqP_ne_cqX : cqP ≠ cqX := by decide
@[simp] theorem ctg_cqP_ne_cqH : cqP ≠ cqH := by decide
@[simp] theorem ctg_cqP_ne_cqC : cqP ≠ cqC := by decide
@[simp] theorem ctg_cqP_ne_cqQ : cqP ≠ cqQ := by decide
@[simp] theorem ctg_cqP_ne_cqK : cqP ≠ cqK := by decide
@[simp] theorem ctg_cqP_ne_cqNp : cqP ≠ cqNp := by decide
@[simp] theorem ctg_cqP_ne_cqNf : cqP ≠ cqNf := by decide
@[simp] theorem ctg_cqP_ne_cqT : cqP ≠ cqT := by decide
@[simp] theorem ctg_cqP_ne_cqNn : cqP ≠ cqNn := by decide
@[simp] theorem ctg_cqP_ne_cqN : cqP ≠ cqN := by decide
@[simp] theorem ctg_cqP_ne_cqP2 : cqP ≠ cqP2 := by decide
@[simp] theorem ctg_cqP_ne_cqQ2 : cqP ≠ cqQ2 := by decide
@[simp] theorem ctg_cqP_ne_cqK2 : cqP ≠ cqK2 := by decide
@[simp] theorem ctg_cqP_ne_cqZ : cqP ≠ cqZ := by decide
@[simp] theorem ctg_cqP_ne_cqEt : cqP ≠ cqEt := by decide
@[simp] theorem ctg_cqP_ne_lFl : cqP ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_cqP : lFl ≠ cqP := by decide
@[simp] theorem ctg_cqP_ne_lDh : cqP ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_cqP : lDh ≠ cqP := by decide
@[simp] theorem ctg_cqP_ne_lDt : cqP ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_cqP : lDt ≠ cqP := by decide
@[simp] theorem ctg_cqP_ne_lDg : cqP ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_cqP : lDg ≠ cqP := by decide
@[simp] theorem ctg_cqP_ne_lDi : cqP ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_cqP : lDi ≠ cqP := by decide
@[simp] theorem ctg_cqP_ne_lRp : cqP ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_cqP : lRp ≠ cqP := by decide
@[simp] theorem ctg_cqP_ne_lRn : cqP ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_cqP : lRn ≠ cqP := by decide
@[simp] theorem ctg_cqP_ne_lDir : cqP ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_cqP : lDir ≠ cqP := by decide
@[simp] theorem ctg_cqP_ne_lFle : cqP ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_cqP : lFle ≠ cqP := by decide
@[simp] theorem ctg_cqP_ne_lKb : cqP ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_cqP : lKb ≠ cqP := by decide
@[simp] theorem ctg_cqQ_ne_cqE : cqQ ≠ cqE := by decide
@[simp] theorem ctg_cqQ_ne_cqX : cqQ ≠ cqX := by decide
@[simp] theorem ctg_cqQ_ne_cqH : cqQ ≠ cqH := by decide
@[simp] theorem ctg_cqQ_ne_cqC : cqQ ≠ cqC := by decide
@[simp] theorem ctg_cqQ_ne_cqP : cqQ ≠ cqP := by decide
@[simp] theorem ctg_cqQ_ne_cqK : cqQ ≠ cqK := by decide
@[simp] theorem ctg_cqQ_ne_cqNp : cqQ ≠ cqNp := by decide
@[simp] theorem ctg_cqQ_ne_cqNf : cqQ ≠ cqNf := by decide
@[simp] theorem ctg_cqQ_ne_cqT : cqQ ≠ cqT := by decide
@[simp] theorem ctg_cqQ_ne_cqNn : cqQ ≠ cqNn := by decide
@[simp] theorem ctg_cqQ_ne_cqN : cqQ ≠ cqN := by decide
@[simp] theorem ctg_cqQ_ne_cqP2 : cqQ ≠ cqP2 := by decide
@[simp] theorem ctg_cqQ_ne_cqQ2 : cqQ ≠ cqQ2 := by decide
@[simp] theorem ctg_cqQ_ne_cqK2 : cqQ ≠ cqK2 := by decide
@[simp] theorem ctg_cqQ_ne_cqZ : cqQ ≠ cqZ := by decide
@[simp] theorem ctg_cqQ_ne_cqEt : cqQ ≠ cqEt := by decide
@[simp] theorem ctg_cqQ_ne_lFl : cqQ ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_cqQ : lFl ≠ cqQ := by decide
@[simp] theorem ctg_cqQ_ne_lDh : cqQ ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_cqQ : lDh ≠ cqQ := by decide
@[simp] theorem ctg_cqQ_ne_lDt : cqQ ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_cqQ : lDt ≠ cqQ := by decide
@[simp] theorem ctg_cqQ_ne_lDg : cqQ ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_cqQ : lDg ≠ cqQ := by decide
@[simp] theorem ctg_cqQ_ne_lDi : cqQ ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_cqQ : lDi ≠ cqQ := by decide
@[simp] theorem ctg_cqQ_ne_lRp : cqQ ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_cqQ : lRp ≠ cqQ := by decide
@[simp] theorem ctg_cqQ_ne_lRn : cqQ ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_cqQ : lRn ≠ cqQ := by decide
@[simp] theorem ctg_cqQ_ne_lDir : cqQ ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_cqQ : lDir ≠ cqQ := by decide
@[simp] theorem ctg_cqQ_ne_lFle : cqQ ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_cqQ : lFle ≠ cqQ := by decide
@[simp] theorem ctg_cqQ_ne_lKb : cqQ ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_cqQ : lKb ≠ cqQ := by decide
@[simp] theorem ctg_cqK_ne_cqE : cqK ≠ cqE := by decide
@[simp] theorem ctg_cqK_ne_cqX : cqK ≠ cqX := by decide
@[simp] theorem ctg_cqK_ne_cqH : cqK ≠ cqH := by decide
@[simp] theorem ctg_cqK_ne_cqC : cqK ≠ cqC := by decide
@[simp] theorem ctg_cqK_ne_cqP : cqK ≠ cqP := by decide
@[simp] theorem ctg_cqK_ne_cqQ : cqK ≠ cqQ := by decide
@[simp] theorem ctg_cqK_ne_cqNp : cqK ≠ cqNp := by decide
@[simp] theorem ctg_cqK_ne_cqNf : cqK ≠ cqNf := by decide
@[simp] theorem ctg_cqK_ne_cqT : cqK ≠ cqT := by decide
@[simp] theorem ctg_cqK_ne_cqNn : cqK ≠ cqNn := by decide
@[simp] theorem ctg_cqK_ne_cqN : cqK ≠ cqN := by decide
@[simp] theorem ctg_cqK_ne_cqP2 : cqK ≠ cqP2 := by decide
@[simp] theorem ctg_cqK_ne_cqQ2 : cqK ≠ cqQ2 := by decide
@[simp] theorem ctg_cqK_ne_cqK2 : cqK ≠ cqK2 := by decide
@[simp] theorem ctg_cqK_ne_cqZ : cqK ≠ cqZ := by decide
@[simp] theorem ctg_cqK_ne_cqEt : cqK ≠ cqEt := by decide
@[simp] theorem ctg_cqK_ne_lFl : cqK ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_cqK : lFl ≠ cqK := by decide
@[simp] theorem ctg_cqK_ne_lDh : cqK ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_cqK : lDh ≠ cqK := by decide
@[simp] theorem ctg_cqK_ne_lDt : cqK ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_cqK : lDt ≠ cqK := by decide
@[simp] theorem ctg_cqK_ne_lDg : cqK ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_cqK : lDg ≠ cqK := by decide
@[simp] theorem ctg_cqK_ne_lDi : cqK ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_cqK : lDi ≠ cqK := by decide
@[simp] theorem ctg_cqK_ne_lRp : cqK ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_cqK : lRp ≠ cqK := by decide
@[simp] theorem ctg_cqK_ne_lRn : cqK ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_cqK : lRn ≠ cqK := by decide
@[simp] theorem ctg_cqK_ne_lDir : cqK ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_cqK : lDir ≠ cqK := by decide
@[simp] theorem ctg_cqK_ne_lFle : cqK ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_cqK : lFle ≠ cqK := by decide
@[simp] theorem ctg_cqK_ne_lKb : cqK ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_cqK : lKb ≠ cqK := by decide
@[simp] theorem ctg_cqNp_ne_cqE : cqNp ≠ cqE := by decide
@[simp] theorem ctg_cqNp_ne_cqX : cqNp ≠ cqX := by decide
@[simp] theorem ctg_cqNp_ne_cqH : cqNp ≠ cqH := by decide
@[simp] theorem ctg_cqNp_ne_cqC : cqNp ≠ cqC := by decide
@[simp] theorem ctg_cqNp_ne_cqP : cqNp ≠ cqP := by decide
@[simp] theorem ctg_cqNp_ne_cqQ : cqNp ≠ cqQ := by decide
@[simp] theorem ctg_cqNp_ne_cqK : cqNp ≠ cqK := by decide
@[simp] theorem ctg_cqNp_ne_cqNf : cqNp ≠ cqNf := by decide
@[simp] theorem ctg_cqNp_ne_cqT : cqNp ≠ cqT := by decide
@[simp] theorem ctg_cqNp_ne_cqNn : cqNp ≠ cqNn := by decide
@[simp] theorem ctg_cqNp_ne_cqN : cqNp ≠ cqN := by decide
@[simp] theorem ctg_cqNp_ne_cqP2 : cqNp ≠ cqP2 := by decide
@[simp] theorem ctg_cqNp_ne_cqQ2 : cqNp ≠ cqQ2 := by decide
@[simp] theorem ctg_cqNp_ne_cqK2 : cqNp ≠ cqK2 := by decide
@[simp] theorem ctg_cqNp_ne_cqZ : cqNp ≠ cqZ := by decide
@[simp] theorem ctg_cqNp_ne_cqEt : cqNp ≠ cqEt := by decide
@[simp] theorem ctg_cqNp_ne_lFl : cqNp ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_cqNp : lFl ≠ cqNp := by decide
@[simp] theorem ctg_cqNp_ne_lDh : cqNp ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_cqNp : lDh ≠ cqNp := by decide
@[simp] theorem ctg_cqNp_ne_lDt : cqNp ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_cqNp : lDt ≠ cqNp := by decide
@[simp] theorem ctg_cqNp_ne_lDg : cqNp ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_cqNp : lDg ≠ cqNp := by decide
@[simp] theorem ctg_cqNp_ne_lDi : cqNp ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_cqNp : lDi ≠ cqNp := by decide
@[simp] theorem ctg_cqNp_ne_lRp : cqNp ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_cqNp : lRp ≠ cqNp := by decide
@[simp] theorem ctg_cqNp_ne_lRn : cqNp ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_cqNp : lRn ≠ cqNp := by decide
@[simp] theorem ctg_cqNp_ne_lDir : cqNp ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_cqNp : lDir ≠ cqNp := by decide
@[simp] theorem ctg_cqNp_ne_lFle : cqNp ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_cqNp : lFle ≠ cqNp := by decide
@[simp] theorem ctg_cqNp_ne_lKb : cqNp ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_cqNp : lKb ≠ cqNp := by decide
@[simp] theorem ctg_cqNf_ne_cqE : cqNf ≠ cqE := by decide
@[simp] theorem ctg_cqNf_ne_cqX : cqNf ≠ cqX := by decide
@[simp] theorem ctg_cqNf_ne_cqH : cqNf ≠ cqH := by decide
@[simp] theorem ctg_cqNf_ne_cqC : cqNf ≠ cqC := by decide
@[simp] theorem ctg_cqNf_ne_cqP : cqNf ≠ cqP := by decide
@[simp] theorem ctg_cqNf_ne_cqQ : cqNf ≠ cqQ := by decide
@[simp] theorem ctg_cqNf_ne_cqK : cqNf ≠ cqK := by decide
@[simp] theorem ctg_cqNf_ne_cqNp : cqNf ≠ cqNp := by decide
@[simp] theorem ctg_cqNf_ne_cqT : cqNf ≠ cqT := by decide
@[simp] theorem ctg_cqNf_ne_cqNn : cqNf ≠ cqNn := by decide
@[simp] theorem ctg_cqNf_ne_cqN : cqNf ≠ cqN := by decide
@[simp] theorem ctg_cqNf_ne_cqP2 : cqNf ≠ cqP2 := by decide
@[simp] theorem ctg_cqNf_ne_cqQ2 : cqNf ≠ cqQ2 := by decide
@[simp] theorem ctg_cqNf_ne_cqK2 : cqNf ≠ cqK2 := by decide
@[simp] theorem ctg_cqNf_ne_cqZ : cqNf ≠ cqZ := by decide
@[simp] theorem ctg_cqNf_ne_cqEt : cqNf ≠ cqEt := by decide
@[simp] theorem ctg_cqNf_ne_lFl : cqNf ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_cqNf : lFl ≠ cqNf := by decide
@[simp] theorem ctg_cqNf_ne_lDh : cqNf ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_cqNf : lDh ≠ cqNf := by decide
@[simp] theorem ctg_cqNf_ne_lDt : cqNf ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_cqNf : lDt ≠ cqNf := by decide
@[simp] theorem ctg_cqNf_ne_lDg : cqNf ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_cqNf : lDg ≠ cqNf := by decide
@[simp] theorem ctg_cqNf_ne_lDi : cqNf ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_cqNf : lDi ≠ cqNf := by decide
@[simp] theorem ctg_cqNf_ne_lRp : cqNf ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_cqNf : lRp ≠ cqNf := by decide
@[simp] theorem ctg_cqNf_ne_lRn : cqNf ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_cqNf : lRn ≠ cqNf := by decide
@[simp] theorem ctg_cqNf_ne_lDir : cqNf ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_cqNf : lDir ≠ cqNf := by decide
@[simp] theorem ctg_cqNf_ne_lFle : cqNf ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_cqNf : lFle ≠ cqNf := by decide
@[simp] theorem ctg_cqNf_ne_lKb : cqNf ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_cqNf : lKb ≠ cqNf := by decide
@[simp] theorem ctg_cqT_ne_cqE : cqT ≠ cqE := by decide
@[simp] theorem ctg_cqT_ne_cqX : cqT ≠ cqX := by decide
@[simp] theorem ctg_cqT_ne_cqH : cqT ≠ cqH := by decide
@[simp] theorem ctg_cqT_ne_cqC : cqT ≠ cqC := by decide
@[simp] theorem ctg_cqT_ne_cqP : cqT ≠ cqP := by decide
@[simp] theorem ctg_cqT_ne_cqQ : cqT ≠ cqQ := by decide
@[simp] theorem ctg_cqT_ne_cqK : cqT ≠ cqK := by decide
@[simp] theorem ctg_cqT_ne_cqNp : cqT ≠ cqNp := by decide
@[simp] theorem ctg_cqT_ne_cqNf : cqT ≠ cqNf := by decide
@[simp] theorem ctg_cqT_ne_cqNn : cqT ≠ cqNn := by decide
@[simp] theorem ctg_cqT_ne_cqN : cqT ≠ cqN := by decide
@[simp] theorem ctg_cqT_ne_cqP2 : cqT ≠ cqP2 := by decide
@[simp] theorem ctg_cqT_ne_cqQ2 : cqT ≠ cqQ2 := by decide
@[simp] theorem ctg_cqT_ne_cqK2 : cqT ≠ cqK2 := by decide
@[simp] theorem ctg_cqT_ne_cqZ : cqT ≠ cqZ := by decide
@[simp] theorem ctg_cqT_ne_cqEt : cqT ≠ cqEt := by decide
@[simp] theorem ctg_cqT_ne_lFl : cqT ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_cqT : lFl ≠ cqT := by decide
@[simp] theorem ctg_cqT_ne_lDh : cqT ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_cqT : lDh ≠ cqT := by decide
@[simp] theorem ctg_cqT_ne_lDt : cqT ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_cqT : lDt ≠ cqT := by decide
@[simp] theorem ctg_cqT_ne_lDg : cqT ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_cqT : lDg ≠ cqT := by decide
@[simp] theorem ctg_cqT_ne_lDi : cqT ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_cqT : lDi ≠ cqT := by decide
@[simp] theorem ctg_cqT_ne_lRp : cqT ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_cqT : lRp ≠ cqT := by decide
@[simp] theorem ctg_cqT_ne_lRn : cqT ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_cqT : lRn ≠ cqT := by decide
@[simp] theorem ctg_cqT_ne_lDir : cqT ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_cqT : lDir ≠ cqT := by decide
@[simp] theorem ctg_cqT_ne_lFle : cqT ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_cqT : lFle ≠ cqT := by decide
@[simp] theorem ctg_cqT_ne_lKb : cqT ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_cqT : lKb ≠ cqT := by decide
@[simp] theorem ctg_cqNn_ne_cqE : cqNn ≠ cqE := by decide
@[simp] theorem ctg_cqNn_ne_cqX : cqNn ≠ cqX := by decide
@[simp] theorem ctg_cqNn_ne_cqH : cqNn ≠ cqH := by decide
@[simp] theorem ctg_cqNn_ne_cqC : cqNn ≠ cqC := by decide
@[simp] theorem ctg_cqNn_ne_cqP : cqNn ≠ cqP := by decide
@[simp] theorem ctg_cqNn_ne_cqQ : cqNn ≠ cqQ := by decide
@[simp] theorem ctg_cqNn_ne_cqK : cqNn ≠ cqK := by decide
@[simp] theorem ctg_cqNn_ne_cqNp : cqNn ≠ cqNp := by decide
@[simp] theorem ctg_cqNn_ne_cqNf : cqNn ≠ cqNf := by decide
@[simp] theorem ctg_cqNn_ne_cqT : cqNn ≠ cqT := by decide
@[simp] theorem ctg_cqNn_ne_cqN : cqNn ≠ cqN := by decide
@[simp] theorem ctg_cqNn_ne_cqP2 : cqNn ≠ cqP2 := by decide
@[simp] theorem ctg_cqNn_ne_cqQ2 : cqNn ≠ cqQ2 := by decide
@[simp] theorem ctg_cqNn_ne_cqK2 : cqNn ≠ cqK2 := by decide
@[simp] theorem ctg_cqNn_ne_cqZ : cqNn ≠ cqZ := by decide
@[simp] theorem ctg_cqNn_ne_cqEt : cqNn ≠ cqEt := by decide
@[simp] theorem ctg_cqNn_ne_lFl : cqNn ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_cqNn : lFl ≠ cqNn := by decide
@[simp] theorem ctg_cqNn_ne_lDh : cqNn ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_cqNn : lDh ≠ cqNn := by decide
@[simp] theorem ctg_cqNn_ne_lDt : cqNn ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_cqNn : lDt ≠ cqNn := by decide
@[simp] theorem ctg_cqNn_ne_lDg : cqNn ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_cqNn : lDg ≠ cqNn := by decide
@[simp] theorem ctg_cqNn_ne_lDi : cqNn ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_cqNn : lDi ≠ cqNn := by decide
@[simp] theorem ctg_cqNn_ne_lRp : cqNn ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_cqNn : lRp ≠ cqNn := by decide
@[simp] theorem ctg_cqNn_ne_lRn : cqNn ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_cqNn : lRn ≠ cqNn := by decide
@[simp] theorem ctg_cqNn_ne_lDir : cqNn ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_cqNn : lDir ≠ cqNn := by decide
@[simp] theorem ctg_cqNn_ne_lFle : cqNn ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_cqNn : lFle ≠ cqNn := by decide
@[simp] theorem ctg_cqNn_ne_lKb : cqNn ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_cqNn : lKb ≠ cqNn := by decide
@[simp] theorem ctg_cqN_ne_cqE : cqN ≠ cqE := by decide
@[simp] theorem ctg_cqN_ne_cqX : cqN ≠ cqX := by decide
@[simp] theorem ctg_cqN_ne_cqH : cqN ≠ cqH := by decide
@[simp] theorem ctg_cqN_ne_cqC : cqN ≠ cqC := by decide
@[simp] theorem ctg_cqN_ne_cqP : cqN ≠ cqP := by decide
@[simp] theorem ctg_cqN_ne_cqQ : cqN ≠ cqQ := by decide
@[simp] theorem ctg_cqN_ne_cqK : cqN ≠ cqK := by decide
@[simp] theorem ctg_cqN_ne_cqNp : cqN ≠ cqNp := by decide
@[simp] theorem ctg_cqN_ne_cqNf : cqN ≠ cqNf := by decide
@[simp] theorem ctg_cqN_ne_cqT : cqN ≠ cqT := by decide
@[simp] theorem ctg_cqN_ne_cqNn : cqN ≠ cqNn := by decide
@[simp] theorem ctg_cqN_ne_cqP2 : cqN ≠ cqP2 := by decide
@[simp] theorem ctg_cqN_ne_cqQ2 : cqN ≠ cqQ2 := by decide
@[simp] theorem ctg_cqN_ne_cqK2 : cqN ≠ cqK2 := by decide
@[simp] theorem ctg_cqN_ne_cqZ : cqN ≠ cqZ := by decide
@[simp] theorem ctg_cqN_ne_cqEt : cqN ≠ cqEt := by decide
@[simp] theorem ctg_cqN_ne_lFl : cqN ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_cqN : lFl ≠ cqN := by decide
@[simp] theorem ctg_cqN_ne_lDh : cqN ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_cqN : lDh ≠ cqN := by decide
@[simp] theorem ctg_cqN_ne_lDt : cqN ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_cqN : lDt ≠ cqN := by decide
@[simp] theorem ctg_cqN_ne_lDg : cqN ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_cqN : lDg ≠ cqN := by decide
@[simp] theorem ctg_cqN_ne_lDi : cqN ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_cqN : lDi ≠ cqN := by decide
@[simp] theorem ctg_cqN_ne_lRp : cqN ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_cqN : lRp ≠ cqN := by decide
@[simp] theorem ctg_cqN_ne_lRn : cqN ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_cqN : lRn ≠ cqN := by decide
@[simp] theorem ctg_cqN_ne_lDir : cqN ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_cqN : lDir ≠ cqN := by decide
@[simp] theorem ctg_cqN_ne_lFle : cqN ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_cqN : lFle ≠ cqN := by decide
@[simp] theorem ctg_cqN_ne_lKb : cqN ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_cqN : lKb ≠ cqN := by decide
@[simp] theorem ctg_cqP2_ne_cqE : cqP2 ≠ cqE := by decide
@[simp] theorem ctg_cqP2_ne_cqX : cqP2 ≠ cqX := by decide
@[simp] theorem ctg_cqP2_ne_cqH : cqP2 ≠ cqH := by decide
@[simp] theorem ctg_cqP2_ne_cqC : cqP2 ≠ cqC := by decide
@[simp] theorem ctg_cqP2_ne_cqP : cqP2 ≠ cqP := by decide
@[simp] theorem ctg_cqP2_ne_cqQ : cqP2 ≠ cqQ := by decide
@[simp] theorem ctg_cqP2_ne_cqK : cqP2 ≠ cqK := by decide
@[simp] theorem ctg_cqP2_ne_cqNp : cqP2 ≠ cqNp := by decide
@[simp] theorem ctg_cqP2_ne_cqNf : cqP2 ≠ cqNf := by decide
@[simp] theorem ctg_cqP2_ne_cqT : cqP2 ≠ cqT := by decide
@[simp] theorem ctg_cqP2_ne_cqNn : cqP2 ≠ cqNn := by decide
@[simp] theorem ctg_cqP2_ne_cqN : cqP2 ≠ cqN := by decide
@[simp] theorem ctg_cqP2_ne_cqQ2 : cqP2 ≠ cqQ2 := by decide
@[simp] theorem ctg_cqP2_ne_cqK2 : cqP2 ≠ cqK2 := by decide
@[simp] theorem ctg_cqP2_ne_cqZ : cqP2 ≠ cqZ := by decide
@[simp] theorem ctg_cqP2_ne_cqEt : cqP2 ≠ cqEt := by decide
@[simp] theorem ctg_cqP2_ne_lFl : cqP2 ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_cqP2 : lFl ≠ cqP2 := by decide
@[simp] theorem ctg_cqP2_ne_lDh : cqP2 ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_cqP2 : lDh ≠ cqP2 := by decide
@[simp] theorem ctg_cqP2_ne_lDt : cqP2 ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_cqP2 : lDt ≠ cqP2 := by decide
@[simp] theorem ctg_cqP2_ne_lDg : cqP2 ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_cqP2 : lDg ≠ cqP2 := by decide
@[simp] theorem ctg_cqP2_ne_lDi : cqP2 ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_cqP2 : lDi ≠ cqP2 := by decide
@[simp] theorem ctg_cqP2_ne_lRp : cqP2 ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_cqP2 : lRp ≠ cqP2 := by decide
@[simp] theorem ctg_cqP2_ne_lRn : cqP2 ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_cqP2 : lRn ≠ cqP2 := by decide
@[simp] theorem ctg_cqP2_ne_lDir : cqP2 ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_cqP2 : lDir ≠ cqP2 := by decide
@[simp] theorem ctg_cqP2_ne_lFle : cqP2 ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_cqP2 : lFle ≠ cqP2 := by decide
@[simp] theorem ctg_cqP2_ne_lKb : cqP2 ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_cqP2 : lKb ≠ cqP2 := by decide
@[simp] theorem ctg_cqQ2_ne_cqE : cqQ2 ≠ cqE := by decide
@[simp] theorem ctg_cqQ2_ne_cqX : cqQ2 ≠ cqX := by decide
@[simp] theorem ctg_cqQ2_ne_cqH : cqQ2 ≠ cqH := by decide
@[simp] theorem ctg_cqQ2_ne_cqC : cqQ2 ≠ cqC := by decide
@[simp] theorem ctg_cqQ2_ne_cqP : cqQ2 ≠ cqP := by decide
@[simp] theorem ctg_cqQ2_ne_cqQ : cqQ2 ≠ cqQ := by decide
@[simp] theorem ctg_cqQ2_ne_cqK : cqQ2 ≠ cqK := by decide
@[simp] theorem ctg_cqQ2_ne_cqNp : cqQ2 ≠ cqNp := by decide
@[simp] theorem ctg_cqQ2_ne_cqNf : cqQ2 ≠ cqNf := by decide
@[simp] theorem ctg_cqQ2_ne_cqT : cqQ2 ≠ cqT := by decide
@[simp] theorem ctg_cqQ2_ne_cqNn : cqQ2 ≠ cqNn := by decide
@[simp] theorem ctg_cqQ2_ne_cqN : cqQ2 ≠ cqN := by decide
@[simp] theorem ctg_cqQ2_ne_cqP2 : cqQ2 ≠ cqP2 := by decide
@[simp] theorem ctg_cqQ2_ne_cqK2 : cqQ2 ≠ cqK2 := by decide
@[simp] theorem ctg_cqQ2_ne_cqZ : cqQ2 ≠ cqZ := by decide
@[simp] theorem ctg_cqQ2_ne_cqEt : cqQ2 ≠ cqEt := by decide
@[simp] theorem ctg_cqQ2_ne_lFl : cqQ2 ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_cqQ2 : lFl ≠ cqQ2 := by decide
@[simp] theorem ctg_cqQ2_ne_lDh : cqQ2 ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_cqQ2 : lDh ≠ cqQ2 := by decide
@[simp] theorem ctg_cqQ2_ne_lDt : cqQ2 ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_cqQ2 : lDt ≠ cqQ2 := by decide
@[simp] theorem ctg_cqQ2_ne_lDg : cqQ2 ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_cqQ2 : lDg ≠ cqQ2 := by decide
@[simp] theorem ctg_cqQ2_ne_lDi : cqQ2 ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_cqQ2 : lDi ≠ cqQ2 := by decide
@[simp] theorem ctg_cqQ2_ne_lRp : cqQ2 ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_cqQ2 : lRp ≠ cqQ2 := by decide
@[simp] theorem ctg_cqQ2_ne_lRn : cqQ2 ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_cqQ2 : lRn ≠ cqQ2 := by decide
@[simp] theorem ctg_cqQ2_ne_lDir : cqQ2 ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_cqQ2 : lDir ≠ cqQ2 := by decide
@[simp] theorem ctg_cqQ2_ne_lFle : cqQ2 ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_cqQ2 : lFle ≠ cqQ2 := by decide
@[simp] theorem ctg_cqQ2_ne_lKb : cqQ2 ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_cqQ2 : lKb ≠ cqQ2 := by decide
@[simp] theorem ctg_cqK2_ne_cqE : cqK2 ≠ cqE := by decide
@[simp] theorem ctg_cqK2_ne_cqX : cqK2 ≠ cqX := by decide
@[simp] theorem ctg_cqK2_ne_cqH : cqK2 ≠ cqH := by decide
@[simp] theorem ctg_cqK2_ne_cqC : cqK2 ≠ cqC := by decide
@[simp] theorem ctg_cqK2_ne_cqP : cqK2 ≠ cqP := by decide
@[simp] theorem ctg_cqK2_ne_cqQ : cqK2 ≠ cqQ := by decide
@[simp] theorem ctg_cqK2_ne_cqK : cqK2 ≠ cqK := by decide
@[simp] theorem ctg_cqK2_ne_cqNp : cqK2 ≠ cqNp := by decide
@[simp] theorem ctg_cqK2_ne_cqNf : cqK2 ≠ cqNf := by decide
@[simp] theorem ctg_cqK2_ne_cqT : cqK2 ≠ cqT := by decide
@[simp] theorem ctg_cqK2_ne_cqNn : cqK2 ≠ cqNn := by decide
@[simp] theorem ctg_cqK2_ne_cqN : cqK2 ≠ cqN := by decide
@[simp] theorem ctg_cqK2_ne_cqP2 : cqK2 ≠ cqP2 := by decide
@[simp] theorem ctg_cqK2_ne_cqQ2 : cqK2 ≠ cqQ2 := by decide
@[simp] theorem ctg_cqK2_ne_cqZ : cqK2 ≠ cqZ := by decide
@[simp] theorem ctg_cqK2_ne_cqEt : cqK2 ≠ cqEt := by decide
@[simp] theorem ctg_cqK2_ne_lFl : cqK2 ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_cqK2 : lFl ≠ cqK2 := by decide
@[simp] theorem ctg_cqK2_ne_lDh : cqK2 ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_cqK2 : lDh ≠ cqK2 := by decide
@[simp] theorem ctg_cqK2_ne_lDt : cqK2 ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_cqK2 : lDt ≠ cqK2 := by decide
@[simp] theorem ctg_cqK2_ne_lDg : cqK2 ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_cqK2 : lDg ≠ cqK2 := by decide
@[simp] theorem ctg_cqK2_ne_lDi : cqK2 ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_cqK2 : lDi ≠ cqK2 := by decide
@[simp] theorem ctg_cqK2_ne_lRp : cqK2 ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_cqK2 : lRp ≠ cqK2 := by decide
@[simp] theorem ctg_cqK2_ne_lRn : cqK2 ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_cqK2 : lRn ≠ cqK2 := by decide
@[simp] theorem ctg_cqK2_ne_lDir : cqK2 ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_cqK2 : lDir ≠ cqK2 := by decide
@[simp] theorem ctg_cqK2_ne_lFle : cqK2 ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_cqK2 : lFle ≠ cqK2 := by decide
@[simp] theorem ctg_cqK2_ne_lKb : cqK2 ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_cqK2 : lKb ≠ cqK2 := by decide
@[simp] theorem ctg_cqZ_ne_cqE : cqZ ≠ cqE := by decide
@[simp] theorem ctg_cqZ_ne_cqX : cqZ ≠ cqX := by decide
@[simp] theorem ctg_cqZ_ne_cqH : cqZ ≠ cqH := by decide
@[simp] theorem ctg_cqZ_ne_cqC : cqZ ≠ cqC := by decide
@[simp] theorem ctg_cqZ_ne_cqP : cqZ ≠ cqP := by decide
@[simp] theorem ctg_cqZ_ne_cqQ : cqZ ≠ cqQ := by decide
@[simp] theorem ctg_cqZ_ne_cqK : cqZ ≠ cqK := by decide
@[simp] theorem ctg_cqZ_ne_cqNp : cqZ ≠ cqNp := by decide
@[simp] theorem ctg_cqZ_ne_cqNf : cqZ ≠ cqNf := by decide
@[simp] theorem ctg_cqZ_ne_cqT : cqZ ≠ cqT := by decide
@[simp] theorem ctg_cqZ_ne_cqNn : cqZ ≠ cqNn := by decide
@[simp] theorem ctg_cqZ_ne_cqN : cqZ ≠ cqN := by decide
@[simp] theorem ctg_cqZ_ne_cqP2 : cqZ ≠ cqP2 := by decide
@[simp] theorem ctg_cqZ_ne_cqQ2 : cqZ ≠ cqQ2 := by decide
@[simp] theorem ctg_cqZ_ne_cqK2 : cqZ ≠ cqK2 := by decide
@[simp] theorem ctg_cqZ_ne_cqEt : cqZ ≠ cqEt := by decide
@[simp] theorem ctg_cqZ_ne_lFl : cqZ ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_cqZ : lFl ≠ cqZ := by decide
@[simp] theorem ctg_cqZ_ne_lDh : cqZ ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_cqZ : lDh ≠ cqZ := by decide
@[simp] theorem ctg_cqZ_ne_lDt : cqZ ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_cqZ : lDt ≠ cqZ := by decide
@[simp] theorem ctg_cqZ_ne_lDg : cqZ ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_cqZ : lDg ≠ cqZ := by decide
@[simp] theorem ctg_cqZ_ne_lDi : cqZ ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_cqZ : lDi ≠ cqZ := by decide
@[simp] theorem ctg_cqZ_ne_lRp : cqZ ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_cqZ : lRp ≠ cqZ := by decide
@[simp] theorem ctg_cqZ_ne_lRn : cqZ ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_cqZ : lRn ≠ cqZ := by decide
@[simp] theorem ctg_cqZ_ne_lDir : cqZ ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_cqZ : lDir ≠ cqZ := by decide
@[simp] theorem ctg_cqZ_ne_lFle : cqZ ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_cqZ : lFle ≠ cqZ := by decide
@[simp] theorem ctg_cqZ_ne_lKb : cqZ ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_cqZ : lKb ≠ cqZ := by decide
@[simp] theorem ctg_cqEt_ne_cqE : cqEt ≠ cqE := by decide
@[simp] theorem ctg_cqEt_ne_cqX : cqEt ≠ cqX := by decide
@[simp] theorem ctg_cqEt_ne_cqH : cqEt ≠ cqH := by decide
@[simp] theorem ctg_cqEt_ne_cqC : cqEt ≠ cqC := by decide
@[simp] theorem ctg_cqEt_ne_cqP : cqEt ≠ cqP := by decide
@[simp] theorem ctg_cqEt_ne_cqQ : cqEt ≠ cqQ := by decide
@[simp] theorem ctg_cqEt_ne_cqK : cqEt ≠ cqK := by decide
@[simp] theorem ctg_cqEt_ne_cqNp : cqEt ≠ cqNp := by decide
@[simp] theorem ctg_cqEt_ne_cqNf : cqEt ≠ cqNf := by decide
@[simp] theorem ctg_cqEt_ne_cqT : cqEt ≠ cqT := by decide
@[simp] theorem ctg_cqEt_ne_cqNn : cqEt ≠ cqNn := by decide
@[simp] theorem ctg_cqEt_ne_cqN : cqEt ≠ cqN := by decide
@[simp] theorem ctg_cqEt_ne_cqP2 : cqEt ≠ cqP2 := by decide
@[simp] theorem ctg_cqEt_ne_cqQ2 : cqEt ≠ cqQ2 := by decide
@[simp] theorem ctg_cqEt_ne_cqK2 : cqEt ≠ cqK2 := by decide
@[simp] theorem ctg_cqEt_ne_cqZ : cqEt ≠ cqZ := by decide
@[simp] theorem ctg_cqEt_ne_lFl : cqEt ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_cqEt : lFl ≠ cqEt := by decide
@[simp] theorem ctg_cqEt_ne_lDh : cqEt ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_cqEt : lDh ≠ cqEt := by decide
@[simp] theorem ctg_cqEt_ne_lDt : cqEt ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_cqEt : lDt ≠ cqEt := by decide
@[simp] theorem ctg_cqEt_ne_lDg : cqEt ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_cqEt : lDg ≠ cqEt := by decide
@[simp] theorem ctg_cqEt_ne_lDi : cqEt ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_cqEt : lDi ≠ cqEt := by decide
@[simp] theorem ctg_cqEt_ne_lRp : cqEt ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_cqEt : lRp ≠ cqEt := by decide
@[simp] theorem ctg_cqEt_ne_lRn : cqEt ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_cqEt : lRn ≠ cqEt := by decide
@[simp] theorem ctg_cqEt_ne_lDir : cqEt ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_cqEt : lDir ≠ cqEt := by decide
@[simp] theorem ctg_cqEt_ne_lFle : cqEt ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_cqEt : lFle ≠ cqEt := by decide
@[simp] theorem ctg_cqEt_ne_lKb : cqEt ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_cqEt : lKb ≠ cqEt := by decide
@[simp] theorem ctg_cfO_ne_cfE : cfO ≠ cfE := by decide
@[simp] theorem ctg_cfO_ne_cfX : cfO ≠ cfX := by decide
@[simp] theorem ctg_cfO_ne_cfR : cfO ≠ cfR := by decide
@[simp] theorem ctg_cfO_ne_lFl : cfO ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_cfO : lFl ≠ cfO := by decide
@[simp] theorem ctg_cfO_ne_lDh : cfO ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_cfO : lDh ≠ cfO := by decide
@[simp] theorem ctg_cfO_ne_lDt : cfO ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_cfO : lDt ≠ cfO := by decide
@[simp] theorem ctg_cfO_ne_lDg : cfO ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_cfO : lDg ≠ cfO := by decide
@[simp] theorem ctg_cfO_ne_lDi : cfO ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_cfO : lDi ≠ cfO := by decide
@[simp] theorem ctg_cfO_ne_lRp : cfO ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_cfO : lRp ≠ cfO := by decide
@[simp] theorem ctg_cfO_ne_lRn : cfO ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_cfO : lRn ≠ cfO := by decide
@[simp] theorem ctg_cfO_ne_lDir : cfO ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_cfO : lDir ≠ cfO := by decide
@[simp] theorem ctg_cfO_ne_lFle : cfO ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_cfO : lFle ≠ cfO := by decide
@[simp] theorem ctg_cfO_ne_lKb : cfO ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_cfO : lKb ≠ cfO := by decide
@[simp] theorem ctg_cfE_ne_cfO : cfE ≠ cfO := by decide
@[simp] theorem ctg_cfE_ne_cfX : cfE ≠ cfX := by decide
@[simp] theorem ctg_cfE_ne_cfR : cfE ≠ cfR := by decide
@[simp] theorem ctg_cfE_ne_lFl : cfE ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_cfE : lFl ≠ cfE := by decide
@[simp] theorem ctg_cfE_ne_lDh : cfE ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_cfE : lDh ≠ cfE := by decide
@[simp] theorem ctg_cfE_ne_lDt : cfE ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_cfE : lDt ≠ cfE := by decide
@[simp] theorem ctg_cfE_ne_lDg : cfE ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_cfE : lDg ≠ cfE := by decide
@[simp] theorem ctg_cfE_ne_lDi : cfE ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_cfE : lDi ≠ cfE := by decide
@[simp] theorem ctg_cfE_ne_lRp : cfE ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_cfE : lRp ≠ cfE := by decide
@[simp] theorem ctg_cfE_ne_lRn : cfE ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_cfE : lRn ≠ cfE := by decide
@[simp] theorem ctg_cfE_ne_lDir : cfE ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_cfE : lDir ≠ cfE := by decide
@[simp] theorem ctg_cfE_ne_lFle : cfE ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_cfE : lFle ≠ cfE := by decide
@[simp] theorem ctg_cfE_ne_lKb : cfE ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_cfE : lKb ≠ cfE := by decide
@[simp] theorem ctg_cfX_ne_cfO : cfX ≠ cfO := by decide
@[simp] theorem ctg_cfX_ne_cfE : cfX ≠ cfE := by decide
@[simp] theorem ctg_cfX_ne_cfR : cfX ≠ cfR := by decide
@[simp] theorem ctg_cfX_ne_lFl : cfX ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_cfX : lFl ≠ cfX := by decide
@[simp] theorem ctg_cfX_ne_lDh : cfX ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_cfX : lDh ≠ cfX := by decide
@[simp] theorem ctg_cfX_ne_lDt : cfX ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_cfX : lDt ≠ cfX := by decide
@[simp] theorem ctg_cfX_ne_lDg : cfX ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_cfX : lDg ≠ cfX := by decide
@[simp] theorem ctg_cfX_ne_lDi : cfX ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_cfX : lDi ≠ cfX := by decide
@[simp] theorem ctg_cfX_ne_lRp : cfX ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_cfX : lRp ≠ cfX := by decide
@[simp] theorem ctg_cfX_ne_lRn : cfX ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_cfX : lRn ≠ cfX := by decide
@[simp] theorem ctg_cfX_ne_lDir : cfX ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_cfX : lDir ≠ cfX := by decide
@[simp] theorem ctg_cfX_ne_lFle : cfX ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_cfX : lFle ≠ cfX := by decide
@[simp] theorem ctg_cfX_ne_lKb : cfX ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_cfX : lKb ≠ cfX := by decide
@[simp] theorem ctg_cfR_ne_cfO : cfR ≠ cfO := by decide
@[simp] theorem ctg_cfR_ne_cfE : cfR ≠ cfE := by decide
@[simp] theorem ctg_cfR_ne_cfX : cfR ≠ cfX := by decide
@[simp] theorem ctg_cfR_ne_lFl : cfR ≠ lFl := by decide
@[simp] theorem ctg_lFl_ne_cfR : lFl ≠ cfR := by decide
@[simp] theorem ctg_cfR_ne_lDh : cfR ≠ lDh := by decide
@[simp] theorem ctg_lDh_ne_cfR : lDh ≠ cfR := by decide
@[simp] theorem ctg_cfR_ne_lDt : cfR ≠ lDt := by decide
@[simp] theorem ctg_lDt_ne_cfR : lDt ≠ cfR := by decide
@[simp] theorem ctg_cfR_ne_lDg : cfR ≠ lDg := by decide
@[simp] theorem ctg_lDg_ne_cfR : lDg ≠ cfR := by decide
@[simp] theorem ctg_cfR_ne_lDi : cfR ≠ lDi := by decide
@[simp] theorem ctg_lDi_ne_cfR : lDi ≠ cfR := by decide
@[simp] theorem ctg_cfR_ne_lRp : cfR ≠ lRp := by decide
@[simp] theorem ctg_lRp_ne_cfR : lRp ≠ cfR := by decide
@[simp] theorem ctg_cfR_ne_lRn : cfR ≠ lRn := by decide
@[simp] theorem ctg_lRn_ne_cfR : lRn ≠ cfR := by decide
@[simp] theorem ctg_cfR_ne_lDir : cfR ≠ lDir := by decide
@[simp] theorem ctg_lDir_ne_cfR : lDir ≠ cfR := by decide
@[simp] theorem ctg_cfR_ne_lFle : cfR ≠ lFle := by decide
@[simp] theorem ctg_lFle_ne_cfR : lFle ≠ cfR := by decide
@[simp] theorem ctg_cfR_ne_lKb : cfR ≠ lKb := by decide
@[simp] theorem ctg_lKb_ne_cfR : lKb ≠ cfR := by decide

def nuBody : ProgHOL 64 := prologue [nuH] (.seq (.call (some (some (.local, nuH), none)) fGetAppFn [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv nuE)]) (.ite (tagIsE nuH 5) (.return (.const 0)) (.ite (tagIsE nuH 7) (.return (.const 0)) (.ite (tagIsE nuH 0) (.return (.const 0)) (.return (.const 1))))))
def chParams : List MlS := [chC, chW]
def chLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, chH, chD, chP, chQ, chK]
def chBody (C : Ctx) : ProgHOL 64 := prologue chLocals (.seq (.call (some (some (.local, chH), none)) fGetAppFn [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv chW)]) (.ite (tagIsE chH 3) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv chH)) (.seq eViewP (.seq (.assign .local chD (.load .one (vv lRp))) (.ite (.cmp .equal (vv chD) (vv chC)) (.return (.const 2)) (envFindP C chP (vv chD) (.ite (.cmp .equal (vv chP) (.const 0)) (.return (.const 0)) (.seq (.assign .local chQ (.op .sub [(vv chP), (.const 1)])) (.seq (.assign .local chK (.load .one (vv chQ))) (.ite (.cmp .equal (vv chK) (.const 4)) (.return (.const 1)) (.return (.const 0)))))))))))) (.return (.const 0))))
def cqLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, cqX, cqH, cqC, cqP, cqQ, cqK, cqNp, cqNf, cqT, cqNn, cqN, cqP2, cqQ2, cqK2, cqZ, cqEt]
def cqBody (C : Ctx) : ProgHOL 64 := prologue cqLocals (.seq (.call (some (some (.local, cqX), none)) ExM.fHasFvar [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv cqE)]) (.ite (vv cqX) (.return (.const 0)) (.seq (.call (some (some (.local, cqH), none)) fGetAppFn [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv cqE)]) (.ite (tagIsE cqH 3) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv cqH)) (.seq eViewP (.seq (.assign .local cqC (.load .one (vv lRp))) (envFindP C cqP (vv cqC) (.ite (.cmp .equal (vv cqP) (.const 0)) (.return (.const 0)) (.seq (.assign .local cqQ (.op .sub [(vv cqP), (.const 1)])) (.seq (.assign .local cqK (.load .one (vv cqQ))) (.ite (.cmp .notEqual (vv cqK) (.const 4)) (.return (.const 0)) (.seq (.assign .local cqNp (.load .one (.op .add [(vv cqQ), (.const 32)]))) (.seq (.assign .local cqNf (.load .one (.op .add [(vv cqQ), (.const 40)]))) (.seq (.assign .local cqT (.load .one (.op .add [(vv cqQ), (.const 48)]))) (.seq (.assign .local cqNn (.load .one (.const (ecell C (C.PO + PIN_NAT))))) (.ite (.cmp .equal (vv cqT) (vv cqNn)) (.return (.const 0)) (.seq (.call (some (some (.local, cqN), none)) fNa [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv cqE)]) (.ite (.cmp .notEqual (vv cqN) (.op .add [(vv cqNp), (vv cqNf)])) (.return (.const 0)) (envFindP C cqP2 (vv cqT) (.ite (.cmp .equal (vv cqP2) (.const 0)) (.return (.const 0)) (.seq (.assign .local cqQ2 (.op .sub [(vv cqP2), (.const 1)])) (.seq (.assign .local cqK2 (.load .one (vv cqQ2))) (.ite (.cmp .notEqual (vv cqK2) (.const 3)) (.return (.const 0)) (.seq (.assign .local cqZ (.load .one (.op .add [(vv cqQ2), (.const 72)]))) (.seq (.assign .local cqEt (.load .one (.op .add [(vv cqQ2), (.const 32)]))) (.ite (vv cqZ) (.ite (vv cqEt) (.return (.const 0)) (.return (.op .add [(vv cqC), (.const 1)]))) (.return (.const 0)))))))))))))))))))))))))) (.return (.const 0))))))
def cfParams : List MlS := [cfO, cfE]
def cfBody (_v : Bool) : ProgHOL 64 := prologue [cfX, cfR] (.ite (.var .global gEo) (.seq (.call (some (some (.local, cfR), none)) fCq [(vv cfE)]) (.return (vv cfR))) (.seq (.call (some (some (.local, cfX), none)) ExM.fHasFvar [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv cfO)]) (.ite (vv cfX) (.return (.const 0)) (.seq (.call (some (some (.local, cfR), none)) fCq [(vv cfE)]) (.return (vv cfR))))))

section
variable {σ : Type}

theorem nu_spec (C : Ctx) (hcaf : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one))
    (s : AState) (e : EIdx) :
    SpecR (σ := σ) (Pre C s [(nuE, Enc.idxW e)]) nuBody s (ioNeutral e) (PostB C) := by
  refine specR_prologue (postB_locals C) (Knot.params_none C [nuH] [nuE] [Enc.idxW e] (by decide) (by decide)) ?_
  unfold ioNeutral
  refine specR_callNIM (C := C) nuH fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv nuE]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e] (by decide) rfl (by decide) hcaf
    ⟨rfl, by simp +decide [Env.get, ctxEnv], trivial⟩
    (fun a w s' st => getAppFn coreWalkFuel e s = .ok (a, s') ∧ Post C s a w s' st)
    (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec C hcaf coreWalkFuel e s CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun h w s' st ⟨hrun, hw, hs, _⟩ => ?_)
  subst hw
  have hret : ∀ (b : Bool) (wv : BitVec 64), wv = boolW b → ∀ {Γ : Env} {M : Mem} {D : List MlS},
      SpecR (σ := σ) (Inv C s' Γ M D) (.return (.const wv)) s' (pure b) (PostB C) :=
    fun b wv hwv {Γ M D} => specR_returnI _ wv rfl
      (fun t ht => ⟨C.H, List.prefix_refl _, hwv, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine Knot.specR_tagIteV nuH h 5 (by decide) (by decide) (by simp) (fun h5 => ?_) (fun h5 => ?_)
  · simp only [h5, show (UInt32.ofNat 5 == ETag.lam) = true by decide, ↓reduceIte]
    exact hret false 0 rfl
  refine Knot.specR_tagIteV nuH h 7 (by decide) (by decide) (by simp) (fun h7 => ?_) (fun h7 => ?_)
  · simp only [show (h.tag == ETag.lam) = false by simpa [ETag.lam] using h5, Bool.false_eq_true, ↓reduceIte, h7,
      show (UInt32.ofNat 7 == ETag.letE) = true by decide]
    exact hret false 0 rfl
  refine Knot.specR_tagIteV nuH h 0 (by decide) (by decide) (by simp) (fun h0 => ?_) (fun h0 => ?_)
  · simp only [show (h.tag == ETag.lam) = false by simpa [ETag.lam] using h5,
      show (h.tag == ETag.letE) = false by simpa [ETag.letE] using h7, Bool.false_eq_true, ↓reduceIte, h0,
      show (UInt32.ofNat 0 == ETag.bvar) = true by decide]
    exact hret false 0 rfl
  simp only [show (h.tag == ETag.lam) = false by simpa [ETag.lam] using h5,
    show (h.tag == ETag.letE) = false by simpa [ETag.letE] using h7,
    show (h.tag == ETag.bvar) = false by simpa [ETag.bvar] using h0, Bool.false_eq_true, ↓reduceIte]
  exact hret true 1 rfl

theorem ch_spec (C : Ctx) (hok : CtxOK C)
    (hcaf : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one))
    (hmg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hmp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (s : AState) (c : NIdx) (w : EIdx) :
    SpecR (σ := σ) (Pre C s (chParams.zip [Enc.idxW c, Enc.idxW w])) (chBody C) s (ctorHeadAgainst C.fe c w)
      (PostOBH C) := by
  refine specR_prologue (postOBH_locals C) (Knot.params_none C chLocals chParams _ (by decide) (by decide)) ?_
  unfold ctorHeadAgainst
  refine specR_callNIM (C := C) chH fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv chW]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW w] (by decide) rfl (by decide) hcaf
    ⟨rfl, by simp +decide [Env.get, chParams, ctxEnv], trivial⟩
    (fun a w' s' st => getAppFn coreWalkFuel w s = .ok (a, s') ∧ Post C s a w' s' st)
    (fun a w' s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec C hcaf coreWalkFuel w s CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun h w' s' st ⟨hrun, hw, hs, _⟩ => ?_)
  subst hw
  have hs' : s = s' := hs.symm
  subst hs'
  have hret : ∀ (o : Option Bool) {Γ : Env} {M : Mem} {D : List MlS} (e : ExpHOL 64), sev Γ e = some (LLeq.obW o) →
      SpecR (σ := σ) (Inv C s Γ M D) (.return e) s (pure o) (PostOBH C) :=
    fun o Γ M D e he => specR_returnI _ (LLeq.obW o) he
      (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine Knot.specR_tagIteV chH h 3 (by decide) (by decide) (by simp) (fun htc => ?_) (fun htc => ?_)
  swap
  · rw [if_neg (show ¬ (h.tag == ETag.const) = true by simpa [ETag.const] using htc)]
    exact hret none _ rfl
  rw [if_pos (show (h.tag == ETag.const) = true by simp [htc, ETag.const])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv chH) (Enc.idxW h) (by decide) (by simp) ?_
  refine specR_viewP h (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
    (fun v P hv htn _ => ?_)
  refine specR_congr (Big.view_bind_eq h v _ s hv) ?_
  have h3 : v.tagN = 3 := by rw [htn, htc]; rfl
  obtain ⟨d, us, rfl⟩ := UD.tagN_const h3
  dsimp only
  refine specR_loadI' chD (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW d) (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW d) [Enc.idxW us] []) ?_
  refine specR_dropM ?_
  by_cases hdc : d = c
  · subst hdc
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, chParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [beq_self_eq_true, ↓reduceIte]
    exact hret (some true) _ rfl
  have hne : Enc.idxW d ≠ Enc.idxW c := fun e => hdc (Enc.idxW_inj e)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, chParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only [show (d == c) = false by simpa using hdc, Bool.false_eq_true, ↓reduceIte]
  refine specR_envFindI hok hmg hmp chP (vv chD) d (by decide) (by simp) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  have hrel := find_rel hok d
  revert hrel
  rcases hfind : C.fe.find? d with _ | ci
  · intro hrel; simp only at hrel; rw [hrel]
    refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact hret none _ rfl
  intro ⟨o, hm, hci⟩
  rw [hm]
  refine specR_atEntry fun t ht => ?_
  have hoE : o < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI chQ _ (ecell C o) (by decide) (by simp [sev, optWG]; exact BitVec.add_sub_cancel _ _) ?_
  rcases ci with cv | ⟨cv, val, hint⟩ | cv | ⟨cv, caps⟩ | ⟨cv, np, nf, ind⟩ | ⟨cv, mi, rp, isK, rules⟩
  · refine specR_envLoadI chK (vv chQ) o 0 (by decide) (by simp) hci.2 ?_
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    exact hret none _ rfl
  · refine specR_envLoadI chK (vv chQ) o 1 (by decide) (by simp) hci.2.1 ?_
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    exact hret none _ rfl
  · refine specR_envLoadI chK (vv chQ) o 2 (by decide) (by simp) hci.2 ?_
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    exact hret none _ rfl
  · refine specR_envLoadI chK (vv chQ) o 3 (by decide) (by simp) hci.2.1 ?_
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    exact hret none _ rfl
  · refine specR_envLoadI chK (vv chQ) o 4 (by decide) (by simp) hci.2.1 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact hret (some false) _ rfl
  · refine specR_envLoadI chK (vv chQ) o 5 (by decide) (by simp) hci.2.1 ?_
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    exact hret none _ rfl

def PostON (C : Ctx) (o : Option NIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ w = optWG Enc.idxW o ∧ SR (ctxH C H') s' st

theorem postON_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostON C a w s' st → PostON C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', h1, h2, h3⟩ => ⟨H', h1, h2, sr_of_eq h3 rfl rfl rfl rfl⟩

theorem cq_spec (C : Ctx) (hok : CtxOK C) (hcF : ExF.CodesF C (ExF.bodyF C))
    (hfvb : C.code.lookup ExF.fFvarB = some ([(pFu, .one), (pH, .one)], ExF.fvbBody C, .one))
    (hhf : C.code.lookup ExM.fHasFvar = some ([(pFu, .one), (pH, .one)], ExM.hasFvarBody, .one))
    (hcaf : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one))
    (hmg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hmp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (hcna : C.code.lookup fNa = some (naParams.map (fun p => (p, ShapeHOL.one)), naBody, .one))
    (s : AState) (e : EIdx) :
    SpecR (σ := σ) (Pre C s [(cqE, Enc.idxW e)]) (cqBody C) s (ctorTarget C.fe e) (PostON C) := by
  refine specR_prologue (postON_locals C) (Knot.params_none C cqLocals [cqE] [Enc.idxW e] (by decide) (by decide)) ?_
  unfold ctorTarget
  refine specR_callNIM (C := C) cqX ExM.fHasFvar [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv cqE]
    ExM.hasFvarBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e] (by decide) rfl (by decide) hhf
    ⟨rfl, by simp +decide [Env.get, ctxEnv], trivial⟩ (ExM.PostB C) (fun _ _ _ _ hp => hp.2)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (ExM.hasFvar_spec C hok hcF hfvb s coreWalkFuel e CV.coreWalkFuel_lt))
    (fun x w s1 st ⟨hw, _⟩ => ?_)
  subst hw
  have hret : ∀ (o : Option NIdx) {Γ : Env} {M : Mem} {D : List MlS} (e : ExpHOL 64), sev Γ e = some (optWG Enc.idxW o) →
      SpecR (σ := σ) (Inv C s1 Γ M D) (.return e) s1 (pure o) (PostON C) :=
    fun o Γ M D e he => specR_returnI _ (optWG Enc.idxW o) he
      (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  cases x
  swap
  · refine specR_ifI _ 1 (by simp) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [↓reduceIte]
    exact hret none _ rfl
  refine specR_ifI _ 0 (by simp) (fun h => absurd rfl h) (fun _ => ?_)
  simp only [Bool.false_eq_true, ↓reduceIte]
  refine specR_callNIM (C := C) cqH fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv cqE]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e] (by decide) rfl (by decide) hcaf
    ⟨rfl, by simp +decide [Env.get, ctxEnv], trivial⟩
    (fun a w' s' st => getAppFn coreWalkFuel e s1 = .ok (a, s') ∧ Post C s1 a w' s' st)
    (fun a w' s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec C hcaf coreWalkFuel e s1 CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun h w' s' st ⟨hrun, hw, hs, _⟩ => ?_)
  subst hw
  have hs' : s1 = s' := hs.symm
  subst hs'
  refine Knot.specR_tagIteV cqH h 3 (by decide) (by decide) (by simp) (fun htc => ?_) (fun htc => ?_)
  swap
  · rw [if_neg (show ¬ (h.tag == ETag.const) = true by simpa [ETag.const] using htc)]
    exact hret none _ rfl
  rw [if_pos (show (h.tag == ETag.const) = true by simp [htc, ETag.const])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv cqH) (Enc.idxW h) (by decide) (by simp) ?_
  refine specR_viewP h (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
    (fun v P hv htn _ => ?_)
  refine specR_congr (Big.view_bind_eq h v _ s1 hv) ?_
  have h3 : v.tagN = 3 := by rw [htn, htc]; rfl
  obtain ⟨c, us, rfl⟩ := UD.tagN_const h3
  dsimp only
  refine specR_loadI' cqC (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW c) (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW c) [Enc.idxW us] []) ?_
  refine specR_dropM ?_
  refine specR_envFindI hok hmg hmp cqP (vv cqC) c (by decide) (by simp) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  have hrel := find_rel hok c
  revert hrel
  rcases hfind : C.fe.find? c with _ | ci
  · intro hrel; simp only at hrel; rw [hrel]
    refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact hret none _ rfl
  intro ⟨o, hm, hci⟩
  rw [hm]
  refine specR_atEntry fun t ht => ?_
  have hoE : o < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI cqQ _ (ecell C o) (by decide) (by simp [sev, optWG]; exact BitVec.add_sub_cancel _ _) ?_
  rcases ci with cv | ⟨cv, val, hint⟩ | cv | ⟨cv, caps⟩ | ⟨cv, np, nf, ind⟩ | ⟨cv, mi, rp, isK, rules⟩
  · refine specR_envLoadI cqK (vv cqQ) o 0 (by decide) (by simp) hci.2 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact hret none _ rfl
  · refine specR_envLoadI cqK (vv cqQ) o 1 (by decide) (by simp) hci.2.1 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact hret none _ rfl
  · refine specR_envLoadI cqK (vv cqQ) o 2 (by decide) (by simp) hci.2 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact hret none _ rfl
  · refine specR_envLoadI cqK (vv cqQ) o 3 (by decide) (by simp) hci.2.1 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact hret none _ rfl
  swap
  · refine specR_envLoadI cqK (vv cqQ) o 5 (by decide) (by simp) hci.2.1 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact hret none _ rfl
  refine specR_envLoadI cqK (vv cqQ) o 4 (by decide) (by simp) hci.2.1 ?_
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
  obtain ⟨_, _, ⟨hnp, hnpl⟩, ⟨hnf, hnfl⟩, hT⟩ := hci
  dsimp only
  refine specR_envLoadI cqNp (.op .add [vv cqQ, .const 32]) (o + 4) _ (by decide)
    (by simp [sev, vv]; simpa using ecell_add C o 4) hnp ?_
  refine specR_envLoadI cqNf (.op .add [vv cqQ, .const 40]) (o + 5) _ (by decide)
    (by simp [sev, vv]; simpa using ecell_add C o 5) hnf ?_
  refine specR_envLoadI cqT (.op .add [vv cqQ, .const 48]) (o + 6) _ (by decide)
    (by simp [sev, vv]; simpa using ecell_add C o 6) hT ?_
  unfold pinNat
  refine specR_pinAtI hok PIN_NAT (by decide) cqNn (by decide) ?_
  by_cases hTn : ind = C.pins.names[PIN_NAT]'(by rw [hok.pinsRel.1]; decide)
  · refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hTn]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [hTn, beq_self_eq_true, ↓reduceIte]
    exact hret none _ rfl
  have hTw : Enc.idxW ind ≠ Enc.idxW (C.pins.names[PIN_NAT]'(by rw [hok.pinsRel.1]; decide)) :=
    fun x => hTn (Enc.idxW_inj x)
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hTw]) (fun h => absurd rfl h) (fun _ => ?_)
  simp only [show (ind == C.pins.names[PIN_NAT]'(by rw [hok.pinsRel.1]; decide)) = false by simpa using hTn,
    Bool.false_eq_true, ↓reduceIte]
  refine specR_callNIM (C := C) cqN fNa naParams [.const (BitVec.ofNat 64 coreWalkFuel), vv cqE]
    naBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e] (by decide) rfl (by decide) hcna
    ⟨rfl, by simp +decide [Env.get, ctxEnv], trivial⟩
    (fun a w' s' st => PostNa C s1 coreWalkFuel a w' s' st)
    (fun a w' s' st ⟨hs, _, _, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu naParams _ rfl hlk)
      (na_spec C hcna coreWalkFuel e s1 (by unfold coreWalkFuel; decide)))
    (fun n w' s' st ⟨hs, hn, hw, _⟩ => ?_)
  subst hw hs
  have hnl : n < 2 ^ 63 := Nat.lt_of_le_of_lt hn (by unfold coreWalkFuel; decide)
  have hsum : BitVec.ofNat 64 np + BitVec.ofNat 64 nf = BitVec.ofNat 64 (np + nf) := BitVec.ofNat_add_ofNat ..
  by_cases hnn : n = np + nf
  swap
  · have hw : BitVec.ofNat 64 n ≠ BitVec.ofNat 64 (np + nf) := by
      intro x; apply hnn
      have := congrArg BitVec.toNat x
      simp only [BitVec.toNat_ofNat] at this
      rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hsum, hw]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [show (n == np + nf) = false by simpa using hnn, Bool.false_eq_true, ↓reduceIte]
    exact hret none _ rfl
  subst hnn
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hsum]) (fun h => absurd rfl h) (fun _ => ?_)
  simp only [beq_self_eq_true, ↓reduceIte]
  refine specR_envFindI hok hmg hmp cqP2 (vv cqT) ind (by decide) (by simp) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  have hrel := find_rel hok ind
  revert hrel
  rcases hfind : C.fe.find? ind with _ | ci
  · intro hrel; simp only at hrel; rw [hrel]
    refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact hret none _ rfl
  intro ⟨o2, hm, hci2⟩
  rw [hm]
  refine specR_atEntry fun t ht => ?_
  have hoE : o2 < C.EN := Nat.lt_of_lt_of_le (cie_lt hci2) ht.sr.env.1.len
  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI cqQ2 _ (ecell C o2) (by decide) (by simp [sev, optWG]; exact BitVec.add_sub_cancel _ _) ?_
  rcases ci with cv2 | ⟨cv2, val2, hint2⟩ | cv | ⟨cv2, caps⟩ | ⟨cv2, np2, nf2, ind2⟩ | ⟨cv2, mi, rp, isK, rules⟩
  · refine specR_envLoadI cqK2 (vv cqQ2) o2 0 (by decide) (by simp) hci2.2 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact hret none _ rfl
  · refine specR_envLoadI cqK2 (vv cqQ2) o2 1 (by decide) (by simp) hci2.2.1 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact hret none _ rfl
  · refine specR_envLoadI cqK2 (vv cqQ2) o2 2 (by decide) (by simp) hci2.2 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact hret none _ rfl
  swap
  · refine specR_envLoadI cqK2 (vv cqQ2) o2 4 (by decide) (by simp) hci2.2.1 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact hret none _ rfl
  swap
  · refine specR_envLoadI cqK2 (vv cqQ2) o2 5 (by decide) (by simp) hci2.2.1 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact hret none _ rfl
  refine specR_envLoadI cqK2 (vv cqQ2) o2 3 (by decide) (by simp) hci2.2.1 ?_
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
  obtain ⟨_, _, het, _, _, _, _, hnz⟩ := hci2
  dsimp only
  refine specR_envLoadI cqZ (.op .add [vv cqQ2, .const 72]) (o2 + 9) _ (by decide)
    (by simp [sev, vv]; simpa using ecell_add C o2 9) hnz ?_
  refine specR_envLoadI cqEt (.op .add [vv cqQ2, .const 32]) (o2 + 4) _ (by decide)
    (by simp [sev, vv]; simpa using ecell_add C o2 4) het ?_
  cases hz : caps.neverZero <;> cases he : caps.eta
  · refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    exact hret none _ rfl
  · refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    exact hret none _ rfl
  · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    exact hret (some c) _ (by simp [sev, optWG])
  · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact hret none _ rfl

theorem cf_spec (C : Ctx) (hok : CtxOK C) (hcF : ExF.CodesF C (ExF.bodyF C))
    (hfvb : C.code.lookup ExF.fFvarB = some ([(pFu, .one), (pH, .one)], ExF.fvbBody C, .one))
    (hhf : C.code.lookup ExM.fHasFvar = some ([(pFu, .one), (pH, .one)], ExM.hasFvarBody, .one))
    (hcaf : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one))
    (hmg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hmp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (hcna : C.code.lookup fNa = some (naParams.map (fun p => (p, ShapeHOL.one)), naBody, .one))
    (hcq : C.code.lookup fCq = some ([(cqE, .one)], cqBody C, .one))
    (v : Bool) (hv : C.side = v) (s : AState) (o e : EIdx) :
    SpecR (σ := σ) (Pre C s (cfParams.zip [Enc.idxW o, Enc.idxW e])) (cfBody v) s (ctorTargetFor C.fe v o e)
      (PostON C) := by
  have hcall : ∀ (s1 : AState) {Γ : Env} {M : Mem} {D : List MlS}, cfR ∈ D → sev Γ (vv cfE) = some (Enc.idxW e) →
      SpecR (σ := σ) (Inv C s1 Γ M D) (.seq (.call (some (some (.local, cfR), none)) fCq [vv cfE]) (.return (vv cfR)))
        s1 (ctorTarget C.fe e) (PostON C) := by
    intro s1 Γ M D hx he
    refine specR_congr (m' := ctorTarget C.fe e >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH cfR fCq [cqE] [vv cfE] (cqBody C) [Enc.idxW e] (by decide) rfl hx hcq ⟨he, trivial⟩
      (PostON C) (fun a w _ _ => w = optWG Enc.idxW a) (fun a w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [cqE] _ rfl hlk)
        (cq_spec C hok hcF hfvb hhf hcaf hmg hmp hcna s1 e))
      (fun a w s' H' hp hw => ?_)
    exact specR_returnI _ w (by simp) (fun t ht => ⟨H', hp, hw, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_prologue (postON_locals C) (Knot.params_none C [cfX, cfR] cfParams _ (by decide) (by decide)) ?_
  unfold ctorTargetFor
  refine specR_iteSide hok.eoNe (fun hs => ?_) (fun hs => ?_)
  rotate_left
  · have hv' : v = false := by rw [← hv, hs]
    subst hv'
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine specR_callNIM (C := C) cfX ExM.fHasFvar [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv cfO]
      ExM.hasFvarBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW o] (by decide) rfl (by decide) hhf
      ⟨rfl, by simp +decide [Env.get, cfParams, ctxEnv], trivial⟩ (ExM.PostB C) (fun _ _ _ _ hp => hp.2)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
        (ExM.hasFvar_spec C hok hcF hfvb s coreWalkFuel o CV.coreWalkFuel_lt))
      (fun x w s1 st ⟨hw, _⟩ => ?_)
    subst hw
    cases x
    · refine specR_ifI _ 0 (by simp) (fun h => absurd rfl h) (fun _ => ?_)
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact hcall s1 (by decide) (by simp +decide [Env.get, cfParams, ctxEnv])
    · refine specR_ifI _ 1 (by simp) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [↓reduceIte]
      exact specR_returnI _ (optWG Enc.idxW none) rfl
        (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · have hv' : v = true := by rw [← hv, hs]
    subst hv'
    simp only [↓reduceIte]
    exact hcall s (by decide) (by simp +decide [Env.get, cfParams, ctxEnv])

end

end ConPanqueque.T.WC
