import ConPanqueque.T.Core.DefeqSpine
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# The lazy-delta step's head readers

`unfoldableHead` (the head a stored definition used at its own level count: `boolW`), `headHint` (its
reducibility hint as `hintN`, `opaque` otherwise), `sameConstHeads` (two applications of the same constant).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def ukE := ofString "dhuk_e"
def ukH := ofString "dhuk_h"
def ukN := ofString "dhuk_n"
def ukU := ofString "dhuk_u"
def ukP := ofString "dhuk_p"
def ukQ := ofString "dhuk_q"
def ukK := ofString "dhuk_k"
def ukLp := ofString "dhuk_lp"
def ukLl := ofString "dhuk_ll"
def hnE := ofString "dhhn_e"
def hnH := ofString "dhhn_h"
def hnN := ofString "dhhn_n"
def hnP := ofString "dhhn_p"
def hnQ := ofString "dhhn_q"
def hnK := ofString "dhhn_k"
def hnV := ofString "dhhn_v"
def sqA := ofString "dhsq_a"
def sqB := ofString "dhsq_b"
def sqF1 := ofString "dhsq_f1"
def sqF2 := ofString "dhsq_f2"
def sqH := ofString "dhsq_h"
def sqN1 := ofString "dhsq_n1"
def sqH2 := ofString "dhsq_h2"
def sqN2 := ofString "dhsq_n2"
def fUk := ofString "unfoldableHead"
def fHn := ofString "headHint"
def fSq := ofString "sameConstHeads"

@[simp] theorem dh_ukE_ne_ukH : ukE ≠ ukH := by decide
@[simp] theorem dh_ukE_ne_ukN : ukE ≠ ukN := by decide
@[simp] theorem dh_ukE_ne_ukU : ukE ≠ ukU := by decide
@[simp] theorem dh_ukE_ne_ukP : ukE ≠ ukP := by decide
@[simp] theorem dh_ukE_ne_ukQ : ukE ≠ ukQ := by decide
@[simp] theorem dh_ukE_ne_ukK : ukE ≠ ukK := by decide
@[simp] theorem dh_ukE_ne_ukLp : ukE ≠ ukLp := by decide
@[simp] theorem dh_ukE_ne_ukLl : ukE ≠ ukLl := by decide
@[simp] theorem dh_ukE_ne_hnE : ukE ≠ hnE := by decide
@[simp] theorem dh_ukE_ne_hnH : ukE ≠ hnH := by decide
@[simp] theorem dh_ukE_ne_hnN : ukE ≠ hnN := by decide
@[simp] theorem dh_ukE_ne_hnP : ukE ≠ hnP := by decide
@[simp] theorem dh_ukE_ne_hnQ : ukE ≠ hnQ := by decide
@[simp] theorem dh_ukE_ne_hnK : ukE ≠ hnK := by decide
@[simp] theorem dh_ukE_ne_hnV : ukE ≠ hnV := by decide
@[simp] theorem dh_ukE_ne_sqA : ukE ≠ sqA := by decide
@[simp] theorem dh_ukE_ne_sqB : ukE ≠ sqB := by decide
@[simp] theorem dh_ukE_ne_sqF1 : ukE ≠ sqF1 := by decide
@[simp] theorem dh_ukE_ne_sqF2 : ukE ≠ sqF2 := by decide
@[simp] theorem dh_ukE_ne_sqH : ukE ≠ sqH := by decide
@[simp] theorem dh_ukE_ne_sqN1 : ukE ≠ sqN1 := by decide
@[simp] theorem dh_ukE_ne_sqH2 : ukE ≠ sqH2 := by decide
@[simp] theorem dh_ukE_ne_sqN2 : ukE ≠ sqN2 := by decide
@[simp] theorem dh_ukE_ne_lFl : ukE ≠ lFl := by decide
@[simp] theorem dh_lFl_ne_ukE : lFl ≠ ukE := by decide
@[simp] theorem dh_ukE_ne_lDh : ukE ≠ lDh := by decide
@[simp] theorem dh_lDh_ne_ukE : lDh ≠ ukE := by decide
@[simp] theorem dh_ukE_ne_lDt : ukE ≠ lDt := by decide
@[simp] theorem dh_lDt_ne_ukE : lDt ≠ ukE := by decide
@[simp] theorem dh_ukE_ne_lDg : ukE ≠ lDg := by decide
@[simp] theorem dh_lDg_ne_ukE : lDg ≠ ukE := by decide
@[simp] theorem dh_ukE_ne_lDi : ukE ≠ lDi := by decide
@[simp] theorem dh_lDi_ne_ukE : lDi ≠ ukE := by decide
@[simp] theorem dh_ukE_ne_lRp : ukE ≠ lRp := by decide
@[simp] theorem dh_lRp_ne_ukE : lRp ≠ ukE := by decide
@[simp] theorem dh_ukE_ne_lRn : ukE ≠ lRn := by decide
@[simp] theorem dh_lRn_ne_ukE : lRn ≠ ukE := by decide
@[simp] theorem dh_ukE_ne_lFle : ukE ≠ lFle := by decide
@[simp] theorem dh_lFle_ne_ukE : lFle ≠ ukE := by decide
@[simp] theorem dh_ukE_ne_lKb : ukE ≠ lKb := by decide
@[simp] theorem dh_lKb_ne_ukE : lKb ≠ ukE := by decide
@[simp] theorem dh_ukE_ne_lDir : ukE ≠ lDir := by decide
@[simp] theorem dh_lDir_ne_ukE : lDir ≠ ukE := by decide
@[simp] theorem dh_ukE_ne_lFln : ukE ≠ lFln := by decide
@[simp] theorem dh_lFln_ne_ukE : lFln ≠ ukE := by decide
@[simp] theorem dh_ukE_ne_lFll : ukE ≠ lFll := by decide
@[simp] theorem dh_lFll_ne_ukE : lFll ≠ ukE := by decide
@[simp] theorem dh_ukE_ne_lFls : ukE ≠ lFls := by decide
@[simp] theorem dh_lFls_ne_ukE : lFls ≠ ukE := by decide
@[simp] theorem dh_ukH_ne_ukE : ukH ≠ ukE := by decide
@[simp] theorem dh_ukH_ne_ukN : ukH ≠ ukN := by decide
@[simp] theorem dh_ukH_ne_ukU : ukH ≠ ukU := by decide
@[simp] theorem dh_ukH_ne_ukP : ukH ≠ ukP := by decide
@[simp] theorem dh_ukH_ne_ukQ : ukH ≠ ukQ := by decide
@[simp] theorem dh_ukH_ne_ukK : ukH ≠ ukK := by decide
@[simp] theorem dh_ukH_ne_ukLp : ukH ≠ ukLp := by decide
@[simp] theorem dh_ukH_ne_ukLl : ukH ≠ ukLl := by decide
@[simp] theorem dh_ukH_ne_hnE : ukH ≠ hnE := by decide
@[simp] theorem dh_ukH_ne_hnH : ukH ≠ hnH := by decide
@[simp] theorem dh_ukH_ne_hnN : ukH ≠ hnN := by decide
@[simp] theorem dh_ukH_ne_hnP : ukH ≠ hnP := by decide
@[simp] theorem dh_ukH_ne_hnQ : ukH ≠ hnQ := by decide
@[simp] theorem dh_ukH_ne_hnK : ukH ≠ hnK := by decide
@[simp] theorem dh_ukH_ne_hnV : ukH ≠ hnV := by decide
@[simp] theorem dh_ukH_ne_sqA : ukH ≠ sqA := by decide
@[simp] theorem dh_ukH_ne_sqB : ukH ≠ sqB := by decide
@[simp] theorem dh_ukH_ne_sqF1 : ukH ≠ sqF1 := by decide
@[simp] theorem dh_ukH_ne_sqF2 : ukH ≠ sqF2 := by decide
@[simp] theorem dh_ukH_ne_sqH : ukH ≠ sqH := by decide
@[simp] theorem dh_ukH_ne_sqN1 : ukH ≠ sqN1 := by decide
@[simp] theorem dh_ukH_ne_sqH2 : ukH ≠ sqH2 := by decide
@[simp] theorem dh_ukH_ne_sqN2 : ukH ≠ sqN2 := by decide
@[simp] theorem dh_ukH_ne_lFl : ukH ≠ lFl := by decide
@[simp] theorem dh_lFl_ne_ukH : lFl ≠ ukH := by decide
@[simp] theorem dh_ukH_ne_lDh : ukH ≠ lDh := by decide
@[simp] theorem dh_lDh_ne_ukH : lDh ≠ ukH := by decide
@[simp] theorem dh_ukH_ne_lDt : ukH ≠ lDt := by decide
@[simp] theorem dh_lDt_ne_ukH : lDt ≠ ukH := by decide
@[simp] theorem dh_ukH_ne_lDg : ukH ≠ lDg := by decide
@[simp] theorem dh_lDg_ne_ukH : lDg ≠ ukH := by decide
@[simp] theorem dh_ukH_ne_lDi : ukH ≠ lDi := by decide
@[simp] theorem dh_lDi_ne_ukH : lDi ≠ ukH := by decide
@[simp] theorem dh_ukH_ne_lRp : ukH ≠ lRp := by decide
@[simp] theorem dh_lRp_ne_ukH : lRp ≠ ukH := by decide
@[simp] theorem dh_ukH_ne_lRn : ukH ≠ lRn := by decide
@[simp] theorem dh_lRn_ne_ukH : lRn ≠ ukH := by decide
@[simp] theorem dh_ukH_ne_lFle : ukH ≠ lFle := by decide
@[simp] theorem dh_lFle_ne_ukH : lFle ≠ ukH := by decide
@[simp] theorem dh_ukH_ne_lKb : ukH ≠ lKb := by decide
@[simp] theorem dh_lKb_ne_ukH : lKb ≠ ukH := by decide
@[simp] theorem dh_ukH_ne_lDir : ukH ≠ lDir := by decide
@[simp] theorem dh_lDir_ne_ukH : lDir ≠ ukH := by decide
@[simp] theorem dh_ukH_ne_lFln : ukH ≠ lFln := by decide
@[simp] theorem dh_lFln_ne_ukH : lFln ≠ ukH := by decide
@[simp] theorem dh_ukH_ne_lFll : ukH ≠ lFll := by decide
@[simp] theorem dh_lFll_ne_ukH : lFll ≠ ukH := by decide
@[simp] theorem dh_ukH_ne_lFls : ukH ≠ lFls := by decide
@[simp] theorem dh_lFls_ne_ukH : lFls ≠ ukH := by decide
@[simp] theorem dh_ukN_ne_ukE : ukN ≠ ukE := by decide
@[simp] theorem dh_ukN_ne_ukH : ukN ≠ ukH := by decide
@[simp] theorem dh_ukN_ne_ukU : ukN ≠ ukU := by decide
@[simp] theorem dh_ukN_ne_ukP : ukN ≠ ukP := by decide
@[simp] theorem dh_ukN_ne_ukQ : ukN ≠ ukQ := by decide
@[simp] theorem dh_ukN_ne_ukK : ukN ≠ ukK := by decide
@[simp] theorem dh_ukN_ne_ukLp : ukN ≠ ukLp := by decide
@[simp] theorem dh_ukN_ne_ukLl : ukN ≠ ukLl := by decide
@[simp] theorem dh_ukN_ne_hnE : ukN ≠ hnE := by decide
@[simp] theorem dh_ukN_ne_hnH : ukN ≠ hnH := by decide
@[simp] theorem dh_ukN_ne_hnN : ukN ≠ hnN := by decide
@[simp] theorem dh_ukN_ne_hnP : ukN ≠ hnP := by decide
@[simp] theorem dh_ukN_ne_hnQ : ukN ≠ hnQ := by decide
@[simp] theorem dh_ukN_ne_hnK : ukN ≠ hnK := by decide
@[simp] theorem dh_ukN_ne_hnV : ukN ≠ hnV := by decide
@[simp] theorem dh_ukN_ne_sqA : ukN ≠ sqA := by decide
@[simp] theorem dh_ukN_ne_sqB : ukN ≠ sqB := by decide
@[simp] theorem dh_ukN_ne_sqF1 : ukN ≠ sqF1 := by decide
@[simp] theorem dh_ukN_ne_sqF2 : ukN ≠ sqF2 := by decide
@[simp] theorem dh_ukN_ne_sqH : ukN ≠ sqH := by decide
@[simp] theorem dh_ukN_ne_sqN1 : ukN ≠ sqN1 := by decide
@[simp] theorem dh_ukN_ne_sqH2 : ukN ≠ sqH2 := by decide
@[simp] theorem dh_ukN_ne_sqN2 : ukN ≠ sqN2 := by decide
@[simp] theorem dh_ukN_ne_lFl : ukN ≠ lFl := by decide
@[simp] theorem dh_lFl_ne_ukN : lFl ≠ ukN := by decide
@[simp] theorem dh_ukN_ne_lDh : ukN ≠ lDh := by decide
@[simp] theorem dh_lDh_ne_ukN : lDh ≠ ukN := by decide
@[simp] theorem dh_ukN_ne_lDt : ukN ≠ lDt := by decide
@[simp] theorem dh_lDt_ne_ukN : lDt ≠ ukN := by decide
@[simp] theorem dh_ukN_ne_lDg : ukN ≠ lDg := by decide
@[simp] theorem dh_lDg_ne_ukN : lDg ≠ ukN := by decide
@[simp] theorem dh_ukN_ne_lDi : ukN ≠ lDi := by decide
@[simp] theorem dh_lDi_ne_ukN : lDi ≠ ukN := by decide
@[simp] theorem dh_ukN_ne_lRp : ukN ≠ lRp := by decide
@[simp] theorem dh_lRp_ne_ukN : lRp ≠ ukN := by decide
@[simp] theorem dh_ukN_ne_lRn : ukN ≠ lRn := by decide
@[simp] theorem dh_lRn_ne_ukN : lRn ≠ ukN := by decide
@[simp] theorem dh_ukN_ne_lFle : ukN ≠ lFle := by decide
@[simp] theorem dh_lFle_ne_ukN : lFle ≠ ukN := by decide
@[simp] theorem dh_ukN_ne_lKb : ukN ≠ lKb := by decide
@[simp] theorem dh_lKb_ne_ukN : lKb ≠ ukN := by decide
@[simp] theorem dh_ukN_ne_lDir : ukN ≠ lDir := by decide
@[simp] theorem dh_lDir_ne_ukN : lDir ≠ ukN := by decide
@[simp] theorem dh_ukN_ne_lFln : ukN ≠ lFln := by decide
@[simp] theorem dh_lFln_ne_ukN : lFln ≠ ukN := by decide
@[simp] theorem dh_ukN_ne_lFll : ukN ≠ lFll := by decide
@[simp] theorem dh_lFll_ne_ukN : lFll ≠ ukN := by decide
@[simp] theorem dh_ukN_ne_lFls : ukN ≠ lFls := by decide
@[simp] theorem dh_lFls_ne_ukN : lFls ≠ ukN := by decide
@[simp] theorem dh_ukU_ne_ukE : ukU ≠ ukE := by decide
@[simp] theorem dh_ukU_ne_ukH : ukU ≠ ukH := by decide
@[simp] theorem dh_ukU_ne_ukN : ukU ≠ ukN := by decide
@[simp] theorem dh_ukU_ne_ukP : ukU ≠ ukP := by decide
@[simp] theorem dh_ukU_ne_ukQ : ukU ≠ ukQ := by decide
@[simp] theorem dh_ukU_ne_ukK : ukU ≠ ukK := by decide
@[simp] theorem dh_ukU_ne_ukLp : ukU ≠ ukLp := by decide
@[simp] theorem dh_ukU_ne_ukLl : ukU ≠ ukLl := by decide
@[simp] theorem dh_ukU_ne_hnE : ukU ≠ hnE := by decide
@[simp] theorem dh_ukU_ne_hnH : ukU ≠ hnH := by decide
@[simp] theorem dh_ukU_ne_hnN : ukU ≠ hnN := by decide
@[simp] theorem dh_ukU_ne_hnP : ukU ≠ hnP := by decide
@[simp] theorem dh_ukU_ne_hnQ : ukU ≠ hnQ := by decide
@[simp] theorem dh_ukU_ne_hnK : ukU ≠ hnK := by decide
@[simp] theorem dh_ukU_ne_hnV : ukU ≠ hnV := by decide
@[simp] theorem dh_ukU_ne_sqA : ukU ≠ sqA := by decide
@[simp] theorem dh_ukU_ne_sqB : ukU ≠ sqB := by decide
@[simp] theorem dh_ukU_ne_sqF1 : ukU ≠ sqF1 := by decide
@[simp] theorem dh_ukU_ne_sqF2 : ukU ≠ sqF2 := by decide
@[simp] theorem dh_ukU_ne_sqH : ukU ≠ sqH := by decide
@[simp] theorem dh_ukU_ne_sqN1 : ukU ≠ sqN1 := by decide
@[simp] theorem dh_ukU_ne_sqH2 : ukU ≠ sqH2 := by decide
@[simp] theorem dh_ukU_ne_sqN2 : ukU ≠ sqN2 := by decide
@[simp] theorem dh_ukU_ne_lFl : ukU ≠ lFl := by decide
@[simp] theorem dh_lFl_ne_ukU : lFl ≠ ukU := by decide
@[simp] theorem dh_ukU_ne_lDh : ukU ≠ lDh := by decide
@[simp] theorem dh_lDh_ne_ukU : lDh ≠ ukU := by decide
@[simp] theorem dh_ukU_ne_lDt : ukU ≠ lDt := by decide
@[simp] theorem dh_lDt_ne_ukU : lDt ≠ ukU := by decide
@[simp] theorem dh_ukU_ne_lDg : ukU ≠ lDg := by decide
@[simp] theorem dh_lDg_ne_ukU : lDg ≠ ukU := by decide
@[simp] theorem dh_ukU_ne_lDi : ukU ≠ lDi := by decide
@[simp] theorem dh_lDi_ne_ukU : lDi ≠ ukU := by decide
@[simp] theorem dh_ukU_ne_lRp : ukU ≠ lRp := by decide
@[simp] theorem dh_lRp_ne_ukU : lRp ≠ ukU := by decide
@[simp] theorem dh_ukU_ne_lRn : ukU ≠ lRn := by decide
@[simp] theorem dh_lRn_ne_ukU : lRn ≠ ukU := by decide
@[simp] theorem dh_ukU_ne_lFle : ukU ≠ lFle := by decide
@[simp] theorem dh_lFle_ne_ukU : lFle ≠ ukU := by decide
@[simp] theorem dh_ukU_ne_lKb : ukU ≠ lKb := by decide
@[simp] theorem dh_lKb_ne_ukU : lKb ≠ ukU := by decide
@[simp] theorem dh_ukU_ne_lDir : ukU ≠ lDir := by decide
@[simp] theorem dh_lDir_ne_ukU : lDir ≠ ukU := by decide
@[simp] theorem dh_ukU_ne_lFln : ukU ≠ lFln := by decide
@[simp] theorem dh_lFln_ne_ukU : lFln ≠ ukU := by decide
@[simp] theorem dh_ukU_ne_lFll : ukU ≠ lFll := by decide
@[simp] theorem dh_lFll_ne_ukU : lFll ≠ ukU := by decide
@[simp] theorem dh_ukU_ne_lFls : ukU ≠ lFls := by decide
@[simp] theorem dh_lFls_ne_ukU : lFls ≠ ukU := by decide
@[simp] theorem dh_ukP_ne_ukE : ukP ≠ ukE := by decide
@[simp] theorem dh_ukP_ne_ukH : ukP ≠ ukH := by decide
@[simp] theorem dh_ukP_ne_ukN : ukP ≠ ukN := by decide
@[simp] theorem dh_ukP_ne_ukU : ukP ≠ ukU := by decide
@[simp] theorem dh_ukP_ne_ukQ : ukP ≠ ukQ := by decide
@[simp] theorem dh_ukP_ne_ukK : ukP ≠ ukK := by decide
@[simp] theorem dh_ukP_ne_ukLp : ukP ≠ ukLp := by decide
@[simp] theorem dh_ukP_ne_ukLl : ukP ≠ ukLl := by decide
@[simp] theorem dh_ukP_ne_hnE : ukP ≠ hnE := by decide
@[simp] theorem dh_ukP_ne_hnH : ukP ≠ hnH := by decide
@[simp] theorem dh_ukP_ne_hnN : ukP ≠ hnN := by decide
@[simp] theorem dh_ukP_ne_hnP : ukP ≠ hnP := by decide
@[simp] theorem dh_ukP_ne_hnQ : ukP ≠ hnQ := by decide
@[simp] theorem dh_ukP_ne_hnK : ukP ≠ hnK := by decide
@[simp] theorem dh_ukP_ne_hnV : ukP ≠ hnV := by decide
@[simp] theorem dh_ukP_ne_sqA : ukP ≠ sqA := by decide
@[simp] theorem dh_ukP_ne_sqB : ukP ≠ sqB := by decide
@[simp] theorem dh_ukP_ne_sqF1 : ukP ≠ sqF1 := by decide
@[simp] theorem dh_ukP_ne_sqF2 : ukP ≠ sqF2 := by decide
@[simp] theorem dh_ukP_ne_sqH : ukP ≠ sqH := by decide
@[simp] theorem dh_ukP_ne_sqN1 : ukP ≠ sqN1 := by decide
@[simp] theorem dh_ukP_ne_sqH2 : ukP ≠ sqH2 := by decide
@[simp] theorem dh_ukP_ne_sqN2 : ukP ≠ sqN2 := by decide
@[simp] theorem dh_ukP_ne_lFl : ukP ≠ lFl := by decide
@[simp] theorem dh_lFl_ne_ukP : lFl ≠ ukP := by decide
@[simp] theorem dh_ukP_ne_lDh : ukP ≠ lDh := by decide
@[simp] theorem dh_lDh_ne_ukP : lDh ≠ ukP := by decide
@[simp] theorem dh_ukP_ne_lDt : ukP ≠ lDt := by decide
@[simp] theorem dh_lDt_ne_ukP : lDt ≠ ukP := by decide
@[simp] theorem dh_ukP_ne_lDg : ukP ≠ lDg := by decide
@[simp] theorem dh_lDg_ne_ukP : lDg ≠ ukP := by decide
@[simp] theorem dh_ukP_ne_lDi : ukP ≠ lDi := by decide
@[simp] theorem dh_lDi_ne_ukP : lDi ≠ ukP := by decide
@[simp] theorem dh_ukP_ne_lRp : ukP ≠ lRp := by decide
@[simp] theorem dh_lRp_ne_ukP : lRp ≠ ukP := by decide
@[simp] theorem dh_ukP_ne_lRn : ukP ≠ lRn := by decide
@[simp] theorem dh_lRn_ne_ukP : lRn ≠ ukP := by decide
@[simp] theorem dh_ukP_ne_lFle : ukP ≠ lFle := by decide
@[simp] theorem dh_lFle_ne_ukP : lFle ≠ ukP := by decide
@[simp] theorem dh_ukP_ne_lKb : ukP ≠ lKb := by decide
@[simp] theorem dh_lKb_ne_ukP : lKb ≠ ukP := by decide
@[simp] theorem dh_ukP_ne_lDir : ukP ≠ lDir := by decide
@[simp] theorem dh_lDir_ne_ukP : lDir ≠ ukP := by decide
@[simp] theorem dh_ukP_ne_lFln : ukP ≠ lFln := by decide
@[simp] theorem dh_lFln_ne_ukP : lFln ≠ ukP := by decide
@[simp] theorem dh_ukP_ne_lFll : ukP ≠ lFll := by decide
@[simp] theorem dh_lFll_ne_ukP : lFll ≠ ukP := by decide
@[simp] theorem dh_ukP_ne_lFls : ukP ≠ lFls := by decide
@[simp] theorem dh_lFls_ne_ukP : lFls ≠ ukP := by decide
@[simp] theorem dh_ukQ_ne_ukE : ukQ ≠ ukE := by decide
@[simp] theorem dh_ukQ_ne_ukH : ukQ ≠ ukH := by decide
@[simp] theorem dh_ukQ_ne_ukN : ukQ ≠ ukN := by decide
@[simp] theorem dh_ukQ_ne_ukU : ukQ ≠ ukU := by decide
@[simp] theorem dh_ukQ_ne_ukP : ukQ ≠ ukP := by decide
@[simp] theorem dh_ukQ_ne_ukK : ukQ ≠ ukK := by decide
@[simp] theorem dh_ukQ_ne_ukLp : ukQ ≠ ukLp := by decide
@[simp] theorem dh_ukQ_ne_ukLl : ukQ ≠ ukLl := by decide
@[simp] theorem dh_ukQ_ne_hnE : ukQ ≠ hnE := by decide
@[simp] theorem dh_ukQ_ne_hnH : ukQ ≠ hnH := by decide
@[simp] theorem dh_ukQ_ne_hnN : ukQ ≠ hnN := by decide
@[simp] theorem dh_ukQ_ne_hnP : ukQ ≠ hnP := by decide
@[simp] theorem dh_ukQ_ne_hnQ : ukQ ≠ hnQ := by decide
@[simp] theorem dh_ukQ_ne_hnK : ukQ ≠ hnK := by decide
@[simp] theorem dh_ukQ_ne_hnV : ukQ ≠ hnV := by decide
@[simp] theorem dh_ukQ_ne_sqA : ukQ ≠ sqA := by decide
@[simp] theorem dh_ukQ_ne_sqB : ukQ ≠ sqB := by decide
@[simp] theorem dh_ukQ_ne_sqF1 : ukQ ≠ sqF1 := by decide
@[simp] theorem dh_ukQ_ne_sqF2 : ukQ ≠ sqF2 := by decide
@[simp] theorem dh_ukQ_ne_sqH : ukQ ≠ sqH := by decide
@[simp] theorem dh_ukQ_ne_sqN1 : ukQ ≠ sqN1 := by decide
@[simp] theorem dh_ukQ_ne_sqH2 : ukQ ≠ sqH2 := by decide
@[simp] theorem dh_ukQ_ne_sqN2 : ukQ ≠ sqN2 := by decide
@[simp] theorem dh_ukQ_ne_lFl : ukQ ≠ lFl := by decide
@[simp] theorem dh_lFl_ne_ukQ : lFl ≠ ukQ := by decide
@[simp] theorem dh_ukQ_ne_lDh : ukQ ≠ lDh := by decide
@[simp] theorem dh_lDh_ne_ukQ : lDh ≠ ukQ := by decide
@[simp] theorem dh_ukQ_ne_lDt : ukQ ≠ lDt := by decide
@[simp] theorem dh_lDt_ne_ukQ : lDt ≠ ukQ := by decide
@[simp] theorem dh_ukQ_ne_lDg : ukQ ≠ lDg := by decide
@[simp] theorem dh_lDg_ne_ukQ : lDg ≠ ukQ := by decide
@[simp] theorem dh_ukQ_ne_lDi : ukQ ≠ lDi := by decide
@[simp] theorem dh_lDi_ne_ukQ : lDi ≠ ukQ := by decide
@[simp] theorem dh_ukQ_ne_lRp : ukQ ≠ lRp := by decide
@[simp] theorem dh_lRp_ne_ukQ : lRp ≠ ukQ := by decide
@[simp] theorem dh_ukQ_ne_lRn : ukQ ≠ lRn := by decide
@[simp] theorem dh_lRn_ne_ukQ : lRn ≠ ukQ := by decide
@[simp] theorem dh_ukQ_ne_lFle : ukQ ≠ lFle := by decide
@[simp] theorem dh_lFle_ne_ukQ : lFle ≠ ukQ := by decide
@[simp] theorem dh_ukQ_ne_lKb : ukQ ≠ lKb := by decide
@[simp] theorem dh_lKb_ne_ukQ : lKb ≠ ukQ := by decide
@[simp] theorem dh_ukQ_ne_lDir : ukQ ≠ lDir := by decide
@[simp] theorem dh_lDir_ne_ukQ : lDir ≠ ukQ := by decide
@[simp] theorem dh_ukQ_ne_lFln : ukQ ≠ lFln := by decide
@[simp] theorem dh_lFln_ne_ukQ : lFln ≠ ukQ := by decide
@[simp] theorem dh_ukQ_ne_lFll : ukQ ≠ lFll := by decide
@[simp] theorem dh_lFll_ne_ukQ : lFll ≠ ukQ := by decide
@[simp] theorem dh_ukQ_ne_lFls : ukQ ≠ lFls := by decide
@[simp] theorem dh_lFls_ne_ukQ : lFls ≠ ukQ := by decide
@[simp] theorem dh_ukK_ne_ukE : ukK ≠ ukE := by decide
@[simp] theorem dh_ukK_ne_ukH : ukK ≠ ukH := by decide
@[simp] theorem dh_ukK_ne_ukN : ukK ≠ ukN := by decide
@[simp] theorem dh_ukK_ne_ukU : ukK ≠ ukU := by decide
@[simp] theorem dh_ukK_ne_ukP : ukK ≠ ukP := by decide
@[simp] theorem dh_ukK_ne_ukQ : ukK ≠ ukQ := by decide
@[simp] theorem dh_ukK_ne_ukLp : ukK ≠ ukLp := by decide
@[simp] theorem dh_ukK_ne_ukLl : ukK ≠ ukLl := by decide
@[simp] theorem dh_ukK_ne_hnE : ukK ≠ hnE := by decide
@[simp] theorem dh_ukK_ne_hnH : ukK ≠ hnH := by decide
@[simp] theorem dh_ukK_ne_hnN : ukK ≠ hnN := by decide
@[simp] theorem dh_ukK_ne_hnP : ukK ≠ hnP := by decide
@[simp] theorem dh_ukK_ne_hnQ : ukK ≠ hnQ := by decide
@[simp] theorem dh_ukK_ne_hnK : ukK ≠ hnK := by decide
@[simp] theorem dh_ukK_ne_hnV : ukK ≠ hnV := by decide
@[simp] theorem dh_ukK_ne_sqA : ukK ≠ sqA := by decide
@[simp] theorem dh_ukK_ne_sqB : ukK ≠ sqB := by decide
@[simp] theorem dh_ukK_ne_sqF1 : ukK ≠ sqF1 := by decide
@[simp] theorem dh_ukK_ne_sqF2 : ukK ≠ sqF2 := by decide
@[simp] theorem dh_ukK_ne_sqH : ukK ≠ sqH := by decide
@[simp] theorem dh_ukK_ne_sqN1 : ukK ≠ sqN1 := by decide
@[simp] theorem dh_ukK_ne_sqH2 : ukK ≠ sqH2 := by decide
@[simp] theorem dh_ukK_ne_sqN2 : ukK ≠ sqN2 := by decide
@[simp] theorem dh_ukK_ne_lFl : ukK ≠ lFl := by decide
@[simp] theorem dh_lFl_ne_ukK : lFl ≠ ukK := by decide
@[simp] theorem dh_ukK_ne_lDh : ukK ≠ lDh := by decide
@[simp] theorem dh_lDh_ne_ukK : lDh ≠ ukK := by decide
@[simp] theorem dh_ukK_ne_lDt : ukK ≠ lDt := by decide
@[simp] theorem dh_lDt_ne_ukK : lDt ≠ ukK := by decide
@[simp] theorem dh_ukK_ne_lDg : ukK ≠ lDg := by decide
@[simp] theorem dh_lDg_ne_ukK : lDg ≠ ukK := by decide
@[simp] theorem dh_ukK_ne_lDi : ukK ≠ lDi := by decide
@[simp] theorem dh_lDi_ne_ukK : lDi ≠ ukK := by decide
@[simp] theorem dh_ukK_ne_lRp : ukK ≠ lRp := by decide
@[simp] theorem dh_lRp_ne_ukK : lRp ≠ ukK := by decide
@[simp] theorem dh_ukK_ne_lRn : ukK ≠ lRn := by decide
@[simp] theorem dh_lRn_ne_ukK : lRn ≠ ukK := by decide
@[simp] theorem dh_ukK_ne_lFle : ukK ≠ lFle := by decide
@[simp] theorem dh_lFle_ne_ukK : lFle ≠ ukK := by decide
@[simp] theorem dh_ukK_ne_lKb : ukK ≠ lKb := by decide
@[simp] theorem dh_lKb_ne_ukK : lKb ≠ ukK := by decide
@[simp] theorem dh_ukK_ne_lDir : ukK ≠ lDir := by decide
@[simp] theorem dh_lDir_ne_ukK : lDir ≠ ukK := by decide
@[simp] theorem dh_ukK_ne_lFln : ukK ≠ lFln := by decide
@[simp] theorem dh_lFln_ne_ukK : lFln ≠ ukK := by decide
@[simp] theorem dh_ukK_ne_lFll : ukK ≠ lFll := by decide
@[simp] theorem dh_lFll_ne_ukK : lFll ≠ ukK := by decide
@[simp] theorem dh_ukK_ne_lFls : ukK ≠ lFls := by decide
@[simp] theorem dh_lFls_ne_ukK : lFls ≠ ukK := by decide
@[simp] theorem dh_ukLp_ne_ukE : ukLp ≠ ukE := by decide
@[simp] theorem dh_ukLp_ne_ukH : ukLp ≠ ukH := by decide
@[simp] theorem dh_ukLp_ne_ukN : ukLp ≠ ukN := by decide
@[simp] theorem dh_ukLp_ne_ukU : ukLp ≠ ukU := by decide
@[simp] theorem dh_ukLp_ne_ukP : ukLp ≠ ukP := by decide
@[simp] theorem dh_ukLp_ne_ukQ : ukLp ≠ ukQ := by decide
@[simp] theorem dh_ukLp_ne_ukK : ukLp ≠ ukK := by decide
@[simp] theorem dh_ukLp_ne_ukLl : ukLp ≠ ukLl := by decide
@[simp] theorem dh_ukLp_ne_hnE : ukLp ≠ hnE := by decide
@[simp] theorem dh_ukLp_ne_hnH : ukLp ≠ hnH := by decide
@[simp] theorem dh_ukLp_ne_hnN : ukLp ≠ hnN := by decide
@[simp] theorem dh_ukLp_ne_hnP : ukLp ≠ hnP := by decide
@[simp] theorem dh_ukLp_ne_hnQ : ukLp ≠ hnQ := by decide
@[simp] theorem dh_ukLp_ne_hnK : ukLp ≠ hnK := by decide
@[simp] theorem dh_ukLp_ne_hnV : ukLp ≠ hnV := by decide
@[simp] theorem dh_ukLp_ne_sqA : ukLp ≠ sqA := by decide
@[simp] theorem dh_ukLp_ne_sqB : ukLp ≠ sqB := by decide
@[simp] theorem dh_ukLp_ne_sqF1 : ukLp ≠ sqF1 := by decide
@[simp] theorem dh_ukLp_ne_sqF2 : ukLp ≠ sqF2 := by decide
@[simp] theorem dh_ukLp_ne_sqH : ukLp ≠ sqH := by decide
@[simp] theorem dh_ukLp_ne_sqN1 : ukLp ≠ sqN1 := by decide
@[simp] theorem dh_ukLp_ne_sqH2 : ukLp ≠ sqH2 := by decide
@[simp] theorem dh_ukLp_ne_sqN2 : ukLp ≠ sqN2 := by decide
@[simp] theorem dh_ukLp_ne_lFl : ukLp ≠ lFl := by decide
@[simp] theorem dh_lFl_ne_ukLp : lFl ≠ ukLp := by decide
@[simp] theorem dh_ukLp_ne_lDh : ukLp ≠ lDh := by decide
@[simp] theorem dh_lDh_ne_ukLp : lDh ≠ ukLp := by decide
@[simp] theorem dh_ukLp_ne_lDt : ukLp ≠ lDt := by decide
@[simp] theorem dh_lDt_ne_ukLp : lDt ≠ ukLp := by decide
@[simp] theorem dh_ukLp_ne_lDg : ukLp ≠ lDg := by decide
@[simp] theorem dh_lDg_ne_ukLp : lDg ≠ ukLp := by decide
@[simp] theorem dh_ukLp_ne_lDi : ukLp ≠ lDi := by decide
@[simp] theorem dh_lDi_ne_ukLp : lDi ≠ ukLp := by decide
@[simp] theorem dh_ukLp_ne_lRp : ukLp ≠ lRp := by decide
@[simp] theorem dh_lRp_ne_ukLp : lRp ≠ ukLp := by decide
@[simp] theorem dh_ukLp_ne_lRn : ukLp ≠ lRn := by decide
@[simp] theorem dh_lRn_ne_ukLp : lRn ≠ ukLp := by decide
@[simp] theorem dh_ukLp_ne_lFle : ukLp ≠ lFle := by decide
@[simp] theorem dh_lFle_ne_ukLp : lFle ≠ ukLp := by decide
@[simp] theorem dh_ukLp_ne_lKb : ukLp ≠ lKb := by decide
@[simp] theorem dh_lKb_ne_ukLp : lKb ≠ ukLp := by decide
@[simp] theorem dh_ukLp_ne_lDir : ukLp ≠ lDir := by decide
@[simp] theorem dh_lDir_ne_ukLp : lDir ≠ ukLp := by decide
@[simp] theorem dh_ukLp_ne_lFln : ukLp ≠ lFln := by decide
@[simp] theorem dh_lFln_ne_ukLp : lFln ≠ ukLp := by decide
@[simp] theorem dh_ukLp_ne_lFll : ukLp ≠ lFll := by decide
@[simp] theorem dh_lFll_ne_ukLp : lFll ≠ ukLp := by decide
@[simp] theorem dh_ukLp_ne_lFls : ukLp ≠ lFls := by decide
@[simp] theorem dh_lFls_ne_ukLp : lFls ≠ ukLp := by decide
@[simp] theorem dh_ukLl_ne_ukE : ukLl ≠ ukE := by decide
@[simp] theorem dh_ukLl_ne_ukH : ukLl ≠ ukH := by decide
@[simp] theorem dh_ukLl_ne_ukN : ukLl ≠ ukN := by decide
@[simp] theorem dh_ukLl_ne_ukU : ukLl ≠ ukU := by decide
@[simp] theorem dh_ukLl_ne_ukP : ukLl ≠ ukP := by decide
@[simp] theorem dh_ukLl_ne_ukQ : ukLl ≠ ukQ := by decide
@[simp] theorem dh_ukLl_ne_ukK : ukLl ≠ ukK := by decide
@[simp] theorem dh_ukLl_ne_ukLp : ukLl ≠ ukLp := by decide
@[simp] theorem dh_ukLl_ne_hnE : ukLl ≠ hnE := by decide
@[simp] theorem dh_ukLl_ne_hnH : ukLl ≠ hnH := by decide
@[simp] theorem dh_ukLl_ne_hnN : ukLl ≠ hnN := by decide
@[simp] theorem dh_ukLl_ne_hnP : ukLl ≠ hnP := by decide
@[simp] theorem dh_ukLl_ne_hnQ : ukLl ≠ hnQ := by decide
@[simp] theorem dh_ukLl_ne_hnK : ukLl ≠ hnK := by decide
@[simp] theorem dh_ukLl_ne_hnV : ukLl ≠ hnV := by decide
@[simp] theorem dh_ukLl_ne_sqA : ukLl ≠ sqA := by decide
@[simp] theorem dh_ukLl_ne_sqB : ukLl ≠ sqB := by decide
@[simp] theorem dh_ukLl_ne_sqF1 : ukLl ≠ sqF1 := by decide
@[simp] theorem dh_ukLl_ne_sqF2 : ukLl ≠ sqF2 := by decide
@[simp] theorem dh_ukLl_ne_sqH : ukLl ≠ sqH := by decide
@[simp] theorem dh_ukLl_ne_sqN1 : ukLl ≠ sqN1 := by decide
@[simp] theorem dh_ukLl_ne_sqH2 : ukLl ≠ sqH2 := by decide
@[simp] theorem dh_ukLl_ne_sqN2 : ukLl ≠ sqN2 := by decide
@[simp] theorem dh_ukLl_ne_lFl : ukLl ≠ lFl := by decide
@[simp] theorem dh_lFl_ne_ukLl : lFl ≠ ukLl := by decide
@[simp] theorem dh_ukLl_ne_lDh : ukLl ≠ lDh := by decide
@[simp] theorem dh_lDh_ne_ukLl : lDh ≠ ukLl := by decide
@[simp] theorem dh_ukLl_ne_lDt : ukLl ≠ lDt := by decide
@[simp] theorem dh_lDt_ne_ukLl : lDt ≠ ukLl := by decide
@[simp] theorem dh_ukLl_ne_lDg : ukLl ≠ lDg := by decide
@[simp] theorem dh_lDg_ne_ukLl : lDg ≠ ukLl := by decide
@[simp] theorem dh_ukLl_ne_lDi : ukLl ≠ lDi := by decide
@[simp] theorem dh_lDi_ne_ukLl : lDi ≠ ukLl := by decide
@[simp] theorem dh_ukLl_ne_lRp : ukLl ≠ lRp := by decide
@[simp] theorem dh_lRp_ne_ukLl : lRp ≠ ukLl := by decide
@[simp] theorem dh_ukLl_ne_lRn : ukLl ≠ lRn := by decide
@[simp] theorem dh_lRn_ne_ukLl : lRn ≠ ukLl := by decide
@[simp] theorem dh_ukLl_ne_lFle : ukLl ≠ lFle := by decide
@[simp] theorem dh_lFle_ne_ukLl : lFle ≠ ukLl := by decide
@[simp] theorem dh_ukLl_ne_lKb : ukLl ≠ lKb := by decide
@[simp] theorem dh_lKb_ne_ukLl : lKb ≠ ukLl := by decide
@[simp] theorem dh_ukLl_ne_lDir : ukLl ≠ lDir := by decide
@[simp] theorem dh_lDir_ne_ukLl : lDir ≠ ukLl := by decide
@[simp] theorem dh_ukLl_ne_lFln : ukLl ≠ lFln := by decide
@[simp] theorem dh_lFln_ne_ukLl : lFln ≠ ukLl := by decide
@[simp] theorem dh_ukLl_ne_lFll : ukLl ≠ lFll := by decide
@[simp] theorem dh_lFll_ne_ukLl : lFll ≠ ukLl := by decide
@[simp] theorem dh_ukLl_ne_lFls : ukLl ≠ lFls := by decide
@[simp] theorem dh_lFls_ne_ukLl : lFls ≠ ukLl := by decide
@[simp] theorem dh_hnE_ne_ukE : hnE ≠ ukE := by decide
@[simp] theorem dh_hnE_ne_ukH : hnE ≠ ukH := by decide
@[simp] theorem dh_hnE_ne_ukN : hnE ≠ ukN := by decide
@[simp] theorem dh_hnE_ne_ukU : hnE ≠ ukU := by decide
@[simp] theorem dh_hnE_ne_ukP : hnE ≠ ukP := by decide
@[simp] theorem dh_hnE_ne_ukQ : hnE ≠ ukQ := by decide
@[simp] theorem dh_hnE_ne_ukK : hnE ≠ ukK := by decide
@[simp] theorem dh_hnE_ne_ukLp : hnE ≠ ukLp := by decide
@[simp] theorem dh_hnE_ne_ukLl : hnE ≠ ukLl := by decide
@[simp] theorem dh_hnE_ne_hnH : hnE ≠ hnH := by decide
@[simp] theorem dh_hnE_ne_hnN : hnE ≠ hnN := by decide
@[simp] theorem dh_hnE_ne_hnP : hnE ≠ hnP := by decide
@[simp] theorem dh_hnE_ne_hnQ : hnE ≠ hnQ := by decide
@[simp] theorem dh_hnE_ne_hnK : hnE ≠ hnK := by decide
@[simp] theorem dh_hnE_ne_hnV : hnE ≠ hnV := by decide
@[simp] theorem dh_hnE_ne_sqA : hnE ≠ sqA := by decide
@[simp] theorem dh_hnE_ne_sqB : hnE ≠ sqB := by decide
@[simp] theorem dh_hnE_ne_sqF1 : hnE ≠ sqF1 := by decide
@[simp] theorem dh_hnE_ne_sqF2 : hnE ≠ sqF2 := by decide
@[simp] theorem dh_hnE_ne_sqH : hnE ≠ sqH := by decide
@[simp] theorem dh_hnE_ne_sqN1 : hnE ≠ sqN1 := by decide
@[simp] theorem dh_hnE_ne_sqH2 : hnE ≠ sqH2 := by decide
@[simp] theorem dh_hnE_ne_sqN2 : hnE ≠ sqN2 := by decide
@[simp] theorem dh_hnE_ne_lFl : hnE ≠ lFl := by decide
@[simp] theorem dh_lFl_ne_hnE : lFl ≠ hnE := by decide
@[simp] theorem dh_hnE_ne_lDh : hnE ≠ lDh := by decide
@[simp] theorem dh_lDh_ne_hnE : lDh ≠ hnE := by decide
@[simp] theorem dh_hnE_ne_lDt : hnE ≠ lDt := by decide
@[simp] theorem dh_lDt_ne_hnE : lDt ≠ hnE := by decide
@[simp] theorem dh_hnE_ne_lDg : hnE ≠ lDg := by decide
@[simp] theorem dh_lDg_ne_hnE : lDg ≠ hnE := by decide
@[simp] theorem dh_hnE_ne_lDi : hnE ≠ lDi := by decide
@[simp] theorem dh_lDi_ne_hnE : lDi ≠ hnE := by decide
@[simp] theorem dh_hnE_ne_lRp : hnE ≠ lRp := by decide
@[simp] theorem dh_lRp_ne_hnE : lRp ≠ hnE := by decide
@[simp] theorem dh_hnE_ne_lRn : hnE ≠ lRn := by decide
@[simp] theorem dh_lRn_ne_hnE : lRn ≠ hnE := by decide
@[simp] theorem dh_hnE_ne_lFle : hnE ≠ lFle := by decide
@[simp] theorem dh_lFle_ne_hnE : lFle ≠ hnE := by decide
@[simp] theorem dh_hnE_ne_lKb : hnE ≠ lKb := by decide
@[simp] theorem dh_lKb_ne_hnE : lKb ≠ hnE := by decide
@[simp] theorem dh_hnE_ne_lDir : hnE ≠ lDir := by decide
@[simp] theorem dh_lDir_ne_hnE : lDir ≠ hnE := by decide
@[simp] theorem dh_hnE_ne_lFln : hnE ≠ lFln := by decide
@[simp] theorem dh_lFln_ne_hnE : lFln ≠ hnE := by decide
@[simp] theorem dh_hnE_ne_lFll : hnE ≠ lFll := by decide
@[simp] theorem dh_lFll_ne_hnE : lFll ≠ hnE := by decide
@[simp] theorem dh_hnE_ne_lFls : hnE ≠ lFls := by decide
@[simp] theorem dh_lFls_ne_hnE : lFls ≠ hnE := by decide
@[simp] theorem dh_hnH_ne_ukE : hnH ≠ ukE := by decide
@[simp] theorem dh_hnH_ne_ukH : hnH ≠ ukH := by decide
@[simp] theorem dh_hnH_ne_ukN : hnH ≠ ukN := by decide
@[simp] theorem dh_hnH_ne_ukU : hnH ≠ ukU := by decide
@[simp] theorem dh_hnH_ne_ukP : hnH ≠ ukP := by decide
@[simp] theorem dh_hnH_ne_ukQ : hnH ≠ ukQ := by decide
@[simp] theorem dh_hnH_ne_ukK : hnH ≠ ukK := by decide
@[simp] theorem dh_hnH_ne_ukLp : hnH ≠ ukLp := by decide
@[simp] theorem dh_hnH_ne_ukLl : hnH ≠ ukLl := by decide
@[simp] theorem dh_hnH_ne_hnE : hnH ≠ hnE := by decide
@[simp] theorem dh_hnH_ne_hnN : hnH ≠ hnN := by decide
@[simp] theorem dh_hnH_ne_hnP : hnH ≠ hnP := by decide
@[simp] theorem dh_hnH_ne_hnQ : hnH ≠ hnQ := by decide
@[simp] theorem dh_hnH_ne_hnK : hnH ≠ hnK := by decide
@[simp] theorem dh_hnH_ne_hnV : hnH ≠ hnV := by decide
@[simp] theorem dh_hnH_ne_sqA : hnH ≠ sqA := by decide
@[simp] theorem dh_hnH_ne_sqB : hnH ≠ sqB := by decide
@[simp] theorem dh_hnH_ne_sqF1 : hnH ≠ sqF1 := by decide
@[simp] theorem dh_hnH_ne_sqF2 : hnH ≠ sqF2 := by decide
@[simp] theorem dh_hnH_ne_sqH : hnH ≠ sqH := by decide
@[simp] theorem dh_hnH_ne_sqN1 : hnH ≠ sqN1 := by decide
@[simp] theorem dh_hnH_ne_sqH2 : hnH ≠ sqH2 := by decide
@[simp] theorem dh_hnH_ne_sqN2 : hnH ≠ sqN2 := by decide
@[simp] theorem dh_hnH_ne_lFl : hnH ≠ lFl := by decide
@[simp] theorem dh_lFl_ne_hnH : lFl ≠ hnH := by decide
@[simp] theorem dh_hnH_ne_lDh : hnH ≠ lDh := by decide
@[simp] theorem dh_lDh_ne_hnH : lDh ≠ hnH := by decide
@[simp] theorem dh_hnH_ne_lDt : hnH ≠ lDt := by decide
@[simp] theorem dh_lDt_ne_hnH : lDt ≠ hnH := by decide
@[simp] theorem dh_hnH_ne_lDg : hnH ≠ lDg := by decide
@[simp] theorem dh_lDg_ne_hnH : lDg ≠ hnH := by decide
@[simp] theorem dh_hnH_ne_lDi : hnH ≠ lDi := by decide
@[simp] theorem dh_lDi_ne_hnH : lDi ≠ hnH := by decide
@[simp] theorem dh_hnH_ne_lRp : hnH ≠ lRp := by decide
@[simp] theorem dh_lRp_ne_hnH : lRp ≠ hnH := by decide
@[simp] theorem dh_hnH_ne_lRn : hnH ≠ lRn := by decide
@[simp] theorem dh_lRn_ne_hnH : lRn ≠ hnH := by decide
@[simp] theorem dh_hnH_ne_lFle : hnH ≠ lFle := by decide
@[simp] theorem dh_lFle_ne_hnH : lFle ≠ hnH := by decide
@[simp] theorem dh_hnH_ne_lKb : hnH ≠ lKb := by decide
@[simp] theorem dh_lKb_ne_hnH : lKb ≠ hnH := by decide
@[simp] theorem dh_hnH_ne_lDir : hnH ≠ lDir := by decide
@[simp] theorem dh_lDir_ne_hnH : lDir ≠ hnH := by decide
@[simp] theorem dh_hnH_ne_lFln : hnH ≠ lFln := by decide
@[simp] theorem dh_lFln_ne_hnH : lFln ≠ hnH := by decide
@[simp] theorem dh_hnH_ne_lFll : hnH ≠ lFll := by decide
@[simp] theorem dh_lFll_ne_hnH : lFll ≠ hnH := by decide
@[simp] theorem dh_hnH_ne_lFls : hnH ≠ lFls := by decide
@[simp] theorem dh_lFls_ne_hnH : lFls ≠ hnH := by decide
@[simp] theorem dh_hnN_ne_ukE : hnN ≠ ukE := by decide
@[simp] theorem dh_hnN_ne_ukH : hnN ≠ ukH := by decide
@[simp] theorem dh_hnN_ne_ukN : hnN ≠ ukN := by decide
@[simp] theorem dh_hnN_ne_ukU : hnN ≠ ukU := by decide
@[simp] theorem dh_hnN_ne_ukP : hnN ≠ ukP := by decide
@[simp] theorem dh_hnN_ne_ukQ : hnN ≠ ukQ := by decide
@[simp] theorem dh_hnN_ne_ukK : hnN ≠ ukK := by decide
@[simp] theorem dh_hnN_ne_ukLp : hnN ≠ ukLp := by decide
@[simp] theorem dh_hnN_ne_ukLl : hnN ≠ ukLl := by decide
@[simp] theorem dh_hnN_ne_hnE : hnN ≠ hnE := by decide
@[simp] theorem dh_hnN_ne_hnH : hnN ≠ hnH := by decide
@[simp] theorem dh_hnN_ne_hnP : hnN ≠ hnP := by decide
@[simp] theorem dh_hnN_ne_hnQ : hnN ≠ hnQ := by decide
@[simp] theorem dh_hnN_ne_hnK : hnN ≠ hnK := by decide
@[simp] theorem dh_hnN_ne_hnV : hnN ≠ hnV := by decide
@[simp] theorem dh_hnN_ne_sqA : hnN ≠ sqA := by decide
@[simp] theorem dh_hnN_ne_sqB : hnN ≠ sqB := by decide
@[simp] theorem dh_hnN_ne_sqF1 : hnN ≠ sqF1 := by decide
@[simp] theorem dh_hnN_ne_sqF2 : hnN ≠ sqF2 := by decide
@[simp] theorem dh_hnN_ne_sqH : hnN ≠ sqH := by decide
@[simp] theorem dh_hnN_ne_sqN1 : hnN ≠ sqN1 := by decide
@[simp] theorem dh_hnN_ne_sqH2 : hnN ≠ sqH2 := by decide
@[simp] theorem dh_hnN_ne_sqN2 : hnN ≠ sqN2 := by decide
@[simp] theorem dh_hnN_ne_lFl : hnN ≠ lFl := by decide
@[simp] theorem dh_lFl_ne_hnN : lFl ≠ hnN := by decide
@[simp] theorem dh_hnN_ne_lDh : hnN ≠ lDh := by decide
@[simp] theorem dh_lDh_ne_hnN : lDh ≠ hnN := by decide
@[simp] theorem dh_hnN_ne_lDt : hnN ≠ lDt := by decide
@[simp] theorem dh_lDt_ne_hnN : lDt ≠ hnN := by decide
@[simp] theorem dh_hnN_ne_lDg : hnN ≠ lDg := by decide
@[simp] theorem dh_lDg_ne_hnN : lDg ≠ hnN := by decide
@[simp] theorem dh_hnN_ne_lDi : hnN ≠ lDi := by decide
@[simp] theorem dh_lDi_ne_hnN : lDi ≠ hnN := by decide
@[simp] theorem dh_hnN_ne_lRp : hnN ≠ lRp := by decide
@[simp] theorem dh_lRp_ne_hnN : lRp ≠ hnN := by decide
@[simp] theorem dh_hnN_ne_lRn : hnN ≠ lRn := by decide
@[simp] theorem dh_lRn_ne_hnN : lRn ≠ hnN := by decide
@[simp] theorem dh_hnN_ne_lFle : hnN ≠ lFle := by decide
@[simp] theorem dh_lFle_ne_hnN : lFle ≠ hnN := by decide
@[simp] theorem dh_hnN_ne_lKb : hnN ≠ lKb := by decide
@[simp] theorem dh_lKb_ne_hnN : lKb ≠ hnN := by decide
@[simp] theorem dh_hnN_ne_lDir : hnN ≠ lDir := by decide
@[simp] theorem dh_lDir_ne_hnN : lDir ≠ hnN := by decide
@[simp] theorem dh_hnN_ne_lFln : hnN ≠ lFln := by decide
@[simp] theorem dh_lFln_ne_hnN : lFln ≠ hnN := by decide
@[simp] theorem dh_hnN_ne_lFll : hnN ≠ lFll := by decide
@[simp] theorem dh_lFll_ne_hnN : lFll ≠ hnN := by decide
@[simp] theorem dh_hnN_ne_lFls : hnN ≠ lFls := by decide
@[simp] theorem dh_lFls_ne_hnN : lFls ≠ hnN := by decide
@[simp] theorem dh_hnP_ne_ukE : hnP ≠ ukE := by decide
@[simp] theorem dh_hnP_ne_ukH : hnP ≠ ukH := by decide
@[simp] theorem dh_hnP_ne_ukN : hnP ≠ ukN := by decide
@[simp] theorem dh_hnP_ne_ukU : hnP ≠ ukU := by decide
@[simp] theorem dh_hnP_ne_ukP : hnP ≠ ukP := by decide
@[simp] theorem dh_hnP_ne_ukQ : hnP ≠ ukQ := by decide
@[simp] theorem dh_hnP_ne_ukK : hnP ≠ ukK := by decide
@[simp] theorem dh_hnP_ne_ukLp : hnP ≠ ukLp := by decide
@[simp] theorem dh_hnP_ne_ukLl : hnP ≠ ukLl := by decide
@[simp] theorem dh_hnP_ne_hnE : hnP ≠ hnE := by decide
@[simp] theorem dh_hnP_ne_hnH : hnP ≠ hnH := by decide
@[simp] theorem dh_hnP_ne_hnN : hnP ≠ hnN := by decide
@[simp] theorem dh_hnP_ne_hnQ : hnP ≠ hnQ := by decide
@[simp] theorem dh_hnP_ne_hnK : hnP ≠ hnK := by decide
@[simp] theorem dh_hnP_ne_hnV : hnP ≠ hnV := by decide
@[simp] theorem dh_hnP_ne_sqA : hnP ≠ sqA := by decide
@[simp] theorem dh_hnP_ne_sqB : hnP ≠ sqB := by decide
@[simp] theorem dh_hnP_ne_sqF1 : hnP ≠ sqF1 := by decide
@[simp] theorem dh_hnP_ne_sqF2 : hnP ≠ sqF2 := by decide
@[simp] theorem dh_hnP_ne_sqH : hnP ≠ sqH := by decide
@[simp] theorem dh_hnP_ne_sqN1 : hnP ≠ sqN1 := by decide
@[simp] theorem dh_hnP_ne_sqH2 : hnP ≠ sqH2 := by decide
@[simp] theorem dh_hnP_ne_sqN2 : hnP ≠ sqN2 := by decide
@[simp] theorem dh_hnP_ne_lFl : hnP ≠ lFl := by decide
@[simp] theorem dh_lFl_ne_hnP : lFl ≠ hnP := by decide
@[simp] theorem dh_hnP_ne_lDh : hnP ≠ lDh := by decide
@[simp] theorem dh_lDh_ne_hnP : lDh ≠ hnP := by decide
@[simp] theorem dh_hnP_ne_lDt : hnP ≠ lDt := by decide
@[simp] theorem dh_lDt_ne_hnP : lDt ≠ hnP := by decide
@[simp] theorem dh_hnP_ne_lDg : hnP ≠ lDg := by decide
@[simp] theorem dh_lDg_ne_hnP : lDg ≠ hnP := by decide
@[simp] theorem dh_hnP_ne_lDi : hnP ≠ lDi := by decide
@[simp] theorem dh_lDi_ne_hnP : lDi ≠ hnP := by decide
@[simp] theorem dh_hnP_ne_lRp : hnP ≠ lRp := by decide
@[simp] theorem dh_lRp_ne_hnP : lRp ≠ hnP := by decide
@[simp] theorem dh_hnP_ne_lRn : hnP ≠ lRn := by decide
@[simp] theorem dh_lRn_ne_hnP : lRn ≠ hnP := by decide
@[simp] theorem dh_hnP_ne_lFle : hnP ≠ lFle := by decide
@[simp] theorem dh_lFle_ne_hnP : lFle ≠ hnP := by decide
@[simp] theorem dh_hnP_ne_lKb : hnP ≠ lKb := by decide
@[simp] theorem dh_lKb_ne_hnP : lKb ≠ hnP := by decide
@[simp] theorem dh_hnP_ne_lDir : hnP ≠ lDir := by decide
@[simp] theorem dh_lDir_ne_hnP : lDir ≠ hnP := by decide
@[simp] theorem dh_hnP_ne_lFln : hnP ≠ lFln := by decide
@[simp] theorem dh_lFln_ne_hnP : lFln ≠ hnP := by decide
@[simp] theorem dh_hnP_ne_lFll : hnP ≠ lFll := by decide
@[simp] theorem dh_lFll_ne_hnP : lFll ≠ hnP := by decide
@[simp] theorem dh_hnP_ne_lFls : hnP ≠ lFls := by decide
@[simp] theorem dh_lFls_ne_hnP : lFls ≠ hnP := by decide
@[simp] theorem dh_hnQ_ne_ukE : hnQ ≠ ukE := by decide
@[simp] theorem dh_hnQ_ne_ukH : hnQ ≠ ukH := by decide
@[simp] theorem dh_hnQ_ne_ukN : hnQ ≠ ukN := by decide
@[simp] theorem dh_hnQ_ne_ukU : hnQ ≠ ukU := by decide
@[simp] theorem dh_hnQ_ne_ukP : hnQ ≠ ukP := by decide
@[simp] theorem dh_hnQ_ne_ukQ : hnQ ≠ ukQ := by decide
@[simp] theorem dh_hnQ_ne_ukK : hnQ ≠ ukK := by decide
@[simp] theorem dh_hnQ_ne_ukLp : hnQ ≠ ukLp := by decide
@[simp] theorem dh_hnQ_ne_ukLl : hnQ ≠ ukLl := by decide
@[simp] theorem dh_hnQ_ne_hnE : hnQ ≠ hnE := by decide
@[simp] theorem dh_hnQ_ne_hnH : hnQ ≠ hnH := by decide
@[simp] theorem dh_hnQ_ne_hnN : hnQ ≠ hnN := by decide
@[simp] theorem dh_hnQ_ne_hnP : hnQ ≠ hnP := by decide
@[simp] theorem dh_hnQ_ne_hnK : hnQ ≠ hnK := by decide
@[simp] theorem dh_hnQ_ne_hnV : hnQ ≠ hnV := by decide
@[simp] theorem dh_hnQ_ne_sqA : hnQ ≠ sqA := by decide
@[simp] theorem dh_hnQ_ne_sqB : hnQ ≠ sqB := by decide
@[simp] theorem dh_hnQ_ne_sqF1 : hnQ ≠ sqF1 := by decide
@[simp] theorem dh_hnQ_ne_sqF2 : hnQ ≠ sqF2 := by decide
@[simp] theorem dh_hnQ_ne_sqH : hnQ ≠ sqH := by decide
@[simp] theorem dh_hnQ_ne_sqN1 : hnQ ≠ sqN1 := by decide
@[simp] theorem dh_hnQ_ne_sqH2 : hnQ ≠ sqH2 := by decide
@[simp] theorem dh_hnQ_ne_sqN2 : hnQ ≠ sqN2 := by decide
@[simp] theorem dh_hnQ_ne_lFl : hnQ ≠ lFl := by decide
@[simp] theorem dh_lFl_ne_hnQ : lFl ≠ hnQ := by decide
@[simp] theorem dh_hnQ_ne_lDh : hnQ ≠ lDh := by decide
@[simp] theorem dh_lDh_ne_hnQ : lDh ≠ hnQ := by decide
@[simp] theorem dh_hnQ_ne_lDt : hnQ ≠ lDt := by decide
@[simp] theorem dh_lDt_ne_hnQ : lDt ≠ hnQ := by decide
@[simp] theorem dh_hnQ_ne_lDg : hnQ ≠ lDg := by decide
@[simp] theorem dh_lDg_ne_hnQ : lDg ≠ hnQ := by decide
@[simp] theorem dh_hnQ_ne_lDi : hnQ ≠ lDi := by decide
@[simp] theorem dh_lDi_ne_hnQ : lDi ≠ hnQ := by decide
@[simp] theorem dh_hnQ_ne_lRp : hnQ ≠ lRp := by decide
@[simp] theorem dh_lRp_ne_hnQ : lRp ≠ hnQ := by decide
@[simp] theorem dh_hnQ_ne_lRn : hnQ ≠ lRn := by decide
@[simp] theorem dh_lRn_ne_hnQ : lRn ≠ hnQ := by decide
@[simp] theorem dh_hnQ_ne_lFle : hnQ ≠ lFle := by decide
@[simp] theorem dh_lFle_ne_hnQ : lFle ≠ hnQ := by decide
@[simp] theorem dh_hnQ_ne_lKb : hnQ ≠ lKb := by decide
@[simp] theorem dh_lKb_ne_hnQ : lKb ≠ hnQ := by decide
@[simp] theorem dh_hnQ_ne_lDir : hnQ ≠ lDir := by decide
@[simp] theorem dh_lDir_ne_hnQ : lDir ≠ hnQ := by decide
@[simp] theorem dh_hnQ_ne_lFln : hnQ ≠ lFln := by decide
@[simp] theorem dh_lFln_ne_hnQ : lFln ≠ hnQ := by decide
@[simp] theorem dh_hnQ_ne_lFll : hnQ ≠ lFll := by decide
@[simp] theorem dh_lFll_ne_hnQ : lFll ≠ hnQ := by decide
@[simp] theorem dh_hnQ_ne_lFls : hnQ ≠ lFls := by decide
@[simp] theorem dh_lFls_ne_hnQ : lFls ≠ hnQ := by decide
@[simp] theorem dh_hnK_ne_ukE : hnK ≠ ukE := by decide
@[simp] theorem dh_hnK_ne_ukH : hnK ≠ ukH := by decide
@[simp] theorem dh_hnK_ne_ukN : hnK ≠ ukN := by decide
@[simp] theorem dh_hnK_ne_ukU : hnK ≠ ukU := by decide
@[simp] theorem dh_hnK_ne_ukP : hnK ≠ ukP := by decide
@[simp] theorem dh_hnK_ne_ukQ : hnK ≠ ukQ := by decide
@[simp] theorem dh_hnK_ne_ukK : hnK ≠ ukK := by decide
@[simp] theorem dh_hnK_ne_ukLp : hnK ≠ ukLp := by decide
@[simp] theorem dh_hnK_ne_ukLl : hnK ≠ ukLl := by decide
@[simp] theorem dh_hnK_ne_hnE : hnK ≠ hnE := by decide
@[simp] theorem dh_hnK_ne_hnH : hnK ≠ hnH := by decide
@[simp] theorem dh_hnK_ne_hnN : hnK ≠ hnN := by decide
@[simp] theorem dh_hnK_ne_hnP : hnK ≠ hnP := by decide
@[simp] theorem dh_hnK_ne_hnQ : hnK ≠ hnQ := by decide
@[simp] theorem dh_hnK_ne_hnV : hnK ≠ hnV := by decide
@[simp] theorem dh_hnK_ne_sqA : hnK ≠ sqA := by decide
@[simp] theorem dh_hnK_ne_sqB : hnK ≠ sqB := by decide
@[simp] theorem dh_hnK_ne_sqF1 : hnK ≠ sqF1 := by decide
@[simp] theorem dh_hnK_ne_sqF2 : hnK ≠ sqF2 := by decide
@[simp] theorem dh_hnK_ne_sqH : hnK ≠ sqH := by decide
@[simp] theorem dh_hnK_ne_sqN1 : hnK ≠ sqN1 := by decide
@[simp] theorem dh_hnK_ne_sqH2 : hnK ≠ sqH2 := by decide
@[simp] theorem dh_hnK_ne_sqN2 : hnK ≠ sqN2 := by decide
@[simp] theorem dh_hnK_ne_lFl : hnK ≠ lFl := by decide
@[simp] theorem dh_lFl_ne_hnK : lFl ≠ hnK := by decide
@[simp] theorem dh_hnK_ne_lDh : hnK ≠ lDh := by decide
@[simp] theorem dh_lDh_ne_hnK : lDh ≠ hnK := by decide
@[simp] theorem dh_hnK_ne_lDt : hnK ≠ lDt := by decide
@[simp] theorem dh_lDt_ne_hnK : lDt ≠ hnK := by decide
@[simp] theorem dh_hnK_ne_lDg : hnK ≠ lDg := by decide
@[simp] theorem dh_lDg_ne_hnK : lDg ≠ hnK := by decide
@[simp] theorem dh_hnK_ne_lDi : hnK ≠ lDi := by decide
@[simp] theorem dh_lDi_ne_hnK : lDi ≠ hnK := by decide
@[simp] theorem dh_hnK_ne_lRp : hnK ≠ lRp := by decide
@[simp] theorem dh_lRp_ne_hnK : lRp ≠ hnK := by decide
@[simp] theorem dh_hnK_ne_lRn : hnK ≠ lRn := by decide
@[simp] theorem dh_lRn_ne_hnK : lRn ≠ hnK := by decide
@[simp] theorem dh_hnK_ne_lFle : hnK ≠ lFle := by decide
@[simp] theorem dh_lFle_ne_hnK : lFle ≠ hnK := by decide
@[simp] theorem dh_hnK_ne_lKb : hnK ≠ lKb := by decide
@[simp] theorem dh_lKb_ne_hnK : lKb ≠ hnK := by decide
@[simp] theorem dh_hnK_ne_lDir : hnK ≠ lDir := by decide
@[simp] theorem dh_lDir_ne_hnK : lDir ≠ hnK := by decide
@[simp] theorem dh_hnK_ne_lFln : hnK ≠ lFln := by decide
@[simp] theorem dh_lFln_ne_hnK : lFln ≠ hnK := by decide
@[simp] theorem dh_hnK_ne_lFll : hnK ≠ lFll := by decide
@[simp] theorem dh_lFll_ne_hnK : lFll ≠ hnK := by decide
@[simp] theorem dh_hnK_ne_lFls : hnK ≠ lFls := by decide
@[simp] theorem dh_lFls_ne_hnK : lFls ≠ hnK := by decide
@[simp] theorem dh_hnV_ne_ukE : hnV ≠ ukE := by decide
@[simp] theorem dh_hnV_ne_ukH : hnV ≠ ukH := by decide
@[simp] theorem dh_hnV_ne_ukN : hnV ≠ ukN := by decide
@[simp] theorem dh_hnV_ne_ukU : hnV ≠ ukU := by decide
@[simp] theorem dh_hnV_ne_ukP : hnV ≠ ukP := by decide
@[simp] theorem dh_hnV_ne_ukQ : hnV ≠ ukQ := by decide
@[simp] theorem dh_hnV_ne_ukK : hnV ≠ ukK := by decide
@[simp] theorem dh_hnV_ne_ukLp : hnV ≠ ukLp := by decide
@[simp] theorem dh_hnV_ne_ukLl : hnV ≠ ukLl := by decide
@[simp] theorem dh_hnV_ne_hnE : hnV ≠ hnE := by decide
@[simp] theorem dh_hnV_ne_hnH : hnV ≠ hnH := by decide
@[simp] theorem dh_hnV_ne_hnN : hnV ≠ hnN := by decide
@[simp] theorem dh_hnV_ne_hnP : hnV ≠ hnP := by decide
@[simp] theorem dh_hnV_ne_hnQ : hnV ≠ hnQ := by decide
@[simp] theorem dh_hnV_ne_hnK : hnV ≠ hnK := by decide
@[simp] theorem dh_hnV_ne_sqA : hnV ≠ sqA := by decide
@[simp] theorem dh_hnV_ne_sqB : hnV ≠ sqB := by decide
@[simp] theorem dh_hnV_ne_sqF1 : hnV ≠ sqF1 := by decide
@[simp] theorem dh_hnV_ne_sqF2 : hnV ≠ sqF2 := by decide
@[simp] theorem dh_hnV_ne_sqH : hnV ≠ sqH := by decide
@[simp] theorem dh_hnV_ne_sqN1 : hnV ≠ sqN1 := by decide
@[simp] theorem dh_hnV_ne_sqH2 : hnV ≠ sqH2 := by decide
@[simp] theorem dh_hnV_ne_sqN2 : hnV ≠ sqN2 := by decide
@[simp] theorem dh_hnV_ne_lFl : hnV ≠ lFl := by decide
@[simp] theorem dh_lFl_ne_hnV : lFl ≠ hnV := by decide
@[simp] theorem dh_hnV_ne_lDh : hnV ≠ lDh := by decide
@[simp] theorem dh_lDh_ne_hnV : lDh ≠ hnV := by decide
@[simp] theorem dh_hnV_ne_lDt : hnV ≠ lDt := by decide
@[simp] theorem dh_lDt_ne_hnV : lDt ≠ hnV := by decide
@[simp] theorem dh_hnV_ne_lDg : hnV ≠ lDg := by decide
@[simp] theorem dh_lDg_ne_hnV : lDg ≠ hnV := by decide
@[simp] theorem dh_hnV_ne_lDi : hnV ≠ lDi := by decide
@[simp] theorem dh_lDi_ne_hnV : lDi ≠ hnV := by decide
@[simp] theorem dh_hnV_ne_lRp : hnV ≠ lRp := by decide
@[simp] theorem dh_lRp_ne_hnV : lRp ≠ hnV := by decide
@[simp] theorem dh_hnV_ne_lRn : hnV ≠ lRn := by decide
@[simp] theorem dh_lRn_ne_hnV : lRn ≠ hnV := by decide
@[simp] theorem dh_hnV_ne_lFle : hnV ≠ lFle := by decide
@[simp] theorem dh_lFle_ne_hnV : lFle ≠ hnV := by decide
@[simp] theorem dh_hnV_ne_lKb : hnV ≠ lKb := by decide
@[simp] theorem dh_lKb_ne_hnV : lKb ≠ hnV := by decide
@[simp] theorem dh_hnV_ne_lDir : hnV ≠ lDir := by decide
@[simp] theorem dh_lDir_ne_hnV : lDir ≠ hnV := by decide
@[simp] theorem dh_hnV_ne_lFln : hnV ≠ lFln := by decide
@[simp] theorem dh_lFln_ne_hnV : lFln ≠ hnV := by decide
@[simp] theorem dh_hnV_ne_lFll : hnV ≠ lFll := by decide
@[simp] theorem dh_lFll_ne_hnV : lFll ≠ hnV := by decide
@[simp] theorem dh_hnV_ne_lFls : hnV ≠ lFls := by decide
@[simp] theorem dh_lFls_ne_hnV : lFls ≠ hnV := by decide
@[simp] theorem dh_sqA_ne_ukE : sqA ≠ ukE := by decide
@[simp] theorem dh_sqA_ne_ukH : sqA ≠ ukH := by decide
@[simp] theorem dh_sqA_ne_ukN : sqA ≠ ukN := by decide
@[simp] theorem dh_sqA_ne_ukU : sqA ≠ ukU := by decide
@[simp] theorem dh_sqA_ne_ukP : sqA ≠ ukP := by decide
@[simp] theorem dh_sqA_ne_ukQ : sqA ≠ ukQ := by decide
@[simp] theorem dh_sqA_ne_ukK : sqA ≠ ukK := by decide
@[simp] theorem dh_sqA_ne_ukLp : sqA ≠ ukLp := by decide
@[simp] theorem dh_sqA_ne_ukLl : sqA ≠ ukLl := by decide
@[simp] theorem dh_sqA_ne_hnE : sqA ≠ hnE := by decide
@[simp] theorem dh_sqA_ne_hnH : sqA ≠ hnH := by decide
@[simp] theorem dh_sqA_ne_hnN : sqA ≠ hnN := by decide
@[simp] theorem dh_sqA_ne_hnP : sqA ≠ hnP := by decide
@[simp] theorem dh_sqA_ne_hnQ : sqA ≠ hnQ := by decide
@[simp] theorem dh_sqA_ne_hnK : sqA ≠ hnK := by decide
@[simp] theorem dh_sqA_ne_hnV : sqA ≠ hnV := by decide
@[simp] theorem dh_sqA_ne_sqB : sqA ≠ sqB := by decide
@[simp] theorem dh_sqA_ne_sqF1 : sqA ≠ sqF1 := by decide
@[simp] theorem dh_sqA_ne_sqF2 : sqA ≠ sqF2 := by decide
@[simp] theorem dh_sqA_ne_sqH : sqA ≠ sqH := by decide
@[simp] theorem dh_sqA_ne_sqN1 : sqA ≠ sqN1 := by decide
@[simp] theorem dh_sqA_ne_sqH2 : sqA ≠ sqH2 := by decide
@[simp] theorem dh_sqA_ne_sqN2 : sqA ≠ sqN2 := by decide
@[simp] theorem dh_sqA_ne_lFl : sqA ≠ lFl := by decide
@[simp] theorem dh_lFl_ne_sqA : lFl ≠ sqA := by decide
@[simp] theorem dh_sqA_ne_lDh : sqA ≠ lDh := by decide
@[simp] theorem dh_lDh_ne_sqA : lDh ≠ sqA := by decide
@[simp] theorem dh_sqA_ne_lDt : sqA ≠ lDt := by decide
@[simp] theorem dh_lDt_ne_sqA : lDt ≠ sqA := by decide
@[simp] theorem dh_sqA_ne_lDg : sqA ≠ lDg := by decide
@[simp] theorem dh_lDg_ne_sqA : lDg ≠ sqA := by decide
@[simp] theorem dh_sqA_ne_lDi : sqA ≠ lDi := by decide
@[simp] theorem dh_lDi_ne_sqA : lDi ≠ sqA := by decide
@[simp] theorem dh_sqA_ne_lRp : sqA ≠ lRp := by decide
@[simp] theorem dh_lRp_ne_sqA : lRp ≠ sqA := by decide
@[simp] theorem dh_sqA_ne_lRn : sqA ≠ lRn := by decide
@[simp] theorem dh_lRn_ne_sqA : lRn ≠ sqA := by decide
@[simp] theorem dh_sqA_ne_lFle : sqA ≠ lFle := by decide
@[simp] theorem dh_lFle_ne_sqA : lFle ≠ sqA := by decide
@[simp] theorem dh_sqA_ne_lKb : sqA ≠ lKb := by decide
@[simp] theorem dh_lKb_ne_sqA : lKb ≠ sqA := by decide
@[simp] theorem dh_sqA_ne_lDir : sqA ≠ lDir := by decide
@[simp] theorem dh_lDir_ne_sqA : lDir ≠ sqA := by decide
@[simp] theorem dh_sqA_ne_lFln : sqA ≠ lFln := by decide
@[simp] theorem dh_lFln_ne_sqA : lFln ≠ sqA := by decide
@[simp] theorem dh_sqA_ne_lFll : sqA ≠ lFll := by decide
@[simp] theorem dh_lFll_ne_sqA : lFll ≠ sqA := by decide
@[simp] theorem dh_sqA_ne_lFls : sqA ≠ lFls := by decide
@[simp] theorem dh_lFls_ne_sqA : lFls ≠ sqA := by decide
@[simp] theorem dh_sqB_ne_ukE : sqB ≠ ukE := by decide
@[simp] theorem dh_sqB_ne_ukH : sqB ≠ ukH := by decide
@[simp] theorem dh_sqB_ne_ukN : sqB ≠ ukN := by decide
@[simp] theorem dh_sqB_ne_ukU : sqB ≠ ukU := by decide
@[simp] theorem dh_sqB_ne_ukP : sqB ≠ ukP := by decide
@[simp] theorem dh_sqB_ne_ukQ : sqB ≠ ukQ := by decide
@[simp] theorem dh_sqB_ne_ukK : sqB ≠ ukK := by decide
@[simp] theorem dh_sqB_ne_ukLp : sqB ≠ ukLp := by decide
@[simp] theorem dh_sqB_ne_ukLl : sqB ≠ ukLl := by decide
@[simp] theorem dh_sqB_ne_hnE : sqB ≠ hnE := by decide
@[simp] theorem dh_sqB_ne_hnH : sqB ≠ hnH := by decide
@[simp] theorem dh_sqB_ne_hnN : sqB ≠ hnN := by decide
@[simp] theorem dh_sqB_ne_hnP : sqB ≠ hnP := by decide
@[simp] theorem dh_sqB_ne_hnQ : sqB ≠ hnQ := by decide
@[simp] theorem dh_sqB_ne_hnK : sqB ≠ hnK := by decide
@[simp] theorem dh_sqB_ne_hnV : sqB ≠ hnV := by decide
@[simp] theorem dh_sqB_ne_sqA : sqB ≠ sqA := by decide
@[simp] theorem dh_sqB_ne_sqF1 : sqB ≠ sqF1 := by decide
@[simp] theorem dh_sqB_ne_sqF2 : sqB ≠ sqF2 := by decide
@[simp] theorem dh_sqB_ne_sqH : sqB ≠ sqH := by decide
@[simp] theorem dh_sqB_ne_sqN1 : sqB ≠ sqN1 := by decide
@[simp] theorem dh_sqB_ne_sqH2 : sqB ≠ sqH2 := by decide
@[simp] theorem dh_sqB_ne_sqN2 : sqB ≠ sqN2 := by decide
@[simp] theorem dh_sqB_ne_lFl : sqB ≠ lFl := by decide
@[simp] theorem dh_lFl_ne_sqB : lFl ≠ sqB := by decide
@[simp] theorem dh_sqB_ne_lDh : sqB ≠ lDh := by decide
@[simp] theorem dh_lDh_ne_sqB : lDh ≠ sqB := by decide
@[simp] theorem dh_sqB_ne_lDt : sqB ≠ lDt := by decide
@[simp] theorem dh_lDt_ne_sqB : lDt ≠ sqB := by decide
@[simp] theorem dh_sqB_ne_lDg : sqB ≠ lDg := by decide
@[simp] theorem dh_lDg_ne_sqB : lDg ≠ sqB := by decide
@[simp] theorem dh_sqB_ne_lDi : sqB ≠ lDi := by decide
@[simp] theorem dh_lDi_ne_sqB : lDi ≠ sqB := by decide
@[simp] theorem dh_sqB_ne_lRp : sqB ≠ lRp := by decide
@[simp] theorem dh_lRp_ne_sqB : lRp ≠ sqB := by decide
@[simp] theorem dh_sqB_ne_lRn : sqB ≠ lRn := by decide
@[simp] theorem dh_lRn_ne_sqB : lRn ≠ sqB := by decide
@[simp] theorem dh_sqB_ne_lFle : sqB ≠ lFle := by decide
@[simp] theorem dh_lFle_ne_sqB : lFle ≠ sqB := by decide
@[simp] theorem dh_sqB_ne_lKb : sqB ≠ lKb := by decide
@[simp] theorem dh_lKb_ne_sqB : lKb ≠ sqB := by decide
@[simp] theorem dh_sqB_ne_lDir : sqB ≠ lDir := by decide
@[simp] theorem dh_lDir_ne_sqB : lDir ≠ sqB := by decide
@[simp] theorem dh_sqB_ne_lFln : sqB ≠ lFln := by decide
@[simp] theorem dh_lFln_ne_sqB : lFln ≠ sqB := by decide
@[simp] theorem dh_sqB_ne_lFll : sqB ≠ lFll := by decide
@[simp] theorem dh_lFll_ne_sqB : lFll ≠ sqB := by decide
@[simp] theorem dh_sqB_ne_lFls : sqB ≠ lFls := by decide
@[simp] theorem dh_lFls_ne_sqB : lFls ≠ sqB := by decide
@[simp] theorem dh_sqF1_ne_ukE : sqF1 ≠ ukE := by decide
@[simp] theorem dh_sqF1_ne_ukH : sqF1 ≠ ukH := by decide
@[simp] theorem dh_sqF1_ne_ukN : sqF1 ≠ ukN := by decide
@[simp] theorem dh_sqF1_ne_ukU : sqF1 ≠ ukU := by decide
@[simp] theorem dh_sqF1_ne_ukP : sqF1 ≠ ukP := by decide
@[simp] theorem dh_sqF1_ne_ukQ : sqF1 ≠ ukQ := by decide
@[simp] theorem dh_sqF1_ne_ukK : sqF1 ≠ ukK := by decide
@[simp] theorem dh_sqF1_ne_ukLp : sqF1 ≠ ukLp := by decide
@[simp] theorem dh_sqF1_ne_ukLl : sqF1 ≠ ukLl := by decide
@[simp] theorem dh_sqF1_ne_hnE : sqF1 ≠ hnE := by decide
@[simp] theorem dh_sqF1_ne_hnH : sqF1 ≠ hnH := by decide
@[simp] theorem dh_sqF1_ne_hnN : sqF1 ≠ hnN := by decide
@[simp] theorem dh_sqF1_ne_hnP : sqF1 ≠ hnP := by decide
@[simp] theorem dh_sqF1_ne_hnQ : sqF1 ≠ hnQ := by decide
@[simp] theorem dh_sqF1_ne_hnK : sqF1 ≠ hnK := by decide
@[simp] theorem dh_sqF1_ne_hnV : sqF1 ≠ hnV := by decide
@[simp] theorem dh_sqF1_ne_sqA : sqF1 ≠ sqA := by decide
@[simp] theorem dh_sqF1_ne_sqB : sqF1 ≠ sqB := by decide
@[simp] theorem dh_sqF1_ne_sqF2 : sqF1 ≠ sqF2 := by decide
@[simp] theorem dh_sqF1_ne_sqH : sqF1 ≠ sqH := by decide
@[simp] theorem dh_sqF1_ne_sqN1 : sqF1 ≠ sqN1 := by decide
@[simp] theorem dh_sqF1_ne_sqH2 : sqF1 ≠ sqH2 := by decide
@[simp] theorem dh_sqF1_ne_sqN2 : sqF1 ≠ sqN2 := by decide
@[simp] theorem dh_sqF1_ne_lFl : sqF1 ≠ lFl := by decide
@[simp] theorem dh_lFl_ne_sqF1 : lFl ≠ sqF1 := by decide
@[simp] theorem dh_sqF1_ne_lDh : sqF1 ≠ lDh := by decide
@[simp] theorem dh_lDh_ne_sqF1 : lDh ≠ sqF1 := by decide
@[simp] theorem dh_sqF1_ne_lDt : sqF1 ≠ lDt := by decide
@[simp] theorem dh_lDt_ne_sqF1 : lDt ≠ sqF1 := by decide
@[simp] theorem dh_sqF1_ne_lDg : sqF1 ≠ lDg := by decide
@[simp] theorem dh_lDg_ne_sqF1 : lDg ≠ sqF1 := by decide
@[simp] theorem dh_sqF1_ne_lDi : sqF1 ≠ lDi := by decide
@[simp] theorem dh_lDi_ne_sqF1 : lDi ≠ sqF1 := by decide
@[simp] theorem dh_sqF1_ne_lRp : sqF1 ≠ lRp := by decide
@[simp] theorem dh_lRp_ne_sqF1 : lRp ≠ sqF1 := by decide
@[simp] theorem dh_sqF1_ne_lRn : sqF1 ≠ lRn := by decide
@[simp] theorem dh_lRn_ne_sqF1 : lRn ≠ sqF1 := by decide
@[simp] theorem dh_sqF1_ne_lFle : sqF1 ≠ lFle := by decide
@[simp] theorem dh_lFle_ne_sqF1 : lFle ≠ sqF1 := by decide
@[simp] theorem dh_sqF1_ne_lKb : sqF1 ≠ lKb := by decide
@[simp] theorem dh_lKb_ne_sqF1 : lKb ≠ sqF1 := by decide
@[simp] theorem dh_sqF1_ne_lDir : sqF1 ≠ lDir := by decide
@[simp] theorem dh_lDir_ne_sqF1 : lDir ≠ sqF1 := by decide
@[simp] theorem dh_sqF1_ne_lFln : sqF1 ≠ lFln := by decide
@[simp] theorem dh_lFln_ne_sqF1 : lFln ≠ sqF1 := by decide
@[simp] theorem dh_sqF1_ne_lFll : sqF1 ≠ lFll := by decide
@[simp] theorem dh_lFll_ne_sqF1 : lFll ≠ sqF1 := by decide
@[simp] theorem dh_sqF1_ne_lFls : sqF1 ≠ lFls := by decide
@[simp] theorem dh_lFls_ne_sqF1 : lFls ≠ sqF1 := by decide
@[simp] theorem dh_sqF2_ne_ukE : sqF2 ≠ ukE := by decide
@[simp] theorem dh_sqF2_ne_ukH : sqF2 ≠ ukH := by decide
@[simp] theorem dh_sqF2_ne_ukN : sqF2 ≠ ukN := by decide
@[simp] theorem dh_sqF2_ne_ukU : sqF2 ≠ ukU := by decide
@[simp] theorem dh_sqF2_ne_ukP : sqF2 ≠ ukP := by decide
@[simp] theorem dh_sqF2_ne_ukQ : sqF2 ≠ ukQ := by decide
@[simp] theorem dh_sqF2_ne_ukK : sqF2 ≠ ukK := by decide
@[simp] theorem dh_sqF2_ne_ukLp : sqF2 ≠ ukLp := by decide
@[simp] theorem dh_sqF2_ne_ukLl : sqF2 ≠ ukLl := by decide
@[simp] theorem dh_sqF2_ne_hnE : sqF2 ≠ hnE := by decide
@[simp] theorem dh_sqF2_ne_hnH : sqF2 ≠ hnH := by decide
@[simp] theorem dh_sqF2_ne_hnN : sqF2 ≠ hnN := by decide
@[simp] theorem dh_sqF2_ne_hnP : sqF2 ≠ hnP := by decide
@[simp] theorem dh_sqF2_ne_hnQ : sqF2 ≠ hnQ := by decide
@[simp] theorem dh_sqF2_ne_hnK : sqF2 ≠ hnK := by decide
@[simp] theorem dh_sqF2_ne_hnV : sqF2 ≠ hnV := by decide
@[simp] theorem dh_sqF2_ne_sqA : sqF2 ≠ sqA := by decide
@[simp] theorem dh_sqF2_ne_sqB : sqF2 ≠ sqB := by decide
@[simp] theorem dh_sqF2_ne_sqF1 : sqF2 ≠ sqF1 := by decide
@[simp] theorem dh_sqF2_ne_sqH : sqF2 ≠ sqH := by decide
@[simp] theorem dh_sqF2_ne_sqN1 : sqF2 ≠ sqN1 := by decide
@[simp] theorem dh_sqF2_ne_sqH2 : sqF2 ≠ sqH2 := by decide
@[simp] theorem dh_sqF2_ne_sqN2 : sqF2 ≠ sqN2 := by decide
@[simp] theorem dh_sqF2_ne_lFl : sqF2 ≠ lFl := by decide
@[simp] theorem dh_lFl_ne_sqF2 : lFl ≠ sqF2 := by decide
@[simp] theorem dh_sqF2_ne_lDh : sqF2 ≠ lDh := by decide
@[simp] theorem dh_lDh_ne_sqF2 : lDh ≠ sqF2 := by decide
@[simp] theorem dh_sqF2_ne_lDt : sqF2 ≠ lDt := by decide
@[simp] theorem dh_lDt_ne_sqF2 : lDt ≠ sqF2 := by decide
@[simp] theorem dh_sqF2_ne_lDg : sqF2 ≠ lDg := by decide
@[simp] theorem dh_lDg_ne_sqF2 : lDg ≠ sqF2 := by decide
@[simp] theorem dh_sqF2_ne_lDi : sqF2 ≠ lDi := by decide
@[simp] theorem dh_lDi_ne_sqF2 : lDi ≠ sqF2 := by decide
@[simp] theorem dh_sqF2_ne_lRp : sqF2 ≠ lRp := by decide
@[simp] theorem dh_lRp_ne_sqF2 : lRp ≠ sqF2 := by decide
@[simp] theorem dh_sqF2_ne_lRn : sqF2 ≠ lRn := by decide
@[simp] theorem dh_lRn_ne_sqF2 : lRn ≠ sqF2 := by decide
@[simp] theorem dh_sqF2_ne_lFle : sqF2 ≠ lFle := by decide
@[simp] theorem dh_lFle_ne_sqF2 : lFle ≠ sqF2 := by decide
@[simp] theorem dh_sqF2_ne_lKb : sqF2 ≠ lKb := by decide
@[simp] theorem dh_lKb_ne_sqF2 : lKb ≠ sqF2 := by decide
@[simp] theorem dh_sqF2_ne_lDir : sqF2 ≠ lDir := by decide
@[simp] theorem dh_lDir_ne_sqF2 : lDir ≠ sqF2 := by decide
@[simp] theorem dh_sqF2_ne_lFln : sqF2 ≠ lFln := by decide
@[simp] theorem dh_lFln_ne_sqF2 : lFln ≠ sqF2 := by decide
@[simp] theorem dh_sqF2_ne_lFll : sqF2 ≠ lFll := by decide
@[simp] theorem dh_lFll_ne_sqF2 : lFll ≠ sqF2 := by decide
@[simp] theorem dh_sqF2_ne_lFls : sqF2 ≠ lFls := by decide
@[simp] theorem dh_lFls_ne_sqF2 : lFls ≠ sqF2 := by decide
@[simp] theorem dh_sqH_ne_ukE : sqH ≠ ukE := by decide
@[simp] theorem dh_sqH_ne_ukH : sqH ≠ ukH := by decide
@[simp] theorem dh_sqH_ne_ukN : sqH ≠ ukN := by decide
@[simp] theorem dh_sqH_ne_ukU : sqH ≠ ukU := by decide
@[simp] theorem dh_sqH_ne_ukP : sqH ≠ ukP := by decide
@[simp] theorem dh_sqH_ne_ukQ : sqH ≠ ukQ := by decide
@[simp] theorem dh_sqH_ne_ukK : sqH ≠ ukK := by decide
@[simp] theorem dh_sqH_ne_ukLp : sqH ≠ ukLp := by decide
@[simp] theorem dh_sqH_ne_ukLl : sqH ≠ ukLl := by decide
@[simp] theorem dh_sqH_ne_hnE : sqH ≠ hnE := by decide
@[simp] theorem dh_sqH_ne_hnH : sqH ≠ hnH := by decide
@[simp] theorem dh_sqH_ne_hnN : sqH ≠ hnN := by decide
@[simp] theorem dh_sqH_ne_hnP : sqH ≠ hnP := by decide
@[simp] theorem dh_sqH_ne_hnQ : sqH ≠ hnQ := by decide
@[simp] theorem dh_sqH_ne_hnK : sqH ≠ hnK := by decide
@[simp] theorem dh_sqH_ne_hnV : sqH ≠ hnV := by decide
@[simp] theorem dh_sqH_ne_sqA : sqH ≠ sqA := by decide
@[simp] theorem dh_sqH_ne_sqB : sqH ≠ sqB := by decide
@[simp] theorem dh_sqH_ne_sqF1 : sqH ≠ sqF1 := by decide
@[simp] theorem dh_sqH_ne_sqF2 : sqH ≠ sqF2 := by decide
@[simp] theorem dh_sqH_ne_sqN1 : sqH ≠ sqN1 := by decide
@[simp] theorem dh_sqH_ne_sqH2 : sqH ≠ sqH2 := by decide
@[simp] theorem dh_sqH_ne_sqN2 : sqH ≠ sqN2 := by decide
@[simp] theorem dh_sqH_ne_lFl : sqH ≠ lFl := by decide
@[simp] theorem dh_lFl_ne_sqH : lFl ≠ sqH := by decide
@[simp] theorem dh_sqH_ne_lDh : sqH ≠ lDh := by decide
@[simp] theorem dh_lDh_ne_sqH : lDh ≠ sqH := by decide
@[simp] theorem dh_sqH_ne_lDt : sqH ≠ lDt := by decide
@[simp] theorem dh_lDt_ne_sqH : lDt ≠ sqH := by decide
@[simp] theorem dh_sqH_ne_lDg : sqH ≠ lDg := by decide
@[simp] theorem dh_lDg_ne_sqH : lDg ≠ sqH := by decide
@[simp] theorem dh_sqH_ne_lDi : sqH ≠ lDi := by decide
@[simp] theorem dh_lDi_ne_sqH : lDi ≠ sqH := by decide
@[simp] theorem dh_sqH_ne_lRp : sqH ≠ lRp := by decide
@[simp] theorem dh_lRp_ne_sqH : lRp ≠ sqH := by decide
@[simp] theorem dh_sqH_ne_lRn : sqH ≠ lRn := by decide
@[simp] theorem dh_lRn_ne_sqH : lRn ≠ sqH := by decide
@[simp] theorem dh_sqH_ne_lFle : sqH ≠ lFle := by decide
@[simp] theorem dh_lFle_ne_sqH : lFle ≠ sqH := by decide
@[simp] theorem dh_sqH_ne_lKb : sqH ≠ lKb := by decide
@[simp] theorem dh_lKb_ne_sqH : lKb ≠ sqH := by decide
@[simp] theorem dh_sqH_ne_lDir : sqH ≠ lDir := by decide
@[simp] theorem dh_lDir_ne_sqH : lDir ≠ sqH := by decide
@[simp] theorem dh_sqH_ne_lFln : sqH ≠ lFln := by decide
@[simp] theorem dh_lFln_ne_sqH : lFln ≠ sqH := by decide
@[simp] theorem dh_sqH_ne_lFll : sqH ≠ lFll := by decide
@[simp] theorem dh_lFll_ne_sqH : lFll ≠ sqH := by decide
@[simp] theorem dh_sqH_ne_lFls : sqH ≠ lFls := by decide
@[simp] theorem dh_lFls_ne_sqH : lFls ≠ sqH := by decide
@[simp] theorem dh_sqN1_ne_ukE : sqN1 ≠ ukE := by decide
@[simp] theorem dh_sqN1_ne_ukH : sqN1 ≠ ukH := by decide
@[simp] theorem dh_sqN1_ne_ukN : sqN1 ≠ ukN := by decide
@[simp] theorem dh_sqN1_ne_ukU : sqN1 ≠ ukU := by decide
@[simp] theorem dh_sqN1_ne_ukP : sqN1 ≠ ukP := by decide
@[simp] theorem dh_sqN1_ne_ukQ : sqN1 ≠ ukQ := by decide
@[simp] theorem dh_sqN1_ne_ukK : sqN1 ≠ ukK := by decide
@[simp] theorem dh_sqN1_ne_ukLp : sqN1 ≠ ukLp := by decide
@[simp] theorem dh_sqN1_ne_ukLl : sqN1 ≠ ukLl := by decide
@[simp] theorem dh_sqN1_ne_hnE : sqN1 ≠ hnE := by decide
@[simp] theorem dh_sqN1_ne_hnH : sqN1 ≠ hnH := by decide
@[simp] theorem dh_sqN1_ne_hnN : sqN1 ≠ hnN := by decide
@[simp] theorem dh_sqN1_ne_hnP : sqN1 ≠ hnP := by decide
@[simp] theorem dh_sqN1_ne_hnQ : sqN1 ≠ hnQ := by decide
@[simp] theorem dh_sqN1_ne_hnK : sqN1 ≠ hnK := by decide
@[simp] theorem dh_sqN1_ne_hnV : sqN1 ≠ hnV := by decide
@[simp] theorem dh_sqN1_ne_sqA : sqN1 ≠ sqA := by decide
@[simp] theorem dh_sqN1_ne_sqB : sqN1 ≠ sqB := by decide
@[simp] theorem dh_sqN1_ne_sqF1 : sqN1 ≠ sqF1 := by decide
@[simp] theorem dh_sqN1_ne_sqF2 : sqN1 ≠ sqF2 := by decide
@[simp] theorem dh_sqN1_ne_sqH : sqN1 ≠ sqH := by decide
@[simp] theorem dh_sqN1_ne_sqH2 : sqN1 ≠ sqH2 := by decide
@[simp] theorem dh_sqN1_ne_sqN2 : sqN1 ≠ sqN2 := by decide
@[simp] theorem dh_sqN1_ne_lFl : sqN1 ≠ lFl := by decide
@[simp] theorem dh_lFl_ne_sqN1 : lFl ≠ sqN1 := by decide
@[simp] theorem dh_sqN1_ne_lDh : sqN1 ≠ lDh := by decide
@[simp] theorem dh_lDh_ne_sqN1 : lDh ≠ sqN1 := by decide
@[simp] theorem dh_sqN1_ne_lDt : sqN1 ≠ lDt := by decide
@[simp] theorem dh_lDt_ne_sqN1 : lDt ≠ sqN1 := by decide
@[simp] theorem dh_sqN1_ne_lDg : sqN1 ≠ lDg := by decide
@[simp] theorem dh_lDg_ne_sqN1 : lDg ≠ sqN1 := by decide
@[simp] theorem dh_sqN1_ne_lDi : sqN1 ≠ lDi := by decide
@[simp] theorem dh_lDi_ne_sqN1 : lDi ≠ sqN1 := by decide
@[simp] theorem dh_sqN1_ne_lRp : sqN1 ≠ lRp := by decide
@[simp] theorem dh_lRp_ne_sqN1 : lRp ≠ sqN1 := by decide
@[simp] theorem dh_sqN1_ne_lRn : sqN1 ≠ lRn := by decide
@[simp] theorem dh_lRn_ne_sqN1 : lRn ≠ sqN1 := by decide
@[simp] theorem dh_sqN1_ne_lFle : sqN1 ≠ lFle := by decide
@[simp] theorem dh_lFle_ne_sqN1 : lFle ≠ sqN1 := by decide
@[simp] theorem dh_sqN1_ne_lKb : sqN1 ≠ lKb := by decide
@[simp] theorem dh_lKb_ne_sqN1 : lKb ≠ sqN1 := by decide
@[simp] theorem dh_sqN1_ne_lDir : sqN1 ≠ lDir := by decide
@[simp] theorem dh_lDir_ne_sqN1 : lDir ≠ sqN1 := by decide
@[simp] theorem dh_sqN1_ne_lFln : sqN1 ≠ lFln := by decide
@[simp] theorem dh_lFln_ne_sqN1 : lFln ≠ sqN1 := by decide
@[simp] theorem dh_sqN1_ne_lFll : sqN1 ≠ lFll := by decide
@[simp] theorem dh_lFll_ne_sqN1 : lFll ≠ sqN1 := by decide
@[simp] theorem dh_sqN1_ne_lFls : sqN1 ≠ lFls := by decide
@[simp] theorem dh_lFls_ne_sqN1 : lFls ≠ sqN1 := by decide
@[simp] theorem dh_sqH2_ne_ukE : sqH2 ≠ ukE := by decide
@[simp] theorem dh_sqH2_ne_ukH : sqH2 ≠ ukH := by decide
@[simp] theorem dh_sqH2_ne_ukN : sqH2 ≠ ukN := by decide
@[simp] theorem dh_sqH2_ne_ukU : sqH2 ≠ ukU := by decide
@[simp] theorem dh_sqH2_ne_ukP : sqH2 ≠ ukP := by decide
@[simp] theorem dh_sqH2_ne_ukQ : sqH2 ≠ ukQ := by decide
@[simp] theorem dh_sqH2_ne_ukK : sqH2 ≠ ukK := by decide
@[simp] theorem dh_sqH2_ne_ukLp : sqH2 ≠ ukLp := by decide
@[simp] theorem dh_sqH2_ne_ukLl : sqH2 ≠ ukLl := by decide
@[simp] theorem dh_sqH2_ne_hnE : sqH2 ≠ hnE := by decide
@[simp] theorem dh_sqH2_ne_hnH : sqH2 ≠ hnH := by decide
@[simp] theorem dh_sqH2_ne_hnN : sqH2 ≠ hnN := by decide
@[simp] theorem dh_sqH2_ne_hnP : sqH2 ≠ hnP := by decide
@[simp] theorem dh_sqH2_ne_hnQ : sqH2 ≠ hnQ := by decide
@[simp] theorem dh_sqH2_ne_hnK : sqH2 ≠ hnK := by decide
@[simp] theorem dh_sqH2_ne_hnV : sqH2 ≠ hnV := by decide
@[simp] theorem dh_sqH2_ne_sqA : sqH2 ≠ sqA := by decide
@[simp] theorem dh_sqH2_ne_sqB : sqH2 ≠ sqB := by decide
@[simp] theorem dh_sqH2_ne_sqF1 : sqH2 ≠ sqF1 := by decide
@[simp] theorem dh_sqH2_ne_sqF2 : sqH2 ≠ sqF2 := by decide
@[simp] theorem dh_sqH2_ne_sqH : sqH2 ≠ sqH := by decide
@[simp] theorem dh_sqH2_ne_sqN1 : sqH2 ≠ sqN1 := by decide
@[simp] theorem dh_sqH2_ne_sqN2 : sqH2 ≠ sqN2 := by decide
@[simp] theorem dh_sqH2_ne_lFl : sqH2 ≠ lFl := by decide
@[simp] theorem dh_lFl_ne_sqH2 : lFl ≠ sqH2 := by decide
@[simp] theorem dh_sqH2_ne_lDh : sqH2 ≠ lDh := by decide
@[simp] theorem dh_lDh_ne_sqH2 : lDh ≠ sqH2 := by decide
@[simp] theorem dh_sqH2_ne_lDt : sqH2 ≠ lDt := by decide
@[simp] theorem dh_lDt_ne_sqH2 : lDt ≠ sqH2 := by decide
@[simp] theorem dh_sqH2_ne_lDg : sqH2 ≠ lDg := by decide
@[simp] theorem dh_lDg_ne_sqH2 : lDg ≠ sqH2 := by decide
@[simp] theorem dh_sqH2_ne_lDi : sqH2 ≠ lDi := by decide
@[simp] theorem dh_lDi_ne_sqH2 : lDi ≠ sqH2 := by decide
@[simp] theorem dh_sqH2_ne_lRp : sqH2 ≠ lRp := by decide
@[simp] theorem dh_lRp_ne_sqH2 : lRp ≠ sqH2 := by decide
@[simp] theorem dh_sqH2_ne_lRn : sqH2 ≠ lRn := by decide
@[simp] theorem dh_lRn_ne_sqH2 : lRn ≠ sqH2 := by decide
@[simp] theorem dh_sqH2_ne_lFle : sqH2 ≠ lFle := by decide
@[simp] theorem dh_lFle_ne_sqH2 : lFle ≠ sqH2 := by decide
@[simp] theorem dh_sqH2_ne_lKb : sqH2 ≠ lKb := by decide
@[simp] theorem dh_lKb_ne_sqH2 : lKb ≠ sqH2 := by decide
@[simp] theorem dh_sqH2_ne_lDir : sqH2 ≠ lDir := by decide
@[simp] theorem dh_lDir_ne_sqH2 : lDir ≠ sqH2 := by decide
@[simp] theorem dh_sqH2_ne_lFln : sqH2 ≠ lFln := by decide
@[simp] theorem dh_lFln_ne_sqH2 : lFln ≠ sqH2 := by decide
@[simp] theorem dh_sqH2_ne_lFll : sqH2 ≠ lFll := by decide
@[simp] theorem dh_lFll_ne_sqH2 : lFll ≠ sqH2 := by decide
@[simp] theorem dh_sqH2_ne_lFls : sqH2 ≠ lFls := by decide
@[simp] theorem dh_lFls_ne_sqH2 : lFls ≠ sqH2 := by decide
@[simp] theorem dh_sqN2_ne_ukE : sqN2 ≠ ukE := by decide
@[simp] theorem dh_sqN2_ne_ukH : sqN2 ≠ ukH := by decide
@[simp] theorem dh_sqN2_ne_ukN : sqN2 ≠ ukN := by decide
@[simp] theorem dh_sqN2_ne_ukU : sqN2 ≠ ukU := by decide
@[simp] theorem dh_sqN2_ne_ukP : sqN2 ≠ ukP := by decide
@[simp] theorem dh_sqN2_ne_ukQ : sqN2 ≠ ukQ := by decide
@[simp] theorem dh_sqN2_ne_ukK : sqN2 ≠ ukK := by decide
@[simp] theorem dh_sqN2_ne_ukLp : sqN2 ≠ ukLp := by decide
@[simp] theorem dh_sqN2_ne_ukLl : sqN2 ≠ ukLl := by decide
@[simp] theorem dh_sqN2_ne_hnE : sqN2 ≠ hnE := by decide
@[simp] theorem dh_sqN2_ne_hnH : sqN2 ≠ hnH := by decide
@[simp] theorem dh_sqN2_ne_hnN : sqN2 ≠ hnN := by decide
@[simp] theorem dh_sqN2_ne_hnP : sqN2 ≠ hnP := by decide
@[simp] theorem dh_sqN2_ne_hnQ : sqN2 ≠ hnQ := by decide
@[simp] theorem dh_sqN2_ne_hnK : sqN2 ≠ hnK := by decide
@[simp] theorem dh_sqN2_ne_hnV : sqN2 ≠ hnV := by decide
@[simp] theorem dh_sqN2_ne_sqA : sqN2 ≠ sqA := by decide
@[simp] theorem dh_sqN2_ne_sqB : sqN2 ≠ sqB := by decide
@[simp] theorem dh_sqN2_ne_sqF1 : sqN2 ≠ sqF1 := by decide
@[simp] theorem dh_sqN2_ne_sqF2 : sqN2 ≠ sqF2 := by decide
@[simp] theorem dh_sqN2_ne_sqH : sqN2 ≠ sqH := by decide
@[simp] theorem dh_sqN2_ne_sqN1 : sqN2 ≠ sqN1 := by decide
@[simp] theorem dh_sqN2_ne_sqH2 : sqN2 ≠ sqH2 := by decide
@[simp] theorem dh_sqN2_ne_lFl : sqN2 ≠ lFl := by decide
@[simp] theorem dh_lFl_ne_sqN2 : lFl ≠ sqN2 := by decide
@[simp] theorem dh_sqN2_ne_lDh : sqN2 ≠ lDh := by decide
@[simp] theorem dh_lDh_ne_sqN2 : lDh ≠ sqN2 := by decide
@[simp] theorem dh_sqN2_ne_lDt : sqN2 ≠ lDt := by decide
@[simp] theorem dh_lDt_ne_sqN2 : lDt ≠ sqN2 := by decide
@[simp] theorem dh_sqN2_ne_lDg : sqN2 ≠ lDg := by decide
@[simp] theorem dh_lDg_ne_sqN2 : lDg ≠ sqN2 := by decide
@[simp] theorem dh_sqN2_ne_lDi : sqN2 ≠ lDi := by decide
@[simp] theorem dh_lDi_ne_sqN2 : lDi ≠ sqN2 := by decide
@[simp] theorem dh_sqN2_ne_lRp : sqN2 ≠ lRp := by decide
@[simp] theorem dh_lRp_ne_sqN2 : lRp ≠ sqN2 := by decide
@[simp] theorem dh_sqN2_ne_lRn : sqN2 ≠ lRn := by decide
@[simp] theorem dh_lRn_ne_sqN2 : lRn ≠ sqN2 := by decide
@[simp] theorem dh_sqN2_ne_lFle : sqN2 ≠ lFle := by decide
@[simp] theorem dh_lFle_ne_sqN2 : lFle ≠ sqN2 := by decide
@[simp] theorem dh_sqN2_ne_lKb : sqN2 ≠ lKb := by decide
@[simp] theorem dh_lKb_ne_sqN2 : lKb ≠ sqN2 := by decide
@[simp] theorem dh_sqN2_ne_lDir : sqN2 ≠ lDir := by decide
@[simp] theorem dh_lDir_ne_sqN2 : lDir ≠ sqN2 := by decide
@[simp] theorem dh_sqN2_ne_lFln : sqN2 ≠ lFln := by decide
@[simp] theorem dh_lFln_ne_sqN2 : lFln ≠ sqN2 := by decide
@[simp] theorem dh_sqN2_ne_lFll : sqN2 ≠ lFll := by decide
@[simp] theorem dh_lFll_ne_sqN2 : lFll ≠ sqN2 := by decide
@[simp] theorem dh_sqN2_ne_lFls : sqN2 ≠ lFls := by decide
@[simp] theorem dh_lFls_ne_sqN2 : lFls ≠ sqN2 := by decide

def ukLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, ukH, ukN, ukU, ukP, ukQ, ukK, ukLp, ukLl]
def ukBody (C : Ctx) : ProgHOL 64 := prologue ukLocals (.seq (.call (some (some (.local, ukH), none)) fGetAppFn [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv ukE)]) (.ite (tagIsE ukH 3) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv ukH)) (.seq eViewP (.seq (.assign .local ukN (.load .one (vv lRp))) (.seq (.assign .local ukU (.load .one (.op .add [(vv lRp), (.const 8)]))) (envFindP C ukP (vv ukN) (.ite (.cmp .equal (vv ukP) (.const 0)) (.return (.const 0)) (.seq (.assign .local ukQ (.op .sub [(vv ukP), (.const 1)])) (.seq (.assign .local ukK (.load .one (vv ukQ))) (.ite (.cmp .notEqual (vv ukK) (.const 1)) (.return (.const 0)) (.seq (.assign .local ukLp (.load .one (.op .add [(vv ukQ), (.const 16)]))) (.seq (.assign .local ukLl (.load .one (vv ukLp))) (.seq (.assign .local lFl (vv lFls)) (.seq (.assign .local lDh (vv ukU)) (.seq lsViewP (.return (.cmp .equal (vv lRn) (vv ukLl)))))))))))))))))) (.return (.const 0))))
def hnLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, hnH, hnN, hnP, hnQ, hnK, hnV]
def hnBody (C : Ctx) : ProgHOL 64 := prologue hnLocals (.seq (.call (some (some (.local, hnH), none)) fGetAppFn [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv hnE)]) (.ite (tagIsE hnH 3) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv hnH)) (.seq eViewP (.seq (.assign .local hnN (.load .one (vv lRp))) (envFindP C hnP (vv hnN) (.ite (.cmp .equal (vv hnP) (.const 0)) (.return (.const 0)) (.seq (.assign .local hnQ (.op .sub [(vv hnP), (.const 1)])) (.seq (.assign .local hnK (.load .one (vv hnQ))) (.ite (.cmp .notEqual (vv hnK) (.const 1)) (.return (.const 0)) (.seq (.assign .local hnV (.load .one (.op .add [(vv hnQ), (.const 40)]))) (.return (vv hnV)))))))))))) (.return (.const 0))))
def sqParams : List MlS := [sqA, sqB]
def sqLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, sqF1, sqF2, sqH, sqN1, sqH2, sqN2]
def sqBody : ProgHOL 64 := prologue sqLocals (.ite (tagIs4E sqA) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv sqA)) (.seq eViewP (.seq (.assign .local sqF1 (.load .one (vv lRp))) (.ite (tagIs4E sqB) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv sqB)) (.seq eViewP (.seq (.assign .local sqF2 (.load .one (vv lRp))) (.seq (.call (some (some (.local, sqH), none)) fGetAppFn [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv sqF1)]) (.ite (tagIsE sqH 3) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv sqH)) (.seq eViewP (.seq (.assign .local sqN1 (.load .one (vv lRp))) (.seq (.call (some (some (.local, sqH2), none)) fGetAppFn [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv sqF2)]) (.ite (tagIsE sqH2 3) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv sqH2)) (.seq eViewP (.seq (.assign .local sqN2 (.load .one (vv lRp))) (.return (.cmp .equal (vv sqN1) (vv sqN2))))))) (.return (.const 0)))))))) (.return (.const 0)))))))) (.return (.const 0))))))) (.return (.const 0)))

section
variable {σ : Type}

theorem uk_spec (C : Ctx)
    (hok : CtxOK C)
    (hcaf : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one))
    (hmg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hmp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (s : AState) (e : EIdx) :
    SpecR (σ := σ) (Pre C s [(ukE, Enc.idxW e)]) (ukBody C) s (unfoldableHead C.fe e) (PostB C) := by
  refine specR_prologue (postB_locals C) (Knot.params_none C ukLocals [ukE] [Enc.idxW e] (by decide) (by decide)) ?_
  unfold unfoldableHead
  refine specR_callNIM (C := C) ukH fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv ukE]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e] (by decide) rfl (by decide) hcaf
    ⟨rfl, by simp +decide [Env.get, ukLocals, ctxEnv], trivial⟩
    (fun x w' s' st => getAppFn coreWalkFuel e s = .ok (x, s') ∧ Post C s x w' s' st)
    (fun x w' s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec C hcaf coreWalkFuel e s CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun h w' s' st ⟨hrun, hw, hs, _⟩ => ?_)
  subst hw
  have hs' : s = s' := hs.symm
  subst hs'
  refine Knot.specR_tagIteV ukH h 3 (by decide) (by decide) (by simp) (fun htc => ?_) (fun htc => ?_)
  swap
  · rw [if_neg (show ¬ (h.tag == ETag.const) = true by simpa [ETag.const] using htc)]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [if_pos (show (h.tag == ETag.const) = true by simp [htc, ETag.const])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv ukH) (Enc.idxW h) (by decide) (by simp) ?_
  refine specR_viewP h (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
    (fun v P hv htn _ => ?_)
  refine specR_congr (Big.view_bind_eq h v _ s hv) ?_
  have h3 : v.tagN = 3 := by rw [htn, htc]; rfl
  obtain ⟨c, us, rfl⟩ := UD.tagN_const h3
  dsimp only
  refine specR_loadI' ukN (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW c) (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW c) [Enc.idxW us] []) ?_
  refine specR_loadI' ukU _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW us) (by decide) (by simp +decide [sev]) rfl
    (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW c) (Enc.idxW us) [] []) ?_
  refine specR_dropM ?_
  refine specR_envFindI hok hmg hmp ukP (vv ukN) c (by decide) (by simp) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  have hrel := find_rel hok c
  revert hrel
  rcases hfind : C.fe.find? c with _ | ci
  · intro hrel; simp only at hrel; rw [hrel]
    refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  intro ⟨o, hm, hci⟩
  rw [hm]
  refine specR_atEntry fun t ht => ?_
  have hoE : o < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI ukQ _ (ecell C o) (by decide) (by simp [sev, optWG]; exact BitVec.add_sub_cancel _ _) ?_
  rcases ci with cv | ⟨cv, val, hint⟩ | cv | ⟨cv, caps⟩ | ⟨cv, np, nf, ind⟩ | ⟨cv, mi, rp, isK, rules⟩
  · refine specR_envLoadI ukK (vv ukQ) o 0 (by decide) (by simp) hci.2 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_envLoadI ukK (vv ukQ) o 1 (by decide) (by simp) hci.2.1 ?_
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    have hcv : CVE C.EB C.EH (o + 1) cv := hci.1
    obtain ⟨_, ⟨w, hw, ok, hw', hblk⟩, _⟩ := hcv
    subst hw'
    refine specR_envLoadI ukLp (.op .add [vv ukQ, .const 16]) (o + 2) _ (by decide)
      (by simp [sev, vv]; exact UD.ecell_add16 C o) (by simpa using hw) ?_
    have hl0 : C.EH[ok]? = some (BitVec.ofNat 64 cv.levelParams.length) := by
      have := hblk.1; simpa using this
    refine specR_envLoadI ukLl (vv ukLp) ok _ (by decide) (by simp; rfl) hl0 ?_
    have hlp : cv.levelParams.length < 2 ^ 61 := by
      have h1 := blkAt_len (show BlkAt C.EH ok (cv.levelParams.map Enc.idxW) from hblk)
      have h2 := ht.sr.env.1.len; have h3 := hok.envLay
      simp only [List.length_map] at h1; omega
    dsimp only
    refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv ukU) (Enc.idxW us) (by decide) (by simp) ?_
    refine specR_lsviewPI us (by simp) (by simp) (by simp +decide [Env.get, ctxEnv]) (by decide)
      (fun vl Pl hvl _ hvll => ?_)
    refine specR_runBind (viewLsLen_run us s vl hvl) ?_
    dsimp only
    have hvl' : vl.length < 2 ^ 61 := by simpa using hvll
    have heqw : BitVec.ofNat 64 vl.length = BitVec.ofNat 64 cv.levelParams.length ↔ vl.length = cv.levelParams.length :=
      UD.ofNat_eq_iff_small _ _ (by omega) (by omega)
    refine specR_returnI _ (boolW (vl.length == cv.levelParams.length)) ?_
      (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    by_cases hl : vl.length = cv.levelParams.length
    · simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hl, boolW]
    · have : BitVec.ofNat 64 vl.length ≠ BitVec.ofNat 64 cv.levelParams.length := fun x => hl (heqw.mp x)
      simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hl, this, boolW]
  · refine specR_envLoadI ukK (vv ukQ) o 2 (by decide) (by simp) hci.2 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_envLoadI ukK (vv ukQ) o 3 (by decide) (by simp) hci.2.1 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_envLoadI ukK (vv ukQ) o 4 (by decide) (by simp) hci.2.1 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_envLoadI ukK (vv ukQ) o 5 (by decide) (by simp) hci.2.1 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

def PostHn (C : Ctx) (a : ConLeche.ReducibilityHint) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ w = BitVec.ofNat 64 (hintN a) ∧ hintN a < 2 ^ 63 ∧ SR (ctxH C H') s' st

theorem postHn_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostHn C a w s' st → PostHn C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', h1, h2, h3, h4⟩ => ⟨H', h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl⟩

theorem hn_spec (C : Ctx)
    (hok : CtxOK C)
    (hcaf : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one))
    (hmg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hmp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (s : AState) (e : EIdx) :
    SpecR (σ := σ) (Pre C s [(hnE, Enc.idxW e)]) (hnBody C) s (headHint C.fe e) (PostHn C) := by
  refine specR_prologue (postHn_locals C) (Knot.params_none C hnLocals [hnE] [Enc.idxW e] (by decide) (by decide)) ?_
  unfold headHint
  refine specR_callNIM (C := C) hnH fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv hnE]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e] (by decide) rfl (by decide) hcaf
    ⟨rfl, by simp +decide [Env.get, hnLocals, ctxEnv], trivial⟩
    (fun x w' s' st => getAppFn coreWalkFuel e s = .ok (x, s') ∧ Post C s x w' s' st)
    (fun x w' s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec C hcaf coreWalkFuel e s CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun h w' s' st ⟨hrun, hw, hs, _⟩ => ?_)
  subst hw
  have hs' : s = s' := hs.symm
  subst hs'
  refine Knot.specR_tagIteV hnH h 3 (by decide) (by decide) (by simp) (fun htc => ?_) (fun htc => ?_)
  swap
  · rw [if_neg (show ¬ (h.tag == ETag.const) = true by simpa [ETag.const] using htc)]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, by decide, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [if_pos (show (h.tag == ETag.const) = true by simp [htc, ETag.const])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv hnH) (Enc.idxW h) (by decide) (by simp) ?_
  refine specR_viewP h (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
    (fun v P hv htn _ => ?_)
  refine specR_congr (Big.view_bind_eq h v _ s hv) ?_
  have h3 : v.tagN = 3 := by rw [htn, htc]; rfl
  obtain ⟨c, us, rfl⟩ := UD.tagN_const h3
  dsimp only
  refine specR_loadI' hnN (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW c) (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW c) [Enc.idxW us] []) ?_
  refine specR_dropM ?_
  refine specR_envFindI hok hmg hmp hnP (vv hnN) c (by decide) (by simp) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  have hrel := find_rel hok c
  revert hrel
  rcases hfind : C.fe.find? c with _ | ci
  · intro hrel; simp only at hrel; rw [hrel]
    refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, by decide, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  intro ⟨o, hm, hci⟩
  rw [hm]
  refine specR_atEntry fun t ht => ?_
  have hoE : o < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI hnQ _ (ecell C o) (by decide) (by simp [sev, optWG]; exact BitVec.add_sub_cancel _ _) ?_
  rcases ci with cv | ⟨cv, val, hint⟩ | cv | ⟨cv, caps⟩ | ⟨cv, np, nf, ind⟩ | ⟨cv, mi, rp, isK, rules⟩
  · refine specR_envLoadI hnK (vv hnQ) o 0 (by decide) (by simp) hci.2 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, by decide, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_envLoadI hnK (vv hnQ) o 1 (by decide) (by simp) hci.2.1 ?_
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    obtain ⟨_, _, _, ⟨hh, hhl⟩⟩ := hci
    refine specR_envLoadI hnV (.op .add [vv hnQ, .const 40]) (o + 5) _ (by decide)
      (by simp [sev, vv]; simpa using ecell_add C o 5) hh ?_
    exact specR_returnI _ _ (by simp) (fun t ht => ⟨C.H, List.prefix_refl _, rfl, hhl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_envLoadI hnK (vv hnQ) o 2 (by decide) (by simp) hci.2 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, by decide, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_envLoadI hnK (vv hnQ) o 3 (by decide) (by simp) hci.2.1 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, by decide, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_envLoadI hnK (vv hnQ) o 4 (by decide) (by simp) hci.2.1 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, by decide, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_envLoadI hnK (vv hnQ) o 5 (by decide) (by simp) hci.2.1 ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, by decide, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem sq_spec (C : Ctx)
    (hcaf : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one))
    (s : AState) (a b : EIdx) :
    SpecR (σ := σ) (Pre C s (sqParams.zip [Enc.idxW a, Enc.idxW b])) sqBody s (sameConstHeads a b) (PostB C) := by
  refine specR_prologue (postB_locals C) (Knot.params_none C sqLocals sqParams _ (by decide) (by decide)) ?_
  unfold sameConstHeads
  refine specR_tag4IteE sqA a (by simp +decide [Env.get, sqParams, ctxEnv]) (fun h4 => ?_) (fun h4 => ?_)
  swap
  · rw [if_neg (show ¬ (a.tag == ETag.app) = true by simpa [ETag.app] using h4)]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [if_pos (show (a.tag == ETag.app) = true by simp [h4, ETag.app])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv sqA) (Enc.idxW a) (by decide) (by simp +decide [Env.get, sqParams, ctxEnv]) ?_
  refine specR_viewP a (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
    (fun va Pa hv htn _ => ?_)
  refine specR_congr (Big.view_bind_eq a va _ s hv) ?_
  have h4' : va.tagN = 4 := by rw [htn, h4]; rfl
  obtain ⟨f1, x1, rfl⟩ : ∃ f a, va = .app f a := by cases va <;> simp [ENodeView.tagN] at h4' ⊢
  dsimp only
  refine specR_loadI' sqF1 (vv lRp) Pa (Pa + BitVec.ofNat 64 0) (Enc.idxW f1) (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encApp] using wordsAt_mem0 Pa (Enc.idxW f1) [Enc.idxW x1] []) ?_
  refine specR_dropM ?_
  refine specR_tag4IteE sqB b (by simp +decide [Env.get, sqParams, ctxEnv]) (fun h4 => ?_) (fun h4 => ?_)
  swap
  · rw [if_neg (show ¬ (b.tag == ETag.app) = true by simpa [ETag.app] using h4)]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [if_pos (show (b.tag == ETag.app) = true by simp [h4, ETag.app])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv sqB) (Enc.idxW b) (by decide) (by simp +decide [Env.get, sqParams, ctxEnv]) ?_
  refine specR_viewP b (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
    (fun vb Pb hv htn _ => ?_)
  refine specR_congr (Big.view_bind_eq b vb _ s hv) ?_
  have h4' : vb.tagN = 4 := by rw [htn, h4]; rfl
  obtain ⟨f2, x2, rfl⟩ : ∃ f a, vb = .app f a := by cases vb <;> simp [ENodeView.tagN] at h4' ⊢
  dsimp only
  refine specR_loadI' sqF2 (vv lRp) Pb (Pb + BitVec.ofNat 64 0) (Enc.idxW f2) (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encApp] using wordsAt_mem0 Pb (Enc.idxW f2) [Enc.idxW x2] []) ?_
  refine specR_dropM ?_
  refine specR_callNIM (C := C) sqH fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv sqF1]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW f1] (by decide) rfl (by decide) hcaf
    ⟨rfl, by simp +decide [Env.get, sqParams, ctxEnv], trivial⟩
    (fun x w' s' st => getAppFn coreWalkFuel f1 s = .ok (x, s') ∧ Post C s x w' s' st)
    (fun x w' s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec C hcaf coreWalkFuel f1 s CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun h w' s' st ⟨hrun, hw, hs, _⟩ => ?_)
  subst hw
  have hs' : s = s' := hs.symm
  subst hs'
  refine Knot.specR_tagIteV sqH h 3 (by decide) (by decide) (by simp) (fun htc => ?_) (fun htc => ?_)
  swap
  · rw [if_neg (show ¬ (h.tag == ETag.const) = true by simpa [ETag.const] using htc)]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [if_pos (show (h.tag == ETag.const) = true by simp [htc, ETag.const])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv sqH) (Enc.idxW h) (by decide) (by simp) ?_
  refine specR_viewP h (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
    (fun v P hv htn _ => ?_)
  refine specR_congr (Big.view_bind_eq h v _ s hv) ?_
  have h3 : v.tagN = 3 := by rw [htn, htc]; rfl
  obtain ⟨c1, us1, rfl⟩ := UD.tagN_const h3
  dsimp only
  refine specR_loadI' sqN1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW c1) (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW c1) [Enc.idxW us1] []) ?_
  refine specR_dropM ?_
  refine specR_callNIM (C := C) sqH2 fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv sqF2]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW f2] (by decide) rfl (by decide) hcaf
    ⟨rfl, by simp +decide [Env.get, sqParams, ctxEnv], trivial⟩
    (fun x w' s' st => getAppFn coreWalkFuel f2 s = .ok (x, s') ∧ Post C s x w' s' st)
    (fun x w' s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec C hcaf coreWalkFuel f2 s CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun h2 w' s' st ⟨hrun, hw, hs, _⟩ => ?_)
  subst hw
  have hs' : s = s' := hs.symm
  subst hs'
  refine Knot.specR_tagIteV sqH2 h2 3 (by decide) (by decide) (by simp) (fun htc => ?_) (fun htc => ?_)
  swap
  · rw [if_neg (show ¬ (h2.tag == ETag.const) = true by simpa [ETag.const] using htc)]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [if_pos (show (h2.tag == ETag.const) = true by simp [htc, ETag.const])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv sqH2) (Enc.idxW h2) (by decide) (by simp) ?_
  refine specR_viewP h2 (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
    (fun v2 P2 hv htn _ => ?_)
  refine specR_congr (Big.view_bind_eq h2 v2 _ s hv) ?_
  have h3 : v2.tagN = 3 := by rw [htn, htc]; rfl
  obtain ⟨c2, us2, rfl⟩ := UD.tagN_const h3
  dsimp only
  refine specR_loadI' sqN2 (vv lRp) P2 (P2 + BitVec.ofNat 64 0) (Enc.idxW c2) (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P2 (Enc.idxW c2) [Enc.idxW us2] []) ?_
  refine specR_dropM ?_
  refine specR_returnI _ (boolW (c1 == c2)) ?_
    (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  by_cases hcc : c1 = c2
  · subst hcc; simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, boolW]
  · have : Enc.idxW c1 ≠ Enc.idxW c2 := fun x => hcc (Enc.idxW_inj x)
    simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hcc, this, boolW]

end

end ConPanqueque.T.WC
