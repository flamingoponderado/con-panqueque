import ConPanqueque.T.Core.DefeqLazy
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `defeqBody`: the definitional-equality body

The syntactic fast path, the constructor shortcut (right side first, then left), the lazy comparison. The eager flag
is the context's `side` (static). Callees are hypotheses restricted to an invariant `Q`.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def bqT := ofString "dbq_bqt"
def bqW := ofString "dbq_bqw"
def bqH := ofString "dbq_bqh"
def bqT2 := ofString "dbq_bqt2"
def bqW2 := ofString "dbq_bqw2"
def bqH2 := ofString "dbq_bqh2"
def bqR := ofString "dbq_bqr"

@[simp] theorem dbq_bqT_ne_bqW : bqT ≠ bqW := by decide
@[simp] theorem dbq_bqT_ne_bqH : bqT ≠ bqH := by decide
@[simp] theorem dbq_bqT_ne_bqT2 : bqT ≠ bqT2 := by decide
@[simp] theorem dbq_bqT_ne_bqW2 : bqT ≠ bqW2 := by decide
@[simp] theorem dbq_bqT_ne_bqH2 : bqT ≠ bqH2 := by decide
@[simp] theorem dbq_bqT_ne_bqR : bqT ≠ bqR := by decide
@[simp] theorem dbq_bqT_ne_lFl : bqT ≠ lFl := by decide
@[simp] theorem dbq_lFl_ne_bqT : lFl ≠ bqT := by decide
@[simp] theorem dbq_bqT_ne_lDh : bqT ≠ lDh := by decide
@[simp] theorem dbq_lDh_ne_bqT : lDh ≠ bqT := by decide
@[simp] theorem dbq_bqT_ne_lDt : bqT ≠ lDt := by decide
@[simp] theorem dbq_lDt_ne_bqT : lDt ≠ bqT := by decide
@[simp] theorem dbq_bqT_ne_lDg : bqT ≠ lDg := by decide
@[simp] theorem dbq_lDg_ne_bqT : lDg ≠ bqT := by decide
@[simp] theorem dbq_bqT_ne_lDi : bqT ≠ lDi := by decide
@[simp] theorem dbq_lDi_ne_bqT : lDi ≠ bqT := by decide
@[simp] theorem dbq_bqT_ne_lRp : bqT ≠ lRp := by decide
@[simp] theorem dbq_lRp_ne_bqT : lRp ≠ bqT := by decide
@[simp] theorem dbq_bqT_ne_lRn : bqT ≠ lRn := by decide
@[simp] theorem dbq_lRn_ne_bqT : lRn ≠ bqT := by decide
@[simp] theorem dbq_bqT_ne_lFle : bqT ≠ lFle := by decide
@[simp] theorem dbq_lFle_ne_bqT : lFle ≠ bqT := by decide
@[simp] theorem dbq_bqT_ne_lKb : bqT ≠ lKb := by decide
@[simp] theorem dbq_lKb_ne_bqT : lKb ≠ bqT := by decide
@[simp] theorem dbq_bqT_ne_lDir : bqT ≠ lDir := by decide
@[simp] theorem dbq_lDir_ne_bqT : lDir ≠ bqT := by decide
@[simp] theorem dbq_bqT_ne_lFln : bqT ≠ lFln := by decide
@[simp] theorem dbq_lFln_ne_bqT : lFln ≠ bqT := by decide
@[simp] theorem dbq_bqT_ne_lFll : bqT ≠ lFll := by decide
@[simp] theorem dbq_lFll_ne_bqT : lFll ≠ bqT := by decide
@[simp] theorem dbq_bqT_ne_lFls : bqT ≠ lFls := by decide
@[simp] theorem dbq_lFls_ne_bqT : lFls ≠ bqT := by decide
@[simp] theorem dbq_bqT_ne_kFu : bqT ≠ kFu := by decide
@[simp] theorem dbq_kFu_ne_bqT : kFu ≠ bqT := by decide
@[simp] theorem dbq_bqT_ne_kD : bqT ≠ kD := by decide
@[simp] theorem dbq_kD_ne_bqT : kD ≠ bqT := by decide
@[simp] theorem dbq_bqT_ne_kA : bqT ≠ kA := by decide
@[simp] theorem dbq_kA_ne_bqT : kA ≠ bqT := by decide
@[simp] theorem dbq_bqT_ne_kB : bqT ≠ kB := by decide
@[simp] theorem dbq_kB_ne_bqT : kB ≠ bqT := by decide
@[simp] theorem dbq_bqW_ne_bqT : bqW ≠ bqT := by decide
@[simp] theorem dbq_bqW_ne_bqH : bqW ≠ bqH := by decide
@[simp] theorem dbq_bqW_ne_bqT2 : bqW ≠ bqT2 := by decide
@[simp] theorem dbq_bqW_ne_bqW2 : bqW ≠ bqW2 := by decide
@[simp] theorem dbq_bqW_ne_bqH2 : bqW ≠ bqH2 := by decide
@[simp] theorem dbq_bqW_ne_bqR : bqW ≠ bqR := by decide
@[simp] theorem dbq_bqW_ne_lFl : bqW ≠ lFl := by decide
@[simp] theorem dbq_lFl_ne_bqW : lFl ≠ bqW := by decide
@[simp] theorem dbq_bqW_ne_lDh : bqW ≠ lDh := by decide
@[simp] theorem dbq_lDh_ne_bqW : lDh ≠ bqW := by decide
@[simp] theorem dbq_bqW_ne_lDt : bqW ≠ lDt := by decide
@[simp] theorem dbq_lDt_ne_bqW : lDt ≠ bqW := by decide
@[simp] theorem dbq_bqW_ne_lDg : bqW ≠ lDg := by decide
@[simp] theorem dbq_lDg_ne_bqW : lDg ≠ bqW := by decide
@[simp] theorem dbq_bqW_ne_lDi : bqW ≠ lDi := by decide
@[simp] theorem dbq_lDi_ne_bqW : lDi ≠ bqW := by decide
@[simp] theorem dbq_bqW_ne_lRp : bqW ≠ lRp := by decide
@[simp] theorem dbq_lRp_ne_bqW : lRp ≠ bqW := by decide
@[simp] theorem dbq_bqW_ne_lRn : bqW ≠ lRn := by decide
@[simp] theorem dbq_lRn_ne_bqW : lRn ≠ bqW := by decide
@[simp] theorem dbq_bqW_ne_lFle : bqW ≠ lFle := by decide
@[simp] theorem dbq_lFle_ne_bqW : lFle ≠ bqW := by decide
@[simp] theorem dbq_bqW_ne_lKb : bqW ≠ lKb := by decide
@[simp] theorem dbq_lKb_ne_bqW : lKb ≠ bqW := by decide
@[simp] theorem dbq_bqW_ne_lDir : bqW ≠ lDir := by decide
@[simp] theorem dbq_lDir_ne_bqW : lDir ≠ bqW := by decide
@[simp] theorem dbq_bqW_ne_lFln : bqW ≠ lFln := by decide
@[simp] theorem dbq_lFln_ne_bqW : lFln ≠ bqW := by decide
@[simp] theorem dbq_bqW_ne_lFll : bqW ≠ lFll := by decide
@[simp] theorem dbq_lFll_ne_bqW : lFll ≠ bqW := by decide
@[simp] theorem dbq_bqW_ne_lFls : bqW ≠ lFls := by decide
@[simp] theorem dbq_lFls_ne_bqW : lFls ≠ bqW := by decide
@[simp] theorem dbq_bqW_ne_kFu : bqW ≠ kFu := by decide
@[simp] theorem dbq_kFu_ne_bqW : kFu ≠ bqW := by decide
@[simp] theorem dbq_bqW_ne_kD : bqW ≠ kD := by decide
@[simp] theorem dbq_kD_ne_bqW : kD ≠ bqW := by decide
@[simp] theorem dbq_bqW_ne_kA : bqW ≠ kA := by decide
@[simp] theorem dbq_kA_ne_bqW : kA ≠ bqW := by decide
@[simp] theorem dbq_bqW_ne_kB : bqW ≠ kB := by decide
@[simp] theorem dbq_kB_ne_bqW : kB ≠ bqW := by decide
@[simp] theorem dbq_bqH_ne_bqT : bqH ≠ bqT := by decide
@[simp] theorem dbq_bqH_ne_bqW : bqH ≠ bqW := by decide
@[simp] theorem dbq_bqH_ne_bqT2 : bqH ≠ bqT2 := by decide
@[simp] theorem dbq_bqH_ne_bqW2 : bqH ≠ bqW2 := by decide
@[simp] theorem dbq_bqH_ne_bqH2 : bqH ≠ bqH2 := by decide
@[simp] theorem dbq_bqH_ne_bqR : bqH ≠ bqR := by decide
@[simp] theorem dbq_bqH_ne_lFl : bqH ≠ lFl := by decide
@[simp] theorem dbq_lFl_ne_bqH : lFl ≠ bqH := by decide
@[simp] theorem dbq_bqH_ne_lDh : bqH ≠ lDh := by decide
@[simp] theorem dbq_lDh_ne_bqH : lDh ≠ bqH := by decide
@[simp] theorem dbq_bqH_ne_lDt : bqH ≠ lDt := by decide
@[simp] theorem dbq_lDt_ne_bqH : lDt ≠ bqH := by decide
@[simp] theorem dbq_bqH_ne_lDg : bqH ≠ lDg := by decide
@[simp] theorem dbq_lDg_ne_bqH : lDg ≠ bqH := by decide
@[simp] theorem dbq_bqH_ne_lDi : bqH ≠ lDi := by decide
@[simp] theorem dbq_lDi_ne_bqH : lDi ≠ bqH := by decide
@[simp] theorem dbq_bqH_ne_lRp : bqH ≠ lRp := by decide
@[simp] theorem dbq_lRp_ne_bqH : lRp ≠ bqH := by decide
@[simp] theorem dbq_bqH_ne_lRn : bqH ≠ lRn := by decide
@[simp] theorem dbq_lRn_ne_bqH : lRn ≠ bqH := by decide
@[simp] theorem dbq_bqH_ne_lFle : bqH ≠ lFle := by decide
@[simp] theorem dbq_lFle_ne_bqH : lFle ≠ bqH := by decide
@[simp] theorem dbq_bqH_ne_lKb : bqH ≠ lKb := by decide
@[simp] theorem dbq_lKb_ne_bqH : lKb ≠ bqH := by decide
@[simp] theorem dbq_bqH_ne_lDir : bqH ≠ lDir := by decide
@[simp] theorem dbq_lDir_ne_bqH : lDir ≠ bqH := by decide
@[simp] theorem dbq_bqH_ne_lFln : bqH ≠ lFln := by decide
@[simp] theorem dbq_lFln_ne_bqH : lFln ≠ bqH := by decide
@[simp] theorem dbq_bqH_ne_lFll : bqH ≠ lFll := by decide
@[simp] theorem dbq_lFll_ne_bqH : lFll ≠ bqH := by decide
@[simp] theorem dbq_bqH_ne_lFls : bqH ≠ lFls := by decide
@[simp] theorem dbq_lFls_ne_bqH : lFls ≠ bqH := by decide
@[simp] theorem dbq_bqH_ne_kFu : bqH ≠ kFu := by decide
@[simp] theorem dbq_kFu_ne_bqH : kFu ≠ bqH := by decide
@[simp] theorem dbq_bqH_ne_kD : bqH ≠ kD := by decide
@[simp] theorem dbq_kD_ne_bqH : kD ≠ bqH := by decide
@[simp] theorem dbq_bqH_ne_kA : bqH ≠ kA := by decide
@[simp] theorem dbq_kA_ne_bqH : kA ≠ bqH := by decide
@[simp] theorem dbq_bqH_ne_kB : bqH ≠ kB := by decide
@[simp] theorem dbq_kB_ne_bqH : kB ≠ bqH := by decide
@[simp] theorem dbq_bqT2_ne_bqT : bqT2 ≠ bqT := by decide
@[simp] theorem dbq_bqT2_ne_bqW : bqT2 ≠ bqW := by decide
@[simp] theorem dbq_bqT2_ne_bqH : bqT2 ≠ bqH := by decide
@[simp] theorem dbq_bqT2_ne_bqW2 : bqT2 ≠ bqW2 := by decide
@[simp] theorem dbq_bqT2_ne_bqH2 : bqT2 ≠ bqH2 := by decide
@[simp] theorem dbq_bqT2_ne_bqR : bqT2 ≠ bqR := by decide
@[simp] theorem dbq_bqT2_ne_lFl : bqT2 ≠ lFl := by decide
@[simp] theorem dbq_lFl_ne_bqT2 : lFl ≠ bqT2 := by decide
@[simp] theorem dbq_bqT2_ne_lDh : bqT2 ≠ lDh := by decide
@[simp] theorem dbq_lDh_ne_bqT2 : lDh ≠ bqT2 := by decide
@[simp] theorem dbq_bqT2_ne_lDt : bqT2 ≠ lDt := by decide
@[simp] theorem dbq_lDt_ne_bqT2 : lDt ≠ bqT2 := by decide
@[simp] theorem dbq_bqT2_ne_lDg : bqT2 ≠ lDg := by decide
@[simp] theorem dbq_lDg_ne_bqT2 : lDg ≠ bqT2 := by decide
@[simp] theorem dbq_bqT2_ne_lDi : bqT2 ≠ lDi := by decide
@[simp] theorem dbq_lDi_ne_bqT2 : lDi ≠ bqT2 := by decide
@[simp] theorem dbq_bqT2_ne_lRp : bqT2 ≠ lRp := by decide
@[simp] theorem dbq_lRp_ne_bqT2 : lRp ≠ bqT2 := by decide
@[simp] theorem dbq_bqT2_ne_lRn : bqT2 ≠ lRn := by decide
@[simp] theorem dbq_lRn_ne_bqT2 : lRn ≠ bqT2 := by decide
@[simp] theorem dbq_bqT2_ne_lFle : bqT2 ≠ lFle := by decide
@[simp] theorem dbq_lFle_ne_bqT2 : lFle ≠ bqT2 := by decide
@[simp] theorem dbq_bqT2_ne_lKb : bqT2 ≠ lKb := by decide
@[simp] theorem dbq_lKb_ne_bqT2 : lKb ≠ bqT2 := by decide
@[simp] theorem dbq_bqT2_ne_lDir : bqT2 ≠ lDir := by decide
@[simp] theorem dbq_lDir_ne_bqT2 : lDir ≠ bqT2 := by decide
@[simp] theorem dbq_bqT2_ne_lFln : bqT2 ≠ lFln := by decide
@[simp] theorem dbq_lFln_ne_bqT2 : lFln ≠ bqT2 := by decide
@[simp] theorem dbq_bqT2_ne_lFll : bqT2 ≠ lFll := by decide
@[simp] theorem dbq_lFll_ne_bqT2 : lFll ≠ bqT2 := by decide
@[simp] theorem dbq_bqT2_ne_lFls : bqT2 ≠ lFls := by decide
@[simp] theorem dbq_lFls_ne_bqT2 : lFls ≠ bqT2 := by decide
@[simp] theorem dbq_bqT2_ne_kFu : bqT2 ≠ kFu := by decide
@[simp] theorem dbq_kFu_ne_bqT2 : kFu ≠ bqT2 := by decide
@[simp] theorem dbq_bqT2_ne_kD : bqT2 ≠ kD := by decide
@[simp] theorem dbq_kD_ne_bqT2 : kD ≠ bqT2 := by decide
@[simp] theorem dbq_bqT2_ne_kA : bqT2 ≠ kA := by decide
@[simp] theorem dbq_kA_ne_bqT2 : kA ≠ bqT2 := by decide
@[simp] theorem dbq_bqT2_ne_kB : bqT2 ≠ kB := by decide
@[simp] theorem dbq_kB_ne_bqT2 : kB ≠ bqT2 := by decide
@[simp] theorem dbq_bqW2_ne_bqT : bqW2 ≠ bqT := by decide
@[simp] theorem dbq_bqW2_ne_bqW : bqW2 ≠ bqW := by decide
@[simp] theorem dbq_bqW2_ne_bqH : bqW2 ≠ bqH := by decide
@[simp] theorem dbq_bqW2_ne_bqT2 : bqW2 ≠ bqT2 := by decide
@[simp] theorem dbq_bqW2_ne_bqH2 : bqW2 ≠ bqH2 := by decide
@[simp] theorem dbq_bqW2_ne_bqR : bqW2 ≠ bqR := by decide
@[simp] theorem dbq_bqW2_ne_lFl : bqW2 ≠ lFl := by decide
@[simp] theorem dbq_lFl_ne_bqW2 : lFl ≠ bqW2 := by decide
@[simp] theorem dbq_bqW2_ne_lDh : bqW2 ≠ lDh := by decide
@[simp] theorem dbq_lDh_ne_bqW2 : lDh ≠ bqW2 := by decide
@[simp] theorem dbq_bqW2_ne_lDt : bqW2 ≠ lDt := by decide
@[simp] theorem dbq_lDt_ne_bqW2 : lDt ≠ bqW2 := by decide
@[simp] theorem dbq_bqW2_ne_lDg : bqW2 ≠ lDg := by decide
@[simp] theorem dbq_lDg_ne_bqW2 : lDg ≠ bqW2 := by decide
@[simp] theorem dbq_bqW2_ne_lDi : bqW2 ≠ lDi := by decide
@[simp] theorem dbq_lDi_ne_bqW2 : lDi ≠ bqW2 := by decide
@[simp] theorem dbq_bqW2_ne_lRp : bqW2 ≠ lRp := by decide
@[simp] theorem dbq_lRp_ne_bqW2 : lRp ≠ bqW2 := by decide
@[simp] theorem dbq_bqW2_ne_lRn : bqW2 ≠ lRn := by decide
@[simp] theorem dbq_lRn_ne_bqW2 : lRn ≠ bqW2 := by decide
@[simp] theorem dbq_bqW2_ne_lFle : bqW2 ≠ lFle := by decide
@[simp] theorem dbq_lFle_ne_bqW2 : lFle ≠ bqW2 := by decide
@[simp] theorem dbq_bqW2_ne_lKb : bqW2 ≠ lKb := by decide
@[simp] theorem dbq_lKb_ne_bqW2 : lKb ≠ bqW2 := by decide
@[simp] theorem dbq_bqW2_ne_lDir : bqW2 ≠ lDir := by decide
@[simp] theorem dbq_lDir_ne_bqW2 : lDir ≠ bqW2 := by decide
@[simp] theorem dbq_bqW2_ne_lFln : bqW2 ≠ lFln := by decide
@[simp] theorem dbq_lFln_ne_bqW2 : lFln ≠ bqW2 := by decide
@[simp] theorem dbq_bqW2_ne_lFll : bqW2 ≠ lFll := by decide
@[simp] theorem dbq_lFll_ne_bqW2 : lFll ≠ bqW2 := by decide
@[simp] theorem dbq_bqW2_ne_lFls : bqW2 ≠ lFls := by decide
@[simp] theorem dbq_lFls_ne_bqW2 : lFls ≠ bqW2 := by decide
@[simp] theorem dbq_bqW2_ne_kFu : bqW2 ≠ kFu := by decide
@[simp] theorem dbq_kFu_ne_bqW2 : kFu ≠ bqW2 := by decide
@[simp] theorem dbq_bqW2_ne_kD : bqW2 ≠ kD := by decide
@[simp] theorem dbq_kD_ne_bqW2 : kD ≠ bqW2 := by decide
@[simp] theorem dbq_bqW2_ne_kA : bqW2 ≠ kA := by decide
@[simp] theorem dbq_kA_ne_bqW2 : kA ≠ bqW2 := by decide
@[simp] theorem dbq_bqW2_ne_kB : bqW2 ≠ kB := by decide
@[simp] theorem dbq_kB_ne_bqW2 : kB ≠ bqW2 := by decide
@[simp] theorem dbq_bqH2_ne_bqT : bqH2 ≠ bqT := by decide
@[simp] theorem dbq_bqH2_ne_bqW : bqH2 ≠ bqW := by decide
@[simp] theorem dbq_bqH2_ne_bqH : bqH2 ≠ bqH := by decide
@[simp] theorem dbq_bqH2_ne_bqT2 : bqH2 ≠ bqT2 := by decide
@[simp] theorem dbq_bqH2_ne_bqW2 : bqH2 ≠ bqW2 := by decide
@[simp] theorem dbq_bqH2_ne_bqR : bqH2 ≠ bqR := by decide
@[simp] theorem dbq_bqH2_ne_lFl : bqH2 ≠ lFl := by decide
@[simp] theorem dbq_lFl_ne_bqH2 : lFl ≠ bqH2 := by decide
@[simp] theorem dbq_bqH2_ne_lDh : bqH2 ≠ lDh := by decide
@[simp] theorem dbq_lDh_ne_bqH2 : lDh ≠ bqH2 := by decide
@[simp] theorem dbq_bqH2_ne_lDt : bqH2 ≠ lDt := by decide
@[simp] theorem dbq_lDt_ne_bqH2 : lDt ≠ bqH2 := by decide
@[simp] theorem dbq_bqH2_ne_lDg : bqH2 ≠ lDg := by decide
@[simp] theorem dbq_lDg_ne_bqH2 : lDg ≠ bqH2 := by decide
@[simp] theorem dbq_bqH2_ne_lDi : bqH2 ≠ lDi := by decide
@[simp] theorem dbq_lDi_ne_bqH2 : lDi ≠ bqH2 := by decide
@[simp] theorem dbq_bqH2_ne_lRp : bqH2 ≠ lRp := by decide
@[simp] theorem dbq_lRp_ne_bqH2 : lRp ≠ bqH2 := by decide
@[simp] theorem dbq_bqH2_ne_lRn : bqH2 ≠ lRn := by decide
@[simp] theorem dbq_lRn_ne_bqH2 : lRn ≠ bqH2 := by decide
@[simp] theorem dbq_bqH2_ne_lFle : bqH2 ≠ lFle := by decide
@[simp] theorem dbq_lFle_ne_bqH2 : lFle ≠ bqH2 := by decide
@[simp] theorem dbq_bqH2_ne_lKb : bqH2 ≠ lKb := by decide
@[simp] theorem dbq_lKb_ne_bqH2 : lKb ≠ bqH2 := by decide
@[simp] theorem dbq_bqH2_ne_lDir : bqH2 ≠ lDir := by decide
@[simp] theorem dbq_lDir_ne_bqH2 : lDir ≠ bqH2 := by decide
@[simp] theorem dbq_bqH2_ne_lFln : bqH2 ≠ lFln := by decide
@[simp] theorem dbq_lFln_ne_bqH2 : lFln ≠ bqH2 := by decide
@[simp] theorem dbq_bqH2_ne_lFll : bqH2 ≠ lFll := by decide
@[simp] theorem dbq_lFll_ne_bqH2 : lFll ≠ bqH2 := by decide
@[simp] theorem dbq_bqH2_ne_lFls : bqH2 ≠ lFls := by decide
@[simp] theorem dbq_lFls_ne_bqH2 : lFls ≠ bqH2 := by decide
@[simp] theorem dbq_bqH2_ne_kFu : bqH2 ≠ kFu := by decide
@[simp] theorem dbq_kFu_ne_bqH2 : kFu ≠ bqH2 := by decide
@[simp] theorem dbq_bqH2_ne_kD : bqH2 ≠ kD := by decide
@[simp] theorem dbq_kD_ne_bqH2 : kD ≠ bqH2 := by decide
@[simp] theorem dbq_bqH2_ne_kA : bqH2 ≠ kA := by decide
@[simp] theorem dbq_kA_ne_bqH2 : kA ≠ bqH2 := by decide
@[simp] theorem dbq_bqH2_ne_kB : bqH2 ≠ kB := by decide
@[simp] theorem dbq_kB_ne_bqH2 : kB ≠ bqH2 := by decide
@[simp] theorem dbq_bqR_ne_bqT : bqR ≠ bqT := by decide
@[simp] theorem dbq_bqR_ne_bqW : bqR ≠ bqW := by decide
@[simp] theorem dbq_bqR_ne_bqH : bqR ≠ bqH := by decide
@[simp] theorem dbq_bqR_ne_bqT2 : bqR ≠ bqT2 := by decide
@[simp] theorem dbq_bqR_ne_bqW2 : bqR ≠ bqW2 := by decide
@[simp] theorem dbq_bqR_ne_bqH2 : bqR ≠ bqH2 := by decide
@[simp] theorem dbq_bqR_ne_lFl : bqR ≠ lFl := by decide
@[simp] theorem dbq_lFl_ne_bqR : lFl ≠ bqR := by decide
@[simp] theorem dbq_bqR_ne_lDh : bqR ≠ lDh := by decide
@[simp] theorem dbq_lDh_ne_bqR : lDh ≠ bqR := by decide
@[simp] theorem dbq_bqR_ne_lDt : bqR ≠ lDt := by decide
@[simp] theorem dbq_lDt_ne_bqR : lDt ≠ bqR := by decide
@[simp] theorem dbq_bqR_ne_lDg : bqR ≠ lDg := by decide
@[simp] theorem dbq_lDg_ne_bqR : lDg ≠ bqR := by decide
@[simp] theorem dbq_bqR_ne_lDi : bqR ≠ lDi := by decide
@[simp] theorem dbq_lDi_ne_bqR : lDi ≠ bqR := by decide
@[simp] theorem dbq_bqR_ne_lRp : bqR ≠ lRp := by decide
@[simp] theorem dbq_lRp_ne_bqR : lRp ≠ bqR := by decide
@[simp] theorem dbq_bqR_ne_lRn : bqR ≠ lRn := by decide
@[simp] theorem dbq_lRn_ne_bqR : lRn ≠ bqR := by decide
@[simp] theorem dbq_bqR_ne_lFle : bqR ≠ lFle := by decide
@[simp] theorem dbq_lFle_ne_bqR : lFle ≠ bqR := by decide
@[simp] theorem dbq_bqR_ne_lKb : bqR ≠ lKb := by decide
@[simp] theorem dbq_lKb_ne_bqR : lKb ≠ bqR := by decide
@[simp] theorem dbq_bqR_ne_lDir : bqR ≠ lDir := by decide
@[simp] theorem dbq_lDir_ne_bqR : lDir ≠ bqR := by decide
@[simp] theorem dbq_bqR_ne_lFln : bqR ≠ lFln := by decide
@[simp] theorem dbq_lFln_ne_bqR : lFln ≠ bqR := by decide
@[simp] theorem dbq_bqR_ne_lFll : bqR ≠ lFll := by decide
@[simp] theorem dbq_lFll_ne_bqR : lFll ≠ bqR := by decide
@[simp] theorem dbq_bqR_ne_lFls : bqR ≠ lFls := by decide
@[simp] theorem dbq_lFls_ne_bqR : lFls ≠ bqR := by decide
@[simp] theorem dbq_bqR_ne_kFu : bqR ≠ kFu := by decide
@[simp] theorem dbq_kFu_ne_bqR : kFu ≠ bqR := by decide
@[simp] theorem dbq_bqR_ne_kD : bqR ≠ kD := by decide
@[simp] theorem dbq_kD_ne_bqR : kD ≠ bqR := by decide
@[simp] theorem dbq_bqR_ne_kA : bqR ≠ kA := by decide
@[simp] theorem dbq_kA_ne_bqR : kA ≠ bqR := by decide
@[simp] theorem dbq_bqR_ne_kB : bqR ≠ kB := by decide
@[simp] theorem dbq_kB_ne_bqR : kB ≠ bqR := by decide

def bqLocals : List MlS := [bqT, bqW, bqH, bqT2, bqW2, bqH2, bqR]
/-- `defeqBody`'s Pancake body (the knot's `fDB`, parameters `dParams`). -/
def bqBody (C : Ctx) : ProgHOL 64 := prologue bqLocals (.ite (.cmp .equal (vv kA) (vv kB)) (.return (.const 1)) (.seq (.call (some (some (.local, bqT), none)) fCf [(vv kA), (vv kB)]) (.ite (.cmp .notEqual (vv bqT) (.const 0)) (.seq (.call (some (some (.local, bqW), none)) fW [(vv kFu), (vv kD), (vv kA)]) (.seq (.call (some (some (.local, bqH), none)) fCh [(.op .sub [(vv bqT), (.const 1)]), (vv bqW)]) (.ite (.cmp .equal (vv bqH) (.const 2)) (.seq (.call (some (some (.local, bqR), none)) fYz [(vv kFu), (vv kD), (vv bqW), (vv kB)]) (.return (vv bqR))) (.ite (.cmp .equal (vv bqH) (.const 1)) (.return (.const 0)) (.seq (.call (some (some (.local, bqR), none)) fYz [(vv kFu), (vv kD), (vv kA), (vv kB)]) (.return (vv bqR))))))) (.seq (.call (some (some (.local, bqT2), none)) fCf [(vv kB), (vv kA)]) (.ite (.cmp .notEqual (vv bqT2) (.const 0)) (.seq (.call (some (some (.local, bqW2), none)) fW [(vv kFu), (vv kD), (vv kB)]) (.seq (.call (some (some (.local, bqH2), none)) fCh [(.op .sub [(vv bqT2), (.const 1)]), (vv bqW2)]) (.ite (.cmp .equal (vv bqH2) (.const 2)) (.seq (.call (some (some (.local, bqR), none)) fYz [(vv kFu), (vv kD), (vv kA), (vv bqW2)]) (.return (vv bqR))) (.ite (.cmp .equal (vv bqH2) (.const 1)) (.return (.const 0)) (.seq (.call (some (some (.local, bqR), none)) fYz [(vv kFu), (vv kD), (vv kA), (vv kB)]) (.return (vv bqR))))))) (.seq (.call (some (some (.local, bqR), none)) fYz [(vv kFu), (vv kD), (vv kA), (vv kB)]) (.return (vv bqR))))))))

structure BqCodes (C : Ctx) : Prop where
  cf : C.code.lookup fCf = some (cfParams.map (fun p => (p, ShapeHOL.one)), cfBody C.side, .one)
  w : C.code.lookup fW = some (kParams.map (fun p => (p, ShapeHOL.one)), whnfE C fWB, .one)
  ch : C.code.lookup fCh = some (chParams.map (fun p => (p, ShapeHOL.one)), chBody C, .one)
  yz : C.code.lookup fYz = some (yzParams.map (fun p => (p, ShapeHOL.one)), yzBody C.side C, .one)

section
variable {σ : Type}

theorem idxW_add_one_ne' {k : IdxKind} (v : Idx k) : Enc.idxW v + 1 ≠ 0 := by
  intro h
  have := congrArg BitVec.toNat h
  have hl : (Enc.idxW v).toNat < 2 ^ 32 := by simp [Enc.idxW]; exact v.word.toNat_lt
  simp [BitVec.toNat_add] at this; omega

theorem bq_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) (hc : BqCodes C) (Q : AState → Prop) (d : Nat)
    (hQcf : ∀ s1 o e r s2, Q s1 → ctorTargetFor C.fe C.side o e s1 = .ok (r, s2) → Q s2)
    (hQw : ∀ s1 e r s2, Q s1 → (knot mode C n).whnf d e s1 = .ok (r, s2) → Q s2)
    (hQch : ∀ s1 c w r s2, Q s1 → ctorHeadAgainst C.fe c w s1 = .ok (r, s2) → Q s2)
    (hQyz : ∀ s1 a b r s2, Q s1 → defeqLazy mode C.side (knot mode C n) C.fe d a b s1 = .ok (r, s2) → Q s2)
    (hCF : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ o e, SpecR (σ := σ) (Pre (ctxH C H) s1 (cfParams.zip [Enc.idxW o, Enc.idxW e])) (cfBody C.side) s1
      (ctorTargetFor C.fe C.side o e) (PostON (ctxH C H)))
    (hW : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ e, Callee (σ := σ) (ctxH C H) kParams [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e]
      (whnfE C fWB) s1 ((knot mode C n).whnf d e) (PostK (ctxH C H)))
    (hCH : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ c w, SpecR (σ := σ) (Pre (ctxH C H) s1 (chParams.zip [Enc.idxW c, Enc.idxW w])) (chBody C) s1
      (ctorHeadAgainst C.fe c w) (PostOBH (ctxH C H)))
    (hYZ : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ a b, SpecR (σ := σ) (Pre (ctxH C H) s1 (yzParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d,
      Enc.idxW a, Enc.idxW b])) (yzBody C.side C) s1 (defeqLazy mode C.side (knot mode C n) C.fe d a b)
      (PostB (ctxH C H))) :
    ∀ (H : List (BitVec 64)) (s : AState) (a b : EIdx), C.H <+: H → Q s →
      SpecR (σ := σ) (Pre (ctxH C H) s (dParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b]))
        (bqBody C) s (defeqBody mode C.side (knot mode C n) C.fe d a b) (PostB (ctxH C H)) := by
  intro H s a b hpH hq
  refine specR_prologue (postB_locals _) (Knot.params_none _ bqLocals dParams _ (by decide) (by decide)) ?_
  unfold defeqBody
  by_cases hab : a = b
  · subst hab
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, dParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [beq_self_eq_true, ↓reduceIte]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  have hne : Enc.idxW a ≠ Enc.idxW b := fun e => hab (Enc.idxW_inj e)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, dParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun h => absurd rfl h) (fun _ => ?_)
  simp only [show (a == b) = false by simpa using hab, Bool.false_eq_true, ↓reduceIte]
  refine specR_callNIH (C := ctxH C H) bqT fCf cfParams [vv kA, vv kB] (cfBody C.side)
    [Enc.idxW a, Enc.idxW b] (by decide) rfl (by decide) hc.cf
    ⟨by simp +decide [Env.get, dParams, ctxEnv], by simp +decide [Env.get, dParams, ctxEnv], trivial⟩
    (fun r_ w s' st => ctorTargetFor C.fe C.side a b s = .ok (r_, s') ∧ PostON (ctxH C H) r_ w s' st) (fun r_ w s' H' => w = optWG Enc.idxW r_ ∧ ctorTargetFor C.fe C.side a b s = .ok (r_, s'))
    (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu cfParams _ rfl hlk) (hCF H s hpH hq a b)))
    (fun oc w1 s1 H1 hp1 ⟨hw1, hrun1⟩ => ?_)
  have hq1 := hQcf s a b oc s1 hq hrun1
  have hpa1 : C.H <+: H1 := hpH.trans hp1
  have hb1 : H <+: H1 := (List.prefix_refl _).trans hp1
  subst hw1
  rcases oc with _ | c
  swap
  · refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne' c) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    refine specR_callNIH (C := ctxH C H1) bqW fW kParams [vv kFu, vv kD, vv kA] (whnfE C fWB)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a] (by decide) rfl (by decide) hc.w
      ⟨by simp +decide [Env.get, dParams, ctxEnv], by simp +decide [Env.get, dParams, ctxEnv], by simp +decide [Env.get, dParams, ctxEnv], trivial⟩
      (fun r_ w s' st => (knot mode C n).whnf d a s1 = .ok (r_, s') ∧ PostK (ctxH C H1) r_ w s' st) (fun r_ w s' H' => w = Enc.idxW r_ ∧ (knot mode C n).whnf d a s1 = .ok (r_, s'))
      (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (hW H1 s1 hpa1 hq1 a u hu (fun i hi _ => hlk i (by omega))))
      (fun wv w2 s2 H2 hp2 ⟨hw2, hrun2⟩ => ?_)
    have hq2 := hQw s1 a wv s2 hq1 hrun2
    have hpa2 : C.H <+: H2 := hpa1.trans hp2
    have hb2 : H <+: H2 := hb1.trans hp2
    subst hw2
    refine specR_callNIH (C := ctxH C H2) bqH fCh chParams [.op .sub [vv bqT, .const 1], vv bqW] (chBody C)
      [Enc.idxW c, Enc.idxW wv] (by decide) rfl (by decide) hc.ch
      ⟨by simp [sev, optWG]; exact BitVec.add_sub_cancel _ _, by simp, trivial⟩
      (fun r_ w s' st => ctorHeadAgainst C.fe c wv s2 = .ok (r_, s') ∧ PostOBH (ctxH C H2) r_ w s' st) (fun r_ w s' H' => w = LLeq.obW r_ ∧ ctorHeadAgainst C.fe c wv s2 = .ok (r_, s'))
      (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu chParams _ rfl hlk) (hCH H2 s2 hpa2 hq2 c wv)))
      (fun oh w3 s3 H3 hp3 ⟨hw3, hrun3⟩ => ?_)
    have hq3 := hQch s2 c wv oh s3 hq2 hrun3
    have hpa3 : C.H <+: H3 := hpa2.trans hp3
    have hb3 : H <+: H3 := hb2.trans hp3
    subst hw3
    rcases oh with _ | ⟨_ | _⟩
    · refine specR_ifI _ 0 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      try dsimp only
      refine specR_congr (m' := defeqLazy mode C.side (knot mode C n) C.fe d a b >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H3) bqR fYz yzParams [vv kFu, vv kD, vv kA, vv kB] (yzBody C.side C)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (by decide) rfl (by decide) hc.yz
        ⟨by simp +decide [Env.get, dParams, ctxEnv], by simp +decide [Env.get, dParams, ctxEnv], by simp +decide [Env.get, dParams, ctxEnv], by simp +decide [Env.get, dParams, ctxEnv], trivial⟩
        (fun r_ w s' st => defeqLazy mode C.side (knot mode C n) C.fe d a b s3 = .ok (r_, s') ∧ PostB (ctxH C H3) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ defeqLazy mode C.side (knot mode C n) C.fe d a b s3 = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu yzParams _ rfl hlk) (hYZ H3 s3 hpa3 hq3 a b)))
        (fun rr w4 s4 H4 hp4 ⟨hw4, hrun4⟩ => ?_)
      have hq4 := hQyz s3 a b rr s4 hq3 hrun4
      have hpa4 : C.H <+: H4 := hpa3.trans hp4
      have hb4 : H <+: H4 := hb3.trans hp4
      subst hw4
      exact specR_returnI _ (boolW rr) (by simp) (fun t ht => ⟨H4, hb4, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    · refine specR_ifI _ 0 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      try dsimp only
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H3, hb3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine specR_ifI _ 1 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    refine specR_congr (m' := defeqLazy mode C.side (knot mode C n) C.fe d wv b >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H3) bqR fYz yzParams [vv kFu, vv kD, vv bqW, vv kB] (yzBody C.side C)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW wv, Enc.idxW b] (by decide) rfl (by decide) hc.yz
      ⟨by simp +decide [Env.get, dParams, ctxEnv], by simp +decide [Env.get, dParams, ctxEnv], by simp, by simp +decide [Env.get, dParams, ctxEnv], trivial⟩
      (fun r_ w s' st => defeqLazy mode C.side (knot mode C n) C.fe d wv b s3 = .ok (r_, s') ∧ PostB (ctxH C H3) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ defeqLazy mode C.side (knot mode C n) C.fe d wv b s3 = .ok (r_, s'))
      (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu yzParams _ rfl hlk) (hYZ H3 s3 hpa3 hq3 wv b)))
      (fun rr w5 s5 H5 hp5 ⟨hw5, hrun5⟩ => ?_)
    have hq5 := hQyz s3 wv b rr s5 hq3 hrun5
    have hpa5 : C.H <+: H5 := hpa3.trans hp5
    have hb5 : H <+: H5 := hb3.trans hp5
    subst hw5
    exact specR_returnI _ (boolW rr) (by simp) (fun t ht => ⟨H5, hb5, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
  try dsimp only
  refine specR_callNIH (C := ctxH C H1) bqT2 fCf cfParams [vv kB, vv kA] (cfBody C.side)
    [Enc.idxW b, Enc.idxW a] (by decide) rfl (by decide) hc.cf
    ⟨by simp +decide [Env.get, dParams, ctxEnv], by simp +decide [Env.get, dParams, ctxEnv], trivial⟩
    (fun r_ w s' st => ctorTargetFor C.fe C.side b a s1 = .ok (r_, s') ∧ PostON (ctxH C H1) r_ w s' st) (fun r_ w s' H' => w = optWG Enc.idxW r_ ∧ ctorTargetFor C.fe C.side b a s1 = .ok (r_, s'))
    (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu cfParams _ rfl hlk) (hCF H1 s1 hpa1 hq1 b a)))
    (fun oc w6 s6 H6 hp6 ⟨hw6, hrun6⟩ => ?_)
  have hq6 := hQcf s1 b a oc s6 hq1 hrun6
  have hpa6 : C.H <+: H6 := hpa1.trans hp6
  have hb6 : H <+: H6 := hb1.trans hp6
  subst hw6
  rcases oc with _ | c
  swap
  · refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne' c) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    refine specR_callNIH (C := ctxH C H6) bqW2 fW kParams [vv kFu, vv kD, vv kB] (whnfE C fWB)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW b] (by decide) rfl (by decide) hc.w
      ⟨by simp +decide [Env.get, dParams, ctxEnv], by simp +decide [Env.get, dParams, ctxEnv], by simp +decide [Env.get, dParams, ctxEnv], trivial⟩
      (fun r_ w s' st => (knot mode C n).whnf d b s6 = .ok (r_, s') ∧ PostK (ctxH C H6) r_ w s' st) (fun r_ w s' H' => w = Enc.idxW r_ ∧ (knot mode C n).whnf d b s6 = .ok (r_, s'))
      (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (hW H6 s6 hpa6 hq6 b u hu (fun i hi _ => hlk i (by omega))))
      (fun wv w7 s7 H7 hp7 ⟨hw7, hrun7⟩ => ?_)
    have hq7 := hQw s6 b wv s7 hq6 hrun7
    have hpa7 : C.H <+: H7 := hpa6.trans hp7
    have hb7 : H <+: H7 := hb6.trans hp7
    subst hw7
    refine specR_callNIH (C := ctxH C H7) bqH2 fCh chParams [.op .sub [vv bqT2, .const 1], vv bqW2] (chBody C)
      [Enc.idxW c, Enc.idxW wv] (by decide) rfl (by decide) hc.ch
      ⟨by simp [sev, optWG]; exact BitVec.add_sub_cancel _ _, by simp, trivial⟩
      (fun r_ w s' st => ctorHeadAgainst C.fe c wv s7 = .ok (r_, s') ∧ PostOBH (ctxH C H7) r_ w s' st) (fun r_ w s' H' => w = LLeq.obW r_ ∧ ctorHeadAgainst C.fe c wv s7 = .ok (r_, s'))
      (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu chParams _ rfl hlk) (hCH H7 s7 hpa7 hq7 c wv)))
      (fun oh w8 s8 H8 hp8 ⟨hw8, hrun8⟩ => ?_)
    have hq8 := hQch s7 c wv oh s8 hq7 hrun8
    have hpa8 : C.H <+: H8 := hpa7.trans hp8
    have hb8 : H <+: H8 := hb7.trans hp8
    subst hw8
    rcases oh with _ | ⟨_ | _⟩
    · refine specR_ifI _ 0 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      try dsimp only
      refine specR_congr (m' := defeqLazy mode C.side (knot mode C n) C.fe d a b >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H8) bqR fYz yzParams [vv kFu, vv kD, vv kA, vv kB] (yzBody C.side C)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (by decide) rfl (by decide) hc.yz
        ⟨by simp +decide [Env.get, dParams, ctxEnv], by simp +decide [Env.get, dParams, ctxEnv], by simp +decide [Env.get, dParams, ctxEnv], by simp +decide [Env.get, dParams, ctxEnv], trivial⟩
        (fun r_ w s' st => defeqLazy mode C.side (knot mode C n) C.fe d a b s8 = .ok (r_, s') ∧ PostB (ctxH C H8) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ defeqLazy mode C.side (knot mode C n) C.fe d a b s8 = .ok (r_, s'))
        (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu yzParams _ rfl hlk) (hYZ H8 s8 hpa8 hq8 a b)))
        (fun rr w9 s9 H9 hp9 ⟨hw9, hrun9⟩ => ?_)
      have hq9 := hQyz s8 a b rr s9 hq8 hrun9
      have hpa9 : C.H <+: H9 := hpa8.trans hp9
      have hb9 : H <+: H9 := hb8.trans hp9
      subst hw9
      exact specR_returnI _ (boolW rr) (by simp) (fun t ht => ⟨H9, hb9, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    · refine specR_ifI _ 0 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      try dsimp only
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H8, hb8, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine specR_ifI _ 1 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    try dsimp only
    refine specR_congr (m' := defeqLazy mode C.side (knot mode C n) C.fe d a wv >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H8) bqR fYz yzParams [vv kFu, vv kD, vv kA, vv bqW2] (yzBody C.side C)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW wv] (by decide) rfl (by decide) hc.yz
      ⟨by simp +decide [Env.get, dParams, ctxEnv], by simp +decide [Env.get, dParams, ctxEnv], by simp +decide [Env.get, dParams, ctxEnv], by simp, trivial⟩
      (fun r_ w s' st => defeqLazy mode C.side (knot mode C n) C.fe d a wv s8 = .ok (r_, s') ∧ PostB (ctxH C H8) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ defeqLazy mode C.side (knot mode C n) C.fe d a wv s8 = .ok (r_, s'))
      (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu yzParams _ rfl hlk) (hYZ H8 s8 hpa8 hq8 a wv)))
      (fun rr w10 s10 H10 hp10 ⟨hw10, hrun10⟩ => ?_)
    have hq10 := hQyz s8 a wv rr s10 hq8 hrun10
    have hpa10 : C.H <+: H10 := hpa8.trans hp10
    have hb10 : H <+: H10 := hb8.trans hp10
    subst hw10
    exact specR_returnI _ (boolW rr) (by simp) (fun t ht => ⟨H10, hb10, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
  try dsimp only
  refine specR_congr (m' := defeqLazy mode C.side (knot mode C n) C.fe d a b >>= fun r => pure r) (by simp) ?_
  refine specR_callNIH (C := ctxH C H6) bqR fYz yzParams [vv kFu, vv kD, vv kA, vv kB] (yzBody C.side C)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (by decide) rfl (by decide) hc.yz
    ⟨by simp +decide [Env.get, dParams, ctxEnv], by simp +decide [Env.get, dParams, ctxEnv], by simp +decide [Env.get, dParams, ctxEnv], by simp +decide [Env.get, dParams, ctxEnv], trivial⟩
    (fun r_ w s' st => defeqLazy mode C.side (knot mode C n) C.fe d a b s6 = .ok (r_, s') ∧ PostB (ctxH C H6) r_ w s' st) (fun r_ w s' H' => w = boolW r_ ∧ defeqLazy mode C.side (knot mode C n) C.fe d a b s6 = .ok (r_, s'))
    (fun r_ w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hw, hr⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu yzParams _ rfl hlk) (hYZ H6 s6 hpa6 hq6 a b)))
    (fun rr w11 s11 H11 hp11 ⟨hw11, hrun11⟩ => ?_)
  have hq11 := hQyz s6 a b rr s11 hq6 hrun11
  have hpa11 : C.H <+: H11 := hpa6.trans hp11
  have hb11 : H <+: H11 := hb6.trans hp11
  subst hw11
  exact specR_returnI _ (boolW rr) (by simp) (fun t ht => ⟨H11, hb11, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
