import ConPanqueque.T.Core.ProjGuardSort
import ConPanqueque.T.Core.ProjGuardRowsF
import ConPanqueque.T.Floor
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `checkProjGuard`

The structure must be an inductive (its record's tag `3`); its guard sort (`projGuardSort`) asks nothing, or the
rows (`projGuardRows`) are checked against it (`checkGuardRows`). The three are callees here, stated at the
states of a family `Q` closed under their runs; a twin failure is a halt.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def gdT := ofString "gdn_t"
def gdI := ofString "gdn_i"
def gdU := ofString "gdn_u"
def gdN := ofString "gdn_n"
def gdP := ofString "gdn_p"
def gdQ := ofString "gdn_q"
def gdK := ofString "gdn_k"
def gdG := ofString "gdn_g"
def gdR := ofString "gdn_r"
def gdL := ofString "gdn_l"
def gdX := ofString "gdn_x"
def fGs := ofString "projGuardSort"
def fGd := ofString "checkProjGuard"

@[simp] theorem gd_gdT_ne_gdI : gdT ≠ gdI := by decide
@[simp] theorem gd_gdT_ne_gdU : gdT ≠ gdU := by decide
@[simp] theorem gd_gdT_ne_gdN : gdT ≠ gdN := by decide
@[simp] theorem gd_gdT_ne_gdP : gdT ≠ gdP := by decide
@[simp] theorem gd_gdT_ne_gdQ : gdT ≠ gdQ := by decide
@[simp] theorem gd_gdT_ne_gdK : gdT ≠ gdK := by decide
@[simp] theorem gd_gdT_ne_gdG : gdT ≠ gdG := by decide
@[simp] theorem gd_gdT_ne_gdR : gdT ≠ gdR := by decide
@[simp] theorem gd_gdT_ne_gdL : gdT ≠ gdL := by decide
@[simp] theorem gd_gdT_ne_gdX : gdT ≠ gdX := by decide
@[simp] theorem gd_gdT_ne_kFu : gdT ≠ kFu := by decide
@[simp] theorem gd_kFu_ne_gdT : kFu ≠ gdT := by decide
@[simp] theorem gd_gdT_ne_lFl : gdT ≠ lFl := by decide
@[simp] theorem gd_lFl_ne_gdT : lFl ≠ gdT := by decide
@[simp] theorem gd_gdT_ne_lDh : gdT ≠ lDh := by decide
@[simp] theorem gd_lDh_ne_gdT : lDh ≠ gdT := by decide
@[simp] theorem gd_gdT_ne_lDt : gdT ≠ lDt := by decide
@[simp] theorem gd_lDt_ne_gdT : lDt ≠ gdT := by decide
@[simp] theorem gd_gdT_ne_lDg : gdT ≠ lDg := by decide
@[simp] theorem gd_lDg_ne_gdT : lDg ≠ gdT := by decide
@[simp] theorem gd_gdT_ne_lDi : gdT ≠ lDi := by decide
@[simp] theorem gd_lDi_ne_gdT : lDi ≠ gdT := by decide
@[simp] theorem gd_gdT_ne_lRp : gdT ≠ lRp := by decide
@[simp] theorem gd_lRp_ne_gdT : lRp ≠ gdT := by decide
@[simp] theorem gd_gdT_ne_lRn : gdT ≠ lRn := by decide
@[simp] theorem gd_lRn_ne_gdT : lRn ≠ gdT := by decide
@[simp] theorem gd_gdT_ne_lDir : gdT ≠ lDir := by decide
@[simp] theorem gd_lDir_ne_gdT : lDir ≠ gdT := by decide
@[simp] theorem gd_gdT_ne_lFle : gdT ≠ lFle := by decide
@[simp] theorem gd_lFle_ne_gdT : lFle ≠ gdT := by decide
@[simp] theorem gd_gdT_ne_lKb : gdT ≠ lKb := by decide
@[simp] theorem gd_lKb_ne_gdT : lKb ≠ gdT := by decide
@[simp] theorem gd_gdI_ne_gdT : gdI ≠ gdT := by decide
@[simp] theorem gd_gdI_ne_gdU : gdI ≠ gdU := by decide
@[simp] theorem gd_gdI_ne_gdN : gdI ≠ gdN := by decide
@[simp] theorem gd_gdI_ne_gdP : gdI ≠ gdP := by decide
@[simp] theorem gd_gdI_ne_gdQ : gdI ≠ gdQ := by decide
@[simp] theorem gd_gdI_ne_gdK : gdI ≠ gdK := by decide
@[simp] theorem gd_gdI_ne_gdG : gdI ≠ gdG := by decide
@[simp] theorem gd_gdI_ne_gdR : gdI ≠ gdR := by decide
@[simp] theorem gd_gdI_ne_gdL : gdI ≠ gdL := by decide
@[simp] theorem gd_gdI_ne_gdX : gdI ≠ gdX := by decide
@[simp] theorem gd_gdI_ne_kFu : gdI ≠ kFu := by decide
@[simp] theorem gd_kFu_ne_gdI : kFu ≠ gdI := by decide
@[simp] theorem gd_gdI_ne_lFl : gdI ≠ lFl := by decide
@[simp] theorem gd_lFl_ne_gdI : lFl ≠ gdI := by decide
@[simp] theorem gd_gdI_ne_lDh : gdI ≠ lDh := by decide
@[simp] theorem gd_lDh_ne_gdI : lDh ≠ gdI := by decide
@[simp] theorem gd_gdI_ne_lDt : gdI ≠ lDt := by decide
@[simp] theorem gd_lDt_ne_gdI : lDt ≠ gdI := by decide
@[simp] theorem gd_gdI_ne_lDg : gdI ≠ lDg := by decide
@[simp] theorem gd_lDg_ne_gdI : lDg ≠ gdI := by decide
@[simp] theorem gd_gdI_ne_lDi : gdI ≠ lDi := by decide
@[simp] theorem gd_lDi_ne_gdI : lDi ≠ gdI := by decide
@[simp] theorem gd_gdI_ne_lRp : gdI ≠ lRp := by decide
@[simp] theorem gd_lRp_ne_gdI : lRp ≠ gdI := by decide
@[simp] theorem gd_gdI_ne_lRn : gdI ≠ lRn := by decide
@[simp] theorem gd_lRn_ne_gdI : lRn ≠ gdI := by decide
@[simp] theorem gd_gdI_ne_lDir : gdI ≠ lDir := by decide
@[simp] theorem gd_lDir_ne_gdI : lDir ≠ gdI := by decide
@[simp] theorem gd_gdI_ne_lFle : gdI ≠ lFle := by decide
@[simp] theorem gd_lFle_ne_gdI : lFle ≠ gdI := by decide
@[simp] theorem gd_gdI_ne_lKb : gdI ≠ lKb := by decide
@[simp] theorem gd_lKb_ne_gdI : lKb ≠ gdI := by decide
@[simp] theorem gd_gdU_ne_gdT : gdU ≠ gdT := by decide
@[simp] theorem gd_gdU_ne_gdI : gdU ≠ gdI := by decide
@[simp] theorem gd_gdU_ne_gdN : gdU ≠ gdN := by decide
@[simp] theorem gd_gdU_ne_gdP : gdU ≠ gdP := by decide
@[simp] theorem gd_gdU_ne_gdQ : gdU ≠ gdQ := by decide
@[simp] theorem gd_gdU_ne_gdK : gdU ≠ gdK := by decide
@[simp] theorem gd_gdU_ne_gdG : gdU ≠ gdG := by decide
@[simp] theorem gd_gdU_ne_gdR : gdU ≠ gdR := by decide
@[simp] theorem gd_gdU_ne_gdL : gdU ≠ gdL := by decide
@[simp] theorem gd_gdU_ne_gdX : gdU ≠ gdX := by decide
@[simp] theorem gd_gdU_ne_kFu : gdU ≠ kFu := by decide
@[simp] theorem gd_kFu_ne_gdU : kFu ≠ gdU := by decide
@[simp] theorem gd_gdU_ne_lFl : gdU ≠ lFl := by decide
@[simp] theorem gd_lFl_ne_gdU : lFl ≠ gdU := by decide
@[simp] theorem gd_gdU_ne_lDh : gdU ≠ lDh := by decide
@[simp] theorem gd_lDh_ne_gdU : lDh ≠ gdU := by decide
@[simp] theorem gd_gdU_ne_lDt : gdU ≠ lDt := by decide
@[simp] theorem gd_lDt_ne_gdU : lDt ≠ gdU := by decide
@[simp] theorem gd_gdU_ne_lDg : gdU ≠ lDg := by decide
@[simp] theorem gd_lDg_ne_gdU : lDg ≠ gdU := by decide
@[simp] theorem gd_gdU_ne_lDi : gdU ≠ lDi := by decide
@[simp] theorem gd_lDi_ne_gdU : lDi ≠ gdU := by decide
@[simp] theorem gd_gdU_ne_lRp : gdU ≠ lRp := by decide
@[simp] theorem gd_lRp_ne_gdU : lRp ≠ gdU := by decide
@[simp] theorem gd_gdU_ne_lRn : gdU ≠ lRn := by decide
@[simp] theorem gd_lRn_ne_gdU : lRn ≠ gdU := by decide
@[simp] theorem gd_gdU_ne_lDir : gdU ≠ lDir := by decide
@[simp] theorem gd_lDir_ne_gdU : lDir ≠ gdU := by decide
@[simp] theorem gd_gdU_ne_lFle : gdU ≠ lFle := by decide
@[simp] theorem gd_lFle_ne_gdU : lFle ≠ gdU := by decide
@[simp] theorem gd_gdU_ne_lKb : gdU ≠ lKb := by decide
@[simp] theorem gd_lKb_ne_gdU : lKb ≠ gdU := by decide
@[simp] theorem gd_gdN_ne_gdT : gdN ≠ gdT := by decide
@[simp] theorem gd_gdN_ne_gdI : gdN ≠ gdI := by decide
@[simp] theorem gd_gdN_ne_gdU : gdN ≠ gdU := by decide
@[simp] theorem gd_gdN_ne_gdP : gdN ≠ gdP := by decide
@[simp] theorem gd_gdN_ne_gdQ : gdN ≠ gdQ := by decide
@[simp] theorem gd_gdN_ne_gdK : gdN ≠ gdK := by decide
@[simp] theorem gd_gdN_ne_gdG : gdN ≠ gdG := by decide
@[simp] theorem gd_gdN_ne_gdR : gdN ≠ gdR := by decide
@[simp] theorem gd_gdN_ne_gdL : gdN ≠ gdL := by decide
@[simp] theorem gd_gdN_ne_gdX : gdN ≠ gdX := by decide
@[simp] theorem gd_gdN_ne_kFu : gdN ≠ kFu := by decide
@[simp] theorem gd_kFu_ne_gdN : kFu ≠ gdN := by decide
@[simp] theorem gd_gdN_ne_lFl : gdN ≠ lFl := by decide
@[simp] theorem gd_lFl_ne_gdN : lFl ≠ gdN := by decide
@[simp] theorem gd_gdN_ne_lDh : gdN ≠ lDh := by decide
@[simp] theorem gd_lDh_ne_gdN : lDh ≠ gdN := by decide
@[simp] theorem gd_gdN_ne_lDt : gdN ≠ lDt := by decide
@[simp] theorem gd_lDt_ne_gdN : lDt ≠ gdN := by decide
@[simp] theorem gd_gdN_ne_lDg : gdN ≠ lDg := by decide
@[simp] theorem gd_lDg_ne_gdN : lDg ≠ gdN := by decide
@[simp] theorem gd_gdN_ne_lDi : gdN ≠ lDi := by decide
@[simp] theorem gd_lDi_ne_gdN : lDi ≠ gdN := by decide
@[simp] theorem gd_gdN_ne_lRp : gdN ≠ lRp := by decide
@[simp] theorem gd_lRp_ne_gdN : lRp ≠ gdN := by decide
@[simp] theorem gd_gdN_ne_lRn : gdN ≠ lRn := by decide
@[simp] theorem gd_lRn_ne_gdN : lRn ≠ gdN := by decide
@[simp] theorem gd_gdN_ne_lDir : gdN ≠ lDir := by decide
@[simp] theorem gd_lDir_ne_gdN : lDir ≠ gdN := by decide
@[simp] theorem gd_gdN_ne_lFle : gdN ≠ lFle := by decide
@[simp] theorem gd_lFle_ne_gdN : lFle ≠ gdN := by decide
@[simp] theorem gd_gdN_ne_lKb : gdN ≠ lKb := by decide
@[simp] theorem gd_lKb_ne_gdN : lKb ≠ gdN := by decide
@[simp] theorem gd_gdP_ne_gdT : gdP ≠ gdT := by decide
@[simp] theorem gd_gdP_ne_gdI : gdP ≠ gdI := by decide
@[simp] theorem gd_gdP_ne_gdU : gdP ≠ gdU := by decide
@[simp] theorem gd_gdP_ne_gdN : gdP ≠ gdN := by decide
@[simp] theorem gd_gdP_ne_gdQ : gdP ≠ gdQ := by decide
@[simp] theorem gd_gdP_ne_gdK : gdP ≠ gdK := by decide
@[simp] theorem gd_gdP_ne_gdG : gdP ≠ gdG := by decide
@[simp] theorem gd_gdP_ne_gdR : gdP ≠ gdR := by decide
@[simp] theorem gd_gdP_ne_gdL : gdP ≠ gdL := by decide
@[simp] theorem gd_gdP_ne_gdX : gdP ≠ gdX := by decide
@[simp] theorem gd_gdP_ne_kFu : gdP ≠ kFu := by decide
@[simp] theorem gd_kFu_ne_gdP : kFu ≠ gdP := by decide
@[simp] theorem gd_gdP_ne_lFl : gdP ≠ lFl := by decide
@[simp] theorem gd_lFl_ne_gdP : lFl ≠ gdP := by decide
@[simp] theorem gd_gdP_ne_lDh : gdP ≠ lDh := by decide
@[simp] theorem gd_lDh_ne_gdP : lDh ≠ gdP := by decide
@[simp] theorem gd_gdP_ne_lDt : gdP ≠ lDt := by decide
@[simp] theorem gd_lDt_ne_gdP : lDt ≠ gdP := by decide
@[simp] theorem gd_gdP_ne_lDg : gdP ≠ lDg := by decide
@[simp] theorem gd_lDg_ne_gdP : lDg ≠ gdP := by decide
@[simp] theorem gd_gdP_ne_lDi : gdP ≠ lDi := by decide
@[simp] theorem gd_lDi_ne_gdP : lDi ≠ gdP := by decide
@[simp] theorem gd_gdP_ne_lRp : gdP ≠ lRp := by decide
@[simp] theorem gd_lRp_ne_gdP : lRp ≠ gdP := by decide
@[simp] theorem gd_gdP_ne_lRn : gdP ≠ lRn := by decide
@[simp] theorem gd_lRn_ne_gdP : lRn ≠ gdP := by decide
@[simp] theorem gd_gdP_ne_lDir : gdP ≠ lDir := by decide
@[simp] theorem gd_lDir_ne_gdP : lDir ≠ gdP := by decide
@[simp] theorem gd_gdP_ne_lFle : gdP ≠ lFle := by decide
@[simp] theorem gd_lFle_ne_gdP : lFle ≠ gdP := by decide
@[simp] theorem gd_gdP_ne_lKb : gdP ≠ lKb := by decide
@[simp] theorem gd_lKb_ne_gdP : lKb ≠ gdP := by decide
@[simp] theorem gd_gdQ_ne_gdT : gdQ ≠ gdT := by decide
@[simp] theorem gd_gdQ_ne_gdI : gdQ ≠ gdI := by decide
@[simp] theorem gd_gdQ_ne_gdU : gdQ ≠ gdU := by decide
@[simp] theorem gd_gdQ_ne_gdN : gdQ ≠ gdN := by decide
@[simp] theorem gd_gdQ_ne_gdP : gdQ ≠ gdP := by decide
@[simp] theorem gd_gdQ_ne_gdK : gdQ ≠ gdK := by decide
@[simp] theorem gd_gdQ_ne_gdG : gdQ ≠ gdG := by decide
@[simp] theorem gd_gdQ_ne_gdR : gdQ ≠ gdR := by decide
@[simp] theorem gd_gdQ_ne_gdL : gdQ ≠ gdL := by decide
@[simp] theorem gd_gdQ_ne_gdX : gdQ ≠ gdX := by decide
@[simp] theorem gd_gdQ_ne_kFu : gdQ ≠ kFu := by decide
@[simp] theorem gd_kFu_ne_gdQ : kFu ≠ gdQ := by decide
@[simp] theorem gd_gdQ_ne_lFl : gdQ ≠ lFl := by decide
@[simp] theorem gd_lFl_ne_gdQ : lFl ≠ gdQ := by decide
@[simp] theorem gd_gdQ_ne_lDh : gdQ ≠ lDh := by decide
@[simp] theorem gd_lDh_ne_gdQ : lDh ≠ gdQ := by decide
@[simp] theorem gd_gdQ_ne_lDt : gdQ ≠ lDt := by decide
@[simp] theorem gd_lDt_ne_gdQ : lDt ≠ gdQ := by decide
@[simp] theorem gd_gdQ_ne_lDg : gdQ ≠ lDg := by decide
@[simp] theorem gd_lDg_ne_gdQ : lDg ≠ gdQ := by decide
@[simp] theorem gd_gdQ_ne_lDi : gdQ ≠ lDi := by decide
@[simp] theorem gd_lDi_ne_gdQ : lDi ≠ gdQ := by decide
@[simp] theorem gd_gdQ_ne_lRp : gdQ ≠ lRp := by decide
@[simp] theorem gd_lRp_ne_gdQ : lRp ≠ gdQ := by decide
@[simp] theorem gd_gdQ_ne_lRn : gdQ ≠ lRn := by decide
@[simp] theorem gd_lRn_ne_gdQ : lRn ≠ gdQ := by decide
@[simp] theorem gd_gdQ_ne_lDir : gdQ ≠ lDir := by decide
@[simp] theorem gd_lDir_ne_gdQ : lDir ≠ gdQ := by decide
@[simp] theorem gd_gdQ_ne_lFle : gdQ ≠ lFle := by decide
@[simp] theorem gd_lFle_ne_gdQ : lFle ≠ gdQ := by decide
@[simp] theorem gd_gdQ_ne_lKb : gdQ ≠ lKb := by decide
@[simp] theorem gd_lKb_ne_gdQ : lKb ≠ gdQ := by decide
@[simp] theorem gd_gdK_ne_gdT : gdK ≠ gdT := by decide
@[simp] theorem gd_gdK_ne_gdI : gdK ≠ gdI := by decide
@[simp] theorem gd_gdK_ne_gdU : gdK ≠ gdU := by decide
@[simp] theorem gd_gdK_ne_gdN : gdK ≠ gdN := by decide
@[simp] theorem gd_gdK_ne_gdP : gdK ≠ gdP := by decide
@[simp] theorem gd_gdK_ne_gdQ : gdK ≠ gdQ := by decide
@[simp] theorem gd_gdK_ne_gdG : gdK ≠ gdG := by decide
@[simp] theorem gd_gdK_ne_gdR : gdK ≠ gdR := by decide
@[simp] theorem gd_gdK_ne_gdL : gdK ≠ gdL := by decide
@[simp] theorem gd_gdK_ne_gdX : gdK ≠ gdX := by decide
@[simp] theorem gd_gdK_ne_kFu : gdK ≠ kFu := by decide
@[simp] theorem gd_kFu_ne_gdK : kFu ≠ gdK := by decide
@[simp] theorem gd_gdK_ne_lFl : gdK ≠ lFl := by decide
@[simp] theorem gd_lFl_ne_gdK : lFl ≠ gdK := by decide
@[simp] theorem gd_gdK_ne_lDh : gdK ≠ lDh := by decide
@[simp] theorem gd_lDh_ne_gdK : lDh ≠ gdK := by decide
@[simp] theorem gd_gdK_ne_lDt : gdK ≠ lDt := by decide
@[simp] theorem gd_lDt_ne_gdK : lDt ≠ gdK := by decide
@[simp] theorem gd_gdK_ne_lDg : gdK ≠ lDg := by decide
@[simp] theorem gd_lDg_ne_gdK : lDg ≠ gdK := by decide
@[simp] theorem gd_gdK_ne_lDi : gdK ≠ lDi := by decide
@[simp] theorem gd_lDi_ne_gdK : lDi ≠ gdK := by decide
@[simp] theorem gd_gdK_ne_lRp : gdK ≠ lRp := by decide
@[simp] theorem gd_lRp_ne_gdK : lRp ≠ gdK := by decide
@[simp] theorem gd_gdK_ne_lRn : gdK ≠ lRn := by decide
@[simp] theorem gd_lRn_ne_gdK : lRn ≠ gdK := by decide
@[simp] theorem gd_gdK_ne_lDir : gdK ≠ lDir := by decide
@[simp] theorem gd_lDir_ne_gdK : lDir ≠ gdK := by decide
@[simp] theorem gd_gdK_ne_lFle : gdK ≠ lFle := by decide
@[simp] theorem gd_lFle_ne_gdK : lFle ≠ gdK := by decide
@[simp] theorem gd_gdK_ne_lKb : gdK ≠ lKb := by decide
@[simp] theorem gd_lKb_ne_gdK : lKb ≠ gdK := by decide
@[simp] theorem gd_gdG_ne_gdT : gdG ≠ gdT := by decide
@[simp] theorem gd_gdG_ne_gdI : gdG ≠ gdI := by decide
@[simp] theorem gd_gdG_ne_gdU : gdG ≠ gdU := by decide
@[simp] theorem gd_gdG_ne_gdN : gdG ≠ gdN := by decide
@[simp] theorem gd_gdG_ne_gdP : gdG ≠ gdP := by decide
@[simp] theorem gd_gdG_ne_gdQ : gdG ≠ gdQ := by decide
@[simp] theorem gd_gdG_ne_gdK : gdG ≠ gdK := by decide
@[simp] theorem gd_gdG_ne_gdR : gdG ≠ gdR := by decide
@[simp] theorem gd_gdG_ne_gdL : gdG ≠ gdL := by decide
@[simp] theorem gd_gdG_ne_gdX : gdG ≠ gdX := by decide
@[simp] theorem gd_gdG_ne_kFu : gdG ≠ kFu := by decide
@[simp] theorem gd_kFu_ne_gdG : kFu ≠ gdG := by decide
@[simp] theorem gd_gdG_ne_lFl : gdG ≠ lFl := by decide
@[simp] theorem gd_lFl_ne_gdG : lFl ≠ gdG := by decide
@[simp] theorem gd_gdG_ne_lDh : gdG ≠ lDh := by decide
@[simp] theorem gd_lDh_ne_gdG : lDh ≠ gdG := by decide
@[simp] theorem gd_gdG_ne_lDt : gdG ≠ lDt := by decide
@[simp] theorem gd_lDt_ne_gdG : lDt ≠ gdG := by decide
@[simp] theorem gd_gdG_ne_lDg : gdG ≠ lDg := by decide
@[simp] theorem gd_lDg_ne_gdG : lDg ≠ gdG := by decide
@[simp] theorem gd_gdG_ne_lDi : gdG ≠ lDi := by decide
@[simp] theorem gd_lDi_ne_gdG : lDi ≠ gdG := by decide
@[simp] theorem gd_gdG_ne_lRp : gdG ≠ lRp := by decide
@[simp] theorem gd_lRp_ne_gdG : lRp ≠ gdG := by decide
@[simp] theorem gd_gdG_ne_lRn : gdG ≠ lRn := by decide
@[simp] theorem gd_lRn_ne_gdG : lRn ≠ gdG := by decide
@[simp] theorem gd_gdG_ne_lDir : gdG ≠ lDir := by decide
@[simp] theorem gd_lDir_ne_gdG : lDir ≠ gdG := by decide
@[simp] theorem gd_gdG_ne_lFle : gdG ≠ lFle := by decide
@[simp] theorem gd_lFle_ne_gdG : lFle ≠ gdG := by decide
@[simp] theorem gd_gdG_ne_lKb : gdG ≠ lKb := by decide
@[simp] theorem gd_lKb_ne_gdG : lKb ≠ gdG := by decide
@[simp] theorem gd_gdR_ne_gdT : gdR ≠ gdT := by decide
@[simp] theorem gd_gdR_ne_gdI : gdR ≠ gdI := by decide
@[simp] theorem gd_gdR_ne_gdU : gdR ≠ gdU := by decide
@[simp] theorem gd_gdR_ne_gdN : gdR ≠ gdN := by decide
@[simp] theorem gd_gdR_ne_gdP : gdR ≠ gdP := by decide
@[simp] theorem gd_gdR_ne_gdQ : gdR ≠ gdQ := by decide
@[simp] theorem gd_gdR_ne_gdK : gdR ≠ gdK := by decide
@[simp] theorem gd_gdR_ne_gdG : gdR ≠ gdG := by decide
@[simp] theorem gd_gdR_ne_gdL : gdR ≠ gdL := by decide
@[simp] theorem gd_gdR_ne_gdX : gdR ≠ gdX := by decide
@[simp] theorem gd_gdR_ne_kFu : gdR ≠ kFu := by decide
@[simp] theorem gd_kFu_ne_gdR : kFu ≠ gdR := by decide
@[simp] theorem gd_gdR_ne_lFl : gdR ≠ lFl := by decide
@[simp] theorem gd_lFl_ne_gdR : lFl ≠ gdR := by decide
@[simp] theorem gd_gdR_ne_lDh : gdR ≠ lDh := by decide
@[simp] theorem gd_lDh_ne_gdR : lDh ≠ gdR := by decide
@[simp] theorem gd_gdR_ne_lDt : gdR ≠ lDt := by decide
@[simp] theorem gd_lDt_ne_gdR : lDt ≠ gdR := by decide
@[simp] theorem gd_gdR_ne_lDg : gdR ≠ lDg := by decide
@[simp] theorem gd_lDg_ne_gdR : lDg ≠ gdR := by decide
@[simp] theorem gd_gdR_ne_lDi : gdR ≠ lDi := by decide
@[simp] theorem gd_lDi_ne_gdR : lDi ≠ gdR := by decide
@[simp] theorem gd_gdR_ne_lRp : gdR ≠ lRp := by decide
@[simp] theorem gd_lRp_ne_gdR : lRp ≠ gdR := by decide
@[simp] theorem gd_gdR_ne_lRn : gdR ≠ lRn := by decide
@[simp] theorem gd_lRn_ne_gdR : lRn ≠ gdR := by decide
@[simp] theorem gd_gdR_ne_lDir : gdR ≠ lDir := by decide
@[simp] theorem gd_lDir_ne_gdR : lDir ≠ gdR := by decide
@[simp] theorem gd_gdR_ne_lFle : gdR ≠ lFle := by decide
@[simp] theorem gd_lFle_ne_gdR : lFle ≠ gdR := by decide
@[simp] theorem gd_gdR_ne_lKb : gdR ≠ lKb := by decide
@[simp] theorem gd_lKb_ne_gdR : lKb ≠ gdR := by decide
@[simp] theorem gd_gdL_ne_gdT : gdL ≠ gdT := by decide
@[simp] theorem gd_gdL_ne_gdI : gdL ≠ gdI := by decide
@[simp] theorem gd_gdL_ne_gdU : gdL ≠ gdU := by decide
@[simp] theorem gd_gdL_ne_gdN : gdL ≠ gdN := by decide
@[simp] theorem gd_gdL_ne_gdP : gdL ≠ gdP := by decide
@[simp] theorem gd_gdL_ne_gdQ : gdL ≠ gdQ := by decide
@[simp] theorem gd_gdL_ne_gdK : gdL ≠ gdK := by decide
@[simp] theorem gd_gdL_ne_gdG : gdL ≠ gdG := by decide
@[simp] theorem gd_gdL_ne_gdR : gdL ≠ gdR := by decide
@[simp] theorem gd_gdL_ne_gdX : gdL ≠ gdX := by decide
@[simp] theorem gd_gdL_ne_kFu : gdL ≠ kFu := by decide
@[simp] theorem gd_kFu_ne_gdL : kFu ≠ gdL := by decide
@[simp] theorem gd_gdL_ne_lFl : gdL ≠ lFl := by decide
@[simp] theorem gd_lFl_ne_gdL : lFl ≠ gdL := by decide
@[simp] theorem gd_gdL_ne_lDh : gdL ≠ lDh := by decide
@[simp] theorem gd_lDh_ne_gdL : lDh ≠ gdL := by decide
@[simp] theorem gd_gdL_ne_lDt : gdL ≠ lDt := by decide
@[simp] theorem gd_lDt_ne_gdL : lDt ≠ gdL := by decide
@[simp] theorem gd_gdL_ne_lDg : gdL ≠ lDg := by decide
@[simp] theorem gd_lDg_ne_gdL : lDg ≠ gdL := by decide
@[simp] theorem gd_gdL_ne_lDi : gdL ≠ lDi := by decide
@[simp] theorem gd_lDi_ne_gdL : lDi ≠ gdL := by decide
@[simp] theorem gd_gdL_ne_lRp : gdL ≠ lRp := by decide
@[simp] theorem gd_lRp_ne_gdL : lRp ≠ gdL := by decide
@[simp] theorem gd_gdL_ne_lRn : gdL ≠ lRn := by decide
@[simp] theorem gd_lRn_ne_gdL : lRn ≠ gdL := by decide
@[simp] theorem gd_gdL_ne_lDir : gdL ≠ lDir := by decide
@[simp] theorem gd_lDir_ne_gdL : lDir ≠ gdL := by decide
@[simp] theorem gd_gdL_ne_lFle : gdL ≠ lFle := by decide
@[simp] theorem gd_lFle_ne_gdL : lFle ≠ gdL := by decide
@[simp] theorem gd_gdL_ne_lKb : gdL ≠ lKb := by decide
@[simp] theorem gd_lKb_ne_gdL : lKb ≠ gdL := by decide
@[simp] theorem gd_gdX_ne_gdT : gdX ≠ gdT := by decide
@[simp] theorem gd_gdX_ne_gdI : gdX ≠ gdI := by decide
@[simp] theorem gd_gdX_ne_gdU : gdX ≠ gdU := by decide
@[simp] theorem gd_gdX_ne_gdN : gdX ≠ gdN := by decide
@[simp] theorem gd_gdX_ne_gdP : gdX ≠ gdP := by decide
@[simp] theorem gd_gdX_ne_gdQ : gdX ≠ gdQ := by decide
@[simp] theorem gd_gdX_ne_gdK : gdX ≠ gdK := by decide
@[simp] theorem gd_gdX_ne_gdG : gdX ≠ gdG := by decide
@[simp] theorem gd_gdX_ne_gdR : gdX ≠ gdR := by decide
@[simp] theorem gd_gdX_ne_gdL : gdX ≠ gdL := by decide
@[simp] theorem gd_gdX_ne_kFu : gdX ≠ kFu := by decide
@[simp] theorem gd_kFu_ne_gdX : kFu ≠ gdX := by decide
@[simp] theorem gd_gdX_ne_lFl : gdX ≠ lFl := by decide
@[simp] theorem gd_lFl_ne_gdX : lFl ≠ gdX := by decide
@[simp] theorem gd_gdX_ne_lDh : gdX ≠ lDh := by decide
@[simp] theorem gd_lDh_ne_gdX : lDh ≠ gdX := by decide
@[simp] theorem gd_gdX_ne_lDt : gdX ≠ lDt := by decide
@[simp] theorem gd_lDt_ne_gdX : lDt ≠ gdX := by decide
@[simp] theorem gd_gdX_ne_lDg : gdX ≠ lDg := by decide
@[simp] theorem gd_lDg_ne_gdX : lDg ≠ gdX := by decide
@[simp] theorem gd_gdX_ne_lDi : gdX ≠ lDi := by decide
@[simp] theorem gd_lDi_ne_gdX : lDi ≠ gdX := by decide
@[simp] theorem gd_gdX_ne_lRp : gdX ≠ lRp := by decide
@[simp] theorem gd_lRp_ne_gdX : lRp ≠ gdX := by decide
@[simp] theorem gd_gdX_ne_lRn : gdX ≠ lRn := by decide
@[simp] theorem gd_lRn_ne_gdX : lRn ≠ gdX := by decide
@[simp] theorem gd_gdX_ne_lDir : gdX ≠ lDir := by decide
@[simp] theorem gd_lDir_ne_gdX : lDir ≠ gdX := by decide
@[simp] theorem gd_gdX_ne_lFle : gdX ≠ lFle := by decide
@[simp] theorem gd_lFle_ne_gdX : lFle ≠ gdX := by decide
@[simp] theorem gd_gdX_ne_lKb : gdX ≠ lKb := by decide
@[simp] theorem gd_lKb_ne_gdX : lKb ≠ gdX := by decide

theorem shr1_two (k : Nat) (hk : 2 * k < 2 ^ 64) : (BitVec.ofNat 64 (2 * k)) >>> (1 : Nat) = BitVec.ofNat 64 k := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hk]
  rw [Nat.mod_eq_of_lt (by omega)]; omega

def gdParams : List MlS := [kFu, gdT, gdI, gdU]
def gdLocals : List MlS := [gdN, gdP, gdQ, gdK, gdG, gdR, gdL, gdX]

def gdBody (C : Ctx) : ProgHOL 64 := prologue gdLocals
  (.seq (.assign .local gdN (.load .one (vv gdT))) (envFindP C gdP (vv gdN) (.ite (.cmp .equal (vv gdP) (.const 0)) hang (.seq (.assign .local gdQ (.op .sub [(vv gdP), (.const 1)])) (.seq (.assign .local gdK (.load .one (vv gdQ))) (.ite (.cmp .equal (vv gdK) (.const 3)) (.seq (.call (some (some (.local, gdG), none)) fGs [(vv kFu), (.const 0), (vv gdQ), (vv gdU)]) (.ite (.cmp .equal (vv gdG) (.const 0)) (.return (.const 0)) (.seq (.call (some (some (.local, gdR), none)) fGw [(vv gdT), (vv gdI), (vv gdU)]) (.ite (.cmp .equal (vv gdR) (.const 0)) hang (.seq (.assign .local gdL (.load .one (vv gdR))) (.seq (.call (some (some (.local, gdX), none)) fCg [(vv kFu), (.op .sub [(vv gdG), (.const 1)]), (vv gdR), (.shift .lsr (vv gdL) (.const 1)), (.const 0)]) (.return (vv gdX)))))))) hang))))))

section
variable {σ : Type}

theorem gd_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ gdLocals → (ctxEnv C ++ gdParams.zip vals).get x = none :=
  Knot.params_none C gdLocals gdParams vals (by decide) (by decide)

structure GdCodes (C : Ctx) : Prop where
  mg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  mp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  gs : C.code.lookup fGs = some (fzParams.map (fun p => (p, ShapeHOL.one)), gsBody C, .one)
  gw : C.code.lookup fGw = some (gwParams.map (fun p => (p, ShapeHOL.one)), gwBody C, .one)
  cg : C.code.lookup fCg = some (cgParams.map (fun p => (p, ShapeHOL.one)), cgBody, .one)

theorem gd_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) (hok : CtxOK C) (hc : GdCodes C)
    (tbl : IProjTable) (ot : Nat) (htb : TblE C.EB C.EH ot tbl) (i : Nat) (us : LsIdx)
    (hGs : ∀ s1 cvT caps o, C.fe.find? tbl.structName = some (.indInfo cvT caps) →
      CIE C.EB C.EH o (.indInfo cvT caps) →
      SpecR (σ := σ) (Pre C s1 (fzParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 0, ecell C o, Enc.idxW us]))
        (gsBody C) s1 (projGuardSort (knot mode C n) cvT caps us) (PostGS C))
    (hGw : ∀ (H : List (BitVec 64)) (St : EStore) s1, C.H <+: H →
      SpecR (σ := σ) (Pre (ctxSt (ctxH C H) St) s1 (gwParams.zip [ecell C ot, BitVec.ofNat 64 i, Enc.idxW us]))
        (gwBody C) s1 (projGuardRows C.fe (tbl.entry i) us) (PostRows (ctxSt (ctxH C H) St)))
    (hCg : ∀ (H : List (BitVec 64)) (St : EStore) s1 gl (gh : LIdx) (rows : Array (Nat × EIdx)) o, C.H <+: H →
      denoteL St.ls gh = some gl → BlkAt H o (rowsW rows.toList) → rows.size < 2 ^ 58 →
      (∀ p ∈ rows.toList, p.1 < 2 ^ 63) →
      SpecR (σ := σ) (Pre (ctxSt (ctxH C H) St) s1 (cgParams.zip [BitVec.ofNat 64 n, Enc.idxW gh, cellA C o,
        BitVec.ofNat 64 rows.size, BitVec.ofNat 64 0])) cgBody s1
        (checkGuardRows (knot mode C n) gl rows 0) (PostU (ctxSt (ctxH C H) St)))
    (s : AState) :
    SpecR (σ := σ) (Pre C s (gdParams.zip [BitVec.ofNat 64 n, ecell C ot, BitVec.ofNat 64 i, Enc.idxW us]))
      (gdBody C) s (checkProjGuard (knot mode C n) C.fe (tbl.entry i) us) (PostU C) := by
  refine specR_prologue (postU_locals C) (gd_none C _) ?_
  refine specR_envLoadI gdN (vv gdT) ot (Enc.idxW tbl.structName) (by decide) (by simp +decide [Env.get, gdParams, ctxEnv] <;> rfl) htb.1 ?_
  refine specR_envFindI hok hc.mg hc.mp gdP (vv gdN) tbl.structName (by decide) (by simp)
    (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  have hrel := find_rel hok tbl.structName
  revert hrel
  unfold checkProjGuard
  simp only [IProjTable.entry]
  rcases hfind : C.fe.find? tbl.structName with _ | ci
  · intro hrel; simp only at hrel; rw [hrel]
    exact specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI)
      (fun h => absurd h (by decide))
  intro ⟨o, hm, hci⟩
  rw [hm]
  refine specR_atEntry fun t ht => ?_
  have hoE : o < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI gdQ _ (ecell C o) (by decide) (by simp [sev, optWG]; exact BitVec.add_sub_cancel _ _) ?_
  have htag : ∃ k : Nat, C.EH[o]? = some (BitVec.ofNat 64 k) ∧ k < 6 ∧ (k = 3 ↔ ∃ cvT caps, ci = .indInfo cvT caps) := by
    rcases ci with _ | _ | _ | ⟨cvT, caps⟩ | _ | _
    all_goals first
      | exact ⟨0, hci.2, by decide, by simp⟩ | exact ⟨1, hci.2.1, by decide, by simp⟩
      | exact ⟨2, hci.2, by decide, by simp⟩ | exact ⟨3, hci.2.1, by decide, by simp⟩
      | exact ⟨4, hci.2.1, by decide, by simp⟩ | exact ⟨5, hci.2.1, by decide, by simp⟩
  obtain ⟨k, hk, hk6, hk3⟩ := htag
  refine specR_envLoadI gdK (vv gdQ) o _ (by decide) (by simp) hk ?_
  by_cases h3 : k = 3
  swap
  · have hne : BitVec.ofNat 64 k ≠ 3#64 := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun h => absurd rfl h)
      (fun _ => ?_)
    have hnot : ¬ ∃ cvT caps, ci = .indInfo cvT caps := fun h => h3 (hk3.mpr h)
    rcases ci with _ | _ | _ | ⟨cvT, caps⟩ | _ | _
    all_goals first | exact specR_hangI | exact absurd ⟨_, _, rfl⟩ hnot
  obtain ⟨cvT, caps, rfl⟩ := hk3.mp h3
  subst h3
  refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
    (fun h => absurd h (by decide))
  dsimp only
  refine specR_callNIH (C := C) gdG fGs fzParams [vv kFu, .const 0, vv gdQ, vv gdU] (gsBody C)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 0, ecell C o, Enc.idxW us] (by decide) rfl (by decide) hc.gs
    ⟨by simp +decide [Env.get, gdParams, ctxEnv], rfl, by simp, by simp +decide [Env.get, gdParams, ctxEnv], trivial⟩
    (fun a w s' st => projGuardSort (knot mode C n) cvT caps us s = .ok (a, s') ∧ PostGS C a w s' st)
    (fun a w s' _ => projGuardSort (knot mode C n) cvT caps us s = .ok (a, s') ∧ (a = none → w = 0) ∧
      ∀ l, a = some l → ∃ h : LIdx, w = Enc.idxW h + 1 ∧ denoteL s'.store.ls h = some l)
    (fun a w s' st ⟨hrun, H', hp, hsr, h1, h2⟩ => ⟨H', hp, ⟨hrun, h1, h2⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu fzParams _ rfl hlk)
      (hGs s cvT caps o hfind hci)))
    (fun g w s1 H1 hp1 ⟨hrun1, h1, h2⟩ => ?_)
  rcases g with _ | gl
  · have hw0 := h1 rfl; subst hw0
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    dsimp only
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  obtain ⟨gh, hw, hgd⟩ := h2 gl rfl
  subst hw
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact lidxW_add_one_ne gh)
    (fun h => absurd rfl h) (fun _ => ?_)
  dsimp only
  refine specR_invRaise (R' := PostU (ctxSt C s1.store)) ?_
    (fun a w s' t hx ⟨H', hp', hsr⟩ => ⟨H', hp', sr_lower hsr hx⟩)
  refine specR_callNIH (C := ctxSt (ctxH C H1) s1.store) gdR fGw gwParams [vv gdT, vv gdI, vv gdU] (gwBody C)
    [ecell C ot, BitVec.ofNat 64 i, Enc.idxW us] (by decide) rfl (by decide) hc.gw
    ⟨by simp +decide [Env.get, gdParams, ctxEnv] <;> rfl, by simp +decide [Env.get, gdParams, ctxEnv], by simp +decide [Env.get, gdParams, ctxEnv], trivial⟩
    (fun a w s' st => projGuardRows C.fe (tbl.entry i) us s1 = .ok (a, s') ∧ PostRows (ctxSt (ctxH C H1) s1.store) a w s' st)
    (fun a w s' H' => projGuardRows C.fe (tbl.entry i) us s1 = .ok (a, s') ∧ (a = none → w = 0) ∧
      ∀ rows, a = some rows → ∃ ob, w = cellA C ob ∧ BlkAt H' ob (rowsW rows.toList) ∧
        (∀ p ∈ rows.toList, p.1 < 2 ^ 63) ∧ rows.size < 2 ^ 58)
    (fun a w s' st ⟨hrun, H', hp, hsr, h1, h2⟩ => ⟨H', hp, ⟨hrun, h1, h2⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu gwParams _ rfl hlk)
      (by simpa [IProjTable.entry] using hGw H1 s1.store s1 hp1)))
    (fun rr w s2 H2 hp2 ⟨hrun2, h1', h2'⟩ => ?_)
  rcases rr with _ | rows
  · have hw0 := h1' rfl; subst hw0
    exact specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI)
      (fun h => absurd h (by decide))
  obtain ⟨ob, hw, hb, hall, hsz⟩ := h2' rows rfl
  subst hw
  refine specR_atEntry fun t2 ht2 => ?_
  have hobN : ob < C.HN := by
    obtain ⟨H0, hp0, ha0⟩ := ht2.sr.heap
    have hl := blkAt_lt hb
    have := ha0.len; have := hp0.length_le
    simp only [ctxH, ctxSt] at *; omega
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ExSP.cellA_ne0 C hok ob hobN)
    (fun h => absurd rfl h) (fun _ => ?_)
  dsimp only
  have hrl := rowsW_length rows.toList
  refine UD.specR_heapLoadI' (C := ctxSt (ctxH C H2) s1.store) gdL (vv gdR) ob (BitVec.ofNat 64 (2 * rows.size)) (by
    show H2[ob]? = _; rw [hb.1, hrl]; simp) (by decide) (by simp; rfl) ?_
  refine specR_congr (m' := checkGuardRows (knot mode C n) gl rows 0 >>= fun r => pure r) (by simp) ?_
  refine specR_callNIH (C := ctxSt (ctxH C H2) s1.store) gdX fCg cgParams
    [vv kFu, .op .sub [vv gdG, .const 1], vv gdR, .shift .lsr (vv gdL) (.const 1), .const 0] cgBody
    [BitVec.ofNat 64 n, Enc.idxW gh, cellA C ob, BitVec.ofNat 64 rows.size, BitVec.ofNat 64 0] (by decide) rfl
    (by decide) hc.cg
    ⟨by simp +decide [Env.get, gdParams, ctxEnv], by simp +decide [sev, Env.get]; exact BitVec.add_sub_cancel _ _, by simp <;> rfl,
      by simp +decide [sev, Env.get]; exact shr1_two rows.size (by omega), rfl, trivial⟩
    (PostU (ctxSt (ctxH C H2) s1.store)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cgParams _ rfl hlk)
      (hCg H2 s1.store s2 gl gh rows ob (hp1.trans hp2) hgd hb hsz hall))
    (fun r w s3 H3 hp3 _ => ?_)
  exact specR_returnI _ w (by simp) (fun t ht => ⟨H3, hp1.trans (hp2.trans hp3), sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
