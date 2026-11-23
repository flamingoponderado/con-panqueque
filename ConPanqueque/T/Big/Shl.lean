import ConPanqueque.T.Big.Shr
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `Nat.shiftLeft`

`shl(a, b)` for `b < 2^64`: `a = 0` or `b = 0` answers `a`; otherwise `t = a * 2^r` by the verified product with
the one-limb block `[2^r]`, and the answer is `q` zero limbs followed by `t`'s (`b = 64 q + r`).
-/

namespace ConPanqueque.T.Big

open ConPanqueque.T ConPanqueque.T.Ex
open ConPanqueque.V.Enc

def gX := ofString "gx"
def gY := ofString "gy"
def gLa := ofString "gla"
def gLb := ofString "glb"
def gBw := ofString "gbw"
def gQ := ofString "gq"
def gR := ofString "gr"
def gP := ofString "gp"
def gT := ofString "gt"
def gLt := ofString "glt"
def gCnt := ofString "gcnt"
def gO := ofString "go"
def gQz := ofString "gqz"
def gZi := ofString "gzi"

@[simp] theorem gX_ne_gY : gX ≠ gY := by decide
@[simp] theorem gX_ne_gLa : gX ≠ gLa := by decide
@[simp] theorem gX_ne_gLb : gX ≠ gLb := by decide
@[simp] theorem gX_ne_gBw : gX ≠ gBw := by decide
@[simp] theorem gX_ne_gQ : gX ≠ gQ := by decide
@[simp] theorem gX_ne_gR : gX ≠ gR := by decide
@[simp] theorem gX_ne_gP : gX ≠ gP := by decide
@[simp] theorem gX_ne_gT : gX ≠ gT := by decide
@[simp] theorem gX_ne_gLt : gX ≠ gLt := by decide
@[simp] theorem gX_ne_gCnt : gX ≠ gCnt := by decide
@[simp] theorem gX_ne_gO : gX ≠ gO := by decide
@[simp] theorem gX_ne_gQz : gX ≠ gQz := by decide
@[simp] theorem gX_ne_gZi : gX ≠ gZi := by decide
@[simp] theorem gY_ne_gX : gY ≠ gX := by decide
@[simp] theorem gY_ne_gLa : gY ≠ gLa := by decide
@[simp] theorem gY_ne_gLb : gY ≠ gLb := by decide
@[simp] theorem gY_ne_gBw : gY ≠ gBw := by decide
@[simp] theorem gY_ne_gQ : gY ≠ gQ := by decide
@[simp] theorem gY_ne_gR : gY ≠ gR := by decide
@[simp] theorem gY_ne_gP : gY ≠ gP := by decide
@[simp] theorem gY_ne_gT : gY ≠ gT := by decide
@[simp] theorem gY_ne_gLt : gY ≠ gLt := by decide
@[simp] theorem gY_ne_gCnt : gY ≠ gCnt := by decide
@[simp] theorem gY_ne_gO : gY ≠ gO := by decide
@[simp] theorem gY_ne_gQz : gY ≠ gQz := by decide
@[simp] theorem gY_ne_gZi : gY ≠ gZi := by decide
@[simp] theorem gLa_ne_gX : gLa ≠ gX := by decide
@[simp] theorem gLa_ne_gY : gLa ≠ gY := by decide
@[simp] theorem gLa_ne_gLb : gLa ≠ gLb := by decide
@[simp] theorem gLa_ne_gBw : gLa ≠ gBw := by decide
@[simp] theorem gLa_ne_gQ : gLa ≠ gQ := by decide
@[simp] theorem gLa_ne_gR : gLa ≠ gR := by decide
@[simp] theorem gLa_ne_gP : gLa ≠ gP := by decide
@[simp] theorem gLa_ne_gT : gLa ≠ gT := by decide
@[simp] theorem gLa_ne_gLt : gLa ≠ gLt := by decide
@[simp] theorem gLa_ne_gCnt : gLa ≠ gCnt := by decide
@[simp] theorem gLa_ne_gO : gLa ≠ gO := by decide
@[simp] theorem gLa_ne_gQz : gLa ≠ gQz := by decide
@[simp] theorem gLa_ne_gZi : gLa ≠ gZi := by decide
@[simp] theorem gLb_ne_gX : gLb ≠ gX := by decide
@[simp] theorem gLb_ne_gY : gLb ≠ gY := by decide
@[simp] theorem gLb_ne_gLa : gLb ≠ gLa := by decide
@[simp] theorem gLb_ne_gBw : gLb ≠ gBw := by decide
@[simp] theorem gLb_ne_gQ : gLb ≠ gQ := by decide
@[simp] theorem gLb_ne_gR : gLb ≠ gR := by decide
@[simp] theorem gLb_ne_gP : gLb ≠ gP := by decide
@[simp] theorem gLb_ne_gT : gLb ≠ gT := by decide
@[simp] theorem gLb_ne_gLt : gLb ≠ gLt := by decide
@[simp] theorem gLb_ne_gCnt : gLb ≠ gCnt := by decide
@[simp] theorem gLb_ne_gO : gLb ≠ gO := by decide
@[simp] theorem gLb_ne_gQz : gLb ≠ gQz := by decide
@[simp] theorem gLb_ne_gZi : gLb ≠ gZi := by decide
@[simp] theorem gBw_ne_gX : gBw ≠ gX := by decide
@[simp] theorem gBw_ne_gY : gBw ≠ gY := by decide
@[simp] theorem gBw_ne_gLa : gBw ≠ gLa := by decide
@[simp] theorem gBw_ne_gLb : gBw ≠ gLb := by decide
@[simp] theorem gBw_ne_gQ : gBw ≠ gQ := by decide
@[simp] theorem gBw_ne_gR : gBw ≠ gR := by decide
@[simp] theorem gBw_ne_gP : gBw ≠ gP := by decide
@[simp] theorem gBw_ne_gT : gBw ≠ gT := by decide
@[simp] theorem gBw_ne_gLt : gBw ≠ gLt := by decide
@[simp] theorem gBw_ne_gCnt : gBw ≠ gCnt := by decide
@[simp] theorem gBw_ne_gO : gBw ≠ gO := by decide
@[simp] theorem gBw_ne_gQz : gBw ≠ gQz := by decide
@[simp] theorem gBw_ne_gZi : gBw ≠ gZi := by decide
@[simp] theorem gQ_ne_gX : gQ ≠ gX := by decide
@[simp] theorem gQ_ne_gY : gQ ≠ gY := by decide
@[simp] theorem gQ_ne_gLa : gQ ≠ gLa := by decide
@[simp] theorem gQ_ne_gLb : gQ ≠ gLb := by decide
@[simp] theorem gQ_ne_gBw : gQ ≠ gBw := by decide
@[simp] theorem gQ_ne_gR : gQ ≠ gR := by decide
@[simp] theorem gQ_ne_gP : gQ ≠ gP := by decide
@[simp] theorem gQ_ne_gT : gQ ≠ gT := by decide
@[simp] theorem gQ_ne_gLt : gQ ≠ gLt := by decide
@[simp] theorem gQ_ne_gCnt : gQ ≠ gCnt := by decide
@[simp] theorem gQ_ne_gO : gQ ≠ gO := by decide
@[simp] theorem gQ_ne_gQz : gQ ≠ gQz := by decide
@[simp] theorem gQ_ne_gZi : gQ ≠ gZi := by decide
@[simp] theorem gR_ne_gX : gR ≠ gX := by decide
@[simp] theorem gR_ne_gY : gR ≠ gY := by decide
@[simp] theorem gR_ne_gLa : gR ≠ gLa := by decide
@[simp] theorem gR_ne_gLb : gR ≠ gLb := by decide
@[simp] theorem gR_ne_gBw : gR ≠ gBw := by decide
@[simp] theorem gR_ne_gQ : gR ≠ gQ := by decide
@[simp] theorem gR_ne_gP : gR ≠ gP := by decide
@[simp] theorem gR_ne_gT : gR ≠ gT := by decide
@[simp] theorem gR_ne_gLt : gR ≠ gLt := by decide
@[simp] theorem gR_ne_gCnt : gR ≠ gCnt := by decide
@[simp] theorem gR_ne_gO : gR ≠ gO := by decide
@[simp] theorem gR_ne_gQz : gR ≠ gQz := by decide
@[simp] theorem gR_ne_gZi : gR ≠ gZi := by decide
@[simp] theorem gP_ne_gX : gP ≠ gX := by decide
@[simp] theorem gP_ne_gY : gP ≠ gY := by decide
@[simp] theorem gP_ne_gLa : gP ≠ gLa := by decide
@[simp] theorem gP_ne_gLb : gP ≠ gLb := by decide
@[simp] theorem gP_ne_gBw : gP ≠ gBw := by decide
@[simp] theorem gP_ne_gQ : gP ≠ gQ := by decide
@[simp] theorem gP_ne_gR : gP ≠ gR := by decide
@[simp] theorem gP_ne_gT : gP ≠ gT := by decide
@[simp] theorem gP_ne_gLt : gP ≠ gLt := by decide
@[simp] theorem gP_ne_gCnt : gP ≠ gCnt := by decide
@[simp] theorem gP_ne_gO : gP ≠ gO := by decide
@[simp] theorem gP_ne_gQz : gP ≠ gQz := by decide
@[simp] theorem gP_ne_gZi : gP ≠ gZi := by decide
@[simp] theorem gT_ne_gX : gT ≠ gX := by decide
@[simp] theorem gT_ne_gY : gT ≠ gY := by decide
@[simp] theorem gT_ne_gLa : gT ≠ gLa := by decide
@[simp] theorem gT_ne_gLb : gT ≠ gLb := by decide
@[simp] theorem gT_ne_gBw : gT ≠ gBw := by decide
@[simp] theorem gT_ne_gQ : gT ≠ gQ := by decide
@[simp] theorem gT_ne_gR : gT ≠ gR := by decide
@[simp] theorem gT_ne_gP : gT ≠ gP := by decide
@[simp] theorem gT_ne_gLt : gT ≠ gLt := by decide
@[simp] theorem gT_ne_gCnt : gT ≠ gCnt := by decide
@[simp] theorem gT_ne_gO : gT ≠ gO := by decide
@[simp] theorem gT_ne_gQz : gT ≠ gQz := by decide
@[simp] theorem gT_ne_gZi : gT ≠ gZi := by decide
@[simp] theorem gLt_ne_gX : gLt ≠ gX := by decide
@[simp] theorem gLt_ne_gY : gLt ≠ gY := by decide
@[simp] theorem gLt_ne_gLa : gLt ≠ gLa := by decide
@[simp] theorem gLt_ne_gLb : gLt ≠ gLb := by decide
@[simp] theorem gLt_ne_gBw : gLt ≠ gBw := by decide
@[simp] theorem gLt_ne_gQ : gLt ≠ gQ := by decide
@[simp] theorem gLt_ne_gR : gLt ≠ gR := by decide
@[simp] theorem gLt_ne_gP : gLt ≠ gP := by decide
@[simp] theorem gLt_ne_gT : gLt ≠ gT := by decide
@[simp] theorem gLt_ne_gCnt : gLt ≠ gCnt := by decide
@[simp] theorem gLt_ne_gO : gLt ≠ gO := by decide
@[simp] theorem gLt_ne_gQz : gLt ≠ gQz := by decide
@[simp] theorem gLt_ne_gZi : gLt ≠ gZi := by decide
@[simp] theorem gCnt_ne_gX : gCnt ≠ gX := by decide
@[simp] theorem gCnt_ne_gY : gCnt ≠ gY := by decide
@[simp] theorem gCnt_ne_gLa : gCnt ≠ gLa := by decide
@[simp] theorem gCnt_ne_gLb : gCnt ≠ gLb := by decide
@[simp] theorem gCnt_ne_gBw : gCnt ≠ gBw := by decide
@[simp] theorem gCnt_ne_gQ : gCnt ≠ gQ := by decide
@[simp] theorem gCnt_ne_gR : gCnt ≠ gR := by decide
@[simp] theorem gCnt_ne_gP : gCnt ≠ gP := by decide
@[simp] theorem gCnt_ne_gT : gCnt ≠ gT := by decide
@[simp] theorem gCnt_ne_gLt : gCnt ≠ gLt := by decide
@[simp] theorem gCnt_ne_gO : gCnt ≠ gO := by decide
@[simp] theorem gCnt_ne_gQz : gCnt ≠ gQz := by decide
@[simp] theorem gCnt_ne_gZi : gCnt ≠ gZi := by decide
@[simp] theorem gO_ne_gX : gO ≠ gX := by decide
@[simp] theorem gO_ne_gY : gO ≠ gY := by decide
@[simp] theorem gO_ne_gLa : gO ≠ gLa := by decide
@[simp] theorem gO_ne_gLb : gO ≠ gLb := by decide
@[simp] theorem gO_ne_gBw : gO ≠ gBw := by decide
@[simp] theorem gO_ne_gQ : gO ≠ gQ := by decide
@[simp] theorem gO_ne_gR : gO ≠ gR := by decide
@[simp] theorem gO_ne_gP : gO ≠ gP := by decide
@[simp] theorem gO_ne_gT : gO ≠ gT := by decide
@[simp] theorem gO_ne_gLt : gO ≠ gLt := by decide
@[simp] theorem gO_ne_gCnt : gO ≠ gCnt := by decide
@[simp] theorem gO_ne_gQz : gO ≠ gQz := by decide
@[simp] theorem gO_ne_gZi : gO ≠ gZi := by decide
@[simp] theorem gQz_ne_gX : gQz ≠ gX := by decide
@[simp] theorem gQz_ne_gY : gQz ≠ gY := by decide
@[simp] theorem gQz_ne_gLa : gQz ≠ gLa := by decide
@[simp] theorem gQz_ne_gLb : gQz ≠ gLb := by decide
@[simp] theorem gQz_ne_gBw : gQz ≠ gBw := by decide
@[simp] theorem gQz_ne_gQ : gQz ≠ gQ := by decide
@[simp] theorem gQz_ne_gR : gQz ≠ gR := by decide
@[simp] theorem gQz_ne_gP : gQz ≠ gP := by decide
@[simp] theorem gQz_ne_gT : gQz ≠ gT := by decide
@[simp] theorem gQz_ne_gLt : gQz ≠ gLt := by decide
@[simp] theorem gQz_ne_gCnt : gQz ≠ gCnt := by decide
@[simp] theorem gQz_ne_gO : gQz ≠ gO := by decide
@[simp] theorem gQz_ne_gZi : gQz ≠ gZi := by decide
@[simp] theorem gZi_ne_gX : gZi ≠ gX := by decide
@[simp] theorem gZi_ne_gY : gZi ≠ gY := by decide
@[simp] theorem gZi_ne_gLa : gZi ≠ gLa := by decide
@[simp] theorem gZi_ne_gLb : gZi ≠ gLb := by decide
@[simp] theorem gZi_ne_gBw : gZi ≠ gBw := by decide
@[simp] theorem gZi_ne_gQ : gZi ≠ gQ := by decide
@[simp] theorem gZi_ne_gR : gZi ≠ gR := by decide
@[simp] theorem gZi_ne_gP : gZi ≠ gP := by decide
@[simp] theorem gZi_ne_gT : gZi ≠ gT := by decide
@[simp] theorem gZi_ne_gLt : gZi ≠ gLt := by decide
@[simp] theorem gZi_ne_gCnt : gZi ≠ gCnt := by decide
@[simp] theorem gZi_ne_gO : gZi ≠ gO := by decide
@[simp] theorem gZi_ne_gQz : gZi ≠ gQz := by decide
@[simp] theorem gX_ne_lFl : gX ≠ lFl := by decide
@[simp] theorem lFl_ne_gX : lFl ≠ gX := by decide
@[simp] theorem gX_ne_lDh : gX ≠ lDh := by decide
@[simp] theorem lDh_ne_gX : lDh ≠ gX := by decide
@[simp] theorem gX_ne_lDt : gX ≠ lDt := by decide
@[simp] theorem lDt_ne_gX : lDt ≠ gX := by decide
@[simp] theorem gX_ne_lDg : gX ≠ lDg := by decide
@[simp] theorem lDg_ne_gX : lDg ≠ gX := by decide
@[simp] theorem gX_ne_lDi : gX ≠ lDi := by decide
@[simp] theorem lDi_ne_gX : lDi ≠ gX := by decide
@[simp] theorem gX_ne_lRp : gX ≠ lRp := by decide
@[simp] theorem lRp_ne_gX : lRp ≠ gX := by decide
@[simp] theorem gX_ne_lRn : gX ≠ lRn := by decide
@[simp] theorem lRn_ne_gX : lRn ≠ gX := by decide
@[simp] theorem gX_ne_lFle : gX ≠ lFle := by decide
@[simp] theorem lFle_ne_gX : lFle ≠ gX := by decide
@[simp] theorem gX_ne_lDir : gX ≠ lDir := by decide
@[simp] theorem lDir_ne_gX : lDir ≠ gX := by decide
@[simp] theorem gX_ne_lFln : gX ≠ lFln := by decide
@[simp] theorem lFln_ne_gX : lFln ≠ gX := by decide
@[simp] theorem gX_ne_lFll : gX ≠ lFll := by decide
@[simp] theorem lFll_ne_gX : lFll ≠ gX := by decide
@[simp] theorem gX_ne_lFls : gX ≠ lFls := by decide
@[simp] theorem lFls_ne_gX : lFls ≠ gX := by decide
@[simp] theorem gX_ne_lKb : gX ≠ lKb := by decide
@[simp] theorem lKb_ne_gX : lKb ≠ gX := by decide
@[simp] theorem gX_ne_lSrc : gX ≠ lSrc := by decide
@[simp] theorem lSrc_ne_gX : lSrc ≠ gX := by decide
@[simp] theorem gX_ne_lDst : gX ≠ lDst := by decide
@[simp] theorem lDst_ne_gX : lDst ≠ gX := by decide
@[simp] theorem gX_ne_lCi : gX ≠ lCi := by decide
@[simp] theorem lCi_ne_gX : lCi ≠ gX := by decide
@[simp] theorem gX_ne_lCz : gX ≠ lCz := by decide
@[simp] theorem lCz_ne_gX : lCz ≠ gX := by decide
@[simp] theorem gX_ne_lCn : gX ≠ lCn := by decide
@[simp] theorem lCn_ne_gX : lCn ≠ gX := by decide
@[simp] theorem gY_ne_lFl : gY ≠ lFl := by decide
@[simp] theorem lFl_ne_gY : lFl ≠ gY := by decide
@[simp] theorem gY_ne_lDh : gY ≠ lDh := by decide
@[simp] theorem lDh_ne_gY : lDh ≠ gY := by decide
@[simp] theorem gY_ne_lDt : gY ≠ lDt := by decide
@[simp] theorem lDt_ne_gY : lDt ≠ gY := by decide
@[simp] theorem gY_ne_lDg : gY ≠ lDg := by decide
@[simp] theorem lDg_ne_gY : lDg ≠ gY := by decide
@[simp] theorem gY_ne_lDi : gY ≠ lDi := by decide
@[simp] theorem lDi_ne_gY : lDi ≠ gY := by decide
@[simp] theorem gY_ne_lRp : gY ≠ lRp := by decide
@[simp] theorem lRp_ne_gY : lRp ≠ gY := by decide
@[simp] theorem gY_ne_lRn : gY ≠ lRn := by decide
@[simp] theorem lRn_ne_gY : lRn ≠ gY := by decide
@[simp] theorem gY_ne_lFle : gY ≠ lFle := by decide
@[simp] theorem lFle_ne_gY : lFle ≠ gY := by decide
@[simp] theorem gY_ne_lDir : gY ≠ lDir := by decide
@[simp] theorem lDir_ne_gY : lDir ≠ gY := by decide
@[simp] theorem gY_ne_lFln : gY ≠ lFln := by decide
@[simp] theorem lFln_ne_gY : lFln ≠ gY := by decide
@[simp] theorem gY_ne_lFll : gY ≠ lFll := by decide
@[simp] theorem lFll_ne_gY : lFll ≠ gY := by decide
@[simp] theorem gY_ne_lFls : gY ≠ lFls := by decide
@[simp] theorem lFls_ne_gY : lFls ≠ gY := by decide
@[simp] theorem gY_ne_lKb : gY ≠ lKb := by decide
@[simp] theorem lKb_ne_gY : lKb ≠ gY := by decide
@[simp] theorem gY_ne_lSrc : gY ≠ lSrc := by decide
@[simp] theorem lSrc_ne_gY : lSrc ≠ gY := by decide
@[simp] theorem gY_ne_lDst : gY ≠ lDst := by decide
@[simp] theorem lDst_ne_gY : lDst ≠ gY := by decide
@[simp] theorem gY_ne_lCi : gY ≠ lCi := by decide
@[simp] theorem lCi_ne_gY : lCi ≠ gY := by decide
@[simp] theorem gY_ne_lCz : gY ≠ lCz := by decide
@[simp] theorem lCz_ne_gY : lCz ≠ gY := by decide
@[simp] theorem gY_ne_lCn : gY ≠ lCn := by decide
@[simp] theorem lCn_ne_gY : lCn ≠ gY := by decide
@[simp] theorem gLa_ne_lFl : gLa ≠ lFl := by decide
@[simp] theorem lFl_ne_gLa : lFl ≠ gLa := by decide
@[simp] theorem gLa_ne_lDh : gLa ≠ lDh := by decide
@[simp] theorem lDh_ne_gLa : lDh ≠ gLa := by decide
@[simp] theorem gLa_ne_lDt : gLa ≠ lDt := by decide
@[simp] theorem lDt_ne_gLa : lDt ≠ gLa := by decide
@[simp] theorem gLa_ne_lDg : gLa ≠ lDg := by decide
@[simp] theorem lDg_ne_gLa : lDg ≠ gLa := by decide
@[simp] theorem gLa_ne_lDi : gLa ≠ lDi := by decide
@[simp] theorem lDi_ne_gLa : lDi ≠ gLa := by decide
@[simp] theorem gLa_ne_lRp : gLa ≠ lRp := by decide
@[simp] theorem lRp_ne_gLa : lRp ≠ gLa := by decide
@[simp] theorem gLa_ne_lRn : gLa ≠ lRn := by decide
@[simp] theorem lRn_ne_gLa : lRn ≠ gLa := by decide
@[simp] theorem gLa_ne_lFle : gLa ≠ lFle := by decide
@[simp] theorem lFle_ne_gLa : lFle ≠ gLa := by decide
@[simp] theorem gLa_ne_lDir : gLa ≠ lDir := by decide
@[simp] theorem lDir_ne_gLa : lDir ≠ gLa := by decide
@[simp] theorem gLa_ne_lFln : gLa ≠ lFln := by decide
@[simp] theorem lFln_ne_gLa : lFln ≠ gLa := by decide
@[simp] theorem gLa_ne_lFll : gLa ≠ lFll := by decide
@[simp] theorem lFll_ne_gLa : lFll ≠ gLa := by decide
@[simp] theorem gLa_ne_lFls : gLa ≠ lFls := by decide
@[simp] theorem lFls_ne_gLa : lFls ≠ gLa := by decide
@[simp] theorem gLa_ne_lKb : gLa ≠ lKb := by decide
@[simp] theorem lKb_ne_gLa : lKb ≠ gLa := by decide
@[simp] theorem gLa_ne_lSrc : gLa ≠ lSrc := by decide
@[simp] theorem lSrc_ne_gLa : lSrc ≠ gLa := by decide
@[simp] theorem gLa_ne_lDst : gLa ≠ lDst := by decide
@[simp] theorem lDst_ne_gLa : lDst ≠ gLa := by decide
@[simp] theorem gLa_ne_lCi : gLa ≠ lCi := by decide
@[simp] theorem lCi_ne_gLa : lCi ≠ gLa := by decide
@[simp] theorem gLa_ne_lCz : gLa ≠ lCz := by decide
@[simp] theorem lCz_ne_gLa : lCz ≠ gLa := by decide
@[simp] theorem gLa_ne_lCn : gLa ≠ lCn := by decide
@[simp] theorem lCn_ne_gLa : lCn ≠ gLa := by decide
@[simp] theorem gLb_ne_lFl : gLb ≠ lFl := by decide
@[simp] theorem lFl_ne_gLb : lFl ≠ gLb := by decide
@[simp] theorem gLb_ne_lDh : gLb ≠ lDh := by decide
@[simp] theorem lDh_ne_gLb : lDh ≠ gLb := by decide
@[simp] theorem gLb_ne_lDt : gLb ≠ lDt := by decide
@[simp] theorem lDt_ne_gLb : lDt ≠ gLb := by decide
@[simp] theorem gLb_ne_lDg : gLb ≠ lDg := by decide
@[simp] theorem lDg_ne_gLb : lDg ≠ gLb := by decide
@[simp] theorem gLb_ne_lDi : gLb ≠ lDi := by decide
@[simp] theorem lDi_ne_gLb : lDi ≠ gLb := by decide
@[simp] theorem gLb_ne_lRp : gLb ≠ lRp := by decide
@[simp] theorem lRp_ne_gLb : lRp ≠ gLb := by decide
@[simp] theorem gLb_ne_lRn : gLb ≠ lRn := by decide
@[simp] theorem lRn_ne_gLb : lRn ≠ gLb := by decide
@[simp] theorem gLb_ne_lFle : gLb ≠ lFle := by decide
@[simp] theorem lFle_ne_gLb : lFle ≠ gLb := by decide
@[simp] theorem gLb_ne_lDir : gLb ≠ lDir := by decide
@[simp] theorem lDir_ne_gLb : lDir ≠ gLb := by decide
@[simp] theorem gLb_ne_lFln : gLb ≠ lFln := by decide
@[simp] theorem lFln_ne_gLb : lFln ≠ gLb := by decide
@[simp] theorem gLb_ne_lFll : gLb ≠ lFll := by decide
@[simp] theorem lFll_ne_gLb : lFll ≠ gLb := by decide
@[simp] theorem gLb_ne_lFls : gLb ≠ lFls := by decide
@[simp] theorem lFls_ne_gLb : lFls ≠ gLb := by decide
@[simp] theorem gLb_ne_lKb : gLb ≠ lKb := by decide
@[simp] theorem lKb_ne_gLb : lKb ≠ gLb := by decide
@[simp] theorem gLb_ne_lSrc : gLb ≠ lSrc := by decide
@[simp] theorem lSrc_ne_gLb : lSrc ≠ gLb := by decide
@[simp] theorem gLb_ne_lDst : gLb ≠ lDst := by decide
@[simp] theorem lDst_ne_gLb : lDst ≠ gLb := by decide
@[simp] theorem gLb_ne_lCi : gLb ≠ lCi := by decide
@[simp] theorem lCi_ne_gLb : lCi ≠ gLb := by decide
@[simp] theorem gLb_ne_lCz : gLb ≠ lCz := by decide
@[simp] theorem lCz_ne_gLb : lCz ≠ gLb := by decide
@[simp] theorem gLb_ne_lCn : gLb ≠ lCn := by decide
@[simp] theorem lCn_ne_gLb : lCn ≠ gLb := by decide
@[simp] theorem gBw_ne_lFl : gBw ≠ lFl := by decide
@[simp] theorem lFl_ne_gBw : lFl ≠ gBw := by decide
@[simp] theorem gBw_ne_lDh : gBw ≠ lDh := by decide
@[simp] theorem lDh_ne_gBw : lDh ≠ gBw := by decide
@[simp] theorem gBw_ne_lDt : gBw ≠ lDt := by decide
@[simp] theorem lDt_ne_gBw : lDt ≠ gBw := by decide
@[simp] theorem gBw_ne_lDg : gBw ≠ lDg := by decide
@[simp] theorem lDg_ne_gBw : lDg ≠ gBw := by decide
@[simp] theorem gBw_ne_lDi : gBw ≠ lDi := by decide
@[simp] theorem lDi_ne_gBw : lDi ≠ gBw := by decide
@[simp] theorem gBw_ne_lRp : gBw ≠ lRp := by decide
@[simp] theorem lRp_ne_gBw : lRp ≠ gBw := by decide
@[simp] theorem gBw_ne_lRn : gBw ≠ lRn := by decide
@[simp] theorem lRn_ne_gBw : lRn ≠ gBw := by decide
@[simp] theorem gBw_ne_lFle : gBw ≠ lFle := by decide
@[simp] theorem lFle_ne_gBw : lFle ≠ gBw := by decide
@[simp] theorem gBw_ne_lDir : gBw ≠ lDir := by decide
@[simp] theorem lDir_ne_gBw : lDir ≠ gBw := by decide
@[simp] theorem gBw_ne_lFln : gBw ≠ lFln := by decide
@[simp] theorem lFln_ne_gBw : lFln ≠ gBw := by decide
@[simp] theorem gBw_ne_lFll : gBw ≠ lFll := by decide
@[simp] theorem lFll_ne_gBw : lFll ≠ gBw := by decide
@[simp] theorem gBw_ne_lFls : gBw ≠ lFls := by decide
@[simp] theorem lFls_ne_gBw : lFls ≠ gBw := by decide
@[simp] theorem gBw_ne_lKb : gBw ≠ lKb := by decide
@[simp] theorem lKb_ne_gBw : lKb ≠ gBw := by decide
@[simp] theorem gBw_ne_lSrc : gBw ≠ lSrc := by decide
@[simp] theorem lSrc_ne_gBw : lSrc ≠ gBw := by decide
@[simp] theorem gBw_ne_lDst : gBw ≠ lDst := by decide
@[simp] theorem lDst_ne_gBw : lDst ≠ gBw := by decide
@[simp] theorem gBw_ne_lCi : gBw ≠ lCi := by decide
@[simp] theorem lCi_ne_gBw : lCi ≠ gBw := by decide
@[simp] theorem gBw_ne_lCz : gBw ≠ lCz := by decide
@[simp] theorem lCz_ne_gBw : lCz ≠ gBw := by decide
@[simp] theorem gBw_ne_lCn : gBw ≠ lCn := by decide
@[simp] theorem lCn_ne_gBw : lCn ≠ gBw := by decide
@[simp] theorem gQ_ne_lFl : gQ ≠ lFl := by decide
@[simp] theorem lFl_ne_gQ : lFl ≠ gQ := by decide
@[simp] theorem gQ_ne_lDh : gQ ≠ lDh := by decide
@[simp] theorem lDh_ne_gQ : lDh ≠ gQ := by decide
@[simp] theorem gQ_ne_lDt : gQ ≠ lDt := by decide
@[simp] theorem lDt_ne_gQ : lDt ≠ gQ := by decide
@[simp] theorem gQ_ne_lDg : gQ ≠ lDg := by decide
@[simp] theorem lDg_ne_gQ : lDg ≠ gQ := by decide
@[simp] theorem gQ_ne_lDi : gQ ≠ lDi := by decide
@[simp] theorem lDi_ne_gQ : lDi ≠ gQ := by decide
@[simp] theorem gQ_ne_lRp : gQ ≠ lRp := by decide
@[simp] theorem lRp_ne_gQ : lRp ≠ gQ := by decide
@[simp] theorem gQ_ne_lRn : gQ ≠ lRn := by decide
@[simp] theorem lRn_ne_gQ : lRn ≠ gQ := by decide
@[simp] theorem gQ_ne_lFle : gQ ≠ lFle := by decide
@[simp] theorem lFle_ne_gQ : lFle ≠ gQ := by decide
@[simp] theorem gQ_ne_lDir : gQ ≠ lDir := by decide
@[simp] theorem lDir_ne_gQ : lDir ≠ gQ := by decide
@[simp] theorem gQ_ne_lFln : gQ ≠ lFln := by decide
@[simp] theorem lFln_ne_gQ : lFln ≠ gQ := by decide
@[simp] theorem gQ_ne_lFll : gQ ≠ lFll := by decide
@[simp] theorem lFll_ne_gQ : lFll ≠ gQ := by decide
@[simp] theorem gQ_ne_lFls : gQ ≠ lFls := by decide
@[simp] theorem lFls_ne_gQ : lFls ≠ gQ := by decide
@[simp] theorem gQ_ne_lKb : gQ ≠ lKb := by decide
@[simp] theorem lKb_ne_gQ : lKb ≠ gQ := by decide
@[simp] theorem gQ_ne_lSrc : gQ ≠ lSrc := by decide
@[simp] theorem lSrc_ne_gQ : lSrc ≠ gQ := by decide
@[simp] theorem gQ_ne_lDst : gQ ≠ lDst := by decide
@[simp] theorem lDst_ne_gQ : lDst ≠ gQ := by decide
@[simp] theorem gQ_ne_lCi : gQ ≠ lCi := by decide
@[simp] theorem lCi_ne_gQ : lCi ≠ gQ := by decide
@[simp] theorem gQ_ne_lCz : gQ ≠ lCz := by decide
@[simp] theorem lCz_ne_gQ : lCz ≠ gQ := by decide
@[simp] theorem gQ_ne_lCn : gQ ≠ lCn := by decide
@[simp] theorem lCn_ne_gQ : lCn ≠ gQ := by decide
@[simp] theorem gR_ne_lFl : gR ≠ lFl := by decide
@[simp] theorem lFl_ne_gR : lFl ≠ gR := by decide
@[simp] theorem gR_ne_lDh : gR ≠ lDh := by decide
@[simp] theorem lDh_ne_gR : lDh ≠ gR := by decide
@[simp] theorem gR_ne_lDt : gR ≠ lDt := by decide
@[simp] theorem lDt_ne_gR : lDt ≠ gR := by decide
@[simp] theorem gR_ne_lDg : gR ≠ lDg := by decide
@[simp] theorem lDg_ne_gR : lDg ≠ gR := by decide
@[simp] theorem gR_ne_lDi : gR ≠ lDi := by decide
@[simp] theorem lDi_ne_gR : lDi ≠ gR := by decide
@[simp] theorem gR_ne_lRp : gR ≠ lRp := by decide
@[simp] theorem lRp_ne_gR : lRp ≠ gR := by decide
@[simp] theorem gR_ne_lRn : gR ≠ lRn := by decide
@[simp] theorem lRn_ne_gR : lRn ≠ gR := by decide
@[simp] theorem gR_ne_lFle : gR ≠ lFle := by decide
@[simp] theorem lFle_ne_gR : lFle ≠ gR := by decide
@[simp] theorem gR_ne_lDir : gR ≠ lDir := by decide
@[simp] theorem lDir_ne_gR : lDir ≠ gR := by decide
@[simp] theorem gR_ne_lFln : gR ≠ lFln := by decide
@[simp] theorem lFln_ne_gR : lFln ≠ gR := by decide
@[simp] theorem gR_ne_lFll : gR ≠ lFll := by decide
@[simp] theorem lFll_ne_gR : lFll ≠ gR := by decide
@[simp] theorem gR_ne_lFls : gR ≠ lFls := by decide
@[simp] theorem lFls_ne_gR : lFls ≠ gR := by decide
@[simp] theorem gR_ne_lKb : gR ≠ lKb := by decide
@[simp] theorem lKb_ne_gR : lKb ≠ gR := by decide
@[simp] theorem gR_ne_lSrc : gR ≠ lSrc := by decide
@[simp] theorem lSrc_ne_gR : lSrc ≠ gR := by decide
@[simp] theorem gR_ne_lDst : gR ≠ lDst := by decide
@[simp] theorem lDst_ne_gR : lDst ≠ gR := by decide
@[simp] theorem gR_ne_lCi : gR ≠ lCi := by decide
@[simp] theorem lCi_ne_gR : lCi ≠ gR := by decide
@[simp] theorem gR_ne_lCz : gR ≠ lCz := by decide
@[simp] theorem lCz_ne_gR : lCz ≠ gR := by decide
@[simp] theorem gR_ne_lCn : gR ≠ lCn := by decide
@[simp] theorem lCn_ne_gR : lCn ≠ gR := by decide
@[simp] theorem gP_ne_lFl : gP ≠ lFl := by decide
@[simp] theorem lFl_ne_gP : lFl ≠ gP := by decide
@[simp] theorem gP_ne_lDh : gP ≠ lDh := by decide
@[simp] theorem lDh_ne_gP : lDh ≠ gP := by decide
@[simp] theorem gP_ne_lDt : gP ≠ lDt := by decide
@[simp] theorem lDt_ne_gP : lDt ≠ gP := by decide
@[simp] theorem gP_ne_lDg : gP ≠ lDg := by decide
@[simp] theorem lDg_ne_gP : lDg ≠ gP := by decide
@[simp] theorem gP_ne_lDi : gP ≠ lDi := by decide
@[simp] theorem lDi_ne_gP : lDi ≠ gP := by decide
@[simp] theorem gP_ne_lRp : gP ≠ lRp := by decide
@[simp] theorem lRp_ne_gP : lRp ≠ gP := by decide
@[simp] theorem gP_ne_lRn : gP ≠ lRn := by decide
@[simp] theorem lRn_ne_gP : lRn ≠ gP := by decide
@[simp] theorem gP_ne_lFle : gP ≠ lFle := by decide
@[simp] theorem lFle_ne_gP : lFle ≠ gP := by decide
@[simp] theorem gP_ne_lDir : gP ≠ lDir := by decide
@[simp] theorem lDir_ne_gP : lDir ≠ gP := by decide
@[simp] theorem gP_ne_lFln : gP ≠ lFln := by decide
@[simp] theorem lFln_ne_gP : lFln ≠ gP := by decide
@[simp] theorem gP_ne_lFll : gP ≠ lFll := by decide
@[simp] theorem lFll_ne_gP : lFll ≠ gP := by decide
@[simp] theorem gP_ne_lFls : gP ≠ lFls := by decide
@[simp] theorem lFls_ne_gP : lFls ≠ gP := by decide
@[simp] theorem gP_ne_lKb : gP ≠ lKb := by decide
@[simp] theorem lKb_ne_gP : lKb ≠ gP := by decide
@[simp] theorem gP_ne_lSrc : gP ≠ lSrc := by decide
@[simp] theorem lSrc_ne_gP : lSrc ≠ gP := by decide
@[simp] theorem gP_ne_lDst : gP ≠ lDst := by decide
@[simp] theorem lDst_ne_gP : lDst ≠ gP := by decide
@[simp] theorem gP_ne_lCi : gP ≠ lCi := by decide
@[simp] theorem lCi_ne_gP : lCi ≠ gP := by decide
@[simp] theorem gP_ne_lCz : gP ≠ lCz := by decide
@[simp] theorem lCz_ne_gP : lCz ≠ gP := by decide
@[simp] theorem gP_ne_lCn : gP ≠ lCn := by decide
@[simp] theorem lCn_ne_gP : lCn ≠ gP := by decide
@[simp] theorem gT_ne_lFl : gT ≠ lFl := by decide
@[simp] theorem lFl_ne_gT : lFl ≠ gT := by decide
@[simp] theorem gT_ne_lDh : gT ≠ lDh := by decide
@[simp] theorem lDh_ne_gT : lDh ≠ gT := by decide
@[simp] theorem gT_ne_lDt : gT ≠ lDt := by decide
@[simp] theorem lDt_ne_gT : lDt ≠ gT := by decide
@[simp] theorem gT_ne_lDg : gT ≠ lDg := by decide
@[simp] theorem lDg_ne_gT : lDg ≠ gT := by decide
@[simp] theorem gT_ne_lDi : gT ≠ lDi := by decide
@[simp] theorem lDi_ne_gT : lDi ≠ gT := by decide
@[simp] theorem gT_ne_lRp : gT ≠ lRp := by decide
@[simp] theorem lRp_ne_gT : lRp ≠ gT := by decide
@[simp] theorem gT_ne_lRn : gT ≠ lRn := by decide
@[simp] theorem lRn_ne_gT : lRn ≠ gT := by decide
@[simp] theorem gT_ne_lFle : gT ≠ lFle := by decide
@[simp] theorem lFle_ne_gT : lFle ≠ gT := by decide
@[simp] theorem gT_ne_lDir : gT ≠ lDir := by decide
@[simp] theorem lDir_ne_gT : lDir ≠ gT := by decide
@[simp] theorem gT_ne_lFln : gT ≠ lFln := by decide
@[simp] theorem lFln_ne_gT : lFln ≠ gT := by decide
@[simp] theorem gT_ne_lFll : gT ≠ lFll := by decide
@[simp] theorem lFll_ne_gT : lFll ≠ gT := by decide
@[simp] theorem gT_ne_lFls : gT ≠ lFls := by decide
@[simp] theorem lFls_ne_gT : lFls ≠ gT := by decide
@[simp] theorem gT_ne_lKb : gT ≠ lKb := by decide
@[simp] theorem lKb_ne_gT : lKb ≠ gT := by decide
@[simp] theorem gT_ne_lSrc : gT ≠ lSrc := by decide
@[simp] theorem lSrc_ne_gT : lSrc ≠ gT := by decide
@[simp] theorem gT_ne_lDst : gT ≠ lDst := by decide
@[simp] theorem lDst_ne_gT : lDst ≠ gT := by decide
@[simp] theorem gT_ne_lCi : gT ≠ lCi := by decide
@[simp] theorem lCi_ne_gT : lCi ≠ gT := by decide
@[simp] theorem gT_ne_lCz : gT ≠ lCz := by decide
@[simp] theorem lCz_ne_gT : lCz ≠ gT := by decide
@[simp] theorem gT_ne_lCn : gT ≠ lCn := by decide
@[simp] theorem lCn_ne_gT : lCn ≠ gT := by decide
@[simp] theorem gLt_ne_lFl : gLt ≠ lFl := by decide
@[simp] theorem lFl_ne_gLt : lFl ≠ gLt := by decide
@[simp] theorem gLt_ne_lDh : gLt ≠ lDh := by decide
@[simp] theorem lDh_ne_gLt : lDh ≠ gLt := by decide
@[simp] theorem gLt_ne_lDt : gLt ≠ lDt := by decide
@[simp] theorem lDt_ne_gLt : lDt ≠ gLt := by decide
@[simp] theorem gLt_ne_lDg : gLt ≠ lDg := by decide
@[simp] theorem lDg_ne_gLt : lDg ≠ gLt := by decide
@[simp] theorem gLt_ne_lDi : gLt ≠ lDi := by decide
@[simp] theorem lDi_ne_gLt : lDi ≠ gLt := by decide
@[simp] theorem gLt_ne_lRp : gLt ≠ lRp := by decide
@[simp] theorem lRp_ne_gLt : lRp ≠ gLt := by decide
@[simp] theorem gLt_ne_lRn : gLt ≠ lRn := by decide
@[simp] theorem lRn_ne_gLt : lRn ≠ gLt := by decide
@[simp] theorem gLt_ne_lFle : gLt ≠ lFle := by decide
@[simp] theorem lFle_ne_gLt : lFle ≠ gLt := by decide
@[simp] theorem gLt_ne_lDir : gLt ≠ lDir := by decide
@[simp] theorem lDir_ne_gLt : lDir ≠ gLt := by decide
@[simp] theorem gLt_ne_lFln : gLt ≠ lFln := by decide
@[simp] theorem lFln_ne_gLt : lFln ≠ gLt := by decide
@[simp] theorem gLt_ne_lFll : gLt ≠ lFll := by decide
@[simp] theorem lFll_ne_gLt : lFll ≠ gLt := by decide
@[simp] theorem gLt_ne_lFls : gLt ≠ lFls := by decide
@[simp] theorem lFls_ne_gLt : lFls ≠ gLt := by decide
@[simp] theorem gLt_ne_lKb : gLt ≠ lKb := by decide
@[simp] theorem lKb_ne_gLt : lKb ≠ gLt := by decide
@[simp] theorem gLt_ne_lSrc : gLt ≠ lSrc := by decide
@[simp] theorem lSrc_ne_gLt : lSrc ≠ gLt := by decide
@[simp] theorem gLt_ne_lDst : gLt ≠ lDst := by decide
@[simp] theorem lDst_ne_gLt : lDst ≠ gLt := by decide
@[simp] theorem gLt_ne_lCi : gLt ≠ lCi := by decide
@[simp] theorem lCi_ne_gLt : lCi ≠ gLt := by decide
@[simp] theorem gLt_ne_lCz : gLt ≠ lCz := by decide
@[simp] theorem lCz_ne_gLt : lCz ≠ gLt := by decide
@[simp] theorem gLt_ne_lCn : gLt ≠ lCn := by decide
@[simp] theorem lCn_ne_gLt : lCn ≠ gLt := by decide
@[simp] theorem gCnt_ne_lFl : gCnt ≠ lFl := by decide
@[simp] theorem lFl_ne_gCnt : lFl ≠ gCnt := by decide
@[simp] theorem gCnt_ne_lDh : gCnt ≠ lDh := by decide
@[simp] theorem lDh_ne_gCnt : lDh ≠ gCnt := by decide
@[simp] theorem gCnt_ne_lDt : gCnt ≠ lDt := by decide
@[simp] theorem lDt_ne_gCnt : lDt ≠ gCnt := by decide
@[simp] theorem gCnt_ne_lDg : gCnt ≠ lDg := by decide
@[simp] theorem lDg_ne_gCnt : lDg ≠ gCnt := by decide
@[simp] theorem gCnt_ne_lDi : gCnt ≠ lDi := by decide
@[simp] theorem lDi_ne_gCnt : lDi ≠ gCnt := by decide
@[simp] theorem gCnt_ne_lRp : gCnt ≠ lRp := by decide
@[simp] theorem lRp_ne_gCnt : lRp ≠ gCnt := by decide
@[simp] theorem gCnt_ne_lRn : gCnt ≠ lRn := by decide
@[simp] theorem lRn_ne_gCnt : lRn ≠ gCnt := by decide
@[simp] theorem gCnt_ne_lFle : gCnt ≠ lFle := by decide
@[simp] theorem lFle_ne_gCnt : lFle ≠ gCnt := by decide
@[simp] theorem gCnt_ne_lDir : gCnt ≠ lDir := by decide
@[simp] theorem lDir_ne_gCnt : lDir ≠ gCnt := by decide
@[simp] theorem gCnt_ne_lFln : gCnt ≠ lFln := by decide
@[simp] theorem lFln_ne_gCnt : lFln ≠ gCnt := by decide
@[simp] theorem gCnt_ne_lFll : gCnt ≠ lFll := by decide
@[simp] theorem lFll_ne_gCnt : lFll ≠ gCnt := by decide
@[simp] theorem gCnt_ne_lFls : gCnt ≠ lFls := by decide
@[simp] theorem lFls_ne_gCnt : lFls ≠ gCnt := by decide
@[simp] theorem gCnt_ne_lKb : gCnt ≠ lKb := by decide
@[simp] theorem lKb_ne_gCnt : lKb ≠ gCnt := by decide
@[simp] theorem gCnt_ne_lSrc : gCnt ≠ lSrc := by decide
@[simp] theorem lSrc_ne_gCnt : lSrc ≠ gCnt := by decide
@[simp] theorem gCnt_ne_lDst : gCnt ≠ lDst := by decide
@[simp] theorem lDst_ne_gCnt : lDst ≠ gCnt := by decide
@[simp] theorem gCnt_ne_lCi : gCnt ≠ lCi := by decide
@[simp] theorem lCi_ne_gCnt : lCi ≠ gCnt := by decide
@[simp] theorem gCnt_ne_lCz : gCnt ≠ lCz := by decide
@[simp] theorem lCz_ne_gCnt : lCz ≠ gCnt := by decide
@[simp] theorem gCnt_ne_lCn : gCnt ≠ lCn := by decide
@[simp] theorem lCn_ne_gCnt : lCn ≠ gCnt := by decide
@[simp] theorem gO_ne_lFl : gO ≠ lFl := by decide
@[simp] theorem lFl_ne_gO : lFl ≠ gO := by decide
@[simp] theorem gO_ne_lDh : gO ≠ lDh := by decide
@[simp] theorem lDh_ne_gO : lDh ≠ gO := by decide
@[simp] theorem gO_ne_lDt : gO ≠ lDt := by decide
@[simp] theorem lDt_ne_gO : lDt ≠ gO := by decide
@[simp] theorem gO_ne_lDg : gO ≠ lDg := by decide
@[simp] theorem lDg_ne_gO : lDg ≠ gO := by decide
@[simp] theorem gO_ne_lDi : gO ≠ lDi := by decide
@[simp] theorem lDi_ne_gO : lDi ≠ gO := by decide
@[simp] theorem gO_ne_lRp : gO ≠ lRp := by decide
@[simp] theorem lRp_ne_gO : lRp ≠ gO := by decide
@[simp] theorem gO_ne_lRn : gO ≠ lRn := by decide
@[simp] theorem lRn_ne_gO : lRn ≠ gO := by decide
@[simp] theorem gO_ne_lFle : gO ≠ lFle := by decide
@[simp] theorem lFle_ne_gO : lFle ≠ gO := by decide
@[simp] theorem gO_ne_lDir : gO ≠ lDir := by decide
@[simp] theorem lDir_ne_gO : lDir ≠ gO := by decide
@[simp] theorem gO_ne_lFln : gO ≠ lFln := by decide
@[simp] theorem lFln_ne_gO : lFln ≠ gO := by decide
@[simp] theorem gO_ne_lFll : gO ≠ lFll := by decide
@[simp] theorem lFll_ne_gO : lFll ≠ gO := by decide
@[simp] theorem gO_ne_lFls : gO ≠ lFls := by decide
@[simp] theorem lFls_ne_gO : lFls ≠ gO := by decide
@[simp] theorem gO_ne_lKb : gO ≠ lKb := by decide
@[simp] theorem lKb_ne_gO : lKb ≠ gO := by decide
@[simp] theorem gO_ne_lSrc : gO ≠ lSrc := by decide
@[simp] theorem lSrc_ne_gO : lSrc ≠ gO := by decide
@[simp] theorem gO_ne_lDst : gO ≠ lDst := by decide
@[simp] theorem lDst_ne_gO : lDst ≠ gO := by decide
@[simp] theorem gO_ne_lCi : gO ≠ lCi := by decide
@[simp] theorem lCi_ne_gO : lCi ≠ gO := by decide
@[simp] theorem gO_ne_lCz : gO ≠ lCz := by decide
@[simp] theorem lCz_ne_gO : lCz ≠ gO := by decide
@[simp] theorem gO_ne_lCn : gO ≠ lCn := by decide
@[simp] theorem lCn_ne_gO : lCn ≠ gO := by decide
@[simp] theorem gQz_ne_lFl : gQz ≠ lFl := by decide
@[simp] theorem lFl_ne_gQz : lFl ≠ gQz := by decide
@[simp] theorem gQz_ne_lDh : gQz ≠ lDh := by decide
@[simp] theorem lDh_ne_gQz : lDh ≠ gQz := by decide
@[simp] theorem gQz_ne_lDt : gQz ≠ lDt := by decide
@[simp] theorem lDt_ne_gQz : lDt ≠ gQz := by decide
@[simp] theorem gQz_ne_lDg : gQz ≠ lDg := by decide
@[simp] theorem lDg_ne_gQz : lDg ≠ gQz := by decide
@[simp] theorem gQz_ne_lDi : gQz ≠ lDi := by decide
@[simp] theorem lDi_ne_gQz : lDi ≠ gQz := by decide
@[simp] theorem gQz_ne_lRp : gQz ≠ lRp := by decide
@[simp] theorem lRp_ne_gQz : lRp ≠ gQz := by decide
@[simp] theorem gQz_ne_lRn : gQz ≠ lRn := by decide
@[simp] theorem lRn_ne_gQz : lRn ≠ gQz := by decide
@[simp] theorem gQz_ne_lFle : gQz ≠ lFle := by decide
@[simp] theorem lFle_ne_gQz : lFle ≠ gQz := by decide
@[simp] theorem gQz_ne_lDir : gQz ≠ lDir := by decide
@[simp] theorem lDir_ne_gQz : lDir ≠ gQz := by decide
@[simp] theorem gQz_ne_lFln : gQz ≠ lFln := by decide
@[simp] theorem lFln_ne_gQz : lFln ≠ gQz := by decide
@[simp] theorem gQz_ne_lFll : gQz ≠ lFll := by decide
@[simp] theorem lFll_ne_gQz : lFll ≠ gQz := by decide
@[simp] theorem gQz_ne_lFls : gQz ≠ lFls := by decide
@[simp] theorem lFls_ne_gQz : lFls ≠ gQz := by decide
@[simp] theorem gQz_ne_lKb : gQz ≠ lKb := by decide
@[simp] theorem lKb_ne_gQz : lKb ≠ gQz := by decide
@[simp] theorem gQz_ne_lSrc : gQz ≠ lSrc := by decide
@[simp] theorem lSrc_ne_gQz : lSrc ≠ gQz := by decide
@[simp] theorem gQz_ne_lDst : gQz ≠ lDst := by decide
@[simp] theorem lDst_ne_gQz : lDst ≠ gQz := by decide
@[simp] theorem gQz_ne_lCi : gQz ≠ lCi := by decide
@[simp] theorem lCi_ne_gQz : lCi ≠ gQz := by decide
@[simp] theorem gQz_ne_lCz : gQz ≠ lCz := by decide
@[simp] theorem lCz_ne_gQz : lCz ≠ gQz := by decide
@[simp] theorem gQz_ne_lCn : gQz ≠ lCn := by decide
@[simp] theorem lCn_ne_gQz : lCn ≠ gQz := by decide
@[simp] theorem gZi_ne_lFl : gZi ≠ lFl := by decide
@[simp] theorem lFl_ne_gZi : lFl ≠ gZi := by decide
@[simp] theorem gZi_ne_lDh : gZi ≠ lDh := by decide
@[simp] theorem lDh_ne_gZi : lDh ≠ gZi := by decide
@[simp] theorem gZi_ne_lDt : gZi ≠ lDt := by decide
@[simp] theorem lDt_ne_gZi : lDt ≠ gZi := by decide
@[simp] theorem gZi_ne_lDg : gZi ≠ lDg := by decide
@[simp] theorem lDg_ne_gZi : lDg ≠ gZi := by decide
@[simp] theorem gZi_ne_lDi : gZi ≠ lDi := by decide
@[simp] theorem lDi_ne_gZi : lDi ≠ gZi := by decide
@[simp] theorem gZi_ne_lRp : gZi ≠ lRp := by decide
@[simp] theorem lRp_ne_gZi : lRp ≠ gZi := by decide
@[simp] theorem gZi_ne_lRn : gZi ≠ lRn := by decide
@[simp] theorem lRn_ne_gZi : lRn ≠ gZi := by decide
@[simp] theorem gZi_ne_lFle : gZi ≠ lFle := by decide
@[simp] theorem lFle_ne_gZi : lFle ≠ gZi := by decide
@[simp] theorem gZi_ne_lDir : gZi ≠ lDir := by decide
@[simp] theorem lDir_ne_gZi : lDir ≠ gZi := by decide
@[simp] theorem gZi_ne_lFln : gZi ≠ lFln := by decide
@[simp] theorem lFln_ne_gZi : lFln ≠ gZi := by decide
@[simp] theorem gZi_ne_lFll : gZi ≠ lFll := by decide
@[simp] theorem lFll_ne_gZi : lFll ≠ gZi := by decide
@[simp] theorem gZi_ne_lFls : gZi ≠ lFls := by decide
@[simp] theorem lFls_ne_gZi : lFls ≠ gZi := by decide
@[simp] theorem gZi_ne_lKb : gZi ≠ lKb := by decide
@[simp] theorem lKb_ne_gZi : lKb ≠ gZi := by decide
@[simp] theorem gZi_ne_lSrc : gZi ≠ lSrc := by decide
@[simp] theorem lSrc_ne_gZi : lSrc ≠ gZi := by decide
@[simp] theorem gZi_ne_lDst : gZi ≠ lDst := by decide
@[simp] theorem lDst_ne_gZi : lDst ≠ gZi := by decide
@[simp] theorem gZi_ne_lCi : gZi ≠ lCi := by decide
@[simp] theorem lCi_ne_gZi : lCi ≠ gZi := by decide
@[simp] theorem gZi_ne_lCz : gZi ≠ lCz := by decide
@[simp] theorem lCz_ne_gZi : lCz ≠ gZi := by decide
@[simp] theorem gZi_ne_lCn : gZi ≠ lCn := by decide
@[simp] theorem lCn_ne_gZi : lCn ≠ gZi := by decide

def fMul := ofString "bigMul"

def shlZero : ProgHOL 64 :=
  .while (.cmp .lower (vv gZi) (vv gQ))
    (.seq (.store (vv gQz) (.const 0))
    (.seq (.assign .local gQz (.op .add [vv gQz, .const 8]))
    (.assign .local gZi (.op .add [vv gZi, .const 1]))))

def shlMain (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local gBw (.load .one (.op .add [vv gY, .const 8])))
  (.seq (.assign .local gQ (.shift .lsr (vv gBw) (.const 6)))
  (.seq (.assign .local gR (.op .and [vv gBw, .const 63]))
  (allocP C gP (.const 16)
  (.seq (.store (vv gP) (.const 1))
  (.seq (.store (.op .add [vv gP, .const 8]) (.shift .lsl (.const 1) (vv gR)))
  (.seq (.call (some (some (.local, gT), none)) fMul [vv gX, vv gP])
  (.seq (.assign .local gLt (.load .one (vv gT)))
  (.seq (.assign .local gCnt (.op .add [vv gLt, vv gQ]))
  (allocP C gO (.panop .mul [.op .add [vv gCnt, .const 1], .const 8])
  (.seq (.store (vv gO) (vv gCnt))
  (.seq (.assign .local gQz (.op .add [vv gO, .const 8])) (.seq (.assign .local gZi (.const 0))
  (.seq shlZero
  (.seq (.assign .local lSrc (.op .add [vv gT, .const 8]))
  (.seq (.assign .local lDst (vv gQz)) (.seq (.assign .local lCi (.const 0))
  (.seq (.assign .local lCn (vv gLt))
  (.seq copyLoop (.return (vv gO))))))))))))))))))))

def shlCore (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local gLa (.load .one (vv gX)))
  (.seq (.assign .local gLb (.load .one (vv gY)))
  (.ite (.cmp .equal (vv gLa) (.const 0)) (.return (vv gX))
  (.ite (.cmp .equal (vv gLb) (.const 0)) (.return (vv gX)) (shlMain C))))

def shlLocals : List MlS := [gLa, gLb, gBw, gQ, gR, gP, gT, gLt, gCnt, gO, gQz, gZi, lSrc, lDst, lCi, lCz, lCn]
def shlParams : List MlS := [gX, gY]
def shlBody (C : Ctx) : ProgHOL 64 := prologue shlLocals (shlCore C)

theorem limbs_mul_pow (t q : Nat) (ht : t ≠ 0) : limbs (t * B ^ q) = List.replicate q 0 ++ limbs t := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hne : t * B ^ (q + 1) ≠ 0 := Nat.mul_ne_zero ht (Nat.pos_iff_ne_zero.mp (pow_pos' _))
    rw [limbs_pos hne, Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_mod_left, Nat.mul_div_cancel _ Bpos, ih]
    rfl

section
variable {σ : Type}

def shlGz (Γ0 : Env) (C : Ctx) (od i : Nat) : Env :=
  (gZi, BitVec.ofNat 64 i) :: (gQz, cellA C (od + 1 + i)) :: Γ0

theorem shl_zero {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ0 : Env} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (N : Nat) (B0 : List (BitVec 64)) (od : Nat)
    (hdst : od + 1 + N ≤ B0.length) (h61 : N < 2 ^ 61) (hD : gQz ∈ D ∧ gZi ∈ D)
    (hN : Γ0.get gQ = some (BitVec.ofNat 64 N))
    (hr : SpecR (Inv (ctxH C (fillI B0 (List.replicate N 0) (od + 1) N)) s (shlGz Γ0 C od N) [] D) rest s m R) :
    SpecR (Inv (ctxH C (fillI B0 (List.replicate N 0) (od + 1) 0)) s (shlGz Γ0 C od 0) [] D) (.seq shlZero rest) s m R := by
  obtain ⟨dq, di⟩ := hD
  have hl := fillI_length B0 (List.replicate N 0) (od + 1)
  refine specR_forI (σ := σ) (D := D) (M := []) _ _ rest N
    (fun i => ctxH C (fillI B0 (List.replicate N 0) (od + 1) i)) (shlGz Γ0 C od)
    (fun i hi => ⟨if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 i) (BitVec.ofNat 64 N)
      then 1 else 0, by simp [sev, shlGz, Env.get, hN], ?_⟩) (fun i hi => ?_) hr
  · have e := word_lt_iff i N (by unfold B; omega) (by unfold B; omega)
    by_cases h' : i < N
    · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e.mpr h', h']
    · have : ¬ BitVec.ofNat 64 i < BitVec.ofNat 64 N := fun x => h' (e.mp x)
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this, h']
  have hj : od + 1 + i < (ctxH C (fillI B0 (List.replicate N 0) (od + 1) i)).H.length := by
    show _ < (fillI _ _ _ _).length; rw [hl]; omega
  refine step_seq (step_heapStoreI (ctxOK_H hok _) (vv gQz) (.const 0) _ hj 0 (by simp [shlGz]; rfl) rfl) ?_
  change Step (Inv (ctxH C ((fillI B0 (List.replicate N 0) (od + 1) i).set (od + 1 + i) 0)) s _ [] D) _ _
  rw [fillI_succ_eq _ _ _ _ _ (by simp [hi])]
  refine step_seq (step_assignI gQz _ (cellA C (od + 1 + i + 1)) dq (by simp [sev, shlGz]; exact cellA_add8 C _)) ?_
  refine step_mono (step_assignI gZi _ (BitVec.ofNat 64 (i + 1)) di (by simp [sev, shlGz]; exact word_add1_eq i))
    (fun _ h => h) (fun t ht => inv_envMono ht (fun z v hz => ?_))
  simp only [shlGz, Env.get_cons] at hz ⊢
  by_cases e1 : z = gZi
  · subst e1; simp_all
  by_cases e2 : z = gQz
  · subst e2; simp_all [Nat.add_assoc]
  simp [e1, e2] at hz ⊢; exact hz


theorem shl_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ shlLocals → (ctxEnv C ++ shlParams.zip vals).get x = none :=
  Knot.params_none C shlLocals shlParams vals (by decide) (by decide)

theorem limbs_two_pow (r : Nat) (hr : r < 64) : limbs (2 ^ r) = [BitVec.ofNat 64 (2 ^ r)] := by
  have h1 : 2 ^ r < B := Nat.pow_lt_pow_right (by decide) hr
  rw [limbs_pos (Nat.pos_iff_ne_zero.mp (Nat.pow_pos (by decide))), Nat.mod_eq_of_lt h1, Nat.div_eq_of_lt h1, limbs_zero]

theorem shl_spec (C : Ctx) (hok : CtxOK C) (s : AState) (a b : Nat) (oa ob : Nat)
    (hcm : C.code.lookup fMul = some (mulParams.map (fun p => (p, ShapeHOL.one)), mulBody C, .one))
    (hba : BlkAt C.H oa (limbs a)) (hbb : BlkAt C.H ob (limbs b)) (hb1 : (limbs b).length ≤ 1) :
    SpecR (σ := σ) (Pre C s (shlParams.zip [cellA C oa, cellA C ob])) (shlBody C) s (pure (a <<< b) : AM Nat)
      (PostH C s) := by
  refine specR_prologue (postH_locals C s) (shl_none C _) ?_
  unfold shlCore
  have hla0 : C.H[oa]? = some (BitVec.ofNat 64 (limbs a).length) := by simpa using hba.1
  have hlb0 : C.H[ob]? = some (BitVec.ofNat 64 (limbs b).length) := by simpa using hbb.1
  refine UD.specR_heapLoadI' gLa (vv gX) oa _ hla0 (by decide) (by simp +decide [Env.get, shlParams, ctxEnv]) ?_
  refine UD.specR_heapLoadI' gLb (vv gY) ob _ hlb0 (by decide) (by simp +decide [Env.get, shlParams, ctxEnv]) ?_
  refine specR_atEntry fun t0 ht0 => ?_
  obtain ⟨H0, hp0, ha0⟩ := ht0.sr.heap
  have hbl := blkAt_len hba
  have hbl2 := blkAt_len hbb
  have hcap := hok.heapCap
  have hlen0 := ha0.len
  have hp0l := hp0.length_le
  have hla58 : (limbs a).length < 2 ^ 58 := by omega
  by_cases ha0' : (limbs a).length = 0
  · have haz : a = 0 := by have := (limbs_length_lt_iff a 0).mp (by omega); simpa using this
    refine specR_ifI _ 1 (by simp [sev, Env.get, ha0', Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    refine specR_returnI _ (cellA C oa) (by simp +decide [Env.get, shlParams, ctxEnv]) (fun t ht => ?_)
    rw [haz, Nat.zero_shiftLeft]
    exact ⟨C.H, oa, List.prefix_refl _, rfl, by rw [← haz]; exact hba, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
  have haw : BitVec.ofNat 64 (limbs a).length ≠ 0 := fun e => ha0' (by
    have := congrArg BitVec.toNat e; simp at this; omega)
  refine specR_ifI _ 0 (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact haw)
    (fun h => absurd rfl h) (fun _ => ?_)
  by_cases hb0 : (limbs b).length = 0
  · have hbz : b = 0 := by have := (limbs_length_lt_iff b 0).mp (by omega); simpa using this
    refine specR_ifI _ 1 (by simp [sev, Env.get, hb0, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    refine specR_returnI _ (cellA C oa) (by simp +decide [Env.get, shlParams, ctxEnv]) (fun t ht => ?_)
    rw [hbz, Nat.shiftLeft_zero]
    exact ⟨C.H, oa, List.prefix_refl _, rfl, hba, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
  have hbw0 : BitVec.ofNat 64 (limbs b).length ≠ 0 := fun e => hb0 (by
    have := congrArg BitVec.toNat e; simp at this; omega)
  refine specR_ifI _ 0 (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hbw0)
    (fun h => absurd rfl h) (fun _ => ?_)
  sorry

end

end ConPanqueque.T.Big
