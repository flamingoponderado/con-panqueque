import ConPanqueque.T.Big.Mul
import ConPanqueque.T.Big.ShiftMath
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `Nat.shiftRight`

`shr(a, b)`: `b = 0` answers `a`; `b ≥ 2^64`, or `b / 64 ≥ |a|`, answers `0`; otherwise limb `k` of the result
is limb `k + q` shifted down by `r` plus limb `k + q + 1` shifted up by `64 - r` (`b = 64 q + r`), then the
canonical length by a counted scan.
-/

namespace ConPanqueque.T.Big

open ConPanqueque.T ConPanqueque.T.Ex
open ConPanqueque.V.Enc

def rX := ofString "rx"
def rY := ofString "ry"
def rLa := ofString "rla"
def rLb := ofString "rlb"
def rBw := ofString "rbw"
def rQ := ofString "rq"
def rR := ofString "rr"
def rR2 := ofString "rr2"
def rCnt := ofString "rcnt"
def rNm1 := ofString "rnm1"
def rO := ofString "ro"
def rQa := ofString "rqa"
def rQo := ofString "rqo"
def rU := ofString "ru"
def rV := ofString "rv"
def rT1 := ofString "rt1"
def rT2 := ofString "rt2"
def rD := ofString "rd"
def rI := ofString "ri"
def rK := ofString "rk"
def rL := ofString "rl"
def rZ := ofString "rz"

@[simp] theorem rX_ne_rY : rX ≠ rY := by decide
@[simp] theorem rX_ne_rLa : rX ≠ rLa := by decide
@[simp] theorem rX_ne_rLb : rX ≠ rLb := by decide
@[simp] theorem rX_ne_rBw : rX ≠ rBw := by decide
@[simp] theorem rX_ne_rQ : rX ≠ rQ := by decide
@[simp] theorem rX_ne_rR : rX ≠ rR := by decide
@[simp] theorem rX_ne_rR2 : rX ≠ rR2 := by decide
@[simp] theorem rX_ne_rCnt : rX ≠ rCnt := by decide
@[simp] theorem rX_ne_rNm1 : rX ≠ rNm1 := by decide
@[simp] theorem rX_ne_rO : rX ≠ rO := by decide
@[simp] theorem rX_ne_rQa : rX ≠ rQa := by decide
@[simp] theorem rX_ne_rQo : rX ≠ rQo := by decide
@[simp] theorem rX_ne_rU : rX ≠ rU := by decide
@[simp] theorem rX_ne_rV : rX ≠ rV := by decide
@[simp] theorem rX_ne_rT1 : rX ≠ rT1 := by decide
@[simp] theorem rX_ne_rT2 : rX ≠ rT2 := by decide
@[simp] theorem rX_ne_rD : rX ≠ rD := by decide
@[simp] theorem rX_ne_rI : rX ≠ rI := by decide
@[simp] theorem rX_ne_rK : rX ≠ rK := by decide
@[simp] theorem rX_ne_rL : rX ≠ rL := by decide
@[simp] theorem rX_ne_rZ : rX ≠ rZ := by decide
@[simp] theorem rY_ne_rX : rY ≠ rX := by decide
@[simp] theorem rY_ne_rLa : rY ≠ rLa := by decide
@[simp] theorem rY_ne_rLb : rY ≠ rLb := by decide
@[simp] theorem rY_ne_rBw : rY ≠ rBw := by decide
@[simp] theorem rY_ne_rQ : rY ≠ rQ := by decide
@[simp] theorem rY_ne_rR : rY ≠ rR := by decide
@[simp] theorem rY_ne_rR2 : rY ≠ rR2 := by decide
@[simp] theorem rY_ne_rCnt : rY ≠ rCnt := by decide
@[simp] theorem rY_ne_rNm1 : rY ≠ rNm1 := by decide
@[simp] theorem rY_ne_rO : rY ≠ rO := by decide
@[simp] theorem rY_ne_rQa : rY ≠ rQa := by decide
@[simp] theorem rY_ne_rQo : rY ≠ rQo := by decide
@[simp] theorem rY_ne_rU : rY ≠ rU := by decide
@[simp] theorem rY_ne_rV : rY ≠ rV := by decide
@[simp] theorem rY_ne_rT1 : rY ≠ rT1 := by decide
@[simp] theorem rY_ne_rT2 : rY ≠ rT2 := by decide
@[simp] theorem rY_ne_rD : rY ≠ rD := by decide
@[simp] theorem rY_ne_rI : rY ≠ rI := by decide
@[simp] theorem rY_ne_rK : rY ≠ rK := by decide
@[simp] theorem rY_ne_rL : rY ≠ rL := by decide
@[simp] theorem rY_ne_rZ : rY ≠ rZ := by decide
@[simp] theorem rLa_ne_rX : rLa ≠ rX := by decide
@[simp] theorem rLa_ne_rY : rLa ≠ rY := by decide
@[simp] theorem rLa_ne_rLb : rLa ≠ rLb := by decide
@[simp] theorem rLa_ne_rBw : rLa ≠ rBw := by decide
@[simp] theorem rLa_ne_rQ : rLa ≠ rQ := by decide
@[simp] theorem rLa_ne_rR : rLa ≠ rR := by decide
@[simp] theorem rLa_ne_rR2 : rLa ≠ rR2 := by decide
@[simp] theorem rLa_ne_rCnt : rLa ≠ rCnt := by decide
@[simp] theorem rLa_ne_rNm1 : rLa ≠ rNm1 := by decide
@[simp] theorem rLa_ne_rO : rLa ≠ rO := by decide
@[simp] theorem rLa_ne_rQa : rLa ≠ rQa := by decide
@[simp] theorem rLa_ne_rQo : rLa ≠ rQo := by decide
@[simp] theorem rLa_ne_rU : rLa ≠ rU := by decide
@[simp] theorem rLa_ne_rV : rLa ≠ rV := by decide
@[simp] theorem rLa_ne_rT1 : rLa ≠ rT1 := by decide
@[simp] theorem rLa_ne_rT2 : rLa ≠ rT2 := by decide
@[simp] theorem rLa_ne_rD : rLa ≠ rD := by decide
@[simp] theorem rLa_ne_rI : rLa ≠ rI := by decide
@[simp] theorem rLa_ne_rK : rLa ≠ rK := by decide
@[simp] theorem rLa_ne_rL : rLa ≠ rL := by decide
@[simp] theorem rLa_ne_rZ : rLa ≠ rZ := by decide
@[simp] theorem rLb_ne_rX : rLb ≠ rX := by decide
@[simp] theorem rLb_ne_rY : rLb ≠ rY := by decide
@[simp] theorem rLb_ne_rLa : rLb ≠ rLa := by decide
@[simp] theorem rLb_ne_rBw : rLb ≠ rBw := by decide
@[simp] theorem rLb_ne_rQ : rLb ≠ rQ := by decide
@[simp] theorem rLb_ne_rR : rLb ≠ rR := by decide
@[simp] theorem rLb_ne_rR2 : rLb ≠ rR2 := by decide
@[simp] theorem rLb_ne_rCnt : rLb ≠ rCnt := by decide
@[simp] theorem rLb_ne_rNm1 : rLb ≠ rNm1 := by decide
@[simp] theorem rLb_ne_rO : rLb ≠ rO := by decide
@[simp] theorem rLb_ne_rQa : rLb ≠ rQa := by decide
@[simp] theorem rLb_ne_rQo : rLb ≠ rQo := by decide
@[simp] theorem rLb_ne_rU : rLb ≠ rU := by decide
@[simp] theorem rLb_ne_rV : rLb ≠ rV := by decide
@[simp] theorem rLb_ne_rT1 : rLb ≠ rT1 := by decide
@[simp] theorem rLb_ne_rT2 : rLb ≠ rT2 := by decide
@[simp] theorem rLb_ne_rD : rLb ≠ rD := by decide
@[simp] theorem rLb_ne_rI : rLb ≠ rI := by decide
@[simp] theorem rLb_ne_rK : rLb ≠ rK := by decide
@[simp] theorem rLb_ne_rL : rLb ≠ rL := by decide
@[simp] theorem rLb_ne_rZ : rLb ≠ rZ := by decide
@[simp] theorem rBw_ne_rX : rBw ≠ rX := by decide
@[simp] theorem rBw_ne_rY : rBw ≠ rY := by decide
@[simp] theorem rBw_ne_rLa : rBw ≠ rLa := by decide
@[simp] theorem rBw_ne_rLb : rBw ≠ rLb := by decide
@[simp] theorem rBw_ne_rQ : rBw ≠ rQ := by decide
@[simp] theorem rBw_ne_rR : rBw ≠ rR := by decide
@[simp] theorem rBw_ne_rR2 : rBw ≠ rR2 := by decide
@[simp] theorem rBw_ne_rCnt : rBw ≠ rCnt := by decide
@[simp] theorem rBw_ne_rNm1 : rBw ≠ rNm1 := by decide
@[simp] theorem rBw_ne_rO : rBw ≠ rO := by decide
@[simp] theorem rBw_ne_rQa : rBw ≠ rQa := by decide
@[simp] theorem rBw_ne_rQo : rBw ≠ rQo := by decide
@[simp] theorem rBw_ne_rU : rBw ≠ rU := by decide
@[simp] theorem rBw_ne_rV : rBw ≠ rV := by decide
@[simp] theorem rBw_ne_rT1 : rBw ≠ rT1 := by decide
@[simp] theorem rBw_ne_rT2 : rBw ≠ rT2 := by decide
@[simp] theorem rBw_ne_rD : rBw ≠ rD := by decide
@[simp] theorem rBw_ne_rI : rBw ≠ rI := by decide
@[simp] theorem rBw_ne_rK : rBw ≠ rK := by decide
@[simp] theorem rBw_ne_rL : rBw ≠ rL := by decide
@[simp] theorem rBw_ne_rZ : rBw ≠ rZ := by decide
@[simp] theorem rQ_ne_rX : rQ ≠ rX := by decide
@[simp] theorem rQ_ne_rY : rQ ≠ rY := by decide
@[simp] theorem rQ_ne_rLa : rQ ≠ rLa := by decide
@[simp] theorem rQ_ne_rLb : rQ ≠ rLb := by decide
@[simp] theorem rQ_ne_rBw : rQ ≠ rBw := by decide
@[simp] theorem rQ_ne_rR : rQ ≠ rR := by decide
@[simp] theorem rQ_ne_rR2 : rQ ≠ rR2 := by decide
@[simp] theorem rQ_ne_rCnt : rQ ≠ rCnt := by decide
@[simp] theorem rQ_ne_rNm1 : rQ ≠ rNm1 := by decide
@[simp] theorem rQ_ne_rO : rQ ≠ rO := by decide
@[simp] theorem rQ_ne_rQa : rQ ≠ rQa := by decide
@[simp] theorem rQ_ne_rQo : rQ ≠ rQo := by decide
@[simp] theorem rQ_ne_rU : rQ ≠ rU := by decide
@[simp] theorem rQ_ne_rV : rQ ≠ rV := by decide
@[simp] theorem rQ_ne_rT1 : rQ ≠ rT1 := by decide
@[simp] theorem rQ_ne_rT2 : rQ ≠ rT2 := by decide
@[simp] theorem rQ_ne_rD : rQ ≠ rD := by decide
@[simp] theorem rQ_ne_rI : rQ ≠ rI := by decide
@[simp] theorem rQ_ne_rK : rQ ≠ rK := by decide
@[simp] theorem rQ_ne_rL : rQ ≠ rL := by decide
@[simp] theorem rQ_ne_rZ : rQ ≠ rZ := by decide
@[simp] theorem rR_ne_rX : rR ≠ rX := by decide
@[simp] theorem rR_ne_rY : rR ≠ rY := by decide
@[simp] theorem rR_ne_rLa : rR ≠ rLa := by decide
@[simp] theorem rR_ne_rLb : rR ≠ rLb := by decide
@[simp] theorem rR_ne_rBw : rR ≠ rBw := by decide
@[simp] theorem rR_ne_rQ : rR ≠ rQ := by decide
@[simp] theorem rR_ne_rR2 : rR ≠ rR2 := by decide
@[simp] theorem rR_ne_rCnt : rR ≠ rCnt := by decide
@[simp] theorem rR_ne_rNm1 : rR ≠ rNm1 := by decide
@[simp] theorem rR_ne_rO : rR ≠ rO := by decide
@[simp] theorem rR_ne_rQa : rR ≠ rQa := by decide
@[simp] theorem rR_ne_rQo : rR ≠ rQo := by decide
@[simp] theorem rR_ne_rU : rR ≠ rU := by decide
@[simp] theorem rR_ne_rV : rR ≠ rV := by decide
@[simp] theorem rR_ne_rT1 : rR ≠ rT1 := by decide
@[simp] theorem rR_ne_rT2 : rR ≠ rT2 := by decide
@[simp] theorem rR_ne_rD : rR ≠ rD := by decide
@[simp] theorem rR_ne_rI : rR ≠ rI := by decide
@[simp] theorem rR_ne_rK : rR ≠ rK := by decide
@[simp] theorem rR_ne_rL : rR ≠ rL := by decide
@[simp] theorem rR_ne_rZ : rR ≠ rZ := by decide
@[simp] theorem rR2_ne_rX : rR2 ≠ rX := by decide
@[simp] theorem rR2_ne_rY : rR2 ≠ rY := by decide
@[simp] theorem rR2_ne_rLa : rR2 ≠ rLa := by decide
@[simp] theorem rR2_ne_rLb : rR2 ≠ rLb := by decide
@[simp] theorem rR2_ne_rBw : rR2 ≠ rBw := by decide
@[simp] theorem rR2_ne_rQ : rR2 ≠ rQ := by decide
@[simp] theorem rR2_ne_rR : rR2 ≠ rR := by decide
@[simp] theorem rR2_ne_rCnt : rR2 ≠ rCnt := by decide
@[simp] theorem rR2_ne_rNm1 : rR2 ≠ rNm1 := by decide
@[simp] theorem rR2_ne_rO : rR2 ≠ rO := by decide
@[simp] theorem rR2_ne_rQa : rR2 ≠ rQa := by decide
@[simp] theorem rR2_ne_rQo : rR2 ≠ rQo := by decide
@[simp] theorem rR2_ne_rU : rR2 ≠ rU := by decide
@[simp] theorem rR2_ne_rV : rR2 ≠ rV := by decide
@[simp] theorem rR2_ne_rT1 : rR2 ≠ rT1 := by decide
@[simp] theorem rR2_ne_rT2 : rR2 ≠ rT2 := by decide
@[simp] theorem rR2_ne_rD : rR2 ≠ rD := by decide
@[simp] theorem rR2_ne_rI : rR2 ≠ rI := by decide
@[simp] theorem rR2_ne_rK : rR2 ≠ rK := by decide
@[simp] theorem rR2_ne_rL : rR2 ≠ rL := by decide
@[simp] theorem rR2_ne_rZ : rR2 ≠ rZ := by decide
@[simp] theorem rCnt_ne_rX : rCnt ≠ rX := by decide
@[simp] theorem rCnt_ne_rY : rCnt ≠ rY := by decide
@[simp] theorem rCnt_ne_rLa : rCnt ≠ rLa := by decide
@[simp] theorem rCnt_ne_rLb : rCnt ≠ rLb := by decide
@[simp] theorem rCnt_ne_rBw : rCnt ≠ rBw := by decide
@[simp] theorem rCnt_ne_rQ : rCnt ≠ rQ := by decide
@[simp] theorem rCnt_ne_rR : rCnt ≠ rR := by decide
@[simp] theorem rCnt_ne_rR2 : rCnt ≠ rR2 := by decide
@[simp] theorem rCnt_ne_rNm1 : rCnt ≠ rNm1 := by decide
@[simp] theorem rCnt_ne_rO : rCnt ≠ rO := by decide
@[simp] theorem rCnt_ne_rQa : rCnt ≠ rQa := by decide
@[simp] theorem rCnt_ne_rQo : rCnt ≠ rQo := by decide
@[simp] theorem rCnt_ne_rU : rCnt ≠ rU := by decide
@[simp] theorem rCnt_ne_rV : rCnt ≠ rV := by decide
@[simp] theorem rCnt_ne_rT1 : rCnt ≠ rT1 := by decide
@[simp] theorem rCnt_ne_rT2 : rCnt ≠ rT2 := by decide
@[simp] theorem rCnt_ne_rD : rCnt ≠ rD := by decide
@[simp] theorem rCnt_ne_rI : rCnt ≠ rI := by decide
@[simp] theorem rCnt_ne_rK : rCnt ≠ rK := by decide
@[simp] theorem rCnt_ne_rL : rCnt ≠ rL := by decide
@[simp] theorem rCnt_ne_rZ : rCnt ≠ rZ := by decide
@[simp] theorem rNm1_ne_rX : rNm1 ≠ rX := by decide
@[simp] theorem rNm1_ne_rY : rNm1 ≠ rY := by decide
@[simp] theorem rNm1_ne_rLa : rNm1 ≠ rLa := by decide
@[simp] theorem rNm1_ne_rLb : rNm1 ≠ rLb := by decide
@[simp] theorem rNm1_ne_rBw : rNm1 ≠ rBw := by decide
@[simp] theorem rNm1_ne_rQ : rNm1 ≠ rQ := by decide
@[simp] theorem rNm1_ne_rR : rNm1 ≠ rR := by decide
@[simp] theorem rNm1_ne_rR2 : rNm1 ≠ rR2 := by decide
@[simp] theorem rNm1_ne_rCnt : rNm1 ≠ rCnt := by decide
@[simp] theorem rNm1_ne_rO : rNm1 ≠ rO := by decide
@[simp] theorem rNm1_ne_rQa : rNm1 ≠ rQa := by decide
@[simp] theorem rNm1_ne_rQo : rNm1 ≠ rQo := by decide
@[simp] theorem rNm1_ne_rU : rNm1 ≠ rU := by decide
@[simp] theorem rNm1_ne_rV : rNm1 ≠ rV := by decide
@[simp] theorem rNm1_ne_rT1 : rNm1 ≠ rT1 := by decide
@[simp] theorem rNm1_ne_rT2 : rNm1 ≠ rT2 := by decide
@[simp] theorem rNm1_ne_rD : rNm1 ≠ rD := by decide
@[simp] theorem rNm1_ne_rI : rNm1 ≠ rI := by decide
@[simp] theorem rNm1_ne_rK : rNm1 ≠ rK := by decide
@[simp] theorem rNm1_ne_rL : rNm1 ≠ rL := by decide
@[simp] theorem rNm1_ne_rZ : rNm1 ≠ rZ := by decide
@[simp] theorem rO_ne_rX : rO ≠ rX := by decide
@[simp] theorem rO_ne_rY : rO ≠ rY := by decide
@[simp] theorem rO_ne_rLa : rO ≠ rLa := by decide
@[simp] theorem rO_ne_rLb : rO ≠ rLb := by decide
@[simp] theorem rO_ne_rBw : rO ≠ rBw := by decide
@[simp] theorem rO_ne_rQ : rO ≠ rQ := by decide
@[simp] theorem rO_ne_rR : rO ≠ rR := by decide
@[simp] theorem rO_ne_rR2 : rO ≠ rR2 := by decide
@[simp] theorem rO_ne_rCnt : rO ≠ rCnt := by decide
@[simp] theorem rO_ne_rNm1 : rO ≠ rNm1 := by decide
@[simp] theorem rO_ne_rQa : rO ≠ rQa := by decide
@[simp] theorem rO_ne_rQo : rO ≠ rQo := by decide
@[simp] theorem rO_ne_rU : rO ≠ rU := by decide
@[simp] theorem rO_ne_rV : rO ≠ rV := by decide
@[simp] theorem rO_ne_rT1 : rO ≠ rT1 := by decide
@[simp] theorem rO_ne_rT2 : rO ≠ rT2 := by decide
@[simp] theorem rO_ne_rD : rO ≠ rD := by decide
@[simp] theorem rO_ne_rI : rO ≠ rI := by decide
@[simp] theorem rO_ne_rK : rO ≠ rK := by decide
@[simp] theorem rO_ne_rL : rO ≠ rL := by decide
@[simp] theorem rO_ne_rZ : rO ≠ rZ := by decide
@[simp] theorem rQa_ne_rX : rQa ≠ rX := by decide
@[simp] theorem rQa_ne_rY : rQa ≠ rY := by decide
@[simp] theorem rQa_ne_rLa : rQa ≠ rLa := by decide
@[simp] theorem rQa_ne_rLb : rQa ≠ rLb := by decide
@[simp] theorem rQa_ne_rBw : rQa ≠ rBw := by decide
@[simp] theorem rQa_ne_rQ : rQa ≠ rQ := by decide
@[simp] theorem rQa_ne_rR : rQa ≠ rR := by decide
@[simp] theorem rQa_ne_rR2 : rQa ≠ rR2 := by decide
@[simp] theorem rQa_ne_rCnt : rQa ≠ rCnt := by decide
@[simp] theorem rQa_ne_rNm1 : rQa ≠ rNm1 := by decide
@[simp] theorem rQa_ne_rO : rQa ≠ rO := by decide
@[simp] theorem rQa_ne_rQo : rQa ≠ rQo := by decide
@[simp] theorem rQa_ne_rU : rQa ≠ rU := by decide
@[simp] theorem rQa_ne_rV : rQa ≠ rV := by decide
@[simp] theorem rQa_ne_rT1 : rQa ≠ rT1 := by decide
@[simp] theorem rQa_ne_rT2 : rQa ≠ rT2 := by decide
@[simp] theorem rQa_ne_rD : rQa ≠ rD := by decide
@[simp] theorem rQa_ne_rI : rQa ≠ rI := by decide
@[simp] theorem rQa_ne_rK : rQa ≠ rK := by decide
@[simp] theorem rQa_ne_rL : rQa ≠ rL := by decide
@[simp] theorem rQa_ne_rZ : rQa ≠ rZ := by decide
@[simp] theorem rQo_ne_rX : rQo ≠ rX := by decide
@[simp] theorem rQo_ne_rY : rQo ≠ rY := by decide
@[simp] theorem rQo_ne_rLa : rQo ≠ rLa := by decide
@[simp] theorem rQo_ne_rLb : rQo ≠ rLb := by decide
@[simp] theorem rQo_ne_rBw : rQo ≠ rBw := by decide
@[simp] theorem rQo_ne_rQ : rQo ≠ rQ := by decide
@[simp] theorem rQo_ne_rR : rQo ≠ rR := by decide
@[simp] theorem rQo_ne_rR2 : rQo ≠ rR2 := by decide
@[simp] theorem rQo_ne_rCnt : rQo ≠ rCnt := by decide
@[simp] theorem rQo_ne_rNm1 : rQo ≠ rNm1 := by decide
@[simp] theorem rQo_ne_rO : rQo ≠ rO := by decide
@[simp] theorem rQo_ne_rQa : rQo ≠ rQa := by decide
@[simp] theorem rQo_ne_rU : rQo ≠ rU := by decide
@[simp] theorem rQo_ne_rV : rQo ≠ rV := by decide
@[simp] theorem rQo_ne_rT1 : rQo ≠ rT1 := by decide
@[simp] theorem rQo_ne_rT2 : rQo ≠ rT2 := by decide
@[simp] theorem rQo_ne_rD : rQo ≠ rD := by decide
@[simp] theorem rQo_ne_rI : rQo ≠ rI := by decide
@[simp] theorem rQo_ne_rK : rQo ≠ rK := by decide
@[simp] theorem rQo_ne_rL : rQo ≠ rL := by decide
@[simp] theorem rQo_ne_rZ : rQo ≠ rZ := by decide
@[simp] theorem rU_ne_rX : rU ≠ rX := by decide
@[simp] theorem rU_ne_rY : rU ≠ rY := by decide
@[simp] theorem rU_ne_rLa : rU ≠ rLa := by decide
@[simp] theorem rU_ne_rLb : rU ≠ rLb := by decide
@[simp] theorem rU_ne_rBw : rU ≠ rBw := by decide
@[simp] theorem rU_ne_rQ : rU ≠ rQ := by decide
@[simp] theorem rU_ne_rR : rU ≠ rR := by decide
@[simp] theorem rU_ne_rR2 : rU ≠ rR2 := by decide
@[simp] theorem rU_ne_rCnt : rU ≠ rCnt := by decide
@[simp] theorem rU_ne_rNm1 : rU ≠ rNm1 := by decide
@[simp] theorem rU_ne_rO : rU ≠ rO := by decide
@[simp] theorem rU_ne_rQa : rU ≠ rQa := by decide
@[simp] theorem rU_ne_rQo : rU ≠ rQo := by decide
@[simp] theorem rU_ne_rV : rU ≠ rV := by decide
@[simp] theorem rU_ne_rT1 : rU ≠ rT1 := by decide
@[simp] theorem rU_ne_rT2 : rU ≠ rT2 := by decide
@[simp] theorem rU_ne_rD : rU ≠ rD := by decide
@[simp] theorem rU_ne_rI : rU ≠ rI := by decide
@[simp] theorem rU_ne_rK : rU ≠ rK := by decide
@[simp] theorem rU_ne_rL : rU ≠ rL := by decide
@[simp] theorem rU_ne_rZ : rU ≠ rZ := by decide
@[simp] theorem rV_ne_rX : rV ≠ rX := by decide
@[simp] theorem rV_ne_rY : rV ≠ rY := by decide
@[simp] theorem rV_ne_rLa : rV ≠ rLa := by decide
@[simp] theorem rV_ne_rLb : rV ≠ rLb := by decide
@[simp] theorem rV_ne_rBw : rV ≠ rBw := by decide
@[simp] theorem rV_ne_rQ : rV ≠ rQ := by decide
@[simp] theorem rV_ne_rR : rV ≠ rR := by decide
@[simp] theorem rV_ne_rR2 : rV ≠ rR2 := by decide
@[simp] theorem rV_ne_rCnt : rV ≠ rCnt := by decide
@[simp] theorem rV_ne_rNm1 : rV ≠ rNm1 := by decide
@[simp] theorem rV_ne_rO : rV ≠ rO := by decide
@[simp] theorem rV_ne_rQa : rV ≠ rQa := by decide
@[simp] theorem rV_ne_rQo : rV ≠ rQo := by decide
@[simp] theorem rV_ne_rU : rV ≠ rU := by decide
@[simp] theorem rV_ne_rT1 : rV ≠ rT1 := by decide
@[simp] theorem rV_ne_rT2 : rV ≠ rT2 := by decide
@[simp] theorem rV_ne_rD : rV ≠ rD := by decide
@[simp] theorem rV_ne_rI : rV ≠ rI := by decide
@[simp] theorem rV_ne_rK : rV ≠ rK := by decide
@[simp] theorem rV_ne_rL : rV ≠ rL := by decide
@[simp] theorem rV_ne_rZ : rV ≠ rZ := by decide
@[simp] theorem rT1_ne_rX : rT1 ≠ rX := by decide
@[simp] theorem rT1_ne_rY : rT1 ≠ rY := by decide
@[simp] theorem rT1_ne_rLa : rT1 ≠ rLa := by decide
@[simp] theorem rT1_ne_rLb : rT1 ≠ rLb := by decide
@[simp] theorem rT1_ne_rBw : rT1 ≠ rBw := by decide
@[simp] theorem rT1_ne_rQ : rT1 ≠ rQ := by decide
@[simp] theorem rT1_ne_rR : rT1 ≠ rR := by decide
@[simp] theorem rT1_ne_rR2 : rT1 ≠ rR2 := by decide
@[simp] theorem rT1_ne_rCnt : rT1 ≠ rCnt := by decide
@[simp] theorem rT1_ne_rNm1 : rT1 ≠ rNm1 := by decide
@[simp] theorem rT1_ne_rO : rT1 ≠ rO := by decide
@[simp] theorem rT1_ne_rQa : rT1 ≠ rQa := by decide
@[simp] theorem rT1_ne_rQo : rT1 ≠ rQo := by decide
@[simp] theorem rT1_ne_rU : rT1 ≠ rU := by decide
@[simp] theorem rT1_ne_rV : rT1 ≠ rV := by decide
@[simp] theorem rT1_ne_rT2 : rT1 ≠ rT2 := by decide
@[simp] theorem rT1_ne_rD : rT1 ≠ rD := by decide
@[simp] theorem rT1_ne_rI : rT1 ≠ rI := by decide
@[simp] theorem rT1_ne_rK : rT1 ≠ rK := by decide
@[simp] theorem rT1_ne_rL : rT1 ≠ rL := by decide
@[simp] theorem rT1_ne_rZ : rT1 ≠ rZ := by decide
@[simp] theorem rT2_ne_rX : rT2 ≠ rX := by decide
@[simp] theorem rT2_ne_rY : rT2 ≠ rY := by decide
@[simp] theorem rT2_ne_rLa : rT2 ≠ rLa := by decide
@[simp] theorem rT2_ne_rLb : rT2 ≠ rLb := by decide
@[simp] theorem rT2_ne_rBw : rT2 ≠ rBw := by decide
@[simp] theorem rT2_ne_rQ : rT2 ≠ rQ := by decide
@[simp] theorem rT2_ne_rR : rT2 ≠ rR := by decide
@[simp] theorem rT2_ne_rR2 : rT2 ≠ rR2 := by decide
@[simp] theorem rT2_ne_rCnt : rT2 ≠ rCnt := by decide
@[simp] theorem rT2_ne_rNm1 : rT2 ≠ rNm1 := by decide
@[simp] theorem rT2_ne_rO : rT2 ≠ rO := by decide
@[simp] theorem rT2_ne_rQa : rT2 ≠ rQa := by decide
@[simp] theorem rT2_ne_rQo : rT2 ≠ rQo := by decide
@[simp] theorem rT2_ne_rU : rT2 ≠ rU := by decide
@[simp] theorem rT2_ne_rV : rT2 ≠ rV := by decide
@[simp] theorem rT2_ne_rT1 : rT2 ≠ rT1 := by decide
@[simp] theorem rT2_ne_rD : rT2 ≠ rD := by decide
@[simp] theorem rT2_ne_rI : rT2 ≠ rI := by decide
@[simp] theorem rT2_ne_rK : rT2 ≠ rK := by decide
@[simp] theorem rT2_ne_rL : rT2 ≠ rL := by decide
@[simp] theorem rT2_ne_rZ : rT2 ≠ rZ := by decide
@[simp] theorem rD_ne_rX : rD ≠ rX := by decide
@[simp] theorem rD_ne_rY : rD ≠ rY := by decide
@[simp] theorem rD_ne_rLa : rD ≠ rLa := by decide
@[simp] theorem rD_ne_rLb : rD ≠ rLb := by decide
@[simp] theorem rD_ne_rBw : rD ≠ rBw := by decide
@[simp] theorem rD_ne_rQ : rD ≠ rQ := by decide
@[simp] theorem rD_ne_rR : rD ≠ rR := by decide
@[simp] theorem rD_ne_rR2 : rD ≠ rR2 := by decide
@[simp] theorem rD_ne_rCnt : rD ≠ rCnt := by decide
@[simp] theorem rD_ne_rNm1 : rD ≠ rNm1 := by decide
@[simp] theorem rD_ne_rO : rD ≠ rO := by decide
@[simp] theorem rD_ne_rQa : rD ≠ rQa := by decide
@[simp] theorem rD_ne_rQo : rD ≠ rQo := by decide
@[simp] theorem rD_ne_rU : rD ≠ rU := by decide
@[simp] theorem rD_ne_rV : rD ≠ rV := by decide
@[simp] theorem rD_ne_rT1 : rD ≠ rT1 := by decide
@[simp] theorem rD_ne_rT2 : rD ≠ rT2 := by decide
@[simp] theorem rD_ne_rI : rD ≠ rI := by decide
@[simp] theorem rD_ne_rK : rD ≠ rK := by decide
@[simp] theorem rD_ne_rL : rD ≠ rL := by decide
@[simp] theorem rD_ne_rZ : rD ≠ rZ := by decide
@[simp] theorem rI_ne_rX : rI ≠ rX := by decide
@[simp] theorem rI_ne_rY : rI ≠ rY := by decide
@[simp] theorem rI_ne_rLa : rI ≠ rLa := by decide
@[simp] theorem rI_ne_rLb : rI ≠ rLb := by decide
@[simp] theorem rI_ne_rBw : rI ≠ rBw := by decide
@[simp] theorem rI_ne_rQ : rI ≠ rQ := by decide
@[simp] theorem rI_ne_rR : rI ≠ rR := by decide
@[simp] theorem rI_ne_rR2 : rI ≠ rR2 := by decide
@[simp] theorem rI_ne_rCnt : rI ≠ rCnt := by decide
@[simp] theorem rI_ne_rNm1 : rI ≠ rNm1 := by decide
@[simp] theorem rI_ne_rO : rI ≠ rO := by decide
@[simp] theorem rI_ne_rQa : rI ≠ rQa := by decide
@[simp] theorem rI_ne_rQo : rI ≠ rQo := by decide
@[simp] theorem rI_ne_rU : rI ≠ rU := by decide
@[simp] theorem rI_ne_rV : rI ≠ rV := by decide
@[simp] theorem rI_ne_rT1 : rI ≠ rT1 := by decide
@[simp] theorem rI_ne_rT2 : rI ≠ rT2 := by decide
@[simp] theorem rI_ne_rD : rI ≠ rD := by decide
@[simp] theorem rI_ne_rK : rI ≠ rK := by decide
@[simp] theorem rI_ne_rL : rI ≠ rL := by decide
@[simp] theorem rI_ne_rZ : rI ≠ rZ := by decide
@[simp] theorem rK_ne_rX : rK ≠ rX := by decide
@[simp] theorem rK_ne_rY : rK ≠ rY := by decide
@[simp] theorem rK_ne_rLa : rK ≠ rLa := by decide
@[simp] theorem rK_ne_rLb : rK ≠ rLb := by decide
@[simp] theorem rK_ne_rBw : rK ≠ rBw := by decide
@[simp] theorem rK_ne_rQ : rK ≠ rQ := by decide
@[simp] theorem rK_ne_rR : rK ≠ rR := by decide
@[simp] theorem rK_ne_rR2 : rK ≠ rR2 := by decide
@[simp] theorem rK_ne_rCnt : rK ≠ rCnt := by decide
@[simp] theorem rK_ne_rNm1 : rK ≠ rNm1 := by decide
@[simp] theorem rK_ne_rO : rK ≠ rO := by decide
@[simp] theorem rK_ne_rQa : rK ≠ rQa := by decide
@[simp] theorem rK_ne_rQo : rK ≠ rQo := by decide
@[simp] theorem rK_ne_rU : rK ≠ rU := by decide
@[simp] theorem rK_ne_rV : rK ≠ rV := by decide
@[simp] theorem rK_ne_rT1 : rK ≠ rT1 := by decide
@[simp] theorem rK_ne_rT2 : rK ≠ rT2 := by decide
@[simp] theorem rK_ne_rD : rK ≠ rD := by decide
@[simp] theorem rK_ne_rI : rK ≠ rI := by decide
@[simp] theorem rK_ne_rL : rK ≠ rL := by decide
@[simp] theorem rK_ne_rZ : rK ≠ rZ := by decide
@[simp] theorem rL_ne_rX : rL ≠ rX := by decide
@[simp] theorem rL_ne_rY : rL ≠ rY := by decide
@[simp] theorem rL_ne_rLa : rL ≠ rLa := by decide
@[simp] theorem rL_ne_rLb : rL ≠ rLb := by decide
@[simp] theorem rL_ne_rBw : rL ≠ rBw := by decide
@[simp] theorem rL_ne_rQ : rL ≠ rQ := by decide
@[simp] theorem rL_ne_rR : rL ≠ rR := by decide
@[simp] theorem rL_ne_rR2 : rL ≠ rR2 := by decide
@[simp] theorem rL_ne_rCnt : rL ≠ rCnt := by decide
@[simp] theorem rL_ne_rNm1 : rL ≠ rNm1 := by decide
@[simp] theorem rL_ne_rO : rL ≠ rO := by decide
@[simp] theorem rL_ne_rQa : rL ≠ rQa := by decide
@[simp] theorem rL_ne_rQo : rL ≠ rQo := by decide
@[simp] theorem rL_ne_rU : rL ≠ rU := by decide
@[simp] theorem rL_ne_rV : rL ≠ rV := by decide
@[simp] theorem rL_ne_rT1 : rL ≠ rT1 := by decide
@[simp] theorem rL_ne_rT2 : rL ≠ rT2 := by decide
@[simp] theorem rL_ne_rD : rL ≠ rD := by decide
@[simp] theorem rL_ne_rI : rL ≠ rI := by decide
@[simp] theorem rL_ne_rK : rL ≠ rK := by decide
@[simp] theorem rL_ne_rZ : rL ≠ rZ := by decide
@[simp] theorem rZ_ne_rX : rZ ≠ rX := by decide
@[simp] theorem rZ_ne_rY : rZ ≠ rY := by decide
@[simp] theorem rZ_ne_rLa : rZ ≠ rLa := by decide
@[simp] theorem rZ_ne_rLb : rZ ≠ rLb := by decide
@[simp] theorem rZ_ne_rBw : rZ ≠ rBw := by decide
@[simp] theorem rZ_ne_rQ : rZ ≠ rQ := by decide
@[simp] theorem rZ_ne_rR : rZ ≠ rR := by decide
@[simp] theorem rZ_ne_rR2 : rZ ≠ rR2 := by decide
@[simp] theorem rZ_ne_rCnt : rZ ≠ rCnt := by decide
@[simp] theorem rZ_ne_rNm1 : rZ ≠ rNm1 := by decide
@[simp] theorem rZ_ne_rO : rZ ≠ rO := by decide
@[simp] theorem rZ_ne_rQa : rZ ≠ rQa := by decide
@[simp] theorem rZ_ne_rQo : rZ ≠ rQo := by decide
@[simp] theorem rZ_ne_rU : rZ ≠ rU := by decide
@[simp] theorem rZ_ne_rV : rZ ≠ rV := by decide
@[simp] theorem rZ_ne_rT1 : rZ ≠ rT1 := by decide
@[simp] theorem rZ_ne_rT2 : rZ ≠ rT2 := by decide
@[simp] theorem rZ_ne_rD : rZ ≠ rD := by decide
@[simp] theorem rZ_ne_rI : rZ ≠ rI := by decide
@[simp] theorem rZ_ne_rK : rZ ≠ rK := by decide
@[simp] theorem rZ_ne_rL : rZ ≠ rL := by decide
@[simp] theorem rX_ne_lFl : rX ≠ lFl := by decide
@[simp] theorem lFl_ne_rX : lFl ≠ rX := by decide
@[simp] theorem rX_ne_lDh : rX ≠ lDh := by decide
@[simp] theorem lDh_ne_rX : lDh ≠ rX := by decide
@[simp] theorem rX_ne_lDt : rX ≠ lDt := by decide
@[simp] theorem lDt_ne_rX : lDt ≠ rX := by decide
@[simp] theorem rX_ne_lDg : rX ≠ lDg := by decide
@[simp] theorem lDg_ne_rX : lDg ≠ rX := by decide
@[simp] theorem rX_ne_lDi : rX ≠ lDi := by decide
@[simp] theorem lDi_ne_rX : lDi ≠ rX := by decide
@[simp] theorem rX_ne_lRp : rX ≠ lRp := by decide
@[simp] theorem lRp_ne_rX : lRp ≠ rX := by decide
@[simp] theorem rX_ne_lRn : rX ≠ lRn := by decide
@[simp] theorem lRn_ne_rX : lRn ≠ rX := by decide
@[simp] theorem rX_ne_lFle : rX ≠ lFle := by decide
@[simp] theorem lFle_ne_rX : lFle ≠ rX := by decide
@[simp] theorem rX_ne_lDir : rX ≠ lDir := by decide
@[simp] theorem lDir_ne_rX : lDir ≠ rX := by decide
@[simp] theorem rX_ne_lFln : rX ≠ lFln := by decide
@[simp] theorem lFln_ne_rX : lFln ≠ rX := by decide
@[simp] theorem rX_ne_lFll : rX ≠ lFll := by decide
@[simp] theorem lFll_ne_rX : lFll ≠ rX := by decide
@[simp] theorem rX_ne_lFls : rX ≠ lFls := by decide
@[simp] theorem lFls_ne_rX : lFls ≠ rX := by decide
@[simp] theorem rX_ne_lKb : rX ≠ lKb := by decide
@[simp] theorem lKb_ne_rX : lKb ≠ rX := by decide
@[simp] theorem rY_ne_lFl : rY ≠ lFl := by decide
@[simp] theorem lFl_ne_rY : lFl ≠ rY := by decide
@[simp] theorem rY_ne_lDh : rY ≠ lDh := by decide
@[simp] theorem lDh_ne_rY : lDh ≠ rY := by decide
@[simp] theorem rY_ne_lDt : rY ≠ lDt := by decide
@[simp] theorem lDt_ne_rY : lDt ≠ rY := by decide
@[simp] theorem rY_ne_lDg : rY ≠ lDg := by decide
@[simp] theorem lDg_ne_rY : lDg ≠ rY := by decide
@[simp] theorem rY_ne_lDi : rY ≠ lDi := by decide
@[simp] theorem lDi_ne_rY : lDi ≠ rY := by decide
@[simp] theorem rY_ne_lRp : rY ≠ lRp := by decide
@[simp] theorem lRp_ne_rY : lRp ≠ rY := by decide
@[simp] theorem rY_ne_lRn : rY ≠ lRn := by decide
@[simp] theorem lRn_ne_rY : lRn ≠ rY := by decide
@[simp] theorem rY_ne_lFle : rY ≠ lFle := by decide
@[simp] theorem lFle_ne_rY : lFle ≠ rY := by decide
@[simp] theorem rY_ne_lDir : rY ≠ lDir := by decide
@[simp] theorem lDir_ne_rY : lDir ≠ rY := by decide
@[simp] theorem rY_ne_lFln : rY ≠ lFln := by decide
@[simp] theorem lFln_ne_rY : lFln ≠ rY := by decide
@[simp] theorem rY_ne_lFll : rY ≠ lFll := by decide
@[simp] theorem lFll_ne_rY : lFll ≠ rY := by decide
@[simp] theorem rY_ne_lFls : rY ≠ lFls := by decide
@[simp] theorem lFls_ne_rY : lFls ≠ rY := by decide
@[simp] theorem rY_ne_lKb : rY ≠ lKb := by decide
@[simp] theorem lKb_ne_rY : lKb ≠ rY := by decide
@[simp] theorem rLa_ne_lFl : rLa ≠ lFl := by decide
@[simp] theorem lFl_ne_rLa : lFl ≠ rLa := by decide
@[simp] theorem rLa_ne_lDh : rLa ≠ lDh := by decide
@[simp] theorem lDh_ne_rLa : lDh ≠ rLa := by decide
@[simp] theorem rLa_ne_lDt : rLa ≠ lDt := by decide
@[simp] theorem lDt_ne_rLa : lDt ≠ rLa := by decide
@[simp] theorem rLa_ne_lDg : rLa ≠ lDg := by decide
@[simp] theorem lDg_ne_rLa : lDg ≠ rLa := by decide
@[simp] theorem rLa_ne_lDi : rLa ≠ lDi := by decide
@[simp] theorem lDi_ne_rLa : lDi ≠ rLa := by decide
@[simp] theorem rLa_ne_lRp : rLa ≠ lRp := by decide
@[simp] theorem lRp_ne_rLa : lRp ≠ rLa := by decide
@[simp] theorem rLa_ne_lRn : rLa ≠ lRn := by decide
@[simp] theorem lRn_ne_rLa : lRn ≠ rLa := by decide
@[simp] theorem rLa_ne_lFle : rLa ≠ lFle := by decide
@[simp] theorem lFle_ne_rLa : lFle ≠ rLa := by decide
@[simp] theorem rLa_ne_lDir : rLa ≠ lDir := by decide
@[simp] theorem lDir_ne_rLa : lDir ≠ rLa := by decide
@[simp] theorem rLa_ne_lFln : rLa ≠ lFln := by decide
@[simp] theorem lFln_ne_rLa : lFln ≠ rLa := by decide
@[simp] theorem rLa_ne_lFll : rLa ≠ lFll := by decide
@[simp] theorem lFll_ne_rLa : lFll ≠ rLa := by decide
@[simp] theorem rLa_ne_lFls : rLa ≠ lFls := by decide
@[simp] theorem lFls_ne_rLa : lFls ≠ rLa := by decide
@[simp] theorem rLa_ne_lKb : rLa ≠ lKb := by decide
@[simp] theorem lKb_ne_rLa : lKb ≠ rLa := by decide
@[simp] theorem rLb_ne_lFl : rLb ≠ lFl := by decide
@[simp] theorem lFl_ne_rLb : lFl ≠ rLb := by decide
@[simp] theorem rLb_ne_lDh : rLb ≠ lDh := by decide
@[simp] theorem lDh_ne_rLb : lDh ≠ rLb := by decide
@[simp] theorem rLb_ne_lDt : rLb ≠ lDt := by decide
@[simp] theorem lDt_ne_rLb : lDt ≠ rLb := by decide
@[simp] theorem rLb_ne_lDg : rLb ≠ lDg := by decide
@[simp] theorem lDg_ne_rLb : lDg ≠ rLb := by decide
@[simp] theorem rLb_ne_lDi : rLb ≠ lDi := by decide
@[simp] theorem lDi_ne_rLb : lDi ≠ rLb := by decide
@[simp] theorem rLb_ne_lRp : rLb ≠ lRp := by decide
@[simp] theorem lRp_ne_rLb : lRp ≠ rLb := by decide
@[simp] theorem rLb_ne_lRn : rLb ≠ lRn := by decide
@[simp] theorem lRn_ne_rLb : lRn ≠ rLb := by decide
@[simp] theorem rLb_ne_lFle : rLb ≠ lFle := by decide
@[simp] theorem lFle_ne_rLb : lFle ≠ rLb := by decide
@[simp] theorem rLb_ne_lDir : rLb ≠ lDir := by decide
@[simp] theorem lDir_ne_rLb : lDir ≠ rLb := by decide
@[simp] theorem rLb_ne_lFln : rLb ≠ lFln := by decide
@[simp] theorem lFln_ne_rLb : lFln ≠ rLb := by decide
@[simp] theorem rLb_ne_lFll : rLb ≠ lFll := by decide
@[simp] theorem lFll_ne_rLb : lFll ≠ rLb := by decide
@[simp] theorem rLb_ne_lFls : rLb ≠ lFls := by decide
@[simp] theorem lFls_ne_rLb : lFls ≠ rLb := by decide
@[simp] theorem rLb_ne_lKb : rLb ≠ lKb := by decide
@[simp] theorem lKb_ne_rLb : lKb ≠ rLb := by decide
@[simp] theorem rBw_ne_lFl : rBw ≠ lFl := by decide
@[simp] theorem lFl_ne_rBw : lFl ≠ rBw := by decide
@[simp] theorem rBw_ne_lDh : rBw ≠ lDh := by decide
@[simp] theorem lDh_ne_rBw : lDh ≠ rBw := by decide
@[simp] theorem rBw_ne_lDt : rBw ≠ lDt := by decide
@[simp] theorem lDt_ne_rBw : lDt ≠ rBw := by decide
@[simp] theorem rBw_ne_lDg : rBw ≠ lDg := by decide
@[simp] theorem lDg_ne_rBw : lDg ≠ rBw := by decide
@[simp] theorem rBw_ne_lDi : rBw ≠ lDi := by decide
@[simp] theorem lDi_ne_rBw : lDi ≠ rBw := by decide
@[simp] theorem rBw_ne_lRp : rBw ≠ lRp := by decide
@[simp] theorem lRp_ne_rBw : lRp ≠ rBw := by decide
@[simp] theorem rBw_ne_lRn : rBw ≠ lRn := by decide
@[simp] theorem lRn_ne_rBw : lRn ≠ rBw := by decide
@[simp] theorem rBw_ne_lFle : rBw ≠ lFle := by decide
@[simp] theorem lFle_ne_rBw : lFle ≠ rBw := by decide
@[simp] theorem rBw_ne_lDir : rBw ≠ lDir := by decide
@[simp] theorem lDir_ne_rBw : lDir ≠ rBw := by decide
@[simp] theorem rBw_ne_lFln : rBw ≠ lFln := by decide
@[simp] theorem lFln_ne_rBw : lFln ≠ rBw := by decide
@[simp] theorem rBw_ne_lFll : rBw ≠ lFll := by decide
@[simp] theorem lFll_ne_rBw : lFll ≠ rBw := by decide
@[simp] theorem rBw_ne_lFls : rBw ≠ lFls := by decide
@[simp] theorem lFls_ne_rBw : lFls ≠ rBw := by decide
@[simp] theorem rBw_ne_lKb : rBw ≠ lKb := by decide
@[simp] theorem lKb_ne_rBw : lKb ≠ rBw := by decide
@[simp] theorem rQ_ne_lFl : rQ ≠ lFl := by decide
@[simp] theorem lFl_ne_rQ : lFl ≠ rQ := by decide
@[simp] theorem rQ_ne_lDh : rQ ≠ lDh := by decide
@[simp] theorem lDh_ne_rQ : lDh ≠ rQ := by decide
@[simp] theorem rQ_ne_lDt : rQ ≠ lDt := by decide
@[simp] theorem lDt_ne_rQ : lDt ≠ rQ := by decide
@[simp] theorem rQ_ne_lDg : rQ ≠ lDg := by decide
@[simp] theorem lDg_ne_rQ : lDg ≠ rQ := by decide
@[simp] theorem rQ_ne_lDi : rQ ≠ lDi := by decide
@[simp] theorem lDi_ne_rQ : lDi ≠ rQ := by decide
@[simp] theorem rQ_ne_lRp : rQ ≠ lRp := by decide
@[simp] theorem lRp_ne_rQ : lRp ≠ rQ := by decide
@[simp] theorem rQ_ne_lRn : rQ ≠ lRn := by decide
@[simp] theorem lRn_ne_rQ : lRn ≠ rQ := by decide
@[simp] theorem rQ_ne_lFle : rQ ≠ lFle := by decide
@[simp] theorem lFle_ne_rQ : lFle ≠ rQ := by decide
@[simp] theorem rQ_ne_lDir : rQ ≠ lDir := by decide
@[simp] theorem lDir_ne_rQ : lDir ≠ rQ := by decide
@[simp] theorem rQ_ne_lFln : rQ ≠ lFln := by decide
@[simp] theorem lFln_ne_rQ : lFln ≠ rQ := by decide
@[simp] theorem rQ_ne_lFll : rQ ≠ lFll := by decide
@[simp] theorem lFll_ne_rQ : lFll ≠ rQ := by decide
@[simp] theorem rQ_ne_lFls : rQ ≠ lFls := by decide
@[simp] theorem lFls_ne_rQ : lFls ≠ rQ := by decide
@[simp] theorem rQ_ne_lKb : rQ ≠ lKb := by decide
@[simp] theorem lKb_ne_rQ : lKb ≠ rQ := by decide
@[simp] theorem rR_ne_lFl : rR ≠ lFl := by decide
@[simp] theorem lFl_ne_rR : lFl ≠ rR := by decide
@[simp] theorem rR_ne_lDh : rR ≠ lDh := by decide
@[simp] theorem lDh_ne_rR : lDh ≠ rR := by decide
@[simp] theorem rR_ne_lDt : rR ≠ lDt := by decide
@[simp] theorem lDt_ne_rR : lDt ≠ rR := by decide
@[simp] theorem rR_ne_lDg : rR ≠ lDg := by decide
@[simp] theorem lDg_ne_rR : lDg ≠ rR := by decide
@[simp] theorem rR_ne_lDi : rR ≠ lDi := by decide
@[simp] theorem lDi_ne_rR : lDi ≠ rR := by decide
@[simp] theorem rR_ne_lRp : rR ≠ lRp := by decide
@[simp] theorem lRp_ne_rR : lRp ≠ rR := by decide
@[simp] theorem rR_ne_lRn : rR ≠ lRn := by decide
@[simp] theorem lRn_ne_rR : lRn ≠ rR := by decide
@[simp] theorem rR_ne_lFle : rR ≠ lFle := by decide
@[simp] theorem lFle_ne_rR : lFle ≠ rR := by decide
@[simp] theorem rR_ne_lDir : rR ≠ lDir := by decide
@[simp] theorem lDir_ne_rR : lDir ≠ rR := by decide
@[simp] theorem rR_ne_lFln : rR ≠ lFln := by decide
@[simp] theorem lFln_ne_rR : lFln ≠ rR := by decide
@[simp] theorem rR_ne_lFll : rR ≠ lFll := by decide
@[simp] theorem lFll_ne_rR : lFll ≠ rR := by decide
@[simp] theorem rR_ne_lFls : rR ≠ lFls := by decide
@[simp] theorem lFls_ne_rR : lFls ≠ rR := by decide
@[simp] theorem rR_ne_lKb : rR ≠ lKb := by decide
@[simp] theorem lKb_ne_rR : lKb ≠ rR := by decide
@[simp] theorem rR2_ne_lFl : rR2 ≠ lFl := by decide
@[simp] theorem lFl_ne_rR2 : lFl ≠ rR2 := by decide
@[simp] theorem rR2_ne_lDh : rR2 ≠ lDh := by decide
@[simp] theorem lDh_ne_rR2 : lDh ≠ rR2 := by decide
@[simp] theorem rR2_ne_lDt : rR2 ≠ lDt := by decide
@[simp] theorem lDt_ne_rR2 : lDt ≠ rR2 := by decide
@[simp] theorem rR2_ne_lDg : rR2 ≠ lDg := by decide
@[simp] theorem lDg_ne_rR2 : lDg ≠ rR2 := by decide
@[simp] theorem rR2_ne_lDi : rR2 ≠ lDi := by decide
@[simp] theorem lDi_ne_rR2 : lDi ≠ rR2 := by decide
@[simp] theorem rR2_ne_lRp : rR2 ≠ lRp := by decide
@[simp] theorem lRp_ne_rR2 : lRp ≠ rR2 := by decide
@[simp] theorem rR2_ne_lRn : rR2 ≠ lRn := by decide
@[simp] theorem lRn_ne_rR2 : lRn ≠ rR2 := by decide
@[simp] theorem rR2_ne_lFle : rR2 ≠ lFle := by decide
@[simp] theorem lFle_ne_rR2 : lFle ≠ rR2 := by decide
@[simp] theorem rR2_ne_lDir : rR2 ≠ lDir := by decide
@[simp] theorem lDir_ne_rR2 : lDir ≠ rR2 := by decide
@[simp] theorem rR2_ne_lFln : rR2 ≠ lFln := by decide
@[simp] theorem lFln_ne_rR2 : lFln ≠ rR2 := by decide
@[simp] theorem rR2_ne_lFll : rR2 ≠ lFll := by decide
@[simp] theorem lFll_ne_rR2 : lFll ≠ rR2 := by decide
@[simp] theorem rR2_ne_lFls : rR2 ≠ lFls := by decide
@[simp] theorem lFls_ne_rR2 : lFls ≠ rR2 := by decide
@[simp] theorem rR2_ne_lKb : rR2 ≠ lKb := by decide
@[simp] theorem lKb_ne_rR2 : lKb ≠ rR2 := by decide
@[simp] theorem rCnt_ne_lFl : rCnt ≠ lFl := by decide
@[simp] theorem lFl_ne_rCnt : lFl ≠ rCnt := by decide
@[simp] theorem rCnt_ne_lDh : rCnt ≠ lDh := by decide
@[simp] theorem lDh_ne_rCnt : lDh ≠ rCnt := by decide
@[simp] theorem rCnt_ne_lDt : rCnt ≠ lDt := by decide
@[simp] theorem lDt_ne_rCnt : lDt ≠ rCnt := by decide
@[simp] theorem rCnt_ne_lDg : rCnt ≠ lDg := by decide
@[simp] theorem lDg_ne_rCnt : lDg ≠ rCnt := by decide
@[simp] theorem rCnt_ne_lDi : rCnt ≠ lDi := by decide
@[simp] theorem lDi_ne_rCnt : lDi ≠ rCnt := by decide
@[simp] theorem rCnt_ne_lRp : rCnt ≠ lRp := by decide
@[simp] theorem lRp_ne_rCnt : lRp ≠ rCnt := by decide
@[simp] theorem rCnt_ne_lRn : rCnt ≠ lRn := by decide
@[simp] theorem lRn_ne_rCnt : lRn ≠ rCnt := by decide
@[simp] theorem rCnt_ne_lFle : rCnt ≠ lFle := by decide
@[simp] theorem lFle_ne_rCnt : lFle ≠ rCnt := by decide
@[simp] theorem rCnt_ne_lDir : rCnt ≠ lDir := by decide
@[simp] theorem lDir_ne_rCnt : lDir ≠ rCnt := by decide
@[simp] theorem rCnt_ne_lFln : rCnt ≠ lFln := by decide
@[simp] theorem lFln_ne_rCnt : lFln ≠ rCnt := by decide
@[simp] theorem rCnt_ne_lFll : rCnt ≠ lFll := by decide
@[simp] theorem lFll_ne_rCnt : lFll ≠ rCnt := by decide
@[simp] theorem rCnt_ne_lFls : rCnt ≠ lFls := by decide
@[simp] theorem lFls_ne_rCnt : lFls ≠ rCnt := by decide
@[simp] theorem rCnt_ne_lKb : rCnt ≠ lKb := by decide
@[simp] theorem lKb_ne_rCnt : lKb ≠ rCnt := by decide
@[simp] theorem rNm1_ne_lFl : rNm1 ≠ lFl := by decide
@[simp] theorem lFl_ne_rNm1 : lFl ≠ rNm1 := by decide
@[simp] theorem rNm1_ne_lDh : rNm1 ≠ lDh := by decide
@[simp] theorem lDh_ne_rNm1 : lDh ≠ rNm1 := by decide
@[simp] theorem rNm1_ne_lDt : rNm1 ≠ lDt := by decide
@[simp] theorem lDt_ne_rNm1 : lDt ≠ rNm1 := by decide
@[simp] theorem rNm1_ne_lDg : rNm1 ≠ lDg := by decide
@[simp] theorem lDg_ne_rNm1 : lDg ≠ rNm1 := by decide
@[simp] theorem rNm1_ne_lDi : rNm1 ≠ lDi := by decide
@[simp] theorem lDi_ne_rNm1 : lDi ≠ rNm1 := by decide
@[simp] theorem rNm1_ne_lRp : rNm1 ≠ lRp := by decide
@[simp] theorem lRp_ne_rNm1 : lRp ≠ rNm1 := by decide
@[simp] theorem rNm1_ne_lRn : rNm1 ≠ lRn := by decide
@[simp] theorem lRn_ne_rNm1 : lRn ≠ rNm1 := by decide
@[simp] theorem rNm1_ne_lFle : rNm1 ≠ lFle := by decide
@[simp] theorem lFle_ne_rNm1 : lFle ≠ rNm1 := by decide
@[simp] theorem rNm1_ne_lDir : rNm1 ≠ lDir := by decide
@[simp] theorem lDir_ne_rNm1 : lDir ≠ rNm1 := by decide
@[simp] theorem rNm1_ne_lFln : rNm1 ≠ lFln := by decide
@[simp] theorem lFln_ne_rNm1 : lFln ≠ rNm1 := by decide
@[simp] theorem rNm1_ne_lFll : rNm1 ≠ lFll := by decide
@[simp] theorem lFll_ne_rNm1 : lFll ≠ rNm1 := by decide
@[simp] theorem rNm1_ne_lFls : rNm1 ≠ lFls := by decide
@[simp] theorem lFls_ne_rNm1 : lFls ≠ rNm1 := by decide
@[simp] theorem rNm1_ne_lKb : rNm1 ≠ lKb := by decide
@[simp] theorem lKb_ne_rNm1 : lKb ≠ rNm1 := by decide
@[simp] theorem rO_ne_lFl : rO ≠ lFl := by decide
@[simp] theorem lFl_ne_rO : lFl ≠ rO := by decide
@[simp] theorem rO_ne_lDh : rO ≠ lDh := by decide
@[simp] theorem lDh_ne_rO : lDh ≠ rO := by decide
@[simp] theorem rO_ne_lDt : rO ≠ lDt := by decide
@[simp] theorem lDt_ne_rO : lDt ≠ rO := by decide
@[simp] theorem rO_ne_lDg : rO ≠ lDg := by decide
@[simp] theorem lDg_ne_rO : lDg ≠ rO := by decide
@[simp] theorem rO_ne_lDi : rO ≠ lDi := by decide
@[simp] theorem lDi_ne_rO : lDi ≠ rO := by decide
@[simp] theorem rO_ne_lRp : rO ≠ lRp := by decide
@[simp] theorem lRp_ne_rO : lRp ≠ rO := by decide
@[simp] theorem rO_ne_lRn : rO ≠ lRn := by decide
@[simp] theorem lRn_ne_rO : lRn ≠ rO := by decide
@[simp] theorem rO_ne_lFle : rO ≠ lFle := by decide
@[simp] theorem lFle_ne_rO : lFle ≠ rO := by decide
@[simp] theorem rO_ne_lDir : rO ≠ lDir := by decide
@[simp] theorem lDir_ne_rO : lDir ≠ rO := by decide
@[simp] theorem rO_ne_lFln : rO ≠ lFln := by decide
@[simp] theorem lFln_ne_rO : lFln ≠ rO := by decide
@[simp] theorem rO_ne_lFll : rO ≠ lFll := by decide
@[simp] theorem lFll_ne_rO : lFll ≠ rO := by decide
@[simp] theorem rO_ne_lFls : rO ≠ lFls := by decide
@[simp] theorem lFls_ne_rO : lFls ≠ rO := by decide
@[simp] theorem rO_ne_lKb : rO ≠ lKb := by decide
@[simp] theorem lKb_ne_rO : lKb ≠ rO := by decide
@[simp] theorem rQa_ne_lFl : rQa ≠ lFl := by decide
@[simp] theorem lFl_ne_rQa : lFl ≠ rQa := by decide
@[simp] theorem rQa_ne_lDh : rQa ≠ lDh := by decide
@[simp] theorem lDh_ne_rQa : lDh ≠ rQa := by decide
@[simp] theorem rQa_ne_lDt : rQa ≠ lDt := by decide
@[simp] theorem lDt_ne_rQa : lDt ≠ rQa := by decide
@[simp] theorem rQa_ne_lDg : rQa ≠ lDg := by decide
@[simp] theorem lDg_ne_rQa : lDg ≠ rQa := by decide
@[simp] theorem rQa_ne_lDi : rQa ≠ lDi := by decide
@[simp] theorem lDi_ne_rQa : lDi ≠ rQa := by decide
@[simp] theorem rQa_ne_lRp : rQa ≠ lRp := by decide
@[simp] theorem lRp_ne_rQa : lRp ≠ rQa := by decide
@[simp] theorem rQa_ne_lRn : rQa ≠ lRn := by decide
@[simp] theorem lRn_ne_rQa : lRn ≠ rQa := by decide
@[simp] theorem rQa_ne_lFle : rQa ≠ lFle := by decide
@[simp] theorem lFle_ne_rQa : lFle ≠ rQa := by decide
@[simp] theorem rQa_ne_lDir : rQa ≠ lDir := by decide
@[simp] theorem lDir_ne_rQa : lDir ≠ rQa := by decide
@[simp] theorem rQa_ne_lFln : rQa ≠ lFln := by decide
@[simp] theorem lFln_ne_rQa : lFln ≠ rQa := by decide
@[simp] theorem rQa_ne_lFll : rQa ≠ lFll := by decide
@[simp] theorem lFll_ne_rQa : lFll ≠ rQa := by decide
@[simp] theorem rQa_ne_lFls : rQa ≠ lFls := by decide
@[simp] theorem lFls_ne_rQa : lFls ≠ rQa := by decide
@[simp] theorem rQa_ne_lKb : rQa ≠ lKb := by decide
@[simp] theorem lKb_ne_rQa : lKb ≠ rQa := by decide
@[simp] theorem rQo_ne_lFl : rQo ≠ lFl := by decide
@[simp] theorem lFl_ne_rQo : lFl ≠ rQo := by decide
@[simp] theorem rQo_ne_lDh : rQo ≠ lDh := by decide
@[simp] theorem lDh_ne_rQo : lDh ≠ rQo := by decide
@[simp] theorem rQo_ne_lDt : rQo ≠ lDt := by decide
@[simp] theorem lDt_ne_rQo : lDt ≠ rQo := by decide
@[simp] theorem rQo_ne_lDg : rQo ≠ lDg := by decide
@[simp] theorem lDg_ne_rQo : lDg ≠ rQo := by decide
@[simp] theorem rQo_ne_lDi : rQo ≠ lDi := by decide
@[simp] theorem lDi_ne_rQo : lDi ≠ rQo := by decide
@[simp] theorem rQo_ne_lRp : rQo ≠ lRp := by decide
@[simp] theorem lRp_ne_rQo : lRp ≠ rQo := by decide
@[simp] theorem rQo_ne_lRn : rQo ≠ lRn := by decide
@[simp] theorem lRn_ne_rQo : lRn ≠ rQo := by decide
@[simp] theorem rQo_ne_lFle : rQo ≠ lFle := by decide
@[simp] theorem lFle_ne_rQo : lFle ≠ rQo := by decide
@[simp] theorem rQo_ne_lDir : rQo ≠ lDir := by decide
@[simp] theorem lDir_ne_rQo : lDir ≠ rQo := by decide
@[simp] theorem rQo_ne_lFln : rQo ≠ lFln := by decide
@[simp] theorem lFln_ne_rQo : lFln ≠ rQo := by decide
@[simp] theorem rQo_ne_lFll : rQo ≠ lFll := by decide
@[simp] theorem lFll_ne_rQo : lFll ≠ rQo := by decide
@[simp] theorem rQo_ne_lFls : rQo ≠ lFls := by decide
@[simp] theorem lFls_ne_rQo : lFls ≠ rQo := by decide
@[simp] theorem rQo_ne_lKb : rQo ≠ lKb := by decide
@[simp] theorem lKb_ne_rQo : lKb ≠ rQo := by decide
@[simp] theorem rU_ne_lFl : rU ≠ lFl := by decide
@[simp] theorem lFl_ne_rU : lFl ≠ rU := by decide
@[simp] theorem rU_ne_lDh : rU ≠ lDh := by decide
@[simp] theorem lDh_ne_rU : lDh ≠ rU := by decide
@[simp] theorem rU_ne_lDt : rU ≠ lDt := by decide
@[simp] theorem lDt_ne_rU : lDt ≠ rU := by decide
@[simp] theorem rU_ne_lDg : rU ≠ lDg := by decide
@[simp] theorem lDg_ne_rU : lDg ≠ rU := by decide
@[simp] theorem rU_ne_lDi : rU ≠ lDi := by decide
@[simp] theorem lDi_ne_rU : lDi ≠ rU := by decide
@[simp] theorem rU_ne_lRp : rU ≠ lRp := by decide
@[simp] theorem lRp_ne_rU : lRp ≠ rU := by decide
@[simp] theorem rU_ne_lRn : rU ≠ lRn := by decide
@[simp] theorem lRn_ne_rU : lRn ≠ rU := by decide
@[simp] theorem rU_ne_lFle : rU ≠ lFle := by decide
@[simp] theorem lFle_ne_rU : lFle ≠ rU := by decide
@[simp] theorem rU_ne_lDir : rU ≠ lDir := by decide
@[simp] theorem lDir_ne_rU : lDir ≠ rU := by decide
@[simp] theorem rU_ne_lFln : rU ≠ lFln := by decide
@[simp] theorem lFln_ne_rU : lFln ≠ rU := by decide
@[simp] theorem rU_ne_lFll : rU ≠ lFll := by decide
@[simp] theorem lFll_ne_rU : lFll ≠ rU := by decide
@[simp] theorem rU_ne_lFls : rU ≠ lFls := by decide
@[simp] theorem lFls_ne_rU : lFls ≠ rU := by decide
@[simp] theorem rU_ne_lKb : rU ≠ lKb := by decide
@[simp] theorem lKb_ne_rU : lKb ≠ rU := by decide
@[simp] theorem rV_ne_lFl : rV ≠ lFl := by decide
@[simp] theorem lFl_ne_rV : lFl ≠ rV := by decide
@[simp] theorem rV_ne_lDh : rV ≠ lDh := by decide
@[simp] theorem lDh_ne_rV : lDh ≠ rV := by decide
@[simp] theorem rV_ne_lDt : rV ≠ lDt := by decide
@[simp] theorem lDt_ne_rV : lDt ≠ rV := by decide
@[simp] theorem rV_ne_lDg : rV ≠ lDg := by decide
@[simp] theorem lDg_ne_rV : lDg ≠ rV := by decide
@[simp] theorem rV_ne_lDi : rV ≠ lDi := by decide
@[simp] theorem lDi_ne_rV : lDi ≠ rV := by decide
@[simp] theorem rV_ne_lRp : rV ≠ lRp := by decide
@[simp] theorem lRp_ne_rV : lRp ≠ rV := by decide
@[simp] theorem rV_ne_lRn : rV ≠ lRn := by decide
@[simp] theorem lRn_ne_rV : lRn ≠ rV := by decide
@[simp] theorem rV_ne_lFle : rV ≠ lFle := by decide
@[simp] theorem lFle_ne_rV : lFle ≠ rV := by decide
@[simp] theorem rV_ne_lDir : rV ≠ lDir := by decide
@[simp] theorem lDir_ne_rV : lDir ≠ rV := by decide
@[simp] theorem rV_ne_lFln : rV ≠ lFln := by decide
@[simp] theorem lFln_ne_rV : lFln ≠ rV := by decide
@[simp] theorem rV_ne_lFll : rV ≠ lFll := by decide
@[simp] theorem lFll_ne_rV : lFll ≠ rV := by decide
@[simp] theorem rV_ne_lFls : rV ≠ lFls := by decide
@[simp] theorem lFls_ne_rV : lFls ≠ rV := by decide
@[simp] theorem rV_ne_lKb : rV ≠ lKb := by decide
@[simp] theorem lKb_ne_rV : lKb ≠ rV := by decide
@[simp] theorem rT1_ne_lFl : rT1 ≠ lFl := by decide
@[simp] theorem lFl_ne_rT1 : lFl ≠ rT1 := by decide
@[simp] theorem rT1_ne_lDh : rT1 ≠ lDh := by decide
@[simp] theorem lDh_ne_rT1 : lDh ≠ rT1 := by decide
@[simp] theorem rT1_ne_lDt : rT1 ≠ lDt := by decide
@[simp] theorem lDt_ne_rT1 : lDt ≠ rT1 := by decide
@[simp] theorem rT1_ne_lDg : rT1 ≠ lDg := by decide
@[simp] theorem lDg_ne_rT1 : lDg ≠ rT1 := by decide
@[simp] theorem rT1_ne_lDi : rT1 ≠ lDi := by decide
@[simp] theorem lDi_ne_rT1 : lDi ≠ rT1 := by decide
@[simp] theorem rT1_ne_lRp : rT1 ≠ lRp := by decide
@[simp] theorem lRp_ne_rT1 : lRp ≠ rT1 := by decide
@[simp] theorem rT1_ne_lRn : rT1 ≠ lRn := by decide
@[simp] theorem lRn_ne_rT1 : lRn ≠ rT1 := by decide
@[simp] theorem rT1_ne_lFle : rT1 ≠ lFle := by decide
@[simp] theorem lFle_ne_rT1 : lFle ≠ rT1 := by decide
@[simp] theorem rT1_ne_lDir : rT1 ≠ lDir := by decide
@[simp] theorem lDir_ne_rT1 : lDir ≠ rT1 := by decide
@[simp] theorem rT1_ne_lFln : rT1 ≠ lFln := by decide
@[simp] theorem lFln_ne_rT1 : lFln ≠ rT1 := by decide
@[simp] theorem rT1_ne_lFll : rT1 ≠ lFll := by decide
@[simp] theorem lFll_ne_rT1 : lFll ≠ rT1 := by decide
@[simp] theorem rT1_ne_lFls : rT1 ≠ lFls := by decide
@[simp] theorem lFls_ne_rT1 : lFls ≠ rT1 := by decide
@[simp] theorem rT1_ne_lKb : rT1 ≠ lKb := by decide
@[simp] theorem lKb_ne_rT1 : lKb ≠ rT1 := by decide
@[simp] theorem rT2_ne_lFl : rT2 ≠ lFl := by decide
@[simp] theorem lFl_ne_rT2 : lFl ≠ rT2 := by decide
@[simp] theorem rT2_ne_lDh : rT2 ≠ lDh := by decide
@[simp] theorem lDh_ne_rT2 : lDh ≠ rT2 := by decide
@[simp] theorem rT2_ne_lDt : rT2 ≠ lDt := by decide
@[simp] theorem lDt_ne_rT2 : lDt ≠ rT2 := by decide
@[simp] theorem rT2_ne_lDg : rT2 ≠ lDg := by decide
@[simp] theorem lDg_ne_rT2 : lDg ≠ rT2 := by decide
@[simp] theorem rT2_ne_lDi : rT2 ≠ lDi := by decide
@[simp] theorem lDi_ne_rT2 : lDi ≠ rT2 := by decide
@[simp] theorem rT2_ne_lRp : rT2 ≠ lRp := by decide
@[simp] theorem lRp_ne_rT2 : lRp ≠ rT2 := by decide
@[simp] theorem rT2_ne_lRn : rT2 ≠ lRn := by decide
@[simp] theorem lRn_ne_rT2 : lRn ≠ rT2 := by decide
@[simp] theorem rT2_ne_lFle : rT2 ≠ lFle := by decide
@[simp] theorem lFle_ne_rT2 : lFle ≠ rT2 := by decide
@[simp] theorem rT2_ne_lDir : rT2 ≠ lDir := by decide
@[simp] theorem lDir_ne_rT2 : lDir ≠ rT2 := by decide
@[simp] theorem rT2_ne_lFln : rT2 ≠ lFln := by decide
@[simp] theorem lFln_ne_rT2 : lFln ≠ rT2 := by decide
@[simp] theorem rT2_ne_lFll : rT2 ≠ lFll := by decide
@[simp] theorem lFll_ne_rT2 : lFll ≠ rT2 := by decide
@[simp] theorem rT2_ne_lFls : rT2 ≠ lFls := by decide
@[simp] theorem lFls_ne_rT2 : lFls ≠ rT2 := by decide
@[simp] theorem rT2_ne_lKb : rT2 ≠ lKb := by decide
@[simp] theorem lKb_ne_rT2 : lKb ≠ rT2 := by decide
@[simp] theorem rD_ne_lFl : rD ≠ lFl := by decide
@[simp] theorem lFl_ne_rD : lFl ≠ rD := by decide
@[simp] theorem rD_ne_lDh : rD ≠ lDh := by decide
@[simp] theorem lDh_ne_rD : lDh ≠ rD := by decide
@[simp] theorem rD_ne_lDt : rD ≠ lDt := by decide
@[simp] theorem lDt_ne_rD : lDt ≠ rD := by decide
@[simp] theorem rD_ne_lDg : rD ≠ lDg := by decide
@[simp] theorem lDg_ne_rD : lDg ≠ rD := by decide
@[simp] theorem rD_ne_lDi : rD ≠ lDi := by decide
@[simp] theorem lDi_ne_rD : lDi ≠ rD := by decide
@[simp] theorem rD_ne_lRp : rD ≠ lRp := by decide
@[simp] theorem lRp_ne_rD : lRp ≠ rD := by decide
@[simp] theorem rD_ne_lRn : rD ≠ lRn := by decide
@[simp] theorem lRn_ne_rD : lRn ≠ rD := by decide
@[simp] theorem rD_ne_lFle : rD ≠ lFle := by decide
@[simp] theorem lFle_ne_rD : lFle ≠ rD := by decide
@[simp] theorem rD_ne_lDir : rD ≠ lDir := by decide
@[simp] theorem lDir_ne_rD : lDir ≠ rD := by decide
@[simp] theorem rD_ne_lFln : rD ≠ lFln := by decide
@[simp] theorem lFln_ne_rD : lFln ≠ rD := by decide
@[simp] theorem rD_ne_lFll : rD ≠ lFll := by decide
@[simp] theorem lFll_ne_rD : lFll ≠ rD := by decide
@[simp] theorem rD_ne_lFls : rD ≠ lFls := by decide
@[simp] theorem lFls_ne_rD : lFls ≠ rD := by decide
@[simp] theorem rD_ne_lKb : rD ≠ lKb := by decide
@[simp] theorem lKb_ne_rD : lKb ≠ rD := by decide
@[simp] theorem rI_ne_lFl : rI ≠ lFl := by decide
@[simp] theorem lFl_ne_rI : lFl ≠ rI := by decide
@[simp] theorem rI_ne_lDh : rI ≠ lDh := by decide
@[simp] theorem lDh_ne_rI : lDh ≠ rI := by decide
@[simp] theorem rI_ne_lDt : rI ≠ lDt := by decide
@[simp] theorem lDt_ne_rI : lDt ≠ rI := by decide
@[simp] theorem rI_ne_lDg : rI ≠ lDg := by decide
@[simp] theorem lDg_ne_rI : lDg ≠ rI := by decide
@[simp] theorem rI_ne_lDi : rI ≠ lDi := by decide
@[simp] theorem lDi_ne_rI : lDi ≠ rI := by decide
@[simp] theorem rI_ne_lRp : rI ≠ lRp := by decide
@[simp] theorem lRp_ne_rI : lRp ≠ rI := by decide
@[simp] theorem rI_ne_lRn : rI ≠ lRn := by decide
@[simp] theorem lRn_ne_rI : lRn ≠ rI := by decide
@[simp] theorem rI_ne_lFle : rI ≠ lFle := by decide
@[simp] theorem lFle_ne_rI : lFle ≠ rI := by decide
@[simp] theorem rI_ne_lDir : rI ≠ lDir := by decide
@[simp] theorem lDir_ne_rI : lDir ≠ rI := by decide
@[simp] theorem rI_ne_lFln : rI ≠ lFln := by decide
@[simp] theorem lFln_ne_rI : lFln ≠ rI := by decide
@[simp] theorem rI_ne_lFll : rI ≠ lFll := by decide
@[simp] theorem lFll_ne_rI : lFll ≠ rI := by decide
@[simp] theorem rI_ne_lFls : rI ≠ lFls := by decide
@[simp] theorem lFls_ne_rI : lFls ≠ rI := by decide
@[simp] theorem rI_ne_lKb : rI ≠ lKb := by decide
@[simp] theorem lKb_ne_rI : lKb ≠ rI := by decide
@[simp] theorem rK_ne_lFl : rK ≠ lFl := by decide
@[simp] theorem lFl_ne_rK : lFl ≠ rK := by decide
@[simp] theorem rK_ne_lDh : rK ≠ lDh := by decide
@[simp] theorem lDh_ne_rK : lDh ≠ rK := by decide
@[simp] theorem rK_ne_lDt : rK ≠ lDt := by decide
@[simp] theorem lDt_ne_rK : lDt ≠ rK := by decide
@[simp] theorem rK_ne_lDg : rK ≠ lDg := by decide
@[simp] theorem lDg_ne_rK : lDg ≠ rK := by decide
@[simp] theorem rK_ne_lDi : rK ≠ lDi := by decide
@[simp] theorem lDi_ne_rK : lDi ≠ rK := by decide
@[simp] theorem rK_ne_lRp : rK ≠ lRp := by decide
@[simp] theorem lRp_ne_rK : lRp ≠ rK := by decide
@[simp] theorem rK_ne_lRn : rK ≠ lRn := by decide
@[simp] theorem lRn_ne_rK : lRn ≠ rK := by decide
@[simp] theorem rK_ne_lFle : rK ≠ lFle := by decide
@[simp] theorem lFle_ne_rK : lFle ≠ rK := by decide
@[simp] theorem rK_ne_lDir : rK ≠ lDir := by decide
@[simp] theorem lDir_ne_rK : lDir ≠ rK := by decide
@[simp] theorem rK_ne_lFln : rK ≠ lFln := by decide
@[simp] theorem lFln_ne_rK : lFln ≠ rK := by decide
@[simp] theorem rK_ne_lFll : rK ≠ lFll := by decide
@[simp] theorem lFll_ne_rK : lFll ≠ rK := by decide
@[simp] theorem rK_ne_lFls : rK ≠ lFls := by decide
@[simp] theorem lFls_ne_rK : lFls ≠ rK := by decide
@[simp] theorem rK_ne_lKb : rK ≠ lKb := by decide
@[simp] theorem lKb_ne_rK : lKb ≠ rK := by decide
@[simp] theorem rL_ne_lFl : rL ≠ lFl := by decide
@[simp] theorem lFl_ne_rL : lFl ≠ rL := by decide
@[simp] theorem rL_ne_lDh : rL ≠ lDh := by decide
@[simp] theorem lDh_ne_rL : lDh ≠ rL := by decide
@[simp] theorem rL_ne_lDt : rL ≠ lDt := by decide
@[simp] theorem lDt_ne_rL : lDt ≠ rL := by decide
@[simp] theorem rL_ne_lDg : rL ≠ lDg := by decide
@[simp] theorem lDg_ne_rL : lDg ≠ rL := by decide
@[simp] theorem rL_ne_lDi : rL ≠ lDi := by decide
@[simp] theorem lDi_ne_rL : lDi ≠ rL := by decide
@[simp] theorem rL_ne_lRp : rL ≠ lRp := by decide
@[simp] theorem lRp_ne_rL : lRp ≠ rL := by decide
@[simp] theorem rL_ne_lRn : rL ≠ lRn := by decide
@[simp] theorem lRn_ne_rL : lRn ≠ rL := by decide
@[simp] theorem rL_ne_lFle : rL ≠ lFle := by decide
@[simp] theorem lFle_ne_rL : lFle ≠ rL := by decide
@[simp] theorem rL_ne_lDir : rL ≠ lDir := by decide
@[simp] theorem lDir_ne_rL : lDir ≠ rL := by decide
@[simp] theorem rL_ne_lFln : rL ≠ lFln := by decide
@[simp] theorem lFln_ne_rL : lFln ≠ rL := by decide
@[simp] theorem rL_ne_lFll : rL ≠ lFll := by decide
@[simp] theorem lFll_ne_rL : lFll ≠ rL := by decide
@[simp] theorem rL_ne_lFls : rL ≠ lFls := by decide
@[simp] theorem lFls_ne_rL : lFls ≠ rL := by decide
@[simp] theorem rL_ne_lKb : rL ≠ lKb := by decide
@[simp] theorem lKb_ne_rL : lKb ≠ rL := by decide
@[simp] theorem rZ_ne_lFl : rZ ≠ lFl := by decide
@[simp] theorem lFl_ne_rZ : lFl ≠ rZ := by decide
@[simp] theorem rZ_ne_lDh : rZ ≠ lDh := by decide
@[simp] theorem lDh_ne_rZ : lDh ≠ rZ := by decide
@[simp] theorem rZ_ne_lDt : rZ ≠ lDt := by decide
@[simp] theorem lDt_ne_rZ : lDt ≠ rZ := by decide
@[simp] theorem rZ_ne_lDg : rZ ≠ lDg := by decide
@[simp] theorem lDg_ne_rZ : lDg ≠ rZ := by decide
@[simp] theorem rZ_ne_lDi : rZ ≠ lDi := by decide
@[simp] theorem lDi_ne_rZ : lDi ≠ rZ := by decide
@[simp] theorem rZ_ne_lRp : rZ ≠ lRp := by decide
@[simp] theorem lRp_ne_rZ : lRp ≠ rZ := by decide
@[simp] theorem rZ_ne_lRn : rZ ≠ lRn := by decide
@[simp] theorem lRn_ne_rZ : lRn ≠ rZ := by decide
@[simp] theorem rZ_ne_lFle : rZ ≠ lFle := by decide
@[simp] theorem lFle_ne_rZ : lFle ≠ rZ := by decide
@[simp] theorem rZ_ne_lDir : rZ ≠ lDir := by decide
@[simp] theorem lDir_ne_rZ : lDir ≠ rZ := by decide
@[simp] theorem rZ_ne_lFln : rZ ≠ lFln := by decide
@[simp] theorem lFln_ne_rZ : lFln ≠ rZ := by decide
@[simp] theorem rZ_ne_lFll : rZ ≠ lFll := by decide
@[simp] theorem lFll_ne_rZ : lFll ≠ rZ := by decide
@[simp] theorem rZ_ne_lFls : rZ ≠ lFls := by decide
@[simp] theorem lFls_ne_rZ : lFls ≠ rZ := by decide
@[simp] theorem rZ_ne_lKb : rZ ≠ lKb := by decide
@[simp] theorem lKb_ne_rZ : lKb ≠ rZ := by decide

/-- An empty block (the number `0`). -/
def zeroBlk (C : Ctx) : ProgHOL 64 :=
  allocP C rZ (.const 8) (.seq (.store (vv rZ) (.const 0)) (.return (vv rZ)))

def shrLoop : ProgHOL 64 :=
  .while (.cmp .lower (vv rI) (vv rNm1))
    (.seq (.assign .local rU (.load .one (vv rQa)))
    (.seq (.assign .local rV (.load .one (.op .add [vv rQa, .const 8])))
    (.seq (.assign .local rD (.op .add [.shift .lsr (vv rU) (vv rR),
        .shift .lsl (.shift .lsl (vv rV) (.const 1)) (vv rR2)]))
    (.seq (.store (vv rQo) (vv rD))
    (.seq (.assign .local rQa (.op .add [vv rQa, .const 8]))
    (.seq (.assign .local rQo (.op .add [vv rQo, .const 8]))
    (.assign .local rI (.op .add [vv rI, .const 1]))))))))

def shrTrimE : ExpHOL 64 :=
  .op .add [vv rL, .panop .mul [.cmp .notEqual (vv rU) (.const 0), .op .sub [.op .add [vv rK, .const 1], vv rL]]]

def shrTrim : ProgHOL 64 :=
  .while (.cmp .lower (vv rK) (vv rCnt))
    (.seq (.assign .local rU (.load .one (vv rQo)))
    (.seq (.assign .local rL shrTrimE)
    (.seq (.assign .local rQo (.op .add [vv rQo, .const 8]))
    (.assign .local rK (.op .add [vv rK, .const 1])))))

def shrMain (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local rCnt (.op .sub [vv rLa, vv rQ]))
  (allocP C rO (.panop .mul [.op .add [vv rCnt, .const 2], .const 8])
  (.seq (.assign .local rQa (.op .add [.op .add [vv rX, .const 8], .panop .mul [vv rQ, .const 8]]))
  (.seq (.assign .local rQo (.op .add [vv rO, .const 8]))
  (.seq (.assign .local rI (.const 0)) (.seq (.assign .local rNm1 (.op .sub [vv rCnt, .const 1]))
  (.seq shrLoop
  (.seq (.assign .local rU (.load .one (vv rQa)))
  (.seq (.assign .local rD (.shift .lsr (vv rU) (vv rR)))
  (.seq (.store (vv rQo) (vv rD))
  (.seq (.assign .local rK (.const 0)) (.seq (.assign .local rL (.const 0))
  (.seq (.assign .local rQo (.op .add [vv rO, .const 8]))
  (.seq shrTrim
  (.seq (.store (vv rO) (vv rL))
  (.return (vv rO))))))))))))))))

def shrCore (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local rLa (.load .one (vv rX)))
  (.seq (.assign .local rLb (.load .one (vv rY)))
  (.ite (.cmp .equal (vv rLb) (.const 0)) (.return (vv rX))
  (.ite (.cmp .lower (.const 1) (vv rLb)) (zeroBlk C)
  (.seq (.assign .local rBw (.load .one (.op .add [vv rY, .const 8])))
  (.seq (.assign .local rQ (.shift .lsr (vv rBw) (.const 6)))
  (.seq (.assign .local rR (.op .and [vv rBw, .const 63]))
  (.seq (.assign .local rR2 (.op .sub [.const 63, vv rR]))
  (.ite (.cmp .lower (vv rQ) (vv rLa)) (shrMain C) (zeroBlk C)))))))))

def shrLocals : List MlS := [rLa, rLb, rBw, rQ, rR, rR2, rCnt, rNm1, rO, rQa, rQo, rU, rV, rT1, rT2, rD, rI, rK, rL, rZ]
def shrParams : List MlS := [rX, rY]
def shrBody (C : Ctx) : ProgHOL 64 := prologue shrLocals (shrCore C)

section
variable {σ : Type}

/-- The digits of `a >>> (64 q + r)`, `n` many. -/
def shrW (a q r n : Nat) : List (BitVec 64) :=
  (List.range n).map fun k => BitVec.ofNat 64 (dg (a / 2 ^ (64 * q + r)) k)

theorem shrW_get (a q r n k : Nat) (hk : k < n) :
    (shrW a q r n)[k]? = some (BitVec.ofNat 64 (dg (a / 2 ^ (64 * q + r)) k)) := by
  simp [shrW, hk]

theorem sev_shrE (Γ : Env) (u v : BitVec 64) (r : Nat) (hr : r < 64) (hu : Γ.get rU = some u)
    (hv : Γ.get rV = some v) (hR : Γ.get rR = some (BitVec.ofNat 64 r))
    (hR2 : Γ.get rR2 = some (BitVec.ofNat 64 (63 - r))) :
    sev Γ (.op .add [.shift .lsr (vv rU) (vv rR), .shift .lsl (.shift .lsl (vv rV) (.const 1)) (vv rR2)]) =
      some (u >>> r + (v <<< 1) <<< (63 - r)) := by
  have hrr : (BitVec.ofNat 64 r).toNat = r := by simp; omega
  have hrr2 : (BitVec.ofNat 64 (63 - r)).toNat = 63 - r := by simp; omega
  simp [sev, vv, hu, hv, hR, hR2, hrr, hrr2, show r < 64 from hr, show 63 - r < 64 by omega]

theorem fill_lo (B0 W : List (BitVec 64)) (o j k : Nat) (hk : k < o) : (fillI B0 W o j)[k]? = B0[k]? := by
  rw [fillI_get?, ite_eq_right (by omega)]

def shrG (Γ0 : Env) (C : Ctx) (od oa q k : Nat) : Env :=
  (rI, BitVec.ofNat 64 k) :: (rQo, cellA C (od + 1 + k)) :: (rQa, cellA C (oa + 1 + q + k)) :: Γ0

theorem cellA_add8' (C : Ctx) (k : Nat) : cellA C k + 8 = cellA C (k + 1) := cellA_add8 C k

theorem shr_loop {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ0 : Env} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (a q r n : Nat) (B0 : List (BitVec 64)) (od oa : Nat)
    (hr : r < 64) (hba : BlkAt B0 oa (limbs a)) (hla : oa + 1 + (limbs a).length ≤ od + 1)
    (hn : n + q = (limbs a).length) (hn1 : 1 ≤ n) (hdst : od + 1 + n ≤ B0.length) (h61 : n < 2 ^ 61)
    (hD : rU ∈ D ∧ rV ∈ D ∧ rD ∈ D ∧ rQa ∈ D ∧ rQo ∈ D ∧ rI ∈ D)
    (hNm1 : Γ0.get rNm1 = some (BitVec.ofNat 64 (n - 1))) (hR : Γ0.get rR = some (BitVec.ofNat 64 r))
    (hR2 : Γ0.get rR2 = some (BitVec.ofNat 64 (63 - r)))
    (hnU : Γ0.get rU = none) (hnV : Γ0.get rV = none) (hnD : Γ0.get rD = none)
    (hrest : SpecR (Inv (ctxH C (fillI B0 (shrW a q r n) (od + 1) (n - 1))) s (shrG Γ0 C od oa q (n - 1)) [] D)
      rest s m R) :
    SpecR (Inv (ctxH C (fillI B0 (shrW a q r n) (od + 1) 0)) s (shrG Γ0 C od oa q 0) [] D) (.seq shrLoop rest) s m R := by
  obtain ⟨du, dv, dd, dqa, dqo, di⟩ := hD
  have hl := fillI_length B0 (shrW a q r n) (od + 1)
  refine specR_forI (σ := σ) (D := D) (M := []) _ _ rest (n - 1)
    (fun k => ctxH C (fillI B0 (shrW a q r n) (od + 1) k)) (shrG Γ0 C od oa q)
    (fun k hk => ⟨if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 k) (BitVec.ofNat 64 (n - 1))
      then 1 else 0, by simp [sev, shrG, Env.get, hNm1], ?_⟩) (fun k hk => ?_) hrest
  · have e := word_lt_iff k (n - 1) (by unfold B; omega) (by unfold B; omega)
    by_cases h' : k < n - 1
    · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e.mpr h', h']
    · have : ¬ BitVec.ofNat 64 k < BitVec.ofNat 64 (n - 1) := fun x => h' (e.mp x)
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this, h']
  have hu : (fillI B0 (shrW a q r n) (od + 1) k)[oa + 1 + q + k]? = some (BitVec.ofNat 64 (dg a (k + q))) := by
    rw [fill_lo B0 _ (od + 1) k _ (by omega), show oa + 1 + q + k = oa + 1 + (k + q) by omega,
      hba.2 (k + q) (by omega)]
    rw [limbs_getElem a (k + q) (by omega)]; rfl
  have hv : (fillI B0 (shrW a q r n) (od + 1) k)[oa + 1 + q + k + 1]? = some (BitVec.ofNat 64 (dg a (k + q + 1))) := by
    rw [fill_lo B0 _ (od + 1) k _ (by omega), show oa + 1 + q + k + 1 = oa + 1 + (k + q + 1) by omega,
      hba.2 (k + q + 1) (by omega)]
    rw [limbs_getElem a (k + q + 1) (by omega)]; rfl
  refine step_seq (step_heapLoadI' (C := ctxH C _) rU (vv rQa) _ _ hu du (by simp [shrG]; rfl)) ?_
  refine step_seq (step_heapLoadI' (C := ctxH C _) rV _ _ _ hv dv (by simp [sev, shrG]; exact cellA_add8 C _)) ?_
  have hd0 := Nat.mod_lt (a / B ^ (k + q)) Bpos
  have hd1 := Nat.mod_lt (a / B ^ (k + q + 1)) Bpos
  have hw := shr_word (dg a (k + q)) (dg a (k + q + 1)) r hd0 hd1 hr
  rw [← shr_digit a q r k hr] at hw
  have hrr : (BitVec.ofNat 64 r).toNat = r := by simp; omega
  have hrr2 : (BitVec.ofNat 64 (63 - r)).toNat = 63 - r := by simp; omega
  refine step_seq (step_assignI rD _ (BitVec.ofNat 64 (dg (a / 2 ^ (64 * q + r)) k)) dd ?_) ?_
  · rw [sev_shrE _ (BitVec.ofNat 64 (dg a (k + q))) (BitVec.ofNat 64 (dg a (k + q + 1))) r hr (by simp) (by simp)
      (by simp [shrG, hR]) (by simp [shrG, hR2])]
    exact congrArg some hw
  have hj : od + 1 + k < (ctxH C (fillI B0 (shrW a q r n) (od + 1) k)).H.length := by
    show _ < (fillI _ _ _ _).length; rw [hl]; omega
  refine step_seq (step_heapStoreI (ctxOK_H hok _) (vv rQo) (vv rD) _ hj (BitVec.ofNat 64 (dg (a / 2 ^ (64 * q + r)) k))
    (by simp [shrG]; rfl) (by simp)) ?_
  change Step (Inv (ctxH C ((fillI B0 (shrW a q r n) (od + 1) k).set (od + 1 + k) _)) s _ [] D) _ _
  rw [fillI_succ_eq _ _ _ _ _ (shrW_get a q r n k (by omega))]
  refine step_seq (step_assignI rQa _ (cellA C (oa + 1 + q + k + 1)) dqa (by simp [sev, shrG]; exact cellA_add8 C _)) ?_
  refine step_seq (step_assignI rQo _ (cellA C (od + 1 + k + 1)) dqo (by simp [sev, shrG]; exact cellA_add8 C _)) ?_
  refine step_mono (step_assignI rI _ (BitVec.ofNat 64 (k + 1)) di (by simp [sev, shrG]; exact word_add1_eq k))
    (fun _ h => h) (fun t ht => inv_envMono ht (fun z v hz => ?_))
  simp only [shrG, Env.get_cons] at hz ⊢
  by_cases e1 : z = rI
  · subst e1; simp_all
  by_cases e2 : z = rQo
  · subst e2; simp_all [Nat.add_assoc]
  by_cases e3 : z = rQa
  · subst e3; simp_all [Nat.add_assoc]
  simp only [e1, e2, e3, ite_false] at hz
  have f : ∀ w, Γ0.get w = none → z ≠ w := fun w hw e => by subst e; rw [hw] at hz; simp at hz
  simp [e1, e2, e3, f _ hnU, f _ hnV, f _ hnD, hz]

def shrG3 (Γ2 : Env) (C : Ctx) (od n k : Nat) : Env :=
  (rK, BitVec.ofNat 64 k) :: (rQo, cellA C (od + 1 + k)) :: (rL, BitVec.ofNat 64 (limbs (n % B ^ k)).length) :: Γ2

theorem shr_trim {α : Type} {C : Ctx} {s : AState} {Γ2 : Env} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (n lx : Nat) (Bf W : List (BitVec 64)) (od : Nat)
    (hW : ∀ k, k < lx → Bf[od + 1 + k]? = some (BitVec.ofNat 64 (n / B ^ k % B))) (h61 : lx < 2 ^ 61)
    (hD : rU ∈ D ∧ rL ∈ D ∧ rQo ∈ D ∧ rK ∈ D)
    (hLa : Γ2.get rCnt = some (BitVec.ofNat 64 lx)) (hn : Γ2.get rU = none)
    (hr : SpecR (Inv (ctxH C Bf) s (shrG3 Γ2 C od n lx) [] D) rest s m R) :
    SpecR (Inv (ctxH C Bf) s (shrG3 Γ2 C od n 0) [] D) (.seq shrTrim rest) s m R := by
  obtain ⟨du, dl, dq, dk⟩ := hD
  refine specR_forI (σ := σ) (D := D) (M := []) _ _ rest lx (fun _ => ctxH C Bf) (shrG3 Γ2 C od n)
    (fun i hi => ⟨if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower (BitVec.ofNat 64 i) (BitVec.ofNat 64 lx)
      then 1 else 0, by simp [sev, shrG3, Env.get, hLa], ?_⟩) (fun i hi => ?_) hr
  · have e := word_lt_iff i lx (by unfold B; omega) (by unfold B; omega)
    by_cases h' : i < lx
    · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e.mpr h', h']
    · have : ¬ BitVec.ofNat 64 i < BitVec.ofNat 64 lx := fun x => h' (e.mp x)
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this, h']
  refine step_seq (step_heapLoadI' (C := ctxH C Bf) rU (vv rQo) (od + 1 + i) _ (hW i hi) du
    (by simp [shrG3]; rfl)) ?_
  refine step_seq (step_assignI rL shrTrimE (BitVec.ofNat 64 (limbs (n % B ^ (i + 1))).length) dl ?_) ?_
  · simp only [shrTrimE, sev, sev_vv, Env.get_cons, shrG3]
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    rw [len_mod_succ, ← trim_word _ i _ (Nat.mod_lt _ Bpos)]
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  refine step_seq (step_assignI rQo _ (cellA C (od + 1 + i + 1)) dq (by simp [sev, shrG3]; exact cellA_add8 C _)) ?_
  refine step_mono (step_assignI rK _ (BitVec.ofNat 64 (i + 1)) dk (by simp [sev, shrG3]; exact word_add1_eq i))
    (fun _ h => h) (fun t ht => inv_envMono ht (fun z v hz => ?_))
  simp only [shrG3, Env.get_cons] at hz ⊢
  by_cases e1 : z = rK
  · subst e1; simp_all
  by_cases e2 : z = rQo
  · subst e2; simp_all [Nat.add_assoc]
  by_cases e3 : z = rL
  · subst e3; simp_all
  simp only [e1, e2, e3, ite_false] at hz
  have f1 : z ≠ rU := by intro e; subst e; rw [hn] at hz; simp at hz
  simp [e1, e2, e3, f1, hz]



theorem zeroBlk_spec {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {D : List MlS} (hz : rZ ∈ D) :
    SpecR (σ := σ) (Inv C s Γ [] D) (zeroBlk C) s (pure 0 : AM Nat) (PostH C s) := by
  unfold zeroBlk
  refine specR_allocI rZ (.const 8) 1 (by norm_num) hz (fun v => by simp [sev]) (fun H' ws hpre hwl hcap => ?_)
  have hj : H'.length < (ctxH C (H' ++ ws)).H.length := by show _ < (H' ++ ws).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv rZ) (.const 0) _ hj 0 (by simp; rfl) rfl ?_
  refine specR_returnI _ (cellA C H'.length) (by simp) (fun t ht => ?_)
  refine ⟨_, H'.length, prefix_set_ge (hpre.trans (List.prefix_append _ _)) _ hpre.length_le _, rfl, ?_, rfl,
    sr_of_eq ht.sr rfl rfl rfl rfl⟩
  rw [limbs_zero]
  refine ⟨?_, fun i hi => absurd hi (by simp)⟩
  show ((H' ++ ws).set H'.length 0)[H'.length]? = _
  rw [List.getElem?_set_self (by simp; omega)]; rfl

theorem shr_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ shrLocals → (ctxEnv C ++ shrParams.zip vals).get x = none :=
  Knot.params_none C shrLocals shrParams vals (by decide) (by decide)

theorem shr_zero_res (a b la : Nat) (ha : a < B ^ la) (hb : 64 * la ≤ b) : a >>> b = 0 := by
  rw [Nat.shiftRight_eq_div_pow]
  apply Nat.div_eq_of_lt
  calc a < B ^ la := ha
    _ = 2 ^ (64 * la) := by rw [Nat.pow_mul]
    _ ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) hb

theorem shr_spec (C : Ctx) (hok : CtxOK C) (s : AState) (a b : Nat) (oa ob : Nat)
    (hba : BlkAt C.H oa (limbs a)) (hbb : BlkAt C.H ob (limbs b)) :
    SpecR (σ := σ) (Pre C s (shrParams.zip [cellA C oa, cellA C ob])) (shrBody C) s (pure (a >>> b) : AM Nat)
      (PostH C s) := by
  refine specR_prologue (postH_locals C s) (shr_none C _) ?_
  unfold shrCore
  have hla0 : C.H[oa]? = some (BitVec.ofNat 64 (limbs a).length) := by simpa using hba.1
  have hlb0 : C.H[ob]? = some (BitVec.ofNat 64 (limbs b).length) := by simpa using hbb.1
  refine UD.specR_heapLoadI' rLa (vv rX) oa _ hla0 (by decide) (by simp +decide [Env.get, shrParams, ctxEnv]) ?_
  refine UD.specR_heapLoadI' rLb (vv rY) ob _ hlb0 (by decide) (by simp +decide [Env.get, shrParams, ctxEnv]) ?_
  refine specR_atEntry fun t0 ht0 => ?_
  obtain ⟨H0, hp0, ha0⟩ := ht0.sr.heap
  have hbl := blkAt_len hba
  have hbl2 := blkAt_len hbb
  have hcap := hok.heapCap
  have hlen0 := ha0.len
  have hp0l := hp0.length_le
  have hla58 : (limbs a).length < 2 ^ 58 := by omega
  have hlb58 : (limbs b).length < 2 ^ 58 := by omega
  have hwl := word_lt_iff 1 (limbs b).length (by decide) (by unfold B; omega)
  have haB : a < B ^ (limbs a).length := (limbs_length_lt_iff a _).mp (Nat.le_refl _)
  by_cases hb0 : (limbs b).length = 0
  · -- b = 0
    have hbz : b = 0 := by
      have := (limbs_length_lt_iff b 0).mp (by omega); simpa using this
    refine specR_ifI _ 1 (by simp [sev, Env.get, hb0, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    refine specR_returnI _ (cellA C oa) (by simp +decide [Env.get, shrParams, ctxEnv]) (fun t ht => ?_)
    rw [hbz, Nat.shiftRight_zero]
    exact ⟨C.H, oa, List.prefix_refl _, rfl, hba, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
  have hb0w : BitVec.ofNat 64 (limbs b).length ≠ 0 := fun e => hb0 (by
    have := congrArg BitVec.toNat e; simp at this; omega)
  refine specR_ifI _ 0 (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hb0w)
    (fun h => absurd rfl h) (fun _ => ?_)
  by_cases hb1 : 1 < (limbs b).length
  · -- b ≥ 2^64: the result is 0
    refine specR_ifI _ 1 (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hwl.mpr hb1])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hbB : B ≤ b := by
      have h2 : ¬ (limbs b).length ≤ 1 := by omega
      rw [limbs_length_lt_iff] at h2; simpa using h2
    rw [shr_zero_res a b _ haB (by unfold B at hbB; omega)]
    exact zeroBlk_spec hok (by decide)
  refine specR_ifI _ 0 (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, (not_congr hwl).mpr hb1])
    (fun h => absurd rfl h) (fun _ => ?_)
  have hb1' : (limbs b).length = 1 := by omega
  have hbB : b < B := by have := (limbs_length_lt_iff b 1).mp (by omega); simpa using this
  have hbB' : b < 2 ^ 64 := hbB
  have hbw : C.H[ob + 1 + 0]? = some (BitVec.ofNat 64 b) := by
    rw [hbb.2 0 (by omega), limbs_getElem b 0 (by omega)]
    simp only [Nat.pow_zero, Nat.div_one]
    rw [Nat.mod_eq_of_lt hbB]
  refine UD.specR_heapLoadI' rBw _ (ob + 1 + 0) _ hbw (by decide)
    (by simp +decide [sev, Env.get, shrParams, ctxEnv]; exact cellA_add8 C _) ?_
  refine specR_assignI rQ _ (BitVec.ofNat 64 (b / 64)) (by decide) (by
    simp only [sev, sev_vv, Env.get_cons]
    simp
    apply BitVec.eq_of_toNat_eq
    simp [Nat.shiftRight_eq_div_pow, Nat.mod_eq_of_lt hbB']
    omega) ?_
  have hand : b &&& 63 = b % 64 := Nat.and_two_pow_sub_one_eq_mod b 6
  refine specR_assignI rR _ (BitVec.ofNat 64 (b % 64)) (by decide) (by
    simp only [sev, sev_vv, Env.get_cons]
    simp
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_and, Nat.mod_eq_of_lt hbB', hand]
    have h64 : b % 64 < 18446744073709551616 := Nat.lt_of_lt_of_le (Nat.mod_lt b (by decide)) (by decide)
    have hb2 : b < 18446744073709551616 := hbB'
    rw [Nat.mod_eq_of_lt hb2, hand]
    exact (Nat.mod_eq_of_lt h64).symm) ?_
  refine specR_assignI rR2 _ (BitVec.ofNat 64 (63 - b % 64)) (by decide) (by
    simp [sev]
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_sub]; omega) ?_
  have hbdm : 64 * (b / 64) + b % 64 = b := Nat.div_add_mod b 64
  have hr64 : b % 64 < 64 := Nat.mod_lt _ (by decide)
  have hqa := word_lt_iff (b / 64) (limbs a).length (by unfold B; omega) (by unfold B; omega)
  by_cases hq : b / 64 < (limbs a).length
  · refine specR_ifI _ 1 (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hqa.mpr hq])
      (fun _ => ?_) (fun h => absurd h (by decide))
    unfold shrMain
    generalize hq' : b / 64 = q at hq hqa hbdm
    generalize hr' : b % 64 = r at hr64 hbdm
    generalize hn : (limbs a).length - q = n
    have hn1 : 1 ≤ n := by omega
    refine specR_assignI rCnt _ (BitVec.ofNat 64 n) (by decide) (by
      simp [sev, Env.get]
      rw [← hn, BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]) ?_
    refine specR_allocI rO (.panop .mul [.op .add [vv rCnt, .const 2], .const 8]) (n + 2) (by omega)
      (by decide) (fun v => by
        simp [sev, Env.get]
        rw [show (2#64 : BitVec 64) = BitVec.ofNat 64 2 from rfl, BitVec.ofNat_add_ofNat]; exact CV.mul8_eq _)
      (fun H' wsN hpre hwl hcap => ?_)
    have hpl := hpre.length_le
    let B0 := H' ++ wsN
    have hB0 : B0.length = H'.length + (n + 2) := by simp [B0, hwl]
    have hba' : BlkAt B0 oa (limbs a) := blkAt_mono hba (hpre.trans (List.prefix_append _ _))
    refine specR_assignI rQa _ (cellA C (oa + 1 + q)) (by decide) (by
      simp [sev, Env.get, shrParams, ctxEnv]
      have m8 : BitVec.ofNat 64 q * 8#64 = BitVec.ofNat 64 (8 * q) := CV.mul8_eq q
      rw [m8, BitVec.add_assoc, show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat]
      unfold cellA; rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]; congr 2; omega) ?_
    refine specR_assignI rQo _ (cellA C (H'.length + 1 + 0)) (by decide) (by simp [sev]; exact cellA_add8 C _) ?_
    refine specR_assignI rI (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
    refine specR_assignI rNm1 _ (BitVec.ofNat 64 (n - 1)) (by decide)
      (by simp [sev]; rw [show (1#64 : BitVec 64) = BitVec.ofNat 64 1 from rfl,
        BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]) ?_
    let Γ0 : Env := [(rNm1, BitVec.ofNat 64 (n - 1)), (rR, BitVec.ofNat 64 r), (rR2, BitVec.ofNat 64 (63 - r)),
      (rCnt, BitVec.ofNat 64 n), (rO, cellA C H'.length)]
    refine specR_envWeak (Γb := shrG Γ0 C H'.length oa q 0) (fun z v hz => ?_) ?_
    · simp only [shrG, Γ0, Env.get_cons, Nat.add_zero] at hz ⊢
      by_cases e1 : z = rI
      · subst e1; simpa using hz
      by_cases e2 : z = rQo
      · subst e2; simpa using hz
      by_cases e3 : z = rQa
      · subst e3; simpa using hz
      by_cases e4 : z = rNm1
      · subst e4; simpa using hz
      by_cases e5 : z = rR
      · subst e5; simpa using hz
      by_cases e6 : z = rR2
      · subst e6; simpa using hz
      by_cases e7 : z = rCnt
      · subst e7; simpa using hz
      by_cases e8 : z = rO
      · subst e8; simpa using hz
      simp [e1, e2, e3, e4, e5, e6, e7, e8, Env.get] at hz
    have hbl := blkAt_len hba
    refine shr_loop hok a q r n B0 H'.length oa hr64 hba' (by omega) (by omega) hn1 (by rw [hB0]; omega) (by omega)
      (by decide) (by simp [Γ0]) (by simp [Γ0]) (by simp [Γ0]) (by simp [Γ0, Env.get]) (by simp [Γ0, Env.get])
      (by simp [Γ0, Env.get]) ?_
    -- the last digit
    have hlast : (fillI B0 (shrW a q r n) (H'.length + 1) (n - 1))[oa + 1 + q + (n - 1)]? =
        some (BitVec.ofNat 64 (dg a ((limbs a).length - 1))) := by
      rw [fill_lo B0 _ (H'.length + 1) _ _ (by omega), show oa + 1 + q + (n - 1) = oa + 1 + ((limbs a).length - 1) by omega,
        hba'.2 _ (by omega), limbs_getElem a _ (by omega)]; rfl
    refine UD.specR_heapLoadI' (C := ctxH C _) rU (vv rQa) _ _ hlast (by decide) (by simp [shrG]; rfl) ?_
    have hdl : dg (a / 2 ^ (64 * q + r)) (n - 1) = dg a ((limbs a).length - 1) / 2 ^ r := by
      rw [shr_digit a q r (n - 1) hr64, show n - 1 + q + 1 = (limbs a).length by omega,
        dg_big a _ haB, Nat.zero_mul, Nat.add_zero, show n - 1 + q = (limbs a).length - 1 by omega]
      exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ Bpos))
    have hrr : (BitVec.ofNat 64 r).toNat = r := by simp; omega
    refine specR_assignI rD _ (BitVec.ofNat 64 (dg (a / 2 ^ (64 * q + r)) (n - 1))) (by decide) (by
      simp [sev, vv, shrG, Γ0, hrr, show r < 64 from hr64]
      rw [hdl]; apply BitVec.eq_of_toNat_eq
      simp [Nat.shiftRight_eq_div_pow]
      have h1 : a / B ^ ((limbs a).length - 1) % B < 18446744073709551616 :=
        Nat.mod_lt (a / B ^ ((limbs a).length - 1)) Bpos
      unfold dg
      rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) h1)]) ?_
    have hl := fillI_length B0 (shrW a q r n) (H'.length + 1)
    have hj : H'.length + 1 + (n - 1) < (ctxH C (fillI B0 (shrW a q r n) (H'.length + 1) (n - 1))).H.length := by
      show _ < (fillI _ _ _ _).length; rw [hl, hB0]; omega
    refine specR_heapStoreI (ctxOK_H hok _) (vv rQo) (vv rD) _ hj (BitVec.ofNat 64 (dg (a / 2 ^ (64 * q + r)) (n - 1)))
      (by simp [shrG]; rfl) (by simp) ?_
    change SpecR (Inv (ctxH C ((fillI B0 (shrW a q r n) (H'.length + 1) (n - 1)).set (H'.length + 1 + (n - 1)) _)) s _
      [] _) _ _ _ _
    rw [fillI_succ_eq _ _ _ _ _ (shrW_get a q r n (n - 1) (by omega)), show n - 1 + 1 = n by omega]
    refine specR_assignI rK (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
    refine specR_assignI rL (.const 0) (BitVec.ofNat 64 0) (by decide) rfl ?_
    refine specR_assignI rQo _ (cellA C (H'.length + 1)) (by decide) (by simp [sev, shrG, Γ0]; exact cellA_add8 C _) ?_
    have hab : a >>> b = a / 2 ^ (64 * q + r) := by rw [Nat.shiftRight_eq_div_pow, hbdm]
    let Bf := fillI B0 (shrW a q r n) (H'.length + 1) n
    have hlf : Bf.length = B0.length := hl n
    have hWf : ∀ k, k < n → Bf[H'.length + 1 + k]? = some (BitVec.ofNat 64 ((a >>> b) / B ^ k % B)) := by
      intro k hk
      rw [fillI_get?, ite_eq_left ⟨by omega, by omega, by rw [hB0]; omega⟩]
      simp [show H'.length + 1 + k - (H'.length + 1) = k by omega, List.getD_eq_getElem?_getD, shrW_get a q r n k hk,
        hab, dg]
    refine specR_envWeak (Γb := shrG3 Γ0 C H'.length (a >>> b) 0) (fun z v hz => ?_) ?_
    · simp only [shrG3, shrG, Γ0, Env.get_cons, Nat.pow_zero, Nat.mod_one, Nat.add_zero] at hz ⊢
      by_cases e1 : z = rK
      · subst e1; simpa using hz
      by_cases e2 : z = rQo
      · subst e2; simpa using hz
      by_cases e3 : z = rL
      · subst e3; simp at hz ⊢; rw [← hz, limbs_zero]; rfl
      simp only [e1, e2, e3, ite_false] at hz ⊢
      by_cases f1 : z = rNm1
      · subst f1; simpa using hz
      by_cases f2 : z = rR
      · subst f2; simpa using hz
      by_cases f3 : z = rR2
      · subst f3; simpa using hz
      by_cases f4 : z = rCnt
      · subst f4; simpa using hz
      by_cases f5 : z = rO
      · subst f5; simpa using hz
      simp [f1, f2, f3, f4, f5, Env.get] at hz
    refine shr_trim (a >>> b) n Bf (shrW a q r n) H'.length hWf (by omega) (by decide)
      (by simp [Γ0]) (by simp [Γ0, Env.get]) ?_
    have hres : a >>> b < B ^ n := by
      rw [hab]
      apply Nat.div_lt_of_lt_mul
      calc a < B ^ (limbs a).length := haB
        _ = 2 ^ (64 * q + r) * B ^ n / 2 ^ r := by
          have hB : B = 2 ^ 64 := rfl
          rw [hB, ← Nat.pow_mul, ← Nat.pow_mul, ← Nat.pow_add, show 64 * q + r + 64 * n = 64 * (limbs a).length + r by omega,
            Nat.pow_add, Nat.mul_div_cancel _ (Nat.pow_pos (by decide))]
        _ ≤ 2 ^ (64 * q + r) * B ^ n := Nat.div_le_self _ _
    have hmod : (a >>> b) % B ^ n = a >>> b := Nat.mod_eq_of_lt hres
    have hj2 : H'.length < (ctxH C Bf).H.length := by show _ < Bf.length; rw [hlf, hB0]; omega
    refine specR_heapStoreI (ctxOK_H hok _) (vv rO) (vv rL) _ hj2 (BitVec.ofNat 64 (limbs (a >>> b)).length)
      (by simp [shrG3, Γ0]; rfl) (by simp [shrG3, hmod]) ?_
    refine specR_returnI _ (cellA C H'.length) (by simp [shrG3, Γ0]) (fun t ht => ?_)
    refine ⟨_, H'.length, ?_, rfl, ?_, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
    · exact prefix_set_ge (CV.prefix_fillI _ _ _ C.H (by omega) (hpre.trans (List.prefix_append _ _)) _) _ hpl _
    · have hlen := (limbs_length_lt_iff (a >>> b) n).mpr hres
      constructor
      · rw [List.getElem?_set_self (by show H'.length < Bf.length; rw [hlf, hB0]; omega)]
      · intro i hi
        rw [List.getElem?_set_ne (by omega)]
        show Bf[H'.length + 1 + i]? = _
        rw [hWf i (by omega), limbs_getElem (a >>> b) i hi]
  · refine specR_ifI _ 0 (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, (not_congr hqa).mpr hq])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [shr_zero_res a b _ haB (by omega)]
    exact zeroBlk_spec hok (by decide)

end

end ConPanqueque.T.Big
