import ConPanqueque.T.Core.DefEqList
import ConPanqueque.T.Core.FormerLoop
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `piResidual` and `iotaIndexOk`

`piResidual`: peel a `∀` telescope along a run of argument cells, instantiating each body
(`instantiate1Fast`); a non-`∀` before the run ends answers `none`.

`iotaIndexOk`: equal major and parameter counts answer `true`; otherwise the constructor type's residual
after the major's arguments, its arguments past the constructor's parameters, compared with the indices by
`defEqList`.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def pxH := ofString "pxh"
def pxA := ofString "pxa"
def pxK := ofString "pxk"
def pxB := ofString "pxb"
def pxX := ofString "pxx"
def pxV := ofString "pxv"
def pxR := ofString "pxr"
def ixMI := ofString "ixmi"
def ixRP := ofString "ixrp"
def ixCn := ofString "ixcn"
def ixT := ofString "ixt"
def ixMa := ofString "ixma"
def ixMn := ofString "ixmn"
def ixIa := ofString "ixia"
def ixIn := ofString "ixin"
def ixR := ofString "ixr"
def ixG := ofString "ixg"
def ixL := ofString "ixl"
def ixT2 := ofString "ixt2"
def ixQ := ofString "ixq"
def ixD := ofString "ixd"
def fPx := ofString "piResidual"
def fIx := ofString "iotaIndexOk"

@[simp] theorem ix_pxH_ne_pxA : pxH ≠ pxA := by decide
@[simp] theorem ix_pxH_ne_pxK : pxH ≠ pxK := by decide
@[simp] theorem ix_pxH_ne_pxB : pxH ≠ pxB := by decide
@[simp] theorem ix_pxH_ne_pxX : pxH ≠ pxX := by decide
@[simp] theorem ix_pxH_ne_pxV : pxH ≠ pxV := by decide
@[simp] theorem ix_pxH_ne_pxR : pxH ≠ pxR := by decide
@[simp] theorem ix_pxH_ne_ixMI : pxH ≠ ixMI := by decide
@[simp] theorem ix_pxH_ne_ixRP : pxH ≠ ixRP := by decide
@[simp] theorem ix_pxH_ne_ixCn : pxH ≠ ixCn := by decide
@[simp] theorem ix_pxH_ne_ixT : pxH ≠ ixT := by decide
@[simp] theorem ix_pxH_ne_ixMa : pxH ≠ ixMa := by decide
@[simp] theorem ix_pxH_ne_ixMn : pxH ≠ ixMn := by decide
@[simp] theorem ix_pxH_ne_ixIa : pxH ≠ ixIa := by decide
@[simp] theorem ix_pxH_ne_ixIn : pxH ≠ ixIn := by decide
@[simp] theorem ix_pxH_ne_ixR : pxH ≠ ixR := by decide
@[simp] theorem ix_pxH_ne_ixG : pxH ≠ ixG := by decide
@[simp] theorem ix_pxH_ne_ixL : pxH ≠ ixL := by decide
@[simp] theorem ix_pxH_ne_ixT2 : pxH ≠ ixT2 := by decide
@[simp] theorem ix_pxH_ne_ixQ : pxH ≠ ixQ := by decide
@[simp] theorem ix_pxH_ne_ixD : pxH ≠ ixD := by decide
@[simp] theorem ix_pxH_ne_kFu : pxH ≠ kFu := by decide
@[simp] theorem ix_pxH_ne_kD : pxH ≠ kD := by decide
@[simp] theorem ix_pxH_ne_lFl : pxH ≠ lFl := by decide
@[simp] theorem ix_pxH_ne_lDh : pxH ≠ lDh := by decide
@[simp] theorem ix_pxH_ne_lDt : pxH ≠ lDt := by decide
@[simp] theorem ix_pxH_ne_lDg : pxH ≠ lDg := by decide
@[simp] theorem ix_pxH_ne_lDi : pxH ≠ lDi := by decide
@[simp] theorem ix_pxH_ne_lRp : pxH ≠ lRp := by decide
@[simp] theorem ix_pxH_ne_lRn : pxH ≠ lRn := by decide
@[simp] theorem ix_pxH_ne_lKb : pxH ≠ lKb := by decide
@[simp] theorem ix_pxH_ne_lFle : pxH ≠ lFle := by decide
@[simp] theorem ix_pxH_ne_lDir : pxH ≠ lDir := by decide
@[simp] theorem ix_pxA_ne_pxH : pxA ≠ pxH := by decide
@[simp] theorem ix_pxA_ne_pxK : pxA ≠ pxK := by decide
@[simp] theorem ix_pxA_ne_pxB : pxA ≠ pxB := by decide
@[simp] theorem ix_pxA_ne_pxX : pxA ≠ pxX := by decide
@[simp] theorem ix_pxA_ne_pxV : pxA ≠ pxV := by decide
@[simp] theorem ix_pxA_ne_pxR : pxA ≠ pxR := by decide
@[simp] theorem ix_pxA_ne_ixMI : pxA ≠ ixMI := by decide
@[simp] theorem ix_pxA_ne_ixRP : pxA ≠ ixRP := by decide
@[simp] theorem ix_pxA_ne_ixCn : pxA ≠ ixCn := by decide
@[simp] theorem ix_pxA_ne_ixT : pxA ≠ ixT := by decide
@[simp] theorem ix_pxA_ne_ixMa : pxA ≠ ixMa := by decide
@[simp] theorem ix_pxA_ne_ixMn : pxA ≠ ixMn := by decide
@[simp] theorem ix_pxA_ne_ixIa : pxA ≠ ixIa := by decide
@[simp] theorem ix_pxA_ne_ixIn : pxA ≠ ixIn := by decide
@[simp] theorem ix_pxA_ne_ixR : pxA ≠ ixR := by decide
@[simp] theorem ix_pxA_ne_ixG : pxA ≠ ixG := by decide
@[simp] theorem ix_pxA_ne_ixL : pxA ≠ ixL := by decide
@[simp] theorem ix_pxA_ne_ixT2 : pxA ≠ ixT2 := by decide
@[simp] theorem ix_pxA_ne_ixQ : pxA ≠ ixQ := by decide
@[simp] theorem ix_pxA_ne_ixD : pxA ≠ ixD := by decide
@[simp] theorem ix_pxA_ne_kFu : pxA ≠ kFu := by decide
@[simp] theorem ix_pxA_ne_kD : pxA ≠ kD := by decide
@[simp] theorem ix_pxA_ne_lFl : pxA ≠ lFl := by decide
@[simp] theorem ix_pxA_ne_lDh : pxA ≠ lDh := by decide
@[simp] theorem ix_pxA_ne_lDt : pxA ≠ lDt := by decide
@[simp] theorem ix_pxA_ne_lDg : pxA ≠ lDg := by decide
@[simp] theorem ix_pxA_ne_lDi : pxA ≠ lDi := by decide
@[simp] theorem ix_pxA_ne_lRp : pxA ≠ lRp := by decide
@[simp] theorem ix_pxA_ne_lRn : pxA ≠ lRn := by decide
@[simp] theorem ix_pxA_ne_lKb : pxA ≠ lKb := by decide
@[simp] theorem ix_pxA_ne_lFle : pxA ≠ lFle := by decide
@[simp] theorem ix_pxA_ne_lDir : pxA ≠ lDir := by decide
@[simp] theorem ix_pxK_ne_pxH : pxK ≠ pxH := by decide
@[simp] theorem ix_pxK_ne_pxA : pxK ≠ pxA := by decide
@[simp] theorem ix_pxK_ne_pxB : pxK ≠ pxB := by decide
@[simp] theorem ix_pxK_ne_pxX : pxK ≠ pxX := by decide
@[simp] theorem ix_pxK_ne_pxV : pxK ≠ pxV := by decide
@[simp] theorem ix_pxK_ne_pxR : pxK ≠ pxR := by decide
@[simp] theorem ix_pxK_ne_ixMI : pxK ≠ ixMI := by decide
@[simp] theorem ix_pxK_ne_ixRP : pxK ≠ ixRP := by decide
@[simp] theorem ix_pxK_ne_ixCn : pxK ≠ ixCn := by decide
@[simp] theorem ix_pxK_ne_ixT : pxK ≠ ixT := by decide
@[simp] theorem ix_pxK_ne_ixMa : pxK ≠ ixMa := by decide
@[simp] theorem ix_pxK_ne_ixMn : pxK ≠ ixMn := by decide
@[simp] theorem ix_pxK_ne_ixIa : pxK ≠ ixIa := by decide
@[simp] theorem ix_pxK_ne_ixIn : pxK ≠ ixIn := by decide
@[simp] theorem ix_pxK_ne_ixR : pxK ≠ ixR := by decide
@[simp] theorem ix_pxK_ne_ixG : pxK ≠ ixG := by decide
@[simp] theorem ix_pxK_ne_ixL : pxK ≠ ixL := by decide
@[simp] theorem ix_pxK_ne_ixT2 : pxK ≠ ixT2 := by decide
@[simp] theorem ix_pxK_ne_ixQ : pxK ≠ ixQ := by decide
@[simp] theorem ix_pxK_ne_ixD : pxK ≠ ixD := by decide
@[simp] theorem ix_pxK_ne_kFu : pxK ≠ kFu := by decide
@[simp] theorem ix_pxK_ne_kD : pxK ≠ kD := by decide
@[simp] theorem ix_pxK_ne_lFl : pxK ≠ lFl := by decide
@[simp] theorem ix_pxK_ne_lDh : pxK ≠ lDh := by decide
@[simp] theorem ix_pxK_ne_lDt : pxK ≠ lDt := by decide
@[simp] theorem ix_pxK_ne_lDg : pxK ≠ lDg := by decide
@[simp] theorem ix_pxK_ne_lDi : pxK ≠ lDi := by decide
@[simp] theorem ix_pxK_ne_lRp : pxK ≠ lRp := by decide
@[simp] theorem ix_pxK_ne_lRn : pxK ≠ lRn := by decide
@[simp] theorem ix_pxK_ne_lKb : pxK ≠ lKb := by decide
@[simp] theorem ix_pxK_ne_lFle : pxK ≠ lFle := by decide
@[simp] theorem ix_pxK_ne_lDir : pxK ≠ lDir := by decide
@[simp] theorem ix_pxB_ne_pxH : pxB ≠ pxH := by decide
@[simp] theorem ix_pxB_ne_pxA : pxB ≠ pxA := by decide
@[simp] theorem ix_pxB_ne_pxK : pxB ≠ pxK := by decide
@[simp] theorem ix_pxB_ne_pxX : pxB ≠ pxX := by decide
@[simp] theorem ix_pxB_ne_pxV : pxB ≠ pxV := by decide
@[simp] theorem ix_pxB_ne_pxR : pxB ≠ pxR := by decide
@[simp] theorem ix_pxB_ne_ixMI : pxB ≠ ixMI := by decide
@[simp] theorem ix_pxB_ne_ixRP : pxB ≠ ixRP := by decide
@[simp] theorem ix_pxB_ne_ixCn : pxB ≠ ixCn := by decide
@[simp] theorem ix_pxB_ne_ixT : pxB ≠ ixT := by decide
@[simp] theorem ix_pxB_ne_ixMa : pxB ≠ ixMa := by decide
@[simp] theorem ix_pxB_ne_ixMn : pxB ≠ ixMn := by decide
@[simp] theorem ix_pxB_ne_ixIa : pxB ≠ ixIa := by decide
@[simp] theorem ix_pxB_ne_ixIn : pxB ≠ ixIn := by decide
@[simp] theorem ix_pxB_ne_ixR : pxB ≠ ixR := by decide
@[simp] theorem ix_pxB_ne_ixG : pxB ≠ ixG := by decide
@[simp] theorem ix_pxB_ne_ixL : pxB ≠ ixL := by decide
@[simp] theorem ix_pxB_ne_ixT2 : pxB ≠ ixT2 := by decide
@[simp] theorem ix_pxB_ne_ixQ : pxB ≠ ixQ := by decide
@[simp] theorem ix_pxB_ne_ixD : pxB ≠ ixD := by decide
@[simp] theorem ix_pxB_ne_kFu : pxB ≠ kFu := by decide
@[simp] theorem ix_pxB_ne_kD : pxB ≠ kD := by decide
@[simp] theorem ix_pxB_ne_lFl : pxB ≠ lFl := by decide
@[simp] theorem ix_pxB_ne_lDh : pxB ≠ lDh := by decide
@[simp] theorem ix_pxB_ne_lDt : pxB ≠ lDt := by decide
@[simp] theorem ix_pxB_ne_lDg : pxB ≠ lDg := by decide
@[simp] theorem ix_pxB_ne_lDi : pxB ≠ lDi := by decide
@[simp] theorem ix_pxB_ne_lRp : pxB ≠ lRp := by decide
@[simp] theorem ix_pxB_ne_lRn : pxB ≠ lRn := by decide
@[simp] theorem ix_pxB_ne_lKb : pxB ≠ lKb := by decide
@[simp] theorem ix_pxB_ne_lFle : pxB ≠ lFle := by decide
@[simp] theorem ix_pxB_ne_lDir : pxB ≠ lDir := by decide
@[simp] theorem ix_pxX_ne_pxH : pxX ≠ pxH := by decide
@[simp] theorem ix_pxX_ne_pxA : pxX ≠ pxA := by decide
@[simp] theorem ix_pxX_ne_pxK : pxX ≠ pxK := by decide
@[simp] theorem ix_pxX_ne_pxB : pxX ≠ pxB := by decide
@[simp] theorem ix_pxX_ne_pxV : pxX ≠ pxV := by decide
@[simp] theorem ix_pxX_ne_pxR : pxX ≠ pxR := by decide
@[simp] theorem ix_pxX_ne_ixMI : pxX ≠ ixMI := by decide
@[simp] theorem ix_pxX_ne_ixRP : pxX ≠ ixRP := by decide
@[simp] theorem ix_pxX_ne_ixCn : pxX ≠ ixCn := by decide
@[simp] theorem ix_pxX_ne_ixT : pxX ≠ ixT := by decide
@[simp] theorem ix_pxX_ne_ixMa : pxX ≠ ixMa := by decide
@[simp] theorem ix_pxX_ne_ixMn : pxX ≠ ixMn := by decide
@[simp] theorem ix_pxX_ne_ixIa : pxX ≠ ixIa := by decide
@[simp] theorem ix_pxX_ne_ixIn : pxX ≠ ixIn := by decide
@[simp] theorem ix_pxX_ne_ixR : pxX ≠ ixR := by decide
@[simp] theorem ix_pxX_ne_ixG : pxX ≠ ixG := by decide
@[simp] theorem ix_pxX_ne_ixL : pxX ≠ ixL := by decide
@[simp] theorem ix_pxX_ne_ixT2 : pxX ≠ ixT2 := by decide
@[simp] theorem ix_pxX_ne_ixQ : pxX ≠ ixQ := by decide
@[simp] theorem ix_pxX_ne_ixD : pxX ≠ ixD := by decide
@[simp] theorem ix_pxX_ne_kFu : pxX ≠ kFu := by decide
@[simp] theorem ix_pxX_ne_kD : pxX ≠ kD := by decide
@[simp] theorem ix_pxX_ne_lFl : pxX ≠ lFl := by decide
@[simp] theorem ix_pxX_ne_lDh : pxX ≠ lDh := by decide
@[simp] theorem ix_pxX_ne_lDt : pxX ≠ lDt := by decide
@[simp] theorem ix_pxX_ne_lDg : pxX ≠ lDg := by decide
@[simp] theorem ix_pxX_ne_lDi : pxX ≠ lDi := by decide
@[simp] theorem ix_pxX_ne_lRp : pxX ≠ lRp := by decide
@[simp] theorem ix_pxX_ne_lRn : pxX ≠ lRn := by decide
@[simp] theorem ix_pxX_ne_lKb : pxX ≠ lKb := by decide
@[simp] theorem ix_pxX_ne_lFle : pxX ≠ lFle := by decide
@[simp] theorem ix_pxX_ne_lDir : pxX ≠ lDir := by decide
@[simp] theorem ix_pxV_ne_pxH : pxV ≠ pxH := by decide
@[simp] theorem ix_pxV_ne_pxA : pxV ≠ pxA := by decide
@[simp] theorem ix_pxV_ne_pxK : pxV ≠ pxK := by decide
@[simp] theorem ix_pxV_ne_pxB : pxV ≠ pxB := by decide
@[simp] theorem ix_pxV_ne_pxX : pxV ≠ pxX := by decide
@[simp] theorem ix_pxV_ne_pxR : pxV ≠ pxR := by decide
@[simp] theorem ix_pxV_ne_ixMI : pxV ≠ ixMI := by decide
@[simp] theorem ix_pxV_ne_ixRP : pxV ≠ ixRP := by decide
@[simp] theorem ix_pxV_ne_ixCn : pxV ≠ ixCn := by decide
@[simp] theorem ix_pxV_ne_ixT : pxV ≠ ixT := by decide
@[simp] theorem ix_pxV_ne_ixMa : pxV ≠ ixMa := by decide
@[simp] theorem ix_pxV_ne_ixMn : pxV ≠ ixMn := by decide
@[simp] theorem ix_pxV_ne_ixIa : pxV ≠ ixIa := by decide
@[simp] theorem ix_pxV_ne_ixIn : pxV ≠ ixIn := by decide
@[simp] theorem ix_pxV_ne_ixR : pxV ≠ ixR := by decide
@[simp] theorem ix_pxV_ne_ixG : pxV ≠ ixG := by decide
@[simp] theorem ix_pxV_ne_ixL : pxV ≠ ixL := by decide
@[simp] theorem ix_pxV_ne_ixT2 : pxV ≠ ixT2 := by decide
@[simp] theorem ix_pxV_ne_ixQ : pxV ≠ ixQ := by decide
@[simp] theorem ix_pxV_ne_ixD : pxV ≠ ixD := by decide
@[simp] theorem ix_pxV_ne_kFu : pxV ≠ kFu := by decide
@[simp] theorem ix_pxV_ne_kD : pxV ≠ kD := by decide
@[simp] theorem ix_pxV_ne_lFl : pxV ≠ lFl := by decide
@[simp] theorem ix_pxV_ne_lDh : pxV ≠ lDh := by decide
@[simp] theorem ix_pxV_ne_lDt : pxV ≠ lDt := by decide
@[simp] theorem ix_pxV_ne_lDg : pxV ≠ lDg := by decide
@[simp] theorem ix_pxV_ne_lDi : pxV ≠ lDi := by decide
@[simp] theorem ix_pxV_ne_lRp : pxV ≠ lRp := by decide
@[simp] theorem ix_pxV_ne_lRn : pxV ≠ lRn := by decide
@[simp] theorem ix_pxV_ne_lKb : pxV ≠ lKb := by decide
@[simp] theorem ix_pxV_ne_lFle : pxV ≠ lFle := by decide
@[simp] theorem ix_pxV_ne_lDir : pxV ≠ lDir := by decide
@[simp] theorem ix_pxR_ne_pxH : pxR ≠ pxH := by decide
@[simp] theorem ix_pxR_ne_pxA : pxR ≠ pxA := by decide
@[simp] theorem ix_pxR_ne_pxK : pxR ≠ pxK := by decide
@[simp] theorem ix_pxR_ne_pxB : pxR ≠ pxB := by decide
@[simp] theorem ix_pxR_ne_pxX : pxR ≠ pxX := by decide
@[simp] theorem ix_pxR_ne_pxV : pxR ≠ pxV := by decide
@[simp] theorem ix_pxR_ne_ixMI : pxR ≠ ixMI := by decide
@[simp] theorem ix_pxR_ne_ixRP : pxR ≠ ixRP := by decide
@[simp] theorem ix_pxR_ne_ixCn : pxR ≠ ixCn := by decide
@[simp] theorem ix_pxR_ne_ixT : pxR ≠ ixT := by decide
@[simp] theorem ix_pxR_ne_ixMa : pxR ≠ ixMa := by decide
@[simp] theorem ix_pxR_ne_ixMn : pxR ≠ ixMn := by decide
@[simp] theorem ix_pxR_ne_ixIa : pxR ≠ ixIa := by decide
@[simp] theorem ix_pxR_ne_ixIn : pxR ≠ ixIn := by decide
@[simp] theorem ix_pxR_ne_ixR : pxR ≠ ixR := by decide
@[simp] theorem ix_pxR_ne_ixG : pxR ≠ ixG := by decide
@[simp] theorem ix_pxR_ne_ixL : pxR ≠ ixL := by decide
@[simp] theorem ix_pxR_ne_ixT2 : pxR ≠ ixT2 := by decide
@[simp] theorem ix_pxR_ne_ixQ : pxR ≠ ixQ := by decide
@[simp] theorem ix_pxR_ne_ixD : pxR ≠ ixD := by decide
@[simp] theorem ix_pxR_ne_kFu : pxR ≠ kFu := by decide
@[simp] theorem ix_pxR_ne_kD : pxR ≠ kD := by decide
@[simp] theorem ix_pxR_ne_lFl : pxR ≠ lFl := by decide
@[simp] theorem ix_pxR_ne_lDh : pxR ≠ lDh := by decide
@[simp] theorem ix_pxR_ne_lDt : pxR ≠ lDt := by decide
@[simp] theorem ix_pxR_ne_lDg : pxR ≠ lDg := by decide
@[simp] theorem ix_pxR_ne_lDi : pxR ≠ lDi := by decide
@[simp] theorem ix_pxR_ne_lRp : pxR ≠ lRp := by decide
@[simp] theorem ix_pxR_ne_lRn : pxR ≠ lRn := by decide
@[simp] theorem ix_pxR_ne_lKb : pxR ≠ lKb := by decide
@[simp] theorem ix_pxR_ne_lFle : pxR ≠ lFle := by decide
@[simp] theorem ix_pxR_ne_lDir : pxR ≠ lDir := by decide
@[simp] theorem ix_ixMI_ne_pxH : ixMI ≠ pxH := by decide
@[simp] theorem ix_ixMI_ne_pxA : ixMI ≠ pxA := by decide
@[simp] theorem ix_ixMI_ne_pxK : ixMI ≠ pxK := by decide
@[simp] theorem ix_ixMI_ne_pxB : ixMI ≠ pxB := by decide
@[simp] theorem ix_ixMI_ne_pxX : ixMI ≠ pxX := by decide
@[simp] theorem ix_ixMI_ne_pxV : ixMI ≠ pxV := by decide
@[simp] theorem ix_ixMI_ne_pxR : ixMI ≠ pxR := by decide
@[simp] theorem ix_ixMI_ne_ixRP : ixMI ≠ ixRP := by decide
@[simp] theorem ix_ixMI_ne_ixCn : ixMI ≠ ixCn := by decide
@[simp] theorem ix_ixMI_ne_ixT : ixMI ≠ ixT := by decide
@[simp] theorem ix_ixMI_ne_ixMa : ixMI ≠ ixMa := by decide
@[simp] theorem ix_ixMI_ne_ixMn : ixMI ≠ ixMn := by decide
@[simp] theorem ix_ixMI_ne_ixIa : ixMI ≠ ixIa := by decide
@[simp] theorem ix_ixMI_ne_ixIn : ixMI ≠ ixIn := by decide
@[simp] theorem ix_ixMI_ne_ixR : ixMI ≠ ixR := by decide
@[simp] theorem ix_ixMI_ne_ixG : ixMI ≠ ixG := by decide
@[simp] theorem ix_ixMI_ne_ixL : ixMI ≠ ixL := by decide
@[simp] theorem ix_ixMI_ne_ixT2 : ixMI ≠ ixT2 := by decide
@[simp] theorem ix_ixMI_ne_ixQ : ixMI ≠ ixQ := by decide
@[simp] theorem ix_ixMI_ne_ixD : ixMI ≠ ixD := by decide
@[simp] theorem ix_ixMI_ne_kFu : ixMI ≠ kFu := by decide
@[simp] theorem ix_ixMI_ne_kD : ixMI ≠ kD := by decide
@[simp] theorem ix_ixMI_ne_lFl : ixMI ≠ lFl := by decide
@[simp] theorem ix_ixMI_ne_lDh : ixMI ≠ lDh := by decide
@[simp] theorem ix_ixMI_ne_lDt : ixMI ≠ lDt := by decide
@[simp] theorem ix_ixMI_ne_lDg : ixMI ≠ lDg := by decide
@[simp] theorem ix_ixMI_ne_lDi : ixMI ≠ lDi := by decide
@[simp] theorem ix_ixMI_ne_lRp : ixMI ≠ lRp := by decide
@[simp] theorem ix_ixMI_ne_lRn : ixMI ≠ lRn := by decide
@[simp] theorem ix_ixMI_ne_lKb : ixMI ≠ lKb := by decide
@[simp] theorem ix_ixMI_ne_lFle : ixMI ≠ lFle := by decide
@[simp] theorem ix_ixMI_ne_lDir : ixMI ≠ lDir := by decide
@[simp] theorem ix_ixRP_ne_pxH : ixRP ≠ pxH := by decide
@[simp] theorem ix_ixRP_ne_pxA : ixRP ≠ pxA := by decide
@[simp] theorem ix_ixRP_ne_pxK : ixRP ≠ pxK := by decide
@[simp] theorem ix_ixRP_ne_pxB : ixRP ≠ pxB := by decide
@[simp] theorem ix_ixRP_ne_pxX : ixRP ≠ pxX := by decide
@[simp] theorem ix_ixRP_ne_pxV : ixRP ≠ pxV := by decide
@[simp] theorem ix_ixRP_ne_pxR : ixRP ≠ pxR := by decide
@[simp] theorem ix_ixRP_ne_ixMI : ixRP ≠ ixMI := by decide
@[simp] theorem ix_ixRP_ne_ixCn : ixRP ≠ ixCn := by decide
@[simp] theorem ix_ixRP_ne_ixT : ixRP ≠ ixT := by decide
@[simp] theorem ix_ixRP_ne_ixMa : ixRP ≠ ixMa := by decide
@[simp] theorem ix_ixRP_ne_ixMn : ixRP ≠ ixMn := by decide
@[simp] theorem ix_ixRP_ne_ixIa : ixRP ≠ ixIa := by decide
@[simp] theorem ix_ixRP_ne_ixIn : ixRP ≠ ixIn := by decide
@[simp] theorem ix_ixRP_ne_ixR : ixRP ≠ ixR := by decide
@[simp] theorem ix_ixRP_ne_ixG : ixRP ≠ ixG := by decide
@[simp] theorem ix_ixRP_ne_ixL : ixRP ≠ ixL := by decide
@[simp] theorem ix_ixRP_ne_ixT2 : ixRP ≠ ixT2 := by decide
@[simp] theorem ix_ixRP_ne_ixQ : ixRP ≠ ixQ := by decide
@[simp] theorem ix_ixRP_ne_ixD : ixRP ≠ ixD := by decide
@[simp] theorem ix_ixRP_ne_kFu : ixRP ≠ kFu := by decide
@[simp] theorem ix_ixRP_ne_kD : ixRP ≠ kD := by decide
@[simp] theorem ix_ixRP_ne_lFl : ixRP ≠ lFl := by decide
@[simp] theorem ix_ixRP_ne_lDh : ixRP ≠ lDh := by decide
@[simp] theorem ix_ixRP_ne_lDt : ixRP ≠ lDt := by decide
@[simp] theorem ix_ixRP_ne_lDg : ixRP ≠ lDg := by decide
@[simp] theorem ix_ixRP_ne_lDi : ixRP ≠ lDi := by decide
@[simp] theorem ix_ixRP_ne_lRp : ixRP ≠ lRp := by decide
@[simp] theorem ix_ixRP_ne_lRn : ixRP ≠ lRn := by decide
@[simp] theorem ix_ixRP_ne_lKb : ixRP ≠ lKb := by decide
@[simp] theorem ix_ixRP_ne_lFle : ixRP ≠ lFle := by decide
@[simp] theorem ix_ixRP_ne_lDir : ixRP ≠ lDir := by decide
@[simp] theorem ix_ixCn_ne_pxH : ixCn ≠ pxH := by decide
@[simp] theorem ix_ixCn_ne_pxA : ixCn ≠ pxA := by decide
@[simp] theorem ix_ixCn_ne_pxK : ixCn ≠ pxK := by decide
@[simp] theorem ix_ixCn_ne_pxB : ixCn ≠ pxB := by decide
@[simp] theorem ix_ixCn_ne_pxX : ixCn ≠ pxX := by decide
@[simp] theorem ix_ixCn_ne_pxV : ixCn ≠ pxV := by decide
@[simp] theorem ix_ixCn_ne_pxR : ixCn ≠ pxR := by decide
@[simp] theorem ix_ixCn_ne_ixMI : ixCn ≠ ixMI := by decide
@[simp] theorem ix_ixCn_ne_ixRP : ixCn ≠ ixRP := by decide
@[simp] theorem ix_ixCn_ne_ixT : ixCn ≠ ixT := by decide
@[simp] theorem ix_ixCn_ne_ixMa : ixCn ≠ ixMa := by decide
@[simp] theorem ix_ixCn_ne_ixMn : ixCn ≠ ixMn := by decide
@[simp] theorem ix_ixCn_ne_ixIa : ixCn ≠ ixIa := by decide
@[simp] theorem ix_ixCn_ne_ixIn : ixCn ≠ ixIn := by decide
@[simp] theorem ix_ixCn_ne_ixR : ixCn ≠ ixR := by decide
@[simp] theorem ix_ixCn_ne_ixG : ixCn ≠ ixG := by decide
@[simp] theorem ix_ixCn_ne_ixL : ixCn ≠ ixL := by decide
@[simp] theorem ix_ixCn_ne_ixT2 : ixCn ≠ ixT2 := by decide
@[simp] theorem ix_ixCn_ne_ixQ : ixCn ≠ ixQ := by decide
@[simp] theorem ix_ixCn_ne_ixD : ixCn ≠ ixD := by decide
@[simp] theorem ix_ixCn_ne_kFu : ixCn ≠ kFu := by decide
@[simp] theorem ix_ixCn_ne_kD : ixCn ≠ kD := by decide
@[simp] theorem ix_ixCn_ne_lFl : ixCn ≠ lFl := by decide
@[simp] theorem ix_ixCn_ne_lDh : ixCn ≠ lDh := by decide
@[simp] theorem ix_ixCn_ne_lDt : ixCn ≠ lDt := by decide
@[simp] theorem ix_ixCn_ne_lDg : ixCn ≠ lDg := by decide
@[simp] theorem ix_ixCn_ne_lDi : ixCn ≠ lDi := by decide
@[simp] theorem ix_ixCn_ne_lRp : ixCn ≠ lRp := by decide
@[simp] theorem ix_ixCn_ne_lRn : ixCn ≠ lRn := by decide
@[simp] theorem ix_ixCn_ne_lKb : ixCn ≠ lKb := by decide
@[simp] theorem ix_ixCn_ne_lFle : ixCn ≠ lFle := by decide
@[simp] theorem ix_ixCn_ne_lDir : ixCn ≠ lDir := by decide
@[simp] theorem ix_ixT_ne_pxH : ixT ≠ pxH := by decide
@[simp] theorem ix_ixT_ne_pxA : ixT ≠ pxA := by decide
@[simp] theorem ix_ixT_ne_pxK : ixT ≠ pxK := by decide
@[simp] theorem ix_ixT_ne_pxB : ixT ≠ pxB := by decide
@[simp] theorem ix_ixT_ne_pxX : ixT ≠ pxX := by decide
@[simp] theorem ix_ixT_ne_pxV : ixT ≠ pxV := by decide
@[simp] theorem ix_ixT_ne_pxR : ixT ≠ pxR := by decide
@[simp] theorem ix_ixT_ne_ixMI : ixT ≠ ixMI := by decide
@[simp] theorem ix_ixT_ne_ixRP : ixT ≠ ixRP := by decide
@[simp] theorem ix_ixT_ne_ixCn : ixT ≠ ixCn := by decide
@[simp] theorem ix_ixT_ne_ixMa : ixT ≠ ixMa := by decide
@[simp] theorem ix_ixT_ne_ixMn : ixT ≠ ixMn := by decide
@[simp] theorem ix_ixT_ne_ixIa : ixT ≠ ixIa := by decide
@[simp] theorem ix_ixT_ne_ixIn : ixT ≠ ixIn := by decide
@[simp] theorem ix_ixT_ne_ixR : ixT ≠ ixR := by decide
@[simp] theorem ix_ixT_ne_ixG : ixT ≠ ixG := by decide
@[simp] theorem ix_ixT_ne_ixL : ixT ≠ ixL := by decide
@[simp] theorem ix_ixT_ne_ixT2 : ixT ≠ ixT2 := by decide
@[simp] theorem ix_ixT_ne_ixQ : ixT ≠ ixQ := by decide
@[simp] theorem ix_ixT_ne_ixD : ixT ≠ ixD := by decide
@[simp] theorem ix_ixT_ne_kFu : ixT ≠ kFu := by decide
@[simp] theorem ix_ixT_ne_kD : ixT ≠ kD := by decide
@[simp] theorem ix_ixT_ne_lFl : ixT ≠ lFl := by decide
@[simp] theorem ix_ixT_ne_lDh : ixT ≠ lDh := by decide
@[simp] theorem ix_ixT_ne_lDt : ixT ≠ lDt := by decide
@[simp] theorem ix_ixT_ne_lDg : ixT ≠ lDg := by decide
@[simp] theorem ix_ixT_ne_lDi : ixT ≠ lDi := by decide
@[simp] theorem ix_ixT_ne_lRp : ixT ≠ lRp := by decide
@[simp] theorem ix_ixT_ne_lRn : ixT ≠ lRn := by decide
@[simp] theorem ix_ixT_ne_lKb : ixT ≠ lKb := by decide
@[simp] theorem ix_ixT_ne_lFle : ixT ≠ lFle := by decide
@[simp] theorem ix_ixT_ne_lDir : ixT ≠ lDir := by decide
@[simp] theorem ix_ixMa_ne_pxH : ixMa ≠ pxH := by decide
@[simp] theorem ix_ixMa_ne_pxA : ixMa ≠ pxA := by decide
@[simp] theorem ix_ixMa_ne_pxK : ixMa ≠ pxK := by decide
@[simp] theorem ix_ixMa_ne_pxB : ixMa ≠ pxB := by decide
@[simp] theorem ix_ixMa_ne_pxX : ixMa ≠ pxX := by decide
@[simp] theorem ix_ixMa_ne_pxV : ixMa ≠ pxV := by decide
@[simp] theorem ix_ixMa_ne_pxR : ixMa ≠ pxR := by decide
@[simp] theorem ix_ixMa_ne_ixMI : ixMa ≠ ixMI := by decide
@[simp] theorem ix_ixMa_ne_ixRP : ixMa ≠ ixRP := by decide
@[simp] theorem ix_ixMa_ne_ixCn : ixMa ≠ ixCn := by decide
@[simp] theorem ix_ixMa_ne_ixT : ixMa ≠ ixT := by decide
@[simp] theorem ix_ixMa_ne_ixMn : ixMa ≠ ixMn := by decide
@[simp] theorem ix_ixMa_ne_ixIa : ixMa ≠ ixIa := by decide
@[simp] theorem ix_ixMa_ne_ixIn : ixMa ≠ ixIn := by decide
@[simp] theorem ix_ixMa_ne_ixR : ixMa ≠ ixR := by decide
@[simp] theorem ix_ixMa_ne_ixG : ixMa ≠ ixG := by decide
@[simp] theorem ix_ixMa_ne_ixL : ixMa ≠ ixL := by decide
@[simp] theorem ix_ixMa_ne_ixT2 : ixMa ≠ ixT2 := by decide
@[simp] theorem ix_ixMa_ne_ixQ : ixMa ≠ ixQ := by decide
@[simp] theorem ix_ixMa_ne_ixD : ixMa ≠ ixD := by decide
@[simp] theorem ix_ixMa_ne_kFu : ixMa ≠ kFu := by decide
@[simp] theorem ix_ixMa_ne_kD : ixMa ≠ kD := by decide
@[simp] theorem ix_ixMa_ne_lFl : ixMa ≠ lFl := by decide
@[simp] theorem ix_ixMa_ne_lDh : ixMa ≠ lDh := by decide
@[simp] theorem ix_ixMa_ne_lDt : ixMa ≠ lDt := by decide
@[simp] theorem ix_ixMa_ne_lDg : ixMa ≠ lDg := by decide
@[simp] theorem ix_ixMa_ne_lDi : ixMa ≠ lDi := by decide
@[simp] theorem ix_ixMa_ne_lRp : ixMa ≠ lRp := by decide
@[simp] theorem ix_ixMa_ne_lRn : ixMa ≠ lRn := by decide
@[simp] theorem ix_ixMa_ne_lKb : ixMa ≠ lKb := by decide
@[simp] theorem ix_ixMa_ne_lFle : ixMa ≠ lFle := by decide
@[simp] theorem ix_ixMa_ne_lDir : ixMa ≠ lDir := by decide
@[simp] theorem ix_ixMn_ne_pxH : ixMn ≠ pxH := by decide
@[simp] theorem ix_ixMn_ne_pxA : ixMn ≠ pxA := by decide
@[simp] theorem ix_ixMn_ne_pxK : ixMn ≠ pxK := by decide
@[simp] theorem ix_ixMn_ne_pxB : ixMn ≠ pxB := by decide
@[simp] theorem ix_ixMn_ne_pxX : ixMn ≠ pxX := by decide
@[simp] theorem ix_ixMn_ne_pxV : ixMn ≠ pxV := by decide
@[simp] theorem ix_ixMn_ne_pxR : ixMn ≠ pxR := by decide
@[simp] theorem ix_ixMn_ne_ixMI : ixMn ≠ ixMI := by decide
@[simp] theorem ix_ixMn_ne_ixRP : ixMn ≠ ixRP := by decide
@[simp] theorem ix_ixMn_ne_ixCn : ixMn ≠ ixCn := by decide
@[simp] theorem ix_ixMn_ne_ixT : ixMn ≠ ixT := by decide
@[simp] theorem ix_ixMn_ne_ixMa : ixMn ≠ ixMa := by decide
@[simp] theorem ix_ixMn_ne_ixIa : ixMn ≠ ixIa := by decide
@[simp] theorem ix_ixMn_ne_ixIn : ixMn ≠ ixIn := by decide
@[simp] theorem ix_ixMn_ne_ixR : ixMn ≠ ixR := by decide
@[simp] theorem ix_ixMn_ne_ixG : ixMn ≠ ixG := by decide
@[simp] theorem ix_ixMn_ne_ixL : ixMn ≠ ixL := by decide
@[simp] theorem ix_ixMn_ne_ixT2 : ixMn ≠ ixT2 := by decide
@[simp] theorem ix_ixMn_ne_ixQ : ixMn ≠ ixQ := by decide
@[simp] theorem ix_ixMn_ne_ixD : ixMn ≠ ixD := by decide
@[simp] theorem ix_ixMn_ne_kFu : ixMn ≠ kFu := by decide
@[simp] theorem ix_ixMn_ne_kD : ixMn ≠ kD := by decide
@[simp] theorem ix_ixMn_ne_lFl : ixMn ≠ lFl := by decide
@[simp] theorem ix_ixMn_ne_lDh : ixMn ≠ lDh := by decide
@[simp] theorem ix_ixMn_ne_lDt : ixMn ≠ lDt := by decide
@[simp] theorem ix_ixMn_ne_lDg : ixMn ≠ lDg := by decide
@[simp] theorem ix_ixMn_ne_lDi : ixMn ≠ lDi := by decide
@[simp] theorem ix_ixMn_ne_lRp : ixMn ≠ lRp := by decide
@[simp] theorem ix_ixMn_ne_lRn : ixMn ≠ lRn := by decide
@[simp] theorem ix_ixMn_ne_lKb : ixMn ≠ lKb := by decide
@[simp] theorem ix_ixMn_ne_lFle : ixMn ≠ lFle := by decide
@[simp] theorem ix_ixMn_ne_lDir : ixMn ≠ lDir := by decide
@[simp] theorem ix_ixIa_ne_pxH : ixIa ≠ pxH := by decide
@[simp] theorem ix_ixIa_ne_pxA : ixIa ≠ pxA := by decide
@[simp] theorem ix_ixIa_ne_pxK : ixIa ≠ pxK := by decide
@[simp] theorem ix_ixIa_ne_pxB : ixIa ≠ pxB := by decide
@[simp] theorem ix_ixIa_ne_pxX : ixIa ≠ pxX := by decide
@[simp] theorem ix_ixIa_ne_pxV : ixIa ≠ pxV := by decide
@[simp] theorem ix_ixIa_ne_pxR : ixIa ≠ pxR := by decide
@[simp] theorem ix_ixIa_ne_ixMI : ixIa ≠ ixMI := by decide
@[simp] theorem ix_ixIa_ne_ixRP : ixIa ≠ ixRP := by decide
@[simp] theorem ix_ixIa_ne_ixCn : ixIa ≠ ixCn := by decide
@[simp] theorem ix_ixIa_ne_ixT : ixIa ≠ ixT := by decide
@[simp] theorem ix_ixIa_ne_ixMa : ixIa ≠ ixMa := by decide
@[simp] theorem ix_ixIa_ne_ixMn : ixIa ≠ ixMn := by decide
@[simp] theorem ix_ixIa_ne_ixIn : ixIa ≠ ixIn := by decide
@[simp] theorem ix_ixIa_ne_ixR : ixIa ≠ ixR := by decide
@[simp] theorem ix_ixIa_ne_ixG : ixIa ≠ ixG := by decide
@[simp] theorem ix_ixIa_ne_ixL : ixIa ≠ ixL := by decide
@[simp] theorem ix_ixIa_ne_ixT2 : ixIa ≠ ixT2 := by decide
@[simp] theorem ix_ixIa_ne_ixQ : ixIa ≠ ixQ := by decide
@[simp] theorem ix_ixIa_ne_ixD : ixIa ≠ ixD := by decide
@[simp] theorem ix_ixIa_ne_kFu : ixIa ≠ kFu := by decide
@[simp] theorem ix_ixIa_ne_kD : ixIa ≠ kD := by decide
@[simp] theorem ix_ixIa_ne_lFl : ixIa ≠ lFl := by decide
@[simp] theorem ix_ixIa_ne_lDh : ixIa ≠ lDh := by decide
@[simp] theorem ix_ixIa_ne_lDt : ixIa ≠ lDt := by decide
@[simp] theorem ix_ixIa_ne_lDg : ixIa ≠ lDg := by decide
@[simp] theorem ix_ixIa_ne_lDi : ixIa ≠ lDi := by decide
@[simp] theorem ix_ixIa_ne_lRp : ixIa ≠ lRp := by decide
@[simp] theorem ix_ixIa_ne_lRn : ixIa ≠ lRn := by decide
@[simp] theorem ix_ixIa_ne_lKb : ixIa ≠ lKb := by decide
@[simp] theorem ix_ixIa_ne_lFle : ixIa ≠ lFle := by decide
@[simp] theorem ix_ixIa_ne_lDir : ixIa ≠ lDir := by decide
@[simp] theorem ix_ixIn_ne_pxH : ixIn ≠ pxH := by decide
@[simp] theorem ix_ixIn_ne_pxA : ixIn ≠ pxA := by decide
@[simp] theorem ix_ixIn_ne_pxK : ixIn ≠ pxK := by decide
@[simp] theorem ix_ixIn_ne_pxB : ixIn ≠ pxB := by decide
@[simp] theorem ix_ixIn_ne_pxX : ixIn ≠ pxX := by decide
@[simp] theorem ix_ixIn_ne_pxV : ixIn ≠ pxV := by decide
@[simp] theorem ix_ixIn_ne_pxR : ixIn ≠ pxR := by decide
@[simp] theorem ix_ixIn_ne_ixMI : ixIn ≠ ixMI := by decide
@[simp] theorem ix_ixIn_ne_ixRP : ixIn ≠ ixRP := by decide
@[simp] theorem ix_ixIn_ne_ixCn : ixIn ≠ ixCn := by decide
@[simp] theorem ix_ixIn_ne_ixT : ixIn ≠ ixT := by decide
@[simp] theorem ix_ixIn_ne_ixMa : ixIn ≠ ixMa := by decide
@[simp] theorem ix_ixIn_ne_ixMn : ixIn ≠ ixMn := by decide
@[simp] theorem ix_ixIn_ne_ixIa : ixIn ≠ ixIa := by decide
@[simp] theorem ix_ixIn_ne_ixR : ixIn ≠ ixR := by decide
@[simp] theorem ix_ixIn_ne_ixG : ixIn ≠ ixG := by decide
@[simp] theorem ix_ixIn_ne_ixL : ixIn ≠ ixL := by decide
@[simp] theorem ix_ixIn_ne_ixT2 : ixIn ≠ ixT2 := by decide
@[simp] theorem ix_ixIn_ne_ixQ : ixIn ≠ ixQ := by decide
@[simp] theorem ix_ixIn_ne_ixD : ixIn ≠ ixD := by decide
@[simp] theorem ix_ixIn_ne_kFu : ixIn ≠ kFu := by decide
@[simp] theorem ix_ixIn_ne_kD : ixIn ≠ kD := by decide
@[simp] theorem ix_ixIn_ne_lFl : ixIn ≠ lFl := by decide
@[simp] theorem ix_ixIn_ne_lDh : ixIn ≠ lDh := by decide
@[simp] theorem ix_ixIn_ne_lDt : ixIn ≠ lDt := by decide
@[simp] theorem ix_ixIn_ne_lDg : ixIn ≠ lDg := by decide
@[simp] theorem ix_ixIn_ne_lDi : ixIn ≠ lDi := by decide
@[simp] theorem ix_ixIn_ne_lRp : ixIn ≠ lRp := by decide
@[simp] theorem ix_ixIn_ne_lRn : ixIn ≠ lRn := by decide
@[simp] theorem ix_ixIn_ne_lKb : ixIn ≠ lKb := by decide
@[simp] theorem ix_ixIn_ne_lFle : ixIn ≠ lFle := by decide
@[simp] theorem ix_ixIn_ne_lDir : ixIn ≠ lDir := by decide
@[simp] theorem ix_ixR_ne_pxH : ixR ≠ pxH := by decide
@[simp] theorem ix_ixR_ne_pxA : ixR ≠ pxA := by decide
@[simp] theorem ix_ixR_ne_pxK : ixR ≠ pxK := by decide
@[simp] theorem ix_ixR_ne_pxB : ixR ≠ pxB := by decide
@[simp] theorem ix_ixR_ne_pxX : ixR ≠ pxX := by decide
@[simp] theorem ix_ixR_ne_pxV : ixR ≠ pxV := by decide
@[simp] theorem ix_ixR_ne_pxR : ixR ≠ pxR := by decide
@[simp] theorem ix_ixR_ne_ixMI : ixR ≠ ixMI := by decide
@[simp] theorem ix_ixR_ne_ixRP : ixR ≠ ixRP := by decide
@[simp] theorem ix_ixR_ne_ixCn : ixR ≠ ixCn := by decide
@[simp] theorem ix_ixR_ne_ixT : ixR ≠ ixT := by decide
@[simp] theorem ix_ixR_ne_ixMa : ixR ≠ ixMa := by decide
@[simp] theorem ix_ixR_ne_ixMn : ixR ≠ ixMn := by decide
@[simp] theorem ix_ixR_ne_ixIa : ixR ≠ ixIa := by decide
@[simp] theorem ix_ixR_ne_ixIn : ixR ≠ ixIn := by decide
@[simp] theorem ix_ixR_ne_ixG : ixR ≠ ixG := by decide
@[simp] theorem ix_ixR_ne_ixL : ixR ≠ ixL := by decide
@[simp] theorem ix_ixR_ne_ixT2 : ixR ≠ ixT2 := by decide
@[simp] theorem ix_ixR_ne_ixQ : ixR ≠ ixQ := by decide
@[simp] theorem ix_ixR_ne_ixD : ixR ≠ ixD := by decide
@[simp] theorem ix_ixR_ne_kFu : ixR ≠ kFu := by decide
@[simp] theorem ix_ixR_ne_kD : ixR ≠ kD := by decide
@[simp] theorem ix_ixR_ne_lFl : ixR ≠ lFl := by decide
@[simp] theorem ix_ixR_ne_lDh : ixR ≠ lDh := by decide
@[simp] theorem ix_ixR_ne_lDt : ixR ≠ lDt := by decide
@[simp] theorem ix_ixR_ne_lDg : ixR ≠ lDg := by decide
@[simp] theorem ix_ixR_ne_lDi : ixR ≠ lDi := by decide
@[simp] theorem ix_ixR_ne_lRp : ixR ≠ lRp := by decide
@[simp] theorem ix_ixR_ne_lRn : ixR ≠ lRn := by decide
@[simp] theorem ix_ixR_ne_lKb : ixR ≠ lKb := by decide
@[simp] theorem ix_ixR_ne_lFle : ixR ≠ lFle := by decide
@[simp] theorem ix_ixR_ne_lDir : ixR ≠ lDir := by decide
@[simp] theorem ix_ixG_ne_pxH : ixG ≠ pxH := by decide
@[simp] theorem ix_ixG_ne_pxA : ixG ≠ pxA := by decide
@[simp] theorem ix_ixG_ne_pxK : ixG ≠ pxK := by decide
@[simp] theorem ix_ixG_ne_pxB : ixG ≠ pxB := by decide
@[simp] theorem ix_ixG_ne_pxX : ixG ≠ pxX := by decide
@[simp] theorem ix_ixG_ne_pxV : ixG ≠ pxV := by decide
@[simp] theorem ix_ixG_ne_pxR : ixG ≠ pxR := by decide
@[simp] theorem ix_ixG_ne_ixMI : ixG ≠ ixMI := by decide
@[simp] theorem ix_ixG_ne_ixRP : ixG ≠ ixRP := by decide
@[simp] theorem ix_ixG_ne_ixCn : ixG ≠ ixCn := by decide
@[simp] theorem ix_ixG_ne_ixT : ixG ≠ ixT := by decide
@[simp] theorem ix_ixG_ne_ixMa : ixG ≠ ixMa := by decide
@[simp] theorem ix_ixG_ne_ixMn : ixG ≠ ixMn := by decide
@[simp] theorem ix_ixG_ne_ixIa : ixG ≠ ixIa := by decide
@[simp] theorem ix_ixG_ne_ixIn : ixG ≠ ixIn := by decide
@[simp] theorem ix_ixG_ne_ixR : ixG ≠ ixR := by decide
@[simp] theorem ix_ixG_ne_ixL : ixG ≠ ixL := by decide
@[simp] theorem ix_ixG_ne_ixT2 : ixG ≠ ixT2 := by decide
@[simp] theorem ix_ixG_ne_ixQ : ixG ≠ ixQ := by decide
@[simp] theorem ix_ixG_ne_ixD : ixG ≠ ixD := by decide
@[simp] theorem ix_ixG_ne_kFu : ixG ≠ kFu := by decide
@[simp] theorem ix_ixG_ne_kD : ixG ≠ kD := by decide
@[simp] theorem ix_ixG_ne_lFl : ixG ≠ lFl := by decide
@[simp] theorem ix_ixG_ne_lDh : ixG ≠ lDh := by decide
@[simp] theorem ix_ixG_ne_lDt : ixG ≠ lDt := by decide
@[simp] theorem ix_ixG_ne_lDg : ixG ≠ lDg := by decide
@[simp] theorem ix_ixG_ne_lDi : ixG ≠ lDi := by decide
@[simp] theorem ix_ixG_ne_lRp : ixG ≠ lRp := by decide
@[simp] theorem ix_ixG_ne_lRn : ixG ≠ lRn := by decide
@[simp] theorem ix_ixG_ne_lKb : ixG ≠ lKb := by decide
@[simp] theorem ix_ixG_ne_lFle : ixG ≠ lFle := by decide
@[simp] theorem ix_ixG_ne_lDir : ixG ≠ lDir := by decide
@[simp] theorem ix_ixL_ne_pxH : ixL ≠ pxH := by decide
@[simp] theorem ix_ixL_ne_pxA : ixL ≠ pxA := by decide
@[simp] theorem ix_ixL_ne_pxK : ixL ≠ pxK := by decide
@[simp] theorem ix_ixL_ne_pxB : ixL ≠ pxB := by decide
@[simp] theorem ix_ixL_ne_pxX : ixL ≠ pxX := by decide
@[simp] theorem ix_ixL_ne_pxV : ixL ≠ pxV := by decide
@[simp] theorem ix_ixL_ne_pxR : ixL ≠ pxR := by decide
@[simp] theorem ix_ixL_ne_ixMI : ixL ≠ ixMI := by decide
@[simp] theorem ix_ixL_ne_ixRP : ixL ≠ ixRP := by decide
@[simp] theorem ix_ixL_ne_ixCn : ixL ≠ ixCn := by decide
@[simp] theorem ix_ixL_ne_ixT : ixL ≠ ixT := by decide
@[simp] theorem ix_ixL_ne_ixMa : ixL ≠ ixMa := by decide
@[simp] theorem ix_ixL_ne_ixMn : ixL ≠ ixMn := by decide
@[simp] theorem ix_ixL_ne_ixIa : ixL ≠ ixIa := by decide
@[simp] theorem ix_ixL_ne_ixIn : ixL ≠ ixIn := by decide
@[simp] theorem ix_ixL_ne_ixR : ixL ≠ ixR := by decide
@[simp] theorem ix_ixL_ne_ixG : ixL ≠ ixG := by decide
@[simp] theorem ix_ixL_ne_ixT2 : ixL ≠ ixT2 := by decide
@[simp] theorem ix_ixL_ne_ixQ : ixL ≠ ixQ := by decide
@[simp] theorem ix_ixL_ne_ixD : ixL ≠ ixD := by decide
@[simp] theorem ix_ixL_ne_kFu : ixL ≠ kFu := by decide
@[simp] theorem ix_ixL_ne_kD : ixL ≠ kD := by decide
@[simp] theorem ix_ixL_ne_lFl : ixL ≠ lFl := by decide
@[simp] theorem ix_ixL_ne_lDh : ixL ≠ lDh := by decide
@[simp] theorem ix_ixL_ne_lDt : ixL ≠ lDt := by decide
@[simp] theorem ix_ixL_ne_lDg : ixL ≠ lDg := by decide
@[simp] theorem ix_ixL_ne_lDi : ixL ≠ lDi := by decide
@[simp] theorem ix_ixL_ne_lRp : ixL ≠ lRp := by decide
@[simp] theorem ix_ixL_ne_lRn : ixL ≠ lRn := by decide
@[simp] theorem ix_ixL_ne_lKb : ixL ≠ lKb := by decide
@[simp] theorem ix_ixL_ne_lFle : ixL ≠ lFle := by decide
@[simp] theorem ix_ixL_ne_lDir : ixL ≠ lDir := by decide
@[simp] theorem ix_ixT2_ne_pxH : ixT2 ≠ pxH := by decide
@[simp] theorem ix_ixT2_ne_pxA : ixT2 ≠ pxA := by decide
@[simp] theorem ix_ixT2_ne_pxK : ixT2 ≠ pxK := by decide
@[simp] theorem ix_ixT2_ne_pxB : ixT2 ≠ pxB := by decide
@[simp] theorem ix_ixT2_ne_pxX : ixT2 ≠ pxX := by decide
@[simp] theorem ix_ixT2_ne_pxV : ixT2 ≠ pxV := by decide
@[simp] theorem ix_ixT2_ne_pxR : ixT2 ≠ pxR := by decide
@[simp] theorem ix_ixT2_ne_ixMI : ixT2 ≠ ixMI := by decide
@[simp] theorem ix_ixT2_ne_ixRP : ixT2 ≠ ixRP := by decide
@[simp] theorem ix_ixT2_ne_ixCn : ixT2 ≠ ixCn := by decide
@[simp] theorem ix_ixT2_ne_ixT : ixT2 ≠ ixT := by decide
@[simp] theorem ix_ixT2_ne_ixMa : ixT2 ≠ ixMa := by decide
@[simp] theorem ix_ixT2_ne_ixMn : ixT2 ≠ ixMn := by decide
@[simp] theorem ix_ixT2_ne_ixIa : ixT2 ≠ ixIa := by decide
@[simp] theorem ix_ixT2_ne_ixIn : ixT2 ≠ ixIn := by decide
@[simp] theorem ix_ixT2_ne_ixR : ixT2 ≠ ixR := by decide
@[simp] theorem ix_ixT2_ne_ixG : ixT2 ≠ ixG := by decide
@[simp] theorem ix_ixT2_ne_ixL : ixT2 ≠ ixL := by decide
@[simp] theorem ix_ixT2_ne_ixQ : ixT2 ≠ ixQ := by decide
@[simp] theorem ix_ixT2_ne_ixD : ixT2 ≠ ixD := by decide
@[simp] theorem ix_ixT2_ne_kFu : ixT2 ≠ kFu := by decide
@[simp] theorem ix_ixT2_ne_kD : ixT2 ≠ kD := by decide
@[simp] theorem ix_ixT2_ne_lFl : ixT2 ≠ lFl := by decide
@[simp] theorem ix_ixT2_ne_lDh : ixT2 ≠ lDh := by decide
@[simp] theorem ix_ixT2_ne_lDt : ixT2 ≠ lDt := by decide
@[simp] theorem ix_ixT2_ne_lDg : ixT2 ≠ lDg := by decide
@[simp] theorem ix_ixT2_ne_lDi : ixT2 ≠ lDi := by decide
@[simp] theorem ix_ixT2_ne_lRp : ixT2 ≠ lRp := by decide
@[simp] theorem ix_ixT2_ne_lRn : ixT2 ≠ lRn := by decide
@[simp] theorem ix_ixT2_ne_lKb : ixT2 ≠ lKb := by decide
@[simp] theorem ix_ixT2_ne_lFle : ixT2 ≠ lFle := by decide
@[simp] theorem ix_ixT2_ne_lDir : ixT2 ≠ lDir := by decide
@[simp] theorem ix_ixQ_ne_pxH : ixQ ≠ pxH := by decide
@[simp] theorem ix_ixQ_ne_pxA : ixQ ≠ pxA := by decide
@[simp] theorem ix_ixQ_ne_pxK : ixQ ≠ pxK := by decide
@[simp] theorem ix_ixQ_ne_pxB : ixQ ≠ pxB := by decide
@[simp] theorem ix_ixQ_ne_pxX : ixQ ≠ pxX := by decide
@[simp] theorem ix_ixQ_ne_pxV : ixQ ≠ pxV := by decide
@[simp] theorem ix_ixQ_ne_pxR : ixQ ≠ pxR := by decide
@[simp] theorem ix_ixQ_ne_ixMI : ixQ ≠ ixMI := by decide
@[simp] theorem ix_ixQ_ne_ixRP : ixQ ≠ ixRP := by decide
@[simp] theorem ix_ixQ_ne_ixCn : ixQ ≠ ixCn := by decide
@[simp] theorem ix_ixQ_ne_ixT : ixQ ≠ ixT := by decide
@[simp] theorem ix_ixQ_ne_ixMa : ixQ ≠ ixMa := by decide
@[simp] theorem ix_ixQ_ne_ixMn : ixQ ≠ ixMn := by decide
@[simp] theorem ix_ixQ_ne_ixIa : ixQ ≠ ixIa := by decide
@[simp] theorem ix_ixQ_ne_ixIn : ixQ ≠ ixIn := by decide
@[simp] theorem ix_ixQ_ne_ixR : ixQ ≠ ixR := by decide
@[simp] theorem ix_ixQ_ne_ixG : ixQ ≠ ixG := by decide
@[simp] theorem ix_ixQ_ne_ixL : ixQ ≠ ixL := by decide
@[simp] theorem ix_ixQ_ne_ixT2 : ixQ ≠ ixT2 := by decide
@[simp] theorem ix_ixQ_ne_ixD : ixQ ≠ ixD := by decide
@[simp] theorem ix_ixQ_ne_kFu : ixQ ≠ kFu := by decide
@[simp] theorem ix_ixQ_ne_kD : ixQ ≠ kD := by decide
@[simp] theorem ix_ixQ_ne_lFl : ixQ ≠ lFl := by decide
@[simp] theorem ix_ixQ_ne_lDh : ixQ ≠ lDh := by decide
@[simp] theorem ix_ixQ_ne_lDt : ixQ ≠ lDt := by decide
@[simp] theorem ix_ixQ_ne_lDg : ixQ ≠ lDg := by decide
@[simp] theorem ix_ixQ_ne_lDi : ixQ ≠ lDi := by decide
@[simp] theorem ix_ixQ_ne_lRp : ixQ ≠ lRp := by decide
@[simp] theorem ix_ixQ_ne_lRn : ixQ ≠ lRn := by decide
@[simp] theorem ix_ixQ_ne_lKb : ixQ ≠ lKb := by decide
@[simp] theorem ix_ixQ_ne_lFle : ixQ ≠ lFle := by decide
@[simp] theorem ix_ixQ_ne_lDir : ixQ ≠ lDir := by decide
@[simp] theorem ix_ixD_ne_pxH : ixD ≠ pxH := by decide
@[simp] theorem ix_ixD_ne_pxA : ixD ≠ pxA := by decide
@[simp] theorem ix_ixD_ne_pxK : ixD ≠ pxK := by decide
@[simp] theorem ix_ixD_ne_pxB : ixD ≠ pxB := by decide
@[simp] theorem ix_ixD_ne_pxX : ixD ≠ pxX := by decide
@[simp] theorem ix_ixD_ne_pxV : ixD ≠ pxV := by decide
@[simp] theorem ix_ixD_ne_pxR : ixD ≠ pxR := by decide
@[simp] theorem ix_ixD_ne_ixMI : ixD ≠ ixMI := by decide
@[simp] theorem ix_ixD_ne_ixRP : ixD ≠ ixRP := by decide
@[simp] theorem ix_ixD_ne_ixCn : ixD ≠ ixCn := by decide
@[simp] theorem ix_ixD_ne_ixT : ixD ≠ ixT := by decide
@[simp] theorem ix_ixD_ne_ixMa : ixD ≠ ixMa := by decide
@[simp] theorem ix_ixD_ne_ixMn : ixD ≠ ixMn := by decide
@[simp] theorem ix_ixD_ne_ixIa : ixD ≠ ixIa := by decide
@[simp] theorem ix_ixD_ne_ixIn : ixD ≠ ixIn := by decide
@[simp] theorem ix_ixD_ne_ixR : ixD ≠ ixR := by decide
@[simp] theorem ix_ixD_ne_ixG : ixD ≠ ixG := by decide
@[simp] theorem ix_ixD_ne_ixL : ixD ≠ ixL := by decide
@[simp] theorem ix_ixD_ne_ixT2 : ixD ≠ ixT2 := by decide
@[simp] theorem ix_ixD_ne_ixQ : ixD ≠ ixQ := by decide
@[simp] theorem ix_ixD_ne_kFu : ixD ≠ kFu := by decide
@[simp] theorem ix_ixD_ne_kD : ixD ≠ kD := by decide
@[simp] theorem ix_ixD_ne_lFl : ixD ≠ lFl := by decide
@[simp] theorem ix_ixD_ne_lDh : ixD ≠ lDh := by decide
@[simp] theorem ix_ixD_ne_lDt : ixD ≠ lDt := by decide
@[simp] theorem ix_ixD_ne_lDg : ixD ≠ lDg := by decide
@[simp] theorem ix_ixD_ne_lDi : ixD ≠ lDi := by decide
@[simp] theorem ix_ixD_ne_lRp : ixD ≠ lRp := by decide
@[simp] theorem ix_ixD_ne_lRn : ixD ≠ lRn := by decide
@[simp] theorem ix_ixD_ne_lKb : ixD ≠ lKb := by decide
@[simp] theorem ix_ixD_ne_lFle : ixD ≠ lFle := by decide
@[simp] theorem ix_ixD_ne_lDir : ixD ≠ lDir := by decide
@[simp] theorem ix_kFu_ne_pxH : kFu ≠ pxH := by decide
@[simp] theorem ix_kFu_ne_pxA : kFu ≠ pxA := by decide
@[simp] theorem ix_kFu_ne_pxK : kFu ≠ pxK := by decide
@[simp] theorem ix_kFu_ne_pxB : kFu ≠ pxB := by decide
@[simp] theorem ix_kFu_ne_pxX : kFu ≠ pxX := by decide
@[simp] theorem ix_kFu_ne_pxV : kFu ≠ pxV := by decide
@[simp] theorem ix_kFu_ne_pxR : kFu ≠ pxR := by decide
@[simp] theorem ix_kFu_ne_ixMI : kFu ≠ ixMI := by decide
@[simp] theorem ix_kFu_ne_ixRP : kFu ≠ ixRP := by decide
@[simp] theorem ix_kFu_ne_ixCn : kFu ≠ ixCn := by decide
@[simp] theorem ix_kFu_ne_ixT : kFu ≠ ixT := by decide
@[simp] theorem ix_kFu_ne_ixMa : kFu ≠ ixMa := by decide
@[simp] theorem ix_kFu_ne_ixMn : kFu ≠ ixMn := by decide
@[simp] theorem ix_kFu_ne_ixIa : kFu ≠ ixIa := by decide
@[simp] theorem ix_kFu_ne_ixIn : kFu ≠ ixIn := by decide
@[simp] theorem ix_kFu_ne_ixR : kFu ≠ ixR := by decide
@[simp] theorem ix_kFu_ne_ixG : kFu ≠ ixG := by decide
@[simp] theorem ix_kFu_ne_ixL : kFu ≠ ixL := by decide
@[simp] theorem ix_kFu_ne_ixT2 : kFu ≠ ixT2 := by decide
@[simp] theorem ix_kFu_ne_ixQ : kFu ≠ ixQ := by decide
@[simp] theorem ix_kFu_ne_ixD : kFu ≠ ixD := by decide
@[simp] theorem ix_kD_ne_pxH : kD ≠ pxH := by decide
@[simp] theorem ix_kD_ne_pxA : kD ≠ pxA := by decide
@[simp] theorem ix_kD_ne_pxK : kD ≠ pxK := by decide
@[simp] theorem ix_kD_ne_pxB : kD ≠ pxB := by decide
@[simp] theorem ix_kD_ne_pxX : kD ≠ pxX := by decide
@[simp] theorem ix_kD_ne_pxV : kD ≠ pxV := by decide
@[simp] theorem ix_kD_ne_pxR : kD ≠ pxR := by decide
@[simp] theorem ix_kD_ne_ixMI : kD ≠ ixMI := by decide
@[simp] theorem ix_kD_ne_ixRP : kD ≠ ixRP := by decide
@[simp] theorem ix_kD_ne_ixCn : kD ≠ ixCn := by decide
@[simp] theorem ix_kD_ne_ixT : kD ≠ ixT := by decide
@[simp] theorem ix_kD_ne_ixMa : kD ≠ ixMa := by decide
@[simp] theorem ix_kD_ne_ixMn : kD ≠ ixMn := by decide
@[simp] theorem ix_kD_ne_ixIa : kD ≠ ixIa := by decide
@[simp] theorem ix_kD_ne_ixIn : kD ≠ ixIn := by decide
@[simp] theorem ix_kD_ne_ixR : kD ≠ ixR := by decide
@[simp] theorem ix_kD_ne_ixG : kD ≠ ixG := by decide
@[simp] theorem ix_kD_ne_ixL : kD ≠ ixL := by decide
@[simp] theorem ix_kD_ne_ixT2 : kD ≠ ixT2 := by decide
@[simp] theorem ix_kD_ne_ixQ : kD ≠ ixQ := by decide
@[simp] theorem ix_kD_ne_ixD : kD ≠ ixD := by decide
@[simp] theorem ix_lFl_ne_pxH : lFl ≠ pxH := by decide
@[simp] theorem ix_lFl_ne_pxA : lFl ≠ pxA := by decide
@[simp] theorem ix_lFl_ne_pxK : lFl ≠ pxK := by decide
@[simp] theorem ix_lFl_ne_pxB : lFl ≠ pxB := by decide
@[simp] theorem ix_lFl_ne_pxX : lFl ≠ pxX := by decide
@[simp] theorem ix_lFl_ne_pxV : lFl ≠ pxV := by decide
@[simp] theorem ix_lFl_ne_pxR : lFl ≠ pxR := by decide
@[simp] theorem ix_lFl_ne_ixMI : lFl ≠ ixMI := by decide
@[simp] theorem ix_lFl_ne_ixRP : lFl ≠ ixRP := by decide
@[simp] theorem ix_lFl_ne_ixCn : lFl ≠ ixCn := by decide
@[simp] theorem ix_lFl_ne_ixT : lFl ≠ ixT := by decide
@[simp] theorem ix_lFl_ne_ixMa : lFl ≠ ixMa := by decide
@[simp] theorem ix_lFl_ne_ixMn : lFl ≠ ixMn := by decide
@[simp] theorem ix_lFl_ne_ixIa : lFl ≠ ixIa := by decide
@[simp] theorem ix_lFl_ne_ixIn : lFl ≠ ixIn := by decide
@[simp] theorem ix_lFl_ne_ixR : lFl ≠ ixR := by decide
@[simp] theorem ix_lFl_ne_ixG : lFl ≠ ixG := by decide
@[simp] theorem ix_lFl_ne_ixL : lFl ≠ ixL := by decide
@[simp] theorem ix_lFl_ne_ixT2 : lFl ≠ ixT2 := by decide
@[simp] theorem ix_lFl_ne_ixQ : lFl ≠ ixQ := by decide
@[simp] theorem ix_lFl_ne_ixD : lFl ≠ ixD := by decide
@[simp] theorem ix_lDh_ne_pxH : lDh ≠ pxH := by decide
@[simp] theorem ix_lDh_ne_pxA : lDh ≠ pxA := by decide
@[simp] theorem ix_lDh_ne_pxK : lDh ≠ pxK := by decide
@[simp] theorem ix_lDh_ne_pxB : lDh ≠ pxB := by decide
@[simp] theorem ix_lDh_ne_pxX : lDh ≠ pxX := by decide
@[simp] theorem ix_lDh_ne_pxV : lDh ≠ pxV := by decide
@[simp] theorem ix_lDh_ne_pxR : lDh ≠ pxR := by decide
@[simp] theorem ix_lDh_ne_ixMI : lDh ≠ ixMI := by decide
@[simp] theorem ix_lDh_ne_ixRP : lDh ≠ ixRP := by decide
@[simp] theorem ix_lDh_ne_ixCn : lDh ≠ ixCn := by decide
@[simp] theorem ix_lDh_ne_ixT : lDh ≠ ixT := by decide
@[simp] theorem ix_lDh_ne_ixMa : lDh ≠ ixMa := by decide
@[simp] theorem ix_lDh_ne_ixMn : lDh ≠ ixMn := by decide
@[simp] theorem ix_lDh_ne_ixIa : lDh ≠ ixIa := by decide
@[simp] theorem ix_lDh_ne_ixIn : lDh ≠ ixIn := by decide
@[simp] theorem ix_lDh_ne_ixR : lDh ≠ ixR := by decide
@[simp] theorem ix_lDh_ne_ixG : lDh ≠ ixG := by decide
@[simp] theorem ix_lDh_ne_ixL : lDh ≠ ixL := by decide
@[simp] theorem ix_lDh_ne_ixT2 : lDh ≠ ixT2 := by decide
@[simp] theorem ix_lDh_ne_ixQ : lDh ≠ ixQ := by decide
@[simp] theorem ix_lDh_ne_ixD : lDh ≠ ixD := by decide
@[simp] theorem ix_lDt_ne_pxH : lDt ≠ pxH := by decide
@[simp] theorem ix_lDt_ne_pxA : lDt ≠ pxA := by decide
@[simp] theorem ix_lDt_ne_pxK : lDt ≠ pxK := by decide
@[simp] theorem ix_lDt_ne_pxB : lDt ≠ pxB := by decide
@[simp] theorem ix_lDt_ne_pxX : lDt ≠ pxX := by decide
@[simp] theorem ix_lDt_ne_pxV : lDt ≠ pxV := by decide
@[simp] theorem ix_lDt_ne_pxR : lDt ≠ pxR := by decide
@[simp] theorem ix_lDt_ne_ixMI : lDt ≠ ixMI := by decide
@[simp] theorem ix_lDt_ne_ixRP : lDt ≠ ixRP := by decide
@[simp] theorem ix_lDt_ne_ixCn : lDt ≠ ixCn := by decide
@[simp] theorem ix_lDt_ne_ixT : lDt ≠ ixT := by decide
@[simp] theorem ix_lDt_ne_ixMa : lDt ≠ ixMa := by decide
@[simp] theorem ix_lDt_ne_ixMn : lDt ≠ ixMn := by decide
@[simp] theorem ix_lDt_ne_ixIa : lDt ≠ ixIa := by decide
@[simp] theorem ix_lDt_ne_ixIn : lDt ≠ ixIn := by decide
@[simp] theorem ix_lDt_ne_ixR : lDt ≠ ixR := by decide
@[simp] theorem ix_lDt_ne_ixG : lDt ≠ ixG := by decide
@[simp] theorem ix_lDt_ne_ixL : lDt ≠ ixL := by decide
@[simp] theorem ix_lDt_ne_ixT2 : lDt ≠ ixT2 := by decide
@[simp] theorem ix_lDt_ne_ixQ : lDt ≠ ixQ := by decide
@[simp] theorem ix_lDt_ne_ixD : lDt ≠ ixD := by decide
@[simp] theorem ix_lDg_ne_pxH : lDg ≠ pxH := by decide
@[simp] theorem ix_lDg_ne_pxA : lDg ≠ pxA := by decide
@[simp] theorem ix_lDg_ne_pxK : lDg ≠ pxK := by decide
@[simp] theorem ix_lDg_ne_pxB : lDg ≠ pxB := by decide
@[simp] theorem ix_lDg_ne_pxX : lDg ≠ pxX := by decide
@[simp] theorem ix_lDg_ne_pxV : lDg ≠ pxV := by decide
@[simp] theorem ix_lDg_ne_pxR : lDg ≠ pxR := by decide
@[simp] theorem ix_lDg_ne_ixMI : lDg ≠ ixMI := by decide
@[simp] theorem ix_lDg_ne_ixRP : lDg ≠ ixRP := by decide
@[simp] theorem ix_lDg_ne_ixCn : lDg ≠ ixCn := by decide
@[simp] theorem ix_lDg_ne_ixT : lDg ≠ ixT := by decide
@[simp] theorem ix_lDg_ne_ixMa : lDg ≠ ixMa := by decide
@[simp] theorem ix_lDg_ne_ixMn : lDg ≠ ixMn := by decide
@[simp] theorem ix_lDg_ne_ixIa : lDg ≠ ixIa := by decide
@[simp] theorem ix_lDg_ne_ixIn : lDg ≠ ixIn := by decide
@[simp] theorem ix_lDg_ne_ixR : lDg ≠ ixR := by decide
@[simp] theorem ix_lDg_ne_ixG : lDg ≠ ixG := by decide
@[simp] theorem ix_lDg_ne_ixL : lDg ≠ ixL := by decide
@[simp] theorem ix_lDg_ne_ixT2 : lDg ≠ ixT2 := by decide
@[simp] theorem ix_lDg_ne_ixQ : lDg ≠ ixQ := by decide
@[simp] theorem ix_lDg_ne_ixD : lDg ≠ ixD := by decide
@[simp] theorem ix_lDi_ne_pxH : lDi ≠ pxH := by decide
@[simp] theorem ix_lDi_ne_pxA : lDi ≠ pxA := by decide
@[simp] theorem ix_lDi_ne_pxK : lDi ≠ pxK := by decide
@[simp] theorem ix_lDi_ne_pxB : lDi ≠ pxB := by decide
@[simp] theorem ix_lDi_ne_pxX : lDi ≠ pxX := by decide
@[simp] theorem ix_lDi_ne_pxV : lDi ≠ pxV := by decide
@[simp] theorem ix_lDi_ne_pxR : lDi ≠ pxR := by decide
@[simp] theorem ix_lDi_ne_ixMI : lDi ≠ ixMI := by decide
@[simp] theorem ix_lDi_ne_ixRP : lDi ≠ ixRP := by decide
@[simp] theorem ix_lDi_ne_ixCn : lDi ≠ ixCn := by decide
@[simp] theorem ix_lDi_ne_ixT : lDi ≠ ixT := by decide
@[simp] theorem ix_lDi_ne_ixMa : lDi ≠ ixMa := by decide
@[simp] theorem ix_lDi_ne_ixMn : lDi ≠ ixMn := by decide
@[simp] theorem ix_lDi_ne_ixIa : lDi ≠ ixIa := by decide
@[simp] theorem ix_lDi_ne_ixIn : lDi ≠ ixIn := by decide
@[simp] theorem ix_lDi_ne_ixR : lDi ≠ ixR := by decide
@[simp] theorem ix_lDi_ne_ixG : lDi ≠ ixG := by decide
@[simp] theorem ix_lDi_ne_ixL : lDi ≠ ixL := by decide
@[simp] theorem ix_lDi_ne_ixT2 : lDi ≠ ixT2 := by decide
@[simp] theorem ix_lDi_ne_ixQ : lDi ≠ ixQ := by decide
@[simp] theorem ix_lDi_ne_ixD : lDi ≠ ixD := by decide
@[simp] theorem ix_lRp_ne_pxH : lRp ≠ pxH := by decide
@[simp] theorem ix_lRp_ne_pxA : lRp ≠ pxA := by decide
@[simp] theorem ix_lRp_ne_pxK : lRp ≠ pxK := by decide
@[simp] theorem ix_lRp_ne_pxB : lRp ≠ pxB := by decide
@[simp] theorem ix_lRp_ne_pxX : lRp ≠ pxX := by decide
@[simp] theorem ix_lRp_ne_pxV : lRp ≠ pxV := by decide
@[simp] theorem ix_lRp_ne_pxR : lRp ≠ pxR := by decide
@[simp] theorem ix_lRp_ne_ixMI : lRp ≠ ixMI := by decide
@[simp] theorem ix_lRp_ne_ixRP : lRp ≠ ixRP := by decide
@[simp] theorem ix_lRp_ne_ixCn : lRp ≠ ixCn := by decide
@[simp] theorem ix_lRp_ne_ixT : lRp ≠ ixT := by decide
@[simp] theorem ix_lRp_ne_ixMa : lRp ≠ ixMa := by decide
@[simp] theorem ix_lRp_ne_ixMn : lRp ≠ ixMn := by decide
@[simp] theorem ix_lRp_ne_ixIa : lRp ≠ ixIa := by decide
@[simp] theorem ix_lRp_ne_ixIn : lRp ≠ ixIn := by decide
@[simp] theorem ix_lRp_ne_ixR : lRp ≠ ixR := by decide
@[simp] theorem ix_lRp_ne_ixG : lRp ≠ ixG := by decide
@[simp] theorem ix_lRp_ne_ixL : lRp ≠ ixL := by decide
@[simp] theorem ix_lRp_ne_ixT2 : lRp ≠ ixT2 := by decide
@[simp] theorem ix_lRp_ne_ixQ : lRp ≠ ixQ := by decide
@[simp] theorem ix_lRp_ne_ixD : lRp ≠ ixD := by decide
@[simp] theorem ix_lRn_ne_pxH : lRn ≠ pxH := by decide
@[simp] theorem ix_lRn_ne_pxA : lRn ≠ pxA := by decide
@[simp] theorem ix_lRn_ne_pxK : lRn ≠ pxK := by decide
@[simp] theorem ix_lRn_ne_pxB : lRn ≠ pxB := by decide
@[simp] theorem ix_lRn_ne_pxX : lRn ≠ pxX := by decide
@[simp] theorem ix_lRn_ne_pxV : lRn ≠ pxV := by decide
@[simp] theorem ix_lRn_ne_pxR : lRn ≠ pxR := by decide
@[simp] theorem ix_lRn_ne_ixMI : lRn ≠ ixMI := by decide
@[simp] theorem ix_lRn_ne_ixRP : lRn ≠ ixRP := by decide
@[simp] theorem ix_lRn_ne_ixCn : lRn ≠ ixCn := by decide
@[simp] theorem ix_lRn_ne_ixT : lRn ≠ ixT := by decide
@[simp] theorem ix_lRn_ne_ixMa : lRn ≠ ixMa := by decide
@[simp] theorem ix_lRn_ne_ixMn : lRn ≠ ixMn := by decide
@[simp] theorem ix_lRn_ne_ixIa : lRn ≠ ixIa := by decide
@[simp] theorem ix_lRn_ne_ixIn : lRn ≠ ixIn := by decide
@[simp] theorem ix_lRn_ne_ixR : lRn ≠ ixR := by decide
@[simp] theorem ix_lRn_ne_ixG : lRn ≠ ixG := by decide
@[simp] theorem ix_lRn_ne_ixL : lRn ≠ ixL := by decide
@[simp] theorem ix_lRn_ne_ixT2 : lRn ≠ ixT2 := by decide
@[simp] theorem ix_lRn_ne_ixQ : lRn ≠ ixQ := by decide
@[simp] theorem ix_lRn_ne_ixD : lRn ≠ ixD := by decide
@[simp] theorem ix_lKb_ne_pxH : lKb ≠ pxH := by decide
@[simp] theorem ix_lKb_ne_pxA : lKb ≠ pxA := by decide
@[simp] theorem ix_lKb_ne_pxK : lKb ≠ pxK := by decide
@[simp] theorem ix_lKb_ne_pxB : lKb ≠ pxB := by decide
@[simp] theorem ix_lKb_ne_pxX : lKb ≠ pxX := by decide
@[simp] theorem ix_lKb_ne_pxV : lKb ≠ pxV := by decide
@[simp] theorem ix_lKb_ne_pxR : lKb ≠ pxR := by decide
@[simp] theorem ix_lKb_ne_ixMI : lKb ≠ ixMI := by decide
@[simp] theorem ix_lKb_ne_ixRP : lKb ≠ ixRP := by decide
@[simp] theorem ix_lKb_ne_ixCn : lKb ≠ ixCn := by decide
@[simp] theorem ix_lKb_ne_ixT : lKb ≠ ixT := by decide
@[simp] theorem ix_lKb_ne_ixMa : lKb ≠ ixMa := by decide
@[simp] theorem ix_lKb_ne_ixMn : lKb ≠ ixMn := by decide
@[simp] theorem ix_lKb_ne_ixIa : lKb ≠ ixIa := by decide
@[simp] theorem ix_lKb_ne_ixIn : lKb ≠ ixIn := by decide
@[simp] theorem ix_lKb_ne_ixR : lKb ≠ ixR := by decide
@[simp] theorem ix_lKb_ne_ixG : lKb ≠ ixG := by decide
@[simp] theorem ix_lKb_ne_ixL : lKb ≠ ixL := by decide
@[simp] theorem ix_lKb_ne_ixT2 : lKb ≠ ixT2 := by decide
@[simp] theorem ix_lKb_ne_ixQ : lKb ≠ ixQ := by decide
@[simp] theorem ix_lKb_ne_ixD : lKb ≠ ixD := by decide
@[simp] theorem ix_lFle_ne_pxH : lFle ≠ pxH := by decide
@[simp] theorem ix_lFle_ne_pxA : lFle ≠ pxA := by decide
@[simp] theorem ix_lFle_ne_pxK : lFle ≠ pxK := by decide
@[simp] theorem ix_lFle_ne_pxB : lFle ≠ pxB := by decide
@[simp] theorem ix_lFle_ne_pxX : lFle ≠ pxX := by decide
@[simp] theorem ix_lFle_ne_pxV : lFle ≠ pxV := by decide
@[simp] theorem ix_lFle_ne_pxR : lFle ≠ pxR := by decide
@[simp] theorem ix_lFle_ne_ixMI : lFle ≠ ixMI := by decide
@[simp] theorem ix_lFle_ne_ixRP : lFle ≠ ixRP := by decide
@[simp] theorem ix_lFle_ne_ixCn : lFle ≠ ixCn := by decide
@[simp] theorem ix_lFle_ne_ixT : lFle ≠ ixT := by decide
@[simp] theorem ix_lFle_ne_ixMa : lFle ≠ ixMa := by decide
@[simp] theorem ix_lFle_ne_ixMn : lFle ≠ ixMn := by decide
@[simp] theorem ix_lFle_ne_ixIa : lFle ≠ ixIa := by decide
@[simp] theorem ix_lFle_ne_ixIn : lFle ≠ ixIn := by decide
@[simp] theorem ix_lFle_ne_ixR : lFle ≠ ixR := by decide
@[simp] theorem ix_lFle_ne_ixG : lFle ≠ ixG := by decide
@[simp] theorem ix_lFle_ne_ixL : lFle ≠ ixL := by decide
@[simp] theorem ix_lFle_ne_ixT2 : lFle ≠ ixT2 := by decide
@[simp] theorem ix_lFle_ne_ixQ : lFle ≠ ixQ := by decide
@[simp] theorem ix_lFle_ne_ixD : lFle ≠ ixD := by decide
@[simp] theorem ix_lDir_ne_pxH : lDir ≠ pxH := by decide
@[simp] theorem ix_lDir_ne_pxA : lDir ≠ pxA := by decide
@[simp] theorem ix_lDir_ne_pxK : lDir ≠ pxK := by decide
@[simp] theorem ix_lDir_ne_pxB : lDir ≠ pxB := by decide
@[simp] theorem ix_lDir_ne_pxX : lDir ≠ pxX := by decide
@[simp] theorem ix_lDir_ne_pxV : lDir ≠ pxV := by decide
@[simp] theorem ix_lDir_ne_pxR : lDir ≠ pxR := by decide
@[simp] theorem ix_lDir_ne_ixMI : lDir ≠ ixMI := by decide
@[simp] theorem ix_lDir_ne_ixRP : lDir ≠ ixRP := by decide
@[simp] theorem ix_lDir_ne_ixCn : lDir ≠ ixCn := by decide
@[simp] theorem ix_lDir_ne_ixT : lDir ≠ ixT := by decide
@[simp] theorem ix_lDir_ne_ixMa : lDir ≠ ixMa := by decide
@[simp] theorem ix_lDir_ne_ixMn : lDir ≠ ixMn := by decide
@[simp] theorem ix_lDir_ne_ixIa : lDir ≠ ixIa := by decide
@[simp] theorem ix_lDir_ne_ixIn : lDir ≠ ixIn := by decide
@[simp] theorem ix_lDir_ne_ixR : lDir ≠ ixR := by decide
@[simp] theorem ix_lDir_ne_ixG : lDir ≠ ixG := by decide
@[simp] theorem ix_lDir_ne_ixL : lDir ≠ ixL := by decide
@[simp] theorem ix_lDir_ne_ixT2 : lDir ≠ ixT2 := by decide
@[simp] theorem ix_lDir_ne_ixQ : lDir ≠ ixQ := by decide
@[simp] theorem ix_lDir_ne_ixD : lDir ≠ ixD := by decide

def pxParams : List MlS := [pxH, pxA, pxK]
def pxLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, pxB, pxX, pxV, pxR]

def pxCore : ProgHOL 64 :=
  .ite (.cmp .equal (vv pxK) (.const 0)) (.return (.op .add [vv pxH, .const 1]))
  (.ite (tagIsE pxH 6)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pxH)) (.seq eViewP
    (.seq (.assign .local pxB (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.assign .local pxX (.load .one (vv pxA)))
    (.seq (.call (some (some (.local, pxV), none)) ExI.fInst1F
        [.const (BitVec.ofNat 64 coreWalkFuel), vv pxB, vv pxX, .const 0])
    (.seq (.call (some (some (.local, pxR), none)) fPx
        [vv pxV, .op .add [vv pxA, .const 8], .op .sub [vv pxK, .const 1]])
      (.return (vv pxR)))))))))
    (.return (.const 0)))

def pxBody : ProgHOL 64 := prologue pxLocals pxCore

structure PxCodes (C : Ctx) : Prop where
  i1 : C.code.lookup ExI.fInst1F = some ([pFu, pH, ExI.pV, ExI.pD].map (fun p => (p, ShapeHOL.one)),
    ExI.fastBody C, .one)
  i1c : ExI.Codes C (ExI.body C)
  self : C.code.lookup fPx = some (pxParams.map (fun p => (p, ShapeHOL.one)), pxBody, .one)

def ixParams : List MlS := [kFu, kD, ixMI, ixRP, ixCn, ixT, ixMa, ixMn, ixIa, ixIn]
def ixLocals : List MlS := [ixR, ixG, ixL, ixT2, ixQ, ixD]

def ixCore : ProgHOL 64 :=
  .ite (.cmp .equal (vv ixMI) (vv ixRP)) (.return (.const 1))
  (.seq (.call (some (some (.local, ixR), none)) fPx [vv ixT, vv ixMa, vv ixMn])
  (.ite (.cmp .equal (vv ixR) (.const 0)) (.return (.const 0))
  (.seq (.call (some (some (.local, ixG), none)) ExG.fGaa
      [.const (BitVec.ofNat 64 coreWalkFuel), .op .sub [vv ixR, .const 1]])
  (.seq (.assign .local ixL (.load .one (vv ixG)))
  (.seq (.assign .local ixT2 (.cmp .lower (vv ixCn) (vv ixL)))
  (.seq (.assign .local ixQ (.op .add [vv ixL, .op .and [.op .sub [vv ixCn, vv ixL], .op .sub [.const 0, vv ixT2]]]))
  (.seq (.call (some (some (.local, ixD), none)) fDl
      [vv kFu, vv kD, .op .add [.op .add [vv ixG, .const 8], .shift .lsl (vv ixQ) (.const 3)],
        .op .sub [vv ixL, vv ixQ], vv ixIa, vv ixIn])
    (.return (vv ixD)))))))))

def ixBody : ProgHOL 64 := prologue ixLocals ixCore

section
variable {σ : Type}

theorem px_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ pxLocals → (ctxEnv C ++ pxParams.zip vals).get x = none :=
  Knot.params_none C pxLocals pxParams vals (by decide) (by decide)

theorem ix_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ixLocals → (ctxEnv C ++ ixParams.zip vals).get x = none :=
  Knot.params_none C ixLocals ixParams vals (by decide) (by decide)

theorem px_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : PxCodes C) :
    ∀ (as : List EIdx) (h : EIdx) (qa : Nat) (H : List (BitVec 64)) (s : AState), C.H <+: H →
      (∀ j (hj : j < as.length), H[qa + j]? = some (Enc.idxW as[j])) → as.length < 2 ^ 63 →
      SpecR (σ := σ) (Pre (ctxH C H) s (pxParams.zip [Enc.idxW h, cellA C qa, BitVec.ofNat 64 as.length])) pxBody s
        (piResidual h as) (UD.PostO (ctxH C H)) := by
  intro as
  induction as with
  | nil =>
    intro h qa H s hp ha hla
    refine specR_prologue (UD.postO_locals _) (px_none _ _) ?_
    unfold pxCore
    rw [piResidual]
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, pxParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ (optW (some h)) (by simp +decide [sev, Env.get, pxParams, ctxEnv, optWG])
      (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | cons a as ih =>
    intro h qa H s hp ha hla
    refine specR_prologue (UD.postO_locals _) (px_none _ _) ?_
    unfold pxCore
    rw [piResidual]
    have hne := ofNat_succ_ne as.length (by simp at hla; omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, pxParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine Knot.specR_tagIteV pxH h 6 (by decide) (by decide) (by simp +decide [Env.get, pxParams, ctxEnv])
      (fun htg => ?_) (fun htg => ?_)
    · rw [if_pos (show (h.tag == ETag.forallE) = true by simp [htg, ETag.forallE])]
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv pxH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, pxParams, ctxEnv]) ?_
      refine specR_viewP (C := ctxH C H) h (by simp) (by simp +decide [Env.get] <;> rfl)
        (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
      have h6 : v.tagN = 6 := by rw [htn, htg]; rfl
      obtain ⟨ty, b, rfl⟩ : ∃ ty b, v = .forallE ty b := by
        cases v <;> simp [ENodeView.tagN] at h6 ⊢
      have hvb : s.store.viewBind h = some (ty, b) := viewBind_of_view_forallE (by rw [htg]; rfl) hv
      refine specR_runBind (by rw [viewBind_run, hvb]) ?_
      dsimp only
      refine specR_loadI' pxB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW b) [] []) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H) pxX (vv pxA) qa (Enc.idxW a) (ha 0 (by simp) : H[qa]? = some (Enc.idxW a))
        (by decide) (by simp +decide [Env.get, pxParams, ctxEnv]; rfl) ?_
      refine ILP.callE_spec (C := ctxH C H) pxV ExI.fInst1F [pFu, pH, ExI.pV, ExI.pD]
        [.const (BitVec.ofNat 64 coreWalkFuel), vv pxB, vv pxX, .const 0] (ExI.fastBody C)
        [BitVec.ofNat 64 coreWalkFuel, Enc.idxW b, Enc.idxW a, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.i1
        ⟨rfl, by simp, by simp, rfl, trivial⟩
        (ExI.fast_spec ra (ctxH C H) (ctxOK_H hok H) (ExIS.codes_H C H hc.i1c) s coreWalkFuel b a 0
          CV.coreWalkFuel_lt (by decide)) (fun b2 s2 => ?_)
      refine specR_congr (m' := piResidual b2 as >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H) pxR fPx pxParams
        [vv pxV, .op .add [vv pxA, .const 8], .op .sub [vv pxK, .const 1]] pxBody
        [Enc.idxW b2, cellA C (qa + 1), BitVec.ofNat 64 as.length] (by decide) rfl (by decide) hc.self
        ⟨by simp,
          by simp +decide [sev, Env.get, pxParams, ctxEnv]; exact cellA_add8 C qa,
          by simp +decide [sev, Env.get, pxParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, trivial⟩
        (UD.PostO (ctxH C H)) (fun o w _ _ => w = optW o)
        (fun o w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pxParams _ rfl hlk)
          (ih b2 (qa + 1) H s2 hp
            (fun j hj => by have h := ha (j + 1) (by simp; omega); rw [show qa + (j + 1) = qa + 1 + j by omega] at h; simpa using h)
            (by simp at hla; omega)))
        (fun o w s4 H4 hp4 hw => ?_)
      subst hw
      exact specR_returnI _ (optW o) (by simp)
        (fun t ht => ⟨H4, hp4, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · rw [if_neg (show ¬ (h.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg)]
      exact specR_returnI _ (optW none) (by simp [optWG]; rfl)
        (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem ix_wsub (a k : Nat) (hk : k ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 k = BitVec.ofNat 64 (a - k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt (by omega : a - k < 2 ^ 64)]
  omega

structure IxCodes (C : Ctx) : Prop where
  px : PxCodes C
  gaa : C.code.lookup ExG.fGaa = some ([(pFu, .one), (pH, .one)], ExG.gaaBody C, .one)
  dl : DlCodes C

theorem ix_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (hc : IxCodes C) (d : Nat)
    (hD : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ a b, Callee (σ := σ) (ctxH C H) dParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (dE C) s1 ((knot mode C n).defeq d a b)
      (PostB (ctxH C H)))
    (mI rP cnP : Nat) (tyC : EIdx) (hmI : mI < 2 ^ 63) (hrP : rP < 2 ^ 63) (hcn : cnP < 2 ^ 63) :
    ∀ (margs idx : List EIdx) (qm qi : Nat) (H : List (BitVec 64)) (s : AState), C.H <+: H →
      (∀ j (hj : j < margs.length), H[qm + j]? = some (Enc.idxW margs[j])) →
      (∀ j (hj : j < idx.length), H[qi + j]? = some (Enc.idxW idx[j])) →
      margs.length < 2 ^ 63 → idx.length < 2 ^ 63 →
      SpecR (σ := σ) (Pre (ctxH C H) s (ixParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, BitVec.ofNat 64 mI,
        BitVec.ofNat 64 rP, BitVec.ofNat 64 cnP, Enc.idxW tyC, cellA C qm, BitVec.ofNat 64 margs.length, cellA C qi,
        BitVec.ofNat 64 idx.length])) ixBody s
        (iotaIndexOk (knot mode C n) C.fe d mI rP cnP tyC margs idx) (PostB (ctxH C H)) := by
  intro margs idx qm qi H s hp hm hi hml hil
  refine specR_prologue (postB_locals _) (ix_none _ _) ?_
  unfold ixCore iotaIndexOk
  by_cases he : mI = rP
  · rw [if_pos he]
    subst he
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ixParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [if_neg he]
  have hne : BitVec.ofNat 64 mI ≠ BitVec.ofNat 64 rP := fun x =>
    he ((UD.ofNat_eq_iff_small _ _ (by omega) (by omega)).mp x)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ixParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_callNIH (C := ctxH C H) ixR fPx pxParams [vv ixT, vv ixMa, vv ixMn] pxBody
    [Enc.idxW tyC, cellA C qm, BitVec.ofNat 64 margs.length] (by decide) rfl (by decide) hc.px.self
    ⟨by simp +decide [Env.get, ixParams, ctxEnv], by simp +decide [Env.get, ixParams, ctxEnv],
      by simp +decide [Env.get, ixParams, ctxEnv], trivial⟩
    (UD.PostO (ctxH C H)) (fun o w _ _ => w = optW o)
    (fun o w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pxParams _ rfl hlk)
      (px_spec ra C hok hc.px margs tyC qm H s hp hm hml))
    (fun r w s1 H1 hp1 hw => ?_)
  subst hw
  rcases r with _ | res
  · refine specR_ifI _ 1 (by simp +decide [sev, Env.get, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  have hne2 : ¬ Enc.idxW res + 1 = 0 := idxW_add_one_ne res
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne2)
    (fun h => absurd rfl h) (fun _ => ?_)
  dsimp only
  refine specR_callNIH (C := ctxH C H1) ixG ExG.fGaa [pFu, pH]
    [.const (BitVec.ofNat 64 coreWalkFuel), .op .sub [vv ixR, .const 1]] (ExG.gaaBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW res] (by decide) rfl (by decide) hc.gaa
    ⟨rfl, by simp +decide [sev, Env.get, optWG]; exact BitVec.add_sub_cancel _ _, trivial⟩
    (PostA (ctxH C H1)) (fun a w _ H2 => ∃ o2, w = cellA C o2 ∧ BlkAt H2 o2 (a.map Enc.idxW))
    (fun a w s' st ⟨H2, o2, hp, hw, hb, hsr⟩ => ⟨H2, hp, ⟨o2, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (ExG.gaa_spec C hok hc.gaa coreWalkFuel CV.coreWalkFuel_lt H1 res s1))
    (fun args w s2 H2 hp2 ⟨o2, hw, hb⟩ => ?_)
  subst hw
  obtain ⟨hlo, hlv⟩ := blkAt_get0 hb
  have hw0 : (ctxH C H2).H[o2]? = some (BitVec.ofNat 64 args.length) := by
    show H2[o2]? = _; rw [List.getElem?_eq_getElem hlo, hlv]; simp
  refine UD.specR_heapLoadI' (C := ctxH C H2) ixL (vv ixG) o2 _ hw0 (by decide) (by simp +decide [sev, Env.get]; rfl) ?_
  refine specR_atEntry fun t ht => ?_
  have hsz := blk_small0 (ctxOK_H hok H2) ht.sr hb
  simp only [List.length_map] at hsz
  refine specR_assignI ixT2 _ (if BitVec.ofNat 64 cnP < BitVec.ofNat 64 args.length then 1#64 else 0#64)
    (by decide) (by simp +decide [sev, Env.get, ixParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) ?_
  refine specR_assignI ixQ _ (BitVec.ofNat 64 (if cnP < args.length then cnP else args.length)) (by decide)
    (by simp +decide [sev, Env.get, ixParams, ctxEnv]; simpa using min_word cnP args.length (by omega) (by omega)) ?_
  generalize hq : (if cnP < args.length then cnP else args.length) = q
  have hql : q ≤ args.length := by rw [← hq]; split <;> omega
  have hdrop : args.drop cnP = args.drop q := by
    rw [← hq]; split
    · rfl
    · rw [List.drop_eq_nil_of_le (by omega), List.drop_eq_nil_of_le (by omega)]
  rw [hdrop]
  refine specR_bindPure ?_
  refine specR_callNIH (C := ctxH C H2) ixD fDl dlParams
    [vv kFu, vv kD, .op .add [.op .add [vv ixG, .const 8], .shift .lsl (vv ixQ) (.const 3)],
      .op .sub [vv ixL, vv ixQ], vv ixIa, vv ixIn] dlBody
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, cellA C (o2 + 1 + q), BitVec.ofNat 64 (args.drop q).length, cellA C qi,
      BitVec.ofNat 64 idx.length] (by decide) rfl (by decide) hc.dl.self
    ⟨by simp +decide [Env.get, ixParams, ctxEnv], by simp +decide [Env.get, ixParams, ctxEnv],
      by simp +decide [sev, Env.get]; rw [← cellA_shl C (o2 + 1) q (by omega), ← cellA_add8]; rfl,
      by simp +decide [sev, Env.get, List.length_drop]; exact ix_wsub _ _ hql (by omega),
      by simp +decide [Env.get, ixParams, ctxEnv], by simp +decide [Env.get, ixParams, ctxEnv], trivial⟩
    (PostB (ctxH C H2)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu dlParams _ rfl hlk)
      (dl_spec mode n C hc.dl d hD (args.drop q) idx (o2 + 1 + q) qi H2 s2 (hp.trans (hp1.trans hp2))
        (fun j hj => by have h := hb.2 (q + j) (by simp at hj ⊢; omega); rw [List.getElem_map] at h; rw [show o2 + 1 + q + j = o2 + 1 + (q + j) by omega, List.getElem_drop]; exact h)
        (fun j hj => pfx_get (hp1.trans hp2) (hi j hj))
        (by simp; omega) hil))
    (fun b w s3 H3 hp3 hw => ?_)
  subst hw
  exact specR_returnI _ (boolW b) (by simp)
    (fun t ht => ⟨H3, hp1.trans (hp2.trans hp3), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
