import ConPanqueque.T.Core.IotaVals
import ConPanqueque.T.Core.WcStuck
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `iotaRecAt`: the ι step at a stored recursor

The arity check (`peelPis`), `bvar 0`, the major's preparation (`prepareMajor`, a callee answering the term and
whether it is a constructor application), the constructor record re-derived (`ctorView` is read-only, so it is
re-run: `prepareMajor_view`), the rule (`findRule`), the spine check, the certificate (`iotaFam`, a callee, at the
verified mode only), the rule body (`ruleBodyAt`, a callee), and one substitution (`iotaVals`, `instantiateListFast`).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.Str
open ConPanqueque.V.Enc

def ioTy := ofString "ioty"
def ioPp := ofString "iopp"
def ioB0 := ofString "iob0"
def ioMj := ofString "iomj"
def ioIk := ofString "ioik"
def ioRs := ofString "iors"
def ioRp := ofString "iorp"
def ioPm := ofString "iopm"
def ioMe := ofString "iome"
def ioHd := ofString "iohd"
def ioCj := ofString "iocj"
def ioUj := ofString "iouj"
def ioW := ofString "iow"
def ioQj := ofString "ioqj"
def ioRn := ofString "iorn"
def ioRl := ofString "iorl"
def ioRq := ofString "iorq"
def ioMa := ofString "ioma"
def ioMl := ofString "ioml"
def ioNp := ofString "ionp"
def ioNf := ofString "ionf"
def ioF := ofString "iof"
def ioLp := ofString "iolp"
def ioRc := ofString "iorc"
def ioRh := ofString "iorh"
def ioBd := ofString "iobd"
def ioT1 := ofString "iot1"
def ioP := ofString "iop"
def ioT2 := ofString "iot2"
def ioQq := ofString "ioqq"
def ioV := ofString "iov"
def ioVl := ofString "iovl"
def ioX := ofString "iox"
def fPm := ofString "prepareMajor"
def fFam := ofString "iotaFam"
def fRb := ofString "ruleBodyAt"
def pmC := ofString "pmc"
def pmK := ofString "pmk"
def pmR := ofString "pmr"
def pmM := ofString "pmm"
def pmParams : List MlS := [kFu, kD, pmC, pmK, pmR, pmM]
def fmParams : List MlS := [kFu, kD, iC, iU, iQ, iA, iK, ioUj, ioQj, ioRq, ioMa]
def rbParams : List MlS := [pmC, pmK, pmR, pmM, ioRp, ioUj]

@[simp] theorem io_ioTy_ne_ioPp : ioTy ≠ ioPp := by decide
@[simp] theorem io_ioTy_ne_ioB0 : ioTy ≠ ioB0 := by decide
@[simp] theorem io_ioTy_ne_ioMj : ioTy ≠ ioMj := by decide
@[simp] theorem io_ioTy_ne_ioIk : ioTy ≠ ioIk := by decide
@[simp] theorem io_ioTy_ne_ioRs : ioTy ≠ ioRs := by decide
@[simp] theorem io_ioTy_ne_ioRp : ioTy ≠ ioRp := by decide
@[simp] theorem io_ioTy_ne_ioPm : ioTy ≠ ioPm := by decide
@[simp] theorem io_ioTy_ne_ioMe : ioTy ≠ ioMe := by decide
@[simp] theorem io_ioTy_ne_ioHd : ioTy ≠ ioHd := by decide
@[simp] theorem io_ioTy_ne_ioCj : ioTy ≠ ioCj := by decide
@[simp] theorem io_ioTy_ne_ioUj : ioTy ≠ ioUj := by decide
@[simp] theorem io_ioTy_ne_ioW : ioTy ≠ ioW := by decide
@[simp] theorem io_ioTy_ne_ioQj : ioTy ≠ ioQj := by decide
@[simp] theorem io_ioTy_ne_ioRn : ioTy ≠ ioRn := by decide
@[simp] theorem io_ioTy_ne_ioRl : ioTy ≠ ioRl := by decide
@[simp] theorem io_ioTy_ne_ioRq : ioTy ≠ ioRq := by decide
@[simp] theorem io_ioTy_ne_ioMa : ioTy ≠ ioMa := by decide
@[simp] theorem io_ioTy_ne_ioMl : ioTy ≠ ioMl := by decide
@[simp] theorem io_ioTy_ne_ioNp : ioTy ≠ ioNp := by decide
@[simp] theorem io_ioTy_ne_ioNf : ioTy ≠ ioNf := by decide
@[simp] theorem io_ioTy_ne_ioF : ioTy ≠ ioF := by decide
@[simp] theorem io_ioTy_ne_ioLp : ioTy ≠ ioLp := by decide
@[simp] theorem io_ioTy_ne_ioRc : ioTy ≠ ioRc := by decide
@[simp] theorem io_ioTy_ne_ioRh : ioTy ≠ ioRh := by decide
@[simp] theorem io_ioTy_ne_ioBd : ioTy ≠ ioBd := by decide
@[simp] theorem io_ioTy_ne_ioT1 : ioTy ≠ ioT1 := by decide
@[simp] theorem io_ioTy_ne_ioP : ioTy ≠ ioP := by decide
@[simp] theorem io_ioTy_ne_ioT2 : ioTy ≠ ioT2 := by decide
@[simp] theorem io_ioTy_ne_ioQq : ioTy ≠ ioQq := by decide
@[simp] theorem io_ioTy_ne_ioV : ioTy ≠ ioV := by decide
@[simp] theorem io_ioTy_ne_ioVl : ioTy ≠ ioVl := by decide
@[simp] theorem io_ioTy_ne_ioX : ioTy ≠ ioX := by decide
@[simp] theorem io_ioTy_ne_lFl : ioTy ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioTy : lFl ≠ ioTy := by decide
@[simp] theorem io_ioTy_ne_lDh : ioTy ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioTy : lDh ≠ ioTy := by decide
@[simp] theorem io_ioTy_ne_lDt : ioTy ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioTy : lDt ≠ ioTy := by decide
@[simp] theorem io_ioTy_ne_lDg : ioTy ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioTy : lDg ≠ ioTy := by decide
@[simp] theorem io_ioTy_ne_lDi : ioTy ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioTy : lDi ≠ ioTy := by decide
@[simp] theorem io_ioTy_ne_lRp : ioTy ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioTy : lRp ≠ ioTy := by decide
@[simp] theorem io_ioTy_ne_lRn : ioTy ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioTy : lRn ≠ ioTy := by decide
@[simp] theorem io_ioTy_ne_lFle : ioTy ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioTy : lFle ≠ ioTy := by decide
@[simp] theorem io_ioTy_ne_lDir : ioTy ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioTy : lDir ≠ ioTy := by decide
@[simp] theorem io_ioTy_ne_lKb : ioTy ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioTy : lKb ≠ ioTy := by decide
@[simp] theorem io_ioTy_ne_kFu : ioTy ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioTy : kFu ≠ ioTy := by decide
@[simp] theorem io_ioTy_ne_kD : ioTy ≠ kD := by decide
@[simp] theorem io_kD_ne_ioTy : kD ≠ ioTy := by decide
@[simp] theorem io_ioTy_ne_iC : ioTy ≠ iC := by decide
@[simp] theorem io_iC_ne_ioTy : iC ≠ ioTy := by decide
@[simp] theorem io_ioTy_ne_iU : ioTy ≠ iU := by decide
@[simp] theorem io_iU_ne_ioTy : iU ≠ ioTy := by decide
@[simp] theorem io_ioTy_ne_iQ : ioTy ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioTy : iQ ≠ ioTy := by decide
@[simp] theorem io_ioTy_ne_iA : ioTy ≠ iA := by decide
@[simp] theorem io_iA_ne_ioTy : iA ≠ ioTy := by decide
@[simp] theorem io_ioTy_ne_iK : ioTy ≠ iK := by decide
@[simp] theorem io_iK_ne_ioTy : iK ≠ ioTy := by decide
@[simp] theorem io_ioPp_ne_ioTy : ioPp ≠ ioTy := by decide
@[simp] theorem io_ioPp_ne_ioB0 : ioPp ≠ ioB0 := by decide
@[simp] theorem io_ioPp_ne_ioMj : ioPp ≠ ioMj := by decide
@[simp] theorem io_ioPp_ne_ioIk : ioPp ≠ ioIk := by decide
@[simp] theorem io_ioPp_ne_ioRs : ioPp ≠ ioRs := by decide
@[simp] theorem io_ioPp_ne_ioRp : ioPp ≠ ioRp := by decide
@[simp] theorem io_ioPp_ne_ioPm : ioPp ≠ ioPm := by decide
@[simp] theorem io_ioPp_ne_ioMe : ioPp ≠ ioMe := by decide
@[simp] theorem io_ioPp_ne_ioHd : ioPp ≠ ioHd := by decide
@[simp] theorem io_ioPp_ne_ioCj : ioPp ≠ ioCj := by decide
@[simp] theorem io_ioPp_ne_ioUj : ioPp ≠ ioUj := by decide
@[simp] theorem io_ioPp_ne_ioW : ioPp ≠ ioW := by decide
@[simp] theorem io_ioPp_ne_ioQj : ioPp ≠ ioQj := by decide
@[simp] theorem io_ioPp_ne_ioRn : ioPp ≠ ioRn := by decide
@[simp] theorem io_ioPp_ne_ioRl : ioPp ≠ ioRl := by decide
@[simp] theorem io_ioPp_ne_ioRq : ioPp ≠ ioRq := by decide
@[simp] theorem io_ioPp_ne_ioMa : ioPp ≠ ioMa := by decide
@[simp] theorem io_ioPp_ne_ioMl : ioPp ≠ ioMl := by decide
@[simp] theorem io_ioPp_ne_ioNp : ioPp ≠ ioNp := by decide
@[simp] theorem io_ioPp_ne_ioNf : ioPp ≠ ioNf := by decide
@[simp] theorem io_ioPp_ne_ioF : ioPp ≠ ioF := by decide
@[simp] theorem io_ioPp_ne_ioLp : ioPp ≠ ioLp := by decide
@[simp] theorem io_ioPp_ne_ioRc : ioPp ≠ ioRc := by decide
@[simp] theorem io_ioPp_ne_ioRh : ioPp ≠ ioRh := by decide
@[simp] theorem io_ioPp_ne_ioBd : ioPp ≠ ioBd := by decide
@[simp] theorem io_ioPp_ne_ioT1 : ioPp ≠ ioT1 := by decide
@[simp] theorem io_ioPp_ne_ioP : ioPp ≠ ioP := by decide
@[simp] theorem io_ioPp_ne_ioT2 : ioPp ≠ ioT2 := by decide
@[simp] theorem io_ioPp_ne_ioQq : ioPp ≠ ioQq := by decide
@[simp] theorem io_ioPp_ne_ioV : ioPp ≠ ioV := by decide
@[simp] theorem io_ioPp_ne_ioVl : ioPp ≠ ioVl := by decide
@[simp] theorem io_ioPp_ne_ioX : ioPp ≠ ioX := by decide
@[simp] theorem io_ioPp_ne_lFl : ioPp ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioPp : lFl ≠ ioPp := by decide
@[simp] theorem io_ioPp_ne_lDh : ioPp ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioPp : lDh ≠ ioPp := by decide
@[simp] theorem io_ioPp_ne_lDt : ioPp ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioPp : lDt ≠ ioPp := by decide
@[simp] theorem io_ioPp_ne_lDg : ioPp ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioPp : lDg ≠ ioPp := by decide
@[simp] theorem io_ioPp_ne_lDi : ioPp ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioPp : lDi ≠ ioPp := by decide
@[simp] theorem io_ioPp_ne_lRp : ioPp ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioPp : lRp ≠ ioPp := by decide
@[simp] theorem io_ioPp_ne_lRn : ioPp ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioPp : lRn ≠ ioPp := by decide
@[simp] theorem io_ioPp_ne_lFle : ioPp ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioPp : lFle ≠ ioPp := by decide
@[simp] theorem io_ioPp_ne_lDir : ioPp ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioPp : lDir ≠ ioPp := by decide
@[simp] theorem io_ioPp_ne_lKb : ioPp ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioPp : lKb ≠ ioPp := by decide
@[simp] theorem io_ioPp_ne_kFu : ioPp ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioPp : kFu ≠ ioPp := by decide
@[simp] theorem io_ioPp_ne_kD : ioPp ≠ kD := by decide
@[simp] theorem io_kD_ne_ioPp : kD ≠ ioPp := by decide
@[simp] theorem io_ioPp_ne_iC : ioPp ≠ iC := by decide
@[simp] theorem io_iC_ne_ioPp : iC ≠ ioPp := by decide
@[simp] theorem io_ioPp_ne_iU : ioPp ≠ iU := by decide
@[simp] theorem io_iU_ne_ioPp : iU ≠ ioPp := by decide
@[simp] theorem io_ioPp_ne_iQ : ioPp ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioPp : iQ ≠ ioPp := by decide
@[simp] theorem io_ioPp_ne_iA : ioPp ≠ iA := by decide
@[simp] theorem io_iA_ne_ioPp : iA ≠ ioPp := by decide
@[simp] theorem io_ioPp_ne_iK : ioPp ≠ iK := by decide
@[simp] theorem io_iK_ne_ioPp : iK ≠ ioPp := by decide
@[simp] theorem io_ioB0_ne_ioTy : ioB0 ≠ ioTy := by decide
@[simp] theorem io_ioB0_ne_ioPp : ioB0 ≠ ioPp := by decide
@[simp] theorem io_ioB0_ne_ioMj : ioB0 ≠ ioMj := by decide
@[simp] theorem io_ioB0_ne_ioIk : ioB0 ≠ ioIk := by decide
@[simp] theorem io_ioB0_ne_ioRs : ioB0 ≠ ioRs := by decide
@[simp] theorem io_ioB0_ne_ioRp : ioB0 ≠ ioRp := by decide
@[simp] theorem io_ioB0_ne_ioPm : ioB0 ≠ ioPm := by decide
@[simp] theorem io_ioB0_ne_ioMe : ioB0 ≠ ioMe := by decide
@[simp] theorem io_ioB0_ne_ioHd : ioB0 ≠ ioHd := by decide
@[simp] theorem io_ioB0_ne_ioCj : ioB0 ≠ ioCj := by decide
@[simp] theorem io_ioB0_ne_ioUj : ioB0 ≠ ioUj := by decide
@[simp] theorem io_ioB0_ne_ioW : ioB0 ≠ ioW := by decide
@[simp] theorem io_ioB0_ne_ioQj : ioB0 ≠ ioQj := by decide
@[simp] theorem io_ioB0_ne_ioRn : ioB0 ≠ ioRn := by decide
@[simp] theorem io_ioB0_ne_ioRl : ioB0 ≠ ioRl := by decide
@[simp] theorem io_ioB0_ne_ioRq : ioB0 ≠ ioRq := by decide
@[simp] theorem io_ioB0_ne_ioMa : ioB0 ≠ ioMa := by decide
@[simp] theorem io_ioB0_ne_ioMl : ioB0 ≠ ioMl := by decide
@[simp] theorem io_ioB0_ne_ioNp : ioB0 ≠ ioNp := by decide
@[simp] theorem io_ioB0_ne_ioNf : ioB0 ≠ ioNf := by decide
@[simp] theorem io_ioB0_ne_ioF : ioB0 ≠ ioF := by decide
@[simp] theorem io_ioB0_ne_ioLp : ioB0 ≠ ioLp := by decide
@[simp] theorem io_ioB0_ne_ioRc : ioB0 ≠ ioRc := by decide
@[simp] theorem io_ioB0_ne_ioRh : ioB0 ≠ ioRh := by decide
@[simp] theorem io_ioB0_ne_ioBd : ioB0 ≠ ioBd := by decide
@[simp] theorem io_ioB0_ne_ioT1 : ioB0 ≠ ioT1 := by decide
@[simp] theorem io_ioB0_ne_ioP : ioB0 ≠ ioP := by decide
@[simp] theorem io_ioB0_ne_ioT2 : ioB0 ≠ ioT2 := by decide
@[simp] theorem io_ioB0_ne_ioQq : ioB0 ≠ ioQq := by decide
@[simp] theorem io_ioB0_ne_ioV : ioB0 ≠ ioV := by decide
@[simp] theorem io_ioB0_ne_ioVl : ioB0 ≠ ioVl := by decide
@[simp] theorem io_ioB0_ne_ioX : ioB0 ≠ ioX := by decide
@[simp] theorem io_ioB0_ne_lFl : ioB0 ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioB0 : lFl ≠ ioB0 := by decide
@[simp] theorem io_ioB0_ne_lDh : ioB0 ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioB0 : lDh ≠ ioB0 := by decide
@[simp] theorem io_ioB0_ne_lDt : ioB0 ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioB0 : lDt ≠ ioB0 := by decide
@[simp] theorem io_ioB0_ne_lDg : ioB0 ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioB0 : lDg ≠ ioB0 := by decide
@[simp] theorem io_ioB0_ne_lDi : ioB0 ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioB0 : lDi ≠ ioB0 := by decide
@[simp] theorem io_ioB0_ne_lRp : ioB0 ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioB0 : lRp ≠ ioB0 := by decide
@[simp] theorem io_ioB0_ne_lRn : ioB0 ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioB0 : lRn ≠ ioB0 := by decide
@[simp] theorem io_ioB0_ne_lFle : ioB0 ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioB0 : lFle ≠ ioB0 := by decide
@[simp] theorem io_ioB0_ne_lDir : ioB0 ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioB0 : lDir ≠ ioB0 := by decide
@[simp] theorem io_ioB0_ne_lKb : ioB0 ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioB0 : lKb ≠ ioB0 := by decide
@[simp] theorem io_ioB0_ne_kFu : ioB0 ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioB0 : kFu ≠ ioB0 := by decide
@[simp] theorem io_ioB0_ne_kD : ioB0 ≠ kD := by decide
@[simp] theorem io_kD_ne_ioB0 : kD ≠ ioB0 := by decide
@[simp] theorem io_ioB0_ne_iC : ioB0 ≠ iC := by decide
@[simp] theorem io_iC_ne_ioB0 : iC ≠ ioB0 := by decide
@[simp] theorem io_ioB0_ne_iU : ioB0 ≠ iU := by decide
@[simp] theorem io_iU_ne_ioB0 : iU ≠ ioB0 := by decide
@[simp] theorem io_ioB0_ne_iQ : ioB0 ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioB0 : iQ ≠ ioB0 := by decide
@[simp] theorem io_ioB0_ne_iA : ioB0 ≠ iA := by decide
@[simp] theorem io_iA_ne_ioB0 : iA ≠ ioB0 := by decide
@[simp] theorem io_ioB0_ne_iK : ioB0 ≠ iK := by decide
@[simp] theorem io_iK_ne_ioB0 : iK ≠ ioB0 := by decide
@[simp] theorem io_ioMj_ne_ioTy : ioMj ≠ ioTy := by decide
@[simp] theorem io_ioMj_ne_ioPp : ioMj ≠ ioPp := by decide
@[simp] theorem io_ioMj_ne_ioB0 : ioMj ≠ ioB0 := by decide
@[simp] theorem io_ioMj_ne_ioIk : ioMj ≠ ioIk := by decide
@[simp] theorem io_ioMj_ne_ioRs : ioMj ≠ ioRs := by decide
@[simp] theorem io_ioMj_ne_ioRp : ioMj ≠ ioRp := by decide
@[simp] theorem io_ioMj_ne_ioPm : ioMj ≠ ioPm := by decide
@[simp] theorem io_ioMj_ne_ioMe : ioMj ≠ ioMe := by decide
@[simp] theorem io_ioMj_ne_ioHd : ioMj ≠ ioHd := by decide
@[simp] theorem io_ioMj_ne_ioCj : ioMj ≠ ioCj := by decide
@[simp] theorem io_ioMj_ne_ioUj : ioMj ≠ ioUj := by decide
@[simp] theorem io_ioMj_ne_ioW : ioMj ≠ ioW := by decide
@[simp] theorem io_ioMj_ne_ioQj : ioMj ≠ ioQj := by decide
@[simp] theorem io_ioMj_ne_ioRn : ioMj ≠ ioRn := by decide
@[simp] theorem io_ioMj_ne_ioRl : ioMj ≠ ioRl := by decide
@[simp] theorem io_ioMj_ne_ioRq : ioMj ≠ ioRq := by decide
@[simp] theorem io_ioMj_ne_ioMa : ioMj ≠ ioMa := by decide
@[simp] theorem io_ioMj_ne_ioMl : ioMj ≠ ioMl := by decide
@[simp] theorem io_ioMj_ne_ioNp : ioMj ≠ ioNp := by decide
@[simp] theorem io_ioMj_ne_ioNf : ioMj ≠ ioNf := by decide
@[simp] theorem io_ioMj_ne_ioF : ioMj ≠ ioF := by decide
@[simp] theorem io_ioMj_ne_ioLp : ioMj ≠ ioLp := by decide
@[simp] theorem io_ioMj_ne_ioRc : ioMj ≠ ioRc := by decide
@[simp] theorem io_ioMj_ne_ioRh : ioMj ≠ ioRh := by decide
@[simp] theorem io_ioMj_ne_ioBd : ioMj ≠ ioBd := by decide
@[simp] theorem io_ioMj_ne_ioT1 : ioMj ≠ ioT1 := by decide
@[simp] theorem io_ioMj_ne_ioP : ioMj ≠ ioP := by decide
@[simp] theorem io_ioMj_ne_ioT2 : ioMj ≠ ioT2 := by decide
@[simp] theorem io_ioMj_ne_ioQq : ioMj ≠ ioQq := by decide
@[simp] theorem io_ioMj_ne_ioV : ioMj ≠ ioV := by decide
@[simp] theorem io_ioMj_ne_ioVl : ioMj ≠ ioVl := by decide
@[simp] theorem io_ioMj_ne_ioX : ioMj ≠ ioX := by decide
@[simp] theorem io_ioMj_ne_lFl : ioMj ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioMj : lFl ≠ ioMj := by decide
@[simp] theorem io_ioMj_ne_lDh : ioMj ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioMj : lDh ≠ ioMj := by decide
@[simp] theorem io_ioMj_ne_lDt : ioMj ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioMj : lDt ≠ ioMj := by decide
@[simp] theorem io_ioMj_ne_lDg : ioMj ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioMj : lDg ≠ ioMj := by decide
@[simp] theorem io_ioMj_ne_lDi : ioMj ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioMj : lDi ≠ ioMj := by decide
@[simp] theorem io_ioMj_ne_lRp : ioMj ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioMj : lRp ≠ ioMj := by decide
@[simp] theorem io_ioMj_ne_lRn : ioMj ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioMj : lRn ≠ ioMj := by decide
@[simp] theorem io_ioMj_ne_lFle : ioMj ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioMj : lFle ≠ ioMj := by decide
@[simp] theorem io_ioMj_ne_lDir : ioMj ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioMj : lDir ≠ ioMj := by decide
@[simp] theorem io_ioMj_ne_lKb : ioMj ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioMj : lKb ≠ ioMj := by decide
@[simp] theorem io_ioMj_ne_kFu : ioMj ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioMj : kFu ≠ ioMj := by decide
@[simp] theorem io_ioMj_ne_kD : ioMj ≠ kD := by decide
@[simp] theorem io_kD_ne_ioMj : kD ≠ ioMj := by decide
@[simp] theorem io_ioMj_ne_iC : ioMj ≠ iC := by decide
@[simp] theorem io_iC_ne_ioMj : iC ≠ ioMj := by decide
@[simp] theorem io_ioMj_ne_iU : ioMj ≠ iU := by decide
@[simp] theorem io_iU_ne_ioMj : iU ≠ ioMj := by decide
@[simp] theorem io_ioMj_ne_iQ : ioMj ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioMj : iQ ≠ ioMj := by decide
@[simp] theorem io_ioMj_ne_iA : ioMj ≠ iA := by decide
@[simp] theorem io_iA_ne_ioMj : iA ≠ ioMj := by decide
@[simp] theorem io_ioMj_ne_iK : ioMj ≠ iK := by decide
@[simp] theorem io_iK_ne_ioMj : iK ≠ ioMj := by decide
@[simp] theorem io_ioIk_ne_ioTy : ioIk ≠ ioTy := by decide
@[simp] theorem io_ioIk_ne_ioPp : ioIk ≠ ioPp := by decide
@[simp] theorem io_ioIk_ne_ioB0 : ioIk ≠ ioB0 := by decide
@[simp] theorem io_ioIk_ne_ioMj : ioIk ≠ ioMj := by decide
@[simp] theorem io_ioIk_ne_ioRs : ioIk ≠ ioRs := by decide
@[simp] theorem io_ioIk_ne_ioRp : ioIk ≠ ioRp := by decide
@[simp] theorem io_ioIk_ne_ioPm : ioIk ≠ ioPm := by decide
@[simp] theorem io_ioIk_ne_ioMe : ioIk ≠ ioMe := by decide
@[simp] theorem io_ioIk_ne_ioHd : ioIk ≠ ioHd := by decide
@[simp] theorem io_ioIk_ne_ioCj : ioIk ≠ ioCj := by decide
@[simp] theorem io_ioIk_ne_ioUj : ioIk ≠ ioUj := by decide
@[simp] theorem io_ioIk_ne_ioW : ioIk ≠ ioW := by decide
@[simp] theorem io_ioIk_ne_ioQj : ioIk ≠ ioQj := by decide
@[simp] theorem io_ioIk_ne_ioRn : ioIk ≠ ioRn := by decide
@[simp] theorem io_ioIk_ne_ioRl : ioIk ≠ ioRl := by decide
@[simp] theorem io_ioIk_ne_ioRq : ioIk ≠ ioRq := by decide
@[simp] theorem io_ioIk_ne_ioMa : ioIk ≠ ioMa := by decide
@[simp] theorem io_ioIk_ne_ioMl : ioIk ≠ ioMl := by decide
@[simp] theorem io_ioIk_ne_ioNp : ioIk ≠ ioNp := by decide
@[simp] theorem io_ioIk_ne_ioNf : ioIk ≠ ioNf := by decide
@[simp] theorem io_ioIk_ne_ioF : ioIk ≠ ioF := by decide
@[simp] theorem io_ioIk_ne_ioLp : ioIk ≠ ioLp := by decide
@[simp] theorem io_ioIk_ne_ioRc : ioIk ≠ ioRc := by decide
@[simp] theorem io_ioIk_ne_ioRh : ioIk ≠ ioRh := by decide
@[simp] theorem io_ioIk_ne_ioBd : ioIk ≠ ioBd := by decide
@[simp] theorem io_ioIk_ne_ioT1 : ioIk ≠ ioT1 := by decide
@[simp] theorem io_ioIk_ne_ioP : ioIk ≠ ioP := by decide
@[simp] theorem io_ioIk_ne_ioT2 : ioIk ≠ ioT2 := by decide
@[simp] theorem io_ioIk_ne_ioQq : ioIk ≠ ioQq := by decide
@[simp] theorem io_ioIk_ne_ioV : ioIk ≠ ioV := by decide
@[simp] theorem io_ioIk_ne_ioVl : ioIk ≠ ioVl := by decide
@[simp] theorem io_ioIk_ne_ioX : ioIk ≠ ioX := by decide
@[simp] theorem io_ioIk_ne_lFl : ioIk ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioIk : lFl ≠ ioIk := by decide
@[simp] theorem io_ioIk_ne_lDh : ioIk ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioIk : lDh ≠ ioIk := by decide
@[simp] theorem io_ioIk_ne_lDt : ioIk ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioIk : lDt ≠ ioIk := by decide
@[simp] theorem io_ioIk_ne_lDg : ioIk ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioIk : lDg ≠ ioIk := by decide
@[simp] theorem io_ioIk_ne_lDi : ioIk ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioIk : lDi ≠ ioIk := by decide
@[simp] theorem io_ioIk_ne_lRp : ioIk ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioIk : lRp ≠ ioIk := by decide
@[simp] theorem io_ioIk_ne_lRn : ioIk ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioIk : lRn ≠ ioIk := by decide
@[simp] theorem io_ioIk_ne_lFle : ioIk ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioIk : lFle ≠ ioIk := by decide
@[simp] theorem io_ioIk_ne_lDir : ioIk ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioIk : lDir ≠ ioIk := by decide
@[simp] theorem io_ioIk_ne_lKb : ioIk ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioIk : lKb ≠ ioIk := by decide
@[simp] theorem io_ioIk_ne_kFu : ioIk ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioIk : kFu ≠ ioIk := by decide
@[simp] theorem io_ioIk_ne_kD : ioIk ≠ kD := by decide
@[simp] theorem io_kD_ne_ioIk : kD ≠ ioIk := by decide
@[simp] theorem io_ioIk_ne_iC : ioIk ≠ iC := by decide
@[simp] theorem io_iC_ne_ioIk : iC ≠ ioIk := by decide
@[simp] theorem io_ioIk_ne_iU : ioIk ≠ iU := by decide
@[simp] theorem io_iU_ne_ioIk : iU ≠ ioIk := by decide
@[simp] theorem io_ioIk_ne_iQ : ioIk ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioIk : iQ ≠ ioIk := by decide
@[simp] theorem io_ioIk_ne_iA : ioIk ≠ iA := by decide
@[simp] theorem io_iA_ne_ioIk : iA ≠ ioIk := by decide
@[simp] theorem io_ioIk_ne_iK : ioIk ≠ iK := by decide
@[simp] theorem io_iK_ne_ioIk : iK ≠ ioIk := by decide
@[simp] theorem io_ioRs_ne_ioTy : ioRs ≠ ioTy := by decide
@[simp] theorem io_ioRs_ne_ioPp : ioRs ≠ ioPp := by decide
@[simp] theorem io_ioRs_ne_ioB0 : ioRs ≠ ioB0 := by decide
@[simp] theorem io_ioRs_ne_ioMj : ioRs ≠ ioMj := by decide
@[simp] theorem io_ioRs_ne_ioIk : ioRs ≠ ioIk := by decide
@[simp] theorem io_ioRs_ne_ioRp : ioRs ≠ ioRp := by decide
@[simp] theorem io_ioRs_ne_ioPm : ioRs ≠ ioPm := by decide
@[simp] theorem io_ioRs_ne_ioMe : ioRs ≠ ioMe := by decide
@[simp] theorem io_ioRs_ne_ioHd : ioRs ≠ ioHd := by decide
@[simp] theorem io_ioRs_ne_ioCj : ioRs ≠ ioCj := by decide
@[simp] theorem io_ioRs_ne_ioUj : ioRs ≠ ioUj := by decide
@[simp] theorem io_ioRs_ne_ioW : ioRs ≠ ioW := by decide
@[simp] theorem io_ioRs_ne_ioQj : ioRs ≠ ioQj := by decide
@[simp] theorem io_ioRs_ne_ioRn : ioRs ≠ ioRn := by decide
@[simp] theorem io_ioRs_ne_ioRl : ioRs ≠ ioRl := by decide
@[simp] theorem io_ioRs_ne_ioRq : ioRs ≠ ioRq := by decide
@[simp] theorem io_ioRs_ne_ioMa : ioRs ≠ ioMa := by decide
@[simp] theorem io_ioRs_ne_ioMl : ioRs ≠ ioMl := by decide
@[simp] theorem io_ioRs_ne_ioNp : ioRs ≠ ioNp := by decide
@[simp] theorem io_ioRs_ne_ioNf : ioRs ≠ ioNf := by decide
@[simp] theorem io_ioRs_ne_ioF : ioRs ≠ ioF := by decide
@[simp] theorem io_ioRs_ne_ioLp : ioRs ≠ ioLp := by decide
@[simp] theorem io_ioRs_ne_ioRc : ioRs ≠ ioRc := by decide
@[simp] theorem io_ioRs_ne_ioRh : ioRs ≠ ioRh := by decide
@[simp] theorem io_ioRs_ne_ioBd : ioRs ≠ ioBd := by decide
@[simp] theorem io_ioRs_ne_ioT1 : ioRs ≠ ioT1 := by decide
@[simp] theorem io_ioRs_ne_ioP : ioRs ≠ ioP := by decide
@[simp] theorem io_ioRs_ne_ioT2 : ioRs ≠ ioT2 := by decide
@[simp] theorem io_ioRs_ne_ioQq : ioRs ≠ ioQq := by decide
@[simp] theorem io_ioRs_ne_ioV : ioRs ≠ ioV := by decide
@[simp] theorem io_ioRs_ne_ioVl : ioRs ≠ ioVl := by decide
@[simp] theorem io_ioRs_ne_ioX : ioRs ≠ ioX := by decide
@[simp] theorem io_ioRs_ne_lFl : ioRs ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioRs : lFl ≠ ioRs := by decide
@[simp] theorem io_ioRs_ne_lDh : ioRs ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioRs : lDh ≠ ioRs := by decide
@[simp] theorem io_ioRs_ne_lDt : ioRs ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioRs : lDt ≠ ioRs := by decide
@[simp] theorem io_ioRs_ne_lDg : ioRs ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioRs : lDg ≠ ioRs := by decide
@[simp] theorem io_ioRs_ne_lDi : ioRs ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioRs : lDi ≠ ioRs := by decide
@[simp] theorem io_ioRs_ne_lRp : ioRs ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioRs : lRp ≠ ioRs := by decide
@[simp] theorem io_ioRs_ne_lRn : ioRs ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioRs : lRn ≠ ioRs := by decide
@[simp] theorem io_ioRs_ne_lFle : ioRs ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioRs : lFle ≠ ioRs := by decide
@[simp] theorem io_ioRs_ne_lDir : ioRs ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioRs : lDir ≠ ioRs := by decide
@[simp] theorem io_ioRs_ne_lKb : ioRs ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioRs : lKb ≠ ioRs := by decide
@[simp] theorem io_ioRs_ne_kFu : ioRs ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioRs : kFu ≠ ioRs := by decide
@[simp] theorem io_ioRs_ne_kD : ioRs ≠ kD := by decide
@[simp] theorem io_kD_ne_ioRs : kD ≠ ioRs := by decide
@[simp] theorem io_ioRs_ne_iC : ioRs ≠ iC := by decide
@[simp] theorem io_iC_ne_ioRs : iC ≠ ioRs := by decide
@[simp] theorem io_ioRs_ne_iU : ioRs ≠ iU := by decide
@[simp] theorem io_iU_ne_ioRs : iU ≠ ioRs := by decide
@[simp] theorem io_ioRs_ne_iQ : ioRs ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioRs : iQ ≠ ioRs := by decide
@[simp] theorem io_ioRs_ne_iA : ioRs ≠ iA := by decide
@[simp] theorem io_iA_ne_ioRs : iA ≠ ioRs := by decide
@[simp] theorem io_ioRs_ne_iK : ioRs ≠ iK := by decide
@[simp] theorem io_iK_ne_ioRs : iK ≠ ioRs := by decide
@[simp] theorem io_ioRp_ne_ioTy : ioRp ≠ ioTy := by decide
@[simp] theorem io_ioRp_ne_ioPp : ioRp ≠ ioPp := by decide
@[simp] theorem io_ioRp_ne_ioB0 : ioRp ≠ ioB0 := by decide
@[simp] theorem io_ioRp_ne_ioMj : ioRp ≠ ioMj := by decide
@[simp] theorem io_ioRp_ne_ioIk : ioRp ≠ ioIk := by decide
@[simp] theorem io_ioRp_ne_ioRs : ioRp ≠ ioRs := by decide
@[simp] theorem io_ioRp_ne_ioPm : ioRp ≠ ioPm := by decide
@[simp] theorem io_ioRp_ne_ioMe : ioRp ≠ ioMe := by decide
@[simp] theorem io_ioRp_ne_ioHd : ioRp ≠ ioHd := by decide
@[simp] theorem io_ioRp_ne_ioCj : ioRp ≠ ioCj := by decide
@[simp] theorem io_ioRp_ne_ioUj : ioRp ≠ ioUj := by decide
@[simp] theorem io_ioRp_ne_ioW : ioRp ≠ ioW := by decide
@[simp] theorem io_ioRp_ne_ioQj : ioRp ≠ ioQj := by decide
@[simp] theorem io_ioRp_ne_ioRn : ioRp ≠ ioRn := by decide
@[simp] theorem io_ioRp_ne_ioRl : ioRp ≠ ioRl := by decide
@[simp] theorem io_ioRp_ne_ioRq : ioRp ≠ ioRq := by decide
@[simp] theorem io_ioRp_ne_ioMa : ioRp ≠ ioMa := by decide
@[simp] theorem io_ioRp_ne_ioMl : ioRp ≠ ioMl := by decide
@[simp] theorem io_ioRp_ne_ioNp : ioRp ≠ ioNp := by decide
@[simp] theorem io_ioRp_ne_ioNf : ioRp ≠ ioNf := by decide
@[simp] theorem io_ioRp_ne_ioF : ioRp ≠ ioF := by decide
@[simp] theorem io_ioRp_ne_ioLp : ioRp ≠ ioLp := by decide
@[simp] theorem io_ioRp_ne_ioRc : ioRp ≠ ioRc := by decide
@[simp] theorem io_ioRp_ne_ioRh : ioRp ≠ ioRh := by decide
@[simp] theorem io_ioRp_ne_ioBd : ioRp ≠ ioBd := by decide
@[simp] theorem io_ioRp_ne_ioT1 : ioRp ≠ ioT1 := by decide
@[simp] theorem io_ioRp_ne_ioP : ioRp ≠ ioP := by decide
@[simp] theorem io_ioRp_ne_ioT2 : ioRp ≠ ioT2 := by decide
@[simp] theorem io_ioRp_ne_ioQq : ioRp ≠ ioQq := by decide
@[simp] theorem io_ioRp_ne_ioV : ioRp ≠ ioV := by decide
@[simp] theorem io_ioRp_ne_ioVl : ioRp ≠ ioVl := by decide
@[simp] theorem io_ioRp_ne_ioX : ioRp ≠ ioX := by decide
@[simp] theorem io_ioRp_ne_lFl : ioRp ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioRp : lFl ≠ ioRp := by decide
@[simp] theorem io_ioRp_ne_lDh : ioRp ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioRp : lDh ≠ ioRp := by decide
@[simp] theorem io_ioRp_ne_lDt : ioRp ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioRp : lDt ≠ ioRp := by decide
@[simp] theorem io_ioRp_ne_lDg : ioRp ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioRp : lDg ≠ ioRp := by decide
@[simp] theorem io_ioRp_ne_lDi : ioRp ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioRp : lDi ≠ ioRp := by decide
@[simp] theorem io_ioRp_ne_lRp : ioRp ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioRp : lRp ≠ ioRp := by decide
@[simp] theorem io_ioRp_ne_lRn : ioRp ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioRp : lRn ≠ ioRp := by decide
@[simp] theorem io_ioRp_ne_lFle : ioRp ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioRp : lFle ≠ ioRp := by decide
@[simp] theorem io_ioRp_ne_lDir : ioRp ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioRp : lDir ≠ ioRp := by decide
@[simp] theorem io_ioRp_ne_lKb : ioRp ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioRp : lKb ≠ ioRp := by decide
@[simp] theorem io_ioRp_ne_kFu : ioRp ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioRp : kFu ≠ ioRp := by decide
@[simp] theorem io_ioRp_ne_kD : ioRp ≠ kD := by decide
@[simp] theorem io_kD_ne_ioRp : kD ≠ ioRp := by decide
@[simp] theorem io_ioRp_ne_iC : ioRp ≠ iC := by decide
@[simp] theorem io_iC_ne_ioRp : iC ≠ ioRp := by decide
@[simp] theorem io_ioRp_ne_iU : ioRp ≠ iU := by decide
@[simp] theorem io_iU_ne_ioRp : iU ≠ ioRp := by decide
@[simp] theorem io_ioRp_ne_iQ : ioRp ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioRp : iQ ≠ ioRp := by decide
@[simp] theorem io_ioRp_ne_iA : ioRp ≠ iA := by decide
@[simp] theorem io_iA_ne_ioRp : iA ≠ ioRp := by decide
@[simp] theorem io_ioRp_ne_iK : ioRp ≠ iK := by decide
@[simp] theorem io_iK_ne_ioRp : iK ≠ ioRp := by decide
@[simp] theorem io_ioPm_ne_ioTy : ioPm ≠ ioTy := by decide
@[simp] theorem io_ioPm_ne_ioPp : ioPm ≠ ioPp := by decide
@[simp] theorem io_ioPm_ne_ioB0 : ioPm ≠ ioB0 := by decide
@[simp] theorem io_ioPm_ne_ioMj : ioPm ≠ ioMj := by decide
@[simp] theorem io_ioPm_ne_ioIk : ioPm ≠ ioIk := by decide
@[simp] theorem io_ioPm_ne_ioRs : ioPm ≠ ioRs := by decide
@[simp] theorem io_ioPm_ne_ioRp : ioPm ≠ ioRp := by decide
@[simp] theorem io_ioPm_ne_ioMe : ioPm ≠ ioMe := by decide
@[simp] theorem io_ioPm_ne_ioHd : ioPm ≠ ioHd := by decide
@[simp] theorem io_ioPm_ne_ioCj : ioPm ≠ ioCj := by decide
@[simp] theorem io_ioPm_ne_ioUj : ioPm ≠ ioUj := by decide
@[simp] theorem io_ioPm_ne_ioW : ioPm ≠ ioW := by decide
@[simp] theorem io_ioPm_ne_ioQj : ioPm ≠ ioQj := by decide
@[simp] theorem io_ioPm_ne_ioRn : ioPm ≠ ioRn := by decide
@[simp] theorem io_ioPm_ne_ioRl : ioPm ≠ ioRl := by decide
@[simp] theorem io_ioPm_ne_ioRq : ioPm ≠ ioRq := by decide
@[simp] theorem io_ioPm_ne_ioMa : ioPm ≠ ioMa := by decide
@[simp] theorem io_ioPm_ne_ioMl : ioPm ≠ ioMl := by decide
@[simp] theorem io_ioPm_ne_ioNp : ioPm ≠ ioNp := by decide
@[simp] theorem io_ioPm_ne_ioNf : ioPm ≠ ioNf := by decide
@[simp] theorem io_ioPm_ne_ioF : ioPm ≠ ioF := by decide
@[simp] theorem io_ioPm_ne_ioLp : ioPm ≠ ioLp := by decide
@[simp] theorem io_ioPm_ne_ioRc : ioPm ≠ ioRc := by decide
@[simp] theorem io_ioPm_ne_ioRh : ioPm ≠ ioRh := by decide
@[simp] theorem io_ioPm_ne_ioBd : ioPm ≠ ioBd := by decide
@[simp] theorem io_ioPm_ne_ioT1 : ioPm ≠ ioT1 := by decide
@[simp] theorem io_ioPm_ne_ioP : ioPm ≠ ioP := by decide
@[simp] theorem io_ioPm_ne_ioT2 : ioPm ≠ ioT2 := by decide
@[simp] theorem io_ioPm_ne_ioQq : ioPm ≠ ioQq := by decide
@[simp] theorem io_ioPm_ne_ioV : ioPm ≠ ioV := by decide
@[simp] theorem io_ioPm_ne_ioVl : ioPm ≠ ioVl := by decide
@[simp] theorem io_ioPm_ne_ioX : ioPm ≠ ioX := by decide
@[simp] theorem io_ioPm_ne_lFl : ioPm ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioPm : lFl ≠ ioPm := by decide
@[simp] theorem io_ioPm_ne_lDh : ioPm ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioPm : lDh ≠ ioPm := by decide
@[simp] theorem io_ioPm_ne_lDt : ioPm ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioPm : lDt ≠ ioPm := by decide
@[simp] theorem io_ioPm_ne_lDg : ioPm ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioPm : lDg ≠ ioPm := by decide
@[simp] theorem io_ioPm_ne_lDi : ioPm ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioPm : lDi ≠ ioPm := by decide
@[simp] theorem io_ioPm_ne_lRp : ioPm ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioPm : lRp ≠ ioPm := by decide
@[simp] theorem io_ioPm_ne_lRn : ioPm ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioPm : lRn ≠ ioPm := by decide
@[simp] theorem io_ioPm_ne_lFle : ioPm ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioPm : lFle ≠ ioPm := by decide
@[simp] theorem io_ioPm_ne_lDir : ioPm ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioPm : lDir ≠ ioPm := by decide
@[simp] theorem io_ioPm_ne_lKb : ioPm ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioPm : lKb ≠ ioPm := by decide
@[simp] theorem io_ioPm_ne_kFu : ioPm ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioPm : kFu ≠ ioPm := by decide
@[simp] theorem io_ioPm_ne_kD : ioPm ≠ kD := by decide
@[simp] theorem io_kD_ne_ioPm : kD ≠ ioPm := by decide
@[simp] theorem io_ioPm_ne_iC : ioPm ≠ iC := by decide
@[simp] theorem io_iC_ne_ioPm : iC ≠ ioPm := by decide
@[simp] theorem io_ioPm_ne_iU : ioPm ≠ iU := by decide
@[simp] theorem io_iU_ne_ioPm : iU ≠ ioPm := by decide
@[simp] theorem io_ioPm_ne_iQ : ioPm ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioPm : iQ ≠ ioPm := by decide
@[simp] theorem io_ioPm_ne_iA : ioPm ≠ iA := by decide
@[simp] theorem io_iA_ne_ioPm : iA ≠ ioPm := by decide
@[simp] theorem io_ioPm_ne_iK : ioPm ≠ iK := by decide
@[simp] theorem io_iK_ne_ioPm : iK ≠ ioPm := by decide
@[simp] theorem io_ioMe_ne_ioTy : ioMe ≠ ioTy := by decide
@[simp] theorem io_ioMe_ne_ioPp : ioMe ≠ ioPp := by decide
@[simp] theorem io_ioMe_ne_ioB0 : ioMe ≠ ioB0 := by decide
@[simp] theorem io_ioMe_ne_ioMj : ioMe ≠ ioMj := by decide
@[simp] theorem io_ioMe_ne_ioIk : ioMe ≠ ioIk := by decide
@[simp] theorem io_ioMe_ne_ioRs : ioMe ≠ ioRs := by decide
@[simp] theorem io_ioMe_ne_ioRp : ioMe ≠ ioRp := by decide
@[simp] theorem io_ioMe_ne_ioPm : ioMe ≠ ioPm := by decide
@[simp] theorem io_ioMe_ne_ioHd : ioMe ≠ ioHd := by decide
@[simp] theorem io_ioMe_ne_ioCj : ioMe ≠ ioCj := by decide
@[simp] theorem io_ioMe_ne_ioUj : ioMe ≠ ioUj := by decide
@[simp] theorem io_ioMe_ne_ioW : ioMe ≠ ioW := by decide
@[simp] theorem io_ioMe_ne_ioQj : ioMe ≠ ioQj := by decide
@[simp] theorem io_ioMe_ne_ioRn : ioMe ≠ ioRn := by decide
@[simp] theorem io_ioMe_ne_ioRl : ioMe ≠ ioRl := by decide
@[simp] theorem io_ioMe_ne_ioRq : ioMe ≠ ioRq := by decide
@[simp] theorem io_ioMe_ne_ioMa : ioMe ≠ ioMa := by decide
@[simp] theorem io_ioMe_ne_ioMl : ioMe ≠ ioMl := by decide
@[simp] theorem io_ioMe_ne_ioNp : ioMe ≠ ioNp := by decide
@[simp] theorem io_ioMe_ne_ioNf : ioMe ≠ ioNf := by decide
@[simp] theorem io_ioMe_ne_ioF : ioMe ≠ ioF := by decide
@[simp] theorem io_ioMe_ne_ioLp : ioMe ≠ ioLp := by decide
@[simp] theorem io_ioMe_ne_ioRc : ioMe ≠ ioRc := by decide
@[simp] theorem io_ioMe_ne_ioRh : ioMe ≠ ioRh := by decide
@[simp] theorem io_ioMe_ne_ioBd : ioMe ≠ ioBd := by decide
@[simp] theorem io_ioMe_ne_ioT1 : ioMe ≠ ioT1 := by decide
@[simp] theorem io_ioMe_ne_ioP : ioMe ≠ ioP := by decide
@[simp] theorem io_ioMe_ne_ioT2 : ioMe ≠ ioT2 := by decide
@[simp] theorem io_ioMe_ne_ioQq : ioMe ≠ ioQq := by decide
@[simp] theorem io_ioMe_ne_ioV : ioMe ≠ ioV := by decide
@[simp] theorem io_ioMe_ne_ioVl : ioMe ≠ ioVl := by decide
@[simp] theorem io_ioMe_ne_ioX : ioMe ≠ ioX := by decide
@[simp] theorem io_ioMe_ne_lFl : ioMe ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioMe : lFl ≠ ioMe := by decide
@[simp] theorem io_ioMe_ne_lDh : ioMe ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioMe : lDh ≠ ioMe := by decide
@[simp] theorem io_ioMe_ne_lDt : ioMe ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioMe : lDt ≠ ioMe := by decide
@[simp] theorem io_ioMe_ne_lDg : ioMe ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioMe : lDg ≠ ioMe := by decide
@[simp] theorem io_ioMe_ne_lDi : ioMe ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioMe : lDi ≠ ioMe := by decide
@[simp] theorem io_ioMe_ne_lRp : ioMe ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioMe : lRp ≠ ioMe := by decide
@[simp] theorem io_ioMe_ne_lRn : ioMe ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioMe : lRn ≠ ioMe := by decide
@[simp] theorem io_ioMe_ne_lFle : ioMe ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioMe : lFle ≠ ioMe := by decide
@[simp] theorem io_ioMe_ne_lDir : ioMe ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioMe : lDir ≠ ioMe := by decide
@[simp] theorem io_ioMe_ne_lKb : ioMe ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioMe : lKb ≠ ioMe := by decide
@[simp] theorem io_ioMe_ne_kFu : ioMe ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioMe : kFu ≠ ioMe := by decide
@[simp] theorem io_ioMe_ne_kD : ioMe ≠ kD := by decide
@[simp] theorem io_kD_ne_ioMe : kD ≠ ioMe := by decide
@[simp] theorem io_ioMe_ne_iC : ioMe ≠ iC := by decide
@[simp] theorem io_iC_ne_ioMe : iC ≠ ioMe := by decide
@[simp] theorem io_ioMe_ne_iU : ioMe ≠ iU := by decide
@[simp] theorem io_iU_ne_ioMe : iU ≠ ioMe := by decide
@[simp] theorem io_ioMe_ne_iQ : ioMe ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioMe : iQ ≠ ioMe := by decide
@[simp] theorem io_ioMe_ne_iA : ioMe ≠ iA := by decide
@[simp] theorem io_iA_ne_ioMe : iA ≠ ioMe := by decide
@[simp] theorem io_ioMe_ne_iK : ioMe ≠ iK := by decide
@[simp] theorem io_iK_ne_ioMe : iK ≠ ioMe := by decide
@[simp] theorem io_ioHd_ne_ioTy : ioHd ≠ ioTy := by decide
@[simp] theorem io_ioHd_ne_ioPp : ioHd ≠ ioPp := by decide
@[simp] theorem io_ioHd_ne_ioB0 : ioHd ≠ ioB0 := by decide
@[simp] theorem io_ioHd_ne_ioMj : ioHd ≠ ioMj := by decide
@[simp] theorem io_ioHd_ne_ioIk : ioHd ≠ ioIk := by decide
@[simp] theorem io_ioHd_ne_ioRs : ioHd ≠ ioRs := by decide
@[simp] theorem io_ioHd_ne_ioRp : ioHd ≠ ioRp := by decide
@[simp] theorem io_ioHd_ne_ioPm : ioHd ≠ ioPm := by decide
@[simp] theorem io_ioHd_ne_ioMe : ioHd ≠ ioMe := by decide
@[simp] theorem io_ioHd_ne_ioCj : ioHd ≠ ioCj := by decide
@[simp] theorem io_ioHd_ne_ioUj : ioHd ≠ ioUj := by decide
@[simp] theorem io_ioHd_ne_ioW : ioHd ≠ ioW := by decide
@[simp] theorem io_ioHd_ne_ioQj : ioHd ≠ ioQj := by decide
@[simp] theorem io_ioHd_ne_ioRn : ioHd ≠ ioRn := by decide
@[simp] theorem io_ioHd_ne_ioRl : ioHd ≠ ioRl := by decide
@[simp] theorem io_ioHd_ne_ioRq : ioHd ≠ ioRq := by decide
@[simp] theorem io_ioHd_ne_ioMa : ioHd ≠ ioMa := by decide
@[simp] theorem io_ioHd_ne_ioMl : ioHd ≠ ioMl := by decide
@[simp] theorem io_ioHd_ne_ioNp : ioHd ≠ ioNp := by decide
@[simp] theorem io_ioHd_ne_ioNf : ioHd ≠ ioNf := by decide
@[simp] theorem io_ioHd_ne_ioF : ioHd ≠ ioF := by decide
@[simp] theorem io_ioHd_ne_ioLp : ioHd ≠ ioLp := by decide
@[simp] theorem io_ioHd_ne_ioRc : ioHd ≠ ioRc := by decide
@[simp] theorem io_ioHd_ne_ioRh : ioHd ≠ ioRh := by decide
@[simp] theorem io_ioHd_ne_ioBd : ioHd ≠ ioBd := by decide
@[simp] theorem io_ioHd_ne_ioT1 : ioHd ≠ ioT1 := by decide
@[simp] theorem io_ioHd_ne_ioP : ioHd ≠ ioP := by decide
@[simp] theorem io_ioHd_ne_ioT2 : ioHd ≠ ioT2 := by decide
@[simp] theorem io_ioHd_ne_ioQq : ioHd ≠ ioQq := by decide
@[simp] theorem io_ioHd_ne_ioV : ioHd ≠ ioV := by decide
@[simp] theorem io_ioHd_ne_ioVl : ioHd ≠ ioVl := by decide
@[simp] theorem io_ioHd_ne_ioX : ioHd ≠ ioX := by decide
@[simp] theorem io_ioHd_ne_lFl : ioHd ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioHd : lFl ≠ ioHd := by decide
@[simp] theorem io_ioHd_ne_lDh : ioHd ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioHd : lDh ≠ ioHd := by decide
@[simp] theorem io_ioHd_ne_lDt : ioHd ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioHd : lDt ≠ ioHd := by decide
@[simp] theorem io_ioHd_ne_lDg : ioHd ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioHd : lDg ≠ ioHd := by decide
@[simp] theorem io_ioHd_ne_lDi : ioHd ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioHd : lDi ≠ ioHd := by decide
@[simp] theorem io_ioHd_ne_lRp : ioHd ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioHd : lRp ≠ ioHd := by decide
@[simp] theorem io_ioHd_ne_lRn : ioHd ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioHd : lRn ≠ ioHd := by decide
@[simp] theorem io_ioHd_ne_lFle : ioHd ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioHd : lFle ≠ ioHd := by decide
@[simp] theorem io_ioHd_ne_lDir : ioHd ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioHd : lDir ≠ ioHd := by decide
@[simp] theorem io_ioHd_ne_lKb : ioHd ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioHd : lKb ≠ ioHd := by decide
@[simp] theorem io_ioHd_ne_kFu : ioHd ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioHd : kFu ≠ ioHd := by decide
@[simp] theorem io_ioHd_ne_kD : ioHd ≠ kD := by decide
@[simp] theorem io_kD_ne_ioHd : kD ≠ ioHd := by decide
@[simp] theorem io_ioHd_ne_iC : ioHd ≠ iC := by decide
@[simp] theorem io_iC_ne_ioHd : iC ≠ ioHd := by decide
@[simp] theorem io_ioHd_ne_iU : ioHd ≠ iU := by decide
@[simp] theorem io_iU_ne_ioHd : iU ≠ ioHd := by decide
@[simp] theorem io_ioHd_ne_iQ : ioHd ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioHd : iQ ≠ ioHd := by decide
@[simp] theorem io_ioHd_ne_iA : ioHd ≠ iA := by decide
@[simp] theorem io_iA_ne_ioHd : iA ≠ ioHd := by decide
@[simp] theorem io_ioHd_ne_iK : ioHd ≠ iK := by decide
@[simp] theorem io_iK_ne_ioHd : iK ≠ ioHd := by decide
@[simp] theorem io_ioCj_ne_ioTy : ioCj ≠ ioTy := by decide
@[simp] theorem io_ioCj_ne_ioPp : ioCj ≠ ioPp := by decide
@[simp] theorem io_ioCj_ne_ioB0 : ioCj ≠ ioB0 := by decide
@[simp] theorem io_ioCj_ne_ioMj : ioCj ≠ ioMj := by decide
@[simp] theorem io_ioCj_ne_ioIk : ioCj ≠ ioIk := by decide
@[simp] theorem io_ioCj_ne_ioRs : ioCj ≠ ioRs := by decide
@[simp] theorem io_ioCj_ne_ioRp : ioCj ≠ ioRp := by decide
@[simp] theorem io_ioCj_ne_ioPm : ioCj ≠ ioPm := by decide
@[simp] theorem io_ioCj_ne_ioMe : ioCj ≠ ioMe := by decide
@[simp] theorem io_ioCj_ne_ioHd : ioCj ≠ ioHd := by decide
@[simp] theorem io_ioCj_ne_ioUj : ioCj ≠ ioUj := by decide
@[simp] theorem io_ioCj_ne_ioW : ioCj ≠ ioW := by decide
@[simp] theorem io_ioCj_ne_ioQj : ioCj ≠ ioQj := by decide
@[simp] theorem io_ioCj_ne_ioRn : ioCj ≠ ioRn := by decide
@[simp] theorem io_ioCj_ne_ioRl : ioCj ≠ ioRl := by decide
@[simp] theorem io_ioCj_ne_ioRq : ioCj ≠ ioRq := by decide
@[simp] theorem io_ioCj_ne_ioMa : ioCj ≠ ioMa := by decide
@[simp] theorem io_ioCj_ne_ioMl : ioCj ≠ ioMl := by decide
@[simp] theorem io_ioCj_ne_ioNp : ioCj ≠ ioNp := by decide
@[simp] theorem io_ioCj_ne_ioNf : ioCj ≠ ioNf := by decide
@[simp] theorem io_ioCj_ne_ioF : ioCj ≠ ioF := by decide
@[simp] theorem io_ioCj_ne_ioLp : ioCj ≠ ioLp := by decide
@[simp] theorem io_ioCj_ne_ioRc : ioCj ≠ ioRc := by decide
@[simp] theorem io_ioCj_ne_ioRh : ioCj ≠ ioRh := by decide
@[simp] theorem io_ioCj_ne_ioBd : ioCj ≠ ioBd := by decide
@[simp] theorem io_ioCj_ne_ioT1 : ioCj ≠ ioT1 := by decide
@[simp] theorem io_ioCj_ne_ioP : ioCj ≠ ioP := by decide
@[simp] theorem io_ioCj_ne_ioT2 : ioCj ≠ ioT2 := by decide
@[simp] theorem io_ioCj_ne_ioQq : ioCj ≠ ioQq := by decide
@[simp] theorem io_ioCj_ne_ioV : ioCj ≠ ioV := by decide
@[simp] theorem io_ioCj_ne_ioVl : ioCj ≠ ioVl := by decide
@[simp] theorem io_ioCj_ne_ioX : ioCj ≠ ioX := by decide
@[simp] theorem io_ioCj_ne_lFl : ioCj ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioCj : lFl ≠ ioCj := by decide
@[simp] theorem io_ioCj_ne_lDh : ioCj ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioCj : lDh ≠ ioCj := by decide
@[simp] theorem io_ioCj_ne_lDt : ioCj ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioCj : lDt ≠ ioCj := by decide
@[simp] theorem io_ioCj_ne_lDg : ioCj ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioCj : lDg ≠ ioCj := by decide
@[simp] theorem io_ioCj_ne_lDi : ioCj ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioCj : lDi ≠ ioCj := by decide
@[simp] theorem io_ioCj_ne_lRp : ioCj ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioCj : lRp ≠ ioCj := by decide
@[simp] theorem io_ioCj_ne_lRn : ioCj ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioCj : lRn ≠ ioCj := by decide
@[simp] theorem io_ioCj_ne_lFle : ioCj ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioCj : lFle ≠ ioCj := by decide
@[simp] theorem io_ioCj_ne_lDir : ioCj ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioCj : lDir ≠ ioCj := by decide
@[simp] theorem io_ioCj_ne_lKb : ioCj ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioCj : lKb ≠ ioCj := by decide
@[simp] theorem io_ioCj_ne_kFu : ioCj ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioCj : kFu ≠ ioCj := by decide
@[simp] theorem io_ioCj_ne_kD : ioCj ≠ kD := by decide
@[simp] theorem io_kD_ne_ioCj : kD ≠ ioCj := by decide
@[simp] theorem io_ioCj_ne_iC : ioCj ≠ iC := by decide
@[simp] theorem io_iC_ne_ioCj : iC ≠ ioCj := by decide
@[simp] theorem io_ioCj_ne_iU : ioCj ≠ iU := by decide
@[simp] theorem io_iU_ne_ioCj : iU ≠ ioCj := by decide
@[simp] theorem io_ioCj_ne_iQ : ioCj ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioCj : iQ ≠ ioCj := by decide
@[simp] theorem io_ioCj_ne_iA : ioCj ≠ iA := by decide
@[simp] theorem io_iA_ne_ioCj : iA ≠ ioCj := by decide
@[simp] theorem io_ioCj_ne_iK : ioCj ≠ iK := by decide
@[simp] theorem io_iK_ne_ioCj : iK ≠ ioCj := by decide
@[simp] theorem io_ioUj_ne_ioTy : ioUj ≠ ioTy := by decide
@[simp] theorem io_ioUj_ne_ioPp : ioUj ≠ ioPp := by decide
@[simp] theorem io_ioUj_ne_ioB0 : ioUj ≠ ioB0 := by decide
@[simp] theorem io_ioUj_ne_ioMj : ioUj ≠ ioMj := by decide
@[simp] theorem io_ioUj_ne_ioIk : ioUj ≠ ioIk := by decide
@[simp] theorem io_ioUj_ne_ioRs : ioUj ≠ ioRs := by decide
@[simp] theorem io_ioUj_ne_ioRp : ioUj ≠ ioRp := by decide
@[simp] theorem io_ioUj_ne_ioPm : ioUj ≠ ioPm := by decide
@[simp] theorem io_ioUj_ne_ioMe : ioUj ≠ ioMe := by decide
@[simp] theorem io_ioUj_ne_ioHd : ioUj ≠ ioHd := by decide
@[simp] theorem io_ioUj_ne_ioCj : ioUj ≠ ioCj := by decide
@[simp] theorem io_ioUj_ne_ioW : ioUj ≠ ioW := by decide
@[simp] theorem io_ioUj_ne_ioQj : ioUj ≠ ioQj := by decide
@[simp] theorem io_ioUj_ne_ioRn : ioUj ≠ ioRn := by decide
@[simp] theorem io_ioUj_ne_ioRl : ioUj ≠ ioRl := by decide
@[simp] theorem io_ioUj_ne_ioRq : ioUj ≠ ioRq := by decide
@[simp] theorem io_ioUj_ne_ioMa : ioUj ≠ ioMa := by decide
@[simp] theorem io_ioUj_ne_ioMl : ioUj ≠ ioMl := by decide
@[simp] theorem io_ioUj_ne_ioNp : ioUj ≠ ioNp := by decide
@[simp] theorem io_ioUj_ne_ioNf : ioUj ≠ ioNf := by decide
@[simp] theorem io_ioUj_ne_ioF : ioUj ≠ ioF := by decide
@[simp] theorem io_ioUj_ne_ioLp : ioUj ≠ ioLp := by decide
@[simp] theorem io_ioUj_ne_ioRc : ioUj ≠ ioRc := by decide
@[simp] theorem io_ioUj_ne_ioRh : ioUj ≠ ioRh := by decide
@[simp] theorem io_ioUj_ne_ioBd : ioUj ≠ ioBd := by decide
@[simp] theorem io_ioUj_ne_ioT1 : ioUj ≠ ioT1 := by decide
@[simp] theorem io_ioUj_ne_ioP : ioUj ≠ ioP := by decide
@[simp] theorem io_ioUj_ne_ioT2 : ioUj ≠ ioT2 := by decide
@[simp] theorem io_ioUj_ne_ioQq : ioUj ≠ ioQq := by decide
@[simp] theorem io_ioUj_ne_ioV : ioUj ≠ ioV := by decide
@[simp] theorem io_ioUj_ne_ioVl : ioUj ≠ ioVl := by decide
@[simp] theorem io_ioUj_ne_ioX : ioUj ≠ ioX := by decide
@[simp] theorem io_ioUj_ne_lFl : ioUj ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioUj : lFl ≠ ioUj := by decide
@[simp] theorem io_ioUj_ne_lDh : ioUj ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioUj : lDh ≠ ioUj := by decide
@[simp] theorem io_ioUj_ne_lDt : ioUj ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioUj : lDt ≠ ioUj := by decide
@[simp] theorem io_ioUj_ne_lDg : ioUj ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioUj : lDg ≠ ioUj := by decide
@[simp] theorem io_ioUj_ne_lDi : ioUj ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioUj : lDi ≠ ioUj := by decide
@[simp] theorem io_ioUj_ne_lRp : ioUj ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioUj : lRp ≠ ioUj := by decide
@[simp] theorem io_ioUj_ne_lRn : ioUj ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioUj : lRn ≠ ioUj := by decide
@[simp] theorem io_ioUj_ne_lFle : ioUj ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioUj : lFle ≠ ioUj := by decide
@[simp] theorem io_ioUj_ne_lDir : ioUj ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioUj : lDir ≠ ioUj := by decide
@[simp] theorem io_ioUj_ne_lKb : ioUj ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioUj : lKb ≠ ioUj := by decide
@[simp] theorem io_ioUj_ne_kFu : ioUj ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioUj : kFu ≠ ioUj := by decide
@[simp] theorem io_ioUj_ne_kD : ioUj ≠ kD := by decide
@[simp] theorem io_kD_ne_ioUj : kD ≠ ioUj := by decide
@[simp] theorem io_ioUj_ne_iC : ioUj ≠ iC := by decide
@[simp] theorem io_iC_ne_ioUj : iC ≠ ioUj := by decide
@[simp] theorem io_ioUj_ne_iU : ioUj ≠ iU := by decide
@[simp] theorem io_iU_ne_ioUj : iU ≠ ioUj := by decide
@[simp] theorem io_ioUj_ne_iQ : ioUj ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioUj : iQ ≠ ioUj := by decide
@[simp] theorem io_ioUj_ne_iA : ioUj ≠ iA := by decide
@[simp] theorem io_iA_ne_ioUj : iA ≠ ioUj := by decide
@[simp] theorem io_ioUj_ne_iK : ioUj ≠ iK := by decide
@[simp] theorem io_iK_ne_ioUj : iK ≠ ioUj := by decide
@[simp] theorem io_ioW_ne_ioTy : ioW ≠ ioTy := by decide
@[simp] theorem io_ioW_ne_ioPp : ioW ≠ ioPp := by decide
@[simp] theorem io_ioW_ne_ioB0 : ioW ≠ ioB0 := by decide
@[simp] theorem io_ioW_ne_ioMj : ioW ≠ ioMj := by decide
@[simp] theorem io_ioW_ne_ioIk : ioW ≠ ioIk := by decide
@[simp] theorem io_ioW_ne_ioRs : ioW ≠ ioRs := by decide
@[simp] theorem io_ioW_ne_ioRp : ioW ≠ ioRp := by decide
@[simp] theorem io_ioW_ne_ioPm : ioW ≠ ioPm := by decide
@[simp] theorem io_ioW_ne_ioMe : ioW ≠ ioMe := by decide
@[simp] theorem io_ioW_ne_ioHd : ioW ≠ ioHd := by decide
@[simp] theorem io_ioW_ne_ioCj : ioW ≠ ioCj := by decide
@[simp] theorem io_ioW_ne_ioUj : ioW ≠ ioUj := by decide
@[simp] theorem io_ioW_ne_ioQj : ioW ≠ ioQj := by decide
@[simp] theorem io_ioW_ne_ioRn : ioW ≠ ioRn := by decide
@[simp] theorem io_ioW_ne_ioRl : ioW ≠ ioRl := by decide
@[simp] theorem io_ioW_ne_ioRq : ioW ≠ ioRq := by decide
@[simp] theorem io_ioW_ne_ioMa : ioW ≠ ioMa := by decide
@[simp] theorem io_ioW_ne_ioMl : ioW ≠ ioMl := by decide
@[simp] theorem io_ioW_ne_ioNp : ioW ≠ ioNp := by decide
@[simp] theorem io_ioW_ne_ioNf : ioW ≠ ioNf := by decide
@[simp] theorem io_ioW_ne_ioF : ioW ≠ ioF := by decide
@[simp] theorem io_ioW_ne_ioLp : ioW ≠ ioLp := by decide
@[simp] theorem io_ioW_ne_ioRc : ioW ≠ ioRc := by decide
@[simp] theorem io_ioW_ne_ioRh : ioW ≠ ioRh := by decide
@[simp] theorem io_ioW_ne_ioBd : ioW ≠ ioBd := by decide
@[simp] theorem io_ioW_ne_ioT1 : ioW ≠ ioT1 := by decide
@[simp] theorem io_ioW_ne_ioP : ioW ≠ ioP := by decide
@[simp] theorem io_ioW_ne_ioT2 : ioW ≠ ioT2 := by decide
@[simp] theorem io_ioW_ne_ioQq : ioW ≠ ioQq := by decide
@[simp] theorem io_ioW_ne_ioV : ioW ≠ ioV := by decide
@[simp] theorem io_ioW_ne_ioVl : ioW ≠ ioVl := by decide
@[simp] theorem io_ioW_ne_ioX : ioW ≠ ioX := by decide
@[simp] theorem io_ioW_ne_lFl : ioW ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioW : lFl ≠ ioW := by decide
@[simp] theorem io_ioW_ne_lDh : ioW ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioW : lDh ≠ ioW := by decide
@[simp] theorem io_ioW_ne_lDt : ioW ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioW : lDt ≠ ioW := by decide
@[simp] theorem io_ioW_ne_lDg : ioW ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioW : lDg ≠ ioW := by decide
@[simp] theorem io_ioW_ne_lDi : ioW ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioW : lDi ≠ ioW := by decide
@[simp] theorem io_ioW_ne_lRp : ioW ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioW : lRp ≠ ioW := by decide
@[simp] theorem io_ioW_ne_lRn : ioW ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioW : lRn ≠ ioW := by decide
@[simp] theorem io_ioW_ne_lFle : ioW ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioW : lFle ≠ ioW := by decide
@[simp] theorem io_ioW_ne_lDir : ioW ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioW : lDir ≠ ioW := by decide
@[simp] theorem io_ioW_ne_lKb : ioW ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioW : lKb ≠ ioW := by decide
@[simp] theorem io_ioW_ne_kFu : ioW ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioW : kFu ≠ ioW := by decide
@[simp] theorem io_ioW_ne_kD : ioW ≠ kD := by decide
@[simp] theorem io_kD_ne_ioW : kD ≠ ioW := by decide
@[simp] theorem io_ioW_ne_iC : ioW ≠ iC := by decide
@[simp] theorem io_iC_ne_ioW : iC ≠ ioW := by decide
@[simp] theorem io_ioW_ne_iU : ioW ≠ iU := by decide
@[simp] theorem io_iU_ne_ioW : iU ≠ ioW := by decide
@[simp] theorem io_ioW_ne_iQ : ioW ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioW : iQ ≠ ioW := by decide
@[simp] theorem io_ioW_ne_iA : ioW ≠ iA := by decide
@[simp] theorem io_iA_ne_ioW : iA ≠ ioW := by decide
@[simp] theorem io_ioW_ne_iK : ioW ≠ iK := by decide
@[simp] theorem io_iK_ne_ioW : iK ≠ ioW := by decide
@[simp] theorem io_ioQj_ne_ioTy : ioQj ≠ ioTy := by decide
@[simp] theorem io_ioQj_ne_ioPp : ioQj ≠ ioPp := by decide
@[simp] theorem io_ioQj_ne_ioB0 : ioQj ≠ ioB0 := by decide
@[simp] theorem io_ioQj_ne_ioMj : ioQj ≠ ioMj := by decide
@[simp] theorem io_ioQj_ne_ioIk : ioQj ≠ ioIk := by decide
@[simp] theorem io_ioQj_ne_ioRs : ioQj ≠ ioRs := by decide
@[simp] theorem io_ioQj_ne_ioRp : ioQj ≠ ioRp := by decide
@[simp] theorem io_ioQj_ne_ioPm : ioQj ≠ ioPm := by decide
@[simp] theorem io_ioQj_ne_ioMe : ioQj ≠ ioMe := by decide
@[simp] theorem io_ioQj_ne_ioHd : ioQj ≠ ioHd := by decide
@[simp] theorem io_ioQj_ne_ioCj : ioQj ≠ ioCj := by decide
@[simp] theorem io_ioQj_ne_ioUj : ioQj ≠ ioUj := by decide
@[simp] theorem io_ioQj_ne_ioW : ioQj ≠ ioW := by decide
@[simp] theorem io_ioQj_ne_ioRn : ioQj ≠ ioRn := by decide
@[simp] theorem io_ioQj_ne_ioRl : ioQj ≠ ioRl := by decide
@[simp] theorem io_ioQj_ne_ioRq : ioQj ≠ ioRq := by decide
@[simp] theorem io_ioQj_ne_ioMa : ioQj ≠ ioMa := by decide
@[simp] theorem io_ioQj_ne_ioMl : ioQj ≠ ioMl := by decide
@[simp] theorem io_ioQj_ne_ioNp : ioQj ≠ ioNp := by decide
@[simp] theorem io_ioQj_ne_ioNf : ioQj ≠ ioNf := by decide
@[simp] theorem io_ioQj_ne_ioF : ioQj ≠ ioF := by decide
@[simp] theorem io_ioQj_ne_ioLp : ioQj ≠ ioLp := by decide
@[simp] theorem io_ioQj_ne_ioRc : ioQj ≠ ioRc := by decide
@[simp] theorem io_ioQj_ne_ioRh : ioQj ≠ ioRh := by decide
@[simp] theorem io_ioQj_ne_ioBd : ioQj ≠ ioBd := by decide
@[simp] theorem io_ioQj_ne_ioT1 : ioQj ≠ ioT1 := by decide
@[simp] theorem io_ioQj_ne_ioP : ioQj ≠ ioP := by decide
@[simp] theorem io_ioQj_ne_ioT2 : ioQj ≠ ioT2 := by decide
@[simp] theorem io_ioQj_ne_ioQq : ioQj ≠ ioQq := by decide
@[simp] theorem io_ioQj_ne_ioV : ioQj ≠ ioV := by decide
@[simp] theorem io_ioQj_ne_ioVl : ioQj ≠ ioVl := by decide
@[simp] theorem io_ioQj_ne_ioX : ioQj ≠ ioX := by decide
@[simp] theorem io_ioQj_ne_lFl : ioQj ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioQj : lFl ≠ ioQj := by decide
@[simp] theorem io_ioQj_ne_lDh : ioQj ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioQj : lDh ≠ ioQj := by decide
@[simp] theorem io_ioQj_ne_lDt : ioQj ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioQj : lDt ≠ ioQj := by decide
@[simp] theorem io_ioQj_ne_lDg : ioQj ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioQj : lDg ≠ ioQj := by decide
@[simp] theorem io_ioQj_ne_lDi : ioQj ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioQj : lDi ≠ ioQj := by decide
@[simp] theorem io_ioQj_ne_lRp : ioQj ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioQj : lRp ≠ ioQj := by decide
@[simp] theorem io_ioQj_ne_lRn : ioQj ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioQj : lRn ≠ ioQj := by decide
@[simp] theorem io_ioQj_ne_lFle : ioQj ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioQj : lFle ≠ ioQj := by decide
@[simp] theorem io_ioQj_ne_lDir : ioQj ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioQj : lDir ≠ ioQj := by decide
@[simp] theorem io_ioQj_ne_lKb : ioQj ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioQj : lKb ≠ ioQj := by decide
@[simp] theorem io_ioQj_ne_kFu : ioQj ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioQj : kFu ≠ ioQj := by decide
@[simp] theorem io_ioQj_ne_kD : ioQj ≠ kD := by decide
@[simp] theorem io_kD_ne_ioQj : kD ≠ ioQj := by decide
@[simp] theorem io_ioQj_ne_iC : ioQj ≠ iC := by decide
@[simp] theorem io_iC_ne_ioQj : iC ≠ ioQj := by decide
@[simp] theorem io_ioQj_ne_iU : ioQj ≠ iU := by decide
@[simp] theorem io_iU_ne_ioQj : iU ≠ ioQj := by decide
@[simp] theorem io_ioQj_ne_iQ : ioQj ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioQj : iQ ≠ ioQj := by decide
@[simp] theorem io_ioQj_ne_iA : ioQj ≠ iA := by decide
@[simp] theorem io_iA_ne_ioQj : iA ≠ ioQj := by decide
@[simp] theorem io_ioQj_ne_iK : ioQj ≠ iK := by decide
@[simp] theorem io_iK_ne_ioQj : iK ≠ ioQj := by decide
@[simp] theorem io_ioRn_ne_ioTy : ioRn ≠ ioTy := by decide
@[simp] theorem io_ioRn_ne_ioPp : ioRn ≠ ioPp := by decide
@[simp] theorem io_ioRn_ne_ioB0 : ioRn ≠ ioB0 := by decide
@[simp] theorem io_ioRn_ne_ioMj : ioRn ≠ ioMj := by decide
@[simp] theorem io_ioRn_ne_ioIk : ioRn ≠ ioIk := by decide
@[simp] theorem io_ioRn_ne_ioRs : ioRn ≠ ioRs := by decide
@[simp] theorem io_ioRn_ne_ioRp : ioRn ≠ ioRp := by decide
@[simp] theorem io_ioRn_ne_ioPm : ioRn ≠ ioPm := by decide
@[simp] theorem io_ioRn_ne_ioMe : ioRn ≠ ioMe := by decide
@[simp] theorem io_ioRn_ne_ioHd : ioRn ≠ ioHd := by decide
@[simp] theorem io_ioRn_ne_ioCj : ioRn ≠ ioCj := by decide
@[simp] theorem io_ioRn_ne_ioUj : ioRn ≠ ioUj := by decide
@[simp] theorem io_ioRn_ne_ioW : ioRn ≠ ioW := by decide
@[simp] theorem io_ioRn_ne_ioQj : ioRn ≠ ioQj := by decide
@[simp] theorem io_ioRn_ne_ioRl : ioRn ≠ ioRl := by decide
@[simp] theorem io_ioRn_ne_ioRq : ioRn ≠ ioRq := by decide
@[simp] theorem io_ioRn_ne_ioMa : ioRn ≠ ioMa := by decide
@[simp] theorem io_ioRn_ne_ioMl : ioRn ≠ ioMl := by decide
@[simp] theorem io_ioRn_ne_ioNp : ioRn ≠ ioNp := by decide
@[simp] theorem io_ioRn_ne_ioNf : ioRn ≠ ioNf := by decide
@[simp] theorem io_ioRn_ne_ioF : ioRn ≠ ioF := by decide
@[simp] theorem io_ioRn_ne_ioLp : ioRn ≠ ioLp := by decide
@[simp] theorem io_ioRn_ne_ioRc : ioRn ≠ ioRc := by decide
@[simp] theorem io_ioRn_ne_ioRh : ioRn ≠ ioRh := by decide
@[simp] theorem io_ioRn_ne_ioBd : ioRn ≠ ioBd := by decide
@[simp] theorem io_ioRn_ne_ioT1 : ioRn ≠ ioT1 := by decide
@[simp] theorem io_ioRn_ne_ioP : ioRn ≠ ioP := by decide
@[simp] theorem io_ioRn_ne_ioT2 : ioRn ≠ ioT2 := by decide
@[simp] theorem io_ioRn_ne_ioQq : ioRn ≠ ioQq := by decide
@[simp] theorem io_ioRn_ne_ioV : ioRn ≠ ioV := by decide
@[simp] theorem io_ioRn_ne_ioVl : ioRn ≠ ioVl := by decide
@[simp] theorem io_ioRn_ne_ioX : ioRn ≠ ioX := by decide
@[simp] theorem io_ioRn_ne_lFl : ioRn ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioRn : lFl ≠ ioRn := by decide
@[simp] theorem io_ioRn_ne_lDh : ioRn ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioRn : lDh ≠ ioRn := by decide
@[simp] theorem io_ioRn_ne_lDt : ioRn ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioRn : lDt ≠ ioRn := by decide
@[simp] theorem io_ioRn_ne_lDg : ioRn ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioRn : lDg ≠ ioRn := by decide
@[simp] theorem io_ioRn_ne_lDi : ioRn ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioRn : lDi ≠ ioRn := by decide
@[simp] theorem io_ioRn_ne_lRp : ioRn ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioRn : lRp ≠ ioRn := by decide
@[simp] theorem io_ioRn_ne_lRn : ioRn ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioRn : lRn ≠ ioRn := by decide
@[simp] theorem io_ioRn_ne_lFle : ioRn ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioRn : lFle ≠ ioRn := by decide
@[simp] theorem io_ioRn_ne_lDir : ioRn ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioRn : lDir ≠ ioRn := by decide
@[simp] theorem io_ioRn_ne_lKb : ioRn ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioRn : lKb ≠ ioRn := by decide
@[simp] theorem io_ioRn_ne_kFu : ioRn ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioRn : kFu ≠ ioRn := by decide
@[simp] theorem io_ioRn_ne_kD : ioRn ≠ kD := by decide
@[simp] theorem io_kD_ne_ioRn : kD ≠ ioRn := by decide
@[simp] theorem io_ioRn_ne_iC : ioRn ≠ iC := by decide
@[simp] theorem io_iC_ne_ioRn : iC ≠ ioRn := by decide
@[simp] theorem io_ioRn_ne_iU : ioRn ≠ iU := by decide
@[simp] theorem io_iU_ne_ioRn : iU ≠ ioRn := by decide
@[simp] theorem io_ioRn_ne_iQ : ioRn ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioRn : iQ ≠ ioRn := by decide
@[simp] theorem io_ioRn_ne_iA : ioRn ≠ iA := by decide
@[simp] theorem io_iA_ne_ioRn : iA ≠ ioRn := by decide
@[simp] theorem io_ioRn_ne_iK : ioRn ≠ iK := by decide
@[simp] theorem io_iK_ne_ioRn : iK ≠ ioRn := by decide
@[simp] theorem io_ioRl_ne_ioTy : ioRl ≠ ioTy := by decide
@[simp] theorem io_ioRl_ne_ioPp : ioRl ≠ ioPp := by decide
@[simp] theorem io_ioRl_ne_ioB0 : ioRl ≠ ioB0 := by decide
@[simp] theorem io_ioRl_ne_ioMj : ioRl ≠ ioMj := by decide
@[simp] theorem io_ioRl_ne_ioIk : ioRl ≠ ioIk := by decide
@[simp] theorem io_ioRl_ne_ioRs : ioRl ≠ ioRs := by decide
@[simp] theorem io_ioRl_ne_ioRp : ioRl ≠ ioRp := by decide
@[simp] theorem io_ioRl_ne_ioPm : ioRl ≠ ioPm := by decide
@[simp] theorem io_ioRl_ne_ioMe : ioRl ≠ ioMe := by decide
@[simp] theorem io_ioRl_ne_ioHd : ioRl ≠ ioHd := by decide
@[simp] theorem io_ioRl_ne_ioCj : ioRl ≠ ioCj := by decide
@[simp] theorem io_ioRl_ne_ioUj : ioRl ≠ ioUj := by decide
@[simp] theorem io_ioRl_ne_ioW : ioRl ≠ ioW := by decide
@[simp] theorem io_ioRl_ne_ioQj : ioRl ≠ ioQj := by decide
@[simp] theorem io_ioRl_ne_ioRn : ioRl ≠ ioRn := by decide
@[simp] theorem io_ioRl_ne_ioRq : ioRl ≠ ioRq := by decide
@[simp] theorem io_ioRl_ne_ioMa : ioRl ≠ ioMa := by decide
@[simp] theorem io_ioRl_ne_ioMl : ioRl ≠ ioMl := by decide
@[simp] theorem io_ioRl_ne_ioNp : ioRl ≠ ioNp := by decide
@[simp] theorem io_ioRl_ne_ioNf : ioRl ≠ ioNf := by decide
@[simp] theorem io_ioRl_ne_ioF : ioRl ≠ ioF := by decide
@[simp] theorem io_ioRl_ne_ioLp : ioRl ≠ ioLp := by decide
@[simp] theorem io_ioRl_ne_ioRc : ioRl ≠ ioRc := by decide
@[simp] theorem io_ioRl_ne_ioRh : ioRl ≠ ioRh := by decide
@[simp] theorem io_ioRl_ne_ioBd : ioRl ≠ ioBd := by decide
@[simp] theorem io_ioRl_ne_ioT1 : ioRl ≠ ioT1 := by decide
@[simp] theorem io_ioRl_ne_ioP : ioRl ≠ ioP := by decide
@[simp] theorem io_ioRl_ne_ioT2 : ioRl ≠ ioT2 := by decide
@[simp] theorem io_ioRl_ne_ioQq : ioRl ≠ ioQq := by decide
@[simp] theorem io_ioRl_ne_ioV : ioRl ≠ ioV := by decide
@[simp] theorem io_ioRl_ne_ioVl : ioRl ≠ ioVl := by decide
@[simp] theorem io_ioRl_ne_ioX : ioRl ≠ ioX := by decide
@[simp] theorem io_ioRl_ne_lFl : ioRl ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioRl : lFl ≠ ioRl := by decide
@[simp] theorem io_ioRl_ne_lDh : ioRl ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioRl : lDh ≠ ioRl := by decide
@[simp] theorem io_ioRl_ne_lDt : ioRl ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioRl : lDt ≠ ioRl := by decide
@[simp] theorem io_ioRl_ne_lDg : ioRl ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioRl : lDg ≠ ioRl := by decide
@[simp] theorem io_ioRl_ne_lDi : ioRl ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioRl : lDi ≠ ioRl := by decide
@[simp] theorem io_ioRl_ne_lRp : ioRl ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioRl : lRp ≠ ioRl := by decide
@[simp] theorem io_ioRl_ne_lRn : ioRl ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioRl : lRn ≠ ioRl := by decide
@[simp] theorem io_ioRl_ne_lFle : ioRl ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioRl : lFle ≠ ioRl := by decide
@[simp] theorem io_ioRl_ne_lDir : ioRl ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioRl : lDir ≠ ioRl := by decide
@[simp] theorem io_ioRl_ne_lKb : ioRl ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioRl : lKb ≠ ioRl := by decide
@[simp] theorem io_ioRl_ne_kFu : ioRl ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioRl : kFu ≠ ioRl := by decide
@[simp] theorem io_ioRl_ne_kD : ioRl ≠ kD := by decide
@[simp] theorem io_kD_ne_ioRl : kD ≠ ioRl := by decide
@[simp] theorem io_ioRl_ne_iC : ioRl ≠ iC := by decide
@[simp] theorem io_iC_ne_ioRl : iC ≠ ioRl := by decide
@[simp] theorem io_ioRl_ne_iU : ioRl ≠ iU := by decide
@[simp] theorem io_iU_ne_ioRl : iU ≠ ioRl := by decide
@[simp] theorem io_ioRl_ne_iQ : ioRl ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioRl : iQ ≠ ioRl := by decide
@[simp] theorem io_ioRl_ne_iA : ioRl ≠ iA := by decide
@[simp] theorem io_iA_ne_ioRl : iA ≠ ioRl := by decide
@[simp] theorem io_ioRl_ne_iK : ioRl ≠ iK := by decide
@[simp] theorem io_iK_ne_ioRl : iK ≠ ioRl := by decide
@[simp] theorem io_ioRq_ne_ioTy : ioRq ≠ ioTy := by decide
@[simp] theorem io_ioRq_ne_ioPp : ioRq ≠ ioPp := by decide
@[simp] theorem io_ioRq_ne_ioB0 : ioRq ≠ ioB0 := by decide
@[simp] theorem io_ioRq_ne_ioMj : ioRq ≠ ioMj := by decide
@[simp] theorem io_ioRq_ne_ioIk : ioRq ≠ ioIk := by decide
@[simp] theorem io_ioRq_ne_ioRs : ioRq ≠ ioRs := by decide
@[simp] theorem io_ioRq_ne_ioRp : ioRq ≠ ioRp := by decide
@[simp] theorem io_ioRq_ne_ioPm : ioRq ≠ ioPm := by decide
@[simp] theorem io_ioRq_ne_ioMe : ioRq ≠ ioMe := by decide
@[simp] theorem io_ioRq_ne_ioHd : ioRq ≠ ioHd := by decide
@[simp] theorem io_ioRq_ne_ioCj : ioRq ≠ ioCj := by decide
@[simp] theorem io_ioRq_ne_ioUj : ioRq ≠ ioUj := by decide
@[simp] theorem io_ioRq_ne_ioW : ioRq ≠ ioW := by decide
@[simp] theorem io_ioRq_ne_ioQj : ioRq ≠ ioQj := by decide
@[simp] theorem io_ioRq_ne_ioRn : ioRq ≠ ioRn := by decide
@[simp] theorem io_ioRq_ne_ioRl : ioRq ≠ ioRl := by decide
@[simp] theorem io_ioRq_ne_ioMa : ioRq ≠ ioMa := by decide
@[simp] theorem io_ioRq_ne_ioMl : ioRq ≠ ioMl := by decide
@[simp] theorem io_ioRq_ne_ioNp : ioRq ≠ ioNp := by decide
@[simp] theorem io_ioRq_ne_ioNf : ioRq ≠ ioNf := by decide
@[simp] theorem io_ioRq_ne_ioF : ioRq ≠ ioF := by decide
@[simp] theorem io_ioRq_ne_ioLp : ioRq ≠ ioLp := by decide
@[simp] theorem io_ioRq_ne_ioRc : ioRq ≠ ioRc := by decide
@[simp] theorem io_ioRq_ne_ioRh : ioRq ≠ ioRh := by decide
@[simp] theorem io_ioRq_ne_ioBd : ioRq ≠ ioBd := by decide
@[simp] theorem io_ioRq_ne_ioT1 : ioRq ≠ ioT1 := by decide
@[simp] theorem io_ioRq_ne_ioP : ioRq ≠ ioP := by decide
@[simp] theorem io_ioRq_ne_ioT2 : ioRq ≠ ioT2 := by decide
@[simp] theorem io_ioRq_ne_ioQq : ioRq ≠ ioQq := by decide
@[simp] theorem io_ioRq_ne_ioV : ioRq ≠ ioV := by decide
@[simp] theorem io_ioRq_ne_ioVl : ioRq ≠ ioVl := by decide
@[simp] theorem io_ioRq_ne_ioX : ioRq ≠ ioX := by decide
@[simp] theorem io_ioRq_ne_lFl : ioRq ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioRq : lFl ≠ ioRq := by decide
@[simp] theorem io_ioRq_ne_lDh : ioRq ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioRq : lDh ≠ ioRq := by decide
@[simp] theorem io_ioRq_ne_lDt : ioRq ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioRq : lDt ≠ ioRq := by decide
@[simp] theorem io_ioRq_ne_lDg : ioRq ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioRq : lDg ≠ ioRq := by decide
@[simp] theorem io_ioRq_ne_lDi : ioRq ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioRq : lDi ≠ ioRq := by decide
@[simp] theorem io_ioRq_ne_lRp : ioRq ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioRq : lRp ≠ ioRq := by decide
@[simp] theorem io_ioRq_ne_lRn : ioRq ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioRq : lRn ≠ ioRq := by decide
@[simp] theorem io_ioRq_ne_lFle : ioRq ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioRq : lFle ≠ ioRq := by decide
@[simp] theorem io_ioRq_ne_lDir : ioRq ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioRq : lDir ≠ ioRq := by decide
@[simp] theorem io_ioRq_ne_lKb : ioRq ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioRq : lKb ≠ ioRq := by decide
@[simp] theorem io_ioRq_ne_kFu : ioRq ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioRq : kFu ≠ ioRq := by decide
@[simp] theorem io_ioRq_ne_kD : ioRq ≠ kD := by decide
@[simp] theorem io_kD_ne_ioRq : kD ≠ ioRq := by decide
@[simp] theorem io_ioRq_ne_iC : ioRq ≠ iC := by decide
@[simp] theorem io_iC_ne_ioRq : iC ≠ ioRq := by decide
@[simp] theorem io_ioRq_ne_iU : ioRq ≠ iU := by decide
@[simp] theorem io_iU_ne_ioRq : iU ≠ ioRq := by decide
@[simp] theorem io_ioRq_ne_iQ : ioRq ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioRq : iQ ≠ ioRq := by decide
@[simp] theorem io_ioRq_ne_iA : ioRq ≠ iA := by decide
@[simp] theorem io_iA_ne_ioRq : iA ≠ ioRq := by decide
@[simp] theorem io_ioRq_ne_iK : ioRq ≠ iK := by decide
@[simp] theorem io_iK_ne_ioRq : iK ≠ ioRq := by decide
@[simp] theorem io_ioMa_ne_ioTy : ioMa ≠ ioTy := by decide
@[simp] theorem io_ioMa_ne_ioPp : ioMa ≠ ioPp := by decide
@[simp] theorem io_ioMa_ne_ioB0 : ioMa ≠ ioB0 := by decide
@[simp] theorem io_ioMa_ne_ioMj : ioMa ≠ ioMj := by decide
@[simp] theorem io_ioMa_ne_ioIk : ioMa ≠ ioIk := by decide
@[simp] theorem io_ioMa_ne_ioRs : ioMa ≠ ioRs := by decide
@[simp] theorem io_ioMa_ne_ioRp : ioMa ≠ ioRp := by decide
@[simp] theorem io_ioMa_ne_ioPm : ioMa ≠ ioPm := by decide
@[simp] theorem io_ioMa_ne_ioMe : ioMa ≠ ioMe := by decide
@[simp] theorem io_ioMa_ne_ioHd : ioMa ≠ ioHd := by decide
@[simp] theorem io_ioMa_ne_ioCj : ioMa ≠ ioCj := by decide
@[simp] theorem io_ioMa_ne_ioUj : ioMa ≠ ioUj := by decide
@[simp] theorem io_ioMa_ne_ioW : ioMa ≠ ioW := by decide
@[simp] theorem io_ioMa_ne_ioQj : ioMa ≠ ioQj := by decide
@[simp] theorem io_ioMa_ne_ioRn : ioMa ≠ ioRn := by decide
@[simp] theorem io_ioMa_ne_ioRl : ioMa ≠ ioRl := by decide
@[simp] theorem io_ioMa_ne_ioRq : ioMa ≠ ioRq := by decide
@[simp] theorem io_ioMa_ne_ioMl : ioMa ≠ ioMl := by decide
@[simp] theorem io_ioMa_ne_ioNp : ioMa ≠ ioNp := by decide
@[simp] theorem io_ioMa_ne_ioNf : ioMa ≠ ioNf := by decide
@[simp] theorem io_ioMa_ne_ioF : ioMa ≠ ioF := by decide
@[simp] theorem io_ioMa_ne_ioLp : ioMa ≠ ioLp := by decide
@[simp] theorem io_ioMa_ne_ioRc : ioMa ≠ ioRc := by decide
@[simp] theorem io_ioMa_ne_ioRh : ioMa ≠ ioRh := by decide
@[simp] theorem io_ioMa_ne_ioBd : ioMa ≠ ioBd := by decide
@[simp] theorem io_ioMa_ne_ioT1 : ioMa ≠ ioT1 := by decide
@[simp] theorem io_ioMa_ne_ioP : ioMa ≠ ioP := by decide
@[simp] theorem io_ioMa_ne_ioT2 : ioMa ≠ ioT2 := by decide
@[simp] theorem io_ioMa_ne_ioQq : ioMa ≠ ioQq := by decide
@[simp] theorem io_ioMa_ne_ioV : ioMa ≠ ioV := by decide
@[simp] theorem io_ioMa_ne_ioVl : ioMa ≠ ioVl := by decide
@[simp] theorem io_ioMa_ne_ioX : ioMa ≠ ioX := by decide
@[simp] theorem io_ioMa_ne_lFl : ioMa ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioMa : lFl ≠ ioMa := by decide
@[simp] theorem io_ioMa_ne_lDh : ioMa ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioMa : lDh ≠ ioMa := by decide
@[simp] theorem io_ioMa_ne_lDt : ioMa ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioMa : lDt ≠ ioMa := by decide
@[simp] theorem io_ioMa_ne_lDg : ioMa ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioMa : lDg ≠ ioMa := by decide
@[simp] theorem io_ioMa_ne_lDi : ioMa ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioMa : lDi ≠ ioMa := by decide
@[simp] theorem io_ioMa_ne_lRp : ioMa ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioMa : lRp ≠ ioMa := by decide
@[simp] theorem io_ioMa_ne_lRn : ioMa ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioMa : lRn ≠ ioMa := by decide
@[simp] theorem io_ioMa_ne_lFle : ioMa ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioMa : lFle ≠ ioMa := by decide
@[simp] theorem io_ioMa_ne_lDir : ioMa ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioMa : lDir ≠ ioMa := by decide
@[simp] theorem io_ioMa_ne_lKb : ioMa ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioMa : lKb ≠ ioMa := by decide
@[simp] theorem io_ioMa_ne_kFu : ioMa ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioMa : kFu ≠ ioMa := by decide
@[simp] theorem io_ioMa_ne_kD : ioMa ≠ kD := by decide
@[simp] theorem io_kD_ne_ioMa : kD ≠ ioMa := by decide
@[simp] theorem io_ioMa_ne_iC : ioMa ≠ iC := by decide
@[simp] theorem io_iC_ne_ioMa : iC ≠ ioMa := by decide
@[simp] theorem io_ioMa_ne_iU : ioMa ≠ iU := by decide
@[simp] theorem io_iU_ne_ioMa : iU ≠ ioMa := by decide
@[simp] theorem io_ioMa_ne_iQ : ioMa ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioMa : iQ ≠ ioMa := by decide
@[simp] theorem io_ioMa_ne_iA : ioMa ≠ iA := by decide
@[simp] theorem io_iA_ne_ioMa : iA ≠ ioMa := by decide
@[simp] theorem io_ioMa_ne_iK : ioMa ≠ iK := by decide
@[simp] theorem io_iK_ne_ioMa : iK ≠ ioMa := by decide
@[simp] theorem io_ioMl_ne_ioTy : ioMl ≠ ioTy := by decide
@[simp] theorem io_ioMl_ne_ioPp : ioMl ≠ ioPp := by decide
@[simp] theorem io_ioMl_ne_ioB0 : ioMl ≠ ioB0 := by decide
@[simp] theorem io_ioMl_ne_ioMj : ioMl ≠ ioMj := by decide
@[simp] theorem io_ioMl_ne_ioIk : ioMl ≠ ioIk := by decide
@[simp] theorem io_ioMl_ne_ioRs : ioMl ≠ ioRs := by decide
@[simp] theorem io_ioMl_ne_ioRp : ioMl ≠ ioRp := by decide
@[simp] theorem io_ioMl_ne_ioPm : ioMl ≠ ioPm := by decide
@[simp] theorem io_ioMl_ne_ioMe : ioMl ≠ ioMe := by decide
@[simp] theorem io_ioMl_ne_ioHd : ioMl ≠ ioHd := by decide
@[simp] theorem io_ioMl_ne_ioCj : ioMl ≠ ioCj := by decide
@[simp] theorem io_ioMl_ne_ioUj : ioMl ≠ ioUj := by decide
@[simp] theorem io_ioMl_ne_ioW : ioMl ≠ ioW := by decide
@[simp] theorem io_ioMl_ne_ioQj : ioMl ≠ ioQj := by decide
@[simp] theorem io_ioMl_ne_ioRn : ioMl ≠ ioRn := by decide
@[simp] theorem io_ioMl_ne_ioRl : ioMl ≠ ioRl := by decide
@[simp] theorem io_ioMl_ne_ioRq : ioMl ≠ ioRq := by decide
@[simp] theorem io_ioMl_ne_ioMa : ioMl ≠ ioMa := by decide
@[simp] theorem io_ioMl_ne_ioNp : ioMl ≠ ioNp := by decide
@[simp] theorem io_ioMl_ne_ioNf : ioMl ≠ ioNf := by decide
@[simp] theorem io_ioMl_ne_ioF : ioMl ≠ ioF := by decide
@[simp] theorem io_ioMl_ne_ioLp : ioMl ≠ ioLp := by decide
@[simp] theorem io_ioMl_ne_ioRc : ioMl ≠ ioRc := by decide
@[simp] theorem io_ioMl_ne_ioRh : ioMl ≠ ioRh := by decide
@[simp] theorem io_ioMl_ne_ioBd : ioMl ≠ ioBd := by decide
@[simp] theorem io_ioMl_ne_ioT1 : ioMl ≠ ioT1 := by decide
@[simp] theorem io_ioMl_ne_ioP : ioMl ≠ ioP := by decide
@[simp] theorem io_ioMl_ne_ioT2 : ioMl ≠ ioT2 := by decide
@[simp] theorem io_ioMl_ne_ioQq : ioMl ≠ ioQq := by decide
@[simp] theorem io_ioMl_ne_ioV : ioMl ≠ ioV := by decide
@[simp] theorem io_ioMl_ne_ioVl : ioMl ≠ ioVl := by decide
@[simp] theorem io_ioMl_ne_ioX : ioMl ≠ ioX := by decide
@[simp] theorem io_ioMl_ne_lFl : ioMl ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioMl : lFl ≠ ioMl := by decide
@[simp] theorem io_ioMl_ne_lDh : ioMl ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioMl : lDh ≠ ioMl := by decide
@[simp] theorem io_ioMl_ne_lDt : ioMl ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioMl : lDt ≠ ioMl := by decide
@[simp] theorem io_ioMl_ne_lDg : ioMl ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioMl : lDg ≠ ioMl := by decide
@[simp] theorem io_ioMl_ne_lDi : ioMl ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioMl : lDi ≠ ioMl := by decide
@[simp] theorem io_ioMl_ne_lRp : ioMl ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioMl : lRp ≠ ioMl := by decide
@[simp] theorem io_ioMl_ne_lRn : ioMl ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioMl : lRn ≠ ioMl := by decide
@[simp] theorem io_ioMl_ne_lFle : ioMl ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioMl : lFle ≠ ioMl := by decide
@[simp] theorem io_ioMl_ne_lDir : ioMl ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioMl : lDir ≠ ioMl := by decide
@[simp] theorem io_ioMl_ne_lKb : ioMl ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioMl : lKb ≠ ioMl := by decide
@[simp] theorem io_ioMl_ne_kFu : ioMl ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioMl : kFu ≠ ioMl := by decide
@[simp] theorem io_ioMl_ne_kD : ioMl ≠ kD := by decide
@[simp] theorem io_kD_ne_ioMl : kD ≠ ioMl := by decide
@[simp] theorem io_ioMl_ne_iC : ioMl ≠ iC := by decide
@[simp] theorem io_iC_ne_ioMl : iC ≠ ioMl := by decide
@[simp] theorem io_ioMl_ne_iU : ioMl ≠ iU := by decide
@[simp] theorem io_iU_ne_ioMl : iU ≠ ioMl := by decide
@[simp] theorem io_ioMl_ne_iQ : ioMl ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioMl : iQ ≠ ioMl := by decide
@[simp] theorem io_ioMl_ne_iA : ioMl ≠ iA := by decide
@[simp] theorem io_iA_ne_ioMl : iA ≠ ioMl := by decide
@[simp] theorem io_ioMl_ne_iK : ioMl ≠ iK := by decide
@[simp] theorem io_iK_ne_ioMl : iK ≠ ioMl := by decide
@[simp] theorem io_ioNp_ne_ioTy : ioNp ≠ ioTy := by decide
@[simp] theorem io_ioNp_ne_ioPp : ioNp ≠ ioPp := by decide
@[simp] theorem io_ioNp_ne_ioB0 : ioNp ≠ ioB0 := by decide
@[simp] theorem io_ioNp_ne_ioMj : ioNp ≠ ioMj := by decide
@[simp] theorem io_ioNp_ne_ioIk : ioNp ≠ ioIk := by decide
@[simp] theorem io_ioNp_ne_ioRs : ioNp ≠ ioRs := by decide
@[simp] theorem io_ioNp_ne_ioRp : ioNp ≠ ioRp := by decide
@[simp] theorem io_ioNp_ne_ioPm : ioNp ≠ ioPm := by decide
@[simp] theorem io_ioNp_ne_ioMe : ioNp ≠ ioMe := by decide
@[simp] theorem io_ioNp_ne_ioHd : ioNp ≠ ioHd := by decide
@[simp] theorem io_ioNp_ne_ioCj : ioNp ≠ ioCj := by decide
@[simp] theorem io_ioNp_ne_ioUj : ioNp ≠ ioUj := by decide
@[simp] theorem io_ioNp_ne_ioW : ioNp ≠ ioW := by decide
@[simp] theorem io_ioNp_ne_ioQj : ioNp ≠ ioQj := by decide
@[simp] theorem io_ioNp_ne_ioRn : ioNp ≠ ioRn := by decide
@[simp] theorem io_ioNp_ne_ioRl : ioNp ≠ ioRl := by decide
@[simp] theorem io_ioNp_ne_ioRq : ioNp ≠ ioRq := by decide
@[simp] theorem io_ioNp_ne_ioMa : ioNp ≠ ioMa := by decide
@[simp] theorem io_ioNp_ne_ioMl : ioNp ≠ ioMl := by decide
@[simp] theorem io_ioNp_ne_ioNf : ioNp ≠ ioNf := by decide
@[simp] theorem io_ioNp_ne_ioF : ioNp ≠ ioF := by decide
@[simp] theorem io_ioNp_ne_ioLp : ioNp ≠ ioLp := by decide
@[simp] theorem io_ioNp_ne_ioRc : ioNp ≠ ioRc := by decide
@[simp] theorem io_ioNp_ne_ioRh : ioNp ≠ ioRh := by decide
@[simp] theorem io_ioNp_ne_ioBd : ioNp ≠ ioBd := by decide
@[simp] theorem io_ioNp_ne_ioT1 : ioNp ≠ ioT1 := by decide
@[simp] theorem io_ioNp_ne_ioP : ioNp ≠ ioP := by decide
@[simp] theorem io_ioNp_ne_ioT2 : ioNp ≠ ioT2 := by decide
@[simp] theorem io_ioNp_ne_ioQq : ioNp ≠ ioQq := by decide
@[simp] theorem io_ioNp_ne_ioV : ioNp ≠ ioV := by decide
@[simp] theorem io_ioNp_ne_ioVl : ioNp ≠ ioVl := by decide
@[simp] theorem io_ioNp_ne_ioX : ioNp ≠ ioX := by decide
@[simp] theorem io_ioNp_ne_lFl : ioNp ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioNp : lFl ≠ ioNp := by decide
@[simp] theorem io_ioNp_ne_lDh : ioNp ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioNp : lDh ≠ ioNp := by decide
@[simp] theorem io_ioNp_ne_lDt : ioNp ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioNp : lDt ≠ ioNp := by decide
@[simp] theorem io_ioNp_ne_lDg : ioNp ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioNp : lDg ≠ ioNp := by decide
@[simp] theorem io_ioNp_ne_lDi : ioNp ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioNp : lDi ≠ ioNp := by decide
@[simp] theorem io_ioNp_ne_lRp : ioNp ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioNp : lRp ≠ ioNp := by decide
@[simp] theorem io_ioNp_ne_lRn : ioNp ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioNp : lRn ≠ ioNp := by decide
@[simp] theorem io_ioNp_ne_lFle : ioNp ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioNp : lFle ≠ ioNp := by decide
@[simp] theorem io_ioNp_ne_lDir : ioNp ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioNp : lDir ≠ ioNp := by decide
@[simp] theorem io_ioNp_ne_lKb : ioNp ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioNp : lKb ≠ ioNp := by decide
@[simp] theorem io_ioNp_ne_kFu : ioNp ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioNp : kFu ≠ ioNp := by decide
@[simp] theorem io_ioNp_ne_kD : ioNp ≠ kD := by decide
@[simp] theorem io_kD_ne_ioNp : kD ≠ ioNp := by decide
@[simp] theorem io_ioNp_ne_iC : ioNp ≠ iC := by decide
@[simp] theorem io_iC_ne_ioNp : iC ≠ ioNp := by decide
@[simp] theorem io_ioNp_ne_iU : ioNp ≠ iU := by decide
@[simp] theorem io_iU_ne_ioNp : iU ≠ ioNp := by decide
@[simp] theorem io_ioNp_ne_iQ : ioNp ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioNp : iQ ≠ ioNp := by decide
@[simp] theorem io_ioNp_ne_iA : ioNp ≠ iA := by decide
@[simp] theorem io_iA_ne_ioNp : iA ≠ ioNp := by decide
@[simp] theorem io_ioNp_ne_iK : ioNp ≠ iK := by decide
@[simp] theorem io_iK_ne_ioNp : iK ≠ ioNp := by decide
@[simp] theorem io_ioNf_ne_ioTy : ioNf ≠ ioTy := by decide
@[simp] theorem io_ioNf_ne_ioPp : ioNf ≠ ioPp := by decide
@[simp] theorem io_ioNf_ne_ioB0 : ioNf ≠ ioB0 := by decide
@[simp] theorem io_ioNf_ne_ioMj : ioNf ≠ ioMj := by decide
@[simp] theorem io_ioNf_ne_ioIk : ioNf ≠ ioIk := by decide
@[simp] theorem io_ioNf_ne_ioRs : ioNf ≠ ioRs := by decide
@[simp] theorem io_ioNf_ne_ioRp : ioNf ≠ ioRp := by decide
@[simp] theorem io_ioNf_ne_ioPm : ioNf ≠ ioPm := by decide
@[simp] theorem io_ioNf_ne_ioMe : ioNf ≠ ioMe := by decide
@[simp] theorem io_ioNf_ne_ioHd : ioNf ≠ ioHd := by decide
@[simp] theorem io_ioNf_ne_ioCj : ioNf ≠ ioCj := by decide
@[simp] theorem io_ioNf_ne_ioUj : ioNf ≠ ioUj := by decide
@[simp] theorem io_ioNf_ne_ioW : ioNf ≠ ioW := by decide
@[simp] theorem io_ioNf_ne_ioQj : ioNf ≠ ioQj := by decide
@[simp] theorem io_ioNf_ne_ioRn : ioNf ≠ ioRn := by decide
@[simp] theorem io_ioNf_ne_ioRl : ioNf ≠ ioRl := by decide
@[simp] theorem io_ioNf_ne_ioRq : ioNf ≠ ioRq := by decide
@[simp] theorem io_ioNf_ne_ioMa : ioNf ≠ ioMa := by decide
@[simp] theorem io_ioNf_ne_ioMl : ioNf ≠ ioMl := by decide
@[simp] theorem io_ioNf_ne_ioNp : ioNf ≠ ioNp := by decide
@[simp] theorem io_ioNf_ne_ioF : ioNf ≠ ioF := by decide
@[simp] theorem io_ioNf_ne_ioLp : ioNf ≠ ioLp := by decide
@[simp] theorem io_ioNf_ne_ioRc : ioNf ≠ ioRc := by decide
@[simp] theorem io_ioNf_ne_ioRh : ioNf ≠ ioRh := by decide
@[simp] theorem io_ioNf_ne_ioBd : ioNf ≠ ioBd := by decide
@[simp] theorem io_ioNf_ne_ioT1 : ioNf ≠ ioT1 := by decide
@[simp] theorem io_ioNf_ne_ioP : ioNf ≠ ioP := by decide
@[simp] theorem io_ioNf_ne_ioT2 : ioNf ≠ ioT2 := by decide
@[simp] theorem io_ioNf_ne_ioQq : ioNf ≠ ioQq := by decide
@[simp] theorem io_ioNf_ne_ioV : ioNf ≠ ioV := by decide
@[simp] theorem io_ioNf_ne_ioVl : ioNf ≠ ioVl := by decide
@[simp] theorem io_ioNf_ne_ioX : ioNf ≠ ioX := by decide
@[simp] theorem io_ioNf_ne_lFl : ioNf ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioNf : lFl ≠ ioNf := by decide
@[simp] theorem io_ioNf_ne_lDh : ioNf ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioNf : lDh ≠ ioNf := by decide
@[simp] theorem io_ioNf_ne_lDt : ioNf ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioNf : lDt ≠ ioNf := by decide
@[simp] theorem io_ioNf_ne_lDg : ioNf ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioNf : lDg ≠ ioNf := by decide
@[simp] theorem io_ioNf_ne_lDi : ioNf ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioNf : lDi ≠ ioNf := by decide
@[simp] theorem io_ioNf_ne_lRp : ioNf ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioNf : lRp ≠ ioNf := by decide
@[simp] theorem io_ioNf_ne_lRn : ioNf ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioNf : lRn ≠ ioNf := by decide
@[simp] theorem io_ioNf_ne_lFle : ioNf ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioNf : lFle ≠ ioNf := by decide
@[simp] theorem io_ioNf_ne_lDir : ioNf ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioNf : lDir ≠ ioNf := by decide
@[simp] theorem io_ioNf_ne_lKb : ioNf ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioNf : lKb ≠ ioNf := by decide
@[simp] theorem io_ioNf_ne_kFu : ioNf ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioNf : kFu ≠ ioNf := by decide
@[simp] theorem io_ioNf_ne_kD : ioNf ≠ kD := by decide
@[simp] theorem io_kD_ne_ioNf : kD ≠ ioNf := by decide
@[simp] theorem io_ioNf_ne_iC : ioNf ≠ iC := by decide
@[simp] theorem io_iC_ne_ioNf : iC ≠ ioNf := by decide
@[simp] theorem io_ioNf_ne_iU : ioNf ≠ iU := by decide
@[simp] theorem io_iU_ne_ioNf : iU ≠ ioNf := by decide
@[simp] theorem io_ioNf_ne_iQ : ioNf ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioNf : iQ ≠ ioNf := by decide
@[simp] theorem io_ioNf_ne_iA : ioNf ≠ iA := by decide
@[simp] theorem io_iA_ne_ioNf : iA ≠ ioNf := by decide
@[simp] theorem io_ioNf_ne_iK : ioNf ≠ iK := by decide
@[simp] theorem io_iK_ne_ioNf : iK ≠ ioNf := by decide
@[simp] theorem io_ioF_ne_ioTy : ioF ≠ ioTy := by decide
@[simp] theorem io_ioF_ne_ioPp : ioF ≠ ioPp := by decide
@[simp] theorem io_ioF_ne_ioB0 : ioF ≠ ioB0 := by decide
@[simp] theorem io_ioF_ne_ioMj : ioF ≠ ioMj := by decide
@[simp] theorem io_ioF_ne_ioIk : ioF ≠ ioIk := by decide
@[simp] theorem io_ioF_ne_ioRs : ioF ≠ ioRs := by decide
@[simp] theorem io_ioF_ne_ioRp : ioF ≠ ioRp := by decide
@[simp] theorem io_ioF_ne_ioPm : ioF ≠ ioPm := by decide
@[simp] theorem io_ioF_ne_ioMe : ioF ≠ ioMe := by decide
@[simp] theorem io_ioF_ne_ioHd : ioF ≠ ioHd := by decide
@[simp] theorem io_ioF_ne_ioCj : ioF ≠ ioCj := by decide
@[simp] theorem io_ioF_ne_ioUj : ioF ≠ ioUj := by decide
@[simp] theorem io_ioF_ne_ioW : ioF ≠ ioW := by decide
@[simp] theorem io_ioF_ne_ioQj : ioF ≠ ioQj := by decide
@[simp] theorem io_ioF_ne_ioRn : ioF ≠ ioRn := by decide
@[simp] theorem io_ioF_ne_ioRl : ioF ≠ ioRl := by decide
@[simp] theorem io_ioF_ne_ioRq : ioF ≠ ioRq := by decide
@[simp] theorem io_ioF_ne_ioMa : ioF ≠ ioMa := by decide
@[simp] theorem io_ioF_ne_ioMl : ioF ≠ ioMl := by decide
@[simp] theorem io_ioF_ne_ioNp : ioF ≠ ioNp := by decide
@[simp] theorem io_ioF_ne_ioNf : ioF ≠ ioNf := by decide
@[simp] theorem io_ioF_ne_ioLp : ioF ≠ ioLp := by decide
@[simp] theorem io_ioF_ne_ioRc : ioF ≠ ioRc := by decide
@[simp] theorem io_ioF_ne_ioRh : ioF ≠ ioRh := by decide
@[simp] theorem io_ioF_ne_ioBd : ioF ≠ ioBd := by decide
@[simp] theorem io_ioF_ne_ioT1 : ioF ≠ ioT1 := by decide
@[simp] theorem io_ioF_ne_ioP : ioF ≠ ioP := by decide
@[simp] theorem io_ioF_ne_ioT2 : ioF ≠ ioT2 := by decide
@[simp] theorem io_ioF_ne_ioQq : ioF ≠ ioQq := by decide
@[simp] theorem io_ioF_ne_ioV : ioF ≠ ioV := by decide
@[simp] theorem io_ioF_ne_ioVl : ioF ≠ ioVl := by decide
@[simp] theorem io_ioF_ne_ioX : ioF ≠ ioX := by decide
@[simp] theorem io_ioF_ne_lFl : ioF ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioF : lFl ≠ ioF := by decide
@[simp] theorem io_ioF_ne_lDh : ioF ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioF : lDh ≠ ioF := by decide
@[simp] theorem io_ioF_ne_lDt : ioF ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioF : lDt ≠ ioF := by decide
@[simp] theorem io_ioF_ne_lDg : ioF ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioF : lDg ≠ ioF := by decide
@[simp] theorem io_ioF_ne_lDi : ioF ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioF : lDi ≠ ioF := by decide
@[simp] theorem io_ioF_ne_lRp : ioF ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioF : lRp ≠ ioF := by decide
@[simp] theorem io_ioF_ne_lRn : ioF ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioF : lRn ≠ ioF := by decide
@[simp] theorem io_ioF_ne_lFle : ioF ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioF : lFle ≠ ioF := by decide
@[simp] theorem io_ioF_ne_lDir : ioF ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioF : lDir ≠ ioF := by decide
@[simp] theorem io_ioF_ne_lKb : ioF ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioF : lKb ≠ ioF := by decide
@[simp] theorem io_ioF_ne_kFu : ioF ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioF : kFu ≠ ioF := by decide
@[simp] theorem io_ioF_ne_kD : ioF ≠ kD := by decide
@[simp] theorem io_kD_ne_ioF : kD ≠ ioF := by decide
@[simp] theorem io_ioF_ne_iC : ioF ≠ iC := by decide
@[simp] theorem io_iC_ne_ioF : iC ≠ ioF := by decide
@[simp] theorem io_ioF_ne_iU : ioF ≠ iU := by decide
@[simp] theorem io_iU_ne_ioF : iU ≠ ioF := by decide
@[simp] theorem io_ioF_ne_iQ : ioF ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioF : iQ ≠ ioF := by decide
@[simp] theorem io_ioF_ne_iA : ioF ≠ iA := by decide
@[simp] theorem io_iA_ne_ioF : iA ≠ ioF := by decide
@[simp] theorem io_ioF_ne_iK : ioF ≠ iK := by decide
@[simp] theorem io_iK_ne_ioF : iK ≠ ioF := by decide
@[simp] theorem io_ioLp_ne_ioTy : ioLp ≠ ioTy := by decide
@[simp] theorem io_ioLp_ne_ioPp : ioLp ≠ ioPp := by decide
@[simp] theorem io_ioLp_ne_ioB0 : ioLp ≠ ioB0 := by decide
@[simp] theorem io_ioLp_ne_ioMj : ioLp ≠ ioMj := by decide
@[simp] theorem io_ioLp_ne_ioIk : ioLp ≠ ioIk := by decide
@[simp] theorem io_ioLp_ne_ioRs : ioLp ≠ ioRs := by decide
@[simp] theorem io_ioLp_ne_ioRp : ioLp ≠ ioRp := by decide
@[simp] theorem io_ioLp_ne_ioPm : ioLp ≠ ioPm := by decide
@[simp] theorem io_ioLp_ne_ioMe : ioLp ≠ ioMe := by decide
@[simp] theorem io_ioLp_ne_ioHd : ioLp ≠ ioHd := by decide
@[simp] theorem io_ioLp_ne_ioCj : ioLp ≠ ioCj := by decide
@[simp] theorem io_ioLp_ne_ioUj : ioLp ≠ ioUj := by decide
@[simp] theorem io_ioLp_ne_ioW : ioLp ≠ ioW := by decide
@[simp] theorem io_ioLp_ne_ioQj : ioLp ≠ ioQj := by decide
@[simp] theorem io_ioLp_ne_ioRn : ioLp ≠ ioRn := by decide
@[simp] theorem io_ioLp_ne_ioRl : ioLp ≠ ioRl := by decide
@[simp] theorem io_ioLp_ne_ioRq : ioLp ≠ ioRq := by decide
@[simp] theorem io_ioLp_ne_ioMa : ioLp ≠ ioMa := by decide
@[simp] theorem io_ioLp_ne_ioMl : ioLp ≠ ioMl := by decide
@[simp] theorem io_ioLp_ne_ioNp : ioLp ≠ ioNp := by decide
@[simp] theorem io_ioLp_ne_ioNf : ioLp ≠ ioNf := by decide
@[simp] theorem io_ioLp_ne_ioF : ioLp ≠ ioF := by decide
@[simp] theorem io_ioLp_ne_ioRc : ioLp ≠ ioRc := by decide
@[simp] theorem io_ioLp_ne_ioRh : ioLp ≠ ioRh := by decide
@[simp] theorem io_ioLp_ne_ioBd : ioLp ≠ ioBd := by decide
@[simp] theorem io_ioLp_ne_ioT1 : ioLp ≠ ioT1 := by decide
@[simp] theorem io_ioLp_ne_ioP : ioLp ≠ ioP := by decide
@[simp] theorem io_ioLp_ne_ioT2 : ioLp ≠ ioT2 := by decide
@[simp] theorem io_ioLp_ne_ioQq : ioLp ≠ ioQq := by decide
@[simp] theorem io_ioLp_ne_ioV : ioLp ≠ ioV := by decide
@[simp] theorem io_ioLp_ne_ioVl : ioLp ≠ ioVl := by decide
@[simp] theorem io_ioLp_ne_ioX : ioLp ≠ ioX := by decide
@[simp] theorem io_ioLp_ne_lFl : ioLp ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioLp : lFl ≠ ioLp := by decide
@[simp] theorem io_ioLp_ne_lDh : ioLp ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioLp : lDh ≠ ioLp := by decide
@[simp] theorem io_ioLp_ne_lDt : ioLp ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioLp : lDt ≠ ioLp := by decide
@[simp] theorem io_ioLp_ne_lDg : ioLp ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioLp : lDg ≠ ioLp := by decide
@[simp] theorem io_ioLp_ne_lDi : ioLp ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioLp : lDi ≠ ioLp := by decide
@[simp] theorem io_ioLp_ne_lRp : ioLp ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioLp : lRp ≠ ioLp := by decide
@[simp] theorem io_ioLp_ne_lRn : ioLp ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioLp : lRn ≠ ioLp := by decide
@[simp] theorem io_ioLp_ne_lFle : ioLp ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioLp : lFle ≠ ioLp := by decide
@[simp] theorem io_ioLp_ne_lDir : ioLp ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioLp : lDir ≠ ioLp := by decide
@[simp] theorem io_ioLp_ne_lKb : ioLp ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioLp : lKb ≠ ioLp := by decide
@[simp] theorem io_ioLp_ne_kFu : ioLp ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioLp : kFu ≠ ioLp := by decide
@[simp] theorem io_ioLp_ne_kD : ioLp ≠ kD := by decide
@[simp] theorem io_kD_ne_ioLp : kD ≠ ioLp := by decide
@[simp] theorem io_ioLp_ne_iC : ioLp ≠ iC := by decide
@[simp] theorem io_iC_ne_ioLp : iC ≠ ioLp := by decide
@[simp] theorem io_ioLp_ne_iU : ioLp ≠ iU := by decide
@[simp] theorem io_iU_ne_ioLp : iU ≠ ioLp := by decide
@[simp] theorem io_ioLp_ne_iQ : ioLp ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioLp : iQ ≠ ioLp := by decide
@[simp] theorem io_ioLp_ne_iA : ioLp ≠ iA := by decide
@[simp] theorem io_iA_ne_ioLp : iA ≠ ioLp := by decide
@[simp] theorem io_ioLp_ne_iK : ioLp ≠ iK := by decide
@[simp] theorem io_iK_ne_ioLp : iK ≠ ioLp := by decide
@[simp] theorem io_ioRc_ne_ioTy : ioRc ≠ ioTy := by decide
@[simp] theorem io_ioRc_ne_ioPp : ioRc ≠ ioPp := by decide
@[simp] theorem io_ioRc_ne_ioB0 : ioRc ≠ ioB0 := by decide
@[simp] theorem io_ioRc_ne_ioMj : ioRc ≠ ioMj := by decide
@[simp] theorem io_ioRc_ne_ioIk : ioRc ≠ ioIk := by decide
@[simp] theorem io_ioRc_ne_ioRs : ioRc ≠ ioRs := by decide
@[simp] theorem io_ioRc_ne_ioRp : ioRc ≠ ioRp := by decide
@[simp] theorem io_ioRc_ne_ioPm : ioRc ≠ ioPm := by decide
@[simp] theorem io_ioRc_ne_ioMe : ioRc ≠ ioMe := by decide
@[simp] theorem io_ioRc_ne_ioHd : ioRc ≠ ioHd := by decide
@[simp] theorem io_ioRc_ne_ioCj : ioRc ≠ ioCj := by decide
@[simp] theorem io_ioRc_ne_ioUj : ioRc ≠ ioUj := by decide
@[simp] theorem io_ioRc_ne_ioW : ioRc ≠ ioW := by decide
@[simp] theorem io_ioRc_ne_ioQj : ioRc ≠ ioQj := by decide
@[simp] theorem io_ioRc_ne_ioRn : ioRc ≠ ioRn := by decide
@[simp] theorem io_ioRc_ne_ioRl : ioRc ≠ ioRl := by decide
@[simp] theorem io_ioRc_ne_ioRq : ioRc ≠ ioRq := by decide
@[simp] theorem io_ioRc_ne_ioMa : ioRc ≠ ioMa := by decide
@[simp] theorem io_ioRc_ne_ioMl : ioRc ≠ ioMl := by decide
@[simp] theorem io_ioRc_ne_ioNp : ioRc ≠ ioNp := by decide
@[simp] theorem io_ioRc_ne_ioNf : ioRc ≠ ioNf := by decide
@[simp] theorem io_ioRc_ne_ioF : ioRc ≠ ioF := by decide
@[simp] theorem io_ioRc_ne_ioLp : ioRc ≠ ioLp := by decide
@[simp] theorem io_ioRc_ne_ioRh : ioRc ≠ ioRh := by decide
@[simp] theorem io_ioRc_ne_ioBd : ioRc ≠ ioBd := by decide
@[simp] theorem io_ioRc_ne_ioT1 : ioRc ≠ ioT1 := by decide
@[simp] theorem io_ioRc_ne_ioP : ioRc ≠ ioP := by decide
@[simp] theorem io_ioRc_ne_ioT2 : ioRc ≠ ioT2 := by decide
@[simp] theorem io_ioRc_ne_ioQq : ioRc ≠ ioQq := by decide
@[simp] theorem io_ioRc_ne_ioV : ioRc ≠ ioV := by decide
@[simp] theorem io_ioRc_ne_ioVl : ioRc ≠ ioVl := by decide
@[simp] theorem io_ioRc_ne_ioX : ioRc ≠ ioX := by decide
@[simp] theorem io_ioRc_ne_lFl : ioRc ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioRc : lFl ≠ ioRc := by decide
@[simp] theorem io_ioRc_ne_lDh : ioRc ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioRc : lDh ≠ ioRc := by decide
@[simp] theorem io_ioRc_ne_lDt : ioRc ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioRc : lDt ≠ ioRc := by decide
@[simp] theorem io_ioRc_ne_lDg : ioRc ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioRc : lDg ≠ ioRc := by decide
@[simp] theorem io_ioRc_ne_lDi : ioRc ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioRc : lDi ≠ ioRc := by decide
@[simp] theorem io_ioRc_ne_lRp : ioRc ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioRc : lRp ≠ ioRc := by decide
@[simp] theorem io_ioRc_ne_lRn : ioRc ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioRc : lRn ≠ ioRc := by decide
@[simp] theorem io_ioRc_ne_lFle : ioRc ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioRc : lFle ≠ ioRc := by decide
@[simp] theorem io_ioRc_ne_lDir : ioRc ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioRc : lDir ≠ ioRc := by decide
@[simp] theorem io_ioRc_ne_lKb : ioRc ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioRc : lKb ≠ ioRc := by decide
@[simp] theorem io_ioRc_ne_kFu : ioRc ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioRc : kFu ≠ ioRc := by decide
@[simp] theorem io_ioRc_ne_kD : ioRc ≠ kD := by decide
@[simp] theorem io_kD_ne_ioRc : kD ≠ ioRc := by decide
@[simp] theorem io_ioRc_ne_iC : ioRc ≠ iC := by decide
@[simp] theorem io_iC_ne_ioRc : iC ≠ ioRc := by decide
@[simp] theorem io_ioRc_ne_iU : ioRc ≠ iU := by decide
@[simp] theorem io_iU_ne_ioRc : iU ≠ ioRc := by decide
@[simp] theorem io_ioRc_ne_iQ : ioRc ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioRc : iQ ≠ ioRc := by decide
@[simp] theorem io_ioRc_ne_iA : ioRc ≠ iA := by decide
@[simp] theorem io_iA_ne_ioRc : iA ≠ ioRc := by decide
@[simp] theorem io_ioRc_ne_iK : ioRc ≠ iK := by decide
@[simp] theorem io_iK_ne_ioRc : iK ≠ ioRc := by decide
@[simp] theorem io_ioRh_ne_ioTy : ioRh ≠ ioTy := by decide
@[simp] theorem io_ioRh_ne_ioPp : ioRh ≠ ioPp := by decide
@[simp] theorem io_ioRh_ne_ioB0 : ioRh ≠ ioB0 := by decide
@[simp] theorem io_ioRh_ne_ioMj : ioRh ≠ ioMj := by decide
@[simp] theorem io_ioRh_ne_ioIk : ioRh ≠ ioIk := by decide
@[simp] theorem io_ioRh_ne_ioRs : ioRh ≠ ioRs := by decide
@[simp] theorem io_ioRh_ne_ioRp : ioRh ≠ ioRp := by decide
@[simp] theorem io_ioRh_ne_ioPm : ioRh ≠ ioPm := by decide
@[simp] theorem io_ioRh_ne_ioMe : ioRh ≠ ioMe := by decide
@[simp] theorem io_ioRh_ne_ioHd : ioRh ≠ ioHd := by decide
@[simp] theorem io_ioRh_ne_ioCj : ioRh ≠ ioCj := by decide
@[simp] theorem io_ioRh_ne_ioUj : ioRh ≠ ioUj := by decide
@[simp] theorem io_ioRh_ne_ioW : ioRh ≠ ioW := by decide
@[simp] theorem io_ioRh_ne_ioQj : ioRh ≠ ioQj := by decide
@[simp] theorem io_ioRh_ne_ioRn : ioRh ≠ ioRn := by decide
@[simp] theorem io_ioRh_ne_ioRl : ioRh ≠ ioRl := by decide
@[simp] theorem io_ioRh_ne_ioRq : ioRh ≠ ioRq := by decide
@[simp] theorem io_ioRh_ne_ioMa : ioRh ≠ ioMa := by decide
@[simp] theorem io_ioRh_ne_ioMl : ioRh ≠ ioMl := by decide
@[simp] theorem io_ioRh_ne_ioNp : ioRh ≠ ioNp := by decide
@[simp] theorem io_ioRh_ne_ioNf : ioRh ≠ ioNf := by decide
@[simp] theorem io_ioRh_ne_ioF : ioRh ≠ ioF := by decide
@[simp] theorem io_ioRh_ne_ioLp : ioRh ≠ ioLp := by decide
@[simp] theorem io_ioRh_ne_ioRc : ioRh ≠ ioRc := by decide
@[simp] theorem io_ioRh_ne_ioBd : ioRh ≠ ioBd := by decide
@[simp] theorem io_ioRh_ne_ioT1 : ioRh ≠ ioT1 := by decide
@[simp] theorem io_ioRh_ne_ioP : ioRh ≠ ioP := by decide
@[simp] theorem io_ioRh_ne_ioT2 : ioRh ≠ ioT2 := by decide
@[simp] theorem io_ioRh_ne_ioQq : ioRh ≠ ioQq := by decide
@[simp] theorem io_ioRh_ne_ioV : ioRh ≠ ioV := by decide
@[simp] theorem io_ioRh_ne_ioVl : ioRh ≠ ioVl := by decide
@[simp] theorem io_ioRh_ne_ioX : ioRh ≠ ioX := by decide
@[simp] theorem io_ioRh_ne_lFl : ioRh ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioRh : lFl ≠ ioRh := by decide
@[simp] theorem io_ioRh_ne_lDh : ioRh ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioRh : lDh ≠ ioRh := by decide
@[simp] theorem io_ioRh_ne_lDt : ioRh ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioRh : lDt ≠ ioRh := by decide
@[simp] theorem io_ioRh_ne_lDg : ioRh ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioRh : lDg ≠ ioRh := by decide
@[simp] theorem io_ioRh_ne_lDi : ioRh ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioRh : lDi ≠ ioRh := by decide
@[simp] theorem io_ioRh_ne_lRp : ioRh ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioRh : lRp ≠ ioRh := by decide
@[simp] theorem io_ioRh_ne_lRn : ioRh ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioRh : lRn ≠ ioRh := by decide
@[simp] theorem io_ioRh_ne_lFle : ioRh ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioRh : lFle ≠ ioRh := by decide
@[simp] theorem io_ioRh_ne_lDir : ioRh ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioRh : lDir ≠ ioRh := by decide
@[simp] theorem io_ioRh_ne_lKb : ioRh ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioRh : lKb ≠ ioRh := by decide
@[simp] theorem io_ioRh_ne_kFu : ioRh ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioRh : kFu ≠ ioRh := by decide
@[simp] theorem io_ioRh_ne_kD : ioRh ≠ kD := by decide
@[simp] theorem io_kD_ne_ioRh : kD ≠ ioRh := by decide
@[simp] theorem io_ioRh_ne_iC : ioRh ≠ iC := by decide
@[simp] theorem io_iC_ne_ioRh : iC ≠ ioRh := by decide
@[simp] theorem io_ioRh_ne_iU : ioRh ≠ iU := by decide
@[simp] theorem io_iU_ne_ioRh : iU ≠ ioRh := by decide
@[simp] theorem io_ioRh_ne_iQ : ioRh ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioRh : iQ ≠ ioRh := by decide
@[simp] theorem io_ioRh_ne_iA : ioRh ≠ iA := by decide
@[simp] theorem io_iA_ne_ioRh : iA ≠ ioRh := by decide
@[simp] theorem io_ioRh_ne_iK : ioRh ≠ iK := by decide
@[simp] theorem io_iK_ne_ioRh : iK ≠ ioRh := by decide
@[simp] theorem io_ioBd_ne_ioTy : ioBd ≠ ioTy := by decide
@[simp] theorem io_ioBd_ne_ioPp : ioBd ≠ ioPp := by decide
@[simp] theorem io_ioBd_ne_ioB0 : ioBd ≠ ioB0 := by decide
@[simp] theorem io_ioBd_ne_ioMj : ioBd ≠ ioMj := by decide
@[simp] theorem io_ioBd_ne_ioIk : ioBd ≠ ioIk := by decide
@[simp] theorem io_ioBd_ne_ioRs : ioBd ≠ ioRs := by decide
@[simp] theorem io_ioBd_ne_ioRp : ioBd ≠ ioRp := by decide
@[simp] theorem io_ioBd_ne_ioPm : ioBd ≠ ioPm := by decide
@[simp] theorem io_ioBd_ne_ioMe : ioBd ≠ ioMe := by decide
@[simp] theorem io_ioBd_ne_ioHd : ioBd ≠ ioHd := by decide
@[simp] theorem io_ioBd_ne_ioCj : ioBd ≠ ioCj := by decide
@[simp] theorem io_ioBd_ne_ioUj : ioBd ≠ ioUj := by decide
@[simp] theorem io_ioBd_ne_ioW : ioBd ≠ ioW := by decide
@[simp] theorem io_ioBd_ne_ioQj : ioBd ≠ ioQj := by decide
@[simp] theorem io_ioBd_ne_ioRn : ioBd ≠ ioRn := by decide
@[simp] theorem io_ioBd_ne_ioRl : ioBd ≠ ioRl := by decide
@[simp] theorem io_ioBd_ne_ioRq : ioBd ≠ ioRq := by decide
@[simp] theorem io_ioBd_ne_ioMa : ioBd ≠ ioMa := by decide
@[simp] theorem io_ioBd_ne_ioMl : ioBd ≠ ioMl := by decide
@[simp] theorem io_ioBd_ne_ioNp : ioBd ≠ ioNp := by decide
@[simp] theorem io_ioBd_ne_ioNf : ioBd ≠ ioNf := by decide
@[simp] theorem io_ioBd_ne_ioF : ioBd ≠ ioF := by decide
@[simp] theorem io_ioBd_ne_ioLp : ioBd ≠ ioLp := by decide
@[simp] theorem io_ioBd_ne_ioRc : ioBd ≠ ioRc := by decide
@[simp] theorem io_ioBd_ne_ioRh : ioBd ≠ ioRh := by decide
@[simp] theorem io_ioBd_ne_ioT1 : ioBd ≠ ioT1 := by decide
@[simp] theorem io_ioBd_ne_ioP : ioBd ≠ ioP := by decide
@[simp] theorem io_ioBd_ne_ioT2 : ioBd ≠ ioT2 := by decide
@[simp] theorem io_ioBd_ne_ioQq : ioBd ≠ ioQq := by decide
@[simp] theorem io_ioBd_ne_ioV : ioBd ≠ ioV := by decide
@[simp] theorem io_ioBd_ne_ioVl : ioBd ≠ ioVl := by decide
@[simp] theorem io_ioBd_ne_ioX : ioBd ≠ ioX := by decide
@[simp] theorem io_ioBd_ne_lFl : ioBd ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioBd : lFl ≠ ioBd := by decide
@[simp] theorem io_ioBd_ne_lDh : ioBd ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioBd : lDh ≠ ioBd := by decide
@[simp] theorem io_ioBd_ne_lDt : ioBd ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioBd : lDt ≠ ioBd := by decide
@[simp] theorem io_ioBd_ne_lDg : ioBd ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioBd : lDg ≠ ioBd := by decide
@[simp] theorem io_ioBd_ne_lDi : ioBd ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioBd : lDi ≠ ioBd := by decide
@[simp] theorem io_ioBd_ne_lRp : ioBd ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioBd : lRp ≠ ioBd := by decide
@[simp] theorem io_ioBd_ne_lRn : ioBd ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioBd : lRn ≠ ioBd := by decide
@[simp] theorem io_ioBd_ne_lFle : ioBd ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioBd : lFle ≠ ioBd := by decide
@[simp] theorem io_ioBd_ne_lDir : ioBd ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioBd : lDir ≠ ioBd := by decide
@[simp] theorem io_ioBd_ne_lKb : ioBd ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioBd : lKb ≠ ioBd := by decide
@[simp] theorem io_ioBd_ne_kFu : ioBd ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioBd : kFu ≠ ioBd := by decide
@[simp] theorem io_ioBd_ne_kD : ioBd ≠ kD := by decide
@[simp] theorem io_kD_ne_ioBd : kD ≠ ioBd := by decide
@[simp] theorem io_ioBd_ne_iC : ioBd ≠ iC := by decide
@[simp] theorem io_iC_ne_ioBd : iC ≠ ioBd := by decide
@[simp] theorem io_ioBd_ne_iU : ioBd ≠ iU := by decide
@[simp] theorem io_iU_ne_ioBd : iU ≠ ioBd := by decide
@[simp] theorem io_ioBd_ne_iQ : ioBd ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioBd : iQ ≠ ioBd := by decide
@[simp] theorem io_ioBd_ne_iA : ioBd ≠ iA := by decide
@[simp] theorem io_iA_ne_ioBd : iA ≠ ioBd := by decide
@[simp] theorem io_ioBd_ne_iK : ioBd ≠ iK := by decide
@[simp] theorem io_iK_ne_ioBd : iK ≠ ioBd := by decide
@[simp] theorem io_ioT1_ne_ioTy : ioT1 ≠ ioTy := by decide
@[simp] theorem io_ioT1_ne_ioPp : ioT1 ≠ ioPp := by decide
@[simp] theorem io_ioT1_ne_ioB0 : ioT1 ≠ ioB0 := by decide
@[simp] theorem io_ioT1_ne_ioMj : ioT1 ≠ ioMj := by decide
@[simp] theorem io_ioT1_ne_ioIk : ioT1 ≠ ioIk := by decide
@[simp] theorem io_ioT1_ne_ioRs : ioT1 ≠ ioRs := by decide
@[simp] theorem io_ioT1_ne_ioRp : ioT1 ≠ ioRp := by decide
@[simp] theorem io_ioT1_ne_ioPm : ioT1 ≠ ioPm := by decide
@[simp] theorem io_ioT1_ne_ioMe : ioT1 ≠ ioMe := by decide
@[simp] theorem io_ioT1_ne_ioHd : ioT1 ≠ ioHd := by decide
@[simp] theorem io_ioT1_ne_ioCj : ioT1 ≠ ioCj := by decide
@[simp] theorem io_ioT1_ne_ioUj : ioT1 ≠ ioUj := by decide
@[simp] theorem io_ioT1_ne_ioW : ioT1 ≠ ioW := by decide
@[simp] theorem io_ioT1_ne_ioQj : ioT1 ≠ ioQj := by decide
@[simp] theorem io_ioT1_ne_ioRn : ioT1 ≠ ioRn := by decide
@[simp] theorem io_ioT1_ne_ioRl : ioT1 ≠ ioRl := by decide
@[simp] theorem io_ioT1_ne_ioRq : ioT1 ≠ ioRq := by decide
@[simp] theorem io_ioT1_ne_ioMa : ioT1 ≠ ioMa := by decide
@[simp] theorem io_ioT1_ne_ioMl : ioT1 ≠ ioMl := by decide
@[simp] theorem io_ioT1_ne_ioNp : ioT1 ≠ ioNp := by decide
@[simp] theorem io_ioT1_ne_ioNf : ioT1 ≠ ioNf := by decide
@[simp] theorem io_ioT1_ne_ioF : ioT1 ≠ ioF := by decide
@[simp] theorem io_ioT1_ne_ioLp : ioT1 ≠ ioLp := by decide
@[simp] theorem io_ioT1_ne_ioRc : ioT1 ≠ ioRc := by decide
@[simp] theorem io_ioT1_ne_ioRh : ioT1 ≠ ioRh := by decide
@[simp] theorem io_ioT1_ne_ioBd : ioT1 ≠ ioBd := by decide
@[simp] theorem io_ioT1_ne_ioP : ioT1 ≠ ioP := by decide
@[simp] theorem io_ioT1_ne_ioT2 : ioT1 ≠ ioT2 := by decide
@[simp] theorem io_ioT1_ne_ioQq : ioT1 ≠ ioQq := by decide
@[simp] theorem io_ioT1_ne_ioV : ioT1 ≠ ioV := by decide
@[simp] theorem io_ioT1_ne_ioVl : ioT1 ≠ ioVl := by decide
@[simp] theorem io_ioT1_ne_ioX : ioT1 ≠ ioX := by decide
@[simp] theorem io_ioT1_ne_lFl : ioT1 ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioT1 : lFl ≠ ioT1 := by decide
@[simp] theorem io_ioT1_ne_lDh : ioT1 ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioT1 : lDh ≠ ioT1 := by decide
@[simp] theorem io_ioT1_ne_lDt : ioT1 ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioT1 : lDt ≠ ioT1 := by decide
@[simp] theorem io_ioT1_ne_lDg : ioT1 ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioT1 : lDg ≠ ioT1 := by decide
@[simp] theorem io_ioT1_ne_lDi : ioT1 ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioT1 : lDi ≠ ioT1 := by decide
@[simp] theorem io_ioT1_ne_lRp : ioT1 ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioT1 : lRp ≠ ioT1 := by decide
@[simp] theorem io_ioT1_ne_lRn : ioT1 ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioT1 : lRn ≠ ioT1 := by decide
@[simp] theorem io_ioT1_ne_lFle : ioT1 ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioT1 : lFle ≠ ioT1 := by decide
@[simp] theorem io_ioT1_ne_lDir : ioT1 ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioT1 : lDir ≠ ioT1 := by decide
@[simp] theorem io_ioT1_ne_lKb : ioT1 ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioT1 : lKb ≠ ioT1 := by decide
@[simp] theorem io_ioT1_ne_kFu : ioT1 ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioT1 : kFu ≠ ioT1 := by decide
@[simp] theorem io_ioT1_ne_kD : ioT1 ≠ kD := by decide
@[simp] theorem io_kD_ne_ioT1 : kD ≠ ioT1 := by decide
@[simp] theorem io_ioT1_ne_iC : ioT1 ≠ iC := by decide
@[simp] theorem io_iC_ne_ioT1 : iC ≠ ioT1 := by decide
@[simp] theorem io_ioT1_ne_iU : ioT1 ≠ iU := by decide
@[simp] theorem io_iU_ne_ioT1 : iU ≠ ioT1 := by decide
@[simp] theorem io_ioT1_ne_iQ : ioT1 ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioT1 : iQ ≠ ioT1 := by decide
@[simp] theorem io_ioT1_ne_iA : ioT1 ≠ iA := by decide
@[simp] theorem io_iA_ne_ioT1 : iA ≠ ioT1 := by decide
@[simp] theorem io_ioT1_ne_iK : ioT1 ≠ iK := by decide
@[simp] theorem io_iK_ne_ioT1 : iK ≠ ioT1 := by decide
@[simp] theorem io_ioP_ne_ioTy : ioP ≠ ioTy := by decide
@[simp] theorem io_ioP_ne_ioPp : ioP ≠ ioPp := by decide
@[simp] theorem io_ioP_ne_ioB0 : ioP ≠ ioB0 := by decide
@[simp] theorem io_ioP_ne_ioMj : ioP ≠ ioMj := by decide
@[simp] theorem io_ioP_ne_ioIk : ioP ≠ ioIk := by decide
@[simp] theorem io_ioP_ne_ioRs : ioP ≠ ioRs := by decide
@[simp] theorem io_ioP_ne_ioRp : ioP ≠ ioRp := by decide
@[simp] theorem io_ioP_ne_ioPm : ioP ≠ ioPm := by decide
@[simp] theorem io_ioP_ne_ioMe : ioP ≠ ioMe := by decide
@[simp] theorem io_ioP_ne_ioHd : ioP ≠ ioHd := by decide
@[simp] theorem io_ioP_ne_ioCj : ioP ≠ ioCj := by decide
@[simp] theorem io_ioP_ne_ioUj : ioP ≠ ioUj := by decide
@[simp] theorem io_ioP_ne_ioW : ioP ≠ ioW := by decide
@[simp] theorem io_ioP_ne_ioQj : ioP ≠ ioQj := by decide
@[simp] theorem io_ioP_ne_ioRn : ioP ≠ ioRn := by decide
@[simp] theorem io_ioP_ne_ioRl : ioP ≠ ioRl := by decide
@[simp] theorem io_ioP_ne_ioRq : ioP ≠ ioRq := by decide
@[simp] theorem io_ioP_ne_ioMa : ioP ≠ ioMa := by decide
@[simp] theorem io_ioP_ne_ioMl : ioP ≠ ioMl := by decide
@[simp] theorem io_ioP_ne_ioNp : ioP ≠ ioNp := by decide
@[simp] theorem io_ioP_ne_ioNf : ioP ≠ ioNf := by decide
@[simp] theorem io_ioP_ne_ioF : ioP ≠ ioF := by decide
@[simp] theorem io_ioP_ne_ioLp : ioP ≠ ioLp := by decide
@[simp] theorem io_ioP_ne_ioRc : ioP ≠ ioRc := by decide
@[simp] theorem io_ioP_ne_ioRh : ioP ≠ ioRh := by decide
@[simp] theorem io_ioP_ne_ioBd : ioP ≠ ioBd := by decide
@[simp] theorem io_ioP_ne_ioT1 : ioP ≠ ioT1 := by decide
@[simp] theorem io_ioP_ne_ioT2 : ioP ≠ ioT2 := by decide
@[simp] theorem io_ioP_ne_ioQq : ioP ≠ ioQq := by decide
@[simp] theorem io_ioP_ne_ioV : ioP ≠ ioV := by decide
@[simp] theorem io_ioP_ne_ioVl : ioP ≠ ioVl := by decide
@[simp] theorem io_ioP_ne_ioX : ioP ≠ ioX := by decide
@[simp] theorem io_ioP_ne_lFl : ioP ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioP : lFl ≠ ioP := by decide
@[simp] theorem io_ioP_ne_lDh : ioP ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioP : lDh ≠ ioP := by decide
@[simp] theorem io_ioP_ne_lDt : ioP ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioP : lDt ≠ ioP := by decide
@[simp] theorem io_ioP_ne_lDg : ioP ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioP : lDg ≠ ioP := by decide
@[simp] theorem io_ioP_ne_lDi : ioP ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioP : lDi ≠ ioP := by decide
@[simp] theorem io_ioP_ne_lRp : ioP ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioP : lRp ≠ ioP := by decide
@[simp] theorem io_ioP_ne_lRn : ioP ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioP : lRn ≠ ioP := by decide
@[simp] theorem io_ioP_ne_lFle : ioP ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioP : lFle ≠ ioP := by decide
@[simp] theorem io_ioP_ne_lDir : ioP ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioP : lDir ≠ ioP := by decide
@[simp] theorem io_ioP_ne_lKb : ioP ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioP : lKb ≠ ioP := by decide
@[simp] theorem io_ioP_ne_kFu : ioP ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioP : kFu ≠ ioP := by decide
@[simp] theorem io_ioP_ne_kD : ioP ≠ kD := by decide
@[simp] theorem io_kD_ne_ioP : kD ≠ ioP := by decide
@[simp] theorem io_ioP_ne_iC : ioP ≠ iC := by decide
@[simp] theorem io_iC_ne_ioP : iC ≠ ioP := by decide
@[simp] theorem io_ioP_ne_iU : ioP ≠ iU := by decide
@[simp] theorem io_iU_ne_ioP : iU ≠ ioP := by decide
@[simp] theorem io_ioP_ne_iQ : ioP ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioP : iQ ≠ ioP := by decide
@[simp] theorem io_ioP_ne_iA : ioP ≠ iA := by decide
@[simp] theorem io_iA_ne_ioP : iA ≠ ioP := by decide
@[simp] theorem io_ioP_ne_iK : ioP ≠ iK := by decide
@[simp] theorem io_iK_ne_ioP : iK ≠ ioP := by decide
@[simp] theorem io_ioT2_ne_ioTy : ioT2 ≠ ioTy := by decide
@[simp] theorem io_ioT2_ne_ioPp : ioT2 ≠ ioPp := by decide
@[simp] theorem io_ioT2_ne_ioB0 : ioT2 ≠ ioB0 := by decide
@[simp] theorem io_ioT2_ne_ioMj : ioT2 ≠ ioMj := by decide
@[simp] theorem io_ioT2_ne_ioIk : ioT2 ≠ ioIk := by decide
@[simp] theorem io_ioT2_ne_ioRs : ioT2 ≠ ioRs := by decide
@[simp] theorem io_ioT2_ne_ioRp : ioT2 ≠ ioRp := by decide
@[simp] theorem io_ioT2_ne_ioPm : ioT2 ≠ ioPm := by decide
@[simp] theorem io_ioT2_ne_ioMe : ioT2 ≠ ioMe := by decide
@[simp] theorem io_ioT2_ne_ioHd : ioT2 ≠ ioHd := by decide
@[simp] theorem io_ioT2_ne_ioCj : ioT2 ≠ ioCj := by decide
@[simp] theorem io_ioT2_ne_ioUj : ioT2 ≠ ioUj := by decide
@[simp] theorem io_ioT2_ne_ioW : ioT2 ≠ ioW := by decide
@[simp] theorem io_ioT2_ne_ioQj : ioT2 ≠ ioQj := by decide
@[simp] theorem io_ioT2_ne_ioRn : ioT2 ≠ ioRn := by decide
@[simp] theorem io_ioT2_ne_ioRl : ioT2 ≠ ioRl := by decide
@[simp] theorem io_ioT2_ne_ioRq : ioT2 ≠ ioRq := by decide
@[simp] theorem io_ioT2_ne_ioMa : ioT2 ≠ ioMa := by decide
@[simp] theorem io_ioT2_ne_ioMl : ioT2 ≠ ioMl := by decide
@[simp] theorem io_ioT2_ne_ioNp : ioT2 ≠ ioNp := by decide
@[simp] theorem io_ioT2_ne_ioNf : ioT2 ≠ ioNf := by decide
@[simp] theorem io_ioT2_ne_ioF : ioT2 ≠ ioF := by decide
@[simp] theorem io_ioT2_ne_ioLp : ioT2 ≠ ioLp := by decide
@[simp] theorem io_ioT2_ne_ioRc : ioT2 ≠ ioRc := by decide
@[simp] theorem io_ioT2_ne_ioRh : ioT2 ≠ ioRh := by decide
@[simp] theorem io_ioT2_ne_ioBd : ioT2 ≠ ioBd := by decide
@[simp] theorem io_ioT2_ne_ioT1 : ioT2 ≠ ioT1 := by decide
@[simp] theorem io_ioT2_ne_ioP : ioT2 ≠ ioP := by decide
@[simp] theorem io_ioT2_ne_ioQq : ioT2 ≠ ioQq := by decide
@[simp] theorem io_ioT2_ne_ioV : ioT2 ≠ ioV := by decide
@[simp] theorem io_ioT2_ne_ioVl : ioT2 ≠ ioVl := by decide
@[simp] theorem io_ioT2_ne_ioX : ioT2 ≠ ioX := by decide
@[simp] theorem io_ioT2_ne_lFl : ioT2 ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioT2 : lFl ≠ ioT2 := by decide
@[simp] theorem io_ioT2_ne_lDh : ioT2 ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioT2 : lDh ≠ ioT2 := by decide
@[simp] theorem io_ioT2_ne_lDt : ioT2 ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioT2 : lDt ≠ ioT2 := by decide
@[simp] theorem io_ioT2_ne_lDg : ioT2 ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioT2 : lDg ≠ ioT2 := by decide
@[simp] theorem io_ioT2_ne_lDi : ioT2 ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioT2 : lDi ≠ ioT2 := by decide
@[simp] theorem io_ioT2_ne_lRp : ioT2 ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioT2 : lRp ≠ ioT2 := by decide
@[simp] theorem io_ioT2_ne_lRn : ioT2 ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioT2 : lRn ≠ ioT2 := by decide
@[simp] theorem io_ioT2_ne_lFle : ioT2 ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioT2 : lFle ≠ ioT2 := by decide
@[simp] theorem io_ioT2_ne_lDir : ioT2 ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioT2 : lDir ≠ ioT2 := by decide
@[simp] theorem io_ioT2_ne_lKb : ioT2 ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioT2 : lKb ≠ ioT2 := by decide
@[simp] theorem io_ioT2_ne_kFu : ioT2 ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioT2 : kFu ≠ ioT2 := by decide
@[simp] theorem io_ioT2_ne_kD : ioT2 ≠ kD := by decide
@[simp] theorem io_kD_ne_ioT2 : kD ≠ ioT2 := by decide
@[simp] theorem io_ioT2_ne_iC : ioT2 ≠ iC := by decide
@[simp] theorem io_iC_ne_ioT2 : iC ≠ ioT2 := by decide
@[simp] theorem io_ioT2_ne_iU : ioT2 ≠ iU := by decide
@[simp] theorem io_iU_ne_ioT2 : iU ≠ ioT2 := by decide
@[simp] theorem io_ioT2_ne_iQ : ioT2 ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioT2 : iQ ≠ ioT2 := by decide
@[simp] theorem io_ioT2_ne_iA : ioT2 ≠ iA := by decide
@[simp] theorem io_iA_ne_ioT2 : iA ≠ ioT2 := by decide
@[simp] theorem io_ioT2_ne_iK : ioT2 ≠ iK := by decide
@[simp] theorem io_iK_ne_ioT2 : iK ≠ ioT2 := by decide
@[simp] theorem io_ioQq_ne_ioTy : ioQq ≠ ioTy := by decide
@[simp] theorem io_ioQq_ne_ioPp : ioQq ≠ ioPp := by decide
@[simp] theorem io_ioQq_ne_ioB0 : ioQq ≠ ioB0 := by decide
@[simp] theorem io_ioQq_ne_ioMj : ioQq ≠ ioMj := by decide
@[simp] theorem io_ioQq_ne_ioIk : ioQq ≠ ioIk := by decide
@[simp] theorem io_ioQq_ne_ioRs : ioQq ≠ ioRs := by decide
@[simp] theorem io_ioQq_ne_ioRp : ioQq ≠ ioRp := by decide
@[simp] theorem io_ioQq_ne_ioPm : ioQq ≠ ioPm := by decide
@[simp] theorem io_ioQq_ne_ioMe : ioQq ≠ ioMe := by decide
@[simp] theorem io_ioQq_ne_ioHd : ioQq ≠ ioHd := by decide
@[simp] theorem io_ioQq_ne_ioCj : ioQq ≠ ioCj := by decide
@[simp] theorem io_ioQq_ne_ioUj : ioQq ≠ ioUj := by decide
@[simp] theorem io_ioQq_ne_ioW : ioQq ≠ ioW := by decide
@[simp] theorem io_ioQq_ne_ioQj : ioQq ≠ ioQj := by decide
@[simp] theorem io_ioQq_ne_ioRn : ioQq ≠ ioRn := by decide
@[simp] theorem io_ioQq_ne_ioRl : ioQq ≠ ioRl := by decide
@[simp] theorem io_ioQq_ne_ioRq : ioQq ≠ ioRq := by decide
@[simp] theorem io_ioQq_ne_ioMa : ioQq ≠ ioMa := by decide
@[simp] theorem io_ioQq_ne_ioMl : ioQq ≠ ioMl := by decide
@[simp] theorem io_ioQq_ne_ioNp : ioQq ≠ ioNp := by decide
@[simp] theorem io_ioQq_ne_ioNf : ioQq ≠ ioNf := by decide
@[simp] theorem io_ioQq_ne_ioF : ioQq ≠ ioF := by decide
@[simp] theorem io_ioQq_ne_ioLp : ioQq ≠ ioLp := by decide
@[simp] theorem io_ioQq_ne_ioRc : ioQq ≠ ioRc := by decide
@[simp] theorem io_ioQq_ne_ioRh : ioQq ≠ ioRh := by decide
@[simp] theorem io_ioQq_ne_ioBd : ioQq ≠ ioBd := by decide
@[simp] theorem io_ioQq_ne_ioT1 : ioQq ≠ ioT1 := by decide
@[simp] theorem io_ioQq_ne_ioP : ioQq ≠ ioP := by decide
@[simp] theorem io_ioQq_ne_ioT2 : ioQq ≠ ioT2 := by decide
@[simp] theorem io_ioQq_ne_ioV : ioQq ≠ ioV := by decide
@[simp] theorem io_ioQq_ne_ioVl : ioQq ≠ ioVl := by decide
@[simp] theorem io_ioQq_ne_ioX : ioQq ≠ ioX := by decide
@[simp] theorem io_ioQq_ne_lFl : ioQq ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioQq : lFl ≠ ioQq := by decide
@[simp] theorem io_ioQq_ne_lDh : ioQq ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioQq : lDh ≠ ioQq := by decide
@[simp] theorem io_ioQq_ne_lDt : ioQq ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioQq : lDt ≠ ioQq := by decide
@[simp] theorem io_ioQq_ne_lDg : ioQq ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioQq : lDg ≠ ioQq := by decide
@[simp] theorem io_ioQq_ne_lDi : ioQq ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioQq : lDi ≠ ioQq := by decide
@[simp] theorem io_ioQq_ne_lRp : ioQq ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioQq : lRp ≠ ioQq := by decide
@[simp] theorem io_ioQq_ne_lRn : ioQq ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioQq : lRn ≠ ioQq := by decide
@[simp] theorem io_ioQq_ne_lFle : ioQq ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioQq : lFle ≠ ioQq := by decide
@[simp] theorem io_ioQq_ne_lDir : ioQq ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioQq : lDir ≠ ioQq := by decide
@[simp] theorem io_ioQq_ne_lKb : ioQq ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioQq : lKb ≠ ioQq := by decide
@[simp] theorem io_ioQq_ne_kFu : ioQq ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioQq : kFu ≠ ioQq := by decide
@[simp] theorem io_ioQq_ne_kD : ioQq ≠ kD := by decide
@[simp] theorem io_kD_ne_ioQq : kD ≠ ioQq := by decide
@[simp] theorem io_ioQq_ne_iC : ioQq ≠ iC := by decide
@[simp] theorem io_iC_ne_ioQq : iC ≠ ioQq := by decide
@[simp] theorem io_ioQq_ne_iU : ioQq ≠ iU := by decide
@[simp] theorem io_iU_ne_ioQq : iU ≠ ioQq := by decide
@[simp] theorem io_ioQq_ne_iQ : ioQq ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioQq : iQ ≠ ioQq := by decide
@[simp] theorem io_ioQq_ne_iA : ioQq ≠ iA := by decide
@[simp] theorem io_iA_ne_ioQq : iA ≠ ioQq := by decide
@[simp] theorem io_ioQq_ne_iK : ioQq ≠ iK := by decide
@[simp] theorem io_iK_ne_ioQq : iK ≠ ioQq := by decide
@[simp] theorem io_ioV_ne_ioTy : ioV ≠ ioTy := by decide
@[simp] theorem io_ioV_ne_ioPp : ioV ≠ ioPp := by decide
@[simp] theorem io_ioV_ne_ioB0 : ioV ≠ ioB0 := by decide
@[simp] theorem io_ioV_ne_ioMj : ioV ≠ ioMj := by decide
@[simp] theorem io_ioV_ne_ioIk : ioV ≠ ioIk := by decide
@[simp] theorem io_ioV_ne_ioRs : ioV ≠ ioRs := by decide
@[simp] theorem io_ioV_ne_ioRp : ioV ≠ ioRp := by decide
@[simp] theorem io_ioV_ne_ioPm : ioV ≠ ioPm := by decide
@[simp] theorem io_ioV_ne_ioMe : ioV ≠ ioMe := by decide
@[simp] theorem io_ioV_ne_ioHd : ioV ≠ ioHd := by decide
@[simp] theorem io_ioV_ne_ioCj : ioV ≠ ioCj := by decide
@[simp] theorem io_ioV_ne_ioUj : ioV ≠ ioUj := by decide
@[simp] theorem io_ioV_ne_ioW : ioV ≠ ioW := by decide
@[simp] theorem io_ioV_ne_ioQj : ioV ≠ ioQj := by decide
@[simp] theorem io_ioV_ne_ioRn : ioV ≠ ioRn := by decide
@[simp] theorem io_ioV_ne_ioRl : ioV ≠ ioRl := by decide
@[simp] theorem io_ioV_ne_ioRq : ioV ≠ ioRq := by decide
@[simp] theorem io_ioV_ne_ioMa : ioV ≠ ioMa := by decide
@[simp] theorem io_ioV_ne_ioMl : ioV ≠ ioMl := by decide
@[simp] theorem io_ioV_ne_ioNp : ioV ≠ ioNp := by decide
@[simp] theorem io_ioV_ne_ioNf : ioV ≠ ioNf := by decide
@[simp] theorem io_ioV_ne_ioF : ioV ≠ ioF := by decide
@[simp] theorem io_ioV_ne_ioLp : ioV ≠ ioLp := by decide
@[simp] theorem io_ioV_ne_ioRc : ioV ≠ ioRc := by decide
@[simp] theorem io_ioV_ne_ioRh : ioV ≠ ioRh := by decide
@[simp] theorem io_ioV_ne_ioBd : ioV ≠ ioBd := by decide
@[simp] theorem io_ioV_ne_ioT1 : ioV ≠ ioT1 := by decide
@[simp] theorem io_ioV_ne_ioP : ioV ≠ ioP := by decide
@[simp] theorem io_ioV_ne_ioT2 : ioV ≠ ioT2 := by decide
@[simp] theorem io_ioV_ne_ioQq : ioV ≠ ioQq := by decide
@[simp] theorem io_ioV_ne_ioVl : ioV ≠ ioVl := by decide
@[simp] theorem io_ioV_ne_ioX : ioV ≠ ioX := by decide
@[simp] theorem io_ioV_ne_lFl : ioV ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioV : lFl ≠ ioV := by decide
@[simp] theorem io_ioV_ne_lDh : ioV ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioV : lDh ≠ ioV := by decide
@[simp] theorem io_ioV_ne_lDt : ioV ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioV : lDt ≠ ioV := by decide
@[simp] theorem io_ioV_ne_lDg : ioV ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioV : lDg ≠ ioV := by decide
@[simp] theorem io_ioV_ne_lDi : ioV ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioV : lDi ≠ ioV := by decide
@[simp] theorem io_ioV_ne_lRp : ioV ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioV : lRp ≠ ioV := by decide
@[simp] theorem io_ioV_ne_lRn : ioV ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioV : lRn ≠ ioV := by decide
@[simp] theorem io_ioV_ne_lFle : ioV ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioV : lFle ≠ ioV := by decide
@[simp] theorem io_ioV_ne_lDir : ioV ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioV : lDir ≠ ioV := by decide
@[simp] theorem io_ioV_ne_lKb : ioV ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioV : lKb ≠ ioV := by decide
@[simp] theorem io_ioV_ne_kFu : ioV ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioV : kFu ≠ ioV := by decide
@[simp] theorem io_ioV_ne_kD : ioV ≠ kD := by decide
@[simp] theorem io_kD_ne_ioV : kD ≠ ioV := by decide
@[simp] theorem io_ioV_ne_iC : ioV ≠ iC := by decide
@[simp] theorem io_iC_ne_ioV : iC ≠ ioV := by decide
@[simp] theorem io_ioV_ne_iU : ioV ≠ iU := by decide
@[simp] theorem io_iU_ne_ioV : iU ≠ ioV := by decide
@[simp] theorem io_ioV_ne_iQ : ioV ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioV : iQ ≠ ioV := by decide
@[simp] theorem io_ioV_ne_iA : ioV ≠ iA := by decide
@[simp] theorem io_iA_ne_ioV : iA ≠ ioV := by decide
@[simp] theorem io_ioV_ne_iK : ioV ≠ iK := by decide
@[simp] theorem io_iK_ne_ioV : iK ≠ ioV := by decide
@[simp] theorem io_ioVl_ne_ioTy : ioVl ≠ ioTy := by decide
@[simp] theorem io_ioVl_ne_ioPp : ioVl ≠ ioPp := by decide
@[simp] theorem io_ioVl_ne_ioB0 : ioVl ≠ ioB0 := by decide
@[simp] theorem io_ioVl_ne_ioMj : ioVl ≠ ioMj := by decide
@[simp] theorem io_ioVl_ne_ioIk : ioVl ≠ ioIk := by decide
@[simp] theorem io_ioVl_ne_ioRs : ioVl ≠ ioRs := by decide
@[simp] theorem io_ioVl_ne_ioRp : ioVl ≠ ioRp := by decide
@[simp] theorem io_ioVl_ne_ioPm : ioVl ≠ ioPm := by decide
@[simp] theorem io_ioVl_ne_ioMe : ioVl ≠ ioMe := by decide
@[simp] theorem io_ioVl_ne_ioHd : ioVl ≠ ioHd := by decide
@[simp] theorem io_ioVl_ne_ioCj : ioVl ≠ ioCj := by decide
@[simp] theorem io_ioVl_ne_ioUj : ioVl ≠ ioUj := by decide
@[simp] theorem io_ioVl_ne_ioW : ioVl ≠ ioW := by decide
@[simp] theorem io_ioVl_ne_ioQj : ioVl ≠ ioQj := by decide
@[simp] theorem io_ioVl_ne_ioRn : ioVl ≠ ioRn := by decide
@[simp] theorem io_ioVl_ne_ioRl : ioVl ≠ ioRl := by decide
@[simp] theorem io_ioVl_ne_ioRq : ioVl ≠ ioRq := by decide
@[simp] theorem io_ioVl_ne_ioMa : ioVl ≠ ioMa := by decide
@[simp] theorem io_ioVl_ne_ioMl : ioVl ≠ ioMl := by decide
@[simp] theorem io_ioVl_ne_ioNp : ioVl ≠ ioNp := by decide
@[simp] theorem io_ioVl_ne_ioNf : ioVl ≠ ioNf := by decide
@[simp] theorem io_ioVl_ne_ioF : ioVl ≠ ioF := by decide
@[simp] theorem io_ioVl_ne_ioLp : ioVl ≠ ioLp := by decide
@[simp] theorem io_ioVl_ne_ioRc : ioVl ≠ ioRc := by decide
@[simp] theorem io_ioVl_ne_ioRh : ioVl ≠ ioRh := by decide
@[simp] theorem io_ioVl_ne_ioBd : ioVl ≠ ioBd := by decide
@[simp] theorem io_ioVl_ne_ioT1 : ioVl ≠ ioT1 := by decide
@[simp] theorem io_ioVl_ne_ioP : ioVl ≠ ioP := by decide
@[simp] theorem io_ioVl_ne_ioT2 : ioVl ≠ ioT2 := by decide
@[simp] theorem io_ioVl_ne_ioQq : ioVl ≠ ioQq := by decide
@[simp] theorem io_ioVl_ne_ioV : ioVl ≠ ioV := by decide
@[simp] theorem io_ioVl_ne_ioX : ioVl ≠ ioX := by decide
@[simp] theorem io_ioVl_ne_lFl : ioVl ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioVl : lFl ≠ ioVl := by decide
@[simp] theorem io_ioVl_ne_lDh : ioVl ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioVl : lDh ≠ ioVl := by decide
@[simp] theorem io_ioVl_ne_lDt : ioVl ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioVl : lDt ≠ ioVl := by decide
@[simp] theorem io_ioVl_ne_lDg : ioVl ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioVl : lDg ≠ ioVl := by decide
@[simp] theorem io_ioVl_ne_lDi : ioVl ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioVl : lDi ≠ ioVl := by decide
@[simp] theorem io_ioVl_ne_lRp : ioVl ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioVl : lRp ≠ ioVl := by decide
@[simp] theorem io_ioVl_ne_lRn : ioVl ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioVl : lRn ≠ ioVl := by decide
@[simp] theorem io_ioVl_ne_lFle : ioVl ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioVl : lFle ≠ ioVl := by decide
@[simp] theorem io_ioVl_ne_lDir : ioVl ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioVl : lDir ≠ ioVl := by decide
@[simp] theorem io_ioVl_ne_lKb : ioVl ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioVl : lKb ≠ ioVl := by decide
@[simp] theorem io_ioVl_ne_kFu : ioVl ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioVl : kFu ≠ ioVl := by decide
@[simp] theorem io_ioVl_ne_kD : ioVl ≠ kD := by decide
@[simp] theorem io_kD_ne_ioVl : kD ≠ ioVl := by decide
@[simp] theorem io_ioVl_ne_iC : ioVl ≠ iC := by decide
@[simp] theorem io_iC_ne_ioVl : iC ≠ ioVl := by decide
@[simp] theorem io_ioVl_ne_iU : ioVl ≠ iU := by decide
@[simp] theorem io_iU_ne_ioVl : iU ≠ ioVl := by decide
@[simp] theorem io_ioVl_ne_iQ : ioVl ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioVl : iQ ≠ ioVl := by decide
@[simp] theorem io_ioVl_ne_iA : ioVl ≠ iA := by decide
@[simp] theorem io_iA_ne_ioVl : iA ≠ ioVl := by decide
@[simp] theorem io_ioVl_ne_iK : ioVl ≠ iK := by decide
@[simp] theorem io_iK_ne_ioVl : iK ≠ ioVl := by decide
@[simp] theorem io_ioX_ne_ioTy : ioX ≠ ioTy := by decide
@[simp] theorem io_ioX_ne_ioPp : ioX ≠ ioPp := by decide
@[simp] theorem io_ioX_ne_ioB0 : ioX ≠ ioB0 := by decide
@[simp] theorem io_ioX_ne_ioMj : ioX ≠ ioMj := by decide
@[simp] theorem io_ioX_ne_ioIk : ioX ≠ ioIk := by decide
@[simp] theorem io_ioX_ne_ioRs : ioX ≠ ioRs := by decide
@[simp] theorem io_ioX_ne_ioRp : ioX ≠ ioRp := by decide
@[simp] theorem io_ioX_ne_ioPm : ioX ≠ ioPm := by decide
@[simp] theorem io_ioX_ne_ioMe : ioX ≠ ioMe := by decide
@[simp] theorem io_ioX_ne_ioHd : ioX ≠ ioHd := by decide
@[simp] theorem io_ioX_ne_ioCj : ioX ≠ ioCj := by decide
@[simp] theorem io_ioX_ne_ioUj : ioX ≠ ioUj := by decide
@[simp] theorem io_ioX_ne_ioW : ioX ≠ ioW := by decide
@[simp] theorem io_ioX_ne_ioQj : ioX ≠ ioQj := by decide
@[simp] theorem io_ioX_ne_ioRn : ioX ≠ ioRn := by decide
@[simp] theorem io_ioX_ne_ioRl : ioX ≠ ioRl := by decide
@[simp] theorem io_ioX_ne_ioRq : ioX ≠ ioRq := by decide
@[simp] theorem io_ioX_ne_ioMa : ioX ≠ ioMa := by decide
@[simp] theorem io_ioX_ne_ioMl : ioX ≠ ioMl := by decide
@[simp] theorem io_ioX_ne_ioNp : ioX ≠ ioNp := by decide
@[simp] theorem io_ioX_ne_ioNf : ioX ≠ ioNf := by decide
@[simp] theorem io_ioX_ne_ioF : ioX ≠ ioF := by decide
@[simp] theorem io_ioX_ne_ioLp : ioX ≠ ioLp := by decide
@[simp] theorem io_ioX_ne_ioRc : ioX ≠ ioRc := by decide
@[simp] theorem io_ioX_ne_ioRh : ioX ≠ ioRh := by decide
@[simp] theorem io_ioX_ne_ioBd : ioX ≠ ioBd := by decide
@[simp] theorem io_ioX_ne_ioT1 : ioX ≠ ioT1 := by decide
@[simp] theorem io_ioX_ne_ioP : ioX ≠ ioP := by decide
@[simp] theorem io_ioX_ne_ioT2 : ioX ≠ ioT2 := by decide
@[simp] theorem io_ioX_ne_ioQq : ioX ≠ ioQq := by decide
@[simp] theorem io_ioX_ne_ioV : ioX ≠ ioV := by decide
@[simp] theorem io_ioX_ne_ioVl : ioX ≠ ioVl := by decide
@[simp] theorem io_ioX_ne_lFl : ioX ≠ lFl := by decide
@[simp] theorem io_lFl_ne_ioX : lFl ≠ ioX := by decide
@[simp] theorem io_ioX_ne_lDh : ioX ≠ lDh := by decide
@[simp] theorem io_lDh_ne_ioX : lDh ≠ ioX := by decide
@[simp] theorem io_ioX_ne_lDt : ioX ≠ lDt := by decide
@[simp] theorem io_lDt_ne_ioX : lDt ≠ ioX := by decide
@[simp] theorem io_ioX_ne_lDg : ioX ≠ lDg := by decide
@[simp] theorem io_lDg_ne_ioX : lDg ≠ ioX := by decide
@[simp] theorem io_ioX_ne_lDi : ioX ≠ lDi := by decide
@[simp] theorem io_lDi_ne_ioX : lDi ≠ ioX := by decide
@[simp] theorem io_ioX_ne_lRp : ioX ≠ lRp := by decide
@[simp] theorem io_lRp_ne_ioX : lRp ≠ ioX := by decide
@[simp] theorem io_ioX_ne_lRn : ioX ≠ lRn := by decide
@[simp] theorem io_lRn_ne_ioX : lRn ≠ ioX := by decide
@[simp] theorem io_ioX_ne_lFle : ioX ≠ lFle := by decide
@[simp] theorem io_lFle_ne_ioX : lFle ≠ ioX := by decide
@[simp] theorem io_ioX_ne_lDir : ioX ≠ lDir := by decide
@[simp] theorem io_lDir_ne_ioX : lDir ≠ ioX := by decide
@[simp] theorem io_ioX_ne_lKb : ioX ≠ lKb := by decide
@[simp] theorem io_lKb_ne_ioX : lKb ≠ ioX := by decide
@[simp] theorem io_ioX_ne_kFu : ioX ≠ kFu := by decide
@[simp] theorem io_kFu_ne_ioX : kFu ≠ ioX := by decide
@[simp] theorem io_ioX_ne_kD : ioX ≠ kD := by decide
@[simp] theorem io_kD_ne_ioX : kD ≠ ioX := by decide
@[simp] theorem io_ioX_ne_iC : ioX ≠ iC := by decide
@[simp] theorem io_iC_ne_ioX : iC ≠ ioX := by decide
@[simp] theorem io_ioX_ne_iU : ioX ≠ iU := by decide
@[simp] theorem io_iU_ne_ioX : iU ≠ ioX := by decide
@[simp] theorem io_ioX_ne_iQ : ioX ≠ iQ := by decide
@[simp] theorem io_iQ_ne_ioX : iQ ≠ ioX := by decide
@[simp] theorem io_ioX_ne_iA : ioX ≠ iA := by decide
@[simp] theorem io_iA_ne_ioX : iA ≠ ioX := by decide
@[simp] theorem io_ioX_ne_iK : ioX ≠ iK := by decide
@[simp] theorem io_iK_ne_ioX : iK ≠ ioX := by decide

/-- The certificate at the verified mode; nothing at the trusted one. -/
def ioFam (v : Bool) (rest : ProgHOL 64) : ProgHOL 64 :=
  if v then
    .seq (.call (some (some (.local, ioF), none)) fFam
      [vv kFu, vv kD, vv iC, vv iU, vv iQ, vv iA, vv iK, vv ioUj, vv ioQj, vv ioRq, vv ioMa])
      (.ite (.cmp .equal (vv ioF) (.const 0)) (.return (.const 0)) rest)
  else rest

def ioLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, ioTy, ioPp, ioB0, ioMj, ioIk, ioRs, ioRp, ioPm, ioMe, ioHd, ioCj, ioUj, ioW, ioQj, ioRn, ioRl, ioRq, ioMa, ioMl, ioNp, ioNf, ioF, ioLp, ioRc, ioRh, ioBd, ioT1, ioP, ioT2, ioQq, ioV, ioVl, ioX]

def ioCore (v : Bool) (C : Ctx) : ProgHOL 64 :=
  (.seq (.assign .local ioTy (.load .one (.op .add [vv iQ, .const 24])))
  (.seq (.call (some (some (.local, ioPp), none)) fPp [vv iK, vv ioTy])
  (.ite (.cmp .equal (vv ioPp) (.const 0)) (.return (.const 0))
  (.seq (.call (some (some (.local, ioB0), none)) fInternBVar [.const 0])
  (.seq (.assign .local ioMj (.load .one (.op .add [vv iA, .shift .lsl (vv iK) (.const 3)])))
  (.seq (.assign .local ioIk (.load .one (.op .add [vv iQ, .const 48])))
  (.seq (.assign .local ioRs (.load .one (.op .add [vv iQ, .const 56])))
  (.seq (.assign .local ioRp (.load .one (.op .add [vv iQ, .const 40])))
  (.seq (.call (some (some (.local, ioPm), none)) fPm [vv kFu, vv kD, vv iC, vv ioIk, vv ioRs, vv ioMj])
  (.ite (.cmp .equal (.op .and [vv ioPm, .const 1]) (.const 0)) (.return (.const 0))
  (.seq (.assign .local ioMe (.shift .lsr (vv ioPm) (.const 1)))
  (.seq (.call (some (some (.local, ioHd), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv ioMe])
  (.seq (.assign .local lFl (vv lFle))
  (.seq (.assign .local lDh (vv ioHd))
  (.seq eViewP
  (.seq (.assign .local ioCj (.load .one (vv lRp)))
  (.seq (.assign .local ioUj (.load .one (.op .add [vv lRp, .const 8])))
  (envFindP C ioW (vv ioCj)
  (.seq (.assign .local ioQj (.op .sub [vv ioW, .const 1]))
  (.seq (.assign .local ioRn (.load .one (vv ioRs)))
  (.seq (.call (some (some (.local, ioRl), none)) fFr [vv ioRs, .const 0, vv ioRn, vv ioCj])
  (.ite (.cmp .equal (vv ioRl) (.const 0)) (.return (.const 0))
  (.seq (.assign .local ioRq (.op .sub [vv ioRl, .const 1]))
  (.seq (.call (some (some (.local, ioMa), none)) ExG.fGaa [.const (BitVec.ofNat 64 coreWalkFuel), vv ioMe])
  (.seq (.assign .local ioMl (.load .one (vv ioMa)))
  (.seq (.assign .local ioNp (.load .one (.op .add [vv ioQj, .const 32])))
  (.seq (.assign .local ioNf (.load .one (.op .add [vv ioRq, .const 8])))
  (.ite (.cmp .notEqual (vv ioMl) (.op .add [vv ioNp, vv ioNf])) (.return (.const 0))
  (ioFam v
  (.seq (.assign .local ioLp (.load .one (.op .add [vv iQ, .const 16])))
  (.seq (.assign .local ioRc (.load .one (vv ioRq)))
  (.seq (.assign .local ioRh (.load .one (.op .add [vv ioRq, .const 40])))
  (.seq (.call (some (some (.local, ioBd), none)) fRb [vv iC, vv ioRc, vv ioLp, vv ioRh, .op .add [vv ioRp, vv ioNf], vv iU])
  (.seq (.assign .local ioT1 (.cmp .lower (vv ioRp) (vv iK)))
  (.seq (.assign .local ioP (.op .add [vv iK, .op .and [.op .sub [vv ioRp, vv iK], .op .sub [.const 0, vv ioT1]]]))
  (.seq (.assign .local ioT2 (.cmp .lower (vv ioNp) (vv ioMl)))
  (.seq (.assign .local ioQq (.op .add [vv ioMl, .op .and [.op .sub [vv ioNp, vv ioMl], .op .sub [.const 0, vv ioT2]]]))
  (.seq (.call (some (some (.local, ioV), none)) fIv [vv iA, vv ioP, vv ioMa, vv ioQq])
  (.seq (.assign .local ioVl (.load .one (vv ioV)))
  (.seq (.call (some (some (.local, ioX), none)) ExQ.fIrr [vv ioV, .const 0, vv ioVl, .const (BitVec.ofNat 64 coreWalkFuel), vv ioBd, .const 0])
  (.return (.op .add [vv ioX, .const 1]))))))))))))))))))))))))))))))))))))))))))

def ioBody (v : Bool) (C : Ctx) : ProgHOL 64 := prologue ioLocals (ioCore v C)

section
variable {σ : Type}

theorem io_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ioLocals → (ctxEnv C ++ ioParams.zip vals).get x = none :=
  Knot.params_none C ioLocals ioParams vals (by decide) (by decide)

/-- A classified major as a word: the term, shifted, and the constructor bit. -/
def encMV (mv : MajorView) : BitVec 64 := (Enc.idxW mv.expr <<< (1 : Nat)) + (if mv.isCtor then 1 else 0)

def PostMV (C : Ctx) (mv : MajorView) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ w = encMV mv ∧ SR (ctxH C H') s' st

theorem encMV_toNat (mv : MajorView) :
    (encMV mv).toNat = 2 * (Enc.idxW mv.expr).toNat + (if mv.isCtor then 1 else 0) := by
  have hw : (Enc.idxW mv.expr).toNat < 2 ^ 32 := by simp [Enc.idxW]; exact UInt32.toNat_lt _
  have h2 : (Enc.idxW mv.expr <<< (1 : Nat)).toNat = 2 * (Enc.idxW mv.expr).toNat := by
    rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega)]; ring
  unfold encMV
  cases mv.isCtor
  · rw [if_neg (by decide), show (0 : BitVec 64) = 0#64 from rfl, BitVec.add_zero, h2]; simp
  · rw [if_pos rfl, BitVec.toNat_add, h2, show (1 : BitVec 64).toNat = 1 from rfl]; simp; omega

theorem encMV_and1 (mv : MajorView) : encMV mv &&& 1#64 = if mv.isCtor then 1#64 else 0#64 := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_and, show (1#64 : BitVec 64).toNat = 2 ^ 1 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod,
    encMV_toNat]
  cases mv.isCtor <;> simp <;> omega

theorem encMV_shr1 (mv : MajorView) : encMV mv >>> (1 : Nat) = Enc.idxW mv.expr := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow, encMV_toNat]
  cases mv.isCtor <;> simp <;> omega

/-- The code `iotaRecAt` calls (the three big callees are given by their specs). -/
structure IoCodes (C : Ctx) (Bpm Bfm Brb : ProgHOL 64) : Prop where
  pp : C.code.lookup fPp = some (ppParams.map (fun p => (p, ShapeHOL.one)), ppBody, .one)
  bv : C.code.lookup fInternBVar = some ([(lIw, .one)], bvarBody, .one)
  pm : C.code.lookup fPm = some (pmParams.map (fun p => (p, ShapeHOL.one)), Bpm, .one)
  af : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  mg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  mp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  fr : C.code.lookup fFr = some (frParams.map (fun p => (p, ShapeHOL.one)), frBody, .one)
  gaa : C.code.lookup ExG.fGaa = some ([(pFu, .one), (pH, .one)], ExG.gaaBody C, .one)
  fm : C.code.lookup fFam = some (fmParams.map (fun p => (p, ShapeHOL.one)), Bfm, .one)
  rb : C.code.lookup fRb = some (rbParams.map (fun p => (p, ShapeHOL.one)), Brb, .one)
  iv : C.code.lookup fIv = some (ivParams.map (fun p => (p, ShapeHOL.one)), ivBody C, .one)
  irr : C.code.lookup ExQ.fIrr = some (ExQ.irrParams.map (fun p => (p, ShapeHOL.one)), ExQ.irrBody C, .one)
  q : ExQ.CodesQ C

end

section
variable {σ : Type}

theorem codesQ_H {C : Ctx} (hc : ExQ.CodesQ C) (H : List (BitVec 64)) : ExQ.CodesQ (ctxH C H) :=
  ⟨⟨hc.ilp, hc.internApp, hc.internLam, hc.internForallE, hc.internLet, hc.internBVar, hc.internProj⟩, hc.ilg,
    hc.memoGet, hc.memoProbe, hc.memoSet, hc.memoIns⟩

theorem min_word (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    BitVec.ofNat 64 b + ((BitVec.ofNat 64 a - BitVec.ofNat 64 b) &&&
      (0#64 - if BitVec.ofNat 64 a < BitVec.ofNat 64 b then 1#64 else 0#64)) =
      BitVec.ofNat 64 (if a < b then a else b) := by
  have hlt := word_lt_iff a b (by unfold B; omega) (by unfold B; omega)
  by_cases h : a < b
  · rw [if_pos (hlt.mpr h), if_pos h, show (0#64 : BitVec 64) - 1#64 = BitVec.allOnes 64 from by decide,
      BitVec.and_allOnes]
    bv_omega
  · rw [if_neg (fun x => h (hlt.mp x)), if_neg h, show (0#64 : BitVec 64) - 0#64 = 0#64 from by decide,
      BitVec.and_zero, BitVec.add_zero]

theorem cellA_shl (C : Ctx) (o k : Nat) (hk : k < 2 ^ 60) :
    cellA C o + BitVec.ofNat 64 k <<< (3 : Nat) = cellA C (o + k) := by
  rw [w_shl _ _ (by omega), show k * 2 ^ 3 = 8 * k by omega, ExPre.cellA_off]

theorem specR_callPure {α β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f : MlS) (ps : List MlS) (es : List (ExpHOL 64)) (B : ProgHOL 64) (vs : List (BitVec 64)) (a : α)
    (hnd : ps.Nodup) (hl : vs.length = ps.length)
    (hx : x ∈ D) (hC : C.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), B, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs)
    (Rf : α → BitVec 64 → AState → PState σ → Prop) (Qx : α → BitVec 64 → AState → List (BitVec 64) → Prop)
    (hRf : ∀ a w s' st, Rf a w s' st → ∃ H', C.H <+: H' ∧ Qx a w s' H' ∧ SR (ctxH C H') s' st)
    (hB : ∀ u : PState σ, SR C s u → (∀ a v, (a, v) ∈ M → u.memaddrs a ∧ u.memory a = .word v) →
      (∀ i (hi : i < ps.length), u.locals.lookup ps[i] = some (.val (.word (vs[i]'(by omega))))) →
      SpecR (· = u) B s (pure a : AM α) Rf)
    (hk : ∀ w H', C.H <+: H' → Qx a w s H' → SpecR (Inv (ctxH C H') s ((x, w) :: Γ) [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f es) rest) s m R := by
  refine specR_congr (m' := (pure a : AM α) >>= fun _ => m) rfl ?_
  refine specR_callNIH x f ps es B vs hnd hl hx hC hes
    (fun b w s' st => (pure a : AM α) s = .ok (b, s') ∧ Rf b w s' st) (fun b w s' H' => b = a ∧ s' = s ∧ Qx b w s' H')
    (fun b w s' st ⟨hrun, hr⟩ => by
      obtain ⟨hb, hs⟩ := pure_ok_inv hrun
      obtain ⟨H', hp, hq, hsr⟩ := hRf b w s' st hr
      exact ⟨H', hp, ⟨hb, hs, hq⟩, hsr⟩)
    (fun u hu h1 h2 => specR_run (hB u hu h1 h2))
    (fun b w s' H' hp ⟨hb, hs, hq⟩ => by subst hb hs; exact hk w H' hp hq)

theorem io_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (Bpm Bfm Brb : ProgHOL 64) (hc : IoCodes C Bpm Bfm Brb)
    (s : AState) (d : Nat) (c : NIdx) (us : LsIdx) (cv : IConstantVal) (mI rP : Nat) (isK : Bool)
    (rules : List IRecRule) (q : Nat) (hci : CIE C.EB C.EH q (.recInfo cv mI rP isK rules))
    (sargs : List EIdx) (oa : Nat) (hba : BlkAt C.H oa (sargs.map Enc.idxW)) (hle : mI + 1 ≤ sargs.length)
    (hPm : ∀ (H : List (BitVec 64)) s1 (m : EIdx) (rw : BitVec 64), C.H <+: H → RulesE C.EB C.EH rw rules →
      SpecR (σ := σ) (Pre (ctxH C H) s1 (pmParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c, boolW isK,
        rw, Enc.idxW m])) Bpm s1 (prepareMajor mode (knot mode C n) C.fe d c isK rules m) (PostMV (ctxH C H)))
    (hFam : mode.verifiedChecks = true → ∀ (H : List (BitVec 64)) s1 (usj : LsIdx) qj cvj cnP nF ind qr
      (rl : IRecRule) om (margs : List EIdx), C.H <+: H → CIE C.EB C.EH qj (.ctorInfo cvj cnP nF ind) →
      RuleE C.EB C.EH qr rl → BlkAt H om (margs.map Enc.idxW) →
      SpecR (σ := σ) (Pre (ctxH C H) s1 (fmParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c, Enc.idxW us,
        ecell C q, cellA C oa, BitVec.ofNat 64 (mI + 1), Enc.idxW usj, ecell C qj, ecell C qr, cellA C om])) Bfm s1
        (iotaFam mode (knot mode C n) C.fe d cv us mI rP isK (sargs.take (mI + 1)) usj cvj cnP ind rl margs)
        (Knot.PostB (ctxH C H)))
    (hRb : ∀ (H : List (BitVec 64)) s1 (wl : BitVec 64) (rl : IRecRule) (k : Nat), C.H <+: H →
      ENList C.EB C.EH wl cv.levelParams →
      SpecR (σ := σ) (Pre (ctxH C H) s1 (rbParams.zip [Enc.idxW c, Enc.idxW rl.ctor, wl, Enc.idxW rl.rhs,
        BitVec.ofNat 64 k, Enc.idxW us])) Brb s1 (ruleBodyAt c rl.ctor cv.levelParams rl.rhs k us)
        (PostK (ctxH C H))) :
    SpecR (σ := σ) (Pre C s (ioParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c, Enc.idxW us, ecell C q,
      cellA C oa, BitVec.ofNat 64 (mI + 1)])) (ioBody mode.verifiedChecks C) s
      (iotaRecAt mode (knot mode C n) C.fe d c us cv mI rP isK rules (takeEidx sargs.toArray (mI + 1)))
      (UD.PostO C) := by
  refine specR_prologue (UD.postO_locals C) (io_none C _) ?_
  unfold ioCore
  rw [iotaRecAt_eq]
  obtain ⟨⟨_, ⟨wl, hwl, hlps⟩, hcty⟩, _, hmi, hrp, hisk, wr, hwr, hrules⟩ := hci
  refine specR_atEntry fun t0 ht0 => ?_
  have hsl := blk_small0 hok ht0.sr hba
  simp only [List.length_map] at hsl
  have hmi2 := hmi.2
  have hrp2 := hrp.2
  refine specR_envLoadI ioTy (.op .add [vv iQ, .const 24]) (q + 3) (Enc.idxW cv.type) (by decide)
    (by simp +decide [sev, Env.get, ioParams, ctxEnv]; exact ecell_add24 C q)
    (by rw [show q + 3 = q + 1 + 2 by omega]; simpa [IConstantInfo.toConstantVal] using hcty) ?_
  refine specR_callNIH ioPp fPp ppParams [vv iK, vv ioTy] ppBody [BitVec.ofNat 64 (mI + 1), Enc.idxW cv.type]
    (by decide) rfl (by decide) hc.pp ⟨by simp +decide [Env.get, ioParams, ctxEnv], by simp, trivial⟩
    (UD.PostO C) (fun o w _ _ => w = optW o) (fun o w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ppParams _ rfl hlk)
      (pp_spec C hok hc.pp (mI + 1) cv.type s (by omega)))
    (fun o w s1 H1 hp1 hw => ?_)
  subst hw
  have hret0 : ∀ {Γ : Env} {M : Mem} {H : List (BitVec 64)} {s2 : AState}, C.H <+: H →
      SpecR (σ := σ) (Inv (ctxH C H) s2 Γ M (ctxLocals ++ ioLocals)) (.return (.const 0)) s2
        (pure none : AM (Option EIdx)) (UD.PostO C) :=
    fun hp => specR_returnI _ (optW none) (by simp [optWG]; rfl)
      (fun t ht => ⟨_, hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rcases o with _ | ty'
  · refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact hret0 hp1
  have hne : optW (some ty') ≠ 0 := WB.idxW_succ_ne ty'
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  dsimp only
  have hok1 := ctxOK_H hok H1
  refine specR_internBVarI (C := ctxH C H1) ra hok1 hc.bv ioB0 (.const 0) 0 (by decide) (by decide) rfl
    (fun b0 s2 => ?_)
  have hba1 := blkAt_mono hba hp1
  refine UD.specR_heapLoadI' (C := ctxH C H1) ioMj _ (oa + 1 + mI) (Enc.idxW sargs[mI])
    (by have := hba1.2 mI (by simp; omega); simp only [List.getElem_map] at this; exact this) (by decide)
    (by simp +decide [sev, Env.get, ioParams, ctxEnv]; rw [cellA_shl C oa (mI + 1) (by have := hle; omega), show oa + (mI + 1) = oa + 1 + mI by omega]; rfl) ?_
  refine specR_envLoadI (C := ctxH C H1) ioIk (.op .add [vv iQ, .const 48]) (q + 6) _ (by decide)
    (by simp +decide [sev, Env.get, ioParams, ctxEnv]; rw [show (48#64 : BitVec 64) = BitVec.ofNat 64 (8 * 6) from rfl,
      ecell_add]; rfl) hisk ?_
  refine specR_envLoadI (C := ctxH C H1) ioRs (.op .add [vv iQ, .const 56]) (q + 7) _ (by decide)
    (by simp +decide [sev, Env.get, ioParams, ctxEnv]; rw [show (56#64 : BitVec 64) = BitVec.ofNat 64 (8 * 7) from rfl,
      ecell_add]; rfl) hwr ?_
  refine specR_envLoadI (C := ctxH C H1) ioRp (.op .add [vv iQ, .const 40]) (q + 5) _ (by decide)
    (by simp +decide [sev, Env.get, ioParams, ctxEnv]; rw [show (40#64 : BitVec 64) = BitVec.ofNat 64 (8 * 5) from rfl,
      ecell_add]; rfl) hrp.1 ?_
  have hgd : (takeEidx sargs.toArray (mI + 1)).toList.getD mI b0 = sargs[mI] := by
    rw [ConRon.Bridge.ExprOps.takeEidx_toList]
    simp [List.getD_eq_getElem?_getD, List.getElem?_take, show mI < mI + 1 by omega,
      List.getElem?_eq_getElem (show mI < sargs.length by omega)]
  rw [hgd]
  refine specR_callNIH (C := ctxH C H1) ioPm fPm pmParams [vv kFu, vv kD, vv iC, vv ioIk, vv ioRs, vv ioMj] Bpm
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c, boolW isK, wr, Enc.idxW sargs[mI]] (by decide) rfl (by decide)
    hc.pm ⟨by simp +decide [Env.get, ioParams, ctxEnv], by simp +decide [Env.get, ioParams, ctxEnv],
      by simp +decide [Env.get, ioParams, ctxEnv], by simp, by simp, by simp, trivial⟩
    (fun mv w s' st => prepareMajor mode (knot mode C n) C.fe d c isK rules sargs[mI] s2 = .ok (mv, s') ∧
      PostMV (ctxH C H1) mv w s' st)
    (fun mv w s' _ => prepareMajor mode (knot mode C n) C.fe d c isK rules sargs[mI] s2 = .ok (mv, s') ∧
      w = encMV mv)
    (fun mv w s' st ⟨hrun, H', hp, hw, hsr⟩ => ⟨H', hp, ⟨hrun, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu pmParams _ rfl hlk)
      (hPm H1 s2 sargs[mI] wr hp1 hrules)))
    (fun mv w s3 H3 hp3 ⟨hrun, hw⟩ => ?_)
  subst hw
  have hview := prepareMajor_view mode (knot mode C n) C.fe d c isK rules _ _ mv s3 hrun
  cases hct : mv.isCtor
  · refine specR_ifI _ 1 (by simp [sev, encMV_and1, hct, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    rcases mv with ⟨⟩ | ⟨e⟩
    · simp [MajorView.isCtor] at hct
    · exact hret0 (hp1.trans hp3)
  refine specR_ifI _ 0 (by simp [sev, encMV_and1, hct, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun h => absurd rfl h) (fun _ => ?_)
  rcases mv with ⟨major, cj, usj, cvj, cnP, nF, ind⟩ | ⟨e⟩
  swap
  · simp [MajorView.isCtor] at hct
  have hcv := hview hct
  simp only [MajorView.expr] at hcv
  obtain ⟨hd, hgaf, hhtg, hvc, hfind, _, _⟩ := ctorView_ctor_inv C.fe major s3 major cj usj cvj cnP nF ind s3 hcv
  have hp13 : C.H <+: H3 := hp1.trans hp3
  have hok3 := ctxOK_H hok H3
  refine specR_assignI ioMe _ (Enc.idxW major) (by decide) (by simp [sev]; exact encMV_shr1 _) ?_
  refine specR_congr (m' := getAppFn coreWalkFuel major >>= fun _ => iotaTail mode (knot mode C n) C.fe d c us cv
    mI rP isK rules (takeEidx sargs.toArray (mI + 1)).toList (.ctor major cj usj cvj cnP nF ind))
    (by simp only [bind, StateT.bind]; rw [hgaf]; rfl) ?_
  refine specR_callNIM (C := ctxH C H3) ioHd fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv ioMe]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW major] (by decide) rfl (by decide) hc.af
    ⟨rfl, by simp, trivial⟩
    (fun a w s' st => getAppFn coreWalkFuel major s3 = .ok (a, s') ∧ Post (ctxH C H3) s3 a w s' st)
    (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec (ctxH C H3) hc.af coreWalkFuel major s3 CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide),
        hlk 1 (by decide)⟩))
    (fun hd' w s' st ⟨hrun2, hw, hs, _⟩ => ?_)
  subst hw
  rw [hgaf] at hrun2
  cases hrun2
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv ioHd) (Enc.idxW hd) (by decide) (by simp) ?_
  refine specR_viewP (C := ctxH C H3) hd (by simp) (by simp +decide [Env.get, ctxEnv] <;> rfl)
    (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv _ _ => ?_)
  have hv' : s3.store.view hd = some (.const cj usj) := ConRon.Bridge.view_of_viewConst hhtg hvc
  rw [hv'] at hv
  cases hv
  refine specR_loadI' ioCj (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW cj) (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW cj) [Enc.idxW usj] []) ?_
  refine specR_loadI' ioUj _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW usj) (by decide) (by simp +decide [sev]) rfl
    (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW cj) (Enc.idxW usj) [] []) ?_
  refine specR_dropM ?_
  refine specR_envFindI (C := ctxH C H3) hok3 hc.mg hc.mp ioW (vv ioCj) cj (by decide) (by simp)
    (by simp +decide [Env.get, ctxEnv]; rfl) ?_
  have hrel := find_rel hok cj
  rw [hfind] at hrel
  obtain ⟨qj, hm, hcij⟩ := hrel
  rw [show (ctxH C H3).envM[cj]? = some (ecell C qj) from hm]
  refine specR_assignI ioQj _ (ecell C qj) (by decide) (by simp [sev, optWG]; exact ecell_succ_sub C qj) ?_
  obtain ⟨orl, hwr_eq, hrlen, hrels⟩ := hrules
  refine specR_envLoadI (C := ctxH C H3) ioRn (vv ioRs) orl _ (by decide) (by simp [hwr_eq]; rfl) hrlen ?_
  refine specR_callPure (C := ctxH C H3) ioRl fFr frParams [vv ioRs, .const 0, vv ioRn, vv ioCj] frBody
    [ecell C orl, BitVec.ofNat 64 0, BitVec.ofNat 64 rules.length, Enc.idxW cj] (findRule (rules.drop 0) cj)
    (by decide) rfl (by decide) hc.fr ⟨by simp [hwr_eq]; rfl, rfl, by simp, by simp, trivial⟩
    (PostFR (ctxH C H3) s3) (fun r w _ _ => match r with
      | none => w = 0
      | some rl => ∃ q, w = ecell C q + 1 ∧ q < C.EN ∧ RuleE C.EB C.EH q rl)
    (fun r w s' st ⟨hs, hsr, hr⟩ => ⟨H3, List.prefix_refl _, hr, by rw [hs]; exact hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu frParams _ rfl hlk)
      (fr_spec (ctxH C H3) hok3 hc.fr rules orl hrlen hrels cj s3 _ 0 rfl (Nat.zero_le _)))
    (fun w H4 hp4 hfr => ?_)
  rw [List.drop_zero] at hfr
  simp only [iotaTail]
  rcases hfrr : findRule rules cj with _ | rl
  · rw [hfrr] at hfr
    simp only at hfr
    subst hfr
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact hret0 (hp13.trans hp4)
  rw [hfrr] at hfr
  obtain ⟨qr, hw, hqr, hrule⟩ := hfr
  subst hw
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hqr)
    (fun h => absurd rfl h) (fun _ => ?_)
  dsimp only
  refine specR_assignI ioRq _ (ecell C qr) (by decide) (by simp [sev]; exact ecell_succ_sub C qr) ?_
  have hp14 : C.H <+: H4 := hp13.trans hp4
  have hok4 := ctxOK_H hok H4
  refine specR_callNIH (C := ctxH C H4) ioMa ExG.fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv ioMe]
    (ExG.gaaBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW major] (by decide) rfl (by decide) hc.gaa
    ⟨rfl, by simp, trivial⟩
    (PostA (ctxH C H4)) (fun a w _ H5 => ∃ o5, w = cellA C o5 ∧ BlkAt H5 o5 (a.map Enc.idxW))
    (fun a w s' st ⟨H5, o5, hp, hw, hb, hsr⟩ => ⟨H5, hp, ⟨o5, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (ExG.gaa_spec (ctxH C H4) hok4 hc.gaa coreWalkFuel CV.coreWalkFuel_lt H4 major s3))
    (fun margs w s5 H5 hp5 ⟨om, hw, hbm⟩ => ?_)
  subst hw
  have hp15 : C.H <+: H5 := hp14.trans hp5
  have hok5 := ctxOK_H hok H5
  have ⟨_, _, hnp, hnf, _⟩ := hcij
  have ⟨hrct, hrnf, _, hrrhs⟩ := hrule
  refine UD.specR_heapLoadI' (C := ctxH C H5) ioMl (vv ioMa) om _ hbm.1 (by decide) (by simp; rfl) ?_
  refine specR_envLoadI (C := ctxH C H5) ioNp (.op .add [vv ioQj, .const 32]) (qj + 4) _ (by decide)
    (by simp [sev, vv]; exact UD.ecell_add32 C qj) hnp.1 ?_
  refine specR_envLoadI (C := ctxH C H5) ioNf (.op .add [vv ioRq, .const 8]) (qr + 1) _ (by decide)
    (by simp [sev, vv]; exact ecell_add C qr 1) hrnf.1 ?_
  refine specR_atEntry fun t5 ht5 => ?_
  have hml := blk_small0 hok5 ht5.sr hbm
  simp only [List.length_map] at hml
  have hnp2 := hnp.2
  have hnf2 := hrnf.2
  have hweq : (BitVec.ofNat 64 margs.length = BitVec.ofNat 64 cnP + BitVec.ofNat 64 rl.nfields) ↔
      margs.length = cnP + rl.nfields := by
    rw [BitVec.ofNat_add_ofNat]
    constructor
    · intro e; have := congrArg BitVec.toNat e; simp at this; omega
    · intro e; rw [e]
  by_cases hal : margs.length = cnP + rl.nfields
  swap
  · refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact fun e => hal (hweq.mp e))
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [if_neg hal]
    exact hret0 hp15
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hweq.mpr hal)
    (fun h => absurd rfl h) (fun _ => ?_)
  rw [if_pos hal]
  have hargs : (takeEidx sargs.toArray (mI + 1)).toList = sargs.take (mI + 1) := by
    rw [ConRon.Bridge.ExprOps.takeEidx_toList]
  rw [hargs]
  have hlps' := hlps
  cases hv : mode.verifiedChecks
  · simp only [ioFam, Bool.false_eq_true, ite_false]
    simp only [iotaFam, hv, Bool.not_false, ite_true, pure_bind]
    have hpXm : H5 <+: H5 := List.prefix_refl _
    have hpX : C.H <+: H5 := hp15
    refine specR_envLoadI (C := ctxH C H5) ioLp (.op .add [vv iQ, .const 16]) (q + 2) wl (by decide)
      (by simp +decide [sev, Env.get, ioParams, ctxEnv]; exact UD.ecell_add16 C q)
      (by rw [show q + 2 = q + 1 + 1 by omega]; exact hwl) ?_
    refine specR_envLoadI (C := ctxH C H5) ioRc (vv ioRq) qr _ (by decide) (by simp; rfl) hrct ?_
    refine specR_envLoadI (C := ctxH C H5) ioRh (.op .add [vv ioRq, .const 40]) (qr + 5) _ (by decide)
      (by simp [sev, vv]; rw [show (40#64 : BitVec 64) = BitVec.ofNat 64 (8 * 5) from rfl, ecell_add]; rfl) hrrhs ?_
    have hokX := ctxOK_H hok H5
    refine specR_callKH (C := ctxH C H5) ioBd fRb rbParams
      [vv iC, vv ioRc, vv ioLp, vv ioRh, .op .add [vv ioRp, vv ioNf], vv iU] Brb
      [Enc.idxW c, Enc.idxW rl.ctor, wl, Enc.idxW rl.rhs, BitVec.ofNat 64 (rP + rl.nfields), Enc.idxW us]
      (by decide) rfl (by decide) hc.rb
      ⟨by simp +decide [Env.get, ioParams, ctxEnv], by simp, by simp, by simp,
        by simp +decide [sev, Env.get, ioParams, ctxEnv, BitVec.ofNat_add_ofNat], by simp +decide [Env.get, ioParams, ctxEnv],
        trivial⟩
      (hRb H5 s5 wl rl (rP + rl.nfields) hpX hlps) (fun body s7 H7 hp7 => ?_)
    have hpX7 : C.H <+: H7 := hpX.trans hp7
    have hok7 := ctxOK_H hok H7
    set pp := if rP < mI + 1 then rP else mI + 1 with hpp
    set qq := if cnP < margs.length then cnP else margs.length with hqq
    refine specR_assignI ioT1 _ (if BitVec.ofNat 64 rP < BitVec.ofNat 64 (mI + 1) then 1#64 else 0#64) (by decide)
      (by simp +decide [sev, Env.get, ioParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) ?_
    refine specR_assignI ioP _ (BitVec.ofNat 64 pp) (by decide)
      (by simp +decide [sev, Env.get, ioParams, ctxEnv]; exact min_word rP (mI + 1) (by omega) (by omega)) ?_
    refine specR_assignI ioT2 _ (if BitVec.ofNat 64 cnP < BitVec.ofNat 64 margs.length then 1#64 else 0#64)
      (by decide) (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) ?_
    refine specR_assignI ioQq _ (BitVec.ofNat 64 qq) (by decide)
      (by simp [sev]; exact min_word cnP margs.length (by omega) (by omega)) ?_
    have hpl : pp ≤ sargs.length := by rw [hpp]; split <;> omega
    have hql : qq ≤ margs.length := by rw [hqq]; split <;> omega
    refine specR_callPG (C := ctxH C H7) ioV fIv ivParams [vv iA, vv ioP, vv ioMa, vv ioQq] (ivBody C)
      [cellA C oa, BitVec.ofNat 64 pp, cellA C om, BitVec.ofNat 64 qq]
      ((sargs.take pp ++ margs.drop qq).map Enc.idxW) (by decide) rfl (by decide) hc.iv
      ⟨by simp +decide [Env.get, ioParams, ctxEnv], by simp, by simp, by simp, trivial⟩
      (iv_spec (ctxH C H7) hok7 sargs margs oa om pp qq (blkAt_mono hba hpX7)
        (blkAt_mono hbm (hpXm.trans hp7)) hpl hql s7) (fun H8 ov hp8 hbv => ?_)
    have hok8 := ctxOK_H hok H8
    refine UD.specR_heapLoadI' (C := ctxH C H8) ioVl (vv ioV) ov _ hbv.1 (by decide) (by simp; rfl) ?_
    refine specR_atEntry fun t8 ht8 => ?_
    have hvsz := blk_small0 hok8 ht8.sr hbv
    simp only [List.length_map] at hvsz
    have hvals : iotaVals (List.take (mI + 1) sargs).toArray pp margs.toArray qq =
        (sargs.take pp ++ margs.drop qq).toArray := by
      rw [iotaVals_eq]
      simp only [List.toList_toArray, List.take_take]
      rw [show min pp (mI + 1) = pp by rw [hpp]; split <;> omega]
    have hlen1 : (List.take (mI + 1) sargs).length = mI + 1 := by simp; omega
    simp only [hlen1, ← hpp, ← hqq, hvals]
    refine ILP.callE_spec (C := ctxH C H8) ioX ExQ.fIrr ExQ.irrParams
      [vv ioV, .const 0, vv ioVl, .const (BitVec.ofNat 64 coreWalkFuel), vv ioBd, .const 0] (ExQ.irrBody C)
      [cellA C ov, BitVec.ofNat 64 0, BitVec.ofNat 64 (sargs.take pp ++ margs.drop qq).toArray.size,
        BitVec.ofNat 64 coreWalkFuel, Enc.idxW body, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.irr
      ⟨by simp; rfl, rfl, by simp, rfl, by simp, rfl, trivial⟩
      (ExQ.ilFast_spec ra (ctxH C H8) hok8 (codesQ_H hc.q H8) _ ov hbv (by simp; omega) s7 coreWalkFuel 0 body
        CV.coreWalkFuel_lt (by decide)) (fun x s9 => ?_)
    exact specR_returnI _ (optW (some x)) (by simp [sev, vv, optWG])
      (fun t ht => ⟨H8, hpX7.trans hp8, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · simp only [ioFam, ite_true]
    refine specR_callNIH (C := ctxH C H5) ioF fFam fmParams
      [vv kFu, vv kD, vv iC, vv iU, vv iQ, vv iA, vv iK, vv ioUj, vv ioQj, vv ioRq, vv ioMa] Bfm
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c, Enc.idxW us, ecell C q, cellA C oa, BitVec.ofNat 64 (mI + 1),
        Enc.idxW usj, ecell C qj, ecell C qr, cellA C om] (by decide) rfl (by decide) hc.fm
      ⟨by simp +decide [Env.get, ioParams, ctxEnv], by simp +decide [Env.get, ioParams, ctxEnv],
        by simp +decide [Env.get, ioParams, ctxEnv], by simp +decide [Env.get, ioParams, ctxEnv],
        by simp +decide [Env.get, ioParams, ctxEnv], by simp +decide [Env.get, ioParams, ctxEnv],
        by simp +decide [Env.get, ioParams, ctxEnv], by simp, by simp, by simp, by simp, trivial⟩
      (Knot.PostB (ctxH C H5)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fmParams _ rfl hlk)
        (hFam hv H5 s5 usj qj cvj cnP nF ind qr rl om margs hp15 hcij hrule hbm))
      (fun b w s6 H6 hp6 hw => ?_)
    subst hw
    cases b
    · refine specR_ifI _ 1 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      simp only [Bool.false_eq_true, ite_false]
      exact hret0 (hp15.trans hp6)
    refine specR_ifI _ 0 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    simp only [ite_true]
    have hpXm : H5 <+: H6 := hp6
    have hpX : C.H <+: H6 := hp15.trans hp6
    refine specR_envLoadI (C := ctxH C H6) ioLp (.op .add [vv iQ, .const 16]) (q + 2) wl (by decide)
      (by simp +decide [sev, Env.get, ioParams, ctxEnv]; exact UD.ecell_add16 C q)
      (by rw [show q + 2 = q + 1 + 1 by omega]; exact hwl) ?_
    refine specR_envLoadI (C := ctxH C H6) ioRc (vv ioRq) qr _ (by decide) (by simp; rfl) hrct ?_
    refine specR_envLoadI (C := ctxH C H6) ioRh (.op .add [vv ioRq, .const 40]) (qr + 5) _ (by decide)
      (by simp [sev, vv]; rw [show (40#64 : BitVec 64) = BitVec.ofNat 64 (8 * 5) from rfl, ecell_add]; rfl) hrrhs ?_
    have hokX := ctxOK_H hok H6
    refine specR_callKH (C := ctxH C H6) ioBd fRb rbParams
      [vv iC, vv ioRc, vv ioLp, vv ioRh, .op .add [vv ioRp, vv ioNf], vv iU] Brb
      [Enc.idxW c, Enc.idxW rl.ctor, wl, Enc.idxW rl.rhs, BitVec.ofNat 64 (rP + rl.nfields), Enc.idxW us]
      (by decide) rfl (by decide) hc.rb
      ⟨by simp +decide [Env.get, ioParams, ctxEnv], by simp, by simp, by simp,
        by simp +decide [sev, Env.get, ioParams, ctxEnv, BitVec.ofNat_add_ofNat], by simp +decide [Env.get, ioParams, ctxEnv],
        trivial⟩
      (hRb H6 s6 wl rl (rP + rl.nfields) hpX hlps) (fun body s7 H7 hp7 => ?_)
    have hpX7 : C.H <+: H7 := hpX.trans hp7
    have hok7 := ctxOK_H hok H7
    set pp := if rP < mI + 1 then rP else mI + 1 with hpp
    set qq := if cnP < margs.length then cnP else margs.length with hqq
    refine specR_assignI ioT1 _ (if BitVec.ofNat 64 rP < BitVec.ofNat 64 (mI + 1) then 1#64 else 0#64) (by decide)
      (by simp +decide [sev, Env.get, ioParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) ?_
    refine specR_assignI ioP _ (BitVec.ofNat 64 pp) (by decide)
      (by simp +decide [sev, Env.get, ioParams, ctxEnv]; exact min_word rP (mI + 1) (by omega) (by omega)) ?_
    refine specR_assignI ioT2 _ (if BitVec.ofNat 64 cnP < BitVec.ofNat 64 margs.length then 1#64 else 0#64)
      (by decide) (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) ?_
    refine specR_assignI ioQq _ (BitVec.ofNat 64 qq) (by decide)
      (by simp [sev]; exact min_word cnP margs.length (by omega) (by omega)) ?_
    have hpl : pp ≤ sargs.length := by rw [hpp]; split <;> omega
    have hql : qq ≤ margs.length := by rw [hqq]; split <;> omega
    refine specR_callPG (C := ctxH C H7) ioV fIv ivParams [vv iA, vv ioP, vv ioMa, vv ioQq] (ivBody C)
      [cellA C oa, BitVec.ofNat 64 pp, cellA C om, BitVec.ofNat 64 qq]
      ((sargs.take pp ++ margs.drop qq).map Enc.idxW) (by decide) rfl (by decide) hc.iv
      ⟨by simp +decide [Env.get, ioParams, ctxEnv], by simp, by simp, by simp, trivial⟩
      (iv_spec (ctxH C H7) hok7 sargs margs oa om pp qq (blkAt_mono hba hpX7)
        (blkAt_mono hbm (hpXm.trans hp7)) hpl hql s7) (fun H8 ov hp8 hbv => ?_)
    have hok8 := ctxOK_H hok H8
    refine UD.specR_heapLoadI' (C := ctxH C H8) ioVl (vv ioV) ov _ hbv.1 (by decide) (by simp; rfl) ?_
    refine specR_atEntry fun t8 ht8 => ?_
    have hvsz := blk_small0 hok8 ht8.sr hbv
    simp only [List.length_map] at hvsz
    have hvals : iotaVals (List.take (mI + 1) sargs).toArray pp margs.toArray qq =
        (sargs.take pp ++ margs.drop qq).toArray := by
      rw [iotaVals_eq]
      simp only [List.toList_toArray, List.take_take]
      rw [show min pp (mI + 1) = pp by rw [hpp]; split <;> omega]
    have hlen1 : (List.take (mI + 1) sargs).length = mI + 1 := by simp; omega
    simp only [hlen1, ← hpp, ← hqq, hvals]
    refine ILP.callE_spec (C := ctxH C H8) ioX ExQ.fIrr ExQ.irrParams
      [vv ioV, .const 0, vv ioVl, .const (BitVec.ofNat 64 coreWalkFuel), vv ioBd, .const 0] (ExQ.irrBody C)
      [cellA C ov, BitVec.ofNat 64 0, BitVec.ofNat 64 (sargs.take pp ++ margs.drop qq).toArray.size,
        BitVec.ofNat 64 coreWalkFuel, Enc.idxW body, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.irr
      ⟨by simp; rfl, rfl, by simp, rfl, by simp, rfl, trivial⟩
      (ExQ.ilFast_spec ra (ctxH C H8) hok8 (codesQ_H hc.q H8) _ ov hbv (by simp; omega) s7 coreWalkFuel 0 body
        CV.coreWalkFuel_lt (by decide)) (fun x s9 => ?_)
    exact specR_returnI _ (optW (some x)) (by simp [sev, vv, optWG])
      (fun t ht => ⟨H8, hpX7.trans hp8, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
