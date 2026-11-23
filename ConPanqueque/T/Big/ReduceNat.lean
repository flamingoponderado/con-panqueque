import ConPanqueque.T.Big.RawNat
import ConPanqueque.T.Ex.StripPis
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `reduceNat`: the leaf of a binary operation

`rdLeaf fn`: `whnf a`, its literal as a block (`rawNat`); `whnf b`, likewise; then the operation's function on the
two blocks. Either `rawNat` answering `none` returns `none`. `whnf` is the knot's entry, given as a callee for
every heap extension and every state of a family `Q` closed under `whnf` runs.
-/

namespace ConPanqueque.T.Big

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot
open ConPanqueque.V.Enc

def zF := ofString "rdf"
def zB := ofString "rdb"
def zG := ofString "rdg"
def zA := ofString "rda"
def zC := ofString "rdc"
def zU := ofString "rdu"
def zE := ofString "rde"
def zN := ofString "rdn"
def zL := ofString "rdl"
def zP := ofString "rdp"
def zW := ofString "rdw"
def zX := ofString "rdx"
def zY := ofString "rdy"
def zR := ofString "rdr"
def zO := ofString "rdo"
def zP2 := ofString "rdp2"
def fNbAdd := ofString "nbAdd"

@[simp] theorem rd_zF_ne_zB : zF ≠ zB := by decide
@[simp] theorem rd_zF_ne_zG : zF ≠ zG := by decide
@[simp] theorem rd_zF_ne_zA : zF ≠ zA := by decide
@[simp] theorem rd_zF_ne_zC : zF ≠ zC := by decide
@[simp] theorem rd_zF_ne_zU : zF ≠ zU := by decide
@[simp] theorem rd_zF_ne_zE : zF ≠ zE := by decide
@[simp] theorem rd_zF_ne_zN : zF ≠ zN := by decide
@[simp] theorem rd_zF_ne_zL : zF ≠ zL := by decide
@[simp] theorem rd_zF_ne_zP : zF ≠ zP := by decide
@[simp] theorem rd_zF_ne_zW : zF ≠ zW := by decide
@[simp] theorem rd_zF_ne_zX : zF ≠ zX := by decide
@[simp] theorem rd_zF_ne_zY : zF ≠ zY := by decide
@[simp] theorem rd_zF_ne_zR : zF ≠ zR := by decide
@[simp] theorem rd_zF_ne_zO : zF ≠ zO := by decide
@[simp] theorem rd_zF_ne_lFl : zF ≠ lFl := by decide
@[simp] theorem rd_lFl_ne_zF : lFl ≠ zF := by decide
@[simp] theorem rd_zF_ne_lDh : zF ≠ lDh := by decide
@[simp] theorem rd_lDh_ne_zF : lDh ≠ zF := by decide
@[simp] theorem rd_zF_ne_lDt : zF ≠ lDt := by decide
@[simp] theorem rd_lDt_ne_zF : lDt ≠ zF := by decide
@[simp] theorem rd_zF_ne_lDg : zF ≠ lDg := by decide
@[simp] theorem rd_lDg_ne_zF : lDg ≠ zF := by decide
@[simp] theorem rd_zF_ne_lDi : zF ≠ lDi := by decide
@[simp] theorem rd_lDi_ne_zF : lDi ≠ zF := by decide
@[simp] theorem rd_zF_ne_lRp : zF ≠ lRp := by decide
@[simp] theorem rd_lRp_ne_zF : lRp ≠ zF := by decide
@[simp] theorem rd_zF_ne_lRn : zF ≠ lRn := by decide
@[simp] theorem rd_lRn_ne_zF : lRn ≠ zF := by decide
@[simp] theorem rd_zF_ne_kFu : zF ≠ kFu := by decide
@[simp] theorem rd_kFu_ne_zF : kFu ≠ zF := by decide
@[simp] theorem rd_zF_ne_kD : zF ≠ kD := by decide
@[simp] theorem rd_kD_ne_zF : kD ≠ zF := by decide
@[simp] theorem rd_zF_ne_kE : zF ≠ kE := by decide
@[simp] theorem rd_kE_ne_zF : kE ≠ zF := by decide
@[simp] theorem rd_zF_ne_lFle : zF ≠ lFle := by decide
@[simp] theorem rd_lFle_ne_zF : lFle ≠ zF := by decide
@[simp] theorem rd_zF_ne_lDir : zF ≠ lDir := by decide
@[simp] theorem rd_lDir_ne_zF : lDir ≠ zF := by decide
@[simp] theorem rd_zF_ne_lKb : zF ≠ lKb := by decide
@[simp] theorem rd_lKb_ne_zF : lKb ≠ zF := by decide
@[simp] theorem rd_zF_ne_qH : zF ≠ qH := by decide
@[simp] theorem rd_qH_ne_zF : qH ≠ zF := by decide
@[simp] theorem rd_zF_ne_nX : zF ≠ nX := by decide
@[simp] theorem rd_nX_ne_zF : nX ≠ zF := by decide
@[simp] theorem rd_zF_ne_nY : zF ≠ nY := by decide
@[simp] theorem rd_nY_ne_zF : nY ≠ zF := by decide
@[simp] theorem rd_zF_ne_rZ : zF ≠ rZ := by decide
@[simp] theorem rd_rZ_ne_zF : rZ ≠ zF := by decide
@[simp] theorem rd_zB_ne_zF : zB ≠ zF := by decide
@[simp] theorem rd_zB_ne_zG : zB ≠ zG := by decide
@[simp] theorem rd_zB_ne_zA : zB ≠ zA := by decide
@[simp] theorem rd_zB_ne_zC : zB ≠ zC := by decide
@[simp] theorem rd_zB_ne_zU : zB ≠ zU := by decide
@[simp] theorem rd_zB_ne_zE : zB ≠ zE := by decide
@[simp] theorem rd_zB_ne_zN : zB ≠ zN := by decide
@[simp] theorem rd_zB_ne_zL : zB ≠ zL := by decide
@[simp] theorem rd_zB_ne_zP : zB ≠ zP := by decide
@[simp] theorem rd_zB_ne_zW : zB ≠ zW := by decide
@[simp] theorem rd_zB_ne_zX : zB ≠ zX := by decide
@[simp] theorem rd_zB_ne_zY : zB ≠ zY := by decide
@[simp] theorem rd_zB_ne_zR : zB ≠ zR := by decide
@[simp] theorem rd_zB_ne_zO : zB ≠ zO := by decide
@[simp] theorem rd_zB_ne_lFl : zB ≠ lFl := by decide
@[simp] theorem rd_lFl_ne_zB : lFl ≠ zB := by decide
@[simp] theorem rd_zB_ne_lDh : zB ≠ lDh := by decide
@[simp] theorem rd_lDh_ne_zB : lDh ≠ zB := by decide
@[simp] theorem rd_zB_ne_lDt : zB ≠ lDt := by decide
@[simp] theorem rd_lDt_ne_zB : lDt ≠ zB := by decide
@[simp] theorem rd_zB_ne_lDg : zB ≠ lDg := by decide
@[simp] theorem rd_lDg_ne_zB : lDg ≠ zB := by decide
@[simp] theorem rd_zB_ne_lDi : zB ≠ lDi := by decide
@[simp] theorem rd_lDi_ne_zB : lDi ≠ zB := by decide
@[simp] theorem rd_zB_ne_lRp : zB ≠ lRp := by decide
@[simp] theorem rd_lRp_ne_zB : lRp ≠ zB := by decide
@[simp] theorem rd_zB_ne_lRn : zB ≠ lRn := by decide
@[simp] theorem rd_lRn_ne_zB : lRn ≠ zB := by decide
@[simp] theorem rd_zB_ne_kFu : zB ≠ kFu := by decide
@[simp] theorem rd_kFu_ne_zB : kFu ≠ zB := by decide
@[simp] theorem rd_zB_ne_kD : zB ≠ kD := by decide
@[simp] theorem rd_kD_ne_zB : kD ≠ zB := by decide
@[simp] theorem rd_zB_ne_kE : zB ≠ kE := by decide
@[simp] theorem rd_kE_ne_zB : kE ≠ zB := by decide
@[simp] theorem rd_zB_ne_lFle : zB ≠ lFle := by decide
@[simp] theorem rd_lFle_ne_zB : lFle ≠ zB := by decide
@[simp] theorem rd_zB_ne_lDir : zB ≠ lDir := by decide
@[simp] theorem rd_lDir_ne_zB : lDir ≠ zB := by decide
@[simp] theorem rd_zB_ne_lKb : zB ≠ lKb := by decide
@[simp] theorem rd_lKb_ne_zB : lKb ≠ zB := by decide
@[simp] theorem rd_zB_ne_qH : zB ≠ qH := by decide
@[simp] theorem rd_qH_ne_zB : qH ≠ zB := by decide
@[simp] theorem rd_zB_ne_nX : zB ≠ nX := by decide
@[simp] theorem rd_nX_ne_zB : nX ≠ zB := by decide
@[simp] theorem rd_zB_ne_nY : zB ≠ nY := by decide
@[simp] theorem rd_nY_ne_zB : nY ≠ zB := by decide
@[simp] theorem rd_zB_ne_rZ : zB ≠ rZ := by decide
@[simp] theorem rd_rZ_ne_zB : rZ ≠ zB := by decide
@[simp] theorem rd_zG_ne_zF : zG ≠ zF := by decide
@[simp] theorem rd_zG_ne_zB : zG ≠ zB := by decide
@[simp] theorem rd_zG_ne_zA : zG ≠ zA := by decide
@[simp] theorem rd_zG_ne_zC : zG ≠ zC := by decide
@[simp] theorem rd_zG_ne_zU : zG ≠ zU := by decide
@[simp] theorem rd_zG_ne_zE : zG ≠ zE := by decide
@[simp] theorem rd_zG_ne_zN : zG ≠ zN := by decide
@[simp] theorem rd_zG_ne_zL : zG ≠ zL := by decide
@[simp] theorem rd_zG_ne_zP : zG ≠ zP := by decide
@[simp] theorem rd_zG_ne_zW : zG ≠ zW := by decide
@[simp] theorem rd_zG_ne_zX : zG ≠ zX := by decide
@[simp] theorem rd_zG_ne_zY : zG ≠ zY := by decide
@[simp] theorem rd_zG_ne_zR : zG ≠ zR := by decide
@[simp] theorem rd_zG_ne_zO : zG ≠ zO := by decide
@[simp] theorem rd_zG_ne_lFl : zG ≠ lFl := by decide
@[simp] theorem rd_lFl_ne_zG : lFl ≠ zG := by decide
@[simp] theorem rd_zG_ne_lDh : zG ≠ lDh := by decide
@[simp] theorem rd_lDh_ne_zG : lDh ≠ zG := by decide
@[simp] theorem rd_zG_ne_lDt : zG ≠ lDt := by decide
@[simp] theorem rd_lDt_ne_zG : lDt ≠ zG := by decide
@[simp] theorem rd_zG_ne_lDg : zG ≠ lDg := by decide
@[simp] theorem rd_lDg_ne_zG : lDg ≠ zG := by decide
@[simp] theorem rd_zG_ne_lDi : zG ≠ lDi := by decide
@[simp] theorem rd_lDi_ne_zG : lDi ≠ zG := by decide
@[simp] theorem rd_zG_ne_lRp : zG ≠ lRp := by decide
@[simp] theorem rd_lRp_ne_zG : lRp ≠ zG := by decide
@[simp] theorem rd_zG_ne_lRn : zG ≠ lRn := by decide
@[simp] theorem rd_lRn_ne_zG : lRn ≠ zG := by decide
@[simp] theorem rd_zG_ne_kFu : zG ≠ kFu := by decide
@[simp] theorem rd_kFu_ne_zG : kFu ≠ zG := by decide
@[simp] theorem rd_zG_ne_kD : zG ≠ kD := by decide
@[simp] theorem rd_kD_ne_zG : kD ≠ zG := by decide
@[simp] theorem rd_zG_ne_kE : zG ≠ kE := by decide
@[simp] theorem rd_kE_ne_zG : kE ≠ zG := by decide
@[simp] theorem rd_zG_ne_lFle : zG ≠ lFle := by decide
@[simp] theorem rd_lFle_ne_zG : lFle ≠ zG := by decide
@[simp] theorem rd_zG_ne_lDir : zG ≠ lDir := by decide
@[simp] theorem rd_lDir_ne_zG : lDir ≠ zG := by decide
@[simp] theorem rd_zG_ne_lKb : zG ≠ lKb := by decide
@[simp] theorem rd_lKb_ne_zG : lKb ≠ zG := by decide
@[simp] theorem rd_zG_ne_qH : zG ≠ qH := by decide
@[simp] theorem rd_qH_ne_zG : qH ≠ zG := by decide
@[simp] theorem rd_zG_ne_nX : zG ≠ nX := by decide
@[simp] theorem rd_nX_ne_zG : nX ≠ zG := by decide
@[simp] theorem rd_zG_ne_nY : zG ≠ nY := by decide
@[simp] theorem rd_nY_ne_zG : nY ≠ zG := by decide
@[simp] theorem rd_zG_ne_rZ : zG ≠ rZ := by decide
@[simp] theorem rd_rZ_ne_zG : rZ ≠ zG := by decide
@[simp] theorem rd_zA_ne_zF : zA ≠ zF := by decide
@[simp] theorem rd_zA_ne_zB : zA ≠ zB := by decide
@[simp] theorem rd_zA_ne_zG : zA ≠ zG := by decide
@[simp] theorem rd_zA_ne_zC : zA ≠ zC := by decide
@[simp] theorem rd_zA_ne_zU : zA ≠ zU := by decide
@[simp] theorem rd_zA_ne_zE : zA ≠ zE := by decide
@[simp] theorem rd_zA_ne_zN : zA ≠ zN := by decide
@[simp] theorem rd_zA_ne_zL : zA ≠ zL := by decide
@[simp] theorem rd_zA_ne_zP : zA ≠ zP := by decide
@[simp] theorem rd_zA_ne_zW : zA ≠ zW := by decide
@[simp] theorem rd_zA_ne_zX : zA ≠ zX := by decide
@[simp] theorem rd_zA_ne_zY : zA ≠ zY := by decide
@[simp] theorem rd_zA_ne_zR : zA ≠ zR := by decide
@[simp] theorem rd_zA_ne_zO : zA ≠ zO := by decide
@[simp] theorem rd_zA_ne_lFl : zA ≠ lFl := by decide
@[simp] theorem rd_lFl_ne_zA : lFl ≠ zA := by decide
@[simp] theorem rd_zA_ne_lDh : zA ≠ lDh := by decide
@[simp] theorem rd_lDh_ne_zA : lDh ≠ zA := by decide
@[simp] theorem rd_zA_ne_lDt : zA ≠ lDt := by decide
@[simp] theorem rd_lDt_ne_zA : lDt ≠ zA := by decide
@[simp] theorem rd_zA_ne_lDg : zA ≠ lDg := by decide
@[simp] theorem rd_lDg_ne_zA : lDg ≠ zA := by decide
@[simp] theorem rd_zA_ne_lDi : zA ≠ lDi := by decide
@[simp] theorem rd_lDi_ne_zA : lDi ≠ zA := by decide
@[simp] theorem rd_zA_ne_lRp : zA ≠ lRp := by decide
@[simp] theorem rd_lRp_ne_zA : lRp ≠ zA := by decide
@[simp] theorem rd_zA_ne_lRn : zA ≠ lRn := by decide
@[simp] theorem rd_lRn_ne_zA : lRn ≠ zA := by decide
@[simp] theorem rd_zA_ne_kFu : zA ≠ kFu := by decide
@[simp] theorem rd_kFu_ne_zA : kFu ≠ zA := by decide
@[simp] theorem rd_zA_ne_kD : zA ≠ kD := by decide
@[simp] theorem rd_kD_ne_zA : kD ≠ zA := by decide
@[simp] theorem rd_zA_ne_kE : zA ≠ kE := by decide
@[simp] theorem rd_kE_ne_zA : kE ≠ zA := by decide
@[simp] theorem rd_zA_ne_lFle : zA ≠ lFle := by decide
@[simp] theorem rd_lFle_ne_zA : lFle ≠ zA := by decide
@[simp] theorem rd_zA_ne_lDir : zA ≠ lDir := by decide
@[simp] theorem rd_lDir_ne_zA : lDir ≠ zA := by decide
@[simp] theorem rd_zA_ne_lKb : zA ≠ lKb := by decide
@[simp] theorem rd_lKb_ne_zA : lKb ≠ zA := by decide
@[simp] theorem rd_zA_ne_qH : zA ≠ qH := by decide
@[simp] theorem rd_qH_ne_zA : qH ≠ zA := by decide
@[simp] theorem rd_zA_ne_nX : zA ≠ nX := by decide
@[simp] theorem rd_nX_ne_zA : nX ≠ zA := by decide
@[simp] theorem rd_zA_ne_nY : zA ≠ nY := by decide
@[simp] theorem rd_nY_ne_zA : nY ≠ zA := by decide
@[simp] theorem rd_zA_ne_rZ : zA ≠ rZ := by decide
@[simp] theorem rd_rZ_ne_zA : rZ ≠ zA := by decide
@[simp] theorem rd_zC_ne_zF : zC ≠ zF := by decide
@[simp] theorem rd_zC_ne_zB : zC ≠ zB := by decide
@[simp] theorem rd_zC_ne_zG : zC ≠ zG := by decide
@[simp] theorem rd_zC_ne_zA : zC ≠ zA := by decide
@[simp] theorem rd_zC_ne_zU : zC ≠ zU := by decide
@[simp] theorem rd_zC_ne_zE : zC ≠ zE := by decide
@[simp] theorem rd_zC_ne_zN : zC ≠ zN := by decide
@[simp] theorem rd_zC_ne_zL : zC ≠ zL := by decide
@[simp] theorem rd_zC_ne_zP : zC ≠ zP := by decide
@[simp] theorem rd_zC_ne_zW : zC ≠ zW := by decide
@[simp] theorem rd_zC_ne_zX : zC ≠ zX := by decide
@[simp] theorem rd_zC_ne_zY : zC ≠ zY := by decide
@[simp] theorem rd_zC_ne_zR : zC ≠ zR := by decide
@[simp] theorem rd_zC_ne_zO : zC ≠ zO := by decide
@[simp] theorem rd_zC_ne_lFl : zC ≠ lFl := by decide
@[simp] theorem rd_lFl_ne_zC : lFl ≠ zC := by decide
@[simp] theorem rd_zC_ne_lDh : zC ≠ lDh := by decide
@[simp] theorem rd_lDh_ne_zC : lDh ≠ zC := by decide
@[simp] theorem rd_zC_ne_lDt : zC ≠ lDt := by decide
@[simp] theorem rd_lDt_ne_zC : lDt ≠ zC := by decide
@[simp] theorem rd_zC_ne_lDg : zC ≠ lDg := by decide
@[simp] theorem rd_lDg_ne_zC : lDg ≠ zC := by decide
@[simp] theorem rd_zC_ne_lDi : zC ≠ lDi := by decide
@[simp] theorem rd_lDi_ne_zC : lDi ≠ zC := by decide
@[simp] theorem rd_zC_ne_lRp : zC ≠ lRp := by decide
@[simp] theorem rd_lRp_ne_zC : lRp ≠ zC := by decide
@[simp] theorem rd_zC_ne_lRn : zC ≠ lRn := by decide
@[simp] theorem rd_lRn_ne_zC : lRn ≠ zC := by decide
@[simp] theorem rd_zC_ne_kFu : zC ≠ kFu := by decide
@[simp] theorem rd_kFu_ne_zC : kFu ≠ zC := by decide
@[simp] theorem rd_zC_ne_kD : zC ≠ kD := by decide
@[simp] theorem rd_kD_ne_zC : kD ≠ zC := by decide
@[simp] theorem rd_zC_ne_kE : zC ≠ kE := by decide
@[simp] theorem rd_kE_ne_zC : kE ≠ zC := by decide
@[simp] theorem rd_zC_ne_lFle : zC ≠ lFle := by decide
@[simp] theorem rd_lFle_ne_zC : lFle ≠ zC := by decide
@[simp] theorem rd_zC_ne_lDir : zC ≠ lDir := by decide
@[simp] theorem rd_lDir_ne_zC : lDir ≠ zC := by decide
@[simp] theorem rd_zC_ne_lKb : zC ≠ lKb := by decide
@[simp] theorem rd_lKb_ne_zC : lKb ≠ zC := by decide
@[simp] theorem rd_zC_ne_qH : zC ≠ qH := by decide
@[simp] theorem rd_qH_ne_zC : qH ≠ zC := by decide
@[simp] theorem rd_zC_ne_nX : zC ≠ nX := by decide
@[simp] theorem rd_nX_ne_zC : nX ≠ zC := by decide
@[simp] theorem rd_zC_ne_nY : zC ≠ nY := by decide
@[simp] theorem rd_nY_ne_zC : nY ≠ zC := by decide
@[simp] theorem rd_zC_ne_rZ : zC ≠ rZ := by decide
@[simp] theorem rd_rZ_ne_zC : rZ ≠ zC := by decide
@[simp] theorem rd_zU_ne_zF : zU ≠ zF := by decide
@[simp] theorem rd_zU_ne_zB : zU ≠ zB := by decide
@[simp] theorem rd_zU_ne_zG : zU ≠ zG := by decide
@[simp] theorem rd_zU_ne_zA : zU ≠ zA := by decide
@[simp] theorem rd_zU_ne_zC : zU ≠ zC := by decide
@[simp] theorem rd_zU_ne_zE : zU ≠ zE := by decide
@[simp] theorem rd_zU_ne_zN : zU ≠ zN := by decide
@[simp] theorem rd_zU_ne_zL : zU ≠ zL := by decide
@[simp] theorem rd_zU_ne_zP : zU ≠ zP := by decide
@[simp] theorem rd_zU_ne_zW : zU ≠ zW := by decide
@[simp] theorem rd_zU_ne_zX : zU ≠ zX := by decide
@[simp] theorem rd_zU_ne_zY : zU ≠ zY := by decide
@[simp] theorem rd_zU_ne_zR : zU ≠ zR := by decide
@[simp] theorem rd_zU_ne_zO : zU ≠ zO := by decide
@[simp] theorem rd_zU_ne_lFl : zU ≠ lFl := by decide
@[simp] theorem rd_lFl_ne_zU : lFl ≠ zU := by decide
@[simp] theorem rd_zU_ne_lDh : zU ≠ lDh := by decide
@[simp] theorem rd_lDh_ne_zU : lDh ≠ zU := by decide
@[simp] theorem rd_zU_ne_lDt : zU ≠ lDt := by decide
@[simp] theorem rd_lDt_ne_zU : lDt ≠ zU := by decide
@[simp] theorem rd_zU_ne_lDg : zU ≠ lDg := by decide
@[simp] theorem rd_lDg_ne_zU : lDg ≠ zU := by decide
@[simp] theorem rd_zU_ne_lDi : zU ≠ lDi := by decide
@[simp] theorem rd_lDi_ne_zU : lDi ≠ zU := by decide
@[simp] theorem rd_zU_ne_lRp : zU ≠ lRp := by decide
@[simp] theorem rd_lRp_ne_zU : lRp ≠ zU := by decide
@[simp] theorem rd_zU_ne_lRn : zU ≠ lRn := by decide
@[simp] theorem rd_lRn_ne_zU : lRn ≠ zU := by decide
@[simp] theorem rd_zU_ne_kFu : zU ≠ kFu := by decide
@[simp] theorem rd_kFu_ne_zU : kFu ≠ zU := by decide
@[simp] theorem rd_zU_ne_kD : zU ≠ kD := by decide
@[simp] theorem rd_kD_ne_zU : kD ≠ zU := by decide
@[simp] theorem rd_zU_ne_kE : zU ≠ kE := by decide
@[simp] theorem rd_kE_ne_zU : kE ≠ zU := by decide
@[simp] theorem rd_zU_ne_lFle : zU ≠ lFle := by decide
@[simp] theorem rd_lFle_ne_zU : lFle ≠ zU := by decide
@[simp] theorem rd_zU_ne_lDir : zU ≠ lDir := by decide
@[simp] theorem rd_lDir_ne_zU : lDir ≠ zU := by decide
@[simp] theorem rd_zU_ne_lKb : zU ≠ lKb := by decide
@[simp] theorem rd_lKb_ne_zU : lKb ≠ zU := by decide
@[simp] theorem rd_zU_ne_qH : zU ≠ qH := by decide
@[simp] theorem rd_qH_ne_zU : qH ≠ zU := by decide
@[simp] theorem rd_zU_ne_nX : zU ≠ nX := by decide
@[simp] theorem rd_nX_ne_zU : nX ≠ zU := by decide
@[simp] theorem rd_zU_ne_nY : zU ≠ nY := by decide
@[simp] theorem rd_nY_ne_zU : nY ≠ zU := by decide
@[simp] theorem rd_zU_ne_rZ : zU ≠ rZ := by decide
@[simp] theorem rd_rZ_ne_zU : rZ ≠ zU := by decide
@[simp] theorem rd_zE_ne_zF : zE ≠ zF := by decide
@[simp] theorem rd_zE_ne_zB : zE ≠ zB := by decide
@[simp] theorem rd_zE_ne_zG : zE ≠ zG := by decide
@[simp] theorem rd_zE_ne_zA : zE ≠ zA := by decide
@[simp] theorem rd_zE_ne_zC : zE ≠ zC := by decide
@[simp] theorem rd_zE_ne_zU : zE ≠ zU := by decide
@[simp] theorem rd_zE_ne_zN : zE ≠ zN := by decide
@[simp] theorem rd_zE_ne_zL : zE ≠ zL := by decide
@[simp] theorem rd_zE_ne_zP : zE ≠ zP := by decide
@[simp] theorem rd_zE_ne_zW : zE ≠ zW := by decide
@[simp] theorem rd_zE_ne_zX : zE ≠ zX := by decide
@[simp] theorem rd_zE_ne_zY : zE ≠ zY := by decide
@[simp] theorem rd_zE_ne_zR : zE ≠ zR := by decide
@[simp] theorem rd_zE_ne_zO : zE ≠ zO := by decide
@[simp] theorem rd_zE_ne_lFl : zE ≠ lFl := by decide
@[simp] theorem rd_lFl_ne_zE : lFl ≠ zE := by decide
@[simp] theorem rd_zE_ne_lDh : zE ≠ lDh := by decide
@[simp] theorem rd_lDh_ne_zE : lDh ≠ zE := by decide
@[simp] theorem rd_zE_ne_lDt : zE ≠ lDt := by decide
@[simp] theorem rd_lDt_ne_zE : lDt ≠ zE := by decide
@[simp] theorem rd_zE_ne_lDg : zE ≠ lDg := by decide
@[simp] theorem rd_lDg_ne_zE : lDg ≠ zE := by decide
@[simp] theorem rd_zE_ne_lDi : zE ≠ lDi := by decide
@[simp] theorem rd_lDi_ne_zE : lDi ≠ zE := by decide
@[simp] theorem rd_zE_ne_lRp : zE ≠ lRp := by decide
@[simp] theorem rd_lRp_ne_zE : lRp ≠ zE := by decide
@[simp] theorem rd_zE_ne_lRn : zE ≠ lRn := by decide
@[simp] theorem rd_lRn_ne_zE : lRn ≠ zE := by decide
@[simp] theorem rd_zE_ne_kFu : zE ≠ kFu := by decide
@[simp] theorem rd_kFu_ne_zE : kFu ≠ zE := by decide
@[simp] theorem rd_zE_ne_kD : zE ≠ kD := by decide
@[simp] theorem rd_kD_ne_zE : kD ≠ zE := by decide
@[simp] theorem rd_zE_ne_kE : zE ≠ kE := by decide
@[simp] theorem rd_kE_ne_zE : kE ≠ zE := by decide
@[simp] theorem rd_zE_ne_lFle : zE ≠ lFle := by decide
@[simp] theorem rd_lFle_ne_zE : lFle ≠ zE := by decide
@[simp] theorem rd_zE_ne_lDir : zE ≠ lDir := by decide
@[simp] theorem rd_lDir_ne_zE : lDir ≠ zE := by decide
@[simp] theorem rd_zE_ne_lKb : zE ≠ lKb := by decide
@[simp] theorem rd_lKb_ne_zE : lKb ≠ zE := by decide
@[simp] theorem rd_zE_ne_qH : zE ≠ qH := by decide
@[simp] theorem rd_qH_ne_zE : qH ≠ zE := by decide
@[simp] theorem rd_zE_ne_nX : zE ≠ nX := by decide
@[simp] theorem rd_nX_ne_zE : nX ≠ zE := by decide
@[simp] theorem rd_zE_ne_nY : zE ≠ nY := by decide
@[simp] theorem rd_nY_ne_zE : nY ≠ zE := by decide
@[simp] theorem rd_zE_ne_rZ : zE ≠ rZ := by decide
@[simp] theorem rd_rZ_ne_zE : rZ ≠ zE := by decide
@[simp] theorem rd_zN_ne_zF : zN ≠ zF := by decide
@[simp] theorem rd_zN_ne_zB : zN ≠ zB := by decide
@[simp] theorem rd_zN_ne_zG : zN ≠ zG := by decide
@[simp] theorem rd_zN_ne_zA : zN ≠ zA := by decide
@[simp] theorem rd_zN_ne_zC : zN ≠ zC := by decide
@[simp] theorem rd_zN_ne_zU : zN ≠ zU := by decide
@[simp] theorem rd_zN_ne_zE : zN ≠ zE := by decide
@[simp] theorem rd_zN_ne_zL : zN ≠ zL := by decide
@[simp] theorem rd_zN_ne_zP : zN ≠ zP := by decide
@[simp] theorem rd_zN_ne_zW : zN ≠ zW := by decide
@[simp] theorem rd_zN_ne_zX : zN ≠ zX := by decide
@[simp] theorem rd_zN_ne_zY : zN ≠ zY := by decide
@[simp] theorem rd_zN_ne_zR : zN ≠ zR := by decide
@[simp] theorem rd_zN_ne_zO : zN ≠ zO := by decide
@[simp] theorem rd_zN_ne_lFl : zN ≠ lFl := by decide
@[simp] theorem rd_lFl_ne_zN : lFl ≠ zN := by decide
@[simp] theorem rd_zN_ne_lDh : zN ≠ lDh := by decide
@[simp] theorem rd_lDh_ne_zN : lDh ≠ zN := by decide
@[simp] theorem rd_zN_ne_lDt : zN ≠ lDt := by decide
@[simp] theorem rd_lDt_ne_zN : lDt ≠ zN := by decide
@[simp] theorem rd_zN_ne_lDg : zN ≠ lDg := by decide
@[simp] theorem rd_lDg_ne_zN : lDg ≠ zN := by decide
@[simp] theorem rd_zN_ne_lDi : zN ≠ lDi := by decide
@[simp] theorem rd_lDi_ne_zN : lDi ≠ zN := by decide
@[simp] theorem rd_zN_ne_lRp : zN ≠ lRp := by decide
@[simp] theorem rd_lRp_ne_zN : lRp ≠ zN := by decide
@[simp] theorem rd_zN_ne_lRn : zN ≠ lRn := by decide
@[simp] theorem rd_lRn_ne_zN : lRn ≠ zN := by decide
@[simp] theorem rd_zN_ne_kFu : zN ≠ kFu := by decide
@[simp] theorem rd_kFu_ne_zN : kFu ≠ zN := by decide
@[simp] theorem rd_zN_ne_kD : zN ≠ kD := by decide
@[simp] theorem rd_kD_ne_zN : kD ≠ zN := by decide
@[simp] theorem rd_zN_ne_kE : zN ≠ kE := by decide
@[simp] theorem rd_kE_ne_zN : kE ≠ zN := by decide
@[simp] theorem rd_zN_ne_lFle : zN ≠ lFle := by decide
@[simp] theorem rd_lFle_ne_zN : lFle ≠ zN := by decide
@[simp] theorem rd_zN_ne_lDir : zN ≠ lDir := by decide
@[simp] theorem rd_lDir_ne_zN : lDir ≠ zN := by decide
@[simp] theorem rd_zN_ne_lKb : zN ≠ lKb := by decide
@[simp] theorem rd_lKb_ne_zN : lKb ≠ zN := by decide
@[simp] theorem rd_zN_ne_qH : zN ≠ qH := by decide
@[simp] theorem rd_qH_ne_zN : qH ≠ zN := by decide
@[simp] theorem rd_zN_ne_nX : zN ≠ nX := by decide
@[simp] theorem rd_nX_ne_zN : nX ≠ zN := by decide
@[simp] theorem rd_zN_ne_nY : zN ≠ nY := by decide
@[simp] theorem rd_nY_ne_zN : nY ≠ zN := by decide
@[simp] theorem rd_zN_ne_rZ : zN ≠ rZ := by decide
@[simp] theorem rd_rZ_ne_zN : rZ ≠ zN := by decide
@[simp] theorem rd_zL_ne_zF : zL ≠ zF := by decide
@[simp] theorem rd_zL_ne_zB : zL ≠ zB := by decide
@[simp] theorem rd_zL_ne_zG : zL ≠ zG := by decide
@[simp] theorem rd_zL_ne_zA : zL ≠ zA := by decide
@[simp] theorem rd_zL_ne_zC : zL ≠ zC := by decide
@[simp] theorem rd_zL_ne_zU : zL ≠ zU := by decide
@[simp] theorem rd_zL_ne_zE : zL ≠ zE := by decide
@[simp] theorem rd_zL_ne_zN : zL ≠ zN := by decide
@[simp] theorem rd_zL_ne_zP : zL ≠ zP := by decide
@[simp] theorem rd_zL_ne_zW : zL ≠ zW := by decide
@[simp] theorem rd_zL_ne_zX : zL ≠ zX := by decide
@[simp] theorem rd_zL_ne_zY : zL ≠ zY := by decide
@[simp] theorem rd_zL_ne_zR : zL ≠ zR := by decide
@[simp] theorem rd_zL_ne_zO : zL ≠ zO := by decide
@[simp] theorem rd_zL_ne_lFl : zL ≠ lFl := by decide
@[simp] theorem rd_lFl_ne_zL : lFl ≠ zL := by decide
@[simp] theorem rd_zL_ne_lDh : zL ≠ lDh := by decide
@[simp] theorem rd_lDh_ne_zL : lDh ≠ zL := by decide
@[simp] theorem rd_zL_ne_lDt : zL ≠ lDt := by decide
@[simp] theorem rd_lDt_ne_zL : lDt ≠ zL := by decide
@[simp] theorem rd_zL_ne_lDg : zL ≠ lDg := by decide
@[simp] theorem rd_lDg_ne_zL : lDg ≠ zL := by decide
@[simp] theorem rd_zL_ne_lDi : zL ≠ lDi := by decide
@[simp] theorem rd_lDi_ne_zL : lDi ≠ zL := by decide
@[simp] theorem rd_zL_ne_lRp : zL ≠ lRp := by decide
@[simp] theorem rd_lRp_ne_zL : lRp ≠ zL := by decide
@[simp] theorem rd_zL_ne_lRn : zL ≠ lRn := by decide
@[simp] theorem rd_lRn_ne_zL : lRn ≠ zL := by decide
@[simp] theorem rd_zL_ne_kFu : zL ≠ kFu := by decide
@[simp] theorem rd_kFu_ne_zL : kFu ≠ zL := by decide
@[simp] theorem rd_zL_ne_kD : zL ≠ kD := by decide
@[simp] theorem rd_kD_ne_zL : kD ≠ zL := by decide
@[simp] theorem rd_zL_ne_kE : zL ≠ kE := by decide
@[simp] theorem rd_kE_ne_zL : kE ≠ zL := by decide
@[simp] theorem rd_zL_ne_lFle : zL ≠ lFle := by decide
@[simp] theorem rd_lFle_ne_zL : lFle ≠ zL := by decide
@[simp] theorem rd_zL_ne_lDir : zL ≠ lDir := by decide
@[simp] theorem rd_lDir_ne_zL : lDir ≠ zL := by decide
@[simp] theorem rd_zL_ne_lKb : zL ≠ lKb := by decide
@[simp] theorem rd_lKb_ne_zL : lKb ≠ zL := by decide
@[simp] theorem rd_zL_ne_qH : zL ≠ qH := by decide
@[simp] theorem rd_qH_ne_zL : qH ≠ zL := by decide
@[simp] theorem rd_zL_ne_nX : zL ≠ nX := by decide
@[simp] theorem rd_nX_ne_zL : nX ≠ zL := by decide
@[simp] theorem rd_zL_ne_nY : zL ≠ nY := by decide
@[simp] theorem rd_nY_ne_zL : nY ≠ zL := by decide
@[simp] theorem rd_zL_ne_rZ : zL ≠ rZ := by decide
@[simp] theorem rd_rZ_ne_zL : rZ ≠ zL := by decide
@[simp] theorem rd_zP_ne_zF : zP ≠ zF := by decide
@[simp] theorem rd_zP_ne_zB : zP ≠ zB := by decide
@[simp] theorem rd_zP_ne_zG : zP ≠ zG := by decide
@[simp] theorem rd_zP_ne_zA : zP ≠ zA := by decide
@[simp] theorem rd_zP_ne_zC : zP ≠ zC := by decide
@[simp] theorem rd_zP_ne_zU : zP ≠ zU := by decide
@[simp] theorem rd_zP_ne_zE : zP ≠ zE := by decide
@[simp] theorem rd_zP_ne_zN : zP ≠ zN := by decide
@[simp] theorem rd_zP_ne_zL : zP ≠ zL := by decide
@[simp] theorem rd_zP_ne_zW : zP ≠ zW := by decide
@[simp] theorem rd_zP_ne_zX : zP ≠ zX := by decide
@[simp] theorem rd_zP_ne_zY : zP ≠ zY := by decide
@[simp] theorem rd_zP_ne_zR : zP ≠ zR := by decide
@[simp] theorem rd_zP_ne_zO : zP ≠ zO := by decide
@[simp] theorem rd_zP_ne_lFl : zP ≠ lFl := by decide
@[simp] theorem rd_lFl_ne_zP : lFl ≠ zP := by decide
@[simp] theorem rd_zP_ne_lDh : zP ≠ lDh := by decide
@[simp] theorem rd_lDh_ne_zP : lDh ≠ zP := by decide
@[simp] theorem rd_zP_ne_lDt : zP ≠ lDt := by decide
@[simp] theorem rd_lDt_ne_zP : lDt ≠ zP := by decide
@[simp] theorem rd_zP_ne_lDg : zP ≠ lDg := by decide
@[simp] theorem rd_lDg_ne_zP : lDg ≠ zP := by decide
@[simp] theorem rd_zP_ne_lDi : zP ≠ lDi := by decide
@[simp] theorem rd_lDi_ne_zP : lDi ≠ zP := by decide
@[simp] theorem rd_zP_ne_lRp : zP ≠ lRp := by decide
@[simp] theorem rd_lRp_ne_zP : lRp ≠ zP := by decide
@[simp] theorem rd_zP_ne_lRn : zP ≠ lRn := by decide
@[simp] theorem rd_lRn_ne_zP : lRn ≠ zP := by decide
@[simp] theorem rd_zP_ne_kFu : zP ≠ kFu := by decide
@[simp] theorem rd_kFu_ne_zP : kFu ≠ zP := by decide
@[simp] theorem rd_zP_ne_kD : zP ≠ kD := by decide
@[simp] theorem rd_kD_ne_zP : kD ≠ zP := by decide
@[simp] theorem rd_zP_ne_kE : zP ≠ kE := by decide
@[simp] theorem rd_kE_ne_zP : kE ≠ zP := by decide
@[simp] theorem rd_zP_ne_lFle : zP ≠ lFle := by decide
@[simp] theorem rd_lFle_ne_zP : lFle ≠ zP := by decide
@[simp] theorem rd_zP_ne_lDir : zP ≠ lDir := by decide
@[simp] theorem rd_lDir_ne_zP : lDir ≠ zP := by decide
@[simp] theorem rd_zP_ne_lKb : zP ≠ lKb := by decide
@[simp] theorem rd_lKb_ne_zP : lKb ≠ zP := by decide
@[simp] theorem rd_zP_ne_qH : zP ≠ qH := by decide
@[simp] theorem rd_qH_ne_zP : qH ≠ zP := by decide
@[simp] theorem rd_zP_ne_nX : zP ≠ nX := by decide
@[simp] theorem rd_nX_ne_zP : nX ≠ zP := by decide
@[simp] theorem rd_zP_ne_nY : zP ≠ nY := by decide
@[simp] theorem rd_nY_ne_zP : nY ≠ zP := by decide
@[simp] theorem rd_zP_ne_rZ : zP ≠ rZ := by decide
@[simp] theorem rd_rZ_ne_zP : rZ ≠ zP := by decide
@[simp] theorem rd_zW_ne_zF : zW ≠ zF := by decide
@[simp] theorem rd_zW_ne_zB : zW ≠ zB := by decide
@[simp] theorem rd_zW_ne_zG : zW ≠ zG := by decide
@[simp] theorem rd_zW_ne_zA : zW ≠ zA := by decide
@[simp] theorem rd_zW_ne_zC : zW ≠ zC := by decide
@[simp] theorem rd_zW_ne_zU : zW ≠ zU := by decide
@[simp] theorem rd_zW_ne_zE : zW ≠ zE := by decide
@[simp] theorem rd_zW_ne_zN : zW ≠ zN := by decide
@[simp] theorem rd_zW_ne_zL : zW ≠ zL := by decide
@[simp] theorem rd_zW_ne_zP : zW ≠ zP := by decide
@[simp] theorem rd_zW_ne_zX : zW ≠ zX := by decide
@[simp] theorem rd_zW_ne_zY : zW ≠ zY := by decide
@[simp] theorem rd_zW_ne_zR : zW ≠ zR := by decide
@[simp] theorem rd_zW_ne_zO : zW ≠ zO := by decide
@[simp] theorem rd_zW_ne_lFl : zW ≠ lFl := by decide
@[simp] theorem rd_lFl_ne_zW : lFl ≠ zW := by decide
@[simp] theorem rd_zW_ne_lDh : zW ≠ lDh := by decide
@[simp] theorem rd_lDh_ne_zW : lDh ≠ zW := by decide
@[simp] theorem rd_zW_ne_lDt : zW ≠ lDt := by decide
@[simp] theorem rd_lDt_ne_zW : lDt ≠ zW := by decide
@[simp] theorem rd_zW_ne_lDg : zW ≠ lDg := by decide
@[simp] theorem rd_lDg_ne_zW : lDg ≠ zW := by decide
@[simp] theorem rd_zW_ne_lDi : zW ≠ lDi := by decide
@[simp] theorem rd_lDi_ne_zW : lDi ≠ zW := by decide
@[simp] theorem rd_zW_ne_lRp : zW ≠ lRp := by decide
@[simp] theorem rd_lRp_ne_zW : lRp ≠ zW := by decide
@[simp] theorem rd_zW_ne_lRn : zW ≠ lRn := by decide
@[simp] theorem rd_lRn_ne_zW : lRn ≠ zW := by decide
@[simp] theorem rd_zW_ne_kFu : zW ≠ kFu := by decide
@[simp] theorem rd_kFu_ne_zW : kFu ≠ zW := by decide
@[simp] theorem rd_zW_ne_kD : zW ≠ kD := by decide
@[simp] theorem rd_kD_ne_zW : kD ≠ zW := by decide
@[simp] theorem rd_zW_ne_kE : zW ≠ kE := by decide
@[simp] theorem rd_kE_ne_zW : kE ≠ zW := by decide
@[simp] theorem rd_zW_ne_lFle : zW ≠ lFle := by decide
@[simp] theorem rd_lFle_ne_zW : lFle ≠ zW := by decide
@[simp] theorem rd_zW_ne_lDir : zW ≠ lDir := by decide
@[simp] theorem rd_lDir_ne_zW : lDir ≠ zW := by decide
@[simp] theorem rd_zW_ne_lKb : zW ≠ lKb := by decide
@[simp] theorem rd_lKb_ne_zW : lKb ≠ zW := by decide
@[simp] theorem rd_zW_ne_qH : zW ≠ qH := by decide
@[simp] theorem rd_qH_ne_zW : qH ≠ zW := by decide
@[simp] theorem rd_zW_ne_nX : zW ≠ nX := by decide
@[simp] theorem rd_nX_ne_zW : nX ≠ zW := by decide
@[simp] theorem rd_zW_ne_nY : zW ≠ nY := by decide
@[simp] theorem rd_nY_ne_zW : nY ≠ zW := by decide
@[simp] theorem rd_zW_ne_rZ : zW ≠ rZ := by decide
@[simp] theorem rd_rZ_ne_zW : rZ ≠ zW := by decide
@[simp] theorem rd_zX_ne_zF : zX ≠ zF := by decide
@[simp] theorem rd_zX_ne_zB : zX ≠ zB := by decide
@[simp] theorem rd_zX_ne_zG : zX ≠ zG := by decide
@[simp] theorem rd_zX_ne_zA : zX ≠ zA := by decide
@[simp] theorem rd_zX_ne_zC : zX ≠ zC := by decide
@[simp] theorem rd_zX_ne_zU : zX ≠ zU := by decide
@[simp] theorem rd_zX_ne_zE : zX ≠ zE := by decide
@[simp] theorem rd_zX_ne_zN : zX ≠ zN := by decide
@[simp] theorem rd_zX_ne_zL : zX ≠ zL := by decide
@[simp] theorem rd_zX_ne_zP : zX ≠ zP := by decide
@[simp] theorem rd_zX_ne_zW : zX ≠ zW := by decide
@[simp] theorem rd_zX_ne_zY : zX ≠ zY := by decide
@[simp] theorem rd_zX_ne_zR : zX ≠ zR := by decide
@[simp] theorem rd_zX_ne_zO : zX ≠ zO := by decide
@[simp] theorem rd_zX_ne_lFl : zX ≠ lFl := by decide
@[simp] theorem rd_lFl_ne_zX : lFl ≠ zX := by decide
@[simp] theorem rd_zX_ne_lDh : zX ≠ lDh := by decide
@[simp] theorem rd_lDh_ne_zX : lDh ≠ zX := by decide
@[simp] theorem rd_zX_ne_lDt : zX ≠ lDt := by decide
@[simp] theorem rd_lDt_ne_zX : lDt ≠ zX := by decide
@[simp] theorem rd_zX_ne_lDg : zX ≠ lDg := by decide
@[simp] theorem rd_lDg_ne_zX : lDg ≠ zX := by decide
@[simp] theorem rd_zX_ne_lDi : zX ≠ lDi := by decide
@[simp] theorem rd_lDi_ne_zX : lDi ≠ zX := by decide
@[simp] theorem rd_zX_ne_lRp : zX ≠ lRp := by decide
@[simp] theorem rd_lRp_ne_zX : lRp ≠ zX := by decide
@[simp] theorem rd_zX_ne_lRn : zX ≠ lRn := by decide
@[simp] theorem rd_lRn_ne_zX : lRn ≠ zX := by decide
@[simp] theorem rd_zX_ne_kFu : zX ≠ kFu := by decide
@[simp] theorem rd_kFu_ne_zX : kFu ≠ zX := by decide
@[simp] theorem rd_zX_ne_kD : zX ≠ kD := by decide
@[simp] theorem rd_kD_ne_zX : kD ≠ zX := by decide
@[simp] theorem rd_zX_ne_kE : zX ≠ kE := by decide
@[simp] theorem rd_kE_ne_zX : kE ≠ zX := by decide
@[simp] theorem rd_zX_ne_lFle : zX ≠ lFle := by decide
@[simp] theorem rd_lFle_ne_zX : lFle ≠ zX := by decide
@[simp] theorem rd_zX_ne_lDir : zX ≠ lDir := by decide
@[simp] theorem rd_lDir_ne_zX : lDir ≠ zX := by decide
@[simp] theorem rd_zX_ne_lKb : zX ≠ lKb := by decide
@[simp] theorem rd_lKb_ne_zX : lKb ≠ zX := by decide
@[simp] theorem rd_zX_ne_qH : zX ≠ qH := by decide
@[simp] theorem rd_qH_ne_zX : qH ≠ zX := by decide
@[simp] theorem rd_zX_ne_nX : zX ≠ nX := by decide
@[simp] theorem rd_nX_ne_zX : nX ≠ zX := by decide
@[simp] theorem rd_zX_ne_nY : zX ≠ nY := by decide
@[simp] theorem rd_nY_ne_zX : nY ≠ zX := by decide
@[simp] theorem rd_zX_ne_rZ : zX ≠ rZ := by decide
@[simp] theorem rd_rZ_ne_zX : rZ ≠ zX := by decide
@[simp] theorem rd_zY_ne_zF : zY ≠ zF := by decide
@[simp] theorem rd_zY_ne_zB : zY ≠ zB := by decide
@[simp] theorem rd_zY_ne_zG : zY ≠ zG := by decide
@[simp] theorem rd_zY_ne_zA : zY ≠ zA := by decide
@[simp] theorem rd_zY_ne_zC : zY ≠ zC := by decide
@[simp] theorem rd_zY_ne_zU : zY ≠ zU := by decide
@[simp] theorem rd_zY_ne_zE : zY ≠ zE := by decide
@[simp] theorem rd_zY_ne_zN : zY ≠ zN := by decide
@[simp] theorem rd_zY_ne_zL : zY ≠ zL := by decide
@[simp] theorem rd_zY_ne_zP : zY ≠ zP := by decide
@[simp] theorem rd_zY_ne_zW : zY ≠ zW := by decide
@[simp] theorem rd_zY_ne_zX : zY ≠ zX := by decide
@[simp] theorem rd_zY_ne_zR : zY ≠ zR := by decide
@[simp] theorem rd_zY_ne_zO : zY ≠ zO := by decide
@[simp] theorem rd_zY_ne_lFl : zY ≠ lFl := by decide
@[simp] theorem rd_lFl_ne_zY : lFl ≠ zY := by decide
@[simp] theorem rd_zY_ne_lDh : zY ≠ lDh := by decide
@[simp] theorem rd_lDh_ne_zY : lDh ≠ zY := by decide
@[simp] theorem rd_zY_ne_lDt : zY ≠ lDt := by decide
@[simp] theorem rd_lDt_ne_zY : lDt ≠ zY := by decide
@[simp] theorem rd_zY_ne_lDg : zY ≠ lDg := by decide
@[simp] theorem rd_lDg_ne_zY : lDg ≠ zY := by decide
@[simp] theorem rd_zY_ne_lDi : zY ≠ lDi := by decide
@[simp] theorem rd_lDi_ne_zY : lDi ≠ zY := by decide
@[simp] theorem rd_zY_ne_lRp : zY ≠ lRp := by decide
@[simp] theorem rd_lRp_ne_zY : lRp ≠ zY := by decide
@[simp] theorem rd_zY_ne_lRn : zY ≠ lRn := by decide
@[simp] theorem rd_lRn_ne_zY : lRn ≠ zY := by decide
@[simp] theorem rd_zY_ne_kFu : zY ≠ kFu := by decide
@[simp] theorem rd_kFu_ne_zY : kFu ≠ zY := by decide
@[simp] theorem rd_zY_ne_kD : zY ≠ kD := by decide
@[simp] theorem rd_kD_ne_zY : kD ≠ zY := by decide
@[simp] theorem rd_zY_ne_kE : zY ≠ kE := by decide
@[simp] theorem rd_kE_ne_zY : kE ≠ zY := by decide
@[simp] theorem rd_zY_ne_lFle : zY ≠ lFle := by decide
@[simp] theorem rd_lFle_ne_zY : lFle ≠ zY := by decide
@[simp] theorem rd_zY_ne_lDir : zY ≠ lDir := by decide
@[simp] theorem rd_lDir_ne_zY : lDir ≠ zY := by decide
@[simp] theorem rd_zY_ne_lKb : zY ≠ lKb := by decide
@[simp] theorem rd_lKb_ne_zY : lKb ≠ zY := by decide
@[simp] theorem rd_zY_ne_qH : zY ≠ qH := by decide
@[simp] theorem rd_qH_ne_zY : qH ≠ zY := by decide
@[simp] theorem rd_zY_ne_nX : zY ≠ nX := by decide
@[simp] theorem rd_nX_ne_zY : nX ≠ zY := by decide
@[simp] theorem rd_zY_ne_nY : zY ≠ nY := by decide
@[simp] theorem rd_nY_ne_zY : nY ≠ zY := by decide
@[simp] theorem rd_zY_ne_rZ : zY ≠ rZ := by decide
@[simp] theorem rd_rZ_ne_zY : rZ ≠ zY := by decide
@[simp] theorem rd_zR_ne_zF : zR ≠ zF := by decide
@[simp] theorem rd_zR_ne_zB : zR ≠ zB := by decide
@[simp] theorem rd_zR_ne_zG : zR ≠ zG := by decide
@[simp] theorem rd_zR_ne_zA : zR ≠ zA := by decide
@[simp] theorem rd_zR_ne_zC : zR ≠ zC := by decide
@[simp] theorem rd_zR_ne_zU : zR ≠ zU := by decide
@[simp] theorem rd_zR_ne_zE : zR ≠ zE := by decide
@[simp] theorem rd_zR_ne_zN : zR ≠ zN := by decide
@[simp] theorem rd_zR_ne_zL : zR ≠ zL := by decide
@[simp] theorem rd_zR_ne_zP : zR ≠ zP := by decide
@[simp] theorem rd_zR_ne_zW : zR ≠ zW := by decide
@[simp] theorem rd_zR_ne_zX : zR ≠ zX := by decide
@[simp] theorem rd_zR_ne_zY : zR ≠ zY := by decide
@[simp] theorem rd_zR_ne_zO : zR ≠ zO := by decide
@[simp] theorem rd_zR_ne_lFl : zR ≠ lFl := by decide
@[simp] theorem rd_lFl_ne_zR : lFl ≠ zR := by decide
@[simp] theorem rd_zR_ne_lDh : zR ≠ lDh := by decide
@[simp] theorem rd_lDh_ne_zR : lDh ≠ zR := by decide
@[simp] theorem rd_zR_ne_lDt : zR ≠ lDt := by decide
@[simp] theorem rd_lDt_ne_zR : lDt ≠ zR := by decide
@[simp] theorem rd_zR_ne_lDg : zR ≠ lDg := by decide
@[simp] theorem rd_lDg_ne_zR : lDg ≠ zR := by decide
@[simp] theorem rd_zR_ne_lDi : zR ≠ lDi := by decide
@[simp] theorem rd_lDi_ne_zR : lDi ≠ zR := by decide
@[simp] theorem rd_zR_ne_lRp : zR ≠ lRp := by decide
@[simp] theorem rd_lRp_ne_zR : lRp ≠ zR := by decide
@[simp] theorem rd_zR_ne_lRn : zR ≠ lRn := by decide
@[simp] theorem rd_lRn_ne_zR : lRn ≠ zR := by decide
@[simp] theorem rd_zR_ne_kFu : zR ≠ kFu := by decide
@[simp] theorem rd_kFu_ne_zR : kFu ≠ zR := by decide
@[simp] theorem rd_zR_ne_kD : zR ≠ kD := by decide
@[simp] theorem rd_kD_ne_zR : kD ≠ zR := by decide
@[simp] theorem rd_zR_ne_kE : zR ≠ kE := by decide
@[simp] theorem rd_kE_ne_zR : kE ≠ zR := by decide
@[simp] theorem rd_zR_ne_lFle : zR ≠ lFle := by decide
@[simp] theorem rd_lFle_ne_zR : lFle ≠ zR := by decide
@[simp] theorem rd_zR_ne_lDir : zR ≠ lDir := by decide
@[simp] theorem rd_lDir_ne_zR : lDir ≠ zR := by decide
@[simp] theorem rd_zR_ne_lKb : zR ≠ lKb := by decide
@[simp] theorem rd_lKb_ne_zR : lKb ≠ zR := by decide
@[simp] theorem rd_zR_ne_qH : zR ≠ qH := by decide
@[simp] theorem rd_qH_ne_zR : qH ≠ zR := by decide
@[simp] theorem rd_zR_ne_nX : zR ≠ nX := by decide
@[simp] theorem rd_nX_ne_zR : nX ≠ zR := by decide
@[simp] theorem rd_zR_ne_nY : zR ≠ nY := by decide
@[simp] theorem rd_nY_ne_zR : nY ≠ zR := by decide
@[simp] theorem rd_zR_ne_rZ : zR ≠ rZ := by decide
@[simp] theorem rd_rZ_ne_zR : rZ ≠ zR := by decide
@[simp] theorem rd_zO_ne_zF : zO ≠ zF := by decide
@[simp] theorem rd_zO_ne_zB : zO ≠ zB := by decide
@[simp] theorem rd_zO_ne_zG : zO ≠ zG := by decide
@[simp] theorem rd_zO_ne_zA : zO ≠ zA := by decide
@[simp] theorem rd_zO_ne_zC : zO ≠ zC := by decide
@[simp] theorem rd_zO_ne_zU : zO ≠ zU := by decide
@[simp] theorem rd_zO_ne_zE : zO ≠ zE := by decide
@[simp] theorem rd_zO_ne_zN : zO ≠ zN := by decide
@[simp] theorem rd_zO_ne_zL : zO ≠ zL := by decide
@[simp] theorem rd_zO_ne_zP : zO ≠ zP := by decide
@[simp] theorem rd_zO_ne_zW : zO ≠ zW := by decide
@[simp] theorem rd_zO_ne_zX : zO ≠ zX := by decide
@[simp] theorem rd_zO_ne_zY : zO ≠ zY := by decide
@[simp] theorem rd_zO_ne_zR : zO ≠ zR := by decide
@[simp] theorem rd_zO_ne_lFl : zO ≠ lFl := by decide
@[simp] theorem rd_lFl_ne_zO : lFl ≠ zO := by decide
@[simp] theorem rd_zO_ne_lDh : zO ≠ lDh := by decide
@[simp] theorem rd_lDh_ne_zO : lDh ≠ zO := by decide
@[simp] theorem rd_zO_ne_lDt : zO ≠ lDt := by decide
@[simp] theorem rd_lDt_ne_zO : lDt ≠ zO := by decide
@[simp] theorem rd_zO_ne_lDg : zO ≠ lDg := by decide
@[simp] theorem rd_lDg_ne_zO : lDg ≠ zO := by decide
@[simp] theorem rd_zO_ne_lDi : zO ≠ lDi := by decide
@[simp] theorem rd_lDi_ne_zO : lDi ≠ zO := by decide
@[simp] theorem rd_zO_ne_lRp : zO ≠ lRp := by decide
@[simp] theorem rd_lRp_ne_zO : lRp ≠ zO := by decide
@[simp] theorem rd_zO_ne_lRn : zO ≠ lRn := by decide
@[simp] theorem rd_lRn_ne_zO : lRn ≠ zO := by decide
@[simp] theorem rd_zO_ne_kFu : zO ≠ kFu := by decide
@[simp] theorem rd_kFu_ne_zO : kFu ≠ zO := by decide
@[simp] theorem rd_zO_ne_kD : zO ≠ kD := by decide
@[simp] theorem rd_kD_ne_zO : kD ≠ zO := by decide
@[simp] theorem rd_zO_ne_kE : zO ≠ kE := by decide
@[simp] theorem rd_kE_ne_zO : kE ≠ zO := by decide
@[simp] theorem rd_zO_ne_lFle : zO ≠ lFle := by decide
@[simp] theorem rd_lFle_ne_zO : lFle ≠ zO := by decide
@[simp] theorem rd_zO_ne_lDir : zO ≠ lDir := by decide
@[simp] theorem rd_lDir_ne_zO : lDir ≠ zO := by decide
@[simp] theorem rd_zO_ne_lKb : zO ≠ lKb := by decide
@[simp] theorem rd_lKb_ne_zO : lKb ≠ zO := by decide
@[simp] theorem rd_zO_ne_qH : zO ≠ qH := by decide
@[simp] theorem rd_qH_ne_zO : qH ≠ zO := by decide
@[simp] theorem rd_zO_ne_nX : zO ≠ nX := by decide
@[simp] theorem rd_nX_ne_zO : nX ≠ zO := by decide
@[simp] theorem rd_zO_ne_nY : zO ≠ nY := by decide
@[simp] theorem rd_nY_ne_zO : nY ≠ zO := by decide
@[simp] theorem rd_zO_ne_rZ : zO ≠ rZ := by decide
@[simp] theorem rd_rZ_ne_zO : rZ ≠ zO := by decide

section
variable {σ : Type}

/-- Calling a `PostK` function given in callee form. -/
theorem specR_callKC {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM EIdx} {k : EIdx → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f : MlS) (ps : List MlS) (es : List (ExpHOL 64)) (Bd : ProgHOL 64) (vs : List (BitVec 64))
    (hnd : ps.Nodup) (hl : vs.length = ps.length)
    (hx : x ∈ D) (hC : C.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), Bd, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs)
    (hspec : Callee (σ := σ) C ps vs Bd s m (PostK C))
    (hk : ∀ a s' H', C.H <+: H' → m s = .ok (a, s') →
      SpecR (Inv (ctxH C H') s' ((x, Enc.idxW a) :: Γ) [] D) rest s' (k a) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f es) rest) s (m >>= k) R :=
  specR_callNIH x f ps es Bd vs hnd hl hx hC hes (fun a w s' st => m s = .ok (a, s') ∧ PostK C a w s' st)
    (fun a w s' _ => w = Enc.idxW a ∧ m s = .ok (a, s'))
    (fun a w s' st ⟨hrun, H', hp, hw, hsr⟩ => ⟨H', hp, ⟨hw, hrun⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (hspec u hu (fun i hi _ => hlk i (by omega))))
    (fun a w s' H' hp ⟨hw, hrun⟩ => by subst hw; exact hk a s' H' hp hrun)

theorem bigCodes_H {C : Ctx} (hc : BigCodes C) (H : List (BitVec 64)) : BigCodes (ctxH C H) :=
  ⟨hc.lit, hc.add, hc.sub, hc.mul, hc.cmp, hc.litb, hc.bit, hc.shr, hc.dm, hc.iconst, hc.shl, hc.pow, hc.gcd⟩

/-- Calling `rawNat`. -/
theorem specR_callRN {β : Type} {C : Ctx} (hok : CtxOK C) (hc : BigCodes C)
    (hcr : C.code.lookup fRaw = some ([(qH, ShapeHOL.one)], rnBody C, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {k : Option Nat → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (e : ExpHOL 64) (h : EIdx) (hx : x ∈ D) (he : sev Γ e = some (Enc.idxW h))
    (hk : ∀ o H' w, C.H <+: H' → (match o with
        | none => w = 0
        | some n => ∃ ob, w = cellA C ob ∧ BlkAt H' ob (limbs n)) →
      SpecR (Inv (ctxH C H') s ((x, w) :: Γ) [] D) rest s (k o) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) fRaw [e]) rest) s
      (rawNatLit? h >>= k) R :=
  specR_callNIH x fRaw [qH] [e] (rnBody C) [Enc.idxW h] (by decide) rfl hx (by simpa using hcr) ⟨he, trivial⟩
    (fun o w s' st => rawNatLit? h s = .ok (o, s') ∧ PostRN C s o w s' st)
    (fun o w s' H' => s' = s ∧ match o with
        | none => w = 0
        | some n => ∃ ob, w = cellA C ob ∧ BlkAt H' ob (limbs n))
    (fun o w s' st ⟨_, hs, H', hp, hsr, hm⟩ => ⟨H', hp, ⟨hs, hm⟩, hs ▸ hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [qH] [Enc.idxW h] rfl hlk)
      (rn_spec C hok hc s h)))
    (fun o w s' H' hp ⟨hs, hm⟩ => by subst hs; exact hk o H' w hp hm)

def rdLeaf (fn : MlS) : ProgHOL 64 :=
  .seq (.call (some (some (.local, zW), none)) fW [vv kFu, vv kD, vv zA])
  (.seq (.call (some (some (.local, zX), none)) fRaw [vv zW])
  (.ite (.cmp .equal (vv zX) (.const 0)) (.return (.const 0))
  (.seq (.call (some (some (.local, zW), none)) fW [vv kFu, vv kD, vv zB])
  (.seq (.call (some (some (.local, zY), none)) fRaw [vv zW])
  (.ite (.cmp .equal (vv zY) (.const 0)) (.return (.const 0))
  (.seq (.call (some (some (.local, zR), none)) fn [vv zX, vv zY]) (.return (vv zR))))))))

/-- The twin's leaf: both arguments to literals, then the operation. -/
def leafT (r : CoreFnsA) (d : Nat) (a b : EIdx) (op : NatBinOp) : AM (Option EIdx) :=
  r.whnf d a >>= fun w1 => rawNatLit? w1 >>= fun o1 => match o1 with
    | some n1 => r.whnf d b >>= fun w2 => rawNatLit? w2 >>= fun o2 => match o2 with
      | some n2 => natBinOpResult op n1 n2
      | none => pure none
    | none => pure none

theorem rd_leaf (mode : ConLeche.CheckMode) (n : Nat) {C : Ctx} (hok : CtxOK C) (hc : BigCodes C)
    (hcr : C.code.lookup fRaw = some ([(qH, ShapeHOL.one)], rnBody C, .one))
    (hcw : C.code.lookup fW = some (kParams.map (fun p => (p, ShapeHOL.one)), whnfE C fWB, .one))
    (Q : AState → Prop) (hQ : ∀ s1 d e a s2, Q s1 → (knot mode C n).whnf d e s1 = .ok (a, s2) → Q s2)
    (hW : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ d e, Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e] (whnfE C fWB) s1 ((knot mode C n).whnf d e)
      (PostK (ctxH C H)))
    (op : NatBinOp) (fn : MlS) (Bfn : ProgHOL 64)
    (hcf : C.code.lookup fn = some (nbParams.map (fun p => (p, ShapeHOL.one)), Bfn, .one))
    (hfn : ∀ (H : List (BitVec 64)) s1 px py a b, C.H <+: H → BlkAt H px (limbs a) → BlkAt H py (limbs b) →
      SpecR (σ := σ) (Pre (ctxH C H) s1 (nbParams.zip [cellA C px, cellA C py])) Bfn s1 (natBinOpResult op a b)
        (UD.PostO (ctxH C H)))
    {H0 : List (BitVec 64)} {s : AState} {Γ : Env} {D : List MlS} (hs : Q s) (hp0 : C.H <+: H0) (d : Nat) (a b : EIdx)
    (hFu : Γ.get kFu = some (BitVec.ofNat 64 n)) (hD0 : Γ.get kD = some (BitVec.ofNat 64 d))
    (hA : Γ.get zA = some (Enc.idxW a)) (hB : Γ.get zB = some (Enc.idxW b))
    (hDD : zW ∈ D ∧ zX ∈ D ∧ zY ∈ D ∧ zR ∈ D)
    (hnX : Γ.get zX = none) :
    SpecR (σ := σ) (Inv (ctxH C H0) s Γ [] D) (rdLeaf fn) s (leafT (knot mode C n) d a b op) (UD.PostO C) := by
  unfold rdLeaf leafT
  refine specR_callKC zW fW kParams _ (whnfE C fWB) [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a] (by decide)
    rfl hDD.1 hcw ⟨by simp [hFu], by simp [hD0], by simp [hA], trivial⟩ (hW H0 s hp0 hs d a)
    (fun w1 s1 H1 hp1 hrun1 => ?_)
  refine specR_callRN (C := ctxH (ctxH C H0) H1) (ctxOK_H hok _) (bigCodes_H hc _) hcr zX (vv zW) w1 hDD.2.1 (by simp)
    (fun o1 H2 x hp2 hx => ?_)
  rcases o1 with _ | n1
  · simp only at hx; subst hx
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    refine specR_returnI _ 0 rfl (fun t ht => ?_)
    exact ⟨H2, hp0.trans (hp1.trans hp2), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
  obtain ⟨ox, rfl, hbx⟩ := hx
  refine specR_atEntry fun t0 ht0 => ?_
  have hox : ox < C.HN := by
    obtain ⟨H', hp', ha'⟩ := ht0.sr.heap
    have := blkAt_len hbx; have := hp'.length_le; have := ha'.len; simp only [ctxH] at *; omega
  have hne := ExSP.cellA_ne0 C hok ox hox
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h)
    (fun _ => ?_)
  have hQ1 : Q s1 := hQ s d a w1 s1 hs hrun1
  refine specR_callKC (C := ctxH C H2) zW fW kParams _ (whnfE C fWB) [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW b]
    (by decide) rfl hDD.1 hcw ⟨by simp [hFu], by simp [hD0], by simp [hB], trivial⟩
    (hW H2 s1 (hp0.trans (hp1.trans hp2)) hQ1 d b) (fun w2 s2 H3 hp3 hrun2 => ?_)
  refine specR_callRN (C := ctxH (ctxH C H2) H3) (ctxOK_H hok _) (bigCodes_H hc _) hcr zY (vv zW) w2 hDD.2.2.1 (by simp)
    (fun o2 H4 y hp4 hy => ?_)
  rcases o2 with _ | n2
  · simp only at hy; subst hy
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    refine specR_returnI _ 0 rfl (fun t ht => ?_)
    exact ⟨H4, hp0.trans (hp1.trans (hp2.trans (hp3.trans hp4))), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
  obtain ⟨oy, rfl, hby⟩ := hy
  refine specR_atEntry fun t1 ht1 => ?_
  have hoy : oy < C.HN := by
    obtain ⟨H', hp', ha'⟩ := ht1.sr.heap
    have := blkAt_len hby; have := hp'.length_le; have := ha'.len; simp only [ctxH] at *; omega
  have hne2 := ExSP.cellA_ne0 C hok oy hoy
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne2) (fun h => absurd rfl h)
    (fun _ => ?_)
  have hbx' : BlkAt H4 ox (limbs n1) := blkAt_mono hbx (hp3.trans hp4)
  refine specR_congr (m' := natBinOpResult op n1 n2 >>= fun r => pure r) (by simp) ?_
  refine specR_callNIH zR fn nbParams [vv zX, vv zY] Bfn [cellA C ox, cellA C oy] (by decide) rfl hDD.2.2.2 hcf
    ⟨by simp; rfl, by simp; rfl, trivial⟩ (UD.PostO (ctxH C H4)) (fun r w _ _ => w = optW r)
    (fun r w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu nbParams _ rfl hlk)
      (hfn H4 s2 ox oy n1 n2 (hp0.trans (hp1.trans (hp2.trans (hp3.trans hp4)))) hbx' hby))
    (fun r w s' H5 hp5 hw => ?_)
  subst hw
  refine specR_returnI _ (optW r) (by simp) (fun t ht => ?_)
  exact ⟨H5, hp0.trans (hp1.trans (hp2.trans (hp3.trans (hp4.trans hp5)))), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩

def opTab : List (Nat × NatBinOp) := [(15, .add), (16, .sub), (17, .mul), (18, .pow), (19, .beq), (20, .ble),
  (21, .div), (22, .mod), (23, .gcd), (24, .land), (25, .lor), (26, .xor), (27, .shiftLeft), (28, .shiftRight)]

def opFind (names : Array NIdx) (c : NIdx) : List (Nat × NatBinOp) → Option NatBinOp
  | [] => none
  | (i, op) :: r => if c == names[i]! then some op else opFind names c r

theorem ite_ok {α : Type} (s : AState) (p : Prop) [Decidable p] (a : α) (m : AM α) (b : α)
    (hm : m s = .ok (b, s)) : (if p then StateT.pure a else m) s = .ok (if p then a else b, s) := by
  by_cases h : p
  · simp [h]; rfl
  · simp [h, hm]

set_option maxHeartbeats 2000000 in
theorem natBinOpOfName_run {C : Ctx} (hok : CtxOK C) (s : AState) (hp : s.pins = C.pins) (c : NIdx) :
    natBinOpOfName? c s = .ok (opFind C.pins.names c opTab, s) := by
  have hsz : C.pins.names.size = 52 := hok.pinsRel.1
  simp (config := { maxSteps := 4000000 }) [natBinOpOfName?, natAddName, natSubName, natMulName, natPowName, natBeqName, natBleName, natDivName,
    natModName, natGcdName, natLandName, natLorName, natXorName, natShiftLeftName, natShiftRightName,
    pinNatAdd, pinNatSub, pinNatMul, pinNatPow, pinNatBeq, pinNatBle, pinNatDiv, pinNatMod, pinNatGcd,
    pinNatLand, pinNatLor, pinNatXor, pinNatShiftLeft, pinNatShiftRight, pinAt, hp, hsz,
    PIN_NAT_ADD, PIN_NAT_SUB, PIN_NAT_MUL, PIN_NAT_POW, PIN_NAT_BEQ, PIN_NAT_BLE, PIN_NAT_DIV, PIN_NAT_MOD,
    PIN_NAT_GCD, PIN_NAT_LAND, PIN_NAT_LOR, PIN_NAT_XOR, PIN_NAT_SHIFT_LEFT, PIN_NAT_SHIFT_RIGHT,
    get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure,
    opFind, opTab]
  repeat (first | refine ite_ok s _ _ _ _ ?_ | rfl)


theorem opFind_cons (names : Array NIdx) (c : NIdx) (i : Nat) (op : NatBinOp) (r : List (Nat × NatBinOp))
    (hi : i < names.size) :
    opFind names c ((i, op) :: r) = if c = names[i] then some op else opFind names c r := by
  simp only [opFind, getElem!_pos names i hi]
  by_cases h : c = names[i] <;> simp [h]

/-- An operation of the table: its pin, its twin operation, its function and body. -/
structure NbE where
  i : Nat
  op : NatBinOp
  fn : MlS
  body : Ctx → ProgHOL 64

def rdChain (C : Ctx) : List (Nat × MlS) → ProgHOL 64
  | [] => .return (.const 0)
  | (i, fn) :: r => .seq (.assign .local zP (.load .one (.const (ecell C (C.PO + i)))))
      (.ite (.cmp .equal (vv zC) (vv zP)) (rdLeaf fn) (rdChain C r))

theorem rd_chain (mode : ConLeche.CheckMode) (n : Nat) {C : Ctx} (hok : CtxOK C) (hc : BigCodes C)
    (hcr : C.code.lookup fRaw = some ([(qH, ShapeHOL.one)], rnBody C, .one))
    (hcw : C.code.lookup fW = some (kParams.map (fun p => (p, ShapeHOL.one)), whnfE C fWB, .one))
    (Q : AState → Prop) (hQ : ∀ s1 d e a s2, Q s1 → (knot mode C n).whnf d e s1 = .ok (a, s2) → Q s2)
    (hW : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ d e, Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e] (whnfE C fWB) s1 ((knot mode C n).whnf d e)
      (PostK (ctxH C H)))
    {H0 : List (BitVec 64)} {s : AState} {D : List MlS} (hs : Q s) (hp0 : C.H <+: H0) (d : Nat) (a b : EIdx)
    (c : NIdx) (hDD : zW ∈ D ∧ zX ∈ D ∧ zY ∈ D ∧ zR ∈ D ∧ zP ∈ D) :
    ∀ (L : List NbE) (Γ : Env), (∀ e ∈ L, e.i < pinCount ∧
      C.code.lookup e.fn = some (nbParams.map (fun p => (p, ShapeHOL.one)), e.body C, .one) ∧
      ∀ (H : List (BitVec 64)) s1 px py a b, C.H <+: H → BlkAt H px (limbs a) → BlkAt H py (limbs b) →
        SpecR (σ := σ) (Pre (ctxH C H) s1 (nbParams.zip [cellA C px, cellA C py])) (e.body C) s1
          (natBinOpResult e.op a b) (UD.PostO (ctxH C H))) →
    Γ.get kFu = some (BitVec.ofNat 64 n) → Γ.get kD = some (BitVec.ofNat 64 d) →
    Γ.get zA = some (Enc.idxW a) → Γ.get zB = some (Enc.idxW b) → Γ.get zC = some (Enc.idxW c) →
    Γ.get zX = none →
    SpecR (σ := σ) (Inv (ctxH C H0) s Γ [] D) (rdChain C (L.map fun e => (e.i, e.fn))) s
      (match opFind C.pins.names c (L.map fun e => (e.i, e.op)) with
        | some op => leafT (knot mode C n) d a b op
        | none => pure none) (UD.PostO C)
  | [], Γ, _, _, _, _, _, _, _ => by
    refine specR_returnI _ 0 rfl (fun t ht => ?_)
    exact ⟨H0, hp0, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
  | e :: L, Γ, hL, hFu, hD0, hA, hB, hC, hnX => by
    obtain ⟨hi, hcf, hfn⟩ := hL e (List.mem_cons_self ..)
    have hi' : e.i < C.pins.names.size := by rw [hok.pinsRel.1]; exact hi
    simp only [List.map_cons, rdChain]
    rw [opFind_cons _ _ _ _ _ hi']
    refine specR_envLoadI (C := ctxH C H0) zP _ (C.PO + e.i) _ hDD.2.2.2.2 rfl (hok.pinsRel.2.1 e.i hi') ?_
    by_cases hce : c = C.pins.names[e.i]
    · refine specR_ifI _ 1 (by simp [sev, hC, hce, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      rw [if_pos hce]
      exact rd_leaf mode n hok hc hcr hcw Q hQ hW e.op e.fn (e.body C) hcf hfn hs hp0 d a b (by simp [hFu])
        (by simp [hD0]) (by simp [hA]) (by simp [hB]) ⟨hDD.1, hDD.2.1, hDD.2.2.1, hDD.2.2.2.1⟩ (by simp [hnX])
    · have hne : Enc.idxW c ≠ Enc.idxW C.pins.names[e.i] := fun h => hce (Enc.idxW_inj h)
      refine specR_ifI _ 0 (by simp [sev, hC, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
        (fun h => absurd rfl h) (fun _ => ?_)
      rw [if_neg hce]
      exact rd_chain mode n hok hc hcr hcw Q hQ hW hs hp0 d a b c hDD L _
        (fun e' he' => hL e' (List.mem_cons_of_mem _ he')) (by simp [hFu]) (by simp [hD0]) (by simp [hA])
        (by simp [hB]) (by simp [hC]) (by simp [hnX])


theorem specR_gLitI {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (hx : x ∈ D)
    (h : SpecR (Inv C s ((x, litW C.fe) :: Γ) M D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (.assign .local x (.var .global gLit)) rest) s m R :=
  specR_pre_assign x _ (fun _ => litW C.fe) (fun t ht => eval_gv t gLit _ ht.sr.env.2.2.2)
    (fun t ht => ht.decl x hx) (fun t ht => inv_set ht x _) h

theorem litW_and1 (fe : IFEnv) : litW fe &&& 1#64 = boolW fe.natLit := by
  unfold litW boolW; cases fe.natLit <;> cases fe.strLit <;> decide

def rdSucc (C : Ctx) : ProgHOL 64 :=
  .seq (.call (some (some (.local, zW), none)) fW [vv kFu, vv kD, vv zB])
  (.seq (.call (some (some (.local, zX), none)) fRaw [vv zW])
  (.ite (.cmp .equal (vv zX) (.const 0)) (.return (.const 0))
  (allocP C zO (.const 16) (.seq (.store (vv zO) (.const 1))
  (.seq (.store (.op .add [vv zO, .const 8]) (.const 1))
  (.seq (.call (some (some (.local, zR), none)) fNbAdd [vv zX, vv zO]) (.return (vv zR))))))))

def succT (r : CoreFnsA) (d : Nat) (b : EIdx) : AM (Option EIdx) :=
  r.whnf d b >>= fun w => rawNatLit? w >>= fun o => match o with
    | some n => litNatSized (n + 1)
    | none => pure none

theorem rd_succ (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) {C : Ctx}
    (hok : CtxOK C) (hc : BigCodes C)
    (hcr : C.code.lookup fRaw = some ([(qH, ShapeHOL.one)], rnBody C, .one))
    (hcw : C.code.lookup fW = some (kParams.map (fun p => (p, ShapeHOL.one)), whnfE C fWB, .one))
    (hca : C.code.lookup fNbAdd = some (nbParams.map (fun p => (p, ShapeHOL.one)), nbAddBody C, .one))
    (Q : AState → Prop)
    (hW : ∀ (H : List (BitVec 64)) s1, C.H <+: H → Q s1 → ∀ d e, Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e] (whnfE C fWB) s1 ((knot mode C n).whnf d e)
      (PostK (ctxH C H)))
    {H0 : List (BitVec 64)} {s : AState} {Γ : Env} {D : List MlS} (hs : Q s) (hp0 : C.H <+: H0) (d : Nat) (b : EIdx)
    (hFu : Γ.get kFu = some (BitVec.ofNat 64 n)) (hD0 : Γ.get kD = some (BitVec.ofNat 64 d))
    (hB : Γ.get zB = some (Enc.idxW b)) (hDD : zW ∈ D ∧ zX ∈ D ∧ zO ∈ D ∧ zR ∈ D) :
    SpecR (σ := σ) (Inv (ctxH C H0) s Γ [] D) (rdSucc C) s (succT (knot mode C n) d b) (UD.PostO C) := by
  unfold rdSucc succT
  refine specR_callKC zW fW kParams _ (whnfE C fWB) [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW b] (by decide)
    rfl hDD.1 hcw ⟨by simp [hFu], by simp [hD0], by simp [hB], trivial⟩ (hW H0 s hp0 hs d b)
    (fun w1 s1 H1 hp1 _ => ?_)
  refine specR_callRN (C := ctxH (ctxH C H0) H1) (ctxOK_H hok _) (bigCodes_H hc _) hcr zX (vv zW) w1 hDD.2.1
    (by simp) (fun o1 H2 x hp2 hx => ?_)
  rcases o1 with _ | n1
  · simp only at hx; subst hx
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    refine specR_returnI _ 0 rfl (fun t ht => ?_)
    exact ⟨H2, hp0.trans (hp1.trans hp2), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
  obtain ⟨ox, rfl, hbx⟩ := hx
  refine specR_atEntry fun t0 ht0 => ?_
  have hox : ox < C.HN := by
    obtain ⟨H', hp', ha'⟩ := ht0.sr.heap
    have := blkAt_len hbx; have := hp'.length_le; have := ha'.len; simp only [ctxH] at *; omega
  have hne := ExSP.cellA_ne0 C hok ox hox
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h)
    (fun _ => ?_)
  refine specR_allocI (C := ctxH C H2) zO (.const 16) 2 (by norm_num) hDD.2.2.1 (fun v => by simp [sev])
    (fun H3 ws hpre hwl hcap => ?_)
  have hpl := hpre.length_le
  have hj : H3.length < (ctxH (ctxH C H2) (H3 ++ ws)).H.length := by show _ < (H3 ++ ws).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv zO) (.const 1) _ hj 1 (by simp; rfl) rfl ?_
  have hj2 : H3.length + 1 < (ctxH (ctxH C H2) ((H3 ++ ws).set H3.length 1)).H.length := by
    show _ < ((H3 ++ ws).set _ _).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) _ (.const 1) _ hj2 1 (by simp [sev]; exact cellA_add8 C _) rfl ?_
  let H4 := ((H3 ++ ws).set H3.length 1).set (H3.length + 1) 1
  have hp1' := prefix_set_ge (hpre.trans (List.prefix_append _ ws)) _ hpl (1 : BitVec 64)
  have hp2' : H2 <+: H4 := prefix_set_ge hp1' (H3.length + 1) (by omega) (1 : BitVec 64)
  have hbo : BlkAt H4 H3.length (limbs 1) := by
    rw [show limbs 1 = [BitVec.ofNat 64 1] by rw [limbs_word 1 (by decide)]; rfl]
    refine ⟨?_, fun i hi => ?_⟩
    · show (((H3 ++ ws).set H3.length 1).set (H3.length + 1) 1)[H3.length]? = _
      rw [List.getElem?_set_ne (by omega), List.getElem?_set_self (by simp; omega)]; rfl
    · have : i = 0 := by simpa using hi
      subst this
      show (((H3 ++ ws).set H3.length 1).set (H3.length + 1) 1)[H3.length + 1 + 0]? = _
      rw [List.getElem?_set_self (by simp; omega)]; rfl
  have hbx' : BlkAt H4 ox (limbs n1) := blkAt_mono hbx hp2'
  show SpecR _ _ _ (natBinOpResult .add n1 1) _
  refine specR_congr (m' := natBinOpResult .add n1 1 >>= fun r => pure r) (by simp) ?_
  have hpall : C.H <+: H4 := hp0.trans (hp1.trans (hp2.trans hp2'))
  refine specR_callNIH zR fNbAdd nbParams [vv zX, vv zO] (nbAddBody C) [cellA C ox, cellA C H3.length]
    (by decide) rfl hDD.2.2.2 hca ⟨by simp; rfl, by simp; rfl, trivial⟩ (UD.PostO (ctxH C H4))
    (fun r w _ _ => w = optW r) (fun r w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu nbParams _ rfl hlk)
      (nbAdd_spec ra (ctxH C H4) (ctxOK_H hok _) (bigCodes_H hc _) s1 n1 1 ox H3.length hbx' hbo))
    (fun r w s' H5 hp5 hw => ?_)
  subst hw
  refine specR_returnI _ (optW r) (by simp) (fun t ht => ?_)
  exact ⟨H5, hpall.trans hp5, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩

end

end ConPanqueque.T.Big
