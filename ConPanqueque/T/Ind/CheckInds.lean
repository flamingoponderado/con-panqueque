import ConPanqueque.T.Ind.Seeds
import ConPanqueque.T.Decl.StepDefn

/-!
# `checkBlockInds` (single-member blocks): the former's telescope, the block's sort, the former pushed

A block with more than one member hangs (mutual blocks are outside the supported subset).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC


def cbiSh := ofString "cbi_sh"
def cbiIr := ofString "cbi_ir"
def cbiOm := ofString "cbi_om"
def cbiL := ofString "cbi_l"
def cbiP0 := ofString "cbi_p0"
def cbiNP := ofString "cbi_np"
def cbiNi := ofString "cbi_ni"
def cbiQ := ofString "cbi_q"
def cbiK := ofString "cbi_k"
def cbiT := ofString "cbi_t"
def cbiZ := ofString "cbi_z"
def cbiO := ofString "cbi_o"
def cbiIp := ofString "cbi_ip"
def cbiW0 := ofString "cbi_w0"
def cbiW1 := ofString "cbi_w1"
def cbiW3 := ofString "cbi_w3"
def cbiW5 := ofString "cbi_w5"
def cbiSh1 := ofString "cbi_sh1"
def cbiD := ofString "cbi_d"
def cbiNz := ofString "cbi_nz"
def cbiNm0 := ofString "cbi_nm0"
def cbiOne := ofString "cbi_one"
def cbiNB := ofString "cbi_nb"
def cbiAll := ofString "cbi_all"
def cbiRc := ofString "cbi_rc"
def cbiX := ofString "cbi_x"
def cbiDn := ofString "cbi_dn"
def cbiRi := ofString "cbi_ri"
def cbiF := ofString "cbi_f"
def fCbi := ofString "checkBlockInds"

def cbiParams : List MlS := [cbiSh, cbiIr]
def cbiLocals : List MlS := [cbiOm, cbiL, cbiP0, cbiNP, cbiNi, cbiQ, cbiK, cbiT, cbiZ, cbiO, cbiIp, cbiW0, cbiW1, cbiW3,
  cbiW5, cbiSh1, cbiD, cbiNz, cbiNm0, cbiOne, cbiNB, cbiAll, cbiRc, cbiX, cbiDn, cbiRi, cbiF]

/-- After the block's `Prop`-ness: the new shape, the former's record, the push, the literal flags. -/
def cbiRest (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local cbiW0 (.load .one (vv cbiSh)))
  (.seq (.assign .local cbiW1 (.load .one (.op .add [vv cbiSh, .const 8])))
  (.seq (.assign .local cbiW3 (.load .one (.op .add [vv cbiSh, .const 24])))
  (.seq (.assign .local cbiW5 (.load .one (.op .add [vv cbiSh, .const 40])))
  (alloc7 C cbiSh1 (vv cbiW0) (vv cbiW1) (vv cbiNP) (vv cbiW3) (vv cbiT) (vv cbiW5) (vv cbiIp)
  (.seq (.assign .local cbiD (.load .one (.op .add [vv cbiP0, .const 8])))
  (.seq (.call (some (some (.local, cbiNz), none)) fMemberNZ [vv cbiD])
  (.seq (.assign .local cbiNm0 (.load .one (vv cbiQ)))
  (.seq (.assign .local cbiOne (.const 1))
  (alloc2 C cbiNB (vv cbiOne) (vv cbiNm0)
  (envBlkP C cbiAll cbiNB cbiOne cbiRc
  (.seq (.call (some (some (.local, cbiX), none)) fFormerRec [vv cbiP0, vv cbiIr, vv cbiAll, vv cbiNP, vv cbiNz])
  (.seq (.assign .local cbiDn (.load .one (vv cbiD)))
  (idxInsP C (vv cbiDn) (vv cbiX) cbiRi
  (.seq (.call (some (some (.local, cbiF), none)) fFlags [])
    (.return (vv cbiSh1))))))))))))))))

def cbiBody (C : Ctx) : ProgHOL 64 := prologue cbiLocals
  (.seq (.assign .local cbiOm (.load .one (vv cbiSh)))
  (.seq (.assign .local cbiL (.load .one (vv cbiOm)))
  (.ite (.cmp .equal (vv cbiL) (.const 1))
    (.seq (.assign .local cbiP0 (.load .one (.op .add [vv cbiOm, .const 8])))
    (.seq (.assign .local cbiNP (.load .one (.op .add [vv cbiSh, .const 16])))
    (.seq (.assign .local cbiNi (.load .one (.op .add [vv cbiP0, .const 16])))
    (.seq (.assign .local cbiQ (.load .one (vv cbiP0)))
    (.seq (.assign .local cbiK (.op .add [vv cbiNP, vv cbiNi]))
    (.seq (.call (some (some (.local, cbiT), none)) fBlockTele [vv cbiQ, vv cbiK])
    (.seq (.assign .local cbiZ (.load .one (.const (ecell C (C.PO + pinCount + 1)))))
    (.seq (.call (some (some (.local, cbiO), none)) LLeq.fEqv [vv cbiT, vv cbiZ])
    (.ite (.cmp .equal (vv cbiO) (.const 2))
      (.seq (.assign .local cbiIp (.const 1)) (cbiRest C))
      (.seq (.assign .local cbiIp (.const 0)) (cbiRest C)))))))))))
    hang)))

end ConPanqueque.T.Ind
