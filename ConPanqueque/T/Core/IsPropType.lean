import ConPanqueque.T.Core.ProofIrrel
import ConPanqueque.T.Core.FormerSort
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `isPropType`: is a type a proposition

The io-inferred type, head-normalized, is a sort whose level is equal to zero (`lvlEq?`; its fuel decline halts).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def ipyT := ofString "pipy_ipyt"
def ipyA := ofString "pipy_ipya"
def ipyW := ofString "pipy_ipyw"
def ipyU := ofString "pipy_ipyu"
def ipyZ := ofString "pipy_ipyz"
def ipyQ := ofString "pipy_ipyq"
def fIpy := ofString "isPropType"

@[simp] theorem pipy_ipyT_ne_ipyA : ipyT ≠ ipyA := by decide
@[simp] theorem pipy_ipyT_ne_ipyW : ipyT ≠ ipyW := by decide
@[simp] theorem pipy_ipyT_ne_ipyU : ipyT ≠ ipyU := by decide
@[simp] theorem pipy_ipyT_ne_ipyZ : ipyT ≠ ipyZ := by decide
@[simp] theorem pipy_ipyT_ne_ipyQ : ipyT ≠ ipyQ := by decide
@[simp] theorem pipy_ipyT_ne_lFl : ipyT ≠ lFl := by decide
@[simp] theorem pipy_lFl_ne_ipyT : lFl ≠ ipyT := by decide
@[simp] theorem pipy_ipyT_ne_lDh : ipyT ≠ lDh := by decide
@[simp] theorem pipy_lDh_ne_ipyT : lDh ≠ ipyT := by decide
@[simp] theorem pipy_ipyT_ne_lDt : ipyT ≠ lDt := by decide
@[simp] theorem pipy_lDt_ne_ipyT : lDt ≠ ipyT := by decide
@[simp] theorem pipy_ipyT_ne_lDg : ipyT ≠ lDg := by decide
@[simp] theorem pipy_lDg_ne_ipyT : lDg ≠ ipyT := by decide
@[simp] theorem pipy_ipyT_ne_lDi : ipyT ≠ lDi := by decide
@[simp] theorem pipy_lDi_ne_ipyT : lDi ≠ ipyT := by decide
@[simp] theorem pipy_ipyT_ne_lRp : ipyT ≠ lRp := by decide
@[simp] theorem pipy_lRp_ne_ipyT : lRp ≠ ipyT := by decide
@[simp] theorem pipy_ipyT_ne_lRn : ipyT ≠ lRn := by decide
@[simp] theorem pipy_lRn_ne_ipyT : lRn ≠ ipyT := by decide
@[simp] theorem pipy_ipyT_ne_lFle : ipyT ≠ lFle := by decide
@[simp] theorem pipy_lFle_ne_ipyT : lFle ≠ ipyT := by decide
@[simp] theorem pipy_ipyT_ne_lKb : ipyT ≠ lKb := by decide
@[simp] theorem pipy_lKb_ne_ipyT : lKb ≠ ipyT := by decide
@[simp] theorem pipy_ipyT_ne_lDir : ipyT ≠ lDir := by decide
@[simp] theorem pipy_lDir_ne_ipyT : lDir ≠ ipyT := by decide
@[simp] theorem pipy_ipyT_ne_lFln : ipyT ≠ lFln := by decide
@[simp] theorem pipy_lFln_ne_ipyT : lFln ≠ ipyT := by decide
@[simp] theorem pipy_ipyT_ne_lFll : ipyT ≠ lFll := by decide
@[simp] theorem pipy_lFll_ne_ipyT : lFll ≠ ipyT := by decide
@[simp] theorem pipy_ipyT_ne_lFls : ipyT ≠ lFls := by decide
@[simp] theorem pipy_lFls_ne_ipyT : lFls ≠ ipyT := by decide
@[simp] theorem pipy_ipyT_ne_kFu : ipyT ≠ kFu := by decide
@[simp] theorem pipy_kFu_ne_ipyT : kFu ≠ ipyT := by decide
@[simp] theorem pipy_ipyT_ne_kD : ipyT ≠ kD := by decide
@[simp] theorem pipy_kD_ne_ipyT : kD ≠ ipyT := by decide
@[simp] theorem pipy_ipyA_ne_ipyT : ipyA ≠ ipyT := by decide
@[simp] theorem pipy_ipyA_ne_ipyW : ipyA ≠ ipyW := by decide
@[simp] theorem pipy_ipyA_ne_ipyU : ipyA ≠ ipyU := by decide
@[simp] theorem pipy_ipyA_ne_ipyZ : ipyA ≠ ipyZ := by decide
@[simp] theorem pipy_ipyA_ne_ipyQ : ipyA ≠ ipyQ := by decide
@[simp] theorem pipy_ipyA_ne_lFl : ipyA ≠ lFl := by decide
@[simp] theorem pipy_lFl_ne_ipyA : lFl ≠ ipyA := by decide
@[simp] theorem pipy_ipyA_ne_lDh : ipyA ≠ lDh := by decide
@[simp] theorem pipy_lDh_ne_ipyA : lDh ≠ ipyA := by decide
@[simp] theorem pipy_ipyA_ne_lDt : ipyA ≠ lDt := by decide
@[simp] theorem pipy_lDt_ne_ipyA : lDt ≠ ipyA := by decide
@[simp] theorem pipy_ipyA_ne_lDg : ipyA ≠ lDg := by decide
@[simp] theorem pipy_lDg_ne_ipyA : lDg ≠ ipyA := by decide
@[simp] theorem pipy_ipyA_ne_lDi : ipyA ≠ lDi := by decide
@[simp] theorem pipy_lDi_ne_ipyA : lDi ≠ ipyA := by decide
@[simp] theorem pipy_ipyA_ne_lRp : ipyA ≠ lRp := by decide
@[simp] theorem pipy_lRp_ne_ipyA : lRp ≠ ipyA := by decide
@[simp] theorem pipy_ipyA_ne_lRn : ipyA ≠ lRn := by decide
@[simp] theorem pipy_lRn_ne_ipyA : lRn ≠ ipyA := by decide
@[simp] theorem pipy_ipyA_ne_lFle : ipyA ≠ lFle := by decide
@[simp] theorem pipy_lFle_ne_ipyA : lFle ≠ ipyA := by decide
@[simp] theorem pipy_ipyA_ne_lKb : ipyA ≠ lKb := by decide
@[simp] theorem pipy_lKb_ne_ipyA : lKb ≠ ipyA := by decide
@[simp] theorem pipy_ipyA_ne_lDir : ipyA ≠ lDir := by decide
@[simp] theorem pipy_lDir_ne_ipyA : lDir ≠ ipyA := by decide
@[simp] theorem pipy_ipyA_ne_lFln : ipyA ≠ lFln := by decide
@[simp] theorem pipy_lFln_ne_ipyA : lFln ≠ ipyA := by decide
@[simp] theorem pipy_ipyA_ne_lFll : ipyA ≠ lFll := by decide
@[simp] theorem pipy_lFll_ne_ipyA : lFll ≠ ipyA := by decide
@[simp] theorem pipy_ipyA_ne_lFls : ipyA ≠ lFls := by decide
@[simp] theorem pipy_lFls_ne_ipyA : lFls ≠ ipyA := by decide
@[simp] theorem pipy_ipyA_ne_kFu : ipyA ≠ kFu := by decide
@[simp] theorem pipy_kFu_ne_ipyA : kFu ≠ ipyA := by decide
@[simp] theorem pipy_ipyA_ne_kD : ipyA ≠ kD := by decide
@[simp] theorem pipy_kD_ne_ipyA : kD ≠ ipyA := by decide
@[simp] theorem pipy_ipyW_ne_ipyT : ipyW ≠ ipyT := by decide
@[simp] theorem pipy_ipyW_ne_ipyA : ipyW ≠ ipyA := by decide
@[simp] theorem pipy_ipyW_ne_ipyU : ipyW ≠ ipyU := by decide
@[simp] theorem pipy_ipyW_ne_ipyZ : ipyW ≠ ipyZ := by decide
@[simp] theorem pipy_ipyW_ne_ipyQ : ipyW ≠ ipyQ := by decide
@[simp] theorem pipy_ipyW_ne_lFl : ipyW ≠ lFl := by decide
@[simp] theorem pipy_lFl_ne_ipyW : lFl ≠ ipyW := by decide
@[simp] theorem pipy_ipyW_ne_lDh : ipyW ≠ lDh := by decide
@[simp] theorem pipy_lDh_ne_ipyW : lDh ≠ ipyW := by decide
@[simp] theorem pipy_ipyW_ne_lDt : ipyW ≠ lDt := by decide
@[simp] theorem pipy_lDt_ne_ipyW : lDt ≠ ipyW := by decide
@[simp] theorem pipy_ipyW_ne_lDg : ipyW ≠ lDg := by decide
@[simp] theorem pipy_lDg_ne_ipyW : lDg ≠ ipyW := by decide
@[simp] theorem pipy_ipyW_ne_lDi : ipyW ≠ lDi := by decide
@[simp] theorem pipy_lDi_ne_ipyW : lDi ≠ ipyW := by decide
@[simp] theorem pipy_ipyW_ne_lRp : ipyW ≠ lRp := by decide
@[simp] theorem pipy_lRp_ne_ipyW : lRp ≠ ipyW := by decide
@[simp] theorem pipy_ipyW_ne_lRn : ipyW ≠ lRn := by decide
@[simp] theorem pipy_lRn_ne_ipyW : lRn ≠ ipyW := by decide
@[simp] theorem pipy_ipyW_ne_lFle : ipyW ≠ lFle := by decide
@[simp] theorem pipy_lFle_ne_ipyW : lFle ≠ ipyW := by decide
@[simp] theorem pipy_ipyW_ne_lKb : ipyW ≠ lKb := by decide
@[simp] theorem pipy_lKb_ne_ipyW : lKb ≠ ipyW := by decide
@[simp] theorem pipy_ipyW_ne_lDir : ipyW ≠ lDir := by decide
@[simp] theorem pipy_lDir_ne_ipyW : lDir ≠ ipyW := by decide
@[simp] theorem pipy_ipyW_ne_lFln : ipyW ≠ lFln := by decide
@[simp] theorem pipy_lFln_ne_ipyW : lFln ≠ ipyW := by decide
@[simp] theorem pipy_ipyW_ne_lFll : ipyW ≠ lFll := by decide
@[simp] theorem pipy_lFll_ne_ipyW : lFll ≠ ipyW := by decide
@[simp] theorem pipy_ipyW_ne_lFls : ipyW ≠ lFls := by decide
@[simp] theorem pipy_lFls_ne_ipyW : lFls ≠ ipyW := by decide
@[simp] theorem pipy_ipyW_ne_kFu : ipyW ≠ kFu := by decide
@[simp] theorem pipy_kFu_ne_ipyW : kFu ≠ ipyW := by decide
@[simp] theorem pipy_ipyW_ne_kD : ipyW ≠ kD := by decide
@[simp] theorem pipy_kD_ne_ipyW : kD ≠ ipyW := by decide
@[simp] theorem pipy_ipyU_ne_ipyT : ipyU ≠ ipyT := by decide
@[simp] theorem pipy_ipyU_ne_ipyA : ipyU ≠ ipyA := by decide
@[simp] theorem pipy_ipyU_ne_ipyW : ipyU ≠ ipyW := by decide
@[simp] theorem pipy_ipyU_ne_ipyZ : ipyU ≠ ipyZ := by decide
@[simp] theorem pipy_ipyU_ne_ipyQ : ipyU ≠ ipyQ := by decide
@[simp] theorem pipy_ipyU_ne_lFl : ipyU ≠ lFl := by decide
@[simp] theorem pipy_lFl_ne_ipyU : lFl ≠ ipyU := by decide
@[simp] theorem pipy_ipyU_ne_lDh : ipyU ≠ lDh := by decide
@[simp] theorem pipy_lDh_ne_ipyU : lDh ≠ ipyU := by decide
@[simp] theorem pipy_ipyU_ne_lDt : ipyU ≠ lDt := by decide
@[simp] theorem pipy_lDt_ne_ipyU : lDt ≠ ipyU := by decide
@[simp] theorem pipy_ipyU_ne_lDg : ipyU ≠ lDg := by decide
@[simp] theorem pipy_lDg_ne_ipyU : lDg ≠ ipyU := by decide
@[simp] theorem pipy_ipyU_ne_lDi : ipyU ≠ lDi := by decide
@[simp] theorem pipy_lDi_ne_ipyU : lDi ≠ ipyU := by decide
@[simp] theorem pipy_ipyU_ne_lRp : ipyU ≠ lRp := by decide
@[simp] theorem pipy_lRp_ne_ipyU : lRp ≠ ipyU := by decide
@[simp] theorem pipy_ipyU_ne_lRn : ipyU ≠ lRn := by decide
@[simp] theorem pipy_lRn_ne_ipyU : lRn ≠ ipyU := by decide
@[simp] theorem pipy_ipyU_ne_lFle : ipyU ≠ lFle := by decide
@[simp] theorem pipy_lFle_ne_ipyU : lFle ≠ ipyU := by decide
@[simp] theorem pipy_ipyU_ne_lKb : ipyU ≠ lKb := by decide
@[simp] theorem pipy_lKb_ne_ipyU : lKb ≠ ipyU := by decide
@[simp] theorem pipy_ipyU_ne_lDir : ipyU ≠ lDir := by decide
@[simp] theorem pipy_lDir_ne_ipyU : lDir ≠ ipyU := by decide
@[simp] theorem pipy_ipyU_ne_lFln : ipyU ≠ lFln := by decide
@[simp] theorem pipy_lFln_ne_ipyU : lFln ≠ ipyU := by decide
@[simp] theorem pipy_ipyU_ne_lFll : ipyU ≠ lFll := by decide
@[simp] theorem pipy_lFll_ne_ipyU : lFll ≠ ipyU := by decide
@[simp] theorem pipy_ipyU_ne_lFls : ipyU ≠ lFls := by decide
@[simp] theorem pipy_lFls_ne_ipyU : lFls ≠ ipyU := by decide
@[simp] theorem pipy_ipyU_ne_kFu : ipyU ≠ kFu := by decide
@[simp] theorem pipy_kFu_ne_ipyU : kFu ≠ ipyU := by decide
@[simp] theorem pipy_ipyU_ne_kD : ipyU ≠ kD := by decide
@[simp] theorem pipy_kD_ne_ipyU : kD ≠ ipyU := by decide
@[simp] theorem pipy_ipyZ_ne_ipyT : ipyZ ≠ ipyT := by decide
@[simp] theorem pipy_ipyZ_ne_ipyA : ipyZ ≠ ipyA := by decide
@[simp] theorem pipy_ipyZ_ne_ipyW : ipyZ ≠ ipyW := by decide
@[simp] theorem pipy_ipyZ_ne_ipyU : ipyZ ≠ ipyU := by decide
@[simp] theorem pipy_ipyZ_ne_ipyQ : ipyZ ≠ ipyQ := by decide
@[simp] theorem pipy_ipyZ_ne_lFl : ipyZ ≠ lFl := by decide
@[simp] theorem pipy_lFl_ne_ipyZ : lFl ≠ ipyZ := by decide
@[simp] theorem pipy_ipyZ_ne_lDh : ipyZ ≠ lDh := by decide
@[simp] theorem pipy_lDh_ne_ipyZ : lDh ≠ ipyZ := by decide
@[simp] theorem pipy_ipyZ_ne_lDt : ipyZ ≠ lDt := by decide
@[simp] theorem pipy_lDt_ne_ipyZ : lDt ≠ ipyZ := by decide
@[simp] theorem pipy_ipyZ_ne_lDg : ipyZ ≠ lDg := by decide
@[simp] theorem pipy_lDg_ne_ipyZ : lDg ≠ ipyZ := by decide
@[simp] theorem pipy_ipyZ_ne_lDi : ipyZ ≠ lDi := by decide
@[simp] theorem pipy_lDi_ne_ipyZ : lDi ≠ ipyZ := by decide
@[simp] theorem pipy_ipyZ_ne_lRp : ipyZ ≠ lRp := by decide
@[simp] theorem pipy_lRp_ne_ipyZ : lRp ≠ ipyZ := by decide
@[simp] theorem pipy_ipyZ_ne_lRn : ipyZ ≠ lRn := by decide
@[simp] theorem pipy_lRn_ne_ipyZ : lRn ≠ ipyZ := by decide
@[simp] theorem pipy_ipyZ_ne_lFle : ipyZ ≠ lFle := by decide
@[simp] theorem pipy_lFle_ne_ipyZ : lFle ≠ ipyZ := by decide
@[simp] theorem pipy_ipyZ_ne_lKb : ipyZ ≠ lKb := by decide
@[simp] theorem pipy_lKb_ne_ipyZ : lKb ≠ ipyZ := by decide
@[simp] theorem pipy_ipyZ_ne_lDir : ipyZ ≠ lDir := by decide
@[simp] theorem pipy_lDir_ne_ipyZ : lDir ≠ ipyZ := by decide
@[simp] theorem pipy_ipyZ_ne_lFln : ipyZ ≠ lFln := by decide
@[simp] theorem pipy_lFln_ne_ipyZ : lFln ≠ ipyZ := by decide
@[simp] theorem pipy_ipyZ_ne_lFll : ipyZ ≠ lFll := by decide
@[simp] theorem pipy_lFll_ne_ipyZ : lFll ≠ ipyZ := by decide
@[simp] theorem pipy_ipyZ_ne_lFls : ipyZ ≠ lFls := by decide
@[simp] theorem pipy_lFls_ne_ipyZ : lFls ≠ ipyZ := by decide
@[simp] theorem pipy_ipyZ_ne_kFu : ipyZ ≠ kFu := by decide
@[simp] theorem pipy_kFu_ne_ipyZ : kFu ≠ ipyZ := by decide
@[simp] theorem pipy_ipyZ_ne_kD : ipyZ ≠ kD := by decide
@[simp] theorem pipy_kD_ne_ipyZ : kD ≠ ipyZ := by decide
@[simp] theorem pipy_ipyQ_ne_ipyT : ipyQ ≠ ipyT := by decide
@[simp] theorem pipy_ipyQ_ne_ipyA : ipyQ ≠ ipyA := by decide
@[simp] theorem pipy_ipyQ_ne_ipyW : ipyQ ≠ ipyW := by decide
@[simp] theorem pipy_ipyQ_ne_ipyU : ipyQ ≠ ipyU := by decide
@[simp] theorem pipy_ipyQ_ne_ipyZ : ipyQ ≠ ipyZ := by decide
@[simp] theorem pipy_ipyQ_ne_lFl : ipyQ ≠ lFl := by decide
@[simp] theorem pipy_lFl_ne_ipyQ : lFl ≠ ipyQ := by decide
@[simp] theorem pipy_ipyQ_ne_lDh : ipyQ ≠ lDh := by decide
@[simp] theorem pipy_lDh_ne_ipyQ : lDh ≠ ipyQ := by decide
@[simp] theorem pipy_ipyQ_ne_lDt : ipyQ ≠ lDt := by decide
@[simp] theorem pipy_lDt_ne_ipyQ : lDt ≠ ipyQ := by decide
@[simp] theorem pipy_ipyQ_ne_lDg : ipyQ ≠ lDg := by decide
@[simp] theorem pipy_lDg_ne_ipyQ : lDg ≠ ipyQ := by decide
@[simp] theorem pipy_ipyQ_ne_lDi : ipyQ ≠ lDi := by decide
@[simp] theorem pipy_lDi_ne_ipyQ : lDi ≠ ipyQ := by decide
@[simp] theorem pipy_ipyQ_ne_lRp : ipyQ ≠ lRp := by decide
@[simp] theorem pipy_lRp_ne_ipyQ : lRp ≠ ipyQ := by decide
@[simp] theorem pipy_ipyQ_ne_lRn : ipyQ ≠ lRn := by decide
@[simp] theorem pipy_lRn_ne_ipyQ : lRn ≠ ipyQ := by decide
@[simp] theorem pipy_ipyQ_ne_lFle : ipyQ ≠ lFle := by decide
@[simp] theorem pipy_lFle_ne_ipyQ : lFle ≠ ipyQ := by decide
@[simp] theorem pipy_ipyQ_ne_lKb : ipyQ ≠ lKb := by decide
@[simp] theorem pipy_lKb_ne_ipyQ : lKb ≠ ipyQ := by decide
@[simp] theorem pipy_ipyQ_ne_lDir : ipyQ ≠ lDir := by decide
@[simp] theorem pipy_lDir_ne_ipyQ : lDir ≠ ipyQ := by decide
@[simp] theorem pipy_ipyQ_ne_lFln : ipyQ ≠ lFln := by decide
@[simp] theorem pipy_lFln_ne_ipyQ : lFln ≠ ipyQ := by decide
@[simp] theorem pipy_ipyQ_ne_lFll : ipyQ ≠ lFll := by decide
@[simp] theorem pipy_lFll_ne_ipyQ : lFll ≠ ipyQ := by decide
@[simp] theorem pipy_ipyQ_ne_lFls : ipyQ ≠ lFls := by decide
@[simp] theorem pipy_lFls_ne_ipyQ : lFls ≠ ipyQ := by decide
@[simp] theorem pipy_ipyQ_ne_kFu : ipyQ ≠ kFu := by decide
@[simp] theorem pipy_kFu_ne_ipyQ : kFu ≠ ipyQ := by decide
@[simp] theorem pipy_ipyQ_ne_kD : ipyQ ≠ kD := by decide
@[simp] theorem pipy_kD_ne_ipyQ : kD ≠ ipyQ := by decide

def ipyParams : List MlS := [kFu, kD, ipyT]
def ipyLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, ipyA, ipyW, ipyU, ipyZ, ipyQ]
def ipyBody (C : Ctx) : ProgHOL 64 := prologue ipyLocals (.seq (.call (some (some (.local, ipyA), none)) fIO [(vv kFu), (vv kD), (vv ipyT)]) (.seq (.call (some (some (.local, ipyW), none)) fW [(vv kFu), (vv kD), (vv ipyA)]) (.ite (tagIsE ipyW 2) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv ipyW)) (.seq eViewP (.seq (.assign .local ipyU (.load .one (vv lRp))) (.seq (.assign .local ipyZ (.load .one (.const (ecell C (C.PO + pinCount + 1))))) (.seq (.call (some (some (.local, ipyQ), none)) LLeq.fEqv [(vv ipyU), (vv ipyZ)]) (.ite (.cmp .equal (vv ipyQ) (.const 0)) hang (.return (.op .sub [(vv ipyQ), (.const 1)]))))))))) (.return (.const 0)))))

structure IpyCodes (C : Ctx) : Prop where
  io : C.code.lookup fIO = some (pmap kParams, inferIOE C fIOB, .one)
  w : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one)
  e : C.code.lookup LLeq.fEqv = some ([(LEq.pLa, .one), (LEq.pLb, .one)], LLeq.eqvBody, .one)

section
variable {σ : Type}

theorem ipy_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) (hok : CtxOK C) (hc : IpyCodes C)
    (s : AState) (d : Nat) (T : EIdx)
    (hIO : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ e', Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e'] (inferIOE C fIOB) s1 ((knot mode C n).inferIO d e')
      (PostK (ctxH C H)))
    (hW : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ e', Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d e')
      (PostK (ctxH C H)))
    (hLE : ∀ (H : List (BitVec 64)) s1 (u v : LIdx), C.H <+: H → (denoteL s1.store.ls u).isSome = true →
      (denoteL s1.store.ls v).isSome = true →
      SpecR (σ := σ) (Pre (ctxH C H) s1 [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s1 (lvlEq? u v)
        (LLeq.PostOB (ctxH C H))) :
    ∀ (H : List (BitVec 64)), C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (ipyParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW T]))
        (ipyBody C) s (isPropType (knot mode C n) d T) (PostB (ctxH C H)) := by
  intro H hpH
  refine specR_prologue (Knot.postB_locals _) (Knot.params_none _ ipyLocals ipyParams _ (by decide) (by decide)) ?_
  unfold isPropType
  refine Big.specR_callKC (C := ctxH C H) ipyA fIO kParams [vv kFu, vv kD, vv ipyT] (inferIOE C fIOB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW T] (by decide) rfl (by decide) hc.io
    ⟨by simp +decide [Env.get, ipyParams, ctxEnv], by simp +decide [Env.get, ipyParams, ctxEnv], by simp +decide [Env.get, ipyParams, ctxEnv], trivial⟩ (hIO H s hpH T) (fun ta s1 H1 hp1 _ => ?_)
  have hp01 : C.H <+: H1 := hpH.trans hp1
  refine Big.specR_callKC (C := ctxH C H1) ipyW fW kParams [vv kFu, vv kD, vv ipyA] (whnfE C fWB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ta] (by decide) rfl (by decide) hc.w
    ⟨by simp +decide [Env.get, ipyParams, ctxEnv], by simp +decide [Env.get, ipyParams, ctxEnv], by simp, trivial⟩ (hW H1 s1 hp01 ta) (fun w s2 H2 hp2 _ => ?_)
  have hp02 : C.H <+: H2 := hp01.trans hp2
  refine Knot.specR_tagIteV ipyW w 2 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
  swap
  · rw [if_neg (show ¬ (w.tag == ETag.sort) = true by simpa [ETag.sort] using htg)]
    exact specR_returnI _ (boolW false) (by simp [boolW]; rfl)
      (fun t ht => ⟨H2, hp1.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [if_pos (show (w.tag == ETag.sort) = true by simp [htg, ETag.sort])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv ipyW) (Enc.idxW w) (by decide) (by simp) ?_
  refine specR_viewP (C := ctxH C H2) w (by simp) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
    (fun v P hv htn _ => ?_)
  have h2 : v.tagN = 2 := by rw [htn, htg]; rfl
  obtain ⟨uT, rfl⟩ : ∃ u, v = .sort u := by cases v <;> simp [ENodeView.tagN] at h2 ⊢
  have hvs : s2.store.viewSort w = some uT := viewSort_of_view (by rw [htg]; rfl) hv
  refine specR_runBind (show ConRon.Arena.viewSort w s2 = .ok (some uT, s2) by
    show Except.ok (s2.store.viewSort w, s2) = _; rw [hvs]) ?_
  dsimp only
  refine specR_loadI' ipyU (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW uT) (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encSort] using wordsAt_mem0 P (Enc.idxW uT) [] []) ?_
  refine specR_dropM ?_
  have hokX := ctxOK_H hok H2
  refine specR_pinXI (C := ctxH C H2) hokX pinZeroLevel 1 C.pins.zeroLevel _
    (fun s hp => pinZeroLevel_run (C := ctxH C H2) hokX hp) (pin_zeroLevel_cell hokX) ipyZ (by decide) ?_
  show SpecR _ _ _ (lvlEq? uT C.pins.zeroLevel >>= fun o => liftFueled "level comparison" o) _
  refine specR_congr (m' := lvlEq? uT C.pins.zeroLevel >>= fun o => liftFueled "level comparison" o >>= fun r => pure r)
    (by simp) ?_
  refine specR_callNIH (C := ctxH C H2) ipyQ LLeq.fEqv [LEq.pLa, LEq.pLb] [vv ipyU, vv ipyZ] LLeq.eqvBody
    [Enc.idxW uT, Enc.idxW C.pins.zeroLevel] (by decide) rfl (by decide) hc.e ⟨by simp, by simp <;> rfl, trivial⟩
    (LLeq.PostOB (ctxH C H2)) (fun o w _ H' => H' = H2 ∧ w = LLeq.obW o)
    (fun o w s' st ⟨hw, hsr⟩ => ⟨H2, List.prefix_refl _, ⟨rfl, hw⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [LEq.pLa, LEq.pLb] _ rfl hlk)
      (hLE H2 s2 uT C.pins.zeroLevel hp02 (sr_sortSome hu hv) (sr_zeroSome (C := ctxH C H2) hu))) (fun o w s3 H3 _ ⟨eH, hw⟩ => ?_)
  subst H3; subst hw
  rcases o with _ | ok
  · refine specR_ifI _ 1 (by simp [sev, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI)
      (fun h => absurd h (by decide))
  have hne : LLeq.obW (some ok) ≠ 0 := by cases ok <;> decide
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
  simp only [liftFueled, pure_bind]
  exact specR_returnI _ (boolW ok) (by simp [sev]; exact obW_sub1 ok)
    (fun t ht => ⟨H2, hp1.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
