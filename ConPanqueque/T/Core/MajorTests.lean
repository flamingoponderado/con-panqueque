import ConPanqueque.T.Core.CtorView
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# The major premise's two read-only tests

`isStrLit` (a string literal) and `isNatSuccApp` (an application of the level-free `Nat.succ`), answering `boolW`.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

theorem viewLit_of_view {st : EStore} {i : EIdx} {l : ConLeche.Literal}
    (htg : i.tag = ETag.lit) (h : st.view i = some (.lit l)) : st.viewLit i = some l := by
  cases hc : st.viewLit i with
  | some l' =>
    have := ConRon.Bridge.view_of_viewLit htg hc
    rw [h] at this; cases this; rfl
  | none =>
    exfalso
    revert h hc
    simp only [EStore.view, EStore.viewLit, EStore.persGetLit]
    split <;> [skip; split] <;> simp [ETables.get, ETables.getLit, htg] <;>
      (try simp only [show ETag.lit ≠ ETag.bvar by decide, show ETag.lit ≠ ETag.fvar by decide,
        show ETag.lit ≠ ETag.sort by decide, show ETag.lit ≠ ETag.const by decide, show ETag.lit ≠ ETag.app by decide,
        show ETag.lit ≠ ETag.lam by decide, show ETag.lit ≠ ETag.forallE by decide, show ETag.lit ≠ ETag.letE by decide,
        ite_false]) <;> intro h1 h2 <;> (try rw [Option.map_eq_none_iff] at h2) <;> (try rw [h2] at h1) <;> simp at h1

theorem sev_eqIdxB {k : IdxKind} {Γ : Env} {a b : ExpHOL 64} {x y : Idx k} (ha : sev Γ a = some (Enc.idxW x))
    (hb : sev Γ b = some (Enc.idxW y)) : sev Γ (.cmp .equal a b) = some (boolW (x == y)) := by
  simp only [sev, ha, hb]
  by_cases he : x = y
  · subst he; simp [boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  · have : Enc.idxW x ≠ Enc.idxW y := fun e => he (Enc.idxW_inj e)
    simp [boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this, he]

def isH := ofString "ish"
def isW := ofString "isw"
def nsE := ofString "nse"
def nsF := ofString "nsf"
def nsC := ofString "nsc"
def nsU := ofString "nsu"
def nsL := ofString "nsl"
def nsN := ofString "nsn"
def fIsl := ofString "isStrLit"
def fNs := ofString "isNatSuccApp"

@[simp] theorem mt_isH_ne_isW : isH ≠ isW := by decide
@[simp] theorem mt_isH_ne_nsE : isH ≠ nsE := by decide
@[simp] theorem mt_isH_ne_nsF : isH ≠ nsF := by decide
@[simp] theorem mt_isH_ne_nsC : isH ≠ nsC := by decide
@[simp] theorem mt_isH_ne_nsU : isH ≠ nsU := by decide
@[simp] theorem mt_isH_ne_nsL : isH ≠ nsL := by decide
@[simp] theorem mt_isH_ne_nsN : isH ≠ nsN := by decide
@[simp] theorem mt_isH_ne_lFl : isH ≠ lFl := by decide
@[simp] theorem mt_lFl_ne_isH : lFl ≠ isH := by decide
@[simp] theorem mt_isH_ne_lDh : isH ≠ lDh := by decide
@[simp] theorem mt_lDh_ne_isH : lDh ≠ isH := by decide
@[simp] theorem mt_isH_ne_lDt : isH ≠ lDt := by decide
@[simp] theorem mt_lDt_ne_isH : lDt ≠ isH := by decide
@[simp] theorem mt_isH_ne_lDg : isH ≠ lDg := by decide
@[simp] theorem mt_lDg_ne_isH : lDg ≠ isH := by decide
@[simp] theorem mt_isH_ne_lDi : isH ≠ lDi := by decide
@[simp] theorem mt_lDi_ne_isH : lDi ≠ isH := by decide
@[simp] theorem mt_isH_ne_lRp : isH ≠ lRp := by decide
@[simp] theorem mt_lRp_ne_isH : lRp ≠ isH := by decide
@[simp] theorem mt_isH_ne_lRn : isH ≠ lRn := by decide
@[simp] theorem mt_lRn_ne_isH : lRn ≠ isH := by decide
@[simp] theorem mt_isH_ne_lFle : isH ≠ lFle := by decide
@[simp] theorem mt_lFle_ne_isH : lFle ≠ isH := by decide
@[simp] theorem mt_isH_ne_lDir : isH ≠ lDir := by decide
@[simp] theorem mt_lDir_ne_isH : lDir ≠ isH := by decide
@[simp] theorem mt_isH_ne_lKb : isH ≠ lKb := by decide
@[simp] theorem mt_lKb_ne_isH : lKb ≠ isH := by decide
@[simp] theorem mt_isW_ne_isH : isW ≠ isH := by decide
@[simp] theorem mt_isW_ne_nsE : isW ≠ nsE := by decide
@[simp] theorem mt_isW_ne_nsF : isW ≠ nsF := by decide
@[simp] theorem mt_isW_ne_nsC : isW ≠ nsC := by decide
@[simp] theorem mt_isW_ne_nsU : isW ≠ nsU := by decide
@[simp] theorem mt_isW_ne_nsL : isW ≠ nsL := by decide
@[simp] theorem mt_isW_ne_nsN : isW ≠ nsN := by decide
@[simp] theorem mt_isW_ne_lFl : isW ≠ lFl := by decide
@[simp] theorem mt_lFl_ne_isW : lFl ≠ isW := by decide
@[simp] theorem mt_isW_ne_lDh : isW ≠ lDh := by decide
@[simp] theorem mt_lDh_ne_isW : lDh ≠ isW := by decide
@[simp] theorem mt_isW_ne_lDt : isW ≠ lDt := by decide
@[simp] theorem mt_lDt_ne_isW : lDt ≠ isW := by decide
@[simp] theorem mt_isW_ne_lDg : isW ≠ lDg := by decide
@[simp] theorem mt_lDg_ne_isW : lDg ≠ isW := by decide
@[simp] theorem mt_isW_ne_lDi : isW ≠ lDi := by decide
@[simp] theorem mt_lDi_ne_isW : lDi ≠ isW := by decide
@[simp] theorem mt_isW_ne_lRp : isW ≠ lRp := by decide
@[simp] theorem mt_lRp_ne_isW : lRp ≠ isW := by decide
@[simp] theorem mt_isW_ne_lRn : isW ≠ lRn := by decide
@[simp] theorem mt_lRn_ne_isW : lRn ≠ isW := by decide
@[simp] theorem mt_isW_ne_lFle : isW ≠ lFle := by decide
@[simp] theorem mt_lFle_ne_isW : lFle ≠ isW := by decide
@[simp] theorem mt_isW_ne_lDir : isW ≠ lDir := by decide
@[simp] theorem mt_lDir_ne_isW : lDir ≠ isW := by decide
@[simp] theorem mt_isW_ne_lKb : isW ≠ lKb := by decide
@[simp] theorem mt_lKb_ne_isW : lKb ≠ isW := by decide
@[simp] theorem mt_nsE_ne_isH : nsE ≠ isH := by decide
@[simp] theorem mt_nsE_ne_isW : nsE ≠ isW := by decide
@[simp] theorem mt_nsE_ne_nsF : nsE ≠ nsF := by decide
@[simp] theorem mt_nsE_ne_nsC : nsE ≠ nsC := by decide
@[simp] theorem mt_nsE_ne_nsU : nsE ≠ nsU := by decide
@[simp] theorem mt_nsE_ne_nsL : nsE ≠ nsL := by decide
@[simp] theorem mt_nsE_ne_nsN : nsE ≠ nsN := by decide
@[simp] theorem mt_nsE_ne_lFl : nsE ≠ lFl := by decide
@[simp] theorem mt_lFl_ne_nsE : lFl ≠ nsE := by decide
@[simp] theorem mt_nsE_ne_lDh : nsE ≠ lDh := by decide
@[simp] theorem mt_lDh_ne_nsE : lDh ≠ nsE := by decide
@[simp] theorem mt_nsE_ne_lDt : nsE ≠ lDt := by decide
@[simp] theorem mt_lDt_ne_nsE : lDt ≠ nsE := by decide
@[simp] theorem mt_nsE_ne_lDg : nsE ≠ lDg := by decide
@[simp] theorem mt_lDg_ne_nsE : lDg ≠ nsE := by decide
@[simp] theorem mt_nsE_ne_lDi : nsE ≠ lDi := by decide
@[simp] theorem mt_lDi_ne_nsE : lDi ≠ nsE := by decide
@[simp] theorem mt_nsE_ne_lRp : nsE ≠ lRp := by decide
@[simp] theorem mt_lRp_ne_nsE : lRp ≠ nsE := by decide
@[simp] theorem mt_nsE_ne_lRn : nsE ≠ lRn := by decide
@[simp] theorem mt_lRn_ne_nsE : lRn ≠ nsE := by decide
@[simp] theorem mt_nsE_ne_lFle : nsE ≠ lFle := by decide
@[simp] theorem mt_lFle_ne_nsE : lFle ≠ nsE := by decide
@[simp] theorem mt_nsE_ne_lDir : nsE ≠ lDir := by decide
@[simp] theorem mt_lDir_ne_nsE : lDir ≠ nsE := by decide
@[simp] theorem mt_nsE_ne_lKb : nsE ≠ lKb := by decide
@[simp] theorem mt_lKb_ne_nsE : lKb ≠ nsE := by decide
@[simp] theorem mt_nsF_ne_isH : nsF ≠ isH := by decide
@[simp] theorem mt_nsF_ne_isW : nsF ≠ isW := by decide
@[simp] theorem mt_nsF_ne_nsE : nsF ≠ nsE := by decide
@[simp] theorem mt_nsF_ne_nsC : nsF ≠ nsC := by decide
@[simp] theorem mt_nsF_ne_nsU : nsF ≠ nsU := by decide
@[simp] theorem mt_nsF_ne_nsL : nsF ≠ nsL := by decide
@[simp] theorem mt_nsF_ne_nsN : nsF ≠ nsN := by decide
@[simp] theorem mt_nsF_ne_lFl : nsF ≠ lFl := by decide
@[simp] theorem mt_lFl_ne_nsF : lFl ≠ nsF := by decide
@[simp] theorem mt_nsF_ne_lDh : nsF ≠ lDh := by decide
@[simp] theorem mt_lDh_ne_nsF : lDh ≠ nsF := by decide
@[simp] theorem mt_nsF_ne_lDt : nsF ≠ lDt := by decide
@[simp] theorem mt_lDt_ne_nsF : lDt ≠ nsF := by decide
@[simp] theorem mt_nsF_ne_lDg : nsF ≠ lDg := by decide
@[simp] theorem mt_lDg_ne_nsF : lDg ≠ nsF := by decide
@[simp] theorem mt_nsF_ne_lDi : nsF ≠ lDi := by decide
@[simp] theorem mt_lDi_ne_nsF : lDi ≠ nsF := by decide
@[simp] theorem mt_nsF_ne_lRp : nsF ≠ lRp := by decide
@[simp] theorem mt_lRp_ne_nsF : lRp ≠ nsF := by decide
@[simp] theorem mt_nsF_ne_lRn : nsF ≠ lRn := by decide
@[simp] theorem mt_lRn_ne_nsF : lRn ≠ nsF := by decide
@[simp] theorem mt_nsF_ne_lFle : nsF ≠ lFle := by decide
@[simp] theorem mt_lFle_ne_nsF : lFle ≠ nsF := by decide
@[simp] theorem mt_nsF_ne_lDir : nsF ≠ lDir := by decide
@[simp] theorem mt_lDir_ne_nsF : lDir ≠ nsF := by decide
@[simp] theorem mt_nsF_ne_lKb : nsF ≠ lKb := by decide
@[simp] theorem mt_lKb_ne_nsF : lKb ≠ nsF := by decide
@[simp] theorem mt_nsC_ne_isH : nsC ≠ isH := by decide
@[simp] theorem mt_nsC_ne_isW : nsC ≠ isW := by decide
@[simp] theorem mt_nsC_ne_nsE : nsC ≠ nsE := by decide
@[simp] theorem mt_nsC_ne_nsF : nsC ≠ nsF := by decide
@[simp] theorem mt_nsC_ne_nsU : nsC ≠ nsU := by decide
@[simp] theorem mt_nsC_ne_nsL : nsC ≠ nsL := by decide
@[simp] theorem mt_nsC_ne_nsN : nsC ≠ nsN := by decide
@[simp] theorem mt_nsC_ne_lFl : nsC ≠ lFl := by decide
@[simp] theorem mt_lFl_ne_nsC : lFl ≠ nsC := by decide
@[simp] theorem mt_nsC_ne_lDh : nsC ≠ lDh := by decide
@[simp] theorem mt_lDh_ne_nsC : lDh ≠ nsC := by decide
@[simp] theorem mt_nsC_ne_lDt : nsC ≠ lDt := by decide
@[simp] theorem mt_lDt_ne_nsC : lDt ≠ nsC := by decide
@[simp] theorem mt_nsC_ne_lDg : nsC ≠ lDg := by decide
@[simp] theorem mt_lDg_ne_nsC : lDg ≠ nsC := by decide
@[simp] theorem mt_nsC_ne_lDi : nsC ≠ lDi := by decide
@[simp] theorem mt_lDi_ne_nsC : lDi ≠ nsC := by decide
@[simp] theorem mt_nsC_ne_lRp : nsC ≠ lRp := by decide
@[simp] theorem mt_lRp_ne_nsC : lRp ≠ nsC := by decide
@[simp] theorem mt_nsC_ne_lRn : nsC ≠ lRn := by decide
@[simp] theorem mt_lRn_ne_nsC : lRn ≠ nsC := by decide
@[simp] theorem mt_nsC_ne_lFle : nsC ≠ lFle := by decide
@[simp] theorem mt_lFle_ne_nsC : lFle ≠ nsC := by decide
@[simp] theorem mt_nsC_ne_lDir : nsC ≠ lDir := by decide
@[simp] theorem mt_lDir_ne_nsC : lDir ≠ nsC := by decide
@[simp] theorem mt_nsC_ne_lKb : nsC ≠ lKb := by decide
@[simp] theorem mt_lKb_ne_nsC : lKb ≠ nsC := by decide
@[simp] theorem mt_nsU_ne_isH : nsU ≠ isH := by decide
@[simp] theorem mt_nsU_ne_isW : nsU ≠ isW := by decide
@[simp] theorem mt_nsU_ne_nsE : nsU ≠ nsE := by decide
@[simp] theorem mt_nsU_ne_nsF : nsU ≠ nsF := by decide
@[simp] theorem mt_nsU_ne_nsC : nsU ≠ nsC := by decide
@[simp] theorem mt_nsU_ne_nsL : nsU ≠ nsL := by decide
@[simp] theorem mt_nsU_ne_nsN : nsU ≠ nsN := by decide
@[simp] theorem mt_nsU_ne_lFl : nsU ≠ lFl := by decide
@[simp] theorem mt_lFl_ne_nsU : lFl ≠ nsU := by decide
@[simp] theorem mt_nsU_ne_lDh : nsU ≠ lDh := by decide
@[simp] theorem mt_lDh_ne_nsU : lDh ≠ nsU := by decide
@[simp] theorem mt_nsU_ne_lDt : nsU ≠ lDt := by decide
@[simp] theorem mt_lDt_ne_nsU : lDt ≠ nsU := by decide
@[simp] theorem mt_nsU_ne_lDg : nsU ≠ lDg := by decide
@[simp] theorem mt_lDg_ne_nsU : lDg ≠ nsU := by decide
@[simp] theorem mt_nsU_ne_lDi : nsU ≠ lDi := by decide
@[simp] theorem mt_lDi_ne_nsU : lDi ≠ nsU := by decide
@[simp] theorem mt_nsU_ne_lRp : nsU ≠ lRp := by decide
@[simp] theorem mt_lRp_ne_nsU : lRp ≠ nsU := by decide
@[simp] theorem mt_nsU_ne_lRn : nsU ≠ lRn := by decide
@[simp] theorem mt_lRn_ne_nsU : lRn ≠ nsU := by decide
@[simp] theorem mt_nsU_ne_lFle : nsU ≠ lFle := by decide
@[simp] theorem mt_lFle_ne_nsU : lFle ≠ nsU := by decide
@[simp] theorem mt_nsU_ne_lDir : nsU ≠ lDir := by decide
@[simp] theorem mt_lDir_ne_nsU : lDir ≠ nsU := by decide
@[simp] theorem mt_nsU_ne_lKb : nsU ≠ lKb := by decide
@[simp] theorem mt_lKb_ne_nsU : lKb ≠ nsU := by decide
@[simp] theorem mt_nsL_ne_isH : nsL ≠ isH := by decide
@[simp] theorem mt_nsL_ne_isW : nsL ≠ isW := by decide
@[simp] theorem mt_nsL_ne_nsE : nsL ≠ nsE := by decide
@[simp] theorem mt_nsL_ne_nsF : nsL ≠ nsF := by decide
@[simp] theorem mt_nsL_ne_nsC : nsL ≠ nsC := by decide
@[simp] theorem mt_nsL_ne_nsU : nsL ≠ nsU := by decide
@[simp] theorem mt_nsL_ne_nsN : nsL ≠ nsN := by decide
@[simp] theorem mt_nsL_ne_lFl : nsL ≠ lFl := by decide
@[simp] theorem mt_lFl_ne_nsL : lFl ≠ nsL := by decide
@[simp] theorem mt_nsL_ne_lDh : nsL ≠ lDh := by decide
@[simp] theorem mt_lDh_ne_nsL : lDh ≠ nsL := by decide
@[simp] theorem mt_nsL_ne_lDt : nsL ≠ lDt := by decide
@[simp] theorem mt_lDt_ne_nsL : lDt ≠ nsL := by decide
@[simp] theorem mt_nsL_ne_lDg : nsL ≠ lDg := by decide
@[simp] theorem mt_lDg_ne_nsL : lDg ≠ nsL := by decide
@[simp] theorem mt_nsL_ne_lDi : nsL ≠ lDi := by decide
@[simp] theorem mt_lDi_ne_nsL : lDi ≠ nsL := by decide
@[simp] theorem mt_nsL_ne_lRp : nsL ≠ lRp := by decide
@[simp] theorem mt_lRp_ne_nsL : lRp ≠ nsL := by decide
@[simp] theorem mt_nsL_ne_lRn : nsL ≠ lRn := by decide
@[simp] theorem mt_lRn_ne_nsL : lRn ≠ nsL := by decide
@[simp] theorem mt_nsL_ne_lFle : nsL ≠ lFle := by decide
@[simp] theorem mt_lFle_ne_nsL : lFle ≠ nsL := by decide
@[simp] theorem mt_nsL_ne_lDir : nsL ≠ lDir := by decide
@[simp] theorem mt_lDir_ne_nsL : lDir ≠ nsL := by decide
@[simp] theorem mt_nsL_ne_lKb : nsL ≠ lKb := by decide
@[simp] theorem mt_lKb_ne_nsL : lKb ≠ nsL := by decide
@[simp] theorem mt_nsN_ne_isH : nsN ≠ isH := by decide
@[simp] theorem mt_nsN_ne_isW : nsN ≠ isW := by decide
@[simp] theorem mt_nsN_ne_nsE : nsN ≠ nsE := by decide
@[simp] theorem mt_nsN_ne_nsF : nsN ≠ nsF := by decide
@[simp] theorem mt_nsN_ne_nsC : nsN ≠ nsC := by decide
@[simp] theorem mt_nsN_ne_nsU : nsN ≠ nsU := by decide
@[simp] theorem mt_nsN_ne_nsL : nsN ≠ nsL := by decide
@[simp] theorem mt_nsN_ne_lFl : nsN ≠ lFl := by decide
@[simp] theorem mt_lFl_ne_nsN : lFl ≠ nsN := by decide
@[simp] theorem mt_nsN_ne_lDh : nsN ≠ lDh := by decide
@[simp] theorem mt_lDh_ne_nsN : lDh ≠ nsN := by decide
@[simp] theorem mt_nsN_ne_lDt : nsN ≠ lDt := by decide
@[simp] theorem mt_lDt_ne_nsN : lDt ≠ nsN := by decide
@[simp] theorem mt_nsN_ne_lDg : nsN ≠ lDg := by decide
@[simp] theorem mt_lDg_ne_nsN : lDg ≠ nsN := by decide
@[simp] theorem mt_nsN_ne_lDi : nsN ≠ lDi := by decide
@[simp] theorem mt_lDi_ne_nsN : lDi ≠ nsN := by decide
@[simp] theorem mt_nsN_ne_lRp : nsN ≠ lRp := by decide
@[simp] theorem mt_lRp_ne_nsN : lRp ≠ nsN := by decide
@[simp] theorem mt_nsN_ne_lRn : nsN ≠ lRn := by decide
@[simp] theorem mt_lRn_ne_nsN : lRn ≠ nsN := by decide
@[simp] theorem mt_nsN_ne_lFle : nsN ≠ lFle := by decide
@[simp] theorem mt_lFle_ne_nsN : lFle ≠ nsN := by decide
@[simp] theorem mt_nsN_ne_lDir : nsN ≠ lDir := by decide
@[simp] theorem mt_lDir_ne_nsN : lDir ≠ nsN := by decide
@[simp] theorem mt_nsN_ne_lKb : nsN ≠ lKb := by decide
@[simp] theorem mt_lKb_ne_nsN : lKb ≠ nsN := by decide

def islLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, isW]

def islBody : ProgHOL 64 :=
  prologue islLocals
  (.ite (tagIsE isH 8)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv isH)) (.seq eViewP
    (.seq (.assign .local isW (.load .one (vv lRp))) (.return (.cmp .equal (vv isW) (.const 1)))))))
    (.return (.const 0)))

def nsLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, nsF, nsC, nsU, nsL, nsN]

def nsBody (C : Ctx) : ProgHOL 64 :=
  prologue nsLocals
  (.ite (tagIs4E nsE)
    (.seq (.assign .local lFl (vv lFle))
    (.seq (.assign .local lDh (vv nsE))
    (.seq eViewP
    (.seq (.assign .local nsF (.load .one (vv lRp)))
    (.ite (tagIsE nsF 3)
    (.seq (.assign .local lDh (vv nsF))
    (.seq eViewP
    (.seq (.assign .local nsC (.load .one (vv lRp)))
    (.seq (.assign .local nsU (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.assign .local nsL (.load .one (.const (ecell C (C.PO + pinCount + 0)))))
    (.seq (.assign .local nsN (.load .one (.const (ecell C (C.PO + PIN_NAT_SUCC)))))
    (.return (andE (.cmp .equal (vv nsU) (vv nsL)) (.cmp .equal (vv nsC) (vv nsN))))))))))
    (.return (.const 0)))))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem isl_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ islLocals → (ctxEnv C ++ [isH].zip vals).get x = none :=
  Knot.params_none C islLocals [isH] vals (by decide) (by decide)

theorem ns_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ nsLocals → (ctxEnv C ++ [nsE].zip vals).get x = none :=
  Knot.params_none C nsLocals [nsE] vals (by decide) (by decide)

theorem isl_spec (C : Ctx) (s : AState) (h : EIdx) :
    SpecR (σ := σ) (Pre C s [(isH, Enc.idxW h)]) islBody s (isStrLit h) (Knot.PostB C) := by
  refine specR_prologue (Knot.postB_locals C) (isl_none C [Enc.idxW h]) ?_
  unfold isStrLit
  refine Knot.specR_tagIteV isH h 8 (by decide) (by decide) (by simp +decide [Env.get, ctxEnv])
    (fun htg => ?_) (fun htg => ?_)
  · rw [if_pos (show (h.tag == ETag.lit) = true by simp [htg, ETag.lit])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv isH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_viewP h (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
      (fun v P hv htn _ => ?_)
    have h8 : v.tagN = 8 := by rw [htn, htg]; rfl
    obtain ⟨l, rfl⟩ := tagN_lit h8
    have hvl : s.store.viewLit h = some l := viewLit_of_view (by rw [htg]; rfl) hv
    refine specR_runBind (show ConRon.Arena.viewLit h s = .ok (some l, s) by
      show Except.ok (s.store.viewLit h, s) = _; rw [hvl]) ?_
    cases l with
    | natVal m =>
      refine specR_loadI' isW (vv lRp) P (P + BitVec.ofNat 64 0) 0 (by decide) (by simp) (by simp)
        (by simpa [encEView, Enc.encLit] using wordsAt_mem0 P 0 (limbs m) []) ?_
      exact specR_returnI _ (boolW false) (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | strVal str =>
      refine specR_loadI' isW (vv lRp) P (P + BitVec.ofNat 64 0) 1 (by decide) (by simp) (by simp)
        (by simpa [encEView, Enc.encLit] using wordsAt_mem0 P 1 (strW str) []) ?_
      exact specR_returnI _ (boolW true) (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · rw [if_neg (show ¬ (h.tag == ETag.lit) = true by simpa [ETag.lit] using htg)]
    exact specR_returnI _ (boolW false) (by simp [sev, boolW])
      (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem ns_spec (C : Ctx) (hok : CtxOK C) (s : AState) (e : EIdx) :
    SpecR (σ := σ) (Pre C s [(nsE, Enc.idxW e)]) (nsBody C) s (isNatSuccApp e) (Knot.PostB C) := by
  refine specR_prologue (Knot.postB_locals C) (ns_none C [Enc.idxW e]) ?_
  unfold isNatSuccApp
  have hret0 : ∀ {Γ : Env} {M : Mem}, SpecR (σ := σ) (Inv C s Γ M (ctxLocals ++ nsLocals)) (.return (.const 0)) s
      (pure false) (Knot.PostB C) := fun {Γ M} =>
    specR_returnI _ (boolW false) (by simp [sev, boolW])
      (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  have hT := sev_tagIs4B (ctxEnv C ++ [(nsE, Enc.idxW e)]) nsE e (by simp +decide [Env.get, ctxEnv])
  by_cases ht : (e.tag == 4) = true
  · rw [if_pos (show (e.tag == ETag.app) = true from ht)]
    refine specR_ifI _ 1 (by rw [hT, ht]; rfl) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv nsE) (Enc.idxW e) (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine ILP.specR_viewIv e (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
      (fun v P hv htn _ => ?_)
    have h4 : v.tagN = 4 := by rw [htn]; simp at ht; rw [ht]; rfl
    obtain ⟨f, a, rfl⟩ := tagN_app h4
    dsimp only
    refine specR_loadI' nsF (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW f) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encApp] using wordsAt_mem0 P (Enc.idxW f) [Enc.idxW a] []) ?_
    refine specR_dropM ?_
    refine Knot.specR_tagIteV nsF f 3 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
    · rw [if_pos (show (f.tag == ETag.const) = true by simp [htg, ETag.const])]
      refine specR_assignI lDh (vv nsF) (Enc.idxW f) (by decide) (by simp) ?_
      refine ILP.specR_viewIv f (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
        (fun v' P' hv' htn' _ => ?_)
      have h3 : v'.tagN = 3 := by rw [htn', htg]; rfl
      obtain ⟨c, us, rfl⟩ := UD.tagN_const h3
      dsimp only
      refine specR_loadI' nsC (vv lRp) P' (P' + BitVec.ofNat 64 0) (Enc.idxW c) (by decide) (by simp) (by simp)
        (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P' (Enc.idxW c) [Enc.idxW us] []) ?_
      refine specR_loadI' nsU _ (P' + 8) (P' + BitVec.ofNat 64 8) (Enc.idxW us) (by decide) (by simp +decide [sev]) rfl
        (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P' (Enc.idxW c) (Enc.idxW us) [] []) ?_
      refine specR_dropM ?_
      refine specR_pinXI hok pinEmptyLevels 0 C.pins.emptyLevels _ (fun s hp => pinEmptyLevels_run hok hp)
        (pin_emptyLevels_cell hok) nsL (by decide) ?_
      show SpecR _ _ _ (pinAt PIN_NAT_SUCC >>= fun ns => pure (us == C.pins.emptyLevels && c == ns)) _
      refine specR_pinAtI hok PIN_NAT_SUCC (by decide) nsN (by decide) ?_
      exact specR_returnI _ _ (sev_andE (sev_eqIdxB (by simp) (by simp)) (sev_eqIdxB (by simp) (by simp)))
        (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · rw [if_neg (show ¬ (f.tag == ETag.const) = true by simpa [ETag.const] using htg)]
      exact hret0
  · rw [if_neg (show ¬ (e.tag == ETag.app) = true from ht)]
    refine specR_ifI _ 0 (by rw [hT]; simp at ht; simp [ht, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    exact hret0

end

end ConPanqueque.T.WC
