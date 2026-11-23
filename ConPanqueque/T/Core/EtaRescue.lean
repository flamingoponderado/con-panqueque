import ConPanqueque.T.Core.ListEq
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `etaRescueTable?`: the structure-η rescue's standing condition

The family's projection table, when the family is η-capable, the table's constructor is the rule's, the
constructor carries the family's level parameters, and it is not `And.intro`. The answer is the table's
environment pointer plus one, or `0`.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def erT := ofString "ert"
def erC := ofString "erc"
def erJ := ofString "erj"
def erF := ofString "erf"
def erW := ofString "erw"
def erQ := ofString "erq"
def erE := ofString "ere"
def erK := ofString "erk"
def erLa := ofString "erla"
def erLb := ofString "erlb"
def erNa := ofString "erna"
def erNb := ofString "ernb"
def erR := ofString "err"
def erAi := ofString "erai"
def fEr := ofString "etaRescueTable"

@[simp] theorem er_erT_ne_erC : erT ≠ erC := by decide
@[simp] theorem er_erT_ne_erJ : erT ≠ erJ := by decide
@[simp] theorem er_erT_ne_erF : erT ≠ erF := by decide
@[simp] theorem er_erT_ne_erW : erT ≠ erW := by decide
@[simp] theorem er_erT_ne_erQ : erT ≠ erQ := by decide
@[simp] theorem er_erT_ne_erE : erT ≠ erE := by decide
@[simp] theorem er_erT_ne_erK : erT ≠ erK := by decide
@[simp] theorem er_erT_ne_erLa : erT ≠ erLa := by decide
@[simp] theorem er_erT_ne_erLb : erT ≠ erLb := by decide
@[simp] theorem er_erT_ne_erNa : erT ≠ erNa := by decide
@[simp] theorem er_erT_ne_erNb : erT ≠ erNb := by decide
@[simp] theorem er_erT_ne_erR : erT ≠ erR := by decide
@[simp] theorem er_erT_ne_erAi : erT ≠ erAi := by decide
@[simp] theorem er_erT_ne_lKb : erT ≠ lKb := by decide
@[simp] theorem er_lKb_ne_erT : lKb ≠ erT := by decide
@[simp] theorem er_erC_ne_erT : erC ≠ erT := by decide
@[simp] theorem er_erC_ne_erJ : erC ≠ erJ := by decide
@[simp] theorem er_erC_ne_erF : erC ≠ erF := by decide
@[simp] theorem er_erC_ne_erW : erC ≠ erW := by decide
@[simp] theorem er_erC_ne_erQ : erC ≠ erQ := by decide
@[simp] theorem er_erC_ne_erE : erC ≠ erE := by decide
@[simp] theorem er_erC_ne_erK : erC ≠ erK := by decide
@[simp] theorem er_erC_ne_erLa : erC ≠ erLa := by decide
@[simp] theorem er_erC_ne_erLb : erC ≠ erLb := by decide
@[simp] theorem er_erC_ne_erNa : erC ≠ erNa := by decide
@[simp] theorem er_erC_ne_erNb : erC ≠ erNb := by decide
@[simp] theorem er_erC_ne_erR : erC ≠ erR := by decide
@[simp] theorem er_erC_ne_erAi : erC ≠ erAi := by decide
@[simp] theorem er_erC_ne_lKb : erC ≠ lKb := by decide
@[simp] theorem er_lKb_ne_erC : lKb ≠ erC := by decide
@[simp] theorem er_erJ_ne_erT : erJ ≠ erT := by decide
@[simp] theorem er_erJ_ne_erC : erJ ≠ erC := by decide
@[simp] theorem er_erJ_ne_erF : erJ ≠ erF := by decide
@[simp] theorem er_erJ_ne_erW : erJ ≠ erW := by decide
@[simp] theorem er_erJ_ne_erQ : erJ ≠ erQ := by decide
@[simp] theorem er_erJ_ne_erE : erJ ≠ erE := by decide
@[simp] theorem er_erJ_ne_erK : erJ ≠ erK := by decide
@[simp] theorem er_erJ_ne_erLa : erJ ≠ erLa := by decide
@[simp] theorem er_erJ_ne_erLb : erJ ≠ erLb := by decide
@[simp] theorem er_erJ_ne_erNa : erJ ≠ erNa := by decide
@[simp] theorem er_erJ_ne_erNb : erJ ≠ erNb := by decide
@[simp] theorem er_erJ_ne_erR : erJ ≠ erR := by decide
@[simp] theorem er_erJ_ne_erAi : erJ ≠ erAi := by decide
@[simp] theorem er_erJ_ne_lKb : erJ ≠ lKb := by decide
@[simp] theorem er_lKb_ne_erJ : lKb ≠ erJ := by decide
@[simp] theorem er_erF_ne_erT : erF ≠ erT := by decide
@[simp] theorem er_erF_ne_erC : erF ≠ erC := by decide
@[simp] theorem er_erF_ne_erJ : erF ≠ erJ := by decide
@[simp] theorem er_erF_ne_erW : erF ≠ erW := by decide
@[simp] theorem er_erF_ne_erQ : erF ≠ erQ := by decide
@[simp] theorem er_erF_ne_erE : erF ≠ erE := by decide
@[simp] theorem er_erF_ne_erK : erF ≠ erK := by decide
@[simp] theorem er_erF_ne_erLa : erF ≠ erLa := by decide
@[simp] theorem er_erF_ne_erLb : erF ≠ erLb := by decide
@[simp] theorem er_erF_ne_erNa : erF ≠ erNa := by decide
@[simp] theorem er_erF_ne_erNb : erF ≠ erNb := by decide
@[simp] theorem er_erF_ne_erR : erF ≠ erR := by decide
@[simp] theorem er_erF_ne_erAi : erF ≠ erAi := by decide
@[simp] theorem er_erF_ne_lKb : erF ≠ lKb := by decide
@[simp] theorem er_lKb_ne_erF : lKb ≠ erF := by decide
@[simp] theorem er_erW_ne_erT : erW ≠ erT := by decide
@[simp] theorem er_erW_ne_erC : erW ≠ erC := by decide
@[simp] theorem er_erW_ne_erJ : erW ≠ erJ := by decide
@[simp] theorem er_erW_ne_erF : erW ≠ erF := by decide
@[simp] theorem er_erW_ne_erQ : erW ≠ erQ := by decide
@[simp] theorem er_erW_ne_erE : erW ≠ erE := by decide
@[simp] theorem er_erW_ne_erK : erW ≠ erK := by decide
@[simp] theorem er_erW_ne_erLa : erW ≠ erLa := by decide
@[simp] theorem er_erW_ne_erLb : erW ≠ erLb := by decide
@[simp] theorem er_erW_ne_erNa : erW ≠ erNa := by decide
@[simp] theorem er_erW_ne_erNb : erW ≠ erNb := by decide
@[simp] theorem er_erW_ne_erR : erW ≠ erR := by decide
@[simp] theorem er_erW_ne_erAi : erW ≠ erAi := by decide
@[simp] theorem er_erW_ne_lKb : erW ≠ lKb := by decide
@[simp] theorem er_lKb_ne_erW : lKb ≠ erW := by decide
@[simp] theorem er_erQ_ne_erT : erQ ≠ erT := by decide
@[simp] theorem er_erQ_ne_erC : erQ ≠ erC := by decide
@[simp] theorem er_erQ_ne_erJ : erQ ≠ erJ := by decide
@[simp] theorem er_erQ_ne_erF : erQ ≠ erF := by decide
@[simp] theorem er_erQ_ne_erW : erQ ≠ erW := by decide
@[simp] theorem er_erQ_ne_erE : erQ ≠ erE := by decide
@[simp] theorem er_erQ_ne_erK : erQ ≠ erK := by decide
@[simp] theorem er_erQ_ne_erLa : erQ ≠ erLa := by decide
@[simp] theorem er_erQ_ne_erLb : erQ ≠ erLb := by decide
@[simp] theorem er_erQ_ne_erNa : erQ ≠ erNa := by decide
@[simp] theorem er_erQ_ne_erNb : erQ ≠ erNb := by decide
@[simp] theorem er_erQ_ne_erR : erQ ≠ erR := by decide
@[simp] theorem er_erQ_ne_erAi : erQ ≠ erAi := by decide
@[simp] theorem er_erQ_ne_lKb : erQ ≠ lKb := by decide
@[simp] theorem er_lKb_ne_erQ : lKb ≠ erQ := by decide
@[simp] theorem er_erE_ne_erT : erE ≠ erT := by decide
@[simp] theorem er_erE_ne_erC : erE ≠ erC := by decide
@[simp] theorem er_erE_ne_erJ : erE ≠ erJ := by decide
@[simp] theorem er_erE_ne_erF : erE ≠ erF := by decide
@[simp] theorem er_erE_ne_erW : erE ≠ erW := by decide
@[simp] theorem er_erE_ne_erQ : erE ≠ erQ := by decide
@[simp] theorem er_erE_ne_erK : erE ≠ erK := by decide
@[simp] theorem er_erE_ne_erLa : erE ≠ erLa := by decide
@[simp] theorem er_erE_ne_erLb : erE ≠ erLb := by decide
@[simp] theorem er_erE_ne_erNa : erE ≠ erNa := by decide
@[simp] theorem er_erE_ne_erNb : erE ≠ erNb := by decide
@[simp] theorem er_erE_ne_erR : erE ≠ erR := by decide
@[simp] theorem er_erE_ne_erAi : erE ≠ erAi := by decide
@[simp] theorem er_erE_ne_lKb : erE ≠ lKb := by decide
@[simp] theorem er_lKb_ne_erE : lKb ≠ erE := by decide
@[simp] theorem er_erK_ne_erT : erK ≠ erT := by decide
@[simp] theorem er_erK_ne_erC : erK ≠ erC := by decide
@[simp] theorem er_erK_ne_erJ : erK ≠ erJ := by decide
@[simp] theorem er_erK_ne_erF : erK ≠ erF := by decide
@[simp] theorem er_erK_ne_erW : erK ≠ erW := by decide
@[simp] theorem er_erK_ne_erQ : erK ≠ erQ := by decide
@[simp] theorem er_erK_ne_erE : erK ≠ erE := by decide
@[simp] theorem er_erK_ne_erLa : erK ≠ erLa := by decide
@[simp] theorem er_erK_ne_erLb : erK ≠ erLb := by decide
@[simp] theorem er_erK_ne_erNa : erK ≠ erNa := by decide
@[simp] theorem er_erK_ne_erNb : erK ≠ erNb := by decide
@[simp] theorem er_erK_ne_erR : erK ≠ erR := by decide
@[simp] theorem er_erK_ne_erAi : erK ≠ erAi := by decide
@[simp] theorem er_erK_ne_lKb : erK ≠ lKb := by decide
@[simp] theorem er_lKb_ne_erK : lKb ≠ erK := by decide
@[simp] theorem er_erLa_ne_erT : erLa ≠ erT := by decide
@[simp] theorem er_erLa_ne_erC : erLa ≠ erC := by decide
@[simp] theorem er_erLa_ne_erJ : erLa ≠ erJ := by decide
@[simp] theorem er_erLa_ne_erF : erLa ≠ erF := by decide
@[simp] theorem er_erLa_ne_erW : erLa ≠ erW := by decide
@[simp] theorem er_erLa_ne_erQ : erLa ≠ erQ := by decide
@[simp] theorem er_erLa_ne_erE : erLa ≠ erE := by decide
@[simp] theorem er_erLa_ne_erK : erLa ≠ erK := by decide
@[simp] theorem er_erLa_ne_erLb : erLa ≠ erLb := by decide
@[simp] theorem er_erLa_ne_erNa : erLa ≠ erNa := by decide
@[simp] theorem er_erLa_ne_erNb : erLa ≠ erNb := by decide
@[simp] theorem er_erLa_ne_erR : erLa ≠ erR := by decide
@[simp] theorem er_erLa_ne_erAi : erLa ≠ erAi := by decide
@[simp] theorem er_erLa_ne_lKb : erLa ≠ lKb := by decide
@[simp] theorem er_lKb_ne_erLa : lKb ≠ erLa := by decide
@[simp] theorem er_erLb_ne_erT : erLb ≠ erT := by decide
@[simp] theorem er_erLb_ne_erC : erLb ≠ erC := by decide
@[simp] theorem er_erLb_ne_erJ : erLb ≠ erJ := by decide
@[simp] theorem er_erLb_ne_erF : erLb ≠ erF := by decide
@[simp] theorem er_erLb_ne_erW : erLb ≠ erW := by decide
@[simp] theorem er_erLb_ne_erQ : erLb ≠ erQ := by decide
@[simp] theorem er_erLb_ne_erE : erLb ≠ erE := by decide
@[simp] theorem er_erLb_ne_erK : erLb ≠ erK := by decide
@[simp] theorem er_erLb_ne_erLa : erLb ≠ erLa := by decide
@[simp] theorem er_erLb_ne_erNa : erLb ≠ erNa := by decide
@[simp] theorem er_erLb_ne_erNb : erLb ≠ erNb := by decide
@[simp] theorem er_erLb_ne_erR : erLb ≠ erR := by decide
@[simp] theorem er_erLb_ne_erAi : erLb ≠ erAi := by decide
@[simp] theorem er_erLb_ne_lKb : erLb ≠ lKb := by decide
@[simp] theorem er_lKb_ne_erLb : lKb ≠ erLb := by decide
@[simp] theorem er_erNa_ne_erT : erNa ≠ erT := by decide
@[simp] theorem er_erNa_ne_erC : erNa ≠ erC := by decide
@[simp] theorem er_erNa_ne_erJ : erNa ≠ erJ := by decide
@[simp] theorem er_erNa_ne_erF : erNa ≠ erF := by decide
@[simp] theorem er_erNa_ne_erW : erNa ≠ erW := by decide
@[simp] theorem er_erNa_ne_erQ : erNa ≠ erQ := by decide
@[simp] theorem er_erNa_ne_erE : erNa ≠ erE := by decide
@[simp] theorem er_erNa_ne_erK : erNa ≠ erK := by decide
@[simp] theorem er_erNa_ne_erLa : erNa ≠ erLa := by decide
@[simp] theorem er_erNa_ne_erLb : erNa ≠ erLb := by decide
@[simp] theorem er_erNa_ne_erNb : erNa ≠ erNb := by decide
@[simp] theorem er_erNa_ne_erR : erNa ≠ erR := by decide
@[simp] theorem er_erNa_ne_erAi : erNa ≠ erAi := by decide
@[simp] theorem er_erNa_ne_lKb : erNa ≠ lKb := by decide
@[simp] theorem er_lKb_ne_erNa : lKb ≠ erNa := by decide
@[simp] theorem er_erNb_ne_erT : erNb ≠ erT := by decide
@[simp] theorem er_erNb_ne_erC : erNb ≠ erC := by decide
@[simp] theorem er_erNb_ne_erJ : erNb ≠ erJ := by decide
@[simp] theorem er_erNb_ne_erF : erNb ≠ erF := by decide
@[simp] theorem er_erNb_ne_erW : erNb ≠ erW := by decide
@[simp] theorem er_erNb_ne_erQ : erNb ≠ erQ := by decide
@[simp] theorem er_erNb_ne_erE : erNb ≠ erE := by decide
@[simp] theorem er_erNb_ne_erK : erNb ≠ erK := by decide
@[simp] theorem er_erNb_ne_erLa : erNb ≠ erLa := by decide
@[simp] theorem er_erNb_ne_erLb : erNb ≠ erLb := by decide
@[simp] theorem er_erNb_ne_erNa : erNb ≠ erNa := by decide
@[simp] theorem er_erNb_ne_erR : erNb ≠ erR := by decide
@[simp] theorem er_erNb_ne_erAi : erNb ≠ erAi := by decide
@[simp] theorem er_erNb_ne_lKb : erNb ≠ lKb := by decide
@[simp] theorem er_lKb_ne_erNb : lKb ≠ erNb := by decide
@[simp] theorem er_erR_ne_erT : erR ≠ erT := by decide
@[simp] theorem er_erR_ne_erC : erR ≠ erC := by decide
@[simp] theorem er_erR_ne_erJ : erR ≠ erJ := by decide
@[simp] theorem er_erR_ne_erF : erR ≠ erF := by decide
@[simp] theorem er_erR_ne_erW : erR ≠ erW := by decide
@[simp] theorem er_erR_ne_erQ : erR ≠ erQ := by decide
@[simp] theorem er_erR_ne_erE : erR ≠ erE := by decide
@[simp] theorem er_erR_ne_erK : erR ≠ erK := by decide
@[simp] theorem er_erR_ne_erLa : erR ≠ erLa := by decide
@[simp] theorem er_erR_ne_erLb : erR ≠ erLb := by decide
@[simp] theorem er_erR_ne_erNa : erR ≠ erNa := by decide
@[simp] theorem er_erR_ne_erNb : erR ≠ erNb := by decide
@[simp] theorem er_erR_ne_erAi : erR ≠ erAi := by decide
@[simp] theorem er_erR_ne_lKb : erR ≠ lKb := by decide
@[simp] theorem er_lKb_ne_erR : lKb ≠ erR := by decide
@[simp] theorem er_erAi_ne_erT : erAi ≠ erT := by decide
@[simp] theorem er_erAi_ne_erC : erAi ≠ erC := by decide
@[simp] theorem er_erAi_ne_erJ : erAi ≠ erJ := by decide
@[simp] theorem er_erAi_ne_erF : erAi ≠ erF := by decide
@[simp] theorem er_erAi_ne_erW : erAi ≠ erW := by decide
@[simp] theorem er_erAi_ne_erQ : erAi ≠ erQ := by decide
@[simp] theorem er_erAi_ne_erE : erAi ≠ erE := by decide
@[simp] theorem er_erAi_ne_erK : erAi ≠ erK := by decide
@[simp] theorem er_erAi_ne_erLa : erAi ≠ erLa := by decide
@[simp] theorem er_erAi_ne_erLb : erAi ≠ erLb := by decide
@[simp] theorem er_erAi_ne_erNa : erAi ≠ erNa := by decide
@[simp] theorem er_erAi_ne_erNb : erAi ≠ erNb := by decide
@[simp] theorem er_erAi_ne_erR : erAi ≠ erR := by decide
@[simp] theorem er_erAi_ne_lKb : erAi ≠ lKb := by decide
@[simp] theorem er_lKb_ne_erAi : lKb ≠ erAi := by decide

def erParams : List MlS := [erT, erC, erJ, erF]
def erLocals : List MlS := [erW, erQ, erE, erK, erLa, erLb, erNa, erNb, erR, erAi]

def erBody (C : Ctx) : ProgHOL 64 := prologue erLocals
  (tblFindP C erW (vv erT)
  (.ite (.cmp .equal (vv erW) (.const 0)) (.return (.const 0))
  (.seq (.assign .local erQ (.op .sub [vv erW, .const 1]))
  (.seq (.assign .local erE (.load .one (.op .add [vv erF, .const 32])))
  (.ite (.cmp .equal (vv erE) (.const 0)) (.return (.const 0))
  (.seq (.assign .local erK (.load .one (.op .add [vv erQ, .const 24])))
  (.ite (.cmp .notEqual (vv erK) (vv erC)) (.return (.const 0))
  (.seq (.assign .local erLa (.load .one (.op .add [vv erJ, .const 16])))
  (.seq (.assign .local erLb (.load .one (.op .add [vv erF, .const 16])))
  (.seq (.assign .local erNa (.load .one (vv erLa)))
  (.seq (.assign .local erNb (.load .one (vv erLb)))
  (.ite (.cmp .notEqual (vv erNa) (vv erNb)) (.return (.const 0))
  (.seq (.call (some (some (.local, erR), none)) fLq [.op .add [vv erLa, .const 8], .op .add [vv erLb, .const 8], .const 0, vv erNa])
  (.ite (.cmp .equal (vv erR) (.const 0)) (.return (.const 0))
  (.seq (.assign .local erAi (.load .one (.const (ecell C (C.PO + PIN_AND_INTRO)))))
  (.ite (.cmp .equal (vv erC) (vv erAi)) (.return (.const 0)) (.return (vv erW))))))))))))))))))

section
variable {σ : Type}

theorem er_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ erLocals → (ctxEnv C ++ erParams.zip vals).get x = none :=
  Knot.params_none C erLocals erParams vals (by decide) (by decide)

/-- A table answer: its environment pointer plus one, or `0` (state and heap unchanged). -/
def PostTB (C : Ctx) (s : AState) (r : Option IProjTable) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  s' = s ∧ (∃ H', C.H <+: H' ∧ SR (ctxH C H') s st) ∧ match r with
    | none => w = 0
    | some t => ∃ o, w = ecell C o + 1 ∧ o < C.EN ∧ TblE C.EB C.EH o t

theorem postTB_locals (C : Ctx) (s : AState) : ∀ (a : Option IProjTable) w s' (st : PState σ)
    (L : HolFiniteMapExact MlS (ValueHOL 64)), PostTB C s a w s' st → PostTB C s a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, ⟨H', hp, h2⟩, h3⟩ => ⟨h1, ⟨H', hp, sr_of_eq h2 rfl rfl rfl rfl⟩, h3⟩

theorem er_spec (C : Ctx) (hok : CtxOK C)
    (hcodeG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcodeP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (hcf : C.code.lookup fLq = some (lqParams.map (fun p => (p, ShapeHOL.one)), lqBody, .one))
    (s : AState) (T ctor : NIdx) (cvj cvT : IConstantVal) (caps : IIndCaps) (qj qT npj nfj : Nat) (indj : NIdx)
    (hcj : CIE C.EB C.EH qj (.ctorInfo cvj npj nfj indj)) (hcT : CIE C.EB C.EH qT (.indInfo cvT caps)) :
    SpecR (σ := σ) (Pre C s (erParams.zip [Enc.idxW T, Enc.idxW ctor, ecell C qj, ecell C qT])) (erBody C) s
      (etaRescueTable? (C.fe.findTable? T) ctor cvj cvT caps) (PostTB C s) := by
  refine specR_prologue (postTB_locals C s) (er_none C _) ?_
  unfold etaRescueTable?
  have hret0 : ∀ {Γ : Env} {M : Mem} {H : List (BitVec 64)}, C.H <+: H →
      SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ erLocals)) (.return (.const 0)) s
      (pure none : AM (Option IProjTable)) (PostTB C s) := fun {Γ M H} hp =>
    specR_returnI _ 0 rfl (fun t ht => ⟨rfl, ⟨H, hp, sr_of_eq ht.sr rfl rfl rfl rfl⟩, rfl⟩)
  refine specR_tblFindI hok hcodeG hcodeP erW (vv erT) T (by decide) (by simp +decide [Env.get, erParams, ctxEnv])
    (by simp +decide [Env.get, erParams, ctxEnv]) ?_
  have hrel := tbl_rel hok T
  revert hrel
  rcases hft : C.fe.findTable? T with _ | tb
  · intro hrel; simp only at hrel
    rw [hrel]
    refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => hret0 (List.prefix_refl _))
      (fun h => absurd h (by decide))
  intro ⟨o, hm, htb⟩
  rw [hm]
  dsimp only
  refine specR_atEntry fun t ht => ?_
  have hoE : o < C.EN := Nat.lt_of_lt_of_le (tblE_lt htb) ht.sr.env.1.len
  have hEN := ht.sr.env.1.len
  have hlay := hok.envLay
  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI erQ _ (ecell C o) (by decide) (by simp [sev, optWG]; exact ecell_succ_sub C o) ?_
  have hcT' := hcT
  obtain ⟨⟨_, ⟨wlT, hwlT, hlpsT⟩, _⟩, _, heta, _⟩ := hcT'
  simp only [IConstantInfo.toConstantVal] at hlpsT
  have hcj' := hcj
  obtain ⟨⟨_, ⟨wlj, hwlj, hlpsj⟩, _⟩, _⟩ := hcj'
  simp only [IConstantInfo.toConstantVal] at hlpsj
  refine specR_envLoadI erE (.op .add [vv erF, .const 32]) (qT + 4) _ (by decide)
    (by simp +decide [sev, Env.get, erParams, ctxEnv]; exact UD.ecell_add32 C qT) heta ?_
  cases hce : caps.eta
  · refine specR_ifI _ 1 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    rw [if_neg (by simp)]
    exact hret0 (List.prefix_refl _)
  refine specR_ifI _ 0 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
    (fun _ => ?_)
  have ⟨_, _, _, hctor, _, _⟩ := htb
  refine specR_envLoadI erK (.op .add [vv erQ, .const 24]) (o + 3) _ (by decide)
    (by simp [sev, vv]; exact ecell_add24 C o) hctor ?_
  by_cases hk : tb.ctor = ctor
  swap
  · have hne : Enc.idxW tb.ctor ≠ Enc.idxW ctor := fun e => hk (Enc.idxW_inj e)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, erParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [if_neg (by simp [hk])]
    exact hret0 (List.prefix_refl _)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, erParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hk])
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_envLoadI erLa (.op .add [vv erJ, .const 16]) (qj + 2) _ (by decide)
    (by simp +decide [sev, Env.get, erParams, ctxEnv]; exact UD.ecell_add16 C qj)
    (by rw [show qj + 2 = qj + 1 + 1 by omega]; exact hwlj) ?_
  refine specR_envLoadI erLb (.op .add [vv erF, .const 16]) (qT + 2) _ (by decide)
    (by simp +decide [sev, Env.get, erParams, ctxEnv]; exact UD.ecell_add16 C qT)
    (by rw [show qT + 2 = qT + 1 + 1 by omega]; exact hwlT) ?_
  obtain ⟨oa, hwa, hba⟩ := hlpsj
  obtain ⟨ob, hwb, hbb⟩ := hlpsT
  refine specR_envLoadI erNa (vv erLa) oa _ (by decide) (by simp [hwa]; rfl) hba.1 ?_
  refine specR_envLoadI erNb (vv erLb) ob _ (by decide) (by simp [hwb]; rfl) hbb.1 ?_
  have hla : cvj.levelParams.length < 2 ^ 61 := by
    have h1 := blkAt_len (show BlkAt C.EH oa (cvj.levelParams.map Enc.idxW) from hba)
    simp only [List.length_map] at h1; omega
  have hlb : cvT.levelParams.length < 2 ^ 61 := by
    have h1 := blkAt_len (show BlkAt C.EH ob (cvT.levelParams.map Enc.idxW) from hbb)
    simp only [List.length_map] at h1; omega
  simp only [List.length_map]
  by_cases hlen : cvj.levelParams.length = cvT.levelParams.length
  swap
  · have hne : BitVec.ofNat 64 cvj.levelParams.length ≠ BitVec.ofNat 64 cvT.levelParams.length := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    have hb : (cvj.levelParams == cvT.levelParams) = false :=
      beq_eq_false_iff_ne.mpr (fun h => hlen (by rw [h]))
    rw [if_neg (by simp [hk, hb])]
    exact hret0 (List.prefix_refl _)
  refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlen]) (fun h => absurd rfl h)
    (fun _ => ?_)
  refine specR_callPure erR fLq lqParams
    [.op .add [vv erLa, .const 8], .op .add [vv erLb, .const 8], .const 0, vv erNa] lqBody
    [ecell C (oa + 1), ecell C (ob + 1), BitVec.ofNat 64 0, BitVec.ofNat 64 cvj.levelParams.length]
    (cvj.levelParams.drop 0 == cvT.levelParams.drop 0) (by decide) rfl (by decide) hcf
    ⟨by simp [sev, hwa]; show ecell C oa + BitVec.ofNat 64 (8 * 1) = _; exact ecell_add C oa 1,
      by simp [sev, hwb]; show ecell C ob + BitVec.ofNat 64 (8 * 1) = _; exact ecell_add C ob 1, rfl, by simp, trivial⟩
    (Knot.PostB C) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu lqParams _ rfl hlk)
      (lq_spec C hcf cvj.levelParams cvT.levelParams (oa + 1) (ob + 1) hlen hla
        (fun i hi => by have := hba.2 i (by simpa using hi); simpa using this)
        (fun i hi => by have := hbb.2 i (by simpa using hi); simpa using this) s _ 0 rfl (Nat.zero_le _)))
    (fun w H1 hp1 hw => ?_)
  subst hw
  simp only [List.drop_zero]
  have hok1 := ctxOK_H hok H1
  cases hb : (cvj.levelParams == cvT.levelParams)
  · refine specR_ifI _ 1 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    rw [if_neg (by simp [hk, hb])]
    exact hret0 hp1
  refine specR_ifI _ 0 (by simp [sev, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
    (fun _ => ?_)
  rw [if_pos (by simp [hce, hk, hb])]
  show SpecR _ _ _ (pinAt PIN_AND_INTRO >>= fun ai => if ctor != ai then pure (some tb) else pure none) _
  refine specR_pinAtI (C := ctxH C H1) hok1 PIN_AND_INTRO (by decide) erAi (by decide) ?_
  by_cases hai : ctor = (ctxH C H1).pins.names[PIN_AND_INTRO]'(by rw [hok1.pinsRel.1]; decide)
  · refine specR_ifI _ 1 (by simp +decide [sev, Env.get, erParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hai])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [if_neg (by simp [hai])]
    exact hret0 hp1
  · have hne : Enc.idxW ctor ≠ Enc.idxW ((ctxH C H1).pins.names[PIN_AND_INTRO]'(by rw [hok1.pinsRel.1]; decide)) :=
      fun e => hai (Enc.idxW_inj e)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, erParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [if_pos (by simp [hai])]
    exact specR_returnI _ (ecell C o + 1) (by simp [optWG])
      (fun t ht => ⟨rfl, ⟨H1, hp1, sr_of_eq ht.sr rfl rfl rfl rfl⟩, o, rfl, hoE, htb⟩)

end

end ConPanqueque.T.WC
