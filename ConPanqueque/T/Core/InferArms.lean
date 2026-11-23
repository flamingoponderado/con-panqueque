import ConPanqueque.T.Core.InferBody
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `inferBody`'s small arms: sort, constant, `let`
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def isS := ofString "is_s"
def isR := ofString "is_r"

@[simp] theorem ia_isS_ne_isR : isS ≠ isR := by decide
@[simp] theorem ia_isS_ne_lKb : isS ≠ lKb := by decide
@[simp] theorem ia_isS_ne_ibU : isS ≠ ibU := by decide
@[simp] theorem ia_isR_ne_isS : isR ≠ isS := by decide
@[simp] theorem ia_isR_ne_lKb : isR ≠ lKb := by decide
@[simp] theorem ia_isR_ne_ibU : isR ≠ ibU := by decide
@[simp] theorem ia_lKb_ne_isS : lKb ≠ isS := by decide
@[simp] theorem ia_lKb_ne_isR : lKb ≠ isR := by decide
@[simp] theorem ia_ibU_ne_isS : ibU ≠ isS := by decide
@[simp] theorem ia_ibU_ne_isR : ibU ≠ isR := by decide

def isLocals : List MlS := [isS, isR]

def isBody : ProgHOL 64 := prologue isLocals
  (.seq (.call (some (some (.local, isS), none)) fInternLSucc [vv ibU])
  (.seq (.call (some (some (.local, isR), none)) fInternSort [vv isS]) (.return (vv isR))))

section
variable {σ : Type}

theorem is_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ isLocals → (ctxEnv C ++ ibsParams.zip vals).get x = none :=
  Knot.params_none C isLocals ibsParams vals (by decide) (by decide)

theorem is_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcs : C.code.lookup fInternLSucc = some ([(lEu, .one)], internLSuccBody, .one))
    (hct : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one)) (s : AState) (u : LIdx) :
    SpecR (σ := σ) (Pre C s (ibsParams.zip [Enc.idxW u])) isBody s (ibSortT u) (PostK C) := by
  refine specR_prologue (postK_locals C) (is_none C _) ?_
  unfold ibSortT
  refine callLN isS fInternLSucc [lEu] [vv ibU] internLSuccBody [Enc.idxW u] (by decide) rfl (by decide) hcs
    ⟨by simp +decide [Env.get, ibsParams, ctxEnv], trivial⟩ (.succ u) (internLSucc_body_spec ra C hok s u)
    (fun su s1 _ => ?_)
  refine specR_bindPure ?_
  refine ILP.callE_spec isR fInternSort [lEu] [vv isS] sortBody [Enc.idxW su] (by decide) rfl (by decide) hct
    ⟨by simp, trivial⟩ (sort_body_spec ra C hok s1 su) (fun r s2 => ?_)
  exact specR_returnI _ (Enc.idxW r) (by simp)
    (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
