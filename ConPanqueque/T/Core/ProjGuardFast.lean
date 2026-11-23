import ConPanqueque.T.Core.HasLoose
import ConPanqueque.T.Core.CheckGuard
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `projGuardFast`

The projection guard's fast case on the raw field telescope: step `k` binders; at the projected field `some`
its raw domain unless a field before it is mentioned (`hasLooseBVarIn 0 j`), at every earlier field `none` if
its domain mentions an earlier one. Answers `optW`.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def pfK := ofString "pfn_k"
def pfJ := ofString "pfn_j"
def pfH := ofString "pfn_h"
def pfD := ofString "pfn_d"
def pfB := ofString "pfn_b"
def pfX := ofString "pfn_x"
def pfR := ofString "pfn_r"
def fPf := ofString "projGuardFast"

@[simp] theorem pf_pfK_ne_pfJ : pfK ≠ pfJ := by decide
@[simp] theorem pf_pfK_ne_pfH : pfK ≠ pfH := by decide
@[simp] theorem pf_pfK_ne_pfD : pfK ≠ pfD := by decide
@[simp] theorem pf_pfK_ne_pfB : pfK ≠ pfB := by decide
@[simp] theorem pf_pfK_ne_pfX : pfK ≠ pfX := by decide
@[simp] theorem pf_pfK_ne_pfR : pfK ≠ pfR := by decide
@[simp] theorem pf_pfK_ne_lFl : pfK ≠ lFl := by decide
@[simp] theorem pf_lFl_ne_pfK : lFl ≠ pfK := by decide
@[simp] theorem pf_pfK_ne_lDh : pfK ≠ lDh := by decide
@[simp] theorem pf_lDh_ne_pfK : lDh ≠ pfK := by decide
@[simp] theorem pf_pfK_ne_lDt : pfK ≠ lDt := by decide
@[simp] theorem pf_lDt_ne_pfK : lDt ≠ pfK := by decide
@[simp] theorem pf_pfK_ne_lDg : pfK ≠ lDg := by decide
@[simp] theorem pf_lDg_ne_pfK : lDg ≠ pfK := by decide
@[simp] theorem pf_pfK_ne_lDi : pfK ≠ lDi := by decide
@[simp] theorem pf_lDi_ne_pfK : lDi ≠ pfK := by decide
@[simp] theorem pf_pfK_ne_lRp : pfK ≠ lRp := by decide
@[simp] theorem pf_lRp_ne_pfK : lRp ≠ pfK := by decide
@[simp] theorem pf_pfK_ne_lRn : pfK ≠ lRn := by decide
@[simp] theorem pf_lRn_ne_pfK : lRn ≠ pfK := by decide
@[simp] theorem pf_pfK_ne_lDir : pfK ≠ lDir := by decide
@[simp] theorem pf_lDir_ne_pfK : lDir ≠ pfK := by decide
@[simp] theorem pf_pfK_ne_lFle : pfK ≠ lFle := by decide
@[simp] theorem pf_lFle_ne_pfK : lFle ≠ pfK := by decide
@[simp] theorem pf_pfK_ne_lKb : pfK ≠ lKb := by decide
@[simp] theorem pf_lKb_ne_pfK : lKb ≠ pfK := by decide
@[simp] theorem pf_pfJ_ne_pfK : pfJ ≠ pfK := by decide
@[simp] theorem pf_pfJ_ne_pfH : pfJ ≠ pfH := by decide
@[simp] theorem pf_pfJ_ne_pfD : pfJ ≠ pfD := by decide
@[simp] theorem pf_pfJ_ne_pfB : pfJ ≠ pfB := by decide
@[simp] theorem pf_pfJ_ne_pfX : pfJ ≠ pfX := by decide
@[simp] theorem pf_pfJ_ne_pfR : pfJ ≠ pfR := by decide
@[simp] theorem pf_pfJ_ne_lFl : pfJ ≠ lFl := by decide
@[simp] theorem pf_lFl_ne_pfJ : lFl ≠ pfJ := by decide
@[simp] theorem pf_pfJ_ne_lDh : pfJ ≠ lDh := by decide
@[simp] theorem pf_lDh_ne_pfJ : lDh ≠ pfJ := by decide
@[simp] theorem pf_pfJ_ne_lDt : pfJ ≠ lDt := by decide
@[simp] theorem pf_lDt_ne_pfJ : lDt ≠ pfJ := by decide
@[simp] theorem pf_pfJ_ne_lDg : pfJ ≠ lDg := by decide
@[simp] theorem pf_lDg_ne_pfJ : lDg ≠ pfJ := by decide
@[simp] theorem pf_pfJ_ne_lDi : pfJ ≠ lDi := by decide
@[simp] theorem pf_lDi_ne_pfJ : lDi ≠ pfJ := by decide
@[simp] theorem pf_pfJ_ne_lRp : pfJ ≠ lRp := by decide
@[simp] theorem pf_lRp_ne_pfJ : lRp ≠ pfJ := by decide
@[simp] theorem pf_pfJ_ne_lRn : pfJ ≠ lRn := by decide
@[simp] theorem pf_lRn_ne_pfJ : lRn ≠ pfJ := by decide
@[simp] theorem pf_pfJ_ne_lDir : pfJ ≠ lDir := by decide
@[simp] theorem pf_lDir_ne_pfJ : lDir ≠ pfJ := by decide
@[simp] theorem pf_pfJ_ne_lFle : pfJ ≠ lFle := by decide
@[simp] theorem pf_lFle_ne_pfJ : lFle ≠ pfJ := by decide
@[simp] theorem pf_pfJ_ne_lKb : pfJ ≠ lKb := by decide
@[simp] theorem pf_lKb_ne_pfJ : lKb ≠ pfJ := by decide
@[simp] theorem pf_pfH_ne_pfK : pfH ≠ pfK := by decide
@[simp] theorem pf_pfH_ne_pfJ : pfH ≠ pfJ := by decide
@[simp] theorem pf_pfH_ne_pfD : pfH ≠ pfD := by decide
@[simp] theorem pf_pfH_ne_pfB : pfH ≠ pfB := by decide
@[simp] theorem pf_pfH_ne_pfX : pfH ≠ pfX := by decide
@[simp] theorem pf_pfH_ne_pfR : pfH ≠ pfR := by decide
@[simp] theorem pf_pfH_ne_lFl : pfH ≠ lFl := by decide
@[simp] theorem pf_lFl_ne_pfH : lFl ≠ pfH := by decide
@[simp] theorem pf_pfH_ne_lDh : pfH ≠ lDh := by decide
@[simp] theorem pf_lDh_ne_pfH : lDh ≠ pfH := by decide
@[simp] theorem pf_pfH_ne_lDt : pfH ≠ lDt := by decide
@[simp] theorem pf_lDt_ne_pfH : lDt ≠ pfH := by decide
@[simp] theorem pf_pfH_ne_lDg : pfH ≠ lDg := by decide
@[simp] theorem pf_lDg_ne_pfH : lDg ≠ pfH := by decide
@[simp] theorem pf_pfH_ne_lDi : pfH ≠ lDi := by decide
@[simp] theorem pf_lDi_ne_pfH : lDi ≠ pfH := by decide
@[simp] theorem pf_pfH_ne_lRp : pfH ≠ lRp := by decide
@[simp] theorem pf_lRp_ne_pfH : lRp ≠ pfH := by decide
@[simp] theorem pf_pfH_ne_lRn : pfH ≠ lRn := by decide
@[simp] theorem pf_lRn_ne_pfH : lRn ≠ pfH := by decide
@[simp] theorem pf_pfH_ne_lDir : pfH ≠ lDir := by decide
@[simp] theorem pf_lDir_ne_pfH : lDir ≠ pfH := by decide
@[simp] theorem pf_pfH_ne_lFle : pfH ≠ lFle := by decide
@[simp] theorem pf_lFle_ne_pfH : lFle ≠ pfH := by decide
@[simp] theorem pf_pfH_ne_lKb : pfH ≠ lKb := by decide
@[simp] theorem pf_lKb_ne_pfH : lKb ≠ pfH := by decide
@[simp] theorem pf_pfD_ne_pfK : pfD ≠ pfK := by decide
@[simp] theorem pf_pfD_ne_pfJ : pfD ≠ pfJ := by decide
@[simp] theorem pf_pfD_ne_pfH : pfD ≠ pfH := by decide
@[simp] theorem pf_pfD_ne_pfB : pfD ≠ pfB := by decide
@[simp] theorem pf_pfD_ne_pfX : pfD ≠ pfX := by decide
@[simp] theorem pf_pfD_ne_pfR : pfD ≠ pfR := by decide
@[simp] theorem pf_pfD_ne_lFl : pfD ≠ lFl := by decide
@[simp] theorem pf_lFl_ne_pfD : lFl ≠ pfD := by decide
@[simp] theorem pf_pfD_ne_lDh : pfD ≠ lDh := by decide
@[simp] theorem pf_lDh_ne_pfD : lDh ≠ pfD := by decide
@[simp] theorem pf_pfD_ne_lDt : pfD ≠ lDt := by decide
@[simp] theorem pf_lDt_ne_pfD : lDt ≠ pfD := by decide
@[simp] theorem pf_pfD_ne_lDg : pfD ≠ lDg := by decide
@[simp] theorem pf_lDg_ne_pfD : lDg ≠ pfD := by decide
@[simp] theorem pf_pfD_ne_lDi : pfD ≠ lDi := by decide
@[simp] theorem pf_lDi_ne_pfD : lDi ≠ pfD := by decide
@[simp] theorem pf_pfD_ne_lRp : pfD ≠ lRp := by decide
@[simp] theorem pf_lRp_ne_pfD : lRp ≠ pfD := by decide
@[simp] theorem pf_pfD_ne_lRn : pfD ≠ lRn := by decide
@[simp] theorem pf_lRn_ne_pfD : lRn ≠ pfD := by decide
@[simp] theorem pf_pfD_ne_lDir : pfD ≠ lDir := by decide
@[simp] theorem pf_lDir_ne_pfD : lDir ≠ pfD := by decide
@[simp] theorem pf_pfD_ne_lFle : pfD ≠ lFle := by decide
@[simp] theorem pf_lFle_ne_pfD : lFle ≠ pfD := by decide
@[simp] theorem pf_pfD_ne_lKb : pfD ≠ lKb := by decide
@[simp] theorem pf_lKb_ne_pfD : lKb ≠ pfD := by decide
@[simp] theorem pf_pfB_ne_pfK : pfB ≠ pfK := by decide
@[simp] theorem pf_pfB_ne_pfJ : pfB ≠ pfJ := by decide
@[simp] theorem pf_pfB_ne_pfH : pfB ≠ pfH := by decide
@[simp] theorem pf_pfB_ne_pfD : pfB ≠ pfD := by decide
@[simp] theorem pf_pfB_ne_pfX : pfB ≠ pfX := by decide
@[simp] theorem pf_pfB_ne_pfR : pfB ≠ pfR := by decide
@[simp] theorem pf_pfB_ne_lFl : pfB ≠ lFl := by decide
@[simp] theorem pf_lFl_ne_pfB : lFl ≠ pfB := by decide
@[simp] theorem pf_pfB_ne_lDh : pfB ≠ lDh := by decide
@[simp] theorem pf_lDh_ne_pfB : lDh ≠ pfB := by decide
@[simp] theorem pf_pfB_ne_lDt : pfB ≠ lDt := by decide
@[simp] theorem pf_lDt_ne_pfB : lDt ≠ pfB := by decide
@[simp] theorem pf_pfB_ne_lDg : pfB ≠ lDg := by decide
@[simp] theorem pf_lDg_ne_pfB : lDg ≠ pfB := by decide
@[simp] theorem pf_pfB_ne_lDi : pfB ≠ lDi := by decide
@[simp] theorem pf_lDi_ne_pfB : lDi ≠ pfB := by decide
@[simp] theorem pf_pfB_ne_lRp : pfB ≠ lRp := by decide
@[simp] theorem pf_lRp_ne_pfB : lRp ≠ pfB := by decide
@[simp] theorem pf_pfB_ne_lRn : pfB ≠ lRn := by decide
@[simp] theorem pf_lRn_ne_pfB : lRn ≠ pfB := by decide
@[simp] theorem pf_pfB_ne_lDir : pfB ≠ lDir := by decide
@[simp] theorem pf_lDir_ne_pfB : lDir ≠ pfB := by decide
@[simp] theorem pf_pfB_ne_lFle : pfB ≠ lFle := by decide
@[simp] theorem pf_lFle_ne_pfB : lFle ≠ pfB := by decide
@[simp] theorem pf_pfB_ne_lKb : pfB ≠ lKb := by decide
@[simp] theorem pf_lKb_ne_pfB : lKb ≠ pfB := by decide
@[simp] theorem pf_pfX_ne_pfK : pfX ≠ pfK := by decide
@[simp] theorem pf_pfX_ne_pfJ : pfX ≠ pfJ := by decide
@[simp] theorem pf_pfX_ne_pfH : pfX ≠ pfH := by decide
@[simp] theorem pf_pfX_ne_pfD : pfX ≠ pfD := by decide
@[simp] theorem pf_pfX_ne_pfB : pfX ≠ pfB := by decide
@[simp] theorem pf_pfX_ne_pfR : pfX ≠ pfR := by decide
@[simp] theorem pf_pfX_ne_lFl : pfX ≠ lFl := by decide
@[simp] theorem pf_lFl_ne_pfX : lFl ≠ pfX := by decide
@[simp] theorem pf_pfX_ne_lDh : pfX ≠ lDh := by decide
@[simp] theorem pf_lDh_ne_pfX : lDh ≠ pfX := by decide
@[simp] theorem pf_pfX_ne_lDt : pfX ≠ lDt := by decide
@[simp] theorem pf_lDt_ne_pfX : lDt ≠ pfX := by decide
@[simp] theorem pf_pfX_ne_lDg : pfX ≠ lDg := by decide
@[simp] theorem pf_lDg_ne_pfX : lDg ≠ pfX := by decide
@[simp] theorem pf_pfX_ne_lDi : pfX ≠ lDi := by decide
@[simp] theorem pf_lDi_ne_pfX : lDi ≠ pfX := by decide
@[simp] theorem pf_pfX_ne_lRp : pfX ≠ lRp := by decide
@[simp] theorem pf_lRp_ne_pfX : lRp ≠ pfX := by decide
@[simp] theorem pf_pfX_ne_lRn : pfX ≠ lRn := by decide
@[simp] theorem pf_lRn_ne_pfX : lRn ≠ pfX := by decide
@[simp] theorem pf_pfX_ne_lDir : pfX ≠ lDir := by decide
@[simp] theorem pf_lDir_ne_pfX : lDir ≠ pfX := by decide
@[simp] theorem pf_pfX_ne_lFle : pfX ≠ lFle := by decide
@[simp] theorem pf_lFle_ne_pfX : lFle ≠ pfX := by decide
@[simp] theorem pf_pfX_ne_lKb : pfX ≠ lKb := by decide
@[simp] theorem pf_lKb_ne_pfX : lKb ≠ pfX := by decide
@[simp] theorem pf_pfR_ne_pfK : pfR ≠ pfK := by decide
@[simp] theorem pf_pfR_ne_pfJ : pfR ≠ pfJ := by decide
@[simp] theorem pf_pfR_ne_pfH : pfR ≠ pfH := by decide
@[simp] theorem pf_pfR_ne_pfD : pfR ≠ pfD := by decide
@[simp] theorem pf_pfR_ne_pfB : pfR ≠ pfB := by decide
@[simp] theorem pf_pfR_ne_pfX : pfR ≠ pfX := by decide
@[simp] theorem pf_pfR_ne_lFl : pfR ≠ lFl := by decide
@[simp] theorem pf_lFl_ne_pfR : lFl ≠ pfR := by decide
@[simp] theorem pf_pfR_ne_lDh : pfR ≠ lDh := by decide
@[simp] theorem pf_lDh_ne_pfR : lDh ≠ pfR := by decide
@[simp] theorem pf_pfR_ne_lDt : pfR ≠ lDt := by decide
@[simp] theorem pf_lDt_ne_pfR : lDt ≠ pfR := by decide
@[simp] theorem pf_pfR_ne_lDg : pfR ≠ lDg := by decide
@[simp] theorem pf_lDg_ne_pfR : lDg ≠ pfR := by decide
@[simp] theorem pf_pfR_ne_lDi : pfR ≠ lDi := by decide
@[simp] theorem pf_lDi_ne_pfR : lDi ≠ pfR := by decide
@[simp] theorem pf_pfR_ne_lRp : pfR ≠ lRp := by decide
@[simp] theorem pf_lRp_ne_pfR : lRp ≠ pfR := by decide
@[simp] theorem pf_pfR_ne_lRn : pfR ≠ lRn := by decide
@[simp] theorem pf_lRn_ne_pfR : lRn ≠ pfR := by decide
@[simp] theorem pf_pfR_ne_lDir : pfR ≠ lDir := by decide
@[simp] theorem pf_lDir_ne_pfR : lDir ≠ pfR := by decide
@[simp] theorem pf_pfR_ne_lFle : pfR ≠ lFle := by decide
@[simp] theorem pf_lFle_ne_pfR : lFle ≠ pfR := by decide
@[simp] theorem pf_pfR_ne_lKb : pfR ≠ lKb := by decide
@[simp] theorem pf_lKb_ne_pfR : lKb ≠ pfR := by decide

theorem hvCodes_H {C : Ctx} (hc : HvCodes C) (H : List (BitVec 64)) : HvCodes (ctxH C H) :=
  ⟨hc.ml, hc.lbb, hc.bvb, codesB_H hc.cB H, hc.self⟩

def pfParams : List MlS := [pfK, pfJ, pfH]
def pfLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, pfD, pfB, pfX, pfR]

def pfBody : ProgHOL 64 := prologue pfLocals
  (.ite (tagIsE pfH 6)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pfH)) (.seq eViewP
    (.seq (.assign .local pfD (.load .one (vv lRp)))
    (.seq (.assign .local pfB (.load .one (.op .add [vv lRp, .const 8])))
    (.ite (.cmp .equal (vv pfK) (.const 0))
      (.seq (.call (some (some (.local, pfX), none)) fHi [.const 0, vv pfJ, vv pfH])
        (.ite (vv pfX) (.return (.const 0)) (.return (.op .add [vv pfD, .const 1]))))
      (.seq (.call (some (some (.local, pfX), none)) fHi [.const 0, vv pfJ, vv pfD])
        (.ite (vv pfX) (.return (.const 0))
          (.seq (.call (some (some (.local, pfR), none)) fPf
              [.op .sub [vv pfK, .const 1], .op .add [vv pfJ, .const 1], vv pfB])
            (.return (vv pfR)))))))))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem pf_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ pfLocals → (ctxEnv C ++ pfParams.zip vals).get x = none :=
  Knot.params_none C pfLocals pfParams vals (by decide) (by decide)

structure PfCodes (C : Ctx) : Prop where
  hv : HvCodes C
  hi : C.code.lookup fHi = some (hiParams.map (fun p => (p, ShapeHOL.one)), hiBody, .one)
  self : C.code.lookup fPf = some (pfParams.map (fun p => (p, ShapeHOL.one)), pfBody, .one)

theorem pf_spec (C : Ctx) (hok : CtxOK C) (hc : PfCodes C) :
    ∀ k (j : Nat) (h : EIdx) (H : List (BitVec 64)) (s : AState), C.H <+: H → j + k < 2 ^ 63 →
      SpecR (σ := σ) (Pre (ctxH C H) s (pfParams.zip [BitVec.ofNat 64 k, BitVec.ofNat 64 j, Enc.idxW h])) pfBody s
        (projGuardFast k j h) (UD.PostO (ctxH C H)) := by
  have hnone : ∀ {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} {D : List MlS},
      SpecR (σ := σ) (Inv (ctxH C H) s Γ M D) (.return (.const 0)) s (pure none) (UD.PostO (ctxH C H)) :=
    fun {H s Γ M D} => specR_returnI _ (optW none) (by simp [optW]; rfl)
      (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  intro k
  induction k with
  | zero =>
    intro j h H s hp hjk
    refine specR_prologue (UD.postO_locals _) (pf_none _ _) ?_
    rw [projGuardFast]
    refine Knot.specR_tagIteV pfH h 6 (by decide) (by decide) (by simp +decide [Env.get, pfParams, ctxEnv]) (fun htg => ?_) (fun htg => ?_)
    swap
    · rw [if_neg (show ¬ (h.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg)]
      exact hnone
    rw [if_pos (show (h.tag == ETag.forallE) = true by simp [htg, ETag.forallE])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv pfH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, pfParams, ctxEnv]) ?_
    refine specR_viewP (C := ctxH C H) h (by simp) (by simp +decide [Env.get] <;> rfl)
      (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
    refine specR_congr (view_bind_eq h v _ s hv) ?_
    have h6 : v.tagN = 6 := by rw [htn, htg]; rfl
    obtain ⟨dom, b, rfl⟩ : ∃ dom b, v = .forallE dom b := by cases v <;> simp [ENodeView.tagN] at h6 ⊢
    dsimp only
    refine specR_loadI' pfD (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW dom) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW dom) [Enc.idxW b] []) ?_
    refine specR_loadI' pfB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW dom) (Enc.idxW b) [] []) ?_
    refine specR_dropM ?_
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, pfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_callNIH (C := ctxH C H) pfX fHi hiParams [.const 0, vv pfJ, vv pfH] hiBody
      [BitVec.ofNat 64 0, BitVec.ofNat 64 j, Enc.idxW h] (by decide) rfl (by decide) hc.hi
      ⟨rfl, by simp +decide [Env.get, pfParams, ctxEnv], by simp +decide [Env.get, pfParams, ctxEnv], trivial⟩ (PostB (ctxH C H)) (fun b w _ _ => w = boolW b)
      (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu hiParams _ rfl hlk)
        (hi_spec (ctxH C H) (ctxOK_H hok H) (hvCodes_H hc.hv H) s 0 j h (by unfold coreWalkFuel; norm_num) (by omega)))
      (fun b w s1 H1 hp1 hw => ?_)
    subst hw
    cases b
    · refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact specR_returnI _ (optW (some dom)) (by simp [sev, optW, optWG])
        (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [↓reduceIte]
      exact specR_returnI _ (optW none) (by simp [optW]; rfl)
        (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro j h H s hp hjk
    refine specR_prologue (UD.postO_locals _) (pf_none _ _) ?_
    rw [projGuardFast]
    refine Knot.specR_tagIteV pfH h 6 (by decide) (by decide) (by simp +decide [Env.get, pfParams, ctxEnv]) (fun htg => ?_) (fun htg => ?_)
    swap
    · rw [if_neg (show ¬ (h.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg)]
      exact hnone
    rw [if_pos (show (h.tag == ETag.forallE) = true by simp [htg, ETag.forallE])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv pfH) (Enc.idxW h) (by decide) (by simp +decide [Env.get, pfParams, ctxEnv]) ?_
    refine specR_viewP (C := ctxH C H) h (by simp) (by simp +decide [Env.get] <;> rfl)
      (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
    refine specR_congr (view_bind_eq h v _ s hv) ?_
    have h6 : v.tagN = 6 := by rw [htn, htg]; rfl
    obtain ⟨dom, b, rfl⟩ : ∃ dom b, v = .forallE dom b := by cases v <;> simp [ENodeView.tagN] at h6 ⊢
    dsimp only
    refine specR_loadI' pfD (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW dom) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW dom) [Enc.idxW b] []) ?_
    refine specR_loadI' pfB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW dom) (Enc.idxW b) [] []) ?_
    refine specR_dropM ?_
    have hne := ofNat_succ_ne k (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, pfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_callNIH (C := ctxH C H) pfX fHi hiParams [.const 0, vv pfJ, vv pfD] hiBody
      [BitVec.ofNat 64 0, BitVec.ofNat 64 j, Enc.idxW dom] (by decide) rfl (by decide) hc.hi
      ⟨rfl, by simp +decide [Env.get, pfParams, ctxEnv], by simp +decide [Env.get, pfParams, ctxEnv], trivial⟩ (PostB (ctxH C H)) (fun b w _ _ => w = boolW b)
      (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu hiParams _ rfl hlk)
        (hi_spec (ctxH C H) (ctxOK_H hok H) (hvCodes_H hc.hv H) s 0 j dom (by unfold coreWalkFuel; norm_num) (by omega)))
      (fun c w s1 H1 hp1 hw => ?_)
    subst hw
    cases c
    · refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine specR_congr (m' := projGuardFast k (j + 1) b >>= fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H1) pfR fPf pfParams
        [.op .sub [vv pfK, .const 1], .op .add [vv pfJ, .const 1], vv pfB] pfBody
        [BitVec.ofNat 64 k, BitVec.ofNat 64 (j + 1), Enc.idxW b] (by decide) rfl (by decide) hc.self
        ⟨by simp +decide [sev, Env.get, pfParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _,
          by simp +decide [sev, Env.get, pfParams, ctxEnv]; exact word_add1_eq j, by simp, trivial⟩
        (UD.PostO (ctxH C H1)) (fun a w _ _ => w = optW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pfParams _ rfl hlk)
          (ih (j + 1) b H1 s1 (hp.trans hp1) (by omega)))
        (fun r w s2 H2 hp2 hw => ?_)
      subst hw
      exact specR_returnI _ (optW r) (by simp)
        (fun t ht => ⟨H2, hp1.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [↓reduceIte]
      exact specR_returnI _ (optW none) (by simp [optW]; rfl)
        (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
