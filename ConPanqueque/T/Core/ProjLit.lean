import ConPanqueque.T.Str.StrCtor
import ConPanqueque.T.Core.WcStep
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `projLitToCtor`: a string-literal scrutinee to its reduced constructor form

A `lit` handle is viewed; a string literal (row word `1`) under the `strLit` flag (`Glit` bit 1) is expanded
(`strLitToCtor`) and head-normalized (`whnf`); every other handle is returned as is.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.Str
open ConPanqueque.V.Enc

def plW := ofString "plw"
def plL := ofString "pll"
def plC := ofString "plc"
def plR := ofString "plr"
def fPl := ofString "projLitToCtor"

@[simp] theorem pl_plW_ne_plL : plW ≠ plL := by decide
@[simp] theorem pl_plW_ne_plC : plW ≠ plC := by decide
@[simp] theorem pl_plW_ne_plR : plW ≠ plR := by decide
@[simp] theorem pl_plW_ne_lFl : plW ≠ lFl := by decide
@[simp] theorem pl_lFl_ne_plW : lFl ≠ plW := by decide
@[simp] theorem pl_plW_ne_lDh : plW ≠ lDh := by decide
@[simp] theorem pl_lDh_ne_plW : lDh ≠ plW := by decide
@[simp] theorem pl_plW_ne_lDt : plW ≠ lDt := by decide
@[simp] theorem pl_lDt_ne_plW : lDt ≠ plW := by decide
@[simp] theorem pl_plW_ne_lDg : plW ≠ lDg := by decide
@[simp] theorem pl_lDg_ne_plW : lDg ≠ plW := by decide
@[simp] theorem pl_plW_ne_lDi : plW ≠ lDi := by decide
@[simp] theorem pl_lDi_ne_plW : lDi ≠ plW := by decide
@[simp] theorem pl_plW_ne_lRp : plW ≠ lRp := by decide
@[simp] theorem pl_lRp_ne_plW : lRp ≠ plW := by decide
@[simp] theorem pl_plW_ne_lRn : plW ≠ lRn := by decide
@[simp] theorem pl_lRn_ne_plW : lRn ≠ plW := by decide
@[simp] theorem pl_plW_ne_lFle : plW ≠ lFle := by decide
@[simp] theorem pl_lFle_ne_plW : lFle ≠ plW := by decide
@[simp] theorem pl_plW_ne_lDir : plW ≠ lDir := by decide
@[simp] theorem pl_lDir_ne_plW : lDir ≠ plW := by decide
@[simp] theorem pl_plW_ne_lKb : plW ≠ lKb := by decide
@[simp] theorem pl_lKb_ne_plW : lKb ≠ plW := by decide
@[simp] theorem pl_plW_ne_kFu : plW ≠ kFu := by decide
@[simp] theorem pl_kFu_ne_plW : kFu ≠ plW := by decide
@[simp] theorem pl_plW_ne_kD : plW ≠ kD := by decide
@[simp] theorem pl_kD_ne_plW : kD ≠ plW := by decide
@[simp] theorem pl_plW_ne_kE : plW ≠ kE := by decide
@[simp] theorem pl_kE_ne_plW : kE ≠ plW := by decide
@[simp] theorem pl_plL_ne_plW : plL ≠ plW := by decide
@[simp] theorem pl_plL_ne_plC : plL ≠ plC := by decide
@[simp] theorem pl_plL_ne_plR : plL ≠ plR := by decide
@[simp] theorem pl_plL_ne_lFl : plL ≠ lFl := by decide
@[simp] theorem pl_lFl_ne_plL : lFl ≠ plL := by decide
@[simp] theorem pl_plL_ne_lDh : plL ≠ lDh := by decide
@[simp] theorem pl_lDh_ne_plL : lDh ≠ plL := by decide
@[simp] theorem pl_plL_ne_lDt : plL ≠ lDt := by decide
@[simp] theorem pl_lDt_ne_plL : lDt ≠ plL := by decide
@[simp] theorem pl_plL_ne_lDg : plL ≠ lDg := by decide
@[simp] theorem pl_lDg_ne_plL : lDg ≠ plL := by decide
@[simp] theorem pl_plL_ne_lDi : plL ≠ lDi := by decide
@[simp] theorem pl_lDi_ne_plL : lDi ≠ plL := by decide
@[simp] theorem pl_plL_ne_lRp : plL ≠ lRp := by decide
@[simp] theorem pl_lRp_ne_plL : lRp ≠ plL := by decide
@[simp] theorem pl_plL_ne_lRn : plL ≠ lRn := by decide
@[simp] theorem pl_lRn_ne_plL : lRn ≠ plL := by decide
@[simp] theorem pl_plL_ne_lFle : plL ≠ lFle := by decide
@[simp] theorem pl_lFle_ne_plL : lFle ≠ plL := by decide
@[simp] theorem pl_plL_ne_lDir : plL ≠ lDir := by decide
@[simp] theorem pl_lDir_ne_plL : lDir ≠ plL := by decide
@[simp] theorem pl_plL_ne_lKb : plL ≠ lKb := by decide
@[simp] theorem pl_lKb_ne_plL : lKb ≠ plL := by decide
@[simp] theorem pl_plL_ne_kFu : plL ≠ kFu := by decide
@[simp] theorem pl_kFu_ne_plL : kFu ≠ plL := by decide
@[simp] theorem pl_plL_ne_kD : plL ≠ kD := by decide
@[simp] theorem pl_kD_ne_plL : kD ≠ plL := by decide
@[simp] theorem pl_plL_ne_kE : plL ≠ kE := by decide
@[simp] theorem pl_kE_ne_plL : kE ≠ plL := by decide
@[simp] theorem pl_plC_ne_plW : plC ≠ plW := by decide
@[simp] theorem pl_plC_ne_plL : plC ≠ plL := by decide
@[simp] theorem pl_plC_ne_plR : plC ≠ plR := by decide
@[simp] theorem pl_plC_ne_lFl : plC ≠ lFl := by decide
@[simp] theorem pl_lFl_ne_plC : lFl ≠ plC := by decide
@[simp] theorem pl_plC_ne_lDh : plC ≠ lDh := by decide
@[simp] theorem pl_lDh_ne_plC : lDh ≠ plC := by decide
@[simp] theorem pl_plC_ne_lDt : plC ≠ lDt := by decide
@[simp] theorem pl_lDt_ne_plC : lDt ≠ plC := by decide
@[simp] theorem pl_plC_ne_lDg : plC ≠ lDg := by decide
@[simp] theorem pl_lDg_ne_plC : lDg ≠ plC := by decide
@[simp] theorem pl_plC_ne_lDi : plC ≠ lDi := by decide
@[simp] theorem pl_lDi_ne_plC : lDi ≠ plC := by decide
@[simp] theorem pl_plC_ne_lRp : plC ≠ lRp := by decide
@[simp] theorem pl_lRp_ne_plC : lRp ≠ plC := by decide
@[simp] theorem pl_plC_ne_lRn : plC ≠ lRn := by decide
@[simp] theorem pl_lRn_ne_plC : lRn ≠ plC := by decide
@[simp] theorem pl_plC_ne_lFle : plC ≠ lFle := by decide
@[simp] theorem pl_lFle_ne_plC : lFle ≠ plC := by decide
@[simp] theorem pl_plC_ne_lDir : plC ≠ lDir := by decide
@[simp] theorem pl_lDir_ne_plC : lDir ≠ plC := by decide
@[simp] theorem pl_plC_ne_lKb : plC ≠ lKb := by decide
@[simp] theorem pl_lKb_ne_plC : lKb ≠ plC := by decide
@[simp] theorem pl_plC_ne_kFu : plC ≠ kFu := by decide
@[simp] theorem pl_kFu_ne_plC : kFu ≠ plC := by decide
@[simp] theorem pl_plC_ne_kD : plC ≠ kD := by decide
@[simp] theorem pl_kD_ne_plC : kD ≠ plC := by decide
@[simp] theorem pl_plC_ne_kE : plC ≠ kE := by decide
@[simp] theorem pl_kE_ne_plC : kE ≠ plC := by decide
@[simp] theorem pl_plR_ne_plW : plR ≠ plW := by decide
@[simp] theorem pl_plR_ne_plL : plR ≠ plL := by decide
@[simp] theorem pl_plR_ne_plC : plR ≠ plC := by decide
@[simp] theorem pl_plR_ne_lFl : plR ≠ lFl := by decide
@[simp] theorem pl_lFl_ne_plR : lFl ≠ plR := by decide
@[simp] theorem pl_plR_ne_lDh : plR ≠ lDh := by decide
@[simp] theorem pl_lDh_ne_plR : lDh ≠ plR := by decide
@[simp] theorem pl_plR_ne_lDt : plR ≠ lDt := by decide
@[simp] theorem pl_lDt_ne_plR : lDt ≠ plR := by decide
@[simp] theorem pl_plR_ne_lDg : plR ≠ lDg := by decide
@[simp] theorem pl_lDg_ne_plR : lDg ≠ plR := by decide
@[simp] theorem pl_plR_ne_lDi : plR ≠ lDi := by decide
@[simp] theorem pl_lDi_ne_plR : lDi ≠ plR := by decide
@[simp] theorem pl_plR_ne_lRp : plR ≠ lRp := by decide
@[simp] theorem pl_lRp_ne_plR : lRp ≠ plR := by decide
@[simp] theorem pl_plR_ne_lRn : plR ≠ lRn := by decide
@[simp] theorem pl_lRn_ne_plR : lRn ≠ plR := by decide
@[simp] theorem pl_plR_ne_lFle : plR ≠ lFle := by decide
@[simp] theorem pl_lFle_ne_plR : lFle ≠ plR := by decide
@[simp] theorem pl_plR_ne_lDir : plR ≠ lDir := by decide
@[simp] theorem pl_lDir_ne_plR : lDir ≠ plR := by decide
@[simp] theorem pl_plR_ne_lKb : plR ≠ lKb := by decide
@[simp] theorem pl_lKb_ne_plR : lKb ≠ plR := by decide
@[simp] theorem pl_plR_ne_kFu : plR ≠ kFu := by decide
@[simp] theorem pl_kFu_ne_plR : kFu ≠ plR := by decide
@[simp] theorem pl_plR_ne_kD : plR ≠ kD := by decide
@[simp] theorem pl_kD_ne_plR : kD ≠ plR := by decide
@[simp] theorem pl_plR_ne_kE : plR ≠ kE := by decide
@[simp] theorem pl_kE_ne_plR : kE ≠ plR := by decide

def plLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, plW, plL, plC, plR]

def plCore : ProgHOL 64 :=
  .ite (tagIsE kE 8)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv kE)) (.seq eViewP
    (.seq (.assign .local plW (.load .one (vv lRp)))
    (.ite (.cmp .equal (vv plW) (.const 1))
      (.seq (.assign .local plL (.var .global gLit))
      (.ite (.op .and [vv plL, .const 2])
        (.seq (.call (some (some (.local, plC), none)) fTc [vv kE])
        (.seq (.call (some (some (.local, plR), none)) fW [vv kFu, vv kD, vv plC]) (.return (vv plR))))
        (.return (vv kE))))
      (.return (vv kE)))))))
    (.return (vv kE))

def plBody : ProgHOL 64 := prologue plLocals plCore

section
variable {σ : Type}

theorem pl_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ plLocals → (ctxEnv C ++ kParams.zip vals).get x = none :=
  Knot.params_none C plLocals kParams vals (by decide) (by decide)

theorem litW_and2 (fe : IFEnv) : litW fe &&& 2#64 = 2 * boolW fe.strLit := by
  unfold litW boolW; cases fe.natLit <;> cases fe.strLit <;> decide

theorem pl_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (hc : TcCodes C)
    (hct : C.code.lookup fTc = some ([(tcH, ShapeHOL.one)], tcBody C, .one))
    (hcw : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one))
    (s : AState) (d : Nat) (h : EIdx)
    (hW : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ e', Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d e')
      (PostK (ctxH C H))) :
    SpecR (σ := σ) (Pre C s (kParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW h])) plBody s
      (projLitToCtor (knot mode C n) C.fe d h) (PostK C) := by
  refine specR_prologue (Knot.postK_locals C) (pl_none C _) ?_
  unfold plCore projLitToCtor
  have hret : ∀ {Γ : Env} {M : Mem}, Γ.get kE = some (Enc.idxW h) →
      SpecR (σ := σ) (Inv C s Γ M (ctxLocals ++ plLocals)) (.return (vv kE)) s (pure h) (PostK C) :=
    fun hE => specR_returnI _ (Enc.idxW h) (by simpa using hE)
      (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine Knot.specR_tagIteV kE h 8 (by decide) (by decide) (by simp +decide [Env.get, kParams, ctxEnv])
    (fun htg => ?_) (fun htg => ?_)
  · rw [if_pos (show (h.tag == ETag.lit) = true by simp [htg, ETag.lit])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_assignI lDh (vv kE) (Enc.idxW h) (by decide) (by simp +decide [Env.get, kParams, ctxEnv]) ?_
    refine ILP.specR_viewIv h (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
      (fun v P hv htn _ => ?_)
    have h8 : v.tagN = 8 := by rw [htn, htg]; rfl
    obtain ⟨l, rfl⟩ := tagN_lit h8
    cases l with
    | natVal m =>
      refine specR_loadI' plW (vv lRp) P (P + BitVec.ofNat 64 0) 0 (by decide) (by simp) (by simp)
        (by simpa [encEView, Enc.encLit] using wordsAt_mem0 P 0 (limbs m) []) ?_
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
        (fun _ => ?_)
      exact hret (by simp +decide [Env.get, kParams, ctxEnv])
    | strVal str =>
      refine specR_loadI' plW (vv lRp) P (P + BitVec.ofNat 64 0) 1 (by decide) (by simp) (by simp)
        (by simpa [encEView, Enc.encLit] using wordsAt_mem0 P 1 (strW str) []) ?_
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      refine specR_gLitI plL (by decide) ?_
      dsimp only
      by_cases hsl : C.fe.strLit = true
      · refine specR_ifI _ 2 (by simp [sev, litW_and2, hsl, boolW]) (fun _ => ?_)
          (fun h => absurd h (by decide))
        rw [if_pos hsl]
        refine specR_dropM ?_
        refine specR_callKH plC fTc [tcH] [vv kE] (tcBody C) [Enc.idxW h] (by decide) rfl (by decide) hct
          ⟨by simp +decide [Env.get, kParams, ctxEnv], trivial⟩ (tc_spec ra C hok hc s h str hv)
          (fun c s1 H1 hp1 => ?_)
        refine specR_congr (m' := (knot mode C n).whnf d c >>= fun r => pure r) (by simp) ?_
        refine Big.specR_callKC (C := ctxH C H1) plR fW kParams [vv kFu, vv kD, vv plC] (whnfE C fWB)
          [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW c] (by decide) rfl (by decide) hcw
          ⟨by simp +decide [Env.get, kParams, ctxEnv], by simp +decide [Env.get, kParams, ctxEnv], by simp, trivial⟩
          (hW H1 s1 hp1 c) (fun r s2 H2 hp2 _ => ?_)
        exact specR_returnI _ (Enc.idxW r) (by simp)
          (fun t ht => ⟨H2, hp1.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      · have hf : C.fe.strLit = false := by simpa using hsl
        refine specR_ifI _ 0 (by simp [sev, litW_and2, hf, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
        rw [if_neg hsl]
        exact hret (by simp +decide [Env.get, kParams, ctxEnv])
  · rw [if_neg (show ¬ (h.tag == ETag.lit) = true by simpa [ETag.lit] using htg)]
    exact hret (by simp +decide [Env.get, kParams, ctxEnv])

end

end ConPanqueque.T.WC
