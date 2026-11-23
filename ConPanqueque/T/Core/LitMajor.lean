import ConPanqueque.T.Core.NatLitCtor
import ConPanqueque.T.Core.ProjLit
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `litMajorToCtor`: a literal major premise in constructor form

A string literal (row word `1`) under `strLit` is expanded and head-normalized, as in `projLitToCtor`; a `Nat`
literal under `natLit` goes one layer (`natLitToCtor`); every other handle is returned as is.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.Str
open ConPanqueque.V.Enc

def lmW := ofString "lmw"
def lmL := ofString "lml"
def lmC := ofString "lmc"
def lmR := ofString "lmr"
def fLm := ofString "litMajorToCtor"

@[simp] theorem lm_lmW_ne_lmL : lmW ≠ lmL := by decide
@[simp] theorem lm_lmW_ne_lmC : lmW ≠ lmC := by decide
@[simp] theorem lm_lmW_ne_lmR : lmW ≠ lmR := by decide
@[simp] theorem lm_lmW_ne_lFl : lmW ≠ lFl := by decide
@[simp] theorem lm_lFl_ne_lmW : lFl ≠ lmW := by decide
@[simp] theorem lm_lmW_ne_lDh : lmW ≠ lDh := by decide
@[simp] theorem lm_lDh_ne_lmW : lDh ≠ lmW := by decide
@[simp] theorem lm_lmW_ne_lDt : lmW ≠ lDt := by decide
@[simp] theorem lm_lDt_ne_lmW : lDt ≠ lmW := by decide
@[simp] theorem lm_lmW_ne_lDg : lmW ≠ lDg := by decide
@[simp] theorem lm_lDg_ne_lmW : lDg ≠ lmW := by decide
@[simp] theorem lm_lmW_ne_lDi : lmW ≠ lDi := by decide
@[simp] theorem lm_lDi_ne_lmW : lDi ≠ lmW := by decide
@[simp] theorem lm_lmW_ne_lRp : lmW ≠ lRp := by decide
@[simp] theorem lm_lRp_ne_lmW : lRp ≠ lmW := by decide
@[simp] theorem lm_lmW_ne_lRn : lmW ≠ lRn := by decide
@[simp] theorem lm_lRn_ne_lmW : lRn ≠ lmW := by decide
@[simp] theorem lm_lmW_ne_lFle : lmW ≠ lFle := by decide
@[simp] theorem lm_lFle_ne_lmW : lFle ≠ lmW := by decide
@[simp] theorem lm_lmW_ne_lDir : lmW ≠ lDir := by decide
@[simp] theorem lm_lDir_ne_lmW : lDir ≠ lmW := by decide
@[simp] theorem lm_lmW_ne_lKb : lmW ≠ lKb := by decide
@[simp] theorem lm_lKb_ne_lmW : lKb ≠ lmW := by decide
@[simp] theorem lm_lmW_ne_kFu : lmW ≠ kFu := by decide
@[simp] theorem lm_kFu_ne_lmW : kFu ≠ lmW := by decide
@[simp] theorem lm_lmW_ne_kD : lmW ≠ kD := by decide
@[simp] theorem lm_kD_ne_lmW : kD ≠ lmW := by decide
@[simp] theorem lm_lmW_ne_kE : lmW ≠ kE := by decide
@[simp] theorem lm_kE_ne_lmW : kE ≠ lmW := by decide
@[simp] theorem lm_lmL_ne_lmW : lmL ≠ lmW := by decide
@[simp] theorem lm_lmL_ne_lmC : lmL ≠ lmC := by decide
@[simp] theorem lm_lmL_ne_lmR : lmL ≠ lmR := by decide
@[simp] theorem lm_lmL_ne_lFl : lmL ≠ lFl := by decide
@[simp] theorem lm_lFl_ne_lmL : lFl ≠ lmL := by decide
@[simp] theorem lm_lmL_ne_lDh : lmL ≠ lDh := by decide
@[simp] theorem lm_lDh_ne_lmL : lDh ≠ lmL := by decide
@[simp] theorem lm_lmL_ne_lDt : lmL ≠ lDt := by decide
@[simp] theorem lm_lDt_ne_lmL : lDt ≠ lmL := by decide
@[simp] theorem lm_lmL_ne_lDg : lmL ≠ lDg := by decide
@[simp] theorem lm_lDg_ne_lmL : lDg ≠ lmL := by decide
@[simp] theorem lm_lmL_ne_lDi : lmL ≠ lDi := by decide
@[simp] theorem lm_lDi_ne_lmL : lDi ≠ lmL := by decide
@[simp] theorem lm_lmL_ne_lRp : lmL ≠ lRp := by decide
@[simp] theorem lm_lRp_ne_lmL : lRp ≠ lmL := by decide
@[simp] theorem lm_lmL_ne_lRn : lmL ≠ lRn := by decide
@[simp] theorem lm_lRn_ne_lmL : lRn ≠ lmL := by decide
@[simp] theorem lm_lmL_ne_lFle : lmL ≠ lFle := by decide
@[simp] theorem lm_lFle_ne_lmL : lFle ≠ lmL := by decide
@[simp] theorem lm_lmL_ne_lDir : lmL ≠ lDir := by decide
@[simp] theorem lm_lDir_ne_lmL : lDir ≠ lmL := by decide
@[simp] theorem lm_lmL_ne_lKb : lmL ≠ lKb := by decide
@[simp] theorem lm_lKb_ne_lmL : lKb ≠ lmL := by decide
@[simp] theorem lm_lmL_ne_kFu : lmL ≠ kFu := by decide
@[simp] theorem lm_kFu_ne_lmL : kFu ≠ lmL := by decide
@[simp] theorem lm_lmL_ne_kD : lmL ≠ kD := by decide
@[simp] theorem lm_kD_ne_lmL : kD ≠ lmL := by decide
@[simp] theorem lm_lmL_ne_kE : lmL ≠ kE := by decide
@[simp] theorem lm_kE_ne_lmL : kE ≠ lmL := by decide
@[simp] theorem lm_lmC_ne_lmW : lmC ≠ lmW := by decide
@[simp] theorem lm_lmC_ne_lmL : lmC ≠ lmL := by decide
@[simp] theorem lm_lmC_ne_lmR : lmC ≠ lmR := by decide
@[simp] theorem lm_lmC_ne_lFl : lmC ≠ lFl := by decide
@[simp] theorem lm_lFl_ne_lmC : lFl ≠ lmC := by decide
@[simp] theorem lm_lmC_ne_lDh : lmC ≠ lDh := by decide
@[simp] theorem lm_lDh_ne_lmC : lDh ≠ lmC := by decide
@[simp] theorem lm_lmC_ne_lDt : lmC ≠ lDt := by decide
@[simp] theorem lm_lDt_ne_lmC : lDt ≠ lmC := by decide
@[simp] theorem lm_lmC_ne_lDg : lmC ≠ lDg := by decide
@[simp] theorem lm_lDg_ne_lmC : lDg ≠ lmC := by decide
@[simp] theorem lm_lmC_ne_lDi : lmC ≠ lDi := by decide
@[simp] theorem lm_lDi_ne_lmC : lDi ≠ lmC := by decide
@[simp] theorem lm_lmC_ne_lRp : lmC ≠ lRp := by decide
@[simp] theorem lm_lRp_ne_lmC : lRp ≠ lmC := by decide
@[simp] theorem lm_lmC_ne_lRn : lmC ≠ lRn := by decide
@[simp] theorem lm_lRn_ne_lmC : lRn ≠ lmC := by decide
@[simp] theorem lm_lmC_ne_lFle : lmC ≠ lFle := by decide
@[simp] theorem lm_lFle_ne_lmC : lFle ≠ lmC := by decide
@[simp] theorem lm_lmC_ne_lDir : lmC ≠ lDir := by decide
@[simp] theorem lm_lDir_ne_lmC : lDir ≠ lmC := by decide
@[simp] theorem lm_lmC_ne_lKb : lmC ≠ lKb := by decide
@[simp] theorem lm_lKb_ne_lmC : lKb ≠ lmC := by decide
@[simp] theorem lm_lmC_ne_kFu : lmC ≠ kFu := by decide
@[simp] theorem lm_kFu_ne_lmC : kFu ≠ lmC := by decide
@[simp] theorem lm_lmC_ne_kD : lmC ≠ kD := by decide
@[simp] theorem lm_kD_ne_lmC : kD ≠ lmC := by decide
@[simp] theorem lm_lmC_ne_kE : lmC ≠ kE := by decide
@[simp] theorem lm_kE_ne_lmC : kE ≠ lmC := by decide
@[simp] theorem lm_lmR_ne_lmW : lmR ≠ lmW := by decide
@[simp] theorem lm_lmR_ne_lmL : lmR ≠ lmL := by decide
@[simp] theorem lm_lmR_ne_lmC : lmR ≠ lmC := by decide
@[simp] theorem lm_lmR_ne_lFl : lmR ≠ lFl := by decide
@[simp] theorem lm_lFl_ne_lmR : lFl ≠ lmR := by decide
@[simp] theorem lm_lmR_ne_lDh : lmR ≠ lDh := by decide
@[simp] theorem lm_lDh_ne_lmR : lDh ≠ lmR := by decide
@[simp] theorem lm_lmR_ne_lDt : lmR ≠ lDt := by decide
@[simp] theorem lm_lDt_ne_lmR : lDt ≠ lmR := by decide
@[simp] theorem lm_lmR_ne_lDg : lmR ≠ lDg := by decide
@[simp] theorem lm_lDg_ne_lmR : lDg ≠ lmR := by decide
@[simp] theorem lm_lmR_ne_lDi : lmR ≠ lDi := by decide
@[simp] theorem lm_lDi_ne_lmR : lDi ≠ lmR := by decide
@[simp] theorem lm_lmR_ne_lRp : lmR ≠ lRp := by decide
@[simp] theorem lm_lRp_ne_lmR : lRp ≠ lmR := by decide
@[simp] theorem lm_lmR_ne_lRn : lmR ≠ lRn := by decide
@[simp] theorem lm_lRn_ne_lmR : lRn ≠ lmR := by decide
@[simp] theorem lm_lmR_ne_lFle : lmR ≠ lFle := by decide
@[simp] theorem lm_lFle_ne_lmR : lFle ≠ lmR := by decide
@[simp] theorem lm_lmR_ne_lDir : lmR ≠ lDir := by decide
@[simp] theorem lm_lDir_ne_lmR : lDir ≠ lmR := by decide
@[simp] theorem lm_lmR_ne_lKb : lmR ≠ lKb := by decide
@[simp] theorem lm_lKb_ne_lmR : lKb ≠ lmR := by decide
@[simp] theorem lm_lmR_ne_kFu : lmR ≠ kFu := by decide
@[simp] theorem lm_kFu_ne_lmR : kFu ≠ lmR := by decide
@[simp] theorem lm_lmR_ne_kD : lmR ≠ kD := by decide
@[simp] theorem lm_kD_ne_lmR : kD ≠ lmR := by decide
@[simp] theorem lm_lmR_ne_kE : lmR ≠ kE := by decide
@[simp] theorem lm_kE_ne_lmR : kE ≠ lmR := by decide


def lmLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, lmW, lmL, lmC, lmR]

def lmCore : ProgHOL 64 :=
  .ite (tagIsE kE 8)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv kE)) (.seq eViewP
    (.seq (.assign .local lmW (.load .one (vv lRp)))
    (.ite (.cmp .equal (vv lmW) (.const 1))
      (.seq (.assign .local lmL (.var .global gLit))
      (.ite (.op .and [vv lmL, .const 2])
        (.seq (.call (some (some (.local, lmC), none)) fTc [vv kE])
        (.seq (.call (some (some (.local, lmR), none)) fW [vv kFu, vv kD, vv lmC]) (.return (vv lmR))))
        (.return (vv kE))))
      (.seq (.assign .local lmL (.var .global gLit))
      (.ite (.op .and [vv lmL, .const 1])
        (.seq (.call (some (some (.local, lmR), none)) fNl [vv kE]) (.return (vv lmR)))
        (.return (vv kE)))))))))
    (.return (vv kE))

def lmBody : ProgHOL 64 := prologue lmLocals lmCore

section
variable {σ : Type}

theorem lm_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ lmLocals → (ctxEnv C ++ kParams.zip vals).get x = none :=
  Knot.params_none C lmLocals kParams vals (by decide) (by decide)

theorem lm_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (hc : TcCodes C) (hcn : NlCodes C)
    (hcl : C.code.lookup fNl = some ([(nlH, ShapeHOL.one)], nlBody C, .one))
    (hct : C.code.lookup fTc = some ([(tcH, ShapeHOL.one)], tcBody C, .one))
    (hcw : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one))
    (s : AState) (d : Nat) (h : EIdx)
    (hW : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ e', Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d e')
      (PostK (ctxH C H))) :
    SpecR (σ := σ) (Pre C s (kParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW h])) lmBody s
      (litMajorToCtor (knot mode C n) C.fe d h) (PostK C) := by
  refine specR_prologue (Knot.postK_locals C) (lm_none C _) ?_
  unfold lmCore litMajorToCtor
  have hret : ∀ {Γ : Env} {M : Mem}, Γ.get kE = some (Enc.idxW h) →
      SpecR (σ := σ) (Inv C s Γ M (ctxLocals ++ lmLocals)) (.return (vv kE)) s (pure h) (PostK C) :=
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
      refine specR_loadI' lmW (vv lRp) P (P + BitVec.ofNat 64 0) 0 (by decide) (by simp) (by simp)
        (by simpa [encEView, Enc.encLit] using wordsAt_mem0 P 0 (limbs m) []) ?_
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
        (fun _ => ?_)
      dsimp only
      unfold litToCtorIfNat
      rw [if_pos (show (h.tag == ETag.lit) = true by simp [htg, ETag.lit])]
      refine specR_runBind (show ConRon.Arena.view h s = .ok (.lit (.natVal m), s) by rw [view_run, hv]) ?_
      dsimp only
      refine specR_gLitI lmL (by decide) ?_
      by_cases hnl : C.fe.natLit = true
      · refine specR_ifI _ 1 (by simp [sev, litW_and1, hnl, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
        rw [if_pos hnl]
        refine specR_dropM ?_
        refine specR_congr (m' := natLitToConstructor m >>= fun r => pure r) (by simp) ?_
        refine specR_callKH lmR fNl [nlH] [vv kE] (nlBody C) [Enc.idxW h] (by decide) rfl (by decide) hcl
          ⟨by simp +decide [Env.get, kParams, ctxEnv], trivial⟩ (nl_spec ra C hok hcn s h m hv)
          (fun r s1 H1 hp1 => ?_)
        exact specR_returnI _ (Enc.idxW r) (by simp)
          (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      · have hf : C.fe.natLit = false := by simpa using hnl
        refine specR_ifI _ 0 (by simp [sev, litW_and1, hf, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
        rw [if_neg hnl]
        exact hret (by simp +decide [Env.get, kParams, ctxEnv])
    | strVal str =>
      refine specR_loadI' lmW (vv lRp) P (P + BitVec.ofNat 64 0) 1 (by decide) (by simp) (by simp)
        (by simpa [encEView, Enc.encLit] using wordsAt_mem0 P 1 (strW str) []) ?_
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
        (fun h => absurd h (by decide))
      refine specR_gLitI lmL (by decide) ?_
      dsimp only
      by_cases hsl : C.fe.strLit = true
      · refine specR_ifI _ 2 (by simp [sev, litW_and2, hsl, boolW]) (fun _ => ?_)
          (fun h => absurd h (by decide))
        rw [if_pos hsl]
        refine specR_dropM ?_
        refine specR_callKH lmC fTc [tcH] [vv kE] (tcBody C) [Enc.idxW h] (by decide) rfl (by decide) hct
          ⟨by simp +decide [Env.get, kParams, ctxEnv], trivial⟩ (tc_spec ra C hok hc s h str hv)
          (fun c s1 H1 hp1 => ?_)
        refine specR_congr (m' := (knot mode C n).whnf d c >>= fun r => pure r) (by simp) ?_
        refine Big.specR_callKC (C := ctxH C H1) lmR fW kParams [vv kFu, vv kD, vv lmC] (whnfE C fWB)
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
    unfold litToCtorIfNat
    rw [if_neg (show ¬ (h.tag == ETag.lit) = true by simpa [ETag.lit] using htg)]
    exact hret (by simp +decide [Env.get, kParams, ctxEnv])

end

end ConPanqueque.T.WC
