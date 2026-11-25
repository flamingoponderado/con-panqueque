import ConPanqueque.T.Core.LitMajor
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `ctorView`: is a term a stored constructor's application

The head (`getAppFn`); a `const` head's name looked up; a `ctorInfo` record makes it a constructor application.
The answer is `encMV` (the term and the constructor bit); the state is unchanged.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

def cwE := ofString "cwe"
def cwH := ofString "cwh"
def cwJ := ofString "cwj"
def cwW := ofString "cww"
def cwQ := ofString "cwq"
def cwT := ofString "cwt"
def fCw := ofString "ctorView"

@[simp] theorem cw_cwE_ne_cwH : cwE ≠ cwH := by decide
@[simp] theorem cw_cwE_ne_cwJ : cwE ≠ cwJ := by decide
@[simp] theorem cw_cwE_ne_cwW : cwE ≠ cwW := by decide
@[simp] theorem cw_cwE_ne_cwQ : cwE ≠ cwQ := by decide
@[simp] theorem cw_cwE_ne_cwT : cwE ≠ cwT := by decide
@[simp] theorem cw_cwE_ne_lFl : cwE ≠ lFl := by decide
@[simp] theorem cw_lFl_ne_cwE : lFl ≠ cwE := by decide
@[simp] theorem cw_cwE_ne_lDh : cwE ≠ lDh := by decide
@[simp] theorem cw_lDh_ne_cwE : lDh ≠ cwE := by decide
@[simp] theorem cw_cwE_ne_lDt : cwE ≠ lDt := by decide
@[simp] theorem cw_lDt_ne_cwE : lDt ≠ cwE := by decide
@[simp] theorem cw_cwE_ne_lDg : cwE ≠ lDg := by decide
@[simp] theorem cw_lDg_ne_cwE : lDg ≠ cwE := by decide
@[simp] theorem cw_cwE_ne_lDi : cwE ≠ lDi := by decide
@[simp] theorem cw_lDi_ne_cwE : lDi ≠ cwE := by decide
@[simp] theorem cw_cwE_ne_lRp : cwE ≠ lRp := by decide
@[simp] theorem cw_lRp_ne_cwE : lRp ≠ cwE := by decide
@[simp] theorem cw_cwE_ne_lRn : cwE ≠ lRn := by decide
@[simp] theorem cw_lRn_ne_cwE : lRn ≠ cwE := by decide
@[simp] theorem cw_cwE_ne_lFle : cwE ≠ lFle := by decide
@[simp] theorem cw_lFle_ne_cwE : lFle ≠ cwE := by decide
@[simp] theorem cw_cwE_ne_lDir : cwE ≠ lDir := by decide
@[simp] theorem cw_lDir_ne_cwE : lDir ≠ cwE := by decide
@[simp] theorem cw_cwE_ne_lKb : cwE ≠ lKb := by decide
@[simp] theorem cw_lKb_ne_cwE : lKb ≠ cwE := by decide
@[simp] theorem cw_cwH_ne_cwE : cwH ≠ cwE := by decide
@[simp] theorem cw_cwH_ne_cwJ : cwH ≠ cwJ := by decide
@[simp] theorem cw_cwH_ne_cwW : cwH ≠ cwW := by decide
@[simp] theorem cw_cwH_ne_cwQ : cwH ≠ cwQ := by decide
@[simp] theorem cw_cwH_ne_cwT : cwH ≠ cwT := by decide
@[simp] theorem cw_cwH_ne_lFl : cwH ≠ lFl := by decide
@[simp] theorem cw_lFl_ne_cwH : lFl ≠ cwH := by decide
@[simp] theorem cw_cwH_ne_lDh : cwH ≠ lDh := by decide
@[simp] theorem cw_lDh_ne_cwH : lDh ≠ cwH := by decide
@[simp] theorem cw_cwH_ne_lDt : cwH ≠ lDt := by decide
@[simp] theorem cw_lDt_ne_cwH : lDt ≠ cwH := by decide
@[simp] theorem cw_cwH_ne_lDg : cwH ≠ lDg := by decide
@[simp] theorem cw_lDg_ne_cwH : lDg ≠ cwH := by decide
@[simp] theorem cw_cwH_ne_lDi : cwH ≠ lDi := by decide
@[simp] theorem cw_lDi_ne_cwH : lDi ≠ cwH := by decide
@[simp] theorem cw_cwH_ne_lRp : cwH ≠ lRp := by decide
@[simp] theorem cw_lRp_ne_cwH : lRp ≠ cwH := by decide
@[simp] theorem cw_cwH_ne_lRn : cwH ≠ lRn := by decide
@[simp] theorem cw_lRn_ne_cwH : lRn ≠ cwH := by decide
@[simp] theorem cw_cwH_ne_lFle : cwH ≠ lFle := by decide
@[simp] theorem cw_lFle_ne_cwH : lFle ≠ cwH := by decide
@[simp] theorem cw_cwH_ne_lDir : cwH ≠ lDir := by decide
@[simp] theorem cw_lDir_ne_cwH : lDir ≠ cwH := by decide
@[simp] theorem cw_cwH_ne_lKb : cwH ≠ lKb := by decide
@[simp] theorem cw_lKb_ne_cwH : lKb ≠ cwH := by decide
@[simp] theorem cw_cwJ_ne_cwE : cwJ ≠ cwE := by decide
@[simp] theorem cw_cwJ_ne_cwH : cwJ ≠ cwH := by decide
@[simp] theorem cw_cwJ_ne_cwW : cwJ ≠ cwW := by decide
@[simp] theorem cw_cwJ_ne_cwQ : cwJ ≠ cwQ := by decide
@[simp] theorem cw_cwJ_ne_cwT : cwJ ≠ cwT := by decide
@[simp] theorem cw_cwJ_ne_lFl : cwJ ≠ lFl := by decide
@[simp] theorem cw_lFl_ne_cwJ : lFl ≠ cwJ := by decide
@[simp] theorem cw_cwJ_ne_lDh : cwJ ≠ lDh := by decide
@[simp] theorem cw_lDh_ne_cwJ : lDh ≠ cwJ := by decide
@[simp] theorem cw_cwJ_ne_lDt : cwJ ≠ lDt := by decide
@[simp] theorem cw_lDt_ne_cwJ : lDt ≠ cwJ := by decide
@[simp] theorem cw_cwJ_ne_lDg : cwJ ≠ lDg := by decide
@[simp] theorem cw_lDg_ne_cwJ : lDg ≠ cwJ := by decide
@[simp] theorem cw_cwJ_ne_lDi : cwJ ≠ lDi := by decide
@[simp] theorem cw_lDi_ne_cwJ : lDi ≠ cwJ := by decide
@[simp] theorem cw_cwJ_ne_lRp : cwJ ≠ lRp := by decide
@[simp] theorem cw_lRp_ne_cwJ : lRp ≠ cwJ := by decide
@[simp] theorem cw_cwJ_ne_lRn : cwJ ≠ lRn := by decide
@[simp] theorem cw_lRn_ne_cwJ : lRn ≠ cwJ := by decide
@[simp] theorem cw_cwJ_ne_lFle : cwJ ≠ lFle := by decide
@[simp] theorem cw_lFle_ne_cwJ : lFle ≠ cwJ := by decide
@[simp] theorem cw_cwJ_ne_lDir : cwJ ≠ lDir := by decide
@[simp] theorem cw_lDir_ne_cwJ : lDir ≠ cwJ := by decide
@[simp] theorem cw_cwJ_ne_lKb : cwJ ≠ lKb := by decide
@[simp] theorem cw_lKb_ne_cwJ : lKb ≠ cwJ := by decide
@[simp] theorem cw_cwW_ne_cwE : cwW ≠ cwE := by decide
@[simp] theorem cw_cwW_ne_cwH : cwW ≠ cwH := by decide
@[simp] theorem cw_cwW_ne_cwJ : cwW ≠ cwJ := by decide
@[simp] theorem cw_cwW_ne_cwQ : cwW ≠ cwQ := by decide
@[simp] theorem cw_cwW_ne_cwT : cwW ≠ cwT := by decide
@[simp] theorem cw_cwW_ne_lFl : cwW ≠ lFl := by decide
@[simp] theorem cw_lFl_ne_cwW : lFl ≠ cwW := by decide
@[simp] theorem cw_cwW_ne_lDh : cwW ≠ lDh := by decide
@[simp] theorem cw_lDh_ne_cwW : lDh ≠ cwW := by decide
@[simp] theorem cw_cwW_ne_lDt : cwW ≠ lDt := by decide
@[simp] theorem cw_lDt_ne_cwW : lDt ≠ cwW := by decide
@[simp] theorem cw_cwW_ne_lDg : cwW ≠ lDg := by decide
@[simp] theorem cw_lDg_ne_cwW : lDg ≠ cwW := by decide
@[simp] theorem cw_cwW_ne_lDi : cwW ≠ lDi := by decide
@[simp] theorem cw_lDi_ne_cwW : lDi ≠ cwW := by decide
@[simp] theorem cw_cwW_ne_lRp : cwW ≠ lRp := by decide
@[simp] theorem cw_lRp_ne_cwW : lRp ≠ cwW := by decide
@[simp] theorem cw_cwW_ne_lRn : cwW ≠ lRn := by decide
@[simp] theorem cw_lRn_ne_cwW : lRn ≠ cwW := by decide
@[simp] theorem cw_cwW_ne_lFle : cwW ≠ lFle := by decide
@[simp] theorem cw_lFle_ne_cwW : lFle ≠ cwW := by decide
@[simp] theorem cw_cwW_ne_lDir : cwW ≠ lDir := by decide
@[simp] theorem cw_lDir_ne_cwW : lDir ≠ cwW := by decide
@[simp] theorem cw_cwW_ne_lKb : cwW ≠ lKb := by decide
@[simp] theorem cw_lKb_ne_cwW : lKb ≠ cwW := by decide
@[simp] theorem cw_cwQ_ne_cwE : cwQ ≠ cwE := by decide
@[simp] theorem cw_cwQ_ne_cwH : cwQ ≠ cwH := by decide
@[simp] theorem cw_cwQ_ne_cwJ : cwQ ≠ cwJ := by decide
@[simp] theorem cw_cwQ_ne_cwW : cwQ ≠ cwW := by decide
@[simp] theorem cw_cwQ_ne_cwT : cwQ ≠ cwT := by decide
@[simp] theorem cw_cwQ_ne_lFl : cwQ ≠ lFl := by decide
@[simp] theorem cw_lFl_ne_cwQ : lFl ≠ cwQ := by decide
@[simp] theorem cw_cwQ_ne_lDh : cwQ ≠ lDh := by decide
@[simp] theorem cw_lDh_ne_cwQ : lDh ≠ cwQ := by decide
@[simp] theorem cw_cwQ_ne_lDt : cwQ ≠ lDt := by decide
@[simp] theorem cw_lDt_ne_cwQ : lDt ≠ cwQ := by decide
@[simp] theorem cw_cwQ_ne_lDg : cwQ ≠ lDg := by decide
@[simp] theorem cw_lDg_ne_cwQ : lDg ≠ cwQ := by decide
@[simp] theorem cw_cwQ_ne_lDi : cwQ ≠ lDi := by decide
@[simp] theorem cw_lDi_ne_cwQ : lDi ≠ cwQ := by decide
@[simp] theorem cw_cwQ_ne_lRp : cwQ ≠ lRp := by decide
@[simp] theorem cw_lRp_ne_cwQ : lRp ≠ cwQ := by decide
@[simp] theorem cw_cwQ_ne_lRn : cwQ ≠ lRn := by decide
@[simp] theorem cw_lRn_ne_cwQ : lRn ≠ cwQ := by decide
@[simp] theorem cw_cwQ_ne_lFle : cwQ ≠ lFle := by decide
@[simp] theorem cw_lFle_ne_cwQ : lFle ≠ cwQ := by decide
@[simp] theorem cw_cwQ_ne_lDir : cwQ ≠ lDir := by decide
@[simp] theorem cw_lDir_ne_cwQ : lDir ≠ cwQ := by decide
@[simp] theorem cw_cwQ_ne_lKb : cwQ ≠ lKb := by decide
@[simp] theorem cw_lKb_ne_cwQ : lKb ≠ cwQ := by decide
@[simp] theorem cw_cwT_ne_cwE : cwT ≠ cwE := by decide
@[simp] theorem cw_cwT_ne_cwH : cwT ≠ cwH := by decide
@[simp] theorem cw_cwT_ne_cwJ : cwT ≠ cwJ := by decide
@[simp] theorem cw_cwT_ne_cwW : cwT ≠ cwW := by decide
@[simp] theorem cw_cwT_ne_cwQ : cwT ≠ cwQ := by decide
@[simp] theorem cw_cwT_ne_lFl : cwT ≠ lFl := by decide
@[simp] theorem cw_lFl_ne_cwT : lFl ≠ cwT := by decide
@[simp] theorem cw_cwT_ne_lDh : cwT ≠ lDh := by decide
@[simp] theorem cw_lDh_ne_cwT : lDh ≠ cwT := by decide
@[simp] theorem cw_cwT_ne_lDt : cwT ≠ lDt := by decide
@[simp] theorem cw_lDt_ne_cwT : lDt ≠ cwT := by decide
@[simp] theorem cw_cwT_ne_lDg : cwT ≠ lDg := by decide
@[simp] theorem cw_lDg_ne_cwT : lDg ≠ cwT := by decide
@[simp] theorem cw_cwT_ne_lDi : cwT ≠ lDi := by decide
@[simp] theorem cw_lDi_ne_cwT : lDi ≠ cwT := by decide
@[simp] theorem cw_cwT_ne_lRp : cwT ≠ lRp := by decide
@[simp] theorem cw_lRp_ne_cwT : lRp ≠ cwT := by decide
@[simp] theorem cw_cwT_ne_lRn : cwT ≠ lRn := by decide
@[simp] theorem cw_lRn_ne_cwT : lRn ≠ cwT := by decide
@[simp] theorem cw_cwT_ne_lFle : cwT ≠ lFle := by decide
@[simp] theorem cw_lFle_ne_cwT : lFle ≠ cwT := by decide
@[simp] theorem cw_cwT_ne_lDir : cwT ≠ lDir := by decide
@[simp] theorem cw_lDir_ne_cwT : lDir ≠ cwT := by decide
@[simp] theorem cw_cwT_ne_lKb : cwT ≠ lKb := by decide
@[simp] theorem cw_lKb_ne_cwT : lKb ≠ cwT := by decide

def cwLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, cwH, cwJ, cwW, cwQ, cwT]

def cwStuck : ProgHOL 64 := .return (.shift .lsl (vv cwE) (.const 1))

def cwCore (C : Ctx) : ProgHOL 64 :=
  .seq (.call (some (some (.local, cwH), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv cwE])
  (.ite (tagIsE cwH 3)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv cwH)) (.seq eViewP
    (.seq (.assign .local cwJ (.load .one (vv lRp)))
    (envFindP C cwW (vv cwJ)
    (.ite (.cmp .equal (vv cwW) (.const 0)) cwStuck
    (.seq (.assign .local cwQ (.op .sub [vv cwW, .const 1]))
    (.seq (.assign .local cwT (.load .one (vv cwQ)))
    (.ite (.cmp .equal (vv cwT) (.const 4)) (.return (.op .add [.shift .lsl (vv cwE) (.const 1), .const 1]))
      cwStuck)))))))))
    cwStuck)

def cwBody (C : Ctx) : ProgHOL 64 := prologue cwLocals (cwCore C)

section
variable {σ : Type}

theorem cw_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cwLocals → (ctxEnv C ++ [cwE].zip vals).get x = none :=
  Knot.params_none C cwLocals [cwE] vals (by decide) (by decide)

theorem encMV_stuck (e : EIdx) : encMV (.stuck e) = Enc.idxW e <<< (1 : Nat) := by
  simp [encMV, MajorView.expr, MajorView.isCtor]

theorem encMV_ctor (e : EIdx) (cj : NIdx) (usj : LsIdx) (cvj : IConstantVal) (nP nF : Nat) (ind : NIdx) :
    encMV (.ctor e cj usj cvj nP nF ind) = Enc.idxW e <<< (1 : Nat) + 1 := by
  simp [encMV, MajorView.expr, MajorView.isCtor]

theorem cw_spec (C : Ctx) (hok : CtxOK C)
    (hcaf : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one))
    (hcodeG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcodeP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (s : AState) (e : EIdx) :
    SpecR (σ := σ) (Pre C s [(cwE, Enc.idxW e)]) (cwBody C) s (ctorView C.fe e) (PostMV C) := by
  refine specR_prologue (fun a w s' st L ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, sr_of_eq hsr rfl rfl rfl rfl⟩)
    (cw_none C [Enc.idxW e]) ?_
  unfold cwCore ctorView
  have hstuck : ∀ {Γ : Env} {M : Mem}, Γ.get cwE = some (Enc.idxW e) →
      SpecR (σ := σ) (Inv C s Γ M (ctxLocals ++ cwLocals)) cwStuck s (pure (.stuck e) : AM MajorView) (PostMV C) :=
    fun hE => specR_returnI _ (encMV (.stuck e)) (by simp [sev, hE, encMV_stuck])
      (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_callNIM cwH fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv cwE]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e] (by decide) rfl (by decide) hcaf
    ⟨rfl, by simp +decide [Env.get, ctxEnv], trivial⟩
    (fun a w s' st => getAppFn coreWalkFuel e s = .ok (a, s') ∧ Post C s a w s' st)
    (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec C hcaf coreWalkFuel e s CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun hh w s' st ⟨hrun2, hw, hs, _⟩ => ?_)
  subst hw
  have hs' : s = s' := hs.symm
  subst hs'
  refine Knot.specR_tagIteV cwH hh 3 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
  swap
  · rw [ite_eq_right (show ¬ (hh.tag == ETag.const) = true by simpa [ETag.const] using htg)]
    exact hstuck (by simp +decide [Env.get, ctxEnv])
  rw [ite_eq_left (show (hh.tag == ETag.const) = true by simp [htg, ETag.const])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
  refine specR_assignI lDh (vv cwH) (Enc.idxW hh) (by decide) (by simp) ?_
  refine specR_viewP hh (by simp) (by simp +decide [Env.get]) (by simp +decide [Env.get, ctxEnv]) (by decide)
    (fun v P hv htn _ => ?_)
  have h3 : v.tagN = 3 := by rw [htn, htg]; rfl
  obtain ⟨cj, us, rfl⟩ := UD.tagN_const h3
  have hvc : s.store.viewConst hh = some (cj, us) := viewConst_of_view (by rw [htg]; rfl) hv
  refine specR_runBind (by rw [viewConst_run, hvc]) ?_
  dsimp only
  refine specR_loadI' cwJ (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW cj) (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW cj) [Enc.idxW us] []) ?_
  refine specR_dropM ?_
  refine specR_envFindI hok hcodeG hcodeP cwW (vv cwJ) cj (by decide) (by simp) (by simp +decide [Env.get, ctxEnv]) ?_
  have hrel := find_rel hok cj
  revert hrel
  rcases hfind : C.fe.find? cj with _ | ci
  · intro hrel; simp only at hrel
    rw [hrel]
    refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact hstuck (by simp +decide [Env.get, ctxEnv])
  intro ⟨o, hm, hci⟩
  rw [hm]
  refine specR_atEntry fun t ht => ?_
  have hoE : o < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI cwQ _ (ecell C o) (by decide) (by simp [sev, optWG]; exact ecell_succ_sub C o) ?_
  refine specR_envLoadI cwT (vv cwQ) o _ (by decide) (by simp) (UD.cie_tag hci) ?_
  cases ci
  case ctorInfo cvj nP nF ind =>
    dsimp only
    refine specR_ifI _ 1 (by simp +decide [sev, UD.ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ (encMV (.ctor e cj us cvj nP nF ind))
      (by simp +decide [sev, Env.get, ctxEnv, encMV_ctor])
      (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  all_goals
    dsimp only
    refine specR_ifI _ 0 (by simp +decide [sev, UD.ciTag, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact hstuck (by simp +decide [Env.get, ctxEnv])

end

end ConPanqueque.T.WC
