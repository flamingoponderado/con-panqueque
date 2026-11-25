import ConPanqueque.T.Ind.ListLvlEq
import ConPanqueque.Start.PinName
import ConPanqueque.T.Env

/-!
# Consumed type annotations (`annWitness`, `annIdent`, `annEq`)

`annWitness fe D`: `D` is a constant type `n` at no levels and the stored constant `n.missing` has type `D` at
no levels. The intern of `n.missing` is the frontend's `internNStr` on a fresh key block (`strStepP`).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI
open ConPanqueque.Start (vPn vKa strStepP strStep_spec strBytes)
open ConPanqueque.Front (FrontOK frontOK_H)

def awD := ofString "aw_d"
def awN := ofString "aw_n"
def awU := ofString "aw_u"
def awX := ofString "aw_x"
def awT := ofString "aw_t"
def awL := ofString "aw_l"
def awC := ofString "aw_c"
def fAnnWitness := ofString "annWitness"

def awParams : List MlS := [awD]
def awLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, awN, awU, vPn, vKa, awX, awT, awL, awC]

def awBody (C : Ctx) : ProgHOL 64 := prologue awLocals
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv awD)) (.seq eViewP
  (.ite (veEqC lDg 3)
    (.seq (.assign .local awN (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local awU (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.assign .local lDh (vv awU)) (.seq (.assign .local lFl (vv lFls)) (.seq lsViewP
    (.ite (veEqC lRn 0)
      (.seq (.assign .local vPn (vv awN)) (strStepP C "missing"
      (envFindP C awX (vv vPn)
      (.ite (veEqC awX 0) (.return (.const 0))
      (.seq (.assign .local awT (.load .one (.op .add [vv awX, .const 23])))
      (.ite (.cmp .equal (vv awT) (vv awD))
        (.seq (.assign .local awL (.load .one (.op .add [vv awX, .const 15])))
        (.seq (.assign .local awC (.load .one (vv awL))) (.return (veEqC awC 0))))
        (.return (.const 0))))))))
      (.return (.const 0))))))))
    (.return (.const 0))))))


section
variable {σ : Type}

theorem aw_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ awLocals → (ctxEnv C ++ awParams.zip vals).get x = none :=
  Knot.params_none C awLocals awParams vals (by decide) (by decide)

/-- **`annWitness`** against the context's environment. -/
theorem aw_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : FrontOK C)
    (hcN : C.code.lookup Front.fInternNStr = some ([(Front.pKeyN, .one), (lEn, .one), (lEp, .one), (lHn, .one)], Front.nameStrBody, .one))
    (hcG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (H : List (BitVec 64)) (D : EIdx) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (awParams.zip [Enc.idxW D])) (awBody (ctxH C H)) s (annWitness C.fe D)
      (PostB (ctxH C H)) := by
  refine specR_prologue (postB_locals _) (aw_none _ _) ?_
  unfold annWitness
  let Γ0 : Env := ctxEnv (ctxH C H) ++ awParams.zip [Enc.idxW D]
  have gD : Γ0.get awD = some (Enc.idxW D) := by simp +decide [Γ0, Env.get, awParams, ctxEnv]
  have ret0 : ∀ (s1 : AState) (Γ : Env) (M : Mem), SpecR (σ := σ) (Inv (ctxH C H) s1 Γ M (ctxLocals ++ awLocals))
      (.return (.const 0)) s1 (pure false) (PostB (ctxH C H)) := fun s1 Γ M =>
    specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get_cons, Env.get, awParams, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv awD) (Enc.idxW D) (by decide)
    (by simp only [sev, sev_vv, Env.get_cons]; simp +decide; exact gD) ?_
  refine ConPanqueque.T.Big.specR_viewP D (by simp) (by simp +decide [Env.get_cons] <;> rfl)
    (by simp +decide [Env.get_cons, Env.get, awParams, ctxEnv] <;> rfl) (by decide) (fun v P hv htn hlen => ?_)
  have hat : D.tag = UInt32.ofNat v.tagN := tag_of_tagN htn
  have gDg : sev ((lRp, P) :: (lRn, BitVec.ofNat 64 (encEView v).length) :: (lDt, BitVec.ofNat 64 D.tier.toNat) ::
      (lDg, BitVec.ofNat 64 v.tagN) :: (lDi, BitVec.ofNat 64 D.idxNat) :: (lDh, Enc.idxW D) :: (lFl, C.FLe) :: Γ0)
      (veEqC lDg 3) = some (boolW (v.tagN == 3)) := by
    unfold veEqC
    rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 v.tagN) (BitVec.ofNat 64 3) (by simp [sev, Env.get_cons]) rfl,
      wcE' _ _ (by have := ConPanqueque.T.Big.tagN_lt v; omega) (by omega)]
    by_cases h : v.tagN = 3 <;> simp [h, boolW]
  by_cases h3 : v.tagN = 3
  swap
  · refine specR_ifI _ _ gDg (fun hw => absurd hw (by simp [boolW, h3])) (fun _ => ?_)
    have : (D.tag == ETag.const) = false := by
      rw [hat]
      have hl := ConPanqueque.T.Big.tagN_lt v
      have : UInt32.ofNat v.tagN ≠ ETag.const := by
        intro e; have := congrArg UInt32.toNat e; simp [ETag.const] at this; omega
      simpa using this
    simp only [this, Bool.false_eq_true, ite_false]
    exact ret0 _ _ _
  refine specR_ifI _ _ gDg (fun _ => ?_) (fun hw => absurd hw (by simp [boolW, h3]))
  rcases v with _ | _ | _ | ⟨n, us⟩ | _ | _ | _ | _ | _ | _ <;> simp [ENodeView.tagN] at h3
  have hta : D.tag = ETag.const := by rw [hat]; rfl
  simp only [hta, beq_self_eq_true, ite_true]
  refine specR_runBind (show viewConst D s = .ok (some (n, us), s) by
    rw [WC.viewConst_run, WC.viewConst_of_view hta hv]) ?_
  refine specR_loadI' awN _ (P + 0) (P + BitVec.ofNat 64 0) (Enc.idxW n) (by decide) (by simp +decide [sev, Env.get_cons])
    rfl (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW n) [Enc.idxW us] []) ?_
  refine specR_loadI' awU _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW us) (by decide) (by simp +decide [sev, Env.get_cons])
    rfl (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW n) (Enc.idxW us) [] []) ?_
  refine specR_assignI lDh (vv awU) (Enc.idxW us) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
  refine specR_assignI lFl (vv lFls) (ctxH C H).FLs (by decide)
    (by simp +decide [Env.get_cons, Env.get, awParams, ctxEnv] <;> rfl) ?_
  refine specR_lsviewPI (C := ctxH C H) us (by simp) (by simp +decide [Env.get_cons] <;> rfl)
    (by simp +decide [Env.get_cons, Env.get, awParams, ctxEnv] <;> rfl) (by decide) (fun vl Pl hvl htl hlenl => ?_)
  refine specR_runBind (WC.viewLsLen_run us s vl hvl) ?_
  rcases vl with _ | ⟨l0, vl⟩
  swap
  · refine specR_ifI _ 0 (by
        simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        intro e; have := congrArg BitVec.toNat e; simp at this; simp at hlenl; omega)
      (fun h => absurd rfl h) (fun _ => ?_)
    exact ret0 _ _ _
  refine specR_ifI _ 1 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun _ => ?_) (fun h => absurd h (by decide))
  simp only [List.length_nil]
  refine specR_assignI vPn (vv awN) (Enc.idxW n) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
  refine strStep_spec ra (ctxH C H) (ctxOK_H hok H) (frontOK_H hf H) hcN s _ _ _ (by decide) (by decide) n
    (by simp [Env.get_cons]) "missing" (by decide) (fun m s' om hrun => ?_)
  refine specR_envFindI (C := ctxH C H) (ctxOK_H hok H) hcG hcP awX (vv vPn) m (by decide)
    (by simp [sev, Env.get_cons]) (by simp +decide [Env.get_cons, Env.get, awParams, ctxEnv] <;> rfl) ?_
  have hfr := find_rel (ctxOK_H hok H) m
  have efe : (ctxH C H).fe = C.fe := rfl
  rw [efe] at hfr
  cases hfm : C.fe.find? m with
  | none =>
    rw [hfm] at hfr
    simp only [hfr, optWG]
    refine specR_ifI _ 1 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact ret0 _ _ _
  | some ci =>
    rw [hfm] at hfr
    obtain ⟨o, he, hcie⟩ := hfr
    simp only [he, optWG, id]
    refine specR_fact (fun t ht => ht.sr.env.1.len) (fun hEN => ?_)
    have ho : o < C.EN := by have := cie_lt hcie; exact Nat.lt_of_lt_of_le this hEN
    have hne : ecell (ctxH C H) o + 1 ≠ 0 := ecell_succ_ne (ctxOK_H hok H) ho
    refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_envLoadI (C := ctxH C H) awT _ (o + 3) (Enc.idxW ci.toConstantVal.type) (by decide)
      (by
        simp +decide [sev, Env.get_cons]
        simp only [ecell]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega)
      (by have := hcie.1.2.2; rw [show o + 1 + 2 = o + 3 by omega] at this; exact this) ?_
    by_cases ht : ci.toConstantVal.type = D
    · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, awParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, ht])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [ht, beq_self_eq_true, ite_true]
      obtain ⟨w, hw2, o', hwo, heb⟩ := hcie.1.2.1
      refine specR_envLoadI (C := ctxH C H) awL _ (o + 2) w (by decide)
        (by
          simp +decide [sev, Env.get_cons]
          simp only [ecell]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega)
        (by rw [show o + 2 = o + 1 + 1 by omega]; exact hw2) ?_
      refine specR_envLoadI (C := ctxH C H) awC _ o' (BitVec.ofNat 64 ci.toConstantVal.levelParams.length) (by decide)
        (by simp [sev, Env.get_cons, hwo]; rfl) (by rw [heb.1]; simp) ?_
      refine specR_returnI _ (boolW (ci.toConstantVal.levelParams.length == 0)) (by
          simp only [veEqC]
          rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 ci.toConstantVal.levelParams.length) (BitVec.ofNat 64 0)
            (by simp [sev, Env.get_cons]) rfl]
          have hl : o' + 1 + ci.toConstantVal.levelParams.length ≤ C.EH.length := by
            have := blkAt_len heb; simp only [List.length_map] at this; exact this
          have : C.EH.length ≤ C.EN := hEN
          have hlay2 := hok.envLay
          rw [wcE' _ _ (by omega) (by omega)]
          by_cases h0 : ci.toConstantVal.levelParams.length = 0 <;> simp [h0, boolW])
        (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · have hne2 : Enc.idxW ci.toConstantVal.type ≠ Enc.idxW D := fun e => ht (Enc.idxW_inj e)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, awParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne2])
        (fun h => absurd rfl h) (fun _ => ?_)
      have : (ci.toConstantVal.type == D) = false := by simpa using ht
      simp only [this, Bool.false_eq_true, ite_false]
      exact ret0 _ _ _

end

end ConPanqueque.T.Ind
