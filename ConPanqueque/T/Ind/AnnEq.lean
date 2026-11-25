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


def aiP := ofString "ai_p"
def aiP2 := ofString "ai_p2"
def aiAr := ofString "ai_ar"
def aiB := ofString "ai_b"
def aiJ := ofString "ai_j"
def aiD := ofString "ai_d"
def aiC := ofString "ai_c"
def aiZ := ofString "ai_z"
def aiR := ofString "ai_r"
def fAnnIdentBody := ofString "annIdentBody"

def aiParams : List MlS := [aiP, aiP2, aiAr, aiB]
def aiLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, aiJ, aiD, aiC, aiZ, aiR]

/-- A `bvar` view's index word into `x`: `0` at no limbs, the limb at one, else hang. -/
def bvIdxP (x : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  .ite (veEqC lRn 0) (.seq (.assign .local x (.const 0)) rest)
    (.ite (veEqC lRn 1) (.seq (.assign .local x (.load .one (.op .add [vv lRp, .const 0]))) rest) hang)

def viewOf (h : MlS) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv h)) (.seq eViewP rest))

def aiBody : ProgHOL 64 := prologue aiLocals
  (.ite (veEqC aiAr 1)
    (viewOf aiB
      (.ite (veEqC lDg 0)
        (bvIdxP aiJ (.ite (veEqC aiJ 0) (.return (.cmp .equal (vv aiP) (vv aiP2))) (.return (.const 0))))
        (.return (.const 0))))
    (.ite (veEqC aiAr 2)
      (viewOf aiB
        (.ite (veEqC lDg 5)
          (.seq (.assign .local aiD (.load .one (.op .add [vv lRp, .const 0])))
          (.seq (.assign .local aiC (.load .one (.op .add [vv lRp, .const 8])))
          (viewOf aiC
            (.ite (veEqC lDg 0)
              (bvIdxP aiJ (.ite (veEqC aiJ 1)
                (.ite (.cmp .equal (vv aiP) (vv aiP2))
                  (.seq (.call (some (some (.local, aiZ), none)) fInternBVar [.const 0])
                  (.ite (.cmp .equal (vv aiD) (vv aiZ)) (.return (.const 1))
                    (.seq (.call (some (some (.local, aiR), none)) fAnnWitness [vv aiD]) (.return (vv aiR)))))
                  (.return (.const 0)))
                (.return (.const 0))))
              (.return (.const 0))))))
          (.return (.const 0))))
      (.return (.const 0))))

def avL := ofString "av_l"
def avAr := ofString "av_ar"
def avV := ofString "av_v"
def avN := ofString "av_n"
def avT := ofString "av_t"
def avB := ofString "av_b"
def avU := ofString "av_u"
def avP := ofString "av_p"
def avP2 := ofString "av_p2"
def avR := ofString "av_r"
def fAnnIdentVal := ofString "annIdentVal"

def avParams : List MlS := [avL, avAr, avV]
def avLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, avN, avT, avB, avU, avP, avP2, avR]

/-- `avL` points at the level parameters' block in the environment heap. -/
def avBody : ProgHOL 64 := prologue avLocals
  (.seq (.assign .local avN (.load .one (vv avL)))
  (.ite (veEqC avN 1)
    (viewOf avV
      (.ite (veEqC lDg 5)
        (.seq (.assign .local avT (.load .one (.op .add [vv lRp, .const 0])))
        (.seq (.assign .local avB (.load .one (.op .add [vv lRp, .const 8])))
        (viewOf avT
          (.ite (veEqC lDg 2)
            (.seq (.assign .local avU (.load .one (.op .add [vv lRp, .const 0])))
            (.seq (.assign .local lFl (vv lFll)) (.seq (.assign .local lDh (vv avU)) (.seq lViewP
            (.ite (veEqC lDg 4)
              (.seq (.assign .local avP2 (.load .one (.op .add [vv lRp, .const 0])))
              (.seq (.assign .local avP (.load .one (.op .add [vv avL, .const 8])))
              (.seq (.call (some (some (.local, avR), none)) fAnnIdentBody [vv avP, vv avP2, vv avAr, vv avB])
                (.return (vv avR)))))
              (.return (.const 0)))))))
            (.return (.const 0))))))
        (.return (.const 0))))
    (.return (.const 0))))

def anN := ofString "an_n"
def anAr := ofString "an_ar"
def anX := ofString "an_x"
def anT := ofString "an_t"
def anL := ofString "an_l"
def anV := ofString "an_v"
def anR := ofString "an_r"
def fAnnIdent := ofString "annIdent"

def anParams : List MlS := [anN, anAr]
def anLocals : List MlS := [anX, anT, anL, anV, anR]

def anBody (C : Ctx) : ProgHOL 64 := prologue anLocals
  (envFindP C anX (vv anN)
  (.ite (veEqC anX 0) (.return (.const 0))
  (.seq (.assign .local anT (.load .one (.op .sub [vv anX, .const 1])))
  (.ite (veEqC anT 1)
    (.seq (.assign .local anL (.load .one (.op .add [vv anX, .const 15])))
    (.seq (.assign .local anV (.load .one (.op .add [vv anX, .const 31])))
    (.seq (.call (some (some (.local, anR), none)) fAnnIdentVal [vv anL, vv anAr, vv anV]) (.return (vv anR)))))
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


/-- A `bvar` view's index. -/
theorem bvIdx_spec {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM β} {R : β → BitVec 64 → AState → PState σ → Prop} (x : MlS) (P : BitVec 64) (i : Nat)
    (hx : x ∈ D) (hn : Γ.get lRn = some (BitVec.ofNat 64 (encEView (.bvar i)).length))
    (hp : Γ.get lRp = some P) (hM : ∀ q, q ∈ wordsAt P (encEView (.bvar i)) → q ∈ M)
    (hlen : (encEView (.bvar i)).length < 2 ^ 61)
    (hk : i < 2 ^ 64 → SpecR (Inv C s ((x, BitVec.ofNat 64 i) :: Γ) M D) rest s m R) :
    SpecR (Inv C s Γ M D) (bvIdxP x rest) s m R := by
  unfold bvIdxP
  have hlenB : (encEView (.bvar i)).length = (Enc.limbs i).length := by simp [encEView, Enc.encBVar]
  by_cases i0 : i = 0
  · subst i0
    refine specR_ifI _ 1 (by simp +decide [veEqC, sev, hn, hlenB, Enc.limbs,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
    exact specR_assignI x (.const 0) (BitVec.ofNat 64 0) hx rfl (hk (by decide))
  · by_cases ib : i < 2 ^ 64
    · have hl : Enc.limbs i = [BitVec.ofNat 64 i] := by rw [limbs_small i ib]; simp [i0]
      refine specR_ifI _ 0 (by simp +decide [veEqC, sev, hn, hlenB, hl,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [veEqC, sev, hn, hlenB, hl,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
      refine specR_loadI' x _ (P + 0) (P + BitVec.ofNat 64 0) (BitVec.ofNat 64 i) hx
        (by simp +decide [sev, hp]) rfl
        (hM _ (by simpa [encEView, Enc.encBVar, hl] using wordsAt_mem0 P (BitVec.ofNat 64 i) [] [])) ?_
      exact hk ib
    · have hl := limbs_len_ge2 i (by omega)
      have hlt' : (Enc.limbs i).length < 2 ^ 61 := by rw [← hlenB]; exact hlen
      have hn0 : BitVec.ofNat 64 (Enc.limbs i).length ≠ 0#64 := by
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      have hn1 : BitVec.ofNat 64 (Enc.limbs i).length ≠ 1#64 := by
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      refine specR_ifI _ 0 (by simp +decide [veEqC, sev, hn, hlenB, hn0,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
      refine specR_ifI _ 0 (by simp +decide [veEqC, sev, hn, hlenB, hn1,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => specR_hangI)


theorem ai_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ aiLocals → (ctxEnv C ++ aiParams.zip vals).get x = none :=
  Knot.params_none C aiLocals aiParams vals (by decide) (by decide)

/-- **`annIdentBody`** against the context's environment. -/
theorem ai_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : FrontOK C)
    (hcN : C.code.lookup Front.fInternNStr = some ([(Front.pKeyN, .one), (lEn, .one), (lEp, .one), (lHn, .one)], Front.nameStrBody, .one))
    (hcG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (hcB : C.code.lookup fInternBVar = some ([(lIw, .one)], bvarBody, .one))
    (hcW : C.code.lookup fAnnWitness = some (awParams.map (fun p => (p, ShapeHOL.one)), awBody C, .one))
    (H : List (BitVec 64)) (p p' : NIdx) (arity : Nat) (har : arity < 2 ^ 64) (b : EIdx) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (aiParams.zip [Enc.idxW p, Enc.idxW p', BitVec.ofNat 64 arity, Enc.idxW b]))
      aiBody s (annIdentBody C.fe p p' arity b) (PostB (ctxH C H)) := by
  refine specR_prologue (postB_locals _) (ai_none _ _) ?_
  unfold annIdentBody
  let Γ0 : Env := ctxEnv (ctxH C H) ++ aiParams.zip [Enc.idxW p, Enc.idxW p', BitVec.ofNat 64 arity, Enc.idxW b]
  have gP : Γ0.get aiP = some (Enc.idxW p) := by simp +decide [Γ0, Env.get, aiParams, ctxEnv]
  have gP2 : Γ0.get aiP2 = some (Enc.idxW p') := by simp +decide [Γ0, Env.get, aiParams, ctxEnv]
  have gAr : Γ0.get aiAr = some (BitVec.ofNat 64 arity) := by simp +decide [Γ0, Env.get, aiParams, ctxEnv]
  have gB : Γ0.get aiB = some (Enc.idxW b) := by simp +decide [Γ0, Env.get, aiParams, ctxEnv]
  have ret0 : ∀ (s1 : AState) (Γ : Env) (M : Mem), SpecR (σ := σ) (Inv (ctxH C H) s1 Γ M (ctxLocals ++ aiLocals))
      (.return (.const 0)) s1 (pure false) (PostB (ctxH C H)) := fun s1 Γ M =>
    specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  have gArk : ∀ k, k < 2 ^ 64 → sev Γ0 (veEqC aiAr k) = some (boolW (arity == k)) := fun k hk => by
    unfold veEqC
    rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 arity) (BitVec.ofNat 64 k) (by simp only [sev, sev_vv]; exact gAr) rfl,
      wcE' _ _ har hk]
    by_cases h : arity = k <;> simp [h, boolW]
  by_cases h1 : arity = 1
  · subst h1
    refine specR_ifI _ _ (gArk 1 (by decide)) (fun _ => ?_) (fun hw => absurd hw (by simp [boolW]))
    simp only [beq_self_eq_true, ite_true]
    unfold viewOf
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get_cons, Env.get, aiParams, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv aiB) (Enc.idxW b) (by decide)
      (by simp only [sev, sev_vv, Env.get_cons]; simp +decide; exact gB) ?_
    refine ConPanqueque.T.Big.specR_viewP b (by simp) (by simp +decide [Env.get_cons] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, aiParams, ctxEnv] <;> rfl) (by decide) (fun v P hv htn hlen => ?_)
    have hat : b.tag = UInt32.ofNat v.tagN := tag_of_tagN htn
    by_cases h0 : v.tagN = 0
    swap
    · refine specR_ifI _ 0 (by
          simp only [veEqC]
          rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 v.tagN) (BitVec.ofNat 64 0) (by simp [sev, Env.get_cons]) rfl,
            wcE' _ _ (by have := ConPanqueque.T.Big.tagN_lt v; omega) (by omega)]
          simp [h0]) (fun h => absurd rfl h) (fun _ => ?_)
      have : (b.tag == ETag.bvar) = false := by
        rw [hat]
        have hl := ConPanqueque.T.Big.tagN_lt v
        have : UInt32.ofNat v.tagN ≠ ETag.bvar := by
          intro e; have := congrArg UInt32.toNat e; simp [ETag.bvar] at this; omega
        simpa using this
      simp only [this, Bool.false_eq_true, ite_false]
      exact ret0 _ _ _
    refine specR_ifI _ 1 (by
        simp only [veEqC]
        rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 v.tagN) (BitVec.ofNat 64 0) (by simp [sev, Env.get_cons]) rfl,
          wcE' _ _ (by have := ConPanqueque.T.Big.tagN_lt v; omega) (by omega)]
        simp [h0]) (fun _ => ?_) (fun h => absurd h (by decide))
    rcases v with ⟨i⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;> simp [ENodeView.tagN] at h0
    have hta : b.tag = 0 := by rw [hat]; rfl
    simp only [show (b.tag == ETag.bvar) = true by rw [hta]; rfl, ite_true]
    refine specR_runBind (viewBVar_run b hta s _ hv) ?_
    simp only [projBVar]
    refine bvIdx_spec aiJ P i (by decide) (by simp [Env.get_cons]) (by simp [Env.get_cons])
      (fun q hq => by simpa using hq) hlen (fun hi => ?_)
    by_cases i0 : i = 0
    · subst i0
      refine specR_ifI _ 1 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [beq_self_eq_true, ite_true]
      refine specR_returnI _ (boolW (p == p')) (by
          rw [sev_cmp2 _ _ _ _ (Enc.idxW p) (Enc.idxW p') (by simp +decide [sev, Env.get_cons]; exact gP)
            (by simp +decide [sev, Env.get_cons]; exact gP2)]
          by_cases e : p = p'
          · subst e; simp [boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
          · have : Enc.idxW p ≠ Enc.idxW p' := fun h => e (Enc.idxW_inj h)
            simp [boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e, this])
        (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · have hne : BitVec.ofNat 64 i ≠ BitVec.ofNat 64 0 := (ofNat_eq_iff hi (by decide)).not.mpr i0
      refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
        (fun h => absurd rfl h) (fun _ => ?_)
      have : (i == 0) = false := by simpa using i0
      simp only [this, Bool.false_eq_true, ite_false]
      exact ret0 _ _ _
  · refine specR_ifI _ _ (gArk 1 (by decide)) (fun hw => absurd hw (by simp [boolW, h1])) (fun _ => ?_)
    have e1 : (arity == 1) = false := by simpa using h1
    simp only [e1, Bool.false_eq_true, ite_false]
    by_cases h2 : arity = 2
    · subst h2
      refine specR_ifI _ _ (gArk 2 (by decide)) (fun _ => ?_) (fun hw => absurd hw (by simp [boolW]))
      simp only [beq_self_eq_true, ite_true]
      unfold viewOf
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get_cons, Env.get, aiParams, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv aiB) (Enc.idxW b) (by decide)
        (by simp only [sev, sev_vv, Env.get_cons]; simp +decide; exact gB) ?_
      refine ConPanqueque.T.Big.specR_viewP b (by simp) (by simp +decide [Env.get_cons] <;> rfl)
        (by simp +decide [Env.get_cons, Env.get, aiParams, ctxEnv] <;> rfl) (by decide) (fun v P hv htn hlen => ?_)
      have hat : b.tag = UInt32.ofNat v.tagN := tag_of_tagN htn
      by_cases h5 : v.tagN = 5
      swap
      · refine specR_ifI _ 0 (by
            simp only [veEqC]
            rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 v.tagN) (BitVec.ofNat 64 5) (by simp [sev, Env.get_cons]) rfl,
              wcE' _ _ (by have := ConPanqueque.T.Big.tagN_lt v; omega) (by omega)]
            simp [h5]) (fun h => absurd rfl h) (fun _ => ?_)
        have : (b.tag == ETag.lam) = false := by
          rw [hat]
          have hl := ConPanqueque.T.Big.tagN_lt v
          have : UInt32.ofNat v.tagN ≠ ETag.lam := by
            intro e; have := congrArg UInt32.toNat e; simp [ETag.lam] at this; omega
          simpa using this
        simp only [this, Bool.false_eq_true, ite_false]
        exact ret0 _ _ _
      refine specR_ifI _ 1 (by
          simp only [veEqC]
          rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 v.tagN) (BitVec.ofNat 64 5) (by simp [sev, Env.get_cons]) rfl,
            wcE' _ _ (by have := ConPanqueque.T.Big.tagN_lt v; omega) (by omega)]
          simp [h5]) (fun _ => ?_) (fun h => absurd h (by decide))
      rcases v with _ | _ | _ | _ | _ | ⟨Dt, c⟩ | _ | _ | _ | _ <;> simp [ENodeView.tagN] at h5
      have hta : b.tag = ETag.lam := by rw [hat]; rfl
      simp only [hta, beq_self_eq_true, ite_true]
      refine specR_runBind (show viewBind b s = .ok (some (Dt, c), s) by
        rw [WC.viewBind_run, WC.viewBind_of_view_lam hta hv]) ?_
      refine specR_loadI' aiD _ (P + 0) (P + BitVec.ofNat 64 0) (Enc.idxW Dt) (by decide)
        (by simp +decide [sev, Env.get_cons]) rfl
        (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW Dt) [Enc.idxW c] []) ?_
      refine specR_loadI' aiC _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW c) (by decide)
        (by simp +decide [sev, Env.get_cons]) rfl
        (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW Dt) (Enc.idxW c) [] []) ?_
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get_cons, Env.get, aiParams, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv aiC) (Enc.idxW c) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
      refine ConPanqueque.T.Big.specR_viewP c (by simp) (by simp +decide [Env.get_cons] <;> rfl)
        (by simp +decide [Env.get_cons, Env.get, aiParams, ctxEnv] <;> rfl) (by decide) (fun vc Pc hvc htnc hlenc => ?_)
      have hatc : c.tag = UInt32.ofNat vc.tagN := tag_of_tagN htnc
      by_cases h0 : vc.tagN = 0
      swap
      · refine specR_ifI _ 0 (by
            simp only [veEqC]
            rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 vc.tagN) (BitVec.ofNat 64 0) (by simp [sev, Env.get_cons]) rfl,
              wcE' _ _ (by have := ConPanqueque.T.Big.tagN_lt vc; omega) (by omega)]
            simp [h0]) (fun h => absurd rfl h) (fun _ => ?_)
        have : (c.tag == ETag.bvar) = false := by
          rw [hatc]
          have hl := ConPanqueque.T.Big.tagN_lt vc
          have : UInt32.ofNat vc.tagN ≠ ETag.bvar := by
            intro e; have := congrArg UInt32.toNat e; simp [ETag.bvar] at this; omega
          simpa using this
        simp only [this, Bool.false_eq_true, ite_false]
        exact ret0 _ _ _
      refine specR_ifI _ 1 (by
          simp only [veEqC]
          rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 vc.tagN) (BitVec.ofNat 64 0) (by simp [sev, Env.get_cons]) rfl,
            wcE' _ _ (by have := ConPanqueque.T.Big.tagN_lt vc; omega) (by omega)]
          simp [h0]) (fun _ => ?_) (fun h => absurd h (by decide))
      rcases vc with ⟨j⟩ | _ | _ | _ | _ | _ | _ | _ | _ | _ <;> simp [ENodeView.tagN] at h0
      have htc : c.tag = 0 := by rw [hatc]; rfl
      simp only [show (c.tag == ETag.bvar) = true by rw [htc]; rfl, ite_true]
      refine specR_runBind (viewBVar_run c htc s _ hvc) ?_
      simp only [projBVar]
      refine bvIdx_spec aiJ Pc j (by decide) (by simp [Env.get_cons]) (by simp [Env.get_cons])
        (fun q hq => List.mem_append_left _ hq) hlenc (fun hj => ?_)
      by_cases j1 : j = 1
      · subst j1
        refine specR_ifI _ 1 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun h => absurd h (by decide))
        simp only [beq_self_eq_true, ite_true]
        by_cases e : p = p'
        · subst e
          refine specR_ifI _ 1 (by
              simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
              simp only [Γ0] at gP gP2; rw [gP, gP2]; simp) (fun _ => ?_) (fun h => absurd h (by decide))
          simp only [beq_self_eq_true, ite_true]
          refine specR_internBVarI ra (ctxOK_H hok H) hcB aiZ (.const 0) 0 (by decide) (by decide) rfl (fun z s1 => ?_)
          by_cases ez : Dt = z
          · subst ez
            refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
              (fun _ => ?_) (fun h => absurd h (by decide))
            simp only [beq_self_eq_true, ite_true]
            exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
          · have hne : Enc.idxW Dt ≠ Enc.idxW z := fun h => ez (Enc.idxW_inj h)
            refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
              (fun h => absurd rfl h) (fun _ => ?_)
            have : (Dt == z) = false := by simpa using ez
            simp only [this, Bool.false_eq_true, ite_false]
            refine specR_congr (m' := annWitness C.fe Dt >>= fun r => pure r) (by rw [bind_pure]) ?_
            refine specR_callNIH (C := ctxH C H) aiR fAnnWitness awParams [vv aiD] (awBody C) [Enc.idxW Dt]
              (by decide) rfl (by decide) hcW ⟨by simp +decide [sev, Env.get_cons], trivial⟩
              (PostB (ctxH C H)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
              (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu awParams _ rfl hlk)
                (aw_spec ra C hok hf hcN hcG hcP H Dt s1))
              (fun r w s2 H2 hp2 hw => ?_)
            subst hw
            exact specR_returnI _ _ (by simp [sev, Env.get_cons])
              (fun t ht => ⟨H2, hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
        · have hne : Enc.idxW p ≠ Enc.idxW p' := fun h => e (Enc.idxW_inj h)
          refine specR_ifI _ 0 (by
              simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
              simp only [Γ0] at gP gP2; rw [gP, gP2]; simp [hne]) (fun h => absurd rfl h) (fun _ => ?_)
          have : (p == p') = false := by simpa using e
          simp only [this, Bool.false_eq_true, ite_false]
          exact ret0 _ _ _
      · have hne : BitVec.ofNat 64 j ≠ BitVec.ofNat 64 1 := (ofNat_eq_iff hj (by decide)).not.mpr j1
        refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
          (fun h => absurd rfl h) (fun _ => ?_)
        have : (j == 1) = false := by simpa using j1
        simp only [this, Bool.false_eq_true, ite_false]
        exact ret0 _ _ _
    · refine specR_ifI _ _ (gArk 2 (by decide)) (fun hw => absurd hw (by simp [boolW, h2])) (fun _ => ?_)
      have e2 : (arity == 2) = false := by simpa using h2
      simp only [e2, Bool.false_eq_true, ite_false]
      exact ret0 _ _ _


theorem av_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ avLocals → (ctxEnv C ++ avParams.zip vals).get x = none :=
  Knot.params_none C avLocals avParams vals (by decide) (by decide)

/-- **`annIdentVal`**, the level parameters a block of the environment heap. -/
theorem av_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : FrontOK C)
    (hcN : C.code.lookup Front.fInternNStr = some ([(Front.pKeyN, .one), (lEn, .one), (lEp, .one), (lHn, .one)], Front.nameStrBody, .one))
    (hcG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (hcB : C.code.lookup fInternBVar = some ([(lIw, .one)], bvarBody, .one))
    (hcW : C.code.lookup fAnnWitness = some (awParams.map (fun p => (p, ShapeHOL.one)), awBody C, .one))
    (hcI : C.code.lookup fAnnIdentBody = some (aiParams.map (fun p => (p, ShapeHOL.one)), aiBody, .one))
    (H : List (BitVec 64)) (lps : List NIdx) (ol : Nat) (hl : EBlk C.EH ol (lps.map Enc.idxW))
    (arity : Nat) (har : arity < 2 ^ 64) (v : EIdx) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (avParams.zip [ecell C ol, BitVec.ofNat 64 arity, Enc.idxW v]))
      avBody s (annIdentVal C.fe lps arity v) (PostB (ctxH C H)) := by
  refine specR_prologue (postB_locals _) (av_none _ _) ?_
  unfold annIdentVal
  let Γ0 : Env := ctxEnv (ctxH C H) ++ avParams.zip [ecell C ol, BitVec.ofNat 64 arity, Enc.idxW v]
  have gL : Γ0.get avL = some (ecell C ol) := by simp +decide [Γ0, Env.get, avParams, ctxEnv]
  have gAr : Γ0.get avAr = some (BitVec.ofNat 64 arity) := by simp +decide [Γ0, Env.get, avParams, ctxEnv]
  have gV : Γ0.get avV = some (Enc.idxW v) := by simp +decide [Γ0, Env.get, avParams, ctxEnv]
  have ret0 : ∀ (s1 : AState) (Γ : Env) (M : Mem), SpecR (σ := σ) (Inv (ctxH C H) s1 Γ M (ctxLocals ++ avLocals))
      (.return (.const 0)) s1 (pure false) (PostB (ctxH C H)) := fun s1 Γ M =>
    specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_fact (fun t ht => ht.sr.env.1.len) (fun hEN => ?_)
  have hEN' : C.EH.length ≤ C.EN := hEN
  have hlay := hok.envLay
  have hll : ol + 1 + lps.length ≤ C.EH.length := by
    have := blkAt_len hl; simp only [List.length_map] at this; exact this
  refine specR_envLoadI (C := ctxH C H) avN (vv avL) ol (BitVec.ofNat 64 lps.length) (by decide)
    (by simp only [sev, sev_vv]; exact gL) (by show C.EH[ol]? = _; rw [hl.1]; simp) ?_
  by_cases h1 : lps.length = 1
  swap
  · refine specR_ifI _ 0 (by
        simp only [veEqC]
        rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 lps.length) (BitVec.ofNat 64 1) (by simp [sev, Env.get_cons]) rfl,
          wcE' _ _ (by omega) (by omega)]
        simp [h1]) (fun h => absurd rfl h) (fun _ => ?_)
    have : (lps.length == 1) = false := by simpa using h1
    simp only [this, Bool.false_eq_true, ite_false]
    exact ret0 _ _ _
  refine specR_ifI _ 1 (by
      simp only [veEqC]
      rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 lps.length) (BitVec.ofNat 64 1) (by simp [sev, Env.get_cons]) rfl,
        wcE' _ _ (by omega) (by omega)]
      simp [h1]) (fun _ => ?_) (fun h => absurd h (by decide))
  simp only [h1, beq_self_eq_true, ite_true]
  have tagNo : ∀ (h : EIdx) (vh : ENodeView) (k : Nat) (u32 : UInt32), u32 = UInt32.ofNat k → k < 16 →
      h.tag = UInt32.ofNat vh.tagN → vh.tagN ≠ k → (h.tag == u32) = false := by
    intro h vh k u32 hu hk hat hne
    rw [hat, hu]
    have hl := ConPanqueque.T.Big.tagN_lt vh
    have : UInt32.ofNat vh.tagN ≠ UInt32.ofNat k := by
      intro e; have := congrArg UInt32.toNat e; simp at this; omega
    simpa using this
  have gTag : ∀ (Γ : Env) (vh : ENodeView) (k : Nat), k < 16 → Γ.get lDg = some (BitVec.ofNat 64 vh.tagN) →
      sev Γ (veEqC lDg k) = some (boolW (vh.tagN == k)) := by
    intro Γ vh k hk hg
    simp only [veEqC]
    rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 vh.tagN) (BitVec.ofNat 64 k) (by simp only [sev, sev_vv]; exact hg) rfl,
      wcE' _ _ (by have := ConPanqueque.T.Big.tagN_lt vh; omega) (by omega)]
    by_cases h : vh.tagN = k <;> simp [h, boolW]
  unfold viewOf
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get_cons, Env.get, avParams, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv avV) (Enc.idxW v) (by decide)
    (by simp only [sev, sev_vv, Env.get_cons]; simp +decide; exact gV) ?_
  refine ConPanqueque.T.Big.specR_viewP v (by simp) (by simp +decide [Env.get_cons] <;> rfl)
    (by simp +decide [Env.get_cons, Env.get, avParams, ctxEnv] <;> rfl) (by decide) (fun vv' P hv htn hlen => ?_)
  have hat := tag_of_tagN htn
  by_cases h5 : vv'.tagN = 5
  swap
  · refine specR_ifI _ _ (gTag _ vv' 5 (by decide) (by simp [Env.get_cons])) (fun h => absurd h (by simp [boolW, h5]))
      (fun _ => ?_)
    simp only [tagNo v vv' 5 ETag.lam rfl (by decide) hat h5, Bool.false_eq_true, ite_false]
    exact ret0 _ _ _
  refine specR_ifI _ _ (gTag _ vv' 5 (by decide) (by simp [Env.get_cons])) (fun _ => ?_)
    (fun h => absurd h (by simp [boolW, h5]))
  rcases vv' with _ | _ | _ | _ | _ | ⟨ty, b⟩ | _ | _ | _ | _ <;> simp [ENodeView.tagN] at h5
  have hta : v.tag = ETag.lam := by rw [hat]; rfl
  simp only [hta, beq_self_eq_true, ite_true]
  refine specR_runBind (show viewBind v s = .ok (some (ty, b), s) by
    rw [WC.viewBind_run, WC.viewBind_of_view_lam hta hv]) ?_
  refine specR_loadI' avT _ (P + 0) (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide)
    (by simp +decide [sev, Env.get_cons]) rfl
    (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW ty) [Enc.idxW b] []) ?_
  refine specR_loadI' avB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide)
    (by simp +decide [sev, Env.get_cons]) rfl
    (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW b) [] []) ?_
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get_cons, Env.get, avParams, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv avT) (Enc.idxW ty) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
  refine ConPanqueque.T.Big.specR_viewP ty (by simp) (by simp +decide [Env.get_cons] <;> rfl)
    (by simp +decide [Env.get_cons, Env.get, avParams, ctxEnv] <;> rfl) (by decide) (fun vt Pt hvt htnt hlent => ?_)
  have hatt := tag_of_tagN htnt
  by_cases h2 : vt.tagN = 2
  swap
  · refine specR_ifI _ _ (gTag _ vt 2 (by decide) (by simp [Env.get_cons])) (fun h => absurd h (by simp [boolW, h2]))
      (fun _ => ?_)
    simp only [tagNo ty vt 2 ETag.sort rfl (by decide) hatt h2, Bool.false_eq_true, ite_false]
    exact ret0 _ _ _
  refine specR_ifI _ _ (gTag _ vt 2 (by decide) (by simp [Env.get_cons])) (fun _ => ?_)
    (fun h => absurd h (by simp [boolW, h2]))
  rcases vt with _ | _ | u | _ | _ | _ | _ | _ | _ | _ <;> simp [ENodeView.tagN] at h2
  have htt : ty.tag = ETag.sort := by rw [hatt]; rfl
  simp only [htt, beq_self_eq_true, ite_true]
  refine specR_runBind (show viewSort ty s = .ok (some u, s) by
    rw [Comp.viewSort_run, WC.viewSort_of_view htt hvt]) ?_
  refine specR_loadI' avU _ (Pt + 0) (Pt + BitVec.ofNat 64 0) (Enc.idxW u) (by decide)
    (by simp +decide [sev, Env.get_cons]) rfl
    (by simpa [encEView, Enc.encSort] using wordsAt_mem0 Pt (Enc.idxW u) [] _) ?_
  refine specR_assignI lFl (vv lFll) C.FLl (by decide) (by simp +decide [Env.get_cons, Env.get, avParams, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv avU) (Enc.idxW u) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
  refine specR_lviewPI (C := ctxH C H) u (by simp) (by simp +decide [Env.get_cons] <;> rfl)
    (by simp +decide [Env.get_cons, Env.get, avParams, ctxEnv] <;> rfl) (by decide) (fun lv Pl hlv htl hlenl => ?_)
  refine specR_runBind (show viewL u s = .ok (lv, s) by rw [viewL_run, hlv]) ?_
  have gL4 : sev ((lRp, Pl) :: (lRn, BitVec.ofNat 64 (encLView lv).length) :: (lDt, BitVec.ofNat 64 u.tier.toNat) ::
      (lDg, BitVec.ofNat 64 lv.tagN) :: (lDi, BitVec.ofNat 64 u.idxNat) :: (lDh, Enc.idxW u) :: (lFl, C.FLl) ::
      (avU, Enc.idxW u) :: (lRp, Pt) :: (lRn, BitVec.ofNat 64 (encEView (.sort u)).length) ::
      (lDt, BitVec.ofNat 64 ty.tier.toNat) :: (lDg, BitVec.ofNat 64 (ENodeView.sort u).tagN) ::
      (lDi, BitVec.ofNat 64 ty.idxNat) :: (lDh, Enc.idxW ty) :: (lFl, C.FLe) :: (avB, Enc.idxW b) :: (avT, Enc.idxW ty) ::
      (lRp, P) :: (lRn, BitVec.ofNat 64 (encEView (.lam ty b)).length) :: (lDt, BitVec.ofNat 64 v.tier.toNat) ::
      (lDg, BitVec.ofNat 64 (ENodeView.lam ty b).tagN) :: (lDi, BitVec.ofNat 64 v.idxNat) :: (lDh, Enc.idxW v) ::
      (lFl, C.FLe) :: (avN, BitVec.ofNat 64 lps.length) :: Γ0) (veEqC lDg 4) = some (boolW (lv.tagN == 4)) := by
    simp only [veEqC]
    have hl4 : lv.tagN < 16 := by cases lv <;> simp [LNodeView.tagN]
    rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 lv.tagN) (BitVec.ofNat 64 4) (by simp [sev, Env.get_cons]) rfl,
      wcE' _ _ (by omega) (by omega)]
    by_cases h : lv.tagN = 4 <;> simp [h, boolW]
  cases lv with
  | param p' =>
    refine specR_ifI _ _ gL4 (fun _ => ?_) (fun h => absurd h (by simp [boolW, LNodeView.tagN]))
    simp only
    refine specR_loadI' avP2 _ (Pl + 0) (Pl + BitVec.ofNat 64 0) (Enc.idxW p') (by decide)
      (by simp +decide [sev, Env.get_cons]) rfl
      (List.mem_append_left _ (by have := wordsAt_mem0 Pl (Enc.idxW p') [] []; simpa [encLView, Enc.encParam] using this)) ?_
    have h0 : 0 < lps.length := by omega
    refine specR_envLoadI (C := ctxH C H) avP _ (ol + 1) (Enc.idxW lps[0]) (by decide)
      (by
        simp +decide [sev, Env.get_cons]
        simp only [Γ0] at gL; rw [gL]; simp
        show _ = ecell C (ol + 1)
        simp only [ecell]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega)
      (by have := hl.2 0 (by simp; omega); show C.EH[ol + 1]? = _; simpa using this) ?_
    have hgd : lps.getD 0 default = lps[0] := by simp [List.getD_eq_getElem?_getD, h0]
    rw [hgd]
    refine specR_congr (m' := annIdentBody C.fe lps[0] p' arity b >>= fun r => pure r) (by rw [bind_pure]) ?_
    refine specR_callNIH (C := ctxH C H) avR fAnnIdentBody aiParams [vv avP, vv avP2, vv avAr, vv avB] aiBody
      [Enc.idxW lps[0], Enc.idxW p', BitVec.ofNat 64 arity, Enc.idxW b] (by decide) rfl (by decide) hcI
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons],
        by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gAr; exact gAr,
        by simp +decide [sev, Env.get_cons], trivial⟩
      (PostB (ctxH C H)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu aiParams _ rfl hlk)
        (ai_spec ra C hok hf hcN hcG hcP hcB hcW H lps[0] p' arity har b s))
      (fun r w s2 H2 hp2 hw => ?_)
    subst hw
    exact specR_returnI _ _ (by simp [sev, Env.get_cons])
      (fun t ht => ⟨H2, hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | _ =>
    refine specR_ifI _ _ gL4 (fun h => absurd h (by simp [boolW, LNodeView.tagN])) (fun _ => ?_)
    exact ret0 _ _ _


theorem an_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ anLocals → (ctxEnv C ++ anParams.zip vals).get x = none :=
  Knot.params_none C anLocals anParams vals (by decide) (by decide)

/-- **`annIdent`** against the context's environment. -/
theorem an_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : FrontOK C)
    (hcN : C.code.lookup Front.fInternNStr = some ([(Front.pKeyN, .one), (lEn, .one), (lEp, .one), (lHn, .one)], Front.nameStrBody, .one))
    (hcG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (hcB : C.code.lookup fInternBVar = some ([(lIw, .one)], bvarBody, .one))
    (hcW : C.code.lookup fAnnWitness = some (awParams.map (fun p => (p, ShapeHOL.one)), awBody C, .one))
    (hcI : C.code.lookup fAnnIdentBody = some (aiParams.map (fun p => (p, ShapeHOL.one)), aiBody, .one))
    (hcV : C.code.lookup fAnnIdentVal = some (avParams.map (fun p => (p, ShapeHOL.one)), avBody, .one))
    (H : List (BitVec 64)) (n : NIdx) (arity : Nat) (har : arity < 2 ^ 64) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (anParams.zip [Enc.idxW n, BitVec.ofNat 64 arity]))
      (anBody (ctxH C H)) s (annIdent C.fe n arity) (PostB (ctxH C H)) := by
  refine specR_prologue (postB_locals _) (an_none _ _) ?_
  unfold annIdent
  let Γ0 : Env := ctxEnv (ctxH C H) ++ anParams.zip [Enc.idxW n, BitVec.ofNat 64 arity]
  have gN : Γ0.get anN = some (Enc.idxW n) := by simp +decide [Γ0, Env.get, anParams, ctxEnv]
  have gAr : Γ0.get anAr = some (BitVec.ofNat 64 arity) := by simp +decide [Γ0, Env.get, anParams, ctxEnv]
  have ret0 : ∀ (Γ : Env) (M : Mem), SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ anLocals))
      (.return (.const 0)) s (pure false) (PostB (ctxH C H)) := fun Γ M =>
    specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_envFindI (C := ctxH C H) (ctxOK_H hok H) hcG hcP anX (vv anN) n (by decide)
    (by simp only [sev, sev_vv]; exact gN) (by simp +decide [Env.get, anParams, ctxEnv] <;> rfl) ?_
  have hfr := find_rel (ctxOK_H hok H) n
  have efe : (ctxH C H).fe = C.fe := rfl
  rw [efe] at hfr
  cases hfm : C.fe.find? n with
  | none =>
    rw [hfm] at hfr
    simp only [hfr, optWG]
    refine specR_ifI _ 1 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact ret0 _ _
  | some ci =>
    rw [hfm] at hfr
    obtain ⟨o, he, hcie⟩ := hfr
    simp only [he, optWG, id]
    refine specR_fact (fun t ht => ht.sr.env.1.len) (fun hEN => ?_)
    have hEN' : C.EH.length ≤ C.EN := hEN
    have ho : o < C.EN := by have := cie_lt hcie; exact Nat.lt_of_lt_of_le this hEN
    have hne : ecell (ctxH C H) o + 1 ≠ 0 := ecell_succ_ne (ctxOK_H hok H) ho
    refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    have hlay := hok.envLay
    cases ci with
    | defnInfo cv val hint =>
      obtain ⟨hcve, h1, hval, -⟩ := hcie
      refine specR_envLoadI (C := ctxH C H) anT _ o (BitVec.ofNat 64 1) (by decide)
        (by simp +decide [sev, Env.get_cons]; exact ecell_succ_sub _ o) h1 ?_
      refine specR_ifI _ 1 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only
      obtain ⟨w, hw2, ol, hwo, heb⟩ := hcve.2.1
      refine specR_envLoadI (C := ctxH C H) anL _ (o + 2) w (by decide)
        (by
          simp +decide [sev, Env.get_cons]
          simp only [ecell]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega)
        (by rw [show o + 2 = o + 1 + 1 by omega]; exact hw2) ?_
      refine specR_envLoadI (C := ctxH C H) anV _ (o + 4) (Enc.idxW val) (by decide)
        (by
          simp +decide [sev, Env.get_cons]
          simp only [ecell]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega) hval ?_
      refine specR_congr (m' := annIdentVal C.fe cv.levelParams arity val >>= fun r => pure r) (by rw [bind_pure]) ?_
      refine specR_callNIH (C := ctxH C H) anR fAnnIdentVal avParams [vv anL, vv anAr, vv anV] avBody
        [ecell C ol, BitVec.ofNat 64 arity, Enc.idxW val] (by decide) rfl (by decide) hcV
        ⟨by simp +decide [sev, Env.get_cons, hwo]; rfl,
          by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gAr; exact gAr,
          by simp +decide [sev, Env.get_cons], trivial⟩
        (PostB (ctxH C H)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu avParams _ rfl hlk)
          (av_spec ra C hok hf hcN hcG hcP hcB hcW hcI H cv.levelParams ol heb arity har val s))
        (fun r w s2 H2 hp2 hw => ?_)
      subst hw
      exact specR_returnI _ _ (by simp [sev, Env.get_cons])
        (fun t ht => ⟨H2, hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | _ =>
      obtain ⟨k, hk, hk1⟩ : ∃ k : Nat, C.EH[o]? = some (BitVec.ofNat 64 k) ∧ k ≠ 1 ∧ k < 16 := by
        first
          | exact ⟨0, hcie.2, by decide, by decide⟩
          | exact ⟨2, hcie.2, by decide, by decide⟩
          | exact ⟨3, hcie.2.1, by decide, by decide⟩
          | exact ⟨4, hcie.2.1, by decide, by decide⟩
          | exact ⟨5, hcie.2.1, by decide, by decide⟩
      refine specR_envLoadI (C := ctxH C H) anT _ o (BitVec.ofNat 64 k) (by decide)
        (by simp +decide [sev, Env.get_cons]; exact ecell_succ_sub _ o) hk ?_
      have hne1 : BitVec.ofNat 64 k ≠ BitVec.ofNat 64 1 := (ofNat_eq_iff (by omega) (by decide)).not.mpr hk1.1
      refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne1])
        (fun h => absurd rfl h) (fun _ => ?_)
      exact ret0 _ _

end

end ConPanqueque.T.Ind
