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

end

end ConPanqueque.T.Ind
