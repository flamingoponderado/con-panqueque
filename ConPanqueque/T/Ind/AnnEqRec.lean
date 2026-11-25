import ConPanqueque.T.Ind.AnnEq

/-!
# `s` is `c` with type annotations consumed at its head (`annEq`)

Lean's `consume_type_annotations` up to equivalent levels: `optParam`/`autoParam` (arity 2) and
`outParam`/`semiOutParam` (arity 1) stored as identities on their type argument are looked through.
The annotation names are interned as `topName`: the anonymous name is an image constant (`anonH`), the
string component the frontend's `internNStr`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI
open ConPanqueque.Start (vPn vKa strStepP strStep_spec strBytes)
open ConPanqueque.Front (FrontOK frontOK_H)

def aeBt := ofString "ae_bt"
def aeS := ofString "ae_s"
def aeC := ofString "ae_c"
def aeR := ofString "ae_r"
def aeF := ofString "ae_f"
def aeX := ofString "ae_x"
def aeG := ofString "ae_g"
def aeA := ofString "ae_a"
def aeN := ofString "ae_n"
def aeU := ofString "ae_u"
def aeO := ofString "ae_o"
def aeT := ofString "ae_t"
def fAnnEq := ofString "annEq"

def aeParams : List MlS := [aeBt, pFu, aeS, aeC]
def aeLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, aeR, aeF, aeX, aeG, aeA, aeN, aeU, aeO, aeT, vPn, vKa]

/-- `topName str` into `vPn`. -/
def topNameP (C : Ctx) (str : String) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local vPn (.const (Enc.idxW anonH))) (strStepP C str rest)

/-- An annotation head `n` (in `aeN`) at levels `aeU`: both annotation names, the identity test at `k`, then the
recursion on `xv`. -/
def aeArm (C : Ctx) (s1 s2 : String) (k : Nat) (xv : MlS) : ProgHOL 64 :=
  .seq (.assign .local lDh (vv aeU)) (.seq (.assign .local lFl (vv lFls)) (.seq lsViewP
  (.ite (veEqC lRn 1)
    (topNameP C s1 (.seq (.assign .local aeO (vv vPn))
    (topNameP C s2 (.seq (.assign .local aeT (vv vPn))
    (.ite (.op .or [.cmp .equal (vv aeN) (vv aeO), .cmp .equal (vv aeN) (vv aeT)])
      (.seq (.call (some (some (.local, aeR), none)) fAnnIdent [vv aeBt, vv aeN, .const (BitVec.ofNat 64 k)])
      (.ite (veEqC aeR 0) (.return (.const 0))
      (.seq (.call (some (some (.local, aeR), none)) fAnnEq [vv aeBt, .op .sub [vv pFu, .const 1], vv aeS, vv xv])
        (.return (vv aeR)))))
      (.return (.const 0)))))))
    (.return (.const 0)))))

def aeBody (C : Ctx) : ProgHOL 64 := prologue aeLocals
  (.ite (.cmp .equal (vv pFu) (.const 0)) hang
  (.seq (.call (some (some (.local, aeR), none)) fLvlEqE [.const (BitVec.ofNat 64 coreWalkFuel), vv aeS, vv aeC])
  (.ite (veEqC aeR 0)
    (viewOf aeC
      (.ite (veEqC lDg 4)
        (.seq (.assign .local aeF (.load .one (.op .add [vv lRp, .const 0])))
        (.seq (.assign .local aeX (.load .one (.op .add [vv lRp, .const 8])))
        (viewOf aeF
          (.ite (veEqC lDg 4)
            (.seq (.assign .local aeG (.load .one (.op .add [vv lRp, .const 0])))
            (.seq (.assign .local aeA (.load .one (.op .add [vv lRp, .const 8])))
            (viewOf aeG
              (.ite (veEqC lDg 3)
                (.seq (.assign .local aeN (.load .one (.op .add [vv lRp, .const 0])))
                (.seq (.assign .local aeU (.load .one (.op .add [vv lRp, .const 8])))
                  (aeArm C "optParam" "autoParam" 2 aeA)))
                (.return (.const 0))))))
            (.ite (veEqC lDg 3)
              (.seq (.assign .local aeN (.load .one (.op .add [vv lRp, .const 0])))
              (.seq (.assign .local aeU (.load .one (.op .add [vv lRp, .const 8])))
                (aeArm C "outParam" "semiOutParam" 1 aeX)))
              (.return (.const 0)))))))
        (.return (.const 0))))
    (.return (.const 1)))))

section
variable {σ : Type}

theorem topName_spec {β : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : FrontOK C)
    (hcN : C.code.lookup Front.fInternNStr = some ([(Front.pKeyN, .one), (lEn, .one), (lEp, .one), (lHn, .one)], Front.nameStrBody, .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hPn : vPn ∈ D) (hKa : vKa ∈ D)
    (hanon : internNNode .anonymous s = .ok (anonH, s)) (str : String) (hn : (strBytes str).length < 2 ^ 50)
    {rest : ProgHOL 64} {k : NIdx → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (hk : ∀ h s' o, internNNode (.str anonH str) s = .ok (h, s') →
      SpecR (Inv C s' ((vPn, Enc.idxW h) :: (vKa, cellA C o) :: (vPn, Enc.idxW anonH) :: Γ) [] D) rest s' (k h) R) :
    SpecR (Inv C s Γ M D) (topNameP C str rest) s (topName str >>= k) R := by
  unfold topNameP topName
  refine specR_assignI vPn _ (Enc.idxW anonH) hPn rfl ?_
  refine specR_congr (m' := internNNode .anonymous >>= fun a => internNNode (.str a str) >>= k)
    (by rw [bind_assoc]) ?_
  refine specR_runBind hanon ?_
  exact strStep_spec ra C hok hf hcN s _ M D hPn hKa anonH (by simp [Env.get_cons]) str hn hk

theorem ae_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ aeLocals → (ctxEnv C ++ aeParams.zip vals).get x = none :=
  Knot.params_none C aeLocals aeParams vals (by decide) (by decide)

/-- The code `annEq` runs. -/
structure AECodes (C : Ctx) : Prop where
  ae : C.code.lookup fAnnEq = some (aeParams.map (fun p => (p, ShapeHOL.one)), aeBody C, .one)
  ve : VECodes C
  cN : C.code.lookup Front.fInternNStr = some ([(Front.pKeyN, .one), (lEn, .one), (lEp, .one), (lHn, .one)], Front.nameStrBody, .one)
  cG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  cP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  cB : C.code.lookup fInternBVar = some ([(lIw, .one)], bvarBody, .one)
  cW : C.code.lookup fAnnWitness = some (awParams.map (fun p => (p, ShapeHOL.one)), awBody C, .one)
  cI : C.code.lookup fAnnIdentBody = some (aiParams.map (fun p => (p, ShapeHOL.one)), aiBody, .one)
  cV : C.code.lookup fAnnIdentVal = some (avParams.map (fun p => (p, ShapeHOL.one)), avBody, .one)
  cA : C.code.lookup fAnnIdent = some (anParams.map (fun p => (p, ShapeHOL.one)), anBody C, .one)
  cF : C.code.lookup fBFindGo = some (bfParams.map (fun p => (p, ShapeHOL.one)), bfBody C, .one)

def RecAE (C : Ctx) (es : List (NIdx × Nat × IConstantInfo)) (ob : Nat) (fe : IFEnv) (n : Nat) : Prop :=
  ∀ (H : List (BitVec 64)) (_ : BTabAt C H ob es) (c0 c : EIdx) (s : AState),
    SpecR (Pre (σ := σ) (ctxH C H) s (aeParams.zip [cellA C ob, BitVec.ofNat 64 n, Enc.idxW c0, Enc.idxW c])) (aeBody C)
      s (annEq fe n c0 c) (PostB (ctxH C H))

theorem sev_or2 (Γ : Env) (e1 e2 : ExpHOL 64) (a b : BitVec 64)
    (h1 : sev Γ e1 = some a) (h2 : sev Γ e2 = some b) : sev Γ (.op .or [e1, e2]) = some (a ||| b) := by
  simp [sev, h1, h2]

theorem boolW_or (a b : Bool) : boolW a ||| boolW b = boolW (a || b) := by
  cases a <;> cases b <;> rfl

theorem sev_eqIdx (Γ : Env) (x y : MlS) (a b : NIdx) (hx : Γ.get x = some (Enc.idxW a))
    (hy : Γ.get y = some (Enc.idxW b)) : sev Γ (.cmp .equal (vv x) (vv y)) = some (boolW (a == b)) := by
  rw [sev_cmp2 _ _ _ _ (Enc.idxW a) (Enc.idxW b) (by simp only [sev, sev_vv]; exact hx)
    (by simp only [sev, sev_vv]; exact hy)]
  by_cases e : a = b
  · subst e; simp [boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  · have : Enc.idxW a ≠ Enc.idxW b := fun h => e (Enc.idxW_inj h)
    simp [boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e, this]

/-- An annotation arm. -/
theorem aeArm_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : FrontOK C)
    (hc : AECodes C) (hA : denoteN C.St.ns anonH = some .anonymous)
    (es : List (NIdx × Nat × IConstantInfo)) (ob : Nat) (fe : IFEnv) (hfe : ∀ n, fe.find? n = bfLook es C.fe n)
    (fuel : Nat) (ih : RecAE (σ := σ) C es ob fe fuel)
    (H H1 : List (BitVec 64)) (hp : H <+: H1) (hT : BTabAt C H1 ob es) (s1 : AState) (Γ : Env) (M : Mem)
    (c0 x : EIdx) (nm : NIdx) (us : LsIdx) (str1 str2 : String) (k : Nat) (hk : k < 2 ^ 64) (xv : MlS)
    (hxv : xv = aeA ∨ xv = aeX) (hb1 : (strBytes str1).length < 2 ^ 50) (hb2 : (strBytes str2).length < 2 ^ 50)
    (gN : Γ.get aeN = some (Enc.idxW nm)) (gU : Γ.get aeU = some (Enc.idxW us)) (gX : Γ.get xv = some (Enc.idxW x))
    (gS : Γ.get aeS = some (Enc.idxW c0)) (gFu : Γ.get pFu = some (BitVec.ofNat 64 (fuel + 1)))
    (gFls : Γ.get lFls = some C.FLs) (gDir : Γ.get lDir = some C.L.DIR) (gBt : Γ.get aeBt = some (cellA C ob)) :
    SpecR (σ := σ) (Inv (ctxH C H1) s1 Γ M (ctxLocals ++ aeLocals)) (aeArm C str1 str2 k xv) s1
      (do
        let __do_lift ← viewLsLen us
        match __do_lift with
          | some 1 => do
            let o ← topName str1
            let t ← topName str2
            if (nm == o || nm == t) = true then do
                let __do_lift ← annIdent fe nm k
                if __do_lift = true then annEq fe fuel c0 x else pure false
              else pure false
          | some _ => pure false
          | none => failDanglingLs)
      (PostB (ctxH C H)) := by
  have ret0 : ∀ (H2 : List (BitVec 64)) (s2 : AState) (Γ' : Env) (M' : Mem), H <+: H2 →
      SpecR (σ := σ) (Inv (ctxH C H2) s2 Γ' M' (ctxLocals ++ aeLocals)) (.return (.const 0)) s2 (pure false)
        (PostB (ctxH C H)) := fun H2 s2 Γ' M' hp2 =>
    specR_returnI _ 0 rfl (fun t ht => ⟨H2, hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  have hxa : xv ≠ lDh ∧ xv ≠ lFl ∧ xv ≠ lRp ∧ xv ≠ lRn ∧ xv ≠ lDt ∧ xv ≠ lDg ∧ xv ≠ lDi ∧ xv ≠ vPn ∧ xv ≠ vKa ∧
      xv ≠ aeO ∧ xv ≠ aeT ∧ xv ≠ aeR := by rcases hxv with rfl | rfl <;> decide
  unfold aeArm
  refine specR_assignI lDh (vv aeU) (Enc.idxW us) (by decide) (by simp only [sev, sev_vv]; exact gU) ?_
  refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [sev, Env.get_cons]; exact gFls) ?_
  refine specR_lsviewPI (C := ctxH C H1) us (by simp) (by simp +decide [Env.get_cons] <;> rfl)
    (by simp +decide [Env.get_cons]; exact gDir) (by decide) (fun vl Pl hvl htl hlenl => ?_)
  refine specR_runBind (WC.viewLsLen_run us s1 vl hvl) ?_
  by_cases h1 : vl.length = 1
  swap
  · refine specR_ifI _ 0 (by
        simp only [veEqC]
        rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 (vl.map Enc.idxW).length) (BitVec.ofNat 64 1)
          (by simp [sev, Env.get_cons]) rfl, wcE' _ _ (by simp at hlenl ⊢; omega) (by omega)]
        simp [h1]) (fun h => absurd rfl h) (fun _ => ?_)
    rcases hl : vl.length with _ | _ | j
    · simp only; exact ret0 H1 s1 _ _ hp
    · exact absurd hl h1
    · simp only; exact ret0 H1 s1 _ _ hp
  refine specR_ifI _ 1 (by
      simp only [veEqC]
      rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 (vl.map Enc.idxW).length) (BitVec.ofNat 64 1)
        (by simp [sev, Env.get_cons]) rfl, wcE' _ _ (by simp at hlenl ⊢; omega) (by omega)]
      simp [h1]) (fun _ => ?_) (fun h => absurd h (by decide))
  rw [h1]; simp only
  refine specR_fact (fun t ht => internAnon_run ht.sr hA) (fun hanon1 => ?_)
  refine topName_spec ra (ctxH C H1) (ctxOK_H hok H1) (frontOK_H hf H1) hc.cN s1 _ _ _ (by decide) (by decide)
    hanon1 str1 hb1 (fun o s2 om1 hr1 => ?_)
  refine specR_assignI aeO (vv vPn) (Enc.idxW o) (by decide) (by simp [sev, Env.get_cons]) ?_
  refine specR_fact (fun t ht => internAnon_run ht.sr hA) (fun hanon2 => ?_)
  refine topName_spec ra (ctxH C H1) (ctxOK_H hok H1) (frontOK_H hf H1) hc.cN s2 _ _ _ (by decide) (by decide)
    hanon2 str2 hb2 (fun t s3 om2 hr2 => ?_)
  refine specR_assignI aeT (vv vPn) (Enc.idxW t) (by decide) (by simp [sev, Env.get_cons]) ?_
  have hor : ∀ (Γ' : Env), Γ'.get aeN = some (Enc.idxW nm) → Γ'.get aeO = some (Enc.idxW o) →
      Γ'.get aeT = some (Enc.idxW t) →
      sev Γ' (.op .or [.cmp .equal (vv aeN) (vv aeO), .cmp .equal (vv aeN) (vv aeT)]) =
        some (boolW (nm == o || nm == t)) := fun Γ' h1 h2 h3 => by
    rw [sev_or2 _ _ _ _ _ (sev_eqIdx _ aeN aeO nm o h1 h2) (sev_eqIdx _ aeN aeT nm t h1 h3), boolW_or]
  by_cases hnt : (nm == o || nm == t) = true
  · refine specR_ifI _ _ (hor _ (by simp +decide [Env.get_cons]; exact gN) (by simp +decide [Env.get_cons])
        (by simp +decide [Env.get_cons])) (fun _ => ?_) (fun h => absurd h (by simp [boolW, hnt]))
    simp only [hnt, ite_true]
    refine specR_callNIH (C := ctxH C H1) aeR fAnnIdent anParams [vv aeBt, vv aeN, .const (BitVec.ofNat 64 k)]
      (anBody C) [cellA C ob, Enc.idxW nm, BitVec.ofNat 64 k] (by decide) rfl (by decide) hc.cA
      ⟨by simp +decide [sev, Env.get_cons]; exact gBt, by simp +decide [sev, Env.get_cons]; exact gN, rfl, trivial⟩
      (PostB (ctxH C H1)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu anParams _ rfl hlk)
        (an_spec ra C hok hf hc.cN hc.cG hc.cP hc.cB hc.cW hc.cI hc.cV hc.cF es ob fe hfe H1 hT nm k hk s3))
      (fun r w s4 H2 hp2 hw => ?_)
    subst hw
    have hp2' : H1 <+: H2 := hp2
    rcases r
    · refine specR_ifI _ 1 (by simp +decide [veEqC, sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact ret0 H2 s4 _ _ (hp.trans hp2')
    refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [ite_true]
    refine specR_congr (m' := annEq fe fuel c0 x >>= fun r => pure r) (by rw [bind_pure]) ?_
    refine specR_callNIH (C := ctxH C H2) aeR fAnnEq aeParams [vv aeBt, .op .sub [vv pFu, .const 1], vv aeS, vv xv]
      (aeBody C) [cellA C ob, BitVec.ofNat 64 fuel, Enc.idxW c0, Enc.idxW x] (by decide) rfl (by decide) hc.ae
      ⟨by simp +decide [sev, Env.get_cons]; exact gBt,
        by
          show sev _ _ = _
          rw [sev_sub2 _ _ _ _ _ (by simp +decide only [sev, sev_vv, Env.get_cons, ite_false]; exact gFu) rfl]
          exact congrArg some (ofNat_succ_sub_one fuel),
        by simp +decide [sev, Env.get_cons]; exact gS,
        by
          simp only [sev, sev_vv, Env.get_cons, hxa.1, hxa.2.1, hxa.2.2.1, hxa.2.2.2.1, hxa.2.2.2.2.1, hxa.2.2.2.2.2.1,
            hxa.2.2.2.2.2.2.1, hxa.2.2.2.2.2.2.2.1, hxa.2.2.2.2.2.2.2.2.1, hxa.2.2.2.2.2.2.2.2.2.1,
            hxa.2.2.2.2.2.2.2.2.2.2.1, hxa.2.2.2.2.2.2.2.2.2.2.2, ite_false]
          exact gX, trivial⟩
      (PostB (ctxH C H2)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu aeParams _ rfl hlk)
        (ih H2 (btabAt_mono hT hp2') c0 x s4))
      (fun r w s5 H3 hp3 hw => ?_)
    subst hw
    have hp3' : H2 <+: H3 := hp3
    exact specR_returnI _ _ (by simp [sev, Env.get_cons])
      (fun t ht => ⟨H3, (hp.trans hp2').trans hp3', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_ifI _ _ (hor _ (by simp +decide [Env.get_cons]; exact gN) (by simp +decide [Env.get_cons])
        (by simp +decide [Env.get_cons])) (fun h => absurd h (by simp [boolW, hnt])) (fun _ => ?_)
    simp only [hnt, Bool.false_eq_true, ite_false]
    exact ret0 H1 s3 _ _ hp

/-- **`annEq`** at fuel below `2 ^ 63`. -/
theorem ae_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : FrontOK C)
    (hc : AECodes C) (hA : denoteN C.St.ns anonH = some .anonymous)
    (es : List (NIdx × Nat × IConstantInfo)) (ob : Nat) (fe : IFEnv) (hfe : ∀ n, fe.find? n = bfLook es C.fe n) :
    ∀ n, n < 2 ^ 63 → RecAE (σ := σ) C es ob fe n := by
  intro n
  induction n with
  | zero =>
    intro _ H _ c0 c s
    refine specR_prologue (postB_locals _) (ae_none _ _) ?_
    refine specR_ifI _ _ rfl (fun _ => specR_hangI) (fun hw => ?_)
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, sev, Env.get, aeParams, ctxEnv] at hw
  | succ n ih =>
    intro hfu H hT c0 c s
    have ih' := ih (by omega)
    refine specR_prologue (postB_locals _) (ae_none _ _) ?_
    let Γ0 : Env := ctxEnv (ctxH C H) ++ aeParams.zip [cellA C ob, BitVec.ofNat 64 (n + 1), Enc.idxW c0, Enc.idxW c]
    have gBt : Γ0.get aeBt = some (cellA C ob) := by simp +decide [Γ0, Env.get, aeParams, ctxEnv]
    have gFu : Γ0.get pFu = some (BitVec.ofNat 64 (n + 1)) := by simp +decide [Γ0, Env.get, aeParams, ctxEnv]
    have gS : Γ0.get aeS = some (Enc.idxW c0) := by simp +decide [Γ0, Env.get, aeParams, ctxEnv]
    have gC : Γ0.get aeC = some (Enc.idxW c) := by simp +decide [Γ0, Env.get, aeParams, ctxEnv]
    refine specR_ifI _ 0 (by
        rw [sev_cmp2 _ _ _ _ _ _ (by simp only [sev, sev_vv]; exact gFu) rfl]
        have := ofNat_ne_zero (n + 1) (by omega) (by omega)
        simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact this)
      (fun hw => absurd rfl hw) (fun _ => ?_)
    rw [annEq]
    refine specR_callNIH (C := ctxH C H) aeR fLvlEqE veParams [.const (BitVec.ofNat 64 coreWalkFuel), vv aeS, vv aeC]
      veBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW c0, Enc.idxW c] (by decide) rfl
      (by simp +decide [ctxLocals, aeLocals]) hc.ve.ve
      ⟨rfl, by simp only [sev, sev_vv]; exact gS, by simp only [sev, sev_vv]; exact gC, trivial⟩
      (PostB (ctxH C H)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu veParams _ rfl hlk)
        (ve_spec C hok hc.ve coreWalkFuel coreWalkFuel_lt63 H c0 c s))
      (fun r w s1 H1 hp1 hw => ?_)
    subst hw
    have hp1' : H <+: H1 := hp1
    rcases r
    swap
    · refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      simp only [ite_true]
      exact specR_returnI _ 1 rfl (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine specR_ifI _ 1 (by simp +decide [veEqC, sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [Bool.false_eq_true, ite_false]
    have ret0 : ∀ (s2 : AState) (Γ : Env) (M : Mem), SpecR (σ := σ) (Inv (ctxH C H1) s2 Γ M (ctxLocals ++ aeLocals))
        (.return (.const 0)) s2 (pure false) (PostB (ctxH C H)) := fun s2 Γ M =>
      specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
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
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get_cons, Env.get, aeParams, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv aeC) (Enc.idxW c) (by decide)
      (by simp only [sev, sev_vv, Env.get_cons]; simp +decide; exact gC) ?_
    refine ConPanqueque.T.Big.specR_viewP c (by simp) (by simp +decide [Env.get_cons] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, aeParams, ctxEnv] <;> rfl) (by decide) (fun vc P hvc htnc hlenc => ?_)
    have hatc := tag_of_tagN htnc
    by_cases h4 : vc.tagN = 4
    swap
    · refine specR_ifI _ _ (gTag _ vc 4 (by decide) (by simp [Env.get_cons])) (fun h => absurd h (by simp [boolW, h4]))
        (fun _ => ?_)
      simp only [tagNo c vc 4 ETag.app rfl (by decide) hatc h4, Bool.false_eq_true, ite_false]
      exact ret0 _ _ _
    refine specR_ifI _ _ (gTag _ vc 4 (by decide) (by simp [Env.get_cons])) (fun _ => ?_)
      (fun h => absurd h (by simp [boolW, h4]))
    rcases vc with _ | _ | _ | _ | ⟨f, x⟩ | _ | _ | _ | _ | _ <;> simp [ENodeView.tagN] at h4
    have htc : c.tag = ETag.app := by rw [hatc]; rfl
    simp only [htc, beq_self_eq_true, ite_true]
    refine specR_runBind (show viewApp c s1 = .ok (some (f, x), s1) by
      rw [viewApp_run, WC.viewApp_of_view htc hvc]) ?_
    refine specR_loadI' aeF _ (P + 0) (P + BitVec.ofNat 64 0) (Enc.idxW f) (by decide)
      (by simp +decide [sev, Env.get_cons]) rfl
      (by simpa [encEView, Enc.encApp] using wordsAt_mem0 P (Enc.idxW f) [Enc.idxW x] []) ?_
    refine specR_loadI' aeX _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW x) (by decide)
      (by simp +decide [sev, Env.get_cons]) rfl
      (by simpa [encEView, Enc.encApp] using wordsAt_mem1 P (Enc.idxW f) (Enc.idxW x) [] []) ?_
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get_cons, Env.get, aeParams, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv aeF) (Enc.idxW f) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
    refine ConPanqueque.T.Big.specR_viewP f (by simp) (by simp +decide [Env.get_cons] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, aeParams, ctxEnv] <;> rfl) (by decide) (fun vf Pf hvf htnf hlenf => ?_)
    have hatf := tag_of_tagN htnf
    by_cases hf4 : vf.tagN = 4
    · refine specR_ifI _ _ (gTag _ vf 4 (by decide) (by simp [Env.get_cons])) (fun _ => ?_)
        (fun h => absurd h (by simp [boolW, hf4]))
      rcases vf with _ | _ | _ | _ | ⟨g, a⟩ | _ | _ | _ | _ | _ <;> simp [ENodeView.tagN] at hf4
      have htf : f.tag = ETag.app := by rw [hatf]; rfl
      simp only [htf, beq_self_eq_true, ite_true]
      refine specR_runBind (show viewApp f s1 = .ok (some (g, a), s1) by
        rw [viewApp_run, WC.viewApp_of_view htf hvf]) ?_
      refine specR_loadI' aeG _ (Pf + 0) (Pf + BitVec.ofNat 64 0) (Enc.idxW g) (by decide)
        (by simp +decide [sev, Env.get_cons]) rfl
        (by simpa [encEView, Enc.encApp] using wordsAt_mem0 Pf (Enc.idxW g) [Enc.idxW a] _) ?_
      refine specR_loadI' aeA _ (Pf + 8) (Pf + BitVec.ofNat 64 8) (Enc.idxW a) (by decide)
        (by simp +decide [sev, Env.get_cons]) rfl
        (by simpa [encEView, Enc.encApp] using wordsAt_mem1 Pf (Enc.idxW g) (Enc.idxW a) [] _) ?_
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get_cons, Env.get, aeParams, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv aeG) (Enc.idxW g) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
      refine ConPanqueque.T.Big.specR_viewP g (by simp) (by simp +decide [Env.get_cons] <;> rfl)
        (by simp +decide [Env.get_cons, Env.get, aeParams, ctxEnv] <;> rfl) (by decide) (fun vg Pg hvg htng hleng => ?_)
      have hatg := tag_of_tagN htng
      by_cases hg3 : vg.tagN = 3
      swap
      · refine specR_ifI _ _ (gTag _ vg 3 (by decide) (by simp [Env.get_cons])) (fun h => absurd h (by simp [boolW, hg3]))
          (fun _ => ?_)
        simp only [tagNo g vg 3 ETag.const rfl (by decide) hatg hg3, Bool.false_eq_true, ite_false]
        exact ret0 _ _ _
      refine specR_ifI _ _ (gTag _ vg 3 (by decide) (by simp [Env.get_cons])) (fun _ => ?_)
        (fun h => absurd h (by simp [boolW, hg3]))
      rcases vg with _ | _ | _ | ⟨nm, us⟩ | _ | _ | _ | _ | _ | _ <;> simp [ENodeView.tagN] at hg3
      have htg : g.tag = ETag.const := by rw [hatg]; rfl
      simp only [htg, beq_self_eq_true, ite_true]
      refine specR_runBind (show viewConst g s1 = .ok (some (nm, us), s1) by
        rw [WC.viewConst_run, WC.viewConst_of_view htg hvg]) ?_
      refine specR_loadI' aeN _ (Pg + 0) (Pg + BitVec.ofNat 64 0) (Enc.idxW nm) (by decide)
        (by simp +decide [sev, Env.get_cons]) rfl
        (List.mem_append_left _ (by have := wordsAt_mem0 Pg (Enc.idxW nm) [Enc.idxW us] []; simpa [encEView, Enc.encConst] using this)) ?_
      refine specR_loadI' aeU _ (Pg + 8) (Pg + BitVec.ofNat 64 8) (Enc.idxW us) (by decide)
        (by simp +decide [sev, Env.get_cons]) rfl
        (List.mem_append_left _ (by have := wordsAt_mem1 Pg (Enc.idxW nm) (Enc.idxW us) [] []; simpa [encEView, Enc.encConst] using this)) ?_
      simp only []
      exact aeArm_spec ra C hok hf hc hA es ob fe hfe n ih' H H1 hp1' (btabAt_mono hT hp1') s1 _ _ c0 a nm us "optParam" "autoParam" 2 (by decide) aeA
        (Or.inl rfl) (by decide) (by decide) (by simp +decide [Env.get_cons]) (by simp [Env.get_cons])
        (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]; exact gS) (by simp +decide [Env.get_cons]; exact gFu)
        (by simp +decide [Env.get_cons, Env.get, aeParams, ctxEnv] <;> rfl)
        (by simp +decide [Env.get_cons, Env.get, aeParams, ctxEnv] <;> rfl)
        (by simp +decide [Env.get_cons]; exact gBt)
    · refine specR_ifI _ _ (gTag _ vf 4 (by decide) (by simp [Env.get_cons])) (fun h => absurd h (by simp [boolW, hf4]))
        (fun _ => ?_)
      simp only [tagNo f vf 4 ETag.app rfl (by decide) hatf hf4, Bool.false_eq_true, ite_false]
      by_cases hf3 : vf.tagN = 3
      swap
      · refine specR_ifI _ _ (gTag _ vf 3 (by decide) (by simp [Env.get_cons])) (fun h => absurd h (by simp [boolW, hf3]))
          (fun _ => ?_)
        simp only [tagNo f vf 3 ETag.const rfl (by decide) hatf hf3, Bool.false_eq_true, ite_false]
        exact ret0 _ _ _
      refine specR_ifI _ _ (gTag _ vf 3 (by decide) (by simp [Env.get_cons])) (fun _ => ?_)
        (fun h => absurd h (by simp [boolW, hf3]))
      rcases vf with _ | _ | _ | ⟨nm, us⟩ | _ | _ | _ | _ | _ | _ <;> simp [ENodeView.tagN] at hf3
      have htf : f.tag = ETag.const := by rw [hatf]; rfl
      simp only [htf, beq_self_eq_true, ite_true]
      refine specR_runBind (show viewConst f s1 = .ok (some (nm, us), s1) by
        rw [WC.viewConst_run, WC.viewConst_of_view htf hvf]) ?_
      refine specR_loadI' aeN _ (Pf + 0) (Pf + BitVec.ofNat 64 0) (Enc.idxW nm) (by decide)
        (by simp +decide [sev, Env.get_cons]) rfl
        (by simpa [encEView, Enc.encConst] using wordsAt_mem0 Pf (Enc.idxW nm) [Enc.idxW us] _) ?_
      refine specR_loadI' aeU _ (Pf + 8) (Pf + BitVec.ofNat 64 8) (Enc.idxW us) (by decide)
        (by simp +decide [sev, Env.get_cons]) rfl
        (by simpa [encEView, Enc.encConst] using wordsAt_mem1 Pf (Enc.idxW nm) (Enc.idxW us) [] _) ?_
      simp only []
      exact aeArm_spec ra C hok hf hc hA es ob fe hfe n ih' H H1 hp1' (btabAt_mono hT hp1') s1 _ _ c0 x nm us "outParam" "semiOutParam" 1 (by decide) aeX
        (Or.inr rfl) (by decide) (by decide) (by simp +decide [Env.get_cons]) (by simp [Env.get_cons])
        (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]; exact gS) (by simp +decide [Env.get_cons]; exact gFu)
        (by simp +decide [Env.get_cons, Env.get, aeParams, ctxEnv] <;> rfl)
        (by simp +decide [Env.get_cons, Env.get, aeParams, ctxEnv] <;> rfl)
        (by simp +decide [Env.get_cons]; exact gBt)

end

end ConPanqueque.T.Ind
