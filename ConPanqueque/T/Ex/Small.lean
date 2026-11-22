import ConPanqueque.T.Ex.BvarBound
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Small expression helpers

`hasFvarFast`, `looseBVarsBoundedFast` (the packed fields, or the memoized walks), and the telescope
helpers `piResult`, `lamBody`, `fvarTypeD`. Booleans are returned as the words `1`/`0`.
-/

namespace ConPanqueque.T.ExM
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExL ConPanqueque.T.ExF

section
variable {σ : Type}

/-- A Bool-returning function's post. -/
def PostB (C : Ctx) (b : Bool) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  w = (if b then 1 else 0) ∧ SR C s' st

theorem postB_locals (C : Ctx) : ∀ (a : Bool) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostB C a w s' st → PostB C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2⟩ => ⟨h1, sr_of_eq h2 rfl rfl rfl rfl⟩

/-- Binding the two parameters `(pFu, pH)` from the callee's locals. -/
theorem pre2 {C : Ctx} {s : AState} {u : PState σ} (hu : SR C s u) (x y : MlS) (vx vy : BitVec 64)
    (h1 : u.locals.lookup x = some (.val (.word vx))) (h2 : u.locals.lookup y = some (.val (.word vy))) :
    Pre C s [(x, vx), (y, vy)] u := ⟨hu, fun z w hz => by
  simp only [Env.get] at hz
  split at hz
  · rename_i e; subst e; simp at hz; subst hz; exact h1
  · split at hz
    · rename_i e; subst e; simp at hz; subst hz; exact h2
    · simp at hz⟩

end

/-! ## `hasFvarFast` -/

def fHasFvar := ofString "hasFvar"

def hasFvarBody : ProgHOL 64 :=
  prologue [lB] (.seq (.call (some (some (.local, lB), none)) fFvarB [vv pFu, vv pH])
    (.return (.cmp .notEqual (vv lB) (.const 0))))

theorem natW_eq_zero_iff (r : Nat) (hr : r < 2 ^ 63) : natW r = 0 ↔ r = 0 := by
  constructor
  · intro e; have := congrArg BitVec.toNat e; simp [natW] at this; omega
  · intro e; subst e; rfl

section
variable {σ : Type}

theorem hasFvar_spec (C : Ctx) (hok : CtxOK C) (hcF : CodesF C (bodyF C))
    (hfvb : C.code.lookup fFvarB = some ([(pFu, .one), (pH, .one)], fvbBody C, .one))
    (s : AState) (fuel : Nat) (e : EIdx) (hf : fuel < 2 ^ 64) :
    SpecR (Pre (σ := σ) C s [(pFu, BitVec.ofNat 64 fuel), (pH, Enc.idxW e)]) hasFvarBody s (hasFvarFast fuel e)
      (PostB C) := by
  refine specR_prologue (postB_locals C) (fun x hx => by simp at hx; subst hx; rfl) ?_
  unfold hasFvarFast
  refine specR_call2IM lB fFvarB pFu pH (by decide) _ _ (fvbBody C) (BitVec.ofNat 64 fuel) (Enc.idxW e) (by decide)
    hfvb (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (PostN C) (fun _ _ _ _ hp => hp.2.2)
    (fun u hu _ h1 h2 w hw => by subst hw; exact fvarB_spec C hok hcF s fuel e hf _ (pre2 hu _ _ _ _ h1 h2))
    (fun r w s' st hp => ?_)
  obtain ⟨rfl, hr, _⟩ := hp
  refine specR_returnI _ (if r != 0 then 1 else 0) ?_ (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  by_cases r0 : r = 0
  · subst r0; simp +decide [sev, natW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  · have : natW r ≠ 0 := fun x => r0 ((natW_eq_zero_iff r hr).mp x)
    simp +decide [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, r0]; exact this

end

/-! ## `looseBVarsBoundedFast` -/

def fLBB := ofString "looseBVarsBounded"
def pKb := ofString "kb"

def lbbBody : ProgHOL 64 :=
  prologue [lB] (.seq (.call (some (some (.local, lB), none)) ExB.fBvarB [vv pFu, vv pH])
    (.return (.cmp .notLower (vv pKb) (vv lB))))

section
variable {σ : Type}

theorem lbb_spec (C : Ctx) (hok : CtxOK C) (hcB : ExB.CodesB C (ExB.bodyB C))
    (hbvb : C.code.lookup ExB.fBvarB = some ([(pFu, .one), (pH, .one)], ExB.bvbBody C, .one))
    (s : AState) (fuel k : Nat) (e : EIdx) (hf : fuel < 2 ^ 64) (hk : k < 2 ^ 63) :
    SpecR (Pre (σ := σ) C s [(pFu, BitVec.ofNat 64 fuel), (pKb, BitVec.ofNat 64 k), (pH, Enc.idxW e)]) lbbBody s
      (looseBVarsBoundedFast fuel k e) (PostB C) := by
  refine specR_prologue (postB_locals C) (fun x hx => by simp at hx; subst hx; rfl) ?_
  unfold looseBVarsBoundedFast
  refine specR_call2IM lB ExB.fBvarB pFu pH (by decide) _ _ (ExB.bvbBody C) (BitVec.ofNat 64 fuel) (Enc.idxW e)
    (by decide) hbvb (by simp +decide [ctxEnv]) (by simp +decide [ctxEnv]) (PostN C) (fun _ _ _ _ hp => hp.2.2)
    (fun u hu _ h1 h2 w hw => by subst hw; exact ExB.bvarB_spec C hok hcB s fuel e hf _ (pre2 hu _ _ _ _ h1 h2))
    (fun r w s' st hp => ?_)
  obtain ⟨rfl, hr, _⟩ := hp
  refine specR_returnI _ (if decide (r ≤ k) then 1 else 0) ?_ (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  by_cases g : r ≤ k
  · have : ¬ BitVec.ofNat 64 k < BitVec.ofNat 64 r := fun x => absurd ((word_lt_iff k r (by omega) (by omega)).mp x) (by omega)
    simp +decide [sev, ctxEnv, natW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this, g]; omega
  · have : BitVec.ofNat 64 k < BitVec.ofNat 64 r := (word_lt_iff k r (by omega) (by omega)).mpr (by omega)
    simp +decide [sev, ctxEnv, natW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this, g]; omega

end

/-! ## `piResult` -/

def fPir := ofString "piResult"
def pKl := ofString "kl"

def pirCore : ProgHOL 64 :=
  .ite (.cmp .equal (vv pFu) (.const 0)) hang
    (.ite (tagIsE pH 6)
      (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
        (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
          (.seq (.call (some (some (.local, lY), none)) fPir [.op .sub [vv pFu, .const 1], vv lA2])
            (.return (vv lY)))))))
      (.return (vv pH)))

def pirBody : ProgHOL 64 := prologue inst1Locals pirCore

section
variable {σ : Type}

theorem params_none2 (va vb : BitVec 64) (C : Ctx) :
    ∀ x, x ∈ inst1Locals → (ctxEnv C ++ [(pFu, va), (pH, vb)]).get x = none := by
  intro x hx
  simp only [inst1Locals, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem params_none2k (va vb : BitVec 64) (C : Ctx) :
    ∀ x, x ∈ inst1Locals → (ctxEnv C ++ [(pKl, va), (pH, vb)]).get x = none := by
  intro x hx
  simp only [inst1Locals, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem params_none1h (vb : BitVec 64) (C : Ctx) :
    ∀ x, x ∈ inst1Locals → (ctxEnv C ++ [(pH, vb)]).get x = none := by
  intro x hx
  simp only [inst1Locals, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem pir_spec (C : Ctx) (hcode : C.code.lookup fPir = some ([(pFu, .one), (pH, .one)], pirBody, .one)) :
    ∀ n, n < 2 ^ 64 → ∀ (h : EIdx) (s : AState),
      SpecR (Pre (σ := σ) C s [(pFu, BitVec.ofNat 64 n), (pH, Enc.idxW h)]) pirBody s (piResult n h) (PostE C) := by
  intro n
  induction n with
  | zero =>
    intro _ h s
    refine specR_prologue (postE_locals C) (params_none2 _ _ C) ?_
    refine specR_ifI _ _ rfl (fun _ => specR_hangI) (fun hw => ?_)
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw
  | succ n ih =>
    intro hf h s
    refine specR_prologue (postE_locals C) (params_none2 _ _ C) ?_
    refine specR_ifI _ _ rfl (fun hw => ?_) (fun _ => ?_)
    · have := ofNat_ne_zero (n + 1) (by omega) hf
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw; exact absurd hw this
    unfold piResult
    refine specR_iteI (tagIsE pH 6) (tagW h 6) ?_ (by rw [tagW_iff h 6 (by decide) (by decide)]; simp [ETag.forallE])
      (fun hb => ?_) (fun _ => ?_)
    · simp +decide [sev, tagIsE, tagW, ctxEnv]
    · have h6 : h.tag = 6 := by simpa [ETag.forallE] using hb
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [ctxEnv]) ?_
      refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [ctxEnv]) ?_
      refine specR_viewXI ConRon.Arena.viewBind projBind h (fun vw hvw => viewBind_run h (Or.inr h6) s vw hvw)
        (by simp) (by simp +decide) (by simp +decide [ctxEnv]) (by decide) (fun vw P htg hsh => ?_)
      cases vw with
      | forallE ty b =>
        refine specR_loadI' lA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
          (wordsAt_mem1 _ _ _ _ _) ?_
        refine specR_congr (m' := piResult n b >>= fun a => pure a) (by simp [projBind]) ?_
        refine specR_call2IM lY fPir pFu pH (by decide) _ _ pirBody (BitVec.ofNat 64 (n + 1) - 1) (Enc.idxW b)
          (by decide) hcode (by simp +decide [sev, ctxEnv]) (by simp +decide) (PostE C) (fun _ _ _ _ hp => hp.2)
          (fun u hu _ h1 h2 w hw => by
            subst hw; rw [ofNat_succ_sub_one] at h1; exact ih (by omega) b s _ (pre2 hu _ _ _ _ h1 h2))
          (fun a w s' st hp => ?_)
        obtain ⟨rfl, _⟩ := hp
        exact specR_returnI (vv lY) (Enc.idxW a) (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      | lam ty b => simp [ENodeView.tagN, h6] at htg
      | _ => simp [ENodeView.tagN, h6] at htg
    · exact specR_returnI (vv pH) (Enc.idxW h) (by simp +decide [ctxEnv])
        (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## `lamBody` -/

def fLamB := ofString "lamBody"

def lambCore : ProgHOL 64 :=
  .ite (.cmp .equal (vv pKl) (.const 0)) (.return (vv pH))
    (.ite (tagIsE pH 5)
      (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
        (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
          (.seq (.call (some (some (.local, lY), none)) fLamB [.op .sub [vv pKl, .const 1], vv lA2])
            (.return (vv lY)))))))
      (.return (vv pH)))

def lambBody : ProgHOL 64 := prologue inst1Locals lambCore

section
variable {σ : Type}

theorem lamb_spec (C : Ctx) (hcode : C.code.lookup fLamB = some ([(pKl, .one), (pH, .one)], lambBody, .one)) :
    ∀ k, k < 2 ^ 64 → ∀ (h : EIdx) (s : AState),
      SpecR (Pre (σ := σ) C s [(pKl, BitVec.ofNat 64 k), (pH, Enc.idxW h)]) lambBody s (lamBody k h) (PostE C) := by
  intro k
  induction k with
  | zero =>
    intro _ h s
    refine specR_prologue (postE_locals C) (params_none2k _ _ C) ?_
    refine specR_ifI _ _ rfl (fun _ => ?_) (fun hw => ?_)
    · exact specR_returnI (vv pH) (Enc.idxW h) (by simp +decide [ctxEnv])
        (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw
  | succ k ih =>
    intro hf h s
    refine specR_prologue (postE_locals C) (params_none2k _ _ C) ?_
    refine specR_ifI _ _ rfl (fun hw => ?_) (fun _ => ?_)
    · have := ofNat_ne_zero (k + 1) (by omega) hf
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL] at hw; exact absurd hw this
    simp only [lamBody]
    refine specR_iteI (tagIsE pH 5) (tagW h 5) ?_ (by rw [tagW_iff h 5 (by decide) (by decide)]; simp [ETag.lam])
      (fun hb => ?_) (fun _ => ?_)
    · simp +decide [sev, tagIsE, tagW, ctxEnv]
    · have h5 : h.tag = 5 := by simpa [ETag.lam] using hb
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [ctxEnv]) ?_
      refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [ctxEnv]) ?_
      refine specR_viewXI ConRon.Arena.viewBind projBind h (fun vw hvw => viewBind_run h (Or.inl h5) s vw hvw)
        (by simp) (by simp +decide) (by simp +decide [ctxEnv]) (by decide) (fun vw P htg hsh => ?_)
      cases vw with
      | lam ty b =>
        refine specR_loadI' lA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev]) rfl
          (wordsAt_mem1 _ _ _ _ _) ?_
        refine specR_congr (m' := lamBody k b >>= fun a => pure a) (by simp [projBind]) ?_
        refine specR_call2IM lY fLamB pKl pH (by decide) _ _ lambBody (BitVec.ofNat 64 (k + 1) - 1) (Enc.idxW b)
          (by decide) hcode (by simp +decide [sev, ctxEnv]) (by simp +decide) (PostE C) (fun _ _ _ _ hp => hp.2)
          (fun u hu _ h1 h2 w hw => by
            subst hw; rw [ofNat_succ_sub_one] at h1; exact ih (by omega) b s _ (pre2 hu _ _ _ _ h1 h2))
          (fun a w s' st hp => ?_)
        obtain ⟨rfl, _⟩ := hp
        exact specR_returnI (vv lY) (Enc.idxW a) (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      | forallE ty b => simp [ENodeView.tagN, h5] at htg
      | _ => simp [ENodeView.tagN, h5] at htg
    · exact specR_returnI (vv pH) (Enc.idxW h) (by simp +decide [ctxEnv])
        (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## `fvarTypeD` -/

def fvtCore : ProgHOL 64 :=
  .ite (tagIsE pH 1)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP
      (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0]))) (.return (vv lA1))))))
    (.return (vv pH))

def fvtBody : ProgHOL 64 := prologue inst1Locals fvtCore

section
variable {σ : Type}

theorem viewFVarTy_run (h : EIdx) (h1 : h.tag = 1) (s : AState) (v : ENodeView)
    (hv : s.store.view h = some v) : ConRon.Arena.viewFVarTy h s = .ok (projFVarTy v, s) :=
  viewX_run ConRon.Arena.viewFVarTy (fun st h => st.viewFVarTy h) (fun _ _ => rfl) projFVarTy h
    (fun st => viewFVarTy_bind st h h1) s v hv

theorem fvt_spec (C : Ctx) (s : AState) (h : EIdx) :
    SpecR (Pre (σ := σ) C s [(pH, Enc.idxW h)]) fvtBody s (fvarTypeD h) (PostE C) := by
  refine specR_prologue (postE_locals C) (params_none1h _ C) ?_
  unfold fvarTypeD fvtCore
  refine specR_iteI (tagIsE pH 1) (tagW h 1) ?_ (by rw [tagW_iff h 1 (by decide) (by decide)]; simp [ETag.fvar])
    (fun hb => ?_) (fun _ => ?_)
  · simp +decide [sev, tagIsE, tagW, ctxEnv]
  · have h1 : h.tag = 1 := by simpa [ETag.fvar] using hb
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [ctxEnv]) ?_
    refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [ctxEnv]) ?_
    refine specR_viewXI ConRon.Arena.viewFVarTy projFVarTy h (fun vw hvw => viewFVarTy_run h h1 s vw hvw)
      (by simp) (by simp +decide) (by simp +decide [ctxEnv]) (by decide) (fun vw P htg hsh => ?_)
    cases vw with
    | fvar idx ty =>
      refine specR_loadI' lA1 _ (P + 0) (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp [sev]) rfl
        (wordsAt_mem0 _ _ _ _) ?_
      exact specR_returnI (vv lA1) (Enc.idxW ty) (by simp +decide) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    | _ => simp [ENodeView.tagN, h1] at htg
  · exact specR_returnI (vv pH) (Enc.idxW h) (by simp +decide [ctxEnv])
      (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.ExM
