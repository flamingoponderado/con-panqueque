import ConPanqueque.T.Ind.NestFields

/-!
# `replaceApps` at `nestCanonSub`: whole member applications abstracted to the canonical holes

`phApp?` (a constant applied to exactly the placeholder variables), `nestCanonSub` (a member at the block's levels
to its hole `fvar (n + m) : Sort 0`).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def phqB := ofString "phq_b"
def phqE := ofString "phq_e"
def phqN := ofString "phq_n"
def phqC := ofString "phq_c"
def phqU := ofString "phq_u"
def phqF := ofString "phq_f"
def phqA := ofString "phq_a"
def phqI := ofString "phq_i"
def phqR := ofString "phq_r"
def fPhApp := ofString "phApp"

def phqParams : List MlS := [phqB, phqE, phqN]
def phqLocals : List MlS := gaaLocals ++ [phqC, phqU, phqF, phqA, phqI, phqR]

def phqRet0 : ProgHOL 64 := .return (.const 0)

def phqIdx : ProgHOL 64 :=
  .ite (.cmp .equal (vv phqI) (.op .add [vv phqB, .op .sub [vv phqN, .const 1]]))
    (.seq (.call (some (some (.local, phqR), none)) fPhApp [vv phqB, vv phqF, .op .sub [vv phqN, .const 1]])
      (.return (vv phqR)))
    phqRet0

def phqBody (C : Ctx) : ProgHOL 64 := prologue phqLocals
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv phqE)) (.seq eViewP
  (.ite (.cmp .equal (vv phqN) (.const 0))
    (.ite (.cmp .equal (vv lDg) (.const 3))
      (.seq (.assign .local phqC (.load .one (vv lRp)))
      (.seq (.assign .local phqU (.load .one (.op .add [vv lRp, .const 8])))
        (alloc2 C phqR (vv phqC) (vv phqU) (.return (vv phqR)))))
      phqRet0)
    (.ite (.cmp .equal (vv lDg) (.const 4))
      (.seq (.assign .local phqF (.load .one (vv lRp)))
      (.seq (.assign .local phqA (.load .one (.op .add [vv lRp, .const 8])))
      (.seq (.assign .local lDh (vv phqA)) (.seq eViewP
      (.ite (.cmp .equal (vv lDg) (.const 1))
        (.ite (.cmp .equal (vv lRn) (.const 1)) (.seq (.assign .local phqI (.const 0)) phqIdx)
          (.ite (.cmp .equal (vv lRn) (.const 2))
            (.seq (.assign .local phqI (.load .one (.op .add [vv lRp, .const 8]))) phqIdx) phqRet0))
        phqRet0)))))
      phqRet0)))))

structure PHQCodes (C : Ctx) : Prop where
  self : C.code.lookup fPhApp = some (phqParams.map (fun p => (p, ShapeHOL.one)), phqBody C, .one)

section
variable {σ : Type}

theorem phq_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ phqLocals → (ctxEnv C ++ phqParams.zip vals).get x = none :=
  Knot.params_none C phqLocals phqParams vals (by decide) (by decide)

/-- An optional `(name, levels)` pair: `0`, or a cell `[name, levels]`. -/
def PairRep (C : Ctx) (H : List (BitVec 64)) (o : Option (NIdx × LsIdx)) (w : BitVec 64) : Prop :=
  match o with
  | none => w = 0
  | some (c, us) => ∃ oc, w = cellA C oc ∧ H[oc]? = some (Enc.idxW c) ∧ H[oc + 1]? = some (Enc.idxW us)

theorem pairRep_mono {C : Ctx} {H H' : List (BitVec 64)} (hp : H <+: H') :
    ∀ {o : Option (NIdx × LsIdx)} {w : BitVec 64}, PairRep C H o w → PairRep C H' o w
  | none, _, h => h
  | some _, _, ⟨oc, h1, h2, h3⟩ => ⟨oc, h1, get_prefix h2 hp, get_prefix h3 hp⟩

def PostPHQ (C : Ctx) (o : Option (NIdx × LsIdx)) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ PairRep C H' o w ∧ SR (ctxH C H') s' st

theorem postPHQ_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostPHQ C a w s' st → PostPHQ C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, h1, hs⟩ => ⟨H', hp, h1, sr_of_eq hs rfl rfl rfl rfl⟩

theorem tagN_ne_w (v : ENodeView) (k : Nat) (hk : k < 16) (h : v.tagN ≠ k) :
    BitVec.ofNat 64 v.tagN ≠ BitVec.ofNat 64 k := by
  have htb : v.tagN < 16 := by cases v <;> simp [ENodeView.tagN]
  intro e; have := congrArg BitVec.toNat e; simp at this; omega

set_option maxHeartbeats 8000000 in
/-- **`phApp?`**. -/
theorem phq_spec (C : Ctx) (hok : CtxOK C) (hc : PHQCodes C) (b : Nat) :
    ∀ n (e : EIdx) (H : List (BitVec 64)) (s : AState), b + n < 2 ^ 64 →
      SpecR (σ := σ) (Pre (ctxH C H) s (phqParams.zip [BitVec.ofNat 64 b, Enc.idxW e, BitVec.ofNat 64 n])) (phqBody C) s
        (phApp? b e n) (PostPHQ (ctxH C H)) := by
  intro n
  induction n with
  | zero =>
    intro e H s hb
    refine specR_prologue (postPHQ_locals _) (phq_none _ _) ?_
    rw [phApp?]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, phqParams, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv phqE) (Enc.idxW e) (by decide) (by simp +decide [Env.get_cons, Env.get, phqParams, ctxEnv]) ?_
    refine ConPanqueque.T.Big.specR_viewP e (by simp) (by simp +decide [Env.get_cons, Env.get, phqParams, ctxEnv] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, phqParams, ctxEnv] <;> rfl) (by decide) (fun v P hv htn hlen => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, phqParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    by_cases h3 : v.tagN = 3
    · obtain ⟨c, us, rfl⟩ : ∃ c us, v = .const c us := by cases v <;> simp [ENodeView.tagN] at h3 ⊢
      have htg : e.tag = ETag.const := by
        have : (Idx.tag e).toNat = 3 := by rw [← htn]; rfl
        simp [ETag.const]; exact UInt32.toNat_inj.mp (by simpa using this)
      rw [if_pos (by simp [htg])]
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_runBind (show ConRon.Arena.viewConst e s = .ok (some (c, us), s) by
        rw [WC.viewConst_run, WC.viewConst_of_view htg hv]) ?_
      dsimp only
      refine specR_loadI' phqC (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW c) (by decide) (by simp [sev, Env.get_cons]) (by simp)
        (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW c) [Enc.idxW us] []) ?_
      refine specR_loadI' phqU _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW us) (by decide) (by simp +decide [sev, Env.get_cons]) rfl
        (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW c) (Enc.idxW us) [] []) ?_
      refine specR_alloc2I (ctxOK_H hok H) phqR (vv phqC) (vv phqU) (Enc.idxW c) (Enc.idxW us) (by decide)
        (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons]) (fun H2 ws hp2 hws => ?_)
      obtain ⟨g0, g1⟩ := img2_get H2 ws (Enc.idxW c) (Enc.idxW us) hws
      have h2 := img2_prefix H2 ws (Enc.idxW c) (Enc.idxW us) hws
      exact specR_returnI (vv phqR) (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht =>
        ⟨_, (hp2 : H <+: H2).trans h2, ⟨H2.length, rfl, g0, g1⟩, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · have htg : ¬ (e.tag == ETag.const) = true := by
        intro e'; apply h3; rw [htn]; simp [ETag.const] at e'; rw [e']; rfl
      rw [if_neg htg]
      exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact tagN_ne_w v 3 (by decide) h3)
        (fun h => absurd rfl h) (fun _ => specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl,
          sr_of_eq ht.sr rfl rfl rfl rfl⟩))
  | succ n ih =>
    intro e H s hb
    refine specR_prologue (postPHQ_locals _) (phq_none _ _) ?_
    rw [phApp?]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, phqParams, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv phqE) (Enc.idxW e) (by decide) (by simp +decide [Env.get_cons, Env.get, phqParams, ctxEnv]) ?_
    refine ConPanqueque.T.Big.specR_viewP e (by simp) (by simp +decide [Env.get_cons, Env.get, phqParams, ctxEnv] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, phqParams, ctxEnv] <;> rfl) (by decide) (fun v P hv htn hlen => ?_)
    have hne : BitVec.ofNat 64 (n + 1) ≠ 0#64 := ofNat_ne_zero (n + 1) (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, phqParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun h => absurd rfl h) (fun _ => ?_)
    by_cases h4 : v.tagN = 4
    swap
    · have htg : ¬ (e.tag == ETag.app) = true := by
        intro e'; apply h4; rw [htn]; simp [ETag.app] at e'; rw [e']; rfl
      rw [if_neg htg]
      exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact tagN_ne_w v 4 (by decide) h4)
        (fun h => absurd rfl h) (fun _ => specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl,
          sr_of_eq ht.sr rfl rfl rfl rfl⟩))
    obtain ⟨f, a, rfl⟩ : ∃ f a, v = .app f a := by cases v <;> simp [ENodeView.tagN] at h4 ⊢
    have htg : e.tag = ETag.app := by
      have : (Idx.tag e).toNat = 4 := by rw [← htn]; rfl
      simp [ETag.app]; exact UInt32.toNat_inj.mp (by simpa using this)
    rw [if_pos (by simp [htg])]
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_runBind (show ConRon.Arena.viewApp e s = .ok (some (f, a), s) by
      rw [WC.viewApp_run, WC.viewApp_of_view htg hv]) ?_
    dsimp only
    refine specR_loadI' phqF (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW f) (by decide) (by simp [sev, Env.get_cons]) (by simp)
      (by simpa [encEView, Enc.encApp] using wordsAt_mem0 P (Enc.idxW f) [Enc.idxW a] []) ?_
    refine specR_loadI' phqA _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW a) (by decide) (by simp +decide [sev, Env.get_cons]) rfl
      (by simpa [encEView, Enc.encApp] using wordsAt_mem1 P (Enc.idxW f) (Enc.idxW a) [] []) ?_
    refine specR_assignI lDh (vv phqA) (Enc.idxW a) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
    refine ConPanqueque.T.Big.specR_viewP a (by simp) (by simp +decide [Env.get_cons, Env.get, phqParams, ctxEnv] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, phqParams, ctxEnv] <;> rfl) (by decide) (fun v2 P2 hv2 htn2 hlen2 => ?_)
    by_cases h1 : v2.tagN = 1
    swap
    · have htg1 : ¬ (a.tag == ETag.fvar) = true := by
        intro e'; apply h1; rw [htn2]; simp [ETag.fvar] at e'; rw [e']; rfl
      rw [if_neg htg1]
      exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact tagN_ne_w v2 1 (by decide) h1)
        (fun h => absurd rfl h) (fun _ => specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl,
          sr_of_eq ht.sr rfl rfl rfl rfl⟩))
    obtain ⟨i, ty, rfl⟩ : ∃ i ty, v2 = .fvar i ty := by cases v2 <;> simp [ENodeView.tagN] at h1 ⊢
    have htg1 : a.tag = ETag.fvar := by
      have : (Idx.tag a).toNat = 1 := by rw [← htn2]; rfl
      simp [ETag.fvar]; exact UInt32.toNat_inj.mp (by simpa using this)
    rw [if_pos (by simp [htg1])]
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_runBind (ExA.viewFVarIdx_run a (by rw [htg1]; rfl) s _ hv2) ?_
    simp only [projFVarIdx]
    have hlen1 : (encEView (.fvar i ty)).length = 1 + (Enc.limbs i).length := by simp [encEView, Enc.encFVar]; omega
    -- the index check and the recursive call, at a small index
    have hidx : ∀ (Γ : Env) (M : Mem), i < 2 ^ 64 → Γ.get phqI = some (BitVec.ofNat 64 i) →
        Γ.get phqB = some (BitVec.ofNat 64 b) → Γ.get phqN = some (BitVec.ofNat 64 (n + 1)) →
        Γ.get phqF = some (Enc.idxW f) →
        SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ phqLocals)) phqIdx s
          (if (i == b + n) = true then phApp? b f n else pure none) (PostPHQ (ctxH C H)) := by
      intro Γ M hi gI gB gN gF
      unfold phqIdx
      have hbn : BitVec.ofNat 64 b + (BitVec.ofNat 64 (n + 1) - 1#64) = BitVec.ofNat 64 (b + n) := by
        rw [show BitVec.ofNat 64 (n + 1) - 1#64 = BitVec.ofNat 64 n from ofNat_succ_sub_one n, BitVec.ofNat_add_ofNat]
      by_cases hib : i = b + n
      · subst hib
        rw [if_pos (by simp)]
        refine specR_ifI _ 1 (by simp only [sev, sev_vv]; simp +decide [gI, gB, gN, hbn, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun h => absurd h (by decide))
        refine specR_congr (m' := phApp? b f n >>= fun r => pure r) (by simp) ?_
        refine specR_callNIH (C := ctxH C H) phqR fPhApp phqParams [vv phqB, vv phqF, .op .sub [vv phqN, .const 1]] (phqBody C)
          [BitVec.ofNat 64 b, Enc.idxW f, BitVec.ofNat 64 n] (by decide) rfl (by decide) hc.self
          ⟨by simp [sev, gB], by simp [sev, gF], by simp only [sev, sev_vv]; simp [gN]; exact ofNat_succ_sub_one n, trivial⟩
          (PostPHQ (ctxH C H)) (fun o w _ H' => PairRep C H' o w)
          (fun o w s' st ⟨H', hp', h1, hsr⟩ => ⟨H', hp', h1, hsr⟩)
          (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu phqParams _ rfl hlk) (ih f H s (by omega)))
          (fun o w s1 H1 hp1 hr => ?_)
        exact specR_returnI _ w (by simp [sev, Env.get_cons]) (fun t ht => ⟨H1, hp1, hr, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      · rw [if_neg (by simpa using hib)]
        have hw : BitVec.ofNat 64 i ≠ BitVec.ofNat 64 (b + n) := by
          intro e'; apply hib; have := congrArg BitVec.toNat e'; simp at this; omega
        exact specR_ifI _ 0 (by simp only [sev, sev_vv]; simp +decide [gI, gB, gN, hbn, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hw])
          (fun h => absurd rfl h) (fun _ => specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl,
            sr_of_eq ht.sr rfl rfl rfl rfl⟩))
    by_cases i0 : i = 0
    · have hlim : (Enc.limbs i).length = 0 := by subst i0; simp [Enc.limbs]
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hlen1, hlim, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun hw => absurd hw (by decide))
      refine specR_assignI phqI (.const 0) (BitVec.ofNat 64 i) (by decide) (by rw [i0]; rfl) ?_
      exact hidx _ _ (by omega) (by simp [Env.get_cons]) (by simp +decide [Env.get_cons, Env.get, phqParams, ctxEnv])
        (by simp +decide [Env.get_cons, Env.get, phqParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, phqParams, ctxEnv])
    by_cases ib : i < 2 ^ 64
    · have hl : Enc.limbs i = [BitVec.ofNat 64 i] := by rw [limbs_small i ib]; simp [i0]
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hlen1, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun hw => absurd rfl hw) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hlen1, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun hw => absurd hw (by decide))
      refine specR_loadI' phqI _ (P2 + 8) (P2 + BitVec.ofNat 64 8) (BitVec.ofNat 64 i) (by decide)
        (by simp +decide [sev, Env.get_cons]) rfl
        (by have := wordsAt_mem1 P2 (Enc.idxW ty) (BitVec.ofNat 64 i) [] (M := [])
            simp [encEView, Enc.encFVar, hl] at this ⊢; exact Or.inl this) ?_
      exact hidx _ _ ib (by simp [Env.get_cons]) (by simp +decide [Env.get_cons, Env.get, phqParams, ctxEnv])
        (by simp +decide [Env.get_cons, Env.get, phqParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, phqParams, ctxEnv])
    have hge : 2 ≤ (Enc.limbs i).length := by
      have := (Big.limbs_length_lt_iff i 1).not.mpr (by simp [Big.B]; omega); omega
    have hsh' : 1 + (Enc.limbs i).length < 2 ^ 61 := by rw [← hlen1]; exact hlen2
    have hn1 : BitVec.ofNat 64 (1 + (Enc.limbs i).length) ≠ 1#64 := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    have hn2 : BitVec.ofNat 64 (1 + (Enc.limbs i).length) ≠ 2#64 := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hlen1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hn1)
      (fun hw => absurd rfl hw) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hlen1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hn2)
      (fun hw => absurd rfl hw) (fun _ => ?_)
    rw [if_neg (by simp; omega)]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## `nestCanonSub` and `appHole?` -/

def ncsMs := ofString "ncs_ms"
def ncsUs := ofString "ncs_us"
def ncsN := ofString "ncs_n"
def ncsC := ofString "ncs_c"
def ncsV := ofString "ncs_v"
def ncsK := ofString "ncs_k"
def ncsX := ofString "ncs_x"
def ncsM := ofString "ncs_m"
def ncsZ := ofString "ncs_z"
def ncsS := ofString "ncs_s"
def ncsF := ofString "ncs_f"
def fNcs := ofString "nestCanonSub"

def ncsParams : List MlS := [ncsMs, ncsUs, ncsN, ncsC, ncsV]
def ncsLocals : List MlS := [ncsK, ncsX, ncsM, ncsZ, ncsS, ncsF]

def ncsBody (C : Ctx) : ProgHOL 64 := prologue ncsLocals
  (.ite (.cmp .equal (vv ncsV) (vv ncsUs))
    (.seq (.assign .local ncsK (.load .one (vv ncsMs)))
    (.seq (.call (some (some (.local, ncsX), none)) fMemFindIdx [vv ncsMs, vv ncsC, .const 0, vv ncsK])
    (.ite (.cmp .equal (vv ncsX) (.const 0)) (.return (.const 0))
      (.seq (.assign .local ncsM (.op .sub [vv ncsX, .const 1]))
      (.seq (.assign .local ncsZ (.load .one (.const (ecell C (C.PO + pinCount + 1)))))
      (.seq (.call (some (some (.local, ncsS), none)) fInternSort [vv ncsZ])
      (.seq (.call (some (some (.local, ncsF), none)) fInternFVar [vv ncsS, .op .add [vv ncsN, vv ncsM]])
        (.return (.op .add [vv ncsF, .const 1])))))))))
    (.return (.const 0)))

structure NCSCodes (C : Ctx) : Prop where
  mfi : C.code.lookup fMemFindIdx = some (mfiParams.map (fun p => (p, ShapeHOL.one)), mfiBody, .one)
  srt : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one)
  fv : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one)
  self : C.code.lookup fNcs = some (ncsParams.map (fun p => (p, ShapeHOL.one)), ncsBody C, .one)

section
variable {σ : Type}

theorem ncs_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ncsLocals → (ctxEnv C ++ ncsParams.zip vals).get x = none :=
  Knot.params_none C ncsLocals ncsParams vals (by decide) (by decide)

/-- **`nestCanonSub`** at the members' names. -/
theorem ncs_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : NCSCodes C)
    (ms : List MemberShape) (om : Nat) (hml : ms.length < 2 ^ 59) (us : LsIdx) (n : Nat) (hn : n < 2 ^ 62)
    (c : NIdx) (v : LsIdx) (H : List (BitVec 64)) (hM : PtrsRep C H om (MemberRep C H) ms) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (ncsParams.zip [cellA C om, Enc.idxW us, BitVec.ofNat 64 n, Enc.idxW c,
      Enc.idxW v])) (ncsBody C) s (nestCanonSub (ms.map (·.cvT.name)) us n c v) (PostOE (ctxH C H)) := by
  refine specR_prologue (postOE_locals _) (ncs_none _ _) ?_
  rw [nestCanonSub]
  by_cases hv : v = us
  swap
  · rw [if_neg (by simpa using hv)]
    have hw : Enc.idxW v ≠ Enc.idxW us := fun e => hv (Enc.idxW_inj e)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get, ncsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hw])
      (fun h => absurd rfl h) (fun _ => specR_returnI _ 0 rfl (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩))
  subst hv
  rw [if_pos (by simp)]
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ncsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun _ => ?_) (fun h => absurd h (by decide))
  refine UD.specR_heapLoadI' (C := ctxH C H) ncsK (vv ncsMs) om _ hM.1 (by decide)
    (by simp +decide [sev, Env.get, ncsParams, ctxEnv]; rfl) ?_
  have hfi : (ms.map (·.cvT.name)).findIdx? (· == c) =
      (((ms.map (·.cvT.name)).drop 0).findIdx? (· == c)).map (· + 0) := by simp
  rw [hfi]
  refine specR_pureBind ((((ms.map (·.cvT.name)).drop 0).findIdx? (· == c)).map (· + 0)) ?_
  refine specR_callNIM ncsX fMemFindIdx mfiParams [vv ncsMs, vv ncsC, .const 0, vv ncsK] mfiBody
    [cellA C om, Enc.idxW c, BitVec.ofNat 64 0, BitVec.ofNat 64 ms.length] (by decide) rfl (by decide) hc.mfi
    ⟨(by simp +decide [sev, Env.get_cons, Env.get, ncsParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, ncsParams, ctxEnv]), rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (fun a w s' st => (pure ((((ms.map (·.cvT.name)).drop 0).findIdx? (· == c)).map (· + 0)) : AM (Option Nat)) s =
      .ok (a, s') ∧ PostON (ctxH C H) a w s' st) (fun _ _ _ _ h => h.2.2.2)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu mfiParams _ rfl hlk)
      (mfi_spec C hok hc.mfi ms c om H hM hml _ 0 s rfl (by omega))))
    (fun a w s2 st ⟨hrun, hw, hb, _⟩ => ?_)
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
  obtain ⟨hra, hs2⟩ := hrun
  subst hw; subst hs2
  rw [hra]
  rcases a with _ | m
  · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, optNatW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_returnI _ 0 rfl (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)) (fun h => absurd h (by decide))
  have hml' : m < ms.length := by
    have h1 : ((ms.map (·.cvT.name)).drop 0).findIdx? (· == c) = some m := by
      have := hra; simp only [Option.map_eq_some_iff] at this; obtain ⟨a, ha, he⟩ := this; simp at he; rw [← he]; exact ha
    have := List.findIdx?_eq_some_iff_getElem.mp h1
    obtain ⟨hlt, -⟩ := this; simpa using hlt
  have hnt : BitVec.ofNat 64 (m + 1) ≠ 0#64 := by intro e; have := congrArg BitVec.toNat e; simp at this; omega
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, optNatW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hnt)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI ncsM _ (BitVec.ofNat 64 m) (by decide)
    (by simp +decide [sev, Env.get_cons, optNatW]; exact word_sub_eq (m + 1) 1 (by omega) (by omega)) ?_
  simp only [zeroLevel, bind_assoc]
  have hokH := ctxOK_H hok H
  refine specR_pinXI hokH pinZeroLevel 1 C.pins.zeroLevel _ (fun s hp => pinZeroLevel_run hokH hp)
    (pin_zeroLevel_cell hokH) ncsZ (by decide) ?_
  refine ILP.callE_spec ncsS fInternSort [lEu] [vv ncsZ] sortBody [Enc.idxW C.pins.zeroLevel] (by decide) rfl
    (by decide) hc.srt ⟨by simp [sev, Env.get_cons]; rfl, trivial⟩
    (sort_body_spec ra (ctxH C H) hokH s C.pins.zeroLevel) (fun s0 s1 => ?_)
  refine ILP.specR_internFVarI ra hokH hc.fv ncsF (vv ncsS) (.op .add [vv ncsN, vv ncsM]) s0 (n + m) (by omega) (by decide)
    (by simp [sev, Env.get_cons]) (by simp +decide [sev, Env.get_cons, Env.get, ncsParams, ctxEnv]; rw [BitVec.ofNat_add_ofNat])
    (fun r s3 => ?_)
  exact specR_returnI _ (Enc.idxW r + 1) (by simp [sev, Env.get_cons]) (fun t ht => ⟨rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

def ahB := ofString "ah_b"
def ahE := ofString "ah_e"
def ahN := ofString "ah_n"
def ahMs := ofString "ah_ms"
def ahUs := ofString "ah_us"
def ahP := ofString "ah_p"
def ahC := ofString "ah_c"
def ahV := ofString "ah_v"
def ahR := ofString "ah_r"
def fAppHole := ofString "appHole"

def ahParams : List MlS := [ahB, ahE, ahN, ahMs, ahUs]
def ahLocals : List MlS := [ahP, ahC, ahV, ahR]

def ahBody : ProgHOL 64 := prologue ahLocals
  (.seq (.call (some (some (.local, ahP), none)) fPhApp [vv ahB, vv ahE, vv ahN])
  (.ite (.cmp .equal (vv ahP) (.const 0)) (.return (.const 0))
    (.seq (.assign .local ahC (.load .one (vv ahP)))
    (.seq (.assign .local ahV (.load .one (.op .add [vv ahP, .const 8])))
    (.seq (.call (some (some (.local, ahR), none)) fNcs [vv ahMs, vv ahUs, vv ahN, vv ahC, vv ahV])
      (.return (vv ahR)))))))

structure AHCodes (C : Ctx) : Prop where
  phq : PHQCodes C
  ncs : NCSCodes C
  self : C.code.lookup fAppHole = some (ahParams.map (fun p => (p, ShapeHOL.one)), ahBody, .one)

section
variable {σ : Type}

theorem ah_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ahLocals → (ctxEnv C ++ ahParams.zip vals).get x = none :=
  Knot.params_none C ahLocals ahParams vals (by decide) (by decide)

/-- An optional handle as `optWG idxW`, the heap extended. -/
def PostOEH (C : Ctx) (o : Option EIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ w = optWG Enc.idxW o ∧ SR (ctxH C H') s' st

theorem postOEH_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostOEH C a w s' st → PostOEH C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, h1, hs⟩ => ⟨H', hp, h1, sr_of_eq hs rfl rfl rfl rfl⟩

/-- **`appHole?`** at the members' names. -/
theorem ah_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : AHCodes C)
    (ms : List MemberShape) (om : Nat) (hml : ms.length < 2 ^ 59) (hM : PtrsRep C C.H om (MemberRep C C.H) ms)
    (us : LsIdx) (b n : Nat) (hb : b + n < 2 ^ 62) (e : EIdx) (H : List (BitVec 64)) (hp : C.H <+: H) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (ahParams.zip [BitVec.ofNat 64 b, Enc.idxW e, BitVec.ofNat 64 n, cellA C om,
      Enc.idxW us])) ahBody s (appHole? (ms.map (·.cvT.name)) us b n e) (PostOEH (ctxH C H)) := by
  refine specR_prologue (postOEH_locals _) (ah_none _ _) ?_
  rw [appHole?]
  refine specR_callNIH (C := ctxH C H) ahP fPhApp phqParams [vv ahB, vv ahE, vv ahN] (phqBody C)
    [BitVec.ofNat 64 b, Enc.idxW e, BitVec.ofNat 64 n] (by decide) rfl (by decide) hc.phq.self
    ⟨(by simp +decide [sev, Env.get_cons, Env.get, ahParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, ahParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, ahParams, ctxEnv]), trivial⟩
    (PostPHQ (ctxH C H)) (fun o w _ H' => PairRep C H' o w) (fun o w s' st ⟨H', hp', h1, hsr⟩ => ⟨H', hp', h1, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu phqParams _ rfl hlk) (phq_spec C hok hc.phq b n e H s (by omega)))
    (fun o w s1 H1 hp1 hr => ?_)
  have hp1' : H <+: H1 := hp1
  rcases o with _ | ⟨c, v⟩
  · simp only [PairRep] at hr; subst hr
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)) (fun h => absurd h (by decide))
  obtain ⟨oc, rfl, h0, h1⟩ := hr
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN => ?_)
  have hol : oc < H1.length := (List.getElem?_eq_some_iff.mp h0).1
  have hHN' : H1.length ≤ C.HN := hHN
  have hne : cellA C oc ≠ 0 := cellA_ne0 C hok oc (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine UD.specR_heapLoadI' (C := ctxH C H1) ahC (vv ahP) oc _ h0 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H1) ahV _ (oc + 1) _ h1 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C oc) ?_
  simp only
  refine specR_congr (m' := nestCanonSub (ms.map (·.cvT.name)) us n c v >>= fun r => pure r) (by simp) ?_
  have hM1 : PtrsRep C H1 om (MemberRep C H1) ms := ptrsRep_mono (hp.trans hp1') (fun _ _ => memberRep_mono (hp.trans hp1')) hM
  refine specR_callNIM ahR fNcs ncsParams [vv ahMs, vv ahUs, vv ahN, vv ahC, vv ahV] (ncsBody C)
    [cellA C om, Enc.idxW us, BitVec.ofNat 64 n, Enc.idxW c, Enc.idxW v] (by decide) rfl (by decide) hc.ncs.self
    ⟨by simp +decide [sev, Env.get_cons, Env.get, ahParams, ctxEnv], (by simp +decide [sev, Env.get_cons, Env.get, ahParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, ahParams, ctxEnv]), by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons], trivial⟩
    (PostOE (ctxH C H1)) (fun _ _ _ _ h => h.2)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ncsParams _ rfl hlk)
      (ncs_spec ra C hok hc.ncs ms om hml us n (by omega) c v H1 hM1 s1))
    (fun r w2 s2 st ⟨hw2, _⟩ => ?_)
  subst hw2
  exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨H1, hp1', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
