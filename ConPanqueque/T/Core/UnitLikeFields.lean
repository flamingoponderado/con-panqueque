import ConPanqueque.T.Core.UnitLikeCode
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `unitLikeFields`

Each field binder is a proposition (`isPropType`) or unit-like (the loop, a hypothesis restricted to an invariant
`Q`), opened at a fresh variable before the next. Run-equation variants of the intern and instantiate calls carry
`Q` forward.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

section
variable {σ : Type}

theorem specR_internFVarR {β : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} (hok : CtxOK C)
    (hcode : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k : EIdx → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x : MlS) (e1 e2 : ExpHOL 64) (ty : EIdx) (idx : Nat)
    (hi : idx < 2 ^ 63) (hx : x ∈ D)
    (he1 : sev Γ e1 = some (Enc.idxW ty)) (he2 : sev Γ e2 = some (BitVec.ofNat 64 idx))
    (hk : ∀ h s', internFVarE idx ty s = .ok (h, s') → SpecR (Inv C s' ((x, Enc.idxW h) :: Γ) [] D) rest s' (k h) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) fInternFVar [e1, e2]) rest) s
      (internFVarE idx ty >>= k) R :=
  specR_call2I x fInternFVar lEty lIw (by decide) e1 e2 fvarBody (Enc.idxW ty) (BitVec.ofNat 64 idx) hx hcode he1 he2
    (fun a w s' st => internFVarE idx ty s = .ok (a, s') ∧ PostE C a w s' st) (fun _ _ _ _ hp => hp.2.2)
    (fun u hu h1 h2 v hv => by
      subst hv
      exact (specR_run (fvar_body_spec ra C hok s idx ty hi)) _ ⟨hu, fun y w hy => by
        simp only [Env.get] at hy
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact h1
        · split at hy
          · rename_i e; subst e; simp at hy; subst hy; exact h2
          · simp at hy⟩)
    (fun h w s' st hp => by obtain ⟨hr, rfl, _⟩ := hp; exact hk h s' hr)

theorem callE_specR {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM EIdx} {k : EIdx → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f : MlS) (ps : List MlS) (es : List (ExpHOL 64)) (B : ProgHOL 64) (vs : List (BitVec 64))
    (hnd : ps.Nodup) (hl : vs.length = ps.length)
    (hx : x ∈ D) (hC : C.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), B, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs)
    (hspec : SpecR (Pre (σ := σ) C s (ps.zip vs)) B s m (PostE C))
    (hk : ∀ h s', m s = .ok (h, s') → SpecR (Inv C s' ((x, Enc.idxW h) :: Γ) [] D) rest s' (k h) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f es) rest) s (m >>= k) R :=
  specR_callNIM x f ps es B vs hnd hl hx hC hes (fun a w s' st => m s = .ok (a, s') ∧ PostE C a w s' st)
    (fun _ _ _ _ hp => hp.2.2)
    (fun u hu _ hlk => fun w hw => by subst hw; exact (specR_run hspec) _ (pre_of_lookups hu ps vs hl hlk))
    (fun h w s' st hp => by obtain ⟨hr, rfl, _⟩ := hp; exact hk h s' hr)

end

structure UlfCodes (C : Ctx) : Prop where
  ipy : C.code.lookup fIpy = some (ipyParams.map (fun p => (p, ShapeHOL.one)), ipyBody C, .one)
  ipyc : IpyCodes C
  ull : C.code.lookup fUll = some (ullParams.map (fun p => (p, ShapeHOL.one)), ullBody, .one)
  fv : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one)
  i1 : C.code.lookup ExI.fInst1F = some ([pFu, pH, ExI.pV, ExI.pD].map (fun p => (p, ShapeHOL.one)), ExI.fastBody C, .one)
  i1c : ExI.Codes C (ExI.body C)
  self : C.code.lookup fUlf = some (ulfParams.map (fun p => (p, ShapeHOL.one)), ulfBody, .one)

section
variable {σ : Type}

theorem ulf_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (hc : UlfCodes C) (Q : AState → Prop) (F : Nat)
    (hQi : ∀ s1 d T b s2, Q s1 → isPropType (knot mode C n) d T s1 = .ok (b, s2) → Q s2)
    (hQf : ∀ s1 i ty h s2, Q s1 → internE (.fvar i ty) s1 = .ok (h, s2) → Q s2)
    (hQ1 : ∀ s1 fu e v d h s2, Q s1 → instantiate1Fast fu e v d s1 = .ok (h, s2) → Q s2)
    (hQl : ∀ s1 d T b s2, Q s1 → unitLikeLoop (knot mode C n) C.fe F d T s1 = .ok (b, s2) → Q s2)
    (hIO : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (inferIOE C fIOB) s1 ((knot mode C n).inferIO d' e')
      (PostK (ctxH C H)))
    (hW : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d' e')
      (PostK (ctxH C H)))
    (hLE : ∀ (H : List (BitVec 64)) s1 (u v : LIdx), C.H <+: H → (denoteL s1.store.ls u).isSome = true →
      (denoteL s1.store.ls v).isSome = true →
      SpecR (σ := σ) (Pre (ctxH C H) s1 [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s1 (lvlEq? u v)
        (LLeq.PostOB (ctxH C H)))
    (hUL : ∀ (H : List (BitVec 64)) s1 d T, C.H <+: H → Q s1 → d < 2 ^ 64 →
      SpecR (σ := σ) (Pre (ctxH C H) s1 (ullParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, BitVec.ofNat 64 F, Enc.idxW T]))
        ullBody s1 (unitLikeLoop (knot mode C n) C.fe F d T) (PostB (ctxH C H))) :
    ∀ (N d : Nat) (tele : EIdx) (H : List (BitVec 64)) (s : AState), C.H <+: H → Q s → N < 2 ^ 64 → d < 2 ^ 64 →
      SpecR (σ := σ) (Pre (ctxH C H) s (ulfParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, BitVec.ofNat 64 F,
        BitVec.ofNat 64 N, Enc.idxW tele])) ulfBody s
        (unitLikeFields (knot mode C n) (unitLikeLoop (knot mode C n) C.fe F) N d tele) (PostB (ctxH C H)) := by
  intro N
  induction N with
  | zero =>
    intro d tele H s hpH hq hN hd
    refine specR_prologue (postB_locals _) (Knot.params_none _ ulfLocals ulfParams _ (by decide) (by decide)) ?_
    rw [unitLikeFields]
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ulfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ N ih =>
    intro d tele H s hpH hq hN hd
    refine specR_prologue (postB_locals _) (Knot.params_none _ ulfLocals ulfParams _ (by decide) (by decide)) ?_
    have hne := ofNat_succ_ne N (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ulfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
    rw [unitLikeFields]
    refine Knot.specR_tagIteV ulfE tele 6 (by decide) (by decide) (by simp +decide [Env.get, ulfParams, ctxEnv]) (fun htg => ?_) (fun htg => ?_)
    swap
    · rw [if_neg (show ¬ (tele.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg)]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    rw [if_pos (show (tele.tag == ETag.forallE) = true by simp [htg, ETag.forallE])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv ulfE) (Enc.idxW tele) (by decide) (by simp +decide [Env.get, ulfParams, ctxEnv]) ?_
    refine specR_viewP (C := ctxH C H) tele (by simp) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
      (fun v P hv htn _ => ?_)
    have h6 : v.tagN = 6 := by rw [htn, htg]; rfl
    obtain ⟨dom, body, rfl⟩ : ∃ ty b, v = .forallE ty b := by cases v <;> simp [ENodeView.tagN] at h6 ⊢
    have hvb : s.store.viewBind tele = some (dom, body) := viewBind_of_view_forallE (by rw [htg]; rfl) hv
    refine specR_runBind (by rw [viewBind_run, hvb]) ?_
    dsimp only
    refine specR_loadI' ulfDm (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW dom) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW dom) [Enc.idxW body] []) ?_
    refine specR_loadI' ulfB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW body) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW dom) (Enc.idxW body) [] []) ?_
    refine specR_dropM ?_
    refine specR_callNIH (C := ctxH C H) ulfP fIpy ipyParams [vv kFu, vv kD, vv ulfDm] (ipyBody C)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW dom] (by decide) rfl (by decide) hc.ipy
      ⟨by simp +decide [Env.get, ulfParams, ctxEnv], by simp +decide [Env.get, ulfParams, ctxEnv], by simp, trivial⟩
      (fun b w s' st => isPropType (knot mode C n) d dom s = .ok (b, s') ∧ PostB (ctxH C H) b w s' st)
      (fun b w s' H' => isPropType (knot mode C n) d dom s = .ok (b, s') ∧ w = boolW b)
      (fun b w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hr, hw⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu ipyParams _ rfl hlk)
        (ipy_spec mode n C hok hc.ipyc s d dom (fun H' s' hp e' => hIO H' s' d e' hp) (fun H' s' hp e' => hW H' s' d e' hp)
          hLE H hpH)))
      (fun p w1 s1 H1 hp1 ⟨hr1, hw1⟩ => ?_)
    subst hw1
    have hq1 := hQi _ _ _ _ _ hq hr1
    rcases Bool.eq_false_or_eq_true p with rfl | rfl
    · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [↓reduceIte]
      by_cases hd2 : d < 2 ^ 62
      swap
      · have hl : ¬ (BitVec.ofNat 64 d < BitVec.ofNat 64 (2 ^ 62)) := by
          rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]; norm_num; omega
        exact specR_ifI _ 0 (by simp +decide [sev, Env.get, ulfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; first | exact hl | (rw [Nat.mod_eq_of_lt (show d < 18446744073709551616 by omega)]; omega))
          (fun h => absurd rfl h) (fun _ => specR_hangI)
      have hl : BitVec.ofNat 64 d < BitVec.ofNat 64 (2 ^ 62) := by
        rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]; norm_num; omega
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ulfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; first | exact hl | (rw [Nat.mod_eq_of_lt (show d < 18446744073709551616 by omega)]; omega))
        (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_internFVarR (C := ctxH C H1) ra (ctxOK_H hok H1) hc.fv ulfV (vv ulfDm) (vv kD) dom d (by omega) (by decide)
        (by simp) (by simp +decide [Env.get, ulfParams, ctxEnv]) (fun fv s4 hr4 => ?_)
      have hq4 := hQf _ _ _ _ _ hq1 hr4
      refine callE_specR (C := ctxH C H1) ulfO ExI.fInst1F [pFu, pH, ExI.pV, ExI.pD]
        [.const (BitVec.ofNat 64 coreWalkFuel), vv ulfB, vv ulfV, .const 0] (ExI.fastBody C)
        [BitVec.ofNat 64 coreWalkFuel, Enc.idxW body, Enc.idxW fv, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.i1
        ⟨rfl, by simp, by simp, rfl, trivial⟩
        (ExI.fast_spec ra (ctxH C H1) (ctxOK_H hok H1) (ExIS.codes_H C H1 hc.i1c) s4 coreWalkFuel body fv 0
          CV.coreWalkFuel_lt (by decide)) (fun ob s5 hr5 => ?_)
      have hq5 := hQ1 _ _ _ _ _ _ _ hq4 hr5
      refine specR_congr (m' := unitLikeFields (knot mode C n) (unitLikeLoop (knot mode C n) C.fe F) N (d + 1) ob >>= fun r => pure r)
        (by simp) ?_
      refine specR_callNIH (C := ctxH C H1) ulfR fUlf ulfParams [vv kFu, .op .add [vv kD, .const 1], vv ulfF,
        .op .sub [vv ulfN, .const 1], vv ulfO] ulfBody
        [BitVec.ofNat 64 n, BitVec.ofNat 64 (d + 1), BitVec.ofNat 64 F, BitVec.ofNat 64 N, Enc.idxW ob] (by decide) rfl (by decide) hc.self
        ⟨by simp +decide [Env.get, ulfParams, ctxEnv], by simp +decide [sev, Env.get, ulfParams, ctxEnv]; exact word_add1_eq d, by simp +decide [Env.get, ulfParams, ctxEnv],
          by simp +decide [sev, Env.get, ulfParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, by simp, trivial⟩
        (PostB (ctxH C H1)) (fun b w s' H' => w = boolW b)
        (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ulfParams _ rfl hlk)
          (ih (d + 1) ob H1 s5 (hpH.trans hp1) hq5 (by omega) (by omega)))
        (fun r w s6 H6 hp6 hw => ?_)
      exact specR_returnI _ w (by simp) (fun t ht => ⟨H6, hp1.trans hp6, hw, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine specR_callNIH (C := ctxH C H1) ulfU fUll ullParams [vv kFu, vv kD, vv ulfF, vv ulfDm] ullBody
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, BitVec.ofNat 64 F, Enc.idxW dom] (by decide) rfl (by decide) hc.ull
      ⟨by simp +decide [Env.get, ulfParams, ctxEnv], by simp +decide [Env.get, ulfParams, ctxEnv], by simp +decide [Env.get, ulfParams, ctxEnv], by simp, trivial⟩
      (fun b w s' st => unitLikeLoop (knot mode C n) C.fe F d dom s1 = .ok (b, s') ∧ PostB (ctxH C H1) b w s' st)
      (fun b w s' H' => unitLikeLoop (knot mode C n) C.fe F d dom s1 = .ok (b, s') ∧ w = boolW b)
      (fun b w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hr, hw⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu ullParams _ rfl hlk)
        (hUL H1 s1 d dom (hpH.trans hp1) hq1 hd)))
      (fun q w2 s2 H2 hp2 ⟨hr2, hw2⟩ => ?_)
    subst hw2
    have hq2 := hQl _ _ _ _ _ hq1 hr2
    have hp12 : H <+: H2 := hp1.trans hp2
    rcases Bool.eq_false_or_eq_true q with rfl | rfl
    · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [↓reduceIte]
      by_cases hd2 : d < 2 ^ 62
      swap
      · have hl : ¬ (BitVec.ofNat 64 d < BitVec.ofNat 64 (2 ^ 62)) := by
          rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]; norm_num; omega
        exact specR_ifI _ 0 (by simp +decide [sev, Env.get, ulfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; first | exact hl | (rw [Nat.mod_eq_of_lt (show d < 18446744073709551616 by omega)]; omega))
          (fun h => absurd rfl h) (fun _ => specR_hangI)
      have hl : BitVec.ofNat 64 d < BitVec.ofNat 64 (2 ^ 62) := by
        rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]; norm_num; omega
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ulfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; first | exact hl | (rw [Nat.mod_eq_of_lt (show d < 18446744073709551616 by omega)]; omega))
        (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_internFVarR (C := ctxH C H2) ra (ctxOK_H hok H2) hc.fv ulfV (vv ulfDm) (vv kD) dom d (by omega) (by decide)
        (by simp) (by simp +decide [Env.get, ulfParams, ctxEnv]) (fun fv s4 hr4 => ?_)
      have hq4 := hQf _ _ _ _ _ hq2 hr4
      refine callE_specR (C := ctxH C H2) ulfO ExI.fInst1F [pFu, pH, ExI.pV, ExI.pD]
        [.const (BitVec.ofNat 64 coreWalkFuel), vv ulfB, vv ulfV, .const 0] (ExI.fastBody C)
        [BitVec.ofNat 64 coreWalkFuel, Enc.idxW body, Enc.idxW fv, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.i1
        ⟨rfl, by simp, by simp, rfl, trivial⟩
        (ExI.fast_spec ra (ctxH C H2) (ctxOK_H hok H2) (ExIS.codes_H C H2 hc.i1c) s4 coreWalkFuel body fv 0
          CV.coreWalkFuel_lt (by decide)) (fun ob s5 hr5 => ?_)
      have hq5 := hQ1 _ _ _ _ _ _ _ hq4 hr5
      refine specR_congr (m' := unitLikeFields (knot mode C n) (unitLikeLoop (knot mode C n) C.fe F) N (d + 1) ob >>= fun r => pure r)
        (by simp) ?_
      refine specR_callNIH (C := ctxH C H2) ulfR fUlf ulfParams [vv kFu, .op .add [vv kD, .const 1], vv ulfF,
        .op .sub [vv ulfN, .const 1], vv ulfO] ulfBody
        [BitVec.ofNat 64 n, BitVec.ofNat 64 (d + 1), BitVec.ofNat 64 F, BitVec.ofNat 64 N, Enc.idxW ob] (by decide) rfl (by decide) hc.self
        ⟨by simp +decide [Env.get, ulfParams, ctxEnv], by simp +decide [sev, Env.get, ulfParams, ctxEnv]; exact word_add1_eq d, by simp +decide [Env.get, ulfParams, ctxEnv],
          by simp +decide [sev, Env.get, ulfParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, by simp, trivial⟩
        (PostB (ctxH C H2)) (fun b w s' H' => w = boolW b)
        (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ulfParams _ rfl hlk)
          (ih (d + 1) ob H2 s5 (hpH.trans hp12) hq5 (by omega) (by omega)))
        (fun r w s6 H6 hp6 hw => ?_)
      exact specR_returnI _ w (by simp) (fun t ht => ⟨H6, hp12.trans hp6, hw, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H2, hp12, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
