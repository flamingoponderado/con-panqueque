import ConPanqueque.T.Core.UnitLikeStruct
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `unitLikeLoop`

Fuel-bounded: the head normal form is a ∀ whose codomain, opened at a fresh variable, is unit-like, or the structure
arm (`unitLikeStruct`, whose fields loop calls back in at the predecessor fuel). Induction on the fuel discharges the
structure arm's loop hypothesis.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

structure UllCodes (C : Ctx) : Prop where
  w : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one)
  fv : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one)
  i1 : C.code.lookup ExI.fInst1F = some ([pFu, pH, ExI.pV, ExI.pD].map (fun p => (p, ShapeHOL.one)), ExI.fastBody C, .one)
  i1c : ExI.Codes C (ExI.body C)
  uls : C.code.lookup fUls = some (ulsParams.map (fun p => (p, ShapeHOL.one)), ulsBody C, .one)
  ulsc : UlsCodes C
  self : C.code.lookup fUll = some (ullParams.map (fun p => (p, ShapeHOL.one)), ullBody, .one)

section
variable {σ : Type}

theorem ull_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (hc : UllCodes C) (Q : AState → Prop)
    (hQF : ∀ s, Q s → UlsFacts C s)
    (hLPl : ∀ c ci, C.fe.find? c = some ci → ci.toConstantVal.levelParams.length + 1 < 2 ^ 60)
    (hQw : ∀ s1 d e r s2, Q s1 → (knot mode C n).whnf d e s1 = .ok (r, s2) → Q s2)
    (hQi : ∀ s1 d T b s2, Q s1 → isPropType (knot mode C n) d T s1 = .ok (b, s2) → Q s2)
    (hQf : ∀ s1 i ty h s2, Q s1 → internE (.fvar i ty) s1 = .ok (h, s2) → Q s2)
    (hQ1 : ∀ s1 fu e v d h s2, Q s1 → instantiate1Fast fu e v d s1 = .ok (h, s2) → Q s2)
    (hQl : ∀ F s1 d T b s2, Q s1 → unitLikeLoop (knot mode C n) C.fe F d T s1 = .ok (b, s2) → Q s2)
    (hQs : ∀ s1 fu lps us e h s2, Q s1 → instLPFast fu lps us e s1 = .ok (h, s2) → Q s2)
    (hQr : ∀ s1 fu e vs st nn dd h s2, Q s1 → instantiateRevRange fu e vs st nn dd s1 = .ok (h, s2) → Q s2)
    (hIO : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (inferIOE C fIOB) s1 ((knot mode C n).inferIO d' e')
      (PostK (ctxH C H)))
    (hW : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d' e')
      (PostK (ctxH C H)))
    (hLE : ∀ (H : List (BitVec 64)) s1 (u v : LIdx), C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s1 [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s1 (lvlEq? u v)
        (LLeq.PostOB (ctxH C H))) :
    ∀ (F : Nat), F < 2 ^ 64 → ∀ (H : List (BitVec 64)) (s : AState) (d : Nat) (T : EIdx), C.H <+: H → Q s → d < 2 ^ 64 →
      SpecR (σ := σ) (Pre (ctxH C H) s (ullParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, BitVec.ofNat 64 F, Enc.idxW T]))
        ullBody s (unitLikeLoop (knot mode C n) C.fe F d T) (PostB (ctxH C H)) := by
  intro F
  induction F with
  | zero =>
    intro _ H s d T hpH hq hd
    refine specR_prologue (postB_locals _) (Knot.params_none _ ullLocals ullParams _ (by decide) (by decide)) ?_
    rw [unitLikeLoop]
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ullParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ F ih =>
    intro hF H s d T hpH hq hd
    refine specR_prologue (postB_locals _) (Knot.params_none _ ullLocals ullParams _ (by decide) (by decide)) ?_
    have hne := ofNat_succ_ne F (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ullParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
    rw [unitLikeLoop]
    refine Big.specR_callKC (C := ctxH C H) ullW fW kParams [vv kFu, vv kD, vv ullT] (whnfE C fWB)
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW T] (by decide) rfl (by decide) hc.w
      ⟨by simp +decide [Env.get, ullParams, ctxEnv], by simp +decide [Env.get, ullParams, ctxEnv], by simp +decide [Env.get, ullParams, ctxEnv], trivial⟩ (hW H s d T hpH) (fun w s1 H1 hp1 hr1 => ?_)
    have hq1 := hQw _ _ _ _ _ hq hr1
    refine Knot.specR_tagIteV ullW w 6 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
    swap
    · rw [if_neg (show ¬ (w.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg)]
      refine specR_congr (m' := unitLikeStruct (knot mode C n) (unitLikeLoop (knot mode C n) C.fe F) C.fe d w >>= fun r => pure r)
        (by simp) ?_
      refine specR_callNIH (C := ctxH C H1) ullR fUls ulsParams [vv kFu, vv kD, .op .sub [vv ullF, .const 1], vv ullW] (ulsBody C)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, BitVec.ofNat 64 F, Enc.idxW w] (by decide) rfl (by decide) hc.uls
        ⟨by simp +decide [Env.get, ullParams, ctxEnv], by simp +decide [Env.get, ullParams, ctxEnv], by simp +decide [sev, Env.get, ullParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, by simp, trivial⟩
        (PostB (ctxH C H1)) (fun b w' _ _ => w' = boolW b) (fun b w' s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ulsParams _ rfl hlk)
          (uls_spec ra mode n C hok hc.ulsc Q F hQF hLPl hQi hQf hQ1 (hQl F) hQs hQr hIO hW hLE
            (fun H' s' d' T' hp' hq' hd' => ih (by omega) H' s' d' T' hp' hq' hd') H1 s1 d w (hpH.trans hp1) hq1 hd))
        (fun r w2 s2 H2 hp2 hw => ?_)
      exact specR_returnI _ w2 (by simp) (fun t ht => ⟨H2, hp1.trans hp2, hw, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    rw [if_pos (show (w.tag == ETag.forallE) = true by simp [htg, ETag.forallE])]
    refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv ullW) (Enc.idxW w) (by decide) (by simp) ?_
    refine specR_viewP (C := ctxH C H1) w (by simp) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
      (fun v P hv htn _ => ?_)
    have h6 : v.tagN = 6 := by rw [htn, htg]; rfl
    obtain ⟨dom, body, rfl⟩ : ∃ ty b, v = .forallE ty b := by cases v <;> simp [ENodeView.tagN] at h6 ⊢
    have hvb : s1.store.viewBind w = some (dom, body) := viewBind_of_view_forallE (by rw [htg]; rfl) hv
    refine specR_runBind (by rw [viewBind_run, hvb]) ?_
    dsimp only
    refine specR_loadI' ullDm (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW dom) (by decide) (by simp) (by simp)
      (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW dom) [Enc.idxW body] []) ?_
    refine specR_loadI' ullB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW body) (by decide) (by simp +decide [sev]) rfl
      (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW dom) (Enc.idxW body) [] []) ?_
    refine specR_dropM ?_
    by_cases hd2 : d < 2 ^ 62
    swap
    · have hl : ¬ (BitVec.ofNat 64 d < BitVec.ofNat 64 (2 ^ 62)) := by
        rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]; norm_num; omega
      exact specR_ifI _ 0 (by simp +decide [sev, Env.get, ullParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; first | exact hl | (rw [Nat.mod_eq_of_lt (show d < 18446744073709551616 by omega)]; omega))
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    have hl : BitVec.ofNat 64 d < BitVec.ofNat 64 (2 ^ 62) := by
      rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hd]; norm_num; omega
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ullParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; first | exact hl | (rw [Nat.mod_eq_of_lt (show d < 18446744073709551616 by omega)]; omega))
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_internFVarR (C := ctxH C H1) ra (ctxOK_H hok H1) hc.fv ullV (vv ullDm) (vv kD) dom d (by omega) (by decide)
      (by simp) (by simp +decide [Env.get, ullParams, ctxEnv]) (fun fv s4 hr4 => ?_)
    have hq4 := hQf _ _ _ _ _ hq1 hr4
    refine callE_specR (C := ctxH C H1) ullO ExI.fInst1F [pFu, pH, ExI.pV, ExI.pD]
      [.const (BitVec.ofNat 64 coreWalkFuel), vv ullB, vv ullV, .const 0] (ExI.fastBody C)
      [BitVec.ofNat 64 coreWalkFuel, Enc.idxW body, Enc.idxW fv, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.i1
      ⟨rfl, by simp, by simp, rfl, trivial⟩
      (ExI.fast_spec ra (ctxH C H1) (ctxOK_H hok H1) (ExIS.codes_H C H1 hc.i1c) s4 coreWalkFuel body fv 0
        CV.coreWalkFuel_lt (by decide)) (fun ob s5 hr5 => ?_)
    have hq5 := hQ1 _ _ _ _ _ _ _ hq4 hr5
    refine specR_congr (m' := unitLikeLoop (knot mode C n) C.fe F (d + 1) ob >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H1) ullR fUll ullParams [vv kFu, .op .add [vv kD, .const 1],
      .op .sub [vv ullF, .const 1], vv ullO] ullBody
      [BitVec.ofNat 64 n, BitVec.ofNat 64 (d + 1), BitVec.ofNat 64 F, Enc.idxW ob] (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [Env.get, ullParams, ctxEnv], by simp +decide [sev, Env.get, ullParams, ctxEnv]; exact word_add1_eq d,
        by simp +decide [sev, Env.get, ullParams, ctxEnv]; exact Ex.ofNat_succ_sub_one _, by simp, trivial⟩
      (PostB (ctxH C H1)) (fun b w' s' H' => w' = boolW b)
      (fun b w' s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ullParams _ rfl hlk)
        (ih (by omega) H1 s5 (d + 1) ob (hpH.trans hp1) hq5 (by omega)))
      (fun r w6 s6 H6 hp6 hw => ?_)
    exact specR_returnI _ w6 (by simp) (fun t ht => ⟨H6, hp1.trans hp6, hw, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
