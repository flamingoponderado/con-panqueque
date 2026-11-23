import ConPanqueque.T.Core.UnitLikeLoop
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `structUnitCert`

`a`'s io-inferred type, head-normalized, is unit-like (`unitLikeLoop` at `unitLikeFuel`) and `b`'s is definitionally
equal to it; a side whose type is a ∀ must be neutral (`ioNeutral`, read-only).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc

theorem RO.ioNeutral (e : EIdx) : RO (ConRon.Arena.ioNeutral e) := by
  unfold ConRon.Arena.ioNeutral
  refine RO.bind (RO.getAppFn _ _) (fun h => ?_)
  dsimp only
  split
  · exact RO.pure _
  split
  · exact RO.pure _
  split
  · exact RO.pure _
  exact RO.pure _

structure SucCodes (C : Ctx) : Prop where
  io : C.code.lookup fIO = some (pmap kParams, inferIOE C fIOB, .one)
  w : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one)
  nu : C.code.lookup fNu = some ([nuE].map (fun p => (p, ShapeHOL.one)), nuBody, .one)
  gaf : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  ull : C.code.lookup fUll = some (ullParams.map (fun p => (p, ShapeHOL.one)), ullBody, .one)
  ullc : UllCodes C
  d : C.code.lookup fD = some (pmap dParams, dE C, .one)

section
variable {σ : Type}

theorem suc_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (hc : SucCodes C) (Q : AState → Prop)
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
    (hLE : ∀ (H : List (BitVec 64)) s1 (u v : LIdx), C.H <+: H → (denoteL s1.store.ls u).isSome = true →
      (denoteL s1.store.ls v).isSome = true →
      SpecR (σ := σ) (Pre (ctxH C H) s1 [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s1 (lvlEq? u v)
        (LLeq.PostOB (ctxH C H)))
    (hQio : ∀ s1 d e r s2, Q s1 → (knot mode C n).inferIO d e s1 = .ok (r, s2) → Q s2)
    (hD : ∀ (H : List (BitVec 64)) s1 d' a b, C.H <+: H → Callee (σ := σ) (ctxH C H) dParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW a, Enc.idxW b] (dE C) s1 ((knot mode C n).defeq d' a b)
      (PostB (ctxH C H))) :
    ∀ (H : List (BitVec 64)) (s : AState) (d : Nat) (a b : EIdx), C.H <+: H → Q s → d < 2 ^ 64 →
      SpecR (σ := σ) (Pre (ctxH C H) s (sucParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b]))
        sucBody s (structUnitCert (knot mode C n) C.fe d a b) (PostB (ctxH C H)) := by
  intro H s d a b hpH hq hd
  refine specR_prologue (postB_locals _) (Knot.params_none _ sucLocals sucParams _ (by decide) (by decide)) ?_
  unfold structUnitCert
  refine Big.specR_callKC (C := ctxH C H) sucTa fIO kParams [vv kFu, vv kD, vv (ofString "suc_a")] (inferIOE C fIOB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a] (by decide) rfl (by decide) hc.io
    ⟨by simp +decide [Env.get, sucParams, ctxEnv], by simp +decide [Env.get, sucParams, ctxEnv], by simp +decide [Env.get, sucParams, ctxEnv], trivial⟩ (hIO H s d a hpH) (fun ta s1 H1 hp1 hr1 => ?_)
  have hq1 := hQio _ _ _ _ _ hq hr1
  refine Big.specR_callKC (C := ctxH C H1) sucWa fW kParams [vv kFu, vv kD, vv sucTa] (whnfE C fWB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW ta] (by decide) rfl (by decide) hc.w
    ⟨by simp +decide [Env.get, sucParams, ctxEnv], by simp +decide [Env.get, sucParams, ctxEnv], by simp, trivial⟩ (hW H1 s1 d ta (hpH.trans hp1)) (fun wa s2 H2 hp2 hr2 => ?_)
  have hq2 := hQw _ _ _ _ _ hq1 hr2
  have hp02 : H <+: H2 := hp1.trans hp2
  refine Knot.specR_tagIteV sucWa wa 6 (by decide) (by decide) (by simp) (fun htga => ?_) (fun htga => ?_)
  swap
  · rw [if_neg (show ¬ isForallE wa = true by simpa [isForallE, ETag.forallE] using htga)]
    try simp only [pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine specR_callNIH (C := ctxH C H2) sucU fUll ullParams [vv kFu, vv kD, .const (BitVec.ofNat 64 unitLikeFuel), vv sucWa]
      ullBody [BitVec.ofNat 64 n, BitVec.ofNat 64 d, BitVec.ofNat 64 unitLikeFuel, Enc.idxW wa] (by decide) rfl (by decide) hc.ull
      ⟨by simp +decide [Env.get, sucParams, ctxEnv], by simp +decide [Env.get, sucParams, ctxEnv], rfl, by simp, trivial⟩
      (PostB (ctxH C H2)) (fun b w' _ _ => w' = boolW b) (fun b w' s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ullParams _ rfl hlk)
        (ull_spec ra mode n C hok hc.ullc Q hQF hLPl hQw hQi hQf hQ1 hQl hQs hQr hIO hW hLE unitLikeFuel
          (by unfold unitLikeFuel; decide) H2 s2 d wa (hpH.trans hp02) hq2 hd))
      (fun u w4 s4 H4 hp4 hw => ?_)
    subst hw
    have hp04 : H <+: H4 := hp02.trans hp4
    rcases Bool.eq_false_or_eq_true u with rfl | rfl
    · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [↓reduceIte]
      refine Big.specR_callKC (C := ctxH C H4) sucTb fIO kParams [vv kFu, vv kD, vv (ofString "suc_b")] (inferIOE C fIOB)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW b] (by decide) rfl (by decide) hc.io
        ⟨by simp +decide [Env.get, sucParams, ctxEnv], by simp +decide [Env.get, sucParams, ctxEnv], by simp +decide [Env.get, sucParams, ctxEnv], trivial⟩ (hIO H4 s4 d b (hpH.trans hp04)) (fun tb s5 H5 hp5 _ => ?_)
      have hp05 : H <+: H5 := hp04.trans hp5
      refine Big.specR_callKC (C := ctxH C H5) sucWb fW kParams [vv kFu, vv kD, vv sucTb] (whnfE C fWB)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW tb] (by decide) rfl (by decide) hc.w
        ⟨by simp +decide [Env.get, sucParams, ctxEnv], by simp +decide [Env.get, sucParams, ctxEnv], by simp, trivial⟩ (hW H5 s5 d tb (hpH.trans hp05)) (fun wb s6 H6 hp6 _ => ?_)
      have hp06 : H <+: H6 := hp05.trans hp6
      refine Knot.specR_tagIteV sucWb wb 6 (by decide) (by decide) (by simp) (fun htgb => ?_) (fun htgb => ?_)
      swap
      · rw [if_neg (show ¬ isForallE wb = true by simpa [isForallE, ETag.forallE] using htgb)]
        try simp only [pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        refine specR_congr (m' := (knot mode C n).defeq d wa wb >>= fun r => pure r) (by simp) ?_
        refine specR_callNIH (C := ctxH C H6) sucR fD dParams [vv kFu, vv kD, vv sucWa, vv sucWb] (dE C)
          [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW wa, Enc.idxW wb] (by decide) rfl (by decide) hc.d
          ⟨by simp +decide [Env.get, sucParams, ctxEnv], by simp +decide [Env.get, sucParams, ctxEnv], by simp, by simp, trivial⟩
          (PostB (ctxH C H6)) (fun b w' _ _ => w' = boolW b) (fun b w' s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
          (fun u hu _ hlk => hD H6 s6 d wa wb (hpH.trans hp06) u hu (fun i hi _ => hlk i (by omega)))
          (fun r w7 s7 H7 hp7 hw => ?_)
        exact specR_returnI _ w7 (by simp) (fun t ht => ⟨H7, hp06.trans hp7, hw, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

      rw [if_pos (show isForallE wb = true by simp [isForallE, htgb, ETag.forallE])]
      refine specR_callNIH (C := ctxH C H6) sucG2 fNu [nuE] [vv (ofString "suc_b")] nuBody [Enc.idxW b] (by decide) rfl (by decide) hc.nu
        ⟨by simp +decide [Env.get, sucParams, ctxEnv], trivial⟩
        (fun g w' s' st => ioNeutral b s6 = .ok (g, s') ∧ PostB (ctxH C H6) g w' s' st)
        (fun g w' s' H' => ioNeutral b s6 = .ok (g, s') ∧ w' = boolW g)
        (fun g w' s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hr, hw⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [nuE] _ rfl hlk) (nu_spec (ctxH C H6) hc.gaf s6 b)))
        (fun g w8 s8 H8 hp8 ⟨hrn8, hw8⟩ => ?_)
      subst hw8
      have hp08 : H <+: H8 := hp06.trans hp8
      rcases Bool.eq_false_or_eq_true g with rfl | rfl
      · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        refine specR_congr (m' := (knot mode C n).defeq d wa wb >>= fun r => pure r) (by simp) ?_
        refine specR_callNIH (C := ctxH C H8) sucR fD dParams [vv kFu, vv kD, vv sucWa, vv sucWb] (dE C)
          [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW wa, Enc.idxW wb] (by decide) rfl (by decide) hc.d
          ⟨by simp +decide [Env.get, sucParams, ctxEnv], by simp +decide [Env.get, sucParams, ctxEnv], by simp, by simp, trivial⟩
          (PostB (ctxH C H8)) (fun b w' _ _ => w' = boolW b) (fun b w' s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
          (fun u hu _ hlk => hD H8 s8 d wa wb (hpH.trans hp08) u hu (fun i hi _ => hlk i (by omega)))
          (fun r w7 s7 H7 hp7 hw => ?_)
        exact specR_returnI _ w7 (by simp) (fun t ht => ⟨H7, hp08.trans hp7, hw, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

      refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
      simp only [Bool.not_false, ↓reduceIte]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H8, hp08, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H4, hp04, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

  rw [if_pos (show isForallE wa = true by simp [isForallE, htga, ETag.forallE])]
  refine specR_callNIH (C := ctxH C H2) sucG fNu [nuE] [vv (ofString "suc_a")] nuBody [Enc.idxW a] (by decide) rfl (by decide) hc.nu
    ⟨by simp +decide [Env.get, sucParams, ctxEnv], trivial⟩
    (fun g w' s' st => ioNeutral a s2 = .ok (g, s') ∧ PostB (ctxH C H2) g w' s' st)
    (fun g w' s' H' => ioNeutral a s2 = .ok (g, s') ∧ w' = boolW g)
    (fun g w' s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hr, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [nuE] _ rfl hlk) (nu_spec (ctxH C H2) hc.gaf s2 a)))
    (fun g w3 s3 H3 hp3 ⟨hrn3, hw3⟩ => ?_)
  subst hw3
  have hs3 : s3 = s2 := RO.ioNeutral _ _ _ _ hrn3
  subst s3
  have hp03 : H <+: H3 := hp02.trans hp3
  rcases Bool.eq_false_or_eq_true g with rfl | rfl
  · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine specR_callNIH (C := ctxH C H3) sucU fUll ullParams [vv kFu, vv kD, .const (BitVec.ofNat 64 unitLikeFuel), vv sucWa]
      ullBody [BitVec.ofNat 64 n, BitVec.ofNat 64 d, BitVec.ofNat 64 unitLikeFuel, Enc.idxW wa] (by decide) rfl (by decide) hc.ull
      ⟨by simp +decide [Env.get, sucParams, ctxEnv], by simp +decide [Env.get, sucParams, ctxEnv], rfl, by simp, trivial⟩
      (PostB (ctxH C H3)) (fun b w' _ _ => w' = boolW b) (fun b w' s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ullParams _ rfl hlk)
        (ull_spec ra mode n C hok hc.ullc Q hQF hLPl hQw hQi hQf hQ1 hQl hQs hQr hIO hW hLE unitLikeFuel
          (by unfold unitLikeFuel; decide) H3 s2 d wa (hpH.trans hp03) hq2 hd))
      (fun u w4 s4 H4 hp4 hw => ?_)
    subst hw
    have hp04 : H <+: H4 := hp03.trans hp4
    rcases Bool.eq_false_or_eq_true u with rfl | rfl
    · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [↓reduceIte]
      refine Big.specR_callKC (C := ctxH C H4) sucTb fIO kParams [vv kFu, vv kD, vv (ofString "suc_b")] (inferIOE C fIOB)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW b] (by decide) rfl (by decide) hc.io
        ⟨by simp +decide [Env.get, sucParams, ctxEnv], by simp +decide [Env.get, sucParams, ctxEnv], by simp +decide [Env.get, sucParams, ctxEnv], trivial⟩ (hIO H4 s4 d b (hpH.trans hp04)) (fun tb s5 H5 hp5 _ => ?_)
      have hp05 : H <+: H5 := hp04.trans hp5
      refine Big.specR_callKC (C := ctxH C H5) sucWb fW kParams [vv kFu, vv kD, vv sucTb] (whnfE C fWB)
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW tb] (by decide) rfl (by decide) hc.w
        ⟨by simp +decide [Env.get, sucParams, ctxEnv], by simp +decide [Env.get, sucParams, ctxEnv], by simp, trivial⟩ (hW H5 s5 d tb (hpH.trans hp05)) (fun wb s6 H6 hp6 _ => ?_)
      have hp06 : H <+: H6 := hp05.trans hp6
      refine Knot.specR_tagIteV sucWb wb 6 (by decide) (by decide) (by simp) (fun htgb => ?_) (fun htgb => ?_)
      swap
      · rw [if_neg (show ¬ isForallE wb = true by simpa [isForallE, ETag.forallE] using htgb)]
        try simp only [pure_bind, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        refine specR_congr (m' := (knot mode C n).defeq d wa wb >>= fun r => pure r) (by simp) ?_
        refine specR_callNIH (C := ctxH C H6) sucR fD dParams [vv kFu, vv kD, vv sucWa, vv sucWb] (dE C)
          [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW wa, Enc.idxW wb] (by decide) rfl (by decide) hc.d
          ⟨by simp +decide [Env.get, sucParams, ctxEnv], by simp +decide [Env.get, sucParams, ctxEnv], by simp, by simp, trivial⟩
          (PostB (ctxH C H6)) (fun b w' _ _ => w' = boolW b) (fun b w' s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
          (fun u hu _ hlk => hD H6 s6 d wa wb (hpH.trans hp06) u hu (fun i hi _ => hlk i (by omega)))
          (fun r w7 s7 H7 hp7 hw => ?_)
        exact specR_returnI _ w7 (by simp) (fun t ht => ⟨H7, hp06.trans hp7, hw, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

      rw [if_pos (show isForallE wb = true by simp [isForallE, htgb, ETag.forallE])]
      refine specR_callNIH (C := ctxH C H6) sucG2 fNu [nuE] [vv (ofString "suc_b")] nuBody [Enc.idxW b] (by decide) rfl (by decide) hc.nu
        ⟨by simp +decide [Env.get, sucParams, ctxEnv], trivial⟩
        (fun g w' s' st => ioNeutral b s6 = .ok (g, s') ∧ PostB (ctxH C H6) g w' s' st)
        (fun g w' s' H' => ioNeutral b s6 = .ok (g, s') ∧ w' = boolW g)
        (fun g w' s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hr, hw⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [nuE] _ rfl hlk) (nu_spec (ctxH C H6) hc.gaf s6 b)))
        (fun g w8 s8 H8 hp8 ⟨hrn8, hw8⟩ => ?_)
      subst hw8
      have hp08 : H <+: H8 := hp06.trans hp8
      rcases Bool.eq_false_or_eq_true g with rfl | rfl
      · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        refine specR_congr (m' := (knot mode C n).defeq d wa wb >>= fun r => pure r) (by simp) ?_
        refine specR_callNIH (C := ctxH C H8) sucR fD dParams [vv kFu, vv kD, vv sucWa, vv sucWb] (dE C)
          [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW wa, Enc.idxW wb] (by decide) rfl (by decide) hc.d
          ⟨by simp +decide [Env.get, sucParams, ctxEnv], by simp +decide [Env.get, sucParams, ctxEnv], by simp, by simp, trivial⟩
          (PostB (ctxH C H8)) (fun b w' _ _ => w' = boolW b) (fun b w' s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
          (fun u hu _ hlk => hD H8 s8 d wa wb (hpH.trans hp08) u hu (fun i hi _ => hlk i (by omega)))
          (fun r w7 s7 H7 hp7 hw => ?_)
        exact specR_returnI _ w7 (by simp) (fun t ht => ⟨H7, hp08.trans hp7, hw, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

      refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
      simp only [Bool.not_false, ↓reduceIte]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H8, hp08, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H4, hp04, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

  refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
  simp only [Bool.not_false, ↓reduceIte]
  exact specR_returnI _ 0 rfl (fun t ht => ⟨H3, hp03, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
