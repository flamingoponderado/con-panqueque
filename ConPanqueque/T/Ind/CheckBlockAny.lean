import ConPanqueque.T.SameLay
import ConPanqueque.T.Ind.CheckBlockK

/-!
# `checkBlock` at any block

`cbk_spec_any`: at a block of one member and one recursor, `cbk_spec` (its facts bundled as `CBKFacts`); at
any other block the member or recursor count test hangs.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

/-- The facts `cbk_spec` takes of a one-member, one-recursor block. -/
structure CBKFacts (mode : ConLeche.CheckMode) (C : Ctx) (block : List IConstantInfo) (p₀ : BlockShape)
    (ms0 : MemberShape) (rc : RecShape) : Prop where
  sp : SplitOK p₀ block
  nP : p₀.nP < 2 ^ 55
  lp : ms0.cvT.levelParams.length < 2 ^ 58
  ni : ms0.nIdx < 2 ^ 56
  cl : ms0.ctors.length < 2 ^ 58
  nf : ∀ c ∈ ms0.ctors, p₀.nP + c.2 < 2 ^ 56
  mI : rc.mI < 2 ^ 56
  rP : rc.rP < 2 ^ 61
  rl : rc.rules.length < 2 ^ 58
  rlp : rc.cvR.levelParams.length < 2 ^ 59
  ks : ∃ ks : List ConLeche.Name, ∃ hkl : ks.length = ms0.cvT.levelParams.length,
    ∀ j (hj : j < ms0.cvT.levelParams.length), denoteN C.St.ns ms0.cvT.levelParams[j] = some (ks[j]'(by omega))
  kr : ∃ kr : List ConLeche.Name, ∃ hkr : kr.length = rc.cvR.levelParams.length,
    ∀ j (hj : j < rc.cvR.levelParams.length), denoteN C.St.ns rc.cvR.levelParams[j] = some (kr[j]'(by omega))
  dd : CVDen ms0.declared C.St
  cs : ∀ c ∈ ms0.ctors, CVDen c.1 C.St ∧ SumCtorOK C p₀.nP c
  rd : CVDen rc.cvR C.St
  run : CBKRun mode C block p₀ ms0 rc

section
variable {σ : Type}

set_option maxHeartbeats 16000000 in
/-- **`checkBlock` at any block**: one member and one recursor checked; any other count hangs. -/
theorem cbk_spec_any (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hpl : C.saved = none) (hc : CBKCodes mode C) (hf : ConPanqueque.Front.FrontOK C)
    (hg : TblGate C.fe) (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins)
    (heqS : ∀ (C' : Ctx), SameLay C C' → CtxOK C' → ∀ (H : List (BitVec 64)) (u v : LIdx) (s : AState)
      (lu lv : ConLeche.Level), denoteL s.store.ls u = some lu → denoteL s.store.ls v = some lv → CachesOK s →
      SpecR (σ := σ) (Pre (ctxH C' H) s [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s (lvlEq? u v)
        (fun o w s' st => LLeq.PostOB (ctxH C' H) o w s' st))
    (block : List IConstantInfo) (p₀ : BlockShape) (osh : Nat) (hsh : ShapeRep C C.H osh p₀)
    (hfacts : ∀ ms0 rc, p₀.members = [ms0] → p₀.recs = [rc] → CBKFacts mode C block p₀ ms0 rc) (s : AState)
    (hck : ∃ env, CheckOK false env C.fe s ∧ ConLeche.EnvWF env ∧ ConRon.Bridge.Inductives.EnvRel env C.fe s.store) :
    SpecR (σ := σ) (Pre C s (cbkParams.zip [cellA C osh])) (cbkBody C) s (checkBlock mode C.fe block p₀) (PostBlk C) := by
  by_cases h1 : ∃ ms0 rc, p₀.members = [ms0] ∧ p₀.recs = [rc]
  · obtain ⟨ms0, rc, hms, hrecs⟩ := h1
    obtain ⟨sp, nP, lp, ni, cl, nf, mI, rP, rl, rlp, ⟨ks, hkl, hks⟩, ⟨kr, hkr, hkrs⟩, dd, cs, rd, run⟩ :=
      hfacts ms0 rc hms hrecs
    exact cbk_spec mode ra C hok hs hpl hc hf hg hF hL heqS block p₀ ms0 hms rc hrecs sp osh hsh nP lp ni cl nf
      mI rP rl rlp ks hkl hks kr hkr hkrs dd cs rd run s hck
  refine specR_prologue (postBlk_locals C) (cbk_none C _) ?_
  obtain ⟨⟨om, hom, hM⟩, ⟨orl, horl, hR⟩, -, -, -, -, -⟩ := hsh
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hlay := hok.heapLay
  have hHN' : C.H.length ≤ C.HN := hHN
  -- the member count
  refine UD.specR_heapLoadI' (C := C) cbkOm _ osh _ hom (by decide) (by simp +decide [sev, Env.get, cbkParams, ctxEnv]) ?_
  refine UD.specR_heapLoadI' (C := C) cbkNm0 (vv cbkOm) om _ hM.1 (by decide) (by simp [sev, Env.get_cons]) ?_
  have hmlen : p₀.members.length < 2 ^ 61 := by
    rcases Nat.eq_zero_or_pos p₀.members.length with h0 | hpos
    · omega
    · obtain ⟨oi, h1', -⟩ := hM.2 (p₀.members.length - 1) (by omega)
      have := (List.getElem?_eq_some_iff.mp h1').1; omega
  by_cases hm1 : p₀.members.length = 1
  swap
  · refine specR_ifI _ 0 (by
      simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      intro h; apply hm1
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega)] at this
      simpa using this) (fun h => absurd rfl h) (fun _ => specR_hangI)
  obtain ⟨ms0, hms⟩ : ∃ ms0, p₀.members = [ms0] := by
    match hmm : p₀.members, hm1 with
    | [x], _ => exact ⟨x, rfl⟩
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hm1])
    (fun _ => ?_) (fun h => absurd h (by decide))
  obtain ⟨omr, homr, hmr⟩ := hM.2 0 (by simp [hms])
  simp only [hms, List.getElem_cons_zero] at hmr
  obtain ⟨⟨oc, hoc, hcv⟩, ⟨od, hod, hcvd⟩, hni0, ⟨oct, hoct, hctr⟩⟩ := hmr
  refine UD.specR_heapLoadI' (C := C) cbkOmr _ (om + 1 + 0) _ homr (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C om) ?_
  refine UD.specR_heapLoadI' (C := C) cbkOc (vv cbkOmr) omr _ hoc (by decide) (by simp [sev, Env.get_cons]) ?_
  refine UD.specR_heapLoadI' (C := C) cbkNm (vv cbkOc) oc _ hcv.1 (by decide) (by simp [sev, Env.get_cons]) ?_
  refine UD.specR_heapLoadI' (C := C) cbkOd _ (omr + 1) _ hod (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C omr) ?_
  refine UD.specR_heapLoadI' (C := C) cbkDnm (vv cbkOd) od _ hcvd.1 (by decide) (by simp [sev, Env.get_cons]) ?_
  refine UD.specR_heapLoadI' (C := C) cbkOct _ (omr + 3) _ hoct (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C omr 3) ?_
  refine UD.specR_heapLoadI' (C := C) cbkNct (vv cbkOct) oct _ hctr.1 (by decide) (by simp [sev, Env.get_cons]) ?_
  refine UD.specR_heapLoadI' (C := C) cbkOrl _ (osh + 1) _ horl (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, cbkParams, ctxEnv]; exact cellA_add8 C osh) ?_
  refine UD.specR_heapLoadI' (C := C) cbkNrl (vv cbkOrl) orl _ hR.1 (by decide) (by simp [sev, Env.get_cons]) ?_
  have hrlen : p₀.recs.length < 2 ^ 61 := by
    rcases Nat.eq_zero_or_pos p₀.recs.length with h0 | hpos
    · omega
    · obtain ⟨oi, h1', -⟩ := hR.2 (p₀.recs.length - 1) (by omega)
      have := (List.getElem?_eq_some_iff.mp h1').1; omega
  have hr1 : p₀.recs.length ≠ 1 := by
    intro hr1; apply h1
    match hrr : p₀.recs, hr1 with
    | [x], _ => exact ⟨ms0, x, hms, rfl⟩
  refine specR_ifI _ 0 (by
      simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      intro h; apply hr1
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega)] at this
      simpa using this) (fun h => absurd rfl h) (fun _ => specR_hangI)

end

end ConPanqueque.T.Ind
