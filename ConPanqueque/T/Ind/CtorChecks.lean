import ConPanqueque.T.Ind.NestCtorNf

/-!
# `nestCtors`' small checks: the walk fuel, U4 (a non-ordinary field used later), the result head
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def wwE := ofString "ww_e"
def wwQ := ofString "ww_q"
def wwD := ofString "ww_d"
def fWwf := ofString "whnfWalkFuel"

def wwParams : List MlS := [wwE]
def wwLocals : List MlS := [wwQ, wwD]

def wwBody : ProgHOL 64 := prologue wwLocals
  (.seq (.call (some (some (.local, wwQ), none)) fDepth [.const (BitVec.ofNat 64 coreWalkFuel), vv wwE, .const 0])
  (.seq (.assign .local wwD (.load .one (vv wwQ))) (.return (.op .add [vv wwD, .const (BitVec.ofNat 64 fuelSlack)]))))

def u4Ks := ofString "u4_ks"
def u4I := ofString "u4_i"
def u4N := ofString "u4_n"
def u4Cl := ofString "u4_cl"
def u4L := ofString "u4_l"
def u4K := ofString "u4_k"
def u4B := ofString "u4_b"
def u4R := ofString "u4_r"
def fU4 := ofString "u4Any"

def u4Params : List MlS := [u4Ks, u4I, u4N, u4Cl]
def u4Locals : List MlS := [u4L, u4K, u4B, u4R]

def u4Next : ProgHOL 64 :=
  .seq (.call (some (some (.local, u4R), none)) fU4 [vv u4Ks, .op .add [vv u4I, .const 1], vv u4N, vv u4Cl])
    (.return (vv u4R))

def u4Body : ProgHOL 64 := prologue u4Locals
  (.ite (.cmp .lower (vv u4I) (vv u4N))
    (.seq (.assign .local u4L (.load .one (vv u4Ks)))
    (.ite (.cmp .lower (vv u4I) (vv u4L))
      (.seq (.assign .local u4K (.load .one (.op .add [.op .add [vv u4Ks, .const 8], .shift .lsl (vv u4I) (.const 3)])))
      (.ite (.cmp .equal (vv u4K) (.const 0)) u4Next
        (.seq (.call (some (some (.local, u4B), none)) fSul [vv u4Cl, .const 0, vv u4I])
        (.ite (.cmp .equal (vv u4B) (.const 0)) u4Next (.return (.const 1))))))
      u4Next))
    (.return (.const 0)))

def nrhE := ofString "nrh_e"
def nrhH := ofString "nrh_h"
def fNrh := ofString "nestResHead"

def nrhParams : List MlS := [nrhE]
def nrhLocals : List MlS := [nrhH]

def nrhBody : ProgHOL 64 := prologue nrhLocals
  (.seq (.call (some (some (.local, nrhH), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv nrhE])
  (.ite (tagIsE nrhH 1) (.return (.const 1)) (.return (.const 0))))

structure CCCodes (C : Ctx) : Prop where
  dpt : DPTCodes C
  ww : C.code.lookup fWwf = some (wwParams.map (fun p => (p, ShapeHOL.one)), wwBody, .one)
  sul : SULCodes C
  sulf : C.code.lookup fSul = some (sulParams.map (fun p => (p, ShapeHOL.one)), sulBody, .one)
  u4 : C.code.lookup fU4 = some (u4Params.map (fun p => (p, ShapeHOL.one)), u4Body, .one)
  gf : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  nrh : C.code.lookup fNrh = some (nrhParams.map (fun p => (p, ShapeHOL.one)), nrhBody, .one)

theorem kindW_eq_zero (k : NestFieldKind) : kindW k = 0 ↔ k = .ordinary := by
  cases k with
  | ordinary => simp [kindW]
  | recursive t =>
    simp only [kindW, reduceCtorEq, iff_false]; intro e; have := congrArg BitVec.toNat e; simp at this; omega
  | reflexive t =>
    simp only [kindW, reduceCtorEq, iff_false]; intro e; have := congrArg BitVec.toNat e; simp at this; omega
  | inProgress => simp [kindW]
  | nested b => cases b <;> simp [kindW]

section
variable {σ : Type}

theorem ww_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ wwLocals → (ctxEnv C ++ wwParams.zip vals).get x = none :=
  Knot.params_none C wwLocals wwParams vals (by decide) (by decide)

theorem u4_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ u4Locals → (ctxEnv C ++ u4Params.zip vals).get x = none :=
  Knot.params_none C u4Locals u4Params vals (by decide) (by decide)

theorem nrh_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ nrhLocals → (ctxEnv C ++ nrhParams.zip vals).get x = none :=
  Knot.params_none C nrhLocals nrhParams vals (by decide) (by decide)

/-- A natural number below `2^63`, the heap extended. -/
def PostNB (C : Ctx) (r : Nat) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ w = BitVec.ofNat 64 r ∧ r < 2 ^ 63 ∧ SR (ctxH C H') s' st

theorem postNB_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostNB C a w s' st → PostNB C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, h1, h2, hs⟩ => ⟨H', hp, h1, h2, sr_of_eq hs rfl rfl rfl rfl⟩

/-- **`whnfWalkFuel`**: the depth plus the slack. -/
theorem ww_spec (C : Ctx) (hok : CtxOK C) (hc : CCCodes C) (e : EIdx) (H : List (BitVec 64)) (hp : C.H <+: H)
    (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (wwParams.zip [Enc.idxW e])) wwBody s (whnfWalkFuel e) (PostNB (ctxH C H)) := by
  refine specR_prologue (postNB_locals _) (ww_none _ _) ?_
  unfold whnfWalkFuel depth
  simp only [bind_assoc, pure_bind]
  have hm0 : MemoRepN C.HB H 0 ∅ := ⟨[], rfl, fun k => by simp, fun p hp => by simp at hp⟩
  refine specR_callNIH (C := ctxH C H) wwQ fDepth dptParams [.const (BitVec.ofNat 64 coreWalkFuel), vv wwE, .const 0]
    (dptBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e, 0] (by decide) rfl (by decide) hc.dpt.self
    ⟨rfl, by simp +decide [sev, Env.get, wwParams, ctxEnv], rfl, trivial⟩
    (PostDW (ctxH C H)) (fun r w _ H' => ∃ op mw', w = cellA C op ∧ H'[op]? = some (BitVec.ofNat 64 r.1) ∧
      r.1 < 2 ^ 62 ∧ H'[op + 1]? = some mw' ∧ MemoRepN C.HB H' mw' r.2)
    (fun r w s' st ⟨H', op, mw', hp', hw, h1, hb, h2, h3, hsr⟩ => ⟨H', hp', ⟨op, mw', hw, h1, hb, h2, by exact h3⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu dptParams _ rfl hlk)
      (dpt_spec C hok hc.dpt coreWalkFuel CV.coreWalkFuel_lt e ∅ 0 H s hp hm0))
    (fun r w s1 H1 hp1 ⟨op, mw', hw, h1, hb, _, _⟩ => ?_)
  subst hw
  refine UD.specR_heapLoadI' (C := ctxH C H1) wwD (vv wwQ) op _ h1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  exact specR_returnI _ (BitVec.ofNat 64 (r.1 + fuelSlack))
    (by simp only [sev, sev_vv, Env.get_cons]; simp; rw [BitVec.ofNat_add_ofNat])
    (fun t ht => ⟨H1, hp1, rfl, by unfold fuelSlack; omega, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- **`nestResHead`**: the result's head is a variable. -/
theorem nrh_spec (C : Ctx) (hc : CCCodes C) (e : EIdx) (H : List (BitVec 64)) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (nrhParams.zip [Enc.idxW e])) nrhBody s (nestResHead e) (PostB (ctxH C H)) := by
  refine specR_prologue (postB_locals _) (nrh_none _ _) ?_
  unfold nestResHead
  refine specR_callNIM nrhH fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv nrhE]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e] (by decide) rfl (by decide) hc.gf
    ⟨rfl, by simp +decide [sev, Env.get, nrhParams, ctxEnv], trivial⟩
    (fun a w s' st => getAppFn coreWalkFuel e s = .ok (a, s') ∧ Post (ctxH C H) s a w s' st)
    (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec (ctxH C H) hc.gf coreWalkFuel e s CV.coreWalkFuel_lt t
        ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun hd wh s' st ⟨_, hwh, hs, _⟩ => ?_)
  subst hwh
  have hs' : s = s' := hs.symm
  subst hs'
  refine Knot.specR_tagIteV nrhH hd 1 (by decide) (by decide) (by simp [Env.get_cons]) (fun htg => ?_) (fun htg => ?_)
  · have hb : (hd.tag == ETag.fvar) = true := by simp [htg, ETag.fvar]
    rw [hb]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · have hb : (hd.tag == ETag.fvar) = false := by simpa [ETag.fvar] using htg
    rw [hb]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-- U4's test at one field. -/
def u4G (ks : List NestFieldKind) (closed : EIdx) : Nat → AM Bool := fun i =>
  if (ks[i]?.map (· == .ordinary)).getD true then pure false else structUsedLater closed 0 i

section
variable {σ : Type}

theorem u4_next {C : Ctx} (hc : CCCodes C) (ks : List NestFieldKind) (closed : EIdx) (nF oks : Nat)
    (i : Nat) (hi : i < nF) (hn : nF < 2 ^ 62) {s : AState} {Γ : Env} {M : Mem} (H : List (BitVec 64))
    (ih : ∀ (H' : List (BitVec 64)) (s' : AState), H <+: H' → SpecR (σ := σ) (Pre (ctxH C H') s'
      (u4Params.zip [cellA C oks, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 nF, Enc.idxW closed])) u4Body s'
      ((List.range' (i + 1) (nF - (i + 1))).anyM (u4G ks closed)) (PostB (ctxH C H')))
    (gK : Γ.get u4Ks = some (cellA C oks)) (gI : Γ.get u4I = some (BitVec.ofNat 64 i))
    (gN : Γ.get u4N = some (BitVec.ofNat 64 nF)) (gC : Γ.get u4Cl = some (Enc.idxW closed)) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ u4Locals)) u4Next s
      ((List.range' (i + 1) (nF - (i + 1))).anyM (u4G ks closed)) (PostB (ctxH C H)) := by
  unfold u4Next
  refine specR_congr (m' := (List.range' (i + 1) (nF - (i + 1))).anyM (u4G ks closed) >>= fun r => pure r)
    (by simp only [bind_pure]) ?_
  refine specR_callNIH (C := ctxH C H) u4R fU4 u4Params [vv u4Ks, .op .add [vv u4I, .const 1], vv u4N, vv u4Cl] u4Body
    [cellA C oks, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 nF, Enc.idxW closed] (by decide) rfl (by decide) hc.u4
    ⟨by simp [sev, gK], by simp only [sev, sev_vv]; simp [gI]; exact e_succ i, by simp [sev, gN], by simp [sev, gC], trivial⟩
    (PostB (ctxH C H)) (fun a w _ _ => w = boolW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu u4Params _ rfl hlk) (ih H s (List.prefix_refl _)))
    (fun r w s3 H3 hp3 hw => ?_)
  subst hw
  exact specR_returnI _ (boolW r) (by simp [sev, Env.get_cons]) (fun t ht => ⟨H3, hp3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- **U4's `anyM`** from field `i` on. -/
theorem u4_spec (C : Ctx) (hok : CtxOK C) (hc : CCCodes C) (ks : List NestFieldKind) (closed : EIdx) (nF oks : Nat)
    (hn : nF < 2 ^ 60) (hkl : ks.length < 2 ^ 62) :
    ∀ f i (H : List (BitVec 64)) (s : AState), nF - i = f → i ≤ nF → C.H <+: H → BlkAt H oks (ks.map kindW) →
      SpecR (σ := σ) (Pre (ctxH C H) s (u4Params.zip [cellA C oks, BitVec.ofNat 64 i, BitVec.ofNat 64 nF,
        Enc.idxW closed])) u4Body s ((List.range' i (nF - i)).anyM (u4G ks closed)) (PostB (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp hb
    have hin : i = nF := by omega
    subst hin
    refine specR_prologue (postB_locals _) (u4_none _ _) ?_
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, u4Params, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Nat.sub_self, List.range'_zero, List.anyM]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp hb
    refine specR_prologue (postB_locals _) (u4_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i nF (by omega) (by omega)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv]; simp +decide [Env.get, u4Params, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr (by omega)]) (fun _ => ?_) (fun h => absurd h (by decide))
    have hr : nF - i = (nF - (i + 1)) + 1 := by omega
    rw [hr, List.range'_succ, List.anyM]
    have ih' : ∀ (H' : List (BitVec 64)) (s' : AState), H <+: H' → SpecR (σ := σ) (Pre (ctxH C H') s'
        (u4Params.zip [cellA C oks, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 nF, Enc.idxW closed])) u4Body s'
        ((List.range' (i + 1) (nF - (i + 1))).anyM (u4G ks closed)) (PostB (ctxH C H')) :=
      fun H' s' hp' => ih (i + 1) H' s' (by omega) (by omega) (hp.trans hp') (blkAt_mono hb hp')
    refine UD.specR_heapLoadI' (C := ctxH C H) u4L (vv u4Ks) oks _ hb.1 (by decide)
      (by simp +decide [sev, Env.get, u4Params, ctxEnv]; rfl) ?_
    have hkw := ConPanqueque.T.Decl.nd_lt_iff i ks.length (by omega) (by omega)
    by_cases hil : i < ks.length
    swap
    · have hg : u4G ks closed i = pure false := by
        simp [u4G, List.getElem?_eq_none (by omega : ks.length ≤ i)]
      rw [hg]
      refine specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, u4Params, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hkw.not.mpr hil]) (fun h => absurd rfl h) (fun _ => ?_)
      simp only [pure_bind]
      exact u4_next hc ks closed nF oks i (by omega) (by omega) H ih' (by simp +decide [sev, Env.get_cons, Env.get, u4Params, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, u4Params, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, u4Params, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, u4Params, ctxEnv])
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, u4Params, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hkw.mpr hil]) (fun _ => ?_) (fun h => absurd h (by decide))
    have h1 := hb.2 i (by simpa using hil)
    rw [List.getElem_map] at h1
    refine UD.specR_heapLoadI' (C := ctxH C H) u4K _ (oks + 1 + i) _ h1 (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, u4Params, ctxEnv]; show _ = cellA C (oks + 1 + i)
          rw [← cellA_shl C (oks + 1) i (by omega), ← cellA_add8]; rfl) ?_
    by_cases hko : ks[i] = .ordinary
    · have hg : u4G ks closed i = pure false := by simp [u4G, List.getElem?_eq_getElem hil, hko]
      rw [hg]
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hko, kindW])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [pure_bind]
      exact u4_next hc ks closed nF oks i (by omega) (by omega) H ih' (by simp +decide [sev, Env.get_cons, Env.get, u4Params, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, u4Params, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, u4Params, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, u4Params, ctxEnv])
    have hg : u4G ks closed i = structUsedLater closed 0 i := by
      have : (ks[i] == NestFieldKind.ordinary) = false := by simpa using hko
      simp [u4G, List.getElem?_eq_getElem hil, this]
    rw [hg]
    have hk0 : kindW ks[i] ≠ 0#64 := fun e => hko ((kindW_eq_zero _).mp e)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hk0)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_callNIH (C := ctxH C H) u4B fSul sulParams [vv u4Cl, .const 0, vv u4I] sulBody
      [Enc.idxW closed, BitVec.ofNat 64 0, BitVec.ofNat 64 i] (by decide) rfl (by decide) hc.sulf
      ⟨(by simp +decide [sev, Env.get_cons, Env.get, u4Params, ctxEnv]), rfl, (by simp +decide [sev, Env.get_cons, Env.get, u4Params, ctxEnv]), trivial⟩
      (PostB (ctxH C H)) (fun a w _ _ => w = boolW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu sulParams _ rfl hlk)
        (sul_spec C hok hc.sul closed 0 i (by omega) H s))
      (fun b w s1 H1 hp1 hw => ?_)
    subst hw
    have hp1' : H <+: H1 := hp1
    cases b
    · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [Bool.false_eq_true]
      refine specR_mono (u4_next (σ := σ) hc ks closed nF oks i (by omega) (by omega) H1
        (fun H' s' hp' => ih' H' s' (hp1'.trans hp')) (by simp +decide [sev, Env.get_cons, Env.get, u4Params, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, u4Params, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, u4Params, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, u4Params, ctxEnv])) (fun t ht => ht)
        (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp1'.trans hp', hw, hsr⟩)
    · refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_returnI _ 1 rfl (fun t ht => ⟨H1, hp1', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
