import ConPanqueque.T.Core.FamilyNZ
import ConPanqueque.T.Core.CheckGuard
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `projGuardSort`

The sort a projection's rows answer to, at this use (`none`: the guard asks nothing): a stored type ending in
a sort answers `Prop` (the zero-level pin) when that sort is always zero; otherwise the sort is walked to at the
use's levels (`formerSortLoop`) and is the guard unless it is never zero. The answer is a level handle `+ 1`
(`0` for `none`). The code follows `formerNeverZeroAt`'s (`FamilyNZ`).
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc
open ConPanqueque.T.ILP (fInstLPF ilpfBody ilpf_spec CodesILP ilpParams ilpBody PostILP)
open ConPanqueque.T.CV (prefix_fillI blk_of_fillI mul8_eq)

theorem isAlwaysZero_eq (l : ConLeche.Level) :
    l.isAlwaysZero = ConLeche.Level.zeroWhereZero .zero l := by
  unfold ConLeche.Level.isAlwaysZero ConLeche.Level.zeroWhereZero
  simp only [ConLeche.Level.zeronessOf]
  cases ConLeche.Level.zeronessOf l with
  | never => rfl
  | ifAllZero qs => cases qs <;> simp

def gsCore (C : Ctx) : ProgHOL 64 :=
  (.seq (.assign .local fzT (.load .one (.op .add [vv fzQ, .const 24])))
  (.seq (.call (some (some (.local, fzR), none)) fFs [vv fzT])
  (.ite (.cmp .notEqual (vv fzR) (.const 0))
    (.seq (.assign .local fzX (.load .one (.const (ecell C (C.PO + pinCount + 1)))))
    (.seq (.call (some (some (.local, fzZ), none)) fZw [vv fzX, .op .sub [vv fzR, .const 1]])
      (.ite (vv fzZ) (.return (.op .add [vv fzX, .const 1])) (.return (.const 0)))))
  (.seq (.assign .local fzP (.load .one (.op .add [vv fzQ, .const 16])))
  (.seq (.assign .local fzL (.load .one (vv fzP)))
  (.seq (.assign .local lCn (.op .add [vv fzL, .const 1]))
  (allocP C fzB (.panop .mul [vv lCn, .const 8])
  (.seq (.assign .local lSrc (vv fzP))
  (.seq (.assign .local lDst (vv fzB))
  (.seq (.assign .local lCi (.const 0))
  (.seq copyLoop
  (.seq (.call (some (some (.local, fzY), none)) fInstLPF
      [.const (BitVec.ofNat 64 coreWalkFuel), vv fzT, vv fzB, vv fzU])
  (.seq (.assign .local fzA (.load .one (.op .add [vv fzQ, .const 48])))
  (.seq (.assign .local fzI (.load .one (.op .add [vv fzQ, .const 56])))
  (.seq (.call (some (some (.local, fzS), none)) fFsl [vv kFu, .const 0, .op .add [vv fzA, vv fzI], vv fzY])
  (.ite (.cmp .equal (vv fzS) (.const 0)) hang
  (.seq (.call (some (some (.local, fzZ), none)) fNz0 [.op .sub [vv fzS, .const 1]])
    (.ite (vv fzZ) (.return (.const 0)) (.return (vv fzS))))))))))))))))))))


def gsBody (C : Ctx) : ProgHOL 64 := prologue fzLocals (gsCore C)

section
variable {σ : Type}

/-- `0` for `none`, else a level handle `+ 1` reading back to the guard sort. -/
def PostGS (C : Ctx) (o : Option ConLeche.Level) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧ (o = none → w = 0) ∧
    ∀ l, o = some l → ∃ h : LIdx, w = Enc.idxW h + 1 ∧ denoteL s'.store.ls h = some l

theorem postGS_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostGS C a w s' st → PostGS C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h1, h2⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h1, h2⟩

theorem gs_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (hc : FzCodes C) (hzw : ZwCodes C) (hn : n < 2 ^ 64)
    (hW : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ d e', Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d e')
      (PostK (ctxH C H)))
    (s : AState) (d : Nat) (cvT : IConstantVal) (caps : IIndCaps) (o : Nat)
    (hci : CIE C.EB C.EH o (.indInfo cvT caps)) (us : LsIdx)
    (hwf : LStoreWF s.store.ls) (hst : StateOK s)
    (ks : List ConLeche.Name) (hks : Frontend.denoteNList s.store.ns cvT.levelParams = some ks)
    (vs : List ConLeche.Level) (hus : denoteLs s.store.lss us = some vs)
    (hrn : ReadNCacheOK s.caches.readNC s.store) (hrl : ReadLCacheOK s.caches.readLC s.store)
    (hrls : ReadLsCacheOK s.caches.readLsC s.store) (hden : (denoteE s.store cvT.type).isSome = true)
    (hsd : ∀ u, formerResSort cvT.type s = .ok (some u, s) → (denoteL s.store.ls u).isSome = true)
    (hsl : ∀ ty s2 u s3, instLPFast coreWalkFuel cvT.levelParams us cvT.type s = .ok (ty, s2) →
      formerSortLoop (knot mode C n) 0 (caps.nparams + caps.nIdx) ty s2 = .ok (some u, s3) →
      (denoteL s3.store.ls u).isSome = true ∧ LStoreWF s3.store.ls ∧ ReadLCacheOK s3.caches.readLC s3.store)
    (hlen : cvT.levelParams.length + 1 < 2 ^ 60) (hK : caps.nparams + caps.nIdx < 2 ^ 63)
    (hz0 : denoteL s.store.ls C.pins.zeroLevel = some .zero) :
    SpecR (σ := σ) (Pre C s (fzParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, ecell C o, Enc.idxW us]))
      (gsBody C) s (projGuardSort (knot mode C n) cvT caps us) (PostGS C) := by
  obtain ⟨hcv, -, -, -, ⟨hnpW, -⟩, ⟨hniW, -⟩, -, -⟩ := hci
  have hcv' : CVE C.EB C.EH (o + 1) cvT := hcv
  obtain ⟨_, ⟨wl, hwl, o', hwl', hblk⟩, hty⟩ := id hcv'
  subst hwl'
  refine specR_prologue (postGS_locals C) (fz_none C _) ?_
  unfold gsCore
  refine specR_envLoadI fzT (.op .add [vv fzQ, .const 24]) (o + 3) _ (by decide)
    (by simp +decide [sev, Env.get, fzParams, ctxEnv]; exact fn_ecell24 C o) (by simpa [Nat.add_assoc] using hty) ?_
  refine specR_congr (m' := formerResSort cvT.type >>= fun r =>
      match r with
      | some s => readLevelM s >>= fun sl => pure (if sl.isAlwaysZero then some .zero else none)
      | none => instLPFast coreWalkFuel cvT.levelParams us cvT.type >>= fun ty =>
          formerSortLoop (knot mode C n) 0 (caps.nparams + caps.nIdx) ty >>= fun o =>
          match o with
          | some s => readLevelM s >>= fun sl =>
              pure (if (ConLeche.Level.zeronessOf sl).isNever then none else some sl)
          | none => fail (.invalid "projection from a structure whose type reaches no sort"))
    (by simp only [projGuardSort, bind_assoc] <;> rfl) ?_
  refine specR_callNIH fzR fFs [fsT] [vv fzT] fsBody [Enc.idxW cvT.type] (by decide) rfl (by decide) hc.fs
    ⟨by simp +decide [sev, Env.get], trivial⟩
    (fun a w s' st => formerResSort cvT.type s = .ok (a, s') ∧ PostOL C s a w s' st)
    (fun a w s' _ => formerResSort cvT.type s = .ok (a, s') ∧ s' = s ∧ w = optWG Enc.idxW a)
    (fun a w s' st ⟨hrun, h1, h2, H', hp, h3⟩ => ⟨H', hp, ⟨hrun, h1, h2⟩, by subst h1; exact h3⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [fsT] _ rfl hlk) (fs_spec C hc.pir s cvT.type)))
    (fun r w s1 H1 hp1 ⟨hrun, hs1, hw⟩ => ?_)
  subst s1 hw
  rcases r with _ | u
  · refine specR_ifI _ 0 (by simp +decide [sev, Env.get, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    dsimp only
    have hl0 : C.EH[o']? = some (BitVec.ofNat 64 cvT.levelParams.length) := by simpa using hblk.1
    refine specR_envLoadI (C := ctxH C H1) fzP (.op .add [vv fzQ, .const 16]) (o + 2) _ (by decide)
      (by simp +decide [sev, Env.get, fzParams, ctxEnv]; exact fn_ecell16 C o)
      (by simpa [Nat.add_assoc] using hwl : C.EH[o + 2]? = _) ?_
    refine specR_envLoadI (C := ctxH C H1) fzL (vv fzP) o' _ (by decide) (by simp +decide [Env.get]; rfl) hl0 ?_
    refine specR_assignI lCn _ (BitVec.ofNat 64 (cvT.levelParams.length + 1)) (by decide)
      (by simp +decide [sev, Env.get]; exact word_add1_eq _) ?_
    refine specR_allocI (C := ctxH C H1) fzB (.panop .mul [vv lCn, .const 8]) (cvT.levelParams.length + 1)
      (by omega) (by decide) (fun v => by simp +decide [sev, Env.get]; exact mul8_eq _)
      (fun H' wsN hpre hwl2 hcap => ?_)
    refine specR_assignI lSrc (vv fzP) (ecell C o') (by decide) (by simp +decide [sev, Env.get]; rfl) ?_
    refine specR_assignI lDst (vv fzB) (cellA C H'.length) (by decide) (by simp +decide [sev, Env.get]; rfl) ?_
    refine specR_assignI lCi (.const 0) 0 (by decide) rfl ?_
    have hws : (BitVec.ofNat 64 cvT.levelParams.length :: cvT.levelParams.map Enc.idxW).length =
        cvT.levelParams.length + 1 := by simp
    refine specR_copyEI (C := C) hok (H' ++ wsN) (BitVec.ofNat 64 cvT.levelParams.length :: cvT.levelParams.map Enc.idxW)
      o' H'.length (by decide) (fun j hj => ?_) (by simp [hwl2]) (by rw [hws]; omega)
      (by rw [hws]; simp +decide [Env.get]) (by decide) (by simp +decide [Env.get, fzParams, ctxEnv]) ?_
    · rcases j with _ | j
      · simpa using hl0
      · have := hblk.2 j (by simp at hj ⊢; omega)
        simp only [List.getElem_cons_succ]
        rw [show o' + (j + 1) = o' + 1 + j by omega]; simpa using this
    have hblk2 := blk_of_fillI (H' ++ wsN) (BitVec.ofNat 64 cvT.levelParams.length :: cvT.levelParams.map Enc.idxW)
      H'.length (cvT.levelParams.map Enc.idxW) (by simp) (by simp [hwl2])
    have hPF0 : C.H <+: fillI (H' ++ wsN) (BitVec.ofNat 64 cvT.levelParams.length :: cvT.levelParams.map Enc.idxW)
        H'.length (BitVec.ofNat 64 cvT.levelParams.length :: cvT.levelParams.map Enc.idxW).length :=
      prefix_fillI _ _ _ C.H ((hp1.trans hpre).length_le) ((hp1.trans hpre).trans (List.prefix_append _ _)) _
    refine specR_callNIH fzY fInstLPF ilpParams [.const (BitVec.ofNat 64 coreWalkFuel), vv fzT, vv fzB, vv fzU]
      (ilpfBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW cvT.type, cellA C H'.length, Enc.idxW us] (by decide) rfl
      (by decide) hc.ilpf
      ⟨rfl, by simp +decide [sev, Env.get], by simp +decide [sev, Env.get]; rfl,
        by simp +decide [sev, Env.get, fzParams, ctxEnv], trivial⟩
      (fun a w s' st => instLPFast coreWalkFuel cvT.levelParams us cvT.type s = .ok (a, s') ∧
        PostILP (ctxH C _) a w s' st)
      (fun a w s' _ => instLPFast coreWalkFuel cvT.levelParams us cvT.type s = .ok (a, s') ∧ w = Enc.idxW a)
      (fun a w s' st ⟨hrun, H'', hp, hw, hsr⟩ => ⟨H'', hp, ⟨hrun, hw⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu ilpParams _ rfl hlk)
        (ilpf_spec ra C hok hc.ilp coreWalkFuel CV.coreWalkFuel_lt H'.length cvT.levelParams ks us vs _ s cvT.type
          hks hus hst hrn hrl hrls hden hblk2)))
      (fun ty w s2 H2 hp2 ⟨hrun2, hw⟩ => ?_)
    subst hw
    have hPF : C.H <+: H2 := hPF0.trans hp2
    refine specR_envLoadI (C := ctxH C H2) fzA (.op .add [vv fzQ, .const 48]) (o + 6) _ (by decide)
      (by simp +decide [sev, Env.get, fzParams, ctxEnv]; exact fz_ecell48 C o) hnpW ?_
    refine specR_envLoadI (C := ctxH C H2) fzI (.op .add [vv fzQ, .const 56]) (o + 7) _ (by decide)
      (by simp +decide [sev, Env.get, fzParams, ctxEnv]; exact fz_ecell56 C o) hniW ?_
    refine specR_callNIH (C := ctxH C H2) fzS fFsl fqParams [vv kFu, .const 0, .op .add [vv fzA, vv fzI], vv fzY]
      fqBody [BitVec.ofNat 64 n, BitVec.ofNat 64 0, BitVec.ofNat 64 (caps.nparams + caps.nIdx), Enc.idxW ty]
      (by decide) rfl (by decide) hc.fq.self
      ⟨by simp +decide [Env.get, fzParams, ctxEnv], rfl,
        by simp +decide [sev, Env.get]; exact BitVec.ofNat_add_ofNat .., by simp +decide [sev, Env.get], trivial⟩
      (fun a w s' st => formerSortLoop (knot mode C n) 0 (caps.nparams + caps.nIdx) ty s2 = .ok (a, s') ∧
        PostOK (ctxH C H2) a w s' st)
      (fun a w s' _ => formerSortLoop (knot mode C n) 0 (caps.nparams + caps.nIdx) ty s2 = .ok (a, s') ∧
        w = optWG Enc.idxW a)
      (fun a w s' st ⟨hrun, H'', hp, hw, hsr⟩ => ⟨H'', hp, ⟨hrun, hw⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu fqParams _ rfl hlk)
        (fq_spec ra mode n C hok hc.fq hW (caps.nparams + caps.nIdx) 0 ty s2 H2 hPF (by omega))))
      (fun r w s3 H3 hp3 ⟨hrun3, hw⟩ => ?_)
    subst hw
    rcases r with _ | u
    · exact specR_ifI _ 1 (by simp +decide [sev, Env.get, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => specR_hangI) (fun h => absurd h (by decide))
    · obtain ⟨hdu, hwf3, hrl3⟩ := hsl ty s2 u s3 hrun2 hrun3
      obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp hdu
      obtain ⟨X, hx, hX⟩ := readLevelM_runC u s3 l hrl3 hl
      refine specR_quiet hx rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl (fun hc => cachesOK_readLC hc X hX) ?_
      have hne : ¬ Enc.idxW u + 1 = 0 := lidxW_add_one_ne u
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
        (fun h => absurd rfl h) (fun _ => ?_)
      rw [isNever_zeronessOf]
      refine specR_callPure (C := ctxH C H3) fzZ fNz0 [nzU] [.op .sub [vv fzS, .const 1]] nzBody [Enc.idxW u] (nz l)
        (by decide) rfl (by decide) hc.nz
        ⟨by simp +decide [sev, Env.get, optWG]; exact BitVec.add_sub_cancel _ _, trivial⟩
        (PostBS (ctxH C H3) _) (fun b w _ H' => H' = H3 ∧ w = boolW b)
        (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨H3, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
        (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu [nzU] _ rfl hlk)
          (nz0_spec (ctxH C H3) hc.nz { s3 with caches := { s3.caches with readLC := X } } hwf3 l u hl))
        (fun w H4 _ ⟨eH, hw⟩ => ?_)
      subst H4; subst hw
      cases hnz : nz l
      · refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact specR_returnI _ (Enc.idxW u + 1) (by simp [optWG])
          (fun t ht => ⟨H3, hPF.trans hp3, sr_of_eq ht.sr rfl rfl rfl rfl, (fun h => by cases h),
            fun l' hl' => by cases hl'; exact ⟨u, rfl, hl⟩⟩)
      · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
        simp only [↓reduceIte]
        exact specR_returnI _ 0 rfl
          (fun t ht => ⟨H3, hPF.trans hp3, sr_of_eq ht.sr rfl rfl rfl rfl, fun _ => rfl, fun l' hl' => by cases hl'⟩)
  · have hne : ¬ Enc.idxW u + 1 = 0 := lidxW_add_one_ne u
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun _ => ?_) (fun h => absurd h (by decide))
    dsimp only
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp (hsd u hrun)
    obtain ⟨X, hx, hX⟩ := readLevelM_runC u s l hrl hl
    refine specR_quiet hx rfl rfl ⟨rfl, rfl, rfl, rfl, rfl⟩ rfl (fun hc => cachesOK_readLC hc X hX) ?_
    refine specR_envLoadI (C := ctxH C H1) fzX (.const (ecell C (C.PO + pinCount + 1))) (C.PO + pinCount + 1)
      (Enc.idxW C.pins.zeroLevel) (by decide) rfl (pin_zeroLevel_cell (ctxOK_H hok H1)) ?_
    rw [isAlwaysZero_eq]
    refine specR_callPure (C := ctxH C H1) fzZ fZw zwParams [vv fzX, .op .sub [vv fzR, .const 1]] zwBody
      [Enc.idxW C.pins.zeroLevel, Enc.idxW u] (ConLeche.Level.zeroWhereZero .zero l) (by decide) rfl (by decide) hzw.zw
      ⟨by simp, by simp +decide [sev, Env.get, optWG]; exact BitVec.add_sub_cancel _ _, trivial⟩
      (PostBS (ctxH C H1) _) (fun b w _ H' => H' = H1 ∧ w = boolW b)
      (fun b w s' st ⟨hs, hw, hsr⟩ => ⟨H1, List.prefix_refl _, ⟨rfl, hw⟩, by rw [hs]; exact hsr⟩)
      (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu zwParams _ rfl hlk)
        (zw_spec (ctxH C H1) (zwCodes_H hzw H1) { s with caches := { s.caches with readLC := X } } hwf .zero l C.pins.zeroLevel u hz0 hl))
      (fun w H2 _ ⟨eH, hw⟩ => ?_)
    subst H2; subst hw
    cases hzz : ConLeche.Level.zeroWhereZero .zero l
    · refine specR_ifI _ 0 (by simp [sev, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact specR_returnI _ 0 rfl
        (fun t ht => ⟨H1, hp1, sr_of_eq ht.sr rfl rfl rfl rfl, fun _ => rfl, fun l' hl' => by cases hl'⟩)
    · refine specR_ifI _ 1 (by simp [sev, boolW]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [↓reduceIte]
      exact specR_returnI _ (Enc.idxW C.pins.zeroLevel + 1) (by simp +decide [sev, Env.get])
        (fun t ht => ⟨H1, hp1, sr_of_eq ht.sr rfl rfl rfl rfl, (fun h => by cases h),
          fun l' hl' => by cases hl'; exact ⟨C.pins.zeroLevel, rfl, hz0⟩⟩)

end

end ConPanqueque.T.WC
