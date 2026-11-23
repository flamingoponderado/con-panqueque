import ConPanqueque.T.Core.UnitLikeFields
import ConPanqueque.T.Core.PropRO
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `unitLikeStruct`, with `unitLikeShape` and `unitLikeShapeAt` inlined

The instance's head is a stored η family at its levels with a projection table; the argument count is the table's
parameter count; the constructor's stored type, at the instance's levels (its level parameters copied to the heap
for `instLPFast`), has the parameter binders peeled and instantiated with the arguments; then the fields loop.
-/

namespace ConPanqueque.T.WC

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc
open ConPanqueque.T.ILP (fInstLPF ilpfBody ilpf_spec CodesILP ilpParams ilpBody PostILP)
open ConPanqueque.T.CV (prefix_fillI blk_of_fillI mul8_eq)
open ConRon.Bridge

theorem RO.peelPis : ∀ (k : Nat) (h : EIdx), RO (ConRon.Arena.peelPis k h)
  | 0, h => by rw [ConRon.Arena.peelPis]; exact RO.pure _
  | k + 1, h => by
    rw [ConRon.Arena.peelPis]
    split
    · refine RO.bind (RO.viewBind h) (fun o => ?_)
      rcases o with _ | ⟨_, b⟩
      · exact RO.failDanglingE
      · exact RO.peelPis k b
    · exact RO.pure _

/-- The twin-state facts `instLPFast` needs, at a state where the structure arm runs. -/
structure UlsFacts (C : Ctx) (s : AState) : Prop where
  st : StateOK s
  rn : ReadNCacheOK s.caches.readNC s.store
  rl : ReadLCacheOK s.caches.readLC s.store
  rls : ReadLsCacheOK s.caches.readLsC s.store
  ctor : ∀ c cv np nf ind, C.fe.find? c = some (.ctorInfo cv np nf ind) →
    (∃ ks, Frontend.denoteNList s.store.ns cv.levelParams = some ks) ∧ (denoteE s.store cv.type).isSome = true
  ls : ∀ us uh, s.store.lss.view us = some uh → ∃ vs, denoteLs s.store.lss us = some vs

structure UlsCodes (C : Ctx) : Prop where
  mg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  mp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  af : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  gaa : C.code.lookup ExG.fGaa = some ([(pFu, .one), (pH, .one)], ExG.gaaBody C, .one)
  ilpf : C.code.lookup fInstLPF = some (ilpParams.map (fun p => (p, ShapeHOL.one)), ilpfBody C, .one)
  ilp : CodesILP C (ilpBody C)
  pp : C.code.lookup fPp = some (ppParams.map (fun p => (p, ShapeHOL.one)), ppBody, .one)
  irr : C.code.lookup ExQ.fIrr = some (ExQ.irrParams.map (fun p => (p, ShapeHOL.one)), ExQ.irrBody C, .one)
  q : ExQ.CodesQ C
  ulf : C.code.lookup fUlf = some (ulfParams.map (fun p => (p, ShapeHOL.one)), ulfBody, .one)
  ulfc : UlfCodes C

section
variable {σ : Type}

theorem uls_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx)
    (hok : CtxOK C) (hc : UlsCodes C) (Q : AState → Prop) (F : Nat)
    (hQF : ∀ s, Q s → UlsFacts C s)
    (hLPl : ∀ c ci, C.fe.find? c = some ci → ci.toConstantVal.levelParams.length + 1 < 2 ^ 60)
    (hQi : ∀ s1 d T b s2, Q s1 → isPropType (knot mode C n) d T s1 = .ok (b, s2) → Q s2)
    (hQf : ∀ s1 i ty h s2, Q s1 → internE (.fvar i ty) s1 = .ok (h, s2) → Q s2)
    (hQ1 : ∀ s1 fu e v d h s2, Q s1 → instantiate1Fast fu e v d s1 = .ok (h, s2) → Q s2)
    (hQl : ∀ s1 d T b s2, Q s1 → unitLikeLoop (knot mode C n) C.fe F d T s1 = .ok (b, s2) → Q s2)
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
    (hUL : ∀ (H : List (BitVec 64)) s1 d T, C.H <+: H → Q s1 → d < 2 ^ 64 →
      SpecR (σ := σ) (Pre (ctxH C H) s1 (ullParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, BitVec.ofNat 64 F, Enc.idxW T]))
        ullBody s1 (unitLikeLoop (knot mode C n) C.fe F d T) (PostB (ctxH C H))) :
    ∀ (H : List (BitVec 64)) (s : AState) (d : Nat) (w : EIdx), C.H <+: H → Q s → d < 2 ^ 64 →
      SpecR (σ := σ) (Pre (ctxH C H) s (ulsParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, BitVec.ofNat 64 F, Enc.idxW w]))
        (ulsBody C) s (unitLikeStruct (knot mode C n) (unitLikeLoop (knot mode C n) C.fe F) C.fe d w) (PostB (ctxH C H)) := by
  intro H s d w hpH hq hd
  refine specR_prologue (postB_locals _) (Knot.params_none _ ulsLocals ulsParams _ (by decide) (by decide)) ?_
  unfold unitLikeStruct unitLikeShape
  simp only [bind_assoc]
  refine specR_callNIM (C := ctxH C H) ulsH fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv ulsW]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW w] (by decide) rfl (by decide) hc.af
    ⟨rfl, by simp +decide [Env.get, ulsParams, ctxEnv], trivial⟩
    (fun a w' s' st => getAppFn coreWalkFuel w s = .ok (a, s') ∧ Post (ctxH C H) s a w' s' st)
    (fun a w' s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec (ctxH C H) hc.af coreWalkFuel w s CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide),
        hlk 1 (by decide)⟩))
    (fun hh w' s' st ⟨hrun, hw, hs, _⟩ => ?_)
  subst hw
  have hs' : s = s' := hs.symm
  subst hs'
  refine Knot.specR_tagIteV ulsH hh 3 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
  swap
  · rw [if_neg (show ¬ (hh.tag == ETag.const) = true by simpa [ETag.const] using htg)]
    simp only [pure_bind]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rw [if_pos (show (hh.tag == ETag.const) = true by simp [htg, ETag.const])]
  simp only [bind_assoc]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv ulsH) (Enc.idxW hh) (by decide) (by simp) ?_
  refine specR_viewP (C := ctxH C H) hh (by simp) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
    (fun v P hv htn _ => ?_)
  refine specR_congr (Big.view_bind_eq hh v _ s hv) ?_
  have h3 : v.tagN = 3 := by rw [htn, htg]; rfl
  obtain ⟨S, us, rfl⟩ := UD.tagN_const h3
  dsimp only
  try simp only [bind_assoc]
  refine specR_loadI' ulsS (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW S) (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW S) [Enc.idxW us] []) ?_
  refine specR_loadI' ulsU _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW us) (by decide) (by simp +decide [sev]) rfl
    (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW S) (Enc.idxW us) [] []) ?_
  refine specR_dropM ?_
  refine specR_envFindI (C := ctxH C H) (ctxOK_H hok H) hc.mg hc.mp ulsP (vv ulsS) S (by decide) (by simp)
    (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  have hrel := find_rel hok S
  try rw [show (ctxH C H).envM = C.envM from rfl]
  revert hrel
  rcases hfind : C.fe.find? S with _ | ci
  · intro hrel; simp only at hrel; rw [hrel]
    refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    dsimp only
    try simp only [bind_assoc]
    simp only [pure_bind]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  intro ⟨o, hm, hci⟩
  rw [hm]
  refine specR_atEntry fun t ht => ?_
  have hoE : o < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE) (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI ulsQ _ (ecell C o) (by decide) (by simp [sev, optWG]; exact BitVec.add_sub_cancel _ _) ?_
  rcases ci with cv | ⟨cv, val, hint⟩ | cv | ⟨cv, caps⟩ | ⟨cv, np, nf, ind⟩ | ⟨cv, mi, rp, isK, rules⟩
  · refine specR_envLoadI ulsTg (vv ulsQ) o _ (by decide) (by simp [sev]; rfl) (by exact hci.2) ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    dsimp only
    try simp only [bind_assoc]
    simp only [pure_bind]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_envLoadI ulsTg (vv ulsQ) o _ (by decide) (by simp [sev]; rfl) (by exact hci.2.1) ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    dsimp only
    try simp only [bind_assoc]
    simp only [pure_bind]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_envLoadI ulsTg (vv ulsQ) o _ (by decide) (by simp [sev]; rfl) (by exact hci.2) ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    dsimp only
    try simp only [bind_assoc]
    simp only [pure_bind]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · obtain ⟨hcv, htag, het, -, -, -, -, -⟩ := hci
    simp only [IConstantInfo.toConstantVal] at hcv
    obtain ⟨_, ⟨wl, hwl, ol, hwl', hbl⟩, hty⟩ := hcv
    subst hwl'
    refine specR_envLoadI ulsTg (vv ulsQ) o _ (by decide) (by simp [sev]; rfl) htag ?_
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    dsimp only
    try simp only [bind_assoc]
    refine specR_envLoadI ulsEt (.op .add [vv ulsQ, .const 32]) (o + 4) _ (by decide)
      (by simp [sev]; exact UD.ecell_add32 C o) het ?_
    refine specR_envLoadI ulsLp0 (.op .add [vv ulsQ, .const 16]) (o + 2) _ (by decide)
      (by simp [sev]; exact UD.ecell_add16 C o) (by rw [show o + 2 = o + 1 + 1 by omega]; exact hwl) ?_
    refine specR_envLoadI ulsLl0 (vv ulsLp0) ol _ (by decide) (by first | rfl | (simp; rfl) | simp) hbl.1 ?_
    refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    refine specR_assignI lDh (vv ulsU) (Enc.idxW us) (by decide) (by simp) ?_
    refine specR_lsviewPI (C := ctxH C H) us (by simp) (by simp <;> rfl) (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide)
      (fun vl Pl hvl _ hvll => ?_)
    refine specR_runBind (viewLsLen_run us s vl hvl) ?_
    dsimp only
    try simp only [bind_assoc]
    simp only [List.length_map]
    have hlpl : cv.levelParams.length + 1 < 2 ^ 60 := by simpa [IConstantInfo.toConstantVal] using hLPl S _ hfind
    have hvl' : vl.length < 2 ^ 61 := by simpa using hvll
    have hwe : (BitVec.ofNat 64 vl.length = BitVec.ofNat 64 cv.levelParams.length) ↔ vl.length = cv.levelParams.length :=
      ⟨fun e => by have := congrArg BitVec.toNat e; simp at this; omega, fun e => by rw [e]⟩
    by_cases hc1 : caps.eta = true ∧ vl.length = cv.levelParams.length
    swap
    · refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rcases Bool.eq_false_or_eq_true caps.eta with he | he <;>
          simp_all [boolW, hwe]) (fun h => absurd rfl h) (fun _ => ?_)
      rw [if_neg hc1]
      simp only [pure_bind]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hc1.1, boolW, hwe.mpr hc1.2]) (fun _ => ?_) (fun h => absurd h (by decide))
    rw [if_pos hc1]
    try simp only [bind_assoc]
    refine specR_tblFindI (C := ctxH C H) (ctxOK_H hok H) hc.mg hc.mp ulsTb (vv ulsS) S (by decide)
      (by simp) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    have hrel := tbl_rel hok S
    try rw [show (ctxH C H).tblM = C.tblM from rfl]
    revert hrel
    rcases hft : C.fe.findTable? S with _ | tb
    · intro hrel; simp only at hrel; rw [hrel]
      refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      dsimp only
      try simp only [bind_assoc]
      simp only [pure_bind]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    intro ⟨ot, hmt, htb⟩
    rw [hmt]
    dsimp only
    try simp only [bind_assoc]
    try simp only [bind_assoc]
    refine specR_atEntry fun t ht => ?_
    have hoT : ot < C.EN := Nat.lt_of_lt_of_le (tblE_lt htb) ht.sr.env.1.len
    refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoT) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI ulsTq _ (ecell C ot) (by decide) (by simp [sev, optWG]; exact BitVec.add_sub_cancel _ _) ?_
    obtain ⟨_, _, hnp, hctor, hnf, _⟩ := htb
    refine specR_envLoadI ulsNp (.op .add [vv ulsTq, .const 16]) (ot + 2) _ (by decide)
      (by simp [sev]; exact UD.ecell_add16 C ot) hnp.1 ?_
    refine specR_envLoadI ulsCt (.op .add [vv ulsTq, .const 24]) (ot + 3) _ (by decide)
      (by simp [sev]; exact ecell_add24 C ot) hctor ?_
    refine specR_envLoadI ulsNf (.op .add [vv ulsTq, .const 32]) (ot + 4) _ (by decide)
      (by simp [sev]; exact UD.ecell_add32 C ot) hnf.1 ?_
    refine specR_callNIH (C := ctxH C H) ulsA ExG.fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv ulsW]
      (ExG.gaaBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW w] (by decide) rfl (by decide) hc.gaa
      ⟨rfl, by simp +decide [Env.get, ulsParams, ctxEnv], trivial⟩
      (fun a w' s' st => getAppArgs coreWalkFuel w s = .ok (a, s') ∧ PostA (ctxH C H) a w' s' st)
      (fun a w' s' H3 => getAppArgs coreWalkFuel w s = .ok (a, s') ∧ ∃ o3, w' = cellA C o3 ∧ BlkAt H3 o3 (a.map Enc.idxW))
      (fun a w' s' st ⟨hr, H3, o3, hp, hw, hb, hsr⟩ => ⟨H3, hp, ⟨hr, o3, hw, hb⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
        (ExG.gaa_spec (ctxH C H) (ctxOK_H hok H) hc.gaa coreWalkFuel CV.coreWalkFuel_lt H w s)))
      (fun targs w2 s3 H3 hp3 ⟨hra, oa, hw, hba⟩ => ?_)
    subst hw
    have hs3 : s3 = s := RO.getAppArgs _ _ _ _ _ hra
    subst s3
    have hok3 := ctxOK_H hok H3
    refine UD.specR_heapLoadI' (C := ctxH C H3) ulsAl (vv ulsA) oa _ hba.1 (by decide) (by simp; rfl) ?_
    refine specR_atEntry fun t3 ht3 => ?_
    have htl := blk_small0 hok3 ht3.sr hba
    simp only [List.length_map] at htl
    have hnp2 := hnp.2
    have hnf2 := hnf.2
    by_cases hA : targs.length = tb.numParams
    swap
    · have hne : BitVec.ofNat 64 targs.length ≠ BitVec.ofNat 64 tb.numParams := by
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun _ => ?_) (fun h => absurd h (by decide))
      rw [if_neg hA]
      simp only [pure_bind]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H3, hp3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hA]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [if_pos hA]
    try simp only [bind_assoc]
    have hlt59 : BitVec.ofNat 64 targs.length < BitVec.ofNat 64 (2 ^ 59) := by
      rw [BitVec.lt_def, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; norm_num; omega
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; first | exact hlt59 | omega) (fun _ => ?_) (fun h => absurd h (by decide))
    unfold unitLikeShapeAt
    try simp only [bind_assoc]
    refine specR_envFindI (C := ctxH C H3) hok3 hc.mg hc.mp ulsP2 (vv ulsCt) tb.ctor (by decide) (by simp)
      (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
    have hrel2 := find_rel hok tb.ctor
    try rw [show (ctxH C H3).envM = C.envM from rfl]
    revert hrel2
    rcases hf2 : C.fe.find? tb.ctor with _ | ci
    · intro hrel2; simp only at hrel2; rw [hrel2]
      refine specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      dsimp only
      try simp only [bind_assoc]
      simp only [pure_bind]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H3, hp3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    intro ⟨o2, hm2, hci2⟩
    rw [hm2]
    refine specR_atEntry fun t4 ht4 => ?_
    have hoE2 : o2 < C.EN := Nat.lt_of_lt_of_le (cie_lt hci2) ht4.sr.env.1.len
    refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE2) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI ulsQ2 _ (ecell C o2) (by decide) (by simp [sev, optWG]; exact BitVec.add_sub_cancel _ _) ?_
    rcases ci with cv | ⟨cv, val, hint⟩ | cv | ⟨cv, caps⟩ | ⟨cv, np, nf, ind⟩ | ⟨cv, mi, rp, isK, rules⟩
    · refine specR_envLoadI ulsTg2 (vv ulsQ2) o2 _ (by decide) (by simp [sev]; rfl) (by exact hci2.2) ?_
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      dsimp only
      try simp only [bind_assoc]
      simp only [pure_bind]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H3, hp3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_envLoadI ulsTg2 (vv ulsQ2) o2 _ (by decide) (by simp [sev]; rfl) (by exact hci2.2.1) ?_
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      dsimp only
      try simp only [bind_assoc]
      simp only [pure_bind]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H3, hp3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_envLoadI ulsTg2 (vv ulsQ2) o2 _ (by decide) (by simp [sev]; rfl) (by exact hci2.2) ?_
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      dsimp only
      try simp only [bind_assoc]
      simp only [pure_bind]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H3, hp3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_envLoadI ulsTg2 (vv ulsQ2) o2 _ (by decide) (by simp [sev]; rfl) (by exact hci2.2.1) ?_
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      dsimp only
      try simp only [bind_assoc]
      simp only [pure_bind]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H3, hp3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · obtain ⟨hcv2, htag2, -, -, -⟩ := hci2
      simp only [IConstantInfo.toConstantVal] at hcv2
      obtain ⟨_, ⟨wl2, hwl2, ol2, hwl2', hbl2⟩, hty2⟩ := hcv2
      subst hwl2'
      refine specR_envLoadI ulsTg2 (vv ulsQ2) o2 _ (by decide) (by simp [sev]; rfl) htag2 ?_
      refine specR_ifI _ 0 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
      dsimp only
      try simp only [bind_assoc]
      have hlpc : cv.levelParams.length + 1 < 2 ^ 60 := by simpa [IConstantInfo.toConstantVal] using hLPl tb.ctor _ hf2
      have hl0 : C.EH[ol2]? = some (BitVec.ofNat 64 cv.levelParams.length) := by simpa using hbl2.1
      refine specR_envLoadI (C := ctxH C H3) ulsLp (.op .add [vv ulsQ2, .const 16]) (o2 + 2) _ (by decide)
        (by simp [sev]; exact UD.ecell_add16 C o2) (by rw [show o2 + 2 = o2 + 1 + 1 by omega]; exact hwl2) ?_
      refine specR_envLoadI (C := ctxH C H3) ulsLl (vv ulsLp) ol2 _ (by decide) (by first | rfl | (simp; rfl) | simp) hl0 ?_
      refine specR_assignI lCn _ (BitVec.ofNat 64 (cv.levelParams.length + 1)) (by decide)
        (by simp +decide [sev, Env.get]; exact word_add1_eq _) ?_
      refine specR_allocI (C := ctxH C H3) ulsB (.panop .mul [vv lCn, .const 8]) (cv.levelParams.length + 1)
        (by omega) (by decide) (fun v => by simp +decide [sev, Env.get]; exact mul8_eq _)
        (fun H' wsN hpre hwl3 hcap => ?_)
      refine specR_assignI lSrc (vv ulsLp) (ecell C ol2) (by decide) (by simp +decide [sev, Env.get]; rfl) ?_
      refine specR_assignI lDst (vv ulsB) (cellA C H'.length) (by decide) (by simp +decide [sev, Env.get]; rfl) ?_
      refine specR_assignI lCi (.const 0) 0 (by decide) rfl ?_
      have hws : (BitVec.ofNat 64 cv.levelParams.length :: cv.levelParams.map Enc.idxW).length =
          cv.levelParams.length + 1 := by simp
      refine specR_copyEI (C := C) hok (H' ++ wsN) (BitVec.ofNat 64 cv.levelParams.length :: cv.levelParams.map Enc.idxW)
        ol2 H'.length (by decide) (fun j hj => ?_) (by simp [hwl3]) (by rw [hws]; omega)
        (by rw [hws]; simp +decide [Env.get]) (by decide) (by simp +decide [Env.get, ulsParams, ctxEnv]) ?_
      · rcases j with _ | j
        · simpa using hl0
        · have := hbl2.2 j (by simp at hj ⊢; omega)
          simp only [List.getElem_cons_succ]
          rw [show ol2 + (j + 1) = ol2 + 1 + j by omega]; simpa using this
      have hblk2 := blk_of_fillI (H' ++ wsN) (BitVec.ofNat 64 cv.levelParams.length :: cv.levelParams.map Enc.idxW)
        H'.length (cv.levelParams.map Enc.idxW) (by simp) (by simp [hwl3])
      have hPF0 : H3 <+: fillI (H' ++ wsN) (BitVec.ofNat 64 cv.levelParams.length :: cv.levelParams.map Enc.idxW)
          H'.length (BitVec.ofNat 64 cv.levelParams.length :: cv.levelParams.map Enc.idxW).length :=
        prefix_fillI _ _ _ H3 (hpre.length_le) (hpre.trans (List.prefix_append _ _)) _
      refine specR_envLoadI ulsT (.op .add [vv ulsQ2, .const 24]) (o2 + 3) _ (by decide)
        (by simp +decide [sev, Env.get, ulsParams, ctxEnv]; exact fn_ecell24 C o2) (by rw [show o2 + 3 = o2 + 1 + 2 by omega]; exact hty2) ?_
      have hF := hQF s hq
      obtain ⟨ks, hks⟩ := (hF.ctor tb.ctor cv np nf ind hf2).1
      have hden := (hF.ctor tb.ctor cv np nf ind hf2).2
      obtain ⟨vsL, hus⟩ := hF.ls us vl hvl
      refine specR_callNIH ulsY fInstLPF ilpParams [.const (BitVec.ofNat 64 coreWalkFuel), vv ulsT, vv ulsB, vv ulsU]
        (ilpfBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW cv.type, cellA C H'.length, Enc.idxW us] (by decide) rfl
        (by decide) hc.ilpf
        ⟨rfl, by simp +decide [sev, Env.get], by simp +decide [sev, Env.get]; rfl,
          by simp +decide [sev, Env.get, ulsParams, ctxEnv], trivial⟩
        (fun a w' s' st => instLPFast coreWalkFuel cv.levelParams us cv.type s = .ok (a, s') ∧
          PostILP (ctxH C _) a w' s' st)
        (fun a w' s' _ => instLPFast coreWalkFuel cv.levelParams us cv.type s = .ok (a, s') ∧ w' = Enc.idxW a)
        (fun a w' s' st ⟨hrun, H'', hp, hw, hsr⟩ => ⟨H'', hp, ⟨hrun, hw⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu ilpParams _ rfl hlk)
          (ilpf_spec ra C hok hc.ilp coreWalkFuel CV.coreWalkFuel_lt H'.length cv.levelParams ks us vsL _ s cv.type
            hks hus hF.st hF.rn hF.rl hF.rls hden hblk2)))
        (fun cty w4 s4 H4 hp4 ⟨hrun4, hw4⟩ => ?_)
      subst hw4
      have hq4 := hQs _ _ _ _ _ _ _ hq hrun4
      have hp34 : H3 <+: H4 := hPF0.trans hp4
      refine specR_callNIH (C := ctxH C H4) ulsK fPp ppParams [vv ulsNp, vv ulsY] ppBody
        [BitVec.ofNat 64 tb.numParams, Enc.idxW cty] (by decide) rfl (by decide) hc.pp
        ⟨by simp, by simp, trivial⟩
        (fun a w' s' st => peelPis tb.numParams cty s4 = .ok (a, s') ∧ UD.PostO (ctxH C H4) a w' s' st)
        (fun a w' s' _ => peelPis tb.numParams cty s4 = .ok (a, s') ∧ w' = optW a)
        (fun a w' s' st ⟨hrun, H'', hp, hw, hsr⟩ => ⟨H'', hp, ⟨hrun, hw⟩, hsr⟩)
        (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu ppParams _ rfl hlk)
          (pp_spec (ctxH C H4) (ctxOK_H hok H4) hc.pp tb.numParams cty s4 (by omega))))
        (fun ob w5 s5 H5 hp5 ⟨hrun5, hw5⟩ => ?_)
      subst hw5
      have hs5 : s5 = s4 := RO.peelPis _ _ _ _ _ hrun5
      subst s5
      have hp35 : H3 <+: H5 := hp34.trans hp5
      rcases ob with _ | body
      · refine specR_ifI _ 1 (by simp [sev, optW, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
        dsimp only
        try simp only [bind_assoc]
        simp only [pure_bind]
        exact specR_returnI _ 0 rfl (fun t ht => ⟨H5, hp3.trans hp35, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      refine specR_ifI _ 0 (by simp [sev, optW, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact idxW_add_one_ne' body) (fun h => absurd rfl h) (fun _ => ?_)
      refine specR_assignI ulsBd _ (Enc.idxW body) (by decide) (by simp [sev, optW, optWG]; exact BitVec.add_sub_cancel _ _) ?_
      dsimp only
      try simp only [bind_assoc]
      simp only [instantiateListFast, List.size_toArray, bind_assoc]
      refine callE_specR (C := ctxH C H5) ulsO ExQ.fIrr ExQ.irrParams
        [vv ulsA, .const 0, vv ulsAl, .const (BitVec.ofNat 64 coreWalkFuel), vv ulsBd, .const 0] (ExQ.irrBody C)
        [cellA C oa, BitVec.ofNat 64 0, BitVec.ofNat 64 targs.length, BitVec.ofNat 64 coreWalkFuel, Enc.idxW body,
          BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.irr
        ⟨by simp, rfl, by simp, rfl, by simp, rfl, trivial⟩
        (ExQ.irr_spec ra (ctxH C H5) (ctxOK_H hok H5) (codesQ_H hc.q H5) targs.toArray oa
          (show BlkAt H5 oa (targs.toArray.toList.map Enc.idxW) by simpa using blkAt_mono hba hp35) (by simp; omega) s4
          coreWalkFuel 0 targs.length 0 body CV.coreWalkFuel_lt (by decide) (by omega) (by decide)) (fun tele s6 hr6 => ?_)
      have hq6 := hQr _ _ _ _ _ _ _ _ _ hq4 hr6
      simp only [pure_bind]
      refine specR_congr (m' := unitLikeFields (knot mode C n) (unitLikeLoop (knot mode C n) C.fe F) tb.numFields d tele >>= fun r => pure r)
        (by simp) ?_
      refine specR_callNIH (C := ctxH C H5) ulsR fUlf ulfParams [vv kFu, vv kD, vv ulsF, vv ulsNf, vv ulsO] ulfBody
        [BitVec.ofNat 64 n, BitVec.ofNat 64 d, BitVec.ofNat 64 F, BitVec.ofNat 64 tb.numFields, Enc.idxW tele] (by decide) rfl
        (by decide) hc.ulf
        ⟨by simp +decide [Env.get, ulsParams, ctxEnv], by simp +decide [Env.get, ulsParams, ctxEnv], by simp +decide [Env.get, ulsParams, ctxEnv], by simp, by simp, trivial⟩
        (PostB (ctxH C H5)) (fun b w' _ _ => w' = boolW b) (fun b w' s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ulfParams _ rfl hlk)
          (ulf_spec ra mode n C hok hc.ulfc Q F hQi hQf hQ1 hQl hIO hW hLE hUL tb.numFields d tele H5 s6
            (hpH.trans (hp3.trans hp35)) hq6 (by omega) hd))
        (fun r w7 s7 H7 hp7 hw7 => ?_)
      exact specR_returnI _ w7 (by simp) (fun t ht => ⟨H7, hp3.trans (hp35.trans hp7), hw7, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

    · refine specR_envLoadI ulsTg2 (vv ulsQ2) o2 _ (by decide) (by simp [sev]; rfl) (by exact hci2.2.1) ?_
      refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      dsimp only
      try simp only [bind_assoc]
      simp only [pure_bind]
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H3, hp3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

  · refine specR_envLoadI ulsTg (vv ulsQ) o _ (by decide) (by simp [sev]; rfl) (by exact hci.2.1) ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    dsimp only
    try simp only [bind_assoc]
    simp only [pure_bind]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_envLoadI ulsTg (vv ulsQ) o _ (by decide) (by simp [sev]; rfl) (by exact hci.2.1) ?_
    refine specR_ifI _ 1 (by simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    dsimp only
    try simp only [bind_assoc]
    simp only [pure_bind]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
