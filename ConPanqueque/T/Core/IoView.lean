import ConPanqueque.T.Core.InferProj
import ConPanqueque.T.Core.IoViewBase
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge
open ConRon.Arena

/-!
# The io grade's view of the knot, below the infer slot

`CoreFnsA.ioView r` changes only the `infer` slot. The projection guard's walks never read it, so they compute the
same at `ioView r` as at `r`; the io-grade projection arm differs from the full one only in its own subject
inference.
-/

namespace ConPanqueque.T.WC
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big
open ConPanqueque.V.Enc


theorem formerSortLoop_ioView (r : CoreFnsA) : ∀ f d e, formerSortLoop (CoreFnsA.ioView r) d f e = formerSortLoop r d f e := by
  intro f
  induction f with
  | zero => intro d e; simp only [formerSortLoop, ioView_whnf]
  | succ f ih => intro d e; simp only [formerSortLoop, ioView_whnf, ih]

theorem checkGuardRows_ioView (r : CoreFnsA) gs rows : ∀ k i, rows.size - i = k →
    checkGuardRows (CoreFnsA.ioView r) gs rows i = checkGuardRows r gs rows i := by
  intro k
  induction k with
  | zero =>
    intro i h; rw [checkGuardRows]; conv => rhs; rw [checkGuardRows]
    rw [dif_neg (by omega), dif_neg (by omega)]
  | succ k ih =>
    intro i h; rw [checkGuardRows]; conv => rhs; rw [checkGuardRows]
    simp only [ioView_whnf, ioView_inferIO, ih (i+1) (by omega)]

theorem projGuardSort_ioView (r : CoreFnsA) cvT caps us :
    projGuardSort (CoreFnsA.ioView r) cvT caps us = projGuardSort r cvT caps us := by
  simp only [projGuardSort, formerSortLoop_ioView]

theorem checkGuardRows_ioView' (r : CoreFnsA) gs rows i :
    checkGuardRows (CoreFnsA.ioView r) gs rows i = checkGuardRows r gs rows i :=
  checkGuardRows_ioView r gs rows _ i rfl

theorem checkProjGuard_ioView (r : CoreFnsA) (fe : IFEnv) e us :
    checkProjGuard (CoreFnsA.ioView r) fe e us = checkProjGuard r fe e us := by
  simp only [checkProjGuard, projGuardSort_ioView, checkGuardRows_ioView']

def pjioBody (C : Ctx) : ProgHOL 64 := prologue pjLocals
  (.seq (.call (some (some (.local, pjA), none)) fIO [(vv kFu), (vv kD), (vv ibPe)]) (.seq (.call (some (some (.local, pjTe), none)) fW [(vv kFu), (vv kD), (vv pjA)]) (.seq (.call (some (some (.local, pjHh), none)) fGetAppFn [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv pjTe)]) (.ite (tagIsE pjHh 3) (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pjHh)) (.seq eViewP (.seq (.assign .local pjT (.load .one (vv lRp))) (.seq (.assign .local pjUs (.load .one (.op .add [(vv lRp), (.const 8)]))) (tblFindP C pjTb (vv pjT) (.ite (.cmp .equal (vv pjTb) (.const 0)) hang (.seq (.assign .local pjTq (.op .sub [(vv pjTb), (.const 1)])) (.seq (.assign .local pjNf (.load .one (.op .add [(vv pjTq), (.const 32)]))) (.ite (.cmp .lower (vv ibIx) (vv pjNf)) (.seq (.call (some (some (.local, pjVa), none)) ExG.fGaa [(.const (BitVec.ofNat 64 coreWalkFuel)), (vv pjTe)]) (.ite (.cmp .notEqual (vv pjT) (vv ibSn)) hang (.seq (.assign .local pjNa (.load .one (vv pjVa))) (.seq (.assign .local pjNp (.load .one (.op .add [(vv pjTq), (.const 16)]))) (.ite (.cmp .notEqual (vv pjNa) (vv pjNp)) hang (.seq (.assign .local pjLp (.load .one (.op .add [(vv pjTq), (.const 8)]))) (.seq (.assign .local pjLl (.load .one (vv pjLp))) (.seq (.assign .local lFl (vv lFls)) (.seq (.assign .local lDh (vv pjUs)) (.seq lsViewP (.ite (.cmp .notEqual (vv lRn) (vv pjLl)) hang (.seq (.call (some (some (.local, pjG), none)) fGd [(vv kFu), (vv pjTq), (vv ibIx), (vv pjUs)]) (.seq (.call (some (some (.local, pjR), none)) fTa [(vv pjTq), (vv ibIx), (vv pjUs), (vv pjVa), (vv ibPe)]) (.return (vv pjR))))))))))))))) hang)))))))))) hang))))

structure PjioCodes (C : Ctx) : Prop where
  i : C.code.lookup fIO = some (pmap kParams, inferIOE C fIOB, .one)
  w : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one)
  af : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  gaa : C.code.lookup ExG.fGaa = some ([(pFu, .one), (pH, .one)], ExG.gaaBody C, .one)
  mg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  mp : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  gd : C.code.lookup fGd = some (gdParams.map (fun p => (p, ShapeHOL.one)), gdBody C, .one)
  ta : C.code.lookup fTa = some (taParams.map (fun p => (p, ShapeHOL.one)), taBody C, .one)

section
variable {σ : Type}

theorem pjio_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ pjLocals → (ctxEnv C ++ iprParams.zip vals).get x = none :=
  Knot.params_none C pjLocals iprParams vals (by decide) (by decide)

theorem pjio_spec (mode : ConLeche.CheckMode) (n : Nat) (C : Ctx) (hok : CtxOK C) (hc : PjioCodes C)
    (Q : AState → Prop)
    (hI : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → d' < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (inferIOE C fIOB) s1 ((knot mode C n).inferIO d' e')
      (PostK (ctxH C H)))
    (hW : ∀ (H : List (BitVec 64)) s1 d' e', C.H <+: H → d' < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 n, BitVec.ofNat 64 d', Enc.idxW e'] (whnfE C fWB) s1 ((knot mode C n).whnf d' e')
      (PostK (ctxH C H)))
    (hQi : ∀ s1 d' e' a s2, Q s1 → (knot mode C n).inferIO d' e' s1 = .ok (a, s2) → Q s2)
    (hQw : ∀ s1 d' e' a s2, Q s1 → (knot mode C n).whnf d' e' s1 = .ok (a, s2) → Q s2)
    (hQgaa : ∀ s1 e' a s2, Q s1 → getAppArgs coreWalkFuel e' s1 = .ok (a, s2) → Q s2)
    (hGd : ∀ (H : List (BitVec 64)) s1 (tbl : IProjTable) ot i us, C.H <+: H → Q s1 → TblE C.EB C.EH ot tbl →
      (∃ T, C.fe.findTable? T = some tbl) → i < 2 ^ 63 →
      SpecR (σ := σ) (Pre (ctxH C H) s1 (gdParams.zip [BitVec.ofNat 64 n, ecell C ot, BitVec.ofNat 64 i,
        Enc.idxW us])) (gdBody C) s1 (checkProjGuard (knot mode C n) C.fe (tbl.entry i) us) (PostU (ctxH C H)))
    (hQgd : ∀ s1 (tbl : IProjTable) i us a s2, Q s1 → checkProjGuard (knot mode C n) C.fe (tbl.entry i) us s1 = .ok (a, s2) → Q s2)
    (hTa : ∀ (H : List (BitVec 64)) s1 (tbl : IProjTable) ot i us (targs : List EIdx) oa pe, C.H <+: H → Q s1 →
      TblE C.EB C.EH ot tbl → (∃ T, C.fe.findTable? T = some tbl) → BlkAt H oa (targs.map Enc.idxW) → i < 2 ^ 63 →
      SpecR (σ := σ) (Pre (ctxH C H) s1 (taParams.zip [ecell C ot, BitVec.ofNat 64 i, Enc.idxW us, cellA C oa,
        Enc.idxW pe])) (taBody C) s1 ((tbl.entry i).typeAt us targs pe) (PostK (ctxH C H)))
    (s : AState) (hq : Q s) (d : Nat) (hd : d < 2 ^ 63) (sn : NIdx) (i : Nat) (pe : EIdx) (hi : i < 2 ^ 64) :
    SpecR (σ := σ) (Pre C s (iprParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW sn, BitVec.ofNat 64 i,
      Enc.idxW pe])) (pjioBody C) s (inferProj (CoreFnsA.ioView (knot mode C n)) C.fe d sn i pe) (PostK C) := by
  refine specR_prologue (postK_locals C) (pjio_none C _) ?_
  unfold inferProj
  simp only [bind_assoc, ioView_infer, ioView_whnf, checkProjGuard_ioView]
  refine Big.specR_callKC (C := C) pjA fIO kParams [vv kFu, vv kD, vv ibPe] (inferIOE C fIOB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW pe] (by decide) rfl (by decide) hc.i
    ⟨by simp +decide [Env.get, iprParams, ctxEnv], by simp +decide [Env.get, iprParams, ctxEnv], by simp +decide [Env.get, iprParams, ctxEnv], trivial⟩ (hI C.H s d pe (List.prefix_refl _) hd) (fun a s1 H1 hp1 hrun1 => ?_)
  have hq1 := hQi s d pe a s1 hq hrun1
  refine Big.specR_callKC (C := ctxH C H1) pjTe fW kParams [vv kFu, vv kD, vv pjA] (whnfE C fWB)
    [BitVec.ofNat 64 n, BitVec.ofNat 64 d, Enc.idxW a] (by decide) rfl (by decide) hc.w
    ⟨by simp +decide [Env.get, iprParams, ctxEnv], by simp +decide [Env.get, iprParams, ctxEnv], by simp, trivial⟩ (hW H1 s1 d a hp1 hd) (fun te s2 H2 hp2 hrun2 => ?_)
  have hq2 := hQw s1 d a te s2 hq1 hrun2
  have hp12 : C.H <+: H2 := hp1.trans hp2
  refine specR_callNIM (C := ctxH C H2) pjHh fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv pjTe]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW te] (by decide) rfl (by decide) hc.af
    ⟨rfl, by simp, trivial⟩
    (fun a w s' st => getAppFn coreWalkFuel te s2 = .ok (a, s') ∧ Post (ctxH C H2) s2 a w s' st)
    (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec (ctxH C H2) hc.af coreWalkFuel te s2 CV.coreWalkFuel_lt t ⟨hu, hlk 0 (by decide),
        hlk 1 (by decide)⟩))
    (fun hh w s' st ⟨hrun3, hw, hs, _⟩ => ?_)
  subst hw
  have hs' : s2 = s' := hs.symm
  subst hs'
  refine Knot.specR_tagIteV pjHh hh 3 (by decide) (by decide) (by simp) (fun htg => ?_) (fun htg => ?_)
  swap
  · rw [if_neg (show ¬ (hh.tag == ETag.const) = true by simpa [ETag.const] using htg)]
    exact specR_hangI
  rw [if_pos (show (hh.tag == ETag.const) = true by simp [htg, ETag.const])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv pjHh) (Enc.idxW hh) (by decide) (by simp) ?_
  refine specR_viewP (C := ctxH C H2) hh (by simp) (by simp +decide [Env.get] <;> rfl)
    (by simp +decide [Env.get, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
  refine specR_congr (view_bind_eq hh v _ s2 hv) ?_
  have h3 : v.tagN = 3 := by rw [htn, htg]; rfl
  obtain ⟨T, us, rfl⟩ := UD.tagN_const h3
  dsimp only
  refine specR_loadI' pjT (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW T) (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW T) [Enc.idxW us] []) ?_
  refine specR_loadI' pjUs _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW us) (by decide) (by simp +decide [sev]) rfl
    (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW T) (Enc.idxW us) [] []) ?_
  refine specR_dropM ?_
  refine specR_tblFindI (C := ctxH C H2) (ctxOK_H hok H2) hc.mg hc.mp pjTb (vv pjT) T (by decide) (by simp)
    (by simp +decide [Env.get, ctxEnv] <;> rfl) ?_
  have hrel := tbl_rel hok T
  revert hrel
  unfold IFEnv.findProj?
  rcases hft : C.fe.findTable? T with _ | tbl
  · intro hrel; simp only at hrel
    rw [show (ctxH C H2).tblM[T]? = none from hrel]
    exact specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI)
      (fun h => absurd h (by decide))
  intro ⟨ot, hm, htb⟩
  rw [show (ctxH C H2).tblM[T]? = some (ecell C ot) from hm]
  refine specR_atEntry fun t ht => ?_
  have hoE : ot < C.EN := Nat.lt_of_lt_of_le (tblE_lt htb) ht.sr.env.1.len
  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI pjTq _ (ecell C ot) (by decide) (by simp [sev, optWG]; exact BitVec.add_sub_cancel _ _) ?_
  obtain ⟨hsn, ⟨wl, hwl, oL, hwL, hblk⟩, ⟨hnp, hnp63⟩, hcto, ⟨hnf, hnf63⟩, _⟩ := id htb
  refine specR_envLoadI (C := ctxH C H2) pjNf (.op .add [vv pjTq, .const 32]) (ot + 4) _ (by decide)
    (by simp +decide [sev, Env.get]; exact UD.ecell_add32 C ot) hnf ?_
  have hlw := word_lt_iff i tbl.numFields (by unfold B; omega) (by unfold B; omega)
  dsimp only
  by_cases hi2 : i < tbl.numFields
  swap
  · simp only [hi2, ↓reduceIte]
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get, iprParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
      (not_congr hlw).mpr hi2]) (fun h => absurd rfl h) (fun _ => specR_hangI)
  simp only [hi2, ↓reduceIte]
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get, iprParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
    hlw.mpr hi2]) (fun _ => ?_) (fun h => absurd h (by decide))
  try dsimp only
  refine specR_callNIH (C := ctxH C H2) pjVa ExG.fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv pjTe]
    (ExG.gaaBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW te] (by decide) rfl (by decide) hc.gaa
    ⟨rfl, by simp, trivial⟩
    (fun a w s' st => getAppArgs coreWalkFuel te s2 = .ok (a, s') ∧ PostA (ctxH C H2) a w s' st)
    (fun a w s' H' => getAppArgs coreWalkFuel te s2 = .ok (a, s') ∧ ∃ o3, w = cellA C o3 ∧
      BlkAt H' o3 (a.map Enc.idxW))
    (fun a w s' st ⟨hrun, H3, o3, hp, hw, hb, hsr⟩ => ⟨H3, hp, ⟨hrun, o3, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (ExG.gaa_spec (ctxH C H2) (ctxOK_H hok _) hc.gaa coreWalkFuel CV.coreWalkFuel_lt H2 te s2)))
    (fun targs w s3 H3 hp3 ⟨hrun3, o3, hw, hb3⟩ => ?_)
  subst hw
  have hq3 := hQgaa s2 te targs s3 hq2 hrun3
  have hp13 : C.H <+: H3 := hp12.trans hp3
  by_cases hT : T = sn
  swap
  · have hne : Enc.idxW T ≠ Enc.idxW sn := fun e => hT (Enc.idxW_inj e)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, iprParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_hangI
  subst hT
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, iprParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only [bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  refine specR_atEntry fun t3 ht3 => ?_
  have hsm := blk_small0 (C := ctxH C H3) (ctxOK_H hok _) ht3.sr hb3
  simp only [List.length_map] at hsm
  obtain ⟨hlo3, hlv3⟩ := blkAt_get0 hb3
  refine UD.specR_heapLoadI' (C := ctxH C H3) pjNa (vv pjVa) o3 (BitVec.ofNat 64 targs.length)
    (by show H3[o3]? = _; rw [List.getElem?_eq_getElem hlo3, hlv3]; simp) (by decide) (by simp; rfl) ?_
  refine specR_envLoadI (C := ctxH C H3) pjNp (.op .add [vv pjTq, .const 16]) (ot + 2) _ (by decide)
    (by simp +decide [sev, Env.get]; exact UD.ecell_add16 C ot) hnp ?_
  simp only [IProjTable.entry]
  by_cases hna : targs.length = tbl.numParams
  swap
  · have hne : BitVec.ofNat 64 targs.length ≠ BitVec.ofNat 64 tbl.numParams := by
      intro e; have := congrArg BitVec.toNat e; simp at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; exact hna this
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_hangI
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hna])
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only [hna, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
  subst hwL
  refine specR_envLoadI (C := ctxH C H3) pjLp (.op .add [vv pjTq, .const 8]) (ot + 1) _ (by decide)
    (by simp +decide [sev, Env.get]; exact ecell_add8 C ot) hwl ?_
  have hl0 : C.EH[oL]? = some (BitVec.ofNat 64 tbl.levelParams.length) := by simpa using hblk.1
  refine specR_envLoadI (C := ctxH C H3) pjLl (vv pjLp) oL _ (by decide) (by simp; rfl) hl0 ?_
  refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [Env.get, iprParams, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv pjUs) (Enc.idxW us) (by decide) (by simp) ?_
  refine specR_lsviewPI us (by simp) (by simp; rfl) (by simp +decide [Env.get, iprParams, ctxEnv] <;> rfl) (by decide)
    (fun vl Pl hvl _ hvll => ?_)
  refine specR_runBind (viewLsLen_run us s3 vl hvl) ?_
  dsimp only
  have hvl' : vl.length < 2 ^ 61 := by simpa using hvll
  have hlp : tbl.levelParams.length < 2 ^ 61 := by
    have h1 := blkAt_len (show BlkAt C.EH oL (tbl.levelParams.map Enc.idxW) from hblk)
    have h2 : C.EH.length ≤ C.EN := ht3.sr.env.1.len
    have h3 := hok.envLay
    simp only [List.length_map] at h1; omega
  by_cases hl : vl.length = tbl.levelParams.length
  swap
  · have hne : BitVec.ofNat 64 (vl.map Enc.idxW).length ≠ BitVec.ofNat 64 tbl.levelParams.length := by
      intro e; have := congrArg BitVec.toNat e; simp at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this; exact hl this
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; simpa using hne)
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_hangI
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hl])
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only [hl, ↓reduceIte]
  refine specR_dropM ?_
  refine specR_callNIH (C := ctxH C H3) pjG fGd gdParams [vv kFu, vv pjTq, vv ibIx, vv pjUs] (gdBody C)
    [BitVec.ofNat 64 n, ecell C ot, BitVec.ofNat 64 i, Enc.idxW us] (by decide) rfl (by decide) hc.gd
    ⟨by simp +decide [Env.get, iprParams, ctxEnv], by simp <;> rfl, by simp +decide [Env.get, iprParams, ctxEnv], by simp, trivial⟩
    (fun a w s' st => checkProjGuard (knot mode C n) C.fe (tbl.entry i) us s3 = .ok (a, s') ∧
      PostU (ctxH C H3) a w s' st)
    (fun a w s' _ => checkProjGuard (knot mode C n) C.fe (tbl.entry i) us s3 = .ok (a, s'))
    (fun a w s' st ⟨hrun, H', hp, hsr⟩ => ⟨H', hp, hrun, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu gdParams _ rfl hlk)
      (hGd H3 s3 tbl ot i us hp13 hq3 htb ⟨_, hft⟩ (by omega))))
    (fun g w s4 H4 hp4 hrun4 => ?_)
  have hq4 := hQgd s3 tbl i us g s4 hq3 hrun4
  refine specR_congr (m' := (tbl.entry i).typeAt us targs pe >>= fun r => pure r) (by simp [IProjTable.entry]) ?_
  refine specR_callNIH (C := ctxH C H4) pjR fTa taParams [vv pjTq, vv ibIx, vv pjUs, vv pjVa, vv ibPe] (taBody C)
    [ecell C ot, BitVec.ofNat 64 i, Enc.idxW us, cellA C o3, Enc.idxW pe] (by decide) rfl (by decide) hc.ta
    ⟨by simp <;> rfl, by simp +decide [Env.get, iprParams, ctxEnv], by simp, by simp <;> rfl, by simp +decide [Env.get, iprParams, ctxEnv], trivial⟩
    (PostK (ctxH C H4)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu taParams _ rfl hlk)
      (hTa H4 s4 tbl ot i us targs o3 pe (hp13.trans hp4) hq4 htb ⟨_, hft⟩ (blkAt_mono hb3 hp4) (by omega)))
    (fun r w s5 H5 hp5 hw => ?_)
  subst hw
  exact specR_returnI _ (Enc.idxW r) (by simp)
    (fun t ht => ⟨H5, hp12.trans (hp3.trans (hp4.trans hp5)), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.WC
