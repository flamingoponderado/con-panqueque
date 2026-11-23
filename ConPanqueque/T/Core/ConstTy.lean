import ConPanqueque.T.Core.ConstVal
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `constTyAt`: a stored type at a universe instantiation, memoized on `(name, levels)`

`constValAt`'s port with the type cache (`constTyC`) and the stored type in place of the value.
-/

namespace ConPanqueque.T.CT

open ConPanqueque.T.Knot (PostK postK_locals params_none)
open ConPanqueque.T.ILP (fInstLPF ilpfBody ilpf_spec CodesILP ilpParams ilpBody)
open ConPanqueque.T ConPanqueque.T.Ex
open ConPanqueque.T.CV (cN cLp cV cUs cX cLen cP cY cZ cvParams cvLocals cv_none prefix_fillI blk_of_fillI mul8_eq
  coreWalkFuel_lt)
open ConRon.Bridge

def fCT := ofString "constTyAt"

def ctMissP (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local cLen (.load .one (vv cLp)))
  (.seq (.assign .local lCn (.op .add [vv cLen, .const 1]))
  (allocP C cP (.panop .mul [vv lCn, .const 8])
  (.seq (.assign .local lSrc (vv cLp)) (.seq (.assign .local lDst (vv cP)) (.seq (.assign .local lCi (.const 0))
  (.seq copyLoop
  (.seq (.call (some (some (.local, cY), none)) fInstLPF
      [.const (BitVec.ofNat 64 coreWalkFuel), vv cV, vv cP, vv cUs])
  (fixSetP C .constTy cZ (vv cN) (vv cUs) (vv cY) (.return (vv cY))))))))))

def ctBody (C : Ctx) : ProgHOL 64 :=
  prologue cvLocals (fixGetP C .constTy cX (vv cN) (vv cUs)
    (.ite (.cmp .notEqual (vv cX) (.const 0)) (.return (.op .sub [vv cX, .const 1])) (ctMissP C)))

section
variable {σ : Type}

theorem constTyAt_eq (cv : IConstantVal) (us : LsIdx) (s : AState) :
    constTyAt cv us s =
      ((fun s => .ok ((FixK.ty.sel s.caches)[(cv.name, us)]?, s) : AM (Option EIdx)) >>= fun r =>
        match r with
        | some x => pure x
        | none => instLPFast coreWalkFuel cv.levelParams us cv.type >>= fun x =>
            FixK.ty.setOp (cv.name, us) x >>= fun _ => pure x) s := by
  rfl

theorem ct_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesILP C (ilpBody C))
    (hcf : C.code.lookup fInstLPF = some (ilpParams.map (fun p => (p, ShapeHOL.one)), ilpfBody C, .one))
    (s : AState) (cv : IConstantVal) (ks : List ConLeche.Name) (us : LsIdx)
    (vsL : List ConLeche.Level) (o : Nat) (hlp : EBlk C.EH o (cv.levelParams.map Enc.idxW)) (hlen : cv.levelParams.length + 1 < 2 ^ 60)
    (hks : Frontend.denoteNList s.store.ns cv.levelParams = some ks) (hus : denoteLs s.store.lss us = some vsL)
    (hst : StateOK s) (hcn : ReadNCacheOK s.caches.readNC s.store) (hcl : ReadLCacheOK s.caches.readLC s.store)
    (hcls : ReadLsCacheOK s.caches.readLsC s.store) (hden : (denoteE s.store cv.type).isSome = true) :
    SpecR (σ := σ) (Pre C s (cvParams.zip [Enc.idxW cv.name, ecell C o, Enc.idxW cv.type, Enc.idxW us])) (ctBody C) s
      (constTyAt cv us) (PostK C) := by
  refine specR_prologue (postK_locals C) (cv_none C _) ?_
  refine specR_congr (constTyAt_eq cv us s) ?_
  refine specR_fixGetI hok .ty hc.memoGet hc.memoProbe cX (vv cN) (vv cUs) cv.name us (by decide)
    (by simp +decide [Env.get, cvParams, ctxEnv]) (by simp +decide [Env.get, cvParams, ctxEnv])
    (by simp +decide [Env.get, cvParams, ctxEnv]) ?_
  rcases hr : (FixK.ty.sel s.caches)[(cv.name, us)]? with _ | x
  · -- miss
    refine specR_ifI _ 0 (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, optW, optWG])
      (fun h => absurd rfl h) (fun _ => ?_)
    unfold ctMissP
    have hl0 : C.EH[o]? = some (BitVec.ofNat 64 cv.levelParams.length) := by have := hlp.1; simpa using this
    refine specR_envLoadI cLen (vv cLp) o _ (by decide) (by simp +decide [Env.get, cvParams, ctxEnv]) hl0 ?_
    refine specR_assignI lCn _ (BitVec.ofNat 64 (cv.levelParams.length + 1)) (by decide)
      (by simp +decide [sev, Env.get]; exact word_add1_eq _) ?_
    refine specR_allocI cP (.panop .mul [vv lCn, .const 8]) (cv.levelParams.length + 1) (by omega) (by decide)
      (fun v => by simp +decide [sev, Env.get]; exact mul8_eq _) (fun H' wsN hpre hwl hcap => ?_)
    refine specR_assignI lSrc (vv cLp) (ecell C o) (by decide) (by simp +decide [sev, Env.get, cvParams, ctxEnv]) ?_
    refine specR_assignI lDst (vv cP) (cellA C H'.length) (by decide) (by simp +decide [sev, Env.get]) ?_
    refine specR_assignI lCi (.const 0) 0 (by decide) rfl ?_
    have hws : (BitVec.ofNat 64 cv.levelParams.length :: cv.levelParams.map Enc.idxW).length = cv.levelParams.length + 1 := by simp
    refine specR_copyEI (C := C) hok (H' ++ wsN) (BitVec.ofNat 64 cv.levelParams.length :: cv.levelParams.map Enc.idxW) o H'.length
      (by decide) (fun j hj => ?_) (by simp [hwl]) (by rw [hws]; omega)
      (by rw [hws]; simp +decide [Env.get]) (by decide) (by simp +decide [Env.get, cvParams, ctxEnv]) ?_
    · rcases j with _ | j
      · simpa using hl0
      · have := hlp.2 j (by simp at hj ⊢; omega)
        simp only [List.getElem_cons_succ]
        rw [show o + (j + 1) = o + 1 + j by omega]; simpa using this
    -- the call
    have hblk := blk_of_fillI (H' ++ wsN) (BitVec.ofNat 64 cv.levelParams.length :: cv.levelParams.map Enc.idxW) H'.length (cv.levelParams.map Enc.idxW)
      (by simp) (by simp [hwl])
    refine specR_callNIH cY fInstLPF ilpParams [.const (BitVec.ofNat 64 coreWalkFuel), vv cV, vv cP, vv cUs]
      (ilpfBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW cv.type, cellA C H'.length, Enc.idxW us] (by decide) rfl
      (by decide) hcf
      ⟨rfl, by simp +decide [sev, Env.get, cvParams, ctxEnv], by simp +decide [sev, Env.get],
        by simp +decide [sev, Env.get, cvParams, ctxEnv], trivial⟩
      (ILP.PostILP (ctxH C _)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H'', hp, hw, hsr⟩ => ⟨H'', hp, hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ilpParams _ rfl hlk)
        (ilpf_spec ra C hok hc coreWalkFuel coreWalkFuel_lt H'.length cv.levelParams ks us vsL _ s cv.type hks hus hst hcn hcl
          hcls hden hblk))
      (fun a w s' H'' hp hw => ?_)
    subst hw
    refine specR_fixSetI (C := ctxH C H'') (ctxOK_H hok H'') .ty hc.memoSet hc.memoIns cZ (vv cN) (vv cUs) (vv cY)
      cv.name us a (by decide) (by simp +decide [sev, Env.get, cvParams, ctxEnv]) (by simp +decide [sev, Env.get, cvParams, ctxEnv])
      (by simp +decide [sev, Env.get]) (by simp +decide [Env.get, cvParams, ctxEnv]; rfl) (fun w => ?_)
    refine specR_returnI _ (Enc.idxW a) (by simp +decide [sev, Env.get]) (fun t ht => ?_)
    refine ⟨H'', ?_, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
    have hp1 : C.H <+: fillI (H' ++ wsN) (BitVec.ofNat 64 cv.levelParams.length :: cv.levelParams.map Enc.idxW) H'.length
        (BitVec.ofNat 64 cv.levelParams.length :: cv.levelParams.map Enc.idxW).length :=
      prefix_fillI _ _ _ C.H (hpre.length_le) (hpre.trans (List.prefix_append _ _)) _
    exact hp1.trans hp
  · -- hit
    refine specR_ifI _ 1 (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact Knot.optW_some_ne x)
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_returnI _ (Enc.idxW x) (by simp [sev, Env.get, optW, optWG]; exact BitVec.add_sub_cancel _ _)
      (fun t ht => ?_)
    exact ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩

end

end ConPanqueque.T.CT
