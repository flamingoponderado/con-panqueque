import ConPanqueque.T.FixMemo
import ConPanqueque.T.EnvCopy
import ConPanqueque.T.InstLPFast
import ConPanqueque.T.Knot
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `constValAt`: a stored value at a universe instantiation, memoized on `(name, levels)`

On a miss the level-parameter names (an environment block) are copied into fresh value-heap cells,
which is what `instLPFast`'s spec reads, and the instantiation is stored in `constValC`.
-/

namespace ConPanqueque.T.CV

open ConPanqueque.T.Knot (PostK postK_locals params_none)
open ConPanqueque.T.ILP (fInstLPF ilpfBody ilpf_spec CodesILP ilpParams ilpBody)
open ConPanqueque.T ConPanqueque.T.Ex
open ConRon.Bridge

def cN := ofString "vn"
def cLp := ofString "vlp"
def cV := ofString "vv"
def cUs := ofString "vus"
def cX := ofString "vx"
def cLen := ofString "vlen"
def cP := ofString "vp"
def cY := ofString "vy"
def cZ := ofString "vz"

def cvParams : List MlS := [cN, cLp, cV, cUs]
def cvLocals : List MlS := [cX, cLen, cP, cY, cZ, lCn, lSrc, lDst, lCi, lCz]

def missP (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local cLen (.load .one (vv cLp)))
  (.seq (.assign .local lCn (.op .add [vv cLen, .const 1]))
  (allocP C cP (.panop .mul [vv lCn, .const 8])
  (.seq (.assign .local lSrc (vv cLp)) (.seq (.assign .local lDst (vv cP)) (.seq (.assign .local lCi (.const 0))
  (.seq copyLoop
  (.seq (.call (some (some (.local, cY), none)) fInstLPF
      [.const (BitVec.ofNat 64 coreWalkFuel), vv cV, vv cP, vv cUs])
  (fixSetP C .constVal cZ (vv cN) (vv cUs) (vv cY) (.return (vv cY))))))))))

def cvBody (C : Ctx) : ProgHOL 64 :=
  prologue cvLocals (fixGetP C .constVal cX (vv cN) (vv cUs)
    (.ite (.cmp .notEqual (vv cX) (.const 0)) (.return (.op .sub [vv cX, .const 1])) (missP C)))

section
variable {σ : Type}

theorem prefix_fillI (B ws : List (BitVec 64)) (o : Nat) (P : List (BitVec 64)) (hP : P.length ≤ o)
    (hpre : P <+: B) : ∀ i, P <+: fillI B ws o i
  | 0 => hpre
  | i + 1 => by
    have ih := prefix_fillI B ws o P hP hpre i
    obtain ⟨r, hr⟩ := ih
    refine ⟨r.set (o + i - P.length) (ws.getD i 0), ?_⟩
    simp only [fillI, ← hr]
    rw [List.set_append_right _ _ (by omega)]

theorem blk_of_fillI (B ws : List (BitVec 64)) (o : Nat) (xs : List (BitVec 64))
    (hws : ws = BitVec.ofNat 64 xs.length :: xs) (hdst : o + ws.length ≤ B.length) :
    BlkAt (fillI B ws o ws.length) o xs := by
  have hl : ws.length = xs.length + 1 := by rw [hws]; rfl
  constructor
  · rw [fillI_get?, ite_eq_left ⟨Nat.le_refl _, by omega, by omega⟩]; simp [hws]
  · intro i hi
    rw [fillI_get?, ite_eq_left ⟨by omega, by omega, by omega⟩]
    simp [hws, show o + 1 + i - o = i + 1 by omega, List.getD_eq_getElem?_getD, hi]

theorem mul8_eq (n : Nat) : BitVec.ofNat 64 n * 8 = BitVec.ofNat 64 (8 * n) := by
  rw [show (8 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_mul_ofNat, Nat.mul_comm]

/-- The twin's `constValAt`, written as the port reads it. -/
theorem constValAt_eq (n : NIdx) (lps : List NIdx) (value : EIdx) (us : LsIdx) (s : AState) :
    constValAt n lps value us s =
      ((fun s => .ok ((FixK.val.sel s.caches)[(n, us)]?, s) : AM (Option EIdx)) >>= fun r =>
        match r with
        | some x => pure x
        | none => instLPFast coreWalkFuel lps us value >>= fun x => FixK.val.setOp (n, us) x >>= fun _ => pure x) s := by
  rfl

theorem cv_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cvLocals → (ctxEnv C ++ cvParams.zip vals).get x = none :=
  params_none C cvLocals cvParams vals (by decide) (by decide)

theorem coreWalkFuel_lt : coreWalkFuel < 2 ^ 64 := by unfold coreWalkFuel; decide

theorem cv_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CodesILP C (ilpBody C))
    (hcf : C.code.lookup fInstLPF = some (ilpParams.map (fun p => (p, ShapeHOL.one)), ilpfBody C, .one))
    (s : AState) (n : NIdx) (lps : List NIdx) (ks : List ConLeche.Name) (value : EIdx) (us : LsIdx)
    (vsL : List ConLeche.Level) (o : Nat) (hlp : EBlk C.EH o (lps.map Enc.idxW)) (hlen : lps.length + 1 < 2 ^ 60)
    (hks : Frontend.denoteNList s.store.ns lps = some ks) (hus : denoteLs s.store.lss us = some vsL)
    (hst : StateOK s) (hcn : ReadNCacheOK s.caches.readNC s.store) (hcl : ReadLCacheOK s.caches.readLC s.store)
    (hcls : ReadLsCacheOK s.caches.readLsC s.store) (hden : (denoteE s.store value).isSome = true) :
    SpecR (σ := σ) (Pre C s (cvParams.zip [Enc.idxW n, ecell C o, Enc.idxW value, Enc.idxW us])) (cvBody C) s
      (constValAt n lps value us) (PostK C) := by
  refine specR_prologue (postK_locals C) (cv_none C _) ?_
  refine specR_congr (constValAt_eq n lps value us s) ?_
  refine specR_fixGetI hok .val hc.memoGet hc.memoProbe cX (vv cN) (vv cUs) n us (by decide)
    (by simp +decide [Env.get, cvParams, ctxEnv]) (by simp +decide [Env.get, cvParams, ctxEnv])
    (by simp +decide [Env.get, cvParams, ctxEnv]) ?_
  rcases hr : (FixK.val.sel s.caches)[(n, us)]? with _ | x
  · -- miss
    refine specR_ifI _ 0 (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, optW, optWG])
      (fun h => absurd rfl h) (fun _ => ?_)
    unfold missP
    have hl0 : C.EH[o]? = some (BitVec.ofNat 64 lps.length) := by have := hlp.1; simpa using this
    refine specR_envLoadI cLen (vv cLp) o _ (by decide) (by simp +decide [Env.get, cvParams, ctxEnv]) hl0 ?_
    refine specR_assignI lCn _ (BitVec.ofNat 64 (lps.length + 1)) (by decide)
      (by simp +decide [sev, Env.get]; exact word_add1_eq _) ?_
    refine specR_allocI cP (.panop .mul [vv lCn, .const 8]) (lps.length + 1) (by omega) (by decide)
      (fun v => by simp +decide [sev, Env.get]; exact mul8_eq _) (fun H' wsN hpre hwl hcap => ?_)
    refine specR_assignI lSrc (vv cLp) (ecell C o) (by decide) (by simp +decide [sev, Env.get, cvParams, ctxEnv]) ?_
    refine specR_assignI lDst (vv cP) (cellA C H'.length) (by decide) (by simp +decide [sev, Env.get]) ?_
    refine specR_assignI lCi (.const 0) 0 (by decide) rfl ?_
    have hws : (BitVec.ofNat 64 lps.length :: lps.map Enc.idxW).length = lps.length + 1 := by simp
    refine specR_copyEI (C := C) hok (H' ++ wsN) (BitVec.ofNat 64 lps.length :: lps.map Enc.idxW) o H'.length
      (by decide) (fun j hj => ?_) (by simp [hwl]) (by rw [hws]; omega)
      (by rw [hws]; simp +decide [Env.get]) (by decide) (by simp +decide [Env.get, cvParams, ctxEnv]) ?_
    · rcases j with _ | j
      · simpa using hl0
      · have := hlp.2 j (by simp at hj ⊢; omega)
        simp only [List.getElem_cons_succ]
        rw [show o + (j + 1) = o + 1 + j by omega]; simpa using this
    -- the call
    have hblk := blk_of_fillI (H' ++ wsN) (BitVec.ofNat 64 lps.length :: lps.map Enc.idxW) H'.length (lps.map Enc.idxW)
      (by simp) (by simp [hwl])
    refine specR_callNIH cY fInstLPF ilpParams [.const (BitVec.ofNat 64 coreWalkFuel), vv cV, vv cP, vv cUs]
      (ilpfBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW value, cellA C H'.length, Enc.idxW us] (by decide) rfl
      (by decide) hcf
      ⟨rfl, by simp +decide [sev, Env.get, cvParams, ctxEnv], by simp +decide [sev, Env.get],
        by simp +decide [sev, Env.get, cvParams, ctxEnv], trivial⟩
      (ILP.PostILP (ctxH C _)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H'', hp, hw, hsr⟩ => ⟨H'', hp, hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ilpParams _ rfl hlk)
        (ilpf_spec ra C hok hc coreWalkFuel coreWalkFuel_lt H'.length lps ks us vsL _ s value hks hus hst hcn hcl
          hcls hden hblk))
      (fun a w s' H'' hp hw => ?_)
    subst hw
    refine specR_fixSetI (C := ctxH C H'') (ctxOK_H hok H'') .val hc.memoSet hc.memoIns cZ (vv cN) (vv cUs) (vv cY)
      n us a (by decide) (by simp +decide [sev, Env.get, cvParams, ctxEnv]) (by simp +decide [sev, Env.get, cvParams, ctxEnv])
      (by simp +decide [sev, Env.get]) (by simp +decide [Env.get, cvParams, ctxEnv]; rfl) (fun w => ?_)
    refine specR_returnI _ (Enc.idxW a) (by simp +decide [sev, Env.get]) (fun t ht => ?_)
    refine ⟨H'', ?_, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩
    have hp1 : C.H <+: fillI (H' ++ wsN) (BitVec.ofNat 64 lps.length :: lps.map Enc.idxW) H'.length
        (BitVec.ofNat 64 lps.length :: lps.map Enc.idxW).length :=
      prefix_fillI _ _ _ C.H (hpre.length_le) (hpre.trans (List.prefix_append _ _)) _
    exact hp1.trans hp
  · -- hit
    refine specR_ifI _ 1 (by simp [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact Knot.optW_some_ne x)
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_returnI _ (Enc.idxW x) (by simp [sev, Env.get, optW, optWG]; exact BitVec.add_sub_cancel _ _)
      (fun t ht => ?_)
    exact ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩

end

end ConPanqueque.T.CV
