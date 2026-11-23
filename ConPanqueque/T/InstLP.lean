import ConPanqueque.T.SubstLsTop
import ConPanqueque.T.EIntern2
import ConPanqueque.T.Ex.Abstract1
import ConRon.Bridge.ExprOps.Owed
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `instLPGo`: substitute level parameters throughout an expression

`instLP(fu, h, ks, us)`: con-ron's `instLPGo` with the names `ks` a heap block of handles and the
levels `us` a list handle. The `hasLP` cutoff reads bit 0 of the derived word; `sort`/`const` call the
level and level-list substitutions; the other composite arms go through the `instLPC` memo at `(h, 0)`.
-/

namespace ConPanqueque.T.ILP
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM
open ConPanqueque.T.LEq ConPanqueque.T.LSub ConPanqueque.T.ExG ConPanqueque.T.LLeq ConPanqueque.T.ExA

def fInstLP := ofString "instLPGo"
def ilpParams : List MlS := [pFu, pH, pKp, pUs]

/-- The memo probe at `(h, 0)`, and on a hit its answer. -/
def probedL (G : BitVec 64) (miss : ProgHOL 64) : ProgHOL 64 :=
  .seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) (vv pH))
  (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 1))]) (.const 0))
  (.seq (.call (some (some (.local, lX), none)) fMemoGet [.const G, lenE (.const 0)])
    (.ite (vv lX) (.return (.op .sub [vv lX, .const 1])) miss)))

/-- `memo[(h, 0)] := w; return w`. -/
def setRetL (G : BitVec 64) : ProgHOL 64 :=
  .seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) (vv pH))
  (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 1))]) (.const 0))
  (.seq (.call (some (some (.local, lX), none)) fMemoSet [.const G, lenE (.const 0), vv lW]) (.return (vv lW))))

def callI (x arg : MlS) : ProgHOL 64 :=
  .call (some (some (.local, x), none)) fInstLP [.op .sub [vv pFu, .const 1], vv arg, vv pKp, vv pUs]

def viewH (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq eViewP rest))

def sortI : ProgHOL 64 :=
  viewH (.seq (.assign .local lA1 (.load .one (vv lRp)))
  (.seq (.call (some (some (.local, lA2), none)) fSubstLH [vv lA1, vv pKp, vv pUs])
  (.ite (eqE lA2 lA1) (.return (vv pH))
    (.seq (.call (some (some (.local, lW), none)) fInternSort [vv lA2]) (.return (vv lW))))))

def constI : ProgHOL 64 :=
  viewH (.seq (.assign .local lA1 (.load .one (vv lRp)))
  (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (.call (some (some (.local, lA3), none)) fSubstLsH [vv lA2, vv pKp, vv pUs])
  (.ite (eqE lA3 lA2) (.return (vv pH))
    (.seq (.call (some (some (.local, lW), none)) fInternConst [vv lA1, vv lA3]) (.return (vv lW)))))))

def fvarRestI (G : BitVec 64) : ProgHOL 64 :=
  .ite (.shift .lsr (vv lB) (.const 63)) hang
  (.seq (callI lY lA1)
    (rebuild (eqE lY lA1) (.call (some (some (.local, lW), none)) fInternFVar [vv lY, vv lB]) (setRetL G)))

def fvarI (G : BitVec 64) : ProgHOL 64 :=
  probedL G (viewH (.seq (.assign .local lA1 (.load .one (vv lRp)))
    (.ite (.cmp .equal (vv lRn) (.const 1)) (.seq (.assign .local lB (.const 0)) (fvarRestI G))
      (.ite (.cmp .equal (vv lRn) (.const 2))
        (.seq (.assign .local lB (.load .one (.op .add [vv lRp, .const 8]))) (fvarRestI G)) hang))))

def binI (G : BitVec 64) (fn : MlS) : ProgHOL 64 :=
  probedL G (viewH (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (callI lY lA1) (.seq (callI lZ lA2)
    (rebuild (.op .and [eqE lY lA1, eqE lZ lA2]) (.call (some (some (.local, lW), none)) fn [vv lY, vv lZ])
      (setRetL G)))))))

def letLP (G : BitVec 64) : ProgHOL 64 :=
  probedL G (viewH (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.seq (.assign .local lA3 (.load .one (.op .add [vv lRp, .const 16])))
    (.seq (callI lY lA1) (.seq (callI lZ lA2) (.seq (callI lB lA3)
    (rebuild (.op .and [.op .and [eqE lY lA1, eqE lZ lA2], eqE lB lA3])
      (.call (some (some (.local, lW), none)) fInternLet [vv lY, vv lZ, vv lB]) (setRetL G)))))))))

def projRestI (G : BitVec 64) : ProgHOL 64 :=
  .ite (.shift .lsr (vv lB) (.const 63)) hang
  (.seq (callI lY lA2)
    (rebuild (eqE lY lA2) (.call (some (some (.local, lW), none)) fInternProj [vv lA1, vv lY, vv lB]) (setRetL G)))

def projI (G : BitVec 64) : ProgHOL 64 :=
  probedL G (viewH (.seq (.assign .local lA1 (.load .one (.op .add [vv lRp, .const 0])))
    (.seq (.assign .local lA2 (.load .one (.op .add [vv lRp, .const 8])))
    (.ite (.cmp .equal (vv lRn) (.const 2)) (.seq (.assign .local lB (.const 0)) (projRestI G))
      (.ite (.cmp .equal (vv lRn) (.const 3))
        (.seq (.assign .local lB (.load .one (.op .add [vv lRp, .const 16]))) (projRestI G)) hang)))))

def coreI (G : BitVec 64) : ProgHOL 64 :=
  .ite (.cmp .equal (vv pFu) (.const 0)) hang
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv pH)) (.seq (storeDerived 9 10)
  (.ite (.cmp .equal (.op .and [vv lDo1, .const 1]) (.const 0)) (.return (vv pH))
  (.ite (isAppE (vv pH)) (binI G fInternApp)
  (.ite (tagIsE pH 5) (binI G fInternLam)
  (.ite (tagIsE pH 6) (binI G fInternForallE)
  (.ite (tagIsE pH 1) (fvarI G)
  (.ite (tagIsE pH 7) (letLP G)
  (.ite (tagIsE pH 9) (projI G)
  (.ite (tagIsE pH 2) sortI
  (.ite (tagIsE pH 3) constI (.return (vv pH))))))))))))))

def ilpBody (C : Ctx) : ProgHOL 64 := prologue inst1Locals (coreI (C.mG (.e .instLP)))

section
variable {σ : Type}

theorem denoteNList_ext {st st' : NStore} (hx : NExt st st') :
    ∀ (hs : List NIdx) (xs : List ConLeche.Name), Frontend.denoteNList st hs = some xs →
      Frontend.denoteNList st' hs = some xs
  | [], xs, h => h
  | x :: xs, ys, h => by
    simp only [Frontend.denoteNList] at h ⊢
    split at h
    · rename_i a b ha hb
      simp at h; subst h
      rw [hx x a ha, denoteNList_ext hx xs b hb]
    · simp at h

/-- The twin-side invariants the walk carries (besides `SR`). -/
structure WInv (s : AState) (khs : List NIdx) (ks : List ConLeche.Name) (usH : LsIdx) (vsL : List ConLeche.Level) :
    Prop where
  wf : StoreWF s.store
  readL : ReadLCacheOK s.caches.readLC s.store
  readLs : ReadLsCacheOK s.caches.readLsC s.store
  memoL : MemoLOK s ks vsL
  memoLs : MemoLsOK s ks vsL
  names : Frontend.denoteNList s.store.ns khs = some ks
  levels : denoteLs s.store.lss usH = some vsL

/-- The invariants survive a step that extends the store and keeps the four memo/cache tables. -/
theorem WInv.step {s s' : AState} {khs : List NIdx} {ks : List ConLeche.Name} {usH : LsIdx}
    {vsL : List ConLeche.Level} (h : WInv s khs ks usH vsL) (hwf : StoreWF s'.store) (hx : Ext s.store s'.store)
    (hc1 : s'.caches.readLC = s.caches.readLC) (hc2 : s'.caches.readLsC = s.caches.readLsC)
    (hm1 : s'.memos.instLPLC = s.memos.instLPLC) (hm2 : s'.memos.instLPLsC = s.memos.instLPLsC) :
    WInv s' khs ks usH vsL where
  wf := hwf
  readL := by rw [hc1]; exact readL_ext h.readL hx
  readLs := by rw [hc2]; exact readLs_ext h.readLs hx
  memoL := fun u r hr => by
    rw [hm1] at hr
    obtain ⟨l, h1, h2⟩ := h.memoL u r hr
    exact ⟨l, denoteL_ext h1 hx, denoteL_ext h2 hx⟩
  memoLs := fun u r hr => by
    rw [hm2] at hr
    obtain ⟨l, h1, h2⟩ := h.memoLs u r hr
    exact ⟨l, denoteLs_ext h1 hx, denoteLs_ext h2 hx⟩
  names := denoteNList_ext hx.lss.ls.ns khs ks h.names
  levels := denoteLs_ext h.levels hx

end

section
variable {σ : Type}
open ConRon.Bridge.ExprOps

/-- The twin-side precondition of the walk: con-ron's invariants for `instLPGo_spec`, and the readbacks of
the substitution. -/
structure PInv (s : AState) (khs : List NIdx) (ks : List ConLeche.Name) (usH : LsIdx) (vsL : List ConLeche.Level) :
    Prop where
  ok : StateOK s
  mf : InstLPMemoF ks vsL s
  ml : InstLPLMemoA ks vsL s
  mls : InstLPLsMemoA ks vsL s
  cl : ReadLCacheOK s.caches.readLC s.store
  cls : ReadLsCacheOK s.caches.readLsC s.store
  names : Frontend.denoteNList s.store.ns khs = some ks
  levels : denoteLs s.store.lss usH = some vsL

/-- After a run of the walk the precondition holds again, and the answer reads back. -/
theorem PInv.after {s s' : AState} {khs : List NIdx} {ks : List ConLeche.Name} {usH : LsIdx}
    {vsL : List ConLeche.Level} (hp : PInv s khs ks usH vsL) (n : Nat) (h r : EIdx)
    (hden : (denoteE s.store h).isSome = true) (hrun : instLPGo ks vsL n h s = .ok (r, s')) :
    PInv s' khs ks usH vsL ∧ (denoteE s'.store r).isSome = true ∧ Ext s.store s'.store ∧
      (∀ i v, s.store.view i = some v → s'.store.view i = some v) := by
  obtain ⟨q1, q2, q3, q4, q5, -, q7, q8, -, -, q11, q12⟩ :=
    AM.of_run (P := fun t => t = s) rfl hrun
      (instLPGo_spec n ks vsL s h hp.ok hp.mf hp.ml hp.mls hp.cl hp.cls hden)
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp hden
  refine ⟨⟨q1, q2, q3, q4, q7, q8, denoteNList_ext q5.lss.ls.ns khs ks hp.names, denoteLs_ext hp.levels q5⟩,
    by rw [q12 e he]; rfl, q5, q11⟩

/-- The walk's post: the answer handle, at some bigger image. -/
def PostILP (C : Ctx) (r : EIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ w = Enc.idxW r ∧ SR (ctxH C H') s' st

theorem postILP_locals (C : Ctx) : ∀ (a : EIdx) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostILP C a w s' st → PostILP C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hw, hs⟩ => ⟨H', hp, hw, sr_of_eq hs rfl rfl rfl rfl⟩

def RecILP (C : Ctx) (B : ProgHOL 64) (ko : Nat) (khs : List NIdx) (ks : List ConLeche.Name) (usH : LsIdx)
    (vsL : List ConLeche.Level) (n : Nat) : Prop :=
  ∀ (H : List (BitVec 64)) (s : AState) (h : EIdx), PInv s khs ks usH vsL → (denoteE s.store h).isSome = true →
    BlkAt H ko (khs.map Enc.idxW) →
    SpecR (Pre (σ := σ) (ctxH C H) s (ilpParams.zip [BitVec.ofNat 64 n, Enc.idxW h, cellA C ko, Enc.idxW usH])) B s
      (instLPGo ks vsL n h) (PostILP (ctxH C H))

end

section
variable {σ : Type}
open ConRon.Bridge.ExprOps

theorem callI_spec {β : Type} (C : Ctx) (B : ProgHOL 64)
    (hcode : C.code.lookup fInstLP = some (ilpParams.map (fun p => (p, ShapeHOL.one)), B, .one))
    (ko : Nat) (khs : List NIdx) (ks : List ConLeche.Name) (usH : LsIdx) (vsL : List ConLeche.Level) (n : Nat)
    (ih : RecILP (σ := σ) C B ko khs ks usH vsL n) {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem}
    {rest : ProgHOL 64} {k : EIdx → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x arg : MlS) (h : EIdx) (hx : x ∈ DI)
    (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (harg : Γ.get arg = some (Enc.idxW h))
    (hkp : Γ.get pKp = some (cellA C ko)) (hus : Γ.get pUs = some (Enc.idxW usH))
    (hp : PInv s khs ks usH vsL) (hden : (denoteE s.store h).isSome = true) (hb : BlkAt H ko (khs.map Enc.idxW))
    (hk : ∀ r s' H', H <+: H' → PInv s' khs ks usH vsL → (denoteE s'.store r).isSome = true →
      Ext s.store s'.store → (∀ i v, s.store.view i = some v → s'.store.view i = some v) →
      instLPGo ks vsL n h s = .ok (r, s') →
      SpecR (Inv (ctxH C H') s' ((x, Enc.idxW r) :: Γ) [] DI) rest s' (k r) R) :
    SpecR (Inv (ctxH C H) s Γ M DI) (.seq (callI x arg) rest) s (instLPGo ks vsL n h >>= k) R :=
  specR_callNIH x fInstLP ilpParams [.op .sub [vv pFu, .const 1], vv arg, vv pKp, vv pUs] B
    [BitVec.ofNat 64 n, Enc.idxW h, cellA C ko, Enc.idxW usH] (by decide) rfl hx hcode
    ⟨by simp [sev, hfu]; exact ofNat_succ_sub_one n, by simp [harg], by simp [hkp], by simp [hus], trivial⟩
    (fun a w s' st => instLPGo ks vsL n h s = .ok (a, s') ∧ PostILP (ctxH C H) a w s' st)
    (fun a w s' _ => instLPGo ks vsL n h s = .ok (a, s') ∧ w = Enc.idxW a)
    (fun a w s' st ⟨hr, H', hpH, hw, hsr⟩ => ⟨H', hpH, ⟨hr, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (fun w hw => by
      subst hw; exact ih H s h hp hden hb _ (pre_of_lookups hu ilpParams _ rfl hlk)))
    (fun a w s' H' hpH ⟨hr, hw⟩ => by
      subst hw
      obtain ⟨p', d', x', v'⟩ := hp.after n h a hden hr
      exact hk a s' H' hpH p' d' x' v' hr)

end

theorem instLPGet_run (k : EIdx × Nat) (s : AState) : instLPGet k s = .ok ((memoSel .instLP s.memos)[k]?, s) := rfl
theorem instLPSet_run (k : EIdx × Nat) (r : EIdx) (s : AState) :
    instLPSet k r s = .ok ((), { s with memos := memoUpd .instLP s.memos ((memoSel .instLP s.memos).insert k r) }) :=
  rfl

section
variable {σ : Type}

theorem probedL_spec {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {H : List (BitVec 64)}
    (hcG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (h : EIdx) (miss : ProgHOL 64) (m : AM EIdx)
    (hh : Γ.get pH = some (Enc.idxW h)) (hkb : Γ.get lKb = some C.KB)
    (hmiss : SpecR (Inv (σ := σ) (ctxH C H) s ((lX, 0) :: Γ) [] DI) miss s m (PostILP (ctxH C H))) :
    SpecR (Inv (σ := σ) (ctxH C H) s Γ M DI) (probedL (C.mG (.e .instLP)) miss) s
      (do match ← instLPGet (h, 0) with | some r => pure r | none => m) (PostILP (ctxH C H)) := by
  unfold probedL
  refine specR_memoGetI (C := ctxH C H) (ctxOK_H hok H) .instLP instLPGet instLPGet_run hcG hcP lX (vv pH)
    (.const 0) h 0 (by decide) (by decide) (by simp [hh]) rfl hkb (fun r => ?_)
  cases r with
  | some w =>
    refine specR_ifI (vv lX) (Enc.idxW w + 1) (by simp [optW, optWG]) (fun _ => ?_)
      (fun hw => absurd hw (idxW_add_one_ne w))
    exact specR_returnI (.op .sub [vv lX, .const 1]) (Enc.idxW w) (by simp [sev, optW, optWG, BitVec.add_sub_cancel])
      (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | none =>
    exact specR_ifI (vv lX) 0 (by simp [optW, optWG]) (fun hw => absurd rfl hw) (fun _ => hmiss)

theorem setRetL_spec {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {H H1 : List (BitVec 64)}
    (hp : H <+: H1)
    (hcS : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one))
    (hcI : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one))
    (h r : EIdx) (hh : Γ.get pH = some (Enc.idxW h)) (hkb : Γ.get lKb = some C.KB)
    (hw : Γ.get lW = some (Enc.idxW r)) :
    SpecR (Inv (σ := σ) (ctxH C H1) s Γ M DI) (setRetL (C.mG (.e .instLP))) s (do instLPSet (h, 0) r; pure r)
      (PostILP (ctxH C H)) := by
  unfold setRetL
  refine specR_memoSetI (C := ctxH C H1) (ctxOK_H hok H1) .instLP instLPSet instLPSet_run hcS hcI lX (vv pH)
    (.const 0) (vv lW) h 0 r (by decide) (by decide) (by simp [hh]) rfl (by simp [hw]) hkb (fun w => ?_)
  exact specR_returnI (vv lW) (Enc.idxW r) (by simp +decide [hw])
    (fun t ht => ⟨H1, hp, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

section
variable {σ : Type}

/-- `specR_viewI`, with the view fact handed to the continuation. -/
theorem specR_viewIv {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {k : ENodeView → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (h : EIdx)
    (hdh : Γ.get lDh = some (Enc.idxW h)) (hfl : Γ.get lFl = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR)
    (hD : lDt ∈ D ∧ lDg ∈ D ∧ lDi ∈ D ∧ lRp ∈ D ∧ lRn ∈ D)
    (hk : ∀ v P, s.store.view h = some v → v.tagN = h.tag.toNat → (encEView v).length < 2 ^ 61 → SpecR (Inv C s ((lRp, P) ::
      (lRn, BitVec.ofNat 64 (encEView v).length) :: (lDt, BitVec.ofNat 64 h.tier.toNat) ::
      (lDg, BitVec.ofNat 64 v.tagN) :: (lDi, BitVec.ofNat 64 h.idxNat) :: Γ)
      (wordsAt P (encEView v) ++ M) D) rest s (k v) R) :
    SpecR (Inv C s Γ M D) (.seq eViewP rest) s (ConRon.Arena.view h >>= k) R := by
  intro t ht
  rcases eView_spec t C.L C.FLe s.store ht.sr.rep.e h (ht.env _ _ hdh) (ht.env _ _ hdir) (ht.env _ _ hfl)
      (ht.decl _ hD.1) (ht.decl _ hD.2.1) (ht.decl _ hD.2.2.1) (ht.decl _ hD.2.2.2.1) (ht.decl _ hD.2.2.2.2) with
    hs | ⟨v, hv, htg, hr⟩
  · exact Or.inl (seq_stop t _ _ hs)
  obtain ⟨hn, hm, hd, hc, hg, _, ⟨P, hrp, hW⟩, hrn, hsh, hdt, hdg, hdi, hfr⟩ := hr
  have e : evaluateHOLFiniteState t eViewP = (none, (evaluateHOLFiniteState t eViewP).2) := by rw [← hn]
  rw [seq_normal rest e]
  have hInv : Inv C s ((lRp, P) :: (lRn, BitVec.ofNat 64 (encEView v).length) ::
      (lDt, BitVec.ofNat 64 h.tier.toNat) :: (lDg, BitVec.ofNat 64 v.tagN) :: (lDi, BitVec.ofNat 64 h.idxNat) :: Γ)
      (wordsAt P (encEView v) ++ M) D (evaluateHOLFiniteState t eViewP).2 := by
    refine ⟨sr_of_eq ht.sr hm hd hg hc, fun y w hy => ?_, fun b w hb => ?_, fun y hy => ?_⟩
    · simp only [Env.get] at hy
      split at hy
      · rename_i e; subst e; simp at hy; subst hy; exact hrp
      split at hy
      · rename_i e; subst e; simp at hy; subst hy; exact hrn
      split at hy
      · rename_i e; subst e; simp at hy; subst hy; exact hdt
      split at hy
      · rename_i e; subst e; simp at hy; subst hy; rw [htg]; exact hdg
      split at hy
      · rename_i e; subst e; simp at hy; subst hy; exact hdi
      rename_i e1 e2 e3 e4 e5
      rw [hfr y e1 e2 e3 e4 e5]; exact ht.env y w hy
    · simp only [List.mem_append] at hb
      rcases hb with hb | hb
      · rw [hm, hd]; exact wordsAt_mem hW b w hb
      · rw [hm, hd]; exact ht.mem b w hb
    · by_cases e1 : y = lRp
      · subst e1; exact ⟨P, hrp⟩
      by_cases e2 : y = lRn
      · subst e2; exact ⟨_, hrn⟩
      by_cases e3 : y = lDt
      · subst e3; exact ⟨_, hdt⟩
      by_cases e4 : y = lDg
      · subst e4; exact ⟨_, hdg⟩
      by_cases e5 : y = lDi
      · subst e5; exact ⟨_, hdi⟩
      obtain ⟨w, hw⟩ := ht.decl y hy; exact ⟨w, by rw [hfr y e1 e2 e3 e4 e5]; exact hw⟩
  rcases hk v P hv htg hsh _ hInv with hs | ⟨w, hr', a, s', hk', hR⟩
  · exact Or.inl hs
  refine Or.inr ⟨w, hr', a, s', ?_, hR⟩
  show (do let r ← ConRon.Arena.view h s; match r with | (a, s) => k a s) = _
  rw [view_run, hv]; exact hk'

end

/-- The code the walk calls. -/
structure CodesILP (C : Ctx) (B : ProgHOL 64) : Prop where
  ilp : C.code.lookup fInstLP = some (ilpParams.map (fun p => (p, ShapeHOL.one)), B, .one)
  memoGet : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  memoProbe : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  memoSet : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one)
  memoIns : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one)
  internApp : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)
  internLam : C.code.lookup fInternLam = some ([(lEf, .one), (lEa, .one)], bin2Body lamDataE 14, .one)
  internForallE : C.code.lookup fInternForallE = some ([(lEf, .one), (lEa, .one)], bin2Body forDataE 15, .one)
  internLet : C.code.lookup fInternLet = some ([(lEty, .one), (lEvl, .one), (lEbd, .one)], letBody, .one)
  internProj : C.code.lookup fInternProj = some ([(lEp, .one), (lEe, .one), (lIw, .one)], projBody, .one)
  internFVar : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one)
  internSort : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one)
  internConst : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one)
  substLH : C.code.lookup fSubstLH = some (substMParams.map (fun p => (p, ShapeHOL.one)), substLHBody C, .one)
  substLsH : C.code.lookup fSubstLsH = some (slsParams.map (fun p => (p, ShapeHOL.one)), substLsHBody, .one)
  substM : C.code.lookup fSubstM = some (substMParams.map (fun p => (p, ShapeHOL.one)), substBodyM C, .one)
  neq : C.code.lookup NEq.fNeq = some ([(NEq.pNa, .one), (NEq.pNb, .one)], NEq.neqBody, .one)
  goM : C.code.lookup fGoM = some (goParams.map (fun p => (p, ShapeHOL.one)), goBody, .one)
  lZero : C.code.lookup fInternLZero = some ([], internLZeroBody, .one)
  lSucc : C.code.lookup fInternLSucc = some ([(lEu, .one)], internLSuccBody, .one)
  lMax : C.code.lookup fInternLMax = some ([(lEu, .one), (lEv, .one)], internLMaxBody, .one)
  lImax : C.code.lookup fInternLImax = some ([(lEu, .one), (lEv, .one)], internLImaxBody, .one)
  lParam : C.code.lookup fInternLParam = some ([(lEn, .one)], internLParamBody, .one)
  lv : C.code.lookup fInternLv = some ([(pLa, .one)], internLvBody, .one)
  lsGoS : C.code.lookup fLsGoS = some (lsgParams.map (fun p => (p, ShapeHOL.one)), lsgBody C, .one)
  internLs : C.code.lookup fInternLs = some ([(pKey, .one), (lEc, .one)], internLsBody, .one)

theorem kids2 {st : EStore} (hwf : StoreWF st) {h : EIdx} {v : ENodeView} (hv : st.view h = some v)
    (hd : (denoteE st h).isSome = true) {f a : EIdx}
    (hfa : denoteEView st v = opt2 (fun x y => x) (denoteE st f) (denoteE st a) ∨ False ∨
      (∃ g : ConLeche.Expr → ConLeche.Expr → ConLeche.Expr, denoteEView st v = opt2 g (denoteE st f) (denoteE st a))) :
    (denoteE st f).isSome = true ∧ (denoteE st a).isSome = true := by
  rw [denoteE_view_eq hwf hv] at hd
  rcases hfa with e | e | ⟨g, e⟩
  · rw [e] at hd; simp only [opt2] at hd; split at hd <;> simp_all
  · exact e.elim
  · rw [e] at hd; simp only [opt2] at hd; split at hd <;> simp_all

/-- The `app` arm after a memo miss. -/
def appMiss (ks : List ConLeche.Name) (vsL : List ConLeche.Level) (n : Nat) (h f a : EIdx) : AM EIdx := do
  let f'' ← instLPGo ks vsL n f
  let a'' ← instLPGo ks vsL n a
  let r ← internRebuiltApp h (f'' == f && a'' == a) f'' a''
  instLPSet (h, 0) r
  pure r

section
variable {σ : Type}
open ConRon.Bridge.ExprOps

theorem appI_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesILP C B) (ko : Nat) (khs : List NIdx) (ks : List ConLeche.Name) (usH : LsIdx)
    (vsL : List ConLeche.Level) (n : Nat) (ih : RecILP (σ := σ) C B ko khs ks usH vsL n)
    {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} (h f a : EIdx) (hv : s.store.view h = some (.app f a))
    (hp : PInv s khs ks usH vsL) (hden : (denoteE s.store h).isSome = true) (hb : BlkAt H ko (khs.map Enc.idxW))
    (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (hh : Γ.get pH = some (Enc.idxW h))
    (hkp : Γ.get pKp = some (cellA C ko)) (hus : Γ.get pUs = some (Enc.idxW usH))
    (hkb : Γ.get lKb = some C.KB) (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) (ctxH C H) s Γ M DI) (binI (C.mG (.e .instLP)) fInternApp) s
      (instLPArmApp ks vsL n h f a) (PostILP (ctxH C H)) := by
  obtain ⟨df, da⟩ := kids2 hp.ok.wf hv hden (f := f) (a := a) (Or.inr (Or.inr ⟨ConLeche.Expr.app, rfl⟩))
  refine specR_congr (m' := do match ← instLPGet (h, 0) with | some r => pure r | none => appMiss ks vsL n h f a)
    (by rw [instLPArmApp]; rfl) ?_
  unfold binI
  refine probedL_spec hok hc.memoGet hc.memoProbe h _ _ hh hkb ?_
  unfold viewH
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [hfle]) ?_
  refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [hh]) ?_
  refine specR_congr (m' := ConRon.Arena.view h >>= fun v => match v with
    | .app f' a' => appMiss ks vsL n h f' a'
    | _ => appMiss ks vsL n h f a)
    (by simp only [bind, StateT.bind]; rw [view_run, hv]; rfl) ?_
  refine specR_viewIv h (by simp) (by simp +decide [hfle] <;> rfl) (by simp +decide [hdir] <;> rfl) (by decide)
    (fun v P hv' _ _ => ?_)
  rw [hv] at hv'; cases hv'
  unfold appMiss
  simp only [encEView, Enc.encApp, wordsAt, List.length_cons, List.length_nil, List.range_succ, List.range_zero,
    List.nil_append, List.zip_cons_cons, List.zip_nil_left, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append]
  refine specR_loadI' lA1 _ (P + BitVec.ofNat 64 (8 * 0)) _ (Enc.idxW f) (by decide) (by simp +decide [sev])
    rfl (List.mem_cons_self ..) ?_
  refine specR_loadI' lA2 _ (P + BitVec.ofNat 64 (8 * 1)) _ (Enc.idxW a) (by decide) (by simp +decide [sev])
    rfl (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ?_
  refine callI_spec C B hc.ilp ko khs ks usH vsL n ih lY lA1 f (by decide) (by simp +decide [hfu])
    (by simp +decide) (by simp +decide [hkp]) (by simp +decide [hus]) hp df hb
    (fun f' s1 H1 hp1 pv1 _ x1 _ _ => ?_)
  refine callI_spec (H := H1) C B hc.ilp ko khs ks usH vsL n ih lZ lA2 a (by decide) (by simp +decide [hfu])
    (by simp +decide) (by simp +decide [hkp]) (by simp +decide [hus]) pv1
    (by obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp da; rw [x1.expr a e he]; rfl) (blkAt_mono hb hp1)
    (fun a' s2 H2 hp2 _ _ _ _ _ => ?_)
  refine rebuild_spec (C := ctxH C H2) _ (eqW f' f &&& eqW a' a) (f' == f && a' == a) h _ _ (internAppE f' a') ?_
    (eqW2_iff _ _ _ _) (by simp +decide [hh]) ?_ ?_
  · simp +decide [sev, eqE, eqW]
  · exact setRetL_spec hok (hp1.trans hp2) hc.memoSet hc.memoIns h h (by simp +decide [hh]) (by simp +decide [hkb])
      (by simp +decide)
  · refine specR_internAppI ra (ctxOK_H hok H2) hc.internApp lW (vv lY) (vv lZ) f' a' (by decide) (by simp +decide)
      (by simp +decide) (fun r s3 => ?_)
    exact setRetL_spec hok (hp1.trans hp2) hc.memoSet hc.memoIns h r (by simp +decide [hh]) (by simp +decide [hkb])
      (by simp +decide)

end

/-- The `lam` arm after a memo miss. -/
def lamMiss (ks : List ConLeche.Name) (vsL : List ConLeche.Level) (n : Nat) (h f a : EIdx) : AM EIdx := do
  let f'' ← instLPGo ks vsL n f
  let a'' ← instLPGo ks vsL n a
  let r ← internRebuiltLam h (f'' == f && a'' == a) f'' a''
  instLPSet (h, 0) r
  pure r

section
variable {σ : Type}
open ConRon.Bridge.ExprOps

theorem lamI_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesILP C B) (ko : Nat) (khs : List NIdx) (ks : List ConLeche.Name) (usH : LsIdx)
    (vsL : List ConLeche.Level) (n : Nat) (ih : RecILP (σ := σ) C B ko khs ks usH vsL n)
    {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} (h f a : EIdx) (hv : s.store.view h = some (.lam f a))
    (hp : PInv s khs ks usH vsL) (hden : (denoteE s.store h).isSome = true) (hb : BlkAt H ko (khs.map Enc.idxW))
    (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (hh : Γ.get pH = some (Enc.idxW h))
    (hkp : Γ.get pKp = some (cellA C ko)) (hus : Γ.get pUs = some (Enc.idxW usH))
    (hkb : Γ.get lKb = some C.KB) (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) (ctxH C H) s Γ M DI) (binI (C.mG (.e .instLP)) fInternLam) s
      (instLPArmLam ks vsL n h f a) (PostILP (ctxH C H)) := by
  obtain ⟨df, da⟩ := kids2 hp.ok.wf hv hden (f := f) (a := a) (Or.inr (Or.inr ⟨ConLeche.Expr.lam, rfl⟩))
  refine specR_congr (m' := do match ← instLPGet (h, 0) with | some r => pure r | none => lamMiss ks vsL n h f a)
    (by rw [instLPArmLam]; rfl) ?_
  unfold binI
  refine probedL_spec hok hc.memoGet hc.memoProbe h _ _ hh hkb ?_
  unfold viewH
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [hfle]) ?_
  refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [hh]) ?_
  refine specR_congr (m' := ConRon.Arena.view h >>= fun v => match v with
    | .lam f' a' => lamMiss ks vsL n h f' a'
    | _ => lamMiss ks vsL n h f a)
    (by simp only [bind, StateT.bind]; rw [view_run, hv]; rfl) ?_
  refine specR_viewIv h (by simp) (by simp +decide [hfle] <;> rfl) (by simp +decide [hdir] <;> rfl) (by decide)
    (fun v P hv' _ _ => ?_)
  rw [hv] at hv'; cases hv'
  unfold lamMiss
  simp only [encEView, Enc.encBind, wordsAt, List.length_cons, List.length_nil, List.range_succ, List.range_zero,
    List.nil_append, List.zip_cons_cons, List.zip_nil_left, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append]
  refine specR_loadI' lA1 _ (P + BitVec.ofNat 64 (8 * 0)) _ (Enc.idxW f) (by decide) (by simp +decide [sev])
    rfl (List.mem_cons_self ..) ?_
  refine specR_loadI' lA2 _ (P + BitVec.ofNat 64 (8 * 1)) _ (Enc.idxW a) (by decide) (by simp +decide [sev])
    rfl (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ?_
  refine callI_spec C B hc.ilp ko khs ks usH vsL n ih lY lA1 f (by decide) (by simp +decide [hfu])
    (by simp +decide) (by simp +decide [hkp]) (by simp +decide [hus]) hp df hb
    (fun f' s1 H1 hp1 pv1 _ x1 _ _ => ?_)
  refine callI_spec (H := H1) C B hc.ilp ko khs ks usH vsL n ih lZ lA2 a (by decide) (by simp +decide [hfu])
    (by simp +decide) (by simp +decide [hkp]) (by simp +decide [hus]) pv1
    (by obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp da; rw [x1.expr a e he]; rfl) (blkAt_mono hb hp1)
    (fun a' s2 H2 hp2 _ _ _ _ _ => ?_)
  refine rebuild_spec (C := ctxH C H2) _ (eqW f' f &&& eqW a' a) (f' == f && a' == a) h _ _ (internLamE f' a') ?_
    (eqW2_iff _ _ _ _) (by simp +decide [hh]) ?_ ?_
  · simp +decide [sev, eqE, eqW]
  · exact setRetL_spec hok (hp1.trans hp2) hc.memoSet hc.memoIns h h (by simp +decide [hh]) (by simp +decide [hkb])
      (by simp +decide)
  · refine specR_internLamI ra (ctxOK_H hok H2) hc.internLam lW (vv lY) (vv lZ) f' a' (by decide) (by simp +decide)
      (by simp +decide) (fun r s3 => ?_)
    exact setRetL_spec hok (hp1.trans hp2) hc.memoSet hc.memoIns h r (by simp +decide [hh]) (by simp +decide [hkb])
      (by simp +decide)

end

/-- The `for` arm after a memo miss. -/
def forMiss (ks : List ConLeche.Name) (vsL : List ConLeche.Level) (n : Nat) (h f a : EIdx) : AM EIdx := do
  let f'' ← instLPGo ks vsL n f
  let a'' ← instLPGo ks vsL n a
  let r ← internRebuiltForallE h (f'' == f && a'' == a) f'' a''
  instLPSet (h, 0) r
  pure r

section
variable {σ : Type}
open ConRon.Bridge.ExprOps

theorem forI_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesILP C B) (ko : Nat) (khs : List NIdx) (ks : List ConLeche.Name) (usH : LsIdx)
    (vsL : List ConLeche.Level) (n : Nat) (ih : RecILP (σ := σ) C B ko khs ks usH vsL n)
    {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} (h f a : EIdx) (hv : s.store.view h = some (.forallE f a))
    (hp : PInv s khs ks usH vsL) (hden : (denoteE s.store h).isSome = true) (hb : BlkAt H ko (khs.map Enc.idxW))
    (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (hh : Γ.get pH = some (Enc.idxW h))
    (hkp : Γ.get pKp = some (cellA C ko)) (hus : Γ.get pUs = some (Enc.idxW usH))
    (hkb : Γ.get lKb = some C.KB) (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) (ctxH C H) s Γ M DI) (binI (C.mG (.e .instLP)) fInternForallE) s
      (instLPArmForallE ks vsL n h f a) (PostILP (ctxH C H)) := by
  obtain ⟨df, da⟩ := kids2 hp.ok.wf hv hden (f := f) (a := a) (Or.inr (Or.inr ⟨ConLeche.Expr.forallE, rfl⟩))
  refine specR_congr (m' := do match ← instLPGet (h, 0) with | some r => pure r | none => forMiss ks vsL n h f a)
    (by rw [instLPArmForallE]; rfl) ?_
  unfold binI
  refine probedL_spec hok hc.memoGet hc.memoProbe h _ _ hh hkb ?_
  unfold viewH
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [hfle]) ?_
  refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [hh]) ?_
  refine specR_congr (m' := ConRon.Arena.view h >>= fun v => match v with
    | .forallE f' a' => forMiss ks vsL n h f' a'
    | _ => forMiss ks vsL n h f a)
    (by simp only [bind, StateT.bind]; rw [view_run, hv]; rfl) ?_
  refine specR_viewIv h (by simp) (by simp +decide [hfle] <;> rfl) (by simp +decide [hdir] <;> rfl) (by decide)
    (fun v P hv' _ _ => ?_)
  rw [hv] at hv'; cases hv'
  unfold forMiss
  simp only [encEView, Enc.encBind, wordsAt, List.length_cons, List.length_nil, List.range_succ, List.range_zero,
    List.nil_append, List.zip_cons_cons, List.zip_nil_left, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append]
  refine specR_loadI' lA1 _ (P + BitVec.ofNat 64 (8 * 0)) _ (Enc.idxW f) (by decide) (by simp +decide [sev])
    rfl (List.mem_cons_self ..) ?_
  refine specR_loadI' lA2 _ (P + BitVec.ofNat 64 (8 * 1)) _ (Enc.idxW a) (by decide) (by simp +decide [sev])
    rfl (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ?_
  refine callI_spec C B hc.ilp ko khs ks usH vsL n ih lY lA1 f (by decide) (by simp +decide [hfu])
    (by simp +decide) (by simp +decide [hkp]) (by simp +decide [hus]) hp df hb
    (fun f' s1 H1 hp1 pv1 _ x1 _ _ => ?_)
  refine callI_spec (H := H1) C B hc.ilp ko khs ks usH vsL n ih lZ lA2 a (by decide) (by simp +decide [hfu])
    (by simp +decide) (by simp +decide [hkp]) (by simp +decide [hus]) pv1
    (by obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp da; rw [x1.expr a e he]; rfl) (blkAt_mono hb hp1)
    (fun a' s2 H2 hp2 _ _ _ _ _ => ?_)
  refine rebuild_spec (C := ctxH C H2) _ (eqW f' f &&& eqW a' a) (f' == f && a' == a) h _ _ (internForallEE f' a') ?_
    (eqW2_iff _ _ _ _) (by simp +decide [hh]) ?_ ?_
  · simp +decide [sev, eqE, eqW]
  · exact setRetL_spec hok (hp1.trans hp2) hc.memoSet hc.memoIns h h (by simp +decide [hh]) (by simp +decide [hkb])
      (by simp +decide)
  · refine specR_internForallEI ra (ctxOK_H hok H2) hc.internForallE lW (vv lY) (vv lZ) f' a' (by decide) (by simp +decide)
      (by simp +decide) (fun r s3 => ?_)
    exact setRetL_spec hok (hp1.trans hp2) hc.memoSet hc.memoIns h r (by simp +decide [hh]) (by simp +decide [hkb])
      (by simp +decide)

end

/-- The `letE` arm after a memo miss. -/
def letMiss (ks : List ConLeche.Name) (vsL : List ConLeche.Level) (n : Nat) (h ty v b : EIdx) : AM EIdx := do
  let t ← instLPGo ks vsL n ty
  let w ← instLPGo ks vsL n v
  let b' ← instLPGo ks vsL n b
  let r ← internRebuiltLetE h (t == ty && w == v && b' == b) t w b'
  instLPSet (h, 0) r
  pure r

theorem kids3 {st : EStore} (hwf : StoreWF st) {h ty v b : EIdx} (hv : st.view h = some (.letE ty v b))
    (hd : (denoteE st h).isSome = true) :
    (denoteE st ty).isSome = true ∧ (denoteE st v).isSome = true ∧ (denoteE st b).isSome = true := by
  rw [denoteE_view_eq hwf hv] at hd
  simp only [denoteEView, opt3] at hd
  split at hd <;> simp_all

section
variable {σ : Type}
open ConRon.Bridge.ExprOps

theorem letLP_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesILP C B) (ko : Nat) (khs : List NIdx) (ks : List ConLeche.Name) (usH : LsIdx)
    (vsL : List ConLeche.Level) (n : Nat) (ih : RecILP (σ := σ) C B ko khs ks usH vsL n)
    {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} (h ty v b : EIdx)
    (hv : s.store.view h = some (.letE ty v b))
    (hp : PInv s khs ks usH vsL) (hden : (denoteE s.store h).isSome = true) (hb : BlkAt H ko (khs.map Enc.idxW))
    (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (hh : Γ.get pH = some (Enc.idxW h))
    (hkp : Γ.get pKp = some (cellA C ko)) (hus : Γ.get pUs = some (Enc.idxW usH))
    (hkb : Γ.get lKb = some C.KB) (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) (ctxH C H) s Γ M DI) (letLP (C.mG (.e .instLP))) s
      (instLPArmLet ks vsL n h ty v b) (PostILP (ctxH C H)) := by
  obtain ⟨dty, dv, db⟩ := kids3 hp.ok.wf hv hden
  refine specR_congr (m' := do match ← instLPGet (h, 0) with | some r => pure r | none => letMiss ks vsL n h ty v b)
    (by rw [instLPArmLet]; rfl) ?_
  unfold letLP
  refine probedL_spec hok hc.memoGet hc.memoProbe h _ _ hh hkb ?_
  unfold viewH
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [hfle]) ?_
  refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [hh]) ?_
  refine specR_congr (m' := ConRon.Arena.view h >>= fun w => match w with
    | .letE ty' v' b' => letMiss ks vsL n h ty' v' b'
    | _ => letMiss ks vsL n h ty v b)
    (by simp only [bind, StateT.bind]; rw [view_run, hv]; rfl) ?_
  refine specR_viewIv h (by simp) (by simp +decide [hfle] <;> rfl) (by simp +decide [hdir] <;> rfl) (by decide)
    (fun w P hv' _ _ => ?_)
  rw [hv] at hv'; cases hv'
  unfold letMiss
  simp only [encEView, Enc.encLet, wordsAt, List.length_cons, List.length_nil, List.range_succ, List.range_zero,
    List.nil_append, List.zip_cons_cons, List.zip_nil_left, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append]
  refine specR_loadI' lA1 _ (P + BitVec.ofNat 64 (8 * 0)) _ (Enc.idxW ty) (by decide) (by simp +decide [sev])
    rfl (List.mem_cons_self ..) ?_
  refine specR_loadI' lA2 _ (P + BitVec.ofNat 64 (8 * 1)) _ (Enc.idxW v) (by decide) (by simp +decide [sev])
    rfl (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ?_
  refine specR_loadI' lA3 _ (P + BitVec.ofNat 64 (8 * 2)) _ (Enc.idxW b) (by decide) (by simp +decide [sev])
    rfl (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) ?_
  refine callI_spec C B hc.ilp ko khs ks usH vsL n ih lY lA1 ty (by decide) (by simp +decide [hfu])
    (by simp +decide) (by simp +decide [hkp]) (by simp +decide [hus]) hp dty hb
    (fun t s1 H1 hp1 pv1 _ x1 _ _ => ?_)
  refine callI_spec (H := H1) C B hc.ilp ko khs ks usH vsL n ih lZ lA2 v (by decide) (by simp +decide [hfu])
    (by simp +decide) (by simp +decide [hkp]) (by simp +decide [hus]) pv1
    (by obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp dv; rw [x1.expr v e he]; rfl) (blkAt_mono hb hp1)
    (fun w s2 H2 hp2 pv2 _ x2 _ _ => ?_)
  refine callI_spec (H := H2) C B hc.ilp ko khs ks usH vsL n ih lB lA3 b (by decide) (by simp +decide [hfu])
    (by simp +decide) (by simp +decide [hkp]) (by simp +decide [hus]) pv2
    (by obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp db; rw [x2.expr b e (x1.expr b e he)]; rfl)
    (blkAt_mono hb (hp1.trans hp2)) (fun b' s3 H3 hp3 _ _ _ _ _ => ?_)
  refine rebuild_spec (C := ctxH C H3) _ (eqW t ty &&& eqW w v &&& eqW b' b) (t == ty && w == v && b' == b) h _ _
    (internLetEE t w b') ?_ (eqW3_iff _ _ _ _ _ _) (by simp +decide [hh]) ?_ ?_
  · simp +decide [sev, eqE, eqW]
  · exact setRetL_spec hok (hp1.trans (hp2.trans hp3)) hc.memoSet hc.memoIns h h (by simp +decide [hh])
      (by simp +decide [hkb]) (by simp +decide)
  · refine specR_internLetI ra (ctxOK_H hok H3) hc.internLet lW (vv lY) (vv lZ) (vv lB) t w b' (by decide)
      (by simp +decide) (by simp +decide) (by simp +decide) (fun r s4 => ?_)
    exact setRetL_spec hok (hp1.trans (hp2.trans hp3)) hc.memoSet hc.memoIns h r (by simp +decide [hh])
      (by simp +decide [hkb]) (by simp +decide)

end

/-- The `proj` arm after a memo miss. -/
def projMiss (ks : List ConLeche.Name) (vsL : List ConLeche.Level) (n : Nat) (h : EIdx) (nm : NIdx) (i : Nat)
    (e : EIdx) : AM EIdx := do
  let u ← instLPGo ks vsL n e
  let r ← internRebuiltProj h (u == e) nm i u
  instLPSet (h, 0) r
  pure r

section
variable {σ : Type}
open ConRon.Bridge.ExprOps

theorem projRestI_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesILP C B) (ko : Nat) (khs : List NIdx) (ks : List ConLeche.Name) (usH : LsIdx)
    (vsL : List ConLeche.Level) (n : Nat) (ih : RecILP (σ := σ) C B ko khs ks usH vsL n)
    {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} (h : EIdx) (nm : NIdx) (i : Nat) (e : EIdx)
    (hi : i < 2 ^ 64) (hp : PInv s khs ks usH vsL) (hde : (denoteE s.store e).isSome = true)
    (hb : BlkAt H ko (khs.map Enc.idxW))
    (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (hh : Γ.get pH = some (Enc.idxW h))
    (hkp : Γ.get pKp = some (cellA C ko)) (hus : Γ.get pUs = some (Enc.idxW usH))
    (hkb : Γ.get lKb = some C.KB) (ha1 : Γ.get lA1 = some (Enc.idxW nm)) (ha2 : Γ.get lA2 = some (Enc.idxW e))
    (hlb : Γ.get lB = some (BitVec.ofNat 64 i)) :
    SpecR (Inv (σ := σ) (ctxH C H) s Γ M DI) (projRestI (C.mG (.e .instLP))) s (projMiss ks vsL n h nm i e)
      (PostILP (ctxH C H)) := by
  unfold projRestI projMiss
  refine specR_ifI (.shift .lsr (vv lB) (.const 63)) (BitVec.ofNat 64 i >>> (63 : BitVec 64).toNat)
    (by simp [sev, hlb]) (fun _ => specR_hangI) (fun hw => ?_)
  have hi63 := (shr63_eq_zero i hi).mp hw
  refine callI_spec C B hc.ilp ko khs ks usH vsL n ih lY lA2 e (by decide) hfu ha2 hkp hus hp hde hb
    (fun u s1 H1 hp1 _ _ _ _ _ => ?_)
  unfold internRebuiltProj
  refine rebuild_spec (C := ctxH C H1) _ (eqW u e) (u == e) h _ _ (internProjE nm i u)
    (sev_eqE _ _ _ _ _ (by simp +decide) (by simp +decide [ha2])) (eqW_iff _ _) (by simp +decide [hh]) ?_ ?_
  · exact setRetL_spec hok hp1 hc.memoSet hc.memoIns h h (by simp +decide [hh]) (by simp +decide [hkb])
      (by simp +decide)
  · refine specR_internProjI ra (ctxOK_H hok H1) hc.internProj lW (vv lA1) (vv lY) (vv lB) nm i u hi63 (by decide)
      (by simp +decide [ha1]) (by simp +decide) (by simp +decide [hlb]) (fun r s2 => ?_)
    exact setRetL_spec hok hp1 hc.memoSet hc.memoIns h r (by simp +decide [hh]) (by simp +decide [hkb])
      (by simp +decide)

theorem projI_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesILP C B) (ko : Nat) (khs : List NIdx) (ks : List ConLeche.Name) (usH : LsIdx)
    (vsL : List ConLeche.Level) (n : Nat) (ih : RecILP (σ := σ) C B ko khs ks usH vsL n)
    {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} (h : EIdx) (nm : NIdx) (i : Nat) (e : EIdx)
    (hv : s.store.view h = some (.proj nm i e))
    (hp : PInv s khs ks usH vsL) (hden : (denoteE s.store h).isSome = true) (hb : BlkAt H ko (khs.map Enc.idxW))
    (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (hh : Γ.get pH = some (Enc.idxW h))
    (hkp : Γ.get pKp = some (cellA C ko)) (hus : Γ.get pUs = some (Enc.idxW usH))
    (hkb : Γ.get lKb = some C.KB) (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) (ctxH C H) s Γ M DI) (projI (C.mG (.e .instLP))) s
      (instLPArmProj ks vsL n h nm i e) (PostILP (ctxH C H)) := by
  have hde : (denoteE s.store e).isSome = true := by
    have hd := hden
    rw [denoteE_view_eq hp.ok.wf hv] at hd
    simp only [denoteEView, opt2] at hd
    split at hd <;> simp_all
  refine specR_congr (m' := do match ← instLPGet (h, 0) with | some r => pure r | none => projMiss ks vsL n h nm i e)
    (by rw [instLPArmProj]; rfl) ?_
  unfold projI
  refine probedL_spec hok hc.memoGet hc.memoProbe h _ _ hh hkb ?_
  unfold viewH
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [hfle]) ?_
  refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [hh]) ?_
  refine specR_congr (m' := ConRon.Arena.view h >>= fun w => match w with
    | .proj nm' i' e' => projMiss ks vsL n h nm' i' e'
    | _ => projMiss ks vsL n h nm i e)
    (by simp only [bind, StateT.bind]; rw [view_run, hv]; rfl) ?_
  refine specR_viewIv h (by simp) (by simp +decide [hfle] <;> rfl) (by simp +decide [hdir] <;> rfl) (by decide)
    (fun w P hv' _ hsh => ?_)
  rw [hv] at hv'; cases hv'
  simp only
  refine specR_loadI' lA1 _ (P + 0) (P + BitVec.ofNat 64 0) (Enc.idxW nm) (by decide) (by simp [sev]) rfl
    (wordsAt_mem0 _ _ _ _) ?_
  refine specR_loadI' lA2 _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW e) (by decide) (by simp +decide [sev]) rfl
    (wordsAt_mem1 _ _ _ _ _) ?_
  have hlen : (encEView (.proj nm i e)).length = 2 + (Enc.limbs i).length := by
    simp [encEView, Enc.encProj]; omega
  by_cases i0 : i = 0
  · subst i0
    refine specR_ifI _ 1 (by simp +decide [sev, hlen, Enc.limbs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
    refine specR_assignI lB (.const 0) 0 (by decide) rfl ?_
    exact projRestI_spec ra C hok B hc ko khs ks usH vsL n ih h nm 0 e (by decide) hp hde hb (by simp +decide [hfu])
      (by simp +decide [hh]) (by simp +decide [hkp]) (by simp +decide [hus]) (by simp +decide [hkb])
      (by simp +decide) (by simp +decide) (by simp)
  · by_cases ib : i < 2 ^ 64
    · have hl : Enc.limbs i = [BitVec.ofNat 64 i] := by rw [limbs_small i ib]; simp [i0]
      refine specR_ifI _ 0 (by simp +decide [sev, hlen, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, hlen, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
      refine specR_loadI' lB _ (P + 16) (P + BitVec.ofNat 64 16) (BitVec.ofNat 64 i) (by decide)
        (by simp +decide [sev]) rfl
        (by have := wordsAt_mem2 P (Enc.idxW nm) (Enc.idxW e) (BitVec.ofNat 64 i) [] (M := [])
            simpa [encEView, Enc.encProj, hl] using this) ?_
      exact projRestI_spec ra C hok B hc ko khs ks usH vsL n ih h nm i e ib hp hde hb (by simp +decide [hfu])
        (by simp +decide [hh]) (by simp +decide [hkp]) (by simp +decide [hus]) (by simp +decide [hkb])
        (by simp +decide) (by simp +decide) (by simp)
    · have hl := limbs_len_ge2 i (by omega)
      have hlt : 2 + (Enc.limbs i).length < 2 ^ 61 := by rw [← hlen]; exact hsh
      have hn2 : BitVec.ofNat 64 (2 + (Enc.limbs i).length) ≠ 2#64 := by
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      have hn3 : BitVec.ofNat 64 (2 + (Enc.limbs i).length) ≠ 3#64 := by
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      refine specR_ifI _ 0 (by simp +decide [sev, hlen, hn2, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
      exact specR_ifI _ 0 (by simp +decide [sev, hlen, hn3, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => specR_hangI)

end

/-- The `fvar` arm after a memo miss. -/
def fvarMiss (ks : List ConLeche.Name) (vsL : List ConLeche.Level) (n : Nat) (h : EIdx) (idx : Nat) (ty : EIdx) :
    AM EIdx := do
  let t ← instLPGo ks vsL n ty
  let r ← internRebuiltFVar h (t == ty) idx t
  instLPSet (h, 0) r
  pure r

section
variable {σ : Type}
open ConRon.Bridge.ExprOps

theorem specR_internFVarI {β : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} (hok : CtxOK C)
    (hcode : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k : EIdx → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x : MlS) (e1 e2 : ExpHOL 64) (ty : EIdx) (idx : Nat)
    (hi : idx < 2 ^ 63) (hx : x ∈ D)
    (he1 : sev Γ e1 = some (Enc.idxW ty)) (he2 : sev Γ e2 = some (BitVec.ofNat 64 idx))
    (hk : ∀ h s', SpecR (Inv C s' ((x, Enc.idxW h) :: Γ) [] D) rest s' (k h) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) fInternFVar [e1, e2]) rest) s
      (internFVarE idx ty >>= k) R :=
  specR_call2I x fInternFVar lEty lIw (by decide) e1 e2 fvarBody (Enc.idxW ty) (BitVec.ofNat 64 idx) hx hcode he1 he2
    (PostE C) (fun _ _ _ _ hp => hp.2)
    (fun u hu h1 h2 v hv => by
      subst hv
      exact fvar_body_spec ra C hok s idx ty hi _ ⟨hu, fun y w hy => by
        simp only [Env.get] at hy
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact h1
        · split at hy
          · rename_i e; subst e; simp at hy; subst hy; exact h2
          · simp at hy⟩)
    (fun h w s' st hp => by obtain ⟨rfl, _⟩ := hp; exact hk h s')

theorem fvarRestI_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesILP C B) (ko : Nat) (khs : List NIdx) (ks : List ConLeche.Name) (usH : LsIdx)
    (vsL : List ConLeche.Level) (n : Nat) (ih : RecILP (σ := σ) C B ko khs ks usH vsL n)
    {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} (h : EIdx) (idx : Nat) (ty : EIdx)
    (hi : idx < 2 ^ 64) (hp : PInv s khs ks usH vsL) (hdt : (denoteE s.store ty).isSome = true)
    (hb : BlkAt H ko (khs.map Enc.idxW))
    (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (hh : Γ.get pH = some (Enc.idxW h))
    (hkp : Γ.get pKp = some (cellA C ko)) (hus : Γ.get pUs = some (Enc.idxW usH))
    (hkb : Γ.get lKb = some C.KB) (ha1 : Γ.get lA1 = some (Enc.idxW ty))
    (hlb : Γ.get lB = some (BitVec.ofNat 64 idx)) :
    SpecR (Inv (σ := σ) (ctxH C H) s Γ M DI) (fvarRestI (C.mG (.e .instLP))) s (fvarMiss ks vsL n h idx ty)
      (PostILP (ctxH C H)) := by
  unfold fvarRestI fvarMiss
  refine specR_ifI (.shift .lsr (vv lB) (.const 63)) (BitVec.ofNat 64 idx >>> (63 : BitVec 64).toNat)
    (by simp [sev, hlb]) (fun _ => specR_hangI) (fun hw => ?_)
  have hi63 := (shr63_eq_zero idx hi).mp hw
  refine callI_spec C B hc.ilp ko khs ks usH vsL n ih lY lA1 ty (by decide) hfu ha1 hkp hus hp hdt hb
    (fun t s1 H1 hp1 _ _ _ _ _ => ?_)
  unfold internRebuiltFVar
  refine rebuild_spec (C := ctxH C H1) _ (eqW t ty) (t == ty) h _ _ (internFVarE idx t)
    (sev_eqE _ _ _ _ _ (by simp +decide) (by simp +decide [ha1])) (eqW_iff _ _) (by simp +decide [hh]) ?_ ?_
  · exact setRetL_spec hok hp1 hc.memoSet hc.memoIns h h (by simp +decide [hh]) (by simp +decide [hkb])
      (by simp +decide)
  · refine specR_internFVarI ra (ctxOK_H hok H1) hc.internFVar lW (vv lY) (vv lB) t idx hi63 (by decide)
      (by simp +decide) (by simp +decide [hlb]) (fun r s2 => ?_)
    exact setRetL_spec hok hp1 hc.memoSet hc.memoIns h r (by simp +decide [hh]) (by simp +decide [hkb])
      (by simp +decide)

theorem fvarI_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesILP C B) (ko : Nat) (khs : List NIdx) (ks : List ConLeche.Name) (usH : LsIdx)
    (vsL : List ConLeche.Level) (n : Nat) (ih : RecILP (σ := σ) C B ko khs ks usH vsL n)
    {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} (h : EIdx) (idx : Nat) (ty : EIdx)
    (hv : s.store.view h = some (.fvar idx ty))
    (hp : PInv s khs ks usH vsL) (hden : (denoteE s.store h).isSome = true) (hb : BlkAt H ko (khs.map Enc.idxW))
    (hfu : Γ.get pFu = some (BitVec.ofNat 64 (n + 1))) (hh : Γ.get pH = some (Enc.idxW h))
    (hkp : Γ.get pKp = some (cellA C ko)) (hus : Γ.get pUs = some (Enc.idxW usH))
    (hkb : Γ.get lKb = some C.KB) (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) (ctxH C H) s Γ M DI) (fvarI (C.mG (.e .instLP))) s
      (instLPArmFVar ks vsL n h idx ty) (PostILP (ctxH C H)) := by
  have hdt : (denoteE s.store ty).isSome = true := by
    have hd := hden
    rw [denoteE_view_eq hp.ok.wf hv] at hd
    simp only [denoteEView] at hd
    cases e : denoteE s.store ty <;> simp_all
  refine specR_congr (m' := do match ← instLPGet (h, 0) with | some r => pure r | none => fvarMiss ks vsL n h idx ty)
    (by rw [instLPArmFVar]; rfl) ?_
  unfold fvarI
  refine probedL_spec hok hc.memoGet hc.memoProbe h _ _ hh hkb ?_
  unfold viewH
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [hfle]) ?_
  refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [hh]) ?_
  refine specR_congr (m' := ConRon.Arena.view h >>= fun w => match w with
    | .fvar idx' ty' => fvarMiss ks vsL n h idx' ty'
    | _ => fvarMiss ks vsL n h idx ty)
    (by simp only [bind, StateT.bind]; rw [view_run, hv]; rfl) ?_
  refine specR_viewIv h (by simp) (by simp +decide [hfle] <;> rfl) (by simp +decide [hdir] <;> rfl) (by decide)
    (fun w P hv' _ hsh => ?_)
  rw [hv] at hv'; cases hv'
  simp only
  refine specR_loadI' lA1 _ P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp [sev]) (by simp)
    (wordsAt_mem0 _ _ _ _) ?_
  have hlen : (encEView (.fvar idx ty)).length = 1 + (Enc.limbs idx).length := by
    simp [encEView, Enc.encFVar]; omega
  by_cases i0 : idx = 0
  · subst i0
    refine specR_ifI _ 1 (by simp +decide [sev, hlen, Enc.limbs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
    refine specR_assignI lB (.const 0) 0 (by decide) rfl ?_
    exact fvarRestI_spec ra C hok B hc ko khs ks usH vsL n ih h 0 ty (by decide) hp hdt hb (by simp +decide [hfu])
      (by simp +decide [hh]) (by simp +decide [hkp]) (by simp +decide [hus]) (by simp +decide [hkb])
      (by simp +decide) (by simp)
  · by_cases ib : idx < 2 ^ 64
    · have hl : Enc.limbs idx = [BitVec.ofNat 64 idx] := by rw [limbs_small idx ib]; simp [i0]
      refine specR_ifI _ 0 (by simp +decide [sev, hlen, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
      refine specR_ifI _ 1 (by simp +decide [sev, hlen, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
      refine specR_loadI' lB _ (P + 8) (P + BitVec.ofNat 64 8) (BitVec.ofNat 64 idx) (by decide)
        (by simp +decide [sev]) rfl
        (by have := wordsAt_mem1 P (Enc.idxW ty) (BitVec.ofNat 64 idx) [] (M := [])
            simpa [encEView, Enc.encFVar, hl] using this) ?_
      exact fvarRestI_spec ra C hok B hc ko khs ks usH vsL n ih h idx ty ib hp hdt hb (by simp +decide [hfu])
        (by simp +decide [hh]) (by simp +decide [hkp]) (by simp +decide [hus]) (by simp +decide [hkb])
        (by simp +decide) (by simp)
    · have hl := limbs_len_ge2 idx (by omega)
      have hlt : 1 + (Enc.limbs idx).length < 2 ^ 61 := by rw [← hlen]; exact hsh
      have hn1 : BitVec.ofNat 64 (1 + (Enc.limbs idx).length) ≠ 1#64 := by
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      have hn2 : BitVec.ofNat 64 (1 + (Enc.limbs idx).length) ≠ 2#64 := by
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      refine specR_ifI _ 0 (by simp +decide [sev, hlen, hn1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => ?_)
      exact specR_ifI _ 0 (by simp +decide [sev, hlen, hn2, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun hw => absurd rfl hw) (fun _ => specR_hangI)

end

section
variable {σ : Type}
open ConRon.Bridge.ExprOps

/-- A call of an expression-node intern wrapper, in a caller (the image is kept). -/
theorem callE_spec {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM EIdx} {k : EIdx → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f : MlS) (ps : List MlS) (es : List (ExpHOL 64)) (B : ProgHOL 64) (vs : List (BitVec 64))
    (hnd : ps.Nodup) (hl : vs.length = ps.length)
    (hx : x ∈ D) (hC : C.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), B, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs)
    (hspec : SpecR (Pre (σ := σ) C s (ps.zip vs)) B s m (PostE C))
    (hk : ∀ h s', SpecR (Inv C s' ((x, Enc.idxW h) :: Γ) [] D) rest s' (k h) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f es) rest) s (m >>= k) R :=
  specR_callNIM x f ps es B vs hnd hl hx hC hes (PostE C) (fun _ _ _ _ hp => hp.2)
    (fun u hu _ hlk => fun w hw => by subst hw; exact hspec _ (pre_of_lookups hu ps vs hl hlk))
    (fun h w s' st hp => by obtain ⟨rfl, _⟩ := hp; exact hk h s')

theorem sortI_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (B : ProgHOL 64)
    (hc : CodesILP C B) (ko : Nat) (khs : List NIdx) (ks : List ConLeche.Name) (usH : LsIdx)
    (vsL : List ConLeche.Level) {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} (h : EIdx) (u : LIdx)
    (hv : s.store.view h = some (.sort u))
    (hp : PInv s khs ks usH vsL) (hden : (denoteE s.store h).isSome = true) (hb : BlkAt H ko (khs.map Enc.idxW))
    (hh : Γ.get pH = some (Enc.idxW h))
    (hkp : Γ.get pKp = some (cellA C ko)) (hus : Γ.get pUs = some (Enc.idxW usH))
    (hfle : Γ.get lFle = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR) :
    SpecR (Inv (σ := σ) (ctxH C H) s Γ M DI) sortI s
      (do let hl ← substLMemoAt ks vsL u; internRebuiltSort h (hl == u) hl) (PostILP (ctxH C H)) := by
  obtain ⟨l, hdl⟩ : ∃ l, denoteL s.store.ls u = some l := by
    have hd := hden
    rw [denoteE_view_eq hp.ok.wf hv] at hd
    simp only [denoteEView] at hd
    cases e : denoteL s.store.ls u <;> simp_all
  obtain ⟨uh2, hu2, hvs2⟩ : ∃ uh2, s.store.lss.view usH = some uh2 ∧ denoteLList s.store.ls uh2 = some vsL := by
    have := hp.levels; unfold denoteLs at this; split at this
    · simp at this
    · rename_i v hv'; exact ⟨v, hv', this⟩
  unfold sortI viewH
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [hfle]) ?_
  refine specR_assignI lDh (vv pH) (Enc.idxW h) (by decide) (by simp +decide [hh]) ?_
  refine specR_congr (m' := ConRon.Arena.view h >>= fun w => match w with
    | .sort u' => (do let hl ← substLMemoAt ks vsL u'; internRebuiltSort h (hl == u') hl)
    | _ => (do let hl ← substLMemoAt ks vsL u; internRebuiltSort h (hl == u) hl))
    (by simp only [bind, StateT.bind]; rw [view_run, hv]; rfl) ?_
  refine specR_viewIv h (by simp) (by simp +decide [hfle] <;> rfl) (by simp +decide [hdir] <;> rfl) (by decide)
    (fun w P hv' _ _ => ?_)
  rw [hv] at hv'; cases hv'
  simp only
  refine specR_loadI' lA1 (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW u) (by decide) (by simp [sev]) (by simp)
    (by simpa [encEView, Enc.encSort] using wordsAt_mem0 P (Enc.idxW u) [] M) ?_
  refine specR_callNIH lA2 fSubstLH substMParams [vv lA1, vv pKp, vv pUs] (substLHBody C)
    [Enc.idxW u, cellA C ko, Enc.idxW usH] (by decide) rfl (by decide) hc.substLH
    ⟨by simp +decide, by simp +decide [hkp], by simp +decide [hus], trivial⟩
    (PostSLH (ctxH C H) s ks vsL l) (fun a w s' _ => w = Enc.idxW a)
    (fun a w s' st ⟨H', hpH, hw, hsr, _⟩ => ⟨H', hpH, hw, hsr⟩)
    (fun u0 hu0 _ hlk => fun w hw => by
      subst hw
      exact substLH_spec ra C hok hc.substM hc.neq hc.goM hc.lZero hc.lSucc hc.lMax hc.lImax hc.lParam hc.lv s ko khs
        ks usH uh2 vsL hp.names hu2 hvs2 hp.cl hp.ml hp.ok.wf H hb u l hdl _ (pre_of_lookups hu0 substMParams _ rfl hlk))
    (fun hl w s1 H1 hp1 hw => ?_)
  subst hw
  unfold internRebuiltSort
  by_cases e : hl = u
  · subst e
    refine specR_ifI _ 1 (by simp +decide [eqE, sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun hw => absurd hw (by decide))
    simp only [beq_self_eq_true, ite_true]
    exact specR_returnI (vv pH) (Enc.idxW h) (by simp +decide [hh])
      (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · have hne : Enc.idxW hl ≠ Enc.idxW u := fun x => e (Enc.idxW_inj x)
    refine specR_ifI _ 0 (by simp +decide [eqE, sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]) (fun hw => absurd rfl hw) (fun _ => ?_)
    have eb : (hl == u) = false := by simp [e]
    rw [eb]; simp only [Bool.false_eq_true, ite_false]
    refine specR_congr (m' := internSortE hl >>= fun r => pure r) (by simp) ?_
    refine callE_spec (C := ctxH C H1) lW fInternSort [lEu] [vv lA2] sortBody [Enc.idxW hl] (by decide) rfl
      (by decide) hc.internSort ⟨by simp +decide, trivial⟩ (sort_body_spec ra (ctxH C H1) (ctxOK_H hok H1) s1 hl)
      (fun r s2 => ?_)
    exact specR_returnI (vv lW) (Enc.idxW r) (by simp)
      (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.ILP
