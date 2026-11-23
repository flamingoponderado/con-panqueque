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
  .seq (callI lY lA1)
    (rebuild (eqE lY lA1) (.call (some (some (.local, lW), none)) fInternFVar [vv lY, vv lB]) (setRetL G))

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
  .seq (callI lY lA2)
    (rebuild (eqE lY lA2) (.call (some (some (.local, lW), none)) fInternProj [vv lA1, vv lY, vv lB]) (setRetL G))

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

end ConPanqueque.T.ILP
