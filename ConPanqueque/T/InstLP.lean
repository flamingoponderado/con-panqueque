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

end ConPanqueque.T.ILP
