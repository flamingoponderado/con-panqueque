import ConPanqueque.T.LInternLv
import ConPanqueque.T.LvlSubstM
import ConRon.Arena.ExprOps
import ConRon.Bridge.SpecsL
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `substLMemoAt`: substitute at a level handle, re-intern

The twin memoizes the handle-level answer in `memos.instLPLC`; the port recomputes (substitute, then
`internLv`). A memo row is the re-intern of its substituted readback (`MemoLOK`), so on a well-formed
store the recomputation finds the memoized handle and changes nothing.
-/

namespace ConPanqueque.T

def withC (s : AState) (c : Caches) : AState := { s with caches := c }

theorem internNNode_frameC (v : NNodeView) (s : AState) (c : Caches) :
    internNNode v (withC s c) = (internNNode v s).map (fun p => (p.1, withC p.2 c)) := by
  unfold internNNode
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, Except.bind,
    Except.pure, withC]
  cases s.store.ns.find? v with
  | some h => rfl
  | none =>
    simp only
    by_cases hc : (if s.store.ns.scratchOn = true then s.store.ns.scr.sizeOf v else s.store.ns.pers.sizeOf v) <
        Idx.idxCap
    · rw [if_pos hc, if_pos hc]; rfl
    · rw [if_neg hc, if_neg hc]; rfl

theorem internLNode_frameC (v : LNodeView) (s : AState) (c : Caches) :
    internLNode v (withC s c) = (internLNode v s).map (fun p => (p.1, withC p.2 c)) := by
  unfold internLNode
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, Except.bind,
    Except.pure, withC]
  cases s.store.ls.find? v with
  | some h => rfl
  | none =>
    simp only
    by_cases hc : (if s.store.ls.scratchOn = true then s.store.ls.scr.sizeOf v else s.store.ls.pers.sizeOf v) <
        Idx.idxCap
    · rw [if_pos hc, if_pos hc]; rfl
    · rw [if_neg hc, if_neg hc]; rfl

theorem internName_frameC (c : Caches) : ∀ (n : ConLeche.Name) (s : AState),
    internName n (withC s c) = (internName n s).map (fun p => (p.1, withC p.2 c)) := by
  intro n
  induction n with
  | anonymous => intro s; simp only [internName]; exact internNNode_frameC _ s c
  | str p x ih =>
    intro s
    simp only [internName, bind, StateT.bind, Except.bind]
    rw [ih s]
    cases internName p s with
    | error e => rfl
    | ok q => exact internNNode_frameC _ q.2 c
  | num p x ih =>
    intro s
    simp only [internName, bind, StateT.bind, Except.bind]
    rw [ih s]
    cases internName p s with
    | error e => rfl
    | ok q => exact internNNode_frameC _ q.2 c

theorem internLevel_frameC (c : Caches) : ∀ (l : ConLeche.Level) (s : AState),
    internLevel l (withC s c) = (internLevel l s).map (fun p => (p.1, withC p.2 c)) := by
  intro l
  induction l with
  | zero => intro s; simp only [internLevel]; exact internLNode_frameC _ s c
  | succ u ih =>
    intro s
    simp only [internLevel, bind, StateT.bind, Except.bind]
    rw [ih s]
    cases internLevel u s with
    | error e => rfl
    | ok q => exact internLNode_frameC _ q.2 c
  | max u v ihu ihv =>
    intro s
    simp only [internLevel, bind, StateT.bind, Except.bind]
    rw [ihu s]
    cases internLevel u s with
    | error e => rfl
    | ok q =>
      simp only [Except.map]
      rw [ihv q.2]
      cases internLevel v q.2 with
      | error e => rfl
      | ok q' => exact internLNode_frameC _ q'.2 c
  | imax u v ihu ihv =>
    intro s
    simp only [internLevel, bind, StateT.bind, Except.bind]
    rw [ihu s]
    cases internLevel u s with
    | error e => rfl
    | ok q =>
      simp only [Except.map]
      rw [ihv q.2]
      cases internLevel v q.2 with
      | error e => rfl
      | ok q' => exact internLNode_frameC _ q'.2 c
  | param n =>
    intro s
    simp only [internLevel, bind, StateT.bind, Except.bind]
    rw [internName_frameC c n s]
    cases internName n s with
    | error e => rfl
    | ok q => exact internLNode_frameC _ q.2 c


theorem denoteL_of_aux (ls : LStore) (rk : LIdx → Nat) (h : LWFAt ls rk) (i : LIdx) (f : Nat) (l : ConLeche.Level)
    (hd : denoteLAux ls f i = some l) : denoteL ls i = some l := by
  unfold denoteL
  by_cases hf : f ≤ ls.nodeCount + 1
  · exact denoteLAux_mono ls f _ i l hf hd
  · obtain ⟨v, hv⟩ := lview_of_denote ls f i l hd
    have hr : rk i < ls.nodeCount := by
      cases hp : i.isPersistent with
      | true => have := h.rankP i hp (by simp [hv]); simp only [LStore.nodeCount] at *; omega
      | false => exact h.rankS i hp (by simp [hv])
    rw [denoteLAux_congr h (rk i + 1) i (ls.nodeCount + 1) f (by omega) (by omega) (by omega)]; exact hd

/-- A row of the level substitution memo is the re-intern of its substituted readback. -/
def MemoLOK (s : AState) (ks : List ConLeche.Name) (vs : List ConLeche.Level) : Prop :=
  ∀ u r, s.memos.instLPLC[u]? = some r → ∃ l, denoteL s.store.ls u = some l ∧
    denoteL s.store.ls r = some (ConLeche.Level.subst ks vs l)

theorem readLevelM_eq (u : LIdx) (s : AState) (l : ConLeche.Level) (hrl : ReadLCacheOK s.caches.readLC s.store)
    (hd : denoteL s.store.ls u = some l) :
    ∃ c1 : Caches, readLevelM u s = .ok (l, withC s c1) ∧ c1 = { s.caches with readLC := c1.readLC } ∧
      ReadLCacheOK c1.readLC s.store := by
  unfold readLevelM
  rcases hc : s.caches.readLC[u]? with _ | l'
  · refine ⟨{ s.caches with readLC := s.caches.readLC.insert u l }, ?_, rfl, ?_⟩
    · simp [hc, hd, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, bind, StateT.bind, pure,
        StateT.pure, Except.bind, Except.pure, withC]
    · intro k v hk
      simp only [Std.HashMap.getElem?_insert] at hk
      split at hk
      · rename_i e; simp at e; subst e; simp at hk; subst hk; exact hd
      · exact hrl k v hk
  · have := hrl u l' hc
    rw [hd] at this; cases this
    refine ⟨s.caches, ?_, rfl, hrl⟩
    simp [hc, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure, Except.bind,
      Except.pure, withC]

theorem readL_ext {tbl : Std.HashMap LIdx ConLeche.Level} {st st' : EStore} (h : ReadLCacheOK tbl st) (hx : Ext st st') :
    ReadLCacheOK tbl st' := fun k u hk => denoteL_ext (h k u hk) hx

theorem substLMemoAt_run (ks : List ConLeche.Name) (vs : List ConLeche.Level) (s : AState) (u : LIdx)
    (l : ConLeche.Level) (hu : denoteL s.store.ls u = some l) (hrl : ReadLCacheOK s.caches.readLC s.store)
    (hm : MemoLOK s ks vs) (hwf : StoreWF s.store) (h : LIdx) (s'' : AState)
    (hint : internLevel (ConLeche.Level.subst ks vs l) s = .ok (h, s'')) :
    ∃ s3, substLMemoAt ks vs u s = .ok (h, s3) ∧ s3.store = s''.store ∧ s3.pins = s.pins ∧
      s3.memos = { s.memos with instLPLC := s3.memos.instLPLC } ∧
      s3.caches = { s.caches with readLC := s3.caches.readLC } ∧
      ReadLCacheOK s3.caches.readLC s3.store ∧ MemoLOK s3 ks vs := by
  obtain ⟨q1, q2, -, -, -, q6, q7, q8, q9⟩ :=
    AM.of_run (P := fun t => t = s) rfl hint (internLevel_spec s _ hwf)
  unfold substLMemoAt
  rcases hc : s.memos.instLPLC[u]? with _ | r
  · obtain ⟨c1, e1, ec1, ok1⟩ := readLevelM_eq u s l hrl hu
    have hint1 := internLevel_frameC c1 (ConLeche.Level.subst ks vs l) s
    rw [hint] at hint1
    simp only [withC, Except.map] at hint1 e1
    refine ⟨{ withC s'' c1 with memos := { s''.memos with instLPLC := s''.memos.instLPLC.insert u h } }, ?_, rfl,
      by simp [withC, q8], by simp [q6], by simp [withC]; exact ec1, ?_, ?_⟩
    · simp [instLPLGet, instLPLSet, hc, e1, hint1, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, bind,
        StateT.bind, pure, StateT.pure, Except.bind, Except.pure, Except.map, withC]
    · exact readL_ext ok1 q2
    · intro k r' hk
      simp only [withC, Std.HashMap.getElem?_insert] at hk
      split at hk
      · rename_i e; simp at e; subst e; simp at hk; subst hk
        exact ⟨l, denoteL_ext hu q2, q9⟩
      · rw [q6] at hk
        obtain ⟨l', h1, h2⟩ := hm k r' hk
        exact ⟨l', denoteL_ext h1 q2, denoteL_ext h2 q2⟩
  · obtain ⟨l', h1, h2⟩ := hm u r hc
    rw [hu] at h1; cases h1
    obtain ⟨⟨rkL, hL⟩, ⟨rkN, hN⟩⟩ := wf_parts hwf
    have hre := internLevel_denote s rkL hL rkN hN _ _ r h2
    rw [hint] at hre
    simp only [Except.ok.injEq, Prod.mk.injEq] at hre
    obtain ⟨e1, e2⟩ := hre
    subst e1; subst e2
    refine ⟨_, ?_, rfl, rfl, rfl, rfl, hrl, hm⟩
    simp [instLPLGet, hc, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure,
      Except.bind, Except.pure]

end ConPanqueque.T
