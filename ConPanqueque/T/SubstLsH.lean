import ConPanqueque.T.SubstLH
import ConPanqueque.T.LsInternT
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `substLsMemoAt`: substitute at a level-list handle, re-intern

The list analogue of `SubstLH`: the twin memoizes in `memos.instLPLsC`; a row is the re-intern of its
substituted readback (`MemoLsOK`), so on a well-formed store the port's recomputation finds it.
-/

namespace ConPanqueque.T

theorem internLsNode_frameC (v : LsNodeView) (s : AState) (c : Caches) :
    internLsNode v (withC s c) = (internLsNode v s).map (fun p => (p.1, withC p.2 c)) := by
  unfold internLsNode
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, Except.bind,
    Except.pure, withC]
  cases s.store.lss.find? v with
  | some h => rfl
  | none =>
    simp only
    by_cases hc : (if s.store.lss.scratchOn = true then s.store.lss.scr.sizeOf v else s.store.lss.pers.sizeOf v) <
        Idx.idxCap
    · rw [if_pos hc, if_pos hc]; rfl
    · rw [if_neg hc, if_neg hc]; rfl

theorem internLevelList_frameC (c : Caches) : ∀ (us : List ConLeche.Level) (s : AState),
    internLevelList us (withC s c) = (internLevelList us s).map (fun p => (p.1, withC p.2 c)) := by
  intro us
  induction us with
  | nil => intro s; rfl
  | cons u us ih =>
    intro s
    simp only [internLevelList, bind, StateT.bind, Except.bind]
    rw [internLevel_frameC c u s]
    cases internLevel u s with
    | error e => rfl
    | ok q =>
      simp only [Except.map]
      rw [ih q.2]
      cases internLevelList us q.2 with
      | error e => rfl
      | ok q' => rfl

theorem internLevels_frameC (c : Caches) (us : List ConLeche.Level) (s : AState) :
    internLevels us (withC s c) = (internLevels us s).map (fun p => (p.1, withC p.2 c)) := by
  simp only [internLevels, bind, StateT.bind, Except.bind]
  rw [internLevelList_frameC c us s]
  cases internLevelList us s with
  | error e => rfl
  | ok q => exact internLsNode_frameC _ q.2 c

theorem lsfind_of_view (lss : LsStore) (hw : LsWF lss) (h : LsIdx) (v : LsNodeView)
    (hv : lss.view h = some v) : lss.find? v = some h := by
  unfold LsStore.find?
  cases hp : h.isPersistent with
  | true => rw [(hw.consP v h).mpr ⟨hv, hp⟩]
  | false =>
    have hs := (hw.consS v h).mpr ⟨hv, hp⟩
    rw [hw.fresh v h hs]
    have hon : lss.scratchOn = true := by
      cases e : lss.scratchOn with
      | true => rfl
      | false => simp [LsStore.view, hp, e] at hv
    simp [hon, hs]

theorem internLsNode_view (s : AState) (hw : LsWF s.store.lss) (h : LsIdx) (v : LsNodeView)
    (hv : s.store.lss.view h = some v) : internLsNode v s = .ok (h, s) := by
  unfold internLsNode
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, Except.bind,
    Except.pure]
  rw [lsfind_of_view _ hw h v hv]; rfl

theorem internLevelList_denote (s : AState) (rk : LIdx → Nat) (hw : LWFAt s.store.ls rk) (rkn : NIdx → Nat)
    (hwn : NWFAt s.store.ns rkn) :
    ∀ (hs : List LIdx) (us : List ConLeche.Level), denoteLList s.store.ls hs = some us →
      internLevelList us s = .ok (hs, s) := by
  intro hs
  induction hs with
  | nil => intro us h; simp [denoteLList] at h; subst h; rfl
  | cons x xs ih =>
    intro us h
    simp only [denoteLList, opt2] at h
    split at h
    · rename_i a b ha hb
      simp at h; subst h
      simp only [internLevelList, bind, StateT.bind, Except.bind]
      rw [internLevel_denote s rk hw rkn hwn a _ x ha]
      simp only
      rw [ih b hb]; rfl
    · simp at h

theorem internLevels_denote (s : AState) (hwf : StoreWF s.store) (r : LsIdx) (us : List ConLeche.Level)
    (hd : denoteLs s.store.lss r = some us) : internLevels us s = .ok (r, s) := by
  obtain ⟨rkE, hE⟩ := hwf
  obtain ⟨⟨rkL, hL⟩, ⟨rkN, hN⟩⟩ := wf_parts ⟨rkE, hE⟩
  unfold denoteLs at hd
  split at hd
  · simp at hd
  rename_i hs hv
  simp only [internLevels, bind, StateT.bind, Except.bind]
  rw [internLevelList_denote s rkL hL rkN hN hs us hd]
  exact internLsNode_view s hE.lss r hs hv

theorem substLevelList_eq (ks : List ConLeche.Name) (us : List ConLeche.Level) :
    ∀ ls, substLevelList ks us ls = ls.map (ConLeche.Level.subst ks us)
  | [] => rfl
  | l :: ls => by simp [substLevelList, substLevelList_eq ks us ls]

/-- A row of the level-list substitution memo is the re-intern of its substituted readback. -/
def MemoLsOK (s : AState) (ks : List ConLeche.Name) (vs : List ConLeche.Level) : Prop :=
  ∀ v r, s.memos.instLPLsC[v]? = some r → ∃ ls, denoteLs s.store.lss v = some ls ∧
    denoteLs s.store.lss r = some (ls.map (ConLeche.Level.subst ks vs))

theorem readLevelsM_eq (u : LsIdx) (s : AState) (l : List ConLeche.Level)
    (hrl : ReadLsCacheOK s.caches.readLsC s.store) (hd : denoteLs s.store.lss u = some l) :
    ∃ c1 : Caches, readLevelsM u s = .ok (l, withC s c1) ∧ c1 = { s.caches with readLsC := c1.readLsC } ∧
      ReadLsCacheOK c1.readLsC s.store := by
  unfold readLevelsM
  rcases hc : s.caches.readLsC[u]? with _ | l'
  · refine ⟨{ s.caches with readLsC := s.caches.readLsC.insert u l }, ?_, rfl, ?_⟩
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

theorem readLs_ext {tbl : Std.HashMap LsIdx (List ConLeche.Level)} {st st' : EStore}
    (h : ReadLsCacheOK tbl st) (hx : Ext st st') : ReadLsCacheOK tbl st' := fun k u hk => denoteLs_ext (h k u hk) hx

theorem substLsMemoAt_run (ks : List ConLeche.Name) (vs : List ConLeche.Level) (s : AState) (u : LsIdx)
    (l : List ConLeche.Level) (hu : denoteLs s.store.lss u = some l) (hrl : ReadLsCacheOK s.caches.readLsC s.store)
    (hm : MemoLsOK s ks vs) (hwf : StoreWF s.store) (h : LsIdx) (s'' : AState)
    (hint : internLevels (l.map (ConLeche.Level.subst ks vs)) s = .ok (h, s'')) :
    ∃ s3, substLsMemoAt ks vs u s = .ok (h, s3) ∧ s3.store = s''.store ∧ s3.pins = s.pins ∧
      s3.memos = { s.memos with instLPLsC := s3.memos.instLPLsC } ∧
      s3.caches = { s.caches with readLsC := s3.caches.readLsC } ∧
      ReadLsCacheOK s3.caches.readLsC s3.store ∧ MemoLsOK s3 ks vs := by
  obtain ⟨q1, q2, -, -, -, q6, q7, q8, q9⟩ :=
    AM.of_run (P := fun t => t = s) rfl hint (internLevels_spec s _ hwf)
  unfold substLsMemoAt
  rcases hc : s.memos.instLPLsC[u]? with _ | r
  · obtain ⟨c1, e1, ec1, ok1⟩ := readLevelsM_eq u s l hrl hu
    have hint1 := internLevels_frameC c1 (l.map (ConLeche.Level.subst ks vs)) s
    rw [hint] at hint1
    simp only [withC, Except.map] at hint1 e1
    refine ⟨{ withC s'' c1 with memos := { s''.memos with instLPLsC := s''.memos.instLPLsC.insert u h } }, ?_, rfl,
      by simp [withC, q8], by simp [q6], by simp [withC]; exact ec1, ?_, ?_⟩
    · simp [instLPLsGet, instLPLsSet, hc, e1, substLevelList_eq, hint1, get, getThe, MonadStateOf.get, StateT.get,
        set, StateT.set, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure, withC]
    · exact readLs_ext ok1 q2
    · intro k r' hk
      simp only [withC, Std.HashMap.getElem?_insert] at hk
      split at hk
      · rename_i e; simp at e; subst e; simp at hk; subst hk
        exact ⟨l, denoteLs_ext hu q2, q9⟩
      · rw [q6] at hk
        obtain ⟨l', h1, h2⟩ := hm k r' hk
        exact ⟨l', denoteLs_ext h1 q2, denoteLs_ext h2 q2⟩
  · obtain ⟨l', h1, h2⟩ := hm u r hc
    rw [hu] at h1; cases h1
    have hre := internLevels_denote s hwf r _ h2
    rw [hint] at hre
    simp only [Except.ok.injEq, Prod.mk.injEq] at hre
    obtain ⟨e1, e2⟩ := hre
    subst e1; subst e2
    refine ⟨_, ?_, rfl, rfl, rfl, rfl, hrl, hm⟩
    simp [instLPLsGet, hc, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure,
      Except.bind, Except.pure]

end ConPanqueque.T
