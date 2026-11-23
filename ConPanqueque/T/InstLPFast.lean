import ConPanqueque.T.InstLP
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `instLPFast`: the top-level entry of `instantiateLevelParams`

The `hasLP` cutoff, then the walk between two clears of its memo. The twin reads the names and levels
back first (through its readback caches) and clears all three per-call memos; the port mirrors only the
expression memo, and the other two are cleared on the twin side alone.
-/

namespace ConPanqueque.T.ILP
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM
open ConPanqueque.T.LEq ConPanqueque.T.LSub ConPanqueque.T.ExG ConPanqueque.T.LLeq ConPanqueque.T.ExA

theorem readNameM_eq (u : NIdx) (s : AState) (x : ConLeche.Name) (hrl : ReadNCacheOK s.caches.readNC s.store)
    (hd : denoteN s.store.ns u = some x) :
    ∃ c1 : Caches, readNameM u s = .ok (x, withC s c1) ∧ c1 = { s.caches with readNC := c1.readNC } ∧
      ReadNCacheOK c1.readNC s.store := by
  unfold readNameM
  rcases hc : s.caches.readNC[u]? with _ | x'
  · refine ⟨{ s.caches with readNC := s.caches.readNC.insert u x }, ?_, rfl, ?_⟩
    · simp [hc, hd, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, bind, StateT.bind, pure,
        StateT.pure, Except.bind, Except.pure, withC]
    · intro k v hk
      simp only [Std.HashMap.getElem?_insert] at hk
      split at hk
      · rename_i e; simp at e; subst e; simp at hk; subst hk; exact hd
      · exact hrl k v hk
  · have := hrl u x' hc
    rw [hd] at this; cases this
    refine ⟨s.caches, ?_, rfl, hrl⟩
    simp [hc, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure, Except.bind,
      Except.pure, withC]

theorem readNamesM_eq : ∀ (us : List NIdx) (s : AState) (xs : List ConLeche.Name),
    ReadNCacheOK s.caches.readNC s.store → Frontend.denoteNList s.store.ns us = some xs →
    ∃ c1 : Caches, readNamesM us s = .ok (xs, withC s c1) ∧ c1 = { s.caches with readNC := c1.readNC } ∧
      ReadNCacheOK c1.readNC s.store
  | [], s, xs, hrl, hd => by
    simp [Frontend.denoteNList] at hd; subst hd
    exact ⟨s.caches, rfl, rfl, hrl⟩
  | u :: us, s, xs, hrl, hd => by
    simp only [Frontend.denoteNList] at hd
    split at hd
    · rename_i a b ha hb
      simp at hd; subst hd
      obtain ⟨c1, e1, ec1, ok1⟩ := readNameM_eq u s a hrl ha
      obtain ⟨c2, e2, ec2, ok2⟩ := readNamesM_eq us (withC s c1) b ok1 hb
      refine ⟨c2, ?_, ?_, ok2⟩
      · simp only [readNamesM, bind, StateT.bind, Except.bind]
        rw [e1]; simp only; rw [e2]; rfl
      · rw [ec2]; simp only [withC]; rw [ec1]
    · simp at hd

end ConPanqueque.T.ILP
