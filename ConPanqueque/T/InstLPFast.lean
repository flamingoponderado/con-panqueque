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

section
variable {σ : Type}

/-- `specR_memoClearI` for a twin clear that may also touch tables the port does not mirror. -/
theorem specR_memoClearIG {β : Type} {C : Ctx} (hok : CtxOK C) (mk : MemoK) (clearOp : AM Unit)
    {s s' : AState} (hclear : clearOp s = .ok ((), s')) (hst : s'.store = s.store)
    (hoE : ∀ k, k ≠ mk → memoSel k s'.memos = memoSel k s.memos)
    (hoN : ∀ k, memoSelN k s'.memos = memoSelN k s.memos) (hsame : memoSel mk s'.memos = ∅)
    {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {k : Unit → AM β} {R : β → BitVec 64 → AState → PState σ → Prop} (hj : lJ0 ∈ D)
    (hk : SpecR (Inv C s' (Γ.kill [lJ0]) [] D) rest s' (k ()) R) :
    SpecR (Inv C s Γ M D) (clearCode (C.mg (.e mk)) rest) s (clearOp >>= k) R := by
  intro t ht
  obtain ⟨w0, hw0⟩ := ht.decl lJ0 hj
  rcases clearCode_core t _ _ _ (ht.sr.memo mk) rest w0 hw0 (fun j hj' => hok.mdescMemo (.e mk) (.e mk) j hj') with
    hs | ⟨t4, he, hmem, hout, hd4, hg4, hc4, hl4, hj4⟩
  · exact Or.inl hs
  have hsr' : SR C s' t4 :=
    sr_upd_region hok (.e mk) ht.sr hout hd4 hg4 hc4 hst
      (fun k' e => hoE k' (fun x => e (by rw [x])))
      (fun k' _ => hoN k')
      (fun k' e => by injection e with e; subst e; rw [hsame]; exact hmem)
      (fun k' e => by simp at e)
  rw [he]
  rcases hk t4 (inv_after_clear ht hsr' hl4 hj4) with hs | ⟨w, hr', a, s', hk', hR⟩
  · exact Or.inl hs
  refine Or.inr ⟨w, hr', a, s', ?_, hR⟩
  show (do let r ← clearOp s; match r with | (a, s) => k a s) = _
  rw [hclear]; exact hk'

end

end ConPanqueque.T.ILP
