import ConPanqueque.T.LvlEquiv
import ConRon.Bridge.StateOK
import ConRon.Arena.Core
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `lvlEq?` at two level handles

The twin caches the verdict (`caches.lvlEqC`) and the readbacks (`caches.readLC`); the port caches
neither. Under con-ron's cache invariants (`ReadLCacheOK`, `LvlEqCacheOK`, carried by its `CheckOK`) a
hit answers what a recomputation answers, so `eqvBody` on the two handle words refines `lvlEq?`.
-/

namespace ConPanqueque.T.LLeq
open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExM ConPanqueque.T.LEq
open ConPanqueque.T.NEq ConPanqueque.T.LComb ConPanqueque.T.LSimp ConPanqueque.T.LSub
open ConLeche (Level)

theorem readLevelM_run (h : LIdx) (s : AState) (l : Level) (hrl : ReadLCacheOK s.caches.readLC s.store)
    (hd : denoteL s.store.ls h = some l) :
    ∃ s1, readLevelM h s = .ok (l, s1) ∧ s1.store = s.store ∧ s1.memos = s.memos ∧
      ReadLCacheOK s1.caches.readLC s1.store ∧ s1.caches.lvlEqC = s.caches.lvlEqC ∧
      MirrorEq s1.caches s.caches := by
  unfold readLevelM
  rcases hc : s.caches.readLC[h]? with _ | l'
  · refine ⟨{ s with caches := { s.caches with readLC := s.caches.readLC.insert h l } }, ?_, rfl, rfl, ?_, rfl, mirrorEq_refl _⟩
    · simp [hc, hd, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure]
    · intro k u hk
      simp only [Std.HashMap.getElem?_insert] at hk
      split at hk
      · rename_i e; simp at e; subst e; simp at hk; subst hk; exact hd
      · exact hrl k u hk
  · have := hrl h l' hc
    rw [hd] at this; cases this
    exact ⟨s, by simp [hc, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure], rfl, rfl, hrl, rfl, mirrorEq_refl _⟩

theorem lvlEqQ_run (u v : LIdx) (s : AState) (lu lv : Level) (hu : denoteL s.store.ls u = some lu)
    (hv : denoteL s.store.ls v = some lv)
    (hrl : ReadLCacheOK s.caches.readLC s.store) (hle : LvlEqCacheOK s.caches.lvlEqC s.store) :
    ∃ s', lvlEq? u v s = .ok (Level.isEquiv lu lv, s') ∧ s'.store = s.store ∧ s'.memos = s.memos ∧
      MirrorEq s'.caches s.caches := by
  unfold lvlEq?
  rcases hc : s.caches.lvlEqC[(u, v)]? with _ | r
  · obtain ⟨s1, h1, e1, m1, ok1, _, c1⟩ := readLevelM_run u s lu hrl hu
    obtain ⟨s2, h2, e2, m2, _, _, c2⟩ := readLevelM_run v s1 lv ok1 (by rw [e1]; exact hv)
    rcases hq : Level.isEquiv lu lv with _ | r
    · refine ⟨s2, ?_, by rw [e2, e1], by rw [m2, m1], mirrorEq_trans c2 c1⟩
      simp [hc, h1, h2, hq, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure,
        Except.bind, Except.pure]
    · refine ⟨{ s2 with caches := { s2.caches with lvlEqC := s2.caches.lvlEqC.insert (u, v) r } }, ?_,
        e2.trans e1, m2.trans m1, mirrorEq_trans c2 c1⟩
      simp [hc, h1, h2, hq, get, getThe, MonadStateOf.get, StateT.get, set, StateT.set, bind, StateT.bind, pure,
        StateT.pure, Except.bind, Except.pure]
  · obtain ⟨u', v', hu', hv', hq⟩ := hle (u, v) r hc
    rw [hu] at hu'; cases hu'
    rw [hv] at hv'; cases hv'
    refine ⟨s, ?_, rfl, rfl, mirrorEq_refl _⟩
    simp [hc, hq, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure, Except.bind,
      Except.pure]

section
variable {σ : Type}

theorem sr_congrS {C : Ctx} {s s' : AState} {t : PState σ} (h : SR C s t) (h1 : s'.store = s.store)
    (h2 : s'.memos = s.memos) (h3 : MirrorEq s'.caches s.caches) : SR C s' t := by
  obtain ⟨s1, m1, c1, p1⟩ := s'
  obtain ⟨s0, m0, c0, p0⟩ := s
  simp only at h1 h2 h3; subst h1 h2
  exact ⟨h.rep, h.gdir, h.gfln, h.gfll, h.gfls, h.gfle, h.gkb, h.code, h.kbuf, h.memo, h.memoN,
    fun k => cacheAt_mirror (h.cache k) h3,
    modeAt_mirror h.mode h3, h.heap⟩

theorem specR_ofRun {α : Type} {P : PState σ → Prop} {c : ProgHOL 64} {s s' : AState} {m : AM α} {a : α}
    {R R' : α → BitVec 64 → AState → PState σ → Prop} (hrun : m s = .ok (a, s'))
    (h : SpecR P c s (pure a) R') (hR : ∀ w st, R' a w s st → R a w s' st) : SpecR P c s m R := by
  intro t ht
  rcases h t ht with hs | ⟨w, hr, a', s1, hm, hq⟩
  · exact Or.inl hs
  · simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hm
    obtain ⟨rfl, rfl⟩ := hm
    exact Or.inr ⟨w, hr, a, s', hrun, hR w _ hq⟩

theorem lvlEqQ_spec (C : Ctx) (hok : CtxOK C)
    (hcS : C.code.lookup fSubst = some (substParams.map (fun p => (p, ShapeHOL.one)), substBody C, .one))
    (hcN : C.code.lookup fNeq = some ([(pNa, .one), (pNb, .one)], neqBody, .one))
    (hcM : C.code.lookup fSimp = some ([(pLa, .one)], simpBody C, .one))
    (hcC : C.code.lookup fComb = some ([(pLa, .one), (pLb, .one)], combBody C, .one))
    (hcB : C.code.lookup fByC = some (bcParams.map (fun p => (p, ShapeHOL.one)), bcBody C, .one))
    (hcI : C.code.lookup fITag = some ([(pLa, .one)], itagBody, .one))
    (hcR : C.code.lookup fImax = some (leqParams.map (fun p => (p, ShapeHOL.one)), imBody C, .one))
    (hcE : C.code.lookup fLvlEq = some ([(pLa, .one), (pLb, .one)], lvlEqBody, .one))
    (hcT : C.code.lookup fRest = some (leqParams.map (fun p => (p, ShapeHOL.one)), restBody, .one))
    (hcL : C.code.lookup fLeq = some (leqParams.map (fun p => (p, ShapeHOL.one)), leqBody, .one))
    (H : List (BitVec 64)) (u v : LIdx) (s : AState) (lu lv : Level)
    (hu : denoteL s.store.ls u = some lu) (hv : denoteL s.store.ls v = some lv)
    (hrl : ReadLCacheOK s.caches.readLC s.store) (hle : LvlEqCacheOK s.caches.lvlEqC s.store) :
    SpecR (Pre (σ := σ) (ctxH C H) s [(pLa, Enc.idxW u), (pLb, Enc.idxW v)]) eqvBody s (lvlEq? u v)
      (fun o w s' st => s'.store = s.store ∧ s'.memos = s.memos ∧ PostOB (ctxH C H) o w s' st) := by
  obtain ⟨s', hrun, e1, e2, e3⟩ := lvlEqQ_run u v s lu lv hu hv hrl hle
  exact specR_ofRun hrun (eqv_spec C hok hcS hcN hcM hcC hcB hcI hcR hcE hcT hcL H lu lv _ _ s
      (lrep_arena _ _ _ u _ lu hu) (lrep_arena _ _ _ v _ lv hv))
    (fun w st ⟨hw, hsr⟩ => ⟨e1, e2, hw, sr_congrS hsr e1 e2 e3⟩)

end

end ConPanqueque.T.LLeq
