import ConPanqueque.T.Inv
import ConRon.Arena.WFProofs
import ConRon.Bridge.ExprOps.MemoSpecs
import ConRon.Bridge.StoreNested
open ConRon.Arena

/-!
# The twin store stays well formed across a node intern

`internNodeE` probes, then tests the active tier's size against the constructor's cap — exactly con-ron's
`capOK` — before `EStore.intern`; with the children decoding (`ViewOK`, which the port's checked derived reads
establish), con-ron's `EStore.intern_wf` applies.
-/

namespace ConPanqueque.T

theorem internNodeE_wf {v : ENodeView} {s s' : AState} {h : EIdx} (hwf : StoreWF s.store)
    (hv : s.store.ViewOK v) (hr : internNodeE v s = .ok (h, s')) : StoreWF s'.store := by
  have e : internNodeE v s = (match s.store.find? v with
    | some h => (pure h : AM EIdx)
    | none => do
      let n := if s.store.scratchOn then s.store.scr.sizeOf v else s.store.pers.sizeOf v
      if n < v.cap then do
        let st := s.store
        let s := { s with store := EStore.empty }
        let (st, h) := st.intern v
        set { s with store := st }
        pure h
      else
        fail (.native "arena: expression constructor array full")) s := rfl
  rw [e] at hr
  cases hf : s.store.find? v with
  | some h' =>
    simp only [hf] at hr
    have e2 : (pure h' : AM EIdx) s = .ok (h', s) := rfl
    rw [e2] at hr
    simp only [Except.ok.injEq, Prod.mk.injEq] at hr
    obtain ⟨_, rfl⟩ := hr; exact hwf
  | none =>
    simp only [hf] at hr
    by_cases hn : (if s.store.scratchOn then s.store.scr.sizeOf v else s.store.pers.sizeOf v) < v.cap
    · have e3 : (do
          let n := if s.store.scratchOn then s.store.scr.sizeOf v else s.store.pers.sizeOf v
          if n < v.cap then do
            let st := s.store
            let s := { s with store := EStore.empty }
            let (st, h) := st.intern v
            set { s with store := st }
            pure h
          else
            fail (.native "arena: expression constructor array full") : AM EIdx) s =
          .ok ((s.store.intern v).2, { s with store := (s.store.intern v).1 }) := by
        simp only [hn, ite_true]; rfl
      rw [e3] at hr
      simp only [Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨_, rfl⟩ := hr
      exact EStore.intern_wf hwf hv hn
    · have e3 : (do
          let n := if s.store.scratchOn then s.store.scr.sizeOf v else s.store.pers.sizeOf v
          if n < v.cap then do
            let st := s.store
            let s := { s with store := EStore.empty }
            let (st, h) := st.intern v
            set { s with store := st }
            pure h
          else
            fail (.native "arena: expression constructor array full") : AM EIdx) s =
          (fail (.native "arena: expression constructor array full") : AM EIdx) s := by
        simp only [hn, ite_false]
      rw [e3] at hr
      cases hr

theorem viewOK_app {st : EStore} {f a : EIdx} (h : (st.view f).isSome = true ∧ (st.view a).isSome = true) :
    st.ViewOK (.app f a) := by
  constructor <;> intro c hc <;> simp [ENodeView.echildren, ENodeView.nchildren, ENodeView.lchildren,
    ENodeView.lschildren] at hc <;> rcases hc with rfl | rfl <;> simp [h.1, h.2]

theorem viewOK_letE {st : EStore} {ty v b : EIdx}
    (h : (st.view ty).isSome = true ∧ (st.view v).isSome = true ∧ (st.view b).isSome = true) :
    st.ViewOK (.letE ty v b) := by
  constructor <;> intro c hc <;> simp [ENodeView.echildren, ENodeView.nchildren, ENodeView.lchildren,
    ENodeView.lschildren] at hc <;> rcases hc with rfl | rfl | rfl <;> simp [h.1, h.2.1, h.2.2]

theorem viewOK_proj {st : EStore} {n : NIdx} {i : Nat} {e : EIdx}
    (h : (st.lss.ls.ns.view n).isSome = true ∧ (st.view e).isSome = true) :
    st.ViewOK (.proj n i e) := by
  constructor <;> intro c hc <;> simp [ENodeView.echildren, ENodeView.nchildren, ENodeView.lchildren,
    ENodeView.lschildren] at hc <;> subst hc
  · exact h.2
  · exact h.1

theorem viewOK_bvar {st : EStore} {i : Nat} : st.ViewOK (.bvar i) := by
  constructor <;> intro c hc <;> simp [ENodeView.echildren, ENodeView.nchildren, ENodeView.lchildren,
    ENodeView.lschildren] at hc

theorem viewOK_sort {st : EStore} {u : LIdx} (h : (st.lss.ls.view u).isSome = true) : st.ViewOK (.sort u) := by
  constructor <;> intro c hc <;> simp [ENodeView.echildren, ENodeView.nchildren, ENodeView.lchildren,
    ENodeView.lschildren] at hc <;> subst hc <;> exact h

theorem viewOK_const {st : EStore} {n : NIdx} {us : LsIdx}
    (h : (st.lss.ls.ns.view n).isSome = true ∧ (st.lss.view us).isSome = true) : st.ViewOK (.const n us) := by
  constructor <;> intro c hc <;> simp [ENodeView.echildren, ENodeView.nchildren, ENodeView.lchildren,
    ENodeView.lschildren] at hc <;> subst hc
  · exact h.1
  · exact h.2

theorem viewOK_fvar {st : EStore} {i : Nat} {ty : EIdx} (h : (st.view ty).isSome = true) :
    st.ViewOK (.fvar i ty) := by
  constructor <;> intro c hc <;> simp [ENodeView.echildren, ENodeView.nchildren, ENodeView.lchildren,
    ENodeView.lschildren] at hc <;> subst hc <;> exact h

theorem viewOK_lit {st : EStore} {l : ConLeche.Literal} : st.ViewOK (.lit l) := by
  constructor <;> intro c hc <;> simp [ENodeView.echildren, ENodeView.nchildren, ENodeView.lchildren,
    ENodeView.lschildren] at hc

theorem internLamE_wf {ty b h : EIdx} {s s' : AState} (hwf : StoreWF s.store) (hty : (s.store.view ty).isSome = true)
    (hb : (s.store.view b).isSome = true) (hr : internLamE ty b s = .ok (h, s')) : StoreWF s'.store :=
  (ConRon.Bridge.AM.of_run (P := fun t => t = s) rfl hr (ConRon.Bridge.ExprOps.internLamE_specV s ty b hwf hty hb)).1

theorem internForallEE_wf {ty b h : EIdx} {s s' : AState} (hwf : StoreWF s.store)
    (hty : (s.store.view ty).isSome = true) (hb : (s.store.view b).isSome = true)
    (hr : internForallEE ty b s = .ok (h, s')) : StoreWF s'.store :=
  (ConRon.Bridge.AM.of_run (P := fun t => t = s) rfl hr (ConRon.Bridge.ExprOps.internForallEE_specV s ty b hwf hty hb)).1

theorem internLNode_wf {v : LNodeView} {s s' : AState} {h : LIdx} (hwf : StoreWF s.store)
    (hv : s.store.ls.ViewOK v) (hr : internLNode v s = .ok (h, s')) : StoreWF s'.store := by
  unfold internLNode at hr
  cases hf : s.store.ls.find? v with
  | some i =>
    simp [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
      Except.pure, Except.bind, hf, StateT.pure] at hr
    rw [← hr.2]; exact hwf
  | none =>
    by_cases hc : (if s.store.ls.scratchOn = true then s.store.ls.scr.sizeOf v
                else s.store.ls.pers.sizeOf v) < Idx.idxCap
    · simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
        Except.pure, Except.bind, hf, StateT.pure, set, StateT.set, ite_eq_left hc,
        Except.ok.injEq, Prod.mk.injEq] at hr
      rw [← hr.2]
      exact (ConRon.Bridge.EStore.internLevel_spec hwf hv hc).1
    · simp [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
        Except.pure, Except.bind, hf, hc, fail, throwThe, MonadExceptOf.throw,
        StateT.lift] at hr

theorem lviewOK_param {st : LStore} {n : NIdx} (h : (st.ns.view n).isSome = true) : st.ViewOK (.param n) := by
  constructor <;> intro c hc <;> simp [LNodeView.lchildren, LNodeView.nchildren] at hc <;> subst hc <;> exact h

theorem lviewOK_zero {st : LStore} : st.ViewOK .zero := by
  constructor <;> intro c hc <;> simp [LNodeView.lchildren, LNodeView.nchildren] at hc

theorem lviewOK_succ {st : LStore} {u : LIdx} (h : (st.view u).isSome = true) : st.ViewOK (.succ u) := by
  constructor <;> intro c hc <;> simp [LNodeView.lchildren, LNodeView.nchildren] at hc <;> subst hc <;> exact h

theorem lviewOK_max {st : LStore} {u v : LIdx} (h : (st.view u).isSome = true ∧ (st.view v).isSome = true) :
    st.ViewOK (.max u v) := by
  constructor <;> intro c hc <;> simp [LNodeView.lchildren, LNodeView.nchildren] at hc <;>
    rcases hc with rfl | rfl <;> simp [h.1, h.2]

theorem lviewOK_imax {st : LStore} {u v : LIdx} (h : (st.view u).isSome = true ∧ (st.view v).isSome = true) :
    st.ViewOK (.imax u v) := by
  constructor <;> intro c hc <;> simp [LNodeView.lchildren, LNodeView.nchildren] at hc <;>
    rcases hc with rfl | rfl <;> simp [h.1, h.2]

theorem internLsNode_wf {v : LsNodeView} {s s' : AState} {h : LsIdx} (hwf : StoreWF s.store)
    (hv : s.store.lss.ViewOK v) (hr : internLsNode v s = .ok (h, s')) : StoreWF s'.store := by
  unfold internLsNode at hr
  cases hf : s.store.lss.find? v with
  | some i =>
    simp [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
      Except.pure, Except.bind, hf, StateT.pure] at hr
    rw [← hr.2]; exact hwf
  | none =>
    by_cases hc : (if s.store.lss.scratchOn = true then s.store.lss.scr.sizeOf v
                else s.store.lss.pers.sizeOf v) < Idx.idxCap
    · simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
        Except.pure, Except.bind, hf, StateT.pure, set, StateT.set, ite_eq_left hc,
        Except.ok.injEq, Prod.mk.injEq] at hr
      rw [← hr.2]
      exact (ConRon.Bridge.EStore.internLevels_spec hwf hv hc).1
    · simp [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
        Except.pure, Except.bind, hf, hc, fail, throwThe, MonadExceptOf.throw,
        StateT.lift] at hr

end ConPanqueque.T
