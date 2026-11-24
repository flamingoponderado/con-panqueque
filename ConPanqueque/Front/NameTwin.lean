import ConPanqueque.Front.Expr
import ConPanqueque.V.NIntern
import ConRon.Bridge.StoreNested

/-! # Interning a name node: the twin's side

The kernel never interns names (the frontend does), so the facts the other intern wrappers rely on
are proved here for `internNNode`: its run is the store's `intern` (`internNNode_ok`), and it keeps
the store well formed and extends it (`internNNode_wf`, from con-ron's `EStore.internName_spec`). -/

open ConRon.Arena

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.V

theorem NStore.intern_of_find' {st : NStore} {v : NNodeView} {h : NIdx}
    (hf : st.find? v = some h) : st.intern v = (st, h) := by
  simp only [NStore.find?] at hf
  simp only [NStore.intern]
  split at hf
  · simp only [Option.some.injEq] at hf; rw [hf]
  · split at hf
    · rename_i hon
      rw [if_pos hon]
      cases hs : st.scr.find? v with
      | some i => simp only [hs, Option.some.injEq] at hf; rw [hf]
      | none => simp only [hs] at hf; simp at hf
    · simp at hf

def NCap (ns : NStore) (v : NNodeView) : Prop :=
  ns.find? v = none → (if ns.scratchOn then ns.scr.sizeOf v else ns.pers.sizeOf v) < Idx.idxCap

theorem internNNode_ok (s : AState) (v : NNodeView) (hcap : NCap s.store.ns v) :
    internNNode v s = .ok ((s.store.ns.intern v).2, { s with store := withN s.store (s.store.ns.intern v).1 }) := by
  unfold internNNode
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, Except.bind,
    Except.pure]
  cases hf : s.store.ns.find? v with
  | some h =>
    simp only [hf]
    rw [NStore.intern_of_find' hf]; rfl
  | none =>
    simp only [hf, if_pos (hcap hf)]
    rfl

theorem internNNode_wf {v : NNodeView} {s s' : AState} {h : NIdx} (hwf : StoreWF s.store)
    (hv : s.store.ns.ViewOK v) (hr : internNNode v s = .ok (h, s')) : StoreWF s'.store ∧ Ext s.store s'.store := by
  unfold internNNode at hr
  cases hf : s.store.ns.find? v with
  | some i =>
    simp [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
      Except.pure, Except.bind, hf, StateT.pure] at hr
    rw [← hr.2]; exact ⟨hwf, Ext.refl _⟩
  | none =>
    by_cases hc : (if s.store.ns.scratchOn = true then s.store.ns.scr.sizeOf v
                else s.store.ns.pers.sizeOf v) < Idx.idxCap
    · simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
        Except.pure, Except.bind, hf, StateT.pure, set, StateT.set, ite_eq_left hc,
        Except.ok.injEq, Prod.mk.injEq] at hr
      rw [← hr.2]
      exact ⟨(ConRon.Bridge.EStore.internName_spec hwf hv hc).1, (ConRon.Bridge.EStore.internName_spec hwf hv hc).2.1⟩
    · simp [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
        Except.pure, Except.bind, hf, hc, fail, throwThe, MonadExceptOf.throw,
        StateT.lift] at hr

end ConPanqueque.Front
