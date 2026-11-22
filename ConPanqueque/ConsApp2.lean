import ConPanqueque.ConsIntern
import ConRon.Arena.Monad
open ConRon.Arena ConPanqueque.ConsIntern

/-!
# The two-tier `app` intern, twin side

`EStore.intern` at an `app` view touches only the two tiers' `apps` tables:
the persistent probe (skipped when the scratch tier is on and a child is a
scratch handle), then, with the scratch tier on, `tierApp` on the scratch
table at tier 1, else `tierApp` on the persistent table at tier 0 (whose own
probe repeats the missed one).
-/

namespace ConPanqueque.ConsApp2

abbrev ATbl := Tbl AppNode EIdx UInt64

/-- The `app` arm of `EStore.intern` over the two `apps` tables. -/
def appIntern (P Sc : ATbl) (on sk : Bool) (x : AppNode) (d : UInt64) : ATbl × ATbl × EIdx :=
  match (if on && sk then none else P.find? x) with
  | some h => (P, Sc, h)
  | none =>
    if on then ((P, (tierApp Sc x d 1).1, (tierApp Sc x d 1).2))
    else ((tierApp P x d 0).1, Sc, (tierApp P x d 0).2)

theorem intern_app (st : EStore) (f a : EIdx) :
    st.intern (.app f a) =
      let r := appIntern st.pers.apps st.scr.apps st.scratchOn (EStore.eViewHasScratchChild (.app f a)) ⟨f, a⟩
        (st.derOfView (.app f a))
      ({ st with pers := { st.pers with apps := r.1 }, scr := { st.scr with apps := r.2.1 } }, r.2.2) := by
  obtain ⟨lss, pers, scr, on⟩ := st
  simp only [EStore.intern, EStore.persFindMaybe, appIntern, ETables.find?, ETables.push, tierApp,
    Idx.tierS, Idx.tierP]
  cases on <;> simp only [Bool.false_and, Bool.true_and, ite_false, ite_true, Bool.false_eq_true]
  · cases h : pers.apps.find? ⟨f, a⟩ <;> simp
  · cases EStore.eViewHasScratchChild (.app f a) <;> simp only [ite_true, ite_false, Bool.false_eq_true]
    · cases h : pers.apps.find? ⟨f, a⟩ <;> simp only
      cases h2 : scr.apps.find? ⟨f, a⟩ <;> simp
    · cases h2 : scr.apps.find? ⟨f, a⟩ <;> simp

/-- On a probe hit, `intern` returns the stored handle and leaves the store alone. -/
theorem intern_app_of_find (st : EStore) (f a h : EIdx) (hf : st.find? (.app f a) = some h) :
    st.intern (.app f a) = (st, h) := by
  obtain ⟨lss, pers, scr, on⟩ := st
  simp only [EStore.find?, EStore.persFindMaybe, ETables.find?] at hf
  simp only [EStore.intern, EStore.persFindMaybe, ETables.find?]
  revert hf
  split <;> simp_all

/-- The monadic `app` intern (probe, capacity test, intern) when the active tier's `apps`
table is below the wide capacity: the store moves as `intern` says. -/
theorem internAppE_ok (s : AState) (f a : EIdx)
    (hcap : (if s.store.scratchOn then s.store.scr.apps.size else s.store.pers.apps.size) < Idx.wideCap) :
    internAppE f a s = .ok ((s.store.intern (.app f a)).2, { s with store := (s.store.intern (.app f a)).1 }) := by
  simp only [internAppE, internE, internNodeE]
  cases hf : s.store.find? (.app f a) with
  | some h =>
    rw [intern_app_of_find _ _ _ _ hf]
    simp [hf, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure, Except.bind]
  | none =>
    have hc : (if s.store.scratchOn then s.store.scr.sizeOf (.app f a) else s.store.pers.sizeOf (.app f a)) <
        ENodeView.cap (.app f a) := by
      simpa [ETables.sizeOf, ENodeView.cap] using hcap
    simp [hf, hc, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, Except.pure, set,
      StateT.set, MonadStateOf.set, Except.bind]

end ConPanqueque.ConsApp2
