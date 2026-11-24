import ConPanqueque.Front.Init
import ConRon.Bridge.Frontend.Rel
import ConRon.Bridge.StateOK

/-! # `StateD.init` after the pins: a probe

Once the reserved pins are interned (`PinsOK`), the zero name handle decodes to `.anonymous` and
`pins.zeroLevel` to `.zero`.  Both are persistent (scratch off), so the cons tables (`consP`) find
them, and `StateD.init` returns their singleton tables without changing the state. -/

open ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge ConRon.Bridge.Frontend

namespace ConPanqueque.Front

theorem view_of_denoteN_anon {ns : NStore} {i : NIdx} (h : denoteN ns i = some .anonymous) :
    ns.view i = some .anonymous := by
  unfold denoteN denoteNAux at h
  cases hv : ns.view i with
  | none => rw [hv] at h; simp at h
  | some v => rw [hv] at h; cases v <;> simp at h ⊢

theorem view_of_denoteL_zero {ls : LStore} {i : LIdx} (h : denoteL ls i = some .zero) :
    ls.view i = some .zero := by
  unfold denoteL denoteLAux at h
  cases hv : ls.view i with
  | none => rw [hv] at h; simp at h
  | some v =>
    rw [hv] at h
    cases v <;> simp at h ⊢

theorem init_names_find {s : AState} (hok : StateOK s) (hoff : s.store.scratchOn = false) (hp : PinsOK s) :
    s.store.ns.find? .anonymous = some default := by
  have hv := view_of_denoteN_anon hp.anon
  have hper := PersN_of_view hok.wf hoff hv
  obtain ⟨rk, hrk⟩ := nsWF_of_StateOK hok
  have := (hrk.consP .anonymous default).mpr ⟨hv, hper⟩
  simp only [NStore.find?, this]

theorem init_levels_find {s : AState} (hok : StateOK s) (hoff : s.store.scratchOn = false) (hp : PinsOK s) :
    s.store.ls.find? .zero = some s.pins.zeroLevel := by
  have hv := view_of_denoteL_zero hp.zeroLevel
  have hper := PersL_of_view hok.wf hoff hv
  obtain ⟨rk, hrk⟩ := hok.wf
  obtain ⟨rkl, hl⟩ := hrk.lss.ls
  have := (hl.consP .zero s.pins.zeroLevel).mpr ⟨hv, hper⟩
  unfold LStore.find?
  rw [show s.store.ls = s.store.lss.ls from rfl, this]

/-- The initial parse state after the pins. -/
def stInit (s : AState) : StateD where
  names := ConLeche.Frontend.IdTable.singleton default
  levels := ConLeche.Frontend.IdTable.singleton s.pins.zeroLevel

/-- **`StateD.init` is a probe** after the pins. -/
theorem stateD_init_probe {s : AState} (hok : StateOK s) (hoff : s.store.scratchOn = false) (hp : PinsOK s) :
    StateD.init s = .ok (stInit s, s) := by
  have h1 := init_names_find hok hoff hp
  have h2 := init_levels_find hok hoff hp
  simp [StateD.init, internNNode, internLNode, h1, h2, bind, StateT.bind, get, getThe, MonadStateOf.get,
    StateT.get, pure, StateT.pure, Except.pure, Except.bind]
  rfl

end ConPanqueque.Front
