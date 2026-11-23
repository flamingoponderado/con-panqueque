import ConPanqueque.T.Env
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Reading the pin table

The pins are the context's (`SR.pins`) and sit in the environment heap at `PO` (`PinsE`), so each
reader is one load at a constant address.
-/

namespace ConPanqueque.T

section
variable {σ : Type}

/-- A spec may first look at an entry state. -/
theorem specR_atEntry {α : Type} {P : PState σ → Prop} {c : ProgHOL 64} {s : AState} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (h : ∀ t, P t → SpecR P c s m R) : SpecR P c s m R :=
  fun t ht => h t ht t ht

theorem pinsReady_of {C : Ctx} (hok : CtxOK C) {s : AState} (hp : s.pins = C.pins) : pinsReady s = true := by
  simp [pinsReady, hp, hok.pinsRel.1]

/-- `x := load (pin cell i); rest` against `pinAt i >>= k`. -/
theorem specR_pinAtI {β : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {k : NIdx → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (i : Nat) (hi : i < pinCount) (x : MlS) (hx : x ∈ D) :
    let hi' : i < C.pins.names.size := by rw [hok.pinsRel.1]; exact hi
    SpecR (Inv C s ((x, Enc.idxW C.pins.names[i]) :: Γ) M D) rest s (k C.pins.names[i]) R →
    SpecR (Inv C s Γ M D) (.seq (.assign .local x (.load .one (.const (ecell C (C.PO + i))))) rest) s
      (pinAt i >>= k) R := by
  intro hi' hk
  refine specR_atEntry fun t ht => ?_
  have hp := ht.sr.pins
  have hrun : pinAt i s = .ok (C.pins.names[i], s) := by
    simp [pinAt, hp, hi', get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure,
      Except.bind, Except.pure]
  exact specR_runBind hrun (specR_envLoadI x _ (C.PO + i) _ hx rfl (hok.pinsRel.2.1 i hi') hk)

theorem pinEmptyLevels_run {C : Ctx} (hok : CtxOK C) {s : AState} (hp : s.pins = C.pins) :
    pinEmptyLevels s = .ok (C.pins.emptyLevels, s) := by
  simp [pinEmptyLevels, pinsReady_of hok hp, hp, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind,
    pure, StateT.pure, Except.bind, Except.pure]

theorem pinZeroLevel_run {C : Ctx} (hok : CtxOK C) {s : AState} (hp : s.pins = C.pins) :
    pinZeroLevel s = .ok (C.pins.zeroLevel, s) := by
  simp [pinZeroLevel, pinsReady_of hok hp, hp, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind,
    pure, StateT.pure, Except.bind, Except.pure]

theorem pinSortOne_run {C : Ctx} (hok : CtxOK C) {s : AState} (hp : s.pins = C.pins) :
    pinSortOne s = .ok (C.pins.sortOne, s) := by
  simp [pinSortOne, pinsReady_of hok hp, hp, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind,
    pure, StateT.pure, Except.bind, Except.pure]

/-- `x := load (cell PO + pinCount + j)`: the three extra pins (`emptyLevels`, `zeroLevel`, `sortOne`). -/
theorem specR_pinXI {β γ : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {k : γ → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (op : AM γ) (j : Nat) (v : γ) (w : BitVec 64)
    (hrun : ∀ s : AState, s.pins = C.pins → op s = .ok (v, s))
    (hw : C.EH[C.PO + pinCount + j]? = some w) (x : MlS) (hx : x ∈ D)
    (hk : SpecR (Inv C s ((x, w) :: Γ) M D) rest s (k v) R) :
    SpecR (Inv C s Γ M D) (.seq (.assign .local x (.load .one (.const (ecell C (C.PO + pinCount + j))))) rest) s
      (op >>= k) R := by
  refine specR_atEntry fun t ht => ?_
  exact specR_runBind (hrun s ht.sr.pins) (specR_envLoadI x _ _ _ hx rfl hw hk)

theorem pin_emptyLevels_cell {C : Ctx} (hok : CtxOK C) :
    C.EH[C.PO + pinCount + 0]? = some (Enc.idxW C.pins.emptyLevels) := hok.pinsRel.2.2.1
theorem pin_zeroLevel_cell {C : Ctx} (hok : CtxOK C) :
    C.EH[C.PO + pinCount + 1]? = some (Enc.idxW C.pins.zeroLevel) := hok.pinsRel.2.2.2.1
theorem pin_sortOne_cell {C : Ctx} (hok : CtxOK C) :
    C.EH[C.PO + pinCount + 2]? = some (Enc.idxW C.pins.sortOne) := hok.pinsRel.2.2.2.2.1

end

end ConPanqueque.T
