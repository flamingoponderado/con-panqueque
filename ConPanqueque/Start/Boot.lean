import ConPanqueque.Code.Layout

/-! # The twin's bootstrap

The program's invariant `SR` needs the pinned zero level to denote (`PinDen`), so it cannot hold
of the empty store.  The program therefore starts from a memory image that already holds two
rows: the anonymous name and the level zero (each the only row of its table).  On the twin side
that is the state after `boot` (the two interns) from the empty store, with a placeholder pin
table `P0` whose handles are all word 0 (the handles both interns return).

`boot_run` computes that state; `boot_ok` gives `StateOK` and the two denotations, so that
con-ron's `internReservedPins_run` applies from it. -/

open ConRon.Arena ConRon.Bridge ConPanqueque.V

namespace ConPanqueque.Start

def boot : AM (NIdx × LIdx) := do
  let a ← internNNode .anonymous
  let z ← internLNode .zero
  pure (a, z)

/-- The store after the bootstrap. -/
def bootStore : EStore := ((EStore.empty.internName .anonymous).1.internLevel .zero).1

/-- The placeholder pin table: `pinCount` copies of the word-0 name handle, level zero at word 0. -/
def P0 : Pins := { Pins.empty with names := Array.replicate pinCount default }

def sInit (P : Pins) : AState := { AState.init EStore.empty with pins := P }

def sBoot (P : Pins) : AState := { AState.init bootStore with pins := P }

theorem boot_run (P : Pins) : boot (sInit P) = .ok ((default, default), sBoot P) := by
  simp [boot, sInit, sBoot, bootStore, internNNode, internLNode, bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, set, MonadStateOf.set, pure, Except.pure, AState.init, NStore.find?,
    LStore.find?, Except.bind, NTables.find?, LTables.find?, Tbl.find?, EStore.empty, NStore.empty,
    NTables.empty, LTables.empty, LStore.empty, LsStore.empty, Tbl.empty, NTables.sizeOf, LTables.sizeOf,
    Tbl.size, Idx.idxCap, StateT.pure, StateT.set, EStore.ns, EStore.ls, EStore.internName,
    LsStore.internName, LStore.internName, EStore.internLevel, LsStore.internLevel, nstore_anon,
    lstore_zero, twoTier, tierInt, Tbl.push]
  exact ⟨rfl, rfl⟩

theorem boot_ok (P : Pins) :
    StateOK (sBoot P) ∧ (sBoot P).store.scratchOn = false ∧
      denoteN (sBoot P).store.ns default = some .anonymous ∧
      denoteL (sBoot P).store.ls default = some .zero ∧
      (sBoot P).memos = Memos.empty ∧ (sBoot P).caches = Caches.empty ∧ (sBoot P).pins = P := by
  have hr := boot_run P
  simp only [boot] at hr
  obtain ⟨a, s1, g1, r1⟩ := AM.bind_ok hr
  obtain ⟨st1, hd1⟩ := Frontend.internNNode_sstep (s := sInit P) ⟨EStore.empty_wf⟩
    (by intro c hc; simp [NNodeView.children] at hc) g1
  obtain ⟨z, s2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨st2, hd2⟩ := Frontend.internLNode_sstep st1.ok
    ⟨by intro c hc; simp [LNodeView.lchildren] at hc, by intro c hc; simp [LNodeView.nchildren] at hc⟩ g2
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at r2
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := r2
  have hacc := st1.trans st2
  refine ⟨st2.ok, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hacc.scratch]; rfl
  · rw [← denoteN_ext (by rw [hd1]; rfl) st2.ext]
  · rw [hd2]; rfl
  · rw [hacc.memos]; rfl
  · rw [hacc.caches]; rfl
  · rw [hacc.pins]; rfl

end ConPanqueque.Start
