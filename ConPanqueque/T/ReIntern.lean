import ConPanqueque.T.LvlView
import ConRon.Arena.WF
open ConRon.Arena

/-!
# Re-interning a denotation is the identity

On a well-formed store (con-ron's `StoreWF`: every viewed node is found by its view, persistent first),
interning the readback of a handle probes its way back to that handle and changes nothing. The port uses
this to keep arena handles where the twin re-interns their trees.
-/

namespace ConPanqueque.T

theorem nfind_of_view (ns : NStore) (rk : NIdx → Nat) (hw : NWFAt ns rk) (h : NIdx) (v : NNodeView)
    (hv : ns.view h = some v) : ns.find? v = some h := by
  unfold NStore.find?
  cases hp : h.isPersistent with
  | true => rw [(hw.consP v h).mpr ⟨hv, hp⟩]
  | false =>
    have hs := (hw.consS v h).mpr ⟨hv, hp⟩
    rw [hw.fresh v h hs]
    have hon : ns.scratchOn = true := by
      cases e : ns.scratchOn with
      | true => rfl
      | false => simp [NStore.view, hp, e] at hv
    simp [hon, hs]

theorem lfind_of_view (ls : LStore) (rk : LIdx → Nat) (hw : LWFAt ls rk) (h : LIdx) (v : LNodeView)
    (hv : ls.view h = some v) : ls.find? v = some h := by
  unfold LStore.find?
  cases hp : h.isPersistent with
  | true => rw [(hw.consP v h).mpr ⟨hv, hp⟩]
  | false =>
    have hs := (hw.consS v h).mpr ⟨hv, hp⟩
    rw [hw.fresh v h hs]
    have hon : ls.scratchOn = true := by
      cases e : ls.scratchOn with
      | true => rfl
      | false => simp [LStore.view, hp, e] at hv
    simp [hon, hs]

theorem nview_of_denote (ns : NStore) (f : Nat) (h : NIdx) (n : ConLeche.Name) (hd : denoteNAux ns f h = some n) :
    ∃ v, ns.view h = some v := by
  cases f with
  | zero => simp [denoteNAux] at hd
  | succ f =>
    simp only [denoteNAux] at hd
    cases e : ns.view h with
    | none => rw [e] at hd; simp at hd
    | some v => exact ⟨v, rfl⟩

theorem lview_of_denote (ls : LStore) (f : Nat) (h : LIdx) (l : ConLeche.Level) (hd : denoteLAux ls f h = some l) :
    ∃ v, ls.view h = some v := by
  cases f with
  | zero => simp [denoteLAux] at hd
  | succ f =>
    simp only [denoteLAux] at hd
    cases e : ls.view h with
    | none => rw [e] at hd; simp at hd
    | some v => exact ⟨v, rfl⟩

theorem internNNode_view (s : AState) (rk : NIdx → Nat) (hw : NWFAt s.store.ns rk) (h : NIdx) (v : NNodeView)
    (hv : s.store.ns.view h = some v) : internNNode v s = .ok (h, s) := by
  unfold internNNode
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, Except.bind,
    Except.pure]
  rw [nfind_of_view _ rk hw h v hv]; rfl

theorem internLNode_view (s : AState) (rk : LIdx → Nat) (hw : LWFAt s.store.ls rk) (h : LIdx) (v : LNodeView)
    (hv : s.store.ls.view h = some v) : internLNode v s = .ok (h, s) := by
  unfold internLNode
  simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, Except.bind,
    Except.pure]
  rw [lfind_of_view _ rk hw h v hv]; rfl

theorem internName_denote (s : AState) (rk : NIdx → Nat) (hw : NWFAt s.store.ns rk) :
    ∀ (n : ConLeche.Name) (f : Nat) (h : NIdx), denoteNAux s.store.ns f h = some n → internName n s = .ok (h, s) := by
  intro n
  induction n with
  | anonymous =>
    intro f h hd
    obtain ⟨v, hv⟩ := nview_of_denote _ f h _ hd
    rcases denoteNAux_cases _ f h _ v hd hv with ⟨rfl, -⟩ | ⟨p, str, q, f', rfl, e, -⟩ | ⟨p, k, q, f', rfl, e, -⟩
    · simp only [internName]; exact internNNode_view s rk hw h _ hv
    · cases e
    · cases e
  | str p str ih =>
    intro f h hd
    obtain ⟨v, hv⟩ := nview_of_denote _ f h _ hd
    rcases denoteNAux_cases _ f h _ v hd hv with ⟨rfl, e⟩ | ⟨p', str', q, f', rfl, e, hq⟩ | ⟨p', k, q, f', rfl, e, -⟩
    · cases e
    · simp only [ConLeche.Name.str.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      simp only [internName, bind, StateT.bind, Except.bind]
      rw [ih f' p' hq]
      exact internNNode_view s rk hw h _ hv
    · cases e
  | num p k ih =>
    intro f h hd
    obtain ⟨v, hv⟩ := nview_of_denote _ f h _ hd
    rcases denoteNAux_cases _ f h _ v hd hv with ⟨rfl, e⟩ | ⟨p', str', q, f', rfl, e, -⟩ | ⟨p', k', q, f', rfl, e, hq⟩
    · cases e
    · cases e
    · simp only [ConLeche.Name.num.injEq] at e
      obtain ⟨rfl, rfl⟩ := e
      simp only [internName, bind, StateT.bind, Except.bind]
      rw [ih f' p' hq]
      exact internNNode_view s rk hw h _ hv

theorem internLevel_denote (s : AState) (rk : LIdx → Nat) (hw : LWFAt s.store.ls rk) (rkn : NIdx → Nat)
    (hwn : NWFAt s.store.ns rkn) :
    ∀ (l : ConLeche.Level) (f : Nat) (h : LIdx), denoteLAux s.store.ls f h = some l → internLevel l s = .ok (h, s) := by
  intro l
  induction l with
  | zero =>
    intro f h hd
    obtain ⟨v, hv⟩ := lview_of_denote _ f h _ hd
    rcases denoteLAux_cases _ f h _ v hd hv with ⟨rfl, -⟩ | ⟨_, _, _, rfl, e, -⟩ | ⟨_, _, _, _, _, rfl, e, -⟩ |
      ⟨_, _, _, _, _, rfl, e, -⟩ | ⟨_, _, rfl, e, -⟩
    · simp only [internLevel]; exact internLNode_view s rk hw h _ hv
    all_goals cases e
  | succ u ih =>
    intro f h hd
    obtain ⟨v, hv⟩ := lview_of_denote _ f h _ hd
    rcases denoteLAux_cases _ f h _ v hd hv with ⟨rfl, e⟩ | ⟨a, la, f', rfl, e, ha⟩ | ⟨_, _, _, _, _, rfl, e, -⟩ |
      ⟨_, _, _, _, _, rfl, e, -⟩ | ⟨_, _, rfl, e, -⟩
    · cases e
    · cases e
      simp only [internLevel, bind, StateT.bind, Except.bind]
      rw [ih f' a ha]
      exact internLNode_view s rk hw h _ hv
    all_goals cases e
  | max u w ihu ihw =>
    intro f h hd
    obtain ⟨v, hv⟩ := lview_of_denote _ f h _ hd
    rcases denoteLAux_cases _ f h _ v hd hv with ⟨rfl, e⟩ | ⟨_, _, _, rfl, e, -⟩ | ⟨a, b, la, lb, f', rfl, e, ha, hb⟩ |
      ⟨_, _, _, _, _, rfl, e, -⟩ | ⟨_, _, rfl, e, -⟩
    · cases e
    · cases e
    · cases e
      simp only [internLevel, bind, StateT.bind, Except.bind]
      rw [ihu f' a ha]; simp only; rw [ihw f' b hb]
      exact internLNode_view s rk hw h _ hv
    all_goals cases e
  | imax u w ihu ihw =>
    intro f h hd
    obtain ⟨v, hv⟩ := lview_of_denote _ f h _ hd
    rcases denoteLAux_cases _ f h _ v hd hv with ⟨rfl, e⟩ | ⟨_, _, _, rfl, e, -⟩ | ⟨_, _, _, _, _, rfl, e, -⟩ |
      ⟨a, b, la, lb, f', rfl, e, ha, hb⟩ | ⟨_, _, rfl, e, -⟩
    · cases e
    · cases e
    · cases e
    · cases e
      simp only [internLevel, bind, StateT.bind, Except.bind]
      rw [ihu f' a ha]; simp only; rw [ihw f' b hb]
      exact internLNode_view s rk hw h _ hv
    · cases e
  | param n =>
    intro f h hd
    obtain ⟨v, hv⟩ := lview_of_denote _ f h _ hd
    rcases denoteLAux_cases _ f h _ v hd hv with ⟨rfl, e⟩ | ⟨_, _, _, rfl, e, -⟩ | ⟨_, _, _, _, _, rfl, e, -⟩ |
      ⟨_, _, _, _, _, rfl, e, -⟩ | ⟨nh, x, rfl, e, hx⟩
    · cases e
    · cases e
    · cases e
    · cases e
    · cases e
      simp only [internLevel, bind, StateT.bind, Except.bind]
      rw [internName_denote s rkn hwn _ _ nh hx]
      exact internLNode_view s rk hw h _ hv

end ConPanqueque.T
