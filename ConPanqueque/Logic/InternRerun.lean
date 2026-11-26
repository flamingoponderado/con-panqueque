import ConRon.Arena.Basis
import ConRon.Bridge.Pers
import ConRon.Bridge.ExprOps.MemoSpecs

/-!
# Interning is a no-op on present nodes

A successful interning run, rerun at a store that still finds every node the run's end store finds (the
persistent cons tables only grown, the scratch tier off), answers the same and leaves the state alone.
-/

namespace ConPanqueque.Logic.InternRerun

open ConRon.Arena ConRon.Bridge

theorem tbl_find?_push_self {α ι δ : Type} [BEq α] [Hashable α] [LawfulBEq α] (t : Tbl α ι δ) (a : α) (d : δ) (i : ι) :
    (t.push a d i).find? a = some i := by
  cases t; simp [Tbl.push, Tbl.find?]

theorem tbl_find?_push_other {α ι δ : Type} [BEq α] [Hashable α] [LawfulBEq α] (t : Tbl α ι δ) (a : α) (d : δ)
    (i : ι) (ha : t.find? a = none) {a' : α} {h : ι} (h' : t.find? a' = some h) : (t.push a d i).find? a' = some h := by
  cases t
  simp only [Tbl.push, Tbl.find?] at *
  rw [Std.HashMap.getElem?_insert]
  by_cases e : (a == a') = true
  · have : a = a' := by simpa using e
    subst this; rw [ha] at h'; cases h'
  · simp only [e, Bool.false_eq_true, ↓reduceIte]; exact h'

theorem nt_find?_push_self (t : NTables) (v : NNodeView) (d : UInt64) (tier : UInt32) :
    (t.push v d tier).1.find? v = some (t.push v d tier).2 := by
  cases v <;> simp [NTables.push, NTables.find?, tbl_find?_push_self]

theorem nt_find?_push_other (t : NTables) (v : NNodeView) (d : UInt64) (tier : UInt32) (hv : t.find? v = none)
    {v' : NNodeView} {h : NIdx} (h' : t.find? v' = some h) : (t.push v d tier).1.find? v' = some h := by
  cases v <;> cases v' <;> simp only [NTables.push, NTables.find?] at hv h' ⊢ <;>
    first | exact h' | exact tbl_find?_push_other _ _ _ _ hv h'

/-- The scratch tier off, in all four stores. -/
def Off (st : EStore) : Prop :=
  st.scratchOn = false ∧ st.lss.scratchOn = false ∧ st.lss.ls.scratchOn = false ∧ st.lss.ls.ns.scratchOn = false

/-- Every persistent cons entry of `a` is one of `b`'s. -/
def FP (a b : EStore) : Prop :=
  (∀ v h, a.lss.ls.ns.pers.find? v = some h → b.lss.ls.ns.pers.find? v = some h) ∧
  (∀ v h, a.lss.ls.pers.find? v = some h → b.lss.ls.pers.find? v = some h) ∧
  (∀ v h, a.lss.pers.find? v = some h → b.lss.pers.find? v = some h) ∧
  (∀ v h, a.pers.find? v = some h → b.pers.find? v = some h)

theorem FP.refl (a : EStore) : FP a a := ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩

theorem FP.trans {a b c : EStore} (h1 : FP a b) (h2 : FP b c) : FP a c :=
  ⟨fun v h x => h2.1 v h (h1.1 v h x), fun v h x => h2.2.1 v h (h1.2.1 v h x),
    fun v h x => h2.2.2.1 v h (h1.2.2.1 v h x), fun v h x => h2.2.2.2 v h (h1.2.2.2 v h x)⟩

/-- **A rerunnable interning computation**: a successful run, rerun at any scratch-off state whose
persistent cons tables contain the run's end ones, answers the same and moves nothing. -/
def RR {α : Type} (x : AM α) : Prop :=
  ∀ s0 r s1, Off s0.store → x s0 = .ok (r, s1) → Off s1.store ∧ FP s0.store s1.store ∧
    ∀ s, Off s.store → FP s1.store s.store → x s = .ok (r, s)

theorem RR.pure {α : Type} (a : α) : RR (pure a : AM α) := by
  intro s0 r s1 ho h
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h
  exact ⟨ho, FP.refl _, fun s _ _ => rfl⟩

theorem RR.bind {α β : Type} {x : AM α} {f : α → AM β} (hx : RR x) (hf : ∀ a, RR (f a)) : RR (x >>= f) := by
  intro s0 r s1 ho h
  obtain ⟨a, sA, h1, h2⟩ := AM.bind_ok h
  obtain ⟨hoA, hpA, hrA⟩ := hx s0 a sA ho h1
  obtain ⟨ho1, hp1, hr1⟩ := hf a sA r s1 hoA h2
  refine ⟨ho1, hpA.trans hp1, fun s hos hps => ?_⟩
  rw [AM.bind_apply, hrA s hos (hp1.trans hps)]
  exact hr1 s hos hps

theorem ns_intern (st : NStore) (hoff : st.scratchOn = false) (v : NNodeView) :
    (st.intern v).1.pers.find? v = some (st.intern v).2 ∧
    (∀ v' h, st.pers.find? v' = some h → (st.intern v).1.pers.find? v' = some h) ∧
    (st.intern v).1.scratchOn = false := by
  unfold NStore.intern
  rcases hf : st.pers.find? v with _ | i
  · simp only [hoff, Bool.false_eq_true, ↓reduceIte]
    exact ⟨nt_find?_push_self _ _ _ _, fun v' h h' => nt_find?_push_other _ _ _ _ hf h', by simp [hoff]⟩
  · exact ⟨hf, fun _ _ h => h, hoff⟩

theorem internNNode_ok {v : NNodeView} {s : AState} {r : NIdx} {s' : AState}
    (h : internNNode v s = .ok (r, s')) :
    (s.store.ns.find? v = some r ∧ s' = s) ∨
      (s.store.ns.find? v = none ∧ r = (s.store.internName v).2 ∧
        s' = { s with store := (s.store.internName v).1 }) := by
  cases hf : s.store.ns.find? v with
  | some i =>
    simp only [internNNode, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.bind, Except.pure, hf, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, rfl⟩
  | none =>
    by_cases hc : (if s.store.ns.scratchOn then s.store.ns.scr.sizeOf v
        else s.store.ns.pers.sizeOf v) < Idx.idxCap
    · simp only [internNNode, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, set, StateT.set, Except.bind, Except.pure, hf,
        ite_eq_left hc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr ⟨rfl, rfl, rfl⟩
    · simp only [internNNode, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, set, Except.bind, Except.pure, hf,
        ite_eq_right hc, fail, throwThe, MonadExceptOf.throw, Function.comp,
        StateT.lift] at h
      exact absurd h (by simp)

theorem nfind_off {st : NStore} (hs : st.scratchOn = false) (v : NNodeView) : st.find? v = st.pers.find? v := by
  unfold NStore.find?; cases st.pers.find? v <;> simp [hs]

theorem internNNode_rr (v : NNodeView) : RR (internNNode v) := by
  intro s0 r s1 ho h
  have hrr : ∀ s : AState, Off s.store → s.store.lss.ls.ns.pers.find? v = some r → internNNode v s = .ok (r, s) := by
    intro s hos hf
    have : s.store.ns.find? v = some r := by rw [show s.store.ns = s.store.lss.ls.ns from rfl, nfind_off hos.2.2.2]; exact hf
    simp only [internNNode, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.bind, Except.pure, this]
  rcases internNNode_ok h with ⟨hf, rfl⟩ | ⟨hf, rfl, rfl⟩
  · refine ⟨ho, FP.refl _, fun s hos hps => hrr s hos (hps.1 v r ?_)⟩
    rw [← nfind_off ho.2.2.2]; exact hf
  · obtain ⟨n1, n2, n3⟩ := ns_intern s0.store.lss.ls.ns ho.2.2.2 v
    refine ⟨⟨ho.1, ho.2.1, ho.2.2.1, n3⟩, ⟨fun v' h h' => n2 v' h h', fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩,
      fun s hos hps => hrr s hos (hps.1 v _ n1)⟩

theorem lt_find?_push_self (t : LTables) (v : LNodeView) (d : LDer) (tier : UInt32) :
    (t.push v d tier).1.find? v = some (t.push v d tier).2 := by
  cases v <;> simp [LTables.push, LTables.find?, tbl_find?_push_self]

theorem lt_find?_push_other (t : LTables) (v : LNodeView) (d : LDer) (tier : UInt32) (hv : t.find? v = none)
    {v' : LNodeView} {h : LIdx} (h' : t.find? v' = some h) : (t.push v d tier).1.find? v' = some h := by
  cases v <;> cases v' <;> simp only [LTables.push, LTables.find?] at hv h' ⊢ <;>
    first | exact h' | exact tbl_find?_push_other _ _ _ _ hv h'

theorem ls_intern (st : LStore) (hoff : st.scratchOn = false) (v : LNodeView) :
    (st.intern v).1.pers.find? v = some (st.intern v).2 ∧
    (∀ v' h, st.pers.find? v' = some h → (st.intern v).1.pers.find? v' = some h) ∧
    (st.intern v).1.scratchOn = false := by
  unfold LStore.intern
  rcases hf : st.pers.find? v with _ | i
  · simp only [hoff, Bool.false_eq_true, ↓reduceIte]
    exact ⟨lt_find?_push_self _ _ _ _, fun v' h h' => lt_find?_push_other _ _ _ _ hf h', by simp [hoff]⟩
  · exact ⟨hf, fun _ _ h => h, hoff⟩


theorem lstore_intern_ns (st : LStore) (v : LNodeView) : (st.intern v).1.ns = st.ns := by
  unfold LStore.intern; split
  · rfl
  · split
    · split <;> rfl
    · rfl

theorem lsstore_intern_ls (st : LsStore) (v : LsNodeView) : (st.intern v).1.ls = st.ls := by
  unfold LsStore.intern; split
  · rfl
  · split
    · split <;> rfl
    · rfl

theorem estore_internLevel_ns (st : EStore) (v : LNodeView) :
    (st.internLevel v).1.lss.ls.ns = st.lss.ls.ns ∧ (st.internLevel v).1.lss.pers = st.lss.pers ∧
    (st.internLevel v).1.pers = st.pers ∧ (st.internLevel v).1.scratchOn = st.scratchOn ∧
    (st.internLevel v).1.lss.scratchOn = st.lss.scratchOn ∧ (st.internLevel v).1.lss.ls = (st.ls.intern v).1 ∧
    (st.internLevel v).2 = (st.ls.intern v).2 := by
  simp [EStore.internLevel, LsStore.internLevel, lstore_intern_ns]; exact ⟨rfl, rfl⟩

theorem estore_internLevels_ls (st : EStore) (v : LsNodeView) :
    (st.internLevels v).1.lss.ls = st.lss.ls ∧ (st.internLevels v).1.pers = st.pers ∧
    (st.internLevels v).1.scratchOn = st.scratchOn ∧ (st.internLevels v).1.lss = (st.lss.intern v).1 ∧
    (st.internLevels v).2 = (st.lss.intern v).2 := by
  simp [EStore.internLevels, lsstore_intern_ls]

theorem internLNode_ok {v : LNodeView} {s : AState} {r : LIdx} {s' : AState}
    (h : internLNode v s = .ok (r, s')) :
    (s.store.ls.find? v = some r ∧ s' = s) ∨
      (s.store.ls.find? v = none ∧ r = (s.store.internLevel v).2 ∧
        s' = { s with store := (s.store.internLevel v).1 }) := by
  cases hf : s.store.ls.find? v with
  | some i =>
    simp only [internLNode, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.bind, Except.pure, hf, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, rfl⟩
  | none =>
    by_cases hc : (if s.store.ls.scratchOn then s.store.ls.scr.sizeOf v
        else s.store.ls.pers.sizeOf v) < Idx.idxCap
    · simp only [internLNode, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, set, StateT.set, Except.bind, Except.pure, hf,
        ite_eq_left hc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr ⟨rfl, rfl, rfl⟩
    · simp only [internLNode, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, set, Except.bind, Except.pure, hf,
        ite_eq_right hc, fail, throwThe, MonadExceptOf.throw, Function.comp,
        StateT.lift] at h
      exact absurd h (by simp)

theorem lfind_off {st : LStore} (hs : st.scratchOn = false) (v : LNodeView) : st.find? v = st.pers.find? v := by
  unfold LStore.find?; cases st.pers.find? v <;> simp [hs]

theorem internLNode_rr (v : LNodeView) : RR (internLNode v) := by
  intro s0 r s1 ho h
  have hrr : ∀ s : AState, Off s.store → s.store.ls.pers.find? v = some r → internLNode v s = .ok (r, s) := by
    intro s hos hf
    have : s.store.ls.find? v = some r := by rw [lfind_off (st := s.store.ls) hos.2.2.1]; exact hf
    simp only [internLNode, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.bind, Except.pure, this]
  rcases internLNode_ok h with ⟨hf, rfl⟩ | ⟨hf, rfl, rfl⟩
  · refine ⟨ho, FP.refl _, fun s hos hps => hrr s hos (hps.2.1 v r ?_)⟩
    rw [← lfind_off ho.2.2.1]; exact hf
  · obtain ⟨n1, n2, n3⟩ := ls_intern s0.store.ls ho.2.2.1 v
    obtain ⟨e1, e2, e3, e4, e5, e6, e7⟩ := estore_internLevel_ns s0.store v
    have ho' : Off (s0.store.internLevel v).1 := ⟨by rw [e4]; exact ho.1, by rw [e5]; exact ho.2.1,
      by rw [e6]; exact n3, by rw [e1]; exact ho.2.2.2⟩
    refine ⟨ho', ⟨fun v' h h' => by rw [e1]; exact h', fun v' h h' => by rw [e6]; exact n2 v' h h',
      fun v' h h' => by rw [e2]; exact h', fun v' h h' => by rw [e3]; exact h'⟩,
      fun s hos hps => hrr s hos (hps.2.1 v _ (by rw [e6, e7]; exact n1))⟩

theorem lst_find?_push_self (t : LsTables) (v : LsNodeView) (d : LDer) (tier : UInt32) :
    (t.push v d tier).1.find? v = some (t.push v d tier).2 := by
  simp [LsTables.push, LsTables.find?, tbl_find?_push_self]

theorem lst_find?_push_other (t : LsTables) (v : LsNodeView) (d : LDer) (tier : UInt32) (hv : t.find? v = none)
    {v' : LsNodeView} {h : LsIdx} (h' : t.find? v' = some h) : (t.push v d tier).1.find? v' = some h := by
  simp only [LsTables.push, LsTables.find?] at hv h' ⊢
  exact tbl_find?_push_other _ _ _ _ hv h'

theorem lss_intern (st : LsStore) (hoff : st.scratchOn = false) (v : LsNodeView) :
    (st.intern v).1.pers.find? v = some (st.intern v).2 ∧
    (∀ v' h, st.pers.find? v' = some h → (st.intern v).1.pers.find? v' = some h) ∧
    (st.intern v).1.scratchOn = false := by
  unfold LsStore.intern
  rcases hf : st.pers.find? v with _ | i
  · simp only [hoff, Bool.false_eq_true, ↓reduceIte]
    exact ⟨lst_find?_push_self _ _ _ _, fun v' h h' => lst_find?_push_other _ _ _ _ hf h', by simp [hoff]⟩
  · exact ⟨hf, fun _ _ h => h, hoff⟩

theorem internLsNode_ok {v : LsNodeView} {s : AState} {r : LsIdx} {s' : AState}
    (h : internLsNode v s = .ok (r, s')) :
    (s.store.lss.find? v = some r ∧ s' = s) ∨
      (s.store.lss.find? v = none ∧ r = (s.store.internLevels v).2 ∧
        s' = { s with store := (s.store.internLevels v).1 }) := by
  cases hf : s.store.lss.find? v with
  | some i =>
    simp only [internLsNode, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.bind, Except.pure, hf, Except.ok.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl ⟨rfl, rfl⟩
  | none =>
    by_cases hc : (if s.store.lss.scratchOn then s.store.lss.scr.sizeOf v
        else s.store.lss.pers.sizeOf v) < Idx.idxCap
    · simp only [internLsNode, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, StateT.pure, set, StateT.set, Except.bind, Except.pure, hf,
        ite_eq_left hc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inr ⟨rfl, rfl, rfl⟩
    · simp only [internLsNode, bind, StateT.bind, get, getThe, MonadStateOf.get,
        StateT.get, pure, set, Except.bind, Except.pure, hf,
        ite_eq_right hc, fail, throwThe, MonadExceptOf.throw, Function.comp,
        StateT.lift] at h
      exact absurd h (by simp)

theorem lsfind_off {st : LsStore} (hs : st.scratchOn = false) (v : LsNodeView) : st.find? v = st.pers.find? v := by
  unfold LsStore.find?; cases st.pers.find? v <;> simp [hs]

theorem internLsNode_rr (v : LsNodeView) : RR (internLsNode v) := by
  intro s0 r s1 ho h
  have hrr : ∀ s : AState, Off s.store → s.store.lss.pers.find? v = some r → internLsNode v s = .ok (r, s) := by
    intro s hos hf
    have : s.store.lss.find? v = some r := by rw [lsfind_off (st := s.store.lss) hos.2.1]; exact hf
    simp only [internLsNode, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.bind, Except.pure, this]
  rcases internLsNode_ok h with ⟨hf, rfl⟩ | ⟨hf, rfl, rfl⟩
  · refine ⟨ho, FP.refl _, fun s hos hps => hrr s hos (hps.2.2.1 v r ?_)⟩
    rw [← lsfind_off ho.2.1]; exact hf
  · obtain ⟨n1, n2, n3⟩ := lss_intern s0.store.lss ho.2.1 v
    obtain ⟨e1, e2, e3, e4, e5⟩ := estore_internLevels_ls s0.store v
    have ho' : Off (s0.store.internLevels v).1 := ⟨by rw [e3]; exact ho.1, by rw [e4]; exact n3,
      by rw [e1]; exact ho.2.2.1, by rw [e1]; exact ho.2.2.2⟩
    refine ⟨ho', ⟨fun v' h h' => by rw [e1]; exact h', fun v' h h' => by rw [e1]; exact h',
      fun v' h h' => by rw [e4]; exact n2 v' h h', fun v' h h' => by rw [e2]; exact h'⟩,
      fun s hos hps => hrr s hos (hps.2.2.1 v _ (by rw [e4, e5]; exact n1))⟩

theorem et_find?_push_self (t : ETables) (v : ENodeView) (d : UInt64) (tier : UInt32) :
    (t.push v d tier).1.find? v = some (t.push v d tier).2 := by
  cases v <;> simp [ETables.push, ETables.find?, tbl_find?_push_self]

theorem et_find?_push_other (t : ETables) (v : ENodeView) (d : UInt64) (tier : UInt32) (hv : t.find? v = none)
    {v' : ENodeView} {h : EIdx} (h' : t.find? v' = some h) : (t.push v d tier).1.find? v' = some h := by
  cases v <;> cases v' <;> simp only [ETables.push, ETables.find?] at hv h' ⊢ <;>
    first | exact h' | exact tbl_find?_push_other _ _ _ _ hv h'

theorem et_pushBind_lam (t : ETables) (ty b : EIdx) (d : UInt64) (tier : UInt32) (hv : t.find? (.lam ty b) = none) :
    (t.pushBind ETag.lam ⟨ty, b⟩ d tier).1.find? (.lam ty b) = some (t.pushBind ETag.lam ⟨ty, b⟩ d tier).2 ∧
    ∀ v' h, t.find? v' = some h → (t.pushBind ETag.lam ⟨ty, b⟩ d tier).1.find? v' = some h := by
  refine ⟨by simp [ETables.pushBind, ETables.find?, tbl_find?_push_self], fun v' h h' => ?_⟩
  simp only [ETables.find?] at hv
  cases v' <;> simp only [ETables.pushBind, ETables.find?, ↓reduceIte] at h' ⊢ <;>
    first | exact h' | exact tbl_find?_push_other _ _ _ _ hv h'

theorem et_pushBind_forall (t : ETables) (ty b : EIdx) (d : UInt64) (tier : UInt32)
    (hv : t.find? (.forallE ty b) = none) :
    (t.pushBind ETag.forallE ⟨ty, b⟩ d tier).1.find? (.forallE ty b) =
      some (t.pushBind ETag.forallE ⟨ty, b⟩ d tier).2 ∧
    ∀ v' h, t.find? v' = some h → (t.pushBind ETag.forallE ⟨ty, b⟩ d tier).1.find? v' = some h := by
  have hne : (ETag.forallE == ETag.lam) = false := by decide
  refine ⟨by simp [ETables.pushBind, ETables.find?, tbl_find?_push_self, hne], fun v' h h' => ?_⟩
  simp only [ETables.find?] at hv
  cases v' <;> simp only [ETables.pushBind, ETables.find?, hne, Bool.false_eq_true, ↓reduceIte] at h' ⊢ <;>
    first | exact h' | exact tbl_find?_push_other _ _ _ _ hv h'

theorem efind_off {st : EStore} (hs : st.scratchOn = false) (v : ENodeView) : st.find? v = st.pers.find? v := by
  unfold EStore.find? EStore.persFindMaybe; cases st.pers.find? v <;> simp [hs]

theorem efindBind_off {st : EStore} (hs : st.scratchOn = false) (tag : UInt32) (ty b : EIdx) :
    st.findBind tag ty b = st.pers.findBind tag ⟨ty, b⟩ := by
  unfold EStore.findBind EStore.persFindBindMaybe
  simp only [hs, Bool.false_eq_true, ↓reduceIte]
  cases st.pers.findBind tag ⟨ty, b⟩ <;> rfl

theorem estore_intern (st : EStore) (hoff : st.scratchOn = false) (v : ENodeView) :
    (st.intern v).1.pers.find? v = some (st.intern v).2 ∧
    (∀ v' h, st.pers.find? v' = some h → (st.intern v).1.pers.find? v' = some h) ∧
    (st.intern v).1.scratchOn = false ∧ (st.intern v).1.lss = st.lss := by
  unfold EStore.intern EStore.persFindMaybe
  rcases hf : st.pers.find? v with _ | i
  · simp only [hoff, Bool.false_eq_true, ↓reduceIte, hf]
    refine ⟨et_find?_push_self _ _ _ _, fun v' h h' => et_find?_push_other _ _ _ _ hf h', ?_⟩
    simp [hoff]
  · simp only [hoff, Bool.false_eq_true, ↓reduceIte, hf]
    refine ⟨?_, fun _ _ h => h, ?_⟩ <;> simp [hoff, hf]

theorem internNodeE_rr (v : ENodeView) : RR (internNodeE v) := by
  intro s0 r s1 ho h
  have hrr : ∀ s : AState, Off s.store → s.store.pers.find? v = some r → internNodeE v s = .ok (r, s) := by
    intro s hos hf
    have : s.store.find? v = some r := by rw [efind_off hos.1]; exact hf
    simp only [internNodeE, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.bind, Except.pure, this]
  rcases ConRon.Bridge.ExprOps.internNodeE_ok h with ⟨hf, rfl⟩ | ⟨hf, rfl, rfl⟩
  · refine ⟨ho, FP.refl _, fun s hos hps => hrr s hos (hps.2.2.2 v r ?_)⟩
    rw [← efind_off ho.1]; exact hf
  · obtain ⟨n1, n2, n3, n4⟩ := estore_intern s0.store ho.1 v
    have ho' : Off (s0.store.intern v).1 := ⟨n3, by rw [n4]; exact ho.2.1, by rw [n4]; exact ho.2.2.1,
      by rw [n4]; exact ho.2.2.2⟩
    refine ⟨ho', ⟨fun v' h h' => by rw [n4]; exact h', fun v' h h' => by rw [n4]; exact h',
      fun v' h h' => by rw [n4]; exact h', fun v' h h' => n2 v' h h'⟩, fun s hos hps => hrr s hos (hps.2.2.2 v _ n1)⟩

theorem estore_internBind (st : EStore) (hoff : st.scratchOn = false) (tag : UInt32) (htag : tag = ETag.lam ∨ tag = ETag.forallE)
    (ty b : EIdx) (v : ENodeView) (hv : v = if tag = ETag.lam then .lam ty b else .forallE ty b) :
    (st.internBind tag ty b).1.pers.find? v = some (st.internBind tag ty b).2 ∧
    (∀ v' h, st.pers.find? v' = some h → (st.internBind tag ty b).1.pers.find? v' = some h) ∧
    (st.internBind tag ty b).1.scratchOn = false ∧ (st.internBind tag ty b).1.lss = st.lss ∧
    (st.findBind tag ty b = st.pers.find? v) := by
  have hfb : st.findBind tag ty b = st.pers.find? v := by
    rw [efindBind_off hoff]
    rcases htag with rfl | rfl
    · subst hv; simp [ETables.findBind, ETables.find?]
    · subst hv; simp [ETables.findBind, ETables.find?, show ETag.forallE ≠ ETag.lam by decide]
  refine ?_
  unfold EStore.internBind EStore.persFindBindMaybe
  rcases hf : st.pers.findBind tag ⟨ty, b⟩ with _ | i
  · simp only [hoff, Bool.false_eq_true, ↓reduceIte, hf]
    have hv0 : st.pers.find? v = none := by rw [← hfb, efindBind_off hoff]; exact hf
    rcases htag with rfl | rfl
    · subst hv
      obtain ⟨a1, a2⟩ := et_pushBind_lam st.pers ty b _ Idx.tierP (by simpa using hv0)
      refine ⟨by simpa using a1, a2, ?_⟩
      simp [hoff, hfb]
    · subst hv
      obtain ⟨a1, a2⟩ := et_pushBind_forall st.pers ty b _ Idx.tierP (by simpa [show ETag.forallE ≠ ETag.lam by decide] using hv0)
      refine ⟨by simpa [show ETag.forallE ≠ ETag.lam by decide] using a1, a2, ?_⟩
      simp [hoff, hfb]
  · simp only [hoff, Bool.false_eq_true, ↓reduceIte, hf]
    refine ⟨?_, fun _ _ h => h, ?_⟩
    · rw [← hfb, efindBind_off hoff]; exact hf
    · simp [hoff, hfb]

theorem internLamE_ok' {ty b : EIdx} {s : AState} {r : EIdx} {s' : AState}
    (h : internLamE ty b s = .ok (r, s')) :
    (s.store.findBind ETag.lam ty b = some r ∧ s' = s) ∨
      (s.store.findBind ETag.lam ty b = none ∧ r = (s.store.internBind ETag.lam ty b).2 ∧
        s' = { s with store := (s.store.internBind ETag.lam ty b).1 }) := by
  unfold internLamE at h
  cases hf : s.store.findBind ETag.lam ty b with
  | some i =>
    simp [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
      Except.pure, Except.bind, hf, StateT.pure] at h
    exact Or.inl ⟨by rw [h.1], h.2.symm⟩
  | none =>
    by_cases hc : (if s.store.scratchOn = true then s.store.scr.bindSizeOf ETag.lam
                else s.store.pers.bindSizeOf ETag.lam) < Idx.idxCap
    · simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
        Except.pure, Except.bind, hf, StateT.pure, set, StateT.set, ite_eq_left hc,
        Except.ok.injEq, Prod.mk.injEq] at h
      exact Or.inr ⟨rfl, h.1.symm, h.2.symm⟩
    · simp [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
        Except.pure, Except.bind, hf, hc, fail, throwThe, MonadExceptOf.throw,
        StateT.lift] at h

theorem internLamE_rr (ty b : EIdx) : RR (internLamE ty b) := by
  intro s0 r s1 ho h
  have hrr : ∀ s : AState, Off s.store → s.store.pers.find? (.lam ty b) = some r → internLamE ty b s = .ok (r, s) := by
    intro s hos hf
    have : s.store.findBind ETag.lam ty b = some r := by
      rw [(estore_internBind s.store hos.1 ETag.lam (by simp) ty b (.lam ty b) (by simp)).2.2.2.2]; exact hf
    simp only [internLamE, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.bind, Except.pure, this]
  obtain ⟨n1, n2, n3, n4, n5⟩ := estore_internBind s0.store ho.1 ETag.lam (by simp) ty b (.lam ty b) (by simp)
  rcases internLamE_ok' h with ⟨hf, rfl⟩ | ⟨hf, rfl, rfl⟩
  · refine ⟨ho, FP.refl _, fun s hos hps => hrr s hos (hps.2.2.2 _ r ?_)⟩
    rw [← n5]; exact hf
  · have ho' : Off (s0.store.internBind ETag.lam ty b).1 := ⟨n3, by rw [n4]; exact ho.2.1, by rw [n4]; exact ho.2.2.1,
      by rw [n4]; exact ho.2.2.2⟩
    refine ⟨ho', ⟨fun v' h h' => by rw [n4]; exact h', fun v' h h' => by rw [n4]; exact h',
      fun v' h h' => by rw [n4]; exact h', fun v' h h' => n2 v' h h'⟩, fun s hos hps => hrr s hos (hps.2.2.2 _ _ n1)⟩

theorem internForallEE_ok' {ty b : EIdx} {s : AState} {r : EIdx} {s' : AState}
    (h : internForallEE ty b s = .ok (r, s')) :
    (s.store.findBind ETag.forallE ty b = some r ∧ s' = s) ∨
      (s.store.findBind ETag.forallE ty b = none ∧ r = (s.store.internBind ETag.forallE ty b).2 ∧
        s' = { s with store := (s.store.internBind ETag.forallE ty b).1 }) := by
  unfold internForallEE at h
  cases hf : s.store.findBind ETag.forallE ty b with
  | some i =>
    simp [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
      Except.pure, Except.bind, hf, StateT.pure] at h
    exact Or.inl ⟨by rw [h.1], h.2.symm⟩
  | none =>
    by_cases hc : (if s.store.scratchOn = true then s.store.scr.bindSizeOf ETag.forallE
                else s.store.pers.bindSizeOf ETag.forallE) < Idx.idxCap
    · simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
        Except.pure, Except.bind, hf, StateT.pure, set, StateT.set, ite_eq_left hc,
        Except.ok.injEq, Prod.mk.injEq] at h
      exact Or.inr ⟨rfl, h.1.symm, h.2.symm⟩
    · simp [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure,
        Except.pure, Except.bind, hf, hc, fail, throwThe, MonadExceptOf.throw,
        StateT.lift] at h

theorem internForallEE_rr (ty b : EIdx) : RR (internForallEE ty b) := by
  intro s0 r s1 ho h
  have hrr : ∀ s : AState, Off s.store → s.store.pers.find? (.forallE ty b) = some r → internForallEE ty b s = .ok (r, s) := by
    intro s hos hf
    have : s.store.findBind ETag.forallE ty b = some r := by
      rw [(estore_internBind s.store hos.1 ETag.forallE (by simp) ty b (.forallE ty b) (by simp; decide)).2.2.2.2]; exact hf
    simp only [internForallEE, bind, StateT.bind, get, getThe, MonadStateOf.get,
      StateT.get, pure, StateT.pure, Except.bind, Except.pure, this]
  obtain ⟨n1, n2, n3, n4, n5⟩ := estore_internBind s0.store ho.1 ETag.forallE (by simp) ty b (.forallE ty b) (by simp; decide)
  rcases internForallEE_ok' h with ⟨hf, rfl⟩ | ⟨hf, rfl, rfl⟩
  · refine ⟨ho, FP.refl _, fun s hos hps => hrr s hos (hps.2.2.2 _ r ?_)⟩
    rw [← n5]; exact hf
  · have ho' : Off (s0.store.internBind ETag.forallE ty b).1 := ⟨n3, by rw [n4]; exact ho.2.1, by rw [n4]; exact ho.2.2.1,
      by rw [n4]; exact ho.2.2.2⟩
    refine ⟨ho', ⟨fun v' h h' => by rw [n4]; exact h', fun v' h h' => by rw [n4]; exact h',
      fun v' h h' => by rw [n4]; exact h', fun v' h h' => n2 v' h h'⟩, fun s hos hps => hrr s hos (hps.2.2.2 _ _ n1)⟩

theorem internE_rr (v : ENodeView) : RR (internE v) := by
  cases v
  case lam ty b => exact internLamE_rr ty b
  case forallE ty b => exact internForallEE_rr ty b
  all_goals exact internNodeE_rr _

theorem internName_rr : ∀ n : ConLeche.Name, RR (internName n)
  | .anonymous => by unfold internName; exact internNNode_rr _
  | .str p _ => by unfold internName; exact RR.bind (internName_rr p) (fun _ => internNNode_rr _)
  | .num p _ => by unfold internName; exact RR.bind (internName_rr p) (fun _ => internNNode_rr _)

theorem internLevel_rr : ∀ u : ConLeche.Level, RR (internLevel u)
  | .zero => by unfold internLevel; exact internLNode_rr _
  | .succ u => by unfold internLevel; exact RR.bind (internLevel_rr u) (fun _ => internLNode_rr _)
  | .max u v => by
    unfold internLevel
    exact RR.bind (internLevel_rr u) (fun _ => RR.bind (internLevel_rr v) (fun _ => internLNode_rr _))
  | .imax u v => by
    unfold internLevel
    exact RR.bind (internLevel_rr u) (fun _ => RR.bind (internLevel_rr v) (fun _ => internLNode_rr _))
  | .param n => by unfold internLevel; exact RR.bind (internName_rr n) (fun _ => internLNode_rr _)

theorem internLevelList_rr : ∀ us : List ConLeche.Level, RR (internLevelList us)
  | [] => by unfold internLevelList; exact RR.pure _
  | u :: us => by
    unfold internLevelList
    exact RR.bind (internLevel_rr u) (fun _ => RR.bind (internLevelList_rr us) (fun _ => RR.pure _))

theorem internLevels_rr (us : List ConLeche.Level) : RR (internLevels us) := by
  unfold internLevels; exact RR.bind (internLevelList_rr us) (fun _ => internLsNode_rr _)

open ConRon.Arena.Frontend in
theorem internExprGo_rr : ∀ (e : ConLeche.Expr) (m : EMemo), RR (internExprGo m e)
  | .bvar _, m => by unfold internExprGo; exact RR.bind (internE_rr _) (fun _ => RR.pure _)
  | .sort u, m => by
    unfold internExprGo
    exact RR.bind (internLevel_rr u) (fun _ => RR.bind (internE_rr _) (fun _ => RR.pure _))
  | .const n us, m => by
    unfold internExprGo
    exact RR.bind (internName_rr n) (fun _ => RR.bind (internLevels_rr us) (fun _ =>
      RR.bind (internE_rr _) (fun _ => RR.pure _)))
  | .lit _, m => by unfold internExprGo; exact RR.bind (internE_rr _) (fun _ => RR.pure _)
  | .fvar i ty, m => by
    unfold internExprGo
    split
    · exact RR.pure _
    · exact RR.bind (internExprGo_rr ty m) (fun p => RR.bind (internE_rr _) (fun _ => RR.pure _))
  | .app f a, m => by
    unfold internExprGo
    split
    · exact RR.pure _
    · exact RR.bind (internExprGo_rr f m) (fun p => RR.bind (internExprGo_rr a p.1) (fun q =>
        RR.bind (internE_rr _) (fun _ => RR.pure _)))
  | .lam ty b, m => by
    unfold internExprGo
    split
    · exact RR.pure _
    · exact RR.bind (internExprGo_rr ty m) (fun p => RR.bind (internExprGo_rr b p.1) (fun q =>
        RR.bind (internE_rr _) (fun _ => RR.pure _)))
  | .forallE ty b, m => by
    unfold internExprGo
    split
    · exact RR.pure _
    · exact RR.bind (internExprGo_rr ty m) (fun p => RR.bind (internExprGo_rr b p.1) (fun q =>
        RR.bind (internE_rr _) (fun _ => RR.pure _)))
  | .letE ty v b, m => by
    unfold internExprGo
    split
    · exact RR.pure _
    · exact RR.bind (internExprGo_rr ty m) (fun p => RR.bind (internExprGo_rr v p.1) (fun q =>
        RR.bind (internExprGo_rr b q.1) (fun r => RR.bind (internE_rr _) (fun _ => RR.pure _))))
  | .proj n i sub, m => by
    unfold internExprGo
    split
    · exact RR.pure _
    · exact RR.bind (internName_rr n) (fun _ => RR.bind (internExprGo_rr sub m) (fun q =>
        RR.bind (internE_rr _) (fun _ => RR.pure _)))

open ConRon.Arena.Frontend in
theorem internExprList_rr : ∀ (es : List ConLeche.Expr) (m : EMemo), RR (ConRon.Arena.Frontend.internExprList m es)
  | [], m => by unfold ConRon.Arena.Frontend.internExprList; exact RR.pure _
  | e :: es, m => by
    unfold ConRon.Arena.Frontend.internExprList
    exact RR.bind (internExprGo_rr e m) (fun p => RR.bind (internExprList_rr es p.1) (fun _ => RR.pure _))

open ConRon.Arena.Frontend in
theorem internNameList_rr : ∀ ns : List ConLeche.Name, RR (ConRon.Arena.Frontend.internNameList ns)
  | [] => by unfold ConRon.Arena.Frontend.internNameList; exact RR.pure _
  | n :: ns => by
    unfold ConRon.Arena.Frontend.internNameList
    exact RR.bind (internName_rr n) (fun _ => RR.bind (internNameList_rr ns) (fun _ => RR.pure _))

open ConRon.Arena.Frontend in
theorem internCV_rr (m : EMemo) (cv : ConLeche.ConstantVal) : RR (ConRon.Arena.Frontend.internCV m cv) := by
  unfold ConRon.Arena.Frontend.internCV
  exact RR.bind (internName_rr _) (fun _ => RR.bind (internNameList_rr _) (fun _ =>
    RR.bind (internExprGo_rr _ m) (fun _ => RR.pure _)))

open ConRon.Arena.Frontend in
theorem internFire_rr (m : EMemo) (f : ConLeche.RecRuleFire) : RR (ConRon.Arena.Frontend.internFire m f) := by
  cases f <;> unfold ConRon.Arena.Frontend.internFire
  · exact RR.pure _
  · exact RR.bind (internLevelList_rr _) (fun _ => RR.bind (internExprList_rr _ m) (fun _ => RR.pure _))
  · exact RR.bind (internLevelList_rr _) (fun _ => RR.pure _)

open ConRon.Arena.Frontend in
theorem internRule_rr (m : EMemo) (rl : ConLeche.RecRule) : RR (ConRon.Arena.Frontend.internRule m rl) := by
  unfold ConRon.Arena.Frontend.internRule
  exact RR.bind (internName_rr _) (fun _ => RR.bind (internFire_rr m _) (fun p =>
    RR.bind (internExprGo_rr _ p.1) (fun _ => RR.pure _)))

open ConRon.Arena.Frontend in
theorem internRules_rr : ∀ (rs : List ConLeche.RecRule) (m : EMemo), RR (ConRon.Arena.Frontend.internRules m rs)
  | [], m => by unfold internRules; exact RR.pure _
  | r :: rs, m => by
    unfold ConRon.Arena.Frontend.internRules
    exact RR.bind (internRule_rr m r) (fun p => RR.bind (internRules_rr rs p.1) (fun _ => RR.pure _))

open ConRon.Arena.Frontend in
theorem internCaps_rr (c : ConLeche.IndCaps) : RR (ConRon.Arena.Frontend.internCaps c) := by
  unfold ConRon.Arena.Frontend.internCaps
  exact RR.bind (internNameList_rr _) (fun _ => RR.bind (internNameList_rr _) (fun _ => RR.pure _))

open ConRon.Arena.Frontend in
theorem internCI_rr (m : EMemo) (c : ConLeche.ConstantInfo) : RR (ConRon.Arena.Frontend.internCI m c) := by
  cases c <;> unfold ConRon.Arena.Frontend.internCI
  · exact RR.bind (internCV_rr m _) (fun _ => RR.pure _)
  · exact RR.bind (internCV_rr m _) (fun p => RR.bind (internExprGo_rr _ p.1) (fun _ => RR.pure _))
  · exact RR.bind (internCV_rr m _) (fun _ => RR.pure _)
  · exact RR.bind (internCV_rr m _) (fun _ => RR.bind (internCaps_rr _) (fun _ => RR.pure _))
  · exact RR.bind (internCV_rr m _) (fun _ => RR.bind (internName_rr _) (fun _ => RR.pure _))
  · exact RR.bind (internCV_rr m _) (fun p => RR.bind (internRules_rr _ p.1) (fun _ => RR.pure _))

open ConRon.Arena.Frontend in
theorem internCIList_rr : ∀ (cs : List ConLeche.ConstantInfo) (m : EMemo), RR (ConRon.Arena.Frontend.internCIList m cs)
  | [], m => by unfold ConRon.Arena.Frontend.internCIList; exact RR.pure _
  | c :: cs, m => by
    unfold ConRon.Arena.Frontend.internCIList
    exact RR.bind (internCI_rr m c) (fun p => RR.bind (internCIList_rr cs p.1) (fun _ => RR.pure _))

/-- **The pinned blocks' intern is rerunnable.** -/
theorem basisDecls_rr (k : ConLeche.BasisKind) : RR (ConRon.Arena.BasisKind.decls k) := by
  unfold ConRon.Arena.BasisKind.decls ConRon.Arena.internCIList
  exact RR.bind (internCIList_rr _ _) (fun _ => RR.pure _)

/-! ## Totality: a viewed handle denotes -/

theorem rank_lt_n {st : NStore} {rk : NIdx → Nat} (h : NWFAt st rk) {i : NIdx} (hv : (st.view i).isSome = true) :
    rk i < st.nodeCount := by
  by_cases hp : i.isPersistent = true
  · exact Nat.lt_of_lt_of_le (h.rankP i hp hv) (NStore.persCount_le st)
  · exact h.rankS i (by simpa using hp) hv

theorem nTotalAux {st : NStore} {rk : NIdx → Nat} (h : NWFAt st rk) :
    ∀ n i, rk i < n → (st.view i).isSome = true → (denoteNAux st n i).isSome = true := by
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi hv
    obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.mp hv
    have hc := h.childOK i v hv'
    unfold denoteNAux
    rw [hv']
    cases v with
    | anonymous => simp
    | str p s =>
      obtain ⟨h1, h2, -⟩ := hc p (by simp [NNodeView.children])
      simp only [Option.bind_some, Option.isSome_map]
      exact ih p (by omega) h1
    | num p k =>
      obtain ⟨h1, h2, -⟩ := hc p (by simp [NNodeView.children])
      simp only [Option.bind_some, Option.isSome_map]
      exact ih p (by omega) h1

theorem nTotal {st : NStore} (h : NStoreWF st) {i : NIdx} (hv : (st.view i).isSome = true) :
    (denoteN st i).isSome = true := by
  obtain ⟨rk, hr⟩ := h
  exact nTotalAux hr _ i (by have := rank_lt_n hr hv; omega) hv

theorem rank_lt_l {st : LStore} {rk : LIdx → Nat} (h : LWFAt st rk) {i : LIdx} (hv : (st.view i).isSome = true) :
    rk i < st.nodeCount := by
  by_cases hp : i.isPersistent = true
  · exact Nat.lt_of_lt_of_le (h.rankP i hp hv) (LStore.persCount_le st)
  · exact h.rankS i (by simpa using hp) hv

theorem lTotalAux {st : LStore} {rk : LIdx → Nat} (h : LWFAt st rk) :
    ∀ n i, rk i < n → (st.view i).isSome = true → (denoteLAux st n i).isSome = true := by
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi hv
    obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.mp hv
    have hc := h.childOK i v hv'
    have hn := h.nchildOK i v hv'
    unfold denoteLAux
    rw [hv']
    cases v with
    | zero => simp
    | succ u =>
      obtain ⟨h1, h2, -⟩ := hc u (by simp [LNodeView.lchildren])
      simp only [Option.bind_some, Option.isSome_map]
      exact ih u (by omega) h1
    | max u w =>
      obtain ⟨h1, h2, -⟩ := hc u (by simp [LNodeView.lchildren])
      obtain ⟨h3, h4, -⟩ := hc w (by simp [LNodeView.lchildren])
      have a := ih u (by omega) h1
      have b := ih w (by omega) h3
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp a
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp b
      simp [opt2, hx, hy]
    | imax u w =>
      obtain ⟨h1, h2, -⟩ := hc u (by simp [LNodeView.lchildren])
      obtain ⟨h3, h4, -⟩ := hc w (by simp [LNodeView.lchildren])
      have a := ih u (by omega) h1
      have b := ih w (by omega) h3
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp a
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp b
      simp [opt2, hx, hy]
    | param k =>
      obtain ⟨h1, -⟩ := hn k (by simp [LNodeView.nchildren])
      simp only [Option.bind_some, Option.isSome_map]
      exact nTotal h.ns h1

theorem lTotal {st : LStore} (h : LStoreWF st) {i : LIdx} (hv : (st.view i).isSome = true) :
    (denoteL st i).isSome = true := by
  obtain ⟨rk, hr⟩ := h
  exact lTotalAux hr _ i (by have := rank_lt_l hr hv; omega) hv

theorem llistTotal {st : LStore} (h : LStoreWF st) :
    ∀ us : List LIdx, (∀ u ∈ us, (st.view u).isSome = true) → (denoteLList st us).isSome = true
  | [], _ => by simp [denoteLList]
  | u :: us, hu => by
    have a := lTotal h (hu u (by simp))
    have b := llistTotal h us (fun x hx => hu x (by simp [hx]))
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp a
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp b
    simp [denoteLList, opt2, hx, hy]

theorem lsTotal {st : LsStore} (h : LsStoreWF st) {i : LsIdx} (hv : (st.view i).isSome = true) :
    (denoteLs st i).isSome = true := by
  obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.mp hv
  unfold denoteLs
  rw [hv']
  exact llistTotal h.ls v (fun u hu => (h.lchildOK i v hv' u hu).1)

theorem rank_lt_e {st : EStore} {rk : EIdx → Nat} (h : EWFAt st rk) {i : EIdx} (hv : (st.view i).isSome = true) :
    rk i < st.nodeCount := by
  by_cases hp : i.isPersistent = true
  · exact Nat.lt_of_lt_of_le (h.rankP i hp hv) (EStore.persCount_le st)
  · exact h.rankS i (by simpa using hp) hv

theorem eTotalAux {st : EStore} {rk : EIdx → Nat} (h : EWFAt st rk) :
    ∀ n i, rk i < n → (st.view i).isSome = true → (denoteEAux st n i).isSome = true := by
  intro n
  induction n with
  | zero => intro i hi; omega
  | succ n ih =>
    intro i hi hv
    obtain ⟨v, hv'⟩ := Option.isSome_iff_exists.mp hv
    have hc := h.childOK i v hv'
    have hn := h.nchildOK i v hv'
    have hl := h.lchildOK i v hv'
    have hls := h.lschildOK i v hv'
    have hnwf : NStoreWF st.lss.ls.ns := by obtain ⟨_, hl'⟩ := h.lss.ls; exact hl'.ns
    have ech : ∀ c ∈ v.echildren, ∃ x, denoteEAux st n c = some x := fun c hcm => by
      obtain ⟨h1, h2, -⟩ := hc c hcm
      exact Option.isSome_iff_exists.mp (ih c (by omega) h1)
    unfold denoteEAux
    rw [hv']
    cases v with
    | bvar k => simp
    | lit l => simp
    | fvar k ty =>
      obtain ⟨x, hx⟩ := ech ty (by simp [ENodeView.echildren])
      simp [hx]
    | sort u =>
      obtain ⟨h1, -⟩ := hl u (by simp [ENodeView.lchildren])
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (lTotal h.lss.ls h1)
      have hx' : denoteL st.ls u = some x := hx
      simp [hx']
    | const k us =>
      obtain ⟨h1, -⟩ := hn k (by simp [ENodeView.nchildren])
      obtain ⟨h2, -⟩ := hls us (by simp [ENodeView.lschildren])
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (nTotal hnwf h1)
      obtain ⟨y, hy⟩ := Option.isSome_iff_exists.mp (lsTotal h.lss h2)
      have hx' : denoteN st.ns k = some x := hx
      simp [opt2, hx', hy]
    | app f a =>
      obtain ⟨x, hx⟩ := ech f (by simp [ENodeView.echildren])
      obtain ⟨y, hy⟩ := ech a (by simp [ENodeView.echildren])
      simp [opt2, hx, hy]
    | lam ty b =>
      obtain ⟨x, hx⟩ := ech ty (by simp [ENodeView.echildren])
      obtain ⟨y, hy⟩ := ech b (by simp [ENodeView.echildren])
      simp [opt2, hx, hy]
    | forallE ty b =>
      obtain ⟨x, hx⟩ := ech ty (by simp [ENodeView.echildren])
      obtain ⟨y, hy⟩ := ech b (by simp [ENodeView.echildren])
      simp [opt2, hx, hy]
    | letE ty w b =>
      obtain ⟨x, hx⟩ := ech ty (by simp [ENodeView.echildren])
      obtain ⟨y, hy⟩ := ech w (by simp [ENodeView.echildren])
      obtain ⟨z, hz⟩ := ech b (by simp [ENodeView.echildren])
      simp [opt3, hx, hy, hz]
    | proj k j e =>
      obtain ⟨h1, -⟩ := hn k (by simp [ENodeView.nchildren])
      obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (nTotal hnwf h1)
      obtain ⟨y, hy⟩ := ech e (by simp [ENodeView.echildren])
      have hx' : denoteN st.ns k = some x := hx
      simp [opt2, hx', hy]

theorem eTotal {st : EStore} (h : StoreWF st) {i : EIdx} (hv : (st.view i).isSome = true) :
    (denoteE st i).isSome = true := by
  obtain ⟨rk, hr⟩ := h
  exact eTotalAux hr _ i (by have := rank_lt_e hr hv; omega) hv

/-! ## `Ext` keeps views (well-formed stores) -/

theorem nview_ext {a b : NStore} (ha : NStoreWF a) (hb : NStoreWF b) (hx : NExt a b) {i : NIdx} {v : NNodeView}
    (hv : a.view i = some v) : b.view i = some v := by
  obtain ⟨rka, hra⟩ := ha
  obtain ⟨x, hxa⟩ := Option.isSome_iff_exists.mp (nTotal ⟨rka, hra⟩ (by rw [hv]; rfl))
  have hxb := hx i x hxa
  obtain ⟨v', hv'⟩ := denoteN_view hxb
  obtain ⟨rkb, hrb⟩ := hb
  rw [denoteN_unfold hra hv] at hxa
  rw [denoteN_unfold hrb hv'] at hxb
  rw [hv']
  have hbw : NStoreWF b := ⟨rkb, hrb⟩
  congr 1
  cases v with
  | anonymous =>
    cases v' with
    | anonymous => rfl
    | str p' s' =>
      simp [denoteNView] at hxa hxb; obtain ⟨q, -, h⟩ := hxb; rw [← hxa] at h; cases h
    | num p' k' =>
      simp [denoteNView] at hxa hxb; obtain ⟨q, -, h⟩ := hxb; rw [← hxa] at h; cases h
  | str p s =>
    cases v' with
    | anonymous =>
      simp [denoteNView] at hxa hxb; obtain ⟨q, -, h⟩ := hxa; rw [← hxb] at h; cases h
    | str p' s' =>
      simp [denoteNView] at hxa hxb
      obtain ⟨q, hq, rfl⟩ := hxa; obtain ⟨q', hq', h⟩ := hxb
      injection h with h1 h2; subst h1 h2
      rw [denoteN_inj hbw (hx _ _ hq) hq']
    | num p' k' =>
      simp [denoteNView] at hxa hxb
      obtain ⟨q, hq, rfl⟩ := hxa; obtain ⟨q', hq', h⟩ := hxb; cases h
  | num p k =>
    cases v' with
    | anonymous =>
      simp [denoteNView] at hxa hxb; obtain ⟨q, -, h⟩ := hxa; rw [← hxb] at h; cases h
    | str p' s' =>
      simp [denoteNView] at hxa hxb
      obtain ⟨q, hq, rfl⟩ := hxa; obtain ⟨q', hq', h⟩ := hxb; cases h
    | num p' k' =>
      simp [denoteNView] at hxa hxb
      obtain ⟨q, hq, rfl⟩ := hxa; obtain ⟨q', hq', h⟩ := hxb
      injection h with h1 h2; subst h1 h2
      rw [denoteN_inj hbw (hx _ _ hq) hq']

theorem lview_ext {a b : LStore} (ha : LStoreWF a) (hb : LStoreWF b) (hx : LExt a b) {i : LIdx} {v : LNodeView}
    (hv : a.view i = some v) : b.view i = some v := by
  obtain ⟨rka, hra⟩ := ha
  obtain ⟨x, hxa⟩ := Option.isSome_iff_exists.mp (lTotal ⟨rka, hra⟩ (by rw [hv]; rfl))
  have hxb := hx.lvl i x hxa
  obtain ⟨v', hv'⟩ := denoteL_view hxb
  have hbw := hb
  obtain ⟨rkb, hrb⟩ := hb
  have hnb : NStoreWF b.ns := hrb.ns
  rw [denoteL_unfold hra hv] at hxa
  rw [denoteL_unfold hrb hv'] at hxb
  rw [hv']
  congr 1
  cases x with
  | zero => rw [denoteLView_zero hxa, denoteLView_zero hxb]
  | succ y =>
    obtain ⟨u, rfl, hu⟩ := denoteLView_succ hxa
    obtain ⟨u', rfl, hu'⟩ := denoteLView_succ hxb
    rw [denoteL_inj hbw (hx.lvl _ _ hu) hu']
  | max y z =>
    obtain ⟨u, w, rfl, hu, hw⟩ := denoteLView_max hxa
    obtain ⟨u', w', rfl, hu', hw'⟩ := denoteLView_max hxb
    rw [denoteL_inj hbw (hx.lvl _ _ hu) hu', denoteL_inj hbw (hx.lvl _ _ hw) hw']
  | imax y z =>
    obtain ⟨u, w, rfl, hu, hw⟩ := denoteLView_imax hxa
    obtain ⟨u', w', rfl, hu', hw'⟩ := denoteLView_imax hxb
    rw [denoteL_inj hbw (hx.lvl _ _ hu) hu', denoteL_inj hbw (hx.lvl _ _ hw) hw']
  | param nm =>
    obtain ⟨n, rfl, hn⟩ := denoteLView_param hxa
    obtain ⟨n', rfl, hn'⟩ := denoteLView_param hxb
    rw [denoteN_inj hnb (hx.ns _ _ hn) hn']

theorem llist_ext {a b : LStore} (hx : LExt a b) :
    ∀ (us : List LIdx) (xs : List ConLeche.Level), denoteLList a us = some xs → denoteLList b us = some xs
  | [], xs, h => by simpa [denoteLList] using h
  | u :: us, xs, h => by
    simp only [denoteLList, opt2_eq_some_iff] at h ⊢
    obtain ⟨y, ys, hy, hys, rfl⟩ := h
    exact ⟨y, ys, hx.lvl _ _ hy, llist_ext hx us ys hys, rfl⟩

theorem lsview_ext {a b : LsStore} (ha : LsStoreWF a) (hb : LsStoreWF b) (hx : LsExt a b) {i : LsIdx}
    {v : LsNodeView} (hv : a.view i = some v) : b.view i = some v := by
  obtain ⟨xs, hxa⟩ := Option.isSome_iff_exists.mp (lsTotal ha (by rw [hv]; rfl))
  have hxb := hx.lst i xs hxa
  obtain ⟨us', hv', hd'⟩ := denoteLs_view hxb
  rw [denoteLs_unfold hv] at hxa
  unfold denoteLsView at hxa
  have hd := llist_ext hx.ls v xs hxa
  rw [hv', denoteLList_inj hb.ls v us' xs hd hd']

theorem eview_ext {a b : EStore} (ha : StoreWF a) (hb : StoreWF b) (hx : Ext a b) {i : EIdx} {v : ENodeView}
    (hv : a.view i = some v) : b.view i = some v := by
  obtain ⟨rka, hra⟩ := ha
  obtain ⟨x, hxa⟩ := Option.isSome_iff_exists.mp (eTotal ⟨rka, hra⟩ (by rw [hv]; rfl))
  have hxb := hx.expr i x hxa
  obtain ⟨v', hv'⟩ := denoteE_view hxb
  have hbw := hb
  obtain ⟨rkb, hrb⟩ := hb
  have hlb : LStoreWF b.lss.ls := hrb.lss.ls
  have hnb : NStoreWF b.lss.ls.ns := by obtain ⟨_, hl'⟩ := hrb.lss.ls; exact hl'.ns
  rw [denoteE_unfold hra hv] at hxa
  rw [denoteE_unfold hrb hv'] at hxb
  rw [hv']
  congr 1
  cases x with
  | bvar k => rw [denoteEView_bvar hxa, denoteEView_bvar hxb]
  | lit l => rw [denoteEView_lit hxa, denoteEView_lit hxb]
  | fvar k y =>
    obtain ⟨t, rfl, ht⟩ := denoteEView_fvar hxa
    obtain ⟨t', rfl, ht'⟩ := denoteEView_fvar hxb
    rw [denoteE_inj hbw (hx.expr _ _ ht) ht']
  | sort y =>
    obtain ⟨u, rfl, hu⟩ := denoteEView_sort hxa
    obtain ⟨u', rfl, hu'⟩ := denoteEView_sort hxb
    rw [denoteL_inj hlb (hx.lss.ls.lvl _ _ hu) hu']
  | const nm us =>
    obtain ⟨n, l, rfl, hn, hl⟩ := denoteEView_const hxa
    obtain ⟨n', l', rfl, hn', hl'⟩ := denoteEView_const hxb
    have e1 := denoteN_inj hnb (hx.lss.ls.ns _ _ hn) hn'
    obtain ⟨xs, hv1, hd1⟩ := denoteLs_view (hx.lss.lst _ _ hl)
    obtain ⟨xs', hv2, hd2⟩ := denoteLs_view hl'
    have e2 : l = l' := LsWF.view_inj hrb.lss hv1 (by rw [denoteLList_inj hrb.lss.ls xs xs' us hd1 hd2]; exact hv2)
    rw [e1, e2]
  | app y z =>
    obtain ⟨g, c, rfl, hg, hc⟩ := denoteEView_app hxa
    obtain ⟨g', c', rfl, hg', hc'⟩ := denoteEView_app hxb
    rw [denoteE_inj hbw (hx.expr _ _ hg) hg', denoteE_inj hbw (hx.expr _ _ hc) hc']
  | lam y z =>
    obtain ⟨g, c, rfl, hg, hc⟩ := denoteEView_lam hxa
    obtain ⟨g', c', rfl, hg', hc'⟩ := denoteEView_lam hxb
    rw [denoteE_inj hbw (hx.expr _ _ hg) hg', denoteE_inj hbw (hx.expr _ _ hc) hc']
  | forallE y z =>
    obtain ⟨g, c, rfl, hg, hc⟩ := denoteEView_forallE hxa
    obtain ⟨g', c', rfl, hg', hc'⟩ := denoteEView_forallE hxb
    rw [denoteE_inj hbw (hx.expr _ _ hg) hg', denoteE_inj hbw (hx.expr _ _ hc) hc']
  | letE y z w =>
    obtain ⟨g, c, d, rfl, hg, hc, hd⟩ := denoteEView_letE hxa
    obtain ⟨g', c', d', rfl, hg', hc', hd'⟩ := denoteEView_letE hxb
    rw [denoteE_inj hbw (hx.expr _ _ hg) hg', denoteE_inj hbw (hx.expr _ _ hc) hc',
      denoteE_inj hbw (hx.expr _ _ hd) hd']
  | proj nm j y =>
    obtain ⟨n, e, rfl, hn, he⟩ := denoteEView_proj hxa
    obtain ⟨n', e', rfl, hn', he'⟩ := denoteEView_proj hxb
    rw [denoteN_inj hnb (hx.lss.ls.ns _ _ hn) hn', denoteE_inj hbw (hx.expr _ _ he) he']

/-- **`Ext` between well-formed stores keeps every persistent cons entry.** -/
theorem fp_of_ext {a b : EStore} (ha : StoreWF a) (hb : StoreWF b) (hx : Ext a b) : FP a b := by
  have ha' := ha
  have hb' := hb
  obtain ⟨rka, hra⟩ := ha'
  obtain ⟨rkb, hrb⟩ := hb'
  obtain ⟨rla, hla⟩ := hra.lss.ls
  obtain ⟨rlb, hlb⟩ := hrb.lss.ls
  obtain ⟨rna, hna⟩ := hla.ns
  obtain ⟨rnb, hnb⟩ := hlb.ns
  refine ⟨fun v h hf => ?_, fun v h hf => ?_, fun v h hf => ?_, fun v h hf => ?_⟩
  · obtain ⟨hv, hp⟩ := (hna.consP v h).mp hf
    exact (hnb.consP v h).mpr ⟨nview_ext ⟨_, hna⟩ ⟨_, hnb⟩ hx.lss.ls.ns hv, hp⟩
  · obtain ⟨hv, hp⟩ := (hla.consP v h).mp hf
    exact (hlb.consP v h).mpr ⟨lview_ext ⟨_, hla⟩ ⟨_, hlb⟩ hx.lss.ls hv, hp⟩
  · obtain ⟨hv, hp⟩ := (hra.lss.consP v h).mp hf
    exact (hrb.lss.consP v h).mpr ⟨lsview_ext hra.lss hrb.lss hx.lss hv, hp⟩
  · obtain ⟨hv, hp⟩ := (hra.consP v h).mp hf
    exact (hrb.consP v h).mpr ⟨eview_ext ha hb hx hv, hp⟩

/-- **The pinned blocks' intern, rerun at a later well-formed, scratch-off state extending one where it ran,
answers the same and moves nothing.** -/
theorem basisDecls_noop (k : ConLeche.BasisKind) {s0 s1 s : AState} {r : List IConstantInfo}
    (ho0 : Off s0.store) (hrun : ConRon.Arena.BasisKind.decls k s0 = .ok (r, s1)) {st : EStore}
    (hfp : FP s1.store st) (hwf : StoreWF st) (hwfs : StoreWF s.store) (hx : Ext st s.store) (hos : Off s.store) :
    ConRon.Arena.BasisKind.decls k s = .ok (r, s) :=
  ((basisDecls_rr k) s0 r s1 ho0 hrun).2.2 s hos (hfp.trans (fp_of_ext hwf hwfs hx))

end ConPanqueque.Logic.InternRerun
