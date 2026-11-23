import ConPanqueque.T.Inv
import ConPanqueque.V.EApp2
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# The twin's monadic interns

`internNodeE v` probes, tests the constructor array's capacity on a miss, and interns; Pancake's
intern code refines `EStore.intern v`. The two agree whenever the new store's tables fit Pancake's
geometry, which the intern's post-state representation gives (a table never exceeds its
geometry's capacity, at most `2^26` rows).
-/

namespace ConPanqueque.T

/-- con-ron's `intern_of_find` (`Refine2/Specs.lean`), restated: a cons hit moves nothing. -/
theorem intern_of_find {st : EStore} {v : ENodeView} {h : EIdx}
    (hf : st.find? v = some h) : st.intern v = (st, h) := by
  unfold EStore.find? at hf
  unfold EStore.intern
  cases hp : st.persFindMaybe v with
  | some j =>
    simp only [hp, Option.some.injEq] at hf
    simp only [hf]
  | none =>
    simp only [hp] at hf ⊢
    by_cases hon : st.scratchOn = true
    · simp only [hon, ite_true] at hf ⊢
      cases hs : st.scr.find? v with
      | some j =>
        simp only [hs, Option.some.injEq] at hf
        simp only [hf]
      | none => simp only [hs] at hf; simp at hf
    · simp only [hon] at hf; simp at hf

variable {σ : Type}

theorem tabAt_size_le {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α] {t : PState σ} {L : Layout}
    {k tier : Nat} {enc : α → List (BitVec 64)} {dW : δ → BitVec 64 × BitVec 64} {tb : Tbl α ι δ} {mkI : Nat → ι}
    (h : TabAt t L k tier enc dW tb mkI) : tb.size ≤ (L.geo k tier).cap := by
  obtain ⟨_, _, rows, ders, slots, hu, hR⟩ := h
  have e := congrArg List.length hR.rel.nodes
  simp only [Array.length_toList] at e
  show tb.nodes.size ≤ _
  rw [e]; exact hR.vt.le


theorem twoTier_miss_size {α ι δ : Type} [BEq α] [Hashable α] (P Sc : Tbl α ι δ) (on sk : Bool) (x : α) (d : δ)
    (mkP mkS : Nat → ι) (h1 : (if on && sk then none else P.find? x) = none) (h2 : on = true → Sc.find? x = none) :
    (on = true → (twoTier P Sc on sk x d mkP mkS).2.1.size = Sc.size + 1) ∧
      (on = false → (twoTier P Sc on sk x d mkP mkS).1.size = P.size + 1) := by
  unfold twoTier
  rw [h1]
  cases on with
  | true =>
    refine ⟨fun _ => ?_, fun h => absurd h (by simp)⟩
    simp only [ite_true, tierInt, h2 rfl, Tbl.push, Tbl.size, Array.size_push]
  | false =>
    refine ⟨fun h => absurd h (by simp), fun _ => ?_⟩
    have hp : P.find? x = none := by simpa using h1
    simp only [Bool.false_eq_true, ite_false, tierInt, hp, Tbl.push, Tbl.size, Array.size_push]

/-- The twin's `internNodeE` at an `app` view is `EStore.intern`, when the new store's `app` tables
have at most `2^26` rows each. -/
theorem internNodeE_app (s : AState) (f a : EIdx)
    (hP : (s.store.intern (.app f a)).1.pers.apps.size ≤ 2 ^ 26)
    (hS : (s.store.intern (.app f a)).1.scr.apps.size ≤ 2 ^ 26) :
    internNodeE (.app f a) s = .ok ((s.store.intern (.app f a)).2, { s with store := (s.store.intern (.app f a)).1 }) := by
  show (match s.store.find? (.app f a) with
    | some h => (pure h : AM EIdx)
    | none => do
      let n := if s.store.scratchOn then s.store.scr.sizeOf (.app f a) else s.store.pers.sizeOf (.app f a)
      if n < (ENodeView.app f a).cap then do
        let st := s.store
        let s := { s with store := EStore.empty }
        let (st, h) := st.intern (.app f a)
        set { s with store := st }
        pure h
      else
        fail (.native "arena: expression constructor array full")) s = _
  cases hf : s.store.find? (.app f a) with
  | some h =>
    rw [intern_of_find hf]; rfl
  | none =>
    have hn : (if s.store.scratchOn then s.store.scr.sizeOf (.app f a) else s.store.pers.sizeOf (.app f a)) <
        (ENodeView.app f a).cap := by
      have h1 : (if s.store.scratchOn && EStore.eViewHasScratchChild (.app f a) then none
          else s.store.pers.apps.find? ⟨f, a⟩) = none := by
        revert hf; simp only [EStore.find?, EStore.persFindMaybe, ETables.find?]
        cases s.store.scratchOn <;> cases EStore.eViewHasScratchChild (.app f a) <;> simp <;>
          (cases s.store.pers.apps.find? ⟨f, a⟩ <;> simp)
      have h2 : s.store.scratchOn = true → s.store.scr.apps.find? ⟨f, a⟩ = none := by
        intro hon; revert hf; simp only [EStore.find?, EStore.persFindMaybe, ETables.find?, hon, ite_true]
        cases EStore.eViewHasScratchChild (.app f a) <;> simp <;>
          (cases s.store.pers.apps.find? ⟨f, a⟩ <;> simp)
      have T := twoTier_miss_size s.store.pers.apps s.store.scr.apps s.store.scratchOn
        (EStore.eViewHasScratchChild (.app f a)) ⟨f, a⟩ (s.store.derOfView (.app f a)) (mkW 0) (mkW 1) h1 h2
      have hint := estore_app s.store f a
      simp only at hint
      rw [hint] at hP hS
      simp only at hP hS
      show (if s.store.scratchOn then s.store.scr.apps.nodes.size else s.store.pers.apps.nodes.size) < 1073741824
      cases hon : s.store.scratchOn with
      | true =>
        have := T.1 hon
        simp only [Tbl.size] at this hS
        simp only [ite_true]; omega
      | false =>
        have := T.2 hon
        simp only [Tbl.size] at this hP
        simp only [Bool.false_eq_true, ite_false]; omega
    simp only [hn, ite_true]
    rfl

/-- The twin's `internNodeE` at a `bvar` view is `EStore.intern`, when the new store's `bvar` tables
have at most `2^26` rows each. -/
theorem internNodeE_bvar (s : AState) (i : Nat)
    (hP : (s.store.intern (.bvar i)).1.pers.bvars.size ≤ 2 ^ 26)
    (hS : (s.store.intern (.bvar i)).1.scr.bvars.size ≤ 2 ^ 26) :
    internNodeE (.bvar i) s = .ok ((s.store.intern (.bvar i)).2, { s with store := (s.store.intern (.bvar i)).1 }) := by
  show (match s.store.find? (.bvar i) with
    | some h => (pure h : AM EIdx)
    | none => do
      let n := if s.store.scratchOn then s.store.scr.sizeOf (.bvar i) else s.store.pers.sizeOf (.bvar i)
      if n < (ENodeView.bvar i).cap then do
        let st := s.store
        let s := { s with store := EStore.empty }
        let (st, h) := st.intern (.bvar i)
        set { s with store := st }
        pure h
      else
        fail (.native "arena: expression constructor array full")) s = _
  cases hf : s.store.find? (.bvar i) with
  | some h =>
    rw [intern_of_find hf]; rfl
  | none =>
    have hn : (if s.store.scratchOn then s.store.scr.sizeOf (.bvar i) else s.store.pers.sizeOf (.bvar i)) <
        (ENodeView.bvar i).cap := by
      have h1 : (if s.store.scratchOn && EStore.eViewHasScratchChild (.bvar i) then none
          else s.store.pers.bvars.find? ⟨i⟩) = none := by
        revert hf; simp only [EStore.find?, EStore.persFindMaybe, ETables.find?]
        cases s.store.scratchOn <;> cases EStore.eViewHasScratchChild (.bvar i) <;> simp <;>
          (cases s.store.pers.bvars.find? ⟨i⟩ <;> simp)
      have h2 : s.store.scratchOn = true → s.store.scr.bvars.find? ⟨i⟩ = none := by
        intro hon; revert hf; simp only [EStore.find?, EStore.persFindMaybe, ETables.find?, hon, ite_true]
        cases EStore.eViewHasScratchChild (.bvar i) <;> simp <;>
          (cases s.store.pers.bvars.find? ⟨i⟩ <;> simp)
      have T := twoTier_miss_size s.store.pers.bvars s.store.scr.bvars s.store.scratchOn
        (EStore.eViewHasScratchChild (.bvar i)) ⟨i⟩ (s.store.derOfView (.bvar i)) (mkN ETag.bvar 0) (mkN ETag.bvar 1) h1 h2
      have hint := estore_bvar s.store i
      simp only at hint
      rw [hint] at hP hS
      simp only at hP hS
      show (if s.store.scratchOn then s.store.scr.bvars.nodes.size else s.store.pers.bvars.nodes.size) < 67108864
      cases hon : s.store.scratchOn with
      | true =>
        have := T.1 hon
        simp only [Tbl.size] at this hS
        simp only [ite_true]; omega
      | false =>
        have := T.2 hon
        simp only [Tbl.size] at this hP
        simp only [Bool.false_eq_true, ite_false]; omega
    simp only [hn, ite_true]
    rfl


/-- The twin's `internNodeE` at a `fvar` view is `EStore.intern`, when the new store's `fvar` tables
have at most `2^26` rows each. -/
theorem internNodeE_fvar (s : AState) (idx : Nat) (ty : EIdx)
    (hP : (s.store.intern (.fvar idx ty)).1.pers.fvars.size ≤ 2 ^ 26)
    (hS : (s.store.intern (.fvar idx ty)).1.scr.fvars.size ≤ 2 ^ 26) :
    internNodeE (.fvar idx ty) s = .ok ((s.store.intern (.fvar idx ty)).2, { s with store := (s.store.intern (.fvar idx ty)).1 }) := by
  show (match s.store.find? (.fvar idx ty) with
    | some h => (pure h : AM EIdx)
    | none => do
      let n := if s.store.scratchOn then s.store.scr.sizeOf (.fvar idx ty) else s.store.pers.sizeOf (.fvar idx ty)
      if n < (ENodeView.fvar idx ty).cap then do
        let st := s.store
        let s := { s with store := EStore.empty }
        let (st, h) := st.intern (.fvar idx ty)
        set { s with store := st }
        pure h
      else
        fail (.native "arena: expression constructor array full")) s = _
  cases hf : s.store.find? (.fvar idx ty) with
  | some h =>
    rw [intern_of_find hf]; rfl
  | none =>
    have hn : (if s.store.scratchOn then s.store.scr.sizeOf (.fvar idx ty) else s.store.pers.sizeOf (.fvar idx ty)) <
        (ENodeView.fvar idx ty).cap := by
      have h1 : (if s.store.scratchOn && EStore.eViewHasScratchChild (.fvar idx ty) then none
          else s.store.pers.fvars.find? ⟨idx, ty⟩) = none := by
        revert hf; simp only [EStore.find?, EStore.persFindMaybe, ETables.find?]
        cases s.store.scratchOn <;> cases EStore.eViewHasScratchChild (.fvar idx ty) <;> simp <;>
          (cases s.store.pers.fvars.find? ⟨idx, ty⟩ <;> simp)
      have h2 : s.store.scratchOn = true → s.store.scr.fvars.find? ⟨idx, ty⟩ = none := by
        intro hon; revert hf; simp only [EStore.find?, EStore.persFindMaybe, ETables.find?, hon, ite_true]
        cases EStore.eViewHasScratchChild (.fvar idx ty) <;> simp <;>
          (cases s.store.pers.fvars.find? ⟨idx, ty⟩ <;> simp)
      have T := twoTier_miss_size s.store.pers.fvars s.store.scr.fvars s.store.scratchOn
        (EStore.eViewHasScratchChild (.fvar idx ty)) ⟨idx, ty⟩ (s.store.derOfView (.fvar idx ty)) (mkN ETag.fvar 0) (mkN ETag.fvar 1) h1 h2
      have hint := estore_fvar s.store idx ty
      simp only at hint
      rw [hint] at hP hS
      simp only at hP hS
      show (if s.store.scratchOn then s.store.scr.fvars.nodes.size else s.store.pers.fvars.nodes.size) < 67108864
      cases hon : s.store.scratchOn with
      | true =>
        have := T.1 hon
        simp only [Tbl.size] at this hS
        simp only [ite_true]; omega
      | false =>
        have := T.2 hon
        simp only [Tbl.size] at this hP
        simp only [Bool.false_eq_true, ite_false]; omega
    simp only [hn, ite_true]
    rfl


/-- The twin's `internNodeE` at a `sort` view is `EStore.intern`, when the new store's `sort` tables
have at most `2^26` rows each. -/
theorem internNodeE_sort (s : AState) (u : LIdx)
    (hP : (s.store.intern (.sort u)).1.pers.sorts.size ≤ 2 ^ 26)
    (hS : (s.store.intern (.sort u)).1.scr.sorts.size ≤ 2 ^ 26) :
    internNodeE (.sort u) s = .ok ((s.store.intern (.sort u)).2, { s with store := (s.store.intern (.sort u)).1 }) := by
  show (match s.store.find? (.sort u) with
    | some h => (pure h : AM EIdx)
    | none => do
      let n := if s.store.scratchOn then s.store.scr.sizeOf (.sort u) else s.store.pers.sizeOf (.sort u)
      if n < (ENodeView.sort u).cap then do
        let st := s.store
        let s := { s with store := EStore.empty }
        let (st, h) := st.intern (.sort u)
        set { s with store := st }
        pure h
      else
        fail (.native "arena: expression constructor array full")) s = _
  cases hf : s.store.find? (.sort u) with
  | some h =>
    rw [intern_of_find hf]; rfl
  | none =>
    have hn : (if s.store.scratchOn then s.store.scr.sizeOf (.sort u) else s.store.pers.sizeOf (.sort u)) <
        (ENodeView.sort u).cap := by
      have h1 : (if s.store.scratchOn && EStore.eViewHasScratchChild (.sort u) then none
          else s.store.pers.sorts.find? ⟨u⟩) = none := by
        revert hf; simp only [EStore.find?, EStore.persFindMaybe, ETables.find?]
        cases s.store.scratchOn <;> cases EStore.eViewHasScratchChild (.sort u) <;> simp <;>
          (cases s.store.pers.sorts.find? ⟨u⟩ <;> simp)
      have h2 : s.store.scratchOn = true → s.store.scr.sorts.find? ⟨u⟩ = none := by
        intro hon; revert hf; simp only [EStore.find?, EStore.persFindMaybe, ETables.find?, hon, ite_true]
        cases EStore.eViewHasScratchChild (.sort u) <;> simp <;>
          (cases s.store.pers.sorts.find? ⟨u⟩ <;> simp)
      have T := twoTier_miss_size s.store.pers.sorts s.store.scr.sorts s.store.scratchOn
        (EStore.eViewHasScratchChild (.sort u)) ⟨u⟩ (s.store.derOfView (.sort u)) (mkN ETag.sort 0) (mkN ETag.sort 1) h1 h2
      have hint := estore_sort s.store u
      simp only at hint
      rw [hint] at hP hS
      simp only at hP hS
      show (if s.store.scratchOn then s.store.scr.sorts.nodes.size else s.store.pers.sorts.nodes.size) < 67108864
      cases hon : s.store.scratchOn with
      | true =>
        have := T.1 hon
        simp only [Tbl.size] at this hS
        simp only [ite_true]; omega
      | false =>
        have := T.2 hon
        simp only [Tbl.size] at this hP
        simp only [Bool.false_eq_true, ite_false]; omega
    simp only [hn, ite_true]
    rfl


/-- The twin's `internNodeE` at a `const` view is `EStore.intern`, when the new store's `const` tables
have at most `2^26` rows each. -/
theorem internNodeE_const (s : AState) (c : NIdx) (us : LsIdx)
    (hP : (s.store.intern (.const c us)).1.pers.consts.size ≤ 2 ^ 26)
    (hS : (s.store.intern (.const c us)).1.scr.consts.size ≤ 2 ^ 26) :
    internNodeE (.const c us) s = .ok ((s.store.intern (.const c us)).2, { s with store := (s.store.intern (.const c us)).1 }) := by
  show (match s.store.find? (.const c us) with
    | some h => (pure h : AM EIdx)
    | none => do
      let n := if s.store.scratchOn then s.store.scr.sizeOf (.const c us) else s.store.pers.sizeOf (.const c us)
      if n < (ENodeView.const c us).cap then do
        let st := s.store
        let s := { s with store := EStore.empty }
        let (st, h) := st.intern (.const c us)
        set { s with store := st }
        pure h
      else
        fail (.native "arena: expression constructor array full")) s = _
  cases hf : s.store.find? (.const c us) with
  | some h =>
    rw [intern_of_find hf]; rfl
  | none =>
    have hn : (if s.store.scratchOn then s.store.scr.sizeOf (.const c us) else s.store.pers.sizeOf (.const c us)) <
        (ENodeView.const c us).cap := by
      have h1 : (if s.store.scratchOn && EStore.eViewHasScratchChild (.const c us) then none
          else s.store.pers.consts.find? ⟨c, us⟩) = none := by
        revert hf; simp only [EStore.find?, EStore.persFindMaybe, ETables.find?]
        cases s.store.scratchOn <;> cases EStore.eViewHasScratchChild (.const c us) <;> simp <;>
          (cases s.store.pers.consts.find? ⟨c, us⟩ <;> simp)
      have h2 : s.store.scratchOn = true → s.store.scr.consts.find? ⟨c, us⟩ = none := by
        intro hon; revert hf; simp only [EStore.find?, EStore.persFindMaybe, ETables.find?, hon, ite_true]
        cases EStore.eViewHasScratchChild (.const c us) <;> simp <;>
          (cases s.store.pers.consts.find? ⟨c, us⟩ <;> simp)
      have T := twoTier_miss_size s.store.pers.consts s.store.scr.consts s.store.scratchOn
        (EStore.eViewHasScratchChild (.const c us)) ⟨c, us⟩ (s.store.derOfView (.const c us)) (mkN ETag.const 0) (mkN ETag.const 1) h1 h2
      have hint := estore_const s.store c us
      simp only at hint
      rw [hint] at hP hS
      simp only at hP hS
      show (if s.store.scratchOn then s.store.scr.consts.nodes.size else s.store.pers.consts.nodes.size) < 67108864
      cases hon : s.store.scratchOn with
      | true =>
        have := T.1 hon
        simp only [Tbl.size] at this hS
        simp only [ite_true]; omega
      | false =>
        have := T.2 hon
        simp only [Tbl.size] at this hP
        simp only [Bool.false_eq_true, ite_false]; omega
    simp only [hn, ite_true]
    rfl


/-- The twin's `internNodeE` at a `letE` view is `EStore.intern`, when the new store's `letE` tables
have at most `2^26` rows each. -/
theorem internNodeE_letE (s : AState) (ty v b : EIdx)
    (hP : (s.store.intern (.letE ty v b)).1.pers.lets.size ≤ 2 ^ 26)
    (hS : (s.store.intern (.letE ty v b)).1.scr.lets.size ≤ 2 ^ 26) :
    internNodeE (.letE ty v b) s = .ok ((s.store.intern (.letE ty v b)).2, { s with store := (s.store.intern (.letE ty v b)).1 }) := by
  show (match s.store.find? (.letE ty v b) with
    | some h => (pure h : AM EIdx)
    | none => do
      let n := if s.store.scratchOn then s.store.scr.sizeOf (.letE ty v b) else s.store.pers.sizeOf (.letE ty v b)
      if n < (ENodeView.letE ty v b).cap then do
        let st := s.store
        let s := { s with store := EStore.empty }
        let (st, h) := st.intern (.letE ty v b)
        set { s with store := st }
        pure h
      else
        fail (.native "arena: expression constructor array full")) s = _
  cases hf : s.store.find? (.letE ty v b) with
  | some h =>
    rw [intern_of_find hf]; rfl
  | none =>
    have hn : (if s.store.scratchOn then s.store.scr.sizeOf (.letE ty v b) else s.store.pers.sizeOf (.letE ty v b)) <
        (ENodeView.letE ty v b).cap := by
      have h1 : (if s.store.scratchOn && EStore.eViewHasScratchChild (.letE ty v b) then none
          else s.store.pers.lets.find? ⟨ty, v, b⟩) = none := by
        revert hf; simp only [EStore.find?, EStore.persFindMaybe, ETables.find?]
        cases s.store.scratchOn <;> cases EStore.eViewHasScratchChild (.letE ty v b) <;> simp <;>
          (cases s.store.pers.lets.find? ⟨ty, v, b⟩ <;> simp)
      have h2 : s.store.scratchOn = true → s.store.scr.lets.find? ⟨ty, v, b⟩ = none := by
        intro hon; revert hf; simp only [EStore.find?, EStore.persFindMaybe, ETables.find?, hon, ite_true]
        cases EStore.eViewHasScratchChild (.letE ty v b) <;> simp <;>
          (cases s.store.pers.lets.find? ⟨ty, v, b⟩ <;> simp)
      have T := twoTier_miss_size s.store.pers.lets s.store.scr.lets s.store.scratchOn
        (EStore.eViewHasScratchChild (.letE ty v b)) ⟨ty, v, b⟩ (s.store.derOfView (.letE ty v b)) (mkN ETag.letE 0) (mkN ETag.letE 1) h1 h2
      have hint := estore_letE s.store ty v b
      simp only at hint
      rw [hint] at hP hS
      simp only at hP hS
      show (if s.store.scratchOn then s.store.scr.lets.nodes.size else s.store.pers.lets.nodes.size) < 67108864
      cases hon : s.store.scratchOn with
      | true =>
        have := T.1 hon
        simp only [Tbl.size] at this hS
        simp only [ite_true]; omega
      | false =>
        have := T.2 hon
        simp only [Tbl.size] at this hP
        simp only [Bool.false_eq_true, ite_false]; omega
    simp only [hn, ite_true]
    rfl


/-- The twin's `internNodeE` at a `lit` view is `EStore.intern`, when the new store's `lit` tables
have at most `2^26` rows each. -/
theorem internNodeE_lit (s : AState) (l : ConLeche.Literal)
    (hP : (s.store.intern (.lit l)).1.pers.lits.size ≤ 2 ^ 26)
    (hS : (s.store.intern (.lit l)).1.scr.lits.size ≤ 2 ^ 26) :
    internNodeE (.lit l) s = .ok ((s.store.intern (.lit l)).2, { s with store := (s.store.intern (.lit l)).1 }) := by
  show (match s.store.find? (.lit l) with
    | some h => (pure h : AM EIdx)
    | none => do
      let n := if s.store.scratchOn then s.store.scr.sizeOf (.lit l) else s.store.pers.sizeOf (.lit l)
      if n < (ENodeView.lit l).cap then do
        let st := s.store
        let s := { s with store := EStore.empty }
        let (st, h) := st.intern (.lit l)
        set { s with store := st }
        pure h
      else
        fail (.native "arena: expression constructor array full")) s = _
  cases hf : s.store.find? (.lit l) with
  | some h =>
    rw [intern_of_find hf]; rfl
  | none =>
    have hn : (if s.store.scratchOn then s.store.scr.sizeOf (.lit l) else s.store.pers.sizeOf (.lit l)) <
        (ENodeView.lit l).cap := by
      have h1 : (if s.store.scratchOn && EStore.eViewHasScratchChild (.lit l) then none
          else s.store.pers.lits.find? ⟨l⟩) = none := by
        revert hf; simp only [EStore.find?, EStore.persFindMaybe, ETables.find?]
        cases s.store.scratchOn <;> cases EStore.eViewHasScratchChild (.lit l) <;> simp <;>
          (cases s.store.pers.lits.find? ⟨l⟩ <;> simp)
      have h2 : s.store.scratchOn = true → s.store.scr.lits.find? ⟨l⟩ = none := by
        intro hon; revert hf; simp only [EStore.find?, EStore.persFindMaybe, ETables.find?, hon, ite_true]
        cases EStore.eViewHasScratchChild (.lit l) <;> simp <;>
          (cases s.store.pers.lits.find? ⟨l⟩ <;> simp)
      have T := twoTier_miss_size s.store.pers.lits s.store.scr.lits s.store.scratchOn
        (EStore.eViewHasScratchChild (.lit l)) ⟨l⟩ (s.store.derOfView (.lit l)) (mkN ETag.lit 0) (mkN ETag.lit 1) h1 h2
      have hint := estore_lit s.store l
      simp only at hint
      rw [hint] at hP hS
      simp only at hP hS
      show (if s.store.scratchOn then s.store.scr.lits.nodes.size else s.store.pers.lits.nodes.size) < 67108864
      cases hon : s.store.scratchOn with
      | true =>
        have := T.1 hon
        simp only [Tbl.size] at this hS
        simp only [ite_true]; omega
      | false =>
        have := T.2 hon
        simp only [Tbl.size] at this hP
        simp only [Bool.false_eq_true, ite_false]; omega
    simp only [hn, ite_true]
    rfl


/-- The twin's `internNodeE` at a `proj` view is `EStore.intern`, when the new store's `proj` tables
have at most `2^26` rows each. -/
theorem internNodeE_proj (s : AState) (c : NIdx) (i : Nat) (e : EIdx)
    (hP : (s.store.intern (.proj c i e)).1.pers.projs.size ≤ 2 ^ 26)
    (hS : (s.store.intern (.proj c i e)).1.scr.projs.size ≤ 2 ^ 26) :
    internNodeE (.proj c i e) s = .ok ((s.store.intern (.proj c i e)).2, { s with store := (s.store.intern (.proj c i e)).1 }) := by
  show (match s.store.find? (.proj c i e) with
    | some h => (pure h : AM EIdx)
    | none => do
      let n := if s.store.scratchOn then s.store.scr.sizeOf (.proj c i e) else s.store.pers.sizeOf (.proj c i e)
      if n < (ENodeView.proj c i e).cap then do
        let st := s.store
        let s := { s with store := EStore.empty }
        let (st, h) := st.intern (.proj c i e)
        set { s with store := st }
        pure h
      else
        fail (.native "arena: expression constructor array full")) s = _
  cases hf : s.store.find? (.proj c i e) with
  | some h =>
    rw [intern_of_find hf]; rfl
  | none =>
    have hn : (if s.store.scratchOn then s.store.scr.sizeOf (.proj c i e) else s.store.pers.sizeOf (.proj c i e)) <
        (ENodeView.proj c i e).cap := by
      have h1 : (if s.store.scratchOn && EStore.eViewHasScratchChild (.proj c i e) then none
          else s.store.pers.projs.find? ⟨c, i, e⟩) = none := by
        revert hf; simp only [EStore.find?, EStore.persFindMaybe, ETables.find?]
        cases s.store.scratchOn <;> cases EStore.eViewHasScratchChild (.proj c i e) <;> simp <;>
          (cases s.store.pers.projs.find? ⟨c, i, e⟩ <;> simp)
      have h2 : s.store.scratchOn = true → s.store.scr.projs.find? ⟨c, i, e⟩ = none := by
        intro hon; revert hf; simp only [EStore.find?, EStore.persFindMaybe, ETables.find?, hon, ite_true]
        cases EStore.eViewHasScratchChild (.proj c i e) <;> simp <;>
          (cases s.store.pers.projs.find? ⟨c, i, e⟩ <;> simp)
      have T := twoTier_miss_size s.store.pers.projs s.store.scr.projs s.store.scratchOn
        (EStore.eViewHasScratchChild (.proj c i e)) ⟨c, i, e⟩ (s.store.derOfView (.proj c i e)) (mkN ETag.proj 0) (mkN ETag.proj 1) h1 h2
      have hint := estore_proj s.store c i e
      simp only at hint
      rw [hint] at hP hS
      simp only at hP hS
      show (if s.store.scratchOn then s.store.scr.projs.nodes.size else s.store.pers.projs.nodes.size) < 67108864
      cases hon : s.store.scratchOn with
      | true =>
        have := T.1 hon
        simp only [Tbl.size] at this hS
        simp only [ite_true]; omega
      | false =>
        have := T.2 hon
        simp only [Tbl.size] at this hP
        simp only [Bool.false_eq_true, ite_false]; omega
    simp only [hn, ite_true]
    rfl


/-! ## The `internApp` function -/

/-- What the layout must satisfy for the interns (static facts about `C`). -/
structure CtxOK (C : Ctx) : Prop where
  sepApp : SepK C.L C.FLn C.FLl C.FLs C.FLe C.KB 2 13
  b0App : C.L.base 13 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + 1073741824
  b1App : C.L.base 13 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + 1073741824
  /-- The memo lies apart from the key buffer and the stores. -/
  kbMemo : ∀ r j, j < 3 → ¬ inR (C.mg r) (C.KB + BitVec.ofNat 64 (8 * j))
  kbMdesc : ∀ r k j, k < 8 → j < 3 → C.mG r + BitVec.ofNat 64 (8 * k) ≠ C.KB + BitVec.ofNat 64 (8 * j)
  memoOut : ∀ r c, inR (C.mg r) c → ¬ inAny C.L c
  mdescOut : ∀ r k, k < 8 → ¬ inAny C.L (C.mG r + BitVec.ofNat 64 (8 * k))
  flMemo : ∀ r F, (F = C.FLn ∨ F = C.FLl ∨ F = C.FLs ∨ F = C.FLe) → ¬ inR (C.mg r) F
  dirMemo : ∀ r k tier m, k < 19 → tier < 2 → m < 8 →
    ¬ inR (C.mg r) (descAddr C.L k tier + BitVec.ofNat 64 (8 * m))
  /-- Every memo descriptor lies outside every memo region; distinct memo regions are disjoint. -/
  mdescMemo : ∀ r r' k, k < 8 → ¬ inR (C.mg r) (C.mG r' + BitVec.ofNat 64 (8 * k))
  memoDis : ∀ r r' c, r ≠ r' → inR (C.mg r) c → ¬ inR (C.mg r') c
  /-- The value heap lies apart from the stores, the key buffer and the memos. -/
  heapOut : ∀ i, i < C.HN → ¬ inAny C.L (C.HB + BitVec.ofNat 64 (8 * i))
  kbHeap : ∀ i j, i < C.HN → j < 3 → C.HB + BitVec.ofNat 64 (8 * i) ≠ C.KB + BitVec.ofNat 64 (8 * j)
  heapMemo : ∀ r i, i < C.HN → ¬ inR (C.mg r) (C.HB + BitVec.ofNat 64 (8 * i))
  flHeap : ∀ i F, i < C.HN → (F = C.FLn ∨ F = C.FLl ∨ F = C.FLs ∨ F = C.FLe) → C.HB + BitVec.ofNat 64 (8 * i) ≠ F
  dirHeap : ∀ i k tier m, i < C.HN → k < 19 → tier < 2 → m < 8 →
    C.HB + BitVec.ofNat 64 (8 * i) ≠ descAddr C.L k tier + BitVec.ofNat 64 (8 * m)
  mdescHeap : ∀ r i k, i < C.HN → k < 8 → C.HB + BitVec.ofNat 64 (8 * i) ≠ C.mG r + BitVec.ofNat 64 (8 * k)
  heapLay : C.HB.toNat + 8 * (C.HN + 2) < 2 ^ 64
  /-- Heap addresses lie above every handle word, so a level word is told apart by size. -/
  heapHigh : 2 ^ 32 ≤ C.HB.toNat
  sepLam : SepK C.L C.FLn C.FLl C.FLs C.FLe C.KB 2 14
  b0Lam : C.L.base 14 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.lam.toUInt64.toBitVec * 67108864
  b1Lam : C.L.base 14 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.lam.toUInt64.toBitVec * 67108864
  sepFor : SepK C.L C.FLn C.FLl C.FLs C.FLe C.KB 2 15
  b0For : C.L.base 15 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.forallE.toUInt64.toBitVec * 67108864
  b1For : C.L.base 15 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.forallE.toUInt64.toBitVec * 67108864
  sepLet : SepK C.L C.FLn C.FLl C.FLs C.FLe C.KB 3 16
  b0Let : C.L.base 16 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.letE.toUInt64.toBitVec * 67108864
  b1Let : C.L.base 16 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.letE.toUInt64.toBitVec * 67108864
  sepBVar : SepK C.L C.FLn C.FLl C.FLs C.FLe C.KB 2 9
  b0BVar : C.L.base 9 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.bvar.toUInt64.toBitVec * 67108864
  b1BVar : C.L.base 9 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.bvar.toUInt64.toBitVec * 67108864
  sepProj : SepK C.L C.FLn C.FLl C.FLs C.FLe C.KB 3 18
  b0Proj : C.L.base 18 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.proj.toUInt64.toBitVec * 67108864
  b1Proj : C.L.base 18 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.proj.toUInt64.toBitVec * 67108864
  sepLZ : SepK C.L C.FLn C.FLl C.FLs C.FLe C.KB 0 3
  b0LZ : C.L.base 3 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + LTag.zero.toUInt64.toBitVec * 67108864
  b1LZ : C.L.base 3 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + LTag.zero.toUInt64.toBitVec * 67108864
  sepLS : SepK C.L C.FLn C.FLl C.FLs C.FLe C.KB 1 4
  b0LS : C.L.base 4 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + LTag.succ.toUInt64.toBitVec * 67108864
  b1LS : C.L.base 4 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + LTag.succ.toUInt64.toBitVec * 67108864
  sepLM : SepK C.L C.FLn C.FLl C.FLs C.FLe C.KB 2 5
  b0LM : C.L.base 5 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + LTag.max.toUInt64.toBitVec * 67108864
  b1LM : C.L.base 5 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + LTag.max.toUInt64.toBitVec * 67108864
  sepLI : SepK C.L C.FLn C.FLl C.FLs C.FLe C.KB 2 6
  b0LI : C.L.base 6 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + LTag.imax.toUInt64.toBitVec * 67108864
  b1LI : C.L.base 6 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + LTag.imax.toUInt64.toBitVec * 67108864
  sepLP : SepK C.L C.FLn C.FLl C.FLs C.FLe C.KB 1 7
  b0LP : C.L.base 7 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + LTag.param.toUInt64.toBitVec * 67108864
  b1LP : C.L.base 7 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + LTag.param.toUInt64.toBitVec * 67108864
  sepLs : SepK C.L C.FLn C.FLl C.FLs C.FLe C.KB 0 8
  b0Ls : C.L.base 8 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + LsTag.list.toUInt64.toBitVec * 67108864
  b1Ls : C.L.base 8 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + LsTag.list.toUInt64.toBitVec * 67108864
  sepSort : SepK C.L C.FLn C.FLl C.FLs C.FLe C.KB 1 11
  b0Sort : C.L.base 11 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.sort.toUInt64.toBitVec * 67108864
  b1Sort : C.L.base 11 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.sort.toUInt64.toBitVec * 67108864
  sepConst : SepK C.L C.FLn C.FLl C.FLs C.FLe C.KB 2 12
  b0Const : C.L.base 12 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.const.toUInt64.toBitVec * 67108864
  b1Const : C.L.base 12 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.const.toUInt64.toBitVec * 67108864
  sepFVar : SepK C.L C.FLn C.FLl C.FLs C.FLe C.KB 2 10
  b0FVar : C.L.base 10 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.fvar.toUInt64.toBitVec * 67108864
  b1FVar : C.L.base 10 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.fvar.toUInt64.toBitVec * 67108864
  sepLit : SepK C.L C.FLn C.FLl C.FLs C.FLe C.KB 0 17
  b0Lit : C.L.base 17 0 = (0 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.lit.toUInt64.toBitVec * 67108864
  b1Lit : C.L.base 17 1 = (1 : UInt32).toUInt64.toBitVec * 2147483648 + ETag.lit.toUInt64.toBitVec * 67108864
  /-- The eager side's mode-memo descriptors sit at a fixed offset from the plain side's. -/
  eoSide : ∀ k, C.mG (.m true k) = C.mG (.m false k) + C.EO
  eoNe : C.EO ≠ 0
  /-- The environment heap lies apart from the stores, the key buffer, the memos and the value heap. -/
  envOut : ∀ i, i < C.EN → ¬ inAny C.L (ecell C i)
  kbEnv : ∀ i j, i < C.EN → j < 3 → ecell C i ≠ C.KB + BitVec.ofNat 64 (8 * j)
  envMemo : ∀ r i, i < C.EN → ¬ inR (C.mg r) (ecell C i)
  flEnv : ∀ i F, i < C.EN → (F = C.FLn ∨ F = C.FLl ∨ F = C.FLs ∨ F = C.FLe) → ecell C i ≠ F
  dirEnv : ∀ i k tier m, i < C.EN → k < 19 → tier < 2 → m < 8 →
    ecell C i ≠ descAddr C.L k tier + BitVec.ofNat 64 (8 * m)
  mdescEnv : ∀ r i k, i < C.EN → k < 8 → ecell C i ≠ C.mG r + BitVec.ofNat 64 (8 * k)
  heapEnv : ∀ i j, i < C.HN → j < C.EN → C.HB + BitVec.ofNat 64 (8 * i) ≠ ecell C j
  /-- The ghost environment tables represent `C.fe`. -/
  envRel : EnvRel C
  pinsRel : PinsE C
  /-- The value heap holds fewer than `2^58` words (blocks stay below `mkAppN`'s bound, limb shifts below `2^64`). -/
  heapCap : C.HN < 2 ^ 58
  /-- Environment-heap pointers plus one are nonzero (`find?` answers `0` for a miss). -/
  envLay : C.EB.toNat + 8 * C.EN + 8 < 2 ^ 64

def fInternApp := ofString "internApp"

def internAppBody : ProgHOL 64 := prologue bin2Scratch (eBin2With Der.appDataE (eRest 13 2))

theorem kb_ne_kb8 (KB : BitVec 64) : KB ≠ KB + 8 := by
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add] at this
  have hk := KB.isLt
  have e8 : (8 : BitVec 64).toNat = 8 := rfl
  rw [e8] at this; omega

/-- The post of an expression-building call: the handle, and the new state represented. -/
def PostE (C : Ctx) (h : EIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  w = Enc.idxW h ∧ SR C s' st

theorem postE_locals (C : Ctx) : ∀ (a : EIdx) w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostE C a w s' st → PostE C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2⟩ => ⟨h1, sr_of_eq h2 rfl rfl rfl rfl⟩

theorem internApp_body_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (s : AState)
    (f a : EIdx) :
    SpecR (Pre (σ := σ) C s [(lEf, Enc.idxW f), (lEa, Enc.idxW a)]) internAppBody s (internAppE f a) (PostE C) := by
  refine specR_prologue (postE_locals C) (fun x hx => ?_) ?_
  · simp only [bin2Scratch, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  intro t ht
  have hw : ∀ y, y ∈ bin2Scratch → ∃ w, t.locals.lookup y = some (.val (.word w)) :=
    fun y hy => ht.decl y (List.mem_append_right _ hy)
  rcases eInternApp2_spec ra t C.L C.FLn C.FLl C.FLs C.FLe C.KB s.store f a ht.sr.rep hok.sepApp
      ⟨by simpa using ht.sr.kbuf 0 (by decide), by simpa using ht.sr.kbuf 1 (by decide)⟩ (kb_ne_kb8 C.KB)
      hok.b0App hok.b1App (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) hw with
    hs | ⟨hr, hsr, hc, hg, hd, _, hm⟩
  · exact Or.inl hs
  right
  refine ⟨_, hr, (s.store.intern (.app f a)).2, { s with store := (s.store.intern (.app f a)).1 }, ?_, rfl, ?_⟩
  · show internNodeE (.app f a) s = _
    exact internNodeE_app s f a
      (Nat.le_trans (tabAt_size_le hsr.e.p4) (hok.sepApp.cap 0 (by decide)))
      (Nat.le_trans (tabAt_size_le hsr.e.s4) (hok.sepApp.cap 1 (by decide)))
  · exact ⟨hsr, by rw [hg]; exact ht.sr.gdir, by rw [hg]; exact ht.sr.gfln, by rw [hg]; exact ht.sr.gfll,
      by rw [hg]; exact ht.sr.gfls, by rw [hg]; exact ht.sr.gfle, by rw [hg]; exact ht.sr.gkb,
      by rw [hc]; exact ht.sr.code, fun j hj => by rw [hd]; exact ht.sr.kbuf j hj,
      fun mk => memoAt_frame (ht.sr.memo mk)
        (fun c hc => hm c (hok.memoOut (.e mk) c hc) (fun j hj e => hok.kbMemo (.e mk) j (by omega) (e ▸ hc)))
        (fun k hk => hm _ (hok.mdescOut (.e mk) k hk) (fun j hj => hok.kbMdesc (.e mk) k j hk (by omega))) hd,
      fun mk => memoAtN_frame (ht.sr.memoN mk)
        (fun c hc => hm c (hok.memoOut (.n mk) c hc) (fun j hj e => hok.kbMemo (.n mk) j (by omega) (e ▸ hc)))
        (fun k hk => hm _ (hok.mdescOut (.n mk) k hk) (fun j hj => hok.kbMdesc (.n mk) k j hk (by omega))) hd,
      fun mk => cacheAt_frame (ht.sr.cache mk)
        (fun c hc => hm c (hok.memoOut (.c mk) c hc) (fun j hj e => hok.kbMemo (.c mk) j (by omega) (e ▸ hc)))
        (fun k hk => hm _ (hok.mdescOut (.c mk) k hk) (fun j hj => hok.kbMdesc (.c mk) k j hk (by omega))) hd,
      modeAt_frame ht.sr.mode
        (fun b mk c hc => hm c (hok.memoOut (.m b mk) c hc) (fun j hj e => hok.kbMemo (.m b mk) j (by omega) (e ▸ hc)))
        (fun b mk k hk => hm _ (hok.mdescOut (.m b mk) k hk) (fun j hj => hok.kbMdesc (.m b mk) k j hk (by omega))) hd (by first | rfl | (rw [hg]) | (rw [hg']) | (rw [hgl _ (by decide)]) | simp_all),
      envAt_frame ht.sr.env
        (fun b c hc => hm c (hok.memoOut (envR b) c hc) (fun j hj e => hok.kbMemo (envR b) j (by omega) (e ▸ hc)))
        (fun b k hk => hm _ (hok.mdescOut (envR b) k hk) (fun j hj => hok.kbMdesc (envR b) k j hk (by omega)))
        (fun i hi => hm _ (hok.envOut i hi) (fun j hj => hok.kbEnv i j hi (by omega))) hd ⟨(by first | rfl | (rw [hg]) | (rw [hg']) | (rw [hgl _ (by decide)]) | simp_all), (by first | rfl | (rw [hg]) | (rw [hg']) | (rw [hgl _ (by decide)]) | simp_all)⟩, ht.sr.pins,
      heapEx_frame ht.sr.heap (fun i hi => hm _ (hok.heapOut i hi) (fun j hj => hok.kbHeap i j hi (by omega))) hd
        (by rw [hg])⟩

/-- In a caller: `x := internApp(e₁, e₂); rest` against `internAppE f a >>= k`. -/
theorem specR_internAppI {β : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} (hok : CtxOK C)
    (hcode : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k : EIdx → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x : MlS) (e1 e2 : ExpHOL 64) (f a : EIdx) (hx : x ∈ D)
    (he1 : sev Γ e1 = some (Enc.idxW f)) (he2 : sev Γ e2 = some (Enc.idxW a))
    (hk : ∀ h s', SpecR (Inv C s' ((x, Enc.idxW h) :: Γ) [] D) rest s' (k h) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) fInternApp [e1, e2]) rest) s
      (internAppE f a >>= k) R :=
  specR_call2I x fInternApp lEf lEa (by decide) e1 e2 internAppBody (Enc.idxW f) (Enc.idxW a) hx hcode he1 he2
    (PostE C) (fun _ _ _ _ hp => hp.2)
    (fun u hu h1 h2 v hv => by
      subst hv
      exact internApp_body_spec ra C hok s f a _ ⟨hu, fun y w hy => by
        simp only [Env.get] at hy
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact h1
        · split at hy
          · rename_i e; subst e; simp at hy; subst hy; exact h2
          · simp at hy⟩)
    (fun h w s' st hp => by obtain ⟨rfl, _⟩ := hp; exact hk h s')

/-! ## Writing the key buffer -/

/-- A store into key-buffer word `j < 2` leaves the stores' representation alone. -/
theorem sr_storeKB {C : Ctx} (hok : CtxOK C) {s : AState} {t : PState σ} (h : SR C s t) (j : Nat) (hj : j < 3)
    (w : BitVec 64) :
    SR C s { t with memory := fun c => if c = C.KB + BitVec.ofNat 64 (8 * j) then .word w else t.memory c } := by
  have S := hok.sepLet
  have hne : ∀ c, c ≠ C.KB + BitVec.ofNat 64 (8 * j) →
      (fun c => if c = C.KB + BitVec.ofNat 64 (8 * j) then HolWordLab.word w else t.memory c) c = t.memory c :=
    fun c hc => by simp [hc]
  refine ⟨srep_frame h.rep ⟨hne _ ((S.fls _ (Or.inl rfl)).2.2 j hj), ?_, ?_, ?_⟩ rfl (fun k tier hk ht => ⟨fun m hm =>
      hne _ ((S.dsc k tier m hk ht hm).2.2 j hj), fun c hc => hne c (fun e => S.kbo j k tier hj hk ht (e ▸ hc))⟩),
    h.gdir, h.gfln, h.gfll, h.gfls, h.gfle, h.gkb, h.code, h.kbuf,
    fun mk => memoAt_frame (h.memo mk) (fun c hc => hne c (fun e => hok.kbMemo (.e mk) j (by omega) (e ▸ hc)))
      (fun k hk => hne _ (hok.kbMdesc (.e mk) k j hk (by omega))) rfl,
      fun mk => memoAtN_frame (h.memoN mk) (fun c hc => hne c (fun e => hok.kbMemo (.n mk) j (by omega) (e ▸ hc)))
      (fun k hk => hne _ (hok.kbMdesc (.n mk) k j hk (by omega))) rfl,
      fun mk => cacheAt_frame (h.cache mk) (fun c hc => hne c (fun e => hok.kbMemo (.c mk) j (by omega) (e ▸ hc)))
      (fun k hk => hne _ (hok.kbMdesc (.c mk) k j hk (by omega))) rfl,
      modeAt_frame h.mode (fun b mk c hc => hne c (fun e => hok.kbMemo (.m b mk) j (by omega) (e ▸ hc)))
      (fun b mk k hk => hne _ (hok.kbMdesc (.m b mk) k j hk (by omega))) rfl (by first | rfl | (rw [hg]) | (rw [hg']) | (rw [hgl _ (by decide)]) | simp_all),
      envAt_frame h.env (fun b c hc => hne c (fun e => hok.kbMemo (envR b) j (by omega) (e ▸ hc)))
      (fun b k hk => hne _ (hok.kbMdesc (envR b) k j hk (by omega)))
        (fun i hi => hne _ (hok.kbEnv i j hi hj)) rfl ⟨(by first | rfl | (rw [hg]) | (rw [hg']) | (rw [hgl _ (by decide)]) | simp_all), (by first | rfl | (rw [hg]) | (rw [hg']) | (rw [hgl _ (by decide)]) | simp_all)⟩, h.pins,
    heapEx_frame h.heap (fun i hi => hne _ (hok.kbHeap i j hi hj)) rfl rfl⟩
  · exact hne _ ((S.fls _ (Or.inr (Or.inl rfl))).2.2 j hj)
  · exact hne _ ((S.fls _ (Or.inr (Or.inr (Or.inl rfl)))).2.2 j hj)
  · exact hne _ ((S.fls _ (Or.inr (Or.inr (Or.inr rfl)))).2.2 j hj)

/-- `KB[j] := e; rest`: the twin sees nothing; afterwards the word is known (other memory facts dropped). -/
theorem specR_storeKBI {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (j : Nat) (hj : j < 3) (e : ExpHOL 64) (w : BitVec 64) (he : sev Γ e = some w) (hkb : Γ.get lKb = some C.KB)
    (h : SpecR (Inv C s Γ [(C.KB + BitVec.ofNat 64 (8 * j), w)] D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * j))]) e) rest) s m R := by
  refine specR_seq (fun t ht => ?_) h
  have hdom : t.memaddrs (C.KB + BitVec.ofNat 64 (8 * j)) := ht.sr.kbuf j (by omega)
  rw [store_word t _ e _ w (eval_add2 t _ _ _ _ (eval_vv t lKb _ (ht.env _ _ hkb)) (eval_const t _))
    (inv_ev ht he) hdom]
  refine Or.inr ⟨rfl, sr_storeKB hok ht.sr j hj w, fun y v hy => ht.env y v hy, fun a v ha => ?_, ht.decl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ha
  obtain ⟨rfl, rfl⟩ := ha
  exact ⟨hdom, by simp⟩

/-- `KB[0] := e₀; KB[1] := e₁; rest`: both words become known memory. -/
theorem specR_storeKB2I {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (e0 e1 : ExpHOL 64) (w0 w1 : BitVec 64) (he0 : sev Γ e0 = some w0) (he1 : sev Γ e1 = some w1)
    (hkb : Γ.get lKb = some C.KB)
    (h : SpecR (Inv C s Γ [(C.KB + BitVec.ofNat 64 (8 * 0), w0), (C.KB + BitVec.ofNat 64 (8 * 1), w1)] D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) e0)
      (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 1))]) e1) rest)) s m R := by
  refine specR_storeKBI hok 0 (by decide) e0 w0 he0 hkb ?_
  refine specR_seq (fun t ht => ?_) h
  have hdom : t.memaddrs (C.KB + BitVec.ofNat 64 (8 * 1)) := ht.sr.kbuf 1 (by decide)
  rw [store_word t _ e1 _ w1 (eval_add2 t _ _ _ _ (eval_vv t lKb _ (ht.env _ _ hkb)) (eval_const t _))
    (inv_ev ht he1) hdom]
  have hne : C.KB + BitVec.ofNat 64 (8 * 0) ≠ C.KB + BitVec.ofNat 64 (8 * 1) := by
    simpa using kb_ne_kb8 C.KB
  refine Or.inr ⟨rfl, sr_storeKB hok ht.sr 1 (by decide) w1, fun y v hy => ht.env y v hy, fun a v ha => ?_, ht.decl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ha
  rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨h1, h2⟩ := ht.mem _ _ (List.mem_singleton_self _)
    exact ⟨h1, by simp only; rw [if_neg hne]; exact h2⟩
  · exact ⟨hdom, by simp⟩

/-! ## The binder wrappers -/

theorem twoTier_hitP {α ι δ : Type} [BEq α] [Hashable α] (P Sc : Tbl α ι δ) (on sk : Bool) (x : α) (d : δ)
    (mkP mkS : Nat → ι) (h : ι) (hf : (if on && sk then none else P.find? x) = some h) :
    twoTier P Sc on sk x d mkP mkS = (P, Sc, h) := by
  unfold twoTier; rw [hf]

theorem twoTier_hitS {α ι δ : Type} [BEq α] [Hashable α] (P Sc : Tbl α ι δ) (on sk : Bool) (hon : on = true) (x : α)
    (d : δ) (mkP mkS : Nat → ι) (h : ι) (hf : (if on && sk then none else P.find? x) = none) (hs : Sc.find? x = some h) :
    twoTier P Sc on sk x d mkP mkS = (P, Sc, h) := by
  unfold twoTier; rw [hf]; subst hon; simp [tierInt, hs]

/-- The twin's `internLamE` is `EStore.internLam` when the new store's `lam` tables have at most `2^26` rows. -/
theorem internLamE_eq (s : AState) (ty b : EIdx)
    (hP : (s.store.internLam ty b).1.pers.lams.size ≤ 2 ^ 26)
    (hS : (s.store.internLam ty b).1.scr.lams.size ≤ 2 ^ 26) :
    internLamE ty b s = .ok ((s.store.internLam ty b).2, { s with store := (s.store.internLam ty b).1 }) := by
  have hint := estore_internLam s.store ty b
  simp only at hint
  show (match s.store.findBind ETag.lam ty b with
    | some h => (pure h : AM EIdx)
    | none => do
      let n := if s.store.scratchOn then s.store.scr.bindSizeOf ETag.lam else s.store.pers.bindSizeOf ETag.lam
      if n < Idx.idxCap then do
        let st := s.store
        let s := { s with store := EStore.empty }
        let (st, h) := st.internLam ty b
        set { s with store := st }
        pure h
      else
        fail (.native "arena: expression constructor array full")) s = _
  have e1 : (if s.store.scratchOn && EStore.bindHasScratchChild ty b then none else s.store.pers.lams.find? ⟨ty, b⟩) =
      s.store.persFindBindMaybe ETag.lam ⟨ty, b⟩ := by
    simp only [EStore.persFindBindMaybe, ETables.findBind, show (ETag.lam == ETag.lam) = true from rfl, ite_true]
    cases s.store.scratchOn <;> simp
  cases hf : s.store.findBind ETag.lam ty b with
  | some h =>
    rw [hint]
    simp only [EStore.findBind] at hf
    cases hpm : s.store.persFindBindMaybe ETag.lam ⟨ty, b⟩ with
    | some h' =>
      rw [hpm] at hf; simp at hf; subst hf
      rw [twoTier_hitP _ _ _ _ _ _ _ _ _ (by rw [e1, hpm])]; rfl
    | none =>
      rw [hpm] at hf; simp only at hf
      by_cases hon : s.store.scratchOn = true
      · rw [hon] at hf; simp only [ite_true, ETables.findBind, show (ETag.lam == ETag.lam) = true from rfl] at hf
        rw [twoTier_hitS _ _ _ _ hon _ _ _ _ _ (by rw [e1, hpm]) hf]; rfl
      · rw [show s.store.scratchOn = false by simpa using hon] at hf; simp at hf
  | none =>
    have hn : (if s.store.scratchOn then s.store.scr.bindSizeOf ETag.lam else s.store.pers.bindSizeOf ETag.lam) <
        Idx.idxCap := by
      simp only [EStore.findBind] at hf
      cases hpm : s.store.persFindBindMaybe ETag.lam ⟨ty, b⟩ with
      | some _ => rw [hpm] at hf; simp at hf
      | none =>
        rw [hpm] at hf; simp only at hf
        have h2 : s.store.scratchOn = true → s.store.scr.lams.find? ⟨ty, b⟩ = none := by
          intro hon; rw [hon] at hf; simpa [ETables.findBind] using hf
        have T := twoTier_miss_size s.store.pers.lams s.store.scr.lams s.store.scratchOn
          (EStore.bindHasScratchChild ty b) ⟨ty, b⟩ (s.store.derOfBindAt 19 ty b) (mkN ETag.lam 0) (mkN ETag.lam 1)
          (by rw [e1, hpm]) h2
        rw [hint] at hP hS
        simp only at hP hS
        show (if s.store.scratchOn then s.store.scr.lams.nodes.size else s.store.pers.lams.nodes.size) < 67108864
        cases hon : s.store.scratchOn with
        | true =>
          have := T.1 hon
          simp only [Tbl.size] at this hS
          simp only [ite_true]; omega
        | false =>
          have := T.2 hon
          simp only [Tbl.size] at this hP
          simp only [Bool.false_eq_true, ite_false]; omega
    simp only [hn, ite_true]
    rfl

/-- The twin's `internForallEE` is `EStore.internLam` when the new store's `forallE` tables have at most `2^26` rows. -/
theorem internForallEE_eq (s : AState) (ty b : EIdx)
    (hP : (s.store.internForallE ty b).1.pers.foralls.size ≤ 2 ^ 26)
    (hS : (s.store.internForallE ty b).1.scr.foralls.size ≤ 2 ^ 26) :
    internForallEE ty b s = .ok ((s.store.internForallE ty b).2, { s with store := (s.store.internForallE ty b).1 }) := by
  have hint := estore_internForallE s.store ty b
  simp only at hint
  show (match s.store.findBind ETag.forallE ty b with
    | some h => (pure h : AM EIdx)
    | none => do
      let n := if s.store.scratchOn then s.store.scr.bindSizeOf ETag.forallE else s.store.pers.bindSizeOf ETag.forallE
      if n < Idx.idxCap then do
        let st := s.store
        let s := { s with store := EStore.empty }
        let (st, h) := st.internForallE ty b
        set { s with store := st }
        pure h
      else
        fail (.native "arena: expression constructor array full")) s = _
  have e1 : (if s.store.scratchOn && EStore.bindHasScratchChild ty b then none else s.store.pers.foralls.find? ⟨ty, b⟩) =
      s.store.persFindBindMaybe ETag.forallE ⟨ty, b⟩ := by
    simp only [EStore.persFindBindMaybe, ETables.findBind, show (ETag.forallE == ETag.lam) = false from rfl, show (ETag.forallE == ETag.forallE) = true from rfl, Bool.false_eq_true, ite_false, ite_true]
    cases s.store.scratchOn <;> simp
  cases hf : s.store.findBind ETag.forallE ty b with
  | some h =>
    rw [hint]
    simp only [EStore.findBind] at hf
    cases hpm : s.store.persFindBindMaybe ETag.forallE ⟨ty, b⟩ with
    | some h' =>
      rw [hpm] at hf; simp at hf; subst hf
      rw [twoTier_hitP _ _ _ _ _ _ _ _ _ (by rw [e1, hpm])]; rfl
    | none =>
      rw [hpm] at hf; simp only at hf
      by_cases hon : s.store.scratchOn = true
      · rw [hon] at hf; simp only [ite_true, ETables.findBind, show (ETag.forallE == ETag.lam) = false from rfl, show (ETag.forallE == ETag.forallE) = true from rfl, Bool.false_eq_true, ite_false] at hf
        rw [twoTier_hitS _ _ _ _ hon _ _ _ _ _ (by rw [e1, hpm]) hf]; rfl
      · rw [show s.store.scratchOn = false by simpa using hon] at hf; simp at hf
  | none =>
    have hn : (if s.store.scratchOn then s.store.scr.bindSizeOf ETag.forallE else s.store.pers.bindSizeOf ETag.forallE) <
        Idx.idxCap := by
      simp only [EStore.findBind] at hf
      cases hpm : s.store.persFindBindMaybe ETag.forallE ⟨ty, b⟩ with
      | some _ => rw [hpm] at hf; simp at hf
      | none =>
        rw [hpm] at hf; simp only at hf
        have h2 : s.store.scratchOn = true → s.store.scr.foralls.find? ⟨ty, b⟩ = none := by
          intro hon; rw [hon] at hf; simpa [ETables.findBind, show (ETag.forallE == ETag.lam) = false from rfl, show (ETag.forallE == ETag.forallE) = true from rfl] using hf
        have T := twoTier_miss_size s.store.pers.foralls s.store.scr.foralls s.store.scratchOn
          (EStore.bindHasScratchChild ty b) ⟨ty, b⟩ (s.store.derOfBindAt 23 ty b) (mkN ETag.forallE 0) (mkN ETag.forallE 1)
          (by rw [e1, hpm]) h2
        rw [hint] at hP hS
        simp only at hP hS
        show (if s.store.scratchOn then s.store.scr.foralls.nodes.size else s.store.pers.foralls.nodes.size) < 67108864
        cases hon : s.store.scratchOn with
        | true =>
          have := T.1 hon
          simp only [Tbl.size] at this hS
          simp only [ite_true]; omega
        | false =>
          have := T.2 hon
          simp only [Tbl.size] at this hP
          simp only [Bool.false_eq_true, ite_false]; omega
    simp only [hn, ite_true]
    rfl


/-! ## Two-child intern functions, generically -/

/-- A two-child intern function's body: the prologue, then the shared intern program at kind `k`. -/
def bin2Body (E : ExpHOL 64) (k : Nat) : ProgHOL 64 := prologue bin2Scratch (eBin2With E (eRest k 2))

theorem bin2_body_spec (C : Ctx) (hok : CtxOK C) (E : ExpHOL 64) (k : Nat) (op : EIdx → EIdx → AM EIdx)
    (res : EStore → EIdx → EIdx → EStore × EIdx)
    (hspec : ∀ (t : PState σ) (st : EStore) (f a : EIdx), SRep t C.L C.FLn C.FLl C.FLs C.FLe st →
      t.memaddrs C.KB ∧ t.memaddrs (C.KB + 8) →
      t.locals.lookup lKb = some (.val (.word C.KB)) → t.locals.lookup lEf = some (.val (.word (Enc.idxW f))) →
      t.locals.lookup lEa = some (.val (.word (Enc.idxW a))) → t.locals.lookup lDir = some (.val (.word C.L.DIR)) →
      t.locals.lookup lFle = some (.val (.word C.FLe)) →
      (∀ y, y ∈ bin2Scratch → ∃ w, t.locals.lookup y = some (.val (.word w))) →
      ERes t C.L C.FLn C.FLl C.FLs C.FLe C.KB 2 st (res st f a) (evaluateHOLFiniteState t (eBin2With E (eRest k 2))))
    (hwrap : ∀ (s : AState) (f a : EIdx) (t : PState σ), SRep t C.L C.FLn C.FLl C.FLs C.FLe (res s.store f a).1 →
      op f a s = .ok ((res s.store f a).2, { s with store := (res s.store f a).1 }))
    (s : AState) (f a : EIdx) :
    SpecR (Pre (σ := σ) C s [(lEf, Enc.idxW f), (lEa, Enc.idxW a)]) (bin2Body E k) s (op f a) (PostE C) := by
  refine specR_prologue (postE_locals C) (fun x hx => ?_) ?_
  · simp only [bin2Scratch, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  intro t ht
  have hw : ∀ y, y ∈ bin2Scratch → ∃ w, t.locals.lookup y = some (.val (.word w)) :=
    fun y hy => ht.decl y (List.mem_append_right _ hy)
  rcases hspec t s.store f a ht.sr.rep
      ⟨by simpa using ht.sr.kbuf 0 (by decide), by simpa using ht.sr.kbuf 1 (by decide)⟩
      (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) hw with
    hs | ⟨hr, hsr, hc, hg, hd, _, hm⟩
  · exact Or.inl hs
  right
  refine ⟨_, hr, (res s.store f a).2, { s with store := (res s.store f a).1 }, hwrap s f a _ hsr, rfl, ?_⟩
  exact ⟨hsr, by rw [hg]; exact ht.sr.gdir, by rw [hg]; exact ht.sr.gfln, by rw [hg]; exact ht.sr.gfll,
    by rw [hg]; exact ht.sr.gfls, by rw [hg]; exact ht.sr.gfle, by rw [hg]; exact ht.sr.gkb,
    by rw [hc]; exact ht.sr.code, fun j hj => by rw [hd]; exact ht.sr.kbuf j hj,
    fun mk => memoAt_frame (ht.sr.memo mk)
        (fun c hc => hm c (hok.memoOut (.e mk) c hc) (fun j hj e => hok.kbMemo (.e mk) j (by omega) (e ▸ hc)))
        (fun k hk => hm _ (hok.mdescOut (.e mk) k hk) (fun j hj => hok.kbMdesc (.e mk) k j hk (by omega))) hd,
      fun mk => memoAtN_frame (ht.sr.memoN mk)
        (fun c hc => hm c (hok.memoOut (.n mk) c hc) (fun j hj e => hok.kbMemo (.n mk) j (by omega) (e ▸ hc)))
        (fun k hk => hm _ (hok.mdescOut (.n mk) k hk) (fun j hj => hok.kbMdesc (.n mk) k j hk (by omega))) hd,
      fun mk => cacheAt_frame (ht.sr.cache mk)
        (fun c hc => hm c (hok.memoOut (.c mk) c hc) (fun j hj e => hok.kbMemo (.c mk) j (by omega) (e ▸ hc)))
        (fun k hk => hm _ (hok.mdescOut (.c mk) k hk) (fun j hj => hok.kbMdesc (.c mk) k j hk (by omega))) hd,
      modeAt_frame ht.sr.mode
        (fun b mk c hc => hm c (hok.memoOut (.m b mk) c hc) (fun j hj e => hok.kbMemo (.m b mk) j (by omega) (e ▸ hc)))
        (fun b mk k hk => hm _ (hok.mdescOut (.m b mk) k hk) (fun j hj => hok.kbMdesc (.m b mk) k j hk (by omega))) hd (by first | rfl | (rw [hg]) | (rw [hg']) | (rw [hgl _ (by decide)]) | simp_all),
      envAt_frame ht.sr.env
        (fun b c hc => hm c (hok.memoOut (envR b) c hc) (fun j hj e => hok.kbMemo (envR b) j (by omega) (e ▸ hc)))
        (fun b k hk => hm _ (hok.mdescOut (envR b) k hk) (fun j hj => hok.kbMdesc (envR b) k j hk (by omega)))
        (fun i hi => hm _ (hok.envOut i hi) (fun j hj => hok.kbEnv i j hi (by omega))) hd ⟨(by first | rfl | (rw [hg]) | (rw [hg']) | (rw [hgl _ (by decide)]) | simp_all), (by first | rfl | (rw [hg]) | (rw [hg']) | (rw [hgl _ (by decide)]) | simp_all)⟩, ht.sr.pins,
      heapEx_frame ht.sr.heap (fun i hi => hm _ (hok.heapOut i hi) (fun j hj => hok.kbHeap i j hi (by omega))) hd
        (by rw [hg])⟩

/-- In a caller: `x := fn(e₁, e₂); rest` against `op f a >>= k`, for a two-child intern function `fn`. -/
theorem specR_bin2I {β : Type} {C : Ctx} (hok : CtxOK C) (fn : MlS) (E : ExpHOL 64) (kk : Nat)
    (op : EIdx → EIdx → AM EIdx) (res : EStore → EIdx → EIdx → EStore × EIdx)
    (hspec : ∀ (t : PState σ) (st : EStore) (f a : EIdx), SRep t C.L C.FLn C.FLl C.FLs C.FLe st →
      t.memaddrs C.KB ∧ t.memaddrs (C.KB + 8) →
      t.locals.lookup lKb = some (.val (.word C.KB)) → t.locals.lookup lEf = some (.val (.word (Enc.idxW f))) →
      t.locals.lookup lEa = some (.val (.word (Enc.idxW a))) → t.locals.lookup lDir = some (.val (.word C.L.DIR)) →
      t.locals.lookup lFle = some (.val (.word C.FLe)) →
      (∀ y, y ∈ bin2Scratch → ∃ w, t.locals.lookup y = some (.val (.word w))) →
      ERes t C.L C.FLn C.FLl C.FLs C.FLe C.KB 2 st (res st f a) (evaluateHOLFiniteState t (eBin2With E (eRest kk 2))))
    (hwrap : ∀ (s : AState) (f a : EIdx) (t : PState σ), SRep t C.L C.FLn C.FLl C.FLs C.FLe (res s.store f a).1 →
      op f a s = .ok ((res s.store f a).2, { s with store := (res s.store f a).1 }))
    (hcode : C.code.lookup fn = some ([(lEf, .one), (lEa, .one)], bin2Body E kk, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k : EIdx → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x : MlS) (e1 e2 : ExpHOL 64) (f a : EIdx) (hx : x ∈ D)
    (he1 : sev Γ e1 = some (Enc.idxW f)) (he2 : sev Γ e2 = some (Enc.idxW a))
    (hk : ∀ h s', SpecR (Inv C s' ((x, Enc.idxW h) :: Γ) [] D) rest s' (k h) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) fn [e1, e2]) rest) s (op f a >>= k) R :=
  specR_call2I x fn lEf lEa (by decide) e1 e2 (bin2Body E kk) (Enc.idxW f) (Enc.idxW a) hx hcode he1 he2
    (PostE C) (fun _ _ _ _ hp => hp.2)
    (fun u hu h1 h2 v hv => by
      subst hv
      exact bin2_body_spec C hok E kk op res hspec hwrap s f a _ ⟨hu, fun y w hy => by
        simp only [Env.get] at hy
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact h1
        · split at hy
          · rename_i e; subst e; simp at hy; subst hy; exact h2
          · simp at hy⟩)
    (fun h w s' st hp => by obtain ⟨rfl, _⟩ := hp; exact hk h s')

def fInternLam := ofString "internLam"
def fInternForallE := ofString "internForallE"

theorem specR_internLamI {β : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} (hok : CtxOK C)
    (hcode : C.code.lookup fInternLam = some ([(lEf, .one), (lEa, .one)], bin2Body lamDataE 14, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k : EIdx → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x : MlS) (e1 e2 : ExpHOL 64) (ty b : EIdx) (hx : x ∈ D)
    (he1 : sev Γ e1 = some (Enc.idxW ty)) (he2 : sev Γ e2 = some (Enc.idxW b))
    (hk : ∀ h s', SpecR (Inv C s' ((x, Enc.idxW h) :: Γ) [] D) rest s' (k h) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) fInternLam [e1, e2]) rest) s
      (internLamE ty b >>= k) R :=
  specR_bin2I hok fInternLam lamDataE 14 internLamE (fun st f a => st.internLam f a)
    (fun t st f a hR kbd lkb lef lea ldir lfle hw =>
      eInternLam_spec ra t C.L C.FLn C.FLl C.FLs C.FLe C.KB st f a hR hok.sepLam kbd (kb_ne_kb8 _) hok.b0Lam hok.b1Lam
        lkb lef lea ldir lfle hw)
    (fun s f a t hsr => internLamE_eq s f a (Nat.le_trans (tabAt_size_le hsr.e.p5) (hok.sepLam.cap 0 (by decide)))
      (Nat.le_trans (tabAt_size_le hsr.e.s5) (hok.sepLam.cap 1 (by decide))))
    hcode x e1 e2 ty b hx he1 he2 hk

theorem specR_internForallEI {β : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} (hok : CtxOK C)
    (hcode : C.code.lookup fInternForallE = some ([(lEf, .one), (lEa, .one)], bin2Body forDataE 15, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k : EIdx → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x : MlS) (e1 e2 : ExpHOL 64) (ty b : EIdx) (hx : x ∈ D)
    (he1 : sev Γ e1 = some (Enc.idxW ty)) (he2 : sev Γ e2 = some (Enc.idxW b))
    (hk : ∀ h s', SpecR (Inv C s' ((x, Enc.idxW h) :: Γ) [] D) rest s' (k h) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) fInternForallE [e1, e2]) rest) s
      (internForallEE ty b >>= k) R :=
  specR_bin2I hok fInternForallE forDataE 15 internForallEE (fun st f a => st.internForallE f a)
    (fun t st f a hR kbd lkb lef lea ldir lfle hw =>
      eInternForallE_spec ra t C.L C.FLn C.FLl C.FLs C.FLe C.KB st f a hR hok.sepFor kbd (kb_ne_kb8 _) hok.b0For
        hok.b1For lkb lef lea ldir lfle hw)
    (fun s f a t hsr => internForallEE_eq s f a (Nat.le_trans (tabAt_size_le hsr.e.p6) (hok.sepFor.cap 0 (by decide)))
      (Nat.le_trans (tabAt_size_le hsr.e.s6) (hok.sepFor.cap 1 (by decide))))
    hcode x e1 e2 ty b hx he1 he2 hk

/-! ## The `letE` intern function -/

def fInternLet := ofString "internLet"
def letBody : ProgHOL 64 := prologue letScratch (eLetWith (eRest 16 3))

theorem kb3_ne (KB : BitVec 64) : KB ≠ KB + 8 ∧ KB ≠ KB + 16 ∧ KB + 8 ≠ KB + 16 := by
  refine ⟨kb_ne_kb8 KB, fun h => ?_, fun h => ?_⟩
  · have := congrArg BitVec.toNat h; simp only [BitVec.toNat_add] at this
    have hk := KB.isLt; have e : (16 : BitVec 64).toNat = 16 := rfl; rw [e] at this; omega
  · have := congrArg BitVec.toNat h; simp only [BitVec.toNat_add] at this
    have hk := KB.isLt; have e8 : (8 : BitVec 64).toNat = 8 := rfl; have e : (16 : BitVec 64).toNat = 16 := rfl
    rw [e8, e] at this; omega

theorem let_body_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (s : AState)
    (ty v b : EIdx) :
    SpecR (Pre (σ := σ) C s [(lEty, Enc.idxW ty), (lEvl, Enc.idxW v), (lEbd, Enc.idxW b)]) letBody s
      (internLetEE ty v b) (PostE C) := by
  refine specR_prologue (postE_locals C) (fun x hx => ?_) ?_
  · simp only [letScratch, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  intro t ht
  have hw : ∀ y, y ∈ letScratch → ∃ w, t.locals.lookup y = some (.val (.word w)) :=
    fun y hy => ht.decl y (List.mem_append_right _ hy)
  rcases eInternLet_spec ra t C.L C.FLn C.FLl C.FLs C.FLe C.KB s.store ty v b ht.sr.rep hok.sepLet
      ⟨by simpa using ht.sr.kbuf 0 (by decide), by simpa using ht.sr.kbuf 1 (by decide),
        by simpa using ht.sr.kbuf 2 (by decide)⟩ (kb3_ne C.KB) hok.b0Let hok.b1Let
      (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) hw with
    hs | ⟨hr, hsr, hc, hg, hd, _, hm⟩
  · exact Or.inl hs
  right
  refine ⟨_, hr, (s.store.intern (.letE ty v b)).2, { s with store := (s.store.intern (.letE ty v b)).1 }, ?_, rfl, ?_⟩
  · show internNodeE (.letE ty v b) s = _
    exact internNodeE_letE s ty v b
      (Nat.le_trans (tabAt_size_le hsr.e.p7) (hok.sepLet.cap 0 (by decide)))
      (Nat.le_trans (tabAt_size_le hsr.e.s7) (hok.sepLet.cap 1 (by decide)))
  · exact ⟨hsr, by rw [hg]; exact ht.sr.gdir, by rw [hg]; exact ht.sr.gfln, by rw [hg]; exact ht.sr.gfll,
      by rw [hg]; exact ht.sr.gfls, by rw [hg]; exact ht.sr.gfle, by rw [hg]; exact ht.sr.gkb,
      by rw [hc]; exact ht.sr.code, fun j hj => by rw [hd]; exact ht.sr.kbuf j hj,
      fun mk => memoAt_frame (ht.sr.memo mk)
        (fun c hc => hm c (hok.memoOut (.e mk) c hc) (fun j hj e => hok.kbMemo (.e mk) j (by omega) (e ▸ hc)))
        (fun k hk => hm _ (hok.mdescOut (.e mk) k hk) (fun j hj => hok.kbMdesc (.e mk) k j hk (by omega))) hd,
      fun mk => memoAtN_frame (ht.sr.memoN mk)
        (fun c hc => hm c (hok.memoOut (.n mk) c hc) (fun j hj e => hok.kbMemo (.n mk) j (by omega) (e ▸ hc)))
        (fun k hk => hm _ (hok.mdescOut (.n mk) k hk) (fun j hj => hok.kbMdesc (.n mk) k j hk (by omega))) hd,
      fun mk => cacheAt_frame (ht.sr.cache mk)
        (fun c hc => hm c (hok.memoOut (.c mk) c hc) (fun j hj e => hok.kbMemo (.c mk) j (by omega) (e ▸ hc)))
        (fun k hk => hm _ (hok.mdescOut (.c mk) k hk) (fun j hj => hok.kbMdesc (.c mk) k j hk (by omega))) hd,
      modeAt_frame ht.sr.mode
        (fun b mk c hc => hm c (hok.memoOut (.m b mk) c hc) (fun j hj e => hok.kbMemo (.m b mk) j (by omega) (e ▸ hc)))
        (fun b mk k hk => hm _ (hok.mdescOut (.m b mk) k hk) (fun j hj => hok.kbMdesc (.m b mk) k j hk (by omega))) hd (by first | rfl | (rw [hg]) | (rw [hg']) | (rw [hgl _ (by decide)]) | simp_all),
      envAt_frame ht.sr.env
        (fun b c hc => hm c (hok.memoOut (envR b) c hc) (fun j hj e => hok.kbMemo (envR b) j (by omega) (e ▸ hc)))
        (fun b k hk => hm _ (hok.mdescOut (envR b) k hk) (fun j hj => hok.kbMdesc (envR b) k j hk (by omega)))
        (fun i hi => hm _ (hok.envOut i hi) (fun j hj => hok.kbEnv i j hi (by omega))) hd ⟨(by first | rfl | (rw [hg]) | (rw [hg']) | (rw [hgl _ (by decide)]) | simp_all), (by first | rfl | (rw [hg]) | (rw [hg']) | (rw [hgl _ (by decide)]) | simp_all)⟩, ht.sr.pins,
      heapEx_frame ht.sr.heap (fun i hi => hm _ (hok.heapOut i hi) (fun j hj => hok.kbHeap i j hi (by omega))) hd
        (by rw [hg])⟩

theorem specR_internLetI {β : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} (hok : CtxOK C)
    (hcode : C.code.lookup fInternLet = some ([(lEty, .one), (lEvl, .one), (lEbd, .one)], letBody, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k : EIdx → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x : MlS) (e1 e2 e3 : ExpHOL 64) (ty v b : EIdx) (hx : x ∈ D)
    (he1 : sev Γ e1 = some (Enc.idxW ty)) (he2 : sev Γ e2 = some (Enc.idxW v)) (he3 : sev Γ e3 = some (Enc.idxW b))
    (hk : ∀ h s', SpecR (Inv C s' ((x, Enc.idxW h) :: Γ) [] D) rest s' (k h) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) fInternLet [e1, e2, e3]) rest) s
      (internLetEE ty v b >>= k) R :=
  specR_call3IM x fInternLet lEty lEvl lEbd (by decide) (by decide) (by decide) e1 e2 e3 letBody (Enc.idxW ty)
    (Enc.idxW v) (Enc.idxW b) hx hcode he1 he2 he3 (PostE C) (fun _ _ _ _ hp => hp.2)
    (fun u hu _ h1 h2 h3 w hw => by
      subst hw
      exact let_body_spec ra C hok s ty v b _ ⟨hu, fun y w hy => by
        simp only [Env.get] at hy
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact h1
        · split at hy
          · rename_i e; subst e; simp at hy; subst hy; exact h2
          · split at hy
            · rename_i e; subst e; simp at hy; subst hy; exact h3
            · simp at hy⟩)
    (fun h w s' st hp => by obtain ⟨rfl, _⟩ := hp; exact hk h s')

/-! ## The `bvar` intern function -/

theorem sepK_mono {L : Layout} {FLn FLl FLs FLe KB : BitVec 64} {w w' k : Nat} (h : SepK L FLn FLl FLs FLe KB w k)
    (hw : w' ≤ w) : SepK L FLn FLl FLs FLe KB w' k :=
  ⟨h.pow, h.cap, h.dis, h.oth, fun k' tier m h1 h2 h3 => ⟨(h.dsc k' tier m h1 h2 h3).1, (h.dsc k' tier m h1 h2 h3).2.1,
    fun j hj => (h.dsc k' tier m h1 h2 h3).2.2 j (by omega)⟩,
    fun F hF => ⟨(h.fls F hF).1, (h.fls F hF).2.1, fun j hj => (h.fls F hF).2.2 j (by omega)⟩,
    fun j k' tier hj h1 h2 => h.kbo j k' tier (by omega) h1 h2⟩

def fInternBVar := ofString "internBVar"
def bvarLocals : List MlS := lEn :: bvarScratch

/-- `internBVar(iw)`: the key `limbs i` (one word, or none for `0`) to the key buffer, its length, then
the intern program at kind 9. -/
def bvarBody : ProgHOL 64 :=
  prologue bvarLocals (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) (vv lIw))
    (.seq (.assign .local lEn (.cmp .notEqual (vv lIw) (.const 0))) (eBVarWith (rRestE 9 (vv lEn) lFle))))

theorem encBVar_small (i : Nat) (hi : i < 2 ^ 64) :
    Enc.encBVar ⟨i⟩ = if i = 0 then [] else [BitVec.ofNat 64 i] := limbs_small i hi

theorem bvar_body_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (s : AState) (i : Nat)
    (hi : i < 2 ^ 63) :
    SpecR (Pre (σ := σ) C s [(lIw, BitVec.ofNat 64 i)]) bvarBody s (internBVarE i) (PostE C) := by
  have hlen : (Enc.encBVar ⟨i⟩).length ≤ 1 := by rw [encBVar_small i (by omega)]; split <;> simp
  have hlenW : (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .notEqual (BitVec.ofNat 64 i) 0 then (1 : BitVec 64)
      else 0) = BitVec.ofNat 64 (Enc.encBVar ⟨i⟩).length := by
    rw [encBVar_small i (by omega)]
    by_cases h0 : i = 0
    · subst h0; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    · have : BitVec.ofNat 64 i ≠ 0#64 := by intro e; have := congrArg BitVec.toNat e; simp at this; omega
      simp [h0, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]
  refine specR_prologue (postE_locals C) (fun x hx => ?_) ?_
  · simp only [bvarLocals, bvarScratch, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  refine specR_storeKBI hok 0 (by decide) (vv lIw) (BitVec.ofNat 64 i) rfl rfl ?_
  refine specR_assignI lEn _ (BitVec.ofNat 64 (Enc.encBVar ⟨i⟩).length) (by decide) (by rw [← hlenW]; rfl) ?_
  intro t ht
  have hw : ∀ y, y ∈ bvarScratch → ∃ w, t.locals.lookup y = some (.val (.word w)) :=
    fun y hy => ht.decl y (List.mem_append_right _ (List.mem_cons_of_mem _ hy))
  have hK : Words t C.KB (Enc.encBVar ⟨i⟩) := by
    intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    have h0 : i ≠ 0 := by intro e; subst e; simp [Enc.encBVar, Enc.limbs] at hj
    have e0 : (Enc.encBVar ⟨i⟩)[0]'hj = BitVec.ofNat 64 i := by
      simp only [encBVar_small i (by omega), h0, ite_false]; rfl
    rw [e0]; exact ht.mem _ _ (by simp)
  rcases eInternBVar_spec ra t C.L C.FLn C.FLl C.FLs C.FLe C.KB s.store i hi ht.sr.rep
      (sepK_mono hok.sepBVar (by omega)) hK (by omega) hok.b0BVar hok.b1BVar (ht.env _ _ rfl) (ht.env _ _ rfl)
      (ht.env _ _ rfl) (ht.env _ _ rfl) (ht.env _ _ rfl) hw with
    hs | ⟨hr, hsr, hc, hg, hd, _, hm⟩
  · exact Or.inl hs
  right
  refine ⟨_, hr, (s.store.intern (.bvar i)).2, { s with store := (s.store.intern (.bvar i)).1 }, ?_, rfl, ?_⟩
  · show internNodeE (.bvar i) s = _
    exact internNodeE_bvar s i
      (Nat.le_trans (tabAt_size_le hsr.e.p0) (hok.sepBVar.cap 0 (by decide)))
      (Nat.le_trans (tabAt_size_le hsr.e.s0) (hok.sepBVar.cap 1 (by decide)))
  · exact ⟨hsr, by rw [hg]; exact ht.sr.gdir, by rw [hg]; exact ht.sr.gfln, by rw [hg]; exact ht.sr.gfll,
      by rw [hg]; exact ht.sr.gfls, by rw [hg]; exact ht.sr.gfle, by rw [hg]; exact ht.sr.gkb,
      by rw [hc]; exact ht.sr.code, fun j hj => by rw [hd]; exact ht.sr.kbuf j hj,
      fun mk => memoAt_frame (ht.sr.memo mk)
        (fun c hc => hm c (hok.memoOut (.e mk) c hc) (fun j hj e => hok.kbMemo (.e mk) j (by omega) (e ▸ hc)))
        (fun k hk => hm _ (hok.mdescOut (.e mk) k hk) (fun j hj => hok.kbMdesc (.e mk) k j hk (by omega))) hd,
      fun mk => memoAtN_frame (ht.sr.memoN mk)
        (fun c hc => hm c (hok.memoOut (.n mk) c hc) (fun j hj e => hok.kbMemo (.n mk) j (by omega) (e ▸ hc)))
        (fun k hk => hm _ (hok.mdescOut (.n mk) k hk) (fun j hj => hok.kbMdesc (.n mk) k j hk (by omega))) hd,
      fun mk => cacheAt_frame (ht.sr.cache mk)
        (fun c hc => hm c (hok.memoOut (.c mk) c hc) (fun j hj e => hok.kbMemo (.c mk) j (by omega) (e ▸ hc)))
        (fun k hk => hm _ (hok.mdescOut (.c mk) k hk) (fun j hj => hok.kbMdesc (.c mk) k j hk (by omega))) hd,
      modeAt_frame ht.sr.mode
        (fun b mk c hc => hm c (hok.memoOut (.m b mk) c hc) (fun j hj e => hok.kbMemo (.m b mk) j (by omega) (e ▸ hc)))
        (fun b mk k hk => hm _ (hok.mdescOut (.m b mk) k hk) (fun j hj => hok.kbMdesc (.m b mk) k j hk (by omega))) hd (by first | rfl | (rw [hg]) | (rw [hg']) | (rw [hgl _ (by decide)]) | simp_all),
      envAt_frame ht.sr.env
        (fun b c hc => hm c (hok.memoOut (envR b) c hc) (fun j hj e => hok.kbMemo (envR b) j (by omega) (e ▸ hc)))
        (fun b k hk => hm _ (hok.mdescOut (envR b) k hk) (fun j hj => hok.kbMdesc (envR b) k j hk (by omega)))
        (fun i hi => hm _ (hok.envOut i hi) (fun j hj => hok.kbEnv i j hi (by omega))) hd ⟨(by first | rfl | (rw [hg]) | (rw [hg']) | (rw [hgl _ (by decide)]) | simp_all), (by first | rfl | (rw [hg]) | (rw [hg']) | (rw [hgl _ (by decide)]) | simp_all)⟩, ht.sr.pins,
      heapEx_frame ht.sr.heap (fun i hi => hm _ (hok.heapOut i hi) (fun j hj => hok.kbHeap i j hi (by omega))) hd
        (by rw [hg])⟩

theorem specR_internBVarI {β : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} (hok : CtxOK C)
    (hcode : C.code.lookup fInternBVar = some ([(lIw, .one)], bvarBody, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k : EIdx → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x : MlS) (e1 : ExpHOL 64) (i : Nat) (hi : i < 2 ^ 63)
    (hx : x ∈ D) (he1 : sev Γ e1 = some (BitVec.ofNat 64 i))
    (hk : ∀ h s', SpecR (Inv C s' ((x, Enc.idxW h) :: Γ) [] D) rest s' (k h) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) fInternBVar [e1]) rest) s
      (internBVarE i >>= k) R := by
  intro t ht
  have hc := spec_call1 (P := (· = t)) (s := s) (m := internBVarE i)
    (Q := fun a s' t' => ∃ w st, PostE C a w s' st ∧ Inv C s' ((x, w) :: Γ) [] D t')
    x fInternBVar lIw e1 bvarBody (fun _ => BitVec.ofNat 64 i) (fun u hu => by rw [hu, ht.sr.code]; exact hcode)
    (fun u hu => by rw [hu]; exact inv_ev ht he1) (fun u hu => by rw [hu]; exact ht.decl x hx) (fun _ => PostE C)
    (fun u hu callee h1 v hv => by
      subst hu hv
      exact bvar_body_spec ra C hok s i hi _ ⟨sr_of_eq ht.sr rfl rfl rfl rfl, fun y w hy => by
        simp only [Env.get] at hy
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact h1
        · simp at hy⟩)
    (fun u hu a w s' st hp => by
      subst hu
      refine ⟨w, st, hp, ⟨sr_of_eq hp.2 rfl rfl rfl rfl, fun y v hy => ?_, fun _ _ h => absurd h (by simp),
        fun y hy => ?_⟩⟩
      · simp only [setKvarHOLFinite, Env.get] at hy ⊢
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact lookup_setVar_same _ _ _
        · rename_i e; rw [lookup_setVar_other _ _ e]; exact ht.env y v hy
      · simp only [setKvarHOLFinite]
        by_cases e : y = x
        · subst e; exact ⟨w, lookup_setVar_same _ _ _⟩
        · rw [lookup_setVar_other _ _ e]; exact ht.decl y hy)
  exact specR_bind (Q1 := fun a s' t' => ∃ w st, PostE C a w s' st ∧ Inv C s' ((x, w) :: Γ) [] D t') hc
    (fun a s' u ⟨w, st, hp, hu⟩ => by obtain ⟨rfl, _⟩ := hp; exact hk a s' u hu) t rfl

/-! ## Three key words, and the `proj` intern function -/

theorem kb_word_ne (KB : BitVec 64) (i j : Nat) (hi : i < 3) (hj : j < 3) (hij : i ≠ j) :
    KB + BitVec.ofNat 64 (8 * i) ≠ KB + BitVec.ofNat 64 (8 * j) := by
  intro h
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
  have hk := KB.isLt
  rw [Nat.mod_eq_of_lt (a := 8 * i) (by omega), Nat.mod_eq_of_lt (a := 8 * j) (by omega)] at this
  omega

theorem specR_storeKB3I {α : Type} {C : Ctx} (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (e0 e1 e2 : ExpHOL 64) (w0 w1 w2 : BitVec 64) (he0 : sev Γ e0 = some w0) (he1 : sev Γ e1 = some w1)
    (he2 : sev Γ e2 = some w2) (hkb : Γ.get lKb = some C.KB)
    (h : SpecR (Inv C s Γ [(C.KB + BitVec.ofNat 64 (8 * 0), w0), (C.KB + BitVec.ofNat 64 (8 * 1), w1),
      (C.KB + BitVec.ofNat 64 (8 * 2), w2)] D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) e0)
      (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 1))]) e1)
        (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 2))]) e2) rest))) s m R := by
  refine specR_storeKB2I hok e0 e1 w0 w1 he0 he1 hkb ?_
  refine specR_seq (fun t ht => ?_) h
  have hdom : t.memaddrs (C.KB + BitVec.ofNat 64 (8 * 2)) := ht.sr.kbuf 2 (by decide)
  rw [store_word t _ e2 _ w2 (eval_add2 t _ _ _ _ (eval_vv t lKb _ (ht.env _ _ hkb)) (eval_const t _))
    (inv_ev ht he2) hdom]
  refine Or.inr ⟨rfl, sr_storeKB hok ht.sr 2 (by decide) w2, fun y v hy => ht.env y v hy, fun a v ha => ?_, ht.decl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ha
  rcases ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨h1, h2⟩ := ht.mem _ _ (List.mem_cons_self ..)
    exact ⟨h1, by simp only; rw [if_neg (kb_word_ne C.KB 0 2 (by decide) (by decide) (by decide))]; exact h2⟩
  · obtain ⟨h1, h2⟩ := ht.mem _ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    exact ⟨h1, by simp only; rw [if_neg (kb_word_ne C.KB 1 2 (by decide) (by decide) (by decide))]; exact h2⟩
  · exact ⟨hdom, by simp⟩

def fInternProj := ofString "internProj"
def projLocals : List MlS := lEn :: projScratch

def projBody : ProgHOL 64 :=
  prologue projLocals (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 0))]) (vv lEp))
    (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 1))]) (vv lEe))
      (.seq (.store (.op .add [vv lKb, .const (BitVec.ofNat 64 (8 * 2))]) (vv lIw))
        (.seq (.assign .local lEn (.op .add [.const 2, .cmp .notEqual (vv lIw) (.const 0)]))
          (eProjWith (rRestE 18 (vv lEn) lFle))))))

theorem proj_body_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (s : AState)
    (n : NIdx) (i : Nat) (e : EIdx) (hi : i < 2 ^ 63) :
    SpecR (Pre (σ := σ) C s [(lEp, Enc.idxW n), (lEe, Enc.idxW e), (lIw, BitVec.ofNat 64 i)]) projBody s
      (internProjE n i e) (PostE C) := by
  have hlimb := limbs_small i (by omega)
  have hlen : (Enc.encProj ⟨n, i, e⟩).length ≤ 3 := by
    simp only [Enc.encProj, List.length_cons, hlimb]; split <;> simp
  have hlenW : (2 : BitVec 64) + (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .notEqual (BitVec.ofNat 64 i) 0 then
      (1 : BitVec 64) else 0) = BitVec.ofNat 64 (Enc.encProj ⟨n, i, e⟩).length := by
    simp only [Enc.encProj, List.length_cons, hlimb]
    by_cases h0 : i = 0
    · subst h0; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    · have : BitVec.ofNat 64 i ≠ 0#64 := by intro e; have := congrArg BitVec.toNat e; simp at this; omega
      simp [h0, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]
  refine specR_prologue (postE_locals C) (fun x hx => ?_) ?_
  · simp only [projLocals, projScratch, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  refine specR_storeKB3I hok (vv lEp) (vv lEe) (vv lIw) (Enc.idxW n) (Enc.idxW e) (BitVec.ofNat 64 i) rfl rfl rfl rfl ?_
  refine specR_assignI lEn _ (BitVec.ofNat 64 (Enc.encProj ⟨n, i, e⟩).length) (by decide) (by rw [← hlenW]; rfl) ?_
  intro t ht
  have hw : ∀ y, y ∈ projScratch → ∃ w, t.locals.lookup y = some (.val (.word w)) :=
    fun y hy => ht.decl y (List.mem_append_right _ (List.mem_cons_of_mem _ hy))
  have hK : Words t C.KB (Enc.encProj ⟨n, i, e⟩) := by
    intro j hj
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl
    · have e0 : (Enc.encProj ⟨n, i, e⟩)[0]'hj = Enc.idxW n := rfl
      rw [e0]; exact ht.mem _ _ (List.mem_cons_self ..)
    · have e1 : (Enc.encProj ⟨n, i, e⟩)[1]'hj = Enc.idxW e := rfl
      rw [e1]; exact ht.mem _ _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · have h0 : i ≠ 0 := by intro h0; subst h0; simp [Enc.encProj, Enc.limbs] at hj
      have e2 : (Enc.encProj ⟨n, i, e⟩)[2]'hj = BitVec.ofNat 64 i := by
        simp only [Enc.encProj, hlimb, h0, ite_false]; rfl
      rw [e2]; exact ht.mem _ _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
  rcases eInternProj_spec ra t C.L C.FLn C.FLl C.FLs C.FLe C.KB s.store n i e ht.sr.rep
      (sepK_mono hok.sepProj hlen) hK (by omega) hok.b0Proj hok.b1Proj (ht.env _ _ rfl) (ht.env _ _ rfl)
      (ht.env _ _ rfl) (ht.env _ _ rfl) (by rw [ht.env _ _ rfl]; rfl) (ht.env _ _ rfl) (ht.env _ _ rfl)
      (ht.env _ _ rfl) hw with
    hs | ⟨hr, hsr, hc, hg, hd, _, hm⟩
  · exact Or.inl hs
  right
  refine ⟨_, hr, (s.store.intern (.proj n i e)).2, { s with store := (s.store.intern (.proj n i e)).1 }, ?_, rfl, ?_⟩
  · show internNodeE (.proj n i e) s = _
    exact internNodeE_proj s n i e
      (Nat.le_trans (tabAt_size_le hsr.e.p9) (hok.sepProj.cap 0 (by decide)))
      (Nat.le_trans (tabAt_size_le hsr.e.s9) (hok.sepProj.cap 1 (by decide)))
  · exact ⟨hsr, by rw [hg]; exact ht.sr.gdir, by rw [hg]; exact ht.sr.gfln, by rw [hg]; exact ht.sr.gfll,
      by rw [hg]; exact ht.sr.gfls, by rw [hg]; exact ht.sr.gfle, by rw [hg]; exact ht.sr.gkb,
      by rw [hc]; exact ht.sr.code, fun j hj => by rw [hd]; exact ht.sr.kbuf j hj,
      fun mk => memoAt_frame (ht.sr.memo mk)
        (fun c hc => hm c (hok.memoOut (.e mk) c hc) (fun j hj e => hok.kbMemo (.e mk) j (by omega) (e ▸ hc)))
        (fun k hk => hm _ (hok.mdescOut (.e mk) k hk) (fun j hj => hok.kbMdesc (.e mk) k j hk (by omega))) hd,
      fun mk => memoAtN_frame (ht.sr.memoN mk)
        (fun c hc => hm c (hok.memoOut (.n mk) c hc) (fun j hj e => hok.kbMemo (.n mk) j (by omega) (e ▸ hc)))
        (fun k hk => hm _ (hok.mdescOut (.n mk) k hk) (fun j hj => hok.kbMdesc (.n mk) k j hk (by omega))) hd,
      fun mk => cacheAt_frame (ht.sr.cache mk)
        (fun c hc => hm c (hok.memoOut (.c mk) c hc) (fun j hj e => hok.kbMemo (.c mk) j (by omega) (e ▸ hc)))
        (fun k hk => hm _ (hok.mdescOut (.c mk) k hk) (fun j hj => hok.kbMdesc (.c mk) k j hk (by omega))) hd,
      modeAt_frame ht.sr.mode
        (fun b mk c hc => hm c (hok.memoOut (.m b mk) c hc) (fun j hj e => hok.kbMemo (.m b mk) j (by omega) (e ▸ hc)))
        (fun b mk k hk => hm _ (hok.mdescOut (.m b mk) k hk) (fun j hj => hok.kbMdesc (.m b mk) k j hk (by omega))) hd (by first | rfl | (rw [hg]) | (rw [hg']) | (rw [hgl _ (by decide)]) | simp_all),
      envAt_frame ht.sr.env
        (fun b c hc => hm c (hok.memoOut (envR b) c hc) (fun j hj e => hok.kbMemo (envR b) j (by omega) (e ▸ hc)))
        (fun b k hk => hm _ (hok.mdescOut (envR b) k hk) (fun j hj => hok.kbMdesc (envR b) k j hk (by omega)))
        (fun i hi => hm _ (hok.envOut i hi) (fun j hj => hok.kbEnv i j hi (by omega))) hd ⟨(by first | rfl | (rw [hg]) | (rw [hg']) | (rw [hgl _ (by decide)]) | simp_all), (by first | rfl | (rw [hg]) | (rw [hg']) | (rw [hgl _ (by decide)]) | simp_all)⟩, ht.sr.pins,
      heapEx_frame ht.sr.heap (fun i hi => hm _ (hok.heapOut i hi) (fun j hj => hok.kbHeap i j hi (by omega))) hd
        (by rw [hg])⟩

theorem specR_internProjI {β : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} (hok : CtxOK C)
    (hcode : C.code.lookup fInternProj = some ([(lEp, .one), (lEe, .one), (lIw, .one)], projBody, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k : EIdx → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x : MlS) (e1 e2 e3 : ExpHOL 64) (n : NIdx) (i : Nat) (e : EIdx)
    (hi : i < 2 ^ 63) (hx : x ∈ D)
    (he1 : sev Γ e1 = some (Enc.idxW n)) (he2 : sev Γ e2 = some (Enc.idxW e))
    (he3 : sev Γ e3 = some (BitVec.ofNat 64 i))
    (hk : ∀ h s', SpecR (Inv C s' ((x, Enc.idxW h) :: Γ) [] D) rest s' (k h) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) fInternProj [e1, e2, e3]) rest) s
      (internProjE n i e >>= k) R :=
  specR_call3IM x fInternProj lEp lEe lIw (by decide) (by decide) (by decide) e1 e2 e3 projBody (Enc.idxW n)
    (Enc.idxW e) (BitVec.ofNat 64 i) hx hcode he1 he2 he3 (PostE C) (fun _ _ _ _ hp => hp.2)
    (fun u hu _ h1 h2 h3 w hw => by
      subst hw
      exact proj_body_spec ra C hok s n i e hi _ ⟨hu, fun y w hy => by
        simp only [Env.get] at hy
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact h1
        · split at hy
          · rename_i e; subst e; simp at hy; subst hy; exact h2
          · split at hy
            · rename_i e; subst e; simp at hy; subst hy; exact h3
            · simp at hy⟩)
    (fun h w s' st hp => by obtain ⟨rfl, _⟩ := hp; exact hk h s')

end ConPanqueque.T
