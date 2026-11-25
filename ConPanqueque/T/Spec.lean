import ConPanqueque.V.EVar
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic
open ConRon.Arena

/-!
# The translator's judgement

A Pancake program `c` refines a twin computation `m : AM α` from twin state `s`:
from every Pancake state satisfying `P`, either the program stops (`Stop`: out of
resources, or a failure, which Pancake compiles to a halt) or it finishes normally
and the twin run succeeds, with the result and both final states in `Q`.
`SpecR` is the same for a program that ends in `return`.

Only the success direction is stated: a twin failure must be a Pancake stop, but a
Pancake stop says nothing about the twin. This is the shape soundness needs
(Pancake accepts ⇒ twin accepts).
-/

namespace ConPanqueque.T

variable {σ : Type}

abbrev PState (σ : Type) := PanSemStateFiniteExact 64 σ

/-- Evaluation of an expression in a state, as the semantics does it. -/
noncomputable abbrev EV (t : PState σ) (e : ExpHOL 64) : Option (ValueHOL 64) :=
  @evalHOLExact 64 σ _ t.toExact (fun c => Classical.propDecidable (t.memaddrs c)) e

def Spec {α : Type} (P : PState σ → Prop) (c : ProgHOL 64) (s : AState) (m : AM α)
    (Q : α → AState → PState σ → Prop) : Prop :=
  ∀ t, P t → Stop (evaluateHOLFiniteState t c).1 ∨
    ((evaluateHOLFiniteState t c).1 = none ∧ ∃ a s', m s = .ok (a, s') ∧ Q a s' (evaluateHOLFiniteState t c).2)

def SpecR {α : Type} (P : PState σ → Prop) (c : ProgHOL 64) (s : AState) (m : AM α)
    (R : α → BitVec 64 → AState → PState σ → Prop) : Prop :=
  ∀ t, P t → Stop (evaluateHOLFiniteState t c).1 ∨
    ∃ w, (evaluateHOLFiniteState t c).1 = some (.returned (.val (.word w))) ∧
      ∃ a s', m s = .ok (a, s') ∧ R a w s' (evaluateHOLFiniteState t c).2

/-! ## Consequence -/

theorem spec_mono {α : Type} {P P' : PState σ → Prop} {c : ProgHOL 64} {s : AState} {m : AM α}
    {Q Q' : α → AState → PState σ → Prop} (h : Spec P c s m Q) (hP : ∀ t, P' t → P t)
    (hQ : ∀ a s' t, Q a s' t → Q' a s' t) : Spec P' c s m Q' := by
  intro t ht
  rcases h t (hP t ht) with hs | ⟨hn, a, s', hm, hq⟩
  · exact Or.inl hs
  · exact Or.inr ⟨hn, a, s', hm, hQ _ _ _ hq⟩

theorem specR_mono {α : Type} {P P' : PState σ → Prop} {c : ProgHOL 64} {s : AState} {m : AM α}
    {R R' : α → BitVec 64 → AState → PState σ → Prop} (h : SpecR P c s m R) (hP : ∀ t, P' t → P t)
    (hR : ∀ a w s' t, R a w s' t → R' a w s' t) : SpecR P' c s m R' := by
  intro t ht
  rcases h t (hP t ht) with hs | ⟨w, hn, a, s', hm, hr⟩
  · exact Or.inl hs
  · exact Or.inr ⟨w, hn, a, s', hm, hR _ _ _ _ hr⟩

/-! ## Sequencing = bind -/

theorem spec_bind {α β : Type} {P : PState σ → Prop} {c1 c2 : ProgHOL 64} {s : AState} {m : AM α}
    {k : α → AM β} {Q1 : α → AState → PState σ → Prop} {Q : β → AState → PState σ → Prop}
    (h1 : Spec P c1 s m Q1) (h2 : ∀ a s', Spec (Q1 a s') c2 s' (k a) Q) :
    Spec P (.seq c1 c2) s (m >>= k) Q := by
  intro t ht
  rcases h1 t ht with hs | ⟨hn, a, s', hm, hq⟩
  · exact Or.inl (seq_stop t c1 c2 hs)
  · have e : evaluateHOLFiniteState t c1 = (none, (evaluateHOLFiniteState t c1).2) := by
      rw [← hn]
    rw [seq_normal c2 e]
    rcases h2 a s' _ hq with hs2 | ⟨hn2, b, s'', hk, hq2⟩
    · exact Or.inl hs2
    · refine Or.inr ⟨hn2, b, s'', ?_, hq2⟩
      show (do let r ← m s; match r with | (a, s) => k a s) = _
      rw [hm]; exact hk

theorem specR_bind {α β : Type} {P : PState σ → Prop} {c1 c2 : ProgHOL 64} {s : AState} {m : AM α}
    {k : α → AM β} {Q1 : α → AState → PState σ → Prop} {R : β → BitVec 64 → AState → PState σ → Prop}
    (h1 : Spec P c1 s m Q1) (h2 : ∀ a s', SpecR (Q1 a s') c2 s' (k a) R) :
    SpecR P (.seq c1 c2) s (m >>= k) R := by
  intro t ht
  rcases h1 t ht with hs | ⟨hn, a, s', hm, hq⟩
  · exact Or.inl (seq_stop t c1 c2 hs)
  · have e : evaluateHOLFiniteState t c1 = (none, (evaluateHOLFiniteState t c1).2) := by
      rw [← hn]
    rw [seq_normal c2 e]
    rcases h2 a s' _ hq with hs2 | ⟨w, hn2, b, s'', hk, hr⟩
    · exact Or.inl hs2
    · refine Or.inr ⟨w, hn2, b, s'', ?_, hr⟩
      show (do let r ← m s; match r with | (a, s) => k a s) = _
      rw [hm]; exact hk

/-- A program step that the twin does not see (`pure ()` on the twin side). -/
theorem spec_seq {β : Type} {P P1 : PState σ → Prop} {c1 c2 : ProgHOL 64} {s : AState} {m : AM β}
    {Q : β → AState → PState σ → Prop}
    (h1 : ∀ t, P t → Stop (evaluateHOLFiniteState t c1).1 ∨
      ((evaluateHOLFiniteState t c1).1 = none ∧ P1 (evaluateHOLFiniteState t c1).2))
    (h2 : Spec P1 c2 s m Q) : Spec P (.seq c1 c2) s m Q := by
  intro t ht
  rcases h1 t ht with hs | ⟨hn, hp⟩
  · exact Or.inl (seq_stop t c1 c2 hs)
  · have e : evaluateHOLFiniteState t c1 = (none, (evaluateHOLFiniteState t c1).2) := by rw [← hn]
    rw [seq_normal c2 e]; exact h2 _ hp

theorem specR_seq {β : Type} {P P1 : PState σ → Prop} {c1 c2 : ProgHOL 64} {s : AState} {m : AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop}
    (h1 : ∀ t, P t → Stop (evaluateHOLFiniteState t c1).1 ∨
      ((evaluateHOLFiniteState t c1).1 = none ∧ P1 (evaluateHOLFiniteState t c1).2))
    (h2 : SpecR P1 c2 s m R) : SpecR P (.seq c1 c2) s m R := by
  intro t ht
  rcases h1 t ht with hs | ⟨hn, hp⟩
  · exact Or.inl (seq_stop t c1 c2 hs)
  · have e : evaluateHOLFiniteState t c1 = (none, (evaluateHOLFiniteState t c1).2) := by rw [← hn]
    rw [seq_normal c2 e]; exact h2 _ hp

/-! ## Leaves -/

theorem spec_skip {α : Type} {P : PState σ → Prop} {s : AState} {a : α} {Q : α → AState → PState σ → Prop}
    (h : ∀ t, P t → Q a s t) : Spec P .skip s (pure a) Q := by
  intro t ht
  have e : evaluateHOLFiniteState t .skip = (none, t) := by
    rw [evaluateHOLFiniteState_eq_evaluate_def]
  rw [e]; exact Or.inr ⟨rfl, a, s, rfl, h t ht⟩

/-- An assignment of a pure value's representation to a declared local. -/
theorem spec_assign {α : Type} {P : PState σ → Prop} {s : AState} {a : α} {Q : α → AState → PState σ → Prop}
    (x : MlS) (e : ExpHOL 64) (w : PState σ → BitVec 64)
    (he : ∀ t, P t → EV t e = some (.val (.word (w t))))
    (hx : ∀ t, P t → ∃ w0, t.locals.lookup x = some (.val (.word w0)))
    (h : ∀ t, P t → Q a s (setVarHOLFinite x (.val (.word (w t))) t)) :
    Spec P (.assign .local x e) s (pure a) Q := by
  intro t ht
  obtain ⟨w0, h0⟩ := hx t ht
  rw [ConsLoop.assign_local t x e (w t) w0 (he t ht) h0]
  exact Or.inr ⟨rfl, a, s, rfl, h t ht⟩

theorem return_word (t : PState σ) (e : ExpHOL 64) (w : BitVec 64) (he : EV t e = some (.val (.word w))) :
    (evaluateHOLFiniteState t (.return e)).1 = some (.returned (.val (.word w))) := by
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  simp only [EV] at he
  simp [he, shapeOfHOLExact]

theorem specR_return {α : Type} {P : PState σ → Prop} {s : AState} {a : α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (e : ExpHOL 64) (w : PState σ → BitVec 64)
    (he : ∀ t, P t → EV t e = some (.val (.word (w t))))
    (h : ∀ t, P t → R a (w t) s (evaluateHOLFiniteState t (.return e)).2) :
    SpecR P (.return e) s (pure a) R := by
  intro t ht
  exact Or.inr ⟨w t, return_word t e (w t) (he t ht), a, s, rfl, h t ht⟩

/-- A twin failure is a Pancake halt. -/
theorem spec_fail {α : Type} {P : PState σ → Prop} {s : AState} (err : CheckError)
    {Q : α → AState → PState σ → Prop} : Spec P hang s (fail err) Q := by
  intro t _
  exact Or.inl (hang_stop t)

theorem specR_fail {α : Type} {P : PState σ → Prop} {s : AState} (err : CheckError)
    {R : α → BitVec 64 → AState → PState σ → Prop} : SpecR P hang s (fail err) R := by
  intro t _
  exact Or.inl (hang_stop t)

/-- Any computation, refined by a halt. -/
theorem spec_hang {α : Type} {P : PState σ → Prop} {s : AState} {m : AM α}
    {Q : α → AState → PState σ → Prop} : Spec P hang s m Q := by
  intro t _
  exact Or.inl (hang_stop t)

/-! ## Branching -/

theorem spec_ite {α : Type} {P : PState σ → Prop} {c1 c2 : ProgHOL 64} {s : AState} {b : Bool}
    {m1 m2 : AM α} {Q : α → AState → PState σ → Prop} (e : ExpHOL 64) (w : PState σ → BitVec 64)
    (he : ∀ t, P t → EV t e = some (.val (.word (w t))))
    (hb : ∀ t, P t → (w t ≠ 0 ↔ b = true))
    (h1 : Spec (fun t => P t ∧ b = true) c1 s m1 Q) (h2 : Spec (fun t => P t ∧ b = false) c2 s m2 Q) :
    Spec P (.ite e c1 c2) s (if b then m1 else m2) Q := by
  intro t ht
  rw [ite_word t e c1 c2 (w t) (he t ht)]
  by_cases hw : w t ≠ 0
  · have hb' : b = true := (hb t ht).mp hw
    rw [ite_eq_left hw]; subst hb'; exact h1 t ⟨ht, rfl⟩
  · have hb' : b = false := by
      cases hc : b
      · rfl
      · exact absurd ((hb t ht).mpr hc) hw
    rw [ite_eq_right hw]; subst hb'; exact h2 t ⟨ht, rfl⟩

theorem specR_ite {α : Type} {P : PState σ → Prop} {c1 c2 : ProgHOL 64} {s : AState} {b : Bool}
    {m1 m2 : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (e : ExpHOL 64) (w : PState σ → BitVec 64)
    (he : ∀ t, P t → EV t e = some (.val (.word (w t))))
    (hb : ∀ t, P t → (w t ≠ 0 ↔ b = true))
    (h1 : SpecR (fun t => P t ∧ b = true) c1 s m1 R) (h2 : SpecR (fun t => P t ∧ b = false) c2 s m2 R) :
    SpecR P (.ite e c1 c2) s (if b then m1 else m2) R := by
  intro t ht
  rw [ite_word t e c1 c2 (w t) (he t ht)]
  by_cases hw : w t ≠ 0
  · have hb' : b = true := (hb t ht).mp hw
    rw [ite_eq_left hw]; subst hb'; exact h1 t ⟨ht, rfl⟩
  · have hb' : b = false := by
      cases hc : b
      · rfl
      · exact absurd ((hb t ht).mpr hc) hw
    rw [ite_eq_right hw]; subst hb'; exact h2 t ⟨ht, rfl⟩

/-! ## Pancake-side branching (the twin computation is the same in both branches) -/

theorem spec_if {α : Type} {P : PState σ → Prop} {c1 c2 : ProgHOL 64} {s : AState} {m : AM α}
    {Q : α → AState → PState σ → Prop} (e : ExpHOL 64) (w : PState σ → BitVec 64)
    (he : ∀ t, P t → EV t e = some (.val (.word (w t))))
    (h1 : Spec (fun t => P t ∧ w t ≠ 0) c1 s m Q) (h2 : Spec (fun t => P t ∧ w t = 0) c2 s m Q) :
    Spec P (.ite e c1 c2) s m Q := by
  intro t ht
  rw [ite_word t e c1 c2 (w t) (he t ht)]
  by_cases hw : w t ≠ 0
  · rw [ite_eq_left hw]; exact h1 t ⟨ht, hw⟩
  · rw [ite_eq_right hw]; exact h2 t ⟨ht, by simpa using hw⟩

theorem specR_if {α : Type} {P : PState σ → Prop} {c1 c2 : ProgHOL 64} {s : AState} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (e : ExpHOL 64) (w : PState σ → BitVec 64)
    (he : ∀ t, P t → EV t e = some (.val (.word (w t))))
    (h1 : SpecR (fun t => P t ∧ w t ≠ 0) c1 s m R) (h2 : SpecR (fun t => P t ∧ w t = 0) c2 s m R) :
    SpecR P (.ite e c1 c2) s m R := by
  intro t ht
  rw [ite_word t e c1 c2 (w t) (he t ht)]
  by_cases hw : w t ≠ 0
  · rw [ite_eq_left hw]; exact h1 t ⟨ht, hw⟩
  · rw [ite_eq_right hw]; exact h2 t ⟨ht, by simpa using hw⟩

theorem spec_false {α : Type} {P : PState σ → Prop} {c : ProgHOL 64} {s : AState} {m : AM α}
    {Q : α → AState → PState σ → Prop} (h : ∀ t, P t → False) : Spec P c s m Q :=
  fun t ht => absurd (h t ht) id

theorem specR_false {α : Type} {P : PState σ → Prop} {c : ProgHOL 64} {s : AState} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (h : ∀ t, P t → False) : SpecR P c s m R :=
  fun t ht => absurd (h t ht) id

theorem specR_hang {α : Type} {P : PState σ → Prop} {s : AState} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} : SpecR P hang s m R := by
  intro t _
  exact Or.inl (hang_stop t)

theorem spec_congr {α : Type} {P : PState σ → Prop} {c : ProgHOL 64} {s : AState} {m m' : AM α}
    {Q : α → AState → PState σ → Prop} (e : m s = m' s) (h : Spec P c s m' Q) : Spec P c s m Q := by
  intro t ht
  rcases h t ht with hs | ⟨hn, a, s', hm, hq⟩
  · exact Or.inl hs
  · exact Or.inr ⟨hn, a, s', by rw [e]; exact hm, hq⟩

theorem specR_congr {α : Type} {P : PState σ → Prop} {c : ProgHOL 64} {s : AState} {m m' : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (e : m s = m' s) (h : SpecR P c s m' R) : SpecR P c s m R := by
  intro t ht
  rcases h t ht with hs | ⟨w, hr, a, s', hm, hq⟩
  · exact Or.inl hs
  · exact Or.inr ⟨w, hr, a, s', by rw [e]; exact hm, hq⟩

/-- A Pancake-only step before a twin computation, as an assignment. -/
theorem spec_pre_assign {β : Type} {P P1 : PState σ → Prop} {c2 : ProgHOL 64} {s : AState} {m : AM β}
    {Q : β → AState → PState σ → Prop} (x : MlS) (e : ExpHOL 64) (w : PState σ → BitVec 64)
    (he : ∀ t, P t → EV t e = some (.val (.word (w t))))
    (hx : ∀ t, P t → ∃ w0, t.locals.lookup x = some (.val (.word w0)))
    (hP : ∀ t, P t → P1 (setVarHOLFinite x (.val (.word (w t))) t))
    (h2 : Spec P1 c2 s m Q) : Spec P (.seq (.assign .local x e) c2) s m Q := by
  refine spec_seq (fun t ht => ?_) h2
  obtain ⟨w0, h0⟩ := hx t ht
  rw [ConsLoop.assign_local t x e (w t) w0 (he t ht) h0]
  exact Or.inr ⟨rfl, hP t ht⟩

theorem specR_pre_assign {β : Type} {P P1 : PState σ → Prop} {c2 : ProgHOL 64} {s : AState} {m : AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (x : MlS) (e : ExpHOL 64) (w : PState σ → BitVec 64)
    (he : ∀ t, P t → EV t e = some (.val (.word (w t))))
    (hx : ∀ t, P t → ∃ w0, t.locals.lookup x = some (.val (.word w0)))
    (hP : ∀ t, P t → P1 (setVarHOLFinite x (.val (.word (w t))) t))
    (h2 : SpecR P1 c2 s m R) : SpecR P (.seq (.assign .local x e) c2) s m R := by
  refine specR_seq (fun t ht => ?_) h2
  obtain ⟨w0, h0⟩ := hx t ht
  rw [ConsLoop.assign_local t x e (w t) w0 (he t ht) h0]
  exact Or.inr ⟨rfl, hP t ht⟩

theorem return_state (t : PState σ) (e : ExpHOL 64) (w : BitVec 64) (he : EV t e = some (.val (.word w))) :
    (evaluateHOLFiniteState t (.return e)).2 = emptyLocalsHOLFinite t := by
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  simp only [EV] at he
  simp [he, shapeOfHOLExact]

end ConPanqueque.T
