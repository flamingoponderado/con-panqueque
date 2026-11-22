import ConPanqueque.T.Spec
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic
open ConRon.Arena

/-!
# Calls

`x := f(e₁, …)`: when the callee's body refines `m` (as a `SpecR` from its entry state), the call
refines `m`, the caller's locals come back with `x` bound to the returned word. A call with the
clock exhausted times out, which is a `Stop`.
-/

namespace ConPanqueque.T

variable {σ : Type}

/-- An empty local map (a default callee). -/
def emptyLocals : HolFiniteMapExact MlS (ValueHOL 64) := ⟨fun _ => none, [], fun _ h => absurd rfl h⟩

/-- Calling with arguments that evaluate to `vs`, at a code entry `lookupCodeHOLFinite` finds. -/
theorem spec_callN {α : Type} {P : PState σ → Prop} {s : AState} {m : AM α} {Q : α → AState → PState σ → Prop}
    (x f : MlS) (args : List (ExpHOL 64)) (B : ProgHOL 64)
    (vs : PState σ → List (ValueHOL 64)) (callee : PState σ → HolFiniteMapExact MlS (ValueHOL 64))
    (hargs : ∀ t, P t → evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) args = some (vs t))
    (hlk : ∀ t, P t → lookupCodeHOLFinite t.code.lookup f (vs t) = some (B, callee t, .one))
    (hx : ∀ t, P t → ∃ w0, t.locals.lookup x = some (.val (.word w0)))
    (R : PState σ → α → BitVec 64 → AState → PState σ → Prop)
    (hB : ∀ t, P t → SpecR (fun u => u = callEntryStateHOLFinite t (callee t)) B s m (R t))
    (hQ : ∀ t, P t → ∀ a w s' st, R t a w s' st →
      Q a s' (setKvarHOLFinite .local x (.val (.word w)) { st with locals := t.locals })) :
    Spec P (.call (some (some (.local, x), none)) f args) s m Q := by
  intro t ht
  by_cases hc : t.clock = 0
  · left
    rw [evaluateHOLFiniteState_call, hargs t ht]; simp only []; rw [hlk t ht]; simp [hc]; exact Or.inl rfl
  rcases hB t ht _ rfl with hs | ⟨w, hr, a, s', hm, hR⟩
  · exact Or.inl (call_stop t _ f args (vs t) B (callee t) .one (hargs t ht) (hlk t ht) hs)
  right
  obtain ⟨w0, hw0⟩ := hx t ht
  generalize hst : evaluateHOLFiniteState (callEntryStateHOLFinite t (callee t)) B = r at hr hR
  obtain ⟨r1, st⟩ := r
  simp only at hr hR
  subst hr
  rw [call_assign t .local x f none args (vs t) B (callee t) .one (.val (.word w)) st (hargs t ht) (hlk t ht) hc hst
    (by simp [shapeOfHOLExact, shapeEqHOL])
    (by simp [isValidValueHOLExact, lookupKvarHOLExact, hw0, shapeOfHOLExact, shapeEqHOL])]
  exact ⟨rfl, a, s', hm, hQ t ht a w s' st hR⟩

theorem spec_call1 {α : Type} {P : PState σ → Prop} {s : AState} {m : AM α} {Q : α → AState → PState σ → Prop}
    (x f p1 : MlS) (e1 : ExpHOL 64) (B : ProgHOL 64) (v1 : PState σ → BitVec 64)
    (hC : ∀ t, P t → t.code.lookup f = some ([(p1, .one)], B, .one))
    (he1 : ∀ t, P t → EV t e1 = some (.val (.word (v1 t))))
    (hx : ∀ t, P t → ∃ w0, t.locals.lookup x = some (.val (.word w0)))
    (R : PState σ → α → BitVec 64 → AState → PState σ → Prop)
    (hB : ∀ t, P t → ∀ callee : HolFiniteMapExact MlS (ValueHOL 64), callee.lookup p1 = some (.val (.word (v1 t))) →
      SpecR (fun u => u = callEntryStateHOLFinite t callee) B s m (R t))
    (hQ : ∀ t, P t → ∀ a w s' st, R t a w s' st →
      Q a s' (setKvarHOLFinite .local x (.val (.word w)) { st with locals := t.locals })) :
    Spec P (.call (some (some (.local, x), none)) f [e1]) s m Q := by
  have hk : ∀ t, P t → ∃ callee, lookupCodeHOLFinite t.code.lookup f [.val (.word (v1 t))] = some (B, callee, .one) ∧
      callee.lookup p1 = some (.val (.word (v1 t))) := fun t ht => lookupCode1 t f p1 B (v1 t) (hC t ht)
  classical
  let cal : PState σ → HolFiniteMapExact MlS (ValueHOL 64) := fun t =>
    if h : P t then Classical.choose (hk t h) else emptyLocals
  have hcal : ∀ t (h : P t), cal t = Classical.choose (hk t h) := fun t h => by simp [cal, h]
  refine spec_callN x f [e1] B (fun t => [.val (.word (v1 t))]) cal
    (fun t ht => by simp only [EV] at he1; simp [evalListHOLFinite, evalListHOLExact, he1 t ht])
    (fun t ht => by rw [hcal t ht]; exact (Classical.choose_spec (hk t ht)).1) hx R
    (fun t ht => hB t ht _ (by rw [hcal t ht]; exact (Classical.choose_spec (hk t ht)).2)) hQ

theorem spec_call2 {α : Type} {P : PState σ → Prop} {s : AState} {m : AM α} {Q : α → AState → PState σ → Prop}
    (x f p1 p2 : MlS) (hne : p1 ≠ p2) (e1 e2 : ExpHOL 64) (B : ProgHOL 64) (v1 v2 : PState σ → BitVec 64)
    (hC : ∀ t, P t → t.code.lookup f = some ([(p1, .one), (p2, .one)], B, .one))
    (he1 : ∀ t, P t → EV t e1 = some (.val (.word (v1 t))))
    (he2 : ∀ t, P t → EV t e2 = some (.val (.word (v2 t))))
    (hx : ∀ t, P t → ∃ w0, t.locals.lookup x = some (.val (.word w0)))
    (R : PState σ → α → BitVec 64 → AState → PState σ → Prop)
    (hB : ∀ t, P t → ∀ callee : HolFiniteMapExact MlS (ValueHOL 64), callee.lookup p1 = some (.val (.word (v1 t))) →
      callee.lookup p2 = some (.val (.word (v2 t))) →
      SpecR (fun u => u = callEntryStateHOLFinite t callee) B s m (R t))
    (hQ : ∀ t, P t → ∀ a w s' st, R t a w s' st →
      Q a s' (setKvarHOLFinite .local x (.val (.word w)) { st with locals := t.locals })) :
    Spec P (.call (some (some (.local, x), none)) f [e1, e2]) s m Q := by
  have hk : ∀ t, P t → ∃ callee, lookupCodeHOLFinite t.code.lookup f [.val (.word (v1 t)), .val (.word (v2 t))] =
      some (B, callee, .one) ∧ callee.lookup p1 = some (.val (.word (v1 t))) ∧
      callee.lookup p2 = some (.val (.word (v2 t))) := fun t ht => lookupCode2 t f p1 p2 B (v1 t) (v2 t) hne (hC t ht)
  classical
  let cal : PState σ → HolFiniteMapExact MlS (ValueHOL 64) := fun t =>
    if h : P t then Classical.choose (hk t h) else emptyLocals
  have hcal : ∀ t (h : P t), cal t = Classical.choose (hk t h) := fun t h => by simp [cal, h]
  refine spec_callN x f [e1, e2] B (fun t => [.val (.word (v1 t)), .val (.word (v2 t))]) cal
    (fun t ht => by simp only [EV] at he1 he2; simp [evalListHOLFinite, evalListHOLExact, he1 t ht, he2 t ht])
    (fun t ht => by rw [hcal t ht]; exact (Classical.choose_spec (hk t ht)).1) hx R
    (fun t ht => hB t ht _ (by rw [hcal t ht]; exact (Classical.choose_spec (hk t ht)).2.1)
      (by rw [hcal t ht]; exact (Classical.choose_spec (hk t ht)).2.2)) hQ

theorem lookupCode3 (s : PState σ) (f x1 x2 x3 : MlS) (body : ProgHOL 64) (v1 v2 v3 : BitVec 64)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hcode : s.code.lookup f = some ([(x1, .one), (x2, .one), (x3, .one)], body, .one)) :
    ∃ callee, lookupCodeHOLFinite s.code.lookup f [.val (.word v1), .val (.word v2), .val (.word v3)] =
      some (body, callee, .one) ∧ callee.lookup x1 = some (.val (.word v1)) ∧
      callee.lookup x2 = some (.val (.word v2)) ∧ callee.lookup x3 = some (.val (.word v3)) := by
  unfold lookupCodeHOLFinite
  split
  · rename_i hh; simp [lookupCodeHOLExact, hcode, shapeOfHOLExact, shapeEqHOL] at hh
    exact absurd hh (by simp [h12, h13, h23])
  · rename_i b cl rs hh
    simp [lookupCodeHOLExact, hcode, shapeOfHOLExact, shapeEqHOL] at hh
    obtain ⟨_, rfl, rfl, rfl⟩ := hh
    exact ⟨_, rfl, by simp [h12, h13], by simp [h23], by simp⟩

theorem spec_call3 {α : Type} {P : PState σ → Prop} {s : AState} {m : AM α} {Q : α → AState → PState σ → Prop}
    (x f p1 p2 p3 : MlS) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3) (e1 e2 e3 : ExpHOL 64) (B : ProgHOL 64)
    (v1 v2 v3 : PState σ → BitVec 64)
    (hC : ∀ t, P t → t.code.lookup f = some ([(p1, .one), (p2, .one), (p3, .one)], B, .one))
    (he1 : ∀ t, P t → EV t e1 = some (.val (.word (v1 t))))
    (he2 : ∀ t, P t → EV t e2 = some (.val (.word (v2 t))))
    (he3 : ∀ t, P t → EV t e3 = some (.val (.word (v3 t))))
    (hx : ∀ t, P t → ∃ w0, t.locals.lookup x = some (.val (.word w0)))
    (R : PState σ → α → BitVec 64 → AState → PState σ → Prop)
    (hB : ∀ t, P t → ∀ callee : HolFiniteMapExact MlS (ValueHOL 64), callee.lookup p1 = some (.val (.word (v1 t))) →
      callee.lookup p2 = some (.val (.word (v2 t))) → callee.lookup p3 = some (.val (.word (v3 t))) →
      SpecR (fun u => u = callEntryStateHOLFinite t callee) B s m (R t))
    (hQ : ∀ t, P t → ∀ a w s' st, R t a w s' st →
      Q a s' (setKvarHOLFinite .local x (.val (.word w)) { st with locals := t.locals })) :
    Spec P (.call (some (some (.local, x), none)) f [e1, e2, e3]) s m Q := by
  have hk : ∀ t, P t → ∃ callee, lookupCodeHOLFinite t.code.lookup f
      [.val (.word (v1 t)), .val (.word (v2 t)), .val (.word (v3 t))] = some (B, callee, .one) ∧
      callee.lookup p1 = some (.val (.word (v1 t))) ∧ callee.lookup p2 = some (.val (.word (v2 t))) ∧
      callee.lookup p3 = some (.val (.word (v3 t))) :=
    fun t ht => lookupCode3 t f p1 p2 p3 B (v1 t) (v2 t) (v3 t) h12 h13 h23 (hC t ht)
  classical
  let cal : PState σ → HolFiniteMapExact MlS (ValueHOL 64) := fun t =>
    if h : P t then Classical.choose (hk t h) else emptyLocals
  have hcal : ∀ t (h : P t), cal t = Classical.choose (hk t h) := fun t h => by simp [cal, h]
  refine spec_callN x f [e1, e2, e3] B (fun t => [.val (.word (v1 t)), .val (.word (v2 t)), .val (.word (v3 t))]) cal
    (fun t ht => by simp only [EV] at he1 he2 he3; simp [evalListHOLFinite, evalListHOLExact, he1 t ht, he2 t ht, he3 t ht])
    (fun t ht => by rw [hcal t ht]; exact (Classical.choose_spec (hk t ht)).1) hx R
    (fun t ht => hB t ht _ (by rw [hcal t ht]; exact (Classical.choose_spec (hk t ht)).2.1)
      (by rw [hcal t ht]; exact (Classical.choose_spec (hk t ht)).2.2.1)
      (by rw [hcal t ht]; exact (Classical.choose_spec (hk t ht)).2.2.2)) hQ

end ConPanqueque.T
