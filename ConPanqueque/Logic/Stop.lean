import ConPanqueque.Logic.Basic
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString

namespace ConPanqueque.Logic

/-- Results that end the whole program without a verdict: out of clock, or a final FFI event. -/
def Stop (r : Option (PanSemResultExact 64)) : Prop := r = some .timeOut ∨ ∃ ev, r = some (.finalFfi ev)

/-- What the program does when it cannot go on (e.g. out of arena space). -/
def hang : ProgHOL 64 := .while (.const 1) .skip

theorem hang_spec {σ : Type} : ∀ (n : Nat) (s : PanSemStateFiniteExact 64 σ), s.clock = n →
    (evaluateHOLFiniteState s hang).1 = some .timeOut := by
  intro n
  induction n with
  | zero =>
    intro s hs
    unfold hang; rw [evaluateHOLFiniteState_eq_evaluate_def]
    simp [evalHOLExact, hs]
  | succ n ih =>
    intro s hs
    unfold hang; rw [evaluateHOLFiniteState_eq_evaluate_def]
    simp [evalHOLExact, hs]
    exact ih _ (by simp [decClockHOLFinite, hs])

theorem stop_timeOut : Stop (some .timeOut) := Or.inl rfl

theorem stop_ne_returned {r : Option (PanSemResultExact 64)} (h : Stop r) (v : ValueHOL 64) :
    r ≠ some (.returned v) := by
  rcases h with h | ⟨ev, h⟩ <;> rw [h] <;> simp

theorem seq_stop {σ : Type} (s : PanSemStateFiniteExact 64 σ) (p q : ProgHOL 64)
    (h : Stop (evaluateHOLFiniteState s p).1) : Stop (evaluateHOLFiniteState s (.seq p q)).1 := by
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  generalize hr : evaluateHOLFiniteState s p = r at h
  obtain ⟨r1, r2⟩ := r
  rcases h with h | ⟨ev, h⟩ <;> (simp only at h; subst h; simp [hr]) <;> first | exact Or.inl rfl | exact Or.inr ⟨ev, rfl⟩

theorem dec_stop {σ : Type} (s : PanSemStateFiniteExact 64 σ) (x : MlS) (e : ExpHOL 64) (v : BitVec 64)
    (body : ProgHOL 64)
    (he : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
      some (.val (.word v)))
    (h : Stop (evaluateHOLFiniteState (setVarHOLFinite x (.val (.word v)) s) body).1) :
    Stop (evaluateHOLFiniteState s (.dec x .one e body)).1 := by
  rw [(dec_word s x e v body he).1]; exact h

theorem call_stop {σ : Type} (s : PanSemStateFiniteExact 64 σ)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64)))
    (f : MlS) (args : List (ExpHOL 64)) (vals : List (ValueHOL 64)) (body : ProgHOL 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (rs : ShapeHOL)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals)
    (hlk : lookupCodeHOLFinite s.code.lookup f vals = some (body, callee, rs))
    (h : Stop (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1) :
    Stop (evaluateHOLFiniteState s (.call info f args)).1 := by
  by_cases hc : s.clock = 0
  · rw [evaluateHOLFiniteState_call, hargs]; simp only []; rw [hlk]; simp [hc]; exact Or.inl rfl
  generalize hb : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = r at h
  obtain ⟨r1, r2⟩ := r
  rcases h with h | ⟨ev, h⟩ <;> simp only at h <;> subst h
  · rw [evaluateHOLFiniteState_call_body_fallback s info f args vals body callee rs .timeOut r2 hargs hlk hc hb
      (Or.inr (Or.inl rfl))]; exact Or.inl rfl
  · rw [evaluateHOLFiniteState_call_body_fallback s info f args vals body callee rs (.finalFfi ev) r2 hargs hlk hc hb
      (Or.inr (Or.inr ⟨ev, rfl⟩))]; exact Or.inr ⟨ev, rfl⟩

/-- `y = f(arg1, arg2)` whose body stops: the call stops. -/
theorem call2_stop {σ : Type} (s : PanSemStateFiniteExact 64 σ) (f x1 x2 : MlS) (body : ProgHOL 64)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64)))
    (arg1 arg2 : ExpHOL 64) (v1 v2 : BitVec 64) (hne : x1 ≠ x2)
    (hcode : s.code.lookup f = some ([(x1, .one), (x2, .one)], body, .one))
    (harg1 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) arg1 =
      some (.val (.word v1)))
    (harg2 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) arg2 =
      some (.val (.word v2)))
    (hbody : ∀ callee : HolFiniteMapExact MlS (ValueHOL 64), callee.lookup x1 = some (.val (.word v1)) →
      callee.lookup x2 = some (.val (.word v2)) →
      Stop (evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body).1) :
    Stop (evaluateHOLFiniteState s (.call info f [arg1, arg2])).1 := by
  obtain ⟨hlk, hx1, hx2⟩ := Classical.choose_spec (lookupCode2 s f x1 x2 body v1 v2 hne hcode)
  exact call_stop s info f [arg1, arg2] _ body _ .one (by simp [evalListHOLFinite, evalListHOLExact, harg1, harg2])
    hlk (hbody _ hx1 hx2)

end ConPanqueque.Logic
