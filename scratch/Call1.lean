import ConPanqueque.Logic.Basic
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The callee locals of a one-parameter function bind the parameter. -/
theorem lookupCode1 {σ : Type} (s : PanSemStateFiniteExact 64 σ) (f x : MlS) (body : ProgHOL 64)
    (v : BitVec 64) (hcode : s.code.lookup f = some ([(x, .one)], body, .one)) :
    ∃ callee, lookupCodeHOLFinite s.code.lookup f [.val (.word v)] = some (body, callee, .one) ∧
      callee.lookup x = some (.val (.word v)) := by
  unfold lookupCodeHOLFinite
  split
  · rename_i hh; simp [lookupCodeHOLExact, hcode, shapeOfHOLExact, shapeEqHOL] at hh
  · rename_i b cl rs hh
    simp [lookupCodeHOLExact, hcode, shapeOfHOLExact, shapeEqHOL] at hh
    obtain ⟨rfl, rfl, rfl⟩ := hh
    exact ⟨_, rfl, by simp⟩

/-- `y = f(arg)` for a one-parameter word function `f(x)` whose body, from any
entry state binding `x` to the argument, returns `w` in a state satisfying `Q`. -/
theorem call1 {σ : Type} (s : PanSemStateFiniteExact 64 σ) (f x y : MlS) (body : ProgHOL 64)
    (arg : ExpHOL 64) (v w : BitVec 64) (Q : PanSemStateFiniteExact 64 σ → Prop)
    (hcode : s.code.lookup f = some ([(x, .one)], body, .one))
    (harg : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) arg =
      some (.val (.word v)))
    (hclk : s.clock ≠ 0)
    (hy : ∃ w0, s.locals.lookup y = some (.val (.word w0)))
    (hbody : ∀ callee : HolFiniteMapExact MlS (ValueHOL 64), callee.lookup x = some (.val (.word v)) →
      ∃ st, evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
        (some (.returned (.val (.word w))), st) ∧ Q st) :
    ∃ st, Q st ∧ evaluateHOLFiniteState s (.call (some (some (.local, y), none)) f [arg]) =
        (none, setKvarHOLFinite .local y (.val (.word w)) { st with locals := s.locals }) := by
  obtain ⟨hlk, hx⟩ := Classical.choose_spec (lookupCode1 s f x body v hcode)
  obtain ⟨st, hb, hq⟩ := hbody _ hx
  obtain ⟨w0, hw0⟩ := hy
  refine ⟨st, hq, ?_⟩
  apply ConPanqueque.Logic.call_assign s .local y f none [arg] [.val (.word v)] body _ .one _ st
  · simp [evalListHOLFinite, evalListHOLExact, harg]
  · exact hlk
  · exact hclk
  · exact hb
  · simp [shapeOfHOLExact, shapeEqHOL]
  · simp [isValidValueHOLExact, lookupKvarHOLExact, hw0, shapeOfHOLExact, shapeEqHOL]
