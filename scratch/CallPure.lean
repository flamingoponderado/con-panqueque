import ConPanqueque.Logic.Basic
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- `y = f(arg)` where `f(a) = return e`: the caller continues with `y = w` and one
clock tick less, nothing else changed. -/
theorem call_pure {σ : Type} (s : PanSemStateFiniteExact 64 σ) (f a y : MlS) (e arg : ExpHOL 64)
    (v w : BitVec 64)
    (hc : s.code.lookup f = some ([(a, .one)], .return e, .one))
    (harg : @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) arg =
      some (.val (.word v)))
    (hclk : s.clock ≠ 0)
    (hy : ∃ w0, s.locals.lookup y = some (.val (.word w0)))
    (he : ∀ callee : HolFiniteMapExact MlS (ValueHOL 64), callee.lookup a = some (.val (.word v)) →
      @evalHOLExact 64 σ _ (callEntryStateHOLFinite s callee).toExact
        (fun x => Classical.propDecidable ((callEntryStateHOLFinite s callee).memaddrs x)) e = some (.val (.word w))) :
    evaluateHOLFiniteState s (.call (some (some (.local, y), none)) f [arg]) =
      (none, setKvarHOLFinite .local y (.val (.word w)) { s with clock := s.clock - 1 }) := by
  obtain ⟨st, hq, hcall⟩ := ConPanqueque.Logic.call1 s f a y (.return e) arg v w
    (fun st => ∃ callee : HolFiniteMapExact MlS (ValueHOL 64), st = emptyLocalsHOLFinite (callEntryStateHOLFinite s callee))
    hc harg hclk hy (fun callee hcl => ⟨_, by
      rw [evaluateHOLFiniteState_eq_evaluate_def]; simp [he callee hcl, shapeOfHOLExact], callee, rfl⟩)
  obtain ⟨callee, rfl⟩ := hq
  rw [hcall]
  simp [emptyLocalsHOLFinite, callEntryStateHOLFinite, setKvarHOLFinite, setVarHOLFinite]
