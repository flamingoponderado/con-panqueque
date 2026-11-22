import ConPanqueque.Logic.Basic
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- `var x = e; body` with `e` a word: the body runs with `x` set; its result and
everything but the locals pass through. -/
theorem dec_word {σ : Type} (s : PanSemStateFiniteExact 64 σ) (x : MlS) (e : ExpHOL 64) (v : BitVec 64)
    (body : ProgHOL 64)
    (he : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
      some (.val (.word v))) :
    let o := evaluateHOLFiniteState (setVarHOLFinite x (.val (.word v)) s) body
    (evaluateHOLFiniteState s (.dec x .one e body)).1 = o.1 ∧
    (evaluateHOLFiniteState s (.dec x .one e body)).2.memory = o.2.memory ∧
    (evaluateHOLFiniteState s (.dec x .one e body)).2.memaddrs = o.2.memaddrs ∧
    (evaluateHOLFiniteState s (.dec x .one e body)).2.globals = o.2.globals ∧
    (evaluateHOLFiniteState s (.dec x .one e body)).2.topAddr = o.2.topAddr := by
  intro o
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  simp [he, shapeOfHOLExact, shapeEqHOL, o]
