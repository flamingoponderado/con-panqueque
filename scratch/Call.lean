import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- `x = f(args)` when the callee returns a value of its declared shape. -/
theorem call_assign {σ : Type} (s : PanSemStateFiniteExact 64 σ) (k : VarKind) (x f : MlS)
    (h : Option (MlS × MlS × ProgHOL 64)) (args : List (ExpHOL 64)) (vs : List (ValueHOL 64))
    (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64)) (rsh : ShapeHOL)
    (v : ValueHOL 64) (st : PanSemStateFiniteExact 64 σ)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vs)
    (hcode : lookupCodeHOLFinite s.code.lookup f vs = some (body, callee, rsh))
    (hclk : s.clock ≠ 0)
    (hbody : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = (some (.returned v), st))
    (hsh : shapeEqHOL (shapeOfHOLExact v) rsh = true)
    (hvalid : isValidValueHOLExact s.toExact k x v = true) :
    evaluateHOLFiniteState s (.call (some (some (k, x), h)) f args) =
      (none, setKvarHOLFinite k x v { st with locals := s.locals }) := by
  rw [evaluateHOLFiniteState_call]
  simp only [evalListHOLFinite] at hargs
  simp [hargs, hcode, hclk, hbody, hsh, hvalid]
