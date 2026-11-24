import ConPanqueque.Scan.Skip

/-! # Calling a pure scanner function

A scanner function reads the buffer and returns a word: `RetSpec t c v` says the body `c` run at
`t` stops, or returns `v` with the memory, its domain, the globals, the code and the byte order as
they were.  `call_ret` is the call statement `x = f(args)` at such a callee. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

namespace ConPanqueque.Scan

section
variable {σ : Type}

def RetSpec (t : PanSemStateFiniteExact 64 σ) (c : ProgHOL 64) (v : BitVec 64) : Prop :=
  Stop (evaluateHOLFiniteState t c).1 ∨
    ((evaluateHOLFiniteState t c).1 = some (.returned (.val (.word v))) ∧
      (evaluateHOLFiniteState t c).2.memory = t.memory ∧
      (evaluateHOLFiniteState t c).2.memaddrs = t.memaddrs ∧
      (evaluateHOLFiniteState t c).2.globals = t.globals ∧
      (evaluateHOLFiniteState t c).2.code = t.code ∧
      (evaluateHOLFiniteState t c).2.be = t.be)

/-- What a statement that only sets local `x` to `v` leaves. -/
def SetsLocal (s : PanSemStateFiniteExact 64 σ) (x : MlS) (v : BitVec 64)
    (u : PanSemStateFiniteExact 64 σ) : Prop :=
  u.memory = s.memory ∧ u.memaddrs = s.memaddrs ∧ u.globals = s.globals ∧ u.code = s.code ∧
    u.be = s.be ∧ u.locals.lookup x = some (.val (.word v)) ∧
    ∀ y, y ≠ x → u.locals.lookup y = s.locals.lookup y

theorem call_ret (s : PanSemStateFiniteExact 64 σ) (x f : MlS) (args : List (ExpHOL 64))
    (vs : List (ValueHOL 64)) (body : ProgHOL 64) (callee : HolFiniteMapExact MlS (ValueHOL 64))
    (v w0 : BitVec 64)
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vs)
    (hcode : lookupCodeHOLFinite s.code.lookup f vs = some (body, callee, .one))
    (hbody : RetSpec (callEntryStateHOLFinite s callee) body v)
    (hx : s.locals.lookup x = some (.val (.word w0))) :
    Stop (evaluateHOLFiniteState s (.call (some (some (.local, x), none)) f args)).1 ∨
      ∃ u, evaluateHOLFiniteState s (.call (some (some (.local, x), none)) f args) = (none, u) ∧
        SetsLocal s x v u := by
  rw [evaluateHOLFiniteState_call]
  simp only [evalListHOLFinite] at hargs
  by_cases hck : s.clock = 0
  · left; simp [hargs, hcode, hck, Stop]
  rcases hbody with hst | ⟨hr, hm, hd, hg, hc, hb⟩
  · left
    generalize he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = r at hst
    obtain ⟨r1, r2⟩ := r
    simp only at hst
    rcases hst with e | ⟨ev, e⟩ <;> subst e <;> simp [hargs, hcode, hck, he, Stop]
  · right
    generalize he : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = r at hr hm hd hg hc hb
    obtain ⟨r1, r2⟩ := r
    simp only at hr hm hd hg hc hb
    subst hr
    have hv : isValidValueHOLExact s.toExact .local x (.val (.word v)) = true := by
      simp [isValidValueHOLExact, lookupKvarHOLExact, hx, shapeOfHOLExact, shapeEqHOL]
    refine ⟨setKvarHOLFinite .local x (.val (.word v)) { r2 with locals := s.locals }, ?_, ?_⟩
    · simp [hargs, hcode, hck, he, shapeOfHOLExact, shapeEqHOL, hv]
    · exact ⟨hm, hd, hg, hc, hb, lookup_setVar_same _ _ _, fun y hy => by
        show (setVarHOLFinite x _ _).locals.lookup y = _
        rw [lookup_setVar_other _ _ hy]⟩

end

end ConPanqueque.Scan
