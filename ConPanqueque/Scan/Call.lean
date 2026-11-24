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

theorem lookupCode3 (s : PanSemStateFiniteExact 64 σ) (f x1 x2 x3 : MlS) (body : ProgHOL 64)
    (v1 v2 v3 : BitVec 64) (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hcode : s.code.lookup f = some ([(x1, .one), (x2, .one), (x3, .one)], body, .one)) :
    ∃ callee, lookupCodeHOLFinite s.code.lookup f [.val (.word v1), .val (.word v2), .val (.word v3)] =
        some (body, callee, .one) ∧
      callee.lookup x1 = some (.val (.word v1)) ∧ callee.lookup x2 = some (.val (.word v2)) ∧
      callee.lookup x3 = some (.val (.word v3)) := by
  unfold lookupCodeHOLFinite
  split
  · rename_i hh; simp [lookupCodeHOLExact, hcode, shapeOfHOLExact, shapeEqHOL] at hh
    exact absurd hh (by simp [h12, h13, h23])
  · rename_i b cl rs hh
    simp [lookupCodeHOLExact, hcode, shapeOfHOLExact, shapeEqHOL] at hh
    obtain ⟨_, rfl, rfl, rfl⟩ := hh
    exact ⟨_, rfl, by simp [h12, h13], by simp [h23], by simp⟩

/-- `x = f(a1, a2, a3)` at a three-parameter pure scanner function. -/
theorem call3_ret (s : PanSemStateFiniteExact 64 σ) (x f x1 x2 x3 : MlS) (body : ProgHOL 64)
    (a1 a2 a3 : ExpHOL 64) (v1 v2 v3 v w0 : BitVec 64) (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3)
    (hcode : s.code.lookup f = some ([(x1, .one), (x2, .one), (x3, .one)], body, .one))
    (ha1 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) a1 =
      some (.val (.word v1)))
    (ha2 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) a2 =
      some (.val (.word v2)))
    (ha3 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) a3 =
      some (.val (.word v3)))
    (hx : s.locals.lookup x = some (.val (.word w0)))
    (hbody : ∀ callee : HolFiniteMapExact MlS (ValueHOL 64),
      callee.lookup x1 = some (.val (.word v1)) → callee.lookup x2 = some (.val (.word v2)) →
      callee.lookup x3 = some (.val (.word v3)) → RetSpec (callEntryStateHOLFinite s callee) body v) :
    Stop (evaluateHOLFiniteState s (.call (some (some (.local, x), none)) f [a1, a2, a3])).1 ∨
      ∃ u, evaluateHOLFiniteState s (.call (some (some (.local, x), none)) f [a1, a2, a3]) = (none, u) ∧
        SetsLocal s x v u := by
  obtain ⟨callee, hlk, hx1, hx2, hx3⟩ := lookupCode3 s f x1 x2 x3 body v1 v2 v3 h12 h13 h23 hcode
  exact call_ret s x f [a1, a2, a3] _ body callee v w0
    (by simp [evalListHOLFinite, evalListHOLExact, ha1, ha2, ha3]) hlk (hbody callee hx1 hx2 hx3) hx

end

end ConPanqueque.Scan
