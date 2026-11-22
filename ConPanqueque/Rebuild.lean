import ConPanqueque.StateHeap
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic ConPanqueque.Alloc ConPanqueque.ExprCons
open ConPanqueque.Node ConPanqueque.StateHeap

/-!
# Allocating recursions: results and child calls

`ROk s st lo hp P c q`: a function body run from `s` ended in `st` returning the
word `q`, which satisfies `P` in `st`'s arena; the arena grew; code and the other
globals are unchanged; at most `c` clock ticks were used. `call_child`: a call
`x := fn(a₁, a₂)` to such a function, then `rest`: either the program stops, or
`rest` runs from a state where `x` holds the result.
-/

namespace ConPanqueque.Rebuild

def ROk {σ : Type} (s st : PanSemStateFiniteExact 64 σ) (lo hp : BitVec 64) (P : Heap → BitVec 64 → Prop)
    (c : Nat) (q : BitVec 64) : Prop :=
  ∃ hp', AInv st lo hp' ∧ Grows s st lo hp hp' ∧ P (hOf st lo hp') q ∧ st.code = s.code ∧
    s.clock ≤ st.clock + c ∧ (∀ g, g ≠ nHp → st.globals.lookup g = s.globals.lookup g) ∧
    st.memaddrs = s.memaddrs ∧ st.topAddr = s.topAddr

/-- What a function body does: stop, or return a word with `ROk`. -/
def RRes {σ : Type} (s : PanSemStateFiniteExact 64 σ) (r : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ)
    (lo hp : BitVec 64) (P : Heap → BitVec 64 → Prop) (c : Nat) : Prop :=
  Stop r.1 ∨ ∃ q, r.1 = some (.returned (.val (.word q))) ∧ ROk s r.2 lo hp P c q

theorem ok_locals {σ : Type} {s st : PanSemStateFiniteExact 64 σ} {lo hp : BitVec 64} {P : Heap → BitVec 64 → Prop}
    {c : Nat} {q : BitVec 64} (L : HolFiniteMapExact MlS (ValueHOL 64)) (h : ROk s st lo hp P c q) :
    ROk s { st with locals := L } lo hp P c q := by
  obtain ⟨hp', a, g, p, cd, ck, gl, md, ta⟩ := h
  exact ⟨hp', ainv_of_eq a rfl rfl rfl, ⟨g.le, g.mem⟩, by rw [hOf_of_eq lo hp' rfl]; exact p, cd, ck, gl, md, ta⟩

/-- A two-parameter call to an allocating function, then `rest`. -/
theorem call_child {σ : Type} (fn x p1 p2 : MlS) (C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (B rest : ProgHOL 64) (hne : p1 ≠ p2) (hC : C.lookup fn = some ([(p1, .one), (p2, .one)], B, .one))
    (P : Heap → BitVec 64 → Prop) (cc : Nat) (t : PanSemStateFiniteExact 64 σ) (lo hp a1 a2 : BitVec 64)
    (e1 e2 : ExpHOL 64) (hcode : t.code = C) (hi : AInv t lo hp)
    (he1 : @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e1 = some (.val (.word a1)))
    (he2 : @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e2 = some (.val (.word a2)))
    (hx : ∃ w0, t.locals.lookup x = some (.val (.word w0))) (hck : 1 + cc ≤ t.clock)
    (hB : ∀ s' : PanSemStateFiniteExact 64 σ, s'.code = C → AInv s' lo hp → s'.memory = t.memory →
      s'.locals.lookup p1 = some (.val (.word a1)) → s'.locals.lookup p2 = some (.val (.word a2)) →
      cc ≤ s'.clock → RRes s' (evaluateHOLFiniteState s' B) lo hp P cc) :
    Stop (evaluateHOLFiniteState t (.seq (.call (some (some (.local, x), none)) fn [e1, e2]) rest)).1 ∨
      ∃ t' q hp', evaluateHOLFiniteState t (.seq (.call (some (some (.local, x), none)) fn [e1, e2]) rest) =
          evaluateHOLFiniteState t' rest ∧
        AInv t' lo hp' ∧ Grows t t' lo hp hp' ∧ P (hOf t' lo hp') q ∧
        t'.locals.lookup x = some (.val (.word q)) ∧ (∀ y, y ≠ x → t'.locals.lookup y = t.locals.lookup y) ∧
        t'.code = t.code ∧ t.clock ≤ t'.clock + 1 + cc ∧ (∀ g, g ≠ nHp → t'.globals.lookup g = t.globals.lookup g) ∧
        t'.memaddrs = t.memaddrs ∧ t'.topAddr = t.topAddr := by
  have hcode' : t.code.lookup fn = some ([(p1, .one), (p2, .one)], B, .one) := by rw [hcode]; exact hC
  obtain ⟨callee, hlk, hx1, hx2⟩ := lookupCode2 t fn p1 p2 B a1 a2 hne hcode'
  have hargs : evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) [e1, e2] =
      some [.val (.word a1), .val (.word a2)] := by
    simp [evalListHOLFinite, evalListHOLExact, he1, he2]
  let s' := callEntryStateHOLFinite t callee
  have hs'clk : s'.clock = t.clock - 1 := rfl
  rcases hB s' (by simp [s', callEntryStateHOLFinite, hcode]) (ainv_of_eq hi rfl rfl rfl) rfl hx1 hx2
      (by simp [s', callEntryStateHOLFinite]; omega) with hs | ⟨q, hr, ok⟩
  · left; apply seq_stop
    exact call_stop t _ fn [e1, e2] _ B callee .one hargs hlk hs
  right
  obtain ⟨hp', a, g, pq, cd, ck, gl, md, ta⟩ := ok
  obtain ⟨w0, hw0⟩ := hx
  generalize hst : evaluateHOLFiniteState s' B = r at hr a g pq cd ck gl md ta
  obtain ⟨r1, st⟩ := r
  simp only at hr a g pq cd ck gl md ta
  subst hr
  have hcall := call_assign t .local x fn none [e1, e2] _ B callee .one (.val (.word q)) st hargs hlk
    (by omega) hst (by simp [shapeOfHOLExact, shapeEqHOL])
    (by simp [isValidValueHOLExact, lookupKvarHOLExact, hw0, shapeOfHOLExact, shapeEqHOL])
  let t' := setKvarHOLFinite .local x (.val (.word q)) { st with locals := t.locals }
  refine ⟨t', q, hp', by rw [seq_normal _ hcall], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ainv_of_eq a (by simp [t', setKvarHOLFinite, setVarHOLFinite]) (by simp [t', setKvarHOLFinite, setVarHOLFinite])
      (by simp [t', setKvarHOLFinite, setVarHOLFinite])
  · exact ⟨g.le, fun b h1 h2 => by simpa [t', setKvarHOLFinite, setVarHOLFinite, s', callEntryStateHOLFinite] using g.mem b h1 h2⟩
  · rw [hOf_of_eq (s := st) lo hp' (by simp [t', setKvarHOLFinite, setVarHOLFinite])]; exact pq
  · simp [t', setKvarHOLFinite, setVarHOLFinite, FUPDATE]
  · intro y hy; simp only [t', setKvarHOLFinite]; exact lookup_setVar_other _ _ hy
  · simp [t', setKvarHOLFinite, setVarHOLFinite, cd, s', callEntryStateHOLFinite]
  · simp [t', setKvarHOLFinite, setVarHOLFinite]; simp [s', callEntryStateHOLFinite] at ck; omega
  · intro g' hg'; simpa [t', setKvarHOLFinite, setVarHOLFinite, s', callEntryStateHOLFinite] using gl g' hg'
  · simpa [t', setKvarHOLFinite, setVarHOLFinite, s', callEntryStateHOLFinite] using md
  · simpa [t', setKvarHOLFinite, setVarHOLFinite, s', callEntryStateHOLFinite] using ta

end ConPanqueque.Rebuild
