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
  exact ⟨hp', ainv_of_eq a rfl rfl rfl, ⟨g.le, g.mem, g.low⟩, by rw [hOf_of_eq lo hp' rfl]; exact p, cd, ck, gl, md, ta⟩

/-- A two-parameter call to an allocating function, then `rest`. -/
theorem call_child {σ : Type} (fn x p1 p2 : MlS) (C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (B rest : ProgHOL 64) (hne : p1 ≠ p2) (hC : C.lookup fn = some ([(p1, .one), (p2, .one)], B, .one))
    (P : Heap → BitVec 64 → Prop) (cc : Nat) (t : PanSemStateFiniteExact 64 σ) (lo hp a1 a2 : BitVec 64)
    (e1 e2 : ExpHOL 64) (hcode : t.code = C) (hi : AInv t lo hp)
    (he1 : @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e1 = some (.val (.word a1)))
    (he2 : @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e2 = some (.val (.word a2)))
    (hx : ∃ w0, t.locals.lookup x = some (.val (.word w0))) (hck : 1 + cc ≤ t.clock)
    (hB : ∀ s' : PanSemStateFiniteExact 64 σ, s'.code = C → AInv s' lo hp → s'.memory = t.memory →
      s'.globals = t.globals →
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
  rcases hB s' (by simp [s', callEntryStateHOLFinite, hcode]) (ainv_of_eq hi rfl rfl rfl) rfl rfl hx1 hx2
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
  · exact ⟨g.le, fun b h1 h2 => by simpa [t', setKvarHOLFinite, setVarHOLFinite, s', callEntryStateHOLFinite] using g.mem b h1 h2,
      fun b h1 => by simpa [t', setKvarHOLFinite, setVarHOLFinite, s', callEntryStateHOLFinite] using g.low b h1⟩
  · rw [hOf_of_eq (s := st) lo hp' (by simp [t', setKvarHOLFinite, setVarHOLFinite])]; exact pq
  · simp [t', setKvarHOLFinite, setVarHOLFinite, FUPDATE]
  · intro y hy; simp only [t', setKvarHOLFinite]; exact lookup_setVar_other _ _ hy
  · simp [t', setKvarHOLFinite, setVarHOLFinite, cd, s', callEntryStateHOLFinite]
  · simp [t', setKvarHOLFinite, setVarHOLFinite]; simp [s', callEntryStateHOLFinite] at ck; omega
  · intro g' hg'; simpa [t', setKvarHOLFinite, setVarHOLFinite, s', callEntryStateHOLFinite] using gl g' hg'
  · simpa [t', setKvarHOLFinite, setVarHOLFinite, s', callEntryStateHOLFinite] using md
  · simpa [t', setKvarHOLFinite, setVarHOLFinite, s', callEntryStateHOLFinite] using ta

theorem ok_trans {σ : Type} {t t' st : PanSemStateFiniteExact 64 σ} {lo hp hq : BitVec 64}
    {P : Heap → BitVec 64 → Prop} {c c' : Nat} {q : BitVec 64} (h : ROk t' st lo hq P c' q)
    (g : Grows t t' lo hp hq) (cd : t'.code = t.code) (ck : t.clock ≤ t'.clock + c)
    (gl : ∀ g, g ≠ nHp → t'.globals.lookup g = t.globals.lookup g) (md : t'.memaddrs = t.memaddrs)
    (ta : t'.topAddr = t.topAddr) : ROk t st lo hp P (c + c') q := by
  obtain ⟨hp', a, g', pq, cd', ck', gl', md', ta'⟩ := h
  exact ⟨hp', a, grows_trans g g', pq, by rw [cd', cd], by omega, fun x hx => by rw [gl' x hx, gl x hx],
    by rw [md', md], by rw [ta', ta]⟩

theorem rres_trans {σ : Type} {t t' : PanSemStateFiniteExact 64 σ} {r : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ}
    {lo hp hq : BitVec 64} {P : Heap → BitVec 64 → Prop} {c c' : Nat} (h : RRes t' r lo hq P c')
    (g : Grows t t' lo hp hq) (cd : t'.code = t.code) (ck : t.clock ≤ t'.clock + c)
    (gl : ∀ g, g ≠ nHp → t'.globals.lookup g = t.globals.lookup g) (md : t'.memaddrs = t.memaddrs)
    (ta : t'.topAddr = t.topAddr) : RRes t r lo hp P (c + c') := by
  rcases h with h | ⟨q, hr, ok⟩
  · exact Or.inl h
  · exact Or.inr ⟨q, hr, ok_trans ok g cd ck gl md ta⟩

theorem rres_locals' {σ : Type} {t : PanSemStateFiniteExact 64 σ} {r1 : Option (PanSemResultExact 64)}
    {st : PanSemStateFiniteExact 64 σ} {lo hp : BitVec 64} {P : Heap → BitVec 64 → Prop} {c : Nat}
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (h : RRes t (r1, st) lo hp P c) :
    RRes t (r1, { st with locals := L }) lo hp P c := by
  rcases h with h | ⟨q, hr, ok⟩
  · exact Or.inl h
  · obtain ⟨hp', a, g, pq, cd, ck, gl, md, ta⟩ := ok
    exact Or.inr ⟨q, hr, hp', ainv_of_eq a rfl rfl rfl, ⟨g.le, g.mem, g.low⟩, by rw [hOf_of_eq lo hp' rfl]; exact pq,
      cd, ck, gl, md, ta⟩

/-- `var x = 0; x := fn(e1, e2); rest`: the call, then `rest` from the state with `x` bound. -/
theorem step_call {σ : Type} (fn x p1 p2 : MlS) (C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (B rest : ProgHOL 64) (hne : p1 ≠ p2) (hC : C.lookup fn = some ([(p1, .one), (p2, .one)], B, .one))
    (P1 P : Heap → BitVec 64 → Prop) (c1 c' : Nat) (t : PanSemStateFiniteExact 64 σ) (lo hp a1 a2 : BitVec 64)
    (e1 e2 : ExpHOL 64) (hcode : t.code = C) (hi : AInv t lo hp)
    (he1 : @evalHOLExact 64 σ _ (setVarHOLFinite x (.val (.word 0)) t).toExact
      (fun a => Classical.propDecidable (t.memaddrs a)) e1 = some (.val (.word a1)))
    (he2 : @evalHOLExact 64 σ _ (setVarHOLFinite x (.val (.word 0)) t).toExact
      (fun a => Classical.propDecidable (t.memaddrs a)) e2 = some (.val (.word a2)))
    (hck : 1 + c1 ≤ t.clock)
    (hB : ∀ s' : PanSemStateFiniteExact 64 σ, s'.code = C → AInv s' lo hp → s'.memory = t.memory →
      s'.globals = t.globals → s'.locals.lookup p1 = some (.val (.word a1)) →
      s'.locals.lookup p2 = some (.val (.word a2)) → c1 ≤ s'.clock → RRes s' (evaluateHOLFiniteState s' B) lo hp P1 c1)
    (hrest : ∀ (t' : PanSemStateFiniteExact 64 σ) (q hq : BitVec 64), t'.code = C → AInv t' lo hq →
      Grows t t' lo hp hq → P1 (hOf t' lo hq) q → t'.locals.lookup x = some (.val (.word q)) →
      (∀ y, y ≠ x → t'.locals.lookup y = t.locals.lookup y) → t.clock ≤ t'.clock + 1 + c1 →
      (∀ g, g ≠ nHp → t'.globals.lookup g = t.globals.lookup g) → t'.memaddrs = t.memaddrs →
      t'.topAddr = t.topAddr → RRes t' (evaluateHOLFiniteState t' rest) lo hq P c') :
    RRes t (evaluateHOLFiniteState t (.dec x .one (.const 0) (.seq (.call (some (some (.local, x), none)) fn [e1, e2]) rest)))
      lo hp P (1 + c1 + c') := by
  let t1 := setVarHOLFinite x (.val (.word 0)) t
  obtain ⟨L1, e1'⟩ := dec_word' t x (.const 0) 0 (.seq (.call (some (some (.local, x), none)) fn [e1, e2]) rest)
    (by simp [evalHOLExact])
  rw [e1']; apply rres_locals'
  rcases call_child fn x p1 p2 C B rest hne hC P1 c1 t1 lo hp a1 a2 e1 e2 hcode (ainv_of_eq hi rfl rfl rfl) he1 he2
      ⟨0, by simp [t1]⟩ hck (fun s' a b c d f g h' => hB s' a b c d f g h') with
    hs | ⟨t2, q, hq, ev, a2', g2, p2', lx, lo2, cd2, ck2, gl2, md2, ta2⟩
  · exact Or.inl hs
  rw [ev]
  have lo2' : ∀ y, y ≠ x → t2.locals.lookup y = t.locals.lookup y := by
    intro y hy; rw [lo2 y hy]; simp only [t1]; exact lookup_setVar_other _ _ hy
  have := hrest t2 q hq (by rw [cd2]; exact hcode) a2' ⟨g2.le, g2.mem, g2.low⟩ p2' lx lo2' ck2 gl2 md2 ta2
  have h' := rres_trans (t := t) (c := 1 + c1) this ⟨g2.le, g2.mem, g2.low⟩ cd2
    (by have : t1.clock = t.clock := rfl; omega) gl2 md2 ta2
  exact h'

/-- `var y = 0; y := f(e); rest` for a one-parameter function that allocates nothing:
`rest` runs from the state with `y` bound, the arena unchanged. -/
theorem pure_step {σ : Type} (f x y : MlS) (B rest : ProgHOL 64) (P : Heap → BitVec 64 → Prop) (c c' : Nat)
    (t : PanSemStateFiniteExact 64 σ) (lo hp a w : BitVec 64) (e : ExpHOL 64) (hi : AInv t lo hp)
    (hcode : t.code.lookup f = some ([(x, .one)], B, .one))
    (he : @evalHOLExact 64 σ _ (setVarHOLFinite y (.val (.word 0)) t).toExact
      (fun a => Classical.propDecidable (t.memaddrs a)) e = some (.val (.word a)))
    (hck : 1 + c ≤ t.clock)
    (hB : ∀ s' : PanSemStateFiniteExact 64 σ, s'.code = t.code → s'.memory = t.memory → s'.memaddrs = t.memaddrs →
      s'.globals = t.globals → s'.locals.lookup x = some (.val (.word a)) → c ≤ s'.clock →
      ∃ st, evaluateHOLFiniteState s' B = (some (.returned (.val (.word w))), st) ∧
        st.code = s'.code ∧ st.memory = s'.memory ∧ st.memaddrs = s'.memaddrs ∧ s'.clock ≤ st.clock + c ∧
        st.globals = s'.globals ∧ st.topAddr = s'.topAddr)
    (hrest : ∀ t' : PanSemStateFiniteExact 64 σ, t'.locals.lookup y = some (.val (.word w)) →
      (∀ z, z ≠ y → t'.locals.lookup z = t.locals.lookup z) → t'.memory = t.memory → t'.code = t.code →
      t'.globals = t.globals → t'.memaddrs = t.memaddrs → t'.topAddr = t.topAddr → t.clock ≤ t'.clock + 1 + c →
      RRes t' (evaluateHOLFiniteState t' rest) lo hp P c') :
    RRes t (evaluateHOLFiniteState t (.dec y .one (.const 0) (.seq (.call (some (some (.local, y), none)) f [e]) rest)))
      lo hp P (1 + c + c') := by
  let t1 := setVarHOLFinite y (.val (.word 0)) t
  obtain ⟨L1, e1⟩ := dec_word' t y (.const 0) 0 (.seq (.call (some (some (.local, y), none)) f [e]) rest)
    (by simp [evalHOLExact])
  obtain ⟨st, ⟨cd, mm, md, ck, gl, ta⟩, hcall⟩ := call1 t1 f x y B e a w
    (fun st => st.code = t.code ∧ st.memory = t.memory ∧ st.memaddrs = t.memaddrs ∧ t.clock - 1 ≤ st.clock + c ∧
      st.globals = t.globals ∧ st.topAddr = t.topAddr)
    hcode he (by show t.clock ≠ 0; omega) ⟨0, by simp [t1]⟩
    (fun callee hx => by
      obtain ⟨st, ev, a1, a2, a3, a4, a5, a6⟩ := hB (callEntryStateHOLFinite t1 callee) rfl rfl rfl rfl hx
        (by show c ≤ t.clock - 1; omega)
      exact ⟨st, ev, a1, a2, a3, a4, a5, a6⟩)
  rw [e1]; apply rres_locals'; rw [seq_normal _ hcall]
  let t2 := setKvarHOLFinite .local y (.val (.word w)) { st with locals := t1.locals }
  have := hrest t2 (by simp [t2, setKvarHOLFinite])
    (fun z hz => by simp only [t2, setKvarHOLFinite, t1]; rw [lookup_setVar_other _ _ hz, lookup_setVar_other _ _ hz])
    (by simp [t2, setKvarHOLFinite, setVarHOLFinite, mm]) (by simp [t2, setKvarHOLFinite, setVarHOLFinite, cd])
    (by simp [t2, setKvarHOLFinite, setVarHOLFinite, gl]) (by simp [t2, setKvarHOLFinite, setVarHOLFinite, md])
    (by simp [t2, setKvarHOLFinite, setVarHOLFinite, ta])
    (by simp [t2, setKvarHOLFinite, setVarHOLFinite]; omega)
  have hm2 : t2.memory = t.memory := by simp [t2, setKvarHOLFinite, setVarHOLFinite, mm]
  exact rres_trans (t := t) (c := 1 + c) this ⟨BitVec.le_refl _, fun b _ _ => by rw [hm2], fun b _ => by rw [hm2]⟩
    (by simp [t2, setKvarHOLFinite, setVarHOLFinite, cd]) (by simp [t2, setKvarHOLFinite, setVarHOLFinite]; omega)
    (fun g _ => by simp [t2, setKvarHOLFinite, setVarHOLFinite, gl]) (by simp [t2, setKvarHOLFinite, setVarHOLFinite, md])
    (by simp [t2, setKvarHOLFinite, setVarHOLFinite, ta])

end ConPanqueque.Rebuild
