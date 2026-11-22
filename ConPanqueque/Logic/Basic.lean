import Flapjack.Pancake.Semantics.PanSem.EvaluateClock

/-!
# A program logic over Flapjack's Pancake semantics (beginning)

Flapjack ports Pancake's semantics (`evaluateHOLFiniteState`, with the
per-construct equations `evaluateHOLFiniteState_eq_evaluate_def`) and its
compiler; it has no program logic. Proofs that con-panqueque's Pancake code
refines con-leche's functions are built here, one construct at a time.

First step: an expression of local words, returned.
-/

namespace ConPanqueque.Logic
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- `return a + b` on two local words returns their (wrapping) sum. -/
theorem return_add {σ : Type} (s : PanSemStateFiniteExact 64 σ) (a b : MlS) (x y : BitVec 64)
    (ha : s.locals.lookup a = some (.val (.word x)))
    (hb : s.locals.lookup b = some (.val (.word y))) :
    (evaluateHOLFiniteState s (.return (.op .add [.var .local a, .var .local b]))).1 =
      some (.returned (.val (.word (x + y)))) := by
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  simp only
  simp [evalHOLExact, evalListHOLExact, ha, hb, wordOpHOL, wordOp, valueIsWord, valueWord,
    shapeOfHOLExact]

/-! ## Structural rules -/

/-- `p; q` after `p` finished normally is `q`. -/
theorem seq_normal {σ : Type} {s s₁ : PanSemStateFiniteExact 64 σ} {p : ProgHOL 64} (q : ProgHOL 64)
    (h : evaluateHOLFiniteState s p = (none, s₁)) :
    evaluateHOLFiniteState s (.seq p q) = evaluateHOLFiniteState s₁ q := by
  rw [evaluateHOLFiniteState_eq_evaluate_def s (.seq p q)]
  simp only [h]

/-- An assignment of an expression's value, when the value fits the variable. -/
theorem assign_ok {σ : Type} (s : PanSemStateFiniteExact 64 σ) (k : VarKind) (n : MlS)
    (e : ExpHOL 64) (v : ValueHOL 64)
    (he : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some v)
    (hv : isValidValueHOLFinite s k n v = true) :
    evaluateHOLFiniteState s (.assign k n e) = (none, setKvarHOLFinite k n v s) := by
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  simp only [he, hv, ite_true]

/-! ## Locals -/

@[simp] theorem lookup_setVar_same {σ : Type} (s : PanSemStateFiniteExact 64 σ) (n : MlS)
    (v : ValueHOL 64) : (setVarHOLFinite n v s).locals.lookup n = some v := by
  simp [setVarHOLFinite, FUPDATE]

theorem lookup_setVar_other {σ : Type} (s : PanSemStateFiniteExact 64 σ) {n m : MlS}
    (v : ValueHOL 64) (h : m ≠ n) :
    (setVarHOLFinite n v s).locals.lookup m = s.locals.lookup m := by
  simp [setVarHOLFinite, FUPDATE, Ne.symm h]

/-! ## Loops -/

/-- Loop rule: an invariant `I` and a measure `m` bounded by the clock. While the
condition holds (a nonzero word), the body ends normally in a state satisfying `I`
with a smaller measure; when it is zero the loop ends normally. -/
theorem while_rule {σ : Type} (c : ExpHOL 64) (body : ProgHOL 64)
    (I : PanSemStateFiniteExact 64 σ → Prop) (m : PanSemStateFiniteExact 64 σ → Nat)
    (Q : PanSemStateFiniteExact 64 σ → Prop)
    (hc : ∀ s, I s → ∃ w : BitVec 64,
      @evalHOLFinite 64 σ _ s (fun a => Classical.propDecidable (s.memaddrs a)) c = some (.val (.word w)) ∧
      (w = 0 → Q s) ∧
      (w ≠ 0 → m s ≤ s.clock ∧ 0 < m s ∧ ∃ s', evaluateHOLFiniteState (decClockHOLFinite s) body = (none, s') ∧
        I s' ∧ m s' < m s)) :
    ∀ s, I s → ∃ s', evaluateHOLFiniteState s (.while c body) = (none, s') ∧ Q s' := by
  intro s hs
  induction h : m s using Nat.strongRecOn generalizing s with
  | _ n ih =>
    obtain ⟨w, hw, h0, h1⟩ := hc s hs
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.while c body)]
    by_cases hw0 : w = 0
    · subst hw0; simp only [hw]; exact ⟨s, by simp, h0 rfl⟩
    · obtain ⟨hclk, hpos, s', hb, hs', hlt⟩ := h1 hw0
      have hck : s.clock ≠ 0 := by omega
      simp only [hw, ne_eq, hw0, not_false_eq_true, ite_true, hck, ite_false, hb]
      exact ih (m s') (by omega) s' hs' rfl

/-! ## Memory -/

/-- A one-word store to an address in the memory domain. -/
theorem store_word {σ : Type} (s : PanSemStateFiniteExact 64 σ) (dst src : ExpHOL 64)
    (a w : BitVec 64)
    (hd : @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) dst =
      some (.val (.word a)))
    (hs : @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) src =
      some (.val (.word w)))
    (hdom : s.memaddrs a) :
    evaluateHOLFiniteState s (.store dst src) =
      (none, { s with memory := fun c => if c = a then .word w else s.memory c }) := by
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  simp [hd, hs, flattenHOL, panMemStoresHOL, panMemStoreHOL, hdom]

/-- A one-word load from an address in the memory domain. -/
theorem eval_load_word {σ : Type} (s : PanSemStateFiniteExact 64 σ) (e : ExpHOL 64) (a : BitVec 64)
    (he : @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e =
      some (.val (.word a)))
    (hdom : s.memaddrs a) :
    @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) (.load .one e) =
      some (.val (s.memory a)) := by
  simp [evalHOLExact, he, memLoadHOLExact, hdom]

/-! ## Calls -/

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

/-! ## Declarations -/

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

/-! ## One-parameter calls -/

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
  apply call_assign s .local y f none [arg] [.val (.word v)] body _ .one _ st
  · simp [evalListHOLFinite, evalListHOLExact, harg]
  · exact hlk
  · exact hclk
  · exact hb
  · simp [shapeOfHOLExact, shapeEqHOL]
  · simp [isValidValueHOLExact, lookupKvarHOLExact, hw0, shapeOfHOLExact, shapeEqHOL]

theorem lookupCode2 {σ : Type} (s : PanSemStateFiniteExact 64 σ) (f x1 x2 : MlS) (body : ProgHOL 64)
    (v1 v2 : BitVec 64) (hne : x1 ≠ x2) (hcode : s.code.lookup f = some ([(x1, .one), (x2, .one)], body, .one)) :
    ∃ callee, lookupCodeHOLFinite s.code.lookup f [.val (.word v1), .val (.word v2)] = some (body, callee, .one) ∧
      callee.lookup x1 = some (.val (.word v1)) ∧ callee.lookup x2 = some (.val (.word v2)) := by
  unfold lookupCodeHOLFinite
  split
  · rename_i hh; simp [lookupCodeHOLExact, hcode, shapeOfHOLExact, shapeEqHOL] at hh; exact absurd hh hne
  · rename_i b cl rs hh
    simp [lookupCodeHOLExact, hcode, shapeOfHOLExact, shapeEqHOL] at hh
    obtain ⟨_, rfl, rfl, rfl⟩ := hh
    exact ⟨_, rfl, by simp [hne], by simp⟩

/-- `y = f(arg1, arg2)` for a two-parameter word function. -/
theorem call2 {σ : Type} (s : PanSemStateFiniteExact 64 σ) (f x1 x2 y : MlS) (body : ProgHOL 64)
    (arg1 arg2 : ExpHOL 64) (v1 v2 w : BitVec 64) (Q : PanSemStateFiniteExact 64 σ → Prop) (hne : x1 ≠ x2)
    (hcode : s.code.lookup f = some ([(x1, .one), (x2, .one)], body, .one))
    (harg1 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) arg1 =
      some (.val (.word v1)))
    (harg2 : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) arg2 =
      some (.val (.word v2)))
    (hclk : s.clock ≠ 0)
    (hy : ∃ w0, s.locals.lookup y = some (.val (.word w0)))
    (hbody : ∀ callee : HolFiniteMapExact MlS (ValueHOL 64), callee.lookup x1 = some (.val (.word v1)) →
      callee.lookup x2 = some (.val (.word v2)) →
      ∃ st, evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body =
        (some (.returned (.val (.word w))), st) ∧ Q st) :
    ∃ st, Q st ∧ evaluateHOLFiniteState s (.call (some (some (.local, y), none)) f [arg1, arg2]) =
        (none, setKvarHOLFinite .local y (.val (.word w)) { st with locals := s.locals }) := by
  obtain ⟨hlk, hx1, hx2⟩ := Classical.choose_spec (lookupCode2 s f x1 x2 body v1 v2 hne hcode)
  obtain ⟨st, hb, hq⟩ := hbody _ hx1 hx2
  obtain ⟨w0, hw0⟩ := hy
  refine ⟨st, hq, ?_⟩
  apply call_assign s .local y f none [arg1, arg2] [.val (.word v1), .val (.word v2)] body _ .one _ st
  · simp [evalListHOLFinite, evalListHOLExact, harg1, harg2]
  · exact hlk
  · exact hclk
  · exact hb
  · simp [shapeOfHOLExact, shapeEqHOL]
  · simp [isValidValueHOLExact, lookupKvarHOLExact, hw0, shapeOfHOLExact, shapeEqHOL]

/-! ## Conditionals and declarations (state-level) -/

theorem ite_word {σ : Type} (s : PanSemStateFiniteExact 64 σ) (c : ExpHOL 64) (p q : ProgHOL 64) (w : BitVec 64)
    (hc : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) c =
      some (.val (.word w))) :
    evaluateHOLFiniteState s (.ite c p q) =
      if w ≠ 0 then evaluateHOLFiniteState s p else evaluateHOLFiniteState s q := by
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  simp only
  rw [hc]
  by_cases hw : w = 0 <;> simp [hw]

theorem dec_word' {σ : Type} (s : PanSemStateFiniteExact 64 σ) (x : MlS) (e : ExpHOL 64) (v : BitVec 64)
    (body : ProgHOL 64)
    (he : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e =
      some (.val (.word v))) :
    ∃ L, evaluateHOLFiniteState s (.dec x .one e body) =
      ((evaluateHOLFiniteState (setVarHOLFinite x (.val (.word v)) s) body).1,
       { (evaluateHOLFiniteState (setVarHOLFinite x (.val (.word v)) s) body).2 with locals := L }) := by
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  simp [he, shapeOfHOLExact, shapeEqHOL]

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
  obtain ⟨st, hq, hcall⟩ := call1 s f a y (.return e) arg v w
    (fun st => ∃ callee : HolFiniteMapExact MlS (ValueHOL 64), st = emptyLocalsHOLFinite (callEntryStateHOLFinite s callee))
    hc harg hclk hy (fun callee hcl => ⟨_, by
      rw [evaluateHOLFiniteState_eq_evaluate_def]; simp [he callee hcl, shapeOfHOLExact], callee, rfl⟩)
  obtain ⟨callee, rfl⟩ := hq
  rw [hcall]
  simp [emptyLocalsHOLFinite, callEntryStateHOLFinite, setKvarHOLFinite, setVarHOLFinite]

end ConPanqueque.Logic
