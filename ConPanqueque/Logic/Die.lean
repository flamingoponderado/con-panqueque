import ConPanqueque.Logic.Stop

/-! # One failure function: `hang` as a tail call to `die`

The proved program writes every failure exit as `hang` (`reject`, then an endless loop).  Inlined
8000 times, those loops make `cake --pancake`'s register allocation very slow (each loop keeps every
local of its scope live).  The emitted program instead replaces each `hang` by the tail call
`return die();` and adds one function `die` whose body is `hang`.

`dieT` performs that replacement; `dieCode` builds the emitted code table from the proved one.
`dieT_sim`: running the emitted program (from a state whose code table is the emitted one) either
stops (`Stop`: out of clock or a final FFI event) or gives exactly the result of the proved program,
with the same state apart from the code table.  The proved soundness theorem therefore carries over
to the emitted program (`ConPanqueque/Start/Main4.lean`). -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString

namespace ConPanqueque.Logic

/-- The failure function. -/
def fDie := ofString "die"
def dieEntry : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL := ([], hang, .one)
/-- `return die();` -/
def dieCall : ProgHOL 64 := .call none fDie []

/-- Is this program `hang`? -/
def isHang : ProgHOL 64 → Bool
  | .seq (.extCall f (.const a) (.const b) (.const c) (.const d))
      (.seq (.while (.const w) .skip) (.return (.const z))) =>
    decide (f = fReject) && a == 0 && b == 0 && c == 0 && d == 0 && w == 1 && z == 0
  | _ => false

/-- Replace every `hang` by `return die();`. -/
def dieT : ProgHOL 64 → ProgHOL 64
  | .dec n sh e b => .dec n sh e (dieT b)
  | .seq a b => if isHang (.seq a b) then dieCall else .seq (dieT a) (dieT b)
  | .ite c a b => .ite c (dieT a) (dieT b)
  | .while c b => .while c (dieT b)
  | .call (some (r, some (eid, v, h))) f args => .call (some (r, some (eid, v, dieT h))) f args
  | .decCall n sh f args k => .decCall n sh f args (dieT k)
  | p => p

/-- A code-table entry with its body transformed. -/
def dieE (e : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL) : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL :=
  (e.1, dieT e.2.1, e.2.2)

/-- The emitted table's entries: `die`, then every entry transformed. -/
def dieEntries (l : List (MlS × (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))) :
    List (MlS × (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)) :=
  (fDie, dieEntry) :: l.map (fun fe => (fe.1, dieE fe.2))

theorem dieEntries_lookup (l : List (MlS × (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))) (f : MlS) :
    (dieEntries l).lookup f = if f = fDie then some dieEntry else (l.lookup f).map dieE := by
  unfold dieEntries
  by_cases h : f = fDie
  · subst h; simp [List.lookup]
  · have hb : (f == fDie) = false := by simp [h]
    simp only [List.lookup, hb, h, ite_false]
    induction l with
    | nil => rfl
    | cons p l ih =>
      obtain ⟨k, e⟩ := p
      by_cases hk : f = k
      · subst hk; simp [List.lookup]
      · have hb' : (f == k) = false := by simp [hk]
        simp only [List.map, List.lookup, hb']; exact ih

/-- Leaves: no sub-programs, no calls. -/
def Leaf : ProgHOL 64 → Prop
  | .skip | .assign .. | .primitive .. | .store .. | .store32 .. | .storeByte .. | .break | .continue
  | .extCall .. | .raise .. | .return .. | .shMemLoad .. | .shMemStore .. | .tick | .annot .. => True
  | _ => False

/-- `q` is `p` with some sub-programs replaced by `return die();`. -/
inductive Repl : ProgHOL 64 → ProgHOL 64 → Prop
  | die (p) : Repl p dieCall
  | leaf (p) : Leaf p → Repl p p
  | dec (n sh e) {b b'} : Repl b b' → Repl (.dec n sh e b) (.dec n sh e b')
  | seq {a a' b b'} : Repl a a' → Repl b b' → Repl (.seq a b) (.seq a' b')
  | ite (c) {a a' b b'} : Repl a a' → Repl b b' → Repl (.ite c a b) (.ite c a' b')
  | while (c) {b b'} : Repl b b' → Repl (.while c b) (.while c b')
  | call0 (f args) : Repl (.call none f args) (.call none f args)
  | call1 (r f args) : Repl (.call (some (r, none)) f args) (.call (some (r, none)) f args)
  | call2 (r eid v) {h h'} (f args) : Repl h h' →
      Repl (.call (some (r, some (eid, v, h))) f args) (.call (some (r, some (eid, v, h'))) f args)
  | decCall (n sh f args) {k k'} : Repl k k' → Repl (.decCall n sh f args k) (.decCall n sh f args k')

theorem repl_dieT : ∀ p : ProgHOL 64, Repl p (dieT p)
  | .skip => .leaf _ trivial
  | .dec n sh e b => .dec n sh e (repl_dieT b)
  | .assign .. => .leaf _ trivial
  | .primitive .. => .leaf _ trivial
  | .store .. => .leaf _ trivial
  | .store32 .. => .leaf _ trivial
  | .storeByte .. => .leaf _ trivial
  | .seq a b => by
    show Repl _ (if isHang (.seq a b) then dieCall else .seq (dieT a) (dieT b))
    split
    · exact .die _
    · exact .seq (repl_dieT a) (repl_dieT b)
  | .ite c a b => .ite c (repl_dieT a) (repl_dieT b)
  | .while c b => .while c (repl_dieT b)
  | .break => .leaf _ trivial
  | .continue => .leaf _ trivial
  | .call none f args => .call0 f args
  | .call (some (r, none)) f args => .call1 r f args
  | .call (some (r, some (eid, v, h))) f args => .call2 r eid v f args (repl_dieT h)
  | .decCall n sh f args k => .decCall n sh f args (repl_dieT k)
  | .extCall .. => .leaf _ trivial
  | .raise .. => .leaf _ trivial
  | .return .. => .leaf _ trivial
  | .shMemLoad .. => .leaf _ trivial
  | .shMemStore .. => .leaf _ trivial
  | .tick => .leaf _ trivial
  | .annot .. => .leaf _ trivial

abbrev DCode := HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)

section
variable {σ : Type} (s : PanSemStateFiniteExact 64 σ) (c : DCode)

theorem wc_setKvar (k : VarKind) (n : MlS) (v : ValueHOL 64) :
    setKvarHOLFinite k n v { s with code := c } = { setKvarHOLFinite k n v s with code := c } := by
  cases k <;> rfl
theorem code_setKvar (k : VarKind) (n : MlS) (v : ValueHOL 64) : (setKvarHOLFinite k n v s).code = s.code := by
  cases k <;> rfl
theorem wc_setVar (n : MlS) (v : ValueHOL 64) :
    setVarHOLFinite n v { s with code := c } = { setVarHOLFinite n v s with code := c } := rfl
theorem wc_emptyLocals : emptyLocalsHOLFinite { s with code := c } = { emptyLocalsHOLFinite s with code := c } := rfl
theorem wc_decClock : decClockHOLFinite { s with code := c } = { decClockHOLFinite s with code := c } := rfl
theorem wc_isValid (k : VarKind) (n : MlS) (v : ValueHOL 64) :
    isValidValueHOLExact ({ s with code := c } : PanSemStateFiniteExact 64 σ).toExact k n v =
      isValidValueHOLExact s.toExact k n v := rfl
theorem wc_isValidF (k : VarKind) (n : MlS) (v : ValueHOL 64) :
    isValidValueHOLFinite { s with code := c } k n v = isValidValueHOLFinite s k n v := rfl
theorem wc_eval (e : ExpHOL 64) :
    @evalHOLExact 64 σ _ ({ s with code := c } : PanSemStateFiniteExact 64 σ).toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) e =
    @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e :=
  @evalHOLExact_upd_code_eq 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e c.lookup
theorem wc_evalList (es : List (ExpHOL 64)) :
    @evalListHOLExact 64 σ _ ({ s with code := c } : PanSemStateFiniteExact 64 σ).toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) es =
    @evalListHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) es := by
  induction es with
  | nil => simp [evalListHOLExact]
  | cons e es ih => simp only [evalListHOLExact, wc_eval, ih]

theorem code_setVar (n : MlS) (v : ValueHOL 64) : (setVarHOLFinite n v s).code = s.code := rfl
theorem code_emptyLocals : (emptyLocalsHOLFinite s).code = s.code := rfl
theorem code_decClock : (decClockHOLFinite s).code = s.code := rfl
theorem wc_evalF (e : ExpHOL 64) :
    @evalHOLFinite 64 σ _ { s with code := c } (fun a => Classical.propDecidable (s.memaddrs a)) e =
    @evalHOLFinite 64 σ _ s (fun a => Classical.propDecidable (s.memaddrs a)) e := wc_eval s c e
theorem wc_evalListF (es : List (ExpHOL 64)) :
    @evalListHOLFinite 64 σ _ { s with code := c } (fun a => Classical.propDecidable (s.memaddrs a)) es =
    @evalListHOLFinite 64 σ _ s (fun a => Classical.propDecidable (s.memaddrs a)) es := wc_evalList s c es
theorem wc_shMemLoad (k : VarKind) (n : MlS) (a : BitVec 64) (nb : Nat) :
    @shMemLoadHOLFiniteExact 64 σ _ { s with code := c } (fun a => Classical.propDecidable (s.shMemaddrs a)) k n a nb =
      ((@shMemLoadHOLFiniteExact 64 σ _ s (fun a => Classical.propDecidable (s.shMemaddrs a)) k n a nb).1,
       { (@shMemLoadHOLFiniteExact 64 σ _ s (fun a => Classical.propDecidable (s.shMemaddrs a)) k n a nb).2 with
          code := c }) ∧
    (@shMemLoadHOLFiniteExact 64 σ _ s (fun a => Classical.propDecidable (s.shMemaddrs a)) k n a nb).2.code
      = s.code := by
  unfold shMemLoadHOLFiniteExact
  simp only
  cases hf : callFFIHOL s.ffi (.sharedMem .mappedRead) [BitVec.ofNat 8 nb] (panWordToBytesHOL a false) <;>
    (repeat' split) <;> (constructor <;> first | rfl | (simp only [setKvarFfiHOLFinite]; cases k <;> rfl))
theorem wc_shMemStore (w a : BitVec 64) (nb : Nat) :
    @shMemStoreHOLExact 64 σ _ ({ s with code := c } : PanSemStateFiniteExact 64 σ).toExact
        (fun a => Classical.propDecidable (({ s with code := c } : PanSemStateFiniteExact 64 σ).shMemaddrs a)) w a nb =
      ((@shMemStoreHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.shMemaddrs a)) w a nb).1,
       { (@shMemStoreHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.shMemaddrs a)) w a nb).2 with
          code := c.lookup }) ∧
    (@shMemStoreHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.shMemaddrs a)) w a nb).2.code
      = s.code.lookup := by
  unfold shMemStoreHOLExact
  simp only
  by_cases h0 : nb = 0
  · cases hf : callFFIHOL s.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 nb]
        (panWordToBytesHOL w false ++ panWordToBytesHOL a false) <;>
      (repeat' split) <;> exact ⟨rfl, rfl⟩
  · cases hf : callFFIHOL s.ffi (.sharedMem .mappedWrite) [BitVec.ofNat 8 nb]
        ((panWordToBytesHOL w false).take nb ++ panWordToBytesHOL a false) <;>
      (repeat' split) <;> exact ⟨rfl, rfl⟩

end


/-! ## The code tables -/

/-- `c'` is the emitted table of `c`: `die` added (absent from `c`), every other body transformed. -/
structure CodeRel (c c' : DCode) : Prop where
  none : c.lookup fDie = none
  die : c'.lookup fDie = some dieEntry
  other : ∀ f, f ≠ fDie → c'.lookup f = (c.lookup f).map dieE

theorem lookupExact_rel {c c' : DCode} (hR : CodeRel c c') {f : MlS} (hf : f ≠ fDie) (vals : List (ValueHOL 64)) :
    lookupCodeHOLExact c'.lookup f vals =
      (lookupCodeHOLExact c.lookup f vals).map (fun x => (dieT x.1, x.2.1, x.2.2)) := by
  unfold lookupCodeHOLExact
  rw [hR.other f hf]
  cases c.lookup f with
  | none => rfl
  | some e =>
    obtain ⟨ps, b, r⟩ := e
    simp only [Option.map, dieE]
    split <;> rfl

theorem lookup_rel {c c' : DCode} (hR : CodeRel c c') {f : MlS} (hf : f ≠ fDie) (vals : List (ValueHOL 64)) :
    lookupCodeHOLFinite c'.lookup f vals =
      (lookupCodeHOLFinite c.lookup f vals).map (fun x => (dieT x.1, x.2.1, x.2.2)) := by
  have he := lookupExact_rel hR hf vals
  cases h : lookupCodeHOLFinite c.lookup f vals with
  | none =>
    rw [(lookupCodeHOLFinite_eq_none_iff _ _ _).1 h] at he
    exact (lookupCodeHOLFinite_eq_none_iff _ _ _).2 he
  | some x =>
    obtain ⟨b, callee, r⟩ := x
    rw [lookupCodeHOLFinite_eq_some _ _ _ _ _ _ h] at he
    cases h' : lookupCodeHOLFinite c'.lookup f vals with
    | none =>
      rw [(lookupCodeHOLFinite_eq_none_iff _ _ _).1 h'] at he; simp at he
    | some y =>
      obtain ⟨b', callee', r'⟩ := y
      rw [lookupCodeHOLFinite_eq_some _ _ _ _ _ _ h'] at he
      simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, hc, rfl⟩ := he
      simp only [Option.map, HolFiniteMapExact.ext hc]

theorem lookup_die_none {c c' : DCode} (hR : CodeRel c c') (vals : List (ValueHOL 64)) :
    lookupCodeHOLFinite c.lookup fDie vals = none :=
  (lookupCodeHOLFinite_eq_none_iff _ _ _).2 (lookupCodeHOLExact_of_code_none _ _ _ hR.none)

theorem lookup_die_body {c c' : DCode} (hR : CodeRel c c') {vals : List (ValueHOL 64)} {b : ProgHOL 64}
    {callee : HolFiniteMapExact MlS (ValueHOL 64)} {r : ShapeHOL}
    (h : lookupCodeHOLFinite c'.lookup fDie vals = some (b, callee, r)) : b = hang := by
  have he := lookupCodeHOLFinite_eq_some _ _ _ _ _ _ h
  unfold lookupCodeHOLExact at he
  rw [hR.die] at he
  simp only [dieEntry] at he
  simp at he
  exact he.2.1.symm

theorem lookup_die_some {c c' : DCode} (hR : CodeRel c c') :
    ∃ x, lookupCodeHOLFinite c'.lookup fDie [] = some x := by
  cases h : lookupCodeHOLFinite c'.lookup fDie [] with
  | some x => exact ⟨x, rfl⟩
  | none =>
    have he := (lookupCodeHOLFinite_eq_none_iff _ _ _).1 h
    unfold lookupCodeHOLExact at he
    rw [hR.die] at he
    simp [dieEntry] at he

/-- A call to `die` (any arguments) whose lookup succeeds stops. -/
theorem call_die_stop {σ : Type} (s : PanSemStateFiniteExact 64 σ) {c : DCode} (hR : CodeRel c s.code)
    (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64))) (args : List (ExpHOL 64))
    (vals : List (ValueHOL 64))
    (hargs : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) args = some vals)
    {b : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)} {r : ShapeHOL}
    (hlk : lookupCodeHOLFinite s.code.lookup fDie vals = some (b, callee, r)) :
    Stop (evaluateHOLFiniteState s (.call info fDie args)).1 := by
  have hb := lookup_die_body hR hlk
  subst hb
  exact call_stop s info fDie args vals hang callee r hargs hlk (hang_stop _)

/-- `return die();` stops. -/
theorem dieCall_stop {σ : Type} (s : PanSemStateFiniteExact 64 σ) {c : DCode} (hR : CodeRel c s.code) :
    Stop (evaluateHOLFiniteState s dieCall).1 := by
  obtain ⟨⟨b, callee, r⟩, h⟩ := lookup_die_some hR
  exact call_die_stop s hR none [] [] (by simp [evalListHOLFinite, evalListHOLExact]) h

theorem leaf_sim {σ : Type} (s : PanSemStateFiniteExact 64 σ) (c : DCode) (p : ProgHOL 64) (hp : Leaf p) :
    evaluateHOLFiniteState { s with code := c } p =
      ((evaluateHOLFiniteState s p).1, { (evaluateHOLFiniteState s p).2 with code := c }) ∧
    (evaluateHOLFiniteState s p).2.code = s.code := by
  cases p <;> simp only [Leaf] at hp <;> rw [evaluateHOLFiniteState_eq_evaluate_def, evaluateHOLFiniteState_eq_evaluate_def] <;>
    dsimp only
  case tick => (repeat' split) <;> exact ⟨rfl, rfl⟩
  case shMemLoad op k n a =>
    have lk : lookupKvarHOLFinite k n { s with code := c } = lookupKvarHOLFinite k n s := by cases k <;> rfl
    simp only [wc_evalF, lk]
    split
    · split
      · obtain ⟨h1, h2⟩ := wc_shMemLoad s c k n _ (nbOpHOL op)
        exact ⟨by simp only [h1], h2⟩
      · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩
  case shMemStore op a v =>
    simp only [wc_eval]
    split
    · rename_i addr bytes _ _
      obtain ⟨h1, h2⟩ := wc_shMemStore s c bytes addr (nbOpHOL op)
      refine ⟨?_, HolFiniteMapExact.ext h2⟩
      simp only [h1]
      rfl
    · exact ⟨rfl, rfl⟩
  all_goals (simp only [wc_eval, wc_evalList, wc_isValidF, wc_evalF]; (repeat' split) <;>
    simp_all [wc_setKvar, code_setKvar, wc_setVar, wc_emptyLocals, code_setVar, code_emptyLocals] <;> exact ⟨rfl, rfl⟩)
/-! ## The simulation -/

section
variable {σ : Type}

/-- The emitted run stops, or agrees with the proved run up to the code table. -/
def SimR (s : PanSemStateFiniteExact 64 σ) (c' : DCode) (p q : ProgHOL 64) : Prop :=
  Stop (evaluateHOLFiniteState { s with code := c' } q).1 ∨
  (evaluateHOLFiniteState { s with code := c' } q =
      ((evaluateHOLFiniteState s p).1, { (evaluateHOLFiniteState s p).2 with code := c' }) ∧
    (evaluateHOLFiniteState s p).2.code = s.code)

/-- Simulation for every state up to clock `n`. -/
def SimN (n : Nat) (p q : ProgHOL 64) : Prop :=
  ∀ (s : PanSemStateFiniteExact 64 σ) (c' : DCode), s.clock ≤ n → CodeRel s.code c' → SimR s c' p q

theorem clock_of {s u : PanSemStateFiniteExact 64 σ} {p : ProgHOL 64} {r : Option (PanSemResultExact 64)}
    (h : evaluateHOLFiniteState s p = (r, u)) : u.clock ≤ s.clock := by
  have := evaluateHOLFiniteState_clock_le s p; rw [h] at this; exact this

theorem seq_sim {n : Nat} {a a' b b' : ProgHOL 64} (ha : SimN (σ := σ) n a a') (hb : SimN (σ := σ) n b b') :
    SimN (σ := σ) n (.seq a b) (.seq a' b') := by
  intro s c' hn hc
  unfold SimR
  rcases ha s c' hn hc with hs | ⟨he, hcode⟩
  · left; exact seq_stop _ _ _ hs
  generalize hA : evaluateHOLFiniteState s a = A at he hcode
  obtain ⟨r, u⟩ := A
  cases r with
  | none =>
    simp only at he hcode
    rw [seq_normal b' he, seq_normal b hA]
    rcases hb u c' (Nat.le_trans (clock_of hA) hn) (by rw [hcode]; exact hc) with h | ⟨h1, h2⟩
    · left; exact h
    · right; exact ⟨h1, h2.trans hcode⟩
  | some x =>
    right
    rw [seq_abort _ _ _ x (by rw [he]), seq_abort _ _ _ x (by rw [hA]), he, hA]; exact ⟨rfl, hcode⟩

theorem dec_sim {n : Nat} (x : MlS) (sh : ShapeHOL) (e : ExpHOL 64) {b b' : ProgHOL 64}
    (hb : SimN (σ := σ) n b b') : SimN (σ := σ) n (.dec x sh e b) (.dec x sh e b') := by
  intro s c' hn hc
  unfold SimR
  rw [evaluateHOLFiniteState_eq_evaluate_def { s with code := c' } (.dec x sh e b'),
    evaluateHOLFiniteState_eq_evaluate_def s (.dec x sh e b)]
  dsimp only
  simp only [wc_eval]
  cases hv : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with
  | none => right; exact ⟨rfl, rfl⟩
  | some v =>
    simp only
    by_cases hs : shapeEqHOL sh (shapeOfHOLExact v) = true
    · simp only [hs, ite_true]
      rcases hb (setVarHOLFinite x v s) c' hn hc with h | ⟨he, hcode⟩
      · left; exact h
      · right; rw [wc_setVar, he]; exact ⟨rfl, hcode⟩
    · simp only [hs]; right; exact ⟨rfl, rfl⟩


theorem simR_code {s u : PanSemStateFiniteExact 64 σ} {c' : DCode} {p q : ProgHOL 64} (hcode : u.code = s.code)
    (h : SimR u c' p q) :
    Stop (evaluateHOLFiniteState { u with code := c' } q).1 ∨
    (evaluateHOLFiniteState { u with code := c' } q =
        ((evaluateHOLFiniteState u p).1, { (evaluateHOLFiniteState u p).2 with code := c' }) ∧
      (evaluateHOLFiniteState u p).2.code = s.code) := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2.trans hcode⟩

theorem ite_sim {n : Nat} (cnd : ExpHOL 64) {a a' b b' : ProgHOL 64} (ha : SimN (σ := σ) n a a')
    (hb : SimN (σ := σ) n b b') : SimN (σ := σ) n (.ite cnd a b) (.ite cnd a' b') := by
  intro s c' hn hc
  unfold SimR
  rw [evaluateHOLFiniteState_eq_evaluate_def { s with code := c' } (.ite cnd a' b'),
    evaluateHOLFiniteState_eq_evaluate_def s (.ite cnd a b)]
  dsimp only
  simp only [wc_eval]
  cases hv : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cnd with
  | none => right; exact ⟨rfl, rfl⟩
  | some v =>
    cases v with
    | rStruct => right; exact ⟨rfl, rfl⟩
    | nStruct => right; exact ⟨rfl, rfl⟩
    | val w =>
      cases w with
      | word w =>
        simp only
        by_cases hw : w = 0
        · simp only [hw, ite_true]; exact hb s c' hn hc
        · simp only [hw, ite_false]; exact ha s c' hn hc

theorem while_sim {n : Nat} (cnd : ExpHOL 64) {b b' : ProgHOL 64} (hb : SimN (σ := σ) n b b')
    (ih : ∀ m, m < n → SimN (σ := σ) m (.while cnd b) (.while cnd b')) :
    SimN (σ := σ) n (.while cnd b) (.while cnd b') := by
  intro s c' hn hc
  unfold SimR
  rw [evaluateHOLFiniteState_eq_evaluate_def { s with code := c' } (.while cnd b'),
    evaluateHOLFiniteState_eq_evaluate_def s (.while cnd b)]
  dsimp only
  simp only [wc_evalF]
  cases hv : @evalHOLFinite 64 σ _ s (fun a => Classical.propDecidable (s.memaddrs a)) cnd with
  | none => right; exact ⟨rfl, rfl⟩
  | some v =>
    cases v with
    | rStruct => right; exact ⟨rfl, rfl⟩
    | nStruct => right; exact ⟨rfl, rfl⟩
    | val w =>
      cases w with
      | word w =>
        simp only
        by_cases hw : w ≠ 0
        · rw [ite_eq_left hw, ite_eq_left hw]
          by_cases hk : s.clock = 0
          · rw [ite_eq_left (show ({ s with code := c' } : PanSemStateFiniteExact 64 σ).clock = 0 from hk)]
            exact Or.inl (Or.inl rfl)
          rw [ite_eq_right (show ¬ ({ s with code := c' } : PanSemStateFiniteExact 64 σ).clock = 0 from hk), ite_eq_right hk,
            wc_decClock]
          have hdn : (decClockHOLFinite s).clock ≤ n := by
            show s.clock - 1 ≤ n; omega
          rcases hb (decClockHOLFinite s) c' hdn hc with hs | ⟨he, hcode⟩
          · left
            generalize hB : evaluateHOLFiniteState { decClockHOLFinite s with code := c' } b' = B at hs
            obtain ⟨r, u⟩ := B
            rcases hs with h | ⟨ev, h⟩ <;> simp only at h <;> subst h
            · exact Or.inl rfl
            · exact Or.inr ⟨ev, rfl⟩
          · rw [he]
            generalize hB : evaluateHOLFiniteState (decClockHOLFinite s) b = B at hcode
            obtain ⟨r, u⟩ := B
            simp only at hcode ⊢
            have hu : u.clock < n := by
              have := clock_of hB
              have e : (decClockHOLFinite s).clock = s.clock - 1 := rfl
              omega
            have hc' : CodeRel u.code c' := by rw [hcode]; exact hc
            cases r with
            | none => exact simR_code hcode (ih u.clock hu u c' (Nat.le_refl _) hc')
            | some r =>
              cases r with
              | «continue» => exact simR_code hcode (ih u.clock hu u c' (Nat.le_refl _) hc')
              | «break» => right; exact ⟨rfl, hcode⟩
              | _ => right; exact ⟨rfl, hcode⟩
        · rw [ite_eq_right hw, ite_eq_right hw]; right; exact ⟨rfl, rfl⟩


/-- Call information related by `Repl` on the handler. -/
def InfoRel : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64)) →
    Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64)) → Prop
  | none, none => True
  | some (r, none), some (r', none) => r = r'
  | some (r, some (e, v, h)), some (r', some (e', v', h')) => r = r' ∧ e = e' ∧ v = v' ∧ Repl h h'
  | _, _ => False

theorem wc_entry (s : PanSemStateFiniteExact 64 σ) (c' : DCode) (callee : HolFiniteMapExact MlS (ValueHOL 64)) :
    callEntryStateHOLFinite { s with code := c' } callee = { callEntryStateHOLFinite s callee with code := c' } := rfl

theorem call_sim {n : Nat} {info info' : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64))}
    (hI : InfoRel info info') (f : MlS) (args : List (ExpHOL 64))
    (ih : ∀ m, m < n → ∀ p q, Repl p q → SimN (σ := σ) m p q) :
    SimN (σ := σ) n (.call info f args) (.call info' f args) := by
  intro s c' hn hc
  unfold SimR
  by_cases hf : f = fDie
  · subst hf
    cases hargs : @evalListHOLFinite 64 σ _ s (fun a => Classical.propDecidable (s.memaddrs a)) args with
    | none =>
      right
      rw [evaluateHOLFiniteState_eq_evaluate_def { s with code := c' } (.call info' fDie args),
        evaluateHOLFiniteState_eq_evaluate_def s (.call info fDie args)]
      dsimp only
      simp only [wc_evalListF, hargs]
      constructor <;> first | rfl | trivial
    | some vals =>
      cases hl : lookupCodeHOLFinite c'.lookup fDie vals with
      | some x =>
        left
        obtain ⟨b, callee, r⟩ := x
        exact call_die_stop { s with code := c' } hc info' args vals (by rw [wc_evalListF]; exact hargs) hl
      | none =>
        right
        rw [evaluateHOLFiniteState_eq_evaluate_def { s with code := c' } (.call info' fDie args),
          evaluateHOLFiniteState_eq_evaluate_def s (.call info fDie args)]
        dsimp only
        simp only [wc_evalListF, hargs]
        rw [hl, lookup_die_none hc]
        exact ⟨rfl, rfl⟩
  rw [evaluateHOLFiniteState_eq_evaluate_def { s with code := c' } (.call info' f args),
    evaluateHOLFiniteState_eq_evaluate_def s (.call info f args)]
  dsimp only
  simp only [wc_evalListF]
  cases hargs : @evalListHOLFinite 64 σ _ s (fun a => Classical.propDecidable (s.memaddrs a)) args with
  | none => right; exact ⟨rfl, rfl⟩
  | some vals =>
    simp only
    rw [lookup_rel hc hf vals]
    cases hl : lookupCodeHOLFinite s.code.lookup f vals with
    | none => right; exact ⟨rfl, rfl⟩
    | some x =>
      obtain ⟨b, callee, r⟩ := x
      simp only [Option.map]
      by_cases hk : s.clock = 0
      · rw [ite_eq_left (show ({ s with code := c' } : PanSemStateFiniteExact 64 σ).clock = 0 from hk)]
        exact Or.inl (Or.inl rfl)
      rw [ite_eq_right (show ¬ ({ s with code := c' } : PanSemStateFiniteExact 64 σ).clock = 0 from hk), ite_eq_right hk,
        wc_entry]
      have hcl : (callEntryStateHOLFinite s callee).clock ≤ s.clock - 1 := Nat.le_refl _
      rcases ih (s.clock - 1) (by omega) b (dieT b) (repl_dieT b) (callEntryStateHOLFinite s callee) c' hcl hc with
        hs | ⟨he, hcode⟩
      · left
        generalize hB : evaluateHOLFiniteState { callEntryStateHOLFinite s callee with code := c' } (dieT b) = B at hs
        obtain ⟨r1, u⟩ := B
        rcases hs with h | ⟨ev, h⟩ <;> simp only at h <;> subst h
        · exact Or.inl rfl
        · exact Or.inr ⟨ev, rfl⟩
      · rw [he]
        generalize hB : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) b = B at hcode
        obtain ⟨r1, u⟩ := B
        simp only at hcode ⊢
        have hu : u.clock ≤ s.clock - 1 := clock_of hB
        cases r1 with
        | none => right; exact ⟨rfl, hcode⟩
        | some r1 =>
          cases r1 with
          | error => right; exact ⟨rfl, hcode⟩
          | timeOut => right; exact ⟨rfl, hcode⟩
          | «break» => right; exact ⟨rfl, hcode⟩
          | «continue» => right; exact ⟨rfl, hcode⟩
          | finalFfi ev => right; exact ⟨rfl, hcode⟩
          | returned v =>
            simp only
            by_cases hsh : shapeEqHOL (shapeOfHOLExact v) r = true
            · simp only [hsh, ite_true]
              rcases info with _ | ⟨ret, hd⟩ <;> rcases info' with _ | ⟨ret', hd'⟩ <;>
                simp only [InfoRel] at hI
              · right; exact ⟨rfl, hcode⟩
              · have hr : ret = ret' := by
                  rcases hd with _ | ⟨_, _, _⟩ <;> rcases hd' with _ | ⟨_, _, _⟩ <;> simp only at hI <;>
                    first | exact hI | exact hI.1
                subst hr
                rcases ret with _ | ⟨k, nm⟩
                · right; exact ⟨rfl, hcode⟩
                · simp only [wc_isValid]
                  by_cases hvv : isValidValueHOLExact s.toExact k nm v = true
                  · simp only [hvv, ite_true]; right
                    exact ⟨by rw [← wc_setKvar], (code_setKvar _ _ _ _).trans hcode⟩
                  · simp only [hvv]; right; exact ⟨rfl, hcode⟩
            · simp only [hsh]; right; exact ⟨rfl, hcode⟩
          | exception eid v =>
            simp only
            rcases info with _ | ⟨ret, hd⟩ <;> rcases info' with _ | ⟨ret', hd'⟩ <;>
              simp only [InfoRel] at hI
            · right; exact ⟨rfl, hcode⟩
            · rcases hd with _ | ⟨hid, hv, hp⟩ <;> rcases hd' with _ | ⟨hid', hv', hp'⟩ <;> simp only at hI
              · right; exact ⟨rfl, hcode⟩
              · obtain ⟨rfl, rfl, rfl, hR⟩ := hI
                simp only
                by_cases hei : eid = hid
                · simp only [hei, ite_true]
                  rw [show ({ s with code := c' } : PanSemStateFiniteExact 64 σ).eshapes = s.eshapes from rfl]
                  cases hes : s.eshapes.lookup hid with
                  | none => right; exact ⟨rfl, hcode⟩
                  | some shp =>
                    simp only [wc_isValid]
                    by_cases hcond : (shapeEqHOL (shapeOfHOLExact v) shp &&
                        isValidValueHOLExact s.toExact .local hv v) = true
                    · simp only [hcond, ite_true]
                      have hst : (setVarHOLFinite hv v { u with locals := s.locals }).clock ≤ s.clock - 1 := hu
                      have hsc : (setVarHOLFinite hv v { u with locals := s.locals }).code = s.code := hcode
                      have := ih (s.clock - 1) (by omega) hp hp' hR (setVarHOLFinite hv v { u with locals := s.locals })
                        c' hst (by rw [hsc]; exact hc)
                      exact simR_code hsc this
                    · simp only [hcond]; right; exact ⟨rfl, hcode⟩
                · simp only [hei, ite_false]; right; exact ⟨rfl, hcode⟩


theorem decCall_sim {n : Nat} (x : MlS) (sh : ShapeHOL) (f : MlS) (args : List (ExpHOL 64)) {k k' : ProgHOL 64}
    (hk : SimN (σ := σ) n k k') (ih : ∀ m, m < n → ∀ p q, Repl p q → SimN (σ := σ) m p q) :
    SimN (σ := σ) n (.decCall x sh f args k) (.decCall x sh f args k') := by
  intro s c' hn hc
  unfold SimR
  rw [evaluateHOLFiniteState_eq_evaluate_def { s with code := c' } (.decCall x sh f args k'),
    evaluateHOLFiniteState_eq_evaluate_def s (.decCall x sh f args k)]
  dsimp only
  simp only [wc_evalListF]
  cases hargs : @evalListHOLFinite 64 σ _ s (fun a => Classical.propDecidable (s.memaddrs a)) args with
  | none => right; exact ⟨rfl, rfl⟩
  | some vals =>
    simp only
    by_cases hf : f = fDie
    · subst hf
      rw [lookup_die_none hc]
      cases hl : lookupCodeHOLFinite c'.lookup fDie vals with
      | none => right; exact ⟨rfl, rfl⟩
      | some y =>
        left
        obtain ⟨b, callee, r⟩ := y
        have hb := lookup_die_body hc hl
        subst hb
        simp only
        by_cases hck : s.clock = 0
        · rw [ite_eq_left (show ({ s with code := c' } : PanSemStateFiniteExact 64 σ).clock = 0 from hck)]
          exact Or.inl rfl
        rw [ite_eq_right (show ¬ ({ s with code := c' } : PanSemStateFiniteExact 64 σ).clock = 0 from hck)]
        have hs := hang_stop (callEntryStateHOLFinite { s with code := c' } callee)
        generalize evaluateHOLFiniteState (callEntryStateHOLFinite { s with code := c' } callee) hang = B at hs
        obtain ⟨r1, u⟩ := B
        rcases hs with h | ⟨ev, h⟩ <;> simp only at h <;> subst h
        · exact Or.inl rfl
        · exact Or.inr ⟨ev, rfl⟩
    rw [lookup_rel hc hf vals]
    cases hl : lookupCodeHOLFinite s.code.lookup f vals with
    | none => right; exact ⟨rfl, rfl⟩
    | some y =>
      obtain ⟨b, callee, r⟩ := y
      simp only [Option.map]
      by_cases hck : s.clock = 0
      · rw [ite_eq_left (show ({ s with code := c' } : PanSemStateFiniteExact 64 σ).clock = 0 from hck)]
        exact Or.inl (Or.inl rfl)
      rw [ite_eq_right (show ¬ ({ s with code := c' } : PanSemStateFiniteExact 64 σ).clock = 0 from hck), ite_eq_right hck,
        wc_entry]
      have hcl : (callEntryStateHOLFinite s callee).clock ≤ s.clock - 1 := Nat.le_refl _
      rcases ih (s.clock - 1) (by omega) b (dieT b) (repl_dieT b) (callEntryStateHOLFinite s callee) c' hcl hc with
        hs | ⟨he, hcode⟩
      · left
        generalize hB : evaluateHOLFiniteState { callEntryStateHOLFinite s callee with code := c' } (dieT b) = B at hs
        obtain ⟨r1, u⟩ := B
        rcases hs with h | ⟨ev, h⟩ <;> simp only at h <;> subst h
        · exact Or.inl rfl
        · exact Or.inr ⟨ev, rfl⟩
      · rw [he]
        generalize hB : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) b = B at hcode
        obtain ⟨r1, u⟩ := B
        simp only at hcode ⊢
        have hu : u.clock ≤ s.clock - 1 := clock_of hB
        cases r1 with
        | none => right; exact ⟨rfl, hcode⟩
        | some r1 =>
          cases r1 with
          | error => right; exact ⟨rfl, hcode⟩
          | timeOut => right; exact ⟨rfl, hcode⟩
          | «break» => right; exact ⟨rfl, hcode⟩
          | «continue» => right; exact ⟨rfl, hcode⟩
          | finalFfi ev => right; exact ⟨rfl, hcode⟩
          | exception eid v => right; exact ⟨rfl, hcode⟩
          | returned v =>
            simp only
            by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) sh && shapeEqHOL (shapeOfHOLExact v) r) = true
            · simp only [hsh, ite_true]
              have hst : (setVarHOLFinite x v { u with locals := s.locals }).clock ≤ n := by
                show u.clock ≤ n; omega
              have hsc : (setVarHOLFinite x v { u with locals := s.locals }).code = s.code := hcode
              rcases hk (setVarHOLFinite x v { u with locals := s.locals }) c' hst (by rw [hsc]; exact hc) with
                hs | ⟨he2, hcode2⟩
              · left; exact hs
              · right
                rw [← wc_setVar] at he2
                dsimp only at he2
                rw [he2]
                exact ⟨rfl, hcode2.trans hsc⟩
            · simp only [hsh]; right; exact ⟨rfl, hcode⟩

/-- **The simulation.** -/
theorem repl_sim : ∀ n (p q : ProgHOL 64), Repl p q → SimN (σ := σ) n p q := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihn =>
    intro p q hR
    induction hR with
    | die p => intro s c' _ hc; exact Or.inl (dieCall_stop { s with code := c' } hc)
    | leaf p hp => intro s c' _ _; exact Or.inr (leaf_sim s c' p hp)
    | dec x sh e _ hb => exact dec_sim x sh e hb
    | seq _ _ ha hb => exact seq_sim ha hb
    | ite cnd _ _ ha hb => exact ite_sim cnd ha hb
    | «while» cnd hR hb => exact while_sim cnd hb (fun m hm => ihn m hm _ _ (.while cnd hR))
    | call0 f args => exact call_sim (info := none) (info' := none) trivial f args ihn
    | call1 r f args => exact call_sim (info := some (r, none)) (info' := some (r, none)) rfl f args ihn
    | call2 r eid v f args hR _ =>
      exact call_sim (info := some (r, some (eid, v, _))) (info' := some (r, some (eid, v, _)))
        ⟨rfl, rfl, rfl, hR⟩ f args ihn
    | decCall x sh f args _ hk => exact decCall_sim x sh f args hk ihn


/-- **The emitted program agrees with the proved one, or stops.**  From a state whose code table `c'`
is the emitted table of the code table `c` of `s`, running `dieT p` either stops or gives the result
of running `p` from `s`, with the same final state apart from the code table. -/
theorem dieT_sim (s : PanSemStateFiniteExact 64 σ) {c' : DCode} (hc : CodeRel s.code c') (p : ProgHOL 64) :
    Stop (evaluateHOLFiniteState { s with code := c' } (dieT p)).1 ∨
      evaluateHOLFiniteState { s with code := c' } (dieT p) =
        ((evaluateHOLFiniteState s p).1, { (evaluateHOLFiniteState s p).2 with code := c' }) := by
  rcases repl_sim s.clock p (dieT p) (repl_dieT p) s c' (Nat.le_refl _) hc with h | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

end

end ConPanqueque.Logic
