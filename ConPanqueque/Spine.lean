import ConPanqueque.LevelsFns
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic

/-!
# Application spines

`spineLen` counts the arguments of an application spine (con-leche's
`getAppNumArgs`), the first step of collecting a spine into an argument array
for beta reduction.
-/

namespace ConPanqueque.Spine

def iC := ofString "c"
def iR := ofString "r"
def vv (n : MlS) : ExpHOL 64 := .var .local n
def ldo (n : MlS) (off : BitVec 64) : ExpHOL 64 := .load .one (.op .add [vv n, .const off])
def ldv (n : MlS) : ExpHOL 64 := .load .one (vv n)

/-- The number of arguments of an application spine. -/
def numArgs : ConLeche.Expr → Nat
  | .app f _ => numArgs f + 1
  | _ => 0

/-- `spineLen(c)`: `1 + spineLen(c.fn)` at an `app` node (tag 4), else `0`. -/
def spineLenBody (fn : MlS) : ProgHOL 64 :=
  .ite (.cmp .equal (ldv iC) (.const 4))
    (.dec iR .one (.const 0) (.seq (.call (some (some (.local, iR), none)) fn [ldo iC 16])
      (.return (.op .add [vv iR, .const 1]))))
    (.return (.const 0))

theorem exprAt_tag {h : Heap} {p : BitVec 64} {e : ConLeche.Expr} (he : ExprAt h p e) :
    ∃ tg, h p = some (.word tg) ∧ (tg = 4 ↔ ∃ f a, e = .app f a) := by
  cases he <;> exact ⟨_, by assumption, by simp⟩

theorem spineLen_spec {σ : Type} (fn : MlS) (h : Heap) {p : BitVec 64} {e : ConLeche.Expr} (he : ExprAt h p e)
    (hsmall : numArgs e < 2 ^ 64) :
    ∀ t : PanSemStateFiniteExact 64 σ, t.code.lookup fn = some ([(iC, .one)], spineLenBody fn, .one) →
      InMem t h → t.locals.lookup iC = some (.val (.word p)) → numArgs e ≤ t.clock →
      ∃ st, evaluateHOLFiniteState t (spineLenBody fn) =
          (some (.returned (.val (.word (BitVec.ofNat 64 (numArgs e))))), st) ∧
        ConPanqueque.LevelsFns.Post t st (numArgs e) := by
  induction e generalizing p with
  | app f a ihf _ =>
    cases he with | @app _ q r _ _ hp h0 hd h2 h3 hf ha =>
    intro t hc hm hlc hck
    simp only [numArgs] at hsmall hck ⊢
    obtain ⟨d0, m0⟩ := hm _ _ h0
    obtain ⟨d2, m2⟩ := hm _ _ h2
    unfold spineLenBody
    rw [ite_word t _ _ _ 1 (by
      simp only [evalHOLExact]
      rw [show @evalHOLExact 64 σ _ t.toExact (fun x => Classical.propDecidable (t.memaddrs x)) (ldv iC) =
          some (.val (.word 4)) by unfold ldv; rw [eval_load_word t _ p (by simp [vv, evalHOLExact, hlc]) d0, m0]]
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
    simp only [ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true, ↓reduceIte]
    let t1 := setVarHOLFinite iR (.val (.word 0)) t
    obtain ⟨L1, e1⟩ := dec_word' t iR (.const 0) 0 _ (by simp [evalHOLExact])
    have hlc1 : t1.locals.lookup iC = some (.val (.word p)) := by
      simp only [t1]; rw [lookup_setVar_other _ _ (by decide)]; exact hlc
    obtain ⟨st, ⟨pc, pm, pd, pclk, pg, pt⟩, hcall⟩ := call1 t1 fn iC iR (spineLenBody fn) (ldo iC 16) q
      (BitVec.ofNat 64 (numArgs f))
      (fun st => st.code = t.code ∧ st.memory = t.memory ∧ st.memaddrs = t.memaddrs ∧
        t.clock - 1 ≤ st.clock + numArgs f ∧ st.globals = t.globals ∧ st.topAddr = t.topAddr)
      (by simpa [t1, setVarHOLFinite] using hc)
      (by unfold ldo vv; rw [eval_load_word t1 _ (p + 16) (by simp [evalHOLExact, evalListHOLExact, hlc1, wordOpHOL,
            wordOp, valueIsWord, valueWord]) d2]; show some (ValueHOL.val (t.memory (p + 16))) = _; rw [m2])
      (by show t.clock ≠ 0; omega) ⟨0, by simp [t1]⟩
      (fun callee hx => by
        obtain ⟨st, ev, a1, a2, a3, a4, a5, a6⟩ := ihf hf (by omega) (callEntryStateHOLFinite t1 callee)
          (by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using hc)
          (fun a w ha => by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using hm a w ha)
          hx (by show numArgs f ≤ t.clock - 1; omega)
        exact ⟨st, ev, by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using a1,
          by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using a2,
          by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using a3,
          by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using a4,
          by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using a5,
          by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using a6⟩)
    let t2 := setKvarHOLFinite .local iR (.val (.word (BitVec.ofNat 64 (numArgs f)))) { st with locals := t1.locals }
    have eret : evaluateHOLFiniteState t2 (.return (.op .add [vv iR, .const 1])) =
        (some (.returned (.val (.word (BitVec.ofNat 64 (numArgs f + 1))))), emptyLocalsHOLFinite t2) := by
      rw [evaluateHOLFiniteState_eq_evaluate_def]
      simp [vv, evalHOLExact, evalListHOLExact, t2, setKvarHOLFinite, wordOpHOL, wordOp, valueIsWord, valueWord,
        shapeOfHOLExact]
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]
    rw [e1]; simp only; rw [seq_normal _ hcall, eret]
    refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [t2, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, pc, pm, pd, pg, pt] at pclk ⊢
    omega
  | _ =>
    intro t hc hm hlc hck
    obtain ⟨tg, h0, htg⟩ := exprAt_tag he
    have hne : tg ≠ 4 := fun e => by have := htg.mp e; simp at this
    obtain ⟨d0, m0⟩ := hm _ _ h0
    unfold spineLenBody
    rw [ite_word t _ _ _ 0 (by
      simp only [evalHOLExact]
      rw [show @evalHOLExact 64 σ _ t.toExact (fun x => Classical.propDecidable (t.memaddrs x)) (ldv iC) =
          some (.val (.word tg)) by unfold ldv; rw [eval_load_word t _ _ (by simp [vv, evalHOLExact, hlc]) d0, m0]]
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)]
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    rw [evaluateHOLFiniteState_eq_evaluate_def]
    refine ⟨emptyLocalsHOLFinite t, by simp [evalHOLExact, shapeOfHOLExact, numArgs], ?_⟩
    simp [ConPanqueque.LevelsFns.Post, emptyLocalsHOLFinite, numArgs]

end ConPanqueque.Spine

namespace ConPanqueque.Spine
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic

/-- The argument pointers of the spine at `q` (outermost argument last). -/
inductive SpArgs (h : Heap) : BitVec 64 → List (BitVec 64) → Prop
  | app {q f x : BitVec 64} {ps : List (BitVec 64)} (h0 : h q = some (.word 4)) (h2 : h (q + 16) = some (.word f))
      (h3 : h (q + 24) = some (.word x)) (hf : SpArgs h f ps) : SpArgs h q (ps ++ [x])
  | stop {q tg : BitVec 64} (h0 : h q = some (.word tg)) (ht : tg ≠ 4) : SpArgs h q []

/-- con-leche's `getAppArgs`, as a list. -/
def args : ConLeche.Expr → List ConLeche.Expr
  | .app f a => args f ++ [a]
  | _ => []

theorem args_length : ∀ e : ConLeche.Expr, (args e).length = numArgs e
  | .app f _ => by simp [args, numArgs, args_length f]
  | .bvar _ | .fvar _ _ | .sort _ | .const _ _ | .lam _ _ | .forallE _ _ | .letE _ _ _ | .lit _ | .proj _ _ _ => rfl

/-- Two lists related pointwise. -/
inductive All2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | nil : All2 R [] []
  | cons {a b as bs} : R a b → All2 R as bs → All2 R (a :: as) (b :: bs)

theorem All2.append {α β : Type} {R : α → β → Prop} : ∀ {as bs cs ds}, All2 R as bs → All2 R cs ds →
    All2 R (as ++ cs) (bs ++ ds)
  | _, _, _, _, .nil, h => h
  | _, _, _, _, .cons r t, h => .cons r (All2.append t h)

theorem spArgs_of_exprAt {h : Heap} (e : ConLeche.Expr) : ∀ {q : BitVec 64}, ExprAt h q e →
    ∃ ps, SpArgs h q ps ∧ All2 (fun p a => ExprAt h p a) ps (args e) := by
  induction e with
  | app f a ihf _ =>
    intro q he
    cases he with | @app _ qf qa _ _ hp h0 hd h2 h3 hf ha =>
    obtain ⟨ps, hs, hall⟩ := ihf hf
    exact ⟨ps ++ [qa], .app h0 h2 h3 hs, All2.append hall (.cons ha .nil)⟩
  | _ =>
    intro q he
    obtain ⟨tg, h0, htg⟩ := exprAt_tag he
    have h4 : tg ≠ 4 := fun e => by have := htg.mp e; simp at this
    exact ⟨[], .stop h0 h4, by simp only [args]; exact .nil⟩

def iA := ofString "a"

theorem ldo_eval_gen {σ : Type} (t : PanSemStateFiniteExact 64 σ) (n : MlS) (off p w : BitVec 64)
    (hn : t.locals.lookup n = some (.val (.word p))) (hd : t.memaddrs (p + off)) (hm : t.memory (p + off) = .word w) :
    @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) (ldo n off) =
      some (.val (.word w)) := by
  unfold ldo vv
  rw [eval_load_word t _ (p + off) (by simp [evalHOLExact, evalListHOLExact, hn, wordOpHOL, wordOp, valueIsWord,
    valueWord]) hd, hm]

def below (a : BitVec 64) (k : Nat) : BitVec 64 := a - BitVec.ofNat 64 (8 * k)

theorem below_succ (a : BitVec 64) (k : Nat) : below (a - 8) k = below a (k + 1) := by
  simp only [below]; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega

/-- `fill(c, a)`: store the spine's argument pointers in the words just below `a`
(the outermost argument at `a - 8`). -/
def fillBody (fn : MlS) : ProgHOL 64 :=
  .ite (.cmp .equal (ldv iC) (.const 4))
    (.seq (.store (.op .sub [vv iA, .const 8]) (ldo iC 24))
      (.dec iR .one (.const 0) (.seq (.call (some (some (.local, iR), none)) fn [ldo iC 16, .op .sub [vv iA, .const 8]])
        (.return (.const 0)))))
    (.return (.const 0))


theorem fill_spec {σ : Type} (fn : MlS) (h : Heap) {q : BitVec 64} {ps : List (BitVec 64)} (hs : SpArgs h q ps) :
    ∀ (t : PanSemStateFiniteExact 64 σ) (a : BitVec 64),
      t.code.lookup fn = some ([(iC, .one), (iA, .one)], fillBody fn, .one) → InMem t h →
      t.locals.lookup iC = some (.val (.word q)) → t.locals.lookup iA = some (.val (.word a)) →
      8 * ps.length ≤ a.toNat →
      (∀ k, 1 ≤ k → k ≤ ps.length → t.memaddrs (below a k) ∧ h (below a k) = none) → ps.length ≤ t.clock →
      ∃ st, evaluateHOLFiniteState t (fillBody fn) = (some (.returned (.val (.word 0))), st) ∧
        st.code = t.code ∧ st.globals = t.globals ∧ st.memaddrs = t.memaddrs ∧ st.topAddr = t.topAddr ∧
        t.clock ≤ st.clock + ps.length ∧
        (∀ j (hj : j < ps.length), st.memory (below a (ps.length - j)) = .word ps[j]) ∧
        (∀ c, (∀ k, 1 ≤ k → k ≤ ps.length → c ≠ below a k) → st.memory c = t.memory c) := by
  induction hs with
  | @stop q tg h0 ht =>
    intro t a hc hm hlc hla hfit hfr hck
    obtain ⟨d0, m0⟩ := hm _ _ h0
    unfold fillBody
    rw [ite_word t _ _ _ 0 (by
      simp only [evalHOLExact]
      rw [show @evalHOLExact 64 σ _ t.toExact (fun x => Classical.propDecidable (t.memaddrs x)) (ldv iC) =
          some (.val (.word tg)) by unfold ldv; rw [eval_load_word t _ _ (by simp [vv, evalHOLExact, hlc]) d0, m0]]
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ht)]
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    rw [evaluateHOLFiniteState_eq_evaluate_def]
    refine ⟨emptyLocalsHOLFinite t, by simp [evalHOLExact, shapeOfHOLExact], ?_⟩
    simp [emptyLocalsHOLFinite]
  | @app q f x ps h0 h2 h3 hf ih =>
    intro t a hc hm hlc hla hfit hfr hck
    simp only [List.length_append, List.length_singleton] at hfit hfr hck ⊢
    obtain ⟨d0, m0⟩ := hm _ _ h0
    obtain ⟨d2, m2⟩ := hm _ _ h2
    obtain ⟨d3, m3⟩ := hm _ _ h3
    unfold fillBody
    rw [ite_word t _ _ _ 1 (by
      simp only [evalHOLExact]
      rw [show @evalHOLExact 64 σ _ t.toExact (fun x => Classical.propDecidable (t.memaddrs x)) (ldv iC) =
          some (.val (.word 4)) by unfold ldv; rw [eval_load_word t _ _ (by simp [vv, evalHOLExact, hlc]) d0, m0]]
      simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
    simp only [ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true, ↓reduceIte]
    have hb1 : below a 1 = a - 8 := by simp [below]
    obtain ⟨fd, fn0⟩ := hfr 1 (Nat.le_refl _) (by omega)
    rw [hb1] at fd fn0
    have es := store_word t (.op .sub [vv iA, .const 8]) (ldo iC 24) (a - 8) x
      (by simp [vv, evalHOLExact, evalListHOLExact, hla, wordOpHOL, wordOp, valueIsWord, valueWord])
      (by unfold ldo vv; rw [eval_load_word t _ (q + 24) (by simp [evalHOLExact, evalListHOLExact, hlc, wordOpHOL,
            wordOp, valueIsWord, valueWord]) d3, m3]) fd
    let t1 : PanSemStateFiniteExact 64 σ := { t with memory := fun c => if c = a - 8 then .word x else t.memory c }
    rw [seq_normal _ es]
    have hm1 : InMem t1 h := fun c w hc' => by
      obtain ⟨d, m⟩ := hm c w hc'
      refine ⟨d, ?_⟩
      show (if c = a - 8 then _ else _) = w
      have hne : ¬ c = a - 8 := fun e => by subst e; rw [fn0] at hc'; cases hc'
      simp only [hne, ↓reduceIte]; exact m
    let t2 := setVarHOLFinite iR (.val (.word 0)) t1
    obtain ⟨L2, e2⟩ := dec_word' t1 iR (.const 0) 0 _ (by simp [evalHOLExact])
    have hlc2 : t2.locals.lookup iC = some (.val (.word q)) := by
      simp only [t2]; rw [lookup_setVar_other _ _ (by decide)]; exact hlc
    have hla2 : t2.locals.lookup iA = some (.val (.word a)) := by
      simp only [t2]; rw [lookup_setVar_other _ _ (by decide)]; exact hla
    have hm2 : InMem t2 h := ConPanqueque.ExprCons.inMem_of_eq rfl rfl hm1
    obtain ⟨callee, hlk, hx1, hx2⟩ := lookupCode2 t2 fn iC iA (fillBody fn) f (a - 8) (by decide) (by exact hc)
    have hargs : evalListHOLFinite t2 (h := fun a => Classical.propDecidable (t2.memaddrs a))
        [ldo iC 16, .op .sub [vv iA, .const 8]] = some [.val (.word f), .val (.word (a - 8))] := by
      simp only [evalListHOLFinite, evalListHOLExact]
      rw [ldo_eval_gen t2 iC 16 q f hlc2 (hm2 _ _ h2).1 (hm2 _ _ h2).2]
      simp [vv, evalHOLExact, evalListHOLExact, hla2, wordOpHOL, wordOp, valueIsWord, valueWord]
    let s' := callEntryStateHOLFinite t2 callee
    obtain ⟨st, hb, cd, gl, md, ta, ck, mset, mkeep⟩ := ih s' (a - 8)
      (by simp only [s', callEntryStateHOLFinite]; exact hc) hm2 hx1 hx2
      (by have : (a - 8).toNat = a.toNat - 8 := by simp [BitVec.toNat_sub]; omega
          rw [this]; omega)
      (fun k h1 h2 => by rw [below_succ]; exact hfr (k + 1) (by omega) (by omega))
      (by show ps.length ≤ t.clock - 1; omega)
    have hcall := call_assign t2 .local iR fn none _ _ (fillBody fn) callee .one (.val (.word 0)) st
      hargs hlk (by show t.clock ≠ 0; omega) hb (by simp [shapeOfHOLExact, shapeEqHOL])
      (by simp [isValidValueHOLExact, lookupKvarHOLExact, t2, shapeOfHOLExact, shapeEqHOL])
    let t3 := setKvarHOLFinite .local iR (.val (.word 0)) { st with locals := t2.locals }
    have eret : evaluateHOLFiniteState t3 (.return (.const 0)) = (some (.returned (.val (.word 0))), emptyLocalsHOLFinite t3) := by
      rw [evaluateHOLFiniteState_eq_evaluate_def]; simp [evalHOLExact, shapeOfHOLExact]
    rw [e2]; simp only; rw [seq_normal _ hcall, eret]
    refine ⟨_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [t3, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, cd, s', callEntryStateHOLFinite, t2, t1]
    · simp [t3, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, gl, s', callEntryStateHOLFinite, t2, t1]
    · simp [t3, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, md, s', callEntryStateHOLFinite, t2, t1]
    · simp [t3, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, ta, s', callEntryStateHOLFinite, t2, t1]
    · simp [t3, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, s', callEntryStateHOLFinite, t2, t1] at ck ⊢
      omega
    · intro j hj
      have hmem : (emptyLocalsHOLFinite t3).memory = st.memory := by
        simp [t3, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite]
      rw [hmem]
      by_cases hj' : j < ps.length
      · rw [List.getElem_append_left hj', show ps.length + 1 - j = (ps.length - j) + 1 by omega, ← below_succ]
        exact mset j hj'
      · have : j = ps.length := by omega
        subst this
        rw [List.getElem_append_right (by omega)]
        simp only [Nat.sub_self, List.getElem_singleton, show ps.length + 1 - ps.length = 1 by omega]
        rw [mkeep _ (fun k h1 h2 e => by
          rw [below_succ] at e
          have : (below a (k + 1)).toNat = a.toNat - 8 * (k + 1) := by simp [below, BitVec.toNat_sub]; omega
          have : (below a 1).toNat = a.toNat - 8 := by simp [below, BitVec.toNat_sub]; omega
          have := congrArg BitVec.toNat e; omega)]
        show (if below a 1 = a - 8 then _ else _) = _
        simp only [hb1, ↓reduceIte]
    · intro c hc'
      have hmem : (emptyLocalsHOLFinite t3).memory = st.memory := by
        simp [t3, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite]
      rw [hmem, mkeep c (fun k h1 h2 => by rw [below_succ]; exact hc' (k + 1) (by omega) (by omega))]
      show (if c = a - 8 then _ else _) = _
      have hne : ¬ c = a - 8 := fun e => hc' 1 (Nat.le_refl _) (by omega) (by rw [hb1]; exact e)
      simp only [hne, ↓reduceIte]

end ConPanqueque.Spine
