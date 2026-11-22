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
