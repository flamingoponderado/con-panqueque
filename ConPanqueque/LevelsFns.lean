import ConPanqueque.LevelFns
import ConPanqueque.Subst
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic

/-!
# Functions over level lists

`lsHash` computes con-leche's `levelsHash` over a `LevelsAt` list (pure,
`lsHash_spec`).
-/

namespace ConPanqueque.LevelsFns

def iC := ofString "c"
def iR := ofString "r"
def vv (n : MlS) : ExpHOL 64 := .var .local n
def ldo (n : MlS) (off : BitVec 64) : ExpHOL 64 := .load .one (.op .add [vv n, .const off])
def ldv (n : MlS) : ExpHOL 64 := .load .one (vv n)

def Post {σ : Type} (s st : PanSemStateFiniteExact 64 σ) (c : Nat) : Prop :=
  st.code = s.code ∧ st.memory = s.memory ∧ st.memaddrs = s.memaddrs ∧ s.clock ≤ st.clock + c ∧
    st.globals = s.globals ∧ st.topAddr = s.topAddr

/-- `lsHash(c)`: `13` at the end, else `mixHash(hash(head), lsHash(tail))`. -/
def lsHashBody (fn : MlS) : ProgHOL 64 :=
  .ite (.cmp .equal (vv iC) (.const 0)) (.return (.const 13))
    (.dec iR .one (.const 0) (.seq (.call (some (some (.local, iR), none)) fn [ldo iC 8])
      (.return (ConPanqueque.Hash.mixExp (.load .one (.op .add [ldv iC, .const 8])) (vv iR)))))

theorem levelAt_hash' {h : Heap} {p : BitVec 64} {u : ConLeche.Level} (hu : LevelAt h p u) :
    h (p + 8) = some (.word u.hashData.toBitVec) := by
  cases hu <;> assumption

theorem lsHash_spec {σ : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (fn : MlS) (h : Heap)
    {c : BitVec 64} {us : List ConLeche.Level} (hl : LevelsAt h c us) :
    ∀ t : PanSemStateFiniteExact 64 σ, t.code.lookup fn = some ([(iC, .one)], lsHashBody fn, .one) →
      InMem t h → t.locals.lookup iC = some (.val (.word c)) → us.length ≤ t.clock →
      ∃ st, evaluateHOLFiniteState t (lsHashBody fn) =
          (some (.returned (.val (.word (ConLeche.levelsHash us).toBitVec))), st) ∧ Post t st us.length := by
  induction hl with
  | nil =>
    intro t hc hm hlc hck
    refine ⟨emptyLocalsHOLFinite t, ?_, by simp [Post, emptyLocalsHOLFinite]⟩
    unfold lsHashBody
    rw [ite_word t _ _ _ 1 (by simp [vv, evalHOLExact, hlc, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
    simp only [ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true, ↓reduceIte]
    rw [evaluateHOLFiniteState_eq_evaluate_def]; simp [evalHOLExact, shapeOfHOLExact, ConLeche.levelsHash] <;> rfl
  | @cons p q r u us hp h0 h1 hu hus ih =>
    intro t hc hm hlc hck
    have m0 := hm _ _ h0
    have m1 := hm _ _ h1
    have mh := hm _ _ (levelAt_hash' hu)
    unfold lsHashBody
    rw [ite_word t _ _ _ 0 (by simp [vv, evalHOLExact, hlc, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hp)]
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    let t1 := setVarHOLFinite iR (.val (.word 0)) t
    obtain ⟨L1, e1⟩ := dec_word' t iR (.const 0) 0 _ (by simp [evalHOLExact])
    have hlc1 : t1.locals.lookup iC = some (.val (.word p)) := by
      simp only [t1]; rw [lookup_setVar_other _ _ (by decide)]; exact hlc
    obtain ⟨st, ⟨pc, pm, pd, pclk, pg, pt⟩, hcall⟩ := call1 t1 fn iC iR (lsHashBody fn) (ldo iC 8) r
      (ConLeche.levelsHash us).toBitVec
      (fun st => st.code = t.code ∧ st.memory = t.memory ∧ st.memaddrs = t.memaddrs ∧
        t.clock - 1 ≤ st.clock + us.length ∧ st.globals = t.globals ∧ st.topAddr = t.topAddr)
      (by simpa [t1, setVarHOLFinite] using hc)
      (by unfold ldo vv; rw [eval_load_word t1 _ (p + 8) (by simp [evalHOLExact, evalListHOLExact, hlc1, wordOpHOL,
            wordOp, valueIsWord, valueWord]) m1.1]; show some (ValueHOL.val (t.memory (p + 8))) = _; rw [m1.2])
      (by show t.clock ≠ 0; simp at hck; omega) ⟨0, by simp [t1]⟩
      (fun callee hcl => by
        obtain ⟨st, ev, a1, a2, a3, a4, a5, a6⟩ := ih (callEntryStateHOLFinite t1 callee)
          (by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using hc)
          (fun a w ha => by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using hm a w ha)
          hcl (by show us.length ≤ t.clock - 1; simp at hck; omega)
        exact ⟨st, ev, by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using a1,
          by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using a2,
          by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using a3,
          by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using a4,
          by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using a5,
          by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using a6⟩)
    let t2 := setKvarHOLFinite .local iR (.val (.word (ConLeche.levelsHash us).toBitVec)) { st with locals := t1.locals }
    have lc2 : t2.locals.lookup iC = some (.val (.word p)) := by
      simp only [t2, setKvarHOLFinite]; rw [lookup_setVar_other _ _ (by decide)]; exact hlc1
    have lr2 : t2.locals.lookup iR = some (.val (.word (ConLeche.levelsHash us).toBitVec)) := by
      simp [t2, setKvarHOLFinite]
    have hm2 : t2.memory = t.memory := by simp [t2, setKvarHOLFinite, setVarHOLFinite, pm]
    have hd2 : t2.memaddrs = t.memaddrs := by simp [t2, setKvarHOLFinite, setVarHOLFinite, pd]
    have ev : @evalHOLExact 64 σ _ t2.toExact (fun a => Classical.propDecidable (t2.memaddrs a))
        (ConPanqueque.Hash.mixExp (.load .one (.op .add [ldv iC, .const 8])) (vv iR)) =
        some (.val (.word (ConLeche.levelsHash (u :: us)).toBitVec)) := by
      have := ConPanqueque.Hash.eval_mixExp t2 (.load .one (.op .add [ldv iC, .const 8])) (vv iR)
        u.hashData (ConLeche.levelsHash us)
        (by
          have hq : @evalHOLExact 64 σ _ t2.toExact (fun a => Classical.propDecidable (t2.memaddrs a))
              (ldv iC) = some (.val (.word q)) := by
            unfold ldv
            rw [eval_load_word t2 _ p (by simp [vv, evalHOLExact, lc2]) (by rw [hd2]; simpa using m0.1)]
            show some (ValueHOL.val (t2.memory p)) = _; rw [hm2]; simpa using m0.2
          rw [eval_load_word t2 _ (q + 8) (by simp only [evalHOLExact, evalListHOLExact]; rw [hq]; simp [wordOpHOL,
            wordOp, valueIsWord, valueWord]) (by rw [hd2]; exact mh.1)]
          show some (ValueHOL.val (t2.memory (q + 8))) = _; rw [hm2, mh.2])
        (by simp [vv, evalHOLExact, lr2])
      rw [this]; simp [ConLeche.levelsHash, ConLeche.levelHash, ra.mixHash]
    have eret : evaluateHOLFiniteState t2 (.return (ConPanqueque.Hash.mixExp (.load .one (.op .add [ldv iC, .const 8])) (vv iR)))
        = (some (.returned (.val (.word (ConLeche.levelsHash (u :: us)).toBitVec))), emptyLocalsHOLFinite t2) := by
      rw [evaluateHOLFiniteState_eq_evaluate_def]; simp only [ev]; simp [shapeOfHOLExact]
    rw [e1]; simp only; rw [seq_normal _ hcall, eret]
    refine ⟨_, rfl, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp [t2, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, pc, pm, pd, pg, pt, t1] at pclk ⊢
    omega

def iR2 := ofString "r2"

/-- `lsHP(c)`: does any level of the list have a parameter (`1`/`0`)? -/
def lsHPBody (fn : MlS) : ProgHOL 64 :=
  .ite (.cmp .equal (vv iC) (.const 0)) (.return (.const 0))
    (.dec iR .one (.const 0) (.seq (.call (some (some (.local, iR), none)) ConPanqueque.LevelFns.nLhp [ldv iC])
      (.ite (.cmp .equal (vv iR) (.const 1)) (.return (.const 1))
        (.dec iR2 .one (.const 0) (.seq (.call (some (some (.local, iR2), none)) fn [ldo iC 8]) (.return (vv iR2)))))))

def lsCost : List ConLeche.Level → Nat
  | [] => 0
  | u :: us => 1 + ConPanqueque.LevelFns.cost u + (1 + lsCost us)

theorem lsHP_spec {σ : Type} (fn : MlS) (h : Heap) {c : BitVec 64} {us : List ConLeche.Level} (hl : LevelsAt h c us) :
    ∀ t : PanSemStateFiniteExact 64 σ, t.code.lookup fn = some ([(iC, .one)], lsHPBody fn, .one) →
      t.code.lookup ConPanqueque.LevelFns.nLhp = some ([(ConPanqueque.LevelFns.nU, .one)], ConPanqueque.LevelFns.lhpBody, .one) →
      InMem t h → t.locals.lookup iC = some (.val (.word c)) → lsCost us ≤ t.clock →
      ∃ st, evaluateHOLFiniteState t (lsHPBody fn) =
          (some (.returned (.val (.word (ConPanqueque.LevelFns.bit (ConLeche.levelsHaveParam us))))), st) ∧
        Post t st (lsCost us) := by
  induction hl with
  | nil =>
    intro t hc hl hm hlc hck
    refine ⟨emptyLocalsHOLFinite t, ?_, by simp [Post, emptyLocalsHOLFinite]⟩
    unfold lsHPBody
    rw [ite_word t _ _ _ 1 (by simp [vv, evalHOLExact, hlc, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
    simp only [ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true, ↓reduceIte]
    rw [evaluateHOLFiniteState_eq_evaluate_def]
    simp [evalHOLExact, shapeOfHOLExact, ConLeche.levelsHaveParam, ConPanqueque.LevelFns.bit]
  | @cons p q r u us hp h0 h1 hu hus ih =>
    intro t hc hcl hm hlc hck
    have m0 := hm _ _ h0
    have m1 := hm _ _ h1
    simp only [lsCost] at hck
    unfold lsHPBody
    rw [ite_word t _ _ _ 0 (by simp [vv, evalHOLExact, hlc, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hp)]
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    let t1 := setVarHOLFinite iR (.val (.word 0)) t
    obtain ⟨L1, e1⟩ := dec_word' t iR (.const 0) 0 _ (by simp [evalHOLExact])
    have hlc1 : t1.locals.lookup iC = some (.val (.word p)) := by
      simp only [t1]; rw [lookup_setVar_other _ _ (by decide)]; exact hlc
    obtain ⟨st, ⟨pc, pm, pd, pclk, pg, pt⟩, hcall⟩ := call1 t1 ConPanqueque.LevelFns.nLhp ConPanqueque.LevelFns.nU iR
      ConPanqueque.LevelFns.lhpBody (ldv iC) q (ConPanqueque.LevelFns.bit (ConLeche.levelHasParam u))
      (fun st => st.code = t.code ∧ st.memory = t.memory ∧ st.memaddrs = t.memaddrs ∧
        t.clock - 1 ≤ st.clock + ConPanqueque.LevelFns.cost u ∧ st.globals = t.globals ∧ st.topAddr = t.topAddr)
      (by simpa [t1, setVarHOLFinite] using hcl)
      (by unfold ldv; rw [eval_load_word t1 _ p (by simp [vv, evalHOLExact, hlc1]) (by show t.memaddrs p; simpa using m0.1)]
          show some (ValueHOL.val (t.memory p)) = _; rw [show t.memory p = _ by simpa using m0.2])
      (by show t.clock ≠ 0; omega) ⟨0, by simp [t1]⟩
      (fun callee hx => by
        obtain ⟨st, ev, a1, a2, a3, a4, a5, a6⟩ := ConPanqueque.LevelFns.lhp_spec h hu (callEntryStateHOLFinite t1 callee)
          (by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using hcl)
          (fun a w ha => by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using hm a w ha)
          hx (by show _ ≤ t.clock - 1; omega)
        exact ⟨st, ev, by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using a1,
          by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using a2,
          by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using a3,
          by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using a4,
          by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using a5,
          by simpa [callEntryStateHOLFinite, t1, setVarHOLFinite] using a6⟩)
    let t2 := setKvarHOLFinite .local iR (.val (.word (ConPanqueque.LevelFns.bit (ConLeche.levelHasParam u))))
      { st with locals := t1.locals }
    have lr2 : t2.locals.lookup iR = some (.val (.word (ConPanqueque.LevelFns.bit (ConLeche.levelHasParam u)))) := by
      simp [t2, setKvarHOLFinite]
    have lc2 : t2.locals.lookup iC = some (.val (.word p)) := by
      simp only [t2, setKvarHOLFinite]; rw [lookup_setVar_other _ _ (by decide)]; exact hlc1
    rw [e1]; simp only; rw [seq_normal _ hcall]
    by_cases hlu : ConLeche.levelHasParam u = true
    · have lr2' : t2.locals.lookup iR = some (.val (.word 1)) := by simpa [ConPanqueque.LevelFns.bit, hlu] using lr2
      rw [ite_word t2 _ _ _ 1 (by simp [vv, evalHOLExact, lr2', Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
      simp only [ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true, ↓reduceIte]
      have eret : evaluateHOLFiniteState t2 (.return (.const 1)) = (some (.returned (.val (.word 1))), emptyLocalsHOLFinite t2) := by
        rw [evaluateHOLFiniteState_eq_evaluate_def]; simp [evalHOLExact, shapeOfHOLExact]
      rw [eret]
      refine ⟨_, Prod.ext (by simp [ConLeche.levelsHaveParam, hlu, ConPanqueque.LevelFns.bit]) rfl, ?_⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [t2, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, pc]
      · simp [t2, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, pm]
      · simp [t2, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, pd]
      · simp [t2, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, lsCost]; omega
      · simp [t2, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, pg]
      · simp [t2, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, pt]

    · have lr2' : t2.locals.lookup iR = some (.val (.word 0)) := by simpa [ConPanqueque.LevelFns.bit, show ConLeche.levelHasParam u = false by simpa using hlu] using lr2
      rw [ite_word t2 _ _ _ 0 (by simp [vv, evalHOLExact, lr2', Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
      simp only [ne_eq, not_true_eq_false, ↓reduceIte]
      let t3 := setVarHOLFinite iR2 (.val (.word 0)) t2
      obtain ⟨L3, e3⟩ := dec_word' t2 iR2 (.const 0) 0 _ (by simp [evalHOLExact])
      have lc3 : t3.locals.lookup iC = some (.val (.word p)) := by
        simp only [t3]; rw [lookup_setVar_other _ _ (by decide)]; exact lc2
      have hm3 : t3.memory = t.memory := by simp [t3, t2, setKvarHOLFinite, setVarHOLFinite, pm]
      have hd3 : t3.memaddrs = t.memaddrs := by simp [t3, t2, setKvarHOLFinite, setVarHOLFinite, pd]
      have hc3 : t3.code = t.code := by simp [t3, t2, setKvarHOLFinite, setVarHOLFinite, pc]
      have hck3 : t3.clock = st.clock := by simp [t3, t2, setKvarHOLFinite, setVarHOLFinite]
      obtain ⟨st2, ⟨qc, qm, qd, qclk, qg, qt⟩, hcall2⟩ := call1 t3 fn iC iR2 (lsHPBody fn) (ldo iC 8) r
        (ConPanqueque.LevelFns.bit (ConLeche.levelsHaveParam us))
        (fun st2 => st2.code = t.code ∧ st2.memory = t.memory ∧ st2.memaddrs = t.memaddrs ∧
          st.clock - 1 ≤ st2.clock + lsCost us ∧ st2.globals = t.globals ∧ st2.topAddr = t.topAddr)
        (by rw [hc3]; exact hc)
        (by unfold ldo vv; rw [eval_load_word t3 _ (p + 8) (by simp [evalHOLExact, evalListHOLExact, lc3, wordOpHOL,
              wordOp, valueIsWord, valueWord]) (by rw [hd3]; exact m1.1)]
            show some (ValueHOL.val (t3.memory (p + 8))) = _; rw [hm3, m1.2])
        (by rw [hck3]; omega) ⟨0, by simp [t3]⟩
        (fun callee hx => by
          obtain ⟨st2, ev, a1, a2, a3, a4, a5, a6⟩ := ih (callEntryStateHOLFinite t3 callee)
            (by simp only [callEntryStateHOLFinite]; rw [hc3]; exact hc)
            (by simp only [callEntryStateHOLFinite]; rw [hc3]; exact hcl)
            (fun a w ha => by simp only [callEntryStateHOLFinite]; rw [hm3, hd3]; exact hm a w ha)
            hx (by simp only [callEntryStateHOLFinite]; rw [hck3]; omega)
          refine ⟨st2, ev, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
            simp only [callEntryStateHOLFinite] at a1 a2 a3 a4 a5 a6 ⊢
          · rw [a1, hc3]
          · rw [a2, hm3]
          · rw [a3, hd3]
          · rw [hck3] at a4; omega
          · rw [a5]; simp [t3, t2, setKvarHOLFinite, setVarHOLFinite, pg]
          · rw [a6]; simp [t3, t2, setKvarHOLFinite, setVarHOLFinite, pt])
      let t4 := setKvarHOLFinite .local iR2 (.val (.word (ConPanqueque.LevelFns.bit (ConLeche.levelsHaveParam us))))
        { st2 with locals := t3.locals }
      have eret : evaluateHOLFiniteState t4 (.return (vv iR2)) =
          (some (.returned (.val (.word (ConPanqueque.LevelFns.bit (ConLeche.levelsHaveParam us))))), emptyLocalsHOLFinite t4) := by
        rw [evaluateHOLFiniteState_eq_evaluate_def]; simp [evalHOLExact, vv, t4, setKvarHOLFinite, shapeOfHOLExact]
      rw [e3]; simp only; rw [seq_normal _ hcall2, eret]
      refine ⟨_, Prod.ext (by simp [ConLeche.levelsHaveParam, show ConLeche.levelHasParam u = false by simpa using hlu]) rfl, ?_⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        simp [t4, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, qc, qm, qd, qg, qt, lsCost] at qclk pclk ⊢
      omega

end ConPanqueque.LevelsFns
