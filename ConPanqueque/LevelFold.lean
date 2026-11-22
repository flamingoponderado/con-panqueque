import ConPanqueque.LevelFns
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic

/-!
# A verified recursion template: folds over levels

`foldBody fn cz cp gs gm gi` is one Pancake function for every fold over a level
in the arena: leaves return `cz`/`cp`; `succ` recurses on its child and returns
`gs` (over local `a`); `max`/`imax` recurse on both children and return `gm`/`gi`
(over `a`, `b`). `fold_spec` proves it once, by induction: for any `f` whose
equations the expressions satisfy (`FoldSpec`), it returns `f lv`. A concrete
function then needs no induction: `lhp2_spec` gets `levelHasParam` from
`fold_spec` and `lhp_fold` (the expressions' facts). This is how the translator
handles structural recursion: verified templates, instantiated with
`pan_exp`-compiled expressions.
-/

namespace ConPanqueque.LevelFold

def nU := ofString "u"
def nT := ofString "tg"
def nA := ofString "a"
def nB := ofString "b"
def vU : ExpHOL 64 := .var .local nU
def vT : ExpHOL 64 := .var .local nT

/-- A fold over a level in the arena: `cz`/`cp` for leaves, `gs` (over local `a`,
the child's result) for `succ`, `gm`/`gi` (over `a`, `b`) for `max`/`imax`;
`fn` is the function's own name (for the recursive calls). -/
def foldBody (fn : MlS) (cz cp gs gm gi : ExpHOL 64) : ProgHOL 64 :=
  .dec nT .one (.load .one vU)
    (.ite (.cmp .equal vT (.const 0)) (.return cz)
      (.ite (.cmp .equal vT (.const 4)) (.return cp)
        (.dec nA .one (.const 0)
          (.seq (.call (some (some (.local, nA), none)) fn [.load .one (.op .add [vU, .const 16])])
            (.ite (.cmp .equal vT (.const 1)) (.return gs)
              (.dec nB .one (.const 0)
                (.seq (.call (some (some (.local, nB), none)) fn [.load .one (.op .add [vU, .const 24])])
                  (.ite (.cmp .equal vT (.const 2)) (.return gm) (.return gi)))))))))

/-- Calls made: one per child, recursively. -/
def cost : ConLeche.Level → Nat
  | .zero | .param _ => 0
  | .succ u => 1 + cost u
  | .max u v | .imax u v => 2 + cost u + cost v

end ConPanqueque.LevelFold

namespace ConPanqueque.LevelFold

def EvW {σ : Type} (t : PanSemStateFiniteExact 64 σ) (e : ExpHOL 64) (w : UInt64) : Prop :=
  @evalHOLExact 64 σ _ t.toExact (fun x => Classical.propDecidable (t.memaddrs x)) e = some (.val (.word w.toBitVec))

def Post {σ : Type} (s st : PanSemStateFiniteExact 64 σ) (c : Nat) : Prop :=
  st.code = s.code ∧ st.memory = s.memory ∧ st.memaddrs = s.memaddrs ∧ s.clock ≤ st.clock + c

/-- The expressions of a fold and the function they compute. -/
structure FoldSpec (fn : MlS) (cz cp gs gm gi : ExpHOL 64) (f : ConLeche.Level → UInt64) : Prop where
  hz : ∀ {σ : Type} (t : PanSemStateFiniteExact 64 σ), EvW t cz (f .zero)
  hp : ∀ {σ : Type} (t : PanSemStateFiniteExact 64 σ) n, EvW t cp (f (.param n))
  hs : ∀ {σ : Type} (t : PanSemStateFiniteExact 64 σ) u,
    t.locals.lookup nA = some (.val (.word (f u).toBitVec)) → EvW t gs (f (.succ u))
  hm : ∀ {σ : Type} (t : PanSemStateFiniteExact 64 σ) u v,
    t.locals.lookup nA = some (.val (.word (f u).toBitVec)) →
    t.locals.lookup nB = some (.val (.word (f v).toBitVec)) → EvW t gm (f (.max u v))
  hi : ∀ {σ : Type} (t : PanSemStateFiniteExact 64 σ) u v,
    t.locals.lookup nA = some (.val (.word (f u).toBitVec)) →
    t.locals.lookup nB = some (.val (.word (f v).toBitVec)) → EvW t gi (f (.imax u v))

end ConPanqueque.LevelFold

namespace ConPanqueque.LevelFold

variable {fn : MlS} {cz cp gs gm gi : ExpHOL 64} {f : ConLeche.Level → UInt64}

theorem dRT : nA ≠ nT := by decide
theorem dBT : nB ≠ nT := by decide
theorem dUA : nU ≠ nA := by decide
theorem dUB : nU ≠ nB := by decide
theorem dUT : nU ≠ nT := by decide
theorem dBA : nB ≠ nA := by decide

/-- A leaf: return the leaf expression. -/
theorem fold_leaf {σ : Type} (s : PanSemStateFiniteExact 64 σ) (h : Heap) (p tg : BitVec 64) (e : ExpHOL 64)
    (w : UInt64) (hm : InMem s h) (h0 : h p = some (.word tg)) (hpu : s.locals.lookup nU = some (.val (.word p)))
    (htg : (tg = 0 ∧ e = cz) ∨ (tg = 4 ∧ e = cp))
    (he : ∀ t : PanSemStateFiniteExact 64 σ, EvW t e w) :
    ∃ st, evaluateHOLFiniteState s (foldBody fn cz cp gs gm gi) = (some (.returned (.val (.word w.toBitVec))), st) ∧
      Post s st 0 := by
  obtain ⟨d0, m0⟩ := hm _ _ h0
  unfold foldBody
  rcases htg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨L, hdec⟩ := dec_word' s nT (.load .one vU) 0 _ (by
      rw [eval_load_word s _ _ (by simp [evalHOLExact, vU, hpu]) d0, m0])
    let s1 := setVarHOLFinite nT (.val (.word 0)) s
    have lt : s1.locals.lookup nT = some (.val (.word 0)) := by simp [s1]
    rw [hdec, ite_word s1 _ _ _ 1 (by simp [evalHOLExact, vT, lt, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
    rw [if_pos (by decide : (1 : BitVec 64) ≠ 0), evaluateHOLFiniteState_eq_evaluate_def]
    simp only
    rw [he s1]
    refine ⟨_, Prod.ext (by simp [shapeOfHOLExact]) rfl, ?_⟩
    simp [Post, s1, setVarHOLFinite, emptyLocalsHOLFinite, shapeOfHOLExact]
  · obtain ⟨L, hdec⟩ := dec_word' s nT (.load .one vU) 4 _ (by
      rw [eval_load_word s _ _ (by simp [evalHOLExact, vU, hpu]) d0, m0])
    let s1 := setVarHOLFinite nT (.val (.word 4)) s
    have lt : s1.locals.lookup nT = some (.val (.word 4)) := by simp [s1]
    rw [hdec, ite_word s1 _ _ _ 0 (by simp [evalHOLExact, vT, lt, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]),
      ite_word s1 _ _ _ 1 (by simp [evalHOLExact, vT, lt, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
    simp only [ne_eq, not_true_eq_false, ite_false]
    rw [if_pos (by decide : (1 : BitVec 64) ≠ 0), evaluateHOLFiniteState_eq_evaluate_def]
    simp only
    rw [he s1]
    refine ⟨_, Prod.ext (by simp [shapeOfHOLExact]) rfl, ?_⟩
    simp [Post, s1, setVarHOLFinite, emptyLocalsHOLFinite, shapeOfHOLExact]

end ConPanqueque.LevelFold

namespace ConPanqueque.LevelFold
variable {fn : MlS} {cz cp gs gm gi : ExpHOL 64} {f : ConLeche.Level → UInt64}

/-- The common prefix of the inner nodes: load the tag, declare `a`, call on the
first child (at offset 16). -/
theorem fold_first {σ : Type} (s : PanSemStateFiniteExact 64 σ) (h : Heap) (p q tg : BitVec 64)
    (u : ConLeche.Level) (c : Nat)
    (hc : s.code.lookup fn = some ([(nU, .one)], foldBody fn cz cp gs gm gi, .one))
    (hm : InMem s h) (h0 : h p = some (.word tg)) (h2 : h (p + 16) = some (.word q))
    (hpu : s.locals.lookup nU = some (.val (.word p))) (hck : 1 + c ≤ s.clock)
    (ih : ∀ t : PanSemStateFiniteExact 64 σ,
      t.code.lookup fn = some ([(nU, .one)], foldBody fn cz cp gs gm gi, .one) → InMem t h →
      t.locals.lookup nU = some (.val (.word q)) → c ≤ t.clock →
      ∃ st, evaluateHOLFiniteState t (foldBody fn cz cp gs gm gi) = (some (.returned (.val (.word (f u).toBitVec))), st) ∧
        Post t st c) :
    let s1 := setVarHOLFinite nT (.val (.word tg)) s
    let s2 := setVarHOLFinite nA (.val (.word 0)) s1
    ∃ st : PanSemStateFiniteExact 64 σ, st.code = s.code ∧ st.memory = s.memory ∧ st.memaddrs = s.memaddrs ∧
      s.clock - 1 ≤ st.clock + c ∧
      evaluateHOLFiniteState s2 (.call (some (some (.local, nA), none)) fn [.load .one (.op .add [vU, .const 16])]) =
        (none, setKvarHOLFinite .local nA (.val (.word (f u).toBitVec)) { st with locals := s2.locals }) := by
  intro s1 s2
  obtain ⟨d2, m2⟩ := hm _ _ h2
  have lu2 : s2.locals.lookup nU = some (.val (.word p)) := by
    simp only [s2, s1]; rw [lookup_setVar_other _ _ dUA, lookup_setVar_other _ _ dUT]; exact hpu
  obtain ⟨st, ⟨pc, pm, pd, pclk⟩, hcall⟩ := call1 s2 fn nU nA (foldBody fn cz cp gs gm gi)
    (.load .one (.op .add [vU, .const 16])) q (f u).toBitVec
    (fun st => st.code = s.code ∧ st.memory = s.memory ∧ st.memaddrs = s.memaddrs ∧ s.clock - 1 ≤ st.clock + c)
    (by simpa [s2, s1, setVarHOLFinite] using hc)
    (by rw [eval_load_word s2 _ (p + 16) (by simp [evalHOLExact, evalListHOLExact, vU, lu2, wordOpHOL, wordOp,
      valueIsWord, valueWord]) (by simpa [s2, s1, setVarHOLFinite] using d2)]
        simp only [s2, s1, setVarHOLFinite]; rw [m2])
    (by simp [s2, s1, setVarHOLFinite]; omega)
    ⟨0, by simp [s2]⟩
    (fun callee hcl => by
      obtain ⟨st, ev, post⟩ := ih (callEntryStateHOLFinite s2 callee)
        (by simpa [callEntryStateHOLFinite, s2, s1, setVarHOLFinite] using hc)
        (fun a w ha => by simpa [callEntryStateHOLFinite, s2, s1, setVarHOLFinite] using hm a w ha)
        (by simpa [callEntryStateHOLFinite] using hcl)
        (by simp [callEntryStateHOLFinite, s2, s1, setVarHOLFinite]; omega)
      obtain ⟨a1, a2, a3, a4⟩ := post
      exact ⟨st, ev, by simpa [callEntryStateHOLFinite, s2, s1, setVarHOLFinite] using a1,
        by simpa [callEntryStateHOLFinite, s2, s1, setVarHOLFinite] using a2,
        by simpa [callEntryStateHOLFinite, s2, s1, setVarHOLFinite] using a3,
        by simpa [callEntryStateHOLFinite, s2, s1, setVarHOLFinite] using a4⟩)
  exact ⟨st, pc, pm, pd, pclk, hcall⟩

end ConPanqueque.LevelFold

namespace ConPanqueque.LevelFold
variable {fn : MlS} {cz cp gs gm gi : ExpHOL 64} {f : ConLeche.Level → UInt64}

/-- A recursive call `x = fn(ld (u + off))` on a child at `p + off`, from any state. -/
theorem fold_call {σ : Type} (t : PanSemStateFiniteExact 64 σ) (h : Heap) (x : MlS) (off p q : BitVec 64)
    (u : ConLeche.Level) (c : Nat)
    (hc : t.code.lookup fn = some ([(nU, .one)], foldBody fn cz cp gs gm gi, .one))
    (hm : InMem t h) (h2 : h (p + off) = some (.word q))
    (hpu : t.locals.lookup nU = some (.val (.word p))) (hx : ∃ w0, t.locals.lookup x = some (.val (.word w0)))
    (hck : 1 + c ≤ t.clock)
    (ih : ∀ t' : PanSemStateFiniteExact 64 σ,
      t'.code.lookup fn = some ([(nU, .one)], foldBody fn cz cp gs gm gi, .one) → InMem t' h →
      t'.locals.lookup nU = some (.val (.word q)) → c ≤ t'.clock →
      ∃ st, evaluateHOLFiniteState t' (foldBody fn cz cp gs gm gi) = (some (.returned (.val (.word (f u).toBitVec))), st) ∧
        Post t' st c) :
    ∃ st : PanSemStateFiniteExact 64 σ, st.code = t.code ∧ st.memory = t.memory ∧ st.memaddrs = t.memaddrs ∧
      t.clock - 1 ≤ st.clock + c ∧
      evaluateHOLFiniteState t (.call (some (some (.local, x), none)) fn [.load .one (.op .add [vU, .const off])]) =
        (none, setKvarHOLFinite .local x (.val (.word (f u).toBitVec)) { st with locals := t.locals }) := by
  obtain ⟨d2, m2⟩ := hm _ _ h2
  obtain ⟨st, ⟨pc, pm, pd, pclk⟩, hcall⟩ := call1 t fn nU x (foldBody fn cz cp gs gm gi)
    (.load .one (.op .add [vU, .const off])) q (f u).toBitVec
    (fun st => st.code = t.code ∧ st.memory = t.memory ∧ st.memaddrs = t.memaddrs ∧ t.clock - 1 ≤ st.clock + c)
    hc
    (by rw [eval_load_word t _ (p + off) (by simp [evalHOLExact, evalListHOLExact, vU, hpu, wordOpHOL, wordOp,
      valueIsWord, valueWord]) d2, m2])
    (by omega) hx
    (fun callee hcl => by
      obtain ⟨st, ev, post⟩ := ih (callEntryStateHOLFinite t callee)
        (by simpa [callEntryStateHOLFinite] using hc)
        (fun a w ha => by simpa [callEntryStateHOLFinite] using hm a w ha)
        (by simpa [callEntryStateHOLFinite] using hcl)
        (by simp [callEntryStateHOLFinite]; omega)
      obtain ⟨a1, a2, a3, a4⟩ := post
      exact ⟨st, ev, by simpa [callEntryStateHOLFinite] using a1, by simpa [callEntryStateHOLFinite] using a2,
        by simpa [callEntryStateHOLFinite] using a3, by simpa [callEntryStateHOLFinite] using a4⟩)
  exact ⟨st, pc, pm, pd, pclk, hcall⟩

end ConPanqueque.LevelFold

namespace ConPanqueque.LevelFold
variable {fn : MlS} {cz cp gs gm gi : ExpHOL 64} {f : ConLeche.Level → UInt64}

/-- Inner nodes: tag `tg ∈ {1, 2, 3}`; the result for `tg = 1` comes from `gs` (one
child), for `tg = 2, 3` from `gm`/`gi` (two children). -/
theorem fold_inner {σ : Type} (sp : FoldSpec fn cz cp gs gm gi f) (h : Heap) (p q r tg : BitVec 64)
    (u v : ConLeche.Level) (res : UInt64) (cu cv : Nat)
    (htg : tg = 1 ∨ tg = 2 ∨ tg = 3)
    (hres : (tg = 1 → res = f (.succ u)) ∧ (tg = 2 → res = f (.max u v)) ∧ (tg = 3 → res = f (.imax u v)))
    (h0 : h p = some (.word tg)) (h2 : h (p + 16) = some (.word q)) (h3 : tg ≠ 1 → h (p + 24) = some (.word r))
    (ihu : ∀ t : PanSemStateFiniteExact 64 σ,
      t.code.lookup fn = some ([(nU, .one)], foldBody fn cz cp gs gm gi, .one) → InMem t h →
      t.locals.lookup nU = some (.val (.word q)) → cu ≤ t.clock →
      ∃ st, evaluateHOLFiniteState t (foldBody fn cz cp gs gm gi) = (some (.returned (.val (.word (f u).toBitVec))), st) ∧
        Post t st cu)
    (ihv : tg ≠ 1 → ∀ t : PanSemStateFiniteExact 64 σ,
      t.code.lookup fn = some ([(nU, .one)], foldBody fn cz cp gs gm gi, .one) → InMem t h →
      t.locals.lookup nU = some (.val (.word r)) → cv ≤ t.clock →
      ∃ st, evaluateHOLFiniteState t (foldBody fn cz cp gs gm gi) = (some (.returned (.val (.word (f v).toBitVec))), st) ∧
        Post t st cv)
    (s : PanSemStateFiniteExact 64 σ) (hc : s.code.lookup fn = some ([(nU, .one)], foldBody fn cz cp gs gm gi, .one))
    (hm : InMem s h) (hpu : s.locals.lookup nU = some (.val (.word p)))
    (hck : 1 + cu + (if tg = 1 then 0 else 1 + cv) ≤ s.clock) :
    ∃ st, evaluateHOLFiniteState s (foldBody fn cz cp gs gm gi) = (some (.returned (.val (.word res.toBitVec))), st) ∧
      Post s st (1 + cu + (if tg = 1 then 0 else 1 + cv)) := by
  obtain ⟨d0, m0⟩ := hm _ _ h0
  have n0 : ¬ tg = 0#64 := by rcases htg with rfl | rfl | rfl <;> decide
  have n4 : ¬ tg = 4#64 := by rcases htg with rfl | rfl | rfl <;> decide
  obtain ⟨L1, hdec1⟩ := dec_word' s nT (.load .one vU) tg _ (by
    rw [eval_load_word s _ _ (by simp [evalHOLExact, vU, hpu]) d0, m0])
  let s1 := setVarHOLFinite nT (.val (.word tg)) s
  have lt1 : s1.locals.lookup nT = some (.val (.word tg)) := by simp [s1]
  obtain ⟨L2, hdec2⟩ := dec_word' s1 nA (.const 0) 0 _ (by simp [evalHOLExact])
  let s2 := setVarHOLFinite nA (.val (.word 0)) s1
  have lt2 : s2.locals.lookup nT = some (.val (.word tg)) := by
    simp only [s2]; rw [lookup_setVar_other _ _ (Ne.symm dRT)]; exact lt1
  have lu2 : s2.locals.lookup nU = some (.val (.word p)) := by
    simp only [s2, s1]; rw [lookup_setVar_other _ _ dUA, lookup_setVar_other _ _ dUT]; exact hpu
  have ck1 : 1 + cu ≤ s2.clock := by
    simp [s2, s1, setVarHOLFinite]; split at hck <;> omega
  obtain ⟨st, pc, pm, pd, pclk, hcall⟩ := fold_call s2 h nA 16 p q u cu
    (by simpa [s2, s1, setVarHOLFinite] using hc)
    (fun a w ha => by simpa [s2, s1, setVarHOLFinite] using hm a w ha) h2 lu2 ⟨0, by simp [s2]⟩ ck1 ihu
  let s3 := setKvarHOLFinite .local nA (.val (.word (f u).toBitVec)) { st with locals := s2.locals }
  have lt3 : s3.locals.lookup nT = some (.val (.word tg)) := by
    simp only [s3, setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dRT)]; exact lt2
  have la3 : s3.locals.lookup nA = some (.val (.word (f u).toBitVec)) := by simp [s3, setKvarHOLFinite]
  have lu3 : s3.locals.lookup nU = some (.val (.word p)) := by
    simp only [s3, setKvarHOLFinite]; rw [lookup_setVar_other _ _ dUA]; exact lu2
  unfold foldBody
  rw [hdec1, ite_word s1 _ _ _ 0 (by simp [evalHOLExact, vT, lt1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, n0]),
    ite_word s1 _ _ _ 0 (by simp [evalHOLExact, vT, lt1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, n4])]
  simp only [ne_eq, not_true_eq_false, ite_false]
  rw [hdec2, show setVarHOLFinite nA (.val (.word 0)) s1 = s2 from rfl, seq_normal _ hcall]
  rcases htg with rfl | htg23
  · -- succ
    rw [ite_word s3 _ _ _ 1 (by simp [evalHOLExact, vT, lt3, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
    rw [if_pos (by decide : (1 : BitVec 64) ≠ 0), evaluateHOLFiniteState_eq_evaluate_def]
    simp only
    rw [hres.1 rfl, sp.hs s3 u la3]
    simp only [shapeOfHOLExact, sizeOfShapeWithContextHOL]
    simp only [show (1 : Nat) ≤ 32 from by decide, ite_true]
    refine ⟨_, rfl, ?_⟩
    refine ⟨by simp [s3, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, pc, s2, s1],
      by simp [s3, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, pm, s2, s1],
      by simp [s3, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, pd, s2, s1], ?_⟩
    simp [s3, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite] at pclk ⊢
    simp [s2, s1, setVarHOLFinite] at pclk
    omega
  · have n1 : ¬ tg = 1#64 := by rcases htg23 with rfl | rfl <;> decide
    have hne1 : tg ≠ 1 := n1
    rw [ite_word s3 _ _ _ 0 (by simp [evalHOLExact, vT, lt3, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, n1])]
    simp only [ne_eq, not_true_eq_false, ite_false]
    obtain ⟨L4, hdec4⟩ := dec_word' s3 nB (.const 0) 0 _ (by simp [evalHOLExact])
    let s4 := setVarHOLFinite nB (.val (.word 0)) s3
    have lu4 : s4.locals.lookup nU = some (.val (.word p)) := by
      simp only [s4]; rw [lookup_setVar_other _ _ dUB]; exact lu3
    have ck2 : 1 + cv ≤ s4.clock := by
      simp [s4, s3, setKvarHOLFinite, setVarHOLFinite]
      simp [s2, s1, setVarHOLFinite] at pclk
      simp [n1] at hck; omega
    obtain ⟨st2, qc, qm, qd, qclk, hcall2⟩ := fold_call s4 h nB 24 p r v cv
      (by simpa [s4, s3, setKvarHOLFinite, setVarHOLFinite, pc, s2, s1] using hc)
      (fun a w ha => by have := hm a w ha; simpa [s4, s3, setKvarHOLFinite, setVarHOLFinite, pm, pd, s2, s1] using this)
      (h3 hne1) lu4 ⟨0, by simp [s4]⟩ ck2 (ihv hne1)
    let s5 := setKvarHOLFinite .local nB (.val (.word (f v).toBitVec)) { st2 with locals := s4.locals }
    have lt5 : s5.locals.lookup nT = some (.val (.word tg)) := by
      simp only [s5, setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dBT)]
      simp only [s4]; rw [lookup_setVar_other _ _ (Ne.symm dBT)]; exact lt3
    have la5 : s5.locals.lookup nA = some (.val (.word (f u).toBitVec)) := by
      simp only [s5, setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dBA)]
      simp only [s4]; rw [lookup_setVar_other _ _ (Ne.symm dBA)]; exact la3
    have lb5 : s5.locals.lookup nB = some (.val (.word (f v).toBitVec)) := by simp [s5, setKvarHOLFinite]
    rw [hdec4, show setVarHOLFinite nB (.val (.word 0)) s3 = s4 from rfl, seq_normal _ hcall2]
    have post : ∀ st' : PanSemStateFiniteExact 64 σ, st' = emptyLocalsHOLFinite s5 →
        Post s { st' with locals := L1 } (1 + cu + (if tg = 1 then 0 else 1 + cv)) := by
      intro st' e; subst e
      refine ⟨by simp [s5, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, qc, s4, s3, pc, s2, s1],
        by simp [s5, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, qm, s4, s3, pm, s2, s1],
        by simp [s5, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, qd, s4, s3, pd, s2, s1], ?_⟩
      simp [s5, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, n1] at qclk ⊢
      simp [s4, s3, setKvarHOLFinite, setVarHOLFinite] at qclk
      simp [s2, s1, setVarHOLFinite] at pclk
      omega
    rcases htg23 with rfl | rfl
    · rw [ite_word s5 _ _ _ 1 (by simp [evalHOLExact, vT, lt5, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
      rw [if_pos (by decide : (1 : BitVec 64) ≠ 0), evaluateHOLFiniteState_eq_evaluate_def]
      simp only
      rw [hres.2.1 rfl, sp.hm s5 u v la5 lb5]
      exact ⟨_, Prod.ext (by simp [shapeOfHOLExact]) rfl, post _ (by simp [shapeOfHOLExact])⟩
    · rw [ite_word s5 _ _ _ 0 (by simp [evalHOLExact, vT, lt5, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
      simp only [ne_eq, not_true_eq_false, ite_false]
      rw [evaluateHOLFiniteState_eq_evaluate_def]
      simp only
      rw [hres.2.2 rfl, sp.hi s5 u v la5 lb5]
      exact ⟨_, Prod.ext (by simp [shapeOfHOLExact]) rfl, post _ (by simp [shapeOfHOLExact])⟩

end ConPanqueque.LevelFold

namespace ConPanqueque.LevelFold
variable {fn : MlS} {cz cp gs gm gi : ExpHOL 64} {f : ConLeche.Level → UInt64}

/-- The fold template computes `f`: from a state whose code table holds it, on a
level in the arena, it returns `f lv`, leaves code and memory unchanged, and uses
at most `cost lv` clock ticks. -/
theorem fold_spec {σ : Type} (sp : FoldSpec fn cz cp gs gm gi f) (h : Heap) {p : BitVec 64}
    {lv : ConLeche.Level} (hl : LevelAt h p lv) :
    ∀ s : PanSemStateFiniteExact 64 σ,
      s.code.lookup fn = some ([(nU, .one)], foldBody fn cz cp gs gm gi, .one) → InMem s h →
      s.locals.lookup nU = some (.val (.word p)) → cost lv ≤ s.clock →
      ∃ st, evaluateHOLFiniteState s (foldBody fn cz cp gs gm gi) = (some (.returned (.val (.word (f lv).toBitVec))), st) ∧
        Post s st (cost lv) := by
  induction hl with
  | zero hp h0 h1 =>
    intro s hc hm hpu hck
    exact fold_leaf s h _ 0 cz (f .zero) hm h0 hpu (.inl ⟨rfl, rfl⟩) (fun t => sp.hz t)
  | param hp h0 h1 h2 hn =>
    intro s hc hm hpu hck
    exact fold_leaf s h _ 4 cp _ hm h0 hpu (.inr ⟨rfl, rfl⟩) (fun t => sp.hp t _)
  | @succ p q u hp h0 h1 h2 hu ih =>
    intro s hc hm hpu hck
    have := fold_inner sp h p q 0 1 u u (f (.succ u)) (cost u) 0 (.inl rfl) ⟨fun _ => rfl, fun h => absurd h (by decide), fun h => absurd h (by decide)⟩
      h0 h2 (fun h => absurd rfl h) ih (fun h => absurd rfl h) s hc hm hpu (by simp [cost] at hck ⊢; omega)
    simpa [cost, Nat.add_comm] using this
  | @max p q r u v hp h0 h1 h2 h3 hu hv ihu ihv =>
    intro s hc hm hpu hck
    have := fold_inner sp h p q r 2 u v (f (.max u v)) (cost u) (cost v) (.inr (.inl rfl))
      ⟨fun h => absurd h (by decide), fun _ => rfl, fun h => absurd h (by decide)⟩ h0 h2 (fun _ => h3) ihu (fun _ => ihv) s hc hm hpu
      (by simp [cost] at hck ⊢; omega)
    simp only [show (2 : BitVec 64) = 1 ↔ False from by decide, ite_false] at this
    refine ⟨this.choose, this.choose_spec.1, ?_⟩
    have p' := this.choose_spec.2
    simp only [Post, cost] at p' ⊢
    exact ⟨p'.1, p'.2.1, p'.2.2.1, by omega⟩
  | @imax p q r u v hp h0 h1 h2 h3 hu hv ihu ihv =>
    intro s hc hm hpu hck
    have := fold_inner sp h p q r 3 u v (f (.imax u v)) (cost u) (cost v) (.inr (.inr rfl))
      ⟨fun h => absurd h (by decide), fun h => absurd h (by decide), fun _ => rfl⟩ h0 h2 (fun _ => h3) ihu (fun _ => ihv) s hc hm hpu
      (by simp [cost] at hck ⊢; omega)
    simp only [show (3 : BitVec 64) = 1 ↔ False from by decide, ite_false] at this
    refine ⟨this.choose, this.choose_spec.1, ?_⟩
    have p' := this.choose_spec.2
    simp only [Post, cost] at p' ⊢
    exact ⟨p'.1, p'.2.1, p'.2.2.1, by omega⟩

end ConPanqueque.LevelFold

namespace ConPanqueque.LevelFold

/-- `levelHasParam` as a word (1/0). -/
def lhpW (lv : ConLeche.Level) : UInt64 := if ConLeche.levelHasParam lv then 1 else 0

def vA : ExpHOL 64 := .var .local nA
def vB : ExpHOL 64 := .var .local nB
/-- `max a b` as `a + (b - a)·[a < b]`. -/
def maxAB : ExpHOL 64 := .op .add [vA, .panop .mul [.op .sub [vB, vA], .cmp .lower vA vB]]

def nLhp2 := ofString "levelHasParam2"

/-- `levelHasParam` by the fold template: no induction, only the expressions' facts. -/
theorem lhp_fold : FoldSpec nLhp2 (.const 0) (.const 1) vA maxAB maxAB lhpW := by
  refine ⟨fun t => ?_, fun t n => ?_, fun t u hu => ?_, fun t u v hu hv => ?_, fun t u v hu hv => ?_⟩
  · simp [EvW, evalHOLExact, lhpW, ConLeche.levelHasParam]
  · simp [EvW, evalHOLExact, lhpW, ConLeche.levelHasParam]
  · cases h1 : ConLeche.levelHasParam u <;>
      simp [EvW, evalHOLExact, vA, hu, lhpW, ConLeche.levelHasParam, h1]
  · cases h1 : ConLeche.levelHasParam u <;> cases h2 : ConLeche.levelHasParam v <;>
      simp [EvW, maxAB, vA, vB, evalHOLExact, evalListHOLExact, hu, hv, wordOpHOL, wordOp, valueIsWord,
        valueWord, panOpHOL, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, lhpW, ConLeche.levelHasParam, h1, h2]
  · cases h1 : ConLeche.levelHasParam u <;> cases h2 : ConLeche.levelHasParam v <;>
      simp [EvW, maxAB, vA, vB, evalHOLExact, evalListHOLExact, hu, hv, wordOpHOL, wordOp, valueIsWord,
        valueWord, panOpHOL, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, lhpW, ConLeche.levelHasParam, h1, h2]

end ConPanqueque.LevelFold

namespace ConPanqueque.LevelFold
/-- `levelHasParam` in Pancake, as an instance of the verified fold template. -/
theorem lhp2_spec {σ : Type} (h : Heap) {p : BitVec 64} {lv : ConLeche.Level} (hl : LevelAt h p lv)
    (s : PanSemStateFiniteExact 64 σ)
    (hc : s.code.lookup nLhp2 = some ([(nU, .one)], foldBody nLhp2 (.const 0) (.const 1) vA maxAB maxAB, .one))
    (hm : InMem s h) (hu : s.locals.lookup nU = some (.val (.word p))) (hck : cost lv ≤ s.clock) :
    ∃ st, evaluateHOLFiniteState s (foldBody nLhp2 (.const 0) (.const 1) vA maxAB maxAB) =
      (some (.returned (.val (.word (lhpW lv).toBitVec))), st) ∧ Post s st (cost lv) :=
  fold_spec lhp_fold h hl s hc hm hu hck
end ConPanqueque.LevelFold
