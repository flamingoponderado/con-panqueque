import ConPanqueque.Rep
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic

/-!
# Recursive level functions: `levelHasParam`

The first recursive con-leche function in Pancake: `lhpBody` walks a level in
the arena, calling itself on the children (`call1`). `lhp_spec`, by induction
on `LevelAt`: from a state whose code table holds the function, it returns
`levelHasParam lv` (as 1/0), leaves code and memory unchanged, and consumes at
most `cost lv` clock ticks.
-/

namespace ConPanqueque.LevelFns

def nU := ofString "u"
def nT := ofString "tg"
def nR := ofString "a"
def nLhp := ofString "levelHasParam"

def vU : ExpHOL 64 := .var .local nU
def vT : ExpHOL 64 := .var .local nT
def vR : ExpHOL 64 := .var .local nR
def callR (e : ExpHOL 64) : ProgHOL 64 := .call (some (some (.local, nR), none)) nLhp [e]

/-- con-leche's `levelHasParam` in Pancake (1 = true, 0 = false). -/
def lhpBody : ProgHOL 64 :=
  .dec nT .one (.load .one vU)
    (.ite (.cmp .equal vT (.const 4)) (.return (.const 1))
      (.ite (.cmp .equal vT (.const 0)) (.return (.const 0))
        (.dec nR .one (.const 0)
          (.seq (callR (.load .one (.op .add [vU, .const 16])))
            (.ite (.cmp .equal vT (.const 1)) (.return vR)
              (.ite (.cmp .equal vR (.const 1)) (.return (.const 1))
                (.seq (callR (.load .one (.op .add [vU, .const 24]))) (.return vR))))))))

/-- Calls made: one per child, recursively. -/
def cost : ConLeche.Level → Nat
  | .zero | .param _ => 0
  | .succ u => 1 + cost u
  | .max u v | .imax u v => 2 + cost u + cost v

def bit (b : Bool) : BitVec 64 := if b then 1 else 0

end ConPanqueque.LevelFns

namespace ConPanqueque.LevelFns

def Post {σ : Type} (s st : PanSemStateFiniteExact 64 σ) (c : Nat) : Prop :=
  st.code = s.code ∧ st.memory = s.memory ∧ st.memaddrs = s.memaddrs ∧ s.clock ≤ st.clock + c

/-- The `max`/`imax` case of `lhp_spec`, for node tag `tg ∈ {2, 3}`. -/
theorem lhp_bin {σ : Type} (h : Heap) (p q r : BitVec 64) (tg : BitVec 64) (u v : ConLeche.Level)
    (htg4 : tg ≠ 4) (htg0 : tg ≠ 0) (htg1 : tg ≠ 1)
    (h0 : h p = some (.word tg)) (h2 : h (p + 16) = some (.word q)) (h3 : h (p + 24) = some (.word r))
    (ihu : ∀ s : PanSemStateFiniteExact 64 σ,
      s.code.lookup nLhp = some ([(nU, .one)], lhpBody, .one) → InMem s h →
      s.locals.lookup nU = some (.val (.word q)) → cost u ≤ s.clock →
      ∃ st, evaluateHOLFiniteState s lhpBody = (some (.returned (.val (.word (bit (ConLeche.levelHasParam u))))), st) ∧
        Post s st (cost u))
    (ihv : ∀ s : PanSemStateFiniteExact 64 σ,
      s.code.lookup nLhp = some ([(nU, .one)], lhpBody, .one) → InMem s h →
      s.locals.lookup nU = some (.val (.word r)) → cost v ≤ s.clock →
      ∃ st, evaluateHOLFiniteState s lhpBody = (some (.returned (.val (.word (bit (ConLeche.levelHasParam v))))), st) ∧
        Post s st (cost v))
    (s : PanSemStateFiniteExact 64 σ) (hc : s.code.lookup nLhp = some ([(nU, .one)], lhpBody, .one))
    (hm : InMem s h) (hpu : s.locals.lookup nU = some (.val (.word p))) (hck : 2 + cost u + cost v ≤ s.clock) :
    ∃ st, evaluateHOLFiniteState s lhpBody =
        (some (.returned (.val (.word (bit (ConLeche.levelHasParam u || ConLeche.levelHasParam v))))), st) ∧
      Post s st (2 + cost u + cost v) := by
  have n4 : ¬ tg = 4#64 := htg4
  have n0 : ¬ tg = 0#64 := htg0
  have n1 : ¬ tg = 1#64 := htg1
  obtain ⟨d0, m0⟩ := hm _ _ h0
  obtain ⟨d2, m2⟩ := hm _ _ h2
  obtain ⟨d3, m3⟩ := hm _ _ h3
  obtain ⟨L1, hdec1⟩ := dec_word' s nT (.load .one vU) tg _ (by
    rw [eval_load_word s _ _ (by simp [evalHOLExact, vU, hpu]) d0, m0])
  let s1 := setVarHOLFinite nT (.val (.word tg)) s
  have lt1 : s1.locals.lookup nT = some (.val (.word tg)) := by simp [s1]
  obtain ⟨L2, hdec2⟩ := dec_word' s1 nR (.const 0) 0 _ (by simp [evalHOLExact])
  let s2 := setVarHOLFinite nR (.val (.word 0)) s1
  have dRT : nR ≠ nT := by decide
  have dUR : nU ≠ nR := by decide
  have dUT : nU ≠ nT := by decide
  have lt2 : s2.locals.lookup nT = some (.val (.word tg)) := by
    simp only [s2]; rw [lookup_setVar_other _ _ (Ne.symm dRT)]; exact lt1
  have lu2 : s2.locals.lookup nU = some (.val (.word p)) := by
    simp only [s2, s1]; rw [lookup_setVar_other _ _ dUR, lookup_setVar_other _ _ dUT]; exact hpu
  -- first call, on u
  obtain ⟨st, ⟨pc, pm, pd, pclk⟩, hcall⟩ := call1 s2 nLhp nU nR lhpBody (.load .one (.op .add [vU, .const 16])) q
    (bit (ConLeche.levelHasParam u))
    (fun st => st.code = s.code ∧ st.memory = s.memory ∧ st.memaddrs = s.memaddrs ∧ s.clock - 1 ≤ st.clock + cost u)
    (by simpa [s2, s1, setVarHOLFinite] using hc)
    (by rw [eval_load_word s2 _ (p + 16) (by simp [evalHOLExact, evalListHOLExact, vU, lu2, wordOpHOL, wordOp,
      valueIsWord, valueWord]) (by simpa [s2, s1, setVarHOLFinite] using d2)]
        simp only [s2, s1, setVarHOLFinite]; rw [m2])
    (by simp [s2, s1, setVarHOLFinite]; omega)
    ⟨0, by simp [s2]⟩
    (fun callee hcl => by
      obtain ⟨st, ev, post⟩ := ihu (callEntryStateHOLFinite s2 callee)
        (by simpa [callEntryStateHOLFinite, s2, s1, setVarHOLFinite] using hc)
        (fun a w ha => by simpa [callEntryStateHOLFinite, s2, s1, setVarHOLFinite] using hm a w ha)
        (by simpa [callEntryStateHOLFinite] using hcl)
        (by simp [callEntryStateHOLFinite, s2, s1, setVarHOLFinite]; omega)
      obtain ⟨a1, a2, a3, a4⟩ := post
      exact ⟨st, ev, by simpa [callEntryStateHOLFinite, s2, s1, setVarHOLFinite] using a1,
        by simpa [callEntryStateHOLFinite, s2, s1, setVarHOLFinite] using a2,
        by simpa [callEntryStateHOLFinite, s2, s1, setVarHOLFinite] using a3,
        by simpa [callEntryStateHOLFinite, s2, s1, setVarHOLFinite] using a4⟩)
  let s3 := setKvarHOLFinite .local nR (.val (.word (bit (ConLeche.levelHasParam u)))) { st with locals := s2.locals }
  have lt3 : s3.locals.lookup nT = some (.val (.word tg)) := by
    simp only [s3, setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dRT)]; exact lt2
  have lr3 : s3.locals.lookup nR = some (.val (.word (bit (ConLeche.levelHasParam u)))) := by
    simp [s3, setKvarHOLFinite]
  have lu3 : s3.locals.lookup nU = some (.val (.word p)) := by
    simp only [s3, setKvarHOLFinite]; rw [lookup_setVar_other _ _ dUR]; exact lu2
  unfold lhpBody
  rw [hdec1, ite_word s1 _ _ _ 0 (by simp [evalHOLExact, vT, lt1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, n4]),
    ite_word s1 _ _ _ 0 (by simp [evalHOLExact, vT, lt1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, n0])]
  simp only [ne_eq, not_true_eq_false, ite_false]
  rw [hdec2]
  simp only [callR]
  rw [show setVarHOLFinite nR (.val (.word 0)) s1 = s2 from rfl]
  rw [seq_normal _ hcall, ite_word s3 _ _ _ 0 (by simp [evalHOLExact, vT, lt3,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL, n1])]
  simp only [ne_eq, not_true_eq_false, ite_false]
  cases hlu : ConLeche.levelHasParam u
  · -- u has no parameter: call on v
    have lr3' : s3.locals.lookup nR = some (.val (.word 0)) := by simpa [bit, hlu] using lr3
    rw [ite_word s3 _ _ _ 0 (by simp [evalHOLExact, vR, lr3', Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
    simp only [ne_eq, not_true_eq_false, ite_false]
    obtain ⟨st2, ⟨qc, qm, qd, qclk⟩, hcall2⟩ := call1 s3 nLhp nU nR lhpBody
      (.load .one (.op .add [vU, .const 24])) r (bit (ConLeche.levelHasParam v))
      (fun st2 => st2.code = s.code ∧ st2.memory = s.memory ∧ st2.memaddrs = s.memaddrs ∧
        st.clock - 1 ≤ st2.clock + cost v)
      (by simpa [s3, setKvarHOLFinite, setVarHOLFinite, pc] using hc)
      (by rw [eval_load_word s3 _ (p + 24) (by simp [evalHOLExact, evalListHOLExact, vU, lu3, wordOpHOL, wordOp,
        valueIsWord, valueWord]) (by simpa [s3, setKvarHOLFinite, setVarHOLFinite, pd] using d3)]
          simp only [s3, setKvarHOLFinite, setVarHOLFinite]; rw [pm, m3])
      (by simp [s3, setKvarHOLFinite, setVarHOLFinite]; omega)
      ⟨_, lr3⟩
      (fun callee hcl => by
        obtain ⟨st2, ev, post⟩ := ihv (callEntryStateHOLFinite s3 callee)
          (by simpa [callEntryStateHOLFinite, s3, setKvarHOLFinite, setVarHOLFinite, pc] using hc)
          (fun a w ha => by
            have := hm a w ha
            simpa [callEntryStateHOLFinite, s3, setKvarHOLFinite, setVarHOLFinite, pm, pd] using this)
          (by simpa [callEntryStateHOLFinite] using hcl)
          (by simp [callEntryStateHOLFinite, s3, setKvarHOLFinite, setVarHOLFinite]; omega)
        obtain ⟨a1, a2, a3, a4⟩ := post
        exact ⟨st2, ev, by simpa [callEntryStateHOLFinite, s3, setKvarHOLFinite, setVarHOLFinite, pc] using a1,
          by simpa [callEntryStateHOLFinite, s3, setKvarHOLFinite, setVarHOLFinite, pm] using a2,
          by simpa [callEntryStateHOLFinite, s3, setKvarHOLFinite, setVarHOLFinite, pd] using a3,
          by simpa [callEntryStateHOLFinite, s3, setKvarHOLFinite, setVarHOLFinite] using a4⟩)
    let s4 := setKvarHOLFinite .local nR (.val (.word (bit (ConLeche.levelHasParam v)))) { st2 with locals := s3.locals }
    have lr4 : s4.locals.lookup nR = some (.val (.word (bit (ConLeche.levelHasParam v)))) := by
      simp [s4, setKvarHOLFinite]
    rw [seq_normal _ hcall2]
    have eret : evaluateHOLFiniteState s4 (.return vR) =
        (some (.returned (.val (.word (bit (ConLeche.levelHasParam v))))), emptyLocalsHOLFinite s4) := by
      rw [evaluateHOLFiniteState_eq_evaluate_def]; simp [evalHOLExact, vR, lr4, shapeOfHOLExact]
    rw [eret]
    simp only [Bool.false_or]
    refine ⟨_, rfl, ?_⟩
    refine ⟨by simp [s4, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, qc],
      by simp [s4, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, qm],
      by simp [s4, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, qd], ?_⟩
    simp [s4, s3, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite] at qclk ⊢
    omega
  · -- u has a parameter: return 1
    have lr3' : s3.locals.lookup nR = some (.val (.word 1)) := by simpa [bit, hlu] using lr3
    rw [ite_word s3 _ _ _ 1 (by simp [evalHOLExact, vR, lr3', Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
    rw [if_pos (by decide : (1 : BitVec 64) ≠ 0)]
    rw [evaluateHOLFiniteState_eq_evaluate_def]
    simp only [Bool.true_or]
    refine ⟨_, Prod.ext (by simp [evalHOLExact, shapeOfHOLExact, bit]) rfl, ?_⟩
    refine ⟨by simp [s3, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, evalHOLExact, shapeOfHOLExact, pc],
      by simp [s3, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, evalHOLExact, shapeOfHOLExact, pm],
      by simp [s3, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, evalHOLExact, shapeOfHOLExact, pd], ?_⟩
    simp [s3, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, evalHOLExact, shapeOfHOLExact]
    omega

theorem lhp_spec {σ : Type} (h : Heap) {p : BitVec 64} {lv : ConLeche.Level} (hl : LevelAt h p lv) :
    ∀ s : PanSemStateFiniteExact 64 σ,
      s.code.lookup nLhp = some ([(nU, .one)], lhpBody, .one) → InMem s h →
      s.locals.lookup nU = some (.val (.word p)) → cost lv ≤ s.clock →
      ∃ st, evaluateHOLFiniteState s lhpBody = (some (.returned (.val (.word (bit (ConLeche.levelHasParam lv))))), st) ∧
        Post s st (cost lv) := by
  induction hl with
  | zero hp h0 h1 =>
    intro s hc hm hu hck
    obtain ⟨d0, m0⟩ := hm _ _ h0
    obtain ⟨L, hdec⟩ := dec_word' s nT (.load .one vU) 0 _ (by
      rw [eval_load_word s _ _ (by simp [evalHOLExact, vU, hu]) d0, m0])
    let s1 := setVarHOLFinite nT (.val (.word 0)) s
    have lt : s1.locals.lookup nT = some (.val (.word 0)) := by simp [s1]
    unfold lhpBody
    rw [hdec, ite_word s1 _ _ _ 0 (by simp [evalHOLExact, vT, lt, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]),
      ite_word s1 _ _ _ 1 (by simp [evalHOLExact, vT, lt, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
    rw [evaluateHOLFiniteState_eq_evaluate_def]
    refine ⟨_, by simp [evalHOLExact, shapeOfHOLExact, bit, ConLeche.levelHasParam] <;> rfl, ?_⟩
    simp [Post, s1, setVarHOLFinite, emptyLocalsHOLFinite, evalHOLExact, shapeOfHOLExact, cost]
  | param hp h0 h1 h2 hn =>
    intro s hc hm hu hck
    obtain ⟨d0, m0⟩ := hm _ _ h0
    obtain ⟨L, hdec⟩ := dec_word' s nT (.load .one vU) 4 _ (by
      rw [eval_load_word s _ _ (by simp [evalHOLExact, vU, hu]) d0, m0])
    let s1 := setVarHOLFinite nT (.val (.word 4)) s
    have lt : s1.locals.lookup nT = some (.val (.word 4)) := by simp [s1]
    unfold lhpBody
    rw [hdec, ite_word s1 _ _ _ 1 (by simp [evalHOLExact, vT, lt, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
    rw [evaluateHOLFiniteState_eq_evaluate_def]
    refine ⟨_, by simp [evalHOLExact, shapeOfHOLExact, bit, ConLeche.levelHasParam] <;> rfl, ?_⟩
    simp [Post, s1, setVarHOLFinite, emptyLocalsHOLFinite, evalHOLExact, shapeOfHOLExact, cost]
  | @succ p q u hp h0 h1 h2 hu ih =>
    intro s hc hm hpu hck
    obtain ⟨d0, m0⟩ := hm _ _ h0
    obtain ⟨d2, m2⟩ := hm _ _ h2
    simp only [cost] at hck
    obtain ⟨L1, hdec1⟩ := dec_word' s nT (.load .one vU) 1 _ (by
      rw [eval_load_word s _ _ (by simp [evalHOLExact, vU, hpu]) d0, m0])
    let s1 := setVarHOLFinite nT (.val (.word 1)) s
    have lt1 : s1.locals.lookup nT = some (.val (.word 1)) := by simp [s1]
    obtain ⟨L2, hdec2⟩ := dec_word' s1 nR (.const 0) 0 _ (by simp [evalHOLExact])
    let s2 := setVarHOLFinite nR (.val (.word 0)) s1
    have dRT : nR ≠ nT := by decide
    have dUR : nU ≠ nR := by decide
    have dUT : nU ≠ nT := by decide
    have lt2 : s2.locals.lookup nT = some (.val (.word 1)) := by
      simp only [s2]; rw [lookup_setVar_other _ _ (Ne.symm dRT)]; exact lt1
    have lu2 : s2.locals.lookup nU = some (.val (.word p)) := by
      simp only [s2, s1]; rw [lookup_setVar_other _ _ dUR, lookup_setVar_other _ _ dUT]; exact hpu
    obtain ⟨st, ⟨pc, pm, pd, pclk⟩, hcall⟩ := call1 s2 nLhp nU nR lhpBody (.load .one (.op .add [vU, .const 16])) q
      (bit (ConLeche.levelHasParam u))
      (fun st => st.code = s.code ∧ st.memory = s.memory ∧ st.memaddrs = s.memaddrs ∧ s.clock - 1 ≤ st.clock + cost u)
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
    let s3 := setKvarHOLFinite .local nR (.val (.word (bit (ConLeche.levelHasParam u)))) { st with locals := s2.locals }
    have lt3 : s3.locals.lookup nT = some (.val (.word 1)) := by
      simp only [s3, setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dRT)]; exact lt2
    have lr3 : s3.locals.lookup nR = some (.val (.word (bit (ConLeche.levelHasParam u)))) := by
      simp [s3, setKvarHOLFinite]
    unfold lhpBody
    rw [hdec1, ite_word s1 _ _ _ 0 (by simp [evalHOLExact, vT, lt1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]),
      ite_word s1 _ _ _ 0 (by simp [evalHOLExact, vT, lt1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
    simp only [ne_eq, not_true_eq_false, ite_false]
    rw [hdec2]
    simp only [callR]
    rw [show setVarHOLFinite nR (.val (.word 0)) s1 = s2 from rfl]
    rw [seq_normal _ hcall, ite_word s3 _ _ _ 1 (by simp [evalHOLExact, vT, lt3,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
    rw [if_pos (by decide : (1 : BitVec 64) ≠ 0)]
    have eret : evaluateHOLFiniteState s3 (.return vR) =
        (some (.returned (.val (.word (bit (ConLeche.levelHasParam u))))), emptyLocalsHOLFinite s3) := by
      rw [evaluateHOLFiniteState_eq_evaluate_def]; simp [evalHOLExact, vR, lr3, shapeOfHOLExact]
    rw [eret]
    have e : ConLeche.levelHasParam (.succ u) = ConLeche.levelHasParam u := by simp [ConLeche.levelHasParam]
    rw [e]
    refine ⟨_, rfl, ?_⟩
    refine ⟨by simp [s3, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, pc],
      by simp [s3, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, pm],
      by simp [s3, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, pd], ?_⟩
    simp [s3, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, cost]
    omega
  | @max p q r u v hp h0 h1 h2 h3 hu hv ihu ihv =>
    intro s hc hm hpu hck
    simp only [cost] at hck ⊢
    have e : ConLeche.levelHasParam (.max u v) = (ConLeche.levelHasParam u || ConLeche.levelHasParam v) := by
      simp [ConLeche.levelHasParam]
    rw [e]
    exact lhp_bin h p q r 2 u v (by decide) (by decide) (by decide) h0 h2 h3 ihu ihv s hc hm hpu hck
  | @imax p q r u v hp h0 h1 h2 h3 hu hv ihu ihv =>
    intro s hc hm hpu hck
    simp only [cost] at hck ⊢
    have e : ConLeche.levelHasParam (.imax u v) = (ConLeche.levelHasParam u || ConLeche.levelHasParam v) := by
      simp [ConLeche.levelHasParam]
    rw [e]
    exact lhp_bin h p q r 3 u v (by decide) (by decide) (by decide) h0 h2 h3 ihu ihv s hc hm hpu hck

end ConPanqueque.LevelFns
