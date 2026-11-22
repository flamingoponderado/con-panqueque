import ConPanqueque.Arena
import ConPanqueque.Hash
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Hash ConPanqueque.Logic ConPanqueque.Alloc

def vp : ExpHOL 64 := .var .local (ofString "p")
def vu : ExpHOL 64 := .var .local (ofString "u")
def plus (e : ExpHOL 64) (k : BitVec 64) : ExpHOL 64 := .op .add [e, .const k]

/-- The stores of the `Level.succ` constructor, then `return p`. -/
def succStores : ProgHOL 64 :=
  .seq (.store vp (.const 1))
    (.seq (.store (plus vp 8) (mixExp (.const 3) (.load .one (plus vu 8))))
      (.seq (.store (plus vp 16) vu) (.return vp)))

/-- Address facts for a 24-byte block at the heap pointer. -/
theorem block24 {σ : Type} {s : PanSemStateFiniteExact 64 σ} {h : Heap} {p0 : BitVec 64}
    (hi : ArenaInv s h p0) (hfit : ¬ s.topAddr - p0 < 24) (hnz : p0 ≠ 0) :
    (s.memaddrs p0 ∧ s.memaddrs (p0 + 8) ∧ s.memaddrs (p0 + 16)) ∧
    (h p0 = none ∧ h (p0 + 8) = none ∧ h (p0 + 16) = none) ∧
    (p0 ≠ p0 + 8 ∧ p0 ≠ p0 + 16 ∧ p0 + 8 ≠ p0 + 16) ∧ Free s (p0 + 24) ∧ p0 ≠ 0 := by
  have hf := hi.2.1
  obtain ⟨hsum, hdom, hfree⟩ := alloc_fresh s p0 24 hf hfit
  have hb : p0.toNat + 24 ≤ s.topAddr.toNat := by simpa using hsum
  have ht : s.topAddr.toNat < 2 ^ 64 := s.topAddr.isLt
  refine ⟨⟨hdom p0 (by bv_omega) (by bv_omega), hdom (p0 + 8) (by bv_omega) (by bv_omega),
      hdom (p0 + 16) (by bv_omega) (by bv_omega)⟩,
    ⟨arena_fresh (a := p0) hi (by bv_omega), arena_fresh (a := p0 + 8) hi (by bv_omega),
      arena_fresh (a := p0 + 16) hi (by bv_omega)⟩,
    ⟨by bv_omega, by bv_omega, by bv_omega⟩, hfree, hnz⟩

theorem levelSucc_hash (ra : RuntimeAssumptions) (u : ConLeche.Level) :
    (ConLeche.Level.succ u).hashData = leanMixHash 3 u.hashData := by
  simp [ConLeche.Level.hashData, ra.mixHash]

/-- The stores of the `Level.succ` constructor build the node and extend the arena. -/
theorem succStores_spec {σ : Type} (ra : RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ)
    (h : Heap) (p0 q : BitVec 64) (u : ConLeche.Level)
    (hp : t.locals.lookup (ofString "p") = some (.val (.word p0)))
    (hu : t.locals.lookup (ofString "u") = some (.val (.word q)))
    (hi : ArenaInv t h p0) (hfit : ¬ t.topAddr - p0 < 24) (hnz : p0 ≠ 0) (hl : LevelAt h q u) :
    ∃ t' h', evaluateHOLFiniteState t succStores = (some (.returned (.val (.word p0))), t') ∧
      ArenaInv t' h' (p0 + 24) ∧ Sub h h' ∧ LevelAt h' p0 (.succ u) := by
  obtain ⟨⟨d0, d8, d16⟩, ⟨f0, f8, f16⟩, ⟨n08, n016, n816⟩, hfree, _⟩ := block24 hi hfit hnz
  obtain ⟨hsum, -, -⟩ := alloc_fresh t p0 24 hi.2.1 hfit
  have hb : p0.toNat + 24 ≤ t.topAddr.toNat := by simpa using hsum
  have ht : t.topAddr.toNat < 2 ^ 64 := t.topAddr.isLt
  obtain ⟨_, hq8⟩ := levelAt_hash hl
  obtain ⟨dq8, mq8⟩ := hi.1 _ _ hq8
  have hqlt : q + 8 < p0 := hi.2.2 _ _ hq8
  have nq0 : q + 8 ≠ p0 := by bv_omega
  -- the three stores
  let w1 : HolWordLab 64 := .word 1
  let w2 : HolWordLab 64 := .word (ConLeche.Level.succ u).hashData.toBitVec
  let w3 : HolWordLab 64 := .word q
  let t1 := { t with memory := fun c => if c = p0 then w1 else t.memory c }
  let t2 := { t1 with memory := fun c => if c = p0 + 8 then w2 else t1.memory c }
  let t3 := { t2 with memory := fun c => if c = p0 + 16 then w3 else t2.memory c }
  have e1 : evaluateHOLFiniteState t (.store vp (.const 1)) = (none, t1) :=
    store_word t _ _ p0 1 (by simp [evalHOLExact, vp, hp]) (by simp [evalHOLExact]) d0
  have e2 : evaluateHOLFiniteState t1 (.store (plus vp 8) (mixExp (.const 3) (.load .one (plus vu 8)))) =
      (none, t2) := by
    apply store_word t1 _ _ (p0 + 8) _ (by simp [evalHOLExact, evalListHOLExact, plus, vp, hp, t1,
      wordOpHOL, wordOp, valueIsWord, valueWord]) _ (by simpa [t1] using d8)
    rw [levelSucc_hash ra]
    apply eval_mixExp t1 _ _ 3 u.hashData (by simp [evalHOLExact])
    rw [eval_load_word t1 _ (q + 8) (by simp [evalHOLExact, evalListHOLExact, plus, vu, hu, t1,
      wordOpHOL, wordOp, valueIsWord, valueWord]) (by simpa [t1] using dq8)]
    simp only [t1]
    split
    · exact absurd ‹_› nq0
    · rw [mq8]
  have e3 : evaluateHOLFiniteState t2 (.store (plus vp 16) vu) = (none, t3) :=
    store_word t2 _ _ (p0 + 16) q (by simp [evalHOLExact, evalListHOLExact, plus, vp, hp, t2, t1,
      wordOpHOL, wordOp, valueIsWord, valueWord]) (by simp [evalHOLExact, vu, hu, t2, t1])
      (by simpa [t2, t1] using d16)
  -- the arena after the stores
  let h1 := ext h p0 w1
  let h2 := ext h1 (p0 + 8) w2
  let h3 := ext h2 (p0 + 16) w3
  have g8 : h1 (p0 + 8) = none := by
    simp only [h1, ext]; split
    · exact absurd ‹_› (Ne.symm n08)
    · exact f8
  have g16 : h2 (p0 + 16) = none := by
    simp only [h2, h1, ext]; split
    · exact absurd ‹_› (Ne.symm n816)
    · split
      · exact absurd ‹_› (Ne.symm n016)
      · exact f16
  have m1 : InMem t1 h1 := inMem_store w1 hi.1 f0 d0
  have m2 : InMem t2 h2 := inMem_store w2 m1 g8 (by simpa [t1] using d8)
  have m3 : InMem t3 h3 := inMem_store w3 m2 g16 (by simpa [t2, t1] using d16)
  have s13 : Sub h h3 := fun a w ha => sub_ext w3 g16 a w (sub_ext w2 g8 a w (sub_ext w1 f0 a w ha))
  refine ⟨emptyLocalsHOLFinite t3, h3, ?_, ⟨?_, ?_, ?_⟩, s13, ?_⟩
  · unfold succStores
    rw [seq_normal _ e1, seq_normal _ e2, seq_normal _ e3, evaluateHOLFiniteState_eq_evaluate_def]
    simp [evalHOLExact, vp, t3, t2, t1, hp, shapeOfHOLExact]
  · intro a w ha; exact m3 a w (by simpa [emptyLocalsHOLFinite] using ha) |>.imp id (by simp [emptyLocalsHOLFinite])
  · simp only [Free] at hfree ⊢; simpa [emptyLocalsHOLFinite, t3, t2, t1] using hfree
  · intro a w ha
    simp only [h3, h2, h1, ext] at ha
    split at ha
    · subst_vars; bv_omega
    · split at ha
      · subst_vars; bv_omega
      · split at ha
        · subst_vars; bv_omega
        · have := hi.2.2 a w ha; bv_omega
  · exact .succ hnz (by simp [h3, h2, h1, ext, n08, n016, w1])
      (by simp [h3, h2, h1, ext, n816, w2]) (by simp [h3, ext, w3]) (levelAt_mono s13 hl)
