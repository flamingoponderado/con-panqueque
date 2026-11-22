import ConPanqueque.ConsProbe
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.ConsModel ConPanqueque.ConsLoop ConPanqueque.ConsIns ConPanqueque.ConsTbl
open ConPanqueque.ConsIntern ConPanqueque.ConsProbe
open ConRon.Arena

/-!
# Selecting a tier

A tier's table geometry lives in a six-word descriptor at `G`:
`S, R, n-1, C, cap, D`. `withGeo g tier body` loads it (through the pointer
local `g`) into the table locals that `internTier`/`probeTier` read, sets the
tier word, and runs `body`. `withGeo_lift` carries a property of the body's
run that survives a `dec` (the per-tier results do) out to the wrapper.
-/

namespace ConPanqueque.ConsGeo

/-- The `k`-th descriptor word. -/
def ldw (g : MlS) (k : Nat) : ExpHOL 64 := .load .one (.op .add [ConsIntern.vv g, .const (BitVec.ofNat 64 (8 * k))])

def withGeo (g : MlS) (tier : BitVec 64) (body : ProgHOL 64) : ProgHOL 64 :=
  .dec lS .one (ldw g 0) (.dec lR .one (ldw g 1) (.dec lM .one (ldw g 2) (.dec lC0 .one (ldw g 3)
   (.dec lCap .one (ldw g 4) (.dec lD .one (ldw g 5) (.dec lTier .one (.const tier) body))))))

/-- The descriptor's words. -/
def descVals (S R : BitVec 64) (n : Nat) (C : BitVec 64) (cap : Nat) (D : BitVec 64) : List (BitVec 64) :=
  [S, R, BitVec.ofNat 64 (n - 1), C, BitVec.ofNat 64 cap, D]

def Desc {σ : Type} (t : PanSemStateFiniteExact 64 σ) (G S R : BitVec 64) (n : Nat) (C : BitVec 64) (cap : Nat)
    (D : BitVec 64) : Prop :=
  ∀ k (hk : k < 6), t.memaddrs (G + BitVec.ofNat 64 (8 * k)) ∧
    t.memory (G + BitVec.ofNat 64 (8 * k)) = .word ((descVals S R n C cap D)[k]'(by simp [descVals]; omega))

theorem eval_ldw {σ : Type} (s : PanSemStateFiniteExact 64 σ) (g : MlS) (G : BitVec 64) (k : Nat)
    (hg : s.locals.lookup g = some (.val (.word G))) (hd : s.memaddrs (G + BitVec.ofNat 64 (8 * k))) :
    @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (ldw g k) =
      some (.val (s.memory (G + BitVec.ofNat 64 (8 * k)))) :=
  eval_load_word s _ _ (by simp [ConsIntern.vv, evalHOLExact, evalListHOLExact, hg, wordOpHOL, wordOp, valueIsWord,
    valueWord]) hd

/-- The state the body runs in. -/
def geoState {σ : Type} (t : PanSemStateFiniteExact 64 σ) (S R : BitVec 64) (n : Nat) (C : BitVec 64) (cap : Nat)
    (D tier : BitVec 64) : PanSemStateFiniteExact 64 σ :=
  setVarHOLFinite lTier (.val (.word tier)) (setVarHOLFinite lD (.val (.word D))
    (setVarHOLFinite lCap (.val (.word (BitVec.ofNat 64 cap))) (setVarHOLFinite lC0 (.val (.word C))
      (setVarHOLFinite lM (.val (.word (BitVec.ofNat 64 (n - 1)))) (setVarHOLFinite lR (.val (.word R))
        (setVarHOLFinite lS (.val (.word S)) t))))))

theorem withGeo_lift {σ : Type}
    (Q : PanSemStateFiniteExact 64 σ → Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ → Prop)
    (hQ : ∀ s x (v : BitVec 64) r, Q (setVarHOLFinite x (.val (.word v)) s) r →
      Q s (r.1, { r.2 with locals := HolFiniteMapExact.resVarEq r.2.locals (x, s.locals.lookup x) }))
    (t : PanSemStateFiniteExact 64 σ) (g : MlS) (G S R : BitVec 64) (n : Nat) (C : BitVec 64) (cap : Nat)
    (D tier : BitVec 64) (body : ProgHOL 64)
    (hg : t.locals.lookup g = some (.val (.word G)))
    (hgn : g ≠ lS ∧ g ≠ lR ∧ g ≠ lM ∧ g ≠ lC0 ∧ g ≠ lCap)
    (hdesc : Desc t G S R n C cap D)
    (hb : Q (geoState t S R n C cap D tier) (evaluateHOLFiniteState (geoState t S R n C cap D tier) body)) :
    Q t (evaluateHOLFiniteState t (withGeo g tier body)) := by
  obtain ⟨n1, n2, n3, n4, n5⟩ := hgn
  have ev : ∀ (s : PanSemStateFiniteExact 64 σ) (k : Nat) (hk : k < 6), s.locals.lookup g = some (.val (.word G)) →
      s.memory = t.memory → s.memaddrs = t.memaddrs →
      @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) (ldw g k) =
        some (.val (.word ((descVals S R n C cap D)[k]'(by simp only [descVals, List.length_cons, List.length_nil]; omega)))) := by
    intro s k hk h1 h2 h3
    rw [eval_ldw s g G k h1 (by rw [h3]; exact (hdesc k hk).1), h2, (hdesc k hk).2]
  unfold withGeo
  rw [dec_word_eq t lS _ S _ (by rw [ev t 0 (by decide) hg rfl rfl]; rfl)]; apply hQ
  let t1 := setVarHOLFinite lS (.val (.word S)) t
  have g1 : t1.locals.lookup g = some (.val (.word G)) := by rw [lookup_setVar_other _ _ n1]; exact hg
  rw [dec_word_eq t1 lR _ R _ (by rw [ev t1 1 (by decide) g1 rfl rfl]; rfl)]; apply hQ
  let t2 := setVarHOLFinite lR (.val (.word R)) t1
  have g2 : t2.locals.lookup g = some (.val (.word G)) := by rw [lookup_setVar_other _ _ n2]; exact g1
  rw [dec_word_eq t2 lM _ (BitVec.ofNat 64 (n - 1)) _ (by rw [ev t2 2 (by decide) g2 rfl rfl]; rfl)]; apply hQ
  let t3 := setVarHOLFinite lM (.val (.word (BitVec.ofNat 64 (n - 1)))) t2
  have g3 : t3.locals.lookup g = some (.val (.word G)) := by rw [lookup_setVar_other _ _ n3]; exact g2
  rw [dec_word_eq t3 lC0 _ C _ (by rw [ev t3 3 (by decide) g3 rfl rfl]; rfl)]; apply hQ
  let t4 := setVarHOLFinite lC0 (.val (.word C)) t3
  have g4 : t4.locals.lookup g = some (.val (.word G)) := by rw [lookup_setVar_other _ _ n4]; exact g3
  rw [dec_word_eq t4 lCap _ (BitVec.ofNat 64 cap) _ (by rw [ev t4 4 (by decide) g4 rfl rfl]; rfl)]; apply hQ
  let t5 := setVarHOLFinite lCap (.val (.word (BitVec.ofNat 64 cap))) t4
  have g5 : t5.locals.lookup g = some (.val (.word G)) := by rw [lookup_setVar_other _ _ n5]; exact g4
  rw [dec_word_eq t5 lD _ D _ (by rw [ev t5 5 (by decide) g5 rfl rfl]; rfl)]; apply hQ
  let t6 := setVarHOLFinite lD (.val (.word D)) t5
  rw [dec_word_eq t6 lTier (.const tier) tier _ (by simp [evalHOLExact])]; apply hQ
  exact hb

/-- The scratch-child test as a word: nonzero iff a child names the scratch tier. -/
def skE : ExpHOL 64 :=
  .op .or [.shift .lsr (ConsIntern.vv lKf) (.const 31), .shift .lsr (ConsIntern.vv lKa) (.const 31)]

theorem shr31_zero (w : UInt32) : w.toUInt64.toBitVec >>> 31 = 0 ↔ (w.toNat / 2147483648 = 0) := by
  constructor
  · intro h; have := congrArg BitVec.toNat h
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow] at this; omega
  · intro h; apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega

theorem tier_zero (i : EIdx) : i.isPersistent = true ↔ i.word.toNat / 2147483648 = 0 := by
  simp only [Idx.isPersistent, Idx.tier, beq_iff_eq]
  constructor
  · intro h; have := congrArg UInt32.toNat h; simpa [UInt32.toNat_div] using this
  · intro h; apply UInt32.toNat_inj.mp; simpa [UInt32.toNat_div] using h

theorem sk_word (f a : EIdx) :
    (f.word.toUInt64.toBitVec >>> 31 ||| a.word.toUInt64.toBitVec >>> 31 = 0) ↔
      EStore.eViewHasScratchChild (.app f a) = false := by
  rw [show (0 : BitVec 64) = 0#64 from rfl, BitVec.or_eq_zero_iff, ← show (0 : BitVec 64) = 0#64 from rfl, shr31_zero, shr31_zero]
  simp only [EStore.eViewHasScratchChild]
  by_cases hf : f.isPersistent = true
  · rw [if_pos hf, Bool.not_eq_false', tier_zero]; rw [tier_zero] at hf; simp [hf]
  · rw [if_neg hf]; rw [tier_zero] at hf; simp [hf]

end ConPanqueque.ConsGeo
