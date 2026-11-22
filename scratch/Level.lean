import ConPanqueque.Rep
open Flapjack Flapjack.PanSemStateFiniteExact ConPanqueque.Sep ConPanqueque.Rep

namespace ConPanqueque.Rep

/-- A level in the arena: always a block `[tag, hashData, children…]`. -/
inductive LevelAt (h : Heap) : BitVec 64 → ConLeche.Level → Prop
  | zero {p : BitVec 64} (hp : p ≠ 0) (h0 : h p = some (.word 0))
      (h1 : h (p + 8) = some (.word ConLeche.Level.zero.hashData.toBitVec)) : LevelAt h p .zero
  | succ {p q : BitVec 64} {u : ConLeche.Level} (hp : p ≠ 0) (h0 : h p = some (.word 1))
      (h1 : h (p + 8) = some (.word (ConLeche.Level.succ u).hashData.toBitVec))
      (h2 : h (p + 16) = some (.word q)) (hu : LevelAt h q u) : LevelAt h p (.succ u)
  | max {p q r : BitVec 64} {u v : ConLeche.Level} (hp : p ≠ 0) (h0 : h p = some (.word 2))
      (h1 : h (p + 8) = some (.word (ConLeche.Level.max u v).hashData.toBitVec))
      (h2 : h (p + 16) = some (.word q)) (h3 : h (p + 24) = some (.word r))
      (hu : LevelAt h q u) (hv : LevelAt h r v) : LevelAt h p (.max u v)
  | imax {p q r : BitVec 64} {u v : ConLeche.Level} (hp : p ≠ 0) (h0 : h p = some (.word 3))
      (h1 : h (p + 8) = some (.word (ConLeche.Level.imax u v).hashData.toBitVec))
      (h2 : h (p + 16) = some (.word q)) (h3 : h (p + 24) = some (.word r))
      (hu : LevelAt h q u) (hv : LevelAt h r v) : LevelAt h p (.imax u v)
  | param {p q : BitVec 64} {n : ConLeche.Name} (hp : p ≠ 0) (h0 : h p = some (.word 4))
      (h1 : h (p + 8) = some (.word (ConLeche.Level.param n).hashData.toBitVec))
      (h2 : h (p + 16) = some (.word q)) (hn : NameAt h q n) : LevelAt h p (.param n)

theorem levelAt_mono {h h' : Heap} (hs : Sub h h') {p : BitVec 64} {u : ConLeche.Level}
    (hu : LevelAt h p u) : LevelAt h' p u := by
  induction hu with
  | zero hp h0 h1 => exact .zero hp (hs _ _ h0) (hs _ _ h1)
  | succ hp h0 h1 h2 _ ih => exact .succ hp (hs _ _ h0) (hs _ _ h1) (hs _ _ h2) ih
  | max hp h0 h1 h2 h3 _ _ ih1 ih2 => exact .max hp (hs _ _ h0) (hs _ _ h1) (hs _ _ h2) (hs _ _ h3) ih1 ih2
  | imax hp h0 h1 h2 h3 _ _ ih1 ih2 => exact .imax hp (hs _ _ h0) (hs _ _ h1) (hs _ _ h2) (hs _ _ h3) ih1 ih2
  | param hp h0 h1 h2 hn => exact .param hp (hs _ _ h0) (hs _ _ h1) (hs _ _ h2) (nameAt_mono hs hn)

theorem levelAt_hash {h : Heap} {p : BitVec 64} {u : ConLeche.Level} (hu : LevelAt h p u) :
    p ≠ 0 ∧ h (p + 8) = some (.word u.hashData.toBitVec) := by
  cases hu with
  | zero hp _ h1 => exact ⟨hp, h1⟩
  | succ hp _ h1 => exact ⟨hp, h1⟩
  | max hp _ h1 => exact ⟨hp, h1⟩
  | imax hp _ h1 => exact ⟨hp, h1⟩
  | param hp _ h1 => exact ⟨hp, h1⟩

open Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString ConPanqueque.Logic in
/-- con-leche's `Level.hashData` in Pancake: the cached hash at offset 8. -/
def levelHashBody : ProgHOL 64 :=
  .return (.load .one (.op .add [.var .local (ofString "u"), .const 8]))

open Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString ConPanqueque.Logic in
theorem levelHashBody_spec {σ : Type} (s : PanSemStateFiniteExact 64 σ) (p : BitVec 64) (u : ConLeche.Level)
    (hu : s.locals.lookup (ofString "u") = some (.val (.word p))) {h : Heap} (hm : InMem s h)
    (hl : LevelAt h p u) :
    (evaluateHOLFiniteState s levelHashBody).1 = some (.returned (.val (.word u.hashData.toBitVec))) := by
  obtain ⟨_, h8⟩ := levelAt_hash hl
  obtain ⟨hd, hv⟩ := hm _ _ h8
  unfold levelHashBody
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  simp only
  rw [eval_load_word s _ (p + 8) (by simp [evalHOLExact, evalListHOLExact, hu, wordOpHOL, wordOp,
    valueIsWord, valueWord]) hd, hv]
  simp [shapeOfHOLExact]

end ConPanqueque.Rep
