import ConPanqueque.Rep
open Flapjack Flapjack.PanSemStateFiniteExact ConPanqueque.Sep ConPanqueque.Rep

namespace ConPanqueque.Rep

/-- A list of levels in the arena: `0`, or cells `[head, next]`. -/
inductive LevelsAt (h : Heap) : BitVec 64 → List ConLeche.Level → Prop
  | nil : LevelsAt h 0 []
  | cons {p q r : BitVec 64} {u : ConLeche.Level} {us : List ConLeche.Level} (hp : p ≠ 0)
      (h0 : h p = some (.word q)) (h1 : h (p + 8) = some (.word r))
      (hu : LevelAt h q u) (hus : LevelsAt h r us) : LevelsAt h p (u :: us)

/-- A literal: `[0, nat]` or `[1, string]`. -/
inductive LitAt (h : Heap) : BitVec 64 → ConLeche.Literal → Prop
  | natVal {p v : BitVec 64} {n : Nat} (hp : p ≠ 0) (h0 : h p = some (.word 0))
      (h1 : h (p + 8) = some (.word v)) (hn : NatAt h v n) : LitAt h p (.natVal n)
  | strVal {p v : BitVec 64} {s : String} (hp : p ≠ 0) (h0 : h p = some (.word 1))
      (h1 : h (p + 8) = some (.word v)) (hs : StrAt h v s) : LitAt h p (.strVal s)

/-- An expression in the arena: a block `[tag, data, fields…]`, tag = constructor index. -/
inductive ExprAt (h : Heap) : BitVec 64 → ConLeche.Expr → Prop
  | bvar {p v : BitVec 64} {i : Nat} (hp : p ≠ 0) (h0 : h p = some (.word 0))
      (hd : h (p + 8) = some (.word (ConLeche.Expr.bvar i).data.toBitVec))
      (h2 : h (p + 16) = some (.word v)) (hi : NatAt h v i) : ExprAt h p (.bvar i)
  | fvar {p v q : BitVec 64} {i : Nat} {ty : ConLeche.Expr} (hp : p ≠ 0) (h0 : h p = some (.word 1))
      (hd : h (p + 8) = some (.word (ConLeche.Expr.fvar i ty).data.toBitVec))
      (h2 : h (p + 16) = some (.word v)) (h3 : h (p + 24) = some (.word q))
      (hi : NatAt h v i) (hty : ExprAt h q ty) : ExprAt h p (.fvar i ty)
  | sort {p q : BitVec 64} {u : ConLeche.Level} (hp : p ≠ 0) (h0 : h p = some (.word 2))
      (hd : h (p + 8) = some (.word (ConLeche.Expr.sort u).data.toBitVec))
      (h2 : h (p + 16) = some (.word q)) (hu : LevelAt h q u) : ExprAt h p (.sort u)
  | const {p q r : BitVec 64} {n : ConLeche.Name} {us : List ConLeche.Level} (hp : p ≠ 0)
      (h0 : h p = some (.word 3)) (hd : h (p + 8) = some (.word (ConLeche.Expr.const n us).data.toBitVec))
      (h2 : h (p + 16) = some (.word q)) (h3 : h (p + 24) = some (.word r))
      (hn : NameAt h q n) (hus : LevelsAt h r us) : ExprAt h p (.const n us)
  | app {p q r : BitVec 64} {f a : ConLeche.Expr} (hp : p ≠ 0) (h0 : h p = some (.word 4))
      (hd : h (p + 8) = some (.word (ConLeche.Expr.app f a).data.toBitVec))
      (h2 : h (p + 16) = some (.word q)) (h3 : h (p + 24) = some (.word r))
      (hf : ExprAt h q f) (ha : ExprAt h r a) : ExprAt h p (.app f a)
  | lam {p q r : BitVec 64} {ty b : ConLeche.Expr} (hp : p ≠ 0) (h0 : h p = some (.word 5))
      (hd : h (p + 8) = some (.word (ConLeche.Expr.lam ty b).data.toBitVec))
      (h2 : h (p + 16) = some (.word q)) (h3 : h (p + 24) = some (.word r))
      (hty : ExprAt h q ty) (hb : ExprAt h r b) : ExprAt h p (.lam ty b)
  | forallE {p q r : BitVec 64} {ty b : ConLeche.Expr} (hp : p ≠ 0) (h0 : h p = some (.word 6))
      (hd : h (p + 8) = some (.word (ConLeche.Expr.forallE ty b).data.toBitVec))
      (h2 : h (p + 16) = some (.word q)) (h3 : h (p + 24) = some (.word r))
      (hty : ExprAt h q ty) (hb : ExprAt h r b) : ExprAt h p (.forallE ty b)
  | letE {p q r s : BitVec 64} {ty v b : ConLeche.Expr} (hp : p ≠ 0) (h0 : h p = some (.word 7))
      (hd : h (p + 8) = some (.word (ConLeche.Expr.letE ty v b).data.toBitVec))
      (h2 : h (p + 16) = some (.word q)) (h3 : h (p + 24) = some (.word r)) (h4 : h (p + 32) = some (.word s))
      (hty : ExprAt h q ty) (hv : ExprAt h r v) (hb : ExprAt h s b) : ExprAt h p (.letE ty v b)
  | lit {p q : BitVec 64} {l : ConLeche.Literal} (hp : p ≠ 0) (h0 : h p = some (.word 8))
      (hd : h (p + 8) = some (.word (ConLeche.Expr.lit l).data.toBitVec))
      (h2 : h (p + 16) = some (.word q)) (hl : LitAt h q l) : ExprAt h p (.lit l)
  | proj {p q v r : BitVec 64} {n : ConLeche.Name} {i : Nat} {e : ConLeche.Expr} (hp : p ≠ 0)
      (h0 : h p = some (.word 9)) (hd : h (p + 8) = some (.word (ConLeche.Expr.proj n i e).data.toBitVec))
      (h2 : h (p + 16) = some (.word q)) (h3 : h (p + 24) = some (.word v)) (h4 : h (p + 32) = some (.word r))
      (hn : NameAt h q n) (hi : NatAt h v i) (he : ExprAt h r e) : ExprAt h p (.proj n i e)

/-- Every expression node is a nonzero block with its data word at offset 8. -/
theorem exprAt_data {h : Heap} {p : BitVec 64} {e : ConLeche.Expr} (he : ExprAt h p e) :
    p ≠ 0 ∧ h (p + 8) = some (.word e.data.toBitVec) := by
  cases he <;> exact ⟨by assumption, by assumption⟩

theorem strAt_mono {h h' : Heap} (hs : Sub h h') {v : BitVec 64} {str : String} (ha : StrAt h v str) :
    StrAt h' v str := fun i hi => hs _ _ (ha i hi)

theorem levelsAt_mono {h h' : Heap} (hs : Sub h h') {p : BitVec 64} {us : List ConLeche.Level}
    (ha : LevelsAt h p us) : LevelsAt h' p us := by
  induction ha with
  | nil => exact .nil
  | cons hp h0 h1 hu _ ih => exact .cons hp (hs _ _ h0) (hs _ _ h1) (levelAt_mono hs hu) ih

theorem litAt_mono {h h' : Heap} (hs : Sub h h') {p : BitVec 64} {l : ConLeche.Literal}
    (ha : LitAt h p l) : LitAt h' p l := by
  cases ha with
  | natVal hp h0 h1 hn => exact .natVal hp (hs _ _ h0) (hs _ _ h1) hn
  | strVal hp h0 h1 hst => exact .strVal hp (hs _ _ h0) (hs _ _ h1) (strAt_mono hs hst)

theorem exprAt_mono {h h' : Heap} (hs : Sub h h') {p : BitVec 64} {e : ConLeche.Expr}
    (he : ExprAt h p e) : ExprAt h' p e := by
  induction he with
  | bvar hp h0 hd h2 hi => exact .bvar hp (hs _ _ h0) (hs _ _ hd) (hs _ _ h2) hi
  | fvar hp h0 hd h2 h3 hi _ ih => exact .fvar hp (hs _ _ h0) (hs _ _ hd) (hs _ _ h2) (hs _ _ h3) hi ih
  | sort hp h0 hd h2 hu => exact .sort hp (hs _ _ h0) (hs _ _ hd) (hs _ _ h2) (levelAt_mono hs hu)
  | const hp h0 hd h2 h3 hn hus =>
    exact .const hp (hs _ _ h0) (hs _ _ hd) (hs _ _ h2) (hs _ _ h3) (nameAt_mono hs hn) (levelsAt_mono hs hus)
  | app hp h0 hd h2 h3 _ _ ih1 ih2 => exact .app hp (hs _ _ h0) (hs _ _ hd) (hs _ _ h2) (hs _ _ h3) ih1 ih2
  | lam hp h0 hd h2 h3 _ _ ih1 ih2 => exact .lam hp (hs _ _ h0) (hs _ _ hd) (hs _ _ h2) (hs _ _ h3) ih1 ih2
  | forallE hp h0 hd h2 h3 _ _ ih1 ih2 =>
    exact .forallE hp (hs _ _ h0) (hs _ _ hd) (hs _ _ h2) (hs _ _ h3) ih1 ih2
  | letE hp h0 hd h2 h3 h4 _ _ _ ih1 ih2 ih3 =>
    exact .letE hp (hs _ _ h0) (hs _ _ hd) (hs _ _ h2) (hs _ _ h3) (hs _ _ h4) ih1 ih2 ih3
  | lit hp h0 hd h2 hl => exact .lit hp (hs _ _ h0) (hs _ _ hd) (hs _ _ h2) (litAt_mono hs hl)
  | proj hp h0 hd h2 h3 h4 hn hi _ ih =>
    exact .proj hp (hs _ _ h0) (hs _ _ hd) (hs _ _ h2) (hs _ _ h3) (hs _ _ h4) (nameAt_mono hs hn) hi ih

open Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString ConPanqueque.Logic in
/-- con-leche's `Expr.data` in Pancake: the data word at offset 8. -/
def exprDataBody : ProgHOL 64 :=
  .return (.load .one (.op .add [.var .local (ofString "e"), .const 8]))

open Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString ConPanqueque.Logic in
theorem exprDataBody_spec {σ : Type} (s : PanSemStateFiniteExact 64 σ) (p : BitVec 64) (e : ConLeche.Expr)
    (hv : s.locals.lookup (ofString "e") = some (.val (.word p))) {h : Heap} (hm : InMem s h)
    (he : ExprAt h p e) :
    (evaluateHOLFiniteState s exprDataBody).1 = some (.returned (.val (.word e.data.toBitVec))) := by
  obtain ⟨_, h8⟩ := exprAt_data he
  obtain ⟨hd, hw⟩ := hm _ _ h8
  unfold exprDataBody
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  simp only
  rw [eval_load_word s _ (p + 8) (by simp [evalHOLExact, evalListHOLExact, hv, wordOpHOL, wordOp,
    valueIsWord, valueWord]) hd, hw]
  simp [shapeOfHOLExact]

end ConPanqueque.Rep
