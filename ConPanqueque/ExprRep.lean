import ConPanqueque.Rep
open Flapjack Flapjack.PanSemStateFiniteExact ConPanqueque.Sep ConPanqueque.Rep

/-!
# Expressions in the arena

`ExprAt h p e`: a block `[tag, data, fields…]` per constructor of con-leche's
`Expr`, with `data` its packed derived-data word; level lists, literals,
names and naturals by their own arena predicates. `exprDataBody` reads
`Expr.data`.
-/

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
    StrAt h' v str := ⟨ha.1, fun i hi => hs _ _ (ha.2 i hi)⟩

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

/-! ## Uniqueness: a pointer represents one value

The arena is immutable, so the value at a pointer is determined: the basis of
memoizing by pointer. -/

theorem strAt_unique {h : Heap} {v : BitVec 64} {s s' : String} (ha : StrAt h v s) (hb : StrAt h v s') : s = s' := by
  obtain ⟨sz, ha⟩ := ha
  obtain ⟨sz', hb⟩ := hb
  have q1 : s.toUTF8.size = s.utf8ByteSize := by simp
  have q2 : s'.toUTF8.size = s'.utf8ByteSize := by simp
  have e0 := (ha 0 (by omega)).symm.trans (hb 0 (by omega))
  simp at e0
  have hsz : s.toUTF8.size = s'.toUTF8.size := by
    have := congrArg BitVec.toNat e0; simp at this; omega
  apply String.toByteArray_inj.mp
  apply ByteArray.ext
  apply Array.ext
  · simpa using hsz
  · intro i h1 h2
    have e := (ha (i + 1) (by simp at h1; omega)).symm.trans (hb (i + 1) (by simp at h2; omega))
    simp at e
    have := congrArg BitVec.toNat e
    simp at this
    have hh := UInt8.toNat_inj.mp this
    have i1 : i < s.toByteArray.data.size := h1
    have i2 : i < s'.toByteArray.data.size := h2
    simp only [ByteArray.get!] at hh
    rw [Array.getElem!_eq_getD, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem i1, Array.getElem?_eq_getElem i2] at hh
    simpa using hh

theorem natAt_unique {h h' : Heap} {v : BitVec 64} {n n' : Nat} (ha : NatAt h v n) (hb : NatAt h' v n') : n = n' := by
  obtain ⟨b1, e1⟩ := ha
  obtain ⟨b2, e2⟩ := hb
  have := congrArg BitVec.toNat (e1.symm.trans e2)
  simp at this; omega


theorem nameAt_unique {h : Heap} {p : BitVec 64} {n n' : ConLeche.Name} (hn : NameAt h p n) (hn' : NameAt h p n') :
    n = n' := by
  induction hn generalizing n' with
  | anonymous => cases hn' with
    | anonymous => rfl
    | str hp => exact absurd rfl hp
    | num hp => exact absurd rfl hp
  | str hp h0 h1 h2 h3 hpre hs ih =>
    cases hn' with
    | anonymous => exact absurd rfl hp
    | str _ h0' _ h2' h3' hpre' hs' =>
      rw [h2] at h2'; rw [h3] at h3'; simp at h2' h3'; subst h2'; subst h3'
      rw [ih hpre', strAt_unique hs hs']
    | num _ h0' => rw [h0] at h0'; simp at h0'
  | num hp h0 h1 h2 h3 hpre hk ih =>
    cases hn' with
    | anonymous => exact absurd rfl hp
    | str _ h0' => rw [h0] at h0'; simp at h0'
    | num _ h0' _ h2' h3' hpre' hk' =>
      rw [h2] at h2'; rw [h3] at h3'; simp at h2' h3'; subst h2'; subst h3'
      rw [ih hpre', natAt_unique hk hk']

theorem levelAt_unique {h : Heap} {p : BitVec 64} {u u' : ConLeche.Level} (hu : LevelAt h p u)
    (hu' : LevelAt h p u') : u = u' := by
  induction hu generalizing u' with
  | zero hp h0 h1 => cases hu' <;> simp_all
  | succ hp h0 h1 h2 hu ih =>
    cases hu' with
    | succ _ h0' _ h2' hu' => rw [h2] at h2'; simp at h2'; subst h2'; rw [ih hu']
    | _ => simp_all
  | max hp h0 h1 h2 h3 hu hv ih1 ih2 =>
    cases hu' with
    | max _ h0' _ h2' h3' hu' hv' =>
      rw [h2] at h2'; rw [h3] at h3'; simp at h2' h3'; subst h2'; subst h3'; rw [ih1 hu', ih2 hv']
    | _ => simp_all
  | imax hp h0 h1 h2 h3 hu hv ih1 ih2 =>
    cases hu' with
    | imax _ h0' _ h2' h3' hu' hv' =>
      rw [h2] at h2'; rw [h3] at h3'; simp at h2' h3'; subst h2'; subst h3'; rw [ih1 hu', ih2 hv']
    | _ => simp_all
  | param hp h0 h1 h2 hn =>
    cases hu' with
    | param _ h0' _ h2' hn' => rw [h2] at h2'; simp at h2'; subst h2'; rw [nameAt_unique hn hn']
    | _ => simp_all


theorem levelsAt_unique {h : Heap} {p : BitVec 64} {us us' : List ConLeche.Level} (ha : LevelsAt h p us)
    (hb : LevelsAt h p us') : us = us' := by
  induction ha generalizing us' with
  | nil => cases hb with
    | nil => rfl
    | cons hp => exact absurd rfl hp
  | cons hp h0 h1 hu hus ih =>
    cases hb with
    | nil => exact absurd rfl hp
    | cons _ h0' h1' hu' hus' =>
      rw [h0] at h0'; rw [h1] at h1'; simp at h0' h1'; subst h0'; subst h1'
      rw [levelAt_unique hu hu', ih hus']

theorem litAt_unique {h : Heap} {p : BitVec 64} {l l' : ConLeche.Literal} (ha : LitAt h p l) (hb : LitAt h p l') :
    l = l' := by
  cases ha with
  | natVal hp h0 h1 hn => cases hb with
    | natVal _ _ h1' hn' => rw [h1] at h1'; simp at h1'; subst h1'; rw [natAt_unique hn hn']
    | strVal _ h0' => rw [h0] at h0'; simp at h0'
  | strVal hp h0 h1 hs => cases hb with
    | natVal _ h0' => rw [h0] at h0'; simp at h0'
    | strVal _ _ h1' hs' => rw [h1] at h1'; simp at h1'; subst h1'; rw [strAt_unique hs hs']

theorem exprAt_unique {h : Heap} {p : BitVec 64} {e e' : ConLeche.Expr} (he : ExprAt h p e) (he' : ExprAt h p e') :
    e = e' := by
  induction he generalizing e' with
  | bvar hp h0 hd h2 hi =>
    cases he' with
    | bvar _ _ _ h2' hi' => rw [h2] at h2'; simp at h2'; subst h2'; rw [natAt_unique hi hi']
    | _ => simp_all
  | fvar hp h0 hd h2 h3 hi hty ih =>
    cases he' with
    | fvar _ _ _ h2' h3' hi' hty' =>
      rw [h2] at h2'; rw [h3] at h3'; simp at h2' h3'; subst h2'; subst h3'; rw [natAt_unique hi hi', ih hty']
    | _ => simp_all
  | sort hp h0 hd h2 hu =>
    cases he' with
    | sort _ _ _ h2' hu' => rw [h2] at h2'; simp at h2'; subst h2'; rw [levelAt_unique hu hu']
    | _ => simp_all
  | const hp h0 hd h2 h3 hn hus =>
    cases he' with
    | const _ _ _ h2' h3' hn' hus' =>
      rw [h2] at h2'; rw [h3] at h3'; simp at h2' h3'; subst h2'; subst h3'
      rw [nameAt_unique hn hn', levelsAt_unique hus hus']
    | _ => simp_all
  | app hp h0 hd h2 h3 ha hb iha ihb =>
    cases he' with
    | app _ _ _ h2' h3' ha' hb' =>
      rw [h2] at h2'; rw [h3] at h3'; simp at h2' h3'; subst h2'; subst h3'; rw [iha ha', ihb hb']
    | _ => simp_all
  | lam hp h0 hd h2 h3 ha hb iha ihb =>
    cases he' with
    | lam _ _ _ h2' h3' ha' hb' =>
      rw [h2] at h2'; rw [h3] at h3'; simp at h2' h3'; subst h2'; subst h3'; rw [iha ha', ihb hb']
    | _ => simp_all
  | forallE hp h0 hd h2 h3 ha hb iha ihb =>
    cases he' with
    | forallE _ _ _ h2' h3' ha' hb' =>
      rw [h2] at h2'; rw [h3] at h3'; simp at h2' h3'; subst h2'; subst h3'; rw [iha ha', ihb hb']
    | _ => simp_all
  | letE hp h0 hd h2 h3 h4 ha hb hc iha ihb ihc =>
    cases he' with
    | letE _ _ _ h2' h3' h4' ha' hb' hc' =>
      rw [h2] at h2'; rw [h3] at h3'; rw [h4] at h4'; simp at h2' h3' h4'; subst h2'; subst h3'; subst h4'
      rw [iha ha', ihb hb', ihc hc']
    | _ => simp_all
  | lit hp h0 hd h2 hl =>
    cases he' with
    | lit _ _ _ h2' hl' => rw [h2] at h2'; simp at h2'; subst h2'; rw [litAt_unique hl hl']
    | _ => simp_all
  | proj hp h0 hd h2 h3 h4 hn hi he ih =>
    cases he' with
    | proj _ _ _ h2' h3' h4' hn' hi' he' =>
      rw [h2] at h2'; rw [h3] at h3'; rw [h4] at h4'; simp at h2' h3' h4'; subst h2'; subst h3'; subst h4'
      rw [nameAt_unique hn hn', natAt_unique hi hi', ih he']
    | _ => simp_all

end ConPanqueque.Rep
