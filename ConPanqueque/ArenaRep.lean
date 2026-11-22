import ConPanqueque.Rebuild
open ConPanqueque.Sep ConPanqueque.Rep

/-!
# Arena representations, uniformly

`ArenaRep α`: how a value of `α` is represented by a word in an arena `h`, with
monotonicity under arena growth (`Sub`). Instances for the checker's
datatypes: words, booleans, small naturals, names, levels, expressions, and the
generic `List`, `Option` and `Prod` (cells in the arena; `0` is `[]`/`none`).
The translator for the rest of the checker states refinements in these terms.
-/

namespace ConPanqueque.ArenaRep

class ArenaRep (α : Type) where
  R : Heap → BitVec 64 → α → Prop
  mono : ∀ {h h' : Heap}, Rep.Sub h h' → ∀ {p : BitVec 64} {a : α}, R h p a → R h' p a

instance : ArenaRep UInt64 where
  R _ p a := p = a.toBitVec
  mono := by intro _ _ _ _ _ hr; exact hr

instance : ArenaRep Bool where
  R _ p b := p = if b then 1 else 0
  mono := by intro _ _ _ _ _ hr; exact hr

instance : ArenaRep Nat where
  R h p n := NatAt h p n
  mono := by intro _ _ _ _ _ hr; exact hr

instance : ArenaRep ConLeche.Name where
  R h p n := NameAt h p n
  mono := by intro _ _ hs _ _ hr; exact nameAt_mono hs hr

instance : ArenaRep ConLeche.Level where
  R h p u := LevelAt h p u
  mono := by intro _ _ hs _ _ hr; exact levelAt_mono hs hr

instance : ArenaRep ConLeche.Expr where
  R h p e := ExprAt h p e
  mono := by intro _ _ hs _ _ hr; exact exprAt_mono hs hr

/-- Lists: `0` is `[]`, a cons is a cell `[head, tail]`. -/
inductive ListAt {α : Type} [ArenaRep α] (h : Heap) : BitVec 64 → List α → Prop
  | nil : ListAt h 0 []
  | cons {p q r : BitVec 64} {a : α} {as : List α} (hp : p ≠ 0) (h0 : h p = some (.word q))
      (h1 : h (p + 8) = some (.word r)) (ha : ArenaRep.R h q a) (has : ListAt h r as) : ListAt h p (a :: as)

theorem listAt_mono {α : Type} [ArenaRep α] {h h' : Heap} (hs : Rep.Sub h h') {p : BitVec 64} {l : List α}
    (hl : ListAt h p l) : ListAt h' p l := by
  induction hl with
  | nil => exact .nil
  | cons hp h0 h1 ha _ ih => exact .cons hp (hs _ _ h0) (hs _ _ h1) (ArenaRep.mono hs ha) ih

instance {α : Type} [ArenaRep α] : ArenaRep (List α) where
  R := ListAt
  mono := by intro _ _ hs _ _ hr; exact listAt_mono hs hr

/-- Options: `0` is `none`, `some a` is a cell `[a]`. -/
def OptionAt {α : Type} [ArenaRep α] (h : Heap) (p : BitVec 64) : Option α → Prop
  | none => p = 0
  | some a => p ≠ 0 ∧ ∃ q, h p = some (.word q) ∧ ArenaRep.R h q a

instance {α : Type} [ArenaRep α] : ArenaRep (Option α) where
  R := OptionAt
  mono := by
    intro h h' hs p o hr
    cases o with
    | none => exact hr
    | some a => obtain ⟨hp, q, h0, ha⟩ := hr; exact ⟨hp, q, hs _ _ h0, ArenaRep.mono hs ha⟩

/-- Pairs: a cell `[fst, snd]`. -/
def PairAt {α β : Type} [ArenaRep α] [ArenaRep β] (h : Heap) (p : BitVec 64) (x : α × β) : Prop :=
  p ≠ 0 ∧ ∃ q r, h p = some (.word q) ∧ h (p + 8) = some (.word r) ∧ ArenaRep.R h q x.1 ∧ ArenaRep.R h r x.2

instance {α β : Type} [ArenaRep α] [ArenaRep β] : ArenaRep (α × β) where
  R := PairAt
  mono := by
    intro h h' hs p x hr
    obtain ⟨hp, q, r, h0, h1, ha, hb⟩ := hr
    exact ⟨hp, q, r, hs _ _ h0, hs _ _ h1, ArenaRep.mono hs ha, ArenaRep.mono hs hb⟩

/-- The level lists of `const` nodes are `ListAt` lists. -/
theorem levelsAt_iff {h : Heap} {p : BitVec 64} {us : List ConLeche.Level} :
    LevelsAt h p us ↔ ListAt h p us := by
  constructor
  · intro hl; induction hl with
    | nil => exact .nil
    | cons hp h0 h1 hu _ ih => exact .cons hp h0 h1 hu ih
  · intro hl; induction hl with
    | nil => exact .nil
    | cons hp h0 h1 hu _ ih => exact .cons hp h0 h1 hu ih

end ConPanqueque.ArenaRep

namespace ConPanqueque.ArenaRep
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.Node ConPanqueque.StateHeap ConPanqueque.Rebuild ConPanqueque.ExprCons

/-- A translated function's result: stop, or a word representing `a` in the grown arena. -/
abbrev RResA {σ : Type} {α : Type} [ArenaRep α] (s : PanSemStateFiniteExact 64 σ)
    (r : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ) (lo hp : BitVec 64) (a : α) (c : Nat) : Prop :=
  RRes s r lo hp (fun h q => ArenaRep.R h q a) c

/-- Allocating a two-word cell `[x, y]` whose words represent `a` and `b` gives a representation of `mk a b`,
for any constructor laid out as such a cell. -/
theorem cell2_spec {σ : Type} {α β γ : Type} [ArenaRep α] [ArenaRep β] [ArenaRep γ]
    (t : PanSemStateFiniteExact 64 σ) (lo hp q r : BitVec 64) (x y : MlS) (a : α) (b : β) (g : γ)
    (hxy : x ≠ y) (hx : x ≠ nP) (hy : y ≠ nP)
    (hi : AInv t lo hp) (ha : ArenaRep.R (hOf t lo hp) q a) (hb : ArenaRep.R (hOf t lo hp) r b)
    (lx : t.locals.lookup x = some (.val (.word q))) (ly : t.locals.lookup y = some (.val (.word r)))
    (hbuild : ∀ (h' : Heap) (p0 : BitVec 64), p0 ≠ 0 → h' p0 = some (.word q) → h' (p0 + 8) = some (.word r) →
      ArenaRep.R h' q a → ArenaRep.R h' r b → ArenaRep.R h' p0 g) :
    RResA t (evaluateHOLFiniteState t (mkCell [x, y])) lo hp g 0 := by
  rcases mkCell_ainv t lo hp [x, y] [q, r] rfl (by simp [Ne.symm hx, Ne.symm hy]) (by simp) (by simp)
      (fun j hj => match j, hj with | 0, _ => lx | 1, _ => ly) hi with
    hs | ⟨hr, a5, g5, hpos, cells, cd5, ck5, gl5, md5, ta5⟩
  · exact Or.inl hs
  right
  have c0 := cells 0 (by simp)
  have c1 := cells 1 (by simp)
  simp only [at8, List.length_cons, List.length_nil] at c0 c1
  rw [show hp + BitVec.ofNat 64 (8 * 0) = hp by simp] at c0
  rw [show BitVec.ofNat 64 (8 * 1) = 8#64 from by decide] at c1
  have sub := grows_sub g5
  exact ⟨hp, hr, _, a5, g5, hbuild _ hp hpos c0 c1 (ArenaRep.mono sub ha) (ArenaRep.mono sub hb),
    cd5, by rw [ck5]; omega, gl5, md5, ta5⟩

theorem cons_spec {σ : Type} {α : Type} [ArenaRep α] (t : PanSemStateFiniteExact 64 σ) (lo hp q r : BitVec 64)
    (x y : MlS) (a : α) (as : List α) (hxy : x ≠ y) (hx : x ≠ nP) (hy : y ≠ nP) (hi : AInv t lo hp)
    (ha : ArenaRep.R (hOf t lo hp) q a) (has : ArenaRep.R (hOf t lo hp) r as)
    (lx : t.locals.lookup x = some (.val (.word q))) (ly : t.locals.lookup y = some (.val (.word r))) :
    RResA t (evaluateHOLFiniteState t (mkCell [x, y])) lo hp (a :: as) 0 :=
  cell2_spec t lo hp q r x y a as (a :: as) hxy hx hy hi ha has lx ly
    (fun _ _ hp0 c0 c1 ha' has' => ListAt.cons hp0 c0 c1 ha' has')

theorem pair_spec {σ : Type} {α β : Type} [ArenaRep α] [ArenaRep β] (t : PanSemStateFiniteExact 64 σ)
    (lo hp q r : BitVec 64) (x y : MlS) (a : α) (b : β) (hxy : x ≠ y) (hx : x ≠ nP) (hy : y ≠ nP) (hi : AInv t lo hp)
    (ha : ArenaRep.R (hOf t lo hp) q a) (hb : ArenaRep.R (hOf t lo hp) r b)
    (lx : t.locals.lookup x = some (.val (.word q))) (ly : t.locals.lookup y = some (.val (.word r))) :
    RResA t (evaluateHOLFiniteState t (mkCell [x, y])) lo hp (a, b) 0 :=
  cell2_spec t lo hp q r x y a b (a, b) hxy hx hy hi ha hb lx ly
    (fun _ _ hp0 c0 c1 ha' hb' => ⟨hp0, q, r, c0, c1, ha', hb'⟩)

end ConPanqueque.ArenaRep
