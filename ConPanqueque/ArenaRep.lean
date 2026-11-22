import ConPanqueque.ExprRep
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
