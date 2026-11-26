import ConPanqueque.T.Ind.IndNames
import ConPanqueque.T.Decl.BasisInv
import ConPanqueque.T.Decl.StepRuns

/-!
# The record of an inductive block: the twin's name checks

`andPinOk` and `basisNamesOk` at an `.indDecl` whose names are free (`NameFree`) and that is none of the pinned
basis blocks (the names against the reserved slices): both `true`, the state kept.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Decl ConPanqueque.Logic.InternRerun ConPanqueque.Logic.BasisNames

theorem blockAndNamed_false {C : Ctx} (hok : CtxOK C) :
    ∀ (block : List IConstantInfo), (∀ c ∈ block, NameFree C c.name) →
      blockAndNamed [C.pins.names[11]!, C.pins.names[48]!, C.pins.names[49]!] block = false
  | [], _ => rfl
  | c :: cs, h => by
    obtain ⟨f1, f2, -⟩ := h c (by simp)
    simp only [pinIn, List.range', List.any_cons, List.any_nil, Bool.or_false, Nat.reduceAdd, Nat.reduceSub,
      Bool.or_eq_false_iff, beq_eq_false_iff_ne] at f1 f2
    simp only [blockAndNamed, List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_false_iff,
      beq_eq_false_iff_ne]
    have ih := blockAndNamed_false hok cs (fun x hx => h x (by simp [hx]))
    refine ⟨?_, ih⟩
    exact ⟨f1, f2⟩

/-- **`andPinOk` at a block of free names**: `true`, the state kept. -/
theorem andPinOk_ind {C : Ctx} (hok : CtxOK C) {s : AState} (hp : s.pins = C.pins) (block : List IConstantInfo)
    (nP : Nat) (hfree : ∀ c ∈ block, NameFree C c.name) : andPinOk (.indDecl block nP) s = .ok (true, s) := by
  have h := fun i (hi : i < pinCount) => pinAt_run hok hp i hi
  unfold andPinOk andPinNameHs
  simp only [pinAnd, pinAndIntro, pinAndRec, PIN_AND, PIN_AND_INTRO, PIN_AND_REC]
  simp [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, h _ (show 11 < pinCount by decide),
    h _ (show 48 < pinCount by decide), h _ (show 49 < pinCount by decide), blockAndNamed_false hok block hfree]

theorem reserved_run {C : Ctx} (hok : CtxOK C) {s : AState} (hp : s.pins = C.pins) :
    reservedBasisNames s = .ok (C.pins.reserved, s) := by
  simp [reservedBasisNames, pinReserved, pinsReady_of hok hp, hp, get, getThe,
    MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure]

/-- The block is none of the pinned basis blocks, by its names. -/
def NoHit (C : Ctx) (block : List IConstantInfo) : Prop :=
  ∀ k ∈ [ConLeche.BasisKind.eqK, .natK, .emptyK, .falseK], resSlice k C.pins.reserved ≠ block.map (·.name)

theorem block_all_free {C : Ctx} : ∀ (block : List IConstantInfo), (∀ c ∈ block, NameFree C c.name) →
    (block.all fun c => !C.pins.reserved.contains c.name) = true
  | [], _ => rfl
  | c :: cs, h => by
    simp only [List.all_cons, Bool.and_eq_true]
    exact ⟨by rw [(h c (by simp)).2.2]; rfl, block_all_free cs (fun x hx => h x (by simp [hx]))⟩

/-- **`basisNamesOk` at a block of free names, none of the pinned ones**: `true`, the state kept. -/
theorem basisNamesOk_ind {σ : Type} {C : Ctx} (hok : CtxOK C) (hb : BasisInv C) {s : AState} {t : PState σ}
    (hsr : SR C s t) (hoff : Off s.store) (block : List IConstantInfo) (nP : Nat)
    (hfree : ∀ c ∈ block, NameFree C c.name) (hnh : NoHit C block) :
    basisNamesOk (.indDecl block nP) s = .ok (true, s) := by
  obtain ⟨r1, h1, n1⟩ := basis_at hb hsr hoff .eqK (by decide)
  obtain ⟨r2, h2, n2⟩ := basis_at hb hsr hoff .natK (by decide)
  obtain ⟨r3, h3, n3⟩ := basis_at hb hsr hoff .emptyK (by decide)
  obtain ⟨r4, h4, n4⟩ := basis_at hb hsr hoff .falseK (by decide)
  have e1 : (blockNames r1 == blockNames block) = false := by
    simp only [blockNames, n1, beq_eq_false_iff_ne]; exact hnh _ (by simp)
  have e2 : (blockNames r2 == blockNames block) = false := by
    simp only [blockNames, n2, beq_eq_false_iff_ne]; exact hnh _ (by simp)
  have e3 : (blockNames r3 == blockNames block) = false := by
    simp only [blockNames, n3, beq_eq_false_iff_ne]; exact hnh _ (by simp)
  have e4 : (blockNames r4 == blockNames block) = false := by
    simp only [blockNames, n4, beq_eq_false_iff_ne]; exact hnh _ (by simp)
  have hr := reserved_run hok hsr.pins
  unfold basisNamesOk basisNameHit
  simp only [basisNameHitGo, bind, StateT.bind, Except.bind, h1, h2, h3, h4, e1, e2, e3, e4,
    Bool.false_eq_true, ↓reduceIte, pure, StateT.pure, Except.pure, hr, block_all_free block hfree]

end ConPanqueque.T.Ind
