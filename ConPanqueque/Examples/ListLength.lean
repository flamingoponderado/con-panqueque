import ConPanqueque.Logic.Sep
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.Sep

/-!
# First data-structure refinement: list length

A Pancake loop walking a linked list (`ListRep`, two-word cons cells) is
proved to compute `List.length`. This file: the loop, reading a cell's next
pointer through `ListRep`, and one iteration of the body.
-/

namespace ConPanqueque.Examples.ListLength

/-- The loop: `while (p != 0) { len = len + 1; p = ld (p + 8); }` -/
def lenLoop : ProgHOL 64 :=
  .while (.cmp .notEqual (.var .local (ofString "p")) (.const 0))
    (.seq (.assign .local (ofString "len") (.op .add [.var .local (ofString "len"), .const 1]))
      (.assign .local (ofString "p") (.load .one (.op .add [.var .local (ofString "p"), .const 8]))))

/-- The next pointer of a cons cell, read through `ListRep`. -/
theorem listRep_cons_next {σ : Type} (t : PanSemStateFiniteExact 64 σ) (q : BitVec 64)
    (y : BitVec 64) (ys : List (BitVec 64)) (hs : Sat t (ListRep q (y :: ys))) :
    q ≠ 0 ∧ ∃ q', t.memaddrs (q + 8) ∧ t.memory (q + 8) = .word q' ∧ Sat t (ListRep q' ys) := by
  obtain ⟨h, ⟨hq, q', hh⟩, hm⟩ := hs
  refine ⟨hq, q', ?_⟩
  have hs' : Sat t (block q [.word y, .word q'] ∗ ListRep q' ys) := ⟨h, hh, hm⟩
  -- block q [y, q'] ∗ L = (q ↦ y ∗ (q+8 ↦ q' ∗ emp)) ∗ L
  have h2 : Sat t ((q + 8 ↦ .word q') ∗ ((emp ∗ ListRep q' ys) ∗ (q ↦ .word y))) := by
    apply sat_mono _ hs'
    intro h hh
    simp only [block] at hh
    have := sep_assoc _ _ _ h hh
    have := sep_comm _ _ h this
    exact sep_assoc _ _ _ h (by
      obtain ⟨h₁, h₂, hd, he, ha, hb⟩ := this
      exact ⟨h₁, h₂, hd, he, sep_assoc _ _ _ h₁ ha, hb⟩)
  obtain ⟨hdom, hval⟩ := load_frame t _ _ _ h2
  refine ⟨hdom, hval, ?_⟩
  exact sat_sep_left (sat_mono (fun h hh => sep_comm _ _ h hh) hs')

theorem sat_of_mem {σ : Type} {t t' : PanSemStateFiniteExact 64 σ} {P : Assn}
    (hm : t'.memory = t.memory) (hd : t'.memaddrs = t.memaddrs) (hs : Sat t P) : Sat t' P := by
  obtain ⟨h, hp, hh⟩ := hs; exact ⟨h, hp, fun a w ha => by rw [hm, hd]; exact hh a w ha⟩

/-- One iteration of `lenLoop`'s body. -/
theorem lenBody_step {σ : Type} (t : PanSemStateFiniteExact 64 σ) (k q q' : BitVec 64)
    (hlen : t.locals.lookup (ofString "len") = some (.val (.word k)))
    (hp : t.locals.lookup (ofString "p") = some (.val (.word q)))
    (hdom : t.memaddrs (q + 8)) (hval : t.memory (q + 8) = .word q') :
    ∃ t', evaluateHOLFiniteState t
      (.seq (.assign .local (ofString "len") (.op .add [.var .local (ofString "len"), .const 1]))
        (.assign .local (ofString "p") (.load .one (.op .add [.var .local (ofString "p"), .const 8])))) =
        (none, t') ∧
      t'.locals.lookup (ofString "len") = some (.val (.word (k + 1))) ∧
      t'.locals.lookup (ofString "p") = some (.val (.word q')) ∧
      t'.memory = t.memory ∧ t'.memaddrs = t.memaddrs ∧ t'.clock = t.clock := by
  have hne : ofString "p" ≠ ofString "len" := by decide
  let t1 := setKvarHOLFinite .local (ofString "len") (.val (.word (k + 1))) t
  have h1 : evaluateHOLFiniteState t (.assign .local (ofString "len")
      (.op .add [.var .local (ofString "len"), .const 1])) = (none, t1) := by
    apply assign_ok
    · simp [evalHOLExact, evalListHOLExact, hlen, wordOpHOL, wordOp, valueIsWord, valueWord]
    · simp [isValidValueHOLFinite, lookupKvarHOLFinite, hlen, shapeOfHOLExact, shapeEqHOL]
  have hp1 : t1.locals.lookup (ofString "p") = some (.val (.word q)) := by
    simp only [t1, setKvarHOLFinite]; rw [lookup_setVar_other _ _ hne, hp]
  refine ⟨setKvarHOLFinite .local (ofString "p") (.val (.word q')) t1, ?_, ?_, ?_, rfl, rfl, rfl⟩
  · rw [seq_normal _ h1]
    apply assign_ok
    · have hd1 : t1.memaddrs (q + 8) := by simpa [t1, setKvarHOLFinite, setVarHOLFinite] using hdom
      have hv1 : t1.memory (q + 8) = .word q' := by simpa [t1, setKvarHOLFinite, setVarHOLFinite] using hval
      rw [eval_load_word t1 _ (q + 8) ?_ hd1, hv1]
      simp [evalHOLExact, evalListHOLExact, hp1, wordOpHOL, wordOp, valueIsWord, valueWord]
    · simp [isValidValueHOLFinite, lookupKvarHOLFinite, hp1, shapeOfHOLExact, shapeEqHOL]
  · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm hne)]
    simp [t1, setKvarHOLFinite]
  · simp [setKvarHOLFinite]

end ConPanqueque.Examples.ListLength
