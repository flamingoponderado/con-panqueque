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

/-- The value of local `len` as a natural number (0 if absent). -/
def lenOf {σ : Type} (t : PanSemStateFiniteExact 64 σ) : Nat :=
  match t.locals.lookup (ofString "len") with
  | some (.val (.word w)) => w.toNat
  | _ => 0

theorem listRep_nil_iff {p : BitVec 64} {xs : List (BitVec 64)} {h : Heap} (hr : ListRep p xs h) :
    p = 0 ↔ xs = [] := by
  cases xs with
  | nil => simp [ListRep] at hr; simp [hr.1]
  | cons y ys => simp [ListRep] at hr; simp [hr.1]

/-- The loop computes `List.length`: from `len = 0` and `p` pointing to a list
representing `xs`, with enough clock, it ends normally with `len = |xs|` and
memory unchanged. -/
theorem lenLoop_spec {σ : Type} (s : PanSemStateFiniteExact 64 σ) (xs : List (BitVec 64)) (l : BitVec 64)
    (hsmall : xs.length < 2 ^ 64)
    (hl0 : s.locals.lookup (ofString "len") = some (.val (.word 0)))
    (hp0 : s.locals.lookup (ofString "p") = some (.val (.word l)))
    (hrep : Sat s (ListRep l xs)) (hclk : xs.length ≤ s.clock) :
    ∃ s', evaluateHOLFiniteState s lenLoop = (none, s') ∧
      s'.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 xs.length))) ∧
      s'.memory = s.memory := by
  let I : PanSemStateFiniteExact 64 σ → Prop := fun t => ∃ k q, k ≤ xs.length ∧
    t.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 k))) ∧
    t.locals.lookup (ofString "p") = some (.val (.word q)) ∧
    Sat t (ListRep q (xs.drop k)) ∧ xs.length - k ≤ t.clock ∧
    t.memory = s.memory ∧ t.memaddrs = s.memaddrs
  let Q : PanSemStateFiniteExact 64 σ → Prop := fun t =>
    t.locals.lookup (ofString "len") = some (.val (.word (BitVec.ofNat 64 xs.length))) ∧ t.memory = s.memory
  have hI0 : I s := ⟨0, l, Nat.zero_le _, by simpa using hl0, hp0, by simpa using hrep, by omega, rfl, rfl⟩
  refine while_rule (.cmp .notEqual (.var .local (ofString "p")) (.const 0))
    (.seq (.assign .local (ofString "len") (.op .add [.var .local (ofString "len"), .const 1]))
      (.assign .local (ofString "p") (.load .one (.op .add [.var .local (ofString "p"), .const 8]))))
    I (fun t => xs.length - lenOf t) Q ?_ s hI0
  rintro t ⟨k, q, hk, hlen, hp, hsat, hck, hmem, hdom⟩
  have hkn : lenOf t = k := by
    simp [lenOf, hlen]; omega
  refine ⟨if q ≠ 0 then 1 else 0, ?_, ?_, ?_⟩
  · simp [evalHOLFinite, evalHOLExact, hp, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  · intro hw
    have hq : q = 0 := by simpa using hw
    obtain ⟨h, hr, _⟩ := hsat
    have hnil := (listRep_nil_iff hr).mp hq
    have : k = xs.length := by simp at hnil; omega
    subst this
    exact ⟨hlen, hmem⟩
  · intro hw
    have hq : q ≠ 0 := by simpa using hw
    obtain ⟨y, ys, hys⟩ : ∃ y ys, xs.drop k = y :: ys := by
      obtain ⟨h, hr, _⟩ := hsat
      cases e : xs.drop k with
      | nil => exact absurd ((listRep_nil_iff hr).mpr e) hq
      | cons y ys => exact ⟨y, ys, rfl⟩
    have hlt : k < xs.length := by
      have : (xs.drop k).length = xs.length - k := List.length_drop ..
      rw [hys] at this; simp at this; omega
    rw [hys] at hsat
    obtain ⟨_, q', hd8, hv8, hrest⟩ := listRep_cons_next t q y ys hsat
    let t0 := decClockHOLFinite t
    obtain ⟨t', hev, hlen', hp', hmem', hdom', hclk'⟩ :=
      lenBody_step t0 (BitVec.ofNat 64 k) q q' (by simpa [t0, decClockHOLFinite] using hlen)
        (by simpa [t0, decClockHOLFinite] using hp) (by simpa [t0, decClockHOLFinite] using hd8)
        (by simpa [t0, decClockHOLFinite] using hv8)
    refine ⟨by omega, by omega, t', hev, ⟨k + 1, q', by omega, ?_, hp', ?_, ?_, ?_, ?_⟩, ?_⟩
    · rw [hlen']; simp [BitVec.ofNat_add]
    · have : xs.drop (k + 1) = ys := by
        rw [← List.drop_drop, hys]; rfl
      rw [this]
      exact sat_of_mem (by simp [hmem', t0, decClockHOLFinite]) (by simp [hdom', t0, decClockHOLFinite]) hrest
    · simp [hclk', t0, decClockHOLFinite]; omega
    · simp [hmem', t0, decClockHOLFinite, hmem]
    · simp [hdom', t0, decClockHOLFinite, hdom]
    · have : lenOf t' = k + 1 := by
        simp [lenOf, hlen']; omega
      omega

end ConPanqueque.Examples.ListLength
