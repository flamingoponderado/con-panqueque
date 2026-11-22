import ConPanqueque.Logic.Sep
import ConLeche
import ConPanqueque.Logic.Basic
open Flapjack ConPanqueque.Sep

/-!
# Representations of con-leche's data in Pancake memory

con-leche's names, levels and expressions are DAGs (shared prefixes and
subterms), so their nodes live in an immutable, append-only arena: the arena is
one owned region (separation logic, `Logic/Sep.lean`), and the shape of a value
is a non-separating predicate over the arena's words (`NameAt h p n`), monotone
under heap extension (`nameAt_mono`). `nameHashBody` is the first con-leche
function in Pancake, proved to compute `Name.hashData`.
-/

namespace ConPanqueque.Rep
open Flapjack Flapjack.PanSemStateFiniteExact ConPanqueque.Sep

/-- The value of little-endian 64-bit limbs. -/
def limbsVal : List (BitVec 64) → Nat
  | [] => 0
  | l :: ls => l.toNat + 2 ^ 64 * limbsVal ls

theorem sat_sep_right {σ : Type} {s : PanSemStateFiniteExact 64 σ} {P Q : Assn}
    (hs : Sat s (P ∗ Q)) : Sat s Q :=
  sat_sep_left (sat_mono (fun h hh => sep_comm _ _ h hh) hs)

/-- The `i`-th word of a block, through `block p ws ∗ R`. -/
theorem block_get {σ : Type} (s : PanSemStateFiniteExact 64 σ) :
    ∀ (ws : List (HolWordLab 64)) (p : BitVec 64) (R : Assn) (i : Nat) (hi : i < ws.length),
      Sat s (block p ws ∗ R) →
      s.memaddrs (p + BitVec.ofNat 64 (8 * i)) ∧ s.memory (p + BitVec.ofNat 64 (8 * i)) = ws[i]
  | [], _, _, i, hi, _ => absurd hi (by simp)
  | w :: ws, p, R, 0, _, hs => by
    simp only [block] at hs
    have := load_frame s p w _ (sat_mono (fun h hh => sep_assoc _ _ _ h hh) hs)
    simpa using this
  | w :: ws, p, R, i + 1, hi, hs => by
    simp only [block] at hs
    have hs' := sat_sep_right (sat_mono (fun h hh => sep_assoc _ _ _ h hh) hs)
    have := block_get s ws (p + 8) R i (by simpa using hi) hs'
    have he : p + 8 + BitVec.ofNat 64 (8 * i) = p + BitVec.ofNat 64 (8 * (i + 1)) := by
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
    rw [he] at this
    simpa using this

/-- A string in an immutable arena `h`: `[len, byte₀, …]`, one byte per word. -/
def StrAt (h : Heap) (v : BitVec 64) (s : String) : Prop :=
  ∀ i (hi : i < s.toUTF8.size + 1),
    h (v + BitVec.ofNat 64 (8 * i)) =
      some (.word (if i = 0 then BitVec.ofNat 64 s.toUTF8.size
                   else BitVec.ofNat 64 (s.toUTF8.get! (i - 1)).toNat))

/-- A natural number (small: odd-tagged word; large: not yet). -/
def NatAt (_h : Heap) (v : BitVec 64) (n : Nat) : Prop :=
  n < 2 ^ 63 ∧ v = BitVec.ofNat 64 (2 * n + 1)

/-- A name in an immutable arena `h`, sharing allowed: `anonymous` is `0`;
`str`/`num` are `[tag, hashData, prefix, payload]`. -/
inductive NameAt (h : Heap) : BitVec 64 → ConLeche.Name → Prop
  | anonymous : NameAt h 0 .anonymous
  | str {p q sv : BitVec 64} {pre : ConLeche.Name} {s : String} (hp : p ≠ 0)
      (h0 : h p = some (.word 1)) (h1 : h (p + 8) = some (.word (ConLeche.Name.str pre s).hashData.toBitVec))
      (h2 : h (p + 16) = some (.word q)) (h3 : h (p + 24) = some (.word sv))
      (hpre : NameAt h q pre) (hs : StrAt h sv s) : NameAt h p (.str pre s)
  | num {p q kv : BitVec 64} {pre : ConLeche.Name} {k : Nat} (hp : p ≠ 0)
      (h0 : h p = some (.word 2)) (h1 : h (p + 8) = some (.word (ConLeche.Name.num pre k).hashData.toBitVec))
      (h2 : h (p + 16) = some (.word q)) (h3 : h (p + 24) = some (.word kv))
      (hpre : NameAt h q pre) (hk : NatAt h kv k) : NameAt h p (.num pre k)

/-- Heap inclusion. -/
def Sub (h h' : Heap) : Prop := ∀ a w, h a = some w → h' a = some w

theorem nameAt_mono {h h' : Heap} (hs : Sub h h') {p : BitVec 64} {n : ConLeche.Name}
    (hn : NameAt h p n) : NameAt h' p n := by
  induction hn with
  | anonymous => exact .anonymous
  | str hp h0 h1 h2 h3 _ hstr ih =>
    exact .str hp (hs _ _ h0) (hs _ _ h1) (hs _ _ h2) (hs _ _ h3) ih (fun i hi => hs _ _ (hstr i hi))
  | num hp h0 h1 h2 h3 _ hk ih => exact .num hp (hs _ _ h0) (hs _ _ h1) (hs _ _ h2) (hs _ _ h3) ih hk

/-- What the memory of a state holds of an arena fragment `h`. -/
def InMem {σ : Type} (s : PanSemStateFiniteExact 64 σ) (h : Heap) : Prop :=
  ∀ a w, h a = some w → s.memaddrs a ∧ s.memory a = w

theorem nameAt_hash {σ : Type} {s : PanSemStateFiniteExact 64 σ} {h : Heap} (hm : InMem s h)
    {p : BitVec 64} {n : ConLeche.Name} (hn : NameAt h p n) (hp : p ≠ 0) :
    s.memaddrs (p + 8) ∧ s.memory (p + 8) = .word n.hashData.toBitVec := by
  cases hn with
  | anonymous => exact absurd rfl hp
  | str _ _ h1 => exact hm _ _ h1
  | num _ _ h1 => exact hm _ _ h1

open Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString ConPanqueque.Logic in
/-- con-leche's `Hashable Name` (`hashData`) in Pancake: `0` is `anonymous`
(hash 1723), otherwise the cached hash at offset 8. -/
def nameHashBody : ProgHOL 64 :=
  .ite (.cmp .equal (.var .local (ofString "n")) (.const 0))
    (.return (.const 1723))
    (.return (.load .one (.op .add [.var .local (ofString "n"), .const 8])))

open Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString ConPanqueque.Logic in
theorem nameHashBody_spec {σ : Type} (s : PanSemStateFiniteExact 64 σ) (p : BitVec 64) (n : ConLeche.Name)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word p))) {h : Heap} (hm : InMem s h) (hs : NameAt h p n) :
    (evaluateHOLFiniteState s nameHashBody).1 = some (.returned (.val (.word n.hashData.toBitVec))) := by
  unfold nameHashBody
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  by_cases hp : p = 0
  · subst hp
    have : n = .anonymous := by
      cases hs with
      | anonymous => rfl
      | str hp => exact absurd rfl hp
      | num hp => exact absurd rfl hp
    subst this
    simp [evalHOLFinite, evalHOLExact, hn, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    simp [shapeOfHOLExact, ConLeche.Name.hashData]
  · obtain ⟨hd, hv⟩ := nameAt_hash hm hs hp
    simp [evalHOLFinite, evalHOLExact, hn, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hp,
      evalListHOLExact, wordOpHOL, wordOp, valueIsWord, valueWord, memLoadHOLExact, hd, hv, shapeOfHOLExact]
    split
    · rename_i h0; exact absurd h0 hp
    · split
      · rename_i hv' hm
        split at hm
        · cases hm
        · exact absurd hd (by assumption)
      · rename_i v hm
        split at hm
        · cases hm; simp [shapeOfHOLExact]; exact hv
        · exact absurd hd (by assumption)

/-! ## Levels -/

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
