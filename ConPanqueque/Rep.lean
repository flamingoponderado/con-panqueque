import ConPanqueque.Logic.Sep
import ConLeche
import ConPanqueque.Logic.Basic
open Flapjack ConPanqueque.Sep

/-!
# Representations of con-leche's data in Pancake memory

Separation-logic predicates relating con-leche values to memory: naturals
(small values odd-tagged, large ones as limb blocks), strings, and names
(hash-carrying blocks). `nameHashBody` is the first con-leche function in
Pancake, proved to compute `Name.hashData`.
-/

namespace ConPanqueque.Rep

/-- The value of little-endian 64-bit limbs. -/
def limbsVal : List (BitVec 64) → Nat
  | [] => 0
  | l :: ls => l.toNat + 2 ^ 64 * limbsVal ls

/-- A natural number: an odd word `2n + 1` when `n < 2^63`, otherwise a pointer
(even, nonzero) to a block `[len, limb₀, …]` whose last limb is nonzero. -/
def NatRep (v : BitVec 64) (n : Nat) : Assn := fun h =>
  (n < 2 ^ 63 ∧ v = BitVec.ofNat 64 (2 * n + 1) ∧ emp h) ∨
  (2 ^ 63 ≤ n ∧ v.getLsbD 0 = false ∧ v ≠ 0 ∧ ∃ ls : List (BitVec 64),
    limbsVal ls = n ∧ ls.getLast? ≠ some 0 ∧
    block v (.word (BitVec.ofNat 64 ls.length) :: ls.map .word) h)

/-- A string: a block `[len, byte₀, …]`, one UTF-8 byte per word. -/
def StrRep (v : BitVec 64) (s : String) : Assn :=
  block v (.word (BitVec.ofNat 64 s.toUTF8.size) ::
    s.toUTF8.toList.map fun b => .word (BitVec.ofNat 64 b.toNat))

/-- A name: `anonymous` is `0`; `str`/`num` are blocks
`[tag, hashData, prefix, payload]` (tag 1 for `str`, 2 for `num`). -/
def NameRep : BitVec 64 → ConLeche.Name → Assn
  | p, .anonymous => fun h => p = 0 ∧ emp h
  | p, n@(.str pre s) => fun h => p ≠ 0 ∧ ∃ q sv,
      (block p [.word 1, .word n.hashData.toBitVec, .word q, .word sv] ∗ (NameRep q pre ∗ StrRep sv s)) h
  | p, n@(.num pre k) => fun h => p ≠ 0 ∧ ∃ q kv,
      (block p [.word 2, .word n.hashData.toBitVec, .word q, .word kv] ∗ (NameRep q pre ∗ NatRep kv k)) h

end ConPanqueque.Rep

namespace ConPanqueque.Rep
open Flapjack.PanSemStateFiniteExact

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

/-- A nonempty name's cached hash is the second word of its block. -/
theorem nameRep_hash {σ : Type} (s : PanSemStateFiniteExact 64 σ) (p : BitVec 64) (n : ConLeche.Name)
    (hs : Sat s (NameRep p n)) (hp : p ≠ 0) :
    s.memaddrs (p + 8) ∧ s.memory (p + 8) = .word n.hashData.toBitVec := by
  obtain ⟨h, hr, hm⟩ := hs
  cases n with
  | anonymous => exact absurd hr.1 hp
  | str pre str =>
    obtain ⟨_, q, sv, hh⟩ := hr
    simpa using block_get s _ p _ 1 (by simp) ⟨h, hh, hm⟩
  | num pre k =>
    obtain ⟨_, q, kv, hh⟩ := hr
    simpa using block_get s _ p _ 1 (by simp) ⟨h, hh, hm⟩

open Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString ConPanqueque.Logic in
/-- con-leche's `Hashable Name` (`hashData`) in Pancake: `0` is `anonymous`
(hash 1723), otherwise the cached hash at offset 8. -/
def nameHashBody : ProgHOL 64 :=
  .ite (.cmp .equal (.var .local (ofString "n")) (.const 0))
    (.return (.const 1723))
    (.return (.load .one (.op .add [.var .local (ofString "n"), .const 8])))

open Flapjack.Pancake.PanLang Flapjack.Basis.Pure.MlString ConPanqueque.Logic in
theorem nameHashBody_spec {σ : Type} (s : PanSemStateFiniteExact 64 σ) (p : BitVec 64) (n : ConLeche.Name)
    (hn : s.locals.lookup (ofString "n") = some (.val (.word p))) (hs : Sat s (NameRep p n)) :
    (evaluateHOLFiniteState s nameHashBody).1 = some (.returned (.val (.word n.hashData.toBitVec))) := by
  unfold nameHashBody
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  by_cases hp : p = 0
  · subst hp
    obtain ⟨h, hr, _⟩ := hs
    have : n = .anonymous := by
      cases n with
      | anonymous => rfl
      | str => exact absurd rfl hr.1
      | num => exact absurd rfl hr.1
    subst this
    simp [evalHOLFinite, evalHOLExact, hn, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
    simp [shapeOfHOLExact, ConLeche.Name.hashData]
  · obtain ⟨hd, hv⟩ := nameRep_hash s p n hs hp
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

end ConPanqueque.Rep
