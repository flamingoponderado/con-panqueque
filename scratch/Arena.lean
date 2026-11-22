import ConPanqueque.Rep
open Flapjack Flapjack.PanSemStateFiniteExact ConPanqueque.Sep

namespace ConPanqueque.Rep

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
theorem nameHashBody_spec' {σ : Type} (s : PanSemStateFiniteExact 64 σ) (p : BitVec 64) (n : ConLeche.Name)
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

end ConPanqueque.Rep
