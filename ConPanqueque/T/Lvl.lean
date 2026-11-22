import ConPanqueque.T.NameEq
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Level trees

The twin runs con-leche's level algorithms on trees read back from the arena. Pancake represents a
tree by a word: an arena handle (below `2^32`) reading back to it, or the address of a heap block
`[tag, children…]` (for the trees the algorithms build). Name leaves are name handles.
-/

namespace ConPanqueque.T

variable {σ : Type}

/-- The tree `l` at word `w`, for the heap base `HB`, image `H` and level store `ls`. -/
def LRep (HB : BitVec 64) (H : List (BitVec 64)) (ls : LStore) (w : BitVec 64) : ConLeche.Level → Prop
  | .zero => (∃ (h : LIdx) (f : Nat), w = Enc.idxW h ∧ denoteLAux ls f h = some .zero) ∨
      ∃ o, w = HB + BitVec.ofNat 64 (8 * o) ∧ H[o]? = some 0
  | .succ u => (∃ (h : LIdx) (f : Nat), w = Enc.idxW h ∧ denoteLAux ls f h = some (.succ u)) ∨
      ∃ o wu, w = HB + BitVec.ofNat 64 (8 * o) ∧ H[o]? = some 1 ∧ H[o + 1]? = some wu ∧ LRep HB H ls wu u
  | .max u v => (∃ (h : LIdx) (f : Nat), w = Enc.idxW h ∧ denoteLAux ls f h = some (.max u v)) ∨
      ∃ o wu wv, w = HB + BitVec.ofNat 64 (8 * o) ∧ H[o]? = some 2 ∧ H[o + 1]? = some wu ∧ H[o + 2]? = some wv ∧
        LRep HB H ls wu u ∧ LRep HB H ls wv v
  | .imax u v => (∃ (h : LIdx) (f : Nat), w = Enc.idxW h ∧ denoteLAux ls f h = some (.imax u v)) ∨
      ∃ o wu wv, w = HB + BitVec.ofNat 64 (8 * o) ∧ H[o]? = some 3 ∧ H[o + 1]? = some wu ∧ H[o + 2]? = some wv ∧
        LRep HB H ls wu u ∧ LRep HB H ls wv v
  | .param n => (∃ (h : LIdx) (f : Nat), w = Enc.idxW h ∧ denoteLAux ls f h = some (.param n)) ∨
      ∃ (o : Nat) (nh : NIdx) (f : Nat), w = HB + BitVec.ofNat 64 (8 * o) ∧ H[o]? = some 4 ∧ H[o + 1]? = some (Enc.idxW nh) ∧
        denoteNAux ls.ns f nh = some n

theorem getElem?_prefix {H H' : List (BitVec 64)} (hp : H <+: H') {i : Nat} {x : BitVec 64}
    (h : H[i]? = some x) : H'[i]? = some x := by
  obtain ⟨r, rfl⟩ := hp
  rw [List.getElem?_append_left (by
    rcases Nat.lt_or_ge i H.length with hl | hl
    · exact hl
    · rw [List.getElem?_eq_none hl] at h; simp at h)]
  exact h

theorem lrep_mono {HB : BitVec 64} {H H' : List (BitVec 64)} {ls : LStore} (hp : H <+: H') :
    ∀ (l : ConLeche.Level) (w : BitVec 64), LRep HB H ls w l → LRep HB H' ls w l
  | .zero, w, h => by
    rcases h with h | ⟨o, h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨o, h1, getElem?_prefix hp h2⟩
  | .succ u, w, h => by
    rcases h with h | ⟨o, wu, h1, h2, h3, h4⟩
    · exact Or.inl h
    · exact Or.inr ⟨o, wu, h1, getElem?_prefix hp h2, getElem?_prefix hp h3, lrep_mono hp u wu h4⟩
  | .max u v, w, h => by
    rcases h with h | ⟨o, wu, wv, h1, h2, h3, h4, h5, h6⟩
    · exact Or.inl h
    · exact Or.inr ⟨o, wu, wv, h1, getElem?_prefix hp h2, getElem?_prefix hp h3, getElem?_prefix hp h4,
        lrep_mono hp u wu h5, lrep_mono hp v wv h6⟩
  | .imax u v, w, h => by
    rcases h with h | ⟨o, wu, wv, h1, h2, h3, h4, h5, h6⟩
    · exact Or.inl h
    · exact Or.inr ⟨o, wu, wv, h1, getElem?_prefix hp h2, getElem?_prefix hp h3, getElem?_prefix hp h4,
        lrep_mono hp u wu h5, lrep_mono hp v wv h6⟩
  | .param n, w, h => by
    rcases h with h | ⟨o, nh, f, h1, h2, h3, h4⟩
    · exact Or.inl h
    · exact Or.inr ⟨o, nh, f, h1, getElem?_prefix hp h2, getElem?_prefix hp h3, h4⟩

end ConPanqueque.T
