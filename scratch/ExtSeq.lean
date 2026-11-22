import ConPanqueque.Arena
open Flapjack ConPanqueque.Sep ConPanqueque.Rep

theorem extSeq_other (p : BitVec 64) : ∀ (vs : List (BitVec 64)) (i : Nat) (h : Heap) (a : BitVec 64),
    (∀ j, j < vs.length → a ≠ at8 p (i + j)) → extSeq h p vs i a = h a
  | [], _, _, _, _ => rfl
  | v :: vs, i, h, a, ha => by
    simp only [extSeq]
    rw [extSeq_other p vs (i + 1) _ a (fun j hj => by
      have := ha (j + 1) (by simp; omega); simpa [Nat.add_assoc, Nat.add_comm 1] using this)]
    have := ha 0 (by simp)
    simp only [ext]; split
    · exact absurd ‹_› (by simpa using this)
    · rfl

theorem extSeq_get (p : BitVec 64) : ∀ (vs : List (BitVec 64)) (i : Nat) (h : Heap) (j : Nat) (hj : j < vs.length),
    (∀ j k, j < vs.length → k < vs.length → j ≠ k → at8 p (i + j) ≠ at8 p (i + k)) →
    extSeq h p vs i (at8 p (i + j)) = some (.word vs[j])
  | [], _, _, _, hj, _ => absurd hj (by simp)
  | v :: vs, i, h, 0, _, hd => by
    simp only [extSeq]
    rw [extSeq_other p vs (i + 1) _ _ (fun j hj => by
      have := hd 0 (j + 1) (by simp) (by simp; omega) (by omega)
      simpa [Nat.add_assoc, Nat.add_comm 1] using this)]
    simp [ext]
  | v :: vs, i, h, j + 1, hj, hd => by
    simp only [extSeq]
    have := extSeq_get p vs (i + 1) (ext h (at8 p i) (.word v)) j (by simpa using hj)
      (fun a b ha hb hab => by
        have := hd (a + 1) (b + 1) (by simp; omega) (by simp; omega) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm 1] using this)
    simpa [Nat.add_assoc, Nat.add_comm 1] using this
