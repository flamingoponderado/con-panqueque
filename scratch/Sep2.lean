import ConPanqueque.Logic.Sep
open Flapjack Flapjack.PanSemStateFiniteExact
namespace ConPanqueque.Sep

/-- A word read through `a ↦ w ∗ R`. -/
theorem load_frame {σ : Type} (s : PanSemStateFiniteExact 64 σ) (a : BitVec 64) (w : HolWordLab 64)
    (R : Assn) (hs : Sat s ((a ↦ w) ∗ R)) : s.memaddrs a ∧ s.memory a = w := by
  obtain ⟨h, ⟨h₁, h₂, _, rfl, ⟨ha, _⟩, _⟩, hm⟩ := hs
  exact hm a w (by simp [union, ha])

/-- Consecutive words from `a`. -/
def block : BitVec 64 → List (HolWordLab 64) → Assn
  | _, [] => emp
  | a, w :: ws => (a ↦ w) ∗ block (a + 8) ws

/-- A linked list of words: `0` is the empty list, a cons cell is a two-word block
(head, next). -/
def ListRep : BitVec 64 → List (BitVec 64) → Assn
  | p, [] => fun h => p = 0 ∧ emp h
  | p, x :: xs => fun h => p ≠ 0 ∧ ∃ q, (block p [.word x, .word q] ∗ ListRep q xs) h

end ConPanqueque.Sep
