import ConPanqueque.Logic.Basic
open Flapjack Flapjack.PanSemStateFiniteExact

/-!
# Separation logic over Pancake memory

Heap fragments are partial maps from addresses to words; `Sat s P` says part of
the memory domain of `s` satisfies `P`. Data-structure predicates (blocks,
lists, expression nodes) are built from `↦` and `∗` (PLAN.md, "Correctness").
-/

namespace ConPanqueque.Sep

/-- A heap fragment: some addresses, each holding a word. -/
abbrev Heap := BitVec 64 → Option (HolWordLab 64)

/-- An assertion on heap fragments. -/
abbrev Assn := Heap → Prop

def emp : Assn := fun h => ∀ a, h a = none

/-- `a ↦ w`: exactly the address `a`, holding `w`. -/
def pts (a : BitVec 64) (w : HolWordLab 64) : Assn :=
  fun h => h a = some w ∧ ∀ b, b ≠ a → h b = none

def Disj (h₁ h₂ : Heap) : Prop := ∀ a, h₁ a = none ∨ h₂ a = none

def union (h₁ h₂ : Heap) : Heap := fun a => (h₁ a).orElse fun _ => h₂ a

/-- Separating conjunction. -/
def sep (P Q : Assn) : Assn :=
  fun h => ∃ h₁ h₂, Disj h₁ h₂ ∧ h = union h₁ h₂ ∧ P h₁ ∧ Q h₂

infixr:35 " ∗ " => sep
infix:50 " ↦ " => pts

/-- A state satisfies `P` when part of its memory domain does: the fragment's
addresses are in `memaddrs` and hold the fragment's words. -/
def Sat {σ : Type} (s : PanSemStateFiniteExact 64 σ) (P : Assn) : Prop :=
  ∃ h, P h ∧ ∀ a w, h a = some w → s.memaddrs a ∧ s.memory a = w

/-- Frame rule for a one-word store: from `a ↦ _ ∗ R`, the store gives `a ↦ w ∗ R`. -/
theorem store_frame {σ : Type} (s : PanSemStateFiniteExact 64 σ) (a : BitVec 64)
    (old w : HolWordLab 64) (R : Assn) (hs : Sat s ((a ↦ old) ∗ R)) :
    s.memaddrs a ∧
    Sat { s with memory := fun c => if c = a then w else s.memory c } ((a ↦ w) ∗ R) := by
  obtain ⟨h, ⟨h₁, h₂, hd, rfl, ⟨ha, hn⟩, hR⟩, hm⟩ := hs
  have hdom : s.memaddrs a := (hm a old (by simp [union, ha])).1
  refine ⟨hdom, fun c => if c = a then some w else h₁ c |>.orElse fun _ => h₂ c, ?_, ?_⟩
  · refine ⟨fun c => if c = a then some w else none, h₂, ?_, ?_, ⟨by simp, fun b hb => by simp [hb]⟩, hR⟩
    · intro c; by_cases hc : c = a
      · subst hc; right; rcases hd c with h' | h'
        · simp [ha] at h'
        · exact h'
      · left; simp [hc]
    · funext c; by_cases hc : c = a
      · simp [union, hc]
      · simp [union, hc, hn c hc]
  · intro c v hv
    by_cases hc : c = a
    · subst hc; simp at hv; exact ⟨hdom, by simp [hv]⟩
    · simp [hc] at hv
      have := hm c v (by simpa [union] using hv)
      exact ⟨this.1, by simp [hc, this.2]⟩

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
