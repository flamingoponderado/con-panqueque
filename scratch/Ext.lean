import ConPanqueque.Rep
import ConPanqueque.Alloc
open Flapjack Flapjack.PanSemStateFiniteExact ConPanqueque.Sep ConPanqueque.Rep

namespace ConPanqueque.Rep

/-- The arena `h` with the cell `a ↦ w` added. -/
def ext (h : Heap) (a : BitVec 64) (w : HolWordLab 64) : Heap :=
  fun c => if c = a then some w else h c

theorem sub_ext {h : Heap} {a : BitVec 64} (w : HolWordLab 64) (ha : h a = none) : Sub h (ext h a w) := by
  intro c v hc
  by_cases e : c = a
  · subst e; simp [ha] at hc
  · simp [ext, e, hc]

/-- A store to an address outside the arena keeps the arena in memory and adds the cell. -/
theorem inMem_store {σ : Type} {s : PanSemStateFiniteExact 64 σ} {h : Heap} {a : BitVec 64}
    (w : HolWordLab 64) (hm : InMem s h) (ha : h a = none) (hd : s.memaddrs a) :
    InMem { s with memory := fun c => if c = a then w else s.memory c } (ext h a w) := by
  intro c v hc
  by_cases e : c = a
  · subst e; simp [ext] at hc; subst hc; exact ⟨hd, by simp⟩
  · simp [ext, e] at hc
    obtain ⟨h1, h2⟩ := hm c v hc
    exact ⟨h1, by simp [e, h2]⟩

/-- The arena invariant: the arena is in memory, below the heap pointer `hp`, and
`[hp, @top)` is free. -/
def ArenaInv {σ : Type} (s : PanSemStateFiniteExact 64 σ) (h : Heap) (hp : BitVec 64) : Prop :=
  InMem s h ∧ ConPanqueque.Alloc.Free s hp ∧ ∀ a w, h a = some w → a < hp

/-- Addresses at or above `hp` are outside the arena. -/
theorem arena_fresh {σ : Type} {s : PanSemStateFiniteExact 64 σ} {h : Heap} {hp a : BitVec 64}
    (hi : ArenaInv s h hp) (ha : hp ≤ a) : h a = none := by
  cases e : h a with
  | none => rfl
  | some w => have := hi.2.2 a w e; exact absurd ha (by bv_omega)

end ConPanqueque.Rep
