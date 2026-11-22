import ConPanqueque.Arena
open Flapjack Flapjack.PanSemStateFiniteExact ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Alloc

/-- Address facts for an `n`-word block at the heap pointer `p0`. -/
theorem blockN {σ : Type} {s : PanSemStateFiniteExact 64 σ} {h : Heap} {p0 : BitVec 64} (n : Nat)
    (hi : ArenaInv s h p0) (hfit : ¬ s.topAddr - p0 < BitVec.ofNat 64 (8 * n)) (hn : 8 * n < 2 ^ 64) :
    (∀ j, j < n → s.memaddrs (at8 p0 j) ∧ h (at8 p0 j) = none) ∧
    (∀ j k, j < n → k < n → j ≠ k → at8 p0 j ≠ at8 p0 k) ∧
    Free s (p0 + BitVec.ofNat 64 (8 * n)) ∧ p0.toNat + 8 * n ≤ s.topAddr.toNat := by
  obtain ⟨hsum, hdom, hfree⟩ := alloc_fresh s p0 _ hi.2.1 hfit
  have hb : p0.toNat + 8 * n ≤ s.topAddr.toNat := by
    have : (BitVec.ofNat 64 (8 * n)).toNat = 8 * n := by simp; omega
    omega
  have ht : s.topAddr.toNat < 2 ^ 64 := s.topAddr.isLt
  refine ⟨fun j hj => ⟨hdom _ ?_ ?_, arena_fresh hi ?_⟩, fun j k hj hk hjk => ?_, hfree, hb⟩
  · simp only [at8]; bv_omega
  · simp only [at8]; bv_omega
  · simp only [at8]; bv_omega
  · simp only [at8]; intro e; apply hjk; have := congrArg BitVec.toNat e; simp at this; omega
