import ConPanqueque.Alloc
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The free region: `[h, @top)` is in the memory domain, and `h ≤ @top`. -/
def Free {σ : Type} (s : PanSemStateFiniteExact 64 σ) (h : BitVec 64) : Prop :=
  h ≤ s.topAddr ∧ ∀ a : BitVec 64, h ≤ a → a < s.topAddr → s.memaddrs a

/-- A successful allocation of `n` bytes at `h`: the block `[h, h + n)` is in the
memory domain (and does not wrap around), and `[h + n, @top)` is free. -/
theorem alloc_fresh {σ : Type} (s : PanSemStateFiniteExact 64 σ) (h n : BitVec 64)
    (hf : Free s h) (hfit : ¬ s.topAddr - h < n) :
    h.toNat + n.toNat ≤ s.topAddr.toNat ∧
    (∀ a : BitVec 64, h ≤ a → a < h + n → s.memaddrs a) ∧ Free s (h + n) := by
  obtain ⟨hle, hdom⟩ := hf
  have hsum : h.toNat + n.toNat ≤ s.topAddr.toNat := by bv_omega
  refine ⟨hsum, fun a h1 h2 => hdom a h1 (by bv_omega), by bv_omega, fun a h1 h2 => hdom a (by bv_omega) h2⟩
