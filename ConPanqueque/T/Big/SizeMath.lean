import ConPanqueque.T.Big.Limbs
import ConRon.Arena

/-!
# `natSizeBytes` from the limb count

The twin's `natSizeBytes n = 8 * (n.log2 / 64 + 1)` is `8 * max(|limbs n|, 1)`: no bit logarithm is needed.
-/

namespace ConPanqueque.T.Big

open ConPanqueque.V.Enc

theorem limbs_length_log2 (n : Nat) (hn : n ≠ 0) : (limbs n).length = n.log2 / 64 + 1 := by
  have key : ∀ k, (limbs n).length ≤ k ↔ n.log2 / 64 + 1 ≤ k := by
    intro k
    rw [limbs_length_lt_iff, show B ^ k = 2 ^ (64 * k) by rw [show B = 2 ^ 64 from rfl, ← Nat.pow_mul],
      ← Nat.log2_lt hn]
    omega
  exact Nat.le_antisymm ((key _).mpr (Nat.le_refl _)) (by have := (key (limbs n).length).mp (Nat.le_refl _); omega)

theorem natSizeBytes_limbs (n : Nat) : ConRon.Arena.natSizeBytes n = 8 * max (limbs n).length 1 := by
  unfold ConRon.Arena.natSizeBytes
  by_cases hn : n = 0
  · subst hn; simp [limbs_zero, Nat.log2_zero]
  · rw [limbs_length_log2 n hn]; omega

end ConPanqueque.T.Big
