import ConPanqueque.Rep
open Flapjack Flapjack.PanSemStateFiniteExact ConPanqueque.Sep ConPanqueque.Rep

theorem sep_assoc_rev (P Q R : Assn) (h : Heap) : (P ∗ (Q ∗ R)) h → ((P ∗ Q) ∗ R) h := by
  intro hh
  have a1 := sep_comm _ _ h hh
  have a2 := sep_assoc _ _ _ h a1
  have a3 := sep_comm _ _ h a2
  have a4 := sep_assoc _ _ _ h a3
  exact sep_comm _ _ h a4

/-- Frame rule for a store into word `j` of a block. -/
theorem block_set {σ : Type} :
    ∀ (ws : List (HolWordLab 64)) (p : BitVec 64) (R : Assn) (j : Nat) (hj : j < ws.length)
      (s : PanSemStateFiniteExact 64 σ) (w : HolWordLab 64),
      Sat s (block p ws ∗ R) →
      Sat { s with memory := fun c => if c = p + BitVec.ofNat 64 (8 * j) then w else s.memory c }
        (block p (ws.set j w) ∗ R)
  | [], _, _, j, hj, _, _, _ => absurd hj (by simp)
  | x :: xs, p, R, 0, _, s, w, hs => by
    simp only [block, List.set_cons_zero] at hs ⊢
    have h1 := sat_mono (fun h hh => sep_assoc _ _ _ h hh) hs
    obtain ⟨_, h2⟩ := store_frame s p x w _ h1
    simpa using sat_mono (fun h hh => sep_assoc_rev _ _ _ h hh) h2
  | x :: xs, p, R, j + 1, hj, s, w, hs => by
    simp only [block, List.set_cons_succ] at hs ⊢
    have h1 : Sat s (block (p + 8) xs ∗ (R ∗ (p ↦ x))) := sat_mono (fun h hh => by
      have := sep_assoc _ _ _ h hh
      have := sep_comm _ _ h this
      exact sep_assoc _ _ _ h this) hs
    have ih := block_set xs (p + 8) (R ∗ (p ↦ x)) j (by simpa using hj) s w h1
    have he : p + 8 + BitVec.ofNat 64 (8 * j) = p + BitVec.ofNat 64 (8 * (j + 1)) := by
      rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
    rw [he] at ih
    exact sat_mono (fun h hh => by
      have := sep_assoc_rev _ _ _ h hh
      have := sep_comm _ _ h this
      exact sep_assoc_rev _ _ _ h this) ih
