import ConPanqueque.Table
import ConPanqueque.StateHeap
open Flapjack Flapjack.PanSemStateFiniteExact
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Table ConPanqueque.StateHeap

/-!
# Tables below the arena

A memo table lives below the arena's low end `lo`, so allocating functions
(which keep memory below `lo`, `Grows.low`) keep it: `sat_transfer` moves a
separation-logic fact whose footprint lies below `lo` across such a call, and
`tableAt_dom` bounds a table's footprint.
-/

namespace ConPanqueque.LowTable

theorem sat_transfer {σ : Type} {s s' : PanSemStateFiniteExact 64 σ} {P : Assn} {lo : BitVec 64}
    (hs : Sat s P) (hdom : ∀ h, P h → ∀ a w, h a = some w → a < lo)
    (hm : ∀ a, a < lo → s'.memory a = s.memory a) (hd : s'.memaddrs = s.memaddrs) : Sat s' P := by
  obtain ⟨h, hp, hh⟩ := hs
  exact ⟨h, hp, fun a w ha => by
    obtain ⟨d, m⟩ := hh a w ha
    have := hdom h hp a w ha
    exact ⟨by rw [hd]; exact d, by rw [hm a this]; exact m⟩⟩

theorem block_dom : ∀ (ws : List (HolWordLab 64)) (a : BitVec 64) (h : Heap), block a ws h →
    ∀ b w, h b = some w → ∃ j, j < ws.length ∧ b = a + BitVec.ofNat 64 (8 * j)
  | [], a, h, hb, b, w, hw => by simp [block, emp] at hb; rw [hb b] at hw; cases hw
  | w0 :: ws, a, h, hb, b, w, hw => by
    obtain ⟨h1, h2, hdj, rfl, hp, hr⟩ := hb
    simp only [union] at hw
    cases e : h1 b with
    | some x =>
      have : b = a := Classical.byContradiction fun hne => by rw [hp.2 b hne] at e; cases e
      exact ⟨0, by simp, by simp [this]⟩
    | none =>
      rw [e] at hw; simp at hw
      obtain ⟨j, hj, hb'⟩ := block_dom ws (a + 8) h2 hr b w hw
      refine ⟨j + 1, by simp; omega, ?_⟩
      rw [hb']
      apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_add]; omega

theorem flat_len : ∀ slots : List (BitVec 64 × BitVec 64),
    (slots.flatMap fun (k, v) => [HolWordLab.word k, HolWordLab.word v]).length = 2 * slots.length
  | [] => by simp
  | s :: ss => by simp [List.flatMap_cons, flat_len ss]; omega

theorem tableAt_dom (tb : BitVec 64) (slots : List (BitVec 64 × BitVec 64)) (lo : BitVec 64)
    (hfit : tb.toNat + 16 * slots.length ≤ lo.toNat) :
    ∀ h, (TableAt tb slots ∗ emp) h → ∀ a w, h a = some w → a < lo := by
  intro h ⟨h1, h2, _, hu, ht, he⟩ a w ha
  rw [hu] at ha
  simp only [union] at ha
  cases e : h1 a with
  | some x =>
    obtain ⟨j, hj, rfl⟩ := block_dom _ tb h1 ht a x e
    have hl := flat_len slots
    rw [hl] at hj
    have hlo := lo.isLt
    have h8 : (BitVec.ofNat 64 (8 * j)).toNat = 8 * j := by simp; omega
    rw [BitVec.lt_def, BitVec.toNat_add, h8, Nat.mod_eq_of_lt (by omega)]; omega
  | none => rw [e] at ha; simp at ha; rw [he a] at ha; cases ha

end ConPanqueque.LowTable
