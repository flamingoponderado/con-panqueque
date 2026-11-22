import ConPanqueque.Table
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Logic ConPanqueque.Table ConPanqueque.Rep

namespace ConPanqueque.Table

/-- The insertion loop: on success `ok = 1` and memory holds `insSlots k v slots`;
if the table is full, `ok = 0` and memory is unchanged. -/
theorem insLoop_spec {σ : Type} (s : PanSemStateFiniteExact 64 σ) (t k v : BitVec 64)
    (slots : List (BitVec 64 × BitVec 64)) (R : Assn) (hn : 16 * slots.length < 2 ^ 64)
    (hs : Sat s (TableAt t slots ∗ R))
    (lt : s.locals.lookup nT = some (.val (.word t))) (lk : s.locals.lookup nK = some (.val (.word k)))
    (lv : s.locals.lookup nV = some (.val (.word v)))
    (ll : s.locals.lookup nL = some (.val (.word (BitVec.ofNat 64 (16 * slots.length)))))
    (lj : s.locals.lookup nJ = some (.val (.word 0)))
    (lo : s.locals.lookup nO = some (.val (.word 0)))
    (lg : s.locals.lookup nG = some (.val (.word 1)))
    (hclk : slots.length + 1 ≤ s.clock) :
    ∃ s', evaluateHOLFiniteState s insLoop = (none, s') ∧ s'.memaddrs = s.memaddrs ∧
      ((s'.locals.lookup nO = some (.val (.word 1)) ∧
          ∃ sl', insSlots k v slots = some sl' ∧ Sat s' (TableAt t sl' ∗ R)) ∨
       (s'.locals.lookup nO = some (.val (.word 0)) ∧ insSlots k v slots = none ∧ s'.memory = s.memory)) := by
  let n := slots.length
  let I : PanSemStateFiniteExact 64 σ → Prop := fun u =>
    u.memaddrs = s.memaddrs ∧
    u.locals.lookup nT = some (.val (.word t)) ∧ u.locals.lookup nK = some (.val (.word k)) ∧
    u.locals.lookup nV = some (.val (.word v)) ∧
    u.locals.lookup nL = some (.val (.word (BitVec.ofNat 64 (16 * n)))) ∧
    ∃ i, i ≤ n ∧ u.locals.lookup nJ = some (.val (.word (BitVec.ofNat 64 (16 * i)))) ∧
      ((u.locals.lookup nG = some (.val (.word 1)) ∧ u.locals.lookup nO = some (.val (.word 0)) ∧
          u.memory = s.memory ∧ (∀ m (hm : m < n), m < i → slots[m].1 ≠ k ∧ slots[m].1 ≠ 0) ∧
          n + 1 - i ≤ u.clock) ∨
       (u.locals.lookup nG = some (.val (.word 0)) ∧ u.locals.lookup nO = some (.val (.word 0)) ∧
          insSlots k v slots = none ∧ u.memory = s.memory) ∨
       (u.locals.lookup nG = some (.val (.word 0)) ∧ u.locals.lookup nO = some (.val (.word 1)) ∧
          ∃ sl', insSlots k v slots = some sl' ∧ Sat u (TableAt t sl' ∗ R)))
  let Q : PanSemStateFiniteExact 64 σ → Prop := fun u =>
    u.memaddrs = s.memaddrs ∧
    ((u.locals.lookup nO = some (.val (.word 1)) ∧ ∃ sl', insSlots k v slots = some sl' ∧ Sat u (TableAt t sl' ∗ R)) ∨
     (u.locals.lookup nO = some (.val (.word 0)) ∧ insSlots k v slots = none ∧ u.memory = s.memory))
  let m : PanSemStateFiniteExact 64 σ → Nat := fun u =>
    if wv u nG = 1 then n + 1 - (wv u nJ).toNat / 16 else 0
  have hI0 : I s := ⟨rfl, lt, lk, lv, ll, 0, Nat.zero_le _, by simpa using lj,
    .inl ⟨lg, lo, rfl, fun m _ hm => absurd hm (by omega), by omega⟩⟩
  have key := while_rule (vv nG) insBody I m Q ?_ s hI0
  · obtain ⟨s', ev, hq1, hq2⟩ := key
    exact ⟨s', ev, hq1, hq2⟩
  rintro u ⟨hd, ut, uk, uv, ul, i, hi, uj, hcase⟩
  have wj : (wv u nJ).toNat / 16 = i := by
    simp [wv, uj]; rw [Nat.mod_eq_of_lt (by omega)]; omega
  rcases hcase with ⟨ug, uo, hm, hnot, uclk⟩ | ⟨ug, uo, hnone, hm⟩ | ⟨ug, uo, sl', hsl, hsat⟩
  · refine ⟨1, by simp [evalHOLFinite, evalHOLExact, vv, ug], fun h => absurd h (by decide), fun _ => ?_⟩
    have g1 : wv u nG = 1 := by simp [wv, ug]
    have mu : m u = n + 1 - i := by simp only [m]; rw [if_pos g1, wj]
    refine ⟨by rw [mu]; exact uclk, by rw [mu]; omega, ?_⟩
    let u0 := decClockHOLFinite u
    have hsu0 : Sat u0 (TableAt t slots ∗ R) :=
      sat_of_eq (by simp [u0, decClockHOLFinite, hm]) (by simp [u0, decClockHOLFinite, hd]) hs
    have uc : u0.clock = u.clock - 1 := by simp [u0, decClockHOLFinite]
    obtain ⟨c1, c2, c3⟩ := insBody_step u0 t k v slots R i hn hi hsu0 (by simpa [u0, decClockHOLFinite] using ut)
      (by simpa [u0, decClockHOLFinite] using uk) (by simpa [u0, decClockHOLFinite] using uv)
      (by simpa [u0, decClockHOLFinite] using ul) (by simpa [u0, decClockHOLFinite] using uj)
      (by simpa [u0, decClockHOLFinite] using uo) (by simpa [u0, decClockHOLFinite] using ug)
    by_cases hin : i = n
    · -- full
      have hnone : insSlots k v slots = none := insSlots_none k v slots (fun m' hm' => hnot m' hm' (by omega))
      refine ⟨_, c1 hin, ⟨by simp [setKvarHOLFinite, setVarHOLFinite, u0, decClockHOLFinite, hd], ?_, ?_, ?_, ?_, i, hi,
        ?_, .inr (.inl ⟨?_, ?_, hnone, by simp [setKvarHOLFinite, setVarHOLFinite, u0, decClockHOLFinite, hm]⟩)⟩, ?_⟩
      · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dG.1)]; simpa [u0, decClockHOLFinite] using ut
      · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dG.2.1)]; simpa [u0, decClockHOLFinite] using uk
      · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dG'.1)]; simpa [u0, decClockHOLFinite] using uv
      · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dG.2.2.1)]; simpa [u0, decClockHOLFinite] using ul
      · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ dJ.2.2.2.2]; simpa [u0, decClockHOLFinite] using uj
      · simp [setKvarHOLFinite]
      · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dG'.2)]; simpa [u0, decClockHOLFinite] using uo
      · have : m (setKvarHOLFinite .local nG (.val (.word 0)) u0) = 0 := by simp [m, wv, setKvarHOLFinite]
        rw [this, mu]; omega
    · have hlt : i < n := by omega
      by_cases hk : slots[i].1 = k ∨ slots[i].1 = 0
      · -- write slot i
        obtain ⟨u2, hsat2, hl2, hd2, hc2, ev⟩ := c2 hlt hk
        have hins : insSlots k v slots = some (slots.set i (k, v)) :=
          insSlots_at k v slots i hlt (fun m' hm' hmi => hnot m' hm' hmi) hk
        have lk2 : ∀ x, u2.locals.lookup x = u0.locals.lookup x := by intro x; rw [hl2]
        refine ⟨_, ev, ⟨by simp [setKvarHOLFinite, setVarHOLFinite, hd2, u0, decClockHOLFinite, hd], ?_, ?_, ?_, ?_, i, hi,
          ?_, .inr (.inr ⟨?_, ?_, _, hins, ?_⟩)⟩, ?_⟩
        · simp only [setKvarHOLFinite]
          rw [lookup_setVar_other _ _ (Ne.symm dG.1), lookup_setVar_other _ _ (Ne.symm dO.1), lk2]
          simpa [u0, decClockHOLFinite] using ut
        · simp only [setKvarHOLFinite]
          rw [lookup_setVar_other _ _ (Ne.symm dG.2.1), lookup_setVar_other _ _ (Ne.symm dO.2.1), lk2]
          simpa [u0, decClockHOLFinite] using uk
        · simp only [setKvarHOLFinite]
          rw [lookup_setVar_other _ _ (Ne.symm dG'.1), lookup_setVar_other _ _ (Ne.symm dO.2.2.2.2.2), lk2]
          simpa [u0, decClockHOLFinite] using uv
        · simp only [setKvarHOLFinite]
          rw [lookup_setVar_other _ _ (Ne.symm dG.2.2.1), lookup_setVar_other _ _ (Ne.symm dO.2.2.1), lk2]
          simpa [u0, decClockHOLFinite] using ul
        · simp only [setKvarHOLFinite]
          rw [lookup_setVar_other _ _ dJ.2.2.2.2, lookup_setVar_other _ _ dJ'.2, lk2]
          simpa [u0, decClockHOLFinite] using uj
        · simp [setKvarHOLFinite]
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dG'.2)]; simp
        · exact sat_of_eq (by simp [setKvarHOLFinite, setVarHOLFinite]) (by simp [setKvarHOLFinite, setVarHOLFinite]) hsat2
        · have : m (setKvarHOLFinite .local nG (.val (.word 0)) (setKvarHOLFinite .local nO (.val (.word 1)) u2)) = 0 := by
            simp [m, wv, setKvarHOLFinite]
          rw [this, mu]; omega
      · -- next slot
        simp only [not_or] at hk
        refine ⟨_, c3 hlt hk.1 hk.2, ⟨by simp [setKvarHOLFinite, setVarHOLFinite, u0, decClockHOLFinite, hd], ?_, ?_, ?_, ?_,
          i + 1, by omega, ?_, .inl ⟨?_, ?_, by simp [setKvarHOLFinite, setVarHOLFinite, u0, decClockHOLFinite, hm], ?_, ?_⟩⟩, ?_⟩
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dJ.1)]; simpa [u0, decClockHOLFinite] using ut
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dJ.2.1)]; simpa [u0, decClockHOLFinite] using uk
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dJ'.1)]; simpa [u0, decClockHOLFinite] using uv
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dJ.2.2.1)]
          simpa [u0, decClockHOLFinite] using ul
        · simp [setKvarHOLFinite]
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ dG.2.2.2.2]; simpa [u0, decClockHOLFinite] using ug
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ dO.2.2.2.1]; simpa [u0, decClockHOLFinite] using uo
        · intro m' hm' hmi
          by_cases e : m' = i
          · subst e; exact hk
          · exact hnot m' hm' (by omega)
        · simp [setKvarHOLFinite, setVarHOLFinite, uc]; omega
        · have wj' : (wv (setKvarHOLFinite .local nJ (.val (.word (BitVec.ofNat 64 (16 * (i + 1))))) u0) nJ).toNat / 16
              = i + 1 := by
            simp [wv, setKvarHOLFinite]; rw [Nat.mod_eq_of_lt (by omega)]; omega
          have g1' : wv (setKvarHOLFinite .local nJ (.val (.word (BitVec.ofNat 64 (16 * (i + 1))))) u0) nG = 1 := by
            simp only [wv, setKvarHOLFinite]; rw [lookup_setVar_other _ _ dG.2.2.2.2]
            simp [u0, decClockHOLFinite, ug]
          have : m (setKvarHOLFinite .local nJ (.val (.word (BitVec.ofNat 64 (16 * (i + 1))))) u0) = n + 1 - (i + 1) := by
            simp only [m]; rw [if_pos g1', wj']
          rw [this, mu]; omega
  · refine ⟨0, by simp [evalHOLFinite, evalHOLExact, vv, ug], fun _ => ⟨hd, .inr ⟨uo, hnone, hm⟩⟩,
      fun h => absurd rfl h⟩
  · refine ⟨0, by simp [evalHOLFinite, evalHOLExact, vv, ug], fun _ => ⟨hd, .inl ⟨uo, sl', hsl, hsat⟩⟩,
      fun h => absurd rfl h⟩

end ConPanqueque.Table
