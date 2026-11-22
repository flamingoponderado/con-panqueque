import ConPanqueque.Table
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Logic ConPanqueque.Table

namespace ConPanqueque.Table

/-- A local's word value (`0` if absent). -/
def wv {σ : Type} (u : PanSemStateFiniteExact 64 σ) (n : MlS) : BitVec 64 :=
  match u.locals.lookup n with
  | some (.val (.word w)) => w
  | _ => 0

theorem sat_of_eq {σ : Type} {u v : PanSemStateFiniteExact 64 σ} {P : Assn}
    (hm : v.memory = u.memory) (hd : v.memaddrs = u.memaddrs) (hs : Sat u P) : Sat v P := by
  obtain ⟨h, hp, hh⟩ := hs; exact ⟨h, hp, fun a w ha => by rw [hm, hd]; exact hh a w ha⟩

/-- The lookup loop returns `find? slots k` (or `0`), memory unchanged. -/
theorem scanLoop_spec {σ : Type} (s : PanSemStateFiniteExact 64 σ) (t k : BitVec 64)
    (slots : List (BitVec 64 × BitVec 64)) (R : Assn) (hn : 16 * slots.length < 2 ^ 64)
    (hs : Sat s (TableAt t slots ∗ R))
    (lt : s.locals.lookup nT = some (.val (.word t))) (lk : s.locals.lookup nK = some (.val (.word k)))
    (ll : s.locals.lookup nL = some (.val (.word (BitVec.ofNat 64 (16 * slots.length)))))
    (lj : s.locals.lookup nJ = some (.val (.word 0)))
    (lr : s.locals.lookup nR = some (.val (.word 0)))
    (lg : s.locals.lookup nG = some (.val (.word 1)))
    (hclk : slots.length + 1 ≤ s.clock) :
    ∃ s', evaluateHOLFiniteState s scanLoop = (none, s') ∧
      s'.locals.lookup nR = some (.val (.word ((find? slots k).getD 0))) ∧ s'.memory = s.memory := by
  let n := slots.length
  let I : PanSemStateFiniteExact 64 σ → Prop := fun u =>
    u.memory = s.memory ∧ u.memaddrs = s.memaddrs ∧
    u.locals.lookup nT = some (.val (.word t)) ∧ u.locals.lookup nK = some (.val (.word k)) ∧
    u.locals.lookup nL = some (.val (.word (BitVec.ofNat 64 (16 * n)))) ∧
    ∃ i, i ≤ n ∧ u.locals.lookup nJ = some (.val (.word (BitVec.ofNat 64 (16 * i)))) ∧
      ((u.locals.lookup nG = some (.val (.word 1)) ∧ u.locals.lookup nR = some (.val (.word 0)) ∧
          (∀ m (hm : m < n), m < i → slots[m].1 ≠ k) ∧ n + 1 - i ≤ u.clock) ∨
       (u.locals.lookup nG = some (.val (.word 0)) ∧
          u.locals.lookup nR = some (.val (.word ((find? slots k).getD 0)))))
  let Q : PanSemStateFiniteExact 64 σ → Prop := fun u =>
    u.locals.lookup nR = some (.val (.word ((find? slots k).getD 0))) ∧ u.memory = s.memory
  let m : PanSemStateFiniteExact 64 σ → Nat := fun u =>
    if wv u nG = 1 then n + 1 - (wv u nJ).toNat / 16 else 0
  have hI0 : I s := ⟨rfl, rfl, lt, lk, ll, 0, Nat.zero_le _, by simpa using lj,
    .inl ⟨lg, lr, fun m _ hm => absurd hm (by omega), by omega⟩⟩
  refine while_rule (vv nG) scanBody I m Q ?_ s hI0
  rintro u ⟨hm, hd, ut, uk, ul, i, hi, uj, hcase⟩
  have hsu : Sat u (TableAt t slots ∗ R) := sat_of_eq hm hd hs
  have wj : (wv u nJ).toNat / 16 = i := by
    simp [wv, uj]; rw [Nat.mod_eq_of_lt (by omega)]; omega
  rcases hcase with ⟨ug, ur, hnot, uclk⟩ | ⟨ug, ur⟩
  · refine ⟨1, by simp [evalHOLFinite, evalHOLExact, vv, ug], fun h => absurd h (by decide), fun _ => ?_⟩
    have g1 : wv u nG = 1 := by simp [wv, ug]
    have mu : m u = n + 1 - i := by simp only [m]; rw [if_pos g1, wj]
    refine ⟨by rw [mu]; exact uclk, by rw [mu]; omega, ?_⟩
    let u0 := decClockHOLFinite u
    have hsu0 : Sat u0 (TableAt t slots ∗ R) := sat_of_eq (by simp [u0, decClockHOLFinite]) (by simp [u0, decClockHOLFinite]) hsu
    obtain ⟨c1, c2, c3⟩ := scanBody_step u0 t k slots R i hn hi hsu0 (by simpa [u0, decClockHOLFinite] using ut)
      (by simpa [u0, decClockHOLFinite] using uk) (by simpa [u0, decClockHOLFinite] using ul)
      (by simpa [u0, decClockHOLFinite] using uj) ⟨0, by simpa [u0, decClockHOLFinite] using ur⟩
      (by simpa [u0, decClockHOLFinite] using ug)
    have uc : u0.clock = u.clock - 1 := by simp [u0, decClockHOLFinite]
    by_cases hin : i = n
    · -- end of the table: not found
      have hres : (find? slots k).getD 0 = 0 := by
        rw [find?_none slots k (fun m hm => hnot m hm (by omega))]; rfl
      refine ⟨_, c1 hin, ⟨by simp [setKvarHOLFinite, setVarHOLFinite, u0, decClockHOLFinite, hm],
        by simp [setKvarHOLFinite, setVarHOLFinite, u0, decClockHOLFinite, hd], ?_, ?_, ?_, i, hi, ?_, .inr ⟨?_, ?_⟩⟩, ?_⟩
      · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dG.1)]; simpa [u0, decClockHOLFinite] using ut
      · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dG.2.1)]; simpa [u0, decClockHOLFinite] using uk
      · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dG.2.2.1)]; simpa [u0, decClockHOLFinite] using ul
      · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ dJ.2.2.2.2]; simpa [u0, decClockHOLFinite] using uj
      · simp [setKvarHOLFinite]
      · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dG.2.2.2.1), hres]
        simpa [u0, decClockHOLFinite] using ur
      · have : m (setKvarHOLFinite .local nG (.val (.word 0)) u0) = 0 := by simp [m, wv, setKvarHOLFinite]
        rw [this, mu]; omega
    · have hlt : i < n := by omega
      by_cases hk : slots[i].1 = k
      · -- found at slot i
        have hres : (find? slots k).getD 0 = slots[i].2 := by
          rw [find?_at slots k i hlt (fun m hm => hnot m (by omega) hm) hk]; rfl
        refine ⟨_, c2 hlt hk, ⟨by simp [setKvarHOLFinite, setVarHOLFinite, u0, decClockHOLFinite, hm],
          by simp [setKvarHOLFinite, setVarHOLFinite, u0, decClockHOLFinite, hd], ?_, ?_, ?_, i, hi, ?_, .inr ⟨?_, ?_⟩⟩, ?_⟩
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dG.1), lookup_setVar_other _ _ (Ne.symm dR.1)]
          simpa [u0, decClockHOLFinite] using ut
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dG.2.1), lookup_setVar_other _ _ (Ne.symm dR.2.1)]
          simpa [u0, decClockHOLFinite] using uk
        · simp only [setKvarHOLFinite]
          rw [lookup_setVar_other _ _ (Ne.symm dG.2.2.1), lookup_setVar_other _ _ (Ne.symm dR.2.2.1)]
          simpa [u0, decClockHOLFinite] using ul
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ dJ.2.2.2.2, lookup_setVar_other _ _ dJ.2.2.2.1]
          simpa [u0, decClockHOLFinite] using uj
        · simp [setKvarHOLFinite]
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dG.2.2.2.1), hres]; simp
        · have : m (setKvarHOLFinite .local nG (.val (.word 0))
              (setKvarHOLFinite .local nR (.val (.word slots[i].2)) u0)) = 0 := by simp [m, wv, setKvarHOLFinite]
          rw [this, mu]; omega
      · -- move to the next slot
        refine ⟨_, c3 hlt hk, ⟨by simp [setKvarHOLFinite, setVarHOLFinite, u0, decClockHOLFinite, hm],
          by simp [setKvarHOLFinite, setVarHOLFinite, u0, decClockHOLFinite, hd], ?_, ?_, ?_, i + 1, by omega, ?_,
          .inl ⟨?_, ?_, ?_, ?_⟩⟩, ?_⟩
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dJ.1)]; simpa [u0, decClockHOLFinite] using ut
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dJ.2.1)]; simpa [u0, decClockHOLFinite] using uk
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ (Ne.symm dJ.2.2.1)]
          simpa [u0, decClockHOLFinite] using ul
        · simp [setKvarHOLFinite]
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ dG.2.2.2.2]; simpa [u0, decClockHOLFinite] using ug
        · simp only [setKvarHOLFinite]; rw [lookup_setVar_other _ _ dR.2.2.2.1]; simpa [u0, decClockHOLFinite] using ur
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
  · refine ⟨0, by simp [evalHOLFinite, evalHOLExact, vv, ug], fun _ => ⟨ur, hm⟩, fun h => absurd rfl h⟩

end ConPanqueque.Table
