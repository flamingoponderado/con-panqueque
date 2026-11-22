import ConPanqueque.Table
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Logic ConPanqueque.Table

namespace ConPanqueque.Table

theorem dJ : nJ ≠ nT ∧ nJ ≠ nK ∧ nJ ≠ nL ∧ nJ ≠ nR ∧ nJ ≠ nG := by decide
theorem dG : nG ≠ nT ∧ nG ≠ nK ∧ nG ≠ nL ∧ nG ≠ nR ∧ nG ≠ nJ := by decide
theorem dR : nR ≠ nT ∧ nR ≠ nK ∧ nR ≠ nL ∧ nR ≠ nJ ∧ nR ≠ nG := by decide

/-- One step of the scan, in its three cases. -/
theorem scanBody_step {σ : Type} (u : PanSemStateFiniteExact 64 σ) (t k : BitVec 64)
    (slots : List (BitVec 64 × BitVec 64)) (R : Assn) (i : Nat) (hn : 16 * slots.length < 2 ^ 64)
    (hi : i ≤ slots.length) (hs : Sat u (TableAt t slots ∗ R))
    (lt : u.locals.lookup nT = some (.val (.word t))) (lk : u.locals.lookup nK = some (.val (.word k)))
    (ll : u.locals.lookup nL = some (.val (.word (BitVec.ofNat 64 (16 * slots.length)))))
    (lj : u.locals.lookup nJ = some (.val (.word (BitVec.ofNat 64 (16 * i)))))
    (lr : ∃ r0, u.locals.lookup nR = some (.val (.word r0)))
    (lg : u.locals.lookup nG = some (.val (.word 1))) :
    (i = slots.length → evaluateHOLFiniteState u scanBody =
      (none, setKvarHOLFinite .local nG (.val (.word 0)) u)) ∧
    (∀ (h : i < slots.length), slots[i].1 = k → evaluateHOLFiniteState u scanBody =
      (none, setKvarHOLFinite .local nG (.val (.word 0)) (setKvarHOLFinite .local nR (.val (.word slots[i].2)) u))) ∧
    (∀ (h : i < slots.length), slots[i].1 ≠ k → evaluateHOLFiniteState u scanBody =
      (none, setKvarHOLFinite .local nJ (.val (.word (BitVec.ofNat 64 (16 * (i + 1))))) u)) := by
  obtain ⟨r0, lr⟩ := lr
  have hend : (BitVec.ofNat 64 (16 * i) = BitVec.ofNat 64 (16 * slots.length)) ↔ i = slots.length := by
    constructor
    · intro e; have := congrArg BitVec.toNat e; simp at this; omega
    · intro e; rw [e]
  refine ⟨fun he => ?_, fun h hk => ?_, fun h hk => ?_⟩
  · unfold scanBody
    rw [ite_word u _ _ _ 1 (by simp [evalHOLExact, vv, lj, ll, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, he])]
    rw [if_pos (by decide : (1 : BitVec 64) ≠ 0)]
    exact assign_ok u .local nG _ _ (by simp [evalHOLExact])
      (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, lg, shapeOfHOLExact, shapeEqHOL])
  · obtain ⟨⟨dk, mk⟩, ⟨dv, mv⟩⟩ := slot_read u t slots R hs i h
    have ne : ¬ i = slots.length := by omega
    unfold scanBody
    rw [ite_word u _ _ _ 0 (by simp [evalHOLExact, vv, lj, ll, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hend, ne])]
    simp only [ne_eq, not_true_eq_false, ite_false]
    rw [ite_word u _ _ _ 1 (by
      simp [evalHOLExact, evalListHOLExact, vv, lt, lj, lk, wordOpHOL, wordOp, valueIsWord, valueWord,
        memLoadHOLExact, dk, mk, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hk])]
    rw [if_pos (by decide : (1 : BitVec 64) ≠ 0)]
    let u1 := setKvarHOLFinite .local nR (.val (.word slots[i].2)) u
    have e1 : evaluateHOLFiniteState u (.assign .local nR (.load .one (.op .add [vv nT, vv nJ, .const 8]))) =
        (none, u1) := by
      apply assign_ok
      · rw [eval_load_word u _ (t + BitVec.ofNat 64 (16 * i) + 8) (by simp [evalHOLExact, evalListHOLExact, vv, lt, lj,
          wordOpHOL, wordOp, valueIsWord, valueWord, BitVec.add_assoc]) dv, mv]
      · simp [isValidValueHOLFinite, lookupKvarHOLFinite, lr, shapeOfHOLExact, shapeEqHOL]
    rw [seq_normal _ e1]
    exact assign_ok u1 .local nG _ _ (by simp [evalHOLExact])
      (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, u1, setKvarHOLFinite, setVarHOLFinite, FUPDATE, dR.2.2.2.2,
        lg, shapeOfHOLExact, shapeEqHOL])
  · obtain ⟨⟨dk, mk⟩, _⟩ := slot_read u t slots R hs i h
    have ne : ¬ i = slots.length := by omega
    unfold scanBody
    rw [ite_word u _ _ _ 0 (by simp [evalHOLExact, vv, lj, ll, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hend, ne])]
    simp only [ne_eq, not_true_eq_false, ite_false]
    rw [ite_word u _ _ _ 0 (by
      simp [evalHOLExact, evalListHOLExact, vv, lt, lj, lk, wordOpHOL, wordOp, valueIsWord, valueWord,
        memLoadHOLExact, dk, mk, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hk])]
    simp only [ne_eq, not_true_eq_false, ite_false]
    apply assign_ok
    · simp [evalHOLExact, evalListHOLExact, vv, lj, wordOpHOL, wordOp, valueIsWord, valueWord]
      apply BitVec.eq_of_toNat_eq; simp; omega
    · simp [isValidValueHOLFinite, lookupKvarHOLFinite, lj, shapeOfHOLExact, shapeEqHOL]

end ConPanqueque.Table
