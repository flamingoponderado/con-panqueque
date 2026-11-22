import ConPanqueque.Table
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Logic ConPanqueque.Table ConPanqueque.Rep

namespace ConPanqueque.Table

theorem dO : nO ≠ nT ∧ nO ≠ nK ∧ nO ≠ nL ∧ nO ≠ nJ ∧ nO ≠ nG ∧ nO ≠ nV := by decide
theorem dG' : nG ≠ nV ∧ nG ≠ nO := by decide
theorem dJ' : nJ ≠ nV ∧ nJ ≠ nO := by decide

theorem insBody_step {σ : Type} (u : PanSemStateFiniteExact 64 σ) (t k v : BitVec 64)
    (slots : List (BitVec 64 × BitVec 64)) (R : Assn) (i : Nat) (hn : 16 * slots.length < 2 ^ 64)
    (hi : i ≤ slots.length) (hs : Sat u (TableAt t slots ∗ R))
    (lt : u.locals.lookup nT = some (.val (.word t))) (lk : u.locals.lookup nK = some (.val (.word k)))
    (lv : u.locals.lookup nV = some (.val (.word v)))
    (ll : u.locals.lookup nL = some (.val (.word (BitVec.ofNat 64 (16 * slots.length)))))
    (lj : u.locals.lookup nJ = some (.val (.word (BitVec.ofNat 64 (16 * i)))))
    (lo : u.locals.lookup nO = some (.val (.word 0)))
    (lg : u.locals.lookup nG = some (.val (.word 1))) :
    (i = slots.length → evaluateHOLFiniteState u insBody =
      (none, setKvarHOLFinite .local nG (.val (.word 0)) u)) ∧
    (∀ (h : i < slots.length), (slots[i].1 = k ∨ slots[i].1 = 0) →
      ∃ u2 : PanSemStateFiniteExact 64 σ, Sat u2 (TableAt t (slots.set i (k, v)) ∗ R) ∧ u2.locals = u.locals ∧
        u2.memaddrs = u.memaddrs ∧ u2.clock = u.clock ∧
        evaluateHOLFiniteState u insBody =
          (none, setKvarHOLFinite .local nG (.val (.word 0)) (setKvarHOLFinite .local nO (.val (.word 1)) u2))) ∧
    (∀ (h : i < slots.length), slots[i].1 ≠ k → slots[i].1 ≠ 0 → evaluateHOLFiniteState u insBody =
      (none, setKvarHOLFinite .local nJ (.val (.word (BitVec.ofNat 64 (16 * (i + 1))))) u)) := by
  have hend : (BitVec.ofNat 64 (16 * i) = BitVec.ofNat 64 (16 * slots.length)) ↔ i = slots.length := by
    constructor
    · intro e; have := congrArg BitVec.toNat e; simp at this; omega
    · intro e; rw [e]
  refine ⟨fun he => ?_, fun h hk => ?_, fun h hk hk0 => ?_⟩
  · unfold insBody
    rw [ite_word u _ _ _ 1 (by simp [evalHOLExact, vv, lj, ll, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, he])]
    rw [if_pos (by decide : (1 : BitVec 64) ≠ 0)]
    exact assign_ok u .local nG _ _ (by simp [evalHOLExact])
      (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, lg, shapeOfHOLExact, shapeEqHOL])
  · obtain ⟨⟨dk, mk⟩, ⟨dv, mv⟩⟩ := slot_read u t slots R hs i h
    have ne : ¬ i = slots.length := by omega
    let a0 := t + BitVec.ofNat 64 (16 * i)
    let u1 := { u with memory := fun c => if c = a0 then HolWordLab.word k else u.memory c }
    let u2 := { u1 with memory := fun c => if c = a0 + 8 then HolWordLab.word v else u1.memory c }
    refine ⟨u2, table_write u t k v slots R i h hs, rfl, rfl, rfl, ?_⟩
    have cw : OrOp.or (if slots[i].1 = k then (1#64 : BitVec 64) else 0#64)
        (OrOp.or (if slots[i].1 = 0#64 then 1#64 else 0#64) 0#64) ≠ 0 := by
      rcases hk with e | e
      · simp only [e, ite_true]; split <;> decide
      · simp only [e, ite_true]; split <;> decide
    unfold insBody
    rw [ite_word u _ _ _ 0 (by simp [evalHOLExact, vv, lj, ll, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hend, ne])]
    simp only [ne_eq, not_true_eq_false, ite_false]
    rw [ite_word u _ _ _ _ (by
      simp [evalHOLExact, evalListHOLExact, keyAt, vv, lt, lj, lk, wordOpHOL, wordOp, valueIsWord, valueWord,
        memLoadHOLExact, dk, mk, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rfl)]
    rw [if_pos cw]
    have e1 : evaluateHOLFiniteState u (.store (.op .add [vv nT, vv nJ]) (vv nK)) = (none, u1) :=
      store_word u _ _ a0 k (by simp [evalHOLExact, evalListHOLExact, vv, lt, lj, wordOpHOL, wordOp, valueIsWord,
        valueWord, a0]) (by simp [evalHOLExact, vv, lk]) dk
    have e2 : evaluateHOLFiniteState u1 (.store (.op .add [vv nT, vv nJ, .const 8]) (vv nV)) = (none, u2) :=
      store_word u1 _ _ (a0 + 8) v (by simp [evalHOLExact, evalListHOLExact, vv, lt, lj, wordOpHOL, wordOp, valueIsWord,
        valueWord, a0, u1, BitVec.add_assoc]) (by simp [evalHOLExact, vv, lv, u1]) (by simpa [u1] using dv)
    let u3 := setKvarHOLFinite .local nO (.val (.word 1)) u2
    have e3 : evaluateHOLFiniteState u2 (.assign .local nO (.const 1)) = (none, u3) :=
      assign_ok u2 .local nO _ _ (by simp [evalHOLExact])
        (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, u2, u1, lo, shapeOfHOLExact, shapeEqHOL])
    rw [seq_normal _ e1, seq_normal _ e2, seq_normal _ e3]
    exact assign_ok u3 .local nG _ _ (by simp [evalHOLExact])
      (by simp [isValidValueHOLFinite, lookupKvarHOLFinite, u3, u2, u1, setKvarHOLFinite, setVarHOLFinite, FUPDATE,
        dO.2.2.2.2.1, lg, shapeOfHOLExact, shapeEqHOL])
  · obtain ⟨⟨dk, mk⟩, _⟩ := slot_read u t slots R hs i h
    have ne : ¬ i = slots.length := by omega
    unfold insBody
    rw [ite_word u _ _ _ 0 (by simp [evalHOLExact, vv, lj, ll, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hend, ne])]
    simp only [ne_eq, not_true_eq_false, ite_false]
    rw [ite_word u _ _ _ 0 (by
      simp [evalHOLExact, evalListHOLExact, keyAt, vv, lt, lj, lk, wordOpHOL, wordOp, valueIsWord, valueWord,
        memLoadHOLExact, dk, mk, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hk, show ¬ slots[i].1 = 0#64 from hk0]
      decide)]
    simp only [ne_eq, not_true_eq_false, ite_false]
    apply assign_ok
    · simp [evalHOLExact, evalListHOLExact, vv, lj, wordOpHOL, wordOp, valueIsWord, valueWord]
      apply BitVec.eq_of_toNat_eq; simp; omega
    · simp [isValidValueHOLFinite, lookupKvarHOLFinite, lj, shapeOfHOLExact, shapeEqHOL]

end ConPanqueque.Table
