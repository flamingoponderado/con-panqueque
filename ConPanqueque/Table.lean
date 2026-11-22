import ConPanqueque.Logic.Sep
import ConPanqueque.Rep
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Logic

/-!
# Tables (memo caches) in Pancake memory

con-leche's kernel memoizes its walks over expression DAGs; in Pancake those
caches are mutable tables: slots `[key, value]` (key `0` empty), a separating
assertion `TableAt`. This file: the representation, its meaning (`find?`), reading
a slot, and the lookup scan loop (its proof follows).
-/

namespace ConPanqueque.Table

/-- Slot `i` of a table at `t` with `cap` slots: two words `[key, value]`, key `0`
meaning empty. -/
def slot (t : BitVec 64) (i : Nat) : BitVec 64 := t + BitVec.ofNat 64 (16 * i)

/-- The table's contents as a list of slots `(key, value)`. -/
def TableAt (t : BitVec 64) (slots : List (BitVec 64 × BitVec 64)) : Assn :=
  block t (slots.flatMap fun (k, v) => [.word k, .word v])

/-- What a slot list means: the first slot holding `k` gives its value. -/
def find? (slots : List (BitVec 64 × BitVec 64)) (k : BitVec 64) : Option (BitVec 64) :=
  (slots.find? (·.1 = k)).map (·.2)

end ConPanqueque.Table

namespace ConPanqueque.Table

def nT := ofString "t"
def nK := ofString "k"
def nL := ofString "lim"
def nJ := ofString "j"
def nR := ofString "r"
def nG := ofString "go"
def vv (n : MlS) : ExpHOL 64 := .var .local n

/-- One step of the scan: at the end stop; on a matching key record the value and
stop; otherwise move to the next slot. -/
def scanBody : ProgHOL 64 :=
  .ite (.cmp .equal (vv nJ) (vv nL)) (.assign .local nG (.const 0))
    (.ite (.cmp .equal (.load .one (.op .add [vv nT, vv nJ])) (vv nK))
      (.seq (.assign .local nR (.load .one (.op .add [vv nT, vv nJ, .const 8]))) (.assign .local nG (.const 0)))
      (.assign .local nJ (.op .add [vv nJ, .const 16])))

/-- The scan loop. -/
def scanLoop : ProgHOL 64 := .while (vv nG) scanBody

end ConPanqueque.Table

namespace ConPanqueque.Table
open ConPanqueque.Rep

theorem flat_length (slots : List (BitVec 64 × BitVec 64)) :
    (slots.flatMap fun (k, v) => [HolWordLab.word k, .word v]).length = 2 * slots.length := by
  induction slots with
  | nil => rfl
  | cons p rest ih => obtain ⟨k, v⟩ := p; simp [ih]; omega

theorem flat_get : ∀ (slots : List (BitVec 64 × BitVec 64)) (i : Nat) (hi : i < slots.length),
    (slots.flatMap fun (k, v) => [HolWordLab.word k, .word v])[2 * i]? = some (.word (slots[i].1)) ∧
    (slots.flatMap fun (k, v) => [HolWordLab.word k, .word v])[2 * i + 1]? = some (.word (slots[i].2))
  | [], _, hi => absurd hi (by simp)
  | (k, v) :: rest, 0, _ => by simp
  | (k, v) :: rest, i + 1, hi => by
    have := flat_get rest i (by simpa using hi)
    simp only [List.flatMap_cons, List.cons_append, List.nil_append]
    refine ⟨?_, ?_⟩
    · rw [show 2 * (i + 1) = 2 * i + 1 + 1 from by omega, List.getElem?_cons_succ, List.getElem?_cons_succ]
      simpa using this.1
    · rw [show 2 * (i + 1) + 1 = 2 * i + 1 + 1 + 1 from by omega, List.getElem?_cons_succ, List.getElem?_cons_succ]
      simpa using this.2

theorem slot_read {σ : Type} (s : PanSemStateFiniteExact 64 σ) (t : BitVec 64)
    (slots : List (BitVec 64 × BitVec 64)) (R : Assn) (hs : Sat s (TableAt t slots ∗ R))
    (i : Nat) (hi : i < slots.length) :
    (s.memaddrs (t + BitVec.ofNat 64 (16 * i)) ∧ s.memory (t + BitVec.ofNat 64 (16 * i)) = .word slots[i].1) ∧
    (s.memaddrs (t + BitVec.ofNat 64 (16 * i) + 8) ∧ s.memory (t + BitVec.ofNat 64 (16 * i) + 8) = .word slots[i].2) := by
  have hl := flat_length slots
  obtain ⟨g1, g2⟩ := flat_get slots i hi
  have r1 := block_get s _ t R (2 * i) (by rw [hl]; omega) hs
  have r2 := block_get s _ t R (2 * i + 1) (by rw [hl]; omega) hs
  rw [Option.some.inj ((List.getElem?_eq_getElem _).symm.trans g1)] at r1
  rw [Option.some.inj ((List.getElem?_eq_getElem _).symm.trans g2)] at r2
  have e1 : BitVec.ofNat 64 (8 * (2 * i)) = BitVec.ofNat 64 (16 * i) := by congr 1; omega
  have e2 : t + BitVec.ofNat 64 (8 * (2 * i + 1)) = t + BitVec.ofNat 64 (16 * i) + 8 := by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
  rw [e1] at r1; rw [e2] at r2
  exact ⟨r1, r2⟩

end ConPanqueque.Table

namespace ConPanqueque.Table

theorem find?_at : ∀ (slots : List (BitVec 64 × BitVec 64)) (k : BitVec 64) (i : Nat) (hi : i < slots.length),
    (∀ m (hm : m < i), (slots[m]'(by omega)).1 ≠ k) → slots[i].1 = k → find? slots k = some slots[i].2
  | [], _, _, hi, _, _ => absurd hi (by simp)
  | p :: rest, k, 0, _, _, hk => by
    simp only [List.getElem_cons_zero] at hk ⊢; simp [find?, List.find?, hk]
  | p :: rest, k, i + 1, hi, hb, hk => by
    have h0 := hb 0 (by omega)
    simp at h0
    have := find?_at rest k i (by simpa using hi)
      (fun m hm => by have := hb (m + 1) (by omega); rw [List.getElem_cons_succ] at this; exact this)
      (by rw [List.getElem_cons_succ] at hk; exact hk)
    rw [List.getElem_cons_succ]
    simpa [find?, List.find?, h0] using this

theorem find?_none : ∀ (slots : List (BitVec 64 × BitVec 64)) (k : BitVec 64),
    (∀ m (hm : m < slots.length), slots[m].1 ≠ k) → find? slots k = none
  | [], _, _ => rfl
  | p :: rest, k, hb => by
    have h0 := hb 0 (by simp)
    simp at h0
    have := find?_none rest k (fun m hm => by
      have := hb (m + 1) (by simp; omega); rw [List.getElem_cons_succ] at this; exact this)
    simpa [find?, List.find?, h0] using this

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
