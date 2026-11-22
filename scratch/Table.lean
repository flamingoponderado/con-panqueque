import ConPanqueque.Logic.Sep
import ConPanqueque.Rep
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Logic

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
