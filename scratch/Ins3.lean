import ConPanqueque.Table
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Logic ConPanqueque.Table ConPanqueque.Rep

namespace ConPanqueque.Table

def nV := ofString "v"
def nO := ofString "ok"

def keyAt : ExpHOL 64 := .load .one (.op .add [vv nT, vv nJ])

/-- One step of insertion: at the end stop (`ok` stays 0); on a slot holding `k` or
empty write `[k, v]`, set `ok`, stop; otherwise move on. -/
def insBody : ProgHOL 64 :=
  .ite (.cmp .equal (vv nJ) (vv nL)) (.assign .local nG (.const 0))
    (.ite (.op .or [.cmp .equal keyAt (vv nK), .cmp .equal keyAt (.const 0)])
      (.seq (.store (.op .add [vv nT, vv nJ]) (vv nK))
        (.seq (.store (.op .add [vv nT, vv nJ, .const 8]) (vv nV))
          (.seq (.assign .local nO (.const 1)) (.assign .local nG (.const 0)))))
      (.assign .local nJ (.op .add [vv nJ, .const 16])))

def insLoop : ProgHOL 64 := .while (vv nG) insBody

/-- Writing slot `i`: two block stores. -/
theorem table_write {σ : Type} (s : PanSemStateFiniteExact 64 σ) (t k v : BitVec 64)
    (slots : List (BitVec 64 × BitVec 64)) (R : Assn) (i : Nat) (hi : i < slots.length)
    (hs : Sat s (TableAt t slots ∗ R)) :
    let s1 := { s with memory := fun c => if c = t + BitVec.ofNat 64 (16 * i) then .word k else s.memory c }
    let s2 := { s1 with memory := fun c => if c = t + BitVec.ofNat 64 (16 * i) + 8 then .word v else s1.memory c }
    Sat s2 (TableAt t (slots.set i (k, v)) ∗ R) := by
  intro s1 s2
  have hl := flat_length slots
  have a1 := block_set _ t R (2 * i) (by rw [hl]; omega) s (.word k) hs
  have e1 : t + BitVec.ofNat 64 (8 * (2 * i)) = t + BitVec.ofNat 64 (16 * i) := by congr 1; congr 1; omega
  rw [e1] at a1
  have a2 := block_set _ t R (2 * i + 1) (by rw [List.length_set, hl]; omega) s1 (.word v) a1
  have e2 : t + BitVec.ofNat 64 (8 * (2 * i + 1)) = t + BitVec.ofNat 64 (16 * i) + 8 := by
    rw [BitVec.add_assoc]; congr 1; apply BitVec.eq_of_toNat_eq; simp; omega
  rw [e2] at a2
  unfold TableAt; rw [flat_set]; exact a2

end ConPanqueque.Table
