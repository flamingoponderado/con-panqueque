import ConRon.Arena.Store
import ConPanqueque.ConsModel

/-!
# The cons table refines the twin's `Tbl`

`TblRel t rows mk`: the twin's table `t` (node array and `Std.HashMap` cons
table) has the model's rows as its nodes, and its cons table sends a key to
`mk i` exactly when row `i` is that key. Then `Tbl.find?` is the model's probe
(`find_probe`), and `Tbl.push` of a fresh key keeps the relation (`push_rel`).
-/

namespace ConPanqueque.ConsTbl
open ConPanqueque.ConsModel ConRon.Arena

variable {α ι δ : Type} [BEq α] [LawfulBEq α] [Hashable α] [DecidableEq α]

structure TblRel (t : Tbl α ι δ) (rows : List α) (mk : Nat → ι) : Prop where
  nodes : t.nodes.toList = rows
  cons : ∀ a, t.cons[a]? = (rows.findIdx? (· = a)).map mk

theorem push_rel (t : Tbl α ι δ) (rows : List α) (mk : Nat → ι) (h : TblRel t rows mk) (a : α) (d : δ)
    (ha : a ∉ rows) : TblRel (t.push a d (mk rows.length)) (rows ++ [a]) mk := by
  constructor
  · simp [Tbl.push, h.nodes]
  · intro b
    simp only [Tbl.push, Std.HashMap.getElem?_insert]
    by_cases hb : a = b
    · subst hb
      have hn : rows.findIdx? (fun x => decide (x = a)) = none :=
        List.findIdx?_eq_none_iff.mpr (fun x hx => by simp; intro e; subst e; exact ha hx)
      simp [List.findIdx?_append, hn]
    · have : (a == b) = false := by simpa using hb
      rw [this]; simp only [Bool.false_eq_true, ↓reduceIte, h.cons b, List.findIdx?_append]
      cases e : rows.findIdx? (· = b) with
      | some i => simp
      | none => simp [hb]

theorem findIdx_of_get (rows : List α) (hnd : rows.Nodup) (a : α) (i : Nat) (h : rows[i]? = some a) :
    rows.findIdx? (· = a) = some i := by
  obtain ⟨hi, hai⟩ := List.getElem?_eq_some_iff.mp h
  rw [List.findIdx?_eq_some_iff_getElem]
  refine ⟨hi, by simp [hai], fun j hj => ?_⟩
  simp only [decide_eq_true_eq]
  intro e
  have := (List.pairwise_iff_getElem.mp hnd) j i (by omega) hi hj
  exact this (e.trans hai.symm)

/-- The twin's lookup is the model's probe, read through `mk`. -/
theorem find_probe (home : α → Nat) (t : Tbl α ι δ) (rows : List α) (slots : List Nat) (n : Nat) (mk : Nat → ι)
    (h : TblRel t rows mk) (hinv : Inv (α := α) home rows slots n) (a : α) :
    t.find? a = (probe rows slots n a n (home a)).map mk := by
  obtain ⟨hsome, hnone⟩ := probe_correct home rows slots n hinv a
  show t.cons[a]? = _
  rw [h.cons a]
  cases e : probe rows slots n a n (home a) with
  | some i => rw [findIdx_of_get rows hinv.rows_nodup a i (hsome i e)]
  | none =>
    have ha := hnone.mp e
    rw [List.findIdx?_eq_none_iff.mpr (fun x hx => by simp; intro e'; subst e'; exact ha hx)]

end ConPanqueque.ConsTbl
