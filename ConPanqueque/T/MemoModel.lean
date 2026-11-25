import ConPanqueque.V.Intern
open ConPanqueque.ConsTbl ConPanqueque.V
open ConRon.Arena

/-!
# Memo tables, modelled

A twin memo `m : Std.HashMap K V` is held as a cons table `tb : Tbl K Nat V` (keys as rows, values
in the derived column, indices as handles): `MemoRel m tb` says every key's lookup agrees.
Inserting interns the key (finding its row or appending one) and overwrites that row's value —
`HashMap.insert`'s semantics whether or not the key was present.
-/

namespace ConPanqueque.T

variable {K V : Type} [BEq K] [LawfulBEq K] [Hashable K] [DecidableEq K] [Inhabited V]

/-- Overwrite row `i`'s value. -/
def Tbl.setDer (tb : Tbl K Nat V) (i : Nat) (v : V) : Tbl K Nat V := { tb with der := tb.der.set! i v }

def MemoRel (m : Std.HashMap K V) (tb : Tbl K Nat V) : Prop :=
  ∀ k, m[k]? = (tb.find? k).map tb.derAt

/-- The row an insert writes. -/
def memoIns (tb : Tbl K Nat V) (k : K) (v : V) : Tbl K Nat V × Nat :=
  let r := tierInt tb k v id
  (Tbl.setDer r.1 r.2 v, r.2)


theorem getD_setIfInBounds_ne {W : Type} (xs : Array W) (i j : Nat) (v d : W) (h : i ≠ j) :
    (xs.setIfInBounds i v).getD j d = xs.getD j d := by
  simp [Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds, h]

theorem getD_push_lt {W : Type} (xs : Array W) (j : Nat) (v d : W) (h : j < xs.size) :
    (xs.push v).getD j d = xs.getD j d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_push_lt h,
    Array.getElem?_eq_getElem h]

theorem memoRel_empty : MemoRel (∅ : Std.HashMap K V) ⟨#[], #[], ∅⟩ := by
  intro k; simp [Tbl.find?]

theorem memoRel_insert (m : Std.HashMap K V) (tb : Tbl K Nat V) (rows : List K) (h : MemoRel m tb)
    (hr : TblRel tb rows id) (hnd : rows.Nodup) (hder : tb.der.size = rows.length) (k : K) (v : V) :
    MemoRel (m.insert k v) (memoIns tb k v).1 ∧ TblRel (memoIns tb k v).1 (if k ∈ rows then rows else rows ++ [k]) id ∧
      (memoIns tb k v).1.der.size = (if k ∈ rows then rows else rows ++ [k]).length := by
  have hsz : tb.nodes.size = rows.length := by have := congrArg List.length hr.nodes; simpa using this
  unfold memoIns tierInt
  simp only
  by_cases hk : k ∈ rows
  · -- the key has a row: its index is that row
    obtain ⟨i, hi, hki⟩ := List.mem_iff_getElem.mp hk
    have hfi : tb.find? k = some i := by
      show tb.cons[k]? = _
      rw [hr.cons k, findIdx_of_get rows hnd k i (by simp [hi, hki])]; rfl
    simp only [hfi, ite_eq_left hk]
    refine ⟨fun k' => ?_, ⟨by simp [Tbl.setDer, hr.nodes], fun a => hr.cons a⟩,
      by simp [Tbl.setDer, hder]⟩
    rw [Std.HashMap.getElem?_insert]
    by_cases e : k = k'
    · subst e
      simp only [beq_self_eq_true, ↓reduceIte, Tbl.find?, Tbl.setDer]
      show some v = (tb.cons[k]?).map _
      rw [show tb.cons[k]? = some i from hfi]
      simp [Tbl.derAt, Array.set!, Array.getD, hi, hder]
    · have hne : (k == k') = false := by simpa using e
      rw [hne]; simp only [Bool.false_eq_true, ↓reduceIte]
      rw [h k']
      show (tb.cons[k']?).map tb.derAt = (tb.cons[k']?).map (Tbl.setDer tb i v).derAt
      cases hj : tb.cons[k']? with
      | none => rfl
      | some j =>
        have hj' := hr.cons k'
        rw [hj] at hj'
        have hjr : rows.findIdx? (· = k') = some j := by
          cases e2 : rows.findIdx? (· = k') with
          | none => rw [e2] at hj'; simp at hj'
          | some j' => rw [e2] at hj'; simp at hj'; rw [hj']
        obtain ⟨hjl, hjk, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hjr
        have hij : j ≠ i := by
          intro eq; subst eq; simp at hjk; exact e (hki.symm.trans hjk)
        show some (tb.derAt j) = some (Tbl.derAt { tb with der := tb.der.setIfInBounds i v } j)
        simp only [Tbl.derAt]
        rw [getD_setIfInBounds_ne _ _ _ _ _ (Ne.symm hij)]
  · -- a new row at the end
    have hfn : tb.find? k = none := by
      show tb.cons[k]? = _
      rw [hr.cons k, List.findIdx?_eq_none_iff.mpr (fun x hx => by simp; intro e; subst e; exact hk hx)]; rfl
    simp only [hfn, ite_eq_right hk]
    have hrel := push_rel tb rows id hr k v hk
    have hts : tb.size = rows.length := hsz
    simp only [hts]
    refine ⟨fun k' => ?_, ⟨by simp [Tbl.setDer]; exact hrel.nodes, fun a => hrel.cons a⟩,
      by simp [Tbl.setDer, Tbl.push, hder]⟩
    rw [Std.HashMap.getElem?_insert]
    by_cases e : k = k'
    · subst e
      simp only [beq_self_eq_true, ↓reduceIte, Tbl.find?, Tbl.setDer, Tbl.push, Std.HashMap.getElem?_insert]
      simp [Tbl.derAt, Array.set!, Array.getD, hder, hsz]
    · have hne : (k == k') = false := by simpa using e
      rw [hne]; simp only [Bool.false_eq_true, ↓reduceIte]
      rw [h k']
      simp only [Tbl.find?, Tbl.setDer, Tbl.push, Std.HashMap.getElem?_insert, hne, Bool.false_eq_true, ↓reduceIte]
      cases hj : tb.cons[k']? with
      | none => rfl
      | some j =>
        have hj' := hr.cons k'
        rw [hj] at hj'
        have hjr : rows.findIdx? (· = k') = some j := by
          cases e2 : rows.findIdx? (· = k') with
          | none => rw [e2] at hj'; simp at hj'
          | some j' => rw [e2] at hj'; simp at hj'; rw [hj']
        obtain ⟨hjl, _, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hjr
        have hij : j ≠ rows.length := by omega
        have hjd : j < tb.der.size := by omega
        show some (tb.derAt j) = some (Tbl.derAt (⟨tb.nodes.push k, (tb.der.push v).setIfInBounds (id rows.length) v,
          tb.cons.insert k (id rows.length)⟩ : Tbl K Nat V) j)
        simp only [Tbl.derAt, id]
        rw [getD_setIfInBounds_ne _ _ _ _ _ (Ne.symm hij), getD_push_lt _ _ _ _ hjd]

end ConPanqueque.T
