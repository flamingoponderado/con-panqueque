import ConPanqueque.T.Ind.Split
import ConRon.Arena.Inductives.BlockShape

/-!
# `blockSplit` as slices of the block

A split block is its inductive types (the first `k` records), its constructors (the next `nC`), and its
recursors (the rest), each list the records' fields (`blockSplit_slices`); and `k`, `k + nC` are the ends of
the runs of kinds `3` and `4` (`runEnd`), the third run reaching the block's end.
-/

open ConRon.Arena

namespace ConPanqueque.T.Ind

/-- The fields `blockSplitRecs` keeps of a recursor record. -/
def recTuple : IConstantInfo → Option (IConstantVal × Nat × Nat × Bool × List IRecRule)
  | .recInfo cvR mI rP isK rules => some (cvR, mI, rP, isK, rules)
  | _ => none

theorem blockSplitRecs_some : ∀ (xs : List IConstantInfo) rs, blockSplitRecs xs = some rs →
    rs.length = xs.length ∧ ∀ i (hi : i < xs.length) (hr : i < rs.length), recTuple xs[i] = some rs[i]
  | [], rs, h => by simp [blockSplitRecs] at h; subst h; simp
  | x :: xs, rs, h => by
    cases x with
    | recInfo cvR mI rP isK rules =>
      simp only [blockSplitRecs] at h
      cases h' : blockSplitRecs xs with
      | none => rw [h'] at h; simp at h
      | some rs' =>
        rw [h'] at h; simp only [Option.some.injEq] at h; subst h
        obtain ⟨hl, hi⟩ := blockSplitRecs_some xs rs' h'
        refine ⟨by simp [hl], fun i hi1 hr => ?_⟩
        cases i with
        | zero => rfl
        | succ i => simpa using hi i (by simpa using hi1) (by simpa using hr)
    | _ => simp [blockSplitRecs] at h

theorem blockSplitRecs_kinds : ∀ (xs : List IConstantInfo) rs, blockSplitRecs xs = some rs →
    ∀ i (hi : i < xs.length), kindOf xs[i] = 5
  | [], _, _ => fun i hi => absurd hi (by simp)
  | x :: xs, rs, h => by
    cases x with
    | recInfo cvR mI rP isK rules =>
      simp only [blockSplitRecs] at h
      cases h' : blockSplitRecs xs with
      | none => rw [h'] at h; simp at h
      | some rs' =>
        intro i hi
        cases i with
        | zero => rfl
        | succ i => simpa using blockSplitRecs_kinds xs rs' h' i (by simpa using hi)
    | _ => simp [blockSplitRecs] at h

/-- A recursor record's fields (`blockSplitRecs`'s tuple; a default elsewhere). -/
def recT : IConstantInfo → IConstantVal × Nat × Nat × Bool × List IRecRule
  | .recInfo cvR mI rP isK rules => (cvR, mI, rP, isK, rules)
  | _ => default

/-- A constructor record's fields (`blockSplitCtors`'s tuple). -/
def ctorT : IConstantInfo → IConstantVal × Nat × Nat
  | .ctorInfo cvC nP nF _ => (cvC, nP, nF)
  | _ => default

theorem blockSplitRecs_all : ∀ (xs : List IConstantInfo), (∀ x ∈ xs, kindOf x = 5) →
    blockSplitRecs xs = some (xs.map recT)
  | [], _ => rfl
  | x :: xs, h => by
    have hx := h x (by simp)
    have ih := blockSplitRecs_all xs (fun y hy => h y (by simp [hy]))
    cases x <;> simp [kindOf] at hx
    simp [blockSplitRecs, ih, recT]

/-- The kind at an index (`none` past the end). -/
def kindAt (xs : List IConstantInfo) (i : Nat) : Option Nat := xs[i]?.map kindOf

@[simp] theorem kindAt_cons_zero (x : IConstantInfo) (xs : List IConstantInfo) : kindAt (x :: xs) 0 = some (kindOf x) := rfl
@[simp] theorem kindAt_cons_succ (x : IConstantInfo) (xs : List IConstantInfo) (i : Nat) :
    kindAt (x :: xs) (i + 1) = kindAt xs i := rfl
@[simp] theorem kindAt_nil (i : Nat) : kindAt [] i = none := rfl

theorem blockSplitCtors_runs : ∀ (xs : List IConstantInfo) (nC : Nat), nC ≤ xs.length →
    (∀ i, i < nC → kindAt xs i = some 4) → kindAt xs nC ≠ some 4 →
    (∀ i, nC ≤ i → i < xs.length → kindAt xs i = some 5) →
    blockSplitCtors xs = some ((xs.take nC).map ctorT, (xs.drop nC).map recT)
  | [], nC, hle, _, _, _ => by
    have : nC = 0 := by simp at hle; omega
    subst this; rfl
  | x :: xs, 0, _, _, hnot, hrest => by
    have hall : ∀ y ∈ x :: xs, kindOf y = 5 := by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
      have := hrest i (by omega) hi
      simpa [kindAt, List.getElem?_eq_getElem hi] using this
    have hx : kindOf x = 5 := hall x (by simp)
    rw [show blockSplitCtors (x :: xs) = (match blockSplitRecs (x :: xs) with
        | some rs => some ([], rs) | none => none) by
      cases x <;> simp [kindOf] at hx; rfl]
    rw [blockSplitRecs_all (x :: xs) hall]; simp
  | x :: xs, nC + 1, hle, hk, hnot, hrest => by
    have hx : kindOf x = 4 := by simpa using hk 0 (by omega)
    have ih := blockSplitCtors_runs xs nC (by simp at hle; omega)
      (fun i hi => by simpa using hk (i + 1) (by omega))
      (by simpa using hnot)
      (fun i hi hl => by simpa using hrest (i + 1) (by omega) (by simp; omega))
    cases x with
    | ctorInfo cvC nP nF ind => simp [blockSplitCtors, ih, ctorT]
    | _ => simp [kindOf] at hx

theorem blockSplit_runs : ∀ (xs : List IConstantInfo) (k nC : Nat), k + nC ≤ xs.length →
    (∀ i, i < k → kindAt xs i = some 3) → kindAt xs k ≠ some 3 →
    (∀ i, i < nC → kindAt xs (k + i) = some 4) → kindAt xs (k + nC) ≠ some 4 →
    (∀ i, k + nC ≤ i → i < xs.length → kindAt xs i = some 5) →
    blockSplit xs = some ((xs.take k).map (·.toConstantVal), ((xs.drop k).take nC).map ctorT,
      ((xs.drop k).drop nC).map recT)
  | xs, 0, nC, hle, _, hnot, hc, hcn, hr => by
    have hcs := blockSplitCtors_runs xs nC (by omega) (fun i hi => by simpa using hc i hi)
      (by simpa using hcn) (fun i hi hl => hr i (by omega) hl)
    cases xs with
    | nil =>
      have : nC = 0 := by simp at hle; omega
      subst this; rfl
    | cons x xs =>
      have hx : kindOf x ≠ 3 := by simpa using hnot
      rw [show blockSplit (x :: xs) = (match blockSplitCtors (x :: xs) with
          | some q => some ([], q.1, q.2) | none => none) by
        cases x <;> simp [kindOf] at hx <;> rfl]
      rw [hcs]; simp
  | [], k + 1, nC, hle, _, _, _, _, _ => by simp at hle
  | x :: xs, k + 1, nC, hle, hk, hnot, hc, hcn, hr => by
    have hx : kindOf x = 3 := by simpa using hk 0 (by omega)
    have ih := blockSplit_runs xs k nC (by simp at hle; omega)
      (fun i hi => by simpa using hk (i + 1) (by omega))
      (by simpa using hnot)
      (fun i hi => by have := hc i hi; rw [show k + 1 + i = (k + i) + 1 by omega] at this; simpa using this)
      (by have := hcn; rw [show k + 1 + nC = (k + nC) + 1 by omega] at this; simpa using this)
      (fun i hi hl => by simpa using hr (i + 1) (by omega) (by simp; omega))
    cases x with
    | indInfo cvT caps => simp [blockSplit, ih, IConstantInfo.toConstantVal]
    | _ => simp [kindOf] at hx

theorem runEnd_spec (blk : List IConstantInfo) (t : Nat) : ∀ fuel j, blk.length - j ≤ fuel → j ≤ blk.length →
    j ≤ runEnd blk t fuel j ∧ runEnd blk t fuel j ≤ blk.length ∧
    (∀ i, j ≤ i → i < runEnd blk t fuel j → kindAt blk i = some t) ∧ kindAt blk (runEnd blk t fuel j) ≠ some t := by
  intro fuel
  induction fuel with
  | zero =>
    intro j h hj
    have : j = blk.length := by omega
    subst this
    refine ⟨le_refl _, le_refl _, fun i h1 h2 => absurd h2 (by simp [runEnd]; omega), ?_⟩
    simp [runEnd, kindAt, List.getElem?_eq_none (le_refl _)]
  | succ f ih =>
    intro j h hj
    by_cases hjl : j < blk.length
    · simp only [runEnd, List.getElem?_eq_getElem hjl]
      by_cases hk : kindOf blk[j] = t
      · rw [ite_eq_left hk]
        obtain ⟨a, b, c, d⟩ := ih (j + 1) (by omega) (by omega)
        refine ⟨by omega, b, fun i h1 h2 => ?_, d⟩
        by_cases e : i = j
        · subst e; simp [kindAt, List.getElem?_eq_getElem hjl, hk]
        · exact c i (by omega) h2
      · rw [ite_eq_right hk]
        exact ⟨le_refl _, by omega, fun i h1 h2 => absurd h2 (by omega),
          by simp [kindAt, List.getElem?_eq_getElem hjl, hk]⟩
    · have : j = blk.length := by omega
      subst this
      refine ⟨by simp [runEnd_zero_len (le_refl _)], by simp [runEnd_zero_len (le_refl _)],
        fun i h1 h2 => by simp [runEnd_zero_len (le_refl _)] at h2; omega, ?_⟩
      simp [runEnd_zero_len (le_refl _), kindAt, List.getElem?_eq_none (le_refl _)]

end ConPanqueque.T.Ind
