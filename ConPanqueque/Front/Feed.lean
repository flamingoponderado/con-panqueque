import ConPanqueque.Front.Apply
import ConRon.Bridge.Pers

/-! # The twin of the line loop

`feedAll st b i n` applies every line of `b` from `i`, the last one without a newline included.
`feedAll_tail`: when it succeeds, con-ron's `feedChunk` followed by `applyFinalLine` (the middle of
`parseBytes`) succeeds with the same state, at the same final `AState`. -/

open ConRon.Arena ConRon.Arena.Frontend ConRon.Bridge

namespace ConPanqueque.Front

open ConLeche.Frontend (scanLineFwd ScanRes usizeInBounds)

/-- Every line from `i`, applied in order. -/
def feedAll (st : StateD) (b : ByteArray) (i : USize) (n : Nat) : AM StateD :=
  if _h : i < b.usize then
    match scanLineFwd b i with
    | .err _ => fail (.internal "line")
    | .ok r j => do
      match ← applyLine st r n with
      | .inr _ => fail (.internal "record")
      | .inl st' =>
        if j == 0 then pure st'
        else if _hj : i < j then feedAll st' b j (n + 1)
        else fail (.internal "progress")
  else pure st
termination_by b.size - i.toNat
decreasing_by exact Nat.sub_lt_sub_left (usizeInBounds b i _h) (USize.lt_iff_toNat_lt.mp _hj)

/-- The middle of `parseBytes`: the complete lines, then the last one. -/
def tailRun (st : StateD) (b : ByteArray) (i : USize) (n : Nat) : AM (Except (CheckError × Nat) StateD) := do
  match ← feedChunk st b i n with
  | .error e => pure (.error e)
  | .ok (st, lineNo, tail) =>
    if tail < b.usize then applyFinalLine st b tail lineNo else pure (.ok st)

theorem bind_ok_apply {α β : Type} {x : AM α} {f : α → AM β} {s s1 : AState} {a : α} (h : x s = .ok (a, s1)) :
    (x >>= f) s = f a s1 := by
  rw [AM.bind_apply, h]; rfl

theorem feedAll_tail (b : ByteArray) :
    ∀ msr (i : USize) (st : StateD) (n : Nat) (s s' : AState) (st' : StateD), b.size - i.toNat = msr →
      feedAll st b i n s = .ok (st', s') → tailRun st b i n s = .ok (.ok st', s') := by
  intro msr
  induction msr using Nat.strongRecOn with
  | ind msr ih =>
    intro i st n s s' st' hm h
    rw [feedAll] at h
    by_cases hi : i < b.usize
    · rw [dif_pos hi] at h
      revert h
      cases hsc : scanLineFwd b i with
      | err e => intro h; exact (AM.fail_ok h).elim
      | ok r j =>
        intro h
        obtain ⟨x, s1, hx, hrest⟩ := AM.bind_ok h
        cases x with
        | inr v => exact (AM.fail_ok hrest).elim
        | inl st1 =>
          simp only at hrest
          by_cases hj0 : (j == 0) = true
          · rw [if_pos hj0] at hrest
            obtain ⟨rfl, rfl⟩ := AM.pure_ok hrest
            unfold tailRun
            rw [feedChunk, dif_pos hi]
            simp only [hsc, if_pos hj0]
            rw [bind_ok_apply (show (pure (Except.ok (st, n, i)) : AM (Except (CheckError × Nat) (StateD × Nat × USize))) s
              = .ok (.ok (st, n, i), s) from rfl)]
            simp only [if_pos hi]
            rw [applyFinalLine, hsc]
            simp only
            rw [bind_ok_apply hx]; rfl
          · rw [if_neg hj0] at hrest
            by_cases hij : i < j
            · rw [dif_pos hij] at hrest
              have hlt := USize.lt_iff_toNat_lt.mp hij
              have hb := usizeInBounds b i hi
              have ih' := ih _ (by omega) j st1 (n + 1) s1 s' st' rfl hrest
              unfold tailRun at ih' ⊢
              rw [feedChunk, dif_pos hi]
              simp only [hsc, if_neg hj0]
              rw [AM.bind_apply, AM.bind_apply, hx]
              simp only [dif_pos hij]
              rw [AM.bind_apply] at ih'
              exact ih'
            · rw [dif_neg hij] at hrest; exact (AM.fail_ok hrest).elim
    · rw [dif_neg hi] at h
      obtain ⟨rfl, rfl⟩ := AM.pure_ok h
      unfold tailRun
      rw [feedChunk, dif_neg hi]
      rw [bind_ok_apply (show (pure (Except.ok (st', n, i)) : AM (Except (CheckError × Nat) (StateD × Nat × USize))) s'
        = .ok (.ok (st', n, i), s') from rfl)]
      simp only [if_neg hi]; rfl

end ConPanqueque.Front
