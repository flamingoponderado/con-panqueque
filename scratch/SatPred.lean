import ConLeche

theorem satPred_bv (x : UInt64) :
    (ConLeche.satPred x).toBitVec =
      x.toBitVec - (if x.toBitVec ≠ 0 then 1 else 0) * (if x.toBitVec ≠ 32767#64 then 1 else 0) := by
  unfold ConLeche.satPred
  by_cases h1 : x = 32767
  · subst h1; decide
  · by_cases h0 : x = 0
    · subst h0; decide
    · have a1 : x.toBitVec ≠ 32767#64 := fun e => h1 (UInt64.toBitVec_inj.mp (by simpa using e))
      have a0 : x.toBitVec ≠ 0 := fun e => h0 (UInt64.toBitVec_inj.mp (by simpa using e))
      simp [h1, h0, a1]; exact a0
