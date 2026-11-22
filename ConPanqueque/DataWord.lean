import ConLeche

/-!
# The packed data word as word operations

con-leche's `Expr.data` accessors (`hashOfData`, `bvarOfData`, …) use division
and modulo; Pancake has shifts and multiplication. Each accessor equals a
shift-only expression (and `packData` a multiply-add), as `BitVec 64`
identities used by the Pancake node constructors.
-/

namespace ConPanqueque.DataWord

theorem hashOfData_bv (w : UInt64) : (ConLeche.hashOfData w).toBitVec = w.toBitVec >>> 32 := by
  apply BitVec.eq_of_toNat_eq
  simp [ConLeche.hashOfData, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
theorem bvarOfData_bv (w : UInt64) : (ConLeche.bvarOfData w).toBitVec = (w.toBitVec <<< 33) >>> 49 := by
  apply BitVec.eq_of_toNat_eq
  simp [ConLeche.bvarOfData, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  omega
theorem fvarOfData_bv (w : UInt64) : (ConLeche.fvarOfData w).toBitVec = (w.toBitVec <<< 48) >>> 49 := by
  apply BitVec.eq_of_toNat_eq
  simp [ConLeche.fvarOfData, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  omega
theorem hash32_bv (w : UInt64) : (ConLeche.hash32 w).toBitVec = (w.toBitVec <<< 32) >>> 32 := by
  apply BitVec.eq_of_toNat_eq
  simp [ConLeche.hash32, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow]
  omega
theorem packData_bv (h b f : UInt64) (lp : Bool) :
    (ConLeche.packData h b f lp).toBitVec =
      h.toBitVec * 4294967296#64 + b.toBitVec * 65536#64 + f.toBitVec * 2#64 + (if lp then 1 else 0) := by
  cases lp <;> simp [ConLeche.packData]

theorem lpOfData_bv (w : UInt64) :
    (if ConLeche.lpOfData w then (1 : BitVec 64) else 0) = (w.toBitVec <<< 63) >>> 63 := by
  apply BitVec.eq_of_toNat_eq
  have hm : (w % 2).toNat = w.toNat % 2 := UInt64.toNat_mod w 2
  by_cases hw : w % 2 = 1
  · have : w.toNat % 2 = 1 := by rw [← hm, hw]; rfl
    simp [ConLeche.lpOfData, hw, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow]; omega
  · have : w.toNat % 2 = 0 := by
      have h2 : (w % 2).toNat < 2 := by rw [hm]; omega
      have : (w % 2).toNat ≠ 1 := fun e => hw (UInt64.toNat_inj.mp (by simpa using e))
      omega
    simp [ConLeche.lpOfData, hw, BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq,
      Nat.shiftRight_eq_div_pow]; omega

end ConPanqueque.DataWord
