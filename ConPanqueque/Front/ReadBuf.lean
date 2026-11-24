import ConPanqueque.Front.Read

/-! # The read buffer as the input

The harness's convention: cell `j0` holds the input's length `n`, the bytes follow from cell
`j0 + 1`.  `inputOf nb n` is the input those bytes carry; `bufOK_of_read` gives `BufOK` for it at
the written image. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan

/-- The input: `n` bytes after the 8-byte header. -/
def inputOf (nb : List (BitVec 8)) (n : Nat) : ByteArray :=
  ⟨(((nb.drop 8).take n).map UInt8.ofBitVec).toArray⟩

theorem inputOf_size (nb : List (BitVec 8)) (n : Nat) (h : 8 + n ≤ nb.length) : (inputOf nb n).size = n := by
  simp [inputOf, ByteArray.size]; omega

theorem inputOf_get (nb : List (BitVec 8)) (n i : Nat) (h : 8 + n ≤ nb.length) (hi : i < (inputOf nb n).data.toList.length) :
    ((inputOf nb n).data.toList[i]).toNat = (nb[8 + i]?.getD 0).toNat := by
  have hi' : i < n := by simp [inputOf] at hi; omega
  simp [inputOf, List.getElem?_eq_getElem (show 8 + i < nb.length by omega)]

theorem cellA_succ_aligned (C : Ctx) (j0 : Nat) (hal : (cellA C j0).toNat % 8 = 0)
    (hov : (cellA C j0).toNat + 8 < 2 ^ 64) : (cellA C (j0 + 1)).toNat % 8 = 0 := by
  rw [cellA_add]; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [show 8 * 1 % 2 ^ 64 = 8 from rfl, Nat.mod_eq_of_lt hov]; omega

/-- **The buffer after the read holds the input.** -/
theorem bufOK_of_read (C : Ctx) (j0 Lw : Nat) (hal : (cellA C j0).toNat % 8 = 0) (hcells : j0 + Lw ≤ C.H.length)
    (hov : (cellA C j0).toNat + 8 * Lw < 2 ^ 64) (h59 : 8 * Lw < 2 ^ 59) (hbits : System.Platform.numBits = 64)
    (nb : List (BitVec 8)) (hnb : nb.length = 8 * Lw) (n : Nat) (hn : n + 16 ≤ 8 * Lw) :
    BufOK (ctxH C (writeH C.H (cellA C j0) j0 0 nb)) (j0 + 1) (inputOf nb n) := by
  have hsz := inputOf_size nb n (by omega)
  have hlen : (writeH C.H (cellA C j0) j0 0 nb).length = C.H.length := writeH_length _ _ _ _ _
  refine ⟨fun i hi => ?_, cellA_succ_aligned C j0 hal (by omega), ?_, ⟨hbits, by omega, by omega⟩, by omega⟩
  · have hl : (inputOf nb n).data.toList.length = n := by rw [Array.length_toList]; exact hsz
    have hi' : i < n := by omega
    have hidx : j0 + 1 + i / 8 < (writeH C.H (cellA C j0) j0 0 nb).length := by rw [hlen]; omega
    refine ⟨_, List.getElem?_eq_getElem hidx, ?_⟩
    have hb := writeH_byte C.H (cellA C j0) j0 hal nb 0 (8 + i) (by omega) (by omega)
    rw [show (8 + i) / 8 = 1 + i / 8 by omega, show (8 + i) % 8 = i % 8 by omega, ← Nat.add_assoc,
      List.getElem?_eq_getElem hidx, Option.getD_some, if_pos ⟨by omega, by omega⟩, Nat.sub_zero] at hb
    show byteW ((writeH C.H (cellA C j0) j0 0 nb)[j0 + 1 + i / 8]) (i % 8) = _
    rw [hb, inputOf_get nb n i (by omega) hi]
  · show j0 + 1 + (inputOf nb n).size / 8 < (writeH C.H (cellA C j0) j0 0 nb).length
    rw [hlen, hsz]; omega

end ConPanqueque.Front
