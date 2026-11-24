import ConPanqueque.T.Heap
import ConPanqueque.Logic.Byte

/-! # The input buffer in the value heap

The frontend keeps its input bytes in cells of the value heap, packed little-endian eight to a word,
so that the buffer survives every arena operation: SR tracks the heap's image exactly
(`heap_cell`), and `bytesAt_of_heap` reads the scanner's `BytesAt` off it. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

namespace ConPanqueque.Front

open ConPanqueque.T

variable {σ : Type}

/-- The image holds `bs` from cell `j0`, packed: byte `i` is byte `i % 8` of cell `j0 + i / 8`. -/
def Packed (H : List (BitVec 64)) (j0 : Nat) (bs : List UInt8) : Prop :=
  ∀ i (hi : i < bs.length), ∃ w, H[j0 + i / 8]? = some w ∧ byteW w (i % 8) = bs[i].toNat

theorem cellA_add (C : Ctx) (j k : Nat) : cellA C (j + k) = cellA C j + BitVec.ofNat 64 (8 * k) := by
  unfold cellA
  rw [BitVec.add_assoc]; congr 1
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, Nat.mul_add, Nat.add_mod]

/-- **The buffer is read off the heap image.** -/
theorem bytesAt_of_heap {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t) (j0 : Nat) (bs : List UInt8)
    (hpk : Packed C.H j0 bs) (hal : (cellA C j0).toNat % 8 = 0)
    (hroom : (cellA C j0).toNat + bs.length < 2 ^ 64) : BytesAt t (cellA C j0) bs := by
  refine ⟨trivial, hal, hroom, fun i hi => ?_⟩
  obtain ⟨w, hw, hb⟩ := hpk i hi
  have hj : j0 + i / 8 < C.H.length := by
    by_cases hl : j0 + i / 8 < C.H.length
    · exact hl
    · rw [List.getElem?_eq_none (by omega)] at hw; cases hw
  have hc := heap_cell h (j0 + i / 8) hj
  rw [cellA_add] at hc
  rw [List.getElem?_eq_getElem hj] at hw
  cases hw
  exact ⟨_, hc.2, hc.1, hb⟩

end ConPanqueque.Front
