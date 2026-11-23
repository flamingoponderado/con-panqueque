import ConPanqueque.T.Str.LitW
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `strLitConsSpine`: a string's characters as a `List.cons` spine

A recursive function over the byte index: decode the character at `i` (1–4 bytes), build the rest of the spine
first (the twin interns the tail first), then `lit c`, `Char.ofNat (lit c)`, `cons ch` and `app f rest`.
-/

namespace ConPanqueque.T.Str

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big

theorem w_sub (a k : Nat) (hk : k ≤ a) (ha : a < 2 ^ 64) :
    BitVec.ofNat 64 a - BitVec.ofNat 64 k = BitVec.ofNat 64 (a - k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt (by omega : a - k < 2 ^ 64)]
  omega
theorem w_shl (x n : Nat) (h : x * 2 ^ n < 2 ^ 64) :
    BitVec.ofNat 64 x <<< n = BitVec.ofNat 64 (x * 2 ^ n) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ofNat, Nat.shiftLeft_eq]
  have hx : x < 2 ^ 64 := by
    have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    calc x = x * 1 := by omega
      _ ≤ x * 2 ^ n := Nat.mul_le_mul_left _ this
      _ < _ := h
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt h]
theorem cp2_eval (b0 b1 : Nat) (h0 : 0xC0 ≤ b0) (h0' : b0 < 0xE0) (h1 : 0x80 ≤ b1) (h1' : b1 < 256) :
    ((BitVec.ofNat 64 b0 - 0xC0) <<< (6 : Nat)) + (BitVec.ofNat 64 b1 - 0x80) =
      BitVec.ofNat 64 ((b0 - 0xC0) * 64 + (b1 - 0x80)) := by
  rw [show (0xC0 : BitVec 64) = BitVec.ofNat 64 0xC0 from rfl, show (0x80 : BitVec 64) = BitVec.ofNat 64 0x80 from rfl,
    w_sub _ _ h0 (by omega), w_sub _ _ h1 (by omega), w_shl _ _ (by omega), BitVec.ofNat_add_ofNat]
  norm_num
theorem cp3_eval (b0 b1 b2 : Nat) (h0 : 0xE0 ≤ b0) (h0' : b0 < 0xF0) (h1 : 0x80 ≤ b1) (h1' : b1 < 256)
    (h2 : 0x80 ≤ b2) (h2' : b2 < 256) :
    ((BitVec.ofNat 64 b0 - 0xE0) <<< (12 : Nat)) + ((BitVec.ofNat 64 b1 - 0x80) <<< (6 : Nat)) + (BitVec.ofNat 64 b2 - 0x80) =
      BitVec.ofNat 64 ((b0 - 0xE0) * 4096 + (b1 - 0x80) * 64 + (b2 - 0x80)) := by
  rw [show (0xE0 : BitVec 64) = BitVec.ofNat 64 0xE0 from rfl, show (0x80 : BitVec 64) = BitVec.ofNat 64 0x80 from rfl,
    w_sub _ _ h0 (by omega), w_sub _ _ h1 (by omega), w_sub _ _ h2 (by omega), w_shl _ _ (by omega),
    w_shl _ _ (by omega), BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]
  norm_num
theorem cp4_eval (b0 b1 b2 b3 : Nat) (h0 : 0xF0 ≤ b0) (h0' : b0 < 256) (h1 : 0x80 ≤ b1) (h1' : b1 < 256)
    (h2 : 0x80 ≤ b2) (h2' : b2 < 256) (h3 : 0x80 ≤ b3) (h3' : b3 < 256) :
    ((BitVec.ofNat 64 b0 - 0xF0) <<< (18 : Nat)) + ((BitVec.ofNat 64 b1 - 0x80) <<< (12 : Nat)) +
      ((BitVec.ofNat 64 b2 - 0x80) <<< (6 : Nat)) + (BitVec.ofNat 64 b3 - 0x80) =
      BitVec.ofNat 64 ((b0 - 0xF0) * 262144 + (b1 - 0x80) * 4096 + (b2 - 0x80) * 64 + (b3 - 0x80)) := by
  rw [show (0xF0 : BitVec 64) = BitVec.ofNat 64 0xF0 from rfl, show (0x80 : BitVec 64) = BitVec.ofNat 64 0x80 from rfl,
    w_sub _ _ h0 (by omega), w_sub _ _ h1 (by omega), w_sub _ _ h2 (by omega), w_sub _ _ h3 (by omega),
    w_shl _ _ (by omega), w_shl _ _ (by omega), w_shl _ _ (by omega), BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat,
    BitVec.ofNat_add_ofNat]
  norm_num

def slC := ofString "slc"
def slO := ofString "slo"
def slN := ofString "sln"
def slB := ofString "slb"
def slI := ofString "sli"
def slL := ofString "sll"
def slP := ofString "slp"
def sl0 := ofString "sl0"
def sl1 := ofString "sl1"
def sl2 := ofString "sl2"
def sl3 := ofString "sl3"
def slCp := ofString "slcp"
def slK := ofString "slk"
def slR := ofString "slr"
def slT := ofString "slt"
def slH := ofString "slh"
def slF := ofString "slf"
def slX := ofString "slx"
def fSl := ofString "strLitSpine"

@[simp] theorem sl_slC_ne_slO : slC ≠ slO := by decide
@[simp] theorem sl_slC_ne_slN : slC ≠ slN := by decide
@[simp] theorem sl_slC_ne_slB : slC ≠ slB := by decide
@[simp] theorem sl_slC_ne_slI : slC ≠ slI := by decide
@[simp] theorem sl_slC_ne_slL : slC ≠ slL := by decide
@[simp] theorem sl_slC_ne_slP : slC ≠ slP := by decide
@[simp] theorem sl_slC_ne_sl0 : slC ≠ sl0 := by decide
@[simp] theorem sl_slC_ne_sl1 : slC ≠ sl1 := by decide
@[simp] theorem sl_slC_ne_sl2 : slC ≠ sl2 := by decide
@[simp] theorem sl_slC_ne_sl3 : slC ≠ sl3 := by decide
@[simp] theorem sl_slC_ne_slCp : slC ≠ slCp := by decide
@[simp] theorem sl_slC_ne_slK : slC ≠ slK := by decide
@[simp] theorem sl_slC_ne_slR : slC ≠ slR := by decide
@[simp] theorem sl_slC_ne_slT : slC ≠ slT := by decide
@[simp] theorem sl_slC_ne_slH : slC ≠ slH := by decide
@[simp] theorem sl_slC_ne_slF : slC ≠ slF := by decide
@[simp] theorem sl_slC_ne_slX : slC ≠ slX := by decide
@[simp] theorem sl_slC_ne_lKb : slC ≠ lKb := by decide
@[simp] theorem sl_lKb_ne_slC : lKb ≠ slC := by decide
@[simp] theorem sl_slO_ne_slC : slO ≠ slC := by decide
@[simp] theorem sl_slO_ne_slN : slO ≠ slN := by decide
@[simp] theorem sl_slO_ne_slB : slO ≠ slB := by decide
@[simp] theorem sl_slO_ne_slI : slO ≠ slI := by decide
@[simp] theorem sl_slO_ne_slL : slO ≠ slL := by decide
@[simp] theorem sl_slO_ne_slP : slO ≠ slP := by decide
@[simp] theorem sl_slO_ne_sl0 : slO ≠ sl0 := by decide
@[simp] theorem sl_slO_ne_sl1 : slO ≠ sl1 := by decide
@[simp] theorem sl_slO_ne_sl2 : slO ≠ sl2 := by decide
@[simp] theorem sl_slO_ne_sl3 : slO ≠ sl3 := by decide
@[simp] theorem sl_slO_ne_slCp : slO ≠ slCp := by decide
@[simp] theorem sl_slO_ne_slK : slO ≠ slK := by decide
@[simp] theorem sl_slO_ne_slR : slO ≠ slR := by decide
@[simp] theorem sl_slO_ne_slT : slO ≠ slT := by decide
@[simp] theorem sl_slO_ne_slH : slO ≠ slH := by decide
@[simp] theorem sl_slO_ne_slF : slO ≠ slF := by decide
@[simp] theorem sl_slO_ne_slX : slO ≠ slX := by decide
@[simp] theorem sl_slO_ne_lKb : slO ≠ lKb := by decide
@[simp] theorem sl_lKb_ne_slO : lKb ≠ slO := by decide
@[simp] theorem sl_slN_ne_slC : slN ≠ slC := by decide
@[simp] theorem sl_slN_ne_slO : slN ≠ slO := by decide
@[simp] theorem sl_slN_ne_slB : slN ≠ slB := by decide
@[simp] theorem sl_slN_ne_slI : slN ≠ slI := by decide
@[simp] theorem sl_slN_ne_slL : slN ≠ slL := by decide
@[simp] theorem sl_slN_ne_slP : slN ≠ slP := by decide
@[simp] theorem sl_slN_ne_sl0 : slN ≠ sl0 := by decide
@[simp] theorem sl_slN_ne_sl1 : slN ≠ sl1 := by decide
@[simp] theorem sl_slN_ne_sl2 : slN ≠ sl2 := by decide
@[simp] theorem sl_slN_ne_sl3 : slN ≠ sl3 := by decide
@[simp] theorem sl_slN_ne_slCp : slN ≠ slCp := by decide
@[simp] theorem sl_slN_ne_slK : slN ≠ slK := by decide
@[simp] theorem sl_slN_ne_slR : slN ≠ slR := by decide
@[simp] theorem sl_slN_ne_slT : slN ≠ slT := by decide
@[simp] theorem sl_slN_ne_slH : slN ≠ slH := by decide
@[simp] theorem sl_slN_ne_slF : slN ≠ slF := by decide
@[simp] theorem sl_slN_ne_slX : slN ≠ slX := by decide
@[simp] theorem sl_slN_ne_lKb : slN ≠ lKb := by decide
@[simp] theorem sl_lKb_ne_slN : lKb ≠ slN := by decide
@[simp] theorem sl_slB_ne_slC : slB ≠ slC := by decide
@[simp] theorem sl_slB_ne_slO : slB ≠ slO := by decide
@[simp] theorem sl_slB_ne_slN : slB ≠ slN := by decide
@[simp] theorem sl_slB_ne_slI : slB ≠ slI := by decide
@[simp] theorem sl_slB_ne_slL : slB ≠ slL := by decide
@[simp] theorem sl_slB_ne_slP : slB ≠ slP := by decide
@[simp] theorem sl_slB_ne_sl0 : slB ≠ sl0 := by decide
@[simp] theorem sl_slB_ne_sl1 : slB ≠ sl1 := by decide
@[simp] theorem sl_slB_ne_sl2 : slB ≠ sl2 := by decide
@[simp] theorem sl_slB_ne_sl3 : slB ≠ sl3 := by decide
@[simp] theorem sl_slB_ne_slCp : slB ≠ slCp := by decide
@[simp] theorem sl_slB_ne_slK : slB ≠ slK := by decide
@[simp] theorem sl_slB_ne_slR : slB ≠ slR := by decide
@[simp] theorem sl_slB_ne_slT : slB ≠ slT := by decide
@[simp] theorem sl_slB_ne_slH : slB ≠ slH := by decide
@[simp] theorem sl_slB_ne_slF : slB ≠ slF := by decide
@[simp] theorem sl_slB_ne_slX : slB ≠ slX := by decide
@[simp] theorem sl_slB_ne_lKb : slB ≠ lKb := by decide
@[simp] theorem sl_lKb_ne_slB : lKb ≠ slB := by decide
@[simp] theorem sl_slI_ne_slC : slI ≠ slC := by decide
@[simp] theorem sl_slI_ne_slO : slI ≠ slO := by decide
@[simp] theorem sl_slI_ne_slN : slI ≠ slN := by decide
@[simp] theorem sl_slI_ne_slB : slI ≠ slB := by decide
@[simp] theorem sl_slI_ne_slL : slI ≠ slL := by decide
@[simp] theorem sl_slI_ne_slP : slI ≠ slP := by decide
@[simp] theorem sl_slI_ne_sl0 : slI ≠ sl0 := by decide
@[simp] theorem sl_slI_ne_sl1 : slI ≠ sl1 := by decide
@[simp] theorem sl_slI_ne_sl2 : slI ≠ sl2 := by decide
@[simp] theorem sl_slI_ne_sl3 : slI ≠ sl3 := by decide
@[simp] theorem sl_slI_ne_slCp : slI ≠ slCp := by decide
@[simp] theorem sl_slI_ne_slK : slI ≠ slK := by decide
@[simp] theorem sl_slI_ne_slR : slI ≠ slR := by decide
@[simp] theorem sl_slI_ne_slT : slI ≠ slT := by decide
@[simp] theorem sl_slI_ne_slH : slI ≠ slH := by decide
@[simp] theorem sl_slI_ne_slF : slI ≠ slF := by decide
@[simp] theorem sl_slI_ne_slX : slI ≠ slX := by decide
@[simp] theorem sl_slI_ne_lKb : slI ≠ lKb := by decide
@[simp] theorem sl_lKb_ne_slI : lKb ≠ slI := by decide
@[simp] theorem sl_slL_ne_slC : slL ≠ slC := by decide
@[simp] theorem sl_slL_ne_slO : slL ≠ slO := by decide
@[simp] theorem sl_slL_ne_slN : slL ≠ slN := by decide
@[simp] theorem sl_slL_ne_slB : slL ≠ slB := by decide
@[simp] theorem sl_slL_ne_slI : slL ≠ slI := by decide
@[simp] theorem sl_slL_ne_slP : slL ≠ slP := by decide
@[simp] theorem sl_slL_ne_sl0 : slL ≠ sl0 := by decide
@[simp] theorem sl_slL_ne_sl1 : slL ≠ sl1 := by decide
@[simp] theorem sl_slL_ne_sl2 : slL ≠ sl2 := by decide
@[simp] theorem sl_slL_ne_sl3 : slL ≠ sl3 := by decide
@[simp] theorem sl_slL_ne_slCp : slL ≠ slCp := by decide
@[simp] theorem sl_slL_ne_slK : slL ≠ slK := by decide
@[simp] theorem sl_slL_ne_slR : slL ≠ slR := by decide
@[simp] theorem sl_slL_ne_slT : slL ≠ slT := by decide
@[simp] theorem sl_slL_ne_slH : slL ≠ slH := by decide
@[simp] theorem sl_slL_ne_slF : slL ≠ slF := by decide
@[simp] theorem sl_slL_ne_slX : slL ≠ slX := by decide
@[simp] theorem sl_slL_ne_lKb : slL ≠ lKb := by decide
@[simp] theorem sl_lKb_ne_slL : lKb ≠ slL := by decide
@[simp] theorem sl_slP_ne_slC : slP ≠ slC := by decide
@[simp] theorem sl_slP_ne_slO : slP ≠ slO := by decide
@[simp] theorem sl_slP_ne_slN : slP ≠ slN := by decide
@[simp] theorem sl_slP_ne_slB : slP ≠ slB := by decide
@[simp] theorem sl_slP_ne_slI : slP ≠ slI := by decide
@[simp] theorem sl_slP_ne_slL : slP ≠ slL := by decide
@[simp] theorem sl_slP_ne_sl0 : slP ≠ sl0 := by decide
@[simp] theorem sl_slP_ne_sl1 : slP ≠ sl1 := by decide
@[simp] theorem sl_slP_ne_sl2 : slP ≠ sl2 := by decide
@[simp] theorem sl_slP_ne_sl3 : slP ≠ sl3 := by decide
@[simp] theorem sl_slP_ne_slCp : slP ≠ slCp := by decide
@[simp] theorem sl_slP_ne_slK : slP ≠ slK := by decide
@[simp] theorem sl_slP_ne_slR : slP ≠ slR := by decide
@[simp] theorem sl_slP_ne_slT : slP ≠ slT := by decide
@[simp] theorem sl_slP_ne_slH : slP ≠ slH := by decide
@[simp] theorem sl_slP_ne_slF : slP ≠ slF := by decide
@[simp] theorem sl_slP_ne_slX : slP ≠ slX := by decide
@[simp] theorem sl_slP_ne_lKb : slP ≠ lKb := by decide
@[simp] theorem sl_lKb_ne_slP : lKb ≠ slP := by decide
@[simp] theorem sl_sl0_ne_slC : sl0 ≠ slC := by decide
@[simp] theorem sl_sl0_ne_slO : sl0 ≠ slO := by decide
@[simp] theorem sl_sl0_ne_slN : sl0 ≠ slN := by decide
@[simp] theorem sl_sl0_ne_slB : sl0 ≠ slB := by decide
@[simp] theorem sl_sl0_ne_slI : sl0 ≠ slI := by decide
@[simp] theorem sl_sl0_ne_slL : sl0 ≠ slL := by decide
@[simp] theorem sl_sl0_ne_slP : sl0 ≠ slP := by decide
@[simp] theorem sl_sl0_ne_sl1 : sl0 ≠ sl1 := by decide
@[simp] theorem sl_sl0_ne_sl2 : sl0 ≠ sl2 := by decide
@[simp] theorem sl_sl0_ne_sl3 : sl0 ≠ sl3 := by decide
@[simp] theorem sl_sl0_ne_slCp : sl0 ≠ slCp := by decide
@[simp] theorem sl_sl0_ne_slK : sl0 ≠ slK := by decide
@[simp] theorem sl_sl0_ne_slR : sl0 ≠ slR := by decide
@[simp] theorem sl_sl0_ne_slT : sl0 ≠ slT := by decide
@[simp] theorem sl_sl0_ne_slH : sl0 ≠ slH := by decide
@[simp] theorem sl_sl0_ne_slF : sl0 ≠ slF := by decide
@[simp] theorem sl_sl0_ne_slX : sl0 ≠ slX := by decide
@[simp] theorem sl_sl0_ne_lKb : sl0 ≠ lKb := by decide
@[simp] theorem sl_lKb_ne_sl0 : lKb ≠ sl0 := by decide
@[simp] theorem sl_sl1_ne_slC : sl1 ≠ slC := by decide
@[simp] theorem sl_sl1_ne_slO : sl1 ≠ slO := by decide
@[simp] theorem sl_sl1_ne_slN : sl1 ≠ slN := by decide
@[simp] theorem sl_sl1_ne_slB : sl1 ≠ slB := by decide
@[simp] theorem sl_sl1_ne_slI : sl1 ≠ slI := by decide
@[simp] theorem sl_sl1_ne_slL : sl1 ≠ slL := by decide
@[simp] theorem sl_sl1_ne_slP : sl1 ≠ slP := by decide
@[simp] theorem sl_sl1_ne_sl0 : sl1 ≠ sl0 := by decide
@[simp] theorem sl_sl1_ne_sl2 : sl1 ≠ sl2 := by decide
@[simp] theorem sl_sl1_ne_sl3 : sl1 ≠ sl3 := by decide
@[simp] theorem sl_sl1_ne_slCp : sl1 ≠ slCp := by decide
@[simp] theorem sl_sl1_ne_slK : sl1 ≠ slK := by decide
@[simp] theorem sl_sl1_ne_slR : sl1 ≠ slR := by decide
@[simp] theorem sl_sl1_ne_slT : sl1 ≠ slT := by decide
@[simp] theorem sl_sl1_ne_slH : sl1 ≠ slH := by decide
@[simp] theorem sl_sl1_ne_slF : sl1 ≠ slF := by decide
@[simp] theorem sl_sl1_ne_slX : sl1 ≠ slX := by decide
@[simp] theorem sl_sl1_ne_lKb : sl1 ≠ lKb := by decide
@[simp] theorem sl_lKb_ne_sl1 : lKb ≠ sl1 := by decide
@[simp] theorem sl_sl2_ne_slC : sl2 ≠ slC := by decide
@[simp] theorem sl_sl2_ne_slO : sl2 ≠ slO := by decide
@[simp] theorem sl_sl2_ne_slN : sl2 ≠ slN := by decide
@[simp] theorem sl_sl2_ne_slB : sl2 ≠ slB := by decide
@[simp] theorem sl_sl2_ne_slI : sl2 ≠ slI := by decide
@[simp] theorem sl_sl2_ne_slL : sl2 ≠ slL := by decide
@[simp] theorem sl_sl2_ne_slP : sl2 ≠ slP := by decide
@[simp] theorem sl_sl2_ne_sl0 : sl2 ≠ sl0 := by decide
@[simp] theorem sl_sl2_ne_sl1 : sl2 ≠ sl1 := by decide
@[simp] theorem sl_sl2_ne_sl3 : sl2 ≠ sl3 := by decide
@[simp] theorem sl_sl2_ne_slCp : sl2 ≠ slCp := by decide
@[simp] theorem sl_sl2_ne_slK : sl2 ≠ slK := by decide
@[simp] theorem sl_sl2_ne_slR : sl2 ≠ slR := by decide
@[simp] theorem sl_sl2_ne_slT : sl2 ≠ slT := by decide
@[simp] theorem sl_sl2_ne_slH : sl2 ≠ slH := by decide
@[simp] theorem sl_sl2_ne_slF : sl2 ≠ slF := by decide
@[simp] theorem sl_sl2_ne_slX : sl2 ≠ slX := by decide
@[simp] theorem sl_sl2_ne_lKb : sl2 ≠ lKb := by decide
@[simp] theorem sl_lKb_ne_sl2 : lKb ≠ sl2 := by decide
@[simp] theorem sl_sl3_ne_slC : sl3 ≠ slC := by decide
@[simp] theorem sl_sl3_ne_slO : sl3 ≠ slO := by decide
@[simp] theorem sl_sl3_ne_slN : sl3 ≠ slN := by decide
@[simp] theorem sl_sl3_ne_slB : sl3 ≠ slB := by decide
@[simp] theorem sl_sl3_ne_slI : sl3 ≠ slI := by decide
@[simp] theorem sl_sl3_ne_slL : sl3 ≠ slL := by decide
@[simp] theorem sl_sl3_ne_slP : sl3 ≠ slP := by decide
@[simp] theorem sl_sl3_ne_sl0 : sl3 ≠ sl0 := by decide
@[simp] theorem sl_sl3_ne_sl1 : sl3 ≠ sl1 := by decide
@[simp] theorem sl_sl3_ne_sl2 : sl3 ≠ sl2 := by decide
@[simp] theorem sl_sl3_ne_slCp : sl3 ≠ slCp := by decide
@[simp] theorem sl_sl3_ne_slK : sl3 ≠ slK := by decide
@[simp] theorem sl_sl3_ne_slR : sl3 ≠ slR := by decide
@[simp] theorem sl_sl3_ne_slT : sl3 ≠ slT := by decide
@[simp] theorem sl_sl3_ne_slH : sl3 ≠ slH := by decide
@[simp] theorem sl_sl3_ne_slF : sl3 ≠ slF := by decide
@[simp] theorem sl_sl3_ne_slX : sl3 ≠ slX := by decide
@[simp] theorem sl_sl3_ne_lKb : sl3 ≠ lKb := by decide
@[simp] theorem sl_lKb_ne_sl3 : lKb ≠ sl3 := by decide
@[simp] theorem sl_slCp_ne_slC : slCp ≠ slC := by decide
@[simp] theorem sl_slCp_ne_slO : slCp ≠ slO := by decide
@[simp] theorem sl_slCp_ne_slN : slCp ≠ slN := by decide
@[simp] theorem sl_slCp_ne_slB : slCp ≠ slB := by decide
@[simp] theorem sl_slCp_ne_slI : slCp ≠ slI := by decide
@[simp] theorem sl_slCp_ne_slL : slCp ≠ slL := by decide
@[simp] theorem sl_slCp_ne_slP : slCp ≠ slP := by decide
@[simp] theorem sl_slCp_ne_sl0 : slCp ≠ sl0 := by decide
@[simp] theorem sl_slCp_ne_sl1 : slCp ≠ sl1 := by decide
@[simp] theorem sl_slCp_ne_sl2 : slCp ≠ sl2 := by decide
@[simp] theorem sl_slCp_ne_sl3 : slCp ≠ sl3 := by decide
@[simp] theorem sl_slCp_ne_slK : slCp ≠ slK := by decide
@[simp] theorem sl_slCp_ne_slR : slCp ≠ slR := by decide
@[simp] theorem sl_slCp_ne_slT : slCp ≠ slT := by decide
@[simp] theorem sl_slCp_ne_slH : slCp ≠ slH := by decide
@[simp] theorem sl_slCp_ne_slF : slCp ≠ slF := by decide
@[simp] theorem sl_slCp_ne_slX : slCp ≠ slX := by decide
@[simp] theorem sl_slCp_ne_lKb : slCp ≠ lKb := by decide
@[simp] theorem sl_lKb_ne_slCp : lKb ≠ slCp := by decide
@[simp] theorem sl_slK_ne_slC : slK ≠ slC := by decide
@[simp] theorem sl_slK_ne_slO : slK ≠ slO := by decide
@[simp] theorem sl_slK_ne_slN : slK ≠ slN := by decide
@[simp] theorem sl_slK_ne_slB : slK ≠ slB := by decide
@[simp] theorem sl_slK_ne_slI : slK ≠ slI := by decide
@[simp] theorem sl_slK_ne_slL : slK ≠ slL := by decide
@[simp] theorem sl_slK_ne_slP : slK ≠ slP := by decide
@[simp] theorem sl_slK_ne_sl0 : slK ≠ sl0 := by decide
@[simp] theorem sl_slK_ne_sl1 : slK ≠ sl1 := by decide
@[simp] theorem sl_slK_ne_sl2 : slK ≠ sl2 := by decide
@[simp] theorem sl_slK_ne_sl3 : slK ≠ sl3 := by decide
@[simp] theorem sl_slK_ne_slCp : slK ≠ slCp := by decide
@[simp] theorem sl_slK_ne_slR : slK ≠ slR := by decide
@[simp] theorem sl_slK_ne_slT : slK ≠ slT := by decide
@[simp] theorem sl_slK_ne_slH : slK ≠ slH := by decide
@[simp] theorem sl_slK_ne_slF : slK ≠ slF := by decide
@[simp] theorem sl_slK_ne_slX : slK ≠ slX := by decide
@[simp] theorem sl_slK_ne_lKb : slK ≠ lKb := by decide
@[simp] theorem sl_lKb_ne_slK : lKb ≠ slK := by decide
@[simp] theorem sl_slR_ne_slC : slR ≠ slC := by decide
@[simp] theorem sl_slR_ne_slO : slR ≠ slO := by decide
@[simp] theorem sl_slR_ne_slN : slR ≠ slN := by decide
@[simp] theorem sl_slR_ne_slB : slR ≠ slB := by decide
@[simp] theorem sl_slR_ne_slI : slR ≠ slI := by decide
@[simp] theorem sl_slR_ne_slL : slR ≠ slL := by decide
@[simp] theorem sl_slR_ne_slP : slR ≠ slP := by decide
@[simp] theorem sl_slR_ne_sl0 : slR ≠ sl0 := by decide
@[simp] theorem sl_slR_ne_sl1 : slR ≠ sl1 := by decide
@[simp] theorem sl_slR_ne_sl2 : slR ≠ sl2 := by decide
@[simp] theorem sl_slR_ne_sl3 : slR ≠ sl3 := by decide
@[simp] theorem sl_slR_ne_slCp : slR ≠ slCp := by decide
@[simp] theorem sl_slR_ne_slK : slR ≠ slK := by decide
@[simp] theorem sl_slR_ne_slT : slR ≠ slT := by decide
@[simp] theorem sl_slR_ne_slH : slR ≠ slH := by decide
@[simp] theorem sl_slR_ne_slF : slR ≠ slF := by decide
@[simp] theorem sl_slR_ne_slX : slR ≠ slX := by decide
@[simp] theorem sl_slR_ne_lKb : slR ≠ lKb := by decide
@[simp] theorem sl_lKb_ne_slR : lKb ≠ slR := by decide
@[simp] theorem sl_slT_ne_slC : slT ≠ slC := by decide
@[simp] theorem sl_slT_ne_slO : slT ≠ slO := by decide
@[simp] theorem sl_slT_ne_slN : slT ≠ slN := by decide
@[simp] theorem sl_slT_ne_slB : slT ≠ slB := by decide
@[simp] theorem sl_slT_ne_slI : slT ≠ slI := by decide
@[simp] theorem sl_slT_ne_slL : slT ≠ slL := by decide
@[simp] theorem sl_slT_ne_slP : slT ≠ slP := by decide
@[simp] theorem sl_slT_ne_sl0 : slT ≠ sl0 := by decide
@[simp] theorem sl_slT_ne_sl1 : slT ≠ sl1 := by decide
@[simp] theorem sl_slT_ne_sl2 : slT ≠ sl2 := by decide
@[simp] theorem sl_slT_ne_sl3 : slT ≠ sl3 := by decide
@[simp] theorem sl_slT_ne_slCp : slT ≠ slCp := by decide
@[simp] theorem sl_slT_ne_slK : slT ≠ slK := by decide
@[simp] theorem sl_slT_ne_slR : slT ≠ slR := by decide
@[simp] theorem sl_slT_ne_slH : slT ≠ slH := by decide
@[simp] theorem sl_slT_ne_slF : slT ≠ slF := by decide
@[simp] theorem sl_slT_ne_slX : slT ≠ slX := by decide
@[simp] theorem sl_slT_ne_lKb : slT ≠ lKb := by decide
@[simp] theorem sl_lKb_ne_slT : lKb ≠ slT := by decide
@[simp] theorem sl_slH_ne_slC : slH ≠ slC := by decide
@[simp] theorem sl_slH_ne_slO : slH ≠ slO := by decide
@[simp] theorem sl_slH_ne_slN : slH ≠ slN := by decide
@[simp] theorem sl_slH_ne_slB : slH ≠ slB := by decide
@[simp] theorem sl_slH_ne_slI : slH ≠ slI := by decide
@[simp] theorem sl_slH_ne_slL : slH ≠ slL := by decide
@[simp] theorem sl_slH_ne_slP : slH ≠ slP := by decide
@[simp] theorem sl_slH_ne_sl0 : slH ≠ sl0 := by decide
@[simp] theorem sl_slH_ne_sl1 : slH ≠ sl1 := by decide
@[simp] theorem sl_slH_ne_sl2 : slH ≠ sl2 := by decide
@[simp] theorem sl_slH_ne_sl3 : slH ≠ sl3 := by decide
@[simp] theorem sl_slH_ne_slCp : slH ≠ slCp := by decide
@[simp] theorem sl_slH_ne_slK : slH ≠ slK := by decide
@[simp] theorem sl_slH_ne_slR : slH ≠ slR := by decide
@[simp] theorem sl_slH_ne_slT : slH ≠ slT := by decide
@[simp] theorem sl_slH_ne_slF : slH ≠ slF := by decide
@[simp] theorem sl_slH_ne_slX : slH ≠ slX := by decide
@[simp] theorem sl_slH_ne_lKb : slH ≠ lKb := by decide
@[simp] theorem sl_lKb_ne_slH : lKb ≠ slH := by decide
@[simp] theorem sl_slF_ne_slC : slF ≠ slC := by decide
@[simp] theorem sl_slF_ne_slO : slF ≠ slO := by decide
@[simp] theorem sl_slF_ne_slN : slF ≠ slN := by decide
@[simp] theorem sl_slF_ne_slB : slF ≠ slB := by decide
@[simp] theorem sl_slF_ne_slI : slF ≠ slI := by decide
@[simp] theorem sl_slF_ne_slL : slF ≠ slL := by decide
@[simp] theorem sl_slF_ne_slP : slF ≠ slP := by decide
@[simp] theorem sl_slF_ne_sl0 : slF ≠ sl0 := by decide
@[simp] theorem sl_slF_ne_sl1 : slF ≠ sl1 := by decide
@[simp] theorem sl_slF_ne_sl2 : slF ≠ sl2 := by decide
@[simp] theorem sl_slF_ne_sl3 : slF ≠ sl3 := by decide
@[simp] theorem sl_slF_ne_slCp : slF ≠ slCp := by decide
@[simp] theorem sl_slF_ne_slK : slF ≠ slK := by decide
@[simp] theorem sl_slF_ne_slR : slF ≠ slR := by decide
@[simp] theorem sl_slF_ne_slT : slF ≠ slT := by decide
@[simp] theorem sl_slF_ne_slH : slF ≠ slH := by decide
@[simp] theorem sl_slF_ne_slX : slF ≠ slX := by decide
@[simp] theorem sl_slF_ne_lKb : slF ≠ lKb := by decide
@[simp] theorem sl_lKb_ne_slF : lKb ≠ slF := by decide
@[simp] theorem sl_slX_ne_slC : slX ≠ slC := by decide
@[simp] theorem sl_slX_ne_slO : slX ≠ slO := by decide
@[simp] theorem sl_slX_ne_slN : slX ≠ slN := by decide
@[simp] theorem sl_slX_ne_slB : slX ≠ slB := by decide
@[simp] theorem sl_slX_ne_slI : slX ≠ slI := by decide
@[simp] theorem sl_slX_ne_slL : slX ≠ slL := by decide
@[simp] theorem sl_slX_ne_slP : slX ≠ slP := by decide
@[simp] theorem sl_slX_ne_sl0 : slX ≠ sl0 := by decide
@[simp] theorem sl_slX_ne_sl1 : slX ≠ sl1 := by decide
@[simp] theorem sl_slX_ne_sl2 : slX ≠ sl2 := by decide
@[simp] theorem sl_slX_ne_sl3 : slX ≠ sl3 := by decide
@[simp] theorem sl_slX_ne_slCp : slX ≠ slCp := by decide
@[simp] theorem sl_slX_ne_slK : slX ≠ slK := by decide
@[simp] theorem sl_slX_ne_slR : slX ≠ slR := by decide
@[simp] theorem sl_slX_ne_slT : slX ≠ slT := by decide
@[simp] theorem sl_slX_ne_slH : slX ≠ slH := by decide
@[simp] theorem sl_slX_ne_slF : slX ≠ slF := by decide
@[simp] theorem sl_slX_ne_lKb : slX ≠ lKb := by decide
@[simp] theorem sl_lKb_ne_slX : lKb ≠ slX := by decide

def slParams : List MlS := [slC, slO, slN, slB, slI, slL]
def slLocals : List MlS := [slP, sl0, sl1, sl2, sl3, slCp, slK, slR, slT, slH, slF, slX]

def slTail : ProgHOL 64 :=
  .seq (.call (some (some (.local, slR), none)) fSl [vv slC, vv slO, vv slN, vv slB, .op .add [vv slI, vv slK], vv slL])
  (.seq (.call (some (some (.local, slT), none)) fLitW [vv slCp])
  (.seq (.call (some (some (.local, slH), none)) fInternApp [vv slO, vv slT])
  (.seq (.call (some (some (.local, slF), none)) fInternApp [vv slC, vv slH])
  (.seq (.call (some (some (.local, slX), none)) fInternApp [vv slF, vv slR])
  (.return (vv slX))))))

def subE (x : MlS) (k : BitVec 64) : ExpHOL 64 := .op .sub [vv x, .const k]

def slCore : ProgHOL 64 :=
  .ite (.cmp .equal (vv slI) (vv slL)) (.return (vv slN))
  (.seq (.assign .local slP (.op .add [vv slB, .shift .lsl (.op .add [vv slI, .const 1]) (.const 3)]))
  (.seq (.assign .local sl0 (.load .one (vv slP)))
  (.ite (.cmp .lower (vv sl0) (.const 0x80))
    (.seq (.assign .local slCp (vv sl0)) (.seq (.assign .local slK (.const 1)) slTail))
  (.seq (.assign .local sl1 (.load .one (.op .add [vv slP, .const 8])))
  (.ite (.cmp .lower (vv sl0) (.const 0xE0))
    (.seq (.assign .local slCp (.op .add [.shift .lsl (subE sl0 0xC0) (.const 6), subE sl1 0x80]))
      (.seq (.assign .local slK (.const 2)) slTail))
  (.seq (.assign .local sl2 (.load .one (.op .add [vv slP, .const 16])))
  (.ite (.cmp .lower (vv sl0) (.const 0xF0))
    (.seq (.assign .local slCp (.op .add [.op .add [.shift .lsl (subE sl0 0xE0) (.const 12),
        .shift .lsl (subE sl1 0x80) (.const 6)], subE sl2 0x80]))
      (.seq (.assign .local slK (.const 3)) slTail))
  (.seq (.assign .local sl3 (.load .one (.op .add [vv slP, .const 24])))
  (.seq (.assign .local slCp (.op .add [.op .add [.op .add [.shift .lsl (subE sl0 0xF0) (.const 18),
        .shift .lsl (subE sl1 0x80) (.const 12)], .shift .lsl (subE sl2 0x80) (.const 6)], subE sl3 0x80]))
    (.seq (.assign .local slK (.const 4)) slTail))))))))))

def slBody : ProgHOL 64 := prologue slLocals slCore

section
variable {σ : Type}

theorem sl_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ slLocals → (ctxEnv C ++ slParams.zip vals).get x = none :=
  Knot.params_none C slLocals slParams vals (by decide) (by decide)

/-- The code the spine calls. -/
structure SlCodes (C : Ctx) : Prop where
  sl : C.code.lookup fSl = some (slParams.map (fun p => (p, ShapeHOL.one)), slBody, .one)
  lw : C.code.lookup fLitW = some ([(wV, .one)], lwBody C, .one)
  lb : C.code.lookup fLitB = some ([(iLx, .one)], litBlkBody C, .one)
  ia : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)

theorem sl_tail (ra : ConPanqueque.Hash.RuntimeAssumptions) {C : Ctx} (hok : CtxOK C) (hc : SlCodes C)
    {s : AState} {Γ : Env} {M : Mem} (cons ofN nilE : EIdx) (c : Char) (cs : List Char) (ob i k len : Nat)
    (hC : Γ.get slC = some (Enc.idxW cons)) (hO : Γ.get slO = some (Enc.idxW ofN))
    (hN : Γ.get slN = some (Enc.idxW nilE)) (hB : Γ.get slB = some (cellA C ob))
    (hI : Γ.get slI = some (BitVec.ofNat 64 i)) (hK : Γ.get slK = some (BitVec.ofNat 64 k))
    (hL : Γ.get slL = some (BitVec.ofNat 64 len)) (hCp : Γ.get slCp = some (BitVec.ofNat 64 c.toNat))
    (hrest : SpecR (σ := σ) (Pre C s (slParams.zip [Enc.idxW cons, Enc.idxW ofN, Enc.idxW nilE, cellA C ob,
      BitVec.ofNat 64 (i + k), BitVec.ofNat 64 len])) slBody s (strLitConsSpine cons ofN nilE cs) (PostK C)) :
    SpecR (σ := σ) (Inv C s Γ M (ctxLocals ++ slLocals)) slTail s (strLitConsSpine cons ofN nilE (c :: cs))
      (PostK C) := by
  rw [strLitConsSpine]
  refine specR_callKH slR fSl slParams [vv slC, vv slO, vv slN, vv slB, .op .add [vv slI, vv slK], vv slL] slBody
    [Enc.idxW cons, Enc.idxW ofN, Enc.idxW nilE, cellA C ob, BitVec.ofNat 64 (i + k), BitVec.ofNat 64 len]
    (by decide) rfl (by decide) hc.sl
    ⟨by simpa using hC, by simpa using hO, by simpa using hN, by simpa using hB,
      by simp [sev, hI, hK, BitVec.ofNat_add_ofNat], by simpa using hL, trivial⟩ hrest (fun rest s1 H1 hp1 => ?_)
  refine specR_callKH (C := ctxH C H1) slT fLitW [wV] [vv slCp] (lwBody C) [BitVec.ofNat 64 c.toNat] (by decide) rfl
    (by decide) hc.lw ⟨by simp [hCp], trivial⟩
    (lw_spec ra (ctxH C H1) (ctxOK_H hok _) hc.lb s1 c.toNat (by have := cp_lt c; omega)) (fun lit s2 H2 hp2 => ?_)
  refine specR_internAppI (C := ctxH (ctxH C H1) H2) ra (ctxOK_H (ctxOK_H hok _) _) hc.ia slH (vv slO) (vv slT) ofN lit
    (by decide) (by simp [hO]) (by simp) (fun ch s3 => ?_)
  refine specR_internAppI (C := ctxH (ctxH C H1) H2) ra (ctxOK_H (ctxOK_H hok _) _) hc.ia slF (vv slC) (vv slH) cons ch
    (by decide) (by simp [hC]) (by simp) (fun f s4 => ?_)
  refine specR_congr (m' := internAppE f rest >>= fun r => pure r) (by simp [internAppE]) ?_
  refine specR_internAppI (C := ctxH (ctxH C H1) H2) ra (ctxOK_H (ctxOK_H hok _) _) hc.ia slX (vv slF) (vv slR) f rest
    (by decide) (by simp) (by simp) (fun x s5 => ?_)
  exact specR_returnI _ (Enc.idxW x) (by simp) (fun t ht => ⟨H2, hp1.trans hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

section
variable {σ : Type}

theorem slP_eq (C : Ctx) (ob i : Nat) (hi : i < 2 ^ 58) :
    cellA C ob + (BitVec.ofNat 64 i + 1) <<< (3 : Nat) = cellA C (ob + 1 + i) := by
  rw [show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat, w_shl _ _ (by omega),
    show (i + 1) * 2 ^ 3 = 8 * (1 + i) by omega, ExPre.cellA_off, Nat.add_assoc]

theorem slP_eq' (C : Ctx) (ob i : Nat) (hi : i < 2 ^ 58) :
    cellA C ob + (BitVec.ofNat 64 i <<< (3 : Nat) + 8#64) = cellA C (ob + 1 + i) := by
  rw [w_shl _ _ (by omega), show (8#64 : BitVec 64) = BitVec.ofNat 64 8 from rfl, BitVec.ofNat_add_ofNat,
    show i * 2 ^ 3 + 8 = 8 * (1 + i) by omega, ExPre.cellA_off, Nat.add_assoc]

theorem cellA_16 (C : Ctx) (o : Nat) : cellA C o + 16 = cellA C (o + 2) := by
  rw [show (16 : BitVec 64) = BitVec.ofNat 64 (8 * 2) from rfl, ExPre.cellA_off]

theorem cellA_24 (C : Ctx) (o : Nat) : cellA C o + 24 = cellA C (o + 3) := by
  rw [show (24 : BitVec 64) = BitVec.ofNat 64 (8 * 3) from rfl, ExPre.cellA_off]

theorem lt_word (b k : Nat) (hb : b < 2 ^ 64) (hk : k < 2 ^ 64) :
    (BitVec.ofNat 64 b < BitVec.ofNat 64 k) ↔ b < k := word_lt_iff b k hb hk

theorem sl_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : SlCodes C)
    (bs : List Nat) (ob : Nat) (hb : BlkAt C.H ob (bs.map (BitVec.ofNat 64))) (hlen : bs.length < 2 ^ 58)
    (cons ofN nilE : EIdx) :
    ∀ (cs : List Char) (i : Nat) (s : AState),
      bs.drop i = (cs.flatMap String.utf8EncodeChar).map UInt8.toNat → i ≤ bs.length →
      SpecR (σ := σ) (Pre C s (slParams.zip [Enc.idxW cons, Enc.idxW ofN, Enc.idxW nilE, cellA C ob,
        BitVec.ofNat 64 i, BitVec.ofNat 64 bs.length])) slBody s (strLitConsSpine cons ofN nilE cs) (PostK C) := by
  intro cs
  induction cs with
  | nil =>
    intro i s hd hi
    have hi' : i = bs.length := by have := congrArg List.length hd; simp at this; omega
    subst hi'
    refine specR_prologue (Knot.postK_locals C) (sl_none C _) ?_
    unfold slCore
    rw [strLitConsSpine]
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, slParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ (Enc.idxW nilE) (by simp +decide [Env.get, slParams, ctxEnv])
      (fun t ht => ⟨C.H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | cons c cs ih =>
    intro i s hd hi
    rw [List.flatMap_cons, List.map_append] at hd
    have hlD : (bs.drop i).length = bs.length - i := List.length_drop
    have hget : ∀ j b, ((String.utf8EncodeChar c).map UInt8.toNat)[j]? = some b →
        C.H[ob + 1 + i + j]? = some (BitVec.ofNat 64 b) := by
      intro j b hj
      have hj' : (bs.drop i)[j]? = some b := by
        rw [hd, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hj).1]; exact hj
      rw [List.getElem?_drop] at hj'
      obtain ⟨hlt, heq⟩ := List.getElem?_eq_some_iff.mp hj'
      have := hb.2 (i + j) (by simpa using hlt)
      rw [Nat.add_assoc]; simpa [heq] using this
    have hdrop : ∀ k, ((String.utf8EncodeChar c).map UInt8.toNat).length = k →
        bs.drop (i + k) = (cs.flatMap String.utf8EncodeChar).map UInt8.toNat := by
      intro k hk
      rw [← List.drop_drop, hd, List.drop_left' hk]
    have hsh := encShape c
    have hpos : 0 < ((String.utf8EncodeChar c).map UInt8.toNat).length := by
      rcases hsh with ⟨_, h, _⟩ | ⟨_, _, h, _⟩ | ⟨_, _, _, h, _⟩ | ⟨_, _, _, _, h, _⟩ <;> rw [h] <;> simp
    have hlenL : ((String.utf8EncodeChar c).map UInt8.toNat).length ≤ bs.length - i := by
      rw [← hlD, hd, List.length_append]; omega
    have hil : i < bs.length := by omega
    refine specR_prologue (Knot.postK_locals C) (sl_none C _) ?_
    unfold slCore
    have hne : BitVec.ofNat 64 i ≠ BitVec.ofNat 64 bs.length := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, slParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI slP _ (cellA C (ob + 1 + i)) (by decide)
      (by simp +decide [sev, Env.get, slParams, ctxEnv]; exact slP_eq' C ob i (by omega)) ?_
    rcases hsh with ⟨b0, hL, h0, hcp⟩ | ⟨b0, b1, hL, h0, h0', h0c, h1, h1', hcp⟩ |
      ⟨b0, b1, b2, hL, h0, h0', h0'', h1, h1', h2, h2', hcp⟩ |
      ⟨b0, b1, b2, b3, hL, h0, h0', h0'', h0b, h1, h1', h2, h2', h3, h3', hcp⟩
    · -- one byte
      refine UD.specR_heapLoadI' sl0 (vv slP) (ob + 1 + i) (BitVec.ofNat 64 b0)
        (by simpa using hget 0 b0 (by rw [hL]; rfl)) (by decide) (by simp) ?_
      refine specR_ifI _ 1 (by
          simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
          exact (lt_word b0 128 (by omega) (by omega)).mpr h0) (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_assignI slCp (vv sl0) (BitVec.ofNat 64 c.toNat) (by decide) (by simp [hcp]) ?_
      refine specR_assignI slK (.const 1) (BitVec.ofNat 64 1) (by decide) rfl ?_
      exact sl_tail ra hok hc cons ofN nilE c cs ob i 1 bs.length
        (by simp +decide [Env.get, slParams, ctxEnv]) (by simp +decide [Env.get, slParams, ctxEnv])
        (by simp +decide [Env.get, slParams, ctxEnv]) (by simp +decide [Env.get, slParams, ctxEnv])
        (by simp +decide [Env.get, slParams, ctxEnv]) (by simp) (by simp +decide [Env.get, slParams, ctxEnv])
        (by simp) (ih (i + 1) s (hdrop 1 (by rw [hL]; rfl)) (by rw [hL] at hlenL; simp at hlenL; omega))
    · -- two bytes
      refine UD.specR_heapLoadI' sl0 (vv slP) (ob + 1 + i) (BitVec.ofNat 64 b0)
        (by simpa using hget 0 b0 (by rw [hL]; rfl)) (by decide) (by simp) ?_
      refine specR_ifI _ 0 (by
          simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
          omega) (fun h => absurd rfl h) (fun _ => ?_)
      refine UD.specR_heapLoadI' sl1 _ (ob + 1 + i + 1) (BitVec.ofNat 64 b1)
        (hget 1 b1 (by rw [hL]; rfl)) (by decide) (by simp [sev]; exact cellA_add8 C _) ?_
      refine specR_ifI _ 1 (by
          simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
          exact (lt_word b0 0xE0 (by omega) (by omega)).mpr h0') (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_assignI slCp _ (BitVec.ofNat 64 c.toNat) (by decide)
        (by simp [sev, subE]; rw [hcp]; exact cp2_eval b0 b1 h0c h0' h1 h1') ?_
      refine specR_assignI slK (.const 2) (BitVec.ofNat 64 2) (by decide) rfl ?_
      exact sl_tail ra hok hc cons ofN nilE c cs ob i 2 bs.length
        (by simp +decide [Env.get, slParams, ctxEnv]) (by simp +decide [Env.get, slParams, ctxEnv])
        (by simp +decide [Env.get, slParams, ctxEnv]) (by simp +decide [Env.get, slParams, ctxEnv])
        (by simp +decide [Env.get, slParams, ctxEnv]) (by simp) (by simp +decide [Env.get, slParams, ctxEnv])
        (by simp) (ih (i + 2) s (hdrop 2 (by rw [hL]; rfl)) (by rw [hL] at hlenL; simp at hlenL; omega))
    · -- three bytes
      refine UD.specR_heapLoadI' sl0 (vv slP) (ob + 1 + i) (BitVec.ofNat 64 b0)
        (by simpa using hget 0 b0 (by rw [hL]; rfl)) (by decide) (by simp) ?_
      refine specR_ifI _ 0 (by
          simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
          omega) (fun h => absurd rfl h) (fun _ => ?_)
      refine UD.specR_heapLoadI' sl1 _ (ob + 1 + i + 1) (BitVec.ofNat 64 b1)
        (hget 1 b1 (by rw [hL]; rfl)) (by decide) (by simp [sev]; exact cellA_add8 C _) ?_
      refine specR_ifI _ 0 (by
          simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
          omega) (fun h => absurd rfl h) (fun _ => ?_)
      refine UD.specR_heapLoadI' sl2 _ (ob + 1 + i + 2) (BitVec.ofNat 64 b2)
        (hget 2 b2 (by rw [hL]; rfl)) (by decide) (by simp [sev]; exact cellA_16 C _) ?_
      refine specR_ifI _ 1 (by
          simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
          exact (lt_word b0 0xF0 (by omega) (by omega)).mpr h0'') (fun _ => ?_) (fun h => absurd h (by decide))
      refine specR_assignI slCp _ (BitVec.ofNat 64 c.toNat) (by decide)
        (by simp [sev, subE]; rw [hcp]; exact cp3_eval b0 b1 b2 (by omega) h0'' h1 h1' h2 h2') ?_
      refine specR_assignI slK (.const 3) (BitVec.ofNat 64 3) (by decide) rfl ?_
      exact sl_tail ra hok hc cons ofN nilE c cs ob i 3 bs.length
        (by simp +decide [Env.get, slParams, ctxEnv]) (by simp +decide [Env.get, slParams, ctxEnv])
        (by simp +decide [Env.get, slParams, ctxEnv]) (by simp +decide [Env.get, slParams, ctxEnv])
        (by simp +decide [Env.get, slParams, ctxEnv]) (by simp) (by simp +decide [Env.get, slParams, ctxEnv])
        (by simp) (ih (i + 3) s (hdrop 3 (by rw [hL]; rfl)) (by rw [hL] at hlenL; simp at hlenL; omega))
    · -- four bytes
      refine UD.specR_heapLoadI' sl0 (vv slP) (ob + 1 + i) (BitVec.ofNat 64 b0)
        (by simpa using hget 0 b0 (by rw [hL]; rfl)) (by decide) (by simp) ?_
      refine specR_ifI _ 0 (by
          simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
          omega) (fun h => absurd rfl h) (fun _ => ?_)
      refine UD.specR_heapLoadI' sl1 _ (ob + 1 + i + 1) (BitVec.ofNat 64 b1)
        (hget 1 b1 (by rw [hL]; rfl)) (by decide) (by simp [sev]; exact cellA_add8 C _) ?_
      refine specR_ifI _ 0 (by
          simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
          omega) (fun h => absurd rfl h) (fun _ => ?_)
      refine UD.specR_heapLoadI' sl2 _ (ob + 1 + i + 2) (BitVec.ofNat 64 b2)
        (hget 2 b2 (by rw [hL]; rfl)) (by decide) (by simp [sev]; exact cellA_16 C _) ?_
      refine specR_ifI _ 0 (by
          simp [sev, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
          omega) (fun h => absurd rfl h) (fun _ => ?_)
      refine UD.specR_heapLoadI' sl3 _ (ob + 1 + i + 3) (BitVec.ofNat 64 b3)
        (hget 3 b3 (by rw [hL]; rfl)) (by decide) (by simp [sev]; exact cellA_24 C _) ?_
      refine specR_assignI slCp _ (BitVec.ofNat 64 c.toNat) (by decide)
        (by simp [sev, subE]; rw [hcp]; exact cp4_eval b0 b1 b2 b3 (by omega) h0b h1 h1' h2 h2' h3 h3') ?_
      refine specR_assignI slK (.const 4) (BitVec.ofNat 64 4) (by decide) rfl ?_
      exact sl_tail ra hok hc cons ofN nilE c cs ob i 4 bs.length
        (by simp +decide [Env.get, slParams, ctxEnv]) (by simp +decide [Env.get, slParams, ctxEnv])
        (by simp +decide [Env.get, slParams, ctxEnv]) (by simp +decide [Env.get, slParams, ctxEnv])
        (by simp +decide [Env.get, slParams, ctxEnv]) (by simp) (by simp +decide [Env.get, slParams, ctxEnv])
        (by simp) (ih (i + 4) s (hdrop 4 (by rw [hL]; rfl)) (by rw [hL] at hlenL; simp at hlenL; omega))

end

end ConPanqueque.T.Str
