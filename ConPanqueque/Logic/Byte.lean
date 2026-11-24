import ConPanqueque.Logic.Basic

/-! # Byte reads

The input buffer is bytes packed little-endian, eight to a word, in Pancake memory.  `BytesAt t a bs`
says byte `i` of `bs` is byte `i % 8` of the word at `a + 8 * (i / 8)`, which is in the memory
domain.  A byte is read as `byteE`: the word holding it, shifted and masked, so the read is
little-endian whatever the machine's byte order is (no `be` fact is needed anywhere);
`eval_byteE_bytes` is the one rule the scanners need. -/

namespace ConPanqueque.Logic
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Byte `k` (little-endian) of a word. -/
def byteW (w : BitVec 64) (k : Nat) : Nat := (w.toNat / 256 ^ k) % 256

theorem byteW_lt (w : BitVec 64) (k : Nat) : byteW w k < 256 := Nat.mod_lt _ (by decide)

/-- The buffer `bs` at the 8-aligned address `a`, little-endian. -/
def BytesAt {σ : Type} (t : PanSemStateFiniteExact 64 σ) (a : BitVec 64) (bs : List UInt8) : Prop :=
  True ∧ a.toNat % 8 = 0 ∧ a.toNat + bs.length < 2 ^ 64 ∧
    ∀ i (hi : i < bs.length), ∃ w, t.memory (a + BitVec.ofNat 64 (8 * (i / 8))) = .word w ∧
      t.memaddrs (a + BitVec.ofNat 64 (8 * (i / 8))) ∧ byteW w (i % 8) = bs[i].toNat

theorem shr3shl3 (j : Nat) (hj : j < 2 ^ 64) :
    (BitVec.ofNat 64 j >>> (3 : Nat)) <<< (3 : Nat) = BitVec.ofNat 64 (8 * (j / 8)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]
  rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
  have : j / 2 ^ 3 * 2 ^ 3 < 2 ^ 64 := by have := Nat.div_mul_le_self j (2 ^ 3); omega
  rw [Nat.mod_eq_of_lt this]; omega

theorem and7shl3 (j : Nat) (hj : j < 2 ^ 64) :
    ((BitVec.ofNat 64 j &&& 7) <<< (3 : Nat)).toNat = 8 * (j % 8) := by
  simp only [BitVec.toNat_shiftLeft, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hj]
  rw [show (7 : BitVec 64).toNat = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq]
  have : j % 2 ^ 3 * 2 ^ 3 < 2 ^ 64 := by have := Nat.mod_lt j (by decide : 2 ^ 3 > 0); omega
  rw [Nat.mod_eq_of_lt this]; omega

theorem byte_extract (w : BitVec 64) (k : Nat) (hk : k < 8) :
    (w >>> (8 * k)) &&& 255 = BitVec.ofNat 64 (byteW w k) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_and, BitVec.toNat_ushiftRight, byteW, BitVec.toNat_ofNat]
  rw [show (255 : BitVec 64).toNat = 2 ^ 8 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]
  rw [show 2 ^ (8 * k) = 256 ^ k by rw [Nat.pow_mul]]
  have : (w.toNat / 256 ^ k) % 256 < 2 ^ 64 := by have := Nat.mod_lt (w.toNat / 256 ^ k) (by decide : 256 > 0); omega
  rw [Nat.mod_eq_of_lt this]

/-- The byte at address `e`: the word holding it, shifted, masked. -/
def byteE (e : ExpHOL 64) : ExpHOL 64 :=
  .op .and [.shift .lsr (.load .one (.shift .lsl (.shift .lsr e (.const 3)) (.const 3)))
    (.shift .lsl (.op .and [e, .const 7]) (.const 3)), .const 255]

section
variable {σ : Type} (s : PanSemStateFiniteExact 64 σ)

local notation "EVs" e => @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e

theorem evb_and_c (e : ExpHOL 64) (v c : BitVec 64) (h : (EVs e) = some (.val (.word v))) :
    (EVs (.op .and [e, .const c])) = some (.val (.word (v &&& c))) := by
  rw [evalHOLExact]; simp [evalListHOLExact, h, evalHOLExact, wordOpHOL, wordOp, valueIsWord, valueWord]
  show v &&& (c &&& 18446744073709551615#64) = v &&& c
  rw [show (18446744073709551615#64 : BitVec 64) = BitVec.allOnes 64 from rfl, BitVec.and_allOnes]

theorem evb_shr (e1 e2 : ExpHOL 64) (v1 v2 : BitVec 64) (h1 : (EVs e1) = some (.val (.word v1)))
    (h2 : (EVs e2) = some (.val (.word v2))) (hv : v2.toNat < 64) :
    (EVs (.shift .lsr e1 e2)) = some (.val (.word (v1 >>> v2.toNat))) := by
  rw [evalHOLExact]; simp [h1, h2, wordShiftHOL]; omega

theorem evb_shl (e1 e2 : ExpHOL 64) (v1 v2 : BitVec 64) (h1 : (EVs e1) = some (.val (.word v1)))
    (h2 : (EVs e2) = some (.val (.word v2))) (hv : v2.toNat < 64) :
    (EVs (.shift .lsl e1 e2)) = some (.val (.word (v1 <<< v2.toNat))) := by
  rw [evalHOLExact]; simp [h1, h2, wordShiftHOL]; omega

theorem evb_const (c : BitVec 64) : (EVs (.const c)) = some (.val (.word c)) := by simp [evalHOLExact]

end

/-- A byte read from inside the buffer. -/
theorem eval_byteE_bytes {σ : Type} (s : PanSemStateFiniteExact 64 σ) (e : ExpHOL 64)
    (a : BitVec 64) (bs : List UInt8) (i : Nat) (hb : BytesAt s a bs) (hi : i < bs.length)
    (he : @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e =
      some (.val (.word (a + BitVec.ofNat 64 i)))) :
    @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) (byteE e) =
      some (.val (.word (BitVec.ofNat 64 bs[i].toNat))) := by
  obtain ⟨-, hal, hov, hw⟩ := hb
  obtain ⟨w, hm, hd, hbyte⟩ := hw i hi
  have hsum : (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have haddr : a + BitVec.ofNat 64 i = BitVec.ofNat 64 (a.toNat + i) := by
    apply BitVec.eq_of_toNat_eq; rw [hsum]; simp; omega
  rw [haddr] at he
  have hwa : (BitVec.ofNat 64 (a.toNat + i) >>> (3 : Nat)) <<< (3 : Nat) = a + BitVec.ofNat 64 (8 * (i / 8)) := by
    rw [shr3shl3 _ (by omega)]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]; omega
  have hsh := and7shl3 (a.toNat + i) (by omega)
  rw [show (a.toNat + i) % 8 = i % 8 by omega] at hsh
  have hadr := evb_shl s _ _ _ _ (evb_shr s _ _ _ _ he (evb_const s 3) (by decide)) (evb_const s 3) (by decide)
  simp only [show (3 : BitVec 64).toNat = 3 from rfl, hwa] at hadr
  have hload := eval_load_word s _ _ hadr hd
  rw [hm] at hload
  have hoff := evb_shl s _ _ _ _ (evb_and_c s _ _ 7 he) (evb_const s 3) (by decide)
  simp only [show (3 : BitVec 64).toNat = 3 from rfl] at hoff
  have hx := evb_shr s _ _ _ _ hload hoff (by rw [hsh]; omega)
  rw [hsh] at hx
  have hfin := evb_and_c s _ _ 255 hx
  unfold byteE
  rw [hfin, byte_extract w (i % 8) (by omega), hbyte]

end ConPanqueque.Logic
