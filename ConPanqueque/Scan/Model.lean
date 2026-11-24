import ConLeche.Frontend.Scan.Fast

/-! # The scanner's list model

con-leche's scanner (`ConLeche/Frontend/Scan/Fast.lean`) indexes a `ByteArray` by `USize`.  The
Pancake scanner is specified against list models of its functions, indexed by `Nat`; each model is
tied to the `USize` original by a lemma under two runtime facts: the platform is 64-bit, and the
buffer is smaller than `USize.size` (con-leche's own `sizeError` guard). -/

namespace ConPanqueque.Scan

/-- The runtime facts the `USize` scanner needs. -/
structure Plat (b : ByteArray) : Prop where
  bits : System.Platform.numBits = 64
  size : b.size < 2 ^ 64

theorem Plat.usize_toNat {b : ByteArray} (h : Plat b) : b.usize.toNat = b.size := by
  simp only [ByteArray.usize, Nat.toUSize]
  rw [USize.toNat_ofNat', h.bits]
  exact Nat.mod_eq_of_lt h.size

theorem Plat.lt_iff {b : ByteArray} (h : Plat b) (i : USize) : i < b.usize ↔ i.toNat < b.size := by
  rw [USize.lt_iff_toNat_lt, h.usize_toNat]

theorem uget_eq (b : ByteArray) (i : USize) (h : i.toNat < b.size) (h' : i < b.usize) :
    b.uget i (ConLeche.Frontend.usizeInBounds b i h') = b.data.toList[i.toNat]'(by simpa using h) := by
  simp [ByteArray.uget, ByteArray.get, Array.getElem_toList]

def isWsN (c : Nat) : Bool := c == 32 || c == 9 || c == 13

theorem beq_ofNat (c : UInt8) (k : Nat) (hk : k < 256) : (c == UInt8.ofNat k) = (c.toNat == k) := by
  by_cases h : c.toNat = k
  · subst h; simp [UInt8.ofNat_toNat]
  · have : c ≠ UInt8.ofNat k := by
      intro e; apply h; subst e; simp [UInt8.toNat_ofNat']; omega
    rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr h]

theorem isWs_eq (c : UInt8) : ConLeche.Frontend.isWs c = isWsN c.toNat := by
  simp only [ConLeche.Frontend.isWs, isWsN]
  rw [show (32 : UInt8) = UInt8.ofNat 32 from rfl, show (9 : UInt8) = UInt8.ofNat 9 from rfl,
    show (13 : UInt8) = UInt8.ofNat 13 from rfl, beq_ofNat c 32 (by decide), beq_ofNat c 9 (by decide),
    beq_ofNat c 13 (by decide)]

/-- Skipping the bytes that pass `p`, on a list. -/
def skipL (p : Nat → Bool) (bs : List UInt8) (i : Nat) : Nat :=
  if h : i < bs.length then
    if p bs[i].toNat then skipL p bs (i + 1) else i
  else i
termination_by bs.length - i

theorem skipL_step (p : Nat → Bool) (bs : List UInt8) (j : Nat) (hj : j < bs.length) :
    skipL p bs j = if p bs[j].toNat then skipL p bs (j + 1) else j := by
  rw [skipL, dif_pos hj]

theorem skipL_end (p : Nat → Bool) (bs : List UInt8) (j : Nat) (hj : ¬ j < bs.length) :
    skipL p bs j = j := by
  rw [skipL, dif_neg hj]

/-- `skipWs`, on a list. -/
abbrev skipWsL := skipL isWsN

def isDigitN (c : Nat) : Bool := decide (48 ≤ c) && decide (c ≤ 57)

theorem isDigit_eq (c : UInt8) : ConLeche.Frontend.isDigit c = isDigitN c.toNat := by
  simp only [ConLeche.Frontend.isDigit, isDigitN, UInt8.le_iff_toNat_le]
  rfl

/-- `skipDigits`, on a list. -/
abbrev skipDigitsL := skipL isDigitN

theorem skipWs_eq {b : ByteArray} (hp : Plat b) :
    ∀ n (i : USize), b.size - i.toNat = n →
      (ConLeche.Frontend.skipWs b i).toNat = skipWsL b.data.toList i.toNat := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i hn
    rw [ConLeche.Frontend.skipWs, skipWsL, skipL]
    by_cases h : i < b.usize
    · have hl : i.toNat < b.size := (hp.lt_iff i).mp h
      have hl' : i.toNat < b.data.toList.length := by simpa using hl
      rw [dif_pos h, dif_pos hl', uget_eq b i hl h, isWs_eq]
      split
      · have hs := ConLeche.Frontend.usizeStep b i h
        rw [ih (b.size - (i + 1).toNat) (by omega) (i + 1) rfl, hs]
      · rfl
    · have hl : ¬ i.toNat < b.data.toList.length := by
        have : ¬ i.toNat < b.size := fun h' => h ((hp.lt_iff i).mpr h'); simpa using this
      rw [dif_neg h, dif_neg hl]

theorem skipDigits_eq {b : ByteArray} (hp : Plat b) :
    ∀ n (i : USize), b.size - i.toNat = n →
      (ConLeche.Frontend.skipDigits b i).toNat = skipDigitsL b.data.toList i.toNat := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i hn
    rw [ConLeche.Frontend.skipDigits, skipDigitsL, skipL]
    by_cases h : i < b.usize
    · have hl : i.toNat < b.size := (hp.lt_iff i).mp h
      have hl' : i.toNat < b.data.toList.length := by simpa using hl
      rw [dif_pos h, dif_pos hl', uget_eq b i hl h, isDigit_eq]
      split
      · have hs := ConLeche.Frontend.usizeStep b i h
        rw [ih (b.size - (i + 1).toNat) (by omega) (i + 1) rfl, hs]
      · rfl
    · have hl : ¬ i.toNat < b.data.toList.length := by
        have : ¬ i.toNat < b.size := fun h' => h ((hp.lt_iff i).mpr h'); simpa using this
      rw [dif_neg h, dif_neg hl]

end ConPanqueque.Scan
