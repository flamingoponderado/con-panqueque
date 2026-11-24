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
  /-- room past the end for the scanners' fixed lookahead -/
  room : b.size + 64 < 2 ^ 64

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

/-- The decimal value of the digits in `[i, e)` accumulated onto `acc`: con-leche's `readNat64`
and `readNat` on a digit run, on a list. -/
def readL (bs : List UInt8) (i e acc : Nat) : Nat :=
  if h : i < e ∧ i < bs.length then readL bs (i + 1) e (acc * 10 + (bs[i].toNat - 48)) else acc
termination_by bs.length - i

theorem readL_step (bs : List UInt8) (i e acc : Nat) (h : i < e) (h' : i < bs.length) :
    readL bs i e acc = readL bs (i + 1) e (acc * 10 + (bs[i].toNat - 48)) := by
  rw [readL, dif_pos ⟨h, h'⟩]

theorem readL_end (bs : List UInt8) (i e acc : Nat) (h : ¬ i < e) : readL bs i e acc = acc := by
  rw [readL, dif_neg (fun h' => h h'.1)]

/-- The saturation bound of the Pancake numeral reader: indices at or above it are no table's. -/
def natCap : Nat := 2 ^ 62

theorem min_step (x d : Nat) (hd : d ≤ 9) :
    min (min x natCap * 10 + d) natCap = min (x * 10 + d) natCap := by
  unfold natCap
  by_cases hx : x < 2 ^ 62
  · rw [Nat.min_eq_left (Nat.le_of_lt hx)]
  · rw [Nat.min_eq_right (by omega)]; omega

theorem digit_sub (c : UInt8) (h : isDigitN c.toNat = true) : (c - 48).toUInt64.toNat = c.toNat - 48 := by
  simp [isDigitN] at h
  rw [UInt8.toNat_toUInt64, UInt8.toNat_sub_of_le]
  · rfl
  · rw [UInt8.le_iff_toNat_le]; exact h.1

/-- con-leche's `readNat64` on a digit run short enough not to overflow. -/
theorem readNat64_eq {b : ByteArray} (hp : Plat b) (e : USize) (he : e.toNat ≤ b.size) :
    ∀ n (i : USize) (acc : UInt64), e.toNat - i.toNat = n →
      (∀ k (hk : k < b.data.toList.length), i.toNat ≤ k → k < e.toNat →
        isDigitN b.data.toList[k].toNat = true) →
      (acc.toNat + 1) * 10 ^ (e.toNat - i.toNat) ≤ 10 ^ 19 →
      (ConLeche.Frontend.readNat64 b i e acc).toNat = readL b.data.toList i.toNat e.toNat acc.toNat := by
  intro n
  induction n with
  | zero =>
    intro i acc hn _ _
    rw [ConLeche.Frontend.readNat64, readL_end _ _ _ _ (by omega)]
    split
    · rw [if_neg (by rw [USize.lt_iff_toNat_lt]; omega)]
    · rfl
  | succ n ih =>
    intro i acc hn hd hb
    have hie : i.toNat < e.toNat := by omega
    have hl : i.toNat < b.size := by omega
    have hl' : i.toNat < b.data.toList.length := by simpa using hl
    have h : i < b.usize := (hp.lt_iff i).mpr hl
    rw [ConLeche.Frontend.readNat64, dif_pos h, if_pos (USize.lt_iff_toNat_lt.mpr hie),
      readL_step _ _ _ _ hie hl', uget_eq b i hl h]
    have hdig := hd i.toNat hl' (Nat.le_refl _) hie
    have hds := digit_sub _ hdig
    have hc : b.data.toList[i.toNat].toNat - 48 ≤ 9 := by
      have := hdig; simp only [isDigitN, Bool.and_eq_true, decide_eq_true_eq] at this; omega
    obtain ⟨k, hk⟩ : ∃ k, e.toNat - (i.toNat + 1) = k := ⟨_, rfl⟩
    have hpow : 10 ^ (e.toNat - i.toNat) = 10 ^ k * 10 := by
      rw [← Nat.pow_succ]; congr 1; omega
    rw [hpow] at hb
    have h1 : 1 ≤ 10 ^ k := Nat.one_le_pow _ _ (by decide)
    have h19 : (10 : Nat) ^ 19 = 10000000000000000000 := rfl
    have hb' : (acc.toNat + 1) * 10 ≤ 10 ^ 19 := by
      calc (acc.toNat + 1) * 10 ≤ (acc.toNat + 1) * 10 * 10 ^ k := Nat.le_mul_of_pos_right _ h1
        _ = (acc.toNat + 1) * (10 ^ k * 10) := by rw [Nat.mul_assoc, Nat.mul_comm 10]
        _ ≤ 10 ^ 19 := hb
    have hacc : acc.toNat * 10 + (b.data.toList[i.toNat].toNat - 48) < 2 ^ 64 := by
      have : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
      omega
    have hval : (acc * 10 + (b.data.toList[i.toNat] - 48).toUInt64).toNat =
        acc.toNat * 10 + (b.data.toList[i.toNat].toNat - 48) := by
      rw [UInt64.toNat_add, UInt64.toNat_mul, hds]
      simp only [UInt64.reduceToNat]
      have : (2 : Nat) ^ 64 = 18446744073709551616 := rfl
      rw [this] at hacc ⊢; omega
    have hs := ConLeche.Frontend.usizeStep b i h
    rw [ih (i + 1) _ (by rw [hs]; omega) (by intro k hk h1 h2; exact hd k hk (by rw [hs] at h1; omega) h2)
      (by
        rw [hval, hs, hk]
        calc (acc.toNat * 10 + (b.data.toList[i.toNat].toNat - 48) + 1) * 10 ^ k
            ≤ ((acc.toNat + 1) * 10) * 10 ^ k := Nat.mul_le_mul_right _ (by omega)
          _ = (acc.toNat + 1) * (10 ^ k * 10) := by rw [Nat.mul_assoc, Nat.mul_comm 10]
          _ ≤ 10 ^ 19 := hb), hval, hs]

theorem skipL_ge (p : Nat → Bool) (bs : List UInt8) :
    ∀ n i, bs.length - i = n → i ≤ skipL p bs i := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i hn
    rw [skipL]
    split
    · split
      · have := ih (bs.length - (i + 1)) (by omega) (i + 1) rfl; omega
      · exact Nat.le_refl _
    · exact Nat.le_refl _

theorem skipL_le_length (p : Nat → Bool) (bs : List UInt8) :
    ∀ n i, bs.length - i = n → i ≤ bs.length → skipL p bs i ≤ bs.length := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i hn hi
    rw [skipL]
    split
    · split
      · exact ih (bs.length - (i + 1)) (by omega) (i + 1) rfl (by omega)
      · exact hi
    · exact hi

/-- Every byte of `[i, skipL p bs i)` passes `p`. -/
theorem skipL_all (p : Nat → Bool) (bs : List UInt8) :
    ∀ n i, bs.length - i = n → ∀ k (hk : k < bs.length), i ≤ k → k < skipL p bs i → p bs[k].toNat = true := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i hn k hk h1 h2
    rw [skipL] at h2
    split at h2
    · rename_i hi
      split at h2
      · rename_i hp
        by_cases hki : k = i
        · subst hki; exact hp
        · exact ih (bs.length - (i + 1)) (by omega) (i + 1) rfl k hk (by omega) h2
      · omega
    · omega

/-- con-leche's `readNat`: the value of the whole digit run at `i`. -/
theorem readNat_eq {b : ByteArray} (hp : Plat b) :
    ∀ n (i : USize) (acc : Nat), b.size - i.toNat = n →
      ConLeche.Frontend.readNat b i acc =
        readL b.data.toList i.toNat (skipDigitsL b.data.toList i.toNat) acc := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i acc hn
    rw [ConLeche.Frontend.readNat]
    by_cases h : i < b.usize
    · have hl : i.toNat < b.size := (hp.lt_iff i).mp h
      have hl' : i.toNat < b.data.toList.length := by simpa using hl
      rw [dif_pos h]
      simp only
      rw [uget_eq b i hl h, isDigit_eq]
      have hsk := skipL_step isDigitN b.data.toList i.toNat hl'
      split
      · rename_i hd
        rw [if_pos hd] at hsk
        have hs := ConLeche.Frontend.usizeStep b i h
        have hge := skipL_ge isDigitN b.data.toList _ (i.toNat + 1) rfl
        rw [ih (b.size - (i + 1).toNat) (by omega) (i + 1) _ rfl, hs, skipDigitsL, hsk,
          readL_step _ _ _ _ (by omega) hl']
      · rename_i hd
        rw [if_neg hd] at hsk
        rw [skipDigitsL, hsk, readL_end _ _ _ _ (Nat.lt_irrefl _)]
    · have hl : ¬ i.toNat < b.data.toList.length := by
        have : ¬ i.toNat < b.size := fun h' => h ((hp.lt_iff i).mpr h'); simpa using this
      rw [dif_neg h, skipDigitsL, skipL_end _ _ _ hl, readL_end _ _ _ _ (Nat.lt_irrefl _)]

/-- **con-leche's `readNatAt` on a digit run is `readL`**: at the end `e` of the digit run at `i`. -/
theorem readNatAt_eq {b : ByteArray} (hp : Plat b) (i e : USize)
    (he : e.toNat = skipDigitsL b.data.toList i.toNat) :
    ConLeche.Frontend.readNatAt b i e = readL b.data.toList i.toNat e.toNat 0 := by
  have hge := skipL_ge isDigitN b.data.toList _ i.toNat rfl
  have hall := skipL_all isDigitN b.data.toList _ i.toNat rfl
  rw [ConLeche.Frontend.readNatAt]
  have hsub : (e - i).toNat = e.toNat - i.toNat := by
    rw [USize.toNat_sub_of_le]; rw [USize.le_iff_toNat_le]; simp only [skipDigitsL] at he; omega
  split
  · rename_i hle
    rw [USize.le_iff_toNat_le, hsub] at hle
    have hle' : e.toNat - i.toNat ≤ 18 := by simpa using hle
    by_cases hi : i.toNat ≤ b.size
    · have hes : e.toNat ≤ b.size := by
        have := skipL_le_length isDigitN b.data.toList _ i.toNat rfl (by simpa using hi)
        simp only [skipDigitsL] at he; simp at this; omega
      rw [readNat64_eq hp e hes _ i 0 rfl
        (fun k hk h1 h2 => hall k hk h1 (by simp only [skipDigitsL] at he; omega))
        (by
          simp only [UInt64.toNat_zero, Nat.zero_add, Nat.one_mul]
          calc 10 ^ (e.toNat - i.toNat) ≤ 10 ^ 18 := Nat.pow_le_pow_right (by decide) hle'
            _ ≤ 10 ^ 19 := by decide)]
      rfl
    · have hn : ¬ i.toNat < b.data.toList.length := by simp; omega
      have he' : e.toNat = i.toNat := by
        rw [he, skipDigitsL, skipL_end _ _ _ hn]
      rw [ConLeche.Frontend.readNat64, dif_neg (fun h => hn (by simpa using (hp.lt_iff i).mp h)),
        readL_end _ _ _ _ (by omega)]
      rfl
  · rw [readNat_eq hp _ i 0 rfl, ← he]

/-- `numEnd`, on a list: the end of the digit run at `i`, unless there is none or it is a
leading `0` followed by more digits. -/
def numEndL (bs : List UInt8) (i : Nat) : Nat :=
  let e := skipDigitsL bs i
  if e = i then i
  else if (bs[i]?.getD 0).toNat = 48 ∧ e ≠ i + 1 then i
  else e

theorem byteAt_eq {b : ByteArray} (hp : Plat b) (i : USize) :
    ConLeche.Frontend.byteAt b i = b.data.toList[i.toNat]?.getD 0 := by
  rw [ConLeche.Frontend.byteAt]
  split
  · rename_i h
    have hl : i.toNat < b.size := (hp.lt_iff i).mp h
    rw [uget_eq b i hl h, List.getElem?_eq_getElem (by simpa using hl)]; rfl
  · rename_i h
    have : ¬ i.toNat < b.data.toList.length := by
      have : ¬ i.toNat < b.size := fun h' => h ((hp.lt_iff i).mpr h'); simpa using this
    rw [List.getElem?_eq_none (by omega)]; rfl

theorem numEnd_eq {b : ByteArray} (hp : Plat b) (i : USize) (hi : i.toNat ≤ b.size) :
    (ConLeche.Frontend.numEnd b i).toNat = numEndL b.data.toList i.toNat := by
  have hs := skipDigits_eq hp _ i rfl
  have hle := skipL_le_length isDigitN b.data.toList _ i.toNat rfl (by simpa using hi)
  have hge := skipL_ge isDigitN b.data.toList _ i.toNat rfl
  have hb64 : b.size < 2 ^ 64 := hp.size
  simp only [ConLeche.Frontend.numEnd, numEndL]
  have heq : (ConLeche.Frontend.skipDigits b i == i) = decide (skipDigitsL b.data.toList i.toNat = i.toNat) := by
    rw [← hs]
    by_cases h : ConLeche.Frontend.skipDigits b i = i
    · simp [h]
    · have : ¬ (ConLeche.Frontend.skipDigits b i).toNat = i.toNat := fun h' => h (USize.toNat_inj.mp h')
      simp [h, this]
  rw [heq]
  by_cases h : skipDigitsL b.data.toList i.toNat = i.toNat
  · simp [h]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    simp only [skipDigitsL] at h hs
    have hlt : i.toNat < b.size := by simp at hle; omega
    have hsucc : (i + 1).toNat = i.toNat + 1 := ConLeche.Frontend.usizeStep b i ((hp.lt_iff i).mpr hlt)
    have hne : (ConLeche.Frontend.skipDigits b i != i + 1) =
        decide (skipL isDigitN b.data.toList i.toNat ≠ i.toNat + 1) := by
      by_cases h' : ConLeche.Frontend.skipDigits b i = i + 1
      · have : skipL isDigitN b.data.toList i.toNat = i.toNat + 1 := by rw [← hs, h', hsucc]
        simp [h', this]
      · have : ¬ skipL isDigitN b.data.toList i.toNat = i.toNat + 1 := by
          rw [← hs, ← hsucc]; exact fun h'' => h' (USize.toNat_inj.mp h'')
        simp [h', this]
    rw [hne, byteAt_eq hp, show (48 : UInt8) = UInt8.ofNat 48 from rfl, beq_ofNat _ 48 (by decide)]
    generalize (b.data.toList[i.toNat]?.getD 0) = g
    unfold skipDigitsL
    by_cases hz : g.toNat = 48 <;>
      by_cases hn : skipL isDigitN b.data.toList i.toNat = i.toNat + 1 <;> simp [hz, hn, hs]

/-- A byte inside a key: not the closing quote, not a control byte, not a backslash. -/
def isKeyN (c : Nat) : Bool := !(c == 34) && !(decide (c < 32) || c == 92)

/-- `keyEnd`, on a list: the closing quote of the key whose contents start at `j`, or `0`. -/
def keyEndL (bs : List UInt8) (j : Nat) : Nat :=
  let k := skipL isKeyN bs j
  if (bs[k]?.getD 0).toNat = 34 then k else 0

theorem keyEnd_eq {b : ByteArray} (hp : Plat b) :
    ∀ n (j : USize), b.size - j.toNat = n →
      (ConLeche.Frontend.keyEnd b j).toNat = keyEndL b.data.toList j.toNat := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro j hn
    rw [ConLeche.Frontend.keyEnd, keyEndL, skipL]
    by_cases h : j < b.usize
    · have hl : j.toNat < b.size := (hp.lt_iff j).mp h
      have hl' : j.toNat < b.data.toList.length := by simpa using hl
      rw [dif_pos h, dif_pos hl']
      simp only
      rw [uget_eq b j hl h]
      generalize hc : b.data.toList[j.toNat] = c
      have e34 := beq_ofNat c 34 (by decide)
      have e92 := beq_ofNat c 92 (by decide)
      have e32 : (c < 32) = (c.toNat < 32) := by
        simp [UInt8.lt_iff_toNat_lt]
      rw [show (34 : UInt8) = UInt8.ofNat 34 from rfl, show (92 : UInt8) = UInt8.ofNat 92 from rfl,
        show (32 : UInt8) = UInt8.ofNat 32 from rfl, e34, e92]
      by_cases q : c.toNat = 34
      · have : isKeyN c.toNat = false := by simp [isKeyN, q]
        simp [q, this, List.getElem?_eq_getElem hl', hc, show isKeyN 34 = false from rfl]
      · by_cases bad : c.toNat < 32 ∨ c.toNat = 92
        · have : isKeyN c.toNat = false := by simp [isKeyN, q]; omega
          have hlt : (c < UInt8.ofNat 32) = decide (c.toNat < 32) := by
            simp [UInt8.lt_iff_toNat_lt]
          simp only [q, this, hlt, beq_iff_eq, ↓reduceIte, Bool.false_eq_true, decide_eq_true_eq]
          have hb' : (decide (c.toNat < 32) || c.toNat == 92) = true := by
            rcases bad with h | h <;> simp [h]
          rw [if_pos hb', List.getElem?_eq_getElem hl', hc]
          simp [q]
        · have : isKeyN c.toNat = true := by simp [isKeyN, q]; omega
          have hlt : (c < UInt8.ofNat 32) = decide (c.toNat < 32) := by
            simp [UInt8.lt_iff_toNat_lt]
          have hs := ConLeche.Frontend.usizeStep b j h
          simp only [q, this, hlt, beq_iff_eq, decide_eq_true_eq, ↓reduceIte, Bool.not_eq_true',
            Bool.false_eq_true, Bool.or_eq_true, decide_eq_false_iff_not]
          rw [if_neg (by omega), ih (b.size - (j + 1).toNat) (by omega) (j + 1) rfl, hs]
          rfl
    · have hl : ¬ j.toNat < b.data.toList.length := by
        have : ¬ j.toNat < b.size := fun h' => h ((hp.lt_iff j).mpr h'); simpa using this
      rw [dif_neg h, dif_neg hl, List.getElem?_eq_none (by omega)]
      simp

/-- `valueAt`, on a list: past the colon after the key's closing quote `ke`, whitespace skipped on
both sides; `i` when the colon is missing. -/
def valueAtL (bs : List UInt8) (i ke : Nat) : Nat :=
  let p := skipWsL bs (ke + 1)
  if (bs[p]?.getD 0).toNat = 58 then skipWsL bs (p + 1) else i

theorem valueAt_eq {b : ByteArray} (hp : Plat b) (i ke : USize) (hke : ke.toNat < b.size) :
    (ConLeche.Frontend.valueAt b i ke).toNat = valueAtL b.data.toList i.toNat ke.toNat := by
  have hk1 : (ke + 1).toNat = ke.toNat + 1 := ConLeche.Frontend.usizeStep b ke ((hp.lt_iff ke).mpr hke)
  simp only [ConLeche.Frontend.valueAt, valueAtL]
  have hs1 := skipWs_eq hp _ (ke + 1) rfl
  rw [hk1] at hs1
  have hle := skipL_le_length isWsN b.data.toList _ (ke.toNat + 1) rfl (by simp; omega)
  rw [byteAt_eq hp, show (58 : UInt8) = UInt8.ofNat 58 from rfl, beq_ofNat _ 58 (by decide)]
  generalize hP : ConLeche.Frontend.skipWs b (ke + 1) = P at hs1
  rw [hs1]
  by_cases hc : (b.data.toList[skipWsL b.data.toList (ke.toNat + 1)]?.getD 0).toNat = 58
  · have hlt : skipWsL b.data.toList (ke.toNat + 1) < b.data.toList.length := by
      by_cases h : skipWsL b.data.toList (ke.toNat + 1) < b.data.toList.length
      · exact h
      · rw [List.getElem?_eq_none (by omega)] at hc; simp at hc
    have hPl : P.toNat < b.size := by rw [hs1]; simpa using hlt
    have hP1 : (P + 1).toNat = P.toNat + 1 := ConLeche.Frontend.usizeStep b P ((hp.lt_iff P).mpr hPl)
    simp only [hc, beq_self_eq_true, ↓reduceIte]
    rw [skipWs_eq hp _ (P + 1) rfl, hP1, hs1]
  · have : ((b.data.toList[skipWsL b.data.toList (ke.toNat + 1)]?.getD 0).toNat == 58) = false :=
      beq_eq_false_iff_ne.mpr hc
    simp only [this, Bool.false_eq_true, ↓reduceIte, hc]

end ConPanqueque.Scan
