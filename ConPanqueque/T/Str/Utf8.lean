import ConPanqueque.V.Enc

/-!
# UTF-8 decoding, as the port runs it

`u8dec` reads a byte list (as naturals) back to code points; on the bytes of a `String` it gives the string's
characters (`u8dec_toByteArray`). The port decodes a string literal's stored bytes this way to walk the
characters the twin walks (`s.toList`).
-/

namespace ConPanqueque.T.Str

def u8dec : List Nat → List Nat
  | [] => []
  | b0 :: rest =>
    if b0 < 0x80 then b0 :: u8dec rest
    else match rest with
      | b1 :: r1 =>
        if b0 < 0xE0 then ((b0 - 0xC0) * 64 + (b1 - 0x80)) :: u8dec r1
        else match r1 with
          | b2 :: r2 =>
            if b0 < 0xF0 then ((b0 - 0xE0) * 4096 + (b1 - 0x80) * 64 + (b2 - 0x80)) :: u8dec r2
            else match r2 with
              | b3 :: r3 => ((b0 - 0xF0) * 262144 + (b1 - 0x80) * 4096 + (b2 - 0x80) * 64 + (b3 - 0x80)) :: u8dec r3
              | [] => []
          | [] => []
      | [] => []

theorem u8_ofNat_toNat (n : Nat) (h : n < 256) : (UInt8.ofNat n).toNat = n := by
  simp [UInt8.toNat_ofNat]; omega

theorem u8dec_one (b : Nat) (l : List Nat) (h : b < 0x80) : u8dec (b :: l) = b :: u8dec l := by
  rw [u8dec.eq_def]; (try dsimp only); rw [ite_eq_left h]
theorem u8dec_two (b0 b1 : Nat) (l : List Nat) (h : ¬ b0 < 0x80) (h2 : b0 < 0xE0) :
    u8dec (b0 :: b1 :: l) = ((b0 - 0xC0) * 64 + (b1 - 0x80)) :: u8dec l := by
  rw [u8dec.eq_def]; (try dsimp only); rw [ite_eq_right h]; rw [ite_eq_left h2]
theorem u8dec_three (b0 b1 b2 : Nat) (l : List Nat) (h : ¬ b0 < 0x80) (h2 : ¬ b0 < 0xE0) (h3 : b0 < 0xF0) :
    u8dec (b0 :: b1 :: b2 :: l) = ((b0 - 0xE0) * 4096 + (b1 - 0x80) * 64 + (b2 - 0x80)) :: u8dec l := by
  rw [u8dec.eq_def]; (try dsimp only); rw [ite_eq_right h]; rw [ite_eq_right h2]; (try dsimp only); rw [ite_eq_left h3]
theorem u8dec_four (b0 b1 b2 b3 : Nat) (l : List Nat) (h : ¬ b0 < 0x80) (h2 : ¬ b0 < 0xE0) (h3 : ¬ b0 < 0xF0) :
    u8dec (b0 :: b1 :: b2 :: b3 :: l) =
      ((b0 - 0xF0) * 262144 + (b1 - 0x80) * 4096 + (b2 - 0x80) * 64 + (b3 - 0x80)) :: u8dec l := by
  rw [u8dec.eq_def]; (try dsimp only); rw [ite_eq_right h]; rw [ite_eq_right h2]; (try dsimp only); rw [ite_eq_right h3]

theorem u8dec_char (c : Char) (l : List Nat) :
    u8dec ((String.utf8EncodeChar c).map UInt8.toNat ++ l) = c.toNat :: u8dec l := by
  have hv : c.val.toNat < 0x110000 := by
    have := c.valid; simp only [UInt32.isValidChar, Nat.isValidChar] at this; omega
  have hc : c.toNat = c.val.toNat := rfl
  unfold String.utf8EncodeChar
  by_cases h1 : c.val.toNat ≤ 0x7f
  · rw [ite_eq_left h1]
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [u8_ofNat_toNat _ (by omega), u8dec_one _ _ (by omega)]; rfl
  rw [ite_eq_right h1]
  by_cases h2 : c.val.toNat ≤ 0x7ff
  · rw [ite_eq_left h2]
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [u8_ofNat_toNat _ (by omega), u8_ofNat_toNat _ (by omega), u8dec_two _ _ _ (by omega) (by omega)]
    exact congrArg (· :: u8dec l) (by rw [hc]; omega)
  rw [ite_eq_right h2]
  by_cases h3 : c.val.toNat ≤ 0xffff
  · rw [ite_eq_left h3]
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
    rw [u8_ofNat_toNat _ (by omega), u8_ofNat_toNat _ (by omega), u8_ofNat_toNat _ (by omega),
      u8dec_three _ _ _ _ (by omega) (by omega) (by omega)]
    exact congrArg (· :: u8dec l) (by rw [hc]; omega)
  rw [ite_eq_right h3]
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append]
  rw [u8_ofNat_toNat _ (by omega), u8_ofNat_toNat _ (by omega), u8_ofNat_toNat _ (by omega),
    u8_ofNat_toNat _ (by omega), u8dec_four _ _ _ _ _ (by omega) (by omega) (by omega)]
  exact congrArg (· :: u8dec l) (by rw [hc]; omega)
theorem u8dec_chars (cs : List Char) :
    u8dec ((cs.flatMap String.utf8EncodeChar).map UInt8.toNat) = cs.map Char.toNat := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [List.flatMap_cons, List.map_append, u8dec_char, ih, List.map_cons]

theorem u8dec_toByteArray (s : String) :
    u8dec (s.toByteArray.data.toList.map UInt8.toNat) = s.toList.map Char.toNat := by
  conv => lhs; rw [← String.ofList_toList (s := s), String.toByteArray_ofList]
  simp only [List.utf8Encode, List.data_toByteArray]
  exact u8dec_chars s.toList

/-- The shape of one character's bytes, as the decoder reads them. -/
def EncShape (L : List Nat) (cp : Nat) : Prop :=
  (∃ b0, L = [b0] ∧ b0 < 0x80 ∧ cp = b0) ∨
  (∃ b0 b1, L = [b0, b1] ∧ ¬ b0 < 0x80 ∧ b0 < 0xE0 ∧ 0xC0 ≤ b0 ∧ 0x80 ≤ b1 ∧ b1 < 256 ∧
    cp = (b0 - 0xC0) * 64 + (b1 - 0x80)) ∨
  (∃ b0 b1 b2, L = [b0, b1, b2] ∧ ¬ b0 < 0x80 ∧ ¬ b0 < 0xE0 ∧ b0 < 0xF0 ∧ 0x80 ≤ b1 ∧ b1 < 256 ∧
    0x80 ≤ b2 ∧ b2 < 256 ∧ cp = (b0 - 0xE0) * 4096 + (b1 - 0x80) * 64 + (b2 - 0x80)) ∨
  (∃ b0 b1 b2 b3, L = [b0, b1, b2, b3] ∧ ¬ b0 < 0x80 ∧ ¬ b0 < 0xE0 ∧ ¬ b0 < 0xF0 ∧ b0 < 256 ∧ 0x80 ≤ b1 ∧
    b1 < 256 ∧ 0x80 ≤ b2 ∧ b2 < 256 ∧ 0x80 ≤ b3 ∧ b3 < 256 ∧
    cp = (b0 - 0xF0) * 262144 + (b1 - 0x80) * 4096 + (b2 - 0x80) * 64 + (b3 - 0x80))

theorem encShape (c : Char) : EncShape ((String.utf8EncodeChar c).map UInt8.toNat) c.toNat := by
  have hv : c.val.toNat < 0x110000 := by
    have := c.valid; simp only [UInt32.isValidChar, Nat.isValidChar] at this; omega
  have hc : c.toNat = c.val.toNat := rfl
  unfold String.utf8EncodeChar
  by_cases h1 : c.val.toNat ≤ 0x7f
  · rw [ite_eq_left h1]
    simp only [List.map_cons, List.map_nil]
    rw [u8_ofNat_toNat _ (by omega)]
    exact Or.inl ⟨_, rfl, by omega, hc⟩
  rw [ite_eq_right h1]
  by_cases h2 : c.val.toNat ≤ 0x7ff
  · rw [ite_eq_left h2]
    simp only [List.map_cons, List.map_nil]
    rw [u8_ofNat_toNat _ (by omega), u8_ofNat_toNat _ (by omega)]
    exact Or.inr (Or.inl ⟨_, _, rfl, by omega, by omega, by omega, by omega, by omega, by rw [hc]; omega⟩)
  rw [ite_eq_right h2]
  by_cases h3 : c.val.toNat ≤ 0xffff
  · rw [ite_eq_left h3]
    simp only [List.map_cons, List.map_nil]
    rw [u8_ofNat_toNat _ (by omega), u8_ofNat_toNat _ (by omega), u8_ofNat_toNat _ (by omega)]
    exact Or.inr (Or.inr (Or.inl ⟨_, _, _, rfl, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
      by rw [hc]; omega⟩))
  rw [ite_eq_right h3]
  simp only [List.map_cons, List.map_nil]
  rw [u8_ofNat_toNat _ (by omega), u8_ofNat_toNat _ (by omega), u8_ofNat_toNat _ (by omega),
    u8_ofNat_toNat _ (by omega)]
  exact Or.inr (Or.inr (Or.inr ⟨_, _, _, _, rfl, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by rw [hc]; omega⟩))

theorem cp_lt (c : Char) : c.toNat < 2 ^ 21 := by
  have := c.valid; simp only [UInt32.isValidChar, Nat.isValidChar] at this
  show c.val.toNat < _; omega

end ConPanqueque.T.Str
