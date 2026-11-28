import ConPanqueque.Scan.ValueAt

/-! # UTF-8 string bodies

The string scanner (`Scan/Str.lean`) walks a string body one character at a time: an ASCII byte
that is not a control byte, `"` or `\`, or a well-formed multi-byte UTF-8 sequence (Unicode's
table 3-7: no overlong forms, no surrogates, nothing past `U+10FFFF`).  `stepN` is the length of
the character at a position (`0`: none), as the sum of four exclusive tests; `stepE` computes it
in Pancake from the four bytes there (`0` past the end).  A body walked this way is valid UTF-8
(`ValidL`, a list of `Char`s encoded) and has no byte con-leche's `strClose`/`hasEscape` stop at
(`isStrN`): `SegOK`. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

namespace ConPanqueque.Scan

/-- A byte inside a string body as `strClose`/`hasEscape` see it: no control byte, `"` or `\`. -/
def isStrN (c : Nat) : Bool := decide (32 ≤ c) && !(c == 34) && !(c == 92)

theorem isStrN_of (c : Nat) (h1 : 32 ≤ c) (h2 : c ≠ 34) (h3 : c ≠ 92) : isStrN c = true := by
  simp [isStrN]; omega

/-- A byte list that is the UTF-8 encoding of a list of characters. -/
def ValidL (l : List UInt8) : Prop := ∃ cs : List Char, cs.flatMap String.utf8EncodeChar = l

theorem ValidL.nil : ValidL [] := ⟨[], rfl⟩

theorem ValidL.append {a b : List UInt8} (ha : ValidL a) (hb : ValidL b) : ValidL (a ++ b) := by
  obtain ⟨c1, rfl⟩ := ha; obtain ⟨c2, rfl⟩ := hb; exact ⟨c1 ++ c2, by simp⟩

theorem ValidL.isValid (b : ByteArray) (h : ValidL b.data.toList) : ByteArray.IsValidUTF8 b := by
  obtain ⟨cs, hcs⟩ := h
  refine ⟨cs, ?_⟩
  simp only [List.utf8Encode, hcs]
  apply ByteArray.ext; simp [List.data_toByteArray]

theorem toNat_charOfNat (v : Nat) (h : v < 0xd800 ∨ (0xdfff < v ∧ v < 0x110000)) :
    (Char.ofNat v).val.toNat = v := by
  have hv : v.isValidChar := by unfold Nat.isValidChar; omega
  simp [Char.ofNat, hv, Char.ofNatAux]

theorem u8eq (a : UInt8) (n : Nat) (h : n = a.toNat) : UInt8.ofNat n = a := by
  subst h; simp

theorem enc1 (a : UInt8) (h : a.toNat < 128) : ValidL [a] := by
  refine ⟨[Char.ofNat a.toNat], ?_⟩
  have hv := toNat_charOfNat a.toNat (by omega)
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, String.utf8EncodeChar, hv]
  simp only [show a.toNat ≤ 127 from by omega, ↓reduceIte, UInt8.ofNat_toNat]

theorem enc2 (a b : UInt8) (ha1 : 194 ≤ a.toNat) (ha2 : a.toNat < 224) (hb1 : 128 ≤ b.toNat)
    (hb2 : b.toNat < 192) : ValidL [a, b] := by
  refine ⟨[Char.ofNat ((a.toNat - 192) * 64 + (b.toNat - 128))], ?_⟩
  have hv := toNat_charOfNat ((a.toNat - 192) * 64 + (b.toNat - 128)) (by omega)
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, String.utf8EncodeChar, hv]
  rw [ite_eq_right (by omega), ite_eq_left (by omega)]
  rw [u8eq a _ (by omega), u8eq b _ (by omega)]

theorem enc3 (a b c : UInt8) (ha1 : 224 ≤ a.toNat) (ha2 : a.toNat < 240)
    (hb0 : a.toNat ≠ 224 ∨ 160 ≤ b.toNat) (hb1 : 128 ≤ b.toNat) (hb3 : a.toNat ≠ 237 ∨ b.toNat < 160)
    (hb2 : b.toNat < 192) (hc1 : 128 ≤ c.toNat) (hc2 : c.toNat < 192) : ValidL [a, b, c] := by
  refine ⟨[Char.ofNat ((a.toNat - 224) * 4096 + (b.toNat - 128) * 64 + (c.toNat - 128))], ?_⟩
  have hv := toNat_charOfNat ((a.toNat - 224) * 4096 + (b.toNat - 128) * 64 + (c.toNat - 128)) (by omega)
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, String.utf8EncodeChar, hv]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left (by omega)]
  rw [u8eq a _ (by omega), u8eq b _ (by omega), u8eq c _ (by omega)]

theorem enc4 (a b c d : UInt8) (ha1 : 240 ≤ a.toNat) (ha2 : a.toNat < 245)
    (hb0 : a.toNat ≠ 240 ∨ 144 ≤ b.toNat) (hb1 : 128 ≤ b.toNat) (hb3 : a.toNat ≠ 244 ∨ b.toNat < 144)
    (hb2 : b.toNat < 192) (hc1 : 128 ≤ c.toNat) (hc2 : c.toNat < 192) (hd1 : 128 ≤ d.toNat)
    (hd2 : d.toNat < 192) : ValidL [a, b, c, d] := by
  refine ⟨[Char.ofNat ((a.toNat - 240) * 262144 + (b.toNat - 128) * 4096 + (c.toNat - 128) * 64 +
    (d.toNat - 128))], ?_⟩
  have hv := toNat_charOfNat ((a.toNat - 240) * 262144 + (b.toNat - 128) * 4096 + (c.toNat - 128) * 64 +
    (d.toNat - 128)) (by omega)
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, String.utf8EncodeChar, hv]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
  rw [u8eq a _ (by omega), u8eq b _ (by omega), u8eq c _ (by omega), u8eq d _ (by omega)]

/-! ## One character -/

/-- A plain ASCII character. -/
abbrev P1 (a : Nat) : Prop := 32 ≤ a ∧ a < 128 ∧ a ≠ 34 ∧ a ≠ 92
/-- A two-byte character. -/
abbrev P2 (a b : Nat) : Prop := 194 ≤ a ∧ a < 224 ∧ 128 ≤ b ∧ b < 192
/-- A three-byte character (no overlong form, no surrogate). -/
abbrev P3 (a b c : Nat) : Prop :=
  224 ≤ a ∧ a < 240 ∧ (a ≠ 224 ∨ 160 ≤ b) ∧ 128 ≤ b ∧ (a ≠ 237 ∨ b < 160) ∧ b < 192 ∧ 128 ≤ c ∧ c < 192
/-- A four-byte character (no overlong form, at most `U+10FFFF`). -/
abbrev P4 (a b c d : Nat) : Prop :=
  240 ≤ a ∧ a < 245 ∧ (a ≠ 240 ∨ 144 ≤ b) ∧ 128 ≤ b ∧ (a ≠ 244 ∨ b < 144) ∧ b < 192 ∧ 128 ≤ c ∧ c < 192 ∧
    128 ≤ d ∧ d < 192

/-- The length of the character starting with bytes `a b c d`, or `0`. -/
def stepN (a b c d : Nat) : Nat :=
  (if P1 a then 1 else 0) + ((if P2 a b then 2 else 0) + ((if P3 a b c then 3 else 0) + (if P4 a b c d then 4 else 0)))

/-- `stepN` at position `j` of a byte list (bytes past the end read `0`). -/
def stepL (bs : List UInt8) (j : Nat) : Nat :=
  stepN (byteL bs j).toNat (byteL bs (j + 1)).toNat (byteL bs (j + 2)).toNat (byteL bs (j + 3)).toNat

/-- The body `[a, e)` is valid UTF-8 and holds no byte `strClose`/`hasEscape` stop at. -/
def SegOK (bs : List UInt8) (a e : Nat) : Prop :=
  ValidL ((bs.drop a).take (e - a)) ∧
    ∀ k (hk : k < bs.length), a ≤ k → k < e → isStrN bs[k].toNat = true

theorem segOK_refl (bs : List UInt8) (a : Nat) : SegOK bs a a :=
  ⟨by simp [ValidL.nil], fun _ _ h1 h2 => absurd h2 (by omega)⟩

theorem segOK_trans {bs : List UInt8} {a j e : Nat} (h1 : SegOK bs a j) (h2 : SegOK bs j e)
    (haj : a ≤ j) (hje : j ≤ e) : SegOK bs a e := by
  refine ⟨?_, fun k hk k1 k2 => ?_⟩
  · have : (bs.drop a).take (e - a) = (bs.drop a).take (j - a) ++ (bs.drop j).take (e - j) := by
      rw [show e - a = (j - a) + (e - j) by omega, List.take_add, List.drop_drop]
      congr 3; omega
    rw [this]; exact h1.1.append h2.1
  · by_cases hk' : k < j
    · exact h1.2 k hk k1 hk'
    · exact h2.2 k hk (by omega) k2

theorem byteL_pos {bs : List UInt8} {p : Nat} (h : 0 < (byteL bs p).toNat) :
    ∃ hp : p < bs.length, byteL bs p = bs[p] := by
  unfold byteL at h ⊢
  by_cases hp : p < bs.length
  · exact ⟨hp, by simp [List.getElem?_eq_getElem hp]⟩
  · rw [List.getElem?_eq_none (by omega)] at h; simp at h

theorem segOK_one {bs : List UInt8} {j : Nat} (hj : j < bs.length) (h : P1 bs[j].toNat) :
    SegOK bs j (j + 1) := by
  refine ⟨?_, fun k hk k1 k2 => ?_⟩
  · rw [show j + 1 - j = 1 by omega, List.drop_eq_getElem_cons hj]
    simp only [List.take_succ_cons, List.take_zero]
    exact enc1 _ (by omega)
  · obtain rfl : k = j := by omega
    exact isStrN_of _ h.1 h.2.2.1 h.2.2.2

theorem segOK_two {bs : List UInt8} {j : Nat} (hj : j + 1 < bs.length)
    (h : P2 (bs[j]'(by omega)).toNat bs[j + 1].toNat) : SegOK bs j (j + 2) := by
  refine ⟨?_, fun k hk k1 k2 => ?_⟩
  · rw [show j + 2 - j = 2 by omega, List.drop_eq_getElem_cons (by omega : j < bs.length),
      List.drop_eq_getElem_cons hj]
    simp only [List.take_succ_cons, List.take_zero]
    exact enc2 _ _ h.1 h.2.1 h.2.2.1 h.2.2.2
  · obtain rfl | rfl : k = j ∨ k = j + 1 := by omega
    · exact isStrN_of _ (by omega) (by omega) (by omega)
    · exact isStrN_of _ (by omega) (by omega) (by omega)

theorem segOK_three {bs : List UInt8} {j : Nat} (hj : j + 2 < bs.length)
    (h : P3 (bs[j]'(by omega)).toNat (bs[j + 1]'(by omega)).toNat bs[j + 2].toNat) :
    SegOK bs j (j + 3) := by
  obtain ⟨a1, a2, b0, b1, b3, b2, c1, c2⟩ := h
  refine ⟨?_, fun k hk k1 k2 => ?_⟩
  · rw [show j + 3 - j = 3 by omega, List.drop_eq_getElem_cons (by omega : j < bs.length),
      List.drop_eq_getElem_cons (by omega : j + 1 < bs.length), List.drop_eq_getElem_cons hj]
    simp only [List.take_succ_cons, List.take_zero]
    exact enc3 _ _ _ a1 a2 b0 b1 b3 b2 c1 c2
  · obtain rfl | rfl | rfl : k = j ∨ k = j + 1 ∨ k = j + 2 := by omega
    · exact isStrN_of _ (by omega) (by omega) (by omega)
    · exact isStrN_of _ (by omega) (by omega) (by omega)
    · exact isStrN_of _ (by omega) (by omega) (by omega)

theorem segOK_four {bs : List UInt8} {j : Nat} (hj : j + 3 < bs.length)
    (h : P4 (bs[j]'(by omega)).toNat (bs[j + 1]'(by omega)).toNat (bs[j + 2]'(by omega)).toNat
      bs[j + 3].toNat) : SegOK bs j (j + 4) := by
  obtain ⟨a1, a2, b0, b1, b3, b2, c1, c2, d1, d2⟩ := h
  refine ⟨?_, fun k hk k1 k2 => ?_⟩
  · rw [show j + 4 - j = 4 by omega, List.drop_eq_getElem_cons (by omega : j < bs.length),
      List.drop_eq_getElem_cons (by omega : j + 1 < bs.length),
      List.drop_eq_getElem_cons (by omega : j + 2 < bs.length), List.drop_eq_getElem_cons hj]
    simp only [List.take_succ_cons, List.take_zero]
    exact enc4 _ _ _ _ a1 a2 b0 b1 b3 b2 c1 c2 d1 d2
  · obtain rfl | rfl | rfl | rfl : k = j ∨ k = j + 1 ∨ k = j + 2 ∨ k = j + 3 := by omega
    · exact isStrN_of _ (by omega) (by omega) (by omega)
    · exact isStrN_of _ (by omega) (by omega) (by omega)
    · exact isStrN_of _ (by omega) (by omega) (by omega)
    · exact isStrN_of _ (by omega) (by omega) (by omega)

/-- **One step of the walk**: a nonzero `stepL` is a character inside the list. -/
theorem stepL_ok (bs : List UInt8) (j : Nat) (h0 : stepL bs j ≠ 0) :
    j + stepL bs j ≤ bs.length ∧ SegOK bs j (j + stepL bs j) := by
  unfold stepL at h0 ⊢
  generalize ha : byteL bs j = a at h0 ⊢
  generalize hb : byteL bs (j + 1) = b at h0 ⊢
  generalize hc : byteL bs (j + 2) = c at h0 ⊢
  generalize hd : byteL bs (j + 3) = d at h0 ⊢
  unfold stepN at h0 ⊢
  by_cases h1 : P1 a.toNat
  · have n2 : ¬ P2 a.toNat b.toNat := by omega
    have n3 : ¬ P3 a.toNat b.toNat c.toNat := by omega
    have n4 : ¬ P4 a.toNat b.toNat c.toNat d.toNat := by omega
    obtain ⟨hj, e⟩ := byteL_pos (p := j) (bs := bs) (by rw [ha]; omega)
    rw [ha] at e; subst e
    rw [ite_eq_left h1, ite_eq_right n2, ite_eq_right n3, ite_eq_right n4]; simp only [Nat.add_zero]
    exact ⟨by omega, segOK_one hj h1⟩
  by_cases h2 : P2 a.toNat b.toNat
  · have n3 : ¬ P3 a.toNat b.toNat c.toNat := by omega
    have n4 : ¬ P4 a.toNat b.toNat c.toNat d.toNat := by omega
    obtain ⟨hj, e⟩ := byteL_pos (p := j) (bs := bs) (by rw [ha]; omega)
    obtain ⟨hj1, e1⟩ := byteL_pos (p := j + 1) (bs := bs) (by rw [hb]; omega)
    rw [ha] at e; rw [hb] at e1; subst e e1
    rw [ite_eq_right h1, ite_eq_left h2, ite_eq_right n3, ite_eq_right n4]; simp only [Nat.add_zero, Nat.zero_add]
    exact ⟨by omega, segOK_two hj1 h2⟩
  by_cases h3 : P3 a.toNat b.toNat c.toNat
  · have n4 : ¬ P4 a.toNat b.toNat c.toNat d.toNat := by omega
    obtain ⟨hj, e⟩ := byteL_pos (p := j) (bs := bs) (by rw [ha]; omega)
    obtain ⟨hj1, e1⟩ := byteL_pos (p := j + 1) (bs := bs) (by rw [hb]; omega)
    obtain ⟨hj2, e2⟩ := byteL_pos (p := j + 2) (bs := bs) (by rw [hc]; omega)
    rw [ha] at e; rw [hb] at e1; rw [hc] at e2; subst e e1 e2
    rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3, ite_eq_right n4]; simp only [Nat.add_zero, Nat.zero_add]
    exact ⟨by omega, segOK_three hj2 h3⟩
  by_cases h4 : P4 a.toNat b.toNat c.toNat d.toNat
  · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3, ite_eq_left h4]; simp only [Nat.zero_add]
    obtain ⟨hj, e⟩ := byteL_pos (p := j) (bs := bs) (by rw [ha]; omega)
    obtain ⟨hj1, e1⟩ := byteL_pos (p := j + 1) (bs := bs) (by rw [hb]; omega)
    obtain ⟨hj2, e2⟩ := byteL_pos (p := j + 2) (bs := bs) (by rw [hc]; omega)
    obtain ⟨hj3, e3⟩ := byteL_pos (p := j + 3) (bs := bs) (by rw [hd]; omega)
    rw [ha] at e; rw [hb] at e1; rw [hc] at e2; rw [hd] at e3; subst e e1 e2 e3
    exact ⟨by omega, segOK_four hj3 h4⟩
  simp [h1, h2, h3, h4] at h0

theorem stepN_le (a b c d : Nat) : stepN a b c d ≤ 10 := by
  unfold stepN; split <;> split <;> split <;> split <;> omega

/-! ## `stepE`: the step in Pancake -/

def sU1 := ofString "u1"
def sU2 := ofString "u2"
def sU3 := ofString "u3"
def sUK := ofString "uk"

def cGe (x : MlS) (k : Nat) : ExpHOL 64 := .cmp .notLower (vv x) (.const (BitVec.ofNat 64 k))
def cLt (x : MlS) (k : Nat) : ExpHOL 64 := .cmp .lower (vv x) (.const (BitVec.ofNat 64 k))
def cNe (x : MlS) (k : Nat) : ExpHOL 64 := .cmp .notEqual (vv x) (.const (BitVec.ofNat 64 k))
def eAnd (a b : ExpHOL 64) : ExpHOL 64 := .op .and [a, b]
def eOr (a b : ExpHOL 64) : ExpHOL 64 := .op .or [a, b]

def p1E : ExpHOL 64 := eAnd (cGe sC 32) (eAnd (cLt sC 128) (eAnd (cNe sC 34) (cNe sC 92)))
def p2E : ExpHOL 64 := eAnd (cGe sC 194) (eAnd (cLt sC 224) (eAnd (cGe sU1 128) (cLt sU1 192)))
def p3E : ExpHOL 64 :=
  eAnd (cGe sC 224) (eAnd (cLt sC 240) (eAnd (eOr (cNe sC 224) (cGe sU1 160)) (eAnd (cGe sU1 128)
    (eAnd (eOr (cNe sC 237) (cLt sU1 160)) (eAnd (cLt sU1 192) (eAnd (cGe sU2 128) (cLt sU2 192)))))))
def p4E : ExpHOL 64 :=
  eAnd (cGe sC 240) (eAnd (cLt sC 245) (eAnd (eOr (cNe sC 240) (cGe sU1 144)) (eAnd (cGe sU1 128)
    (eAnd (eOr (cNe sC 244) (cLt sU1 144)) (eAnd (cLt sU1 192) (eAnd (cGe sU2 128) (eAnd (cLt sU2 192)
      (eAnd (cGe sU3 128) (cLt sU3 192)))))))))

/-- The character length from the bytes in `c`, `u1`, `u2`, `u3`. -/
def stepE : ExpHOL 64 :=
  .op .add [p1E, .op .add [.shift .lsl p2E (.const 1),
    .op .add [.op .add [p3E, .shift .lsl p3E (.const 1)], .shift .lsl p4E (.const 2)]]]

section
variable {σ : Type} (s : PanSemStateFiniteExact 64 σ)

local notation "EV" e => @evalHOLExact 64 σ _ (PanSemStateFiniteExact.toExact s)
  (fun a => Classical.propDecidable (PanSemStateFiniteExact.memaddrs s a)) e

theorem ev_ge (x : MlS) (v k : Nat) (hv : v < 2 ^ 64) (hk : k < 2 ^ 64)
    (h : s.locals.lookup x = some (.val (.word (BitVec.ofNat 64 v)))) :
    (EV (cGe x k)) = some (.val (.word (bw (k ≤ v)))) := by
  unfold cGe
  rw [ConsLoop.eval_cmp_of s _ _ _ (BitVec.ofNat 64 v) (BitVec.ofNat 64 k) (eval_vv s x _ h) (by simp [evalHOLExact])]
  have hiff := ofNat_lt_iff v k hv hk
  by_cases hh : v < k
  · have h2 : ¬ k ≤ v := by omega
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, bw, hiff, hh, h2]
  · have h2 : k ≤ v := by omega
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, bw, hiff, hh, h2]

theorem ev_lt (x : MlS) (v k : Nat) (hv : v < 2 ^ 64) (hk : k < 2 ^ 64)
    (h : s.locals.lookup x = some (.val (.word (BitVec.ofNat 64 v)))) :
    (EV (cLt x k)) = some (.val (.word (bw (v < k)))) := by
  unfold cLt
  rw [ConsLoop.eval_cmp_of s _ _ _ (BitVec.ofNat 64 v) (BitVec.ofNat 64 k) (eval_vv s x _ h) (by simp [evalHOLExact])]
  have := ofNat_lt_iff v k hv hk
  by_cases hh : v < k <;> simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, bw, hh, this]

theorem ev_ne (x : MlS) (v k : Nat) (hv : v < 2 ^ 64) (hk : k < 2 ^ 64)
    (h : s.locals.lookup x = some (.val (.word (BitVec.ofNat 64 v)))) :
    (EV (cNe x k)) = some (.val (.word (bw (v ≠ k)))) := by
  unfold cNe
  rw [ConsLoop.eval_cmp_of s _ _ _ (BitVec.ofNat 64 v) (BitVec.ofNat 64 k) (eval_vv s x _ h) (by simp [evalHOLExact])]
  have := ofNat_inj v k hv hk
  by_cases hh : v = k <;> simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, bw, hh, this]

theorem ev_and {a b : ExpHOL 64} {p q : Prop} [Decidable p] [Decidable q]
    (ha : (EV a) = some (.val (.word (bw p)))) (hb : (EV b) = some (.val (.word (bw q)))) :
    (EV (eAnd a b)) = some (.val (.word (bw (p ∧ q)))) := by
  unfold eAnd
  rw [evalHOLExact]; simp [evalListHOLExact, ha, hb, wordOpHOL, wordOp, valueIsWord, valueWord]
  by_cases hp : p <;> by_cases hq : q <;> simp [bw, hp, hq] <;> decide

theorem ev_or {a b : ExpHOL 64} {p q : Prop} [Decidable p] [Decidable q]
    (ha : (EV a) = some (.val (.word (bw p)))) (hb : (EV b) = some (.val (.word (bw q)))) :
    (EV (eOr a b)) = some (.val (.word (bw (p ∨ q)))) := by
  unfold eOr
  rw [evalHOLExact]; simp [evalListHOLExact, ha, hb, wordOpHOL, wordOp, valueIsWord, valueWord]
  by_cases hp : p <;> by_cases hq : q <;> simp [bw, hp, hq] <;> decide

theorem ev_add {a b : ExpHOL 64} {v w : BitVec 64}
    (ha : (EV a) = some (.val (.word v))) (hb : (EV b) = some (.val (.word w))) :
    (EV (.op .add [a, b])) = some (.val (.word (v + w))) := by
  rw [evalHOLExact]; simp [evalListHOLExact, ha, hb, wordOpHOL, wordOp, valueIsWord, valueWord]

theorem stepE_val (p1 p2 p3 p4 : Prop) [Decidable p1] [Decidable p2] [Decidable p3] [Decidable p4] :
    bw p1 + ((bw p2 <<< 1) + ((bw p3 + (bw p3 <<< 1)) + (bw p4 <<< 2))) =
      BitVec.ofNat 64 ((if p1 then 1 else 0) + ((if p2 then 2 else 0) + ((if p3 then 3 else 0) +
        (if p4 then 4 else 0)))) := by
  by_cases h1 : p1 <;> by_cases h2 : p2 <;> by_cases h3 : p3 <;> by_cases h4 : p4 <;>
    simp [bw, h1, h2, h3, h4] <;> decide

/-- **`stepE` computes `stepN`** of the four bytes in `c`, `u1`, `u2`, `u3`. -/
theorem ev_stepE (a b c d : Nat) (ha : a < 256) (hb : b < 256) (hc : c < 256) (hd : d < 256)
    (la : s.locals.lookup sC = some (.val (.word (BitVec.ofNat 64 a))))
    (lb : s.locals.lookup sU1 = some (.val (.word (BitVec.ofNat 64 b))))
    (lc : s.locals.lookup sU2 = some (.val (.word (BitVec.ofNat 64 c))))
    (ld : s.locals.lookup sU3 = some (.val (.word (BitVec.ofNat 64 d)))) :
    (EV stepE) = some (.val (.word (BitVec.ofNat 64 (stepN a b c d)))) := by
  have ga := fun k (hk : k < 256) => ev_ge s sC a k (by omega) (by omega) la
  have la' := fun k (hk : k < 256) => ev_lt s sC a k (by omega) (by omega) la
  have na := fun k (hk : k < 256) => ev_ne s sC a k (by omega) (by omega) la
  have gb := fun k (hk : k < 256) => ev_ge s sU1 b k (by omega) (by omega) lb
  have lb' := fun k (hk : k < 256) => ev_lt s sU1 b k (by omega) (by omega) lb
  have gc := fun k (hk : k < 256) => ev_ge s sU2 c k (by omega) (by omega) lc
  have lc' := fun k (hk : k < 256) => ev_lt s sU2 c k (by omega) (by omega) lc
  have gd := fun k (hk : k < 256) => ev_ge s sU3 d k (by omega) (by omega) ld
  have ld' := fun k (hk : k < 256) => ev_lt s sU3 d k (by omega) (by omega) ld
  have e1 : (EV p1E) = some (.val (.word (bw (P1 a)))) :=
    ev_and s (ga 32 (by decide)) (ev_and s (la' 128 (by decide)) (ev_and s (na 34 (by decide)) (na 92 (by decide))))
  have e2 : (EV p2E) = some (.val (.word (bw (P2 a b)))) :=
    ev_and s (ga 194 (by decide)) (ev_and s (la' 224 (by decide))
      (ev_and s (gb 128 (by decide)) (lb' 192 (by decide))))
  have e3 : (EV p3E) = some (.val (.word (bw (P3 a b c)))) :=
    ev_and s (ga 224 (by decide)) (ev_and s (la' 240 (by decide))
      (ev_and s (ev_or s (na 224 (by decide)) (gb 160 (by decide))) (ev_and s (gb 128 (by decide))
        (ev_and s (ev_or s (na 237 (by decide)) (lb' 160 (by decide))) (ev_and s (lb' 192 (by decide))
          (ev_and s (gc 128 (by decide)) (lc' 192 (by decide))))))))
  have e4 : (EV p4E) = some (.val (.word (bw (P4 a b c d)))) :=
    ev_and s (ga 240 (by decide)) (ev_and s (la' 245 (by decide))
      (ev_and s (ev_or s (na 240 (by decide)) (gb 144 (by decide))) (ev_and s (gb 128 (by decide))
        (ev_and s (ev_or s (na 244 (by decide)) (lb' 144 (by decide))) (ev_and s (lb' 192 (by decide))
          (ev_and s (gc 128 (by decide)) (ev_and s (lc' 192 (by decide))
            (ev_and s (gd 128 (by decide)) (ld' 192 (by decide))))))))))
  unfold stepE
  rw [ev_add s e1 (ev_add s (eval_shl s _ _ _ e2 (by decide))
    (ev_add s (ev_add s e3 (eval_shl s _ _ _ e3 (by decide))) (eval_shl s _ _ _ e4 (by decide))))]
  rw [show (1 : BitVec 64).toNat = 1 from rfl, show (2 : BitVec 64).toNat = 2 from rfl]
  exact congrArg (fun v => some (ValueHOL.val (HolWordLab.word v))) (stepE_val _ _ _ _)

end

/-! ## The walk in Pancake -/

def addC (x : MlS) (k : Nat) : ExpHOL 64 := .op .add [vv x, .const (BitVec.ofNat 64 k)]

/-- One step: the four bytes at `e`, their character length `uk`; advance by it, or stop. -/
def u8Body : ProgHOL 64 :=
  .seq (bAt sC (vv sE2)) (.seq (bAt sU1 (addC sE2 1)) (.seq (bAt sU2 (addC sE2 2))
    (.seq (bAt sU3 (addC sE2 3))
      (.seq (.assign .local sUK stepE)
        (.ite (vv sUK) (.assign .local sE2 (.op .add [vv sE2, vv sUK])) (.assign .local sG (.const 0)))))))

def u8Loop : ProgHOL 64 := .while (vv sG) u8Body

section
variable {σ : Type}

/-- The walk's invariant: the frame, the buffer, word-valued scratch locals, and a position `j`
with `[i0, j)` a good body. -/
def U8I (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (i0 : Nat)
    (u : PanSemStateFiniteExact 64 σ) : Prop :=
  u.memory = t.memory ∧ u.memaddrs = t.memaddrs ∧ u.code = t.code ∧ u.globals = t.globals ∧
  u.be = t.be ∧
  u.locals.lookup sB = some (.val (.word A)) ∧
  u.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 bs.length))) ∧
  (∃ w, u.locals.lookup sC = some (.val (.word w))) ∧
  (∃ w, u.locals.lookup sU1 = some (.val (.word w))) ∧
  (∃ w, u.locals.lookup sU2 = some (.val (.word w))) ∧
  (∃ w, u.locals.lookup sU3 = some (.val (.word w))) ∧
  (∃ w, u.locals.lookup sUK = some (.val (.word w))) ∧
  (∃ w, u.locals.lookup sG = some (.val (.word w))) ∧
  (∃ w, u.locals.lookup sY = some (.val (.word w))) ∧
  ∃ j, i0 ≤ j ∧ j ≤ bs.length ∧ u.locals.lookup sE2 = some (.val (.word (BitVec.ofNat 64 j))) ∧
    SegOK bs i0 j

theorem ev_addC (u : PanSemStateFiniteExact 64 σ) (x : MlS) (j k : Nat) (_hjk : j + k < 2 ^ 64)
    (h : u.locals.lookup x = some (.val (.word (BitVec.ofNat 64 j)))) :
    @evalHOLExact 64 σ _ u.toExact (fun a => Classical.propDecidable (u.memaddrs a)) (addC x k) =
      some (.val (.word (BitVec.ofNat 64 (j + k)))) := by
  unfold addC
  rw [eval_add_c u x _ _ h]; congr 3; apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_add]

theorem u8_step (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (i0 : Nat)
    (hroom : bs.length + 4 < 2 ^ 64) (hb : BytesAt t A bs) (u : PanSemStateFiniteExact 64 σ)
    (hu : U8I t A bs i0 u) :
    ∃ u', evaluateHOLFiniteState (decClockHOLFinite u) u8Body = (none, u') ∧ U8I t A bs i0 u' := by
  obtain ⟨m0, d0, c0, g0, b0, lb, ln, ⟨wc, lc⟩, ⟨w1, l1⟩, ⟨w2, l2⟩, ⟨w3, l3⟩, ⟨wk, lK⟩, ⟨wg, lg⟩,
    ⟨wy, ly⟩, j, hij, hj, le, hseg⟩ := hu
  let v := decClockHOLFinite u
  have hbv : BytesAt v A bs := bytesAt_congr hb m0 d0 b0
  unfold u8Body
  rw [seq_normal _ (bAt_spec v A bs sC (vv sE2) j hbv (by omega) wc (by lk [v]; exact lc)
    (by lk [v]; exact lb) (by lk [v]; exact ln) (eval_vv v sE2 _ (by lk [v]; exact le)))]
  let v1 := setVarHOLFinite sC (.val (.word (BitVec.ofNat 64 (byteL bs j).toNat))) v
  rw [seq_normal _ (bAt_spec v1 A bs sU1 (addC sE2 1) (j + 1) hbv (by omega) w1 (by lk [v1, v]; exact l1)
    (by lk [v1, v]; exact lb) (by lk [v1, v]; exact ln) (ev_addC v1 sE2 j 1 (by omega) (by lk [v1, v]; exact le)))]
  let v2 := setVarHOLFinite sU1 (.val (.word (BitVec.ofNat 64 (byteL bs (j + 1)).toNat))) v1
  rw [seq_normal _ (bAt_spec v2 A bs sU2 (addC sE2 2) (j + 2) hbv (by omega) w2 (by lk [v2, v1, v]; exact l2)
    (by lk [v2, v1, v]; exact lb) (by lk [v2, v1, v]; exact ln)
    (ev_addC v2 sE2 j 2 (by omega) (by lk [v2, v1, v]; exact le)))]
  let v3 := setVarHOLFinite sU2 (.val (.word (BitVec.ofNat 64 (byteL bs (j + 2)).toNat))) v2
  rw [seq_normal _ (bAt_spec v3 A bs sU3 (addC sE2 3) (j + 3) hbv (by omega) w3
    (by lk [v3, v2, v1, v]; exact l3) (by lk [v3, v2, v1, v]; exact lb) (by lk [v3, v2, v1, v]; exact ln)
    (ev_addC v3 sE2 j 3 (by omega) (by lk [v3, v2, v1, v]; exact le)))]
  let v4 := setVarHOLFinite sU3 (.val (.word (BitVec.ofNat 64 (byteL bs (j + 3)).toNat))) v3
  rw [seq_normal _ (ConsLoop.assign_local v4 sUK stepE (BitVec.ofNat 64 (stepL bs j)) wk
    (ev_stepE v4 _ _ _ _ (UInt8.toNat_lt _) (UInt8.toNat_lt _) (UInt8.toNat_lt _) (UInt8.toNat_lt _)
      (by lk [v4, v3, v2, v1]) (by lk [v4, v3, v2]) (by lk [v4, v3]) (by lk [v4]))
    (by lk [v4, v3, v2, v1, v]; exact lK))]
  let v5 := setVarHOLFinite sUK (.val (.word (BitVec.ofNat 64 (stepL bs j)))) v4
  rw [ite_word v5 _ _ _ _ (eval_vv v5 sUK (.val (.word (BitVec.ofNat 64 (stepL bs j)))) (by lk [v5]))]
  have hk10 := stepN_le (byteL bs j).toNat (byteL bs (j + 1)).toNat (byteL bs (j + 2)).toNat
    (byteL bs (j + 3)).toNat
  by_cases hk : stepL bs j = 0
  · have h0 : BitVec.ofNat 64 (stepL bs j) = 0 := by rw [hk]; rfl
    simp only [h0, ne_eq, not_true_eq_false, ↓reduceIte]
    rw [ConsLoop.assign_local v5 sG (.const 0) 0 wg (by simp [evalHOLExact])
      (by lk [v5, v4, v3, v2, v1, v]; exact lg)]
    exact ⟨_, rfl, m0, d0, c0, g0, b0, by lk [v5, v4, v3, v2, v1, v]; exact lb,
      by lk [v5, v4, v3, v2, v1, v]; exact ln, ⟨BitVec.ofNat 64 (byteL bs j).toNat, by lk [v5, v4, v3, v2, v1]⟩,
      ⟨BitVec.ofNat 64 (byteL bs (j + 1)).toNat, by lk [v5, v4, v3, v2]⟩,
      ⟨BitVec.ofNat 64 (byteL bs (j + 2)).toNat, by lk [v5, v4, v3]⟩,
      ⟨BitVec.ofNat 64 (byteL bs (j + 3)).toNat, by lk [v5, v4]⟩,
      ⟨BitVec.ofNat 64 (stepL bs j), by lk [v5]⟩, ⟨0, by lk⟩,
      ⟨wy, by lk [v5, v4, v3, v2, v1, v]; exact ly⟩, j, hij, hj, by lk [v5, v4, v3, v2, v1, v]; exact le, hseg⟩
  · have hne : BitVec.ofNat 64 (stepL bs j) ≠ 0 := by
      intro h; apply hk
      have := (ofNat_inj (stepL bs j) 0 (by unfold stepL; omega) (by decide)).mp (by rw [h]; rfl)
      exact this
    simp only [hne, ne_eq, not_false_eq_true, ↓reduceIte]
    obtain ⟨hle, hseg2⟩ := stepL_ok bs j hk
    rw [ConsLoop.assign_local v5 sE2 (.op .add [vv sE2, vv sUK]) (BitVec.ofNat 64 (j + stepL bs j))
      (BitVec.ofNat 64 j) (by
        rw [ev_add v5 (eval_vv v5 sE2 _ (by lk [v5, v4, v3, v2, v1, v]; exact le)) (eval_vv v5 sUK (.val (.word (BitVec.ofNat 64 (stepL bs j)))) (by lk [v5]))]
        congr 3; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add])
      (by lk [v5, v4, v3, v2, v1, v]; exact le)]
    exact ⟨_, rfl, m0, d0, c0, g0, b0, by lk [v5, v4, v3, v2, v1, v]; exact lb,
      by lk [v5, v4, v3, v2, v1, v]; exact ln, ⟨BitVec.ofNat 64 (byteL bs j).toNat, by lk [v5, v4, v3, v2, v1]⟩,
      ⟨BitVec.ofNat 64 (byteL bs (j + 1)).toNat, by lk [v5, v4, v3, v2]⟩,
      ⟨BitVec.ofNat 64 (byteL bs (j + 2)).toNat, by lk [v5, v4, v3]⟩,
      ⟨BitVec.ofNat 64 (byteL bs (j + 3)).toNat, by lk [v5, v4]⟩,
      ⟨BitVec.ofNat 64 (stepL bs j), by lk [v5]⟩,
      ⟨wg, by lk [v5, v4, v3, v2, v1, v]; exact lg⟩,
      ⟨wy, by lk [v5, v4, v3, v2, v1, v]; exact ly⟩, j + stepL bs j, by omega, hle, by lk,
      segOK_trans hseg hseg2 hij (by omega)⟩

theorem u8Loop_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (i0 : Nat)
    (hroom : bs.length + 4 < 2 ^ 64) (hb : BytesAt t A bs) (u : PanSemStateFiniteExact 64 σ)
    (hu : U8I t A bs i0 u) :
    Stop (evaluateHOLFiniteState u u8Loop).1 ∨ ((evaluateHOLFiniteState u u8Loop).1 = none ∧
      U8I t A bs i0 (evaluateHOLFiniteState u u8Loop).2) := by
  refine while_stop (vv sG) u8Body (U8I t A bs i0) (U8I t A bs i0) (fun u hu => ?_) u hu
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨wg, lg⟩, -⟩ := id hu
  refine ⟨wg, by simp [evalHOLFinite, vv, evalHOLExact, lg], fun _ => hu, fun _ _ => ?_⟩
  obtain ⟨u', e, hu'⟩ := u8_step t A bs i0 hroom hb u hu
  rw [e]; exact Or.inr ⟨rfl, hu'⟩

end

end ConPanqueque.Scan
