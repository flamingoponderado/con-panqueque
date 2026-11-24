import ConPanqueque.Logic.Basic

/-! # Byte loads

The input buffer is bytes packed little-endian, eight to a word, in Pancake memory, read one byte
at a time with `loadByte`.  `BytesAt t a bs` says byte `i` of `bs` is byte `i % 8` of the word at
`a + 8 * (i / 8)`, which is in the memory domain; `eval_loadByte_bytes` is the one rule the scanner
needs. -/

namespace ConPanqueque.Logic
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Byte `k` (little-endian) of a word. -/
def byteW (w : BitVec 64) (k : Nat) : Nat := (w.toNat / 256 ^ k) % 256

theorem byteW_lt (w : BitVec 64) (k : Nat) : byteW w k < 256 := Nat.mod_lt _ (by decide)

/-- The buffer `bs` at the 8-aligned address `a`, little-endian. -/
def BytesAt {σ : Type} (t : PanSemStateFiniteExact 64 σ) (a : BitVec 64) (bs : List UInt8) : Prop :=
  t.be = false ∧ a.toNat % 8 = 0 ∧ a.toNat + bs.length < 2 ^ 64 ∧
    ∀ i (hi : i < bs.length), ∃ w, t.memory (a + BitVec.ofNat 64 (8 * (i / 8))) = .word w ∧
      t.memaddrs (a + BitVec.ofNat 64 (8 * (i / 8))) ∧ byteW w (i % 8) = bs[i].toNat

/-- A byte load from inside the buffer. -/
theorem eval_loadByte_bytes {σ : Type} (s : PanSemStateFiniteExact 64 σ) (e : ExpHOL 64)
    (a : BitVec 64) (bs : List UInt8) (i : Nat) (hb : BytesAt s a bs) (hi : i < bs.length)
    (he : @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) e =
      some (.val (.word (a + BitVec.ofNat 64 i)))) :
    @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) (.loadByte e) =
      some (.val (.word (BitVec.ofNat 64 bs[i].toNat))) := by
  obtain ⟨hbe, hal, hov, hw⟩ := hb
  obtain ⟨w, hm, hd, hbyte⟩ := hw i hi
  have hsum : (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat]; omega
  have hal' : panByteAlignHOL (width := 64) (a + BitVec.ofNat 64 i) =
      a + BitVec.ofNat 64 (8 * (i / 8)) := by
    apply BitVec.eq_of_toNat_eq
    have h8 : (2 : Nat) ^ Nat.log2 (64 / 8) = 8 := by decide
    simp only [panByteAlignHOL, h8, BitVec.toNat_ofNat, hsum, BitVec.toNat_add]
    omega
  have hmod : (a + BitVec.ofNat 64 i).toNat % (64 / 8) = i % 8 := by rw [hsum]; omega
  simp only [evalHOLExact, he, panMemLoadByteHOL, hal', hm, hd, if_true, Option.map_some,
    panGetByteHOL, hbe, Bool.false_eq_true, if_false, hmod]
  have : (w.toNat / 256 ^ (i % 8)) % 256 = bs[i].toNat := hbyte
  simp [this]

end ConPanqueque.Logic
