import ConPanqueque.Front.ReadBuf
import ConPanqueque.Prelude.Text

/-! # The built-in prelude's bytes, as words

`preBytes`: the UTF-8 of con-leche's `builtinPreludeText`, the bytes its `parseExportD` parses.
`packW`: eight bytes to a little-endian word.  The program stores `preWords := packW preBytes`
word by word (`storesP`), and `packed_packW` says the image then holds the bytes `Packed`, the form
the frontend's buffer relation reads (`BufOK`). -/

open ConRon.Arena

namespace ConPanqueque.Prelude

open ConPanqueque.Front ConPanqueque.T

/-- Little-endian number of a byte list. -/
def leNum : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 256 * leNum bs

/-- Eight bytes to a word, little-endian; the last word may hold fewer. -/
def packW (bs : List UInt8) : List (BitVec 64) :=
  if h : bs = [] then [] else BitVec.ofNat 64 (leNum (bs.take 8)) :: packW (bs.drop 8)
termination_by bs.length
decreasing_by
  have : bs.length ≠ 0 := by simpa using h
  simp; omega

theorem leNum_lt : ∀ bs : List UInt8, leNum bs < 256 ^ bs.length
  | [] => by simp [leNum]
  | b :: bs => by
    have := leNum_lt bs; have := b.toNat_lt
    simp only [leNum, List.length_cons, Nat.pow_succ]; omega

theorem leNum_byte : ∀ (bs : List UInt8) (k : Nat) (hk : k < bs.length), leNum bs / 256 ^ k % 256 = bs[k].toNat
  | b :: bs, 0, _ => by have := b.toNat_lt; simp [leNum]; try omega
  | b :: bs, k + 1, hk => by
    have ih := leNum_byte bs k (by simpa using hk)
    simp only [leNum, List.getElem_cons_succ, Nat.pow_succ]
    rw [Nat.mul_comm (256 ^ k), ← Nat.div_div_eq_div_mul,
      show (b.toNat + 256 * leNum bs) / 256 = leNum bs by have := b.toNat_lt; omega]
    exact ih

theorem packW_length_aux : ∀ n (bs : List UInt8), bs.length ≤ n → (packW bs).length = (bs.length + 7) / 8
  | 0, bs, h => by
    have : bs = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst this; simp [packW]
  | n + 1, bs, h => by
    rw [packW]; split
    · rename_i e; subst e; rfl
    · rename_i e
      have hl : bs.length ≠ 0 := by simpa using e
      have := packW_length_aux n (bs.drop 8) (by simp; omega)
      rw [List.length_cons, this, List.length_drop]; omega

theorem packW_length (bs : List UInt8) : (packW bs).length = (bs.length + 7) / 8 :=
  packW_length_aux _ bs (Nat.le_refl _)

theorem packW_get : ∀ (bs : List UInt8) (i : Nat) (hi : i < bs.length),
    ∃ w, (packW bs)[i / 8]? = some w ∧ ConPanqueque.Logic.byteW w (i % 8) = bs[i].toNat
  | bs, i, hi => by
    rw [packW]
    have h : bs ≠ [] := by intro e; subst e; simp at hi
    rw [dif_neg h]
    by_cases hi8 : i < 8
    · refine ⟨_, by rw [show i / 8 = 0 by omega]; rfl, ?_⟩
      have hlt := leNum_lt (bs.take 8)
      have hlen : (bs.take 8).length ≤ 8 := by simp
      have h64 : leNum (bs.take 8) < 2 ^ 64 :=
        Nat.lt_of_lt_of_le hlt (by rw [show (2 : Nat) ^ 64 = 256 ^ 8 by norm_num]; exact Nat.pow_le_pow_right (by omega) hlen)
      unfold ConPanqueque.Logic.byteW
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt h64, show i % 8 = i by omega,
        leNum_byte (bs.take 8) i (by simp; omega)]
      simp
    · obtain ⟨w, hw, hb⟩ := packW_get (bs.drop 8) (i - 8) (by simp; omega)
      refine ⟨w, ?_, ?_⟩
      · rw [show i / 8 = (i - 8) / 8 + 1 by omega, List.getElem?_cons_succ]; exact hw
      · rw [show i % 8 = (i - 8) % 8 by omega, hb]; simp [show 8 + (i - 8) = i by omega]
termination_by bs => bs.length
decreasing_by simp; omega

/-- **The stored words hold the bytes.** -/
theorem packed_packW (H : List (BitVec 64)) (r : Nat) (bs : List UInt8)
    (hH : r + (packW bs).length ≤ H.length) :
    Packed (kcH H r (packW bs) (packW bs).length) r bs := by
  intro i hi
  obtain ⟨w, hw, hb⟩ := packW_get bs i hi
  have hl := packW_length bs
  have hi8 : i / 8 < (packW bs).length := by rw [hl]; omega
  refine ⟨w, ?_, hb⟩
  rw [kcH_get, ite_eq_left ⟨by omega, by omega, by omega⟩, show r + i / 8 - r = i / 8 by omega,
    List.getD_eq_getElem?_getD, hw]; rfl

/-- The prelude's bytes: the UTF-8 con-leche's `parseExportD` parses. -/
def preBytes : ByteArray := ConLeche.Frontend.builtinPreludeText.toUTF8

/-- The prelude's size in bytes. -/
def preSize : Nat := 15700

theorem preBytes_size : preBytes.size = preSize := Text.preludeText_size

/-- The words the program stores. -/
def preWords : List (BitVec 64) := packW preBytes.data.toList

theorem packW_length' (b : ByteArray) : (packW b.data.toList).length = (b.size + 7) / 8 := by
  rw [packW_length, Array.length_toList]; rfl

theorem preWords_length : preWords.length = (preSize + 7) / 8 := by
  unfold preWords
  exact (packW_length' preBytes).trans (congrArg (fun n => (n + 7) / 8) preBytes_size)

end ConPanqueque.Prelude
