import ConPanqueque.Front.ByteSet
import ConPanqueque.Front.Main

/-! # A byte-array write into heap cells

`writeH H A0 j0 a xs`: the image after `write_bytearray (A0 + a) xs` when `A0 = cellA C j0` is
8-aligned — each byte replaces one byte of one cell.  `sr_write`: the representation follows. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan

variable {σ : Type}

def writeH (H : List (BitVec 64)) (A0 : BitVec 64) (j0 : Nat) : Nat → List (BitVec 8) → List (BitVec 64)
  | _, [] => H
  | a, x :: xs =>
    let H1 := writeH H A0 j0 (a + 1) xs
    H1.set (j0 + a / 8) (panSetByteHOL (A0 + BitVec.ofNat 64 a) (BitVec.ofNat 64 x.toNat)
      (H1[j0 + a / 8]?.getD 0) false)

theorem writeH_length (H : List (BitVec 64)) (A0 : BitVec 64) (j0 : Nat) :
    ∀ a xs, (writeH H A0 j0 a xs).length = H.length
  | _, [] => rfl
  | a, x :: xs => by simp [writeH, writeH_length H A0 j0 (a + 1) xs]

theorem align_cell (A0 : BitVec 64) (a : Nat) (hal : A0.toNat % 8 = 0) (hov : A0.toNat + a < 2 ^ 64) :
    panByteAlignHOL (A0 + BitVec.ofNat 64 a) = A0 + BitVec.ofNat 64 (8 * (a / 8)) := by
  unfold panByteAlignHOL
  simp only [show Nat.log2 (64 / 8) = 3 from rfl, show (2 : Nat) ^ 3 = 8 from rfl]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  have h1 : (A0.toNat + a % 2 ^ 64) % 2 ^ 64 = A0.toNat + a := by
    rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega)]; exact Nat.mod_eq_of_lt hov
  have h2 : (8 * (a / 8)) % 2 ^ 64 = 8 * (a / 8) := Nat.mod_eq_of_lt (by omega)
  rw [h1, h2, Nat.mod_eq_of_lt (show A0.toNat + 8 * (a / 8) < 2 ^ 64 by omega)]
  rw [Nat.mod_eq_of_lt (show (A0.toNat + a) / 8 * 8 < 2 ^ 64 by omega)]
  omega

/-- **A byte-array write into heap cells keeps the representation**, at the written image. -/
theorem sr_write {C : Ctx} (hok : CtxOK C) {s : AState} (j0 : Nat) (hal : (cellA C j0).toNat % 8 = 0) :
    ∀ (xs : List (BitVec 8)) (a : Nat) (t : PState σ) [inst : DecidablePred t.memaddrs], SR C s t →
      j0 + (a + xs.length + 7) / 8 ≤ C.H.length → (cellA C j0).toNat + a + xs.length < 2 ^ 64 →
      SR (ctxH C (writeH C.H (cellA C j0) j0 a xs)) s
        { t with memory := (@panWriteBytearrayWord8HOL 64 _ (cellA C j0 + BitVec.ofNat 64 a) xs t.memory t.memaddrs
            inst false) }
  | [], a, t, inst, h, _, _ => by
    simp only [writeH, panWriteBytearrayWord8HOL]; rw [ctxH_self]; exact h
  | x :: xs, a, t, inst, h, hr, hov => by
    have ih := sr_write hok j0 hal xs (a + 1) t h (by simp at hr; omega) (by simp at hov; omega)
    let H1 := writeH C.H (cellA C j0) j0 (a + 1) xs
    let t1 : PState σ := { t with memory := (@panWriteBytearrayWord8HOL 64 _ (cellA C j0 + BitVec.ofNat 64 (a + 1)) xs
      t.memory t.memaddrs inst false) }
    have hj : j0 + a / 8 < H1.length := by
      simp only [H1, writeH_length]; simp at hr; omega
    have hc := heap_cell (C := ctxH C H1) ih (j0 + a / 8) hj
    have hal' : panByteAlignHOL (cellA C j0 + BitVec.ofNat 64 a) = cellA C (j0 + a / 8) := by
      rw [align_cell _ _ hal (by simp at hov; omega), cellA_add]
    have hadd : cellA C j0 + BitVec.ofNat 64 a + 1 = cellA C j0 + BitVec.ofNat 64 (a + 1) := by
      rw [BitVec.add_assoc, show (1 : BitVec 64) = BitVec.ofNat 64 1 from rfl, ofNat_add64]
    have hst := sr_heapStore (ctxOK_ctxH hok) ih (j0 + a / 8) hj
      (panSetByteHOL (cellA C j0 + BitVec.ofNat 64 a) (BitVec.ofNat 64 x.toNat) (H1[j0 + a / 8]?.getD 0) false)
    have e : (@panWriteBytearrayWord8HOL 64 _ (cellA C j0 + BitVec.ofNat 64 a) (x :: xs) t.memory t.memaddrs inst false) =
        fun c => if c = cellA (ctxH C H1) (j0 + a / 8) then
          .word (panSetByteHOL (cellA C j0 + BitVec.ofNat 64 a) (BitVec.ofNat 64 x.toNat) (H1[j0 + a / 8]?.getD 0) false)
          else t1.memory c := by
      simp only [panWriteBytearrayWord8HOL, hadd]
      have hm : (@panWriteBytearrayWord8HOL 64 _ (cellA C j0 + BitVec.ofNat 64 (a + 1)) xs t.memory t.memaddrs inst false)
          (cellA C (j0 + a / 8)) = .word H1[j0 + a / 8] := hc.2
      have hd : t.memaddrs (cellA C (j0 + a / 8)) := hc.1
      simp only [panMemStoreByteWord8HOL, hal', hm, if_pos hd, List.getElem?_eq_getElem hj, Option.getD_some]
      rfl
    rw [show ({ t with memory := (@panWriteBytearrayWord8HOL 64 _ (cellA C j0 + BitVec.ofNat 64 a) (x :: xs) t.memory
      t.memaddrs inst false) } : PState σ) = { t1 with memory := (fun c => if c = cellA (ctxH C H1) (j0 + a / 8) then
        .word (panSetByteHOL (cellA C j0 + BitVec.ofNat 64 a) (BitVec.ofNat 64 x.toNat) (H1[j0 + a / 8]?.getD 0) false)
        else t1.memory c) } by rw [e]]
    exact hst

theorem addr_mod8 (A0 : BitVec 64) (a : Nat) (hal : A0.toNat % 8 = 0) (hov : A0.toNat + a < 2 ^ 64) :
    (A0 + BitVec.ofNat 64 a).toNat % 8 = a % 8 := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show a < 2 ^ 64 by omega), Nat.mod_eq_of_lt hov]; omega

theorem getElem?_set' (H : List (BitVec 64)) (j c : Nat) (w : BitVec 64) (hj : j < H.length) :
    (H.set j w)[c]? = if j = c then some w else H[c]? := by
  rw [List.getElem?_set]; split <;> simp_all

/-- **Reading back**: byte `p` of the written image. -/
theorem writeH_byte (H : List (BitVec 64)) (A0 : BitVec 64) (j0 : Nat) (hal : A0.toNat % 8 = 0) :
    ∀ (xs : List (BitVec 8)) (a p : Nat), j0 + (a + xs.length + 7) / 8 ≤ H.length →
      A0.toNat + a + xs.length < 2 ^ 64 →
      byteW ((writeH H A0 j0 a xs)[j0 + p / 8]?.getD 0) (p % 8) =
        if a ≤ p ∧ p < a + xs.length then (xs[p - a]?.getD 0).toNat
        else byteW (H[j0 + p / 8]?.getD 0) (p % 8)
  | [], a, p, _, _ => by simp [writeH]
  | x :: xs, a, p, hr, hov => by
    have ih := writeH_byte H A0 j0 hal xs (a + 1) p (by simp at hr; omega) (by simp at hov; omega)
    have hlen : j0 + a / 8 < (writeH H A0 j0 (a + 1) xs).length := by rw [writeH_length]; simp at hr; omega
    have hm8 := addr_mod8 A0 a hal (by simp at hov; omega)
    simp only [writeH]
    rw [getElem?_set' _ _ _ _ hlen]
    simp only [List.length_cons] at *
    by_cases hc : j0 + a / 8 = j0 + p / 8
    · rw [if_pos hc, Option.getD_some, byteW_setByte _ _ _ _ (Nat.mod_lt _ (by decide)), hm8]
      by_cases hpa : p = a
      · subst hpa
        rw [if_pos rfl, if_pos ⟨Nat.le_refl _, by omega⟩]
        simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, BitVec.toNat_ofNat]
        have := x.isLt; omega
      · have hne : ¬ p % 8 = a % 8 := by omega
        rw [if_neg hne, hc, ih]
        by_cases hin : a + 1 ≤ p ∧ p < a + 1 + xs.length
        · rw [if_pos hin, if_pos ⟨by omega, by omega⟩, show p - a = (p - (a + 1)) + 1 by omega,
            List.getElem?_cons_succ]
        · rw [if_neg hin, if_neg (by omega)]
    · rw [if_neg hc, ih]
      have hpa : p ≠ a := fun h => hc (by rw [h])
      by_cases hin : a + 1 ≤ p ∧ p < a + 1 + xs.length
      · rw [if_pos hin, if_pos ⟨by omega, by omega⟩, show p - a = (p - (a + 1)) + 1 by omega, List.getElem?_cons_succ]
      · rw [if_neg hin, if_neg (by omega)]

end ConPanqueque.Front
