import ConPanqueque.Scan.HintVal

/-! # A definition's safety: the literal `"safe"`

`sfFun(b, n, p)` returns `p + 6` when the bytes at `p` are `"safe"` (quotes included) and rejects
anything else.  `sfFun_sound`: when con-leche's `scanString b p` gives `x`, a return means
`x = "safe"`.  (A safety con-leche reads as `safe` through escapes is rejected, which is sound.) -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

namespace ConPanqueque.Scan

open ConLeche.Frontend

def safeCands : List (List UInt8 × Nat) := [([34, 115, 97, 102, 101, 34], 6)]

def fSafe := ofString "isSafe"

def sfFun : ProgHOL 64 :=
  .dec sJ .one (vv sI) (.dec sL .one (.const 0) (.dec sX .one (.const 0) (.dec sY .one (.const 0)
    (.dec sOk .one (.const 0) (genChoice hang safeCands)))))

section
variable {σ : Type}

theorem sfFun_spec (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (bs : List UInt8) (i : Nat)
    (hb : BytesAt t A bs) (hi : i + 32 < 2 ^ 64)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 bs.length))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 i)))) :
    RetP t sfFun (fun w => ∃ off, choiceL bs i safeCands = some off ∧ w = BitVec.ofNat 64 (i + off)) :=
  choiceEntry t A bs i lb ln li _ _ (fun u hu =>
    genChoice_spec t A bs i 0 hb hi hang _ safeCands u (by decide) hu (fun off h => ⟨off, h, rfl⟩)
      (fun _ u' _ => retP_hang u' _))

theorem scanString_det {b : ByteArray} {p e e' : USize} {x x' : String}
    (h : scanString b p = .ok x e) (h' : scanString b p = .ok x' e') : x = x' := by
  rw [h] at h'; simp only [ScanRes.ok.injEq] at h'; exact h'.1

/-- **The safety check is sound**: a return means the string con-leche scans at `p` is `safe`. -/
theorem sfFun_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (p : USize) (hpb : p.toNat ≤ b.size) (x : String) (e : USize)
    (hx : scanString b p = .ok x e)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 p.toNat)))) :
    RetP t sfFun (fun _ => x = "safe") := by
  have hroom := hp.room
  rcases sfFun_spec t A b.data.toList p.toNat hb (by omega) lb (by simpa using ln) li with hs | ⟨w, r1, ⟨off, hc, -⟩, r2⟩
  · exact Or.inl hs
  refine Or.inr ⟨w, r1, ?_, r2⟩
  simp only [choiceL, safeCands] at hc
  split at hc
  · rename_i hl
    have g : ∀ m (hm : m < 6), byteL b.data.toList (p.toNat + 0 + m) = [34, 115, 97, 102, 101, 34][m] :=
      fun m hm => litsL_get _ _ _ 0 hl m hm
    have b0 := g 0 (by decide)
    have b5 := g 5 (by decide)
    have hpl5 : p.toNat + 5 < b.size := by
      have := lt_of_byteL (c := 34) (by rw [b5]; rfl) (by decide); simpa using this
    have hEU : (USize.ofNat (p.toNat + 5)).toNat = p.toNat + 5 := by
      rw [USize.toNat_ofNat']; simp only [USize.size_eq_two_pow, hp.bits]; exact Nat.mod_eq_of_lt (by omega)
    have gb : ∀ m, m < 6 → b.data.toList[p.toNat + m]? = some ([34, 115, 97, 102, 101, 34] : List UInt8)[m]! := by
      intro m hm
      have := g m hm
      simp only [Nat.add_zero, byteL] at this
      have hl' : p.toNat + m < b.data.toList.length := by simp; omega
      rw [List.getElem?_eq_getElem hl'] at this ⊢
      simp at this; rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 by omega) with
        rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
    obtain ⟨s, hs1, hs2⟩ := scanString_plain hp p (USize.ofNat (p.toNat + 5)) (by omega) (by rw [hEU]; omega)
      (by rw [hEU]; omega)
      (by have := gb 0 (by decide); rw [List.getElem?_eq_getElem (by simp; omega)] at this; simpa using this)
      (by simp only [hEU]; have := gb 5 (by decide)
          rw [List.getElem?_eq_getElem (by simp; omega)] at this; simpa using this)
      (fun k hk h1 h2 => by
        rw [hEU] at h2
        have hk' : k = p.toNat + 1 ∨ k = p.toNat + 2 ∨ k = p.toNat + 3 ∨ k = p.toNat + 4 := by omega
        rcases hk' with rfl | rfl | rfl | rfl
        · have h := gb 1 (by decide); simp only [List.getElem?_eq_getElem hk, Option.some.injEq] at h
          simp only [h]; decide
        · have h := gb 2 (by decide); simp only [List.getElem?_eq_getElem hk, Option.some.injEq] at h
          simp only [h]; decide
        · have h := gb 3 (by decide); simp only [List.getElem?_eq_getElem hk, Option.some.injEq] at h
          simp only [h]; decide
        · have h := gb 4 (by decide); simp only [List.getElem?_eq_getElem hk, Option.some.injEq] at h
          simp only [h]; decide)
    rw [scanString_det hx hs1]
    have hp1 : (p + 1).toNat = p.toNat + 1 := ConLeche.Frontend.usizeStep b p ((hp.lt_iff p).mpr (by omega))
    rw [hp1, hEU] at hs2
    apply String.toByteArray_inj.mp
    show s.toUTF8 = "safe".toUTF8
    rw [hs2]
    apply ByteArray.ext
    rw [ByteArray.data_extract]
    apply Array.ext'
    rw [Array.toList_extract, List.extract_eq_take_drop]
    have : "safe".toUTF8.data.toList = [115, 97, 102, 101] := by decide
    rw [this, show p.toNat + 5 - (p.toNat + 1) = 4 by omega]
    apply List.ext_getElem?
    intro m
    rw [List.getElem?_take, List.getElem?_drop]
    by_cases hm : m < 4
    · rw [ite_eq_left hm, show p.toNat + 1 + m = p.toNat + (m + 1) by omega, gb (m + 1) (by omega)]
      rcases (show m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 by omega) with rfl | rfl | rfl | rfl <;> rfl
    · rw [ite_eq_right hm]
      simp [List.getElem?_eq_none (by simp; omega : [115, 97, 102, 101].length ≤ m)]; omega
  · simp at hc

end

end ConPanqueque.Scan
