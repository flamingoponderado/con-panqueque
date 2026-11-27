import ConPanqueque.Scan.Safe

/-!
# A quotient record's kind string

`qkFun`: the string at `sI` is one of `"type"`, `"ctor"`, `"lift"`, `"ind"` (else hang); the return is `sI + k`
with `k` the kind's number (`1 … 4`). `qkFun_sound`: the string con-leche scans there is that kind's.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V

namespace ConPanqueque.Scan

open ConLeche.Frontend

set_option autoImplicit false

theorem getElem_of_some {l : List UInt8} {i : Nat} {v : UInt8} (h : l[i]? = some v) (hi : i < l.length) :
    l[i] = v := by
  rw [List.getElem?_eq_getElem hi] at h; exact Option.some.inj h

/-- A quoted plain literal: the string con-leche scans where its bytes stand is the literal. -/
theorem litStr_sound {b : ByteArray} (hp : Plat b) (p : USize) (str : String) (cs : List UInt8)
    (hcs : str.toUTF8.data.toList = cs) (hplain : ∀ c ∈ cs, isPlainN c.toNat = true)
    (hlit : litsL b.data.toList p.toNat (34 :: cs ++ [34]) 0 = true)
    {x : String} {e : USize} (hx : scanString b p = .ok x e) : x = str := by
  have g := litsL_get _ _ _ 0 hlit
  have hn : (34 :: cs ++ [34]).length = cs.length + 2 := by simp
  have hroom := hp.room
  have hnz : ∀ (m : Nat) (v : UInt8), (34 :: (cs ++ [34]))[m]? = some v → v ≠ 0 := by
    intro m v hv
    rcases m with _ | j
    · simp at hv; subst hv; decide
    · rw [List.getElem?_cons_succ] at hv
      rcases Nat.lt_or_ge j cs.length with hj | hj
      · rw [List.getElem?_append_left hj, List.getElem?_eq_getElem hj] at hv
        have hc := hplain _ (List.getElem_mem hj)
        simp only [Option.some.injEq] at hv; subst hv
        intro hz; rw [hz] at hc; simp [isPlainN] at hc
      · rw [List.getElem?_append_right hj] at hv
        rcases Nat.lt_or_ge (j - cs.length) 1 with h0 | h0
        · rw [show j - cs.length = 0 by omega] at hv; simp at hv; subst hv; decide
        · rw [List.getElem?_eq_none (by simp; omega)] at hv; cases hv
  have gb : ∀ m, m < cs.length + 2 → b.data.toList[p.toNat + m]? = (34 :: (cs ++ [34]))[m]? := by
    intro m hm
    have h := g m (by rw [hn]; exact hm)
    simp only [Nat.add_zero, byteL] at h
    have hv := List.getElem?_eq_getElem (l := 34 :: (cs ++ [34])) (i := m) (by simp; omega)
    by_cases hc : p.toNat + m < b.data.toList.length
    · rw [List.getElem?_eq_getElem hc] at h ⊢
      rw [hv]; simp only [Option.getD_some] at h; rw [h]; rfl
    · exfalso
      rw [List.getElem?_eq_none (by omega)] at h
      exact hnz m _ hv (by simpa using h.symm)
  have hpe : p.toNat + cs.length + 1 < b.size := by
    have h := gb (cs.length + 1) (by omega)
    have h34 : (34 :: (cs ++ [34]))[cs.length + 1]? = some 34 := by
      rw [List.getElem?_cons_succ, List.getElem?_append_right (Nat.le_refl _)]; simp
    rw [h34] at h
    have := (List.getElem?_eq_some_iff.mp h).1
    simp at this; omega
  have hE : (USize.ofNat (p.toNat + cs.length + 1)).toNat = p.toNat + cs.length + 1 := by
    rw [USize.toNat_ofNat']; simp only [USize.size_eq_two_pow, hp.bits]; exact Nat.mod_eq_of_lt (by omega)
  obtain ⟨s, hs1, hs2⟩ := scanString_plain hp p (USize.ofNat (p.toNat + cs.length + 1)) (by omega) (by rw [hE]; omega)
    (by rw [hE]; omega)
    (getElem_of_some (by have := gb 0 (by omega); simpa using this) _)
    (by
      have h := gb (cs.length + 1) (by omega)
      rw [show p.toNat + (cs.length + 1) = (USize.ofNat (p.toNat + cs.length + 1)).toNat by rw [hE]; omega,
        List.getElem?_cons_succ, List.getElem?_append_right (Nat.le_refl _)] at h
      exact getElem_of_some (by rw [h]; simp) _)
    (fun k hk h1 h2 => by
      rw [hE] at h2
      have h := gb (k - p.toNat) (by omega)
      rw [show p.toNat + (k - p.toNat) = k by omega, show k - p.toNat = (k - p.toNat - 1) + 1 by omega,
        List.getElem?_cons_succ, List.getElem?_append_left (by omega)] at h
      rw [List.getElem?_eq_getElem (show k - p.toNat - 1 < cs.length by omega)] at h
      rw [getElem_of_some h hk]
      exact hplain _ (List.getElem_mem _))
  rw [scanString_det hx hs1]
  have hp1 : (p + 1).toNat = p.toNat + 1 := ConLeche.Frontend.usizeStep b p ((hp.lt_iff p).mpr (by omega))
  rw [hp1, hE] at hs2
  apply String.toByteArray_inj.mp
  show s.toUTF8 = str.toUTF8
  rw [hs2]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  apply Array.ext'
  rw [Array.toList_extract, List.extract_eq_take_drop, show p.toNat + cs.length + 1 - (p.toNat + 1) = cs.length by omega,
    hcs]
  apply List.ext_getElem?
  intro m
  rcases Nat.lt_or_ge m cs.length with hm | hm
  · rw [List.getElem?_take_of_lt hm, List.getElem?_drop]
    have h := gb (m + 1) (by omega)
    rw [show p.toNat + (m + 1) = p.toNat + 1 + m by omega, List.getElem?_cons_succ,
      List.getElem?_append_left hm] at h
    simpa using h
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none hm]

/-- The four kind strings, each with its number. -/
def quotKindCands : List (List UInt8 × Nat) :=
  [([34, 116, 121, 112, 101, 34], 1), ([34, 99, 116, 111, 114, 34], 2), ([34, 108, 105, 102, 116, 34], 3),
   ([34, 105, 110, 100, 34], 4)]

def fQKind := ofString "quotKind"

def qkFun : ProgHOL 64 :=
  .dec sJ .one (vv sI) (.dec sL .one (.const 0) (.dec sX .one (.const 0) (.dec sY .one (.const 0)
    (.dec sOk .one (.const 0) (genChoice hang quotKindCands)))))

/-- The kind a string names (con-leche's `processLineCoreD` match). -/
def quotKindOf : String → Option Nat
  | "type" => some 1
  | "ctor" => some 2
  | "lift" => some 3
  | "ind" => some 4
  | _ => none

section
variable {σ : Type}

theorem qkFun_sound (t : PanSemStateFiniteExact 64 σ) (A : BitVec 64) (b : ByteArray) (hp : Plat b)
    (hb : BytesAt t A b.data.toList) (p : USize) (hpb : p.toNat ≤ b.size) (x : String) (e : USize)
    (hx : scanString b p = .ok x e)
    (lb : t.locals.lookup sB = some (.val (.word A)))
    (ln : t.locals.lookup sN = some (.val (.word (BitVec.ofNat 64 b.size))))
    (li : t.locals.lookup sI = some (.val (.word (BitVec.ofNat 64 p.toNat)))) :
    RetP t qkFun (fun w => ∃ k, quotKindOf x = some k ∧ w = BitVec.ofNat 64 (p.toNat + k)) := by
  have hroom := hp.room
  refine choiceEntry t A b.data.toList p.toNat lb (by simpa using ln) li _ _ (fun u hu =>
    genChoice_spec t A b.data.toList p.toNat 0 hb (by omega) hang _ quotKindCands u (by decide) hu
      (fun off h => ?_) (fun _ u' _ => retP_hang u' _))
  simp only [choiceL, quotKindCands] at h
  split at h
  · rename_i hl
    simp only [Option.some.injEq] at h; subst h
    have := litStr_sound hp p "type" [116, 121, 112, 101] (by decide) (by decide) hl hx
    subst this; exact ⟨1, rfl, rfl⟩
  · split at h
    · rename_i _ hl
      simp only [Option.some.injEq] at h; subst h
      have := litStr_sound hp p "ctor" [99, 116, 111, 114] (by decide) (by decide) hl hx
      subst this; exact ⟨2, rfl, rfl⟩
    · split at h
      · rename_i _ _ hl
        simp only [Option.some.injEq] at h; subst h
        have := litStr_sound hp p "lift" [108, 105, 102, 116] (by decide) (by decide) hl hx
        subst this; exact ⟨3, rfl, rfl⟩
      · split at h
        · rename_i _ _ _ hl
          simp only [Option.some.injEq] at h; subst h
          have := litStr_sound hp p "ind" [105, 110, 100] (by decide) (by decide) hl hx
          subst this; exact ⟨4, rfl, rfl⟩
        · simp at h

end

end ConPanqueque.Scan
