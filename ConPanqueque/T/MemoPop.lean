import ConPanqueque.T.MemoRep
import ConPanqueque.V.Pop

/-!
# A memo without its newest key

When the newest row of a memo's table is the key `k` (its count `c`, its row's key words `enc k`, its slot `j`),
lowering the count and clearing that slot leaves the memo of `m.erase k`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

namespace ConPanqueque.T

variable {σ : Type}

theorem words_eq {t : PanSemStateFiniteExact 64 σ} {P : BitVec 64} {xs ys : List (BitVec 64)}
    (hx : Words t P xs) (hy : Words t P ys) (hl : xs.length = ys.length) : xs = ys := by
  apply List.ext_getElem hl
  intro k h1 h2
  have a := (hx k h1).2; have b := (hy k h2).2
  rw [a] at b; exact HolWordLab.word.inj b

theorem findIdx_append_last {K : Type} [DecidableEq K] (rows : List K) (k a : K) (ha : a ≠ k) :
    (rows ++ [k]).findIdx? (· = a) = rows.findIdx? (· = a) := by
  rw [List.findIdx?_append]
  cases h : rows.findIdx? (· = a) with
  | some i => rfl
  | none => simp [List.findIdx?_cons, Ne.symm ha]

theorem findIdx_lt {K : Type} [DecidableEq K] (rows : List K) (a : K) (i : Nat) (h : rows.findIdx? (· = a) = some i) :
    i < rows.length := by
  have := List.findIdx?_eq_some_iff_getElem.mp h
  obtain ⟨hi, _⟩ := this
  exact hi

set_option maxHeartbeats 4000000 in
/-- **The memo of `m.erase k`** after the newest row (`k`) is undone. -/
theorem memoAtG_pop {K V : Type} [BEq K] [LawfulBEq K] [Hashable K] [DecidableEq K] [Inhabited V]
    {enc : K → List (BitVec 64)} {valW : V → BitVec 64} (hinj : ∀ x y, enc x = enc y → x = y)
    {t t' : PanSemStateFiniteExact 64 σ} {G : BitVec 64} {g : VGeo} {m : Std.HashMap K V}
    (h : MemoAtG enc valW t G g m) (k : K) (c j : Nat) (P : BitVec 64) (hc0 : 0 < c) (hc64 : c < 2 ^ 64)
    (hcC : t.memory g.C = .word (BitVec.ofNat 64 c))
    (hP : t.memory (g.R + BitVec.ofNat 64 (16 * (c - 1))) = .word P)
    (hlen : t.memory (g.R + BitVec.ofNat 64 (16 * (c - 1)) + 8) = .word (BitVec.ofNat 64 (enc k).length))
    (hkl : (enc k).length < 2 ^ 61) (hW : Words t P (enc k)) (hj : j < g.n)
    (hS : t.memory (g.S + BitVec.ofNat 64 (8 * j)) = .word (BitVec.ofNat 64 c))
    (hd : t'.memaddrs = t.memaddrs) (hC' : t'.memory g.C = .word (BitVec.ofNat 64 (c - 1)))
    (hS' : t'.memory (g.S + BitVec.ofNat 64 (8 * j)) = .word 0)
    (hrest : ∀ x, x ≠ g.C → x ≠ g.S + BitVec.ofNat 64 (8 * j) → t'.memory x = t.memory x)
    (hGout : ∀ i, i < 8 → G + BitVec.ofNat 64 (8 * i) ≠ g.C ∧ G + BitVec.ofNat 64 (8 * i) ≠ g.S + BitVec.ofNat 64 (8 * j)) :
    MemoAtG enc valW t' G g (m.erase k) := by
  obtain ⟨hdesc, hn, hb, hcap, tb, rows, ders, slots, hu, hT, hinv, hr, hder, hrel⟩ := h
  -- the count is `rows.length`
  have hrl : rows.length = c := by
    have e := hT.cnt.2; rw [hcC] at e
    have e2 := HolWordLab.word.inj e
    have := congrArg BitVec.toNat e2
    have hle := hT.le
    simp at this; rw [Nat.mod_eq_of_lt hc64, Nat.mod_eq_of_lt (by omega)] at this; omega
  -- rows = rows0 ++ [x]
  obtain ⟨rows0, x, hrx⟩ : ∃ rows0 x, rows = rows0 ++ [x] := by
    rcases List.eq_nil_or_concat rows with e | ⟨r0, x, e⟩
    · rw [e] at hrl; simp at hrl; omega
    · exact ⟨r0, x, by rw [e, List.concat_eq_append]⟩
  subst hrx
  have hl0 : rows0.length = c - 1 := by simp at hrl; omega
  -- the newest row's key is `k`
  have hxk : x = k := by
    have hi : rows0.length < (rows0 ++ [x]).length := by simp
    obtain ⟨P', a1, a2, a3, a4, a5, -, -⟩ := hT.row rows0.length hi
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_singleton] at a4 a5
    rw [hl0, hP] at a3
    have hPP := HolWordLab.word.inj a3
    subst hPP
    rw [hl0, hlen] at a4
    have hsx := hT.short rows0.length hi
    simp only [List.getElem_append_right (Nat.le_refl _), Nat.sub_self, List.getElem_singleton] at hsx
    have e4 := congrArg BitVec.toNat (HolWordLab.word.inj a4)
    simp at e4; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at e4
    exact hinj _ _ (words_eq a5 hW e4.symm)
  subst hxk
  -- the slot names the newest row
  have hsj : slots[j]? = some (rows0.length + 1) := by
    obtain ⟨v, hv, hvlt, -, hmv⟩ := hT.slot j hj
    rw [hS] at hmv
    have := congrArg BitVec.toNat (HolWordLab.word.inj hmv)
    simp at this; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    rw [hv]; congr 1; omega
  have hknot : x ∉ rows0 := by
    have := (List.nodup_append.mp hinv.rows_nodup).2.2
    exact fun hm => this x hm x (List.mem_singleton_self _) rfl
  have hdl : ders.length = rows0.length + 1 := by rw [hT.dlen]; simp
  have hderl : tb.der.size = rows0.length + 1 := by
    have := congrArg List.length hder; simp at this; omega
  -- the old table
  let tb0 : Tbl K Nat V := ⟨rows0.toArray, tb.der.pop, tb.cons.erase x⟩
  refine ⟨fun i hi => ?_, hn, hb, hcap, tb0, rows0, ders.dropLast, slots.set j 0, hu, ?_,
    pop_inv _ rows0 x slots g.n hinv j hsj, ?_, ?_, ?_⟩
  · rw [hrest _ (hGout i hi).1 (hGout i hi).2, hd]; exact hdesc i hi
  · exact vt_pop hT j hj hd (by rw [hC', hl0]) hS' hrest
  · refine ⟨by simp [tb0], fun a => ?_⟩
    show (tb.cons.erase x)[a]? = _
    rw [Std.HashMap.getElem?_erase]
    by_cases e : x = a
    · subst e; simp
      exact (List.findIdx?_eq_none_iff.mpr (fun y hy => by simp; exact fun e => hknot (e ▸ hy))).symm
    · simp [e]
      have := hr.cons a
      rw [findIdx_append_last rows0 x a (Ne.symm e)] at this
      simpa using this
  · show (tb.der.pop).toList.map (dWG valW) = ders.dropLast
    rw [Array.toList_pop, List.map_dropLast, hder]
  · intro a
    rw [Std.HashMap.getElem?_erase]
    show _ = ((tb.cons.erase x)[a]?).map tb0.derAt
    rw [Std.HashMap.getElem?_erase]
    by_cases e : x = a
    · simp [e]
    · simp only [e, beq_iff_eq, ↓reduceIte]
      rw [hrel a]
      rcases hf : tb.find? a with _ | i
      · simp only [Tbl.find?] at hf
        rw [hf]; rfl
      · simp only [Tbl.find?] at hf ⊢
        rw [hf]
        have hi : i < rows0.length := by
          have := hr.cons a; rw [hf, findIdx_append_last rows0 x a (Ne.symm e)] at this
          cases h2 : rows0.findIdx? (· = a) with
          | none => rw [h2] at this; cases this
          | some i' => rw [h2] at this; simp at this; subst this; exact findIdx_lt _ _ _ h2
        simp only [Option.map_some, Tbl.derAt, tb0]
        congr 1
        rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_pop]
        simp [hi, hderl]

end ConPanqueque.T
