import ConPanqueque.T.MemoModel
import ConPanqueque.V.Two
import ConPanqueque.V.Enc
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

/-!
# Memo tables: keys and representation

A memo `Std.HashMap (EIdx × Nat) EIdx` is a one-tier generic table at its own descriptor (base word
`1`), keyed by `idxW h :: limbs d`, answers in the derived column (`(idxW v, 0)`).
-/

namespace ConPanqueque.T

variable {σ : Type}

/-- A memo's key: the handle, then the number's limbs (injective at every `Nat`). -/
def encMemo (k : EIdx × Nat) : List (BitVec 64) := Enc.idxW k.1 :: Enc.limbs k.2

theorem encMemo_inj : ∀ x y, encMemo x = encMemo y → x = y := by
  intro ⟨h, d⟩ ⟨h', d'⟩ e
  simp only [encMemo, List.cons.injEq] at e
  rw [Enc.idxW_inj e.1, Enc.limbs_inj e.2]

/-! ## The representation of a memo -/

/-- A memo value's derived pair: its word, then zero. -/
def dWG {V : Type} (valW : V → BitVec 64) (v : V) : BitVec 64 × BitVec 64 := (valW v, 0)

abbrev dWE : EIdx → BitVec 64 × BitVec 64 := dWG Enc.idxW

/-- A twin memo `m : Std.HashMap K V` is held at descriptor `G` with geometry `g`, keys encoded by `enc`,
values as the words `valW`. -/
def MemoAtG {K V : Type} [BEq K] [LawfulBEq K] [Hashable K] [DecidableEq K] [Inhabited V] (enc : K → List (BitVec 64)) (valW : V → BitVec 64)
    (t : PanSemStateFiniteExact 64 σ) (G : BitVec 64) (g : VGeo) (m : Std.HashMap K V) : Prop :=
  DescV t G g 1 ∧ g.n = 2 ^ g.b ∧ g.b ≤ 56 ∧ g.cap < 2 ^ 30 ∧
  ∃ (tb : Tbl K Nat V) (rows : List K) (ders : List (BitVec 64 × BitVec 64)) (slots : List Nat) (hu : Nat),
    VT t enc rows ders slots g hu ∧ ConsModel.Inv (homeV enc g.b) rows slots g.n ∧ TblRel tb rows id ∧
      tb.der.toList.map (dWG valW) = ders ∧ MemoRel m tb

/-- The `(EIdx × Nat) → EIdx` memos. -/
abbrev MemoAt (t : PanSemStateFiniteExact 64 σ) (G : BitVec 64) (g : VGeo) (m : Std.HashMap (EIdx × Nat) EIdx) :
    Prop := MemoAtG encMemo Enc.idxW t G g m

theorem memoAtG_frame {K V : Type} [BEq K] [LawfulBEq K] [Hashable K] [DecidableEq K] [Inhabited V] {enc : K → List (BitVec 64)}
    {valW : V → BitVec 64} {t u : PanSemStateFiniteExact 64 σ} {G : BitVec 64} {g : VGeo} {m : Std.HashMap K V}
    (h : MemoAtG enc valW t G g m) (hm : ∀ c, inR g c → u.memory c = t.memory c)
    (hdsc : ∀ k, k < 8 → u.memory (G + BitVec.ofNat 64 (8 * k)) = t.memory (G + BitVec.ofNat 64 (8 * k)))
    (hd : u.memaddrs = t.memaddrs) : MemoAtG enc valW u G g m := by
  obtain ⟨hdesc, h1, h2, h3, tb, rows, ders, slots, hu, hT, hi, hr, hder, hrel⟩ := h
  exact ⟨fun k hk => by rw [hdsc k hk, hd]; exact hdesc k hk, h1, h2, h3, tb, rows, ders, slots, hu,
    vt_frame hT hm hd, hi, hr, hder, hrel⟩

theorem memoAtG_of_eq {K V : Type} [BEq K] [LawfulBEq K] [Hashable K] [DecidableEq K] [Inhabited V] {enc : K → List (BitVec 64)}
    {valW : V → BitVec 64} {t u : PanSemStateFiniteExact 64 σ} {G : BitVec 64} {g : VGeo} {m : Std.HashMap K V}
    (h : MemoAtG enc valW t G g m) (hm : u.memory = t.memory) (hd : u.memaddrs = t.memaddrs) :
    MemoAtG enc valW u G g m :=
  memoAtG_frame h (fun _ _ => by rw [hm]) (fun _ _ => by rw [hm]) hd

theorem memoAt_frame {t u : PanSemStateFiniteExact 64 σ} {G : BitVec 64} {g : VGeo} {m : Std.HashMap (EIdx × Nat) EIdx}
    (h : MemoAt t G g m) (hm : ∀ c, inR g c → u.memory c = t.memory c)
    (hdsc : ∀ k, k < 8 → u.memory (G + BitVec.ofNat 64 (8 * k)) = t.memory (G + BitVec.ofNat 64 (8 * k)))
    (hd : u.memaddrs = t.memaddrs) : MemoAt u G g m := memoAtG_frame h hm hdsc hd

theorem memoAt_of_eq {t u : PanSemStateFiniteExact 64 σ} {G : BitVec 64} {g : VGeo} {m : Std.HashMap (EIdx × Nat) EIdx}
    (h : MemoAt t G g m) (hm : u.memory = t.memory) (hd : u.memaddrs = t.memaddrs) : MemoAt u G g m :=
  memoAtG_of_eq h hm hd

theorem limbs_small (d : Nat) (hd : d < 2 ^ 64) : Enc.limbs d = if d = 0 then [] else [BitVec.ofNat 64 d] := by
  unfold Enc.limbs
  by_cases h : d = 0
  · simp [h]
  · simp only [h, ↓reduceDIte, ite_false]
    rw [Nat.div_eq_of_lt hd]
    simp [Enc.limbs, Nat.mod_eq_of_lt hd]

end ConPanqueque.T
