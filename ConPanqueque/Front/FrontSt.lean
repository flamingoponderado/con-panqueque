import ConPanqueque.Front.LevelLine

/-! # The frontend's state between lines

`FrontSt` relates a value-heap image to the twin's parse state: the three tables, the declaration
registry and the input buffer, in a fixed layout (tables, then the registry, then the buffer, then
records from the frontier `F`).  A line changes one table cell, or (a declaration) only cells at or
above the frontier and the registry; either way the rest of `FrontSt` carries over. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (IdTable)

/-- The frontend layout: the three tables apart, below the registry. -/
structure Lay (F rb capD jN jL jE cap bufJ : Nat) (b : ByteArray) : Prop where
  fl : FrontLay F rb capD jN jL jE cap bufJ b
  nl : jN + cap ≤ jL
  le : jL + cap ≤ jE
  capN : cap ≤ natCap
  cap8 : 8 * cap < 2 ^ 64
  capD8 : 8 * (rb + 1 + capD) < 2 ^ 64

/-- The parse state at image `H`. -/
structure FrontSt (C : Ctx) (F rb capD jN jL jE cap bufJ : Nat) (b : ByteArray) (H : List (BitVec 64))
    (st : StateD) : Prop where
  lay : Lay F rb capD jN jL jE cap bufJ b
  tN : TblRel H jN cap st.names
  tL : TblRel H jL cap st.levels
  tE : TblRel H jE cap st.exprs
  dr : DeclsRel C F rb capD H st.decls
  buf : BufOK (ctxH C H) bufJ b

theorem tblRel_set_out {k : IdxKind} {H : List (BitVec 64)} {j cap : Nat} {tbl : IdTable (Idx k)}
    (h : TblRel H j cap tbl) (c : Nat) (hc : c < j ∨ j + cap ≤ c) (w : BitVec 64) : TblRel (H.set c w) j cap tbl :=
  ⟨fun i hi => by rw [List.getElem?_set, if_neg (by omega)]; exact h.1 i hi, h.2⟩

theorem packed_set_below {H : List (BitVec 64)} {j0 : Nat} {bs : List UInt8} (h : Packed H j0 bs) (c : Nat)
    (hc : c < j0) (w : BitVec 64) : Packed (H.set c w) j0 bs := fun i hi => by
  obtain ⟨w', hw, hb⟩ := h i hi
  exact ⟨w', by rw [List.getElem?_set, if_neg (by omega)]; exact hw, hb⟩

theorem bufOK_set {C : Ctx} {H : List (BitVec 64)} {bufJ : Nat} {b : ByteArray} (h : BufOK (ctxH C H) bufJ b)
    (c : Nat) (hc : c < bufJ) (w : BitVec 64) : BufOK (ctxH C (H.set c w)) bufJ b :=
  ⟨packed_set_below h.pk c hc w, h.al, by simpa [ctxH] using h.len, h.plat, h.small⟩

theorem bufOK_agree {C : Ctx} {F rb capD : Nat} {H H' : List (BitVec 64)} {bufJ : Nat} {b : ByteArray}
    (h : BufOK (ctxH C H) bufJ b) (ha : AgreeBelow F rb capD H H') (hl : H.length ≤ H'.length)
    (hlay : rb + 1 + capD ≤ bufJ) (hF : bufJ + b.size / 8 + 1 ≤ F) : BufOK (ctxH C H') bufJ b := by
  refine ⟨packed_agree h.pk ha (fun i hi => ?_), h.al, ?_, h.plat, h.small⟩
  · have : i / 8 ≤ b.size / 8 := Nat.div_le_div_right (by simpa using Nat.le_of_lt hi)
    omega
  · have := h.len; simp only [ctxH] at this ⊢; omega

/-- One table cell changed (the table at `j`, index `i < cap`): the rest of the state carries over. -/
theorem frontSt_setE {C : Ctx} {F rb capD jN jL jE cap bufJ : Nat} {b : ByteArray} {H : List (BitVec 64)}
    {st st' : StateD} (h : FrontSt C F rb capD jN jL jE cap bufJ b H st) (i : Nat) (hi : i < cap) (w : BitVec 64)
    (hE : TblRel (H.set (jE + i) w) jE cap st'.exprs) (h1 : st'.names = st.names) (h2 : st'.levels = st.levels)
    (h3 : st'.decls = st.decls) : FrontSt C F rb capD jN jL jE cap bufJ b (H.set (jE + i) w) st' := by
  have L := h.lay; have FL := L.fl
  refine ⟨L, ?_, ?_, hE, ?_, bufOK_set h.buf _ (by have := FL.tE; have := FL.buf; omega) w⟩
  · rw [h1]; exact tblRel_set_out h.tN _ (by have := L.nl; have := L.le; omega) w
  · rw [h2]; exact tblRel_set_out h.tL _ (by have := L.le; omega) w
  · rw [h3]; exact declsRel_set h.dr _ (by have := FL.tE; have := FL.buf; have := FL.bufF; omega)
      (Or.inl (by have := FL.tE; omega)) w

theorem frontSt_setL {C : Ctx} {F rb capD jN jL jE cap bufJ : Nat} {b : ByteArray} {H : List (BitVec 64)}
    {st st' : StateD} (h : FrontSt C F rb capD jN jL jE cap bufJ b H st) (i : Nat) (hi : i < cap) (w : BitVec 64)
    (hL : TblRel (H.set (jL + i) w) jL cap st'.levels) (h1 : st'.names = st.names) (h2 : st'.exprs = st.exprs)
    (h3 : st'.decls = st.decls) : FrontSt C F rb capD jN jL jE cap bufJ b (H.set (jL + i) w) st' := by
  have L := h.lay; have FL := L.fl
  refine ⟨L, ?_, hL, ?_, ?_, bufOK_set h.buf _ (by have := L.le; have := FL.tE; have := FL.buf; omega) w⟩
  · rw [h1]; exact tblRel_set_out h.tN _ (by have := L.nl; omega) w
  · rw [h2]; exact tblRel_set_out h.tE _ (by have := L.le; omega) w
  · rw [h3]; exact declsRel_set h.dr _ (by have := L.le; have := FL.tE; have := FL.buf; have := FL.bufF; omega)
      (Or.inl (by have := L.le; have := FL.tE; omega)) w

theorem frontSt_setN {C : Ctx} {F rb capD jN jL jE cap bufJ : Nat} {b : ByteArray} {H : List (BitVec 64)}
    {st st' : StateD} (h : FrontSt C F rb capD jN jL jE cap bufJ b H st) (i : Nat) (hi : i < cap) (w : BitVec 64)
    (hN : TblRel (H.set (jN + i) w) jN cap st'.names) (h1 : st'.levels = st.levels) (h2 : st'.exprs = st.exprs)
    (h3 : st'.decls = st.decls) : FrontSt C F rb capD jN jL jE cap bufJ b (H.set (jN + i) w) st' := by
  have L := h.lay; have FL := L.fl
  refine ⟨L, hN, ?_, ?_, ?_, bufOK_set h.buf _ (by have := L.nl; have := L.le; have := FL.tE; have := FL.buf; omega) w⟩
  · rw [h1]; exact tblRel_set_out h.tL _ (by have := L.nl; omega) w
  · rw [h2]; exact tblRel_set_out h.tE _ (by have := L.nl; have := L.le; omega) w
  · rw [h3]
    have := L.nl; have := L.le; have := FL.tE; have := FL.buf; have := FL.bufF
    exact declsRel_set h.dr _ (by omega) (Or.inl (by omega)) w

/-- A declaration: cells below the frontier kept outside the registry, the registry re-established. -/
theorem frontSt_decl {C : Ctx} {F rb capD jN jL jE cap bufJ : Nat} {b : ByteArray} {H H' : List (BitVec 64)}
    {st : StateD} (h : FrontSt C F rb capD jN jL jE cap bufJ b H st) (d : IDeclaration)
    (ha : AgreeBelow F rb capD H H') (hl : H.length ≤ H'.length)
    (hd : DeclsRel C F rb capD H' (st.decls.push d)) :
    FrontSt C F rb capD jN jL jE cap bufJ b H' { st with decls := st.decls.push d } := by
  have L := h.lay; have FL := L.fl
  refine ⟨L, ?_, ?_, ?_, hd, bufOK_agree h.buf ha hl FL.buf FL.bufF⟩
  · exact tblRel_agree h.tN ha (by have := L.nl; have := L.le; have := FL.tE; have := FL.buf; have := FL.bufF; omega)
      (Or.inl (by have := FL.tN; omega))
  · exact tblRel_agree h.tL ha (by have := L.le; have := FL.tE; have := FL.buf; have := FL.bufF; omega)
      (Or.inl (by have := FL.tL; omega))
  · exact tblRel_agree h.tE ha (by have := FL.tE; have := FL.buf; have := FL.bufF; omega)
      (Or.inl (by have := FL.tE; omega))

end ConPanqueque.Front
