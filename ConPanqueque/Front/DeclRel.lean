import ConPanqueque.Front.LstBlk
import ConPanqueque.T.Decl.Step
import ConPanqueque.Bridge.SeqFold

/-! # The parsed declarations in the value heap

The twin's `StateD.decls` is an array of `IDeclaration`.  The frontend keeps it as a registry
`[count, r₀, r₁, …]` of record addresses (capacity `capD`) from cell `rb`, each record in the layout
the fold reads (`RecOK`'s cells: kind, name, level-parameter block, type, value, hint).  `RecEnc` is
that layout's encoding part; the denotation facts `RecOK` adds come from the twin's own theorems.

Records and their blocks lie at or above a frontier `F`, which the frontend's writes (table cells,
registry cells) never reach, so a record once written stays. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan

variable {σ : Type}

/-- A constant's common data at `q`: name, level-parameter block, type. -/
def CVEnc (C : Ctx) (F : Nat) (H : List (BitVec 64)) (q : Nat) (cv : IConstantVal) : Prop :=
  ∃ ol, F ≤ ol ∧ H[q]? = some (Enc.idxW cv.name) ∧ H[q + 1]? = some (cellA C ol) ∧
    H[q + 2]? = some (Enc.idxW cv.type) ∧ BlkAt H ol (cv.levelParams.map Enc.idxW) ∧
    cv.levelParams.length < 2 ^ 59

/-- `H'` keeps every cell of `H` at or above `F`. -/
def KeepsAbove (F : Nat) (H H' : List (BitVec 64)) : Prop :=
  ∀ c, F ≤ c → ∀ v, H[c]? = some v → H'[c]? = some v

/-- A declaration record's cells at `o`.  An inductive block's records lie at or above `F`: its
`IndBlk` holds in every image keeping the cells at or above `F`. -/
def RecEnc (C : Ctx) (F : Nat) (H : List (BitVec 64)) (o : Nat) : IDeclaration → Prop
  | .defnDecl cv v hint => F ≤ o ∧ H[o]? = some 1 ∧ CVEnc C F H (o + 1) cv ∧ H[o + 4]? = some (Enc.idxW v) ∧
      H[o + 5]? = some (BitVec.ofNat 64 (T.hintN hint)) ∧ T.hintN hint < 2 ^ 63
  | .thmDecl cv v => F ≤ o ∧ H[o]? = some 2 ∧ CVEnc C F H (o + 1) cv ∧ H[o + 4]? = some (Enc.idxW v)
  | .opaqueDecl cv v => F ≤ o ∧ H[o]? = some 3 ∧ CVEnc C F H (o + 1) cv ∧ H[o + 4]? = some (Enc.idxW v)
  | .axiomDecl cv => F ≤ o ∧ H[o]? = some 5 ∧ CVEnc C F H (o + 1) cv ∧ (∃ w, H[o + 4]? = some w) ∧
      ConPanqueque.Bridge.AxPinName C.pins cv.name
  | .quotDecl k cv => F ≤ o ∧ H[o]? = some 6 ∧ CVEnc C F H (o + 1) cv ∧
      H[o + 4]? = some (BitVec.ofNat 64 (match k with | .type => 1 | .ctor => 2 | .lift => 3 | .ind => 4 | .sound => 5))
  | .indDecl block nP => ConPanqueque.Bridge.IsFrontDecl C.pins (.indDecl block nP) ∧ F ≤ o ∧ H[o]? = some 4 ∧ H[o + 1]? = some (BitVec.ofNat 64 nP) ∧
      ∃ ob, F ≤ ob ∧ H[o + 2]? = some (cellA C ob) ∧
      (∀ H', KeepsAbove F H H' → T.Ind.IndBlk C H' ob block) ∧ block.length < 2 ^ 59 ∧ nP < 2 ^ 59 ∧
      ∀ i (hi : i < block.length), block[i].toConstantVal.levelParams.length < 2 ^ 59

/-- The registry of declarations. -/
def DeclsRel (C : Ctx) (F rb capD : Nat) (H : List (BitVec 64)) (decls : Array IDeclaration) : Prop :=
  H[rb]? = some (BitVec.ofNat 64 decls.size) ∧ decls.size ≤ capD ∧ rb + 1 + capD ≤ F ∧ F ≤ H.length ∧
    ∀ k (hk : k < decls.size), ∃ o, H[rb + 1 + k]? = some (cellA C o) ∧ RecEnc C F H o decls[k]

/-- A cell below the frontier is not a record's. -/
theorem getElem?_set_ge {H : List (BitVec 64)} {j c : Nat} (w : BitVec 64) (h : j < c) :
    (H.set j w)[c]? = H[c]? := by
  rw [List.getElem?_set, ite_eq_right (by omega)]

theorem getElem?_prefix {H H' : List (BitVec 64)} (hp : H <+: H') {c : Nat} {v : BitVec 64}
    (h : H[c]? = some v) : H'[c]? = some v := by
  have hl : c < H.length := by
    by_cases hl : c < H.length
    · exact hl
    · rw [List.getElem?_eq_none (by omega)] at h; cases h
  obtain ⟨r, rfl⟩ := hp; rw [List.getElem?_append_left hl]; exact h

theorem blkAt_set_below {H : List (BitVec 64)} {o : Nat} {xs : List (BitVec 64)} (h : BlkAt H o xs) (j : Nat)
    (hj : j < o) (w : BitVec 64) : BlkAt (H.set j w) o xs :=
  ⟨by rw [getElem?_set_ge w hj]; exact h.1, fun i hi => by rw [getElem?_set_ge w (by omega)]; exact h.2 i hi⟩

theorem cvEnc_set {C : Ctx} {F : Nat} {H : List (BitVec 64)} {q : Nat} {cv : IConstantVal} (h : CVEnc C F H q cv)
    (j : Nat) (hj : j < F) (hq : F ≤ q) (w : BitVec 64) : CVEnc C F (H.set j w) q cv := by
  obtain ⟨ol, hol, h1, h2, h3, h4, h5⟩ := h
  exact ⟨ol, hol, by rw [getElem?_set_ge w (by omega)]; exact h1, by rw [getElem?_set_ge w (by omega)]; exact h2,
    by rw [getElem?_set_ge w (by omega)]; exact h3, blkAt_set_below h4 j (by omega) w, h5⟩

theorem cvEnc_prefix {C : Ctx} {F : Nat} {H H' : List (BitVec 64)} {q : Nat} {cv : IConstantVal}
    (h : CVEnc C F H q cv) (hp : H <+: H') : CVEnc C F H' q cv := by
  obtain ⟨ol, hol, h1, h2, h3, h4, h5⟩ := h
  exact ⟨ol, hol, getElem?_prefix hp h1, getElem?_prefix hp h2, getElem?_prefix hp h3, blkAt_mono h4 hp, h5⟩

theorem recEnc_set {C : Ctx} {F : Nat} {H : List (BitVec 64)} {o : Nat} {d : IDeclaration} (h : RecEnc C F H o d)
    (j : Nat) (hj : j < F) (w : BitVec 64) : RecEnc C F (H.set j w) o d := by
  cases d with
  | defnDecl cv v hint =>
    obtain ⟨ho, h1, h2, h3, h4, h5⟩ := h
    exact ⟨ho, by rw [getElem?_set_ge w (by omega)]; exact h1, cvEnc_set h2 j hj (by omega) w,
      by rw [getElem?_set_ge w (by omega)]; exact h3, by rw [getElem?_set_ge w (by omega)]; exact h4, h5⟩
  | thmDecl cv v =>
    obtain ⟨ho, h1, h2, h3⟩ := h
    exact ⟨ho, by rw [getElem?_set_ge w (by omega)]; exact h1, cvEnc_set h2 j hj (by omega) w,
      by rw [getElem?_set_ge w (by omega)]; exact h3⟩
  | opaqueDecl cv v =>
    obtain ⟨ho, h1, h2, h3⟩ := h
    exact ⟨ho, by rw [getElem?_set_ge w (by omega)]; exact h1, cvEnc_set h2 j hj (by omega) w,
      by rw [getElem?_set_ge w (by omega)]; exact h3⟩
  | axiomDecl cv =>
    obtain ⟨ho, h1, h2, ⟨w4, h3⟩, h4⟩ := h
    exact ⟨ho, by rw [getElem?_set_ge w (by omega)]; exact h1, cvEnc_set h2 j hj (by omega) w,
      ⟨w4, by rw [getElem?_set_ge w (by omega)]; exact h3⟩, h4⟩
  | quotDecl k cv =>
    obtain ⟨ho, h1, h2, h3⟩ := h
    exact ⟨ho, by rw [getElem?_set_ge w (by omega)]; exact h1, cvEnc_set h2 j hj (by omega) w,
      by rw [getElem?_set_ge w (by omega)]; exact h3⟩
  | indDecl block nP =>
    obtain ⟨hf, ho, h1, h2, ob, hob, h3, h4, h5⟩ := h
    exact ⟨hf, ho, by rw [getElem?_set_ge w (by omega)]; exact h1, by rw [getElem?_set_ge w (by omega)]; exact h2,
      ob, hob, by rw [getElem?_set_ge w (by omega)]; exact h3,
      fun H' hk => h4 H' (fun c hc v hv => hk c hc v (by rw [getElem?_set_ge w (by omega)]; exact hv)), h5⟩

theorem keepsAbove_prefix {F : Nat} {H H' : List (BitVec 64)} (hp : H <+: H') : KeepsAbove F H H' :=
  fun _ _ _ hv => getElem?_prefix hp hv

theorem keepsAbove_trans {F : Nat} {H1 H2 H3 : List (BitVec 64)} (a : KeepsAbove F H1 H2) (b : KeepsAbove F H2 H3) :
    KeepsAbove F H1 H3 := fun c hc v hv => b c hc v (a c hc v hv)

theorem recEnc_prefix {C : Ctx} {F : Nat} {H H' : List (BitVec 64)} {o : Nat} {d : IDeclaration}
    (h : RecEnc C F H o d) (hp : H <+: H') : RecEnc C F H' o d := by
  cases d with
  | defnDecl cv v hint =>
    obtain ⟨ho, h1, h2, h3, h4, h5⟩ := h
    exact ⟨ho, getElem?_prefix hp h1, cvEnc_prefix h2 hp, getElem?_prefix hp h3, getElem?_prefix hp h4, h5⟩
  | thmDecl cv v =>
    obtain ⟨ho, h1, h2, h3⟩ := h
    exact ⟨ho, getElem?_prefix hp h1, cvEnc_prefix h2 hp, getElem?_prefix hp h3⟩
  | opaqueDecl cv v =>
    obtain ⟨ho, h1, h2, h3⟩ := h
    exact ⟨ho, getElem?_prefix hp h1, cvEnc_prefix h2 hp, getElem?_prefix hp h3⟩
  | axiomDecl cv =>
    obtain ⟨ho, h1, h2, ⟨w4, h3⟩, h4⟩ := h
    exact ⟨ho, getElem?_prefix hp h1, cvEnc_prefix h2 hp, ⟨w4, getElem?_prefix hp h3⟩, h4⟩
  | quotDecl k cv =>
    obtain ⟨ho, h1, h2, h3⟩ := h
    exact ⟨ho, getElem?_prefix hp h1, cvEnc_prefix h2 hp, getElem?_prefix hp h3⟩
  | indDecl block nP =>
    obtain ⟨hf, ho, h1, h2, ob, hob, h3, h4, h5⟩ := h
    exact ⟨hf, ho, getElem?_prefix hp h1, getElem?_prefix hp h2, ob, hob, getElem?_prefix hp h3,
      fun H' hk => h4 H' (keepsAbove_trans (keepsAbove_prefix hp) hk), h5⟩

/-- A write below the frontier and outside the registry keeps the registry. -/
theorem declsRel_set {C : Ctx} {F rb capD : Nat} {H : List (BitVec 64)} {decls : Array IDeclaration}
    (h : DeclsRel C F rb capD H decls) (j : Nat) (hj : j < F) (hr : j < rb ∨ rb + 1 + capD ≤ j) (w : BitVec 64) :
    DeclsRel C F rb capD (H.set j w) decls := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨by rw [List.getElem?_set, ite_eq_right (by omega)]; exact h1, h2, h3, by simp; exact h4, fun k hk => ?_⟩
  obtain ⟨o, ho, hrec⟩ := h5 k hk
  exact ⟨o, by rw [List.getElem?_set, ite_eq_right (by omega)]; exact ho, recEnc_set hrec j hj w⟩

theorem declsRel_prefix {C : Ctx} {F rb capD : Nat} {H H' : List (BitVec 64)} {decls : Array IDeclaration}
    (h : DeclsRel C F rb capD H decls) (hp : H <+: H') : DeclsRel C F rb capD H' decls := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨getElem?_prefix hp h1, h2, h3, Nat.le_trans h4 hp.length_le, fun k hk => ?_⟩
  obtain ⟨o, ho, hrec⟩ := h5 k hk
  exact ⟨o, getElem?_prefix hp ho, recEnc_prefix hrec hp⟩

end ConPanqueque.Front
