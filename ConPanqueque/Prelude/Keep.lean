import ConPanqueque.Prelude.RecEq

/-! # Records survive writes below the frontier

`recEnc_keeps`/`declsRel_keeps`: a record's cells lie at or above the frontier `F`, so an image
that keeps every cell at or above `F` keeps the record; `Agree` is the frame of the passes after
the parses (they write only a scratch span below `F`). -/

open ConRon.Arena ConPanqueque.V

namespace ConPanqueque.Prelude

open ConPanqueque.Front ConPanqueque.T

theorem blkAt_keeps {F : Nat} {H H' : List (BitVec 64)} {o : Nat} {xs : List (BitVec 64)} (h : BlkAt H o xs)
    (ho : F ≤ o) (hk : KeepsAbove F H H') : BlkAt H' o xs :=
  ⟨hk o ho _ h.1, fun i hi => hk _ (by omega) _ (h.2 i hi)⟩

theorem cvEnc_keeps {C : Ctx} {F : Nat} {H H' : List (BitVec 64)} {q : Nat} {cv : IConstantVal}
    (h : CVEnc C F H q cv) (hq : F ≤ q) (hk : KeepsAbove F H H') : CVEnc C F H' q cv := by
  obtain ⟨ol, hol, h1, h2, h3, h4, h5⟩ := h
  exact ⟨ol, hol, hk _ hq _ h1, hk _ (by omega) _ h2, hk _ (by omega) _ h3, blkAt_keeps h4 hol hk, h5⟩

theorem recEnc_keeps {C : Ctx} {F : Nat} {H H' : List (BitVec 64)} {o : Nat} {d : IDeclaration}
    (h : RecEnc C F H o d) (hk : KeepsAbove F H H') : RecEnc C F H' o d := by
  cases d with
  | defnDecl cv v hint =>
    obtain ⟨ho, h1, h2, h3, h4, h5⟩ := h
    exact ⟨ho, hk _ ho _ h1, cvEnc_keeps h2 (by omega) hk, hk _ (by omega) _ h3, hk _ (by omega) _ h4, h5⟩
  | thmDecl cv v =>
    obtain ⟨ho, h1, h2, h3⟩ := h
    exact ⟨ho, hk _ ho _ h1, cvEnc_keeps h2 (by omega) hk, hk _ (by omega) _ h3⟩
  | opaqueDecl cv v =>
    obtain ⟨ho, h1, h2, h3⟩ := h
    exact ⟨ho, hk _ ho _ h1, cvEnc_keeps h2 (by omega) hk, hk _ (by omega) _ h3⟩
  | axiomDecl cv =>
    obtain ⟨ho, h1, h2, ⟨w4, h3⟩, h4⟩ := h
    exact ⟨ho, hk _ ho _ h1, cvEnc_keeps h2 (by omega) hk, ⟨w4, hk _ (by omega) _ h3⟩, h4⟩
  | quotDecl k cv =>
    obtain ⟨ho, h1, h2, h3⟩ := h
    exact ⟨ho, hk _ ho _ h1, cvEnc_keeps h2 (by omega) hk, hk _ (by omega) _ h3⟩
  | indDecl block nP =>
    obtain ⟨hf, ho, h1, h2, ob, hob, h3, h4, h5⟩ := h
    exact ⟨hf, ho, hk _ ho _ h1, hk _ (by omega) _ h2, ob, hob, hk _ (by omega) _ h3,
      fun H'' hk' => h4 H'' (keepsAbove_trans hk hk'), h5⟩

/-- The frame of the passes: same length, same cells outside the scratch span `[a, b)`. -/
def Agree (a b : Nat) (H H' : List (BitVec 64)) : Prop :=
  H'.length = H.length ∧ ∀ c, (c < a ∨ b ≤ c) → H'[c]? = H[c]?

theorem agree_refl (a b : Nat) (H : List (BitVec 64)) : Agree a b H H := ⟨rfl, fun _ _ => rfl⟩

theorem agree_trans {a b : Nat} {H1 H2 H3 : List (BitVec 64)} (h1 : Agree a b H1 H2) (h2 : Agree a b H2 H3) :
    Agree a b H1 H3 := ⟨h2.1.trans h1.1, fun c hc => (h2.2 c hc).trans (h1.2 c hc)⟩

theorem agree_set {a b : Nat} {H H' : List (BitVec 64)} (h : Agree a b H H') (j : Nat) (hj1 : a ≤ j) (hj2 : j < b)
    (w : BitVec 64) : Agree a b H (H'.set j w) :=
  ⟨by simp [h.1], fun c hc => by rw [List.getElem?_set, ite_eq_right (by omega)]; exact h.2 c hc⟩

theorem agree_keeps {a b F : Nat} {H H' : List (BitVec 64)} (h : Agree a b H H') (hF : b ≤ F) : KeepsAbove F H H' :=
  fun c hc v hv => by rw [h.2 c (Or.inr (by omega))]; exact hv

end ConPanqueque.Prelude
