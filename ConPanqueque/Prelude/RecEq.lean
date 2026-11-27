import ConPanqueque.Start.Rest2
import ConPanqueque.Prelude.Defs

/-! # Two value records with the same cells are the same record

`recEnc_eq`: two value records (not blocks) encoded at `o` and `o'` whose kind, name, type,
level-parameter block and kind-specific fields hold the same words are equal as `IDeclaration`s
(handles are compared as words; `Enc.idxW` is injective).  The override pass compares a stream
record with the prelude's this way. -/

open ConRon.Arena ConPanqueque.V

namespace ConPanqueque.Prelude

open ConPanqueque.Front ConPanqueque.T

theorem some_inj' {α : Type} {a b : α} {x : Option α} (h1 : x = some a) (h2 : x = some b) : a = b := by
  rw [h1] at h2; exact Option.some.inj h2

theorem map_idxW_inj {k : IdxKind} : ∀ {xs ys : List (Idx k)}, xs.map Enc.idxW = ys.map Enc.idxW → xs = ys
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [Enc.idxW_inj h.1, map_idxW_inj h.2]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- Two blocks with the same length cell and the same entries hold the same list. -/
theorem blkAt_eq {H : List (BitVec 64)} {ol ol' : Nat} {xs ys : List (BitVec 64)} (hx : BlkAt H ol xs)
    (hy : BlkAt H ol' ys) (hn : H[ol]? = H[ol']?)
    (he : ∀ i, i < xs.length → H[ol + 1 + i]? = H[ol' + 1 + i]?) (h59 : xs.length < 2 ^ 59) (h59' : ys.length < 2 ^ 59) :
    xs = ys := by
  have hl : xs.length = ys.length := by
    have e := some_inj' hx.1 (hn.trans hy.1)
    have := congrArg BitVec.toNat e
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  apply List.ext_getElem hl
  intro i h1 h2
  exact some_inj' (hx.2 i h1) ((he i h1).trans (hy.2 i h2))

theorem hintN_inj {a b : ConLeche.ReducibilityHint} (h : hintN a = hintN b) : a = b := by
  cases a <;> cases b <;> simp_all [hintN] <;> omega

theorem ofNat_inj63 {a b : Nat} (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) (h : BitVec.ofNat 64 a = BitVec.ofNat 64 b) :
    a = b := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

/-- A value record's constant data. -/
def cvOf : IDeclaration → IConstantVal
  | .defnDecl cv .. | .thmDecl cv .. | .opaqueDecl cv .. | .axiomDecl cv | .quotDecl _ cv => cv
  | .indDecl .. => default

theorem valName_cvOf (d : IDeclaration) (h : isVal d = true) : valName d = (cvOf d).name := by
  cases d <;> simp_all [isVal, valName, cvOf]

/-- Two constants' cells with the same words (the level-parameter blocks at `ol`, `ol'`). -/
theorem cv_eq_at {C : Ctx} {H : List (BitVec 64)} {q q' ol ol' : Nat} {cv cv' : IConstantVal}
    (h1 : H[q]? = some (Enc.idxW cv.name)) (h3 : H[q + 2]? = some (Enc.idxW cv.type))
    (h4 : BlkAt H ol (cv.levelParams.map Enc.idxW)) (h5 : cv.levelParams.length < 2 ^ 59)
    (h1' : H[q']? = some (Enc.idxW cv'.name)) (h3' : H[q' + 2]? = some (Enc.idxW cv'.type))
    (h4' : BlkAt H ol' (cv'.levelParams.map Enc.idxW)) (h5' : cv'.levelParams.length < 2 ^ 59)
    (hn : H[q]? = H[q']?) (ht : H[q + 2]? = H[q' + 2]?) (hb : H[ol]? = H[ol']?)
    (he : ∀ i, i < cv.levelParams.length → H[ol + 1 + i]? = H[ol' + 1 + i]?) : cv = cv' := by
  have en := Enc.idxW_inj (some_inj' h1 (hn.trans h1'))
  have et := Enc.idxW_inj (some_inj' h3 (ht.trans h3'))
  have el := map_idxW_inj (blkAt_eq h4 h4' hb (fun i hi => he i (by simpa using hi)) (by simpa using h5)
    (by simpa using h5'))
  cases cv; cases cv'; simp_all

/-- A value record's kind word. -/
def tagOf : IDeclaration → Nat
  | .defnDecl .. => 1 | .thmDecl .. => 2 | .opaqueDecl .. => 3 | .indDecl .. => 4 | .axiomDecl .. => 5
  | .quotDecl .. => 6

theorem recEnc_tag {C : Ctx} {F : Nat} {H : List (BitVec 64)} {o : Nat} {d : IDeclaration} (h : RecEnc C F H o d) :
    H[o]? = some (BitVec.ofNat 64 (tagOf d)) := by
  cases d with
  | defnDecl => exact h.2.1
  | thmDecl => exact h.2.1
  | opaqueDecl => exact h.2.1
  | axiomDecl => exact h.2.1
  | quotDecl => exact h.2.1
  | indDecl => exact h.2.2.1

theorem recEnc_cv {C : Ctx} {F : Nat} {H : List (BitVec 64)} {o : Nat} {d : IDeclaration} (h : RecEnc C F H o d)
    (hv : isVal d = true) : CVEnc C F H (o + 1) (cvOf d) := by
  cases d with
  | defnDecl => exact h.2.2.1
  | thmDecl => exact h.2.2.1
  | opaqueDecl => exact h.2.2.1
  | axiomDecl => exact h.2.2.1
  | quotDecl => exact h.2.2.1
  | indDecl => simp [isVal] at hv

theorem tagOf_inj {a b : Nat} (ha : a < 7) (hb : b < 7) (h : BitVec.ofNat 64 a = BitVec.ofNat 64 b) : a = b :=
  ofNat_inj63 (by omega) (by omega) h

theorem tagOf_lt (d : IDeclaration) : tagOf d < 7 := by cases d <;> simp [tagOf]

theorem quotW_inj {k k' : ConLeche.QuotKind}
    (h : BitVec.ofNat 64 (match k with | .type => 1 | .ctor => 2 | .lift => 3 | .ind => 4 | .sound => 5) =
      BitVec.ofNat 64 (match k' with | .type => 1 | .ctor => 2 | .lift => 3 | .ind => 4 | .sound => 5)) : k = k' := by
  cases k <;> cases k' <;> first | rfl | (exfalso; revert h; decide)

/-- **Same kind, same constant data, same kind-specific words: the same record.** -/
theorem recEnc_eq {C : Ctx} {F : Nat} {H : List (BitVec 64)} {o o' : Nat} {d d' : IDeclaration}
    (h : RecEnc C F H o d) (h' : RecEnc C F H o' d') (hv : isVal d = true) (hv' : isVal d' = true)
    (hcv : cvOf d = cvOf d') (htag : H[o]? = H[o']?)
    (h4 : H[o]? ≠ some 5 → H[o + 4]? = H[o' + 4]?) (h5 : H[o]? = some 1 → H[o + 5]? = H[o' + 5]?) : d = d' := by
  have t := recEnc_tag h
  have t' := recEnc_tag h'
  have et : tagOf d = tagOf d' := tagOf_inj (tagOf_lt d) (tagOf_lt d') (some_inj' t (htag.trans t'))
  cases d <;> cases d' <;> simp only [tagOf, isVal, cvOf] at et hv hv' hcv <;> (try omega) <;> (try simp at hv) <;>
    (try simp at hv') <;> subst hcv
  · rfl
  · -- definitions
    rename_i v hint v' hint'
    have e4 := some_inj' h.2.2.2.1 ((h4 (by rw [t]; simp [tagOf])).trans h'.2.2.2.1)
    have e5 := some_inj' h.2.2.2.2.1 ((h5 (by rw [t]; simp [tagOf])).trans h'.2.2.2.2.1)
    rw [Enc.idxW_inj e4, hintN_inj (ofNat_inj63 h.2.2.2.2.2 h'.2.2.2.2.2 e5)]
  · rename_i v v'
    rw [Enc.idxW_inj (some_inj' h.2.2.2 ((h4 (by rw [t]; simp [tagOf])).trans h'.2.2.2))]
  · rename_i v v'
    rw [Enc.idxW_inj (some_inj' h.2.2.2 ((h4 (by rw [t]; simp [tagOf])).trans h'.2.2.2))]
  · have e4 := some_inj' h.2.2.2 ((h4 (by rw [t]; simp [tagOf])).trans h'.2.2.2)
    congr 1
    exact quotW_inj e4

end ConPanqueque.Prelude
