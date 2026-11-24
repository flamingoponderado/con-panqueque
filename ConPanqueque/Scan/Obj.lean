import ConPanqueque.Scan.Model

/-! # The record scanners as one object loop

Every `scan*Loop` of con-leche's scanner is the same loop over a JSON object: whitespace, `}`
(all required keys seen?), `,`, or a key whose value is scanned into a slot.  `objLoopN` is that
loop for nat-valued slots, parameterised by a slot table (`ObjSpec`); each con-leche loop is an
instance (`scanAppExprLoop_eq`, …). -/

namespace ConPanqueque.Scan

open ConLeche.Frontend

/-- A slot table: for each key, its bit in the seen-mask and its slot; and the mask of the keys
that must be present. -/
structure ObjSpec where
  keys : List (Key × UInt32 × Nat)
  need : UInt32

def lookupKey (k : Key) : List (Key × UInt32 × Nat) → Option (UInt32 × Nat)
  | [] => none
  | (k', bit, sl) :: r => if k = k' then some (bit, sl) else lookupKey k r

/-- The object loop, nat slots: con-leche's loops with the key dispatch read off the table. -/
def objLoopN (sp : ObjSpec) (b : ByteArray) (i : USize) (wantMember : Bool) (seen : UInt32)
    (slots : List Nat) : ScanRes (List Nat) :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isWs c then objLoopN sp b (i + 1) wantMember seen slots
    else if c == 125 then
      if wantMember && seen != 0 then .err ⟨i.toNat, .expectedKey⟩
      else if (seen &&& sp.need) != sp.need then .err ⟨i.toNat, .missingKey⟩
      else .ok slots (i + 1)
    else if c == 44 then
      if wantMember then .err ⟨i.toNat, .expectedKey⟩
      else objLoopN sp b (i + 1) true seen slots
    else if c == 34 then
      if !wantMember then .err ⟨i.toNat, .expectedComma⟩
      else
        let ke := keyEnd b (i + 1)
        let v := valueAt b i ke
        if ke == 0 then .err ⟨i.toNat, .expectedKey⟩
        else if v == i then .err ⟨i.toNat, .expectedColon⟩
        else
        match lookupKey (keyAt b i (ke - (i + 1))) sp.keys with
        | some (bit, sl) =>
          if (seen &&& bit) != 0 then .err ⟨i.toNat, .duplicateKey⟩
          else
            let e := numEnd b v
            if e == v then .err ⟨v.toNat, .expectedNat⟩
            else if _hj : i < e then
              objLoopN sp b e false (seen ||| bit) (slots.set sl (readNatAt b v e))
            else .err ⟨i.toNat, .noProgress⟩
        | none => .err ⟨i.toNat, .unknownKey⟩
    else .err ⟨i.toNat, .expectedComma⟩
  else .err ⟨i.toNat, .expectedComma⟩
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)

def srMap {α β : Type} (f : α → β) : ScanRes α → ScanRes β
  | .ok a p => .ok (f a) p
  | .err e => .err e

def appSpec : ObjSpec := ⟨[(.kArg, 1, 0), (.kFn, 2, 1)], 3⟩

theorem scanAppExprLoop_eq (b : ByteArray) :
    ∀ n (i : USize) (wm : Bool) (seen : UInt32) (arg fn : Nat), b.size - i.toNat = n →
      scanAppExprLoop b i wm seen arg fn =
        srMap (fun sl => ExprRec.app (sl.getD 1 0) (sl.getD 0 0)) (objLoopN appSpec b i wm seen [arg, fn]) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro i wm seen arg fn hn
    rw [scanAppExprLoop, objLoopN]
    by_cases h : i < b.usize
    · rw [dif_pos h, dif_pos h]
      have hs := usizeStep b i h
      have hb := usizeInBounds b i h
      generalize b.uget i (usizeInBounds b i h) = c
      by_cases hw : isWs c
      · simp only [hw, ↓reduceIte]; exact ih _ (by omega) _ _ _ _ _ rfl
      simp only [hw, Bool.false_eq_true, ↓reduceIte]
      by_cases h125 : c = 125
      · subst h125
        simp only [beq_self_eq_true, ↓reduceIte]
        by_cases h1 : (wm && seen != 0) = true
        · simp [h1, srMap]
        · simp only [h1, Bool.false_eq_true, ↓reduceIte, appSpec]
          by_cases h2 : (seen &&& 3 != 3) = true <;> simp [h2, srMap]
      have n125 : (c == 125) = false := beq_eq_false_iff_ne.mpr h125
      simp only [n125, Bool.false_eq_true, ↓reduceIte]
      by_cases h44 : c = 44
      · subst h44
        simp only [beq_self_eq_true, ↓reduceIte]
        cases wm
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih _ (by omega) _ _ _ _ _ rfl
        · simp [srMap]
      have n44 : (c == 44) = false := beq_eq_false_iff_ne.mpr h44
      simp only [n44, Bool.false_eq_true, ↓reduceIte]
      by_cases h34 : c = 34
      · subst h34
        simp only [beq_self_eq_true, ↓reduceIte]
        cases wm
        · simp [srMap]
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        generalize keyEnd b (i + 1) = ke
        by_cases hk0 : (ke == 0) = true
        · simp [hk0, srMap]
        simp only [hk0, Bool.false_eq_true, ↓reduceIte]
        generalize valueAt b i ke = v
        by_cases hv : (v == i) = true
        · simp [hv, srMap]
        simp only [hv, Bool.false_eq_true, ↓reduceIte]
        generalize keyAt b i (ke - (i + 1)) = k
        cases k <;> simp only [lookupKey, appSpec, reduceCtorEq, ↓reduceIte] <;> try (simp [srMap]; done)
        all_goals
          split
          · rename_i hd; simp [hd, srMap]
          generalize numEnd b v = e
          by_cases he : (e == v) = true
          · simp [he, srMap]
          simp only [he, Bool.false_eq_true, ↓reduceIte]
          by_cases hie : i < e
          · rw [dif_pos hie, dif_pos hie]
            have := USize.lt_iff_toNat_lt.mp hie
            rw [ih _ (by omega) e false _ _ _ rfl]
            simp only [List.set]; rfl
          · rw [dif_neg hie, dif_neg hie]; rfl
      have n34 : (c == 34) = false := beq_eq_false_iff_ne.mpr h34
      simp [n34, srMap]
    · rw [dif_neg h, dif_neg h]; rfl

end ConPanqueque.Scan
