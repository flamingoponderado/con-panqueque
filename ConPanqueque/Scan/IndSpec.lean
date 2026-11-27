import ConPanqueque.Scan.SlotKinds

/-! # Inductive records as object-loop instances

con-leche scans an `inductive` line's payload with five record loops (`scanIndDeclLoop`,
`scanIndTypeLoop`, `scanIndCtorLoop`, `scanIndRecLoop`, `scanRuleLoop`) and four list loops
(`scanInd{Type,Ctor,Rec}ListLoop`, `scanRuleListLoop`).  Here:

* each record loop is `objLoop` at a slot table (`indDeclSpec`, `indTypeSpec`, `indCtorSpec`,
  `indRecSpec`, `ruleSpec`), with the builder of con-leche's record (`*_eq`, in the style of
  `scanAppExprLoop_eq`);
* each list loop is the generic `objList` at its item scanner (`*ListLoop_objList`).

Representation in the slots:
* a value that is a list of records (`types`/`ctors`/`recs` of the declaration, `rules` of a
  recursor) is the `.sub` action: a separate Pancake function scans it, and the slot keeps the
  value's position (`SVal.p`).  The builder reads it again (`rescanL`); the initial slot is
  `.p (2 ^ 64)`, which reads as `[]`;
* `cidx`/`induct` of a constructor (optional numbers) are `.natSet` into a slot that starts as
  `.p (2 ^ 63)` (`optSV none`): the slot's word is the sentinel `2 ^ 63` for `none`, and the capped
  number (`≤ natCap = 2 ^ 62`) for `some x`. -/

namespace ConPanqueque.Scan

open ConLeche.Frontend

/-- A list value read again from a position (`[]` past `2 ^ 64`, or when the scan fails). -/
def rescanL {α : Type} (sc : ByteArray → USize → ScanRes (List α)) (b : ByteArray) (p : Nat) : List α :=
  if p < 2 ^ 64 then
    match sc b (USize.ofNat p) with
    | .ok x _ => x
    | .err _ => []
  else []

theorem usize_toNat_lt64 (v : USize) : v.toNat < 2 ^ 64 :=
  Nat.lt_of_lt_of_le v.toNat_lt_two_pow_numBits (Nat.pow_le_pow_right (by decide) (by
    rcases System.Platform.numBits_eq with h | h <;> omega))

theorem rescanL_of {α : Type} {sc : ByteArray → USize → ScanRes (List α)} {b : ByteArray} {v : USize}
    {x : List α} {e : USize} (h : sc b v = .ok x e) : rescanL sc b v.toNat = x := by
  unfold rescanL
  rw [if_pos (usize_toNat_lt64 v), USize.ofNat_toNat, h]

theorem rescanL_top {α : Type} (sc : ByteArray → USize → ScanRes (List α)) (b : ByteArray) :
    rescanL sc b (2 ^ 64) = [] := by
  simp [rescanL]

/-- The `.sub` scanners (the value accepted, its records dropped). -/
def scRulesU (b : ByteArray) (v : USize) : ScanRes Unit := srMap (fun _ => ()) (scanRules b v)
def scCtorsU (b : ByteArray) (v : USize) : ScanRes Unit := srMap (fun _ => ()) (scanIndCtors b v)
def scRecsU (b : ByteArray) (v : USize) : ScanRes Unit := srMap (fun _ => ()) (scanIndRecs b v)
def scTypesU (b : ByteArray) (v : USize) : ScanRes Unit := srMap (fun _ => ()) (scanIndTypes b v)

/-- An optional number in a slot: `.n x` for `some x`, the sentinel position `2 ^ 63` for `none`. -/
def optSV : Option Nat → SVal
  | none => .p (2 ^ 63)
  | some x => .n x

def SVal.opt : SVal → Option Nat
  | .n x => some x
  | _ => none

@[simp] theorem opt_optSV (o : Option Nat) : (optSV o).opt = o := by cases o <;> rfl

/-! ## The list loops -/

/-- con-leche's `scan*ListLoop`, at any item scanner. -/
def objList {α : Type} (item : ByteArray → USize → ScanRes α) (b : ByteArray) (i : USize) (acc : List α)
    (wantItem : Bool) : ScanRes (List α) :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isWs c then objList item b (i + 1) acc wantItem
    else if c == 93 then
      if wantItem && !acc.isEmpty then .err ⟨i.toNat, .expectedList⟩
      else .ok acc.reverse (i + 1)
    else if c == 44 then
      if wantItem then .err ⟨i.toNat, .expectedList⟩
      else objList item b (i + 1) acc true
    else if c == 123 then
      if !wantItem then .err ⟨i.toNat, .expectedList⟩
      else
        match item b i with
        | .err err => .err err
        | .ok x e =>
          if _hj : i < e then objList item b e (x :: acc) false
          else .err ⟨i.toNat, .noProgress⟩
    else .err ⟨i.toNat, .expectedList⟩
  else .err ⟨i.toNat, .expectedList⟩
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)

/-- `[ … ]` of items. -/
def objListOpen {α : Type} (item : ByteArray → USize → ScanRes α) (b : ByteArray) (i : USize) : ScanRes (List α) :=
  if byteAt b i == 91 then objList item b (i + 1) [] true
  else .err ⟨i.toNat, .expectedList⟩

theorem scanRuleListLoop_objList (b : ByteArray) :
    ∀ msr (i : USize) (acc : List RuleRec) (wi : Bool), b.size - i.toNat = msr →
      scanRuleListLoop b i acc wi = objList scanRule b i acc wi := by
  intro msr
  induction msr using Nat.strongRecOn with
  | _ msr ih =>
    intro i acc wi hn
    rw [scanRuleListLoop, objList]
    by_cases h : i < b.usize
    · rw [dite_eq_left h, dite_eq_left h]
      have hs := usizeStep b i h
      have hb := usizeInBounds b i h
      generalize b.uget i (usizeInBounds b i h) = c
      simp only
      by_cases hw : isWs c
      · simp only [hw, ↓reduceIte]; exact ih _ (by omega) _ _ _ rfl
      simp only [hw, Bool.false_eq_true, ↓reduceIte]
      by_cases h93 : c = 93
      · simp only [h93, beq_self_eq_true, ↓reduceIte]
      have n93 : (c == 93) = false := beq_eq_false_iff_ne.mpr h93
      simp only [n93, Bool.false_eq_true, ↓reduceIte]
      by_cases h44 : c = 44
      · subst h44
        simp only [beq_self_eq_true, ↓reduceIte]
        cases wi
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih _ (by omega) _ _ _ rfl
        · rfl
      have n44 : (c == 44) = false := beq_eq_false_iff_ne.mpr h44
      simp only [n44, Bool.false_eq_true, ↓reduceIte]
      by_cases h123 : c = 123
      · subst h123
        simp only [beq_self_eq_true, ↓reduceIte]
        cases wi
        · rfl
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases scanRule b i with
        | err er => rfl
        | ok x e =>
          simp only
          by_cases hie : i < e
          · rw [dite_eq_left hie, dite_eq_left hie]
            exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ rfl
          · rw [dite_eq_right hie, dite_eq_right hie]
      have n123 : (c == 123) = false := beq_eq_false_iff_ne.mpr h123
      simp only [n123, Bool.false_eq_true, ↓reduceIte]
    · rw [dite_eq_right h, dite_eq_right h]

theorem scanRules_objList (b : ByteArray) (i : USize) : scanRules b i = objListOpen scanRule b i := by
  rw [scanRules, objListOpen, scanRuleListLoop_objList b _ (i + 1) [] true rfl]

theorem scanIndTypeListLoop_objList (b : ByteArray) :
    ∀ msr (i : USize) (acc : List IndTypeRec) (wi : Bool), b.size - i.toNat = msr →
      scanIndTypeListLoop b i acc wi = objList scanIndType b i acc wi := by
  intro msr
  induction msr using Nat.strongRecOn with
  | _ msr ih =>
    intro i acc wi hn
    rw [scanIndTypeListLoop, objList]
    by_cases h : i < b.usize
    · rw [dite_eq_left h, dite_eq_left h]
      have hs := usizeStep b i h
      have hb := usizeInBounds b i h
      generalize b.uget i (usizeInBounds b i h) = c
      simp only
      by_cases hw : isWs c
      · simp only [hw, ↓reduceIte]; exact ih _ (by omega) _ _ _ rfl
      simp only [hw, Bool.false_eq_true, ↓reduceIte]
      by_cases h93 : c = 93
      · simp only [h93, beq_self_eq_true, ↓reduceIte]
      have n93 : (c == 93) = false := beq_eq_false_iff_ne.mpr h93
      simp only [n93, Bool.false_eq_true, ↓reduceIte]
      by_cases h44 : c = 44
      · subst h44
        simp only [beq_self_eq_true, ↓reduceIte]
        cases wi
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih _ (by omega) _ _ _ rfl
        · rfl
      have n44 : (c == 44) = false := beq_eq_false_iff_ne.mpr h44
      simp only [n44, Bool.false_eq_true, ↓reduceIte]
      by_cases h123 : c = 123
      · subst h123
        simp only [beq_self_eq_true, ↓reduceIte]
        cases wi
        · rfl
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases scanIndType b i with
        | err er => rfl
        | ok x e =>
          simp only
          by_cases hie : i < e
          · rw [dite_eq_left hie, dite_eq_left hie]
            exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ rfl
          · rw [dite_eq_right hie, dite_eq_right hie]
      have n123 : (c == 123) = false := beq_eq_false_iff_ne.mpr h123
      simp only [n123, Bool.false_eq_true, ↓reduceIte]
    · rw [dite_eq_right h, dite_eq_right h]

theorem scanIndTypes_objList (b : ByteArray) (i : USize) : scanIndTypes b i = objListOpen scanIndType b i := by
  rw [scanIndTypes, objListOpen, scanIndTypeListLoop_objList b _ (i + 1) [] true rfl]

theorem scanIndCtorListLoop_objList (b : ByteArray) :
    ∀ msr (i : USize) (acc : List IndCtorRec) (wi : Bool), b.size - i.toNat = msr →
      scanIndCtorListLoop b i acc wi = objList scanIndCtor b i acc wi := by
  intro msr
  induction msr using Nat.strongRecOn with
  | _ msr ih =>
    intro i acc wi hn
    rw [scanIndCtorListLoop, objList]
    by_cases h : i < b.usize
    · rw [dite_eq_left h, dite_eq_left h]
      have hs := usizeStep b i h
      have hb := usizeInBounds b i h
      generalize b.uget i (usizeInBounds b i h) = c
      simp only
      by_cases hw : isWs c
      · simp only [hw, ↓reduceIte]; exact ih _ (by omega) _ _ _ rfl
      simp only [hw, Bool.false_eq_true, ↓reduceIte]
      by_cases h93 : c = 93
      · simp only [h93, beq_self_eq_true, ↓reduceIte]
      have n93 : (c == 93) = false := beq_eq_false_iff_ne.mpr h93
      simp only [n93, Bool.false_eq_true, ↓reduceIte]
      by_cases h44 : c = 44
      · subst h44
        simp only [beq_self_eq_true, ↓reduceIte]
        cases wi
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih _ (by omega) _ _ _ rfl
        · rfl
      have n44 : (c == 44) = false := beq_eq_false_iff_ne.mpr h44
      simp only [n44, Bool.false_eq_true, ↓reduceIte]
      by_cases h123 : c = 123
      · subst h123
        simp only [beq_self_eq_true, ↓reduceIte]
        cases wi
        · rfl
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases scanIndCtor b i with
        | err er => rfl
        | ok x e =>
          simp only
          by_cases hie : i < e
          · rw [dite_eq_left hie, dite_eq_left hie]
            exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ rfl
          · rw [dite_eq_right hie, dite_eq_right hie]
      have n123 : (c == 123) = false := beq_eq_false_iff_ne.mpr h123
      simp only [n123, Bool.false_eq_true, ↓reduceIte]
    · rw [dite_eq_right h, dite_eq_right h]

theorem scanIndCtors_objList (b : ByteArray) (i : USize) : scanIndCtors b i = objListOpen scanIndCtor b i := by
  rw [scanIndCtors, objListOpen, scanIndCtorListLoop_objList b _ (i + 1) [] true rfl]

theorem scanIndRecListLoop_objList (b : ByteArray) :
    ∀ msr (i : USize) (acc : List IndRecRec) (wi : Bool), b.size - i.toNat = msr →
      scanIndRecListLoop b i acc wi = objList scanIndRec b i acc wi := by
  intro msr
  induction msr using Nat.strongRecOn with
  | _ msr ih =>
    intro i acc wi hn
    rw [scanIndRecListLoop, objList]
    by_cases h : i < b.usize
    · rw [dite_eq_left h, dite_eq_left h]
      have hs := usizeStep b i h
      have hb := usizeInBounds b i h
      generalize b.uget i (usizeInBounds b i h) = c
      simp only
      by_cases hw : isWs c
      · simp only [hw, ↓reduceIte]; exact ih _ (by omega) _ _ _ rfl
      simp only [hw, Bool.false_eq_true, ↓reduceIte]
      by_cases h93 : c = 93
      · simp only [h93, beq_self_eq_true, ↓reduceIte]
      have n93 : (c == 93) = false := beq_eq_false_iff_ne.mpr h93
      simp only [n93, Bool.false_eq_true, ↓reduceIte]
      by_cases h44 : c = 44
      · subst h44
        simp only [beq_self_eq_true, ↓reduceIte]
        cases wi
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih _ (by omega) _ _ _ rfl
        · rfl
      have n44 : (c == 44) = false := beq_eq_false_iff_ne.mpr h44
      simp only [n44, Bool.false_eq_true, ↓reduceIte]
      by_cases h123 : c = 123
      · subst h123
        simp only [beq_self_eq_true, ↓reduceIte]
        cases wi
        · rfl
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        cases scanIndRec b i with
        | err er => rfl
        | ok x e =>
          simp only
          by_cases hie : i < e
          · rw [dite_eq_left hie, dite_eq_left hie]
            exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ rfl
          · rw [dite_eq_right hie, dite_eq_right hie]
      have n123 : (c == 123) = false := beq_eq_false_iff_ne.mpr h123
      simp only [n123, Bool.false_eq_true, ↓reduceIte]
    · rw [dite_eq_right h, dite_eq_right h]

theorem scanIndRecs_objList (b : ByteArray) (i : USize) : scanIndRecs b i = objListOpen scanIndRec b i := by
  rw [scanIndRecs, objListOpen, scanIndRecListLoop_objList b _ (i + 1) [] true rfl]

/-! ## The record loops (generated) -/

def ruleSpec : ObjSpec := ⟨[(.kCtor, 1, .natSet 0), (.kNfields, 2, .natSet 1), (.kRhs, 4, .natSet 2)], 7⟩

def ruleOf (sl : List SVal) : RuleRec := (⟨(sl.getD 0 default).nat, (sl.getD 1 default).nat, (sl.getD 2 default).nat⟩)

theorem scanRuleLoop_eq (b : ByteArray) :
    ∀ msr (i : USize) (wm : Bool) (seen : UInt32) (ct : Nat) (nf : Nat) (rhs : Nat), b.size - i.toNat = msr →
      scanRuleLoop b i wm seen ct nf rhs =
        srMap (ruleOf) (objLoop ruleSpec b i wm seen [.n ct, .n nf, .n rhs]) := by
  intro msr
  induction msr using Nat.strongRecOn with
  | _ msr ih =>
    intro i wm seen ct nf rhs hn
    rw [scanRuleLoop, objLoop]
    by_cases h : i < b.usize
    · rw [dite_eq_left h, dite_eq_left h]
      have hs := usizeStep b i h
      have hb := usizeInBounds b i h
      generalize b.uget i (usizeInBounds b i h) = c
      by_cases hw : isWs c
      · simp only [hw, ↓reduceIte]; exact ih _ (by omega) _ _ _ _ _ _ rfl
      simp only [hw, Bool.false_eq_true, ↓reduceIte]
      by_cases h125 : c = 125
      · subst h125
        simp only [beq_self_eq_true, ↓reduceIte]
        by_cases h1 : (wm && seen != 0) = true
        · simp [h1, srMap]
        · simp only [h1, Bool.false_eq_true, ↓reduceIte, ruleSpec]
          by_cases h2 : ((seen &&& 7) != 7) = true <;> simp only [h2, ↓reduceIte, srMap, Bool.false_eq_true] <;>
            first | rfl | simp [ruleOf, opt_optSV, SVal.pos, SVal.nat, SVal.list, SVal.bool]
      have n125 : (c == 125) = false := beq_eq_false_iff_ne.mpr h125
      simp only [n125, Bool.false_eq_true, ↓reduceIte]
      by_cases h44 : c = 44
      · subst h44
        simp only [beq_self_eq_true, ↓reduceIte]
        cases wm
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih _ (by omega) _ _ _ _ _ _ rfl
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
        cases k <;> simp only [lookupKey, ruleSpec, reduceCtorEq, ↓reduceIte] <;> try (simp [srMap]; done)
        case kCtor =>
          split
          · simp [srMap]
          simp only [stepVal]
          generalize numEnd b v = e
          by_cases he : (e == v) = true
          · simp [he, srMap]
          simp only [he, Bool.false_eq_true, ↓reduceIte]
          by_cases hie : i < e
          · rw [dite_eq_left hie, dite_eq_left hie]
            have := USize.lt_iff_toNat_lt.mp hie
            rw [ih _ (by omega) e false _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> try rfl
          · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kNfields =>
          split
          · simp [srMap]
          simp only [stepVal]
          generalize numEnd b v = e
          by_cases he : (e == v) = true
          · simp [he, srMap]
          simp only [he, Bool.false_eq_true, ↓reduceIte]
          by_cases hie : i < e
          · rw [dite_eq_left hie, dite_eq_left hie]
            have := USize.lt_iff_toNat_lt.mp hie
            rw [ih _ (by omega) e false _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> try rfl
          · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kRhs =>
          split
          · simp [srMap]
          simp only [stepVal]
          generalize numEnd b v = e
          by_cases he : (e == v) = true
          · simp [he, srMap]
          simp only [he, Bool.false_eq_true, ↓reduceIte]
          by_cases hie : i < e
          · rw [dite_eq_left hie, dite_eq_left hie]
            have := USize.lt_iff_toNat_lt.mp hie
            rw [ih _ (by omega) e false _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> try rfl
          · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
      have n34 : (c == 34) = false := beq_eq_false_iff_ne.mpr h34
      simp [n34, srMap]
    · rw [dite_eq_right h, dite_eq_right h]; rfl

def indTypeSpec : ObjSpec := ⟨[(.kAll, 1, .natListDrop), (.kCtors, 2, .natList 0), (.kIsRec, 4, .bool 1), (.kIsReflexive, 8, .bool 2), (.kIsUnsafe, 16, .bool 3), (.kLevelParams, 32, .natList 4), (.kName, 64, .natSet 5), (.kNumIndices, 128, .natSet 6), (.kNumNested, 256, .natSet 7), (.kNumParams, 512, .natSet 8), (.kType, 1024, .natSet 9)], 2046⟩

def indTypeOf (sl : List SVal) : IndTypeRec := (⟨⟨(sl.getD 5 default).nat, (sl.getD 4 default).list, (sl.getD 9 default).nat⟩, (sl.getD 0 default).list, (sl.getD 1 default).bool, (sl.getD 2 default).bool, (sl.getD 3 default).bool, (sl.getD 6 default).nat, (sl.getD 7 default).nat, (sl.getD 8 default).nat⟩)

theorem scanIndTypeLoop_eq (b : ByteArray) :
    ∀ msr (i : USize) (wm : Bool) (seen : UInt32) (ctors : List Nat) (isRec : Bool) (isRefl : Bool) (isUns : Bool) (lps : List Nat) (nm : Nat) (nIdx : Nat) (nNest : Nat) (nP : Nat) (ty : Nat), b.size - i.toNat = msr →
      scanIndTypeLoop b i wm seen ctors isRec isRefl isUns lps nm nIdx nNest nP ty =
        srMap (indTypeOf) (objLoop indTypeSpec b i wm seen [.l ctors, .b isRec, .b isRefl, .b isUns, .l lps, .n nm, .n nIdx, .n nNest, .n nP, .n ty]) := by
  intro msr
  induction msr using Nat.strongRecOn with
  | _ msr ih =>
    intro i wm seen ctors isRec isRefl isUns lps nm nIdx nNest nP ty hn
    rw [scanIndTypeLoop, objLoop]
    by_cases h : i < b.usize
    · rw [dite_eq_left h, dite_eq_left h]
      have hs := usizeStep b i h
      have hb := usizeInBounds b i h
      generalize b.uget i (usizeInBounds b i h) = c
      by_cases hw : isWs c
      · simp only [hw, ↓reduceIte]; exact ih _ (by omega) _ _ _ _ _ _ _ _ _ _ _ _ _ rfl
      simp only [hw, Bool.false_eq_true, ↓reduceIte]
      by_cases h125 : c = 125
      · subst h125
        simp only [beq_self_eq_true, ↓reduceIte]
        by_cases h1 : (wm && seen != 0) = true
        · simp [h1, srMap]
        · simp only [h1, Bool.false_eq_true, ↓reduceIte, indTypeSpec]
          by_cases h2 : ((seen &&& 2046) != 2046) = true <;> simp only [h2, ↓reduceIte, srMap, Bool.false_eq_true] <;>
            first | rfl | simp [indTypeOf, opt_optSV, SVal.pos, SVal.nat, SVal.list, SVal.bool]
      have n125 : (c == 125) = false := beq_eq_false_iff_ne.mpr h125
      simp only [n125, Bool.false_eq_true, ↓reduceIte]
      by_cases h44 : c = 44
      · subst h44
        simp only [beq_self_eq_true, ↓reduceIte]
        cases wm
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih _ (by omega) _ _ _ _ _ _ _ _ _ _ _ _ _ rfl
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
        cases k <;> simp only [lookupKey, indTypeSpec, reduceCtorEq, ↓reduceIte] <;> try (simp [srMap]; done)
        case kAll =>
          split
          · simp [srMap]
          simp only [stepVal]
          cases hx : scanNatList b v with
          | err er => simp [srMap]
          | ok x e =>
            simp only
            by_cases hie : i < e
            · rw [dite_eq_left hie, dite_eq_left hie]
              have := USize.lt_iff_toNat_lt.mp hie
              rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> try rfl
            · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kCtors =>
          split
          · simp [srMap]
          simp only [stepVal]
          cases hx : scanNatList b v with
          | err er => simp [srMap]
          | ok x e =>
            simp only
            by_cases hie : i < e
            · rw [dite_eq_left hie, dite_eq_left hie]
              have := USize.lt_iff_toNat_lt.mp hie
              rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> try rfl
            · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kIsRec =>
          split
          · simp [srMap]
          simp only [stepVal]
          cases hx : scanBool b v with
          | err er => simp [srMap]
          | ok x e =>
            simp only
            by_cases hie : i < e
            · rw [dite_eq_left hie, dite_eq_left hie]
              have := USize.lt_iff_toNat_lt.mp hie
              rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> try rfl
            · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kIsReflexive =>
          split
          · simp [srMap]
          simp only [stepVal]
          cases hx : scanBool b v with
          | err er => simp [srMap]
          | ok x e =>
            simp only
            by_cases hie : i < e
            · rw [dite_eq_left hie, dite_eq_left hie]
              have := USize.lt_iff_toNat_lt.mp hie
              rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> try rfl
            · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kIsUnsafe =>
          split
          · simp [srMap]
          simp only [stepVal]
          cases hx : scanBool b v with
          | err er => simp [srMap]
          | ok x e =>
            simp only
            by_cases hie : i < e
            · rw [dite_eq_left hie, dite_eq_left hie]
              have := USize.lt_iff_toNat_lt.mp hie
              rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> try rfl
            · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kLevelParams =>
          split
          · simp [srMap]
          simp only [stepVal]
          cases hx : scanNatList b v with
          | err er => simp [srMap]
          | ok x e =>
            simp only
            by_cases hie : i < e
            · rw [dite_eq_left hie, dite_eq_left hie]
              have := USize.lt_iff_toNat_lt.mp hie
              rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> try rfl
            · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kName =>
          split
          · simp [srMap]
          simp only [stepVal]
          generalize numEnd b v = e
          by_cases he : (e == v) = true
          · simp [he, srMap]
          simp only [he, Bool.false_eq_true, ↓reduceIte]
          by_cases hie : i < e
          · rw [dite_eq_left hie, dite_eq_left hie]
            have := USize.lt_iff_toNat_lt.mp hie
            rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> try rfl
          · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kNumIndices =>
          split
          · simp [srMap]
          simp only [stepVal]
          generalize numEnd b v = e
          by_cases he : (e == v) = true
          · simp [he, srMap]
          simp only [he, Bool.false_eq_true, ↓reduceIte]
          by_cases hie : i < e
          · rw [dite_eq_left hie, dite_eq_left hie]
            have := USize.lt_iff_toNat_lt.mp hie
            rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> try rfl
          · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kNumNested =>
          split
          · simp [srMap]
          simp only [stepVal]
          generalize numEnd b v = e
          by_cases he : (e == v) = true
          · simp [he, srMap]
          simp only [he, Bool.false_eq_true, ↓reduceIte]
          by_cases hie : i < e
          · rw [dite_eq_left hie, dite_eq_left hie]
            have := USize.lt_iff_toNat_lt.mp hie
            rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> try rfl
          · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kNumParams =>
          split
          · simp [srMap]
          simp only [stepVal]
          generalize numEnd b v = e
          by_cases he : (e == v) = true
          · simp [he, srMap]
          simp only [he, Bool.false_eq_true, ↓reduceIte]
          by_cases hie : i < e
          · rw [dite_eq_left hie, dite_eq_left hie]
            have := USize.lt_iff_toNat_lt.mp hie
            rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> try rfl
          · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kType =>
          split
          · simp [srMap]
          simp only [stepVal]
          generalize numEnd b v = e
          by_cases he : (e == v) = true
          · simp [he, srMap]
          simp only [he, Bool.false_eq_true, ↓reduceIte]
          by_cases hie : i < e
          · rw [dite_eq_left hie, dite_eq_left hie]
            have := USize.lt_iff_toNat_lt.mp hie
            rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> try rfl
          · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
      have n34 : (c == 34) = false := beq_eq_false_iff_ne.mpr h34
      simp [n34, srMap]
    · rw [dite_eq_right h, dite_eq_right h]; rfl

def indCtorSpec : ObjSpec := ⟨[(.kCidx, 1, .natSet 6), (.kInduct, 2, .natSet 7), (.kIsUnsafe, 4, .bool 0), (.kLevelParams, 8, .natList 1), (.kName, 16, .natSet 2), (.kNumFields, 32, .natSet 3), (.kNumParams, 64, .natSet 4), (.kType, 128, .natSet 5)], 252⟩

def indCtorOf (sl : List SVal) : IndCtorRec := (⟨⟨(sl.getD 2 default).nat, (sl.getD 1 default).list, (sl.getD 5 default).nat⟩, (sl.getD 0 default).bool, (sl.getD 3 default).nat, (sl.getD 4 default).nat, (sl.getD 6 default).opt, (sl.getD 7 default).opt⟩)

theorem scanIndCtorLoop_eq (b : ByteArray) :
    ∀ msr (i : USize) (wm : Bool) (seen : UInt32) (isUns : Bool) (lps : List Nat) (nm : Nat) (nF : Nat) (nP : Nat) (ty : Nat) (ci : Option Nat) (ind : Option Nat), b.size - i.toNat = msr →
      scanIndCtorLoop b i wm seen isUns lps nm nF nP ty ci ind =
        srMap (indCtorOf) (objLoop indCtorSpec b i wm seen [.b isUns, .l lps, .n nm, .n nF, .n nP, .n ty, optSV ci, optSV ind]) := by
  intro msr
  induction msr using Nat.strongRecOn with
  | _ msr ih =>
    intro i wm seen isUns lps nm nF nP ty ci ind hn
    rw [scanIndCtorLoop, objLoop]
    by_cases h : i < b.usize
    · rw [dite_eq_left h, dite_eq_left h]
      have hs := usizeStep b i h
      have hb := usizeInBounds b i h
      generalize b.uget i (usizeInBounds b i h) = c
      by_cases hw : isWs c
      · simp only [hw, ↓reduceIte]; exact ih _ (by omega) _ _ _ _ _ _ _ _ _ _ _ rfl
      simp only [hw, Bool.false_eq_true, ↓reduceIte]
      by_cases h125 : c = 125
      · subst h125
        simp only [beq_self_eq_true, ↓reduceIte]
        by_cases h1 : (wm && seen != 0) = true
        · simp [h1, srMap]
        · simp only [h1, Bool.false_eq_true, ↓reduceIte, indCtorSpec]
          by_cases h2 : ((seen &&& 252) != 252) = true <;> simp only [h2, ↓reduceIte, srMap, Bool.false_eq_true] <;>
            first | rfl | simp [indCtorOf, opt_optSV, SVal.pos, SVal.nat, SVal.list, SVal.bool]
      have n125 : (c == 125) = false := beq_eq_false_iff_ne.mpr h125
      simp only [n125, Bool.false_eq_true, ↓reduceIte]
      by_cases h44 : c = 44
      · subst h44
        simp only [beq_self_eq_true, ↓reduceIte]
        cases wm
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih _ (by omega) _ _ _ _ _ _ _ _ _ _ _ rfl
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
        cases k <;> simp only [lookupKey, indCtorSpec, reduceCtorEq, ↓reduceIte] <;> try (simp [srMap]; done)
        case kCidx =>
          split
          · simp [srMap]
          simp only [stepVal]
          generalize numEnd b v = e
          by_cases he : (e == v) = true
          · simp [he, srMap]
          simp only [he, Bool.false_eq_true, ↓reduceIte]
          by_cases hie : i < e
          · rw [dite_eq_left hie, dite_eq_left hie]
            have := USize.lt_iff_toNat_lt.mp hie
            rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> try rfl
          · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kInduct =>
          split
          · simp [srMap]
          simp only [stepVal]
          generalize numEnd b v = e
          by_cases he : (e == v) = true
          · simp [he, srMap]
          simp only [he, Bool.false_eq_true, ↓reduceIte]
          by_cases hie : i < e
          · rw [dite_eq_left hie, dite_eq_left hie]
            have := USize.lt_iff_toNat_lt.mp hie
            rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> try rfl
          · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kIsUnsafe =>
          split
          · simp [srMap]
          simp only [stepVal]
          cases hx : scanBool b v with
          | err er => simp [srMap]
          | ok x e =>
            simp only
            by_cases hie : i < e
            · rw [dite_eq_left hie, dite_eq_left hie]
              have := USize.lt_iff_toNat_lt.mp hie
              rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> try rfl
            · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kLevelParams =>
          split
          · simp [srMap]
          simp only [stepVal]
          cases hx : scanNatList b v with
          | err er => simp [srMap]
          | ok x e =>
            simp only
            by_cases hie : i < e
            · rw [dite_eq_left hie, dite_eq_left hie]
              have := USize.lt_iff_toNat_lt.mp hie
              rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> try rfl
            · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kName =>
          split
          · simp [srMap]
          simp only [stepVal]
          generalize numEnd b v = e
          by_cases he : (e == v) = true
          · simp [he, srMap]
          simp only [he, Bool.false_eq_true, ↓reduceIte]
          by_cases hie : i < e
          · rw [dite_eq_left hie, dite_eq_left hie]
            have := USize.lt_iff_toNat_lt.mp hie
            rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> try rfl
          · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kNumFields =>
          split
          · simp [srMap]
          simp only [stepVal]
          generalize numEnd b v = e
          by_cases he : (e == v) = true
          · simp [he, srMap]
          simp only [he, Bool.false_eq_true, ↓reduceIte]
          by_cases hie : i < e
          · rw [dite_eq_left hie, dite_eq_left hie]
            have := USize.lt_iff_toNat_lt.mp hie
            rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> try rfl
          · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kNumParams =>
          split
          · simp [srMap]
          simp only [stepVal]
          generalize numEnd b v = e
          by_cases he : (e == v) = true
          · simp [he, srMap]
          simp only [he, Bool.false_eq_true, ↓reduceIte]
          by_cases hie : i < e
          · rw [dite_eq_left hie, dite_eq_left hie]
            have := USize.lt_iff_toNat_lt.mp hie
            rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> try rfl
          · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kType =>
          split
          · simp [srMap]
          simp only [stepVal]
          generalize numEnd b v = e
          by_cases he : (e == v) = true
          · simp [he, srMap]
          simp only [he, Bool.false_eq_true, ↓reduceIte]
          by_cases hie : i < e
          · rw [dite_eq_left hie, dite_eq_left hie]
            have := USize.lt_iff_toNat_lt.mp hie
            rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> try rfl
          · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
      have n34 : (c == 34) = false := beq_eq_false_iff_ne.mpr h34
      simp [n34, srMap]
    · rw [dite_eq_right h, dite_eq_right h]; rfl

def indRecSpec : ObjSpec := ⟨[(.kAll, 1, .natListDrop), (.kIsUnsafe, 2, .bool 0), (.kK, 4, .bool 1), (.kLevelParams, 8, .natList 2), (.kName, 16, .natSet 3), (.kNumIndices, 32, .natSet 4), (.kNumMinors, 64, .natSet 5), (.kNumMotives, 128, .natSet 6), (.kNumParams, 256, .natSet 7), (.kRules, 512, .sub 0 scRulesU 8), (.kType, 1024, .natSet 9)], 2046⟩

def indRecOf (b : ByteArray) (sl : List SVal) : IndRecRec := (⟨⟨(sl.getD 3 default).nat, (sl.getD 2 default).list, (sl.getD 9 default).nat⟩, (sl.getD 0 default).bool, (sl.getD 1 default).bool, (sl.getD 4 default).nat, (sl.getD 5 default).nat, (sl.getD 6 default).nat, (sl.getD 7 default).nat, (rescanL scanRules b (sl.getD 8 default).pos)⟩)

theorem scanIndRecLoop_eq (b : ByteArray) :
    ∀ msr (i : USize) (wm : Bool) (seen : UInt32) (isUns : Bool) (kf : Bool) (lps : List Nat) (nm : Nat) (nIdx : Nat) (nMin : Nat) (nMot : Nat) (nP : Nat) (prules : Nat) (ty : Nat), b.size - i.toNat = msr →
      scanIndRecLoop b i wm seen isUns kf lps nm nIdx nMin nMot nP (rescanL scanRules b prules) ty =
        srMap (indRecOf b) (objLoop indRecSpec b i wm seen [.b isUns, .b kf, .l lps, .n nm, .n nIdx, .n nMin, .n nMot, .n nP, .p prules, .n ty]) := by
  intro msr
  induction msr using Nat.strongRecOn with
  | _ msr ih =>
    intro i wm seen isUns kf lps nm nIdx nMin nMot nP prules ty hn
    rw [scanIndRecLoop, objLoop]
    by_cases h : i < b.usize
    · rw [dite_eq_left h, dite_eq_left h]
      have hs := usizeStep b i h
      have hb := usizeInBounds b i h
      generalize b.uget i (usizeInBounds b i h) = c
      by_cases hw : isWs c
      · simp only [hw, ↓reduceIte]; exact ih _ (by omega) _ _ _ _ _ _ _ _ _ _ _ _ _ rfl
      simp only [hw, Bool.false_eq_true, ↓reduceIte]
      by_cases h125 : c = 125
      · subst h125
        simp only [beq_self_eq_true, ↓reduceIte]
        by_cases h1 : (wm && seen != 0) = true
        · simp [h1, srMap]
        · simp only [h1, Bool.false_eq_true, ↓reduceIte, indRecSpec]
          by_cases h2 : ((seen &&& 2046) != 2046) = true <;> simp only [h2, ↓reduceIte, srMap, Bool.false_eq_true] <;>
            first | rfl | simp [indRecOf, opt_optSV, SVal.pos, SVal.nat, SVal.list, SVal.bool]
      have n125 : (c == 125) = false := beq_eq_false_iff_ne.mpr h125
      simp only [n125, Bool.false_eq_true, ↓reduceIte]
      by_cases h44 : c = 44
      · subst h44
        simp only [beq_self_eq_true, ↓reduceIte]
        cases wm
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih _ (by omega) _ _ _ _ _ _ _ _ _ _ _ _ _ rfl
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
        cases k <;> simp only [lookupKey, indRecSpec, reduceCtorEq, ↓reduceIte] <;> try (simp [srMap]; done)
        case kAll =>
          split
          · simp [srMap]
          simp only [stepVal]
          cases hx : scanNatList b v with
          | err er => simp [srMap]
          | ok x e =>
            simp only
            by_cases hie : i < e
            · rw [dite_eq_left hie, dite_eq_left hie]
              have := USize.lt_iff_toNat_lt.mp hie
              rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> try rfl
            · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kIsUnsafe =>
          split
          · simp [srMap]
          simp only [stepVal]
          cases hx : scanBool b v with
          | err er => simp [srMap]
          | ok x e =>
            simp only
            by_cases hie : i < e
            · rw [dite_eq_left hie, dite_eq_left hie]
              have := USize.lt_iff_toNat_lt.mp hie
              rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> try rfl
            · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kK =>
          split
          · simp [srMap]
          simp only [stepVal]
          cases hx : scanBool b v with
          | err er => simp [srMap]
          | ok x e =>
            simp only
            by_cases hie : i < e
            · rw [dite_eq_left hie, dite_eq_left hie]
              have := USize.lt_iff_toNat_lt.mp hie
              rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> try rfl
            · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kLevelParams =>
          split
          · simp [srMap]
          simp only [stepVal]
          cases hx : scanNatList b v with
          | err er => simp [srMap]
          | ok x e =>
            simp only
            by_cases hie : i < e
            · rw [dite_eq_left hie, dite_eq_left hie]
              have := USize.lt_iff_toNat_lt.mp hie
              rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> try rfl
            · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kName =>
          split
          · simp [srMap]
          simp only [stepVal]
          generalize numEnd b v = e
          by_cases he : (e == v) = true
          · simp [he, srMap]
          simp only [he, Bool.false_eq_true, ↓reduceIte]
          by_cases hie : i < e
          · rw [dite_eq_left hie, dite_eq_left hie]
            have := USize.lt_iff_toNat_lt.mp hie
            rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> try rfl
          · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kNumIndices =>
          split
          · simp [srMap]
          simp only [stepVal]
          generalize numEnd b v = e
          by_cases he : (e == v) = true
          · simp [he, srMap]
          simp only [he, Bool.false_eq_true, ↓reduceIte]
          by_cases hie : i < e
          · rw [dite_eq_left hie, dite_eq_left hie]
            have := USize.lt_iff_toNat_lt.mp hie
            rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> try rfl
          · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kNumMinors =>
          split
          · simp [srMap]
          simp only [stepVal]
          generalize numEnd b v = e
          by_cases he : (e == v) = true
          · simp [he, srMap]
          simp only [he, Bool.false_eq_true, ↓reduceIte]
          by_cases hie : i < e
          · rw [dite_eq_left hie, dite_eq_left hie]
            have := USize.lt_iff_toNat_lt.mp hie
            rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> try rfl
          · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kNumMotives =>
          split
          · simp [srMap]
          simp only [stepVal]
          generalize numEnd b v = e
          by_cases he : (e == v) = true
          · simp [he, srMap]
          simp only [he, Bool.false_eq_true, ↓reduceIte]
          by_cases hie : i < e
          · rw [dite_eq_left hie, dite_eq_left hie]
            have := USize.lt_iff_toNat_lt.mp hie
            rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> try rfl
          · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kNumParams =>
          split
          · simp [srMap]
          simp only [stepVal]
          generalize numEnd b v = e
          by_cases he : (e == v) = true
          · simp [he, srMap]
          simp only [he, Bool.false_eq_true, ↓reduceIte]
          by_cases hie : i < e
          · rw [dite_eq_left hie, dite_eq_left hie]
            have := USize.lt_iff_toNat_lt.mp hie
            rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> try rfl
          · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kRules =>
          split
          · simp [srMap]
          simp only [stepVal, scRulesU]
          cases hx : scanRules b v with
          | err er => simp [srMap]
          | ok x e =>
            simp only [srMap]
            by_cases hie : i < e
            · rw [dite_eq_left hie, dite_eq_left hie]
              have := USize.lt_iff_toNat_lt.mp hie
              rw [← rescanL_of hx, ih _ (by omega) e false _ _ _ _ _ _ _ _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> try rfl
            · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kType =>
          split
          · simp [srMap]
          simp only [stepVal]
          generalize numEnd b v = e
          by_cases he : (e == v) = true
          · simp [he, srMap]
          simp only [he, Bool.false_eq_true, ↓reduceIte]
          by_cases hie : i < e
          · rw [dite_eq_left hie, dite_eq_left hie]
            have := USize.lt_iff_toNat_lt.mp hie
            rw [ih _ (by omega) e false _ _ _ _ _ _ _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> try rfl
          · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
      have n34 : (c == 34) = false := beq_eq_false_iff_ne.mpr h34
      simp [n34, srMap]
    · rw [dite_eq_right h, dite_eq_right h]; rfl

def indDeclSpec : ObjSpec := ⟨[(.kAll, 1, .natListDrop), (.kCtors, 2, .sub 1 scCtorsU 0), (.kIsUnsafe, 4, .boolDrop), (.kRecs, 8, .sub 2 scRecsU 1), (.kTypes, 16, .sub 3 scTypesU 2)], 26⟩

def indDeclOf (b : ByteArray) (sl : List SVal) : DeclRec := (.ind (rescanL scanIndTypes b (sl.getD 2 default).pos) (rescanL scanIndCtors b (sl.getD 0 default).pos) (rescanL scanIndRecs b (sl.getD 1 default).pos))

theorem scanIndDeclLoop_eq (b : ByteArray) :
    ∀ msr (i : USize) (wm : Bool) (seen : UInt32) (pctors : Nat) (precs : Nat) (ptypes : Nat), b.size - i.toNat = msr →
      scanIndDeclLoop b i wm seen (rescanL scanIndCtors b pctors) (rescanL scanIndRecs b precs) (rescanL scanIndTypes b ptypes) =
        srMap (indDeclOf b) (objLoop indDeclSpec b i wm seen [.p pctors, .p precs, .p ptypes]) := by
  intro msr
  induction msr using Nat.strongRecOn with
  | _ msr ih =>
    intro i wm seen pctors precs ptypes hn
    rw [scanIndDeclLoop, objLoop]
    by_cases h : i < b.usize
    · rw [dite_eq_left h, dite_eq_left h]
      have hs := usizeStep b i h
      have hb := usizeInBounds b i h
      generalize b.uget i (usizeInBounds b i h) = c
      by_cases hw : isWs c
      · simp only [hw, ↓reduceIte]; exact ih _ (by omega) _ _ _ _ _ _ rfl
      simp only [hw, Bool.false_eq_true, ↓reduceIte]
      by_cases h125 : c = 125
      · subst h125
        simp only [beq_self_eq_true, ↓reduceIte]
        by_cases h1 : (wm && seen != 0) = true
        · simp [h1, srMap]
        · simp only [h1, Bool.false_eq_true, ↓reduceIte, indDeclSpec]
          by_cases h2 : ((seen &&& 26) != 26) = true <;> simp only [h2, ↓reduceIte, srMap, Bool.false_eq_true] <;>
            first | rfl | simp [indDeclOf, opt_optSV, SVal.pos, SVal.nat, SVal.list, SVal.bool]
      have n125 : (c == 125) = false := beq_eq_false_iff_ne.mpr h125
      simp only [n125, Bool.false_eq_true, ↓reduceIte]
      by_cases h44 : c = 44
      · subst h44
        simp only [beq_self_eq_true, ↓reduceIte]
        cases wm
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih _ (by omega) _ _ _ _ _ _ rfl
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
        cases k <;> simp only [lookupKey, indDeclSpec, reduceCtorEq, ↓reduceIte] <;> try (simp [srMap]; done)
        case kAll =>
          split
          · simp [srMap]
          simp only [stepVal]
          cases hx : scanNatList b v with
          | err er => simp [srMap]
          | ok x e =>
            simp only
            by_cases hie : i < e
            · rw [dite_eq_left hie, dite_eq_left hie]
              have := USize.lt_iff_toNat_lt.mp hie
              rw [ih _ (by omega) e false _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> try rfl
            · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kCtors =>
          split
          · simp [srMap]
          simp only [stepVal, scCtorsU]
          cases hx : scanIndCtors b v with
          | err er => simp [srMap]
          | ok x e =>
            simp only [srMap]
            by_cases hie : i < e
            · rw [dite_eq_left hie, dite_eq_left hie]
              have := USize.lt_iff_toNat_lt.mp hie
              rw [← rescanL_of hx, ih _ (by omega) e false _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> try rfl
            · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kIsUnsafe =>
          split
          · simp [srMap]
          simp only [stepVal]
          cases hx : scanBool b v with
          | err er => simp [srMap]
          | ok x e =>
            simp only
            by_cases hie : i < e
            · rw [dite_eq_left hie, dite_eq_left hie]
              have := USize.lt_iff_toNat_lt.mp hie
              rw [ih _ (by omega) e false _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> try rfl
            · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kRecs =>
          split
          · simp [srMap]
          simp only [stepVal, scRecsU]
          cases hx : scanIndRecs b v with
          | err er => simp [srMap]
          | ok x e =>
            simp only [srMap]
            by_cases hie : i < e
            · rw [dite_eq_left hie, dite_eq_left hie]
              have := USize.lt_iff_toNat_lt.mp hie
              rw [← rescanL_of hx, ih _ (by omega) e false _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> try rfl
            · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
        case kTypes =>
          split
          · simp [srMap]
          simp only [stepVal, scTypesU]
          cases hx : scanIndTypes b v with
          | err er => simp [srMap]
          | ok x e =>
            simp only [srMap]
            by_cases hie : i < e
            · rw [dite_eq_left hie, dite_eq_left hie]
              have := USize.lt_iff_toNat_lt.mp hie
              rw [← rescanL_of hx, ih _ (by omega) e false _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> try rfl
            · rw [dite_eq_right hie, dite_eq_right hie] <;> rfl
      have n34 : (c == 34) = false := beq_eq_false_iff_ne.mpr h34
      simp [n34, srMap]
    · rw [dite_eq_right h, dite_eq_right h]; rfl


/-! ## What the object loop leaves in its slots

`objLoop_slots`: each slot of an accepted record is its initial value or a value one of the spec's
actions wrote (`WrBy`); and every key the spec requires was seen, so its slot holds what its action
wrote.  The bits of distinct actions writing distinct slots must not overlap (`BitsOK`). -/

/-- `sv` is a value an action of `sp` writes to slot `sl`. -/
def WrBy (b : ByteArray) (sp : ObjSpec) (sl : Nat) (sv : SVal) : Prop :=
  ∃ e ∈ sp.keys, ∃ (i v e' : USize), stepVal b i v e.2.2 = .ok (some (sl, sv)) e'

/-- Every seen key's slot holds a written value. -/
def SeenWr (b : ByteArray) (sp : ObjSpec) (seen : UInt32) (slots : List SVal) : Prop :=
  ∀ e ∈ sp.keys, (seen &&& e.2.1) ≠ 0 → ∀ sl kd, e.2.2.wr = some (sl, kd) →
    ∀ h : sl < slots.length, WrBy b sp sl slots[sl]

/-- Overlapping bits write the same slot. -/
def BitsOK (sp : ObjSpec) : Prop :=
  ∀ e1 ∈ sp.keys, ∀ e2 ∈ sp.keys, (e1.2.1 &&& e2.2.1) ≠ 0 → e1.2.2.wr = e2.2.2.wr

theorem stepVal_wr {b : ByteArray} {i v : USize} {a : VAct} {upd : Option (Nat × SVal)} {e : USize}
    (h : stepVal b i v a = .ok upd e) {sl kd : Nat} (hw : a.wr = some (sl, kd)) : ∃ x, upd = some (sl, x) := by
  cases a <;> simp only [VAct.wr, reduceCtorEq, Option.some.injEq, Prod.mk.injEq] at hw <;> simp only [stepVal] at h
  all_goals first
    | (obtain ⟨rfl, -⟩ := hw
       split at h
       · simp at h
       · simp only [ScanRes.ok.injEq] at h; obtain ⟨rfl, -⟩ := h; exact ⟨_, rfl⟩)
    | (obtain ⟨rfl, -⟩ := hw
       split at h <;> simp only [ScanRes.ok.injEq, reduceCtorEq] at h
       obtain ⟨rfl, -⟩ := h; exact ⟨_, rfl⟩)

theorem wrBy_kind {b : ByteArray} {sp : ObjSpec} {sl : Nat} {sv : SVal} (h : WrBy b sp sl sv) :
    ∃ e ∈ sp.keys, e.2.2.wr = some (sl, sv.kind) := by
  obtain ⟨e, he, i, v, e', hs⟩ := h
  refine ⟨e, he, ?_⟩
  rcases stepVal_kind hs with h0 | ⟨sl', x, hx, hw⟩
  · cases h0
  · simp only [Option.some.injEq, Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx; exact hw

theorem u32_and_or (s b c : UInt32) : (s ||| b) &&& c = (s &&& c) ||| (b &&& c) := by
  apply UInt32.toBitVec_inj.mp; simp [BitVec.and_or_distrib_right]

theorem u32_or_ne0 {x y : UInt32} (h : x ||| y ≠ 0) : x ≠ 0 ∨ y ≠ 0 := by
  by_cases hx : x = 0
  · subst hx; right; intro hy; subst hy; exact h (by decide)
  · exact Or.inl hx

/-- A required key is seen once the mask is complete. -/
theorem u32_need {s n bt : UInt32} (h : s &&& n = n) (hb : bt &&& n = bt) (h0 : bt ≠ 0) : s &&& bt ≠ 0 := by
  have : s &&& bt = bt := by
    have e : s &&& bt = s &&& (bt &&& n) := by rw [hb]
    rw [e]
    apply UInt32.toBitVec_inj.mp
    have h' := congrArg UInt32.toBitVec h
    simp only [UInt32.toBitVec_and] at h' ⊢
    rw [BitVec.and_comm bt.toBitVec, ← BitVec.and_assoc, h']
    have hb' := congrArg UInt32.toBitVec hb
    simp only [UInt32.toBitVec_and] at hb'
    rw [BitVec.and_comm]; exact hb'
  rw [this]; exact h0

theorem objLoop_slots (sp : ObjSpec) (hbits : BitsOK sp) (b : ByteArray) :
    ∀ msr (i : USize) (wm : Bool) (seen : UInt32) (slots : List SVal), b.size - i.toNat = msr →
      ∀ slots' j, objLoop sp b i wm seen slots = .ok slots' j → SeenWr b sp seen slots →
      slots'.length = slots.length ∧
      (∀ sl (h : sl < slots.length) (h' : sl < slots'.length), slots'[sl] = slots[sl] ∨ WrBy b sp sl slots'[sl]) ∧
      ∃ seen', (seen' &&& sp.need) = sp.need ∧ SeenWr b sp seen' slots' := by
  intro msr
  induction msr using Nat.strongRecOn with
  | ind msr ih =>
    intro i wm seen slots hm slots' j h hsw
    rw [objLoop] at h
    split at h
    · rename_i hi
      have h1 := usizeInBounds b i hi
      have h2 := usizeStep b i hi
      simp only at h
      split at h
      · exact ih _ (by omega) _ _ _ _ rfl _ _ h hsw
      split at h
      · split at h
        · simp at h
        split at h
        · simp at h
        · rename_i hneed
          simp only [ScanRes.ok.injEq] at h; obtain ⟨rfl, -⟩ := h
          refine ⟨rfl, fun sl _ _ => Or.inl rfl, seen, ?_, hsw⟩
          simpa using hneed
      split at h
      · split at h
        · simp at h
        · exact ih _ (by omega) _ _ _ _ rfl _ _ h hsw
      split at h
      · split at h
        · simp at h
        split at h
        · simp at h
        split at h
        · simp at h
        split at h
        · rename_i bit a hl
          have hmem := lookupKey_mem hl
          split at h
          · simp at h
          split at h
          · simp at h
          · rename_i upd e hsv
            split at h
            · rename_i hj
              -- the slots after this key
              have hsw' : SeenWr b sp (seen ||| bit) (applyUpd slots upd) := by
                intro e2 he2 hs2 sl kd hw2 hsl
                rcases u32_or_ne0 (by rw [← u32_and_or]; exact hs2) with hs | hs
                · -- seen before: its slot was written, and stays so or is rewritten
                  rcases stepVal_kind hsv with rfl | ⟨sl', x, rfl, hwa⟩
                  · exact hsw e2 he2 hs sl kd hw2 hsl
                  · simp only [applyUpd, List.length_set] at hsl ⊢
                    rw [List.getElem_set]
                    split
                    · rename_i hss; subst hss; exact ⟨_, hmem, i, _, _, hsv⟩
                    · exact hsw e2 he2 hs sl kd hw2 hsl
                · -- this key's bit: the same slot as this action
                  have hwe := hbits _ hmem e2 he2 (by
                    intro h0; apply hs; apply UInt32.toBitVec_inj.mp
                    have := congrArg UInt32.toBitVec h0
                    simp only [UInt32.toBitVec_and, UInt32.toBitVec_zero] at this ⊢
                    exact this)
                  simp only at hwe
                  rw [← hwe] at hw2
                  obtain ⟨x, rfl⟩ := stepVal_wr hsv hw2
                  simp only [applyUpd, List.length_set] at hsl ⊢
                  rw [List.getElem_set_self]
                  exact ⟨_, hmem, i, _, _, hsv⟩
              obtain ⟨r1, r2, r3⟩ := ih _ (by have := USize.lt_iff_toNat_lt.mp hj; omega) _ _ _ _ rfl _ _ h hsw'
              have hlen : (applyUpd slots upd).length = slots.length := by
                cases upd with
                | none => rfl
                | some p => simp [applyUpd]
              refine ⟨r1.trans hlen, fun sl hs hs' => ?_, r3⟩
              rcases r2 sl (by rw [hlen]; exact hs) hs' with he | he
              · rw [he]
                rcases stepVal_kind hsv with rfl | ⟨sl', x, rfl, hwa⟩
                · exact Or.inl rfl
                · simp only [applyUpd]
                  rw [List.getElem_set]
                  split
                  · rename_i hss; subst hss; exact Or.inr ⟨_, hmem, i, _, _, hsv⟩
                  · exact Or.inl rfl
              · exact Or.inr he
            · simp at h
        · simp at h
      · simp at h
    · simp at h

/-- At the start nothing is seen. -/
theorem seenWr_zero (b : ByteArray) (sp : ObjSpec) (slots : List SVal) : SeenWr b sp 0 slots := by
  intro e _ h; simp at h

/-- A required key's slot holds what its action wrote. -/
theorem need_wr {b : ByteArray} {sp : ObjSpec} {seen : UInt32} {slots : List SVal}
    (hn : (seen &&& sp.need) = sp.need) (hs : SeenWr b sp seen slots) {e : Key × UInt32 × VAct}
    (he : e ∈ sp.keys) (hb : (e.2.1 &&& sp.need) = e.2.1) (h0 : e.2.1 ≠ 0) {sl kd : Nat}
    (hw : e.2.2.wr = some (sl, kd)) (hl : sl < slots.length) : WrBy b sp sl slots[sl] :=
  hs e he (u32_need hn hb h0) sl kd hw hl

theorem stepVal_sub {b : ByteArray} {i v : USize} {fid : Nat} {sc : ByteArray → USize → ScanRes Unit} {sl sl' : Nat}
    {sv : SVal} {e : USize} (h : stepVal b i v (.sub fid sc sl) = .ok (some (sl', sv)) e) :
    sl' = sl ∧ sv = .p v.toNat ∧ sc b v = .ok () e := by
  simp only [stepVal] at h
  split at h
  · simp at h
  · rename_i u e2 hsc
    simp only [ScanRes.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    exact ⟨rfl, rfl, hsc⟩

theorem stepVal_wr' {b : ByteArray} {i v : USize} {a : VAct} {sl : Nat} {sv : SVal} {e : USize}
    (h : stepVal b i v a = .ok (some (sl, sv)) e) : a.wr = some (sl, sv.kind) := by
  rcases stepVal_kind h with h0 | ⟨sl', x, hx, hw⟩
  · cases h0
  · simp only [Option.some.injEq, Prod.mk.injEq] at hx; obtain ⟨rfl, rfl⟩ := hx; exact hw

end ConPanqueque.Scan
