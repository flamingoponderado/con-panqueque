import ConPanqueque.Scan.Obj

/-! # Each con-leche record loop is an instance of `objLoop` (generated from the scanner source). -/

namespace ConPanqueque.Scan

open ConLeche.Frontend

def scanStrNameSpec : ObjSpec := ⟨[(.kPre, 1, .natSet 0), (.kStr, 2, .str 1)], 3⟩

theorem scanStrNameLoop_eq (b : ByteArray) :
    ∀ msr (i : USize) (wm : Bool) (seen : UInt32) (pre : Nat) (s : String), b.size - i.toNat = msr →
      scanStrNameLoop b i wm seen pre s =
        srMap (fun sl => (NameRec.str (sl.getD 0 default).nat (sl.getD 1 default).str)) (objLoop scanStrNameSpec b i wm seen [.n pre, .s s]) := by
  intro msr
  induction msr using Nat.strongRecOn with
  | _ msr ih =>
    intro i wm seen pre s hn
    rw [scanStrNameLoop, objLoop]
    by_cases h : i < b.usize
    · rw [dite_eq_left h, dite_eq_left h]
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
        · simp only [h1, Bool.false_eq_true, ↓reduceIte, scanStrNameSpec]
          split <;> simp_all [srMap, SVal.nat, SVal.list, SVal.str, SVal.bool, SVal.hint]
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
        cases k <;> simp only [lookupKey, scanStrNameSpec, reduceCtorEq, ↓reduceIte] <;> try (simp [srMap]; done)
        case kPre =>
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
            rw [ih _ (by omega) e false _ _ _ rfl]
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
        case kStr =>
          split
          · simp [srMap]
          simp only [stepVal]
          cases hx : scanString b v with
          | err er => simp [srMap]
          | ok x e =>
            simp only
            by_cases hie : i < e
            · rw [dite_eq_left hie, dite_eq_left hie]
              have := USize.lt_iff_toNat_lt.mp hie
              rw [ih _ (by omega) e false _ _ _ rfl]
              simp only [applyUpd, List.set] <;> rfl
            · rw [dite_eq_right hie, dite_eq_right hie]; rfl
      have n34 : (c == 34) = false := beq_eq_false_iff_ne.mpr h34
      simp [n34, srMap]
    · rw [dite_eq_right h, dite_eq_right h]; rfl

def scanNumNameSpec : ObjSpec := ⟨[(.kI, 1, .natSet 0), (.kPre, 2, .natSet 1)], 3⟩

theorem scanNumNameLoop_eq (b : ByteArray) :
    ∀ msr (i : USize) (wm : Bool) (seen : UInt32) (n : Nat) (pre : Nat), b.size - i.toNat = msr →
      scanNumNameLoop b i wm seen n pre =
        srMap (fun sl => (NameRec.num (sl.getD 1 default).nat (sl.getD 0 default).nat)) (objLoop scanNumNameSpec b i wm seen [.n n, .n pre]) := by
  intro msr
  induction msr using Nat.strongRecOn with
  | _ msr ih =>
    intro i wm seen n pre hn
    rw [scanNumNameLoop, objLoop]
    by_cases h : i < b.usize
    · rw [dite_eq_left h, dite_eq_left h]
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
        · simp only [h1, Bool.false_eq_true, ↓reduceIte, scanNumNameSpec]
          split <;> simp_all [srMap, SVal.nat, SVal.list, SVal.str, SVal.bool, SVal.hint]
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
        cases k <;> simp only [lookupKey, scanNumNameSpec, reduceCtorEq, ↓reduceIte] <;> try (simp [srMap]; done)
        case kI =>
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
            rw [ih _ (by omega) e false _ _ _ rfl]
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
        case kPre =>
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
            rw [ih _ (by omega) e false _ _ _ rfl]
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
      have n34 : (c == 34) = false := beq_eq_false_iff_ne.mpr h34
      simp [n34, srMap]
    · rw [dite_eq_right h, dite_eq_right h]; rfl

def scanLamExprSpec : ObjSpec := ⟨[(.kBinderInfo, 1, .binder), (.kBody, 2, .natSet 0), (.kName, 4, .natDrop), (.kType, 8, .natSet 1)], 15⟩

theorem scanLamExprLoop_eq (b : ByteArray) :
    ∀ msr (i : USize) (wm : Bool) (seen : UInt32) (bd : Nat) (ty : Nat), b.size - i.toNat = msr →
      scanLamExprLoop b i wm seen bd ty =
        srMap (fun sl => (ExprRec.lam (sl.getD 1 default).nat (sl.getD 0 default).nat)) (objLoop scanLamExprSpec b i wm seen [.n bd, .n ty]) := by
  intro msr
  induction msr using Nat.strongRecOn with
  | _ msr ih =>
    intro i wm seen bd ty hn
    rw [scanLamExprLoop, objLoop]
    by_cases h : i < b.usize
    · rw [dite_eq_left h, dite_eq_left h]
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
        · simp only [h1, Bool.false_eq_true, ↓reduceIte, scanLamExprSpec]
          split <;> simp_all [srMap, SVal.nat, SVal.list, SVal.str, SVal.bool, SVal.hint]
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
        cases k <;> simp only [lookupKey, scanLamExprSpec, reduceCtorEq, ↓reduceIte] <;> try (simp [srMap]; done)
        case kBinderInfo =>
          split
          · simp [srMap]
          simp only [stepVal]
          generalize scanBinderInfo b v = e
          by_cases he : (e == 0) = true
          · simp [he, srMap]
          simp only [he, Bool.false_eq_true, ↓reduceIte]
          by_cases hie : i < e
          · rw [dite_eq_left hie, dite_eq_left hie]
            have := USize.lt_iff_toNat_lt.mp hie
            rw [ih _ (by omega) e false _ _ _ rfl]
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
        case kBody =>
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
            rw [ih _ (by omega) e false _ _ _ rfl]
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
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
            rw [ih _ (by omega) e false _ _ _ rfl]
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
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
            rw [ih _ (by omega) e false _ _ _ rfl]
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
      have n34 : (c == 34) = false := beq_eq_false_iff_ne.mpr h34
      simp [n34, srMap]
    · rw [dite_eq_right h, dite_eq_right h]; rfl

def scanForallExprSpec : ObjSpec := ⟨[(.kBinderInfo, 1, .binder), (.kBody, 2, .natSet 0), (.kName, 4, .natDrop), (.kType, 8, .natSet 1)], 15⟩

theorem scanForallExprLoop_eq (b : ByteArray) :
    ∀ msr (i : USize) (wm : Bool) (seen : UInt32) (bd : Nat) (ty : Nat), b.size - i.toNat = msr →
      scanForallExprLoop b i wm seen bd ty =
        srMap (fun sl => (ExprRec.forallE (sl.getD 1 default).nat (sl.getD 0 default).nat)) (objLoop scanForallExprSpec b i wm seen [.n bd, .n ty]) := by
  intro msr
  induction msr using Nat.strongRecOn with
  | _ msr ih =>
    intro i wm seen bd ty hn
    rw [scanForallExprLoop, objLoop]
    by_cases h : i < b.usize
    · rw [dite_eq_left h, dite_eq_left h]
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
        · simp only [h1, Bool.false_eq_true, ↓reduceIte, scanForallExprSpec]
          split <;> simp_all [srMap, SVal.nat, SVal.list, SVal.str, SVal.bool, SVal.hint]
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
        cases k <;> simp only [lookupKey, scanForallExprSpec, reduceCtorEq, ↓reduceIte] <;> try (simp [srMap]; done)
        case kBinderInfo =>
          split
          · simp [srMap]
          simp only [stepVal]
          generalize scanBinderInfo b v = e
          by_cases he : (e == 0) = true
          · simp [he, srMap]
          simp only [he, Bool.false_eq_true, ↓reduceIte]
          by_cases hie : i < e
          · rw [dite_eq_left hie, dite_eq_left hie]
            have := USize.lt_iff_toNat_lt.mp hie
            rw [ih _ (by omega) e false _ _ _ rfl]
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
        case kBody =>
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
            rw [ih _ (by omega) e false _ _ _ rfl]
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
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
            rw [ih _ (by omega) e false _ _ _ rfl]
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
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
            rw [ih _ (by omega) e false _ _ _ rfl]
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
      have n34 : (c == 34) = false := beq_eq_false_iff_ne.mpr h34
      simp [n34, srMap]
    · rw [dite_eq_right h, dite_eq_right h]; rfl

def scanLetExprSpec : ObjSpec := ⟨[(.kBody, 1, .natSet 0), (.kName, 2, .natDrop), (.kNondep, 4, .boolDrop), (.kType, 8, .natSet 1), (.kValue, 16, .natSet 2)], 27⟩

theorem scanLetExprLoop_eq (b : ByteArray) :
    ∀ msr (i : USize) (wm : Bool) (seen : UInt32) (bd : Nat) (ty : Nat) (vl : Nat), b.size - i.toNat = msr →
      scanLetExprLoop b i wm seen bd ty vl =
        srMap (fun sl => (ExprRec.letE (sl.getD 1 default).nat (sl.getD 2 default).nat (sl.getD 0 default).nat)) (objLoop scanLetExprSpec b i wm seen [.n bd, .n ty, .n vl]) := by
  intro msr
  induction msr using Nat.strongRecOn with
  | _ msr ih =>
    intro i wm seen bd ty vl hn
    rw [scanLetExprLoop, objLoop]
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
        · simp only [h1, Bool.false_eq_true, ↓reduceIte, scanLetExprSpec]
          split <;> simp_all [srMap, SVal.nat, SVal.list, SVal.str, SVal.bool, SVal.hint]
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
        cases k <;> simp only [lookupKey, scanLetExprSpec, reduceCtorEq, ↓reduceIte] <;> try (simp [srMap]; done)
        case kBody =>
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
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
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
            rw [ih _ (by omega) e false _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
        case kNondep =>
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
              simp only [applyUpd, List.set] <;> rfl
            · rw [dite_eq_right hie, dite_eq_right hie]; rfl
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
            rw [ih _ (by omega) e false _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
        case kValue =>
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
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
      have n34 : (c == 34) = false := beq_eq_false_iff_ne.mpr h34
      simp [n34, srMap]
    · rw [dite_eq_right h, dite_eq_right h]; rfl

def scanConstExprSpec : ObjSpec := ⟨[(.kName, 1, .natSet 0), (.kUs, 2, .natList 1)], 3⟩

theorem scanConstExprLoop_eq (b : ByteArray) :
    ∀ msr (i : USize) (wm : Bool) (seen : UInt32) (nm : Nat) (us : List Nat), b.size - i.toNat = msr →
      scanConstExprLoop b i wm seen nm us =
        srMap (fun sl => (ExprRec.const (sl.getD 0 default).nat (sl.getD 1 default).list)) (objLoop scanConstExprSpec b i wm seen [.n nm, .l us]) := by
  intro msr
  induction msr using Nat.strongRecOn with
  | _ msr ih =>
    intro i wm seen nm us hn
    rw [scanConstExprLoop, objLoop]
    by_cases h : i < b.usize
    · rw [dite_eq_left h, dite_eq_left h]
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
        · simp only [h1, Bool.false_eq_true, ↓reduceIte, scanConstExprSpec]
          split <;> simp_all [srMap, SVal.nat, SVal.list, SVal.str, SVal.bool, SVal.hint]
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
        cases k <;> simp only [lookupKey, scanConstExprSpec, reduceCtorEq, ↓reduceIte] <;> try (simp [srMap]; done)
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
            rw [ih _ (by omega) e false _ _ _ rfl]
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
        case kUs =>
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
              rw [ih _ (by omega) e false _ _ _ rfl]
              simp only [applyUpd, List.set] <;> rfl
            · rw [dite_eq_right hie, dite_eq_right hie]; rfl
      have n34 : (c == 34) = false := beq_eq_false_iff_ne.mpr h34
      simp [n34, srMap]
    · rw [dite_eq_right h, dite_eq_right h]; rfl

def scanProjExprSpec : ObjSpec := ⟨[(.kIdx, 1, .natSet 0), (.kStruct, 2, .natSet 1), (.kTypeName, 4, .natSet 2)], 7⟩

theorem scanProjExprLoop_eq (b : ByteArray) :
    ∀ msr (i : USize) (wm : Bool) (seen : UInt32) (ix : Nat) (st : Nat) (tn : Nat), b.size - i.toNat = msr →
      scanProjExprLoop b i wm seen ix st tn =
        srMap (fun sl => (ExprRec.proj (sl.getD 2 default).nat (sl.getD 0 default).nat (sl.getD 1 default).nat)) (objLoop scanProjExprSpec b i wm seen [.n ix, .n st, .n tn]) := by
  intro msr
  induction msr using Nat.strongRecOn with
  | _ msr ih =>
    intro i wm seen ix st tn hn
    rw [scanProjExprLoop, objLoop]
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
        · simp only [h1, Bool.false_eq_true, ↓reduceIte, scanProjExprSpec]
          split <;> simp_all [srMap, SVal.nat, SVal.list, SVal.str, SVal.bool, SVal.hint]
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
        cases k <;> simp only [lookupKey, scanProjExprSpec, reduceCtorEq, ↓reduceIte] <;> try (simp [srMap]; done)
        case kIdx =>
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
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
        case kStruct =>
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
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
        case kTypeName =>
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
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
      have n34 : (c == 34) = false := beq_eq_false_iff_ne.mpr h34
      simp [n34, srMap]
    · rw [dite_eq_right h, dite_eq_right h]; rfl

def scanDefDeclSpec : ObjSpec := ⟨[(.kAll, 1, .natListDrop), (.kHints, 2, .hints 0), (.kLevelParams, 4, .natList 1), (.kName, 8, .natSet 2), (.kSafety, 16, .str 3), (.kType, 32, .natSet 4), (.kValue, 64, .natSet 5)], 124⟩

theorem scanDefDeclLoop_eq (b : ByteArray) :
    ∀ msr (i : USize) (wm : Bool) (seen : UInt32) (hints : HintsRec) (lps : List Nat) (nm : Nat) (safety : String) (ty : Nat) (vl : Nat), b.size - i.toNat = msr →
      scanDefDeclLoop b i wm seen hints lps nm safety ty vl =
        srMap (fun sl => (DeclRec.defn ⟨(sl.getD 2 default).nat, (sl.getD 1 default).list, (sl.getD 4 default).nat⟩ (sl.getD 5 default).nat (sl.getD 0 default).hint (sl.getD 3 default).str)) (objLoop scanDefDeclSpec b i wm seen [.h hints, .l lps, .n nm, .s safety, .n ty, .n vl]) := by
  intro msr
  induction msr using Nat.strongRecOn with
  | _ msr ih =>
    intro i wm seen hints lps nm safety ty vl hn
    rw [scanDefDeclLoop, objLoop]
    by_cases h : i < b.usize
    · rw [dite_eq_left h, dite_eq_left h]
      have hs := usizeStep b i h
      have hb := usizeInBounds b i h
      generalize b.uget i (usizeInBounds b i h) = c
      by_cases hw : isWs c
      · simp only [hw, ↓reduceIte]; exact ih _ (by omega) _ _ _ _ _ _ _ _ _ rfl
      simp only [hw, Bool.false_eq_true, ↓reduceIte]
      by_cases h125 : c = 125
      · subst h125
        simp only [beq_self_eq_true, ↓reduceIte]
        by_cases h1 : (wm && seen != 0) = true
        · simp [h1, srMap]
        · simp only [h1, Bool.false_eq_true, ↓reduceIte, scanDefDeclSpec]
          split <;> simp_all [srMap, SVal.nat, SVal.list, SVal.str, SVal.bool, SVal.hint]
      have n125 : (c == 125) = false := beq_eq_false_iff_ne.mpr h125
      simp only [n125, Bool.false_eq_true, ↓reduceIte]
      by_cases h44 : c = 44
      · subst h44
        simp only [beq_self_eq_true, ↓reduceIte]
        cases wm
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih _ (by omega) _ _ _ _ _ _ _ _ _ rfl
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
        cases k <;> simp only [lookupKey, scanDefDeclSpec, reduceCtorEq, ↓reduceIte] <;> try (simp [srMap]; done)
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
              rw [ih _ (by omega) e false _ _ _ _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> rfl
            · rw [dite_eq_right hie, dite_eq_right hie]; rfl
        case kHints =>
          split
          · simp [srMap]
          simp only [stepVal]
          cases hx : scanHints b v with
          | err er => simp [srMap]
          | ok x e =>
            simp only
            by_cases hie : i < e
            · rw [dite_eq_left hie, dite_eq_left hie]
              have := USize.lt_iff_toNat_lt.mp hie
              rw [ih _ (by omega) e false _ _ _ _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> rfl
            · rw [dite_eq_right hie, dite_eq_right hie]; rfl
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
              rw [ih _ (by omega) e false _ _ _ _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> rfl
            · rw [dite_eq_right hie, dite_eq_right hie]; rfl
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
            rw [ih _ (by omega) e false _ _ _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
        case kSafety =>
          split
          · simp [srMap]
          simp only [stepVal]
          cases hx : scanString b v with
          | err er => simp [srMap]
          | ok x e =>
            simp only
            by_cases hie : i < e
            · rw [dite_eq_left hie, dite_eq_left hie]
              have := USize.lt_iff_toNat_lt.mp hie
              rw [ih _ (by omega) e false _ _ _ _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> rfl
            · rw [dite_eq_right hie, dite_eq_right hie]; rfl
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
            rw [ih _ (by omega) e false _ _ _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
        case kValue =>
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
            rw [ih _ (by omega) e false _ _ _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
      have n34 : (c == 34) = false := beq_eq_false_iff_ne.mpr h34
      simp [n34, srMap]
    · rw [dite_eq_right h, dite_eq_right h]; rfl

def scanThmDeclSpec : ObjSpec := ⟨[(.kAll, 1, .natListDrop), (.kLevelParams, 2, .natList 0), (.kName, 4, .natSet 1), (.kType, 8, .natSet 2), (.kValue, 16, .natSet 3)], 30⟩

theorem scanThmDeclLoop_eq (b : ByteArray) :
    ∀ msr (i : USize) (wm : Bool) (seen : UInt32) (lps : List Nat) (nm : Nat) (ty : Nat) (vl : Nat), b.size - i.toNat = msr →
      scanThmDeclLoop b i wm seen lps nm ty vl =
        srMap (fun sl => (DeclRec.thm ⟨(sl.getD 1 default).nat, (sl.getD 0 default).list, (sl.getD 2 default).nat⟩ (sl.getD 3 default).nat)) (objLoop scanThmDeclSpec b i wm seen [.l lps, .n nm, .n ty, .n vl]) := by
  intro msr
  induction msr using Nat.strongRecOn with
  | _ msr ih =>
    intro i wm seen lps nm ty vl hn
    rw [scanThmDeclLoop, objLoop]
    by_cases h : i < b.usize
    · rw [dite_eq_left h, dite_eq_left h]
      have hs := usizeStep b i h
      have hb := usizeInBounds b i h
      generalize b.uget i (usizeInBounds b i h) = c
      by_cases hw : isWs c
      · simp only [hw, ↓reduceIte]; exact ih _ (by omega) _ _ _ _ _ _ _ rfl
      simp only [hw, Bool.false_eq_true, ↓reduceIte]
      by_cases h125 : c = 125
      · subst h125
        simp only [beq_self_eq_true, ↓reduceIte]
        by_cases h1 : (wm && seen != 0) = true
        · simp [h1, srMap]
        · simp only [h1, Bool.false_eq_true, ↓reduceIte, scanThmDeclSpec]
          split <;> simp_all [srMap, SVal.nat, SVal.list, SVal.str, SVal.bool, SVal.hint]
      have n125 : (c == 125) = false := beq_eq_false_iff_ne.mpr h125
      simp only [n125, Bool.false_eq_true, ↓reduceIte]
      by_cases h44 : c = 44
      · subst h44
        simp only [beq_self_eq_true, ↓reduceIte]
        cases wm
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih _ (by omega) _ _ _ _ _ _ _ rfl
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
        cases k <;> simp only [lookupKey, scanThmDeclSpec, reduceCtorEq, ↓reduceIte] <;> try (simp [srMap]; done)
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
              rw [ih _ (by omega) e false _ _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> rfl
            · rw [dite_eq_right hie, dite_eq_right hie]; rfl
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
              rw [ih _ (by omega) e false _ _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> rfl
            · rw [dite_eq_right hie, dite_eq_right hie]; rfl
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
            rw [ih _ (by omega) e false _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
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
            rw [ih _ (by omega) e false _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
        case kValue =>
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
            rw [ih _ (by omega) e false _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
      have n34 : (c == 34) = false := beq_eq_false_iff_ne.mpr h34
      simp [n34, srMap]
    · rw [dite_eq_right h, dite_eq_right h]; rfl

def scanOpaqueDeclSpec : ObjSpec := ⟨[(.kAll, 1, .natListDrop), (.kIsUnsafe, 2, .bool 0), (.kLevelParams, 4, .natList 1), (.kName, 8, .natSet 2), (.kType, 16, .natSet 3), (.kValue, 32, .natSet 4)], 62⟩

theorem scanOpaqueDeclLoop_eq (b : ByteArray) :
    ∀ msr (i : USize) (wm : Bool) (seen : UInt32) (isUns : Bool) (lps : List Nat) (nm : Nat) (ty : Nat) (vl : Nat), b.size - i.toNat = msr →
      scanOpaqueDeclLoop b i wm seen isUns lps nm ty vl =
        srMap (fun sl => (DeclRec.opaq ⟨(sl.getD 2 default).nat, (sl.getD 1 default).list, (sl.getD 3 default).nat⟩ (sl.getD 4 default).nat (sl.getD 0 default).bool)) (objLoop scanOpaqueDeclSpec b i wm seen [.b isUns, .l lps, .n nm, .n ty, .n vl]) := by
  intro msr
  induction msr using Nat.strongRecOn with
  | _ msr ih =>
    intro i wm seen isUns lps nm ty vl hn
    rw [scanOpaqueDeclLoop, objLoop]
    by_cases h : i < b.usize
    · rw [dite_eq_left h, dite_eq_left h]
      have hs := usizeStep b i h
      have hb := usizeInBounds b i h
      generalize b.uget i (usizeInBounds b i h) = c
      by_cases hw : isWs c
      · simp only [hw, ↓reduceIte]; exact ih _ (by omega) _ _ _ _ _ _ _ _ rfl
      simp only [hw, Bool.false_eq_true, ↓reduceIte]
      by_cases h125 : c = 125
      · subst h125
        simp only [beq_self_eq_true, ↓reduceIte]
        by_cases h1 : (wm && seen != 0) = true
        · simp [h1, srMap]
        · simp only [h1, Bool.false_eq_true, ↓reduceIte, scanOpaqueDeclSpec]
          split <;> simp_all [srMap, SVal.nat, SVal.list, SVal.str, SVal.bool, SVal.hint]
      have n125 : (c == 125) = false := beq_eq_false_iff_ne.mpr h125
      simp only [n125, Bool.false_eq_true, ↓reduceIte]
      by_cases h44 : c = 44
      · subst h44
        simp only [beq_self_eq_true, ↓reduceIte]
        cases wm
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih _ (by omega) _ _ _ _ _ _ _ _ rfl
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
        cases k <;> simp only [lookupKey, scanOpaqueDeclSpec, reduceCtorEq, ↓reduceIte] <;> try (simp [srMap]; done)
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
              rw [ih _ (by omega) e false _ _ _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> rfl
            · rw [dite_eq_right hie, dite_eq_right hie]; rfl
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
              rw [ih _ (by omega) e false _ _ _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> rfl
            · rw [dite_eq_right hie, dite_eq_right hie]; rfl
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
              rw [ih _ (by omega) e false _ _ _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> rfl
            · rw [dite_eq_right hie, dite_eq_right hie]; rfl
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
            rw [ih _ (by omega) e false _ _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
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
            rw [ih _ (by omega) e false _ _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
        case kValue =>
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
            rw [ih _ (by omega) e false _ _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
      have n34 : (c == 34) = false := beq_eq_false_iff_ne.mpr h34
      simp [n34, srMap]
    · rw [dite_eq_right h, dite_eq_right h]; rfl

def scanAxiomDeclSpec : ObjSpec := ⟨[(.kIsUnsafe, 1, .bool 0), (.kLevelParams, 2, .natList 1), (.kName, 4, .natSet 2), (.kType, 8, .natSet 3)], 15⟩

theorem scanAxiomDeclLoop_eq (b : ByteArray) :
    ∀ msr (i : USize) (wm : Bool) (seen : UInt32) (isUns : Bool) (lps : List Nat) (nm : Nat) (ty : Nat), b.size - i.toNat = msr →
      scanAxiomDeclLoop b i wm seen isUns lps nm ty =
        srMap (fun sl => (DeclRec.ax ⟨(sl.getD 2 default).nat, (sl.getD 1 default).list, (sl.getD 3 default).nat⟩ (sl.getD 0 default).bool)) (objLoop scanAxiomDeclSpec b i wm seen [.b isUns, .l lps, .n nm, .n ty]) := by
  intro msr
  induction msr using Nat.strongRecOn with
  | _ msr ih =>
    intro i wm seen isUns lps nm ty hn
    rw [scanAxiomDeclLoop, objLoop]
    by_cases h : i < b.usize
    · rw [dite_eq_left h, dite_eq_left h]
      have hs := usizeStep b i h
      have hb := usizeInBounds b i h
      generalize b.uget i (usizeInBounds b i h) = c
      by_cases hw : isWs c
      · simp only [hw, ↓reduceIte]; exact ih _ (by omega) _ _ _ _ _ _ _ rfl
      simp only [hw, Bool.false_eq_true, ↓reduceIte]
      by_cases h125 : c = 125
      · subst h125
        simp only [beq_self_eq_true, ↓reduceIte]
        by_cases h1 : (wm && seen != 0) = true
        · simp [h1, srMap]
        · simp only [h1, Bool.false_eq_true, ↓reduceIte, scanAxiomDeclSpec]
          split <;> simp_all [srMap, SVal.nat, SVal.list, SVal.str, SVal.bool, SVal.hint]
      have n125 : (c == 125) = false := beq_eq_false_iff_ne.mpr h125
      simp only [n125, Bool.false_eq_true, ↓reduceIte]
      by_cases h44 : c = 44
      · subst h44
        simp only [beq_self_eq_true, ↓reduceIte]
        cases wm
        · simp only [Bool.false_eq_true, ↓reduceIte]; exact ih _ (by omega) _ _ _ _ _ _ _ rfl
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
        cases k <;> simp only [lookupKey, scanAxiomDeclSpec, reduceCtorEq, ↓reduceIte] <;> try (simp [srMap]; done)
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
              rw [ih _ (by omega) e false _ _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> rfl
            · rw [dite_eq_right hie, dite_eq_right hie]; rfl
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
              rw [ih _ (by omega) e false _ _ _ _ _ rfl]
              simp only [applyUpd, List.set] <;> rfl
            · rw [dite_eq_right hie, dite_eq_right hie]; rfl
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
            rw [ih _ (by omega) e false _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
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
            rw [ih _ (by omega) e false _ _ _ _ _ rfl]
            simp only [applyUpd, List.set] <;> rfl
          · rw [dite_eq_right hie, dite_eq_right hie]; rfl
      have n34 : (c == 34) = false := beq_eq_false_iff_ne.mpr h34
      simp [n34, srMap]
    · rw [dite_eq_right h, dite_eq_right h]; rfl


end ConPanqueque.Scan
