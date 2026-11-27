import ConPanqueque.Scan.ObjInst

/-! # The line loop as a table

con-leche's `scanLineLoop` reads one line's object: index keys (`in`/`il`/`ie`) and one payload
key.  `lineLoopI` is the same loop with the payload keys read off a table of actions (`LAct`);
keys the port does not handle yet are rejected (`.reject`).  Soundness only:
`lineLoopI_sound` says an accept of `lineLoopI` is an accept of `scanLineLoop` with the same record. -/

namespace ConPanqueque.Scan

open ConLeche.Frontend

/-- A payload key's action. -/
inductive LAct where
  /-- an index key: `in` (1), `il` (2), `ie` (3) -/
  | idx (kind : UInt8)
  /-- a number payload -/
  | natPl (mk : Nat → LinePayload)
  /-- a string payload -/
  | strPl (mk : String → LinePayload)
  /-- a record payload, read by `scan` -/
  | objPl (scan : ByteArray → USize → ScanRes LinePayload)
  /-- not handled by the port: rejected -/
  | reject

def lookupL (k : Key) : List (Key × LAct) → LAct
  | [] => .reject
  | (k', a) :: r => if k = k' then a else lookupL k r

def lineEnd (i : USize) (idxKind : UInt8) (idx : Nat) : LinePayload → ScanRes LineRec
  | .name r => if idxKind = 1 then .ok (.name idx r) (i + 1) else .err ⟨i.toNat, .mixedKeys⟩
  | .level r => if idxKind = 2 then .ok (.level idx r) (i + 1) else .err ⟨i.toNat, .mixedKeys⟩
  | .expr r => if idxKind = 3 then .ok (.expr idx r) (i + 1) else .err ⟨i.toNat, .mixedKeys⟩
  | .decl d => if idxKind = 0 then .ok (.decl d) (i + 1) else .err ⟨i.toNat, .mixedKeys⟩
  | .header => if idxKind = 0 then .ok .header (i + 1) else .err ⟨i.toNat, .mixedKeys⟩
  | .absent => .err ⟨i.toNat, .missingKey⟩

/-- The line loop, payload keys from a table. -/
def lineLoopI (tbl : List (Key × LAct)) (b : ByteArray) (i : USize) (wantMember : Bool)
    (idxKind : UInt8) (idx : Nat) (pl : LinePayload) : ScanRes LineRec :=
  if h : i < b.usize then
    let c := b.uget i (usizeInBounds b i h)
    if isWs c then lineLoopI tbl b (i + 1) wantMember idxKind idx pl
    else if c == 125 then
      if wantMember && (idxKind != 0 || !pl.isAbsent) then .err ⟨i.toNat, .expectedKey⟩
      else lineEnd i idxKind idx pl
    else if c == 44 then
      if wantMember then .err ⟨i.toNat, .expectedKey⟩
      else lineLoopI tbl b (i + 1) true idxKind idx pl
    else if c == 34 then
      if !wantMember then .err ⟨i.toNat, .expectedComma⟩
      else
        let ke := keyEnd b (i + 1)
        let v := valueAt b i ke
        if ke == 0 then .err ⟨i.toNat, .expectedKey⟩
        else if v == i then .err ⟨i.toNat, .expectedColon⟩
        else
          match lookupL (keyAt b i (ke - (i + 1))) tbl with
          | .idx kind =>
            if idxKind != 0 then .err ⟨i.toNat, .duplicateKey⟩
            else
              let e := numEnd b v
              if e == v then .err ⟨v.toNat, .expectedNat⟩
              else if _hj : i < e then lineLoopI tbl b e false kind (readNatAt b v e) pl
              else .err ⟨i.toNat, .noProgress⟩
          | .natPl mk =>
            if !pl.isAbsent then .err ⟨i.toNat, .duplicateKey⟩
            else
              let e := numEnd b v
              if e == v then .err ⟨v.toNat, .expectedNat⟩
              else if _hj : i < e then lineLoopI tbl b e false idxKind idx (mk (readNatAt b v e))
              else .err ⟨i.toNat, .noProgress⟩
          | .strPl mk =>
            if !pl.isAbsent then .err ⟨i.toNat, .duplicateKey⟩
            else
              match scanString b v with
              | .err err => .err err
              | .ok s e =>
                if _hj : i < e then lineLoopI tbl b e false idxKind idx (mk s)
                else .err ⟨i.toNat, .noProgress⟩
          | .objPl scan =>
            if !pl.isAbsent then .err ⟨i.toNat, .duplicateKey⟩
            else
              match scan b v with
              | .err err => .err err
              | .ok r e =>
                if _hj : i < e then lineLoopI tbl b e false idxKind idx r
                else .err ⟨i.toNat, .noProgress⟩
          | .reject => .err ⟨i.toNat, .unknownKey⟩
    else .err ⟨i.toNat, .expectedComma⟩
  else .err ⟨i.toNat, .expectedComma⟩
termination_by b.size - i.toNat
decreasing_by
  all_goals
    first
      | (have := usizeInBounds b i h; have := usizeStep b i h; omega)
      | exact Nat.sub_lt_sub_left (usizeInBounds b i h) (USize.lt_iff_toNat_lt.mp _hj)

def nameStr (b : ByteArray) (v : USize) : ScanRes LinePayload := srMap .name (scanStrName b v)
def nameNum (b : ByteArray) (v : USize) : ScanRes LinePayload := srMap .name (scanNumName b v)
def exprApp (b : ByteArray) (v : USize) : ScanRes LinePayload := srMap .expr (scanAppExpr b v)
def exprLam (b : ByteArray) (v : USize) : ScanRes LinePayload := srMap .expr (scanLamExpr b v)
def exprForall (b : ByteArray) (v : USize) : ScanRes LinePayload := srMap .expr (scanForallExpr b v)
def exprLet (b : ByteArray) (v : USize) : ScanRes LinePayload := srMap .expr (scanLetExpr b v)
def exprConst (b : ByteArray) (v : USize) : ScanRes LinePayload := srMap .expr (scanConstExpr b v)
def exprProj (b : ByteArray) (v : USize) : ScanRes LinePayload := srMap .expr (scanProjExpr b v)
def declDef (b : ByteArray) (v : USize) : ScanRes LinePayload := srMap .decl (scanDefDecl b v)
def declThm (b : ByteArray) (v : USize) : ScanRes LinePayload := srMap .decl (scanThmDecl b v)
def declOpaque (b : ByteArray) (v : USize) : ScanRes LinePayload := srMap .decl (scanOpaqueDecl b v)
def declAx (b : ByteArray) (v : USize) : ScanRes LinePayload := srMap .decl (scanAxiomDecl b v)
def declQuot (b : ByteArray) (v : USize) : ScanRes LinePayload := srMap .decl (scanQuotDecl b v)
def declInd (b : ByteArray) (v : USize) : ScanRes LinePayload := srMap .decl (scanIndDecl b v)
def natValPl (b : ByteArray) (v : USize) : ScanRes LinePayload := srMap (fun n => .expr (.natVal n)) (scanQuotedNat b v)

/-- The header's value: a `{`-opened object skipped by bracket depth. -/
def metaHdr (b : ByteArray) (v : USize) : ScanRes LinePayload :=
  if byteAt b v != 123 then .err ⟨v.toNat, .expectedObject⟩
  else
    let e := skipBraced b (v + 1) 0
    if e == 0 then .err ⟨v.toNat, .expectedObject⟩ else .ok .header e

/-- `max`/`imax`: a two-element number list. -/
def levMax (b : ByteArray) (v : USize) : ScanRes LinePayload :=
  match scanNatList b v with
  | .err er => .err er
  | .ok us e => match us with
    | [a, d] => .ok (.level (.max a d)) e
    | _ => .err ⟨v.toNat, .expectedList⟩

def levImax (b : ByteArray) (v : USize) : ScanRes LinePayload :=
  match scanNatList b v with
  | .err er => .err er
  | .ok us e => match us with
    | [a, d] => .ok (.level (.imax a d)) e
    | _ => .err ⟨v.toNat, .expectedList⟩

theorem levMax_ok {b : ByteArray} {v e : USize} {r : LinePayload} (h : levMax b v = .ok r e) :
    ∃ a d, r = .level (.max a d) ∧ scanNatList b v = .ok [a, d] e := by
  unfold levMax at h
  split at h
  · simp at h
  · rename_i us e' hsc
    rcases us with _ | ⟨a, _ | ⟨d, _ | ⟨x, rest⟩⟩⟩ <;> simp only [ScanRes.ok.injEq, reduceCtorEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨a, d, rfl, hsc⟩

theorem levImax_ok {b : ByteArray} {v e : USize} {r : LinePayload} (h : levImax b v = .ok r e) :
    ∃ a d, r = .level (.imax a d) ∧ scanNatList b v = .ok [a, d] e := by
  unfold levImax at h
  split at h
  · simp at h
  · rename_i us e' hsc
    rcases us with _ | ⟨a, _ | ⟨d, _ | ⟨x, rest⟩⟩⟩ <;> simp only [ScanRes.ok.injEq, reduceCtorEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨a, d, rfl, hsc⟩

/-- The port's line table. -/
def lineTbl : List (Key × LAct) :=
  [(.kIn, .idx 1), (.kIl, .idx 2), (.kIe, .idx 3),
   (.kBvar, .natPl (fun n => .expr (.bvar n))), (.kSort, .natPl (fun n => .expr (.sort n))),
   (.kSucc, .natPl (fun n => .level (.succ n))), (.kParam, .natPl (fun n => .level (.param n))),
   (.kStr, .objPl nameStr), (.kNum, .objPl nameNum),
   (.kApp, .objPl exprApp), (.kLam, .objPl exprLam), (.kForallE, .objPl exprForall), (.kLetE, .objPl exprLet),
   (.kConst, .objPl exprConst), (.kProj, .objPl exprProj),
   (.kStrVal, .strPl (fun s => .expr (.strVal s))),
   (.kDef, .objPl declDef), (.kThm, .objPl declThm), (.kOpaque, .objPl declOpaque),
   (.kMeta, .objPl metaHdr), (.kMax, .objPl levMax), (.kImax, .objPl levImax),
   (.kNatVal, .objPl natValPl), (.kAxiom, .objPl declAx), (.kQuot, .objPl declQuot),
   (.kInductive, .objPl declInd)]

theorem srMap_ok {α β : Type} {f : α → β} {x : ScanRes α} {y : β} {p : USize} (h : srMap f x = .ok y p) :
    ∃ a, x = .ok a p ∧ y = f a := by
  cases x with
  | ok a q => simp only [srMap, ScanRes.ok.injEq] at h; exact ⟨a, by rw [h.2], h.1.symm⟩
  | err e => simp [srMap] at h

set_option maxHeartbeats 4000000 in
/-- **The table's line loop is sound for con-leche's**. -/
theorem lineLoopI_sound (b : ByteArray) :
    ∀ msr (i : USize) (wm : Bool) (ik : UInt8) (idx : Nat) (pl : LinePayload) (r : LineRec) (p : USize),
      b.size - i.toNat = msr → lineLoopI lineTbl b i wm ik idx pl = .ok r p →
      scanLineLoop b i wm ik idx pl = .ok r p := by
  intro msr
  induction msr using Nat.strongRecOn with
  | _ msr ih =>
    intro i wm ik idx pl r p hn hok
    rw [lineLoopI] at hok
    unfold scanLineLoop
    by_cases h0 : ¬ i < b.usize
    · rw [dite_eq_right h0] at hok; simp at hok
    have h : i < b.usize := by simpa using h0
    rw [dite_eq_left h] at hok ⊢
    have hs := usizeStep b i h
    have hb := usizeInBounds b i h
    generalize b.uget i (usizeInBounds b i h) = c at hok ⊢
    simp only at hok ⊢
    by_cases hw : isWs c
    · simp only [hw, ↓reduceIte] at hok ⊢; exact ih _ (by omega) _ _ _ _ _ _ _ rfl hok
    simp only [hw, Bool.false_eq_true, ↓reduceIte] at hok ⊢
    by_cases h125 : c = 125
    · subst h125
      simp only [beq_self_eq_true, ↓reduceIte] at hok ⊢
      split at hok
      · simp at hok
      rename_i hwm
      rw [ite_eq_right hwm]
      cases pl <;> simp only [lineEnd] at hok
      · simp at hok
      all_goals
        split at hok
        · rename_i hik; subst hik; simpa using hok
        · simp at hok
    have n125 : (c == 125) = false := beq_eq_false_iff_ne.mpr h125
    simp only [n125, Bool.false_eq_true, ↓reduceIte] at hok ⊢
    by_cases h44 : c = 44
    · subst h44
      simp only [beq_self_eq_true, ↓reduceIte] at hok ⊢
      cases wm
      · simp only [Bool.false_eq_true, ↓reduceIte] at hok ⊢; exact ih _ (by omega) _ _ _ _ _ _ _ rfl hok
      · simp at hok
    have n44 : (c == 44) = false := beq_eq_false_iff_ne.mpr h44
    simp only [n44, Bool.false_eq_true, ↓reduceIte] at hok ⊢
    by_cases h34 : c = 34
    · subst h34
      simp only [beq_self_eq_true, ↓reduceIte] at hok ⊢
      cases wm
      · simp at hok
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      generalize keyEnd b (i + 1) = ke at hok ⊢
      by_cases hk0 : (ke == 0) = true
      · simp [hk0] at hok
      simp only [hk0, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      generalize valueAt b i ke = v at hok ⊢
      by_cases hv : (v == i) = true
      · simp [hv] at hok
      simp only [hv, Bool.false_eq_true, ↓reduceIte] at hok ⊢
      generalize keyAt b i (ke - (i + 1)) = k at hok ⊢
      cases k <;> simp only [lookupL, lineTbl, reduceCtorEq, ↓reduceIte] at hok <;> (try simp at hok; done)
      case kIn =>
        dsimp only
        split at hok
        · simp at hok
        rename_i hik
        rw [ite_eq_right hik]
        generalize numEnd b v = e at hok ⊢
        split at hok
        · simp at hok
        rename_i he
        rw [ite_eq_right he]
        split at hok
        · rename_i hie
          rw [dite_eq_left hie]
          exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ _ _ _ _ rfl hok
        · simp at hok
      case kIl =>
        dsimp only
        split at hok
        · simp at hok
        rename_i hik
        rw [ite_eq_right hik]
        generalize numEnd b v = e at hok ⊢
        split at hok
        · simp at hok
        rename_i he
        rw [ite_eq_right he]
        split at hok
        · rename_i hie
          rw [dite_eq_left hie]
          exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ _ _ _ _ rfl hok
        · simp at hok
      case kIe =>
        dsimp only
        split at hok
        · simp at hok
        rename_i hik
        rw [ite_eq_right hik]
        generalize numEnd b v = e at hok ⊢
        split at hok
        · simp at hok
        rename_i he
        rw [ite_eq_right he]
        split at hok
        · rename_i hie
          rw [dite_eq_left hie]
          exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ _ _ _ _ rfl hok
        · simp at hok
      case kBvar =>
        dsimp only
        split at hok
        · simp at hok
        rename_i hpl
        rw [ite_eq_right hpl]
        generalize numEnd b v = e at hok ⊢
        split at hok
        · simp at hok
        rename_i he
        rw [ite_eq_right he]
        split at hok
        · rename_i hie
          rw [dite_eq_left hie]
          exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ _ _ _ _ rfl hok
        · simp at hok
      case kSort =>
        dsimp only
        split at hok
        · simp at hok
        rename_i hpl
        rw [ite_eq_right hpl]
        generalize numEnd b v = e at hok ⊢
        split at hok
        · simp at hok
        rename_i he
        rw [ite_eq_right he]
        split at hok
        · rename_i hie
          rw [dite_eq_left hie]
          exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ _ _ _ _ rfl hok
        · simp at hok
      case kSucc =>
        dsimp only
        split at hok
        · simp at hok
        rename_i hpl
        rw [ite_eq_right hpl]
        generalize numEnd b v = e at hok ⊢
        split at hok
        · simp at hok
        rename_i he
        rw [ite_eq_right he]
        split at hok
        · rename_i hie
          rw [dite_eq_left hie]
          exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ _ _ _ _ rfl hok
        · simp at hok
      case kParam =>
        dsimp only
        split at hok
        · simp at hok
        rename_i hpl
        rw [ite_eq_right hpl]
        generalize numEnd b v = e at hok ⊢
        split at hok
        · simp at hok
        rename_i he
        rw [ite_eq_right he]
        split at hok
        · rename_i hie
          rw [dite_eq_left hie]
          exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ _ _ _ _ rfl hok
        · simp at hok
      case kStr =>
        dsimp only
        split at hok
        · simp at hok
        rename_i hpl
        rw [ite_eq_right hpl]
        simp only [nameStr] at hok
        cases hsc : scanStrName b v with
        | err er => rw [hsc] at hok; simp [srMap] at hok
        | ok r0 e =>
          rw [hsc] at hok
          simp only [srMap] at hok ⊢
          split at hok
          · rename_i hie
            rw [dite_eq_left hie]
            exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ _ _ _ _ rfl hok
          · simp at hok
      case kNum =>
        dsimp only
        split at hok
        · simp at hok
        rename_i hpl
        rw [ite_eq_right hpl]
        simp only [nameNum] at hok
        cases hsc : scanNumName b v with
        | err er => rw [hsc] at hok; simp [srMap] at hok
        | ok r0 e =>
          rw [hsc] at hok
          simp only [srMap] at hok ⊢
          split at hok
          · rename_i hie
            rw [dite_eq_left hie]
            exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ _ _ _ _ rfl hok
          · simp at hok
      case kApp =>
        dsimp only
        split at hok
        · simp at hok
        rename_i hpl
        rw [ite_eq_right hpl]
        simp only [exprApp] at hok
        cases hsc : scanAppExpr b v with
        | err er => rw [hsc] at hok; simp [srMap] at hok
        | ok r0 e =>
          rw [hsc] at hok
          simp only [srMap] at hok ⊢
          split at hok
          · rename_i hie
            rw [dite_eq_left hie]
            exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ _ _ _ _ rfl hok
          · simp at hok
      case kLam =>
        dsimp only
        split at hok
        · simp at hok
        rename_i hpl
        rw [ite_eq_right hpl]
        simp only [exprLam] at hok
        cases hsc : scanLamExpr b v with
        | err er => rw [hsc] at hok; simp [srMap] at hok
        | ok r0 e =>
          rw [hsc] at hok
          simp only [srMap] at hok ⊢
          split at hok
          · rename_i hie
            rw [dite_eq_left hie]
            exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ _ _ _ _ rfl hok
          · simp at hok
      case kForallE =>
        dsimp only
        split at hok
        · simp at hok
        rename_i hpl
        rw [ite_eq_right hpl]
        simp only [exprForall] at hok
        cases hsc : scanForallExpr b v with
        | err er => rw [hsc] at hok; simp [srMap] at hok
        | ok r0 e =>
          rw [hsc] at hok
          simp only [srMap] at hok ⊢
          split at hok
          · rename_i hie
            rw [dite_eq_left hie]
            exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ _ _ _ _ rfl hok
          · simp at hok
      case kLetE =>
        dsimp only
        split at hok
        · simp at hok
        rename_i hpl
        rw [ite_eq_right hpl]
        simp only [exprLet] at hok
        cases hsc : scanLetExpr b v with
        | err er => rw [hsc] at hok; simp [srMap] at hok
        | ok r0 e =>
          rw [hsc] at hok
          simp only [srMap] at hok ⊢
          split at hok
          · rename_i hie
            rw [dite_eq_left hie]
            exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ _ _ _ _ rfl hok
          · simp at hok
      case kConst =>
        dsimp only
        split at hok
        · simp at hok
        rename_i hpl
        rw [ite_eq_right hpl]
        simp only [exprConst] at hok
        cases hsc : scanConstExpr b v with
        | err er => rw [hsc] at hok; simp [srMap] at hok
        | ok r0 e =>
          rw [hsc] at hok
          simp only [srMap] at hok ⊢
          split at hok
          · rename_i hie
            rw [dite_eq_left hie]
            exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ _ _ _ _ rfl hok
          · simp at hok
      case kProj =>
        dsimp only
        split at hok
        · simp at hok
        rename_i hpl
        rw [ite_eq_right hpl]
        simp only [exprProj] at hok
        cases hsc : scanProjExpr b v with
        | err er => rw [hsc] at hok; simp [srMap] at hok
        | ok r0 e =>
          rw [hsc] at hok
          simp only [srMap] at hok ⊢
          split at hok
          · rename_i hie
            rw [dite_eq_left hie]
            exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ _ _ _ _ rfl hok
          · simp at hok
      case kDef =>
        dsimp only
        split at hok
        · simp at hok
        rename_i hpl
        rw [ite_eq_right hpl]
        simp only [declDef] at hok
        cases hsc : scanDefDecl b v with
        | err er => rw [hsc] at hok; simp [srMap] at hok
        | ok r0 e =>
          rw [hsc] at hok
          simp only [srMap] at hok ⊢
          split at hok
          · rename_i hie
            rw [dite_eq_left hie]
            exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ _ _ _ _ rfl hok
          · simp at hok
      case kThm =>
        dsimp only
        split at hok
        · simp at hok
        rename_i hpl
        rw [ite_eq_right hpl]
        simp only [declThm] at hok
        cases hsc : scanThmDecl b v with
        | err er => rw [hsc] at hok; simp [srMap] at hok
        | ok r0 e =>
          rw [hsc] at hok
          simp only [srMap] at hok ⊢
          split at hok
          · rename_i hie
            rw [dite_eq_left hie]
            exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ _ _ _ _ rfl hok
          · simp at hok
      case kOpaque =>
        dsimp only
        split at hok
        · simp at hok
        rename_i hpl
        rw [ite_eq_right hpl]
        simp only [declOpaque] at hok
        cases hsc : scanOpaqueDecl b v with
        | err er => rw [hsc] at hok; simp [srMap] at hok
        | ok r0 e =>
          rw [hsc] at hok
          simp only [srMap] at hok ⊢
          split at hok
          · rename_i hie
            rw [dite_eq_left hie]
            exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ _ _ _ _ rfl hok
          · simp at hok
      case kStrVal =>
        dsimp only
        split at hok
        · simp at hok
        rename_i hpl
        rw [ite_eq_right hpl]
        cases hsc : scanString b v with
        | err er => rw [hsc] at hok; simp at hok
        | ok s0 e =>
          rw [hsc] at hok
          simp only at hok ⊢
          split at hok
          · rename_i hie
            rw [dite_eq_left hie]
            exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ _ _ _ _ rfl hok
          · simp at hok
      case kMeta =>
        dsimp only
        split at hok
        · simp at hok
        rename_i hpl
        rw [ite_eq_right hpl]
        simp only [metaHdr] at hok
        by_cases hb1 : (byteAt b v != 123) = true
        · simp only [hb1, ↓reduceIte] at hok; simp at hok
        simp only [hb1, Bool.false_eq_true, ↓reduceIte] at hok ⊢
        by_cases he0 : (skipBraced b (v + 1) 0 == 0) = true
        · simp only [he0, ↓reduceIte] at hok; simp at hok
        simp only [he0, Bool.false_eq_true, ↓reduceIte] at hok ⊢
        split at hok
        · rename_i hie
          rw [dite_eq_left hie]
          exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ _ _ _ _ rfl hok
        · simp at hok
      case kMax =>
        dsimp only
        split at hok
        · simp at hok
        rename_i hpl
        rw [ite_eq_right hpl]
        simp only [levMax] at hok
        cases hsc : scanNatList b v with
        | err er => rw [hsc] at hok; simp at hok
        | ok us e =>
          rw [hsc] at hok
          simp only at hok ⊢
          rcases us with _ | ⟨a, _ | ⟨d, _ | ⟨x, rest⟩⟩⟩ <;> simp only [reduceCtorEq] at hok
          all_goals try (simp at hok; done)
          simp only at hok ⊢
          split at hok
          · rename_i hie
            rw [dite_eq_left hie]
            exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ _ _ _ _ rfl hok
          · simp at hok
      case kImax =>
        dsimp only
        split at hok
        · simp at hok
        rename_i hpl
        rw [ite_eq_right hpl]
        simp only [levImax] at hok
        cases hsc : scanNatList b v with
        | err er => rw [hsc] at hok; simp at hok
        | ok us e =>
          rw [hsc] at hok
          simp only at hok ⊢
          rcases us with _ | ⟨a, _ | ⟨d, _ | ⟨x, rest⟩⟩⟩ <;> simp only [reduceCtorEq] at hok
          all_goals try (simp at hok; done)
          simp only at hok ⊢
          split at hok
          · rename_i hie
            rw [dite_eq_left hie]
            exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ _ _ _ _ rfl hok
          · simp at hok
      case kAxiom =>
        dsimp only
        split at hok
        · simp at hok
        rename_i hpl
        rw [ite_eq_right hpl]
        simp only [declAx] at hok
        cases hsc : scanAxiomDecl b v with
        | err er => rw [hsc] at hok; simp [srMap] at hok
        | ok r0 e =>
          rw [hsc] at hok
          simp only [srMap] at hok ⊢
          split at hok
          · rename_i hie
            rw [dite_eq_left hie]
            exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ _ _ _ _ rfl hok
          · simp at hok
      case kQuot =>
        dsimp only
        split at hok
        · simp at hok
        rename_i hpl
        rw [ite_eq_right hpl]
        simp only [declQuot] at hok
        cases hsc : scanQuotDecl b v with
        | err er => rw [hsc] at hok; simp [srMap] at hok
        | ok r0 e =>
          rw [hsc] at hok
          simp only [srMap] at hok ⊢
          split at hok
          · rename_i hie
            rw [dite_eq_left hie]
            exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ _ _ _ _ rfl hok
          · simp at hok
      case kInductive =>
        dsimp only
        split at hok
        · simp at hok
        rename_i hpl
        rw [ite_eq_right hpl]
        simp only [declInd] at hok
        cases hsc : scanIndDecl b v with
        | err er => rw [hsc] at hok; simp [srMap] at hok
        | ok r0 e =>
          rw [hsc] at hok
          simp only [srMap] at hok ⊢
          split at hok
          · rename_i hie
            rw [dite_eq_left hie]
            exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ _ _ _ _ rfl hok
          · simp at hok
      case kNatVal =>
        dsimp only
        split at hok
        · simp at hok
        rename_i hpl
        rw [ite_eq_right hpl]
        simp only [natValPl] at hok
        cases hsc : scanQuotedNat b v with
        | err er => rw [hsc] at hok; simp [srMap] at hok
        | ok r0 e =>
          rw [hsc] at hok
          simp only [srMap] at hok ⊢
          split at hok
          · rename_i hie
            rw [dite_eq_left hie]
            exact ih _ (by have := USize.lt_iff_toNat_lt.mp hie; omega) _ _ _ _ _ _ _ rfl hok
          · simp at hok
    have n34 : (c == 34) = false := beq_eq_false_iff_ne.mpr h34
    simp [n34] at hok

end ConPanqueque.Scan
