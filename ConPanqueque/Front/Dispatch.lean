import ConPanqueque.Front.LineFns

/-! # The line dispatcher, branch by branch

A branch: the line's tag names a table entry (`tag_t`), the entry's scanner gives con-leche's
payload, `lineEnd` gives the record, and `applyLine` (the line placed) is the record's entry
function; the branch calls the tag's line function, whose core is in `LineFns`. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (ExprRec LevelRec NameRec LineRec LinePayload ScanRes byteAt)

variable {σ : Type}

def kTg := ofString "ktg"
def kS0 := ofString "ks0"
def kIx := ofString "kix"
def kNx := ofString "knx"
def kR0 := ofString "kr0"
def kLn := ofString "kln"

/-- The line functions' arguments at the dispatcher. -/
def lineArgs : List (ExpHOL 64) :=
  [vv fTN, vv fTL, vv fTE, vv fCap, vv kIx, vv kS0, vv kS0, vv kBA, vv kBN, vv kRB, vv kCapD]

theorem evAll_lineArgs (Γ : Env) (C : Ctx) (jN jL jE cap : Nat) (wi ws0 : BitVec 64) (bufJ bsz rb capD : Nat)
    (h1 : Γ.get fTN = some (cellA C jN)) (h2 : Γ.get fTL = some (cellA C jL)) (h3 : Γ.get fTE = some (cellA C jE))
    (h4 : Γ.get fCap = some (BitVec.ofNat 64 cap)) (h5 : Γ.get kIx = some wi) (h6 : Γ.get kS0 = some ws0)
    (h7 : Γ.get kBA = some (cellA C bufJ)) (h8 : Γ.get kBN = some (BitVec.ofNat 64 bsz))
    (h9 : Γ.get kRB = some (cellA C rb)) (h10 : Γ.get kCapD = some (BitVec.ofNat 64 capD)) :
    EvAll (fun e v => sev Γ e = some v) lineArgs (lineVs C jN jL jE cap wi ws0 bufJ bsz rb capD) := by
  simp only [lineArgs, lineVs, EvAll, sev, vv]
  exact ⟨h1, h2, h3, h4, h5, h6, h6, h7, h8, h9, h10, trivial⟩

/-- A scanner that opens with its `{` check starts inside the buffer. -/
theorem start_lt {α : Type} {b : ByteArray} (hp : Plat b) {v : USize} {x : ScanRes α} {er : ConLeche.Frontend.ScanErr}
    {r : α} {j : USize} (h : (if byteAt b v == 123 then x else .err er) = .ok r j) : v.toNat < b.size := by
  split at h
  · rename_i hb
    by_cases hl : v.toNat < b.size
    · exact hl
    · have : byteAt b v = 0 := by
        rw [byteAt_eq hp v]; simp [List.getElem?_eq_none (by simp; omega : b.data.toList.length ≤ v.toNat)]
      rw [this] at hb; simp at hb
  · simp at h

theorem applyLine_expr (st : StateD) (i : Nat) (e : ExprRec) (n : Nat) (hn : n ≠ 0) :
    applyLine st (.expr i e) n = (parseExprEntryD st i e >>= fun st' => pure (.inl st')) := by
  simp [applyLine, lineRecPlaced, applyRecord, hn]

theorem applyLine_level (st : StateD) (i : Nat) (e : LevelRec) (n : Nat) (hn : n ≠ 0) :
    applyLine st (.level i e) n = (parseLevelEntryD st i e >>= fun st' => pure (.inl st')) := by
  simp [applyLine, lineRecPlaced, applyRecord, hn]

theorem applyLine_name (st : StateD) (i : Nat) (e : NameRec) (n : Nat) (hn : n ≠ 0) :
    applyLine st (.name i e) n = (parseNameEntryD st i e >>= fun st' => pure (.inl st')) := by
  simp [applyLine, lineRecPlaced, applyRecord, hn]

theorem applyLine_decl (st : StateD) (d : ConLeche.Frontend.DeclRec) (n : Nat) (hn : n ≠ 0) :
    applyLine st (.decl d) n = processLineCoreD st d := by
  simp [applyLine, lineRecPlaced, applyRecord, applyDeclD, hn]

/-- An expression payload's record. -/
theorem lineEnd_expr {j0 j' : USize} {ik : UInt8} {idx : Nat} {e : ExprRec} {rec : LineRec}
    (h : lineEnd j0 ik idx (.expr e) = .ok rec j') : rec = .expr idx e := by
  simp only [lineEnd] at h; split at h
  · simp only [ScanRes.ok.injEq] at h; exact h.1.symm
  · simp at h

theorem lineEnd_level {j0 j' : USize} {ik : UInt8} {idx : Nat} {e : LevelRec} {rec : LineRec}
    (h : lineEnd j0 ik idx (.level e) = .ok rec j') : rec = .level idx e := by
  simp only [lineEnd] at h; split at h
  · simp only [ScanRes.ok.injEq] at h; exact h.1.symm
  · simp at h

theorem lineEnd_name {j0 j' : USize} {ik : UInt8} {idx : Nat} {e : NameRec} {rec : LineRec}
    (h : lineEnd j0 ik idx (.name e) = .ok rec j') : rec = .name idx e := by
  simp only [lineEnd] at h; split at h
  · simp only [ScanRes.ok.injEq] at h; exact h.1.symm
  · simp at h

theorem lineEnd_decl {j0 j' : USize} {ik : UInt8} {idx : Nat} {d : ConLeche.Frontend.DeclRec} {rec : LineRec}
    (h : lineEnd j0 ik idx (.decl d) = .ok rec j') : rec = .decl d := by
  simp only [lineEnd] at h; split at h
  · simp only [ScanRes.ok.injEq] at h; exact h.1.symm
  · simp at h

section
variable {F rb capD jN jL jE cap bufJ : Nat} {b : ByteArray}

/-- The `app` branch. -/
theorem brApp {β : Type} {k : StateD ⊕ RecordVerdict → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64} (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcA : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one))
    (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcT : ∀ k, k < 2 → C.code.lookup (fAppF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun appSpec appInits (vv (slotName k)), .one))
    (fL : MlS) (hcL : C.code.lookup fL =
      some (linePs.map (fun p => (p, ShapeHOL.one)), prologue binL (binLineP fInternApp fAppF), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hx : kR0 ∈ D) (st : StateD)
    (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (ws0 : BitVec 64) (pl : LinePayload) (hpl : PlOK b (BitVec.ofNat 64 7) ws0 pl) (j0 j' : USize) (ik : UInt8)
    (idx : Nat) (rec : LineRec) (hle : lineEnd j0 ik idx pl = .ok rec j') (n : Nat) (hn : n ≠ 0) (hi : idx < cap)
    (h1 : Γ.get fTN = some (cellA C jN)) (h2 : Γ.get fTL = some (cellA C jL)) (h3 : Γ.get fTE = some (cellA C jE))
    (h4 : Γ.get fCap = some (BitVec.ofNat 64 cap)) (h5 : Γ.get kIx = some (BitVec.ofNat 64 (min idx natCap)))
    (h6 : Γ.get kS0 = some ws0)
    (h7 : Γ.get kBA = some (cellA C bufJ)) (h8 : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (h9 : Γ.get kRB = some (cellA C rb)) (h10 : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hk : ∀ st' w s' H', FrontSt C F rb capD jN jL jE cap bufJ b H' st' →
      SpecR (Inv (ctxH C H') s' ((kR0, w) :: Γ) [] D) rest s' (k (.inl st')) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, kR0), none)) fL lineArgs) rest) s
      (applyLine st rec n >>= k) R := by
  obtain ⟨kk, a, hm, hta, he⟩ := plOK_tag (by decide) (by decide) hpl
  obtain rfl := tag_7 hm hta
  obtain ⟨v, e, r', hws, hsc', rfl⟩ := objPl (sc := ConLeche.Frontend.scanAppExpr) (wrap := LinePayload.expr) he
  subst hws
  rw [lineEnd_expr hle, applyLine_expr _ _ _ _ hn]
  simp only [bind_assoc, pure_bind]
  have hbuf : BufOK C bufJ b := by have := hfs.buf; rwa [ctxH_self] at this
  have hpos : v.toNat ≤ b.size := Nat.le_of_lt (start_lt hbuf.plat (by rw [ConLeche.Frontend.scanAppExpr] at hsc'; exact hsc'))
  exact specR_exLineCall kR0 fL binL _ lineArgs _ rfl hx hcL
    (evAll_lineArgs Γ C jN jL jE cap _ _ bufJ b.size rb capD h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    (binL_none C jN jL jE cap _ _ bufJ b.size rb capD) st idx r' hi hfs
    (appCore ra C hok hcA hsc hcT s st jN jL jE cap rb capD hfs.tE hfs.lay.cap8 bufJ b hbuf v e hpos r' hsc' idx)
    hk

end

section
variable {F rb capD jN jL jE cap bufJ : Nat} {b : ByteArray}

theorem brLam {β : Type} {k : StateD ⊕ RecordVerdict → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64} (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcA : C.code.lookup fInternLam = some ([(lEf, .one), (lEa, .one)], bin2Body lamDataE 14, .one)) (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcT : ∀ k, k < 2 → C.code.lookup (fLamF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanLamExprSpec lamInits (vv (slotName k)), .one))
    (fL : MlS) (hcL : C.code.lookup fL =
      some (linePs.map (fun p => (p, ShapeHOL.one)), prologue binL (binLineP fInternLam fLamF), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hx : kR0 ∈ D) (st : StateD)
    (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (ws0 : BitVec 64) (pl : LinePayload) (hpl : PlOK b (BitVec.ofNat 64 8) ws0 pl) (j0 j' : USize) (ik : UInt8)
    (idx : Nat) (rec : LineRec) (hle : lineEnd j0 ik idx pl = .ok rec j') (n : Nat) (hn : n ≠ 0) (hi : idx < cap)
    (h1 : Γ.get fTN = some (cellA C jN)) (h2 : Γ.get fTL = some (cellA C jL)) (h3 : Γ.get fTE = some (cellA C jE))
    (h4 : Γ.get fCap = some (BitVec.ofNat 64 cap)) (h5 : Γ.get kIx = some (BitVec.ofNat 64 (min idx natCap)))
    (h6 : Γ.get kS0 = some ws0)
    (h7 : Γ.get kBA = some (cellA C bufJ)) (h8 : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (h9 : Γ.get kRB = some (cellA C rb)) (h10 : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hk : ∀ st' w s' H', FrontSt C F rb capD jN jL jE cap bufJ b H' st' →
      SpecR (Inv (ctxH C H') s' ((kR0, w) :: Γ) [] D) rest s' (k (.inl st')) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, kR0), none)) fL lineArgs) rest) s
      (applyLine st rec n >>= k) R := by
  obtain ⟨kk, a, hm, hta, he⟩ := plOK_tag (by decide) (by decide) hpl
  obtain rfl := tag_8 hm hta
  obtain ⟨v, e, r', hws, hsc', rfl⟩ := objPl (sc := ConLeche.Frontend.scanLamExpr) (wrap := LinePayload.expr) he
  subst hws
  rw [lineEnd_expr hle, applyLine_expr _ _ _ _ hn]
  simp only [bind_assoc, pure_bind]
  have hbuf : BufOK C bufJ b := by have := hfs.buf; rwa [ctxH_self] at this
  have hpos : v.toNat ≤ b.size := Nat.le_of_lt (start_lt hbuf.plat (by rw [ConLeche.Frontend.scanLamExpr] at hsc'; exact hsc'))
  exact specR_exLineCall kR0 fL binL _ lineArgs _ rfl hx hcL
    (evAll_lineArgs Γ C jN jL jE cap _ _ bufJ b.size rb capD h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    (binL_none C jN jL jE cap _ _ bufJ b.size rb capD) st idx r' hi hfs
    (lamCore ra C hok hcA hsc hcT s st jN jL jE cap rb capD hfs.tE hfs.lay.cap8 bufJ b hbuf v e hpos r' hsc' idx)
    hk

theorem brAll {β : Type} {k : StateD ⊕ RecordVerdict → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64} (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcA : C.code.lookup fInternForallE = some ([(lEf, .one), (lEa, .one)], bin2Body forDataE 15, .one)) (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcT : ∀ k, k < 2 → C.code.lookup (fAllF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanForallExprSpec allInits (vv (slotName k)), .one))
    (fL : MlS) (hcL : C.code.lookup fL =
      some (linePs.map (fun p => (p, ShapeHOL.one)), prologue binL (binLineP fInternForallE fAllF), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hx : kR0 ∈ D) (st : StateD)
    (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (ws0 : BitVec 64) (pl : LinePayload) (hpl : PlOK b (BitVec.ofNat 64 9) ws0 pl) (j0 j' : USize) (ik : UInt8)
    (idx : Nat) (rec : LineRec) (hle : lineEnd j0 ik idx pl = .ok rec j') (n : Nat) (hn : n ≠ 0) (hi : idx < cap)
    (h1 : Γ.get fTN = some (cellA C jN)) (h2 : Γ.get fTL = some (cellA C jL)) (h3 : Γ.get fTE = some (cellA C jE))
    (h4 : Γ.get fCap = some (BitVec.ofNat 64 cap)) (h5 : Γ.get kIx = some (BitVec.ofNat 64 (min idx natCap)))
    (h6 : Γ.get kS0 = some ws0)
    (h7 : Γ.get kBA = some (cellA C bufJ)) (h8 : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (h9 : Γ.get kRB = some (cellA C rb)) (h10 : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hk : ∀ st' w s' H', FrontSt C F rb capD jN jL jE cap bufJ b H' st' →
      SpecR (Inv (ctxH C H') s' ((kR0, w) :: Γ) [] D) rest s' (k (.inl st')) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, kR0), none)) fL lineArgs) rest) s
      (applyLine st rec n >>= k) R := by
  obtain ⟨kk, a, hm, hta, he⟩ := plOK_tag (by decide) (by decide) hpl
  obtain rfl := tag_9 hm hta
  obtain ⟨v, e, r', hws, hsc', rfl⟩ := objPl (sc := ConLeche.Frontend.scanForallExpr) (wrap := LinePayload.expr) he
  subst hws
  rw [lineEnd_expr hle, applyLine_expr _ _ _ _ hn]
  simp only [bind_assoc, pure_bind]
  have hbuf : BufOK C bufJ b := by have := hfs.buf; rwa [ctxH_self] at this
  have hpos : v.toNat ≤ b.size := Nat.le_of_lt (start_lt hbuf.plat (by rw [ConLeche.Frontend.scanForallExpr] at hsc'; exact hsc'))
  exact specR_exLineCall kR0 fL binL _ lineArgs _ rfl hx hcL
    (evAll_lineArgs Γ C jN jL jE cap _ _ bufJ b.size rb capD h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    (binL_none C jN jL jE cap _ _ bufJ b.size rb capD) st idx r' hi hfs
    (allCore ra C hok hcA hsc hcT s st jN jL jE cap rb capD hfs.tE hfs.lay.cap8 bufJ b hbuf v e hpos r' hsc' idx)
    hk

theorem brLet {β : Type} {k : StateD ⊕ RecordVerdict → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64} (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcL0 : C.code.lookup fInternLet = some ([(lEty, .one), (lEvl, .one), (lEbd, .one)], letBody, .one)) (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcT : ∀ k, k < 3 → C.code.lookup (fLetF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanLetExprSpec letInits (vv (slotName k)), .one))
    (fL : MlS) (hcL : C.code.lookup fL =
      some (linePs.map (fun p => (p, ShapeHOL.one)), prologue letL (letLineP), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hx : kR0 ∈ D) (st : StateD)
    (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (ws0 : BitVec 64) (pl : LinePayload) (hpl : PlOK b (BitVec.ofNat 64 10) ws0 pl) (j0 j' : USize) (ik : UInt8)
    (idx : Nat) (rec : LineRec) (hle : lineEnd j0 ik idx pl = .ok rec j') (n : Nat) (hn : n ≠ 0) (hi : idx < cap)
    (h1 : Γ.get fTN = some (cellA C jN)) (h2 : Γ.get fTL = some (cellA C jL)) (h3 : Γ.get fTE = some (cellA C jE))
    (h4 : Γ.get fCap = some (BitVec.ofNat 64 cap)) (h5 : Γ.get kIx = some (BitVec.ofNat 64 (min idx natCap)))
    (h6 : Γ.get kS0 = some ws0)
    (h7 : Γ.get kBA = some (cellA C bufJ)) (h8 : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (h9 : Γ.get kRB = some (cellA C rb)) (h10 : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hk : ∀ st' w s' H', FrontSt C F rb capD jN jL jE cap bufJ b H' st' →
      SpecR (Inv (ctxH C H') s' ((kR0, w) :: Γ) [] D) rest s' (k (.inl st')) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, kR0), none)) fL lineArgs) rest) s
      (applyLine st rec n >>= k) R := by
  obtain ⟨kk, a, hm, hta, he⟩ := plOK_tag (by decide) (by decide) hpl
  obtain rfl := tag_10 hm hta
  obtain ⟨v, e, r', hws, hsc', rfl⟩ := objPl (sc := ConLeche.Frontend.scanLetExpr) (wrap := LinePayload.expr) he
  subst hws
  rw [lineEnd_expr hle, applyLine_expr _ _ _ _ hn]
  simp only [bind_assoc, pure_bind]
  have hbuf : BufOK C bufJ b := by have := hfs.buf; rwa [ctxH_self] at this
  have hpos : v.toNat ≤ b.size := Nat.le_of_lt (start_lt hbuf.plat (by rw [ConLeche.Frontend.scanLetExpr] at hsc'; exact hsc'))
  exact specR_exLineCall kR0 fL letL _ lineArgs _ rfl hx hcL
    (evAll_lineArgs Γ C jN jL jE cap _ _ bufJ b.size rb capD h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    (letL_none C jN jL jE cap _ _ bufJ b.size rb capD) st idx r' hi hfs
    (letCore ra C hok hcL0 hsc hcT s st jN jL jE cap rb capD hfs.tE hfs.lay.cap8 bufJ b hbuf v e hpos r' hsc' idx)
    hk

theorem brProj {β : Type} {k : StateD ⊕ RecordVerdict → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64} (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcP : C.code.lookup fInternProj = some ([(lEp, .one), (lEe, .one), (lIw, .one)], projBody, .one)) (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcT : ∀ k, k < 3 → C.code.lookup (fProjF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanProjExprSpec projInits (vv (slotName k)), .one))
    (fL : MlS) (hcL : C.code.lookup fL =
      some (linePs.map (fun p => (p, ShapeHOL.one)), prologue projL (projLineP), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hx : kR0 ∈ D) (st : StateD)
    (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (ws0 : BitVec 64) (pl : LinePayload) (hpl : PlOK b (BitVec.ofNat 64 12) ws0 pl) (j0 j' : USize) (ik : UInt8)
    (idx : Nat) (rec : LineRec) (hle : lineEnd j0 ik idx pl = .ok rec j') (n : Nat) (hn : n ≠ 0) (hi : idx < cap)
    (h1 : Γ.get fTN = some (cellA C jN)) (h2 : Γ.get fTL = some (cellA C jL)) (h3 : Γ.get fTE = some (cellA C jE))
    (h4 : Γ.get fCap = some (BitVec.ofNat 64 cap)) (h5 : Γ.get kIx = some (BitVec.ofNat 64 (min idx natCap)))
    (h6 : Γ.get kS0 = some ws0)
    (h7 : Γ.get kBA = some (cellA C bufJ)) (h8 : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (h9 : Γ.get kRB = some (cellA C rb)) (h10 : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hk : ∀ st' w s' H', FrontSt C F rb capD jN jL jE cap bufJ b H' st' →
      SpecR (Inv (ctxH C H') s' ((kR0, w) :: Γ) [] D) rest s' (k (.inl st')) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, kR0), none)) fL lineArgs) rest) s
      (applyLine st rec n >>= k) R := by
  obtain ⟨kk, a, hm, hta, he⟩ := plOK_tag (by decide) (by decide) hpl
  obtain rfl := tag_12 hm hta
  obtain ⟨v, e, r', hws, hsc', rfl⟩ := objPl (sc := ConLeche.Frontend.scanProjExpr) (wrap := LinePayload.expr) he
  subst hws
  rw [lineEnd_expr hle, applyLine_expr _ _ _ _ hn]
  simp only [bind_assoc, pure_bind]
  have hbuf : BufOK C bufJ b := by have := hfs.buf; rwa [ctxH_self] at this
  have hpos : v.toNat ≤ b.size := Nat.le_of_lt (start_lt hbuf.plat (by rw [ConLeche.Frontend.scanProjExpr] at hsc'; exact hsc'))
  exact specR_exLineCall kR0 fL projL _ lineArgs _ rfl hx hcL
    (evAll_lineArgs Γ C jN jL jE cap _ _ bufJ b.size rb capD h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    (projL_none C jN jL jE cap _ _ bufJ b.size rb capD) st idx r' hi hfs
    (projCore ra C hok hcP hsc hcT s st jN jL jE cap rb capD hfs.tE hfs.tN hfs.lay.cap8 bufJ b hbuf v e hpos r' hsc' idx)
    hk

theorem brConst {β : Type} {k : StateD ⊕ RecordVerdict → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64} (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hnc : ∀ t : PState σ, t.code = C.code → NnCodes t) (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t) (hcN : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one))
    (hcLs : C.code.lookup fInternLs = some ([(pKey, .one), (lEc, .one)], internLsBody, .one))
    (hcC : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one))
    (hcT : ∀ k, k < 2 → C.code.lookup (fConstF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanConstExprSpec constInits (vv (slotName k)), .one))
    (fL : MlS) (hcL : C.code.lookup fL =
      some (linePs.map (fun p => (p, ShapeHOL.one)), prologue constL (constLineP C), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hx : kR0 ∈ D) (st : StateD)
    (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (ws0 : BitVec 64) (pl : LinePayload) (hpl : PlOK b (BitVec.ofNat 64 11) ws0 pl) (j0 j' : USize) (ik : UInt8)
    (idx : Nat) (rec : LineRec) (hle : lineEnd j0 ik idx pl = .ok rec j') (n : Nat) (hn : n ≠ 0) (hi : idx < cap)
    (h1 : Γ.get fTN = some (cellA C jN)) (h2 : Γ.get fTL = some (cellA C jL)) (h3 : Γ.get fTE = some (cellA C jE))
    (h4 : Γ.get fCap = some (BitVec.ofNat 64 cap)) (h5 : Γ.get kIx = some (BitVec.ofNat 64 (min idx natCap)))
    (h6 : Γ.get kS0 = some ws0)
    (h7 : Γ.get kBA = some (cellA C bufJ)) (h8 : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (h9 : Γ.get kRB = some (cellA C rb)) (h10 : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hk : ∀ st' w s' H', FrontSt C F rb capD jN jL jE cap bufJ b H' st' →
      SpecR (Inv (ctxH C H') s' ((kR0, w) :: Γ) [] D) rest s' (k (.inl st')) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, kR0), none)) fL lineArgs) rest) s
      (applyLine st rec n >>= k) R := by
  obtain ⟨kk, a, hm, hta, he⟩ := plOK_tag (by decide) (by decide) hpl
  obtain rfl := tag_11 hm hta
  obtain ⟨v, e, r', hws, hsc', rfl⟩ := objPl (sc := ConLeche.Frontend.scanConstExpr) (wrap := LinePayload.expr) he
  subst hws
  rw [lineEnd_expr hle, applyLine_expr _ _ _ _ hn]
  simp only [bind_assoc, pure_bind]
  have hbuf : BufOK C bufJ b := by have := hfs.buf; rwa [ctxH_self] at this
  have hpos : v.toNat ≤ b.size := Nat.le_of_lt (start_lt hbuf.plat (by rw [ConLeche.Frontend.scanConstExpr] at hsc'; exact hsc'))
  exact specR_exLineCall kR0 fL constL _ lineArgs _ rfl hx hcL
    (evAll_lineArgs Γ C jN jL jE cap _ _ bufJ b.size rb capD h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    (constL_none C jN jL jE cap _ _ bufJ b.size rb capD) st idx r' hi hfs
    (constCore ra C hok hnc hsc hcN hcLs hcC hcT s st jN jL jE cap rb capD hfs.tE hfs.tL hfs.tN hfs.lay.cap8 hfs.lay.capN bufJ b hbuf v e hpos r' hsc' idx)
    hk

theorem brNum {β : Type} {k : StateD ⊕ RecordVerdict → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64} (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : FrontOK C)
    (hcN0 : C.code.lookup fInternNNum = some ([(pKeyN, .one), (lEn, .one), (lEp, .one), (lNw, .one)], nameNumBody, .one)) (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcT : ∀ k, k < 2 → C.code.lookup (fNumF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanNumNameSpec numInits (vv (slotName k)), .one))
    (fL : MlS) (hcL : C.code.lookup fL =
      some (linePs.map (fun p => (p, ShapeHOL.one)), prologue numL (numLineP C), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hx : kR0 ∈ D) (st : StateD)
    (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (ws0 : BitVec 64) (pl : LinePayload) (hpl : PlOK b (BitVec.ofNat 64 6) ws0 pl) (j0 j' : USize) (ik : UInt8)
    (idx : Nat) (rec : LineRec) (hle : lineEnd j0 ik idx pl = .ok rec j') (n : Nat) (hn : n ≠ 0) (hi : idx < cap)
    (h1 : Γ.get fTN = some (cellA C jN)) (h2 : Γ.get fTL = some (cellA C jL)) (h3 : Γ.get fTE = some (cellA C jE))
    (h4 : Γ.get fCap = some (BitVec.ofNat 64 cap)) (h5 : Γ.get kIx = some (BitVec.ofNat 64 (min idx natCap)))
    (h6 : Γ.get kS0 = some ws0)
    (h7 : Γ.get kBA = some (cellA C bufJ)) (h8 : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (h9 : Γ.get kRB = some (cellA C rb)) (h10 : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hk : ∀ st' w s' H', FrontSt C F rb capD jN jL jE cap bufJ b H' st' →
      SpecR (Inv (ctxH C H') s' ((kR0, w) :: Γ) [] D) rest s' (k (.inl st')) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, kR0), none)) fL lineArgs) rest) s
      (applyLine st rec n >>= k) R := by
  obtain ⟨kk, a, hm, hta, he⟩ := plOK_tag (by decide) (by decide) hpl
  obtain rfl := tag_6 hm hta
  obtain ⟨v, e, r', hws, hsc', rfl⟩ := objPl (sc := ConLeche.Frontend.scanNumName) (wrap := LinePayload.name) he
  subst hws
  rw [lineEnd_name hle, applyLine_name _ _ _ _ hn]
  simp only [bind_assoc, pure_bind]
  have hbuf : BufOK C bufJ b := by have := hfs.buf; rwa [ctxH_self] at this
  have hpos : v.toNat ≤ b.size := Nat.le_of_lt (start_lt hbuf.plat (by rw [ConLeche.Frontend.scanNumName] at hsc'; exact hsc'))
  exact specR_nmLineCall kR0 fL numL _ lineArgs _ rfl hx hcL
    (evAll_lineArgs Γ C jN jL jE cap _ _ bufJ b.size rb capD h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    (numL_none C jN jL jE cap _ _ bufJ b.size rb capD) st idx r' hi hfs
    (numCore ra C hok hf hcN0 hsc hcT s st jN jL jE cap rb capD hfs.tN hfs.lay.cap8 bufJ b hbuf v e hpos r' hsc' idx)
    hk

theorem brStr {β : Type} {k : StateD ⊕ RecordVerdict → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64} (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : FrontOK C)
    (hcN0 : C.code.lookup fInternNStr = some ([(pKeyN, .one), (lEn, .one), (lEp, .one), (lHn, .one)], nameStrBody, .one)) (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcS : C.code.lookup fStr = some ([(sB, .one), (sN, .one), (sI, .one)], ssFun, .one))
    (hcT : ∀ k, k < 2 → C.code.lookup (fStrF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanStrNameSpec strInits (vv (slotName k)), .one))
    (fL : MlS) (hcL : C.code.lookup fL =
      some (linePs.map (fun p => (p, ShapeHOL.one)), prologue strL (strLineP C), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hx : kR0 ∈ D) (st : StateD)
    (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (ws0 : BitVec 64) (pl : LinePayload) (hpl : PlOK b (BitVec.ofNat 64 5) ws0 pl) (j0 j' : USize) (ik : UInt8)
    (idx : Nat) (rec : LineRec) (hle : lineEnd j0 ik idx pl = .ok rec j') (n : Nat) (hn : n ≠ 0) (hi : idx < cap)
    (h1 : Γ.get fTN = some (cellA C jN)) (h2 : Γ.get fTL = some (cellA C jL)) (h3 : Γ.get fTE = some (cellA C jE))
    (h4 : Γ.get fCap = some (BitVec.ofNat 64 cap)) (h5 : Γ.get kIx = some (BitVec.ofNat 64 (min idx natCap)))
    (h6 : Γ.get kS0 = some ws0)
    (h7 : Γ.get kBA = some (cellA C bufJ)) (h8 : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (h9 : Γ.get kRB = some (cellA C rb)) (h10 : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hk : ∀ st' w s' H', FrontSt C F rb capD jN jL jE cap bufJ b H' st' →
      SpecR (Inv (ctxH C H') s' ((kR0, w) :: Γ) [] D) rest s' (k (.inl st')) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, kR0), none)) fL lineArgs) rest) s
      (applyLine st rec n >>= k) R := by
  obtain ⟨kk, a, hm, hta, he⟩ := plOK_tag (by decide) (by decide) hpl
  obtain rfl := tag_5 hm hta
  obtain ⟨v, e, r', hws, hsc', rfl⟩ := objPl (sc := ConLeche.Frontend.scanStrName) (wrap := LinePayload.name) he
  subst hws
  rw [lineEnd_name hle, applyLine_name _ _ _ _ hn]
  simp only [bind_assoc, pure_bind]
  have hbuf : BufOK C bufJ b := by have := hfs.buf; rwa [ctxH_self] at this
  have hpos : v.toNat ≤ b.size := Nat.le_of_lt (start_lt hbuf.plat (by rw [ConLeche.Frontend.scanStrName] at hsc'; exact hsc'))
  exact specR_nmLineCall kR0 fL strL _ lineArgs _ rfl hx hcL
    (evAll_lineArgs Γ C jN jL jE cap _ _ bufJ b.size rb capD h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    (strL_none C jN jL jE cap _ _ bufJ b.size rb capD) st idx r' hi hfs
    (strCore ra C hok hf hcN0 hsc hcS hcT s st jN jL jE cap rb capD hfs.tN hfs.lay.cap8 bufJ b hbuf v e hpos r' hsc' idx)
    hk

end


section
variable {F rb capD jN jL jE cap bufJ : Nat} {b : ByteArray}

theorem brThm {β : Type} {k : StateD ⊕ RecordVerdict → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64} (C : Ctx) (hok : CtxOK C) (hnc : ∀ t : PState σ, t.code = C.code → NnCodes t) (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t) (hcN : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one))
    (hcT : ∀ k, k < 4 → C.code.lookup (fThmF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanThmDeclSpec thmInits (vv (slotName k)), .one))
    (fL : MlS) (hcL : C.code.lookup fL =
      some (linePs.map (fun p => (p, ShapeHOL.one)), prologue thL (thLineP C), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hx : kR0 ∈ D) (st : StateD)
    (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (ws0 : BitVec 64) (pl : LinePayload) (hpl : PlOK b (BitVec.ofNat 64 15) ws0 pl) (j0 j' : USize) (ik : UInt8)
    (idx : Nat) (rec : LineRec) (hle : lineEnd j0 ik idx pl = .ok rec j') (n : Nat) (hn : n ≠ 0)
    (h1 : Γ.get fTN = some (cellA C jN)) (h2 : Γ.get fTL = some (cellA C jL)) (h3 : Γ.get fTE = some (cellA C jE))
    (h4 : Γ.get fCap = some (BitVec.ofNat 64 cap)) (h5 : Γ.get kIx = some (BitVec.ofNat 64 (min idx natCap)))
    (h6 : Γ.get kS0 = some ws0)
    (h7 : Γ.get kBA = some (cellA C bufJ)) (h8 : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (h9 : Γ.get kRB = some (cellA C rb)) (h10 : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hk : ∀ st' w s' H', FrontSt C F rb capD jN jL jE cap bufJ b H' st' →
      SpecR (Inv (ctxH C H') s' ((kR0, w) :: Γ) [] D) rest s' (k (.inl st')) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, kR0), none)) fL lineArgs) rest) s
      (applyLine st rec n >>= k) R := by
  obtain ⟨kk, a, hm, hta, he⟩ := plOK_tag (by decide) (by decide) hpl
  obtain rfl := tag_15 hm hta
  obtain ⟨v, e, r', hws, hsc', rfl⟩ := objPl (sc := ConLeche.Frontend.scanThmDecl) (wrap := LinePayload.decl) he
  subst hws
  rw [lineEnd_decl hle, applyLine_decl _ _ _ hn]
  have hbuf : BufOK C bufJ b := by have := hfs.buf; rwa [ctxH_self] at this
  have hpos : v.toNat ≤ b.size := Nat.le_of_lt (start_lt hbuf.plat (by rw [ConLeche.Frontend.scanThmDecl] at hsc'; exact hsc'))
  exact specR_dcLineCall kR0 fL thL _ lineArgs _ rfl hx hcL
    (evAll_lineArgs Γ C jN jL jE cap _ _ bufJ b.size rb capD h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    (thL_none C jN jL jE cap _ _ bufJ b.size rb capD) st r' hfs
    (thCore C hok hnc hsc hcN hcT s st F rb capD jN jL jE cap bufJ b hfs.lay.fl hfs.tN hfs.tE hfs.lay.cap8 hfs.lay.capN hbuf hfs.dr
      hfs.lay.capD8 v e hpos r' hsc' idx)
    hk

theorem brOpq {β : Type} {k : StateD ⊕ RecordVerdict → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64} (C : Ctx) (hok : CtxOK C) (hnc : ∀ t : PState σ, t.code = C.code → NnCodes t) (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t) (hcN : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one))
    (hcT : ∀ k, k < 5 → C.code.lookup (fOpqF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanOpaqueDeclSpec opqInits (vv (slotName k)), .one))
    (fL : MlS) (hcL : C.code.lookup fL =
      some (linePs.map (fun p => (p, ShapeHOL.one)), prologue opL (opLineP C), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hx : kR0 ∈ D) (st : StateD)
    (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (ws0 : BitVec 64) (pl : LinePayload) (hpl : PlOK b (BitVec.ofNat 64 16) ws0 pl) (j0 j' : USize) (ik : UInt8)
    (idx : Nat) (rec : LineRec) (hle : lineEnd j0 ik idx pl = .ok rec j') (n : Nat) (hn : n ≠ 0)
    (h1 : Γ.get fTN = some (cellA C jN)) (h2 : Γ.get fTL = some (cellA C jL)) (h3 : Γ.get fTE = some (cellA C jE))
    (h4 : Γ.get fCap = some (BitVec.ofNat 64 cap)) (h5 : Γ.get kIx = some (BitVec.ofNat 64 (min idx natCap)))
    (h6 : Γ.get kS0 = some ws0)
    (h7 : Γ.get kBA = some (cellA C bufJ)) (h8 : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (h9 : Γ.get kRB = some (cellA C rb)) (h10 : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hk : ∀ st' w s' H', FrontSt C F rb capD jN jL jE cap bufJ b H' st' →
      SpecR (Inv (ctxH C H') s' ((kR0, w) :: Γ) [] D) rest s' (k (.inl st')) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, kR0), none)) fL lineArgs) rest) s
      (applyLine st rec n >>= k) R := by
  obtain ⟨kk, a, hm, hta, he⟩ := plOK_tag (by decide) (by decide) hpl
  obtain rfl := tag_16 hm hta
  obtain ⟨v, e, r', hws, hsc', rfl⟩ := objPl (sc := ConLeche.Frontend.scanOpaqueDecl) (wrap := LinePayload.decl) he
  subst hws
  rw [lineEnd_decl hle, applyLine_decl _ _ _ hn]
  have hbuf : BufOK C bufJ b := by have := hfs.buf; rwa [ctxH_self] at this
  have hpos : v.toNat ≤ b.size := Nat.le_of_lt (start_lt hbuf.plat (by rw [ConLeche.Frontend.scanOpaqueDecl] at hsc'; exact hsc'))
  exact specR_dcLineCall kR0 fL opL _ lineArgs _ rfl hx hcL
    (evAll_lineArgs Γ C jN jL jE cap _ _ bufJ b.size rb capD h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    (opL_none C jN jL jE cap _ _ bufJ b.size rb capD) st r' hfs
    (opCore C hok hnc hsc hcN hcT s st F rb capD jN jL jE cap bufJ b hfs.lay.fl hfs.tN hfs.tE hfs.lay.cap8 hfs.lay.capN hbuf hfs.dr
      hfs.lay.capD8 v e hpos r' hsc' idx)
    hk

theorem brDef {β : Type} {k : StateD ⊕ RecordVerdict → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64} (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hnc : ∀ t : PState σ, t.code = C.code → NnCodes t) (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t) (hcN : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one))
    (hcS : C.code.lookup fSafe = some ([(sB, .one), (sN, .one), (sI, .one)], sfFun, .one))
    (hcH : C.code.lookup fHintV = some ([(sB, .one), (sN, .one), (sI, .one)], hvFun, .one))
    (hhc : ∀ t : PState σ, t.code = C.code → HvCodes t)
    (hcT : ∀ k, k < 6 → C.code.lookup (fDefF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanDefDeclSpec defInits (vv (slotName k)), .one))
    (fL : MlS) (hcL : C.code.lookup fL =
      some (linePs.map (fun p => (p, ShapeHOL.one)), prologue dfL (dfLineP C), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hx : kR0 ∈ D) (st : StateD)
    (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (ws0 : BitVec 64) (pl : LinePayload) (hpl : PlOK b (BitVec.ofNat 64 14) ws0 pl) (j0 j' : USize) (ik : UInt8)
    (idx : Nat) (rec : LineRec) (hle : lineEnd j0 ik idx pl = .ok rec j') (n : Nat) (hn : n ≠ 0)
    (h1 : Γ.get fTN = some (cellA C jN)) (h2 : Γ.get fTL = some (cellA C jL)) (h3 : Γ.get fTE = some (cellA C jE))
    (h4 : Γ.get fCap = some (BitVec.ofNat 64 cap)) (h5 : Γ.get kIx = some (BitVec.ofNat 64 (min idx natCap)))
    (h6 : Γ.get kS0 = some ws0)
    (h7 : Γ.get kBA = some (cellA C bufJ)) (h8 : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (h9 : Γ.get kRB = some (cellA C rb)) (h10 : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hk : ∀ st' w s' H', FrontSt C F rb capD jN jL jE cap bufJ b H' st' →
      SpecR (Inv (ctxH C H') s' ((kR0, w) :: Γ) [] D) rest s' (k (.inl st')) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, kR0), none)) fL lineArgs) rest) s
      (applyLine st rec n >>= k) R := by
  obtain ⟨kk, a, hm, hta, he⟩ := plOK_tag (by decide) (by decide) hpl
  obtain rfl := tag_14 hm hta
  obtain ⟨v, e, r', hws, hsc', rfl⟩ := objPl (sc := ConLeche.Frontend.scanDefDecl) (wrap := LinePayload.decl) he
  subst hws
  rw [lineEnd_decl hle, applyLine_decl _ _ _ hn]
  have hbuf : BufOK C bufJ b := by have := hfs.buf; rwa [ctxH_self] at this
  have hpos : v.toNat ≤ b.size := Nat.le_of_lt (start_lt hbuf.plat (by rw [ConLeche.Frontend.scanDefDecl] at hsc'; exact hsc'))
  exact specR_dcLineCall kR0 fL dfL _ lineArgs _ rfl hx hcL
    (evAll_lineArgs Γ C jN jL jE cap _ _ bufJ b.size rb capD h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    (dfL_none C jN jL jE cap _ _ bufJ b.size rb capD) st r' hfs
    (dfCore ra C hok hnc hsc hcN hcS hcH hhc hcT s st F rb capD jN jL jE cap bufJ b hfs.lay.fl hfs.tN hfs.tE hfs.lay.cap8 hfs.lay.capN hbuf hfs.dr
      hfs.lay.capD8 v e hpos r' hsc' idx)
    hk

end


section
variable {F rb capD jN jL jE cap bufJ : Nat} {b : ByteArray}

theorem brBVar {β : Type} {k : StateD ⊕ RecordVerdict → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64} (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcB : C.code.lookup fInternBVar = some ([(lIw, .one)], bvarBody, .one))
    (fL : MlS) (hcL : C.code.lookup fL =
      some (linePs.map (fun p => (p, ShapeHOL.one)), prologue natL (natLineP exBVarP), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hx : kR0 ∈ D) (st : StateD)
    (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (ws0 : BitVec 64) (pl : LinePayload) (hpl : PlOK b (BitVec.ofNat 64 1) ws0 pl) (j0 j' : USize) (ik : UInt8)
    (idx : Nat) (rec : LineRec) (hle : lineEnd j0 ik idx pl = .ok rec j') (n : Nat) (hn : n ≠ 0) (hi : idx < cap)
    (h1 : Γ.get fTN = some (cellA C jN)) (h2 : Γ.get fTL = some (cellA C jL)) (h3 : Γ.get fTE = some (cellA C jE))
    (h4 : Γ.get fCap = some (BitVec.ofNat 64 cap)) (h5 : Γ.get kIx = some (BitVec.ofNat 64 (min idx natCap)))
    (h6 : Γ.get kS0 = some ws0)
    (h7 : Γ.get kBA = some (cellA C bufJ)) (h8 : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (h9 : Γ.get kRB = some (cellA C rb)) (h10 : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hk : ∀ st' w s' H', FrontSt C F rb capD jN jL jE cap bufJ b H' st' →
      SpecR (Inv (ctxH C H') s' ((kR0, w) :: Γ) [] D) rest s' (k (.inl st')) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, kR0), none)) fL lineArgs) rest) s
      (applyLine st rec n >>= k) R := by
  obtain ⟨kk, a, hm, hta, he⟩ := plOK_tag (by decide) (by decide) hpl
  obtain rfl := tag_1 hm hta
  obtain ⟨-, u, rfl, rfl⟩ := he
  rw [lineEnd_expr hle, applyLine_expr _ _ _ _ hn]
  simp only [bind_assoc, pure_bind]
  exact specR_exLineCall kR0 fL natL _ lineArgs _ rfl hx hcL
    (evAll_lineArgs Γ C jN jL jE cap _ _ bufJ b.size rb capD h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    (natL_none C jN jL jE cap _ _ bufJ b.size rb capD) st idx _ hi hfs
    (bvarCore ra C hok hcB s st jN jL jE cap rb capD hfs.tE hfs.lay.cap8 bufJ b.size idx u)
    hk

theorem brSort {β : Type} {k : StateD ⊕ RecordVerdict → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64} (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcS : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one))
    (fL : MlS) (hcL : C.code.lookup fL =
      some (linePs.map (fun p => (p, ShapeHOL.one)), prologue natL (natLineP exSortP), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hx : kR0 ∈ D) (st : StateD)
    (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (ws0 : BitVec 64) (pl : LinePayload) (hpl : PlOK b (BitVec.ofNat 64 2) ws0 pl) (j0 j' : USize) (ik : UInt8)
    (idx : Nat) (rec : LineRec) (hle : lineEnd j0 ik idx pl = .ok rec j') (n : Nat) (hn : n ≠ 0) (hi : idx < cap)
    (h1 : Γ.get fTN = some (cellA C jN)) (h2 : Γ.get fTL = some (cellA C jL)) (h3 : Γ.get fTE = some (cellA C jE))
    (h4 : Γ.get fCap = some (BitVec.ofNat 64 cap)) (h5 : Γ.get kIx = some (BitVec.ofNat 64 (min idx natCap)))
    (h6 : Γ.get kS0 = some ws0)
    (h7 : Γ.get kBA = some (cellA C bufJ)) (h8 : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (h9 : Γ.get kRB = some (cellA C rb)) (h10 : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hk : ∀ st' w s' H', FrontSt C F rb capD jN jL jE cap bufJ b H' st' →
      SpecR (Inv (ctxH C H') s' ((kR0, w) :: Γ) [] D) rest s' (k (.inl st')) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, kR0), none)) fL lineArgs) rest) s
      (applyLine st rec n >>= k) R := by
  obtain ⟨kk, a, hm, hta, he⟩ := plOK_tag (by decide) (by decide) hpl
  obtain rfl := tag_2 hm hta
  obtain ⟨-, u, rfl, rfl⟩ := he
  rw [lineEnd_expr hle, applyLine_expr _ _ _ _ hn]
  simp only [bind_assoc, pure_bind]
  exact specR_exLineCall kR0 fL natL _ lineArgs _ rfl hx hcL
    (evAll_lineArgs Γ C jN jL jE cap _ _ bufJ b.size rb capD h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    (natL_none C jN jL jE cap _ _ bufJ b.size rb capD) st idx _ hi hfs
    (sortCore ra C hok hcS s st jN jL jE cap rb capD hfs.tE hfs.tL hfs.lay.cap8 bufJ b.size idx u)
    hk

theorem brSucc {β : Type} {k : StateD ⊕ RecordVerdict → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64} (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcS : C.code.lookup fInternLSucc = some ([(lEu, .one)], internLSuccBody, .one))
    (fL : MlS) (hcL : C.code.lookup fL =
      some (linePs.map (fun p => (p, ShapeHOL.one)), prologue natL (natLineP lvSuccP), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hx : kR0 ∈ D) (st : StateD)
    (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (ws0 : BitVec 64) (pl : LinePayload) (hpl : PlOK b (BitVec.ofNat 64 3) ws0 pl) (j0 j' : USize) (ik : UInt8)
    (idx : Nat) (rec : LineRec) (hle : lineEnd j0 ik idx pl = .ok rec j') (n : Nat) (hn : n ≠ 0) (hi : idx < cap)
    (h1 : Γ.get fTN = some (cellA C jN)) (h2 : Γ.get fTL = some (cellA C jL)) (h3 : Γ.get fTE = some (cellA C jE))
    (h4 : Γ.get fCap = some (BitVec.ofNat 64 cap)) (h5 : Γ.get kIx = some (BitVec.ofNat 64 (min idx natCap)))
    (h6 : Γ.get kS0 = some ws0)
    (h7 : Γ.get kBA = some (cellA C bufJ)) (h8 : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (h9 : Γ.get kRB = some (cellA C rb)) (h10 : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hk : ∀ st' w s' H', FrontSt C F rb capD jN jL jE cap bufJ b H' st' →
      SpecR (Inv (ctxH C H') s' ((kR0, w) :: Γ) [] D) rest s' (k (.inl st')) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, kR0), none)) fL lineArgs) rest) s
      (applyLine st rec n >>= k) R := by
  obtain ⟨kk, a, hm, hta, he⟩ := plOK_tag (by decide) (by decide) hpl
  obtain rfl := tag_3 hm hta
  obtain ⟨-, u, rfl, rfl⟩ := he
  rw [lineEnd_level hle, applyLine_level _ _ _ _ hn]
  simp only [bind_assoc, pure_bind]
  exact specR_lvLineCall kR0 fL natL _ lineArgs _ rfl hx hcL
    (evAll_lineArgs Γ C jN jL jE cap _ _ bufJ b.size rb capD h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    (natL_none C jN jL jE cap _ _ bufJ b.size rb capD) st idx _ hi hfs
    (succCore ra C hok hcS s st jN jL jE cap rb capD hfs.tL hfs.lay.cap8 bufJ b.size idx u)
    hk

theorem brParam {β : Type} {k : StateD ⊕ RecordVerdict → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64} (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcP : C.code.lookup fInternLParam = some ([(lEn, .one)], internLParamBody, .one))
    (fL : MlS) (hcL : C.code.lookup fL =
      some (linePs.map (fun p => (p, ShapeHOL.one)), prologue natL (natLineP lvParamP), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hx : kR0 ∈ D) (st : StateD)
    (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (ws0 : BitVec 64) (pl : LinePayload) (hpl : PlOK b (BitVec.ofNat 64 4) ws0 pl) (j0 j' : USize) (ik : UInt8)
    (idx : Nat) (rec : LineRec) (hle : lineEnd j0 ik idx pl = .ok rec j') (n : Nat) (hn : n ≠ 0) (hi : idx < cap)
    (h1 : Γ.get fTN = some (cellA C jN)) (h2 : Γ.get fTL = some (cellA C jL)) (h3 : Γ.get fTE = some (cellA C jE))
    (h4 : Γ.get fCap = some (BitVec.ofNat 64 cap)) (h5 : Γ.get kIx = some (BitVec.ofNat 64 (min idx natCap)))
    (h6 : Γ.get kS0 = some ws0)
    (h7 : Γ.get kBA = some (cellA C bufJ)) (h8 : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (h9 : Γ.get kRB = some (cellA C rb)) (h10 : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hk : ∀ st' w s' H', FrontSt C F rb capD jN jL jE cap bufJ b H' st' →
      SpecR (Inv (ctxH C H') s' ((kR0, w) :: Γ) [] D) rest s' (k (.inl st')) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, kR0), none)) fL lineArgs) rest) s
      (applyLine st rec n >>= k) R := by
  obtain ⟨kk, a, hm, hta, he⟩ := plOK_tag (by decide) (by decide) hpl
  obtain rfl := tag_4 hm hta
  obtain ⟨-, u, rfl, rfl⟩ := he
  rw [lineEnd_level hle, applyLine_level _ _ _ _ hn]
  simp only [bind_assoc, pure_bind]
  exact specR_lvLineCall kR0 fL natL _ lineArgs _ rfl hx hcL
    (evAll_lineArgs Γ C jN jL jE cap _ _ bufJ b.size rb capD h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    (natL_none C jN jL jE cap _ _ bufJ b.size rb capD) st idx _ hi hfs
    (paramCore ra C hok hcP s st jN jL jE cap rb capD hfs.tL hfs.tN hfs.lay.cap8 bufJ b.size idx u)
    hk

theorem brMax {β : Type} {k : StateD ⊕ RecordVerdict → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64} (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hnc : ∀ t : PState σ, t.code = C.code → NnCodes t) (hcN : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one))
    (hcM : C.code.lookup fInternLMax = some ([(lEu, .one), (lEv, .one)], internLMaxBody, .one))
    (fL : MlS) (hcL : C.code.lookup fL =
      some (linePs.map (fun p => (p, ShapeHOL.one)), prologue pairL (lvPairLineP fInternLMax), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hx : kR0 ∈ D) (st : StateD)
    (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (ws0 : BitVec 64) (pl : LinePayload) (hpl : PlOK b (BitVec.ofNat 64 18) ws0 pl) (j0 j' : USize) (ik : UInt8)
    (idx : Nat) (rec : LineRec) (hle : lineEnd j0 ik idx pl = .ok rec j') (n : Nat) (hn : n ≠ 0) (hi : idx < cap)
    (h1 : Γ.get fTN = some (cellA C jN)) (h2 : Γ.get fTL = some (cellA C jL)) (h3 : Γ.get fTE = some (cellA C jE))
    (h4 : Γ.get fCap = some (BitVec.ofNat 64 cap)) (h5 : Γ.get kIx = some (BitVec.ofNat 64 (min idx natCap)))
    (h6 : Γ.get kS0 = some ws0)
    (h7 : Γ.get kBA = some (cellA C bufJ)) (h8 : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (h9 : Γ.get kRB = some (cellA C rb)) (h10 : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hk : ∀ st' w s' H', FrontSt C F rb capD jN jL jE cap bufJ b H' st' →
      SpecR (Inv (ctxH C H') s' ((kR0, w) :: Γ) [] D) rest s' (k (.inl st')) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, kR0), none)) fL lineArgs) rest) s
      (applyLine st rec n >>= k) R := by
  obtain ⟨kk, a, hm, hta, he⟩ := plOK_tag (by decide) (by decide) hpl
  obtain rfl := tag_18 hm hta
  obtain ⟨-, v, e, hs0, rfl⟩ := he
  obtain ⟨x, y, rfl, hs⟩ := levMax_ok hs0
  rw [lineEnd_level hle, applyLine_level _ _ _ _ hn]
  simp only [bind_assoc, pure_bind]
  have hbuf : BufOK C bufJ b := by have := hfs.buf; rwa [ctxH_self] at this
  exact specR_lvLineCall kR0 fL pairL _ lineArgs _ rfl hx hcL
    (evAll_lineArgs Γ C jN jL jE cap _ _ bufJ b.size rb capD h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    (pairL_none C jN jL jE cap _ _ bufJ b.size rb capD) st idx _ hi hfs
    (maxCore ra C hok hnc hcN hcM s st jN jL jE cap rb capD hfs.tL hfs.lay.cap8 bufJ b hbuf v e x y idx hs)
    hk

theorem brImax {β : Type} {k : StateD ⊕ RecordVerdict → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64} (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hnc : ∀ t : PState σ, t.code = C.code → NnCodes t) (hcN : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one))
    (hcM : C.code.lookup fInternLImax = some ([(lEu, .one), (lEv, .one)], internLImaxBody, .one))
    (fL : MlS) (hcL : C.code.lookup fL =
      some (linePs.map (fun p => (p, ShapeHOL.one)), prologue pairL (lvPairLineP fInternLImax), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hx : kR0 ∈ D) (st : StateD)
    (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (ws0 : BitVec 64) (pl : LinePayload) (hpl : PlOK b (BitVec.ofNat 64 19) ws0 pl) (j0 j' : USize) (ik : UInt8)
    (idx : Nat) (rec : LineRec) (hle : lineEnd j0 ik idx pl = .ok rec j') (n : Nat) (hn : n ≠ 0) (hi : idx < cap)
    (h1 : Γ.get fTN = some (cellA C jN)) (h2 : Γ.get fTL = some (cellA C jL)) (h3 : Γ.get fTE = some (cellA C jE))
    (h4 : Γ.get fCap = some (BitVec.ofNat 64 cap)) (h5 : Γ.get kIx = some (BitVec.ofNat 64 (min idx natCap)))
    (h6 : Γ.get kS0 = some ws0)
    (h7 : Γ.get kBA = some (cellA C bufJ)) (h8 : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (h9 : Γ.get kRB = some (cellA C rb)) (h10 : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hk : ∀ st' w s' H', FrontSt C F rb capD jN jL jE cap bufJ b H' st' →
      SpecR (Inv (ctxH C H') s' ((kR0, w) :: Γ) [] D) rest s' (k (.inl st')) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, kR0), none)) fL lineArgs) rest) s
      (applyLine st rec n >>= k) R := by
  obtain ⟨kk, a, hm, hta, he⟩ := plOK_tag (by decide) (by decide) hpl
  obtain rfl := tag_19 hm hta
  obtain ⟨-, v, e, hs0, rfl⟩ := he
  obtain ⟨x, y, rfl, hs⟩ := levImax_ok hs0
  rw [lineEnd_level hle, applyLine_level _ _ _ _ hn]
  simp only [bind_assoc, pure_bind]
  have hbuf : BufOK C bufJ b := by have := hfs.buf; rwa [ctxH_self] at this
  exact specR_lvLineCall kR0 fL pairL _ lineArgs _ rfl hx hcL
    (evAll_lineArgs Γ C jN jL jE cap _ _ bufJ b.size rb capD h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    (pairL_none C jN jL jE cap _ _ bufJ b.size rb capD) st idx _ hi hfs
    (imaxCore ra C hok hnc hcN hcM s st jN jL jE cap rb capD hfs.tL hfs.lay.cap8 bufJ b hbuf v e x y idx hs)
    hk

end


end ConPanqueque.Front
