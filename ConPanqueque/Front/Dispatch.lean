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

end ConPanqueque.Front
