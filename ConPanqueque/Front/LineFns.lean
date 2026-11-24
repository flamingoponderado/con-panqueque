import ConPanqueque.Front.Tags

/-! # The line functions' cores at their entry environment

A line function is entered with `linePs` bound to `lineVs …`; `prologue` adds the context.  Each
core lemma is a line procedure's rule at that environment, the parameter `fU` (assigned by the
procedure) declared through `specR_declAdd`. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (ExprRec LevelRec NameRec)

variable {σ : Type}

/-- A local the environment binds may be declared. -/
theorem specR_declAdd {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {c : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (v : BitVec 64) (hx : Γ.get x = some v)
    (h : SpecR (Inv C s Γ M (x :: D)) c s m R) : SpecR (Inv C s Γ M D) c s m R :=
  fun t ht => h t ⟨ht.sr, ht.env, ht.mem, fun y hy => by
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨v, ht.env y v hx⟩
    · exact ht.decl y hy⟩

/-- The line functions' arguments. -/
def lineVs (C : Ctx) (jN jL jE cap : Nat) (wi ws0 : BitVec 64) (bufJ bsz rb capD : Nat) : List (BitVec 64) :=
  [cellA C jN, cellA C jL, cellA C jE, BitVec.ofNat 64 cap, wi, ws0, ws0, cellA C bufJ, BitVec.ofNat 64 bsz,
    cellA C rb, BitVec.ofNat 64 capD]

/-- The entry environment. -/
abbrev lineEnv (C : Ctx) (jN jL jE cap : Nat) (wi ws0 : BitVec 64) (bufJ bsz rb capD : Nat) : Env :=
  ctxEnv C ++ linePs.zip (lineVs C jN jL jE cap wi ws0 bufJ bsz rb capD)

section
variable (C : Ctx) (jN jL jE cap : Nat) (wi ws0 : BitVec 64) (bufJ bsz rb capD : Nat)

theorem lineEnv_TN : (lineEnv C jN jL jE cap wi ws0 bufJ bsz rb capD).get fTN = some (cellA C jN) := by
  simp +decide [lineEnv, ctxEnv, linePs, lineVs, Env.get]
theorem lineEnv_TL : (lineEnv C jN jL jE cap wi ws0 bufJ bsz rb capD).get fTL = some (cellA C jL) := by
  simp +decide [lineEnv, ctxEnv, linePs, lineVs, Env.get]
theorem lineEnv_TE : (lineEnv C jN jL jE cap wi ws0 bufJ bsz rb capD).get fTE = some (cellA C jE) := by
  simp +decide [lineEnv, ctxEnv, linePs, lineVs, Env.get]
theorem lineEnv_Cap : (lineEnv C jN jL jE cap wi ws0 bufJ bsz rb capD).get fCap = some (BitVec.ofNat 64 cap) := by
  simp +decide [lineEnv, ctxEnv, linePs, lineVs, Env.get]
theorem lineEnv_I : (lineEnv C jN jL jE cap wi ws0 bufJ bsz rb capD).get fI = some wi := by
  simp +decide [lineEnv, ctxEnv, linePs, lineVs, Env.get]
theorem lineEnv_U : (lineEnv C jN jL jE cap wi ws0 bufJ bsz rb capD).get fU = some ws0 := by
  simp +decide [lineEnv, ctxEnv, linePs, lineVs, Env.get]
theorem lineEnv_Pos : (lineEnv C jN jL jE cap wi ws0 bufJ bsz rb capD).get kPos = some ws0 := by
  simp +decide [lineEnv, ctxEnv, linePs, lineVs, Env.get]
theorem lineEnv_BA : (lineEnv C jN jL jE cap wi ws0 bufJ bsz rb capD).get kBA = some (cellA C bufJ) := by
  simp +decide [lineEnv, ctxEnv, linePs, lineVs, Env.get]
theorem lineEnv_BN : (lineEnv C jN jL jE cap wi ws0 bufJ bsz rb capD).get kBN = some (BitVec.ofNat 64 bsz) := by
  simp +decide [lineEnv, ctxEnv, linePs, lineVs, Env.get]
theorem lineEnv_RB : (lineEnv C jN jL jE cap wi ws0 bufJ bsz rb capD).get kRB = some (cellA C rb) := by
  simp +decide [lineEnv, ctxEnv, linePs, lineVs, Env.get]
theorem lineEnv_CD : (lineEnv C jN jL jE cap wi ws0 bufJ bsz rb capD).get kCapD = some (BitVec.ofNat 64 capD) := by
  simp +decide [lineEnv, ctxEnv, linePs, lineVs, Env.get]

end

def binL : List MlS := [fV2, fx, fy, fz, fh]

theorem binL_none (C : Ctx) (jN jL jE cap : Nat) (wi ws0 : BitVec 64) (bufJ bsz rb capD : Nat) :
    ∀ y, y ∈ binL → (lineEnv C jN jL jE cap wi ws0 bufJ bsz rb capD).get y = none := by
  intro y hy; simp only [binL, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl <;> simp +decide [lineEnv, ctxEnv, linePs, lineVs, Env.get]

theorem appCore (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcA : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one))
    (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcT : ∀ k, k < 2 → C.code.lookup (fAppF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun appSpec appInits (vv (slotName k)), .one))
    (s : AState) (st : StateD) (jN jL jE cap rb capD : Nat) (hrel : TblRel C.H jE cap st.exprs)
    (hcap : 8 * cap < 2 ^ 64) (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b) (pos e : USize)
    (hpos : pos.toNat ≤ b.size) (r : ExprRec) (hr : ConLeche.Frontend.scanAppExpr b pos = .ok r e) (i : Nat) :
    SpecR (Inv (σ := σ) C s (lineEnv C jN jL jE cap (BitVec.ofNat 64 (min i natCap)) (BitVec.ofNat 64 pos.toNat)
      bufJ b.size rb capD) [] (ctxLocals ++ binL)) (binLineP fInternApp fAppF) s (parseExprEntryD st i r)
      (ExPost C jE cap st i) :=
  specR_declAdd fU _ (lineEnv_U ..) (appLine_spec ra C hok hcA hsc hcT s _ [] _
    (fun x hx => by simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
                    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp +decide [binL, ctxLocals])
    st jE cap hrel hcap bufJ b hbuf pos e hpos r hr i (lineEnv_TE ..) (lineEnv_Cap ..) (lineEnv_I ..)
    (lineEnv_Pos ..) (lineEnv_BA ..) (lineEnv_BN ..))

theorem lamCore (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcA : C.code.lookup fInternLam = some ([(lEf, .one), (lEa, .one)], bin2Body lamDataE 14, .one))
    (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcT : ∀ k, k < 2 → C.code.lookup (fLamF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanLamExprSpec lamInits (vv (slotName k)), .one))
    (s : AState) (st : StateD) (jN jL jE cap rb capD : Nat) (hrel : TblRel C.H jE cap st.exprs)
    (hcap : 8 * cap < 2 ^ 64) (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b) (pos e : USize)
    (hpos : pos.toNat ≤ b.size) (r : ExprRec) (hr : ConLeche.Frontend.scanLamExpr b pos = .ok r e) (i : Nat) :
    SpecR (Inv (σ := σ) C s (lineEnv C jN jL jE cap (BitVec.ofNat 64 (min i natCap)) (BitVec.ofNat 64 pos.toNat)
      bufJ b.size rb capD) [] (ctxLocals ++ binL)) (binLineP fInternLam fLamF) s (parseExprEntryD st i r)
      (ExPost C jE cap st i) :=
  specR_declAdd fU _ (lineEnv_U ..) (lamLine_spec ra C hok hcA hsc hcT s _ [] _
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp +decide [binL, ctxLocals])
    st jE cap hrel hcap bufJ b hbuf pos e hpos r hr i (lineEnv_TE ..) (lineEnv_Cap ..) (lineEnv_I ..)
    (lineEnv_Pos ..) (lineEnv_BA ..) (lineEnv_BN ..))

theorem allCore (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcA : C.code.lookup fInternForallE = some ([(lEf, .one), (lEa, .one)], bin2Body forDataE 15, .one))
    (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcT : ∀ k, k < 2 → C.code.lookup (fAllF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanForallExprSpec allInits (vv (slotName k)), .one))
    (s : AState) (st : StateD) (jN jL jE cap rb capD : Nat) (hrel : TblRel C.H jE cap st.exprs)
    (hcap : 8 * cap < 2 ^ 64) (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b) (pos e : USize)
    (hpos : pos.toNat ≤ b.size) (r : ExprRec) (hr : ConLeche.Frontend.scanForallExpr b pos = .ok r e) (i : Nat) :
    SpecR (Inv (σ := σ) C s (lineEnv C jN jL jE cap (BitVec.ofNat 64 (min i natCap)) (BitVec.ofNat 64 pos.toNat)
      bufJ b.size rb capD) [] (ctxLocals ++ binL)) (binLineP fInternForallE fAllF) s (parseExprEntryD st i r)
      (ExPost C jE cap st i) :=
  specR_declAdd fU _ (lineEnv_U ..) (allLine_spec ra C hok hcA hsc hcT s _ [] _
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp +decide [binL, ctxLocals])
    st jE cap hrel hcap bufJ b hbuf pos e hpos r hr i (lineEnv_TE ..) (lineEnv_Cap ..) (lineEnv_I ..)
    (lineEnv_Pos ..) (lineEnv_BA ..) (lineEnv_BN ..))

def letL : List MlS := [fV2, fx, fy, fz, fW3, fh]

theorem letL_none (C : Ctx) (jN jL jE cap : Nat) (wi ws0 : BitVec 64) (bufJ bsz rb capD : Nat) :
    ∀ y, y ∈ letL → (lineEnv C jN jL jE cap wi ws0 bufJ bsz rb capD).get y = none := by
  intro y hy; simp only [letL, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> simp +decide [lineEnv, ctxEnv, linePs, lineVs, Env.get]

theorem letCore (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcL : C.code.lookup fInternLet = some ([(lEty, .one), (lEvl, .one), (lEbd, .one)], letBody, .one))
    (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcT : ∀ k, k < 3 → C.code.lookup (fLetF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanLetExprSpec letInits (vv (slotName k)), .one))
    (s : AState) (st : StateD) (jN jL jE cap rb capD : Nat) (hrel : TblRel C.H jE cap st.exprs)
    (hcap : 8 * cap < 2 ^ 64) (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b) (pos e : USize)
    (hpos : pos.toNat ≤ b.size) (r : ExprRec) (hr : ConLeche.Frontend.scanLetExpr b pos = .ok r e) (i : Nat) :
    SpecR (Inv (σ := σ) C s (lineEnv C jN jL jE cap (BitVec.ofNat 64 (min i natCap)) (BitVec.ofNat 64 pos.toNat)
      bufJ b.size rb capD) [] (ctxLocals ++ letL)) letLineP s (parseExprEntryD st i r) (ExPost C jE cap st i) :=
  specR_declAdd fU _ (lineEnv_U ..) (specR_declAdd fTN _ (lineEnv_TN ..) (letLine_spec ra C hok hcL hsc hcT s _ [] _
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp +decide [letL, ctxLocals])
    st jE cap hrel hcap bufJ b hbuf pos e hpos r hr i (lineEnv_TE ..) (lineEnv_Cap ..) (lineEnv_I ..)
    (lineEnv_Pos ..) (lineEnv_BA ..) (lineEnv_BN ..)))

def projL : List MlS := [fV2, fW3, fx, fy, fz, fh]

theorem projL_none (C : Ctx) (jN jL jE cap : Nat) (wi ws0 : BitVec 64) (bufJ bsz rb capD : Nat) :
    ∀ y, y ∈ projL → (lineEnv C jN jL jE cap wi ws0 bufJ bsz rb capD).get y = none := by
  intro y hy; simp only [projL, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;> simp +decide [lineEnv, ctxEnv, linePs, lineVs, Env.get]

theorem projCore (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcP : C.code.lookup fInternProj = some ([(lEp, .one), (lEe, .one), (lIw, .one)], projBody, .one))
    (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcT : ∀ k, k < 3 → C.code.lookup (fProjF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanProjExprSpec projInits (vv (slotName k)), .one))
    (s : AState) (st : StateD) (jN jL jE cap rb capD : Nat) (hrel : TblRel C.H jE cap st.exprs) (hreln : TblRel C.H jN cap st.names)
    (hcap : 8 * cap < 2 ^ 64) (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b) (pos e : USize)
    (hpos : pos.toNat ≤ b.size) (r : ExprRec) (hr : ConLeche.Frontend.scanProjExpr b pos = .ok r e) (i : Nat) :
    SpecR (Inv (σ := σ) C s (lineEnv C jN jL jE cap (BitVec.ofNat 64 (min i natCap)) (BitVec.ofNat 64 pos.toNat)
      bufJ b.size rb capD) [] (ctxLocals ++ projL)) projLineP s (parseExprEntryD st i r) (ExPost C jE cap st i) :=
  specR_declAdd fU _ (lineEnv_U ..) (projLine_spec ra C hok hcP hsc hcT s _ [] _
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp +decide [projL, ctxLocals])
    st jE jN cap hrel hreln hcap bufJ b hbuf pos e hpos r hr i (lineEnv_TE ..) (lineEnv_TN ..) (lineEnv_Cap ..)
    (lineEnv_I ..) (lineEnv_Pos ..) (lineEnv_BA ..) (lineEnv_BN ..))

def constL : List MlS := [fV2, fx, fy, kG2, kKA0, kN, kK, kX, kY, kLs, fh]

theorem constL_none (C : Ctx) (jN jL jE cap : Nat) (wi ws0 : BitVec 64) (bufJ bsz rb capD : Nat) :
    ∀ y, y ∈ constL → (lineEnv C jN jL jE cap wi ws0 bufJ bsz rb capD).get y = none := by
  intro y hy; simp only [constL, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp +decide [lineEnv, ctxEnv, linePs, lineVs, Env.get]

theorem constCore (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hnc : ∀ t : PState σ, t.code = C.code → NnCodes t)
    (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcN : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one))
    (hcLs : C.code.lookup fInternLs = some ([(pKey, .one), (lEc, .one)], internLsBody, .one))
    (hcC : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one))
    (hcT : ∀ k, k < 2 → C.code.lookup (fConstF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanConstExprSpec constInits (vv (slotName k)), .one))
    (s : AState) (st : StateD) (jN jL jE cap rb capD : Nat) (hrel : TblRel C.H jE cap st.exprs) (hrell : TblRel C.H jL cap st.levels)
    (hreln : TblRel C.H jN cap st.names) (hcap : 8 * cap < 2 ^ 64) (hcapN : cap ≤ natCap)
    (bufJ : Nat) (b : ByteArray) (hbuf : BufOK C bufJ b) (pos e : USize)
    (hpos : pos.toNat ≤ b.size) (r : ExprRec) (hr : ConLeche.Frontend.scanConstExpr b pos = .ok r e) (i : Nat) :
    SpecR (Inv (σ := σ) C s (lineEnv C jN jL jE cap (BitVec.ofNat 64 (min i natCap)) (BitVec.ofNat 64 pos.toNat)
      bufJ b.size rb capD) [] (ctxLocals ++ constL)) (constLineP C) s (parseExprEntryD st i r) (ExPost C jE cap st i) :=
  specR_declAdd fU _ (lineEnv_U ..) (constLine_spec ra C hok hnc hsc hcN hcLs hcC hcT s _ [] _
    (fun x hx => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp +decide [constL, ctxLocals])
    st jE jL jN cap hrel hrell hreln hcap hcapN bufJ b hbuf pos e hpos r hr i (lineEnv_TE ..) (lineEnv_TL ..)
    (lineEnv_TN ..) (lineEnv_Cap ..) (lineEnv_I ..) (lineEnv_Pos ..) (lineEnv_BA ..) (lineEnv_BN ..))


end ConPanqueque.Front
