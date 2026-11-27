import ConPanqueque.Front.AxiomDisp
import ConPanqueque.Front.QuotLine

/-! # The quotient line's branch (tag 22) -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (ExprRec LevelRec NameRec LineRec LinePayload ScanRes byteAt Key)

variable {σ : Type}

def qtL : List MlS := [kSf, fV2, fW3, kT, fy, fz, kVh, kR, kCnt, kK, kG2, kX, kY, kKA0, kKA, kN]

theorem qtL_none (C : Ctx) (jN jL jE cap : Nat) (wi ws0 : BitVec 64) (bufJ bsz rb capD : Nat) :
    ∀ y, y ∈ qtL → (lineEnv C jN jL jE cap wi ws0 bufJ bsz rb capD).get y = none := by
  intro y hy; simp only [qtL, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp +decide [lineEnv, ctxEnv, linePs, lineVs, Env.get]

theorem tag_22 {k : Key} {a : LActP} (hm : (k, a) ∈ lineTblP) (ht : a.tag = 22) : a = .objP 22 0 fRecQuot declQuot := by
  simp only [lineTblP, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h) <;>
    first | rfl | (simp [LActP.tag] at ht)

theorem qtCore (C : Ctx) (hok : CtxOK C)
    (hnc : ∀ t : PState σ, t.code = C.code → NnCodes t)
    (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t)
    (hcN : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one))
    (hcK : C.code.lookup fQKind = some ([(sB, .one), (sN, .one), (sI, .one)], qkFun, .one))
    (hcT : ∀ k, k < 4 → C.code.lookup (fQtF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanQuotDeclSpec qtInits (vv (slotName k)), .one))
    (s : AState) (st : StateD) (F rb capD jN jL jE cap bufJ : Nat) (b : ByteArray)
    (hlay : FrontLay F rb capD jN jL jE cap bufJ b) (hreln : TblRel C.H jN cap st.names) (hrele : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (hcapN : cap ≤ natCap) (hbuf : BufOK C bufJ b) (hdr : DeclsRel C F rb capD C.H st.decls)
    (hcapD : 8 * (rb + 1 + capD) < 2 ^ 64)
    (pos e : USize) (hpos : pos.toNat ≤ b.size) (d : ConLeche.Frontend.DeclRec)
    (hd : ConLeche.Frontend.scanQuotDecl b pos = .ok d e) (i : Nat) :
    SpecR (Inv (σ := σ) C s (lineEnv C jN jL jE cap (BitVec.ofNat 64 (min i natCap)) (BitVec.ofNat 64 pos.toNat)
      bufJ b.size rb capD) [] (ctxLocals ++ qtL)) (qtLineP C) s (processLineCoreD st d)
      (fun a w s' t' => ∃ d, DeclPost C F rb capD C.H st d a w s' t') :=
  specR_declAdd fU _ (lineEnv_U ..) (qtLine_spec C hok hnc hsc hcN hcK hcT s _ [] _
    (fun x hx => by
      simp only [lbMods, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp +decide [qtL, ctxLocals])
    st F rb capD jN jL jE cap bufJ b hlay hreln hrele hcap hcapN hbuf hdr hcapD pos e hpos d hd
    (lineEnv_TN ..) (lineEnv_TE ..) (lineEnv_Cap ..) (lineEnv_Pos ..) (lineEnv_BA ..) (lineEnv_BN ..)
    (lineEnv_RB ..) (lineEnv_CD ..))

section
variable {F rb capD jN jL jE cap bufJ : Nat} {b : ByteArray}

theorem brQt {β : Type} {k : StateD ⊕ RecordVerdict → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64} (C : Ctx) (hok : CtxOK C) (hnc : ∀ t : PState σ, t.code = C.code → NnCodes t) (hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t) (hcN : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one))
    (hcK : C.code.lookup fQKind = some ([(sB, .one), (sN, .one), (sI, .one)], qkFun, .one))
    (hcT : ∀ k, k < 4 → C.code.lookup (fQtF k) =
      some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanQuotDeclSpec qtInits (vv (slotName k)), .one))
    (fL : MlS) (hcL : C.code.lookup fL =
      some (linePs.map (fun p => (p, ShapeHOL.one)), prologue qtL (qtLineP C), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hx : kR0 ∈ D) (st : StateD)
    (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (ws0 : BitVec 64) (pl : LinePayload) (hpl : PlOK b (BitVec.ofNat 64 22) ws0 pl) (j0 j' : USize) (ik : UInt8)
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
  obtain rfl := tag_22 hm hta
  obtain ⟨v, e, r', hws, hsc', rfl⟩ := objPl (sc := ConLeche.Frontend.scanQuotDecl) (wrap := LinePayload.decl) he
  subst hws
  rw [lineEnd_decl hle, applyLine_decl _ _ _ hn]
  have hbuf : BufOK C bufJ b := by have := hfs.buf; rwa [ctxH_self] at this
  have hpos : v.toNat ≤ b.size := Nat.le_of_lt (start_lt hbuf.plat (by rw [ConLeche.Frontend.scanQuotDecl] at hsc'; exact hsc'))
  exact specR_dcLineCall kR0 fL qtL _ lineArgs _ rfl hx hcL
    (evAll_lineArgs Γ C jN jL jE cap _ _ bufJ b.size rb capD h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    (qtL_none C jN jL jE cap _ _ bufJ b.size rb capD) st r' hfs
    (qtCore C hok hnc hsc hcN hcK hcT s st F rb capD jN jL jE cap bufJ b hfs.lay.fl hfs.tN hfs.tE hfs.lay.cap8 hfs.lay.capN hbuf hfs.dr
      hfs.lay.capD8 v e hpos r' hsc' idx)
    hk

end

end ConPanqueque.Front
