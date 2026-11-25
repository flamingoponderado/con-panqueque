import ConPanqueque.Front.ScanPhase
import ConPanqueque.Front.ScanKB

/-! # The frontend's code table and the line dispatcher

`FrontCodes σ C`: every function the frontend calls is in the code table, with its body.  `fLine t`
is the line function for tag `t`. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan

def fLine (t : Nat) : MlS := ofString ("line" ++ toString t)

structure FrontCodes (σ : Type) (C : Ctx) : Prop where
  hsc : ∀ t : PState σ, t.code = C.code → ScanCodes t
  hnc : ∀ t : PState σ, t.code = C.code → NnCodes t
  hhc : ∀ t : PState σ, t.code = C.code → HvCodes t
  hlc : ∀ t : PState σ, t.code = C.code → LineCodes t
  cNth : C.code.lookup fNth = some ([(sB, .one), (sN, .one), (sI, .one), (sL, .one)], nnFun, .one)
  cSafe : C.code.lookup fSafe = some ([(sB, .one), (sN, .one), (sI, .one)], sfFun, .one)
  cHintV : C.code.lookup fHintV = some ([(sB, .one), (sN, .one), (sI, .one)], hvFun, .one)
  cStr : C.code.lookup fStr = some ([(sB, .one), (sN, .one), (sI, .one)], ssFun, .one)
  cApp : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)
  cLam : C.code.lookup fInternLam = some ([(lEf, .one), (lEa, .one)], bin2Body lamDataE 14, .one)
  cAll : C.code.lookup fInternForallE = some ([(lEf, .one), (lEa, .one)], bin2Body forDataE 15, .one)
  cLet : C.code.lookup fInternLet = some ([(lEty, .one), (lEvl, .one), (lEbd, .one)], letBody, .one)
  cProj : C.code.lookup fInternProj = some ([(lEp, .one), (lEe, .one), (lIw, .one)], projBody, .one)
  cLs : C.code.lookup fInternLs = some ([(pKey, .one), (lEc, .one)], internLsBody, .one)
  cConst : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one)
  cBVar : C.code.lookup fInternBVar = some ([(lIw, .one)], bvarBody, .one)
  cSort : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one)
  cSucc : C.code.lookup fInternLSucc = some ([(lEu, .one)], internLSuccBody, .one)
  cParam : C.code.lookup fInternLParam = some ([(lEn, .one)], internLParamBody, .one)
  cMax : C.code.lookup fInternLMax = some ([(lEu, .one), (lEv, .one)], internLMaxBody, .one)
  cImax : C.code.lookup fInternLImax = some ([(lEu, .one), (lEv, .one)], internLImaxBody, .one)
  cNNum : C.code.lookup fInternNNum = some ([(pKeyN, .one), (lEn, .one), (lEp, .one), (lNw, .one)], nameNumBody, .one)
  cNStr : C.code.lookup fInternNStr = some ([(pKeyN, .one), (lEn, .one), (lEp, .one), (lHn, .one)], nameStrBody, .one)
  fApp : ∀ k, k < 2 → C.code.lookup (fAppF k) = some ([(sB, .one), (sN, .one), (sI, .one)], recFun appSpec appInits (vv (slotName k)), .one)
  fLam : ∀ k, k < 2 → C.code.lookup (fLamF k) = some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanLamExprSpec lamInits (vv (slotName k)), .one)
  fAll : ∀ k, k < 2 → C.code.lookup (fAllF k) = some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanForallExprSpec allInits (vv (slotName k)), .one)
  fLet : ∀ k, k < 3 → C.code.lookup (fLetF k) = some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanLetExprSpec letInits (vv (slotName k)), .one)
  fProj : ∀ k, k < 3 → C.code.lookup (fProjF k) = some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanProjExprSpec projInits (vv (slotName k)), .one)
  fConst : ∀ k, k < 2 → C.code.lookup (fConstF k) = some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanConstExprSpec constInits (vv (slotName k)), .one)
  fNum : ∀ k, k < 2 → C.code.lookup (fNumF k) = some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanNumNameSpec numInits (vv (slotName k)), .one)
  fStrN : ∀ k, k < 2 → C.code.lookup (fStrF k) = some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanStrNameSpec strInits (vv (slotName k)), .one)
  fThm : ∀ k, k < 4 → C.code.lookup (fThmF k) = some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanThmDeclSpec thmInits (vv (slotName k)), .one)
  fOpq : ∀ k, k < 5 → C.code.lookup (fOpqF k) = some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanOpaqueDeclSpec opqInits (vv (slotName k)), .one)
  fDef : ∀ k, k < 6 → C.code.lookup (fDefF k) = some ([(sB, .one), (sN, .one), (sI, .one)], recFun scanDefDeclSpec defInits (vv (slotName k)), .one)
  cLnPl : C.code.lookup fLnPl = some ([(sB, .one), (sN, .one), (sI, .one)], lineFun sPl, .one)
  cLnS0 : C.code.lookup fLnS0 = some ([(sB, .one), (sN, .one), (sI, .one)], lineFun (slotName 0), .one)
  cLnIx : C.code.lookup fLnIx = some ([(sB, .one), (sN, .one), (sI, .one)], lineFun sIdx, .one)
  cLnNx : C.code.lookup fLnNx = some ([(sB, .one), (sN, .one), (sI, .one)], lineFun sI, .one)
  l1 : C.code.lookup (fLine 1) = some (linePs.map (fun p => (p, ShapeHOL.one)), prologue natL (natLineP exBVarP), .one)
  l2 : C.code.lookup (fLine 2) = some (linePs.map (fun p => (p, ShapeHOL.one)), prologue natL (natLineP exSortP), .one)
  l3 : C.code.lookup (fLine 3) = some (linePs.map (fun p => (p, ShapeHOL.one)), prologue natL (natLineP lvSuccP), .one)
  l4 : C.code.lookup (fLine 4) = some (linePs.map (fun p => (p, ShapeHOL.one)), prologue natL (natLineP lvParamP), .one)
  l5 : C.code.lookup (fLine 5) = some (linePs.map (fun p => (p, ShapeHOL.one)), prologue strL (strLineP C), .one)
  l6 : C.code.lookup (fLine 6) = some (linePs.map (fun p => (p, ShapeHOL.one)), prologue numL (numLineP C), .one)
  l7 : C.code.lookup (fLine 7) = some (linePs.map (fun p => (p, ShapeHOL.one)), prologue binL (binLineP fInternApp fAppF), .one)
  l8 : C.code.lookup (fLine 8) = some (linePs.map (fun p => (p, ShapeHOL.one)), prologue binL (binLineP fInternLam fLamF), .one)
  l9 : C.code.lookup (fLine 9) = some (linePs.map (fun p => (p, ShapeHOL.one)), prologue binL (binLineP fInternForallE fAllF), .one)
  l10 : C.code.lookup (fLine 10) = some (linePs.map (fun p => (p, ShapeHOL.one)), prologue letL (letLineP), .one)
  l11 : C.code.lookup (fLine 11) = some (linePs.map (fun p => (p, ShapeHOL.one)), prologue constL (constLineP C), .one)
  l12 : C.code.lookup (fLine 12) = some (linePs.map (fun p => (p, ShapeHOL.one)), prologue projL (projLineP), .one)
  l14 : C.code.lookup (fLine 14) = some (linePs.map (fun p => (p, ShapeHOL.one)), prologue dfL (dfLineP C), .one)
  l15 : C.code.lookup (fLine 15) = some (linePs.map (fun p => (p, ShapeHOL.one)), prologue thL (thLineP C), .one)
  l16 : C.code.lookup (fLine 16) = some (linePs.map (fun p => (p, ShapeHOL.one)), prologue opL (opLineP C), .one)
  l18 : C.code.lookup (fLine 18) = some (linePs.map (fun p => (p, ShapeHOL.one)), prologue pairL (lvPairLineP fInternLMax), .one)
  l19 : C.code.lookup (fLine 19) = some (linePs.map (fun p => (p, ShapeHOL.one)), prologue pairL (lvPairLineP fInternLImax), .one)
  cLnKB : C.code.lookup fLnKB = some ([(sB, .one), (sN, .one), (sI, .one)], lineFunKB, .one)

variable {σ : Type}

def callLine (t : Nat) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.local, kR0), none)) (fLine t) lineArgs) rest

def guardIx (c : ProgHOL 64) : ProgHOL 64 := .ite (.cmp .lower (vv kIx) (vv fCap)) c hang

def isDeclTag (t : Nat) : Bool := t == 14 || t == 15 || t == 16

def branchP (rest : ProgHOL 64) (t : Nat) : ProgHOL 64 :=
  if isDeclTag t then callLine t rest else guardIx (callLine t rest)

def chainP (rest : ProgHOL 64) : List Nat → ProgHOL 64
  | [] => hang
  | t :: ts => .ite (.cmp .equal (vv kTg) (.const (BitVec.ofNat 64 t))) (branchP rest t) (chainP rest ts)

def dispTags : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 14, 15, 16, 18, 19]

/-- The dispatch after the scan phase. -/
def dispatchP (rest : ProgHOL 64) : ProgHOL 64 :=
  .ite (.cmp .equal (vv kTg) (.const (BitVec.ofNat 64 17)))
    (.ite (.cmp .equal (vv kLn) (.const 0)) rest hang)
    (.ite (.cmp .equal (vv kLn) (.const 0)) hang (chainP rest dispTags))

theorem plTag_lt (pl : ConLeche.Frontend.LinePayload) : plTag pl < 32 := by
  unfold plTag; split <;> decide

theorem bw_eq_ne {w c : BitVec 64} (h : bw (w = c) ≠ 0) : w = c := by
  by_cases e : w = c
  · exact e
  · simp [bw, e] at h

theorem chain_spec {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (rest : ProgHOL 64) (wt : BitVec 64)
    (hTg : Γ.get kTg = some wt) :
    ∀ ts : List Nat, (∀ t ∈ ts, wt = BitVec.ofNat 64 t → SpecR (Inv C s Γ M D) (branchP rest t) s m R) →
      SpecR (Inv C s Γ M D) (chainP rest ts) s m R
  | [], _ => specR_hangI
  | t :: ts, hb => specR_ifI _ _ (sev_eq_c' Γ kTg wt (BitVec.ofNat 64 t) hTg)
      (fun h => hb t (List.mem_cons_self) (bw_eq_ne h))
      (fun _ => chain_spec rest wt hTg ts (fun t' ht' => hb t' (List.mem_cons_of_mem _ ht')))

theorem inv_dropMem {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {t : PState σ}
    (h : Inv C s Γ M D t) : Inv C s Γ [] D t :=
  ⟨h.sr, h.env, fun _ _ h' => absurd h' (by simp), h.decl⟩

theorem recPl_header {rec : ConLeche.Frontend.LineRec} (h : plTag (recPl rec) = 17) : rec = .header := by
  cases rec with
  | name i r => cases r <;> simp [recPl, plTag] at h
  | level i r => cases r <;> simp [recPl, plTag] at h
  | expr i r => cases r <;> simp [recPl, plTag] at h
  | decl d => cases d <;> simp [recPl, plTag] at h
  | header => rfl
  | blank => simp [recPl, plTag] at h

theorem specR_guardIx {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {c : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (idx cap : Nat) (hcapN : cap ≤ natCap)
    (hc64 : cap < 2 ^ 64) (hIx : Γ.get kIx = some (BitVec.ofNat 64 (min idx natCap)))
    (hC : Γ.get fCap = some (BitVec.ofNat 64 cap)) (h : idx < cap → SpecR (Inv C s Γ M D) c s m R) :
    SpecR (Inv C s Γ M D) (guardIx c) s m R := by
  unfold guardIx
  refine specR_ifI _ _ (sev_lower Γ (vv kIx) (vv fCap) (min idx natCap) cap (by simpa [sev, vv] using hIx)
    (by simpa [sev, vv] using hC) (Nat.lt_of_le_of_lt (Nat.min_le_right _ _) natCap_lt) hc64) (fun hw => ?_)
    (fun _ => specR_hangI)
  have hl : min idx natCap < cap := by
    by_cases e : min idx natCap < cap
    · exact e
    · simp [bw, e] at hw
  exact h (by omega)

theorem ofNat_lt32_inj {a c : Nat} (ha : a < 32) (hc : c < 32) (h : BitVec.ofNat 64 a = BitVec.ofNat 64 c) : a = c := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

section
variable {F rb capD jN jL jE cap bufJ : Nat} {b : ByteArray}

/-- **The dispatcher refines `applyLine`.** -/
theorem dispatch_spec {β : Type} {k : StateD ⊕ RecordVerdict → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64} (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : FrontOK C)
    (fc : FrontCodes σ C) (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hx : kR0 ∈ D) (st : StateD)
    (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (rec : ConLeche.Frontend.LineRec) (next : USize) (wt ws wi wn : BitVec 64) (hso : ScanOut b rec next wt ws wi wn)
    (n : Nat) (hn64 : n < 2 ^ 64)
    (hTg : Γ.get kTg = some wt) (hS0 : Γ.get kS0 = some ws) (hIx : Γ.get kIx = some wi)
    (hLn : Γ.get kLn = some (BitVec.ofNat 64 n))
    (h1 : Γ.get fTN = some (cellA C jN)) (h2 : Γ.get fTL = some (cellA C jL)) (h3 : Γ.get fTE = some (cellA C jE))
    (h4 : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (h7 : Γ.get kBA = some (cellA C bufJ)) (h8 : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (h9 : Γ.get kRB = some (cellA C rb)) (h10 : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hk : ∀ st' s' H' (Γ' : Env), FrontSt C F rb capD jN jL jE cap bufJ b H' st' →
      (∀ y, y ≠ kR0 → Γ'.get y = Γ.get y) → SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k (.inl st')) R) :
    SpecR (Inv C s Γ M D) (dispatchP rest) s (applyLine st rec n >>= k) R := by
  obtain ⟨hwt, hwn, hpay⟩ := hso
  have hk' : ∀ st' w s' H', FrontSt C F rb capD jN jL jE cap bufJ b H' st' →
      SpecR (Inv (ctxH C H') s' ((kR0, w) :: Γ) [] D) rest s' (k (.inl st')) R :=
    fun st' w s' H' hf => hk st' s' H' _ hf (fun y hy => by simp only [Env.get_cons, if_neg hy])
  unfold dispatchP
  refine specR_ifI _ _ (sev_eq_c' Γ kTg wt (BitVec.ofNat 64 17) hTg) (fun h17 => ?_) (fun h17 => ?_)
  · have hpt : plTag (recPl rec) = 17 := by
      have e := bw_eq_ne h17; rw [hwt] at e; exact ofNat_lt32_inj (plTag_lt _) (by decide) e
    obtain rfl := recPl_header hpt
    refine specR_ifI _ _ (sev_eq_c' Γ kLn (BitVec.ofNat 64 n) 0 hLn) (fun h0 => ?_) (fun _ => specR_hangI)
    have hn0 : n = 0 := by
      have e := congrArg BitVec.toNat (bw_eq_ne h0); simp only [BitVec.toNat_ofNat] at e
      rw [Nat.mod_eq_of_lt hn64] at e; simpa using e
    subst hn0
    have ha : applyLine st .header 0 = pure (.inl st) := by simp [applyLine, lineRecPlaced, applyRecord]
    rw [ha, pure_bind]
    intro t ht
    have := hk st s C.H Γ hfs (fun y _ => rfl)
    rw [ctxH_self] at this
    exact this t (inv_dropMem ht)
  · refine specR_ifI _ _ (sev_eq_c' Γ kLn (BitVec.ofNat 64 n) 0 hLn) (fun _ => specR_hangI) (fun h0 => ?_)
    have hn : n ≠ 0 := by
      intro e; subst e; simp [bw] at h0
    refine chain_spec rest wt hTg dispTags (fun t ht he => ?_)
    have ht32 : t < 32 := by simp only [dispTags, List.mem_cons, List.not_mem_nil, or_false] at ht; omega
    have hpt : plTag (recPl rec) = t := by
      rw [hwt] at he; exact ofNat_lt32_inj (plTag_lt _) ht32 he
    have hnb : rec ≠ .blank := by
      intro hb; subst hb; simp only [recPl, plTag] at hpt; subst hpt
      simp [dispTags] at ht
    obtain ⟨hpl, j0, ik, idx, j', hle, hwi⟩ := hpay hnb
    rw [he] at hpl
    simp only [dispTags, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · show SpecR _ (guardIx (callLine 1 rest)) _ _ _
      refine specR_guardIx idx cap hfs.lay.capN (by have := hfs.lay.cap8; omega) (by rw [hIx, hwi]) h4 (fun hi => ?_)
      exact brBVar ra C hok fc.cBVar (fLine 1) fc.l1 s Γ M D hx st hfs ws (recPl rec) hpl j0 j' ik idx rec hle n hn hi h1 h2 h3 h4 (by rw [hIx, hwi]) hS0 h7 h8 h9 h10 hk'
    · show SpecR _ (guardIx (callLine 2 rest)) _ _ _
      refine specR_guardIx idx cap hfs.lay.capN (by have := hfs.lay.cap8; omega) (by rw [hIx, hwi]) h4 (fun hi => ?_)
      exact brSort ra C hok fc.cSort (fLine 2) fc.l2 s Γ M D hx st hfs ws (recPl rec) hpl j0 j' ik idx rec hle n hn hi h1 h2 h3 h4 (by rw [hIx, hwi]) hS0 h7 h8 h9 h10 hk'
    · show SpecR _ (guardIx (callLine 3 rest)) _ _ _
      refine specR_guardIx idx cap hfs.lay.capN (by have := hfs.lay.cap8; omega) (by rw [hIx, hwi]) h4 (fun hi => ?_)
      exact brSucc ra C hok fc.cSucc (fLine 3) fc.l3 s Γ M D hx st hfs ws (recPl rec) hpl j0 j' ik idx rec hle n hn hi h1 h2 h3 h4 (by rw [hIx, hwi]) hS0 h7 h8 h9 h10 hk'
    · show SpecR _ (guardIx (callLine 4 rest)) _ _ _
      refine specR_guardIx idx cap hfs.lay.capN (by have := hfs.lay.cap8; omega) (by rw [hIx, hwi]) h4 (fun hi => ?_)
      exact brParam ra C hok fc.cParam (fLine 4) fc.l4 s Γ M D hx st hfs ws (recPl rec) hpl j0 j' ik idx rec hle n hn hi h1 h2 h3 h4 (by rw [hIx, hwi]) hS0 h7 h8 h9 h10 hk'
    · show SpecR _ (guardIx (callLine 5 rest)) _ _ _
      refine specR_guardIx idx cap hfs.lay.capN (by have := hfs.lay.cap8; omega) (by rw [hIx, hwi]) h4 (fun hi => ?_)
      exact brStr ra C hok hf fc.cNStr fc.hsc fc.cStr fc.fStrN (fLine 5) fc.l5 s Γ M D hx st hfs ws (recPl rec) hpl j0 j' ik idx rec hle n hn hi h1 h2 h3 h4 (by rw [hIx, hwi]) hS0 h7 h8 h9 h10 hk'
    · show SpecR _ (guardIx (callLine 6 rest)) _ _ _
      refine specR_guardIx idx cap hfs.lay.capN (by have := hfs.lay.cap8; omega) (by rw [hIx, hwi]) h4 (fun hi => ?_)
      exact brNum ra C hok hf fc.cNNum fc.hsc fc.fNum (fLine 6) fc.l6 s Γ M D hx st hfs ws (recPl rec) hpl j0 j' ik idx rec hle n hn hi h1 h2 h3 h4 (by rw [hIx, hwi]) hS0 h7 h8 h9 h10 hk'
    · show SpecR _ (guardIx (callLine 7 rest)) _ _ _
      refine specR_guardIx idx cap hfs.lay.capN (by have := hfs.lay.cap8; omega) (by rw [hIx, hwi]) h4 (fun hi => ?_)
      exact brApp ra C hok fc.cApp fc.hsc fc.fApp (fLine 7) fc.l7 s Γ M D hx st hfs ws (recPl rec) hpl j0 j' ik idx rec hle n hn hi h1 h2 h3 h4 (by rw [hIx, hwi]) hS0 h7 h8 h9 h10 hk'
    · show SpecR _ (guardIx (callLine 8 rest)) _ _ _
      refine specR_guardIx idx cap hfs.lay.capN (by have := hfs.lay.cap8; omega) (by rw [hIx, hwi]) h4 (fun hi => ?_)
      exact brLam ra C hok fc.cLam fc.hsc fc.fLam (fLine 8) fc.l8 s Γ M D hx st hfs ws (recPl rec) hpl j0 j' ik idx rec hle n hn hi h1 h2 h3 h4 (by rw [hIx, hwi]) hS0 h7 h8 h9 h10 hk'
    · show SpecR _ (guardIx (callLine 9 rest)) _ _ _
      refine specR_guardIx idx cap hfs.lay.capN (by have := hfs.lay.cap8; omega) (by rw [hIx, hwi]) h4 (fun hi => ?_)
      exact brAll ra C hok fc.cAll fc.hsc fc.fAll (fLine 9) fc.l9 s Γ M D hx st hfs ws (recPl rec) hpl j0 j' ik idx rec hle n hn hi h1 h2 h3 h4 (by rw [hIx, hwi]) hS0 h7 h8 h9 h10 hk'
    · show SpecR _ (guardIx (callLine 10 rest)) _ _ _
      refine specR_guardIx idx cap hfs.lay.capN (by have := hfs.lay.cap8; omega) (by rw [hIx, hwi]) h4 (fun hi => ?_)
      exact brLet ra C hok fc.cLet fc.hsc fc.fLet (fLine 10) fc.l10 s Γ M D hx st hfs ws (recPl rec) hpl j0 j' ik idx rec hle n hn hi h1 h2 h3 h4 (by rw [hIx, hwi]) hS0 h7 h8 h9 h10 hk'
    · show SpecR _ (guardIx (callLine 11 rest)) _ _ _
      refine specR_guardIx idx cap hfs.lay.capN (by have := hfs.lay.cap8; omega) (by rw [hIx, hwi]) h4 (fun hi => ?_)
      exact brConst ra C hok fc.hnc fc.hsc fc.cNth fc.cLs fc.cConst fc.fConst (fLine 11) fc.l11 s Γ M D hx st hfs ws (recPl rec) hpl j0 j' ik idx rec hle n hn hi h1 h2 h3 h4 (by rw [hIx, hwi]) hS0 h7 h8 h9 h10 hk'
    · show SpecR _ (guardIx (callLine 12 rest)) _ _ _
      refine specR_guardIx idx cap hfs.lay.capN (by have := hfs.lay.cap8; omega) (by rw [hIx, hwi]) h4 (fun hi => ?_)
      exact brProj ra C hok fc.cProj fc.hsc fc.fProj (fLine 12) fc.l12 s Γ M D hx st hfs ws (recPl rec) hpl j0 j' ik idx rec hle n hn hi h1 h2 h3 h4 (by rw [hIx, hwi]) hS0 h7 h8 h9 h10 hk'
    · show SpecR _ (callLine 14 rest) _ _ _
      exact brDef ra C hok fc.hnc fc.hsc fc.cNth fc.cSafe fc.cHintV fc.hhc fc.fDef (fLine 14) fc.l14 s Γ M D hx st hfs ws (recPl rec) hpl j0 j' ik idx rec hle n hn h1 h2 h3 h4 (by rw [hIx, hwi]) hS0 h7 h8 h9 h10 hk'
    · show SpecR _ (callLine 15 rest) _ _ _
      exact brThm C hok fc.hnc fc.hsc fc.cNth fc.fThm (fLine 15) fc.l15 s Γ M D hx st hfs ws (recPl rec) hpl j0 j' ik idx rec hle n hn h1 h2 h3 h4 (by rw [hIx, hwi]) hS0 h7 h8 h9 h10 hk'
    · show SpecR _ (callLine 16 rest) _ _ _
      exact brOpq C hok fc.hnc fc.hsc fc.cNth fc.fOpq (fLine 16) fc.l16 s Γ M D hx st hfs ws (recPl rec) hpl j0 j' ik idx rec hle n hn h1 h2 h3 h4 (by rw [hIx, hwi]) hS0 h7 h8 h9 h10 hk'
    · show SpecR _ (guardIx (callLine 18 rest)) _ _ _
      refine specR_guardIx idx cap hfs.lay.capN (by have := hfs.lay.cap8; omega) (by rw [hIx, hwi]) h4 (fun hi => ?_)
      exact brMax ra C hok fc.hnc fc.cNth fc.cMax (fLine 18) fc.l18 s Γ M D hx st hfs ws (recPl rec) hpl j0 j' ik idx rec hle n hn hi h1 h2 h3 h4 (by rw [hIx, hwi]) hS0 h7 h8 h9 h10 hk'
    · show SpecR _ (guardIx (callLine 19 rest)) _ _ _
      refine specR_guardIx idx cap hfs.lay.capN (by have := hfs.lay.cap8; omega) (by rw [hIx, hwi]) h4 (fun hi => ?_)
      exact brImax ra C hok fc.hnc fc.cNth fc.cImax (fLine 19) fc.l19 s Γ M D hx st hfs ws (recPl rec) hpl j0 j' ik idx rec hle n hn hi h1 h2 h3 h4 (by rw [hIx, hwi]) hS0 h7 h8 h9 h10 hk'

end


/-- One line: the scan phase, then the dispatch. -/
def applyLineP (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (callTo kNx fLnKB [vv kBA, vv kBN, vv kLI]) (.seq (.assign .local kTg (kbLoad 0))
    (.seq (.assign .local kS0 (kbLoad 1)) (.seq (.assign .local kIx (kbLoad 2)) (dispatchP rest))))

section
variable {F rb capD jN jL jE cap bufJ : Nat} {b : ByteArray}

/-- **One line of the frontend refines `applyLine`**: the continuation runs at `FrontSt` of the new
image, `kNx` holding the next position. -/
theorem applyLine_spec {β : Type} {k : StateD ⊕ RecordVerdict → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64} (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : FrontOK C)
    (fc : FrontCodes σ C) (s : AState) (Γ : Env) (M : Mem) (D : List MlS)
    (hD : ∀ x ∈ [kTg, kS0, kIx, kNx, kR0], x ∈ D) (st : StateD)
    (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (i : USize) (hi : i.toNat ≤ b.size) (rec : ConLeche.Frontend.LineRec) (next : USize)
    (hs : ConLeche.Frontend.scanLineFwd b i = .ok rec next) (n : Nat) (hn64 : n < 2 ^ 64)
    (hLI : Γ.get kLI = some (BitVec.ofNat 64 i.toNat)) (hLn : Γ.get kLn = some (BitVec.ofNat 64 n))
    (h1 : Γ.get fTN = some (cellA C jN)) (h2 : Γ.get fTL = some (cellA C jL)) (h3 : Γ.get fTE = some (cellA C jE))
    (h4 : Γ.get fCap = some (BitVec.ofNat 64 cap))
    (h7 : Γ.get kBA = some (cellA C bufJ)) (h8 : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (h9 : Γ.get kRB = some (cellA C rb)) (h10 : Γ.get kCapD = some (BitVec.ofNat 64 capD))
    (hk : ∀ st' s' H' (Γ' : Env), FrontSt C F rb capD jN jL jE cap bufJ b H' st' →
      (∀ y, y ∉ [kTg, kS0, kIx, kNx, kR0] → Γ'.get y = Γ.get y) →
      Γ'.get kNx = some (BitVec.ofNat 64 next.toNat) →
      SpecR (Inv (ctxH C H') s' Γ' [] D) rest s' (k (.inl st')) R) :
    SpecR (Inv C s Γ M D) (applyLineP rest) s (applyLine st rec n >>= k) R := by
  have hbuf : BufOK C bufJ b := by have := hfs.buf; rwa [ctxH_self] at this
  unfold applyLineP
  refine specR_scanPhaseK C hok bufJ b hbuf fc.hlc fc.cLnKB s Γ M D
    (fun x hx => hD x (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢; rcases hx with rfl | rfl | rfl | rfl <;> simp))
    i hi rec next hs
    hLI h7 h8 (fun wt ws wi wn hso => ?_)
  let Γ4 : Env := (kIx, wi) :: (kS0, ws) :: (kTg, wt) :: (kNx, wn) :: Γ
  have g4 : ∀ y, y ∉ [kTg, kS0, kIx, kNx, kR0] → Γ4.get y = Γ.get y := fun y hy => by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp only [Γ4, Env.get_cons, if_neg hy.1, if_neg hy.2.1, if_neg hy.2.2.1, if_neg hy.2.2.2.1]
  have hn' : ∀ y, y ≠ kTg → y ≠ kS0 → y ≠ kIx → y ≠ kNx → y ≠ kR0 → y ∉ [kTg, kS0, kIx, kNx, kR0] :=
    fun y a1 a2 a3 a4 a5 => by simp [a1, a2, a3, a4, a5]
  have L : ∀ y, y ≠ kTg → y ≠ kS0 → y ≠ kIx → y ≠ kNx → y ≠ kR0 → Γ4.get y = Γ.get y :=
    fun y a1 a2 a3 a4 a5 => g4 y (hn' y a1 a2 a3 a4 a5)
  refine dispatch_spec ra C hok hf fc s Γ4 [] D (hD _ (by simp)) st hfs rec next wt ws wi wn hso n hn64
    (by simp (config := {decide := true}) [Γ4, Env.get_cons])
    (by simp (config := {decide := true}) [Γ4, Env.get_cons])
    (by simp (config := {decide := true}) [Γ4, Env.get_cons])
    (by rw [L _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hLn)
    (by rw [L _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h1)
    (by rw [L _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h2)
    (by rw [L _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h3)
    (by rw [L _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h4)
    (by rw [L _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h7)
    (by rw [L _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h8)
    (by rw [L _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h9)
    (by rw [L _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h10)
    (fun st' s' H' Γ' hf' hag => hk st' s' H' Γ' hf' (fun y hy => by
        have hy' : y ≠ kR0 := fun e => hy (by simp [e])
        rw [hag y hy', g4 y hy])
      (by rw [hag kNx (by decide)]; simp (config := {decide := true}) only [Γ4, Env.get_cons, if_pos, if_neg]
          rw [hso.2.1]))

end

end ConPanqueque.Front
