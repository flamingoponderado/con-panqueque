import ConPanqueque.Front.Dispatch
import ConPanqueque.Front.IndLine

/-! # The inductive line's branch (tag 23)

`indL`: the line function's locals; `indCore`: the inductive line procedure (`indLine_spec`) at the line
function's entry environment; `brInd`: the dispatcher's arm. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (ExprRec LevelRec NameRec LineRec LinePayload ScanRes byteAt Key DeclRec scanIndDecl)

variable {σ : Type}

/-- The inductive line function's locals (`indMods` without the parameter `fU`). -/
def indL : List MlS := [ilTp, ilCp, ilRp, ilN, ilQ, ilP, ilNc, ilRq, ilE, ilOB, ilTh, ilTy, ilCB, ilA, ilB, ilX, ilY, fW3, fV2, ilD, ilK, ilRl, ilNu, ilRP, ilZ, ilR, kR, kCnt, fy, fz, ilT, ilL, kK, kG2, kX, kY, kKA0, kKA, kN]

theorem indL_none (C : Ctx) (jN jL jE cap : Nat) (wi ws0 : BitVec 64) (bufJ bsz rb capD : Nat) :
    ∀ y, y ∈ indL → (lineEnv C jN jL jE cap wi ws0 bufJ bsz rb capD).get y = none := by
  intro y hy; simp only [indL, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp +decide [lineEnv, ctxEnv, linePs, lineVs, Env.get]

theorem indMods_sub : ∀ x ∈ indMods, x ∈ fU :: (ctxLocals ++ indL) := by
  intro x hx
  simp only [indMods, distMods, recMods, cvMods, lbMods, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp +decide [indL, ctxLocals]

theorem scanIndDecl_ind {b : ByteArray} {i e : USize} {r : DeclRec} (h : scanIndDecl b i = .ok r e) :
    ∃ tys cts rcs, r = .ind tys cts rcs := by
  have hq := scanIndDeclLoop_eq b _ (i + 1) true 0 (2 ^ 64) (2 ^ 64) (2 ^ 64) rfl
  simp only [rescanL_top] at hq
  rw [scanIndDecl, hq] at h
  split at h
  · revert h
    generalize objLoop indDeclSpec b (i + 1) true 0 _ = x
    intro h
    cases x with
    | err er => simp [srMap] at h
    | ok sl e' => simp only [srMap, ScanRes.ok.injEq] at h; exact ⟨_, _, _, h.1.symm⟩
  · simp at h

theorem tag_23 {k : Key} {a : LActP} (hm : (k, a) ∈ lineTblP) (ht : a.tag = 23) : a = .objP 23 0 fRecInd declInd := by
  simp only [lineTblP, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> (simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h) <;>
    first | rfl | (simp [LActP.tag] at ht)

theorem indCore (C : Ctx) (hok : CtxOK C) (cc : ILCodes σ C)
    (hcL : C.code.lookup fCtorLoop = some (ctorPs.map (fun p => (p, ShapeHOL.one)), prologue ctorL (ctorCore C), .one))
    (hrL : C.code.lookup fRuleLoop = some (rulePs.map (fun p => (p, ShapeHOL.one)), prologue ruleL (ruleCore C), .one))
    (s : AState) (st : StateD) (F rb capD jN jL jE cap bufJ : Nat) (b : ByteArray)
    (hreln : TblRel C.H jN cap st.names) (hrele : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (hcapN : cap ≤ natCap) (hbuf : BufOK C bufJ b) (hdr : DeclsRel C F rb capD C.H st.decls)
    (hcapD : 8 * (rb + 1 + capD) < 2 ^ 64)
    (pos e : USize) (hpos : pos.toNat ≤ b.size) (d : DeclRec)
    (hd : scanIndDecl b pos = .ok d e) (i : Nat) :
    SpecR (Inv (σ := σ) C s (lineEnv C jN jL jE cap (BitVec.ofNat 64 (min i natCap)) (BitVec.ofNat 64 pos.toNat)
      bufJ b.size rb capD) [] (ctxLocals ++ indL)) (indLineP C) s (processLineCoreD st d)
      (fun a w s' t' => ∃ d, DeclPost C F rb capD C.H st d a w s' t') := by
  obtain ⟨tys, cts, rcs, rfl⟩ := scanIndDecl_ind hd
  exact specR_declAdd fU _ (lineEnv_U ..) (specR_mono (indLine_spec C hok cc hcL hrL s _ [] _ indMods_sub
    st F rb capD jN jE cap bufJ b hreln hrele hcap hcapN hbuf hdr hcapD pos e hpos tys cts rcs hd
    (lineEnv_TN ..) (lineEnv_TE ..) (lineEnv_Cap ..) (lineEnv_Pos ..) (lineEnv_BA ..) (lineEnv_BN ..)
    (lineEnv_RB ..) (lineEnv_CD ..)) (fun u hu => hu) (fun a w s' u ⟨_, _, hp, _⟩ => ⟨_, hp⟩))

section
variable {F rb capD jN jL jE cap bufJ : Nat} {b : ByteArray}

theorem brInd {β : Type} {k : StateD ⊕ RecordVerdict → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    {rest : ProgHOL 64} (C : Ctx) (hok : CtxOK C) (cc : ILCodes σ C)
    (hcL : C.code.lookup fCtorLoop = some (ctorPs.map (fun p => (p, ShapeHOL.one)), prologue ctorL (ctorCore C), .one))
    (hrL : C.code.lookup fRuleLoop = some (rulePs.map (fun p => (p, ShapeHOL.one)), prologue ruleL (ruleCore C), .one))
    (fL : MlS) (hcF : C.code.lookup fL =
      some (linePs.map (fun p => (p, ShapeHOL.one)), prologue indL (indLineP C), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hx : kR0 ∈ D) (st : StateD)
    (hfs : FrontSt C F rb capD jN jL jE cap bufJ b C.H st)
    (ws0 : BitVec 64) (pl : LinePayload) (hpl : PlOK b (BitVec.ofNat 64 23) ws0 pl) (j0 j' : USize) (ik : UInt8)
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
  obtain rfl := tag_23 hm hta
  obtain ⟨v, e, r', hws, hsc', rfl⟩ := objPl (sc := scanIndDecl) (wrap := LinePayload.decl) he
  subst hws
  rw [lineEnd_decl hle, applyLine_decl _ _ _ hn]
  have hbuf : BufOK C bufJ b := by have := hfs.buf; rwa [ctxH_self] at this
  have hpos : v.toNat ≤ b.size := Nat.le_of_lt (start_lt hbuf.plat (by rw [scanIndDecl] at hsc'; exact hsc'))
  exact specR_dcLineCall kR0 fL indL _ lineArgs _ rfl hx hcF
    (evAll_lineArgs Γ C jN jL jE cap _ _ bufJ b.size rb capD h1 h2 h3 h4 h5 h6 h7 h8 h9 h10)
    (indL_none C jN jL jE cap _ _ bufJ b.size rb capD) st r' hfs
    (indCore C hok cc hcL hrL s st F rb capD jN jL jE cap bufJ b hfs.tN hfs.tE hfs.lay.cap8 hfs.lay.capN hbuf hfs.dr
      hfs.lay.capD8 v e hpos r' hsc' idx)
    hk

end

end ConPanqueque.Front
