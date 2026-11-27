import ConPanqueque.Front.IndLineH

/-! # The inductive line

`indLineP C` refines the twin's `processLineCoreD st (.ind tys cts rcs)` on the supported shape (else
it hangs): one type record, safe and unnested, its constructors listed in `ctors` order with distinct
names, one recursor; every count, level-parameter list and telescope below `2⁵⁵`.  It writes the
block's stored constants (the type former, the constructors, the recursor with its rules), the
pointer block, and the record `[4, nP, block]`, appended to the registry (`indLine_spec`). -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (IdTable CVRec DeclRec IndTypeRec IndCtorRec IndRecRec RuleRec scanRules scanIndDecl
  scanIndTypes scanIndCtors scanIndRecs)

set_option autoImplicit false

variable {σ : Type}

def ilTp := ofString "il_tp"
def ilRp := ofString "il_rpos"
def ilN := ofString "il_n"
def ilE := ofString "il_e"

def ctorPart (C : Ctx) : ProgHOL 64 :=
  .seq (callTo fV2 (fItF 0) [vv kBA, vv kBN, vv ilQ])
  (lstBlkP C fTN
    (.seq (.assign .local ilCB (vv kKA0))
    (.seq (.assign .local ilN (.load .one (vv ilCB)))
    (.ite (.cmp .notEqual (vv ilN) (vv ilNc)) hang
    (distP
    (.seq (.call (some (some (.local, ilZ), none)) fCtorLoop (ctorArgs (.const 0)))
    (recP C)))))))

def typePart (C : Ctx) : ProgHOL 64 :=
  allocP C ilOB (.shift .lsl (.op .add [vv ilNc, .const 3]) (.const 3))
  (.seq (.store (vv ilOB) (.op .add [vv ilNc, .const 2]))
  (allocWr C ilE [.const 0]
  (.seq (callTo fU (fItF 5) [vv kBA, vv kBN, vv ilQ])
  (.seq (callTo fW3 (fItF 9) [vv kBA, vv kBN, vv ilQ])
  (.seq (callTo fV2 (fItF 4) [vv kBA, vv kBN, vv ilQ])
  (cvP C
    (.seq (.assign .local ilTh (vv fy))
    (.seq (.assign .local ilTy (vv fz))
    (allocWr C ilR [.const 3, vv fy, vv kKA0, vv fz, .const 0, vv ilE, .const 0, .const 0, vv ilE, .const 0]
    (.seq (.store (.op .add [vv ilOB, .const 8]) (vv ilR))
    (ctorPart C)))))))))))

/-- The inductive line's procedure (its fields read from the payload position `kPos`). -/
def indLineP (C : Ctx) : ProgHOL 64 :=
  .seq (callTo ilTp (fIdF 2) [vv kBA, vv kBN, vv kPos])
  (.seq (callTo ilCp (fIdF 0) [vv kBA, vv kBN, vv kPos])
  (.seq (callTo ilRp (fIdF 1) [vv kBA, vv kBN, vv kPos])
  (.seq (callTo ilN fIndTypesN [vv kBA, vv kBN, vv ilTp])
  (.ite (.cmp .notEqual (vv ilN) (.const 1)) hang
  (.seq (callTo ilQ fIndTypesAt [vv kBA, vv kBN, vv ilTp, .const 0])
  (.seq (callTo ilX (fItF 3) [vv kBA, vv kBN, vv ilQ])
  (.ite (.cmp .notEqual (vv ilX) (.const 0)) hang
  (.seq (callTo ilX (fItF 7) [vv kBA, vv kBN, vv ilQ])
  (.ite (.cmp .notEqual (vv ilX) (.const 0)) hang
  (.seq (callTo ilP (fItF 8) [vv kBA, vv kBN, vv ilQ])
  (.ite (.cmp .lower (vv ilP) (.const b55W))
    (.seq (callTo ilNc fIndCtorsN [vv kBA, vv kBN, vv ilCp])
    (.ite (.cmp .lower (vv ilNc) (.const b55W))
      (.seq (callTo ilN fIndRecsN [vv kBA, vv kBN, vv ilRp])
      (.ite (.cmp .notEqual (vv ilN) (.const 1)) hang
      (.seq (callTo ilRq fIndRecsAt [vv kBA, vv kBN, vv ilRp, .const 0])
      (typePart C)))) hang)) hang)))))))))))

def indMods : List MlS := [ilTp, ilCp, ilRp, ilN, ilQ, ilP, ilNc, ilRq, ilE, ilOB, ilTh, ilTy, ilCB] ++ distMods ++ recMods

/-- What the line's run establishes about the pushed block beyond its encoding: its shape and bounds. -/
structure IndBounds (s : AState) (blk : List IConstantInfo) (nP : Nat) : Prop where
  np : nP < 2 ^ 55
  len : blk.length < 2 ^ 55 + 2
  lps : ∀ ci ∈ blk, ci.toConstantVal.levelParams.length < 2 ^ 55
  tele : ∀ ci ∈ blk, ∀ e, denoteE s.store ci.toConstantVal.type = some e → ConLeche.Frontend.indPiTeleLen e < 2 ^ 55
  ctor : ∀ ci ∈ blk, ∀ cv np nf T, ci = .ctorInfo cv np nf T → np < 2 ^ 55 ∧ nf < 2 ^ 55
  rcs : ∀ ci ∈ blk, ∀ cv mi rp k rules, ci = .recInfo cv mi rp k rules →
    mi < 2 ^ 56 ∧ rp < 2 ^ 57 ∧ rules.length < 2 ^ 55 ∧ ∀ ru ∈ rules, ru.nfields < 2 ^ 55

theorem IndBounds.toP {s : AState} {blk : List IConstantInfo} {nP : Nat} (h : IndBounds s blk nP) :
    IndBoundsP blk nP := ⟨h.np, h.len, h.lps, h.ctor, h.rcs⟩

/-- The line's records in the supported shape. -/
def IndShape (st : StateD) (s : AState) (tys : List IndTypeRec) (cts : List IndCtorRec) (rcs : List IndRecRec)
    (blk : List IConstantInfo) (nP : Nat) : Prop :=
  ∃ t r T, tys = [t] ∧ rcs = [r] ∧ st.names.get? t.cv.name = some T ∧ blk = indBlockD st t cts r T ∧
    nP = t.numParams ∧ cts.length < 2 ^ 55 ∧ r.numParams = t.numParams ∧ r.numMotives = 1 ∧
    r.numMinors = cts.length ∧ r.numIndices < 2 ^ 55 ∧ r.rules.length < 2 ^ 55 ∧ IndBounds s blk nP


theorem nodup_of_map' {α β : Type} (f : α → β) : ∀ {l : List α}, (l.map f).Nodup → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    rw [List.map_cons, List.nodup_cons] at h
    exact List.nodup_cons.mpr ⟨fun ha => h.1 (List.mem_map_of_mem ha), nodup_of_map' f h.2⟩

theorem indBlock_cases {st : StateD} {t : IndTypeRec} {cts : List IndCtorRec} {r : IndRecRec} {T : NIdx}
    {ci : IConstantInfo} (h : ci ∈ indBlockD st t cts r T) :
    ci = .indInfo (cvOfD st t.cv) {} ∨
      (∃ j, ∃ hj : j < cts.length, ci = .ctorInfo (cvOfD st cts[j].cv) cts[j].numParams cts[j].numFields T) ∨
      ci = recInfoD st r := by
  simp only [indBlockD, List.mem_append, List.mem_singleton, List.mem_map] at h
  rcases h with (rfl | ⟨c, hc, rfl⟩) | rfl
  · exact Or.inl rfl
  · obtain ⟨j, hj, e⟩ := List.getElem_of_mem hc
    exact Or.inr (Or.inl ⟨j, hj, by rw [e]⟩)
  · exact Or.inr (Or.inr rfl)

theorem indLine_spec (C : Ctx) (hok : CtxOK C) (cc : ILCodes σ C)
    (hcL : C.code.lookup fCtorLoop = some (ctorPs.map (fun p => (p, ShapeHOL.one)), prologue ctorL (ctorCore C), .one))
    (hrL : C.code.lookup fRuleLoop = some (rulePs.map (fun p => (p, ShapeHOL.one)), prologue ruleL (ruleCore C), .one))
    (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (hD : ∀ x ∈ indMods, x ∈ D)
    (st : StateD) (F rb capD jN jE cap bufJ : Nat) (b : ByteArray)
    (hreln : TblRel C.H jN cap st.names) (hrele : TblRel C.H jE cap st.exprs) (hcap : 8 * cap < 2 ^ 64)
    (hcapN : cap ≤ natCap) (hbuf : BufOK C bufJ b) (hdr : DeclsRel C F rb capD C.H st.decls)
    (hcapD : 8 * (rb + 1 + capD) < 2 ^ 64)
    (pos e : USize) (hpos : pos.toNat ≤ b.size) (tys : List IndTypeRec) (cts : List IndCtorRec) (rcs : List IndRecRec)
    (hd : scanIndDecl b pos = .ok (.ind tys cts rcs) e)
    (hTN : Γ.get fTN = some (cellA C jN)) (hTE : Γ.get fTE = some (cellA C jE))
    (hC : Γ.get fCap = some (BitVec.ofNat 64 cap)) (hPos : Γ.get kPos = some (BitVec.ofNat 64 pos.toNat))
    (hBA : Γ.get kBA = some (cellA C bufJ)) (hBN : Γ.get kBN = some (BitVec.ofNat 64 b.size))
    (hRB : Γ.get kRB = some (cellA C rb)) (hCD : Γ.get kCapD = some (BitVec.ofNat 64 capD)) :
    SpecR (Inv (σ := σ) C s Γ M D) (indLineP C) s (processLineCoreD st (.ind tys cts rcs))
      (fun a w s' t' => ∃ blk nP, DeclPost C F rb capD C.H st (.indDecl blk nP) a w s' t' ∧
        IndShape st s tys cts rcs blk nP) := by
  have hplat := hbuf.plat
  have hsm := hbuf.small
  have hlay := hok.heapLay
  have hFl : F ≤ C.H.length := hdr.2.2.2.1
  have hk0 : ∀ y, y ∉ indMods → ∀ (Δ : Env), (∀ z, z ∉ indMods → Δ.get z = Γ.get z) → Δ.get y = Γ.get y :=
    fun y hy Δ h => h y hy
  unfold indLineP
  -- the three lists
  refine specR_scan3 hok bufJ b hbuf ilTp (fIdF 2) kPos _ pos.toNat _ (hD ilTp (by decide))
    (cc.declF 2 (by decide)) hBA hBN hPos
    (fun u hb hu l1 l2 l3 => indDeclField_sound u _ b hplat hb (cc.sc u hu) (cc.ic u hu) pos hpos l1 l2 l3 2 (by decide)
      tys cts rcs e hd) (fun wT hwT => ?_)
  simp only [IndDeclField] at hwT
  obtain ⟨pT, eT, rfl, hpT⟩ := hwT
  refine specR_scan3 hok bufJ b hbuf ilCp (fIdF 0) kPos _ pos.toNat _ (hD ilCp (by decide))
    (cc.declF 0 (by decide)) (by envg; exact hBA) (by envg; exact hBN) (by envg; exact hPos)
    (fun u hb hu l1 l2 l3 => indDeclField_sound u _ b hplat hb (cc.sc u hu) (cc.ic u hu) pos hpos l1 l2 l3 0 (by decide)
      tys cts rcs e hd) (fun wC hwC => ?_)
  simp only [IndDeclField] at hwC
  obtain ⟨pC, eC, rfl, hpC⟩ := hwC
  refine specR_scan3 hok bufJ b hbuf ilRp (fIdF 1) kPos _ pos.toNat _ (hD ilRp (by decide))
    (cc.declF 1 (by decide)) (by envg; exact hBA) (by envg; exact hBN) (by envg; exact hPos)
    (fun u hb hu l1 l2 l3 => indDeclField_sound u _ b hplat hb (cc.sc u hu) (cc.ic u hu) pos hpos l1 l2 l3 1 (by decide)
      tys cts rcs e hd) (fun wR hwR => ?_)
  simp only [IndDeclField] at hwR
  obtain ⟨pRs, eRs, rfl, hpRs⟩ := hwR
  -- one type
  refine specR_scan3 hok bufJ b hbuf ilN fIndTypesN ilTp _ pT.toNat _ (hD ilN (by decide)) cc.typesN
    (by envg; exact hBA) (by envg; exact hBN) (by envg)
    (fun u hb hu l1 l2 l3 => indTypeCount_sound u _ b hplat hb (cc.sc u hu) (cc.ic u hu) pT eT tys hpT l1 l2 l3)
    (fun wn ⟨hwn, hnb⟩ => ?_)
  subst hwn
  refine specR_eqcGuardI ilN (BitVec.ofNat 64 tys.length) 1 (by envg) (fun he1 => ?_)
  have htl : tys.length = 1 := ofNat_inj64 (by omega) (by decide) he1
  obtain ⟨t, rfl⟩ := List.length_eq_one_iff.mp htl
  refine specR_scan4 hok bufJ b hbuf ilQ fIndTypesAt ilTp (.const 0) _ pT.toNat 0 _ (hD ilQ (by decide))
    cc.typesAt (by envg; exact hBA) (by envg; exact hBN) (by envg) rfl
    (fun u hb hu l1 l2 l3 l4 => indTypeAt_sound u _ b hplat hb (cc.sc u hu) (cc.ic u hu) pT eT [t] hpT 0 (by decide)
      l1 l2 l3 l4) (fun wq hq => ?_)
  obtain ⟨q, eq, rfl, hqb, hsq⟩ := hq (by simp)
  simp only [List.getElem_cons_zero] at hsq
  refine specR_scan3 hok bufJ b hbuf ilX (fItF 3) ilQ _ q.toNat _ (hD ilX (by decide)) (cc.typeF 3 (by decide))
    (by envg; exact hBA) (by envg; exact hBN) (by envg)
    (fun u hb hu l1 l2 l3 => indTypeField_sound u _ b hplat hb (cc.sc u hu) q hqb l1 l2 l3 3 (by decide) t eq hsq)
    (fun w3 hw3 => ?_)
  simp only [IndTypeField] at hw3; subst hw3
  refine specR_eqcGuardI ilX (bw (t.isUnsafe = true)) 0 (by envg) (fun hu0 => ?_)
  have hu : t.isUnsafe = false := by cases h : t.isUnsafe <;> simp_all [bw]
  refine specR_scan3 hok bufJ b hbuf ilX (fItF 7) ilQ _ q.toNat _ (hD ilX (by decide)) (cc.typeF 7 (by decide))
    (by envg; exact hBA) (by envg; exact hBN) (by envg)
    (fun u hb hu l1 l2 l3 => indTypeField_sound u _ b hplat hb (cc.sc u hu) q hqb l1 l2 l3 7 (by decide) t eq hsq)
    (fun w7 hw7 => ?_)
  simp only [IndTypeField] at hw7; subst hw7
  refine specR_eqcGuardI ilX (Scan.natW t.numNested) 0 (by envg) (fun hn0 => ?_)
  have hnest : t.numNested = 0 := natW_eq_small (n := 0) (by unfold B55; decide) hn0
  refine specR_scan3 hok bufJ b hbuf ilP (fItF 8) ilQ _ q.toNat _ (hD ilP (by decide)) (cc.typeF 8 (by decide))
    (by envg; exact hBA) (by envg; exact hBN) (by envg)
    (fun u hb hu l1 l2 l3 => indTypeField_sound u _ b hplat hb (cc.sc u hu) q hqb l1 l2 l3 8 (by decide) t eq hsq)
    (fun w8 hw8 => ?_)
  simp only [IndTypeField] at hw8; subst hw8
  refine specR_ltGuardI ilP (Scan.natW t.numParams) b55W (by envg) (fun hl8 => ?_)
  obtain ⟨hnP, hnPw⟩ := natW_small (by rw [b55W_toNat] at hl8; exact hl8)
  rw [hnPw]
  refine specR_scan3 hok bufJ b hbuf ilNc fIndCtorsN ilCp _ pC.toNat _ (hD ilNc (by decide)) cc.ctorsN
    (by envg; exact hBA) (by envg; exact hBN) (by envg)
    (fun u hb hu l1 l2 l3 => indCtorCount_sound u _ b hplat hb (cc.sc u hu) (cc.ic u hu) pC eC cts hpC l1 l2 l3)
    (fun wc ⟨hwc, hcb⟩ => ?_)
  subst hwc
  refine specR_ltGuardI ilNc (BitVec.ofNat 64 cts.length) b55W (by envg) (fun hlc => ?_)
  have hnC : cts.length < B55 := lt_b55 rfl (by omega) hlc
  refine specR_scan3 hok bufJ b hbuf ilN fIndRecsN ilRp _ pRs.toNat _ (hD ilN (by decide)) cc.recsN
    (by envg; exact hBA) (by envg; exact hBN) (by envg)
    (fun u hb hu l1 l2 l3 => indRecCount_sound u _ b hplat hb (cc.sc u hu) (cc.ic u hu) pRs eRs rcs hpRs l1 l2 l3)
    (fun wr ⟨hwr, hrb⟩ => ?_)
  subst hwr
  refine specR_eqcGuardI ilN (BitVec.ofNat 64 rcs.length) 1 (by envg) (fun hr1 => ?_)
  have hrl : rcs.length = 1 := ofNat_inj64 (by omega) (by decide) hr1
  obtain ⟨r, rfl⟩ := List.length_eq_one_iff.mp hrl
  refine specR_scan4 hok bufJ b hbuf ilRq fIndRecsAt ilRp (.const 0) _ pRs.toNat 0 _ (hD ilRq (by decide))
    cc.recsAt (by envg; exact hBA) (by envg; exact hBN) (by envg) rfl
    (fun u hb hu l1 l2 l3 l4 => indRecAt_sound u _ b hplat hb (cc.sc u hu) (cc.ic u hu) pRs eRs [r] hpRs 0 (by decide)
      l1 l2 l3 l4) (fun wqr hqr => ?_)
  obtain ⟨qR, eR, rfl, hqR, hsR⟩ := hqr (by simp)
  simp only [List.getElem_cons_zero] at hsR
  -- the pointer block
  unfold typePart
  have hnC' : cts.length < 2 ^ 55 := hnC
  have hnP' : t.numParams < 2 ^ 55 := hnP
  refine specR_allocI (C := C) ilOB (.shift .lsl (.op .add [vv ilNc, .const 3]) (.const 3)) (cts.length + 3) (by omega)
    (hD ilOB (by decide)) (fun v => by
      simp only [sev, vv]; envg
      simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.map_some,
        show (3 : BitVec 64).toNat = 3 from rfl, show (3 : Nat) < 64 by decide, ite_true]
      congr 1; apply BitVec.eq_of_toNat_eq
      simp [BitVec.toNat_shiftLeft, BitVec.toNat_add, Nat.shiftLeft_eq]; omega)
    (fun H2 wsR hp2 hwl hcap2 => ?_)
  have hob : C.H.length ≤ H2.length := hp2.length_le
  refine specR_heapStoreI (C := ctxH C (H2 ++ wsR)) (ctxOK_H hok _) (vv ilOB) (.op .add [vv ilNc, .const 2]) H2.length
    (by show H2.length < (H2 ++ wsR).length; simp [hwl]) (BitVec.ofNat 64 (cts.length + 2))
    (by simp [sev, vv, ConPanqueque.T.Env.get_cons]; rfl)
    (by simp only [sev, vv]; envg
        simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        congr 1; apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]) ?_
  let ob := H2.length
  let X := ob + cts.length + 3
  let H2' := (H2 ++ wsR).set ob (BitVec.ofNat 64 (cts.length + 2))
  have hl2' : H2'.length = X := by simp [H2', hwl, X, ob]; omega
  have hp2' : C.H <+: H2' := prefix_set_ge (hp2.trans (List.prefix_append _ _)) ob hob _
  have hob2 : H2'[ob]? = some (BitVec.ofNat 64 (cts.length + 2)) := by simp [H2', List.getElem?_set, hwl, ob]
  -- the empty block
  refine specR_allocWrI (ctxH C H2') (ctxOK_H hok H2') ilE (hD ilE (by decide)) [.const 0] [0] rfl (by simp)
    (fun v i hi => by simp at hi; subst hi; rfl) (fun H3 oe hp3 hoe _ hw3 => ?_)
  have hoe' : X ≤ oe := by have : H2'.length ≤ oe := hoe; omega
  have he3 : H3[oe]? = some 0 := by simpa using hw3 0 (by simp)
  have hp03 : C.H <+: H3 := hp2'.trans hp3
  have hok3 := ctxOK_H hok H3
  have hbuf3 := bufOK_prefix hbuf hp03
  -- the type former
  refine specR_scan3 hok3 bufJ b hbuf3 fU (fItF 5) ilQ _ q.toNat _ (hD fU (by decide)) (cc.typeF 5 (by decide))
    (by envg; exact hBA) (by envg; exact hBN) (by envg)
    (fun u hb hu l1 l2 l3 => indTypeField_sound u _ b hplat hb (cc.sc u hu) q hqb l1 l2 l3 5 (by decide) t eq hsq)
    (fun w5 hw5 => ?_)
  simp only [IndTypeField] at hw5; subst hw5
  refine specR_scan3 hok3 bufJ b hbuf3 fW3 (fItF 9) ilQ _ q.toNat _ (hD fW3 (by decide)) (cc.typeF 9 (by decide))
    (by envg; exact hBA) (by envg; exact hBN) (by envg)
    (fun u hb hu l1 l2 l3 => indTypeField_sound u _ b hplat hb (cc.sc u hu) q hqb l1 l2 l3 9 (by decide) t eq hsq)
    (fun w9 hw9 => ?_)
  simp only [IndTypeField] at hw9; subst hw9
  refine specR_scan3 hok3 bufJ b hbuf3 fV2 (fItF 4) ilQ _ q.toNat _ (hD fV2 (by decide)) (cc.typeF 4 (by decide))
    (by envg; exact hBA) (by envg; exact hBN) (by envg)
    (fun u hb hu l1 l2 l3 => indTypeField_sound u _ b hplat hb (cc.sc u hu) q hqb l1 l2 l3 4 (by decide) t eq hsq)
    (fun w4 hw4 => ?_)
  simp only [IndTypeField] at hw4
  refine cvP_spec (ctxH C H3) hok3 cc.nc cc.cN cc.cI s _ [] D (fun x hx => hD x (by
      simp only [indMods, recMods, List.mem_append]; exact Or.inr (Or.inr hx)))
    st jN jE cap bufJ b (tblRel_prefix hreln hp03) (tblRel_prefix hrele hp03) hcap hcapN hbuf3 t.cv w4 hw4
    (by envg; exact hTN) (by envg; exact hTE) (by envg; exact hC) (by envg) (by envg) (by envg)
    (by envg; exact hBA) (by envg; exact hBN) _
    (fun H4 olT Γ4 T tyh nT hp4 holT hblkT hT hty hlpT hlplT hnT hrunT hdenT h4y h4z h4T h4K h4k => ?_)
  have a1 : Γ4.get kBA = some (cellA C bufJ) := by rw [h4k _ (by decide)]; envg; exact hBA
  have a2 : Γ4.get kBN = some (BitVec.ofNat 64 b.size) := by rw [h4k _ (by decide)]; envg; exact hBN
  have a3 : Γ4.get fTN = some (cellA C jN) := by rw [h4k _ (by decide)]; envg; exact hTN
  have a4 : Γ4.get fTE = some (cellA C jE) := by rw [h4k _ (by decide)]; envg; exact hTE
  have a5 : Γ4.get fCap = some (BitVec.ofNat 64 cap) := by rw [h4k _ (by decide)]; envg; exact hC
  have a6 : Γ4.get kRB = some (cellA C rb) := by rw [h4k _ (by decide)]; envg; exact hRB
  have a7 : Γ4.get kCapD = some (BitVec.ofNat 64 capD) := by rw [h4k _ (by decide)]; envg; exact hCD
  have a8 : Γ4.get ilQ = some (BitVec.ofNat 64 q.toNat) := by rw [h4k _ (by decide)]; envg
  have a9 : Γ4.get ilRq = some (BitVec.ofNat 64 qR.toNat) := by rw [h4k _ (by decide)]; envg
  have a10 : Γ4.get ilP = some (BitVec.ofNat 64 t.numParams) := by rw [h4k _ (by decide)]; envg
  have a11 : Γ4.get ilNc = some (BitVec.ofNat 64 cts.length) := by rw [h4k _ (by decide)]; envg
  have a12 : Γ4.get ilCp = some (BitVec.ofNat 64 pC.toNat) := by rw [h4k _ (by decide)]; envg
  have a13 : Γ4.get ilOB = some (cellA C ob) := by rw [h4k _ (by decide)]; envg; rfl
  have a14 : Γ4.get ilE = some (cellA C oe) := by rw [h4k _ (by decide)]; envg; rfl
  have hp34 : H3 <+: H4 := hp4
  have holT' : H3.length ≤ olT := holT
  refine specR_assignI ilTh (vv fy) (Enc.idxW T) (hD ilTh (by decide)) (by simpa [sev, vv] using h4y) ?_
  refine specR_assignI ilTy (vv fz) (Enc.idxW tyh) (hD ilTy (by decide)) (by simp only [sev, vv]; envg; exact h4z) ?_
  refine specR_allocWrI (ctxH C H4) (ctxOK_H hok H4) ilR (hD ilR (by decide))
    [.const 3, vv fy, vv kKA0, vv fz, .const 0, vv ilE, .const 0, .const 0, vv ilE, .const 0]
    [BitVec.ofNat 64 3, Enc.idxW T, cellA C olT, Enc.idxW tyh, 0, cellA C oe, 0, 0, cellA C oe, 0] rfl (by simp)
    (fun v i hi => ?_) (fun H5 oT hp5 hoT _ hw5 => ?_)
  · simp only [List.length_cons, List.length_nil] at hi
    rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [List.getElem_cons_succ, List.getElem_cons_zero, List.getD_cons_succ, List.getD_cons_zero, sev, vv] <;>
    envg
    · exact h4y
    · exact h4K
    · exact h4z
    · exact a14
    · exact a14
  have hoT' : H4.length ≤ oT := hoT
  have hl5 : H4.length ≤ H5.length := hp5.length_le
  have hl4 : H3.length ≤ H4.length := hp34.length_le
  have hl3 : H2'.length ≤ H3.length := hp3.length_le
  refine specR_heapStoreI (C := ctxH (ctxH C H4) H5) (ctxOK_H hok H5) (.op .add [vv ilOB, .const 8]) (vv ilR) (ob + 1)
    (by show ob + 1 < H5.length; omega) (cellA C oT)
    (by simp only [sev, vv]; envg; rw [a13]; simp only [Option.bind_eq_bind, Option.bind_some, Option.pure_def]
        rw [show (8 : BitVec 64) = 8 from rfl, cellA_add8]; rfl)
    (by simp only [sev, vv]; envg; rfl) ?_
  let H5' := H5.set (ob + 1) (cellA C oT)
  have hl5' : H5'.length = H5.length := by simp [H5']
  have hp05 : C.H <+: H5' := prefix_set_ge (hp03.trans (hp34.trans hp5)) _ (by omega) _
  -- the type former's record, robust above X
  have hcvT := cvOfD_eq st t.cv T tyh hT hty
  have hrT : RCIE X C H5' oT (.indInfo (cvOfD st t.cv) {}) := by
    refine rcie_keep (rcie_ind X C H5 oT olT oe (cvOfD st t.cv) (by omega) (by omega) hoe' (fun i hi => ?_) ?_ ?_)
      (keepsAbove_set_lt (by omega) _)
    · rw [hcvT]; have := hw5 i (by simpa using hi); simpa using this
    · rw [tWords_cvOfD]; exact blkAt_mono hblkT hp5
    · exact getElem?_prefix (hp34.trans hp5) (getElem?_prefix (List.prefix_refl _) he3)
  have hob5 : H5'[ob]? = some (BitVec.ofNat 64 (cts.length + 2)) :=
    get_set_ne' (getElem?_prefix (hp3.trans (hp34.trans hp5)) hob2) (by omega)
  have hslotT : H5'[ob + 1]? = some (cellA C oT) := by simp [H5', List.getElem?_set]; omega
  -- the constructor names of the type
  unfold ctorPart
  have hok5 := ctxOK_H hok H5'
  have hbuf5 := bufOK_prefix hbuf hp05
  refine specR_scan3 hok5 bufJ b hbuf5 fV2 (fItF 0) ilQ _ q.toNat _ (hD fV2 (by decide)) (cc.typeF 0 (by decide))
    (by envg; exact a1) (by envg; exact a2) (by envg; exact a8)
    (fun u hb hu l1 l2 l3 => indTypeField_sound u _ b hplat hb (cc.sc u hu) q hqb l1 l2 l3 0 (by decide) t eq hsq)
    (fun w0 hw0 => ?_)
  simp only [IndTypeField] at hw0
  have hctl : t.ctors.length < 2 ^ 60 := by
    rcases hw0 with ⟨p0, e0, -, hsc0⟩ | ⟨h0, -⟩
    · have := scanNatList_len hsc0; omega
    · rw [h0]; simp
  change SpecR _ (lstBlkP (ctxH C H5') fTN _) _ _ _
  refine lstBlk_spec (ctxH C H5') hok5 cc.nc cc.cN s _ [] D (fun x hx => hD x (by
      simp only [indMods, recMods, cvMods, List.mem_append]; simp [hx]))
    fTN (by decide) st.names jN cap (tblRel_prefix hreln hp05) hcap hcapN bufJ b hbuf5 t.ctors hctl w0 hw0
    (by envg; exact a3) (by envg; exact a5) (by envg; exact a1) (by envg; exact a2) (by envg) _
    (fun H6 cb Γ6 hp6 hcb6 hblkC hallC hka6 hkeep6 => ?_)
  have hl6 : H5'.length ≤ H6.length := hp6.length_le
  have hcb6' : H5'.length ≤ cb := hcb6
  have b0 : ∀ y, y ∉ lbMods → y ≠ fV2 → y ≠ ilR → y ≠ ilTy → y ≠ ilTh → Γ6.get y = Γ4.get y :=
    fun y hy h1 h2 h3 h4 => by
      rw [hkeep6 y hy]; simp only [ConPanqueque.T.Env.get_cons, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3,
        ite_eq_right h4]
  refine specR_assignI ilCB (vv kKA0) (cellA C cb) (hD ilCB (by decide)) (by simp only [sev, vv]; exact hka6) ?_
  have hlenW : (tWords st.names t.ctors).length = t.ctors.length := by simp [tWords]
  have c11 : Γ6.get ilNc = some (BitVec.ofNat 64 cts.length) := by
    rw [b0 _ (by decide) (by decide) (by decide) (by decide) (by decide)]; exact a11
  refine specR_heapLoadV ilN (vv ilCB) cb (BitVec.ofNat 64 t.ctors.length) (by rw [← hlenW]; exact hblkC.1)
    (hD ilN (by decide)) (by simp only [sev, vv]; envg; rfl) ?_
  refine specR_eqGuardI ilN ilNc (BitVec.ofNat 64 t.ctors.length) (BitVec.ofNat 64 cts.length) (by envg)
    (by envg; exact c11) (fun hlc => ?_)
  have hlen : t.ctors.length = cts.length := ofNat_inj64 (by omega) (by omega) hlc
  have hwl' : (tWords st.names t.ctors).length = cts.length := by rw [hlenW, hlen]
  refine distP_spec (ctxH (ctxH C H5') H6) s _ [] D (fun x hx => hD x (by
      simp only [indMods, List.mem_append]; simp [hx])) cb (tWords st.names t.ctors) hblkC
    (by rw [hwl']; exact hnC) (by envg; rfl) (by rw [hwl']; envg; exact c11) _ (fun Γ8 hnd hk8 => ?_)
  have e4 : ∀ y, y ∉ distMods → y ∉ lbMods → y ∉ [ilN, ilCB, fV2, ilR, ilTy, ilTh] → Γ8.get y = Γ4.get y :=
    fun y h1 h2 h3 => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h3
      rw [hk8 y h1]
      simp only [ConPanqueque.T.Env.get_cons, ite_eq_right h3.1, ite_eq_right h3.2.1]
      exact b0 y h2 h3.2.2.1 h3.2.2.2.1 h3.2.2.2.2.1 h3.2.2.2.2.2
  have f1 : Γ8.get kBA = some (cellA C bufJ) := (e4 _ (by decide) (by decide) (by decide)).trans a1
  have f2 : Γ8.get kBN = some (BitVec.ofNat 64 b.size) := (e4 _ (by decide) (by decide) (by decide)).trans a2
  have f3 : Γ8.get fTN = some (cellA C jN) := (e4 _ (by decide) (by decide) (by decide)).trans a3
  have f4 : Γ8.get fTE = some (cellA C jE) := (e4 _ (by decide) (by decide) (by decide)).trans a4
  have f5 : Γ8.get fCap = some (BitVec.ofNat 64 cap) := (e4 _ (by decide) (by decide) (by decide)).trans a5
  have f6 : Γ8.get kRB = some (cellA C rb) := (e4 _ (by decide) (by decide) (by decide)).trans a6
  have f7 : Γ8.get kCapD = some (BitVec.ofNat 64 capD) := (e4 _ (by decide) (by decide) (by decide)).trans a7
  have f9 : Γ8.get ilRq = some (BitVec.ofNat 64 qR.toNat) := (e4 _ (by decide) (by decide) (by decide)).trans a9
  have f10 : Γ8.get ilP = some (BitVec.ofNat 64 t.numParams) := (e4 _ (by decide) (by decide) (by decide)).trans a10
  have f11 : Γ8.get ilNc = some (BitVec.ofNat 64 cts.length) := (e4 _ (by decide) (by decide) (by decide)).trans a11
  have f12 : Γ8.get ilCp = some (BitVec.ofNat 64 pC.toNat) := (e4 _ (by decide) (by decide) (by decide)).trans a12
  have f13 : Γ8.get ilOB = some (cellA C ob) := (e4 _ (by decide) (by decide) (by decide)).trans a13
  have f14 : Γ8.get ilCB = some (cellA C cb) := by rw [hk8 _ (by decide)]; envg
  have f15 : Γ8.get ilTh = some (Enc.idxW T) := by rw [hk8 _ (by decide)]; envg; rw [hkeep6 _ (by decide)]; envg
  have f16 : Γ8.get ilTy = some (Enc.idxW tyh) := by rw [hk8 _ (by decide)]; envg; rw [hkeep6 _ (by decide)]; envg
  -- the constructors
  have hp06 : C.H <+: H6 := hp05.trans hp6
  have hX6 : X ≤ H6.length := by omega
  refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => processLineCoreD st (.ind [t] cts [r])) rfl ?_
  refine specR_protoCall (C := ctxH C H6) ilZ fCtorLoop ctorPs (by decide) ctorL (ctorCore C) (ctorArgs (.const 0))
    (ctorVals (ctxH C H6) bufJ b.size jN jE cap pC.toNat 0 cts.length cb ob T t.numParams) rfl (hD ilZ (by decide))
    hcL ?_ (ctorL_none (ctxH C H6) bufJ b.size jN jE cap pC.toNat 0 cts.length cb ob T t.numParams)
    (CtorPost (ctxH C H6) s st t cts T ob X 0)
    (fun _ _ _ _ _ ⟨h0, H'', h1, h2⟩ => ⟨h0, H'', sr_of_eq h1 rfl rfl rfl rfl, h2⟩)
    (ctorCore_spec C hok cc hcL s st jN jE cap bufJ b hreln hrele hcap hcapN hbuf t cts T pC eC hpC hnC hnP hlen cb ob
      hob (by omega) cts.length 0 H6 (by omega) (Nat.zero_le _) hp06 hblkC hX6)
    (fun _ _ s'' H'' => s'' = s ∧ CtorFacts (ctxH C H6) s st t cts T ob X 0 H'')
    (fun a w s'' u ⟨h0, H'', h1, h2⟩ => ⟨H'', ⟨h0, h2⟩, by rw [h0]; exact h1⟩) ?_
  · simp only [EvAll, ctorArgs, ctorVals, sev, vv]
    exact ⟨f1, f2, f3, f4, f5, f12, rfl, f11, f14, f13, f15, f10, trivial⟩
  intro a w s'' H7 ⟨h0, hl7, hpres7, hall7⟩
  subst s''
  have hl7' : H6.length ≤ H7.length := hl7
  have hpres7' : ∀ c v, H6[c]? = some v → (c < ob + 2 + 0 ∨ X ≤ c) → H7[c]? = some v := hpres7
  have hp07 : C.H <+: H7 := prefix_of_agree (by have := hp06.length_le; omega) (fun c hc => by
    obtain ⟨v, hv⟩ : ∃ v, C.H[c]? = some v := ⟨C.H[c], List.getElem?_eq_getElem hc⟩
    rw [hv, hpres7' c v (getElem?_prefix hp06 hv) (by omega)])
  let osC : List Nat := List.ofFn (fun j : Fin cts.length => Classical.choose (hall7 j.1 (Nat.zero_le _) j.2))
  have hosC : ∀ j (hj : j < cts.length) (ho : j < osC.length), X ≤ osC[j] ∧ H7[ob + 2 + j]? = some (cellA C osC[j]) ∧
      RCIE X C H7 osC[j] (.ctorInfo (cvOfD st cts[j].cv) cts[j].numParams cts[j].numFields T) ∧
      CtorOK st s t T cts[j] j ((st.names.get? (t.ctors.getD j 0)).getD default) := by
    intro j hj ho
    have := Classical.choose_spec (hall7 j (Nat.zero_le _) hj)
    simp only [osC, List.getElem_ofFn]
    exact this
  have hosCl : osC.length = cts.length := by simp [osC]
  have hco : ∀ j (hj : j < cts.length), CtorOK st s t T cts[j] j ((st.names.get? (t.ctors.getD j 0)).getD default) :=
    fun j hj => (hosC j hj (by omega)).2.2.2
  let os := oT :: osC
  have hosl : os.length = cts.length + 1 := by simp [os, hosCl]
  have hk57 : KeepsAbove X H5' H7 := fun c hc v hv => hpres7' c v (getElem?_prefix hp6 hv) (Or.inr hc)
  have hos7 : ∀ i (hi : i < os.length), H7[ob + 1 + i]? = some (cellA C os[i]) := by
    intro i hi
    cases i with
    | zero => exact hpres7' _ _ (getElem?_prefix hp6 hslotT) (Or.inl (by omega))
    | succ j =>
      have hj : j < cts.length := by simp [os, hosCl] at hi; omega
      rw [show ob + 1 + (j + 1) = ob + 2 + j by omega]
      exact (hosC j hj (by omega)).2.1
  have hhead7 : ∀ i (hi : i < (indHead st t cts T).length) (ho : i < os.length),
      RCIE X C H7 os[i] (indHead st t cts T)[i] := by
    intro i hi ho
    cases i with
    | zero => simpa [os, indHead] using rcie_keep hrT hk57
    | succ j =>
      have hj : j < cts.length := by simp [os, hosCl] at ho; omega
      simpa [os, indHead] using (hosC j hj (by omega)).2.2.1
  have hob7 : H7[ob]? = some (BitVec.ofNat 64 (cts.length + 2)) :=
    hpres7' _ _ (getElem?_prefix hp6 hob5) (Or.inl (by omega))
  -- the twin's facts
  let ns : List NIdx := t.ctors.map (fun x => (st.names.get? x).getD default)
  have hns : ns.length = cts.length := by simp [ns, hlen]
  have hgetD : ∀ j (hj : j < t.ctors.length), t.ctors.getD j 0 = t.ctors[j] := fun j hj => by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  have hnl : ∀ j (hj : j < cts.length), st.names.get? (t.ctors[j]'(by omega)) = some (ns[j]'(by omega)) ∧
      st.names.get? cts[j].cv.name = some (ns[j]'(by omega)) := by
    intro j hj
    have hs := hallC j (by omega)
    obtain ⟨h, hh⟩ := Option.isSome_iff_exists.mp hs
    refine ⟨by simp [ns, hh], ?_⟩
    have := (hco j hj).nm
    rw [hgetD j (by omega)] at this
    simp only [ns, List.getElem_map]; exact this
  have hnd' : ns.Nodup := by
    have e : tWords st.names t.ctors = ns.map Enc.idxW := by simp [tWords, ns]
    rw [e] at hnd; exact nodup_of_map' _ hnd
  have hlpT' : ∀ x ∈ t.cv.levelParams, (st.names.get? x).isSome := fun x hx => by
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem hx; rw [← e]; exact hlpT j hj
  have hlpC' : ∀ c ∈ cts, ∀ x ∈ c.cv.levelParams, (st.names.get? x).isSome := fun c hc => by
    obtain ⟨j, hj, e⟩ := List.getElem_of_mem hc; rw [← e]; exact (hco j hj).lps
  have hm : RecTwin st s t cts r tyh → processLineCoreD st (.ind [t] cts [r]) s =
      (pure (.inl { st with decls := st.decls.push (.indDecl (indBlockD st t cts r T) t.numParams) }) :
        AM (StateD ⊕ RecordVerdict)) s := by
    intro tw
    obtain ⟨rn, hrn, hview⟩ := tw.rn
    rw [processInd_ok st s t cts r T tyh rn ns hu hnest hT hty hlpT' hlpC' tw.lps hlen hns hnl hnd'
      (fun j hj => (hco j hj).cidx) (fun j hj => (hco j hj).ind)
      (fun j hj => let ⟨ch, h1, h2, _⟩ := (hco j hj).ty; ⟨ch, h1, h2⟩) hrn hview
      (let ⟨rty, _, h1, _⟩ := tw.tele; by rw [h1]; rfl) tw.rp tw.rm tw.rmin tw.idx tw.rules
      (fun c hc => by obtain ⟨j, hj, e⟩ := List.getElem_of_mem hc; rw [← e]
                      obtain ⟨ch, h1, _⟩ := (hco j hj).ty; rw [h1]; rfl)]
    rfl
  have mkB : RecTwin st s t cts r tyh → IndBounds s (indBlockD st t cts r T) t.numParams := by
    intro tw
    have hB : B55 = 2 ^ 55 := rfl
    obtain ⟨rty, nR, hrty, hnR, hdenR⟩ := tw.tele
    refine ⟨by rw [← hB]; exact hnP, by have := hnC; unfold B55 at this; simp [indBlockD]; omega,
      fun ci hci => by rw [← hB]; exact indBlock_lps st t cts r T hlplT (fun c hc => by
        obtain ⟨j, hj, e⟩ := List.getElem_of_mem hc; rw [← e]; exact (hco j hj).lpl) tw.lpl ci hci, ?_, ?_, ?_⟩
    · intro ci hci ex hex
      rcases indBlock_cases hci with rfl | ⟨j, hj, rfl⟩ | rfl
      · simp only [IConstantInfo.toConstantVal, cvOfD, hty, Option.getD_some] at hex
        rw [← hdenT ex hex, ← hB]; exact hnT
      · obtain ⟨ch, h1, _, h3⟩ := (hco j hj).ty
        simp only [IConstantInfo.toConstantVal, cvOfD, h1, Option.getD_some] at hex
        rw [← h3 ex hex, ← hB]; exact (hco j hj).tl
      · simp only [recInfoD, IConstantInfo.toConstantVal, cvOfD, hrty, Option.getD_some] at hex
        rw [← hdenR ex hex, ← hB]; exact hnR
    · intro ci hci cv np nf T' e
      rcases indBlock_cases hci with rfl | ⟨j, hj, rfl⟩ | rfl
      · cases e
      · simp only [IConstantInfo.ctorInfo.injEq] at e
        obtain ⟨-, rfl, rfl, -⟩ := e
        rw [← hB]; exact ⟨(hco j hj).np, (hco j hj).nf⟩
      · simp [recInfoD] at e
    · intro ci hci cv mi rp k rules e
      rcases indBlock_cases hci with rfl | ⟨j, hj, rfl⟩ | rfl
      · cases e
      · cases e
      · simp only [recInfoD, IConstantInfo.recInfo.injEq] at e
        obtain ⟨-, rfl, rfl, -, rfl⟩ := e
        have := tw.ni; have := tw.nr; have hmi := tw.mi; unfold B55 at *
        rw [tw.rp, tw.rm, tw.rmin] at hmi ⊢
        refine ⟨by omega, by omega, by simp; omega, fun ru hru => ?_⟩
        simp only [List.mem_map] at hru
        obtain ⟨ru0, hru0, rfl⟩ := hru
        have := tw.nf ru0 hru0; unfold B55 at this; simpa [ruleOfD] using this
  -- the recursor, the record and the push
  refine specR_mono (recP_spec (α := Unit) C hok cc hrL s _ D (fun x hx => hD x (by
      simp only [indMods, List.mem_append]; simp [hx])) st F rb capD jN jE cap bufJ b hreln hrele hcap hcapN hbuf
    hdr hcapD t cts r T tyh qR eR hqR hsR hnP hnC hlplT (fun c hc => by
      obtain ⟨j, hj, e⟩ := List.getElem_of_mem hc; rw [← e]; exact (hco j hj).lpl)
    H7 hp07 ob hob (by omega) hob7 os hosl hos7 hhead7
    (by envg; exact f1) (by envg; exact f2) (by envg; exact f3) (by envg; exact f4) (by envg; exact f5)
    (by envg; exact f6) (by envg; exact f7) (by envg; exact f9) (by envg; exact f10) (by envg; exact f11)
    (by envg; exact f13) (by envg; exact f16) (fun tw => (mkB tw).toP) hm) (fun u hu => hu) (fun a w s' u ⟨hpost, tw⟩ => ?_)
  refine ⟨_, _, hpost, t, r, T, rfl, rfl, hT, rfl, rfl, hnC, tw.rp, tw.rm, tw.rmin, tw.ni, tw.nr, mkB tw⟩

end ConPanqueque.Front
