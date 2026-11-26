import ConPanqueque.T.Ind.Seeds
import ConPanqueque.T.Decl.StepDefn

/-!
# `checkBlockInds` (single-member blocks): the former's telescope, the block's sort, the former pushed

A block with more than one member hangs (mutual blocks are outside the supported subset).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC


def cbiSh := ofString "cbi_sh"
def cbiIr := ofString "cbi_ir"
def cbiOm := ofString "cbi_om"
def cbiL := ofString "cbi_l"
def cbiP0 := ofString "cbi_p0"
def cbiNP := ofString "cbi_np"
def cbiNi := ofString "cbi_ni"
def cbiQ := ofString "cbi_q"
def cbiK := ofString "cbi_k"
def cbiT := ofString "cbi_t"
def cbiZ := ofString "cbi_z"
def cbiO := ofString "cbi_o"
def cbiIp := ofString "cbi_ip"
def cbiW0 := ofString "cbi_w0"
def cbiW1 := ofString "cbi_w1"
def cbiW3 := ofString "cbi_w3"
def cbiW5 := ofString "cbi_w5"
def cbiSh1 := ofString "cbi_sh1"
def cbiD := ofString "cbi_d"
def cbiNz := ofString "cbi_nz"
def cbiNm0 := ofString "cbi_nm0"
def cbiOne := ofString "cbi_one"
def cbiNB := ofString "cbi_nb"
def cbiAll := ofString "cbi_all"
def cbiRc := ofString "cbi_rc"
def cbiX := ofString "cbi_x"
def cbiDn := ofString "cbi_dn"
def cbiRi := ofString "cbi_ri"
def cbiF := ofString "cbi_f"
def fCbi := ofString "checkBlockInds"

def cbiParams : List MlS := [cbiSh, cbiIr]
def cbiLocals : List MlS := [cbiOm, cbiL, cbiP0, cbiNP, cbiNi, cbiQ, cbiK, cbiT, cbiZ, cbiO, cbiIp, cbiW0, cbiW1, cbiW3,
  cbiW5, cbiSh1, cbiD, cbiNz, cbiNm0, cbiOne, cbiNB, cbiAll, cbiRc, cbiX, cbiDn, cbiRi, cbiF]

/-- After the block's `Prop`-ness: the new shape, the former's record, the push, the literal flags. -/
def cbiRest (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local cbiW0 (.load .one (vv cbiSh)))
  (.seq (.assign .local cbiW1 (.load .one (.op .add [vv cbiSh, .const 8])))
  (.seq (.assign .local cbiW3 (.load .one (.op .add [vv cbiSh, .const 24])))
  (.seq (.assign .local cbiW5 (.load .one (.op .add [vv cbiSh, .const 40])))
  (alloc7 C cbiSh1 (vv cbiW0) (vv cbiW1) (vv cbiNP) (vv cbiW3) (vv cbiT) (vv cbiW5) (vv cbiIp)
  (.seq (.assign .local cbiD (.load .one (.op .add [vv cbiP0, .const 8])))
  (.seq (.call (some (some (.local, cbiNz), none)) fMemberNZ [vv cbiD])
  (.seq (.assign .local cbiNm0 (.load .one (vv cbiQ)))
  (.seq (.assign .local cbiOne (.const 1))
  (alloc2 C cbiNB (vv cbiOne) (vv cbiNm0)
  (envBlkP C cbiAll cbiNB cbiOne cbiRc
  (.seq (.call (some (some (.local, cbiX), none)) fFormerRec [vv cbiP0, vv cbiIr, vv cbiAll, vv cbiNP, vv cbiNz])
  (.seq (.assign .local cbiDn (.load .one (vv cbiD)))
  (idxInsP C (vv cbiDn) (vv cbiX) cbiRi
  (.seq (.call (some (some (.local, cbiF), none)) fFlags [])
    (.return (vv cbiSh1))))))))))))))))

def cbiBody (C : Ctx) : ProgHOL 64 := prologue cbiLocals
  (.seq (.assign .local cbiOm (.load .one (vv cbiSh)))
  (.seq (.assign .local cbiL (.load .one (vv cbiOm)))
  (.ite (.cmp .equal (vv cbiL) (.const 1))
    (.seq (.assign .local cbiP0 (.load .one (.op .add [vv cbiOm, .const 8])))
    (.seq (.assign .local cbiNP (.load .one (.op .add [vv cbiSh, .const 16])))
    (.seq (.assign .local cbiNi (.load .one (.op .add [vv cbiP0, .const 16])))
    (.seq (.assign .local cbiQ (.load .one (vv cbiP0)))
    (.seq (.assign .local cbiK (.op .add [vv cbiNP, vv cbiNi]))
    (.seq (.call (some (some (.local, cbiT), none)) fBlockTele [vv cbiQ, vv cbiK])
    (.seq (.assign .local cbiZ (.load .one (.const (ecell C (C.PO + pinCount + 1)))))
    (.seq (.call (some (some (.local, cbiO), none)) LLeq.fEqv [vv cbiT, vv cbiZ])
    (.ite (.cmp .equal (vv cbiO) (.const 2))
      (.seq (.assign .local cbiIp (.const 1)) (cbiRest C))
      (.seq (.assign .local cbiIp (.const 0)) (cbiRest C)))))))))))
    hang)))

structure CBICodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  ccv : CcvCodes mode C
  sp : C.code.lookup fStripPis = some ([(pFu, .one), (pH, .one)], stripBody C fStripPis 6, .one)
  srt : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one)
  ct : C.code.lookup fBlockTele = some (ctParams.map (fun p => (p, ShapeHOL.one)), ctBody, .one)
  eqv : C.code.lookup LLeq.fEqv = some ([LEq.pLa, LEq.pLb].map (fun p => (p, ShapeHOL.one)), LLeq.eqvBody, .one)
  mv : MVCodes C
  mvf : C.code.lookup fMemberNZ = some (mvParams.map (fun p => (p, ShapeHOL.one)), mvBody, .one)
  cp : C.code.lookup fCpy = some (Decl.cpParams.map (fun p => (p, ShapeHOL.one)), cpyBody, .one)
  cn : C.code.lookup fCnFill = some (cnParams.map (fun p => (p, ShapeHOL.one)), cnBody, .one)
  cw : C.code.lookup fConstRec = some (cwParams.map (fun p => (p, ShapeHOL.one)), cwBody C, .one)
  fm : C.code.lookup fFormerRec = some (fmParams.map (fun p => (p, ShapeHOL.one)), fmBody C, .one)
  k : KCodes C Comp.kBodies
  natF : C.code.lookup fNatF = some (([] : List MlS).map (fun p => (p, ShapeHOL.one)), natFBody C, .one)
  strF : C.code.lookup fStrF = some (([] : List MlS).map (fun p => (p, ShapeHOL.one)), strFBody C, .one)
  flags : C.code.lookup fFlags = some (([] : List MlS).map (fun p => (p, ShapeHOL.one)), Decl.flBody, .one)

section
variable {σ : Type}

theorem cbi_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cbiLocals → (ctxEnv C ++ cbiParams.zip vals).get x = none :=
  Knot.params_none C cbiLocals cbiParams vals (by decide) (by decide)

/-- After `checkBlockInds`: the next context (its environment the twin's), the new shape. -/
def PostCBI (C : Ctx) (p : BlockShape) (r : IFEnv × BlockShape) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ EH envM H o, C.EH <+: EH ∧ C.H <+: H ∧ CtxOK (ctxNew C r.1 EH envM H) ∧ SR (ctxNew C r.1 EH envM H) s' st ∧
    TblGate r.1 ∧ FlagsOK r.1 ∧ LitsPinned r.1 C.pins ∧
    (∀ n, (∀ ms ∈ p.members, ms.declared.name ≠ n) → r.1.find? n = C.fe.find? n) ∧ w = cellA C o ∧ ShapeRep C H o r.2 ∧
    ∃ s0 ip, r.2 = { p with resSort := s0, isProp := ip } ∧ ∃ l, denoteL s'.store.ls s0 = some l

theorem postCBI_locals (C : Ctx) (p : BlockShape) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostCBI C p a w s' st → PostCBI C p a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨EH, envM, H, o, h1, h2, h3, h4, h5⟩ => ⟨EH, envM, H, o, h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl, h5⟩

theorem ctxOK_unSt {C : Ctx} {St : EStore} (hok : CtxOK (ctxSt C St)) : CtxOK C := by
  cases hok; constructor <;> assumption

theorem postCBI_lower {C : Ctx} {St : EStore} (p : BlockShape) (hx : Ext C.St St) :
    ∀ a w s' (st : PState σ), PostCBI (ctxSt C St) p a w s' st → PostCBI C p a w s' st :=
  fun _ _ _ _ ⟨EH, envM, H, o, h1, h2, h3, h4, h5⟩ =>
    ⟨EH, envM, H, o, h1, h2, ctxOK_unSt h3, sr_lower (C := ctxNew C _ EH envM H) h4 hx, h5⟩

set_option maxHeartbeats 32000000 in
/-- **`checkBlockInds`** (a block with one member; any other hangs). -/
theorem cbi_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hc : CBICodes mode C) (hg : TblGate C.fe) (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins)
    (heqS : ∀ (C' : Ctx), C'.code = C.code → CtxOK C' → ∀ (H : List (BitVec 64)) (u v : LIdx) (s : AState)
      (lu lv : ConLeche.Level), denoteL s.store.ls u = some lu → denoteL s.store.ls v = some lv → CachesOK s →
      SpecR (σ := σ) (Pre (ctxH C' H) s [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s (lvlEq? u v)
        (fun o w s' st => LLeq.PostOB (ctxH C' H) o w s' st))
    (p : BlockShape) (osh : Nat) (hsh : ShapeRep C C.H osh p) (isRec : Bool) (hnP : p.nP < 2 ^ 62)
    (hml : p.members.length < 2 ^ 58)
    (hmem : ∀ ms ∈ p.members, ms.nIdx < 2 ^ 62 ∧ ms.cvT.levelParams.length < 2 ^ 62 ∧
      (∃ ks : List ConLeche.Name, ∃ hkl : ks.length = ms.cvT.levelParams.length,
        ∀ j (hj : j < ms.cvT.levelParams.length), denoteN C.St.ns ms.cvT.levelParams[j] = some (ks[j]'(by omega))) ∧
      CVDen ms.declared C.St ∧ C.fe.find? ms.declared.name = none)
    (s : AState) :
    SpecR (σ := σ) (Pre C s (cbiParams.zip [cellA C osh, boolW isRec])) (cbiBody C) s
      (checkBlockInds mode C.fe p isRec) (PostCBI C p) := by
  refine specR_prologue (postCBI_locals C p) (cbi_none C _) ?_
  obtain ⟨⟨om, hom, hM⟩, ⟨or_, hor, hR⟩, hnPe, hel, hrs, hlg, hip⟩ := hsh
  refine UD.specR_heapLoadI' (C := C) cbiOm (vv cbiSh) osh _ hom (by decide)
    (by simp +decide [sev, Env.get, cbiParams, ctxEnv]) ?_
  refine UD.specR_heapLoadI' (C := C) cbiL (vv cbiOm) om _ hM.1 (by decide) (by simp [sev, Env.get_cons]) ?_
  unfold checkBlockInds
  rcases hms : p.members with _ | ⟨ms0, _ | ⟨m1, rest⟩⟩
  · rw [hms] at hM
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => specR_hangI)
  swap
  · rw [hms] at hM
    have hw : BitVec.ofNat 64 (ms0 :: m1 :: rest).length ≠ 1#64 := by
      intro e; have := congrArg BitVec.toNat e
      rw [hms] at hml
      simp at this hml; omega
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hw) (fun h => absurd rfl h)
      (fun _ => specR_hangI)
  rw [hms] at hM
  obtain ⟨hmn, hmk, ⟨ks, hkl, hks⟩, hcd, hnew⟩ := hmem ms0 (by rw [hms]; simp)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
  obtain ⟨o0, ho0, hrep0⟩ := hM.2 0 (by simp)
  simp only [List.getElem_cons_zero] at hrep0 ho0
  obtain ⟨⟨oc, hoc, hcv⟩, ⟨od, hod, hdv⟩, hni, ⟨ol, hol, hcsr⟩⟩ := id hrep0
  refine UD.specR_heapLoadI' (C := C) cbiP0 _ (om + 1 + 0) _ ho0 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C om) ?_
  refine UD.specR_heapLoadI' (C := C) cbiNP _ (osh + 2) _ hnPe.1 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, cbiParams, ctxEnv]; exact cellA_add_ofNat C osh 2) ?_
  refine UD.specR_heapLoadI' (C := C) cbiNi _ (o0 + 2) _ hni (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C o0 2) ?_
  refine UD.specR_heapLoadI' (C := C) cbiQ (vv cbiP0) o0 _ hoc (by decide) (by simp +decide [sev, Env.get_cons]) ?_
  refine specR_assignI cbiK _ (BitVec.ofNat 64 (p.nP + ms0.nIdx)) (by decide)
    (by simp +decide [sev, Env.get_cons]; rw [BitVec.ofNat_add_ofNat]) ?_
  simp only
  refine specR_callNIH (C := C) cbiT fBlockTele ctParams [vv cbiQ, vv cbiK] ctBody
    [cellA C oc, BitVec.ofNat 64 (p.nP + ms0.nIdx)] (by decide) rfl (by decide) hc.ct
    ⟨by simp +decide [sev, Env.get_cons] <;> rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (PostCT C ms0.cvT) (fun r w s' H' => r.1 = ms0.cvT ∧ w = Enc.idxW r.2 ∧ ∃ l, denoteL s'.store.ls r.2 = some l)
    (fun r w s' st ⟨h1, h2, ⟨H', hp', hsr⟩, h3⟩ => ⟨H', hp', ⟨h1, h2, h3⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ctParams _ rfl hlk)
      (ct_spec mode C.fe ra C hok hs hc.ccv hc.sp hc.srt rfl p.nP ms0 oc (by omega) C.H (List.prefix_refl _) hcv
        hmk ks hkl hks s))
    (fun r w s1 H1 hp1 ⟨hr1, hw1, l0, hl0⟩ => ?_)
  obtain ⟨cv0, s0⟩ := r
  simp only at hr1 hw1 hl0
  subst hr1; subst hw1
  have hp1' : C.H <+: H1 := hp1
  simp only [checkBlockTeles, checkBlockAgree, pure_bind]
  rw [BlockShape.withSort]
  simp only [zeroLevel, bind_assoc]
  refine specR_atEntry fun t1 ht1 => ?_
  have hz := sr_zeroLevel ht1.sr
  have hco := ht1.sr.cok
  have hx1 : Ext C.St s1.store := ht1.sr.floor
  refine specR_invRaise (R' := PostCBI (ctxSt C s1.store) p) ?_
    (fun a w s' t _ hpost => postCBI_lower p hx1 a w s' t hpost)
  set C1 := ctxSt C s1.store with hC1
  have hokC1 : CtxOK C1 := ctxOK_St hok _
  have hok1 : CtxOK (ctxH C1 H1) := ctxOK_H hokC1 H1
  refine specR_pinXI (C := ctxH C1 H1) hok1 pinZeroLevel 1 C.pins.zeroLevel _
    (fun s hp => pinZeroLevel_run (C := ctxH C1 H1) hok1 hp) (pin_zeroLevel_cell hok1) cbiZ (by decide) ?_
  refine specR_callNIH (C := ctxH C1 H1) cbiO LLeq.fEqv [LEq.pLa, LEq.pLb] [vv cbiT, vv cbiZ] LLeq.eqvBody
    [Enc.idxW s0, Enc.idxW C.pins.zeroLevel] (by decide) rfl (by decide) hc.eqv
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons] <;> rfl, trivial⟩
    (LLeq.PostOB (ctxH C1 H1)) (fun o w s' H' => H' = H1 ∧ w = LLeq.obW o)
    (fun o w s' st ⟨hw, hsr⟩ => ⟨H1, List.prefix_refl _, ⟨rfl, hw⟩, hsr⟩)
    (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu [LEq.pLa, LEq.pLb] _ rfl hlk)
      (heqS C1 rfl hokC1 H1 s0 C.pins.zeroLevel s1 l0 .zero hl0 hz hco))
    (fun o w s2 H2 hp2 ⟨eH2, hw⟩ => ?_)
  subst hw; subst H2
  have hrest : ∀ (ip : Bool) (Γ : Env) (M : Mem), Γ.get cbiIp = some (boolW ip) → Γ.get cbiSh = some (cellA C osh) →
      Γ.get cbiNP = some (BitVec.ofNat 64 p.nP) → Γ.get cbiT = some (Enc.idxW s0) →
      Γ.get cbiP0 = some (cellA C o0) → Γ.get cbiQ = some (cellA C oc) → Γ.get cbiIr = some (boolW isRec) → Γ.get lKb = some C.KB →
      SpecR (σ := σ) (Inv (ctxH C1 H1) s2 Γ M (ctxLocals ++ cbiLocals)) (cbiRest C) s2
        (consBlockInds { p with members := [ms0], resSort := s0, isProp := ip } isRec [ms0.declared] 0 C.fe >>=
          fun fe₁ => pure (fe₁, { p with members := [ms0], resSort := s0, isProp := ip })) (PostCBI C1 p) := by
    intro ip Γ M gIp gSh gNP gT gP0 gQ gIr gKb
    unfold cbiRest
    set p₁ : BlockShape := { p with members := [ms0], resSort := s0, isProp := ip } with hp₁
    refine UD.specR_heapLoadI' (C := ctxH C1 H1) cbiW0 (vv cbiSh) osh _ (get_prefix hom hp1') (by decide)
      (by simp [sev, gSh]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C1 H1) cbiW1 _ (osh + 1) _ (get_prefix hor hp1') (by decide)
      (by simp +decide [sev, Env.get_cons, gSh]; exact cellA_add8 C osh) ?_
    refine UD.specR_heapLoadI' (C := ctxH C1 H1) cbiW3 _ (osh + 3) _ (get_prefix hel hp1') (by decide)
      (by simp +decide [sev, Env.get_cons, gSh]; exact cellA_add_ofNat C osh 3) ?_
    refine UD.specR_heapLoadI' (C := ctxH C1 H1) cbiW5 _ (osh + 5) _ (get_prefix hlg hp1') (by decide)
      (by simp +decide [sev, Env.get_cons, gSh]; exact cellA_add_ofNat C osh 5) ?_
    refine specR_alloc7I (ctxOK_H hokC1 H1) cbiSh1 (vv cbiW0) (vv cbiW1) (vv cbiNP) (vv cbiW3) (vv cbiT) (vv cbiW5)
      (vv cbiIp) (cellA C om) (cellA C or_) (BitVec.ofNat 64 p.nP) (Enc.idxW p.elim) (Enc.idxW s0) (boolW p.large)
      (boolW ip) (by decide) (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons])
      (fun _ => by simp +decide [sev, Env.get_cons, gNP]) (fun _ => by simp +decide [sev, Env.get_cons])
      (fun _ => by simp +decide [sev, Env.get_cons, gT]) (fun _ => by simp +decide [sev, Env.get_cons])
      (fun _ => by simp +decide [sev, Env.get_cons, gIp]) (fun H2 ws hp2 hws => ?_)
    have hg7 := img7_get H2 ws (cellA C om) (cellA C or_) (BitVec.ofNat 64 p.nP) (Enc.idxW p.elim) (Enc.idxW s0)
      (boolW p.large) (boolW ip) hws
    have hp7 : H1 <+: _ := (hp2 : H1 <+: H2).trans (img7_prefix H2 ws (cellA C om) (cellA C or_) (BitVec.ofNat 64 p.nP)
      (Enc.idxW p.elim) (Enc.idxW s0) (boolW p.large) (boolW ip) hws)
    set H2' := img7 H2 ws (cellA C om) (cellA C or_) (BitVec.ofNat 64 p.nP) (Enc.idxW p.elim) (Enc.idxW s0)
      (boolW p.large) (boolW ip) with hH2'
    have hpC2 : C.H <+: H2' := hp1'.trans hp7
    have hsh7 : ShapeRep C H2' H2.length p₁ :=
      ⟨⟨om, by simpa using hg7 0 (by decide), ptrsRep_mono hpC2 (fun _ _ => memberRep_mono hpC2) hM⟩,
        ⟨or_, by simpa using hg7 1 (by decide), ptrsRep_mono hpC2 (fun _ _ => recRep_mono hpC2) hR⟩,
        ⟨by simpa using hg7 2 (by decide), show p.nP < 2 ^ 63 by omega⟩, by simpa using hg7 3 (by decide),
        by simpa using hg7 4 (by decide), by simpa using hg7 5 (by decide), by simpa using hg7 6 (by decide)⟩
    refine UD.specR_heapLoadI' (C := ctxH C1 H2') cbiD _ (o0 + 1) _ (get_prefix hod hpC2) (by decide)
      (by simp +decide [sev, Env.get_cons, gP0]; exact cellA_add8 C o0) ?_
    have hcaps : blockCapsAt p₁ 0 isRec = (formerZ ms0.declared >>= fun z => pure (capsOf p₁ ms0 isRec z.isNever)) :=
      blockCapsAt_eq p₁ 0 isRec ms0 rfl
    refine specR_congr (m' := (formerZ ms0.declared >>= fun z => pure z.isNever) >>= fun nz =>
      (pure (IConstantInfo.indInfo ms0.declared (capsOf p₁ ms0 isRec nz)) : AM IConstantInfo) >>= fun ci =>
        pure (C.fe.push ci, p₁)) (by simp [consBlockInds, hcaps, bind_assoc]) ?_
    refine specR_callNIH (C := ctxH C1 H2') cbiNz fMemberNZ mvParams [vv cbiD] mvBody [cellA C od] (by decide) rfl
      (by decide) hc.mvf ⟨by simp [sev, Env.get_cons], trivial⟩
      (PostB (ctxH C1 H2')) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mvParams _ rfl hlk)
        (mv_spec C1 (by ctx_tr hc.mv) ms0.declared od H2' hpC2 (cvRep_mono hpC2 hdv) s2))
      (fun nz w s3 H3 hp3 hw => ?_)
    subst hw
    have hp3' : H2' <+: H3 := hp3
    have hpC3 : C.H <+: H3 := hpC2.trans hp3'
    refine UD.specR_heapLoadI' (C := ctxH C1 H3) cbiNm0 (vv cbiQ) oc _ (get_prefix hcv.1 hpC3) (by decide)
      (by simp +decide [sev, Env.get_cons, gQ]; rfl) ?_
    refine specR_assignI cbiOne (.const 1) (BitVec.ofNat 64 1) (by decide) rfl ?_
    refine specR_alloc2I (ctxOK_H hokC1 H3) cbiNB (vv cbiOne) (vv cbiNm0) (BitVec.ofNat 64 1) (Enc.idxW ms0.cvT.name)
      (by decide) (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons])
      (fun H4 ws4 hp4 hws4 => ?_)
    obtain ⟨k0, k1⟩ := img2_get H4 ws4 (BitVec.ofNat 64 1) (Enc.idxW ms0.cvT.name) hws4
    have hp4' : H3 <+: _ := (hp4 : H3 <+: H4).trans (img2_prefix H4 ws4 (BitVec.ofNat 64 1) (Enc.idxW ms0.cvT.name) hws4)
    set H4' := ((H4 ++ ws4).set H4.length (BitVec.ofNat 64 1)).set (H4.length + 1) (Enc.idxW ms0.cvT.name) with hH4'
    have hpC4 : C.H <+: H4' := hpC3.trans hp4'
    have hnb : BlkAt H4' H4.length [Enc.idxW ms0.cvT.name] := ⟨by simpa using k0, fun i hi => by
      simp at hi; subst hi; simpa using k1⟩
    refine specR_envBlkI (C := ctxH C1 H4') (ctxOK_H hokC1 H4') hc.cp cbiAll cbiNB cbiOne cbiRc H4.length
      [Enc.idxW ms0.cvT.name] hnb (by simp) (by decide) (by decide) (by decide) (by decide)
      (by simp [Env.get_cons]; try rfl) (by simp +decide [Env.get_cons]; try rfl) (fun EH' wr hpE hblk => ?_)
    set Cfm := ctxE (ctxH C1 H4') EH' with hCfm
    have hokfm : CtxOK Cfm := ctxOK_E (ctxOK_H hokC1 H4') hpE
    have hall : ENList Cfm.EB Cfm.EH (ecell (ctxH C1 H4') (ctxH C1 H4').EH.length) p₁.memberNames :=
      ⟨_, rfl, by simp only [BlockShape.memberNames, hp₁, List.map_cons, List.map_nil]; exact hblk⟩
    set ci : IConstantInfo := .indInfo ms0.declared (capsOf p₁ ms0 isRec nz) with hci
    refine specR_callNC (C := Cfm) (D := ctxLocals ++ cbiLocals) cbiX fFormerRec fmParams
      [vv cbiP0, vv cbiIr, vv cbiAll, vv cbiNP, vv cbiNz] (fmBody C)
      [cellA C o0, boolW isRec, ecell (ctxH C1 H4') (ctxH C1 H4').EH.length, BitVec.ofNat 64 p.nP, boolW nz]
      (by decide) rfl (by decide) hc.fm ?_
      (fun a w s' st => (pure ci : AM IConstantInfo) s3 = .ok (a, s') ∧ PostFM Cfm a w s' st)
      (fun a w s' C' => s' = s3 ∧ a = ci ∧ ∃ H5 EH5 ox, C' = ctxE (ctxH Cfm H5) EH5 ∧ Cfm.H <+: H5 ∧
        Cfm.EH <+: EH5 ∧ w = ecell Cfm ox ∧ CIE Cfm.EB EH5 ox ci)
      (fun a w s' st ⟨hrun, ⟨H5, EH5, ox, hp5, hpE5, _, hw, hcie, hsr⟩⟩ => by
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        exact ⟨_, ⟨rfl, rfl, H5, EH5, ox, rfl, hp5, hpE5, hw, hcie⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fmParams _ rfl hlk)
        (specR_run (fm_spec Cfm hokfm hc.cp hc.cn (by ctx_tr hc.cw) p₁ ms0 o0 (memberRep_mono hpC4 hrep0) isRec _ hall
          (show p.nP < 2 ^ 63 by omega) (by omega) (by have := hcd.2.2; omega) nz s3)))
      (fun a w s4 C4 ⟨hs4, ha, H5, EH5, ox, eC, hp5, hpE5, hw, hcie⟩ => ?_)
    · exact ⟨by simp +decide [sev, Env.get_cons, gP0], by simp +decide [sev, Env.get_cons, gIr],
        by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, gNP],
        by simp +decide [sev, Env.get_cons], trivial⟩
    subst eC hs4 ha hw
    have hp5' : H4' <+: H5 := hp5
    have hpC5 : C.H <+: H5 := hpC4.trans hp5'
    refine UD.specR_heapLoadI' (C := ctxE (ctxH Cfm H5) EH5) cbiDn (vv cbiD) od _ (get_prefix hdv.1 hpC5) (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine specR_atEntry fun t5 ht5 => ?_
    have hd5 : CVDen ms0.declared s4.store := cvDen_ext (cvDen_ext hcd hx1) ht5.sr.floor
    have hden : NewDen ci s4.store := by
      refine ⟨hd5.1, hd5.2.1, hd5.2.2, fun _ _ _ h => (by simp [hci] at h), fun cv caps h => ?_⟩
      simp only [hci, IConstantInfo.indInfo.injEq] at h
      obtain ⟨-, rfl⟩ := h; show p.nP + ms0.nIdx < 2 ^ 63; omega
    refine specR_idxInsI (C := ctxH Cfm H5) (ctxOK_H hokfm H5) hc.k.s hc.k.i hg ci hnew
      (fun _ _ _ _ _ h => by simp [hci] at h) EH5 ox hpE5 hden (vv cbiDn) (vv cbiX) cbiRi (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl)
      (fun v hv => by simp +decide [sev, Env.get_cons] at hv; exact hv.symm) (by simp +decide [sev, Env.get_cons]; rfl)
      (by simp +decide [Env.get_cons, gKb]; rfl) (fun wr2 => ?_)
    have hokI := ctxOK_ins (ctxOK_H hokfm H5) hpE5 hcie (pushOld_find C.fe ci) (pushOld_findTable hg ci hnew)
    have hfP : ∀ n, (C.fe.push ci).find? n = (ctxIns (ctxH Cfm H5) ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit) EH5
        (C.envM.insert ci.name (ecell C ox))).fe.find? n := fun n => (IFEnv.setFlags_find? _ _ _ n).symm
    have htP : ∀ n, (C.fe.push ci).findTable? n = (ctxIns (ctxH Cfm H5) ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit)
        EH5 (C.envM.insert ci.name (ecell C ox))).fe.findTable? n := fun n => by
      show _ = ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit).findTable? n
      unfold IFEnv.findTable?; rw [IFEnv.setFlags_find?, IFEnv.setFlags_rawTable?]
    obtain ⟨hfn, hfs⟩ := push_flags_found (C := ctxH Cfm H5) hF hL ci ox EH5
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => (pure (C.fe.push ci, p₁) : AM (IFEnv × BlockShape)))
      (by simp) ?_
    refine specR_callNC (C := ctxIns (ctxH Cfm H5) ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit) EH5
        (C.envM.insert ci.name (ecell C ox))) (D := ctxLocals ++ cbiLocals) cbiF fFlags [] [] Decl.flBody []
      (by decide) rfl (by decide) hc.flags trivial
      (fun a w s' st => PostFl (ctxIns (ctxH Cfm H5) ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit) EH5
        (C.envM.insert ci.name (ecell C ox))) (C.fe.push ci) a w s' st ∧ s' = s4)
      (fun _ w s' C' => s' = s4 ∧ ∃ H6, C' = ctxFe (ctxH (ctxIns (ctxH Cfm H5) ((C.fe.push ci).setFlags C.fe.natLit
        C.fe.strLit) EH5 (C.envM.insert ci.name (ecell C ox))) H6) (C.fe.push ci) ∧ H5 <+: H6)
      (fun a w s' st ⟨⟨H6, hp6, hsr⟩, hs'⟩ => ⟨_, ⟨hs', H6, rfl, hp6⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [] _ rfl hlk)
        (specR_pureState (fl_spec _ hokI hc.natF hc.strF hc.k.g hc.k.p s4 hfP htP hfn hfs)))
      (fun _ w s5 C5 ⟨hs5, H6, eC, hp6⟩ => ?_)
    subst eC hs5
    have hokF := ctxOK_fe (ctxOK_H hokI H6) (fe := C.fe.push ci) (fun n => hfP n) (fun n => htP n)
    have hpC6 : C.H <+: H6 := hpC5.trans hp6
    refine specR_returnI (vv cbiSh1) (cellA C H2.length) (by simp +decide [sev, Env.get_cons]; rfl) (fun t ht => ?_)
    refine ⟨EH5, C.envM.insert ci.name (ecell C ox), H6, H2.length, hpE.trans hpE5, hp1'.trans (hp7.trans ?_), hokF,
      sr_of_eq ht.sr rfl rfl rfl rfl, hg.push ci, hF.push ci, by unfold LitsPinned; rw [IFEnv.push_base]; exact hL,
      fun n hn => by
        rw [IFEnv.find?_push]
        have : (ci.name == n) = false := by
          simp only [hci, beq_eq_false_iff_ne]; exact hn ms0 (by simp [hms])
        simp [this]; rfl,
      rfl, shapeRep_mono ?_ hsh7, s0, ip, by simp only [hp₁, hms], l0, denoteL_ext hl0 ht.sr.floor⟩
    · exact hp3'.trans (hp4'.trans (hp5'.trans hp6))
    · exact hp3'.trans (hp4'.trans (hp5'.trans hp6))
  simp only [hms, List.map_cons, List.map_nil]
  rcases o with _ | ⟨_ | _⟩
  · refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI cbiIp (.const 0) (boolW false) (by decide) (by simp [sev, boolW]) ?_
    simp only [pure_bind]
    refine hrest false _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp +decide [Env.get_cons, Env.get, cbiParams, ctxEnv]
  · refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI cbiIp (.const 0) (boolW false) (by decide) (by simp [sev, boolW]) ?_
    simp only [pure_bind]
    refine hrest false _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp +decide [Env.get_cons, Env.get, cbiParams, ctxEnv]
  · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_assignI cbiIp (.const 1) (boolW true) (by decide) (by simp [sev, boolW]) ?_
    simp only [pure_bind]
    refine hrest true _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp +decide [Env.get_cons, Env.get, cbiParams, ctxEnv]

end

end ConPanqueque.T.Ind
