import ConPanqueque.T.SameLay
import ConPanqueque.T.Ind.Seeds
import ConPanqueque.T.Decl.StepDefn
import ConPanqueque.T.Ind.BlockAgree
import ConPanqueque.T.Ind.ConsInds
import ConPanqueque.T.Ind.CtorNamesAll

/-!
# `checkBlockInds` at any number of members

Member 0's telescope (`ct`), the other members' (`ctl`, their sorts a linked list), the agreements (`cag`: the
parameter domains defeq to member 0's, the sorts equal to member 0's), the block's `Prop`-ness, the new shape, the
member names into an environment block, every member's former pushed (`cbn`). A block with no member hangs.
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
def cbiNB := ofString "cbi_nb"
def cbiAll := ofString "cbi_all"
def cbiRc := ofString "cbi_rc"
def cbiX := ofString "cbi_x"
def cbiLs := ofString "cbi_ls"
def cbiTy0 := ofString "cbi_ty0"
def fCbi := ofString "checkBlockInds"

def cbiParams : List MlS := [cbiSh, cbiIr]
def cbiLocals : List MlS := [cbiOm, cbiL, cbiP0, cbiNP, cbiNi, cbiQ, cbiK, cbiT, cbiZ, cbiO, cbiIp, cbiW0, cbiW1, cbiW3,
  cbiW5, cbiSh1, cbiNB, cbiAll, cbiRc, cbiX, cbiLs, cbiTy0]

/-- After the block's `Prop`-ness: the new shape, the member names into an environment block, the formers pushed. -/
def cbiRest (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local cbiW0 (.load .one (vv cbiSh)))
  (.seq (.assign .local cbiW1 (.load .one (.op .add [vv cbiSh, .const 8])))
  (.seq (.assign .local cbiW3 (.load .one (.op .add [vv cbiSh, .const 24])))
  (.seq (.assign .local cbiW5 (.load .one (.op .add [vv cbiSh, .const 40])))
  (alloc7 C cbiSh1 (vv cbiW0) (vv cbiW1) (vv cbiNP) (vv cbiW3) (vv cbiT) (vv cbiW5) (vv cbiIp)
  (allocP C cbiNB (.shift .lsl (.op .add [vv cbiL, .const 1]) (.const 3))
  (.seq (.store (vv cbiNB) (vv cbiL))
  (.seq (.call (some (some (.local, cbiX), none)) fMna [vv cbiOm, vv cbiNB, .const 0, vv cbiL])
  (envBlkP C cbiAll cbiNB cbiL cbiRc
  (.seq (.call (some (some (.local, cbiX), none)) fCbn [vv cbiOm, .const 0, vv cbiL, vv cbiIr, vv cbiAll, vv cbiNP])
    (.return (vv cbiSh1)))))))))))

def cbiBody (C : Ctx) : ProgHOL 64 := prologue cbiLocals
  (.seq (.assign .local cbiOm (.load .one (vv cbiSh)))
  (.seq (.assign .local cbiL (.load .one (vv cbiOm)))
  (.ite (.cmp .equal (vv cbiL) (.const 0)) hang
    (.seq (.assign .local cbiP0 (.load .one (.op .add [vv cbiOm, .const 8])))
    (.seq (.assign .local cbiNP (.load .one (.op .add [vv cbiSh, .const 16])))
    (guardP cbiNP 56
    (.seq (.assign .local cbiNi (.load .one (.op .add [vv cbiP0, .const 16])))
    (.seq (.assign .local cbiQ (.load .one (vv cbiP0)))
    (.seq (.assign .local cbiK (.op .add [vv cbiNP, vv cbiNi]))
    (.seq (.call (some (some (.local, cbiT), none)) fBlockTele [vv cbiQ, vv cbiK])
    (.seq (.call (some (some (.local, cbiLs), none)) fCtl [vv cbiOm, .const 1, vv cbiL, vv cbiNP])
    (.seq (.assign .local cbiTy0 (.load .one (.op .add [vv cbiQ, .const 16])))
    (.seq (.call (some (some (.local, cbiX), none)) fCag
        [vv cbiOm, .const 1, vv cbiL, vv cbiNP, vv cbiTy0, vv cbiT, vv cbiLs])
    (.seq (.assign .local cbiZ (.load .one (.const (ecell C (C.PO + pinCount + 1)))))
    (.seq (.call (some (some (.local, cbiO), none)) LLeq.fEqv [vv cbiT, vv cbiZ])
    (.ite (.cmp .equal (vv cbiO) (.const 2))
      (.seq (.assign .local cbiIp (.const 1)) (cbiRest C))
      (.seq (.assign .local cbiIp (.const 0)) (cbiRest C))))))))))))))))))

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
  ac : Comp.AllCodes mode C
  ctl : C.code.lookup fCtl = some (ctlParams.map (fun p => (p, ShapeHOL.one)), ctlBody C, .one)
  cag : CAGCodes C
  mna : C.code.lookup fMna = some (mnaParams.map (fun p => (p, ShapeHOL.one)), mnaBody, .one)
  cbn : C.code.lookup fCbn = some (cbnParams.map (fun p => (p, ShapeHOL.one)), cbnBody C, .one)

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
    (heqS : ∀ (C' : Ctx), SameLay C C' → CtxOK C' → ∀ (H : List (BitVec 64)) (u v : LIdx) (s : AState)
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
  have hT : ∀ ms ∈ p.members, TeleOK C ms := fun ms hm =>
    let ⟨h1, h2, h3, _⟩ := hmem ms hm
    ⟨h1, h2, h3⟩
  unfold checkBlockInds
  rcases hms : p.members with _ | ⟨ms0, rest⟩
  · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hms, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  have hlenM : p.members.length = rest.length + 1 := by rw [hms]; rfl
  have hw : BitVec.ofNat 64 (rest.length + 1) ≠ 0#64 := by
    intro e; have := congrArg BitVec.toNat e
    simp at this; omega
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hw)
    (fun h => absurd rfl h) (fun _ => ?_)
  obtain ⟨hmn, hmk, ⟨ks, hkl, hks⟩, hcd, hnew⟩ := hmem ms0 (by rw [hms]; simp)
  obtain ⟨o0, ho0, hrep0⟩ := hM.2 0 (by omega)
  simp only [hms, List.getElem_cons_zero] at hrep0
  obtain ⟨⟨oc, hoc, hcv⟩, ⟨od, hod, hdv⟩, hni, ⟨ol, hol, hcsr⟩⟩ := id hrep0
  refine UD.specR_heapLoadI' (C := C) cbiP0 _ (om + 1 + 0) _ ho0 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C om) ?_
  refine UD.specR_heapLoadI' (C := C) cbiNP _ (osh + 2) _ hnPe.1 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, cbiParams, ctxEnv]; exact cellA_add_ofNat C osh 2) ?_
  refine specR_guardI cbiNP p.nP 56 (by decide) (by simp +decide [Env.get_cons]) (by omega) (fun hnP56 => ?_)
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
  refine specR_atEntry fun t1 ht1 => ?_
  have hx1 : Ext C.St s1.store := ht1.sr.floor
  refine specR_invRaise (R' := PostCBI (ctxSt C s1.store) p) ?_
    (fun a w s' t _ hpost => postCBI_lower p hx1 a w s' t hpost)
  set C1 := ctxSt C s1.store with hC1
  have hokC1 : CtxOK C1 := ctxOK_St hok _
  -- the other members' telescopes
  have hctl : CTLCodes mode C := ⟨hc.ccv, hc.sp, hc.srt, hc.ct, hc.ctl⟩
  have hctl1 : CTLCodes mode C1 := by ctx_tr hctl
  rw [show checkBlockTeles mode C.fe p.nP rest = checkBlockTeles mode C.fe p.nP (p.members.drop 1) by rw [hms]; rfl]
  refine specR_callNIH (C := ctxH C1 H1) cbiLs fCtl ctlParams [vv cbiOm, .const 1, vv cbiL, vv cbiNP] (ctlBody C1)
    [cellA C om, BitVec.ofNat 64 1, BitVec.ofNat 64 p.members.length, BitVec.ofNat 64 p.nP] (by decide) rfl
    (by decide) hctl1.self
    ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons, hlenM],
      by simp +decide [sev, Env.get_cons], trivial⟩
    (PostCTL (ctxH C1 H1) (p.members.drop 1))
    (fun rs w s' H' => rs.map Prod.fst = (p.members.drop 1).map (·.cvT) ∧ SLink C.HB H' w (rs.map Prod.snd) ∧
      (∀ x ∈ rs, ∃ l, denoteL s'.store.ls x.2 = some l) ∧ Ext s1.store s'.store)
    (fun rs w s' st ⟨H', hp', hsr, h1, h2, h3⟩ => ⟨H', hp', ⟨h1, h2, h3, hsr.floor⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ctlParams _ rfl hlk)
      (ctl_spec mode ra p om hml hnP _ C1 hokC1 hs hctl1 hM (fun ms hm => teleOK_ext hx1 (hT ms hm)) 1 H1 s1 rfl
        (by omega) hp1'))
    (fun rs wl sT HT hpT ⟨hm1, hsl, hden, hxT⟩ => ?_)
  have hpT' : H1 <+: HT := hpT
  refine specR_invRaise (R' := PostCBI (ctxSt C1 sT.store) p) ?_
    (fun a w s' t hx hpost => postCBI_lower (C := C1) p hx a w s' t hpost)
  set C2 := ctxSt C1 sT.store with hC2
  have hokC2 : CtxOK C2 := ctxOK_St hokC1 _
  have hxCT : Ext C.St sT.store := Ext.trans hx1 hxT
  have hl0T : denoteL sT.store.ls s0 = some l0 := denoteL_ext hl0 hxT
  have hpCT : C.H <+: HT := hp1'.trans hpT'
  -- the agreements
  refine UD.specR_heapLoadI' (C := ctxH C2 HT) cbiTy0 _ (oc + 2) _ (get_prefix hcv.2.2 hpCT) (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C oc 2) ?_
  have hcag2 : CAGCodes C2 := by ctx_tr hc.cag
  refine specR_callNIH (C := ctxH C2 HT) cbiX fCag cagParams
    [vv cbiOm, .const 1, vv cbiL, vv cbiNP, vv cbiTy0, vv cbiT, vv cbiLs] (cagBody C2)
    [cellA C om, BitVec.ofNat 64 1, BitVec.ofNat 64 p.members.length, BitVec.ofNat 64 p.nP, Enc.idxW ms0.cvT.type,
      Enc.idxW s0, wl] (by decide) rfl (by decide) hcag2.self
    ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons, hlenM],
      by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons], trivial⟩
    (Decl.PostU (ctxH C2 HT)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cagParams _ rfl hlk)
      (cag_spec mode ra C2 hokC2 hs (by ctx_tr hc.k) (by ctx_tr hc.ac) hcag2
        (fun H u v s lu lv h1 h2 h3 => heqS C2 rfl hokC2 H u v s lu lv h1 h2 h3) p om hM hml hnP56 ms0.cvT s0 l0 hl0T
        rs 1 HT sT wl hm1 (by omega) hpCT hsl hden))
    (fun _ w s3 H3 hp3 _ => ?_)
  have hp3' : HT <+: H3 := hp3
  have hpC3 : C.H <+: H3 := hpCT.trans hp3'
  rw [BlockShape.withSort]
  simp only [zeroLevel, bind_assoc]
  refine specR_atEntry fun t3 ht3 => ?_
  have hz := sr_zeroLevel ht3.sr
  have hco := ht3.sr.cok
  have hl03 : denoteL s3.store.ls s0 = some l0 := denoteL_ext hl0T ht3.sr.floor
  have hok3 : CtxOK (ctxH C2 H3) := ctxOK_H hokC2 H3
  refine specR_pinXI (C := ctxH C2 H3) hok3 pinZeroLevel 1 C.pins.zeroLevel _
    (fun s hp => pinZeroLevel_run (C := ctxH C2 H3) hok3 hp) (pin_zeroLevel_cell hok3) cbiZ (by decide) ?_
  refine specR_callNIH (C := ctxH C2 H3) cbiO LLeq.fEqv [LEq.pLa, LEq.pLb] [vv cbiT, vv cbiZ] LLeq.eqvBody
    [Enc.idxW s0, Enc.idxW C.pins.zeroLevel] (by decide) rfl (by decide) hc.eqv
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons] <;> rfl, trivial⟩
    (LLeq.PostOB (ctxH C2 H3)) (fun o w s' H' => H' = H3 ∧ w = LLeq.obW o)
    (fun o w s' st ⟨hw, hsr⟩ => ⟨H3, List.prefix_refl _, ⟨rfl, hw⟩, hsr⟩)
    (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu [LEq.pLa, LEq.pLb] _ rfl hlk)
      (heqS C2 rfl hokC2 H3 s0 C.pins.zeroLevel s3 l0 .zero hl03 hz hco))
    (fun o w s4 H4 hp4 ⟨eH4, hw⟩ => ?_)
  subst hw; subst H4
  have hrest : ∀ (ip : Bool) (Γ : Env) (M : Mem), Γ.get cbiIp = some (boolW ip) → Γ.get cbiSh = some (cellA C osh) →
      Γ.get cbiNP = some (BitVec.ofNat 64 p.nP) → Γ.get cbiT = some (Enc.idxW s0) →
      Γ.get cbiOm = some (cellA C om) → Γ.get cbiL = some (BitVec.ofNat 64 p.members.length) →
      Γ.get cbiIr = some (boolW isRec) → Γ.get lKb = some C.KB →
      SpecR (σ := σ) (Inv (ctxH C2 H3) s4 Γ M (ctxLocals ++ cbiLocals)) (cbiRest C) s4
        (consBlockInds { p with resSort := s0, isProp := ip } isRec
          ((ms0 :: rest).map (·.declared)) 0 C.fe >>=
          fun fe₁ => pure (fe₁, { p with resSort := s0, isProp := ip })) (PostCBI C2 p) := by
    intro ip Γ M gIp gSh gNP gT gOm gL gIr gKb
    unfold cbiRest
    set p₁ : BlockShape := { p with resSort := s0, isProp := ip } with hp₁
    refine UD.specR_heapLoadI' (C := ctxH C2 H3) cbiW0 (vv cbiSh) osh _ (get_prefix hom hpC3) (by decide)
      (by simp [sev, gSh]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C2 H3) cbiW1 _ (osh + 1) _ (get_prefix hor hpC3) (by decide)
      (by simp +decide [sev, Env.get_cons, gSh]; exact cellA_add8 C osh) ?_
    refine UD.specR_heapLoadI' (C := ctxH C2 H3) cbiW3 _ (osh + 3) _ (get_prefix hel hpC3) (by decide)
      (by simp +decide [sev, Env.get_cons, gSh]; exact cellA_add_ofNat C osh 3) ?_
    refine UD.specR_heapLoadI' (C := ctxH C2 H3) cbiW5 _ (osh + 5) _ (get_prefix hlg hpC3) (by decide)
      (by simp +decide [sev, Env.get_cons, gSh]; exact cellA_add_ofNat C osh 5) ?_
    refine specR_alloc7I (ctxOK_H hokC2 H3) cbiSh1 (vv cbiW0) (vv cbiW1) (vv cbiNP) (vv cbiW3) (vv cbiT) (vv cbiW5)
      (vv cbiIp) (cellA C om) (cellA C or_) (BitVec.ofNat 64 p.nP) (Enc.idxW p.elim) (Enc.idxW s0) (boolW p.large)
      (boolW ip) (by decide) (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons])
      (fun _ => by simp +decide [sev, Env.get_cons, gNP]) (fun _ => by simp +decide [sev, Env.get_cons])
      (fun _ => by simp +decide [sev, Env.get_cons, gT]) (fun _ => by simp +decide [sev, Env.get_cons])
      (fun _ => by simp +decide [sev, Env.get_cons, gIp]) (fun H2 ws hp2 hws => ?_)
    have hg7 := img7_get H2 ws (cellA C om) (cellA C or_) (BitVec.ofNat 64 p.nP) (Enc.idxW p.elim) (Enc.idxW s0)
      (boolW p.large) (boolW ip) hws
    have hp7 : H3 <+: _ := (hp2 : H3 <+: H2).trans (img7_prefix H2 ws (cellA C om) (cellA C or_) (BitVec.ofNat 64 p.nP)
      (Enc.idxW p.elim) (Enc.idxW s0) (boolW p.large) (boolW ip) hws)
    set H2' := img7 H2 ws (cellA C om) (cellA C or_) (BitVec.ofNat 64 p.nP) (Enc.idxW p.elim) (Enc.idxW s0)
      (boolW p.large) (boolW ip) with hH2'
    have hpC2 : C.H <+: H2' := hpC3.trans hp7
    have hsh7 : ShapeRep C H2' H2.length p₁ :=
      ⟨⟨om, by simpa using hg7 0 (by decide), ptrsRep_mono hpC2 (fun _ _ => memberRep_mono hpC2) hM⟩,
        ⟨or_, by simpa using hg7 1 (by decide), ptrsRep_mono hpC2 (fun _ _ => recRep_mono hpC2) hR⟩,
        ⟨by simpa using hg7 2 (by decide), show p.nP < 2 ^ 63 by omega⟩, by simpa using hg7 3 (by decide),
        by simpa using hg7 4 (by decide), by simpa using hg7 5 (by decide), by simpa using hg7 6 (by decide)⟩
    -- the member names, into a block
    refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN2 => ?_)
    have hlay := hok.heapLay
    refine specR_allocI (C := ctxH C2 H2') cbiNB _ (p.members.length + 1) (by omega) (by decide) (fun v => ?_)
      (fun H5 ws5 hp5 hws5 hroom5 => ?_)
    · simp +decide [sev, Env.get_cons, gL]
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
    have hp5' : H2' <+: H5 := hp5
    have hq5 : H5.length < (ctxH (ctxH C2 H2') (H5 ++ ws5)).H.length := by
      show H5.length < (H5 ++ ws5).length; simp; omega
    refine specR_heapStoreI (ctxOK_H hokC2 _) (vv cbiNB) (vv cbiL) H5.length hq5 (BitVec.ofNat 64 p.members.length)
      (by simp +decide [sev, Env.get_cons] <;> rfl) (by simp +decide [sev, Env.get_cons, gL]) ?_
    change SpecR (Inv (ctxH C2 ((H5 ++ ws5).set H5.length (BitVec.ofNat 64 p.members.length))) _ _ _ _) _ _ _ _
    generalize hB5 : (H5 ++ ws5).set H5.length (BitVec.ofNat 64 p.members.length) = B5
    have hB5len : B5.length = H5.length + (p.members.length + 1) := by rw [← hB5]; simp [hws5]
    have hpB5 : H5 <+: B5 := by
      refine prefix_of_get? (by omega) (fun j hj => ?_)
      rw [← hB5, List.getElem?_set_ne (by omega), List.getElem?_append_left hj]
    let Hc5 := B5.take (H5.length + 1)
    have hpc5 : H5 <+: Hc5 := by
      refine prefix_of_get? (by simp [Hc5]; omega) (fun j hj => ?_)
      simp only [Hc5]; rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj]
      exact get_prefix (List.getElem?_eq_getElem hj) hpB5
    have hpCc5 : C.H <+: Hc5 := hpC2.trans (hp5'.trans hpc5)
    refine specR_pureBind () ?_
    refine specR_callNIG (C := ctxH C2 B5) cbiX fMna mnaParams [vv cbiOm, vv cbiNB, .const 0, vv cbiL] mnaBody
      [cellA C om, cellA C H5.length, BitVec.ofNat 64 0, BitVec.ofNat 64 p.members.length] (by decide) rfl (by decide)
      hc.mna
      ⟨by simp +decide [sev, Env.get_cons, gOm], by simp +decide [sev, Env.get_cons]; rfl, rfl,
        by simp +decide [sev, Env.get_cons, gL], trivial⟩
      (fun a w s' st => (pure () : AM Unit) s4 = .ok (a, s') ∧ PostMNA C2 Hc5 H5.length p.members 0 B5.length a w s' st)
      (fun a w s' H' => s' = s4 ∧ Hc5 <+: H' ∧
        ∀ j (hj : j < p.members.length), H'[H5.length + 1 + j]? = some (Enc.idxW p.members[j].cvT.name))
      (fun a w s' st ⟨hr, H', hp', _, hs', hc'⟩ => by
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
        obtain ⟨-, rfl⟩ := hr
        exact ⟨H', ⟨rfl, hp', fun j hj => hc' j hj (Nat.zero_le _)⟩, hs'⟩)
      (fun u hu _ hlk => specR_run (fun w hw => by
        subst hw
        exact mna_spec C2 hokC2 (by ctx_tr hc.mna) p.members om H5.length hM hml _ 0 B5 Hc5 s4 rfl (Nat.zero_le _)
          hpCc5 (by simp [Hc5]) (List.take_prefix _ _) (by omega) _ (pre_of_lookups hu mnaParams _ rfl hlk)))
      (fun a w s' H6 ⟨hs', hp6, hc6⟩ => ?_)
    subst s'
    have hp6' : H2' <+: H6 := hp5'.trans (hpc5.trans hp6)
    have hpC6 : C.H <+: H6 := hpC2.trans hp6'
    have hmn : BlkAt H6 H5.length ((p.members.map (fun x => x.cvT.name)).map Enc.idxW) := by
      refine ⟨?_, fun j hj => ?_⟩
      · have h0 : B5[H5.length]? = some (BitVec.ofNat 64 p.members.length) := by
          rw [← hB5, List.getElem?_set_self (by simp; omega)]
        have h0' : Hc5[H5.length]? = some (BitVec.ofNat 64 p.members.length) := by
          simp only [Hc5]; rw [List.getElem?_take_of_lt (by omega)]; exact h0
        simpa using get_prefix h0' hp6
      · simp only [List.length_map] at hj
        simp only [List.map_map, List.getElem_map, Function.comp]
        exact hc6 j hj
    refine specR_envBlkI (C := ctxH C2 H6) (ctxOK_H hokC2 H6) hc.cp cbiAll cbiNB cbiL cbiRc H5.length
      _ hmn (by simp; omega) (by decide) (by decide) (by decide) (by decide)
      (by simp [Env.get_cons]; try rfl) (by simp +decide [Env.get_cons, gL]) (fun EH' wr hpE hblk => ?_)
    set Cfm := ctxE (ctxH C2 H6) EH' with hCfm
    have hokfm : CtxOK Cfm := ctxOK_E (ctxOK_H hokC2 H6) hpE
    have hall : ENList Cfm.EB Cfm.EH (ecell (ctxH C2 H6) (ctxH C2 H6).EH.length) p₁.memberNames := ⟨_, rfl, hblk⟩
    have hcbn : CBNCodes Cfm := by
      have h0 : CBNCodes C := ⟨hc.ccv.g, hc.ccv.pr, hc.mv, hc.mvf, hc.cp, hc.cn, hc.cw, hc.fm, hc.k, hc.natF, hc.strF,
        hc.flags, hc.cbn⟩
      ctx_tr h0
    refine specR_congr (m' := consBlockInds p₁ isRec ((p₁.members.drop 0).map (·.declared)) 0 Cfm.fe >>=
      fun fe₁ => pure (fe₁, p₁)) (by simp only [List.drop_zero, hp₁, hms]; rfl) ?_
    refine specR_callNC (C := Cfm) (D := ctxLocals ++ cbiLocals) cbiX fCbn cbnParams
      [vv cbiOm, .const 0, vv cbiL, vv cbiIr, vv cbiAll, vv cbiNP] (cbnBody Cfm)
      [cellA C om, BitVec.ofNat 64 0, BitVec.ofNat 64 p₁.members.length, boolW isRec,
        ecell (ctxH C2 H6) (ctxH C2 H6).EH.length, BitVec.ofNat 64 p₁.nP] (by decide) rfl (by decide) hcbn.self
      ⟨by simp +decide [sev, Env.get_cons, gOm], rfl, by simp +decide [sev, Env.get_cons, gL, hp₁],
        by simp +decide [sev, Env.get_cons, gIr], by simp +decide [sev, Env.get_cons],
        by simp +decide [sev, Env.get_cons, gNP, hp₁], trivial⟩
      (PostCBN (ctxH Cfm Cfm.H) p₁) (fun r w s' C' => ∃ EH envM Hn, C' = ctxNew (ctxH Cfm Cfm.H) r EH envM Hn ∧
        Cfm.EH <+: EH ∧ Cfm.H <+: Hn ∧ CtxOK C' ∧ TblGate r ∧ FlagsOK r ∧ LitsPinned r C.pins ∧
        (∀ n, (∀ ms ∈ p₁.members, ms.declared.name ≠ n) → r.find? n = C.fe.find? n))
      (fun r w s' st ⟨EH, envM, Hn, h1, h2, h3, h4, h5, h6, h7, h8⟩ =>
        ⟨_, ⟨EH, envM, Hn, rfl, h1, h2, h3, h5, h6, h7, h8⟩, h4⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cbnParams _ rfl hlk)
        (cbn_spec p₁ om isRec _ hml (by omega) _ Cfm hokfm hcbn hg hF hL
          (ptrsRep_mono hpC6 (fun _ _ => memberRep_mono hpC6) hM) hall
          (fun m hm => ⟨(hmem m hm).1, cvDen_ext (hmem m hm).2.2.2.1 hxCT⟩) 0 Cfm.H s4 rfl (Nat.zero_le _)
          (List.prefix_refl _)))
      (fun r w s5 C5 ⟨EH5, envM5, H7, eC5, hpE5, hp7', hok5, hg5, hF5, hL5, hfr5⟩ => ?_)
    subst eC5
    refine specR_returnI (vv cbiSh1) (cellA C H2.length) (by simp +decide [sev, Env.get_cons]; rfl) (fun t ht => ?_)
    refine ⟨EH5, envM5, H7, H2.length, hpE.trans hpE5, hpC6.trans hp7', hok5, sr_of_eq ht.sr rfl rfl rfl rfl, hg5, hF5,
      hL5, fun n hn => hfr5 n hn, rfl, shapeRep_mono (hp6'.trans hp7') hsh7, s0, ip, rfl, l0,
      denoteL_ext hl0T ht.sr.floor⟩
  rcases o with _ | ⟨_ | _⟩
  · refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI cbiIp (.const 0) (boolW false) (by decide) (by simp [sev, boolW]) ?_
    simp only [pure_bind]
    refine hrest false _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp +decide [Env.get_cons, Env.get, cbiParams, ctxEnv, hlenM]
  · refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_assignI cbiIp (.const 0) (boolW false) (by decide) (by simp [sev, boolW]) ?_
    simp only [pure_bind]
    refine hrest false _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp +decide [Env.get_cons, Env.get, cbiParams, ctxEnv, hlenM]
  · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_assignI cbiIp (.const 1) (boolW true) (by decide) (by simp [sev, boolW]) ?_
    simp only [pure_bind]
    refine hrest true _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;> simp +decide [Env.get_cons, Env.get, cbiParams, ctxEnv, hlenM]

end

end ConPanqueque.T.Ind
