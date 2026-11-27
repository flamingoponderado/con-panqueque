import ConPanqueque.T.SameLay
import ConPanqueque.T.Ind.Seeds
import ConPanqueque.T.Decl.StepDefn

/-!
# `consBlockInds` at any number of members

`cbnBody(om, i, n, ir, all, nP)`: member `i`'s declared former, its name checked fresh at the current environment
(a found name hangs: the twin's block check rejects duplicate names before, and the members' names are fresh at
the block's environment), its record (`fFormerRec`, the capability record at the block's `is_rec`), pushed, the
literal flags recomputed, then itself at `i + 1`. `cbn_spec` refines
`consBlockInds p isRec ((p.members.drop i).map (·.declared)) i fe` (any context of the same layout).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def cbnOm := ofString "cbn_om"
def cbnI := ofString "cbn_i"
def cbnN := ofString "cbn_n"
def cbnIr := ofString "cbn_ir"
def cbnAll := ofString "cbn_all"
def cbnNP := ofString "cbn_np"
def cbnMi := ofString "cbn_mi"
def cbnD := ofString "cbn_d"
def cbnDn := ofString "cbn_dn"
def cbnY := ofString "cbn_y"
def cbnNz := ofString "cbn_nz"
def cbnX := ofString "cbn_x"
def cbnRi := ofString "cbn_ri"
def cbnF := ofString "cbn_f"
def cbnR := ofString "cbn_r"
def fCbn := ofString "consBlockIndsAll"

def cbnParams : List MlS := [cbnOm, cbnI, cbnN, cbnIr, cbnAll, cbnNP]
def cbnLocals : List MlS := [cbnMi, cbnD, cbnDn, cbnY, cbnNz, cbnX, cbnRi, cbnF, cbnR]

def cbnBody (C : Ctx) : ProgHOL 64 := prologue cbnLocals
  (.ite (.cmp .lower (vv cbnI) (vv cbnN))
    (.seq (.assign .local cbnMi (.load .one (.op .add [vv cbnOm, .op .add [.panop .mul [vv cbnI, .const 8], .const 8]])))
    (.seq (.assign .local cbnD (.load .one (.op .add [vv cbnMi, .const 8])))
    (.seq (.assign .local cbnDn (.load .one (vv cbnD)))
    (envFindP C cbnY (vv cbnDn)
    (.ite (.cmp .notEqual (vv cbnY) (.const 0)) hang
    (.seq (.call (some (some (.local, cbnNz), none)) fMemberNZ [vv cbnD])
    (.seq (.call (some (some (.local, cbnX), none)) fFormerRec [vv cbnMi, vv cbnIr, vv cbnAll, vv cbnNP, vv cbnNz])
    (idxInsP C (vv cbnDn) (vv cbnX) cbnRi
    (.seq (.call (some (some (.local, cbnF), none)) fFlags [])
    (.seq (.call (some (some (.local, cbnR), none)) fCbn
        [vv cbnOm, .op .add [vv cbnI, .const 1], vv cbnN, vv cbnIr, vv cbnAll, vv cbnNP])
      (.return (.const 0))))))))))))
    (.return (.const 0)))

structure CBNCodes (C : Ctx) : Prop where
  g : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  pr : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
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
  self : C.code.lookup fCbn = some (cbnParams.map (fun p => (p, ShapeHOL.one)), cbnBody C, .one)

section
variable {σ : Type}

theorem cbn_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cbnLocals → (ctxEnv C ++ cbnParams.zip vals).get x = none :=
  Knot.params_none C cbnLocals cbnParams vals (by decide) (by decide)

/-- After the cons loop: the next context (its environment the twin's), the frame off the members' names. -/
def PostCBN (C : Ctx) (p : BlockShape) (r : IFEnv) (_ : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ EH envM H, C.EH <+: EH ∧ C.H <+: H ∧ CtxOK (ctxNew C r EH envM H) ∧ SR (ctxNew C r EH envM H) s' st ∧
    TblGate r ∧ FlagsOK r ∧ LitsPinned r C.pins ∧
    (∀ n, (∀ ms ∈ p.members, ms.declared.name ≠ n) → r.find? n = C.fe.find? n)

theorem postCBN_locals (C : Ctx) (p : BlockShape) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostCBN C p a w s' st → PostCBN C p a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨EH, envM, H, h1, h2, h3, h4, h5⟩ => ⟨EH, envM, H, h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl, h5⟩

set_option maxHeartbeats 32000000 in
/-- **`consBlockInds`** over the members from `i` on. -/
theorem cbn_spec (p : BlockShape) (om : Nat) (isRec : Bool) (wAll : BitVec 64) (hml : p.members.length < 2 ^ 58)
    (hnP : p.nP < 2 ^ 62) :
    ∀ f (C : Ctx), CtxOK C → CBNCodes C → TblGate C.fe → FlagsOK C.fe → LitsPinned C.fe C.pins →
      PtrsRep C C.H om (MemberRep C C.H) p.members → ENList C.EB C.EH wAll p.memberNames →
      (∀ ms ∈ p.members, ms.nIdx < 2 ^ 62 ∧ CVDen ms.declared C.St) →
      ∀ i (H : List (BitVec 64)) (s : AState), p.members.length - i = f → i ≤ p.members.length → C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (cbnParams.zip [cellA C om, BitVec.ofNat 64 i,
        BitVec.ofNat 64 p.members.length, boolW isRec, wAll, BitVec.ofNat 64 p.nP])) (cbnBody C) s
        (consBlockInds p isRec ((p.members.drop i).map (·.declared)) i C.fe) (PostCBN (ctxH C H) p) := by
  intro f
  induction f with
  | zero =>
    intro C hok hc hg hF hL hM hall hmem i H s hf hi hp
    have hin : i = p.members.length := by omega
    subst hin
    refine specR_prologue (postCBN_locals _ _) (cbn_none _ _) ?_
    have hlw := nd_lt_iff p.members.length p.members.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, cbnParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length, List.map_nil]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.EH, C.envM, H, List.prefix_refl _, List.prefix_refl _, ctxOK_H hok H,
      sr_of_eq ht.sr rfl rfl rfl rfl, hg, hF, hL, fun n _ => rfl⟩)
  | succ f ih =>
    intro C hok hc hg hF hL hM hall hmem i H s hf hi hp
    have hin : i < p.members.length := by omega
    refine specR_prologue (postCBN_locals _ _) (cbn_none _ _) ?_
    have hlw := nd_lt_iff i p.members.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, cbnParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons hin, List.map_cons]
    set ms := p.members[i] with hmsdef
    obtain ⟨hmn, hcd⟩ := hmem ms (List.getElem_mem hin)
    obtain ⟨oi, hoi, hrep⟩ := hM.2 i hin
    obtain ⟨-, ⟨od, hod, hdv⟩, -, -⟩ := id hrep
    have hokH := ctxOK_H hok H
    refine UD.specR_heapLoadI' (C := ctxH C H) cbnMi _ (om + 1 + i) _ (get_prefix hoi hp) (by decide)
      (by simp +decide [sev, Env.get, cbnParams, ctxEnv]; exact cellA_mulIdx C om i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) cbnD _ (oi + 1) _ (get_prefix hod hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C oi) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) cbnDn (vv cbnD) od _ (get_prefix hdv.1 hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    -- the name fresh at the current environment
    refine specR_envFindI hokH hc.g hc.pr cbnY (vv cbnDn) ms.declared.name (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) (by simp +decide [Env.get_cons, Env.get, cbnParams, ctxEnv]) ?_
    have hrel := find_rel hokH ms.declared.name
    revert hrel
    rcases hfn : (ctxH C H).fe.find? ms.declared.name with _ | ci0
    swap
    · intro ⟨o', hm, hci⟩
      rw [hm]
      refine specR_atEntry fun t ht => ?_
      have hoE : o' < (ctxH C H).EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
      exact specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hokH hoE)
        (fun _ => specR_hangI) (fun h => absurd h (by decide))
    intro hrel
    simp only at hrel
    rw [hrel]
    refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    have hnew : C.fe.find? ms.declared.name = none := hfn
    -- the record
    have hcaps : blockCapsAt p i isRec = (formerZ ms.declared >>= fun z => pure (capsOf p ms isRec z.isNever)) :=
      blockCapsAt_eq p i isRec ms (List.getElem?_eq_getElem hin)
    refine specR_congr (m' := (formerZ ms.declared >>= fun z => pure z.isNever) >>= fun nz =>
      (pure (IConstantInfo.indInfo ms.declared (capsOf p ms isRec nz)) : AM IConstantInfo) >>= fun ci =>
        consBlockInds p isRec ((p.members.drop (i + 1)).map (·.declared)) (i + 1) (C.fe.push ci))
      (by simp [consBlockInds, hcaps, bind_assoc]) ?_
    refine specR_callNIH (C := ctxH C H) cbnNz fMemberNZ mvParams [vv cbnD] mvBody [cellA C od] (by decide) rfl
      (by decide) hc.mvf ⟨by simp +decide [sev, Env.get_cons], trivial⟩
      (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mvParams _ rfl hlk)
        (mv_spec C hc.mv ms.declared od H hp (cvRep_mono hp hdv) s))
      (fun nz w s3 H3 hp3 hw => ?_)
    subst hw
    have hp3' : H <+: H3 := hp3
    have hpC3 : C.H <+: H3 := hp.trans hp3'
    set Cfm := ctxH C H3 with hCfm
    have hokfm : CtxOK Cfm := ctxOK_H hok H3
    set ci : IConstantInfo := .indInfo ms.declared (capsOf p ms isRec nz) with hci
    refine specR_callNC (C := Cfm) (D := ctxLocals ++ cbnLocals) cbnX fFormerRec fmParams
      [vv cbnMi, vv cbnIr, vv cbnAll, vv cbnNP, vv cbnNz] (fmBody C)
      [cellA C oi, boolW isRec, wAll, BitVec.ofNat 64 p.nP, boolW nz]
      (by decide) rfl (by decide) hc.fm ?_
      (fun a w s' st => (pure ci : AM IConstantInfo) s3 = .ok (a, s') ∧ PostFM Cfm a w s' st)
      (fun a w s' C' => s' = s3 ∧ a = ci ∧ ∃ H5 EH5 ox, C' = ctxE (ctxH Cfm H5) EH5 ∧ Cfm.H <+: H5 ∧
        Cfm.EH <+: EH5 ∧ w = ecell Cfm ox ∧ CIE Cfm.EB EH5 ox ci)
      (fun a w s' st ⟨hrun, ⟨H5, EH5, ox, hp5, hpE5, _, hw, hcie, hsr⟩⟩ => by
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
        obtain ⟨rfl, rfl⟩ := hrun
        exact ⟨_, ⟨rfl, rfl, H5, EH5, ox, rfl, hp5, hpE5, hw, hcie⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fmParams _ rfl hlk)
        (specR_run (fm_spec Cfm hokfm hc.cp hc.cn (by ctx_tr hc.cw) p ms oi (memberRep_mono hpC3 hrep) isRec wAll hall
          (show p.nP < 2 ^ 63 by omega) (by omega) (by have := hcd.2.2; omega) nz s3)))
      (fun a w s4 C4 ⟨hs4, ha, H5, EH5, ox, eC, hp5, hpE5, hw, hcie⟩ => ?_)
    · exact ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, cbnParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cbnParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cbnParams, ctxEnv],
        by simp +decide [sev, Env.get_cons], trivial⟩
    subst eC hs4 ha hw
    have hp5' : H3 <+: H5 := hp5
    have hpC5 : C.H <+: H5 := hpC3.trans hp5'
    refine specR_atEntry fun t5 ht5 => ?_
    have hd5 : CVDen ms.declared s4.store := cvDen_ext hcd ht5.sr.floor
    have hden : NewDen ci s4.store := by
      refine ⟨hd5.1, hd5.2.1, hd5.2.2, fun _ _ _ h => (by simp [hci] at h), fun cv caps h => ?_⟩
      simp only [hci, IConstantInfo.indInfo.injEq] at h
      obtain ⟨-, rfl⟩ := h; show p.nP + ms.nIdx < 2 ^ 63; omega
    refine specR_idxInsI (C := ctxH Cfm H5) (ctxOK_H hokfm H5) hc.k.s hc.k.i hg ci hnew
      (fun _ _ _ _ _ h => by simp [hci] at h) EH5 ox hpE5 hden (vv cbnDn) (vv cbnX) cbnRi (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl)
      (fun v hv => by simp +decide [sev, Env.get_cons] at hv; exact hv.symm) (by simp +decide [sev, Env.get_cons]; rfl)
      (by simp +decide [Env.get_cons, Env.get, cbnParams, ctxEnv]; rfl) (fun wr2 => ?_)
    have hokI := ctxOK_ins (ctxOK_H hokfm H5) hpE5 hcie (pushOld_find C.fe ci) (pushOld_findTable hg ci hnew)
    have hfP : ∀ n, (C.fe.push ci).find? n = (ctxIns (ctxH Cfm H5) ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit) EH5
        (C.envM.insert ci.name (ecell C ox))).fe.find? n := fun n => (IFEnv.setFlags_find? _ _ _ n).symm
    have htP : ∀ n, (C.fe.push ci).findTable? n = (ctxIns (ctxH Cfm H5) ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit)
        EH5 (C.envM.insert ci.name (ecell C ox))).fe.findTable? n := fun n => by
      show _ = ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit).findTable? n
      unfold IFEnv.findTable?; rw [IFEnv.setFlags_find?, IFEnv.setFlags_rawTable?]
    obtain ⟨hfn', hfs⟩ := push_flags_found (C := ctxH Cfm H5) hF hL ci ox EH5
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ =>
      consBlockInds p isRec ((p.members.drop (i + 1)).map (·.declared)) (i + 1) (C.fe.push ci)) (by simp) ?_
    refine specR_callNC (C := ctxIns (ctxH Cfm H5) ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit) EH5
        (C.envM.insert ci.name (ecell C ox))) (D := ctxLocals ++ cbnLocals) cbnF fFlags [] [] Decl.flBody []
      (by decide) rfl (by decide) hc.flags trivial
      (fun a w s' st => PostFl (ctxIns (ctxH Cfm H5) ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit) EH5
        (C.envM.insert ci.name (ecell C ox))) (C.fe.push ci) a w s' st ∧ s' = s4)
      (fun _ w s' C' => s' = s4 ∧ ∃ H6, C' = ctxFe (ctxH (ctxIns (ctxH Cfm H5) ((C.fe.push ci).setFlags C.fe.natLit
        C.fe.strLit) EH5 (C.envM.insert ci.name (ecell C ox))) H6) (C.fe.push ci) ∧ H5 <+: H6)
      (fun a w s' st ⟨⟨H6, hp6, hsr⟩, hs'⟩ => ⟨_, ⟨hs', H6, rfl, hp6⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [] _ rfl hlk)
        (specR_pureState (fl_spec _ hokI hc.natF hc.strF hc.k.g hc.k.p s4 hfP htP hfn' hfs)))
      (fun _ w s5 C5 ⟨hs5, H6, eC, hp6⟩ => ?_)
    subst eC hs5
    have hokF := ctxOK_fe (ctxOK_H hokI H6) (fe := C.fe.push ci) (fun n => hfP n) (fun n => htP n)
    have hpC6 : C.H <+: H6 := hpC5.trans hp6
    -- the rest of the members
    set C6 := ctxFe (ctxH (ctxIns (ctxH Cfm H5) ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit) EH5
      (C.envM.insert ci.name (ecell C ox))) H6) (C.fe.push ci) with hC6
    have hc6 : CBNCodes C6 := by ctx_tr hc
    have hpE6 : C.EH <+: C6.EH := hpE5
    refine specR_congr (m' := consBlockInds p isRec ((p.members.drop (i + 1)).map (·.declared)) (i + 1) (C.fe.push ci)
      >>= fun r => pure r) (by rw [bind_pure]) ?_
    refine specR_callNC (C := C6) (D := ctxLocals ++ cbnLocals) cbnR fCbn cbnParams
      [vv cbnOm, .op .add [vv cbnI, .const 1], vv cbnN, vv cbnIr, vv cbnAll, vv cbnNP] (cbnBody C6)
      [cellA C om, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 p.members.length, boolW isRec, wAll, BitVec.ofNat 64 p.nP]
      (by decide) rfl (by decide) hc6.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cbnParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cbnParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, cbnParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cbnParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cbnParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cbnParams, ctxEnv], trivial⟩
      (PostCBN (ctxH C6 H6) p) (fun r w s' C' => ∃ EH envM H7, C' = ctxNew (ctxH C6 H6) r EH envM H7 ∧
        C6.EH <+: EH ∧ H6 <+: H7 ∧ CtxOK C' ∧ TblGate r ∧ FlagsOK r ∧ LitsPinned r C.pins ∧
        (∀ n, (∀ ms ∈ p.members, ms.declared.name ≠ n) → r.find? n = (C.fe.push ci).find? n))
      (fun r w s' st ⟨EH, envM, H7, h1, h2, h3, h4, h5, h6, h7, h8⟩ =>
        ⟨_, ⟨EH, envM, H7, rfl, h1, h2, h3, h5, h6, h7, h8⟩, h4⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cbnParams _ rfl hlk)
        (ih C6 hokF hc6 (hg.push ci) (hF.push ci)
          (show LitsPinned (C.fe.push ci) C.pins by unfold LitsPinned; rw [IFEnv.push_base]; exact hL)
          (ptrsRep_mono hpC6 (fun _ _ => memberRep_mono hpC6) hM) (enlist_mono hpE6 hall)
          (fun m hm => ⟨(hmem m hm).1, (hmem m hm).2⟩) (i + 1) H6 s5 (by omega) (by omega) (List.prefix_refl _)))
      (fun r w s7 C7 ⟨EH7, envM7, H7, eC7, hpE7, hp7, hok7, hg7, hF7, hL7, hfr7⟩ => ?_)
    subst eC7
    refine specR_returnI _ 0 rfl (fun t ht => ?_)
    refine ⟨EH7, envM7, H7, hpE6.trans hpE7, hp3'.trans (hp5'.trans (hp6.trans hp7)), hok7,
      sr_of_eq ht.sr rfl rfl rfl rfl, hg7, hF7, hL7, fun n hn => ?_⟩
    rw [hfr7 n hn, IFEnv.find?_push]
    have : (ci.name == n) = false := by
      simp only [hci, beq_eq_false_iff_ne]; exact hn ms (List.getElem_mem hin)
    simp [this]; rfl

end

end ConPanqueque.T.Ind
