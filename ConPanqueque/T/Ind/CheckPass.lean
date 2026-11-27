import ConPanqueque.T.SameLay
import ConPanqueque.T.Ind.CheckInds
import ConPanqueque.T.Ind.ClassPass
import ConPanqueque.T.Ind.KindsFlat
import ConPanqueque.T.Ind.SumCtorsAll

/-!
# `checkBlockPass` (any number of members, unnested)

`cpsBody`: the formers (`checkBlockInds`), the flush, every member's constructors (`checkBlockCtors`, `sca`),
the walk's context (`blockNestCtx`), the classes, the positivity check, the seeds (a class without a member
hangs); the pass's pieces returned as a record `[shape, nest ctx, classes, positivity, 0, 0]`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def cpsSh := ofString "cps_sh"
def cpsIr := ofString "cps_ir"
def cpsS1 := ofString "cps_s1"
def cpsOm := ofString "cps_om"
def cpsOmr := ofString "cps_omr"
def cpsOc := ofString "cps_oc"
def cpsOlw := ofString "cps_olw"
def cpsNm := ofString "cps_nm"
def cpsNp := ofString "cps_np"
def cpsRs := ofString "cps_rs"
def cpsLg := ofString "cps_lg"
def cpsIp := ofString "cps_ip"
def cpsX := ofString "cps_x"
def cpsBn := ofString "cps_bn"
def cpsPp := ofString "cps_pp"
def cpsOrr := ofString "cps_orr"
def cpsCb := ofString "cps_cb"
def cpsCp := ofString "cps_cp"
def cpsOms := ofString "cps_oms"
def cpsNcl := ofString "cps_ncl"
def cpsR := ofString "cps_r"

def fCps := ofString "checkBlockPass"

def cpsParams : List MlS := [cpsSh, cpsIr]
def cpsLocals : List MlS := [cpsS1, cpsOm, cpsOmr, cpsOc, cpsOlw, cpsNm, cpsNp, cpsRs, cpsLg, cpsIp, cpsX,
  cpsBn, cpsPp, cpsOrr, cpsCb, cpsCp, cpsOms, cpsNcl, cpsR, lJ0]

def cpsBody (C : Ctx) : ProgHOL 64 := prologue cpsLocals
  (.seq (.call (some (some (.local, cpsS1), none)) fCbi [vv cpsSh, vv cpsIr])
  (flushCode C (flushRegions false)
  (.seq (.assign .local cpsOm (.load .one (vv cpsS1)))
  (.seq (.assign .local cpsOmr (.load .one (.op .add [vv cpsOm, .const 8])))
  (.seq (.assign .local cpsOc (.load .one (vv cpsOmr)))
  (.seq (.assign .local cpsOlw (.load .one (.op .add [vv cpsOc, .const 8])))
  (.seq (.assign .local cpsNm (.load .one (vv cpsOm)))
  (.seq (.assign .local cpsNp (.load .one (.op .add [vv cpsS1, .const 16])))
  (.seq (.assign .local cpsRs (.load .one (.op .add [vv cpsS1, .const 32])))
  (.seq (.assign .local cpsLg (.load .one (.op .add [vv cpsS1, .const 40])))
  (.seq (.assign .local cpsIp (.load .one (.op .add [vv cpsS1, .const 48])))
  (.seq (.call (some (some (.local, cpsX), none)) fSca
      [vv cpsOm, .const 0, vv cpsNm, vv cpsOlw, vv cpsNp, vv cpsRs, vv cpsIp, vv cpsLg])
  (.seq (.call (some (some (.local, cpsBn), none)) fBlockNestCtx [vv cpsOm, vv cpsNp])
  (.seq (.assign .local cpsPp (.load .one (vv cpsBn)))
  (.seq (.assign .local cpsOrr (.load .one (.op .add [vv cpsS1, .const 8])))
  (.seq (.call (some (some (.local, cpsCb), none)) fCheckBlockClasses [vv cpsOm, vv cpsNp, vv cpsOrr, vv cpsOlw, vv cpsPp])
  (.seq (.call (some (some (.local, cpsCp), none)) fCbp [vv cpsOm, vv cpsNp, vv cpsRs])
  (.seq (.assign .local cpsOms (.load .one (.op .add [vv cpsCb, .const 8])))
  (.seq (.assign .local cpsNcl (.load .one (vv cpsOms)))
  (guardP cpsNcl 58
  (.seq (.call (some (some (.local, cpsX), none)) fSd [vv cpsOms, .const 0])
  (alloc6 C cpsR (vv cpsS1) (vv cpsBn) (vv cpsCb) (vv cpsCp) (.const 0) (.const 0) (.return (vv cpsR))))))))))))))))))))))))

structure CPSCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  cbi : CBICodes mode C
  cbiS : C.code.lookup fCbi = some (cbiParams.map (fun p => (p, ShapeHOL.one)), cbiBody C, .one)
  sc : SCCodes mode C
  scS : C.code.lookup fSumCtor = some (scParams.map (fun p => (p, ShapeHOL.one)), scBody C, .one)
  scs : C.code.lookup fSumCtors = some (scsParams.map (fun p => (p, ShapeHOL.one)), scsBody, .one)
  sca : C.code.lookup fSca = some (scaParams.map (fun p => (p, ShapeHOL.one)), scaBody, .one)
  bn : BNCodes C
  cbc : CBCCodes C
  k : KCodes C Comp.kBodies
  ac : Comp.AllCodes mode C
  cbp : CBPCodes C
  cse : C.code.lookup fSd = some (cseParams.map (fun p => (p, ShapeHOL.one)), cseBody, .one)
  self : C.code.lookup fCps = some (cpsParams.map (fun p => (p, ShapeHOL.one)), cpsBody C, .one)

section
variable {σ : Type}

theorem cps_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cpsLocals → (ctxEnv C ++ cpsParams.zip vals).get x = none :=
  Knot.params_none C cpsLocals cpsParams vals (by decide) (by decide)

/-- The pass's record: its environment the twin's, its pieces in the heap. -/
def PostCPS (C : Ctx) (p₀ : BlockShape) (q : BlockPass) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ EH envM H o, C.EH <+: EH ∧ C.H <+: H ∧ CtxOK (ctxNew C q.env1 EH envM H) ∧ SR (ctxNew C q.env1 EH envM H) s' st ∧
    TblGate q.env1 ∧ FlagsOK q.env1 ∧ LitsPinned q.env1 C.pins ∧
    (∀ n, (∀ ms ∈ p₀.members, ms.declared.name ≠ n) → q.env1.find? n = C.fe.find? n) ∧ w = cellA C o ∧
    (∃ o1, H[o]? = some (cellA C o1) ∧ ShapeRep C H o1 q.p) ∧
    (∃ s0 ip, q.p = { p₀ with resSort := s0, isProp := ip } ∧ ∃ l, denoteL s'.store.ls s0 = some l) ∧
    (∃ ob opp, H[o + 1]? = some (cellA C ob) ∧ H[ob]? = some (cellA C opp) ∧ BlkAt H opp (q.params.map Enc.idxW)) ∧
    (∃ ocb ord oms, H[o + 2]? = some (cellA C ocb) ∧ H[ocb]? = some (cellA C ord) ∧ ClassReadRep C H ord q.rd ∧
      H[ocb + 1]? = some (cellA C oms) ∧ TMBlk C H oms q.params q.cls) ∧
    (∃ ocp oo on outs, H[o + 3]? = some (cellA C ocp) ∧ H[ocp]? = some (cellA C oo) ∧ PRep C H oo (OutsRep C) outs ∧
      q.kinds = nestOutKinds outs ∧ H[ocp + 1]? = some (cellA C on) ∧ PRep C H on (NfRep C) q.tbl)

theorem postCPS_locals (C : Ctx) (p₀ : BlockShape) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostCPS C p₀ a w s' st → PostCPS C p₀ a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨EH, envM, H, o, h1, h2, h3, h4, h5⟩ => ⟨EH, envM, H, o, h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl, h5⟩

theorem postCPS_lower {C : Ctx} {St : EStore} (hx : Ext C.St St) {p₀ : BlockShape} :
    ∀ a w s' (st : PState σ), PostCPS (ctxSt C St) p₀ a w s' st → PostCPS C p₀ a w s' st :=
  fun _ _ _ _ ⟨EH, envM, H, o, h1, h2, h3, h4, h5⟩ =>
    ⟨EH, envM, H, o, h1, h2, ctxOK_unSt h3, sr_lower (C := ctxNew C _ EH envM H) h4 hx, h5⟩

theorem classReadRep_mono {C : Ctx} {H H' : List (BitVec 64)} (hp : H <+: H') {o : Nat} {rd : ClassRead}
    (h : ClassReadRep C H o rd) : ClassReadRep C H' o rd :=
  let ⟨os, orc, h1, h2, h3, h4⟩ := h
  ⟨os, orc, ConPanqueque.T.Decl.get_prefix h1 hp, slotBlk_mono hp h2, ConPanqueque.T.Decl.get_prefix h3 hp, blkAt_mono h4 hp⟩

theorem sumCtorOK_ext {C : Ctx} {St : EStore} (hx : Ext C.St St) {nP : Nat} {c : IConstantVal × Nat}
    (h : SumCtorOK C nP c) : SumCtorOK (ctxSt C St) nP c := by
  obtain ⟨h1, h2, ks, hkl, hks⟩ := h
  refine ⟨h1, h2, ks, hkl, fun j hj => ?_⟩
  have e := hks j hj
  rw [List.getElem?_eq_getElem (by omega)] at e ⊢
  exact hx.lss.ls.ns _ _ e

/-- What one member needs for the pass. -/
def CPSMemberOK (C : Ctx) (nP : Nat) (ms : MemberShape) : Prop :=
  ms.cvT.levelParams.length < 2 ^ 59 ∧ ms.nIdx < 2 ^ 56 ∧ ms.ctors.length < 2 ^ 58 ∧
  (∃ ks : List ConLeche.Name, ∃ hkl : ks.length = ms.cvT.levelParams.length,
    ∀ j (hj : j < ms.cvT.levelParams.length), denoteN C.St.ns ms.cvT.levelParams[j] = some (ks[j]'(by omega))) ∧
  CVDen ms.declared C.St ∧ C.fe.find? ms.declared.name = none ∧ ∀ c ∈ ms.ctors, CVDen c.1 C.St ∧ SumCtorOK C nP c

set_option maxHeartbeats 64000000 in
/-- **`checkBlockPass`**: any number of members (at least one), unnested. -/
theorem cps_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hpl : C.saved = none) (hc : CPSCodes mode C)
    (hg : TblGate C.fe) (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins)
    (heqS : ∀ (C' : Ctx), SameLay C C' → CtxOK C' → ∀ (H : List (BitVec 64)) (u v : LIdx) (s : AState)
      (lu lv : ConLeche.Level), denoteL s.store.ls u = some lu → denoteL s.store.ls v = some lv → CachesOK s →
      SpecR (σ := σ) (Pre (ctxH C' H) s [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s (lvlEq? u v)
        (fun o w s' st => LLeq.PostOB (ctxH C' H) o w s' st))
    (p₀ : BlockShape) (hne : p₀.members ≠ [])
    (osh : Nat) (hsh : ShapeRep C C.H osh p₀) (isRec : Bool)
    (hnP : p₀.nP < 2 ^ 55) (hml : p₀.members.length < 2 ^ 55) (hrl : p₀.recs.length < 2 ^ 59)
    (hmem : ∀ ms ∈ p₀.members, CPSMemberOK C p₀.nP ms)
    (hrecs : ∀ rc ∈ p₀.recs, rc.mI < 2 ^ 56 ∧ rc.rP < 2 ^ 61)
    (hrun : ∀ (s0 : LIdx) (ip : Bool) (s s1 : AState) (ctx : NestCtx) (holes : List EIdx), StateOK s → Ext C.St s.store →
      (denoteL s.store.ls s0).isSome = true →
      blockNestCtx { p₀ with resSort := s0, isProp := ip } s = .ok ((ctx, holes), s1) →
      (∃ vs, denoteLs s1.store.lss ctx.lvls = some vs) ∧ ctx.params.length < 2 ^ 56 ∧ holes.length < 2 ^ 56)
    (s : AState) :
    SpecR (σ := σ) (Pre C s (cpsParams.zip [cellA C osh, boolW isRec])) (cpsBody C) s
      (checkBlockPass mode C.fe p₀ isRec) (PostCPS C p₀) := by
  refine specR_prologue (postCPS_locals C p₀) (cps_none C _) ?_
  unfold checkBlockPass
  obtain ⟨ms0, rest, hms⟩ : ∃ a l, p₀.members = a :: l := by
    cases h : p₀.members with
    | nil => exact absurd h hne
    | cons a l => exact ⟨a, l, rfl⟩
  have hlpp : p₀.lps = ms0.cvT.levelParams := by simp [BlockShape.lps, hms]
  obtain ⟨hlp, -, -, ⟨ks, hkl, hks⟩, -⟩ := hmem ms0 (by simp [hms])
  refine specR_callNC (C := C) cpsS1 fCbi cbiParams [vv cpsSh, vv cpsIr] (cbiBody C) [cellA C osh, boolW isRec]
    (by decide) rfl (by decide) hc.cbiS
    ⟨by simp +decide [sev, Env.get, cpsParams, ctxEnv], by simp +decide [sev, Env.get, cpsParams, ctxEnv], trivial⟩
    (PostCBI C p₀)
    (fun r w s' C' => ∃ EH envM H o, C' = ctxNew C r.1 EH envM H ∧ C.EH <+: EH ∧ C.H <+: H ∧
      CtxOK (ctxNew C r.1 EH envM H) ∧ TblGate r.1 ∧ FlagsOK r.1 ∧ LitsPinned r.1 C.pins ∧
      (∀ n, (∀ ms ∈ p₀.members, ms.declared.name ≠ n) → r.1.find? n = C.fe.find? n) ∧ w = cellA C o ∧
      ShapeRep C H o r.2 ∧ ∃ s0 ip, r.2 = { p₀ with resSort := s0, isProp := ip } ∧ ∃ l, denoteL s'.store.ls s0 = some l)
    (fun r w s' st ⟨EH, envM, H, o, h1, h2, h3, h4, h5⟩ => ⟨_, ⟨EH, envM, H, o, rfl, h1, h2, h3, h5⟩, h4⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cbiParams _ rfl hlk)
      (cbi_spec mode ra C hok hs hc.cbi hg hF hL heqS p₀ osh hsh isRec (by omega) (by omega)
        (fun ms hm => by
          obtain ⟨h1, h2, -, h4, h5, h6, -⟩ := hmem ms hm
          exact ⟨by omega, by omega, h4, h5, h6⟩) s))
    (fun r w s1 C1 ⟨EH1, envM1, H1, o1, eC, hpE1, hp1, hok1, hg1, hF1, hL1, hf1, ew, hsh1, s0, ip, hp₁, l0, hl0⟩ => ?_)
  subst eC ew
  obtain ⟨fe₁, p₁⟩ := r
  simp only at hp₁ hsh1 hf1 hg1 hF1 hL1 hok1 ⊢
  subst hp₁
  set p₁ : BlockShape := { p₀ with resSort := s0, isProp := ip } with hp₁
  have hp1' : C.H <+: H1 := hp1
  refine specR_flushTopI hok1 hpl false flushCaches rfl (by decide) ?_
  generalize hsF : flushedS false s1 = sF
  have hstF : sF.store = s1.store := by rw [← hsF]; rfl
  refine specR_atEntry fun tF htF => ?_
  have hxF : Ext C.St sF.store := htF.sr.floor
  refine specR_invRaise (R' := PostCPS (ctxSt C sF.store) p₀) ?_ (fun a w s' t hx h => postCPS_lower (C := C) hx a w s' t h)
  set C2 := ctxSt (ctxNew C fe₁ EH1 envM1 H1) sF.store with hC2
  have hok2 : CtxOK C2 := ctxOK_St hok1 _
  obtain ⟨⟨om, hom, hM⟩, ⟨or_, hor, hR⟩, hnP1, hel1, hrs1, hlg1, hip1⟩ := hsh1
  have hm0 : p₁.members = ms0 :: rest := hms
  obtain ⟨omr, homr, hmr⟩ := hM.2 0 (by simp [hm0])
  simp only [hm0, List.getElem_cons_zero] at hmr
  obtain ⟨⟨oc, hoc, hcv⟩, -, -, -⟩ := hmr
  obtain ⟨wl, hwl, olp, hwo, hlpb⟩ := hcv.2.1
  refine UD.specR_heapLoadI' (C := C2) cpsOm _ o1 _ hom (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cpsParams, ctxEnv] <;> rfl) ?_
  refine UD.specR_heapLoadI' (C := C2) cpsOmr _ (om + 1 + 0) _ homr (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C om) ?_
  refine UD.specR_heapLoadI' (C := C2) cpsOc (vv cpsOmr) omr _ hoc (by decide) (by simp [sev, Env.get_cons] <;> rfl) ?_
  refine UD.specR_heapLoadI' (C := C2) cpsOlw _ (oc + 1) _ hwl (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C oc) ?_
  rw [hwo]
  refine UD.specR_heapLoadI' (C := C2) cpsNm (vv cpsOm) om _ hM.1 (by decide) (by simp [sev, Env.get_cons] <;> rfl) ?_
  refine UD.specR_heapLoadI' (C := C2) cpsNp _ (o1 + 2) _ hnP1.1 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cpsParams, ctxEnv]; exact cellA_add_ofNat C o1 2) ?_
  refine UD.specR_heapLoadI' (C := C2) cpsRs _ (o1 + 4) _ hrs1 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cpsParams, ctxEnv]; exact cellA_add_ofNat C o1 4) ?_
  refine UD.specR_heapLoadI' (C := C2) cpsLg _ (o1 + 5) _ hlg1 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cpsParams, ctxEnv]; exact cellA_add_ofNat C o1 5) ?_
  refine UD.specR_heapLoadI' (C := C2) cpsIp _ (o1 + 6) _ hip1 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cpsParams, ctxEnv]; exact cellA_add_ofNat C o1 6) ?_
  have hlp1 : p₁.lps = ms0.cvT.levelParams := by simp [hp₁, BlockShape.lps, hms]
  have hml1 : p₁.members.length = p₀.members.length := rfl
  have hokS : CtxOK (ctxSt C sF.store) := ctxOK_St hok sF.store
  have hscaC : SCACodes mode C2 := ⟨by ctx_tr hc.sc, by ctx_tr hc.scS, hc.scs, hc.sca⟩
  refine specR_callNIH (C := C2) cpsX fSca scaParams
    [vv cpsOm, .const 0, vv cpsNm, vv cpsOlw, vv cpsNp, vv cpsRs, vv cpsIp, vv cpsLg] scaBody
    [cellA C om, BitVec.ofNat 64 0, BitVec.ofNat 64 p₁.members.length, cellA C olp, BitVec.ofNat 64 p₀.nP,
      Enc.idxW s0, boolW ip, boolW p₀.large] (by decide) rfl (by decide) hc.sca
    ⟨by simp +decide [sev, Env.get_cons] <;> rfl, by simp [sev], by simp +decide [sev, Env.get_cons] <;> rfl,
      by simp +decide [sev, Env.get_cons] <;> rfl, by simp +decide [sev, Env.get_cons] <;> rfl,
      by simp +decide [sev, Env.get_cons] <;> rfl, by simp +decide [sev, Env.get_cons] <;> rfl,
      by simp +decide [sev, Env.get_cons] <;> rfl, trivial⟩
    (Decl.PostU (ctxH C2 H1)) (fun _ _ _ _ => True)
    (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu scaParams _ rfl hlk)
      (by
        have h := sca_spec mode ra C2 hok2 hs hscaC (heqS C2 rfl hok2) p₁ om olp hM (by omega) l0
          (by show denoteL sF.store.ls s0 = _; rw [hstF]; exact hl0) (by rw [hlp1]; omega)
          (by rw [hlp1]; exact hlpb)
          (fun ms hm => by
            obtain ⟨-, h2, h3, -, -, -, h7⟩ := hmem ms hm
            exact ⟨h2, h3, fun i hi => sumCtorOK_ext (C := ctxNew C fe₁ EH1 envM1 H1) hxF
              (h7 _ (List.getElem_mem hi)).2⟩)
          _ 0 H1 sF rfl (by omega) (List.prefix_refl _)
        rw [List.drop_zero] at h
        exact h))
    (fun _ w s3 H3 hp3 _ => ?_)
  have hp3' : H1 <+: H3 := hp3
  refine specR_callNIH (C := ctxH C2 H3) cpsBn fBlockNestCtx bnParams [vv cpsOm, vv cpsNp] (bnBody C)
    [cellA C om, BitVec.ofNat 64 p₁.nP] (by decide) rfl (by decide) (by ctx_tr hc.bn.self)
    ⟨by simp +decide [sev, Env.get_cons] <;> rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (PostBN (ctxH C2 H3) p₁)
    (fun r w s' H' => ∃ orb opp, w = cellA C orb ∧ H'[orb]? = some (cellA C opp) ∧ BlkAt H' opp (r.1.params.map Enc.idxW))
    (fun r w s' st ⟨H', hp', hsr, _, _, _, _, _, _, orb, oq, oh, hw, h1, h2, _⟩ => ⟨H', hp', ⟨orb, oq, hw, h1, h2⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu bnParams _ rfl hlk)
      (bn_spec ra C2 hok2 (by ctx_tr hc.bn) p₁ om H3 hp3'
        (ptrsRep_mono hp3' (fun _ _ h => memberRep_mono hp3' h) hM) (by show p₀.nP + p₀.members.length < _; omega)
        (by omega) (by rw [hlp1]; omega) s3))
    (fun bnr w s4 H4 hp4 ⟨orb, opp, ew, hpp4, hppb⟩ => ?_)
  subst ew
  obtain ⟨ctx, holes⟩ := bnr
  simp only at hppb ⊢
  have hp4' : H3 <+: H4 := hp4
  have hp14 : H1 <+: H4 := hp3'.trans hp4'
  refine UD.specR_heapLoadI' (C := ctxH C2 H4) cpsPp (vv cpsBn) orb _ hpp4 (by decide) (by simp [sev, Env.get_cons] <;> rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C2 H4) cpsOrr _ (o1 + 1) _ (ConPanqueque.T.Decl.get_prefix hor hp14) (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cpsParams, ctxEnv]; exact cellA_add8 C o1) ?_
  refine specR_callNIH (C := ctxH C2 H4) cpsCb fCheckBlockClasses cbcParams [vv cpsOm, vv cpsNp, vv cpsOrr, vv cpsOlw, vv cpsPp]
    (cbcBody C) [cellA C om, BitVec.ofNat 64 p₁.nP, cellA C or_, cellA C olp, cellA C opp] (by decide) rfl (by decide)
    (by ctx_tr hc.cbc.self)
    ⟨by simp +decide [sev, Env.get_cons] <;> rfl, by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons] <;> rfl,
      by simp +decide [sev, Env.get_cons] <;> rfl, by simp +decide [sev, Env.get_cons] <;> rfl, trivial⟩
    (PostCBC (ctxH C2 H4) ctx.params)
    (fun r w s' H' => ∃ ocb ord oms, w = cellA C ocb ∧ H'[ocb]? = some (cellA C ord) ∧ ClassReadRep C H' ord r.1 ∧
      H'[ocb + 1]? = some (cellA C oms) ∧ TMBlk C H' oms ctx.params r.2)
    (fun r w s' st ⟨H', o, ord, oms, hp', hw, h1, h2, h3, h4, hs⟩ => ⟨H', hp', ⟨o, ord, oms, hw, h1, h2, h3, h4⟩, hs⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cbcParams _ rfl hlk)
      (cbc_spec ra C2 hok2 (by ctx_tr hc.cbc) mode p₁ ctx.params om or_ olp opp H4 hp14
        (ptrsRep_mono hp14 (fun _ _ h => memberRep_mono hp14 h) hM) (ptrsRep_mono hp14 (fun _ _ h => recRep_mono hp14 h) hR)
        (by omega) (by show p₀.nP < _; omega) hrl
        (fun i hi => (hrecs _ (List.getElem_mem hi)).1)
        (fun i hi => (hrecs _ (List.getElem_mem hi)).2)
        (fun i hi => by have := (hmem _ (List.getElem_mem hi)).2.1; omega)
        (by rw [hlp1]; exact eblk_mono hlpb hp14) (by rw [hlp1]; omega) hppb s4))
    (fun cbr w s5 H5 hp5 ⟨ocb, ord, oms, ew, hcb5, hrd5, hms5, htm5⟩ => ?_)
  subst ew
  obtain ⟨rd, cls⟩ := cbr
  simp only at hrd5 htm5 ⊢
  have hp5' : H4 <+: H5 := hp5
  have hp15 : H1 <+: H5 := hp14.trans hp5'
  refine specR_atEntry fun t5 ht5 => ?_
  have hx5 : Ext C.St s5.store := hxF.trans ht5.sr.floor
  have hs0d : (denoteL s5.store.ls s0).isSome = true := by
    rw [ConRon.Bridge.denoteL_ext (show denoteL sF.store.ls s0 = some l0 by rw [hstF]; exact hl0) ht5.sr.floor]; rfl
  refine specR_callNIH (C := ctxH C2 H5) cpsCp fCbp cbpParams [vv cpsOm, vv cpsNp, vv cpsRs] (cbpBody C)
    [cellA C om, BitVec.ofNat 64 p₁.nP, Enc.idxW p₁.resSort] (by decide) rfl (by decide) (by ctx_tr hc.cbp.self)
    ⟨by simp +decide [sev, Env.get_cons] <;> rfl, by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], trivial⟩
    (PostCBP (ctxH C2 H5))
    (fun r w s' H' => ∃ ocp oo on, w = cellA C ocp ∧ H'[ocp]? = some (cellA C oo) ∧ PRep C H' oo (OutsRep C) r.1 ∧
      H'[ocp + 1]? = some (cellA C on) ∧ PRep C H' on (NfRep C) r.2.ctorNfs.toList)
    (fun r w s' st ⟨H', o, oo, on, hp', hw, h1, h2, h3, h4, hs⟩ => ⟨H', hp', ⟨o, oo, on, hw, h1, h2, h3, h4⟩, hs⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cbpParams _ rfl hlk)
      (cbp_spec ra mode C2 hok2 hs (by ctx_tr hc.k) (by ctx_tr hc.ac) (by ctx_tr hc.cbp)
        (fun C' hcode => heqS C' hcode) p₁ om hM (by omega) (by show p₀.nP < _; omega) (by rw [hlp1]; omega)
        (fun i hi => by have := (hmem _ (List.getElem_mem hi)).2.1; omega)
        (fun m hm => by
          obtain ⟨-, -, h3, -, -, -, h7⟩ := hmem m hm
          exact ⟨h3, fun c hc' => ⟨cvDen_ext (h7 c hc').1 hxF, by have := (h7 c hc').2.1; omega⟩⟩)
        ks (by rw [hlp1]; exact hkl)
        (fun j hj => by
          have hj' : j < ms0.cvT.levelParams.length := by rw [← hlp1]; exact hj
          have e := hks j hj'
          have hjj : p₁.lps[j] = ms0.cvT.levelParams[j] := by simp [hlp1]
          rw [hjj]; exact hxF.lss.ls.ns _ _ e)
        l0 (by show denoteL sF.store.ls s0 = _; rw [hstF]; exact hl0) s5
        (fun s1' ctx' holes' h => hrun s0 ip s5 s1' ctx' holes' ⟨ht5.sr.twf⟩ hx5 hs0d h) H5 hp15))
    (fun cpr w s6 H6 hp6 ⟨ocp, oo, on, ew, hcp6, hout6, hon6, hnf6⟩ => ?_)
  subst ew
  obtain ⟨outs, pos⟩ := cpr
  simp only at hout6 hnf6 ⊢
  have hp6' : H5 <+: H6 := hp6
  have hp16 : H1 <+: H6 := hp15.trans hp6'
  have hp56 := hp6'
  refine UD.specR_heapLoadI' (C := ctxH C2 H6) cpsOms _ (ocb + 1) _ (ConPanqueque.T.Decl.get_prefix hms5 hp56) (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C ocb) ?_
  have htm6 := tmBlk_mono hp56 htm5
  obtain ⟨ps, hpsl, hpsb, hpsr⟩ := htm6
  have hncl : H6[oms]? = some (BitVec.ofNat 64 cls.length) := by simpa [hpsl] using hpsb.1
  refine UD.specR_heapLoadI' (C := ctxH C2 H6) cpsNcl (vv cpsOms) oms _ hncl (by decide) (by simp [sev, Env.get_cons] <;> rfl) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hbl := blkAt_len (ctxOK_H hok2 H6) hHN hpsb
  simp only [List.length_map] at hbl
  refine specR_guardI cpsNcl cls.length 58 (by decide) (by simp [Env.get_cons]) (by omega) (fun hcl58 => ?_)
  refine specR_callNIH (C := ctxH C2 H6) cpsX fSd cseParams [vv cpsOms, .const 0] cseBody
    [cellA C oms, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.cse
    ⟨by simp +decide [sev, Env.get_cons] <;> rfl, by simp [sev], trivial⟩
    (PostCse (ctxH C2 H6)) (fun r _ _ H' => r = [] ∧ H' = H6)
    (fun r w s' st ⟨hr, hs⟩ => ⟨H6, List.prefix_refl _, ⟨hr, rfl⟩, hs⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cseParams _ rfl hlk)
      (cse_spec C2 hok2 hc.cse ctx holes ctx.params cls oms H6 ⟨ps, hpsl, hpsb, hpsr⟩ (by omega) _ 0 s6 rfl (by omega)))
    (fun sd w s7 H7 _ ⟨er, eH⟩ => ?_)
  subst er; subst H7
  simp only [nestSeeds, pure_bind]
  refine specR_alloc6I (ctxOK_H hok2 H6) cpsR (vv cpsS1) (vv cpsBn) (vv cpsCb) (vv cpsCp) (.const 0) (.const 0)
    (cellA C o1) (cellA C orb) (cellA C ocb) (cellA C ocp) 0 0 (by decide)
    (fun _ => by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cpsParams, ctxEnv] <;> rfl)
    (fun _ => by simp +decide [sev, Env.get_cons] <;> rfl) (fun _ => by simp +decide [sev, Env.get_cons] <;> rfl)
    (fun _ => by simp +decide [sev, Env.get_cons] <;> rfl) (fun _ => rfl) (fun _ => rfl) (fun H8 ws8 hp8 hws8 _ => ?_)
  obtain ⟨g0, g1, g2, g3, -, -⟩ := img6_get H8 ws8 (cellA C o1) (cellA C orb) (cellA C ocb) (cellA C ocp) 0 0 hws8
  have hp8' : H6 <+: _ := (hp8 : H6 <+: H8).trans (img6_prefix H8 ws8 (cellA C o1) (cellA C orb) (cellA C ocb) (cellA C ocp) 0 0 hws8)
  set H9 := img6 H8 ws8 (cellA C o1) (cellA C orb) (cellA C ocb) (cellA C ocp) 0 0 with hH9
  have hp49 : H4 <+: H9 := hp5'.trans (hp6'.trans hp8')
  have hp19 : H1 <+: H9 := hp16.trans hp8'
  refine specR_returnI _ (cellA C H8.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ?_)
  refine ⟨EH1, envM1, H9, H8.length, hpE1, hp1'.trans hp19, ctxOK_H hok2 H9, sr_of_eq ht.sr rfl rfl rfl rfl, hg1, hF1, hL1,
    hf1, rfl, ⟨o1, g0, shapeRep_mono hp19 ⟨⟨om, hom, hM⟩, ⟨or_, hor, hR⟩, hnP1, ?_, hrs1, hlg1, hip1⟩⟩,
    ⟨s0, ip, rfl, l0, ?_⟩, ⟨orb, opp, g1, ConPanqueque.T.Decl.get_prefix hpp4 hp49, blkAt_mono hppb hp49⟩,
    ⟨ocb, ord, oms, g2, ConPanqueque.T.Decl.get_prefix hcb5 (hp6'.trans hp8'), classReadRep_mono (hp6'.trans hp8') hrd5,
      ConPanqueque.T.Decl.get_prefix hms5 (hp6'.trans hp8'), tmBlk_mono (hp6'.trans hp8') htm5⟩,
    ⟨ocp, oo, on, outs, g3, ConPanqueque.T.Decl.get_prefix hcp6 hp8', pRep_mono hp8' (fun _ _ h => outsRep_mono hp8' h) hout6,
      rfl, ConPanqueque.T.Decl.get_prefix hon6 hp8', pRep_mono hp8' (fun _ _ h => nfRep_mono hp8' h) hnf6⟩⟩
  · exact hel1
  · exact denoteL_ext hl0 (by rw [← hstF]; exact ht.sr.floor)

end

end ConPanqueque.T.Ind
