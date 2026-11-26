import ConPanqueque.T.Ind.FeR

/-!
# `genRecCheck` assembled (one member, one recursor, one class)

`gbBody`: from the generator's data on: the prefix (`prefixBinders`, none hangs), the recursor's generated type
checked and compared (`classRecTyOk`), then the rules under the temporary push (`genRules`).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

/-- `genRecCheck` from the generator's data on. -/
def genRecB (mode : ConLeche.CheckMode) (fe : IFEnv) (p : BlockShape) (g0 : ClassGen) (cvRis : List IConstantVal)
    (recCls : List Nat) : AM (IFEnv × List (IConstantVal × TargetMajor × List EIdx)) := do
  match ← g0.prefixBinders with
  | none => fail (.internal "generated recursor: recursor prefix")
  | some pre => do
    let g := { g0 with pre := pre }
    let cvGs ← classRecTysOk mode fe g p.k p.recs cvRis recCls
    genRules mode fe p g recCls cvGs

theorem classRecTyOk_shape {mode : ConLeche.CheckMode} {fe : IFEnv} {g : ClassGen} {k : Nat} {rc : RecShape}
    {cvRi : IConstantVal} {c : Nat} {s s' : AState} {cv : IConstantVal}
    (h : classRecTyOk mode fe g k rc cvRi c s = .ok (cv, s')) :
    cv.name = rc.cvR.name ∧ cv.levelParams = rc.cvR.levelParams := by
  unfold classRecTyOk at h
  obtain ⟨ci, s1, -, h2⟩ := AM.bind_ok h
  dsimp only at h2
  split at h2
  · obtain ⟨_, s2, -, h3⟩ := AM.bind_ok h2
    split at h3
    · obtain ⟨_, s3, -, h4⟩ := AM.bind_ok h3
      obtain ⟨o, s4, -, h5⟩ := AM.bind_ok h4
      split at h5
      · exact (AM.fail_ok h5).elim
      · obtain ⟨_, s5, -, h6⟩ := AM.bind_ok h5
        obtain ⟨rfl, -⟩ := AM.pure_ok h6
        exact ⟨rfl, rfl⟩
    · obtain ⟨_, s3, h3', -⟩ := AM.bind_ok h3
      exact (AM.fail_ok h3').elim
  · obtain ⟨_, s2, h2', -⟩ := AM.bind_ok h2
    exact (AM.fail_ok h2').elim

def gbOpp := ofString "gb_opp"
def gbOsl := ofString "gb_osl"
def gbNsl := ofString "gb_nsl"
def gbNp := ofString "gb_np"
def gbOc := ofString "gb_oc"
def gbNc := ofString "gb_nc"
def gbPd := ofString "gb_pd"
def gbNd := ofString "gb_nd"
def gbFty := ofString "gb_fty"
def gbNi := ofString "gb_ni"
def gbInd := ofString "gb_ind"
def gbLv := ofString "gb_lv"
def gbEl := ofString "gb_el"
def gbNpc := ofString "gb_npc"
def gbOrr := ofString "gb_orr"
def gbPr := ofString "gb_pr"
def gbPl := ofString "gb_pl"
def gbN0 := ofString "gb_n0"
def gbCv := ofString "gb_cv"
def gbRs := ofString "gb_rs"
def fGb := ofString "genRecB"

def gbParams : List MlS := [gbOpp, gbOsl, gbNsl, gbNp, gbOc, gbNc, gbPd, gbNd, gbFty, gbNi, gbInd, gbLv, gbEl, gbNpc, gbOrr]
def gbLocals : List MlS := [gbPr, gbPl, gbN0, gbCv, gbRs]

def gbBody : ProgHOL 64 := prologue gbLocals
  (.seq (.call (some (some (.local, gbPr), none)) fPb
      [vv gbOpp, vv gbOsl, vv gbNsl, vv gbNp, vv gbOc, vv gbNc, vv gbPd, vv gbNd, vv gbFty, vv gbNi, vv gbInd, vv gbLv,
        vv gbEl, vv gbNpc])
  (.seq (.assign .local gbPl (.load .one (vv gbPr)))
  (.ite (.cmp .lower (vv gbPl) (.const (BitVec.ofNat 64 (2 ^ 56))))
  (.seq (.assign .local gbN0 (.op .add [vv gbNp, vv gbNsl]))
  (.seq (.call (some (some (.local, gbCv), none)) fCro
      [vv gbOrr, vv gbN0, vv gbPr, vv gbPl, vv gbPd, vv gbNd, vv gbFty, vv gbNi, vv gbInd, vv gbLv, vv gbNp])
  (.seq (.call (some (some (.local, gbRs), none)) fCfr
      [vv gbCv, vv gbOrr, vv gbOc, vv gbNc, vv gbPl, vv gbNp, vv gbOpp, vv gbOsl, vv gbPr, vv gbN0])
    (.return (vv gbRs)))))
  hang)))

structure GBCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  pb : PBCodes C
  cro : CROCodes mode C
  cfr : CFRCodes mode C
  self : C.code.lookup fGb = some (gbParams.map (fun p => (p, ShapeHOL.one)), gbBody, .one)

section
variable {σ : Type}

theorem gb_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ gbLocals → (ctxEnv C ++ gbParams.zip vals).get x = none :=
  Knot.params_none C gbLocals gbParams vals (by decide) (by decide)

theorem postGR_lower {C : Ctx} {St : EStore} (hx : Ext C.St St) {H : List (BitVec 64)} (hp : C.H <+: H) :
    ∀ a w s' (st : PState σ), PostGR (ctxSt (ctxH C H) St) a w s' st → PostGR C a w s' st := by
  intro a w s' st ⟨EH, envM, H', o, h1, h2, h3, h4, h5⟩
  refine ⟨EH, envM, H', o, h1, hp.trans h2, ?_, sr_lower (St := St) h4 hx, h5⟩
  have := h3; cases this; constructor <;> assumption

set_option maxHeartbeats 64000000 in
/-- **`genRecCheck` from the generator's data on**, one member, one recursor, one class. -/
theorem gb_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hpl : C.saved = none) (hc : GBCodes mode C)
    (hg : TblGate C.fe) (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins)
    (p : BlockShape) (rc : RecShape) (hrecs : p.recs = [rc]) (orr : Nat) (hrr : RecRep C C.H orr rc)
    (hrl : rc.cvR.levelParams.length < 2 ^ 59) (ks : List ConLeche.Name) (hkl : ks.length = rc.cvR.levelParams.length)
    (hks : ∀ j (hj : j < rc.cvR.levelParams.length), denoteN C.St.ns rc.cvR.levelParams[j] = some (ks[j]'(by omega)))
    (g0 : ClassGen) (m : TargetMajor) (hcls : g0.cls = [m]) (hmm : m.member = some 0) (fty : EIdx)
    (hft : g0.formerTys[0]? = some fty) (ccs : List ClassCtor) (hctors : g0.ctors = [ccs]) (k0 : ClassKey)
    (hsl0 : g0.slots[0]? = some (.motive k0))
    (opp osl oc pd : Nat) (hppl : g0.params.length < 2 ^ 56) (hpp : BlkAt C.H opp (g0.params.map Enc.idxW))
    (hsll : g0.slots.length < 2 ^ 56) (hsb : SlotBlk C C.H osl g0.slots)
    (hcl : ccs.length < 2 ^ 58) (hcs : PRep C C.H oc (fun H o cc => CCRep C H o cc) ccs)
    (hnf : ∀ x ∈ ccs, x.nF < 2 ^ 56) (hds : BlkAt C.H pd (m.ds.map Enc.idxW)) (hdl : m.ds.length < 2 ^ 56)
    (hni : m.nIdx < 2 ^ 56) (hnP : g0.nP < 2 ^ 56) (hnpc : m.nPc < 2 ^ 62)
    (hcb : ∀ sl ∈ g0.slots, ∀ c C' ihs, sl = .minor c C' ihs → c < 2 ^ 63)
    (hcvd : ∀ (pre : List EIdx) s s' cv, classRecTyOk mode C.fe { g0 with pre := pre } p.k rc rc.cvR 0 s = .ok (cv, s') →
      (denoteE s'.store cv.type).isSome = true)
    (s : AState) :
    SpecR (σ := σ) (Pre C s (gbParams.zip [cellA C opp, cellA C osl, BitVec.ofNat 64 g0.slots.length,
        BitVec.ofNat 64 g0.nP, cellA C oc, BitVec.ofNat 64 ccs.length, cellA C pd, BitVec.ofNat 64 m.ds.length,
        Enc.idxW fty, BitVec.ofNat 64 m.nIdx, Enc.idxW m.ind, Enc.idxW m.lvls, Enc.idxW g0.elim,
        BitVec.ofNat 64 m.nPc, cellA C orr])) gbBody s (genRecB mode C.fe p g0 [rc.cvR] [0]) (PostGR C) := by
  refine specR_prologue (postGR_locals C) (gb_none C _) ?_
  unfold genRecB
  refine specR_callNIH (C := C) gbPr fPb pbParams
    [vv gbOpp, vv gbOsl, vv gbNsl, vv gbNp, vv gbOc, vv gbNc, vv gbPd, vv gbNd, vv gbFty, vv gbNi, vv gbInd, vv gbLv,
      vv gbEl, vv gbNpc] (pbBody C)
    [cellA C opp, cellA C osl, BitVec.ofNat 64 g0.slots.length, BitVec.ofNat 64 g0.nP, cellA C oc,
      BitVec.ofNat 64 ccs.length, cellA C pd, BitVec.ofNat 64 m.ds.length, Enc.idxW fty, BitVec.ofNat 64 m.nIdx,
      Enc.idxW m.ind, Enc.idxW m.lvls, Enc.idxW g0.elim, BitVec.ofNat 64 m.nPc] (by decide) rfl (by decide) hc.pb.self
    ⟨by simp +decide [sev, Env.get, gbParams, ctxEnv], by simp +decide [sev, Env.get, gbParams, ctxEnv],
      by simp +decide [sev, Env.get, gbParams, ctxEnv], by simp +decide [sev, Env.get, gbParams, ctxEnv],
      by simp +decide [sev, Env.get, gbParams, ctxEnv], by simp +decide [sev, Env.get, gbParams, ctxEnv],
      by simp +decide [sev, Env.get, gbParams, ctxEnv], by simp +decide [sev, Env.get, gbParams, ctxEnv],
      by simp +decide [sev, Env.get, gbParams, ctxEnv], by simp +decide [sev, Env.get, gbParams, ctxEnv],
      by simp +decide [sev, Env.get, gbParams, ctxEnv], by simp +decide [sev, Env.get, gbParams, ctxEnv],
      by simp +decide [sev, Env.get, gbParams, ctxEnv], by simp +decide [sev, Env.get, gbParams, ctxEnv], trivial⟩
    (PostSL C) (fun o w _ H' => ∃ ds ob, o = some ds ∧ w = cellA C ob ∧ BlkAt H' ob (ds.map Enc.idxW))
    (fun o w s' st ⟨ds, H', ob, h0, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨ds, ob, h0, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pbParams _ rfl hlk)
      (pb_spec ra C hok hc.pb g0 m hcls fty hft ccs hctors k0 hsl0 opp osl oc pd hppl hpp hsll hsb hcl hcs hnf hds hdl
        hni hnP hnpc hcb s))
    (fun o w s1 H1 hp1 ⟨pre, opr, ho, hw, hpr⟩ => ?_)
  subst ho hw
  have hp1' : C.H <+: H1 := hp1
  simp only
  have hprl0 : H1[opr]? = some (BitVec.ofNat 64 pre.length) := by simpa using hpr.1
  refine UD.specR_heapLoadI' (C := ctxH C H1) gbPl (vv gbPr) opr _ hprl0 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : H1.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  have hprlb : pre.length < 2 ^ 61 := by
    rcases Nat.eq_zero_or_pos pre.length with h0 | hpos
    · omega
    · have h1 := hpr.2 (pre.length - 1) (by simp; omega)
      have := (List.getElem?_eq_some_iff.mp h1).1
      omega
  have hlw := nd_lt_iff pre.length (2 ^ 56) (by omega) (by omega)
  by_cases hpl56 : pre.length < 2 ^ 56
  swap
  · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega)]; omega)
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega)]; omega)
    (fun _ => ?_) (fun h => absurd h (by decide))
  refine specR_assignI gbN0 _ (BitVec.ofNat 64 (g0.nP + g0.slots.length)) (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv]; rw [BitVec.ofNat_add]) ?_
  rw [hrecs]
  simp only [classRecTysOk, bind_assoc, pure_bind]
  have hok1 := ctxOK_H hok H1
  refine specR_callNIH (C := ctxH C H1) gbCv fCro croParams
    [vv gbOrr, vv gbN0, vv gbPr, vv gbPl, vv gbPd, vv gbNd, vv gbFty, vv gbNi, vv gbInd, vv gbLv, vv gbNp] (croBody C)
    [cellA C orr, BitVec.ofNat 64 (g0.nP + g0.slots.length), cellA C opr, BitVec.ofNat 64 pre.length, cellA C pd,
      BitVec.ofNat 64 m.ds.length, Enc.idxW fty, BitVec.ofNat 64 m.nIdx, Enc.idxW m.ind, Enc.idxW m.lvls,
      BitVec.ofNat 64 g0.nP] (by decide) rfl (by decide) hc.cro.self
    ⟨by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv], by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv], trivial⟩
    (fun a w s' st => classRecTyOk mode C.fe { g0 with pre := pre } p.k rc rc.cvR 0 s1 = .ok (a, s') ∧
      PostCVG (ctxH C H1) a w s' st)
    (fun cv w s' H' => classRecTyOk mode C.fe { g0 with pre := pre } p.k rc rc.cvR 0 s1 = .ok (cv, s') ∧
      ∃ o, w = cellA C o ∧ Ind.CVRep C H' o cv)
    (fun a w s' st ⟨hrun, H', o, hp', hw, hcv, hsr⟩ => ⟨H', hp', ⟨hrun, o, hw, hcv⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu croParams _ rfl hlk)
      (cro_spec mode ra (ctxH C H1) hok1 hs (by ctx_tr hc.cro) { g0 with pre := pre } m hcls hmm fty hft k0 hsl0
        opr pd hpl56 hpr hni (blkAt_mono hds hp1') hdl hnP hsll p.k rc orr (recRep_mono hp1' hrr) (by omega) ks hkl hks s1)))
    (fun cvG w s2 H2 hp2 ⟨hrun, oq, hw, hcvq⟩ => ?_)
  subst hw
  have hp2' : H1 <+: H2 := hp2
  have hpC2 : C.H <+: H2 := hp1'.trans hp2'
  obtain ⟨hnm, hlps⟩ := classRecTyOk_shape hrun
  have hty := hcvd pre s1 s2 cvG hrun
  refine specR_atEntry fun t2 ht2 => ?_
  have hfl : Ext C.St s2.store := ht2.sr.floor
  refine specR_invRaise (C := ctxH C H2) (R' := PostGR (ctxSt (ctxH C H2) s2.store)) ?_
    (fun a w s' t hx h => postGR_lower (C := C) (H := H2) hx hpC2 a w s' t h)
  have hokS := ctxOK_St (ctxOK_H hok H2) s2.store
  have hden : CVDen cvG s2.store :=
    ⟨fun n hn => by
      rw [hlps] at hn
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hn
      have := hks j hj
      rw [denoteN_isSome_ext hfl (by rw [this]; rfl)], hty, by rw [hlps]; omega⟩
  refine specR_congr (m' := genRules mode C.fe p { g0 with pre := pre } [0] [cvG] >>= fun r => pure r)
    (by simp only [bind_pure]) ?_
  refine specR_callNC (C := ctxSt (ctxH C H2) s2.store) (D := ctxLocals ++ gbLocals) gbRs fCfr cfrParams
    [vv gbCv, vv gbOrr, vv gbOc, vv gbNc, vv gbPl, vv gbNp, vv gbOpp, vv gbOsl, vv gbPr, vv gbN0] (cfrBody C)
    [cellA C oq, cellA C orr, cellA C oc, BitVec.ofNat 64 ccs.length, BitVec.ofNat 64 pre.length, BitVec.ofNat 64 g0.nP,
      cellA C opp, cellA C osl, cellA C opr, BitVec.ofNat 64 (g0.nP + g0.slots.length)] (by decide) rfl (by decide)
    hc.cfr.self
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv],
      by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv],
      by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], trivial⟩
    (PostGR (ctxSt (ctxH C H2) s2.store))
    (fun r w s' C' => ∃ EH envM H o, C' = ctxNew (ctxSt (ctxH C H2) s2.store) r.1 EH envM H ∧
      (ctxSt (ctxH C H2) s2.store).EH <+: EH ∧ (ctxSt (ctxH C H2) s2.store).H <+: H ∧
      CtxOK (ctxNew (ctxSt (ctxH C H2) s2.store) r.1 EH envM H) ∧
      TblGate r.1 ∧ FlagsOK r.1 ∧ LitsPinned r.1 C.pins ∧ (∀ n, r.1.find? n = C.fe.find? n) ∧
      (∀ n, r.1.findTable? n = C.fe.findTable? n) ∧
      ∃ cv m rhss orh oc, r.2 = [(cv, m, rhss)] ∧ w = cellA C o ∧ H[o]? = some (cellA C orh) ∧
      H[o + 1]? = some (cellA C oc) ∧ BlkAt H orh (rhss.map Enc.idxW) ∧ CVRep C H oc cv)
    (fun r w s' st ⟨EH, envM, H, o, h1, h2, h3, h4, h5⟩ => ⟨_, ⟨EH, envM, H, o, rfl, h1, h2, h3, h5⟩, h4⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cfrParams _ rfl hlk)
      (cfr_spec mode ra (ctxSt (ctxH C H2) s2.store) hokS hs hpl (by ctx_tr hc.cfr) hg hF hL p rc
        (by rw [hrecs]; rfl) orr (recRep_mono hpC2 hrr) { g0 with pre := pre } m hcls cvG oq hcvq
        (by rw [hlps]; exact hrl) ks (by rw [hlps]; exact hkl)
        (fun j hj => by
          have hj' : j < rc.cvR.levelParams.length := by rw [← hlps]; exact hj
          have e := hks j hj'
          have hjj : cvG.levelParams[j] = rc.cvR.levelParams[j] := by simp [hlps]
          rw [hjj]; exact hfl.lss.ls.ns _ _ e)
        hden opp (blkAt_mono hpp hpC2) hppl osl (slotBlk_mono hpC2 hsb) hsll hcb opr (blkAt_mono hpr hp2') hpl56 hnP ccs
        (by simp [hctors]) oc (pRep_mono hpC2 (fun _ _ => ccRep_mono hpC2) hcs) hcl hnf s2))
    (fun r w s3 C3 ⟨EH, envM, H, o, eC, h1, h2, h3, h4⟩ => ?_)
  subst eC
  exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨EH, envM, H, o, h1, h2, h3,
    sr_of_eq ht.sr rfl rfl rfl rfl, h4⟩)

end

end ConPanqueque.T.Ind
