import ConPanqueque.T.Ind.FeR
import ConPanqueque.T.Ind.RecTys
import ConPanqueque.T.Ind.RecGen

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

theorem classRecTysOk_one {mode : ConLeche.CheckMode} {fe : IFEnv} {g : ClassGen} {k : Nat} {rc : RecShape}
    {cv : IConstantVal} {c : Nat} {s s' : AState} {xs : List IConstantVal}
    (h : classRecTysOk mode fe g k [rc] [cv] [c] s = .ok (xs, s')) :
    ∃ x, classRecTyOk mode fe g k rc cv c s = .ok (x, s') ∧ xs = [x] := by
  simp only [classRecTysOk] at h
  obtain ⟨x, s1, h1, h⟩ := AM.bind_ok h
  obtain ⟨xs', s2, h2, h⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h2
  exact ⟨x, h1, rfl⟩

theorem genRules_out_one {mode : ConLeche.CheckMode} {fe : IFEnv} {p : BlockShape} {g : ClassGen}
    {cv : IConstantVal} {m : TargetMajor} (hcls : g.cls = [m]) {s s' : AState}
    {r : IFEnv × List (IConstantVal × TargetMajor × List EIdx)}
    (h : genRules mode fe p g [0] [cv] s = .ok (r, s')) : ∃ rhss, r.2 = [(cv, m, rhss)] := by
  rw [genRules_eq] at h
  obtain ⟨out, s1, h1, h2⟩ := AM.bind_ok h
  obtain ⟨_, s3, -, h4⟩ := AM.bind_ok h2
  obtain ⟨rfl, -⟩ := AM.pure_ok h4
  unfold gprM at h1
  obtain ⟨_, s5, -, h6⟩ := AM.bind_ok h1
  simp only [List.zip_cons_cons, List.zip_nil_right, classRecsRulesOk, hcls, targetMajorAt, List.getElem?_cons_zero,
    pure_bind, bind_assoc] at h6
  obtain ⟨rhss, s7, -, h8⟩ := AM.bind_ok h6
  obtain ⟨rfl, -⟩ := AM.pure_ok h8
  exact ⟨rhss, rfl⟩

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
def gbOms := ofString "gb_oms"
def gbCss := ofString "gb_css"
def gbFts := ofString "gb_fts"
def gbOrl := ofString "gb_orl"
def gbOrc := ofString "gb_orc"
def gbNr := ofString "gb_nr"
def gbCs := ofString "gb_cs"
def gbT := ofString "gb_t"
def fGb := ofString "genRecB"

def gbParams : List MlS := [gbOpp, gbOsl, gbNsl, gbNp, gbOc, gbNc, gbNi, gbEl, gbOrr, gbOms, gbCss, gbFts, gbOrl, gbOrc]
def gbLocals : List MlS := [gbPr, gbPl, gbN0, gbCv, gbRs, gbNr, gbCs, gbT]

def gbBody : ProgHOL 64 := prologue gbLocals
  (.seq (.call (some (some (.local, gbPr), none)) fPb
      [vv gbOpp, vv gbOsl, vv gbNsl, vv gbNp, vv gbCss, vv gbFts, vv gbEl, vv gbOms])
  (.seq (.assign .local gbPl (.load .one (vv gbPr)))
  (.ite (.cmp .lower (vv gbPl) (.const (BitVec.ofNat 64 (2 ^ 56))))
  (.seq (.assign .local gbN0 (.op .add [vv gbNp, vv gbNsl]))
  (.seq (.assign .local gbNr (.load .one (vv gbOrl)))
  (.seq (.call (some (some (.local, gbCs), none)) fCrs
      [vv gbOrl, .const 0, vv gbNr, vv gbOrc, vv gbN0, vv gbPr, vv gbPl, vv gbNp, vv gbOms, vv gbFts, vv gbOsl])
  (.seq (.assign .local gbCv (.load .one (.op .add [vv gbCs, .const 8])))
  (.seq (.call (some (some (.local, gbRs), none)) fCfk
      [vv gbCs, vv gbOrl, vv gbOrc, vv gbCss, vv gbOms, vv gbPl, vv gbNp, vv gbOpp, vv gbOsl, vv gbPr, vv gbN0])
  (.seq (.assign .local gbT (.load .one (.op .add [vv gbRs, .const 8])))
    (.return (vv gbT))))))))
  hang)))

structure GBCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  pb : PBCodes C
  crs : CRSCodes mode C
  cfk : CFKCodes mode C
  self : C.code.lookup fGb = some (gbParams.map (fun p => (p, ShapeHOL.one)), gbBody, .one)

section
variable {σ : Type}

theorem gb_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ gbLocals → (ctxEnv C ++ gbParams.zip vals).get x = none :=
  Knot.params_none C gbLocals gbParams vals (by decide) (by decide)

theorem postGR_lower {m0 : TargetMajor} {C : Ctx} {St : EStore} (hx : Ext C.St St) {H : List (BitVec 64)} (hp : C.H <+: H) :
    ∀ a w s' (st : PState σ), PostGR m0 (ctxSt (ctxH C H) St) a w s' st → PostGR m0 C a w s' st := by
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
    (g0 : ClassGen) (m : TargetMajor) (hcls : g0.cls = [m]) (hmm : m.member = some 0)
    (ccs : List ClassCtor) (hctors : g0.ctors = [ccs])
    (opp osl oc : Nat) (hppl : g0.params.length < 2 ^ 56) (hpp : BlkAt C.H opp (g0.params.map Enc.idxW))
    (hsll : g0.slots.length < 2 ^ 56) (hsb : SlotBlk C C.H osl g0.slots)
    (hcl : ccs.length < 2 ^ 58) (hcs : PRep C C.H oc (fun H o cc => CCRep C H o cc) ccs)
    (hnf : ∀ x ∈ ccs, x.nF < 2 ^ 56) (hni : m.nIdx < 2 ^ 56) (hnP : g0.nP < 2 ^ 56)
    (hcb : ∀ sl ∈ g0.slots, ∀ c C' ihs, sl = .minor c C' ihs → c < 2 ^ 63)
    (oms : Nat) (hT : TMBlkR C C.H oms g0.cls) (ocss fts : Nat)
    (hcss : PRep C C.H ocss (fun H o xs => PRep C H o (fun H o cc => CCRep C H o cc) xs) g0.ctors)
    (hfts : BlkAt C.H fts (g0.formerTys.map Enc.idxW)) (orl : Nat) (hR : PtrsRep C C.H orl (RecRep C C.H) p.recs)
    (orc : Nat) (hRC : BlkAt C.H orc (([0] : List Nat).map (BitVec.ofNat 64))) (s : AState)
    (hcvd : ∀ (pre : List EIdx) s1 s' cv, g0.prefixBinders s = .ok (some pre, s1) →
      classRecTyOk mode C.fe { g0 with pre := pre } p.k rc rc.cvR 0 s1 = .ok (cv, s') →
      (denoteE s'.store cv.type).isSome = true) :
    SpecR (σ := σ) (Pre C s (gbParams.zip [cellA C opp, cellA C osl, BitVec.ofNat 64 g0.slots.length,
        BitVec.ofNat 64 g0.nP, cellA C oc, BitVec.ofNat 64 ccs.length, BitVec.ofNat 64 m.nIdx, Enc.idxW g0.elim,
        cellA C orr, cellA C oms, cellA C ocss, cellA C fts, cellA C orl, cellA C orc])) gbBody s (genRecB mode C.fe p g0 [rc.cvR] [0]) (PostGR m C) := by
  refine specR_prologue (postGR_locals m C) (gb_none C _) ?_
  unfold genRecB
  refine specR_callNIH (C := C) gbPr fPb pbParams
    [vv gbOpp, vv gbOsl, vv gbNsl, vv gbNp, vv gbCss, vv gbFts, vv gbEl, vv gbOms] (pbBody C)
    [cellA C opp, cellA C osl, BitVec.ofNat 64 g0.slots.length, BitVec.ofNat 64 g0.nP, cellA C ocss, cellA C fts,
      Enc.idxW g0.elim, cellA C oms] (by decide) rfl (by decide) hc.pb.self
    ⟨by simp +decide [sev, Env.get, gbParams, ctxEnv], by simp +decide [sev, Env.get, gbParams, ctxEnv], by simp +decide [sev, Env.get, gbParams, ctxEnv], by simp +decide [sev, Env.get, gbParams, ctxEnv], by simp +decide [sev, Env.get, gbParams, ctxEnv], by simp +decide [sev, Env.get, gbParams, ctxEnv], by simp +decide [sev, Env.get, gbParams, ctxEnv], by simp +decide [sev, Env.get, gbParams, ctxEnv], trivial⟩
    (fun o w s' st => g0.prefixBinders s = .ok (o, s') ∧ PostSL C o w s' st)
    (fun o w s' H' => g0.prefixBinders s = .ok (o, s') ∧ ∃ ds ob, o = some ds ∧ w = cellA C ob ∧ BlkAt H' ob (ds.map Enc.idxW))
    (fun o w s' st ⟨hpbr, ds, H', ob, h0, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨hpbr, ds, ob, h0, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu pbParams _ rfl hlk)
      (pb_spec ra C hok hc.pb g0 opp osl ocss fts oms hppl hpp hsll hsb hcss
        (fun xs hx => by rw [hctors] at hx; simp only [List.mem_singleton] at hx; subst hx; exact ⟨hcl, hnf⟩) hfts hT hnP hcb s)))
    (fun o w s1 H1 hp1 ⟨hpbr, pre, opr, ho, hw, hpr⟩ => ?_)
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
  have ehr : p.recs.map (·.cvR) = [rc.cvR] := by simp [hrecs]
  refine UD.specR_heapLoadI' (C := ctxH C H1) gbNr (vv gbOrl) orl _ (get_prefix hR.1 hp1') (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv]; rfl) ?_
  have hok1 := ctxOK_H hok H1
  refine specR_callNIH (C := ctxH C H1) gbCs fCrs crsParams
    [vv gbOrl, .const 0, vv gbNr, vv gbOrc, vv gbN0, vv gbPr, vv gbPl, vv gbNp, vv gbOms, vv gbFts, vv gbOsl] (crsBody C)
    [cellA C orl, BitVec.ofNat 64 0, BitVec.ofNat 64 p.recs.length, cellA C orc,
      BitVec.ofNat 64 (g0.nP + g0.slots.length), cellA C opr, BitVec.ofNat 64 pre.length, BitVec.ofNat 64 g0.nP,
      cellA C oms, cellA C fts, cellA C osl] (by decide) rfl (by decide) hc.crs.self
    ⟨by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv], rfl, by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv], by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv], trivial⟩
    (fun a w s' st => classRecTysOk mode C.fe { g0 with pre := pre } p.k p.recs [rc.cvR] [0] s1 = .ok (a, s') ∧
      PostCVGs (ctxH C H1) a w s' st)
    (fun cvs w s' H' => classRecTysOk mode C.fe { g0 with pre := pre } p.k p.recs [rc.cvR] [0] s1 = .ok (cvs, s') ∧
      ∃ o, w = cellA C o ∧ PRep C H' o (fun H o cv => CVRep C H o cv) cvs)
    (fun a w s' st ⟨hrun, H', o, hp', hw, hcv, hsr⟩ => ⟨H', hp', ⟨hrun, o, hw, hcv⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu crsParams _ rfl hlk)
      (by
        have h := crs_spec (σ := σ) mode ra (ctxH C H1) hok1 hs (by ctx_tr hc.crs) { g0 with pre := pre } opr hpl56 hpr
          oms fts osl (tmBlkR_mono hp1' hT) (blkAt_mono hfts hp1') (slotBlk_mono hp1' hsb) hnP hsll p.k p.recs orl
          (ptrsRep_mono hp1' (fun _ _ => recRep_mono hp1') hR) [0] orc (blkAt_mono hRC hp1') (by simp)
          (fun rc' hm => by rw [hrecs, List.mem_singleton] at hm; subst hm; omega)
          (fun rc' hm => by rw [hrecs, List.mem_singleton] at hm; subst hm; exact ⟨ks, hkl, hks⟩)
          (p.recs.length - 0) 0 H1 s1 rfl (Nat.zero_le _) (List.prefix_refl _)
        simp only [List.drop_zero] at h
        rw [ehr] at h
        exact h)))
    (fun cvs w s2 H2 hp2 ⟨hrunS, oq0, hw, hcvs⟩ => ?_)
  subst hw
  rw [hrecs] at hrunS
  obtain ⟨cvG, hrun, rfl⟩ := classRecTysOk_one hrunS
  have hcvsP := hcvs
  obtain ⟨os, hosl, hosb, hosr⟩ := hcvs
  obtain ⟨oq, rfl⟩ : ∃ oq, os = [oq] := by
    rcases os with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp at hosl; exact ⟨a, rfl⟩
  have hcvq : CVRep C H2 oq cvG := hosr 0 (by simp) (by simp)
  have hq1 : H2[oq0 + 1]? = some (cellA C oq) := by simpa using hosb.2 0 (by simp)
  refine UD.specR_heapLoadI' (C := ctxH C H2) gbCv _ (oq0 + 1) _ hq1 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C oq0) ?_
  have hp2' : H1 <+: H2 := hp2
  have hpC2 : C.H <+: H2 := hp1'.trans hp2'
  obtain ⟨hnm, hlps⟩ := classRecTyOk_shape hrun
  have hty := hcvd pre s1 s2 cvG hpbr hrun
  refine specR_atEntry fun t2 ht2 => ?_
  have hfl : Ext C.St s2.store := ht2.sr.floor
  refine specR_invRaise (C := ctxH C H2) (R' := PostGR m (ctxSt (ctxH C H2) s2.store)) ?_
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
  have hpC2' : C.H <+: H2 := hpC2
  refine specR_callNC (C := ctxSt (ctxH C H2) s2.store) (D := ctxLocals ++ gbLocals) gbRs fCfk cfkParams
    [vv gbCs, vv gbOrl, vv gbOrc, vv gbCss, vv gbOms, vv gbPl, vv gbNp, vv gbOpp, vv gbOsl, vv gbPr, vv gbN0] (cfkBody C)
    [cellA C oq0, cellA C orl, cellA C orc, cellA C ocss, cellA C oms, BitVec.ofNat 64 pre.length, BitVec.ofNat 64 g0.nP,
      cellA C opp, cellA C osl, cellA C opr, BitVec.ofNat 64 (g0.nP + g0.slots.length)] (by decide) rfl (by decide)
    hc.cfk.self
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv], by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, gbParams, ctxEnv], by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons], trivial⟩
    (fun r w s' st => genRules mode C.fe p { g0 with pre := pre } [0] [cvG] s2 = .ok (r, s') ∧
      PostGRK (ctxSt (ctxH C H2) s2.store) r w s' st)
    (fun r w s' C' => ∃ EH envM H o, C' = ctxNew (ctxSt (ctxH C H2) s2.store) r.1 EH envM H ∧
      (ctxSt (ctxH C H2) s2.store).EH <+: EH ∧ (ctxSt (ctxH C H2) s2.store).H <+: H ∧
      CtxOK (ctxNew (ctxSt (ctxH C H2) s2.store) r.1 EH envM H) ∧
      TblGate r.1 ∧ FlagsOK r.1 ∧ LitsPinned r.1 C.pins ∧ (∀ n, r.1.find? n = C.fe.find? n) ∧
      (∀ n, r.1.findTable? n = C.fe.findTable? n) ∧
      genRules mode C.fe p { g0 with pre := pre } [0] [cvG] s2 = .ok (r, s') ∧ w = cellA C o ∧
      PRep C H o (fun H o t => RRRep C H o t) r.2)
    (fun r w s' st ⟨hrun, EH, envM, H, o, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ =>
      ⟨_, ⟨EH, envM, H, o, rfl, h1, h2, h3, h5, h6, h7, h8, h9, hrun, h10, h11⟩, h4⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu cfkParams _ rfl hlk)
      (cfk_spec mode ra (ctxSt (ctxH C H2) s2.store) hokS hs hpl (by ctx_tr hc.cfk) hg hF hL p { g0 with pre := pre } [0]
        [cvG] hppl hsll hcb hpl56 hnP
        (fun cv hm => by simp only [List.mem_singleton] at hm; subst hm; rw [hlps]; exact hrl)
        (by simp) (fun xs hx => by
          simp only [hctors, List.mem_singleton] at hx; subst hx; exact ⟨hcl, hnf⟩)
        (fun cv hm => by simp only [List.mem_singleton] at hm; subst hm; exact hden)
        (fun cv hm => by
          simp only [List.mem_singleton] at hm; subst hm
          refine ⟨ks, by rw [hlps]; exact hkl, fun j hj => ?_⟩
          have hj' : j < rc.cvR.levelParams.length := by rw [← hlps]; exact hj
          have e := hks j hj'
          have hjj : cv.levelParams[j] = rc.cvR.levelParams[j] := by simp [hlps]
          rw [hjj]; exact hfl.lss.ls.ns _ _ e)
        oq0 orl orc ocss oms opp osl opr hcvsP (ptrsRep_mono hpC2' (fun _ _ => recRep_mono hpC2') hR)
        (blkAt_mono hRC hpC2') (pRep_mono hpC2' (fun _ _ h => pRep_mono hpC2' (fun _ _ => ccRep_mono hpC2') h) hcss)
        (tmBlkR_mono hpC2' hT) (blkAt_mono hpp hpC2') (slotBlk_mono hpC2' hsb) (blkAt_mono hpr hp2') s2)))
    (fun r w s3 C3 ⟨EH, envM, H, o, eC, h1, h2, h3, h4, h5, h6, h7, h8, hrun, hw, hout⟩ => ?_)
  subst eC hw
  obtain ⟨rhss, hr2⟩ := genRules_out_one (g := { g0 with pre := pre }) hcls hrun
  obtain ⟨ots, hotl, hotb, hotr⟩ := hout
  rw [hr2] at hotl hotr
  obtain ⟨ot, rfl⟩ : ∃ ot, ots = [ot] := by
    rcases ots with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> simp at hotl; exact ⟨a, rfl⟩
  have hot1 : H[o + 1]? = some (cellA C ot) := by simpa using hotb.2 0 (by simp)
  obtain ⟨orh, oc, om, k0, k1, k2, k3, -, -⟩ := hotr 0 (by simp) (by simp)
  refine UD.specR_heapLoadI' (C := ctxNew (ctxSt (ctxH C H2) s2.store) r.1 EH envM H) gbT _ (o + 1) _ hot1 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C o) ?_
  exact specR_returnI _ _ (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨EH, envM, H, ot, h1, h2, h3,
    sr_of_eq ht.sr rfl rfl rfl rfl, h4, h5, h6, h7, h8, cvG, rhss, orh, oc, hr2, rfl, k0, k2, k1, k3⟩)

end

end ConPanqueque.T.Ind
