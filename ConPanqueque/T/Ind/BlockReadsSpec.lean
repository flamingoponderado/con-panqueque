import ConPanqueque.T.Ind.BlockReadsAt

/-!
# `blockReadsAt`'s spec
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.Decl ConPanqueque.T.WC

/-- The code `blockReadsAt` runs. -/
structure BRCodes (C : Ctx) : Prop where
  bi : BICodes C
  bix : C.code.lookup fBlockIsRec = some (biParams.map (fun p => (p, ShapeHOL.one)), biBody C, .one)
  nm : C.code.lookup fNmFill = some (nmParams.map (fun p => (p, ShapeHOL.one)), nmBody, .one)
  mv : MVCodes C
  cm : C.code.lookup fMemberNZ = some (mvParams.map (fun p => (p, ShapeHOL.one)), mvBody, .one)
  zf : C.code.lookup fZfFill = some (zfParams.map (fun p => (p, ShapeHOL.one)), zfBody, .one)
  fx : FXCodes C
  cx : C.code.lookup fRecFire = some (fxParams.map (fun p => (p, ShapeHOL.one)), fxBody C, .one)
  ff : C.code.lookup fFfFill = some (ffParams.map (fun p => (p, ShapeHOL.one)), ffBody C, .one)
  cc : C.code.lookup fCtorCount = some (ccParams.map (fun p => (p, ShapeHOL.one)), ccBody, .one)
  cp : C.code.lookup fCpy = some (Decl.cpParams.map (fun p => (p, ShapeHOL.one)), cpyBody, .one)
  cn : C.code.lookup fCnFill = some (cnParams.map (fun p => (p, ShapeHOL.one)), cnBody, .one)
  cw : C.code.lookup fConstRec = some (cwParams.map (fun p => (p, ShapeHOL.one)), cwBody C, .one)
  fm : C.code.lookup fFormerRec = some (fmParams.map (fun p => (p, ShapeHOL.one)), fmBody C, .one)
  tf : C.code.lookup fTfFill = some (tfParams.map (fun p => (p, ShapeHOL.one)), tfBody, .one)
  cr : C.code.lookup fCtorRec = some (crParams.map (fun p => (p, ShapeHOL.one)), crBody C, .one)
  tc : C.code.lookup fTcFill = some (tcParams.map (fun p => (p, ShapeHOL.one)), tcBody, .one)
  tm : C.code.lookup fTmFill = some (tmParams.map (fun p => (p, ShapeHOL.one)), tmBody, .one)
  fw : C.code.lookup fFireEnv = some (fwParams.map (fun p => (p, ShapeHOL.one)), fwBody C, .one)
  rw : C.code.lookup fRuleFill = some (rwParams.map (fun p => (p, ShapeHOL.one)), rwBody C, .one)
  rq : C.code.lookup fRecRec = some (rqParams.map (fun p => (p, ShapeHOL.one)), rqBody C, .one)
  tq : C.code.lookup fTqFill = some (tqParams.map (fun p => (p, ShapeHOL.one)), tqBody, .one)
  tx : C.code.lookup fTxFill = some (txParams.map (fun p => (p, ShapeHOL.one)), txBody, .one)
  rd : RDCodes C
  ro : ROCodes C
  hcr : C.code.lookup fRuleReads = some (rdParams.map (fun p => (p, ShapeHOL.one)), rdBody C, .one)
  hcl : C.code.lookup fRulesRead = some (ulParams.map (fun p => (p, ShapeHOL.one)), ulBody, .one)
  hck : C.code.lookup fRecReads = some (rkParams.map (fun p => (p, ShapeHOL.one)), rkBody, .one)
  hcs : C.code.lookup fRecsRead = some (ksParams.map (fun p => (p, ShapeHOL.one)), ksBody, .one)

theorem crt_pop_feq (cs : List IConstantInfo) (fe : IFEnv) :
    ConRon.Bridge.Inductives.GR.FEq (((consBlockRecsTemp cs fe []).2.foldr
      (fun (x : NIdx × Option IConstantInfo) acc => acc.popTemp x.1 x.2) (consBlockRecsTemp cs fe []).1).setFlags
      fe.natLit fe.strLit) fe := by
  obtain ⟨news, hn, hf⟩ := ConRon.Bridge.Inductives.BT.consBlockRecsTemp_pop cs fe []
  simp only [List.nil_append] at hn
  rw [hn]
  exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2⟩

theorem blockDen_of (p : BlockShape) (isRec : Bool) (nzs : List Bool) (fs : List IRecRuleFire) (st : EStore)
    (hcap : ∀ ms ∈ p.members, p.nP + ms.nIdx < 2 ^ 63)
    (hCV : (∀ ms ∈ p.members, CVDen ms.declared st ∧ (CVDen ms.cvT st) ∧ ∀ c ∈ ms.ctors, CVDen c.1 st) ∧
      ∀ rc ∈ p.recs, CVDen rc.cvR st) :
    BlockDen (formersOf p isRec p.members nzs ++ membersCtors p.nP p.members ++ recsOf p.recs fs) st := by
  intro ci hci
  simp only [List.mem_append] at hci
  rcases hci with (h | h) | h
  · simp only [formersOf, List.mem_map] at h
    obtain ⟨⟨ms, nz⟩, hm, rfl⟩ := h
    have hms := List.of_mem_zip hm |>.1
    refine ⟨(hCV.1 ms hms).1, (fun _ _ _ h => by cases h), fun cv caps h => ?_⟩
    cases h
    simp only [capsOf]; exact hcap ms hms
  · simp only [membersCtors, List.mem_flatMap, ctorsOf, List.mem_map] at h
    obtain ⟨ms, hms, c, hc, rfl⟩ := h
    exact ⟨(hCV.1 ms hms).2.2 c hc, (fun _ _ _ h => by cases h), (fun _ _ h => by cases h)⟩
  · simp only [recsOf, List.mem_map] at h
    obtain ⟨⟨rc, f⟩, hm, rfl⟩ := h
    have hrc := List.of_mem_zip hm |>.1
    exact ⟨hCV.2 rc hrc, (fun _ _ _ h => by cases h), (fun _ _ h => by cases h)⟩

section
variable {σ : Type}

/-- `blockReadsAt`'s answer, the environment it gives back answering as the input, the heaps grown. -/
def PostBR (C : Ctx) (r : Bool × IFEnv) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  w = boolW r.1 ∧ ConRon.Bridge.Inductives.GR.FEq r.2 C.fe ∧ r.2.natLit = C.fe.natLit ∧ r.2.strLit = C.fe.strLit ∧
    ∃ H' EH', C.H <+: H' ∧ C.EH <+: EH' ∧ SR (ctxE (ctxH C H') EH') s' st

theorem postBR_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostBR C a w s' st → PostBR C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2, h3, h4, H', EH', h5, h6, h7⟩ => ⟨h1, h2, h3, h4, H', EH', h5, h6, sr_of_eq h7 rfl rfl rfl rfl⟩

theorem br_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ brLocals → (ctxEnv C ++ brParams.zip vals).get x = none :=
  Knot.params_none C brLocals brParams vals (by decide) (by decide)

set_option maxHeartbeats 8000000 in
/-- **`blockReadsAt`**. -/
theorem br_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : Front.FrontOK C)
    (hc : BRCodes C) (hAn : denoteN C.St.ns anonH = some .anonymous)
    (hpa : ∀ sa : AState, sa.pins = C.pins → Ext C.St sa.store → PinsOK sa)
    (p : BlockShape) (os : Nat) (hsh : ShapeRep C C.H os p)
    (hni : ∀ ms ∈ p.members, ms.nIdx < 2 ^ 63) (hcap : ∀ ms ∈ p.members, p.nP + ms.nIdx < 2 ^ 63)
    (hlD : ∀ ms ∈ p.members, ms.declared.levelParams.length < 2 ^ 60)
    (hlC : ∀ ms ∈ p.members, ∀ c ∈ ms.ctors, c.1.levelParams.length < 2 ^ 60)
    (hlR : ∀ rc ∈ p.recs, rc.cvR.levelParams.length < 2 ^ 60)
    (hnc : (p.members.map (·.ctors.length)).sum < 2 ^ 58)
    (hCV : (∀ ms ∈ p.members, CVDen ms.declared C.St ∧ (CVDen ms.cvT C.St) ∧ ∀ c ∈ ms.ctors, CVDen c.1 C.St) ∧
      ∀ rc ∈ p.recs, CVDen rc.cvR C.St)
    (hRD : ∀ sa sb fs, StateOK sa → PinsOK sa → Ext C.St sa.store → p.recs.mapM (recFire p) sa = .ok (fs, sb) →
      ∀ ci ∈ recsOf p.recs fs, ∀ cv mI rP isK rules, ci = .recInfo cv mI rP isK rules → ∀ rl ∈ rules, RuleDen rl sb.store)
    (s : AState) :
    SpecR (σ := σ) (Pre C s (brParams.zip [cellA C os])) (brBody C) s (blockReadsAt C.fe p) (PostBR C) := by
  refine specR_prologue (postBR_locals _) (br_none _ _) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : C.H.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  obtain ⟨⟨om, hom, hpm⟩, ⟨orr, hor, hpr⟩, ⟨hnp, hnpb⟩, -, -, -, -⟩ := hsh
  have hK : p.members.length + 2 < 2 ^ 61 := by
    have h0 := (List.getElem?_eq_some_iff.mp hpm.1).1
    rcases Nat.lt_or_ge 0 p.members.length with h | h
    · obtain ⟨oc, h1, -⟩ := hpm.2 (p.members.length - 1) (by omega)
      have := (List.getElem?_eq_some_iff.mp h1).1; omega
    · omega
  have hR : p.recs.length + 2 < 2 ^ 61 := by
    have h0 := (List.getElem?_eq_some_iff.mp hpr.1).1
    rcases Nat.lt_or_ge 0 p.recs.length with h | h
    · obtain ⟨oc, h1, -⟩ := hpr.2 (p.recs.length - 1) (by omega)
      have := (List.getElem?_eq_some_iff.mp h1).1; omega
    · omega
  refine UD.specR_heapLoadI' (C := C) brOm _ os _ hom (by decide) (by simp +decide [Env.get, brParams, ctxEnv]) ?_
  refine UD.specR_heapLoadI' (C := C) brK _ om _ hpm.1 (by decide) (by simp +decide [Env.get] <;> rfl) ?_
  refine UD.specR_heapLoadI' (C := C) brOr _ (os + 1) _ hor (by decide)
    (by simp +decide [sev, Env.get, brParams, ctxEnv]; exact cellA_add8 C os) ?_
  refine UD.specR_heapLoadI' (C := C) brNr _ orr _ hpr.1 (by decide) (by simp +decide [Env.get] <;> rfl) ?_
  refine UD.specR_heapLoadI' (C := C) brNp _ (os + 2) _ hnp (by decide)
    (by simp +decide [sev, Env.get, brParams, ctxEnv]; exact cellA_add_ofNat C os 2) ?_
  refine specR_guardI brK p.members.length 58 (by decide) (by simp +decide [Env.get]) (by omega) (fun hK58 => ?_)
  refine specR_guardI brNr p.recs.length 58 (by decide) (by simp +decide [Env.get]) (by omega) (fun hR58 => ?_)
  rw [blockReadsAt_eq]
  -- recursiveness
  refine specR_callNIH (C := C) brIr fBlockIsRec biParams [vv brOm, vv brK] (biBody C)
    [cellA C om, BitVec.ofNat 64 p.members.length] (by decide) rfl (by decide) hc.bix
    ⟨by simp +decide [sev, Env.get], by simp +decide [sev, Env.get], trivial⟩
    (PostB (ctxH C C.H)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu biParams _ rfl hlk)
      (bi_spec C hok hc.bi hc.nm p om hpm C.H (List.prefix_refl _) s))
    (fun isRec w s1 H1 hp1 hw => ?_)
  subst hw
  have hp1' : C.H <+: H1 := hp1
  -- the never-zero bits
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN1 => ?_)
  have hHN1' : H1.length ≤ C.HN := hHN1
  refine specR_allocI (C := ctxH C H1) brNz _ (p.members.length + 1) (by omega) (by decide) (fun v => ?_)
    (fun H2 ws hp2 hws hroom => ?_)
  · simp +decide [sev, Env.get]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hp2' : H1 <+: H2 := hp2
  have hq0 : H2.length < (ctxH (ctxH C H1) (H2 ++ ws)).H.length := by show H2.length < (H2 ++ ws).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv brNz) (vv brK) H2.length hq0 (BitVec.ofNat 64 p.members.length)
    (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get]) ?_
  change SpecR (Inv (ctxH C ((H2 ++ ws).set H2.length (BitVec.ofNat 64 p.members.length))) _ _ _ _) _ _ _ _
  generalize hB : (H2 ++ ws).set H2.length (BitVec.ofNat 64 p.members.length) = B
  have hBlen : B.length = H2.length + (p.members.length + 1) := by rw [← hB]; simp [hws]
  have hpB : H2 <+: B := by
    refine prefix_of_get? (by omega) (fun j hj => ?_)
    rw [← hB, List.getElem?_set_ne (by omega), List.getElem?_append_left hj]
  let Hc := B.take (H2.length + 1)
  have hpc : H2 <+: Hc := by
    refine prefix_of_get? (by simp [Hc]; omega) (fun j hj => ?_)
    simp only [Hc]; rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj]
    exact get_prefix (List.getElem?_eq_getElem hj) hpB
  have hHc0 : Hc[H2.length]? = some (BitVec.ofNat 64 p.members.length) := by
    simp only [Hc]; rw [List.getElem?_take_of_lt (by omega), ← hB, List.getElem?_set_self (by simp; omega)]
  refine specR_congr (m' := ((p.members.drop 0).mapM fun ms => formerZ ms.declared >>= fun z => pure z.isNever) >>=
    fun nzs => _) (by rw [List.drop_zero]) ?_
  refine specR_callNIG (C := ctxH C B) brX2 fZfFill zfParams [vv brOm, vv brNz, .const 0, vv brK] zfBody
    [cellA C om, cellA C H2.length, BitVec.ofNat 64 0, BitVec.ofNat 64 p.members.length] (by decide) rfl (by decide) hc.zf
    ⟨by simp +decide [sev, Env.get], by simp +decide [sev, Env.get] <;> rfl, rfl, by simp +decide [sev, Env.get], trivial⟩
    (fun nzs w s' st => ((p.members.drop 0).mapM fun ms => formerZ ms.declared >>= fun z => pure z.isNever) s1 =
      .ok (nzs, s') ∧ PostZF C Hc H2.length 0 nzs w s' st)
    (fun nzs w s' H' => ((p.members.drop 0).mapM fun ms => formerZ ms.declared >>= fun z => pure z.isNever) s1 =
      .ok (nzs, s') ∧ Hc <+: H' ∧ ∀ j (hj : j < nzs.length), H'[H2.length + 1 + 0 + j]? = some (boolW nzs[j]))
    (fun nzs w s' st ⟨hr, H', hp', hs', hc'⟩ => ⟨H', ⟨hr, hp', hc'⟩, hs'⟩)
    (fun u hu _ hlk => specR_run (fun w' hw' => by
      subst hw'
      exact zf_spec C hok hc.mv hc.cm hc.zf p.members om H2.length C.H hpm _ 0 B Hc s1 rfl (Nat.zero_le _)
        ((hp1'.trans hp2').trans hpc) (by simp [Hc]) (List.take_prefix _ _) (by omega) _
        (pre_of_lookups hu zfParams _ rfl hlk)))
    (fun nzs w s2 H3 ⟨hr2, hp3, hnz3⟩ => ?_)
  have hnzl : nzs.length = p.members.length := by
    have := mapM_len _ _ _ _ _ hr2; simpa using this
  have hpH3 : C.H <+: H3 := ((hp1'.trans hp2').trans hpc).trans hp3
  -- the firing modes, twice
  refine specR_congr (m' := ((p.recs.drop 0).mapM (recFire p)) >>= fun fs => _) (by rw [List.drop_zero]) ?_
  refine specR_callNIH (C := ctxH C H3) brF1 fFfFill ffParams [vv brOr, .const 0, vv brNr, vv brK] (ffBody C)
    [cellA C orr, BitVec.ofNat 64 0, BitVec.ofNat 64 p.recs.length, BitVec.ofNat 64 p.members.length] (by decide) rfl
    (by decide) hc.ff
    ⟨by simp +decide [sev, Env.get], rfl, by simp +decide [sev, Env.get], by simp +decide [sev, Env.get], trivial⟩
    (fun fs w s' st => ((p.recs.drop 0).mapM (recFire p)) s2 = .ok (fs, s') ∧ PostFF (ctxH C H3) p.recs.length 0 fs w s' st)
    (fun fs w s' H' => ((p.recs.drop 0).mapM (recFire p)) s2 = .ok (fs, s') ∧ ∃ Hf od, H3 <+: Hf ∧ Hf <+: H' ∧
      Hf.length ≤ od ∧ w = cellA C od ∧ H'[od]? = some (BitVec.ofNat 64 p.recs.length) ∧ od + 1 + p.recs.length ≤ H'.length ∧
      ∀ j (hj : j < fs.length), ∃ o, H'[od + 1 + 0 + j]? = some (cellA C o) ∧ FireE C.HB Hf o fs[j])
    (fun fs w s' st ⟨hr, H', Hf, od, h1, h2, h3, h4, h5, h6, h7, h8⟩ => ⟨H', h1.trans h2, ⟨hr, Hf, od, h1, h2, h3, h4, h5, h6, h8⟩, h7⟩)
    (fun u hu _ hlk => specR_run (fun w' hw' => by
      subst hw'
      exact ff_spec ra C hok hc.fx hc.cx hc.ff p (by simp [BlockShape.k]; omega) p.recs orr hpr _ 0 H3 s2 rfl (Nat.zero_le _)
        hpH3 _ (pre_of_lookups hu ffParams _ rfl hlk)))
    (fun fs1 w4 s3 H4 hp4 ⟨hr3, Hf1, od1, hHf1, hf1H, hf1l, hw4, hod1, hodl1, hfs1⟩ => ?_)
  subst hw4
  have hfs1l : fs1.length = p.recs.length := by have := mapM_len _ _ _ _ _ hr3; simpa using this
  have hp4' : H3 <+: H4 := hp4
  refine specR_atEntry fun t3 ht3 => ?_
  have hst3 : StateOK s3 := ⟨ht3.sr.twf⟩
  have hx3 : Ext C.St s3.store := ht3.sr.floor
  have hpo3 : PinsOK s3 := hpa s3 ht3.sr.pins hx3
  refine specR_congr (m' := ((p.recs.drop 0).mapM (recFire p)) >>= fun fs => _) (by rw [List.drop_zero]) ?_
  refine specR_callNIH (C := ctxH C H4) brF2 fFfFill ffParams [vv brOr, .const 0, vv brNr, vv brK] (ffBody C)
    [cellA C orr, BitVec.ofNat 64 0, BitVec.ofNat 64 p.recs.length, BitVec.ofNat 64 p.members.length] (by decide) rfl
    (by decide) hc.ff
    ⟨by simp +decide [sev, Env.get], rfl, by simp +decide [sev, Env.get], by simp +decide [sev, Env.get], trivial⟩
    (fun fs w s' st => ((p.recs.drop 0).mapM (recFire p)) s3 = .ok (fs, s') ∧ PostFF (ctxH C H4) p.recs.length 0 fs w s' st)
    (fun fs w s' H' => ((p.recs.drop 0).mapM (recFire p)) s3 = .ok (fs, s') ∧ ∃ Hf od, H4 <+: Hf ∧ Hf <+: H' ∧
      Hf.length ≤ od ∧ w = cellA C od ∧ H'[od]? = some (BitVec.ofNat 64 p.recs.length) ∧ od + 1 + p.recs.length ≤ H'.length ∧
      ∀ j (hj : j < fs.length), ∃ o, H'[od + 1 + 0 + j]? = some (cellA C o) ∧ FireE C.HB Hf o fs[j])
    (fun fs w s' st ⟨hr, H', Hf, od, h1, h2, h3, h4, h5, h6, h7, h8⟩ => ⟨H', h1.trans h2, ⟨hr, Hf, od, h1, h2, h3, h4, h5, h6, h8⟩, h7⟩)
    (fun u hu _ hlk => specR_run (fun w' hw' => by
      subst hw'
      exact ff_spec ra C hok hc.fx hc.cx hc.ff p (by simp [BlockShape.k]; omega) p.recs orr hpr _ 0 H4 s3 rfl (Nat.zero_le _)
        (hpH3.trans hp4') _ (pre_of_lookups hu ffParams _ rfl hlk)))
    (fun fs2 w5 s4 H5 hp5 ⟨hr4, Hf2, od2, hHf2, hf2H, hf2l, hw5, hod2, hodl2, hfs2⟩ => ?_)
  subst hw5
  have hfs2l : fs2.length = p.recs.length := by have := mapM_len _ _ _ _ _ hr4; simpa using this
  have hp5' : H4 <+: H5 := hp5
  have hpH5 : C.H <+: H5 := (hpH3.trans hp4').trans hp5'
  -- the constructor count
  refine specR_pureBind () ?_
  refine specR_callNIH (C := ctxH C H5) brNc fCtorCount ccParams [vv brOm, .const 0, vv brK, .const 0] ccBody
    [cellA C om, BitVec.ofNat 64 0, BitVec.ofNat 64 p.members.length, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.cc
    ⟨by simp +decide [sev, Env.get], rfl, by simp +decide [sev, Env.get], rfl, trivial⟩
    (fun _ w s' st => s' = s4 ∧ w = BitVec.ofNat 64 (0 + ((p.members.drop 0).map (·.ctors.length)).sum) ∧
      ∃ H', H5 <+: H' ∧ SR (ctxH C H') s4 st)
    (fun _ w s' H' => s' = s4 ∧ w = BitVec.ofNat 64 (0 + ((p.members.drop 0).map (·.ctors.length)).sum))
    (fun _ w s' st ⟨h1, h2, H', hp', hs⟩ => ⟨H', hp', ⟨h1, h2⟩, by subst h1; exact hs⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ccParams _ rfl hlk)
      (cc_spec C hok hc.cc p.members om hpm _ 0 0 H5 s4 rfl (Nat.zero_le _) hpH5 (by simp; omega)))
    (fun _ w6 s5 H6 hp6 ⟨hs5, hw6⟩ => ?_)
  subst hw6; subst s5
  have hp6' : H5 <+: H6 := hp6
  have hpH6 : C.H <+: H6 := hpH5.trans hp6'
  simp only [List.drop_zero, Nat.zero_add] at *
  set nC := (p.members.map (·.ctors.length)).sum with hnC
  refine specR_guardI brNc nC 58 (by decide) (by simp +decide [Env.get]) (by omega) (fun hc58 => ?_)
  -- the members' names, in the environment heap
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN6 => ?_)
  have hHN6' : H6.length ≤ C.HN := hHN6
  refine specR_allocI (C := ctxH C H6) brNb _ (p.members.length + 1) (by omega) (by decide) (fun v => ?_)
    (fun H7 ws7 hp7 hws7 hroom7 => ?_)
  · simp +decide [sev, Env.get]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hp7' : H6 <+: H7 := hp7
  have hq7 : H7.length < (ctxH (ctxH C H6) (H7 ++ ws7)).H.length := by show H7.length < (H7 ++ ws7).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv brNb) (vv brK) H7.length hq7 (BitVec.ofNat 64 p.members.length)
    (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get]) ?_
  change SpecR (Inv (ctxH C ((H7 ++ ws7).set H7.length (BitVec.ofNat 64 p.members.length))) _ _ _ _) _ _ _ _
  generalize hB7 : (H7 ++ ws7).set H7.length (BitVec.ofNat 64 p.members.length) = B7
  have hB7len : B7.length = H7.length + (p.members.length + 1) := by rw [← hB7]; simp [hws7]
  have hpB7 : H7 <+: B7 := by
    refine prefix_of_get? (by omega) (fun j hj => ?_)
    rw [← hB7, List.getElem?_set_ne (by omega), List.getElem?_append_left hj]
  let Hc7 := B7.take (H7.length + 1)
  have hpc7 : H7 <+: Hc7 := by
    refine prefix_of_get? (by simp [Hc7]; omega) (fun j hj => ?_)
    simp only [Hc7]; rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj]
    exact get_prefix (List.getElem?_eq_getElem hj) hpB7
  have hHc70 : Hc7[H7.length]? = some (BitVec.ofNat 64 p.members.length) := by
    simp only [Hc7]; rw [List.getElem?_take_of_lt (by omega), ← hB7, List.getElem?_set_self (by simp; omega)]
  refine specR_pureBind () ?_
  refine specR_callNIG (C := ctxH C B7) brX1 fNmFill nmParams [vv brOm, vv brNb, .const 0, vv brK] nmBody
    [cellA C om, cellA C H7.length, BitVec.ofNat 64 0, BitVec.ofNat 64 p.members.length] (by decide) rfl (by decide) hc.nm
    ⟨by simp +decide [sev, Env.get], by simp +decide [sev, Env.get] <;> rfl, rfl, by simp +decide [sev, Env.get], trivial⟩
    (fun a w s' st => (pure () : AM Unit) s4 = .ok (a, s') ∧ PostNM C Hc7 H7.length p.members 0 a w s' st)
    (fun a w s' H' => s' = s4 ∧ Hc7 <+: H' ∧
      ∀ j (hj : j < p.members.length), 0 ≤ j → H'[H7.length + 1 + j]? = some (Enc.idxW p.members[j].cvT.name))
    (fun a w s' st ⟨hr, H', hp', hs', hc'⟩ => ⟨H', ⟨pure_run_unit _ _ _ hr, hp', hc'⟩, hs'⟩)
    (fun u hu _ hlk => specR_run (fun w hw => by
      subst hw
      exact nm_spec C hok hc.nm p.members om H7.length C.H hpm _ 0 B7 Hc7 s4 rfl (Nat.zero_le _)
        (hpH6.trans (hp7'.trans hpc7)) (by simp [Hc7]) (List.take_prefix _ _) (by omega) _
        (pre_of_lookups hu nmParams _ rfl hlk)))
    (fun _ w s' H8 ⟨hs', hp8, hc8⟩ => ?_)
  subst s'
  have hpH8 : C.H <+: H8 := (hpH6.trans (hp7'.trans hpc7)).trans hp8
  let nms : List (BitVec 64) := p.memberNames.map Enc.idxW
  have hnmsl : nms.length = p.members.length := by simp [nms, BlockShape.memberNames]
  have hbn : BlkAt H8 H7.length nms := by
    refine ⟨by rw [hnmsl]; exact get_prefix hHc70 hp8, fun j hj => ?_⟩
    have := hc8 j (by omega) (Nat.zero_le _)
    simpa [nms, BlockShape.memberNames] using this
  refine specR_envBlkI (ctxOK_H hok H8) hc.cp brAll brNb brK brR1 H7.length nms hbn (by omega) (by decide) (by decide)
    (by decide) (by decide) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, hnmsl])
    (fun EH1 w9 hpe1 hebn => ?_)
  have hall : ENList C.EB EH1 (ecell C C.EH.length) p.memberNames := ⟨C.EH.length, rfl, hebn⟩
  -- the table
  set nT := p.members.length + nC + p.recs.length with hnT
  refine specR_assignI brN _ (BitVec.ofNat 64 nT) (by decide)
    (by
      simp +decide [sev, Env.get]
      rw [BitVec.ofNat_add_ofNat, BitVec.ofNat_add_ofNat]) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN8 => ?_)
  have hHN8' : H8.length ≤ C.HN := hHN8
  have hl8 := hp8.length_le
  refine specR_allocI (C := ctxE (ctxH C H8) EH1) brT _ (2 * nT + 1) (by omega) (by decide) (fun v => ?_)
    (fun H9 ws9 hp9 hws9 hroom9 => ?_)
  · simp +decide [sev, Env.get]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hp9' : H8 <+: H9 := hp9
  change SpecR (Inv (ctxE (ctxH C (H9 ++ ws9)) EH1) _ _ _ _) _ _ _ _
  have hq9 : H9.length < (ctxE (ctxH C (H9 ++ ws9)) EH1).H.length := by show H9.length < (H9 ++ ws9).length; simp; omega
  refine specR_heapStoreI (ctxOK_E (ctxOK_H hok (H9 ++ ws9)) hpe1) (vv brT) (vv brN) H9.length hq9 (BitVec.ofNat 64 nT)
    (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get]) ?_
  change SpecR (Inv (ctxE (ctxH C ((H9 ++ ws9).set H9.length (BitVec.ofNat 64 nT))) EH1) _ _ _ _) _ _ _ _
  generalize hB9 : (H9 ++ ws9).set H9.length (BitVec.ofNat 64 nT) = B9
  have hB9len : B9.length = H9.length + (2 * nT + 1) := by rw [← hB9]; simp [hws9]
  have hpB9 : H9 <+: B9 := by
    refine prefix_of_get? (by omega) (fun j hj => ?_)
    rw [← hB9, List.getElem?_set_ne (by omega), List.getElem?_append_left hj]
  let Hc9 := B9.take (H9.length + 1)
  have hpc9 : H9 <+: Hc9 := by
    refine prefix_of_get? (by simp [Hc9]; omega) (fun j hj => ?_)
    simp only [Hc9]; rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj]
    exact get_prefix (List.getElem?_eq_getElem hj) hpB9
  have hHc90 : Hc9[H9.length]? = some (BitVec.ofNat 64 nT) := by
    simp only [Hc9]; rw [List.getElem?_take_of_lt (by omega), ← hB9, List.getElem?_set_self (by simp; omega)]
  have hHc9l : Hc9.length = H9.length + 1 := by simp [Hc9]; omega
  have hp39 : H3 <+: Hc9 := (((hp4'.trans hp5').trans hp6').trans (hp7'.trans (hpc7.trans hp8))).trans (hp9'.trans hpc9)
  have hpH9 : C.H <+: Hc9 := hpH3.trans hp39
  -- the formers' entries
  have hok1 : CtxOK (ctxE C EH1) := ctxOK_E hok hpe1
  refine specR_pureBind () ?_
  refine specR_callNC (C := ctxE (ctxH C B9) EH1) (D := ctxLocals ++ brLocals) brX3 fTfFill tfParams
    [vv brOm, vv brNz, vv brT, .const 0, .const 0, vv brK, vv brIr, vv brAll, vv brNp] tfBody
    [cellA C om, cellA C H2.length, cellA C H9.length, BitVec.ofNat 64 0, BitVec.ofNat 64 0,
      BitVec.ofNat 64 p.members.length, boolW isRec, ecell C C.EH.length, BitVec.ofNat 64 p.nP]
    (by decide) rfl (by decide) hc.tf ?_
    (fun a w s' st => (pure () : AM Unit) s4 = .ok (a, s') ∧
      PostTF (ctxE C EH1) Hc9 EH1 B9.length H9.length 0 (formersOf p isRec p.members nzs) 0 a w s' st)
    (fun a w s' C' => s' = s4 ∧ ∃ H' EH', C' = ctxE (ctxH C H') EH' ∧ Hc9 <+: H' ∧ EH1 <+: EH' ∧ B9.length ≤ H'.length ∧
      ∀ j (hj : j < (formersOf p isRec p.members nzs).length), 0 ≤ j → ∃ o,
        H'[H9.length + 1 + 2 * (0 + j)]? = some (Enc.idxW (formersOf p isRec p.members nzs)[j].name) ∧
        H'[H9.length + 2 + 2 * (0 + j)]? = some (ecell C o) ∧ CIE C.EB EH' o (formersOf p isRec p.members nzs)[j])
    (fun a w s' st ⟨hr, H', EH', hp', hpe', hl', hs', hc'⟩ =>
      ⟨_, ⟨pure_run_unit _ _ _ hr, H', EH', rfl, hp', hpe', hl', hc'⟩, hs'⟩)
    (fun u hu _ hlk => specR_run (fun w' hw' => by
      subst hw'
      exact (tf_spec (ctxE C EH1) hok1 hc.cp hc.cn hc.cw hc.fm hc.tf p isRec nzs hnzl om H2.length H9.length 0 Hc9
        (ptrsRep_mono hpH9 (fun oi a h => memberRep_mono hpH9 h) hpm)
        (fun j hj => get_prefix (by simpa using hnz3 j hj) hp39) (ecell C C.EH.length) hall hnpb hni hlD
        _ 0 B9 Hc9 EH1 s4 rfl (Nat.zero_le _) (List.prefix_refl _) (by omega) (List.take_prefix _ _) (by omega)
        (List.prefix_refl _)) _ (pre_of_lookups hu tfParams _ rfl hlk)))
    (fun _ w10 s6 C10 ⟨hs6, H10, EH2, eC10, hp10, hpe2, hl10, hfm⟩ => ?_)
  · exact ⟨by simp +decide [sev, Env.get], by simp +decide [sev, Env.get] <;> rfl, by simp +decide [sev, Env.get] <;> rfl,
      rfl, rfl, by simp +decide [sev, Env.get], by simp +decide [sev, Env.get], by simp +decide [sev, Env.get] <;> rfl,
      by simp +decide [sev, Env.get], trivial⟩
  subst eC10; subst s6
  have hfml : (formersOf p isRec p.members nzs).length = p.members.length := by simp [formersOf, hnzl]
  have hmcl : (membersCtors p.nP p.members).length = nC := by rw [membersCtors_length]
  have hrcl : (recsOf p.recs fs1).length = p.recs.length := by simp [recsOf, hfs1l]
  -- the constructors' entries
  let Hc10 := H10.take (H9.length + 1 + 2 * p.members.length)
  have hpc10 : Hc10 <+: H10 := List.take_prefix _ _
  have hHc910 : Hc9 <+: Hc10 := by
    refine prefix_of_get? (by simp [Hc10]; omega) (fun j hj => ?_)
    simp only [Hc10]; rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj]
    exact get_prefix (List.getElem?_eq_getElem hj) hp10
  refine specR_pureBind () ?_
  refine specR_callNC (C := ctxE (ctxH C H10) EH2) (D := ctxLocals ++ brLocals) brX4 fTmFill tmParams
    [vv brOm, vv brT, vv brK, .const 0, vv brK, vv brNp] tmBody
    [cellA C om, cellA C H9.length, BitVec.ofNat 64 p.members.length, BitVec.ofNat 64 0,
      BitVec.ofNat 64 p.members.length, BitVec.ofNat 64 p.nP]
    (by decide) rfl (by decide) hc.tm ?_
    (fun a w s' st => (pure () : AM Unit) s4 = .ok (a, s') ∧
      PostTF C Hc10 EH2 H10.length H9.length p.members.length (membersCtors p.nP (p.members.drop 0)) 0 a w s' st)
    (fun a w s' C' => s' = s4 ∧ ∃ H' EH', C' = ctxE (ctxH C H') EH' ∧ Hc10 <+: H' ∧ EH2 <+: EH' ∧ H10.length ≤ H'.length ∧
      ∀ j (hj : j < (membersCtors p.nP p.members).length), 0 ≤ j → ∃ o,
        H'[H9.length + 1 + 2 * (p.members.length + j)]? = some (Enc.idxW (membersCtors p.nP p.members)[j].name) ∧
        H'[H9.length + 2 + 2 * (p.members.length + j)]? = some (ecell C o) ∧
        CIE C.EB EH' o (membersCtors p.nP p.members)[j])
    (fun a w s' st ⟨hr, H', EH', hp', hpe', hl', hs', hc'⟩ =>
      ⟨_, ⟨pure_run_unit _ _ _ hr, H', EH', rfl, hp', hpe', hl', by simpa using hc'⟩, hs'⟩)
    (fun u hu _ hlk => specR_run (fun w' hw' => by
      subst hw'
      exact (tm_spec C hok hc.cp hc.cr hc.tc hc.tm p.nP hnpb p.members om H9.length Hc9
        (ptrsRep_mono hpH9 (fun oi a h => memberRep_mono hpH9 h) hpm) hlC _ 0 p.members.length H10 Hc10 EH2 s4 rfl
        (Nat.zero_le _) hHc910 (by simp [Hc10]) hpc10 (by simp only [List.drop_zero]; rw [hmcl]; omega)
        (hpe1.trans hpe2)) _ (pre_of_lookups hu tmParams _ rfl hlk)))
    (fun _ w11 s7 C11 ⟨hs7, H11, EH3, eC11, hp11, hpe3, hl11, hct⟩ => ?_)
  · exact ⟨by simp +decide [sev, Env.get], by simp +decide [sev, Env.get] <;> rfl, by simp +decide [sev, Env.get],
      rfl, by simp +decide [sev, Env.get], by simp +decide [sev, Env.get], trivial⟩
  subst eC11; subst s7
  -- the recursors' entries (the first firing modes)
  let Hc11 := H11.take (H9.length + 1 + 2 * (p.members.length + nC))
  have hpc11 : Hc11 <+: H11 := List.take_prefix _ _
  have hHc1011 : Hc10 <+: Hc11 := by
    refine prefix_of_get? (by simp [Hc11, Hc10]; omega) (fun j hj => ?_)
    simp only [Hc11]; rw [List.getElem?_take_of_lt (by simp [Hc10] at hj; omega), List.getElem?_eq_getElem hj]
    exact get_prefix (List.getElem?_eq_getElem hj) hp11
  have hp49 : H4 <+: Hc9 := ((hp5'.trans hp6').trans (hp7'.trans (hpc7.trans hp8))).trans (hp9'.trans hpc9)
  have hfsat1 : FiresAt C Hc9 Hf1 od1 fs1 := fun j hj => by
    obtain ⟨o, h1', h2'⟩ := hfs1 j hj
    exact ⟨o, get_prefix (by simpa using h1') hp49, h2'⟩
  refine specR_pureBind () ?_
  refine specR_callNC (C := ctxE (ctxH C H11) EH3) (D := ctxLocals ++ brLocals) brX5 fTqFill tqParams
    [vv brOr, vv brF1, vv brT, .op .add [vv brK, vv brNc], .const 0, vv brNr] tqBody
    [cellA C orr, cellA C od1, cellA C H9.length, BitVec.ofNat 64 (p.members.length + nC), BitVec.ofNat 64 0,
      BitVec.ofNat 64 p.recs.length]
    (by decide) rfl (by decide) hc.tq ?_
    (fun a w s' st => (pure () : AM Unit) s4 = .ok (a, s') ∧
      PostTF C Hc11 EH3 H11.length H9.length (p.members.length + nC) (recsOf p.recs fs1) 0 a w s' st)
    (fun a w s' C' => s' = s4 ∧ ∃ H' EH', C' = ctxE (ctxH C H') EH' ∧ Hc11 <+: H' ∧ EH3 <+: EH' ∧ H11.length ≤ H'.length ∧
      ∀ j (hj : j < (recsOf p.recs fs1).length), 0 ≤ j → ∃ o,
        H'[H9.length + 1 + 2 * (p.members.length + nC + j)]? = some (Enc.idxW (recsOf p.recs fs1)[j].name) ∧
        H'[H9.length + 2 + 2 * (p.members.length + nC + j)]? = some (ecell C o) ∧ CIE C.EB EH' o (recsOf p.recs fs1)[j])
    (fun a w s' st ⟨hr, H', EH', hp', hpe', hl', hs', hc'⟩ =>
      ⟨_, ⟨pure_run_unit _ _ _ hr, H', EH', rfl, hp', hpe', hl', hc'⟩, hs'⟩)
    (fun u hu _ hlk => specR_run (fun w' hw' => by
      subst hw'
      exact (tq_spec C hok hc.cp hc.fw hc.rw hc.cw hc.rq hc.tq p.recs fs1 hfs1l orr od1 H9.length (p.members.length + nC)
        Hc9 Hf1 (ptrsRep_mono hpH9 (fun oi a h => recRep_mono hpH9 h) hpr) hfsat1 (hf1H.trans hp49) hlR
        _ 0 H11 Hc11 EH3 s4 rfl (Nat.zero_le _) (hHc910.trans hHc1011) (by simp [Hc11]) hpc11 (by omega)
        ((hpe1.trans hpe2).trans hpe3)) _ (pre_of_lookups hu tqParams _ rfl hlk)))
    (fun _ w12 s8 C12 ⟨hs8, H12, EH4, eC12, hp12, hpe4, hl12, hrc⟩ => ?_)
  · exact ⟨by simp +decide [sev, Env.get], by simp +decide [sev, Env.get] <;> rfl, by simp +decide [sev, Env.get] <;> rfl,
      by simp +decide [sev, Env.get]; rw [BitVec.ofNat_add_ofNat], rfl, by simp +decide [sev, Env.get], trivial⟩
  subst eC12; subst s8
  -- the recursors' block (the second firing modes)
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN12 => ?_)
  have hHN12' : H12.length ≤ C.HN := hHN12
  refine specR_allocI (C := ctxE (ctxH C H12) EH4) brD _ (p.recs.length + 1) (by omega) (by decide) (fun v => ?_)
    (fun H13 ws13 hp13 hws13 hroom13 => ?_)
  · simp +decide [sev, Env.get]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hp13' : H12 <+: H13 := hp13
  change SpecR (Inv (ctxE (ctxH C (H13 ++ ws13)) EH4) _ _ _ _) _ _ _ _
  have hpeA4 : C.EH <+: EH4 := ((hpe1.trans hpe2).trans hpe3).trans hpe4
  have hq13 : H13.length < (ctxE (ctxH C (H13 ++ ws13)) EH4).H.length := by
    show H13.length < (H13 ++ ws13).length; simp; omega
  refine specR_heapStoreI (ctxOK_E (ctxOK_H hok (H13 ++ ws13)) hpeA4) (vv brD) (vv brNr) H13.length hq13
    (BitVec.ofNat 64 p.recs.length) (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get]) ?_
  change SpecR (Inv (ctxE (ctxH C ((H13 ++ ws13).set H13.length (BitVec.ofNat 64 p.recs.length))) EH4) _ _ _ _) _ _ _ _
  generalize hB13 : (H13 ++ ws13).set H13.length (BitVec.ofNat 64 p.recs.length) = B13
  have hB13len : B13.length = H13.length + (p.recs.length + 1) := by rw [← hB13]; simp [hws13]
  have hpB13 : H13 <+: B13 := by
    refine prefix_of_get? (by omega) (fun j hj => ?_)
    rw [← hB13, List.getElem?_set_ne (by omega), List.getElem?_append_left hj]
  let Hc13 := B13.take (H13.length + 1)
  have hpc13 : H13 <+: Hc13 := by
    refine prefix_of_get? (by simp [Hc13]; omega) (fun j hj => ?_)
    simp only [Hc13]; rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj]
    exact get_prefix (List.getElem?_eq_getElem hj) hpB13
  have hHc130 : Hc13[H13.length]? = some (BitVec.ofNat 64 p.recs.length) := by
    simp only [Hc13]; rw [List.getElem?_take_of_lt (by omega), ← hB13, List.getElem?_set_self (by simp; omega)]
  have hp9c13 : Hc9 <+: Hc13 := (((hHc910.trans hHc1011).trans hp12).trans hp13').trans hpc13
  have hp5c13 : H5 <+: Hc9 := (hp6'.trans (hp7'.trans (hpc7.trans hp8))).trans (hp9'.trans hpc9)
  have hfsat2 : FiresAt C Hc9 Hf2 od2 fs2 := fun j hj => by
    obtain ⟨o, h1', h2'⟩ := hfs2 j hj
    exact ⟨o, get_prefix (by simpa using h1') hp5c13, h2'⟩
  refine specR_pureBind () ?_
  refine specR_callNC (C := ctxE (ctxH C B13) EH4) (D := ctxLocals ++ brLocals) brX6 fTxFill txParams
    [vv brOr, vv brF2, vv brD, .const 0, vv brNr] txBody
    [cellA C orr, cellA C od2, cellA C H13.length, BitVec.ofNat 64 0, BitVec.ofNat 64 p.recs.length]
    (by decide) rfl (by decide) hc.tx
    ⟨by simp +decide [sev, Env.get], by simp +decide [sev, Env.get] <;> rfl, by simp +decide [sev, Env.get] <;> rfl,
      rfl, by simp +decide [sev, Env.get], trivial⟩
    (fun a w s' st => (pure () : AM Unit) s4 = .ok (a, s') ∧
      PostTX C Hc13 EH4 B13.length H13.length (recsOf p.recs fs2) 0 a w s' st)
    (fun a w s' C' => s' = s4 ∧ ∃ H' EH', C' = ctxE (ctxH C H') EH' ∧ Hc13 <+: H' ∧ EH4 <+: EH' ∧
      ∀ j (hj : j < (recsOf p.recs fs2).length), 0 ≤ j → ∃ o,
        H'[H13.length + 1 + j]? = some (ecell C o) ∧ CIE C.EB EH' o (recsOf p.recs fs2)[j])
    (fun a w s' st ⟨hr, H', EH', hp', hpe', hl', hs', hc'⟩ =>
      ⟨_, ⟨pure_run_unit _ _ _ hr, H', EH', rfl, hp', hpe', hc'⟩, hs'⟩)
    (fun u hu _ hlk => specR_run (fun w' hw' => by
      subst hw'
      exact (tx_spec C hok hc.cp hc.fw hc.rw hc.cw hc.rq hc.tx p.recs fs2 hfs2l orr od2 H13.length Hc9 Hf2
        (ptrsRep_mono hpH9 (fun oi a h => recRep_mono hpH9 h) hpr) hfsat2 (hf2H.trans hp5c13) hlR
        _ 0 B13 Hc13 EH4 s4 rfl (Nat.zero_le _) hp9c13 (by simp [Hc13]) (List.take_prefix _ _) (by omega) hpeA4)
        _ (pre_of_lookups hu txParams _ rfl hlk)))
    (fun _ w14 s9 C14 ⟨hs9, H14, EH5, eC14, hp14, hpe5, hrs2⟩ => ?_)
  subst eC14; subst s9
  -- the table and the recursors' block, read back in the final heaps
  have hpe5A : C.EH <+: EH5 := hpeA4.trans hpe5
  have hp12H14 : H12 <+: H14 := hp13'.trans (hpc13.trans hp14)
  have hc11H14 : Hc11 <+: H14 := hp12.trans hp12H14
  have hc10H14 : Hc10 <+: H14 := hHc1011.trans hc11H14
  have hc9H14 : Hc9 <+: H14 := hHc910.trans hc10H14
  have hpH14 : C.H <+: H14 := hpH9.trans hc9H14
  have tr10 : ∀ q, q < H9.length + 1 + 2 * p.members.length → H14[q]? = H10[q]? := fun q hq => by
    have h1 : Hc10[q]? = H10[q]? := by simp only [Hc10]; rw [List.getElem?_take_of_lt hq]
    rw [← h1]
    rcases hcq : Hc10[q]? with _ | v
    · simp [Hc10] at hcq; omega
    · exact get_prefix hcq hc10H14
  have tr11 : ∀ q, q < H9.length + 1 + 2 * (p.members.length + nC) → H14[q]? = H11[q]? := fun q hq => by
    have h1 : Hc11[q]? = H11[q]? := by simp only [Hc11]; rw [List.getElem?_take_of_lt hq]
    rw [← h1]
    rcases hcq : Hc11[q]? with _ | v
    · simp [Hc11] at hcq; omega
    · exact get_prefix hcq hc11H14
  set cs := formersOf p isRec p.members nzs ++ membersCtors p.nP p.members ++ recsOf p.recs fs1 with hcs
  have hcsl : cs.length = nT := by simp only [hcs, List.length_append, hfml, hmcl, hrcl, hnT]
  have hent : ∀ j, j < nT → ∃ o, ∀ hj : j < cs.length,
      H14[H9.length + 1 + 2 * j]? = some (Enc.idxW (cs[j]'hj).name) ∧ H14[H9.length + 2 + 2 * j]? = some (ecell C o) ∧
      CIE C.EB EH5 o (cs[j]'hj) := by
    intro j hj
    rcases Nat.lt_or_ge j p.members.length with h1 | h1
    · obtain ⟨o, ho1, ho2, ho3⟩ := hfm j (by omega) (Nat.zero_le _)
      refine ⟨o, fun hj' => ⟨?_, ?_, ?_⟩⟩
      · rw [tr10 _ (by omega), show H9.length + 1 + 2 * j = H9.length + 1 + 2 * (0 + j) by omega, ho1]
        simp only [hcs, List.getElem_append_left (show j < (formersOf p isRec p.members nzs ++ membersCtors p.nP p.members).length by simp [hfml]; omega),
          List.getElem_append_left (show j < (formersOf p isRec p.members nzs).length by omega)]
      · rw [tr10 _ (by omega), show H9.length + 2 + 2 * j = H9.length + 2 + 2 * (0 + j) by omega, ho2]
      · simp only [hcs, List.getElem_append_left (show j < (formersOf p isRec p.members nzs ++ membersCtors p.nP p.members).length by simp [hfml]; omega),
          List.getElem_append_left (show j < (formersOf p isRec p.members nzs).length by omega)]
        exact cie_mono (hpe3.trans (hpe4.trans hpe5)) ho3
    rcases Nat.lt_or_ge j (p.members.length + nC) with h2 | h2
    · obtain ⟨o, ho1, ho2, ho3⟩ := hct (j - p.members.length) (by rw [hmcl]; omega) (Nat.zero_le _)
      refine ⟨o, fun hj' => ⟨?_, ?_, ?_⟩⟩
      · rw [tr11 _ (by omega), show H9.length + 1 + 2 * j = H9.length + 1 + 2 * (p.members.length + (j - p.members.length)) by omega, ho1]
        simp only [hcs, List.getElem_append_left (show j < (formersOf p isRec p.members nzs ++ membersCtors p.nP p.members).length by simp [hfml, hmcl]; omega),
          List.getElem_append_right (show (formersOf p isRec p.members nzs).length ≤ j by omega), hfml]
      · rw [tr11 _ (by omega), show H9.length + 2 + 2 * j = H9.length + 2 + 2 * (p.members.length + (j - p.members.length)) by omega, ho2]
      · simp only [hcs, List.getElem_append_left (show j < (formersOf p isRec p.members nzs ++ membersCtors p.nP p.members).length by simp [hfml, hmcl]; omega),
          List.getElem_append_right (show (formersOf p isRec p.members nzs).length ≤ j by omega), hfml]
        exact cie_mono (hpe4.trans hpe5) ho3
    · obtain ⟨o, ho1, ho2, ho3⟩ := hrc (j - (p.members.length + nC)) (by rw [hrcl]; omega) (Nat.zero_le _)
      refine ⟨o, fun hj' => ⟨?_, ?_, ?_⟩⟩
      · rw [show H9.length + 1 + 2 * j = H9.length + 1 + 2 * (p.members.length + nC + (j - (p.members.length + nC))) by omega]
        rw [get_prefix ho1 hp12H14]
        simp only [hcs, List.getElem_append_right (show (formersOf p isRec p.members nzs ++ membersCtors p.nP p.members).length ≤ j by simp [hfml, hmcl]; omega),
          List.length_append, hfml, hmcl]
      · rw [show H9.length + 2 + 2 * j = H9.length + 2 + 2 * (p.members.length + nC + (j - (p.members.length + nC))) by omega]
        exact get_prefix ho2 hp12H14
      · simp only [hcs, List.getElem_append_right (show (formersOf p isRec p.members nzs ++ membersCtors p.nP p.members).length ≤ j by simp [hfml, hmcl]; omega),
          List.length_append, hfml, hmcl]
        exact cie_mono hpe5 ho3
  obtain ⟨os', hosl, hos⟩ := exists_list_of_forall nT hent
  let es : List (NIdx × Nat × IConstantInfo) := (cs.zip os').map fun x => (x.1.name, x.2, x.1)
  have hesl : es.length = nT := by simp [es, hcsl, hosl]
  have hes2 : es.map (·.2.2) = cs := by
    simp only [es, List.map_map]
    exact List.map_fst_zip (by omega)
  have hesn : ∀ e ∈ es, e.1 = e.2.2.name := by
    intro e he; simp only [es, List.mem_map] at he; obtain ⟨x, -, rfl⟩ := he; rfl
  let C2 := ctxSt (ctxE C EH5) s4.store
  have hBT : BTabAt C2 H14 H9.length es := by
    refine ⟨by rw [hesl]; exact get_prefix hHc90 hc9H14, fun j hj => ?_⟩
    have hjc : j < cs.length := by omega
    obtain ⟨h1, h2, h3⟩ := hos j (by omega) hjc
    have hej : es[j] = ((cs[j]'hjc).name, os'.getD j 0, cs[j]'hjc) := by
      simp only [es, List.getElem_map, List.getElem_zip, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show j < os'.length by omega), Option.getD_some]
    rw [hej]
    exact ⟨h1, h2, h3⟩
  have hfe : ∀ n, (consBlockRecsTemp cs C.fe []).1.find? n = bfLook es C2.fe n := fun n => by
    show _ = bfLook es C.fe n
    rw [bfLook_crt es C.fe hesn n, hes2]
  refine specR_fact (fun t ht => And.intro ht.sr.envd.1 ht.sr.floor) (fun ⟨hcd, hfl⟩ => ?_)
  have hfD : ConstDen (consBlockRecsTemp cs C.fe []).1 C2.St :=
    constDen_bfLook hfe hcd (by
      rw [hes2]
      exact blockDen_of p isRec nzs fs1 s4.store hcap
        ⟨fun ms hms => ⟨cvDen_ext (hCV.1 ms hms).1 hfl, cvDen_ext (hCV.1 ms hms).2.1 hfl,
          fun c hc => cvDen_ext ((hCV.1 ms hms).2.2 c hc) hfl⟩, fun rc hrc => cvDen_ext (hCV.2 rc hrc) hfl⟩)
  have hr4' : p.recs.mapM (recFire p) s3 = .ok (fs2, s4) := by simpa using hr4
  have hRA : RecsAt C2 H14 H13.length (recsOf p.recs fs2) := by
    have hl2 : (recsOf p.recs fs2).length = p.recs.length := by simp [recsOf, hfs2l]
    refine ⟨by rw [hl2]; exact get_prefix hHc130 hp14, fun i hi => ?_⟩
    obtain ⟨o, ho1, ho2⟩ := hrs2 i hi (Nat.zero_le _)
    exact ⟨o, ho1, ho2, fun cv mI rP isK rules h rl hrl =>
      hRD s3 s4 fs2 hst3 hpo3 hx3 hr4' _ (List.getElem_mem hi) cv mI rP isK rules h rl hrl⟩
  have hAn2 : denoteN C2.St.ns anonH = some .anonymous := hfl.lss.ls.ns _ _ hAn
  have hf2 : Front.FrontOK C2 := by cases hf; constructor <;> assumption
  have hok2 : CtxOK C2 := ctxOK_St (ctxOK_E hok hpe5A) _
  -- the read, at the raised floor
  refine specR_invRaise (R' := fun r w s' st => w = boolW r.1 ∧ ConRon.Bridge.Inductives.GR.FEq r.2 C.fe ∧
      r.2.natLit = C.fe.natLit ∧ r.2.strLit = C.fe.strLit ∧ ∃ H' EH', C.H <+: H' ∧ C.EH <+: EH' ∧
      SR (ctxSt (ctxE (ctxH C H') EH') s4.store) s' st) ?_
    (fun r w s' t hx ⟨h1, h2, h3, h4, H', EH', h5, h6, h7⟩ => ⟨h1, h2, h3, h4, H', EH', h5, h6, sr_lower h7 hx⟩)
  refine specR_congr (m' := recsRead (consBlockRecsTemp cs C.fe []).1 ((recsOf p.recs fs2).drop 0) >>= fun ok => _)
    (by rw [List.drop_zero]) ?_
  refine specR_callNIH (C := ctxSt (ctxE (ctxH C H14) EH5) s4.store) brOk fRecsRead ksParams
    [vv brT, vv brD, .const 0] ksBody [cellA C H9.length, cellA C H13.length, BitVec.ofNat 64 0] (by decide) rfl
    (by decide) hc.hcs
    ⟨by simp +decide [sev, Env.get] <;> rfl, by simp +decide [sev, Env.get] <;> rfl, rfl, trivial⟩
    (PostB (ctxH C2 H14)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ksParams _ rfl hlk)
      (ks_spec ra C2 hok2 hf2 (by ctx_tr hc.rd) hAn2 (by ctx_tr hc.ro) hc.hcr hc.hcl hc.hck hc.hcs es H9.length
        (consBlockRecsTemp cs C.fe []).1 hfe hfD (recsOf p.recs fs2) H13.length _ 0 H14 s4 rfl (Nat.zero_le _) hpH14
        hBT hRA))
    (fun ok w s10 H15 hp15 hw => ?_)
  subst hw
  have hp15' : H14 <+: H15 := hp15
  exact specR_returnI _ _ (by simp [Env.get])
    (fun t ht => ⟨rfl, crt_pop_feq cs C.fe, rfl, rfl, H15, EH5, hpH14.trans hp15', hpe5A,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
