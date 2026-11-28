import ConPanqueque.T.Ind.RecPush
import ConPanqueque.T.Ind.RecNames
import ConRon.Bridge.Inductives.GenRec

/-!
# `genRules` over every recursor

`cfkBody`: the pushed names (`constNames`), every class's recursor name (`classRecNames`), then the pushes, the
rules and the pops (`genRulesPush`), and the flush leaving the pushed environment.  The environment handed back is
the twin's (`classFeR`'s pops with the flags set back), which answers as the entry one (`classFeR_pop`).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

/-- The twin's environment after the pops, the flags set back. -/
def feBack (p : BlockShape) (cvGs : List IConstantVal) (recCls : List Nat) (fe : IFEnv) : IFEnv :=
  ((classFeR p cvGs recCls fe).2.foldr (fun (x : NIdx × Option IConstantInfo) acc => acc.popTemp x.1 x.2)
    (classFeR p cvGs recCls fe).1).setFlags fe.natLit fe.strLit

theorem genRules_eq (mode : ConLeche.CheckMode) (fe : IFEnv) (p : BlockShape) (g : ClassGen) (recCls : List Nat)
    (cvGs : List IConstantVal) :
    genRules mode fe p g recCls cvGs = (gprM mode p g recCls cvGs (cvGs.map (·.name)) 0 fe >>= fun out => do
      flushCaches
      pure (feBack p cvGs recCls fe, out)) := by
  unfold genRules gprM feBack classFeR
  simp only [List.drop_zero, bind_assoc]

theorem feBack_find (p : BlockShape) (cvGs : List IConstantVal) (recCls : List Nat) (fe : IFEnv) (n : NIdx) :
    (feBack p cvGs recCls fe).find? n = fe.find? n := by
  unfold feBack; rw [IFEnv.setFlags_find?]; exact (Inductives.GR.classFeR_pop p cvGs recCls fe).find? n

theorem feBack_rawTable (p : BlockShape) (cvGs : List IConstantVal) (recCls : List Nat) (fe : IFEnv) (n : NIdx) :
    (feBack p cvGs recCls fe).rawTable? n = fe.rawTable? n := by
  unfold feBack; rw [IFEnv.setFlags_rawTable?]; exact (Inductives.GR.classFeR_pop p cvGs recCls fe).rawTable? n

theorem feBack_findTable (p : BlockShape) (cvGs : List IConstantVal) (recCls : List Nat) (fe : IFEnv) (n : NIdx) :
    (feBack p cvGs recCls fe).findTable? n = fe.findTable? n := by
  unfold IFEnv.findTable?; rw [feBack_find, feBack_rawTable]

theorem feBack_base (p : BlockShape) (cvGs : List IConstantVal) (recCls : List Nat) (fe : IFEnv) :
    (feBack p cvGs recCls fe).base = fe.base := by
  unfold feBack; exact (Inductives.GR.classFeR_pop p cvGs recCls fe).2.2.1

theorem feBack_litW (p : BlockShape) (cvGs : List IConstantVal) (recCls : List Nat) (fe : IFEnv) :
    litW (feBack p cvGs recCls fe) = litW fe := rfl

theorem feBack_tblGate {p : BlockShape} {cvGs : List IConstantVal} {recCls : List Nat} {fe : IFEnv}
    (h : TblGate fe) : TblGate (feBack p cvGs recCls fe) := by
  intro n t ht
  rw [feBack_rawTable] at ht
  rw [feBack_find]; exact h n t ht

theorem feBack_flagsOK {p : BlockShape} {cvGs : List IConstantVal} {recCls : List Nat} {fe : IFEnv}
    (h : FlagsOK fe) : FlagsOK (feBack p cvGs recCls fe) :=
  Inductives.GR.classFeR_pop_flags p cvGs recCls h

theorem feBack_litsPinned {p : BlockShape} {cvGs : List IConstantVal} {recCls : List Nat} {fe : IFEnv} {ps : Pins}
    (h : LitsPinned fe ps) : LitsPinned (feBack p cvGs recCls fe) ps := by
  unfold LitsPinned; rw [feBack_base]; exact h

def cfkCv := ofString "cfk_cv"
def cfkRl := ofString "cfk_rl"
def cfkOc := ofString "cfk_oc"
def cfkCss := ofString "cfk_css"
def cfkOms := ofString "cfk_oms"
def cfkRp := ofString "cfk_rp"
def cfkNp := ofString "cfk_np"
def cfkPm := ofString "cfk_pm"
def cfkSl := ofString "cfk_sl"
def cfkPr := ofString "cfk_pr"
def cfkN0 := ofString "cfk_n0"
def cfkN := ofString "cfk_n"
def cfkPn := ofString "cfk_pn"
def cfkPl := ofString "cfk_pl"
def cfkT := ofString "cfk_t"
def cfkK := ofString "cfk_k"
def cfkRnb := ofString "cfk_rnb"
def cfkR := ofString "cfk_r"
def fCfk := ofString "genRulesAll"

def cfkParams : List MlS := [cfkCv, cfkRl, cfkOc, cfkCss, cfkOms, cfkRp, cfkNp, cfkPm, cfkSl, cfkPr, cfkN0]
def cfkLocals : List MlS := [cfkN, cfkPn, cfkPl, cfkT, cfkK, cfkRnb, cfkR, lJ0]

def cfkBody (C : Ctx) : ProgHOL 64 := prologue cfkLocals
  (.seq (.assign .local cfkN (.load .one (vv cfkCv)))
  (.seq (.call (some (some (.local, cfkPn), none)) fCvn [vv cfkCv, .const 0, vv cfkN])
  (.seq (.assign .local cfkPl (.load .one (vv cfkPn)))
  (guardP cfkPl 59
  (.seq (.assign .local cfkT (.load .one (vv cfkOc)))
  (.ite (.cmp .lower (vv cfkT) (vv cfkN)) hang
  (.seq (.assign .local cfkK (.load .one (vv cfkOms)))
  (guardP cfkK 62
  (.seq (.call (some (some (.local, cfkRnb), none)) fRnb [vv cfkOc, vv cfkCv, .const 0, vv cfkK, vv cfkN])
  (.seq (.call (some (some (.local, cfkR), none)) fGpr
      [vv cfkCv, vv cfkRl, .const 0, vv cfkN, vv cfkOc, vv cfkCss, vv cfkOms, vv cfkRp, vv cfkNp, vv cfkPm, vv cfkSl,
        vv cfkPr, vv cfkN0, vv cfkPn, vv cfkPl, vv cfkRnb])
  (flushCode C (flushRegions false)
  (.return (vv cfkR)))))))))))))

structure CFKCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  gpr : GPRCodes mode C
  rnb : RNBCodes C
  cvn : C.code.lookup fCvn = some (cvnParams.map (fun p => (p, ShapeHOL.one)), cvnBody C, .one)
  self : C.code.lookup fCfk = some (cfkParams.map (fun p => (p, ShapeHOL.one)), cfkBody C, .one)

section
variable {σ : Type}

theorem cfk_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cfkLocals → (ctxEnv C ++ cfkParams.zip vals).get x = none :=
  Knot.params_none C cfkLocals cfkParams vals (by decide) (by decide)

/-- After every recursor's rules: the twin's environment (answering as `C`'s), and the output list. -/
def PostGRK (C : Ctx) (r : IFEnv × List (IConstantVal × TargetMajor × List EIdx)) (w : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  ∃ EH envM H o, C.EH <+: EH ∧ C.H <+: H ∧ CtxOK (ctxNew C r.1 EH envM H) ∧ SR (ctxNew C r.1 EH envM H) s' st ∧
    TblGate r.1 ∧ FlagsOK r.1 ∧ LitsPinned r.1 C.pins ∧ (∀ n, r.1.find? n = C.fe.find? n) ∧
    (∀ n, r.1.findTable? n = C.fe.findTable? n) ∧ w = cellA C o ∧ PRep C H o (fun H o t => RRRep C H o t) r.2

theorem postGRK_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostGRK C a w s' st → PostGRK C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨EH, envM, H, o, h1, h2, h3, h4, h5⟩ => ⟨EH, envM, H, o, h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl, h5⟩

set_option maxHeartbeats 64000000 in
/-- **`genRules`** over every recursor. -/
theorem cfk_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hpl : C.saved = none) (hc : CFKCodes mode C)
    (hg : TblGate C.fe) (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins)
    (p : BlockShape) (g : ClassGen) (recCls : List Nat) (cvGs : List IConstantVal)
    (hpml : g.params.length < 2 ^ 56) (hsl : g.slots.length < 2 ^ 56)
    (hcb : ∀ sl ∈ g.slots, ∀ c C' ihs, sl = .minor c C' ihs → c < 2 ^ 63)
    (hprl : g.pre.length < 2 ^ 56) (hnP : g.nP < 2 ^ 56)
    (hlen : ∀ cv ∈ cvGs, cv.levelParams.length < 2 ^ 59) (hrcb : ∀ c ∈ recCls, c < 2 ^ 63)
    (hxb : ∀ xs ∈ g.ctors, xs.length < 2 ^ 58 ∧ ∀ x ∈ xs, x.nF < 2 ^ 56)
    (hden : ∀ cv ∈ cvGs, CVDen cv C.St)
    (hks : ∀ cv ∈ cvGs, ∃ ks : List ConLeche.Name, ∃ _ : ks.length = cv.levelParams.length,
      ∀ j (hj : j < cv.levelParams.length), denoteN C.St.ns cv.levelParams[j] = some (ks[j]'(by omega)))
    (ocv orl orc ocss oms opm os opr : Nat)
    (hcv : PRep C C.H ocv (fun H o cv => CVRep C H o cv) cvGs) (hR : PtrsRep C C.H orl (RecRep C C.H) p.recs)
    (hRC : BlkAt C.H orc (recCls.map (BitVec.ofNat 64)))
    (hcss : PRep C C.H ocss (fun H o xs => PRep C H o (fun H o cc => CCRep C H o cc) xs) g.ctors)
    (hT : TMBlkR C C.H oms g.cls) (hpm : BlkAt C.H opm (g.params.map Enc.idxW)) (hsb : SlotBlk C C.H os g.slots)
    (hpr : BlkAt C.H opr (g.pre.map Enc.idxW)) (s : AState) :
    SpecR (σ := σ) (Pre C s (cfkParams.zip [cellA C ocv, cellA C orl, cellA C orc, cellA C ocss, cellA C oms,
        BitVec.ofNat 64 g.pre.length, BitVec.ofNat 64 g.nP, cellA C opm, cellA C os, cellA C opr,
        BitVec.ofNat 64 (g.nP + g.slots.length)])) (cfkBody C) s (genRules mode C.fe p g recCls cvGs) (PostGRK C) := by
  refine specR_prologue (postGRK_locals C) (cfk_none C _) ?_
  rw [genRules_eq]
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : C.H.length ≤ C.HN := hHN
  obtain ⟨ovs, hovl, hovb, hovr⟩ := id hcv
  have hn0 : C.H[ocv]? = some (BitVec.ofNat 64 cvGs.length) := by simpa [hovl] using hovb.1
  refine UD.specR_heapLoadI' (C := C) cfkN (vv cfkCv) ocv _ hn0 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, cfkParams, ctxEnv] <;> rfl) ?_
  -- the pushed names
  refine specR_congr (m' := pure ((cvGs.drop 0).map (·.name)) >>= fun _ => _) (by rw [pure_bind]) ?_
  refine specR_callNIH (C := C) cfkPn fCvn cvnParams [vv cfkCv, .const 0, vv cfkN] (cvnBody C)
    [cellA C ocv, BitVec.ofNat 64 0, BitVec.ofNat 64 cvGs.length] (by decide) rfl (by decide) hc.cvn
    ⟨by simp +decide [sev, Env.get_cons, Env.get, cfkParams, ctxEnv], rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (fun a w s' st => (pure ((cvGs.drop 0).map (·.name)) : AM (List NIdx)) s = .ok (a, s') ∧ PostNBlk C a w s' st)
    (fun ns w s' H' => (pure ((cvGs.drop 0).map (·.name)) : AM (List NIdx)) s = .ok (ns, s') ∧
      ∃ o, w = cellA C o ∧ BlkAt H' o (ns.map Enc.idxW))
    (fun ns w s' st ⟨hrun, H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨hrun, o, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu cvnParams _ rfl hlk)
      (cvn_spec C hok hc.cvn cvGs ocv hcv (cvGs.length - 0) 0 C.H s rfl (Nat.zero_le _) (List.prefix_refl _))))
    (fun ns w s1 H1 hp1 ⟨hrun, opn, hw, hpnb⟩ => ?_)
  subst hw
  obtain ⟨rfl, rfl⟩ := AM.pure_ok hrun
  simp only [List.drop_zero] at hpnb ⊢
  have hp1' : C.H <+: H1 := hp1
  have hpl0 : H1[opn]? = some (BitVec.ofNat 64 cvGs.length) := by simpa using hpnb.1
  refine UD.specR_heapLoadI' (C := ctxH C H1) cfkPl (vv cfkPn) opn _ hpl0 (by decide)
    (by simp +decide [sev, Env.get_cons] <;> rfl) ?_
  have hcvl := blk_len_lt hok hHN' hovb
  simp only [List.length_map] at hcvl
  refine specR_guardI cfkPl cvGs.length 59 (by decide) (by simp +decide [Env.get_cons]) (by omega) (fun hcv59 => ?_)
  -- every recursor has a class
  have hrc0 := get_prefix hRC.1 hp1'
  simp only [List.length_map] at hrc0
  refine UD.specR_heapLoadI' (C := ctxH C H1) cfkT (vv cfkOc) orc _ hrc0 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, cfkParams, ctxEnv] <;> rfl) ?_
  have hrcl : recCls.length < 2 ^ 61 := by
    have := blk_len_lt hok hHN' hRC; simp at this; omega
  have hlw := nd_lt_iff recCls.length cvGs.length (by omega) (by omega)
  by_cases hrn : recCls.length < cvGs.length
  · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, cfkParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hrn]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
  refine specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, cfkParams, ctxEnv,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
    (fun h => absurd rfl h) (fun _ => ?_)
  -- every class's recursor name
  obtain ⟨ps, hpsL, hpsb, hpsr⟩ := id hT
  have hk0 := get_prefix hpsb.1 hp1'
  simp only [List.length_map, hpsL] at hk0
  refine UD.specR_heapLoadI' (C := ctxH C H1) cfkK (vv cfkOms) oms _ hk0 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, cfkParams, ctxEnv] <;> rfl) ?_
  have hclsl : g.cls.length < 2 ^ 61 := by
    have := blk_len_lt hok hHN' hpsb; simp at this; omega
  refine specR_guardI cfkK g.cls.length 62 (by decide) (by simp +decide [Env.get_cons]) (by omega) (fun hk62 => ?_)
  refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => _) (by rw [pure_bind]) ?_
  refine specR_callNIH (C := ctxH C H1) cfkRnb fRnb rnbParams [vv cfkOc, vv cfkCv, .const 0, vv cfkK, vv cfkN]
    (rnbBody C) [cellA C orc, cellA C ocv, BitVec.ofNat 64 0, BitVec.ofNat 64 g.cls.length, BitVec.ofNat 64 cvGs.length]
    (by decide) rfl (by decide) hc.rnb.self
    ⟨by simp +decide [sev, Env.get_cons, Env.get, cfkParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cfkParams, ctxEnv],
      rfl, by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], trivial⟩
    (PostRNB (ctxH C H1) recCls cvGs 0 g.cls.length)
    (fun _ w _ H' => ∃ o, ∃ rns : List NIdx, w = cellA C o ∧ BlkAt H' o (rns.map Enc.idxW) ∧
      ∀ j (hj : j < rns.length), classRecOf recCls cvGs (0 + j) = some rns[j])
    (fun a w s' st ⟨H', o, rns, hp', hw, hb, hl, hr, hsr⟩ => ⟨H', hp', ⟨o, rns, hw, hb, hr⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rnbParams _ rfl hlk)
      (rnb_spec C hok hc.rnb recCls orc hRC hrcb cvGs ocv hcv (by omega) g.cls.length (by omega)
        (g.cls.length - 0) 0 H1 s1 rfl (Nat.zero_le _) hp1'))
    (fun _ w s2 H2 hp2 ⟨orn, rns, hw, hrb, hrr⟩ => ?_)
  subst hw
  have hp2' : H1 <+: H2 := hp2
  have hpC2 : C.H <+: H2 := hp1'.trans hp2'
  -- the pushes, the rules, the pops
  refine specR_callNC (C := ctxH C H2) (D := ctxLocals ++ cfkLocals) cfkR fGpr gprParams
    [vv cfkCv, vv cfkRl, .const 0, vv cfkN, vv cfkOc, vv cfkCss, vv cfkOms, vv cfkRp, vv cfkNp, vv cfkPm, vv cfkSl,
      vv cfkPr, vv cfkN0, vv cfkPn, vv cfkPl, vv cfkRnb] (gprBody C)
    [cellA C ocv, cellA C orl, BitVec.ofNat 64 0, BitVec.ofNat 64 cvGs.length, cellA C orc, cellA C ocss, cellA C oms,
      BitVec.ofNat 64 g.pre.length, BitVec.ofNat 64 g.nP, cellA C opm, cellA C os, cellA C opr,
      BitVec.ofNat 64 (g.nP + g.slots.length), cellA C opn, BitVec.ofNat 64 (cvGs.map (·.name)).length, cellA C orn]
    (by decide) rfl (by decide) hc.gpr.self
    ⟨by simp +decide [sev, Env.get_cons, Env.get, cfkParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cfkParams, ctxEnv],
      rfl, by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, cfkParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, cfkParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cfkParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, cfkParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cfkParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, cfkParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cfkParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, cfkParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cfkParams, ctxEnv],
      by simp +decide [sev, Env.get_cons] <;> rfl, by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons] <;> rfl,
      trivial⟩
    (PostGP (ctxH C H2))
    (fun out w s' C' => ∃ EH envM H o, C' = ctxNew (ctxH C H2) C.fe EH envM H ∧ C.EH <+: EH ∧ H2 <+: H ∧
      CtxOK (ctxNew (ctxH C H2) C.fe EH envM H) ∧ w = cellA C o ∧ PRep C H o (fun H o t => RRRep C H o t) out)
    (fun out w s' st ⟨EH, envM, H, o, h1, h2, h3, h4, h5, h6⟩ => ⟨_, ⟨EH, envM, H, o, rfl, h1, h2, h4, h6⟩, h5⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu gprParams _ rfl hlk)
      (gpr_spec mode ra p g recCls cvGs (cvGs.map (·.name)) rns (fun t ht => by simpa using hrr t ht) hpml hsl hcb hprl hnP
        (by simp; omega) hlen hrcb hxb ocv orl orc ocss oms opm os opr opn orn (cvGs.length - 0) 0 (ctxH C H2) s2 rfl
        (Nat.zero_le _) (ctxOK_H hok H2) hs hpl (by ctx_tr hc.gpr) hg hF hL hden hks
        (pRep_mono hpC2 (fun _ _ => cvRep_mono hpC2) hcv) (ptrsRep_mono hpC2 (fun _ _ => recRep_mono hpC2) hR)
        (blkAt_mono hRC hpC2) (pRep_mono hpC2 (fun _ _ h => pRep_mono hpC2 (fun _ _ => ccRep_mono hpC2) h) hcss)
        (tmBlkR_mono hpC2 hT) (blkAt_mono hpm hpC2) (slotBlk_mono hpC2 hsb) (blkAt_mono hpr hpC2)
        (fun j hj => get_prefix (by simpa using hpnb.2 j (by simpa using hj)) hp2') hrb))
    (fun out w s3 C3 ⟨EH, envM, H3, o, eC, hpE, hp3, hok3, hw, hout⟩ => ?_)
  subst eC hw
  refine specR_flushTopI hok3 hpl false flushCaches rfl (by decide) ?_
  refine specR_atEntry fun t4 ht4 => ?_
  refine specR_feI (fe := feBack p cvGs recCls C.fe) (feBack_litW _ _ _ _)
    (envDen_congr (feBack_find p cvGs recCls C.fe) (feBack_findTable p cvGs recCls C.fe) ht4.sr.envd) ?_
  exact specR_returnI _ _ (by simp +decide [sev, Env.get_cons, Env.kill]) (fun t ht => ⟨EH, envM, H3, o, hpE,
    hpC2.trans hp3, ctxOK_fe hok3 (feBack_find p cvGs recCls C.fe) (feBack_findTable p cvGs recCls C.fe),
    sr_of_eq ht.sr rfl rfl rfl rfl, feBack_tblGate hg, feBack_flagsOK hF, feBack_litsPinned hL,
    feBack_find p cvGs recCls C.fe, feBack_findTable p cvGs recCls C.fe, rfl, hout⟩)

end

end ConPanqueque.T.Ind
