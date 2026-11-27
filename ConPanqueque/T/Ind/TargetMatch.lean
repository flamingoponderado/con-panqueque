import ConPanqueque.T.Ind.TargetAbs
import ConPanqueque.T.Ind.ClassKeys

/-!
# `targetParamsDefEq` (single-member blocks)

Each pair closed over the openers, moved to them, member-abstracted, then equal or inferred and defeq.  Every
`false` of the twin hangs, so the port answers only `true`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def tpdA := ofString "tpd_a"
def tpdB := ofString "tpd_b"
def tpdI := ofString "tpd_i"
def tpdN := ofString "tpd_n"
def tpdP := ofString "tpd_p"
def tpdPn := ofString "tpd_pn"
def tpdNm := ofString "tpd_nm"
def tpdUs := ofString "tpd_us"
def tpdHl := ofString "tpd_hl"
def tpdD := ofString "tpd_d"
def tpdX := ofString "tpd_x"
def tpdY := ofString "tpd_y"
def tpdV := ofString "tpd_v"
def tpdXc := ofString "tpd_xc"
def tpdXa := ofString "tpd_xa"
def tpdYc := ofString "tpd_yc"
def tpdYa := ofString "tpd_ya"
def tpdT := ofString "tpd_t"
def tpdR := ofString "tpd_r"
def fTpd := ofString "targetParamsDefEq"

def tpdParams : List MlS := [tpdA, tpdB, tpdI, tpdN, tpdP, tpdPn, tpdNm, tpdUs, tpdHl, tpdD]
def tpdLocals : List MlS := [tpdX, tpdY, tpdV, tpdXc, tpdXa, tpdYc, tpdYa, tpdT, tpdR]

def tpdRec : ProgHOL 64 :=
  .seq (.call (some (some (.local, tpdR), none)) fTpd
      [vv tpdA, vv tpdB, .op .add [vv tpdI, .const 1], vv tpdN, vv tpdP, vv tpdPn, vv tpdNm, vv tpdUs, vv tpdHl, vv tpdD])
    (.return (vv tpdR))

def tpdBody : ProgHOL 64 := prologue tpdLocals
  (.ite (.cmp .lower (vv tpdI) (vv tpdN))
  (.seq (.assign .local tpdX (.load .one (.op .add [vv tpdA, .op .add [.panop .mul [vv tpdI, .const 8], .const 8]])))
  (.seq (.assign .local tpdY (.load .one (.op .add [vv tpdB, .op .add [.panop .mul [vv tpdI, .const 8], .const 8]])))
  (.seq (.call (some (some (.local, tpdV), none)) ExB.fBvarB [(.const (BitVec.ofNat 64 coreWalkFuel)), vv tpdX])
  (.ite (.cmp .equal (vv tpdV) (.const 0))
  (.seq (.call (some (some (.local, tpdV), none)) ExB.fBvarB [(.const (BitVec.ofNat 64 coreWalkFuel)), vv tpdY])
  (.ite (.cmp .equal (vv tpdV) (.const 0))
  (.seq (.call (some (some (.local, tpdV), none)) ExF.fFvarB [(.const (BitVec.ofNat 64 coreWalkFuel)), vv tpdX])
  (.ite (.cmp .lower (vv tpdPn) (vv tpdV))
  hang
  (.seq (.call (some (some (.local, tpdV), none)) ExF.fFvarB [(.const (BitVec.ofNat 64 coreWalkFuel)), vv tpdY])
  (.ite (.cmp .lower (vv tpdPn) (vv tpdV))
  hang
  (.seq (.call (some (some (.local, tpdXc), none)) fTcp [vv tpdX, vv tpdP])
  (.seq (.call (some (some (.local, tpdXa), none)) fTa [vv tpdXc, vv tpdNm, vv tpdUs, vv tpdHl])
  (.seq (.call (some (some (.local, tpdYc), none)) fTcp [vv tpdY, vv tpdP])
  (.seq (.call (some (some (.local, tpdYa), none)) fTa [vv tpdYc, vv tpdNm, vv tpdUs, vv tpdHl])
  (.ite (.cmp .equal (vv tpdXa) (vv tpdYa))
  tpdRec
  (.seq (.call (some (some (.local, tpdT), none)) fI [(.const (BitVec.ofNat 64 checkFuel)), vv tpdD, vv tpdXa])
  (.seq (.call (some (some (.local, tpdT), none)) fI [(.const (BitVec.ofNat 64 checkFuel)), vv tpdD, vv tpdYa])
  (.seq (.call (some (some (.local, tpdT), none)) fD [(.const (BitVec.ofNat 64 checkFuel)), vv tpdD, vv tpdXa, vv tpdYa])
  (.ite (.cmp .equal (vv tpdT) (.const 0))
  hang
  tpdRec)))))))))))))
  hang))
  hang))))
  (.return (.const 1)))

structure TPDCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  hcB : ExB.CodesB C (ExB.bodyB C)
  bvb : C.code.lookup ExB.fBvarB = some ([(pFu, .one), (pH, .one)], ExB.bvbBody C, .one)
  hcF : ExF.CodesF C (ExF.bodyF C)
  fvb : C.code.lookup ExF.fFvarB = some ([(pFu, .one), (pH, .one)], ExF.fvbBody C, .one)
  rfw : RFWCodes C
  tcp : C.code.lookup fTcp = some (tcpParams.map (fun p => (p, ShapeHOL.one)), tcpBody, .one)
  tab : TABCodes C
  ta : C.code.lookup fTa = some (taParams.map (fun p => (p, ShapeHOL.one)), taBody, .one)
  k : KCodes C Comp.kBodies
  ac : Comp.AllCodes mode C
  self : C.code.lookup fTpd = some (tpdParams.map (fun p => (p, ShapeHOL.one)), tpdBody, .one)

section
variable {σ : Type}

theorem tpd_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ tpdLocals → (ctxEnv C ++ tpdParams.zip vals).get x = none :=
  Knot.params_none C tpdLocals tpdParams vals (by decide) (by decide)

set_option maxHeartbeats 16000000 in
/-- **`targetParamsDefEq`** from pair `i` on (only `true` returns). -/
theorem tpd_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hc : TPDCodes mode C) (d : Nat) (hd : d < 2 ^ 63) (tnm : NIdx) (tus : LsIdx) (tx : EIdx)
    (pfvs as bs : List EIdx) (pp pa pb : Nat) (hab : as.length = bs.length) (hal : as.length < 2 ^ 58)
    (hpl : pfvs.length < 2 ^ 58) (H0 : List (BitVec 64)) (hp0 : C.H <+: H0) (hpf : BlkAt H0 pp (pfvs.map Enc.idxW))
    (hA : BlkAt H0 pa (as.map Enc.idxW)) (hB : BlkAt H0 pb (bs.map Enc.idxW)) :
    ∀ f i (H : List (BitVec 64)) (s : AState), as.length - i = f → i ≤ as.length → H0 <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (tpdParams.zip [cellA C pa, cellA C pb, BitVec.ofNat 64 i,
        BitVec.ofNat 64 as.length, cellA C pp, BitVec.ofNat 64 pfvs.length, Enc.idxW tnm, Enc.idxW tus, Enc.idxW tx,
        BitVec.ofNat 64 d])) tpdBody s
        (targetParamsDefEq mode C.fe d [tnm] tus [tx] pfvs (as.drop i) (bs.drop i)) (PostB (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp
    have hin : i = as.length := by omega
    subst hin
    refine specR_prologue (postB_locals _) (tpd_none _ _) ?_
    have hlw := nd_lt_iff as.length as.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, tpdParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length, hab, List.drop_length]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp
    have hin : i < as.length := by omega
    have hpC : C.H <+: H := hp0.trans hp
    refine specR_prologue (postB_locals _) (tpd_none _ _) ?_
    have hlw := nd_lt_iff i as.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, tpdParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hinb : i < bs.length := by omega
    rw [List.drop_eq_getElem_cons hin, List.drop_eq_getElem_cons hinb]
    have hx := hA.2 i (by simp; omega)
    have hy := hB.2 i (by simp; omega)
    simp only [List.getElem_map] at hx hy
    refine UD.specR_heapLoadI' (C := ctxH C H) tpdX _ (pa + 1 + i) _ (get_prefix hx hp) (by decide)
      (by simp +decide [sev, Env.get, tpdParams, ctxEnv]; exact cellA_mulIdx C pa i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) tpdY _ (pb + 1 + i) _ (get_prefix hy hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv]; exact cellA_mulIdx C pb i (by omega)) ?_
    unfold targetParamsDefEq
    simp only [bind_assoc]
    -- bvarB a
    refine specR_callNIM tpdV ExB.fBvarB [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv tpdX] (ExB.bvbBody C)
      [BitVec.ofNat 64 coreWalkFuel, Enc.idxW as[i]] (by decide) rfl (by decide) hc.bvb
      ⟨rfl, by simp +decide [sev, Env.get_cons], trivial⟩ (ExF.PostN (ctxH C H)) (fun _ _ _ _ h => h.2.2)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
        (ExB.bvarB_spec (ctxH C H) (ctxOK_H hok H) (by ctx_tr hc.hcB) s coreWalkFuel as[i] CV.coreWalkFuel_lt))
      (fun b1 w s1 st ⟨hw, hb1, _⟩ => ?_)
    subst hw
    by_cases hb0 : b1 = 0
    swap
    · have hw0 : natW b1 ≠ 0#64 := by intro e; have := congrArg BitVec.toNat e; simp [natW] at this; omega
      exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hw0)
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    subst hb0
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, natW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, bind_assoc]
    -- bvarB b
    refine specR_callNIM tpdV ExB.fBvarB [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv tpdY] (ExB.bvbBody C)
      [BitVec.ofNat 64 coreWalkFuel, Enc.idxW bs[i]] (by decide) rfl (by decide) hc.bvb
      ⟨rfl, by simp +decide [sev, Env.get_cons], trivial⟩ (ExF.PostN (ctxH C H)) (fun _ _ _ _ h => h.2.2)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
        (ExB.bvarB_spec (ctxH C H) (ctxOK_H hok H) (by ctx_tr hc.hcB) s1 coreWalkFuel bs[i] CV.coreWalkFuel_lt))
      (fun b2 w s2 st ⟨hw, hb2, _⟩ => ?_)
    subst hw
    by_cases hb0 : b2 = 0
    swap
    · have hw0 : natW b2 ≠ 0#64 := by intro e; have := congrArg BitVec.toNat e; simp [natW] at this; omega
      exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hw0)
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    subst hb0
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, natW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [bne_self_eq_false, Bool.false_eq_true, ite_false, bind_assoc]
    -- fvarB a
    refine specR_callNIM tpdV ExF.fFvarB [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv tpdX] (ExF.fvbBody C)
      [BitVec.ofNat 64 coreWalkFuel, Enc.idxW as[i]] (by decide) rfl (by decide) hc.fvb
      ⟨rfl, by simp +decide [sev, Env.get_cons], trivial⟩ (ExF.PostN (ctxH C H)) (fun _ _ _ _ h => h.2.2)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
        (ExF.fvarB_spec (ctxH C H) (ctxOK_H hok H) (by ctx_tr hc.hcF) s2 coreWalkFuel as[i] CV.coreWalkFuel_lt))
      (fun fa w s3 st ⟨hw, hfa, _⟩ => ?_)
    subst hw
    have hlwa := ConPanqueque.T.Decl.nd_lt_iff pfvs.length fa (by omega) (by omega)
    by_cases hlea : fa ≤ pfvs.length
    swap
    · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv, natW,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlwa.mpr (by omega)]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv, natW,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega) (fun h => absurd rfl h) (fun _ => ?_)
    have hgt : ¬ (fa > pfvs.length) := by omega
    simp only [gt_iff_lt, hgt, decide_false, ite_false, bind_assoc, if_neg (show ¬ pfvs.length < fa by omega)]
    -- fvarB b
    refine specR_callNIM tpdV ExF.fFvarB [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv tpdY] (ExF.fvbBody C)
      [BitVec.ofNat 64 coreWalkFuel, Enc.idxW bs[i]] (by decide) rfl (by decide) hc.fvb
      ⟨rfl, by simp +decide [sev, Env.get_cons], trivial⟩ (ExF.PostN (ctxH C H)) (fun _ _ _ _ h => h.2.2)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
        (ExF.fvarB_spec (ctxH C H) (ctxOK_H hok H) (by ctx_tr hc.hcF) s3 coreWalkFuel bs[i] CV.coreWalkFuel_lt))
      (fun fb w s4 st ⟨hw, hfb, _⟩ => ?_)
    subst hw
    have hlwb := ConPanqueque.T.Decl.nd_lt_iff pfvs.length fb (by omega) (by omega)
    by_cases hleb : fb ≤ pfvs.length
    swap
    · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv, natW,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlwb.mpr (by omega)]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv, natW,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [pure_bind, decide_eq_true_eq, hleb, Bool.not_true, Bool.false_eq_true, ite_false, bind_assoc]
    simp only [decide_true, Bool.not_true, Bool.false_eq_true, ite_false, bind_assoc]
    have hpH : H0 <+: H := hp
    refine specR_callNIH (C := ctxH C H) tpdXc fTcp tcpParams [vv tpdX, vv tpdP] tcpBody [Enc.idxW as[i], cellA C pp]
      (by decide) rfl (by decide) hc.tcp
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv], trivial⟩
      (PostK (ctxH C H)) (fun y w _ _ => w = Enc.idxW y) (fun y w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tcpParams _ rfl hlk)
        (tcp_spec ra C hok hc.rfw hc.tcp pfvs pp H (by assumption) (blkAt_mono hpf (by assumption)) s4 as[i]))
      (fun ytpdXc w stpdXc H1 hpH1 hw => ?_)
    subst hw
    have hpC1 : C.H <+: H1 := hpC.trans hpH1
    have h01 : H0 <+: H1 := hp.trans hpH1
    refine specR_callNIH (C := ctxH C H1) tpdXa fTa taParams [vv tpdXc, vv tpdNm, vv tpdUs, vv tpdHl] taBody
      [Enc.idxW ytpdXc, Enc.idxW tnm, Enc.idxW tus, Enc.idxW tx] (by decide) rfl (by decide) hc.ta
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv], trivial⟩
      (PostK (ctxH C H1)) (fun y w _ _ => w = Enc.idxW y) (fun y w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu taParams _ rfl hlk)
        (ta_spec ra C hok hc.tab hc.ta tnm tus tx H1 (by assumption) stpdXc ytpdXc))
      (fun ytpdXa w stpdXa H2 hpH2 hw => ?_)
    subst hw
    have hpC2 : C.H <+: H2 := hpC1.trans hpH2
    have h02 : H0 <+: H2 := h01.trans hpH2
    refine specR_callNIH (C := ctxH C H2) tpdYc fTcp tcpParams [vv tpdY, vv tpdP] tcpBody [Enc.idxW bs[i], cellA C pp]
      (by decide) rfl (by decide) hc.tcp
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv], trivial⟩
      (PostK (ctxH C H2)) (fun y w _ _ => w = Enc.idxW y) (fun y w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tcpParams _ rfl hlk)
        (tcp_spec ra C hok hc.rfw hc.tcp pfvs pp H2 (by assumption) (blkAt_mono hpf (by assumption)) stpdXa bs[i]))
      (fun ytpdYc w stpdYc H3 hpH3 hw => ?_)
    subst hw
    have hpC3 : C.H <+: H3 := hpC2.trans hpH3
    have h03 : H0 <+: H3 := h02.trans hpH3
    refine specR_callNIH (C := ctxH C H3) tpdYa fTa taParams [vv tpdYc, vv tpdNm, vv tpdUs, vv tpdHl] taBody
      [Enc.idxW ytpdYc, Enc.idxW tnm, Enc.idxW tus, Enc.idxW tx] (by decide) rfl (by decide) hc.ta
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv], trivial⟩
      (PostK (ctxH C H3)) (fun y w _ _ => w = Enc.idxW y) (fun y w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu taParams _ rfl hlk)
        (ta_spec ra C hok hc.tab hc.ta tnm tus tx H3 (by assumption) stpdYc ytpdYc))
      (fun ytpdYa w stpdYa H4 hpH4 hw => ?_)
    subst hw
    have hpC4 : C.H <+: H4 := hpC3.trans hpH4
    have h04 : H0 <+: H4 := h03.trans hpH4
    have hrec : ∀ (Hx : List (BitVec 64)) (sx : AState) (Γ : Env), H4 <+: Hx →
        Γ.get tpdA = some (cellA C pa) → Γ.get tpdB = some (cellA C pb) → Γ.get tpdI = some (BitVec.ofNat 64 i) →
        Γ.get tpdN = some (BitVec.ofNat 64 as.length) → Γ.get tpdP = some (cellA C pp) →
        Γ.get tpdPn = some (BitVec.ofNat 64 pfvs.length) → Γ.get tpdNm = some (Enc.idxW tnm) →
        Γ.get tpdUs = some (Enc.idxW tus) → Γ.get tpdHl = some (Enc.idxW tx) → Γ.get tpdD = some (BitVec.ofNat 64 d) →
        SpecR (σ := σ) (Inv (ctxH C Hx) sx Γ [] (ctxLocals ++ tpdLocals)) tpdRec sx
          (targetParamsDefEq mode C.fe d [tnm] tus [tx] pfvs (List.drop (i + 1) as) (List.drop (i + 1) bs))
          (PostB (ctxH C H)) := by
      intro Hx sx Γ hpx gA gB gI gN gP gPn gNm gUs gHl gD
      unfold tpdRec
      refine specR_congr (m' := targetParamsDefEq mode C.fe d [tnm] tus [tx] pfvs (List.drop (i + 1) as)
        (List.drop (i + 1) bs) >>= fun r => pure r) (by simp only [bind_pure]) ?_
      refine specR_callNIH (C := ctxH C Hx) tpdR fTpd tpdParams
        [vv tpdA, vv tpdB, .op .add [vv tpdI, .const 1], vv tpdN, vv tpdP, vv tpdPn, vv tpdNm, vv tpdUs, vv tpdHl, vv tpdD]
        tpdBody [cellA C pa, cellA C pb, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 as.length, cellA C pp,
          BitVec.ofNat 64 pfvs.length, Enc.idxW tnm, Enc.idxW tus, Enc.idxW tx, BitVec.ofNat 64 d] (by decide) rfl
        (by decide) hc.self
        ⟨by simp [sev, gA], by simp [sev, gB], by simp only [sev, sev_vv, gI]; simp; exact word_add1_eq i,
          by simp [sev, gN], by simp [sev, gP], by simp [sev, gPn], by simp [sev, gNm], by simp [sev, gUs],
          by simp [sev, gHl], by simp [sev, gD], trivial⟩
        (PostB (ctxH C Hx)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tpdParams _ rfl hlk)
          (ih (i + 1) Hx sx (by omega) (by omega) (h04.trans hpx)))
        (fun b w s5 H5 hp5 hw => ?_)
      subst hw
      exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht =>
        ⟨H5, (hpH1.trans (hpH2.trans (hpH3.trans (hpH4.trans (hpx.trans hp5))))), rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    by_cases heq : ytpdXa = ytpdYa
    · subst heq
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [beq_self_eq_true, ↓reduceIte]
      exact hrec H4 _ _ (List.prefix_refl _) (by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv])
    have hne : Enc.idxW ytpdXa ≠ Enc.idxW ytpdYa := fun e => heq (Enc.idxW_inj e)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
    have hbe : (ytpdXa == ytpdYa) = false := beq_eq_false_iff_ne.mpr heq
    simp only [hbe, Bool.false_eq_true, ↓reduceIte, bind_assoc]
    have hk4 := kcodes_H hc.k H4
    refine Big.specR_callKC (C := ctxH C H4) tpdT fI kParams [.const (BitVec.ofNat 64 checkFuel), vv tpdD, vv tpdXa]
      (inferE (ctxH C H4) fIB) [BitVec.ofNat 64 checkFuel, BitVec.ofNat 64 d, Enc.idxW ytpdXa] (by decide) rfl
      (by decide) hk4.ei ⟨rfl, by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv], by simp +decide [sev, Env.get_cons], trivial⟩
      (Comp.inferTop ra mode (ctxOK_H hok H4) hk4 (allCodes_H hc.ac H4) hs _ d hd ytpdXa) (fun _ s6 H6 hp6 _ => ?_)
    have hk6 := kcodes_H hc.k H6
    refine Big.specR_callKC (C := ctxH C H6) tpdT fI kParams [.const (BitVec.ofNat 64 checkFuel), vv tpdD, vv tpdYa]
      (inferE (ctxH C H6) fIB) [BitVec.ofNat 64 checkFuel, BitVec.ofNat 64 d, Enc.idxW ytpdYa] (by decide) rfl
      (by decide) hk6.ei ⟨rfl, by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv], by simp +decide [sev, Env.get_cons], trivial⟩
      (Comp.inferTop ra mode (ctxOK_H hok H6) hk6 (allCodes_H hc.ac H6) hs _ d hd ytpdYa) (fun _ s7 H7 hp7 _ => ?_)
    have hk7 := kcodes_H hc.k H7
    refine specR_callCB (C := ctxH C H7) tpdT fD dParams
      [.const (BitVec.ofNat 64 checkFuel), vv tpdD, vv tpdXa, vv tpdYa]
      (dE (ctxH C H7)) [BitVec.ofNat 64 checkFuel, BitVec.ofNat 64 d, Enc.idxW ytpdXa, Enc.idxW ytpdYa] (by decide) rfl
      (by decide) hk7.ed ⟨rfl, by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv], by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], trivial⟩
      (Comp.defeqTop ra mode (ctxOK_H hok H7) hk7 (allCodes_H hc.ac H7) hs _ d hd ytpdXa ytpdYa)
      (fun b s8 H8 hp8 _ => ?_)
    cases b
    · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI)
        (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [↓reduceIte]
    exact hrec H8 _ _ ((hp6 : H4 <+: H6).trans ((hp7 : H6 <+: H7).trans hp8)) (by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv])
      (by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, tpdParams, ctxEnv])

/-! ## `targetClassMatch` (single-member blocks; only `true` returns) -/

def tccU := ofString "tcc_u"
def tccL := ofString "tcc_l"
def tccLp := ofString "tcc_lp"
def tccFt := ofString "tcc_ft"
def tccP := ofString "tcc_p"
def tccPn := ofString "tcc_pn"
def tccA := ofString "tcc_a"
def tccB := ofString "tcc_b"
def tccN := ofString "tcc_n"
def tccNm := ofString "tcc_nm"
def tccO := ofString "tcc_o"
def tccUs := ofString "tcc_us"
def tccX := ofString "tcc_x"
def tccNb := ofString "tcc_nb"
def tccR := ofString "tcc_r"
def fTcc := ofString "targetClassMatch"

def tccParams : List MlS := [tccU, tccL, tccLp, tccFt, tccP, tccPn, tccA, tccB, tccN, tccNm]
def tccLocals : List MlS := [tccO, tccUs, tccX, tccNb, tccR]

def tccBody (C : Ctx) : ProgHOL 64 := prologue tccLocals
  (.seq (.call (some (some (.local, tccO), none)) LLeq.fLsGo [vv tccU, vv tccL, .const 0])
  (.ite (.cmp .equal (vv tccO) (.const 2))
    (.seq (.call (some (some (.local, tccUs), none)) fParamLevels [vv tccLp])
    (.seq (.call (some (some (.local, tccX), none)) fInternFVar [vv tccFt, vv tccPn])
    (.seq (.assign .local tccNb (.load .one (vv tccB)))
    (.ite (.cmp .equal (vv tccNb) (vv tccN))
      (.seq (.call (some (some (.local, tccR), none)) fTpd
          [vv tccA, vv tccB, .const 0, vv tccN, vv tccP, vv tccPn, vv tccNm, vv tccUs, vv tccX,
            .op .add [vv tccPn, .const 1]])
        (.return (vv tccR)))
      hang))))
    hang))

structure TCCCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  ls : Comp.LsCodes C
  pl : C.code.lookup fParamLevels = some (plParams.map (fun p => (p, ShapeHOL.one)), plBody C, .one)
  pf : C.code.lookup fPlFill = some (pfParams.map (fun p => (p, ShapeHOL.one)), pfBody, .one)
  lp : C.code.lookup fInternLParam = some ([(lEn, .one)], internLParamBody, .one)
  lss : C.code.lookup fInternLs = some ([(pKey, .one), (lEc, .one)], internLsBody, .one)
  fv : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one)
  tpd : TPDCodes mode C
  self : C.code.lookup fTcc = some (tccParams.map (fun p => (p, ShapeHOL.one)), tccBody C, .one)

theorem tcc_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ tccLocals → (ctxEnv C ++ tccParams.zip vals).get x = none :=
  Knot.params_none C tccLocals tccParams vals (by decide) (by decide)

set_option maxHeartbeats 16000000 in
/-- **`targetClassMatch`** for a single-member block (only `true` returns). -/
theorem tcc_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hc : TCCCodes mode C) (p : BlockShape) (ms0 : MemberShape) (hms : p.members = [ms0])
    (ty0 : EIdx) (pfvs ds eds : List EIdx) (us lvls : LsIdx) (olp pp pa pb : Nat)
    (hlpl : ms0.cvT.levelParams.length < 2 ^ 59) (hdl : ds.length < 2 ^ 58) (heds : eds.length < 2 ^ 61)
    (hpl : pfvs.length < 2 ^ 58)
    (H0 : List (BitVec 64)) (hp0 : C.H <+: H0) (hlp : EBlk H0 olp (ms0.cvT.levelParams.map Enc.idxW))
    (hpf : BlkAt H0 pp (pfvs.map Enc.idxW)) (hA : BlkAt H0 pa (ds.map Enc.idxW)) (hB : BlkAt H0 pb (eds.map Enc.idxW))
    (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H0) s (tccParams.zip [Enc.idxW us, Enc.idxW lvls, cellA C olp, Enc.idxW ty0,
        cellA C pp, BitVec.ofNat 64 pfvs.length, cellA C pa, cellA C pb, BitVec.ofNat 64 ds.length,
        Enc.idxW ms0.cvT.name])) (tccBody C) s
      (targetClassMatch mode C.fe p [ty0] pfvs us ds lvls eds) (PostB (ctxH C H0)) := by
  refine specR_prologue (postB_locals _) (tcc_none _ _) ?_
  unfold targetClassMatch
  refine specR_callNIH (C := ctxH C H0) tccO LLeq.fLsGo LLeq.lsParams [vv tccU, vv tccL, .const 0] LLeq.lsGoBody
    [Enc.idxW us, Enc.idxW lvls, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.ls.G
    ⟨by simp +decide [sev, Env.get, tccParams, ctxEnv], by simp +decide [sev, Env.get, tccParams, ctxEnv], rfl, trivial⟩
    (fun o w s' st => s'.store = s.store ∧ s'.memos = s.memos ∧ LLeq.PostOB (ctxH (ctxH C H0) H0) o w s' st)
    (fun o w _ H' => H' = H0 ∧ w = LLeq.obW o)
    (fun o w s' st ⟨_, _, hw, hsr⟩ => ⟨H0, List.prefix_refl _, ⟨rfl, hw⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu LLeq.lsParams _ rfl hlk)
      (LLeq.lvlsEqQ_spec' (ctxH C H0) (ctxOK_H hok H0) hc.ls.S hc.ls.N hc.ls.M hc.ls.Cb hc.ls.B hc.ls.I hc.ls.R
        hc.ls.E hc.ls.Tr hc.ls.L hc.ls.V hc.ls.G H0 us lvls s))
    (fun o w s1 H1 hp1 ⟨eH, hw⟩ => ?_)
  subst hw; subst H1
  rcases o with _ | ⟨_ | _⟩
  · exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => specR_hangI)
  · exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
  simp only
  have hlps : p.lps = ms0.cvT.levelParams := by simp [BlockShape.lps, hms]
  have hnames : p.memberNames = [ms0.cvT.name] := by simp [BlockShape.memberNames, hms]
  rw [hlps, hnames]
  refine specR_callNIH (C := ctxH C H0) tccUs fParamLevels plParams [vv tccLp] (plBody C) [cellA C olp]
    (by decide) rfl (by decide) hc.pl ⟨by simp +decide [sev, Env.get_cons, Env.get, tccParams, ctxEnv], trivial⟩
    (PostLsH (ctxH C H0)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu plParams _ rfl hlk)
      (pl_spec ra C hok hc.pl hc.pf hc.lp hc.lss ms0.cvT.levelParams olp hlpl H0 s1 hlp))
    (fun bl w s2 H2 hp2 hw => ?_)
  subst hw
  have hp2' : H0 <+: H2 := hp2
  simp only [targetHoles, bind_assoc, pure_bind]
  refine ILP.specR_internFVarI ra (ctxOK_H hok H2) hc.fv tccX (vv tccFt) (vv tccPn) ty0 pfvs.length (by omega) (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, tccParams, ctxEnv])
    (by simp +decide [sev, Env.get_cons, Env.get, tccParams, ctxEnv]) (fun x s3 => ?_)
  have hbl := hB.1
  simp only [List.length_map] at hbl
  refine UD.specR_heapLoadI' (C := ctxH C H2) tccNb (vv tccB) pb _ (get_prefix hbl hp2') (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, tccParams, ctxEnv]; rfl) ?_
  have hel : eds.length < 2 ^ 63 := by omega
  by_cases hle : eds.length = ds.length
  swap
  · have hne : BitVec.ofNat 64 eds.length ≠ BitVec.ofNat 64 ds.length := fun e => hle (by
      have := congrArg BitVec.toNat e; simp at this; omega)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, tccParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, tccParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hle])
    (fun _ => ?_) (fun h => absurd h (by decide))
  refine specR_congr (m' := targetParamsDefEq mode C.fe (pfvs.length + 1) [ms0.cvT.name] bl [x] pfvs (ds.drop 0)
    (eds.drop 0) >>= fun r => pure r) (by simp) ?_
  refine specR_callNIH (C := ctxH C H2) tccR fTpd tpdParams
    [vv tccA, vv tccB, .const 0, vv tccN, vv tccP, vv tccPn, vv tccNm, vv tccUs, vv tccX, .op .add [vv tccPn, .const 1]]
    tpdBody [cellA C pa, cellA C pb, BitVec.ofNat 64 0, BitVec.ofNat 64 ds.length, cellA C pp,
      BitVec.ofNat 64 pfvs.length, Enc.idxW ms0.cvT.name, Enc.idxW bl, Enc.idxW x, BitVec.ofNat 64 (pfvs.length + 1)]
    (by decide) rfl (by decide) hc.tpd.self
    ⟨by simp +decide [sev, Env.get_cons, Env.get, tccParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tccParams, ctxEnv],
      rfl, by simp +decide [sev, Env.get_cons, Env.get, tccParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tccParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, tccParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, tccParams, ctxEnv],
      by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons, Env.get, tccParams, ctxEnv]; exact word_add1_eq _, trivial⟩
    (PostB (ctxH C H2)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tpdParams _ rfl hlk)
      (tpd_spec mode ra C hok hs hc.tpd (pfvs.length + 1) (by omega) ms0.cvT.name bl x pfvs ds eds pp pa pb hle.symm hdl
        hpl H0 hp0 hpf hA hB ds.length 0 H2 s3 (by omega) (by omega) hp2'))
    (fun b w s4 H4 hp4 hw => ?_)
  subst hw
  exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨H4, hp2'.trans hp4, rfl,
    sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
