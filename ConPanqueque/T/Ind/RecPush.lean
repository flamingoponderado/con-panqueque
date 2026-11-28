import ConPanqueque.T.Ind.RecRules
import ConPanqueque.T.Ind.RecTys
import ConPanqueque.T.Ind.FeR
import ConPanqueque.T.Decl.FeSwitch

/-!
# The rule-less recursors pushed, every recursor's rules checked, the pushes undone

`gprBody`: recursor `i`'s rule-less record written and its name inserted (a name already present hangs), the
flags read, the rest pushed recursively, then the name undone and the flags read again; past the last recursor,
the flush entering the pushed environment and every recursor's rules (`classRecsRulesOk`, `crrBody`).  The
environment comes back as it was (the twin's `classFeR` pops, in reverse order).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

/-- `classFeR.go`'s environment does not read the recorded rows. -/
theorem classFeR_go_fst (p : BlockShape) : ∀ (l : List (IConstantVal × Nat)) (m : Nat) (fe : IFEnv)
    (prevs prevs' : List (NIdx × Option IConstantInfo)),
    (classFeR.go p m l fe prevs).1 = (classFeR.go p m l fe prevs').1
  | [], _, _, _, _ => rfl
  | (cv, _) :: rest, m, fe, prevs, prevs' => by
    simp only [classFeR.go]
    exact classFeR_go_fst p rest (m + 1) _ _ _

/-- The recursor `classFeR` pushes for recursor `i`. -/
def feRCiAt (p : BlockShape) (cv : IConstantVal) (i : Nat) : IConstantInfo :=
  .recInfo cv (p.majorIdxAt i) (p.rulePrefixAt i) false []

/-- The rules phase from recursor `i` on: the pushes left, the flush, every recursor's rules. -/
def gprM (mode : ConLeche.CheckMode) (p : BlockShape) (g : ClassGen) (recCls : List Nat) (cvGs : List IConstantVal)
    (pushed : List NIdx) (i : Nat) (fe : IFEnv) : AM (List (IConstantVal × TargetMajor × List EIdx)) := do
  flushCaches
  classRecsRulesOk mode (classFeR.go p i ((cvGs.zip recCls).drop i) fe []).1 pushed g recCls cvGs cvGs recCls

theorem gprM_succ (mode : ConLeche.CheckMode) (p : BlockShape) (g : ClassGen) (recCls : List Nat)
    (cvGs : List IConstantVal) (pushed : List NIdx) (i : Nat) (fe : IFEnv) (hi : i < cvGs.length)
    (hic : i < recCls.length) :
    gprM mode p g recCls cvGs pushed i fe = gprM mode p g recCls cvGs pushed (i + 1) (fe.push (feRCiAt p cvGs[i] i)) := by
  unfold gprM
  rw [List.drop_eq_getElem_cons (show i < (cvGs.zip recCls).length by simp; omega)]
  simp only [List.getElem_zip, classFeR.go]
  rw [classFeR_go_fst p _ (i + 1) _ _ []]
  rfl

theorem gprM_end (mode : ConLeche.CheckMode) (p : BlockShape) (g : ClassGen) (recCls : List Nat)
    (cvGs : List IConstantVal) (pushed : List NIdx) (fe : IFEnv) :
    gprM mode p g recCls cvGs pushed cvGs.length fe = (do
      flushCaches
      classRecsRulesOk mode fe pushed g recCls cvGs cvGs recCls) := by
  unfold gprM
  rw [List.drop_eq_nil_of_le (by simp)]
  rfl

def gpCv := ofString "gp_cv"
def gpRl := ofString "gp_rl"
def gpI := ofString "gp_i"
def gpN := ofString "gp_n"
def gpOc := ofString "gp_oc"
def gpCss := ofString "gp_css"
def gpOms := ofString "gp_oms"
def gpRp := ofString "gp_rp"
def gpNp := ofString "gp_np"
def gpPm := ofString "gp_pm"
def gpSl := ofString "gp_sl"
def gpPr := ofString "gp_pr"
def gpN0 := ofString "gp_n0"
def gpPn := ofString "gp_pn"
def gpPl := ofString "gp_pl"
def gpRnb := ofString "gp_rnb"
def gpT := ofString "gp_t"
def gpQ := ofString "gp_q"
def gpNm := ofString "gp_nm"
def gpY := ofString "gp_y"
def gpRb := ofString "gp_rb"
def gpRr := ofString "gp_rr"
def gpMi := ofString "gp_mi"
def gpRq := ofString "gp_rq"
def gpX := ofString "gp_x"
def gpRi := ofString "gp_ri"
def gpFl := ofString "gp_fl"
def gpR := ofString "gp_r"
def fGpr := ofString "genRulesPush"

def gprParams : List MlS := [gpCv, gpRl, gpI, gpN, gpOc, gpCss, gpOms, gpRp, gpNp, gpPm, gpSl, gpPr, gpN0, gpPn, gpPl,
  gpRnb]
def gprLocals : List MlS := [gpT, gpQ, gpNm, gpY, gpRb, gpRr, gpMi, gpRq, gpX, gpRi, gpFl, gpR, lJ0]

/-- Recursor `i` pushed, the rest recursively, the push undone. -/
def gprStep (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local gpQ (.load .one (.op .add [vv gpCv, .op .add [.panop .mul [vv gpI, .const 8], .const 8]])))
  (.seq (.assign .local gpNm (.load .one (vv gpQ)))
  (envFindP C gpY (vv gpNm)
  (.ite (.cmp .notEqual (vv gpY) (.const 0)) hang
  (envRecP C gpRb [.const 0]
  (.seq (.assign .local gpRr (.load .one (.op .add [vv gpRl, .op .add [.panop .mul [vv gpI, .const 8], .const 8]])))
  (.seq (.assign .local gpMi (.load .one (.op .add [vv gpRr, .const 16])))
  (.seq (.assign .local gpRq (.load .one (.op .add [vv gpRr, .const 8])))
  (.seq (.call (some (some (.local, gpX), none)) fConstRec
      [vv gpQ, .const 5, vv gpMi, vv gpRq, .const 0, vv gpRb, .const 0, .const 0])
  (idxInsP C (vv gpNm) (vv gpX) gpRi
  (.seq (.call (some (some (.local, gpFl), none)) fFlags [])
  (.seq (.call (some (some (.local, gpR), none)) fGpr
      [vv gpCv, vv gpRl, .op .add [vv gpI, .const 1], vv gpN, vv gpOc, vv gpCss, vv gpOms, vv gpRp, vv gpNp, vv gpPm,
        vv gpSl, vv gpPr, vv gpN0, vv gpPn, vv gpPl, vv gpRnb])
  (undoCode (C.mg .env) (vv gpNm)
  (.seq (.call (some (some (.local, gpFl), none)) fFlags [])
  (.return (vv gpR)))))))))))))))

def gprBody (C : Ctx) : ProgHOL 64 := prologue gprLocals
  (.ite (.cmp .lower (vv gpI) (vv gpN))
    (.seq (.assign .local gpT (.load .one (vv gpOc)))
    (.ite (.cmp .lower (vv gpI) (vv gpT))
      (.seq (.assign .local gpT (.load .one (vv gpRl)))
      (.ite (.cmp .lower (vv gpI) (vv gpT))
        (gprStep C)
        hang))
      hang))
    (flushCode C (flushRegions false)
    (.seq (.call (some (some (.local, gpR), none)) fCrr
      [vv gpCv, .const 0, vv gpN, vv gpOc, vv gpCss, vv gpOms, vv gpRp, vv gpNp, vv gpPm, vv gpSl, vv gpPr, vv gpN0,
        vv gpPn, vv gpPl, vv gpRnb])
    (.return (vv gpR)))))

structure GPRCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  csc : CSCCodes C
  crr : CRRCodes mode C
  self : C.code.lookup fGpr = some (gprParams.map (fun p => (p, ShapeHOL.one)), gprBody C, .one)

section
variable {σ : Type}

theorem gpr_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ gprLocals → (ctxEnv C ++ gprParams.zip vals).get x = none :=
  Knot.params_none C gprLocals gprParams vals (by decide) (by decide)

/-- Back at the entry environment (heaps grown, the constant map answering alike), with the output list. -/
def PostGP (C : Ctx) (out : List (IConstantVal × TargetMajor × List EIdx)) (w : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  ∃ EH envM H o, C.EH <+: EH ∧ C.H <+: H ∧ (∀ n : NIdx, envM[n]? = C.envM[n]?) ∧
    CtxOK (ctxNew C C.fe EH envM H) ∧ SR (ctxNew C C.fe EH envM H) s' st ∧ w = cellA C o ∧
    PRep C H o (fun H o t => RRRep C H o t) out

theorem postGP_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostGP C a w s' st → PostGP C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨EH, envM, H, o, h1, h2, h3, h4, h5, h6⟩ =>
    ⟨EH, envM, H, o, h1, h2, h3, h4, sr_of_eq h5 rfl rfl rfl rfl, h6⟩

set_option maxHeartbeats 64000000 in
/-- **The pushes from recursor `i` on, the rules, the pops** (`gprM`), the context's environment the one with
recursors `0 … i-1` pushed. -/
theorem gpr_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions)
    (p : BlockShape) (g : ClassGen) (recCls : List Nat) (cvGs : List IConstantVal) (pushed : List NIdx)
    (rns : List NIdx) (hrns : ∀ t (ht : t < rns.length), classRecOf recCls cvGs t = some rns[t])
    (hpml : g.params.length < 2 ^ 56) (hsl : g.slots.length < 2 ^ 56)
    (hcb : ∀ sl ∈ g.slots, ∀ c C' ihs, sl = .minor c C' ihs → c < 2 ^ 63)
    (hprl : g.pre.length < 2 ^ 56) (hnP : g.nP < 2 ^ 56) (hpsl : pushed.length < 2 ^ 59)
    (hlen : ∀ cv ∈ cvGs, cv.levelParams.length < 2 ^ 59) (hrcb : ∀ c ∈ recCls, c < 2 ^ 63)
    (hxb : ∀ xs ∈ g.ctors, xs.length < 2 ^ 58 ∧ ∀ x ∈ xs, x.nF < 2 ^ 56)
    (ocv orl orc ocss oms opm os opr pn prn : Nat) :
    ∀ f i (C : Ctx) (s : AState), cvGs.length - i = f → i ≤ cvGs.length → CtxOK C → C.side = false →
      C.saved = none → GPRCodes mode C → TblGate C.fe → FlagsOK C.fe → LitsPinned C.fe C.pins →
      (∀ cv ∈ cvGs, CVDen cv C.St) →
      (∀ cv ∈ cvGs, ∃ ks : List ConLeche.Name, ∃ _ : ks.length = cv.levelParams.length,
        ∀ j (hj : j < cv.levelParams.length), denoteN C.St.ns cv.levelParams[j] = some (ks[j]'(by omega))) →
      PRep C C.H ocv (fun H o cv => CVRep C H o cv) cvGs → PtrsRep C C.H orl (RecRep C C.H) p.recs →
      BlkAt C.H orc (recCls.map (BitVec.ofNat 64)) →
      PRep C C.H ocss (fun H o xs => PRep C H o (fun H o cc => CCRep C H o cc) xs) g.ctors →
      TMBlkR C C.H oms g.cls → BlkAt C.H opm (g.params.map Enc.idxW) → SlotBlk C C.H os g.slots →
      BlkAt C.H opr (g.pre.map Enc.idxW) → Elems C.H pn pushed → BlkAt C.H prn (rns.map Enc.idxW) →
      SpecR (σ := σ) (Pre C s (gprParams.zip [cellA C ocv, cellA C orl, BitVec.ofNat 64 i,
        BitVec.ofNat 64 cvGs.length, cellA C orc, cellA C ocss, cellA C oms, BitVec.ofNat 64 g.pre.length,
        BitVec.ofNat 64 g.nP, cellA C opm, cellA C os, cellA C opr, BitVec.ofNat 64 (g.nP + g.slots.length),
        cellA C pn, BitVec.ofNat 64 pushed.length, cellA C prn])) (gprBody C) s
        (gprM mode p g recCls cvGs pushed i C.fe) (PostGP C) := by
  intro f
  induction f with
  | zero =>
    intro i C s hf hi hok hs hpl hc hg hF hL hden hks hcv hR hRC hcss hT hpm hsb hpr hpn hrnb
    have hin : i = cvGs.length := by omega
    subst hin
    refine specR_prologue (postGP_locals _) (gpr_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hcvl := blk_len_lt hok hHN hcv.choose_spec.2.1
    simp only [List.length_map, hcv.choose_spec.1] at hcvl
    have hlw := nd_lt_iff cvGs.length cvGs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, gprParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [gprM_end]
    refine specR_flushTopI hok hpl false flushCaches rfl (by decide) ?_
    refine specR_congr (m' := _ >>= fun r => pure r) (by rw [bind_pure]) ?_
    refine specR_callNIH (C := C) gpR fCrr crrParams
      [vv gpCv, .const 0, vv gpN, vv gpOc, vv gpCss, vv gpOms, vv gpRp, vv gpNp, vv gpPm, vv gpSl, vv gpPr, vv gpN0,
        vv gpPn, vv gpPl, vv gpRnb] (crrBody C)
      [cellA C ocv, BitVec.ofNat 64 0, BitVec.ofNat 64 cvGs.length, cellA C orc, cellA C ocss, cellA C oms,
        BitVec.ofNat 64 g.pre.length, BitVec.ofNat 64 g.nP, cellA C opm, cellA C os, cellA C opr,
        BitVec.ofNat 64 (g.nP + g.slots.length), cellA C pn, BitVec.ofNat 64 pushed.length, cellA C prn]
      (by decide) rfl (by decide) hc.crr.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv], rfl,
        by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv], trivial⟩
      (PostOut C) (fun out w _ H' => ∃ o, w = cellA C o ∧ PRep C H' o (fun H o t => RRRep C H o t) out)
      (fun out w s' st ⟨H', o, hp', hw, hr, hsr⟩ => ⟨H', hp', ⟨o, hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu crrParams _ rfl hlk)
        (by
          have h := crr_spec (σ := σ) mode ra C hok hs hpl hc.crr g recCls cvGs oms hT rns prn hrns opm hpm hpml os hsb
            hsl hcb opr hpr hprl hnP pushed pn hpsl ocv hcv hlen hks orc hRC hrcb ocss hcss hxb (cvGs.length - 0) 0 C.H
            (flushedS false s) rfl (Nat.zero_le _) (List.prefix_refl _) hpn hrnb
          simp only [List.drop_zero] at h
          exact h))
      (fun out w s1 H1 hp1 ⟨o, hw, hr⟩ => ?_)
    subst hw
    exact specR_returnI _ _ (by simp [sev, Env.get_cons]) (fun t ht => ⟨C.EH, C.envM, H1, o, List.prefix_refl _, hp1,
      fun _ => rfl, ctxOK_H hok H1, sr_of_eq ht.sr rfl rfl rfl rfl, rfl, hr⟩)
  | succ f ih =>
    intro i C s hf hi hok hs hpl hc hg hF hL hden hks hcv hR hRC hcss hT hpm hsb hpr hpn hrnb
    have hin : i < cvGs.length := by omega
    refine specR_prologue (postGP_locals _) (gpr_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : C.H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    obtain ⟨ovs, hovl, hovb, hovr⟩ := id hcv
    have hcvl := blk_len_lt hok hHN' hovb
    simp only [List.length_map] at hcvl
    have hlw := nd_lt_iff i cvGs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, gprParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin]) (fun _ => ?_) (fun h => absurd h (by decide))
    have hrc0 := hRC.1
    simp only [List.length_map] at hrc0
    refine UD.specR_heapLoadI' (C := C) gpT (vv gpOc) orc _ hrc0 (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, gprParams, ctxEnv] <;> rfl) ?_
    have hrcl : recCls.length < 2 ^ 61 := by
      have := blk_len_lt hok hHN' hRC; simp at this; omega
    have hlw2 := nd_lt_iff i recCls.length (by omega) (by omega)
    by_cases hic : i < recCls.length
    swap
    · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, gprParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, gprParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw2.mpr hic]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine UD.specR_heapLoadI' (C := C) gpT (vv gpRl) orl _ hR.1 (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, gprParams, ctxEnv] <;> rfl) ?_
    have hrsl := ptrsRep_len_lt hok hHN' hR
    have hlw3 := nd_lt_iff i p.recs.length (by omega) (by omega)
    by_cases hir : i < p.recs.length
    swap
    · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, gprParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, gprParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw3.mpr hir]) (fun _ => ?_) (fun h => absurd h (by decide))
    unfold gprStep
    rw [gprM_succ mode p g recCls cvGs pushed i C.fe hin hic]
    -- recursor `i`'s generated constant
    have hvi := hovb.2 i (by simp; omega)
    simp only [List.getElem_map] at hvi
    have hcvi : CVRep C C.H ovs[i] cvGs[i] := hovr i hin (by omega)
    have hmem := List.getElem_mem hin
    have hdi := hden _ hmem
    generalize hcvg : cvGs[i] = cvG at hcvi hdi
    generalize hqdef : ovs[i] = q at hvi hcvi
    refine UD.specR_heapLoadI' (C := C) gpQ _ (ocv + 1 + i) _ hvi (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, gprParams, ctxEnv]; exact cellA_mulIdx C ocv i (by omega)) ?_
    obtain ⟨hn0, ⟨wl, hwl, ol, hwlo, hebl⟩, hty⟩ := hcvi
    refine UD.specR_heapLoadI' (C := C) gpNm (vv gpQ) q _ hn0 (by decide) (by simp +decide [sev, Env.get_cons] <;> rfl) ?_
    -- the name must be new
    refine specR_envFindI hok hc.csc.k.g hc.csc.k.p gpY (vv gpNm) cvG.name (by decide) (by simp +decide [sev, Env.get_cons])
      (by simp +decide [Env.get_cons, Env.get, gprParams, ctxEnv]) ?_
    have hrel := find_rel hok cvG.name
    revert hrel
    rcases hfn : C.fe.find? cvG.name with _ | ci0
    swap
    · intro ⟨o', hm, hci⟩
      rw [hm]
      refine specR_atEntry fun t ht => ?_
      have hoE : o' < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
      exact specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
        (fun _ => specR_hangI) (fun h => absurd h (by decide))
    intro hrel
    simp only at hrel
    rw [hrel]
    refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    -- the empty rules block
    refine specR_envRecI hok gpRb [.const 0] [0] (by decide) rfl (by decide)
      (fun w j hj hj' => by rcases j with _ | j <;> simp at hj; rfl) (fun EH1 hp1 hl1 hv1 => ?_)
    have hok1 := ctxOK_E hok hp1
    have hrb : RulesE C.EB EH1 (ecell C C.EH.length) [] :=
      ⟨C.EH.length, rfl, by simpa using hv1 0 (by simp), fun i hi => absurd hi (by simp)⟩
    -- recursor `i`'s record
    obtain ⟨orr, horr, hrr⟩ := hR.2 i hir
    refine UD.specR_heapLoadI' (C := ctxE C EH1) gpRr _ (orl + 1 + i) _ horr (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, gprParams, ctxEnv]; exact cellA_mulIdx C orl i (by omega)) ?_
    obtain ⟨-, ⟨hrp, hrpb⟩, ⟨hmi, hmib⟩, -, -, -⟩ := hrr
    have hmaj : p.majorIdxAt i = p.recs[i].mI := by simp [BlockShape.majorIdxAt, List.getElem?_eq_getElem hir]
    have hrpe : p.rulePrefixAt i = p.recs[i].rP := by simp [BlockShape.rulePrefixAt, List.getElem?_eq_getElem hir]
    refine UD.specR_heapLoadI' (C := ctxE C EH1) gpMi _ (orr + 2) _ hmi (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C orr 2) ?_
    refine UD.specR_heapLoadI' (C := ctxE C EH1) gpRq _ (orr + 1) _ hrp (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C orr) ?_
    set ci : IConstantInfo := feRCiAt p cvG i with hci
    have hcin : ci.name = cvG.name := rfl
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => _) (by rw [pure_bind]) ?_
    refine specR_callNC (C := ctxE C EH1) (D := ctxLocals ++ gprLocals) gpX fConstRec cwParams
      [vv gpQ, .const 5, vv gpMi, vv gpRq, .const 0, vv gpRb, .const 0, .const 0] (cwBody C)
      [cellA C q, 5, BitVec.ofNat 64 p.recs[i].mI, BitVec.ofNat 64 p.recs[i].rP, 0, ecell C C.EH.length, 0, 0]
      (by decide) rfl (by decide) hc.csc.cw ?_
      (PostCW (ctxE C EH1) cvG 5 [BitVec.ofNat 64 p.recs[i].mI, BitVec.ofNat 64 p.recs[i].rP, 0, ecell C C.EH.length, 0, 0] s)
      (fun _ w s' C' => s' = s ∧ ∃ EH2 ox, C' = ctxE (ctxE C EH1) EH2 ∧ EH1 <+: EH2 ∧ w = ecell C ox ∧ CIE C.EB EH2 ox ci)
      (fun _ w s' st ⟨hs', EH2, ox, hp2, _, hw, hcve, htg, hfs, hsr⟩ => by
        subst hs'
        exact ⟨_, ⟨rfl, EH2, ox, rfl, hp2, hw, hcve, htg,
          ⟨by simpa [hmaj] using hfs 0 (by simp), by rw [hmaj]; exact hmib⟩,
          ⟨by simpa [hrpe] using hfs 1 (by simp), by rw [hrpe]; exact hrpb⟩,
          by simpa [boolW] using hfs 2 (by simp), ecell C C.EH.length, by simpa using hfs 3 (by simp),
          rulesE_mono hp2 hrb⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cwParams _ rfl hlk)
        (cw_spec (ctxE C EH1) hok1 (by ctx_tr hc.csc.cp) cvG q ⟨hn0, ⟨_, hwl, ol, hwlo, hebl⟩, hty⟩
          (by have := hdi.2.2; omega) 5 _ _ _ _ _ _ s))
      (fun _ w s3 C3 ⟨hs3, EH2, ox, eC, hpE2, hw, hcie⟩ => ?_)
    · exact ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons],
        by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons], rfl, rfl, trivial⟩
    subst eC hw s3
    refine specR_atEntry fun t5 ht5 => ?_
    have hd5 : CVDen cvG s.store := cvDen_ext hdi ht5.sr.floor
    have hdn : NewDen ci s.store := by
      refine ⟨hd5.1, hd5.2.1, hd5.2.2, fun _ _ _ h => (by simp [hci, feRCiAt] at h), fun _ _ h => (by simp [hci, feRCiAt] at h)⟩
    refine specR_idxInsI' (C := ctxE C EH1) hok1 hc.csc.k.s hc.csc.k.i hg ci hfn
      (fun _ _ _ _ _ h => by simp only [hci, feRCiAt, IConstantInfo.recInfo.injEq] at h; exact h.2.2.2.2.symm) EH2 ox hpE2 hdn
      (vv gpNm) (vv gpX) gpRi (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) (by simp +decide [sev, Env.get_cons]; rfl)
      (by simp +decide [Env.get_cons, Env.get, gprParams, ctxEnv]; rfl) (fun wr2 => ?_)
    have hokI := ctxOK_ins hok1 hpE2 hcie (pushOld_find C.fe ci) (pushOld_findTable hg ci hfn)
    have hfP : ∀ n, (C.fe.push ci).find? n = (ctxIns (ctxE C EH1) ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit)
        EH2 (C.envM.insert ci.name (ecell C ox))).fe.find? n := fun n => (IFEnv.setFlags_find? _ _ _ n).symm
    have htP : ∀ n, (C.fe.push ci).findTable? n = (ctxIns (ctxE C EH1) ((C.fe.push ci).setFlags C.fe.natLit
        C.fe.strLit) EH2 (C.envM.insert ci.name (ecell C ox))).fe.findTable? n := fun n => by
      show _ = ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit).findTable? n
      unfold IFEnv.findTable?; rw [IFEnv.setFlags_find?, IFEnv.setFlags_rawTable?]
    obtain ⟨hfn', hfs'⟩ := push_flags_found (C := ctxE C EH1) hF hL ci ox EH2
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => _) (by rw [pure_bind]) ?_
    refine specR_callNC (C := ctxIns (ctxE C EH1) ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit) EH2
        (C.envM.insert ci.name (ecell C ox))) (D := ctxLocals ++ gprLocals) gpFl fFlags [] [] Decl.flBody []
      (by decide) rfl (by decide) hc.csc.flags trivial
      (fun a w s' st => PostFl (ctxIns (ctxE C EH1) ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit) EH2
        (C.envM.insert ci.name (ecell C ox))) (C.fe.push ci) a w s' st ∧ s' = s)
      (fun _ w s' C' => s' = s ∧ ∃ H6, C' = ctxFe (ctxH (ctxIns (ctxE C EH1) ((C.fe.push ci).setFlags C.fe.natLit
        C.fe.strLit) EH2 (C.envM.insert ci.name (ecell C ox))) H6) (C.fe.push ci) ∧ C.H <+: H6)
      (fun a w s' st ⟨⟨H6, hp6, hsr⟩, hs'⟩ => ⟨_, ⟨hs', H6, rfl, hp6⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [] _ rfl hlk)
        (specR_pureState (fl_spec _ hokI (by ctx_tr hc.csc.natF) (by ctx_tr hc.csc.strF) (by ctx_tr hc.csc.k.g)
          (by ctx_tr hc.csc.k.p) s hfP htP hfn' hfs')))
      (fun _ w s5 C5 ⟨hs5, H6, eC, hp6⟩ => ?_)
    subst eC s5
    have hokF := ctxOK_fe (ctxOK_H hokI H6) (fe := C.fe.push ci) (fun n => hfP n) (fun n => htP n)
    have hpC6 : C.H <+: H6 := hp6
    set C' := ctxFe (ctxH (ctxIns (ctxE C EH1) ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit) EH2
        (C.envM.insert ci.name (ecell C ox))) H6) (C.fe.push ci) with hC'
    -- the rest, recursively
    refine specR_congr (m' := _ >>= fun r => pure r) (by rw [bind_pure]) ?_
    refine specR_callNC (C := C') (D := ctxLocals ++ gprLocals) gpR fGpr gprParams
      [vv gpCv, vv gpRl, .op .add [vv gpI, .const 1], vv gpN, vv gpOc, vv gpCss, vv gpOms, vv gpRp, vv gpNp, vv gpPm,
        vv gpSl, vv gpPr, vv gpN0, vv gpPn, vv gpPl, vv gpRnb] (gprBody C)
      [cellA C ocv, cellA C orl, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 cvGs.length, cellA C orc, cellA C ocss,
        cellA C oms, BitVec.ofNat 64 g.pre.length, BitVec.ofNat 64 g.nP, cellA C opm, cellA C os, cellA C opr,
        BitVec.ofNat 64 (g.nP + g.slots.length), cellA C pn, BitVec.ofNat 64 pushed.length, cellA C prn]
      (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv], trivial⟩
      (PostGP C')
      (fun out w s' C'' => ∃ EH3 envM3 H3 o, C'' = ctxNew C' C'.fe EH3 envM3 H3 ∧ C'.EH <+: EH3 ∧ C'.H <+: H3 ∧
        (∀ n : NIdx, envM3[n]? = C'.envM[n]?) ∧ CtxOK (ctxNew C' C'.fe EH3 envM3 H3) ∧ w = cellA C o ∧
        PRep C H3 o (fun H o t => RRRep C H o t) out)
      (fun out w s' st ⟨EH3, envM3, H3, o, h1, h2, h3, h4, h5, h6⟩ => ⟨_, ⟨EH3, envM3, H3, o, rfl, h1, h2, h3, h4, h6⟩, h5⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu gprParams _ rfl hlk)
        (ih (i + 1) C' s (by omega) (by omega) hokF hs hpl (by ctx_tr hc) (TblGate.push hg ci) (hF.push ci)
          (by show LitsPinned (C.fe.push ci) C.pins; unfold LitsPinned; rw [IFEnv.push_base]; exact hL) hden hks
          (pRep_mono hpC6 (fun _ _ => cvRep_mono hpC6) hcv) (ptrsRep_mono hpC6 (fun _ _ => recRep_mono hpC6) hR)
          (blkAt_mono hRC hpC6) (pRep_mono hpC6 (fun _ _ h => pRep_mono hpC6 (fun _ _ => ccRep_mono hpC6) h) hcss)
          (tmBlkR_mono hpC6 hT) (blkAt_mono hpm hpC6) (slotBlk_mono hpC6 hsb) (blkAt_mono hpr hpC6)
          (fun j hj => get_prefix (hpn j hj) hpC6) (blkAt_mono hrnb hpC6)))
      (fun out w s8 C8 ⟨EH3, envM3, H3, o, eC, hpE3, hp3, hm3, hok3, hw, hout⟩ => ?_)
    subst eC hw
    have hp3' : H6 <+: H3 := hp3
    -- the push undone
    refine specR_atEntry fun t8 ht8 => ?_
    have hden8 : EnvDen (feMid C.fe ci) C.pins s8.store := by
      refine envDen_sub (fe := C.fe.push ci) (fun n ci' h => ?_) (fun n => by rw [feMid_findTable, push_findTable hg ci hfn])
        ht8.sr.envd
      rw [feMid_find] at h
      rw [IFEnv.find?_push]
      by_cases hb : (ci.name == n) = true
      · have : cvG.name = n := by simpa [hcin] using hb
        subst this; rw [hfn] at h; cases h
      · rw [if_neg hb]; exact h
    refine specR_envUndoI (C := ctxNew C' C'.fe EH3 envM3 H3) hok3 cvG.name (feMid C.fe ci) rfl hden8 (vv gpNm)
      (by simp +decide [sev, Env.get_cons, Env.get, Env.kill, gprParams, ctxEnv]) (by decide) ?_
    have hm : ∀ n : NIdx, (envM3.erase cvG.name)[n]? = C.envM[n]? := by
      intro n
      rw [Std.HashMap.getElem?_erase, hm3 n, hC']
      by_cases h : cvG.name = n
      · subst h; simp [hrel]
      · simp only [ctxFe, ctxH, ctxIns, Std.HashMap.getElem?_insert]
        simp [hcin, h]
    have hEH : C.EH <+: EH3 := hp1.trans (hpE2.trans hpE3)
    have hokV : CtxOK (ctxIns (ctxH C H3) (feMid C.fe ci) EH3 (envM3.erase cvG.name)) :=
      ctxOK_insEq (ctxOK_H hok H3) hEH (feMid_find _ _) (feMid_findTable _ _) hm
    set fe2 := (feMid C.fe ci).setFlags C.fe.natLit C.fe.strLit with hfe2
    have hfV : ∀ n, fe2.find? n = (ctxIns (ctxH C H3) (feMid C.fe ci) EH3 (envM3.erase cvG.name)).fe.find? n :=
      fun n => IFEnv.setFlags_find? _ _ _ n
    have htV : ∀ n, fe2.findTable? n = (ctxIns (ctxH C H3) (feMid C.fe ci) EH3 (envM3.erase cvG.name)).fe.findTable? n :=
      fun n => by
        show (feMid C.fe ci |>.setFlags C.fe.natLit C.fe.strLit).findTable? n = (feMid C.fe ci).findTable? n
        unfold IFEnv.findTable?; rw [IFEnv.setFlags_find?, IFEnv.setFlags_rawTable?]
    have hnV : fe2.natLit = pinsFound (ctxIns (ctxH C H3) (feMid C.fe ci) EH3 (envM3.erase cvG.name)) natPins := by
      show C.fe.natLit = _
      rw [hF.nat, natLitStoredBy_pins hL]
      unfold pinsFound ctxIns
      simp only [feMid_find]; rfl
    have hsV : fe2.strLit = pinsFound (ctxIns (ctxH C H3) (feMid C.fe ci) EH3 (envM3.erase cvG.name)) strPins := by
      show C.fe.strLit = _
      rw [hF.str, strLitStoredBy_pins hL]
      unfold pinsFound ctxIns
      simp only [feMid_find]; rfl
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => _) (by rw [pure_bind]) ?_
    refine specR_callNC (C := ctxIns (ctxH C H3) (feMid C.fe ci) EH3 (envM3.erase cvG.name))
      (D := ctxLocals ++ gprLocals) gpFl fFlags [] [] Decl.flBody []
      (by decide) rfl (by decide) hc.csc.flags trivial
      (fun a w s' st => PostFl (ctxIns (ctxH C H3) (feMid C.fe ci) EH3 (envM3.erase cvG.name)) fe2 a w s' st ∧ s' = s8)
      (fun _ w s' C' => s' = s8 ∧ ∃ H9, C' = ctxFe (ctxH (ctxIns (ctxH C H3) (feMid C.fe ci) EH3
        (envM3.erase cvG.name)) H9) fe2 ∧ H3 <+: H9)
      (fun a w s' st ⟨⟨H9, hp9, hsr⟩, hs'⟩ => ⟨_, ⟨hs', H9, rfl, hp9⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [] _ rfl hlk)
        (specR_pureState (fl_spec _ hokV (by ctx_tr hc.csc.natF) (by ctx_tr hc.csc.strF) (by ctx_tr hc.csc.k.g)
          (by ctx_tr hc.csc.k.p) s8 hfV htV hnV hsV)))
      (fun _ w s9 C9 ⟨hs9, H9, eC, hp9⟩ => ?_)
    subst eC s9
    have hp9' : H3 <+: H9 := hp9
    -- back at the entry environment
    refine specR_atEntry fun t9 ht9 => ?_
    have hfE : ∀ n, C.fe.find? n = fe2.find? n := fun n => (fe2_find C.fe ci n).symm
    have htE : ∀ n, C.fe.findTable? n = fe2.findTable? n := fun n => (fe2_findTable C.fe ci n).symm
    refine specR_feI (fe := C.fe) rfl (envDen_congr hfE htE ht9.sr.envd) ?_
    exact specR_returnI _ _ (by simp +decide [sev, Env.get_cons, Env.kill]) (fun t ht => ⟨EH3, envM3.erase cvG.name, H9, o, hEH,
      hpC6.trans (hp3'.trans hp9'), hm,
      ctxOK_fe (ctxOK_H hokV H9) (fe := C.fe) (fun n => (feMid_find C.fe ci n).symm)
        (fun n => (feMid_findTable C.fe ci n).symm),
      sr_of_eq ht.sr rfl rfl rfl rfl, rfl, pRep_mono hp9' (fun _ _ => rrRep_mono hp9') hout⟩)

end

end ConPanqueque.T.Ind
