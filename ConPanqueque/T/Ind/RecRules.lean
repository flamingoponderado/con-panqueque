import ConPanqueque.T.Ind.RuleCheck

/-!
# `classRecsRulesOk`: every recursor's generated rules

`crrBody`: a loop over the generated recursor constants (a block of pointers to their records) and the recursors'
classes (a word block): recursor `i` at class `c = recCls[i]` checks its rules (`classRulesOk`, `crlBody`) over class
`c`'s constructors (the block-of-blocks `css`), and contributes the record `[rules block, constant, class c's record]`.
The walk stops (an empty block) when either list runs out, as the twin's zip does.  A class past the constructor
block-of-blocks or past the class block hangs.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

/-- One output triple `(cv, m, rhss)` at `o`: `[rules block, constant record, class record]`. -/
def RRRep (C : Ctx) (H : List (BitVec 64)) (o : Nat) (t : IConstantVal × TargetMajor × List EIdx) : Prop :=
  ∃ orh oc om, H[o]? = some (cellA C orh) ∧ BlkAt H orh (t.2.2.map Enc.idxW) ∧ H[o + 1]? = some (cellA C oc) ∧
    CVRep C H oc t.1 ∧ H[o + 2]? = some (cellA C om) ∧ TMRep C H om t.2.1

theorem rrRep_mono {C : Ctx} {H H' : List (BitVec 64)} (hp : H <+: H') {o : Nat}
    {t : IConstantVal × TargetMajor × List EIdx} (h : RRRep C H o t) : RRRep C H' o t :=
  let ⟨orh, oc, om, a, b, c, d, e, f⟩ := h
  ⟨orh, oc, om, get_prefix a hp, blkAt_mono b hp, get_prefix c hp, cvRep_mono hp d, get_prefix e hp, tmRep_mono hp f⟩

theorem classRecsRulesOk_nil_right (mode : ConLeche.CheckMode) (feR : IFEnv) (pushed : List NIdx) (g : ClassGen)
    (recCls : List Nat) (cvGs : List IConstantVal) (l : List IConstantVal) :
    classRecsRulesOk mode feR pushed g recCls cvGs l [] = pure [] := by
  cases l <;> rfl

def crrCv := ofString "crr_cv"
def crrI := ofString "crr_i"
def crrN := ofString "crr_n"
def crrOc := ofString "crr_oc"
def crrCss := ofString "crr_css"
def crrOms := ofString "crr_oms"
def crrRp := ofString "crr_rp"
def crrNp := ofString "crr_np"
def crrPm := ofString "crr_pm"
def crrSl := ofString "crr_sl"
def crrPr := ofString "crr_pr"
def crrN0 := ofString "crr_n0"
def crrPn := ofString "crr_pn"
def crrPl := ofString "crr_pl"
def crrRnb := ofString "crr_rnb"
def crrQ := ofString "crr_q"
def crrC := ofString "crr_c"
def crrV := ofString "crr_v"
def crrXs := ofString "crr_xs"
def crrK := ofString "crr_k"
def crrM := ofString "crr_m"
def crrLp := ofString "crr_lp"
def crrLn := ofString "crr_ln"
def crrRs := ofString "crr_rs"
def crrT := ofString "crr_t"
def fCrr := ofString "classRecsRulesOk"

def crrParams : List MlS := [crrCv, crrI, crrN, crrOc, crrCss, crrOms, crrRp, crrNp, crrPm, crrSl, crrPr, crrN0, crrPn,
  crrPl, crrRnb]
def crrLocals : List MlS := gaaLocals ++ [crrQ, crrC, crrV, crrXs, crrK, crrM, crrLp, crrLn, crrRs, crrT]

/-- The empty block. -/
def crrNil (C : Ctx) : ProgHOL 64 := alloc1 C lW (.const 0) (.return (vv lW))

def crrStep (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local crrV (.load .one (.op .add [vv crrCv, .op .add [.panop .mul [vv crrI, .const 8], .const 8]])))
  (.seq (.assign .local crrXs (.load .one (.op .add [vv crrCss, .op .add [.panop .mul [vv crrC, .const 8], .const 8]])))
  (.seq (.assign .local crrK (.load .one (vv crrXs)))
  (.seq (.assign .local crrM (.load .one (.op .add [vv crrOms, .op .add [.panop .mul [vv crrC, .const 8], .const 8]])))
  (.seq (.assign .local crrLp (.load .one (.op .add [vv crrV, .const 8])))
  (.seq (.assign .local crrLn (.load .one (vv crrLp)))
  (.seq (.call (some (some (.local, crrRs), none)) fCrl
      [vv crrXs, .const 0, vv crrK, vv crrRp, vv crrNp, vv crrPm, vv crrSl, vv crrPr, vv crrLp, vv crrLn, vv crrN0,
        vv crrPn, vv crrPl, vv crrOms, vv crrRnb, vv crrC])
  (.seq (.call (some (some (.local, ExS.lY), none)) fCrr
      [vv crrCv, .op .add [vv crrI, .const 1], vv crrN, vv crrOc, vv crrCss, vv crrOms, vv crrRp, vv crrNp, vv crrPm,
        vv crrSl, vv crrPr, vv crrN0, vv crrPn, vv crrPl, vv crrRnb])
  (alloc3 C crrT (vv crrRs) (vv crrV) (vv crrM)
  (prependP C crrT)))))))))

def crrBody (C : Ctx) : ProgHOL 64 := prologue crrLocals
  (.ite (.cmp .lower (vv crrI) (vv crrN))
    (.seq (.assign .local crrQ (.load .one (vv crrOc)))
    (.ite (.cmp .lower (vv crrI) (vv crrQ))
      (.seq (.assign .local crrC (.load .one (.op .add [vv crrOc, .op .add [.panop .mul [vv crrI, .const 8], .const 8]])))
      (.seq (.assign .local crrQ (.load .one (vv crrCss)))
      (.ite (.cmp .lower (vv crrC) (vv crrQ))
        (.seq (.assign .local crrQ (.load .one (vv crrOms)))
        (.ite (.cmp .lower (vv crrC) (vv crrQ))
          (crrStep C)
          hang))
        hang)))
      (crrNil C)))
    (crrNil C))

structure CRRCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  crl : CRLCodes mode C
  self : C.code.lookup fCrr = some (crrParams.map (fun p => (p, ShapeHOL.one)), crrBody C, .one)

section
variable {σ : Type}

theorem crr_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ crrLocals → (ctxEnv C ++ crrParams.zip vals).get x = none :=
  Knot.params_none C crrLocals crrParams vals (by decide) (by decide)

/-- The output list, as a block of pointers to triples. -/
def PostOut (C : Ctx) (out : List (IConstantVal × TargetMajor × List EIdx)) (w : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  ∃ H' o, C.H <+: H' ∧ w = cellA C o ∧ PRep C H' o (fun H o t => RRRep C H o t) out ∧ SR (ctxH C H') s' st

theorem postOut_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostOut C a w s' st → PostOut C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, h1, h2, h3, h4⟩ => ⟨H', o, h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl⟩

theorem crrNil_spec {C : Ctx} (hok : CtxOK C) {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem}
    (hD : lW ∈ ctxLocals ++ crrLocals) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ crrLocals)) (crrNil C) s
      (pure ([] : List (IConstantVal × TargetMajor × List EIdx))) (PostOut (ctxH C H)) := by
  unfold crrNil
  refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 hD (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
  have hg : ((H2 ++ ws).set H2.length (0 : BitVec 64))[H2.length]? = some 0 := List.getElem?_set_self (by simp [hws])
  have hpr' : H2 <+: (H2 ++ ws).set H2.length (0 : BitVec 64) := prefix_set (List.prefix_append _ _) (Nat.le_refl _) _
  exact specR_returnI _ (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨_, H2.length,
    (hp2 : H <+: H2).trans hpr', rfl, ⟨[], rfl, ⟨by simpa using hg, fun i hi => absurd hi (by simp)⟩,
      fun i hi => absurd hi (by simp)⟩, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

set_option maxHeartbeats 32000000 in
/-- **`classRecsRulesOk`** from recursor `i` on, at the context's environment. -/
theorem crr_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hpl : C.saved = none) (hc : CRRCodes mode C)
    (g : ClassGen) (recCls : List Nat) (cvGs : List IConstantVal)
    (oms : Nat) (hT : TMBlkR C C.H oms g.cls)
    (rns : List NIdx) (prn : Nat)
    (hrns : ∀ t (ht : t < rns.length), classRecOf recCls cvGs t = some rns[t])
    (opm : Nat) (hpm : BlkAt C.H opm (g.params.map Enc.idxW)) (hpml : g.params.length < 2 ^ 56)
    (os : Nat) (hsb : SlotBlk C C.H os g.slots) (hsl : g.slots.length < 2 ^ 56)
    (hcb : ∀ sl ∈ g.slots, ∀ c C' ihs, sl = .minor c C' ihs → c < 2 ^ 63)
    (opr : Nat) (hpr : BlkAt C.H opr (g.pre.map Enc.idxW)) (hprl : g.pre.length < 2 ^ 56) (hnP : g.nP < 2 ^ 56)
    (pushed : List NIdx) (pn : Nat) (hpsl : pushed.length < 2 ^ 59)
    (ocv : Nat) (hcv : PRep C C.H ocv (fun H o cv => CVRep C H o cv) cvGs)
    (hlen : ∀ cv ∈ cvGs, cv.levelParams.length < 2 ^ 59)
    (hks : ∀ cv ∈ cvGs, ∃ ks : List ConLeche.Name, ∃ _ : ks.length = cv.levelParams.length,
      ∀ j (hj : j < cv.levelParams.length), denoteN C.St.ns cv.levelParams[j] = some (ks[j]'(by omega)))
    (orc : Nat) (hRC : BlkAt C.H orc (recCls.map (BitVec.ofNat 64))) (hrcb : ∀ c ∈ recCls, c < 2 ^ 63)
    (ocss : Nat) (hcss : PRep C C.H ocss (fun H o xs => PRep C H o (fun H o cc => CCRep C H o cc) xs) g.ctors)
    (hxb : ∀ xs ∈ g.ctors, xs.length < 2 ^ 58 ∧ ∀ x ∈ xs, x.nF < 2 ^ 56) :
    ∀ f i (H : List (BitVec 64)) (s : AState), cvGs.length - i = f → i ≤ cvGs.length → C.H <+: H → Elems H pn pushed →
      BlkAt H prn (rns.map Enc.idxW) →
      SpecR (σ := σ) (Pre (ctxH C H) s (crrParams.zip [cellA C ocv, BitVec.ofNat 64 i, BitVec.ofNat 64 cvGs.length,
        cellA C orc, cellA C ocss, cellA C oms, BitVec.ofNat 64 g.pre.length, BitVec.ofNat 64 g.nP, cellA C opm,
        cellA C os, cellA C opr, BitVec.ofNat 64 (g.nP + g.slots.length), cellA C pn, BitVec.ofNat 64 pushed.length,
        cellA C prn])) (crrBody C) s
        (classRecsRulesOk mode C.fe pushed g recCls cvGs (cvGs.drop i) (recCls.drop i)) (PostOut (ctxH C H)) := by
  obtain ⟨ovs, hovl, hovb, hovr⟩ := hcv
  obtain ⟨oxs, hoxl, hoxb, hoxr⟩ := hcss
  obtain ⟨ps, hpsL, hpsb, hpsr⟩ := hT
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp hpn hrnb
    have hin : i = cvGs.length := by omega
    subst hin
    refine specR_prologue (postOut_locals _) (crr_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hcvl := blk_len_lt hok (Nat.le_trans (List.IsPrefix.length_le hp) hHN) hovb
    simp only [List.length_map] at hcvl
    have hlw := nd_lt_iff cvGs.length cvGs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    simp only [classRecsRulesOk]
    exact crrNil_spec hok (by decide)
  | succ f ih =>
    intro i H s hf hi hp hpn hrnb
    have hin : i < cvGs.length := by omega
    refine specR_prologue (postOut_locals _) (crr_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hHC : C.H.length ≤ C.HN := Nat.le_trans (List.IsPrefix.length_le hp) hHN
    have hlay := hok.heapLay
    have hcvl := blk_len_lt hok hHC hovb
    simp only [List.length_map] at hcvl
    have hlw := nd_lt_iff i cvGs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv]; simp +decide [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin]) (fun _ => ?_) (fun h => absurd h (by decide))
    have hrc0 := get_prefix hRC.1 hp
    simp only [List.length_map] at hrc0
    refine UD.specR_heapLoadI' (C := ctxH C H) crrQ (vv crrOc) orc _ hrc0 (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv]; rfl) ?_
    have hrcl : recCls.length < 2 ^ 61 := by
      have := blk_len_lt hok hHC hRC; simp at this; omega
    have hlw2 := nd_lt_iff i recCls.length (by omega) (by omega)
    by_cases hic : i < recCls.length
    swap
    · refine specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, crrParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
        (fun h => absurd rfl h) (fun _ => ?_)
      rw [List.drop_eq_nil_of_le (by omega : recCls.length ≤ i), classRecsRulesOk_nil_right]
      exact crrNil_spec hok (by decide)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, crrParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw2.mpr hic]) (fun _ => ?_) (fun h => absurd h (by decide))
    have hci := hRC.2 i (by simp; omega)
    simp only [List.getElem_map] at hci
    have hcb63 := hrcb _ (List.getElem_mem hic)
    generalize hcdef : recCls[i] = c at hcb63 hci
    refine UD.specR_heapLoadI' (C := ctxH C H) crrC _ (orc + 1 + i) _ (get_prefix hci hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv]; exact cellA_mulIdx C orc i (by omega)) ?_
    have hxl0 := get_prefix hoxb.1 hp
    simp only [List.length_map, hoxl] at hxl0
    refine UD.specR_heapLoadI' (C := ctxH C H) crrQ (vv crrCss) ocss _ hxl0 (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv]; rfl) ?_
    have hcssl : g.ctors.length < 2 ^ 61 := by
      have := blk_len_lt hok hHC hoxb; simp at this; omega
    have hlw3 := nd_lt_iff c g.ctors.length (by omega) (by omega)
    by_cases hcc : c < g.ctors.length
    swap
    · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, crrParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, crrParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw3.mpr hcc]) (fun _ => ?_) (fun h => absurd h (by decide))
    have hml0 := get_prefix hpsb.1 hp
    simp only [List.length_map, hpsL] at hml0
    refine UD.specR_heapLoadI' (C := ctxH C H) crrQ (vv crrOms) oms _ hml0 (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv]; rfl) ?_
    have hclsl : g.cls.length < 2 ^ 61 := by
      have := blk_len_lt hok hHC hpsb; simp at this; omega
    have hlw4 := nd_lt_iff c g.cls.length (by omega) (by omega)
    by_cases hcm : c < g.cls.length
    swap
    · exact specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, crrParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega)
        (fun h => absurd rfl h) (fun _ => specR_hangI)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, crrParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw4.mpr hcm]) (fun _ => ?_) (fun h => absurd h (by decide))
    unfold crrStep
    -- the constant
    have hvi := hovb.2 i (by simp; omega)
    simp only [List.getElem_map] at hvi
    have hcvi : CVRep C C.H ovs[i] cvGs[i] := hovr i hin (by omega)
    refine UD.specR_heapLoadI' (C := ctxH C H) crrV _ (ocv + 1 + i) _ (get_prefix hvi hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv]; exact cellA_mulIdx C ocv i (by omega)) ?_
    -- class c's constructors
    have hxc := hoxb.2 c (by simp; omega)
    simp only [List.getElem_map] at hxc
    have hxsc : PRep C C.H oxs[c] (fun H o cc => CCRep C H o cc) g.ctors[c] := hoxr c hcc (by omega)
    refine UD.specR_heapLoadI' (C := ctxH C H) crrXs _ (ocss + 1 + c) _ (get_prefix hxc hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv]; exact cellA_mulIdx C ocss c (by omega)) ?_
    have hxk := get_prefix hxsc.choose_spec.2.1.1 hp
    simp only [List.length_map, hxsc.choose_spec.1] at hxk
    refine UD.specR_heapLoadI' (C := ctxH C H) crrK (vv crrXs) oxs[c] _ hxk (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    -- class c's record
    obtain ⟨op, hop, hrep⟩ := hpsr c hcm
    have hq := hpsb.2 c (by simp; omega)
    simp only [List.getElem_map] at hq
    have hpi : ps[c]'(by omega) = op := by
      rw [List.getElem?_eq_getElem (by omega)] at hop; exact Option.some.inj hop
    rw [hpi] at hq
    refine UD.specR_heapLoadI' (C := ctxH C H) crrM _ (oms + 1 + c) _ (get_prefix hq hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv]; exact cellA_mulIdx C oms c (by omega)) ?_
    -- the constant's level parameters
    obtain ⟨hn0, ⟨wl, hwl, ol, hwlo, hebl⟩, hty⟩ := hcvi
    subst hwlo
    have hbl : BlkAt C.H ol (cvGs[i].levelParams.map Enc.idxW) := hebl
    refine UD.specR_heapLoadI' (C := ctxH C H) crrLp _ (ovs[i] + 1) _ (get_prefix hwl hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C ovs[i]) ?_
    have hb1 := get_prefix hbl.1 hp
    simp only [List.length_map] at hb1
    refine UD.specR_heapLoadI' (C := ctxH C H) crrLn (vv crrLp) ol _ hb1 (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    rw [List.drop_eq_getElem_cons hin, List.drop_eq_getElem_cons hic]
    simp only [classRecsRulesOk, bind_assoc, hcdef, targetMajorAt, List.getElem?_eq_getElem hcm, pure_bind,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcc, Option.getD_some]
    have hmem := List.getElem_mem hin
    obtain ⟨ks, hkl, hks'⟩ := hks _ hmem
    have hxbc := hxb _ (List.getElem_mem hcc)
    refine specR_callNIH (C := ctxH C H) crrRs fCrl crlParams
      [vv crrXs, .const 0, vv crrK, vv crrRp, vv crrNp, vv crrPm, vv crrSl, vv crrPr, vv crrLp, vv crrLn, vv crrN0,
        vv crrPn, vv crrPl, vv crrOms, vv crrRnb, vv crrC] (crlBody C)
      [cellA C oxs[c], BitVec.ofNat 64 0, BitVec.ofNat 64 g.ctors[c].length, BitVec.ofNat 64 g.pre.length,
        BitVec.ofNat 64 g.nP, cellA C opm, cellA C os, cellA C opr, cellA C ol,
        BitVec.ofNat 64 cvGs[i].levelParams.length, BitVec.ofNat 64 (g.nP + g.slots.length), cellA C pn,
        BitVec.ofNat 64 pushed.length, cellA C oms, cellA C prn, BitVec.ofNat 64 c] (by decide) rfl (by decide)
      hc.crl.self
      ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons],
        by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv], by simp +decide [sev, Env.get_cons] <;> rfl,
        by simp +decide [sev, Env.get_cons] <;> rfl, by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv],
        by simp +decide [sev, Env.get_cons], trivial⟩
      (PostRs (ctxH C H)) (fun rs w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (rs.map Enc.idxW))
      (fun rs w s' st ⟨H', o, hp', hw, hr, hsr⟩ => ⟨H', hp', ⟨o, hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu crlParams _ rfl hlk)
        (by
          have h := crl_spec (σ := σ) mode ra C hok hs hpl hc.crl g recCls cvGs c oms hcb63 ⟨ps, hpsL, hpsb, hpsr⟩
            rns prn hrns opm hpm hpml os hsb hsl hcb opr hpr hprl hnP pushed pn hpsl cvGs[i] ol hbl
            (hlen _ hmem) ks hkl hks' g.ctors[c] oxs[c] hxsc hxbc.1 hxbc.2 (g.ctors[c].length - 0) 0 H s rfl
            (Nat.zero_le _) hp hpn hrnb
          simp only [List.drop_zero] at h
          exact h))
      (fun rhss w s1 H1 hp1 ⟨orh, hw, hrh⟩ => ?_)
    subst hw
    have hp1' : H <+: H1 := hp1
    refine specR_callNIH (C := ctxH C H1) ExS.lY fCrr crrParams
      [vv crrCv, .op .add [vv crrI, .const 1], vv crrN, vv crrOc, vv crrCss, vv crrOms, vv crrRp, vv crrNp, vv crrPm,
        vv crrSl, vv crrPr, vv crrN0, vv crrPn, vv crrPl, vv crrRnb] (crrBody C)
      [cellA C ocv, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 cvGs.length, cellA C orc, cellA C ocss, cellA C oms,
        BitVec.ofNat 64 g.pre.length, BitVec.ofNat 64 g.nP, cellA C opm, cellA C os, cellA C opr,
        BitVec.ofNat 64 (g.nP + g.slots.length), cellA C pn, BitVec.ofNat 64 pushed.length, cellA C prn]
      (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, crrParams, ctxEnv], trivial⟩
      (PostOut (ctxH C H1))
      (fun out w _ H' => ∃ o, w = cellA C o ∧ PRep C H' o (fun H o t => RRRep C H o t) out)
      (fun out w s' st ⟨H', o, hp', hw, hr, hsr⟩ => ⟨H', hp', ⟨o, hw, hr⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu crrParams _ rfl hlk)
        (ih (i + 1) H1 s1 (by omega) (by omega) (hp.trans hp1') (fun j hj => get_prefix (hpn j hj) hp1')
          (blkAt_mono hrnb hp1')))
      (fun out w s2 H2 hp2 ⟨oy, hw, hry⟩ => ?_)
    subst hw
    have hp2' : H1 <+: H2 := hp2
    have hpC2 : C.H <+: H2 := hp.trans (hp1'.trans hp2')
    refine specR_alloc3I (ctxOK_H hok H2) crrT (vv crrRs) (vv crrV) (vv crrM) (cellA C orh) (cellA C ovs[i])
      (cellA C op) (by decide) (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons])
      (fun _ => by simp +decide [sev, Env.get_cons]) (fun H3 ws hp3 hws => ?_)
    obtain ⟨g0, g1, g2⟩ := img3_get H3 ws (cellA C orh) (cellA C ovs[i]) (cellA C op) hws
    have hp3' : H2 <+: _ := (hp3 : H2 <+: H3).trans (img3_prefix H3 ws (cellA C orh) (cellA C ovs[i]) (cellA C op) hws)
    generalize (((H3 ++ ws).set H3.length (cellA C orh)).set (H3.length + 1) (cellA C ovs[i])).set (H3.length + 2)
      (cellA C op) = H4 at hp3' g0 g1 g2
    obtain ⟨oss, hossl, hossb, hossr⟩ := hry
    refine ExPre.prepend_spec C hok (H := H4) crrT (cellA C H3.length) oy (oss.map (cellA C)) (by decide)
      (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons] <;> rfl) (blkAt_mono hossb hp3') (by decide)
      (by simp +decide [Env.get_cons, Env.get, crrParams, ctxEnv]) (by decide) (fun H' o t hp' hb hsr => ?_)
    have hp4 : H4 <+: H' := hp'
    have hrep4 : RRRep C H' H3.length (cvGs[i], g.cls[c], rhss) :=
      ⟨orh, ovs[i], op, get_prefix g0 hp4, blkAt_mono hrh (hp2'.trans (hp3'.trans hp4)), get_prefix g1 hp4,
        cvRep_mono (hpC2.trans (hp3'.trans hp4)) ⟨hn0, ⟨_, hwl, ol, rfl, hebl⟩, hty⟩, get_prefix g2 hp4,
        tmRep_mono (hpC2.trans (hp3'.trans hp4)) hrep⟩
    exact ⟨H', o, hp1'.trans (hp2'.trans (hp3'.trans hp4)), rfl,
      ⟨H3.length :: oss, by simp [hossl], hb, fun j hj hjo => by
        rcases j with _ | j
        · exact hrep4
        · exact rrRep_mono (hp3'.trans hp4) (hossr j (by simpa using hj) (by simpa using hjo))⟩, hsr⟩

end

end ConPanqueque.T.Ind
