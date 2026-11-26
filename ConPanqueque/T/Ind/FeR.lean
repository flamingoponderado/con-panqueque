import ConPanqueque.T.Ind.RuleCheck
import ConPanqueque.T.Ind.ConsCtors
import ConPanqueque.T.Decl.IdxInsRec

/-!
# The rule-less recursor pushed, the rules checked, the push undone

`genRules`: `genRecCheck`'s tail once the generated recursor constants are in hand — the temporary push
(`classFeR`), the flush entering it, the rules, the pop and the flags set back, the flush leaving it.
The port (one recursor, class `0`) writes the recursor's record, inserts its name (a name already present
hangs), reads the flags, checks the rules, undoes the insert (`undoCode`), and reads the flags again.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

/-- `genRecCheck` after the generated recursor constants `cvGs`. -/
def genRules (mode : ConLeche.CheckMode) (fe : IFEnv) (p : BlockShape) (g : ClassGen) (recCls : List Nat)
    (cvGs : List IConstantVal) : AM (IFEnv × List (IConstantVal × TargetMajor × List EIdx)) := do
  let (feR, prevs) := classFeR p cvGs recCls fe
  let pushed := cvGs.map (·.name)
  flushCaches
  let out ← classRecsRulesOk mode feR pushed g recCls cvGs cvGs recCls
  let fe2 := (prevs.foldr (fun (n, prev) acc => acc.popTemp n prev) feR).setFlags fe.natLit fe.strLit
  flushCaches
  pure (fe2, out)

/-! ## The environments -/

/-- The recursor `classFeR` pushes for recursor `0`. -/
def feRCi (p : BlockShape) (cv : IConstantVal) : IConstantInfo :=
  .recInfo cv (p.majorIdxAt 0) (p.rulePrefixAt 0) false []

theorem classFeR_one (p : BlockShape) (cv : IConstantVal) (fe : IFEnv) :
    classFeR p [cv] [0] fe = (fe.push (feRCi p cv), [(cv.name, fe.idx[cv.name]?)]) := rfl

/-- The pushed recursor popped. -/
def feMid (fe : IFEnv) (ci : IConstantInfo) : IFEnv := (fe.push ci).popTemp ci.name fe.idx[ci.name]?

theorem feMid_find (fe : IFEnv) (ci : IConstantInfo) (n : NIdx) : (feMid fe ci).find? n = fe.find? n :=
  IFEnv.find?_popTemp fe ci n

theorem feMid_rawTable (fe : IFEnv) (ci : IConstantInfo) (n : NIdx) : (feMid fe ci).rawTable? n = fe.rawTable? n := by
  rw [← IFEnv.rawTable?_push fe ci n]; rfl

theorem feMid_findTable (fe : IFEnv) (ci : IConstantInfo) (n : NIdx) :
    (feMid fe ci).findTable? n = fe.findTable? n := by
  unfold IFEnv.findTable?; rw [feMid_find, feMid_rawTable]

theorem feMid_base (fe : IFEnv) (ci : IConstantInfo) : (feMid fe ci).base = fe.base := by
  simp [feMid]

theorem feMid_flags (fe : IFEnv) (ci : IConstantInfo) :
    (feMid fe ci).natLit = (fe.push ci).natLit ∧ (feMid fe ci).strLit = (fe.push ci).strLit := ⟨rfl, rfl⟩

theorem fe2_find (fe : IFEnv) (ci : IConstantInfo) (n : NIdx) :
    ((feMid fe ci).setFlags fe.natLit fe.strLit).find? n = fe.find? n := by
  rw [IFEnv.setFlags_find?, feMid_find]

theorem fe2_findTable (fe : IFEnv) (ci : IConstantInfo) (n : NIdx) :
    ((feMid fe ci).setFlags fe.natLit fe.strLit).findTable? n = fe.findTable? n := by
  unfold IFEnv.findTable?; rw [IFEnv.setFlags_find?, IFEnv.setFlags_rawTable?, feMid_find, feMid_rawTable]

theorem fe2_flagsOK {fe : IFEnv} (h : FlagsOK fe) (ci : IConstantInfo) :
    FlagsOK ((feMid fe ci).setFlags fe.natLit fe.strLit) :=
  FlagsOK.of_same h (by show (feMid fe ci).base.lits = _; rw [feMid_base]) (fe2_find fe ci) rfl rfl

theorem fe2_litsPinned {fe : IFEnv} {p : Pins} (h : LitsPinned fe p) (ci : IConstantInfo) :
    LitsPinned ((feMid fe ci).setFlags fe.natLit fe.strLit) p := by
  unfold LitsPinned; show (feMid fe ci).base.lits = _; rw [feMid_base]; exact h

theorem fe2_tblGate {fe : IFEnv} (h : TblGate fe) (ci : IConstantInfo) :
    TblGate ((feMid fe ci).setFlags fe.natLit fe.strLit) := by
  intro n t ht
  rw [IFEnv.setFlags_rawTable?, feMid_rawTable] at ht
  rw [fe2_find]; exact h n t ht

/-- The denotation facts carried to an environment answering alike. -/
theorem envDen_congr {fe fe' : IFEnv} {p : Pins} {st : EStore} (hf : ∀ n, fe'.find? n = fe.find? n)
    (ht : ∀ n, fe'.findTable? n = fe.findTable? n) (h : EnvDen fe p st) : EnvDen fe' p st := by
  obtain ⟨hc, htb, hp, hr⟩ := h
  exact ⟨fun c ci hci => hc c ci (by rw [← hf]; exact hci), fun T tbl h' => htb T tbl (by rw [← ht]; exact h'), hp,
    fun c cv mI rP isK rules hci => hr c cv mI rP isK rules (by rw [← hf]; exact hci)⟩

/-- The denotation facts carried to an environment answering fewer lookups (and the same tables). -/
theorem envDen_sub {fe fe' : IFEnv} {p : Pins} {st : EStore}
    (hf : ∀ n ci, fe'.find? n = some ci → fe.find? n = some ci)
    (ht : ∀ n, fe'.findTable? n = fe.findTable? n) (h : EnvDen fe p st) : EnvDen fe' p st := by
  obtain ⟨hc, htb, hp, hr⟩ := h
  exact ⟨fun c ci hci => hc c ci (hf c ci hci), fun T tbl h' => htb T tbl (by rw [← ht]; exact h'), hp,
    fun c cv mI rP isK rules hci => hr c cv mI rP isK rules (hf c _ hci)⟩

theorem genRules_one (mode : ConLeche.CheckMode) (fe : IFEnv) (p : BlockShape) (g : ClassGen) (cv : IConstantVal) :
    genRules mode fe p g [0] [cv] = (do
      flushCaches
      let out ← classRecsRulesOk mode (fe.push (feRCi p cv)) [cv.name] g [0] [cv] [cv] [0]
      flushCaches
      pure ((feMid fe (feRCi p cv)).setFlags fe.natLit fe.strLit, out)) := rfl

/-! ## The port -/

def cfrQ := ofString "cfr_q"
def cfrRc := ofString "cfr_rc"
def cfrCs := ofString "cfr_cs"
def cfrK := ofString "cfr_k"
def cfrRpL := ofString "cfr_rpl"
def cfrNp := ofString "cfr_np"
def cfrPm := ofString "cfr_pm"
def cfrSl := ofString "cfr_sl"
def cfrPr := ofString "cfr_pr"
def cfrN0 := ofString "cfr_n0"
def cfrNm := ofString "cfr_nm"
def cfrLp := ofString "cfr_lp"
def cfrLn := ofString "cfr_ln"
def cfrY := ofString "cfr_y"
def cfrRb := ofString "cfr_rb"
def cfrMi := ofString "cfr_mi"
def cfrRp := ofString "cfr_rp"
def cfrX := ofString "cfr_x"
def cfrRi := ofString "cfr_ri"
def cfrFl := ofString "cfr_fl"
def cfrPb := ofString "cfr_pb"
def cfrRs := ofString "cfr_rs"
def fCfr := ofString "genRules"

def cfrParams : List MlS := [cfrQ, cfrRc, cfrCs, cfrK, cfrRpL, cfrNp, cfrPm, cfrSl, cfrPr, cfrN0]
def cfrLocals : List MlS := [cfrNm, cfrLp, cfrLn, cfrY, cfrRb, cfrMi, cfrRp, cfrX, cfrRi, cfrFl, cfrPb, cfrRs, lJ0]

def cfrBody (C : Ctx) : ProgHOL 64 := prologue cfrLocals
  (.seq (.assign .local cfrNm (.load .one (vv cfrQ)))
  (.seq (.assign .local cfrLp (.load .one (.op .add [(vv cfrQ), .const 8])))
  (.seq (.assign .local cfrLn (.load .one (vv cfrLp)))
  (envFindP C cfrY (vv cfrNm)
  (.ite (.cmp .notEqual (vv cfrY) (.const 0)) hang
  (envRecP C cfrRb [.const 0]
  (.seq (.assign .local cfrMi (.load .one (.op .add [(vv cfrRc), .const 16])))
  (.seq (.assign .local cfrRp (.load .one (.op .add [(vv cfrRc), .const 8])))
  (.seq (.call (some (some (.local, cfrX), none)) fConstRec [vv cfrQ, .const 5, vv cfrMi, vv cfrRp, .const 0, vv cfrRb, .const 0, .const 0])
  (idxInsP C (vv cfrNm) (vv cfrX) cfrRi
  (.seq (.call (some (some (.local, cfrFl), none)) fFlags [])
  (flushCode C (flushRegions false)
  (alloc2 C cfrPb (.const 1) (vv cfrNm)
  (.seq (.call (some (some (.local, cfrRs), none)) fCrl [vv cfrCs, .const 0, vv cfrK, vv cfrRpL, vv cfrNp, vv cfrPm, vv cfrSl, vv cfrPr, vv cfrLp, vv cfrLn, vv cfrN0, vv cfrPb, .const 1])
  (undoCode (C.mg .env) (vv cfrNm)
  (.seq (.call (some (some (.local, cfrFl), none)) fFlags [])
  (flushCode C (flushRegions false)
  (.return (vv cfrRs)))))))))))))))))))


structure CFRCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  csc : CSCCodes C
  crl : CRLCodes mode C
  self : C.code.lookup fCfr = some (cfrParams.map (fun p => (p, ShapeHOL.one)), cfrBody C, .one)

section
variable {σ : Type}

theorem cfr_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cfrLocals → (ctxEnv C ++ cfrParams.zip vals).get x = none :=
  Knot.params_none C cfrLocals cfrParams vals (by decide) (by decide)

/-- After the rules: the environment the twin hands back (answering as `C`'s), and the rules block. -/
def PostGR (C : Ctx) (r : IFEnv × List (IConstantVal × TargetMajor × List EIdx)) (w : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  ∃ EH envM H o, C.EH <+: EH ∧ C.H <+: H ∧ CtxOK (ctxNew C r.1 EH envM H) ∧ SR (ctxNew C r.1 EH envM H) s' st ∧
    TblGate r.1 ∧ FlagsOK r.1 ∧ LitsPinned r.1 C.pins ∧ (∀ n, r.1.find? n = C.fe.find? n) ∧
    (∀ n, r.1.findTable? n = C.fe.findTable? n) ∧
    ∃ cv m rhss, r.2 = [(cv, m, rhss)] ∧ w = cellA C o ∧ BlkAt H o (rhss.map Enc.idxW)

theorem postGR_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostGR C a w s' st → PostGR C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨EH, envM, H, o, h1, h2, h3, h4, h5⟩ => ⟨EH, envM, H, o, h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl, h5⟩

set_option maxHeartbeats 64000000 in
/-- **`genRules`** for one recursor of the one class. -/
theorem cfr_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hpl : C.saved = none) (hc : CFRCodes mode C)
    (hg : TblGate C.fe) (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins)
    (p : BlockShape) (rc : RecShape) (hrc : p.recs[0]? = some rc) (orc : Nat) (hrr : RecRep C C.H orc rc)
    (g : ClassGen) (m0 : TargetMajor) (hcls : g.cls = [m0])
    (cvG : IConstantVal) (q : Nat) (hcv : CVRep C C.H q cvG) (hlen : cvG.levelParams.length < 2 ^ 59)
    (ks : List ConLeche.Name) (hkl : ks.length = cvG.levelParams.length)
    (hks : ∀ j (hj : j < cvG.levelParams.length), denoteN C.St.ns cvG.levelParams[j] = some (ks[j]'(by omega)))
    (hden : CVDen cvG C.St)
    (opm : Nat) (hpm : BlkAt C.H opm (g.params.map Enc.idxW)) (hpml : g.params.length < 2 ^ 56)
    (os : Nat) (hsb : SlotBlk C C.H os g.slots) (hsl : g.slots.length < 2 ^ 56)
    (hcb : ∀ sl ∈ g.slots, ∀ c C' ihs, sl = .minor c C' ihs → c < 2 ^ 63)
    (opr : Nat) (hpr : BlkAt C.H opr (g.pre.map Enc.idxW)) (hprl : g.pre.length < 2 ^ 56) (hnP : g.nP < 2 ^ 56)
    (xs : List ClassCtor) (hxs : g.ctors.getD 0 [] = xs) (ocs : Nat)
    (hcs : PRep C C.H ocs (fun H o cc => CCRep C H o cc) xs) (hxl : xs.length < 2 ^ 58) (hnf : ∀ x ∈ xs, x.nF < 2 ^ 56)
    (s : AState) :
    SpecR (σ := σ) (Pre C s (cfrParams.zip [cellA C q, cellA C orc, cellA C ocs, BitVec.ofNat 64 xs.length,
        BitVec.ofNat 64 g.pre.length, BitVec.ofNat 64 g.nP, cellA C opm, cellA C os, cellA C opr,
        BitVec.ofNat 64 (g.nP + g.slots.length)])) (cfrBody C) s (genRules mode C.fe p g [0] [cvG]) (PostGR C) := by
  refine specR_prologue (postGR_locals C) (cfr_none C _) ?_
  rw [genRules_one]
  obtain ⟨hn0, ⟨wl, hwl, ol, hwlo, hebl⟩, hty⟩ := hcv
  have hbl : BlkAt C.H ol (cvG.levelParams.map Enc.idxW) := hebl
  refine UD.specR_heapLoadI' (C := C) cfrNm _ q _ hn0 (by decide) (by simp +decide [Env.get, cfrParams, ctxEnv]) ?_
  refine UD.specR_heapLoadI' (C := C) cfrLp _ (q + 1) _ hwl (by decide)
    (by simp +decide [sev, Env.get, cfrParams, ctxEnv]; exact cellA_add8 C q) ?_
  subst hwlo
  have hb1 : C.H[ol]? = some (BitVec.ofNat 64 cvG.levelParams.length) := by simpa using hbl.1
  refine UD.specR_heapLoadI' (C := C) cfrLn _ ol _ hb1 (by decide) (by simp +decide [Env.get]; rfl) ?_
  -- the name must be new
  refine specR_envFindI hok hc.csc.k.g hc.csc.k.p cfrY (vv cfrNm) cvG.name (by decide) (by simp +decide [sev, Env.get])
    (by simp +decide [Env.get, cfrParams, ctxEnv]) ?_
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
  refine specR_envRecI hok cfrRb [.const 0] [0] (by decide) rfl (by decide)
    (fun w j hj hj' => by rcases j with _ | j <;> simp at hj; rfl) (fun EH1 hp1 hl1 hv1 => ?_)
  have hok1 := ctxOK_E hok hp1
  have hrb : RulesE C.EB EH1 (ecell C C.EH.length) [] :=
    ⟨C.EH.length, rfl, by simpa using hv1 0 (by simp), fun i hi => absurd hi (by simp)⟩
  obtain ⟨⟨ocr, hocr, hcvr⟩, ⟨hrp, hrpb⟩, ⟨hmi, hmib⟩, -, -, -⟩ := hrr
  have hmaj : p.majorIdxAt 0 = rc.mI := by simp [BlockShape.majorIdxAt, hrc]
  have hrpe : p.rulePrefixAt 0 = rc.rP := by simp [BlockShape.rulePrefixAt, hrc]
  refine UD.specR_heapLoadI' (C := ctxE C EH1) cfrMi _ (orc + 2) _ hmi (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, cfrParams, ctxEnv]; exact cellA_add_ofNat C orc 2) ?_
  refine UD.specR_heapLoadI' (C := ctxE C EH1) cfrRp _ (orc + 1) _ hrp (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, cfrParams, ctxEnv]; exact cellA_add8 C orc) ?_
  set ci : IConstantInfo := feRCi p cvG with hci
  have hcin : ci.name = cvG.name := rfl
  refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => _) (by rw [pure_bind]) ?_
  refine specR_callNC (C := ctxE C EH1) (D := ctxLocals ++ cfrLocals) cfrX fConstRec cwParams
    [vv cfrQ, .const 5, vv cfrMi, vv cfrRp, .const 0, vv cfrRb, .const 0, .const 0] (cwBody C)
    [cellA C q, 5, BitVec.ofNat 64 rc.mI, BitVec.ofNat 64 rc.rP, 0, ecell C C.EH.length, 0, 0]
    (by decide) rfl (by decide) hc.csc.cw ?_
    (PostCW (ctxE C EH1) cvG 5 [BitVec.ofNat 64 rc.mI, BitVec.ofNat 64 rc.rP, 0, ecell C C.EH.length, 0, 0] s)
    (fun _ w s' C' => s' = s ∧ ∃ EH2 ox, C' = ctxE (ctxE C EH1) EH2 ∧ EH1 <+: EH2 ∧ w = ecell C ox ∧ CIE C.EB EH2 ox ci)
    (fun _ w s' st ⟨hs', EH2, ox, hp2, _, hw, hcve, htg, hfs, hsr⟩ => by
      subst hs'
      exact ⟨_, ⟨rfl, EH2, ox, rfl, hp2, hw, hcve, htg,
        ⟨by simpa [hmaj] using hfs 0 (by simp), by rw [hmaj]; exact hmib⟩,
        ⟨by simpa [hrpe] using hfs 1 (by simp), by rw [hrpe]; exact hrpb⟩,
        by simpa [boolW] using hfs 2 (by simp), ecell C C.EH.length, by simpa using hfs 3 (by simp),
        rulesE_mono hp2 hrb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cwParams _ rfl hlk)
      (cw_spec (ctxE C EH1) hok1 (by ctx_tr hc.csc.cp) cvG q ⟨hn0, ⟨_, hwl, ol, rfl, hebl⟩, hty⟩
        (by have := hden.2.2; omega) 5 _ _ _ _ _ _ s))
    (fun _ w s3 C3 ⟨hs3, EH2, ox, eC, hpE2, hw, hcie⟩ => ?_)
  · exact ⟨by simp +decide [sev, Env.get_cons, Env.get, cfrParams, ctxEnv], rfl, by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons], rfl, rfl, trivial⟩
  subst eC hw s3
  refine specR_atEntry fun t5 ht5 => ?_
  have hd5 : CVDen cvG s.store := cvDen_ext hden ht5.sr.floor
  have hdn : NewDen ci s.store := by
    refine ⟨hd5.1, hd5.2.1, hd5.2.2, fun _ _ _ h => (by simp [hci, feRCi] at h), fun _ _ h => (by simp [hci, feRCi] at h)⟩
  refine specR_idxInsI' (C := ctxE C EH1) hok1 hc.csc.k.s hc.csc.k.i hg ci hfn
    (fun _ _ _ _ _ h => by simp only [hci, feRCi, IConstantInfo.recInfo.injEq] at h; exact h.2.2.2.2.symm) EH2 ox hpE2 hdn (vv cfrNm) (vv cfrX) cfrRi (by decide)
    (by simp +decide [sev, Env.get_cons]; rfl) (by simp +decide [sev, Env.get_cons]; rfl)
    (by simp +decide [Env.get_cons, Env.get, cfrParams, ctxEnv]; rfl) (fun wr2 => ?_)
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
      (C.envM.insert ci.name (ecell C ox))) (D := ctxLocals ++ cfrLocals) cfrFl fFlags [] [] Decl.flBody []
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
  refine specR_flushTopI hokF hpl false flushCaches rfl (by decide) ?_
  have hpC6 : C.H <+: H6 := hp6
  refine specR_alloc2I hokF cfrPb (.const 1) (vv cfrNm) 1 (Enc.idxW cvG.name) (by decide) (fun _ => rfl)
    (fun _ => by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cfrParams, ctxEnv]) (fun H7 ws7 hp7 hws7 => ?_)
  obtain ⟨k0, k1⟩ := img2_get H7 ws7 (1 : BitVec 64) (Enc.idxW cvG.name) hws7
  have hp7' : H6 <+: _ := (hp7 : H6 <+: H7).trans (img2_prefix H7 ws7 (1 : BitVec 64) (Enc.idxW cvG.name) hws7)
  set H7' := ((H7 ++ ws7).set H7.length (1 : BitVec 64)).set (H7.length + 1) (Enc.idxW cvG.name) with hH7'
  have hpC7 : C.H <+: H7' := hpC6.trans hp7'
  have hel : Elems H7' H7.length [cvG.name] := fun j hj => by
    have : j = 0 := by simp at hj; omega
    subst this; simpa using k1
  simp only [classRecsRulesOk, hxs, hcls, targetMajorAt, List.getElem?_cons_zero, pure_bind, bind_assoc]
  refine specR_callNIH (C := ctxH (ctxFe (ctxH (ctxIns (ctxE C EH1) ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit)
      EH2 (C.envM.insert ci.name (ecell C ox))) H6) (C.fe.push ci)) H7') cfrRs fCrl crlParams
    [vv cfrCs, .const 0, vv cfrK, vv cfrRpL, vv cfrNp, vv cfrPm, vv cfrSl, vv cfrPr, vv cfrLp, vv cfrLn, vv cfrN0, vv cfrPb,
      .const 1] (crlBody C)
    [cellA C ocs, BitVec.ofNat 64 0, BitVec.ofNat 64 xs.length, BitVec.ofNat 64 g.pre.length, BitVec.ofNat 64 g.nP,
      cellA C opm, cellA C os, cellA C opr, cellA C ol, BitVec.ofNat 64 cvG.levelParams.length,
      BitVec.ofNat 64 (g.nP + g.slots.length), cellA C H7.length, BitVec.ofNat 64 [cvG.name].length]
    (by decide) rfl (by decide) hc.crl.self
    ⟨by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cfrParams, ctxEnv], rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cfrParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cfrParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cfrParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cfrParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cfrParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cfrParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cfrParams, ctxEnv]; rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cfrParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cfrParams, ctxEnv],
      by simp +decide [sev, Env.get_cons]; rfl, rfl, trivial⟩
    (PostRs (ctxH (ctxFe (ctxH (ctxIns (ctxE C EH1) ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit)
      EH2 (C.envM.insert ci.name (ecell C ox))) H6) (C.fe.push ci)) H7'))
    (fun rs w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (rs.map Enc.idxW))
    (fun rs w s' st ⟨H', o, hp', hw, hr, hsr⟩ => ⟨H', hp', ⟨o, hw, hr⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu crlParams _ rfl hlk)
      (crl_spec mode ra _ hokF hs hpl (by ctx_tr hc.crl) g [0] [cvG] opm (blkAt_mono hpm hpC6) hpml os
        (slotBlk_mono hpC6 hsb) hsl hcb opr (blkAt_mono hpr hpC6) hprl hnP [cvG.name] H7.length (by simp)
        cvG ol (blkAt_mono hbl hpC6) hlen ks hkl hks xs ocs (pRep_mono hpC6 (fun _ _ => ccRep_mono hpC6) hcs) hxl hnf
        xs.length 0 H7' (flushedS false s) (by omega) (by omega) hp7' hel))
    (fun rhss w s8 H8 hp8 ⟨orr, hw, hbr⟩ => ?_)
  subst hw
  have hp8' : H7' <+: H8 := hp8
  have hpC8 : C.H <+: H8 := hpC7.trans hp8'
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
  refine specR_envUndoI (C := ctxH (ctxH (ctxFe (ctxH (ctxIns (ctxE C EH1) ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit)
      EH2 (C.envM.insert ci.name (ecell C ox))) H6) (C.fe.push ci)) H7') H8) (ctxOK_H (ctxOK_H hokF H7') H8) cvG.name
    (feMid C.fe ci) rfl hden8 (vv cfrNm) (by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cfrParams, ctxEnv])
    (by decide) ?_
  have hm : ∀ n : NIdx, ((C.envM.insert ci.name (ecell C ox)).erase cvG.name)[n]? = C.envM[n]? := by
    intro n
    rw [Std.HashMap.getElem?_erase, Std.HashMap.getElem?_insert]
    by_cases h : cvG.name = n
    · subst h; simp [hrel]
    · simp [h, hcin]
  have hokV : CtxOK (ctxIns (ctxH (ctxE C EH1) H8) (feMid C.fe ci) EH2
      ((C.envM.insert ci.name (ecell C ox)).erase cvG.name)) :=
    ctxOK_insEq (ctxOK_H hok1 H8) hpE2 (feMid_find _ _) (feMid_findTable _ _) hm
  set fe2 := (feMid C.fe ci).setFlags C.fe.natLit C.fe.strLit with hfe2
  have hfV : ∀ n, fe2.find? n = (ctxIns (ctxH (ctxE C EH1) H8) (feMid C.fe ci) EH2
      ((C.envM.insert ci.name (ecell C ox)).erase cvG.name)).fe.find? n := fun n => IFEnv.setFlags_find? _ _ _ n
  have htV : ∀ n, fe2.findTable? n = (ctxIns (ctxH (ctxE C EH1) H8) (feMid C.fe ci) EH2
      ((C.envM.insert ci.name (ecell C ox)).erase cvG.name)).fe.findTable? n := fun n => by
    show (feMid C.fe ci |>.setFlags C.fe.natLit C.fe.strLit).findTable? n = (feMid C.fe ci).findTable? n
    unfold IFEnv.findTable?; rw [IFEnv.setFlags_find?, IFEnv.setFlags_rawTable?]
  have hnV : fe2.natLit = pinsFound (ctxIns (ctxH (ctxE C EH1) H8) (feMid C.fe ci) EH2
      ((C.envM.insert ci.name (ecell C ox)).erase cvG.name)) natPins := by
    show C.fe.natLit = _
    rw [hF.nat, natLitStoredBy_pins hL]
    unfold pinsFound ctxIns
    simp only [feMid_find]; rfl
  have hsV : fe2.strLit = pinsFound (ctxIns (ctxH (ctxE C EH1) H8) (feMid C.fe ci) EH2
      ((C.envM.insert ci.name (ecell C ox)).erase cvG.name)) strPins := by
    show C.fe.strLit = _
    rw [hF.str, strLitStoredBy_pins hL]
    unfold pinsFound ctxIns
    simp only [feMid_find]; rfl
  refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => _) (by rw [pure_bind]) ?_
  refine specR_callNC (C := ctxIns (ctxH (ctxE C EH1) H8) (feMid C.fe ci) EH2
      ((C.envM.insert ci.name (ecell C ox)).erase cvG.name)) (D := ctxLocals ++ cfrLocals) cfrFl fFlags [] [] Decl.flBody []
    (by decide) rfl (by decide) hc.csc.flags trivial
    (fun a w s' st => PostFl (ctxIns (ctxH (ctxE C EH1) H8) (feMid C.fe ci) EH2
      ((C.envM.insert ci.name (ecell C ox)).erase cvG.name)) fe2 a w s' st ∧ s' = s8)
    (fun _ w s' C' => s' = s8 ∧ ∃ H9, C' = ctxFe (ctxH (ctxIns (ctxH (ctxE C EH1) H8) (feMid C.fe ci) EH2
      ((C.envM.insert ci.name (ecell C ox)).erase cvG.name)) H9) fe2 ∧ H8 <+: H9)
    (fun a w s' st ⟨⟨H9, hp9, hsr⟩, hs'⟩ => ⟨_, ⟨hs', H9, rfl, hp9⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [] _ rfl hlk)
      (specR_pureState (fl_spec _ hokV (by ctx_tr hc.csc.natF) (by ctx_tr hc.csc.strF) (by ctx_tr hc.csc.k.g)
        (by ctx_tr hc.csc.k.p) s8 hfV htV hnV hsV)))
    (fun _ w s9 C9 ⟨hs9, H9, eC, hp9⟩ => ?_)
  subst eC s9
  have hokFin := ctxOK_fe (ctxOK_H hokV H9) (fe := fe2) (fun n => hfV n) (fun n => htV n)
  refine specR_flushTopI hokFin hpl false flushCaches rfl (by decide) ?_
  exact specR_returnI _ (cellA C orr) (by simp +decide [sev, Env.get_cons, Env.get, Env.kill])
    (fun t ht => ⟨EH2, (C.envM.insert ci.name (ecell C ox)).erase cvG.name, H9, orr, hp1.trans hpE2,
      hpC8.trans hp9, hokFin, sr_of_eq ht.sr rfl rfl rfl rfl, fe2_tblGate hg ci, fe2_flagsOK hF ci,
      fe2_litsPinned hL ci, fe2_find C.fe ci, fe2_findTable C.fe ci, cvG, m0, rhss, rfl, rfl, blkAt_mono hbr hp9⟩)

end

end ConPanqueque.T.Ind
