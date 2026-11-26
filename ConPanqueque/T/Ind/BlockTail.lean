import ConPanqueque.T.Ind.RecInstall
import ConPanqueque.T.Decl.FeSwitch
import ConPanqueque.T.Ind.IdxSorts

/-!
# `checkBlockTail` (one member, one recursor)

`cqBody`: the block's tables (none or one) checked.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def cqQ := ofString "cq_q"
def cqN := ofString "cq_n"
def cqT := ofString "cq_t"
def cqX := ofString "cq_x"
def fCq := ofString "checkBlockTables"

def cqParams : List MlS := [cqQ]
def cqLocals : List MlS := [cqN, cqT, cqX]

def cqBody : ProgHOL 64 := prologue cqLocals
  (.seq (.assign .local cqN (.load .one (vv cqQ)))
  (.ite (.cmp .equal (vv cqN) (.const 0)) (.return (.const 0))
    (.seq (.assign .local cqT (.load .one (.op .add [vv cqQ, .const 8])))
    (.seq (.call (some (some (.local, cqX), none)) fCst [vv cqT]) (.return (.const 0))))))

structure CQCodes (C : Ctx) : Prop where
  cst : CSTCodes C
  self : C.code.lookup fCq = some (cqParams.map (fun p => (p, ShapeHOL.one)), cqBody, .one)

/-- `checkBlockTail` after the generated recursor stage. -/
def tailS (mode : ConLeche.CheckMode) (p : BlockShape) (Q : List IProjTable)
    (r : IFEnv × List (IConstantVal × TargetMajor × List EIdx)) : AM IFEnv :=
  match r with
  | (fe₂b, out) => do
    streamKCheck p p.recs out
    let infos ← blockRecInfosTF p 0 out
    let (feG, prevs) := consBlockRecsTemp infos fe₂b []
    flushCaches
    streamRecsCheck mode feG p.recs out
    let fe₃ := (prevs.foldr (fun (n, prev) acc => acc.popTemp n prev) feG).setFlags fe₂b.natLit fe₂b.strLit
    flushCaches
    checkBlockTables fe₃ Q
    pure fe₃

theorem checkBlockTail_eq (mode : ConLeche.CheckMode) (block : List IConstantInfo) (q : BlockPass)
    (Q : List IProjTable) :
    checkBlockTail mode block q Q = (do
      checkBlockIdxSorts mode q.env1 q.p q.p.members
      let fe₂ := consBlockCtors q.p.nP q.p.ctorGroups q.env1
      flushCaches
      let r ← checkBlockRec mode fe₂ q.p (blockNestedBit q.p q.kinds) q.params q.tbl q.rd q.cls block
      tailS mode q.p Q r) := rfl

/-- The pops give back an index answering as the pushes' start, its flags set back. -/
theorem tail_fe (cs : List IConstantInfo) (fe : IFEnv) :
    let fe₃ := ((consBlockRecsTemp cs fe []).2.foldr (fun (x : NIdx × Option IConstantInfo) acc => acc.popTemp x.1 x.2)
      (consBlockRecsTemp cs fe []).1).setFlags fe.natLit fe.strLit
    (∀ n, fe₃.find? n = fe.find? n) ∧ (∀ n, fe₃.findTable? n = fe.findTable? n) ∧ fe₃.base = fe.base ∧
      fe₃.natLit = fe.natLit ∧ fe₃.strLit = fe.strLit ∧ (∀ n, fe₃.rawTable? n = fe.rawTable? n) := by
  intro fe₃
  obtain ⟨news, hn, hf⟩ := ConRon.Bridge.Inductives.BT.consBlockRecsTemp_pop cs fe []
  simp only [List.nil_append] at hn
  have hq : ConRon.Bridge.Inductives.GR.FEq fe₃ fe := by
    have : fe₃ = (news.foldr (fun (x : NIdx × Option IConstantInfo) acc => acc.popTemp x.1 x.2)
      (consBlockRecsTemp cs fe []).1).setFlags fe.natLit fe.strLit := by simp only [fe₃, hn]
    rw [this]; exact ⟨hf.1, hf.2.1, hf.2.2.1, hf.2.2.2⟩
  refine ⟨hq.find?, fun n => ?_, hq.2.2.1, rfl, rfl, hq.rawTable?⟩
  simp only [IFEnv.findTable?, hq.find?, hq.rawTable?]

def ctsR := ofString "cts_r"
def ctsOrr := ofString "cts_orr"
def ctsOq := ofString "cts_oq"
def ctsNc := ofString "cts_nc"
def ctsOsh := ofString "cts_osh"
def ctsQ := ofString "cts_q"
def ctsK := ofString "cts_k"
def ctsKi := ofString "cts_ki"
def ctsRl := ofString "cts_rl"
def ctsNr := ofString "cts_nr"
def ctsX := ofString "cts_x"
def ctsRcv := ofString "cts_rcv"
def ctsTyR := ofString "cts_tyr"
def ctsGcv := ofString "cts_gcv"
def ctsTyG := ofString "cts_tyg"
def ctsOrh := ofString "cts_orh"
def ctsNh := ofString "cts_nh"
def ctsRp := ofString "cts_rp"
def fCts := ofString "checkBlockTailS"

def ctsParams : List MlS := [ctsR, ctsOrr, ctsOq, ctsNc, ctsOsh, ctsQ]
def ctsLocals : List MlS := [ctsK, ctsKi, ctsRl, ctsNr, ctsX, ctsRcv, ctsTyR, ctsGcv, ctsTyG, ctsOrh, ctsNh, ctsRp, lJ0]

def ctsBody (C : Ctx) : ProgHOL 64 := prologue ctsLocals
  (.seq (.call (some (some (.local, ctsK), none)) fKexp [vv ctsOsh, vv ctsOq])
  (.seq (.assign .local ctsKi (.load .one (.op .add [vv ctsOrr, .const 40])))
  (.ite (.cmp .equal (vv ctsK) (vv ctsKi))
    (flushCode C (flushRegions false)
    (.seq (.assign .local ctsRl (.load .one (.op .add [vv ctsOrr, .const 32])))
    (.seq (.assign .local ctsNr (.load .one (vv ctsRl)))
    (.ite (.cmp .equal (vv ctsNr) (vv ctsNc))
      (.seq (.call (some (some (.local, ctsX), none)) fSrs [vv ctsRl, vv ctsOq, .const 0, vv ctsNc])
      (.seq (.assign .local ctsRcv (.load .one (vv ctsOrr)))
      (.seq (.assign .local ctsTyR (.load .one (.op .add [vv ctsRcv, .const 16])))
      (.seq (.assign .local ctsGcv (.load .one (.op .add [vv ctsR, .const 8])))
      (.seq (.assign .local ctsTyG (.load .one (.op .add [vv ctsGcv, .const 16])))
      (.ite (.cmp .equal (vv ctsTyR) (vv ctsTyG))
        (.seq (.assign .local ctsOrh (.load .one (vv ctsR)))
        (.seq (.assign .local ctsNh (.load .one (vv ctsOrh)))
        (.ite (.cmp .equal (vv ctsNh) (vv ctsNc))
          (.seq (.assign .local ctsRp (.load .one (.op .add [vv ctsOrr, .const 8])))
          (.seq (.call (some (some (.local, ctsX), none)) fSrr [vv ctsRl, vv ctsOrh, .const 0, vv ctsNc, vv ctsRp])
          (flushCode C (flushRegions false)
          (.seq (.call (some (some (.local, ctsX), none)) fCq [vv ctsQ])
            (.return (.const 0))))))
          hang)))
        hang))))))
      hang))))
    hang)))

structure CTSCodes (C : Ctx) : Prop where
  kx : C.code.lookup fKexp = some (kxParams.map (fun p => (p, ShapeHOL.one)), kxBody, .one)
  srs : C.code.lookup fSrs = some (srsParams.map (fun p => (p, ShapeHOL.one)), srsBody, .one)
  sl : C.code.lookup fStripLams = some ([(pFu, .one), (pH, .one)], stripBody C fStripLams 5, .one)
  srr : C.code.lookup fSrr = some (srrParams.map (fun p => (p, ShapeHOL.one)), srrBody, .one)
  cq : CQCodes C
  self : C.code.lookup fCts = some (ctsParams.map (fun p => (p, ShapeHOL.one)), ctsBody C, .one)


def ctbSh := ofString "ctb_sh"
def ctbOrr := ofString "ctb_orr"
def ctbPm := ofString "ctb_pm"
def ctbOt := ofString "ctb_ot"
def ctbNt := ofString "ctb_nt"
def ctbOq := ofString "ctb_oq"
def ctbNq := ofString "ctb_nq"
def ctbLv := ofString "ctb_lv"
def ctbOlp := ofString "ctb_olp"
def ctbTy0 := ofString "ctb_ty0"
def ctbPp := ofString "ctb_pp"
def ctbNpp := ofString "ctb_npp"
def ctbPa := ofString "ctb_pa"
def ctbNd := ofString "ctb_nd"
def ctbNm := ofString "ctb_nm"
def ctbOsl := ofString "ctb_osl"
def ctbNsl := ofString "ctb_nsl"
def ctbOm := ofString "ctb_om"
def ctbNc := ofString "ctb_nc"
def ctbNi := ofString "ctb_ni"
def ctbInd := ofString "ctb_ind"
def ctbNpc := ofString "ctb_npc"
def ctbNP := ofString "ctb_np"
def ctbRs := ofString "ctb_rs"
def ctbQ := ofString "ctb_q"
def ctbX := ofString "ctb_x"
def ctbR := ofString "ctb_r"
def fCtb := ofString "checkBlockTail"

def ctbParams : List MlS := [ctbSh, ctbOrr, ctbPm, ctbOt, ctbNt, ctbOq, ctbNq, ctbLv, ctbOlp, ctbTy0, ctbPp, ctbNpp, ctbPa, ctbNd, ctbNm, ctbOsl, ctbNsl, ctbOm, ctbNc, ctbNi, ctbInd, ctbNpc, ctbNP, ctbRs, ctbQ]
def ctbLocals : List MlS := [ctbX, ctbR, lJ0]

def ctbBody (C : Ctx) : ProgHOL 64 := prologue ctbLocals
  (.seq (.call (some (some (.local, ctbX), none)) fBis [vv ctbOm, vv ctbNP, vv ctbRs])
  (.seq (.call (some (some (.local, ctbX), none)) fConsCtors [vv ctbOq, .const 0, vv ctbNq, vv ctbNP, vv ctbNm])
  (flushCode C (flushRegions false)
  (.seq (.call (some (some (.local, ctbR), none)) fGa [vv ctbSh, vv ctbOrr, vv ctbPm, vv ctbOt, vv ctbNt, vv ctbOq, vv ctbNq, vv ctbLv, vv ctbOlp, vv ctbTy0, vv ctbPp, vv ctbNpp, vv ctbPa, vv ctbNd, vv ctbNm, vv ctbOsl, vv ctbNsl, vv ctbOm, vv ctbNc, vv ctbNi, vv ctbInd, vv ctbNpc])
  (.seq (.call (some (some (.local, ctbX), none)) fCts [vv ctbR, vv ctbOrr, vv ctbOq, vv ctbNq, vv ctbSh, vv ctbQ])
    (.return (vv ctbX)))))))

structure CTBCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  bis : BISCodes C
  k : KCodes C Comp.kBodies
  ac : Comp.AllCodes mode C
  csc : CSCCodes C
  ga : GACodes mode C
  cts : CTSCodes C
  self : C.code.lookup fCtb = some (ctbParams.map (fun p => (p, ShapeHOL.one)), ctbBody C, .one)


section
variable {σ : Type}

theorem cq_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cqLocals → (ctxEnv C ++ cqParams.zip vals).get x = none :=
  Knot.params_none C cqLocals cqParams vals (by decide) (by decide)

/-- **`checkBlockTables`** on at most one table. -/
theorem cq_spec (C : Ctx) (hok : CtxOK C) (hc : CQCodes C) (Q : List IProjTable) (hQ : Q.length ≤ 1) (oq : Nat)
    (hq : PRep C C.H oq (fun H o t => TblVRep C H o t) Q)
    (hden : ∀ t ∈ Q, ∃ ks : List ConLeche.Name, ∃ hkl : ks.length = t.levelParams.length,
      ∀ j (hj : j < t.levelParams.length), denoteN C.St.ns t.levelParams[j] = some (ks[j]'(by rw [hkl]; exact hj)))
    (hbd : ∀ t ∈ Q, t.levelParams.length < 2 ^ 62 ∧ t.numParams < 2 ^ 62 ∧ t.numFields < 2 ^ 64 ∧ t.bodies.size < 2 ^ 58)
    (s : AState) :
    SpecR (σ := σ) (Pre C s (cqParams.zip [cellA C oq])) cqBody s (checkBlockTables C.fe Q) (Decl.PostU C) := by
  refine specR_prologue (Decl.postU_locals C) (cq_none C _) ?_
  obtain ⟨os, hosl, hosb, hosr⟩ := hq
  have hn : C.H[oq]? = some (BitVec.ofNat 64 Q.length) := by simpa [hosl] using hosb.1
  refine UD.specR_heapLoadI' (C := C) cqN _ oq _ hn (by decide) (by simp +decide [sev, Env.get, cqParams, ctxEnv]) ?_
  rcases hQs : Q with _ | ⟨t, _ | ⟨t', Q'⟩⟩
  · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    simp only [checkBlockTables]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C.H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    subst hQs
    obtain ⟨o0, rfl⟩ : ∃ o0, os = [o0] := by
      match os, hosl with
      | [o0], _ => exact ⟨o0, rfl⟩
    have hp0' : C.H[oq + 1 + 0]? = some (cellA C o0) := by simpa using hosb.2 0 (by simp)
    refine UD.specR_heapLoadI' (C := C) cqT _ (oq + 1 + 0) _ hp0' (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, cqParams, ctxEnv]; exact cellA_add8 C oq) ?_
    have htv : TblVRep C C.H o0 t := by simpa using hosr 0 (by simp) (by simp)
    obtain ⟨ks, hkl, hks⟩ := hden t (by simp)
    obtain ⟨b1, b2, b3, b4⟩ := hbd t (by simp)
    simp only [checkBlockTables, bind_assoc]
    refine specR_congr (m' := checkStructProjTable t C.fe >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNIH (C := C) cqX fCst cstParams [vv cqT] (cstBody C) [cellA C o0] (by decide) rfl (by decide)
      hc.cst.self ⟨by simp +decide [sev, Env.get_cons], trivial⟩ (Decl.PostU C) (fun _ _ _ _ => True)
      (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cstParams _ rfl hlk)
        (cst_spec C hok hc.cst t o0 htv ks hkl hks b1 b2 b3 b4 s))
      (fun _ w s1 H1 hp1 _ => ?_)
    exact specR_returnI _ 0 rfl (fun t' ht => ⟨H1, hp1, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · subst hQs; simp at hQ

theorem cts_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ctsLocals → (ctxEnv C ++ ctsParams.zip vals).get x = none :=
  Knot.params_none C ctsLocals ctsParams vals (by decide) (by decide)

theorem boolW_inj' {a b : Bool} (h : boolW a = boolW b) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-- After the stream's checks: the environment the pops give back, answering as the context's. -/
def PostTS (C : Ctx) (r : IFEnv) (_ : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H, C.H <+: H ∧ SR (ctxNew C r C.EH C.envM H) s' st ∧ (∀ n, r.find? n = C.fe.find? n) ∧
    (∀ n, r.findTable? n = C.fe.findTable? n) ∧ r.base = C.fe.base ∧ r.natLit = C.fe.natLit ∧ r.strLit = C.fe.strLit ∧
    (∀ n, r.rawTable? n = C.fe.rawTable? n)

theorem postTS_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostTS C a w s' st → PostTS C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H, h1, h2, h3⟩ => ⟨H, h1, sr_of_eq h2 rfl rfl rfl rfl, h3⟩

set_option maxHeartbeats 16000000 in
/-- **`checkBlockTail` after the recursor stage**: one member, one recursor at it. -/
theorem cts_spec (mode : ConLeche.CheckMode) (C : Ctx) (hok : CtxOK C) (hpl : C.saved = none) (hc : CTSCodes C)
    (p : BlockShape) (hk : p.k = 1) (osh : Nat) (hip : C.H[osh + 6]? = some (boolW p.isProp))
    (rc : RecShape) (hrecs : p.recs = [rc]) (orr : Nat) (hrr : RecRep C C.H orr rc) (hrP : rc.rP < 2 ^ 62)
    (hrl : rc.rules.length < 2 ^ 58)
    (m : TargetMajor) (hmm : m.member = some 0) (oq : Nat) (hcr : CtorsRep C C.H oq m.ctors)
    (hcsl : m.ctors.length < 2 ^ 58)
    (cv : IConstantVal) (rhss : List EIdx) (o orh oc : Nat) (ho1 : C.H[o]? = some (cellA C orh))
    (ho2 : C.H[o + 1]? = some (cellA C oc)) (hrh : BlkAt C.H orh (rhss.map Enc.idxW)) (hcv : CVRep C C.H oc cv)
    (Q : List IProjTable) (hQ : Q.length ≤ 1) (oQ : Nat)
    (hq : PRep C C.H oQ (fun H o t => TblVRep C H o t) Q)
    (hden : ∀ t ∈ Q, ∃ ks : List ConLeche.Name, ∃ hkl : ks.length = t.levelParams.length,
      ∀ j (hj : j < t.levelParams.length), denoteN C.St.ns t.levelParams[j] = some (ks[j]'(by rw [hkl]; exact hj)))
    (hbd : ∀ t ∈ Q, t.levelParams.length < 2 ^ 62 ∧ t.numParams < 2 ^ 62 ∧ t.numFields < 2 ^ 64 ∧ t.bodies.size < 2 ^ 58)
    (s : AState) :
    SpecR (σ := σ) (Pre C s (ctsParams.zip [cellA C o, cellA C orr, cellA C oq, BitVec.ofNat 64 m.ctors.length,
        cellA C osh, cellA C oQ])) (ctsBody C) s (tailS mode p Q (C.fe, [(cv, m, rhss)])) (PostTS C) := by
  refine specR_prologue (postTS_locals C) (cts_none C _) ?_
  simp only [tailS, hrecs, streamKCheck, blockRecInfosTF, generatedRules, hmm, pure_bind]
  obtain ⟨hf3, ht3, hb3, hn3, hs3, hr3⟩ := tail_fe
    [IConstantInfo.recInfo cv (p.majorIdxAt 0) (p.rulePrefixAt 0) (recKExpected p m) (sumRules m.ctors rhss)] C.fe
  generalize ((List.foldr (fun (x : NIdx × Option IConstantInfo) acc => acc.popTemp x.1 x.2)
    (consBlockRecsTemp [IConstantInfo.recInfo cv (p.majorIdxAt 0) (p.rulePrefixAt 0) (recKExpected p m)
      (sumRules m.ctors rhss)] C.fe []).1
    (consBlockRecsTemp [IConstantInfo.recInfo cv (p.majorIdxAt 0) (p.rulePrefixAt 0) (recKExpected p m)
      (sumRules m.ctors rhss)] C.fe []).2).setFlags C.fe.natLit C.fe.strLit) = fe₃ at hf3 ht3 hb3 hn3 hs3 hr3 ⊢
  generalize (consBlockRecsTemp [IConstantInfo.recInfo cv (p.majorIdxAt 0) (p.rulePrefixAt 0) (recKExpected p m)
      (sumRules m.ctors rhss)] C.fe []).1 = feG
  obtain ⟨⟨ocr, hcr0, hcvr⟩, hrp, -, -, ⟨wr, hwr, orl, hwo, hrl0, hrls⟩, hisk⟩ := hrr
  refine specR_congr (m' := pure (recKExpected p m) >>= fun b => (if (rc.isK == b) = true then pure () else
      (fail (CheckError.invalid "recursor  declares k := ; the generated recursor of this block is K-like") >>= fun _ => pure ())) >>= fun _ => _)
    (by rw [pure_bind]) ?_
  refine specR_callNIH (C := C) ctsK fKexp kxParams [vv ctsOsh, vv ctsOq] kxBody [cellA C osh, cellA C oq] (by decide) rfl
    (by decide) hc.kx ⟨by simp +decide [sev, Env.get, ctsParams, ctxEnv], by simp +decide [sev, Env.get, ctsParams, ctxEnv], trivial⟩
    (PostKX C s) (fun b w s' H' => s' = s ∧ H' = C.H ∧ w = boolW b)
    (fun a w s' st ⟨h1, h2, h3⟩ => ⟨C.H, List.prefix_refl _, ⟨h1, rfl, h2⟩, h3⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu kxParams _ rfl hlk)
      (kx_spec C p hk osh hip m hmm oq hcr (by omega) s))
    (fun b w s1 H1 _ ⟨e1, e2, e3⟩ => ?_)
  subst e1 e2 e3
  refine UD.specR_heapLoadI' (C := C) ctsKi _ (orr + 5) _ hisk (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, ctsParams, ctxEnv]; exact cellA_add_ofNat C orr 5) ?_
  by_cases hK : b = rc.isK
  swap
  · refine specR_ifI _ 0 (by
      simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      exact fun h => hK (boolW_inj' h)) (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hK])
    (fun _ => ?_) (fun h => absurd h (by decide))
  subst hK
  simp only [beq_self_eq_true, ite_true, pure_bind]
  refine specR_flushTopI hok hpl false flushCaches rfl (by decide) ?_
  generalize flushedS false s1 = s2
  refine UD.specR_heapLoadI' (C := C) ctsRl _ (orr + 4) _ hwr (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctsParams, ctxEnv]; exact cellA_add_ofNat C orr 4) ?_
  rw [hwo] at hwr ⊢
  refine UD.specR_heapLoadI' (C := C) ctsNr (vv ctsRl) orl _ hrl0 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  by_cases hlen : rc.rules.length = m.ctors.length
  swap
  · refine specR_ifI _ 0 (by
      simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      intro h; apply hlen
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      exact this) (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by
      simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlen])
    (fun _ => ?_) (fun h => absurd h (by decide))
  simp only [streamRecsCheck, streamRecCheck, generatedFire, hmm, streamNestedOk, streamRecCompare, bind_assoc, pure_bind,
    ↓reduceIte]
  refine specR_callNIH (C := C) ctsX fSrs srsParams [vv ctsRl, vv ctsOq, .const 0, vv ctsNc] srsBody
    [cellA C orl, cellA C oq, BitVec.ofNat 64 0, BitVec.ofNat 64 m.ctors.length] (by decide) rfl (by decide) hc.srs
    ⟨by simp [sev, Env.get_cons]; rfl, by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctsParams, ctxEnv],
      by simp [sev], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctsParams, ctxEnv], trivial⟩
    (PostSame C s2) (fun _ _ s' H' => s' = s2 ∧ H' = C.H)
    (fun a w s' st ⟨h1, h2⟩ => ⟨C.H, List.prefix_refl _, ⟨h1, rfl⟩, h2⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu srsParams _ rfl hlk)
      (srs_spec C hc.srs rc.rules orl hrl0 hrls m.ctors oq hcr hlen (by omega) _ 0 s2 rfl (by omega)))
    (fun _ w s3 H3 _ ⟨e1, e2⟩ => ?_)
  subst e1 e2
  refine UD.specR_heapLoadI' (C := C) ctsRcv _ orr _ hcr0 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctsParams, ctxEnv]) ?_
  refine UD.specR_heapLoadI' (C := C) ctsTyR _ (ocr + 2) _ hcvr.2.2 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C ocr 2) ?_
  refine UD.specR_heapLoadI' (C := C) ctsGcv _ (o + 1) _ ho2 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctsParams, ctxEnv]; exact cellA_add8 C o) ?_
  refine UD.specR_heapLoadI' (C := C) ctsTyG _ (oc + 2) _ hcv.2.2 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C oc 2) ?_
  by_cases hty : rc.cvR.type = cv.type
  swap
  · refine specR_ifI _ 0 (by
      simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      exact fun h => hty (Enc.idxW_inj h)) (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hty])
    (fun _ => ?_) (fun h => absurd h (by decide))
  simp only [hty, beq_self_eq_true, ↓reduceIte]
  refine UD.specR_heapLoadI' (C := C) ctsOrh _ o _ ho1 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctsParams, ctxEnv]) ?_
  have hnh : C.H[orh]? = some (BitVec.ofNat 64 rhss.length) := by simpa using hrh.1
  refine UD.specR_heapLoadI' (C := C) ctsNh (vv ctsOrh) orh _ hnh (by decide) (by simp [sev, Env.get_cons]) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hlay := hok.heapLay
  have hrhb : rhss.length < 2 ^ 61 := by
    rcases Nat.eq_zero_or_pos rhss.length with h0 | hpos
    · omega
    · have h1 := hrh.2 (rhss.length - 1) (by simp; omega)
      have := (List.getElem?_eq_some_iff.mp h1).1
      omega
  by_cases hlen2 : rhss.length = m.ctors.length
  swap
  · refine specR_ifI _ 0 (by
      simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      intro h; apply hlen2
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      exact this) (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by
      simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlen2])
    (fun _ => ?_) (fun h => absurd h (by decide))
  refine UD.specR_heapLoadI' (C := C) ctsRp _ (orr + 1) _ hrp.1 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctsParams, ctxEnv]; exact cellA_add8 C orr) ?_
  refine specR_callNIH (C := C) ctsX fSrr srrParams [vv ctsRl, vv ctsOrh, .const 0, vv ctsNc, vv ctsRp] srrBody
    [cellA C orl, cellA C orh, BitVec.ofNat 64 0, BitVec.ofNat 64 rhss.length, BitVec.ofNat 64 rc.rP] (by decide) rfl
    (by decide) hc.srr
    ⟨by simp [sev, Env.get_cons]; rfl, by simp +decide [sev, Env.get_cons], by simp [sev],
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctsParams, ctxEnv, hlen2], by simp [sev, Env.get_cons], trivial⟩
    (Decl.PostU C) (fun _ _ _ _ => True)
    (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu srrParams _ rfl hlk)
      (srr_spec C hok hc.sl hc.srr mode feG cv.levelParams rc.rP hrP rc.rules orl hrls rhss orh hrh (by omega) (by omega)
        _ 0 C.H s3 rfl (by omega) (List.prefix_refl _)))
    (fun _ w s4 H4 hp4 _ => ?_)
  have hok4 := ctxOK_H hok H4
  refine specR_flushTopI hok4 hpl false flushCaches rfl (by decide) ?_
  generalize flushedS false s4 = s5
  refine specR_atEntry fun t5 ht5 => ?_
  refine specR_feI (fe := fe₃) (by unfold litW; rw [hn3, hs3]; rfl) (Decl.envDen_congr hf3 ht3 ht5.sr.envd) ?_
  have hp4' : C.H <+: H4 := hp4
  refine specR_callNIH (C := ctxFe (ctxH C H4) fe₃) ctsX fCq cqParams [vv ctsQ] cqBody [cellA C oQ] (by decide) rfl
    (by decide) hc.cq.self ⟨by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctsParams, ctxEnv], trivial⟩
    (Decl.PostU (ctxFe (ctxH C H4) fe₃)) (fun _ _ _ _ => True)
    (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cqParams _ rfl hlk)
      (cq_spec (ctxFe (ctxH C H4) fe₃) (ctxOK_fe hok4 hf3 ht3) (by ctx_tr hc.cq) Q hQ oQ
        (pRep_mono hp4' (fun _ _ h => tblVRep_mono hp4' h) hq) hden hbd s5))
    (fun _ w s6 H6 hp6 _ => ?_)
  exact specR_returnI _ 0 rfl (fun t ht => ⟨H6, hp4'.trans hp6, sr_of_eq ht.sr rfl rfl rfl rfl, hf3, ht3, hb3, hn3, hs3, hr3⟩)

/-- After the block's tail: the constructors' environment the pops give back. -/
def PostCB (C : Ctx) (fe₂ : IFEnv) (r : IFEnv) (_ : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ EH envM H, C.EH <+: EH ∧ C.H <+: H ∧ CtxOK (ctxNew C r EH envM H) ∧ SR (ctxNew C r EH envM H) s' st ∧
    TblGate r ∧ FlagsOK r ∧ LitsPinned r C.pins ∧ (∀ n, r.find? n = fe₂.find? n) ∧
    (∀ n, r.findTable? n = fe₂.findTable? n)

theorem postCB_locals (C : Ctx) (fe₂ : IFEnv) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostCB C fe₂ a w s' st → PostCB C fe₂ a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨EH, envM, H, h1, h2, h3, h4, h5⟩ => ⟨EH, envM, H, h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl, h5⟩

theorem ctb_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ctbLocals → (ctxEnv C ++ ctbParams.zip vals).get x = none :=
  Knot.params_none C ctbLocals ctbParams vals (by decide) (by decide)

set_option maxHeartbeats 64000000 in
/-- **`checkBlockTail`**: one member, one recursor at it, unnested. -/
theorem ctb_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hpl : C.saved = none) (hc : CTBCodes mode C) (hf : ConPanqueque.Front.FrontOK C)
    (hg : TblGate C.fe) (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins)
    (heqS : ∀ (H : List (BitVec 64)) (u v : LIdx) (s : AState) (lu lv : ConLeche.Level),
      denoteL s.store.ls u = some lu → denoteL s.store.ls v = some lv → CachesOK s →
      SpecR (σ := σ) (Pre (ctxH C H) s [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s (lvlEq? u v)
        (fun o w s' st => LLeq.PostOB (ctxH C H) o w s' st))
    (q : BlockPass) (p : BlockShape) (hqp : q.p = p) (hq1 : q.env1 = C.fe)
    (ms0 : MemberShape) (hms : p.members = [ms0]) (block : List IConstantInfo)
    (hsp : SplitOK p block) (osh : Nat) (hsh : ShapeRep C C.H osh p)
    (hlq : ms0.cvT.levelParams.length < 2 ^ 58) (hlr : ∀ rc ∈ p.recs, rc.cvR.levelParams.length < 2 ^ 59)
    (rc : RecShape) (hrecs : p.recs = [rc]) (orr : Nat) (hrr : RecRep C C.H orr rc) (hrP : rc.rP < 2 ^ 62)
    (hrl : rc.rules.length < 2 ^ 58)
    (ks : List ConLeche.Name) (hkl : ks.length = rc.cvR.levelParams.length)
    (hks : ∀ j (hj : j < rc.cvR.levelParams.length), denoteN C.St.ns rc.cvR.levelParams[j] = some (ks[j]'(by omega)))
    (lsr : ConLeche.Level) (hSd : denoteL C.St.ls p.resSort = some lsr) (hnc : p.numCtors < 2 ^ 63)
    (hnP : p.nP < 2 ^ 56)
    (opm : Nat) (hpm : BlkAt C.H opm (q.params.map Enc.idxW)) (hpml : q.params.length < 2 ^ 56)
    (ot : Nat) (htb : PRep C C.H ot (fun H o nf => NfRep C H o nf) q.tbl)
    (htl : q.tbl.length < 2 ^ 58) (hel : ∀ e ∈ q.tbl, e.ds.length < 2 ^ 58)
    (m : TargetMajor) (hcls : q.cls = [m]) (hmm : m.member = some 0) (hmc : m.ctors = ms0.ctors) (oq : Nat)
    (hcr : CtorsRep C C.H oq m.ctors)
    (hcsl : m.ctors.length < 2 ^ 58) (hnfc : ∀ c ∈ m.ctors, c.2 < 2 ^ 56)
    (hcden : ∀ c ∈ ms0.ctors, CVDen c.1 C.St) (hcnd : (ms0.ctors.map (·.1.name)).Nodup)
    (hcnew : ∀ c ∈ ms0.ctors, C.fe.find? c.1.name = none)
    (olp : Nat) (hlp : EBlk C.H olp (ms0.cvT.levelParams.map Enc.idxW)) (pp : Nat)
    (hpf : BlkAt C.H pp (m.pfvs.map Enc.idxW)) (hppl : m.pfvs.length < 2 ^ 58) (pa : Nat)
    (hA : BlkAt C.H pa (m.ds.map Enc.idxW)) (hdl : m.ds.length < 2 ^ 56)
    (osl : Nat) (hsb : SlotBlk C C.H osl q.rd.slots) (hsl : q.rd.slots.length < 2 ^ 56)
    (hcb : ∀ sl ∈ q.rd.slots, ∀ c C' ihs, sl = .minor c C' ihs → c < 2 ^ 63 ∧ ihs.length < 2 ^ 63) (k0 : ClassKey)
    (hsl0 : q.rd.slots[0]? = some (.motive k0))
    (om : Nat) (hM : PtrsRep C C.H om (MemberRep C C.H) p.members) (hnk : p.nP + p.k < 2 ^ 56)
    (hni : m.nIdx < 2 ^ 56) (hnpc : m.nPc < 2 ^ 62) (hni0 : ms0.nIdx < 2 ^ 56)
    (hcvd : ∀ (xs : List ClassCtor) (el : LIdx) (pre : List EIdx) s s' cv,
      classRecTyOk mode (consSumCtors p.nP ms0.cvT.name ms0.ctors C.fe)
        ⟨p.nP, q.params, [{ m with nfs := q.tbl }], [ms0.cvT.type], q.rd.slots, [xs], el, pre⟩
        p.k rc rc.cvR 0 s = .ok (cv, s') → (denoteE s'.store cv.type).isSome = true)
    (hrc0 : q.rd.recCls = [0]) (hnest : blockNestedBit p q.kinds = false)
    (Q : List IProjTable) (hQ : Q.length ≤ 1) (oQ : Nat)
    (hqQ : PRep C C.H oQ (fun H o t => TblVRep C H o t) Q)
    (hden : ∀ t ∈ Q, ∃ ks : List ConLeche.Name, ∃ hkl : ks.length = t.levelParams.length,
      ∀ j (hj : j < t.levelParams.length), denoteN C.St.ns t.levelParams[j] = some (ks[j]'(by rw [hkl]; exact hj)))
    (hbd : ∀ t ∈ Q, t.levelParams.length < 2 ^ 62 ∧ t.numParams < 2 ^ 62 ∧ t.numFields < 2 ^ 64 ∧ t.bodies.size < 2 ^ 58)
    (s : AState) :
    SpecR (σ := σ) (Pre C s (ctbParams.zip ([cellA C osh, cellA C orr, cellA C opm, cellA C ot,
        BitVec.ofNat 64 q.tbl.length, cellA C oq, BitVec.ofNat 64 m.ctors.length, Enc.idxW m.lvls, cellA C olp,
        Enc.idxW ms0.cvT.type, cellA C pp, BitVec.ofNat 64 m.pfvs.length, cellA C pa, BitVec.ofNat 64 m.ds.length,
        Enc.idxW ms0.cvT.name, cellA C osl, BitVec.ofNat 64 q.rd.slots.length, cellA C om, BitVec.ofNat 64 p.numCtors,
        BitVec.ofNat 64 m.nIdx, Enc.idxW m.ind, BitVec.ofNat 64 m.nPc] ++
        [BitVec.ofNat 64 p.nP, Enc.idxW p.resSort, cellA C oQ]))) (ctbBody C) s
      (checkBlockTail mode block q Q) (PostCB C (consSumCtors p.nP ms0.cvT.name ms0.ctors C.fe)) := by
  refine specR_prologue (postCB_locals C _) (ctb_none C _) ?_
  rw [checkBlockTail_eq, hqp, hq1, hnest, hcls]
  have hk1 : p.k = 1 := by simp [BlockShape.k, hms]
  refine specR_callNIH (C := C) ctbX fBis bisParams [vv ctbOm, vv ctbNP, vv ctbRs] (bisBody C)
    [cellA C om, BitVec.ofNat 64 p.nP, Enc.idxW p.resSort] (by decide) rfl (by decide) hc.bis.self
    ⟨by simp +decide [sev, Env.get, ctbParams, ctxEnv], by simp +decide [sev, Env.get, ctbParams, ctxEnv],
      by simp +decide [sev, Env.get, ctbParams, ctxEnv], trivial⟩
    (Decl.PostU C) (fun _ _ _ _ => True)
    (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu bisParams _ rfl hlk)
      (bis_spec mode ra C hok hs hc.k hc.ac hc.bis heqS p ms0 hms om (by rw [← hms]; exact hM) lsr hSd (by omega) hni0 s))
    (fun _ w s1 H1 hp1 _ => ?_)
  have hp1' : C.H <+: H1 := hp1
  have hok1 := ctxOK_H hok H1
  refine specR_congr (m' := pure (consSumCtors p.nP ms0.cvT.name (ms0.ctors.drop 0) C.fe) >>= fun fe₂ =>
      flushCaches >>= fun _ => genRecCheck mode fe₂ p false q.params q.tbl q.rd [m] block >>= fun r => tailS mode p Q r)
    (by simp [checkBlockRec, BlockShape.ctorGroups, hms, consBlockCtors]) ?_
  refine specR_callNC (C := ctxH C H1) ctbX fConsCtors cscParams [vv ctbOq, .const 0, vv ctbNq, vv ctbNP, vv ctbNm]
    (cscBody C) [cellA C oq, BitVec.ofNat 64 0, BitVec.ofNat 64 ms0.ctors.length, BitVec.ofNat 64 p.nP,
      Enc.idxW ms0.cvT.name] (by decide) rfl (by decide) (by ctx_tr hc.csc.self)
    ⟨by simp +decide [sev, Env.get_cons, Env.get, ctbParams, ctxEnv], by simp [sev],
      by simp +decide [sev, Env.get_cons, Env.get, ctbParams, ctxEnv, hmc],
      by simp +decide [sev, Env.get_cons, Env.get, ctbParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, ctbParams, ctxEnv], trivial⟩
    (fun a w s' st => (pure (consSumCtors p.nP ms0.cvT.name (ms0.ctors.drop 0) C.fe) : AM IFEnv) s1 = .ok (a, s') ∧
      PostEnv (ctxH C H1) a w s' st)
    (fun r w s' C' => r = consSumCtors p.nP ms0.cvT.name ms0.ctors C.fe ∧ s' = s1 ∧ ∃ EH envM H,
      C' = ctxNew (ctxH C H1) r EH envM H ∧ C.EH <+: EH ∧ H1 <+: H ∧ CtxOK (ctxNew (ctxH C H1) r EH envM H) ∧
      TblGate r ∧ FlagsOK r ∧ LitsPinned r C.pins)
    (fun a w s' st ⟨hrun, EH, envM, H, h1, h2, h3, h4, h5, h6, h7⟩ => by
      obtain ⟨e1, e2⟩ := AM.pure_ok hrun
      exact ⟨_, ⟨by rw [e1, List.drop_zero], e2, EH, envM, H, rfl, h1, h2, h3, h5, h6, h7⟩, h4⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu cscParams _ rfl hlk)
      (csc_spec (ctxH C H1) (by ctx_tr hc.csc) p.nP (by omega) ms0.cvT.name ms0.ctors oq (by rw [← hmc]; exact ctorsRep_mono hp1' hcr)
        (by rw [← hmc]; exact hcsl) hcden hcnd _ 0 C.fe C.EH C.envM H1 s1 rfl (by omega) (List.prefix_refl _)
        (List.prefix_refl _) hok1 hg hF hL (by simpa using hcnew))))
    (fun r w s2 C2 ⟨er, es, EH2, envM2, H2, eC, hpE2, hp2, hok2, hg2, hF2, hL2⟩ => ?_)
  subst eC er es
  have hpC2 : C.H <+: H2 := hp1'.trans hp2
  refine specR_flushTopI hok2 hpl false flushCaches rfl (by decide) ?_
  generalize flushedS false s2 = s3
  set fe₂ := consSumCtors p.nP ms0.cvT.name ms0.ctors C.fe with hfe₂
  set C2 := ctxNew (ctxH C H1) fe₂ EH2 envM2 H2 with hC2
  refine specR_callNC (C := C2) ctbR fGa gaParams
    [vv ctbSh, vv ctbOrr, vv ctbPm, vv ctbOt, vv ctbNt, vv ctbOq, vv ctbNq, vv ctbLv, vv ctbOlp, vv ctbTy0,
      vv ctbPp, vv ctbNpp, vv ctbPa, vv ctbNd, vv ctbNm, vv ctbOsl, vv ctbNsl, vv ctbOm, vv ctbNc, vv ctbNi,
      vv ctbInd, vv ctbNpc] gaBody [cellA C osh, cellA C orr, cellA C opm, cellA C ot,
        BitVec.ofNat 64 q.tbl.length, cellA C oq, BitVec.ofNat 64 m.ctors.length, Enc.idxW m.lvls, cellA C olp,
        Enc.idxW ms0.cvT.type, cellA C pp, BitVec.ofNat 64 m.pfvs.length, cellA C pa, BitVec.ofNat 64 m.ds.length,
        Enc.idxW ms0.cvT.name, cellA C osl, BitVec.ofNat 64 q.rd.slots.length, cellA C om, BitVec.ofNat 64 p.numCtors,
        BitVec.ofNat 64 m.nIdx, Enc.idxW m.ind, BitVec.ofNat 64 m.nPc] (by decide) rfl (by decide) (by ctx_tr hc.ga.self)
    ⟨by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctbParams, ctxEnv], trivial⟩
    (PostGR { m with nfs := q.tbl } C2)
    (fun r w s' C' => ∃ EH envM H o, C' = ctxNew C2 r.1 EH envM H ∧ C2.EH <+: EH ∧ C2.H <+: H ∧
      CtxOK (ctxNew C2 r.1 EH envM H) ∧ TblGate r.1 ∧ FlagsOK r.1 ∧ LitsPinned r.1 C2.pins ∧
      (∀ n, r.1.find? n = C2.fe.find? n) ∧ (∀ n, r.1.findTable? n = C2.fe.findTable? n) ∧
      ∃ cv rhss orh oc, r.2 = [(cv, { m with nfs := q.tbl }, rhss)] ∧ w = cellA C o ∧ H[o]? = some (cellA C orh) ∧
      H[o + 1]? = some (cellA C oc) ∧ BlkAt H orh (rhss.map Enc.idxW) ∧ CVRep C H oc cv)
    (fun r w s' st ⟨EH, envM, H, o, h1, h2, h3, h4, h5⟩ => ⟨_, ⟨EH, envM, H, o, rfl, h1, h2, h3, h5⟩, h4⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu gaParams _ rfl hlk)
      (ga_spec mode ra C2 hok2 hs hpl (by ctx_tr hc.ga) (by obtain ⟨⟩ := hf; constructor <;> assumption) hg2 hF2 hL2 p ms0 hms block hsp osh (shapeRep_mono hpC2 hsh)
        hlq hlr rc hrecs orr (recRep_mono hpC2 hrr) ks hkl hks lsr hSd hnc q.params opm (blkAt_mono hpm hpC2) hpml
        q.tbl ot (pRep_mono hpC2 (fun _ _ h => nfRep_mono hpC2 h) htb) htl hel m hmm oq (ctorsRep_mono hpC2 hcr) hcsl
        hnfc olp (eblk_mono hlp hpC2) pp (blkAt_mono hpf hpC2) hppl pa (blkAt_mono hA hpC2) hdl q.rd osl
        (slotBlk_mono hpC2 hsb) hsl hcb k0 hsl0 om (ptrsRep_mono hpC2 (fun _ _ h => memberRep_mono hpC2 h) hM) hnk hni hnpc
        hcvd hrc0 s3 hu.pins))
    (fun r w s4 C3 ⟨EH3, envM3, H3, o, eC, hpE3, hp3, hok3, hg3, hF3, hL3, hf3, ht3, cv, rhss, orh, oc, er, ew, ho1, ho2,
      hrh, hcv⟩ => ?_)
  subst eC ew
  obtain ⟨fe₂b, out⟩ := r
  simp only at er hf3 ht3 hg3 hF3 hL3 hok3 ⊢
  subst er
  have hp3' : H2 <+: H3 := hp3
  have hpC3 : C.H <+: H3 := hpC2.trans hp3'
  set C3 := ctxNew C2 fe₂b EH3 envM3 H3 with hC3
  refine specR_congr (m' := tailS mode p Q (C3.fe, [(cv, { m with nfs := q.tbl }, rhss)]) >>= fun r => pure r)
    (by rw [bind_pure]; rfl) ?_
  refine specR_callNC (C := C3) ctbX fCts ctsParams [vv ctbR, vv ctbOrr, vv ctbOq, vv ctbNq, vv ctbSh, vv ctbQ]
    (ctsBody C) [cellA C o, cellA C orr, cellA C oq, BitVec.ofNat 64 m.ctors.length, cellA C osh, cellA C oQ]
    (by decide) rfl (by decide) (by ctx_tr hc.cts.self)
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctbParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctbParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctbParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctbParams, ctxEnv],
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, ctbParams, ctxEnv], trivial⟩
    (PostTS C3)
    (fun r w s' C' => ∃ H, C' = ctxNew C3 r C3.EH C3.envM H ∧ C3.H <+: H ∧ (∀ n, r.find? n = C3.fe.find? n) ∧
      (∀ n, r.findTable? n = C3.fe.findTable? n) ∧ r.base = C3.fe.base ∧ r.natLit = C3.fe.natLit ∧
      r.strLit = C3.fe.strLit ∧ (∀ n, r.rawTable? n = C3.fe.rawTable? n))
    (fun r w s' st ⟨H, h1, h2, h3⟩ => ⟨_, ⟨H, rfl, h1, h3⟩, h2⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ctsParams _ rfl hlk)
      (cts_spec mode C3 hok3 hpl (by ctx_tr hc.cts) p hk1 osh (shapeRep_mono hpC3 hsh).2.2.2.2.2.2 rc hrecs orr
        (recRep_mono hpC3 hrr) hrP hrl { m with nfs := q.tbl } hmm oq (ctorsRep_mono hpC3 hcr) hcsl cv rhss o orh oc
        ho1 ho2 hrh hcv Q hQ oQ (pRep_mono hpC3 (fun _ _ h => tblVRep_mono hpC3 h) hqQ) hden hbd s4))
    (fun fe₃ w s5 C5 ⟨H5, eC, hp5, hf5, ht5, hb5, hn5, hs5, hr5⟩ => ?_)
  subst eC
  have hok5 : CtxOK (ctxNew C3 fe₃ C3.EH C3.envM H5) := ctxOK_fe (ctxOK_H hok3 H5) hf5 ht5
  exact specR_returnI _ w (by simp [sev, Env.get_cons]) (fun t ht => ⟨EH3, envM3, H5, hpE2.trans hpE3,
    hpC3.trans hp5, hok5, sr_of_eq ht.sr rfl rfl rfl rfl,
    fun n t' h' => by rw [hf5]; rw [hr5] at h'; exact hg3 n t' h',
    FlagsOK.of_same hF3 (by rw [hb5]; rfl) hf5 hn5 hs5, by unfold LitsPinned; rw [hb5]; exact hL3,
    fun n => (hf5 n).trans (hf3 n), fun n => (ht5 n).trans (ht3 n)⟩)

end

end ConPanqueque.T.Ind
