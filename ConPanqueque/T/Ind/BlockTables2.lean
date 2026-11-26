import ConPanqueque.T.Ind.BlockTables

/-!
# The check of a projection table (`checkStructProjTable`)

`csbBody`: each body free of free variables, its level parameters the structure's, resolving, its loose
variables below `nP + 1` (a failing body hangs).  `csptBody`: the bodies checked, one per field, the structure
found and its table slot empty.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def csbB := ofString "csb_b"
def csbI := ofString "csb_i"
def csbN := ofString "csb_n"
def csbL := ofString "csb_l"
def csbLn := ofString "csb_ln"
def csbNp1 := ofString "csb_np1"
def csbE := ofString "csb_e"
def csbR := ofString "csb_r"
def csbX := ofString "csb_x"
def fCsb := ofString "tableBodiesOk"

def csbParams : List MlS := [csbB, csbI, csbN, csbL, csbLn, csbNp1]
def csbLocals : List MlS := [csbE, csbR, csbX]

def csbBody : ProgHOL 64 := prologue csbLocals
  (.ite (.cmp .lower (vv csbI) (vv csbN))
    (.seq (.assign .local csbE (.load .one (.op .add [vv csbB, .op .add [.panop .mul [vv csbI, .const 8], .const 8]])))
    (callR csbR ExM.fHasFvar [.const (BitVec.ofNat 64 coreWalkFuel), vv csbE]
    (.ite (.cmp .notEqual (vv csbR) (.const 0)) hang
    (callR csbR fAt [vv csbE, vv csbL, vv csbLn]
    (.ite (.cmp .equal (vv csbR) (.const 0)) hang
    (callR csbR fCrff [vv csbE]
    (.ite (.cmp .equal (vv csbR) (.const 0)) hang
    (callR csbR ExM.fLBB [.const (BitVec.ofNat 64 coreWalkFuel), vv csbNp1, vv csbE]
    (.ite (.cmp .equal (vv csbR) (.const 0)) hang
    (.seq (.call (some (some (.local, csbX), none)) fCsb
        [vv csbB, .op .add [vv csbI, .const 1], vv csbN, vv csbL, vv csbLn, vv csbNp1])
      (.return (.const 1))))))))))))
    (.return (.const 1)))

structure CSBCodes (C : Ctx) : Prop where
  lbb : C.code.lookup ExM.fLBB = some ([pFu, ExM.pKb, pH].map (fun p => (p, ShapeHOL.one)), ExM.lbbBody, .one)
  cB : ExB.CodesB C (ExB.bodyB C)
  bvb : C.code.lookup ExB.fBvarB = some ([(pFu, .one), (pH, .one)], ExB.bvbBody C, .one)
  hf : C.code.lookup ExM.fHasFvar = some ([pFu, pH].map (fun p => (p, ShapeHOL.one)), ExM.hasFvarBody, .one)
  cF : ExF.CodesF C (ExF.bodyF C)
  fvb : C.code.lookup ExF.fFvarB = some ([(pFu, .one), (pH, .one)], ExF.fvbBody C, .one)
  atc : C.code.lookup fAt = some (atParams.map (fun p => (p, ShapeHOL.one)), atBody, .one)
  al : AlCodes C
  crff : C.code.lookup fCrff = some ([crffE].map (fun p => (p, ShapeHOL.one)), crffBody, .one)
  crf : CrfCodes C
  self : C.code.lookup fCsb = some (csbParams.map (fun p => (p, ShapeHOL.one)), csbBody, .one)

def cstT := ofString "cst_t"
def cstNm := ofString "cst_nm"
def cstLp := ofString "cst_lp"
def cstLn := ofString "cst_ln"
def cstNp := ofString "cst_np"
def cstNf := ofString "cst_nf"
def cstBp := ofString "cst_bp"
def cstBn := ofString "cst_bn"
def cstNp1 := ofString "cst_np1"
def cstX := ofString "cst_x"
def cstY := ofString "cst_y"
def cstZ := ofString "cst_z"
def fCst := ofString "checkStructProjTable"

def cstParams : List MlS := [cstT]
def cstLocals : List MlS := [cstNm, cstLp, cstLn, cstNp, cstNf, cstBp, cstBn, cstNp1, cstX, cstY, cstZ]

def cstBody (C : Ctx) : ProgHOL 64 := prologue cstLocals
  (.seq (.assign .local cstNm (.load .one (vv cstT)))
  (.seq (.assign .local cstLp (.load .one (.op .add [vv cstT, .const 8])))
  (.seq (.assign .local cstLn (.load .one (vv cstLp)))
  (.seq (.assign .local cstNp (.load .one (.op .add [vv cstT, .const 16])))
  (.seq (.assign .local cstNf (.load .one (.op .add [vv cstT, .const 32])))
  (.seq (.assign .local cstBp (.load .one (.op .add [vv cstT, .const 40])))
  (.seq (.assign .local cstBn (.load .one (vv cstBp)))
  (.seq (.assign .local cstNp1 (.op .add [vv cstNp, .const 1]))
  (.seq (.call (some (some (.local, cstX), none)) fCsb [vv cstBp, .const 0, vv cstBn, vv cstLp, vv cstLn, vv cstNp1])
  (.ite (.cmp .notEqual (vv cstBn) (vv cstNf)) hang
  (envFindP C cstY (vv cstNm)
  (.ite (.cmp .equal (vv cstY) (.const 0)) hang
  (tblFindP C cstZ (vv cstNm)
  (.ite (.cmp .notEqual (vv cstZ) (.const 0)) hang
  (.return (.const 0))))))))))))))))

section
variable {σ : Type}

theorem csb_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ csbLocals → (ctxEnv C ++ csbParams.zip vals).get x = none :=
  Knot.params_none C csbLocals csbParams vals (by decide) (by decide)

set_option maxHeartbeats 32000000 in
/-- **The bodies' scoping** from `i` on. -/
theorem csb_spec (C : Ctx) (hok : CtxOK C) (hc : CSBCodes C) (lps : List NIdx) (ol : Nat) (ks : List ConLeche.Name)
    (hkl : ks.length = lps.length) (hks : ∀ j (hj : j < lps.length), denoteN C.St.ns lps[j] = some (ks[j]'(by omega)))
    (hlb : BlkAt C.H ol (lps.map Enc.idxW)) (hll : lps.length < 2 ^ 62) (nP : Nat) (hnP : nP + 1 < 2 ^ 63)
    (bs : List EIdx) (ob : Nat) (hbs : BlkAt C.H ob (bs.map Enc.idxW)) (hbl : bs.length < 2 ^ 58) :
    ∀ f i (H : List (BitVec 64)) (s : AState), bs.length - i = f → i ≤ bs.length → C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (csbParams.zip [cellA C ob, BitVec.ofNat 64 i, BitVec.ofNat 64 bs.length,
        cellA C ol, BitVec.ofNat 64 lps.length, BitVec.ofNat 64 (nP + 1)])) csbBody s
        ((bs.drop i).allM fun b => do
          pure (!(← hasFvarFast coreWalkFuel b) && (← allLevelParamsDefined lps b) &&
            (← constsResolveFFast C.fe b) && (← looseBVarsBoundedFast coreWalkFuel (nP + 1) b)))
        (PostT (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp
    have hin : i = bs.length := by omega
    subst hin
    refine specR_prologue (postT_locals _) (csb_none _ _) ?_
    have hlw := nd_lt_iff bs.length bs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, csbParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨rfl, H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp
    have hin : i < bs.length := by omega
    refine specR_prologue (postT_locals _) (csb_none _ _) ?_
    have hlw := nd_lt_iff i bs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, csbParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have he := hbs.2 i (by simp; omega)
    simp only [List.getElem_map] at he
    refine UD.specR_heapLoadI' (C := ctxH C H) csbE _ (ob + 1 + i) _ (get_prefix he hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, csbParams, ctxEnv]; exact cellA_mulIdx C ob i (by omega)) ?_
    rw [List.drop_eq_getElem_cons hin, allM_cons_ite]
    simp only [bind_assoc]
    have hokH := ctxOK_H hok H
    refine specR_callNIH (C := ctxH C H) csbR ExM.fHasFvar [pFu, pH]
      [.const (BitVec.ofNat 64 coreWalkFuel), vv csbE] ExM.hasFvarBody
      [BitVec.ofNat 64 coreWalkFuel, Enc.idxW bs[i]] (by decide) rfl (by decide) hc.hf
      ⟨rfl, (by simp +decide [Env.get_cons]), trivial⟩ (ExM.PostB (ctxH C H)) (fun b w _ H' => H' = H ∧ w = boolW b)
      (fun b w s' st ⟨hw, hsr⟩ => ⟨H, List.prefix_refl _, ⟨rfl, by rw [hw]; cases b <;> rfl⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
        (ExM.hasFvar_spec (ctxH C H) hokH (by ctx_tr hc.cF) hc.fvb s coreWalkFuel bs[i] CV.coreWalkFuel_lt))
      (fun a w s1 H1 hp1 ⟨eH1, hw⟩ => ?_)
    subst hw; subst H1
    cases a
    swap
    · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => specR_hangI) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_atEntry fun t1 ht1 => ?_
    have hL : LpsAt (ctxH C H) s1 ol lps ks :=
      ⟨blkAt_mono hlb hp, hkl, fun j hj => denoteN_ext (hks j hj) ht1.sr.floor, hll⟩
    refine specR_callNIH (C := ctxH C H) csbR fAt atParams [vv csbE, vv csbL, vv csbLn] atBody
      [Enc.idxW bs[i], cellA C ol, BitVec.ofNat 64 lps.length] (by decide) rfl (by decide) hc.atc
      ⟨by simp +decide [Env.get_cons], by simp +decide [Env.get_cons, Env.get, csbParams, ctxEnv],
        by simp +decide [Env.get_cons, Env.get, csbParams, ctxEnv], trivial⟩ (PostB (ctxH C H)) (fun b w _ _ => w = boolW b)
      (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu atParams _ rfl hlk)
        (at_spec (ctxH C H) hokH (by ctx_tr hc.al) s1 bs[i] hL))
      (fun b2 w s2 H2 hp2 hw => ?_)
    subst hw
    have hp2' : H <+: H2 := hp2
    cases b2
    · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => specR_hangI) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    have hok2 := ctxOK_H hok H2
    refine specR_callNIH (C := ctxH C H2) csbR fCrff [crffE] [vv csbE] crffBody [Enc.idxW bs[i]] (by decide) rfl
      (by decide) hc.crff ⟨by simp +decide [Env.get_cons], trivial⟩ (PostB (ctxH C H2)) (fun b w _ _ => w = boolW b)
      (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [crffE] _ rfl hlk)
        (crff_spec (ctxH C H2) hok2 (by ctx_tr hc.crf) s2 bs[i]))
      (fun b3 w s3 H3 hp3 hw => ?_)
    subst hw
    have hp3' : H2 <+: H3 := hp3
    cases b3
    · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => specR_hangI) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    have hok3 := ctxOK_H hok H3
    refine specR_callNIH (C := ctxH C H3) csbR ExM.fLBB [pFu, ExM.pKb, pH]
      [.const (BitVec.ofNat 64 coreWalkFuel), vv csbNp1, vv csbE] ExM.lbbBody
      [BitVec.ofNat 64 coreWalkFuel, BitVec.ofNat 64 (nP + 1), Enc.idxW bs[i]] (by decide) rfl (by decide) hc.lbb
      ⟨rfl, by simp +decide [Env.get_cons, Env.get, csbParams, ctxEnv], by simp +decide [Env.get_cons], trivial⟩
      (ExM.PostB (ctxH C H3)) (fun b w _ H' => H' = H3 ∧ w = boolW b)
      (fun b w s' st ⟨hw, hsr⟩ => ⟨H3, List.prefix_refl _, ⟨rfl, by rw [hw]; cases b <;> rfl⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, ExM.pKb, pH] _ rfl hlk)
        (ExM.lbb_spec (ctxH C H3) hok3 (by ctx_tr hc.cB) hc.bvb s3 coreWalkFuel (nP + 1) bs[i] CV.coreWalkFuel_lt hnP))
      (fun b4 w s4 H4 hp4 ⟨eH4, hw⟩ => ?_)
    subst hw; subst H4
    cases b4
    · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => specR_hangI) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Bool.not_false, Bool.and_self, pure_bind, ite_true]
    refine specR_congr (m' := ((bs.drop (i + 1)).allM fun b => do
          pure (!(← hasFvarFast coreWalkFuel b) && (← allLevelParamsDefined lps b) &&
            (← constsResolveFFast C.fe b) && (← looseBVarsBoundedFast coreWalkFuel (nP + 1) b))) >>= fun r => pure r)
      (by simp only [bind_pure]) ?_
    refine specR_callNIH (C := ctxH C H3) csbX fCsb csbParams
      [vv csbB, .op .add [vv csbI, .const 1], vv csbN, vv csbL, vv csbLn, vv csbNp1] csbBody
      [cellA C ob, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 bs.length, cellA C ol, BitVec.ofNat 64 lps.length,
        BitVec.ofNat 64 (nP + 1)] (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, csbParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, csbParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, csbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, csbParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, csbParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, csbParams, ctxEnv], trivial⟩
      (PostT (ctxH C H3)) (fun r _ _ _ => r = true) (fun r w s' st ⟨h0, H', hp', hsr⟩ => ⟨H', hp', h0, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu csbParams _ rfl hlk)
        (ih (i + 1) H3 s4 (by omega) (by omega) (hp.trans (hp2'.trans hp3'))))
      (fun r w s5 H5 hp5 hr => ?_)
    subst hr
    exact specR_returnI _ 1 rfl (fun t ht => ⟨rfl, H5, hp2'.trans (hp3'.trans hp5), sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

structure CSTCodes (C : Ctx) : Prop where
  csb : CSBCodes C
  g : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  p : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  self : C.code.lookup fCst = some (cstParams.map (fun p => (p, ShapeHOL.one)), cstBody C, .one)

section
variable {σ : Type}

theorem cst_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cstLocals → (ctxEnv C ++ cstParams.zip vals).get x = none :=
  Knot.params_none C cstLocals cstParams vals (by decide) (by decide)

set_option maxHeartbeats 32000000 in
/-- **`checkStructProjTable`** at the context's environment. -/
theorem cst_spec (C : Ctx) (hok : CtxOK C) (hc : CSTCodes C) (t : IProjTable) (o : Nat) (htv : TblVRep C C.H o t)
    (ks : List ConLeche.Name) (hkl : ks.length = t.levelParams.length)
    (hks : ∀ j (hj : j < t.levelParams.length), denoteN C.St.ns t.levelParams[j] = some (ks[j]'(by omega)))
    (hll : t.levelParams.length < 2 ^ 62) (hnp : t.numParams < 2 ^ 62) (hnf : t.numFields < 2 ^ 64)
    (hbl : t.bodies.size < 2 ^ 58) (s : AState) :
    SpecR (σ := σ) (Pre C s (cstParams.zip [cellA C o])) (cstBody C) s (checkStructProjTable t C.fe) (Decl.PostU C) := by
  refine specR_prologue (Decl.postU_locals C) (cst_none C _) ?_
  obtain ⟨h0, ⟨ol, h1, hlb⟩, h2, -, h4, ⟨ob, h5, hbb⟩⟩ := htv
  refine UD.specR_heapLoadI' (C := C) cstNm _ o _ h0 (by decide) (by simp +decide [sev, Env.get, cstParams, ctxEnv]) ?_
  refine UD.specR_heapLoadI' (C := C) cstLp _ (o + 1) _ h1 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, cstParams, ctxEnv]; exact cellA_add8 C o) ?_
  have hll0 : C.H[ol]? = some (BitVec.ofNat 64 t.levelParams.length) := by simpa using hlb.1
  refine UD.specR_heapLoadI' (C := C) cstLn (vv cstLp) ol _ hll0 (by decide) (by simp [sev, Env.get_cons]) ?_
  refine UD.specR_heapLoadI' (C := C) cstNp _ (o + 2) _ h2 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, cstParams, ctxEnv]; exact cellA_add_ofNat C o 2) ?_
  refine UD.specR_heapLoadI' (C := C) cstNf _ (o + 4) _ h4 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, cstParams, ctxEnv]; exact cellA_add_ofNat C o 4) ?_
  refine UD.specR_heapLoadI' (C := C) cstBp _ (o + 5) _ h5 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, cstParams, ctxEnv]; exact cellA_add_ofNat C o 5) ?_
  have hbn : C.H[ob]? = some (BitVec.ofNat 64 t.bodies.size) := by simpa using hbb.1
  refine UD.specR_heapLoadI' (C := C) cstBn (vv cstBp) ob _ hbn (by decide) (by simp [sev, Env.get_cons]) ?_
  refine specR_assignI cstNp1 _ (BitVec.ofNat 64 (t.numParams + 1)) (by decide)
    (by simp +decide [sev, Env.get_cons]; exact word_add1_eq _) ?_
  unfold checkStructProjTable
  refine specR_congr (m' := ((t.bodies.toList.drop 0).allM fun b => do
      pure (!(← hasFvarFast coreWalkFuel b) && (← allLevelParamsDefined t.levelParams b) &&
        (← constsResolveFFast C.fe b) && (← looseBVarsBoundedFast coreWalkFuel (t.numParams + 1) b))) >>= fun scopedOk => _)
    (by rw [List.drop_zero]) ?_
  refine specR_callNIH (C := C) cstX fCsb csbParams [vv cstBp, .const 0, vv cstBn, vv cstLp, vv cstLn, vv cstNp1] csbBody
    [cellA C ob, BitVec.ofNat 64 0, BitVec.ofNat 64 t.bodies.toList.length, cellA C ol, BitVec.ofNat 64 t.levelParams.length,
      BitVec.ofNat 64 (t.numParams + 1)] (by decide) rfl (by decide) hc.csb.self
    ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], trivial⟩
    (PostT C) (fun r _ _ _ => r = true) (fun r w s' st ⟨h0, H', hp', hsr⟩ => ⟨H', hp', h0, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu csbParams _ rfl hlk)
      (by have h := csb_spec (σ := σ) C hok hc.csb t.levelParams ol ks hkl hks hlb hll t.numParams (by omega) t.bodies.toList ob
            hbb (by simpa using hbl) t.bodies.toList.length 0 C.H s (by omega) (by omega) (List.prefix_refl _)
          exact h))
    (fun r w s1 H1 hp1 hr => ?_)
  subst hr
  have hp1' : C.H <+: H1 := hp1
  have hok1 := ctxOK_H hok H1
  by_cases hsz : t.bodies.size = t.numFields
  swap
  · have hne : BitVec.ofNat 64 t.bodies.size ≠ BitVec.ofNat 64 t.numFields := fun e => hsz (by
      have := congrArg BitVec.toNat e; simp at this; omega)
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hsz])
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only [hsz, and_self, decide_true, ite_true, pure_bind]
  refine specR_envFindI hok1 hc.g hc.p cstY (vv cstNm) t.structName (by decide) (by simp +decide [sev, Env.get_cons])
    (by simp +decide [Env.get_cons, Env.get, cstParams, ctxEnv]; rfl) ?_
  have hrel := find_rel hok1 t.structName
  revert hrel
  rcases hfn : (ctxH C H1).fe.find? t.structName with _ | ci0
  · intro hrel
    simp only at hrel
    rw [hrel]
    exact specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI)
      (fun h => absurd h (by decide))
  intro ⟨o', hm, hci⟩
  rw [hm]
  refine specR_atEntry fun t1 ht1 => ?_
  have hoE : o' < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht1.sr.env.1.len
  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok1 hoE)
    (fun h => absurd rfl h) (fun _ => ?_)
  have hfs : (C.fe.find? t.structName).isSome = true := by
    show ((ctxH C H1).fe.find? t.structName).isSome = true; rw [hfn]; rfl
  simp only [hfs, ite_true, pure_bind]
  refine specR_tblFindI hok1 hc.g hc.p cstZ (vv cstNm) t.structName (by decide) (by simp +decide [sev, Env.get_cons])
    (by simp +decide [Env.get_cons, Env.get, cstParams, ctxEnv]; rfl) ?_
  have htr := tbl_rel hok1 t.structName
  revert htr
  rcases hft : (ctxH C H1).fe.findTable? t.structName with _ | tb0
  · intro htr
    simp only at htr
    rw [htr]
    refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    have hfn' : (C.fe.findTable? t.structName).isNone = true := by
      show ((ctxH C H1).fe.findTable? t.structName).isNone = true; rw [hft]; rfl
    simp only [hfn', ite_true]
    exact specR_returnI _ 0 rfl (fun t2 ht2 => ⟨H1, hp1', sr_of_eq ht2.sr rfl rfl rfl rfl⟩)
  intro ⟨o2, hm2, htb⟩
  rw [hm2]
  have hoE2 : o2 < C.EN := Nat.lt_of_lt_of_le (tblE_lt htb) ht1.sr.env.1.len
  exact specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok1 hoE2)
    (fun _ => specR_hangI) (fun h => absurd h (by decide))

end

end ConPanqueque.T.Ind
