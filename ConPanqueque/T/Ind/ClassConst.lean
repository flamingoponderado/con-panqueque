import ConPanqueque.T.Ind.GenMotive
import ConPanqueque.T.Decl.LitShape

/-!
# `classConstOk`: a generated constant, checked

`checkConstantVal`'s checks without the name guards (natOp, reduce, sorry), as `gccBody`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC
open ConPanqueque.V.Enc

def gccParams : List MlS := [cvQ]

def gccBody (C : Ctx) : ProgHOL 64 := prologue ccvLocals
  (.seq (.assign .local cvN (.load .one (vv cvQ)))
  (.seq (.assign .local cvL (.load .one (.op .add [vv cvQ, .const 8])))
  (.seq (.assign .local cvT (.load .one (.op .add [vv cvQ, .const 16])))
  (.seq (.assign .local cvLn (.load .one (vv cvL)))
  (envFindP C cvY (vv cvN)
  (.ite (.cmp .notEqual (vv cvY) (.const 0)) rejectP
  (callR cvR fLso [vv cvQ]
  (.ite (.cmp .equal (vv cvR) (.const 0)) rejectP
  (callR cvR fNdg [vv cvL, .const 0, vv cvLn]
  (.ite (.cmp .equal (vv cvR) (.const 0)) rejectP
  (callR cvR ExM.fLBB [.const (BitVec.ofNat 64 coreWalkFuel), .const 0, vv cvT]
  (.ite (.cmp .equal (vv cvR) (.const 0)) rejectP
  (callR cvR ExM.fHasFvar [.const (BitVec.ofNat 64 coreWalkFuel), vv cvT]
  (.ite (.cmp .notEqual (vv cvR) (.const 0)) rejectP
  (callR cvR fAt [vv cvT, vv cvL, vv cvLn]
  (.ite (.cmp .equal (vv cvR) (.const 0)) rejectP
  (callR cvR fCrff [vv cvT]
  (.ite (.cmp .equal (vv cvR) (.const 0)) rejectP
  (callR cvX fI [.const (BitVec.ofNat 64 checkFuel), .const 0, vv cvT]
  (callR cvX fEns [.const (BitVec.ofNat 64 checkFuel), .const 0, vv cvX]
  (.return (.const 0))))))))))))))))))))))

def fGcc := ofString "classConstOk"

/-! ## `classRecTyOk` (one class, one recursor) -/

def croRr := ofString "cro_rr"
def croNS := ofString "cro_ns"
def croPre := ofString "cro_pre"
def croPrl := ofString "cro_prl"
def croDs := ofString "cro_ds"
def croDn := ofString "cro_dn"
def croFt := ofString "cro_ft"
def croNi := ofString "cro_ni"
def croInd := ofString "cro_ind"
def croLv := ofString "cro_lv"
def croNP := ofString "cro_np"
def croTg := ofString "cro_tg"
def croRp := ofString "cro_rp"
def croMi := ofString "cro_mi"
def croG := ofString "cro_g"
def croCv := ofString "cro_cv"
def croNm := ofString "cro_nm"
def croLp := ofString "cro_lp"
def croTy0 := ofString "cro_ty0"
def croQ := ofString "cro_q"
def croU := ofString "cro_u"
def croB := ofString "cro_b"
def croOms := ofString "cro_oms"
def croFts := ofString "cro_fts"
def croOsl := ofString "cro_osl"
def fCro := ofString "classRecTyOk"

def croParams : List MlS := [croRr, croNS, croPre, croPrl, croNi, croNP, croOms, croFts, croOsl]
def croLocals : List MlS := [croTg, croRp, croMi, croG, croCv, croNm, croLp, croTy0, croQ, croU, croB]

def croBody (C : Ctx) : ProgHOL 64 := prologue croLocals
  (.seq (.assign .local croTg (.load .one (.op .add [vv croRr, .const 24])))
  (.ite (.cmp .equal (vv croTg) (.const 0))
  (.seq (.assign .local croRp (.load .one (.op .add [vv croRr, .const 8])))
  (.ite (.cmp .equal (vv croRp) (vv croNS))
  (.seq (.assign .local croMi (.load .one (.op .add [vv croRr, .const 16])))
  (.ite (.cmp .equal (vv croMi) (.op .add [vv croRp, vv croNi]))
  (.seq (.call (some (some (.local, croG), none)) Ind.fGrt [vv croPre, vv croPrl, vv croNP, vv croOms, vv croFts, vv croOsl, .const 0])
  (.seq (.assign .local croCv (.load .one (vv croRr)))
  (.seq (.assign .local croNm (.load .one (vv croCv)))
  (.seq (.assign .local croLp (.load .one (.op .add [vv croCv, .const 8])))
  (.seq (.assign .local croTy0 (.load .one (.op .add [vv croCv, .const 16])))
  (alloc3 C croQ (vv croNm) (vv croLp) (vv croG)
  (.seq (.call (some (some (.local, croU), none)) fGcc [vv croQ])
  (.seq (.call (some (some (.local, croB), none)) fD [(.const (BitVec.ofNat 64 checkFuel)), .const 0, vv croTy0, vv croG])
  (.ite (.cmp .equal (vv croB) (.const 0))
  hang
  (.return (vv croQ)))))))))))
  hang))
  hang))
  hang))

section
variable {σ : Type}

theorem gcc_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ccvLocals → (ctxEnv C ++ gccParams.zip vals).get x = none :=
  Knot.params_none C ccvLocals gccParams vals (by decide) (by decide)

set_option maxHeartbeats 16000000 in
theorem gcc_spec (mode : ConLeche.CheckMode) (C : Ctx) (hok : CtxOK C)
    (hg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hpr : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (ra : ConPanqueque.Hash.RuntimeAssumptions) (hs : C.side = false) (hk : KCodes C Comp.kBodies) (hac : Comp.AllCodes mode C)
    (LB : ProgHOL 64) (hcl : C.code.lookup fLso = some ([lsQ].map (fun p => (p, ShapeHOL.one)), LB, .one))
    (hndh : C.code.lookup fNdh = some (ndhParams.map (fun p => (p, ShapeHOL.one)), ndhBody, .one))
    (hndg : C.code.lookup fNdg = some (ndgParams.map (fun p => (p, ShapeHOL.one)), ndgBody, .one))
    (hlbb : C.code.lookup ExM.fLBB = some ([pFu, ExM.pKb, pH].map (fun p => (p, ShapeHOL.one)), ExM.lbbBody, .one))
    (hcB : ExB.CodesB C (ExB.bodyB C))
    (hbvb : C.code.lookup ExB.fBvarB = some ([(pFu, .one), (pH, .one)], ExB.bvbBody C, .one))
    (hhf : C.code.lookup ExM.fHasFvar = some ([pFu, pH].map (fun p => (p, ShapeHOL.one)), ExM.hasFvarBody, .one))
    (hcF : ExF.CodesF C (ExF.bodyF C))
    (hfvb : C.code.lookup ExF.fFvarB = some ([(pFu, .one), (pH, .one)], ExF.fvbBody C, .one))
    (hat : C.code.lookup fAt = some (atParams.map (fun p => (p, ShapeHOL.one)), atBody, .one)) (hal : AlCodes C)
    (hcrff : C.code.lookup fCrff = some ([crffE].map (fun p => (p, ShapeHOL.one)), crffBody, .one)) (hcrf : CrfCodes C)
    (hens : C.code.lookup fEns = some (kParams.map (fun p => (p, ShapeHOL.one)), ensBody, .one))
    (fe : IFEnv) (hfe : fe = C.fe) (cv : IConstantVal) (q o : Nat)
    (hn : C.H[q]? = some (Enc.idxW cv.name)) (hl : C.H[q + 1]? = some (cellA C o))
    (ht : C.H[q + 2]? = some (Enc.idxW cv.type)) (hb : BlkAt C.H o (cv.levelParams.map Enc.idxW))
    (hlen : cv.levelParams.length < 2 ^ 62) (ks : List ConLeche.Name) (hkl : ks.length = cv.levelParams.length)
    (hks : ∀ j (hj : j < cv.levelParams.length), denoteN C.St.ns cv.levelParams[j] = some (ks[j]'(by omega)))
    (hlso : ∀ (H : List (BitVec 64)) (s : AState), C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s [(lsQ, cellA C q)]) LB s (litShapeOk (.axiomInfo cv)) (PostB (ctxH C H)))
    (s : AState) :
    SpecR (σ := σ) (Pre C s (gccParams.zip [cellA C q])) (gccBody C) s
      (classConstOk mode fe cv) (PostU C) := by
  refine specR_prologue (postU_locals C) (gcc_none C _) ?_
  unfold classConstOk
  dsimp only
  refine UD.specR_heapLoadI' (C := C) cvN _ q _ hn (by decide) (by simp +decide [Env.get, gccParams, ctxEnv]) ?_
  refine UD.specR_heapLoadI' (C := C) cvL _ (q + 1) _ hl (by decide)
    (by simp +decide [sev, Env.get, gccParams, ctxEnv]; exact cellA_add8 C q) ?_
  refine UD.specR_heapLoadI' (C := C) cvT _ (q + 2) _ ht (by decide)
    (by simp +decide [sev, Env.get, gccParams, ctxEnv]; exact cellA_add_ofNat C q 2) ?_
  refine UD.specR_heapLoadI' (C := C) cvLn _ o _ hb.1 (by decide) (by simp +decide [Env.get]) ?_
  refine specR_envFindI hok hg hpr cvY (vv cvN) cv.name (by decide) (by simp +decide [Env.get])
    (by simp +decide [Env.get, gccParams, ctxEnv]) ?_
  have hrel := find_rel hok cv.name
  subst hfe
  revert hrel
  rcases hf : C.fe.find? cv.name with _ | ci
  · intro hrel
    simp only at hrel
    rw [hrel]
    refine specR_failIteT (c := false) _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd h (by decide)) (fun _ => rfl) (fun _ => ?_)
    simp only [pure_bind]
    -- litShapeOk
    refine specR_callNIH (C := ctxH C C.H) cvR fLso [lsQ] [vv cvQ] LB [cellA C q] (by decide) rfl (by decide) hcl
      ⟨(by simp +decide [Env.get, gccParams, ctxEnv]), trivial⟩ (PostB (ctxH C C.H)) (fun b w _ _ => w = boolW b)
      (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [lsQ] _ rfl hlk) (hlso C.H s (List.prefix_refl _)))
      (fun b w s3 H3 hp3 hw => ?_)
    subst hw
    refine specR_failIteF (c := b) _ (boolW (!b)) (by simp +decide [sev, Env.get]; exact eqz_b b)
      (boolW_not_eq _) (boolW_not_ne _) (fun _ => ?_)
    -- nameNodup
    have hp03 : C.H <+: H3 := hp3
    refine specR_callPure (C := ctxH C H3) cvR fNdg ndgParams [vv cvL, .const 0, vv cvLn] ndgBody
      [cellA C o, BitVec.ofNat 64 0, BitVec.ofNat 64 cv.levelParams.length] (nameNodup (cv.levelParams.drop 0))
      (by decide) rfl (by decide) hndg ⟨(by simp +decide [Env.get, gccParams, ctxEnv]), rfl, by simp +decide [Env.get, gccParams, ctxEnv], trivial⟩
      (PostB (ctxH C H3)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ndgParams _ rfl hlk)
        (ndg_spec C hndh hndg cv.levelParams o hlen _ 0 H3 s3 hp03 (blkAt_mono hb hp03) rfl (Nat.zero_le _)))
      (fun w H4 hp4 hw => ?_)
    subst hw
    refine specR_failIteF (c := nameNodup cv.levelParams) _ (boolW (!nameNodup cv.levelParams))
      (by simp +decide [sev, Env.get]; exact eqz_b _) (boolW_not_eq _) (boolW_not_ne _) (fun _ => ?_)
    -- looseBVarsBoundedFast
    have hok4 := ctxOK_H hok H4
    refine specR_callNIH (C := ctxH C H4) cvR ExM.fLBB [pFu, ExM.pKb, pH]
      [.const (BitVec.ofNat 64 coreWalkFuel), .const 0, vv cvT] ExM.lbbBody
      [BitVec.ofNat 64 coreWalkFuel, BitVec.ofNat 64 0, Enc.idxW cv.type] (by decide) rfl (by decide) hlbb
      ⟨rfl, rfl, (by simp +decide [Env.get, gccParams, ctxEnv]), trivial⟩ (ExM.PostB (ctxH C H4)) (fun b w _ H' => H' = H4 ∧ w = boolW b)
      (fun b w s' st ⟨hw, hsr⟩ => ⟨H4, List.prefix_refl _, ⟨rfl, by rw [hw]; cases b <;> rfl⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, ExM.pKb, pH] _ rfl hlk)
        (ExM.lbb_spec (ctxH C H4) hok4 (by ctx_tr hcB) hbvb s3 coreWalkFuel 0 cv.type CV.coreWalkFuel_lt (by decide)))
      (fun b w s5 H5 hp5 ⟨eH5, hw⟩ => ?_)
    subst hw; subst H5
    refine specR_failIteF (c := b) _ (boolW (!b)) (by simp +decide [sev, Env.get]; exact eqz_b b)
      (boolW_not_eq _) (boolW_not_ne _) (fun _ => ?_)
    -- hasFvarFast
    refine specR_callNIH (C := ctxH C H4) cvR ExM.fHasFvar [pFu, pH]
      [.const (BitVec.ofNat 64 coreWalkFuel), vv cvT] ExM.hasFvarBody
      [BitVec.ofNat 64 coreWalkFuel, Enc.idxW cv.type] (by decide) rfl (by decide) hhf
      ⟨rfl, (by simp +decide [Env.get, gccParams, ctxEnv]), trivial⟩ (ExM.PostB (ctxH C H4)) (fun b w _ H' => H' = H4 ∧ w = boolW b)
      (fun b w s' st ⟨hw, hsr⟩ => ⟨H4, List.prefix_refl _, ⟨rfl, by rw [hw]; cases b <;> rfl⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
        (ExM.hasFvar_spec (ctxH C H4) hok4 (by ctx_tr hcF) hfvb s5 coreWalkFuel cv.type CV.coreWalkFuel_lt))
      (fun b w s6 H6 hp6 ⟨eH6, hw⟩ => ?_)
    subst hw; subst H6
    refine specR_failIteT (c := b) _ (boolW b) (by simp +decide [sev, Env.get]; exact nez_b b)
      (boolW_ne _) (boolW_eq _) (fun _ => ?_)
    -- allLevelParamsDefined
    refine specR_atEntry fun t6 ht6 => ?_
    have hL : LpsAt (ctxH C H4) s6 o cv.levelParams ks :=
      ⟨blkAt_mono hb (hp03.trans hp4), hkl, fun j hj => denoteN_ext (hks j hj) ht6.sr.floor, hlen⟩
    refine specR_callNIH (C := ctxH C H4) cvR fAt atParams [vv cvT, vv cvL, vv cvLn] atBody
      [Enc.idxW cv.type, cellA C o, BitVec.ofNat 64 cv.levelParams.length] (by decide) rfl (by decide) hat
      ⟨(by simp +decide [Env.get, gccParams, ctxEnv]), (by simp +decide [Env.get, gccParams, ctxEnv]), by simp +decide [Env.get, gccParams, ctxEnv], trivial⟩ (PostB (ctxH C H4)) (fun b w _ _ => w = boolW b)
      (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu atParams _ rfl hlk)
        (at_spec (ctxH C H4) hok4 (by ctx_tr hal) s6 cv.type hL))
      (fun b w s7 H7 hp7 hw => ?_)
    subst hw
    refine specR_failIteF (c := b) _ (boolW (!b)) (by simp +decide [sev, Env.get]; exact eqz_b b)
      (boolW_not_eq _) (boolW_not_ne _) (fun _ => ?_)
    -- constsResolveFFast
    have hok7 := ctxOK_H hok H7
    refine specR_callNIH (C := ctxH C H7) cvR fCrff [crffE] [vv cvT] crffBody [Enc.idxW cv.type] (by decide) rfl
      (by decide) hcrff ⟨(by simp +decide [Env.get, gccParams, ctxEnv]), trivial⟩ (PostB (ctxH C H7)) (fun b w _ _ => w = boolW b)
      (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [crffE] _ rfl hlk)
        (crff_spec (ctxH C H7) hok7 (by ctx_tr hcrf) s7 cv.type))
      (fun b w s8 H8 hp8 hw => ?_)
    subst hw
    refine specR_failIteF (c := b) _ (boolW (!b)) (by simp +decide [sev, Env.get]; exact eqz_b b)
      (boolW_not_eq _) (boolW_not_ne _) (fun _ => ?_)
    exact specR_inferEnsI mode C hok ra hs hk hac hens H8 (hp03.trans (hp4.trans (hp7.trans hp8))) cv.type
      (by simp +decide [Env.get, gccParams, ctxEnv]) (by decide)
  · intro ⟨o', hm, hci⟩
    rw [hm]
    refine specR_atEntry fun t ht => ?_
    have hoE : o' < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
    refine specR_failIteT (c := true) _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
      (fun _ => by decide) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))

/-- **`classConstOk`**, `litShapeOk` discharged. -/
theorem gcc_full (mode : ConLeche.CheckMode) (C : Ctx) (hok : CtxOK C)
    (hg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hpr : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (ra : ConPanqueque.Hash.RuntimeAssumptions) (hs : C.side = false) (hk : KCodes C Comp.kBodies)
    (hac : Comp.AllCodes mode C)
    (hcl : C.code.lookup fLso = some ([lsQ].map (fun p => (p, ShapeHOL.one)), lsoBody C, .one)) (hlso : LsoCodes C)
    (hndh : C.code.lookup fNdh = some (ndhParams.map (fun p => (p, ShapeHOL.one)), ndhBody, .one))
    (hndg : C.code.lookup fNdg = some (ndgParams.map (fun p => (p, ShapeHOL.one)), ndgBody, .one))
    (hlbb : C.code.lookup ExM.fLBB = some ([pFu, ExM.pKb, pH].map (fun p => (p, ShapeHOL.one)), ExM.lbbBody, .one))
    (hcB : ExB.CodesB C (ExB.bodyB C))
    (hbvb : C.code.lookup ExB.fBvarB = some ([(pFu, .one), (pH, .one)], ExB.bvbBody C, .one))
    (hhf : C.code.lookup ExM.fHasFvar = some ([pFu, pH].map (fun p => (p, ShapeHOL.one)), ExM.hasFvarBody, .one))
    (hcF : ExF.CodesF C (ExF.bodyF C))
    (hfvb : C.code.lookup ExF.fFvarB = some ([(pFu, .one), (pH, .one)], ExF.fvbBody C, .one))
    (hat : C.code.lookup fAt = some (atParams.map (fun p => (p, ShapeHOL.one)), atBody, .one)) (hal : AlCodes C)
    (hcrff : C.code.lookup fCrff = some ([crffE].map (fun p => (p, ShapeHOL.one)), crffBody, .one)) (hcrf : CrfCodes C)
    (hens : C.code.lookup fEns = some (kParams.map (fun p => (p, ShapeHOL.one)), ensBody, .one))
    (fe : IFEnv) (hfe : fe = C.fe) (cv : IConstantVal) (q o : Nat)
    (hn : C.H[q]? = some (Enc.idxW cv.name)) (hl : C.H[q + 1]? = some (cellA C o))
    (ht : C.H[q + 2]? = some (Enc.idxW cv.type)) (hb : BlkAt C.H o (cv.levelParams.map Enc.idxW))
    (hlen : cv.levelParams.length < 2 ^ 62) (ks : List ConLeche.Name) (hkl : ks.length = cv.levelParams.length)
    (hks : ∀ j (hj : j < cv.levelParams.length), denoteN C.St.ns cv.levelParams[j] = some (ks[j]'(by omega)))
    (s : AState) :
    SpecR (σ := σ) (Pre C s (gccParams.zip [cellA C q])) (gccBody C) s (classConstOk mode fe cv) (PostU C) :=
  gcc_spec mode C hok hg hpr ra hs hk hac (lsoBody C) hcl hndh hndg hlbb hcB hbvb hhf hcF hfvb hat hal hcrff hcrf
    hens fe hfe cv q o hn hl ht hb hlen ks hkl hks
    (fun H s1 hp => lso_spec ra (ctxH C H) (ctxOK_H hok H) (by ctx_tr hlso) s1 cv q o (get_prefix hn hp) (get_prefix hl hp)
      (get_prefix ht hp) (blkAt_mono hb hp) hlen) s

structure GCCCodes (C : Ctx) : Prop where
  hg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  hpr : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  hcl : C.code.lookup fLso = some ([lsQ].map (fun p => (p, ShapeHOL.one)), lsoBody C, .one)
  hlso : LsoCodes C
  hndh : C.code.lookup fNdh = some (ndhParams.map (fun p => (p, ShapeHOL.one)), ndhBody, .one)
  hndg : C.code.lookup fNdg = some (ndgParams.map (fun p => (p, ShapeHOL.one)), ndgBody, .one)
  hlbb : C.code.lookup ExM.fLBB = some ([pFu, ExM.pKb, pH].map (fun p => (p, ShapeHOL.one)), ExM.lbbBody, .one)
  hcB : ExB.CodesB C (ExB.bodyB C)
  hbvb : C.code.lookup ExB.fBvarB = some ([(pFu, .one), (pH, .one)], ExB.bvbBody C, .one)
  hhf : C.code.lookup ExM.fHasFvar = some ([pFu, pH].map (fun p => (p, ShapeHOL.one)), ExM.hasFvarBody, .one)
  hcF : ExF.CodesF C (ExF.bodyF C)
  hfvb : C.code.lookup ExF.fFvarB = some ([(pFu, .one), (pH, .one)], ExF.fvbBody C, .one)
  hat : C.code.lookup fAt = some (atParams.map (fun p => (p, ShapeHOL.one)), atBody, .one)
  hal : AlCodes C
  hcrff : C.code.lookup fCrff = some ([crffE].map (fun p => (p, ShapeHOL.one)), crffBody, .one)
  hcrf : CrfCodes C
  hens : C.code.lookup fEns = some (kParams.map (fun p => (p, ShapeHOL.one)), ensBody, .one)
  self : C.code.lookup fGcc = some (gccParams.map (fun p => (p, ShapeHOL.one)), gccBody C, .one)

structure CROCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  grt : Ind.GRTCodes C
  gcc : GCCCodes C
  k : KCodes C Comp.kBodies
  ac : Comp.AllCodes mode C
  self : C.code.lookup fCro = some (croParams.map (fun p => (p, ShapeHOL.one)), croBody C, .one)

theorem cro_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ croLocals → (ctxEnv C ++ croParams.zip vals).get x = none :=
  Knot.params_none C croLocals croParams vals (by decide) (by decide)

/-- A constant value, as its `CVE` record. -/
def PostCVG (C : Ctx) (cv : IConstantVal) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' o, C.H <+: H' ∧ w = cellA C o ∧ Ind.CVRep C H' o cv ∧ SR (ctxH C H') s' st

theorem postCVG_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostCVG C a w s' st → PostCVG C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, h1, h2, h3, h4⟩ => ⟨H', o, h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl⟩

set_option maxHeartbeats 16000000 in
/-- **`classRecTyOk g k rc rc.cvR 0`** (one class). -/
theorem cro_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hc : CROCodes mode C)
    (g : ClassGen) (m : TargetMajor) (hcls : g.cls = [m]) (hmm : m.member = some 0) (opre : Nat)
    (hprl : g.pre.length < 2 ^ 56) (hpre : BlkAt C.H opre (g.pre.map Enc.idxW)) (hni : m.nIdx < 2 ^ 56)
    (oms fts osl : Nat) (hT : Ind.TMBlkR C C.H oms g.cls) (hfts : BlkAt C.H fts (g.formerTys.map Enc.idxW))
    (hsb : Ind.SlotBlk C C.H osl g.slots) (hnP : g.nP < 2 ^ 56)
    (hsll : g.slots.length < 2 ^ 56) (kk : Nat) (rc : RecShape) (orr : Nat) (hrr : Ind.RecRep C C.H orr rc)
    (hrl : rc.cvR.levelParams.length < 2 ^ 62) (ks : List ConLeche.Name) (hkl : ks.length = rc.cvR.levelParams.length)
    (hks : ∀ j (hj : j < rc.cvR.levelParams.length), denoteN C.St.ns rc.cvR.levelParams[j] = some (ks[j]'(by omega)))
    (s : AState) :
    SpecR (σ := σ) (Pre C s (croParams.zip [cellA C orr, BitVec.ofNat 64 (g.nP + g.slots.length), cellA C opre,
        BitVec.ofNat 64 g.pre.length, BitVec.ofNat 64 m.nIdx, BitVec.ofNat 64 g.nP, cellA C oms, cellA C fts,
        cellA C osl])) (croBody C) s
      (classRecTyOk mode C.fe g kk rc rc.cvR 0) (PostCVG C) := by
  refine specR_prologue (postCVG_locals _) (cro_none _ _) ?_
  obtain ⟨⟨ocv, hocv, hcv⟩, hrP, hmI, htgE, -, -⟩ := hrr
  unfold classRecTyOk
  simp only [hcls, targetMajorAt, List.getElem?_cons_zero, pure_bind, hmm, Option.getD_some]
  refine UD.specR_heapLoadI' (C := ctxH C C.H) croTg _ (orr + 3) _ htgE.1 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, croParams, ctxEnv]; exact cellA_add_ofNat C orr 3) ?_
  by_cases htg : rc.tgt = 0
  swap
  · have hne : BitVec.ofNat 64 rc.tgt ≠ 0#64 := fun e => htg (by
      have := congrArg BitVec.toNat e; have := htgE.2; simp at *; omega)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h)
      (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, htg]) (fun _ => ?_) (fun h => absurd h (by decide))
  refine UD.specR_heapLoadI' (C := ctxH C C.H) croRp _ (orr + 1) _ hrP.1 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, croParams, ctxEnv]; exact cellA_add8 C orr) ?_
  by_cases hrp : rc.rP = g.nP + g.slots.length
  swap
  · have hne : BitVec.ofNat 64 rc.rP ≠ BitVec.ofNat 64 (g.nP + g.slots.length) := fun e => hrp (by
      have h1 := hrP.2; have h2 := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at h2
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2; omega)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, croParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, croParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hrp]) (fun _ => ?_)
    (fun h => absurd h (by decide))
  refine UD.specR_heapLoadI' (C := ctxH C C.H) croMi _ (orr + 2) _ hmI.1 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, croParams, ctxEnv]; exact cellA_add_ofNat C orr 2) ?_
  by_cases hmi : rc.mI = rc.rP + m.nIdx
  swap
  · have hne : BitVec.ofNat 64 rc.mI ≠ BitVec.ofNat 64 rc.rP + BitVec.ofNat 64 m.nIdx := fun e => hmi (by
      rw [BitVec.ofNat_add_ofNat] at e
      have h1 := hmI.2; have h2 := congrArg BitVec.toNat e; simp only [BitVec.toNat_ofNat] at h2
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2; omega)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, croParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, croParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hmi, BitVec.ofNat_add_ofNat])
    (fun _ => ?_) (fun h => absurd h (by decide))
  simp only [htg, hrp, hmi, beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
  have hp0 : C.H <+: C.H := List.prefix_refl _
  refine specR_callNIH (C := ctxH C C.H) croG Ind.fGrt Ind.grtParams
    [vv croPre, vv croPrl, vv croNP, vv croOms, vv croFts, vv croOsl, .const 0] (Ind.grtBody C)
    [cellA C opre, BitVec.ofNat 64 g.pre.length, BitVec.ofNat 64 g.nP, cellA C oms, cellA C fts, cellA C osl, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.grt.self
    ⟨by simp +decide [sev, Env.get_cons, Env.get, croParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, croParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, croParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, croParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, croParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, croParams, ctxEnv], rfl, trivial⟩
    (Ind.PostSomeH (ctxH C C.H)) (fun o w _ _ => ∃ t, o = some t ∧ w = Enc.idxW t)
    (fun o w s' st ⟨H', t, hp', h1, h2, hsr⟩ => ⟨H', hp', ⟨t, h1, h2⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu Ind.grtParams _ rfl hlk)
      (Ind.grt_spec ra (ctxH C C.H) (ctxOK_H hok C.H) (by ctx_tr hc.grt) g 0 oms fts osl (by decide) hT hfts hsb hsll opre
        hprl hpre hnP s))
    (fun o w s1 H1 hp1 ⟨gty, ho, hw⟩ => ?_)
  subst ho hw
  have hp1' : C.H <+: H1 := hp1
  simp only
  obtain ⟨hnm, ⟨wl, hwl, hlE⟩, hty⟩ := hcv
  obtain ⟨olp, rfl, hlb⟩ := Ind.enlist_cell hlE
  refine UD.specR_heapLoadI' (C := ctxH C H1) croCv _ orr _ (get_prefix hocv hp1') (by decide) (by simp +decide [sev, Env.get_cons, Env.get, croParams, ctxEnv]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H1) croNm (vv croCv) ocv _ (get_prefix hnm hp1') (by decide)
    (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H1) croLp _ (ocv + 1) _ (get_prefix hwl hp1') (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C ocv) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H1) croTy0 _ (ocv + 2) _ (get_prefix hty hp1') (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C ocv 2) ?_
  refine specR_alloc3I (ctxOK_H hok H1) croQ (vv croNm) (vv croLp) (vv croG) (Enc.idxW rc.cvR.name) (cellA C olp)
    (Enc.idxW gty) (by decide) (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons])
    (fun _ => by simp +decide [sev, Env.get_cons]) (fun H2 ws hp2 hws => ?_)
  obtain ⟨g0, g1, g2⟩ := img3_get H2 ws (Enc.idxW rc.cvR.name) (cellA C olp) (Enc.idxW gty) hws
  have hp2' : H1 <+: _ := (hp2 : H1 <+: H2).trans (img3_prefix H2 ws (Enc.idxW rc.cvR.name) (cellA C olp) (Enc.idxW gty) hws)
  set H3 := (((H2 ++ ws).set H2.length (Enc.idxW rc.cvR.name)).set (H2.length + 1) (cellA C olp)).set (H2.length + 2)
    (Enc.idxW gty) with hH3
  have hpC3 : C.H <+: H3 := hp1'.trans hp2'
  have hok3 := ctxOK_H hok H3
  unfold classRecTyCheck
  simp only [bind_assoc]
  refine specR_callNIH (C := ctxH C H3) croU fGcc gccParams [vv croQ] (gccBody C) [cellA C H2.length] (by decide) rfl
    (by decide) hc.gcc.self ⟨by simp +decide [sev, Env.get_cons]; rfl, trivial⟩
    (PostU (ctxH C H3)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu gccParams _ rfl hlk)
      (gcc_full mode (ctxH C H3) hok3 hc.gcc.hg hc.gcc.hpr ra hs (kcodes_H hc.k H3) (allCodes_H hc.ac H3)
        (by ctx_tr hc.gcc.hcl) (by ctx_tr hc.gcc.hlso) hc.gcc.hndh hc.gcc.hndg hc.gcc.hlbb (by ctx_tr hc.gcc.hcB)
        (by ctx_tr hc.gcc.hbvb) hc.gcc.hhf (by ctx_tr hc.gcc.hcF) (by ctx_tr hc.gcc.hfvb) hc.gcc.hat (by ctx_tr hc.gcc.hal)
        hc.gcc.hcrff (by ctx_tr hc.gcc.hcrf) hc.gcc.hens C.fe rfl ⟨rc.cvR.name, rc.cvR.levelParams, gty⟩ H2.length olp
        g0 g1 g2 (blkAt_mono hlb hpC3) hrl ks hkl hks s1))
    (fun _ w s2 H4 hp4 _ => ?_)
  have hp4' : H3 <+: H4 := hp4
  have hk4 := kcodes_H hc.k H4
  refine specR_callCB (C := ctxH C H4) croB fD dParams
    [.const (BitVec.ofNat 64 checkFuel), .const 0, vv croTy0, vv croG]
    (dE (ctxH C H4)) [BitVec.ofNat 64 checkFuel, BitVec.ofNat 64 0, Enc.idxW rc.cvR.type, Enc.idxW gty] (by decide) rfl
    (by decide) hk4.ed ⟨rfl, rfl, by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], trivial⟩
    (Comp.defeqTop ra mode (ctxOK_H hok H4) hk4 (allCodes_H hc.ac H4) hs s2 0 (by decide) rc.cvR.type gty)
    (fun b s3 H5 hp5 _ => ?_)
  cases b
  · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI)
      (fun h => absurd h (by decide))
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind]
  exact specR_returnI _ (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨H5, H2.length,
    hpC3.trans (hp4'.trans hp5), rfl, ⟨get_prefix g0 (hp4'.trans hp5), ⟨_, get_prefix g1 (hp4'.trans hp5),
      ⟨olp, rfl, eblk_mono (hpC3.trans (hp4'.trans hp5)) hlb⟩⟩, get_prefix g2 (hp4'.trans hp5)⟩,
    sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Decl
