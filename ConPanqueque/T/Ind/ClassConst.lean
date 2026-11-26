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

end

end ConPanqueque.T.Decl
