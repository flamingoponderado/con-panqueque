import ConPanqueque.T.Decl.PinNames
import ConPanqueque.T.Comp.Entries
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# `checkConstantVal`: the front door

The record's constant value is a `CVE` block in the value heap (name, level-parameter block, type). The checks
run in the twin's order; where the twin fails the port rejects (`rejectP`).
-/

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC
open ConPanqueque.V.Enc

def cvQ := ofString "cv_q"
def cvAO := ofString "cv_ao"
def cvAR := ofString "cv_ar"
def cvAS := ofString "cv_as"
def cvN := ofString "cv_n"
def cvL := ofString "cv_l"
def cvLn := ofString "cv_ln"
def cvT := ofString "cv_t"
def cvY := ofString "cv_y"
def cvX := ofString "cv_x"
def cvR := ofString "cv_r"
def fLso := ofString "litShapeOk"
def fAt := ofString "allLevelParamsDefined"
def fCrff := ofString "constsResolveFFast"
def lsQ := ofString "ls_q"

def ccvParams : List MlS := [cvQ, cvAO, cvAR, cvAS]
def ccvLocals : List MlS := [cvN, cvL, cvLn, cvT, cvY, cvX, cvR]

def callR (x f : MlS) (es : List (ExpHOL 64)) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.local, x), none)) f es) rest

def ccvBody (C : Ctx) : ProgHOL 64 := prologue ccvLocals
  (.seq (.assign .local cvN (.load .one (vv cvQ)))
  (.seq (.assign .local cvL (.load .one (.op .add [vv cvQ, .const 8])))
  (.seq (.assign .local cvT (.load .one (.op .add [vv cvQ, .const 16])))
  (.seq (.assign .local cvLn (.load .one (vv cvL)))
  (envFindP C cvY (vv cvN)
  (.ite (.cmp .notEqual (vv cvY) (.const 0)) rejectP
  (callR cvX fPim [vv cvN, .const 14, .const 29]
  (.ite (.op .and [vv cvX, .cmp .equal (vv cvAO) (.const 0)]) rejectP
  (callR cvX fPim [vv cvN, .const 43, .const 45]
  (.ite (.op .and [vv cvX, .cmp .equal (vv cvAR) (.const 0)]) rejectP
  (.seq (.assign .local cvX (.load .one (.const (ecell C (C.PO + PIN_SORRY_AX)))))
  (.ite (.op .and [.cmp .equal (vv cvX) (vv cvN), .cmp .equal (vv cvAS) (.const 0)]) rejectP
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
  (.return (.const 0))))))))))))))))))))))))))))

section
variable {σ : Type}

theorem specR_failIteT {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {c : Bool} {F K : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (cond : ExpHOL 64) (v : BitVec 64)
    (hv : sev Γ cond = some v) (hvt : c = true → v ≠ 0) (hvf : c = false → v = 0)
    (hk : c = false → SpecR (Inv C s Γ M D) rest s K R) :
    SpecR (Inv C s Γ M D) (.ite cond rejectP rest) s (if c = true then F else K) R := by
  cases c
  · rw [if_neg (by decide)]; exact specR_ifI _ v hv (fun h => absurd (hvf rfl) h) (fun _ => hk rfl)
  · rw [if_pos rfl]; exact specR_ifI _ v hv (fun _ => specR_rejectI) (fun h => absurd h (hvt rfl))

theorem specR_failIteF {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {c : Bool} {F K : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (cond : ExpHOL 64) (v : BitVec 64)
    (hv : sev Γ cond = some v) (hvt : c = true → v = 0) (hvf : c = false → v ≠ 0)
    (hk : c = true → SpecR (Inv C s Γ M D) rest s K R) :
    SpecR (Inv C s Γ M D) (.ite cond rejectP rest) s (if c = true then K else F) R := by
  cases c
  · rw [if_neg (by decide)]; exact specR_ifI _ v hv (fun _ => specR_rejectI) (fun h => absurd h (hvf rfl))
  · rw [if_pos rfl]; exact specR_ifI _ v hv (fun h => absurd (hvt rfl) h) (fun _ => hk rfl)

theorem reduceOpNames_run {C : Ctx} (hok : CtxOK C) {s : AState} (hp : s.pins = C.pins) :
    reduceOpNames s = .ok ([C.pins.names[43]!, C.pins.names[44]!], s) := by
  have h := fun i (hi : i < pinCount) => pinAt_run hok hp i hi
  simp only [reduceOpNames, reduceNatName, reduceBoolName, pinReduceNat, pinReduceBool, PIN_REDUCE_NAT,
    PIN_REDUCE_BOOL]
  simp [bind, StateT.bind, Except.bind, h _ (show 43 < pinCount by decide), h _ (show 44 < pinCount by decide),
    pure, StateT.pure, Except.pure]

theorem reduceOps_contains (C : Ctx) (n : NIdx) :
    [C.pins.names[43]!, C.pins.names[44]!].contains n = pinIn C 43 45 n := by
  simp only [pinIn, List.range', List.any_cons, List.any_nil, Bool.or_false, Nat.reduceAdd, Nat.reduceSub]
  apply Bool.eq_iff_iff.mpr
  simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_true, beq_iff_eq]

/-- The answer of a check with no value: the heap may have grown. -/
def PostU (C : Ctx) (_ : Unit) (_ : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st

theorem postU_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostU C a w s' st → PostU C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, h⟩ => ⟨H', hp, sr_of_eq h rfl rfl rfl rfl⟩

theorem ccv_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ccvLocals → (ctxEnv C ++ ccvParams.zip vals).get x = none :=
  Knot.params_none C ccvLocals ccvParams vals (by decide) (by decide)

theorem eqIdx_w (a b : NIdx) :
    (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal (Enc.idxW a) (Enc.idxW b) then (1 : BitVec 64) else 0)
      = boolW (b == a) := by
  by_cases h : a = b
  · subst h; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, boolW]
  · have h' : Enc.idxW a ≠ Enc.idxW b := fun e => h (idxW_inj e)
    have h'' : (b == a) = false := beq_false_of_ne (Ne.symm h)
    simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, h', h'', boolW]

theorem boolW_ne (c : Bool) (h : c = true) : boolW c ≠ 0 := by rw [h]; decide
theorem boolW_eq (c : Bool) (h : c = false) : boolW c = 0 := by rw [h]; decide

theorem and_eqz (b a : Bool) :
    (boolW b &&& if Flapjack.Compiler.Encoders.Asm.wordCmpHOL Cmp.equal (boolW a) 0#64 = true then 1#64 else 0#64)
      = boolW (b && !a) := by cases a <;> cases b <;> decide

theorem eqIdx_and_eqz (x y : NIdx) (a : Bool) :
    ((if Flapjack.Compiler.Encoders.Asm.wordCmpHOL Cmp.equal (Enc.idxW x) (Enc.idxW y) = true then 1#64 else 0#64) &&&
      if Flapjack.Compiler.Encoders.Asm.wordCmpHOL Cmp.equal (boolW a) 0#64 = true then 1#64 else 0#64)
      = boolW (y == x && !a) := by
  have h := eqIdx_w x y
  rw [show (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL Cmp.equal (Enc.idxW x) (Enc.idxW y) = true then (1#64 : BitVec 64) else 0#64)
    = boolW (y == x) from h]
  exact and_eqz _ _

theorem eqz_b (b : Bool) :
    (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL Cmp.equal (boolW b) 0#64 = true then 1#64 else 0#64) = boolW (!b) := by
  cases b <;> decide

theorem nez_b (b : Bool) :
    (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL Cmp.notEqual (boolW b) 0#64 = true then 1#64 else 0#64) = boolW b := by
  cases b <;> decide

theorem boolW_not_eq (c : Bool) (h : c = true) : boolW (!c) = 0 := by rw [h]; decide
theorem boolW_not_ne (c : Bool) (h : c = false) : boolW (!c) ≠ 0 := by rw [h]; decide

theorem ensureSortCore_eq (mode : ConLeche.CheckMode) {C : Ctx} (hs : C.side = false) (d : Nat) (e : EIdx) :
    ensureSortCore mode C.fe checkFuel d e = ensureSort (knot mode C checkFuel) C.fe d e := by
  unfold knot; rw [hs]; rfl

theorem and_w (a b : Bool) :
    (boolW a &&& boolW b) = boolW (a && b) := by cases a <;> cases b <;> decide

theorem eqz_w (b : Bool) : (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal (boolW b) 0 then (1 : BitVec 64) else 0)
    = boolW (!b) := by cases b <;> decide

theorem allCodes_H {mode : ConLeche.CheckMode} {C : Ctx} (hac : Comp.AllCodes mode C) (H : List (BitVec 64)) :
    Comp.AllCodes mode (ctxH C H) := by ctx_tr hac

/-- `ensureSortCore` at the checker's fuel, by the port. -/
theorem ens_top (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) {C : Ctx} (hok : CtxOK C)
    (hk : KCodes C Comp.kBodies) (hac : Comp.AllCodes mode C) (hs : C.side = false) (s : AState) (e : EIdx) :
    SpecR (σ := σ) (Pre C s (kParams.zip [BitVec.ofNat 64 checkFuel, BitVec.ofNat 64 0, Enc.idxW e])) ensBody s
      (ensureSortCore mode C.fe checkFuel 0 e) (PostLH C) := by
  rw [ensureSortCore_eq mode hs]
  exact ens_spec (d := 0) mode checkFuel C hk.ew s e
    ((Comp.knot_closed (σ := σ) ra mode checkFuel Comp.checkFuel_le C hok hk s hac).2.1 0 e (by decide))

/-- The front door's last two steps: the type's type, a sort. -/
theorem specR_inferEnsI (mode : ConLeche.CheckMode) (C : Ctx) (hok : CtxOK C)
    (ra : ConPanqueque.Hash.RuntimeAssumptions) (hs : C.side = false) (hk : KCodes C Comp.kBodies)
    (hac : Comp.AllCodes mode C)
    (hens : C.code.lookup fEns = some (kParams.map (fun p => (p, ShapeHOL.one)), ensBody, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (H8 : List (BitVec 64)) (hp : C.H <+: H8) (e : EIdx)
    (hT : Γ.get cvT = some (Enc.idxW e)) (hD : cvX ∈ D) :
    SpecR (σ := σ) (Inv (ctxH C H8) s Γ M D)
      (callR cvX fI [.const (BitVec.ofNat 64 checkFuel), .const 0, vv cvT]
        (callR cvX fEns [.const (BitVec.ofNat 64 checkFuel), .const 0, vv cvX] (.return (.const 0)))) s
      (do let st ← inferTypeCore mode C.fe checkFuel 0 e; let _ ← ensureSortCore mode C.fe checkFuel 0 st; pure PUnit.unit)
      (PostU C) := by
  have hok8 := ctxOK_H hok H8
  have hk8 := kcodes_H hk H8
  have hac8 := allCodes_H hac H8
  refine Big.specR_callKC (C := ctxH C H8) cvX fI kParams [.const (BitVec.ofNat 64 checkFuel), .const 0, vv cvT]
    (inferE (ctxH C H8) fIB) [BitVec.ofNat 64 checkFuel, BitVec.ofNat 64 0, Enc.idxW e] (by decide) rfl
    hD hk8.ei ⟨rfl, rfl, by simp [sev, hT], trivial⟩ (Comp.inferTop ra mode hok8 hk8 hac8 hs s 0 (by decide) e)
    (fun st s9 H9 hp9 _ => ?_)
  have hok9 := ctxOK_H hok H9
  refine specR_callNIH (C := ctxH C H9) cvX fEns kParams [.const (BitVec.ofNat 64 checkFuel), .const 0, vv cvX]
    ensBody [BitVec.ofNat 64 checkFuel, BitVec.ofNat 64 0, Enc.idxW st] (by decide) rfl hD hens
    ⟨rfl, rfl, by simp [sev, Env.get], trivial⟩ (PostLH (ctxH C H9)) (fun _ _ _ _ => True)
    (fun u w s' st' ⟨H', hp', _, hsr⟩ => ⟨H', hp', trivial, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu kParams _ rfl hlk)
      (ens_top ra mode hok9 (kcodes_H hk H9) (allCodes_H hac H9) hs s9 st))
    (fun u w s10 H10 hp10 _ => ?_)
  exact specR_returnI _ 0 rfl (fun t ht => ⟨H10, hp.trans (hp9.trans hp10), sr_of_eq ht.sr rfl rfl rfl rfl⟩)

set_option maxRecDepth 20000 in
/-- **`checkConstantVal`** (`litShapeOk`'s body and spec as hypotheses). -/
theorem ccv_spec (mode : ConLeche.CheckMode) (C : Ctx) (hok : CtxOK C)
    (hg : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hpr : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (hpim : C.code.lookup fPim = some (pmParams.map (fun p => (p, ShapeHOL.one)), pimBody C, .one))
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
    (fe : IFEnv) (hfe : fe = C.fe) (cv : IConstantVal) (aO aR aS : Bool) (q o : Nat)
    (hn : C.H[q]? = some (Enc.idxW cv.name)) (hl : C.H[q + 1]? = some (cellA C o))
    (ht : C.H[q + 2]? = some (Enc.idxW cv.type)) (hb : BlkAt C.H o (cv.levelParams.map Enc.idxW))
    (hlen : cv.levelParams.length < 2 ^ 62) (ks : List ConLeche.Name) (hkl : ks.length = cv.levelParams.length)
    (hks : ∀ j (hj : j < cv.levelParams.length), denoteN C.St.ns cv.levelParams[j] = some (ks[j]'(by omega)))
    (hlso : ∀ (H : List (BitVec 64)) (s : AState), C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s [(lsQ, cellA C q)]) LB s (litShapeOk (.axiomInfo cv)) (PostB (ctxH C H)))
    (s : AState) :
    SpecR (σ := σ) (Pre C s (ccvParams.zip [cellA C q, boolW aO, boolW aR, boolW aS])) (ccvBody C) s
      (checkConstantVal mode fe cv aO aR aS) (PostU C) := by
  refine specR_prologue (postU_locals C) (ccv_none C _) ?_
  unfold checkConstantVal
  dsimp only
  refine UD.specR_heapLoadI' (C := C) cvN _ q _ hn (by decide) (by simp +decide [Env.get, ccvParams, ctxEnv]) ?_
  refine UD.specR_heapLoadI' (C := C) cvL _ (q + 1) _ hl (by decide)
    (by simp +decide [sev, Env.get, ccvParams, ctxEnv]; exact cellA_add8 C q) ?_
  refine UD.specR_heapLoadI' (C := C) cvT _ (q + 2) _ ht (by decide)
    (by simp +decide [sev, Env.get, ccvParams, ctxEnv]; exact cellA_add_ofNat C q 2) ?_
  refine UD.specR_heapLoadI' (C := C) cvLn _ o _ hb.1 (by decide) (by simp +decide [Env.get]) ?_
  refine specR_envFindI hok hg hpr cvY (vv cvN) cv.name (by decide) (by simp +decide [Env.get])
    (by simp +decide [Env.get, ccvParams, ctxEnv]) ?_
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
    refine specR_atEntry fun t ht => ?_
    have hpins := ht.sr.pins
    refine specR_runBind (natOpName_run hok hpins cv.name) ?_
    refine specR_callPure cvX fPim pmParams [vv cvN, .const 14, .const 29] (pimBody C)
      [Enc.idxW cv.name, BitVec.ofNat 64 14, BitVec.ofNat 64 29] (pinIn C 14 29 cv.name) (by decide) rfl (by decide) hpim
      ⟨(by simp +decide [Env.get, ccvParams, ctxEnv]), rfl, rfl, trivial⟩ (PostB C) (fun b w _ _ => w = boolW b)
      (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pmParams _ rfl hlk)
        (pim_spec C hok hpim s cv.name 29 (by decide) _ 14 C.H (List.prefix_refl _) rfl (by omega)))
      (fun w H1 hp1 hw => ?_)
    subst hw
    refine specR_failIteT (c := pinIn C 14 29 cv.name && !aO) _ (boolW (pinIn C 14 29 cv.name && !aO))
      (by simp +decide [sev, Env.get, ccvParams, ctxEnv]; exact and_eqz _ _) (boolW_ne _) (boolW_eq _) (fun _ => ?_)
    refine specR_runBind (reduceOpNames_run hok hpins) ?_
    rw [reduceOps_contains]
    refine specR_callPure (C := ctxH C H1) cvX fPim pmParams [vv cvN, .const 43, .const 45] (pimBody C)
      [Enc.idxW cv.name, BitVec.ofNat 64 43, BitVec.ofNat 64 45] (pinIn C 43 45 cv.name) (by decide) rfl (by decide) hpim
      ⟨(by simp +decide [Env.get, ccvParams, ctxEnv]), rfl, rfl, trivial⟩ (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b)
      (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pmParams _ rfl hlk)
        (pim_spec C hok hpim s cv.name 45 (by decide) _ 43 H1 hp1 rfl (by omega)))
      (fun w H2 hp2 hw => ?_)
    subst hw
    refine specR_failIteT (c := pinIn C 43 45 cv.name && !aR) _ (boolW (pinIn C 43 45 cv.name && !aR))
      (by simp +decide [sev, Env.get, ccvParams, ctxEnv]; exact and_eqz _ _) (boolW_ne _) (boolW_eq _) (fun _ => ?_)
    have hok2 := ctxOK_H hok H2
    refine specR_pinAtI (C := ctxH C H2) hok2 PIN_SORRY_AX (by decide) cvX (by decide) ?_
    refine specR_failIteT _ _ (by simp +decide [sev, Env.get, ccvParams, ctxEnv]; exact eqIdx_and_eqz _ _ _)
      (boolW_ne _) (boolW_eq _) (fun _ => ?_)
    -- litShapeOk
    refine specR_callNIH (C := ctxH C H2) cvR fLso [lsQ] [vv cvQ] LB [cellA C q] (by decide) rfl (by decide) hcl
      ⟨(by simp +decide [Env.get, ccvParams, ctxEnv]), trivial⟩ (PostB (ctxH C H2)) (fun b w _ _ => w = boolW b)
      (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [lsQ] _ rfl hlk) (hlso H2 s (hp1.trans hp2)))
      (fun b w s3 H3 hp3 hw => ?_)
    subst hw
    refine specR_failIteF (c := b) _ (boolW (!b)) (by simp +decide [sev, Env.get]; exact eqz_b b)
      (boolW_not_eq _) (boolW_not_ne _) (fun _ => ?_)
    -- nameNodup
    have hp03 : C.H <+: H3 := hp1.trans (hp2.trans hp3)
    refine specR_callPure (C := ctxH C H3) cvR fNdg ndgParams [vv cvL, .const 0, vv cvLn] ndgBody
      [cellA C o, BitVec.ofNat 64 0, BitVec.ofNat 64 cv.levelParams.length] (nameNodup (cv.levelParams.drop 0))
      (by decide) rfl (by decide) hndg ⟨(by simp +decide [Env.get, ccvParams, ctxEnv]), rfl, by simp +decide [Env.get, ccvParams, ctxEnv], trivial⟩
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
      ⟨rfl, rfl, (by simp +decide [Env.get, ccvParams, ctxEnv]), trivial⟩ (ExM.PostB (ctxH C H4)) (fun b w _ H' => H' = H4 ∧ w = boolW b)
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
      ⟨rfl, (by simp +decide [Env.get, ccvParams, ctxEnv]), trivial⟩ (ExM.PostB (ctxH C H4)) (fun b w _ H' => H' = H4 ∧ w = boolW b)
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
      ⟨(by simp +decide [Env.get, ccvParams, ctxEnv]), (by simp +decide [Env.get, ccvParams, ctxEnv]), by simp +decide [Env.get, ccvParams, ctxEnv], trivial⟩ (PostB (ctxH C H4)) (fun b w _ _ => w = boolW b)
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
      (by decide) hcrff ⟨(by simp +decide [Env.get, ccvParams, ctxEnv]), trivial⟩ (PostB (ctxH C H7)) (fun b w _ _ => w = boolW b)
      (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [crffE] _ rfl hlk)
        (crff_spec (ctxH C H7) hok7 (by ctx_tr hcrf) s7 cv.type))
      (fun b w s8 H8 hp8 hw => ?_)
    subst hw
    refine specR_failIteF (c := b) _ (boolW (!b)) (by simp +decide [sev, Env.get]; exact eqz_b b)
      (boolW_not_eq _) (boolW_not_ne _) (fun _ => ?_)
    exact specR_inferEnsI mode C hok ra hs hk hac hens H8 (hp03.trans (hp4.trans (hp7.trans hp8))) cv.type
      (by simp +decide [Env.get, ccvParams, ctxEnv]) (by decide)
  · intro ⟨o', hm, hci⟩
    rw [hm]
    refine specR_atEntry fun t ht => ?_
    have hoE : o' < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
    refine specR_failIteT (c := true) _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
      (fun _ => by decide) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))

end

end ConPanqueque.T.Decl
