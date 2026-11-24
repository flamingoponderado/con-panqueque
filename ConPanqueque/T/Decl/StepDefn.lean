import ConPanqueque.T.Decl.Names
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# A definition record

`checkDecl` at a `def`: the front door, the value check, the pinned `Nat` operations (the port stops there:
their certification is not ported yet), the install and its literal flags, the flush, and the reserved names.
-/

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC
open ConPanqueque.V.Enc

def fCcv := ofString "checkConstantVal"

/-- Every function a record's check calls, at its body. -/
structure DeclCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  k : KCodes C Comp.kBodies
  ac : Comp.AllCodes mode C
  pim : C.code.lookup fPim = some (pmParams.map (fun p => (p, ShapeHOL.one)), pimBody C, .one)
  ccv : C.code.lookup fCcv = some (ccvParams.map (fun p => (p, ShapeHOL.one)), ccvBody C, .one)
  lso : C.code.lookup fLso = some ([lsQ].map (fun p => (p, ShapeHOL.one)), lsoBody C, .one)
  lsoc : LsoCodes C
  ndh : C.code.lookup fNdh = some (ndhParams.map (fun p => (p, ShapeHOL.one)), ndhBody, .one)
  ndg : C.code.lookup fNdg = some (ndgParams.map (fun p => (p, ShapeHOL.one)), ndgBody, .one)
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
  ens : C.code.lookup fEns = some (kParams.map (fun p => (p, ShapeHOL.one)), ensBody, .one)
  vg : C.code.lookup fVg = some (vgParams.map (fun p => (p, ShapeHOL.one)), vgBody, .one)
  dv : C.code.lookup fDv = some (dvParams.map (fun p => (p, ShapeHOL.one)), dvBody, .one)
  cp : C.code.lookup fCpy = some (cpParams.map (fun p => (p, ShapeHOL.one)), cpyBody, .one)
  inst : C.code.lookup fInst = some (inParams.map (fun p => (p, ShapeHOL.one)), instBody C, .one)
  natF : C.code.lookup fNatF = some (([] : List MlS).map (fun p => (p, ShapeHOL.one)), natFBody C, .one)
  strF : C.code.lookup fStrF = some (([] : List MlS).map (fun p => (p, ShapeHOL.one)), strFBody C, .one)
  flags : C.code.lookup fFlags = some (([] : List MlS).map (fun p => (p, ShapeHOL.one)), flBody, .one)
  rsm : C.code.lookup fRsm = some (rmParams.map (fun p => (p, ShapeHOL.one)), rsmBody, .one)
  th : C.code.lookup fTh = some (thParams.map (fun p => (p, ShapeHOL.one)), thBody C, .one)
  eqv : C.code.lookup LLeq.fEqv = some ([LEq.pLa, LEq.pLb].map (fun p => (p, ShapeHOL.one)), LLeq.eqvBody, .one)

theorem natOpNames_list {C : Ctx} (hok : CtxOK C) {s : AState} (hp : s.pins = C.pins) (n : NIdx) :
    (natOpNames >>= fun l => (pure (l.contains n) : AM Bool)) s = .ok (pinIn C 14 21 n, s) := by
  have h := fun i (hi : i < pinCount) => pinAt_run hok hp i hi
  simp only [natOpNames, natPredName, natAddName, natSubName, natMulName, natPowName, natBeqName, natBleName,
    pinNatPred, pinNatAdd, pinNatSub, pinNatMul, pinNatPow, pinNatBeq, pinNatBle, PIN_NAT_PRED, PIN_NAT_ADD,
    PIN_NAT_SUB, PIN_NAT_MUL, PIN_NAT_POW, PIN_NAT_BEQ, PIN_NAT_BLE]
  simp [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, h _ (show 14 < pinCount by decide),
    h _ (show 15 < pinCount by decide), h _ (show 16 < pinCount by decide), h _ (show 17 < pinCount by decide),
    h _ (show 18 < pinCount by decide), h _ (show 19 < pinCount by decide), h _ (show 20 < pinCount by decide)]
  simp only [pinIn, List.range', List.any_cons, List.any_nil, Bool.or_false, Nat.reduceAdd, Nat.reduceSub]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq, List.mem_cons, List.mem_nil_iff, or_false]


def natOpsL (C : Ctx) : List NIdx := (List.range' 14 7).map (fun i => C.pins.names[i]!)
def divModsL (C : Ctx) : List NIdx := (List.range' 21 8).map (fun i => C.pins.names[i]!)

theorem natOpNames_run {C : Ctx} (hok : CtxOK C) {s : AState} (hp : s.pins = C.pins) :
    natOpNames s = .ok (natOpsL C, s) := by
  have h := fun i (hi : i < pinCount) => pinAt_run hok hp i hi
  simp only [natOpNames, natPredName, natAddName, natSubName, natMulName, natPowName, natBeqName, natBleName,
    pinNatPred, pinNatAdd, pinNatSub, pinNatMul, pinNatPow, pinNatBeq, pinNatBle, PIN_NAT_PRED, PIN_NAT_ADD,
    PIN_NAT_SUB, PIN_NAT_MUL, PIN_NAT_POW, PIN_NAT_BEQ, PIN_NAT_BLE]
  simp [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, natOpsL, List.range',
    h _ (show 14 < pinCount by decide), h _ (show 15 < pinCount by decide), h _ (show 16 < pinCount by decide), h _ (show 17 < pinCount by decide), h _ (show 18 < pinCount by decide), h _ (show 19 < pinCount by decide), h _ (show 20 < pinCount by decide)] 

theorem divModNames_run {C : Ctx} (hok : CtxOK C) {s : AState} (hp : s.pins = C.pins) :
    natDivModNames s = .ok (divModsL C, s) := by
  have h := fun i (hi : i < pinCount) => pinAt_run hok hp i hi
  simp only [natDivModNames, natDivName, natModName, natGcdName, natLandName, natLorName, natXorName,
    natShiftLeftName, natShiftRightName, pinNatDiv, pinNatMod, pinNatGcd, pinNatLand, pinNatLor, pinNatXor,
    pinNatShiftLeft, pinNatShiftRight, PIN_NAT_DIV, PIN_NAT_MOD, PIN_NAT_GCD, PIN_NAT_LAND, PIN_NAT_LOR, PIN_NAT_XOR,
    PIN_NAT_SHIFT_LEFT, PIN_NAT_SHIFT_RIGHT]
  simp [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, divModsL, List.range',
    h _ (show 21 < pinCount by decide), h _ (show 22 < pinCount by decide), h _ (show 23 < pinCount by decide), h _ (show 24 < pinCount by decide), h _ (show 25 < pinCount by decide), h _ (show 26 < pinCount by decide), h _ (show 27 < pinCount by decide), h _ (show 28 < pinCount by decide)]

theorem rangeL_contains (C : Ctx) (i n : Nat) (x : NIdx) :
    ((List.range' i n).map (fun j => C.pins.names[j]!)).contains x = pinIn C i (i + n) x := by
  unfold pinIn
  rw [show i + n - i = n by omega]
  induction (List.range' i n) with
  | nil => rfl
  | cons a l ih =>
    simp only [List.map_cons, List.contains_cons, List.any_cons, ih]

theorem basisUnres_run {C : Ctx} (hok : CtxOK C) {s : AState} (hp : s.pins = C.pins) (n : NIdx) :
    basisNameUnreserved n s = .ok (!C.pins.reserved.contains n, s) := by
  simp [basisNameUnreserved, reservedBasisNames, pinReserved, pinsReady_of hok hp, hp, get, getThe,
    MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure, Except.bind, Except.pure]


/-- A front door that passed saw a fresh name. -/
theorem ccv_fresh {mode : ConLeche.CheckMode} {fe : IFEnv} {cv : IConstantVal} {aO aR aS : Bool} {s s' : AState}
    {r : Unit} (h : checkConstantVal mode fe cv aO aR aS s = .ok (r, s')) : fe.find? cv.name = none := by
  cases hf : fe.find? cv.name with
  | none => rfl
  | some ci =>
    exfalso
    unfold checkConstantVal at h
    simp only [hf, Option.isSome_some, if_true] at h
    simp [fail, throw, throwThe, MonadExceptOf.throw, bind, StateT.bind, Except.bind, StateT.lift,
      ExceptT.lift] at h

theorem ok_of_bind_pure {α β : Type} {A : AM α} {r : β} {s s' : AState} {ci : β}
    (h : (A >>= fun _ => pure r) s = .ok (ci, s')) : ci = r := by
  simp only [bind, StateT.bind, Except.bind] at h
  cases hA : A s with
  | error e => rw [hA] at h; simp at h
  | ok p => rw [hA] at h; simp [pure, StateT.pure, Except.pure] at h; exact h.1.symm

/-- A definition's value check returns the definition. -/
theorem checkDefnVal_ci {mode : ConLeche.CheckMode} {fe : IFEnv} {cv : IConstantVal} {v : EIdx}
    {hint : ConLeche.ReducibilityHint} {s s' : AState} {ci : IConstantInfo}
    (h : checkDefnVal mode fe cv v hint s = .ok (ci, s')) : ci = .defnInfo cv v hint := by
  have e : checkDefnVal mode fe cv v hint = (do
      valueGuards fe cv v
      let vtype ← inferTypeCore mode fe checkFuel 0 v
      unless ← isDefEqCore mode fe checkFuel 0 vtype cv.type do
        fail (.invalid "type mismatch in definition")) >>= fun _ => pure (.defnInfo cv v hint) := by
    unfold checkDefnVal; simp only [bind_assoc]
    congr 1; funext _; congr 1; funext _; congr 1; funext x
    split <;> simp
  rw [e] at h
  exact ok_of_bind_pure h


def kdQ := ofString "kd_q"
def kdV := ofString "kd_v"
def kdHn := ofString "kd_h"
def kdN := ofString "kd_n"
def kdX := ofString "kd_x"
def kdL := ofString "kd_l"
def kdLn := ofString "kd_ln"
def kdParams : List MlS := [kdQ, kdV, kdHn]
def kdLocals : List MlS := [kdN, kdX, kdL, kdLn, lJ0]

/-- `checkDecl` at a definition (its constant value at `kdQ`, value `kdV`, hint `kdHn`). -/
def kdBody (C : Ctx) : ProgHOL 64 := prologue kdLocals
  (.seq (.assign .local kdN (.load .one (vv kdQ)))
  (callR kdX fCcv [vv kdQ, .const 1, .const 0, .const 0]
  (callR kdX fDv [vv kdQ, vv kdV]
  (callR kdX fPim [vv kdN, .const 14, .const 21]
  (.ite (.cmp .notEqual (vv kdX) (.const 0)) rejectP
  (callR kdX fPim [vv kdN, .const 21, .const 29]
  (.ite (.cmp .notEqual (vv kdX) (.const 0)) rejectP
  (callR kdX fInst [.const 1, vv kdQ, vv kdV, vv kdHn]
  (callR kdX fFlags []
  (flushCode C (flushRegions false)
  (.seq (.assign .local kdL (.load .one (.const (ecell C (C.PO + pinCount + 4)))))
  (.seq (.assign .local kdLn (.load .one (vv kdL)))
  (callR kdX fRsm [vv kdN, vv kdL, .const 0, vv kdLn]
  (.ite (.cmp .notEqual (vv kdX) (.const 0)) rejectP (.return (.const 0))))))))))))))))

theorem ite_bindM {α β : Type} (c : Prop) [Decidable c] (F K : AM α) (f : α → AM β) :
    ((if c then F else K) >>= f) = if c then F >>= f else K >>= f := by split <;> rfl


/-- `checkDecl` at an opaque (its constant value at `kdQ`, value `kdV`). -/
def koBody (C : Ctx) : ProgHOL 64 := prologue kdLocals
  (.seq (.assign .local kdN (.load .one (vv kdQ)))
  (callR kdX fCcv [vv kdQ, .const 0, .const 1, .const 0]
  (callR kdX fDv [vv kdQ, vv kdV]
  (callR kdX fPim [vv kdN, .const 43, .const 45]
  (.ite (.cmp .notEqual (vv kdX) (.const 0)) rejectP
  (callR kdX fInst [.const 0, vv kdQ, vv kdV, vv kdHn]
  (callR kdX fFlags []
  (flushCode C (flushRegions false)
  (.seq (.assign .local kdL (.load .one (.const (ecell C (C.PO + pinCount + 4)))))
  (.seq (.assign .local kdLn (.load .one (vv kdL)))
  (callR kdX fRsm [vv kdN, vv kdL, .const 0, vv kdLn]
  (.ite (.cmp .notEqual (vv kdX) (.const 0)) rejectP (.return (.const 0))))))))))))))


/-- `checkDecl` at a theorem (its constant value at `kdQ`, value `kdV`). -/
def ktBody (C : Ctx) : ProgHOL 64 := prologue kdLocals
  (.seq (.assign .local kdN (.load .one (vv kdQ)))
  (callR kdX fCcv [vv kdQ, .const 0, .const 0, .const 0]
  (callR kdX fTh [vv kdQ, vv kdV]
  (callR kdX fInst [.const 2, vv kdQ, vv kdV, vv kdHn]
  (callR kdX fFlags []
  (flushCode C (flushRegions false)
  (.seq (.assign .local kdL (.load .one (.const (ecell C (C.PO + pinCount + 4)))))
  (.seq (.assign .local kdLn (.load .one (vv kdL)))
  (callR kdX fRsm [vv kdN, vv kdL, .const 0, vv kdLn]
  (.ite (.cmp .notEqual (vv kdX) (.const 0)) rejectP (.return (.const 0))))))))))))

/-- The context after a record: its environment, images and heap. -/
def ctxNew (C : Ctx) (fe : IFEnv) (EH : List (BitVec 64)) (envM : Std.HashMap NIdx (BitVec 64))
    (H : List (BitVec 64)) : Ctx := { C with fe := fe, EH := EH, envM := envM, H := H }

section
variable {σ : Type}

/-- After a record: the next context is well formed and related, with the fold's invariants. -/
def PostStep (C : Ctx) (fe : IFEnv) (_ : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ EH envM H, C.EH <+: EH ∧ C.H <+: H ∧ CtxOK (ctxNew C fe EH envM H) ∧ SR (ctxNew C fe EH envM H) s' st ∧
    TblGate fe ∧ FlagsOK fe ∧ LitsPinned fe C.pins

theorem postStep_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostStep C a w s' st → PostStep C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨EH, envM, H, h1, h2, h3, h4, h5⟩ => ⟨EH, envM, H, h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl, h5⟩

theorem kd_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ kdLocals → (ctxEnv C ++ kdParams.zip vals).get x = none :=
  Knot.params_none C kdLocals kdParams vals (by decide) (by decide)

set_option maxHeartbeats 2000000 in
/-- **`checkDecl` at a definition**. -/
theorem kd_spec (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (C : Ctx) (hok : CtxOK C)
    (hc : DeclCodes mode C) (ra : ConPanqueque.Hash.RuntimeAssumptions) (hs : C.side = false)
    (hpl : C.saved = none) (hg : TblGate C.fe) (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins)
    (cv : IConstantVal) (v : EIdx) (hint : ConLeche.ReducibilityHint) (q o : Nat)
    (hn : C.H[q]? = some (Enc.idxW cv.name)) (hl : C.H[q + 1]? = some (cellA C o))
    (ht : C.H[q + 2]? = some (Enc.idxW cv.type)) (hb : BlkAt C.H o (cv.levelParams.map Enc.idxW))
    (hlen : cv.levelParams.length < 2 ^ 59) (ks : List ConLeche.Name) (hkl : ks.length = cv.levelParams.length)
    (hks : ∀ j (hj : j < cv.levelParams.length), denoteN C.St.ns cv.levelParams[j] = some (ks[j]'(by omega)))
    (htyD : (denoteE C.St cv.type).isSome = true) (hvD : (denoteE C.St v).isSome = true)
    (hhint : hintN hint < 2 ^ 63) (s : AState) :
    SpecR (σ := σ) (Pre C s (kdParams.zip [cellA C q, Enc.idxW v, BitVec.ofNat 64 (hintN hint)])) (kdBody C) s
      (checkDecl mode pins C.fe (.defnDecl cv v hint)) (PostStep C) := by
  refine specR_prologue (postStep_locals C) (kd_none C _) ?_
  unfold checkDecl checkDeclKind
  dsimp only
  simp only [bind_assoc]
  refine UD.specR_heapLoadI' (C := C) kdN _ q _ hn (by decide) (by simp +decide [Env.get, kdParams, ctxEnv]) ?_
  -- the front door
  refine specR_callNIH (C := C) kdX fCcv ccvParams [vv kdQ, .const 1, .const 0, .const 0] (ccvBody C)
    [cellA C q, boolW true, boolW false, boolW false] (by decide) rfl (by decide) hc.ccv
    ⟨(by simp +decide [Env.get, kdParams, ctxEnv]), rfl, rfl, rfl, trivial⟩
    (fun a w s' st => checkConstantVal mode C.fe cv true false false s = .ok (a, s') ∧ PostU C a w s' st)
    (fun a w s' H' => checkConstantVal mode C.fe cv true false false s = .ok (a, s'))
    (fun a w s' st ⟨hrun, H', hp', hsr⟩ => ⟨H', hp', hrun, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ccvParams _ rfl hlk)
      (specR_run (ccv_full mode C hok hc.k.g hc.k.p hc.pim ra hs hc.k hc.ac hc.lso hc.lsoc hc.ndh hc.ndg hc.lbb hc.cB
        hc.bvb hc.hf hc.cF hc.fvb hc.atc hc.al hc.crff hc.crf hc.ens C.fe rfl cv true false false q o hn hl ht hb
        (by omega) ks hkl hks s)))
    (fun _ w s1 H1 hp1 hrun1 => ?_)
  have hnew := ccv_fresh hrun1
  have hok1 := ctxOK_H hok H1
  -- the value check
  refine specR_callNIH (C := ctxH C H1) kdX fDv dvParams [vv kdQ, vv kdV] dvBody [cellA C q, Enc.idxW v]
    (by decide) rfl (by decide) hc.dv ⟨(by simp +decide [Env.get, kdParams, ctxEnv]), (by simp +decide [Env.get, kdParams, ctxEnv]), trivial⟩
    (fun a w s' st => checkDefnVal mode C.fe cv v hint s1 = .ok (a, s') ∧ PostCI (ctxH C H1) a w s' st)
    (fun a w s' H' => checkDefnVal mode C.fe cv v hint s1 = .ok (a, s'))
    (fun a w s' st ⟨hrun, H', hp', hsr⟩ => ⟨H', hp', hrun, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu dvParams _ rfl hlk)
      (specR_run (defn_spec mode (ctxH C H1) hok1 ra hs (kcodes_H hc.k H1) (allCodes_H hc.ac H1) hc.vg cv v q
        (fun H s' hp => vg_spec (ctxH C H) (ctxOK_H hok H) hc.lbb (by ctx_tr hc.cB) hc.bvb hc.hf (by ctx_tr hc.cF) hc.fvb
          hc.atc (by ctx_tr hc.al) hc.crff (by ctx_tr hc.crf) C.fe rfl cv v q o (get_prefix hl (hp1.trans hp))
          (blkAt_mono hb (hp1.trans hp)) (by omega) ks hkl hks s')
        (get_prefix ht hp1) hint s1)))
    (fun ci w s2 H2 hp2 hrun2 => ?_)
  have hci := checkDefnVal_ci hrun2
  subst hci
  have hp12 : C.H <+: H2 := hp1.trans hp2
  have hok2 := ctxOK_H hok H2
  -- the pinned Nat operations: the port stops at them
  refine specR_atEntry fun t2 ht2 => ?_
  have hpins := ht2.sr.pins
  refine specR_runBind (natOpNames_run hok2 hpins) ?_
  rw [ite_bindM]
  unfold natOpsL
  rw [rangeL_contains]
  refine specR_callPure (C := ctxH C H2) kdX fPim pmParams [vv kdN, .const 14, .const 21] (pimBody C)
    [Enc.idxW cv.name, BitVec.ofNat 64 14, BitVec.ofNat 64 21] (pinIn C 14 21 cv.name) (by decide) rfl (by decide) hc.pim
    ⟨(by simp +decide [Env.get, kdParams, ctxEnv]), rfl, rfl, trivial⟩ (PostB (ctxH C H2)) (fun b w _ _ => w = boolW b)
    (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pmParams _ rfl hlk)
      (pim_spec C hok hc.pim s2 cv.name 21 (by decide) _ 14 H2 hp12 rfl (by omega)))
    (fun w H3 hp3 hw => ?_)
  subst hw
  refine specR_failIteT (c := pinIn C 14 21 cv.name) _ (boolW (pinIn C 14 21 cv.name))
    (by simp +decide [sev, Env.get]; exact nez_b _) (boolW_ne _) (boolW_eq _) (fun _ => ?_)
  simp only [pure_bind, bind_assoc]
  refine specR_runBind (divModNames_run (ctxOK_H hok H3) hpins) ?_
  unfold divModsL
  rw [rangeL_contains]
  have hp13 : C.H <+: H3 := hp12.trans hp3
  refine specR_callPure (C := ctxH C H3) kdX fPim pmParams [vv kdN, .const 21, .const 29] (pimBody C)
    [Enc.idxW cv.name, BitVec.ofNat 64 21, BitVec.ofNat 64 29] (pinIn C 21 29 cv.name) (by decide) rfl (by decide) hc.pim
    ⟨(by simp +decide [Env.get, kdParams, ctxEnv]), rfl, rfl, trivial⟩ (PostB (ctxH C H3)) (fun b w _ _ => w = boolW b)
    (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pmParams _ rfl hlk)
      (pim_spec C hok hc.pim s2 cv.name 29 (by decide) _ 21 H3 hp13 rfl (by omega)))
    (fun w H4 hp4 hw => ?_)
  subst hw
  rw [ite_bindM]
  refine specR_failIteT (c := pinIn C 21 29 cv.name) _ (boolW (pinIn C 21 29 cv.name))
    (by simp +decide [sev, Env.get]; exact nez_b _) (boolW_ne _) (boolW_eq _) (fun _ => ?_)
  -- install
  have hp14 : C.H <+: H4 := hp13.trans hp4
  have hok4 := ctxOK_H hok H4
  have hden : NewDen (.defnInfo cv v hint) s2.store := by
    refine ⟨fun n hn' => ?_, denoteE_isSome_ext ht2.sr.floor htyD, by show cv.levelParams.length + 1 < 2 ^ 60; omega,
      fun cv' v' h' e => by cases e; exact denoteE_isSome_ext ht2.sr.floor hvD, fun _ _ e => by cases e⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hn'
    exact Option.isSome_iff_exists.mpr ⟨_, denoteN_ext (hks j hj) ht2.sr.floor⟩
  refine specR_callNC (C := ctxH C H4) (D := ctxLocals ++ kdLocals) kdX fInst inParams
    [.const 1, vv kdQ, vv kdV, vv kdHn] (instBody C)
    [1, cellA C q, Enc.idxW v, BitVec.ofNat 64 (hintN hint)] (by decide) rfl (by decide) hc.inst ?_
    (fun a w s' st => (pure (C.fe.push (.defnInfo cv v hint)) : AM IFEnv) s2 = .ok (a, s') ∧
      PostInst (ctxH C H4) (.defnInfo cv v hint) a w s' st)
    (fun a w s' C' => s' = s2 ∧ a = C.fe.push (.defnInfo cv v hint) ∧ ∃ EH ox, C' = ctxIns (ctxH C H4)
        ((C.fe.push (.defnInfo cv v hint)).setFlags C.fe.natLit C.fe.strLit) EH
        (C.envM.insert cv.name (ecell C ox)) ∧ C.EH <+: EH ∧ CIE C.EB EH ox (.defnInfo cv v hint))
    (fun a w s' st ⟨hrun, ⟨EH, ox, hpE, hcie, hsr⟩⟩ => by
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      exact ⟨_, ⟨hrun.2.symm, hrun.1.symm, EH, ox, rfl, hpE, hcie⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu inParams _ rfl hlk)
      (specR_run (inst_spec (ctxH C H4) hok4 hc.cp hc.k.s hc.k.i s2 (.defnInfo cv v hint) q o
        (get_prefix hn hp14) (get_prefix hl hp14) (get_prefix ht hp14) (blkAt_mono hb hp14)
        (by show cv.levelParams.length < 2 ^ 60; omega)
        1 (Enc.idxW v) (BitVec.ofNat 64 (hintN hint)) (fun EH ox b h => cie_defn hhint h) hg hnew hden
        (fun _ _ _ _ _ e => by cases e))))
    (fun a w s3 C3 ⟨hs3, ha, EH, ox, eC, hpE, hcie⟩ => ?_)
  · exact ⟨rfl, (by simp +decide [Env.get, kdParams, ctxEnv]), (by simp +decide [Env.get, kdParams, ctxEnv]), (by simp +decide [Env.get, kdParams, ctxEnv]), trivial⟩
  subst eC hs3 ha
  -- the literal flags
  set ci : IConstantInfo := .defnInfo cv v hint with hcidef
  set CI := ctxIns (ctxH C H4) ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit) EH (C.envM.insert cv.name (ecell C ox))
    with hCI
  have hokI : CtxOK CI := ctxOK_ins hok4 hpE hcie (pushOld_find C.fe ci) (pushOld_findTable hg ci hnew)
  have hfP : ∀ n, (C.fe.push ci).find? n = CI.fe.find? n := fun n => (IFEnv.setFlags_find? _ _ _ n).symm
  have htP : ∀ n, (C.fe.push ci).findTable? n = CI.fe.findTable? n := fun n => by
    show _ = ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit).findTable? n
    unfold IFEnv.findTable?; rw [IFEnv.setFlags_find?, IFEnv.setFlags_rawTable?]
  obtain ⟨hfn, hfs⟩ := push_flags_found (C := ctxH C H4) hF hL ci ox EH
  refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => (pure (C.fe.push ci) >>= fun fe₂ => (do
      flushCaches
      let b ← basisNamesOk (IDeclaration.defnDecl cv v hint)
      if b = true then pure fe₂ else do
        let e ← basisNamesError (IDeclaration.defnDecl cv v hint)
        fail e))) rfl ?_
  refine specR_callNC (C := CI) (D := ctxLocals ++ kdLocals) kdX fFlags [] [] flBody [] (by decide) rfl (by decide)
    hc.flags trivial (fun a w s' st => PostFl CI (C.fe.push ci) a w s' st ∧ s' = s3)
    (fun _ w s' C' => s' = s3 ∧ ∃ H5, C' = ctxFe (ctxH CI H5) (C.fe.push ci) ∧ CI.H <+: H5)
    (fun a w s' st ⟨⟨H5, hp5, hsr⟩, hs'⟩ => ⟨_, ⟨hs', H5, rfl, hp5⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [] _ rfl hlk)
      (specR_pureState (fl_spec CI hokI hc.natF hc.strF hc.k.g hc.k.p s3 hfP htP hfn hfs)))
    (fun _ w s4 C4 ⟨hs4, H5, eC, hp5⟩ => ?_)
  subst eC hs4
  simp only [pure_bind]
  -- the flush
  have hokF : CtxOK (ctxFe (ctxH CI H5) (C.fe.push ci)) :=
    ctxOK_fe (ctxOK_H hokI H5) (fun n => hfP n) (fun n => htP n)
  refine specR_flushTopI hokF hpl false flushCaches rfl (by decide) ?_
  -- the reserved names
  simp only [basisNamesOk]
  refine specR_atEntry fun t4 ht4 => ?_
  refine specR_runBind (basisUnres_run hokF ht4.sr.pins cv.name) ?_
  obtain ⟨wR, hwR, oR, hwoR, hblkR⟩ := hokF.pinsRel.2.2.2.2.2.2
  have hblkR' : EBlk EH oR (C.pins.reserved.map Enc.idxW) := hblkR
  refine specR_envLoadI kdL _ (C.PO + pinCount + 4) wR (by decide) rfl hwR ?_
  have hlR : (ctxFe (ctxH CI H5) (C.fe.push ci)).EH[oR]? = some (BitVec.ofNat 64 C.pins.reserved.length) := by
    have h := hblkR'.1; simp only [List.length_map] at h; exact h
  refine specR_envLoadI kdLn (vv kdL) oR _ (by decide) (by simp [Env.get, hwoR]; rfl) hlR ?_
  refine specR_atEntry fun t5 ht5 => ?_
  have hlenR : C.pins.reserved.length < 2 ^ 62 := by
    have hl2 : EH.length ≤ C.EN := ht5.sr.env.1.len
    have hlay : C.EB.toNat + 8 * C.EN + 8 < 2 ^ 64 := hokF.envLay
    rcases Nat.eq_zero_or_pos C.pins.reserved.length with h0 | hpos
    · omega
    · have h1 := hblkR'.2 (C.pins.reserved.length - 1) (by simp; omega)
      have hlt : oR + 1 + (C.pins.reserved.length - 1) < EH.length := (List.getElem?_eq_some_iff.mp h1).1
      omega
  refine specR_callPure (C := ctxFe (ctxH CI H5) (C.fe.push ci)) kdX fRsm rmParams
    [vv kdN, vv kdL, .const 0, vv kdLn] rsmBody
    [Enc.idxW cv.name, ecell C oR, BitVec.ofNat 64 0, BitVec.ofNat 64 C.pins.reserved.length]
    (C.pins.reserved.contains cv.name) (by decide) rfl (by decide) hc.rsm
    ⟨by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, kdParams, ctxEnv], by simp [Env.get, hwoR]; rfl,
      rfl, by simp +decide [Env.get], trivial⟩
    (PostB (ctxFe (ctxH CI H5) (C.fe.push ci))) (fun b w _ _ => w = boolW b)
    (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rmParams _ rfl hlk)
      (rsm_spec (ctxFe (ctxH CI H5) (C.fe.push ci)) hc.rsm C.pins.reserved oR hblkR' hlenR cv.name _ _ 0
        (ctxFe (ctxH CI H5) (C.fe.push ci)).H (List.prefix_refl _) rfl (Nat.zero_le _)))
    (fun w H6 hp6 hw => ?_)
  subst hw
  refine specR_failIteF (c := !C.pins.reserved.contains cv.name) _ (boolW (C.pins.reserved.contains cv.name))
    (by simp +decide [sev, Env.get]; exact nez_b _)
    (fun h => by
      have e : C.pins.reserved.contains cv.name = false := by simpa using h
      rw [e]; rfl)
    (fun h => by
      have e : C.pins.reserved.contains cv.name = true := by simpa using h
      rw [e]; decide) (fun _ => ?_)
  exact specR_returnI _ 0 rfl (fun t ht => ⟨EH, C.envM.insert cv.name (ecell C ox), H6, hpE,
    hp14.trans (hp5.trans hp6), ctxOK_H hokF H6, sr_of_eq ht.sr rfl rfl rfl rfl, hg.push ci, hF.push ci,
    by unfold LitsPinned; rw [IFEnv.push_base]; exact hL⟩)



end


/-- An opaque's value check returns the opaque as an axiom. -/
theorem checkOpaqueVal_ci {mode : ConLeche.CheckMode} {fe : IFEnv} {cv : IConstantVal} {v : EIdx}
    {s s' : AState} {ci : IConstantInfo}
    (h : checkOpaqueVal mode fe cv v s = .ok (ci, s')) : ci = .axiomInfo cv := by
  have e : checkOpaqueVal mode fe cv v = (do
      valueGuards fe cv v
      let vtype ← inferTypeCore mode fe checkFuel 0 v
      unless ← isDefEqCore mode fe checkFuel 0 vtype cv.type do
        fail (.invalid "type mismatch in opaque")) >>= fun _ => pure (.axiomInfo cv) := by
    unfold checkOpaqueVal; simp only [bind_assoc]
    congr 1; funext _; congr 1; funext _; congr 1; funext x
    split <;> simp
  rw [e] at h
  exact ok_of_bind_pure h

/-- A theorem's check returns the theorem. -/
theorem checkThmVal_ci {mode : ConLeche.CheckMode} {fe : IFEnv} {cv : IConstantVal} {v : EIdx}
    {s s' : AState} {ci : IConstantInfo}
    (h : checkThmVal mode fe cv v s = .ok (ci, s')) : ci = .thmInfo cv := by
  have e : checkThmVal mode fe cv v = (do
      let stype ← inferTypeCore mode fe checkFuel 0 cv.type
      let u ← ensureSortCore mode fe checkFuel 0 stype
      let z ← zeroLevel
      unless ← liftFueled "level comparison" (← lvlEq? u z) do
        fail (.invalid "type of theorem is not a proposition")
      valueGuards fe cv v
      let vtype ← inferTypeCore mode fe checkFuel 0 v
      unless ← isDefEqCore mode fe checkFuel 0 vtype cv.type do
        fail (.invalid "type mismatch in theorem")) >>= fun _ => pure (.thmInfo cv) := by
    unfold checkThmVal
    simp only [bind_assoc, ite_bindM, pure_bind]
  rw [e] at h
  exact ok_of_bind_pure h

section
variable {σ : Type}

set_option maxHeartbeats 2000000 in
/-- **`checkDecl` at an opaque**. -/
theorem ko_spec (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (C : Ctx) (hok : CtxOK C)
    (hc : DeclCodes mode C) (ra : ConPanqueque.Hash.RuntimeAssumptions) (hs : C.side = false)
    (hpl : C.saved = none) (hg : TblGate C.fe) (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins)
    (cv : IConstantVal) (v : EIdx) (q o : Nat)
    (hn : C.H[q]? = some (Enc.idxW cv.name)) (hl : C.H[q + 1]? = some (cellA C o))
    (ht : C.H[q + 2]? = some (Enc.idxW cv.type)) (hb : BlkAt C.H o (cv.levelParams.map Enc.idxW))
    (hlen : cv.levelParams.length < 2 ^ 59) (ks : List ConLeche.Name) (hkl : ks.length = cv.levelParams.length)
    (hks : ∀ j (hj : j < cv.levelParams.length), denoteN C.St.ns cv.levelParams[j] = some (ks[j]'(by omega)))
    (htyD : (denoteE C.St cv.type).isSome = true) (s : AState) :
    SpecR (σ := σ) (Pre C s (kdParams.zip [cellA C q, Enc.idxW v, 0])) (koBody C) s
      (checkDecl mode pins C.fe (.opaqueDecl cv v)) (PostStep C) := by
  refine specR_prologue (postStep_locals C) (kd_none C _) ?_
  unfold checkDecl checkDeclKind
  dsimp only
  simp only [bind_assoc]
  refine UD.specR_heapLoadI' (C := C) kdN _ q _ hn (by decide) (by simp +decide [Env.get, kdParams, ctxEnv]) ?_
  -- the front door
  refine specR_callNIH (C := C) kdX fCcv ccvParams [vv kdQ, .const 0, .const 1, .const 0] (ccvBody C)
    [cellA C q, boolW false, boolW true, boolW false] (by decide) rfl (by decide) hc.ccv
    ⟨(by simp +decide [Env.get, kdParams, ctxEnv]), rfl, rfl, rfl, trivial⟩
    (fun a w s' st => checkConstantVal mode C.fe cv false true false s = .ok (a, s') ∧ PostU C a w s' st)
    (fun a w s' H' => checkConstantVal mode C.fe cv false true false s = .ok (a, s'))
    (fun a w s' st ⟨hrun, H', hp', hsr⟩ => ⟨H', hp', hrun, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ccvParams _ rfl hlk)
      (specR_run (ccv_full mode C hok hc.k.g hc.k.p hc.pim ra hs hc.k hc.ac hc.lso hc.lsoc hc.ndh hc.ndg hc.lbb hc.cB
        hc.bvb hc.hf hc.cF hc.fvb hc.atc hc.al hc.crff hc.crf hc.ens C.fe rfl cv false true false q o hn hl ht hb
        (by omega) ks hkl hks s)))
    (fun _ w s1 H1 hp1 hrun1 => ?_)
  have hnew := ccv_fresh hrun1
  have hok1 := ctxOK_H hok H1
  -- the value check
  refine specR_callNIH (C := ctxH C H1) kdX fDv dvParams [vv kdQ, vv kdV] dvBody [cellA C q, Enc.idxW v]
    (by decide) rfl (by decide) hc.dv ⟨(by simp +decide [Env.get, kdParams, ctxEnv]), (by simp +decide [Env.get, kdParams, ctxEnv]), trivial⟩
    (fun a w s' st => checkOpaqueVal mode C.fe cv v s1 = .ok (a, s') ∧ PostCI (ctxH C H1) a w s' st)
    (fun a w s' H' => checkOpaqueVal mode C.fe cv v s1 = .ok (a, s'))
    (fun a w s' st ⟨hrun, H', hp', hsr⟩ => ⟨H', hp', hrun, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu dvParams _ rfl hlk)
      (specR_run (opaque_spec mode (ctxH C H1) hok1 ra hs (kcodes_H hc.k H1) (allCodes_H hc.ac H1) hc.vg cv v q
        (fun H s' hp => vg_spec (ctxH C H) (ctxOK_H hok H) hc.lbb (by ctx_tr hc.cB) hc.bvb hc.hf (by ctx_tr hc.cF) hc.fvb
          hc.atc (by ctx_tr hc.al) hc.crff (by ctx_tr hc.crf) C.fe rfl cv v q o (get_prefix hl (hp1.trans hp))
          (blkAt_mono hb (hp1.trans hp)) (by omega) ks hkl hks s')
        (get_prefix ht hp1) s1)))
    (fun ci w s2 H2 hp2 hrun2 => ?_)
  have hci := checkOpaqueVal_ci hrun2
  subst hci
  have hp12 : C.H <+: H2 := hp1.trans hp2
  have hok2 := ctxOK_H hok H2
  -- the pinned reduce operations: the port stops at them
  refine specR_atEntry fun t2 ht2 => ?_
  have hpins := ht2.sr.pins
  refine specR_runBind (reduceOpNames_run hok2 hpins) ?_
  rw [ite_bindM]
  rw [reduceOps_contains]
  refine specR_callPure (C := ctxH C H2) kdX fPim pmParams [vv kdN, .const 43, .const 45] (pimBody C)
    [Enc.idxW cv.name, BitVec.ofNat 64 43, BitVec.ofNat 64 45] (pinIn C 43 45 cv.name) (by decide) rfl (by decide) hc.pim
    ⟨(by simp +decide [Env.get, kdParams, ctxEnv]), rfl, rfl, trivial⟩ (PostB (ctxH C H2)) (fun b w _ _ => w = boolW b)
    (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pmParams _ rfl hlk)
      (pim_spec C hok hc.pim s2 cv.name 45 (by decide) _ 43 H2 hp12 rfl (by omega)))
    (fun w H4 hp4 hw => ?_)
  subst hw
  refine specR_failIteT (c := pinIn C 43 45 cv.name) _ (boolW (pinIn C 43 45 cv.name))
    (by simp +decide [sev, Env.get]; exact nez_b _) (boolW_ne _) (boolW_eq _) (fun _ => ?_)
  have hp13 : C.H <+: H2 := hp12
  -- install
  have hp14 : C.H <+: H4 := hp13.trans hp4
  have hok4 := ctxOK_H hok H4
  have hden : NewDen (.axiomInfo cv) s2.store := by
    refine ⟨fun n hn' => ?_, denoteE_isSome_ext ht2.sr.floor htyD, by show cv.levelParams.length + 1 < 2 ^ 60; omega,
      fun cv' v' h' e => (by cases e), fun _ _ e => (by cases e)⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hn'
    exact Option.isSome_iff_exists.mpr ⟨_, denoteN_ext (hks j hj) ht2.sr.floor⟩
  refine specR_callNC (C := ctxH C H4) (D := ctxLocals ++ kdLocals) kdX fInst inParams
    [.const 0, vv kdQ, vv kdV, vv kdHn] (instBody C)
    [0, cellA C q, Enc.idxW v, 0] (by decide) rfl (by decide) hc.inst ?_
    (fun a w s' st => (pure (C.fe.push (.axiomInfo cv)) : AM IFEnv) s2 = .ok (a, s') ∧
      PostInst (ctxH C H4) (.axiomInfo cv) a w s' st)
    (fun a w s' C' => s' = s2 ∧ a = C.fe.push (.axiomInfo cv) ∧ ∃ EH ox, C' = ctxIns (ctxH C H4)
        ((C.fe.push (.axiomInfo cv)).setFlags C.fe.natLit C.fe.strLit) EH
        (C.envM.insert cv.name (ecell C ox)) ∧ C.EH <+: EH ∧ CIE C.EB EH ox (.axiomInfo cv))
    (fun a w s' st ⟨hrun, ⟨EH, ox, hpE, hcie, hsr⟩⟩ => by
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      exact ⟨_, ⟨hrun.2.symm, hrun.1.symm, EH, ox, rfl, hpE, hcie⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu inParams _ rfl hlk)
      (specR_run (inst_spec (ctxH C H4) hok4 hc.cp hc.k.s hc.k.i s2 (.axiomInfo cv) q o
        (get_prefix hn hp14) (get_prefix hl hp14) (get_prefix ht hp14) (blkAt_mono hb hp14)
        (by show cv.levelParams.length < 2 ^ 60; omega)
        0 (Enc.idxW v) 0 (fun EH ox b h => cie_axiom h) hg hnew hden
        (fun _ _ _ _ _ e => by cases e))))
    (fun a w s3 C3 ⟨hs3, ha, EH, ox, eC, hpE, hcie⟩ => ?_)
  · exact ⟨rfl, (by simp +decide [Env.get, kdParams, ctxEnv]), (by simp +decide [Env.get, kdParams, ctxEnv]), (by simp +decide [Env.get, kdParams, ctxEnv]), trivial⟩
  subst eC hs3 ha
  -- the literal flags
  set ci : IConstantInfo := .axiomInfo cv with hcidef
  set CI := ctxIns (ctxH C H4) ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit) EH (C.envM.insert cv.name (ecell C ox))
    with hCI
  have hokI : CtxOK CI := ctxOK_ins hok4 hpE hcie (pushOld_find C.fe ci) (pushOld_findTable hg ci hnew)
  have hfP : ∀ n, (C.fe.push ci).find? n = CI.fe.find? n := fun n => (IFEnv.setFlags_find? _ _ _ n).symm
  have htP : ∀ n, (C.fe.push ci).findTable? n = CI.fe.findTable? n := fun n => by
    show _ = ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit).findTable? n
    unfold IFEnv.findTable?; rw [IFEnv.setFlags_find?, IFEnv.setFlags_rawTable?]
  obtain ⟨hfn, hfs⟩ := push_flags_found (C := ctxH C H4) hF hL ci ox EH
  refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => (pure (C.fe.push ci) >>= fun fe₂ => (do
      flushCaches
      let b ← basisNamesOk (IDeclaration.opaqueDecl cv v)
      if b = true then pure fe₂ else do
        let e ← basisNamesError (IDeclaration.opaqueDecl cv v)
        fail e))) rfl ?_
  refine specR_callNC (C := CI) (D := ctxLocals ++ kdLocals) kdX fFlags [] [] flBody [] (by decide) rfl (by decide)
    hc.flags trivial (fun a w s' st => PostFl CI (C.fe.push ci) a w s' st ∧ s' = s3)
    (fun _ w s' C' => s' = s3 ∧ ∃ H5, C' = ctxFe (ctxH CI H5) (C.fe.push ci) ∧ CI.H <+: H5)
    (fun a w s' st ⟨⟨H5, hp5, hsr⟩, hs'⟩ => ⟨_, ⟨hs', H5, rfl, hp5⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [] _ rfl hlk)
      (specR_pureState (fl_spec CI hokI hc.natF hc.strF hc.k.g hc.k.p s3 hfP htP hfn hfs)))
    (fun _ w s4 C4 ⟨hs4, H5, eC, hp5⟩ => ?_)
  subst eC hs4
  simp only [pure_bind]
  -- the flush
  have hokF : CtxOK (ctxFe (ctxH CI H5) (C.fe.push ci)) :=
    ctxOK_fe (ctxOK_H hokI H5) (fun n => hfP n) (fun n => htP n)
  refine specR_flushTopI hokF hpl false flushCaches rfl (by decide) ?_
  -- the reserved names
  simp only [basisNamesOk]
  refine specR_atEntry fun t4 ht4 => ?_
  refine specR_runBind (basisUnres_run hokF ht4.sr.pins cv.name) ?_
  obtain ⟨wR, hwR, oR, hwoR, hblkR⟩ := hokF.pinsRel.2.2.2.2.2.2
  have hblkR' : EBlk EH oR (C.pins.reserved.map Enc.idxW) := hblkR
  refine specR_envLoadI kdL _ (C.PO + pinCount + 4) wR (by decide) rfl hwR ?_
  have hlR : (ctxFe (ctxH CI H5) (C.fe.push ci)).EH[oR]? = some (BitVec.ofNat 64 C.pins.reserved.length) := by
    have h := hblkR'.1; simp only [List.length_map] at h; exact h
  refine specR_envLoadI kdLn (vv kdL) oR _ (by decide) (by simp [Env.get, hwoR]; rfl) hlR ?_
  refine specR_atEntry fun t5 ht5 => ?_
  have hlenR : C.pins.reserved.length < 2 ^ 62 := by
    have hl2 : EH.length ≤ C.EN := ht5.sr.env.1.len
    have hlay : C.EB.toNat + 8 * C.EN + 8 < 2 ^ 64 := hokF.envLay
    rcases Nat.eq_zero_or_pos C.pins.reserved.length with h0 | hpos
    · omega
    · have h1 := hblkR'.2 (C.pins.reserved.length - 1) (by simp; omega)
      have hlt : oR + 1 + (C.pins.reserved.length - 1) < EH.length := (List.getElem?_eq_some_iff.mp h1).1
      omega
  refine specR_callPure (C := ctxFe (ctxH CI H5) (C.fe.push ci)) kdX fRsm rmParams
    [vv kdN, vv kdL, .const 0, vv kdLn] rsmBody
    [Enc.idxW cv.name, ecell C oR, BitVec.ofNat 64 0, BitVec.ofNat 64 C.pins.reserved.length]
    (C.pins.reserved.contains cv.name) (by decide) rfl (by decide) hc.rsm
    ⟨by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, kdParams, ctxEnv], by simp [Env.get, hwoR]; rfl,
      rfl, by simp +decide [Env.get], trivial⟩
    (PostB (ctxFe (ctxH CI H5) (C.fe.push ci))) (fun b w _ _ => w = boolW b)
    (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rmParams _ rfl hlk)
      (rsm_spec (ctxFe (ctxH CI H5) (C.fe.push ci)) hc.rsm C.pins.reserved oR hblkR' hlenR cv.name _ _ 0
        (ctxFe (ctxH CI H5) (C.fe.push ci)).H (List.prefix_refl _) rfl (Nat.zero_le _)))
    (fun w H6 hp6 hw => ?_)
  subst hw
  refine specR_failIteF (c := !C.pins.reserved.contains cv.name) _ (boolW (C.pins.reserved.contains cv.name))
    (by simp +decide [sev, Env.get]; exact nez_b _)
    (fun h => by
      have e : C.pins.reserved.contains cv.name = false := by simpa using h
      rw [e]; rfl)
    (fun h => by
      have e : C.pins.reserved.contains cv.name = true := by simpa using h
      rw [e]; decide) (fun _ => ?_)
  exact specR_returnI _ 0 rfl (fun t ht => ⟨EH, C.envM.insert cv.name (ecell C ox), H6, hpE,
    hp14.trans (hp5.trans hp6), ctxOK_H hokF H6, sr_of_eq ht.sr rfl rfl rfl rfl, hg.push ci, hF.push ci,
    by unfold LitsPinned; rw [IFEnv.push_base]; exact hL⟩)


end

section
variable {σ : Type}

set_option maxHeartbeats 2000000 in
/-- **`checkDecl` at a theorem** (the level comparison's spec a hypothesis). -/
theorem kt_spec (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (C : Ctx) (hok : CtxOK C)
    (hc : DeclCodes mode C) (ra : ConPanqueque.Hash.RuntimeAssumptions) (hs : C.side = false)
    (hpl : C.saved = none) (hg : TblGate C.fe) (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins)
    (heqS : ∀ (H : List (BitVec 64)) (u v : LIdx) (s : AState) (lu lv : ConLeche.Level),
      denoteL s.store.ls u = some lu → denoteL s.store.ls v = some lv → CachesOK s →
      SpecR (σ := σ) (Pre (ctxH C H) s [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s (lvlEq? u v)
        (fun o w s' st => LLeq.PostOB (ctxH C H) o w s' st))
    (cv : IConstantVal) (v : EIdx) (q o : Nat)
    (hn : C.H[q]? = some (Enc.idxW cv.name)) (hl : C.H[q + 1]? = some (cellA C o))
    (ht : C.H[q + 2]? = some (Enc.idxW cv.type)) (hb : BlkAt C.H o (cv.levelParams.map Enc.idxW))
    (hlen : cv.levelParams.length < 2 ^ 59) (ks : List ConLeche.Name) (hkl : ks.length = cv.levelParams.length)
    (hks : ∀ j (hj : j < cv.levelParams.length), denoteN C.St.ns cv.levelParams[j] = some (ks[j]'(by omega)))
    (htyD : (denoteE C.St cv.type).isSome = true) (s : AState) :
    SpecR (σ := σ) (Pre C s (kdParams.zip [cellA C q, Enc.idxW v, 0])) (ktBody C) s
      (checkDecl mode pins C.fe (.thmDecl cv v)) (PostStep C) := by
  refine specR_prologue (postStep_locals C) (kd_none C _) ?_
  unfold checkDecl checkDeclKind
  dsimp only
  simp only [bind_assoc]
  refine UD.specR_heapLoadI' (C := C) kdN _ q _ hn (by decide) (by simp +decide [Env.get, kdParams, ctxEnv]) ?_
  -- the front door
  refine specR_callNIH (C := C) kdX fCcv ccvParams [vv kdQ, .const 0, .const 0, .const 0] (ccvBody C)
    [cellA C q, boolW false, boolW false, boolW false] (by decide) rfl (by decide) hc.ccv
    ⟨(by simp +decide [Env.get, kdParams, ctxEnv]), rfl, rfl, rfl, trivial⟩
    (fun a w s' st => checkConstantVal mode C.fe cv false false false s = .ok (a, s') ∧ PostU C a w s' st)
    (fun a w s' H' => checkConstantVal mode C.fe cv false false false s = .ok (a, s'))
    (fun a w s' st ⟨hrun, H', hp', hsr⟩ => ⟨H', hp', hrun, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ccvParams _ rfl hlk)
      (specR_run (ccv_full mode C hok hc.k.g hc.k.p hc.pim ra hs hc.k hc.ac hc.lso hc.lsoc hc.ndh hc.ndg hc.lbb hc.cB
        hc.bvb hc.hf hc.cF hc.fvb hc.atc hc.al hc.crff hc.crf hc.ens C.fe rfl cv false false false q o hn hl ht hb
        (by omega) ks hkl hks s)))
    (fun _ w s1 H1 hp1 hrun1 => ?_)
  have hnew := ccv_fresh hrun1
  have hok1 := ctxOK_H hok H1
  -- the theorem's check
  refine specR_callNIH (C := ctxH C H1) kdX fTh thParams [vv kdQ, vv kdV] (thBody C) [cellA C q, Enc.idxW v]
    (by decide) rfl (by decide) hc.th ⟨(by simp +decide [Env.get, kdParams, ctxEnv]), (by simp +decide [Env.get, kdParams, ctxEnv]), trivial⟩
    (fun a w s' st => checkThmVal mode C.fe cv v s1 = .ok (a, s') ∧ PostCI (ctxH C H1) a w s' st)
    (fun a w s' H' => checkThmVal mode C.fe cv v s1 = .ok (a, s'))
    (fun a w s' st ⟨hrun, H', hp', hsr⟩ => ⟨H', hp', hrun, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu thParams _ rfl hlk)
      (specR_run (thm_spec mode (ctxH C H1) hok1 ra hs (kcodes_H hc.k H1) (allCodes_H hc.ac H1) hc.ens hc.eqv
        (fun H u' v' s' lu lv h1 h2 h3 => heqS H u' v' s' lu lv h1 h2 h3) hc.dv cv v q
        (fun H s' hp => dv_spec mode (ctxH C H) (ctxOK_H hok H) ra hs (kcodes_H hc.k H) (allCodes_H hc.ac H) hc.vg cv v q
          (fun H' s'' hp' => vg_spec (ctxH C H') (ctxOK_H hok H') hc.lbb (by ctx_tr hc.cB) hc.bvb hc.hf (by ctx_tr hc.cF)
            hc.fvb hc.atc (by ctx_tr hc.al) hc.crff (by ctx_tr hc.crf) C.fe rfl cv v q o
            (get_prefix hl ((hp1.trans hp).trans hp')) (blkAt_mono hb ((hp1.trans hp).trans hp')) (by omega) ks hkl hks s'')
          (get_prefix ht (hp1.trans hp)) (.thmInfo cv) (.invalid "type mismatch in theorem") s')
        (get_prefix ht hp1) s1)))
    (fun ci w s2 H2 hp2 hrun2 => ?_)
  have hci := checkThmVal_ci hrun2
  subst hci
  have hp12 : C.H <+: H2 := hp1.trans hp2
  have hok2 := ctxOK_H hok H2
  refine specR_atEntry fun t2 ht2 => ?_
  -- install
  have hp14 : C.H <+: H2 := hp12
  have hok4 := ctxOK_H hok H2
  have hden : NewDen (.thmInfo cv) s2.store := by
    refine ⟨fun n hn' => ?_, denoteE_isSome_ext ht2.sr.floor htyD, by show cv.levelParams.length + 1 < 2 ^ 60; omega,
      fun cv' v' h' e => (by cases e), fun _ _ e => (by cases e)⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hn'
    exact Option.isSome_iff_exists.mpr ⟨_, denoteN_ext (hks j hj) ht2.sr.floor⟩
  refine specR_callNC (C := ctxH C H2) (D := ctxLocals ++ kdLocals) kdX fInst inParams
    [.const 2, vv kdQ, vv kdV, vv kdHn] (instBody C)
    [2, cellA C q, Enc.idxW v, 0] (by decide) rfl (by decide) hc.inst ?_
    (fun a w s' st => (pure (C.fe.push (.thmInfo cv)) : AM IFEnv) s2 = .ok (a, s') ∧
      PostInst (ctxH C H2) (.thmInfo cv) a w s' st)
    (fun a w s' C' => s' = s2 ∧ a = C.fe.push (.thmInfo cv) ∧ ∃ EH ox, C' = ctxIns (ctxH C H2)
        ((C.fe.push (.thmInfo cv)).setFlags C.fe.natLit C.fe.strLit) EH
        (C.envM.insert cv.name (ecell C ox)) ∧ C.EH <+: EH ∧ CIE C.EB EH ox (.thmInfo cv))
    (fun a w s' st ⟨hrun, ⟨EH, ox, hpE, hcie, hsr⟩⟩ => by
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      exact ⟨_, ⟨hrun.2.symm, hrun.1.symm, EH, ox, rfl, hpE, hcie⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu inParams _ rfl hlk)
      (specR_run (inst_spec (ctxH C H2) hok4 hc.cp hc.k.s hc.k.i s2 (.thmInfo cv) q o
        (get_prefix hn hp14) (get_prefix hl hp14) (get_prefix ht hp14) (blkAt_mono hb hp14)
        (by show cv.levelParams.length < 2 ^ 60; omega)
        2 (Enc.idxW v) 0 (fun EH ox b h => cie_thm h) hg hnew hden
        (fun _ _ _ _ _ e => by cases e))))
    (fun a w s3 C3 ⟨hs3, ha, EH, ox, eC, hpE, hcie⟩ => ?_)
  · exact ⟨rfl, (by simp +decide [Env.get, kdParams, ctxEnv]), (by simp +decide [Env.get, kdParams, ctxEnv]), (by simp +decide [Env.get, kdParams, ctxEnv]), trivial⟩
  subst eC hs3 ha
  -- the literal flags
  set ci : IConstantInfo := .thmInfo cv with hcidef
  set CI := ctxIns (ctxH C H2) ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit) EH (C.envM.insert cv.name (ecell C ox))
    with hCI
  have hokI : CtxOK CI := ctxOK_ins hok4 hpE hcie (pushOld_find C.fe ci) (pushOld_findTable hg ci hnew)
  have hfP : ∀ n, (C.fe.push ci).find? n = CI.fe.find? n := fun n => (IFEnv.setFlags_find? _ _ _ n).symm
  have htP : ∀ n, (C.fe.push ci).findTable? n = CI.fe.findTable? n := fun n => by
    show _ = ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit).findTable? n
    unfold IFEnv.findTable?; rw [IFEnv.setFlags_find?, IFEnv.setFlags_rawTable?]
  obtain ⟨hfn, hfs⟩ := push_flags_found (C := ctxH C H2) hF hL ci ox EH
  refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => (pure (C.fe.push ci) >>= fun fe₂ => (do
      flushCaches
      let b ← basisNamesOk (IDeclaration.thmDecl cv v)
      if b = true then pure fe₂ else do
        let e ← basisNamesError (IDeclaration.thmDecl cv v)
        fail e))) rfl ?_
  refine specR_callNC (C := CI) (D := ctxLocals ++ kdLocals) kdX fFlags [] [] flBody [] (by decide) rfl (by decide)
    hc.flags trivial (fun a w s' st => PostFl CI (C.fe.push ci) a w s' st ∧ s' = s3)
    (fun _ w s' C' => s' = s3 ∧ ∃ H5, C' = ctxFe (ctxH CI H5) (C.fe.push ci) ∧ CI.H <+: H5)
    (fun a w s' st ⟨⟨H5, hp5, hsr⟩, hs'⟩ => ⟨_, ⟨hs', H5, rfl, hp5⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [] _ rfl hlk)
      (specR_pureState (fl_spec CI hokI hc.natF hc.strF hc.k.g hc.k.p s3 hfP htP hfn hfs)))
    (fun _ w s4 C4 ⟨hs4, H5, eC, hp5⟩ => ?_)
  subst eC hs4
  simp only [pure_bind]
  -- the flush
  have hokF : CtxOK (ctxFe (ctxH CI H5) (C.fe.push ci)) :=
    ctxOK_fe (ctxOK_H hokI H5) (fun n => hfP n) (fun n => htP n)
  refine specR_flushTopI hokF hpl false flushCaches rfl (by decide) ?_
  -- the reserved names
  simp only [basisNamesOk]
  refine specR_atEntry fun t4 ht4 => ?_
  refine specR_runBind (basisUnres_run hokF ht4.sr.pins cv.name) ?_
  obtain ⟨wR, hwR, oR, hwoR, hblkR⟩ := hokF.pinsRel.2.2.2.2.2.2
  have hblkR' : EBlk EH oR (C.pins.reserved.map Enc.idxW) := hblkR
  refine specR_envLoadI kdL _ (C.PO + pinCount + 4) wR (by decide) rfl hwR ?_
  have hlR : (ctxFe (ctxH CI H5) (C.fe.push ci)).EH[oR]? = some (BitVec.ofNat 64 C.pins.reserved.length) := by
    have h := hblkR'.1; simp only [List.length_map] at h; exact h
  refine specR_envLoadI kdLn (vv kdL) oR _ (by decide) (by simp [Env.get, hwoR]; rfl) hlR ?_
  refine specR_atEntry fun t5 ht5 => ?_
  have hlenR : C.pins.reserved.length < 2 ^ 62 := by
    have hl2 : EH.length ≤ C.EN := ht5.sr.env.1.len
    have hlay : C.EB.toNat + 8 * C.EN + 8 < 2 ^ 64 := hokF.envLay
    rcases Nat.eq_zero_or_pos C.pins.reserved.length with h0 | hpos
    · omega
    · have h1 := hblkR'.2 (C.pins.reserved.length - 1) (by simp; omega)
      have hlt : oR + 1 + (C.pins.reserved.length - 1) < EH.length := (List.getElem?_eq_some_iff.mp h1).1
      omega
  refine specR_callPure (C := ctxFe (ctxH CI H5) (C.fe.push ci)) kdX fRsm rmParams
    [vv kdN, vv kdL, .const 0, vv kdLn] rsmBody
    [Enc.idxW cv.name, ecell C oR, BitVec.ofNat 64 0, BitVec.ofNat 64 C.pins.reserved.length]
    (C.pins.reserved.contains cv.name) (by decide) rfl (by decide) hc.rsm
    ⟨by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, kdParams, ctxEnv], by simp [Env.get, hwoR]; rfl,
      rfl, by simp +decide [Env.get], trivial⟩
    (PostB (ctxFe (ctxH CI H5) (C.fe.push ci))) (fun b w _ _ => w = boolW b)
    (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rmParams _ rfl hlk)
      (rsm_spec (ctxFe (ctxH CI H5) (C.fe.push ci)) hc.rsm C.pins.reserved oR hblkR' hlenR cv.name _ _ 0
        (ctxFe (ctxH CI H5) (C.fe.push ci)).H (List.prefix_refl _) rfl (Nat.zero_le _)))
    (fun w H6 hp6 hw => ?_)
  subst hw
  refine specR_failIteF (c := !C.pins.reserved.contains cv.name) _ (boolW (C.pins.reserved.contains cv.name))
    (by simp +decide [sev, Env.get]; exact nez_b _)
    (fun h => by
      have e : C.pins.reserved.contains cv.name = false := by simpa using h
      rw [e]; rfl)
    (fun h => by
      have e : C.pins.reserved.contains cv.name = true := by simpa using h
      rw [e]; decide) (fun _ => ?_)
  exact specR_returnI _ 0 rfl (fun t ht => ⟨EH, C.envM.insert cv.name (ecell C ox), H6, hpE,
    hp14.trans (hp5.trans hp6), ctxOK_H hokF H6, sr_of_eq ht.sr rfl rfl rfl rfl, hg.push ci, hF.push ci,
    by unfold LitsPinned; rw [IFEnv.push_base]; exact hL⟩)




end

end ConPanqueque.T.Decl
