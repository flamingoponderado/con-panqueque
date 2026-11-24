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

end ConPanqueque.T.Decl
