import ConPanqueque.T.Ind.ConsCtors
import ConPanqueque.T.Decl.PinNames
import ConPanqueque.T.Ind.LpsEq
import ConPanqueque.Start.PinName

/-!
# `targetRecPins` (single-member blocks, one recursor)

`reservedRecName` is pin membership: pins `1 … 3`, `5 … 10`, `12`, `14 … 31`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC
open ConPanqueque.Start (vPn vKa strStepP strStep_spec strBytes)
open ConPanqueque.Front (FrontOK frontOK_H)

theorem pinAt_bindR {β : Type} {C : Ctx} (hok : CtxOK C) {s : AState} (hp : s.pins = C.pins) (i : Nat)
    (hi : i < pinCount) (k : NIdx → AM β) : (pinAt i >>= k) s = k C.pins.names[i]! s := by
  simp [bind, StateT.bind, Except.bind, pinAt_run hok hp i hi]

theorem pinIn_false {C : Ctx} {i e : Nat} {n : NIdx} (h : pinIn C i e n = false) :
    ∀ j, i ≤ j → j < e → n ≠ C.pins.names[j]! := by
  intro j hij hje hn
  have : pinIn C i e n = true := by
    unfold pinIn; rw [List.any_eq_true]
    exact ⟨j, List.mem_range'_1.mpr ⟨hij, by omega⟩, by simp [hn]⟩
  rw [h] at this; exact absurd this (by decide)

/-- **`reservedRecName`** on a name in none of its pin ranges: `false`, the state kept. -/
theorem reservedRecName_false {C : Ctx} (hok : CtxOK C) {s : AState} (hp : s.pins = C.pins) (n : NIdx)
    (h1 : pinIn C 1 4 n = false) (h2 : pinIn C 5 11 n = false) (h3 : pinIn C 12 13 n = false)
    (h4 : pinIn C 14 32 n = false) : reservedRecName n s = .ok (false, s) := by
  have hpc : pinCount = 52 := rfl
  have a1 := pinIn_false h1; have a2 := pinIn_false h2; have a3 := pinIn_false h3; have a4 := pinIn_false h4
  have hb : ∀ {β : Type} (i : Nat) (k : NIdx → AM β), i < 52 → (pinAt i >>= k) s = k C.pins.names[i]! s :=
    fun i k hi => pinAt_bindR hok hp i (by rw [hpc]; exact hi) k
  simp only [reservedRecName, litGuardNames, natOpNames, natDivModNames, reservedRecBool, pinNat, pinNatZero,
    pinNatSucc, pinString, pinStringOfList, pinList, pinListNil, pinListCons, pinChar, pinCharOfNat, natPredName,
    natAddName, natSubName, natMulName, natPowName, natBeqName, natBleName, natDivName, natModName, natGcdName,
    natLandName, natLorName, natXorName, natShiftLeftName, natShiftRightName, pinNatPred, pinNatAdd, pinNatSub,
    pinNatMul, pinNatPow, pinNatBeq, pinNatBle, pinNatDiv, pinNatMod, pinNatGcd, pinNatLand, pinNatLor, pinNatXor,
    pinNatShiftLeft, pinNatShiftRight, pinBool, pinBoolTrue, pinBoolFalse, PIN_NAT, PIN_NAT_ZERO, PIN_NAT_SUCC,
    PIN_STRING, PIN_STRING_OF_LIST, PIN_LIST, PIN_LIST_NIL, PIN_LIST_CONS, PIN_CHAR, PIN_CHAR_OF_NAT, PIN_NAT_PRED,
    PIN_NAT_ADD, PIN_NAT_SUB, PIN_NAT_MUL, PIN_NAT_POW, PIN_NAT_BEQ, PIN_NAT_BLE, PIN_NAT_DIV, PIN_NAT_MOD,
    PIN_NAT_GCD, PIN_NAT_LAND, PIN_NAT_LOR, PIN_NAT_XOR, PIN_NAT_SHIFT_LEFT, PIN_NAT_SHIFT_RIGHT, PIN_BOOL,
    PIN_BOOL_TRUE, PIN_BOOL_FALSE, bind_assoc, pure_bind]
  simp only [hb _ _ (by decide : 1 < 52), hb _ _ (by decide : 2 < 52), hb _ _ (by decide : 3 < 52),
    hb _ _ (by decide : 5 < 52), hb _ _ (by decide : 6 < 52), hb _ _ (by decide : 7 < 52), hb _ _ (by decide : 8 < 52),
    hb _ _ (by decide : 9 < 52), hb _ _ (by decide : 10 < 52), hb _ _ (by decide : 12 < 52)]
  have c1 : ([C.pins.names[1]!, C.pins.names[2]!, C.pins.names[3]!, C.pins.names[5]!, C.pins.names[6]!,
      C.pins.names[7]!, C.pins.names[8]!, C.pins.names[9]!, C.pins.names[10]!, C.pins.names[12]!].contains n) = false := by
    simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    exact ⟨a1 1 (by omega) (by omega), a1 2 (by omega) (by omega), a1 3 (by omega) (by omega),
      a2 5 (by omega) (by omega), a2 6 (by omega) (by omega), a2 7 (by omega) (by omega), a2 8 (by omega) (by omega),
      a2 9 (by omega) (by omega), a2 10 (by omega) (by omega), a3 12 (by omega) (by omega)⟩
  simp only [c1, Bool.false_eq_true, ↓reduceIte]
  simp only [hb _ _ (by decide : 14 < 52), hb _ _ (by decide : 15 < 52), hb _ _ (by decide : 16 < 52),
    hb _ _ (by decide : 17 < 52), hb _ _ (by decide : 18 < 52), hb _ _ (by decide : 19 < 52),
    hb _ _ (by decide : 20 < 52)]
  have c2 : ([C.pins.names[14]!, C.pins.names[15]!, C.pins.names[16]!, C.pins.names[17]!, C.pins.names[18]!,
      C.pins.names[19]!, C.pins.names[20]!].contains n) = false := by
    simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    exact ⟨a4 14 (by omega) (by omega), a4 15 (by omega) (by omega), a4 16 (by omega) (by omega),
      a4 17 (by omega) (by omega), a4 18 (by omega) (by omega), a4 19 (by omega) (by omega), a4 20 (by omega) (by omega)⟩
  simp only [c2, Bool.false_eq_true, ↓reduceIte]
  simp only [hb _ _ (by decide : 21 < 52), hb _ _ (by decide : 22 < 52), hb _ _ (by decide : 23 < 52),
    hb _ _ (by decide : 24 < 52), hb _ _ (by decide : 25 < 52), hb _ _ (by decide : 26 < 52),
    hb _ _ (by decide : 27 < 52), hb _ _ (by decide : 28 < 52)]
  have c3 : ([C.pins.names[21]!, C.pins.names[22]!, C.pins.names[23]!, C.pins.names[24]!, C.pins.names[25]!,
      C.pins.names[26]!, C.pins.names[27]!, C.pins.names[28]!].contains n) = false := by
    simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.or_eq_false_iff, beq_eq_false_iff_ne]
    exact ⟨a4 21 (by omega) (by omega), a4 22 (by omega) (by omega), a4 23 (by omega) (by omega),
      a4 24 (by omega) (by omega), a4 25 (by omega) (by omega), a4 26 (by omega) (by omega),
      a4 27 (by omega) (by omega), a4 28 (by omega) (by omega)⟩
  simp only [c3, Bool.false_eq_true, ↓reduceIte]
  simp only [hb _ _ (by decide : 29 < 52), hb _ _ (by decide : 30 < 52), hb _ _ (by decide : 31 < 52)]
  have e29 : (n == C.pins.names[29]!) = false := by simpa using a4 29 (by omega) (by omega)
  have e30 : (n == C.pins.names[30]!) = false := by simpa using a4 30 (by omega) (by omega)
  have e31 : (n == C.pins.names[31]!) = false := by simpa using a4 31 (by omega) (by omega)
  simp only [e29, Bool.false_eq_true, ↓reduceIte]
  rw [hb 30 _ (by decide)]
  beta_reduce
  rw [e30]; simp only [Bool.false_eq_true, ↓reduceIte]
  rw [hb 31 _ (by decide)]
  simp [e31, StateT.pure, pure, Except.pure]

def trpSh := ofString "trp_sh"
def trpOm := ofString "trp_om"
def trpOr := ofString "trp_or"
def trpLm := ofString "trp_lm"
def trpR0 := ofString "trp_r0"
def trpCr := ofString "trp_cr"
def trpTg := ofString "trp_tg"
def trpLr := ofString "trp_lr"
def trpP0 := ofString "trp_p0"
def trpQ := ofString "trp_q"
def trpLq := ofString "trp_lq"
def trpLg := ofString "trp_lg"
def trpEl := ofString "trp_el"
def trpB := ofString "trp_b"
def trpE := ofString "trp_e"
def trpBq := ofString "trp_bq"
def trpNr := ofString "trp_nr"
def trpA := ofString "trp_a"
def fTrp := ofString "targetRecPins"

def trpParams : List MlS := [trpSh]
def trpLocals : List MlS := [trpOm, trpOr, trpLm, trpR0, trpCr, trpTg, trpLr, trpP0, trpQ, trpLq, trpLg, trpEl, trpB,
  trpE, trpBq, trpNr, trpA, vPn, vKa]

/-- `x := pinNameMem(nr, i, e)`; a hit hangs. -/
def trpPin (i e : Nat) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.call (some (some (.local, trpA), none)) fPim [vv trpNr, .const (BitVec.ofNat 64 i), .const (BitVec.ofNat 64 e)])
    (.ite (.cmp .equal (vv trpA) (.const 0)) rest hang)

/-- After the comparand `trp_e` is built: the levels, the reserved names, the `T.rec` name. -/
def trpRest (C : Ctx) : ProgHOL 64 :=
  .seq (.call (some (some (.local, trpBq), none)) fLpsEq [vv trpLr, vv trpE])
  (.ite (.cmp .equal (vv trpBq) (.const 0)) hang
  (.seq (.assign .local trpNr (.load .one (vv trpCr)))
  (trpPin 1 4 (trpPin 5 11 (trpPin 12 13 (trpPin 14 32
  (.seq (.assign .local vPn (.load .one (vv trpQ)))
  (strStepP C "rec"
  (.ite (.cmp .equal (vv vPn) (vv trpNr)) (.return (.const 0)) hang)))))))))

def trpBody (C : Ctx) : ProgHOL 64 := prologue trpLocals
  (.seq (.assign .local trpOm (.load .one (vv trpSh)))
  (.seq (.assign .local trpOr (.load .one (.op .add [vv trpSh, .const 8])))
  (.seq (.assign .local trpLm (.load .one (vv trpOr)))
  (.ite (.cmp .equal (vv trpLm) (.const 1))
    (.seq (.assign .local trpR0 (.load .one (.op .add [vv trpOr, .const 8])))
    (.seq (.assign .local trpCr (.load .one (vv trpR0)))
    (.seq (.assign .local trpTg (.load .one (.op .add [vv trpR0, .const 24])))
    (.ite (.cmp .equal (vv trpTg) (.const 0))
      (.seq (.assign .local trpLr (.load .one (.op .add [vv trpCr, .const 8])))
      (.seq (.assign .local trpP0 (.load .one (.op .add [vv trpOm, .const 8])))
      (.seq (.assign .local trpQ (.load .one (vv trpP0)))
      (.seq (.assign .local trpLq (.load .one (.op .add [vv trpQ, .const 8])))
      (.seq (.assign .local trpLg (.load .one (.op .add [vv trpSh, .const 40])))
      (.ite (.cmp .equal (vv trpLg) (.const 0))
        (.seq (.assign .local trpE (vv trpLq)) (trpRest C))
        (.seq (.assign .local trpEl (.load .one (.op .add [vv trpSh, .const 24])))
        (alloc2 C trpB (.const 1) (vv trpEl)
        (.seq (.call (some (some (.local, trpE), none)) fCat [vv trpB, vv trpLq, .const 0])
          (trpRest C))))))))))
      hang))))
    hang))))

structure TRPCodes (C : Ctx) : Prop where
  pim : C.code.lookup fPim = some (Decl.pmParams.map (fun p => (p, ShapeHOL.one)), pimBody C, .one)
  leg : C.code.lookup fLpsEqGo = some (legParams.map (fun p => (p, ShapeHOL.one)), legBody, .one)
  le : C.code.lookup fLpsEq = some (leParams.map (fun p => (p, ShapeHOL.one)), leBody, .one)
  cat : CatCodes C
  nstr : C.code.lookup Front.fInternNStr =
    some ([(Front.pKeyN, .one), (lEn, .one), (lEp, .one), (lHn, .one)], Front.nameStrBody, .one)
  self : C.code.lookup fTrp = some (trpParams.map (fun p => (p, ShapeHOL.one)), trpBody C, .one)

section
variable {σ : Type}

theorem trp_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ trpLocals → (ctxEnv C ++ trpParams.zip vals).get x = none :=
  Knot.params_none C trpLocals trpParams vals (by decide) (by decide)

/-- The stream-side part of `targetRecPins` the port does not re-check: the block splits with one former, the
recursors as read, and the constructors in block order. -/
def SplitOK (p : BlockShape) (block : List IConstantInfo) : Prop :=
  ∃ cvTs cs rs, blockSplit block = some (cvTs, cs, rs) ∧ cvTs.length = p.k ∧ rs.length = p.recs.length ∧
    p.allCtors.map (·.1.name) = cs.map (·.1.name)


theorem am_bind_run {α β : Type} {x : AM α} {f : α → AM β} {s s1 : AState} {a : α} (h : x s = .ok (a, s1)) :
    (x >>= f) s = f a s1 := by rw [AM.bind_apply, h]; rfl

/-- The simplified twin the port runs: the levels, the reserved names, the `T.rec` name. -/
def trpM (p : BlockShape) (ms0 : MemberShape) (rc0 : RecShape) (X : CheckError) : AM Unit :=
  if blockRecLpsOk p then
    reservedRecName rc0.cvR.name >>= fun b =>
      if b then fail X else internNNode (.str ms0.cvT.name "rec") >>= fun h =>
        if h = rc0.cvR.name then pure () else fail X
  else fail X

theorem trp_twin (p : BlockShape) (ms0 : MemberShape) (rc0 : RecShape) (hms : p.members = [ms0])
    (hrs : p.recs = [rc0]) (htg : rc0.tgt = 0) (block : List IConstantInfo) (hsp : SplitOK p block) (X : CheckError) :
    ∀ a s s', trpM p ms0 rc0 X s = .ok (a, s') → targetRecPins p block s = .ok (a, s') := by
  intro a s s' h
  obtain ⟨cvTs, cs, rs, hbs, hk, hr, hcn⟩ := hsp
  unfold trpM at h
  by_cases hl : blockRecLpsOk p
  swap
  · simp only [hl, Bool.false_eq_true, ↓reduceIte] at h; exact (AM.fail_ok h).elim
  simp only [hl, ↓reduceIte] at h
  obtain ⟨b, s1, hb, h2⟩ := AM.bind_ok h
  cases b
  swap
  · simp only [↓reduceIte] at h2; exact (AM.fail_ok h2).elim
  simp only [Bool.false_eq_true, ↓reduceIte] at h2
  obtain ⟨hn, s2, hi, h3⟩ := AM.bind_ok h2
  by_cases he : hn = rc0.cvR.name
  swap
  · simp only [he, ↓reduceIte] at h3; exact (AM.fail_ok h3).elim
  simp only [he, ↓reduceIte] at h3
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h3
  subst he
  have hk1 : p.k = 1 := by simp [BlockShape.k, hms]
  unfold targetRecPins
  simp only [hl, hms, hrs, htg, hk1, hbs, hk, hr, hcn, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    List.filter_cons, List.filter_nil, Nat.lt_irrefl, decide_true, decide_false, Bool.not_false,
    blockRecNamesUnreserved, blockRecNameSetOk, List.mapM_cons, List.mapM_nil, List.length_nil, List.range_zero,
    nameNodup, List.map_cons, List.map_nil, List.contains_nil, beq_self_eq_true, Bool.and_self, bind_assoc,
    pure_bind, Nat.zero_lt_one]
  rw [am_bind_run hb]
  simp only [Bool.false_eq_true, ↓reduceIte, pure_bind]
  rw [am_bind_run hi]
  simp [pure, StateT.pure, Except.pure]

set_option maxHeartbeats 16000000 in
/-- The tail: the levels compared, the reserved names, the `T.rec` name. -/
theorem trpRest_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : FrontOK C)
    (hc : TRPCodes C) (p : BlockShape) (ms0 : MemberShape) (rc0 : RecShape) (X : CheckError)
    (Hx : List (BitVec 64)) (hpx : C.H <+: Hx) (ys : List NIdx) (hys : blockRecLpsOk p = (rc0.cvR.levelParams == ys))
    (olr oe ocr oq : Nat) (hblr : EBlk Hx olr (rc0.cvR.levelParams.map Enc.idxW)) (hbe : EBlk Hx oe (ys.map Enc.idxW))
    (hnr : Hx[ocr]? = some (Enc.idxW rc0.cvR.name)) (hqn : Hx[oq]? = some (Enc.idxW ms0.cvT.name))
    (hlr : rc0.cvR.levelParams.length < 2 ^ 59) (hly : ys.length < 2 ^ 59) (s : AState) (Γ : Env) (M : Mem)
    (gLr : Γ.get trpLr = some (cellA C olr)) (gE : Γ.get trpE = some (cellA C oe))
    (gCr : Γ.get trpCr = some (cellA C ocr)) (gQ : Γ.get trpQ = some (cellA C oq)) :
    SpecR (σ := σ) (Inv (ctxH C Hx) s Γ M (ctxLocals ++ trpLocals)) (trpRest C) s (trpM p ms0 rc0 X) (Decl.PostU C) := by
  unfold trpRest
  refine specR_congr (m' := (pure (rc0.cvR.levelParams == ys) : AM Bool) >>= fun b => if b then
    (reservedRecName rc0.cvR.name >>= fun b =>
      if b then fail X else internNNode (.str ms0.cvT.name "rec") >>= fun h =>
        if h = rc0.cvR.name then pure () else fail X) else fail X) (by simp [trpM, hys]) ?_
  refine specR_callNIH (C := ctxH C Hx) trpBq fLpsEq leParams [vv trpLr, vv trpE] leBody
    [cellA C olr, cellA C oe] (by decide) rfl (by decide) hc.le
    ⟨by simp [sev, gLr], by simp [sev, Env.get_cons, gE], trivial⟩
    (PostB (ctxH C Hx)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu leParams _ rfl hlk)
      (le_spec C hc.leg hc.le _ _ olr oe (by omega) (by omega) Hx s hpx hblr hbe))
    (fun b w s1 H1 hp1 hw => ?_)
  subst hw
  have hp1' : Hx <+: H1 := hp1
  cases b
  · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI)
      (fun h => absurd h (by decide))
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
  simp only [↓reduceIte]
  refine UD.specR_heapLoadI' (C := ctxH C H1) trpNr (vv trpCr) ocr _ (get_prefix hnr hp1') (by decide)
    (by simp [sev, Env.get_cons, gCr]; rfl) ?_
  have hq1 : C.H <+: H1 := hpx.trans hp1'
  refine specR_callPure (C := ctxH C H1) trpA fPim Decl.pmParams
    [vv trpNr, .const (BitVec.ofNat 64 1), .const (BitVec.ofNat 64 4)] (pimBody C)
    [Enc.idxW rc0.cvR.name, BitVec.ofNat 64 1, BitVec.ofNat 64 4] (pinIn C 1 4 rc0.cvR.name) (by decide) rfl
    (by decide) hc.pim ⟨by simp +decide [sev, Env.get_cons], rfl, rfl, trivial⟩ (PostB (ctxH C H1))
    (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu Decl.pmParams _ rfl hlk)
      (pim_spec C hok hc.pim s1 rc0.cvR.name 4 (by decide) _ 1 H1 hq1 rfl (by omega)))
    (fun w H2 hqH2 hw => ?_)
  subst hw
  cases hb1 : pinIn C 1 4 rc0.cvR.name
  swap
  · exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hb1, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hb1, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
    (fun h => absurd h (by decide))
  have hq2' : C.H <+: H2 := hq1.trans hqH2
  refine specR_callPure (C := ctxH C H2) trpA fPim Decl.pmParams
    [vv trpNr, .const (BitVec.ofNat 64 5), .const (BitVec.ofNat 64 11)] (pimBody C)
    [Enc.idxW rc0.cvR.name, BitVec.ofNat 64 5, BitVec.ofNat 64 11] (pinIn C 5 11 rc0.cvR.name) (by decide) rfl
    (by decide) hc.pim ⟨by simp +decide [sev, Env.get_cons], rfl, rfl, trivial⟩ (PostB (ctxH C H2))
    (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu Decl.pmParams _ rfl hlk)
      (pim_spec C hok hc.pim s1 rc0.cvR.name 11 (by decide) _ 5 H2 hq2' rfl (by omega)))
    (fun w H3 hqH3 hw => ?_)
  subst hw
  cases hb5 : pinIn C 5 11 rc0.cvR.name
  swap
  · exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hb5, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hb5, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
    (fun h => absurd h (by decide))
  have hq3' : C.H <+: H3 := hq2'.trans hqH3
  refine specR_callPure (C := ctxH C H3) trpA fPim Decl.pmParams
    [vv trpNr, .const (BitVec.ofNat 64 12), .const (BitVec.ofNat 64 13)] (pimBody C)
    [Enc.idxW rc0.cvR.name, BitVec.ofNat 64 12, BitVec.ofNat 64 13] (pinIn C 12 13 rc0.cvR.name) (by decide) rfl
    (by decide) hc.pim ⟨by simp +decide [sev, Env.get_cons], rfl, rfl, trivial⟩ (PostB (ctxH C H3))
    (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu Decl.pmParams _ rfl hlk)
      (pim_spec C hok hc.pim s1 rc0.cvR.name 13 (by decide) _ 12 H3 hq3' rfl (by omega)))
    (fun w H4 hqH4 hw => ?_)
  subst hw
  cases hb12 : pinIn C 12 13 rc0.cvR.name
  swap
  · exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hb12, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hb12, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
    (fun h => absurd h (by decide))
  have hq4' : C.H <+: H4 := hq3'.trans hqH4
  refine specR_callPure (C := ctxH C H4) trpA fPim Decl.pmParams
    [vv trpNr, .const (BitVec.ofNat 64 14), .const (BitVec.ofNat 64 32)] (pimBody C)
    [Enc.idxW rc0.cvR.name, BitVec.ofNat 64 14, BitVec.ofNat 64 32] (pinIn C 14 32 rc0.cvR.name) (by decide) rfl
    (by decide) hc.pim ⟨by simp +decide [sev, Env.get_cons], rfl, rfl, trivial⟩ (PostB (ctxH C H4))
    (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu Decl.pmParams _ rfl hlk)
      (pim_spec C hok hc.pim s1 rc0.cvR.name 32 (by decide) _ 14 H4 hq4' rfl (by omega)))
    (fun w H5 hqH5 hw => ?_)
  subst hw
  cases hb14 : pinIn C 14 32 rc0.cvR.name
  swap
  · exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hb14, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hb14, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
    (fun h => absurd h (by decide))
  have hq5' : C.H <+: H5 := hq4'.trans hqH5
  refine specR_atEntry fun t5 ht5 => ?_
  refine specR_runBind (reservedRecName_false hok ht5.sr.pins rc0.cvR.name hb1 hb5 hb12 hb14) ?_
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hp15 : Hx <+: H5 := hp1'.trans ((hqH2 : H1 <+: H2).trans ((hqH3 : H2 <+: H3).trans
    ((hqH4 : H3 <+: H4).trans (hqH5 : H4 <+: H5))))
  refine UD.specR_heapLoadI' (C := ctxH C H5) vPn (vv trpQ) oq _ (get_prefix hqn hp15) (by decide)
    (by simp [sev, Env.get_cons, gQ]; rfl) ?_
  refine strStep_spec ra (ctxH C H5) (ctxOK_H hok H5) (frontOK_H hf H5) hc.nstr s1 _ _ (ctxLocals ++ trpLocals) (by decide) (by decide)
    ms0.cvT.name (by simp [Env.get_cons]) "rec" (by decide) (fun h s' o hrun => ?_)
  by_cases hh : h = rc0.cvR.name
  · subst hh
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [↓reduceIte]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H5, hq5', sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · have hne : Enc.idxW h ≠ Enc.idxW rc0.cvR.name := fun e => hh (Enc.idxW_inj e)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h)
      (fun _ => specR_hangI)

set_option maxHeartbeats 16000000 in
/-- **`targetRecPins`** on a single-member block. -/
theorem trp_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : FrontOK C)
    (hc : TRPCodes C) (p : BlockShape) (ms0 : MemberShape) (hms : p.members = [ms0]) (block : List IConstantInfo)
    (hsp : SplitOK p block) (osh : Nat) (hsh : ShapeRep C C.H osh p)
    (hlq : ms0.cvT.levelParams.length < 2 ^ 58) (hlr : ∀ rc ∈ p.recs, rc.cvR.levelParams.length < 2 ^ 59)
    (s : AState) (hpins : s.pins = C.pins) :
    SpecR (σ := σ) (Pre C s (trpParams.zip [cellA C osh])) (trpBody C) s (targetRecPins p block) (Decl.PostU C) := by
  refine specR_prologue (Decl.postU_locals _) (trp_none _ _) ?_
  obtain ⟨⟨om, hom, hM⟩, ⟨or_, hor, hR⟩, hnPe, hel, hrs, hlg, hip⟩ := hsh
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : C.H.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  have hp0 : C.H <+: C.H := List.prefix_refl _
  refine UD.specR_heapLoadI' (C := ctxH C C.H) trpOm (vv trpSh) osh _ hom (by decide)
    (by simp +decide [sev, Env.get, trpParams, ctxEnv]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C C.H) trpOr _ (osh + 1) _ hor (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, trpParams, ctxEnv]; exact cellA_add8 C osh) ?_
  refine UD.specR_heapLoadI' (C := ctxH C C.H) trpLm (vv trpOr) or_ _ hR.1 (by decide)
    (by simp [sev, Env.get_cons]; rfl) ?_
  have hrl : p.recs.length < 2 ^ 61 := by
    rcases Nat.eq_zero_or_pos p.recs.length with h0 | hpos
    · omega
    · obtain ⟨o', h1, -⟩ := hR.2 (p.recs.length - 1) (by omega)
      have := (List.getElem?_eq_some_iff.mp h1).1; omega
  by_cases hl1 : p.recs.length = 1
  swap
  · have hne : BitVec.ofNat 64 p.recs.length ≠ 1#64 := fun h => hl1 (by
      have := congrArg BitVec.toNat h; simp at this; omega)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h)
      (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hl1]) (fun _ => ?_) (fun h => absurd h (by decide))
  obtain ⟨rc0, hrs⟩ := List.length_eq_one_iff.mp hl1
  obtain ⟨orc, horc, hrr⟩ := hR.2 0 (by omega)
  simp only [Nat.add_zero, hrs, List.getElem_cons_zero] at horc hrr
  obtain ⟨⟨ocr, hocr, hcvr⟩, -, -, htgE, -, -⟩ := hrr
  refine UD.specR_heapLoadI' (C := ctxH C C.H) trpR0 _ (or_ + 1) _ horc (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C or_) ?_
  refine UD.specR_heapLoadI' (C := ctxH C C.H) trpCr (vv trpR0) orc _ hocr (by decide)
    (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C C.H) trpTg _ (orc + 3) _ htgE.1 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C orc 3) ?_
  by_cases htg : rc0.tgt = 0
  swap
  · have hne : BitVec.ofNat 64 rc0.tgt ≠ 0#64 := fun h => htg (by
      have := congrArg BitVec.toNat h; have := htgE.2; simp at *; omega)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h)
      (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, htg]) (fun _ => ?_) (fun h => absurd h (by decide))
  refine specR_okMono (fun a s' h => trp_twin p ms0 rc0 hms hrs htg block hsp (.internal "targetRecPins") a s s' h) ?_
  obtain ⟨hnr, ⟨wr, hwr, hlrE⟩, -⟩ := hcvr
  obtain ⟨olr, rfl, hblr⟩ := enlist_cell hlrE
  refine UD.specR_heapLoadI' (C := ctxH C C.H) trpLr _ (ocr + 1) _ hwr (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C ocr) ?_
  rw [hms] at hM
  obtain ⟨o0, ho0, hmr⟩ := hM.2 0 (by simp)
  simp only [Nat.add_zero, List.getElem_cons_zero] at ho0 hmr
  obtain ⟨⟨oq, hoq, hcvq⟩, -, -, -⟩ := hmr
  obtain ⟨hqn, ⟨wq, hwq, hlq'⟩, -⟩ := hcvq
  obtain ⟨olq, rfl, hblq⟩ := enlist_cell hlq'
  refine UD.specR_heapLoadI' (C := ctxH C C.H) trpP0 _ (om + 1) _ ho0 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C om) ?_
  refine UD.specR_heapLoadI' (C := ctxH C C.H) trpQ (vv trpP0) o0 _ hoq (by decide)
    (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C C.H) trpLq _ (oq + 1) _ hwq (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C oq) ?_
  refine UD.specR_heapLoadI' (C := ctxH C C.H) trpLg _ (osh + 5) _ hlg (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, trpParams, ctxEnv]; exact cellA_add_ofNat C osh 5) ?_
  have hlr' := hlr rc0 (by simp [hrs])
  have hlpsP : p.lps = ms0.cvT.levelParams := by simp [BlockShape.lps, hms]
  cases hlarge : p.large
  · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, boolW]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    refine specR_assignI trpE (vv trpLq) (cellA C olq) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
    exact trpRest_spec ra C hok hf hc p ms0 rc0 _ C.H hp0 ms0.cvT.levelParams
      (by simp [blockRecLpsOk, hrs, hlarge, hlpsP]) olr olq ocr oq hblr hblq hnr hqn hlr' (by omega) s _ _
      (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons])
      (by simp +decide [Env.get_cons])
  · refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, boolW]) (fun h => absurd rfl h) (fun _ => ?_)
    refine UD.specR_heapLoadI' (C := ctxH C C.H) trpEl _ (osh + 3) _ hel (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, trpParams, ctxEnv]; exact cellA_add_ofNat C osh 3) ?_
    refine specR_alloc2I (ctxOK_H hok C.H) trpB (.const 1) (vv trpEl) (BitVec.ofNat 64 1) (Enc.idxW p.elim)
      (by decide) (fun _ => rfl) (fun _ => by simp +decide [sev, Env.get_cons]) (fun H2 ws2 hp2 hws2 => ?_)
    obtain ⟨k0, k1⟩ := img2_get H2 ws2 (BitVec.ofNat 64 1) (Enc.idxW p.elim) hws2
    have hp2' : C.H <+: _ := (hp2 : C.H <+: H2).trans (img2_prefix H2 ws2 (BitVec.ofNat 64 1) (Enc.idxW p.elim) hws2)
    have hb2 : BlkAt (((H2 ++ ws2).set H2.length (BitVec.ofNat 64 1)).set (H2.length + 1) (Enc.idxW p.elim))
        H2.length [Enc.idxW p.elim] := ⟨by simpa using k0, fun i hi => by simp at hi; subst hi; simpa using k1⟩
    refine specR_callPure (C := ctxH C _) trpE fCat catParams [vv trpB, vv trpLq, .const 0] catBody
      [cellA C H2.length, cellA C olq, BitVec.ofNat 64 0] ([Enc.idxW p.elim] ++ (ms0.cvT.levelParams.map Enc.idxW).drop 0)
      (by decide) rfl (by decide) hc.cat.self
      ⟨by simp [sev, Env.get_cons]; rfl, by simp +decide [sev, Env.get_cons] <;> rfl, rfl, trivial⟩
      (fun r w s' st => ∃ H' o, _ <+: H' ∧ s' = s ∧ w = cellA C o ∧ BlkAt H' o r ∧ SR (ctxH C H') s' st)
      (fun r w s' H' => ∃ o, w = cellA C o ∧ BlkAt H' o r)
      (fun r w s' st ⟨H', o, hp', hs', hw, hb', hsr⟩ => ⟨H', hp', ⟨o, hw, hb'⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu catParams _ rfl hlk)
        (cat_spec C hok hc.cat (ms0.cvT.levelParams.map Enc.idxW) olq (by simp; omega) _ 0 _ H2.length _ s rfl
          (by omega) hb2 (blkAt_mono hblq hp2')))
      (fun w H3 hp3 ⟨o3, hw3, hb3⟩ => ?_)
    subst hw3
    have hp3' : _ <+: H3 := hp3
    have hb3' : EBlk H3 o3 ((p.elim :: ms0.cvT.levelParams).map Enc.idxW) := by
      have h : BlkAt H3 o3 ((p.elim :: ms0.cvT.levelParams).map Enc.idxW) := by simpa using hb3
      exact h
    have hpC3 : C.H <+: H3 := hp2'.trans hp3'
    exact trpRest_spec ra C hok hf hc p ms0 rc0 _ H3 hpC3 (p.elim :: ms0.cvT.levelParams)
      (by simp [blockRecLpsOk, hrs, hlarge, hlpsP]) olr o3 ocr oq (eblk_mono hblr hpC3) hb3'
      (get_prefix hnr hpC3) (get_prefix hqn hpC3) hlr' (by simp; omega) s _ _
      (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons])
      (by simp +decide [Env.get_cons])

end

end ConPanqueque.T.Ind
