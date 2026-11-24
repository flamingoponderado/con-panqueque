import ConPanqueque.T.Decl.AllLevelParams
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# Reserved names, and the reject

`pim` asks whether a name is among the pins `i … e-1` (the pin block in the environment heap): the certified
`Nat` operations are pins `14 … 28`, the reduce operations `43, 44`. `rejectP` is what the port does where the
twin fails: it stops (the soundness direction).
-/

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC
open ConPanqueque.V.Enc

/-- The port's reject: the twin failed, the program stops. -/
def rejectP : ProgHOL 64 := hang

section
variable {σ : Type}

theorem specR_rejectI {α : Type} {P : PState σ → Prop} {s : AState} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} : SpecR P rejectP s m R := specR_hangI

end

def pmN := ofString "pm_n"
def pmI := ofString "pm_i"
def pmE := ofString "pm_e"
def pmX := ofString "pm_x"
def pmR := ofString "pm_r"
def fPim := ofString "pinNameMem"

def pmParams : List MlS := [pmN, pmI, pmE]
def pmLocals : List MlS := [pmX, pmR]

def pimBody (C : Ctx) : ProgHOL 64 := prologue pmLocals
  (.ite (.cmp .lower (vv pmI) (vv pmE))
    (.seq (.assign .local pmX (.load .one (.op .add [.const (ecell C C.PO), .shift .lsl (vv pmI) (.const 3)])))
    (.ite (.cmp .equal (vv pmX) (vv pmN)) (.return (.const 1))
      (.seq (.call (some (some (.local, pmR), none)) fPim [vv pmN, .op .add [vv pmI, .const 1], vv pmE])
        (.return (vv pmR)))))
    (.return (.const 0)))

/-- Is `n` among pins `i … e-1`. -/
def pinIn (C : Ctx) (i e : Nat) (n : NIdx) : Bool := (List.range' i (e - i)).any fun j => n == C.pins.names[j]!

theorem pinIn_stop (C : Ctx) (i e : Nat) (n : NIdx) (h : e ≤ i) : pinIn C i e n = false := by
  simp [pinIn, show e - i = 0 by omega]

theorem pinIn_step (C : Ctx) (i e : Nat) (n : NIdx) (h : i < e) :
    pinIn C i e n = ((n == C.pins.names[i]!) || pinIn C (i + 1) e n) := by
  unfold pinIn
  rw [show e - i = (e - (i + 1)) + 1 by omega, List.range'_succ, List.any_cons]

section
variable {σ : Type}

theorem pm_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ pmLocals → (ctxEnv C ++ pmParams.zip vals).get x = none :=
  Knot.params_none C pmLocals pmParams vals (by decide) (by decide)

theorem pin_cell {C : Ctx} (hok : CtxOK C) (i : Nat) (hi : i < pinCount) :
    C.EH[C.PO + i]? = some (Enc.idxW C.pins.names[i]!) := by
  have hi' : i < C.pins.names.size := by rw [hok.pinsRel.1]; exact hi
  rw [getElem!_pos C.pins.names i hi']
  exact hok.pinsRel.2.1 i hi'

/-- **`pim`**. -/
theorem pim_spec (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fPim = some (pmParams.map (fun p => (p, ShapeHOL.one)), pimBody C, .one))
    (s : AState) (n : NIdx) (e : Nat) (he : e ≤ pinCount) :
    ∀ k i (H : List (BitVec 64)), C.H <+: H → e - i = k → i ≤ e →
      SpecR (σ := σ) (Pre (ctxH C H) s (pmParams.zip [Enc.idxW n, BitVec.ofNat 64 i, BitVec.ofNat 64 e]))
        (pimBody C) s (pure (pinIn C i e n)) (PostB (ctxH C H)) := by
  have hpc : pinCount = 52 := rfl
  intro k
  induction k with
  | zero =>
    intro i H hp hk hi
    have hie : i = e := by omega
    subst hie
    refine specR_prologue (postB_locals _) (pm_none _ _) ?_
    have hlw := nd_lt_iff i i (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, pmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [pinIn_stop C i i n (le_refl _)]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, by simp [boolW], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro i H hp hk hi
    have hil : i < e := by omega
    refine specR_prologue (postB_locals _) (pm_none _ _) ?_
    have hlw := nd_lt_iff i e (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, pmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_envLoadI (C := ctxH C H) pmX _ (C.PO + i) _ (by decide)
      (by simp +decide [sev, Env.get, pmParams, ctxEnv]; exact ecell_shl3 C C.PO i (by omega))
      (pin_cell (ctxOK_H hok H) i (by omega)) ?_
    rw [pinIn_step C i e n hil]
    by_cases heq : C.pins.names[i]! = n
    · refine specR_ifI _ 1 (by simp +decide [sev, Env.get, pmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, heq]; exact congrArg Enc.idxW heq)
        (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ 1 rfl (fun t ht => ⟨H, List.prefix_refl _, by simp [boolW, heq], sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · have hne : Enc.idxW C.pins.names[i]! ≠ Enc.idxW n := fun h => heq (idxW_inj h)
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get, pmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne]; exact hne)
        (fun h => absurd rfl h) (fun _ => ?_)
      rw [beq_false_of_ne (Ne.symm heq), Bool.false_or]
      refine specR_callPure (C := ctxH C H) pmR fPim pmParams [vv pmN, .op .add [vv pmI, .const 1], vv pmE]
        (pimBody C) [Enc.idxW n, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 e] (pinIn C (i + 1) e n)
        (by decide) rfl (by decide) hc
        ⟨by simp +decide [Env.get, pmParams, ctxEnv], by simp +decide [sev, Env.get, pmParams, ctxEnv]; exact word_add1_eq i,
          by simp +decide [Env.get, pmParams, ctxEnv], trivial⟩
        (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pmParams _ rfl hlk) (ih (i + 1) H hp (by omega) (by omega)))
        (fun w H2 hp2 hw => ?_)
      subst hw
      exact specR_returnI _ _ (by simp +decide [Env.get]) (fun t ht => ⟨H2, hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem natOpName_run {C : Ctx} (hok : CtxOK C) {s : AState} (hp : s.pins = C.pins) (n : NIdx) :
    natOpName n s = .ok (pinIn C 14 29 n, s) := by
  have h := fun i (hi : i < pinCount) => pinAt_run hok hp i hi
  simp only [natOpName, natOpNames, natDivModNames, natPredName, natAddName, natSubName, natMulName, natPowName,
    natBeqName, natBleName, natDivName, natModName, natGcdName, natLandName, natLorName, natXorName,
    natShiftLeftName, natShiftRightName, pinNatPred, pinNatAdd, pinNatSub, pinNatMul, pinNatPow, pinNatBeq,
    pinNatBle, pinNatDiv, pinNatMod, pinNatGcd, pinNatLand, pinNatLor, pinNatXor, pinNatShiftLeft,
    pinNatShiftRight, PIN_NAT_PRED, PIN_NAT_ADD, PIN_NAT_SUB, PIN_NAT_MUL, PIN_NAT_POW, PIN_NAT_BEQ, PIN_NAT_BLE,
    PIN_NAT_DIV, PIN_NAT_MOD, PIN_NAT_GCD, PIN_NAT_LAND, PIN_NAT_LOR, PIN_NAT_XOR, PIN_NAT_SHIFT_LEFT,
    PIN_NAT_SHIFT_RIGHT]
  simp [bind, StateT.bind, Except.bind, h _ (show 14 < pinCount by decide), h _ (show 15 < pinCount by decide),
    h _ (show 16 < pinCount by decide), h _ (show 17 < pinCount by decide), h _ (show 18 < pinCount by decide),
    h _ (show 19 < pinCount by decide), h _ (show 20 < pinCount by decide), h _ (show 21 < pinCount by decide),
    h _ (show 22 < pinCount by decide), h _ (show 23 < pinCount by decide), h _ (show 24 < pinCount by decide),
    h _ (show 25 < pinCount by decide), h _ (show 26 < pinCount by decide), h _ (show 27 < pinCount by decide),
    h _ (show 28 < pinCount by decide), pure, StateT.pure, Except.pure]
  split_ifs with h1
  · show Except.ok (true, s) = Except.ok (_, s)
    simp only [pinIn, List.range', List.any_cons, List.any_nil, Bool.or_false]
    congr 2; symm
    simp only [Bool.or_eq_true, beq_iff_eq]
    tauto
  · simp [StateT.bind, StateT.pure, Except.bind, Except.pure, bind, pure, Functor.map, Except.map, h _ (show 21 < pinCount by decide), h _ (show 22 < pinCount by decide), h _ (show 23 < pinCount by decide), h _ (show 24 < pinCount by decide), h _ (show 25 < pinCount by decide), h _ (show 26 < pinCount by decide), h _ (show 27 < pinCount by decide), h _ (show 28 < pinCount by decide)]
    simp only [pinIn, List.range', List.any_cons, List.any_nil, Bool.or_false, Nat.reduceAdd]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq]
    tauto

end

end ConPanqueque.T.Decl
