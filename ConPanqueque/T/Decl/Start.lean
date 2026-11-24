import ConPanqueque.T.Decl.Fold
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-! # The driver's start

`checkDeclsPure` opens with `mkIFEnvLits IEnv.empty`: an index with no constants, no
tables, and the ten pinned literal names.  This file names that index, proves the fold's
three environment invariants hold of it, and composes the start with `fold_spec`. -/

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC
open ConPanqueque.V.Enc

/-- The index `mkIFEnvLits IEnv.empty` builds off pin table `p`. -/
def feStart (p : Pins) : IFEnv :=
  IFEnv.ofParts IEnv.empty ∅ { lits := strPins.map (fun i => p.names[i]!) } ∅

theorem mkIFEnvLits_run {C : Ctx} (hok : CtxOK C) {s : AState} (hp : s.pins = C.pins) :
    mkIFEnvLits IEnv.empty s = .ok (feStart C.pins, s) := by
  simp only [mkIFEnvLits, strLitNames, natLitNames, pinNat, pinNatZero, pinNatSucc, pinString,
    pinStringOfList, pinList, pinListNil, pinListCons, pinChar, pinCharOfNat, bind, StateT.bind,
    Except.bind, pinAt_run hok hp PIN_NAT (by decide), pinAt_run hok hp PIN_NAT_ZERO (by decide),
    pinAt_run hok hp PIN_NAT_SUCC (by decide)]
  simp [feStart, strPins, pure, StateT.pure, Except.pure, IEnv.empty, mkIFEnvGo, mkIFEnvTblsGo,
    pinAt_run hok hp PIN_STRING (by decide), pinAt_run hok hp PIN_STRING_OF_LIST (by decide),
    pinAt_run hok hp PIN_LIST (by decide), pinAt_run hok hp PIN_LIST_NIL (by decide),
    pinAt_run hok hp PIN_LIST_CONS (by decide), pinAt_run hok hp PIN_CHAR (by decide),
    pinAt_run hok hp PIN_CHAR_OF_NAT (by decide)]

theorem tblGate_start (p : Pins) : TblGate (feStart p) := by
  intro n t ht
  simp [feStart, IFEnv.ofParts, IFEnv.rawTable?, IFBase.findTable?] at ht

theorem flagsOK_start (p : Pins) : FlagsOK (feStart p) := FlagsOK.ofParts _ _ _ _

theorem litsPinned_start (p : Pins) : LitsPinned (feStart p) p := by
  simp [LitsPinned, feStart, IFEnv.ofParts]

variable {σ : Type}

/-- **The driver over a record block**: started in a context whose index is the start index,
the fold body refines `checkDeclsPure` on the block's records. -/
theorem checkDeclsPure_spec (mode : ConLeche.CheckMode) (pins : List INatOpPinSet)
    (ra : ConPanqueque.Hash.RuntimeAssumptions) (rs : List (Nat × IDeclaration)) (ob : Nat)
    (hlenR : rs.length < 2 ^ 62) (C : Ctx) (s : AState) (hok : CtxOK C) (hc : FoldCodes mode C)
    (hs : C.side = false) (hpl : C.saved = none) (hfe : C.fe = feStart C.pins)
    (hp : s.pins = C.pins) (hb : BlkAt C.H ob (rs.map (fun r => cellA C r.1)))
    (hrec : ∀ j (hj : j < rs.length), RecOK C rs[j].1 rs[j].2) :
    SpecR (σ := σ) (Pre C s (foParams.zip [cellA C ob, BitVec.ofNat 64 0, BitVec.ofNat 64 rs.length]))
      foldBody s (checkDeclsPure mode pins (rs.map Prod.snd)) PostFold := by
  have e : checkDeclsPure mode pins (rs.map Prod.snd) s =
      checkDeclsPureGo mode pins C.fe ((rs.drop 0).map Prod.snd) s := by
    simp only [checkDeclsPure, bind, StateT.bind, mkIFEnvLits_run hok hp, Except.bind, hfe,
      List.drop_zero]
  refine specR_congr e ?_
  exact fold_spec mode pins ra rs ob hlenR rs.length 0 C s hok hc hs hpl
    (hfe ▸ tblGate_start _) (hfe ▸ flagsOK_start _) (by rw [hfe]; exact litsPinned_start _) hb
    (fun j hj _ => hrec j hj) (by simp) (by simp)

end ConPanqueque.T.Decl
