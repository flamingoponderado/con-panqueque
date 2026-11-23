import ConPanqueque.T.Comp.KnotC
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# The knot's entries at the checker's fuel

The declaration checker calls the knot at `checkFuel` (`2^62`), the fuel `inferTypeCore`, `isDefEqCore` and
`ensureSortCore` use, from the non-eager side. These are `knot_closed` at that fuel.
-/

namespace ConPanqueque.T.Comp

open ConPanqueque.T ConPanqueque.T.Knot

section
variable {σ : Type}

theorem checkFuel_le : checkFuel ≤ 2 ^ 62 := by unfold checkFuel; omega

/-- `inferTypeCore`, as the `infer` entry at the checker's fuel. -/
theorem inferTypeCore_eq (mode : ConLeche.CheckMode) {C : Ctx} (hs : C.side = false) (d : Nat) (e : EIdx) :
    inferTypeCore mode C.fe checkFuel d e = (knot mode C checkFuel).infer d e := by
  unfold knot; rw [hs]; rfl

/-- `isDefEqCore`, as the `defeq` entry at the checker's fuel. -/
theorem isDefEqCore_eq (mode : ConLeche.CheckMode) {C : Ctx} (hs : C.side = false) (d : Nat) (a b : EIdx) :
    isDefEqCore mode C.fe checkFuel d a b = (knot mode C checkFuel).defeq d a b := by
  unfold knot; rw [hs]; rfl

/-- **The type of an expression, by the port**: the `infer` entry refines `inferTypeCore`. -/
theorem inferTop (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) {C : Ctx}
    (hok : CtxOK C) (hc : KCodes C kBodies) (hac : AllCodes mode C) (hs : C.side = false) (s : AState)
    (d : Nat) (hd : d < 2 ^ 63) (e : EIdx) :
    Callee (σ := σ) C kParams [BitVec.ofNat 64 checkFuel, BitVec.ofNat 64 d, Enc.idxW e] (inferE C fIB) s
      (inferTypeCore mode C.fe checkFuel d e) (PostK C) := by
  rw [inferTypeCore_eq mode hs]
  exact (knot_closed (σ := σ) ra mode checkFuel checkFuel_le C hok hc s hac).2.2.1 d e hd

/-- **Definitional equality, by the port**: the `defeq` entry refines `isDefEqCore`. -/
theorem defeqTop (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) {C : Ctx}
    (hok : CtxOK C) (hc : KCodes C kBodies) (hac : AllCodes mode C) (hs : C.side = false) (s : AState)
    (d : Nat) (hd : d < 2 ^ 63) (a b : EIdx) :
    Callee (σ := σ) C dParams [BitVec.ofNat 64 checkFuel, BitVec.ofNat 64 d, Enc.idxW a, Enc.idxW b] (dE C) s
      (isDefEqCore mode C.fe checkFuel d a b) (PostB C) := by
  rw [isDefEqCore_eq mode hs]
  exact (knot_closed (σ := σ) ra mode checkFuel checkFuel_le C hok hc s hac).2.2.2.1 d a b hd

end

end ConPanqueque.T.Comp
