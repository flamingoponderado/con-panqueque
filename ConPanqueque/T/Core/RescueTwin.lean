import ConPanqueque.T.Core.EtaRescue
open ConRon.Arena ConLeche

/-!
# The stuck-major rescue, decomposed on the twin side

`majorToCtorRescue` as its dispatch over the single rule's records, and its three branches (K, structure η, `And`)
as separate twin functions (`majorToCtorRescue_eq`, by `rfl`).
-/

set_option linter.unusedVariables false

namespace ConPanqueque.T.WC

/-- The rescue's K branch (`to_cnstr_when_K`), as the twin runs it. -/
def rescueK (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (rl : IRecRule) (cvj : IConstantVal) (cnP : Nat)
    (T : NIdx) (major : EIdx) : AM EIdx := do
  -- io grade (lean4lean `toCtorWhenK`'s `inferType`)
  let tmaj ← r.whnf depth (← r.inferIO depth major)
  let hh ← getAppFn coreWalkFuel tmaj
  if hh.tag == ETag.const then
    match ← view hh with
    | .const T' ust => do
      let ustl ← viewLs ust
      if T' = T ∧ cvj.levelParams.length = ustl.length then do
        let targs ← getAppArgs coreWalkFuel tmaj
        if cnP ≤ targs.length then do
          let hd ← internE (.const rl.ctor ust)
          let fab ← mkAppN hd (targs.take cnP)
          if ← fabScopeOk depth fab major then do
            -- the official `to_cnstr_when_K` type check, both modes
            if ← r.defeq depth tmaj (← r.inferIO depth fab) then do
              -- `proofIrrel`, a certificate family (official stops
              -- at the type check): off at `.trusted`
              let irK ←
                if mode.verifiedChecks then proofIrrel r fe depth fab major
                else pure true
              if irK then pure fab else pure major
            else pure major
          else pure major
        else pure major
      else pure major
    | _ => pure major
  else pure major

/-- The rescue's structure-η branch, at the table `etaRescueTable?` found. -/
def rescueEta (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (rl : IRecRule) (cvj : IConstantVal) (cnP : Nat)
    (T : NIdx) (major : EIdx) (cvT : IConstantVal) (caps : IIndCaps) (tbl : IProjTable) : AM EIdx := do
  let tmaj ← r.whnf depth (← r.inferIO depth major)
  let hh ← getAppFn coreWalkFuel tmaj
  if hh.tag == ETag.const then
    match ← view hh with
    | .const T' ust => do
      let ustl ← viewLs ust
      let targs ← getAppArgs coreWalkFuel tmaj
      if T' = T ∧ targs.length = tbl.numParams ∧
          ustl.length = cvT.levelParams.length then do
        -- the *instantiated* non-Prop test at the use, the stored
        -- fact first (`familyNeverZeroAt`); the constructor and
        -- the counts are the table's
        if ← familyNeverZeroAt r cvT caps ust then do
          let fabArgs ← etaFabArgsE T targs major tbl.numFields
          let hd ← internE (.const tbl.ctor ust)
          let fab ← mkAppN hd fabArgs
          -- no certificate on the fabricated spine (task #342 L11b)
          if ← fabScopeOk depth fab major then pure fab
          else pure major
        else pure major
      else pure major
    | _ => pure major
  else pure major

/-- The rescue's `And` branch (no η table). -/
def rescueAnd (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (rl : IRecRule) (cvj : IConstantVal) (cnP : Nat)
    (T : NIdx) (major : EIdx) : AM EIdx := do
  let an ← pinAnd
  if T = an then do
    -- THE `And`-ONLY η RESCUE (user ruling: `And` and nothing else)
    let tmaj ← r.whnf depth (← r.inferIO depth major)
    let hh ← getAppFn coreWalkFuel tmaj
    if hh.tag == ETag.const then
      match ← view hh with
      | .const T' ust => do
        match ← viewLsLen ust with
        | none => failDanglingLs
        | some ustl =>
        let targs ← getAppArgs coreWalkFuel tmaj
        let ars ← andRescueSlots fe rl.ctor cnP
        if T' = T ∧ targs.length = cnP ∧
            cvj.levelParams.length = ustl ∧ ars = true then do
          let p0 ← internE (.proj T 0 major)
          let p1 ← internE (.proj T 1 major)
          let fabArgs := targs ++ [p0, p1]
          let hd ← internE (.const rl.ctor ust)
          let fab ← mkAppN hd fabArgs
          if ← fabScopeOk depth fab major then do
            if ← r.defeq depth tmaj (← r.inferIO depth fab) then do
              let irA ←
                if mode.verifiedChecks then proofIrrel r fe depth fab major
                else pure true
              if irA then pure fab else pure major
            else pure major
          else pure major
        else pure major
      | _ => pure major
    else pure major
  else pure major

theorem majorToCtorRescue_eq (mode : CheckMode) (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (c : NIdx) (isK : Bool)
    (rules : List IRecRule) (major : EIdx) :
    majorToCtorRescue mode r fe depth c isK rules major =
      match rules with
      | [rl] =>
        match fe.find? rl.ctor with
        | some (.ctorInfo cvj cnP _cnF T) =>
          match fe.find? T with
          | some (.indInfo cvT caps) =>
            if isK = true then rescueK mode r fe depth rl cvj cnP T major
            else etaRescueTable? (fe.findTable? T) rl.ctor cvj cvT caps >>= fun o => match o with
              | some tbl => rescueEta mode r fe depth rl cvj cnP T major cvT caps tbl
              | none => rescueAnd mode r fe depth rl cvj cnP T major
          | _ => pure major
        | _ => pure major
      | _ => pure major := by
  rfl

end ConPanqueque.T.WC
