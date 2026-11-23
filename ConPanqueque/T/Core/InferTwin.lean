import ConPanqueque.T.Core.FabScope
open ConRon.Arena

/-!
# `inferBody`'s twin, its inline arms named

The sort, constant, literal and `let` clauses of `inferBody` as functions, so the port's dispatcher can call each
arm as a callee; `inferBody_eq` restates the body as one `view` and a dispatch.
-/

namespace ConPanqueque.T.WC

def ibSortT (u : LIdx) : AM EIdx := do
  let su ← internLNode (.succ u)
  internE (.sort su)

def ibConstT (fe : IFEnv) (n : NIdx) (us : LsIdx) : AM EIdx := do
  match fe.find? n with
  | none => do
    let err ← unknownConstError n
    fail err
  | some ci => do
    let cv := ci.toConstantVal
    let usl ← viewLs us
    if usl.length != cv.levelParams.length then do
      fail (.invalid "incorrect number of universe levels")
    else constTyAt cv us

def ibLitT (fe : IFEnv) : ConLeche.Literal → AM EIdx
  | .natVal n => do
    if fe.natLit then do
      if ← natSizeRefused n then
        fail (.invalid "the kernel refused a `Nat` numeral because its size exceeds the maximum; raise it with --max-nat-size")
      else do
        let nn ← pinNat
        constE nn
    else fail (.invalid "Nat literal without the Nat basis declarations")
  | .strVal _ => do
    if fe.strLit then do
      let sn ← pinString
      constE sn
    else fail (.notImplemented
      "string literals before the String support declarations")

def ibLetT (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (ty v b : EIdx) : AM EIdx := do
  let tty ← r.infer depth ty
  let _ ← ensureSort r fe depth tty
  let tv ← r.infer depth v
  if !(← r.defeq depth tv ty) then
    fail (.invalid "let value type mismatch")
  else do
    let ob ← instantiate1Fast coreWalkFuel b v 0
    r.infer depth ob

theorem inferBody_eq (r : CoreFnsA) (fe : IFEnv) (depth : Nat) (e : EIdx) :
    ConRon.Arena.inferBody r fe depth e = (view e >>= fun v => match v with
      | .sort u => ibSortT u
      | .fvar idx ty => if idx < depth then pure ty else fail (.invalid "free variable out of scope")
      | .const n us => ibConstT fe n us
      | .lit l => ibLitT fe l
      | .forallE ty body => inferForall r fe depth ty body
      | .lam ty body => inferLam r depth ty body
      | .app _ _ => inferApp r fe depth e
      | .proj sn i pe => inferProj r fe depth sn i pe
      | .letE ty v b => ibLetT r fe depth ty v b
      | .bvar _ => fail (.notImplemented "inferType beyond the supported fragment")) := by
  unfold ConRon.Arena.inferBody
  congr 1
  funext v
  cases v with
  | lit l => cases l <;> rfl
  | _ => rfl

end ConPanqueque.T.WC
