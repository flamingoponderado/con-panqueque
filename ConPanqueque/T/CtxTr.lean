import Lean
open Lean Meta Elab Tactic

/-!
# `ctx_tr h`: transport a code bundle to a context with the same code table

A bundle `X C` (a `Prop` structure of code-lookup facts, possibly nesting other bundles) holds at any `C'` that
differs from `C` only in fields the bodies do not read (heap image, store floor, saved memos). `ctx_tr h`
closes `X C'` from `h : X C`: by `h` itself when the two are definitionally equal, else field by field.
-/

namespace ConPanqueque.CtxTr

partial def tr (h : Expr) (goal : Expr) : MetaM Expr := do
  let ht ← inferType h
  if ← withDefault (isDefEq ht goal) then return h
  let env ← getEnv
  let goal ← whnfR goal
  let some n := goal.getAppFn.constName? | throwError "ctx_tr: goal is not a structure: {goal}"
  unless isStructure env n do throwError "ctx_tr: cannot transport {ht} to {goal}"
  let ctor := getStructureCtor env n
  let us := goal.getAppFn.constLevels!
  let params := goal.getAppArgs
  let mut val := mkAppN (.const ctor.name us) params
  for f in getStructureFields env n do
    let ty ← whnf (← inferType val)
    let .forallE _ bt _ _ := ty | throwError "ctx_tr: unexpected constructor type"
    let p ← mkProjection h f
    let v ← tr p bt
    val := mkApp val v
  return val

elab "ctx_tr " h:term : tactic => withMainContext do
  let goal ← getMainTarget
  let h ← elabTerm h none
  let v ← tr h goal
  closeMainGoal `ctx_tr v

end ConPanqueque.CtxTr
