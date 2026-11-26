import Lean
open Lean Meta Elab Tactic

/-! # `kernel_rfl`: close `a = b` with `Eq.refl a`, the definitional check left to the kernel

The code-table lookups reduce a long association list; the elaborator's `isDefEq` on them is slow, the
kernel's check fast. -/

namespace ConPanqueque.Code

elab "kernel_rfl" : tactic => do
  let g ← getMainGoal
  let t ← whnfR (← instantiateMVars (← g.getType))
  let some (_, a, _) := t.eq? | throwError "kernel_rfl: not an equation"
  g.assign (← mkEqRefl a)
  replaceMainGoal []

end ConPanqueque.Code
