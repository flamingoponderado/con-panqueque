import ConPanqueque.T.Decl.EnvGrow
open ConRon.Arena ConRon.Bridge

/-!
# The fold's environment, pushed

con-ron's push family: `IFEnv.find?_push` (a push answers at its own name and nowhere else), `TblGate` (no raw
table without its structure, kept by a push) and `FlagsOK` (the literal flags are the lookups', kept by a push).
With the gate, a push of a fresh name opens no table.
-/

namespace ConPanqueque.T.Decl

theorem push_findTable {fe : IFEnv} (hg : TblGate fe) (ci : IConstantInfo) (hnew : fe.find? ci.name = none)
    (n : NIdx) : (fe.push ci).findTable? n = fe.findTable? n := by
  unfold IFEnv.findTable?
  rw [IFEnv.find?_push, IFEnv.rawTable?_push]
  by_cases e : (ci.name == n) = true
  · have en : ci.name = n := by simpa using e
    subst en
    have hr : fe.rawTable? ci.name = none := by
      cases h : fe.rawTable? ci.name with
      | none => rfl
      | some t => have := hg ci.name t h; rw [hnew] at this; simp at this
    simp [hnew, hr]
  · have ef : (ci.name == n) = false := by simpa using e
    simp only [ef, Bool.false_eq_true, ite_false]

end ConPanqueque.T.Decl
