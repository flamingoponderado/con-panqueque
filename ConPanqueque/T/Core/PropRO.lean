import ConPanqueque.T.Core.IotaTwin
import ConPanqueque.T.Core.PropTele
open ConRon.Arena

/-!
# Read-only twin steps of PropRead

`RO m`: a run of `m` leaves the state as it was. The views, the level readback (uncached), the spine walks and
PropRead's telescope readers are read-only.
-/

namespace ConPanqueque.T.WC

theorem RO.viewBVar (h : EIdx) : RO (ConRon.Arena.viewBVar h) := RO.bind RO.get (fun _ => RO.pure _)
theorem RO.viewConstName (h : EIdx) : RO (ConRon.Arena.viewConstName h) := RO.bind RO.get (fun _ => RO.pure _)
theorem RO.viewSort (h : EIdx) : RO (ConRon.Arena.viewSort h) := RO.bind RO.get (fun _ => RO.pure _)
theorem RO.viewLsLen (h : LsIdx) : RO (ConRon.Arena.viewLsLen h) := RO.bind RO.get (fun _ => RO.pure _)

theorem RO.readLevel (u : LIdx) : RO (ConRon.Arena.readLevel u) := by
  refine RO.bind RO.get (fun s => ?_)
  split
  · exact RO.pure _
  · exact RO.fail _

theorem RO.getAppFn (fuel : Nat) (h : EIdx) : RO (ConRon.Arena.getAppFn fuel h) :=
  fun s r s' e => getAppFn_ro fuel h s r s' e

theorem RO.getAppArgs : ∀ (fuel : Nat) (h : EIdx), RO (ConRon.Arena.getAppArgs fuel h)
  | 0, h => by rw [ConRon.Arena.getAppArgs]; exact RO.fail _
  | n + 1, h => by
    rw [ConRon.Arena.getAppArgs]
    split
    · refine RO.bind (RO.viewApp h) (fun o => ?_)
      rcases o with _ | ⟨f, a⟩
      · exact RO.failDanglingE
      · exact RO.bind (RO.getAppArgs n f) (fun _ => RO.pure _)
    · exact RO.pure _

theorem RO.lamProj : ∀ (fuel k : Nat) (h : EIdx), RO (ConRon.Arena.lamProj? fuel k h)
  | 0, k, h => by rw [ConRon.Arena.lamProj?]; exact RO.fail _
  | n + 1, k, h => by
    rw [ConRon.Arena.lamProj?]
    split
    · refine RO.bind (RO.viewBind h) (fun o => ?_)
      rcases o with _ | ⟨_, b⟩
      · exact RO.failDanglingE
      · exact RO.lamProj n (k + 1) b
    · split
      · refine RO.bind (RO.viewBVar h) (fun o => ?_)
        rcases o with _ | j
        · exact RO.failDanglingE
        · exact RO.pure _
      · exact RO.pure _

theorem RO.unwrapIdDefs (fe : IFEnv) (fuel : Nat) : ∀ (n : Nat) (e : EIdx), RO (ConRon.Arena.unwrapIdDefs fe fuel n e)
  | 0, e => by rw [ConRon.Arena.unwrapIdDefs]; exact RO.pure _
  | n + 1, e => by
    rw [ConRon.Arena.unwrapIdDefs]
    refine RO.bind (RO.getAppFn fuel e) (fun hh => ?_)
    split
    · refine RO.bind (RO.viewConstName hh) (fun o => ?_)
      rcases o with _ | c
      · exact RO.failDanglingE
      · dsimp only
        split
        · refine RO.bind (RO.lamProj fuel 0 _) (fun o => ?_)
          rcases o with _ | ⟨k, j⟩
          · exact RO.pure _
          · refine RO.bind (RO.getAppArgs fuel e) (fun args => ?_)
            split
            · exact RO.unwrapIdDefs fe fuel n _
            · exact RO.pure _
        · exact RO.pure _
    · exact RO.pure _

theorem RO.peelPisW (fe : IFEnv) (fuel : Nat) : ∀ (k : Nat) (e : EIdx), RO (ConRon.Arena.peelPisW fe fuel k e)
  | 0, e => by rw [ConRon.Arena.peelPisW]; exact RO.bind (RO.unwrapIdDefs fe fuel 4 e) (fun _ => RO.pure _)
  | k + 1, e => by
    rw [ConRon.Arena.peelPisW]
    split
    · refine RO.bind (RO.viewBind e) (fun o => ?_)
      rcases o with _ | ⟨_, b⟩
      · exact RO.failDanglingE
      · exact RO.peelPisW fe fuel k b
    · refine RO.bind (RO.unwrapIdDefs fe fuel 4 e) (fun u => ?_)
      split
      · refine RO.bind (RO.viewBind u) (fun o => ?_)
        rcases o with _ | ⟨_, b⟩
        · exact RO.failDanglingE
        · exact RO.peelPisW fe fuel k b
      · exact RO.pure _

theorem RO.binderDom : ∀ (k : Nat) (h : EIdx), RO (ConRon.Arena.binderDom k h)
  | 0, h => by
    rw [ConRon.Arena.binderDom]
    split
    · refine RO.bind (RO.viewBind h) (fun o => ?_)
      rcases o with _ | ⟨A, _⟩
      · exact RO.failDanglingE
      · exact RO.pure _
    · exact RO.pure _
  | k + 1, h => by
    rw [ConRon.Arena.binderDom]
    split
    · refine RO.bind (RO.viewBind h) (fun o => ?_)
      rcases o with _ | ⟨_, b⟩
      · exact RO.failDanglingE
      · exact RO.binderDom k b
    · exact RO.pure _

theorem RO.residualPW : ∀ (r : Option EIdx), RO (ConRon.Arena.residualPW r)
  | none => by rw [ConRon.Arena.residualPW]; exact RO.pure _
  | some h => by
    rw [ConRon.Arena.residualPW]
    split
    · refine RO.bind (RO.viewSort h) (fun o => ?_)
      rcases o with _ | u
      · exact RO.failDanglingE
      · exact RO.bind (RO.readLevel u) (fun _ => RO.pure _)
    · exact RO.pure _

end ConPanqueque.T.WC
