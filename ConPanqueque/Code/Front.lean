import ConPanqueque.Code.Map

open Lean Meta Elab Tactic in
/-- Unfold the goal's head definition once. -/
elab "unfold_head" : tactic => liftMetaTactic fun g => do
  let t ← whnfR (← g.getType)
  match ← unfoldDefinition? t with
  | some t' => return [← g.replaceTargetDefEq t']
  | none => throwError "unfold_head: nothing to unfold"

namespace ConPanqueque.Code

open Flapjack Flapjack.Pancake.PanLang

set_option hygiene false in
/-- `code_auto`, also unfolding plain definitions. -/
macro "code_auto'" : tactic => `(tactic| repeat' (first
  | (rw [hC, codeMap_lookup]; rfl)
  | (rename_i ht; rw [ht, hC, codeMap_lookup]; rfl)
  | (intro (o : ConPanqueque.T.Big.BitOp); cases o)
  | (intro (b : Bool); cases b)
  | (intro (k : Nat) hk; rcases k with _ | _ | _ | _ | _ | _ | k <;> (try omega))
  | (intro _)
  | (constructor)
  | unfold_head))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem front_ok (σ : Type) (C : ConPanqueque.T.Ctx) (hC : C.code = codeMap (codeEntries C)) :
    ConPanqueque.Front.FrontCodes σ C := by
  have hscan : ∀ t : ConPanqueque.T.PState σ, t.code = C.code → ConPanqueque.Scan.ScanCodes t := by code_auto'
  have hrec : ∀ t : ConPanqueque.T.PState σ, t.code = C.code → ConPanqueque.Scan.RecTable t := by code_auto'
  refine ⟨?_, ?_, ?_, fun t ht => ConPanqueque.Scan.lineCodes_of t (hscan t ht) (hrec t ht), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals code_auto'

set_option maxRecDepth 100000 in
theorem feed_ok (C : ConPanqueque.T.Ctx) (hC : C.code = codeMap (codeEntries C)) :
    C.code.lookup ConPanqueque.Front.fFeed = some (ConPanqueque.Front.feedPs.map (fun p => (p, ShapeHOL.one)),
      ConPanqueque.T.prologue ConPanqueque.Front.feedL ConPanqueque.Front.feedCore, .one) := by
  rw [hC, codeMap_lookup]; rfl

end ConPanqueque.Code
