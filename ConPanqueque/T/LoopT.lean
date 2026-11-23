import ConPanqueque.T.Loop

/-!
# A loop that threads the twin

`specR_whileT`: a `while` loop whose iterations advance the twin. A loop point carries the context, the twin's
state, the locals and the twin computation still to run; every reachable point's computation, run at its state,
answers what the original does. When the test fails, `rest` refines the point's computation; otherwise the body
steps to another reachable point. Termination is the clock's (`while_stop`), so no variant is needed.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open ConPanqueque.Logic
open ConRon.Arena

namespace ConPanqueque.T

structure LoopPt (β : Type) where
  C : Ctx
  s : AState
  Γ : Env
  m : AM β

section
variable {σ : Type}

theorem specR_whileT {β : Type} {c : ExpHOL 64} {body rest : ProgHOL 64} {D : List MlS}
    {R : β → BitVec 64 → AState → PState σ → Prop} (P : LoopPt β → Prop) (p0 : LoopPt β) (hp0 : P p0)
    (hc : ∀ p, P p → p.m p.s = p0.m p0.s → ∃ w, sev p.Γ c = some w ∧
      (w = 0 → SpecR (Inv p.C p.s p.Γ [] D) rest p.s p.m R) ∧
      (w ≠ 0 → Step (σ := σ) (Inv p.C p.s p.Γ [] D) body
        (fun t' => ∃ p' : LoopPt β, P p' ∧ p'.m p'.s = p.m p.s ∧ Inv p'.C p'.s p'.Γ [] D t'))) :
    SpecR (Inv p0.C p0.s p0.Γ [] D) (.seq (.while c body) rest) p0.s p0.m R := by
  intro t ht
  have W := while_stop (σ := σ) c body
    (fun u => ∃ p : LoopPt β, P p ∧ p.m p.s = p0.m p0.s ∧ Inv p.C p.s p.Γ [] D u)
    (fun u => ∃ p : LoopPt β, p.m p.s = p0.m p0.s ∧ Inv p.C p.s p.Γ [] D u ∧ SpecR (Inv p.C p.s p.Γ [] D) rest p.s p.m R)
    (by
      intro u ⟨p, hp, hm, hu⟩
      obtain ⟨w, hw, h0, h1⟩ := hc p hp hm
      refine ⟨w, ?_, fun e => ⟨p, hm, hu, h0 e⟩, fun hn _ => ?_⟩
      · simp only [evalHOLFinite]; exact inv_ev hu hw
      · rcases h1 hn _ (inv_decClock hu) with hs | ⟨hn', p', hp', hm', hq⟩
        · exact Or.inl hs
        · exact Or.inr ⟨hn', p', hp', hm'.trans hm, hq⟩)
    t ⟨p0, hp0, rfl, ht⟩
  rcases W with hs | ⟨hn, p, hm, hu, hrest⟩
  · exact Or.inl (seq_stop t _ _ hs)
  have e : evaluateHOLFiniteState t (.while c body) = (none, (evaluateHOLFiniteState t (.while c body)).2) := by
    rw [← hn]
  rw [seq_normal rest e]
  rcases hrest _ hu with hs | ⟨w, hr, a, s', hrun, hR⟩
  · exact Or.inl hs
  · exact Or.inr ⟨w, hr, a, s', hm ▸ hrun, hR⟩

end

end ConPanqueque.T
