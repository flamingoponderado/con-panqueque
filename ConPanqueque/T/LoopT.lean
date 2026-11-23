import ConPanqueque.T.Loop
import ConPanqueque.T.CallN

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

/-- A call as a `Step`: the twin's run and the callee's post are kept in the post. -/
theorem step_callNIH {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {m : AM α}
    (x f : MlS) (ps : List MlS) (es : List (ExpHOL 64)) (B : ProgHOL 64) (vs : List (BitVec 64))
    (hnd : ps.Nodup) (hl : vs.length = ps.length)
    (hx : x ∈ D) (hC : C.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), B, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs)
    (Rf : α → BitVec 64 → AState → PState σ → Prop) (Qx : α → BitVec 64 → AState → List (BitVec 64) → Prop)
    (hRf : ∀ a w s' st, Rf a w s' st → ∃ H', C.H <+: H' ∧ Qx a w s' H' ∧ SR (ctxH C H') s' st)
    (hB : ∀ u : PState σ, SR C s u → (∀ a v, (a, v) ∈ M → u.memaddrs a ∧ u.memory a = .word v) →
      (∀ i (hi : i < ps.length), u.locals.lookup ps[i] = some (.val (.word (vs[i]'(by omega))))) →
      SpecR (· = u) B s m Rf) :
    Step (σ := σ) (Inv C s Γ M D) (.call (some (some (.local, x), none)) f es)
      (fun t' => ∃ a w s' H', m s = .ok (a, s') ∧ C.H <+: H' ∧ Qx a w s' H' ∧
        Inv (ctxH C H') s' ((x, w) :: Γ) [] D t') := by
  intro t ht
  obtain ⟨cal, hlk, hcal⟩ := lookupCodeN t f ps B vs hnd hl (by rw [ht.sr.code]; exact hC)
  have hc := spec_callN (P := (· = t)) (s := s) (m := m)
    (Q := fun a s' t' => ∃ w H', C.H <+: H' ∧ Qx a w s' H' ∧ Inv (ctxH C H') s' ((x, w) :: Γ) [] D t')
    x f es B (fun _ => vs.map fun v => .val (.word v)) (fun _ => cal)
    (fun u hu => by subst hu; exact evalList_words u es vs (evAll_imp (fun e v h => inv_ev ht h) es vs hes))
    (fun u hu => by subst hu; exact hlk) (fun u hu => by rw [hu]; exact ht.decl x hx) (fun _ => Rf)
    (fun u hu => by
      subst hu
      exact hB _ (sr_of_eq ht.sr rfl rfl rfl rfl) (fun a v ha => ht.mem a v ha) hcal)
    (fun u hu a w s' st hr => by
      subst hu
      obtain ⟨H', hp, hq, hs⟩ := hRf a w s' st hr
      refine ⟨w, H', hp, hq, ⟨sr_of_eq hs rfl rfl rfl rfl, fun y v hy => ?_, fun _ _ h => absurd h (by simp),
        fun y hy => ?_⟩⟩
      · simp only [setKvarHOLFinite, Env.get] at hy ⊢
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact lookup_setVar_same _ _ _
        · rename_i e; rw [lookup_setVar_other _ _ e]; exact ht.env y v hy
      · simp only [setKvarHOLFinite]
        by_cases e : y = x
        · subst e; exact ⟨w, lookup_setVar_same _ _ _⟩
        · rw [lookup_setVar_other _ _ e]; exact ht.decl y hy)
  rcases hc t rfl with hs | ⟨hn, a, s', hm, w, H', hp, hq, hi⟩
  · exact Or.inl hs
  · exact Or.inr ⟨hn, a, w, s', H', hm, hp, hq, hi⟩

end

end ConPanqueque.T
