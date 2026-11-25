import ConPanqueque.T.CallN

/-!
# A call whose callee rewrites heap cells

`specR_callNIH` asks the callee's heap to extend the caller's.  A callee that stores into heap cells it was
handed (an output array) does not; `specR_callNIG` drops that requirement: the caller continues at whatever
heap the callee's post names.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T

variable {σ : Type}

theorem specR_callNIG {α β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {k : α → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f : MlS) (ps : List MlS) (es : List (ExpHOL 64)) (B : ProgHOL 64) (vs : List (BitVec 64))
    (hnd : ps.Nodup) (hl : vs.length = ps.length)
    (hx : x ∈ D) (hC : C.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), B, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs)
    (Rf : α → BitVec 64 → AState → PState σ → Prop) (Qx : α → BitVec 64 → AState → List (BitVec 64) → Prop)
    (hRf : ∀ a w s' st, Rf a w s' st → ∃ H', Qx a w s' H' ∧ SR (ctxH C H') s' st)
    (hB : ∀ u : PState σ, SR C s u → (∀ a v, (a, v) ∈ M → u.memaddrs a ∧ u.memory a = .word v) →
      (∀ i (hi : i < ps.length), u.locals.lookup ps[i] = some (.val (.word (vs[i]'(by omega))))) →
      SpecR (· = u) B s m Rf)
    (hk : ∀ a w s' H', Qx a w s' H' → SpecR (Inv (ctxH C H') s' ((x, w) :: Γ) [] D) rest s' (k a) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f es) rest) s (m >>= k) R := by
  intro t ht
  obtain ⟨cal, hlk, hcal⟩ := lookupCodeN t f ps B vs hnd hl (by rw [ht.sr.code]; exact hC)
  have hc := spec_callN (P := (· = t)) (s := s) (m := m)
    (Q := fun a s' t' => ∃ w H', Qx a w s' H' ∧ Inv (ctxH C H') s' ((x, w) :: Γ) [] D t')
    x f es B (fun _ => vs.map fun v => .val (.word v)) (fun _ => cal)
    (fun u hu => by subst hu; exact evalList_words u es vs (evAll_imp (fun e v h => inv_ev ht h) es vs hes))
    (fun u hu => by subst hu; exact hlk) (fun u hu => by rw [hu]; exact ht.decl x hx) (fun _ => Rf)
    (fun u hu => by
      subst hu
      exact hB _ (sr_of_eq ht.sr rfl rfl rfl rfl) (fun a v ha => ht.mem a v ha) hcal)
    (fun u hu a w s' st hr => by
      subst hu
      obtain ⟨H', hq, hs⟩ := hRf a w s' st hr
      refine ⟨w, H', hq, ⟨sr_of_eq hs rfl rfl rfl rfl, fun y v hy => ?_, fun _ _ h => absurd h (by simp),
        fun y hy => ?_⟩⟩
      · simp only [setKvarHOLFinite, Env.get] at hy ⊢
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact lookup_setVar_same _ _ _
        · rename_i e; rw [lookup_setVar_other _ _ e]; exact ht.env y v hy
      · simp only [setKvarHOLFinite]
        by_cases e : y = x
        · subst e; exact ⟨w, lookup_setVar_same _ _ _⟩
        · rw [lookup_setVar_other _ _ e]; exact ht.decl y hy)
  exact specR_bind (Q1 := fun a s' t' => ∃ w H', Qx a w s' H' ∧ Inv (ctxH C H') s' ((x, w) :: Γ) [] D t')
    hc (fun a s' u ⟨w, H', hq, hu⟩ => hk a w s' H' hq u hu) t rfl

end ConPanqueque.T
