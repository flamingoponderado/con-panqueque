import ConPanqueque.T.Heap
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# The store floor

`ctxSt C St` raises the context's store floor to `St`. A caller raises it to the current store before a
callee runs; the callee's post, read at the raised context, then says the store only grew since the call.
-/

namespace ConPanqueque.T

def ctxSt (C : Ctx) (St : EStore) : Ctx := { C with St := St }

theorem ctxOK_St {C : Ctx} (hok : CtxOK C) (St : EStore) : CtxOK (ctxSt C St) := by
  cases hok; constructor <;> assumption

section
variable {σ : Type}

theorem sr_raise {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t) : SR (ctxSt C s.store) s t :=
  ⟨h.rep, h.gdir, h.gfln, h.gfll, h.gfls, h.gfle, h.gkb, h.code, h.kbuf, h.memo, h.memoN, h.cache, h.mode, h.env, h.pins,
    h.heap, h.twf, h.envd, Ext.refl _, h.cok⟩

theorem sr_lower {C : Ctx} {St : EStore} {s : AState} {t : PState σ} (h : SR (ctxSt C St) s t)
    (hx : Ext C.St St) : SR C s t :=
  ⟨h.rep, h.gdir, h.gfln, h.gfll, h.gfls, h.gfle, h.gkb, h.code, h.kbuf, h.memo, h.memoN, h.cache, h.mode, h.env, h.pins,
    h.heap, h.twf, h.envd, Ext.trans hx h.floor, h.cok⟩

/-- Raise the floor to the current store for the rest of a body; the post is lowered back at the end. -/
theorem specR_invRaise {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {c : ProgHOL 64}
    {m : AM α} {R R' : α → BitVec 64 → AState → PState σ → Prop}
    (h : SpecR (Inv (ctxSt C s.store) s Γ M D) c s m R')
    (hR : ∀ a w s' t, Ext C.St s.store → R' a w s' t → R a w s' t) : SpecR (Inv C s Γ M D) c s m R := by
  intro t ht
  rcases h t ⟨sr_raise ht.sr, ht.env, ht.mem, ht.decl⟩ with hs | ⟨w, hn, a, s', hm, hr⟩
  · exact Or.inl hs
  · exact Or.inr ⟨w, hn, a, s', hm, hR _ _ _ _ ht.sr.floor hr⟩

/-- The same at a callee's entry. -/
theorem specR_preRaise {α : Type} {C : Ctx} {s : AState} {Γ : Env} {c : ProgHOL 64}
    {m : AM α} {R R' : α → BitVec 64 → AState → PState σ → Prop}
    (h : SpecR (Pre (ctxSt C s.store) s Γ) c s m R')
    (hR : ∀ a w s' t, Ext C.St s.store → R' a w s' t → R a w s' t) : SpecR (Pre C s Γ) c s m R := by
  intro t ht
  rcases h t ⟨sr_raise ht.1, ht.2⟩ with hs | ⟨w, hn, a, s', hm, hr⟩
  · exact Or.inl hs
  · exact Or.inr ⟨w, hn, a, s', hm, hR _ _ _ _ ht.1.floor hr⟩

end

end ConPanqueque.T
