import ConPanqueque.T.Decl.Flags

/-!
# The context's environment exchanged for one answering alike

`sr_fe` / `specR_feI`: an environment with the same lookups, tables and literal word, its constants denoting,
stands for the context's in `SR` and the invariant (the twin's temporary pushes popped).
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Decl

open ConPanqueque.T

section
variable {σ : Type}

theorem sr_fe {C : Ctx} {s : AState} {t : PState σ} (h : SR C s t) {fe : IFEnv} (hlit : litW fe = litW C.fe)
    (hden : EnvDen fe C.pins s.store) : SR (ctxFe C fe) s t := by
  obtain ⟨hH, hm1, hm2, hl⟩ := h.env
  exact ⟨h.rep, h.gdir, h.gfln, h.gfll, h.gfls, h.gfle, h.gkb, h.code, h.kbuf, h.memo, h.memoN, h.cache, h.mode,
    ⟨hH, hm1, hm2, by rw [show (ctxFe C fe).fe = fe from rfl, hlit]; exact hl⟩, h.pins, h.heap, h.twf, hden, h.floor,
    h.cok⟩

theorem specR_feI {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {c : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} {fe : IFEnv} (hlit : litW fe = litW C.fe)
    (hden : EnvDen fe C.pins s.store) (h : SpecR (Inv (ctxFe C fe) s Γ M D) c s m R) :
    SpecR (Inv C s Γ M D) c s m R := fun t ht =>
  h t ⟨sr_fe ht.sr hlit hden, ht.env, ht.mem, ht.decl⟩

end

end ConPanqueque.T.Decl
