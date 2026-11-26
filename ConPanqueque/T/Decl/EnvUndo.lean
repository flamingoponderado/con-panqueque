import ConPanqueque.T.Ind.IdxIns
import ConPanqueque.T.MemoUndo

/-!
# Undoing the newest constant-table insert

`undoCode (C.mg .env) eN rest`: the constant table's newest row must be the name `eN` (else hang); it is
removed.  The context continues with the table `C.envM.erase n` and any environment `fe` the caller names
(with the same literal word and denotation facts) — the temporary pushes of an inductive block's recursors,
undone newest first, land back on an environment answering as before them.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC

section
variable {σ : Type}

/-- The continuation after an undo, in its new context: `cj0` dropped from the environment. -/
theorem inv_after_undo {C C' : Ctx} {s s' : AState} {Γ : Env} {M : Mem} {D : List MlS} {t u : PState σ}
    (ht : Inv C s Γ M D t) (hsr : SR C' s' u) (hl : ∀ y, y ≠ lJ0 → u.locals.lookup y = t.locals.lookup y)
    (hj : ∃ w, u.locals.lookup lJ0 = some (.val (.word w))) : Inv C' s' (Γ.kill [lJ0]) [] D u := by
  refine ⟨hsr, fun y w hy => ?_, fun _ _ h => absurd h (by simp), fun y hy => ?_⟩
  · obtain ⟨hk1, hy'⟩ := Env.get_kill Γ _ y w hy
    have hne : y ≠ lJ0 := by simpa using hk1
    rw [hl y hne]; exact ht.env y w hy'
  · by_cases e : y = lJ0
    · subst e; exact hj
    · rw [hl y e]; exact ht.decl y hy

/-- **The constant table's newest insert undone**: the program continues in the context with table
`C.envM.erase n` and the environment `fe`. -/
theorem specR_envUndoI {α : Type} {C : Ctx} (hok : CtxOK C) (n : NIdx) (fe : IFEnv)
    (hlit : litW fe = litW C.fe) {s : AState} (hden : EnvDen fe C.pins s.store)
    {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (eN : ExpHOL 64) (heN : sev Γ eN = some (Enc.idxW n)) (hj : lJ0 ∈ D)
    (hk : SpecR (Inv (ctxIns C fe C.EH (C.envM.erase n)) s (Γ.kill [lJ0]) [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (undoCode (C.mg .env) eN rest) s m R := by
  intro t ht
  obtain ⟨w0, hw0⟩ := ht.decl lJ0 hj
  rcases undoCode_core (K := NIdx) (V := BitVec 64) encNI_inj t (C.mG .env) (C.mg .env) C.envM ht.sr.env.2.1 n
      (Enc.idxW n) rfl eN (inv_ev ht heN) rest w0 hw0 (fun j hj' => hok.mdescMemo .env .env j hj') with
    hs | ⟨t4, he, hmem, hout, hd4, hg4, hc4, hl4, hj4⟩
  · exact Or.inl hs
  have hsr' : SR (ctxIns C fe C.EH (C.envM.erase n)) s t4 :=
    sr_envIns (C := C) (EH := C.EH) hok ht.sr hout hd4 hg4 hc4 hmem hlit hden
  rw [he]
  exact hk t4 (inv_after_undo ht hsr' hl4 hj4)

end

end ConPanqueque.T.Decl
