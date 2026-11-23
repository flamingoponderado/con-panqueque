import ConPanqueque.T.Big.ReduceNat
import ConPanqueque.T.LoopT
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# `whnfBody`: the reduction loop

The twin's `whnfLoop` iterates `whnfStep` — `whnfCore`, then `reduceNat`, then `unfoldDefinition` — on a step
budget of `2^62`. The port runs the same steps in a `while` loop, threading the twin (`specR_whileT`).
-/

namespace ConPanqueque.T.WB

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big

section
variable {σ : Type}

theorem step_ifI {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {Q : PState σ → Prop}
    {c1 c2 : ProgHOL 64} (e : ExpHOL 64) (w : BitVec 64) (he : sev Γ e = some w)
    (h1 : w ≠ 0 → Step (Inv C s Γ M D) c1 Q) (h2 : w = 0 → Step (Inv C s Γ M D) c2 Q) :
    Step (Inv C s Γ M D) (.ite e c1 c2) Q := by
  intro t ht
  rw [ite_word t e c1 c2 w (inv_ev ht he)]
  by_cases hw : w ≠ 0
  · rw [if_pos hw]; exact h1 hw t ht
  · rw [if_neg hw]; exact h2 (by simpa using hw) t ht

theorem step_hangI {P Q : PState σ → Prop} : Step P hang Q :=
  fun t _ => Or.inl (Or.inl (hang_spec t.clock t rfl))

theorem step_ex {α : Type} {P : α → PState σ → Prop} {Q : PState σ → Prop} {c : ProgHOL 64}
    (h : ∀ a, Step (P a) c Q) : Step (fun t => ∃ a, P a t) c Q :=
  fun t ⟨a, ht⟩ => h a t ht

/-! ## The twin's loop, one step at a time -/

theorem whnfLoop_succ (r : CoreFnsA) (fe : IFEnv) (d f : Nat) (e : EIdx) (s : AState) :
    whnfLoop r fe d (f + 1) e s = (whnfStep r fe d e >>= fun st => match st with
      | .done v => pure v
      | .cont e' => whnfLoop r fe d f e') s := rfl

theorem whnfStep_lit (r : CoreFnsA) (fe : IFEnv) (d : Nat) (e e1 e2 : EIdx) (s1 s2 s3 : AState)
    (h1 : r.whnfCore false d e s1 = .ok (e1, s2)) (h2 : reduceNat r fe d e1 s2 = .ok (some e2, s3)) :
    whnfStep r fe d e s1 = .ok (if e2.tag == ETag.lit then .done e2 else .cont e2, s3) := by
  show (Except.bind (r.whnfCore false d e s1) fun x => _) = _
  rw [h1]; simp only [Except.bind]
  show (Except.bind (reduceNat r fe d e1 s2) fun x => _) = _
  rw [h2]; simp only [Except.bind]
  split <;> rfl

theorem whnfStep_unf (r : CoreFnsA) (fe : IFEnv) (d : Nat) (e e1 : EIdx) (o : Option EIdx) (s1 s2 s3 s4 : AState)
    (h1 : r.whnfCore false d e s1 = .ok (e1, s2)) (h2 : reduceNat r fe d e1 s2 = .ok (none, s3))
    (h3 : unfoldDefinition fe e1 s3 = .ok (o, s4)) :
    whnfStep r fe d e s1 = .ok (match o with | some e2 => .cont e2 | none => .done e1, s4) := by
  show (Except.bind (r.whnfCore false d e s1) fun x => _) = _
  rw [h1]; simp only [Except.bind]
  show (Except.bind (reduceNat r fe d e1 s2) fun x => _) = _
  rw [h2]; simp only [Except.bind]
  show (Except.bind (unfoldDefinition fe e1 s3) fun x => _) = _
  cases o <;> (simp only [h3, Except.bind]; rfl)

end

end ConPanqueque.T.WB
