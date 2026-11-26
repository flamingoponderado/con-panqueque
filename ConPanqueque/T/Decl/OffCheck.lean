import ConPanqueque.T.Decl.Flush
import ConPanqueque.Logic.InternRerun

/-!
# The scratch tier off (else hang)

`offCheckP C rest`: the four stores' scratch flags (memory words at `C.FLe`, `C.FLs`, `C.FLl`, `C.FLn`) read;
any set hangs.  Past it the twin store is `InternRerun.Off`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot

def ocA := ofString "oc_a"
def ocB := ofString "oc_b"
def ocC := ofString "oc_c"
def ocD := ofString "oc_d"

def offCheckP (C : Ctx) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local ocA (.load .one (.const C.FLe)))
  (.seq (.assign .local ocB (.load .one (.const C.FLs)))
  (.seq (.assign .local ocC (.load .one (.const C.FLl)))
  (.seq (.assign .local ocD (.load .one (.const C.FLn)))
  (.ite (.op .or [vv ocA, .op .or [vv ocB, .op .or [vv ocC, vv ocD]]]) hang rest))))

section
variable {σ : Type}

theorem specR_flagLoadI {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (FL : BitVec 64) (b : Bool)
    (hfl : ∀ t : PState σ, Inv C s Γ M D t → t.memaddrs FL ∧ t.memory FL = .word (if b then 1 else 0)) (hx : x ∈ D)
    (h : SpecR (Inv C s ((x, if b then 1 else 0) :: Γ) M D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (.assign .local x (.load .one (.const FL))) rest) s m R :=
  specR_pre_assign x (.load .one (.const FL)) (fun _ => if b then 1 else 0)
    (fun t ht => by
      rw [EV, eval_load_word t _ _ (by rfl) (hfl t ht).1, (hfl t ht).2])
    (fun t ht => ht.decl x hx) (fun t ht => inv_set ht x _) h

/-- **The scratch tier checked off.** -/
theorem specR_offCheckI {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (hD : ocA ∈ D ∧ ocB ∈ D ∧ ocC ∈ D ∧ ocD ∈ D)
    (hk : InternRerun.Off s.store → SpecR (Inv C s ((ocD, 0) :: (ocC, 0) :: (ocB, 0) :: (ocA, 0) :: Γ) M D) rest s m R) :
    SpecR (Inv C s Γ M D) (offCheckP C rest) s m R := by
  unfold offCheckP
  refine specR_flagLoadI ocA C.FLe s.store.scratchOn (fun t ht => ht.sr.rep.e.fl) hD.1 ?_
  refine specR_flagLoadI ocB C.FLs s.store.lss.scratchOn (fun t ht => ht.sr.rep.ls.fl) hD.2.1 ?_
  refine specR_flagLoadI ocC C.FLl s.store.lss.ls.scratchOn (fun t ht => ht.sr.rep.l.fl) hD.2.2.1 ?_
  refine specR_flagLoadI ocD C.FLn s.store.lss.ls.ns.scratchOn (fun t ht => ht.sr.rep.n.fl) hD.2.2.2 ?_
  by_cases hoff : InternRerun.Off s.store
  · obtain ⟨h1, h2, h3, h4⟩ := hoff
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, h1, h2, h3, h4]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte]
    exact hk ⟨h1, h2, h3, h4⟩
  · refine specR_ifI _ ((if s.store.scratchOn then 1 else 0) ||| ((if s.store.lss.scratchOn then 1 else 0) |||
      ((if s.store.lss.ls.scratchOn then 1 else 0) ||| (if s.store.lss.ls.ns.scratchOn then 1 else 0))))
      (by simp +decide [sev, Env.get_cons]) (fun _ => specR_hangI) (fun h => ?_)
    exfalso; apply hoff
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      (revert h; cases s.store.scratchOn <;> cases s.store.lss.scratchOn <;> cases s.store.lss.ls.scratchOn <;>
        cases s.store.lss.ls.ns.scratchOn <;> decide)

end

end ConPanqueque.T.Decl
