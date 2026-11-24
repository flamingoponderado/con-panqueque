import ConPanqueque.Front.Tbl
import ConPanqueque.Scan.LineFun

/-! # Pure scanner calls inside the declaration layer's `Inv` world

The scanners are specified in the soundness form `RetP` (they stop, or return a word satisfying a
predicate with memory, its domain, the globals, the code and the endianness unchanged).  A call to
one from a procedure specified with `SpecR`/`Inv` keeps the state's representation (`SR` reads only
those components) and every memory fact, and binds the result. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan

variable {σ : Type}

/-- `x := f(a₁, a₂, a₃); rest` at a pure callee specified by `RetP`. -/
theorem specR_retP3 {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    {rest : ProgHOL 64} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (x f x1 x2 x3 : MlS) (body : ProgHOL 64) (a1 a2 a3 : ExpHOL 64) (v1 v2 v3 : BitVec 64)
    (P : BitVec 64 → Prop) (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3) (hx : x ∈ D)
    (hcode : C.code.lookup f = some ([(x1, .one), (x2, .one), (x3, .one)], body, .one))
    (he1 : sev Γ a1 = some v1) (he2 : sev Γ a2 = some v2) (he3 : sev Γ a3 = some v3)
    (hbody : ∀ (t : PState σ) (callee : HolFiniteMapExact MlS (ValueHOL 64)), Inv C s Γ M D t →
      callee.lookup x1 = some (.val (.word v1)) → callee.lookup x2 = some (.val (.word v2)) →
      callee.lookup x3 = some (.val (.word v3)) → RetP (callEntryStateHOLFinite t callee) body P)
    (hk : ∀ w, P w → SpecR (Inv C s ((x, w) :: Γ) M D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (callTo x f [a1, a2, a3]) rest) s m R := by
  intro t ht
  obtain ⟨w0, hw0⟩ := ht.decl x hx
  rcases call3_retP t x f x1 x2 x3 body a1 a2 a3 v1 v2 v3 w0 P h12 h13 h23 (by rw [ht.sr.code]; exact hcode)
      (inv_ev ht he1) (inv_ev ht he2) (inv_ev ht he3) hw0 (fun callee h1 h2 h3 => hbody t callee ht h1 h2 h3) with
    hs | ⟨w, u, hp, hu, m1, d1, g1, c1, b1, lx, lo⟩
  · exact Or.inl (seq_stop t _ _ hs)
  have hinv : Inv C s ((x, w) :: Γ) M D u := by
    refine ⟨sr_of_eq ht.sr m1 d1 g1 c1, fun y v hy => ?_, fun a v ha => by rw [m1, d1]; exact ht.mem a v ha,
      fun y hy => ?_⟩
    · simp only [Env.get] at hy
      split at hy
      · rename_i e; subst e; simp at hy; subst hy; exact lx
      · rename_i e; rw [lo y e]; exact ht.env y v hy
    · by_cases e : y = x
      · subst e; exact ⟨w, lx⟩
      · rw [lo y e]; exact ht.decl y hy
  simp only [callTo]
  rw [seq_normal _ hu]
  exact hk w hp u hinv

end ConPanqueque.Front
