import ConPanqueque.T.Big.Cmp
import ConPanqueque.T.Core.ConstVal
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# A literal's limbs into the value heap

The bignum arithmetic works heap block to heap block. `litToHeap(h)` copies the limbs of the literal at `h`
into a fresh block. A heap store forgets the store-row facts a view gave, so the loop views the handle again
for each limb (`step_eViewI`, the view as a `Step`).
-/

namespace ConPanqueque.T.Big

open ConPanqueque.T ConPanqueque.T.Ex
open ConPanqueque.V.Enc

section
variable {σ : Type}

/-- The expression view as a step: afterwards the row's words are memory facts. -/
theorem step_eViewI {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} (h : EIdx) (v : ENodeView)
    (hv : s.store.view h = some v)
    (hdh : Γ.get lDh = some (Enc.idxW h)) (hfl : Γ.get lFl = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR)
    (hD : lDt ∈ D ∧ lDg ∈ D ∧ lDi ∈ D ∧ lRp ∈ D ∧ lRn ∈ D) :
    Step (Inv (σ := σ) C s Γ M D) eViewP (fun t => ∃ P, Inv C s ((lRp, P) ::
      (lRn, BitVec.ofNat 64 (encEView v).length) :: (lDt, BitVec.ofNat 64 h.tier.toNat) ::
      (lDg, BitVec.ofNat 64 v.tagN) :: (lDi, BitVec.ofNat 64 h.idxNat) :: Γ) (wordsAt P (encEView v) ++ M) D t) := by
  intro t ht
  rcases eView_spec t C.L C.FLe s.store ht.sr.rep.e h (ht.env _ _ hdh) (ht.env _ _ hdir) (ht.env _ _ hfl)
      (ht.decl _ hD.1) (ht.decl _ hD.2.1) (ht.decl _ hD.2.2.1) (ht.decl _ hD.2.2.2.1) (ht.decl _ hD.2.2.2.2) with
    hs | ⟨v', hv', htg, hr⟩
  · exact Or.inl hs
  rw [hv] at hv'; cases hv'
  obtain ⟨hn, hm, hd, hc, hg, _, ⟨P, hrp, hW⟩, hrn, hsh, hdt, hdg, hdi, hfr⟩ := hr
  refine Or.inr ⟨hn, P, sr_of_eq ht.sr hm hd hg hc, fun y w hy => ?_, fun b w hb => ?_, fun y hy => ?_⟩
  · simp only [Env.get] at hy
    split at hy
    · rename_i e; subst e; simp at hy; subst hy; exact hrp
    split at hy
    · rename_i e; subst e; simp at hy; subst hy; exact hrn
    split at hy
    · rename_i e; subst e; simp at hy; subst hy; exact hdt
    split at hy
    · rename_i e; subst e; simp at hy; subst hy; rw [htg]; exact hdg
    split at hy
    · rename_i e; subst e; simp at hy; subst hy; exact hdi
    rename_i e1 e2 e3 e4 e5
    rw [hfr y e1 e2 e3 e4 e5]; exact ht.env y w hy
  · simp only [List.mem_append] at hb
    rcases hb with hb | hb
    · rw [hm, hd]; exact wordsAt_mem hW b w hb
    · rw [hm, hd]; exact ht.mem b w hb
  · by_cases e1 : y = lRp
    · subst e1; exact ⟨P, hrp⟩
    by_cases e2 : y = lRn
    · subst e2; exact ⟨_, hrn⟩
    by_cases e3 : y = lDt
    · subst e3; exact ⟨_, hdt⟩
    by_cases e4 : y = lDg
    · subst e4; exact ⟨_, hdg⟩
    by_cases e5 : y = lDi
    · subst e5; exact ⟨_, hdi⟩
    obtain ⟨w, hw⟩ := ht.decl y hy; exact ⟨w, by rw [hfr y e1 e2 e3 e4 e5]; exact hw⟩

end

end ConPanqueque.T.Big
