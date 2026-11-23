import ConPanqueque.T.NView
import ConPanqueque.V.LsView
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-! # The level-list view over the invariant -/

namespace ConPanqueque.T

variable {σ : Type}

theorem specR_lsviewPI {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (h : LsIdx)
    (hdh : Γ.get lDh = some (Enc.idxW h)) (hfl : Γ.get lFl = some C.FLs) (hdir : Γ.get lDir = some C.L.DIR)
    (hD : lDt ∈ D ∧ lDg ∈ D ∧ lDi ∈ D ∧ lRp ∈ D ∧ lRn ∈ D)
    (hk : ∀ v P, s.store.lss.view h = some v → h.tag.toNat = 0 → (v.map Enc.idxW).length < 2 ^ 61 →
      SpecR (Inv C s ((lRp, P) ::
      (lRn, BitVec.ofNat 64 (v.map Enc.idxW).length) :: (lDt, BitVec.ofNat 64 h.tier.toNat) ::
      (lDg, BitVec.ofNat 64 0) :: (lDi, BitVec.ofNat 64 h.idxNat) :: Γ)
      (wordsAt P (v.map Enc.idxW) ++ M) D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq lsViewP rest) s m R := by
  intro t ht
  rcases lsView_spec t C.L C.FLs s.store.lss ht.sr.rep.ls h (ht.env _ _ hdh) (ht.env _ _ hdir) (ht.env _ _ hfl)
      (ht.decl _ hD.1) (ht.decl _ hD.2.1) (ht.decl _ hD.2.2.1) (ht.decl _ hD.2.2.2.1) (ht.decl _ hD.2.2.2.2) with
    hs | ⟨v, hv, htg, hr⟩
  · exact Or.inl (seq_stop t _ _ hs)
  obtain ⟨hn, hm, hd, hc, hg, _, ⟨P, hrp, hW⟩, hrn, hsh, hdt, hdg, hdi, hfr⟩ := hr
  have e : evaluateHOLFiniteState t lsViewP = (none, (evaluateHOLFiniteState t lsViewP).2) := by rw [← hn]
  rw [seq_normal rest e]
  refine hk v P hv htg hsh _ ⟨sr_of_eq ht.sr hm hd hg hc, fun y w hy => ?_, fun b w hb => ?_, fun y hy => ?_⟩
  · simp only [Env.get] at hy
    split at hy
    · rename_i e; subst e; simp at hy; subst hy; exact hrp
    split at hy
    · rename_i e; subst e; simp at hy; subst hy; simpa using hrn
    split at hy
    · rename_i e; subst e; simp at hy; subst hy; exact hdt
    split at hy
    · rename_i e; subst e; simp at hy; subst hy; exact hdg
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


end ConPanqueque.T
