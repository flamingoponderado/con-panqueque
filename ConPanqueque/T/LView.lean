import ConPanqueque.T.Loop
import ConPanqueque.V.LView
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# The level view in a caller

`lViewP; rest` against the twin's `viewL h >>= k`: the fields become known memory words.
-/

namespace ConPanqueque.T

variable {σ : Type}

theorem viewL_run (h : LIdx) (s : AState) :
    ConRon.Arena.viewL h s = match s.store.ls.view h with
      | some v => .ok (v, s)
      | none => .error (.internal "arena: dangling level handle") := by
  show (match s.store.ls.view h with
    | some v => (pure v : AM LNodeView)
    | none => fail (.internal "arena: dangling level handle")) s = _
  cases s.store.ls.view h <;> rfl

theorem specR_lviewI {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {k : LNodeView → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (h : LIdx)
    (hdh : Γ.get lDh = some (Enc.idxW h)) (hfl : Γ.get lFl = some C.FLl) (hdir : Γ.get lDir = some C.L.DIR)
    (hD : lDt ∈ D ∧ lDg ∈ D ∧ lDi ∈ D ∧ lRp ∈ D ∧ lRn ∈ D)
    (hk : ∀ v P, v.tagN = h.tag.toNat → (encLView v).length < 2 ^ 61 → SpecR (Inv C s ((lRp, P) ::
      (lRn, BitVec.ofNat 64 (encLView v).length) :: (lDt, BitVec.ofNat 64 h.tier.toNat) ::
      (lDg, BitVec.ofNat 64 v.tagN) :: (lDi, BitVec.ofNat 64 h.idxNat) :: Γ)
      (wordsAt P (encLView v) ++ M) D) rest s (k v) R) :
    SpecR (Inv C s Γ M D) (.seq lViewP rest) s (ConRon.Arena.viewL h >>= k) R := by
  intro t ht
  rcases lView_spec t C.L C.FLl s.store.ls ht.sr.rep.l h (ht.env _ _ hdh) (ht.env _ _ hdir) (ht.env _ _ hfl)
      (ht.decl _ hD.1) (ht.decl _ hD.2.1) (ht.decl _ hD.2.2.1) (ht.decl _ hD.2.2.2.1) (ht.decl _ hD.2.2.2.2) with
    hs | ⟨v, hv, htg, hr⟩
  · exact Or.inl (seq_stop t _ _ hs)
  obtain ⟨hn, hm, hd, hc, hg, _, ⟨P, hrp, hW⟩, hrn, hsh, hdt, hdg, hdi, hfr⟩ := hr
  have e : evaluateHOLFiniteState t lViewP = (none, (evaluateHOLFiniteState t lViewP).2) := by rw [← hn]
  rw [seq_normal rest e]
  have hInv : Inv C s ((lRp, P) :: (lRn, BitVec.ofNat 64 (encLView v).length) ::
      (lDt, BitVec.ofNat 64 h.tier.toNat) :: (lDg, BitVec.ofNat 64 v.tagN) :: (lDi, BitVec.ofNat 64 h.idxNat) :: Γ)
      (wordsAt P (encLView v) ++ M) D (evaluateHOLFiniteState t lViewP).2 := by
    refine ⟨sr_of_eq ht.sr hm hd hg hc, fun y w hy => ?_, fun b w hb => ?_, fun y hy => ?_⟩
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
  rcases hk v P htg hsh _ hInv with hs | ⟨w, hr', a, s', hk', hR⟩
  · exact Or.inl hs
  refine Or.inr ⟨w, hr', a, s', ?_, hR⟩
  show (do let r ← ConRon.Arena.viewL h s; match r with | (a, s) => k a s) = _
  rw [viewL_run, hv]; exact hk'

end ConPanqueque.T
