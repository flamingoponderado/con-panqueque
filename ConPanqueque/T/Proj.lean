import ConPanqueque.T.Inv
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Projections of the expression view

The twin's projections (`viewLet`, `viewBind`, `viewProj`, `viewBVar`) read one constructor's table;
after the tag test that precedes them they agree with the view. `specR_viewXI` is `specR_viewI` for
any such projection.
-/

namespace ConPanqueque.T

variable {σ : Type}

theorem specR_viewXI {α β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {k : Option α → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (viewX : EIdx → AM (Option α)) (proj : ENodeView → Option α) (h : EIdx)
    (hrel : ∀ v, s.store.view h = some v → viewX h s = .ok (proj v, s))
    (hdh : Γ.get lDh = some (Enc.idxW h)) (hfl : Γ.get lFl = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR)
    (hD : lDt ∈ D ∧ lDg ∈ D ∧ lDi ∈ D ∧ lRp ∈ D ∧ lRn ∈ D)
    (hk : ∀ v P, v.tagN = h.tag.toNat → SpecR (Inv C s ((lRp, P) ::
      (lRn, BitVec.ofNat 64 (encEView v).length) :: (lDt, BitVec.ofNat 64 h.tier.toNat) ::
      (lDg, BitVec.ofNat 64 v.tagN) :: (lDi, BitVec.ofNat 64 h.idxNat) :: Γ)
      (wordsAt P (encEView v) ++ M) D) rest s (k (proj v)) R) :
    SpecR (Inv C s Γ M D) (.seq eViewP rest) s (viewX h >>= k) R := by
  intro t ht
  rcases eView_spec t C.L C.FLe s.store ht.sr.rep.e h (ht.env _ _ hdh) (ht.env _ _ hdir) (ht.env _ _ hfl)
      (ht.decl _ hD.1) (ht.decl _ hD.2.1) (ht.decl _ hD.2.2.1) (ht.decl _ hD.2.2.2.1) (ht.decl _ hD.2.2.2.2) with
    hs | ⟨v, hv, htg, hr⟩
  · exact Or.inl (seq_stop t _ _ hs)
  obtain ⟨hn, hm, hd, hc, hg, _, ⟨P, hrp, hW⟩, hrn, _, hdt, hdg, hdi, hfr⟩ := hr
  have e : evaluateHOLFiniteState t eViewP = (none, (evaluateHOLFiniteState t eViewP).2) := by rw [← hn]
  rw [seq_normal rest e]
  have hInv : Inv C s ((lRp, P) :: (lRn, BitVec.ofNat 64 (encEView v).length) ::
      (lDt, BitVec.ofNat 64 h.tier.toNat) :: (lDg, BitVec.ofNat 64 v.tagN) :: (lDi, BitVec.ofNat 64 h.idxNat) :: Γ)
      (wordsAt P (encEView v) ++ M) D (evaluateHOLFiniteState t eViewP).2 := by
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
  rcases hk v P htg _ hInv with hs | ⟨w, hr', a, s', hk', hR⟩
  · exact Or.inl hs
  refine Or.inr ⟨w, hr', a, s', ?_, hR⟩
  show (do let r ← viewX h s; match r with | (a, s) => k a s) = _
  rw [hrel v hv]; exact hk'

/-- A view's `let` fields. -/
def projLet : ENodeView → Option (EIdx × EIdx × EIdx)
  | .letE ty v b => some (ty, v, b)
  | _ => none

def projBind : ENodeView → Option (EIdx × EIdx)
  | .lam ty b => some (ty, b)
  | .forallE ty b => some (ty, b)
  | _ => none

def projProj : ENodeView → Option (NIdx × Nat × EIdx)
  | .proj n i e => some (n, i, e)
  | _ => none

def projBVar : ENodeView → Option Nat
  | .bvar i => some i
  | _ => none


theorem viewLet_bind (st : EStore) (h : EIdx) (h7 : h.tag = 7) :
    st.viewLet h = (st.view h).bind projLet := by
  simp only [EStore.view, EStore.viewLet, EStore.persGetLet]
  split
  · simp only [ETables.get, ETables.getLet, h7, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj]
    cases st.pers.lets.node? h.idxNat <;> rfl
  · split
    · simp only [ETables.get, ETables.getLet, h7, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj]
      cases st.scr.lets.node? h.idxNat <;> rfl
    · rfl

theorem viewProj_bind (st : EStore) (h : EIdx) (h9 : h.tag = 9) :
    st.viewProj h = (st.view h).bind projProj := by
  simp only [EStore.view, EStore.viewProj, EStore.persGetProj]
  split
  · simp only [ETables.get, ETables.getProj, h9, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj]
    cases st.pers.projs.node? h.idxNat <;> rfl
  · split
    · simp only [ETables.get, ETables.getProj, h9, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj]
      cases st.scr.projs.node? h.idxNat <;> rfl
    · rfl

theorem viewBVar_bind (st : EStore) (h : EIdx) (h0 : h.tag = 0) :
    st.viewBVar h = (st.view h).bind projBVar := by
  simp only [EStore.view, EStore.viewBVar, EStore.persGetBVar]
  split
  · simp only [ETables.get, ETables.getBVar, h0, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj]
    cases st.pers.bvars.node? h.idxNat <;> rfl
  · split
    · simp only [ETables.get, ETables.getBVar, h0, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj]
      cases st.scr.bvars.node? h.idxNat <;> rfl
    · rfl

theorem viewX_run {α : Type} (viewX : EIdx → AM (Option α)) (f : EStore → EIdx → Option α)
    (hdef : ∀ h s, viewX h s = .ok (f s.store h, s)) (proj : ENodeView → Option α) (h : EIdx)
    (hb : ∀ st : EStore, f st h = (st.view h).bind proj) (s : AState) (v : ENodeView) (hv : s.store.view h = some v) :
    viewX h s = .ok (proj v, s) := by
  rw [hdef, hb, hv]; rfl


theorem viewBind_bind (st : EStore) (h : EIdx) (hb : h.tag = 5 ∨ h.tag = 6) :
    st.viewBind h = (st.view h).bind projBind := by
  simp only [EStore.view, EStore.viewBind, EStore.persGetBind]
  rcases hb with hb | hb
  · split
    · simp only [ETables.get, ETables.getBind, hb, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj]
      cases st.pers.lams.node? h.idxNat <;> rfl
    · split
      · simp only [ETables.get, ETables.getBind, hb, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj]
        cases st.scr.lams.node? h.idxNat <;> rfl
      · rfl
  · split
    · simp only [ETables.get, ETables.getBind, hb, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj]
      cases st.pers.foralls.node? h.idxNat <;> rfl
    · split
      · simp only [ETables.get, ETables.getBind, hb, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, ETag.lam, ETag.forallE, ETag.letE, ETag.lit, ETag.proj]
        cases st.scr.foralls.node? h.idxNat <;> rfl
      · rfl

end ConPanqueque.T
