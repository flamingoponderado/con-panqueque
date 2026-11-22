import ConPanqueque.T.LView
import ConPanqueque.V.NView
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Name views that the twin does not see

`nViewP; rest` where the twin computes on read-back names: the continuation gets the view the store
holds and its row as known memory, against the same twin computation.
-/

namespace ConPanqueque.T

variable {σ : Type}

theorem wordsAt_get (P : BitVec 64) (xs : List (BitVec 64)) (i : Nat) (hi : i < xs.length) (M : Mem) :
    (P + BitVec.ofNat 64 (8 * i), xs[i]) ∈ wordsAt P xs ++ M := by
  refine List.mem_append_left _ ?_
  simp only [wordsAt, List.mem_map]
  exact ⟨(i, xs[i]), List.mem_iff_getElem.mpr ⟨i, by simp [hi], by simp⟩, rfl⟩

theorem specR_nviewPI {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (h : NIdx)
    (hdh : Γ.get lDh = some (Enc.idxW h)) (hfl : Γ.get lFl = some C.FLn) (hdir : Γ.get lDir = some C.L.DIR)
    (hD : lDt ∈ D ∧ lDg ∈ D ∧ lDi ∈ D ∧ lRp ∈ D ∧ lRn ∈ D)
    (hk : ∀ v P, s.store.ns.view h = some v → v.tagN = h.tag.toNat → (encNView v).length < 2 ^ 61 →
      SpecR (Inv C s ((lRp, P) ::
      (lRn, BitVec.ofNat 64 (encNView v).length) :: (lDt, BitVec.ofNat 64 h.tier.toNat) ::
      (lDg, BitVec.ofNat 64 v.tagN) :: (lDi, BitVec.ofNat 64 h.idxNat) :: Γ)
      (wordsAt P (encNView v) ++ M) D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq nViewP rest) s m R := by
  intro t ht
  rcases nView_spec t C.L C.FLn s.store.ns ht.sr.rep.n h (ht.env _ _ hdh) (ht.env _ _ hdir) (ht.env _ _ hfl)
      (ht.decl _ hD.1) (ht.decl _ hD.2.1) (ht.decl _ hD.2.2.1) (ht.decl _ hD.2.2.2.1) (ht.decl _ hD.2.2.2.2) with
    hs | ⟨v, hv, htg, hr⟩
  · exact Or.inl (seq_stop t _ _ hs)
  obtain ⟨hn, hm, hd, hc, hg, _, ⟨P, hrp, hW⟩, hrn, hsh, hdt, hdg, hdi, hfr⟩ := hr
  have e : evaluateHOLFiniteState t nViewP = (none, (evaluateHOLFiniteState t nViewP).2) := by rw [← hn]
  rw [seq_normal rest e]
  refine hk v P hv htg hsh _ ⟨sr_of_eq ht.sr hm hd hg hc, fun y w hy => ?_, fun b w hb => ?_, fun y hy => ?_⟩
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

/-- A denoting name handle's view, and the name it reads back to. -/
theorem denoteNAux_cases (st : NStore) (f : Nat) (i : NIdx) (x : ConLeche.Name) (v : NNodeView)
    (hd : denoteNAux st f i = some x) (hv : st.view i = some v) :
    (v = .anonymous ∧ x = .anonymous) ∨
    (∃ p str q f', v = .str p str ∧ x = .str q str ∧ denoteNAux st f' p = some q) ∨
    (∃ p n q f', v = .num p n ∧ x = .num q n ∧ denoteNAux st f' p = some q) := by
  cases f with
  | zero => simp [denoteNAux] at hd
  | succ f =>
    simp only [denoteNAux, hv, Option.bind_some] at hd
    cases v with
    | anonymous => left; simp at hd; exact ⟨rfl, hd.symm⟩
    | str p str =>
      right; left
      simp only [Option.map_eq_some_iff] at hd
      obtain ⟨q, hq, rfl⟩ := hd
      exact ⟨p, str, q, f, rfl, rfl, hq⟩
    | num p n =>
      right; right
      simp only [Option.map_eq_some_iff] at hd
      obtain ⟨q, hq, rfl⟩ := hd
      exact ⟨p, n, q, f, rfl, rfl, hq⟩

theorem denoteNAux_det (st : NStore) (f f' : Nat) (i : NIdx) (x y : ConLeche.Name)
    (h1 : denoteNAux st f i = some x) (h2 : denoteNAux st f' i = some y) : x = y := by
  have a := denoteNAux_mono st f (max f f') i x (by omega) h1
  have b := denoteNAux_mono st f' (max f f') i y (by omega) h2
  rw [a] at b; exact Option.some.inj b

end ConPanqueque.T
