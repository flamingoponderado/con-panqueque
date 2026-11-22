import ConPanqueque.T.Call
import ConPanqueque.V.View
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# The state relation, and the store primitives as `Spec`s

`SR C s t`: the twin state `s` is represented in the Pancake state `t` under the context `C` — the
stores (`SRep`), and the context words (layout directory, flag words, key buffer) in globals,
which a translated function's prologue copies into the locals the store code reads.
(Memos, caches and pins join later.)
-/

namespace ConPanqueque.T

structure Ctx where
  L : Layout
  FLn : BitVec 64
  FLl : BitVec 64
  FLs : BitVec 64
  FLe : BitVec 64
  KB : BitVec 64
  /-- The program's functions. -/
  code : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)

def gDir := ofString "Gdir"
def gFln := ofString "Gfln"
def gFll := ofString "Gfll"
def gFls := ofString "Gfls"
def gFle := ofString "Gfle"
def gKb := ofString "Gkb"

variable {σ : Type}

structure SR (C : Ctx) (s : AState) (t : PState σ) : Prop where
  rep : SRep t C.L C.FLn C.FLl C.FLs C.FLe s.store
  gdir : t.globals.lookup gDir = some (.val (.word C.L.DIR))
  gfln : t.globals.lookup gFln = some (.val (.word C.FLn))
  gfll : t.globals.lookup gFll = some (.val (.word C.FLl))
  gfls : t.globals.lookup gFls = some (.val (.word C.FLs))
  gfle : t.globals.lookup gFle = some (.val (.word C.FLe))
  gkb : t.globals.lookup gKb = some (.val (.word C.KB))
  code : t.code = C.code

theorem sr_of_eq {C : Ctx} {s : AState} {t u : PState σ} (h : SR C s t) (hm : u.memory = t.memory)
    (hd : u.memaddrs = t.memaddrs) (hg : u.globals = t.globals) (hc : u.code = t.code) : SR C s u :=
  ⟨srep_frame h.rep ⟨by rw [hm], by rw [hm], by rw [hm], by rw [hm]⟩ hd
      (fun _ _ _ _ => ⟨fun _ _ => by rw [hm], fun _ _ => by rw [hm]⟩),
    by rw [hg]; exact h.gdir, by rw [hg]; exact h.gfln, by rw [hg]; exact h.gfll, by rw [hg]; exact h.gfls,
    by rw [hg]; exact h.gfle, by rw [hg]; exact h.gkb, by rw [hc]; exact h.code⟩

theorem eval_gv (t : PState σ) (g : MlS) (w : BitVec 64) (h : t.globals.lookup g = some (.val (.word w))) :
    EV t (.var .global g) = some (.val (.word w)) := by
  simp [EV, evalHOLExact, h]

/-! ## Local declarations -/

theorem specR_dec {α : Type} {P P1 : PState σ → Prop} {s : AState} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (e : ExpHOL 64) (body : ProgHOL 64)
    (v : PState σ → BitVec 64) (he : ∀ t, P t → EV t e = some (.val (.word (v t))))
    (h : SpecR P1 body s m R) (hP : ∀ t, P t → P1 (setVarHOLFinite x (.val (.word (v t))) t))
    (hR : ∀ a w s' st (L : HolFiniteMapExact MlS (ValueHOL 64)), R a w s' st → R a w s' { st with locals := L }) :
    SpecR P (.dec x .one e body) s m R := by
  intro t ht
  rw [dec_word_eq t x e (v t) body (he t ht)]
  rcases h _ (hP t ht) with hs | ⟨w, hr, a, s', hm, hR'⟩
  · exact Or.inl hs
  · exact Or.inr ⟨w, hr, a, s', hm, hR _ _ _ _ _ hR'⟩

/-! ## `app` handles -/

theorem view_app_some (st : EStore) (i : EIdx) (f a : EIdx) (h4 : i.tag = 4) (hv : st.view i = some (.app f a)) :
    st.viewApp i = some (f, a) := by
  have hw : i.isWide = true := by
    cases hw : i.isWide
    · exfalso
      simp only [EStore.view] at hv
      split at hv
      · simp [ETables.get, h4, hw, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app] at hv
      · split at hv
        · simp [ETables.get, h4, hw, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app] at hv
        · exact absurd hv (by simp)
    · rfl
  simp only [EStore.view] at hv
  simp only [EStore.viewApp, EStore.persGetApp]
  split
  · rename_i hp; rw [if_pos hp] at hv
    simp only [ETables.get, h4, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, hw] at hv
    simp only [ETables.getApp, hw, ↓reduceIte]
    revert hv; cases st.pers.apps.node? i.idxNat <;> simp
  · rename_i hp; rw [if_neg hp] at hv
    split
    · rename_i hon; rw [if_pos hon] at hv
      simp only [ETables.get, h4, ETag.bvar, ETag.fvar, ETag.sort, ETag.const, ETag.app, hw] at hv
      simp only [ETables.getApp, hw, ↓reduceIte]
      revert hv; cases st.scr.apps.node? i.idxNat <;> simp
    · rename_i hon; rw [if_neg hon] at hv; exact absurd hv (by simp)

theorem viewApp_run (h : EIdx) (s : AState) : ConRon.Arena.viewApp h s = .ok (s.store.viewApp h, s) := rfl

/-- The twin's `viewApp h` at an `app`-tagged handle, by the expression view; the fields are at `rp`. -/
theorem spec_viewApp {C : Ctx} {s : AState} {P : PState σ → Prop} {Q : Option (EIdx × EIdx) → AState → PState σ → Prop}
    (h : EIdx) (h4 : h.tag = 4)
    (hP : ∀ t, P t → SR C s t ∧ t.locals.lookup lDh = some (.val (.word (Enc.idxW h))) ∧
      t.locals.lookup lDir = some (.val (.word C.L.DIR)) ∧ t.locals.lookup lFl = some (.val (.word C.FLe)) ∧
      (∃ w, t.locals.lookup lDt = some (.val (.word w))) ∧ (∃ w, t.locals.lookup lDg = some (.val (.word w))) ∧
      (∃ w, t.locals.lookup lDi = some (.val (.word w))) ∧ (∃ w, t.locals.lookup lRp = some (.val (.word w))) ∧
      (∃ w, t.locals.lookup lRn = some (.val (.word w))))
    (hQ : ∀ t, P t → ∀ f a, RowRes t h.tier.toNat h.tag.toNat h.idxNat (Enc.encApp ⟨f, a⟩) (evaluateHOLFiniteState t eViewP) →
      Q (some (f, a)) s (evaluateHOLFiniteState t eViewP).2) :
    Spec P eViewP s (ConRon.Arena.viewApp h) Q := by
  intro t ht
  obtain ⟨hsr, hh, hdir, hfl, ht', hg, hi, h1, h2⟩ := hP t ht
  rcases eView_spec t C.L C.FLe s.store hsr.rep.e h hh hdir hfl ht' hg hi h1 h2 with hs | ⟨v, hv, htg, hr⟩
  · exact Or.inl hs
  rw [h4] at htg
  cases v with
  | app f a =>
    right
    refine ⟨hr.1, some (f, a), s, ?_, hQ t ht f a hr⟩
    rw [viewApp_run, view_app_some s.store h f a h4 hv]
  | _ => simp [ENodeView.tagN] at htg

/-- `var x₁ = 0; …; var xₙ = 0; body`. -/
def decs0 : List MlS → ProgHOL 64 → ProgHOL 64
  | [], b => b
  | x :: xs, b => .dec x .one (.const 0) (decs0 xs b)

/-- `t'` is `t` with the locals `xs` freshly zeroed. -/
def Zeroed (xs : List MlS) (t t' : PState σ) : Prop :=
  t'.memory = t.memory ∧ t'.memaddrs = t.memaddrs ∧ t'.globals = t.globals ∧ t'.code = t.code ∧
    (∀ y, y ∉ xs → t'.locals.lookup y = t.locals.lookup y) ∧
    (∀ x, x ∈ xs → t'.locals.lookup x = some (.val (.word 0)))

theorem specR_decs0 {α : Type} {s : AState} {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop}
    (hR : ∀ a w s' st (L : HolFiniteMapExact MlS (ValueHOL 64)), R a w s' st → R a w s' { st with locals := L })
    (body : ProgHOL 64) (I : PState σ → Prop) (h : SpecR I body s m R) :
    ∀ (xs : List MlS) (P : PState σ → Prop), (∀ t, P t → ∀ t', Zeroed xs t t' → I t') → SpecR P (decs0 xs body) s m R
  | [], P, hP => fun t ht => h t (hP t ht t ⟨rfl, rfl, rfl, rfl, fun _ _ => rfl, fun _ hx => absurd hx (by simp)⟩)
  | x :: xs, P, hP => by
    refine specR_dec x (.const 0) (decs0 xs body) (fun _ => 0) (fun t _ => by simp [EV, evalHOLExact])
      (specR_decs0 hR body I h xs (fun u => ∃ t, P t ∧ u = setVarHOLFinite x (.val (.word 0)) t) ?_)
      (fun t ht => ⟨t, ht, rfl⟩) hR
    rintro u ⟨t, ht, rfl⟩ t' ⟨m1, d1, g1, c1, fr1, z1⟩
    refine hP t ht t' ⟨m1, d1, g1, c1, fun y hy => ?_, fun z hz => ?_⟩
    · simp only [List.mem_cons, not_or] at hy
      rw [fr1 y hy.2]; exact lookup_setVar_other _ _ hy.1
    · by_cases hzx : z ∈ xs
      · exact z1 z hzx
      · simp only [List.mem_cons] at hz
        rcases hz with rfl | hz
        · rw [fr1 _ hzx]; exact lookup_setVar_same _ _ _
        · exact absurd hz hzx

end ConPanqueque.T
