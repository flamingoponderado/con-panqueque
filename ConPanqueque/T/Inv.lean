import ConPanqueque.T.Store
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Symbolic environments

A translated function's state at a program point: `Inv C s Γ M D t` — the twin state `s` is
represented (`SR`), the locals in `Γ` hold their listed words, the memory words in `M` are known,
and every declared local in `D` holds a word. Expressions over `Γ` are evaluated symbolically
(`sev`, proved sound), so a step's obligations are computations; the combinators below are stated
in continuation style, the form the translator applies by goal shape.
-/

namespace ConPanqueque.T

abbrev Env := List (MlS × BitVec 64)

def Env.get : Env → MlS → Option (BitVec 64)
  | [], _ => none
  | (y, v) :: Γ, x => if x = y then some v else Env.get Γ x

abbrev Mem := List (BitVec 64 × BitVec 64)

/-- Symbolic evaluation of the word expressions translated code uses. -/
def sev (Γ : Env) : ExpHOL 64 → Option (BitVec 64)
  | .const w => some w
  | .var .local x => Γ.get x
  | .op .add [a, b] => do let x ← sev Γ a; let y ← sev Γ b; pure (x + y)
  | .op .sub [a, b] => do let x ← sev Γ a; let y ← sev Γ b; pure (x - y)
  | .op .and [a, b] => do let x ← sev Γ a; let y ← sev Γ b; pure (x &&& y)
  | .op .or [a, b] => do let x ← sev Γ a; let y ← sev Γ b; pure (x ||| y)
  | .op .xor [a, b] => do let x ← sev Γ a; let y ← sev Γ b; pure (x ^^^ y)
  | .panop .mul [a, b] => do let x ← sev Γ a; let y ← sev Γ b; pure (x * y)
  | .shift .lsl a (.const c) => if c.toNat < 64 then (sev Γ a).map (fun x : BitVec 64 => x <<< c.toNat) else none
  | .shift .lsr a (.const c) => if c.toNat < 64 then (sev Γ a).map (fun x : BitVec 64 => x >>> c.toNat) else none
  | .shift .lsl a (.var .local z) => do
      let x ← sev Γ a; let c ← Γ.get z
      if c.toNat < 64 then some (x <<< c.toNat) else none
  | .shift .lsr a (.var .local z) => do
      let x ← sev Γ a; let c ← Γ.get z
      if c.toNat < 64 then some (x >>> c.toNat) else none
  | .cmp o a b => do
      let x ← sev Γ a; let y ← sev Γ b
      pure (if Flapjack.Compiler.Encoders.Asm.wordCmpHOL o x y then 1 else 0)
  | _ => none

variable {σ : Type}

theorem sev_sound (Γ : Env) (t : PState σ)
    (hΓ : ∀ x v, Γ.get x = some v → t.locals.lookup x = some (.val (.word v))) :
    ∀ (e : ExpHOL 64) (v : BitVec 64), sev Γ e = some v → EV t e = some (.val (.word v))
  | .const w, v, h => by simp [sev] at h; subst h; exact eval_const t w
  | .var .local x, v, h => by simp only [sev] at h; exact eval_vv t x _ (hΓ x v h)
  | .op .add [a, b], v, h => by
    simp only [sev, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    exact eval_add2 t _ _ _ _ (sev_sound Γ t hΓ a x hx) (sev_sound Γ t hΓ b y hy)
  | .op .sub [a, b], v, h => by
    simp only [sev, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    exact eval_sub2 t _ _ _ _ (sev_sound Γ t hΓ a x hx) (sev_sound Γ t hΓ b y hy)
  | .op .and [a, b], v, h => by
    simp only [sev, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    exact eval_and2' t _ _ _ _ (sev_sound Γ t hΓ a x hx) (sev_sound Γ t hΓ b y hy)
  | .op .or [a, b], v, h => by
    simp only [sev, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    exact eval_or2 t _ _ _ _ (sev_sound Γ t hΓ a x hx) (sev_sound Γ t hΓ b y hy)
  | .op .xor [a, b], v, h => by
    simp only [sev, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    exact eval_xor2 t _ _ _ _ (sev_sound Γ t hΓ a x hx) (sev_sound Γ t hΓ b y hy)
  | .panop .mul [a, b], v, h => by
    simp only [sev, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    exact eval_mul2 t _ _ _ _ (sev_sound Γ t hΓ a x hx) (sev_sound Γ t hΓ b y hy)
  | .shift .lsl a (.const c), v, h => by
    simp only [sev] at h
    split at h
    · rename_i hc
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      exact eval_shl t _ _ _ (sev_sound Γ t hΓ a x hx) hc
    · exact absurd h (by simp)
  | .shift .lsr a (.const c), v, h => by
    simp only [sev] at h
    split at h
    · rename_i hc
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      exact eval_shr t _ _ _ (sev_sound Γ t hΓ a x hx) hc
    · exact absurd h (by simp)
  | .shift .lsl a (.var .local z), v, h => by
    simp only [sev, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, c, hcz, h⟩ := h
    split at h
    · rename_i hc; cases h
      exact eval_shlV t _ _ _ _ (sev_sound Γ t hΓ a x hx) (eval_vv t z _ (hΓ z c hcz)) hc
    · exact absurd h (by simp)
  | .shift .lsr a (.var .local z), v, h => by
    simp only [sev, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨x, hx, c, hcz, h⟩ := h
    split at h
    · rename_i hc; cases h
      exact eval_shrV t _ _ _ _ (sev_sound Γ t hΓ a x hx) (eval_vv t z _ (hΓ z c hcz)) hc
    · exact absurd h (by simp)
  | .cmp o a b, v, h => by
    simp only [sev, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def, Option.some.injEq] at h
    obtain ⟨x, hx, y, hy, rfl⟩ := h
    exact ConsLoop.eval_cmp_of t o _ _ _ _ (sev_sound Γ t hΓ a x hx) (sev_sound Γ t hΓ b y hy)

structure Inv (C : Ctx) (s : AState) (Γ : Env) (M : Mem) (D : List MlS) (t : PState σ) : Prop where
  sr : SR C s t
  env : ∀ x v, Γ.get x = some v → t.locals.lookup x = some (.val (.word v))
  mem : ∀ a v, (a, v) ∈ M → t.memaddrs a ∧ t.memory a = .word v
  decl : ∀ x, x ∈ D → ∃ w, t.locals.lookup x = some (.val (.word w))

theorem inv_ev {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {t : PState σ} (h : Inv C s Γ M D t)
    {e : ExpHOL 64} {v : BitVec 64} (he : sev Γ e = some v) : EV t e = some (.val (.word v)) :=
  sev_sound Γ t h.env e v he

theorem inv_set {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {t : PState σ} (h : Inv C s Γ M D t)
    (x : MlS) (v : BitVec 64) : Inv C s ((x, v) :: Γ) M D (setVarHOLFinite x (.val (.word v)) t) := by
  refine ⟨sr_of_eq h.sr rfl rfl rfl rfl, fun y w hy => ?_, fun a w ha => h.mem a w ha, fun y hy => ?_⟩
  · simp only [Env.get] at hy
    split at hy
    · rename_i e; subst e; simp at hy; subst hy; exact lookup_setVar_same _ _ _
    · rename_i e; rw [lookup_setVar_other _ _ e]; exact h.env y w hy
  · by_cases e : y = x
    · subst e; exact ⟨v, lookup_setVar_same _ _ _⟩
    · rw [lookup_setVar_other _ _ e]; exact h.decl y hy

theorem specR_assignI {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (e : ExpHOL 64) (v : BitVec 64)
    (hx : x ∈ D) (he : sev Γ e = some v) (h : SpecR (Inv C s ((x, v) :: Γ) M D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (.assign .local x e) rest) s m R :=
  specR_pre_assign x e (fun _ => v) (fun t ht => inv_ev ht he) (fun t ht => ht.decl x hx)
    (fun t ht => inv_set ht x v) h

theorem specR_loadI {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (e : ExpHOL 64) (a v : BitVec 64)
    (hx : x ∈ D) (he : sev Γ e = some a) (hm : (a, v) ∈ M) (h : SpecR (Inv C s ((x, v) :: Γ) M D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (.assign .local x (.load .one e)) rest) s m R :=
  specR_pre_assign x (.load .one e) (fun _ => v)
    (fun t ht => by rw [EV, eval_load_word t _ _ (inv_ev ht he) (ht.mem a v hm).1, (ht.mem a v hm).2])
    (fun t ht => ht.decl x hx) (fun t ht => inv_set ht x v) h

theorem specR_returnI {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {a : α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (e : ExpHOL 64) (v : BitVec 64) (he : sev Γ e = some v)
    (hR : ∀ t : PState σ, Inv C s Γ M D t → R a v s (emptyLocalsHOLFinite t)) :
    SpecR (Inv C s Γ M D) (.return e) s (pure a) R :=
  specR_return e (fun _ => v) (fun t ht => inv_ev ht he)
    (fun t ht => by rw [return_state t e v (inv_ev ht he)]; exact hR t ht)

theorem specR_ifI {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {c1 c2 : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (e : ExpHOL 64) (w : BitVec 64) (he : sev Γ e = some w)
    (h1 : w ≠ 0 → SpecR (Inv C s Γ M D) c1 s m R) (h2 : w = 0 → SpecR (Inv C s Γ M D) c2 s m R) :
    SpecR (Inv C s Γ M D) (.ite e c1 c2) s m R := by
  intro t ht
  rw [ite_word t e c1 c2 w (inv_ev ht he)]
  by_cases hw : w ≠ 0
  · rw [if_pos hw]; exact h1 hw t ht
  · rw [if_neg hw]; exact h2 (by simpa using hw) t ht

theorem specR_iteI {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {c1 c2 : ProgHOL 64}
    {b : Bool} {m1 m2 : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (e : ExpHOL 64) (w : BitVec 64)
    (he : sev Γ e = some w) (hb : w ≠ 0 ↔ b = true)
    (h1 : b = true → SpecR (Inv C s Γ M D) c1 s m1 R) (h2 : b = false → SpecR (Inv C s Γ M D) c2 s m2 R) :
    SpecR (Inv C s Γ M D) (.ite e c1 c2) s (if b then m1 else m2) R := by
  refine specR_ifI e w he (fun hw => ?_) (fun hw => ?_)
  · have hb' := hb.mp hw; subst hb'; exact h1 rfl
  · have hb' : b = false := by cases c : b; rfl; exact absurd (hb.mpr c) (by simp [hw])
    subst hb'; exact h2 rfl

theorem specR_hangI {α : Type} {P : PState σ → Prop} {s : AState} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} : SpecR P hang s m R := specR_hang

/-- `x := f(e₁, e₂); rest` against `m >>= k`: the callee's body refines `m` from any entry state that
represents `s` and binds the parameters; afterwards the caller's locals are back (memory facts are
dropped: the callee may have written memory) with `x` bound. -/
theorem specR_call2I {α β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {k : α → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f p1 p2 : MlS) (hne : p1 ≠ p2) (e1 e2 : ExpHOL 64) (B : ProgHOL 64) (v1 v2 : BitVec 64)
    (hx : x ∈ D) (hC : C.code.lookup f = some ([(p1, .one), (p2, .one)], B, .one))
    (he1 : sev Γ e1 = some v1) (he2 : sev Γ e2 = some v2)
    (Rf : α → BitVec 64 → AState → PState σ → Prop) (hRf : ∀ a w s' st, Rf a w s' st → SR C s' st)
    (hB : ∀ u : PState σ, SR C s u → u.locals.lookup p1 = some (.val (.word v1)) →
      u.locals.lookup p2 = some (.val (.word v2)) → SpecR (· = u) B s m Rf)
    (hk : ∀ a w s' (st : PState σ), Rf a w s' st → SpecR (Inv C s' ((x, w) :: Γ) [] D) rest s' (k a) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f [e1, e2]) rest) s (m >>= k) R := by
  intro t ht
  have hc := spec_call2 (P := (· = t)) (s := s) (m := m)
    (Q := fun a s' t' => ∃ w st, Rf a w s' st ∧ Inv C s' ((x, w) :: Γ) [] D t')
    x f p1 p2 hne e1 e2 B (fun _ => v1) (fun _ => v2) (fun u hu => by rw [hu, ht.sr.code]; exact hC)
    (fun u hu => by rw [hu]; exact inv_ev ht he1) (fun u hu => by rw [hu]; exact inv_ev ht he2)
    (fun u hu => by rw [hu]; exact ht.decl x hx) (fun _ => Rf)
    (fun u hu callee h1 h2 => by
      subst hu; exact hB _ (sr_of_eq ht.sr rfl rfl rfl rfl) h1 h2)
    (fun u hu a w s' st hr => by
      subst hu
      refine ⟨w, st, hr, ⟨sr_of_eq (hRf a w s' st hr) rfl rfl rfl rfl, fun y v hy => ?_, fun _ _ h => absurd h (by simp),
        fun y hy => ?_⟩⟩
      · simp only [setKvarHOLFinite, Env.get] at hy ⊢
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact lookup_setVar_same _ _ _
        · rename_i e; rw [lookup_setVar_other _ _ e]; exact ht.env y v hy
      · simp only [setKvarHOLFinite]
        by_cases e : y = x
        · subst e; exact ⟨w, lookup_setVar_same _ _ _⟩
        · rw [lookup_setVar_other _ _ e]; exact ht.decl y hy)
  exact specR_bind (Q1 := fun a s' t' => ∃ w st, Rf a w s' st ∧ Inv C s' ((x, w) :: Γ) [] D t') hc
    (fun a s' u ⟨w, st, hr, hu⟩ => hk a w s' st hr u hu) t rfl

/-! ## The view of an `app` handle -/

theorem specR_viewAppI {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {k : Option (EIdx × EIdx) → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (h : EIdx) (h4 : h.tag = 4)
    (hdh : Γ.get lDh = some (Enc.idxW h)) (hfl : Γ.get lFl = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR)
    (hD : lDt ∈ D ∧ lDg ∈ D ∧ lDi ∈ D ∧ lRp ∈ D ∧ lRn ∈ D)
    (hk : ∀ f a P, SpecR (Inv C s ((lRp, P) :: (lRn, BitVec.ofNat 64 2) :: (lDt, BitVec.ofNat 64 h.tier.toNat) ::
      (lDg, BitVec.ofNat 64 h.tag.toNat) :: (lDi, BitVec.ofNat 64 h.idxNat) :: Γ)
      ((P, Enc.idxW f) :: (P + 8, Enc.idxW a) :: M) D) rest s (k (some (f, a))) R) :
    SpecR (Inv C s Γ M D) (.seq eViewP rest) s (ConRon.Arena.viewApp h >>= k) R := by
  refine specR_bind (Q1 := fun r s' t' => ∃ f a P, r = some (f, a) ∧ s' = s ∧
      Inv C s ((lRp, P) :: (lRn, BitVec.ofNat 64 2) :: (lDt, BitVec.ofNat 64 h.tier.toNat) ::
        (lDg, BitVec.ofNat 64 h.tag.toNat) :: (lDi, BitVec.ofNat 64 h.idxNat) :: Γ)
        ((P, Enc.idxW f) :: (P + 8, Enc.idxW a) :: M) D t')
    (spec_viewApp (C := C) h h4 (fun t ht => ⟨ht.sr, ht.env _ _ hdh, ht.env _ _ hdir, ht.env _ _ hfl,
      ht.decl _ hD.1, ht.decl _ hD.2.1, ht.decl _ hD.2.2.1, ht.decl _ hD.2.2.2.1, ht.decl _ hD.2.2.2.2⟩)
      (fun t ht f a hr => ?_)) ?_
  · obtain ⟨_, hm, hd, hc, hg, _, ⟨P, hrp, hW⟩, hrn, _, hdt, hdg, hdi, hfr⟩ := hr
    have w0 := hW 0 (by simp [Enc.encApp]); have w1 := hW 1 (by simp [Enc.encApp])
    simp only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at w0
    refine ⟨f, a, P, rfl, rfl, sr_of_eq ht.sr hm hd hg hc, fun y v hy => ?_, fun b v hb => ?_, fun y hy => ?_⟩
    · simp only [Env.get] at hy
      split at hy
      · rename_i e; subst e; simp at hy; subst hy; exact hrp
      split at hy
      · rename_i e; subst e; simp at hy; subst hy; exact hrn
      split at hy
      · rename_i e; subst e; simp at hy; subst hy; exact hdt
      split at hy
      · rename_i e; subst e; simp at hy; subst hy; exact hdg
      split at hy
      · rename_i e; subst e; simp at hy; subst hy; exact hdi
      rename_i e1 e2 e3 e4 e5
      rw [hfr y e1 e2 e3 e4 e5]; exact ht.env y v hy
    · simp only [List.mem_cons] at hb
      rcases hb with hb | hb | hb
      · simp only [Prod.mk.injEq] at hb; obtain ⟨rfl, rfl⟩ := hb
        rw [hm, hd]; exact w0
      · simp only [Prod.mk.injEq] at hb; obtain ⟨rfl, rfl⟩ := hb
        rw [hm, hd]; exact w1
      · rw [hm, hd]; exact ht.mem b v hb
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
  · rintro r s' t ⟨f, a, P, rfl, rfl, ht⟩
    exact hk f a P t ht

/-! ## The function prologue -/

/-- The context's locals, as the store code reads them. -/
def ctxLocals : List MlS := [lDir, lFln, lFll, lFls, lFle, lKb]

def ctxEnv (C : Ctx) : Env :=
  [(lDir, C.L.DIR), (lFln, C.FLn), (lFll, C.FLl), (lFls, C.FLs), (lFle, C.FLe), (lKb, C.KB)]

/-- Load the context into its locals, zero the function's other locals, run `core`. -/
def prologue (L : List MlS) (core : ProgHOL 64) : ProgHOL 64 :=
  .dec lKb .one (.var .global gKb) (.dec lFle .one (.var .global gFle) (.dec lFls .one (.var .global gFls)
    (.dec lFll .one (.var .global gFll) (.dec lFln .one (.var .global gFln) (.dec lDir .one (.var .global gDir)
      (decs0 L core))))))

/-- An entry state: `s` represented, the parameters bound as `Γp` lists. -/
def Pre (C : Ctx) (s : AState) (Γ : Env) (u : PState σ) : Prop :=
  SR C s u ∧ ∀ x v, Γ.get x = some v → u.locals.lookup x = some (.val (.word v))

theorem pre_set {C : Ctx} {s : AState} {Γ : Env} {u : PState σ} (h : Pre C s Γ u) (x : MlS) (v : BitVec 64) :
    Pre C s ((x, v) :: Γ) (setVarHOLFinite x (.val (.word v)) u) := by
  refine ⟨sr_of_eq h.1 rfl rfl rfl rfl, fun y w hy => ?_⟩
  simp only [Env.get] at hy
  split at hy
  · rename_i e; subst e; simp at hy; subst hy; exact lookup_setVar_same _ _ _
  · rename_i e; rw [lookup_setVar_other _ _ e]; exact h.2 y w hy

theorem specR_decG {α : Type} {C : Ctx} {s : AState} {Γ : Env} {body : ProgHOL 64} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (x g : MlS) (v : BitVec 64)
    (hg : ∀ u : PState σ, SR C s u → u.globals.lookup g = some (.val (.word v)))
    (hR : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)), R a w s' st → R a w s' { st with locals := L })
    (h : SpecR (Pre C s ((x, v) :: Γ)) body s m R) : SpecR (Pre C s Γ) (.dec x .one (.var .global g) body) s m R :=
  specR_dec x _ body (fun _ => v) (fun u hu => eval_gv u g v (hg u hu.1)) h (fun u hu => pre_set hu x v) hR

theorem specR_prologue {α : Type} {C : Ctx} {s : AState} {Γ : Env} {L : List MlS} {core : ProgHOL 64} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop}
    (hR : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)), R a w s' st → R a w s' { st with locals := L })
    (hL : ∀ x, x ∈ L → (ctxEnv C ++ Γ).get x = none)
    (h : SpecR (Inv C s (ctxEnv C ++ Γ) [] (ctxLocals ++ L)) core s m R) :
    SpecR (Pre C s Γ) (prologue L core) s m R := by
  unfold prologue
  refine specR_decG lKb gKb C.KB (fun u hu => hu.gkb) hR ?_
  refine specR_decG lFle gFle C.FLe (fun u hu => hu.gfle) hR ?_
  refine specR_decG lFls gFls C.FLs (fun u hu => hu.gfls) hR ?_
  refine specR_decG lFll gFll C.FLl (fun u hu => hu.gfll) hR ?_
  refine specR_decG lFln gFln C.FLn (fun u hu => hu.gfln) hR ?_
  refine specR_decG lDir gDir C.L.DIR (fun u hu => hu.gdir) hR ?_
  refine specR_decs0 hR core _ h L _ ?_
  intro u hu t' ⟨m1, d1, g1, c1, fr1, z1⟩
  have henv : ∀ x v, (ctxEnv C ++ Γ).get x = some v → t'.locals.lookup x = some (.val (.word v)) := by
    intro x v hx
    have hxL : x ∉ L := fun hm => by rw [hL x hm] at hx; exact absurd hx (by simp)
    rw [fr1 x hxL]
    exact hu.2 x v hx
  refine ⟨sr_of_eq hu.1 m1 d1 g1 c1, henv, fun _ _ h => absurd h (by simp), fun y hy => ?_⟩
  simp only [List.mem_append] at hy
  rcases hy with hy | hy
  · simp only [ctxLocals, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨C.L.DIR, henv _ _ rfl⟩
    · exact ⟨C.FLn, henv _ _ rfl⟩
    · exact ⟨C.FLl, henv _ _ rfl⟩
    · exact ⟨C.FLs, henv _ _ rfl⟩
    · exact ⟨C.FLe, henv _ _ rfl⟩
    · exact ⟨C.KB, henv _ _ rfl⟩
  · exact ⟨0, z1 y hy⟩

/-! ## The general expression view -/

/-- The words `xs` at `P`, `P + 8`, … as known memory. -/
def wordsAt (P : BitVec 64) (xs : List (BitVec 64)) : Mem :=
  (List.range xs.length).zip xs |>.map fun (j, w) => (P + BitVec.ofNat 64 (8 * j), w)

theorem wordsAt_mem {t : PState σ} {P : BitVec 64} {xs : List (BitVec 64)} (h : Words t P xs) :
    ∀ a v, (a, v) ∈ wordsAt P xs → t.memaddrs a ∧ t.memory a = .word v := by
  intro a v hm
  simp only [wordsAt, List.mem_map, Prod.mk.injEq] at hm
  obtain ⟨⟨j, w⟩, hj, rfl, rfl⟩ := hm
  have hj' := List.mem_iff_getElem.mp hj
  obtain ⟨i, hi, he⟩ := hj'
  simp only [List.length_zip, List.length_range, Nat.min_self] at hi
  simp only [List.getElem_zip, List.getElem_range, Prod.mk.injEq] at he
  obtain ⟨rfl, rfl⟩ := he
  exact h i hi

theorem view_run (h : EIdx) (s : AState) :
    ConRon.Arena.view h s = match s.store.view h with
      | some v => .ok (v, s)
      | none => .error (.internal "arena: dangling expression handle") := by
  show (match s.store.view h with
    | some v => (pure v : AM ENodeView)
    | none => fail (.internal "arena: dangling expression handle")) s = _
  cases s.store.view h <;> rfl

theorem specR_viewI {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {k : ENodeView → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (h : EIdx)
    (hdh : Γ.get lDh = some (Enc.idxW h)) (hfl : Γ.get lFl = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR)
    (hD : lDt ∈ D ∧ lDg ∈ D ∧ lDi ∈ D ∧ lRp ∈ D ∧ lRn ∈ D)
    (hk : ∀ v P, v.tagN = h.tag.toNat → (encEView v).length < 2 ^ 61 → SpecR (Inv C s ((lRp, P) ::
      (lRn, BitVec.ofNat 64 (encEView v).length) :: (lDt, BitVec.ofNat 64 h.tier.toNat) ::
      (lDg, BitVec.ofNat 64 v.tagN) :: (lDi, BitVec.ofNat 64 h.idxNat) :: Γ)
      (wordsAt P (encEView v) ++ M) D) rest s (k v) R) :
    SpecR (Inv C s Γ M D) (.seq eViewP rest) s (ConRon.Arena.view h >>= k) R := by
  intro t ht
  rcases eView_spec t C.L C.FLe s.store ht.sr.rep.e h (ht.env _ _ hdh) (ht.env _ _ hdir) (ht.env _ _ hfl)
      (ht.decl _ hD.1) (ht.decl _ hD.2.1) (ht.decl _ hD.2.2.1) (ht.decl _ hD.2.2.2.1) (ht.decl _ hD.2.2.2.2) with
    hs | ⟨v, hv, htg, hr⟩
  · exact Or.inl (seq_stop t _ _ hs)
  obtain ⟨hn, hm, hd, hc, hg, _, ⟨P, hrp, hW⟩, hrn, hsh, hdt, hdg, hdi, hfr⟩ := hr
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
  rcases hk v P htg hsh _ hInv with hs | ⟨w, hr', a, s', hk', hR⟩
  · exact Or.inl hs
  refine Or.inr ⟨w, hr', a, s', ?_, hR⟩
  show (do let r ← ConRon.Arena.view h s; match r with | (a, s) => k a s) = _
  rw [view_run, hv]; exact hk'

theorem specR_loadI' {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (e : ExpHOL 64) (a a' v : BitVec 64)
    (hx : x ∈ D) (he : sev Γ e = some a) (ha : a = a') (hm : (a', v) ∈ M)
    (h : SpecR (Inv C s ((x, v) :: Γ) M D) rest s m R) :
    SpecR (Inv C s Γ M D) (.seq (.assign .local x (.load .one e)) rest) s m R := by
  subst ha; exact specR_loadI x e a v hx he hm h

theorem wordsAt_mem0 (P a : BitVec 64) (rest : List (BitVec 64)) (M : Mem) :
    (P + BitVec.ofNat 64 0, a) ∈ wordsAt P (a :: rest) ++ M := by
  simp [wordsAt, List.range_succ_eq_map]

theorem wordsAt_mem1 (P a b : BitVec 64) (rest : List (BitVec 64)) (M : Mem) :
    (P + BitVec.ofNat 64 8, b) ∈ wordsAt P (a :: b :: rest) ++ M := by
  simp only [wordsAt, List.mem_append, List.mem_map, Prod.mk.injEq]
  left
  refine ⟨(1, b), ?_, rfl, rfl⟩
  rw [List.mem_iff_getElem]
  exact ⟨1, by simp, by simp⟩

theorem wordsAt_mem2 (P a b c : BitVec 64) (rest : List (BitVec 64)) (M : Mem) :
    (P + BitVec.ofNat 64 16, c) ∈ wordsAt P (a :: b :: c :: rest) ++ M := by
  simp only [wordsAt, List.mem_append, List.mem_map, Prod.mk.injEq]
  left
  refine ⟨(2, c), ?_, rfl, rfl⟩
  rw [List.mem_iff_getElem]
  exact ⟨2, by simp, by simp⟩

/-! ## Small naturals as words -/

theorem nat_add_word (a b : Nat) : BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) :=
  by rw [BitVec.ofNat_add_ofNat]

theorem shr63_eq_zero (c : Nat) (hc : c < 2 ^ 64) : (BitVec.ofNat 64 c >>> (63 : BitVec 64).toNat = 0) ↔ c < 2 ^ 63 := by
  rw [show (63 : BitVec 64).toNat = 63 from rfl]
  constructor
  · intro h; have := congrArg BitVec.toNat h
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow] at this
    rw [Nat.mod_eq_of_lt hc] at this
    simp at this; omega
  · intro h; apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    rw [Nat.mod_eq_of_lt hc]; simp; omega

@[simp] theorem sev_vv (Γ : Env) (x : MlS) : sev Γ (vv x) = Γ.get x := rfl
@[simp] theorem Env.get_cons (Γ : Env) (x y : MlS) (v : BitVec 64) :
    Env.get ((y, v) :: Γ) x = if x = y then some v else Env.get Γ x := rfl

theorem word_add_eq (a b : Nat) (ha : a < 2 ^ 63) (hb : b < 2 ^ 63) :
    BitVec.ofNat 64 a + BitVec.ofNat 64 b = BitVec.ofNat 64 (a + b) := by
  rw [BitVec.ofNat_add_ofNat]

theorem word_add1_eq (a : Nat) : BitVec.ofNat 64 a + 1#64 = BitVec.ofNat 64 (a + 1) := by
  rw [show (1#64) = BitVec.ofNat 64 1 from rfl, BitVec.ofNat_add_ofNat]

/-! ## Forgetting locals, and derived words -/

/-- `Γ` without the entries for `xs` (locals a step clobbers). -/
def Env.kill (Γ : Env) (xs : List MlS) : Env := Γ.filter fun p => !(xs.contains p.1)

theorem Env.get_kill (Γ : Env) (xs : List MlS) (y : MlS) (w : BitVec 64) (h : (Γ.kill xs).get y = some w) :
    y ∉ xs ∧ Γ.get y = some w := by
  induction Γ with
  | nil => simp [Env.kill, Env.get] at h
  | cons p Γ ih =>
    obtain ⟨x, v⟩ := p
    simp only [Env.kill, List.filter_cons] at h
    split at h
    · rename_i hx
      simp only [Env.get] at h
      split at h
      · rename_i e; subst e
        simp at h; subst h
        refine ⟨by simpa using hx, by simp [Env.get]⟩
      · rename_i e
        obtain ⟨h1, h2⟩ := ih h
        exact ⟨h1, by simp [Env.get, e, h2]⟩
    · rename_i hx
      obtain ⟨h1, h2⟩ := ih h
      refine ⟨h1, ?_⟩
      simp only [Env.get]
      split
      · rename_i e; subst e
        exact absurd (by simpa using hx) h1
      · exact h2

theorem derivedE_run (h : EIdx) (s : AState) : ConRon.Arena.derivedE h s = .ok (s.store.derived h, s) := rfl

/-- `storeDerived 9 10; rest` against `derivedE h >>= k`: the derived word lands in `do1`, `do2` is zero;
the decode scratch `dt`, `dg`, `di` is clobbered (dropped from `Γ`, still words). -/
theorem specR_derivedEI {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {k : UInt64 → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (h : EIdx)
    (hdh : Γ.get lDh = some (Enc.idxW h)) (hfl : Γ.get lFl = some C.FLe) (hdir : Γ.get lDir = some C.L.DIR)
    (hD : lDt ∈ D ∧ lDg ∈ D ∧ lDi ∈ D ∧ lDo1 ∈ D ∧ lDo2 ∈ D)
    (hk : SpecR (Inv C s ((lDo1, (s.store.derived h).toBitVec) :: (lDo2, 0) :: Γ.kill [lDt, lDg, lDi]) M D) rest s
      (k (s.store.derived h)) R) :
    SpecR (Inv C s Γ M D) (.seq (storeDerived 9 10) rest) s (ConRon.Arena.derivedE h >>= k) R := by
  intro t ht
  obtain ⟨hn, hm, hd, hc, hg, _, _, o1, o2, fr, wd⟩ := eDerived_spec t C.L C.FLe s.store ht.sr.rep.e h
    (ht.env _ _ hdh) (ht.env _ _ hdir) (ht.env _ _ hfl) (ht.decl _ hD.1) (ht.decl _ hD.2.1) (ht.decl _ hD.2.2.1)
    (ht.decl _ hD.2.2.2.1) (ht.decl _ hD.2.2.2.2)
  have e : evaluateHOLFiniteState t (storeDerived 9 10) = (none, (evaluateHOLFiniteState t (storeDerived 9 10)).2) := by
    rw [← hn]
  rw [seq_normal rest e]
  have hInv : Inv C s ((lDo1, (s.store.derived h).toBitVec) :: (lDo2, 0) :: Γ.kill [lDt, lDg, lDi]) M D
      (evaluateHOLFiniteState t (storeDerived 9 10)).2 := by
    refine ⟨sr_of_eq ht.sr hm hd hg hc, fun y w hy => ?_, fun b w hb => by rw [hm, hd]; exact ht.mem b w hb,
      fun y hy => ?_⟩
    · simp only [Env.get] at hy
      split at hy
      · rename_i e; subst e; simp at hy; subst hy; exact o1
      split at hy
      · rename_i e; subst e; simp at hy; subst hy; exact o2
      rename_i e1 e2
      obtain ⟨hk', hy'⟩ := Env.get_kill Γ _ y w hy
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hk'
      rw [fr y e1 e2 hk'.1 hk'.2.1 hk'.2.2]; exact ht.env y w hy'
    · by_cases e1 : y = lDo1
      · subst e1; exact ⟨_, o1⟩
      by_cases e2 : y = lDo2
      · subst e2; exact ⟨_, o2⟩
      by_cases e3 : y = lDt
      · subst e3; exact wd _ (Or.inl rfl)
      by_cases e4 : y = lDg
      · subst e4; exact wd _ (Or.inr (Or.inl rfl))
      by_cases e5 : y = lDi
      · subst e5; exact wd _ (Or.inr (Or.inr rfl))
      obtain ⟨w, hw⟩ := ht.decl y hy; exact ⟨w, by rw [fr y e1 e2 e3 e4 e5]; exact hw⟩
  rcases hk _ hInv with hs | ⟨w, hr', a, s', hk', hR⟩
  · exact Or.inl hs
  refine Or.inr ⟨w, hr', a, s', ?_, hR⟩
  show (do let r ← ConRon.Arena.derivedE h s; match r with | (a, s) => k a s) = _
  rw [derivedE_run]; exact hk'

/-- `specR_call2I` whose callee spec may use the caller's known memory words. -/
theorem specR_call2IM {α β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {k : α → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f p1 p2 : MlS) (hne : p1 ≠ p2) (e1 e2 : ExpHOL 64) (B : ProgHOL 64) (v1 v2 : BitVec 64)
    (hx : x ∈ D) (hC : C.code.lookup f = some ([(p1, .one), (p2, .one)], B, .one))
    (he1 : sev Γ e1 = some v1) (he2 : sev Γ e2 = some v2)
    (Rf : α → BitVec 64 → AState → PState σ → Prop) (hRf : ∀ a w s' st, Rf a w s' st → SR C s' st)
    (hB : ∀ u : PState σ, SR C s u → (∀ a v, (a, v) ∈ M → u.memaddrs a ∧ u.memory a = .word v) →
      u.locals.lookup p1 = some (.val (.word v1)) →
      u.locals.lookup p2 = some (.val (.word v2)) → SpecR (· = u) B s m Rf)
    (hk : ∀ a w s' (st : PState σ), Rf a w s' st → SpecR (Inv C s' ((x, w) :: Γ) [] D) rest s' (k a) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f [e1, e2]) rest) s (m >>= k) R := by
  intro t ht
  have hc := spec_call2 (P := (· = t)) (s := s) (m := m)
    (Q := fun a s' t' => ∃ w st, Rf a w s' st ∧ Inv C s' ((x, w) :: Γ) [] D t')
    x f p1 p2 hne e1 e2 B (fun _ => v1) (fun _ => v2) (fun u hu => by rw [hu, ht.sr.code]; exact hC)
    (fun u hu => by rw [hu]; exact inv_ev ht he1) (fun u hu => by rw [hu]; exact inv_ev ht he2)
    (fun u hu => by rw [hu]; exact ht.decl x hx) (fun _ => Rf)
    (fun u hu callee h1 h2 => by
      subst hu; exact hB _ (sr_of_eq ht.sr rfl rfl rfl rfl) (fun a v ha => ht.mem a v ha) h1 h2)
    (fun u hu a w s' st hr => by
      subst hu
      refine ⟨w, st, hr, ⟨sr_of_eq (hRf a w s' st hr) rfl rfl rfl rfl, fun y v hy => ?_, fun _ _ h => absurd h (by simp),
        fun y hy => ?_⟩⟩
      · simp only [setKvarHOLFinite, Env.get] at hy ⊢
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact lookup_setVar_same _ _ _
        · rename_i e; rw [lookup_setVar_other _ _ e]; exact ht.env y v hy
      · simp only [setKvarHOLFinite]
        by_cases e : y = x
        · subst e; exact ⟨w, lookup_setVar_same _ _ _⟩
        · rw [lookup_setVar_other _ _ e]; exact ht.decl y hy)
  exact specR_bind (Q1 := fun a s' t' => ∃ w st, Rf a w s' st ∧ Inv C s' ((x, w) :: Γ) [] D t') hc
    (fun a s' u ⟨w, st, hr, hu⟩ => hk a w s' st hr u hu) t rfl

/-- Three parameters, the callee spec seeing the caller's known memory words. -/
theorem specR_call3IM {α β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {k : α → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f p1 p2 p3 : MlS) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3) (e1 e2 e3 : ExpHOL 64) (B : ProgHOL 64)
    (v1 v2 v3 : BitVec 64)
    (hx : x ∈ D) (hC : C.code.lookup f = some ([(p1, .one), (p2, .one), (p3, .one)], B, .one))
    (he1 : sev Γ e1 = some v1) (he2 : sev Γ e2 = some v2) (he3 : sev Γ e3 = some v3)
    (Rf : α → BitVec 64 → AState → PState σ → Prop) (hRf : ∀ a w s' st, Rf a w s' st → SR C s' st)
    (hB : ∀ u : PState σ, SR C s u → (∀ a v, (a, v) ∈ M → u.memaddrs a ∧ u.memory a = .word v) →
      u.locals.lookup p1 = some (.val (.word v1)) → u.locals.lookup p2 = some (.val (.word v2)) →
      u.locals.lookup p3 = some (.val (.word v3)) → SpecR (· = u) B s m Rf)
    (hk : ∀ a w s' (st : PState σ), Rf a w s' st → SpecR (Inv C s' ((x, w) :: Γ) [] D) rest s' (k a) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f [e1, e2, e3]) rest) s (m >>= k) R := by
  intro t ht
  have hc := spec_call3 (P := (· = t)) (s := s) (m := m)
    (Q := fun a s' t' => ∃ w st, Rf a w s' st ∧ Inv C s' ((x, w) :: Γ) [] D t')
    x f p1 p2 p3 h12 h13 h23 e1 e2 e3 B (fun _ => v1) (fun _ => v2) (fun _ => v3)
    (fun u hu => by rw [hu, ht.sr.code]; exact hC)
    (fun u hu => by rw [hu]; exact inv_ev ht he1) (fun u hu => by rw [hu]; exact inv_ev ht he2)
    (fun u hu => by rw [hu]; exact inv_ev ht he3)
    (fun u hu => by rw [hu]; exact ht.decl x hx) (fun _ => Rf)
    (fun u hu callee h1 h2 h3 => by
      subst hu; exact hB _ (sr_of_eq ht.sr rfl rfl rfl rfl) (fun a v ha => ht.mem a v ha) h1 h2 h3)
    (fun u hu a w s' st hr => by
      subst hu
      refine ⟨w, st, hr, ⟨sr_of_eq (hRf a w s' st hr) rfl rfl rfl rfl, fun y v hy => ?_, fun _ _ h => absurd h (by simp),
        fun y hy => ?_⟩⟩
      · simp only [setKvarHOLFinite, Env.get] at hy ⊢
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact lookup_setVar_same _ _ _
        · rename_i e; rw [lookup_setVar_other _ _ e]; exact ht.env y v hy
      · simp only [setKvarHOLFinite]
        by_cases e : y = x
        · subst e; exact ⟨w, lookup_setVar_same _ _ _⟩
        · rw [lookup_setVar_other _ _ e]; exact ht.decl y hy)
  exact specR_bind (Q1 := fun a s' t' => ∃ w st, Rf a w s' st ∧ Inv C s' ((x, w) :: Γ) [] D t') hc
    (fun a s' u ⟨w, st, hr, hu⟩ => hk a w s' st hr u hu) t rfl

/-- Four parameters, the callee spec seeing the caller's known memory words. -/
theorem specR_call4IM {α β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {k : α → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f p1 p2 p3 p4 : MlS) (hnd : [p1, p2, p3, p4].Nodup) (e1 e2 e3 e4 : ExpHOL 64) (B : ProgHOL 64)
    (v1 v2 v3 v4 : BitVec 64)
    (hx : x ∈ D) (hC : C.code.lookup f = some ([(p1, .one), (p2, .one), (p3, .one), (p4, .one)], B, .one))
    (he1 : sev Γ e1 = some v1) (he2 : sev Γ e2 = some v2) (he3 : sev Γ e3 = some v3)
    (he4 : sev Γ e4 = some v4)
    (Rf : α → BitVec 64 → AState → PState σ → Prop) (hRf : ∀ a w s' st, Rf a w s' st → SR C s' st)
    (hB : ∀ u : PState σ, SR C s u → (∀ a v, (a, v) ∈ M → u.memaddrs a ∧ u.memory a = .word v) →
      u.locals.lookup p1 = some (.val (.word v1)) → u.locals.lookup p2 = some (.val (.word v2)) →
      u.locals.lookup p3 = some (.val (.word v3)) → u.locals.lookup p4 = some (.val (.word v4)) →
      SpecR (· = u) B s m Rf)
    (hk : ∀ a w s' (st : PState σ), Rf a w s' st → SpecR (Inv C s' ((x, w) :: Γ) [] D) rest s' (k a) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f [e1, e2, e3, e4]) rest) s (m >>= k) R := by
  intro t ht
  have hc := spec_call4 (P := (· = t)) (s := s) (m := m)
    (Q := fun a s' t' => ∃ w st, Rf a w s' st ∧ Inv C s' ((x, w) :: Γ) [] D t')
    x f p1 p2 p3 p4 hnd e1 e2 e3 e4 B (fun _ => v1) (fun _ => v2) (fun _ => v3) (fun _ => v4)
    (fun u hu => by rw [hu, ht.sr.code]; exact hC)
    (fun u hu => by rw [hu]; exact inv_ev ht he1) (fun u hu => by rw [hu]; exact inv_ev ht he2)
    (fun u hu => by rw [hu]; exact inv_ev ht he3) (fun u hu => by rw [hu]; exact inv_ev ht he4)
    (fun u hu => by rw [hu]; exact ht.decl x hx) (fun _ => Rf)
    (fun u hu callee h1 h2 h3 h4 => by
      subst hu; exact hB _ (sr_of_eq ht.sr rfl rfl rfl rfl) (fun a v ha => ht.mem a v ha) h1 h2 h3 h4)
    (fun u hu a w s' st hr => by
      subst hu
      refine ⟨w, st, hr, ⟨sr_of_eq (hRf a w s' st hr) rfl rfl rfl rfl, fun y v hy => ?_, fun _ _ h => absurd h (by simp),
        fun y hy => ?_⟩⟩
      · simp only [setKvarHOLFinite, Env.get] at hy ⊢
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact lookup_setVar_same _ _ _
        · rename_i e; rw [lookup_setVar_other _ _ e]; exact ht.env y v hy
      · simp only [setKvarHOLFinite]
        by_cases e : y = x
        · subst e; exact ⟨w, lookup_setVar_same _ _ _⟩
        · rw [lookup_setVar_other _ _ e]; exact ht.decl y hy)
  exact specR_bind (Q1 := fun a s' t' => ∃ w st, Rf a w s' st ∧ Inv C s' ((x, w) :: Γ) [] D t') hc
    (fun a s' u ⟨w, st, hr, hu⟩ => hk a w s' st hr u hu) t rfl

theorem specR_call5IM {α β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {k : α → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f p1 p2 p3 p4 p5 : MlS) (hnd : [p1, p2, p3, p4, p5].Nodup) (e1 e2 e3 e4 e5 : ExpHOL 64) (B : ProgHOL 64)
    (v1 v2 v3 v4 v5 : BitVec 64)
    (hx : x ∈ D) (hC : C.code.lookup f = some ([(p1, .one), (p2, .one), (p3, .one), (p4, .one), (p5, .one)], B, .one))
    (he1 : sev Γ e1 = some v1) (he2 : sev Γ e2 = some v2) (he3 : sev Γ e3 = some v3)
    (he4 : sev Γ e4 = some v4) (he5 : sev Γ e5 = some v5)
    (Rf : α → BitVec 64 → AState → PState σ → Prop) (hRf : ∀ a w s' st, Rf a w s' st → SR C s' st)
    (hB : ∀ u : PState σ, SR C s u → (∀ a v, (a, v) ∈ M → u.memaddrs a ∧ u.memory a = .word v) →
      u.locals.lookup p1 = some (.val (.word v1)) → u.locals.lookup p2 = some (.val (.word v2)) →
      u.locals.lookup p3 = some (.val (.word v3)) → u.locals.lookup p4 = some (.val (.word v4)) →
      u.locals.lookup p5 = some (.val (.word v5)) → SpecR (· = u) B s m Rf)
    (hk : ∀ a w s' (st : PState σ), Rf a w s' st → SpecR (Inv C s' ((x, w) :: Γ) [] D) rest s' (k a) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f [e1, e2, e3, e4, e5]) rest) s (m >>= k) R := by
  intro t ht
  have hc := spec_call5 (P := (· = t)) (s := s) (m := m)
    (Q := fun a s' t' => ∃ w st, Rf a w s' st ∧ Inv C s' ((x, w) :: Γ) [] D t')
    x f p1 p2 p3 p4 p5 hnd e1 e2 e3 e4 e5 B (fun _ => v1) (fun _ => v2) (fun _ => v3) (fun _ => v4) (fun _ => v5)
    (fun u hu => by rw [hu, ht.sr.code]; exact hC)
    (fun u hu => by rw [hu]; exact inv_ev ht he1) (fun u hu => by rw [hu]; exact inv_ev ht he2)
    (fun u hu => by rw [hu]; exact inv_ev ht he3) (fun u hu => by rw [hu]; exact inv_ev ht he4)
    (fun u hu => by rw [hu]; exact inv_ev ht he5)
    (fun u hu => by rw [hu]; exact ht.decl x hx) (fun _ => Rf)
    (fun u hu callee h1 h2 h3 h4 h5 => by
      subst hu; exact hB _ (sr_of_eq ht.sr rfl rfl rfl rfl) (fun a v ha => ht.mem a v ha) h1 h2 h3 h4 h5)
    (fun u hu a w s' st hr => by
      subst hu
      refine ⟨w, st, hr, ⟨sr_of_eq (hRf a w s' st hr) rfl rfl rfl rfl, fun y v hy => ?_, fun _ _ h => absurd h (by simp),
        fun y hy => ?_⟩⟩
      · simp only [setKvarHOLFinite, Env.get] at hy ⊢
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact lookup_setVar_same _ _ _
        · rename_i e; rw [lookup_setVar_other _ _ e]; exact ht.env y v hy
      · simp only [setKvarHOLFinite]
        by_cases e : y = x
        · subst e; exact ⟨w, lookup_setVar_same _ _ _⟩
        · rw [lookup_setVar_other _ _ e]; exact ht.decl y hy)
  exact specR_bind (Q1 := fun a s' t' => ∃ w st, Rf a w s' st ∧ Inv C s' ((x, w) :: Γ) [] D t') hc
    (fun a s' u ⟨w, st, hr, hu⟩ => hk a w s' st hr u hu) t rfl

end ConPanqueque.T
