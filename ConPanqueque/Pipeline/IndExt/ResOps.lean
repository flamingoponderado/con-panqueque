import ConPanqueque.Pipeline.IndExt.InferRes
import ConLeche.Kernel.Inductives.Positivity
import ConLeche.Kernel.Inductives.FieldTele

/-! # Resolution under the inductive checker's term operations

The positivity walk and the recursor stage build terms by telescope closing, Π instantiation,
whole-application and free-variable replacement.  Each keeps resolution, given resolving pieces. -/

namespace ConPanqueque.Pipeline.IndExt

open ConLeche ConLeche.Verify

set_option autoImplicit false

variable {env : Env}

theorem res_closeTelescope : ∀ (bs : List Expr) (i : Nat) {body : Expr},
    (∀ b ∈ bs, Res env b) → Res env body → Res env (closeTelescope bs i body)
  | [], _, _, _, hb => hb
  | d :: bs, i, body, hbs, hb => by
    simp only [closeTelescope]
    exact res_forall.mpr ⟨hbs d (List.mem_cons_self ..),
      res_abstract1 i _ 0 (res_closeTelescope bs (i + 1) (fun b h => hbs b (List.mem_cons_of_mem _ h)) hb)⟩

theorem res_instPisWith : ∀ (as : List Expr) {e r : Expr},
    (∀ a ∈ as, Res env a) → Res env e → instPisWith as e = some r → Res env r
  | [], e, r, _, he, h => by simp only [instPisWith, Option.some.injEq] at h; subst h; exact he
  | a :: as, e, r, has, he, h => by
    cases e with
    | forallE t b =>
      simp only [instPisWith] at h
      exact res_instPisWith as (fun x hx => has x (List.mem_cons_of_mem _ hx))
        (res_instantiate1 (has a (List.mem_cons_self ..)) b 0 (res_forall.mp he).2) h
    | _ => simp [instPisWith] at h

theorem res_replaceFVars {f : Nat → Option Expr} (hf : ∀ i x, f i = some x → Res env x) :
    ∀ (e : Expr), Res env e → Res env (e.replaceFVars f)
  | .bvar _, _ => rfl
  | .sort _, _ => rfl
  | .const _ _, h => h
  | .lit _, h => h
  | .fvar i ty, h => by
    simp only [Expr.replaceFVars]
    cases hi : f i with
    | none => exact h
    | some x => exact hf i x hi
  | .app a b, h => res_app.mpr ⟨res_replaceFVars hf a (res_app.mp h).1, res_replaceFVars hf b (res_app.mp h).2⟩
  | .lam t b, h => res_lam.mpr ⟨res_replaceFVars hf t (res_lam.mp h).1, res_replaceFVars hf b (res_lam.mp h).2⟩
  | .forallE t b, h =>
    res_forall.mpr ⟨res_replaceFVars hf t (res_forall.mp h).1, res_replaceFVars hf b (res_forall.mp h).2⟩
  | .letE t v b, h => res_let.mpr ⟨res_replaceFVars hf t (res_let.mp h).1,
      res_replaceFVars hf v (res_let.mp h).2.1, res_replaceFVars hf b (res_let.mp h).2.2⟩
  | .proj s i x, h => res_proj.mpr ⟨(res_proj.mp h).1, res_replaceFVars hf x (res_proj.mp h).2⟩

theorem res_appHole {f : Name → List Level → Option Expr} (hf : ∀ c us x, f c us = some x → Res env x)
    {b n : Nat} {e x : Expr} (h : e.appHole? f b n = some x) : Res env x := by
  unfold Expr.appHole? at h
  cases hp : e.phApp? b n with
  | none => rw [hp] at h; cases h
  | some p => rw [hp] at h; exact hf _ _ _ h

theorem res_replaceApps {f : Name → List Level → Option Expr} (hf : ∀ c us x, f c us = some x → Res env x)
    (b n : Nat) : ∀ (e : Expr), Res env e → Res env (e.replaceApps f b n)
  | .bvar _, _ => rfl
  | .sort _, _ => rfl
  | .lit _, h => h
  | .fvar _ _, h => h
  | .const c us, h => by
    simp only [Expr.replaceApps]
    cases hx : (Expr.const c us).appHole? f b n with
    | none => exact h
    | some x => exact res_appHole hf hx
  | .app a x, h => by
    simp only [Expr.replaceApps]
    cases hx : (Expr.app a x).appHole? f b n with
    | none => exact res_app.mpr ⟨res_replaceApps hf b n a (res_app.mp h).1, res_replaceApps hf b n x (res_app.mp h).2⟩
    | some y => exact res_appHole hf hx
  | .lam t c, h => res_lam.mpr ⟨res_replaceApps hf b n t (res_lam.mp h).1, res_replaceApps hf b n c (res_lam.mp h).2⟩
  | .forallE t c, h =>
    res_forall.mpr ⟨res_replaceApps hf b n t (res_forall.mp h).1, res_replaceApps hf b n c (res_forall.mp h).2⟩
  | .letE t v c, h => res_let.mpr ⟨res_replaceApps hf b n t (res_let.mp h).1,
      res_replaceApps hf b n v (res_let.mp h).2.1, res_replaceApps hf b n c (res_let.mp h).2.2⟩
  | .proj s i x, h => res_proj.mpr ⟨(res_proj.mp h).1, res_replaceApps hf b n x (res_proj.mp h).2⟩

theorem res_nestPhs (n : Nat) : ∀ x ∈ nestPhs n, Res env x := by
  intro x hx
  simp only [nestPhs, List.mem_map] at hx
  obtain ⟨i, -, rfl⟩ := hx
  exact res_fvar.mpr res_sort

theorem res_nestCanonSub (names : List Name) (us : List Level) (n : Nat) :
    ∀ c vs x, nestCanonSub names us n c vs = some x → Res env x := by
  intro c vs x h
  simp only [nestCanonSub] at h
  split at h
  · cases hm : names.findIdx? (· == c) with
    | none => rw [hm] at h; cases h
    | some m => rw [hm] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h; exact res_fvar.mpr res_sort
  · cases h

theorem res_nestCanonCrest {names : List Name} {us : List Level} {n : Nat} {cty r : Expr} (hc : Res env cty)
    (h : nestCanonCrest names us n cty = some r) : Res env r := by
  unfold nestCanonCrest at h
  cases hi : instPisWith (nestPhs n) cty with
  | none => rw [hi] at h; cases h
  | some y =>
    rw [hi] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
    exact res_replaceApps (res_nestCanonSub names us n) 0 n y (res_instPisWith _ (res_nestPhs n) hc hi)

theorem res_nestKeyMap {ds holes : List Expr} (hd : ∀ x ∈ ds, Res env x) (hh : ∀ x ∈ holes, Res env x) :
    ∀ i x, nestKeyMap ds holes i = some x → Res env x := by
  intro i x h
  simp only [nestKeyMap] at h
  split at h
  · exact hd x (List.mem_of_getElem? h)
  · exact hh x (List.mem_of_getElem? h)

theorem res_nestCrest {names : List Name} {us : List Level} {ds holes : List Expr} {cty r : Expr}
    (hd : ∀ x ∈ ds, Res env x) (hh : ∀ x ∈ holes, Res env x) (hc : Res env cty)
    (h : nestCrest names us ds holes cty = some r) : Res env r := by
  unfold nestCrest at h
  cases hi : nestCanonCrest names us ds.length cty with
  | none => rw [hi] at h; cases h
  | some y =>
    rw [hi] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
    exact res_replaceFVars (res_nestKeyMap hd hh) y (res_nestCanonCrest hc hi)

theorem res_piBinders : ∀ {e : Expr}, Res env e → (∀ b ∈ e.piBinders.1, Res env b) ∧ Res env e.piBinders.2
  | .forallE t b, h => by
    have ih := res_piBinders (res_forall.mp h).2
    simp only [Expr.piBinders]
    refine ⟨fun x hx => ?_, ih.2⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact (res_forall.mp h).1
    · exact ih.1 x hx
  | .bvar _, h | .sort _, h | .const _ _, h | .lit _, h | .fvar _ _, h | .app _ _, h | .lam _ _, h
  | .letE _ _ _, h | .proj _ _ _, h => by simp only [Expr.piBinders]; exact ⟨(fun _ hx => nomatch hx), h⟩

theorem res_stripPis : ∀ (k : Nat) {e : Expr} {bs : List Expr} {r : Expr}, Res env e →
    e.stripPis k = some (bs, r) → (∀ b ∈ bs, Res env b) ∧ Res env r
  | 0, e, bs, r, he, h => by
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; exact ⟨(fun _ hx => nomatch hx), he⟩
  | k + 1, e, bs, r, he, h => by
    cases e with
    | forallE t b =>
      simp only [Expr.stripPis] at h
      cases hs : b.stripPis k with
      | none => rw [hs] at h; cases h
      | some q =>
        rw [hs] at h
        simp only [Option.map_some, Option.some.injEq] at h
        obtain ⟨q1, q2⟩ := q
        simp only [Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have ih := res_stripPis k (res_forall.mp he).2 hs
        refine ⟨fun x hx => ?_, ih.2⟩
        rcases List.mem_cons.mp hx with rfl | hx
        · exact (res_forall.mp he).1
        · exact ih.1 x hx
    | _ => simp [Expr.stripPis] at h

/-- Lists of resolving terms. -/
def ResL (env : Env) (xs : List Expr) : Prop := ∀ x ∈ xs, Res env x

theorem res_take {xs : List Expr} (h : ResL env xs) (n : Nat) : ResL env (xs.take n) :=
  fun x hx => h x (List.mem_of_mem_take hx)

theorem res_drop {xs : List Expr} (h : ResL env xs) (n : Nat) : ResL env (xs.drop n) :=
  fun x hx => h x (List.mem_of_mem_drop hx)

end ConPanqueque.Pipeline.IndExt
