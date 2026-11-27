import ConPanqueque.Pipeline.IndExt.ResOps
import ConPanqueque.Pipeline.Ext
import ConLeche.Model.Inductives.RunEnv

/-! # The positivity walk's readers at an extension

The walk reads the environment through its context's `find?` (`nestContainer`, `nestInstType`,
`familyKeyCheck`) and the checker's operations.  At an extension `EnvExt A₁ A₂` whose stored
inductives' constructor lists read alike (`CtorsAgree`), a reader that accepts at `A₁` (context
`ctx₁`, `ctx₁.find? = A₁.find?`) accepts alike at `A₂` (the same context at `A₂.find?`), on terms
that resolve at `A₁`. -/

namespace ConPanqueque.Pipeline.IndExt

open ConLeche ConLeche.Verify ConPanqueque.Pipeline

set_option autoImplicit false

variable {A₁ A₂ : Env}

/-- Close a goal whose hypothesis `h` is a thrown error equated to a success. -/
macro "kill " h:ident : tactic =>
  `(tactic| simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, unwrapOr] at $h:ident)

/-- The constructor names a stored inductive of `A₁` lists read alike at `A₂`. -/
def CtorsAgree (A₁ A₂ : Env) : Prop :=
  ∀ I cv caps, A₁.find? I = some (.indInfo cv caps) → ∀ n ∈ caps.ctors, A₂.find? n = A₁.find? n

/-! ## The operations -/

theorem whnf_rel (hx : EnvExt A₁ A₂) (F d : Nat) {e : Expr} (he : Res A₁ e) :
    (fueledOps .verified F).whnf A₂ d e = (fueledOps .verified F).whnf A₁ d e ∧
      ∀ y, (fueledOps .verified F).whnf A₁ d e = .ok y → Res A₁ y :=
  ⟨ops_whnf hx F d he, ((knot_ext .verified hx F false).whnf d he).2⟩

theorem okBind {ε α β : Type} {m₁ m₂ : Except ε α} {k₁ k₂ : α → Except ε β} {r : β}
    (h : (m₁ >>= k₁) = .ok r) (hm : ∀ y, m₁ = .ok y → m₂ = .ok y)
    (hk : ∀ y, m₁ = .ok y → k₁ y = .ok r → k₂ y = .ok r) : (m₂ >>= k₂) = .ok r := by
  obtain ⟨y, hy, hr⟩ := exceptBind_ok h
  rw [hm y hy]
  exact hk y hy hr

/-! ## Telescopes -/

theorem res_whnfTele (hx : EnvExt A₁ A₂) (F : Nat) :
    ∀ (n i : Nat) {e : Expr} {bs : List Expr} {s : Level}, Res A₁ e →
      whnfTelescope (m := CheckM) (fueledOps .verified F) A₁ i n e = .ok (bs, s) → ResL A₁ bs
  | 0, i, e, bs, s, he, h => by
    unfold whnfTelescope at h
    obtain ⟨w, -, h⟩ := exceptBind_ok h
    split at h
    · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      exact fun _ hx => nomatch hx
    · simp [throw, throwThe, MonadExceptOf.throw] at h
  | n + 1, i, e, bs, s, he, h => by
    unfold whnfTelescope at h
    obtain ⟨w, hw, h⟩ := exceptBind_ok h
    have hrw := (whnf_rel hx F i he).2 w hw
    split at h
    · rename_i dom body
      obtain ⟨⟨bs', s'⟩, hrec, h⟩ := exceptBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, -⟩ := h
      have hd := (res_forall.mp hrw).1
      have ih := res_whnfTele hx F n (i + 1) (res_open hd (res_forall.mp hrw).2) hrec
      intro x hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hd
      · exact ih x hm
    · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem res_familyTelescope (hx : EnvExt A₁ A₂) (F : Nat) {cv : ConstantVal} {caps : IndCaps} {t : Expr}
    (hr : Res A₁ cv.type) (h : familyTelescope (m := CheckM) (fueledOps .verified F) A₁ cv caps = .ok t) :
    Res A₁ t := by
  unfold familyTelescope at h
  split at h
  · obtain ⟨cvR, hR, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    unfold reducedFormer at hR
    obtain ⟨⟨bs, s⟩, hw, hR⟩ := exceptBind_ok hR
    simp only [pure, Except.pure, Except.ok.injEq] at hR; subst hR
    exact res_closeTelescope bs 0 (res_whnfTele hx F _ 0 hr hw) res_sort
  · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact hr

/-! ## The context's lookups -/

theorem filterMap_congr' {α β : Type} {f g : α → Option β} : ∀ {l : List α}, (∀ x ∈ l, f x = g x) →
    l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: l, h => by
    simp only [List.filterMap_cons, h a (List.mem_cons_self ..),
      filterMap_congr' (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem nestContainer_ext (hc : CtorsAgree A₁ A₂) (hx : EnvExt A₁ A₂) {ctx : NestCtx} (hf : ctx.find? = A₁.find?)
    {C : Name} {q : Nat × List (ConstantVal × Nat)} (h : nestContainer ctx C = some q) :
    nestContainer { ctx with find? := A₂.find? } C = some q := by
  unfold nestContainer at h ⊢
  rw [hf] at h
  split at h
  · rename_i cv caps hI
    simp only
    rw [hx.find _ _ hI]
    simp only
    have hcs : caps.ctors.filterMap (fun n => (A₂.find? n).bind (nestCtorEntry C)) =
        caps.ctors.filterMap (fun n => (A₁.find? n).bind (nestCtorEntry C)) :=
      filterMap_congr' (fun n hn => by rw [hc C cv caps hI n hn])
    rw [hcs]
    exact h
  · cases h

/-- The constructors `nestContainer` lists are stored constructors. -/
theorem nestContainer_stored {ctx : NestCtx} {C : Name} {q : Nat × List (ConstantVal × Nat)}
    (h : nestContainer ctx C = some q) :
    ∀ c ∈ q.2, ∃ n ci, ctx.find? n = some ci ∧ ci.toConstantVal = c.1 := by
  unfold nestContainer at h
  split at h
  · rename_i cv caps hI
    generalize hcs : caps.ctors.filterMap (fun n => (ctx.find? n).bind (nestCtorEntry C)) = cs at h
    have hmem : ∀ x ∈ cs, ∃ n ci, ctx.find? n = some ci ∧ ci.toConstantVal = x.1 := by
      intro x hx
      rw [← hcs] at hx
      obtain ⟨n, -, hn⟩ := List.mem_filterMap.mp hx
      cases hfn : ctx.find? n with
      | none => rw [hfn] at hn; cases hn
      | some ci =>
        rw [hfn] at hn
        simp only [Option.bind_some] at hn
        refine ⟨n, ci, hfn, ?_⟩
        unfold nestCtorEntry at hn
        split at hn
        · rename_i cv' nPc nF T
          split at hn
          · split at hn
            · split at hn
              · simp only [Option.some.injEq] at hn; subst hn; rfl
              · cases hn
            · cases hn
          · cases hn
        · cases hn
    dsimp only at h
    cases cs with
    | nil => simp only [Option.some.injEq] at h; subst h; intro c hc; exact nomatch hc
    | cons x tl =>
      obtain ⟨c0, nPc, nF⟩ := x
      simp only [Option.some.injEq] at h; subst h
      intro c hcm
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hcm
      exact hmem x hx
  · cases h

/-! ## A family at a key -/

theorem checkSpineAt_ext (hx : EnvExt A₁ A₂) (F d : Nat) :
    ∀ (t : Expr) (as : List Expr), Res A₁ t → ResL A₁ as →
      checkSpineAt (m := CheckM) (fueledOps .verified F) A₁ d t as = .ok () →
      checkSpineAt (m := CheckM) (fueledOps .verified F) A₂ d t as = .ok ()
  | _, [], _, _, _ => rfl
  | t, a :: as, ht, has, h => by
    unfold checkSpineAt at h ⊢
    split at h
    · rename_i ty body
      have ha := has a (List.mem_cons_self ..)
      refine okBind h (fun y hy => by rw [(ops_infer hx F d ha).1]; exact hy) (fun ta hta h => ?_)
      have hrta := (ops_infer hx F d ha).2 ta hta
      have hty := (res_forall.mp ht).1
      refine okBind h (fun y hy => by rw [ops_defeq hx F d hrta hty]; exact hy) (fun b hb h => ?_)
      split at h
      · rename_i hb'
        simp only [hb', bind, Except.bind] at h ⊢
        exact checkSpineAt_ext hx F d _ as (res_instantiate1 ha body 0 (res_forall.mp ht).2)
          (fun x hm => has x (List.mem_cons_of_mem _ hm)) h
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem familyKeyCheck_ext (hx : EnvExt A₁ A₂) (F d : Nat) (c : Name) (us : List Level) {ds : List Expr}
    (hds : ResL A₁ ds)
    (h : familyKeyCheck (m := CheckM) (fueledOps .verified F) A₁ A₁.find? d c us ds = .ok ()) :
    familyKeyCheck (m := CheckM) (fueledOps .verified F) A₂ A₂.find? d c us ds = .ok () := by
  unfold familyKeyCheck at h ⊢
  split at h
  · rename_i cv caps hI
    rw [hx.find _ _ hI]
    simp only
    have hrt : Res A₁ cv.type := hx.facts.type hI
    by_cases hlen : us.length = cv.levelParams.length
    · simp only [hlen, ↓reduceIte] at h ⊢
      try dsimp only at h ⊢
      refine okBind h (fun y hy => by rw [ConLeche.Model.familyTelescope_ext hx F caps hrt]; exact hy) (fun ty hty h => ?_)
      exact checkSpineAt_ext hx F d _ ds (res_inst _ _ (res_familyTelescope hx F hrt hty)) hds h
    · simp [hlen, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem familyKeyChecks_ext (hx : EnvExt A₁ A₂) (F d : Nat) (us : List Level) {ds : List Expr}
    (hds : ResL A₁ ds) : ∀ (cs : List Name),
      familyKeyChecks (m := CheckM) (fueledOps .verified F) A₁ A₁.find? d us ds cs = .ok () →
      familyKeyChecks (m := CheckM) (fueledOps .verified F) A₂ A₂.find? d us ds cs = .ok ()
  | [], _ => rfl
  | c :: cs, h => by
    unfold familyKeyChecks at h ⊢
    exact okBind h (fun y hy => by cases y; exact familyKeyCheck_ext hx F d c us hds hy)
      (fun _ _ h => familyKeyChecks_ext hx F d us hds cs h)

end ConPanqueque.Pipeline.IndExt

namespace ConPanqueque.Pipeline.IndExt

open ConLeche ConLeche.Verify ConPanqueque.Pipeline

variable {A₁ A₂ : Env}

theorem nestInstType_res (hx : EnvExt A₁ A₂) (F : Nat) {ctx : NestCtx} (hf : ctx.find? = A₁.find?)
    (hi : Nat) (key : NestKey) (hds : ResL A₁ key.ds) {r : Nat × Expr}
    (h : nestInstType (m := CheckM) ctx (fueledOps .verified F) A₁ hi key = .ok r) : Res A₁ r.2 := by
  unfold nestInstType at h
  rw [hf] at h
  cases hI : A₁.find? key.cname with
  | none => simp [hI, unwrapOr, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  | some ci =>
    cases ci with
    | indInfo cv caps =>
      have hrt : Res A₁ cv.type := hx.facts.type hI
      simp only [hI, unwrapOr, pure_bind] at h
      split at h
      · obtain ⟨tyC, ht, h⟩ := exceptBind_ok h
        have hrC := res_familyTelescope hx F hrt ht
        split at h
        · obtain ⟨ty, hp, h⟩ := exceptBind_ok h
          have hp' : instPisWith key.ds (tyC.instantiateLevelParams cv.levelParams key.lvls) = some ty := by
            cases hq : instPisWith key.ds (tyC.instantiateLevelParams cv.levelParams key.lvls) with
            | none => simp [hq, throw, throwThe, MonadExceptOf.throw] at hp
            | some y => simp only [hq, pure, Except.pure, Except.ok.injEq] at hp; rw [hp]
          have hrty := res_instPisWith _ hds (res_inst _ _ hrC) hp'
          obtain ⟨s, -, h⟩ := exceptBind_ok h
          split at h
          · kill h
          · obtain ⟨b, -, h⟩ := exceptBind_ok h
            split at h
            · simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; exact hrty
            · kill h
        · kill h
      · kill h
    | _ => simp [hI, unwrapOr, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

theorem nestInstType_eq (hx : EnvExt A₁ A₂) (F : Nat) {ctx : NestCtx} (hf : ctx.find? = A₁.find?)
    (hi : Nat) (key : NestKey) {r : Nat × Expr}
    (h : nestInstType (m := CheckM) ctx (fueledOps .verified F) A₁ hi key = .ok r) :
    nestInstType (m := CheckM) { ctx with find? := A₂.find? } (fueledOps .verified F) A₂ hi key = .ok r := by
  unfold nestInstType at h ⊢
  rw [hf] at h
  dsimp only
  cases hI : A₁.find? key.cname with
  | none => simp [hI, unwrapOr, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  | some ci =>
    cases ci with
    | indInfo cv caps =>
      have hrt : Res A₁ cv.type := hx.facts.type hI
      simp only [hI, hx.find _ _ hI, unwrapOr, pure_bind] at h ⊢
      rw [ConLeche.Model.familyTelescope_ext hx F caps hrt]
      exact h
    | _ => simp [hI, unwrapOr, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

end ConPanqueque.Pipeline.IndExt
