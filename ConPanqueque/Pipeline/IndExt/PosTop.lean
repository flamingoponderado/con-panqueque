import ConPanqueque.Pipeline.IndExt.PosWalk
import ConPanqueque.Pipeline.IndExt.Ctors

/-! # The block's positivity check and the seeds' walk at an extension -/

namespace ConPanqueque.Pipeline.IndExt

open ConLeche ConLeche.Verify ConPanqueque.Pipeline

set_option autoImplicit false

variable {A₁ A₂ : Env}

theorem mapM_some_mem {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {r : List β}, l.mapM f = some r → ∀ x ∈ r, ∃ a ∈ l, f a = some x
  | [], r, h, x, hx => by simp at h; subst h; exact nomatch hx
  | a :: l, r, h, x, hx => by
    rw [List.mapM_cons] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hl : l.mapM f with
      | none => simp [ha, hl] at h
      | some rs =>
        simp only [ha, hl, Option.bind_eq_bind, Option.bind_some, Option.pure_def, Option.some.injEq] at h
        subst h
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨a, List.mem_cons_self .., ha⟩
        · obtain ⟨a', ha', hf⟩ := mapM_some_mem hl x hx
          exact ⟨a', List.mem_cons_of_mem _ ha', hf⟩

/-- The member holes resolve where the formers and the parameters do. -/
theorem res_nestHoles {ctx : NestCtx} {holes : List Expr} (hp : ResL A₁ ctx.params)
    (hfm : ∀ cv ∈ ctx.formers, Res A₁ cv.type) (h : nestHoles ctx = some holes) : ResL A₁ holes := by
  unfold nestHoles at h
  intro x hxm
  obtain ⟨mm, -, hf⟩ := mapM_some_mem h x hxm
  split at hf
  · rename_i cv hcv
    cases hi : instPisWith ctx.params cv.type with
    | none => rw [hi] at hf; cases hf
    | some y =>
      rw [hi] at hf; simp only [Option.map_some, Option.some.injEq] at hf; subst hf
      exact res_fvar.mpr (res_instPisWith _ hp (hfm cv (List.mem_of_getElem? hcv)) hi)
  · cases hf

theorem blockNestCtx_atF (p : BlockShape) (g : Name → Option ConstantInfo) {ctx : NestCtx} {holes : List Expr}
    {f : Name → Option ConstantInfo}
    (h : blockNestCtx (m := CheckM) p f = .ok (ctx, holes)) :
    blockNestCtx (m := CheckM) p g = .ok (atF ctx g, holes) ∧ ctx.find? = f ∧
      ctx.formers = p.formers ∧ (∃ cvTa0 rest, p.formers = cvTa0 :: rest ∧
        ∃ b, openPisAtFvars p.nP cvTa0.type 0 = some (ctx.params, b)) ∧ nestHoles ctx = some holes := by
  unfold blockNestCtx at h ⊢
  cases hh : p.formers with
  | nil => simp [hh] at h; kill h
  | cons cvTa0 rest =>
    simp only [hh, List.head?_cons, unwrapOr, pure_bind] at h ⊢
    cases ho : openPisAtFvars p.nP cvTa0.type 0 with
    | none => simp [ho] at h; kill h
    | some pq =>
      simp only [ho, pure_bind] at h ⊢
      cases hn : nestHoles (p.nestCtx pq.1 f) with
      | none => simp [hn, throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map] at h
      | some hs =>
        have hn' : nestHoles (p.nestCtx pq.1 g) = some hs := by rw [← hn]; rfl
        simp only [hn, hn', pure_bind, pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h ⊢
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨rfl, rfl, hh, ⟨cvTa0, rest, rfl, pq.2, by rw [ho]; rfl⟩, hn⟩

theorem checkAbsCtorSorts_ext (hx : EnvExt A₁ A₂) (F : Nat) (ctx : NestCtx) (g : Name → Option ConstantInfo) :
    ∀ (cs : List (ConstantVal × Nat)) (os : List (List NestFieldKind × Expr)), (∀ o ∈ os, Res A₁ o.2) →
      checkAbsCtorSorts (m := CheckM) (fueledOps .verified F) A₁ ctx cs os = .ok () →
      checkAbsCtorSorts (m := CheckM) (fueledOps .verified F) A₂ (atF ctx g) cs os = .ok ()
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | c :: cs, o :: os, hos, h => by
    have ho : Res A₁ o.2 := hos o (List.mem_cons_self ..)
    unfold checkAbsCtorSorts at h ⊢
    dsimp only [atF] at h ⊢
    simp only [NestCtx.hiAt, Nat.add_zero] at h ⊢
    split at h
    · rename_i hl
      simp only [hl, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
      try dsimp only at h ⊢
      cases hq : openPisAtFvars c.2 o.2 (ctx.nP + ctx.names.length) with
      | none => simp [hq] at h; kill h
      | some xq =>
        have hrq := (resOpen_open ho c.2 (ctx.nP + ctx.names.length)) xq.1 xq.2 (by rw [hq])
        simp only [hq, unwrapOr, pure_bind] at h ⊢
        rw [checkStructFieldSortsI_eq hx F _ _ _ _ _ _ hrq.1]
        obtain ⟨u, hu, h⟩ := exceptBind_ok h
        rw [hu]
        exact checkAbsCtorSorts_ext hx F ctx g cs os (fun o' h' => hos o' (List.mem_cons_of_mem _ h')) h
    · kill h

theorem checkAbsCtorSortsAll_ext (hx : EnvExt A₁ A₂) (F : Nat) (ctx : NestCtx) (g : Name → Option ConstantInfo) :
    ∀ (css : List (List (ConstantVal × Nat))) (oss : List (List (List NestFieldKind × Expr))),
      (∀ os ∈ oss, ∀ o ∈ os, Res A₁ o.2) →
      checkAbsCtorSortsAll (m := CheckM) (fueledOps .verified F) A₁ ctx css oss = .ok () →
      checkAbsCtorSortsAll (m := CheckM) (fueledOps .verified F) A₂ (atF ctx g) css oss = .ok ()
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | cs :: css, os :: oss, hos, h => by
    unfold checkAbsCtorSortsAll at h ⊢
    obtain ⟨u, hu, h⟩ := exceptBind_ok h
    rw [checkAbsCtorSorts_ext hx F ctx g cs os (hos os (List.mem_cons_self ..)) hu]
    exact checkAbsCtorSortsAll_ext hx F ctx g css oss (fun os' h' => hos os' (List.mem_cons_of_mem _ h')) h

theorem nestRoot_ext (hc : CtorsAgree A₁ A₂) (hx : EnvExt A₁ A₂) (F : Nat) {ctx : NestCtx}
    (hf : ctx.find? = A₁.find?) (hp : ResL A₁ ctx.params) {holes : List Expr} (hh : ResL A₁ holes) :
    ∀ (css : List (List (ConstantVal × Nat))) (st : NestState) (r : List (List (List NestFieldKind × Expr)) × NestState),
      (∀ cs ∈ css, ∀ c ∈ cs, Res A₁ c.1.type) →
      nestRoot (m := CheckM) (fueledOps .verified F) A₁ ctx holes css st = .ok r →
      nestRoot (m := CheckM) (fueledOps .verified F) A₂ (atF ctx A₂.find?) holes css st = .ok r ∧
        ∀ os ∈ r.1, ∀ o ∈ os, Res A₁ o.2
  | [], st, r, _, h => by
    simp only [nestRoot, pure, Except.pure, Except.ok.injEq] at h ⊢; subst h; exact ⟨rfl, fun _ h => nomatch h⟩
  | cs :: css, st, r, hcs, h => by
    unfold nestRoot at h ⊢
    obtain ⟨⟨o, st1⟩, h1, h⟩ := exceptBind_ok h
    obtain ⟨h1', ho⟩ := nestCtors_ext hx F ctx (fun crest => nestPos_ext hc hx F hf (whnfWalkFuel crest)) [] _ _ hp hh
      _ cs st _ (hcs cs (List.mem_cons_self ..)) h1
    have e : (atF ctx A₂.find?).hiAt 0 = ctx.hiAt 0 := rfl
    have e2 : (atF ctx A₂.find?).lps = ctx.lps := rfl
    have e3 : (atF ctx A₂.find?).params = ctx.params := rfl
    have e4 : (atF ctx A₂.find?).names = ctx.names := rfl
    rw [e, e2, e3, e4, h1']
    simp only [bind, Except.bind] at h ⊢
    obtain ⟨⟨os, st2⟩, h2, h⟩ := exceptBind_ok h
    obtain ⟨h2', hos⟩ := nestRoot_ext hc hx F hf hp hh css st1 _ (fun cs' h' => hcs cs' (List.mem_cons_of_mem _ h')) h2
    rw [h2']
    simp only [pure, Except.pure, Except.ok.injEq] at h ⊢
    subst h
    refine ⟨rfl, fun os' h' => ?_⟩
    rcases List.mem_cons.mp h' with rfl | h'
    · exact ho
    · exact hos os' h'

theorem nestUniform_atF (ctx : NestCtx) (g : Name → Option ConstantInfo) (css : List (List (ConstantVal × Nat))) :
    nestUniform (m := CheckM) (atF ctx g) css = nestUniform (m := CheckM) ctx css := rfl

theorem checkBlockPositivity_ext (hc : CtorsAgree A₁ A₂) (hx : EnvExt A₁ A₂) (F : Nat) (p : BlockShape)
    (hT : ∀ ms ∈ p.members, Res A₁ ms.cvT.type) (hC : ∀ cs ∈ p.memberCtors, ∀ c ∈ cs, Res A₁ c.1.type)
    {r : List (List (List NestFieldKind × Expr)) × NestState}
    (h : checkBlockPositivity (m := CheckM) (fueledOps .verified F) A₁ A₁.find? p = .ok r) :
    checkBlockPositivity (m := CheckM) (fueledOps .verified F) A₂ A₂.find? p = .ok r := by
  unfold checkBlockPositivity at h ⊢
  obtain ⟨⟨ctx, holes⟩, h1, h⟩ := exceptBind_ok h
  obtain ⟨h1', hf, hfm, ⟨cvTa0, rest, hfs, b, hop⟩, hn⟩ := blockNestCtx_atF p A₂.find? h1
  rw [h1']
  simp only [bind, Except.bind] at h ⊢
  have hfm' : ∀ cv ∈ ctx.formers, Res A₁ cv.type := by
    intro cv hcv; rw [hfm] at hcv
    obtain ⟨ms, hms, rfl⟩ := List.mem_map.mp hcv; exact hT ms hms
  have hp : ResL A₁ ctx.params :=
    res_openPisAtFvars p.nP 0 (hfm' cvTa0 (by rw [hfm, hfs]; exact List.mem_cons_self ..)) hop
  have hh := res_nestHoles hp hfm' hn
  rw [nestUniform_atF]
  obtain ⟨u, hu, h⟩ := exceptBind_ok h
  rw [hu]
  simp only [bind, Except.bind] at h ⊢
  obtain ⟨⟨outs, st⟩, h2, h⟩ := exceptBind_ok h
  obtain ⟨h2', hos⟩ := nestRoot_ext hc hx F hf hp hh _ {} _ hC h2
  rw [h2']
  simp only [bind, Except.bind] at h ⊢
  obtain ⟨u, hu, h⟩ := exceptBind_ok h
  rw [checkAbsCtorSortsAll_ext hx F ctx A₂.find? _ _ hos hu]
  exact h

theorem nestInstType_found {ctx : NestCtx} {ops : CheckerOps CheckM} {env : Env} {hi : Nat} {key : NestKey}
    {r : Nat × Expr} (h : nestInstType ctx ops env hi key = .ok r) : (ctx.find? key.cname).isSome = true := by
  unfold nestInstType at h
  cases hI : ctx.find? key.cname with
  | none => simp [hI, unwrapOr, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  | some ci => rfl

theorem nestSeeds_ext (hc : CtorsAgree A₁ A₂) (hx : EnvExt A₁ A₂) (F : Nat) {ctx : NestCtx}
    (hf : ctx.find? = A₁.find?) :
    ∀ (keys : List (NestKey × Nat)) (st r : NestState), (∀ k ∈ keys, ResL A₁ k.1.ds) →
      nestSeeds (m := CheckM) (fueledOps .verified F) A₁ ctx keys st = .ok r →
      nestSeeds (m := CheckM) (fueledOps .verified F) A₂ (atF ctx A₂.find?) keys st = .ok r
  | [], st, r, _, h => h
  | (key, nPc) :: ks, st, r, hk, h => by
    have hds : ResL A₁ key.ds := hk _ (List.mem_cons_self ..)
    unfold nestSeeds at h ⊢
    dsimp only at h ⊢
    obtain ⟨⟨k, cty⟩, h1, h⟩ := exceptBind_ok h
    have hn : (A₁.find? key.cname).isSome = true := by have := nestInstType_found h1; rwa [hf] at this
    have hcty := nestInstType_res hx F hf _ key hds h1
    have e : (atF ctx A₂.find?).hiAt 0 = ctx.hiAt 0 := rfl
    rw [e, nestInstType_eq hx F hf _ key h1]
    simp only [bind, Except.bind] at h ⊢
    obtain ⟨⟨k2, st1⟩, h2, h⟩ := exceptBind_ok h
    rw [nestContKey_ext hc hx F hf (nestPos_ext hc hx F hf _) [] 0 key.cname hn key.lvls hds nPc hcty st _ h2]
    simp only [bind, Except.bind] at h ⊢
    exact nestSeeds_ext hc hx F hf ks st1 r (fun k' h' => hk k' (List.mem_cons_of_mem _ h')) h

end ConPanqueque.Pipeline.IndExt
