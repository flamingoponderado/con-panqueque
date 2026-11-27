import ConPanqueque.Pipeline.IndExt.PosBase

/-! # The positivity walk at an extension

The walk's functions take the walk itself as an argument (`rec`).  Each one carries over from `A₁`
(context `ctx`) to `A₂` (context `ctx` at `A₂.find?`) given that its `rec` does (`RecT`), on
resolving terms; every normal form the walk returns resolves at `A₁`. -/

namespace ConPanqueque.Pipeline.IndExt

open ConLeche ConLeche.Verify ConPanqueque.Pipeline

set_option autoImplicit false

variable {A₁ A₂ : Env}

abbrev WalkFn := List NestHole → Nat → Nat → Expr → NestState → CheckM (NestFieldKind × Expr × NestState)

/-- The walk carries over on resolving terms, and its normal forms resolve. -/
def RecT (A₁ : Env) (rec₁ rec₂ : WalkFn) : Prop :=
  ∀ prog dep kb e st r, Res A₁ e → rec₁ prog dep kb e st = .ok r → rec₂ prog dep kb e st = .ok r ∧ Res A₁ r.2.1

/-- The context at another lookup. -/
abbrev atF (ctx : NestCtx) (g : Name → Option ConstantInfo) : NestCtx := { ctx with find? := g }

theorem nestHoleImg_atF (ctx : NestCtx) (g : Name → Option ConstantInfo) :
    ∀ (prog : List NestHole), nestHoleImg (atF ctx g) prog = nestHoleImg ctx prog
  | [] => rfl
  | h :: prog => by
    funext i
    simp only [nestHoleImg]
    rw [nestHoleImg_atF ctx g prog]
    rfl

theorem nestCtorNf_atF (ctx : NestCtx) (g : Name → Option ConstantInfo) (prog : List NestHole) (hi : Nat)
    (us : List Level) (ds : List Expr) (cv : ConstantVal) (nds : List Expr) (cur : Expr) :
    nestCtorNf (atF ctx g) prog hi us ds cv nds cur = nestCtorNf ctx prog hi us ds cv nds cur := by
  unfold nestCtorNf; rw [nestHoleImg_atF]

theorem nestFields_ext {rec₁ rec₂ : WalkFn} (hrec : RecT A₁ rec₁ rec₂) (prog : List NestHole) (base : Nat)
    (err : CheckError) :
    ∀ (nF j : Nat) (cur : Expr) (st : NestState) (r : List NestFieldKind × List Expr × Expr × NestState),
      Res A₁ cur → nestFields (m := CheckM) rec₁ prog base err nF j cur st = .ok r →
      nestFields (m := CheckM) rec₂ prog base err nF j cur st = .ok r ∧ ResL A₁ r.2.1 ∧ Res A₁ r.2.2.1
  | 0, j, cur, st, r, hc, h => by
    simp only [nestFields, pure, Except.pure, Except.ok.injEq] at h ⊢
    subst h; exact ⟨rfl, (fun _ hx => nomatch hx), hc⟩
  | nF + 1, j, cur, st, r, hc, h => by
    unfold nestFields at h ⊢
    split at h
    · rename_i a b
      have ha := (res_forall.mp hc).1
      obtain ⟨⟨k, nd, st1⟩, h1, h⟩ := exceptBind_ok h
      obtain ⟨h1', hnd⟩ := hrec _ _ _ _ _ _ ha h1
      obtain ⟨⟨ks, nds, res, st2⟩, h2, h⟩ := exceptBind_ok h
      obtain ⟨h2', hnds, hres⟩ := nestFields_ext hrec prog base err nF (j + 1) _ st1 _
        (res_open ha (res_forall.mp hc).2) h2
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      simp only [h1', h2', bind, Except.bind, pure, Except.pure]
      refine ⟨trivial, fun x hx => ?_, hres⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hnd
      · exact hnds x hx
    · kill h

theorem nestCtors_ext (hx : EnvExt A₁ A₂) (F : Nat) (ctx : NestCtx)
    {rec₁ rec₂ : Expr → WalkFn} (hrec : ∀ c, RecT A₁ (rec₁ c) (rec₂ c)) (prog : List NestHole) (hi : Nat)
    (us : List Level) {ds holes : List Expr} (hds : ResL A₁ ds) (hh : ResL A₁ holes) (names : List Name) :
    ∀ (cs : List (ConstantVal × Nat)) (st : NestState) (r : List (List NestFieldKind × Expr) × NestState),
      (∀ c ∈ cs, Res A₁ c.1.type) →
      nestCtors (m := CheckM) ctx (fueledOps .verified F) A₁ rec₁ prog hi us ds names holes cs st = .ok r →
      nestCtors (m := CheckM) (atF ctx A₂.find?) (fueledOps .verified F) A₂ rec₂ prog hi us ds names holes cs st
        = .ok r ∧ ∀ o ∈ r.1, Res A₁ o.2
  | [], st, r, _, h => by
    simp only [nestCtors, pure, Except.pure, Except.ok.injEq] at h ⊢
    subst h; exact ⟨rfl, fun _ hx => nomatch hx⟩
  | (cv, nF) :: cs, st, r, hcs, h => by
    have hcv : Res A₁ cv.type := hcs _ (List.mem_cons_self ..)
    unfold nestCtors at h ⊢
    by_cases hnd : Name.nodup cv.levelParams = true
    · simp only [hnd, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h ⊢
      try dsimp only at h ⊢
      cases hcr : nestCrest names us ds holes (cv.type.instantiateLevelParams cv.levelParams us) with
      | none => simp [hcr] at h; kill h
      | some crest =>
        have hrc : Res A₁ crest := res_nestCrest hds hh (res_inst _ _ hcv) hcr
        simp only [hcr, unwrapOr, pure_bind] at h ⊢
        obtain ⟨ty, hty, h⟩ := exceptBind_ok h
        have hrty := (ops_infer hx F hi hrc).2 ty hty
        rw [(ops_infer hx F hi hrc).1, hty]
        simp only [bind, Except.bind] at h ⊢
        obtain ⟨u, hu, h⟩ := exceptBind_ok h
        rw [ops_ensureSort hx F hi hrty, hu]
        simp only [bind, Except.bind] at h ⊢
        obtain ⟨⟨ks, nds, cur, st1⟩, hf, h⟩ := exceptBind_ok h
        obtain ⟨hf', hnds, hcur⟩ := nestFields_ext (hrec crest) prog hi _ nF 0 crest st _ hrc hf
        rw [hf']
        simp only [bind, Except.bind] at h ⊢
        split at h
        · kill h
        · rename_i hU
          simp only [hU, Bool.false_eq_true, ↓reduceIte]
          try dsimp only at h ⊢
          split at h
          · rename_i hR
            simp only [hR, ↓reduceIte, nestCtorNf_atF]
            try dsimp only at h ⊢
            obtain ⟨⟨os, st2⟩, hr, h⟩ := exceptBind_ok h
            obtain ⟨hr', hos⟩ := nestCtors_ext hx F ctx hrec prog hi us hds hh names cs _ _
              (fun c hc => hcs c (List.mem_cons_of_mem _ hc)) hr
            rw [hr']
            simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h ⊢
            subst h
            refine ⟨rfl, fun o ho => ?_⟩
            rcases List.mem_cons.mp ho with rfl | ho
            · exact res_closeTelescope nds hi hnds hcur
            · exact hos o ho
          · kill h
    · simp [hnd] at h; kill h

theorem nestContainer_found {ctx : NestCtx} {C : Name} {q : Nat × List (ConstantVal × Nat)}
    (h : nestContainer ctx C = some q) : ∃ cv caps, ctx.find? C = some (.indInfo cv caps) := by
  unfold nestContainer at h
  split at h
  · rename_i cv caps hI; exact ⟨cv, caps, hI⟩
  · cases h

theorem nestGroupCtors_ext (hc : CtorsAgree A₁ A₂) (hx : EnvExt A₁ A₂) {ctx : NestCtx} (hf : ctx.find? = A₁.find?)
    (nPc : Nat) : ∀ (cs : List Name) (r : List (ConstantVal × Nat)),
      nestGroupCtors (m := CheckM) ctx nPc cs = .ok r →
      nestGroupCtors (m := CheckM) (atF ctx A₂.find?) nPc cs = .ok r ∧ ∀ c ∈ r, Res A₁ c.1.type
  | [], r, h => by
    simp only [nestGroupCtors, pure, Except.pure, Except.ok.injEq] at h ⊢; subst h
    exact ⟨rfl, fun _ hx => nomatch hx⟩
  | c :: cs, r, h => by
    unfold nestGroupCtors at h ⊢
    cases hq : nestContainer ctx c with
    | none => simp [hq] at h; kill h
    | some q =>
      have hq2 := nestContainer_ext hc hx hf hq
      have hst := nestContainer_stored hq
      simp only [hq, hq2, unwrapOr, pure_bind] at h ⊢
      obtain ⟨nPc', ctors⟩ := q
      simp only at h ⊢
      split at h
      · rename_i hok
        simp only [hok, ↓reduceIte]
        try dsimp only at h ⊢
        obtain ⟨rest, hr, h⟩ := exceptBind_ok h
        obtain ⟨hr', hres⟩ := nestGroupCtors_ext hc hx hf nPc cs rest hr
        rw [hr']
        simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h ⊢
        subst h
        refine ⟨rfl, fun x hxm => ?_⟩
        rcases List.mem_append.mp hxm with hxm | hxm
        · obtain ⟨n, ci, hn, hcv⟩ := hst x hxm
          rw [hf] at hn
          have := hx.facts.type hn
          rw [hcv] at this; exact this
        · exact hres x hxm
      · kill h

theorem nestGrowGroup_ext (hx : EnvExt A₁ A₂) (F : Nat) {ctx : NestCtx} (hf : ctx.find? = A₁.find?)
    (hi : Nat) (us : List Level) {ds : List Expr} (hds : ResL A₁ ds) :
    ∀ (cs : List Name) (grp r : List (Name × Expr)), (∀ p ∈ grp, Res A₁ p.2) →
      nestGrowGroup (m := CheckM) ctx (fueledOps .verified F) A₁ hi us ds cs grp = .ok r →
      nestGrowGroup (m := CheckM) (atF ctx A₂.find?) (fueledOps .verified F) A₂ hi us ds cs grp = .ok r ∧
        ∀ p ∈ r, Res A₁ p.2
  | [], grp, r, hg, h => by
    simp only [nestGrowGroup, pure, Except.pure, Except.ok.injEq] at h ⊢; subst h; exact ⟨rfl, hg⟩
  | c :: cs, grp, r, hg, h => by
    unfold nestGrowGroup at h ⊢
    obtain ⟨⟨k, cty⟩, h1, h⟩ := exceptBind_ok h
    have hcty := nestInstType_res hx F hf hi ⟨c, us, ds⟩ hds h1
    rw [nestInstType_eq hx F hf hi ⟨c, us, ds⟩ h1]
    simp only [bind, Except.bind] at h ⊢
    exact nestGrowGroup_ext hx F hf hi us hds cs _ r (fun p hp => by
      rcases List.mem_append.mp hp with hp | hp
      · exact hg p hp
      · simp only [List.mem_singleton] at hp; subst hp; exact hcty) h

theorem nestFrame_ext (hc : CtorsAgree A₁ A₂) (hx : EnvExt A₁ A₂) (F : Nat) {ctx : NestCtx}
    (hf : ctx.find? = A₁.find?) {rec₁ rec₂ : WalkFn} (hrec : RecT A₁ rec₁ rec₂) (prog : List NestHole)
    (hi : Nat) (us : List Level) {ds : List Expr} (hds : ResL A₁ ds) (nPc : Nat) (grp : List (Name × Expr))
    (hg : ∀ p ∈ grp, Res A₁ p.2) (st r : NestState)
    (h : nestFrame (m := CheckM) ctx (fueledOps .verified F) A₁ rec₁ prog hi us ds nPc grp st = .ok r) :
    nestFrame (m := CheckM) (atF ctx A₂.find?) (fueledOps .verified F) A₂ rec₂ prog hi us ds nPc grp st = .ok r := by
  unfold nestFrame at h ⊢
  rw [hf] at h
  obtain ⟨u, h1, h⟩ := exceptBind_ok h
  cases u
  rw [show (atF ctx A₂.find?).find? = A₂.find? from rfl, familyKeyChecks_ext hx F hi us hds _ h1]
  simp only [bind, Except.bind] at h ⊢
  obtain ⟨ctors, h2, h⟩ := exceptBind_ok h
  obtain ⟨h2', hct⟩ := nestGroupCtors_ext hc hx hf nPc _ ctors h2
  rw [h2']
  simp only [bind, Except.bind] at h ⊢
  obtain ⟨⟨os, st1⟩, h3, h⟩ := exceptBind_ok h
  have hholes : ResL A₁ (grp.mapIdx fun i (p : Name × Expr) => Expr.fvar (hi + i) p.2) := by
    intro x hxm
    obtain ⟨i, hi', rfl⟩ := List.getElem_of_mem hxm
    simp only [List.getElem_mapIdx]
    exact res_fvar.mpr (hg _ (List.getElem_mem _))
  obtain ⟨h3', -⟩ := nestCtors_ext hx F ctx (fun _ => hrec) _ _ us hds hholes _ ctors st _ hct h3
  rw [h3']
  exact h

theorem nestFrameMates_eq (hx : EnvExt A₁ A₂) {ctx : NestCtx} (hf : ctx.find? = A₁.find?) {n : Name}
    (hn : (A₁.find? n).isSome = true) : nestFrameMates (atF ctx A₂.find?) n = nestFrameMates ctx n := by
  unfold nestFrameMates nestBlockOf
  rw [hf]
  dsimp only
  rw [hx.find_of_isSome hn]

theorem nestContNew_ext (hc : CtorsAgree A₁ A₂) (hx : EnvExt A₁ A₂) (F : Nat) {ctx : NestCtx}
    (hf : ctx.find? = A₁.find?) {rec₁ rec₂ : WalkFn} (hrec : RecT A₁ rec₁ rec₂) (prog : List NestHole)
    (kb : Nat) (n : Name) (hn : (A₁.find? n).isSome = true) (us : List Level) {ds : List Expr}
    (hds : ResL A₁ ds) (nPc : Nat) {cty : Expr} (hcty : Res A₁ cty) (st : NestState)
    (r : NestFieldKind × NestState)
    (h : nestContNew (m := CheckM) ctx (fueledOps .verified F) A₁ rec₁ prog kb n us ds nPc cty st = .ok r) :
    nestContNew (m := CheckM) (atF ctx A₂.find?) (fueledOps .verified F) A₂ rec₂ prog kb n us ds nPc cty st
      = .ok r := by
  unfold nestContNew at h ⊢
  dsimp only at h ⊢
  rw [nestFrameMates_eq hx hf hn]
  obtain ⟨grp, h1, h⟩ := exceptBind_ok h
  obtain ⟨h1', hg⟩ := nestGrowGroup_ext hx F hf _ us hds _ _ grp (fun p hp => by
    simp only [List.mem_singleton] at hp; subst hp; exact hcty) h1
  have e1 : nestWalkStack (atF ctx A₂.find?) prog ds = nestWalkStack ctx prog ds := rfl
  have e2 : (atF ctx A₂.find?).hiAt = ctx.hiAt := rfl
  rw [e1, e2, h1']
  simp only [bind, Except.bind] at h ⊢
  obtain ⟨st1, h2, h⟩ := exceptBind_ok h
  rw [nestFrame_ext hc hx F hf hrec _ _ us hds nPc grp hg _ st1 h2]
  exact h

theorem nestContKey_ext (hc : CtorsAgree A₁ A₂) (hx : EnvExt A₁ A₂) (F : Nat) {ctx : NestCtx}
    (hf : ctx.find? = A₁.find?) {rec₁ rec₂ : WalkFn} (hrec : RecT A₁ rec₁ rec₂) (prog : List NestHole)
    (kb : Nat) (n : Name) (hn : (A₁.find? n).isSome = true) (us : List Level) {ds : List Expr}
    (hds : ResL A₁ ds) (nPc : Nat) {cty : Expr} (hcty : Res A₁ cty) (st : NestState)
    (r : NestFieldKind × NestState)
    (h : nestContKey (m := CheckM) ctx (fueledOps .verified F) A₁ rec₁ prog kb n us ds nPc cty st = .ok r) :
    nestContKey (m := CheckM) (atF ctx A₂.find?) (fueledOps .verified F) A₂ rec₂ prog kb n us ds nPc cty st
      = .ok r := by
  unfold nestContKey at h ⊢
  have e2 : (atF ctx A₂.find?).hiAt = ctx.hiAt := rfl
  rw [e2]
  split at h
  · kill h
  · rename_i h1
    rw [if_neg h1]
    split at h
    · rename_i h2; rw [if_pos h2]; exact h
    · rename_i h2; rw [if_neg h2]
      exact nestContNew_ext hc hx F hf hrec prog kb n hn us hds nPc hcty st r h

theorem nestCont_ext (hc : CtorsAgree A₁ A₂) (hx : EnvExt A₁ A₂) (F : Nat) {ctx : NestCtx}
    (hf : ctx.find? = A₁.find?) {rec₁ rec₂ : WalkFn} (hrec : RecT A₁ rec₁ rec₂) (prog : List NestHole)
    (kb : Nat) (n : Name) (us : List Level) {args : List Expr} (hargs : ResL A₁ args) (st : NestState)
    (r : NestFieldKind × NestState)
    (h : nestCont (m := CheckM) ctx (fueledOps .verified F) A₁ rec₁ prog kb n us args st = .ok r) :
    nestCont (m := CheckM) (atF ctx A₂.find?) (fueledOps .verified F) A₂ rec₂ prog kb n us args st = .ok r := by
  unfold nestCont at h ⊢
  cases hq : nestContainer ctx n with
  | none => simp [hq] at h; kill h
  | some q =>
    obtain ⟨cv, caps, hI⟩ := nestContainer_found hq
    rw [hf] at hI
    have hn : (A₁.find? n).isSome = true := by rw [hI]; rfl
    simp only [hq, nestContainer_ext hc hx hf hq, unwrapOr, pure_bind] at h ⊢
    have e2 : (atF ctx A₂.find?).hiAt = ctx.hiAt := rfl
    have e3 : (atF ctx A₂.find?).names = ctx.names := rfl
    have e4 : (atF ctx A₂.find?).nP = ctx.nP := rfl
    rw [e2, e3, e4]
    split at h
    · kill h
    · rename_i h1
      rw [if_neg h1]
      split at h
      · kill h
      · rename_i h2
        rw [if_neg h2]
        try dsimp only at h ⊢
        split at h
        · rename_i h3
          simp only [h3, ↓reduceIte] at h ⊢
          try dsimp only at h ⊢
          obtain ⟨ni, h4, h⟩ := exceptBind_ok h
          have hds : ResL A₁ (args.take q.1) := res_take hargs _
          have hni := nestInstType_res hx F hf _ ⟨n, us, args.take q.1⟩ hds h4
          rw [nestInstType_eq hx F hf _ ⟨n, us, args.take q.1⟩ h4]
          simp only [bind, Except.bind] at h ⊢
          split at h
          · rename_i h5
            simp only [h5, ↓reduceIte] at h ⊢
            try dsimp only at h ⊢
            exact nestContKey_ext hc hx F hf hrec prog kb n hn us hds q.1 hni st r h
          · kill h
        · kill h

/-- **The walk at an extension.** -/
theorem nestPos_ext (hc : CtorsAgree A₁ A₂) (hx : EnvExt A₁ A₂) (F : Nat) {ctx : NestCtx}
    (hf : ctx.find? = A₁.find?) :
    ∀ fuel, RecT A₁ (nestPos (m := CheckM) (fueledOps .verified F) A₁ ctx fuel)
      (nestPos (m := CheckM) (fueledOps .verified F) A₂ (atF ctx A₂.find?) fuel)
  | 0 => by
    intro prog dep kb e st r _ h
    simp [nestPos, throw, throwThe, MonadExceptOf.throw] at h
  | fuel + 1 => by
    intro prog dep kb e st r he h
    have ih := nestPos_ext hc hx F hf fuel
    unfold nestPos at h ⊢
    have e2 : (atF ctx A₂.find?).hiAt = ctx.hiAt := rfl
    have e3 : (atF ctx A₂.find?).names = ctx.names := rfl
    have e4 : (atF ctx A₂.find?).nP = ctx.nP := rfl
    rw [e2, e3, e4]
    obtain ⟨hw, hwr⟩ := whnf_rel hx F dep he
    obtain ⟨w, h1, h⟩ := exceptBind_ok h
    have hrw := hwr w h1
    rw [hw, h1]
    simp only [bind, Except.bind] at h ⊢
    split at h
    · rename_i hocc
      simp only [hocc, ↓reduceIte] at h ⊢
      simp only [pure, Except.pure, Except.ok.injEq] at h
      subst h
      refine ⟨rfl, ?_⟩
      dsimp only
      split
      · exact hrw
      · exact he
    · rename_i hocc
      simp only [hocc, Bool.false_eq_true, ↓reduceIte] at h ⊢
      split at h
      · rename_i a b
        have ha := (res_forall.mp hrw).1
        split at h
        · kill h
        · rename_i hna
          simp only [hna, Bool.false_eq_true, ↓reduceIte]
          obtain ⟨⟨k, nb, st1⟩, h2, h⟩ := exceptBind_ok h
          obtain ⟨h2', hnb⟩ := ih _ _ _ _ _ _ (res_open ha (res_forall.mp hrw).2) h2
          rw [h2']
          simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h ⊢
          subst h
          exact ⟨rfl, res_forall.mpr ⟨ha, res_abstract1 dep _ 0 hnb⟩⟩
      · rename_i hnf
        have hnestHole : ∀ i, nestHoleAt (atF ctx A₂.find?) prog i = nestHoleAt ctx prog i := fun _ => rfl
        split at h
        · rename_i i ty hfn
          rw [hnestHole]
          split at h
          · rename_i hh hhe
            split at h
            · rename_i hcond
              simp only [hcond, ↓reduceIte, pure, Except.pure, Except.ok.injEq] at h ⊢
              subst h
              exact ⟨rfl, hrw⟩
            · kill h
          · kill h
        · rename_i n us hfn
          split at h
          · kill h
          · rename_i hmem
            simp only [hmem, Bool.false_eq_true, ↓reduceIte]
            obtain ⟨⟨k, st1⟩, h2, h⟩ := exceptBind_ok h
            have hargs : ResL A₁ w.getAppArgs := res_getAppArgs hrw
            rw [nestCont_ext hc hx F hf (fun prog dep kb e st r he h => ih prog dep kb e st r he h) prog kb n us
              hargs st _ h2]
            simp only [bind, Except.bind, pure, Except.pure, Except.ok.injEq] at h ⊢
            subst h
            exact ⟨rfl, hrw⟩
        · kill h

end ConPanqueque.Pipeline.IndExt
