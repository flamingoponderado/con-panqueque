import ConPanqueque.Pipeline.IndExt.Classes
import ConPanqueque.Pipeline.IndExt.PosTop
import ConPanqueque.Pipeline.IndExt.Agree
import ConPanqueque.Pipeline.IndExt.Inds
import ConLeche.Verify.Denote.IndFrame

/-! # The block's pass at an extension

`checkBlockPass`: the formers (`checkBlockInds`), the constructors, the walk's context, the classes,
the positivity walk and the seeds, from `X₁` to an extension `X₂`. -/

namespace ConPanqueque.Pipeline.IndExt

open ConLeche ConLeche.Verify ConPanqueque.Pipeline

set_option autoImplicit false

variable {X₁ X₂ : Env}

theorem res_prepend {X : Env} (R : List ConstantInfo) (ts : List ProjTable) {e : Expr} (h : Res X e) :
    Res ⟨R ++ X.consts, ts⟩ e :=
  Expr.constsResolve_of_find (fun n hn => find?_prepend_isSome (ts := X.tables) hn) h

theorem checkBlockTele_resIn {F nP : Nat} {env : Env} {ms : MemberShape} {q : ConstantVal × Level}
    (h : checkBlockTele (m := CheckM) (fueledOps .verified F) env nP ms = .ok q) : Res env ms.cvT.type := by
  unfold checkBlockTele at h
  obtain ⟨u, hu, -⟩ := exceptBind_ok h
  cases u
  exact (checkConstantVal_res F env ms.cvT _ _ _ hu).1

theorem checkBlockTeles_resIn {F nP : Nat} {env : Env} :
    ∀ {mss : List MemberShape} {cvs : List (ConstantVal × Level)},
      checkBlockTeles (m := CheckM) (fueledOps .verified F) env nP mss = .ok cvs → ∀ ms ∈ mss, Res env ms.cvT.type
  | [], _, _, _, hm => nomatch hm
  | ms :: rest, cvs, h, x, hm => by
    unfold checkBlockTeles at h
    obtain ⟨q, hq, h⟩ := exceptBind_ok h
    obtain ⟨qs, hqs, -⟩ := exceptBind_ok h
    rcases List.mem_cons.mp hm with rfl | hm
    · exact checkBlockTele_resIn hq
    · exact checkBlockTeles_resIn hqs x hm

theorem checkBlockInds_resIn {F : Nat} {env A : Env} {p p₁ : BlockShape} {isRec : Bool}
    (h : checkBlockInds (m := CheckM) (fueledOps .verified F) env p isRec = .ok (A, p₁)) :
    ∀ ms ∈ p.members, Res env ms.cvT.type := by
  obtain ⟨ms0, rest, cvTa0, s0, cvs, hm, -, -, h0, hr, -⟩ := checkBlockInds_shape h
  intro ms hms
  rw [hm] at hms
  rcases List.mem_cons.mp hms with rfl | hms
  · exact checkBlockTele_resIn h0
  · exact checkBlockTeles_resIn hr ms hms

theorem checkSumCtors_resIn {F : Nat} {env₀ env : Env} {T : Name} {lps : List Name} {nP nIdx : Nat}
    {resSort : Level} {isProp large : Bool} {cvTa : ConstantVal} :
    ∀ {cs : List (ConstantVal × Nat)},
      checkSumCtors (m := CheckM) (fueledOps .verified F) env₀ env T lps nP nIdx resSort isProp large cvTa cs = .ok () →
      ∀ c ∈ cs, Res env c.1.type
  | [], _, _, hm => nomatch hm
  | c :: cs, h, x, hm => by
    unfold checkSumCtors at h
    obtain ⟨u, hu, h⟩ := exceptBind_ok h
    rcases List.mem_cons.mp hm with rfl | hm
    · unfold checkSumCtor at hu
      obtain ⟨u', hu', -⟩ := exceptBind_ok hu
      cases u'
      exact (checkConstantVal_res F env _ _ _ _ hu').1
    · exact checkSumCtors_resIn h x hm

theorem checkBlockCtors_resIn {F : Nat} {env₀ env : Env} {p : BlockShape} :
    ∀ {l : List MemberShape}, checkBlockCtors (m := CheckM) (fueledOps .verified F) env₀ env p l = .ok () →
      ∀ cs ∈ l.map (·.ctors), ∀ c ∈ cs, Res env c.1.type
  | [], _, _, hm => nomatch hm
  | ms :: rest, h, cs, hm => by
    unfold checkBlockCtors at h
    obtain ⟨u, hu, h⟩ := exceptBind_ok h
    rcases List.mem_cons.mp hm with rfl | hm
    · exact checkSumCtors_resIn hu
    · exact checkBlockCtors_resIn h cs hm

theorem blockCapsAt_ctors_mem {p : BlockShape} {i : Nat} {isRec : Bool} {n : Name}
    (h : n ∈ (blockCapsAt p i isRec).ctors) : ∃ ms ∈ p.members, ∃ c ∈ ms.ctors, c.1.name = n := by
  have hget : (p.members.getD i default) ∈ p.members ∨ (p.members.getD i default).ctors = [] := by
    by_cases hi : i < p.members.length
    · left; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    · right; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi)]; rfl
  unfold blockCapsAt at h
  split at h
  · rename_i x c hcs
    simp only [List.mem_singleton] at h
    subst h
    rcases hget with hm | he
    · exact ⟨_, hm, c, by rw [hcs]; exact List.mem_singleton_self _, rfl⟩
    · rw [he] at hcs; cases hcs
  · simp only at h
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h
    rcases hget with hm | he
    · exact ⟨_, hm, c, hc, rfl⟩
    · rw [he] at hc; exact nomatch hc

theorem checkSumCtors_fresh {F : Nat} {env₀ env : Env} {T : Name} {lps : List Name} {nP nIdx : Nat}
    {resSort : Level} {isProp large : Bool} {cvTa : ConstantVal} :
    ∀ {cs : List (ConstantVal × Nat)},
      checkSumCtors (m := CheckM) (fueledOps .verified F) env₀ env T lps nP nIdx resSort isProp large cvTa cs = .ok () →
      ∀ c ∈ cs, env.find? c.1.name = none
  | [], _, _, hm => nomatch hm
  | c :: cs, h, x, hm => by
    unfold checkSumCtors at h
    obtain ⟨u, hu, h⟩ := exceptBind_ok h
    rcases List.mem_cons.mp hm with rfl | hm
    · unfold checkSumCtor at hu
      obtain ⟨u', hu', -⟩ := exceptBind_ok hu
      cases u'
      exact (checkConstantVal_res F env _ _ _ _ hu').2
    · exact checkSumCtors_fresh h x hm

theorem checkBlockCtors_fresh {F : Nat} {env₀ env : Env} {p : BlockShape} :
    ∀ {l : List MemberShape}, checkBlockCtors (m := CheckM) (fueledOps .verified F) env₀ env p l = .ok () →
      ∀ ms ∈ l, ∀ c ∈ ms.ctors, env.find? c.1.name = none
  | [], _, _, hm => nomatch hm
  | ms :: rest, h, x, hm => by
    unfold checkBlockCtors at h
    obtain ⟨u, hu, h⟩ := exceptBind_ok h
    rcases List.mem_cons.mp hm with rfl | hm
    · exact checkSumCtors_fresh hu
    · exact checkBlockCtors_fresh h x hm

theorem res_nestSeedOf {A : Env} {ctx : NestCtx} {holes : List Expr} (hp : ResL A ctx.params) (hh : ResL A holes)
    {I : Name} {us : List Level} {ds : List Expr} (hds : ResL A ds) (nPc : Nat) :
    ResL A (nestSeedOf ctx holes I us ds nPc).1.ds := by
  intro x hxm
  simp only [nestSeedOf, List.mem_map] at hxm
  obtain ⟨y, hy, rfl⟩ := hxm
  exact res_replaceFVars (res_nestKeyMap hp hh) _
    (res_replaceApps (res_nestCanonSub _ _ _) 0 _ y (hds y hy))

theorem res_classSeeds {A : Env} {ctx : NestCtx} {holes : List Expr} (hp : ResL A ctx.params) (hh : ResL A holes)
    {Ms : List TargetMajor} (hMs : ∀ M ∈ Ms, ResL A M.ds) : ∀ k ∈ classSeeds ctx holes Ms, ResL A k.1.ds := by
  intro k hk
  simp only [classSeeds, List.mem_filterMap] at hk
  obtain ⟨M, hM, hk⟩ := hk
  split at hk
  · simp only [Option.some.injEq] at hk; subst hk; exact res_nestSeedOf hp hh (hMs M hM) _
  · cases hk

/-- The formers' push. -/
def formersR (p₁ : BlockShape) (isRec : Bool) (cvs : List ConstantVal) : List ConstantInfo :=
  ((cvs.zipIdx 0).map fun x => ConstantInfo.indInfo x.1 (blockCapsAt p₁ x.2 isRec)).reverse

theorem formersR_mem {p₁ : BlockShape} {isRec : Bool} {cvs : List ConstantVal} {c : ConstantInfo}
    (h : c ∈ formersR p₁ isRec cvs) : ∃ cv ∈ cvs, ∃ i, c = .indInfo cv (blockCapsAt p₁ i isRec) := by
  simp only [formersR, List.mem_reverse, List.mem_map] at h
  obtain ⟨⟨cv, i⟩, hm, rfl⟩ := h
  exact ⟨cv, List.fst_mem_of_mem_zipIdx hm, i, rfl⟩

/-- **The pass at an extension.** -/
theorem checkBlockPass_ext (hx : EnvExt X₁ X₂) (ht2 : TablesStored X₂) (hca : CtorsAgree X₁ X₂) (F : Nat)
    {p : BlockShape} {isRec : Bool} {q : BlockPass Env}
    (hfrF : ∀ ms ∈ p.members, NameOK ms.declared.name ∧ X₂.find? ms.declared.name = none)
    (hdn : ∀ ms ∈ p.members, ms.cvT.name = ms.declared.name)
    (hfrC : ∀ ms ∈ p.members, ∀ c ∈ ms.ctors, X₂.find? c.1.name = none)
    (hwA : ∀ A p₁, checkBlockInds (m := CheckM) (fueledOps .verified F) X₁ p isRec = .ok (A, p₁) → EnvWF A)
    (h : checkBlockPass (m := CheckM) (fueledOps .verified F) X₁ p isRec = .ok q) :
    checkBlockPass (m := CheckM) (fueledOps .verified F) X₂ p isRec =
        .ok { q with env₁ := consBlockInds q.p isRec (p.members.map (·.declared)) 0 X₂ } ∧
      q.env₁ = consBlockInds q.p isRec (p.members.map (·.declared)) 0 X₁ ∧
      EnvExt q.env₁ (consBlockInds q.p isRec (p.members.map (·.declared)) 0 X₂) ∧
      CtorsAgree q.env₁ (consBlockInds q.p isRec (p.members.map (·.declared)) 0 X₂) ∧
      q.p.members = p.members ∧ ResL q.env₁ q.params ∧ q.params.length = p.nP ∧
      (∀ M ∈ q.cls, ResL q.env₁ M.ds) ∧ (∀ ms ∈ p.members, Res q.env₁ ms.cvT.type) ∧
      (∀ ms ∈ p.members, ∀ c ∈ ms.ctors, Res q.env₁ c.1.type ∧ q.env₁.find? c.1.name = none) := by
  unfold checkBlockPass at h ⊢
  obtain ⟨⟨A₁, p₁⟩, h1, h⟩ := exceptBind_ok h
  have hfrT : ∀ ms ∈ p.members, X₂.find? ms.cvT.name = none := fun ms hm => by
    rw [hdn ms hm]; exact (hfrF ms hm).2
  obtain ⟨h1', hA⟩ := checkBlockInds_ext hx hfrT h1
  have hwA1 := hwA _ _ h1
  have hp1m : p₁.members = p.members ∧ p₁.nP = p.nP := by
    obtain ⟨_, _, _, s0, _, _, hp1, _⟩ := checkBlockInds_shape h1
    subst hp1; exact ⟨rfl, rfl⟩
  have hp1n := hp1m.2
  replace hp1m := hp1m.1
  rw [h1']
  simp only [bind, Except.bind] at h ⊢
  generalize hcvs : p.members.map (·.declared) = cvs at *
  have eA : ∀ X : Env, consBlockInds p₁ isRec cvs 0 X = ⟨formersR p₁ isRec cvs ++ X.consts, X.tables⟩ :=
    fun X => consBlockInds_consts' p₁ isRec cvs 0 X
  have hRn : ∀ c ∈ formersR p₁ isRec cvs, ∃ ms ∈ p.members, c.name = ms.declared.name := by
    intro c hc
    obtain ⟨cv, hcv, i, rfl⟩ := formersR_mem hc
    rw [← hcvs] at hcv
    obtain ⟨ms, hms, rfl⟩ := List.mem_map.mp hcv
    exact ⟨ms, hms, rfl⟩
  have hxA : EnvExt A₁ (consBlockInds p₁ isRec cvs 0 X₂) := by
    rw [hA, eA, eA]
    have := envExt_prepend (X₁ := X₁) (X₂ := X₂) (formersR p₁ isRec cvs) [] hx ht2 (fun _ h => nomatch h)
      (fun c hc => by obtain ⟨ms, hms, he⟩ := hRn c hc; rw [he]; exact hfrF ms hms)
      (by rw [hA, eA] at hwA1; simpa using hwA1)
      (fun c hc cv mI rP isK rules he => by obtain ⟨_, _, i, rfl⟩ := formersR_mem hc; cases he)
      (fun _ h => nomatch h)
    simpa using this
  have hfr1 : ∀ n, X₂.find? n = none → X₁.find? n = none := fun n hn => by
    cases h1n : X₁.find? n with
    | none => rfl
    | some ci => rw [hx.find _ _ h1n] at hn; cases hn
  have hcA : CtorsAgree A₁ (consBlockInds p₁ isRec cvs 0 X₂) := by
    rw [hA, eA, eA]
    refine ctorsAgree_prepend _ _ _ hca (fun c hc cv caps he n hn => Or.inr ?_)
    obtain ⟨_, _, i, rfl⟩ := formersR_mem hc
    cases he
    obtain ⟨ms, hms, c', hc', rfl⟩ := blockCapsAt_ctors_mem hn
    rw [hp1m] at hms
    have h2 := hfrC ms hms c' hc'
    rw [h2, hfr1 _ h2]
  have hT : ∀ ms ∈ p.members, Res A₁ ms.cvT.type := fun ms hm => by
    rw [hA, eA]; exact res_prepend _ _ (checkBlockInds_resIn h1 ms hm)
  -- the constructors
  obtain ⟨u, h2, h⟩ := exceptBind_ok h
  cases u
  have hCfr := checkBlockCtors_fresh h2
  have hCres := checkBlockCtors_resIn h2
  have hfrC2 : ∀ c ∈ p₁.members.flatMap (·.ctors), (consBlockInds p₁ isRec cvs 0 X₂).find? c.1.name = none := by
    intro c hc
    obtain ⟨ms, hms, hc⟩ := List.mem_flatMap.mp hc
    have h1n := hCfr ms hms c hc
    rw [hA, eA] at h1n
    rw [eA]
    have hnR : c.1.name ∉ (formersR p₁ isRec cvs).map (·.name) := fun hmR => by
      have := find?_mem_name (cs := X₁.consts) (ts := X₁.tables) hmR
      rw [h1n] at this; cases this
    rw [find?_prepend_of_not_mem hnR]
    rw [hp1m] at hms
    exact hfrC ms hms c hc
  rw [checkBlockCtors_ext hxA F p₁ _ hfrC2 (fun ms hm => by rw [hp1m] at hm; exact hT ms hm) h2]
  simp only [bind, Except.bind] at h ⊢
  -- the walk's context
  obtain ⟨⟨ctx, holes⟩, h3, h⟩ := exceptBind_ok h
  obtain ⟨h3', hf, hfm, ⟨cvTa0, rest, hfs, b, hop⟩, hn⟩ := blockNestCtx_atF p₁ (consBlockInds p₁ isRec cvs 0 X₂).find? h3
  rw [h3']
  simp only [bind, Except.bind] at h ⊢
  have hfm' : ∀ cv ∈ ctx.formers, Res A₁ cv.type := by
    intro cv hcv; rw [hfm] at hcv
    simp only [BlockShape.formers, hp1m] at hcv
    obtain ⟨ms, hms, rfl⟩ := List.mem_map.mp hcv; exact hT ms hms
  have hpar : ResL A₁ ctx.params :=
    res_openPisAtFvars p₁.nP 0 (hfm' cvTa0 (by rw [hfm, hfs]; exact List.mem_cons_self ..)) hop
  have hlen : ctx.params.length = p₁.nP := openPisAtFvars_length _ hop
  have hh := res_nestHoles hpar hfm' hn
  -- the classes
  obtain ⟨⟨rd, Ms⟩, h4, h⟩ := exceptBind_ok h
  obtain ⟨h4', hMs, -, -⟩ := checkBlockClasses_ext hcA hxA F hpar (by omega) h4
  rw [show (atF ctx (consBlockInds p₁ isRec cvs 0 X₂).find?).params = ctx.params from rfl, h4']
  simp only [bind, Except.bind] at h ⊢
  -- positivity
  obtain ⟨⟨outs, pos⟩, h5, h⟩ := exceptBind_ok h
  rw [checkBlockPositivity_ext hcA hxA F p₁ (fun ms hm => by rw [hp1m] at hm; exact hT ms hm)
    (fun cs hcs c hc => by
      simp only [BlockShape.memberCtors] at hcs
      exact hCres cs hcs c hc) h5]
  simp only [bind, Except.bind] at h ⊢
  -- the seeds
  obtain ⟨st, h6, h⟩ := exceptBind_ok h
  have e7 : classSeeds (atF ctx (consBlockInds p₁ isRec cvs 0 X₂).find?) holes Ms = classSeeds ctx holes Ms := rfl
  rw [e7, nestSeeds_ext hcA hxA F hf _ _ _ (res_classSeeds hpar hh hMs) h6]
  simp only [pure, Except.pure, Except.ok.injEq] at h ⊢
  subst h
  refine ⟨rfl, hA, hxA, hcA, hp1m, hpar, by rw [hlen, hp1n], hMs,
    fun ms hm => hT ms hm, fun ms hm c hc => ⟨hCres _ (List.mem_map_of_mem (by rw [hp1m]; exact hm)) c hc,
      hCfr ms (by rw [hp1m]; exact hm) c hc⟩⟩

end ConPanqueque.Pipeline.IndExt
