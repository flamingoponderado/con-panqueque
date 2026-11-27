import ConPanqueque.Pipeline.IndExt.GenRec

/-! # The generated-recursor stage's output, read off an accepting run

An accepting `genRecCheck` at `C₁` returns recursors whose generated types resolve at `C₁` (the
`constsResolveF` guard of `classConstOk`), whose generated rules resolve at the installed family's
environment `consBlockRecsT p 0 out C₁` (they resolve at the rule-less recursors' environment by
`classRuleCheck`'s guard, and that environment's names are found in the installed one), and whose
classes list the input classes' constructors (`classesNfs` keeps `ctors`). -/

namespace ConPanqueque.Pipeline.IndExt

open ConLeche ConLeche.Verify ConPanqueque.Pipeline

set_option autoImplicit false

/-! ## The generated types -/

theorem classConstOk_res {C : Env} {F : Nat} {cv : ConstantVal}
    (h : classConstOk (m := CheckM) (fueledOps .verified F) (mkFEnv C) cv = .ok ()) : Res C cv.type := by
  unfold classConstOk at h
  rw [mkFEnv_find?, mkFEnv_env, constsResolveF_eq] at h
  simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  cases hr : cv.type.constsResolve C with
  | true => exact hr
  | false =>
    exfalso; rw [hr] at h
    repeat' split at h
    all_goals first | contradiction | (simp at h) | simp_all

theorem classRecTysOk_res {C : Env} {F : Nat} (g : ClassGen) (k : Nat) :
    ∀ (recs : List RecShape) (cvs : List ConstantVal) (cs : List Nat) (out : List ConstantVal),
      classRecTysOk (m := CheckM) (fueledOps .verified F) (mkFEnv C) g k recs cvs cs = .ok out →
      ∀ x ∈ out, Res C x.type
  | rc :: rcs, cvRi :: cvs, c :: cs, out, h => by
    unfold classRecTysOk at h
    obtain ⟨x, hx1, h⟩ := exceptBind_ok h
    obtain ⟨xs, hxs, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    have hrx : Res C x.type := by
      unfold classRecTyOk at hx1
      dsimp only at hx1
      by_cases c1 : (rc.tgt == (g.cls.getD c default).member.getD k) = true
      case neg => rw [ite_eq_right c1] at hx1; kill hx1
      rw [ite_eq_left c1] at hx1
      by_cases c2 : (rc.rP == g.nP + g.slots.length && rc.mI == rc.rP + (g.cls.getD c default).nIdx) = true
      case neg => rw [ite_eq_right c2] at hx1; kill hx1
      rw [ite_eq_left c2] at hx1
      obtain ⟨gty, -, hx1⟩ := exceptBind_ok hx1
      obtain ⟨u, hu, hx1⟩ := exceptBind_ok hx1
      simp only [pure, Except.pure, Except.ok.injEq] at hx1; subst hx1
      unfold classRecTyCheck at hu
      obtain ⟨u', hu', -⟩ := exceptBind_ok hu
      cases u'
      exact classConstOk_res hu'
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hrx
    · exact classRecTysOk_res g k rcs cvs cs xs hxs y hy
  | [], _, _, out, h => by
    unfold classRecTysOk at h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact fun _ h => nomatch h
  | _ :: _, [], _, _, h => by unfold classRecTysOk at h; kill h
  | _ :: _, _ :: _, [], _, h => by unfold classRecTysOk at h; kill h

/-! ## The generated rules -/

theorem classRuleCheck_res {C R : Env} {F : Nat} {cvR : ConstantVal} {n : Nat} {gen : Expr}
    (h : classRuleCheck (m := CheckM) (fueledOps .verified F) (mkFEnv C) (mkFEnv R) cvR n gen = .ok ()) :
    Res R gen := by
  unfold classRuleCheck at h
  simp only [mkFEnv_env, constsResolveF_eq] at h
  by_cases c1 : (gen.looseBVarsBounded 0 && !gen.hasFvar) = true
  case neg => rw [ite_eq_right c1] at h; kill h
  rw [ite_eq_left c1] at h
  by_cases c2 : gen.allLevelParamsDefined cvR.levelParams = true
  case neg => rw [ite_eq_right c2] at h; kill h
  rw [ite_eq_left c2] at h
  by_cases c3 : gen.constsResolve R = true
  case neg => rw [ite_eq_right c3] at h; kill h
  exact c3

theorem classRulesOk_res {C R : Env} {F : Nat} (g : ClassGen) (recOf : Nat → Option Name)
    (cvR : ConstantVal) (c : Nat) :
    ∀ (xs : List ClassCtor) (rs : List Expr),
      classRulesOk (m := CheckM) (fueledOps .verified F) (mkFEnv C) (mkFEnv R) g recOf cvR c xs = .ok rs →
      ∀ e ∈ rs, Res R e
  | [], rs, h => by
    unfold classRulesOk at h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact fun _ h => nomatch h
  | x :: xs, rs, h => by
    unfold classRulesOk at h
    obtain ⟨gen, -, h⟩ := exceptBind_ok h
    obtain ⟨r, hr, h⟩ := exceptBind_ok h
    obtain ⟨rs', hrs, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    unfold classRuleOk at hr
    obtain ⟨u, hu, hr⟩ := exceptBind_ok hr
    simp only [pure, Except.pure, Except.ok.injEq] at hr; subst hr
    cases u
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · exact classRuleCheck_res hu
    · exact classRulesOk_res g recOf cvR c xs rs' hrs e he

/-- Every record of the rule stage: its constant one of the zipped generated constants, its class
one of the generator's, its rules resolving at the rule environment. -/
theorem classRecsRulesOk_out {C R : Env} {F : Nat} (g : ClassGen) (recOf : Nat → Option Name) :
    ∀ (cvs : List ConstantVal) (cs : List Nat) (out : List (ConstantVal × TargetMajor × List Expr)),
      classRecsRulesOk (m := CheckM) (fueledOps .verified F) (mkFEnv C) (mkFEnv R) g recOf cvs cs = .ok out →
      out.map (·.1) = (cvs.zip cs).map (·.1) ∧
        ∀ x ∈ out, (∃ c, x.2.1 = g.cls.getD c default) ∧ ∀ e ∈ x.2.2, Res R e
  | cvG :: cvs, c :: cs, out, h => by
    unfold classRecsRulesOk at h
    obtain ⟨rhss, hr, h⟩ := exceptBind_ok h
    obtain ⟨xs, hxs, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    obtain ⟨ih1, ih2⟩ := classRecsRulesOk_out g recOf cvs cs xs hxs
    refine ⟨by simp only [List.map_cons, List.zip_cons_cons, ih1], ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨⟨c, rfl⟩, classRulesOk_res g recOf cvG c _ rhss hr⟩
    · exact ih2 x hx
  | [], _, out, h => by
    unfold classRecsRulesOk at h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact ⟨rfl, fun _ h => nomatch h⟩
  | _ :: _, [], out, h => by
    unfold classRecsRulesOk at h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact ⟨rfl, fun _ h => nomatch h⟩

/-! ## The classes' constructors -/

theorem classesNfs_ctors {env : Env} {F : Nat} {p : BlockShape} {formerTys : List Expr}
    {tbl : List NestCtorNf} :
    ∀ {Ms out : List TargetMajor},
      classesNfs (m := CheckM) (fueledOps .verified F) env p formerTys tbl Ms = .ok out →
      ∀ M' ∈ out, ∃ M ∈ Ms, M'.ctors = M.ctors
  | [], out, h => by
    unfold classesNfs at h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact fun _ h => nomatch h
  | M :: Ms, out, h => by
    unfold classesNfs at h
    obtain ⟨es, -, h⟩ := exceptBind_ok h
    obtain ⟨rest, hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    intro M' hM'
    rcases List.mem_cons.mp hM' with rfl | hM'
    · exact ⟨M, List.mem_cons_self .., rfl⟩
    · obtain ⟨M0, hM0, e⟩ := classesNfs_ctors hrest M' hM'
      exact ⟨M0, List.mem_cons_of_mem _ hM0, e⟩

/-! ## The installed family's environment -/

/-- The recursors `consBlockRecsT` pushes, newest first. -/
def bareT (p : BlockShape) : Nat → List (ConstantVal × TargetMajor × List Expr) → List ConstantInfo
  | _, [] => []
  | m, (cv, M, rhss) :: rest =>
    bareT p (m + 1) rest ++ [.recInfo cv (p.majorIdxAt m) (p.rulePrefixAt m)
      (recKExpected p M) (generatedRules (p.rulePrefixAt m) M rhss)]

theorem consBlockRecsT_eq (p : BlockShape) :
    ∀ (m : Nat) (L : List (ConstantVal × TargetMajor × List Expr)) (env : Env),
      consBlockRecsT p m L env = ⟨bareT p m L ++ env.consts, env.tables⟩
  | _, [], _ => rfl
  | m, (cv, M, rhss) :: rest, env => by
    simp only [consBlockRecsT, bareT]
    rw [consBlockRecsT_eq p (m + 1) rest]
    simp only [List.append_assoc, List.singleton_append]

theorem mem_bareT_name (p : BlockShape) :
    ∀ (m : Nat) (L : List (ConstantVal × TargetMajor × List Expr)) (x : ConstantVal × TargetMajor × List Expr),
      x ∈ L → x.1.name ∈ (bareT p m L).map (·.name)
  | _, [], _, h => nomatch h
  | m, (cv, M, rhss) :: rest, x, h => by
    simp only [bareT, List.map_append, List.mem_append, List.map_cons, List.map_nil, List.mem_singleton]
    rcases List.mem_cons.mp h with rfl | h
    · exact Or.inr rfl
    · exact Or.inl (mem_bareT_name p (m + 1) rest x h)

/-- Every name the rule-less recursors' environment finds, the installed family's finds. -/
theorem ruleEnv_find_consBlockRecsT {C : Env} (p : BlockShape) (Ms : List TargetMajor)
    (cvGs : List ConstantVal) (recCls : List Nat) (out : List (ConstantVal × TargetMajor × List Expr))
    (hout : out.map (·.1) = (cvGs.zip recCls).map (·.1)) (n : Name)
    (hn : ((ConLeche.Cached.ruleEnv p Ms cvGs recCls C).find? n).isSome = true) :
    ((consBlockRecsT p 0 out C).find? n).isSome = true := by
  unfold ConLeche.Cached.ruleEnv at hn
  rw [consBlockRecsBare_eq] at hn
  rw [consBlockRecsT_eq]
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
  rcases find?_prepend_mem hci with ⟨hm, rfl⟩ | ⟨-, h1⟩
  · obtain ⟨x, hxm, mI, rP, rfl⟩ := mem_bareR p 0 _ ci hm
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hxm
    have hy1 : y.1 ∈ out.map (·.1) := by
      rw [hout]; exact List.mem_map.mpr ⟨y, hy, rfl⟩
    obtain ⟨z, hz, ez⟩ := List.mem_map.mp hy1
    have := mem_bareT_name p 0 out z hz
    rw [ez] at this
    exact find?_mem_name this
  · exact find?_prepend_isSome (ts := C.tables) (by rw [h1]; rfl)

/-! ## The stage's output -/

theorem genRecCheck_outFacts {C₁ : Env} {F : Nat} {p : BlockShape} {nestedBit : Bool}
    {params : List Expr} {tbl : List NestCtorNf} {rd : ClassRead} {Ms : List TargetMajor}
    {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}
    (h : genRecCheck (m := CheckM) (fueledOps .verified F) (mkFEnv C₁) p nestedBit params tbl rd Ms block
      = .ok out)
    (hMs : ∀ M ∈ Ms, ∀ c ∈ M.ctors, ∃ cv nP nF T, C₁.find? c.1.name = some (.ctorInfo cv nP nF T)) :
    (∀ g ∈ out, Res C₁ g.1.type ∧ ∀ e ∈ g.2.2, Res (consBlockRecsT p 0 out C₁) e) ∧
    (∀ g ∈ out, ∀ c ∈ g.2.1.ctors, ∃ cv nP nF T, C₁.find? c.1.name = some (.ctorInfo cv nP nF T)) := by
  unfold genRecCheck at h
  obtain ⟨u, -, h⟩ := exceptBind_ok h
  obtain ⟨cvRis, -, h⟩ := exceptBind_ok h
  dsimp only at h
  by_cases g1 : 0 < p.k
  case neg => rw [ite_eq_right g1] at h; kill h
  rw [ite_eq_left g1] at h
  by_cases g2 : (p.large && !blockLargeElimAllowed p (nestedBit || Ms.any fun x => x.member.isNone)) = true
  case pos => rw [ite_eq_left g2] at h; kill h
  rw [ite_eq_right g2] at h
  simp only [mkFEnv_env] at h
  obtain ⟨Ms', hMs', h⟩ := exceptBind_ok h
  have hct := classesNfs_ctors hMs'
  obtain ⟨ctors, -, h⟩ := exceptBind_ok h
  by_cases g3 : ((List.filter ClassSlot.isMinor rd.slots).length == (List.map List.length ctors).sum) = true
  case neg => rw [ite_eq_right g3] at h; kill h
  rw [ite_eq_left g3] at h
  obtain ⟨ftc, -, h⟩ := exceptBind_ok h
  obtain ⟨pre, -, h⟩ := exceptBind_ok h
  obtain ⟨cvGs, hcv, h⟩ := exceptBind_ok h
  have hresG := classRecTysOk_res _ p.k p.recs cvRis rd.recCls cvGs hcv
  rw [ConLeche.Cached.classFeR_mkFEnv] at h
  obtain ⟨hfst, hall⟩ := classRecsRulesOk_out _ _ cvGs rd.recCls out h
  refine ⟨fun g hg => ⟨?_, fun e he => ?_⟩, fun g hg c hc => ?_⟩
  · have hg1 : g.1 ∈ (cvGs.zip rd.recCls).map (·.1) := by
      rw [← hfst]; exact List.mem_map.mpr ⟨g, hg, rfl⟩
    obtain ⟨y, hy, ey⟩ := List.mem_map.mp hg1
    rw [← ey]
    exact hresG _ (List.of_mem_zip hy).1
  · exact Expr.constsResolve_of_find
      (ruleEnv_find_consBlockRecsT p Ms' cvGs rd.recCls out hfst) ((hall g hg).2 e he)
  · obtain ⟨⟨i, ei⟩, -⟩ := hall g hg
    rw [ei] at hc
    simp only at hc
    rw [List.getD_eq_getElem?_getD] at hc
    cases hi : Ms'[i]? with
    | none => rw [hi] at hc; exact nomatch hc
    | some M' =>
      rw [hi, Option.getD_some] at hc
      obtain ⟨M, hM, e⟩ := hct M' (mem_of_getElem? hi)
      rw [e] at hc
      exact hMs M hM c hc

end ConPanqueque.Pipeline.IndExt
