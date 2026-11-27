import ConPanqueque.Pipeline.IndExt.Ctors
import ConPanqueque.Pipeline.IndExt.PosBase
import ConPanqueque.Pipeline.IndExt.InferRes
import ConLeche.Kernel.Inductives.GenRec
import ConLeche.Verify.Cached.GenRecC
import ConLeche.Verify.BridgeDecl

/-! # The generated-recursor stage at an extension

`genRecCheck` reads the environment through the checker's operations (the class matches'
inferences and comparisons, the generated constants' checks, the rules' inferences at the
rule-less recursors' environment) and a few lookups (the stream's recursors' freshness, an outside
class's stored former).  An accepting run at `C₁` is an accepting run at an extension `C₂`, with
the same output (`genRecCheck_ext`).  Resolution is read off the run (the constant checks'
`constsResolveF` guards, `inferType_ok_res`), except for the class matches' contexts: the
classes' parameter openers and the formers' types (`GenRecRes`). -/

namespace ConPanqueque.Pipeline.IndExt

open ConLeche ConLeche.Verify ConPanqueque.Pipeline

set_option autoImplicit false

variable {X₁ X₂ : Env}

/-! ## Free-variable annotations through the class matches' rewrites -/

theorem fvRes_replaceFVars_cover {env : Env} {f : Nat → Option Expr} {n : Nat}
    (hf : ∀ i, i < n → ∃ x, f i = some x ∧ FvRes env x) :
    ∀ (e : Expr), e.fvarRange ≤ n → FvRes env (e.replaceFVars f)
  | .bvar _, _ => trivial
  | .sort _, _ => trivial
  | .const _ _, _ => trivial
  | .lit _, _ => trivial
  | .fvar i ty, h => by
    obtain ⟨x, hx, hr⟩ := hf i (by simp only [Expr.fvarRange] at h; omega)
    simp only [Expr.replaceFVars, hx, Option.getD_some]; exact hr
  | .app a b, h => by
    simp only [Expr.fvarRange, Nat.max_le] at h
    exact ⟨fvRes_replaceFVars_cover hf a h.1, fvRes_replaceFVars_cover hf b h.2⟩
  | .lam a b, h => by
    simp only [Expr.fvarRange, Nat.max_le] at h
    exact ⟨fvRes_replaceFVars_cover hf a h.1, fvRes_replaceFVars_cover hf b h.2⟩
  | .forallE a b, h => by
    simp only [Expr.fvarRange, Nat.max_le] at h
    exact ⟨fvRes_replaceFVars_cover hf a h.1, fvRes_replaceFVars_cover hf b h.2⟩
  | .letE a v b, h => by
    simp only [Expr.fvarRange, Nat.max_le] at h
    exact ⟨fvRes_replaceFVars_cover hf a h.1.1, fvRes_replaceFVars_cover hf v h.1.2,
      fvRes_replaceFVars_cover hf b h.2⟩
  | .proj _ _ e, h => by
    simp only [Expr.fvarRange] at h
    exact fvRes_replaceFVars_cover hf e h

theorem fvRes_targetCanonParams {env : Env} {pfvs : List Expr} (hp : ResL env pfvs) {e : Expr}
    (h : e.fvarB ≤ pfvs.length) : FvRes env (targetCanonParams pfvs e) := by
  unfold targetCanonParams
  refine fvRes_replaceFVars_cover (fun i hi => ⟨pfvs[i], List.getElem?_eq_getElem hi,
    fvRes_of_res (hp _ (List.getElem_mem hi))⟩) e ?_
  rw [← Expr.fvarB_eq]; exact h

theorem fvRes_targetAbs {env : Env} (names : List Name) (lvls : List Level) {holes : List Expr}
    (hh : ∀ x ∈ holes, FvRes env x) :
    ∀ (e : Expr), FvRes env e → FvRes env (targetAbs names lvls holes e)
  | .bvar _, _ => trivial
  | .sort _, _ => trivial
  | .lit _, _ => trivial
  | .fvar _ _, h => h
  | .const n us, h => by
    simp only [targetAbs]
    split
    · split
      · rename_i t _
        rw [List.getD_eq_getElem?_getD]
        cases ht : holes[t]? with
        | none => exact h
        | some x => exact hh x (mem_of_getElem? ht)
      · exact h
    · exact h
  | .app a b, h => ⟨fvRes_targetAbs names lvls hh a h.1, fvRes_targetAbs names lvls hh b h.2⟩
  | .lam a b, h => ⟨fvRes_targetAbs names lvls hh a h.1, fvRes_targetAbs names lvls hh b h.2⟩
  | .forallE a b, h => ⟨fvRes_targetAbs names lvls hh a h.1, fvRes_targetAbs names lvls hh b h.2⟩
  | .letE a v b, h => ⟨fvRes_targetAbs names lvls hh a h.1, fvRes_targetAbs names lvls hh v h.2.1,
      fvRes_targetAbs names lvls hh b h.2.2⟩
  | .proj _ _ e, h => fvRes_targetAbs names lvls hh e h

theorem fvRes_targetHoles {env : Env} {formerTys : List Expr} (hf : ResL env formerTys) (base : Nat) :
    ∀ x ∈ targetHoles formerTys base, FvRes env x := by
  intro x hx
  simp only [targetHoles, List.mem_map, List.mem_range] at hx
  obtain ⟨t, ht, rfl⟩ := hx
  show Res env (formerTys.getD t default)
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
  exact hf _ (List.getElem_mem ht)

/-! ## The class matches -/

theorem targetParamsDefEq_ext (hx : EnvExt X₁ X₂) (F d : Nat) (absM : Expr → Expr) (pfvs : List Expr)
    (habs : ∀ e, FvRes X₁ e → FvRes X₁ (absM e)) (hp : ResL X₁ pfvs) :
    ∀ (as bs : List Expr) (r : Bool),
      targetParamsDefEq (m := CheckM) (fueledOps .verified F) X₁ d absM pfvs as bs = .ok r →
      targetParamsDefEq (m := CheckM) (fueledOps .verified F) X₂ d absM pfvs as bs = .ok r
  | [], [], r, h => h
  | [], _ :: _, r, h => h
  | _ :: _, [], r, h => h
  | a :: as, b :: bs, r, h => by
    unfold targetParamsDefEq at h ⊢
    have ih := targetParamsDefEq_ext hx F d absM pfvs habs hp as bs r
    split at h
    · rename_i c
      rw [ite_eq_left c]
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at c
      have hfa := habs _ (fvRes_targetCanonParams hp c.1.2)
      have hfb := habs _ (fvRes_targetCanonParams hp c.2)
      dsimp only at h ⊢
      split at h
      · rename_i e
        rw [ite_eq_left e]; exact ih h
      · rename_i e
        rw [ite_eq_right e]
        obtain ⟨ta, hta, h⟩ := exceptBind_ok h
        have hra := inferType_ok_res hfa hta
        refine bind_ok_of (by rw [(ops_infer hx F d hra).1]; exact hta) ?_
        obtain ⟨tb, htb, h⟩ := exceptBind_ok h
        have hrb := inferType_ok_res hfb htb
        refine bind_ok_of (by rw [(ops_infer hx F d hrb).1]; exact htb) ?_
        rw [ops_defeq hx F d hra hrb]
        obtain ⟨bq, hbq, h⟩ := exceptBind_ok h
        refine bind_ok_of hbq ?_
        split at h
        · rename_i hb; rw [ite_eq_left hb]; exact ih h
        · rename_i hb; rw [ite_eq_right hb]; exact h
    · rename_i c
      rw [ite_eq_right c]; exact h

theorem targetClassMatch_ext (hx : EnvExt X₁ X₂) (F : Nat) (p : BlockShape) (formerTys pfvs : List Expr)
    (us : List Level) (ds : List Expr) (lvls : List Level) (eds : List Expr)
    (hf : ResL X₁ formerTys) (hp : ResL X₁ pfvs) {r : Bool}
    (h : targetClassMatch (m := CheckM) (fueledOps .verified F) X₁ p formerTys pfvs us ds lvls eds = .ok r) :
    targetClassMatch (m := CheckM) (fueledOps .verified F) X₂ p formerTys pfvs us ds lvls eds = .ok r := by
  unfold targetClassMatch at h ⊢
  split at h
  · rename_i c
    rw [ite_eq_left c]
    exact targetParamsDefEq_ext hx F _ _ pfvs
      (fvRes_targetAbs _ _ (fvRes_targetHoles hf _)) hp ds eds r h
  · rename_i c
    rw [ite_eq_right c]; exact h

theorem targetMajorNfs_ext (hx : EnvExt X₁ X₂) (F : Nat) (p : BlockShape) (formerTys pfvs : List Expr)
    (us : List Level) (ds : List Expr) (ctors : List (ConstantVal × Nat))
    (hf : ResL X₁ formerTys) (hp : ResL X₁ pfvs) :
    ∀ (tbl r : List NestCtorNf),
      targetMajorNfs (m := CheckM) (fueledOps .verified F) X₁ p formerTys pfvs us ds ctors tbl = .ok r →
      targetMajorNfs (m := CheckM) (fueledOps .verified F) X₂ p formerTys pfvs us ds ctors tbl = .ok r
  | [], r, h => h
  | e :: es, r, h => by
    unfold targetMajorNfs at h ⊢
    obtain ⟨rest, hrest, h⟩ := exceptBind_ok h
    refine bind_ok_of (targetMajorNfs_ext hx F p formerTys pfvs us ds ctors hf hp es rest hrest) ?_
    split at h
    · rename_i c
      rw [ite_eq_left c]
      obtain ⟨b, hb, h⟩ := exceptBind_ok h
      exact bind_ok_of (targetClassMatch_ext hx F p formerTys pfvs us ds _ _ hf hp hb) h
    · rename_i c
      rw [ite_eq_right c]; exact h

theorem targetK53_ext (hx : EnvExt X₁ X₂) (F : Nat) (p : BlockShape) (formerTys : List Expr)
    (Mc : TargetMajor) (tele : List Expr) (majDom f : Expr)
    (hf : ResL X₁ formerTys) (hp : ResL X₁ Mc.pfvs) {r : Bool}
    (h : targetK53 (m := CheckM) (fueledOps .verified F) X₁ p formerTys Mc tele majDom f = .ok r) :
    targetK53 (m := CheckM) (fueledOps .verified F) X₂ p formerTys Mc tele majDom f = .ok r := by
  unfold targetK53 at h ⊢
  cases hs : f.stripPis tele.length with
  | none => simp only [hs] at h ⊢; exact h
  | some q =>
    obtain ⟨teleW, leafW⟩ := q
    simp only [hs] at h ⊢
    split at h
    · rename_i c
      rw [ite_eq_left c]; exact h
    · rename_i c
      rw [ite_eq_right c]
      split at h
      · rename_i I' us' I _ hA hB
        try simp only [hA, hB]
        split at h
        · rename_i c2
          rw [ite_eq_left c2]
          exact targetClassMatch_ext hx F p formerTys _ _ _ _ _ hf hp h
        · rename_i c2
          rw [ite_eq_right c2]; exact h
      · exact h

/-! ## The classes' constructors -/

/-- Every class's parameter openers resolve. -/
def PfvsRes (env : Env) (Ms : List TargetMajor) : Prop := ∀ M ∈ Ms, ResL env M.pfvs

theorem pfvsRes_getD {env : Env} {Ms : List TargetMajor} (h : PfvsRes env Ms) (t : Nat) :
    ResL env (Ms.getD t default).pfvs := by
  rw [List.getD_eq_getElem?_getD]
  cases ht : Ms[t]? with
  | none => intro x hx; exact nomatch hx
  | some M => exact h M (mem_of_getElem? ht)

theorem classNodesAgree_ext (hx : EnvExt X₁ X₂) (F : Nat) (p : BlockShape) (formerTys : List Expr)
    (Mc : TargetMajor) (tele : List Expr) (leaf : Expr) (fvs : List Expr) (i : Nat) (ctor : Name)
    (hf : ResL X₁ formerTys) (hp : ResL X₁ Mc.pfvs) :
    ∀ (E : List NestCtorNf),
      classNodesAgree (m := CheckM) (fueledOps .verified F) X₁ p formerTys Mc tele leaf fvs i ctor E = .ok () →
      classNodesAgree (m := CheckM) (fueledOps .verified F) X₂ p formerTys Mc tele leaf fvs i ctor E = .ok ()
  | [], _ => rfl
  | e :: es, h => by
    unfold classNodesAgree at h ⊢
    cases hq : ((targetPiDomsWith fvs e.ty).getD [])[i]? with
    | none => simp only [hq] at h; kill h
    | some f =>
      simp only [hq] at h ⊢
      obtain ⟨b, hb, h⟩ := exceptBind_ok h
      refine bind_ok_of (targetK53_ext hx F p formerTys Mc tele leaf f hf hp hb) ?_
      split at h
      · rename_i c
        rw [ite_eq_left c]
        exact classNodesAgree_ext hx F p formerTys Mc tele leaf fvs i ctor hf hp es h
      · kill h

theorem classFieldsAgree_ext (hx : EnvExt X₁ X₂) (F : Nat) (p : BlockShape) (formerTys : List Expr)
    (Ms : List TargetMajor) (fvs : List Expr) (ctor : Name) (E : List NestCtorNf)
    (hf : ResL X₁ formerTys) (hp : PfvsRes X₁ Ms) :
    ∀ (i : Nat) (ks : List ClassField),
      classFieldsAgree (m := CheckM) (fueledOps .verified F) X₁ p formerTys Ms fvs ctor E i ks = .ok () →
      classFieldsAgree (m := CheckM) (fueledOps .verified F) X₂ p formerTys Ms fvs ctor E i ks = .ok ()
  | _, [], _ => rfl
  | i, .ordinary :: ks, h => by
    unfold classFieldsAgree at h ⊢
    exact classFieldsAgree_ext hx F p formerTys Ms fvs ctor E hf hp (i + 1) ks h
  | i, .recursive t tele :: ks, h => by
    unfold classFieldsAgree at h ⊢
    obtain ⟨q, hq, h⟩ := exceptBind_ok h
    refine bind_ok_of hq ?_
    obtain ⟨teleB, leaf⟩ := q
    dsimp only at h ⊢
    split at h
    case isFalse => kill h
    rename_i c
    rw [ite_eq_left c]
    obtain ⟨u2, hu2, h⟩ := exceptBind_ok h
    cases u2
    refine bind_ok_of (classNodesAgree_ext hx F p formerTys _ teleB leaf fvs i ctor hf
      (pfvsRes_getD hp t) E hu2) ?_
    exact classFieldsAgree_ext hx F p formerTys Ms fvs ctor E hf hp (i + 1) ks h

theorem classCtorOf_ext (hx : EnvExt X₁ X₂) (F : Nat) (p : BlockShape) (formerTys : List Expr)
    (rd : ClassRead) (Ms : List TargetMajor) (c : Nat) (ctor : ConstantVal × Nat)
    (hf : ResL X₁ formerTys) (hp : PfvsRes X₁ Ms) {x : ClassCtor}
    (h : classCtorOf (m := CheckM) (fueledOps .verified F) X₁ p formerTys rd Ms c ctor = .ok x) :
    classCtorOf (m := CheckM) (fueledOps .verified F) X₂ p formerTys rd Ms c ctor = .ok x := by
  unfold classCtorOf at h ⊢
  obtain ⟨e0, he0, h⟩ := exceptBind_ok h
  refine bind_ok_of he0 ?_
  obtain ⟨q, hq, h⟩ := exceptBind_ok h
  refine bind_ok_of hq ?_
  obtain ⟨_, ihs⟩ := q
  dsimp only at h ⊢
  obtain ⟨q, hq, h⟩ := exceptBind_ok h
  refine bind_ok_of hq ?_
  obtain ⟨fvs, _⟩ := q
  dsimp only at h ⊢
  obtain ⟨kinds, hk, h⟩ := exceptBind_ok h
  refine bind_ok_of hk ?_
  obtain ⟨u, hu, h⟩ := exceptBind_ok h
  cases u
  exact bind_ok_of (classFieldsAgree_ext hx F p formerTys Ms fvs _ _ hf hp 0 kinds hu) h

theorem classCtorsOf_ext (hx : EnvExt X₁ X₂) (F : Nat) (p : BlockShape) (formerTys : List Expr)
    (rd : ClassRead) (Ms : List TargetMajor) (c : Nat) (hf : ResL X₁ formerTys) (hp : PfvsRes X₁ Ms) :
    ∀ (cs : List (ConstantVal × Nat)) (xs : List ClassCtor),
      classCtorsOf (m := CheckM) (fueledOps .verified F) X₁ p formerTys rd Ms c cs = .ok xs →
      classCtorsOf (m := CheckM) (fueledOps .verified F) X₂ p formerTys rd Ms c cs = .ok xs
  | [], _, h => h
  | ctor :: cs, xs, h => by
    unfold classCtorsOf at h ⊢
    obtain ⟨x, hx1, h⟩ := exceptBind_ok h
    refine bind_ok_of (classCtorOf_ext hx F p formerTys rd Ms c ctor hf hp hx1) ?_
    obtain ⟨xs', hxs, h⟩ := exceptBind_ok h
    exact bind_ok_of (classCtorsOf_ext hx F p formerTys rd Ms c hf hp cs xs' hxs) h

theorem classesCtors_ext (hx : EnvExt X₁ X₂) (F : Nat) (p : BlockShape) (formerTys : List Expr)
    (rd : ClassRead) (Ms : List TargetMajor) (hf : ResL X₁ formerTys) (hp : PfvsRes X₁ Ms) :
    ∀ (c : Nat) (l : List TargetMajor) (xss : List (List ClassCtor)),
      classesCtors (m := CheckM) (fueledOps .verified F) X₁ p formerTys rd Ms c l = .ok xss →
      classesCtors (m := CheckM) (fueledOps .verified F) X₂ p formerTys rd Ms c l = .ok xss
  | _, [], _, h => h
  | c, M :: rest, xss, h => by
    unfold classesCtors at h ⊢
    obtain ⟨xs, hxs, h⟩ := exceptBind_ok h
    refine bind_ok_of (classCtorsOf_ext hx F p formerTys rd Ms c hf hp _ xs hxs) ?_
    obtain ⟨xss', hxss, h⟩ := exceptBind_ok h
    exact bind_ok_of (classesCtors_ext hx F p formerTys rd Ms hf hp (c + 1) rest xss' hxss) h

/-! ## The classes' table entries -/

theorem classesNfs_ext (hx : EnvExt X₁ X₂) (F : Nat) (p : BlockShape) (formerTys : List Expr)
    (tbl : List NestCtorNf) (hf : ResL X₁ formerTys) :
    ∀ (Ms out : List TargetMajor), PfvsRes X₁ Ms →
      classesNfs (m := CheckM) (fueledOps .verified F) X₁ p formerTys tbl Ms = .ok out →
      classesNfs (m := CheckM) (fueledOps .verified F) X₂ p formerTys tbl Ms = .ok out
  | [], _, _, h => h
  | M :: Ms, out, hp, h => by
    unfold classesNfs at h ⊢
    obtain ⟨es, hes, h⟩ := exceptBind_ok h
    refine bind_ok_of (targetMajorNfs_ext hx F p formerTys M.pfvs M.lvls M.ds M.ctors hf
      (hp M (List.mem_cons_self ..)) tbl es hes) ?_
    obtain ⟨rest, hrest, h⟩ := exceptBind_ok h
    exact bind_ok_of (classesNfs_ext hx F p formerTys tbl hf Ms rest
      (fun M' hM' => hp M' (List.mem_cons_of_mem _ hM')) hrest) h

/-- The table entries keep every class's openers. -/
theorem classesNfs_pfvs {env : Env} {F : Nat} {p : BlockShape} {formerTys : List Expr}
    {tbl : List NestCtorNf} {X : Env} :
    ∀ {Ms out : List TargetMajor}, PfvsRes X Ms →
      classesNfs (m := CheckM) (fueledOps .verified F) env p formerTys tbl Ms = .ok out → PfvsRes X out
  | [], out, _, h => by
    unfold classesNfs at h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    intro M hM; exact nomatch hM
  | M :: Ms, out, hp, h => by
    unfold classesNfs at h
    obtain ⟨es, -, h⟩ := exceptBind_ok h
    obtain ⟨rest, hrest, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    have ih := classesNfs_pfvs (fun M' hM' => hp M' (List.mem_cons_of_mem _ hM')) hrest
    intro M' hM'
    rcases List.mem_cons.mp hM' with rfl | hM'
    · exact hp M (List.mem_cons_self ..)
    · exact ih M' hM'

-- One environment-free guard: split `h`, close the failing branch, take the passing branch in
-- the goal.
set_option hygiene false in
local macro "guard_step" : tactic =>
  `(tactic| (split at h <;> first
    | (kill h)
    | (rename_i c; first | rw [ite_eq_left c] | rw [ite_eq_right c])))

/-! ## The stream's recursors -/

theorem classStreamRecs_ext (hx : EnvExt X₁ X₂) (F : Nat) :
    ∀ (recs : List RecShape) (cvs : List ConstantVal), (∀ rc ∈ recs, X₂.find? rc.cvR.name = none) →
      classStreamRecs (m := CheckM) (fueledOps .verified F) (mkFEnv X₁) recs = .ok cvs →
      classStreamRecs (m := CheckM) (fueledOps .verified F) (mkFEnv X₂) recs = .ok cvs ∧
        ∀ cv ∈ cvs, Res X₁ cv.type
  | [], cvs, _, h => by
    unfold classStreamRecs at h ⊢
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact ⟨rfl, fun _ h => nomatch h⟩
  | rc :: rcs, cvs, hfr, h => by
    unfold classStreamRecs at h ⊢
    obtain ⟨u, hc, h⟩ := exceptBind_ok h
    cases u
    rw [checkConstantValF_eq] at hc ⊢
    have hr := (checkConstantVal_res F X₁ _ _ _ _ hc).1
    refine ⟨bind_ok_of (checkConstantVal_ext hx F _ _ _ _ (hfr rc (List.mem_cons_self ..)) hc) ?_, ?_⟩
    · obtain ⟨cvs', hcvs, h⟩ := exceptBind_ok h
      exact bind_ok_of (classStreamRecs_ext hx F rcs cvs'
        (fun rc' h' => hfr rc' (List.mem_cons_of_mem _ h')) hcvs).1 h
    · obtain ⟨cvs', hcvs, h⟩ := exceptBind_ok h
      simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
      have ih := (classStreamRecs_ext hx F rcs cvs'
        (fun rc' h' => hfr rc' (List.mem_cons_of_mem _ h')) hcvs).2
      intro cv hcv
      rcases List.mem_cons.mp hcv with rfl | hcv
      · exact hr
      · exact ih cv hcv

/-! ## The classes' formers -/

theorem classFormerTy_ext (hx : EnvExt X₁ X₂) (F : Nat) (formers : List ConstantVal) (M : TargetMajor)
    {ty : Expr} (h : classFormerTy (m := CheckM) (fueledOps .verified F) (mkFEnv X₁) formers M = .ok ty) :
    classFormerTy (m := CheckM) (fueledOps .verified F) (mkFEnv X₂) formers M = .ok ty := by
  unfold classFormerTy at h ⊢
  cases hm : M.member with
  | some t => simp only [hm] at h ⊢; exact h
  | none =>
    simp only [hm, mkFEnv_find?, mkFEnv_env] at h ⊢
    cases hI : X₁.find? M.ind with
    | none => simp only [hI] at h; kill h
    | some ci =>
      rw [hx.find _ _ hI]
      simp only [hI] at h
      cases ci
      case indInfo cv caps =>
        simp only at h ⊢
        rw [ConLeche.Model.familyTelescope_ext hx F (cv := cv) caps (hx.facts.type hI)]
        exact h
      all_goals kill h

theorem mapM_ok_of {α β : Type} {f g : α → CheckM β} (hfg : ∀ a b, f a = .ok b → g a = .ok b) :
    ∀ (l : List α) (r : List β), l.mapM f = .ok r → l.mapM g = .ok r
  | [], r, h => by simpa only [List.mapM_nil] using h
  | a :: l, r, h => by
    rw [List.mapM_cons] at h ⊢
    obtain ⟨b, hb, h⟩ := exceptBind_ok h
    refine bind_ok_of (hfg a b hb) ?_
    obtain ⟨bs, hbs, h⟩ := exceptBind_ok h
    exact bind_ok_of (mapM_ok_of hfg l bs hbs) h

/-! ## The generated types -/

theorem classConstOk_ext (hx : EnvExt X₁ X₂) (F : Nat) (cv : ConstantVal)
    (hfr : X₂.find? cv.name = none)
    (h : classConstOk (m := CheckM) (fueledOps .verified F) (mkFEnv X₁) cv = .ok ()) :
    classConstOk (m := CheckM) (fueledOps .verified F) (mkFEnv X₂) cv = .ok () ∧ Res X₁ cv.type := by
  unfold classConstOk at h ⊢
  rw [mkFEnv_find?, mkFEnv_env, constsResolveF_eq] at h
  rw [mkFEnv_find?, mkFEnv_env, constsResolveF_eq]
  simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h ⊢
  cases hr : cv.type.constsResolve X₁ with
  | false =>
    exfalso; rw [hr] at h
    repeat' split at h
    all_goals first | contradiction | (simp at h) | simp_all
  | true =>
    refine ⟨?_, hr⟩
    have hr2 := res_ext hx hr
    rw [hr] at h; rw [hr2, hfr]
    have hf1 : X₁.find? cv.name = none := by
      cases hc : X₁.find? cv.name with
      | none => rfl
      | some ci => rw [hc] at h; simp at h
    rw [hf1] at h
    rw [(ops_infer hx F 0 hr).1]
    cases hi : (fueledOps .verified F).inferType X₁ 0 cv.type with
    | error e => simp only [hi] at h ⊢; exact h
    | ok s =>
      simp only [hi] at h ⊢
      rw [ops_ensureSort hx F 0 ((ops_infer hx F 0 hr).2 s hi)]
      exact h

theorem classRecTyCheck_ext (hx : EnvExt X₁ X₂) (F : Nat) (cvRi cvG : ConstantVal)
    (hri : Res X₁ cvRi.type) (hfr : X₂.find? cvG.name = none)
    (h : classRecTyCheck (m := CheckM) (fueledOps .verified F) (mkFEnv X₁) cvRi cvG = .ok ()) :
    classRecTyCheck (m := CheckM) (fueledOps .verified F) (mkFEnv X₂) cvRi cvG = .ok () := by
  unfold classRecTyCheck at h ⊢
  obtain ⟨u, hu, h⟩ := exceptBind_ok h
  cases u
  obtain ⟨hu2, hrg⟩ := classConstOk_ext hx F cvG hfr hu
  refine bind_ok_of hu2 ?_
  simp only [mkFEnv_env] at h ⊢
  rw [ops_defeq hx F 0 hri hrg]
  exact h

theorem classRecTyOk_ext (hx : EnvExt X₁ X₂) (F : Nat) (g : ClassGen) (k : Nat) (rc : RecShape)
    (cvRi : ConstantVal) (c : Nat) (hri : Res X₁ cvRi.type) (hfr : X₂.find? rc.cvR.name = none)
    {x : ConstantVal}
    (h : classRecTyOk (m := CheckM) (fueledOps .verified F) (mkFEnv X₁) g k rc cvRi c = .ok x) :
    classRecTyOk (m := CheckM) (fueledOps .verified F) (mkFEnv X₂) g k rc cvRi c = .ok x ∧
      x.name = rc.cvR.name := by
  unfold classRecTyOk at h ⊢
  dsimp only at h ⊢
  by_cases c1 : (rc.tgt == (g.cls.getD c default).member.getD k) = true
  case neg => rw [ite_eq_right c1] at h; kill h
  rw [ite_eq_left c1] at h ⊢
  by_cases c2 : (rc.rP == g.nP + g.slots.length && rc.mI == rc.rP + (g.cls.getD c default).nIdx) = true
  case neg => rw [ite_eq_right c2] at h; kill h
  rw [ite_eq_left c2] at h ⊢
  obtain ⟨gty, hg, h⟩ := exceptBind_ok h
  obtain ⟨u, hu, h⟩ := exceptBind_ok h
  cases u
  simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
  exact ⟨bind_ok_of hg (bind_ok_of (classRecTyCheck_ext hx F cvRi _ hri hfr hu) rfl), rfl⟩

theorem classRecTysOk_ext (hx : EnvExt X₁ X₂) (F : Nat) (g : ClassGen) (k : Nat) :
    ∀ (recs : List RecShape) (cvs : List ConstantVal) (cs : List Nat) (out : List ConstantVal),
      (∀ cv ∈ cvs, Res X₁ cv.type) → (∀ rc ∈ recs, X₂.find? rc.cvR.name = none) →
      classRecTysOk (m := CheckM) (fueledOps .verified F) (mkFEnv X₁) g k recs cvs cs = .ok out →
      classRecTysOk (m := CheckM) (fueledOps .verified F) (mkFEnv X₂) g k recs cvs cs = .ok out ∧
        ∀ x ∈ out, ∃ rc ∈ recs, x.name = rc.cvR.name
  | rc :: rcs, cvRi :: cvs, c :: cs, out, hri, hfr, h => by
    unfold classRecTysOk at h ⊢
    obtain ⟨x, hx1, h⟩ := exceptBind_ok h
    obtain ⟨hx2, hn⟩ := classRecTyOk_ext hx F g k rc cvRi c (hri _ (List.mem_cons_self ..))
      (hfr _ (List.mem_cons_self ..)) hx1
    obtain ⟨xs, hxs, h⟩ := exceptBind_ok h
    obtain ⟨hxs2, hns⟩ := classRecTysOk_ext hx F g k rcs cvs cs xs
      (fun cv h' => hri cv (List.mem_cons_of_mem _ h')) (fun rc' h' => hfr rc' (List.mem_cons_of_mem _ h')) hxs
    refine ⟨bind_ok_of hx2 (bind_ok_of hxs2 h), ?_⟩
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact ⟨rc, List.mem_cons_self .., hn⟩
    · obtain ⟨rc', hrc', e⟩ := hns y hy
      exact ⟨rc', List.mem_cons_of_mem _ hrc', e⟩
  | [], _, _, out, _, _, h => by
    unfold classRecTysOk at h
    simp only [pure, Except.pure, Except.ok.injEq] at h; subst h
    exact ⟨rfl, fun _ h => nomatch h⟩
  | _ :: _, [], _, _, _, _, h => by unfold classRecTysOk at h; kill h
  | _ :: _, _ :: _, [], _, _, _, h => by unfold classRecTysOk at h; kill h

/-! ## The generated rules -/

theorem classRuleCheck_ext (hx : EnvExt X₁ X₂) {R₁ R₂ : Env} (hxR : EnvExt R₁ R₂) (F : Nat)
    (cvR : ConstantVal) (n : Nat) (gen : Expr)
    (h : classRuleCheck (m := CheckM) (fueledOps .verified F) (mkFEnv X₁) (mkFEnv R₁) cvR n gen = .ok ()) :
    classRuleCheck (m := CheckM) (fueledOps .verified F) (mkFEnv X₂) (mkFEnv R₂) cvR n gen = .ok () := by
  unfold classRuleCheck at h ⊢
  simp only [mkFEnv_env, constsResolveF_eq] at h ⊢
  by_cases c1 : (gen.looseBVarsBounded 0 && !gen.hasFvar) = true
  case neg => rw [ite_eq_right c1] at h; kill h
  rw [ite_eq_left c1] at h ⊢
  by_cases c2 : gen.allLevelParamsDefined cvR.levelParams = true
  case neg => rw [ite_eq_right c2] at h; kill h
  rw [ite_eq_left c2] at h ⊢
  by_cases c3 : gen.constsResolve R₁ = true
  case neg => rw [ite_eq_right c3] at h; kill h
  rw [ite_eq_left c3] at h
  rw [ite_eq_left (res_ext hxR c3)]
  obtain ⟨t, ht, h⟩ := exceptBind_ok h
  refine bind_ok_of (by rw [(ops_infer hxR F 0 c3).1]; exact ht) ?_
  obtain ⟨q, hq, h⟩ := exceptBind_ok h
  refine bind_ok_of hq ?_
  obtain ⟨rbs, _⟩ := q
  dsimp only at h ⊢
  by_cases c4 : (rbs.all fun b => b.constsResolve X₁) = true
  case neg => rw [ite_eq_right c4] at h; kill h
  have c4' : (rbs.all fun b => b.constsResolve X₂) = true := by
    rw [List.all_eq_true] at c4 ⊢
    exact fun b hb => res_ext hx (c4 b hb)
  rw [ite_eq_left c4']
  rfl

theorem classRulesOk_ext (hx : EnvExt X₁ X₂) {R₁ R₂ : Env} (hxR : EnvExt R₁ R₂) (F : Nat) (g : ClassGen)
    (recOf : Nat → Option Name) (cvR : ConstantVal) (c : Nat) :
    ∀ (xs : List ClassCtor) (rs : List Expr),
      classRulesOk (m := CheckM) (fueledOps .verified F) (mkFEnv X₁) (mkFEnv R₁) g recOf cvR c xs = .ok rs →
      classRulesOk (m := CheckM) (fueledOps .verified F) (mkFEnv X₂) (mkFEnv R₂) g recOf cvR c xs = .ok rs
  | [], _, h => h
  | x :: xs, rs, h => by
    unfold classRulesOk at h ⊢
    obtain ⟨gen, hgen, h⟩ := exceptBind_ok h
    refine bind_ok_of hgen ?_
    obtain ⟨r, hr, h⟩ := exceptBind_ok h
    refine bind_ok_of (?_ : classRuleOk (m := CheckM) (fueledOps .verified F) (mkFEnv X₂) (mkFEnv R₂)
      cvR _ gen = .ok r) ?_
    · unfold classRuleOk at hr ⊢
      obtain ⟨u, hu, hr⟩ := exceptBind_ok hr
      cases u
      exact bind_ok_of (classRuleCheck_ext hx hxR F cvR _ gen hu) hr
    obtain ⟨rs', hrs, h⟩ := exceptBind_ok h
    exact bind_ok_of (classRulesOk_ext hx hxR F g recOf cvR c xs rs' hrs) h

theorem classRecsRulesOk_ext (hx : EnvExt X₁ X₂) {R₁ R₂ : Env} (hxR : EnvExt R₁ R₂) (F : Nat)
    (g : ClassGen) (recOf : Nat → Option Name) :
    ∀ (cvs : List ConstantVal) (cs : List Nat) (out : List (ConstantVal × TargetMajor × List Expr)),
      classRecsRulesOk (m := CheckM) (fueledOps .verified F) (mkFEnv X₁) (mkFEnv R₁) g recOf cvs cs = .ok out →
      classRecsRulesOk (m := CheckM) (fueledOps .verified F) (mkFEnv X₂) (mkFEnv R₂) g recOf cvs cs = .ok out
  | cvG :: cvs, c :: cs, out, h => by
    unfold classRecsRulesOk at h ⊢
    obtain ⟨rhss, hr, h⟩ := exceptBind_ok h
    refine bind_ok_of (classRulesOk_ext hx hxR F g recOf cvG c _ rhss hr) ?_
    obtain ⟨xs, hxs, h⟩ := exceptBind_ok h
    exact bind_ok_of (classRecsRulesOk_ext hx hxR F g recOf cvs cs xs hxs) h
  | [], _, _, h => h
  | _ :: _, [], _, h => h

/-! ## The rule-less recursors' environment at an extension -/

/-- The rule-less recursors `consBlockRecsBare` pushes, newest first. -/
def bareR (p : BlockShape) : Nat → List (ConstantVal × Nat) → List ConstantInfo
  | _, [] => []
  | m, (cv, _) :: rest =>
    bareR p (m + 1) rest ++ [.recInfo cv (p.majorIdxAt m) (p.rulePrefixAt m) false []]

theorem consBlockRecsBare_eq (p : BlockShape) :
    ∀ (m : Nat) (L : List (ConstantVal × Nat)) (env : Env),
      consBlockRecsBare p m L env = ⟨bareR p m L ++ env.consts, env.tables⟩
  | _, [], _ => rfl
  | m, (cv, n) :: rest, env => by
    simp only [consBlockRecsBare, bareR]
    rw [consBlockRecsBare_eq p (m + 1) rest]
    simp only [List.append_assoc, List.singleton_append]

theorem mem_bareR (p : BlockShape) :
    ∀ (m : Nat) (L : List (ConstantVal × Nat)) (c : ConstantInfo), c ∈ bareR p m L →
      ∃ x ∈ L, ∃ mI rP, c = .recInfo x.1 mI rP false []
  | _, [], c, h => nomatch h
  | m, (cv, n) :: rest, c, h => by
    simp only [bareR, List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · obtain ⟨x, hx, mI, rP, e⟩ := mem_bareR p (m + 1) rest c h
      exact ⟨x, List.mem_cons_of_mem _ hx, mI, rP, e⟩
    · exact ⟨(cv, n), List.mem_cons_self .., _, _, rfl⟩

/-- **The rule-less recursors' environments are an extension**: fresh `NameOK` names at `X₂`, the
pushed `X₁` side well formed. -/
theorem ruleEnv_ext (hx : EnvExt X₁ X₂) (ht2 : TablesStored X₂) (p : BlockShape) (Ms : List TargetMajor)
    (cvGs : List ConstantVal) (recCls : List Nat)
    (hfr : ∀ cv ∈ cvGs, NameOK cv.name ∧ X₂.find? cv.name = none)
    (hw : EnvWF (ConLeche.Cached.ruleEnv p Ms cvGs recCls X₁)) :
    EnvExt (ConLeche.Cached.ruleEnv p Ms cvGs recCls X₁) (ConLeche.Cached.ruleEnv p Ms cvGs recCls X₂) := by
  unfold ConLeche.Cached.ruleEnv at hw ⊢
  rw [consBlockRecsBare_eq] at hw ⊢
  rw [consBlockRecsBare_eq]
  have hmem := mem_bareR p 0 ((cvGs.zip recCls).map fun (x : ConstantVal × Nat) => (x.1, (Ms.getD x.2 default).nIdx))
  exact envExt_prepend _ [] hx ht2 (fun t ht => nomatch ht)
    (fun c hc => by
      obtain ⟨x, hxm, mI, rP, rfl⟩ := hmem c hc
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hxm
      exact hfr y.1 (List.of_mem_zip hy).1)
    hw
    (fun c hc cv mI rP isK rules he r hr => by
      obtain ⟨x, -, mI', rP', rfl⟩ := hmem c hc
      cases he
      exact nomatch hr)
    (fun t ht => nomatch ht)

/-! ## The stage -/

/-- **What the generated-recursor stage needs resolved at `C₁` from the earlier pass**: the
members' formers' types (`formerTys`, the holes' annotations in every class match) and every
class's parameter openers (`TargetMajor.pfvs`, the context of its class matches).  Everything else
the stage reads is either checked by the stage itself (the stream's and the generated constants'
`constsResolveF` guards, the rules' guards) or inferred successfully over these
(`inferType_ok_res`). -/
structure GenRecRes (C₁ : Env) (p : BlockShape) (Ms : List TargetMajor) : Prop where
  formers : ∀ cv ∈ p.formers, Res C₁ cv.type
  pfvs : PfvsRes C₁ Ms

theorem genRecCheck_ext {C₁ C₂ : Env} (hx : EnvExt C₁ C₂) (ht2 : TablesStored C₂) (F : Nat)
    (p : BlockShape) (nestedBit : Bool) (params : List Expr) (tbl : List NestCtorNf) (rd : ClassRead)
    (Ms : List TargetMajor) (block : List ConstantInfo)
    (hres : GenRecRes C₁ p Ms)
    (hfr : ∀ rc ∈ p.recs, NameOK rc.cvR.name ∧ C₂.find? rc.cvR.name = none)
    {out : List (ConstantVal × TargetMajor × List Expr)}
    (h : genRecCheck (m := CheckM) (fueledOps .verified F) (mkFEnv C₁) p nestedBit params tbl rd Ms block
      = .ok out) :
    genRecCheck (m := CheckM) (fueledOps .verified F) (mkFEnv C₂) p nestedBit params tbl rd Ms block
      = .ok out := by
  have hft : ResL C₁ (p.formers.map (·.type)) := by
    intro x hx'
    obtain ⟨cv, hcv, rfl⟩ := List.mem_map.mp hx'
    exact hres.formers cv hcv
  unfold genRecCheck at h ⊢
  obtain ⟨u, hu, h⟩ := exceptBind_ok h
  refine bind_ok_of hu ?_
  obtain ⟨cvRis, hc, h⟩ := exceptBind_ok h
  obtain ⟨hc2, hcr⟩ := classStreamRecs_ext hx F p.recs cvRis (fun rc h' => (hfr rc h').2) hc
  refine bind_ok_of hc2 ?_
  dsimp only at h ⊢
  by_cases g1 : 0 < p.k
  case neg => rw [ite_eq_right g1] at h; kill h
  rw [ite_eq_left g1] at h ⊢
  by_cases g2 : (p.large && !blockLargeElimAllowed p (nestedBit || Ms.any fun x => x.member.isNone)) = true
  case pos => rw [ite_eq_left g2] at h; kill h
  rw [ite_eq_right g2] at h ⊢
  simp only [mkFEnv_env] at h ⊢
  obtain ⟨Ms', hMs, h⟩ := exceptBind_ok h
  refine bind_ok_of (classesNfs_ext hx F p _ tbl hft Ms Ms' hres.pfvs hMs) ?_
  have hp' : PfvsRes C₁ Ms' := classesNfs_pfvs hres.pfvs hMs
  obtain ⟨ctors, hct, h⟩ := exceptBind_ok h
  refine bind_ok_of (classesCtors_ext hx F p _ rd Ms' hft hp' 0 Ms' ctors hct) ?_
  by_cases g3 : ((List.filter ClassSlot.isMinor rd.slots).length == (List.map List.length ctors).sum) = true
  case neg => rw [ite_eq_right g3] at h; kill h
  rw [ite_eq_left g3] at h ⊢
  obtain ⟨ftc, hftc, h⟩ := exceptBind_ok h
  refine bind_ok_of (mapM_ok_of (fun M ty hM => classFormerTy_ext hx F p.formers M hM) Ms' ftc hftc) ?_
  obtain ⟨pre, hpre, h⟩ := exceptBind_ok h
  refine bind_ok_of hpre ?_
  obtain ⟨cvGs, hcv, h⟩ := exceptBind_ok h
  obtain ⟨hcv2, hnames⟩ := classRecTysOk_ext hx F _ p.k p.recs cvRis rd.recCls cvGs hcr
    (fun rc h' => (hfr rc h').2) hcv
  refine bind_ok_of hcv2 ?_
  rw [ConLeche.Cached.classFeR_mkFEnv] at h ⊢
  have hw := ConLeche.Cached.envWF_ruleEnv (mode := .verified) hx.facts.wf
    ⟨F, by rw [classRecTysOk_datF]; exact hcv⟩ Ms' rd.recCls
  have hfrG : ∀ cv ∈ cvGs, NameOK cv.name ∧ C₂.find? cv.name = none := by
    intro cv hcvm
    obtain ⟨rc, hrc, e⟩ := hnames cv hcvm
    rw [e]; exact hfr rc hrc
  exact classRecsRulesOk_ext hx (ruleEnv_ext hx ht2 p Ms' cvGs rd.recCls hfrG hw) F _ _ cvGs rd.recCls out h

end ConPanqueque.Pipeline.IndExt
