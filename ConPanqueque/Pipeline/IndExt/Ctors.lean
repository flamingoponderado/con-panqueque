import ConPanqueque.Pipeline.IndExt.Inds
import ConLeche.Verify.CheckerF
import ConLeche.Verify.Inductives.DirectInv
import ConLeche.Kernel.Inductives.StreamRecs

/-! # The block's constructor, index-sort and stream-recursor checks at an extension

Every term these checks hand to the operations is built from a term that resolves at the smaller
environment: on such terms the operations agree at an extension (`ops_infer`, `ops_ensureSort`,
`ops_defeq`), so the pure-operation stages are equal at both environments (`*_eq`), and the
stages with resolution guards or a constant check carry their success over (`*_ext`). -/

namespace ConPanqueque.Pipeline.IndExt

open ConLeche ConLeche.Verify ConPanqueque.Pipeline

set_option autoImplicit false

local syntax "close_throw" : tactic
local macro_rules
  | `(tactic| close_throw) =>
    `(tactic| first
        | (exfalso; exact structThrow_ne_ok (by assumption))
        | (exfalso; exact structThrow_ne_ok
            (by simpa [bind, Except.bind] using ‹_›)))

/-! ## Small tools -/

theorem bind_of_eq {α β : Type} {x : CheckM α} {a : α} {f : α → CheckM β} {b : β}
    (hx : x = .ok a) (hf : f a = .ok b) : (x >>= f) = .ok b := by
  rw [hx]; exact hf


theorem res_map_fvarTypeD {env : Env} {l : List Expr} (h : ∀ x ∈ l, Res env x) :
    ∀ x ∈ l.map Expr.fvarTypeD, Res env x := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  exact res_fvarTypeD (h y hy)

theorem mem_of_getElem? {α : Type} {l : List α} {i : Nat} {a : α} (h : l[i]? = some a) : a ∈ l := by
  obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp h
  exact List.getElem_mem hi

theorem unwrapOr_none_bind {α β : Type} (err : CheckError) (f g : α → CheckM β) :
    (unwrapOr (m := CheckM) (none : Option α) err >>= f) = (unwrapOr (m := CheckM) none err >>= g) := rfl

theorem error_bind_eq {α β : Type} (e : CheckError) (f g : α → CheckM β) :
    (Except.error e >>= f : CheckM β) = (Except.error e >>= g) := rfl


theorem ok_bind_eq {α β : Type} (a : α) (f : α → CheckM β) : (Except.ok a >>= f : CheckM β) = f a := rfl

variable {X₁ X₂ : Env}

/-! ## The pure-operation stages: equal at an extension -/

/-- The field-sort walk, on resolving fields. -/
theorem checkStructFieldSortsI_eq (hx : EnvExt X₁ X₂) (F : Nat) (isProp large : Bool) (s : Level)
    (nP : Nat) (fvs idxArgs : List Expr) (hfv : ∀ x ∈ fvs, Res X₁ x) :
    ∀ n, checkStructFieldSortsI (m := CheckM) (fueledOps .verified F) X₂ isProp large s nP fvs idxArgs n =
      checkStructFieldSortsI (m := CheckM) (fueledOps .verified F) X₁ isProp large s nP fvs idxArgs n
  | 0 => rfl
  | j + 1 => by
    simp only [checkStructFieldSortsI]
    cases hf : fvs[j]? with
    | none => exact unwrapOr_none_bind _ _ _
    | some fv =>
      simp only [unwrapOr, pure_bind]
      have hr : Res X₁ fv.fvarTypeD := res_fvarTypeD (hfv fv (mem_of_getElem? hf))
      rw [(ops_infer hx F _ hr).1]
      cases hi : (fueledOps .verified F).inferType X₁ (nP + j) fv.fvarTypeD with
      | error e => exact error_bind_eq _ _ _
      | ok ty =>
        simp only [ok_bind_eq]
        rw [ops_ensureSort hx F _ ((ops_infer hx F _ hr).2 ty hi),
          checkStructFieldSortsI_eq hx F isProp large s nP fvs idxArgs hfv j]

/-- The parameter-domain pins, on resolving locals and domains. -/
theorem checkStructDomsAt_eq (hx : EnvExt X₁ X₂) (F off : Nat) (fvs doms : List Expr)
    (hf : ∀ x ∈ fvs, Res X₁ x) (hd : ∀ x ∈ doms, Res X₁ x) :
    ∀ n, checkStructDomsAt (m := CheckM) (fueledOps .verified F) X₂ off fvs doms n =
      checkStructDomsAt (m := CheckM) (fueledOps .verified F) X₁ off fvs doms n
  | 0 => rfl
  | j + 1 => by
    simp only [checkStructDomsAt]
    cases ha : fvs[j]? with
    | none => exact unwrapOr_none_bind _ _ _
    | some a =>
      cases hb : doms[j]? with
      | none => simp only [unwrapOr_some, ok_bind_eq]; exact unwrapOr_none_bind _ _ _
      | some b =>
        simp only [unwrapOr, pure_bind]
        rw [ops_defeq hx F _ (res_fvarTypeD (hf a (mem_of_getElem? ha))) (hd b (mem_of_getElem? hb)),
          checkStructDomsAt_eq hx F off fvs doms hf hd j]

/-! ## The constructors -/

theorem checkSumCtor_ext (hx : EnvExt X₁ X₂) (F : Nat) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (resSort : Level) (isProp large : Bool) (cvC : ConstantVal) (nF : Nat) (cvTa : ConstantVal)
    (hfr : X₂.find? cvC.name = none) (hTa : Res X₁ cvTa.type)
    (h : checkSumCtor (m := CheckM) (fueledOps .verified F) X₁ X₁ T lps nP nIdx resSort isProp large
      cvC nF cvTa = .ok ()) :
    checkSumCtor (m := CheckM) (fueledOps .verified F) X₂ X₂ T lps nP nIdx resSort isProp large
      cvC nF cvTa = .ok () := by
  unfold checkSumCtor at h ⊢
  obtain ⟨u₀, hccv₀, h⟩ := exceptBind_ok h
  cases u₀
  have hres := (checkConstantVal_res F X₁ cvC _ _ _ hccv₀).1
  refine bind_of_eq (checkConstantVal_ext hx F cvC _ _ _ hfr hccv₀) ?_
  obtain ⟨q, hq, h⟩ := exceptBind_ok h
  refine bind_of_eq hq ?_
  obtain ⟨cbs, cbody⟩ := q
  try simp only at h ⊢
  by_cases hc : structCtorResidOk T lps nP nF nIdx cbody = true
  case neg => rw [ite_eq_right hc] at h; close_throw
  rw [ite_eq_left hc] at h ⊢
  obtain ⟨cq, hcq, h⟩ := exceptBind_ok h
  refine bind_of_eq hcq ?_
  have hcq' := unwrapOr_ok hcq
  obtain ⟨tq, htq, h⟩ := exceptBind_ok h
  refine bind_of_eq htq ?_
  have htq' := unwrapOr_ok htq
  obtain ⟨fvsP, crest⟩ := cq
  obtain ⟨tfvs, trest⟩ := tq
  try simp only at h ⊢
  have hfP : ∀ x ∈ fvsP, Res X₁ x := res_openPisAtFvars nP 0 hres hcq'
  have hcrest : Res X₁ crest := res_openPisAtFvars_body nP 0 hres hcq'
  have htf : ∀ x ∈ tfvs, Res X₁ x := res_openPisAtFvars nP 0 hTa htq'
  obtain ⟨u, hdoms, h⟩ := exceptBind_ok h
  refine bind_of_eq (by
    rw [checkStructDomsAt_eq hx F 0 fvsP _ hfP (res_map_fvarTypeD htf)]; exact hdoms) ?_
  obtain ⟨xq, hxq, h⟩ := exceptBind_ok h
  refine bind_of_eq hxq ?_
  have hxq' := unwrapOr_ok hxq
  obtain ⟨xFvs, xrest⟩ := xq
  have hxF : ∀ x ∈ xFvs, Res X₁ x := res_openPisAtFvars nF nP hcrest hxq'
  try simp only at h ⊢
  by_cases h2 : (xrest.getAppFn == Expr.const T (lps.map .param) &&
      xrest.getAppArgs.take nP == fvsP && xrest.getAppArgs.length == nP + nIdx) = true
  case neg => rw [ite_eq_right h2] at h; close_throw
  rw [ite_eq_left h2] at h ⊢
  by_cases h3 : (xFvs.all fun x => Expr.constsResolve X₁ x.fvarTypeD) = true
  case neg => rw [ite_eq_right h3] at h; close_throw
  rw [ite_eq_left h3] at h
  have h3' : (xFvs.all fun x => Expr.constsResolve X₂ x.fvarTypeD) = true := by
    rw [List.all_eq_true] at h3 ⊢
    exact fun x hx' => res_ext hx (h3 x hx')
  rw [ite_eq_left h3']
  by_cases h4 : ((xrest.getAppArgs.drop nP).all fun e => Expr.constsResolve X₁ e) = true
  case neg => rw [ite_eq_right h4] at h; close_throw
  rw [ite_eq_left h4] at h
  have h4' : ((xrest.getAppArgs.drop nP).all fun e => Expr.constsResolve X₂ e) = true := by
    rw [List.all_eq_true] at h4 ⊢
    exact fun x hx' => res_ext hx (h4 x hx')
  rw [ite_eq_left h4']
  rw [checkStructFieldSortsI_eq hx F isProp large resSort nP xFvs _ hxF]
  exact h

theorem checkSumCtors_ext (hx : EnvExt X₁ X₂) (F : Nat) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (resSort : Level) (isProp large : Bool) (cvTa : ConstantVal) (hTa : Res X₁ cvTa.type) :
    ∀ (cs : List (ConstantVal × Nat)), (∀ c ∈ cs, X₂.find? c.1.name = none) →
      checkSumCtors (m := CheckM) (fueledOps .verified F) X₁ X₁ T lps nP nIdx resSort isProp large cvTa cs
        = .ok () →
      checkSumCtors (m := CheckM) (fueledOps .verified F) X₂ X₂ T lps nP nIdx resSort isProp large cvTa cs
        = .ok ()
  | [], _, _ => rfl
  | c :: cs, hfr, h => by
    unfold checkSumCtors at h ⊢
    obtain ⟨u, hc, h⟩ := exceptBind_ok h
    cases u
    refine bind_of_eq (checkSumCtor_ext hx F T lps nP nIdx resSort isProp large c.1 c.2 cvTa
      (hfr c (List.mem_cons_self ..)) hTa hc) ?_
    exact checkSumCtors_ext hx F T lps nP nIdx resSort isProp large cvTa hTa cs
      (fun c' hc' => hfr c' (List.mem_cons_of_mem _ hc')) h

/-- **The block's constructor stage at an extension**: fresh constructor names at `X₂`, and the
members' formers (as the block reads them) resolving at `X₁`. -/
theorem checkBlockCtors_ext (hx : EnvExt X₁ X₂) (F : Nat) (p : BlockShape) :
    ∀ (l : List MemberShape), (∀ c ∈ l.flatMap (·.ctors), X₂.find? c.1.name = none) →
      (∀ ms ∈ l, Res X₁ ms.cvT.type) →
      checkBlockCtors (m := CheckM) (fueledOps .verified F) X₁ X₁ p l = .ok () →
      checkBlockCtors (m := CheckM) (fueledOps .verified F) X₂ X₂ p l = .ok ()
  | [], _, _, _ => rfl
  | ms :: rest, hfr, hT, h => by
    unfold checkBlockCtors at h ⊢
    obtain ⟨u, hc, h⟩ := exceptBind_ok h
    cases u
    refine bind_of_eq (checkSumCtors_ext hx F _ _ _ _ _ _ _ _ (hT ms (List.mem_cons_self ..)) _
      (fun c hc' => hfr c (by simp only [List.flatMap_cons]; exact List.mem_append_left _ hc')) hc) ?_
    exact checkBlockCtors_ext hx F p rest
      (fun c hc' => hfr c (by simp only [List.flatMap_cons]; exact List.mem_append_right _ hc'))
      (fun ms' hm => hT ms' (List.mem_cons_of_mem _ hm)) h

/-! ## The index sorts -/

/-- The index-sort stage is the same run at an extension, given the members' formers (as the block
reads them) resolving at `X₁`. -/
theorem checkBlockIdxSorts_eq (hx : EnvExt X₁ X₂) (F : Nat) (p : BlockShape) :
    ∀ (l : List MemberShape), (∀ ms ∈ l, Res X₁ ms.cvT.type) →
      checkBlockIdxSorts (m := CheckM) (fueledOps .verified F) X₂ p l =
        checkBlockIdxSorts (m := CheckM) (fueledOps .verified F) X₁ p l
  | [], _ => rfl
  | ms :: rest, hT => by
    unfold checkBlockIdxSorts
    cases hq : openPisAtFvars (p.nP + ms.nIdx) ms.cvT.type 0 with
    | none => exact unwrapOr_none_bind _ _ _
    | some tq =>
      simp only [unwrapOr, pure_bind]
      have htf : ∀ x ∈ tq.1, Res X₁ x :=
        res_openPisAtFvars _ 0 (hT ms (List.mem_cons_self ..)) hq
      rw [checkStructFieldSortsI_eq hx F _ _ _ _ _ _ (fun x hm => htf x (List.mem_of_mem_drop hm)),
        checkBlockIdxSorts_eq hx F p rest (fun ms' hm => hT ms' (List.mem_cons_of_mem _ hm))]

theorem checkBlockIdxSorts_ext (hx : EnvExt X₁ X₂) (F : Nat) (p : BlockShape) (l : List MemberShape)
    (hT : ∀ ms ∈ l, Res X₁ ms.cvT.type)
    (h : checkBlockIdxSorts (m := CheckM) (fueledOps .verified F) X₁ p l = .ok ()) :
    checkBlockIdxSorts (m := CheckM) (fueledOps .verified F) X₂ p l = .ok () := by
  rw [checkBlockIdxSorts_eq hx F p l hT]; exact h

/-! ## The stream's recursors -/

/-- A record's domains against the generated ones, on resolving locals. -/
theorem recDomsAt_eq (hx : EnvExt X₁ X₂) (F : Nat) (rec : Name) (sfvs gfvs : List Expr)
    (hs : ∀ x ∈ sfvs, Res X₁ x) (hg : ∀ x ∈ gfvs, Res X₁ x) :
    ∀ j k, recDomsAt (m := CheckM) (fueledOps .verified F) X₂ rec sfvs gfvs j k =
      recDomsAt (m := CheckM) (fueledOps .verified F) X₁ rec sfvs gfvs j k
  | _, 0 => rfl
  | j, k + 1 => by
    simp only [recDomsAt]
    cases ha : sfvs[j]? with
    | none => exact unwrapOr_none_bind _ _ _
    | some a =>
      cases hb : gfvs[j]? with
      | none => simp only [unwrapOr_some, ok_bind_eq]; exact unwrapOr_none_bind _ _ _
      | some b =>
        simp only [unwrapOr, pure_bind]
        rw [ops_defeq hx F _ (res_fvarTypeD (hs a (mem_of_getElem? ha)))
            (res_fvarTypeD (hg b (mem_of_getElem? hb))),
          recDomsAt_eq hx F rec sfvs gfvs hs hg (j + 1) k]

/-- What an optional opening carries resolves. -/
def ResOpen (env : Env) (o : Option (List Expr × Expr)) : Prop :=
  ∀ a b, o = some (a, b) → (∀ x ∈ a, Res env x) ∧ Res env b

theorem resOpen_open {env : Env} {e : Expr} (he : Res env e) (n i : Nat) :
    ResOpen env (openPisAtFvars n e i) := fun _ _ hab =>
  ⟨res_openPisAtFvars n i he hab, res_openPisAtFvars_body n i he hab⟩

theorem recTyOpened_eq (hx : EnvExt X₁ X₂) (F : Nat) (rec : Name) (n : Nat)
    (o₁ o₂ : Option (List Expr × Expr)) (h₁ : ResOpen X₁ o₁) (h₂ : ResOpen X₁ o₂) :
    recTyOpened (m := CheckM) (fueledOps .verified F) X₂ rec n o₁ o₂ =
      recTyOpened (m := CheckM) (fueledOps .verified F) X₁ rec n o₁ o₂ := by
  match o₁, o₂, h₁, h₂ with
  | some (sfvs, srest), some (gfvs, grest), h₁, h₂ =>
    obtain ⟨hs, hsr⟩ := h₁ _ _ rfl
    obtain ⟨hg, hgr⟩ := h₂ _ _ rfl
    simp only [recTyOpened]
    rw [recDomsAt_eq hx F rec sfvs gfvs hs hg, ops_defeq hx F _ hsr hgr]
  | none, _, _, _ => rfl
  | some _, none, _, _ => rfl

theorem recTyCheck_ext (hx : EnvExt X₁ X₂) (F : Nat) (rec : Name) (lps : List Name) (n : Nat)
    (s g : Expr) (hg : Res X₁ g)
    (h : recTyCheck (m := CheckM) (fueledOps .verified F) (mkFEnv X₁) rec lps n s g = .ok ()) :
    recTyCheck (m := CheckM) (fueledOps .verified F) (mkFEnv X₂) rec lps n s g = .ok () := by
  unfold recTyCheck at h ⊢
  simp only [mkFEnv_env, constsResolveF_eq] at h ⊢
  by_cases c1 : (s.looseBVarsBounded 0 && !s.hasFvar && !g.hasFvar) = true
  case neg => rw [ite_eq_right c1] at h; close_throw
  rw [ite_eq_left c1] at h ⊢
  by_cases c2 : s.allLevelParamsDefined lps = true
  case neg => rw [ite_eq_right c2] at h; close_throw
  rw [ite_eq_left c2] at h ⊢
  by_cases c3 : s.constsResolve X₁ = true
  case neg => rw [ite_eq_right c3] at h; close_throw
  rw [ite_eq_left c3] at h
  rw [ite_eq_left (res_ext hx c3)]
  obtain ⟨st, hst, h⟩ := exceptBind_ok h
  refine bind_of_eq (by rw [(ops_infer hx F 0 c3).1]; exact hst) ?_
  obtain ⟨u, hu, h⟩ := exceptBind_ok h
  refine bind_of_eq (by rw [ops_ensureSort hx F 0 ((ops_infer hx F 0 c3).2 st hst)]; exact hu) ?_
  rw [recTyOpened_eq hx F rec n _ _ (resOpen_open c3 n 0) (resOpen_open hg n 0)]
  exact h

theorem ruleAgree_ext (hx : EnvExt X₁ X₂) (F : Nat) (rec ctor : Name) (lps : List Name)
    (s g : Expr) (hg : Res X₁ g)
    (h : ruleAgree (m := CheckM) (fueledOps .verified F) (mkFEnv X₁) rec ctor lps s g = .ok ()) :
    ruleAgree (m := CheckM) (fueledOps .verified F) (mkFEnv X₂) rec ctor lps s g = .ok () := by
  unfold ruleAgree at h ⊢
  simp only [mkFEnv_env, constsResolveF_eq] at h ⊢
  by_cases c1 : (s.looseBVarsBounded 0 && !s.hasFvar && !g.hasFvar) = true
  case neg => rw [ite_eq_right c1] at h; close_throw
  rw [ite_eq_left c1] at h ⊢
  by_cases c2 : s.allLevelParamsDefined lps = true
  case neg => rw [ite_eq_right c2] at h; close_throw
  rw [ite_eq_left c2] at h ⊢
  by_cases c3 : s.constsResolve X₁ = true
  case neg => rw [ite_eq_right c3] at h; close_throw
  rw [ite_eq_left c3] at h
  rw [ite_eq_left (res_ext hx c3)]
  obtain ⟨ts, hts, h⟩ := exceptBind_ok h
  refine bind_of_eq (by rw [(ops_infer hx F 0 c3).1]; exact hts) ?_
  obtain ⟨tg, htg, h⟩ := exceptBind_ok h
  refine bind_of_eq (by rw [(ops_infer hx F 0 hg).1]; exact htg) ?_
  rw [ops_defeq hx F 0 ((ops_infer hx F 0 c3).2 ts hts) ((ops_infer hx F 0 hg).2 tg htg),
    ops_defeq hx F 0 c3 hg]
  exact h

theorem streamRulesCheck_ext (hx : EnvExt X₁ X₂) (F : Nat) (rec : Name) (lps : List Name) (rP : Nat) :
    ∀ (rs : List RecRule) (gs : List Expr), (∀ g ∈ gs, Res X₁ g) →
      streamRulesCheck (m := CheckM) (fueledOps .verified F) (mkFEnv X₁) rec lps rP rs gs = .ok () →
      streamRulesCheck (m := CheckM) (fueledOps .verified F) (mkFEnv X₂) rec lps rP rs gs = .ok ()
  | r :: rs, g :: gs, hg, h => by
    unfold streamRulesCheck at h ⊢
    obtain ⟨u, hb, h⟩ := exceptBind_ok h
    cases u
    refine bind_of_eq hb ?_
    have ih := streamRulesCheck_ext hx F rec lps rP rs gs (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg'))
    try simp only at h ⊢
    by_cases c : (r.rhs == g) = true
    · rw [ite_eq_left c] at h ⊢
      exact ih h
    · rw [ite_eq_right c] at h ⊢
      obtain ⟨u, ha, h⟩ := exceptBind_ok h
      cases u
      exact bind_of_eq (ruleAgree_ext hx F rec r.ctor lps r.rhs g (hg g (List.mem_cons_self ..)) ha) (ih h)
  | [], [], _, _ => rfl
  | _ :: _, [], _, h => by
    exfalso; unfold streamRulesCheck at h; exact structThrow_ne_ok h
  | [], _ :: _, _, h => by
    exfalso; unfold streamRulesCheck at h; exact structThrow_ne_ok h

theorem streamRecCompare_ext (hx : EnvExt X₁ X₂) (F : Nat) (rc : RecShape)
    (g : ConstantVal × TargetMajor × List Expr) (hg : Res X₁ g.1.type ∧ ∀ e ∈ g.2.2, Res X₁ e)
    (h : streamRecCompare (m := CheckM) (fueledOps .verified F) (mkFEnv X₁) rc g = .ok ()) :
    streamRecCompare (m := CheckM) (fueledOps .verified F) (mkFEnv X₂) rc g = .ok () := by
  unfold streamRecCompare at h ⊢
  try simp only at h ⊢
  by_cases c : (rc.cvR.type == g.1.type) = true
  · rw [ite_eq_left c] at h ⊢
    exact streamRulesCheck_ext hx F _ _ _ _ _ hg.2 h
  · rw [ite_eq_right c] at h ⊢
    obtain ⟨u, ht, h⟩ := exceptBind_ok h
    cases u
    exact bind_of_eq (recTyCheck_ext hx F _ _ _ _ _ hg.1 ht) (streamRulesCheck_ext hx F _ _ _ _ _ hg.2 h)

theorem streamRecCheck_ext (hx : EnvExt X₁ X₂) (F : Nat) (rc : RecShape)
    (g : ConstantVal × TargetMajor × List Expr) (hg : Res X₁ g.1.type ∧ ∀ e ∈ g.2.2, Res X₁ e)
    (h : streamRecCheck (m := CheckM) (fueledOps .verified F) (mkFEnv X₁) rc g = .ok ()) :
    streamRecCheck (m := CheckM) (fueledOps .verified F) (mkFEnv X₂) rc g = .ok () := by
  unfold streamRecCheck at h ⊢
  obtain ⟨u, hs, h⟩ := exceptBind_ok h
  cases u
  refine bind_of_eq hs ?_
  try simp only at h ⊢
  by_cases c : streamNestedOk rc.cvR.type rc.mI rc.rP (generatedFire g.2.1 rc.rP) = true
  case neg => rw [ite_eq_right c] at h; close_throw
  rw [ite_eq_left c] at h ⊢
  exact streamRecCompare_ext hx F rc g hg h

/-- **The stream's recursors against the generated ones, at an extension**: the generated types
and right-hand sides resolving at `R₁` (the run reads the records' own terms' resolution only). -/
theorem streamRecsCheck_ext {R₁ R₂ : Env} (hx : EnvExt R₁ R₂) (F : Nat) :
    ∀ (recs : List RecShape) (out : List (ConstantVal × TargetMajor × List Expr)),
      (∀ g ∈ out, Res R₁ g.1.type ∧ ∀ e ∈ g.2.2, Res R₁ e) →
      streamRecsCheck (m := CheckM) (fueledOps .verified F) (mkFEnv R₁) recs out = .ok () →
      streamRecsCheck (m := CheckM) (fueledOps .verified F) (mkFEnv R₂) recs out = .ok ()
  | rc :: rcs, g :: gs, hg, h => by
    unfold streamRecsCheck at h ⊢
    obtain ⟨u, hc, h⟩ := exceptBind_ok h
    cases u
    exact bind_of_eq (streamRecCheck_ext hx F rc g (hg g (List.mem_cons_self ..)) hc)
      (streamRecsCheck_ext hx F rcs gs (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) h)
  | [], [], _, _ => rfl
  | _ :: _, [], _, h => by
    exfalso; unfold streamRecsCheck at h; exact structThrow_ne_ok h
  | [], _ :: _, _, h => by
    exfalso; unfold streamRecsCheck at h; exact structThrow_ne_ok h

end ConPanqueque.Pipeline.IndExt
