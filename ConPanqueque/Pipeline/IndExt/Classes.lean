import ConPanqueque.Pipeline.IndExt.PosWalk
import ConPanqueque.Pipeline.IndExt.InferRes
import ConLeche.Verify.Inductives.GenRecRun
import ConLeche.Verify.Cached.Erase
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.CheckerF

/-! # The block's classes at an extension

`checkBlockClasses` reads the environment in two places: the pre-pass's parameter counts
(`classNPcOf`, at the heads of the motives only) and the class check (`classMajors`:
`targetMajorOf`, `targetMajorPins`).  Every class head of an accepting run at `A₁` is a member or
a stored inductive of `A₁` (`targetMajorOf` refuses any other head), so the parameter counts read
alike at `A₂` on every head the pre-pass queried (`classRead_congr`), and the class check carries
over (`targetMajorOf_transport`, `targetPinTys_ext`, `familyKeyCheck_ext`). -/

namespace ConPanqueque.Pipeline.IndExt

open ConLeche ConLeche.Verify ConPanqueque.Pipeline

set_option autoImplicit false

variable {A₁ A₂ : Env}

/-! ## The pre-pass, congruent in the parameter counts -/

theorem obind' {α β : Type} {x : Option α} {k : α → Option β} {b : β}
    (h : x.bind k = some b) : ∃ a, x = some a ∧ k a = some b := by
  cases x with
  | none => cases h
  | some a => exact ⟨a, rfl, h⟩

theorem classReadSlots_congr {f g : Name → Nat} (np : Nat) :
    ∀ (n : Nat) (motPos : List Nat) (d : Nat) (e : Expr) (sl : List ClassSlot),
      classReadSlots f np n motPos d e = some sl →
      (∀ k, ClassSlot.motive k ∈ sl → f k.ind = g k.ind) →
      classReadSlots g np n motPos d e = some sl
  | 0, _, _, _, _, h, _ => h
  | n + 1, motPos, d, e, sl, h, hag => by
    cases e with
    | forallE dom body =>
      simp only [classReadSlots, Option.bind_eq_bind, Option.pure_def] at h ⊢
      split at h
      · obtain ⟨mdom, hm, h⟩ := obind' h
        rw [hm]
        simp only [Option.bind_some]
        split at h
        · rename_i I us hI
          simp only [Option.bind_some] at h ⊢
          obtain ⟨rest, hr, h⟩ := obind' h
          simp only [Option.some.injEq] at h
          subst h
          have hfg := hag _ (List.mem_cons_self ..)
          simp only at hfg
          rw [classReadSlots_congr np n _ _ _ rest hr (fun k hk => hag k (List.mem_cons_of_mem _ hk))]
          rw [← hfg]
          rfl
        · simp at h
      · obtain ⟨slot, hm, h⟩ := obind' h
        rw [hm]
        simp only [Option.bind_some] at h ⊢
        obtain ⟨rest, hr, h⟩ := obind' h
        simp only [Option.some.injEq] at h
        subst h
        have hr' := classReadSlots_congr np n _ _ _ rest hr
          (fun k hk => hag k (List.mem_cons_of_mem _ hk))
        rw [hr']
        rfl
    | _ => simp [classReadSlots] at h

theorem classRead_congr {f g : Name → Nat} {nP : Nat} {recs : List RecShape} {rd : ClassRead}
    (h : classRead nP f recs = some rd) (hag : ∀ k ∈ rd.classes, f k.ind = g k.ind) :
    classRead nP g recs = some rd := by
  unfold classRead at h ⊢
  simp only [Option.bind_eq_bind, Option.pure_def] at h ⊢
  obtain ⟨rc0, h0, h⟩ := obind' h
  rw [h0]
  simp only [Option.bind_some] at h ⊢
  obtain ⟨⟨fvs, body⟩, hb, h⟩ := obind' h
  rw [hb]
  simp only [Option.bind_some] at h ⊢
  obtain ⟨slots, hs, h⟩ := obind' h
  have hrd : rd.slots = slots := by
    obtain ⟨recCls, -, h⟩ := obind' h
    simp only [Option.some.injEq] at h
    subst h; rfl
  have hs' := classReadSlots_congr nP _ [] nP body slots hs (fun k hk => hag k (by
    unfold ClassRead.classes
    rw [hrd]
    exact List.mem_filterMap.mpr ⟨_, hk, rfl⟩))
  rw [hs']
  simp only [Option.bind_some]
  exact h

/-! ## The class check's environment -/

theorem classEnvAgree_ext (hc : CtorsAgree A₁ A₂) (hx : EnvExt A₁ A₂) (F : Nat) (p : BlockShape) :
    ClassEnvAgree (fueledOps .verified F) p (mkFEnv A₁) (mkFEnv A₂) := by
  intro I cv caps _ hI
  rw [mkFEnv_find?] at hI
  refine ⟨by rw [mkFEnv_find?, mkFEnv_find?, hx.find _ _ hI, hI], ?_, ?_⟩
  · unfold targetCtorsOf
    rw [mkFEnv_find?_fun, mkFEnv_find?_fun]
    have hs : ∃ q, nestContainer ⟨[], [], 0, [], [], .zero, A₁.find?, []⟩ I = some q := by
      unfold nestContainer
      simp only [hI]
      split <;> exact ⟨_, rfl⟩
    obtain ⟨q, hq⟩ := hs
    rw [hq]
    exact nestContainer_ext hc hx (ctx := ⟨[], [], 0, [], [], .zero, A₁.find?, []⟩) rfl hq
  · exact ConLeche.Model.familyTelescope_ext hx F caps (hx.facts.type hI)

/-! ## Free variables of the class keys -/

theorem fvRes_canon {A : Env} {params : List Expr} (hp : ResL A params) {n : Nat}
    (hn : n ≤ params.length) :
    ∀ (e : Expr), (e.replaceFVars fun i => params[i]?).fvarsBelow n →
      FvRes A (e.replaceFVars fun i => params[i]?)
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => trivial
  | .fvar i ty, h => by
    simp only [Expr.replaceFVars] at h ⊢
    cases hi : params[i]? with
    | none =>
      rw [hi] at h
      simp only [Option.getD_none, Expr.fvarsBelow] at h
      have := List.getElem?_eq_none_iff.mp hi
      omega
    | some x =>
      simp only [Option.getD_some]
      exact fvRes_of_res (hp x (List.mem_of_getElem? hi))
  | .app a b, h => ⟨fvRes_canon hp hn a h.1, fvRes_canon hp hn b h.2⟩
  | .lam a b, h => ⟨fvRes_canon hp hn a h.1, fvRes_canon hp hn b h.2⟩
  | .forallE a b, h => ⟨fvRes_canon hp hn a h.1, fvRes_canon hp hn b h.2⟩
  | .letE a v b, h => ⟨fvRes_canon hp hn a h.1, fvRes_canon hp hn v h.2.1, fvRes_canon hp hn b h.2.2⟩
  | .proj _ _ e, h => fvRes_canon hp hn e h

theorem classKeys_facts {nP : Nat} {params : List Expr} (hpar : ResL A₁ params)
    (hlen : nP ≤ params.length) :
    ∀ (ks keys : List ClassKey), ks.mapM (classKeyOf (m := CheckM) nP params) = .ok keys →
      (∀ key ∈ keys, ∀ x ∈ key.ds, FvRes A₁ x) ∧ (∀ k ∈ ks, ∃ key ∈ keys, key.ind = k.ind)
  | [], keys, h => by
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨fun _ hk => (nomatch hk), fun _ hk => (nomatch hk)⟩
  | k :: ks, keys, h => by
    rw [List.mapM_cons] at h
    obtain ⟨key, hkey, h⟩ := exceptBind_ok h
    obtain ⟨keys', hks, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    obtain ⟨ih1, ih2⟩ := classKeys_facts hpar hlen ks keys' hks
    obtain ⟨rfl, hsc⟩ := classKeyOf_run hkey
    refine ⟨fun key' hk' x hx => ?_, fun k' hk' => ?_⟩
    · rcases List.mem_cons.mp hk' with rfl | hk'
      · have hb := (hsc x hx).2
        simp only [classKeyCanon, List.mem_map] at hx
        obtain ⟨y, -, rfl⟩ := hx
        exact fvRes_canon hpar hlen y (Expr.fvarB_le hb)
      · exact ih1 key' hk' x hx
    · rcases List.mem_cons.mp hk' with rfl | hk'
      · exact ⟨_, List.mem_cons_self .., rfl⟩
      · obtain ⟨key', hm, he⟩ := ih2 k' hk'
        exact ⟨key', List.mem_cons_of_mem _ hm, he⟩

/-! ## The outside classes' pins -/

theorem targetPinTys_res {A : Env} (F d : Nat) :
    ∀ (xs : List Expr), (∀ x ∈ xs, FvRes A x) →
      targetPinTys (m := CheckM) (fueledOps .verified F) A d xs = .ok () → ResL A xs
  | [], _, _ => fun _ hx => nomatch hx
  | x :: xs, hf, h => by
    unfold targetPinTys at h
    obtain ⟨t, ht, h⟩ := exceptBind_ok h
    have hx := inferType_ok_res (hf x (List.mem_cons_self ..)) ht
    have ih := targetPinTys_res F d xs (fun y hy => hf y (List.mem_cons_of_mem _ hy)) h
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hx
    · exact ih y hy

theorem targetPinTys_ext (hx : EnvExt A₁ A₂) (F d : Nat) :
    ∀ (xs : List Expr), ResL A₁ xs →
      targetPinTys (m := CheckM) (fueledOps .verified F) A₁ d xs = .ok () →
      targetPinTys (m := CheckM) (fueledOps .verified F) A₂ d xs = .ok ()
  | [], _, _ => rfl
  | x :: xs, hr, h => by
    unfold targetPinTys at h ⊢
    have hx0 := hr x (List.mem_cons_self ..)
    exact okBind h (fun y hy => by rw [(ops_infer hx F d hx0).1]; exact hy)
      (fun _ _ h => targetPinTys_ext hx F d xs (fun y hy => hr y (List.mem_cons_of_mem _ hy)) h)

/-! ## One class, checked as a major -/

theorem getAppFn_const_mkAppN (I : Name) (us : List Level) (ds : List Expr) :
    (Expr.mkAppN (.const I us) ds).getAppFn = .const I us := by
  rw [Expr.getAppFn_mkAppN]; rfl

theorem getAppArgs_const_mkAppN (I : Name) (us : List Level) (ds : List Expr) :
    (Expr.mkAppN (.const I us) ds).getAppArgs = ds := by
  rw [Expr.getAppArgs_mkAppN]; rfl

theorem classMajor_ext (hc : CtorsAgree A₁ A₂) (hx : EnvExt A₁ A₂) (F : Nat) (p : BlockShape)
    {params : List Expr} (hpar : ResL A₁ params) {key : ClassKey} {M : TargetMajor}
    (hds : ∀ x ∈ key.ds, FvRes A₁ x)
    (hM : targetMajorOf (fueledOps .verified F) (mkFEnv A₁) p params params
      (Expr.mkAppN (.const key.ind key.lvls) key.ds) = .ok M)
    (hu : targetMajorPins (fueledOps .verified F) (mkFEnv A₁) p.nP M = .ok ()) :
    targetMajorOf (fueledOps .verified F) (mkFEnv A₂) p params params
      (Expr.mkAppN (.const key.ind key.lvls) key.ds) = .ok M ∧
    targetMajorPins (fueledOps .verified F) (mkFEnv A₂) p.nP M = .ok () ∧
    (key.ind ∈ p.memberNames ∨ ∃ cv caps, A₁.find? key.ind = some (.indInfo cv caps)) ∧
    M.ind = key.ind ∧
    (M.member = none → ∃ cv caps, A₁.find? M.ind = some (.indInfo cv caps)) ∧
    ResL A₁ M.ds := by
  have hM2 := targetMajorOf_transport (classEnvAgree_ext hc hx F p) hM
  refine ⟨hM2, ?_⟩
  obtain ⟨⟨R⟩, -⟩ := targetMajorOf_run hM
  cases R with
  | member I t ms hfn ht hms hpar' nfs =>
    rw [getAppFn_const_mkAppN] at hfn
    obtain ⟨rfl, -⟩ := Expr.const.inj hfn
    refine ⟨by unfold targetMajorPins; rfl, Or.inl ?_, rfl, fun hn => (nomatch hn), res_take hpar _⟩
    by_cases hm : key.ind ∈ p.memberNames
    · exact hm
    · rw [List.findIdx?_eq_none_iff.mpr (fun x hx => beq_false_of_ne (fun he : x = key.ind => hm (he ▸ hx)))] at ht
      cases ht
  | outside I us nPc nIdx ctors sI hfn ht hnq hct hl hsc hment hinst hsort nfs =>
    rw [getAppFn_const_mkAppN] at hfn
    cases hfn
    obtain ⟨cv, caps, hI⟩ := targetCtorsOf_indInfo hct
    rw [mkFEnv_find?] at hI
    rw [getAppArgs_const_mkAppN] at hu ⊢
    unfold targetMajorPins at hu ⊢
    simp only [Option.isNone_none, ↓reduceIte] at hu ⊢
    obtain ⟨u, hpt, hfk⟩ := exceptBind_ok hu
    have hres : ResL A₁ (key.ds.take nPc) :=
      targetPinTys_res F _ _ (fun x hm => hds x (List.mem_of_mem_take hm)) hpt
    refine ⟨?_, Or.inr ⟨cv, caps, hI⟩, trivial, fun _ => ⟨cv, caps, hI⟩, hres⟩
    have hpt2 := targetPinTys_ext hx F _ _ hres hpt
    have hfk2 : familyKeyCheck (fueledOps .verified F) (mkFEnv A₁).env (mkFEnv A₁).find? p.nP
        key.ind key.lvls (key.ds.take nPc) = .ok () := by cases u; exact hfk
    rw [mkFEnv_find?_fun] at hfk2
    have hfk3 := familyKeyCheck_ext hx F p.nP key.ind key.lvls hres hfk2
    rw [← mkFEnv_find?_fun A₂] at hfk3
    simp only [bind, Except.bind]
    rw [mkFEnv_env, hpt2]
    exact hfk3

theorem classMajors_ext (hc : CtorsAgree A₁ A₂) (hx : EnvExt A₁ A₂) (F : Nat) (p : BlockShape)
    {params : List Expr} (hpar : ResL A₁ params) :
    ∀ (keys : List ClassKey) (Ms : List TargetMajor), (∀ key ∈ keys, ∀ x ∈ key.ds, FvRes A₁ x) →
      classMajors (m := CheckM) (fueledOps .verified F) (mkFEnv A₁) p params keys = .ok Ms →
      classMajors (m := CheckM) (fueledOps .verified F) (mkFEnv A₂) p params keys = .ok Ms ∧
      (∀ key ∈ keys, key.ind ∈ p.memberNames ∨ ∃ cv caps, A₁.find? key.ind = some (.indInfo cv caps)) ∧
      (∀ M ∈ Ms, M.member = none → ∃ cv caps, A₁.find? M.ind = some (.indInfo cv caps)) ∧
      (∀ M ∈ Ms, ResL A₁ M.ds)
  | [], Ms, _, h => by
    simp only [classMajors, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact ⟨rfl, fun _ hk => (nomatch hk), fun _ hk => (nomatch hk), fun _ hk => (nomatch hk)⟩
  | key :: keys, Ms, hds, h => by
    unfold classMajors at h ⊢
    obtain ⟨M, hM, h⟩ := exceptBind_ok h
    obtain ⟨u, hu, h⟩ := exceptBind_ok h
    obtain ⟨Ms', hMs, h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    have hu' : targetMajorPins (fueledOps .verified F) (mkFEnv A₁) p.nP M = .ok () := by
      cases u; exact hu
    obtain ⟨hM2, hu2, hhead, -, hMst, hMds⟩ :=
      classMajor_ext hc hx F p hpar (hds key (List.mem_cons_self ..)) hM hu'
    obtain ⟨ih1, ih2, ih3, ih4⟩ :=
      classMajors_ext hc hx F p hpar keys Ms' (fun k hk => hds k (List.mem_cons_of_mem _ hk)) hMs
    refine ⟨?_, fun k hk => ?_, fun M' hM' => ?_, fun M' hM' => ?_⟩
    · simp only [hM2, hu2, ih1, bind, Except.bind, pure, Except.pure]
    · rcases List.mem_cons.mp hk with rfl | hk
      · exact hhead
      · exact ih2 k hk
    · rcases List.mem_cons.mp hM' with rfl | hM'
      · exact hMst
      · exact ih3 M' hM'
    · rcases List.mem_cons.mp hM' with rfl | hM'
      · exact hMds
      · exact ih4 M' hM'

/-! ## The classes -/

theorem classNPcOf_ext (hx : EnvExt A₁ A₂) (p : BlockShape) {I : Name}
    (hI : I ∈ p.memberNames ∨ ∃ cv caps, A₁.find? I = some (.indInfo cv caps)) :
    classNPcOf p (mkFEnv A₁) I = classNPcOf p (mkFEnv A₂) I := by
  unfold classNPcOf
  rcases hI with hm | ⟨cv, caps, hI⟩
  · simp [hm]
  · rw [mkFEnv_find?, mkFEnv_find?, hx.find _ _ hI, hI]

/-- **The classes carry over** to an extension, with what later stages read of them: every
class's parameters resolve at `A₁`, every outside class's head is a stored inductive of `A₁`, and
every class head the pre-pass read is a member or a stored inductive of `A₁`. -/
theorem checkBlockClasses_ext (hc : CtorsAgree A₁ A₂) (hx : EnvExt A₁ A₂) (F : Nat) {p : BlockShape}
    {params : List Expr} (hpar : ResL A₁ params) (hlen : p.nP ≤ params.length)
    {rd : ClassRead} {Ms : List TargetMajor}
    (h : checkBlockClasses (m := CheckM) (fueledOps .verified F) (mkFEnv A₁) p params = .ok (rd, Ms)) :
    checkBlockClasses (m := CheckM) (fueledOps .verified F) (mkFEnv A₂) p params = .ok (rd, Ms) ∧
    (∀ M ∈ Ms, ResL A₁ M.ds) ∧
    (∀ M ∈ Ms, M.member = none → ∃ cv caps, A₁.find? M.ind = some (.indInfo cv caps)) ∧
    (∀ k ∈ rd.classes, k.ind ∈ p.memberNames ∨ ∃ cv caps, A₁.find? k.ind = some (.indInfo cv caps)) := by
  obtain ⟨R⟩ := checkBlockClasses_run h
  obtain ⟨hkds, hkind⟩ := classKeys_facts hpar hlen _ _ R.hkeys
  obtain ⟨hMs2, hhead, hMst, hMds⟩ := classMajors_ext hc hx F p hpar _ _ hkds R.hMs
  have hcls : ∀ k ∈ rd.classes,
      k.ind ∈ p.memberNames ∨ ∃ cv caps, A₁.find? k.ind = some (.indInfo cv caps) := by
    intro k hk
    obtain ⟨key, hkey, he⟩ := hkind k hk
    rw [← he]
    exact hhead key hkey
  have hrd2 := classRead_congr R.hrd (fun k hk => classNPcOf_ext hx p (hcls k hk))
  refine ⟨?_, hMds, hMst, hcls⟩
  unfold checkBlockClasses at h ⊢
  rw [R.hrd] at h
  rw [hrd2]
  simp only [unwrapOr, pure_bind] at h ⊢
  rw [R.hkeys] at h ⊢
  simp only [bind, Except.bind] at h ⊢
  rw [R.hMs] at h
  rw [hMs2]
  exact h

end ConPanqueque.Pipeline.IndExt
