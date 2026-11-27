import ConPanqueque.Pipeline.IndExt.Pass
import ConPanqueque.Pipeline.IndExt.GenRecOut
import ConPanqueque.Pipeline.IndExt.Tail
import ConLeche.Verify.Inductives.RecCheckRun

/-! # The inductive block at an extension: the tail, the block, the declaration -/

namespace ConPanqueque.Pipeline.IndExt

open ConLeche ConLeche.Verify ConPanqueque.Pipeline

set_option autoImplicit false

/-- What a class says of its constructors: a member's, or stored constructors of the class's
environment. -/
def MajorCtors (fe : FEnv) (p : BlockShape) (M : TargetMajor) : Prop :=
  ∀ c ∈ M.ctors, (∃ ms ∈ p.members, c ∈ ms.ctors) ∨ ∃ cv nP nF T, fe.find? c.1.name = some (.ctorInfo cv nP nF T)

theorem find?_name {A : Env} {n : Name} {c : ConstantInfo} (h : A.find? n = some c) : c.name = n := by
  unfold Env.find? at h
  simpa using List.find?_some h

theorem targetCtorsOf_stored {A : Env} {I : Name} {q : Nat × List (ConstantVal × Nat)}
    (h : targetCtorsOf (mkFEnv A) I = some q) :
    ∀ c ∈ q.2, ∃ cv nP nF T, A.find? c.1.name = some (.ctorInfo cv nP nF T) := by
  have hf : (mkFEnv A).find? = A.find? := mkFEnv_find?_fun A
  unfold targetCtorsOf nestContainer at h
  rw [hf] at h
  dsimp only at h
  split at h
  · rename_i cv caps hI
    generalize hcs : caps.ctors.filterMap (fun n => (A.find? n).bind (nestCtorEntry I)) = cs at h
    have hmem : ∀ x ∈ cs, ∃ cv nP nF T, A.find? x.1.name = some (.ctorInfo cv nP nF T) := by
      intro x hx
      rw [← hcs] at hx
      obtain ⟨n, -, hn⟩ := List.mem_filterMap.mp hx
      cases hfn : A.find? n with
      | none => rw [hfn] at hn; cases hn
      | some ci =>
        rw [hfn] at hn
        simp only [Option.bind_some] at hn
        unfold nestCtorEntry at hn
        split at hn
        · rename_i cv' nPc nF T
          split at hn
          · split at hn
            · split at hn
              · simp only [Option.some.injEq] at hn; subst hn
                have := find?_name hfn
                simp only [ConstantInfo.name, ConstantInfo.toConstantVal] at this
                exact ⟨cv', nPc, nF, T, by rw [this]; exact hfn⟩
              · cases hn
            · cases hn
          · cases hn
        · cases hn
    cases cs with
    | nil => simp only [Option.some.injEq] at h; subst h; intro c hc; exact nomatch hc
    | cons x tl =>
      obtain ⟨c0, nPc, nF⟩ := x
      simp only [Option.some.injEq] at h; subst h
      intro c hcm
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hcm
      exact hmem x hx
  · cases h

/-- What a class says of its constructors and its openers. -/
def MajorFacts (A : Env) (p : BlockShape) (pfvs : List Expr) (M : TargetMajor) : Prop :=
  M.pfvs = pfvs ∧ ∀ c ∈ M.ctors, (∃ ms ∈ p.members, c ∈ ms.ctors) ∨
    ∃ cv nP nF T, A.find? c.1.name = some (.ctorInfo cv nP nF T)

theorem targetMajorOf_facts {A : Env} {ops : CheckerOps CheckM} {p : BlockShape} {pfvs fvs : List Expr}
    {mty : Expr} {M : TargetMajor} (h : targetMajorOf ops (mkFEnv A) p pfvs fvs mty = .ok M) :
    MajorFacts A p pfvs M := by
  obtain ⟨⟨R⟩, hpf⟩ := targetMajorOf_run h
  refine ⟨hpf, ?_⟩
  cases R with
  | member I t ms hfn ht hms hpar nfs =>
    intro c hc
    exact Or.inl ⟨ms, List.mem_of_getElem? hms, hc⟩
  | outside I us nPc nIdx ctors sI hfn ht hnq hct hdsLen hdsSc hment hinst hsort nfs =>
    intro c hc
    exact Or.inr (targetCtorsOf_stored hct c hc)

theorem classMajors_facts {A : Env} {F : Nat} {p : BlockShape} {pfvs : List Expr} :
    ∀ {keys : List ClassKey} {Ms : List TargetMajor},
      classMajors (m := CheckM) (fueledOps .verified F) (mkFEnv A) p pfvs keys = .ok Ms →
      ∀ M ∈ Ms, MajorFacts A p pfvs M
  | [], Ms, h, M, hM => by
    simp only [classMajors, pure, Except.pure, Except.ok.injEq] at h; subst h; exact nomatch hM
  | key :: keys, Ms, h, M, hM => by
    unfold classMajors at h
    obtain ⟨M0, h0, h⟩ := exceptBind_ok h
    obtain ⟨-, -, h⟩ := exceptBind_ok h
    obtain ⟨Ms', h', h⟩ := exceptBind_ok h
    simp only [pure, Except.pure, Except.ok.injEq] at h
    subst h
    rcases List.mem_cons.mp hM with rfl | hM
    · exact targetMajorOf_facts h0
    · exact classMajors_facts h' M hM

theorem checkBlockClasses_facts {A : Env} {F : Nat} {p : BlockShape} {params : List Expr} {rd : ClassRead}
    {Ms : List TargetMajor}
    (h : checkBlockClasses (m := CheckM) (fueledOps .verified F) (mkFEnv A) p params = .ok (rd, Ms)) :
    ∀ M ∈ Ms, MajorFacts A p params M := by
  unfold checkBlockClasses at h
  obtain ⟨rd', -, h⟩ := exceptBind_ok h
  obtain ⟨keys, -, h⟩ := exceptBind_ok h
  obtain ⟨Ms', hMs, h⟩ := exceptBind_ok h
  split at h
  · simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    exact classMajors_facts hMs
  · kill h

theorem sumRules_ctor : ∀ {cs : List (ConstantVal × Nat)} {rhss : List Expr} {rl : RecRule},
    rl ∈ sumRules cs rhss → ∃ c ∈ cs, rl.ctor = c.1.name
  | [], _, _, h => by simp [sumRules] at h
  | _ :: _, [], _, h => by simp [sumRules] at h
  | c :: cs, rhs :: rhss, rl, h => by
    simp only [sumRules, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨c, List.mem_cons_self .., rfl⟩
    · obtain ⟨c', hc', he⟩ := sumRules_ctor h
      exact ⟨c', List.mem_cons_of_mem _ hc', he⟩

theorem generatedRules_ctor {rP : Nat} {M : TargetMajor} {rhss : List Expr} {rl : RecRule}
    (h : rl ∈ generatedRules rP M rhss) : ∃ c ∈ M.ctors, rl.ctor = c.1.name := by
  unfold generatedRules at h
  dsimp only at h
  split at h
  · obtain ⟨rl', h', rfl⟩ := List.mem_map.mp h
    obtain ⟨c, hc, he⟩ := sumRules_ctor h'
    exact ⟨c, hc, he⟩
  · exact sumRules_ctor h

theorem mem_blockRecInfosTF {p : BlockShape} :
    ∀ {m : Nat} {out : List (ConstantVal × TargetMajor × List Expr)} {c : ConstantInfo},
      c ∈ blockRecInfosTF p m out → ∃ g ∈ out, ∃ a b k, c = .recInfo g.1 a b k (generatedRules b g.2.1 g.2.2)
  | _, [], _, h => nomatch h
  | m, (cv, M, rhss) :: rest, c, h => by
    simp only [blockRecInfosTF, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨(cv, M, rhss), List.mem_cons_self .., _, _, _, rfl⟩
    · obtain ⟨g, hg, a, b, k, he⟩ := mem_blockRecInfosTF h
      exact ⟨g, List.mem_cons_of_mem _ hg, a, b, k, he⟩

theorem blockRecInfosTF_names {p : BlockShape} :
    ∀ (m : Nat) (out : List (ConstantVal × TargetMajor × List Expr)),
      (blockRecInfosTF p m out).map (·.name) = out.map (·.1.name)
  | _, [] => rfl
  | m, (cv, M, rhss) :: rest => by
    simp only [blockRecInfosTF, List.map_cons]
    rw [blockRecInfosTF_names (m + 1) rest]
    rfl

/-- The constructors' push. -/
def ctorsR (nP : Nat) (L : List (Name × List (ConstantVal × Nat))) : List ConstantInfo :=
  (L.flatMap fun g => g.2.map fun c => ConstantInfo.ctorInfo c.1 nP c.2 g.1).reverse

theorem mem_ctorsR {nP : Nat} {L : List (Name × List (ConstantVal × Nat))} {ci : ConstantInfo}
    (h : ci ∈ ctorsR nP L) : ∃ g ∈ L, ∃ c ∈ g.2, ci = .ctorInfo c.1 nP c.2 g.1 := by
  simp only [ctorsR, List.mem_reverse, List.mem_flatMap, List.mem_map] at h
  obtain ⟨g, hg, c, hc, rfl⟩ := h
  exact ⟨g, hg, c, hc, rfl⟩

theorem find?_ctor_prepend {R : List ConstantInfo} {X : Env} (ts : List ProjTable)
    (hR : ∀ c ∈ R, ∃ cv nP nF T, c = .ctorInfo cv nP nF T) {n : Name}
    (h : n ∈ R.map (·.name) ∨ ∃ cv nP nF T, X.find? n = some (.ctorInfo cv nP nF T)) :
    ∃ cv nP nF T, Env.find? ⟨R ++ X.consts, ts⟩ n = some (.ctorInfo cv nP nF T) := by
  rw [find?_prepend]
  cases hr : R.find? (·.name == n) with
  | some c =>
    obtain ⟨cv, nP, nF, T, rfl⟩ := hR c (List.mem_of_find?_eq_some hr)
    exact ⟨cv, nP, nF, T, rfl⟩
  | none =>
    rcases h with hm | ⟨cv, nP, nF, T, hf⟩
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
      rw [List.find?_eq_none] at hr; exact absurd (hr x hx) (by simp)
    · exact ⟨cv, nP, nF, T, by rw [show Env.find? ⟨X.consts, ts⟩ n = X.find? n from rfl, hf]; rfl⟩

/-- **The tail at an extension.** -/
theorem checkBlockTail_ext {A₁ A₂ : Env} (hxA : EnvExt A₁ A₂) (htA : TablesStored A₂) (F : Nat)
    (block : List ConstantInfo) (q : BlockPass Env) (hq : q.env₁ = A₁) (Q : List ProjTable)
    (hT : ∀ ms ∈ q.p.members, Res A₁ ms.cvT.type)
    (hMf : ∀ M ∈ q.cls, MajorFacts A₁ q.p q.params M) (hMo : ∀ M ∈ q.cls, ClassOutParams q.p.nP M)
    (hpar : ResL A₁ q.params) (hpl : q.params.length = q.p.nP)
    (hCn : ∀ ms ∈ q.p.members, ∀ c ∈ ms.ctors, NameOK c.1.name ∧ A₂.find? c.1.name = none)
    (hRn : ∀ rc ∈ q.p.recs, NameOK rc.cvR.name ∧
      (consBlockCtors q.p.nP q.p.ctorGroups A₂).find? rc.cvR.name = none)
    (hwC : EnvWF (consBlockCtors q.p.nP q.p.ctorGroups A₁))
    (h : checkBlockTail (m := CheckM) (fueledOps .verified F) block q Q = .ok ()) :
    checkBlockTail (m := CheckM) (fueledOps .verified F) block { q with env₁ := A₂ } Q = .ok () := by
  subst hq
  unfold checkBlockTail at h ⊢
  dsimp only at h ⊢
  -- the index sorts
  obtain ⟨u, h1, h⟩ := exceptBind_ok h
  cases u
  rw [checkBlockIdxSorts_ext hxA F q.p q.p.members hT h1]
  simp only [bind, Except.bind] at h ⊢
  -- the constructors' environment
  have eC : ∀ X : Env, consBlockCtors q.p.nP q.p.ctorGroups X = ⟨ctorsR q.p.nP q.p.ctorGroups ++ X.consts, X.tables⟩ :=
    fun X => consBlockCtors_eq q.p.nP q.p.ctorGroups X
  have hRC : ∀ c ∈ ctorsR q.p.nP q.p.ctorGroups, ∃ ms ∈ q.p.members, ∃ c' ∈ ms.ctors, c.name = c'.1.name := by
    intro c hc
    obtain ⟨g, hg, c', hc', rfl⟩ := mem_ctorsR hc
    simp only [BlockShape.ctorGroups, List.mem_map] at hg
    obtain ⟨ms, hms, rfl⟩ := hg
    exact ⟨ms, hms, c', hc', rfl⟩
  have hxC : EnvExt (consBlockCtors q.p.nP q.p.ctorGroups q.env₁) (consBlockCtors q.p.nP q.p.ctorGroups A₂) := by
    rw [eC, eC]
    have := envExt_prepend (X₁ := q.env₁) (X₂ := A₂) (ctorsR q.p.nP q.p.ctorGroups) [] hxA htA (fun _ h => nomatch h)
      (fun c hc => by obtain ⟨ms, hms, c', hc', he⟩ := hRC c hc; rw [he]; exact hCn ms hms c' hc')
      (by rw [eC] at hwC; simpa using hwC)
      (fun c hc cv mI rP isK rules he => by obtain ⟨_, _, _, _, rfl⟩ := mem_ctorsR hc; cases he)
      (fun _ h => nomatch h)
    simpa using this
  have htC : TablesStored (consBlockCtors q.p.nP q.p.ctorGroups A₂) := by
    rw [eC]; have := tablesStored_prepend (X := A₂) (ctorsR q.p.nP q.p.ctorGroups) [] htA (fun _ h => nomatch h)
    simpa using this
  have hresC : ∀ {e}, Res q.env₁ e → Res (consBlockCtors q.p.nP q.p.ctorGroups q.env₁) e := fun he => by
    rw [eC]; exact res_prepend _ _ he
  -- the generated recursors
  obtain ⟨out, h2, h⟩ := exceptBind_ok h
  have h2' : genRecCheck (m := CheckM) (fueledOps .verified F) (mkFEnv (consBlockCtors q.p.nP q.p.ctorGroups q.env₁))
      q.p (blockNestedBit q.p q.kinds) q.params q.tbl.toList q.rd q.cls block = .ok out := h2
  have hgr : GenRecRes (consBlockCtors q.p.nP q.p.ctorGroups q.env₁) q.p q.cls :=
    ⟨fun cv hcv => by
        simp only [BlockShape.formers, List.mem_map] at hcv
        obtain ⟨ms, hms, rfl⟩ := hcv; exact hresC (hT ms hms),
     fun M hM => by rw [(hMf M hM).1]; exact fun x hx => hresC (hpar x hx)⟩
  have h2'' := genRecCheck_ext hxC htC F q.p _ q.params q.tbl.toList q.rd q.cls block hgr hRn h2'
  show (checkBlockRec (m := CheckM) (fueledOps .verified F) (consBlockCtors q.p.nP q.p.ctorGroups A₂) q.p
      (blockNestedBit q.p q.kinds) q.params q.tbl.toList q.rd q.cls block >>= _) = _
  unfold checkBlockRec
  rw [h2'']
  simp only [bind, Except.bind] at h ⊢
  obtain ⟨u, h3, h⟩ := exceptBind_ok h
  rw [h3]
  simp only [bind, Except.bind] at h ⊢
  -- the stream's recursors
  have hMs : ∀ M ∈ q.cls, ∀ c ∈ M.ctors, ∃ cv nP nF T,
      (consBlockCtors q.p.nP q.p.ctorGroups q.env₁).find? c.1.name = some (.ctorInfo cv nP nF T) := by
    intro M hM c hc
    rw [eC]
    refine find?_ctor_prepend _ (fun c' hc' => by obtain ⟨g, -, c'', -, rfl⟩ := mem_ctorsR hc'; exact ⟨_, _, _, _, rfl⟩) ?_
    rcases (hMf M hM).2 c hc with ⟨ms, hms, hc'⟩ | hst
    · left
      simp only [ctorsR, List.map_reverse, List.mem_reverse, List.map_flatMap, List.mem_flatMap, List.map_map]
      exact ⟨(ms.cvT.name, ms.ctors), List.mem_map_of_mem hms, by
        simp only [List.mem_map, Function.comp_def]
        exact ⟨c, hc', rfl⟩⟩
    · exact Or.inr hst
  obtain ⟨hOres, hOct⟩ := genRecCheck_outFacts h2' hMs
  have hwR := ConLeche.Cached.genRecCheck_recsWF hwC h2' hpl hMo
  have hnames := ConLeche.Cached.genRecCheck_out_names h2'
  have hfreshO := genRecCheck_out_fresh h2'
  have eR : ∀ X : Env, consBlockRecsT q.p 0 out X = ⟨(blockRecInfosTF q.p 0 out).reverse ++ X.consts, X.tables⟩ :=
    fun X => consBlockRecsT_eq_infos q.p out 0 X
  have hxR : EnvExt (consBlockRecsT q.p 0 out (consBlockCtors q.p.nP q.p.ctorGroups q.env₁))
      (consBlockRecsT q.p 0 out (consBlockCtors q.p.nP q.p.ctorGroups A₂)) := by
    rw [eR, eR]
    have hnm : ∀ c ∈ (blockRecInfosTF q.p 0 out).reverse, ∃ g ∈ out, c.name = g.1.name := by
      intro c hc
      obtain ⟨g, hg, a, b, k, rfl⟩ := mem_blockRecInfosTF (List.mem_reverse.mp hc)
      exact ⟨g, hg, rfl⟩
    have hgrec : ∀ g ∈ out, ∃ rc ∈ q.p.recs, g.1.name = rc.cvR.name := by
      intro g hg
      have : g.1.name ∈ q.p.recs.map (·.cvR.name) := by rw [← hnames]; exact List.mem_map_of_mem hg
      obtain ⟨rc, hrc, he⟩ := List.mem_map.mp this
      exact ⟨rc, hrc, he.symm⟩
    have := envExt_prepend (X₁ := consBlockCtors q.p.nP q.p.ctorGroups q.env₁)
      (X₂ := consBlockCtors q.p.nP q.p.ctorGroups A₂) (blockRecInfosTF q.p 0 out).reverse [] hxC htC
      (fun _ h => nomatch h)
      (fun c hc => by
        obtain ⟨g, hg, hcn⟩ := hnm c hc
        obtain ⟨rc, hrc, hgn⟩ := hgrec g hg
        rw [hcn, hgn]; exact hRn rc hrc)
      (by rw [eR] at hwR; simpa using hwR)
      (fun c hc cv mI rP isK rules he r hr => by
        obtain ⟨g, hg, a, b, k, hge⟩ := mem_blockRecInfosTF (List.mem_reverse.mp hc)
        rw [hge] at he
        simp only [ConstantInfo.recInfo.injEq] at he
        obtain ⟨-, -, -, -, rfl⟩ := he
        obtain ⟨c', hc', hrc'⟩ := generatedRules_ctor hr
        obtain ⟨cv', nP', nF', T', hf⟩ := hOct g hg c' hc'
        refine ⟨cv', nP', nF', T', ?_⟩
        have hnR : r.ctor ∉ ((blockRecInfosTF q.p 0 out).reverse).map (·.name) := by
          intro hm
          rw [List.map_reverse, List.mem_reverse, blockRecInfosTF_names] at hm
          obtain ⟨o, ho, hon⟩ := List.mem_map.mp hm
          have := hfreshO o ho
          rw [hon, hrc', hf] at this; cases this
        rw [find?_prepend_of_not_mem hnR, hrc']
        simpa using hf)
      (fun _ h => nomatch h)
    simpa using this
  obtain ⟨u, h4, h⟩ := exceptBind_ok h
  cases u
  have hresR : ∀ {e}, Res (consBlockCtors q.p.nP q.p.ctorGroups q.env₁) e →
      Res (consBlockRecsT q.p 0 out (consBlockCtors q.p.nP q.p.ctorGroups q.env₁)) e := fun he => by
    rw [eR]; exact res_prepend _ _ he
  rw [streamRecsCheck_ext hxR F q.p.recs out (fun g hg => ⟨hresR (hOres g hg).1, (hOres g hg).2⟩) h4]
  simp only [bind, Except.bind] at h ⊢
  exact checkBlockTables_ext hxC Q h

end ConPanqueque.Pipeline.IndExt
