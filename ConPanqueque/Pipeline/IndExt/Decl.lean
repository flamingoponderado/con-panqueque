import ConPanqueque.Pipeline.IndExt.Block
import ConLeche.Verify.Cached.PureRun
import ConLeche.Verify.Cached.Scoped
import ConLeche.Semantics.DeclWF

/-! # An inductive declaration at an extension of the environment -/

namespace ConPanqueque.Pipeline.IndExt

open ConLeche ConLeche.Verify ConPanqueque.Pipeline

set_option autoImplicit false

theorem ruleReadsB_ctor {f : Name → Option ConstantInfo} {cv : ConstantVal} {mI rP i : Nat} {rl : RecRule}
    (h : ruleReadsB f cv mI rP i rl = true) : ∃ cvj cnP cnF T, f rl.ctor = some (.ctorInfo cvj cnP cnF T) := by
  unfold ruleReadsB at h
  split at h
  · rename_i p' cvj cnP a b hp hf
    exact ⟨cvj, cnP, a, b, hf⟩
  · exact nomatch h

theorem checkDecl_indK {F : Nat} {pins : List NatOpPinSet} {env E : Env} {block : List ConstantInfo} {nP : Nat}
    (h : checkDecl .verified (fueledOps .verified F) pins env (.indDecl block nP) = .ok E) :
    indParamsOk nP block = true ∧ ∃ p₀, readBlock nP block = .ok p₀ ∧
      checkBlock (m := CheckM) (fueledOps .verified F) env block p₀ = .ok E ∧ blockReadsOk E.find? p₀ = .ok () := by
  obtain ⟨hK, -⟩ := ConLeche.checkDecl_inv h
  simp only [ConLeche.checkDeclKind] at hK
  by_cases hok : indParamsOk nP block = true
  · rw [ite_eq_left hok] at hK
    refine ⟨hok, ?_⟩
    cases hp : readBlock nP block with
    | error e => rw [hp] at hK; exact nomatch hK
    | ok p₀ =>
      rw [hp] at hK
      simp only at hK
      obtain ⟨E₁, h1, h2⟩ := exceptBind_ok hK
      cases hr : blockReadsOk E₁.find? p₀ with
      | error e => rw [hr] at h2; exact nomatch h2
      | ok u =>
        rw [hr] at h2
        obtain rfl := Except.ok.inj h2
        cases u
        exact ⟨p₀, rfl, h1, hr⟩
  · rw [ite_eq_right hok] at hK
    exact nomatch hK

theorem blockRecs_isRec (p : BlockShape) : ∀ {rcs : List RecShape} {c : ConstantInfo}, c ∈ blockRecs p rcs →
    ∃ cv mI rP isK rules, c = .recInfo cv mI rP isK rules
  | [], _, h => nomatch h
  | rc :: rest, c, h => by
    simp only [blockRecs, List.mem_cons] at h
    rcases h with rfl | h
    · exact ⟨_, _, _, _, _, rfl⟩
    · exact blockRecs_isRec p h

variable {env₁ env₂ : Env}

/-- **An inductive declaration carries over to an extension.** -/
theorem checkDecl_ind_ext (hx : EnvExt env₁ env₂) (hw2 : EnvWF env₂) (hca : CtorsAgree env₁ env₂) (F : Nat)
    (pins pins' : List NatOpPinSet) (block : List ConstantInfo) (nP : Nat)
    (hfr : ∀ c ∈ declConstants (.indDecl block nP), NameOK c.name ∧ env₂.find? c.name = none) {E : Env}
    (h : checkDecl .verified (fueledOps .verified F) pins env₁ (.indDecl block nP) = .ok E) :
    ∃ E₂, checkDecl .verified (fueledOps .verified F) pins' env₂ (.indDecl block nP) = .ok E₂ ∧ EnvExt E E₂ ∧
      EnvWF E₂ ∧ CtorsAgree E E₂ ∧
      E = env₁.pushDelta (declConstants (.indDecl block nP)) (declTables (.indDecl block nP)) ∧
      E₂ = env₂.pushDelta (declConstants (.indDecl block nP)) (declTables (.indDecl block nP)) := by
  have hwE : EnvWF E := ConLeche.Semantics.checkDecl_envWF hx.facts.wf h
  obtain ⟨hnd, -⟩ := ConLeche.Cached.checkDecl_fresh h
  have hEp := ConLeche.Cached.checkDecl_pushes h
  have hb := checkDecl_basis h
  obtain ⟨hok, p₀, hp, hcb, hrd⟩ := checkDecl_indK h
  have hdc : declConstants (.indDecl block nP) = blockConstants p₀ := by simp [declConstants, hp]
  have hdt : declTables (.indDecl block nP) = (blockTables p₀ p₀.members).getD [] := by simp [declTables, hp]
  rw [hdc] at hnd hfr
  have hcb2 := checkBlock_ext hx (tablesStored_of_wf hw2) hca F block p₀ (ConLeche.readBlock_declared hp) hnd
    (fun n hn => by obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn; exact hfr c hc) hcb
  generalize hQ : (blockTables p₀ p₀.members).getD [] = Q at *
  have eE : E = ⟨(blockConstants p₀).reverse ++ env₁.consts, Q.reverse ++ env₁.tables⟩ := by
    rw [hEp, hdc, hdt]; rfl
  have hxE : EnvExt E (env₂.pushDelta (blockConstants p₀) Q) := by
    rw [eE]
    refine envExt_prepend _ _ hx (tablesStored_of_wf hw2) (fun t ht => ?_)
      (fun c hc => hfr c (List.mem_reverse.mp hc)) (by rw [← eE]; exact hwE) ?_ ?_
    · obtain ⟨cv, caps, hm, hn⟩ := ConLeche.Cached.declTables_former (e := .indDecl block nP)
        (by rw [hdt]; exact List.mem_reverse.mp ht)
      rw [hdc] at hm
      exact List.mem_map.mpr ⟨_, List.mem_reverse.mpr hm, hn⟩
    · intro c hc cv mI rP isK rules he r hr
      have hci : c ∈ blockRecs p₀ p₀.recs := ConLeche.Cached.blockConstants_rec (List.mem_reverse.mp hc) he
      have hreads := ConLeche.blockReadsOk_reads hrd c hci
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hr
      have := hreads cv mI rP isK rules he i r hi
      rw [← eE]
      exact ruleReadsB_ctor this
    · intro t ht
      cases hbt : blockTables p₀ p₀.members with
      | none => rw [hbt] at hQ; simp only [Option.getD_none] at hQ; subst hQ; simp at ht
      | some Q' =>
      rw [hbt] at hQ; simp only [Option.getD_some] at hQ; subst hQ
      have hQ' := hbt
      obtain ⟨ms, hms, c, hc, hct⟩ := ConLeche.Cached.blockTables_ctor p₀ _ _ hQ' t (List.mem_reverse.mp ht)
      rw [hct]
      apply find?_mem_name
      rw [List.map_reverse, List.mem_reverse, ConLeche.Cached.blockConstants_names]
      exact List.mem_append_left _ (List.mem_append_right _
        (List.mem_map_of_mem (List.mem_flatten.mpr ⟨ms.ctors, List.mem_map_of_mem hms, hc⟩)))
  have hrd2 : blockReadsOk (env₂.pushDelta (blockConstants p₀) Q).find? p₀ = .ok () :=
    blockReadsOk_mono (grows_ext hxE) p₀ hrd
  have h2 : checkDecl .verified (fueledOps .verified F) pins' env₂ (.indDecl block nP) =
      .ok (env₂.pushDelta (blockConstants p₀) Q) := by
    unfold checkDecl
    simp only [ConLeche.checkDeclKind, hok, ↓reduceIte, hp, bind, Except.bind]
    rw [hcb2]
    simp only [hrd2, hb, pure, Except.pure]
    rfl
  refine ⟨_, h2, hxE, ConLeche.Semantics.checkDecl_envWF hw2 h2, ?_, by rw [hEp, hdc, hdt], by rw [hdc, hdt]⟩
  rw [eE]
  refine ctorsAgree_prepend _ _ _ hca (fun c hc cv caps he n hn => Or.inl ?_)
  have hc' := List.mem_reverse.mp hc
  unfold blockConstants at hc'
  rcases List.mem_append.mp hc' with hc' | hc'
  · rcases List.mem_append.mp hc' with hc' | hc'
    · unfold blockFormers at hc'
      obtain ⟨⟨cv', i⟩, -, rfl⟩ := List.mem_map.mp hc'
      simp only [ConstantInfo.indInfo.injEq] at he
      obtain ⟨-, rfl⟩ := he
      obtain ⟨ms, hms, c', hc'', rfl⟩ := blockCapsAt_ctors_mem hn
      rw [List.map_reverse, List.mem_reverse, ConLeche.Cached.blockConstants_names]
      exact List.mem_append_left _ (List.mem_append_right _
        (List.mem_map_of_mem (List.mem_flatten.mpr ⟨ms.ctors, List.mem_map_of_mem hms, hc''⟩)))
    · unfold blockCtors at hc'
      obtain ⟨_, -, hc'⟩ := List.mem_flatMap.mp hc'
      obtain ⟨_, -, rfl⟩ := List.mem_map.mp hc'
      cases he
  · obtain ⟨cv', mI, rP, isK, rules, rfl⟩ : ∃ cv' mI rP isK rules, c = .recInfo cv' mI rP isK rules := by
      exact blockRecs_isRec p₀ hc'
    cases he

end ConPanqueque.Pipeline.IndExt
