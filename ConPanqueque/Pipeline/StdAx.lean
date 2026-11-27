import ConPanqueque.Pipeline.Ext

/-! # The standard axioms at an extension of the environment

An accepted standard axiom record (`propext`, `Classical.choice`, `Lean.trustCompiler`,
`Lean.ofReduceNat`, `Lean.ofReduceBool`) reads the environment only through lookups that hit
(`stdAxiomOk`, `trustCompilerOk`, `ofReduceAxOk`) and through its constant check; both carry over to
an extension. -/

namespace ConPanqueque.Pipeline

open ConLeche ConLeche.Verify

set_option autoImplicit true

/-- The standard axioms' names. -/
def StdAxName (n : Name) : Prop :=
  n = propextName ∨ n = choiceName ∨ n = trustCompilerName ∨ n = ofReduceNatName ∨ n = ofReduceBoolName

instance (n : Name) : Decidable (StdAxName n) := by unfold StdAxName; infer_instance

/-- A lookup that hits at `env₁` hits alike at `env₂`. -/
theorem match_hit {α : Type} (hx : EnvExt env₁ env₂) (n : Name) (k : ConstantInfo → α) (d : α) (p : α → Prop)
    (h : p (match env₁.find? n with | some ci => k ci | none => d)) (hd : ¬ p d) :
    p (match env₂.find? n with | some ci => k ci | none => d) := by
  cases hf : env₁.find? n with
  | none => rw [hf] at h; exact absurd h hd
  | some ci => rw [hf] at h; rw [hx.find n ci hf]; exact h

theorem isSome_hit (hx : EnvExt env₁ env₂) {n : Name} (h : (env₁.find? n).isSome = true) :
    (env₂.find? n).isSome = true := by rw [hx.find_of_isSome h]; exact h

theorem stdAxiomOk_mono (hx : EnvExt env₁ env₂) {cv : ConstantVal} (h : stdAxiomOk env₁ cv = true) :
    stdAxiomOk env₂ cv = true := by
  unfold stdAxiomOk at h ⊢
  split at h
  · rename_i h1
    rw [if_pos h1]
    simp only [Bool.and_eq_true] at h ⊢
    obtain ⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩ := h
    refine ⟨⟨⟨⟨isSome_hit hx a, ?_⟩, ?_⟩, ?_⟩, e⟩
    · revert b; cases hf : env₁.find? iffName with
      | none => simp
      | some ci => rw [hx.find _ _ hf]; exact id
    · revert c; cases hf : env₁.find? iffIntroName with
      | none => simp
      | some ci => rw [hx.find _ _ hf]; exact id
    · revert d; cases hf : env₁.find? iffRecName with
      | none => simp
      | some ci => rw [hx.find _ _ hf]; exact id
  · rename_i h1
    rw [if_neg h1]
    split at h
    · rename_i h2
      rw [if_pos h2]
      simp only [Bool.and_eq_true] at h ⊢
      obtain ⟨⟨⟨b, c⟩, d⟩, e⟩ := h
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, e⟩
      · revert b; cases hf : env₁.find? nonemptyName with
        | none => simp
        | some ci => rw [hx.find _ _ hf]; exact id
      · revert c; cases hf : env₁.find? nonemptyIntroName with
        | none => simp
        | some ci => rw [hx.find _ _ hf]; exact id
      · revert d; cases hf : env₁.find? nonemptyRecName with
        | none => simp
        | some ci => rw [hx.find _ _ hf]; exact id
    · exact absurd h (by simp)

theorem trustCompilerOk_mono (hx : EnvExt env₁ env₂) {cv : ConstantVal} (h : trustCompilerOk env₁ cv = true) :
    trustCompilerOk env₂ cv = true := by
  unfold trustCompilerOk at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨b, c⟩, e⟩ := h
  refine ⟨⟨?_, ?_⟩, e⟩
  · revert b; cases hf : env₁.find? trueName with
    | none => simp
    | some ci => rw [hx.find _ _ hf]; exact id
  · revert c; cases hf : env₁.find? trueIntroName with
    | none => simp
    | some ci => rw [hx.find _ _ hf]; exact id

theorem ofReduceAxOk_mono (hx : EnvExt env₁ env₂) {cv : ConstantVal} (h : ofReduceAxOk env₁ cv = true) :
    ofReduceAxOk env₂ cv = true := by
  unfold ofReduceAxOk reduceElemOk reduceStoredOk at h ⊢
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨a, b⟩, c⟩, e⟩ := h
  refine ⟨⟨⟨isSome_hit hx a, ?_⟩, ?_⟩, e⟩
  · split at b
    · rename_i h1; rw [if_pos h1]
      revert b; cases hf : env₁.find? natName with
      | none => simp
      | some ci => rw [hx.find _ _ hf]; exact id
    · rename_i h1; rw [if_neg h1]
      revert b; cases hf : env₁.find? boolName with
      | none => simp
      | some ci => rw [hx.find _ _ hf]; exact id
  · revert c; cases hf : env₁.find? (ofReduceOp cv.name) with
    | none => simp
    | some ci => rw [hx.find _ _ hf]; exact id

theorem stdAxName_nameOK {n : Name} (h : StdAxName n) : NameOK n := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> (unfold NameOK; decide)

theorem stdAx_not_quotSound {n : Name} (h : StdAxName n) : ¬ n = quotSoundName := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

theorem stdAx_not_sorry {n : Name} (h : StdAxName n) : ¬ n = sorryAxName := by
  rcases h with rfl | rfl | rfl | rfl | rfl <;> decide

/-- The axiom arm past its constant check: the standard axioms' acceptance. -/
def axTail (env : Env) (c : ConstantVal) : CheckM Env :=
  if stdAxiomOk env c then pure ⟨.axiomInfo c :: env.consts, env.tables⟩
  else if c.name = trustCompilerName then
    (if trustCompilerOk env c then pure ⟨.axiomInfo c :: env.consts, env.tables⟩
     else throw (.notImplemented s!"unsupported Lean.trustCompiler shape ({c.name})"))
  else if c.name = ofReduceNatName ∨ c.name = ofReduceBoolName then
    (if ofReduceAxOk env c then pure ⟨.axiomInfo c :: env.consts, env.tables⟩
     else throw (.notImplemented s!"unsupported compiler-trust axiom environment ({c.name})"))
  else if c.name = propextName ∨ c.name = choiceName then
    throw (.notImplemented s!"standard axiom shape mismatch ({c.name})")
  else if c.name = sorryAxName then pure env
  else throw (.notImplemented (nonStdAxiomMsg c.name))

theorem axTail_ext (hx : EnvExt env₁ env₂) {c : ConstantVal} (hs : StdAxName c.name) {E : Env}
    (h : axTail env₁ c = .ok E) :
    axTail env₂ c = .ok ⟨.axiomInfo c :: env₂.consts, env₂.tables⟩ ∧ E = ⟨.axiomInfo c :: env₁.consts, env₁.tables⟩ := by
  unfold axTail at h ⊢
  by_cases h1 : stdAxiomOk env₁ c = true
  · rw [if_pos h1] at h; rw [if_pos (stdAxiomOk_mono hx h1)]
    exact ⟨rfl, (Except.ok.inj h).symm⟩
  · rw [if_neg h1] at h
    by_cases h1' : stdAxiomOk env₂ c = true
    · rw [if_pos h1']
      -- the record reached a later branch at `env₁`
      split at h
      · split at h
        · exact ⟨rfl, (Except.ok.inj h).symm⟩
        · simp [throw, throwThe, MonadExceptOf.throw] at h
      · split at h
        · split at h
          · exact ⟨rfl, (Except.ok.inj h).symm⟩
          · simp [throw, throwThe, MonadExceptOf.throw] at h
        · split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · split at h
            · exact absurd ‹c.name = sorryAxName› (stdAx_not_sorry hs)
            · simp [throw, throwThe, MonadExceptOf.throw] at h
    · rw [if_neg h1']
      split at h
      · rename_i h2; rw [if_pos h2]
        split at h
        · rename_i h3; rw [if_pos (trustCompilerOk_mono hx h3)]; exact ⟨rfl, (Except.ok.inj h).symm⟩
        · simp [throw, throwThe, MonadExceptOf.throw] at h
      · rename_i h2; rw [if_neg h2]
        split at h
        · rename_i h3; rw [if_pos h3]
          split at h
          · rename_i h4; rw [if_pos (ofReduceAxOk_mono hx h4)]; exact ⟨rfl, (Except.ok.inj h).symm⟩
          · simp [throw, throwThe, MonadExceptOf.throw] at h
        · split at h
          · simp [throw, throwThe, MonadExceptOf.throw] at h
          · split at h
            · exact absurd ‹c.name = sorryAxName› (stdAx_not_sorry hs)
            · simp [throw, throwThe, MonadExceptOf.throw] at h

theorem checkDecl_ax_tail (F : Nat) (pins : List NatOpPinSet) (env : Env) (c : ConstantVal)
    (hq : ¬ c.name = quotSoundName) :
    checkDecl .verified (fueledOps .verified F) pins env (.axiomDecl c) =
      (checkConstantVal (fueledOps .verified F) env c false false true >>= fun _ => axTail env c) >>= fun env₂ =>
        (if basisNamesOk (.axiomDecl c) then pure env₂ else throw (basisNamesError (.axiomDecl c))) := by
  unfold checkDecl checkDeclKind axTail
  simp only [ite_eq_right hq]
  rfl

/-- **A standard axiom record carries over to an extension.** -/
theorem checkDecl_stdAx_ext (hx : EnvExt env₁ env₂) (hw2 : EnvWF env₂) (F : Nat) (pins pins' : List NatOpPinSet)
    (c : ConstantVal) (hs : StdAxName c.name) (hf2 : env₂.find? c.name = none) {E : Env}
    (h : checkDecl .verified (fueledOps .verified F) pins env₁ (.axiomDecl c) = .ok E) :
    ∃ E₂, checkDecl .verified (fueledOps .verified F) pins' env₂ (.axiomDecl c) = .ok E₂ ∧ EnvExt E E₂ ∧
      EnvWF E₂ ∧ E = ⟨.axiomInfo c :: env₁.consts, env₁.tables⟩ ∧ E₂ = ⟨.axiomInfo c :: env₂.consts, env₂.tables⟩ := by
  have hwE : EnvWF E := ConLeche.Semantics.checkDecl_envWF hx.facts.wf h
  have hq := stdAx_not_quotSound hs
  rw [checkDecl_ax_tail F pins env₁ c hq] at h
  obtain ⟨E₁, h1, h⟩ := exceptBind_ok h
  obtain ⟨u, hc, ht⟩ := exceptBind_ok h1
  obtain ⟨ht2, rfl⟩ := axTail_ext hx hs ht
  have hf1 := (checkConstantVal_res F env₁ c false false true hc).2
  have hb : basisNamesOk (.axiomDecl c) = true := by
    by_cases hb : basisNamesOk (.axiomDecl c) = true
    · exact hb
    · rw [if_neg hb] at h; simp [throw, throwThe, MonadExceptOf.throw] at h
  rw [if_pos hb] at h
  obtain rfl := (Except.ok.inj h).symm
  have h2 : checkDecl .verified (fueledOps .verified F) pins' env₂ (.axiomDecl c) =
      .ok ⟨.axiomInfo c :: env₂.consts, env₂.tables⟩ := by
    rw [checkDecl_ax_tail F pins' env₂ c hq, checkConstantVal_ext hx F c false false true hf2 hc]
    simp only [bind, Except.bind, ht2, if_pos hb, pure, Except.pure]
  refine ⟨_, h2, envExt_cons' hx hw2 _ hf1 hf2 hwE (stdAxName_nameOK hs) (fun _ _ _ _ _ he => nomatch he),
    ConLeche.Semantics.checkDecl_envWF hw2 h2, rfl, rfl⟩

end ConPanqueque.Pipeline
