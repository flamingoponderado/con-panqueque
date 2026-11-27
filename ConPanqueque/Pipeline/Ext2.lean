import ConPanqueque.Pipeline.Ext
import ConPanqueque.Pipeline.IndExt.Decl

/-! # Stream records, inductive blocks included, at an extension of the environment

`pureRun_ext` (`Ext.lean`) carries an accepting run of value, `sorryAx` and quotient records over to an
extension.  `pureRun_extI` adds inductive blocks (`checkDecl_ind_ext`), at fresh `NameOK` names none
of which is `Quot.mk`; the run keeps the constructor lists of the stored inductives reading alike on
both sides (`CtorsAgree`). -/

namespace ConPanqueque.Pipeline

open ConLeche ConLeche.Verify ConPanqueque.Pipeline.IndExt

set_option autoImplicit true

/-- A stream record's names: a block's raw names and installed constants', the others' `recName`. -/
def recNames : Declaration → Option (List Name)
  | d@(.indDecl _ _) => some (d.names ++ (declConstants d).map (·.name))
  | d => (recName d).map ([·])

theorem recNames_of_recName {d : Declaration} {n : Name} (h : recName d = some n) : recNames d = some [n] := by
  cases d with
  | indDecl b k => simp [recName, valName] at h
  | _ => simp only [recNames]; rw [h]; rfl

/-- The stream's records at names the guards do not read, the base does not declare, and (for a block)
not `Quot.mk`. -/
def StreamOKI (envP : Env) (ds : List Declaration) : Prop :=
  ∀ d ∈ ds, ∃ ns, recNames d = some ns ∧ ∀ n ∈ ns, NameOK n ∧ envP.find? n = none ∧
    ((∃ b k, d = .indDecl b k) → n ≠ quotMkName)

theorem quotAt_caps (k : QuotKind) (c : ConstantVal) {cv : ConstantVal} {caps : IndCaps}
    (h : quotAt k c = .indInfo cv caps) : caps.ctors = [] := by
  cases k <;> simp [quotAt, quotPin, ConstantInfo.atLps, BasisKind.decls, QuotKind.slot,
      quotBasis, quotA, quotMkA, quotLiftA, quotIndA, quotSoundA] at h
  obtain ⟨-, rfl⟩ := h
  rfl

theorem ctorsAgree_cons {e₁ e₂ : Env} (hca : CtorsAgree e₁ e₂) (c : ConstantInfo)
    (hc : ∀ cv caps, c = .indInfo cv caps → caps.ctors = []) :
    CtorsAgree ⟨c :: e₁.consts, e₁.tables⟩ ⟨c :: e₂.consts, e₂.tables⟩ :=
  ctorsAgree_prepend [c] e₁.tables e₂.tables hca (fun c' hc' cv caps he n hn => by
    rw [List.mem_singleton] at hc'; subst hc'; rw [hc cv caps he] at hn; exact nomatch hn)

end ConPanqueque.Pipeline

namespace ConPanqueque.Pipeline

open ConLeche ConLeche.Verify ConPanqueque.Pipeline.IndExt

theorem ctorsAgree_decl {e₁ e₂ : Env} (hca : CtorsAgree e₁ e₂) (d : Declaration) (hnd : ∀ b k, d ≠ .indDecl b k) :
    CtorsAgree (e₁.pushDelta (declConstants d) (declTables d)) (e₂.pushDelta (declConstants d) (declTables d)) := by
  unfold Env.pushDelta
  refine ctorsAgree_prepend _ _ _ hca (fun c hc cv caps he n hn => ?_)
  rw [List.mem_reverse] at hc
  exfalso
  cases d with
  | indDecl b k => exact hnd b k rfl
  | quotDecl q v =>
    simp only [declConstants, List.mem_singleton] at hc
    subst hc
    rw [quotAt_caps q v he] at hn; exact nomatch hn
  | axiomDecl v =>
    simp only [declConstants] at hc
    split at hc
    · simp only [List.mem_singleton] at hc; subst hc
      rw [quotAt_caps _ v he] at hn; exact nomatch hn
    · split at hc
      · exact nomatch hc
      · simp only [List.mem_singleton] at hc; subst hc; cases he
  | defnDecl v x h => simp only [declConstants, List.mem_singleton] at hc; subst hc; cases he
  | thmDecl v x => simp only [declConstants, List.mem_singleton] at hc; subst hc; cases he
  | opaqueDecl v x => simp only [declConstants, List.mem_singleton] at hc; subst hc; cases he

theorem recNames_cases {d : Declaration} {ns : List Name} (h : recNames d = some ns) :
    (∃ b k, d = .indDecl b k ∧ ns = d.names ++ (declConstants d).map (·.name)) ∨
      (∃ n, recName d = some n ∧ ns = [n] ∧ ∀ b k, d ≠ .indDecl b k) := by
  cases d with
  | indDecl b k => simp only [recNames, Option.some.injEq] at h; exact Or.inl ⟨b, k, rfl, h.symm⟩
  | _ =>
    simp only [recNames] at h
    cases hr : recName _ with
    | none => rw [hr] at h; cases h
    | some n =>
      rw [hr] at h; simp only [Option.map_some, Option.some.injEq] at h
      exact Or.inr ⟨n, rfl, h.symm, fun _ _ he => nomatch he⟩

/-- **An accepting run, inductive blocks included, carries over to an extension.** -/
theorem pureRun_extI {pins pins' : List NatOpPinSet} (envP : Env) : ∀ {ds : List Declaration} {env₁ E₁ env₂ : Env},
    PureRun pins ds env₁ E₁ → EnvExt env₁ env₂ → EnvWF env₂ → StreamOKI envP ds → QuotMkCtor env₁ →
    CtorsAgree env₁ env₂ → (∀ m, env₁.find? m = none → envP.find? m = none → env₂.find? m = none) →
    ∃ E₂, PureRun pins' ds env₂ E₂
  | _, _, _, _, .nil _, _, _, _, _, _, _ => ⟨_, .nil _⟩
  | d :: ds, env₁, _, env₂, .cons ⟨F, hs⟩ rest, hx, hw2, hok, hq, hca, hinv => by
    obtain ⟨ns, hns, hall⟩ := hok d (List.mem_cons_self ..)
    have hok' : StreamOKI envP ds := fun d' hd' => hok d' (List.mem_cons_of_mem _ hd')
    -- the step's environments, pushed alike
    have hinv' : ∀ {E E₂ : Env} (L : List ConstantInfo) (Q : List ProjTable), E = env₁.pushDelta L Q →
        E₂ = env₂.pushDelta L Q → ∀ m, E.find? m = none → envP.find? m = none → E₂.find? m = none := by
      intro E E₂ L Q e1 e2 m hm hmP
      subst e1 e2
      unfold Env.pushDelta at hm ⊢
      obtain ⟨hnm, h1⟩ := ConLeche.Cached.find?_none_append_rev hm
      have hnm' : m ∉ L.reverse.map (·.name) := by rw [List.map_reverse, List.mem_reverse]; exact hnm
      rw [find?_prepend_of_not_mem hnm']
      exact hinv m h1 hmP
    rcases recNames_cases hns with ⟨b, k, rfl, rfl⟩ | ⟨n, hd', rfl, hnd⟩
    · -- an inductive block
      obtain ⟨-, hfr1⟩ := ConLeche.Cached.checkDecl_fresh hs
      have hfr : ∀ c ∈ declConstants (.indDecl b k), NameOK c.name ∧ env₂.find? c.name = none := by
        intro c hc
        obtain ⟨hn, hP, -⟩ := hall c.name (List.mem_append_right _ (List.mem_map_of_mem hc))
        exact ⟨hn, hinv _ (hfr1 c hc) hP⟩
      obtain ⟨E₂, h2, hx', hw', hca', e1, e2⟩ := checkDecl_ind_ext hx hw2 hca F pins pins' b k hfr hs
      have hnq : quotMkName ∉ (declConstants (.indDecl b k)).reverse.map (·.name) := by
        intro hm
        rw [List.map_reverse, List.mem_reverse] at hm
        exact (hall _ (List.mem_append_right _ hm)).2.2 ⟨b, k, rfl⟩ rfl
      obtain ⟨E₃, hr⟩ := pureRun_extI envP rest hx' hw' hok' (by
          rw [e1]; intro ci h
          unfold Env.pushDelta at h
          rw [find?_prepend_of_not_mem hnq] at h
          exact hq ci h) hca' (hinv' _ _ e1 e2)
      exact ⟨E₃, .cons ⟨F, h2⟩ hr⟩
    · obtain ⟨hn, hP, -⟩ := hall n (List.mem_singleton_self _)
      rcases recName_cases hd' with hd | ⟨c, rfl, hsn, rfl⟩ | ⟨kq, c, rfl, rfl⟩ | ⟨c, rfl, hqs, rfl⟩
      · have hf1 := checkDecl_val_fresh F pins env₁ d n hd hs
        obtain ⟨E₂, h2, hx', hw', c, hc, -, e1, e2⟩ :=
          checkDecl_ext hx hw2 F pins pins' d n hd (hinv n hf1 hP) hn hs
        have hb := checkDecl_basis hs
        have hcaE := ctorsAgree_decl hca d hnd
        rw [← ConLeche.Cached.checkDecl_pushes hs, ← ConLeche.Cached.checkDecl_pushes h2] at hcaE
        obtain ⟨E₃, hr⟩ := pureRun_extI envP rest hx' hw' hok'
          (by
            rw [e1]
            refine quotMkCtor_cons hq (fun he => ?_)
            have hn' : n = quotMkName := hc ▸ he
            subst hn'
            exfalso
            cases d <;> simp only [valName, Option.some.injEq, reduceCtorEq] at hd <;>
              simp only [basisNamesOk, hd] at hb <;> exact absurd hb (by decide)) hcaE
          (hinv' _ _ (ConLeche.Cached.checkDecl_pushes hs) (ConLeche.Cached.checkDecl_pushes h2))
        exact ⟨E₃, .cons ⟨F, h2⟩ hr⟩
      · have hf1 := checkDecl_sorry_fresh F pins env₁ c hsn hs
        obtain ⟨rfl, h2⟩ := checkDecl_sorry_ext hx F pins pins' c hsn (hinv _ hf1 hP) hs
        obtain ⟨E₃, hr⟩ := pureRun_extI envP rest hx hw2 hok' hq hca hinv
        exact ⟨E₃, .cons ⟨F, h2⟩ hr⟩
      · obtain ⟨hhit, -, hf1, -⟩ := checkDecl_quot_inv hs
        have hnm := quotHit_name hhit
        obtain ⟨E₂, h2, hx', hw', e1, e2⟩ :=
          checkDecl_quot_ext hx hw2 F pins pins' kq c (hinv _ hf1 (by rw [← hnm]; exact hP)) hq hs
        have hcaE := ctorsAgree_decl hca _ hnd
        rw [← ConLeche.Cached.checkDecl_pushes hs, ← ConLeche.Cached.checkDecl_pushes h2] at hcaE
        obtain ⟨E₃, hr⟩ := pureRun_extI envP rest hx' hw' hok'
          (by rw [e1]; exact quotMkCtor_quot kq c hq) hcaE
          (hinv' _ _ (ConLeche.Cached.checkDecl_pushes hs) (ConLeche.Cached.checkDecl_pushes h2))
        exact ⟨E₃, .cons ⟨F, h2⟩ hr⟩
      · have hs' := hs
        rw [checkDecl_axSound hqs] at hs
        obtain ⟨hhit, -, hf1, -⟩ := checkDecl_quot_inv hs
        have hnm := quotHit_name hhit
        obtain ⟨E₂, h2, hx', hw', e1, e2⟩ :=
          checkDecl_quot_ext hx hw2 F pins pins' .sound c (hinv _ hf1 (by rw [← hnm]; exact hP)) hq hs
        have h2' : checkDecl .verified (fueledOps .verified F) pins' env₂ (.axiomDecl c) = .ok E₂ := by
          rw [checkDecl_axSound hqs]; exact h2
        have hcaE := ctorsAgree_decl hca _ hnd
        rw [← ConLeche.Cached.checkDecl_pushes hs', ← ConLeche.Cached.checkDecl_pushes h2'] at hcaE
        obtain ⟨E₃, hr⟩ := pureRun_extI envP rest hx' hw' hok'
          (by rw [e1]; exact quotMkCtor_quot .sound c hq) hcaE
          (hinv' _ _ (ConLeche.Cached.checkDecl_pushes hs') (ConLeche.Cached.checkDecl_pushes h2'))
        exact ⟨E₃, .cons ⟨F, h2'⟩ hr⟩

/-- **The prelude, then the stream**, inductive blocks included. -/
theorem prelude_then_streamI (pins pins₀ : List NatOpPinSet) (P S : List Declaration) {envP E₁ : Env}
    (hP : PureRun pins P Env.empty envP) (hS : PureRun pins₀ S Env.empty E₁) (hok : StreamOKI envP S) :
    ∃ E, PureRun pins (P ++ S) Env.empty E := by
  have hwP := pureRun_envWF hP ConLeche.Semantics.EnvWF.empty
  obtain ⟨E₂, h2⟩ := pureRun_extI (pins' := pins) envP hS (envExt_empty envP) hwP hok quotMkCtor_empty
    (ctorsAgree_empty envP) (fun _ _ h => h)
  exact ⟨E₂, pureRun_append hP h2⟩

end ConPanqueque.Pipeline
