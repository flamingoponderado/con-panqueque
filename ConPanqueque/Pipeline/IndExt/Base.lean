import ConPanqueque.Pipeline.Ext

/-! # An inductive block's pushes at an extension of the environment

An inductive block's check pushes its constants in stages (the formers, the constructors, the
rule-less recursors, the recursors, the tables).  Each stage pushes the same constants on both
sides of an extension `EnvExt X₁ X₂`.  `envExt_prepend` carries the extension across such a push,
given fresh, `NameOK` names and the facts of the pushed `X₁` side. -/

namespace ConPanqueque.Pipeline.IndExt

open ConLeche ConLeche.Verify ConPanqueque.Pipeline

set_option autoImplicit false

/-- Every stored table's structure is stored (`EnvWF`'s first table fact, which every push keeps). -/
def TablesStored (env : Env) : Prop :=
  ∀ t ∈ env.tables, (env.find? t.structName).isSome = true

theorem tablesStored_of_wf {env : Env} (h : EnvWF env) : TablesStored env :=
  fun t ht => (h.tables t ht).1

theorem find?_prepend (R : List ConstantInfo) (cs : List ConstantInfo) (ts : List ProjTable) (n : Name) :
    Env.find? ⟨R ++ cs, ts⟩ n = (R.find? (·.name == n)).or (Env.find? ⟨cs, ts⟩ n) := by
  simp only [Env.find?, List.find?_append]

theorem find?_prepend_of_not_mem {R : List ConstantInfo} {n : Name} (h : n ∉ R.map (·.name))
    (cs : List ConstantInfo) (ts : List ProjTable) :
    Env.find? ⟨R ++ cs, ts⟩ n = Env.find? ⟨cs, ts⟩ n := by
  rw [find?_prepend]
  have : R.find? (·.name == n) = none := by
    rw [List.find?_eq_none]
    intro x hx hq
    exact h (List.mem_map.mpr ⟨x, hx, by simpa using hq⟩)
  rw [this]; rfl

theorem find?_prepend_isSome {R : List ConstantInfo} {cs : List ConstantInfo} {ts ts' : List ProjTable}
    {n : Name} (h : (Env.find? ⟨cs, ts⟩ n).isSome = true) : (Env.find? ⟨R ++ cs, ts'⟩ n).isSome = true := by
  rw [find?_prepend]
  have : Env.find? ⟨cs, ts'⟩ n = Env.find? ⟨cs, ts⟩ n := rfl
  rw [this]
  cases R.find? (·.name == n) <;> simp_all

theorem find?_prepend_mem {R : List ConstantInfo} {cs : List ConstantInfo} {ts : List ProjTable}
    {n : Name} {ci : ConstantInfo} (h : Env.find? ⟨R ++ cs, ts⟩ n = some ci) :
    (ci ∈ R ∧ ci.name = n) ∨ (n ∉ R.map (·.name) ∧ Env.find? ⟨cs, ts⟩ n = some ci) := by
  rw [find?_prepend] at h
  cases hr : R.find? (·.name == n) with
  | some c =>
    rw [hr] at h
    simp only [Option.some_or, Option.some.injEq] at h
    subst h
    exact Or.inl ⟨List.mem_of_find?_eq_some hr, by simpa using List.find?_some hr⟩
  | none =>
    rw [hr] at h
    refine Or.inr ⟨fun hm => ?_, by simpa using h⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
    rw [List.find?_eq_none] at hr
    exact hr x hx (by simp)

theorem find?_mem_name {R : List ConstantInfo} {cs : List ConstantInfo} {ts : List ProjTable}
    {n : Name} (h : n ∈ R.map (·.name)) : (Env.find? ⟨R ++ cs, ts⟩ n).isSome = true := by
  rw [find?_prepend]
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp h
  cases hr : R.find? (·.name == x.name) with
  | some c => rfl
  | none => rw [List.find?_eq_none] at hr; exact absurd (hr x hx) (by simp)

/-- No stored table at a name the environment does not hold. -/
theorem tables_find_none {env : Env} (ht : TablesStored env) {T : Name} (hT : env.find? T = none) :
    env.tables.find? (·.structName == T) = none := by
  rw [List.find?_eq_none]
  intro t htm hq
  have := ht t htm
  rw [show t.structName = T by simpa using hq, hT] at this
  exact absurd this (by simp)

/-- **The extension across a push.**  The same constants `R` (newest first) and tables `Qr` (newest
first, all at structures of `R`) pushed on both sides of an extension: fresh `NameOK` names, the
pushed `X₁` side well formed, its new recursors' rules and new tables naming stored constructors. -/
theorem envExt_prepend {X₁ X₂ : Env} (R : List ConstantInfo) (Qr : List ProjTable)
    (hx : EnvExt X₁ X₂) (ht2 : TablesStored X₂)
    (hQ : ∀ t ∈ Qr, t.structName ∈ R.map (·.name))
    (hfr : ∀ c ∈ R, NameOK c.name ∧ X₂.find? c.name = none)
    (hwE : EnvWF ⟨R ++ X₁.consts, Qr ++ X₁.tables⟩)
    (hrc : ∀ c ∈ R, ∀ cv mI rP isK rules, c = .recInfo cv mI rP isK rules → ∀ r ∈ rules,
      ∃ cvj cnP cnF T, Env.find? ⟨R ++ X₁.consts, Qr ++ X₁.tables⟩ (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF T))
    (htc : ∀ t ∈ Qr, (Env.find? ⟨R ++ X₁.consts, Qr ++ X₁.tables⟩ t.ctor).isSome = true) :
    EnvExt ⟨R ++ X₁.consts, Qr ++ X₁.tables⟩ ⟨R ++ X₂.consts, Qr ++ X₂.tables⟩ := by
  have ht1 : TablesStored X₁ := tablesStored_of_wf hx.facts.wf
  -- names of `R` are fresh on both sides
  have hfr1 : ∀ n ∈ R.map (·.name), X₁.find? n = none ∧ X₂.find? n = none := by
    intro n hn
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
    have h2 := (hfr c hc).2
    refine ⟨?_, h2⟩
    cases h1 : X₁.find? c.name with
    | none => rfl
    | some ci => rw [hx.find _ ci h1] at h2; cases h2
  have nm : ∀ n, (∃ ci, X₁.find? n = some ci) → n ∉ R.map (·.name) := by
    intro n ⟨ci, h⟩ hm; rw [(hfr1 n hm).1] at h; cases h
  -- the plain lookups
  have fe : ∀ (X : Env) (ts : List ProjTable) n, Env.find? ⟨X.consts, ts⟩ n = X.find? n := fun _ _ _ => rfl
  refine ⟨fun n ci h => ?_, fun T hT => ?_, ?_⟩
  · rcases find?_prepend_mem h with ⟨hm, rfl⟩ | ⟨hn, h1⟩
    · -- found in `R`: the same element on the other side
      rw [find?_prepend] at h ⊢
      have e : Env.find? ⟨X₁.consts, Qr ++ X₁.tables⟩ ci.name = X₁.find? ci.name := rfl
      have e2 : Env.find? ⟨X₂.consts, Qr ++ X₂.tables⟩ ci.name = X₂.find? ci.name := rfl
      have hmn : ci.name ∈ R.map (·.name) := List.mem_map.mpr ⟨ci, hm, rfl⟩
      rw [e2, (hfr1 _ hmn).2]; rw [e, (hfr1 _ hmn).1] at h
      simpa using h
    · rw [find?_prepend_of_not_mem hn] at ⊢
      exact hx.find n ci (by simpa [fe] using h1)
  · unfold Env.findTable?
    have hT2 : (Env.find? ⟨R ++ X₂.consts, Qr ++ X₂.tables⟩ T).isSome = true := by
      by_cases hm : T ∈ R.map (·.name)
      · exact find?_mem_name hm
      · rw [find?_prepend_of_not_mem hm] at hT ⊢
        obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hT
        rw [show Env.find? ⟨X₂.consts, Qr ++ X₂.tables⟩ T = X₂.find? T from rfl, hx.find T ci (by simpa [fe] using hci)]
        rfl
    rw [if_pos hT, if_pos hT2]
    simp only [List.find?_append]
    cases hq : Qr.find? (·.structName == T) with
    | some t => rfl
    | none =>
      simp only [Option.none_or]
      by_cases hm : T ∈ R.map (·.name)
      · rw [tables_find_none ht1 (hfr1 T hm).1, tables_find_none ht2 (hfr1 T hm).2]
      · rw [find?_prepend_of_not_mem hm] at hT
        have hT1 : (X₁.find? T).isSome = true := by simpa [fe] using hT
        have := hx.table T hT1
        unfold Env.findTable? at this
        obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hT1
        rw [if_pos hT1, if_pos (by rw [hx.find T ci hci]; rfl)] at this
        exact this
  · obtain ⟨hwf, hnat, hrc0, htc0, hbool⟩ := hx.facts
    have nR : ∀ m, (∀ c ∈ R, c.name ≠ m) → m ∉ R.map (·.name) := by
      intro m h hm; obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hm; exact h c hc rfl
    have keep : ∀ m, m ∉ R.map (·.name) →
        Env.find? ⟨R ++ X₁.consts, Qr ++ X₁.tables⟩ m = X₁.find? m := fun m hm => by
      rw [find?_prepend_of_not_mem hm]; rfl
    refine ⟨hwE, ?_, ?_, ?_, ?_⟩
    · have n1 := nR natName (fun c hc => (hfr c hc).1.2.2.1)
      have n2 := nR natZeroName (fun c hc => (hfr c hc).1.2.2.2.1)
      have n3 := nR natSuccName (fun c hc => (hfr c hc).1.2.2.2.2.1)
      rw [keep _ n1, keep _ n2, keep _ n3]; exact hnat
    · intro n cv mI rP isK rules hn r hr
      rcases find?_prepend_mem hn with ⟨hm, -⟩ | ⟨hnn, h1⟩
      · exact hrc _ hm cv mI rP isK rules rfl r hr
      · obtain ⟨cvj, cnP, cnF, T, hj⟩ := hrc0 n cv mI rP isK rules (by simpa [fe] using h1) r hr
        exact ⟨cvj, cnP, cnF, T, by rw [keep _ (nm _ ⟨_, hj⟩)]; exact hj⟩
    · intro T tbl hT
      unfold Env.findTable? at hT
      split at hT
      · simp only [List.find?_append] at hT
        cases hq : Qr.find? (·.structName == T) with
        | some t =>
          rw [hq] at hT; simp only [Option.some_or, Option.some.injEq] at hT; subst hT
          exact htc _ (List.mem_of_find?_eq_some hq)
        | none =>
          rw [hq] at hT; simp only [Option.none_or] at hT
          have hst : tbl.structName = T := by simpa using List.find?_some hT
          have hT1 : (X₁.find? T).isSome = true := by
            have := ht1 tbl (List.mem_of_find?_eq_some hT); rwa [hst] at this
          have : X₁.findTable? T = some tbl := by unfold Env.findTable?; rw [if_pos hT1]; exact hT
          exact find?_prepend_isSome (htc0 T tbl this)
      · cases hT
    · have hop : ∀ m ∈ natOpNames, m ∉ R.map (·.name) := fun m hm => nR m (fun c hc e => by
        have := (hfr c hc).1.1; rw [e] at this; simp [natOpName, hm] at this)
      have n4 := nR boolTrueName (fun c hc => (hfr c hc).1.2.2.2.2.2.1)
      have n5 := nR boolFalseName (fun c hc => (hfr c hc).1.2.2.2.2.2.2)
      rw [keep _ (hop _ (by simp [natOpNames])), keep _ (hop _ (by simp [natOpNames])), keep _ n4, keep _ n5]
      exact hbool

/-- Pushing constants keeps `TablesStored`. -/
theorem tablesStored_prepend {X : Env} (R : List ConstantInfo) (Qr : List ProjTable) (ht : TablesStored X)
    (hQ : ∀ t ∈ Qr, t.structName ∈ R.map (·.name)) : TablesStored ⟨R ++ X.consts, Qr ++ X.tables⟩ := by
  intro t htm
  rcases List.mem_append.mp htm with h | h
  · exact find?_mem_name (hQ t h)
  · exact find?_prepend_isSome (ht t h)

end ConPanqueque.Pipeline.IndExt
