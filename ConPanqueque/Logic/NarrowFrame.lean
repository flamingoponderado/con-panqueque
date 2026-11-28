import ConPanqueque.Logic.NarrowDefs

/-! # Narrowing: frame lemmas

Two facts about running a program whose behaviour does not depend on the old value of a local `x`:

* `fl`: if `dk x p ≠ .dep`, two runs of `p` from states that differ only at the local `x` give
  the same result, and final states that differ at most at `x` (only in their locals, if the result
  is not `none`/`break`/`continue`); after a `kill` the final states are equal.
* `kp`: a run that completes normally keeps a word-shaped `x` word-shaped, and leaves `x`
  unchanged if `occ x p = false`. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString

namespace ConPanqueque.Logic

section
variable {σ : Type}

/-- Results after which the enclosing statement goes on with the locals. -/
def Normalish : Option (PanSemResultExact 64) → Prop
  | none => True
  | some .break => True
  | some .continue => True
  | _ => False

/-! ## Expressions do not see locals they do not mention -/

theorem evalE_eq {t1 t2 : PanSemStateExact 64 σ} (h : t1 = t2) (i1 : DecidablePred t1.memaddrs)
    (i2 : DecidablePred t2.memaddrs) (e : ExpHOL 64) :
    @evalHOLExact 64 σ _ t1 i1 e = @evalHOLExact 64 σ _ t2 i2 e := by
  subst h; cases Subsingleton.elim i1 i2; rfl

theorem evalLE_eq {t1 t2 : PanSemStateExact 64 σ} (h : t1 = t2) (i1 : DecidablePred t1.memaddrs)
    (i2 : DecidablePred t2.memaddrs) (es : List (ExpHOL 64)) :
    @evalListHOLExact 64 σ _ t1 i1 es = @evalListHOLExact 64 σ _ t2 i2 es := by
  subst h; cases Subsingleton.elim i1 i2; rfl

section
variable (s : PanSemStateFiniteExact 64 σ) (L : HolFiniteMapExact MlS (ValueHOL 64)) (x : MlS)
  (hL : ∀ y, y ≠ x → L.lookup y = s.locals.lookup y)
include hL

mutual
theorem eval_offx : ∀ (e : ExpHOL 64), ev x e = false →
    @evalHOLExact 64 σ _ ({ s with locals := L } : PanSemStateFiniteExact 64 σ).toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) e =
    @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e
  | .const _, _ => by simp only [evalHOLExact]
  | .var .local y, h => by
    simp only [evalHOLExact, PanSemStateFiniteExact.toExact]
    exact hL y (by simpa [ev] using h)
  | .var .global _, _ => by simp only [evalHOLExact, PanSemStateFiniteExact.toExact]
  | .load _ a, h => by
    simp only [evalHOLExact]; rw [eval_offx a (by simpa [ev] using h)]
  | .load32 a, h => by
    simp only [evalHOLExact]; rw [eval_offx a (by simpa [ev] using h)]
  | .loadByte a, h => by
    simp only [evalHOLExact]; rw [eval_offx a (by simpa [ev] using h)]
  | .op _ args, h => by
    simp only [evalHOLExact]; rw [evalList_offx args (by simpa [ev] using h)]
  | .panop _ args, h => by
    simp only [evalHOLExact]; rw [evalList_offx args (by simpa [ev] using h)]
  | .cmp _ a b, h => by
    simp only [ev, Bool.or_eq_false_iff] at h
    simp only [evalHOLExact]; rw [eval_offx a h.1, eval_offx b h.2]
  | .shift _ a b, h => by
    simp only [ev, Bool.or_eq_false_iff] at h
    simp only [evalHOLExact]; rw [eval_offx a h.1, eval_offx b h.2]
  | .baseAddr, _ => by simp only [evalHOLExact]
  | .topAddr, _ => by simp only [evalHOLExact]
  | .bytesInWord, _ => by simp only [evalHOLExact]
  | .rstruct _, h => by simp [ev] at h
  | .rfield _ _, h => by simp [ev] at h
  | .nstruct _ _, h => by simp [ev] at h
  | .nfield _ _, h => by simp [ev] at h

theorem evalList_offx : ∀ (es : List (ExpHOL 64)), evs x es = false →
    @evalListHOLExact 64 σ _ ({ s with locals := L } : PanSemStateFiniteExact 64 σ).toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) es =
    @evalListHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) es
  | [], _ => by simp only [evalListHOLExact]
  | e :: es, h => by
    simp only [evs, Bool.or_eq_false_iff] at h
    simp only [evalListHOLExact]
    rw [eval_offx e h.1, evalList_offx es h.2]
end
end

/-! ## Related states -/

/-- Same shape (or both absent). -/
def SameSh : Option (ValueHOL 64) → Option (ValueHOL 64) → Prop
  | some a, some b => shapeOfHOLExact a = shapeOfHOLExact b
  | none, none => True
  | _, _ => False

theorem sameSh_refl : ∀ o : Option (ValueHOL 64), SameSh o o
  | some _ => rfl
  | none => trivial

/-- Two states equal apart from the local `x`. -/
structure XR (x : MlS) (s1 s2 : PanSemStateFiniteExact 64 σ) : Prop where
  oth : s2 = { s1 with locals := s2.locals }
  off : ∀ y, y ≠ x → s2.locals.lookup y = s1.locals.lookup y

theorem xr_refl (x : MlS) (s : PanSemStateFiniteExact 64 σ) : XR x s s := ⟨rfl, fun _ _ => rfl⟩

/-- What two runs of a program from `XR`-related states give. -/
def FPost (x : MlS) (d : DK) (s1 s2 : PanSemStateFiniteExact 64 σ)
    (A B : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ) : Prop :=
  B.1 = A.1 ∧ B.2 = { A.2 with locals := B.2.locals } ∧
    (Normalish A.1 → XR x A.2 B.2 ∧
      (SameSh (s1.locals.lookup x) (s2.locals.lookup x) → SameSh (A.2.locals.lookup x) (B.2.locals.lookup x))) ∧
    (A.1 = none → d = .kill → B.2 = A.2)

theorem isValid_xr {x : MlS} {s1 s2 : PanSemStateFiniteExact 64 σ} (h : XR x s1 s2)
    (hS : SameSh (s1.locals.lookup x) (s2.locals.lookup x)) (k : VarKind) (y : MlS) (v : ValueHOL 64) :
    isValidValueHOLExact s2.toExact k y v = isValidValueHOLExact s1.toExact k y v := by
  rw [h.oth]
  cases k
  · simp only [isValidValueHOLExact, lookupKvarHOLExact, PanSemStateFiniteExact.toExact]
    by_cases hy : y = x
    · subst hy
      revert hS
      cases s1.locals.lookup y <;> cases s2.locals.lookup y <;> simp [SameSh]
      intro e; rw [e]
    · rw [h.off y hy]
  · rfl

theorem isValid_xr_ne {x : MlS} {s1 s2 : PanSemStateFiniteExact 64 σ} (h : XR x s1 s2) (k : VarKind) (y : MlS)
    (hy : ¬ (k = .local ∧ y = x)) (v : ValueHOL 64) :
    isValidValueHOLExact s2.toExact k y v = isValidValueHOLExact s1.toExact k y v := by
  rw [h.oth]
  cases k
  · simp only [isValidValueHOLExact, lookupKvarHOLExact, PanSemStateFiniteExact.toExact]
    rw [h.off y (fun e => hy ⟨rfl, e⟩)]
  · rfl


/-! ## Closing lemmas for `FPost` -/

theorem fpost_same {x : MlS} {d : DK} {s1 s2 : PanSemStateFiniteExact 64 σ}
    (A : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ) : FPost x d s1 s2 A A :=
  ⟨rfl, by cases A.2; rfl, fun _ => ⟨xr_refl x _, fun _ => sameSh_refl _⟩, fun _ _ => rfl⟩

/-- Same run apart from the locals, which the program left alone. -/
theorem fpost_L {x : MlS} {d : DK} {s : PanSemStateFiniteExact 64 σ} {L : HolFiniteMapExact MlS (ValueHOL 64)}
    (hL : ∀ y, y ≠ x → L.lookup y = s.locals.lookup y) (r : Option (PanSemResultExact 64))
    (t : PanSemStateFiniteExact 64 σ) (ht : t.locals = s.locals) (hk : r = none → d ≠ .kill) :
    FPost x d s { s with locals := L } (r, t) (r, { t with locals := L }) := by
  refine ⟨rfl, rfl, fun _ => ⟨⟨rfl, fun y hy => by rw [ht]; exact hL y hy⟩, fun h => by rw [ht]; exact h⟩,
    fun h1 h2 => absurd h2 (hk h1)⟩

theorem fpost_weak {x : MlS} {d d' : DK} {s1 s2 : PanSemStateFiniteExact 64 σ}
    {A B : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ}
    (h : FPost x d s1 s2 A B) (hd : d' = .kill → d = .kill) : FPost x d' s1 s2 A B :=
  ⟨h.1, h.2.1, h.2.2.1, fun h1 h2 => h.2.2.2 h1 (hd h2)⟩

theorem xr_L {x : MlS} {u1 u2 : PanSemStateFiniteExact 64 σ} (h : XR x u1 u2) :
    u2 = { u1 with locals := u2.locals } ∧ ∀ y, y ≠ x → u2.locals.lookup y = u1.locals.lookup y := ⟨h.oth, h.off⟩

theorem upd_eq_of_off {x : MlS} {L M : HolFiniteMapExact MlS (ValueHOL 64)}
    (hL : ∀ y, y ≠ x → L.lookup y = M.lookup y) (v : ValueHOL 64) : L.update (x, v) = M.update (x, v) := by
  apply HolFiniteMapExact.ext; funext y
  simp only [HolFiniteMapExact.lookup_update, FUPDATE]
  by_cases hy : y = x
  · subst hy; simp
  · have : (x == y) = false := by simp [Ne.symm hy]
    simp only [this, Bool.false_eq_true, ite_false]; exact hL y hy

theorem upd_off {x y : MlS} {L M : HolFiniteMapExact MlS (ValueHOL 64)}
    (hL : ∀ z, z ≠ x → L.lookup z = M.lookup z) (v : ValueHOL 64) :
    ∀ z, z ≠ x → (L.update (y, v)).lookup z = (M.update (y, v)).lookup z := by
  intro z hz
  simp only [HolFiniteMapExact.lookup_update, FUPDATE]
  split
  · rfl
  · exact hL z hz

theorem upd_at {x y : MlS} (hy : y ≠ x) (L : HolFiniteMapExact MlS (ValueHOL 64)) (v : ValueHOL 64) :
    (L.update (y, v)).lookup x = L.lookup x := by
  simp only [HolFiniteMapExact.lookup_update, FUPDATE]
  have : (y == x) = false := by simp [hy]
  simp [this]

theorem shape_val (w : HolWordLab 64) : shapeOfHOLExact (ValueHOL.val w) = .one := by
  rw [shapeOfHOLExact]

theorem upd_self (L : HolFiniteMapExact MlS (ValueHOL 64)) (y : MlS) (v : ValueHOL 64) :
    (L.update (y, v)).lookup y = some v := by
  simp [FUPDATE]

theorem resVar_off {x : MlS} {L M : HolFiniteMapExact MlS (ValueHOL 64)}
    (hL : ∀ z, z ≠ x → L.lookup z = M.lookup z) (y : MlS) (o : Option (ValueHOL 64)) :
    ∀ z, z ≠ x → (HolFiniteMapExact.resVarEq L (y, o)).lookup z = (HolFiniteMapExact.resVarEq M (y, o)).lookup z := by
  intro z hz
  cases o <;> simp only [HolFiniteMapExact.resVarEq, HolFiniteMapExact.lookup_eraseEq,
    HolFiniteMapExact.lookup_updateEq, FDOMSUB_HOL, FUPDATE_HOL] <;> split <;> first | rfl | exact hL z hz

theorem resVar_at {x y : MlS} (hy : y ≠ x) (L : HolFiniteMapExact MlS (ValueHOL 64)) (o : Option (ValueHOL 64)) :
    (HolFiniteMapExact.resVarEq L (y, o)).lookup x = L.lookup x := by
  cases o <;> simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.lookup_eraseEq,
    HolFiniteMapExact.lookup_updateEq, FDOMSUB_HOL, FUPDATE_HOL, Ne.symm hy]

theorem resVar_self (x : MlS) (L : HolFiniteMapExact MlS (ValueHOL 64)) (o : Option (ValueHOL 64)) :
    (HolFiniteMapExact.resVarEq L (x, o)).lookup x = o := by
  cases o <;> simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.lookup_eraseEq,
    HolFiniteMapExact.lookup_updateEq, FDOMSUB_HOL, FUPDATE_HOL]

theorem resVar_eq_of_off {x : MlS} {L M : HolFiniteMapExact MlS (ValueHOL 64)}
    (hL : ∀ z, z ≠ x → L.lookup z = M.lookup z) (o : Option (ValueHOL 64)) :
    HolFiniteMapExact.resVarEq L (x, o) = HolFiniteMapExact.resVarEq M (x, o) := by
  apply HolFiniteMapExact.ext; funext z
  by_cases hz : z = x
  · subst hz; rw [resVar_self, resVar_self]
  · exact resVar_off hL x o z hz

theorem ofExact_mf (t : PanSemStateFiniteExact 64 σ) (m : RiscV.Word 64 → HolWordLab 64) (f : HolFfiState σ) (h) :
    PanSemStateFiniteExact.ofExact { t.toExact with memory := m, ffi := f } h = { t with memory := m, ffi := f } := by
  cases t
  simp only [PanSemStateFiniteExact.ofExact, PanSemStateFiniteExact.toExact]


theorem fpost_re {x : MlS} {d : DK} {s1 s2 u1 u2 : PanSemStateFiniteExact 64 σ}
    {A B : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ}
    (h : FPost x d u1 u2 A B)
    (hs : SameSh (s1.locals.lookup x) (s2.locals.lookup x) → SameSh (u1.locals.lookup x) (u2.locals.lookup x)) :
    FPost x d s1 s2 A B :=
  ⟨h.1, h.2.1, fun hn => ⟨(h.2.2.1 hn).1, fun h0 => (h.2.2.1 hn).2 (hs h0)⟩, h.2.2.2⟩

/-! ## The frame lemma -/

/-- `p` run from `s` and from `s` with other values for the local `x`. -/
def FLN (x : MlS) (n : Nat) (p : ProgHOL 64) : Prop :=
  ∀ (s : PanSemStateFiniteExact 64 σ) (L : HolFiniteMapExact MlS (ValueHOL 64)), s.clock ≤ n →
    (∀ y, y ≠ x → L.lookup y = s.locals.lookup y) →
    (SameSh (s.locals.lookup x) (L.lookup x) ∨ occ x p = false) →
    FPost x (dk x p) s { s with locals := L } (evaluateHOLFiniteState s p)
      (evaluateHOLFiniteState { s with locals := L } p)

theorem occ_sameSh {x : MlS} {p : ProgHOL 64} {o1 o2 : Option (ValueHOL 64)} (h : SameSh o1 o2 ∨ occ x p = false)
    (ho : occ x p = true) : SameSh o1 o2 := by
  rcases h with h | h
  · exact h
  · rw [ho] at h; cases h

theorem fl_step (x : MlS) (n : Nat) (ih : ∀ m, m < n → ∀ p, dk x p ≠ .dep → FLN (σ := σ) x m p) :
    ∀ p, dk x p ≠ .dep → FLN (σ := σ) x n p
  | .skip, _ => by
    intro s L _ hL _
    rw [evaluateHOLFiniteState_eq_evaluate_def s .skip,
      evaluateHOLFiniteState_eq_evaluate_def { s with locals := L } .skip]
    exact fpost_L hL none s rfl (by simp [dk])
  | .break, _ => by
    intro s L _ hL _
    rw [evaluateHOLFiniteState_eq_evaluate_def s .break,
      evaluateHOLFiniteState_eq_evaluate_def { s with locals := L } .break]
    exact fpost_L hL _ s rfl (by simp)
  | .continue, _ => by
    intro s L _ hL _
    rw [evaluateHOLFiniteState_eq_evaluate_def s .continue,
      evaluateHOLFiniteState_eq_evaluate_def { s with locals := L } .continue]
    exact fpost_L hL _ s rfl (by simp)
  | .tick, _ => by
    intro s L _ hL _
    rw [evaluateHOLFiniteState_eq_evaluate_def s .tick,
      evaluateHOLFiniteState_eq_evaluate_def { s with locals := L } .tick]
    dsimp only
    by_cases hk : s.clock = 0
    · rw [if_pos hk, if_pos (show ({ s with locals := L } : PanSemStateFiniteExact 64 σ).clock = 0 from hk)]
      exact fpost_same _
    · rw [if_neg hk, if_neg (show ¬ ({ s with locals := L } : PanSemStateFiniteExact 64 σ).clock = 0 from hk)]
      exact fpost_L hL none (decClockHOLFinite s) rfl (by simp [dk])
  | .assign k y e, hd => by
    intro s L _ hL hS
    have he : ev x e = false := by
      cases h : ev x e
      · rfl
      · simp [dk, h] at hd
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.assign k y e),
      evaluateHOLFiniteState_eq_evaluate_def { s with locals := L } (.assign k y e)]
    dsimp only
    rw [eval_offx s L x hL e he]
    cases hv : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with
    | none => exact fpost_L hL _ s rfl (by simp)
    | some v =>
      dsimp only
      simp only [isValidValueHOLFinite_eq]
      by_cases hk : k = .local ∧ y = x
      · obtain ⟨rfl, rfl⟩ := hk
        have hS' := occ_sameSh hS (by simp [occ])
        have hdk : dk y (.assign .local y e) = .kill := by simp [dk, he]
        rw [hdk]
        have hv' : isValidValueHOLExact ({ s with locals := L } : PanSemStateFiniteExact 64 σ).toExact .local y v =
            isValidValueHOLExact s.toExact .local y v :=
          isValid_xr ⟨rfl, hL⟩ hS' .local y v
        rw [hv']
        split
        · simp only [setKvarHOLFinite, setVarHOLFinite]
          rw [upd_eq_of_off hL v]
          exact fpost_same _
        · exact fpost_L hL _ s rfl (by simp)
      · have hv' := isValid_xr_ne (s1 := s) (s2 := { s with locals := L }) ⟨rfl, hL⟩ k y hk v
        rw [hv']
        have hdk : dk x (.assign k y e) = .pass := by simp [dk, he, hk]
        rw [hdk]
        split
        · cases k
          · have hy : y ≠ x := fun h => hk ⟨rfl, h⟩
            simp only [setKvarHOLFinite, setVarHOLFinite]
            refine ⟨rfl, rfl, fun _ => ⟨⟨rfl, upd_off hL v⟩, fun h0 => ?_⟩, fun _ h => by cases h⟩
            simp only [upd_at hy]; exact h0
          · exact fpost_L hL none _ rfl (by simp)
        · exact fpost_L hL _ s rfl (by simp)
  | .store a v, hd => by
    intro s L _ hL _
    have he : ev x a = false ∧ ev x v = false := by
      cases h1 : ev x a <;> cases h2 : ev x v <;> simp_all [dk]
    have hdk : dk x (.store a v) = .pass := by simp [dk, he]
    rw [hdk, evaluateHOLFiniteState_eq_evaluate_def s (.store a v),
      evaluateHOLFiniteState_eq_evaluate_def { s with locals := L } (.store a v)]
    dsimp only
    rw [eval_offx s L x hL a he.1, eval_offx s L x hL v he.2]
    repeat' split
    all_goals (try simp_all only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq, reduceCtorEq,
      HolFfiResult.final.injEq, HolFfiResult.ret.injEq, forall_eq', forall_eq, imp_false, not_true_eq_false,
      false_implies, implies_true, and_imp, forall_apply_eq_imp_iff, forall_apply_eq_imp_iff₂])
    all_goals (try subst_vars)
    all_goals (try (exfalso; simp_all; done))
    all_goals first
      | exact fpost_L hL _ s rfl (by simp)
      | exact fpost_L hL none _ rfl (by simp)
  | .store32 a v, hd => by
    intro s L _ hL _
    have he : ev x a = false ∧ ev x v = false := by
      cases h1 : ev x a <;> cases h2 : ev x v <;> simp_all [dk]
    have hdk : dk x (.store32 a v) = .pass := by simp [dk, he]
    rw [hdk, evaluateHOLFiniteState_eq_evaluate_def s (.store32 a v),
      evaluateHOLFiniteState_eq_evaluate_def { s with locals := L } (.store32 a v)]
    dsimp only
    rw [eval_offx s L x hL a he.1, eval_offx s L x hL v he.2]
    repeat' split
    all_goals (try simp_all only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq, reduceCtorEq,
      HolFfiResult.final.injEq, HolFfiResult.ret.injEq, forall_eq', forall_eq, imp_false, not_true_eq_false,
      false_implies, implies_true, and_imp, forall_apply_eq_imp_iff, forall_apply_eq_imp_iff₂])
    all_goals (try subst_vars)
    all_goals (try (exfalso; simp_all; done))
    all_goals first
      | exact fpost_L hL _ s rfl (by simp)
      | exact fpost_L hL none _ rfl (by simp)
  | .storeByte a v, hd => by
    intro s L _ hL _
    have he : ev x a = false ∧ ev x v = false := by
      cases h1 : ev x a <;> cases h2 : ev x v <;> simp_all [dk]
    have hdk : dk x (.storeByte a v) = .pass := by simp [dk, he]
    rw [hdk, evaluateHOLFiniteState_eq_evaluate_def s (.storeByte a v),
      evaluateHOLFiniteState_eq_evaluate_def { s with locals := L } (.storeByte a v)]
    dsimp only
    rw [eval_offx s L x hL a he.1, eval_offx s L x hL v he.2]
    repeat' split
    all_goals (try simp_all only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq, reduceCtorEq,
      HolFfiResult.final.injEq, HolFfiResult.ret.injEq, forall_eq', forall_eq, imp_false, not_true_eq_false,
      false_implies, implies_true, and_imp, forall_apply_eq_imp_iff, forall_apply_eq_imp_iff₂])
    all_goals (try subst_vars)
    all_goals (try (exfalso; simp_all; done))
    all_goals first
      | exact fpost_L hL _ s rfl (by simp)
      | exact fpost_L hL none _ rfl (by simp)
  | .return e, hd => by
    intro s L _ hL _
    have he : ev x e = false := by
      cases h : ev x e
      · rfl
      · simp [dk, h] at hd
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.return e),
      evaluateHOLFiniteState_eq_evaluate_def { s with locals := L } (.return e)]
    dsimp only
    rw [eval_offx s L x hL e he]
    have hdk : dk x (.return e) = .pass := by simp [dk, he]
    rw [hdk]
    repeat' split
    all_goals (try simp_all only [Option.some.injEq, ValueHOL.val.injEq, HolWordLab.word.injEq, reduceCtorEq,
      HolFfiResult.final.injEq, HolFfiResult.ret.injEq, forall_eq', forall_eq, imp_false, not_true_eq_false,
      false_implies, implies_true, and_imp, forall_apply_eq_imp_iff, forall_apply_eq_imp_iff₂])
    all_goals (try subst_vars)
    all_goals (try (exfalso; simp_all; done))
    all_goals first
      | exact fpost_L hL _ s rfl (by simp)
      | exact fpost_same _
  | .extCall g a b c d, hd => by
    intro s L _ hL _
    have he : ev x a = false ∧ ev x b = false ∧ ev x c = false ∧ ev x d = false := by
      cases h1 : ev x a <;> cases h2 : ev x b <;> cases h3 : ev x c <;> cases h4 : ev x d <;> simp_all [dk]
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.extCall g a b c d),
      evaluateHOLFiniteState_eq_evaluate_def { s with locals := L } (.extCall g a b c d)]
    dsimp only
    simp only [evalHOLFinite]
    rw [eval_offx s L x hL a he.1, eval_offx s L x hL b he.2.1, eval_offx s L x hL c he.2.2.1,
      eval_offx s L x hL d he.2.2.2]
    have hdk : dk x (.extCall g a b c d) = .pass := by simp [dk, he]
    rw [hdk]
    rcases ha : (@evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) a) with
      _ | ⟨⟨⟨a1⟩⟩ | _ | ⟨_, _⟩⟩ <;> (try simp only [ha]) <;> (try exact fpost_L hL _ s rfl (by simp))
    rcases hb : (@evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) b) with
      _ | ⟨⟨⟨l1⟩⟩ | _ | ⟨_, _⟩⟩ <;> (try simp only [hb]) <;> (try exact fpost_L hL _ s rfl (by simp))
    rcases hc : (@evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) c) with
      _ | ⟨⟨⟨a2⟩⟩ | _ | ⟨_, _⟩⟩ <;> (try simp only [hc]) <;> (try exact fpost_L hL _ s rfl (by simp))
    rcases hd : (@evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) d) with
      _ | ⟨⟨⟨l2⟩⟩ | _ | ⟨_, _⟩⟩ <;> (try simp only [hd]) <;> (try exact fpost_L hL _ s rfl (by simp))
    try dsimp only
    rcases h5 : readBytearrayWordHOL (byteWidth := 8) a1 l1.toNat
        (@panMemLoadByteWord8HOL 64 _ s.memory s.memaddrs (fun a => Classical.propDecidable (s.memaddrs a)) s.be) with
      _ | bytes1 <;> (try simp only [h5]) <;> (try exact fpost_L hL _ s rfl (by simp))
    rcases h6 : readBytearrayWordHOL (byteWidth := 8) a2 l2.toNat
        (@panMemLoadByteWord8HOL 64 _ s.memory s.memaddrs (fun a => Classical.propDecidable (s.memaddrs a)) s.be) with
      _ | bytes2 <;> (try simp only [h6]) <;> (try exact fpost_L hL _ s rfl (by simp))
    rcases h7 : callFFIHOL s.ffi (.extCall g) bytes1 bytes2 with ⟨nf, nb⟩ | ev <;> (try simp only [h7])
    · exact fpost_L hL none _ rfl (by simp)
    · exact fpost_same _
  | .seq a b, hd => by
    intro s L hn hL hS
    have hda : dk x a ≠ .dep := by
      intro h; apply hd; simp [dk, h, DK.seq]
    have hSa : SameSh (s.locals.lookup x) (L.lookup x) ∨ occ x a = false := by
      rcases hS with h | h
      · exact Or.inl h
      · simp only [occ, Bool.or_eq_false_iff] at h; exact Or.inr h.1
    have ha := fl_step x n ih a hda s L hn hL hSa
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.seq a b),
      evaluateHOLFiniteState_eq_evaluate_def { s with locals := L } (.seq a b)]
    dsimp only
    generalize hA : evaluateHOLFiniteState s a = A at ha ⊢
    generalize hB : evaluateHOLFiniteState { s with locals := L } a = B at ha ⊢
    obtain ⟨r, u1⟩ := A
    obtain ⟨r2, u2⟩ := B
    obtain ⟨h1, h2, h3, h4⟩ := ha
    simp only at h1 h2 h3 h4
    subst h1
    cases r2 with
    | none =>
      simp only
      obtain ⟨hx, hsh⟩ := h3 trivial
      cases hk : dk x a with
      | kill =>
        have e2 := h4 rfl hk
        subst e2
        have : dk x (.seq a b) = .kill := by simp [dk, hk, DK.seq]
        rw [this]
        exact fpost_same _
      | pass =>
        have hdb : dk x (.seq a b) = dk x b := by simp [dk, hk, DK.seq]
        rw [hdb]
        obtain ⟨L2, rfl⟩ : ∃ L2, u2 = { u1 with locals := L2 } := ⟨_, hx.oth⟩
        have hcl : u1.clock ≤ n := Nat.le_trans (clock_of hA) hn
        have hSb : SameSh (u1.locals.lookup x) (L2.lookup x) ∨ occ x b = false := by
          rcases hS with h | h
          · exact Or.inl (hsh h)
          · simp only [occ, Bool.or_eq_false_iff] at h; exact Or.inr h.2
        exact fpost_re (fl_step x n ih b (by rw [← hdb]; exact hd) u1 L2 hcl hx.off hSb) hsh
      | dep => exact absurd hk hda
    | some r =>
      simp only
      exact ⟨rfl, h2, h3, fun h => by cases h⟩
  | .ite c a b, hd => by
    intro s L hn hL hS
    have hc : ev x c = false := by
      cases h : ev x c
      · rfl
      · simp [dk, h] at hd
    have hm : dk x (.ite c a b) = (dk x a).meet (dk x b) := by simp [dk, hc]
    have hda : dk x a ≠ .dep := by
      intro h; apply hd; rw [hm, h]; cases dk x b <;> rfl
    have hdb : dk x b ≠ .dep := by
      intro h; apply hd; rw [hm, h]; cases dk x a <;> rfl
    have hoc : occ x (.ite c a b) = false → occ x a = false ∧ occ x b = false := by
      intro h; simp only [occ, Bool.or_eq_false_iff] at h; exact ⟨h.1.2, h.2⟩
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.ite c a b),
      evaluateHOLFiniteState_eq_evaluate_def { s with locals := L } (.ite c a b)]
    dsimp only
    rw [eval_offx s L x hL c hc]
    rcases hcv : (@evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) c) with
      _ | ⟨⟨⟨w⟩⟩ | _ | ⟨_, _⟩⟩ <;> (try simp only [hcv]) <;> (try exact fpost_L hL _ s rfl (by simp))
    · by_cases hw : w = 0
      · simp only [hw, ite_true]
        refine fpost_weak (fl_step x n ih b hdb s L hn hL ?_) ?_
        · rcases hS with h | h
          · exact Or.inl h
          · exact Or.inr (hoc h).2
        · intro h; rw [hm] at h; revert h; cases dk x a <;> cases dk x b <;> simp [DK.meet]
      · simp only [hw, ite_false]
        refine fpost_weak (fl_step x n ih a hda s L hn hL ?_) ?_
        · rcases hS with h | h
          · exact Or.inl h
          · exact Or.inr (hoc h).1
        · intro h; rw [hm] at h; revert h; cases dk x a <;> cases dk x b <;> simp [DK.meet]
  | .dec y sh e b, hd => by
    intro s L hn hL hS
    have he : ev x e = false := by
      cases h : ev x e
      · rfl
      · simp [dk, h] at hd
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.dec y sh e b),
      evaluateHOLFiniteState_eq_evaluate_def { s with locals := L } (.dec y sh e b)]
    dsimp only
    rw [eval_offx s L x hL e he]
    cases hv : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with
    | none => exact fpost_L hL _ s rfl (by simp)
    | some v =>
      dsimp only
      split
      · by_cases hy : y = x
        · subst hy
          have hS' := occ_sameSh hS (by simp [occ])
          have hdk : dk y (.dec y sh e b) = .pass := by simp [dk, he]
          rw [hdk]
          simp only [setVarHOLFinite]
          rw [upd_eq_of_off hL v]
          generalize evaluateHOLFiniteState { s with locals := s.locals.update (y, v) } b = W
          obtain ⟨r, w⟩ := W
          refine ⟨rfl, rfl, fun _ => ⟨⟨rfl, ?_⟩, fun _ => ?_⟩, fun _ h => by cases h⟩
          · intro z hz
            show (HolFiniteMapExact.resVarEq w.locals (y, L.lookup y)).lookup z =
              (HolFiniteMapExact.resVarEq w.locals (y, s.locals.lookup y)).lookup z
            rw [resVar_at (Ne.symm hz), resVar_at (Ne.symm hz)]
          · show SameSh ((HolFiniteMapExact.resVarEq w.locals (y, s.locals.lookup y)).lookup y)
              ((HolFiniteMapExact.resVarEq w.locals (y, L.lookup y)).lookup y)
            rw [resVar_self, resVar_self]; exact hS'
        · have hdk : dk x (.dec y sh e b) = dk x b := by simp [dk, he, hy]
          rw [hdk]
          have hdb : dk x b ≠ .dep := by rw [← hdk]; exact hd
          have hSb : SameSh ((setVarHOLFinite y v s).locals.lookup x) ((L.update (y, v)).lookup x) ∨
              occ x b = false := by
            simp only [setVarHOLFinite, upd_at hy]
            rcases hS with h | h
            · exact Or.inl h
            · simp only [occ, Bool.or_eq_false_iff] at h; exact Or.inr h.2
          have hb := fl_step x n ih b hdb (setVarHOLFinite y v s) (L.update (y, v)) hn
            (fun z hz => upd_off hL v z hz) hSb
          have hLy : L.lookup y = s.locals.lookup y := hL y hy
          simp only [setVarHOLFinite] at hb ⊢
          rw [hLy]
          generalize evaluateHOLFiniteState { s with locals := s.locals.update (y, v) } b = W1 at hb ⊢
          generalize evaluateHOLFiniteState { s with locals := L.update (y, v) } b = W2 at hb ⊢
          obtain ⟨r1, w1⟩ := W1
          obtain ⟨r2, w2⟩ := W2
          obtain ⟨h1, h2, h3, h4⟩ := hb
          simp only at h1 h2 h3 h4
          subst h1
          refine ⟨rfl, ?_, fun hn' => ⟨⟨?_, ?_⟩, fun h0 => ?_⟩, fun h5 h6 => ?_⟩
          · simp only; rw [h2]
          · simp only; rw [h2]
          · exact resVar_off (h3 hn').1.off _ _
          · simp only [resVar_at hy]
            exact (h3 hn').2 (by simp only [upd_at hy]; exact h0)
          · simp only; rw [h4 h5 h6]
      · exact fpost_L hL _ s rfl (by simp)
  | .while c b, hd => by
    intro s L hn hL hS
    have hc : ev x c = false := by
      cases h : ev x c
      · rfl
      · simp [dk, h] at hd
    have hdb : dk x b ≠ .dep := by
      intro h; apply hd; simp [dk, hc, h]
    have hdw : dk x (.while c b) = .pass := by simp [dk, hc, hdb]
    rw [hdw]
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.while c b),
      evaluateHOLFiniteState_eq_evaluate_def { s with locals := L } (.while c b)]
    dsimp only
    simp only [evalHOLFinite]
    rw [eval_offx s L x hL c hc]
    rcases hcv : (@evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) c) with
      _ | ⟨⟨⟨w⟩⟩ | _ | ⟨_, _⟩⟩ <;> (try simp only [hcv]) <;> (try exact fpost_L hL _ s rfl (by simp))
    by_cases hw : w ≠ 0
    · rw [ite_eq_left hw, ite_eq_left hw]
      by_cases hk : s.clock = 0
      · rw [if_pos hk, if_pos (show ({ s with locals := L } : PanSemStateFiniteExact 64 σ).clock = 0 from hk)]
        exact fpost_same _
      rw [if_neg hk, if_neg (show ¬ ({ s with locals := L } : PanSemStateFiniteExact 64 σ).clock = 0 from hk)]
      have hSb : SameSh ((decClockHOLFinite s).locals.lookup x) (L.lookup x) ∨ occ x b = false := by
        rcases hS with h | h
        · exact Or.inl h
        · simp only [occ, Bool.or_eq_false_iff] at h; exact Or.inr h.2
      have hb := fl_step x n ih b hdb (decClockHOLFinite s) L (by simp [decClockHOLFinite]; omega) hL hSb
      rw [show decClockHOLFinite { s with locals := L } = { decClockHOLFinite s with locals := L } from rfl]
      generalize hW : evaluateHOLFiniteState (decClockHOLFinite s) b = W1 at hb ⊢
      generalize evaluateHOLFiniteState { decClockHOLFinite s with locals := L } b = W2 at hb ⊢
      obtain ⟨r1, w1⟩ := W1
      obtain ⟨r2, w2⟩ := W2
      obtain ⟨h1, h2, h3, h4⟩ := hb
      simp only at h1 h2 h3 h4
      subst h1
      have hcw : w1.clock < n := by
        have := clock_of hW; simp [decClockHOLFinite] at this; omega
      have hnext : ∀ (hn' : Normalish r2), FPost x DK.pass s { s with locals := L }
          (evaluateHOLFiniteState w1 (.while c b)) (evaluateHOLFiniteState w2 (.while c b)) := by
        intro hn'
        obtain ⟨hx, hsh⟩ := h3 hn'
        obtain ⟨L2, rfl⟩ : ∃ L2, w2 = { w1 with locals := L2 } := ⟨_, hx.oth⟩
        have := ih w1.clock hcw (.while c b) hd w1 L2 (Nat.le_refl _) hx.off (by
          rcases hS with h | h
          · exact Or.inl (hsh h)
          · exact Or.inr h)
        rw [hdw] at this
        exact fpost_re this hsh
      cases r2 with
      | none => exact hnext trivial
      | some r =>
        cases r with
        | «continue» => exact hnext trivial
        | «break» =>
          obtain ⟨hx, hsh⟩ := h3 trivial
          exact ⟨rfl, h2, fun _ => ⟨hx, hsh⟩, fun _ h => by cases h⟩
        | _ => exact ⟨rfl, h2, fun h => by simp [Normalish] at h, fun h => by simp at h⟩
    · rw [ite_eq_right hw, ite_eq_right hw]
      exact fpost_L hL none s rfl (by simp)
  | .call info f args, hd => by
    intro s L hn hL hS
    have hargs : evs x args = false ∧ (info = none ∨ info = some (none, none) ∨
        ∃ k y, info = some (some (k, y), none)) := by
      rcases info with _ | ⟨_ | ⟨k, y⟩, _ | ⟨eid, hv, h⟩⟩
      · cases h : evs x args
        · exact ⟨rfl, Or.inl rfl⟩
        · simp [dk, h] at hd
      · cases h : evs x args
        · exact ⟨rfl, Or.inr (Or.inl rfl)⟩
        · simp [dk, h] at hd
      · simp [dk] at hd
      · cases h : evs x args
        · exact ⟨rfl, Or.inr (Or.inr ⟨k, y, rfl⟩)⟩
        · simp [dk, h] at hd
      · simp [dk] at hd
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.call info f args),
      evaluateHOLFiniteState_eq_evaluate_def { s with locals := L } (.call info f args)]
    dsimp only
    simp only [evalListHOLFinite]
    rw [evalList_offx s L x hL args hargs.1]
    cases hv : @evalListHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) args with
    | none => exact fpost_L hL _ s rfl (by simp)
    | some vals =>
      dsimp only
      cases hl : lookupCodeHOLFinite s.code.lookup f vals with
      | none => exact fpost_L hL _ s rfl (by simp)
      | some z =>
        obtain ⟨body, callee, rs⟩ := z
        dsimp only
        by_cases hk : s.clock = 0
        · rw [if_pos hk, if_pos (show ({ s with locals := L } : PanSemStateFiniteExact 64 σ).clock = 0 from hk)]
          exact fpost_same _
        rw [if_neg hk, if_neg (show ¬ ({ s with locals := L } : PanSemStateFiniteExact 64 σ).clock = 0 from hk)]
        rw [show callEntryStateHOLFinite { s with locals := L } callee = callEntryStateHOLFinite s callee from rfl]
        generalize evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body = C
        obtain ⟨rc, st⟩ := C
        cases rc with
        | none => exact fpost_same _
        | some r =>
          cases r with
          | returned v =>
            dsimp only
            by_cases hsh : shapeEqHOL (shapeOfHOLExact v) rs = true
            · rw [if_pos hsh, if_pos hsh]
              rcases hargs.2 with rfl | rfl | ⟨k, y, rfl⟩
              · exact fpost_same _
              · exact fpost_L hL none { st with locals := s.locals } rfl (by simp [dk, hargs.1])
              · dsimp only
                by_cases hky : k = .local ∧ y = x
                · obtain ⟨rfl, rfl⟩ := hky
                  have hS' := occ_sameSh hS (by simp [occ])
                  rw [isValid_xr (s1 := s) (s2 := { s with locals := L }) ⟨rfl, hL⟩ hS' .local y]
                  split
                  · simp only [setKvarHOLFinite, setVarHOLFinite]
                    rw [upd_eq_of_off hL]
                    exact fpost_same _
                  · exact fpost_same _
                · rw [isValid_xr_ne (s1 := s) (s2 := { s with locals := L }) ⟨rfl, hL⟩ k y hky]
                  have hdk : dk x (.call (some (some (k, y), none)) f args) = .pass := by simp [dk, hargs.1, hky]
                  rw [hdk]
                  split
                  · cases k
                    · have hy : y ≠ x := fun h => hky ⟨rfl, h⟩
                      simp only [setKvarHOLFinite, setVarHOLFinite]
                      refine ⟨rfl, rfl, fun _ => ⟨⟨rfl, upd_off hL _⟩, fun h0 => ?_⟩, fun _ h => by cases h⟩
                      simp only [upd_at hy]; exact h0
                    · exact fpost_L hL none _ rfl (by simp)
                  · exact fpost_same _
            · rw [if_neg hsh, if_neg hsh]; exact fpost_same _
          | exception eid v =>
            dsimp only
            rcases hargs.2 with rfl | rfl | ⟨k, y, rfl⟩ <;> exact fpost_same _
          | _ => exact fpost_same _
  | .primitive .., hd => by simp [dk] at hd
  | .decCall .., hd => by simp [dk] at hd
  | .raise .., hd => by simp [dk] at hd
  | .shMemLoad .., hd => by simp [dk] at hd
  | .shMemStore .., hd => by simp [dk] at hd
  | .annot .., hd => by simp [dk] at hd

theorem fl (x : MlS) : ∀ n p, dk x p ≠ .dep → FLN (σ := σ) x n p := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihn => exact fl_step x n ihn


/-! ## Single runs: the local `x` keeps its shape, and is left alone by programs that do not touch it -/

def ShOne (o : Option (ValueHOL 64)) : Prop := ∃ v, o = some v ∧ shapeOfHOLExact v = .one

theorem shapeEq_one {v : ValueHOL 64} (h : shapeEqHOL (shapeOfHOLExact v) .one = true) : shapeOfHOLExact v = .one := by
  revert h; generalize shapeOfHOLExact v = sh; cases sh <;> simp [shapeEqHOL]

theorem shOne_valid {s : PanSemStateFiniteExact 64 σ} {x : MlS} {v : ValueHOL 64}
    (hv : isValidValueHOLExact s.toExact .local x v = true) (h : ShOne (s.locals.lookup x)) :
    ShOne ((s.locals.update (x, v)).lookup x) := by
  obtain ⟨w, hw, hsh⟩ := h
  simp only [isValidValueHOLExact, lookupKvarHOLExact, PanSemStateFiniteExact.toExact, hw, hsh] at hv
  exact ⟨v, by simp [FUPDATE], shapeEq_one hv⟩

/-- What a single run keeps. -/
def KPost (x : MlS) (p : ProgHOL 64) (s : PanSemStateFiniteExact 64 σ)
    (A : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ) : Prop :=
  Normalish A.1 → (occ x p = false → A.2.locals.lookup x = s.locals.lookup x) ∧
    (ShOne (s.locals.lookup x) → ShOne (A.2.locals.lookup x))

def KN (x : MlS) (n : Nat) (p : ProgHOL 64) : Prop :=
  ∀ (s : PanSemStateFiniteExact 64 σ), s.clock ≤ n → KPost x p s (evaluateHOLFiniteState s p)

theorem kpost_ab {x : MlS} {p : ProgHOL 64} {s : PanSemStateFiniteExact 64 σ} {r : PanSemResultExact 64}
    {u : PanSemStateFiniteExact 64 σ} (h : ¬ Normalish (some r)) : KPost x p s (some r, u) :=
  fun hn => absurd hn h

theorem kpost_same {x : MlS} {p : ProgHOL 64} {s : PanSemStateFiniteExact 64 σ} (r : Option (PanSemResultExact 64))
    {u : PanSemStateFiniteExact 64 σ} (h : u.locals = s.locals) : KPost x p s (r, u) :=
  fun _ => ⟨fun _ => by rw [h], fun h0 => by rw [h]; exact h0⟩

theorem kpost_set {x y : MlS} {p : ProgHOL 64} {s : PanSemStateFiniteExact 64 σ} (r : Option (PanSemResultExact 64))
    (v : ValueHOL 64) (hy : occ x p = false → y ≠ x)
    (hv : y = x → isValidValueHOLExact s.toExact .local x v = true) (t : PanSemStateFiniteExact 64 σ) :
    KPost x p s (r, { t with locals := s.locals.update (y, v) }) := by
  intro _
  by_cases h : y = x
  · subst h
    exact ⟨fun ho => absurd rfl (hy ho), fun h0 => shOne_valid (hv rfl) h0⟩
  · exact ⟨fun _ => upd_at h _ _, fun h0 => by simp only [upd_at h]; exact h0⟩

theorem kp_step (x : MlS) (n : Nat) (ih : ∀ m, m < n → ∀ p, KN (σ := σ) x m p) :
    ∀ p, KN (σ := σ) x n p
  | .skip => fun s _ => by
    rw [evaluateHOLFiniteState_eq_evaluate_def s .skip]; exact kpost_same _ rfl
  | .break => fun s _ => by
    rw [evaluateHOLFiniteState_eq_evaluate_def s .break]; exact kpost_same _ rfl
  | .continue => fun s _ => by
    rw [evaluateHOLFiniteState_eq_evaluate_def s .continue]; exact kpost_same _ rfl
  | .annot _ _ => fun s _ => by
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.annot _ _)]; exact kpost_same _ rfl
  | .tick => fun s _ => by
    rw [evaluateHOLFiniteState_eq_evaluate_def s .tick]; dsimp only
    split
    · exact kpost_ab (by simp [Normalish])
    · exact kpost_same _ rfl
  | .raise eid e => fun s _ => by
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.raise eid e)]; dsimp only
    repeat' split
    all_goals first | exact kpost_ab (by simp [Normalish]) | exact kpost_same _ rfl
  | .return e => fun s _ => by
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.return e)]; dsimp only
    repeat' split
    all_goals first | exact kpost_ab (by simp [Normalish]) | exact kpost_same _ rfl
  | .store a v => fun s _ => by
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.store a v)]; dsimp only
    repeat' split
    all_goals first | exact kpost_ab (by simp [Normalish]) | exact kpost_same _ rfl
  | .store32 a v => fun s _ => by
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.store32 a v)]; dsimp only
    repeat' split
    all_goals first | exact kpost_ab (by simp [Normalish]) | exact kpost_same _ rfl
  | .storeByte a v => fun s _ => by
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.storeByte a v)]; dsimp only
    repeat' split
    all_goals first | exact kpost_ab (by simp [Normalish]) | exact kpost_same _ rfl
  | .extCall g a b c d => fun s _ => by
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.extCall g a b c d)]; dsimp only
    repeat' split
    all_goals first | exact kpost_ab (by simp [Normalish]) | exact kpost_same _ rfl
  | .shMemStore op a v => fun s _ => by
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.shMemStore op a v)]; dsimp only
    split
    · refine kpost_same _ (HolFiniteMapExact.ext ?_)
      simp only [PanSemStateFiniteExact.ofExact]
      unfold shMemStoreHOLExact
      repeat' split
      all_goals rfl
    · exact kpost_ab (by simp [Normalish])
  | .shMemLoad op k y a => fun s _ => by
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.shMemLoad op k y a)]; dsimp only
    split
    · split
      · rename_i hlk
        simp only [shMemLoadHOLFiniteExact]
        repeat' split
        all_goals first
          | exact kpost_ab (by simp [Normalish])
          | exact kpost_same _ rfl
          | skip
        all_goals
          simp only [setKvarFfiHOLFinite]
          cases k
          · simp only [setKvarHOLFinite, setVarHOLFinite]
            intro _
            by_cases h : y = x
            · subst h
              exact ⟨fun ho => by simp [occ] at ho, fun _ => ⟨_, upd_self _ _ _, shape_val _⟩⟩
            · exact ⟨fun _ => upd_at h _ _, fun h0 => by simp only [upd_at h]; exact h0⟩
          · exact kpost_same _ rfl
      · exact kpost_ab (by simp [Normalish])
    · exact kpost_ab (by simp [Normalish])
  | .assign k y e => fun s _ => by
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.assign k y e)]; dsimp only
    split
    · exact kpost_ab (by simp [Normalish])
    · split
      · rename_i hv
        cases k
        · exact kpost_set _ _ (fun ho => by simp [occ] at ho; exact ho.1)
            (fun h => by subst h; simpa using hv) s
        · exact kpost_same _ rfl
      · exact kpost_ab (by simp [Normalish])
  | .primitive y op args => fun s _ => by
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.primitive y op args)]; dsimp only
    repeat' split
    all_goals first
      | exact kpost_ab (by simp [Normalish])
      | (rename_i hv; exact kpost_set _ _ (fun ho => by simp [occ] at ho) (fun h => by subst h; simpa using hv) s)
  | .seq a b => fun s hn => by
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.seq a b)]; dsimp only
    have ha := kp_step x n ih a s hn
    generalize hA : evaluateHOLFiniteState s a = A at ha ⊢
    obtain ⟨r, u⟩ := A
    cases r with
    | none =>
      have hb := kp_step x n ih b u (Nat.le_trans (clock_of hA) hn)
      intro hn'
      obtain ⟨ha1, ha2⟩ := ha trivial
      obtain ⟨hb1, hb2⟩ := hb hn'
      refine ⟨fun ho => ?_, fun h0 => hb2 (ha2 h0)⟩
      simp only [occ, Bool.or_eq_false_iff] at ho
      rw [hb1 ho.2, ha1 ho.1]
    | some r =>
      intro hn'
      obtain ⟨ha1, ha2⟩ := ha hn'
      exact ⟨fun ho => ha1 (by simp only [occ, Bool.or_eq_false_iff] at ho; exact ho.1), ha2⟩
  | .ite c a b => fun s hn => by
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.ite c a b)]; dsimp only
    split
    · split
      · intro hn'
        obtain ⟨h1, h2⟩ := kp_step x n ih b s hn hn'
        exact ⟨fun ho => h1 (by simp only [occ, Bool.or_eq_false_iff] at ho; exact ho.2), h2⟩
      · intro hn'
        obtain ⟨h1, h2⟩ := kp_step x n ih a s hn hn'
        exact ⟨fun ho => h1 (by simp only [occ, Bool.or_eq_false_iff] at ho; exact ho.1.2), h2⟩
    · exact kpost_ab (by simp [Normalish])
  | .dec y sh e b => fun s hn => by
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.dec y sh e b)]; dsimp only
    split
    · exact kpost_ab (by simp [Normalish])
    · split
      · rename_i v _ _
        intro hn'
        by_cases hy : y = x
        · subst hy
          exact ⟨fun _ => by simp [resVar_self], fun h => by simpa [resVar_self] using h⟩
        · have hb := kp_step x n ih b (setVarHOLFinite y v s) hn
          obtain ⟨h1, h2⟩ := hb hn'
          simp only [setVarHOLFinite, upd_at hy] at h1 h2
          simp only [resVar_at hy]
          exact ⟨fun ho => h1 (by simp only [occ, Bool.or_eq_false_iff] at ho; exact ho.2), h2⟩
      · exact kpost_ab (by simp [Normalish])
  | .while c b => fun s hn => by
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.while c b)]; dsimp only
    split
    · split
      · split
        · exact kpost_ab (by simp [Normalish])
        · rename_i hk
          have hb := kp_step x n ih b (decClockHOLFinite s) (by simp [decClockHOLFinite]; omega)
          generalize hW : evaluateHOLFiniteState (decClockHOLFinite s) b = W at hb ⊢
          obtain ⟨r, w⟩ := W
          have hcw : w.clock < n := by
            have := clock_of hW; simp [decClockHOLFinite] at this; omega
          have hob : occ x (.while c b) = false → occ x b = false := by
            intro ho; simp only [occ, Bool.or_eq_false_iff] at ho; exact ho.2
          have hnext : Normalish r → KPost x (.while c b) s (evaluateHOLFiniteState w (.while c b)) := by
            intro hr hn'
            obtain ⟨h1, h2⟩ := hb hr
            obtain ⟨h3, h4⟩ := ih w.clock hcw (.while c b) w (Nat.le_refl _) hn'
            exact ⟨fun ho => by rw [h3 ho, h1 (hob ho)]; rfl, fun h0 => h4 (h2 h0)⟩
          cases r with
          | none => exact hnext trivial
          | some r =>
            cases r with
            | «continue» => exact hnext trivial
            | «break» =>
              intro _
              obtain ⟨h1, h2⟩ := hb trivial
              exact ⟨fun ho => h1 (hob ho), h2⟩
            | _ => exact kpost_ab (by simp [Normalish])
      · exact kpost_same _ rfl
    · exact kpost_ab (by simp [Normalish])
  | .call info f args => fun s hn => by
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.call info f args)]; dsimp only
    split
    · exact kpost_ab (by simp [Normalish])
    · split
      · exact kpost_ab (by simp [Normalish])
      · split
        · exact kpost_ab (by simp [Normalish])
        · generalize hC : evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ = C
          obtain ⟨rc, st⟩ := C
          cases rc with
          | none => exact kpost_ab (by simp [Normalish])
          | some r =>
            cases r with
            | returned v =>
              dsimp only
              split
              · rcases info with _ | ⟨_ | ⟨k, y⟩, hd⟩
                · exact kpost_ab (by simp [Normalish])
                · exact kpost_same _ rfl
                · dsimp only
                  split
                  · rename_i hv
                    cases k
                    · exact kpost_set _ _ (fun ho => by
                          rcases hd with _ | _ <;> simp [occ] at ho; exact ho.1)
                        (fun h => by subst h; exact hv) st
                    · exact kpost_same _ rfl
                  · exact kpost_ab (by simp [Normalish])
              · exact kpost_ab (by simp [Normalish])
            | exception eid v =>
              dsimp only
              rcases info with _ | ⟨ret, _ | ⟨hid, hv, h⟩⟩
              · exact kpost_ab (by simp [Normalish])
              · exact kpost_ab (by simp [Normalish])
              · dsimp only
                split
                · split
                  · split
                    · rename_i hcond
                      simp only [Bool.and_eq_true] at hcond
                      intro hn'
                      have hcl : (setVarHOLFinite hv v { st with locals := s.locals }).clock ≤ n := by
                        have := clock_of hC
                        simp [callEntryStateHOLFinite] at this
                        show st.clock ≤ n; omega
                      obtain ⟨h1, h2⟩ := kp_step x n ih h _ hcl hn'
                      refine ⟨fun ho => by simp [occ] at ho, fun h0 => h2 ?_⟩
                      simp only [setVarHOLFinite]
                      by_cases hx : hv = x
                      · subst hx
                        exact shOne_valid (s := { st with locals := s.locals }) hcond.2 h0
                      · simp only [upd_at hx]; exact h0
                    · exact kpost_ab (by simp [Normalish])
                  · exact kpost_ab (by simp [Normalish])
                · exact kpost_ab (by simp [Normalish])
            | _ => exact kpost_ab (by simp [Normalish])
  | .decCall y sh f args k => fun s hn => by
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.decCall y sh f args k)]; dsimp only
    split
    · exact kpost_ab (by simp [Normalish])
    · split
      · exact kpost_ab (by simp [Normalish])
      · split
        · exact kpost_ab (by simp [Normalish])
        · generalize hC : evaluateHOLFiniteState (callEntryStateHOLFinite s _) _ = C
          obtain ⟨rc, st⟩ := C
          cases rc with
          | none => exact kpost_ab (by simp [Normalish])
          | some r =>
            cases r with
            | returned v =>
              dsimp only
              split
              · intro hn'
                by_cases hy : y = x
                · subst hy
                  exact ⟨fun _ => by simp [resVar_self], fun h => by simpa [resVar_self] using h⟩
                · have hcl : (setVarHOLFinite y v { st with locals := s.locals }).clock ≤ n := by
                    have := clock_of hC
                    simp [callEntryStateHOLFinite] at this
                    show st.clock ≤ n; omega
                  obtain ⟨h1, h2⟩ := kp_step x n ih k _ hcl hn'
                  simp only [setVarHOLFinite, upd_at hy] at h1 h2
                  simp only [resVar_at hy]
                  exact ⟨fun ho => by simp [occ] at ho, h2⟩
              · exact kpost_ab (by simp [Normalish])
            | _ => exact kpost_ab (by simp [Normalish])

theorem kp (x : MlS) : ∀ n p, KN (σ := σ) x n p := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihn => exact kp_step x n ihn

end

end ConPanqueque.Logic
