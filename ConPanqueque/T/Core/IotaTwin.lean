import ConPanqueque.T.Core.ReduceProj
open ConRon.Arena

/-!
# The ι step's major premise, on the twin side

Read-only twin computations (`RO`), and `prepareMajor_view`: a `.ctor` classification is `ctorView` of its
term at the state it is returned in, so the port re-derives the constructor record instead of passing it back.
-/

namespace ConPanqueque.T.WC

theorem getAppFn_ro : ∀ (fuel : Nat) (h : EIdx) (s : AState) (r : EIdx) (s' : AState),
    getAppFn fuel h s = .ok (r, s') → s' = s := by
  intro fuel
  induction fuel with
  | zero => intro h s r s' e; simp [getAppFn, fail, throw, throwThe, MonadExceptOf.throw] at e; cases e
  | succ n ih =>
    intro h s r s' e
    unfold getAppFn at e
    by_cases ht : (h.tag == ETag.app) = true
    · rw [if_pos ht] at e
      simp only [bind, StateT.bind] at e
      rw [show viewApp h s = .ok (s.store.viewApp h, s) from rfl] at e
      simp only [Except.bind] at e
      cases hv : s.store.viewApp h with
      | none => rw [hv] at e; simp [failDanglingE, fail, throwThe, MonadExceptOf.throw] at e; cases e
      | some p => obtain ⟨f, a⟩ := p; rw [hv] at e; exact ih f s r s' e
    · rw [if_neg ht] at e
      simp [pure, StateT.pure, Except.pure] at e
      exact e.2.symm


theorem bind_ok_inv {α β : Type} {m : AM α} {k : α → AM β} {s : AState} {a : β} {s' : AState}
    (h : (m >>= k) s = .ok (a, s')) : ∃ b s1, m s = .ok (b, s1) ∧ k b s1 = .ok (a, s') := by
  simp only [bind, StateT.bind] at h
  cases hm : m s with
  | error e => rw [hm] at h; cases h
  | ok p => obtain ⟨b, s1⟩ := p; rw [hm] at h; exact ⟨b, s1, rfl, h⟩

theorem pure_ok_inv {α : Type} {x a : α} {s s' : AState} (h : (pure x : AM α) s = .ok (a, s')) : a = x ∧ s' = s := by
  simp [pure, StateT.pure, Except.pure] at h; exact ⟨h.1.symm, h.2.symm⟩

theorem fail_ok_inv {α : Type} {e : CheckError} {s : AState} {a : α} {s' : AState} (h : (fail e : AM α) s = .ok (a, s')) :
    False := by
  simp [fail, throwThe, MonadExceptOf.throw] at h; cases h

theorem failDanglingE_ok_inv {α : Type} {s : AState} {a : α} {s' : AState} (h : (failDanglingE : AM α) s = .ok (a, s')) :
    False := by
  simp [failDanglingE, fail, throwThe, MonadExceptOf.throw] at h; cases h

theorem ctorView_ro (fe : IFEnv) (a : EIdx) (s : AState) (v : MajorView) (s' : AState)
    (h : ctorView fe a s = .ok (v, s')) : s' = s ∧ v.expr = a := by
  unfold ctorView at h
  obtain ⟨hd, s1, h1, h2⟩ := bind_ok_inv h
  have e1 := getAppFn_ro _ _ _ _ _ h1
  rw [e1] at h2
  clear h1 e1 s1
  by_cases ht : (hd.tag == ETag.const) = true
  · rw [if_pos ht] at h2
    obtain ⟨oc, s2, h3, h4⟩ := bind_ok_inv h2
    have e3 : oc = s.store.viewConst hd ∧ s2 = s := by
      have : viewConst hd s = .ok (s.store.viewConst hd, s) := rfl
      rw [this] at h3; cases h3; exact ⟨rfl, rfl⟩
    obtain ⟨e3a, e3b⟩ := e3
    rw [e3a, e3b] at h4
    cases hoc : s.store.viewConst hd with
    | none => rw [hoc] at h4; exact (failDanglingE_ok_inv h4).elim
    | some p =>
      obtain ⟨cj, usj⟩ := p
      rw [hoc] at h4
      dsimp only at h4
      rcases hf : fe.find? cj with _ | ci
      · rw [hf] at h4; obtain ⟨rfl, rfl⟩ := pure_ok_inv h4; exact ⟨rfl, rfl⟩
      · rw [hf] at h4
        cases ci <;> (dsimp only at h4; obtain ⟨rfl, rfl⟩ := pure_ok_inv h4; exact ⟨rfl, rfl⟩)
  · rw [if_neg ht] at h2
    obtain ⟨rfl, rfl⟩ := pure_ok_inv h2; exact ⟨rfl, rfl⟩


/-- A read-only twin computation: a successful run leaves the state unchanged. -/
def RO {α : Type} (m : AM α) : Prop := ∀ s a s', m s = .ok (a, s') → s' = s

theorem RO.pure {α : Type} (x : α) : RO (pure x : AM α) := by
  intro s a s' h; simp [Pure.pure, StateT.pure, Except.pure] at h; exact h.2.symm

theorem RO.bind {α β : Type} {m : AM α} {k : α → AM β} (hm : RO m) (hk : ∀ a, RO (k a)) : RO (m >>= k) := by
  intro s a s' h
  simp only [Bind.bind, StateT.bind] at h
  cases e : m s with
  | error _ => rw [e] at h; cases h
  | ok p => obtain ⟨b, s1⟩ := p; rw [e] at h; rw [hk b s1 a s' h, hm s b s1 e]

theorem RO.fail {α : Type} (e : CheckError) : RO (fail e : AM α) := by
  intro s a s' h; simp [ConRon.Arena.fail, throwThe, MonadExceptOf.throw] at h; cases h

theorem RO.failDanglingE {α : Type} : RO (failDanglingE : AM α) := RO.fail _

theorem RO.ite {α : Type} (c : Prop) [Decidable c] {m₁ m₂ : AM α} (h₁ : RO m₁) (h₂ : RO m₂) :
    RO (if c then m₁ else m₂) := by
  by_cases hc : c
  · rw [if_pos hc]; exact h₁
  · rw [if_neg hc]; exact h₂

theorem RO.get : RO (get : AM AState) := by
  intro s a s' h; simp [MonadState.get, getThe, MonadStateOf.get, StateT.get, Pure.pure, Except.pure] at h
  exact h.2.symm

theorem RO.view (h : EIdx) : RO (ConRon.Arena.view h) := by
  unfold ConRon.Arena.view
  refine RO.bind RO.get (fun s => ?_)
  split
  · exact RO.pure _
  · exact RO.failDanglingE

theorem RO.viewLit (h : EIdx) : RO (ConRon.Arena.viewLit h) := RO.bind RO.get (fun _ => RO.pure _)
theorem RO.viewConst (h : EIdx) : RO (ConRon.Arena.viewConst h) := RO.bind RO.get (fun _ => RO.pure _)
theorem RO.viewApp (h : EIdx) : RO (ConRon.Arena.viewApp h) := RO.bind RO.get (fun _ => RO.pure _)

theorem RO.pinAt (i : Nat) : RO (ConRon.Arena.pinAt i) := by
  unfold ConRon.Arena.pinAt
  refine RO.bind RO.get (fun s => ?_)
  split
  · exact RO.pure _
  · exact RO.fail _

theorem RO.pinEmptyLevels : RO ConRon.Arena.pinEmptyLevels := by
  unfold ConRon.Arena.pinEmptyLevels
  exact RO.bind RO.get (fun s => RO.ite _ (RO.pure _) (RO.fail _))

theorem RO.isStrLit (h : EIdx) : RO (ConRon.Arena.isStrLit h) := by
  unfold ConRon.Arena.isStrLit
  refine RO.ite _ (RO.bind (RO.viewLit h) (fun o => ?_)) (RO.pure _)
  rcases o with _ | l
  · exact RO.failDanglingE
  · cases l <;> exact RO.pure _

theorem RO.isNatSuccApp (e : EIdx) : RO (ConRon.Arena.isNatSuccApp e) := by
  unfold ConRon.Arena.isNatSuccApp
  refine RO.ite _ (RO.bind (RO.view e) (fun v => ?_)) (RO.pure _)
  cases v <;> try exact RO.pure _
  rename_i f a
  refine RO.ite _ (RO.bind (RO.view f) (fun w => ?_)) (RO.pure _)
  cases w <;> try exact RO.pure _
  exact RO.bind RO.pinEmptyLevels (fun _ => RO.bind (RO.pinAt _) (fun _ => RO.pure _))


/-- A `.ctor` classification is `ctorView` of its term, re-run at the state it is handed over in. -/
def CtorOK (fe : IFEnv) (mv : MajorView) (s : AState) : Prop :=
  mv.isCtor = true → ctorView fe mv.expr s = .ok (mv, s)

theorem majorToCtor_view (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (d : Nat) (c : NIdx) (isK : Bool)
    (rules : List IRecRule) (m : EIdx) (s : AState) (mv : MajorView) (s' : AState)
    (h : majorToCtor mode r fe d c isK rules m s = .ok (mv, s')) : CtorOK fe mv s' := by
  unfold majorToCtor at h
  obtain ⟨v, s1, h1, h2⟩ := bind_ok_inv h
  obtain ⟨e1, ex⟩ := ctorView_ro fe m s v s1 h1
  by_cases hv : v.isCtor = true
  · rw [if_pos hv] at h2
    obtain ⟨rfl, rfl⟩ := pure_ok_inv h2
    intro _
    rw [ex]; rw [e1] at h1 ⊢; exact h1
  · rw [if_neg hv] at h2
    obtain ⟨x, s2, h3, h4⟩ := bind_ok_inv h2
    by_cases hx : (x == m) = true
    · rw [if_pos hx] at h4
      obtain ⟨rfl, rfl⟩ := pure_ok_inv h4
      intro hc; simp [MajorView.isCtor] at hc
    · rw [if_neg hx] at h4
      obtain ⟨e4, ex4⟩ := ctorView_ro fe x s2 mv s' h4
      intro _
      rw [ex4, e4]; rw [e4] at h4; exact h4

theorem prepareMajorWhnf_view (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (d : Nat) (c : NIdx)
    (isK : Bool) (rules : List IRecRule) (m : EIdx) (s : AState) (mv : MajorView) (s' : AState)
    (h : prepareMajorWhnf mode r fe d c isK rules m s = .ok (mv, s')) : CtorOK fe mv s' := by
  unfold prepareMajorWhnf at h
  obtain ⟨_, _, _, h2⟩ := bind_ok_inv h
  obtain ⟨_, _, _, h4⟩ := bind_ok_inv h2
  exact majorToCtor_view mode r fe d c isK rules _ _ mv s' h4

theorem prepareMajor_view (mode : ConLeche.CheckMode) (r : CoreFnsA) (fe : IFEnv) (d : Nat) (c : NIdx)
    (isK : Bool) (rules : List IRecRule) (m : EIdx) (s : AState) (mv : MajorView) (s' : AState)
    (h : prepareMajor mode r fe d c isK rules m s = .ok (mv, s')) : CtorOK fe mv s' := by
  unfold prepareMajor at h
  cases isK
  · simp only [Bool.false_eq_true, ite_false] at h
    have hrest : ∀ (vE : MajorView) s1, CtorOK fe vE s1 →
        (if vE.isCtor = true then (isNatSuccApp vE.expr >>= fun b =>
            if b = true then prepareMajorWhnf mode r fe d c false rules vE.expr else pure vE)
          else prepareMajorWhnf mode r fe d c false rules vE.expr) s1 = .ok (mv, s') → CtorOK fe mv s' := by
      intro vE s1 hv1 h2
      by_cases hc : vE.isCtor = true
      · rw [if_pos hc] at h2
        obtain ⟨b, s2, h3, h4⟩ := bind_ok_inv h2
        have e3 := RO.isNatSuccApp vE.expr s1 b s2 h3
        cases b
        · simp only [Bool.false_eq_true, ite_false] at h4
          obtain ⟨rfl, rfl⟩ := pure_ok_inv h4
          rw [e3]; exact hv1
        · simp only [ite_true] at h4
          exact prepareMajorWhnf_view mode r fe d c false rules _ _ mv s' h4
      · rw [if_neg hc] at h2
        exact prepareMajorWhnf_view mode r fe d c false rules _ _ mv s' h2
    obtain ⟨b, s0, h0, h1'⟩ := bind_ok_inv h
    cases b
    · simp only [Bool.false_eq_true, ite_false] at h1'
      obtain ⟨vE, s1, h1, h2⟩ := bind_ok_inv h1'
      exact hrest vE s1 (majorToCtor_view mode r fe d c false rules m s0 vE s1 h1) h2
    · simp only [ite_true] at h1'
      obtain ⟨vE, s1, h1, h2⟩ := bind_ok_inv h1'
      obtain ⟨rfl, rfl⟩ := pure_ok_inv h1
      exact hrest _ _ (fun hc => by simp [MajorView.isCtor] at hc) h2
  · simp only [ite_true] at h
    exact majorToCtor_view mode r fe d c true rules m s mv s' h

end ConPanqueque.T.WC
