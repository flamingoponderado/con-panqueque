import ConPanqueque.Logic.NarrowFrame

/-! # Narrowing local scopes: the simulation

`narrowT` (`ConPanqueque/Logic/NarrowDefs.lean`) rewrites every function body.  `narrowT_sim`: from
a state whose code table is the narrowed table of the code table of `s`, the narrowed program gives
the result of the original one, with the same final state apart from the code table and (when the
result is not `none`/`break`/`continue`) the locals. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString

namespace ConPanqueque.Logic

section
variable {σ : Type}

/-! ## Same code table: `Sim0` -/

/-- Two outputs: same result, same state apart from the locals, same locals if the result lets the
enclosing statement go on. -/
def ROut (A B : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ) : Prop :=
  B.1 = A.1 ∧ B.2 = { A.2 with locals := B.2.locals } ∧ (Normalish A.1 → B.2.locals = A.2.locals)

theorem rout_refl (A : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ) : ROut A A :=
  ⟨rfl, by cases A.2; rfl, fun _ => rfl⟩

theorem rout_trans {A B C : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ}
    (h1 : ROut A B) (h2 : ROut B C) : ROut A C := by
  refine ⟨h2.1.trans h1.1, ?_, fun hn => (h2.2.2 (h1.1 ▸ hn)).trans (h1.2.2 hn)⟩
  rw [h2.2.1, h1.2.1]

theorem rout_symm {A B : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ} (h : ROut A B) : ROut B A := by
  refine ⟨h.1.symm, ?_, fun hn => (h.2.2 (h.1 ▸ hn)).symm⟩
  rw [h.2.1]

theorem rout_eq {A B : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ} (h : ROut A B) (hn : Normalish A.1) :
    B = A := by
  obtain ⟨r, u⟩ := A
  obtain ⟨r', u'⟩ := B
  obtain ⟨h1, h2, h3⟩ := h
  simp only at h1 h2 h3 hn
  subst h1
  rw [h2, h3 hn]

end

/-- `q` behaves like `p` from every state. -/
def Sim0 (p q : ProgHOL 64) : Prop :=
  ∀ (σ : Type) (s : PanSemStateFiniteExact 64 σ), ROut (evaluateHOLFiniteState s p) (evaluateHOLFiniteState s q)

/-- `q` evaluates exactly like `p`. -/
def EqE (p q : ProgHOL 64) : Prop :=
  ∀ (σ : Type) (s : PanSemStateFiniteExact 64 σ), evaluateHOLFiniteState s p = evaluateHOLFiniteState s q

theorem sim0_refl (p : ProgHOL 64) : Sim0 p p := fun _ s => rout_refl _
theorem sim0_trans {p q r : ProgHOL 64} (h1 : Sim0 p q) (h2 : Sim0 q r) : Sim0 p r :=
  fun _ s => rout_trans (h1 _ s) (h2 _ s)
theorem sim0_symm {p q : ProgHOL 64} (h : Sim0 p q) : Sim0 q p := fun _ s => rout_symm (h _ s)
theorem sim0_of_eqE {p q : ProgHOL 64} (h : EqE p q) : Sim0 p q := fun _ s => by rw [h _ s]; exact rout_refl _
theorem eqE_symm {p q : ProgHOL 64} (h : EqE p q) : EqE q p := fun _ s => (h _ s).symm
theorem eqE_trans {p q r : ProgHOL 64} (h1 : EqE p q) (h2 : EqE q r) : EqE p r := fun _ s => (h1 _ s).trans (h2 _ s)

theorem sim0_seq {a a' b b' : ProgHOL 64} (ha : Sim0 a a') (hb : Sim0 b b') : Sim0 (.seq a b) (.seq a' b') := by
  intro σ s
  rw [evaluateHOLFiniteState_eq_evaluate_def s (.seq a b), evaluateHOLFiniteState_eq_evaluate_def s (.seq a' b')]
  dsimp only
  have h := ha _ s
  generalize evaluateHOLFiniteState s a = A at h ⊢
  generalize evaluateHOLFiniteState s a' = B at h ⊢
  obtain ⟨r, u⟩ := A
  cases r with
  | none =>
    rw [rout_eq h trivial]
    exact hb _ u
  | some r =>
    obtain ⟨r', u'⟩ := B
    obtain ⟨h1, h2, h3⟩ := h
    simp only at h1 h2 h3
    subst h1
    exact ⟨rfl, h2, h3⟩

theorem sim0_ite (c : ExpHOL 64) {a a' b b' : ProgHOL 64} (ha : Sim0 a a') (hb : Sim0 b b') :
    Sim0 (.ite c a b) (.ite c a' b') := by
  intro σ s
  rw [evaluateHOLFiniteState_eq_evaluate_def s (.ite c a b), evaluateHOLFiniteState_eq_evaluate_def s (.ite c a' b')]
  dsimp only
  split
  · split
    · exact hb _ s
    · exact ha _ s
  · exact rout_refl _

theorem sim0_dec (x : MlS) (sh : ShapeHOL) (e : ExpHOL 64) {b b' : ProgHOL 64} (hb : Sim0 b b') :
    Sim0 (.dec x sh e b) (.dec x sh e b') := by
  intro σ s
  rw [evaluateHOLFiniteState_eq_evaluate_def s (.dec x sh e b), evaluateHOLFiniteState_eq_evaluate_def s (.dec x sh e b')]
  dsimp only
  split
  · exact rout_refl _
  · split
    · rename_i v _ _
      have h := hb _ (setVarHOLFinite x v s)
      generalize evaluateHOLFiniteState (setVarHOLFinite x v s) b = A at h ⊢
      generalize evaluateHOLFiniteState (setVarHOLFinite x v s) b' = B at h ⊢
      obtain ⟨r, u⟩ := A
      obtain ⟨r', u'⟩ := B
      obtain ⟨h1, h2, h3⟩ := h
      simp only at h1 h2 h3
      subst h1
      refine ⟨rfl, ?_, fun hn => ?_⟩
      · simp only; rw [h2]
      · simp only; rw [h3 hn]
    · exact rout_refl _

theorem eqE_seq {a a' b b' : ProgHOL 64} (ha : EqE a a') (hb : EqE b b') : EqE (.seq a b) (.seq a' b') := by
  intro σ s
  rw [evaluateHOLFiniteState_eq_evaluate_def s (.seq a b), evaluateHOLFiniteState_eq_evaluate_def s (.seq a' b')]
  dsimp only
  rw [ha _ s]
  split
  · exact hb _ _
  · rfl

/-! ## Statement lists -/

theorem E_skip {σ : Type} (s : PanSemStateFiniteExact 64 σ) : evaluateHOLFiniteState s .skip = (none, s) := by
  rw [evaluateHOLFiniteState_eq_evaluate_def]

theorem seq_skip_l (b : ProgHOL 64) : EqE (.seq .skip b) b := by
  intro σ s
  rw [evaluateHOLFiniteState_eq_evaluate_def s (.seq .skip b)]
  dsimp only
  rw [E_skip]

theorem seq_skip_r (a : ProgHOL 64) : EqE (.seq a .skip) a := by
  intro σ s
  rw [evaluateHOLFiniteState_eq_evaluate_def s (.seq a .skip)]
  dsimp only
  generalize evaluateHOLFiniteState s a = A
  obtain ⟨r, u⟩ := A
  cases r
  · simp only; rw [E_skip]
  · rfl

theorem eqE_assoc (a b c : ProgHOL 64) : EqE (.seq (.seq a b) c) (.seq a (.seq b c)) := fun _ s => seq_assoc s a b c

theorem ofL_cons (a : ProgHOL 64) (l : List (ProgHOL 64)) : EqE (ofL (a :: l)) (.seq a (ofL l)) := by
  cases l with
  | nil => exact eqE_symm (seq_skip_r a)
  | cons b l => intro σ s; rfl

theorem ofL_append : ∀ (l1 l2 : List (ProgHOL 64)), EqE (ofL (l1 ++ l2)) (.seq (ofL l1) (ofL l2))
  | [], l2 => eqE_symm (seq_skip_l _)
  | a :: l1, l2 => by
    refine eqE_trans (ofL_cons a (l1 ++ l2)) ?_
    refine eqE_trans (eqE_seq (fun _ _ => rfl) (ofL_append l1 l2)) ?_
    refine eqE_trans (eqE_symm (eqE_assoc _ _ _)) ?_
    exact eqE_seq (eqE_symm (ofL_cons a l1)) (fun _ _ => rfl)

theorem ofL_toL : ∀ (p : ProgHOL 64), EqE (ofL (toL p)) p
  | .seq a b => eqE_trans (ofL_append (toL a) (toL b)) (eqE_seq (ofL_toL a) (ofL_toL b))
  | .skip => fun _ _ => rfl
  | .dec .. => fun _ _ => rfl
  | .assign .. => fun _ _ => rfl
  | .primitive .. => fun _ _ => rfl
  | .store .. => fun _ _ => rfl
  | .store32 .. => fun _ _ => rfl
  | .storeByte .. => fun _ _ => rfl
  | .ite .. => fun _ _ => rfl
  | .while .. => fun _ _ => rfl
  | .break => fun _ _ => rfl
  | .continue => fun _ _ => rfl
  | .call .. => fun _ _ => rfl
  | .decCall .. => fun _ _ => rfl
  | .extCall .. => fun _ _ => rfl
  | .raise .. => fun _ _ => rfl
  | .return .. => fun _ _ => rfl
  | .shMemLoad .. => fun _ _ => rfl
  | .shMemStore .. => fun _ _ => rfl
  | .tick => fun _ _ => rfl
  | .annot .. => fun _ _ => rfl

/-! ## Flattening an `if` with a leaving branch -/

theorem aborts_some {σ : Type} (s : PanSemStateFiniteExact 64 σ) {a : ProgHOL 64} (h : aborts a = true) :
    (evaluateHOLFiniteState s a).1 ≠ none := by
  match a, h with
  | .call none f args, _ =>
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.call none f args)]
    dsimp only
    repeat' split
    all_goals simp
  | .return e, _ =>
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.return e)]
    dsimp only
    repeat' split
    all_goals simp

theorem flatIte_eqE (c : ExpHOL 64) (a b : ProgHOL 64) : EqE (.ite c a b) (flatIte c a b) := by
  intro σ s
  unfold flatIte
  split
  · rename_i ha
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.ite c a b),
      evaluateHOLFiniteState_eq_evaluate_def s (.seq (.ite c a .skip) b)]
    dsimp only
    rw [evaluateHOLFiniteState_eq_evaluate_def s (.ite c a .skip)]
    dsimp only
    split
    · split
      · rw [E_skip]
      · have := aborts_some s ha
        generalize evaluateHOLFiniteState s a = A at this ⊢
        obtain ⟨r, u⟩ := A
        cases r
        · exact absurd rfl this
        · rfl
    · rfl
  · split
    · rename_i _ hb
      rw [evaluateHOLFiniteState_eq_evaluate_def s (.ite c a b),
        evaluateHOLFiniteState_eq_evaluate_def s (.seq (.ite c .skip b) a)]
      dsimp only
      rw [evaluateHOLFiniteState_eq_evaluate_def s (.ite c .skip b)]
      dsimp only
      split
      · split
        · have := aborts_some s hb
          generalize evaluateHOLFiniteState s b = A at this ⊢
          obtain ⟨r, u⟩ := A
          cases r
          · exact absurd rfl this
          · rfl
        · rw [E_skip]
      · rfl
    · rfl

/-! ## Declarations of a constant -/

theorem E_decC {σ : Type} (s : PanSemStateFiniteExact 64 σ) (x : MlS) (c : BitVec 64) (p : ProgHOL 64) :
    evaluateHOLFiniteState s (decC x c p) =
      ((evaluateHOLFiniteState (setVarHOLFinite x (.val (.word c)) s) p).1,
       { (evaluateHOLFiniteState (setVarHOLFinite x (.val (.word c)) s) p).2 with
         locals := HolFiniteMapExact.resVarEq
           (evaluateHOLFiniteState (setVarHOLFinite x (.val (.word c)) s) p).2.locals (x, s.locals.lookup x) }) := by
  unfold decC
  rw [evaluateHOLFiniteState_eq_evaluate_def]
  dsimp only
  simp only [evalHOLExact, shape_val, shapeEqHOL, ite_true]

theorem dk_pass_of_occ {x : MlS} : ∀ {p : ProgHOL 64}, occ x p = false → dk x p = .pass
  | .skip, _ => rfl
  | .break, _ => rfl
  | .continue, _ => rfl
  | .tick, _ => rfl
  | .dec y sh e b, h => by
    simp only [occ, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    simp [dk, h.1.1, h.1.2, dk_pass_of_occ h.2]
  | .assign k y e, h => by
    simp only [occ, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    simp [dk, h.1, h.2]
  | .store a v, h => by simp only [occ, Bool.or_eq_false_iff] at h; simp [dk, h.1, h.2]
  | .store32 a v, h => by simp only [occ, Bool.or_eq_false_iff] at h; simp [dk, h.1, h.2]
  | .storeByte a v, h => by simp only [occ, Bool.or_eq_false_iff] at h; simp [dk, h.1, h.2]
  | .seq a b, h => by
    simp only [occ, Bool.or_eq_false_iff] at h
    simp [dk, dk_pass_of_occ h.1, dk_pass_of_occ h.2, DK.seq]
  | .ite c a b, h => by
    simp only [occ, Bool.or_eq_false_iff] at h
    simp [dk, h.1.1, dk_pass_of_occ h.1.2, dk_pass_of_occ h.2, DK.meet]
  | .while c b, h => by
    simp only [occ, Bool.or_eq_false_iff] at h
    simp [dk, h.1, dk_pass_of_occ h.2]
  | .call none f args, h => by simp only [occ] at h; simp [dk, h]
  | .call (some (none, none)) f args, h => by simp only [occ] at h; simp [dk, h]
  | .call (some (some (k, y), none)) f args, h => by
    simp only [occ, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
    simp [dk, h.1, h.2]
  | .call (some (_, some _)) _ _, h => by simp [occ] at h
  | .extCall g a b c d, h => by
    simp only [occ, Bool.or_eq_false_iff] at h
    simp [dk, h.1.1.1, h.1.1.2, h.1.2, h.2]
  | .return e, h => by simp only [occ] at h; simp [dk, h]
  | .primitive .., h => by simp [occ] at h
  | .decCall .., h => by simp [occ] at h
  | .raise .., h => by simp [occ] at h
  | .shMemLoad .., h => by simp [occ] at h
  | .shMemStore .., h => by simp [occ] at h
  | .annot .., h => by simp [occ] at h

theorem upd_off_self (x : MlS) (L : HolFiniteMapExact MlS (ValueHOL 64)) (v : ValueHOL 64) :
    ∀ y, y ≠ x → L.lookup y = (L.update (x, v)).lookup y :=
  fun y hy => (upd_at (Ne.symm hy) L v).symm

theorem resVar_upd_self (x : MlS) (L : HolFiniteMapExact MlS (ValueHOL 64)) (v : ValueHOL 64) :
    HolFiniteMapExact.resVarEq (L.update (x, v)) (x, L.lookup x) = L := by
  apply HolFiniteMapExact.ext; funext z
  by_cases hz : z = x
  · subst hz; rw [resVar_self]
  · rw [resVar_at (Ne.symm hz), upd_at (Ne.symm hz)]

/-- **Drop** a declaration whose variable does not occur. -/
theorem drop_sim (x : MlS) (c : BitVec 64) {p : ProgHOL 64} (ho : occ x p = false) : Sim0 (decC x c p) p := by
  intro σ s
  rw [E_decC]
  have hf := fl (σ := σ) x (setVarHOLFinite x (.val (.word c)) s).clock p (by rw [dk_pass_of_occ ho]; simp)
    (setVarHOLFinite x (.val (.word c)) s) s.locals (Nat.le_refl _) (upd_off_self x s.locals _) (Or.inr ho)
  have e : ({ setVarHOLFinite x (.val (.word c)) s with locals := s.locals } : PanSemStateFiniteExact 64 σ) = s := rfl
  rw [e] at hf
  have hk := kp (σ := σ) x s.clock p s (Nat.le_refl _)
  generalize evaluateHOLFiniteState (setVarHOLFinite x (.val (.word c)) s) p = A at hf ⊢
  generalize evaluateHOLFiniteState s p = B at hf hk ⊢
  obtain ⟨r, u1⟩ := A
  obtain ⟨r2, u2⟩ := B
  obtain ⟨h1, h2, h3, -⟩ := hf
  simp only at h1 h2 h3
  subst h1
  refine ⟨rfl, h2, fun hn => ?_⟩
  apply HolFiniteMapExact.ext; funext z
  by_cases hz : z = x
  · subst hz; simp only [resVar_self]; exact (hk hn).1 ho
  · simp only [resVar_at (Ne.symm hz)]; exact (h3 hn).1.off z hz

/-- **Move** a statement that does not touch the variable out of the scope. -/
theorem move_sim (x : MlS) (c : BitVec 64) {a : ProgHOL 64} (b : ProgHOL 64) (ho : occ x a = false) :
    Sim0 (decC x c (.seq a b)) (.seq a (decC x c b)) := by
  intro σ s
  rw [E_decC, evaluateHOLFiniteState_eq_evaluate_def s (.seq a (decC x c b)),
    evaluateHOLFiniteState_eq_evaluate_def (setVarHOLFinite x (.val (.word c)) s) (.seq a b)]
  dsimp only
  have hf := fl (σ := σ) x (setVarHOLFinite x (.val (.word c)) s).clock a (by rw [dk_pass_of_occ ho]; simp)
    (setVarHOLFinite x (.val (.word c)) s) s.locals (Nat.le_refl _) (upd_off_self x s.locals _) (Or.inr ho)
  have e : ({ setVarHOLFinite x (.val (.word c)) s with locals := s.locals } : PanSemStateFiniteExact 64 σ) = s := rfl
  rw [e] at hf
  have hk := kp (σ := σ) x s.clock a s (Nat.le_refl _)
  have hk1 := kp (σ := σ) x s.clock a (setVarHOLFinite x (.val (.word c)) s) (Nat.le_refl _)
  generalize evaluateHOLFiniteState (setVarHOLFinite x (.val (.word c)) s) a = A at hf hk1 ⊢
  generalize evaluateHOLFiniteState s a = B at hf hk ⊢
  obtain ⟨r, u1⟩ := A
  obtain ⟨r2, u2⟩ := B
  obtain ⟨h1, h2, h3, -⟩ := hf
  simp only at h1 h2 h3
  subst h1
  cases r2 with
  | none =>
    simp only
    have hx2 : u2.locals.lookup x = s.locals.lookup x := (hk trivial).1 ho
    have hx1 : u1.locals.lookup x = some (.val (.word c)) := by
      rw [(hk1 trivial).1 ho]; exact upd_self _ _ _
    have hu : setVarHOLFinite x (.val (.word c)) u2 = u1 := by
      rw [h2]
      simp only [setVarHOLFinite]
      congr 1
      apply HolFiniteMapExact.ext; funext z
      by_cases hz : z = x
      · subst hz; rw [upd_self, hx1]
      · rw [upd_at (Ne.symm hz)]; exact (h3 trivial).1.off z hz
    rw [E_decC, hu, hx2]
    exact rout_refl _
  | some r =>
    simp only
    refine ⟨rfl, h2, fun hn => ?_⟩
    apply HolFiniteMapExact.ext; funext z
    by_cases hz : z = x
    · subst hz; simp only [resVar_self]; exact (hk hn).1 ho
    · simp only [resVar_at (Ne.symm hz)]; exact (h3 hn).1.off z hz

/-- **Split** the scope where the variable is dead. -/
theorem split_sim (x : MlS) (c : BitVec 64) (a : ProgHOL 64) {b : ProgHOL 64} (hd : dk x b ≠ .dep) :
    Sim0 (decC x c (.seq a b)) (.seq (decC x c a) (decC x c b)) := by
  intro σ s
  rw [E_decC, evaluateHOLFiniteState_eq_evaluate_def s (.seq (decC x c a) (decC x c b)),
    evaluateHOLFiniteState_eq_evaluate_def (setVarHOLFinite x (.val (.word c)) s) (.seq a b)]
  dsimp only
  rw [E_decC s x c a]
  have hk1 := kp (σ := σ) x s.clock a (setVarHOLFinite x (.val (.word c)) s) (Nat.le_refl _)
  generalize hA : evaluateHOLFiniteState (setVarHOLFinite x (.val (.word c)) s) a = A at hk1 ⊢
  obtain ⟨r, u⟩ := A
  cases r with
  | some r => exact rout_refl _
  | none =>
    simp only
    rw [E_decC]
    have hsh : ShOne (u.locals.lookup x) :=
      (hk1 trivial).2 ⟨_, upd_self _ _ _, shape_val _⟩
    obtain ⟨w0, hw0, hsw⟩ := hsh
    have hf := fl (σ := σ) x u.clock b hd u (u.locals.update (x, .val (.word c))) (Nat.le_refl _)
      (fun y hy => upd_at (Ne.symm hy) _ _) (Or.inl (by
        rw [upd_self, hw0]; show shapeOfHOLExact w0 = shapeOfHOLExact (.val (.word c)); rw [hsw, shape_val]))
    have e : setVarHOLFinite x (.val (.word c))
        { u with locals := HolFiniteMapExact.resVarEq u.locals (x, s.locals.lookup x) } =
        { u with locals := u.locals.update (x, .val (.word c)) } := by
      simp only [setVarHOLFinite]
      congr 1
      apply HolFiniteMapExact.ext; funext z
      by_cases hz : z = x
      · subst hz; rw [upd_self, upd_self]
      · rw [upd_at (Ne.symm hz), upd_at (Ne.symm hz), resVar_at (Ne.symm hz)]
    rw [e]
    simp only [resVar_self]
    generalize evaluateHOLFiniteState u b = W1 at hf ⊢
    generalize evaluateHOLFiniteState { u with locals := u.locals.update (x, .val (.word c)) } b = W2 at hf ⊢
    obtain ⟨r1, w1⟩ := W1
    obtain ⟨r2, w2⟩ := W2
    obtain ⟨h1, h2, h3, -⟩ := hf
    simp only at h1 h2 h3
    subst h1
    refine ⟨rfl, ?_, fun hn => ?_⟩
    · simp only; rw [h2]
    · simp only
      exact resVar_eq_of_off (h3 hn).1.off _

/-- Into both branches of an `if` whose condition does not read the variable. -/
theorem ite_eqE (x : MlS) (c : BitVec 64) {e : ExpHOL 64} (a b : ProgHOL 64) (he : ev x e = false) :
    EqE (decC x c (.ite e a b)) (.ite e (decC x c a) (decC x c b)) := by
  intro σ s
  rw [E_decC, evaluateHOLFiniteState_eq_evaluate_def s (.ite e (decC x c a) (decC x c b)),
    evaluateHOLFiniteState_eq_evaluate_def (setVarHOLFinite x (.val (.word c)) s) (.ite e a b)]
  dsimp only
  have hev := eval_offx s (s.locals.update (x, .val (.word c))) x
    (fun y hy => upd_at (Ne.symm hy) _ _) e he
  simp only [setVarHOLFinite] at hev ⊢
  erw [hev]
  rcases hcv : (@evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e) with
    _ | ⟨⟨⟨w⟩⟩ | _ | ⟨_, _⟩⟩ <;> simp only [hcv]
  all_goals try (rw [resVar_upd_self])
  by_cases hw : w = 0
  · simp only [hw, ite_true]; rw [E_decC]; rfl
  · simp only [hw, ite_false]; rw [E_decC]; rfl

theorem upd_lookup (L : HolFiniteMapExact MlS (ValueHOL 64)) (k z : MlS) (v : ValueHOL 64) :
    (L.update (k, v)).lookup z = if k = z then some v else L.lookup z := by
  simp only [HolFiniteMapExact.lookup_update, FUPDATE]
  by_cases h : k = z <;> simp [h]

theorem resVar_lookup (L : HolFiniteMapExact MlS (ValueHOL 64)) (k z : MlS) (o : Option (ValueHOL 64)) :
    (HolFiniteMapExact.resVarEq L (k, o)).lookup z = if z = k then o else L.lookup z := by
  cases o <;> simp [HolFiniteMapExact.resVarEq, HolFiniteMapExact.lookup_eraseEq,
    HolFiniteMapExact.lookup_updateEq, FDOMSUB_HOL, FUPDATE_HOL]

/-- Through another declaration. -/
theorem dec_eqE (x : MlS) (c : BitVec 64) {y : MlS} (sh : ShapeHOL) {e : ExpHOL 64} (b : ProgHOL 64)
    (hy : y ≠ x) (he : ev x e = false) :
    EqE (decC x c (.dec y sh e b)) (.dec y sh e (decC x c b)) := by
  intro σ s
  rw [E_decC, evaluateHOLFiniteState_eq_evaluate_def s (.dec y sh e (decC x c b)),
    evaluateHOLFiniteState_eq_evaluate_def (setVarHOLFinite x (.val (.word c)) s) (.dec y sh e b)]
  dsimp only
  have hev := eval_offx s (s.locals.update (x, .val (.word c))) x
    (fun y hy => upd_at (Ne.symm hy) _ _) e he
  simp only [setVarHOLFinite] at hev ⊢
  erw [hev]
  cases hcv : (@evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e) with
  | none => simp only; rw [resVar_upd_self]
  | some v =>
    simp only
    by_cases hsv : shapeEqHOL sh (shapeOfHOLExact v) = true
    · simp only [hsv, ite_true]
      rw [E_decC]
      simp only [setVarHOLFinite]
      have hc : (s.locals.update (x, .val (.word c))).update (y, v) =
          (s.locals.update (y, v)).update (x, .val (.word c)) := by
        apply HolFiniteMapExact.ext; funext z
        simp only [upd_lookup]
        by_cases hzx : x = z <;> by_cases hzy : y = z <;> simp_all
      rw [hc, upd_at hy, upd_at (Ne.symm hy)]
      generalize evaluateHOLFiniteState { s with locals := (s.locals.update (y, v)).update (x, .val (.word c)) } b = W
      obtain ⟨r, w⟩ := W
      simp only
      congr 2
      apply HolFiniteMapExact.ext; funext z
      simp only [resVar_lookup]
      by_cases hzx : z = x <;> by_cases hzy : z = y <;> simp_all
    · have hf : shapeEqHOL sh (shapeOfHOLExact v) = false := by simpa using hsv
      simp only [hf, Bool.false_eq_true, ite_false]; rw [resVar_upd_self]

/-! ## `push` -/

theorem dk_ofL (x : MlS) : ∀ l : List (ProgHOL 64), dk x (ofL l) = dkL x l
  | [] => rfl
  | [a] => by
    show dk x a = dkL x [a]
    simp only [dkL]
    cases dk x a <;> rfl
  | a :: b :: l => by
    show (dk x a).seq (dk x (ofL (b :: l))) = dkL x (a :: b :: l)
    rw [dk_ofL x (b :: l)]
    simp only [dkL]
    cases dk x a <;> rfl

section
variable (x : MlS) (c : BitVec 64)

theorem push1_sim (n : Nat) (ih : ∀ p, Sim0 (decC x c p) (push n x c p)) :
    ∀ a, Sim0 (decC x c a) (push1 n x c a) := by
  intro a
  cases a with
  | ite e a b =>
    unfold push1
    split
    · exact sim0_refl _
    · rename_i he
      exact sim0_trans (sim0_of_eqE (ite_eqE x c a b (by simpa using he))) (sim0_ite e (ih a) (ih b))
  | dec y sh e b =>
    unfold push1
    split
    · rename_i h
      exact sim0_trans (sim0_of_eqE (dec_eqE x c sh b h.1 h.2)) (sim0_dec y sh e (ih b))
    · exact sim0_refl _
  | _ => unfold push1; exact sim0_refl _

theorem pushA_sim (n : Nat) (ih : ∀ p, Sim0 (decC x c p) (push n x c p)) :
    ∀ (l acc : List (ProgHOL 64)), Sim0 (decC x c (ofL (acc.reverse ++ l))) (ofL (pushA n x c acc l))
  | [], [] => by
    unfold pushA
    exact drop_sim x c (p := .skip) rfl
  | [], a :: acc => by
    unfold pushA
    simp only [List.append_nil]
    exact sim0_refl _
  | a :: l, [] => by
    unfold pushA
    split
    · split
      · have := pushA_sim n ih l [a]
        simpa using this
      · rename_i _ hd
        refine sim0_trans (sim0_dec x .one _ (sim0_of_eqE (ofL_cons a l))) ?_
        refine sim0_trans (split_sim x c a (b := ofL l) (by rw [dk_ofL]; exact hd)) ?_
        refine sim0_trans (sim0_seq (push1_sim x c n ih a) (by simpa using pushA_sim n ih l [])) ?_
        exact sim0_of_eqE (eqE_symm (ofL_cons _ _))
    · rename_i ho
      refine sim0_trans (sim0_dec x .one _ (sim0_of_eqE (ofL_cons a l))) ?_
      refine sim0_trans (move_sim x c (ofL l) (by simpa using ho)) ?_
      refine sim0_trans (sim0_seq (sim0_refl a) (by simpa using pushA_sim n ih l [])) ?_
      exact sim0_of_eqE (eqE_symm (ofL_cons _ _))
  | a :: l, b :: acc => by
    unfold pushA
    split
    · have := pushA_sim n ih l (a :: b :: acc)
      simpa using this
    · rename_i hd
      have e : (b :: acc).reverse ++ a :: l = (a :: b :: acc).reverse ++ l := by simp
      rw [e]
      refine sim0_trans (sim0_dec x .one _ (sim0_of_eqE (ofL_append _ l))) ?_
      refine sim0_trans (split_sim x c _ (b := ofL l) (by rw [dk_ofL]; exact hd)) ?_
      refine sim0_trans (sim0_seq (sim0_refl _) (by simpa using pushA_sim n ih l [])) ?_
      exact sim0_of_eqE (eqE_symm (ofL_cons _ _))

theorem push_sim : ∀ n p, Sim0 (decC x c p) (push n x c p)
  | 0, p => by unfold push; exact sim0_refl _
  | n + 1, p => by
    unfold push
    split
    · refine sim0_trans (sim0_dec x .one _ (sim0_of_eqE (eqE_symm (ofL_toL p)))) ?_
      have h := pushA_sim x c n (push_sim n) (toL p) []
      simp only [List.reverse_nil, List.nil_append] at h
      exact h
    · rename_i ho
      exact drop_sim x c (by simpa using ho)

end

/-! ## The narrowed program: a relation between programs -/

/-- `q` is `p` with narrowed sub-programs. -/
inductive NRel : ProgHOL 64 → ProgHOL 64 → Prop
  | leaf (p) : Leaf p → NRel p p
  | dec (n sh e) {b b'} : NRel b b' → NRel (.dec n sh e b) (.dec n sh e b')
  | seq {a a' b b'} : NRel a a' → NRel b b' → NRel (.seq a b) (.seq a' b')
  | ite (c) {a a' b b'} : NRel a a' → NRel b b' → NRel (.ite c a b) (.ite c a' b')
  | while (c) {b b'} : NRel b b' → NRel (.while c b) (.while c b')
  | call0 (f args) : NRel (.call none f args) (.call none f args)
  | call1 (r f args) : NRel (.call (some (r, none)) f args) (.call (some (r, none)) f args)
  | call2 (r eid v) {h h'} (f args) : NRel h h' →
      NRel (.call (some (r, some (eid, v, h))) f args) (.call (some (r, some (eid, v, h'))) f args)
  | decCall (n sh f args) {k k'} : NRel k k' → NRel (.decCall n sh f args k) (.decCall n sh f args k')
  | post {p q r} : NRel p q → Sim0 q r → NRel p r

theorem nrel_narrowT : ∀ p : ProgHOL 64, NRel p (narrowT p)
  | .dec x sh e b => by
    cases sh with
    | one =>
      cases e with
      | const c =>
        exact .post (.dec x .one (.const c) (nrel_narrowT b)) (push_sim x c narrowFuel (narrowT b))
      | _ => exact .dec _ _ _ (nrel_narrowT b)
    | _ => exact .dec _ _ _ (nrel_narrowT b)
  | .seq a b => .seq (nrel_narrowT a) (nrel_narrowT b)
  | .ite c a b => .post (.ite c (nrel_narrowT a) (nrel_narrowT b)) (sim0_of_eqE (flatIte_eqE c _ _))
  | .while c b => .while c (nrel_narrowT b)
  | .call none f args => .call0 f args
  | .call (some (r, none)) f args => .call1 r f args
  | .call (some (r, some (eid, v, h))) f args => .call2 r eid v f args (nrel_narrowT h)
  | .decCall n sh f args k => .decCall n sh f args (nrel_narrowT k)
  | .skip => .leaf _ trivial
  | .assign .. => .leaf _ trivial
  | .primitive .. => .leaf _ trivial
  | .store .. => .leaf _ trivial
  | .store32 .. => .leaf _ trivial
  | .storeByte .. => .leaf _ trivial
  | .break => .leaf _ trivial
  | .continue => .leaf _ trivial
  | .extCall .. => .leaf _ trivial
  | .raise .. => .leaf _ trivial
  | .return .. => .leaf _ trivial
  | .shMemLoad .. => .leaf _ trivial
  | .shMemStore .. => .leaf _ trivial
  | .tick => .leaf _ trivial
  | .annot .. => .leaf _ trivial

/-! ## Code tables -/

/-- `c'` is the narrowed table of `c`. -/
def NCode (c c' : DCode) : Prop := ∀ f, c'.lookup f = (c.lookup f).map narrowE

theorem narrowEntries_lookup (l : List (MlS × (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))) (f : MlS) :
    (narrowEntries l).lookup f = (l.lookup f).map narrowE := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    obtain ⟨k, e⟩ := p
    by_cases hk : f = k
    · subst hk; simp [narrowEntries, List.lookup]
    · have hb : (f == k) = false := by simp [hk]
      simp only [narrowEntries, List.map, List.lookup, hb] at ih ⊢
      exact ih

theorem nlookupExact_rel {c c' : DCode} (hR : NCode c c') (f : MlS) (vals : List (ValueHOL 64)) :
    lookupCodeHOLExact c'.lookup f vals =
      (lookupCodeHOLExact c.lookup f vals).map (fun x => (narrowT x.1, x.2.1, x.2.2)) := by
  unfold lookupCodeHOLExact
  rw [hR f]
  cases c.lookup f with
  | none => rfl
  | some e =>
    obtain ⟨ps, b, r⟩ := e
    simp only [Option.map, narrowE]
    split <;> rfl

theorem nlookup_rel {c c' : DCode} (hR : NCode c c') (f : MlS) (vals : List (ValueHOL 64)) :
    lookupCodeHOLFinite c'.lookup f vals =
      (lookupCodeHOLFinite c.lookup f vals).map (fun x => (narrowT x.1, x.2.1, x.2.2)) := by
  have he := nlookupExact_rel hR f vals
  cases h : lookupCodeHOLFinite c.lookup f vals with
  | none =>
    rw [(lookupCodeHOLFinite_eq_none_iff _ _ _).1 h] at he
    exact (lookupCodeHOLFinite_eq_none_iff _ _ _).2 he
  | some x =>
    obtain ⟨b, callee, r⟩ := x
    rw [lookupCodeHOLFinite_eq_some _ _ _ _ _ _ h] at he
    cases h' : lookupCodeHOLFinite c'.lookup f vals with
    | none =>
      rw [(lookupCodeHOLFinite_eq_none_iff _ _ _).1 h'] at he; simp at he
    | some y =>
      obtain ⟨b', callee', r'⟩ := y
      rw [lookupCodeHOLFinite_eq_some _ _ _ _ _ _ h'] at he
      simp only [Option.map, Option.some.injEq, Prod.mk.injEq] at he
      obtain ⟨rfl, hc, rfl⟩ := he
      simp only [Option.map, HolFiniteMapExact.ext hc]

/-! ## The simulation -/

section
variable {σ : Type}

/-- The narrowed run's output `B` against the original run's output `A` (code table `sc`). -/
def NOut (c' : DCode) (sc : DCode) (A B : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ) : Prop :=
  B.1 = A.1 ∧ B.2 = { A.2 with code := c', locals := B.2.locals } ∧ A.2.code = sc ∧
    (Normalish A.1 → B.2.locals = A.2.locals)

def NSimN (n : Nat) (p q : ProgHOL 64) : Prop :=
  ∀ (s : PanSemStateFiniteExact 64 σ) (c' : DCode), s.clock ≤ n → NCode s.code c' →
    NOut c' s.code (evaluateHOLFiniteState s p) (evaluateHOLFiniteState { s with code := c' } q)

theorem nout_eq {c' sc : DCode} {A B : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ}
    (h : NOut c' sc A B) (hn : Normalish A.1) : B = (A.1, { A.2 with code := c' }) := by
  obtain ⟨r, u⟩ := A
  obtain ⟨r', u'⟩ := B
  obtain ⟨h1, h2, -, h4⟩ := h
  simp only at h1 h2 h4 hn
  subst h1
  rw [h2, h4 hn]

theorem nout_same {c' : DCode} (r : Option (PanSemResultExact 64)) (u : PanSemStateFiniteExact 64 σ) (sc : DCode)
    (hc : u.code = sc) : NOut c' sc (r, u) (r, { u with code := c' }) :=
  ⟨rfl, rfl, hc, fun _ => rfl⟩

theorem nout_ab {c' : DCode} (r : PanSemResultExact 64) (u u' : PanSemStateFiniteExact 64 σ) (sc : DCode)
    (hc : u.code = sc) (h : u' = { u with code := c', locals := u'.locals }) (hn : ¬ Normalish (some r)) :
    NOut c' sc (some r, u) (some r, u') :=
  ⟨rfl, h, hc, fun h' => absurd h' hn⟩

theorem nseq_sim {n : Nat} {a a' b b' : ProgHOL 64} (ha : NSimN (σ := σ) n a a') (hb : NSimN (σ := σ) n b b') :
    NSimN (σ := σ) n (.seq a b) (.seq a' b') := by
  intro s c' hn hc
  rw [evaluateHOLFiniteState_eq_evaluate_def s (.seq a b),
    evaluateHOLFiniteState_eq_evaluate_def { s with code := c' } (.seq a' b')]
  dsimp only
  have h := ha s c' hn hc
  generalize hA : evaluateHOLFiniteState s a = A at h ⊢
  generalize evaluateHOLFiniteState { s with code := c' } a' = B at h ⊢
  obtain ⟨r, u⟩ := A
  cases r with
  | none =>
    rw [nout_eq h trivial]
    have hu : u.code = s.code := h.2.2.1
    have := hb u c' (Nat.le_trans (clock_of hA) hn) (by rw [hu]; exact hc)
    rw [hu] at this
    exact this
  | some r =>
    obtain ⟨r', u'⟩ := B
    obtain ⟨h1, h2, h3, h4⟩ := h
    simp only at h1 h2 h3 h4
    subst h1
    exact ⟨rfl, h2, h3, h4⟩

theorem ndec_sim {n : Nat} (x : MlS) (sh : ShapeHOL) (e : ExpHOL 64) {b b' : ProgHOL 64}
    (hb : NSimN (σ := σ) n b b') : NSimN (σ := σ) n (.dec x sh e b) (.dec x sh e b') := by
  intro s c' hn hc
  rw [evaluateHOLFiniteState_eq_evaluate_def { s with code := c' } (.dec x sh e b'),
    evaluateHOLFiniteState_eq_evaluate_def s (.dec x sh e b)]
  dsimp only
  simp only [wc_eval]
  cases hv : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e with
  | none => exact nout_ab _ s _ _ rfl rfl (by simp [Normalish])
  | some v =>
    simp only
    by_cases hs : shapeEqHOL sh (shapeOfHOLExact v) = true
    · simp only [hs, ite_true]
      have h := hb (setVarHOLFinite x v s) c' hn hc
      rw [wc_setVar s c' x v]
      generalize evaluateHOLFiniteState (setVarHOLFinite x v s) b = A at h ⊢
      generalize evaluateHOLFiniteState { setVarHOLFinite x v s with code := c' } b' = B at h ⊢
      obtain ⟨r, u⟩ := A
      obtain ⟨r', u'⟩ := B
      obtain ⟨h1, h2, h3, h4⟩ := h
      simp only at h1 h2 h3 h4
      subst h1
      refine ⟨rfl, ?_, h3, fun hn' => ?_⟩
      · simp only; rw [h2]
      · simp only; rw [h4 hn']
    · simp only [hs]; exact nout_ab _ s _ _ rfl rfl (by simp [Normalish])

theorem nite_sim {n : Nat} (cnd : ExpHOL 64) {a a' b b' : ProgHOL 64} (ha : NSimN (σ := σ) n a a')
    (hb : NSimN (σ := σ) n b b') : NSimN (σ := σ) n (.ite cnd a b) (.ite cnd a' b') := by
  intro s c' hn hc
  rw [evaluateHOLFiniteState_eq_evaluate_def { s with code := c' } (.ite cnd a' b'),
    evaluateHOLFiniteState_eq_evaluate_def s (.ite cnd a b)]
  dsimp only
  simp only [wc_eval]
  cases hv : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) cnd with
  | none => exact nout_ab _ s _ _ rfl rfl (by simp [Normalish])
  | some v =>
    cases v with
    | rStruct => exact nout_ab _ s _ _ rfl rfl (by simp [Normalish])
    | nStruct => exact nout_ab _ s _ _ rfl rfl (by simp [Normalish])
    | val w =>
      cases w with
      | word w =>
        simp only
        by_cases hw : w = 0
        · simp only [hw, ite_true]; exact hb s c' hn hc
        · simp only [hw, ite_false]; exact ha s c' hn hc

theorem nwhile_sim {n : Nat} (cnd : ExpHOL 64) {b b' : ProgHOL 64} (hb : NSimN (σ := σ) n b b')
    (ih : ∀ m, m < n → NSimN (σ := σ) m (.while cnd b) (.while cnd b')) :
    NSimN (σ := σ) n (.while cnd b) (.while cnd b') := by
  intro s c' hn hc
  rw [evaluateHOLFiniteState_eq_evaluate_def { s with code := c' } (.while cnd b'),
    evaluateHOLFiniteState_eq_evaluate_def s (.while cnd b)]
  dsimp only
  simp only [wc_evalF]
  cases hv : @evalHOLFinite 64 σ _ s (fun a => Classical.propDecidable (s.memaddrs a)) cnd with
  | none => exact nout_ab _ s _ _ rfl rfl (by simp [Normalish])
  | some v =>
    cases v with
    | rStruct => exact nout_ab _ s _ _ rfl rfl (by simp [Normalish])
    | nStruct => exact nout_ab _ s _ _ rfl rfl (by simp [Normalish])
    | val w =>
      cases w with
      | word w =>
        simp only
        by_cases hw : w ≠ 0
        · rw [ite_eq_left hw, ite_eq_left hw]
          by_cases hk : s.clock = 0
          · rw [ite_eq_left (show ({ s with code := c' } : PanSemStateFiniteExact 64 σ).clock = 0 from hk), ite_eq_left hk]
            exact nout_ab _ _ _ _ rfl rfl (by simp [Normalish])
          rw [ite_eq_right (show ¬ ({ s with code := c' } : PanSemStateFiniteExact 64 σ).clock = 0 from hk), ite_eq_right hk,
            wc_decClock s c']
          have hdn : (decClockHOLFinite s).clock ≤ n := by
            show s.clock - 1 ≤ n; omega
          have h := hb (decClockHOLFinite s) c' hdn hc
          generalize hB : evaluateHOLFiniteState (decClockHOLFinite s) b = A at h ⊢
          generalize evaluateHOLFiniteState { decClockHOLFinite s with code := c' } b' = B at h ⊢
          obtain ⟨r, u⟩ := A
          have hu : u.clock < n := by
            have := clock_of hB
            have e : (decClockHOLFinite s).clock = s.clock - 1 := rfl
            omega
          have hcode : u.code = s.code := h.2.2.1
          have hnext : Normalish r → NOut c' s.code (evaluateHOLFiniteState u (.while cnd b))
              (evaluateHOLFiniteState { u with code := c' } (.while cnd b')) := by
            intro hr
            have := ih u.clock hu u c' (Nat.le_refl _) (by rw [hcode]; exact hc)
            rw [hcode] at this; exact this
          cases r with
          | none => rw [nout_eq h trivial]; exact hnext trivial
          | some r =>
            cases r with
            | «continue» => rw [nout_eq h trivial]; exact hnext trivial
            | «break» => rw [nout_eq h trivial]; exact nout_same none u _ hcode
            | _ =>
              obtain ⟨r', u'⟩ := B
              obtain ⟨h1, h2, h3, h4⟩ := h
              simp only at h1 h2 h3 h4
              subst h1
              exact ⟨rfl, h2, h3, h4⟩
        · rw [ite_eq_right hw, ite_eq_right hw]; exact nout_same none s _ rfl

/-- Call information related by `NRel` on the handler. -/
def NInfoRel : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64)) →
    Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64)) → Prop
  | none, none => True
  | some (r, none), some (r', none) => r = r'
  | some (r, some (e, v, h)), some (r', some (e', v', h')) => r = r' ∧ e = e' ∧ v = v' ∧ NRel h h'
  | _, _ => False

theorem ncall_sim {n : Nat} {info info' : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64))}
    (hI : NInfoRel info info') (f : MlS) (args : List (ExpHOL 64))
    (ih : ∀ m, m < n → ∀ p q, NRel p q → NSimN (σ := σ) m p q) :
    NSimN (σ := σ) n (.call info f args) (.call info' f args) := by
  intro s c' hn hc
  rw [evaluateHOLFiniteState_eq_evaluate_def { s with code := c' } (.call info' f args),
    evaluateHOLFiniteState_eq_evaluate_def s (.call info f args)]
  dsimp only
  simp only [wc_evalListF]
  cases hargs : @evalListHOLFinite 64 σ _ s (fun a => Classical.propDecidable (s.memaddrs a)) args with
  | none => exact nout_ab _ s _ _ rfl rfl (by simp [Normalish])
  | some vals =>
    simp only
    rw [nlookup_rel hc f vals]
    cases hl : lookupCodeHOLFinite s.code.lookup f vals with
    | none => exact nout_ab _ s _ _ rfl rfl (by simp [Normalish])
    | some x =>
      obtain ⟨b, callee, r⟩ := x
      simp only [Option.map]
      by_cases hk : s.clock = 0
      · rw [ite_eq_left (show ({ s with code := c' } : PanSemStateFiniteExact 64 σ).clock = 0 from hk), ite_eq_left hk]
        exact nout_ab _ _ _ _ rfl rfl (by simp [Normalish])
      rw [ite_eq_right (show ¬ ({ s with code := c' } : PanSemStateFiniteExact 64 σ).clock = 0 from hk), ite_eq_right hk,
        wc_entry s c' callee]
      have hcl : (callEntryStateHOLFinite s callee).clock ≤ s.clock - 1 := Nat.le_refl _
      have h := ih (s.clock - 1) (by omega) b (narrowT b) (nrel_narrowT b) (callEntryStateHOLFinite s callee) c' hcl hc
      generalize hB : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) b = A at h ⊢
      generalize evaluateHOLFiniteState { callEntryStateHOLFinite s callee with code := c' } (narrowT b) = B at h ⊢
      obtain ⟨r1, u⟩ := A
      obtain ⟨r1', u'⟩ := B
      obtain ⟨h1, h2, h3, h4⟩ := h
      simp only at h1 h2 h3 h4
      subst h1
      have hu : u.clock ≤ s.clock - 1 := clock_of hB
      have hcode : u.code = s.code := h3
      cases r1' with
      | none => exact nout_ab _ _ _ _ hcode h2 (by simp [Normalish])
      | some r1 =>
        cases r1 with
        | error => exact nout_ab _ _ _ _ hcode (by simp only [emptyLocalsHOLFinite]; rw [h2]) (by simp [Normalish])
        | timeOut => exact nout_ab _ _ _ _ hcode (by simp only [emptyLocalsHOLFinite]; rw [h2]) (by simp [Normalish])
        | «break» => exact nout_ab _ _ _ _ hcode h2 (by simp [Normalish])
        | «continue» => exact nout_ab _ _ _ _ hcode h2 (by simp [Normalish])
        | finalFfi ev => exact nout_ab _ _ _ _ hcode (by simp only [emptyLocalsHOLFinite]; rw [h2]) (by simp [Normalish])
        | returned v =>
          simp only
          by_cases hsh : shapeEqHOL (shapeOfHOLExact v) r = true
          · simp only [hsh, ite_true]
            rcases info with _ | ⟨ret, hd⟩ <;> rcases info' with _ | ⟨ret', hd'⟩ <;>
              simp only [NInfoRel] at hI
            · exact nout_ab _ _ _ _ hcode (by simp only [emptyLocalsHOLFinite]; rw [h2]) (by simp [Normalish])
            · have hr : ret = ret' := by
                rcases hd with _ | ⟨_, _, _⟩ <;> rcases hd' with _ | ⟨_, _, _⟩ <;> simp only at hI <;>
                  first | exact hI | exact hI.1
              subst hr
              rcases ret with _ | ⟨k, nm⟩
              · refine ⟨rfl, ?_, hcode, fun _ => rfl⟩
                simp only; rw [h2]
              · simp only [wc_isValid]
                by_cases hvv : isValidValueHOLExact s.toExact k nm v = true
                · simp only [hvv, ite_true]
                  have e : setKvarHOLFinite k nm v { u' with locals := s.locals } =
                      { setKvarHOLFinite k nm v { u with locals := s.locals } with code := c' } := by
                    rw [h2]; cases k <;> rfl
                  rw [e]
                  exact nout_same none _ _ ((code_setKvar _ _ _ _).trans hcode)
                · simp only [hvv]; exact nout_ab _ _ _ _ hcode h2 (by simp [Normalish])
          · simp only [hsh]; exact nout_ab _ _ _ _ hcode h2 (by simp [Normalish])
        | exception eid v =>
          simp only
          rcases info with _ | ⟨ret, hd⟩ <;> rcases info' with _ | ⟨ret', hd'⟩ <;>
            simp only [NInfoRel] at hI
          · exact nout_ab _ _ _ _ hcode (by simp only [emptyLocalsHOLFinite]; rw [h2]) (by simp [Normalish])
          · rcases hd with _ | ⟨hid, hv, hp⟩ <;> rcases hd' with _ | ⟨hid', hv', hp'⟩ <;> simp only at hI
            · exact nout_ab _ _ _ _ hcode (by simp only [emptyLocalsHOLFinite]; rw [h2]) (by simp [Normalish])
            · obtain ⟨rfl, rfl, rfl, hR⟩ := hI
              simp only
              by_cases hei : eid = hid
              · simp only [hei, ite_true]
                rw [show ({ s with code := c' } : PanSemStateFiniteExact 64 σ).eshapes = s.eshapes from rfl]
                cases hes : s.eshapes.lookup hid with
                | none => exact nout_ab _ _ _ _ hcode h2 (by simp [Normalish])
                | some shp =>
                  simp only [wc_isValid]
                  by_cases hcond : (shapeEqHOL (shapeOfHOLExact v) shp &&
                      isValidValueHOLExact s.toExact .local hv v) = true
                  · simp only [hcond, ite_true]
                    have hst : (setVarHOLFinite hv v { u with locals := s.locals }).clock ≤ s.clock - 1 := hu
                    have hsc : (setVarHOLFinite hv v { u with locals := s.locals }).code = s.code := hcode
                    have e : setVarHOLFinite hv v { u' with locals := s.locals } =
                        { setVarHOLFinite hv v { u with locals := s.locals } with code := c' } := by
                      rw [h2]; rfl
                    rw [e]
                    have := ih (s.clock - 1) (by omega) hp hp' hR (setVarHOLFinite hv v { u with locals := s.locals })
                      c' hst (by rw [hsc]; exact hc)
                    rw [hsc] at this
                    exact this
                  · simp only [hcond]; exact nout_ab _ _ _ _ hcode h2 (by simp [Normalish])
              · simp only [hei, ite_false]
                exact nout_ab _ _ _ _ hcode (by simp only [emptyLocalsHOLFinite]; rw [h2]) (by simp [Normalish])

theorem ndecCall_sim {n : Nat} (x : MlS) (sh : ShapeHOL) (f : MlS) (args : List (ExpHOL 64)) {k k' : ProgHOL 64}
    (hk : NSimN (σ := σ) n k k') (ih : ∀ m, m < n → ∀ p q, NRel p q → NSimN (σ := σ) m p q) :
    NSimN (σ := σ) n (.decCall x sh f args k) (.decCall x sh f args k') := by
  intro s c' hn hc
  rw [evaluateHOLFiniteState_eq_evaluate_def { s with code := c' } (.decCall x sh f args k'),
    evaluateHOLFiniteState_eq_evaluate_def s (.decCall x sh f args k)]
  dsimp only
  simp only [wc_evalListF]
  cases hargs : @evalListHOLFinite 64 σ _ s (fun a => Classical.propDecidable (s.memaddrs a)) args with
  | none => exact nout_ab _ s _ _ rfl rfl (by simp [Normalish])
  | some vals =>
    simp only
    rw [nlookup_rel hc f vals]
    cases hl : lookupCodeHOLFinite s.code.lookup f vals with
    | none => exact nout_ab _ s _ _ rfl rfl (by simp [Normalish])
    | some y =>
      obtain ⟨b, callee, r⟩ := y
      simp only [Option.map]
      by_cases hck : s.clock = 0
      · rw [ite_eq_left (show ({ s with code := c' } : PanSemStateFiniteExact 64 σ).clock = 0 from hck), ite_eq_left hck]
        exact nout_ab _ _ _ _ rfl rfl (by simp [Normalish])
      rw [ite_eq_right (show ¬ ({ s with code := c' } : PanSemStateFiniteExact 64 σ).clock = 0 from hck), ite_eq_right hck,
        wc_entry s c' callee]
      have hcl : (callEntryStateHOLFinite s callee).clock ≤ s.clock - 1 := Nat.le_refl _
      have h := ih (s.clock - 1) (by omega) b (narrowT b) (nrel_narrowT b) (callEntryStateHOLFinite s callee) c' hcl hc
      generalize hB : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) b = A at h ⊢
      generalize evaluateHOLFiniteState { callEntryStateHOLFinite s callee with code := c' } (narrowT b) = B at h ⊢
      obtain ⟨r1, u⟩ := A
      obtain ⟨r1', u'⟩ := B
      obtain ⟨h1, h2, h3, h4⟩ := h
      simp only at h1 h2 h3 h4
      subst h1
      have hu : u.clock ≤ s.clock - 1 := clock_of hB
      have hcode : u.code = s.code := h3
      cases r1' with
      | none => exact nout_ab _ _ _ _ hcode h2 (by simp [Normalish])
      | some r1 =>
        cases r1 with
        | error => exact nout_ab _ _ _ _ hcode (by simp only [emptyLocalsHOLFinite]; rw [h2]) (by simp [Normalish])
        | timeOut => exact nout_ab _ _ _ _ hcode (by simp only [emptyLocalsHOLFinite]; rw [h2]) (by simp [Normalish])
        | «break» => exact nout_ab _ _ _ _ hcode h2 (by simp [Normalish])
        | «continue» => exact nout_ab _ _ _ _ hcode h2 (by simp [Normalish])
        | finalFfi ev => exact nout_ab _ _ _ _ hcode (by simp only [emptyLocalsHOLFinite]; rw [h2]) (by simp [Normalish])
        | exception eid v =>
          exact nout_ab _ _ _ _ hcode (by simp only [emptyLocalsHOLFinite]; rw [h2]) (by simp [Normalish])
        | returned v =>
          simp only
          by_cases hsh : (shapeEqHOL (shapeOfHOLExact v) sh && shapeEqHOL (shapeOfHOLExact v) r) = true
          · simp only [hsh, ite_true]
            have hst : (setVarHOLFinite x v { u with locals := s.locals }).clock ≤ n := by
              show u.clock ≤ n; omega
            have hsc : (setVarHOLFinite x v { u with locals := s.locals }).code = s.code := hcode
            have e : setVarHOLFinite x v { u' with locals := s.locals } =
                { setVarHOLFinite x v { u with locals := s.locals } with code := c' } := by
              rw [h2]; rfl
            rw [e]
            have h' := hk (setVarHOLFinite x v { u with locals := s.locals }) c' hst (by rw [hsc]; exact hc)
            generalize evaluateHOLFiniteState (setVarHOLFinite x v { u with locals := s.locals }) k = A at h' ⊢
            generalize evaluateHOLFiniteState { setVarHOLFinite x v { u with locals := s.locals } with code := c' } k' = B
              at h' ⊢
            obtain ⟨r2, w⟩ := A
            obtain ⟨r2', w'⟩ := B
            obtain ⟨g1, g2, g3, g4⟩ := h'
            simp only at g1 g2 g3 g4
            subst g1
            refine ⟨rfl, ?_, g3.trans hsc, fun hn' => ?_⟩
            · simp only; rw [g2]
            · simp only; rw [g4 hn']
          · simp only [hsh]; exact nout_ab _ _ _ _ hcode h2 (by simp [Normalish])

theorem npost_sim {n : Nat} {p q r : ProgHOL 64} (h : NSimN (σ := σ) n p q) (h0 : Sim0 q r) :
    NSimN (σ := σ) n p r := by
  intro s c' hn hc
  obtain ⟨h1, h2, h3, h4⟩ := h s c' hn hc
  obtain ⟨g1, g2, g4⟩ := h0 σ { s with code := c' }
  refine ⟨g1.trans h1, ?_, h3, fun hn' => (g4 (h1 ▸ hn')).trans (h4 hn')⟩
  rw [g2, h2]

theorem nleaf_sim {n : Nat} (p : ProgHOL 64) (hp : Leaf p) : NSimN (σ := σ) n p p := by
  intro s c' _ _
  obtain ⟨h1, h2⟩ := leaf_sim s c' p hp
  rw [h1]
  exact nout_same _ _ _ h2

theorem nrel_sim : ∀ n (p q : ProgHOL 64), NRel p q → NSimN (σ := σ) n p q := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ihn =>
    intro p q hR
    induction hR with
    | leaf p hp => exact nleaf_sim p hp
    | dec x sh e _ hb => exact ndec_sim x sh e hb
    | seq _ _ ha hb => exact nseq_sim ha hb
    | ite cnd _ _ ha hb => exact nite_sim cnd ha hb
    | «while» cnd hR hb => exact nwhile_sim cnd hb (fun m hm => ihn m hm _ _ (.while cnd hR))
    | call0 f args => exact ncall_sim (info := none) (info' := none) trivial f args ihn
    | call1 r f args => exact ncall_sim (info := some (r, none)) (info' := some (r, none)) rfl f args ihn
    | call2 r eid v f args hR _ =>
      exact ncall_sim (info := some (r, some (eid, v, _))) (info' := some (r, some (eid, v, _)))
        ⟨rfl, rfl, rfl, hR⟩ f args ihn
    | decCall x sh f args _ hk => exact ndecCall_sim x sh f args hk ihn
    | post _ h0 hp => exact npost_sim hp h0

/-- **The narrowed program gives the original program's result**, with the same final state apart
from the code table and the locals. -/
theorem narrowT_sim (s : PanSemStateFiniteExact 64 σ) {c' : DCode} (hc : NCode s.code c') (p : ProgHOL 64) :
    (evaluateHOLFiniteState { s with code := c' } (narrowT p)).1 = (evaluateHOLFiniteState s p).1 ∧
      (evaluateHOLFiniteState { s with code := c' } (narrowT p)).2.ffi = (evaluateHOLFiniteState s p).2.ffi := by
  obtain ⟨h1, h2, -, -⟩ := nrel_sim s.clock p (narrowT p) (nrel_narrowT p) s c' (Nat.le_refl _) hc
  refine ⟨h1, ?_⟩
  rw [h2]

end

end ConPanqueque.Logic
