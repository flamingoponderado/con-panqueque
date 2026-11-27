import ConRon.Bridge.Checker.Canon
import ConRon.Bridge.Checker.Basis
import ConPanqueque.Logic.PlainIntern
import ConPanqueque.T.ReIntern
import ConPanqueque.T.LInternLv

/-!
# The twin's canonical comparison of a constant against itself

`canonExprEq ps ps cs fuel e e` (and the level, rule and constant comparisons) answer `true` and keep the state
when the fuel exceeds the depth of what `e` denotes (`edep`). The `And` pin's comparison (`canonEqList block
pinned`) of a block whose records agree with the pin's handle for handle (`CanonAgree`) is then `true`, the
state the one `canonNames` leaves.
-/

namespace ConPanqueque.T.Ind

set_option autoImplicit false

open ConRon.Arena ConRon.Bridge ConLeche

/-- A level's depth. -/
def ldep : Level → Nat
  | .zero => 0
  | .succ a => ldep a + 1
  | .max a b => max (ldep a) (ldep b) + 1
  | .imax a b => max (ldep a) (ldep b) + 1
  | .param _ => 0

/-- The deepest of a level list. -/
def ldepL : List Level → Nat
  | [] => 0
  | l :: ls => max (ldep l) (ldepL ls)

/-- An expression's depth (levels included). -/
def edep : Expr → Nat
  | .bvar _ => 0
  | .fvar _ t => edep t + 1
  | .sort l => ldep l + 1
  | .const _ ls => ldepL ls + 1
  | .app f a => max (edep f) (edep a) + 1
  | .lam t b => max (edep t) (edep b) + 1
  | .forallE t b => max (edep t) (edep b) + 1
  | .letE t v b => max (edep t) (max (edep v) (edep b)) + 1
  | .lit _ => 0
  | .proj _ _ e => edep e + 1

theorem viewL_run_of_some {h : LIdx} {s : AState} {v : LNodeView}
    (hv : s.store.ls.view h = some v) : viewL h s = .ok (v, s) := by
  simp only [viewL, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, StateT.pure, Except.bind, Except.pure, hv]

theorem viewLs_run_of_some {h : LsIdx} {s : AState} {v : LsNodeView}
    (hv : s.store.lss.view h = some v) : viewLs h s = .ok (v, s) := by
  simp only [viewLs, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get,
    pure, StateT.pure, Except.bind, Except.pure, hv]

theorem lview_of_denote {st : LStore} {i : LIdx} {x : Level} (h : denoteL st i = some x) :
    ∃ v, st.view i = some v := by
  unfold denoteL denoteLAux at h
  cases hv : st.view i with
  | none => rw [hv] at h; simp at h
  | some v => exact ⟨v, rfl⟩

theorem eview_of_denote {st : EStore} {i : EIdx} {x : Expr} (h : denoteE st i = some x) :
    ∃ v, st.view i = some v := by
  unfold denoteE denoteEAux at h
  cases hv : st.view i with
  | none => rw [hv] at h; simp at h
  | some v => exact ⟨v, rfl⟩

theorem bind_ok_l {α β : Type} {m : AM α} {k : α → AM β} {s s1 : AState} {a : α} (h : m s = .ok (a, s1)) :
    (m >>= k) s = k a s1 := by
  show (do let r ← m s; match r with | (a, s) => k a s) = _
  rw [h]; rfl

theorem canonLevelEq_refl (ps cs : List NIdx) (s : AState) (hok : StateOK s) :
    ∀ (fuel : Nat) (u : LIdx) (x : Level), denoteL s.store.ls u = some x → ldep x < fuel →
      canonLevelEq ps ps cs fuel u u s = .ok (true, s) := by
  intro fuel
  induction fuel with
  | zero => intro u x _ h; exact absurd h (Nat.not_lt_zero _)
  | succ fuel ih =>
    intro u x hx hd
    obtain ⟨rk, hrk⟩ := hok.wf
    have hlw : LStoreWF s.store.ls := hrk.lsWF
    obtain ⟨v, hv⟩ := lview_of_denote hx
    have hvr := viewL_run_of_some (s := s) hv
    simp only [ConRon.Arena.canonLevelEq]
    rw [bind_ok_l hvr, bind_ok_l hvr]
    cases v with
    | zero => rfl
    | succ a =>
      obtain ⟨p, rfl, hp⟩ := denoteL_succ_inv hlw hv hx
      simp only [ldep] at hd
      exact ih a p hp (by omega)
    | max a b =>
      obtain ⟨p, q, rfl, hp, hq⟩ := denoteL_max_inv hlw hv hx
      simp only [ldep] at hd
      simp only
      rw [bind_ok_l (ih a p hp (by omega))]
      simp only [ite_true]
      exact ih b q hq (by omega)
    | imax a b =>
      obtain ⟨p, q, rfl, hp, hq⟩ := denoteL_imax_inv hlw hv hx
      simp only [ldep] at hd
      simp only
      rw [bind_ok_l (ih a p hp (by omega))]
      simp only [ite_true]
      exact ih b q hq (by omega)
    | param n =>
      simp only [beq_self_eq_true]; rfl

theorem canonLevelListEq_refl (ps cs : List NIdx) (s : AState) (hok : StateOK s) (fuel : Nat) :
    ∀ (us : List LIdx) (xs : List Level), denoteLList s.store.ls us = some xs → ldepL xs < fuel →
      canonLevelListEq ps ps cs fuel us us s = .ok (true, s)
  | [], _, _, _ => rfl
  | u :: us, xs, hxs, hd => by
    obtain ⟨q, qs, hq, hqs, rfl⟩ := denoteLList_cons hxs
    simp only [ldepL] at hd
    simp only [ConRon.Arena.canonLevelListEq]
    rw [bind_ok_l (canonLevelEq_refl ps cs s hok fuel u q hq (by omega))]
    simp only [ite_true]
    exact canonLevelListEq_refl ps cs s hok fuel us qs hqs (by omega)

theorem lsview_of_denote {st : LsStore} {i : LsIdx} {x : List Level} (h : denoteLs st i = some x) :
    ∃ v, st.view i = some v := by
  unfold denoteLs at h
  cases hv : st.view i with
  | none => rw [hv] at h; simp at h
  | some v => exact ⟨v, rfl⟩

theorem canonLevelsEq_refl (ps cs : List NIdx) (s : AState) (hok : StateOK s) (fuel : Nat) (us : LsIdx)
    (xs : List Level) (hx : denoteLs s.store.lss us = some xs) (hd : ldepL xs < fuel) :
    canonLevelsEq ps ps cs fuel us us s = .ok (true, s) := by
  obtain ⟨v, hv⟩ := lsview_of_denote hx
  have hvr := viewLs_run_of_some (s := s) hv
  simp only [ConRon.Arena.canonLevelsEq]
  rw [bind_ok_l hvr, bind_ok_l hvr]
  exact canonLevelListEq_refl ps cs s hok fuel v xs (denoteLs_view_inv hv hx) hd

theorem canonExprEq_refl (ps cs : List NIdx) (s : AState) (hok : StateOK s) :
    ∀ (fuel : Nat) (e : EIdx) (x : Expr), denoteE s.store e = some x → edep x < fuel →
      canonExprEq ps ps cs fuel e e s = .ok (true, s) := by
  intro fuel
  induction fuel with
  | zero => intro e x _ h; exact absurd h (Nat.not_lt_zero _)
  | succ fuel ih =>
    intro e x hx hd
    have hwf : StoreWF s.store := hok.wf
    obtain ⟨v, hv⟩ := eview_of_denote hx
    have hvr := view_run_of_some (s := s) hv
    simp only [ConRon.Arena.canonExprEq]
    rw [bind_ok_l hvr, bind_ok_l hvr]
    cases v with
    | bvar i => simp only [beq_self_eq_true]; rfl
    | fvar i t =>
      obtain ⟨p, rfl, hp⟩ := denote_fvar_inv hwf hv hx
      simp only [edep] at hd
      simp only [beq_self_eq_true, ite_true]
      exact ih t p hp (by omega)
    | sort u =>
      obtain ⟨l, rfl, hl⟩ := denote_sort_inv hwf hv hx
      simp only [edep] at hd
      exact canonLevelEq_refl ps cs s hok fuel u l hl (by omega)
    | const n us =>
      obtain ⟨nm, ls, rfl, -, hls⟩ := denote_const_inv hwf hv hx
      simp only [edep] at hd
      simp only [beq_self_eq_true, ite_true]
      exact canonLevelsEq_refl ps cs s hok fuel us ls hls (by omega)
    | app f a =>
      obtain ⟨p, q, rfl, hp, hq⟩ := denote_app_inv hwf hv hx
      simp only [edep] at hd
      simp only
      rw [bind_ok_l (ih f p hp (by omega))]
      simp only [ite_true]
      exact ih a q hq (by omega)
    | lam t b =>
      obtain ⟨p, q, rfl, hp, hq⟩ := denote_lam_inv hwf hv hx
      simp only [edep] at hd
      simp only
      rw [bind_ok_l (ih t p hp (by omega))]
      simp only [ite_true]
      exact ih b q hq (by omega)
    | forallE t b =>
      obtain ⟨p, q, rfl, hp, hq⟩ := denote_forallE_inv hwf hv hx
      simp only [edep] at hd
      simp only
      rw [bind_ok_l (ih t p hp (by omega))]
      simp only [ite_true]
      exact ih b q hq (by omega)
    | letE t w b =>
      obtain ⟨p, q, r, rfl, hp, hq, hr⟩ := denote_letE_inv hwf hv hx
      simp only [edep] at hd
      simp only
      rw [bind_ok_l (ih t p hp (by omega))]
      simp only [ite_true]
      rw [bind_ok_l (ih w q hq (by omega))]
      simp only [ite_true]
      exact ih b r hr (by omega)
    | lit l => simp only [beq_self_eq_true]; rfl
    | proj n i sub =>
      obtain ⟨nm, es, rfl, -, hes⟩ := denote_proj_inv hwf hv hx
      simp only [edep] at hd
      simp only [beq_self_eq_true, Bool.and_self, ite_true]
      exact ih sub es hes (by omega)

/-! ## Constants -/

/-- A handle's denotation shallower than the twin's walk fuel. -/
def ShallowE (st : EStore) (e : EIdx) : Prop := ∃ x, denoteE st e = some x ∧ edep x < coreWalkFuel

theorem ShallowE.mono {st st' : EStore} {e : EIdx} (h : ShallowE st e) (hx : Ext st st') : ShallowE st' e :=
  let ⟨x, h1, h2⟩ := h; ⟨x, hx.expr _ _ h1, h2⟩

/-- The records the `And` pin's comparison accepts against the pin: equal but for an inductive's
capabilities. -/
def CanonAgree : IConstantInfo → IConstantInfo → Prop
  | .indInfo cv _, .indInfo cv' _ => cv = cv'
  | .ctorInfo cv a b c, .ctorInfo cv' a' b' c' => cv = cv' ∧ a = a' ∧ b = b' ∧ c = c'
  | .recInfo cv a b k rs, .recInfo cv' a' b' k' rs' => cv = cv' ∧ a = a' ∧ b = b' ∧ k = k' ∧ rs = rs'
  | _, _ => False

/-- A pinned record the comparison walks within the fuel: its type, and a recursor's right-hand sides. -/
def ShallowCI (st : EStore) (c : IConstantInfo) : Prop :=
  ShallowE st c.toConstantVal.type ∧
  match c with
  | .recInfo _ _ _ _ rs => ∀ r ∈ rs, ShallowE st r.rhs
  | _ => True

theorem ShallowCI.mono {st st' : EStore} {c : IConstantInfo} (h : ShallowCI st c) (hx : Ext st st') :
    ShallowCI st' c := by
  refine ⟨h.1.mono hx, ?_⟩
  have h2 := h.2
  cases c <;> first | trivial | exact fun r hr => (h2 r hr).mono hx

theorem canonNames_one_eq : canonNames 1 = (internName (.num .anonymous 0) >>= fun h => pure [h]) := by
  funext s
  simp only [canonNames, canonNamesGo, internName, bind_assoc, pure_bind]

/-- `canonNames n`, rerun where it ran, moves nothing (`n ≤ 1`). -/
def NamesFix (n : Nat) (s1 : AState) (cs : List NIdx) : Prop := canonNames n s1 = .ok (cs, s1)

theorem namesFix_zero (s : AState) : ∀ cs s1, canonNames 0 s = .ok (cs, s1) → s1 = s ∧ cs = [] ∧ NamesFix 0 s1 cs := by
  intro cs s1 h
  simp only [canonNames, canonNamesGo] at h
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h
  exact ⟨rfl, rfl, rfl⟩

theorem namesFix_one {s s1 : AState} {cs : List NIdx} (hok : StateOK s) (h : canonNames 1 s = .ok (cs, s1)) :
    NamesFix 1 s1 cs := by
  obtain ⟨ok1, -, -, -, hd⟩ := canonNames_run hok h
  rw [canonNames_one_eq] at h
  obtain ⟨a, s2, g1, k1⟩ := AM.bind_ok h
  obtain ⟨rfl, rfl⟩ := AM.pure_ok k1
  simp only [Frontend.denoteNList, List.range_one, List.map_cons, List.map_nil] at hd
  have hd' : denoteN s1.store.ns a = some (.num .anonymous 0) := by
    cases e : denoteN s1.store.ns a with
    | none => rw [e] at hd; simp at hd
    | some x => rw [e] at hd; simp at hd; rw [hd]
  obtain ⟨-, ⟨rkN, hN⟩⟩ := wf_parts ok1.wf
  have := ConPanqueque.T.internName_denote s1 rkN hN (.num .anonymous 0) _ a hd'
  unfold NamesFix
  rw [canonNames_one_eq, bind_ok_l this]; rfl

theorem cvCanonEq_self (cv : IConstantVal) {s s1 : AState} {cs : List NIdx} (hok : StateOK s)
    (hn : canonNames cv.levelParams.length s = .ok (cs, s1)) (hsh : ShallowE s.store cv.type) :
    cv.canonEq cv s = .ok (true, s1) := by
  obtain ⟨ok1, hx1, -, -, -⟩ := canonNames_run hok hn
  obtain ⟨x, hx, hd⟩ := hsh.mono hx1
  simp only [IConstantVal.canonEq, beq_self_eq_true, Bool.and_self, ite_true]
  rw [bind_ok_l hn]
  exact canonExprEq_refl cv.levelParams cs s1 ok1 _ _ x hx hd

theorem canonRulesEq_self (ps cs : List NIdx) (s : AState) (hok : StateOK s) :
    ∀ (rs : List IRecRule), (∀ r ∈ rs, ShallowE s.store r.rhs) →
      canonRulesEq ps ps cs coreWalkFuel rs rs s = .ok (true, s)
  | [], _ => rfl
  | r :: rs, h => by
    obtain ⟨x, hx, hd⟩ := h r (by simp)
    simp only [ConRon.Arena.canonRulesEq, beq_self_eq_true, ite_true]
    rw [bind_ok_l (canonExprEq_refl ps cs s hok _ _ x hx hd)]
    simp only [ite_true]
    exact canonRulesEq_self ps cs s hok rs (fun q hq => h q (by simp [hq]))

/-- **A record against a pinned record it agrees with**: `true`, at the state `canonNames` leaves. -/
theorem ciCanonEq_agree {b p : IConstantInfo} {s s1 : AState} {cs : List NIdx} (hok : StateOK s)
    (hag : CanonAgree b p) (hn : canonNames p.toConstantVal.levelParams.length s = .ok (cs, s1))
    (hfix : NamesFix p.toConstantVal.levelParams.length s1 cs) (hsh : ShallowCI s.store p) :
    b.canonEq p s = .ok (true, s1) := by
  obtain ⟨ok1, hx1, -, -, -⟩ := canonNames_run hok hn
  cases b <;> cases p <;> simp only [CanonAgree] at hag
  case indInfo.indInfo cv _ cv' _ =>
    subst hag
    exact cvCanonEq_self cv hok hn hsh.1
  case ctorInfo.ctorInfo cv a b c cv' a' b' c' =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := hag
    simp only [IConstantInfo.canonEq, beq_self_eq_true, Bool.and_self, ite_true]
    exact cvCanonEq_self cv hok hn hsh.1
  case recInfo.recInfo cv a b k rs cv' a' b' k' rs' =>
    obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hag
    simp only [IConstantInfo.canonEq, beq_self_eq_true, Bool.and_self, ite_true]
    rw [bind_ok_l (cvCanonEq_self cv hok hn hsh.1)]
    simp only [ite_true]
    rw [bind_ok_l (show canonNames cv.levelParams.length s1 = .ok (cs, s1) from hfix)]
    exact canonRulesEq_self _ cs s1 ok1 rs (fun r hr => (hsh.2 r hr).mono hx1)

/-- **The `And` pin's comparison of a block agreeing with the pin**: `true`, at the state the recursor's one
`canonNames` leaves. -/
theorem canonEqList_and {b0 b1 b2 p0 p1 p2 : IConstantInfo} {s s3 : AState} {cs : List NIdx} (hok : StateOK s)
    (h0 : CanonAgree b0 p0) (h1 : CanonAgree b1 p1) (h2 : CanonAgree b2 p2)
    (l0 : p0.toConstantVal.levelParams.length = 0) (l1 : p1.toConstantVal.levelParams.length = 0)
    (l2 : p2.toConstantVal.levelParams.length = 1)
    (sh0 : ShallowCI s.store p0) (sh1 : ShallowCI s.store p1) (sh2 : ShallowCI s.store p2)
    (hn : canonNames 1 s = .ok (cs, s3)) :
    canonEqList [b0, b1, b2] [p0, p1, p2] s = .ok (true, s3) := by
  have n0 : canonNames 0 s = .ok ([], s) := rfl
  have e0 := ciCanonEq_agree hok h0 (by rw [l0]; exact n0) (by rw [l0]; exact n0) sh0
  have e1 := ciCanonEq_agree hok h1 (by rw [l1]; exact n0) (by rw [l1]; exact n0) sh1
  have e2 := ciCanonEq_agree hok h2 (by rw [l2]; exact hn) (by rw [l2]; exact namesFix_one hok hn) sh2
  simp only [ConRon.Arena.canonEqList]
  rw [bind_ok_l e0]; simp only [ite_true]
  rw [bind_ok_l e1]; simp only [ite_true]
  rw [bind_ok_l e2]; simp only [ite_true]
  rfl

/-- **The pinned `And` block's interning is its plain interning.** -/
theorem andPinDecls_plain {s s' : AState} {r : List IConstantInfo} (ho : ConPanqueque.Logic.InternRerun.Off s.store)
    (h : ConPanqueque.Logic.PlainIntern.plainCIList ConLeche.andPin s = .ok (r, s')) :
    andPinDecls s = .ok (r, s') := by
  obtain ⟨-, m, e, -⟩ := ConPanqueque.Logic.PlainIntern.internCIList_plain _ ∅ s r s' ho
    (ConPanqueque.Logic.PlainIntern.memoOK_empty s) h
  unfold andPinDecls ConRon.Arena.internCIList
  simp [bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure, e]

/-- A recursor's rules (none for another constant). -/
def ciRules : ConstantInfo → List RecRule
  | .recInfo _ _ _ _ rs => rs
  | _ => []

theorem rules_rhs_some {st : EStore} : ∀ (rs : List IRecRule) (Rs : List RecRule),
    Frontend.denoteRules st rs = some Rs → ∀ r ∈ rs, ∃ R ∈ Rs, denoteE st r.rhs = some R.rhs
  | [], _, _, r, hr => by simp at hr
  | a :: as, Rs, h, r, hr => by
    obtain ⟨x, xs, h1, h2, rfl⟩ := denoteRules_cons h
    rcases List.mem_cons.mp hr with rfl | hr
    · obtain ⟨-, -, h3, -⟩ := denoteRule_inv h1
      exact ⟨x, by simp, h3⟩
    · obtain ⟨R, hR, h3⟩ := rules_rhs_some as xs h2 r hr
      exact ⟨R, by simp [hR], h3⟩

theorem shallowCI_of_denote {st : EStore} {c : IConstantInfo} {x : ConstantInfo}
    (h : Frontend.denoteCI st c = some x) (ht : edep x.toConstantVal.type < coreWalkFuel)
    (hr : ∀ R ∈ ciRules x, edep R.rhs < coreWalkFuel) : ShallowCI st c := by
  obtain ⟨-, -, hty⟩ := denoteCV_inv (denoteCI_toConstantVal h)
  refine ⟨⟨_, hty, ht⟩, ?_⟩
  cases c with
  | recInfo v mI rP k rs =>
    obtain ⟨cv, Rs, rfl, -, hRs⟩ := denoteCI_rec_inv h
    intro r hr'
    obtain ⟨R, hR, hd⟩ := rules_rhs_some rs Rs hRs r hr'
    exact ⟨_, hd, hr R hR⟩
  | _ => trivial

theorem lps_len_of_denote {st : EStore} {c : IConstantInfo} {x : ConstantInfo}
    (h : Frontend.denoteCI st c = some x) :
    c.toConstantVal.levelParams.length = x.toConstantVal.levelParams.length := by
  obtain ⟨-, hl, -⟩ := denoteCV_inv (denoteCI_toConstantVal h)
  exact ConRon.Bridge.denoteNList_length _ _ hl

set_option maxRecDepth 100000 in
theorem andPin_shallow : ∀ x ∈ ConLeche.andPin, edep x.toConstantVal.type < coreWalkFuel ∧
    ∀ R ∈ ciRules x, edep R.rhs < coreWalkFuel := by
  decide

theorem fire_plain_of {st : EStore} {f : IRecRuleFire} (h : Frontend.denoteFire st f = some .plain) :
    f = .plain := by
  cases f with
  | plain => rfl
  | nested l p =>
    simp only [Frontend.denoteFire] at h
    split at h <;> simp at h
  | levels l => simp [Frontend.denoteFire] at h

/-- **The pinned `And` block's records' kinds**: an inductive, a constructor, a recursor with one plain rule. -/
theorem andPin_shape {st : EStore} {p0 p1 p2 : IConstantInfo} (d0 : Frontend.denoteCI st p0 = some ConLeche.andRaw)
    (d1 : Frontend.denoteCI st p1 = some ConLeche.andIntroRaw)
    (d2 : Frontend.denoteCI st p2 = some ConLeche.andRecRaw) :
    (∃ cv caps, p0 = .indInfo cv caps) ∧ (∃ cv a b T, p1 = .ctorInfo cv a b T) ∧
      (∃ cv mi rp k r, p2 = .recInfo cv mi rp k [r] ∧ r.fire = .plain) := by
  refine ⟨?_, ?_, ?_⟩
  · cases p0 with
    | indInfo cv caps => exact ⟨cv, caps, rfl⟩
    | axiomInfo v => obtain ⟨_, e, -⟩ := denoteCI_axiom_inv d0; simp [ConLeche.andRaw] at e
    | defnInfo v x h => obtain ⟨_, _, e, -⟩ := denoteCI_defn_inv d0; simp [ConLeche.andRaw] at e
    | thmInfo v => obtain ⟨_, e, -⟩ := denoteCI_thm_inv d0; simp [ConLeche.andRaw] at e
    | ctorInfo v a b T => obtain ⟨_, e, -⟩ := denoteCI_ctor_inv d0; simp [ConLeche.andRaw] at e
    | recInfo v a b k rs => obtain ⟨_, _, e, -⟩ := denoteCI_rec_inv d0; simp [ConLeche.andRaw] at e
  · cases p1 with
    | ctorInfo v a b T => exact ⟨v, a, b, T, rfl⟩
    | axiomInfo v => obtain ⟨_, e, -⟩ := denoteCI_axiom_inv d1; simp [ConLeche.andIntroRaw] at e
    | defnInfo v x h => obtain ⟨_, _, e, -⟩ := denoteCI_defn_inv d1; simp [ConLeche.andIntroRaw] at e
    | thmInfo v => obtain ⟨_, e, -⟩ := denoteCI_thm_inv d1; simp [ConLeche.andIntroRaw] at e
    | indInfo v c => obtain ⟨_, _, e, -⟩ := denoteCI_ind_inv d1; simp [ConLeche.andIntroRaw] at e
    | recInfo v a b k rs => obtain ⟨_, _, e, -⟩ := denoteCI_rec_inv d1; simp [ConLeche.andIntroRaw] at e
  · cases p2 with
    | recInfo v a b k rs =>
      obtain ⟨cv, Rs, e, -, hRs⟩ := denoteCI_rec_inv d2
      simp only [ConLeche.andRecRaw, ConLeche.ConstantInfo.recInfo.injEq] at e
      obtain ⟨-, -, -, -, rfl⟩ := e
      match rs, hRs with
      | [r], hRs =>
        obtain ⟨x, xs, h1, -, e2⟩ := denoteRules_cons hRs
        simp only [List.cons.injEq] at e2
        obtain ⟨rfl, -⟩ := e2
        obtain ⟨-, hf, -, -⟩ := denoteRule_inv h1
        exact ⟨v, a, b, k, r, rfl, fire_plain_of hf⟩
      | [], hRs => simp [Frontend.denoteRules] at hRs
      | _ :: _ :: _, hRs =>
        obtain ⟨x, xs, -, h2, e2⟩ := denoteRules_cons hRs
        simp only [List.cons.injEq] at e2
        obtain ⟨-, rfl⟩ := e2
        obtain ⟨y, ys, -, -, e3⟩ := denoteRules_cons h2
        cases e3
    | axiomInfo v => obtain ⟨_, e, -⟩ := denoteCI_axiom_inv d2; simp [ConLeche.andRecRaw] at e
    | defnInfo v x h => obtain ⟨_, _, e, -⟩ := denoteCI_defn_inv d2; simp [ConLeche.andRecRaw] at e
    | thmInfo v => obtain ⟨_, e, -⟩ := denoteCI_thm_inv d2; simp [ConLeche.andRecRaw] at e
    | indInfo v c => obtain ⟨_, _, e, -⟩ := denoteCI_ind_inv d2; simp [ConLeche.andRecRaw] at e
    | ctorInfo v a b T => obtain ⟨_, e, -⟩ := denoteCI_ctor_inv d2; simp [ConLeche.andRecRaw] at e

/-- **What the pinned `And` block's interning is**: three records, level-parameter counts `0, 0, 1`, every one
walked within the fuel. -/
theorem andPin_facts {st : EStore} {r : List IConstantInfo} (h : Frontend.denoteCIList st r = some ConLeche.andPin) :
    ∃ p0 p1 p2, r = [p0, p1, p2] ∧ p0.toConstantVal.levelParams.length = 0 ∧
      p1.toConstantVal.levelParams.length = 0 ∧ p2.toConstantVal.levelParams.length = 1 ∧
      ShallowCI st p0 ∧ ShallowCI st p1 ∧ ShallowCI st p2 ∧
      (∃ cv caps, p0 = .indInfo cv caps) ∧ (∃ cv a b T, p1 = .ctorInfo cv a b T) ∧
      (∃ cv mi rp k r, p2 = .recInfo cv mi rp k [r] ∧ r.fire = .plain) := by
  have hl := denoteCIList_length r _ h
  match r, hl with
  | [p0, p1, p2], _ =>
    obtain ⟨x0, hx0, d0⟩ := denoteCIList_get _ _ 0 p0 h rfl
    obtain ⟨x1, hx1, d1⟩ := denoteCIList_get _ _ 1 p1 h rfl
    obtain ⟨x2, hx2, d2⟩ := denoteCIList_get _ _ 2 p2 h rfl
    have hm : ∀ x, x ∈ ConLeche.andPin → _ := andPin_shallow
    simp only [ConLeche.andPin, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hx0 hx1 hx2
    subst hx0 hx1 hx2
    have m0 := hm ConLeche.andRaw (by simp [ConLeche.andPin])
    have m1 := hm ConLeche.andIntroRaw (by simp [ConLeche.andPin])
    have m2 := hm ConLeche.andRecRaw (by simp [ConLeche.andPin])
    refine ⟨p0, p1, p2, rfl, by rw [lps_len_of_denote d0]; rfl, by rw [lps_len_of_denote d1]; rfl,
      by rw [lps_len_of_denote d2]; rfl, shallowCI_of_denote d0 m0.1 m0.2, shallowCI_of_denote d1 m1.1 m1.2,
      shallowCI_of_denote d2 m2.1 m2.2, andPin_shape d0 d1 d2⟩

end ConPanqueque.T.Ind
