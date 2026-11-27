import ConLeche.Verify.EnvExt
import ConLeche.Verify.Cached.PureRun
import ConLeche.Semantics.DeclWF

/-! # Stream records at an extension of the environment

con-leche's verdict checks the built-in prelude, then the stream.  The port's verdict is the pure
fold on the stream alone.  The bridge is con-leche's knot theorem (`knot_ext`: a run on terms that
resolve in `env₁` is the same run at any extension `env₂`), lifted here to value records
(`checkDecl_ext`) and to accepting runs (`pureRun_ext`): a run of value records whose names the
environment's guards never read (`NameOK`) and the base does not declare carries over from the
empty environment to the prelude's. -/

namespace ConPanqueque.Pipeline

open ConLeche ConLeche.Verify

set_option autoImplicit true

variable {env₁ env₂ : Env}

theorem ops_infer (hx : EnvExt env₁ env₂) (F d : Nat) {e : Expr} (he : Res env₁ e) :
    (fueledOps .verified F).inferType env₂ d e = (fueledOps .verified F).inferType env₁ d e ∧
      ∀ y, (fueledOps .verified F).inferType env₁ d e = .ok y → Res env₁ y :=
  (knot_ext .verified hx F false).infer d he

theorem ops_whnf (hx : EnvExt env₁ env₂) (F d : Nat) {e : Expr} (he : Res env₁ e) :
    (fueledOps .verified F).whnf env₂ d e = (fueledOps .verified F).whnf env₁ d e :=
  ((knot_ext .verified hx F false).whnf d he).1

theorem ops_ensureSort (hx : EnvExt env₁ env₂) (F d : Nat) {e : Expr} (he : Res env₁ e) :
    (fueledOps .verified F).ensureSort env₂ d e = (fueledOps .verified F).ensureSort env₁ d e := by
  show ensureSort _ env₂ d e = ensureSort _ env₁ d e
  unfold ensureSort
  rw [show (pureFns .verified false env₂ F).whnf d e = (pureFns .verified false env₁ F).whnf d e from
    ((knot_ext .verified hx F false).whnf d he).1]

theorem ops_defeq (hx : EnvExt env₁ env₂) (F d : Nat) {a b : Expr} (ha : Res env₁ a) (hb : Res env₁ b) :
    (fueledOps .verified F).isDefEq env₂ d a b = (fueledOps .verified F).isDefEq env₁ d a b :=
  ((knot_ext .verified hx F false).defeq d ha hb).1

theorem res_ext (hx : EnvExt env₁ env₂) {e : Expr} (h : e.constsResolve env₁ = true) : e.constsResolve env₂ = true :=
  Expr.constsResolve_of_find (fun n hn => by
    obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hn
    rw [hx.find n ci hci]; rfl) h

theorem checkConstantVal_ext (hx : EnvExt env₁ env₂) (F : Nat) (cv : ConstantVal) (a b c : Bool)
    (hfresh : env₂.find? cv.name = none)
    (h : checkConstantVal (fueledOps .verified F) env₁ cv a b c = .ok ()) :
    checkConstantVal (fueledOps .verified F) env₂ cv a b c = .ok () := by
  unfold checkConstantVal at h ⊢
  simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, ite_not] at h ⊢
  cases hr : cv.type.constsResolve env₁ with
  | false =>
    exfalso; rw [hr] at h
    repeat' split at h
    all_goals first | contradiction | (simp at h) | simp_all
  | true =>
    have hr2 := res_ext hx hr
    rw [hr] at h; rw [hr2, hfresh]
    have hf1 : env₁.find? cv.name = none := by
      cases hc : env₁.find? cv.name with
      | none => rfl
      | some ci => rw [hc] at h; simp at h
    rw [hf1] at h
    rw [(ops_infer hx F 0 hr).1]
    cases hi : (fueledOps .verified F).inferType env₁ 0 cv.type with
    | error e => simp only [hi] at h ⊢; exact h
    | ok s =>
      simp only [hi] at h ⊢
      rw [ops_ensureSort hx F 0 ((ops_infer hx F 0 hr).2 s hi)]
      exact h

/-- The value check of a definition/theorem/opaque: resolution, inference, comparison. -/
theorem valCore_ext (hx : EnvExt env₁ env₂) (F : Nat) (cv : ConstantVal) (v : Expr)
    (hv : v.constsResolve env₁ = true) (hty : cv.type.constsResolve env₁ = true)
    (k : Bool → CheckM Env) (k₂ : Bool → CheckM Env)
    (hk : ∀ b, k b = .ok E → ∃ E₂, k₂ b = .ok E₂)
    (h : ((fueledOps .verified F).inferType env₁ 0 v >>= fun vt =>
      (fueledOps .verified F).isDefEq env₁ 0 vt cv.type >>= k) = .ok E) :
    ∃ E₂, ((fueledOps .verified F).inferType env₂ 0 v >>= fun vt =>
      (fueledOps .verified F).isDefEq env₂ 0 vt cv.type >>= k₂) = .ok E₂ := by
  rw [(ops_infer hx F 0 hv).1]
  cases hi : (fueledOps .verified F).inferType env₁ 0 v with
  | error e => simp [hi, bind, Except.bind] at h
  | ok vt =>
    simp only [hi, bind, Except.bind] at h ⊢
    rw [ops_defeq hx F 0 ((ops_infer hx F 0 hv).2 vt hi) hty]
    cases hd : (fueledOps .verified F).isDefEq env₁ 0 vt cv.type with
    | error e => simp [hd] at h
    | ok b => simp only [hd] at h ⊢; exact hk b h

theorem checkDefnVal_ext (hx : EnvExt env₁ env₂) (F : Nat) (cv : ConstantVal) (v : Expr) (hint : ReducibilityHint)
    (hty : cv.type.constsResolve env₁ = true) {E : Env}
    (h : checkDefnVal (fueledOps .verified F) env₁ cv v hint = .ok E) :
    checkDefnVal (fueledOps .verified F) env₂ cv v hint = .ok ⟨.defnInfo cv v hint :: env₂.consts, env₂.tables⟩ ∧
      E = ⟨.defnInfo cv v hint :: env₁.consts, env₁.tables⟩ := by
  unfold checkDefnVal at h ⊢
  simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h ⊢
  cases hr : v.constsResolve env₁ with
  | false =>
    exfalso; rw [hr] at h
    repeat' split at h
    all_goals first | contradiction | (simp at h) | simp_all
  | true =>
    rw [hr] at h; rw [res_ext hx hr]
    rw [(ops_infer hx F 0 hr).1]
    cases hi : (fueledOps .verified F).inferType env₁ 0 v with
    | error e =>
      simp only [hi] at h
      exfalso; repeat' split at h
      all_goals first | contradiction | (simp at h) | simp_all
    | ok vt =>
      simp only [hi] at h ⊢
      rw [ops_defeq hx F 0 ((ops_infer hx F 0 hr).2 vt hi) hty]
      cases hd : (fueledOps .verified F).isDefEq env₁ 0 vt cv.type with
      | error e =>
        simp only [hd] at h
        exfalso; repeat' split at h
        all_goals first | contradiction | (simp at h) | simp_all
      | ok b =>
        simp only [hd] at h ⊢
        cases b
        · exfalso; repeat' split at h
          all_goals first | contradiction | (simp at h) | simp_all
        · repeat' split at h
          all_goals first | contradiction |
            (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; simp_all [pure, Except.pure]) | (simp at h)

set_option hygiene false in
macro "close_br" : tactic => `(tactic| (repeat' split at h) <;> first | contradiction |
  (simp only [pure, Except.pure, Except.ok.injEq] at h; subst h; simp_all [pure, Except.pure]) | (simp at h))

theorem checkOpaqueVal_ext (hx : EnvExt env₁ env₂) (F : Nat) (cv : ConstantVal) (v : Expr)
    (hty : cv.type.constsResolve env₁ = true) {E : Env}
    (h : checkOpaqueVal (fueledOps .verified F) env₁ cv v = .ok E) :
    checkOpaqueVal (fueledOps .verified F) env₂ cv v = .ok ⟨.axiomInfo cv :: env₂.consts, env₂.tables⟩ ∧
      E = ⟨.axiomInfo cv :: env₁.consts, env₁.tables⟩ := by
  unfold checkOpaqueVal at h ⊢
  simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h ⊢
  cases hr : v.constsResolve env₁ with
  | false => exfalso; rw [hr] at h; close_br
  | true =>
    rw [hr] at h; rw [res_ext hx hr]
    rw [(ops_infer hx F 0 hr).1]
    cases hi : (fueledOps .verified F).inferType env₁ 0 v with
    | error e => simp only [hi] at h; exfalso; close_br
    | ok vt =>
      simp only [hi] at h ⊢
      rw [ops_defeq hx F 0 ((ops_infer hx F 0 hr).2 vt hi) hty]
      cases hd : (fueledOps .verified F).isDefEq env₁ 0 vt cv.type with
      | error e => simp only [hd] at h; exfalso; close_br
      | ok b =>
        simp only [hd] at h ⊢
        cases b
        · exfalso; close_br
        · close_br

theorem checkThmVal_ext (hx : EnvExt env₁ env₂) (F : Nat) (cv : ConstantVal) (v : Expr)
    (hty : cv.type.constsResolve env₁ = true) {E : Env}
    (h : checkThmVal (fueledOps .verified F) env₁ cv v = .ok E) :
    checkThmVal (fueledOps .verified F) env₂ cv v = .ok ⟨.thmInfo cv :: env₂.consts, env₂.tables⟩ ∧
      E = ⟨.thmInfo cv :: env₁.consts, env₁.tables⟩ := by
  unfold checkThmVal at h ⊢
  simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h ⊢
  rw [(ops_infer hx F 0 hty).1]
  cases hs : (fueledOps .verified F).inferType env₁ 0 cv.type with
  | error e => simp only [hs] at h; exfalso; close_br
  | ok st =>
    simp only [hs] at h ⊢
    rw [ops_ensureSort hx F 0 ((ops_infer hx F 0 hty).2 st hs)]
    cases hu : (fueledOps .verified F).ensureSort env₁ 0 st with
    | error e => simp only [hu] at h; exfalso; close_br
    | ok u =>
      simp only [hu] at h ⊢
      cases hl : (liftFueled "level comparison" (Level.isEquiv u .zero) : CheckM Bool) with
      | error e => simp only [hl] at h; exfalso; close_br
      | ok bl =>
        simp only [hl] at h ⊢
        cases hr : v.constsResolve env₁ with
        | false => exfalso; rw [hr] at h; close_br
        | true =>
          rw [hr] at h; rw [res_ext hx hr]
          rw [(ops_infer hx F 0 hr).1]
          cases hi : (fueledOps .verified F).inferType env₁ 0 v with
          | error e => simp only [hi] at h; exfalso; close_br
          | ok vt =>
            simp only [hi] at h ⊢
            rw [ops_defeq hx F 0 ((ops_infer hx F 0 hr).2 vt hi) hty]
            cases hd : (fueledOps .verified F).isDefEq env₁ 0 vt cv.type with
            | error e => simp only [hd] at h; exfalso; close_br
            | ok b =>
              simp only [hd] at h ⊢
              cases b
              · exfalso; close_br
              · close_br

theorem checkConstantVal_res (F : Nat) (env : Env) (cv : ConstantVal) (a b c : Bool)
    (h : checkConstantVal (fueledOps .verified F) env cv a b c = .ok ()) :
    cv.type.constsResolve env = true ∧ env.find? cv.name = none := by
  unfold checkConstantVal at h
  simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
  constructor
  · cases hr : cv.type.constsResolve env with
    | true => rfl
    | false => exfalso; rw [hr] at h; close_br
  · cases hc : env.find? cv.name with
    | none => rfl
    | some ci => rw [hc] at h; simp at h

/-- The names a stream record may take for the extension argument: none of the environment's
guards or certified operations looks them up. -/
def NameOK (n : Name) : Prop :=
  natOpName n = false ∧ n ∉ reduceOpNames ∧ n ≠ natName ∧ n ≠ natZeroName ∧ n ≠ natSuccName ∧
    n ≠ boolTrueName ∧ n ≠ boolFalseName

theorem envExt_cons (hx : EnvExt env₁ env₂) (hw2 : EnvWF env₂) (c : ConstantInfo)
    (hf1 : env₁.find? c.name = none) (hf2 : env₂.find? c.name = none) (hwE : EnvWF ⟨c :: env₁.consts, env₁.tables⟩)
    (hn : NameOK c.name) (hrec : ∀ cv mI rP isK rules, c ≠ .recInfo cv mI rP isK rules) :
    EnvExt ⟨c :: env₁.consts, env₁.tables⟩ ⟨c :: env₂.consts, env₂.tables⟩ := by
  have fc : ∀ (e : Env) (n : Name), n ≠ c.name → Env.find? ⟨c :: e.consts, e.tables⟩ n = e.find? n := by
    intro e n hne; rw [Env.find?_cons, ite_eq_right (fun h => hne h.symm)]
  refine ⟨fun n ci h => ?_, fun T hT => ?_, ?_⟩
  · by_cases e : n = c.name
    · subst e; rw [Env.find?_cons_self] at h ⊢; exact h
    · rw [fc _ _ e] at h ⊢; exact hx.find n ci h
  · rw [EnvWF.findTable?_cons hw2 hf2, EnvWF.findTable?_cons hx.facts.wf hf1]
    by_cases e : T = c.name
    · subst e; simp [Env.findTable?, hf1, hf2]
    · rw [fc _ _ e] at hT; exact hx.table T hT
  · obtain ⟨hwf, hnat, hrc, htc, hbool⟩ := hx.facts
    obtain ⟨hop, hred, h1, h2, h3, h4, h5⟩ := hn
    have nOp : ∀ m ∈ natOpNames, m ≠ c.name := fun m hm e => by
      subst e; simp [natOpName, List.contains_iff_mem, hm] at hop
    refine ⟨hwE, ?_, ?_, ?_, ?_⟩
    · rw [fc _ _ (Ne.symm h1), fc _ _ (Ne.symm h2), fc _ _ (Ne.symm h3)]; exact hnat
    · intro n cv mI rP isK rules hn' r hr
      have hne : n ≠ c.name := by
        intro e; subst e; rw [Env.find?_cons_self] at hn'; exact hrec _ _ _ _ _ (Option.some.inj hn')
      rw [fc _ _ hne] at hn'
      obtain ⟨cvj, cnP, cnF, T, hj⟩ := hrc n cv mI rP isK rules hn' r hr
      have hne2 : RecRule.ctor r ≠ c.name := by intro e; rw [e, hf1] at hj; cases hj
      exact ⟨cvj, cnP, cnF, T, by rw [fc _ _ hne2]; exact hj⟩
    · intro T tbl hT
      rw [EnvWF.findTable?_cons hx.facts.wf hf1] at hT
      obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (htc T tbl hT)
      rw [Env.find?_cons]; split <;> simp [hci]
    · rw [fc _ _ (nOp _ (by simp [natOpNames])), fc _ _ (nOp _ (by simp [natOpNames])),
        fc _ _ (Ne.symm h4), fc _ _ (Ne.symm h5)]; exact hbool

/-- A value record's name. -/
def valName : Declaration → Option Name
  | .defnDecl cv _ _ => some cv.name
  | .thmDecl cv _ => some cv.name
  | .opaqueDecl cv _ => some cv.name
  | _ => none

/-- The shared tail: from the step's run at `env₂` and the result at `env₁`, the conclusion. -/
theorem checkDecl_ext_tail (hx : EnvExt env₁ env₂) (hw2 : EnvWF env₂) (F : Nat) (pins' : List NatOpPinSet)
    (d : Declaration) (c : ConstantInfo) (hf1 : env₁.find? c.name = none) (hf2 : env₂.find? c.name = none)
    (hn : NameOK c.name) (hrec : ∀ cv mI rP isK rules, c ≠ .recInfo cv mI rP isK rules) {E : Env}
    (hwE : EnvWF E) (hE : E = ⟨c :: env₁.consts, env₁.tables⟩)
    (h2 : checkDecl .verified (fueledOps .verified F) pins' env₂ d = .ok ⟨c :: env₂.consts, env₂.tables⟩) :
    ∃ E₂, checkDecl .verified (fueledOps .verified F) pins' env₂ d = .ok E₂ ∧ EnvExt E E₂ ∧ EnvWF E₂ ∧
      env₁.find? c.name = none ∧ E = ⟨c :: env₁.consts, env₁.tables⟩ ∧ E₂ = ⟨c :: env₂.consts, env₂.tables⟩ :=
  ⟨_, h2, by subst hE; exact envExt_cons hx hw2 c hf1 hf2 hwE hn hrec,
    ConLeche.Semantics.checkDecl_envWF hw2 h2, hf1, hE, rfl⟩

theorem checkDecl_ext (hx : EnvExt env₁ env₂) (hw2 : EnvWF env₂) (F : Nat) (pins pins' : List NatOpPinSet)
    (d : Declaration) (n : Name) (hd : valName d = some n) (hf2 : env₂.find? n = none) (hn : NameOK n)
    {E : Env} (h : checkDecl .verified (fueledOps .verified F) pins env₁ d = .ok E) :
    ∃ E₂, checkDecl .verified (fueledOps .verified F) pins' env₂ d = .ok E₂ ∧ EnvExt E E₂ ∧ EnvWF E₂ ∧
      ∃ c : ConstantInfo, c.name = n ∧ env₁.find? n = none ∧ E = ⟨c :: env₁.consts, env₁.tables⟩ ∧
        E₂ = ⟨c :: env₂.consts, env₂.tables⟩ := by
  have hwE : EnvWF E := ConLeche.Semantics.checkDecl_envWF hx.facts.wf h
  have hn0 := hn
  obtain ⟨hop, hred, -⟩ := hn
  have hop1 : natOpNames.contains n = false := by
    simp only [natOpName, Bool.or_eq_false_iff] at hop; exact hop.1
  have hop2 : natDivModNames.contains n = false := by
    simp only [natOpName, Bool.or_eq_false_iff] at hop; exact hop.2
  have hred' : reduceOpNames.contains n = false := by simpa using hred
  cases d with
  | defnDecl cv v hint =>
    simp only [valName, Option.some.injEq] at hd; subst hd
    have key : checkDecl .verified (fueledOps .verified F) pins' env₂ (.defnDecl cv v hint) =
        .ok ⟨.defnInfo cv v hint :: env₂.consts, env₂.tables⟩ ∧ E = ⟨.defnInfo cv v hint :: env₁.consts, env₁.tables⟩ ∧
        env₁.find? cv.name = none := by
      unfold checkDecl checkDeclKind at h ⊢
      simp only [bind, Except.bind, hop1, hop2] at h ⊢
      cases hc : checkConstantVal (fueledOps .verified F) env₁ cv true with
      | error e => rw [hc] at h; cases h
      | ok u =>
        rw [hc] at h
        obtain ⟨hty, hf1⟩ := checkConstantVal_res F env₁ cv true false false hc
        rw [checkConstantVal_ext hx F cv true false false hf2 hc]
        cases hv : checkDefnVal (fueledOps .verified F) env₁ cv v hint with
        | error e => rw [hv] at h; cases h
        | ok E1 =>
          rw [hv] at h
          obtain ⟨hv2, rfl⟩ := checkDefnVal_ext hx F cv v hint hty hv
          rw [hv2]
          simp only [Bool.false_eq_true, ite_false, pure, Except.pure] at h ⊢
          split at h
          · rename_i hb; simp only [hb, ite_true, Except.ok.injEq] at h ⊢; exact ⟨trivial, h.symm, hf1⟩
          · simp [throw, throwThe, MonadExceptOf.throw] at h
    obtain ⟨E₂, e1, e2, e3, e4, e5, e6⟩ :=
      checkDecl_ext_tail hx hw2 F pins' _ (.defnInfo cv v hint) key.2.2 hf2 hn0 (fun _ _ _ _ _ h => by cases h) hwE key.2.1 key.1
    exact ⟨E₂, e1, e2, e3, _, rfl, e4, e5, e6⟩
  | thmDecl cv v =>
    simp only [valName, Option.some.injEq] at hd; subst hd
    have key : checkDecl .verified (fueledOps .verified F) pins' env₂ (.thmDecl cv v) =
        .ok ⟨.thmInfo cv :: env₂.consts, env₂.tables⟩ ∧ E = ⟨.thmInfo cv :: env₁.consts, env₁.tables⟩ ∧
        env₁.find? cv.name = none := by
      unfold checkDecl checkDeclKind at h ⊢
      simp only [bind, Except.bind] at h ⊢
      cases hc : checkConstantVal (fueledOps .verified F) env₁ cv with
      | error e => rw [hc] at h; cases h
      | ok u =>
        rw [hc] at h
        obtain ⟨hty, hf1⟩ := checkConstantVal_res F env₁ cv false false false hc
        rw [checkConstantVal_ext hx F cv false false false hf2 hc]
        cases hv : checkThmVal (fueledOps .verified F) env₁ cv v with
        | error e => rw [hv] at h; cases h
        | ok E1 =>
          rw [hv] at h
          obtain ⟨hv2, rfl⟩ := checkThmVal_ext hx F cv v hty hv
          rw [hv2]
          simp only [pure, Except.pure] at h ⊢
          split at h
          · rename_i hb; simp only [hb, ite_true, Except.ok.injEq] at h ⊢; exact ⟨trivial, h.symm, hf1⟩
          · simp [throw, throwThe, MonadExceptOf.throw] at h
    obtain ⟨E₂, e1, e2, e3, e4, e5, e6⟩ :=
      checkDecl_ext_tail hx hw2 F pins' _ (.thmInfo cv) key.2.2 hf2 hn0 (fun _ _ _ _ _ h => by cases h) hwE key.2.1 key.1
    exact ⟨E₂, e1, e2, e3, _, rfl, e4, e5, e6⟩
  | opaqueDecl cv v =>
    simp only [valName, Option.some.injEq] at hd; subst hd
    have key : checkDecl .verified (fueledOps .verified F) pins' env₂ (.opaqueDecl cv v) =
        .ok ⟨.axiomInfo cv :: env₂.consts, env₂.tables⟩ ∧ E = ⟨.axiomInfo cv :: env₁.consts, env₁.tables⟩ ∧
        env₁.find? cv.name = none := by
      unfold checkDecl checkDeclKind at h ⊢
      simp only [bind, Except.bind, hred'] at h ⊢
      cases hc : checkConstantVal (fueledOps .verified F) env₁ cv false true with
      | error e => rw [hc] at h; cases h
      | ok u =>
        rw [hc] at h
        obtain ⟨hty, hf1⟩ := checkConstantVal_res F env₁ cv false true false hc
        rw [checkConstantVal_ext hx F cv false true false hf2 hc]
        cases hv : checkOpaqueVal (fueledOps .verified F) env₁ cv v with
        | error e => rw [hv] at h; cases h
        | ok E1 =>
          rw [hv] at h
          obtain ⟨hv2, rfl⟩ := checkOpaqueVal_ext hx F cv v hty hv
          rw [hv2]
          simp only [Bool.false_eq_true, ite_false, pure, Except.pure] at h ⊢
          split at h
          · rename_i hb; simp only [hb, ite_true, Except.ok.injEq] at h ⊢; exact ⟨trivial, h.symm, hf1⟩
          · simp [throw, throwThe, MonadExceptOf.throw] at h
    obtain ⟨E₂, e1, e2, e3, e4, e5, e6⟩ :=
      checkDecl_ext_tail hx hw2 F pins' _ (.axiomInfo cv) key.2.2 hf2 hn0 (fun _ _ _ _ _ h => by cases h) hwE key.2.1 key.1
    exact ⟨E₂, e1, e2, e3, _, rfl, e4, e5, e6⟩
  | _ => simp [valName] at hd

theorem storedFacts_empty : StoredFacts Env.empty :=
  ⟨ConLeche.Semantics.EnvWF.empty, by simp [Env.empty, Env.find?], fun n _ _ _ _ _ h => by simp [Env.empty, Env.find?] at h,
    fun T tbl h => by simp [Env.empty, Env.findTable?, Env.find?] at h, by simp [Env.empty, Env.find?]⟩

theorem envExt_empty (env : Env) : EnvExt Env.empty env :=
  ⟨fun n ci h => by simp [Env.empty, Env.find?] at h, fun T h => by simp [Env.empty, Env.find?] at h, storedFacts_empty⟩

theorem pureRun_envWF {pins : List NatOpPinSet} : ∀ {ds : List Declaration} {E E' : Env},
    PureRun pins ds E E' → EnvWF E → EnvWF E'
  | _, _, _, .nil _, h => h
  | _, _, _, .cons ⟨F, hs⟩ rest, h => pureRun_envWF rest (ConLeche.Semantics.checkDecl_envWF h hs)

theorem pureRun_append {pins : List NatOpPinSet} : ∀ {ps qs : List Declaration} {E0 E1 E2 : Env},
    PureRun pins ps E0 E1 → PureRun pins qs E1 E2 → PureRun pins (ps ++ qs) E0 E2
  | _, _, _, _, _, .nil _, h => h
  | _, _, _, _, _, .cons hs rest, h => .cons hs (pureRun_append rest h)

theorem checkDecl_val_fresh (F : Nat) (pins : List NatOpPinSet) (env : Env) (d : Declaration) (n : Name)
    (hd : valName d = some n) {E : Env} (h : checkDecl .verified (fueledOps .verified F) pins env d = .ok E) :
    env.find? n = none := by
  cases d with
  | defnDecl cv v hint =>
    simp only [valName, Option.some.injEq] at hd; subst hd
    unfold checkDecl checkDeclKind at h; simp only [bind, Except.bind] at h
    cases hc : checkConstantVal (fueledOps .verified F) env cv true with
    | error e => rw [hc] at h; cases h
    | ok u => exact (checkConstantVal_res F env cv true false false hc).2
  | thmDecl cv v =>
    simp only [valName, Option.some.injEq] at hd; subst hd
    unfold checkDecl checkDeclKind at h; simp only [bind, Except.bind] at h
    cases hc : checkConstantVal (fueledOps .verified F) env cv with
    | error e => rw [hc] at h; cases h
    | ok u => exact (checkConstantVal_res F env cv false false false hc).2
  | opaqueDecl cv v =>
    simp only [valName, Option.some.injEq] at hd; subst hd
    unfold checkDecl checkDeclKind at h; simp only [bind, Except.bind] at h
    cases hc : checkConstantVal (fueledOps .verified F) env cv false true with
    | error e => rw [hc] at h; cases h
    | ok u => exact (checkConstantVal_res F env cv false true false hc).2
  | _ => simp [valName] at hd

theorem stdAxiomOk_sorry (env : Env) (c : ConstantVal) (hs : c.name = sorryAxName) : stdAxiomOk env c = false := by
  unfold stdAxiomOk
  rw [if_neg (by rw [hs]; decide), if_neg (by rw [hs]; decide)]

theorem checkDecl_sorry_ext (hx : EnvExt env₁ env₂) (F : Nat) (pins pins' : List NatOpPinSet) (c : ConstantVal)
    (hs : c.name = sorryAxName) (hf2 : env₂.find? c.name = none) {E : Env}
    (h : checkDecl .verified (fueledOps .verified F) pins env₁ (.axiomDecl c) = .ok E) :
    E = env₁ ∧ checkDecl .verified (fueledOps .verified F) pins' env₂ (.axiomDecl c) = .ok env₂ := by
  unfold checkDecl checkDeclKind at h ⊢
  have hq : ¬ (c.name = quotSoundName) := by rw [hs]; decide
  have h3 : ¬ (c.name = trustCompilerName) := by rw [hs]; decide
  have h4 : ¬ (c.name = ofReduceNatName ∨ c.name = ofReduceBoolName) := by rw [hs]; decide
  have h5 : ¬ (c.name = propextName ∨ c.name = choiceName) := by rw [hs]; decide
  simp only [ite_eq_right hq, bind, Except.bind] at h ⊢
  cases hc : checkConstantVal (fueledOps .verified F) env₁ c false false true with
  | error e => rw [hc] at h; cases h
  | ok u =>
    rw [hc] at h
    rw [checkConstantVal_ext hx F c false false true hf2 hc]
    simp only [stdAxiomOk_sorry _ c hs, Bool.false_eq_true, ite_false, ite_eq_right h3, ite_eq_right h4,
      ite_eq_right h5, ite_eq_left hs] at h ⊢
    simp only [pure, Except.pure] at h ⊢
    split at h
    · rename_i hb; simp only [hb, ite_true, Except.ok.injEq] at h ⊢; exact ⟨h.symm, trivial⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at h
theorem checkDecl_sorry_fresh (F : Nat) (pins : List NatOpPinSet) (env : Env) (c : ConstantVal)
    (hs : c.name = sorryAxName) {E : Env}
    (h : checkDecl .verified (fueledOps .verified F) pins env (.axiomDecl c) = .ok E) : env.find? c.name = none := by
  unfold checkDecl checkDeclKind at h
  have hq : ¬ (c.name = quotSoundName) := by rw [hs]; decide
  simp only [ite_eq_right hq, bind, Except.bind] at h
  cases hc : checkConstantVal (fueledOps .verified F) env c false false true with
  | error e => rw [hc] at h; cases h
  | ok u => exact (checkConstantVal_res F env c false false true hc).2

/-! ## Quotient records -/

/-- `Quot.mk`, when stored, is a constructor (the quotient recursors' rules name it). -/
def QuotMkCtor (env : Env) : Prop :=
  ∀ ci, env.find? quotMkName = some ci → ∃ cv nP nF T, ci = .ctorInfo cv nP nF T

theorem quotMkCtor_empty : QuotMkCtor Env.empty := fun ci h => by simp [Env.empty, Env.find?] at h

/-- `envExt_cons` for a constant whose rules (if a recursor) name stored constructors. -/
theorem envExt_cons' (hx : EnvExt env₁ env₂) (hw2 : EnvWF env₂) (c : ConstantInfo)
    (hf1 : env₁.find? c.name = none) (hf2 : env₂.find? c.name = none) (hwE : EnvWF ⟨c :: env₁.consts, env₁.tables⟩)
    (hn : NameOK c.name) (hrc : ∀ cv mI rP isK rules, c = .recInfo cv mI rP isK rules → ∀ r ∈ rules,
      ∃ cvj cnP cnF T, env₁.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF T)) :
    EnvExt ⟨c :: env₁.consts, env₁.tables⟩ ⟨c :: env₂.consts, env₂.tables⟩ := by
  have fc : ∀ (e : Env) (n : Name), n ≠ c.name → Env.find? ⟨c :: e.consts, e.tables⟩ n = e.find? n := by
    intro e n hne; rw [Env.find?_cons, ite_eq_right (fun h => hne h.symm)]
  refine ⟨fun n ci h => ?_, fun T hT => ?_, ?_⟩
  · by_cases e : n = c.name
    · subst e; rw [Env.find?_cons_self] at h ⊢; exact h
    · rw [fc _ _ e] at h ⊢; exact hx.find n ci h
  · rw [EnvWF.findTable?_cons hw2 hf2, EnvWF.findTable?_cons hx.facts.wf hf1]
    by_cases e : T = c.name
    · subst e; simp [Env.findTable?, hf1, hf2]
    · rw [fc _ _ e] at hT; exact hx.table T hT
  · obtain ⟨hwf, hnat, hrc0, htc, hbool⟩ := hx.facts
    obtain ⟨hop, hred, h1, h2, h3, h4, h5⟩ := hn
    have nOp : ∀ m ∈ natOpNames, m ≠ c.name := fun m hm e => by
      subst e; simp [natOpName, List.contains_iff_mem, hm] at hop
    refine ⟨hwE, ?_, ?_, ?_, ?_⟩
    · rw [fc _ _ (Ne.symm h1), fc _ _ (Ne.symm h2), fc _ _ (Ne.symm h3)]; exact hnat
    · intro n cv mI rP isK rules hn' r hr
      by_cases hne : n = c.name
      · subst hne
        rw [Env.find?_cons_self] at hn'
        obtain ⟨cvj, cnP, cnF, T, hj⟩ := hrc cv mI rP isK rules (Option.some.inj hn') r hr
        have hne2 : RecRule.ctor r ≠ c.name := by intro e; rw [e, hf1] at hj; cases hj
        exact ⟨cvj, cnP, cnF, T, by rw [fc _ _ hne2]; exact hj⟩
      · rw [fc _ _ hne] at hn'
        obtain ⟨cvj, cnP, cnF, T, hj⟩ := hrc0 n cv mI rP isK rules hn' r hr
        have hne2 : RecRule.ctor r ≠ c.name := by intro e; rw [e, hf1] at hj; cases hj
        exact ⟨cvj, cnP, cnF, T, by rw [fc _ _ hne2]; exact hj⟩
    · intro T tbl hT
      rw [EnvWF.findTable?_cons hx.facts.wf hf1] at hT
      obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp (htc T tbl hT)
      rw [Env.find?_cons]; split <;> simp [hci]
    · rw [fc _ _ (nOp _ (by simp [natOpNames])), fc _ _ (nOp _ (by simp [natOpNames])),
        fc _ _ (Ne.symm h4), fc _ _ (Ne.symm h5)]; exact hbool

/-- A pin hit names the record at its pin's name. -/
theorem quotHit_name {k : QuotKind} {c : ConstantVal} (h : quotPinHit k c = true) : c.name = (quotAt k c).name := by
  simp only [quotPinHit, Bool.and_eq_true] at h
  have e := ConstantVal.eq_of_beqP h.2
  rw [show (quotAt k c).name = (quotPin k).name from atLps_name _ _, e]
  rfl

/-- The pinned quotient names' properties the extension reads (none an operation or a literal name). -/
theorem quotAt_nameOK (k : QuotKind) (c : ConstantVal) : NameOK (quotAt k c).name := by
  rw [show (quotAt k c).name = (quotPin k).name from atLps_name _ _]
  cases k <;> refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- A quotient record's check: the pin hit, the predecessors, the install. -/
theorem checkDecl_quot_inv {F : Nat} {pins : List NatOpPinSet} {env E : Env} {k : QuotKind} {c : ConstantVal}
    (h : checkDecl .verified (fueledOps .verified F) pins env (.quotDecl k c) = .ok E) :
    quotPinHit k c = true ∧ quotPredsOk env.find? k = true ∧ env.find? (quotAt k c).name = none ∧
      E = ⟨quotAt k c :: env.consts, env.tables⟩ := by
  unfold checkDecl checkDeclKind checkQuotRecord installBasisDecl at h
  simp only [bind, Except.bind] at h
  by_cases h1 : quotPinHit k c = true
  · by_cases h2 : quotPredsOk env.find? k = true
    · by_cases h3 : (env.find? (quotAt k c).name).isNone = true
      · simp only [h1, h2, h3, Bool.not_true, Bool.false_eq_true, ite_false, pure, Except.pure] at h
        simp only [basisNamesOk, ite_true] at h
        refine ⟨h1, h2, by simpa using h3, ?_⟩
        simpa using h.symm
      · simp [h1, h2, h3, throw, throwThe, MonadExceptOf.throw] at h
    · simp [h1, h2, throw, throwThe, MonadExceptOf.throw] at h
  · simp [h1, throw, throwThe, MonadExceptOf.throw] at h

theorem checkDecl_quot_ext (hx : EnvExt env₁ env₂) (hw2 : EnvWF env₂) (F : Nat) (pins pins' : List NatOpPinSet)
    (k : QuotKind) (c : ConstantVal) (hf2 : env₂.find? (quotAt k c).name = none) (hq : QuotMkCtor env₁) {E : Env}
    (h : checkDecl .verified (fueledOps .verified F) pins env₁ (.quotDecl k c) = .ok E) :
    ∃ E₂, checkDecl .verified (fueledOps .verified F) pins' env₂ (.quotDecl k c) = .ok E₂ ∧ EnvExt E E₂ ∧ EnvWF E₂ ∧
      E = ⟨quotAt k c :: env₁.consts, env₁.tables⟩ ∧ E₂ = ⟨quotAt k c :: env₂.consts, env₂.tables⟩ := by
  have hwE : EnvWF E := ConLeche.Semantics.checkDecl_envWF hx.facts.wf h
  obtain ⟨hhit, hpred, hf1, rfl⟩ := checkDecl_quot_inv h
  have hpred2 : quotPredsOk env₂.find? k = true := by
    have hs : ∀ n, (env₁.find? n).isSome = true → (env₂.find? n).isSome = true := fun n hn => by
      rw [hx.find_of_isSome hn]; exact hn
    cases k <;> simp only [quotPredsOk, Bool.and_eq_true] at hpred ⊢ <;> simp_all
  have h2 : checkDecl .verified (fueledOps .verified F) pins' env₂ (.quotDecl k c) =
      .ok ⟨quotAt k c :: env₂.consts, env₂.tables⟩ := by
    unfold checkDecl checkDeclKind checkQuotRecord installBasisDecl
    simp [bind, Except.bind, hhit, hpred2, hf2, basisNamesOk, pure, Except.pure]
  refine ⟨_, h2, envExt_cons' hx hw2 _ hf1 hf2 hwE (quotAt_nameOK k c) ?_, ConLeche.Semantics.checkDecl_envWF hw2 h2,
    rfl, rfl⟩
  intro cv mI rP isK rules he r hr
  have hM : (env₁.find? quotMkName).isSome = true ∧ RecRule.ctor r = quotMkName := by
    cases k <;> simp [quotAt, quotPin, ConstantInfo.atLps, BasisKind.decls, QuotKind.slot,
      quotBasis, quotA, quotMkA, quotLiftA, quotIndA, quotSoundA] at he
    all_goals (obtain ⟨-, -, -, -, hrules⟩ := he
               subst hrules
               simp only [List.mem_singleton] at hr
               subst hr
               simp only [quotPredsOk, Bool.and_eq_true] at hpred
               exact ⟨by simp_all, rfl⟩)
  obtain ⟨hs, hc⟩ := hM
  obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨cvj, cnP, cnF, T, rfl⟩ := hq ci hci
  exact ⟨cvj, cnP, cnF, T, by rw [hc]; exact hci⟩

theorem checkDecl_basis {F : Nat} {pins : List NatOpPinSet} {env E : Env} {d : Declaration}
    (h : checkDecl .verified (fueledOps .verified F) pins env d = .ok E) : basisNamesOk d = true := by
  unfold checkDecl at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · by_cases hb : basisNamesOk d = true
    · exact hb
    · simp [hb, throw, throwThe, MonadExceptOf.throw] at h

theorem quotMkCtor_cons {env : Env} {c : ConstantInfo} (hq : QuotMkCtor env)
    (hc : c.name = quotMkName → ∃ cv nP nF T, c = .ctorInfo cv nP nF T) : QuotMkCtor ⟨c :: env.consts, env.tables⟩ := by
  intro ci h
  rw [Env.find?_cons] at h
  split at h
  · rename_i he; simp only [Option.some.injEq] at h; subst h; exact hc he
  · exact hq ci h

theorem quotMkCtor_quot {env : Env} (k : QuotKind) (c : ConstantVal) (hq : QuotMkCtor env) :
    QuotMkCtor ⟨quotAt k c :: env.consts, env.tables⟩ :=
  quotMkCtor_cons hq (fun he => by
    rw [show (quotAt k c).name = (quotPin k).name from atLps_name _ _] at he
    cases k <;> first
      | (exact absurd he (by decide))
      | (simp [quotAt, quotPin, ConstantInfo.atLps, BasisKind.decls, QuotKind.slot,
          quotBasis, quotA, quotMkA, quotLiftA, quotIndA, quotSoundA]))

/-- The `Quot.sound` axiom record is checked as the soundness quotient record. -/
theorem checkDecl_axSound {F : Nat} {pins : List NatOpPinSet} {env : Env} {c : ConstantVal}
    (hs : c.name = quotSoundName) :
    checkDecl .verified (fueledOps .verified F) pins env (.axiomDecl c) =
      checkDecl .verified (fueledOps .verified F) pins env (.quotDecl .sound c) := by
  unfold checkDecl checkDeclKind
  simp [hs, basisNamesOk]

/-- A stream record's name: a value record's, `sorryAx` for the `sorryAx` axiom record (which
installs nothing), `Quot.sound` for its axiom record, a quotient record's. -/
def recName : Declaration → Option Name
  | .axiomDecl c => if c.name = sorryAxName ∨ c.name = quotSoundName then some c.name else none
  | .quotDecl _ c => some c.name
  | d => valName d

theorem recName_cases {d : Declaration} {n : Name} (h : recName d = some n) :
    valName d = some n ∨ (∃ c, d = .axiomDecl c ∧ c.name = sorryAxName ∧ n = c.name) ∨
      (∃ k c, d = .quotDecl k c ∧ n = c.name) ∨ (∃ c, d = .axiomDecl c ∧ c.name = quotSoundName ∧ n = c.name) := by
  cases d with
  | axiomDecl c =>
    simp only [recName] at h
    split at h
    · rename_i hs
      simp only [Option.some.injEq] at h
      rcases hs with hs | hs
      · exact Or.inr (Or.inl ⟨c, rfl, hs, h.symm⟩)
      · exact Or.inr (Or.inr (Or.inr ⟨c, rfl, hs, h.symm⟩))
    · cases h
  | quotDecl k c => simp only [recName, Option.some.injEq] at h; exact Or.inr (Or.inr (Or.inl ⟨k, c, rfl, h.symm⟩))
  | _ => exact Or.inl h

/-- The stream's records: value records, or the `sorryAx` axiom record, at names the environment's guards
do not read and the base environment does not declare. -/
def StreamOK (envP : Env) (ds : List Declaration) : Prop :=
  ∀ d ∈ ds, ∃ n, recName d = some n ∧ NameOK n ∧ envP.find? n = none

/-- **An accepting run over value records carries over to an extension.** -/
theorem pureRun_ext {pins pins' : List NatOpPinSet} (envP : Env) : ∀ {ds : List Declaration} {env₁ E₁ env₂ : Env},
    PureRun pins ds env₁ E₁ → EnvExt env₁ env₂ → EnvWF env₂ → StreamOK envP ds → QuotMkCtor env₁ →
    (∀ m, env₁.find? m = none → envP.find? m = none → env₂.find? m = none) →
    ∃ E₂, PureRun pins' ds env₂ E₂
  | _, _, _, _, .nil _, _, _, _, _, _ => ⟨_, .nil _⟩
  | d :: ds, env₁, _, env₂, .cons ⟨F, hs⟩ rest, hx, hw2, hok, hq, hinv => by
    obtain ⟨n, hd', hn, hP⟩ := hok d (List.mem_cons_self ..)
    rcases recName_cases hd' with hd | ⟨c, rfl, hsn, rfl⟩ | ⟨k, c, rfl, rfl⟩ | ⟨c, rfl, hqs, rfl⟩
    · have hf1 := checkDecl_val_fresh F pins env₁ d n hd hs
      obtain ⟨E₂, h2, hx', hw', c, hc, -, e1, e2⟩ :=
        checkDecl_ext hx hw2 F pins pins' d n hd (hinv n hf1 hP) hn hs
      have hb := checkDecl_basis hs
      obtain ⟨E₃, hr⟩ := pureRun_ext envP rest hx' hw' (fun d' hd' => hok d' (List.mem_cons_of_mem _ hd'))
        (by
          rw [e1]
          refine quotMkCtor_cons hq (fun he => ?_)
          have hn' : n = quotMkName := hc ▸ he
          subst hn'
          exfalso
          cases d <;> simp only [valName, Option.some.injEq, reduceCtorEq] at hd <;>
            simp only [basisNamesOk, hd] at hb <;> exact absurd hb (by decide)) (by
        intro m hm1 hmP
        subst e1 e2
        rw [Env.find?_cons] at hm1 ⊢
        split at hm1
        · cases hm1
        · rename_i hne; rw [ite_eq_right hne]; exact hinv m hm1 hmP)
      exact ⟨E₃, .cons ⟨F, h2⟩ hr⟩
    · have hf1 := checkDecl_sorry_fresh F pins env₁ c hsn hs
      obtain ⟨rfl, h2⟩ := checkDecl_sorry_ext hx F pins pins' c hsn (hinv _ hf1 hP) hs
      obtain ⟨E₃, hr⟩ := pureRun_ext envP rest hx hw2 (fun d' hd'' => hok d' (List.mem_cons_of_mem _ hd'')) hq hinv
      exact ⟨E₃, .cons ⟨F, h2⟩ hr⟩
    · obtain ⟨hhit, -, hf1, -⟩ := checkDecl_quot_inv hs
      have hnm := quotHit_name hhit
      obtain ⟨E₂, h2, hx', hw', e1, e2⟩ :=
        checkDecl_quot_ext hx hw2 F pins pins' k c (hinv _ hf1 (by rw [← hnm]; exact hP)) hq hs
      obtain ⟨E₃, hr⟩ := pureRun_ext envP rest hx' hw' (fun d' hd' => hok d' (List.mem_cons_of_mem _ hd'))
        (by rw [e1]; exact quotMkCtor_quot k c hq) (by
          intro m hm1 hmP
          subst e1 e2
          rw [Env.find?_cons] at hm1 ⊢
          split at hm1
          · cases hm1
          · rename_i hne; rw [ite_eq_right hne]; exact hinv m hm1 hmP)
      exact ⟨E₃, .cons ⟨F, h2⟩ hr⟩
    · rw [checkDecl_axSound hqs] at hs
      obtain ⟨hhit, -, hf1, -⟩ := checkDecl_quot_inv hs
      have hnm := quotHit_name hhit
      obtain ⟨E₂, h2, hx', hw', e1, e2⟩ :=
        checkDecl_quot_ext hx hw2 F pins pins' .sound c (hinv _ hf1 (by rw [← hnm]; exact hP)) hq hs
      obtain ⟨E₃, hr⟩ := pureRun_ext envP rest hx' hw' (fun d' hd' => hok d' (List.mem_cons_of_mem _ hd'))
        (by rw [e1]; exact quotMkCtor_quot .sound c hq) (by
          intro m hm1 hmP
          subst e1 e2
          rw [Env.find?_cons] at hm1 ⊢
          split at hm1
          · cases hm1
          · rename_i hne; rw [ite_eq_right hne]; exact hinv m hm1 hmP)
      exact ⟨E₃, .cons ⟨F, by rw [checkDecl_axSound hqs]; exact h2⟩ hr⟩

/-- **The prelude, then the stream.**  An accepting run of the prelude from the empty environment
and an accepting run of the stream from the empty environment (at any pins) give an accepting run
of the prelude followed by the stream, when the stream's records are value records at names the
prelude's environment does not declare and the guards do not read. -/
theorem prelude_then_stream (pins pins₀ : List NatOpPinSet) (P S : List Declaration) {envP E₁ : Env}
    (hP : PureRun pins P Env.empty envP) (hS : PureRun pins₀ S Env.empty E₁) (hok : StreamOK envP S) :
    ∃ E, PureRun pins (P ++ S) Env.empty E := by
  have hwP := pureRun_envWF hP ConLeche.Semantics.EnvWF.empty
  obtain ⟨E₂, h2⟩ := pureRun_ext (pins' := pins) envP hS (envExt_empty envP) hwP hok quotMkCtor_empty (fun _ _ h => h)
  exact ⟨E₂, pureRun_append hP h2⟩

end ConPanqueque.Pipeline
