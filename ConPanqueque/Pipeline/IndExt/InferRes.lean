import ConLeche.Verify.EnvExt
import ConLeche.Verify.ExceptBind

/-! # A full-grade inference that succeeds saw every constant

`inferBody` (official's `infer_type_core` with `infer_only = false`) visits every subterm of its
input except free variables' annotations: a constant is looked up, a literal needs its basis stored,
a projection its table.  So an accepting inference, on a term whose free variables' annotations
resolve, shows the term resolves (`infer_ok_res`). -/

namespace ConPanqueque.Pipeline.IndExt

open ConLeche ConLeche.Verify

set_option autoImplicit false

/-- Every free variable's annotation in `e` resolves. -/
def FvRes (env : Env) : Expr → Prop
  | .fvar _ ty => Res env ty
  | .app f a => FvRes env f ∧ FvRes env a
  | .lam ty b | .forallE ty b => FvRes env ty ∧ FvRes env b
  | .letE ty v b => FvRes env ty ∧ FvRes env v ∧ FvRes env b
  | .proj _ _ e => FvRes env e
  | _ => True

theorem fvRes_of_res {env : Env} : ∀ {e : Expr}, Res env e → FvRes env e
  | .bvar _, _ | .sort _, _ | .const _ _, _ | .lit _, _ => trivial
  | .fvar _ _, h => res_fvar.mp h
  | .app _ _, h => ⟨fvRes_of_res (res_app.mp h).1, fvRes_of_res (res_app.mp h).2⟩
  | .lam _ _, h => ⟨fvRes_of_res (res_lam.mp h).1, fvRes_of_res (res_lam.mp h).2⟩
  | .forallE _ _, h => ⟨fvRes_of_res (res_forall.mp h).1, fvRes_of_res (res_forall.mp h).2⟩
  | .letE _ _ _, h => ⟨fvRes_of_res (res_let.mp h).1, fvRes_of_res (res_let.mp h).2.1,
      fvRes_of_res (res_let.mp h).2.2⟩
  | .proj _ _ e, h => by simp only [FvRes]; exact fvRes_of_res (e := e) (res_proj.mp h).2

theorem fvRes_instantiate1 {env : Env} {v : Expr} (hv : FvRes env v) :
    ∀ (e : Expr) (k : Nat), FvRes env e → FvRes env (e.instantiate1 v k)
  | .bvar i, k, _ => by
    simp only [Expr.instantiate1]
    split
    · exact hv
    · split <;> trivial
  | .sort _, _, _ | .const _ _, _, _ | .lit _, _, _ => trivial
  | .fvar _ _, _, h => h
  | .app f a, k, h => ⟨fvRes_instantiate1 hv f k h.1, fvRes_instantiate1 hv a k h.2⟩
  | .lam t b, k, h => ⟨fvRes_instantiate1 hv t k h.1, fvRes_instantiate1 hv b (k + 1) h.2⟩
  | .forallE t b, k, h => ⟨fvRes_instantiate1 hv t k h.1, fvRes_instantiate1 hv b (k + 1) h.2⟩
  | .letE t w b, k, h => ⟨fvRes_instantiate1 hv t k h.1, fvRes_instantiate1 hv w k h.2.1,
      fvRes_instantiate1 hv b (k + 1) h.2.2⟩
  | .proj _ _ e, k, h => fvRes_instantiate1 hv e k h

/-- An instantiation resolves only where the term does. -/
theorem res_of_instantiate1 {env : Env} {v : Expr} :
    ∀ (e : Expr) (k : Nat), Res env (e.instantiate1 v k) → Res env e
  | .bvar i, _, _ => rfl
  | .sort _, _, _ => rfl
  | .const _ _, _, h => h
  | .lit _, _, h => h
  | .fvar _ _, _, h => h
  | .app f a, k, h => by
    have h' := res_app.mp h
    exact res_app.mpr ⟨res_of_instantiate1 f k h'.1, res_of_instantiate1 a k h'.2⟩
  | .lam t b, k, h => by
    have h' := res_lam.mp h
    exact res_lam.mpr ⟨res_of_instantiate1 t k h'.1, res_of_instantiate1 b (k + 1) h'.2⟩
  | .forallE t b, k, h => by
    have h' := res_forall.mp h
    exact res_forall.mpr ⟨res_of_instantiate1 t k h'.1, res_of_instantiate1 b (k + 1) h'.2⟩
  | .letE t w b, k, h => by
    have h' := res_let.mp h
    exact res_let.mpr ⟨res_of_instantiate1 t k h'.1, res_of_instantiate1 w k h'.2.1,
      res_of_instantiate1 b (k + 1) h'.2.2⟩
  | .proj s i e, k, h => by
    have h' := res_proj.mp h
    exact res_proj.mpr ⟨h'.1, res_of_instantiate1 e k h'.2⟩

theorem findProj_isSome {env : Env} {T : Name} {i : Nat} {e : ProjEntry} (h : env.findProj? T i = some e) :
    (env.find? T).isSome = true := by
  obtain ⟨tbl, hT, -⟩ := Env.findProj?_some h
  unfold Env.findTable? at hT
  split at hT
  · assumption
  · cases hT

/-- **An accepting full-grade inference saw every constant.** -/
theorem infer_ok_res (mode : CheckMode) (eager : Bool) (env : Env) :
    ∀ (fuel d : Nat) (e t : Expr), FvRes env e →
      (pureFns mode eager env fuel).infer d e = .ok t → Res env e
  | 0, _, _, _, _, h => by
    simp [pureFns, coreKnot, throw, throwThe, MonadExceptOf.throw] at h
  | fuel + 1, d, e, t, hf, h => by
    have ih := infer_ok_res mode eager env fuel
    change inferBody (coreKnot mode eager env id fuel) env d e = (Except.ok t : CheckM Expr) at h
    have hk : ∀ d' e' t', FvRes env e' → (coreKnot mode eager env id fuel).infer d' e' = (Except.ok t' : CheckM Expr) → Res env e' :=
      fun d' e' t' hf' h' => ih d' e' t' hf' h'
    unfold inferBody at h
    cases e with
    | bvar i => simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    | sort u => exact res_sort
    | fvar i ty => exact res_fvar.mpr hf
    | const n us =>
      simp only [bind, Except.bind] at h
      split at h
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
      · rename_i ci hci
        show (env.find? n).isSome = true
        rw [hci]; rfl
    | lit l =>
      cases l with
      | natVal k =>
        simp only [bind, Except.bind] at h
        split at h
        · rename_i hs
          simp only [natLitStored, Bool.and_eq_true] at hs
          simp [Res, Expr.constsResolve, hs.1.1, hs.1.2, hs.2]
        · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
      | strVal s =>
        simp only [bind, Except.bind] at h
        split at h
        · rename_i hs
          simp only [strLitStored, natLitStored, Bool.and_eq_true] at hs
          simp [Res, Expr.constsResolve, hs]
        · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    | app f a =>
      obtain ⟨tf, hf1, h⟩ := exceptBind_ok h
      obtain ⟨w, -, h⟩ := exceptBind_ok h
      split at h
      · obtain ⟨ta, ha, -⟩ := exceptBind_ok h
        exact res_app.mpr ⟨hk _ _ _ hf.1 hf1, hk _ _ _ hf.2 ha⟩
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    | forallE ty b =>
      obtain ⟨tt, ht, h⟩ := exceptBind_ok h
      have rty := hk _ _ _ hf.1 ht
      obtain ⟨w, -, h⟩ := exceptBind_ok h
      split at h
      · obtain ⟨tb, hb, -⟩ := exceptBind_ok h
        have := hk _ _ _ (fvRes_instantiate1 (env := env) (v := .fvar d ty) rty b 0 hf.2) hb
        exact res_forall.mpr ⟨rty, res_of_instantiate1 b 0 this⟩
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    | lam ty b =>
      obtain ⟨tt, ht, h⟩ := exceptBind_ok h
      have rty := hk _ _ _ hf.1 ht
      obtain ⟨w, -, h⟩ := exceptBind_ok h
      split at h
      · obtain ⟨tb, hb, -⟩ := exceptBind_ok h
        have := hk _ _ _ (fvRes_instantiate1 (env := env) (v := .fvar d ty) rty b 0 hf.2) hb
        exact res_lam.mpr ⟨rty, res_of_instantiate1 b 0 this⟩
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    | letE ty v b =>
      obtain ⟨tt, ht, h⟩ := exceptBind_ok h
      have rty := hk _ _ _ hf.1 ht
      obtain ⟨-, -, h⟩ := exceptBind_ok h
      obtain ⟨tv, hv, h⟩ := exceptBind_ok h
      have rv := hk _ _ _ hf.2.1 hv
      obtain ⟨bb, -, h⟩ := exceptBind_ok h
      split at h
      · have := hk _ _ _ (fvRes_instantiate1 (fvRes_of_res rv) b 0 hf.2.2) h
        exact res_let.mpr ⟨rty, rv, res_of_instantiate1 b 0 this⟩
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
    | proj sn i pe =>
      obtain ⟨tp, hp, h⟩ := exceptBind_ok h
      have rp := hk _ _ _ (by simpa only [FvRes] using hf) hp
      obtain ⟨te, -, h⟩ := exceptBind_ok h
      split at h
      · split at h
        · rename_i T us hT entry he
          split at h
          · rename_i hc
            obtain ⟨rfl, -⟩ := hc
            exact res_proj.mpr ⟨findProj_isSome he, rp⟩
          · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
        · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h
      · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at h

/-- The same at the checker's front door. -/
theorem inferType_ok_res {F d : Nat} {env : Env} {e t : Expr} (hf : FvRes env e)
    (h : (fueledOps .verified F).inferType env d e = .ok t) : Res env e :=
  infer_ok_res .verified false env F d e t hf h

end ConPanqueque.Pipeline.IndExt
