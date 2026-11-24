import ConPanqueque.T.Decl.Push
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# Installing a checked constant

`fe.push ci` in the port: the constant's block is already in the environment heap (copied), its name goes into
the constant table, and the context becomes `ctxPush C ci o EH`. A call may end in another context than it
started in (the table it writes is part of the context), so the call and table-set lemmas here are stated across
two contexts.
-/

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC
open ConPanqueque.V.Enc

/-- The context after installing `ci` at environment block `o` of image `EH`. -/
def ctxPush (C : Ctx) (ci : IConstantInfo) (o : Nat) (EH : List (BitVec 64)) : Ctx :=
  { C with fe := C.fe.push ci, EH := EH, envM := C.envM.insert ci.name (ecell C o) }

theorem envRel_push {C : Ctx} (h : EnvRel C) (hg : TblGate C.fe) {ci : IConstantInfo} {o : Nat}
    {EH : List (BitVec 64)} (hp : C.EH <+: EH) (hcie : CIE C.EB EH o ci) (hnew : C.fe.find? ci.name = none) :
    EnvRel (ctxPush C ci o EH) := by
  refine ⟨fun n => ?_, fun n => ?_⟩
  · show match (C.fe.push ci).find? n with
      | none => (C.envM.insert ci.name (ecell C o))[n]? = none
      | some ci' => ∃ o', (C.envM.insert ci.name (ecell C o))[n]? = some (ecell C o') ∧ CIE C.EB EH o' ci'
    rw [IFEnv.find?_push, Std.HashMap.getElem?_insert]
    by_cases e : (ci.name == n) = true
    · simp only [e, if_true]; exact ⟨o, rfl, hcie⟩
    · have ef : (ci.name == n) = false := by simpa using e
      simp only [ef, Bool.false_eq_true, if_false]
      have := h.1 n
      revert this
      cases C.fe.find? n with
      | none => exact id
      | some ci' => exact fun ⟨o', hm, hc⟩ => ⟨o', hm, cie_mono hp hc⟩
  · show match (C.fe.push ci).findTable? n with
      | none => C.tblM[n]? = none
      | some tb => ∃ o', C.tblM[n]? = some (ecell C o') ∧ TblE C.EB EH o' tb
    rw [push_findTable hg ci hnew]
    have := h.2 n
    revert this
    cases C.fe.findTable? n with
    | none => exact id
    | some tb => exact fun ⟨o', hm, hc⟩ => ⟨o', hm, tblE_mono hp hc⟩

theorem ctxOK_push {C : Ctx} (hok : CtxOK C) (hg : TblGate C.fe) {ci : IConstantInfo} {o : Nat}
    {EH : List (BitVec 64)} (hp : C.EH <+: EH) (hcie : CIE C.EB EH o ci) (hnew : C.fe.find? ci.name = none) :
    CtxOK (ctxPush C ci o EH) := by
  have h1 := envRel_push hok.envRel hg hp hcie hnew
  have h2 : PinsE (ctxPush C ci o EH) := pinsE_E hok.pinsRel hp
  cases hok; constructor <;> first | assumption | exact h1 | exact h2

section
variable {σ : Type}

/-- A three-argument call that ends in another context `C'` (its post builds `SR C'`). -/
theorem specR_call3IMC {α β : Type} {C C' : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {k : α → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f p1 p2 p3 : MlS) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3) (e1 e2 e3 : ExpHOL 64) (B : ProgHOL 64)
    (v1 v2 v3 : BitVec 64)
    (hx : x ∈ D) (hC : C.code.lookup f = some ([(p1, .one), (p2, .one), (p3, .one)], B, .one))
    (he1 : sev Γ e1 = some v1) (he2 : sev Γ e2 = some v2) (he3 : sev Γ e3 = some v3)
    (Rf : α → BitVec 64 → AState → PState σ → Prop) (hRf : ∀ a w s' st, Rf a w s' st → SR C' s' st)
    (hB : ∀ u : PState σ, SR C s u → (∀ a v, (a, v) ∈ M → u.memaddrs a ∧ u.memory a = .word v) →
      u.locals.lookup p1 = some (.val (.word v1)) → u.locals.lookup p2 = some (.val (.word v2)) →
      u.locals.lookup p3 = some (.val (.word v3)) → SpecR (· = u) B s m Rf)
    (hk : ∀ a w s' (st : PState σ), Rf a w s' st → SpecR (Inv C' s' ((x, w) :: Γ) [] D) rest s' (k a) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f [e1, e2, e3]) rest) s (m >>= k) R := by
  intro t ht
  have hc := spec_call3 (P := (· = t)) (s := s) (m := m)
    (Q := fun a s' t' => ∃ w st, Rf a w s' st ∧ Inv C' s' ((x, w) :: Γ) [] D t')
    x f p1 p2 p3 h12 h13 h23 e1 e2 e3 B (fun _ => v1) (fun _ => v2) (fun _ => v3)
    (fun u hu => by rw [hu, ht.sr.code]; exact hC)
    (fun u hu => by rw [hu]; exact inv_ev ht he1) (fun u hu => by rw [hu]; exact inv_ev ht he2)
    (fun u hu => by rw [hu]; exact inv_ev ht he3)
    (fun u hu => by rw [hu]; exact ht.decl x hx) (fun _ => Rf)
    (fun u hu callee h1 h2 h3 => by
      subst hu; exact hB _ (sr_of_eq ht.sr rfl rfl rfl rfl) (fun a v ha => ht.mem a v ha) h1 h2 h3)
    (fun u hu a w s' st hr => by
      subst hu
      refine ⟨w, st, hr, ⟨sr_of_eq (hRf a w s' st hr) rfl rfl rfl rfl, fun y v hy => ?_, fun _ _ h => absurd h (by simp),
        fun y hy => ?_⟩⟩
      · simp only [setKvarHOLFinite, Env.get] at hy ⊢
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact lookup_setVar_same _ _ _
        · rename_i e; rw [lookup_setVar_other _ _ e]; exact ht.env y v hy
      · simp only [setKvarHOLFinite]
        by_cases e : y = x
        · subst e; exact ⟨w, lookup_setVar_same _ _ _⟩
        · rw [lookup_setVar_other _ _ e]; exact ht.decl y hy)
  exact specR_bind (Q1 := fun a s' t' => ∃ w st, Rf a w s' st ∧ Inv C' s' ((x, w) :: Γ) [] D t') hc
    (fun a s' u ⟨w, st, hr, hu⟩ => hk a w s' st hr u hu) t rfl

end


section
variable {σ : Type} {K V : Type} [BEq K] [LawfulBEq K] [Hashable K] [DecidableEq K] [Inhabited V]
  {enc : K → List (BitVec 64)} {valW : V → BitVec 64}

/-- `specR_memoSetGI`, ending in another context `C'` (the table set is part of the context). -/
theorem specR_memoSetGIC {β : Type} {C C' : Ctx} (hinj : ∀ x y, enc x = enc y → x = y)
    (G : BitVec 64) (g : VGeo) (m : Std.HashMap K V) (key : K) (v : V) (setOp : AM Unit) {s s' : AState}
    (hset : setOp s = .ok ((), s'))
    (hmem : ∀ u : PState σ, SR C s u → MemoAtG enc valW u G g m)
    (hKout : ∀ i, i < (enc key).length → ¬ inR g (C.KB + BitVec.ofNat 64 (8 * i)))
    (hGout : ∀ j, j < 8 → ¬ inR g (G + BitVec.ofNat 64 (8 * j)))
    (hsr' : ∀ u u' : PState σ, SR C s u → MemoAtG enc valW u' G g (m.insert key v) →
      (∀ c, ¬ inR g c → u'.memory c = u.memory c) → u'.memaddrs = u.memaddrs → u'.globals = u.globals →
      u'.code = u.code → SR C' s' u')
    (hcodeS : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one))
    (hcodeI : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one))
    {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {k : Unit → AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop}
    (x : MlS) (eG eL ev : ExpHOL 64) (hx : x ∈ D) (heG : sev Γ eG = some G)
    (heL : sev Γ eL = some (BitVec.ofNat 64 (enc key).length)) (hev : sev Γ ev = some (valW v))
    (hkl : (enc key).length < 2 ^ 61)
    (hW : ∀ u : PState σ, (∀ a v, (a, v) ∈ M → u.memaddrs a ∧ u.memory a = .word v) → Words u C.KB (enc key))
    (hk : ∀ w, SpecR (Inv C' s' ((x, w) :: Γ) [] D) rest s' (k ()) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) fMemoSet [eG, eL, ev]) rest) s
      (setOp >>= k) R := by
  refine specR_call3IMC (C' := C') x fMemoSet pG pLen pVal (by decide) (by decide) (by decide) eG eL ev memoSetBody G
    (BitVec.ofNat 64 (enc key).length) (valW v) hx hcodeS heG heL hev
    (fun _ _ s'' st => s'' = s' ∧ SR C' s' st) (fun _ _ _ _ hp => by rw [hp.1]; exact hp.2)
    (fun u hsr hM h1 h2 h3 => ?_) (fun a w s'' st hp => by obtain ⟨rfl, _⟩ := hp; exact hk w)
  have S := memoSet_spec (σ := σ) G C.KB g hinj m key v s u (hmem u hsr) (hW u hM) hkl hKout hGout hsr.gkb h1 h2 h3
    (by rw [hsr.code]; exact hcodeI)
  intro t ht
  rcases S t ht with hs | ⟨w, hr', _, s'', _, hp⟩
  · exact Or.inl hs
  obtain ⟨_, hmem', hfr, hd', hg, hc⟩ := hp
  subst ht
  exact Or.inr ⟨w, hr', (), s', hset, rfl, hsr' t _ hsr hmem' hfr hd' hg hc⟩

end

end ConPanqueque.T.Decl
