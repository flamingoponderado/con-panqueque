import ConPanqueque.T.Blk
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

/-!
# Calls of any arity

`specR_callNIM` / `specR_callNIH`: `x := f(e₁, …, eₙ); rest` for a parameter list `ps` and argument
values `vs`, the callee entered with `ps[i] ↦ vs[i]`.
-/

namespace ConPanqueque.T

variable {σ : Type}

theorem foldl_upd_notin {V : Type} (L : List (MlS × V)) (m0 : MlS → Option V) (x : MlS)
    (hx : x ∉ L.map Prod.fst) :
    (L.foldl (fun (map : MlS → Option V) (entry : MlS × V) =>
      fun cur => if cur = entry.1 then some entry.2 else map cur) m0) x = m0 x := by
  induction L generalizing m0 with
  | nil => rfl
  | cons p L ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    simp only [List.foldl_cons]
    rw [ih _ hx.2]
    simp [Ne.symm hx.1, hx.1]

theorem foldl_upd_get {V : Type} (L : List (MlS × V)) (m0 : MlS → Option V) (x : MlS) (v : V)
    (hnd : (L.map Prod.fst).Nodup) (hm : (x, v) ∈ L) :
    (L.foldl (fun (map : MlS → Option V) (entry : MlS × V) =>
      fun cur => if cur = entry.1 then some entry.2 else map cur) m0) x = some v := by
  induction L generalizing m0 with
  | nil => simp at hm
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hm with e | e
    · cases e
      rw [foldl_upd_notin L _ x hnd.1]; simp
    · exact ih _ hnd.2 e

/-- Pointwise over an argument list and its values (same length). -/
def EvAll (P : ExpHOL 64 → BitVec 64 → Prop) : List (ExpHOL 64) → List (BitVec 64) → Prop
  | [], [] => True
  | e :: es, v :: vs => P e v ∧ EvAll P es vs
  | _, _ => False

theorem evAll_imp {P Q : ExpHOL 64 → BitVec 64 → Prop} (hpq : ∀ e v, P e v → Q e v) :
    ∀ es vs, EvAll P es vs → EvAll Q es vs
  | [], [], _ => trivial
  | _ :: es, _ :: vs, ⟨h1, h2⟩ => ⟨hpq _ _ h1, evAll_imp hpq es vs h2⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem evalList_words (t : PState σ) : ∀ (es : List (ExpHOL 64)) (vs : List (BitVec 64)),
    EvAll (fun e v => EV t e = some (.val (.word v))) es vs →
    evalListHOLFinite t (h := fun a => Classical.propDecidable (t.memaddrs a)) es =
      some (vs.map fun v => .val (.word v))
  | [], [], _ => rfl
  | e :: es, v :: vs, ⟨he, h⟩ => by
    have ih := evalList_words t es vs h
    simp only [evalListHOLFinite] at ih ⊢
    simp only [evalListHOLExact, List.map_cons]
    simp only [EV] at he
    rw [he, ih]
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

theorem lookupCodeN (s : PState σ) (f : MlS) (ps : List MlS) (body : ProgHOL 64) (vs : List (BitVec 64))
    (hnd : ps.Nodup) (hl : vs.length = ps.length)
    (hcode : s.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), body, .one)) :
    ∃ callee, lookupCodeHOLFinite s.code.lookup f (vs.map fun v => .val (.word v)) = some (body, callee, .one) ∧
      ∀ i (hi : i < ps.length), callee.lookup ps[i] = some (.val (.word (vs[i]'(by omega)))) := by
  have hall : ((ps.map fun p => (p, ShapeHOL.one)).zip (vs.map fun v => ValueHOL.val (HolWordLab.word v))).all
      (fun pair => shapeEqHOL pair.1.2 (shapeOfHOLExact pair.2)) = true := by
    rw [List.all_eq_true]
    intro q hq
    obtain ⟨⟨p, sh⟩, w⟩ := q
    have h1 := (List.of_mem_zip hq).1
    have h2 := (List.of_mem_zip hq).2
    simp only [List.mem_map] at h1 h2
    obtain ⟨_, _, e1⟩ := h1
    obtain ⟨_, _, e2⟩ := h2
    cases e1; cases e2
    simp [shapeOfHOLExact, shapeEqHOL]
  have hmf : (ps.map fun p => (p, ShapeHOL.one)).map Prod.fst = ps := by simp [List.map_map, Function.comp_def]
  unfold lookupCodeHOLFinite
  split
  · rename_i hh
    simp only [lookupCodeHOLExact, hcode, hmf, hnd, List.length_map, hl, hall, and_self, ite_true] at hh
    exact absurd hh (by simp)
  · rename_i b cl rs hh
    simp only [lookupCodeHOLExact, hcode, hmf, hnd, List.length_map, hl, hall, and_self, ite_true,
      Option.some.injEq, Prod.mk.injEq] at hh
    obtain ⟨rfl, rfl, rfl⟩ := hh
    refine ⟨_, rfl, fun i hi => ?_⟩
    exact foldl_upd_get _ _ _ _ (by rw [List.map_fst_zip (by simp [hl])]; exact hnd)
      (by rw [List.mem_iff_getElem]; exact ⟨i, by simp [hl]; omega, by simp⟩)

/-- A call with any number of word parameters, the callee seeing the caller's known memory words. -/
theorem specR_callNIM {α β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {k : α → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f : MlS) (ps : List MlS) (es : List (ExpHOL 64)) (B : ProgHOL 64) (vs : List (BitVec 64))
    (hnd : ps.Nodup) (hl : vs.length = ps.length)
    (hx : x ∈ D) (hC : C.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), B, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs)
    (Rf : α → BitVec 64 → AState → PState σ → Prop) (hRf : ∀ a w s' st, Rf a w s' st → SR C s' st)
    (hB : ∀ u : PState σ, SR C s u → (∀ a v, (a, v) ∈ M → u.memaddrs a ∧ u.memory a = .word v) →
      (∀ i (hi : i < ps.length), u.locals.lookup ps[i] = some (.val (.word (vs[i]'(by omega))))) →
      SpecR (· = u) B s m Rf)
    (hk : ∀ a w s' (st : PState σ), Rf a w s' st → SpecR (Inv C s' ((x, w) :: Γ) [] D) rest s' (k a) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f es) rest) s (m >>= k) R := by
  intro t ht
  obtain ⟨cal, hlk, hcal⟩ := lookupCodeN t f ps B vs hnd hl (by rw [ht.sr.code]; exact hC)
  have hc := spec_callN (P := (· = t)) (s := s) (m := m)
    (Q := fun a s' t' => ∃ w st, Rf a w s' st ∧ Inv C s' ((x, w) :: Γ) [] D t')
    x f es B (fun _ => vs.map fun v => .val (.word v)) (fun _ => cal)
    (fun u hu => by subst hu; exact evalList_words u es vs (evAll_imp (fun e v h => inv_ev ht h) es vs hes))
    (fun u hu => by subst hu; exact hlk) (fun u hu => by rw [hu]; exact ht.decl x hx) (fun _ => Rf)
    (fun u hu => by
      subst hu
      exact hB _ (sr_of_eq ht.sr rfl rfl rfl rfl) (fun a v ha => ht.mem a v ha) hcal)
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
  exact specR_bind (Q1 := fun a s' t' => ∃ w st, Rf a w s' st ∧ Inv C s' ((x, w) :: Γ) [] D t') hc
    (fun a s' u ⟨w, st, hr, hu⟩ => hk a w s' st hr u hu) t rfl

/-- A call with any number of word parameters where the callee may grow the heap: the continuation runs at
the image the callee's post names. -/
theorem specR_callNIH {α β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {k : α → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (x f : MlS) (ps : List MlS) (es : List (ExpHOL 64)) (B : ProgHOL 64) (vs : List (BitVec 64))
    (hnd : ps.Nodup) (hl : vs.length = ps.length)
    (hx : x ∈ D) (hC : C.code.lookup f = some (ps.map (fun p => (p, ShapeHOL.one)), B, .one))
    (hes : EvAll (fun e v => sev Γ e = some v) es vs)
    (Rf : α → BitVec 64 → AState → PState σ → Prop) (Qx : α → BitVec 64 → AState → List (BitVec 64) → Prop)
    (hRf : ∀ a w s' st, Rf a w s' st → ∃ H', C.H <+: H' ∧ Qx a w s' H' ∧ SR (ctxH C H') s' st)
    (hB : ∀ u : PState σ, SR C s u → (∀ a v, (a, v) ∈ M → u.memaddrs a ∧ u.memory a = .word v) →
      (∀ i (hi : i < ps.length), u.locals.lookup ps[i] = some (.val (.word (vs[i]'(by omega))))) →
      SpecR (· = u) B s m Rf)
    (hk : ∀ a w s' H', C.H <+: H' → Qx a w s' H' →
      SpecR (Inv (ctxH C H') s' ((x, w) :: Γ) [] D) rest s' (k a) R) :
    SpecR (Inv C s Γ M D) (.seq (.call (some (some (.local, x), none)) f es) rest) s (m >>= k) R := by
  intro t ht
  obtain ⟨cal, hlk, hcal⟩ := lookupCodeN t f ps B vs hnd hl (by rw [ht.sr.code]; exact hC)
  have hc := spec_callN (P := (· = t)) (s := s) (m := m)
    (Q := fun a s' t' => ∃ w H', C.H <+: H' ∧ Qx a w s' H' ∧ Inv (ctxH C H') s' ((x, w) :: Γ) [] D t')
    x f es B (fun _ => vs.map fun v => .val (.word v)) (fun _ => cal)
    (fun u hu => by subst hu; exact evalList_words u es vs (evAll_imp (fun e v h => inv_ev ht h) es vs hes))
    (fun u hu => by subst hu; exact hlk) (fun u hu => by rw [hu]; exact ht.decl x hx) (fun _ => Rf)
    (fun u hu => by
      subst hu
      exact hB _ (sr_of_eq ht.sr rfl rfl rfl rfl) (fun a v ha => ht.mem a v ha) hcal)
    (fun u hu a w s' st hr => by
      subst hu
      obtain ⟨H', hp, hq, hs⟩ := hRf a w s' st hr
      refine ⟨w, H', hp, hq, ⟨sr_of_eq hs rfl rfl rfl rfl, fun y v hy => ?_, fun _ _ h => absurd h (by simp),
        fun y hy => ?_⟩⟩
      · simp only [setKvarHOLFinite, Env.get] at hy ⊢
        split at hy
        · rename_i e; subst e; simp at hy; subst hy; exact lookup_setVar_same _ _ _
        · rename_i e; rw [lookup_setVar_other _ _ e]; exact ht.env y v hy
      · simp only [setKvarHOLFinite]
        by_cases e : y = x
        · subst e; exact ⟨w, lookup_setVar_same _ _ _⟩
        · rw [lookup_setVar_other _ _ e]; exact ht.decl y hy)
  exact specR_bind (Q1 := fun a s' t' => ∃ w H', C.H <+: H' ∧ Qx a w s' H' ∧ Inv (ctxH C H') s' ((x, w) :: Γ) [] D t')
    hc (fun a s' u ⟨w, H', hp, hq, hu⟩ => hk a w s' H' hp hq u hu) t rfl

/-- A callee entry state binding `ps[i] ↦ vs[i]` satisfies `Pre` for the zipped environment. -/
theorem pre_of_lookups {C : Ctx} {s : AState} {u : PState σ} (hu : SR C s u) (ps : List MlS) (vs : List (BitVec 64))
    (hl : vs.length = ps.length)
    (h : ∀ i (hi : i < ps.length), u.locals.lookup ps[i] = some (.val (.word (vs[i]'(by omega))))) :
    Pre C s (ps.zip vs) u := by
  refine ⟨hu, fun y w hy => ?_⟩
  induction ps generalizing vs with
  | nil => simp [Env.get] at hy
  | cons p ps ih =>
    cases vs with
    | nil => simp at hl
    | cons v vs =>
      simp only [List.zip_cons_cons, Env.get] at hy
      split at hy
      · rename_i e; subst e; simp at hy; subst hy; exact h 0 (by simp)
      · exact ih vs (by simpa using hl) (fun i hi => h (i + 1) (by simp; omega)) hy

end ConPanqueque.T
