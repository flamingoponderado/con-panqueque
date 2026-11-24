import ConPanqueque.Front.DeclRel
import ConPanqueque.Scan.Safe

/-! # Definition records into the registry (`processLineCoreD` at `.defn`)

The name's, type's and value's handles from the tables, the safety (`"safe"`, else rejected), the
hint's value, the level parameters as a block of name handles, then a six-cell record and a registry
entry.  When every lookup succeeds and the safety is `safe`, the twin's step is a pure push. -/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V ConPanqueque.ConsModel ConPanqueque.ConsTbl
open ConRon.Arena ConRon.Arena.Frontend

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.Scan
open ConLeche.Frontend (IdTable CVRec DeclRec HintsRec scanNatList scanString scanHints)

variable {σ : Type}

/-- The twin's hint conversion. -/
def convHint : HintsRec → ConLeche.ReducibilityHint
  | .«abbrev» => .«abbrev»
  | .«opaque» => .«opaque»
  | .regular n => .regular n

theorem hintN_conv (x : HintsRec) : T.hintN (convHint x) = Scan.hintN x := by
  cases x <;> rfl

theorem mapM_name_ok (st : StateD) :
    ∀ (us : List Nat), (∀ j (hj : j < us.length), (st.names.get? us[j]).isSome) →
      us.mapM st.name = pure (us.map (fun x => (st.names.get? x).getD default))
  | [], _ => rfl
  | x :: xs, h => by
    have h0 := h 0 (by simp)
    simp only [List.getElem_cons_zero] at h0
    obtain ⟨hx, hhx⟩ := Option.isSome_iff_exists.mp h0
    have ih := mapM_name_ok st xs (fun j hj => by have := h (j + 1) (by simp; omega); simpa using this)
    simp [List.mapM_cons, StateD.name, hhx, ih]

/-- **The twin's step on a safe definition whose indices are all bound** is a pure push. -/
theorem processDefn_ok (st : StateD) (cv : CVRec) (vl : Nat) (hints : HintsRec) (nmh : NIdx) (tyh vlh : EIdx)
    (hnm : st.names.get? cv.name = some nmh) (hty : st.exprs.get? cv.type = some tyh)
    (hvl : st.exprs.get? vl = some vlh) (hlps : ∀ j (hj : j < cv.levelParams.length),
      (st.names.get? cv.levelParams[j]).isSome) :
    processLineCoreD st (.defn cv vl hints "safe") =
      pure (.inl { st with decls := st.decls.push (.defnDecl
        ⟨nmh, cv.levelParams.map (fun x => (st.names.get? x).getD default), tyh⟩ vlh (convHint hints)) }) := by
  have hm := mapM_name_ok st cv.levelParams hlps
  cases hints <;>
  simp [processLineCoreD, parseCVD, StateD.name, getDeclD, StateD.expr, hnm, hty, hvl, hm, pushDecl, convHint]

/-- `x := f(a₁, a₂, a₃)` at a pure callee with a determined answer, as a step. -/
theorem step_call3I {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS}
    (x f x1 x2 x3 : MlS) (body : ProgHOL 64) (a1 a2 a3 : ExpHOL 64) (v1 v2 v3 v : BitVec 64)
    (h12 : x1 ≠ x2) (h13 : x1 ≠ x3) (h23 : x2 ≠ x3) (hx : x ∈ D)
    (hcode : C.code.lookup f = some ([(x1, .one), (x2, .one), (x3, .one)], body, .one))
    (he1 : sev Γ a1 = some v1) (he2 : sev Γ a2 = some v2) (he3 : sev Γ a3 = some v3)
    (hbody : ∀ (t : PState σ) (callee : HolFiniteMapExact MlS (ValueHOL 64)), Inv C s Γ M D t →
      callee.lookup x1 = some (.val (.word v1)) → callee.lookup x2 = some (.val (.word v2)) →
      callee.lookup x3 = some (.val (.word v3)) → RetSpec (callEntryStateHOLFinite t callee) body v) :
    Step (σ := σ) (Inv C s Γ M D) (callTo x f [a1, a2, a3]) (Inv C s ((x, v) :: Γ) M D) := by
  intro t ht
  obtain ⟨w0, hw0⟩ := ht.decl x hx
  rcases call3_ret t x f x1 x2 x3 body a1 a2 a3 v1 v2 v3 v w0 h12 h13 h23 (by rw [ht.sr.code]; exact hcode)
      (inv_ev ht he1) (inv_ev ht he2) (inv_ev ht he3) hw0 (fun callee h1 h2 h3 => hbody t callee ht h1 h2 h3) with
    hs | ⟨u, hu, m1, d1, g1, c1, b1, lx, lo⟩
  · exact Or.inl hs
  simp only [callTo]
  rw [hu]
  refine Or.inr ⟨rfl, sr_of_eq ht.sr m1 d1 g1 c1, fun y v' hy => ?_, fun a v' ha => by rw [m1, d1]; exact ht.mem a v' ha,
    fun y hy => ?_⟩
  · simp only [Env.get] at hy
    split at hy
    · rename_i e; subst e; simp at hy; subst hy; exact lx
    · rename_i e; rw [lo y e]; exact ht.env y v' hy
  · by_cases e : y = x
    · subst e; exact ⟨v, lx⟩
    · rw [lo y e]; exact ht.decl y hy

/-- The heap image keeps every cell below the frontier other than the registry's. -/
def AgreeBelow (F rb capD : Nat) (H H' : List (BitVec 64)) : Prop :=
  ∀ c, c < F → (c < rb ∨ rb + 1 + capD ≤ c) → H'[c]? = H[c]?

theorem tblRel_agree {k : IdxKind} {F rb capD : Nat} {H H' : List (BitVec 64)} {j cap : Nat} {tbl : IdTable (Idx k)}
    (h : TblRel H j cap tbl) (ha : AgreeBelow F rb capD H H') (hjF : j + cap ≤ F)
    (hjr : j + cap ≤ rb ∨ rb + 1 + capD ≤ j) : TblRel H' j cap tbl :=
  ⟨fun i hi => by rw [ha (j + i) (by omega) (by omega)]; exact h.1 i hi, h.2⟩

theorem packed_agree {F rb capD : Nat} {H H' : List (BitVec 64)} {j0 : Nat} {bs : List UInt8} (h : Packed H j0 bs)
    (ha : AgreeBelow F rb capD H H') (hF : ∀ i, i < bs.length → j0 + i / 8 < F ∧ (j0 + i / 8 < rb ∨ rb + 1 + capD ≤ j0 + i / 8)) :
    Packed H' j0 bs := fun i hi => by
  obtain ⟨w, hw, hb⟩ := h i hi
  exact ⟨w, by rw [ha _ (hF i hi).1 (hF i hi).2]; exact hw, hb⟩

end ConPanqueque.Front
