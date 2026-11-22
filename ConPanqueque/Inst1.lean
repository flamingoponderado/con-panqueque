import ConPanqueque.Subst
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic ConPanqueque.Alloc ConPanqueque.ExprCons
open ConPanqueque.Node ConPanqueque.StateHeap ConPanqueque.Rebuild ConPanqueque.Subst

/-!
# `Expr.instantiate1` in Pancake

An instance of the substitution template (`Subst.lean`): the value `v` is held in
the global `ivv`; at `bvar i` the case returns `v` if `i = k`, builds `bvar (i-1)`
if `i > k`, else returns the node. `inst1_spec`: the Pancake function computes
con-leche's `Expr.instantiate1` (or stops when out of arena space).
-/

namespace ConPanqueque.Inst1

def gV := ofString "ivv"
def iIv := ofString "iv"
def iI := ofString "i"
def iW := ofString "w"

/-- The leaf `bvar i`: `v` if `i = k`, `bvar (i-1)` if `i > k`, else the node. -/
def bvarCase : ProgHOL 64 :=
  .dec iIv .one (ldo iU 16)
   (.dec iI .one (.shift .lsr (vv iIv) (.const 1))
    (.ite (.cmp .equal (vv iI) (vv iK)) (.return (.var .global gV))
     (.ite (.cmp .lower (vv iK) (vv iI))
       (.dec iW .one (.op .sub [vv iIv, .const 2])
         (.dec iIw .one (.op .sub [vv iI, .const 1]) (mkNode 0 ConPanqueque.ExprData.bvarDataE [iW])))
       (.return (vv iU)))))

theorem cut_inst1 {e : ConLeche.Expr} {k : Nat} (v : ConLeche.Expr) (h : Cut e k) : e.instantiate1 v k = e := by
  apply ConLeche.Expr.instantiate1_eq_self
  rw [ConLeche.Expr.looseBVarsBounded_iff, ← ConLeche.Expr.bvarBRaw_exact e (by simp [ConLeche.satRange]; exact h.1)]
  exact h.2

def shape (v : ConLeche.Expr) : Subst.Shape where
  F e k := e.instantiate1 v k
  cut _ _ h := cut_inst1 v h
  app _ _ _ := rfl
  lam _ _ _ := rfl
  forallE _ _ _ := rfl
  letE _ _ _ _ := rfl
  proj _ _ _ _ := rfl

/-- `v` is held in the global `ivv` and represented in the arena. -/
def inv (v : ConLeche.Expr) : Subst.Inv where
  P gl hh := ∃ pv, gl gV = some (.val (.word pv)) ∧ ExprAt hh pv v
  mono gl gl' h h' := fun ⟨pv, a, b⟩ hs hg => ⟨pv, by rw [hg gV (by decide)]; exact a, exprAt_mono hs b⟩

theorem spec_bvar {σ : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (fn : MlS)
    (C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (v : ConLeche.Expr) (lo : BitVec 64) (h : Heap) (p vw : BitVec 64) (i : Nat)
    (he : ExprAt h p (.bvar i)) (h0 : h p = some (.word 0)) (h2 : h (p + 16) = some (.word vw)) (hi : NatAt h vw i) :
    Spec (σ := σ) bvarCase fn C (shape v) (inv v) lo h p (.bvar i) := by
  intro t k hp hcd hai hs hx hu hk hd hck
  obtain ⟨pv, hgv, hv⟩ := hx
  obtain ⟨_, h8⟩ := exprAt_data he
  apply entry (cases bvarCase fn) t lo hp p 0 (.bvar i) k (by omega) hai hu hk (hs _ _ h0) (hs _ _ h8)
  · intro hct; rw [(shape v).cut _ _ hct]; exact exprAt_mono hs he
  intro hct t2 cd2 m2 d2 g2 ta2 ck2 hu2 hk2
  dsimp only [shape]
  show RRes t2 (evaluateHOLFiniteState t2 bvarCase) lo hp _ _
  obtain ⟨hi63, rfl⟩ := hi
  have hO2 : hOf t2 lo hp = hOf t lo hp := hOf_of_eq lo hp m2
  have hai2 : AInv t2 lo hp := ainv_of_eq hai g2 d2 ta2
  have m16 := (ainv_arena hai2).1 _ _ (by rw [hO2]; exact hs _ _ h2)
  have hk64 : k < 2 ^ 64 := by omega
  let iw := BitVec.ofNat 64 i
  let t3 := setVarHOLFinite iIv (.val (.word (BitVec.ofNat 64 (2 * i + 1)))) t2
  obtain ⟨L3, e3⟩ := dec_word' t2 iIv (ldo iU 16) _ _ (ldo_eval t2 iU 16 p _ hu2 m16.1 m16.2)
  let t4 := setVarHOLFinite iI (.val (.word iw)) t3
  have hsh : BitVec.ofNat 64 (2 * i + 1) >>> (1 : Nat) = iw := by
    apply BitVec.eq_of_toNat_eq; simp [iw, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
  obtain ⟨L4, e4⟩ := dec_word' t3 iI (.shift .lsr (vv iIv) (.const 1)) iw _
    (by simp [vv, evalHOLExact, t3, wordShiftHOL]; exact hsh)
  have l4u : t4.locals.lookup iU = some (.val (.word p)) := by
    simp only [t4, t3]; rw [lookup_setVar_other _ _ (by decide), lookup_setVar_other _ _ (by decide)]; exact hu2
  have l4k : t4.locals.lookup iK = some (.val (.word (BitVec.ofNat 64 k))) := by
    simp only [t4, t3]; rw [lookup_setVar_other _ _ (by decide), lookup_setVar_other _ _ (by decide)]; exact hk2
  have l4i : t4.locals.lookup iI = some (.val (.word iw)) := by simp [t4]
  have l4v : t4.locals.lookup iIv = some (.val (.word (BitVec.ofNat 64 (2 * i + 1)))) := by
    simp only [t4]; rw [lookup_setVar_other _ _ (by decide)]; simp [t3]
  have hiw : iw.toNat = i := by simp [iw]; omega
  have hkw : (BitVec.ofNat 64 k).toNat = k := by simp; omega
  unfold bvarCase; rw [e3]; apply rres_locals; rw [e4]; apply rres_locals
  rw [ite_word t4 _ _ _ (if iw = BitVec.ofNat 64 k then 1 else 0)
    (by simp [vv, evalHOLExact, l4i, l4k, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
  by_cases hik : i = k
  · have : iw = BitVec.ofNat 64 k := by simp only [iw, hik]
    simp only [this, ↓reduceIte]
    split
    · rw [evaluateHOLFiniteState_eq_evaluate_def]
      have hg4 : t4.globals.lookup gV = some (.val (.word pv)) := by
        show t2.globals.lookup gV = _; rw [g2]; exact hgv
      simp only [evalHOLExact, hg4]
      simp only [shapeOfHOLExact]
      simp
      apply rres_ret hai2 (by simp [hik]; rw [hO2]; exact hv)
        <;> simp [emptyLocalsHOLFinite, t4, t3, setVarHOLFinite]
    · rename_i hh; exact absurd (by decide) hh
  have hne : ¬ iw = BitVec.ofNat 64 k := fun e => hik (by rw [← hiw, e, hkw])
  simp only [hne, ↓reduceIte]
  split
  · rename_i hh; exact absurd rfl hh
  rw [ite_word t4 _ _ _ (if BitVec.ofNat 64 k < iw then 1 else 0)
    (by simp [vv, evalHOLExact, l4i, l4k, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
  by_cases hlt : k < i
  · have : BitVec.ofNat 64 k < iw := by rw [BitVec.lt_def, hiw, hkw]; exact hlt
    simp only [this, ↓reduceIte]
    split
    · have hi1 : 1 ≤ i := by omega
      let w2 := BitVec.ofNat 64 (2 * (i - 1) + 1)
      let t5 := setVarHOLFinite iW (.val (.word w2)) t4
      obtain ⟨L5, e5⟩ := dec_word' t4 iW (.op .sub [vv iIv, .const 2]) w2
        (.dec iIw .one (.op .sub [vv iI, .const 1]) (mkNode 0 ConPanqueque.ExprData.bvarDataE [iW]))
        (by simp [vv, evalHOLExact, evalListHOLExact, l4v, wordOpHOL, wordOp, valueIsWord, valueWord]
            apply BitVec.eq_of_toNat_eq; simp [w2, BitVec.toNat_sub]; omega)
      let iw1 := (UInt64.ofNat (i - 1)).toBitVec
      let t6 := setVarHOLFinite iIw (.val (.word iw1)) t5
      have l5i : t5.locals.lookup iI = some (.val (.word iw)) := by
        simp only [t5]; rw [lookup_setVar_other _ _ (by decide)]; exact l4i
      obtain ⟨L6, e6⟩ := dec_word' t5 iIw (.op .sub [vv iI, .const 1]) iw1
        (mkNode 0 ConPanqueque.ExprData.bvarDataE [iW])
        (by simp [vv, evalHOLExact, evalListHOLExact, l5i, wordOpHOL, wordOp, valueIsWord, valueWord]
            apply BitVec.eq_of_toNat_eq; simp [iw1, iw, BitVec.toNat_sub]; omega)
      rw [e5]; apply rres_locals; rw [e6]; apply rres_locals
      have hai6 : AInv t6 lo hp := ainv_of_eq hai2 rfl rfl rfl
      rcases mkNode_ainv t6 lo hp 0 _ ConPanqueque.ExprData.bvarDataE [iW] [w2] rfl (by decide) (by decide) (by decide)
          (by simp) (ConPanqueque.ExprData.bvarDataE.eval t6 (UInt64.ofNat (i - 1)) (by show t6.locals.lookup iIw = _; simp [t6, iw1]))
          (fun j hj => match j, hj with
            | 0, _ => by simp only [t6, List.getElem_cons_zero]; rw [lookup_setVar_other _ _ (by decide)]; simp [t5])
          hai6 with hs' | ⟨hr, a5, g5, hpos, cells, cd5, ck5, gl5, md5, ta5⟩
      · exact Or.inl hs'
      right
      have c0 := cells 0 (by decide)
      have c1 := cells 1 (by decide)
      have c2 := cells 2 (by decide)
      simp only [at8, List.length_cons, List.length_nil] at c0 c1 c2
      have e0 : hp + BitVec.ofNat 64 (8 * 0) = hp := by simp
      have e8 : BitVec.ofNat 64 (8 * 1) = 8#64 := by decide
      have e16 : BitVec.ofNat 64 (8 * 2) = 16#64 := by decide
      rw [e0] at c0; rw [e8] at c1; rw [e16] at c2
      have hdat : (ConLeche.Expr.bvar (i - 1)).data = ConPanqueque.ExprData.bvarDataW (UInt64.ofNat (i - 1)) :=
        ConPanqueque.ExprData.bvar_data ra (i - 1) (by omega)
      refine ⟨hp, hr, _, a5, ⟨g5.le, g5.mem⟩, ?_, cd5, ?_, gl5, md5, ta5⟩
      · have hgt : i > k := hlt
        simp only [ConLeche.Expr.instantiate1, hik, hgt, ↓reduceIte]
        exact .bvar hpos c0 (by rw [hdat]; exact c1) c2 ⟨by omega, rfl⟩
      · rw [ck5]; show t2.clock ≤ t2.clock + ConPanqueque.ExprFold.cost (.bvar i); omega
    · rename_i hh; exact absurd (by decide) hh
  · have : ¬ BitVec.ofNat 64 k < iw := by rw [BitVec.lt_def, hiw, hkw]; exact hlt
    simp only [this, ↓reduceIte]
    split
    · rename_i hh; exact absurd rfl hh
    rw [eval_return_local t4 iU p l4u]
    apply rres_ret hai2 (by
        have : ¬ i > k := hlt
        simp [ConLeche.Expr.instantiate1, hik, this]; rw [hO2]; exact exprAt_mono hs he)
      <;> simp [emptyLocalsHOLFinite, t4, t3, setVarHOLFinite]


theorem inst1_spec {σ : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (fn : MlS)
    (C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (hC : C.lookup fn = some ([(iU, .one), (iK, .one)], body (cases bvarCase fn), .one)) (v : ConLeche.Expr)
    (lo : BitVec 64) {h : Heap} {p : BitVec 64} {e : ConLeche.Expr} (he : ExprAt h p e) :
    Spec (σ := σ) bvarCase fn C (shape v) (inv v) lo h p e :=
  subst_spec ra bvarCase fn C hC (shape v) (inv v) lo
    (fun h p vw i he h0 h2 hi => spec_bvar ra fn C v lo h p vw i he h0 h2 hi) he

end ConPanqueque.Inst1
