import ConPanqueque.Subst
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic ConPanqueque.Alloc ConPanqueque.ExprCons
open ConPanqueque.Node ConPanqueque.StateHeap ConPanqueque.Rebuild ConPanqueque.Subst

/-!
# `Expr.liftLooseBVars` in Pancake

An instance of the substitution template: the amount is held in the global `amt`;
at `bvar i` the case returns the node if `i < c`, else builds `bvar (i + amount)`
(and stops if that index does not fit the small-natural representation).
-/

namespace ConPanqueque.Lift

def gA := ofString "amt"
def iIv := ofString "iv"
def iI := ofString "i"
def iW := ofString "w"

def bvarCase : ProgHOL 64 :=
  .dec iIv .one (ldo iU 16)
   (.dec iI .one (.shift .lsr (vv iIv) (.const 1))
    (.ite (.cmp .lower (vv iI) (vv iK)) (.return (vv iU))
     (.dec iIw .one (.op .add [vv iI, .var .global gA])
       (.ite (.cmp .lower (vv iIw) (.const 0x8000000000000000#64))
         (.dec iW .one (.op .add [.op .add [vv iIw, vv iIw], .const 1]) (mkNode 0 ConPanqueque.ExprData.bvarDataE [iW]))
         hang))))

/-- The amount is held in the global `amt`. -/
def inv (a : Nat) : Subst.Inv where
  P gl _ := gl gA = some (.val (.word (BitVec.ofNat 64 a)))
  mono gl gl' h h' := fun x _ hg => by rw [hg gA (by decide)]; exact x

def shape (a : Nat) : Subst.Shape (inv a) where
  F e c := e.liftLooseBVars a c
  CP := Cut
  ce := cutE
  ceval t e k hk hd hkw _ _ := ⟨_, eval_cutE t e k hk hd hkw, by by_cases h : Cut e k <;> simp [h]⟩
  leaf e k hb _ := ⟨by omega, by omega⟩
  cut e k h := ConLeche.Expr.liftLooseBVars_eq_self (by
    rw [ConLeche.Expr.looseBVarsBounded_iff, ← ConLeche.Expr.bvarBRaw_exact e (by simp [ConLeche.satRange]; exact h.1)]
    exact h.2)
  app _ _ _ := rfl
  lam _ _ _ := rfl
  forallE _ _ _ := rfl
  letE _ _ _ _ := rfl
  proj _ _ _ _ := rfl

theorem spec_bvar {σ : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (fn : MlS)
    (C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (a : Nat) (ha : a < 2 ^ 63) (lo : BitVec 64) (h : Heap) (p vw : BitVec 64) (i : Nat)
    (he : ExprAt h p (.bvar i)) (h0 : h p = some (.word 0)) (h2 : h (p + 16) = some (.word vw)) (hi : NatAt h vw i) :
    Spec (σ := σ) bvarCase idCase fn C (inv a) (shape a) lo h p (.bvar i) := by
  intro t k hp hcd hai hs hx hu hk hd hck
  obtain ⟨_, h8⟩ := exprAt_data he
  apply entry cutE Cut (cases bvarCase idCase fn) t lo hp p 0 (.bvar i) k (by omega) hai hu hk (hs _ _ h0) (hs _ _ h8)
    (fun t' x y g => (shape a).ceval t' _ k (by omega) x y _ (by rw [g]; exact hx))
  · intro hct; rw [(shape a).cut _ _ hct]; exact exprAt_mono hs he
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
  rw [ite_word t4 _ _ _ (if iw < BitVec.ofNat 64 k then 1 else 0)
    (by simp [vv, evalHOLExact, l4i, l4k, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
  by_cases hlt : i < k
  · have : iw < BitVec.ofNat 64 k := by rw [BitVec.lt_def, hiw, hkw]; exact hlt
    simp only [this, ↓reduceIte]
    split
    · rw [eval_return_local t4 iU p l4u]
      apply rres_ret hai2 (by
          have : ¬ i ≥ k := by omega
          simp [ConLeche.Expr.liftLooseBVars, this]; rw [hO2]; exact exprAt_mono hs he)
        <;> simp [emptyLocalsHOLFinite, t4, t3, setVarHOLFinite]
    · rename_i hh; exact absurd (by decide) hh
  have : ¬ iw < BitVec.ofNat 64 k := by rw [BitVec.lt_def, hiw, hkw]; exact hlt
  simp only [this, ↓reduceIte]
  split
  · rename_i hh; exact absurd rfl hh
  have hga : t4.globals.lookup gA = some (.val (.word (BitVec.ofNat 64 a))) := by
    show t2.globals.lookup gA = _; rw [g2]; exact hx
  let jw := (UInt64.ofNat (i + a)).toBitVec
  have hjw : jw.toNat = i + a := by simp [jw]; omega
  let t5 := setVarHOLFinite iIw (.val (.word jw)) t4
  obtain ⟨L5, e5⟩ := dec_word' t4 iIw (.op .add [vv iI, .var .global gA]) jw _
    (by simp [vv, evalHOLExact, evalListHOLExact, l4i, hga, wordOpHOL, wordOp, valueIsWord, valueWord]
        apply BitVec.eq_of_toNat_eq; simp [jw, iw, BitVec.toNat_add] <;> omega)
  rw [e5]; apply rres_locals
  have l5j : t5.locals.lookup iIw = some (.val (.word jw)) := by simp [t5]
  rw [ite_word t5 _ _ _ (if jw < 0x8000000000000000#64 then 1 else 0)
    (by simp [vv, evalHOLExact, l5j, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
  by_cases hb : i + a < 2 ^ 63
  · have : jw < 0x8000000000000000#64 := by rw [BitVec.lt_def, hjw]; simpa using hb
    simp only [this, ↓reduceIte]
    split
    · let w2 := BitVec.ofNat 64 (2 * (i + a) + 1)
      let t6 := setVarHOLFinite iW (.val (.word w2)) t5
      obtain ⟨L6, e6⟩ := dec_word' t5 iW (.op .add [.op .add [vv iIw, vv iIw], .const 1]) w2
        (mkNode 0 ConPanqueque.ExprData.bvarDataE [iW])
        (by simp [vv, evalHOLExact, evalListHOLExact, l5j, wordOpHOL, wordOp, valueIsWord, valueWord]
            apply BitVec.eq_of_toNat_eq; simp [w2, BitVec.toNat_add, hjw]; omega)
      rw [e6]; apply rres_locals
      have hai6 : AInv t6 lo hp := ainv_of_eq hai2 rfl rfl rfl
      rcases mkNode_ainv t6 lo hp 0 _ ConPanqueque.ExprData.bvarDataE [iW] [w2] rfl (by decide) (by decide) (by decide)
          (by simp) (ConPanqueque.ExprData.bvarDataE.eval t6 (UInt64.ofNat (i + a))
            (by show t6.locals.lookup iIw = _; simp only [t6]; rw [lookup_setVar_other _ _ (by decide)]; exact l5j))
          (fun j hj => match j, hj with
            | 0, _ => by simp [t6])
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
      have hdat : (ConLeche.Expr.bvar (i + a)).data = ConPanqueque.ExprData.bvarDataW (UInt64.ofNat (i + a)) :=
        ConPanqueque.ExprData.bvar_data ra (i + a) hb
      refine ⟨hp, hr, _, a5, ⟨g5.le, g5.mem⟩, ?_, cd5, ?_, gl5, md5, ta5⟩
      · have hge : i ≥ k := by omega
        simp only [ConLeche.Expr.liftLooseBVars, hge, ↓reduceIte]
        exact .bvar hpos c0 (by rw [hdat]; exact c1) c2 ⟨hb, rfl⟩
      · rw [ck5]; show t2.clock ≤ t2.clock + ConPanqueque.ExprFold.cost (.bvar i); omega
    · rename_i hh; exact absurd (by decide) hh
  · have : ¬ jw < 0x8000000000000000#64 := by rw [BitVec.lt_def, hjw]; simpa using hb
    simp only [this, ↓reduceIte]
    split
    · rename_i hh; exact absurd rfl hh
    left; rw [hang_spec _ _ rfl]; exact Or.inl rfl

theorem lift_spec {σ : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (fn : MlS)
    (C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (hC : C.lookup fn = some ([(iU, .one), (iK, .one)], body cutE (cases bvarCase idCase fn), .one)) (a : Nat) (ha : a < 2 ^ 63)
    (lo : BitVec 64) {h : Heap} {p : BitVec 64} {e : ConLeche.Expr} (he : ExprAt h p e) :
    Spec (σ := σ) bvarCase idCase fn C (inv a) (shape a) lo h p e :=
  subst_spec ra bvarCase idCase fn C (inv a) (shape a) hC lo
    (fun h p vw i he h0 h2 hi => spec_bvar ra fn C a ha lo h p vw i he h0 h2 hi)
    (fun h p vw q i ty he h0 h2 h3 hi hty => spec_leaf bvarCase idCase fn C (inv a) (shape a) lo h p 1 _ he h0
      (fun k => ⟨by simp, by simp⟩)) he

end ConPanqueque.Lift
