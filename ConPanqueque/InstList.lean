import ConPanqueque.AbstractRange
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic ConPanqueque.Alloc ConPanqueque.ExprCons
open ConPanqueque.Node ConPanqueque.StateHeap ConPanqueque.Rebuild ConPanqueque.Subst

/-!
# `Expr.instantiateList` in Pancake (closed values)

An instance of the substitution template: the values `vs` are an array of
expression pointers at the global `ila`, their count at `iln`; at `bvar i`
(past depth `d`) the case returns `vs[i-d]`, or builds `bvar (i - |vs|)`. The
values must be closed, which con-leche notes holds at every checker call site
of `instantiateListC` (then its nested re-instantiation is the identity).
-/

namespace ConPanqueque.InstList

def gA := ofString "ila"
def gN := ofString "iln"
def iIv := ofString "iv"
def iI := ofString "i"
def iJ := ofString "j"

def bvarCase : ProgHOL 64 :=
  .dec iIv .one (ldo iU 16) (.dec iI .one (.shift .lsr (vv iIv) (.const 1))
   (.ite (.cmp .lower (vv iI) (vv iK)) (.return (vv iU))
    (.dec iJ .one (.op .sub [vv iI, vv iK])
     (.ite (.cmp .lower (vv iJ) (.var .global gN))
       (.return (.load .one (.op .add [.var .global gA, .shift .lsl (vv iJ) (.const 3)])))
       (.dec AbstractRange.iW .one (.op .sub [vv iIv, .op .add [.var .global gN, .var .global gN]])
         (.dec iIw .one (.op .sub [vv iI, .var .global gN])
           (mkNode 0 ConPanqueque.ExprData.bvarDataE [AbstractRange.iW])))))))

/-- The values are an array of pointers at `ila`, their count at `iln`. -/
def inv (vs : List ConLeche.Expr) (a : BitVec 64) : Subst.Inv where
  P gl hh := gl gA = some (.val (.word a)) ∧ gl gN = some (.val (.word (BitVec.ofNat 64 vs.length))) ∧
    ∀ j (hj : j < vs.length), ∃ pj, hh (a + BitVec.ofNat 64 (8 * j)) = some (.word pj) ∧ ExprAt hh pj (vs[j]'hj)
  mono gl gl' h h' := fun ⟨x, y, z⟩ hs hg => ⟨by rw [hg _ (by decide)]; exact x, by rw [hg _ (by decide)]; exact y,
    fun j hj => let ⟨pj, a1, a2⟩ := z j hj; ⟨pj, hs _ _ a1, exprAt_mono hs a2⟩⟩

def shape (vs : List ConLeche.Expr) (a : BitVec 64) : Subst.Shape (inv vs a) where
  F e d := e.instantiateList vs d
  CP := Cut
  ce := cutE
  ceval t e k hk hd hkw _ _ := ⟨_, eval_cutE t e k hk hd hkw, by by_cases h : Cut e k <;> simp [h]⟩
  leaf l k := ⟨by simp, by simp⟩
  cut e k h := ConLeche.Expr.instantiateList_eq_self (by
    rw [ConLeche.Expr.looseBVarsBounded_iff, ← ConLeche.Expr.bvarBRaw_exact e (by simp [ConLeche.satRange]; exact h.1)]
    exact h.2)
  app _ _ _ := by rw [ConLeche.Expr.instantiateList]
  lam _ _ _ := by rw [ConLeche.Expr.instantiateList]
  forallE _ _ _ := by rw [ConLeche.Expr.instantiateList]
  letE _ _ _ _ := by rw [ConLeche.Expr.instantiateList]
  proj _ _ _ _ := by rw [ConLeche.Expr.instantiateList]
  cost := ConPanqueque.ExprFold.cost
  cost_app _ _ := by simp [ConPanqueque.ExprFold.cost]; omega
  cost_lam _ _ := by simp [ConPanqueque.ExprFold.cost]; omega
  cost_forallE _ _ := by simp [ConPanqueque.ExprFold.cost]; omega
  cost_letE _ _ _ := by simp [ConPanqueque.ExprFold.cost]
  cost_proj _ _ _ := by simp [ConPanqueque.ExprFold.cost]

theorem spec_bvar {σ : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (fn : MlS)
    (C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (vs : List ConLeche.Expr) (hvs : vs.length < 2 ^ 60)
    (hcl : ∀ w ∈ vs, w.looseBVarsBounded 0 = true) (a lo : BitVec 64) (h : Heap) (p vw : BitVec 64) (i : Nat)
    (he : ExprAt h p (.bvar i)) (h0 : h p = some (.word 0)) (h2 : h (p + 16) = some (.word vw)) (hi : NatAt h vw i) :
    Spec (σ := σ) bvarCase idCase idCase idCase fn C (inv vs a) (shape vs a) lo h p (.bvar i) := by
  intro t k hp hcd hai hs hx hu hk hd hck
  obtain ⟨_, h8⟩ := exprAt_data he
  apply entry cutE Cut (cases bvarCase idCase idCase idCase fn) t lo hp p 0 (.bvar i) k (by omega) hai hu hk (hs _ _ h0) (hs _ _ h8)
    (fun t' x y g => (shape vs a).ceval t' _ k (by omega) x y _ (by rw [g]; exact hx))
  · intro hct; rw [(shape vs a).cut _ _ hct]; exact exprAt_mono hs he
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
  obtain ⟨hga, hgn, harr⟩ := hx
  have hga4 : t4.globals.lookup gA = some (.val (.word a)) := by show t2.globals.lookup gA = _; rw [g2]; exact hga
  have hgn4 : t4.globals.lookup gN = some (.val (.word (BitVec.ofNat 64 vs.length))) := by
    show t2.globals.lookup gN = _; rw [g2]; exact hgn
  have hnw : (BitVec.ofNat 64 vs.length).toNat = vs.length := by simp; omega
  rw [ite_word t4 _ _ _ (if iw < BitVec.ofNat 64 k then 1 else 0)
    (by simp [vv, evalHOLExact, l4i, l4k, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
  by_cases hlt : i < k
  · have : iw < BitVec.ofNat 64 k := by rw [BitVec.lt_def, hiw, hkw]; exact hlt
    simp only [this, ↓reduceIte]
    split
    · rw [eval_return_local t4 iU p l4u]
      apply rres_ret hai2 (by
          show ExprAt _ p ((ConLeche.Expr.bvar i).instantiateList vs k)
          simp [ConLeche.Expr.instantiateList, hlt]; rw [hO2]; exact exprAt_mono hs he)
        <;> simp [emptyLocalsHOLFinite, t4, t3, setVarHOLFinite]
    · rename_i hh; exact absurd (by decide) hh
  have : ¬ iw < BitVec.ofNat 64 k := by rw [BitVec.lt_def, hiw, hkw]; exact hlt
  simp only [this, ↓reduceIte]
  split
  · rename_i hh; exact absurd rfl hh
  let jw := BitVec.ofNat 64 (i - k)
  have hjw : jw.toNat = i - k := by simp [jw]; omega
  let t5 := setVarHOLFinite iJ (.val (.word jw)) t4
  obtain ⟨L5, e5⟩ := dec_word' t4 iJ (.op .sub [vv iI, vv iK]) jw _
    (by simp [vv, evalHOLExact, evalListHOLExact, l4i, l4k, wordOpHOL, wordOp, valueIsWord, valueWord]
        apply BitVec.eq_of_toNat_eq; simp [jw, iw, BitVec.toNat_sub] <;> omega)
  rw [e5]; apply rres_locals
  have l5j : t5.locals.lookup iJ = some (.val (.word jw)) := by simp [t5]
  rw [ite_word t5 _ _ _ (if jw < BitVec.ofNat 64 vs.length then 1 else 0)
    (by
      have : t5.globals.lookup gN = some (.val (.word (BitVec.ofNat 64 vs.length))) := hgn4
      simp [vv, evalHOLExact, l5j, this, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
  have hai5 : AInv t5 lo hp := ainv_of_eq hai2 rfl rfl rfl
  by_cases hin : i - k < vs.length
  · have : jw < BitVec.ofNat 64 vs.length := by rw [BitVec.lt_def, hjw, hnw]; exact hin
    simp only [this, ↓reduceIte]
    split
    · obtain ⟨pj, hpj, epj⟩ := harr (i - k) hin
      have hpj2 : hOf t2 lo hp (a + BitVec.ofNat 64 (8 * (i - k))) = some (.word pj) := by rw [hO2]; exact hpj
      have mj := (ainv_arena hai2).1 _ _ hpj2
      have hadr : @evalHOLExact 64 σ _ t5.toExact (fun x => Classical.propDecidable (t5.memaddrs x))
          (.op .add [.var .global gA, .shift .lsl (vv iJ) (.const 3)]) =
          some (.val (.word (a + BitVec.ofNat 64 (8 * (i - k))))) := by
        have : t5.globals.lookup gA = some (.val (.word a)) := hga4
        simp [vv, evalHOLExact, evalListHOLExact, l5j, this, wordOpHOL, wordOp, valueIsWord, valueWord, wordShiftHOL]
        apply BitVec.eq_of_toNat_eq; simp [jw, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
      have eret : evaluateHOLFiniteState t5 (.return (.load .one (.op .add [.var .global gA, .shift .lsl (vv iJ) (.const 3)])))
          = (some (.returned (.val (.word pj))), emptyLocalsHOLFinite t5) := by
        rw [evaluateHOLFiniteState_eq_evaluate_def]
        simp only
        have mj2 : t5.memory (a + BitVec.ofNat 64 (8 * (i - k))) = .word pj := mj.2
        rw [eval_load_word t5 _ _ hadr mj.1, mj2]; simp [shapeOfHOLExact]
      rw [eret]
      apply rres_ret hai2 (by
          show ExprAt _ pj ((ConLeche.Expr.bvar i).instantiateList vs k)
          have hw : (vs[i - k]'hin).instantiateList (vs.take (i - k)) k = vs[i - k]'hin :=
            ConLeche.Expr.instantiateList_eq_self (by
              have := hcl _ (List.getElem_mem hin)
              rw [ConLeche.Expr.looseBVarsBounded_iff] at this ⊢; omega)
          simp only [ConLeche.Expr.instantiateList, hlt, ↓reduceIte, hin, ↓reduceDIte, hw]
          rw [hO2]; exact epj)
        <;> simp [emptyLocalsHOLFinite, t5, t4, t3, setVarHOLFinite]
    · rename_i hh; exact absurd (by decide) hh
  · have : ¬ jw < BitVec.ofNat 64 vs.length := by rw [BitVec.lt_def, hjw, hnw]; exact hin
    simp only [this, ↓reduceIte]
    split
    · rename_i hh; exact absurd rfl hh
    let m := i - vs.length
    let w2 := BitVec.ofNat 64 (2 * m + 1)
    let t6 := setVarHOLFinite AbstractRange.iW (.val (.word w2)) t5
    have l5v : t5.locals.lookup iIv = some (.val (.word (BitVec.ofNat 64 (2 * i + 1)))) := by
      simp only [t5]; rw [lookup_setVar_other _ _ (by decide)]; exact l4v
    obtain ⟨L6, e6⟩ := dec_word' t5 AbstractRange.iW (.op .sub [vv iIv, .op .add [.var .global gN, .var .global gN]]) w2
      (.dec iIw .one (.op .sub [vv iI, .var .global gN]) (mkNode 0 ConPanqueque.ExprData.bvarDataE [AbstractRange.iW]))
      (by
        have : t5.globals.lookup gN = some (.val (.word (BitVec.ofNat 64 vs.length))) := hgn4
        simp [vv, evalHOLExact, evalListHOLExact, l5v, this, wordOpHOL, wordOp, valueIsWord, valueWord]
        apply BitVec.eq_of_toNat_eq; simp [w2, m, BitVec.toNat_sub, BitVec.toNat_add] <;> omega)
    let mw := (UInt64.ofNat m).toBitVec
    let t7 := setVarHOLFinite iIw (.val (.word mw)) t6
    obtain ⟨L7, e7⟩ := dec_word' t6 iIw (.op .sub [vv iI, .var .global gN]) mw
      (mkNode 0 ConPanqueque.ExprData.bvarDataE [AbstractRange.iW])
      (by
        have : t6.globals.lookup gN = some (.val (.word (BitVec.ofNat 64 vs.length))) := hgn4
        have l6i : t6.locals.lookup iI = some (.val (.word iw)) := by
          simp only [t6, t5]; rw [lookup_setVar_other _ _ (by decide), lookup_setVar_other _ _ (by decide)]; exact l4i
        simp [vv, evalHOLExact, evalListHOLExact, l6i, this, wordOpHOL, wordOp, valueIsWord, valueWord]
        apply BitVec.eq_of_toNat_eq; simp [mw, m, iw, BitVec.toNat_sub] <;> omega)
    rw [e6]; apply rres_locals; rw [e7]; apply rres_locals
    have hb := AbstractRange.build_bvar ra t7 lo hp m (by omega) (ainv_of_eq hai2 rfl rfl rfl)
      (by show t7.locals.lookup AbstractRange.iW = _; simp only [t7]; rw [lookup_setVar_other _ _ (by decide)]; simp [t6, w2])
      (by show t7.locals.lookup iIw = _; simp [t7, mw])
    have hF : (ConLeche.Expr.bvar i).instantiateList vs k = .bvar m := by
      simp [ConLeche.Expr.instantiateList, hlt, hin, m]
    show RRes t2 _ lo hp (fun h q => ExprAt h q ((ConLeche.Expr.bvar i).instantiateList vs k)) _
    rw [hF]
    have := rres_trans (c := ConPanqueque.ExprFold.cost (.bvar i)) (t := t2) hb ⟨BitVec.le_refl _, fun _ _ _ => rfl⟩ rfl
      (by show t2.clock ≤ t2.clock + _; omega) (fun _ _ => rfl) rfl rfl
    simpa using this

theorem instList_spec {σ : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (fn : MlS)
    (C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (vs : List ConLeche.Expr) (hvs : vs.length < 2 ^ 60) (hcl : ∀ w ∈ vs, w.looseBVarsBounded 0 = true)
    (a : BitVec 64)
    (hC : C.lookup fn = some ([(iU, .one), (iK, .one)], body cutE (cases bvarCase idCase idCase idCase fn), .one))
    (lo : BitVec 64) {h : Heap} {p : BitVec 64} {e : ConLeche.Expr} (he : ExprAt h p e) :
    Spec (σ := σ) bvarCase idCase idCase idCase fn C (inv vs a) (shape vs a) lo h p e :=
  subst_spec ra bvarCase idCase idCase idCase fn C (inv vs a) (shape vs a) hC lo
    (fun p vw i he h0 h2 hi => spec_bvar ra fn C vs hvs hcl a lo h p vw i he h0 h2 hi)
    (fun p vw q i ty he h0 h2 h3 hi hty _ => spec_leaf bvarCase idCase idCase idCase fn C (inv vs a) (shape vs a) lo h p 1 _
      he h0 (fun k => ⟨by simp, by simp⟩))
    (fun p q u he h0 h2 hu => spec_leaf bvarCase idCase idCase idCase fn C (inv vs a) (shape vs a) lo h p 2 _ he h0
      (fun k => ⟨by simp, by simp⟩))
    (fun p q r n us he h0 h2 h3 hn hus => spec_leaf bvarCase idCase idCase idCase fn C (inv vs a) (shape vs a) lo h p 3 _
      he h0 (fun k => ⟨by simp, by simp⟩)) he

end ConPanqueque.InstList
