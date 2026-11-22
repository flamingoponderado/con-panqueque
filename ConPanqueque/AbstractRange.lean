import ConPanqueque.Abstract1
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic ConPanqueque.Alloc ConPanqueque.ExprCons
open ConPanqueque.Node ConPanqueque.StateHeap ConPanqueque.Rebuild ConPanqueque.Subst

/-!
# `Expr.abstractRange` in Pancake

Bulk abstraction, an instance of the substitution template with `abstract1`'s
cutoff (`fvarB ≤ d`): `d` and the count `n` are held in the globals `absd` and
`absn`; at `fvar i` with `d ≤ i < d + n` the case builds `bvar (c + (d+n-1-i))`.
`build_bvar` (writing a `bvar j` node) is shared by the instances' leaf cases.
-/

namespace ConPanqueque.AbstractRange

def gN := ofString "absn"
def iIv := ofString "iv"
def iI := ofString "i"
def iE := ofString "e"
def iW := ofString "w"

/-- Write a `bvar j` node from `w = 2j+1` and `iw = j`. -/
theorem build_bvar {σ : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ)
    (lo hp : BitVec 64) (j : Nat) (hj : j < 2 ^ 63) (hi : AInv t lo hp)
    (lw : t.locals.lookup iW = some (.val (.word (BitVec.ofNat 64 (2 * j + 1)))))
    (lj : t.locals.lookup iIw = some (.val (.word (UInt64.ofNat j).toBitVec))) :
    RRes t (evaluateHOLFiniteState t (mkNode 0 ConPanqueque.ExprData.bvarDataE [iW])) lo hp
      (fun h q => ExprAt h q (.bvar j)) 0 := by
  rcases mkNode_ainv t lo hp 0 _ ConPanqueque.ExprData.bvarDataE [iW] [_] rfl (by decide) (by decide) (by decide)
      (by simp) (ConPanqueque.ExprData.bvarDataE.eval t (UInt64.ofNat j) lj)
      (fun j' hj' => match j', hj' with
        | 0, _ => lw)
      hi with hs' | ⟨hr, a5, g5, hpos, cells, cd5, ck5, gl5, md5, ta5⟩
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
  have hdat : (ConLeche.Expr.bvar j).data = ConPanqueque.ExprData.bvarDataW (UInt64.ofNat j) :=
    ConPanqueque.ExprData.bvar_data ra j hj
  exact ⟨hp, hr, _, a5, g5, .bvar hpos c0 (by rw [hdat]; exact c1) c2 ⟨hj, rfl⟩, cd5,
    by rw [ck5]; omega, gl5, md5, ta5⟩

def fvarCase : ProgHOL 64 :=
  .dec iIv .one (ldo iU 16) (.dec iI .one (.shift .lsr (vv iIv) (.const 1))
   (.ite (.cmp .lower (vv iI) (.var .global Abstract1.gD)) (.return (vv iU))
    (.dec iE .one (.op .add [.var .global Abstract1.gD, .var .global gN])
     (.ite (.cmp .lower (vv iI) (vv iE))
       (.ite (.cmp .lower (vv iK) (.const 0x8000000000000000#64))
         (.dec iIw .one (.op .add [vv iK, .op .sub [.op .sub [vv iE, .const 1], vv iI]])
           (.ite (.cmp .lower (vv iIw) (.const 0x8000000000000000#64))
             (.dec iW .one (.op .add [.op .add [vv iIw, vv iIw], .const 1]) (mkNode 0 ConPanqueque.ExprData.bvarDataE [iW]))
             hang))
         hang)
       (.return (vv iU))))))

/-- `d` and `n` are held in the globals `absd` and `absn`. -/
def inv (d n : Nat) : Subst.Inv where
  P gl _ := gl Abstract1.gD = some (.val (.word (BitVec.ofNat 64 d))) ∧ gl gN = some (.val (.word (BitVec.ofNat 64 n)))
  mono gl gl' h h' := fun x _ hg => ⟨by rw [hg _ (by decide)]; exact x.1, by rw [hg _ (by decide)]; exact x.2⟩

def shape (d n : Nat) (hdn : d + n < 2 ^ 63) : Subst.Shape (inv d n) where
  F e c := e.abstractRange d n c
  CP := Abstract1.CutF d
  ce := Abstract1.cutF
  ceval t e k _ hdw _ _ hg := Abstract1.eval_cutF t e d (by omega) hdw hg.1
  leaf l k := ⟨by simp, by simp⟩
  cut e k h := ConLeche.abstractRange_eq_self (ConLeche.Expr.fvarsBelow_iff.mpr (by
    rw [← ConLeche.Expr.fvarBRaw_exact e (by simp [ConLeche.satRange]; exact h.1)]; exact h.2))
  app _ _ _ := rfl
  lam _ _ _ := rfl
  forallE _ _ _ := rfl
  letE _ _ _ _ := rfl
  proj _ _ _ _ := rfl
  cost := ConPanqueque.ExprFold.cost
  cost_app _ _ := by simp [ConPanqueque.ExprFold.cost]; omega
  cost_lam _ _ := by simp [ConPanqueque.ExprFold.cost]; omega
  cost_forallE _ _ := by simp [ConPanqueque.ExprFold.cost]; omega
  cost_letE _ _ _ := by simp [ConPanqueque.ExprFold.cost]
  cost_proj _ _ _ := by simp [ConPanqueque.ExprFold.cost]

theorem spec_fvar {σ : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (fn : MlS)
    (C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (d n : Nat) (hdn : d + n < 2 ^ 63) (lo : BitVec 64) (h : Heap) (p vw : BitVec 64) (i : Nat) (ty : ConLeche.Expr)
    (he : ExprAt h p (.fvar i ty)) (h0 : h p = some (.word 1)) (h2 : h (p + 16) = some (.word vw)) (hi : NatAt h vw i) :
    Spec (σ := σ) idCase fvarCase idCase idCase fn C (inv d n) (shape d n hdn) lo h p (.fvar i ty) := by
  intro t k hp hcd hai hs hx hu hk hd hck
  obtain ⟨_, h8⟩ := exprAt_data he
  apply entry (Abstract1.cutF) (Abstract1.CutF d) (cases idCase fvarCase idCase idCase fn) t lo hp p 1 (.fvar i ty) k (by omega) hai hu hk (hs _ _ h0) (hs _ _ h8)
    (fun t' x y g => (shape d n hdn).ceval t' _ k (by omega) x y (hOf t lo hp) (by rw [g]; exact hx))
  · intro hct; rw [(shape d n hdn).cut _ _ hct]; exact exprAt_mono hs he
  intro hct t2 cd2 m2 d2 g2 ta2 ck2 hu2 hk2
  dsimp only [shape]
  show RRes t2 (evaluateHOLFiniteState t2 fvarCase) lo hp _ _
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
  unfold fvarCase; rw [e3]; apply rres_locals; rw [e4]; apply rres_locals
  have hgd : t4.globals.lookup Abstract1.gD = some (.val (.word (BitVec.ofNat 64 d))) := by
    show t2.globals.lookup _ = _; rw [g2]; exact hx.1
  have hgn : t4.globals.lookup gN = some (.val (.word (BitVec.ofNat 64 n))) := by
    show t2.globals.lookup _ = _; rw [g2]; exact hx.2
  have hdw : (BitVec.ofNat 64 d).toNat = d := by simp; omega
  have keep : ¬ (d ≤ i ∧ i < d + n) → ∀ t' : PanSemStateFiniteExact 64 σ,
      t'.locals.lookup iU = some (.val (.word p)) → t'.memory = t2.memory → t'.code = t2.code →
      t'.clock = t2.clock → t'.globals = t2.globals → t'.memaddrs = t2.memaddrs → t'.topAddr = t2.topAddr →
      RRes t2 (evaluateHOLFiniteState t' (.return (vv iU))) lo hp
        (fun h q => ExprAt h q ((ConLeche.Expr.fvar i ty).abstractRange d n k)) (ConPanqueque.ExprFold.cost (.fvar i ty)) := by
    intro hn t' lu m1 m2 m3 m4 m5 m6
    rw [eval_return_local t' iU p lu]
    apply rres_ret hai2 (by
        show ExprAt _ p ((ConLeche.Expr.fvar i ty).abstractRange d n k)
        simp only [ConLeche.Expr.abstractRange, hn, ↓reduceIte]; rw [hO2]; exact exprAt_mono hs he)
      <;> simp [emptyLocalsHOLFinite, m1, m2, m3, m4, m5, m6]
  rw [ite_word t4 _ _ _ (if iw < BitVec.ofNat 64 d then 1 else 0)
    (by simp [vv, evalHOLExact, l4i, hgd, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
  by_cases hlt : i < d
  · have : iw < BitVec.ofNat 64 d := by rw [BitVec.lt_def, hiw, hdw]; exact hlt
    simp only [this, ↓reduceIte]
    split
    · exact keep (by omega) t4 l4u rfl rfl rfl rfl rfl rfl
    · rename_i hh; exact absurd (by decide) hh
  have : ¬ iw < BitVec.ofNat 64 d := by rw [BitVec.lt_def, hiw, hdw]; exact hlt
  simp only [this, ↓reduceIte]
  split
  · rename_i hh; exact absurd rfl hh
  let ew := BitVec.ofNat 64 (d + n)
  have hew : ew.toNat = d + n := by simp [ew]; omega
  let t5 := setVarHOLFinite iE (.val (.word ew)) t4
  obtain ⟨L5, e5⟩ := dec_word' t4 iE (.op .add [.var .global Abstract1.gD, .var .global gN]) ew _
    (by simp [evalHOLExact, evalListHOLExact, hgd, hgn, wordOpHOL, wordOp, valueIsWord, valueWord]
        apply BitVec.eq_of_toNat_eq; simp [ew, BitVec.toNat_add] <;> omega)
  rw [e5]; apply rres_locals
  have l5i : t5.locals.lookup iI = some (.val (.word iw)) := by
    simp only [t5]; rw [lookup_setVar_other _ _ (by decide)]; exact l4i
  have l5e : t5.locals.lookup iE = some (.val (.word ew)) := by simp [t5]
  have l5k : t5.locals.lookup iK = some (.val (.word (BitVec.ofNat 64 k))) := by
    simp only [t5]; rw [lookup_setVar_other _ _ (by decide)]; exact l4k
  have hai5 : AInv t5 lo hp := ainv_of_eq hai2 rfl rfl rfl
  rw [ite_word t5 _ _ _ (if iw < ew then 1 else 0)
    (by simp [vv, evalHOLExact, l5i, l5e, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
  by_cases hin : i < d + n
  · have : iw < ew := by rw [BitVec.lt_def, hiw, hew]; exact hin
    simp only [this, ↓reduceIte]
    split
    · rw [ite_word t5 _ _ _ (if BitVec.ofNat 64 k < 0x8000000000000000#64 then 1 else 0)
        (by simp [vv, evalHOLExact, l5k, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
      by_cases hk63 : k < 2 ^ 63
      · have : BitVec.ofNat 64 k < 0x8000000000000000#64 := by rw [BitVec.lt_def, hkw]; simpa using hk63
        simp only [this, ↓reduceIte]
        split
        · let j := k + (d + n - 1 - i)
          let jw := (UInt64.ofNat j).toBitVec
          have hjw : jw.toNat = j := by simp [jw, j]; omega
          let t6 := setVarHOLFinite iIw (.val (.word jw)) t5
          obtain ⟨L6, e6⟩ := dec_word' t5 iIw (.op .add [vv iK, .op .sub [.op .sub [vv iE, .const 1], vv iI]]) jw _
            (by simp [vv, evalHOLExact, evalListHOLExact, l5k, l5e, l5i, wordOpHOL, wordOp, valueIsWord, valueWord]
                apply BitVec.eq_of_toNat_eq; simp [jw, j, ew, iw, BitVec.toNat_add, BitVec.toNat_sub] <;> omega)
          rw [e6]; apply rres_locals
          have l6j : t6.locals.lookup iIw = some (.val (.word jw)) := by simp [t6]
          rw [ite_word t6 _ _ _ (if jw < 0x8000000000000000#64 then 1 else 0)
            (by simp [vv, evalHOLExact, l6j, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
          by_cases hj : j < 2 ^ 63
          · have : jw < 0x8000000000000000#64 := by rw [BitVec.lt_def, hjw]; simpa using hj
            simp only [this, ↓reduceIte]
            split
            · let w2 := BitVec.ofNat 64 (2 * j + 1)
              let t7 := setVarHOLFinite iW (.val (.word w2)) t6
              obtain ⟨L7, e7⟩ := dec_word' t6 iW (.op .add [.op .add [vv iIw, vv iIw], .const 1]) w2
                (mkNode 0 ConPanqueque.ExprData.bvarDataE [iW])
                (by simp [vv, evalHOLExact, evalListHOLExact, l6j, wordOpHOL, wordOp, valueIsWord, valueWord]
                    apply BitVec.eq_of_toNat_eq; simp [w2, BitVec.toNat_add, hjw] <;> omega)
              rw [e7]; apply rres_locals
              have hb := build_bvar ra t7 lo hp j hj (ainv_of_eq hai2 rfl rfl rfl) (by simp [t7, w2])
                (by show t7.locals.lookup iIw = _; simp only [t7]; rw [lookup_setVar_other _ _ (by decide)]; exact l6j)
              have hF : (ConLeche.Expr.fvar i ty).abstractRange d n k = .bvar j := by
                have h1 : d ≤ i := by omega
                simp [ConLeche.Expr.abstractRange, h1, hin, j]
              show RRes t2 _ lo hp (fun h q => ExprAt h q ((ConLeche.Expr.fvar i ty).abstractRange d n k)) _
              rw [hF]
              have := rres_trans (c := ConPanqueque.ExprFold.cost (.fvar i ty)) (t := t2) hb ⟨BitVec.le_refl _, fun _ _ _ => rfl⟩ rfl
                (by show t2.clock ≤ t2.clock + _; omega) (fun _ _ => rfl) rfl rfl
              simpa using this
            · rename_i hh; exact absurd (by decide) hh
          · have : ¬ jw < 0x8000000000000000#64 := by rw [BitVec.lt_def, hjw]; simpa using hj
            simp only [this, ↓reduceIte]
            split
            · rename_i hh; exact absurd rfl hh
            left; rw [hang_spec _ _ rfl]; exact Or.inl rfl
        · rename_i hh; exact absurd (by decide) hh
      · have : ¬ BitVec.ofNat 64 k < 0x8000000000000000#64 := by rw [BitVec.lt_def, hkw]; simpa using hk63
        simp only [this, ↓reduceIte]
        split
        · rename_i hh; exact absurd rfl hh
        left; rw [hang_spec _ _ rfl]; exact Or.inl rfl
    · rename_i hh; exact absurd (by decide) hh
  · have : ¬ iw < ew := by rw [BitVec.lt_def, hiw, hew]; exact hin
    simp only [this, ↓reduceIte]
    split
    · rename_i hh; exact absurd rfl hh
    exact keep (by omega) t5 (by simp only [t5]; rw [lookup_setVar_other _ _ (by decide)]; exact l4u) rfl rfl rfl rfl rfl rfl

theorem abstractRange_spec {σ : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (fn : MlS)
    (C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (d n : Nat) (hdn : d + n < 2 ^ 63)
    (hC : C.lookup fn = some ([(iU, .one), (iK, .one)], body Abstract1.cutF (cases idCase fvarCase idCase idCase fn), .one))
    (lo : BitVec 64) {h : Heap} {p : BitVec 64} {e : ConLeche.Expr} (he : ExprAt h p e) :
    Spec (σ := σ) idCase fvarCase idCase idCase fn C (inv d n) (shape d n hdn) lo h p e :=
  subst_spec ra idCase fvarCase idCase idCase fn C (inv d n) (shape d n hdn) hC lo
    (fun h p vw i he h0 h2 hi => spec_leaf idCase fvarCase idCase idCase fn C (inv d n) (shape d n hdn) lo h p 0 _ he h0
      (fun k => ⟨by simp, by simp⟩))
    (fun h p vw q i ty he h0 h2 h3 hi hty _ => spec_fvar ra fn C d n hdn lo h p vw i ty he h0 h2 hi)
    (fun h p q u he h0 h2 hu => spec_leaf idCase fvarCase idCase idCase fn C (inv d n) (shape d n hdn) lo h p 2 _ he h0
      (fun k => ⟨by simp, by simp⟩))
    (fun h p q r nm us he h0 h2 h3 hn hus => spec_leaf idCase fvarCase idCase idCase fn C (inv d n) (shape d n hdn) lo h p 3 _ he h0
      (fun k => ⟨by simp, by simp⟩)) he

end ConPanqueque.AbstractRange
