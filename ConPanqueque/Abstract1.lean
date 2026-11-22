import ConPanqueque.Subst
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic ConPanqueque.Alloc ConPanqueque.ExprCons
open ConPanqueque.Node ConPanqueque.StateHeap ConPanqueque.Rebuild ConPanqueque.Subst

/-!
# `Expr.abstract1` in Pancake

An instance of the substitution template with the cutoff on the stored fvar
range (`fvarB ≤ d`, as con-leche's `abstract1C`): the index `d` is held in the
global `absd`; at `fvar d` the case builds `bvar k` (stopping if `k` does not
fit the small-natural representation); `bvar` is past the cutoff.
-/

namespace ConPanqueque.Abstract1

def gD := ofString "absd"
def iIv := ofString "iv"
def iI := ofString "i"
def iW := ofString "w"

def fvE : ExpHOL 64 := ConPanqueque.AppData.shr (ConPanqueque.AppData.shl (vv iDw) 48) 49
/-- `[fvarBRaw < satRange] · [fvarBRaw ≤ d]`. -/
def cutF : ExpHOL 64 := .panop .mul [.cmp .lower fvE (.const 32767), .cmp .notLower (.var .global gD) fvE]

def CutF (d : Nat) (e : ConLeche.Expr) (_k : Nat) : Prop := e.fvarBRaw < 32767 ∧ e.fvarBRaw ≤ d

instance (d : Nat) (e : ConLeche.Expr) (k : Nat) : Decidable (CutF d e k) := by unfold CutF; infer_instance

theorem eval_cutF {σ : Type} (t : PanSemStateFiniteExact 64 σ) (e : ConLeche.Expr) (d : Nat) (hd64 : d < 2 ^ 64)
    (hdw : t.locals.lookup iDw = some (.val (.word e.data.toBitVec)))
    (hg : t.globals.lookup gD = some (.val (.word (BitVec.ofNat 64 d)))) :
    ∃ w, @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) cutF =
      some (.val (.word w)) ∧ (w ≠ 0 ↔ CutF d e 0) := by
  refine ⟨if CutF d e 0 then 1 else 0, ?_, by by_cases h : CutF d e 0 <;> simp [h]⟩
  have hx : (e.data.toBitVec <<< (48 : Nat) >>> (49 : Nat)).toNat = e.fvarBRaw := by
    simp [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
      ConLeche.Expr.fvarBRaw, ConLeche.fvarOfData, UInt64.toNat_div, UInt64.toNat_mod]
    omega
  simp [cutF, fvE, ConPanqueque.AppData.shr, ConPanqueque.AppData.shl, vv, evalHOLExact, evalListHOLExact, hdw, hg,
    wordShiftHOL, panOpHOL, valueIsWord, valueWord, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  generalize e.data.toBitVec <<< (48 : Nat) >>> (49 : Nat) = x at *
  have e1 : x < 32767#64 ↔ e.fvarBRaw < 32767 := by simp [BitVec.lt_def, hx]
  have e2 : x ≤ BitVec.ofNat 64 d ↔ e.fvarBRaw ≤ d := by simp [BitVec.le_def, Nat.mod_eq_of_lt hd64, hx]
  by_cases c1 : e.fvarBRaw < 32767 <;> by_cases c2 : e.fvarBRaw ≤ d <;>
    simp [e1, e2, c1, c2, CutF]

private theorem abstract1_eq_self : ∀ {e : ConLeche.Expr} {d k : Nat},
    ConLeche.Expr.fvarsBelow d e → e.abstract1 d k = e := by
  intro e
  induction e <;> intro d k hb <;>
    simp_all only [ConLeche.Expr.fvarsBelow, ConLeche.Expr.abstract1]
  rw [ite_eq_right (by omega)]

/-- The leaf `fvar i ty`: `bvar k` if `i = d`, else the node. -/
def fvarCase : ProgHOL 64 :=
  .dec iIv .one (ldo iU 16)
   (.dec iI .one (.shift .lsr (vv iIv) (.const 1))
    (.ite (.cmp .equal (vv iI) (.var .global gD))
      (.ite (.cmp .lower (vv iK) (.const 0x8000000000000000#64))
        (.dec iW .one (.op .add [.op .add [vv iK, vv iK], .const 1])
          (.dec iIw .one (vv iK) (mkNode 0 ConPanqueque.ExprData.bvarDataE [iW])))
        hang)
      (.return (vv iU))))

/-- The index is held in the global `absd`. -/
def inv (d : Nat) : Subst.Inv where
  P gl _ := gl gD = some (.val (.word (BitVec.ofNat 64 d)))
  mono gl gl' h h' := fun x _ hg => by rw [hg gD (by decide)]; exact x

def shape (d : Nat) (hd64 : d < 2 ^ 64) : Subst.Shape (inv d) where
  F e k := e.abstract1 d k
  CP := CutF d
  ce := cutF
  ceval t e k _ hdw _ _ hg := eval_cutF t e d hd64 hdw hg
  leaf l k := ⟨by simp, by simp⟩
  cut e k h := abstract1_eq_self (ConLeche.Expr.fvarsBelow_iff.mpr (by
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
    (d : Nat) (hd64 : d < 2 ^ 64) (lo : BitVec 64) (h : Heap) (p vw : BitVec 64) (i : Nat) (ty : ConLeche.Expr)
    (he : ExprAt h p (.fvar i ty)) (h0 : h p = some (.word 1)) (h2 : h (p + 16) = some (.word vw)) (hi : NatAt h vw i) :
    Spec (σ := σ) idCase fvarCase idCase idCase fn C (inv d) (shape d hd64) lo h p (.fvar i ty) := by
  intro t k hp hcd hai hs hx hu hk hd hck
  obtain ⟨_, h8⟩ := exprAt_data he
  apply entry (cutF) (CutF d) (cases idCase fvarCase idCase idCase fn) t lo hp p 1 (.fvar i ty) k (by omega) hai hu hk (hs _ _ h0) (hs _ _ h8)
    (fun t' x y g => (shape d hd64).ceval t' _ k (by omega) x y _ (by rw [g]; exact hx))
  · intro hct; rw [(shape d hd64).cut _ _ hct]; exact exprAt_mono hs he
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
  have hgd : t4.globals.lookup gD = some (.val (.word (BitVec.ofNat 64 d))) := by
    show t2.globals.lookup gD = _; rw [g2]; exact hx
  have hdw : (BitVec.ofNat 64 d).toNat = d := by simp; omega
  rw [ite_word t4 _ _ _ (if iw = BitVec.ofNat 64 d then 1 else 0)
    (by simp [vv, evalHOLExact, l4i, hgd, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
  by_cases hid : i = d
  · have : iw = BitVec.ofNat 64 d := by simp only [iw, hid]
    simp only [this, ↓reduceIte]
    split
    · rw [ite_word t4 _ _ _ (if BitVec.ofNat 64 k < 0x8000000000000000#64 then 1 else 0)
        (by simp [vv, evalHOLExact, l4k, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
      by_cases hb : k < 2 ^ 63
      · have : BitVec.ofNat 64 k < 0x8000000000000000#64 := by rw [BitVec.lt_def, hkw]; simpa using hb
        simp only [this, ↓reduceIte]
        split
        · let w2 := BitVec.ofNat 64 (2 * k + 1)
          let t5 := setVarHOLFinite iW (.val (.word w2)) t4
          obtain ⟨L5, e5⟩ := dec_word' t4 iW (.op .add [.op .add [vv iK, vv iK], .const 1]) w2
            (.dec iIw .one (vv iK) (mkNode 0 ConPanqueque.ExprData.bvarDataE [iW]))
            (by simp [vv, evalHOLExact, evalListHOLExact, l4k, wordOpHOL, wordOp, valueIsWord, valueWord]
                apply BitVec.eq_of_toNat_eq; simp [w2, BitVec.toNat_add] <;> omega)
          let kw := (UInt64.ofNat k).toBitVec
          let t6 := setVarHOLFinite iIw (.val (.word kw)) t5
          obtain ⟨L6, e6⟩ := dec_word' t5 iIw (vv iK) kw (mkNode 0 ConPanqueque.ExprData.bvarDataE [iW])
            (by simp only [vv, evalHOLExact, t5]; rw [lookup_setVar_other _ _ (by decide), l4k]; simp [kw]; apply BitVec.eq_of_toNat_eq; simp)
          rw [e5]; apply rres_locals; rw [e6]; apply rres_locals
          have hai6 : AInv t6 lo hp := ainv_of_eq hai2 rfl rfl rfl
          rcases mkNode_ainv t6 lo hp 0 _ ConPanqueque.ExprData.bvarDataE [iW] [w2] rfl (by decide) (by decide)
              (by decide) (by simp) (ConPanqueque.ExprData.bvarDataE.eval t6 (UInt64.ofNat k)
                (by show t6.locals.lookup iIw = _; simp [t6, kw]))
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
          have hdat : (ConLeche.Expr.bvar k).data = ConPanqueque.ExprData.bvarDataW (UInt64.ofNat k) :=
            ConPanqueque.ExprData.bvar_data ra k hb
          refine ⟨hp, hr, _, a5, ⟨g5.le, g5.mem, g5.low⟩, ?_, cd5, ?_, gl5, md5, ta5⟩
          · show ExprAt _ hp ((ConLeche.Expr.fvar i ty).abstract1 d k)
            simp only [ConLeche.Expr.abstract1, hid, ↓reduceIte]
            exact .bvar hpos c0 (by rw [hdat]; exact c1) c2 ⟨hb, rfl⟩
          · rw [ck5]; show t2.clock ≤ t2.clock + ConPanqueque.ExprFold.cost (.fvar i ty); omega
        · rename_i hh; exact absurd (by decide) hh
      · have : ¬ BitVec.ofNat 64 k < 0x8000000000000000#64 := by rw [BitVec.lt_def, hkw]; simpa using hb
        simp only [this, ↓reduceIte]
        split
        · rename_i hh; exact absurd rfl hh
        left; rw [hang_spec _ _ rfl]; exact Or.inl rfl
    · rename_i hh; exact absurd (by decide) hh
  have hne : ¬ iw = BitVec.ofNat 64 d := fun e => hid (by rw [← hiw, e, hdw])
  simp only [hne, ↓reduceIte]
  split
  · rename_i hh; exact absurd rfl hh
  rw [eval_return_local t4 iU p l4u]
  apply rres_ret hai2 (by
      show ExprAt _ p ((ConLeche.Expr.fvar i ty).abstract1 d k)
      simp [ConLeche.Expr.abstract1, hid]; rw [hO2]; exact exprAt_mono hs he)
    <;> simp [emptyLocalsHOLFinite, t4, t3, setVarHOLFinite]

theorem abstract1_spec {σ : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (fn : MlS)
    (C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (d : Nat) (hd64 : d < 2 ^ 64)
    (hC : C.lookup fn = some ([(iU, .one), (iK, .one)], body cutF (cases idCase fvarCase idCase idCase fn), .one))
    (lo : BitVec 64) {h : Heap} {p : BitVec 64} {e : ConLeche.Expr} (he : ExprAt h p e) :
    Spec (σ := σ) idCase fvarCase idCase idCase fn C (inv d) (shape d hd64) lo h p e :=
  subst_spec ra idCase fvarCase idCase idCase fn C (inv d) (shape d hd64) hC lo
    (fun p vw i he h0 h2 hi => spec_leaf idCase fvarCase idCase idCase fn C (inv d) (shape d hd64) lo h p 0 _ he h0
      (fun k => ⟨by simp, by simp⟩))
    (fun p vw q i ty he h0 h2 h3 hi hty _ => spec_fvar ra fn C d hd64 lo h p vw i ty he h0 h2 hi)
    (fun p q u he h0 h2 hu => spec_leaf idCase fvarCase idCase idCase fn C (inv d) (shape d hd64) lo h p 2 _ he h0
      (fun k => ⟨by simp, by simp⟩))
    (fun p q r n us he h0 h2 h3 hn hus => spec_leaf idCase fvarCase idCase idCase fn C (inv d) (shape d hd64) lo h p 3 _ he h0
      (fun k => ⟨by simp, by simp⟩)) he

end ConPanqueque.Abstract1
