import ConPanqueque.Rebuild
import ConPanqueque.BinCons
import ConPanqueque.ExprData
import ConPanqueque.ExprFold
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic ConPanqueque.Alloc ConPanqueque.ExprCons
open ConPanqueque.Node ConPanqueque.StateHeap ConPanqueque.Rebuild

/-!
# Substitutions over expressions in Pancake: the template

con-leche's substitutions (`instantiate1P`, `liftLooseBVarsP`, `instantiateLiftP`,
…) share one shape: the cutoff on the stored loose-bvar bound, then a descent
that rebuilds `app`/`lam`/`forallE`/`letE`/`proj` nodes (depth `k + 1` under
binders) and does something specific at `bvar`. `body S.ce (cases bc fc sc cc fn)` is that
descent in Pancake with the `bvar` case `bc` a parameter; `subst_spec` proves it
computes any `F` with the shape's equations (`Shape`), given the `bvar` case's
spec, under an extra invariant `X` (e.g. a value held in a global) that only
needs to survive arena growth.
-/

namespace ConPanqueque.Subst

def iU := ofString "u"
def iK := ofString "k"
def iRa := ofString "ra"
def iRb := ofString "rb"
def vv (n : MlS) : ExpHOL 64 := .var .local n
def ldo (n : MlS) (off : BitVec 64) : ExpHOL 64 := .load .one (.op .add [vv n, .const off])

/-- Two children: `ra := fn(u[off1], k)`, `rb := fn(u[off2], k2)`, then the node `[tag, dexp, ra, rb]`. -/
def binCase (fn : MlS) (tag : BitVec 64) (dexp : ExpHOL 64) (k2 : ExpHOL 64) : ProgHOL 64 :=
  .dec iRa .one (.const 0) (.seq (.call (some (some (.local, iRa), none)) fn [ldo iU 16, vv iK])
    (.dec iRb .one (.const 0) (.seq (.call (some (some (.local, iRb), none)) fn [ldo iU 24, k2])
      (mkNode tag dexp [iRa, iRb]))))

theorem ldo_eval {σ : Type} (t : PanSemStateFiniteExact 64 σ) (n : MlS) (off p w : BitVec 64)
    (hn : t.locals.lookup n = some (.val (.word p))) (hd : t.memaddrs (p + off)) (hm : t.memory (p + off) = .word w) :
    @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) (ldo n off) =
      some (.val (.word w)) := by
  unfold ldo vv
  rw [eval_load_word t _ (p + off) (by simp [evalHOLExact, evalListHOLExact, hn, wordOpHOL, wordOp, valueIsWord,
    valueWord]) hd, hm]

/-- A word of the arena, read in a grown state. -/
theorem arena_read {σ : Type} {t t' : PanSemStateFiniteExact 64 σ} {lo hp hp' a w : BitVec 64}
    (ha : hOf t lo hp a = some (.word w)) (g : Grows t t' lo hp hp') (hi : AInv t' lo hp') :
    t'.memaddrs a ∧ t'.memory a = .word w := by
  have := grows_sub g a _ ha
  exact (ainv_arena hi).1 a _ this

theorem bin_case {σ : Type} (bc fc sc cc : ProgHOL 64) (fn : MlS) (C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (B : ProgHOL 64) (hC : C.lookup fn = some ([(iU, .one), (iK, .one)], B, .one))
    (tag : BitVec 64) (dexp k2 : ExpHOL 64) (v1 v2 vn : ConLeche.Expr) (dv : BitVec 64) (c1 c2 : Nat)
    (t : PanSemStateFiniteExact 64 σ) (lo hp p kw k2w cp1 cp2 : BitVec 64)
    (hcode : t.code = C) (hi : AInv t lo hp)
    (hu : t.locals.lookup iU = some (.val (.word p))) (hk : t.locals.lookup iK = some (.val (.word kw)))
    (hk2 : ∀ t' : PanSemStateFiniteExact 64 σ, t'.locals.lookup iK = some (.val (.word kw)) →
      @evalHOLExact 64 σ _ t'.toExact (fun a => Classical.propDecidable (t'.memaddrs a)) k2 = some (.val (.word k2w)))
    (h1 : hOf t lo hp (p + 16) = some (.word cp1)) (h2 : hOf t lo hp (p + 24) = some (.word cp2))
    (hck : 2 + c1 + c2 ≤ t.clock)
    (hB1 : ∀ s' : PanSemStateFiniteExact 64 σ, ∀ hq, s'.code = C → AInv s' lo hq → Sub (hOf t lo hp) (hOf s' lo hq) →
      (∀ g, g ≠ nHp → s'.globals.lookup g = t.globals.lookup g) →
      s'.locals.lookup iU = some (.val (.word cp1)) → s'.locals.lookup iK = some (.val (.word kw)) →
      c1 ≤ s'.clock → RRes s' (evaluateHOLFiniteState s' B) lo hq (fun h q => ExprAt h q v1) c1)
    (hB2 : ∀ s' : PanSemStateFiniteExact 64 σ, ∀ hq, s'.code = C → AInv s' lo hq → Sub (hOf t lo hp) (hOf s' lo hq) →
      (∀ g, g ≠ nHp → s'.globals.lookup g = t.globals.lookup g) →
      s'.locals.lookup iU = some (.val (.word cp2)) → s'.locals.lookup iK = some (.val (.word k2w)) →
      c2 ≤ s'.clock → RRes s' (evaluateHOLFiniteState s' B) lo hq (fun h q => ExprAt h q v2) c2)
    (hdata : ∀ (t' : PanSemStateFiniteExact 64 σ) (h' : Heap) (q1 q2 : BitVec 64), InMem t' h' →
      ExprAt h' q1 v1 → ExprAt h' q2 v2 → t'.locals.lookup iRa = some (.val (.word q1)) →
      t'.locals.lookup iRb = some (.val (.word q2)) →
      @evalHOLExact 64 σ _ t'.toExact (fun a => Classical.propDecidable (t'.memaddrs a)) dexp = some (.val (.word dv)))
    (hbuild : ∀ (h' : Heap) (p0 q1 q2 : BitVec 64), p0 ≠ 0 → h' p0 = some (.word tag) →
      h' (p0 + 8) = some (.word dv) → h' (p0 + 16) = some (.word q1) → h' (p0 + 24) = some (.word q2) →
      ExprAt h' q1 v1 → ExprAt h' q2 v2 → ExprAt h' p0 vn) :
    RRes t (evaluateHOLFiniteState t (binCase fn tag dexp k2)) lo hp (fun h q => ExprAt h q vn) (2 + c1 + c2) := by
  have dAU : iRa ≠ iU := by decide
  have dAK : iRa ≠ iK := by decide
  have dBU : iRb ≠ iU := by decide
  have dBK : iRb ≠ iK := by decide
  have dAB : iRa ≠ iRb := by decide
  -- ra := 0
  let t1 := setVarHOLFinite iRa (.val (.word 0)) t
  obtain ⟨L1, e1⟩ := dec_word' t iRa (.const 0) 0
    (.seq (.call (some (some (.local, iRa), none)) fn [ldo iU 16, vv iK])
      (.dec iRb .one (.const 0) (.seq (.call (some (some (.local, iRb), none)) fn [ldo iU 24, k2])
        (mkNode tag dexp [iRa, iRb])))) (by simp [evalHOLExact])
  have hu1 : t1.locals.lookup iU = some (.val (.word p)) := by
    simp only [t1]; rw [lookup_setVar_other _ _ (Ne.symm dAU)]; exact hu
  have hk1 : t1.locals.lookup iK = some (.val (.word kw)) := by
    simp only [t1]; rw [lookup_setVar_other _ _ (Ne.symm dAK)]; exact hk
  have m1 := (ainv_arena hi).1 _ _ h1
  have m2 := (ainv_arena hi).1 _ _ h2
  have hOf1 : hOf t1 lo hp = hOf t lo hp := hOf_of_eq lo hp rfl
  -- first child
  rcases call_child fn iRa iU iK C B _ (by decide) hC (fun h q => ExprAt h q v1) c1 t1 lo hp cp1 kw (ldo iU 16) (vv iK)
      hcode (ainv_of_eq hi rfl rfl rfl) (ldo_eval t1 iU 16 p cp1 hu1 m1.1 m1.2)
      (by simp [vv, evalHOLExact, hk1]) ⟨0, by simp [t1]⟩ (by show 1 + c1 ≤ t.clock; omega)
      (fun s' hcs ha hm hg hu' hk' hc' => hB1 s' hp hcs ha
        (by rw [hOf_of_eq (s := t1) lo hp hm, hOf1]; exact fun a w h => h) (fun g _ => by rw [hg]; rfl) hu' hk' hc') with
    hs | ⟨t2, q1, hp2, ev2, a2, g2, r1, lra2, lo2, cd2, ck2, gl2, md2, ta2⟩
  · left; unfold binCase; rw [e1]; exact hs
  -- rb := 0
  let t3 := setVarHOLFinite iRb (.val (.word 0)) t2
  obtain ⟨L3, e3⟩ := dec_word' t2 iRb (.const 0) 0
    (.seq (.call (some (some (.local, iRb), none)) fn [ldo iU 24, k2]) (mkNode tag dexp [iRa, iRb]))
    (by simp [evalHOLExact])
  have hu3 : t3.locals.lookup iU = some (.val (.word p)) := by
    simp only [t3]; rw [lookup_setVar_other _ _ (Ne.symm dBU), lo2 _ (Ne.symm dAU)]; exact hu1
  have hk3 : t3.locals.lookup iK = some (.val (.word kw)) := by
    simp only [t3]; rw [lookup_setVar_other _ _ (Ne.symm dBK), lo2 _ (Ne.symm dAK)]; exact hk1
  have g2' : Grows t t2 lo hp hp2 := ⟨g2.le, g2.mem⟩
  have hOf3 : hOf t3 lo hp2 = hOf t2 lo hp2 := hOf_of_eq lo hp2 rfl
  have m2' := arena_read h2 g2' a2
  -- second child
  rcases call_child fn iRb iU iK C B _ (by decide) hC (fun h q => ExprAt h q v2) c2 t3 lo hp2 cp2 k2w (ldo iU 24) k2
      (by show t2.code = C; rw [cd2]; exact hcode) (ainv_of_eq a2 rfl rfl rfl) (ldo_eval t3 iU 24 p cp2 hu3 m2'.1 m2'.2)
      (hk2 t3 hk3) ⟨0, by simp [t3]⟩ (by have : t1.clock = t.clock := rfl; show 1 + c2 ≤ t2.clock; omega)
      (fun s' hcs ha hm hg hu' hk' hc' => hB2 s' hp2 hcs ha
        (by rw [hOf_of_eq (s := t3) lo hp2 hm, hOf3]; exact grows_sub g2')
        (fun g hg' => by rw [hg]; show t2.globals.lookup g = _; rw [gl2 g hg']; rfl) hu' hk' hc') with
    hs | ⟨t4, q2, hp4, ev4, a4, g4, r2, lrb4, lo4, cd4, ck4, gl4, md4, ta4⟩
  · left; unfold binCase; rw [e1]; simp only; rw [ev2, e3]; exact hs
  have g4' : Grows t2 t4 lo hp2 hp4 := ⟨g4.le, g4.mem⟩
  have r1' : ExprAt (hOf t4 lo hp4) q1 v1 := exprAt_mono (grows_sub g4') r1
  have lra4 : t4.locals.lookup iRa = some (.val (.word q1)) := by
    rw [lo4 _ dAB]; simp only [t3]; rw [lookup_setVar_other _ _ dAB]; exact lra2
  -- the node
  rcases mkNode_ainv t4 lo hp4 tag dv dexp [iRa, iRb] [q1, q2] rfl (by decide) (by decide) (by decide) (by simp)
      (hdata t4 (hOf t4 lo hp4) q1 q2 (ainv_arena a4).1 r1' r2 lra4 lrb4)
      (fun j hj => match j, hj with
        | 0, _ => lra4
        | 1, _ => lrb4) a4 with
    hs | ⟨hr, a5, g5, hpos, cells, cd5, ck5, gl5, md5, ta5⟩
  · left; unfold binCase; rw [e1]; simp only; rw [ev2, e3]; simp only; rw [ev4]; exact hs
  right
  refine ⟨hp4, ?_, ?_⟩
  · unfold binCase; rw [e1]; simp only; rw [ev2, e3]; simp only; rw [ev4]; exact hr
  unfold binCase; rw [e1]; simp only; rw [ev2, e3]; simp only; rw [ev4]
  apply ok_locals; apply ok_locals
  have g5' : Grows t4 _ lo hp4 _ := g5
  have sub5 := grows_sub g5'
  have c0 := cells 0 (by decide)
  have c1' := cells 1 (by decide)
  have c2' := cells 2 (by decide)
  have c3' := cells 3 (by decide)
  simp only [at8, List.length_cons, List.length_nil] at c0 c1' c2' c3'
  have e0 : hp4 + BitVec.ofNat 64 (8 * 0) = hp4 := by simp
  have e8 : BitVec.ofNat 64 (8 * 1) = 8#64 := by decide
  have e16 : BitVec.ofNat 64 (8 * 2) = 16#64 := by decide
  have e24 : BitVec.ofNat 64 (8 * 3) = 24#64 := by decide
  rw [e0] at c0; rw [e8] at c1'; rw [e16] at c2'; rw [e24] at c3'
  refine ⟨_, a5, ?_, hbuild _ hp4 q1 q2 hpos c0 c1' c2' c3' (exprAt_mono sub5 r1') (exprAt_mono sub5 r2), ?_, ?_, ?_, ?_, ?_⟩
  · exact grows_trans (grows_trans g2' (grows_trans (grows_refl _ _ _) g4')) g5'
  · rw [cd5, cd4]; show t2.code = t.code; rw [cd2]; rfl
  · rw [ck5]; have : t1.clock = t.clock := rfl; have : t3.clock = t2.clock := rfl; omega
  · intro g hg; rw [gl5 g hg, gl4 g hg]; show t2.globals.lookup g = _; rw [gl2 g hg]; rfl
  · rw [md5, md4]; show t2.memaddrs = _; rw [md2]; rfl
  · rw [ta5, ta4]; show t2.topAddr = _; rw [ta2]; rfl

/-! ## The cutoff and the tag dispatch -/

def iDw := ofString "dw"
def bvE : ExpHOL 64 := ConPanqueque.AppData.shr (ConPanqueque.AppData.shl (vv iDw) 33) 49
/-- `[bvarBRaw < satRange] · [bvarBRaw ≤ k]`. -/
def cutE : ExpHOL 64 := .panop .mul [.cmp .lower bvE (.const 32767), .cmp .notLower (vv iK) bvE]

/-- The body: read the data word; past the cutoff return `u`; else dispatch on the tag. -/
def body (ce : ExpHOL 64) (cs : List (BitVec 64 × ProgHOL 64)) : ProgHOL 64 :=
  .dec iDw .one (ldo iU 8) (.ite ce (.return (vv iU))
    (.dec ConPanqueque.Fold.nTg .one (.load .one (vv iU)) (ConPanqueque.Fold.iteChain cs (.return (vv iU)))))

/-- The cutoff, in con-leche's terms. -/
def Cut (e : ConLeche.Expr) (k : Nat) : Prop := e.bvarBRaw < 32767 ∧ e.bvarBRaw ≤ k

instance (e : ConLeche.Expr) (k : Nat) : Decidable (Cut e k) := by unfold Cut; infer_instance

theorem eval_cutE {σ : Type} (t : PanSemStateFiniteExact 64 σ) (e : ConLeche.Expr) (k : Nat) (hk : k < 2 ^ 64)
    (hd : t.locals.lookup iDw = some (.val (.word e.data.toBitVec)))
    (hkw : t.locals.lookup iK = some (.val (.word (BitVec.ofNat 64 k)))) :
    @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) cutE =
      some (.val (.word (if Cut e k then 1 else 0))) := by
  have hb : (ConLeche.bvarOfData e.data).toBitVec = (e.data.toBitVec <<< 33) >>> 49 := ConPanqueque.DataWord.bvarOfData_bv _
  have hlt := ConLeche.bvarOfData_lt e.data
  simp [cutE, bvE, ConPanqueque.AppData.shr, ConPanqueque.AppData.shl, vv, evalHOLExact, evalListHOLExact, hd, hkw,
    wordShiftHOL, panOpHOL, valueIsWord, valueWord, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  have hx : (e.data.toBitVec <<< (33 : Nat) >>> (49 : Nat)).toNat = e.bvarBRaw := by
    simp [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
      ConLeche.Expr.bvarBRaw, ConLeche.bvarOfData, UInt64.toNat_div, UInt64.toNat_mod]
    omega
  generalize e.data.toBitVec <<< (33 : Nat) >>> (49 : Nat) = x at *
  have e1 : x < 32767#64 ↔ e.bvarBRaw < 32767 := by simp [BitVec.lt_def, hx]
  have e2 : x ≤ BitVec.ofNat 64 k ↔ e.bvarBRaw ≤ k := by simp [BitVec.le_def, Nat.mod_eq_of_lt hk, hx]
  by_cases c1 : e.bvarBRaw < 32767 <;> by_cases c2 : e.bvarBRaw ≤ k <;>
    simp [e1, e2, c1, c2, Cut]

theorem ok_of_eq {σ : Type} {t t2 st : PanSemStateFiniteExact 64 σ} {lo hp : BitVec 64} {P : Heap → BitVec 64 → Prop}
    {c : Nat} {q : BitVec 64} (h : ROk t2 st lo hp P c q) (hm : t2.memory = t.memory) (hcd : t2.code = t.code)
    (hck : t2.clock = t.clock) (hg : t2.globals = t.globals) (hd : t2.memaddrs = t.memaddrs)
    (ht : t2.topAddr = t.topAddr) : ROk t st lo hp P c q := by
  obtain ⟨hp', a, g, pq, cd, ck, gl, md, ta⟩ := h
  exact ⟨hp', a, ⟨g.le, fun b h1 h2 => by rw [g.mem b h1 h2, hm]⟩, pq, by rw [cd, hcd], by omega,
    fun g' h' => by rw [gl g' h', hg], by rw [md, hd], by rw [ta, ht]⟩

theorem rres_of_eq {σ : Type} {t t2 : PanSemStateFiniteExact 64 σ} {r : Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 σ}
    {lo hp : BitVec 64} {P : Heap → BitVec 64 → Prop} {c : Nat} (h : RRes t2 r lo hp P c)
    (hm : t2.memory = t.memory) (hcd : t2.code = t.code) (hck : t2.clock = t.clock) (hg : t2.globals = t.globals)
    (hd : t2.memaddrs = t.memaddrs) (ht : t2.topAddr = t.topAddr) : RRes t r lo hp P c := by
  rcases h with h | ⟨q, hr, ok⟩
  · exact Or.inl h
  · exact Or.inr ⟨q, hr, ok_of_eq ok hm hcd hck hg hd ht⟩

theorem rres_locals {σ : Type} {t : PanSemStateFiniteExact 64 σ} {r1 : Option (PanSemResultExact 64)}
    {st : PanSemStateFiniteExact 64 σ} {lo hp : BitVec 64} {P : Heap → BitVec 64 → Prop} {c : Nat}
    (L : HolFiniteMapExact MlS (ValueHOL 64)) (h : RRes t (r1, st) lo hp P c) :
    RRes t (r1, { st with locals := L }) lo hp P c := by
  rcases h with h | ⟨q, hr, ok⟩
  · exact Or.inl h
  · exact Or.inr ⟨q, hr, ok_locals L ok⟩

/-- Entering the body: past the cutoff the node itself is returned; else the case of its tag runs. -/
theorem entry {σ : Type} (ce : ExpHOL 64) (CP : ConLeche.Expr → Nat → Prop)
    (cs : List (BitVec 64 × ProgHOL 64)) (t : PanSemStateFiniteExact 64 σ)
    (lo hp p tg : BitVec 64) (e : ConLeche.Expr) (k : Nat) (hk : k < 2 ^ 64) (hi : AInv t lo hp)
    (hu : t.locals.lookup iU = some (.val (.word p))) (hkw : t.locals.lookup iK = some (.val (.word (BitVec.ofNat 64 k))))
    (h0 : hOf t lo hp p = some (.word tg)) (h8 : hOf t lo hp (p + 8) = some (.word e.data.toBitVec))
    (hce : ∀ t' : PanSemStateFiniteExact 64 σ, t'.locals.lookup iDw = some (.val (.word e.data.toBitVec)) →
      t'.locals.lookup iK = some (.val (.word (BitVec.ofNat 64 k))) → t'.globals = t.globals →
      ∃ w, @evalHOLExact 64 σ _ t'.toExact (fun a => Classical.propDecidable (t'.memaddrs a)) ce =
        some (.val (.word w)) ∧ (w ≠ 0 ↔ CP e k))
    (P : Heap → BitVec 64 → Prop) (c : Nat)
    (hcut : CP e k → P (hOf t lo hp) p)
    (hcase : ¬ CP e k → ∀ t2 : PanSemStateFiniteExact 64 σ, t2.code = t.code → t2.memory = t.memory →
      t2.memaddrs = t.memaddrs → t2.globals = t.globals → t2.topAddr = t.topAddr → t2.clock = t.clock →
      t2.locals.lookup iU = some (.val (.word p)) → t2.locals.lookup iK = some (.val (.word (BitVec.ofNat 64 k))) →
      RRes t2 (evaluateHOLFiniteState t2 (ConPanqueque.Fold.pick tg cs (.return (vv iU)))) lo hp P c) :
    RRes t (evaluateHOLFiniteState t (body ce cs)) lo hp P c := by
  have m0 := (ainv_arena hi).1 _ _ h0
  have m8 := (ainv_arena hi).1 _ _ h8
  let t1 := setVarHOLFinite iDw (.val (.word e.data.toBitVec)) t
  obtain ⟨L1, e1⟩ := dec_word' t iDw (ldo iU 8) e.data.toBitVec _ (ldo_eval t iU 8 p _ hu m8.1 m8.2)
  have hu1 : t1.locals.lookup iU = some (.val (.word p)) := by
    simp only [t1]; rw [lookup_setVar_other _ _ (by decide)]; exact hu
  have hk1 : t1.locals.lookup iK = some (.val (.word (BitVec.ofNat 64 k))) := by
    simp only [t1]; rw [lookup_setVar_other _ _ (by decide)]; exact hkw
  obtain ⟨w, hc, hw⟩ := hce t1 (by simp [t1]) hk1 rfl
  unfold body; rw [e1]
  apply rres_locals
  rw [ite_word t1 _ _ _ _ hc]
  by_cases hct : CP e k
  · have hw0 : ¬ w = 0 := hw.mpr hct
    simp only [ne_eq, hw0, not_false_eq_true, ↓reduceIte]
    · right
      refine ⟨p, ?_, ?_⟩
      · rw [evaluateHOLFiniteState_eq_evaluate_def]; simp [evalHOLExact, vv, hu1, shapeOfHOLExact]
      · rw [evaluateHOLFiniteState_eq_evaluate_def]
        simp only [vv, evalHOLExact, hu1]
        simp [shapeOfHOLExact, emptyLocalsHOLFinite]
        exact ⟨hp, ainv_of_eq hi rfl rfl rfl, ⟨BitVec.le_refl _, fun _ _ _ => rfl⟩,
          by rw [hOf_of_eq lo hp rfl]; exact hcut hct,
          rfl, by show t.clock ≤ t.clock + c; omega, fun _ _ => rfl, rfl, rfl⟩
  · have hw0 : w = 0 := Classical.byContradiction fun hne => hct (hw.mp hne)
    simp only [ne_eq, hw0, not_true_eq_false, ↓reduceIte]
    let t2 := setVarHOLFinite ConPanqueque.Fold.nTg (.val (.word tg)) t1
    obtain ⟨L2, e2⟩ := dec_word' t1 ConPanqueque.Fold.nTg (.load .one (vv iU)) tg _
      (by rw [eval_load_word t1 _ p (by simp [vv, evalHOLExact, hu1]) m0.1]; show some (ValueHOL.val (t.memory p)) = _; rw [m0.2])
    rw [e2]
    apply rres_locals
    rw [ConPanqueque.Fold.iteChain_eval t2 tg (by simp [t2]) cs]
    exact rres_of_eq (hcase hct t2 rfl rfl rfl rfl rfl rfl
      (by simp only [t2]; rw [lookup_setVar_other _ _ (by decide)]; exact hu1)
      (by simp only [t2]; rw [lookup_setVar_other _ _ (by decide)]; exact hk1)) rfl rfl rfl rfl rfl rfl

/-! ## The data words of rebuilt nodes -/

theorem data_load {σ : Type} {t : PanSemStateFiniteExact 64 σ} {h : Heap} {x : MlS} {q : BitVec 64}
    {e : ConLeche.Expr} (hm : InMem t h) (he : ExprAt h q e) (hx : t.locals.lookup x = some (.val (.word q))) :
    @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) (ldo x 8) =
      some (.val (.word e.data.toBitVec)) := by
  obtain ⟨_, h8⟩ := exprAt_data he
  obtain ⟨d, m⟩ := hm _ _ h8
  exact ldo_eval t x 8 q _ hx d m

theorem app_data {σ : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (v1 v2 : ConLeche.Expr)
    (t' : PanSemStateFiniteExact 64 σ) (h' : Heap) (q1 q2 : BitVec 64) (hm : InMem t' h')
    (e1 : ExprAt h' q1 v1) (e2 : ExprAt h' q2 v2) (l1 : t'.locals.lookup iRa = some (.val (.word q1)))
    (l2 : t'.locals.lookup iRb = some (.val (.word q2))) :
    @evalHOLExact 64 σ _ t'.toExact (fun a => Classical.propDecidable (t'.memaddrs a))
      (ConPanqueque.AppData.appDataExp (ldo iRa 8) (ldo iRb 8)) = some (.val (.word (ConLeche.Expr.app v1 v2).data.toBitVec)) :=
  ConPanqueque.AppData.eval_appDataExp ra t' _ _ v1 v2 (data_load hm e1 l1) (data_load hm e2 l2)

theorem lam_data {σ : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (v1 v2 : ConLeche.Expr)
    (t' : PanSemStateFiniteExact 64 σ) (h' : Heap) (q1 q2 : BitVec 64) (hm : InMem t' h')
    (e1 : ExprAt h' q1 v1) (e2 : ExprAt h' q2 v2) (l1 : t'.locals.lookup iRa = some (.val (.word q1)))
    (l2 : t'.locals.lookup iRb = some (.val (.word q2))) :
    @evalHOLExact 64 σ _ t'.toExact (fun a => Classical.propDecidable (t'.memaddrs a))
      (ConPanqueque.BinCons.binDataExp (19 : UInt64).toBitVec (ldo iRa 8) (ldo iRb 8)) =
      some (.val (.word (ConLeche.Expr.lam v1 v2).data.toBitVec)) := by
  rw [ConPanqueque.BinCons.eval_binDataExp t' 19 _ _ v1 v2 (data_load hm e1 l1) (data_load hm e2 l2),
    (ConPanqueque.BinCons.bin_data_bv ra v1 v2).1]

theorem forallE_data {σ : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (v1 v2 : ConLeche.Expr)
    (t' : PanSemStateFiniteExact 64 σ) (h' : Heap) (q1 q2 : BitVec 64) (hm : InMem t' h')
    (e1 : ExprAt h' q1 v1) (e2 : ExprAt h' q2 v2) (l1 : t'.locals.lookup iRa = some (.val (.word q1)))
    (l2 : t'.locals.lookup iRb = some (.val (.word q2))) :
    @evalHOLExact 64 σ _ t'.toExact (fun a => Classical.propDecidable (t'.memaddrs a))
      (ConPanqueque.BinCons.binDataExp (23 : UInt64).toBitVec (ldo iRa 8) (ldo iRb 8)) =
      some (.val (.word (ConLeche.Expr.forallE v1 v2).data.toBitVec)) := by
  rw [ConPanqueque.BinCons.eval_binDataExp t' 23 _ _ v1 v2 (data_load hm e1 l1) (data_load hm e2 l2),
    (ConPanqueque.BinCons.bin_data_bv ra v1 v2).2]

def kPlus1 : ExpHOL 64 := .op .add [vv iK, .const 1]

theorem eval_kPlus1 {σ : Type} (k : Nat) (t' : PanSemStateFiniteExact 64 σ)
    (hk : t'.locals.lookup iK = some (.val (.word (BitVec.ofNat 64 k)))) :
    @evalHOLExact 64 σ _ t'.toExact (fun a => Classical.propDecidable (t'.memaddrs a)) kPlus1 =
      some (.val (.word (BitVec.ofNat 64 (k + 1)))) := by
  simp [kPlus1, vv, evalHOLExact, evalListHOLExact, hk, wordOpHOL, wordOp, valueIsWord, valueWord]
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add]

/-! ## The program -/

def iIw := ofString "iw"
def iRc := ofString "rc"
def iDt := ofString "dt"
def iDv := ofString "dv"
def iDb := ofString "db"
def letFin : ProgHOL 64 :=
  .dec iDt .one (ldo iRa 8) (.dec iDv .one (ldo iRb 8) (.dec iDb .one (ldo iRc 8)
    (mkNode 7 ConPanqueque.ExprData.letDataE [iRa, iRb, iRc])))
def letCase (fn : MlS) : ProgHOL 64 :=
  .dec iRa .one (.const 0) (.seq (.call (some (some (.local, iRa), none)) fn [ldo iU 16, vv iK])
  (.dec iRb .one (.const 0) (.seq (.call (some (some (.local, iRb), none)) fn [ldo iU 24, vv iK])
  (.dec iRc .one (.const 0) (.seq (.call (some (some (.local, iRc), none)) fn [ldo iU 32, kPlus1]) letFin)))))
def iNm := ofString "nm"
def iIx := ofString "ix"
def iHs := ofString "hs"
def iDe := ofString "de"
def projFin : ProgHOL 64 :=
  .dec iHs .one (.const 1723) (.seq (.ite (.cmp .notEqual (vv iNm) (.const 0)) (.assign .local iHs (ldo iNm 8)) .skip)
   (.dec iIw .one (.shift .lsr (vv iIx) (.const 1)) (.dec iDe .one (ldo iRa 8)
     (mkNode 9 ConPanqueque.ExprData.projDataE [iNm, iIx, iRa]))))
def projCase (fn : MlS) : ProgHOL 64 :=
  .dec iNm .one (ldo iU 16) (.dec iIx .one (ldo iU 24)
   (.dec iRa .one (.const 0) (.seq (.call (some (some (.local, iRa), none)) fn [ldo iU 32, vv iK]) projFin)))

/-- A leaf case that returns the node. -/
def idCase : ProgHOL 64 := .return (vv iU)

def cases (bc fc sc cc : ProgHOL 64) (fn : MlS) : List (BitVec 64 × ProgHOL 64) :=
  [(0, bc), (1, fc), (2, sc), (3, cc),
   (4, binCase fn 4 (ConPanqueque.AppData.appDataExp (ldo iRa 8) (ldo iRb 8)) (vv iK)),
   (5, binCase fn 5 (ConPanqueque.BinCons.binDataExp (19 : UInt64).toBitVec (ldo iRa 8) (ldo iRb 8)) kPlus1),
   (6, binCase fn 6 (ConPanqueque.BinCons.binDataExp (23 : UInt64).toBitVec (ldo iRa 8) (ldo iRb 8)) kPlus1),
   (7, letCase fn),
   (9, projCase fn)]

/-- Binder depth: how far `k` grows below the root. -/
def bdepth : ConLeche.Expr → Nat
  | .app f a => max (bdepth f) (bdepth a)
  | .lam t b | .forallE t b => max (bdepth t) (bdepth b + 1)
  | .letE t v b => max (max (bdepth t) (bdepth v)) (bdepth b + 1)
  | .proj _ _ e => bdepth e
  | .fvar _ ty => bdepth ty
  | _ => 0

/-- An extra invariant over the globals and the arena that survives arena growth. -/
structure Inv where
  P : (MlS → Option (ValueHOL 64)) → Heap → Prop
  mono : ∀ gl gl' h h', P gl h → Sub h h' → (∀ g, g ≠ nHp → gl' g = gl g) → P gl' h'

/-- The equations of a substitution `F e k` (`k`: binders passed): the identity past the
cutoff, and a rebuild of each compound node. -/
structure Shape (X : Inv) where
  F : ConLeche.Expr → Nat → ConLeche.Expr
  /-- The cutoff: past it `F` is the identity. -/
  CP : ConLeche.Expr → Nat → Prop
  /-- Its test in Pancake, over the data word `dw` and the depth `k`. -/
  ce : ExpHOL 64
  ceval : ∀ {σ : Type} (t : PanSemStateFiniteExact 64 σ) (e : ConLeche.Expr) (k : Nat), k < 2 ^ 64 →
    t.locals.lookup iDw = some (.val (.word e.data.toBitVec)) →
    t.locals.lookup iK = some (.val (.word (BitVec.ofNat 64 k))) → ∀ h, X.P t.globals.lookup h →
    ∃ w, @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) ce =
      some (.val (.word w)) ∧ (w ≠ 0 ↔ CP e k)
  /-- Literals are always past the cutoff. -/
  leaf : ∀ l k, CP (.lit l) k
  cut : ∀ e k, CP e k → F e k = e
  /-- The clock a call uses (an upper bound on the calls it makes). -/
  cost : ConLeche.Expr → Nat
  cost_app : ∀ f a, cost (.app f a) = 2 + cost f + cost a
  cost_lam : ∀ t b, cost (.lam t b) = 2 + cost t + cost b
  cost_forallE : ∀ t b, cost (.forallE t b) = 2 + cost t + cost b
  cost_letE : ∀ t v b, cost (.letE t v b) = 1 + cost t + (1 + cost v + (1 + cost b + 0))
  cost_proj : ∀ n i e, cost (.proj n i e) = 1 + cost e + 0
  app : ∀ f a k, F (.app f a) k = .app (F f k) (F a k)
  lam : ∀ t b k, F (.lam t b) k = .lam (F t k) (F b (k + 1))
  forallE : ∀ t b k, F (.forallE t b) k = .forallE (F t k) (F b (k + 1))
  letE : ∀ t v b k, F (.letE t v b) k = .letE (F t k) (F v k) (F b (k + 1))
  proj : ∀ n i e k, F (.proj n i e) k = .proj n i (F e k)

/-- What a call on `e` at depth `k` does. -/
def Spec {σ : Type} (bc fc sc cc : ProgHOL 64) (fn : MlS) (C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (X : Inv) (S : Shape X) (lo : BitVec 64) (h : Heap) (p : BitVec 64) (e : ConLeche.Expr) : Prop :=
  ∀ (t : PanSemStateFiniteExact 64 σ) (k : Nat) (hp : BitVec 64), t.code = C → AInv t lo hp →
    Sub h (hOf t lo hp) → X.P t.globals.lookup (hOf t lo hp) →
    t.locals.lookup iU = some (.val (.word p)) → t.locals.lookup iK = some (.val (.word (BitVec.ofNat 64 k))) →
    k + bdepth e < 2 ^ 64 → S.cost e ≤ t.clock →
    RRes t (evaluateHOLFiniteState t (body S.ce (cases bc fc sc cc fn))) lo hp (fun h q => ExprAt h q (S.F e k))
      (S.cost e)

/-- A two-child node of `inst1`, from its children's specs. -/
theorem spec_bin {σ : Type} (bc fc sc cc : ProgHOL 64) (fn : MlS) (C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (X : Inv) (S : Shape X)
    (hC : C.lookup fn = some ([(iU, .one), (iK, .one)], body S.ce (cases bc fc sc cc fn), .one)) (lo : BitVec 64)
    (h : Heap) (p q r : BitVec 64) (e f a : ConLeche.Expr) (tg : BitVec 64) (dexp k2 : ExpHOL 64) (bump : Nat)
    (hpick : ConPanqueque.Fold.pick tg (cases bc fc sc cc fn) (.return (vv iU)) = binCase fn tg dexp k2)
    (hk2 : ∀ (k : Nat) (t' : PanSemStateFiniteExact 64 σ), t'.locals.lookup iK = some (.val (.word (BitVec.ofNat 64 k))) →
      @evalHOLExact 64 σ _ t'.toExact (fun a => Classical.propDecidable (t'.memaddrs a)) k2 =
        some (.val (.word (BitVec.ofNat 64 (k + bump)))))
    (hcost : S.cost e = 2 + S.cost f + S.cost a)
    (hdep : ∀ k, k + bdepth e < 2 ^ 64 → k + bdepth f < 2 ^ 64 ∧ k + bump + bdepth a < 2 ^ 64)
    (hdata : ∀ (k : Nat) (t' : PanSemStateFiniteExact 64 σ) (h' : Heap) (q1 q2 : BitVec 64), InMem t' h' →
      ExprAt h' q1 (S.F f k) → ExprAt h' q2 (S.F a (k + bump)) →
      t'.locals.lookup iRa = some (.val (.word q1)) → t'.locals.lookup iRb = some (.val (.word q2)) →
      @evalHOLExact 64 σ _ t'.toExact (fun a => Classical.propDecidable (t'.memaddrs a)) dexp =
        some (.val (.word (S.F e k).data.toBitVec)))
    (hbuild : ∀ (k : Nat) (h' : Heap) (p0 q1 q2 : BitVec 64), p0 ≠ 0 → h' p0 = some (.word tg) →
      h' (p0 + 8) = some (.word (S.F e k).data.toBitVec) → h' (p0 + 16) = some (.word q1) →
      h' (p0 + 24) = some (.word q2) → ExprAt h' q1 (S.F f k) →
      ExprAt h' q2 (S.F a (k + bump)) → ExprAt h' p0 (S.F e k))
    (he : ExprAt h p e) (h0 : h p = some (.word tg)) (h2 : h (p + 16) = some (.word q))
    (h3 : h (p + 24) = some (.word r))
    (ihf : Spec (σ := σ) bc fc sc cc fn C X S lo h q f) (iha : Spec (σ := σ) bc fc sc cc fn C X S lo h r a) :
    Spec (σ := σ) bc fc sc cc fn C X S lo h p e := by
  intro t k hp hcd hi hs hx hu hk hd hck
  have hk64 : k < 2 ^ 64 := by omega
  obtain ⟨_, h8⟩ := exprAt_data he
  apply entry S.ce S.CP (cases bc fc sc cc fn) t lo hp p tg e k hk64 hi hu hk (hs _ _ h0) (hs _ _ h8)
    (fun t' a b g => S.ceval t' _ k (by omega) a b _ (by rw [g]; exact hx))
  · intro hct; rw [S.cut _ _ hct]; exact exprAt_mono hs he
  intro hct t2 cd2 m2 d2 g2 ta2 ck2 hu2 hk2'
  rw [hpick, hcost]
  have hO2 : hOf t2 lo hp = hOf t lo hp := hOf_of_eq lo hp m2
  obtain ⟨df, da⟩ := hdep k hd
  exact bin_case bc fc sc cc fn C _ hC tg dexp k2 (S.F f k) (S.F a (k + bump)) (S.F e k)
    _ (S.cost f) (S.cost a) t2 lo hp p _ _ q r
    (by rw [cd2]; exact hcd) (ainv_of_eq hi g2 d2 ta2) hu2 hk2' (hk2 k)
    (by rw [hO2]; exact hs _ _ h2) (by rw [hO2]; exact hs _ _ h3) (by rw [ck2]; omega)
    (fun s' hq cd' a' sub' gl' hu' hk' hc' => ihf s' k hq cd' a'
      (fun x w hx => sub' x w (by rw [hO2]; exact hs x w hx))
      (X.mono _ _ _ _ hx (fun x w hx' => sub' x w (by rw [hO2]; exact hx')) (fun g hg => by rw [gl' g hg, g2]))
      hu' hk' df hc')
    (fun s' hq cd' a' sub' gl' hu' hk' hc' => iha s' (k + bump) hq cd' a'
      (fun x w hx => sub' x w (by rw [hO2]; exact hs x w hx))
      (X.mono _ _ _ _ hx (fun x w hx' => sub' x w (by rw [hO2]; exact hx')) (fun g hg => by rw [gl' g hg, g2]))
      hu' hk' da hc')
    (hdata k) (hbuild k)

/-- A node whose loose-bvar bound is `0`: always past the cutoff. -/
theorem spec_leaf {σ : Type} (bc fc sc cc : ProgHOL 64) (fn : MlS) (C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (X : Inv) (S : Shape X) (lo : BitVec 64) (h : Heap) (p tg : BitVec 64) (e : ConLeche.Expr)
    (he : ExprAt h p e) (h0 : h p = some (.word tg)) (hz : ∀ k, S.CP e k) : Spec (σ := σ) bc fc sc cc fn C X S lo h p e := by
  intro t k hp hcd hi hs hx hu hk hd hck
  obtain ⟨_, h8⟩ := exprAt_data he
  apply entry S.ce S.CP (cases bc fc sc cc fn) t lo hp p tg e k (by omega) hi hu hk (hs _ _ h0) (hs _ _ h8)
    (fun t' a b g => S.ceval t' _ k (by omega) a b _ (by rw [g]; exact hx))
  · intro hct; rw [S.cut _ _ hct]; exact exprAt_mono hs he
  · intro hct; exact absurd (hz k) hct

/-- Returning without allocating: the state differs from `s` only in its locals. -/
theorem rres_ret {σ : Type} {s st : PanSemStateFiniteExact 64 σ} {lo hp q : BitVec 64} {P : Heap → BitVec 64 → Prop}
    {c : Nat} (hi : AInv s lo hp) (hP : P (hOf s lo hp) q) (hm : st.memory = s.memory) (hcd : st.code = s.code)
    (hck : st.clock = s.clock) (hg : st.globals = s.globals) (hd : st.memaddrs = s.memaddrs)
    (ht : st.topAddr = s.topAddr) : RRes s (some (.returned (.val (.word q))), st) lo hp P c :=
  Or.inr ⟨q, rfl, hp, ainv_of_eq hi hg hd ht, ⟨BitVec.le_refl _, fun a _ _ => by rw [hm]⟩,
    by rw [hOf_of_eq lo hp hm]; exact hP, hcd, by show s.clock ≤ st.clock + c; omega, fun g _ => by rw [hg], hd, ht⟩

theorem eval_return_local {σ : Type} (t : PanSemStateFiniteExact 64 σ) (x : MlS) (w : BitVec 64)
    (hx : t.locals.lookup x = some (.val (.word w))) :
    evaluateHOLFiniteState t (.return (vv x)) = (some (.returned (.val (.word w))), emptyLocalsHOLFinite t) := by
  rw [evaluateHOLFiniteState_eq_evaluate_def]; simp [evalHOLExact, vv, hx, shapeOfHOLExact]

theorem fin_let {σ : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ)
    (lo hq q1 q2 q3 : BitVec 64) (v1 v2 v3 : ConLeche.Expr) (hi : AInv t lo hq)
    (e1 : ExprAt (hOf t lo hq) q1 v1) (e2 : ExprAt (hOf t lo hq) q2 v2) (e3 : ExprAt (hOf t lo hq) q3 v3)
    (l1 : t.locals.lookup iRa = some (.val (.word q1))) (l2 : t.locals.lookup iRb = some (.val (.word q2)))
    (l3 : t.locals.lookup iRc = some (.val (.word q3))) :
    RRes t (evaluateHOLFiniteState t letFin) lo hq (fun h q => ExprAt h q (.letE v1 v2 v3)) 0 := by
  have hm := (ainv_arena hi).1
  let t1 := setVarHOLFinite iDt (.val (.word v1.data.toBitVec)) t
  obtain ⟨L1, f1⟩ := dec_word' t iDt (ldo iRa 8) _ _ (data_load hm e1 l1)
  have hm1 : InMem t1 (hOf t lo hq) := inMem_of_eq rfl rfl hm
  let t2 := setVarHOLFinite iDv (.val (.word v2.data.toBitVec)) t1
  obtain ⟨L2, f2⟩ := dec_word' t1 iDv (ldo iRb 8) _ _
    (data_load hm1 e2 (by simp only [t1]; rw [lookup_setVar_other _ _ (by decide)]; exact l2))
  have hm2 : InMem t2 (hOf t lo hq) := inMem_of_eq rfl rfl hm
  let t3 := setVarHOLFinite iDb (.val (.word v3.data.toBitVec)) t2
  obtain ⟨L3, f3⟩ := dec_word' t2 iDb (ldo iRc 8) _ _
    (data_load hm2 e3 (by simp only [t2, t1]; rw [lookup_setVar_other _ _ (by decide),
      lookup_setVar_other _ _ (by decide)]; exact l3))
  have hl : ∀ y, y ≠ iDt → y ≠ iDv → y ≠ iDb → t3.locals.lookup y = t.locals.lookup y := by
    intro y a b c; simp only [t3, t2, t1]
    rw [lookup_setVar_other _ _ c, lookup_setVar_other _ _ b, lookup_setVar_other _ _ a]
  unfold letFin; rw [f1]; apply rres_locals'; rw [f2]; apply rres_locals'; rw [f3]; apply rres_locals'
  have hi3 : AInv t3 lo hq := ainv_of_eq hi rfl rfl rfl
  have hdat := ConPanqueque.ExprData.letDataE.eval t3 v1.data v2.data v3.data
    (by show t3.locals.lookup iDt = _; simp only [t3, t2]
        rw [lookup_setVar_other _ _ (by decide), lookup_setVar_other _ _ (by decide)]; simp [t1])
    (by show t3.locals.lookup iDv = _; simp only [t3]; rw [lookup_setVar_other _ _ (by decide)]; simp [t2])
    (by show t3.locals.lookup iDb = _; simp [t3])
  simp only [← ConPanqueque.ExprData.letE_data ra] at hdat
  rcases mkNode_ainv t3 lo hq 7 _ ConPanqueque.ExprData.letDataE [iRa, iRb, iRc] [q1, q2, q3] rfl (by decide)
      (by decide) (by decide) (by simp) hdat
      (fun j hj => match j, hj with
        | 0, _ => by show t3.locals.lookup iRa = _; rw [hl _ (by decide) (by decide) (by decide)]; exact l1
        | 1, _ => by show t3.locals.lookup iRb = _; rw [hl _ (by decide) (by decide) (by decide)]; exact l2
        | 2, _ => by show t3.locals.lookup iRc = _; rw [hl _ (by decide) (by decide) (by decide)]; exact l3) hi3 with
    hs | ⟨hr, a5, g5, hpos, cells, cd5, ck5, gl5, md5, ta5⟩
  · exact Or.inl hs
  right
  have sub5 := grows_sub (show Grows t _ lo hq _ from ⟨g5.le, g5.mem⟩)
  have c0 := cells 0 (by decide)
  have c1 := cells 1 (by decide)
  have c2 := cells 2 (by decide)
  have c3 := cells 3 (by decide)
  have c4 := cells 4 (by decide)
  simp only [at8, List.length_cons, List.length_nil] at c0 c1 c2 c3 c4
  have e0 : hq + BitVec.ofNat 64 (8 * 0) = hq := by simp
  rw [e0] at c0
  rw [show BitVec.ofNat 64 (8 * 1) = 8#64 from by decide] at c1
  rw [show BitVec.ofNat 64 (8 * 2) = 16#64 from by decide] at c2
  rw [show BitVec.ofNat 64 (8 * 3) = 24#64 from by decide] at c3
  rw [show BitVec.ofNat 64 (8 * 4) = 32#64 from by decide] at c4
  exact ⟨hq, hr, _, a5, ⟨g5.le, g5.mem⟩,
    .letE hpos c0 c1 c2 c3 c4 (exprAt_mono sub5 e1) (exprAt_mono sub5 e2) (exprAt_mono sub5 e3),
    cd5, by rw [ck5]; show t.clock ≤ t.clock + 0; omega, gl5, md5, ta5⟩

/-- `hs := hash(nm)` (con-leche's `Hashable Name`), then `rest`. -/
theorem hash_then {σ : Type} (t : PanSemStateFiniteExact 64 σ) (h : Heap) (q : BitVec 64) (n : ConLeche.Name)
    (hm : InMem t h) (hn : NameAt h q n) (hl : t.locals.lookup iNm = some (.val (.word q))) (rest : ProgHOL 64) :
    ∃ t' L, evaluateHOLFiniteState t (.dec iHs .one (.const 1723)
        (.seq (.ite (.cmp .notEqual (vv iNm) (.const 0)) (.assign .local iHs (ldo iNm 8)) .skip) rest)) =
        ((evaluateHOLFiniteState t' rest).1, { (evaluateHOLFiniteState t' rest).2 with locals := L }) ∧
      t'.locals.lookup iHs = some (.val (.word n.hashData.toBitVec)) ∧
      (∀ y, y ≠ iHs → t'.locals.lookup y = t.locals.lookup y) ∧
      t'.memory = t.memory ∧ t'.code = t.code ∧ t'.clock = t.clock ∧ t'.globals = t.globals ∧
      t'.memaddrs = t.memaddrs ∧ t'.topAddr = t.topAddr := by
  let t1 := setVarHOLFinite iHs (.val (.word 1723)) t
  obtain ⟨L1, e1⟩ := dec_word' t iHs (.const 1723) 1723
    (.seq (.ite (.cmp .notEqual (vv iNm) (.const 0)) (.assign .local iHs (ldo iNm 8)) .skip) rest) (by simp [evalHOLExact])
  have hl1 : t1.locals.lookup iNm = some (.val (.word q)) := by
    simp only [t1]; rw [lookup_setVar_other _ _ (by decide)]; exact hl
  have hc := ite_word t1 (.cmp .notEqual (vv iNm) (.const 0)) (.assign .local iHs (ldo iNm 8)) .skip
    (if q ≠ 0 then 1 else 0) (by simp [vv, evalHOLExact, hl1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
  by_cases hq : q = 0
  · subst hq
    have : n = .anonymous := by
      cases hn with
      | anonymous => rfl
      | str hp _ _ _ _ => exact absurd rfl hp
      | num hp _ _ _ _ => exact absurd rfl hp
    subst this
    have es : evaluateHOLFiniteState t1 (.ite (.cmp .notEqual (vv iNm) (.const 0)) (.assign .local iHs (ldo iNm 8)) .skip)
        = (none, t1) := by
      rw [hc]; simp only [ne_eq, not_true_eq_false, ↓reduceIte]
      rw [evaluateHOLFiniteState_eq_evaluate_def]
    rw [seq_normal _ es] at e1
    refine ⟨t1, L1, e1, by simp [t1]; rfl, fun y hy => lookup_setVar_other _ _ hy, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · have hns := nameAt_hash (s := t1) (inMem_of_eq rfl rfl hm) hn hq
    let t2 := setKvarHOLFinite .local iHs (.val (.word n.hashData.toBitVec)) t1
    have es : evaluateHOLFiniteState t1 (.ite (.cmp .notEqual (vv iNm) (.const 0)) (.assign .local iHs (ldo iNm 8)) .skip)
        = (none, t2) := by
      rw [hc]; simp only [ne_eq, hq, not_false_eq_true, ↓reduceIte]
      split
      · apply assign_ok
        · exact ldo_eval t1 iNm 8 q _ hl1 hns.1 hns.2
        · simp [isValidValueHOLFinite, lookupKvarHOLFinite, t1, shapeOfHOLExact, shapeEqHOL]
      · rename_i hh; exact absurd (by decide) hh
    rw [seq_normal _ es] at e1
    refine ⟨t2, L1, e1, by simp [t2, setKvarHOLFinite], fun y hy => ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    simp only [t2, setKvarHOLFinite, t1]
    rw [lookup_setVar_other _ _ hy, lookup_setVar_other _ _ hy]

theorem fin_proj {σ : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ)
    (lo hq q q1 : BitVec 64) (n : ConLeche.Name) (i : Nat) (v1 : ConLeche.Expr) (hi : AInv t lo hq)
    (hn : NameAt (hOf t lo hq) q n) (hi63 : i < 2 ^ 63) (e1 : ExprAt (hOf t lo hq) q1 v1)
    (lnm : t.locals.lookup iNm = some (.val (.word q)))
    (lix : t.locals.lookup iIx = some (.val (.word (BitVec.ofNat 64 (2 * i + 1)))))
    (lra : t.locals.lookup iRa = some (.val (.word q1))) :
    RRes t (evaluateHOLFiniteState t projFin) lo hq (fun h q => ExprAt h q (.proj n i v1)) 0 := by
  obtain ⟨t', L, f1, lhs, lo', mm, cd, ck, gl, md, ta⟩ := hash_then t (hOf t lo hq) q n (ainv_arena hi).1 hn lnm
    (.dec iIw .one (.shift .lsr (vv iIx) (.const 1)) (.dec iDe .one (ldo iRa 8)
      (mkNode 9 ConPanqueque.ExprData.projDataE [iNm, iIx, iRa])))
  unfold projFin; rw [f1]; apply rres_locals'
  let iw := (UInt64.ofNat i).toBitVec
  have lix' : t'.locals.lookup iIx = some (.val (.word (BitVec.ofNat 64 (2 * i + 1)))) := by
    rw [lo' _ (by decide)]; exact lix
  have hsh : BitVec.ofNat 64 (2 * i + 1) >>> (1 : Nat) = iw := by
    apply BitVec.eq_of_toNat_eq; simp [iw, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
  let t3 := setVarHOLFinite iIw (.val (.word iw)) t'
  obtain ⟨L3, f3⟩ := dec_word' t' iIw (.shift .lsr (vv iIx) (.const 1)) iw _
    (by simp [vv, evalHOLExact, lix', wordShiftHOL]; exact hsh)
  have hm3 : InMem t3 (hOf t lo hq) := by
    intro a w ha; obtain ⟨x, y⟩ := (ainv_arena hi).1 a w ha
    exact ⟨by show t'.memaddrs a; rw [md]; exact x, by show t'.memory a = w; rw [mm]; exact y⟩
  have lra3 : t3.locals.lookup iRa = some (.val (.word q1)) := by
    simp only [t3]; rw [lookup_setVar_other _ _ (by decide), lo' _ (by decide)]; exact lra
  let t4 := setVarHOLFinite iDe (.val (.word v1.data.toBitVec)) t3
  obtain ⟨L4, f4⟩ := dec_word' t3 iDe (ldo iRa 8) _ _ (data_load hm3 e1 lra3)
  rw [f3]; apply rres_locals'; rw [f4]; apply rres_locals'
  have hl4 : ∀ y, y ≠ iDe → y ≠ iIw → y ≠ iHs → t4.locals.lookup y = t.locals.lookup y := by
    intro y a b c; simp only [t4, t3]; rw [lookup_setVar_other _ _ a, lookup_setVar_other _ _ b, lo' _ c]
  have hi4 : AInv t4 lo hq := ⟨by show t'.globals.lookup nHp = _; rw [gl]; exact hi.hpv, hi.le, hi.pos,
    fun a h1 h2 => by show t'.memaddrs a; rw [md]; exact hi.mem a h1 h2,
    ⟨by show hq ≤ t'.topAddr; rw [ta]; exact hi.free.1,
     fun a h1 h2 => by show t'.memaddrs a; rw [md]; exact hi.free.2 a h1 (by rw [← ta]; exact h2)⟩⟩
  have hdat := ConPanqueque.ExprData.projDataE.eval t4 n.hashData (UInt64.ofNat i) v1.data
    (by show t4.locals.lookup iHs = _; simp only [t4, t3]
        rw [lookup_setVar_other _ _ (by decide), lookup_setVar_other _ _ (by decide)]; exact lhs)
    (by show t4.locals.lookup iIw = _; simp only [t4]; rw [lookup_setVar_other _ _ (by decide)]; simp [t3, iw])
    (by show t4.locals.lookup iDe = _; simp [t4])
  simp only [← ConPanqueque.ExprData.proj_data ra] at hdat
  rcases mkNode_ainv t4 lo hq 9 _ ConPanqueque.ExprData.projDataE [iNm, iIx, iRa] [q, _, q1] rfl (by decide)
      (by decide) (by decide) (by simp) hdat
      (fun j hj => match j, hj with
        | 0, _ => by show t4.locals.lookup iNm = _; rw [hl4 _ (by decide) (by decide) (by decide)]; exact lnm
        | 1, _ => by show t4.locals.lookup iIx = _; rw [hl4 _ (by decide) (by decide) (by decide)]; exact lix
        | 2, _ => by show t4.locals.lookup iRa = _; rw [hl4 _ (by decide) (by decide) (by decide)]; exact lra) hi4 with
    hs | ⟨hr, a5, g5, hpos, cells, cd5, ck5, gl5, md5, ta5⟩
  · exact Or.inl hs
  right
  have g5' : Grows t _ lo hq _ := ⟨g5.le, fun a h1 h2 => by rw [g5.mem a h1 h2]; show t'.memory a = _; rw [mm]⟩
  have sub5 := grows_sub g5'
  have c0 := cells 0 (by decide)
  have c1 := cells 1 (by decide)
  have c2 := cells 2 (by decide)
  have c3 := cells 3 (by decide)
  have c4 := cells 4 (by decide)
  simp only [at8, List.length_cons, List.length_nil] at c0 c1 c2 c3 c4
  have e0 : hq + BitVec.ofNat 64 (8 * 0) = hq := by simp
  rw [e0] at c0
  rw [show BitVec.ofNat 64 (8 * 1) = 8#64 from by decide] at c1
  rw [show BitVec.ofNat 64 (8 * 2) = 16#64 from by decide] at c2
  rw [show BitVec.ofNat 64 (8 * 3) = 24#64 from by decide] at c3
  rw [show BitVec.ofNat 64 (8 * 4) = 32#64 from by decide] at c4
  exact ⟨hq, hr, _, a5, g5',
    .proj hpos c0 c1 c2 c3 c4 (nameAt_mono sub5 hn) ⟨hi63, rfl⟩ (exprAt_mono sub5 e1),
    by rw [cd5]; exact cd, by rw [ck5]; show t.clock ≤ t'.clock + 0; omega,
    fun g hg => by rw [gl5 g hg]; show t'.globals.lookup g = _; rw [gl],
    by rw [md5]; exact md, by rw [ta5]; exact ta⟩

theorem hB_of_spec {σ : Type} {bc fc sc cc : ProgHOL 64} {fn : MlS} {C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)}
    {X : Inv} {S : Shape X} {lo : BitVec 64} {h : Heap} {q : BitVec 64} {f : ConLeche.Expr}
    (ihs : Spec (σ := σ) bc fc sc cc fn C X S lo h q f) (k : Nat) (ti : PanSemStateFiniteExact 64 σ) (hq : BitVec 64)
    (hsub : Sub h (hOf ti lo hq)) (hx : X.P ti.globals.lookup (hOf ti lo hq)) (hd : k + bdepth f < 2 ^ 64) :
    ∀ s' : PanSemStateFiniteExact 64 σ, s'.code = C → AInv s' lo hq → s'.memory = ti.memory →
      s'.globals = ti.globals → s'.locals.lookup iU = some (.val (.word q)) →
      s'.locals.lookup iK = some (.val (.word (BitVec.ofNat 64 k))) → S.cost f ≤ s'.clock →
      RRes s' (evaluateHOLFiniteState s' (body S.ce (cases bc fc sc cc fn))) lo hq (fun h q => ExprAt h q (S.F f k))
        (S.cost f) := by
  intro s' cd a m g hu hk hc
  exact ihs s' k hq cd a (by rw [hOf_of_eq lo hq m]; exact hsub)
    (X.mono _ _ _ _ hx (by rw [hOf_of_eq lo hq m]; exact fun a w h => h) (fun g' _ => by rw [g])) hu hk hd hc

theorem spec_letE {σ : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (bc fc sc cc : ProgHOL 64) (fn : MlS)
    (C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (X : Inv) (S : Shape X)
    (hC : C.lookup fn = some ([(iU, .one), (iK, .one)], body S.ce (cases bc fc sc cc fn), .one)) (lo : BitVec 64)
    (h : Heap) (p q r w : BitVec 64) (a b c : ConLeche.Expr) (he : ExprAt h p (.letE a b c))
    (h0 : h p = some (.word 7)) (h2 : h (p + 16) = some (.word q)) (h3 : h (p + 24) = some (.word r))
    (h4 : h (p + 32) = some (.word w))
    (iha : Spec (σ := σ) bc fc sc cc fn C X S lo h q a) (ihb : Spec (σ := σ) bc fc sc cc fn C X S lo h r b) (ihc : Spec (σ := σ) bc fc sc cc fn C X S lo h w c) :
    Spec (σ := σ) bc fc sc cc fn C X S lo h p (.letE a b c) := by
  intro t k hp hcd hai hs hx hu hk hd hck
  obtain ⟨_, h8⟩ := exprAt_data he
  apply entry S.ce S.CP (cases bc fc sc cc fn) t lo hp p 7 _ k (by omega) hai hu hk (hs _ _ h0) (hs _ _ h8)
    (fun t' a b g => S.ceval t' _ k (by omega) a b _ (by rw [g]; exact hx))
  · intro hct; rw [S.cut _ _ hct]; exact exprAt_mono hs he
  intro hct t2 cd2 m2 d2 g2 ta2 ck2 hu2 hk2
  show RRes t2 (evaluateHOLFiniteState t2 (letCase fn)) lo hp _ _
  have hO2 : hOf t2 lo hp = hOf t lo hp := hOf_of_eq lo hp m2
  have hai2 : AInv t2 lo hp := ainv_of_eq hai g2 d2 ta2
  have hs2 : Sub h (hOf t2 lo hp) := by rw [hO2]; exact hs
  have hx2 : X.P t2.globals.lookup (hOf t2 lo hp) :=
    X.mono _ _ _ _ hx (by rw [hO2]; exact fun a w h => h) (fun g _ => by rw [g2])
  simp only [bdepth] at hd
  have da : k + bdepth a < 2 ^ 64 := by omega
  have db : k + bdepth b < 2 ^ 64 := by omega
  have dc : k + 1 + bdepth c < 2 ^ 64 := by omega
  have hcost := S.cost_letE a b c
  rw [hcost] at hck ⊢
  rw [S.letE]
  have m16 := (ainv_arena hai2).1 _ _ (hs2 _ _ h2)
  unfold letCase
  apply step_call fn iRa iU iK C _ _ (by decide) hC (fun h q => ExprAt h q (S.F a k)) _ _ _ t2 lo hp q
    (BitVec.ofNat 64 k) (ldo iU 16) (vv iK) (by rw [cd2]; exact hcd) hai2
    (ldo_eval _ iU 16 p q (by rw [lookup_setVar_other _ _ (by decide)]; exact hu2) m16.1 m16.2)
    (by simp [vv, evalHOLExact]; rw [lookup_setVar_other _ _ (by decide)]; exact hk2) (by rw [ck2]; omega)
    (hB_of_spec iha k t2 hp hs2 hx2 da)
  intro t3 q1 hq1 cd3 a3 g3 r1 l3a l3o ck3 gl3 md3 ta3
  have hs3 : Sub h (hOf t3 lo hq1) := fun x y hx => grows_sub g3 x y (hs2 x y hx)
  have m24 := arena_read (hs2 _ _ h3) g3 a3
  have hu3 : t3.locals.lookup iU = some (.val (.word p)) := by rw [l3o _ (by decide)]; exact hu2
  have hk3 : t3.locals.lookup iK = some (.val (.word (BitVec.ofNat 64 k))) := by rw [l3o _ (by decide)]; exact hk2
  apply step_call fn iRb iU iK C _ _ (by decide) hC (fun h q => ExprAt h q (S.F b k)) _ _ _ t3 lo hq1 r
    (BitVec.ofNat 64 k) (ldo iU 24) (vv iK) cd3 a3
    (ldo_eval _ iU 24 p r (by rw [lookup_setVar_other _ _ (by decide)]; exact hu3) m24.1 m24.2)
    (by simp [vv, evalHOLExact] <;> (rw [lookup_setVar_other _ _ (by decide)]; exact hk3)) (by omega)
    (hB_of_spec ihb k t3 hq1 hs3 (X.mono _ _ _ _ hx2 (grows_sub g3) gl3) db)
  intro t4 q2 hq2 cd4 a4 g4 r2 l4b l4o ck4 gl4 md4 ta4
  have g34 := grows_trans g3 g4
  have hs4 : Sub h (hOf t4 lo hq2) := fun x y hx => grows_sub g34 x y (hs2 x y hx)
  have m32 := arena_read (hs2 _ _ h4) g34 a4
  have hu4 : t4.locals.lookup iU = some (.val (.word p)) := by rw [l4o _ (by decide)]; exact hu3
  have hk4 : t4.locals.lookup iK = some (.val (.word (BitVec.ofNat 64 k))) := by rw [l4o _ (by decide)]; exact hk3
  apply step_call fn iRc iU iK C _ _ (by decide) hC (fun h q => ExprAt h q (S.F c (k + 1))) _ _ _ t4 lo hq2 w
    (BitVec.ofNat 64 (k + 1)) (ldo iU 32) kPlus1 cd4 a4
    (ldo_eval _ iU 32 p w (by rw [lookup_setVar_other _ _ (by decide)]; exact hu4) m32.1 m32.2)
    (eval_kPlus1 k _ (by rw [lookup_setVar_other _ _ (by decide)]; exact hk4)) (by omega)
    (hB_of_spec ihc (k + 1) t4 hq2 hs4
      (X.mono _ _ _ _ hx2 (grows_sub g34) (fun g hg => by rw [gl4 g hg, gl3 g hg])) dc)
  intro t5 q3 hq3 cd5 a5 g5 r3 l5c l5o ck5 gl5 md5 ta5
  exact fin_let ra t5 lo hq3 q1 q2 q3 _ _ _ a5
    (exprAt_mono (grows_sub (grows_trans g4 g5)) r1) (exprAt_mono (grows_sub g5) r2) r3
    (by rw [l5o _ (by decide), l4o _ (by decide)]; exact l3a) (by rw [l5o _ (by decide)]; exact l4b) l5c

theorem spec_proj {σ : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (bc fc sc cc : ProgHOL 64) (fn : MlS)
    (C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (X : Inv) (S : Shape X)
    (hC : C.lookup fn = some ([(iU, .one), (iK, .one)], body S.ce (cases bc fc sc cc fn), .one)) (lo : BitVec 64)
    (h : Heap) (p q vix r : BitVec 64) (n : ConLeche.Name) (i : Nat) (e : ConLeche.Expr)
    (he : ExprAt h p (.proj n i e)) (h0 : h p = some (.word 9)) (h2 : h (p + 16) = some (.word q))
    (h3 : h (p + 24) = some (.word vix)) (h4 : h (p + 32) = some (.word r)) (hn : NameAt h q n) (hi : NatAt h vix i)
    (ihe : Spec (σ := σ) bc fc sc cc fn C X S lo h r e) :
    Spec (σ := σ) bc fc sc cc fn C X S lo h p (.proj n i e) := by
  intro t k hp hcd hai hs hx hu hk hd hck
  obtain ⟨_, h8⟩ := exprAt_data he
  apply entry S.ce S.CP (cases bc fc sc cc fn) t lo hp p 9 _ k (by omega) hai hu hk (hs _ _ h0) (hs _ _ h8)
    (fun t' a b g => S.ceval t' _ k (by omega) a b _ (by rw [g]; exact hx))
  · intro hct; rw [S.cut _ _ hct]; exact exprAt_mono hs he
  intro hct t2 cd2 m2 d2 g2 ta2 ck2 hu2 hk2
  show RRes t2 (evaluateHOLFiniteState t2 (projCase fn)) lo hp _ _
  obtain ⟨hi63, rfl⟩ := hi
  have hO2 : hOf t2 lo hp = hOf t lo hp := hOf_of_eq lo hp m2
  have hai2 : AInv t2 lo hp := ainv_of_eq hai g2 d2 ta2
  have hs2 : Sub h (hOf t2 lo hp) := by rw [hO2]; exact hs
  have hx2 : X.P t2.globals.lookup (hOf t2 lo hp) :=
    X.mono _ _ _ _ hx (by rw [hO2]; exact fun a w h => h) (fun g _ => by rw [g2])
  simp only [bdepth] at hd
  have hcost := S.cost_proj n i e
  rw [hcost] at hck ⊢
  rw [S.proj]
  have m16 := (ainv_arena hai2).1 _ _ (hs2 _ _ h2)
  have m24 := (ainv_arena hai2).1 _ _ (hs2 _ _ h3)
  let t3 := setVarHOLFinite iNm (.val (.word q)) t2
  obtain ⟨L3, f3⟩ := dec_word' t2 iNm (ldo iU 16) q _ (ldo_eval t2 iU 16 p q hu2 m16.1 m16.2)
  let t4 := setVarHOLFinite iIx (.val (.word (BitVec.ofNat 64 (2 * i + 1)))) t3
  obtain ⟨L4, f4⟩ := dec_word' t3 iIx (ldo iU 24) _ _
    (ldo_eval t3 iU 24 p _ (by simp only [t3]; rw [lookup_setVar_other _ _ (by decide)]; exact hu2) m24.1 m24.2)
  unfold projCase; rw [f3]; apply rres_locals'; rw [f4]; apply rres_locals'
  have hl4 : ∀ y, y ≠ iIx → y ≠ iNm → t4.locals.lookup y = t2.locals.lookup y := by
    intro y a b; simp only [t4, t3]; rw [lookup_setVar_other _ _ a, lookup_setVar_other _ _ b]
  have hai4 : AInv t4 lo hp := ainv_of_eq hai2 rfl rfl rfl
  have m32 := (ainv_arena hai4).1 _ _ (by show hOf t2 lo hp (p + 32) = _; exact hs2 _ _ h4)
  have rr := step_call fn iRa iU iK C _ projFin (by decide) hC (fun h q => ExprAt h q (S.F e k))
    (fun h q => ExprAt h q (.proj n i (S.F e k))) _ 0 t4 lo hp r
    (BitVec.ofNat 64 k) (ldo iU 32) (vv iK) (by show t2.code = C; rw [cd2]; exact hcd) hai4
    (ldo_eval _ iU 32 p r (by rw [lookup_setVar_other _ _ (by decide), hl4 _ (by decide) (by decide)]; exact hu2)
      m32.1 m32.2)
    (by simp [vv, evalHOLExact] <;> (rw [lookup_setVar_other _ _ (by decide), hl4 _ (by decide) (by decide)]; exact hk2))
    (by show 1 + _ ≤ t2.clock; omega)
    (hB_of_spec ihe k t4 hp hs2 hx2 (by omega))
    (fun t5 q1 hq1 cd5 a5 g5 r1 l5a l5o ck5 gl5 md5 ta5 => fin_proj ra t5 lo hq1 q q1 n i _ a5
      (nameAt_mono (fun x y hx => grows_sub g5 x y (hs2 x y hx)) hn) hi63 r1
      (by rw [l5o _ (by decide)]; simp [t4, t3]; rfl) (by rw [l5o _ (by decide)]; simp [t4])
      l5a)
  exact rres_of_eq rr rfl rfl rfl rfl rfl rfl

theorem subst_spec {σ : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (bc fc sc cc : ProgHOL 64) (fn : MlS)
    (C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (X : Inv) (S : Shape X)
    (hC : C.lookup fn = some ([(iU, .one), (iK, .one)], body S.ce (cases bc fc sc cc fn), .one))
    (lo : BitVec 64) {h : Heap}
    (hbv : ∀ (p vw : BitVec 64) (i : Nat), ExprAt h p (.bvar i) → h p = some (.word 0) →
      h (p + 16) = some (.word vw) → NatAt h vw i → Spec (σ := σ) bc fc sc cc fn C X S lo h p (.bvar i))
    (hfv : ∀ (p vw q : BitVec 64) (i : Nat) (ty : ConLeche.Expr), ExprAt h p (.fvar i ty) →
      h p = some (.word 1) → h (p + 16) = some (.word vw) → h (p + 24) = some (.word q) → NatAt h vw i →
      ExprAt h q ty → Spec (σ := σ) bc fc sc cc fn C X S lo h q ty → Spec (σ := σ) bc fc sc cc fn C X S lo h p (.fvar i ty))
    (hsort : ∀ (p q : BitVec 64) (u : ConLeche.Level), ExprAt h p (.sort u) → h p = some (.word 2) →
      h (p + 16) = some (.word q) → LevelAt h q u → Spec (σ := σ) bc fc sc cc fn C X S lo h p (.sort u))
    (hconst : ∀ (p q r : BitVec 64) (n : ConLeche.Name) (us : List ConLeche.Level),
      ExprAt h p (.const n us) → h p = some (.word 3) → h (p + 16) = some (.word q) → h (p + 24) = some (.word r) →
      NameAt h q n → LevelsAt h r us → Spec (σ := σ) bc fc sc cc fn C X S lo h p (.const n us))
    {p : BitVec 64} {e : ConLeche.Expr} (he : ExprAt h p e) : Spec (σ := σ) bc fc sc cc fn C X S lo h p e := by
  induction he with
  | @app p q r f a hp0 h0 hd h2 h3 hf ha ihf iha =>
    exact spec_bin bc fc sc cc fn C X S hC lo _ p q r (.app f a) f a 4 _ (vv iK) 0 rfl
      (fun k t' hk => by simpa [vv, evalHOLExact] using hk) (S.cost_app f a)
      (fun k hk => by simp [bdepth] at hk; omega)
      (fun k t' h' q1 q2 hm e1 e2 l1 l2 => by
        rw [S.app]; exact app_data ra _ _ t' h' q1 q2 hm e1 e2 l1 l2)
      (fun k h' p0 q1 q2 hp c0 c8 c16 c24 e1 e2 => by
        rw [S.app] at c8 ⊢; exact .app hp c0 c8 c16 c24 e1 e2)
      (.app hp0 h0 hd h2 h3 hf ha) h0 h2 h3 ihf iha
  | @lam p q r f a hp0 h0 hd h2 h3 hf ha ihf iha =>
    exact spec_bin bc fc sc cc fn C X S hC lo _ p q r (.lam f a) f a 5 _ kPlus1 1 rfl
      (fun k t' hk => eval_kPlus1 k t' hk) (S.cost_lam f a)
      (fun k hk => by simp [bdepth] at hk; omega)
      (fun k t' h' q1 q2 hm e1 e2 l1 l2 => by
        rw [S.lam]; exact lam_data ra _ _ t' h' q1 q2 hm e1 e2 l1 l2)
      (fun k h' p0 q1 q2 hp c0 c8 c16 c24 e1 e2 => by
        rw [S.lam] at c8 ⊢; exact .lam hp c0 c8 c16 c24 e1 e2)
      (.lam hp0 h0 hd h2 h3 hf ha) h0 h2 h3 ihf iha
  | @forallE p q r f a hp0 h0 hd h2 h3 hf ha ihf iha =>
    exact spec_bin bc fc sc cc fn C X S hC lo _ p q r (.forallE f a) f a 6 _ kPlus1 1 rfl
      (fun k t' hk => eval_kPlus1 k t' hk) (S.cost_forallE f a)
      (fun k hk => by simp [bdepth] at hk; omega)
      (fun k t' h' q1 q2 hm e1 e2 l1 l2 => by
        rw [S.forallE]; exact forallE_data ra _ _ t' h' q1 q2 hm e1 e2 l1 l2)
      (fun k h' p0 q1 q2 hp c0 c8 c16 c24 e1 e2 => by
        rw [S.forallE] at c8 ⊢; exact .forallE hp c0 c8 c16 c24 e1 e2)
      (.forallE hp0 h0 hd h2 h3 hf ha) h0 h2 h3 ihf iha
  | fvar hp h0 hd h2 h3 hi hty ih => exact hfv _ _ _ _ _ (.fvar hp h0 hd h2 h3 hi hty) h0 h2 h3 hi hty ih
  | sort hp h0 hd h2 hu => exact hsort _ _ _ (.sort hp h0 hd h2 hu) h0 h2 hu
  | const hp h0 hd h2 h3 hn hus => exact hconst _ _ _ _ _ (.const hp h0 hd h2 h3 hn hus) h0 h2 h3 hn hus
  | lit hp h0 hd h2 hl => exact spec_leaf bc fc sc cc fn C X S lo _ _ _ _ (.lit hp h0 hd h2 hl) h0 (fun k => S.leaf _ k)
  | bvar hp h0 hd h2 hi => exact hbv _ _ _ (.bvar hp h0 hd h2 hi) h0 h2 hi
  | letE hp h0 hd h2 h3 h4 ha hb hc iha ihb ihc =>
    exact spec_letE ra bc fc sc cc fn C X S hC lo _ _ _ _ _ _ _ _ (.letE hp h0 hd h2 h3 h4 ha hb hc) h0 h2 h3 h4 iha ihb ihc
  | proj hp h0 hd h2 h3 h4 hn hi he ih =>
    exact spec_proj ra bc fc sc cc fn C X S hC lo _ _ _ _ _ _ _ _ (.proj hp h0 hd h2 h3 h4 hn hi he) h0 h2 h3 h4 hn hi ih

end ConPanqueque.Subst
