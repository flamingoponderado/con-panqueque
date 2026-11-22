import ConPanqueque.Rebuild
import ConPanqueque.BinCons
import ConPanqueque.ExprData
import ConPanqueque.Fold
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic ConPanqueque.Alloc ConPanqueque.ExprCons
open ConPanqueque.Node ConPanqueque.StateHeap ConPanqueque.Rebuild

/-!
# `Expr.instantiate1` in Pancake

`inst1 u k` (global `ivv` = the value `v`): con-leche's `instantiate1P` — the
cutoff on the stored loose-bvar bound, then the descent, rebuilding the nodes on
the way up with `mkNode`. `bin_case` is the generic two-child rebuild (`app`,
`lam`, `forallE`).
-/

namespace ConPanqueque.Inst1

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

theorem bin_case {σ : Type} (fn : MlS) (C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
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
      s'.locals.lookup iU = some (.val (.word cp1)) → s'.locals.lookup iK = some (.val (.word kw)) →
      c1 ≤ s'.clock → RRes s' (evaluateHOLFiniteState s' B) lo hq (fun h q => ExprAt h q v1) c1)
    (hB2 : ∀ s' : PanSemStateFiniteExact 64 σ, ∀ hq, s'.code = C → AInv s' lo hq → Sub (hOf t lo hp) (hOf s' lo hq) →
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
      (fun s' hcs ha hm hu' hk' hc' => hB1 s' hp hcs ha
        (by rw [hOf_of_eq (s := t1) lo hp hm, hOf1]; exact fun a w h => h) hu' hk' hc') with
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
      (fun s' hcs ha hm hu' hk' hc' => hB2 s' hp2 hcs ha
        (by rw [hOf_of_eq (s := t3) lo hp2 hm, hOf3]; exact grows_sub g2') hu' hk' hc') with
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

end ConPanqueque.Inst1
