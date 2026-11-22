import ConPanqueque.LevelSubst
import ConPanqueque.LevelsFns
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic ConPanqueque.Alloc ConPanqueque.ExprCons
open ConPanqueque.Node ConPanqueque.StateHeap ConPanqueque.Rebuild ConPanqueque.Subst

/-!
# `Expr.instantiateLevelParams` in Pancake

An instance of the substitution template with the cutoff on the has-level-param
bit (as con-leche's `instLevelParamsP`): `sort` and `const` levels are rewritten
with `lsub`/`lmap`, `fvar` types are descended into. The node builders
`fin_fvar`, `fin_sort`, `fin_const` compute the new data words.
-/

namespace ConPanqueque.ILP

def iIv := ofString "iv"
def iDty := ofString "dty"
def iLh := ofString "lh"
def iLp := ofString "lp"

def finFvar : ProgHOL 64 :=
  .dec iIw .one (.shift .lsr (vv iIv) (.const 1)) (.dec iDty .one (ldo iRa 8)
    (mkNode 1 ConPanqueque.ExprData.fvarDataE [iIv, iRa]))

theorem fin_fvar {σ : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ)
    (lo hq q1 : BitVec 64) (i : Nat) (hi63 : i < 2 ^ 63) (ty : ConLeche.Expr) (hi : AInv t lo hq)
    (e1 : ExprAt (hOf t lo hq) q1 ty)
    (liv : t.locals.lookup iIv = some (.val (.word (BitVec.ofNat 64 (2 * i + 1)))))
    (lra : t.locals.lookup iRa = some (.val (.word q1))) :
    RRes t (evaluateHOLFiniteState t finFvar) lo hq (fun h q => ExprAt h q (.fvar i ty)) 0 := by
  let iw := (UInt64.ofNat i).toBitVec
  have hsh : BitVec.ofNat 64 (2 * i + 1) >>> (1 : Nat) = iw := by
    apply BitVec.eq_of_toNat_eq; simp [iw, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]; omega
  let t1 := setVarHOLFinite iIw (.val (.word iw)) t
  obtain ⟨L1, f1⟩ := dec_word' t iIw (.shift .lsr (vv iIv) (.const 1)) iw _
    (by simp [vv, evalHOLExact, liv, wordShiftHOL]; exact hsh)
  have hm1 : InMem t1 (hOf t lo hq) := inMem_of_eq rfl rfl (ainv_arena hi).1
  have lra1 : t1.locals.lookup iRa = some (.val (.word q1)) := by
    simp only [t1]; rw [lookup_setVar_other _ _ (by decide)]; exact lra
  let t2 := setVarHOLFinite iDty (.val (.word ty.data.toBitVec)) t1
  obtain ⟨L2, f2⟩ := dec_word' t1 iDty (ldo iRa 8) _ _ (data_load hm1 e1 lra1)
  unfold finFvar; rw [f1]; apply rres_locals'; rw [f2]; apply rres_locals'
  have hd := ConPanqueque.ExprData.fvarDataE.eval t2 (UInt64.ofNat i) ty.data
    (by show t2.locals.lookup iIw = _; simp only [t2]; rw [lookup_setVar_other _ _ (by decide)]; simp [t1, iw])
    (by show t2.locals.lookup iDty = _; simp [t2])
  simp only [← ConPanqueque.ExprData.fvar_data ra i hi63] at hd
  rcases mkNode_ainv t2 lo hq 1 _ _ [iIv, iRa] [_, q1] rfl (by decide) (by decide) (by decide) (by simp) hd
      (fun j hj => match j, hj with
        | 0, _ => by
          show t2.locals.lookup iIv = _
          simp only [t2, t1]; rw [lookup_setVar_other _ _ (by decide), lookup_setVar_other _ _ (by decide)]; exact liv
        | 1, _ => by show t2.locals.lookup iRa = _; simp only [t2]; rw [lookup_setVar_other _ _ (by decide)]; exact lra1)
      (ainv_of_eq hi rfl rfl rfl) with
    hs | ⟨hr, a5, g5, hpos, cells, cd5, ck5, gl5, md5, ta5⟩
  · exact Or.inl hs
  right
  have c0 := cells 0 (by decide)
  have c1 := cells 1 (by decide)
  have c2 := cells 2 (by decide)
  have c3 := cells 3 (by decide)
  simp only [at8, List.length_cons, List.length_nil] at c0 c1 c2 c3
  rw [show hq + BitVec.ofNat 64 (8 * 0) = hq by simp] at c0
  rw [show BitVec.ofNat 64 (8 * 1) = 8#64 from by decide] at c1
  rw [show BitVec.ofNat 64 (8 * 2) = 16#64 from by decide] at c2
  rw [show BitVec.ofNat 64 (8 * 3) = 24#64 from by decide] at c3
  have sub := grows_sub (show Grows t _ lo hq _ from ⟨g5.le, g5.mem⟩)
  exact ⟨hq, hr, _, a5, ⟨g5.le, g5.mem⟩, .fvar hpos c0 c1 c2 c3 ⟨hi63, rfl⟩ (exprAt_mono sub e1),
    cd5, by rw [ck5]; show t.clock ≤ t.clock + 0; omega, gl5, md5, ta5⟩

theorem bit_toBitVec (b : Bool) : ConPanqueque.LevelFns.bit b = (if b then (1 : UInt64) else 0).toBitVec := by
  cases b <;> rfl

def finSort : ProgHOL 64 :=
  .dec iLh .one (ldo iRa 8) (mkNode 2 ConPanqueque.ExprData.sortDataE [iRa])

theorem fin_sort {σ : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ)
    (lo hq q1 : BitVec 64) (u : ConLeche.Level) (hi : AInv t lo hq) (e1 : LevelAt (hOf t lo hq) q1 u)
    (lra : t.locals.lookup iRa = some (.val (.word q1)))
    (llp : t.locals.lookup iLp = some (.val (.word (ConPanqueque.LevelFns.bit (ConLeche.levelHasParam u))))) :
    RRes t (evaluateHOLFiniteState t finSort) lo hq (fun h q => ExprAt h q (.sort u)) 0 := by
  let t1 := setVarHOLFinite iLh (.val (.word u.hashData.toBitVec)) t
  obtain ⟨L1, f1⟩ := dec_word' t iLh (ldo iRa 8) _ _
    (ConPanqueque.LevelSubst.hash_load (ainv_arena hi).1 e1 lra)
  unfold finSort; rw [f1]; apply rres_locals'
  have hd := ConPanqueque.ExprData.sortDataE.eval t1 u.hashData (if ConLeche.levelHasParam u then 1 else 0)
    (by show t1.locals.lookup iLh = _; simp [t1])
    (by show t1.locals.lookup iLp = _; simp only [t1]; rw [lookup_setVar_other _ _ (by decide), llp, bit_toBitVec])
  simp only [← ConPanqueque.ExprData.sort_data ra] at hd
  rcases mkNode_ainv t1 lo hq 2 _ _ [iRa] [q1] rfl (by decide) (by decide) (by decide) (by simp) hd
      (fun j hj => match j, hj with
        | 0, _ => by show t1.locals.lookup iRa = _; simp only [t1]; rw [lookup_setVar_other _ _ (by decide)]; exact lra)
      (ainv_of_eq hi rfl rfl rfl) with
    hs | ⟨hr, a5, g5, hpos, cells, cd5, ck5, gl5, md5, ta5⟩
  · exact Or.inl hs
  right
  have c0 := cells 0 (by decide)
  have c1 := cells 1 (by decide)
  have c2 := cells 2 (by decide)
  simp only [at8, List.length_cons, List.length_nil] at c0 c1 c2
  rw [show hq + BitVec.ofNat 64 (8 * 0) = hq by simp] at c0
  rw [show BitVec.ofNat 64 (8 * 1) = 8#64 from by decide] at c1
  rw [show BitVec.ofNat 64 (8 * 2) = 16#64 from by decide] at c2
  have sub := grows_sub (show Grows t _ lo hq _ from ⟨g5.le, g5.mem⟩)
  exact ⟨hq, hr, _, a5, ⟨g5.le, g5.mem⟩, .sort hpos c0 c1 c2 (levelAt_mono sub e1),
    cd5, by rw [ck5]; show t.clock ≤ t.clock + 0; omega, gl5, md5, ta5⟩

def finConst : ProgHOL 64 :=
  .dec iHs .one (.const 1723) (.seq (.ite (.cmp .notEqual (vv iNm) (.const 0)) (.assign .local iHs (ldo iNm 8)) .skip)
    (mkNode 3 ConPanqueque.ExprData.constDataE [iNm, iRa]))

theorem fin_const {σ : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ)
    (lo hq q q1 : BitVec 64) (n : ConLeche.Name) (us : List ConLeche.Level) (hi : AInv t lo hq)
    (hn : NameAt (hOf t lo hq) q n) (e1 : LevelsAt (hOf t lo hq) q1 us)
    (lnm : t.locals.lookup iNm = some (.val (.word q))) (lra : t.locals.lookup iRa = some (.val (.word q1)))
    (llh : t.locals.lookup iLh = some (.val (.word (ConLeche.levelsHash us).toBitVec)))
    (llp : t.locals.lookup iLp = some (.val (.word (ConPanqueque.LevelFns.bit (ConLeche.levelsHaveParam us))))) :
    RRes t (evaluateHOLFiniteState t finConst) lo hq (fun h q => ExprAt h q (.const n us)) 0 := by
  obtain ⟨t', L, f1, lhs, lo', mm, cd, ck, gl, md, ta⟩ := hash_then t (hOf t lo hq) q n (ainv_arena hi).1 hn lnm
    (mkNode 3 ConPanqueque.ExprData.constDataE [iNm, iRa])
  unfold finConst; rw [f1]; apply rres_locals'
  have hi' : AInv t' lo hq := ⟨by rw [gl]; exact hi.hpv, hi.le, hi.pos, fun a h1 h2 => by rw [md]; exact hi.mem a h1 h2,
    ⟨by rw [ta]; exact hi.free.1, fun a h1 h2 => by rw [md]; exact hi.free.2 a h1 (by rw [← ta]; exact h2)⟩⟩
  have hd := ConPanqueque.ExprData.constDataE.eval t' n.hashData (ConLeche.levelsHash us)
    (if ConLeche.levelsHaveParam us then 1 else 0) lhs
    (by rw [lo' _ (by decide)]; exact llh) (by rw [lo' _ (by decide)]; show t.locals.lookup iLp = _; rw [llp, bit_toBitVec])
  simp only [← ConPanqueque.ExprData.const_data ra] at hd
  rcases mkNode_ainv t' lo hq 3 _ _ [iNm, iRa] [q, q1] rfl (by decide) (by decide) (by decide) (by simp) hd
      (fun j hj => match j, hj with
        | 0, _ => by show t'.locals.lookup iNm = _; rw [lo' _ (by decide)]; exact lnm
        | 1, _ => by show t'.locals.lookup iRa = _; rw [lo' _ (by decide)]; exact lra) hi' with
    hs | ⟨hr, a5, g5, hpos, cells, cd5, ck5, gl5, md5, ta5⟩
  · exact Or.inl hs
  right
  have g5' : Grows t _ lo hq _ := ⟨g5.le, fun a h1 h2 => by rw [g5.mem a h1 h2, mm]⟩
  have sub := grows_sub g5'
  have c0 := cells 0 (by decide)
  have c1 := cells 1 (by decide)
  have c2 := cells 2 (by decide)
  have c3 := cells 3 (by decide)
  simp only [at8, List.length_cons, List.length_nil] at c0 c1 c2 c3
  rw [show hq + BitVec.ofNat 64 (8 * 0) = hq by simp] at c0
  rw [show BitVec.ofNat 64 (8 * 1) = 8#64 from by decide] at c1
  rw [show BitVec.ofNat 64 (8 * 2) = 16#64 from by decide] at c2
  rw [show BitVec.ofNat 64 (8 * 3) = 24#64 from by decide] at c3
  exact ⟨hq, hr, _, a5, g5', .const hpos c0 c1 c2 c3 (nameAt_mono sub hn) (levelsAt_mono sub e1),
    by rw [cd5, cd], by rw [ck5, ck]; omega, fun g hg => by rw [gl5 g hg, gl], by rw [md5, md], by rw [ta5, ta]⟩

/-! ## The instance -/

open ConPanqueque.LevelSubst in
/-- Clock: the descent's calls, plus `lsub`/`levelHasParam` at `sort` and the list functions at `const`. -/
noncomputable def ilpCost (ks : List ConLeche.Name) (vs : List ConLeche.Level) : ConLeche.Expr → Nat
  | .bvar _ | .lit _ => 0
  | .fvar _ ty => 1 + ilpCost ks vs ty + 0
  | .sort u => 1 + lcost (ks.zip vs).length u + (1 + ConPanqueque.LevelFns.cost (ConLeche.Level.subst ks vs u) + 0)
  | .const _ us => 1 + lmcost (ks.zip vs).length us +
      (1 + (us.map (ConLeche.Level.subst ks vs)).length +
        (1 + ConPanqueque.LevelsFns.lsCost (us.map (ConLeche.Level.subst ks vs)) + 0))
  | .app f a | .lam f a | .forallE f a => 2 + ilpCost ks vs f + ilpCost ks vs a
  | .letE t v b => 1 + ilpCost ks vs t + (1 + ilpCost ks vs v + (1 + ilpCost ks vs b + 0))
  | .proj _ _ e => 1 + ilpCost ks vs e + 0

/-- `[hasLP = false]`: bit 0 of the data word is clear. -/
def lpE : ExpHOL 64 := .cmp .equal (ConPanqueque.AppData.shr (ConPanqueque.AppData.shl (vv iDw) 63) 63) (.const 0)

theorem eval_lpE {σ : Type} (t : PanSemStateFiniteExact 64 σ) (e : ConLeche.Expr)
    (hdw : t.locals.lookup iDw = some (.val (.word e.data.toBitVec))) :
    ∃ w, @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) lpE =
      some (.val (.word w)) ∧ (w ≠ 0 ↔ e.hasLP = false) := by
  have hx : (e.data.toBitVec <<< (63 : Nat) >>> (63 : Nat)).toNat = e.data.toNat % 2 := by
    simp [BitVec.toNat_ushiftRight, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]; omega
  have hlp : e.hasLP = (e.data.toNat % 2 == 1) := by
    simp only [ConLeche.Expr.hasLP, ConLeche.lpOfData]
    have hm : (e.data % 2).toNat = e.data.toNat % 2 := UInt64.toNat_mod _ _
    by_cases h1 : e.data.toNat % 2 = 1
    · have : e.data % 2 = 1 := UInt64.toNat_inj.mp (by rw [hm, h1]; rfl)
      simp [this, h1]
    · have : e.data % 2 ≠ 1 := fun e' => h1 (by rw [← hm, e']; rfl)
      rw [beq_eq_false_iff_ne.mpr this, beq_eq_false_iff_ne.mpr h1]
  refine ⟨if e.data.toBitVec <<< (63 : Nat) >>> (63 : Nat) = 0#64 then 1#64 else 0#64, by simp [lpE, ConPanqueque.AppData.shr, ConPanqueque.AppData.shl, vv, evalHOLExact, hdw, wordShiftHOL,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL], ?_⟩
  generalize e.data.toBitVec <<< (63 : Nat) >>> (63 : Nat) = x at *
  rw [hlp]
  have : x = 0#64 ↔ e.data.toNat % 2 = 0 := by
    constructor <;> intro h
    · rw [h] at hx; simp at hx; omega
    · apply BitVec.eq_of_toNat_eq; simp; omega
  by_cases h0 : e.data.toNat % 2 = 0
  · simp [this.mpr h0, h0]
  · have h1 : e.data.toNat % 2 = 1 := by omega
    simp [show ¬ x = 0#64 from fun e => h0 (this.mp e), h1]

def gKV := ConPanqueque.LevelSubst.gKV

/-- The substitution list is held in the global `kv`. -/
def inv (c : BitVec 64) : Subst.Inv where
  P gl _ := gl gKV = some (.val (.word c))
  mono gl gl' h h' := fun x _ hg => by rw [hg gKV (by decide)]; exact x

noncomputable def shape (ks : List ConLeche.Name) (vs : List ConLeche.Level) (c : BitVec 64) : Subst.Shape (inv c) where
  F e _ := e.instantiateLevelParams ks vs
  CP e _ := e.hasLP = false
  ce := lpE
  ceval t e _ _ hdw _ _ _ := eval_lpE t e hdw
  leaf l k := by simp
  cut e k h := ConLeche.Expr.hasLP_false h
  app _ _ _ := rfl
  lam _ _ _ := rfl
  forallE _ _ _ := rfl
  letE _ _ _ _ := rfl
  proj _ _ _ _ := rfl
  cost := ilpCost ks vs
  cost_app _ _ := by simp [ilpCost]
  cost_lam _ _ := by simp [ilpCost]
  cost_forallE _ _ := by simp [ilpCost]
  cost_letE _ _ _ := by simp [ilpCost]
  cost_proj _ _ _ := by simp [ilpCost]

def fvarC (fn : MlS) : ProgHOL 64 :=
  .dec iIv .one (ldo iU 16) (.dec iRa .one (.const 0)
    (.seq (.call (some (some (.local, iRa), none)) fn [ldo iU 24, vv iK]) finFvar))

def sortC (ls : MlS) : ProgHOL 64 :=
  .dec iRa .one (.const 0) (.seq (.call (some (some (.local, iRa), none)) ls [ldo iU 16, vv iK])
    (.dec iLp .one (.const 0) (.seq (.call (some (some (.local, iLp), none)) ConPanqueque.LevelFns.nLhp [vv iRa])
      finSort)))

def constC (lm lhf lpf : MlS) : ProgHOL 64 :=
  .dec iNm .one (ldo iU 16) (.dec iRa .one (.const 0) (.seq (.call (some (some (.local, iRa), none)) lm [ldo iU 24, vv iK])
    (.dec iLh .one (.const 0) (.seq (.call (some (some (.local, iLh), none)) lhf [vv iRa])
      (.dec iLp .one (.const 0) (.seq (.call (some (some (.local, iLp), none)) lpf [vv iRa]) finConst))))))

end ConPanqueque.ILP
