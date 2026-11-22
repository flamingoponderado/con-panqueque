import ConPanqueque.Subst
import ConPanqueque.LevelCons
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic ConPanqueque.Alloc ConPanqueque.ExprCons
open ConPanqueque.Node ConPanqueque.StateHeap ConPanqueque.Rebuild ConPanqueque.Subst

/-!
# Level-parameter substitution in Pancake

con-leche's `Level.subst ks vs`. The substitution is a list of cells
`[name, level, next]` (`KVAt`, the zip of `ks` and `vs`); names are compared by
pointer, which is exact when the names involved are interned (`Interned`).
`lkp` finds a parameter's replacement (`lkp_spec`).
-/

namespace ConPanqueque.LevelSubst

/-- `subst.go` on the zipped list. -/
def goZ : List (ConLeche.Name × ConLeche.Level) → ConLeche.Name → Option ConLeche.Level
  | [], _ => none
  | (k, v) :: rest, n => if k = n then some v else goZ rest n

theorem subst_go_eq : ∀ (ks : List ConLeche.Name) (vs : List ConLeche.Level) (n : ConLeche.Name),
    ConLeche.Level.subst.go ks vs n = (goZ (ks.zip vs) n).getD (.param n)
  | [], _, n => by simp [ConLeche.Level.subst.go, goZ]
  | _ :: _, [], n => by simp [ConLeche.Level.subst.go, goZ]
  | k :: ks, v :: vs, n => by
    simp only [ConLeche.Level.subst.go, List.zip_cons_cons, goZ]
    split <;> simp_all [subst_go_eq ks vs n]

/-- A substitution list in the arena. -/
inductive KVAt (h : Heap) : BitVec 64 → List (ConLeche.Name × ConLeche.Level) → Prop
  | nil : KVAt h 0 []
  | cons {c pk pv nx : BitVec 64} {k : ConLeche.Name} {v : ConLeche.Level} {rest}
      (hc : c ≠ 0) (h0 : h c = some (.word pk)) (h8 : h (c + 8) = some (.word pv))
      (h16 : h (c + 16) = some (.word nx)) (hk : NameAt h pk k) (hv : LevelAt h pv v) (hr : KVAt h nx rest) :
      KVAt h c ((k, v) :: rest)

theorem kvAt_mono {h h' : Heap} (hs : Sub h h') {c : BitVec 64} {l} (hk : KVAt h c l) : KVAt h' c l := by
  induction hk with
  | nil => exact .nil
  | cons hc h0 h8 h16 hk hv _ ih =>
    exact .cons hc (hs _ _ h0) (hs _ _ h8) (hs _ _ h16) (nameAt_mono hs hk) (levelAt_mono hs hv) ih

def iC := ofString "c"
def iN := ofString "n"
def iR := ofString "r"

/-- `lkp(c, n)`: the replacement of the parameter named by the pointer `n`, or `0`. -/
def lkpBody (fn : MlS) : ProgHOL 64 :=
  .ite (.cmp .equal (vv iC) (.const 0)) (.return (.const 0))
   (.ite (.cmp .equal (ldo iC 0) (vv iN)) (.return (ldo iC 8))
     (.dec iR .one (.const 0) (.seq (.call (some (some (.local, iR), none)) fn [ldo iC 16, vv iN]) (.return (vv iR)))))

/-- What `lkp` returns for `n`: the replacement's node, or `0`. -/
def LkRes (h : Heap) (kvs : List (ConLeche.Name × ConLeche.Level)) (n : ConLeche.Name) (w : BitVec 64) : Prop :=
  (goZ kvs n = none ∧ w = 0) ∨ (∃ v, goZ kvs n = some v ∧ LevelAt h w v)

theorem lkp_spec {σ : Type} (fn : MlS) (h : Heap) (pn : BitVec 64) (n : ConLeche.Name)
    (hint : ∀ pk k, NameAt h pk k → (pk = pn ↔ k = n)) {c : BitVec 64} {kvs} (hk : KVAt h c kvs) :
    ∀ t : PanSemStateFiniteExact 64 σ, t.code.lookup fn = some ([(iC, .one), (iN, .one)], lkpBody fn, .one) →
      InMem t h → t.locals.lookup iC = some (.val (.word c)) → t.locals.lookup iN = some (.val (.word pn)) →
      kvs.length ≤ t.clock →
      ∃ w st, evaluateHOLFiniteState t (lkpBody fn) = (some (.returned (.val (.word w))), st) ∧ LkRes h kvs n w ∧
        ConPanqueque.Fold.Post t st kvs.length ∧ st.globals = t.globals ∧ st.topAddr = t.topAddr := by
  induction hk with
  | nil =>
    intro t hc hm hlc hln hck
    refine ⟨0, emptyLocalsHOLFinite t, ?_, Or.inl ⟨rfl, rfl⟩, ?_, rfl, rfl⟩
    · unfold lkpBody
      rw [ite_word t _ _ _ 1 (by simp [vv, evalHOLExact, hlc, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
      simp only [ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true, ↓reduceIte]
      rw [evaluateHOLFiniteState_eq_evaluate_def]; simp [evalHOLExact, shapeOfHOLExact]
    · simp [ConPanqueque.Fold.Post, emptyLocalsHOLFinite]
  | @cons c pk pv nx k v rest hc0 h0 h8 h16 hkn hv hr ih =>
    intro t hc hm hlc hln hck
    have m0 := hm _ _ (show h (c + 0) = _ by simpa using h0)
    have m8 := hm _ _ h8
    have m16 := hm _ _ h16
    unfold lkpBody
    rw [ite_word t _ _ _ 0 (by simp [vv, evalHOLExact, hlc, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hc0)]
    simp only [ne_eq, not_true_eq_false, ↓reduceIte]
    have hl0 := ldo_eval t iC 0 c pk hlc m0.1 m0.2
    by_cases hkn' : k = n
    · have hpk : pk = pn := (hint pk k hkn).mpr hkn'
      rw [ite_word t _ _ _ 1 (by simp only [vv, evalHOLExact, hln]; rw [hl0]; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hpk])]
      simp only [ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true, ↓reduceIte]
      refine ⟨pv, emptyLocalsHOLFinite t, ?_, Or.inr ⟨v, by simp [goZ, hkn'], hv⟩, ?_, rfl, rfl⟩
      · rw [evaluateHOLFiniteState_eq_evaluate_def]
        simp only; rw [ldo_eval t iC 8 c pv hlc m8.1 m8.2]; simp [shapeOfHOLExact]
      · simp [ConPanqueque.Fold.Post, emptyLocalsHOLFinite]
    · have hpk : pk ≠ pn := fun e => hkn' ((hint pk k hkn).mp e)
      rw [ite_word t _ _ _ 0 (by simp only [vv, evalHOLExact, hln]; rw [hl0]; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hpk])]
      simp only [ne_eq, not_true_eq_false, ↓reduceIte]
      let t1 := setVarHOLFinite iR (.val (.word 0)) t
      obtain ⟨L1, e1⟩ := dec_word' t iR (.const 0) 0
        (.seq (.call (some (some (.local, iR), none)) fn [ldo iC 16, vv iN]) (.return (vv iR))) (by simp [evalHOLExact])
      have hlc1 : t1.locals.lookup iC = some (.val (.word c)) := by
        simp only [t1]; rw [lookup_setVar_other _ _ (by decide)]; exact hlc
      have hln1 : t1.locals.lookup iN = some (.val (.word pn)) := by
        simp only [t1]; rw [lookup_setVar_other _ _ (by decide)]; exact hln
      obtain ⟨callee, hlk, hx1, hx2⟩ := lookupCode2 t1 fn iC iN (lkpBody fn) nx pn (by decide) (by exact hc)
      have hargs : evalListHOLFinite t1 (h := fun a => Classical.propDecidable (t1.memaddrs a)) [ldo iC 16, vv iN] =
          some [.val (.word nx), .val (.word pn)] := by
        simp only [evalListHOLFinite, evalListHOLExact]
        rw [ldo_eval t1 iC 16 c nx hlc1 m16.1 m16.2]; simp [vv, evalHOLExact, hln1]
      let s' := callEntryStateHOLFinite t1 callee
      have hck' : rest.length ≤ t.clock - 1 := by simp at hck; omega
      obtain ⟨w, st, hb, hres, hpost, hgl, hta⟩ := ih s' (by simp only [s', callEntryStateHOLFinite]; exact hc) hm hx1 hx2
        (by simp [s', callEntryStateHOLFinite, t1]; exact hck')
      have hcall := call_assign t1 .local iR fn none [ldo iC 16, vv iN] _ (lkpBody fn) callee .one (.val (.word w)) st
        hargs hlk (by show t.clock ≠ 0; simp at hck; omega) hb (by simp [shapeOfHOLExact, shapeEqHOL])
        (by simp [isValidValueHOLExact, lookupKvarHOLExact, t1, shapeOfHOLExact, shapeEqHOL])
      let t2 := setKvarHOLFinite .local iR (.val (.word w)) { st with locals := t1.locals }
      have eret : evaluateHOLFiniteState t2 (.return (vv iR)) = (some (.returned (.val (.word w))), emptyLocalsHOLFinite t2) :=
        eval_return_local t2 iR w (by simp [t2, setKvarHOLFinite])
      rw [e1]; simp only; rw [seq_normal _ hcall, eret]
      refine ⟨w, _, rfl, ?_, ?_, ?_, ?_⟩
      · rcases hres with ⟨hz, hw⟩ | ⟨v', hg, hl⟩
        · exact Or.inl ⟨by simp [goZ, hkn', hz], hw⟩
        · exact Or.inr ⟨v', by simp [goZ, hkn', hg], hl⟩
      · obtain ⟨cd, mm, md, ck⟩ := hpost
        refine ⟨?_, ?_, ?_, ?_⟩ <;>
          simp [t2, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, cd, mm, md, s', callEntryStateHOLFinite, t1] at ck ⊢
        omega
      · simp [t2, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, hgl, s', callEntryStateHOLFinite, t1]
      · simp [t2, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, hta, s', callEntryStateHOLFinite, t1]

/-! ## The level rebuild -/

def gKV := ofString "kv"

def succC (fn : MlS) : ProgHOL 64 :=
  .dec iRa .one (.const 0) (.seq (.call (some (some (.local, iRa), none)) fn [ldo iU 16, vv iK])
    (mkNode 1 (ConPanqueque.Hash.mixExp (.const 3) (ldo iRa 8)) [iRa]))

def binL (fn : MlS) (tag c : BitVec 64) : ProgHOL 64 :=
  .dec iRa .one (.const 0) (.seq (.call (some (some (.local, iRa), none)) fn [ldo iU 16, vv iK])
  (.dec iRb .one (.const 0) (.seq (.call (some (some (.local, iRb), none)) fn [ldo iU 24, vv iK])
    (mkNode tag (ConPanqueque.Hash.mixExp (.const c) (ConPanqueque.Hash.mixExp (ldo iRa 8) (ldo iRb 8))) [iRa, iRb]))))

def paramC (lk : MlS) : ProgHOL 64 :=
  .dec iR .one (.const 0) (.seq (.call (some (some (.local, iR), none)) lk [.var .global gKV, ldo iU 16])
    (.ite (.cmp .equal (vv iR) (.const 0)) (.return (vv iU)) (.return (vv iR))))

def lcases (fn lk : MlS) : List (BitVec 64 × ProgHOL 64) :=
  [(1, succC fn), (2, binL fn 2 5), (3, binL fn 3 7), (4, paramC lk)]

def lsubBody (fn lk : MlS) : ProgHOL 64 :=
  .dec ConPanqueque.Fold.nTg .one (.load .one (vv iU))
    (ConPanqueque.Fold.iteChain (lcases fn lk) (.return (vv iU)))

/-- Calls made (each `lkp` step included). -/
def lcost (L : Nat) : ConLeche.Level → Nat
  | .zero => 0
  | .succ u => 1 + lcost L u
  | .max u v | .imax u v => 1 + lcost L u + (1 + lcost L v)
  | .param _ => 1 + L

/-- Names are interned in `h`: one node per name. -/
def Interned (h : Heap) : Prop := ∀ p q n, NameAt h p n → NameAt h q n → p = q

/-- What a call of `lsub` on the level at `p` does. -/
def LSpec {σ : Type} (fn lk : MlS) (C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
    (ks : List ConLeche.Name) (vs : List ConLeche.Level) (c lo : BitVec 64) (h : Heap) (p : BitVec 64)
    (u : ConLeche.Level) : Prop :=
  ∀ (t : PanSemStateFiniteExact 64 σ) (hp : BitVec 64), t.code = C → AInv t lo hp → Sub h (hOf t lo hp) →
    t.globals.lookup gKV = some (.val (.word c)) → t.locals.lookup iU = some (.val (.word p)) →
    (∃ w, t.locals.lookup iK = some (.val (.word w))) → lcost (ks.zip vs).length u ≤ t.clock →
    RRes t (evaluateHOLFiniteState t (lsubBody fn lk)) lo hp
      (fun h q => LevelAt h q (ConLeche.Level.subst ks vs u)) (lcost (ks.zip vs).length u)

theorem levelAt_hash {h : Heap} {p : BitVec 64} {u : ConLeche.Level} (hu : LevelAt h p u) :
    p ≠ 0 ∧ h (p + 8) = some (.word u.hashData.toBitVec) := by
  cases hu <;> exact ⟨by assumption, by assumption⟩

theorem hash_load {σ : Type} {t : PanSemStateFiniteExact 64 σ} {h : Heap} {x : MlS} {q : BitVec 64}
    {u : ConLeche.Level} (hm : InMem t h) (hu : LevelAt h q u) (hx : t.locals.lookup x = some (.val (.word q))) :
    @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) (ldo x 8) =
      some (.val (.word u.hashData.toBitVec)) := by
  obtain ⟨_, h8⟩ := levelAt_hash hu
  obtain ⟨d, m⟩ := hm _ _ h8
  exact ldo_eval t x 8 q _ hx d m

theorem eval_const_u {σ : Type} (t : PanSemStateFiniteExact 64 σ) (c : UInt64) :
    @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) (.const c.toBitVec) =
      some (.val (.word c.toBitVec)) := by simp [evalHOLExact]

/-- Entering `lsub`: the case of the node's tag runs. -/
theorem lentry {σ : Type} (fn lk : MlS) (t : PanSemStateFiniteExact 64 σ) (lo hp p tg : BitVec 64)
    (hi : AInv t lo hp) (hu : t.locals.lookup iU = some (.val (.word p)))
    (h0 : hOf t lo hp p = some (.word tg)) (P : Heap → BitVec 64 → Prop) (c : Nat)
    (hcase : ∀ t2 : PanSemStateFiniteExact 64 σ, t2.code = t.code → t2.memory = t.memory →
      t2.memaddrs = t.memaddrs → t2.globals = t.globals → t2.topAddr = t.topAddr → t2.clock = t.clock →
      t2.locals.lookup iU = some (.val (.word p)) → (∀ y, y ≠ ConPanqueque.Fold.nTg → t2.locals.lookup y = t.locals.lookup y) →
      RRes t2 (evaluateHOLFiniteState t2 (ConPanqueque.Fold.pick tg (lcases fn lk) (.return (vv iU)))) lo hp P c) :
    RRes t (evaluateHOLFiniteState t (lsubBody fn lk)) lo hp P c := by
  have m0 := (ainv_arena hi).1 _ _ h0
  let t2 := setVarHOLFinite ConPanqueque.Fold.nTg (.val (.word tg)) t
  obtain ⟨L2, e2⟩ := dec_word' t ConPanqueque.Fold.nTg (.load .one (vv iU)) tg _
    (by rw [eval_load_word t _ p (by simp [vv, evalHOLExact, hu]) m0.1]; show some (ValueHOL.val (t.memory p)) = _; rw [m0.2])
  unfold lsubBody; rw [e2]
  apply rres_locals
  rw [ConPanqueque.Fold.iteChain_eval t2 tg (by simp [t2]) _]
  exact rres_of_eq (hcase t2 rfl rfl rfl rfl rfl rfl
    (by simp only [t2]; rw [lookup_setVar_other _ _ (by decide)]; exact hu)
    (fun y hy => by simp only [t2]; exact lookup_setVar_other _ _ hy)) rfl rfl rfl rfl rfl rfl

theorem fin_succ {σ : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ)
    (lo hq q1 : BitVec 64) (v1 : ConLeche.Level) (hi : AInv t lo hq) (e1 : LevelAt (hOf t lo hq) q1 v1)
    (l1 : t.locals.lookup iRa = some (.val (.word q1))) :
    RRes t (evaluateHOLFiniteState t (mkNode 1 (ConPanqueque.Hash.mixExp (.const 3) (ldo iRa 8)) [iRa])) lo hq
      (fun h q => LevelAt h q (.succ v1)) 0 := by
  have hd := ConPanqueque.Hash.eval_mixExp t (.const 3) (ldo iRa 8) 3 v1.hashData (by simp [evalHOLExact] <;> rfl)
    (hash_load (ainv_arena hi).1 e1 l1)
  rw [← ConPanqueque.LevelCons.levelSucc_hash ra] at hd
  rcases mkNode_ainv t lo hq 1 _ _ [iRa] [q1] rfl (by decide) (by decide) (by decide) (by simp) hd
      (fun j hj => match j, hj with | 0, _ => l1) hi with
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
  exact ⟨hq, hr, _, a5, g5, .succ hpos c0 c1 c2 (levelAt_mono (grows_sub g5) e1), cd5,
    by rw [ck5]; omega, gl5, md5, ta5⟩

theorem fin_binL {σ : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ)
    (tag : BitVec 64) (c : UInt64) (mk : ConLeche.Level → ConLeche.Level → ConLeche.Level)
    (hmk : ∀ u v, (mk u v).hashData = ConPanqueque.Hash.leanMixHash c (ConPanqueque.Hash.leanMixHash u.hashData v.hashData))
    (hbuild : ∀ (h' : Heap) (p0 q1 q2 : BitVec 64) u v, p0 ≠ 0 → h' p0 = some (.word tag) →
      h' (p0 + 8) = some (.word (mk u v).hashData.toBitVec) → h' (p0 + 16) = some (.word q1) →
      h' (p0 + 24) = some (.word q2) → LevelAt h' q1 u → LevelAt h' q2 v → LevelAt h' p0 (mk u v))
    (lo hq q1 q2 : BitVec 64) (v1 v2 : ConLeche.Level) (hi : AInv t lo hq) (e1 : LevelAt (hOf t lo hq) q1 v1)
    (e2 : LevelAt (hOf t lo hq) q2 v2)
    (l1 : t.locals.lookup iRa = some (.val (.word q1))) (l2 : t.locals.lookup iRb = some (.val (.word q2))) :
    RRes t (evaluateHOLFiniteState t (mkNode tag (ConPanqueque.Hash.mixExp (.const c.toBitVec)
      (ConPanqueque.Hash.mixExp (ldo iRa 8) (ldo iRb 8))) [iRa, iRb])) lo hq
      (fun h q => LevelAt h q (mk v1 v2)) 0 := by
  have hm := (ainv_arena hi).1
  have hd := ConPanqueque.Hash.eval_mixExp t (.const c.toBitVec) _ c _ (eval_const_u t c)
    (ConPanqueque.Hash.eval_mixExp t _ _ _ _ (hash_load hm e1 l1) (hash_load hm e2 l2))
  rw [← hmk] at hd
  rcases mkNode_ainv t lo hq tag _ _ [iRa, iRb] [q1, q2] rfl (by decide) (by decide) (by decide) (by simp) hd
      (fun j hj => match j, hj with | 0, _ => l1 | 1, _ => l2) hi with
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
  have sub := grows_sub g5
  exact ⟨hq, hr, _, a5, g5, hbuild _ hq q1 q2 v1 v2 hpos c0 c1 c2 c3 (levelAt_mono sub e1) (levelAt_mono sub e2),
    cd5, by rw [ck5]; omega, gl5, md5, ta5⟩

section
variable {σ : Type} (ra : ConPanqueque.Hash.RuntimeAssumptions) (fn lk : MlS)
  (C : HolFiniteMapExact MlS (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL))
  (hC : C.lookup fn = some ([(iU, .one), (iK, .one)], lsubBody fn lk, .one))
  (hCk : C.lookup lk = some ([(iC, .one), (iN, .one)], lkpBody lk, .one))
  (ks : List ConLeche.Name) (vs : List ConLeche.Level) (c lo : BitVec 64) (h : Heap)

theorem hB_of_lspec {q : BitVec 64} {u : ConLeche.Level} (ihs : LSpec (σ := σ) fn lk C ks vs c lo h q u)
    (ti : PanSemStateFiniteExact 64 σ) (hq : BitVec 64) (hsub : Sub h (hOf ti lo hq))
    (hg : ti.globals.lookup gKV = some (.val (.word c))) (a2 : BitVec 64) :
    ∀ s' : PanSemStateFiniteExact 64 σ, s'.code = C → AInv s' lo hq → s'.memory = ti.memory →
      s'.globals = ti.globals → s'.locals.lookup iU = some (.val (.word q)) →
      s'.locals.lookup iK = some (.val (.word a2)) → lcost (ks.zip vs).length u ≤ s'.clock →
      RRes s' (evaluateHOLFiniteState s' (lsubBody fn lk)) lo hq
        (fun h q => LevelAt h q (ConLeche.Level.subst ks vs u)) (lcost (ks.zip vs).length u) := by
  intro s' cd a m g hu hk hc
  exact ihs s' hq cd a (by rw [hOf_of_eq lo hq m]; exact hsub) (by rw [g]; exact hg) hu ⟨a2, hk⟩ hc


include ra hC in
theorem lspec_bin (tag : BitVec 64) (cc : UInt64) (mk : ConLeche.Level → ConLeche.Level → ConLeche.Level)
    (hmk : ∀ u v, (mk u v).hashData = ConPanqueque.Hash.leanMixHash cc (ConPanqueque.Hash.leanMixHash u.hashData v.hashData))
    (hbuild : ∀ (h' : Heap) (p0 q1 q2 : BitVec 64) u v, p0 ≠ 0 → h' p0 = some (.word tag) →
      h' (p0 + 8) = some (.word (mk u v).hashData.toBitVec) → h' (p0 + 16) = some (.word q1) →
      h' (p0 + 24) = some (.word q2) → LevelAt h' q1 u → LevelAt h' q2 v → LevelAt h' p0 (mk u v))
    (hpick : ConPanqueque.Fold.pick tag (lcases fn lk) (.return (vv iU)) = binL fn tag cc.toBitVec)
    (hsb : ∀ v w, ConLeche.Level.subst ks vs (mk v w) = mk (ConLeche.Level.subst ks vs v) (ConLeche.Level.subst ks vs w))
    (hcost : ∀ v w, lcost (ks.zip vs).length (mk v w) = 1 + lcost (ks.zip vs).length v + (1 + lcost (ks.zip vs).length w + 0))
    {p q r : BitVec 64} {v w : ConLeche.Level} (h0 : h p = some (.word tag)) (h2 : h (p + 16) = some (.word q))
    (h3 : h (p + 24) = some (.word r))
    (ihv : LSpec (σ := σ) fn lk C ks vs c lo h q v) (ihw : LSpec (σ := σ) fn lk C ks vs c lo h r w) :
    LSpec (σ := σ) fn lk C ks vs c lo h p (mk v w) := by
  intro t hq hcd hai hs hg hlu hk hck
  apply lentry fn lk t lo hq _ tag hai hlu (hs _ _ h0)
  intro t2 cd2 m2 d2 g2 ta2 ck2 hu2 lo2
  rw [hpick]
  have hO2 : hOf t2 lo hq = hOf t lo hq := hOf_of_eq lo hq m2
  have hai2 : AInv t2 lo hq := ainv_of_eq hai g2 d2 ta2
  have hs2 : Sub h (hOf t2 lo hq) := by rw [hO2]; exact hs
  have hg2 : t2.globals.lookup gKV = some (.val (.word c)) := by rw [g2]; exact hg
  obtain ⟨kw, hk⟩ := hk
  have hk2 : t2.locals.lookup iK = some (.val (.word kw)) := by rw [lo2 _ (by decide)]; exact hk
  have m16 := (ainv_arena hai2).1 _ _ (hs2 _ _ h2)
  rw [hcost] at hck ⊢
  rw [hsb]
  unfold binL
  apply step_call fn iRa iU iK C _ _ (by decide) hC (fun h q => LevelAt h q (ConLeche.Level.subst ks vs v)) _ _ _
    t2 lo hq q kw (ldo iU 16) (vv iK) (by rw [cd2]; exact hcd) hai2
    (ldo_eval _ iU 16 _ q (by rw [lookup_setVar_other _ _ (by decide)]; exact hu2) m16.1 m16.2)
    (by simp [vv, evalHOLExact] <;> (rw [lookup_setVar_other _ _ (by decide)]; exact hk2)) (by omega)
    (hB_of_lspec fn lk C ks vs c lo h ihv t2 hq hs2 hg2 kw)
  intro t3 q1 hq1 cd3 a3 g3 r1 l3a l3o ck3 gl3 md3 ta3
  have hs3 : Sub h (hOf t3 lo hq1) := fun x y hx => grows_sub g3 x y (hs2 x y hx)
  have m24 := arena_read (hs2 _ _ h3) g3 a3
  have hu3 : t3.locals.lookup iU = some (.val (.word p)) := by rw [l3o _ (by decide)]; exact hu2
  have hk3 : t3.locals.lookup iK = some (.val (.word kw)) := by rw [l3o _ (by decide)]; exact hk2
  apply step_call fn iRb iU iK C _ _ (by decide) hC (fun h q => LevelAt h q (ConLeche.Level.subst ks vs w)) _ _ _
    t3 lo hq1 r kw (ldo iU 24) (vv iK) cd3 a3
    (ldo_eval _ iU 24 p r (by rw [lookup_setVar_other _ _ (by decide)]; exact hu3) m24.1 m24.2)
    (by simp [vv, evalHOLExact] <;> (rw [lookup_setVar_other _ _ (by decide)]; exact hk3)) (by omega)
    (hB_of_lspec fn lk C ks vs c lo h ihw t3 hq1 hs3 (by rw [gl3 gKV (by decide)]; exact hg2) kw)
  intro t4 q2 hq2 cd4 a4 g4 r2 l4b l4o ck4 gl4 md4 ta4
  exact fin_binL ra t4 tag cc mk hmk hbuild lo hq2 q1 q2 _ _ a4 (levelAt_mono (grows_sub g4) r1) r2
    (by rw [l4o _ (by decide)]; exact l3a) l4b

include ra hC hCk in
theorem lsub_spec (hkv : KVAt h c (ks.zip vs)) (hint : Interned h) {p : BitVec 64} {u : ConLeche.Level}
    (hu : LevelAt h p u) : LSpec (σ := σ) fn lk C ks vs c lo h p u := by
  induction hu with
  | zero hp h0 h1 =>
    intro t hq hcd hai hs hg hlu hk hck
    apply lentry fn lk t lo hq _ 0 hai hlu (hs _ _ h0)
    intro t2 cd2 m2 d2 g2 ta2 ck2 hu2 _
    show RRes t2 (evaluateHOLFiniteState t2 (.return (vv iU))) lo hq _ _
    rw [eval_return_local t2 iU _ hu2]
    exact rres_of_eq (rres_ret (ainv_of_eq hai g2 d2 ta2)
      (by rw [hOf_of_eq lo hq m2]; exact levelAt_mono hs (.zero hp h0 h1)) rfl rfl rfl rfl rfl rfl)
      rfl rfl rfl rfl rfl rfl
  | @succ p q v hp h0 h1 h2 hv ih =>
    intro t hq hcd hai hs hg hlu hk hck
    apply lentry fn lk t lo hq _ 1 hai hlu (hs _ _ h0)
    intro t2 cd2 m2 d2 g2 ta2 ck2 hu2 lo2
    show RRes t2 (evaluateHOLFiniteState t2 (succC fn)) lo hq _ _
    have hO2 : hOf t2 lo hq = hOf t lo hq := hOf_of_eq lo hq m2
    have hai2 : AInv t2 lo hq := ainv_of_eq hai g2 d2 ta2
    have hs2 : Sub h (hOf t2 lo hq) := by rw [hO2]; exact hs
    obtain ⟨kw, hk⟩ := hk
    have hk2 : t2.locals.lookup iK = some (.val (.word kw)) := by rw [lo2 _ (by decide)]; exact hk
    have m16 := (ainv_arena hai2).1 _ _ (hs2 _ _ h2)
    have hcost : lcost (ks.zip vs).length (.succ v) = 1 + lcost (ks.zip vs).length v + 0 := by simp [lcost]
    rw [hcost] at hck ⊢
    unfold succC
    apply step_call fn iRa iU iK C _ _ (by decide) hC (fun h q => LevelAt h q (ConLeche.Level.subst ks vs v)) _ _ _
      t2 lo hq q kw (ldo iU 16) (vv iK) (by rw [cd2]; exact hcd) hai2
      (ldo_eval _ iU 16 _ q (by rw [lookup_setVar_other _ _ (by decide)]; exact hu2) m16.1 m16.2)
      (by simp [vv, evalHOLExact] <;> (rw [lookup_setVar_other _ _ (by decide)]; exact hk2)) (by omega)
      (hB_of_lspec fn lk C ks vs c lo h ih t2 hq hs2 (by rw [g2]; exact hg) kw)
    intro t3 q1 hq1 cd3 a3 g3 r1 l3a l3o ck3 gl3 md3 ta3
    simp only [ConLeche.Level.subst]
    exact fin_succ ra t3 lo hq1 q1 _ a3 r1 l3a
  | @max p q r v w hp h0 h1 h2 h3 hv hw ihv ihw =>
    exact lspec_bin ra fn lk C hC ks vs c lo h 2 5 ConLeche.Level.max
      (fun u v => by simp [ConLeche.Level.hashData, ra.mixHash])
      (fun h' p0 q1 q2 u v a b c' d e f g => .max a b c' d e f g) rfl (fun _ _ => rfl)
      (fun _ _ => by simp [lcost]) h0 h2 h3 ihv ihw
  | @imax p q r v w hp h0 h1 h2 h3 hv hw ihv ihw =>
    exact lspec_bin ra fn lk C hC ks vs c lo h 3 7 ConLeche.Level.imax
      (fun u v => by simp [ConLeche.Level.hashData, ra.mixHash])
      (fun h' p0 q1 q2 u v a b c' d e f g => .imax a b c' d e f g) rfl (fun _ _ => rfl)
      (fun _ _ => by simp [lcost]) h0 h2 h3 ihv ihw
  | @param p q n hp h0 h1 h2 hn =>
    intro t hq hcd hai hs hg hlu hk hck
    apply lentry fn lk t lo hq _ 4 hai hlu (hs _ _ h0)
    intro t2 cd2 m2 d2 g2 ta2 ck2 hu2 lo2
    show RRes t2 (evaluateHOLFiniteState t2 (paramC lk)) lo hq _ _
    have hO2 : hOf t2 lo hq = hOf t lo hq := hOf_of_eq lo hq m2
    have hai2 : AInv t2 lo hq := ainv_of_eq hai g2 d2 ta2
    have hs2 : Sub h (hOf t2 lo hq) := by rw [hO2]; exact hs
    have hm2 : InMem t2 h := fun a w ha => (ainv_arena hai2).1 a w (hs2 a w ha)
    have m16 := hm2 _ _ h2
    let t3 := setVarHOLFinite iR (.val (.word 0)) t2
    obtain ⟨L3, e3⟩ := dec_word' t2 iR (.const 0) 0
      (.seq (.call (some (some (.local, iR), none)) lk [.var .global gKV, ldo iU 16])
        (.ite (.cmp .equal (vv iR) (.const 0)) (.return (vv iU)) (.return (vv iR)))) (by simp [evalHOLExact])
    have hu3 : t3.locals.lookup iU = some (.val (.word p)) := by
      simp only [t3]; rw [lookup_setVar_other _ _ (by decide)]; exact hu2
    have hcode3 : t3.code.lookup lk = some ([(iC, .one), (iN, .one)], lkpBody lk, .one) := by
      show t2.code.lookup lk = _; rw [cd2, hcd]; exact hCk
    obtain ⟨callee, hlk, hx1, hx2⟩ := lookupCode2 t3 lk iC iN (lkpBody lk) c q (by decide) hcode3
    have hargs : evalListHOLFinite t3 (h := fun a => Classical.propDecidable (t3.memaddrs a))
        [.var .global gKV, ldo iU 16] = some [.val (.word c), .val (.word q)] := by
      simp only [evalListHOLFinite, evalListHOLExact]
      rw [ldo_eval t3 iU 16 p q hu3 m16.1 m16.2]
      have : t3.globals.lookup gKV = some (.val (.word c)) := by show t2.globals.lookup gKV = _; rw [g2]; exact hg
      simp [evalHOLExact, this]
    let s' := callEntryStateHOLFinite t3 callee
    have hint' : ∀ pk k, NameAt h pk k → (pk = q ↔ k = n) := fun pk k hk =>
      ⟨fun e => by subst e; exact nameAt_unique hk hn, fun e => by subst e; exact hint _ _ _ hk hn⟩
    simp only [lcost] at hck ⊢
    obtain ⟨w, st, hb, hres, ⟨cd, mm, md, ck⟩, hgl, hta⟩ := lkp_spec lk h q n hint' hkv s'
      (by simp only [s', callEntryStateHOLFinite]; exact hcode3) hm2 hx1 hx2
      (by simp only [s', callEntryStateHOLFinite]; show _ ≤ t2.clock - 1; omega)
    have hcall := call_assign t3 .local iR lk none _ _ (lkpBody lk) callee .one (.val (.word w)) st
      hargs hlk (by show t2.clock ≠ 0; omega) hb (by simp [shapeOfHOLExact, shapeEqHOL])
      (by simp [isValidValueHOLExact, lookupKvarHOLExact, t3, shapeOfHOLExact, shapeEqHOL])
    let t4 := setKvarHOLFinite .local iR (.val (.word w)) { st with locals := t3.locals }
    unfold paramC; rw [e3]; apply rres_locals; rw [seq_normal _ hcall]
    have l4r : t4.locals.lookup iR = some (.val (.word w)) := by simp [t4, setKvarHOLFinite]
    have l4u : t4.locals.lookup iU = some (.val (.word p)) := by
      simp only [t4, setKvarHOLFinite]; rw [lookup_setVar_other _ _ (by decide)]; exact hu3
    have f4 : t4.memory = t2.memory ∧ t4.code = t2.code ∧ t4.globals = t2.globals ∧ t4.memaddrs = t2.memaddrs ∧
        t4.topAddr = t2.topAddr := by
      simp [t4, setKvarHOLFinite, setVarHOLFinite, mm, cd, hgl, md, hta, s', callEntryStateHOLFinite, t3]
    rw [ite_word t4 _ _ _ (if w = 0 then 1 else 0)
      (by simp [vv, evalHOLExact, l4r, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])]
    have hclk : t2.clock ≤ (emptyLocalsHOLFinite t4).clock + (1 + (ks.zip vs).length) := by
      simp [t4, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, s', callEntryStateHOLFinite, t3] at ck ⊢
      omega
    rcases hres with ⟨hz, hw⟩ | ⟨v, hgz, hlv⟩
    · subst hw
      simp only [↓reduceIte, ne_eq, show ¬ (1 : BitVec 64) = 0 from by decide, not_false_eq_true]
      rw [eval_return_local t4 iU p l4u]
      refine Or.inr ⟨p, rfl, hq, ainv_of_eq hai2 (by simp [emptyLocalsHOLFinite, f4.2.2.1])
        (by simp [emptyLocalsHOLFinite, f4.2.2.2.1]) (by simp [emptyLocalsHOLFinite, f4.2.2.2.2]),
        ⟨BitVec.le_refl _, fun a _ _ => by simp [emptyLocalsHOLFinite, f4.1]⟩, ?_,
        by simp [emptyLocalsHOLFinite, f4.2.1], hclk, fun g' _ => by simp [emptyLocalsHOLFinite, f4.2.2.1],
        by simp [emptyLocalsHOLFinite, f4.2.2.2.1], by simp [emptyLocalsHOLFinite, f4.2.2.2.2]⟩
      rw [hOf_of_eq lo hq (show (emptyLocalsHOLFinite t4).memory = t2.memory by simp [emptyLocalsHOLFinite, f4.1])]
      simp only [ConLeche.Level.subst, subst_go_eq, hz, Option.getD_none]
      exact levelAt_mono hs2 (.param hp h0 h1 h2 hn)
    · have hw0 : w ≠ 0 := (levelAt_hash hlv).1
      simp only [hw0, ↓reduceIte, ne_eq, not_true_eq_false]
      rw [eval_return_local t4 iR w l4r]
      refine Or.inr ⟨w, rfl, hq, ainv_of_eq hai2 (by simp [emptyLocalsHOLFinite, f4.2.2.1])
        (by simp [emptyLocalsHOLFinite, f4.2.2.2.1]) (by simp [emptyLocalsHOLFinite, f4.2.2.2.2]),
        ⟨BitVec.le_refl _, fun a _ _ => by simp [emptyLocalsHOLFinite, f4.1]⟩, ?_,
        by simp [emptyLocalsHOLFinite, f4.2.1], hclk, fun g' _ => by simp [emptyLocalsHOLFinite, f4.2.2.1],
        by simp [emptyLocalsHOLFinite, f4.2.2.2.1], by simp [emptyLocalsHOLFinite, f4.2.2.2.2]⟩
      rw [hOf_of_eq lo hq (show (emptyLocalsHOLFinite t4).memory = t2.memory by simp [emptyLocalsHOLFinite, f4.1])]
      simp only [ConLeche.Level.subst, subst_go_eq, hgz, Option.getD_some]
      exact levelAt_mono hs2 hlv

end

end ConPanqueque.LevelSubst
