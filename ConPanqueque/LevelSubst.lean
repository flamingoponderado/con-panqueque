import ConPanqueque.Subst
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
        ConPanqueque.Fold.Post t st kvs.length := by
  induction hk with
  | nil =>
    intro t hc hm hlc hln hck
    refine ⟨0, emptyLocalsHOLFinite t, ?_, Or.inl ⟨rfl, rfl⟩, ?_⟩
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
      refine ⟨pv, emptyLocalsHOLFinite t, ?_, Or.inr ⟨v, by simp [goZ, hkn'], hv⟩, ?_⟩
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
      obtain ⟨w, st, hb, hres, hpost⟩ := ih s' (by simp only [s', callEntryStateHOLFinite]; exact hc) hm hx1 hx2
        (by simp [s', callEntryStateHOLFinite, t1]; exact hck')
      have hcall := call_assign t1 .local iR fn none [ldo iC 16, vv iN] _ (lkpBody fn) callee .one (.val (.word w)) st
        hargs hlk (by show t.clock ≠ 0; simp at hck; omega) hb (by simp [shapeOfHOLExact, shapeEqHOL])
        (by simp [isValidValueHOLExact, lookupKvarHOLExact, t1, shapeOfHOLExact, shapeEqHOL])
      let t2 := setKvarHOLFinite .local iR (.val (.word w)) { st with locals := t1.locals }
      have eret : evaluateHOLFiniteState t2 (.return (vv iR)) = (some (.returned (.val (.word w))), emptyLocalsHOLFinite t2) :=
        eval_return_local t2 iR w (by simp [t2, setKvarHOLFinite])
      rw [e1]; simp only; rw [seq_normal _ hcall, eret]
      refine ⟨w, _, rfl, ?_, ?_⟩
      · rcases hres with ⟨hz, hw⟩ | ⟨v', hg, hl⟩
        · exact Or.inl ⟨by simp [goZ, hkn', hz], hw⟩
        · exact Or.inr ⟨v', by simp [goZ, hkn', hg], hl⟩
      · obtain ⟨cd, mm, md, ck⟩ := hpost
        refine ⟨?_, ?_, ?_, ?_⟩ <;>
          simp [t2, setKvarHOLFinite, setVarHOLFinite, emptyLocalsHOLFinite, cd, mm, md, s', callEntryStateHOLFinite, t1] at ck ⊢
        omega

end ConPanqueque.LevelSubst
