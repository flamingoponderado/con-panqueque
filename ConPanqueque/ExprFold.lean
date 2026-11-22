import ConPanqueque.Fold
import ConPanqueque.ExprRep
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic ConPanqueque.Fold

/-!
# A verified recursion template: folds over expressions

`body fn g` is one Pancake function for every fold over con-leche's `Expr` in the
arena: it loads the node's tag, dispatches (`iteChain`), recurses on the child
expressions (`callKids`), and returns the constructor's result expression `g c`
(over the children's results in locals `a`, `b`, `c`). `fold_spec` proves it once,
by induction on `ExprAt`: for any `f` whose equations the expressions satisfy
(`ExprFoldSpec`), it returns `f e`. Concrete expression functions are instances,
with no induction.
-/

namespace ConPanqueque.ExprFold

def nA := ofString "a"
def nB := ofString "b"
def nC := ofString "c"

/-- The cases of an expression fold: per tag, its child offsets and result expression. -/
def cases (fn : MlS) (g : Fin 10 → ExpHOL 64) : List (BitVec 64 × ProgHOL 64) :=
  [(0, callKids fn [] (.return (g 0))),
   (1, callKids fn [(nA, 24)] (.return (g 1))),
   (2, callKids fn [] (.return (g 2))),
   (3, callKids fn [] (.return (g 3))),
   (4, callKids fn [(nA, 16), (nB, 24)] (.return (g 4))),
   (5, callKids fn [(nA, 16), (nB, 24)] (.return (g 5))),
   (6, callKids fn [(nA, 16), (nB, 24)] (.return (g 6))),
   (7, callKids fn [(nA, 16), (nB, 24), (nC, 32)] (.return (g 7))),
   (8, callKids fn [] (.return (g 8))),
   (9, callKids fn [(nA, 32)] (.return (g 9)))]

/-- A fold over an expression in the arena. -/
def body (fn : MlS) (g : Fin 10 → ExpHOL 64) : ProgHOL 64 :=
  .dec nTg .one (.load .one vU) (iteChain (cases fn g) (.return (.const 0)))

/-- One case: the node's tag is `c`, its case is `callKids ks (return gc)`. -/
theorem fold_case {σ : Type} (fn : MlS) (g : Fin 10 → ExpHOL 64) (h : Heap) (p c : BitVec 64)
    (ks : List Kid) (gc : ExpHOL 64) (W : UInt64)
    (hpick : pick c (cases fn g) (.return (.const 0)) = callKids fn (ks.map fun k => (k.x, k.off)) (.return gc))
    (hnd : (ks.map Kid.x).Nodup) (hnu : nU ∉ ks.map Kid.x) (htg : nTg ∉ ks.map Kid.x)
    (hkids : ∀ k ∈ ks, h (p + k.off) = some (.word k.q) ∧
        ∀ t' : PanSemStateFiniteExact 64 σ, t'.code.lookup fn = some ([(nU, .one)], body fn g, .one) → InMem t' h →
          t'.locals.lookup nU = some (.val (.word k.q)) → k.c ≤ t'.clock →
          ∃ st, evaluateHOLFiniteState t' (body fn g) = (some (.returned (.val (.word k.r.toBitVec))), st) ∧
            Post t' st k.c)
    (hg : ∀ t' : PanSemStateFiniteExact 64 σ, (∀ k ∈ ks, t'.locals.lookup k.x = some (.val (.word k.r.toBitVec))) →
      @evalHOLExact 64 σ _ t'.toExact (fun x => Classical.propDecidable (t'.memaddrs x)) gc =
        some (.val (.word W.toBitVec)))
    (s : PanSemStateFiniteExact 64 σ) (hc : s.code.lookup fn = some ([(nU, .one)], body fn g, .one))
    (hm : InMem s h) (hu : s.locals.lookup nU = some (.val (.word p))) (h0 : h p = some (.word c))
    (hck : kidsCost ks ≤ s.clock) :
    ∃ st, evaluateHOLFiniteState s (body fn g) = (some (.returned (.val (.word W.toBitVec))), st) ∧
      Post s st (kidsCost ks) := by
  obtain ⟨d0, m0⟩ := hm _ _ h0
  obtain ⟨L, hdec⟩ := dec_word' s nTg (.load .one vU) c (iteChain (cases fn g) (.return (.const 0))) (by
    rw [eval_load_word s _ _ (by simp [evalHOLExact, vU, hu]) d0, m0])
  let s1 := setVarHOLFinite nTg (.val (.word c)) s
  have ltg : s1.locals.lookup nTg = some (.val (.word c)) := by simp [s1]
  have hun : nU ≠ nTg := by decide
  have lu : s1.locals.lookup nU = some (.val (.word p)) := by
    simp only [s1]; rw [lookup_setVar_other _ _ hun]; exact hu
  obtain ⟨st, ev, post⟩ := callKids_spec fn (body fn g) h p ks [] (.return gc) W 0 s1 hnd hnu (by simp) hkids
    (fun t' _ _ _ _ _ hk _ => by
      refine ⟨emptyLocalsHOLFinite t', ?_, ?_⟩
      · rw [evaluateHOLFiniteState_eq_evaluate_def]; simp only; rw [hg t' hk]
        simp only [shapeOfHOLExact, sizeOfShapeWithContextHOL]
        simp only [show (1 : Nat) ≤ 32 from by decide, ite_true]
      · simp [Post, emptyLocalsHOLFinite])
    (by simpa [s1, setVarHOLFinite] using hc)
    (fun a w ha => by simpa [s1, setVarHOLFinite] using hm a w ha) lu (by simp)
    (by simp [s1, setVarHOLFinite]; omega)
  unfold body
  rw [hdec, show setVarHOLFinite nTg (.val (.word c)) s = s1 from rfl, iteChain_eval s1 c ltg, hpick, ev]
  obtain ⟨a1, a2, a3, a4⟩ := post
  exact ⟨_, rfl, by simp [a1, s1, setVarHOLFinite], by simp [a2, s1, setVarHOLFinite],
    by simp [a3, s1, setVarHOLFinite], by simp [s1, setVarHOLFinite] at a4; simpa using a4⟩

end ConPanqueque.ExprFold

namespace ConPanqueque.ExprFold

def EvW {σ : Type} (t : PanSemStateFiniteExact 64 σ) (e : ExpHOL 64) (w : UInt64) : Prop :=
  @evalHOLExact 64 σ _ t.toExact (fun x => Classical.propDecidable (t.memaddrs x)) e = some (.val (.word w.toBitVec))

def Lv {σ : Type} (t : PanSemStateFiniteExact 64 σ) (x : MlS) (w : UInt64) : Prop :=
  t.locals.lookup x = some (.val (.word w.toBitVec))

/-- The per-constructor result expressions of a fold and the function they compute. -/
structure ExprFoldSpec (g : Fin 10 → ExpHOL 64) (f : ConLeche.Expr → UInt64) : Prop where
  bvar : ∀ {σ : Type} (t : PanSemStateFiniteExact 64 σ) i, EvW t (g 0) (f (.bvar i))
  fvar : ∀ {σ : Type} (t : PanSemStateFiniteExact 64 σ) i ty, Lv t nA (f ty) → EvW t (g 1) (f (.fvar i ty))
  sort : ∀ {σ : Type} (t : PanSemStateFiniteExact 64 σ) u, EvW t (g 2) (f (.sort u))
  const : ∀ {σ : Type} (t : PanSemStateFiniteExact 64 σ) n us, EvW t (g 3) (f (.const n us))
  app : ∀ {σ : Type} (t : PanSemStateFiniteExact 64 σ) a b, Lv t nA (f a) → Lv t nB (f b) → EvW t (g 4) (f (.app a b))
  lam : ∀ {σ : Type} (t : PanSemStateFiniteExact 64 σ) a b, Lv t nA (f a) → Lv t nB (f b) → EvW t (g 5) (f (.lam a b))
  forallE : ∀ {σ : Type} (t : PanSemStateFiniteExact 64 σ) a b, Lv t nA (f a) → Lv t nB (f b) →
    EvW t (g 6) (f (.forallE a b))
  letE : ∀ {σ : Type} (t : PanSemStateFiniteExact 64 σ) a b c, Lv t nA (f a) → Lv t nB (f b) → Lv t nC (f c) →
    EvW t (g 7) (f (.letE a b c))
  lit : ∀ {σ : Type} (t : PanSemStateFiniteExact 64 σ) l, EvW t (g 8) (f (.lit l))
  proj : ∀ {σ : Type} (t : PanSemStateFiniteExact 64 σ) n i e, Lv t nA (f e) → EvW t (g 9) (f (.proj n i e))

/-- Calls made: one per child expression, recursively. -/
def cost : ConLeche.Expr → Nat
  | .bvar _ | .sort _ | .const _ _ | .lit _ => 0
  | .fvar _ ty | .proj _ _ ty => 1 + cost ty
  | .app a b | .lam a b | .forallE a b => 1 + cost a + (1 + cost b)
  | .letE a b c => 1 + cost a + (1 + cost b + (1 + cost c))

/-- The expression fold template computes `f`. -/
theorem fold_spec {σ : Type} (fn : MlS) (g : Fin 10 → ExpHOL 64) (f : ConLeche.Expr → UInt64)
    (sp : ExprFoldSpec g f) (h : Heap) {p : BitVec 64} {e : ConLeche.Expr} (he : ExprAt h p e) :
    ∀ s : PanSemStateFiniteExact 64 σ,
      s.code.lookup fn = some ([(nU, .one)], body fn g, .one) → InMem s h →
      s.locals.lookup nU = some (.val (.word p)) → cost e ≤ s.clock →
      ∃ st, evaluateHOLFiniteState s (body fn g) = (some (.returned (.val (.word (f e).toBitVec))), st) ∧
        Post s st (cost e) := by
  induction he with
  | bvar hp h0 hd h2 hi =>
    intro s hc hm hu hck
    exact fold_case fn g h _ 0 [] (g 0) _ rfl (by simp) (by simp) (by simp) (by simp)
      (fun t _ => sp.bvar t _) s hc hm hu h0 (by simp [kidsCost])
  | @fvar p v q i ty hp h0 hd h2 h3 hi hty ih =>
    intro s hc hm hu hck
    have := fold_case fn g h p 1 [⟨nA, 24, q, f ty, cost ty⟩] (g 1) (f (.fvar i ty)) rfl (by simp) (by simp only [List.map_cons, List.map_nil]; decide) (by simp only [List.map_cons, List.map_nil]; decide)
      (by simpa using ⟨h3, ih⟩) (fun t hk => sp.fvar t i ty (by simp at hk; exact hk)) s hc hm hu h0
      (by simp [kidsCost, cost] at hck ⊢; omega)
    simpa [kidsCost, cost] using this
  | sort hp h0 hd h2 hu' =>
    intro s hc hm hu hck
    exact fold_case fn g h _ 2 [] (g 2) _ rfl (by simp) (by simp) (by simp) (by simp)
      (fun t _ => sp.sort t _) s hc hm hu h0 (by simp [kidsCost])
  | const hp h0 hd h2 h3 hn hus =>
    intro s hc hm hu hck
    exact fold_case fn g h _ 3 [] (g 3) _ rfl (by simp) (by simp) (by simp) (by simp)
      (fun t _ => sp.const t _ _) s hc hm hu h0 (by simp [kidsCost])
  | @app p q r a b hp h0 hd h2 h3 ha hb iha ihb =>
    intro s hc hm hu hck
    have := fold_case fn g h p 4 [⟨nA, 16, q, f a, cost a⟩, ⟨nB, 24, r, f b, cost b⟩] (g 4) (f (.app a b)) rfl
      (by simp only [List.map_cons, List.map_nil]; decide) (by simp only [List.map_cons, List.map_nil]; decide) (by simp only [List.map_cons, List.map_nil]; decide)
      (by simpa using ⟨⟨h2, iha⟩, ⟨h3, ihb⟩⟩) (fun t hk => sp.app t a b (by simp at hk; exact hk.1) (by simp at hk; exact hk.2))
      s hc hm hu h0 (by simp [kidsCost, cost] at hck ⊢; omega)
    simpa [kidsCost, cost] using this
  | @lam p q r a b hp h0 hd h2 h3 ha hb iha ihb =>
    intro s hc hm hu hck
    have := fold_case fn g h p 5 [⟨nA, 16, q, f a, cost a⟩, ⟨nB, 24, r, f b, cost b⟩] (g 5) (f (.lam a b)) rfl
      (by simp only [List.map_cons, List.map_nil]; decide) (by simp only [List.map_cons, List.map_nil]; decide) (by simp only [List.map_cons, List.map_nil]; decide)
      (by simpa using ⟨⟨h2, iha⟩, ⟨h3, ihb⟩⟩) (fun t hk => sp.lam t a b (by simp at hk; exact hk.1) (by simp at hk; exact hk.2))
      s hc hm hu h0 (by simp [kidsCost, cost] at hck ⊢; omega)
    simpa [kidsCost, cost] using this
  | @forallE p q r a b hp h0 hd h2 h3 ha hb iha ihb =>
    intro s hc hm hu hck
    have := fold_case fn g h p 6 [⟨nA, 16, q, f a, cost a⟩, ⟨nB, 24, r, f b, cost b⟩] (g 6) (f (.forallE a b)) rfl
      (by simp only [List.map_cons, List.map_nil]; decide) (by simp only [List.map_cons, List.map_nil]; decide) (by simp only [List.map_cons, List.map_nil]; decide)
      (by simpa using ⟨⟨h2, iha⟩, ⟨h3, ihb⟩⟩) (fun t hk => sp.forallE t a b (by simp at hk; exact hk.1) (by simp at hk; exact hk.2))
      s hc hm hu h0 (by simp [kidsCost, cost] at hck ⊢; omega)
    simpa [kidsCost, cost] using this
  | @letE p q r w a b c hp h0 hd h2 h3 h4 ha hb hc' iha ihb ihc =>
    intro s hc hm hu hck
    have := fold_case fn g h p 7 [⟨nA, 16, q, f a, cost a⟩, ⟨nB, 24, r, f b, cost b⟩, ⟨nC, 32, w, f c, cost c⟩]
      (g 7) (f (.letE a b c)) rfl (by simp only [List.map_cons, List.map_nil]; decide) (by simp only [List.map_cons, List.map_nil]; decide) (by simp only [List.map_cons, List.map_nil]; decide)
      (by simpa using ⟨⟨h2, iha⟩, ⟨h3, ihb⟩, ⟨h4, ihc⟩⟩)
      (fun t hk => sp.letE t a b c (by simp at hk; exact hk.1) (by simp at hk; exact hk.2.1) (by simp at hk; exact hk.2.2))
      s hc hm hu h0 (by simp [kidsCost, cost] at hck ⊢; omega)
    simpa [kidsCost, cost] using this
  | lit hp h0 hd h2 hl =>
    intro s hc hm hu hck
    exact fold_case fn g h _ 8 [] (g 8) _ rfl (by simp) (by simp) (by simp) (by simp)
      (fun t _ => sp.lit t _) s hc hm hu h0 (by simp [kidsCost])
  | @proj p q v r n i e hp h0 hd h2 h3 h4 hn hi he ih =>
    intro s hc hm hu hck
    have := fold_case fn g h p 9 [⟨nA, 32, r, f e, cost e⟩] (g 9) (f (.proj n i e)) rfl (by simp) (by simp only [List.map_cons, List.map_nil]; decide)
      (by simp only [List.map_cons, List.map_nil]; decide) (by simpa using ⟨h4, ih⟩) (fun t hk => sp.proj t n i e (by simp at hk; exact hk)) s hc hm hu h0
      (by simp [kidsCost, cost] at hck ⊢; omega)
    simpa [kidsCost, cost] using this

end ConPanqueque.ExprFold
