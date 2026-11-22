import ConPanqueque.ExprRep
import ConPanqueque.Arena
import ConPanqueque.AppData
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic ConPanqueque.Alloc

theorem inMem_of_eq {σ : Type} {t t' : PanSemStateFiniteExact 64 σ} {h : Heap}
    (hm : t'.memory = t.memory) (hd : t'.memaddrs = t.memaddrs) (hi : InMem t h) : InMem t' h := by
  intro a w ha; rw [hm, hd]; exact hi a w ha

def nP := ofString "p"
def nHp := ofString "hp"
def nTg := ofString "tg"
def nD := ofString "d"
def nF := ofString "f"
def nA := ofString "a"

/-- Allocate 4 words and write `[tg, d, f, a]`, returning the block. -/
def appTail : ProgHOL 64 :=
  .dec nP .one (.var .global nHp)
    (.seq (.assign .global nHp (.op .add [.var .global nHp, .const 32]))
      (.seq (storeSeq nP [nTg, nD, nF, nA] 0) (.return (.var .local nP))))

theorem appTail_spec {σ : Type} (t : PanSemStateFiniteExact 64 σ) (h : Heap) (p0 q r : BitVec 64)
    (f a : ConLeche.Expr)
    (htg : t.locals.lookup nTg = some (.val (.word 4)))
    (hd : t.locals.lookup nD = some (.val (.word (ConLeche.Expr.app f a).data.toBitVec)))
    (hf : t.locals.lookup nF = some (.val (.word q)))
    (ha : t.locals.lookup nA = some (.val (.word r)))
    (hhp : t.globals.lookup nHp = some (.val (.word p0)))
    (hi : ArenaInv t h p0) (hfit : ¬ t.topAddr - p0 < 32) (hnz : p0 ≠ 0)
    (hF : ExprAt h q f) (hA : ExprAt h r a) :
    ∃ h', (evaluateHOLFiniteState t appTail).1 = some (.returned (.val (.word p0))) ∧
      ArenaInv (evaluateHOLFiniteState t appTail).2 h' (p0 + 32) ∧ Sub h h' ∧ ExprAt h' p0 (.app f a) ∧
      (evaluateHOLFiniteState t appTail).2.globals.lookup nHp = some (.val (.word (p0 + 32))) := by
  have dPtg : nP ≠ nTg := by decide
  have dPd : nP ≠ nD := by decide
  have dPf : nP ≠ nF := by decide
  have dPa : nP ≠ nA := by decide
  obtain ⟨hfresh, hdist, hfree, hb⟩ := blockN 4 hi (by simpa using hfit) (by decide)
  let t0 := setVarHOLFinite nP (.val (.word p0)) t
  let t1 := setKvarHOLFinite .global nHp (.val (.word (p0 + 32))) t0
  have e1 : evaluateHOLFiniteState t0 (.assign .global nHp (.op .add [.var .global nHp, .const 32])) =
      (none, t1) := by
    apply assign_ok
    · simp [evalHOLExact, evalListHOLExact, t0, setVarHOLFinite, hhp, wordOpHOL, wordOp, valueIsWord, valueWord]
    · simp [isValidValueHOLFinite, lookupKvarHOLFinite, t0, setVarHOLFinite, hhp, shapeOfHOLExact, shapeEqHOL]
  have l1 : ∀ n, n ≠ nP → t1.locals.lookup n = t.locals.lookup n := by
    intro n hn; simp only [t1, t0, setKvarHOLFinite, setGlobalHOLFinite]; exact lookup_setVar_other _ _ hn
  have lp1 : t1.locals.lookup nP = some (.val (.word p0)) := by
    simp [t1, t0, setKvarHOLFinite, setGlobalHOLFinite]
  obtain ⟨t2, ev2, hl2, hd2, ht2, hg2, hm2, hs2⟩ :=
    storeSeq_spec nP p0 [nTg, nD, nF, nA] [4, (ConLeche.Expr.app f a).data.toBitVec, q, r] 0 t1 h rfl lp1
      (fun j hj => by
        match j, hj with
        | 0, _ => simpa [l1 nTg (Ne.symm dPtg)] using htg
        | 1, _ => simpa [l1 nD (Ne.symm dPd)] using hd
        | 2, _ => simpa [l1 nF (Ne.symm dPf)] using hf
        | 3, _ => simpa [l1 nA (Ne.symm dPa)] using ha)
      (inMem_of_eq (by simp [t1, t0, setKvarHOLFinite, setGlobalHOLFinite, setVarHOLFinite])
        (by simp [t1, t0, setKvarHOLFinite, setGlobalHOLFinite, setVarHOLFinite]) hi.1)
      (fun j hj => by
        obtain ⟨x, y⟩ := hfresh j (by simpa using hj)
        exact ⟨by simpa [t1, t0, setKvarHOLFinite, setGlobalHOLFinite, setVarHOLFinite] using x, by simpa using y⟩)
      (fun j k hj hk hjk => by simpa using hdist j k (by simpa using hj) (by simpa using hk) hjk)
  have lp2 : t2.locals.lookup nP = some (.val (.word p0)) := by rw [hl2]; exact lp1
  have eret : evaluateHOLFiniteState t2 (.return (.var .local nP)) =
      (some (.returned (.val (.word p0))), emptyLocalsHOLFinite t2) := by
    rw [evaluateHOLFiniteState_eq_evaluate_def]; simp [evalHOLExact, lp2, shapeOfHOLExact]
  have einner : evaluateHOLFiniteState t0
      (.seq (.assign .global nHp (.op .add [.var .global nHp, .const 32]))
        (.seq (storeSeq nP [nTg, nD, nF, nA] 0) (.return (.var .local nP)))) =
      (some (.returned (.val (.word p0))), emptyLocalsHOLFinite t2) := by
    rw [seq_normal _ e1, seq_normal _ ev2, eret]
  obtain ⟨r1, rm, rd, rg, rt⟩ := dec_word t nP (.var .global nHp) p0 _ (by simp [evalHOLExact, hhp])
  simp only [t0] at einner
  rw [einner] at r1 rm rd rg rt
  let h' := extSeq h p0 [4, (ConLeche.Expr.app f a).data.toBitVec, q, r] 0
  have get : ∀ j (hj : j < 4), h' (at8 p0 j) =
      some (.word ([4, (ConLeche.Expr.app f a).data.toBitVec, q, r][j]'(by simpa using hj))) := by
    intro j hj
    have := extSeq_get p0 [4, (ConLeche.Expr.app f a).data.toBitVec, q, r] 0 h j (by simpa using hj)
      (fun j k hj hk hjk => by simpa using hdist j k (by simpa using hj) (by simpa using hk) hjk)
    simp only [h']; simpa using this
  refine ⟨h', ?_, ⟨?_, ?_, ?_⟩, hs2, ?_, ?_⟩
  · unfold appTail; exact r1
  · unfold appTail
    exact inMem_of_eq (by rw [rm]; simp [emptyLocalsHOLFinite]) (by rw [rd]; simp [emptyLocalsHOLFinite]) hm2
  · unfold appTail
    have hfr : Free t2 (p0 + 32) := by
      simp only [Free] at hfree ⊢
      rw [hd2, ht2]; simpa [t1, t0, setKvarHOLFinite, setGlobalHOLFinite, setVarHOLFinite] using hfree
    simp only [Free] at hfr ⊢
    rw [rd, rt]; simpa [emptyLocalsHOLFinite] using hfr
  · intro x w hx
    by_cases hin : ∃ j, j < 4 ∧ x = at8 p0 j
    · obtain ⟨j, hj, rfl⟩ := hin
      simp only [at8]
      have : j * 8 < 32 := by omega
      bv_omega
    · have hx' : h x = some w := by
        rw [← extSeq_other p0 [4, (ConLeche.Expr.app f a).data.toBitVec, q, r] 0 h x (fun j hj e =>
          hin ⟨j, by simpa using hj, by simpa using e⟩)]
        exact hx
      have := hi.2.2 x w hx'
      bv_omega
  · have g0 := get 0 (by decide); have g1 := get 1 (by decide)
    have g2 := get 2 (by decide); have g3 := get 3 (by decide)
    simp [at8] at g0 g1 g2 g3
    exact .app hnz g0 g1 g2 g3 (exprAt_mono hs2 hF) (exprAt_mono hs2 hA)
  · unfold appTail; rw [rg]; simp [emptyLocalsHOLFinite, hg2, t1, setKvarHOLFinite, setGlobalHOLFinite, FUPDATE]

def nFd := ofString "fd"
def nAd := ofString "ad"

open ConPanqueque.AppData ConPanqueque.Hash in
/-- con-leche's `Expr.app f a` as a Pancake node constructor. -/
def mkAppBody : ProgHOL 64 :=
  .dec nFd .one (.load .one (.op .add [.var .local nF, .const 8]))
    (.dec nAd .one (.load .one (.op .add [.var .local nA, .const 8]))
      (.dec nD .one (appDataExp (.var .local nFd) (.var .local nAd))
        (.dec nTg .one (.const 4) appTail)))

open ConPanqueque.AppData ConPanqueque.Hash in
theorem mkAppBody_spec {σ : Type} (ra : RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ) (h : Heap)
    (p0 q r : BitVec 64) (f a : ConLeche.Expr)
    (hf : t.locals.lookup nF = some (.val (.word q)))
    (ha : t.locals.lookup nA = some (.val (.word r)))
    (hhp : t.globals.lookup nHp = some (.val (.word p0)))
    (hi : ArenaInv t h p0) (hfit : ¬ t.topAddr - p0 < 32) (hnz : p0 ≠ 0)
    (hF : ExprAt h q f) (hA : ExprAt h r a) :
    ∃ h', (evaluateHOLFiniteState t mkAppBody).1 = some (.returned (.val (.word p0))) ∧
      ArenaInv (evaluateHOLFiniteState t mkAppBody).2 h' (p0 + 32) ∧ Sub h h' ∧ ExprAt h' p0 (.app f a) ∧
      (evaluateHOLFiniteState t mkAppBody).2.globals.lookup nHp = some (.val (.word (p0 + 32))) := by
  obtain ⟨_, hf8⟩ := exprAt_data hF
  obtain ⟨_, ha8⟩ := exprAt_data hA
  obtain ⟨df, mf⟩ := hi.1 _ _ hf8
  obtain ⟨da, ma⟩ := hi.1 _ _ ha8
  -- the four declared locals
  let t1 := setVarHOLFinite nFd (.val (.word f.data.toBitVec)) t
  let t2 := setVarHOLFinite nAd (.val (.word a.data.toBitVec)) t1
  let t3 := setVarHOLFinite nD (.val (.word (ConLeche.Expr.app f a).data.toBitVec)) t2
  let t4 := setVarHOLFinite nTg (.val (.word 4)) t3
  have s1 : t1.memory = t.memory ∧ t1.memaddrs = t.memaddrs ∧ t1.globals = t.globals ∧ t1.topAddr = t.topAddr :=
    ⟨rfl, rfl, rfl, rfl⟩
  have lf : ∀ n, n ≠ nFd → n ≠ nAd → n ≠ nD → n ≠ nTg → t4.locals.lookup n = t.locals.lookup n := by
    intro n h1 h2 h3 h4
    simp only [t4, t3, t2, t1]
    rw [lookup_setVar_other _ _ h4, lookup_setVar_other _ _ h3, lookup_setVar_other _ _ h2,
      lookup_setVar_other _ _ h1]
  have ev1 : @evalHOLExact 64 σ _ t.toExact (fun x => Classical.propDecidable (t.memaddrs x))
      (.load .one (.op .add [.var .local nF, .const 8])) = some (.val (.word f.data.toBitVec)) := by
    rw [eval_load_word t _ (q + 8) (by simp [evalHOLExact, evalListHOLExact, hf, wordOpHOL, wordOp,
      valueIsWord, valueWord]) df, mf]
  have ev2 : @evalHOLExact 64 σ _ t1.toExact (fun x => Classical.propDecidable (t1.memaddrs x))
      (.load .one (.op .add [.var .local nA, .const 8])) = some (.val (.word a.data.toBitVec)) := by
    have hat1 : t1.locals.lookup nA = some (.val (.word r)) := by
      simp only [t1]; rw [lookup_setVar_other _ _ (by decide)]; exact ha
    rw [eval_load_word t1 _ (r + 8) (by simp [evalHOLExact, evalListHOLExact, hat1, wordOpHOL, wordOp,
      valueIsWord, valueWord]) da]
    simp [t1, setVarHOLFinite]; exact ma
  have ev3 : @evalHOLExact 64 σ _ t2.toExact (fun x => Classical.propDecidable (t2.memaddrs x))
      (appDataExp (.var .local nFd) (.var .local nAd)) =
      some (.val (.word (ConLeche.Expr.app f a).data.toBitVec)) := by
    apply eval_appDataExp ra t2
    · simp only [evalHOLExact, t2]; rw [lookup_setVar_other _ _ (by decide)]; simp [t1]
    · simp [evalHOLExact, t2]
  obtain ⟨h', r1, ⟨m1, m2, m3⟩, sub, ex, g⟩ :=
    appTail_spec t4 h p0 q r f a (by simp [t4]) (by simp only [t4]; rw [lookup_setVar_other _ _ (by decide)]; simp [t3])
      (by rw [lf nF (by decide) (by decide) (by decide) (by decide)]; exact hf)
      (by rw [lf nA (by decide) (by decide) (by decide) (by decide)]; exact ha)
      (by simpa [t4, t3, t2, t1, setVarHOLFinite] using hhp)
      ⟨inMem_of_eq rfl rfl hi.1, by simpa [t4, t3, t2, t1, setVarHOLFinite, Free] using hi.2.1, hi.2.2⟩
      (by simpa [t4, t3, t2, t1, setVarHOLFinite] using hfit) hnz hF hA
  -- pass the result out through the four declarations
  obtain ⟨a4, b4, c4, d4, e4⟩ := dec_word t3 nTg (.const 4) 4 appTail (by simp [evalHOLExact])
  obtain ⟨a3, b3, c3, d3, e3⟩ := dec_word t2 nD _ _ (.dec nTg .one (.const 4) appTail) ev3
  obtain ⟨a2, b2, c2, d2, e2⟩ := dec_word t1 nAd _ _ _ ev2
  obtain ⟨a1, b1, c1, d1, e1⟩ := dec_word t nFd _ _ _ ev1
  refine ⟨h', ?_, ⟨?_, ?_, ?_⟩, sub, ex, ?_⟩
  · unfold mkAppBody; rw [a1, a2, a3, a4]; exact r1
  · unfold mkAppBody
    exact inMem_of_eq (by rw [b1, b2, b3, b4]) (by rw [c1, c2, c3, c4]) m1
  · unfold mkAppBody
    simp only [Free] at m2 ⊢; rw [c1, c2, c3, c4, e1, e2, e3, e4]; exact m2
  · exact m3
  · unfold mkAppBody; rw [d1, d2, d3, d4]; exact g
