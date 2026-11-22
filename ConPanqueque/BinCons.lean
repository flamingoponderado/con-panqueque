import ConPanqueque.AppData
import ConPanqueque.ExprCons
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Hash ConPanqueque.DataWord ConPanqueque.AppData ConPanqueque.ExprCons
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic ConPanqueque.Alloc

/-!
# Binder node constructors: `Expr.lam`, `Expr.forallE`

The data word of a binder (`bin_data_bv`) differs from `app`'s in its hash tag
and the saturating decrement of the body's bvar range (`satPred`, as
`x - [x ≠ 0]·[x ≠ 32767]`). `tail4_spec` generalizes `appTail_spec` to any tag
and data value; `mkBinBody_spec` is the generic binder constructor, with
`mkLamBody_spec` and `mkForallEBody_spec` its instances.
-/

namespace ConPanqueque.BinCons

theorem satPred_bv (x : UInt64) :
    (ConLeche.satPred x).toBitVec =
      x.toBitVec - (if x.toBitVec ≠ 0 then 1 else 0) * (if x.toBitVec ≠ 32767#64 then 1 else 0) := by
  unfold ConLeche.satPred
  by_cases h1 : x = 32767
  · subst h1; decide
  · by_cases h0 : x = 0
    · subst h0; decide
    · have a1 : x.toBitVec ≠ 32767#64 := fun e => h1 (UInt64.toBitVec_inj.mp (by simpa using e))
      have a0 : x.toBitVec ≠ 0 := fun e => h0 (UInt64.toBitVec_inj.mp (by simpa using e))
      simp [h1, h0, a1]; exact a0

def satPredW (x : BitVec 64) : BitVec 64 :=
  x - (if x ≠ 0 then 1 else 0) * (if x ≠ 32767#64 then 1 else 0)

theorem bvarOf_satPred_bv (w : UInt64) :
    (ConLeche.satPred (ConLeche.bvarOfData w)).toBitVec = satPredW (bvF w.toBitVec) := by
  rw [satPred_bv, bvarOfData_bv]; rfl

/-- The data word of a two-child node with hash tag `c`; `pred` applies `satPred`
to the second child's bvar range (binders). -/
theorem bin_data_bv (ra : RuntimeAssumptions) (ty b : ConLeche.Expr) :
    (ConLeche.Expr.lam ty b).data.toBitVec =
      (((leanMixHash 19 (leanMixHash (ConLeche.hashOfData ty.data) (ConLeche.hashOfData b.data))).toBitVec
          <<< 32) >>> 32) * 4294967296#64 +
      maxW (bvF ty.data.toBitVec) (satPredW (bvF b.data.toBitVec)) * 65536#64 +
      maxW (fvF ty.data.toBitVec) (fvF b.data.toBitVec) * 2#64 +
      maxW (lpF ty.data.toBitVec) (lpF b.data.toBitVec) ∧
    (ConLeche.Expr.forallE ty b).data.toBitVec =
      (((leanMixHash 23 (leanMixHash (ConLeche.hashOfData ty.data) (ConLeche.hashOfData b.data))).toBitVec
          <<< 32) >>> 32) * 4294967296#64 +
      maxW (bvF ty.data.toBitVec) (satPredW (bvF b.data.toBitVec)) * 65536#64 +
      maxW (fvF ty.data.toBitVec) (fvF b.data.toBitVec) * 2#64 +
      maxW (lpF ty.data.toBitVec) (lpF b.data.toBitVec) := by
  constructor <;>
  · simp only [ConLeche.Expr.data, packData_bv, hash32_bv, ra.mixHash, max_bv, bvarOfData_bv, fvarOfData_bv]
    rw [or_bit, lpOfData_bv, lpOfData_bv, satPred_bv]
    simp [maxW, bvF, fvF, lpF, satPredW, bvarOfData_bv]

/-- `appTail` for any tag and data values: the four cells and the arena facts. -/
theorem tail4_spec {σ : Type} (t : PanSemStateFiniteExact 64 σ) (h : Heap) (p0 q r : BitVec 64)
    (tv dv : BitVec 64)
    (htg : t.locals.lookup nTg = some (.val (.word tv)))
    (hd : t.locals.lookup nD = some (.val (.word dv)))
    (hf : t.locals.lookup nF = some (.val (.word q)))
    (ha : t.locals.lookup nA = some (.val (.word r)))
    (hhp : t.globals.lookup nHp = some (.val (.word p0)))
    (hi : ArenaInv t h p0) (hfit : ¬ t.topAddr - p0 < 32) :
    ∃ h', (evaluateHOLFiniteState t appTail).1 = some (.returned (.val (.word p0))) ∧
      ArenaInv (evaluateHOLFiniteState t appTail).2 h' (p0 + 32) ∧ Sub h h' ∧
      (h' p0 = some (.word tv) ∧ h' (p0 + 8) = some (.word dv) ∧ h' (p0 + 16) = some (.word q) ∧
        h' (p0 + 24) = some (.word r)) ∧
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
    storeSeq_spec nP p0 [nTg, nD, nF, nA] [tv, dv, q, r] 0 t1 h rfl lp1
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
  let h' := extSeq h p0 [tv, dv, q, r] 0
  have get : ∀ j (hj : j < 4), h' (at8 p0 j) =
      some (.word ([tv, dv, q, r][j]'(by simpa using hj))) := by
    intro j hj
    have := extSeq_get p0 [tv, dv, q, r] 0 h j (by simpa using hj)
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
        rw [← extSeq_other p0 [tv, dv, q, r] 0 h x (fun j hj e =>
          hin ⟨j, by simpa using hj, by simpa using e⟩)]
        exact hx
      have := hi.2.2 x w hx'
      bv_omega
  · have g0 := get 0 (by decide); have g1 := get 1 (by decide)
    have g2 := get 2 (by decide); have g3 := get 3 (by decide)
    simp [at8] at g0 g1 g2 g3
    exact ⟨g0, g1, g2, g3⟩
  · unfold appTail; rw [rg]; simp [emptyLocalsHOLFinite, hg2, t1, setKvarHOLFinite, setGlobalHOLFinite, FUPDATE]


def satPredE (e : ExpHOL 64) : ExpHOL 64 :=
  .op .sub [e, .panop .mul [.cmp .notEqual e (.const 0), .cmp .notEqual e (.const 32767#64)]]

/-- The data word of a binder node with hash tag `c`, from the children's data words. -/
def binDataExp (c : BitVec 64) (fd ad : ExpHOL 64) : ExpHOL 64 :=
  .op .add [.panop .mul [shr (shl (mixExp (.const c) (mixExp (shr fd 32) (shr ad 32))) 32) 32, .const 4294967296#64],
    .panop .mul [maxE (shr (shl fd 33) 49) (satPredE (shr (shl ad 33) 49)), .const 65536#64],
    .panop .mul [maxE (shr (shl fd 48) 49) (shr (shl ad 48) 49), .const 2#64],
    maxE (shr (shl fd 63) 63) (shr (shl ad 63) 63)]

theorem eval_binDataExp {σ : Type} (s : PanSemStateFiniteExact 64 σ) (c : UInt64)
    (fdE adE : ExpHOL 64) (f a : ConLeche.Expr)
    (hf : @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) fdE =
      some (.val (.word f.data.toBitVec)))
    (ha : @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) adE =
      some (.val (.word a.data.toBitVec))) :
    @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x)) (binDataExp c.toBitVec fdE adE) =
      some (.val (.word ((((leanMixHash c (leanMixHash (ConLeche.hashOfData f.data)
          (ConLeche.hashOfData a.data))).toBitVec <<< 32) >>> 32) * 4294967296#64 +
        maxW (bvF f.data.toBitVec) (satPredW (bvF a.data.toBitVec)) * 65536#64 +
        maxW (fvF f.data.toBitVec) (fvF a.data.toBitVec) * 2#64 +
        maxW (lpF f.data.toBitVec) (lpF a.data.toBitVec)))) := by
  have hi := eval_mixExp s (shr fdE 32) (shr adE 32) (ConLeche.hashOfData f.data) (ConLeche.hashOfData a.data)
    (by simp [shr, evalHOLExact, hf, wordShiftHOL, hashOfData_bv])
    (by simp [shr, evalHOLExact, ha, wordShiftHOL, hashOfData_bv])
  have ho : @evalHOLExact 64 σ _ s.toExact (fun x => Classical.propDecidable (s.memaddrs x))
      (mixExp (.const c.toBitVec) (mixExp (.shift .lsr fdE (.const 32#64)) (.shift .lsr adE (.const 32#64)))) =
      some (.val (.word (leanMixHash c (leanMixHash (ConLeche.hashOfData f.data)
        (ConLeche.hashOfData a.data))).toBitVec)) :=
    eval_mixExp s (.const c.toBitVec) _ c _ (by simp [evalHOLExact]) hi
  simp [binDataExp, satPredE, shr, shl, maxE, evalHOLExact, evalListHOLExact, ho, hf, ha, wordShiftHOL, wordOpHOL,
    wordOp, valueIsWord, valueWord, panOpHOL, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, maxW, bvF, fvF, lpF,
    satPredW, BitVec.add_assoc]

/-- A binder-node constructor: hash tag `c`, node tag `tag`. -/
def mkBinBody (c tag : BitVec 64) : ProgHOL 64 :=
  .dec nFd .one (.load .one (.op .add [.var .local nF, .const 8]))
    (.dec nAd .one (.load .one (.op .add [.var .local nA, .const 8]))
      (.dec nD .one (binDataExp c (.var .local nFd) (.var .local nAd))
        (.dec nTg .one (.const tag) appTail)))

theorem mkBinBody_spec {σ : Type} (t : PanSemStateFiniteExact 64 σ) (h : Heap)
    (p0 q r : BitVec 64) (f a : ConLeche.Expr) (c : UInt64) (tag : BitVec 64)
    (hf : t.locals.lookup nF = some (.val (.word q)))
    (ha : t.locals.lookup nA = some (.val (.word r)))
    (hhp : t.globals.lookup nHp = some (.val (.word p0)))
    (hi : ArenaInv t h p0) (hfit : ¬ t.topAddr - p0 < 32)
    (hF : ExprAt h q f) (hA : ExprAt h r a) :
    let dv := (((leanMixHash c (leanMixHash (ConLeche.hashOfData f.data)
          (ConLeche.hashOfData a.data))).toBitVec <<< 32) >>> 32) * 4294967296#64 +
        maxW (bvF f.data.toBitVec) (satPredW (bvF a.data.toBitVec)) * 65536#64 +
        maxW (fvF f.data.toBitVec) (fvF a.data.toBitVec) * 2#64 +
        maxW (lpF f.data.toBitVec) (lpF a.data.toBitVec)
    ∃ h', (evaluateHOLFiniteState t (mkBinBody c.toBitVec tag)).1 = some (.returned (.val (.word p0))) ∧
      ArenaInv (evaluateHOLFiniteState t (mkBinBody c.toBitVec tag)).2 h' (p0 + 32) ∧ Sub h h' ∧
      (h' p0 = some (.word tag) ∧ h' (p0 + 8) = some (.word dv) ∧ h' (p0 + 16) = some (.word q) ∧
        h' (p0 + 24) = some (.word r)) ∧
      (evaluateHOLFiniteState t (mkBinBody c.toBitVec tag)).2.globals.lookup nHp = some (.val (.word (p0 + 32))) := by
  intro dv
  obtain ⟨_, hf8⟩ := exprAt_data hF
  obtain ⟨_, ha8⟩ := exprAt_data hA
  obtain ⟨df, mf⟩ := hi.1 _ _ hf8
  obtain ⟨da, ma⟩ := hi.1 _ _ ha8
  -- the four declared locals
  let t1 := setVarHOLFinite nFd (.val (.word f.data.toBitVec)) t
  let t2 := setVarHOLFinite nAd (.val (.word a.data.toBitVec)) t1
  let t3 := setVarHOLFinite nD (.val (.word dv)) t2
  let t4 := setVarHOLFinite nTg (.val (.word tag)) t3
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
      (binDataExp c.toBitVec (.var .local nFd) (.var .local nAd)) =
      some (.val (.word dv)) := by
    apply eval_binDataExp t2
    · simp only [evalHOLExact, t2]; rw [lookup_setVar_other _ _ (by decide)]; simp [t1]
    · simp [evalHOLExact, t2]
  obtain ⟨h', r1, ⟨m1, m2, m3⟩, sub, ex, g⟩ :=
    tail4_spec t4 h p0 q r tag dv (by simp [t4]) (by simp only [t4]; rw [lookup_setVar_other _ _ (by decide)]; simp [t3])
      (by rw [lf nF (by decide) (by decide) (by decide) (by decide)]; exact hf)
      (by rw [lf nA (by decide) (by decide) (by decide) (by decide)]; exact ha)
      (by simpa [t4, t3, t2, t1, setVarHOLFinite] using hhp)
      ⟨inMem_of_eq rfl rfl hi.1, by simpa [t4, t3, t2, t1, setVarHOLFinite, Free] using hi.2.1, hi.2.2⟩
      (by simpa [t4, t3, t2, t1, setVarHOLFinite] using hfit)
  -- pass the result out through the four declarations
  obtain ⟨a4, b4, c4, d4, e4⟩ := dec_word t3 nTg (.const tag) tag appTail (by simp [evalHOLExact])
  obtain ⟨a3, b3, c3, d3, e3⟩ := dec_word t2 nD _ _ (.dec nTg .one (.const tag) appTail) ev3
  obtain ⟨a2, b2, c2, d2, e2⟩ := dec_word t1 nAd _ _ _ ev2
  obtain ⟨a1, b1, c1, d1, e1⟩ := dec_word t nFd _ _ _ ev1
  refine ⟨h', ?_, ⟨?_, ?_, ?_⟩, sub, ex, ?_⟩
  · unfold mkBinBody; rw [a1, a2, a3, a4]; exact r1
  · unfold mkBinBody
    exact inMem_of_eq (by rw [b1, b2, b3, b4]) (by rw [c1, c2, c3, c4]) m1
  · unfold mkBinBody
    simp only [Free] at m2 ⊢; rw [c1, c2, c3, c4, e1, e2, e3, e4]; exact m2
  · exact m3
  · unfold mkBinBody; rw [d1, d2, d3, d4]; exact g


/-- con-leche's `Expr.lam ty b` as a Pancake node constructor (hash tag 19, node tag 5). -/
def mkLamBody : ProgHOL 64 := mkBinBody (19 : UInt64).toBitVec 5
/-- con-leche's `Expr.forallE ty b` (hash tag 23, node tag 6). -/
def mkForallEBody : ProgHOL 64 := mkBinBody (23 : UInt64).toBitVec 6

theorem mkLamBody_spec {σ : Type} (ra : RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ) (h : Heap)
    (p0 q r : BitVec 64) (ty b : ConLeche.Expr)
    (hf : t.locals.lookup nF = some (.val (.word q))) (ha : t.locals.lookup nA = some (.val (.word r)))
    (hhp : t.globals.lookup nHp = some (.val (.word p0)))
    (hi : ArenaInv t h p0) (hfit : ¬ t.topAddr - p0 < 32) (hnz : p0 ≠ 0)
    (hT : ExprAt h q ty) (hB : ExprAt h r b) :
    ∃ h', (evaluateHOLFiniteState t mkLamBody).1 = some (.returned (.val (.word p0))) ∧
      ArenaInv (evaluateHOLFiniteState t mkLamBody).2 h' (p0 + 32) ∧ Sub h h' ∧ ExprAt h' p0 (.lam ty b) ∧
      (evaluateHOLFiniteState t mkLamBody).2.globals.lookup nHp = some (.val (.word (p0 + 32))) := by
  obtain ⟨h', r1, ai, sub, ⟨c0, c1, c2, c3⟩, g⟩ := mkBinBody_spec t h p0 q r ty b 19 5 hf ha hhp hi hfit hT hB
  refine ⟨h', r1, ai, sub, .lam hnz c0 (by rw [(bin_data_bv ra ty b).1]; exact c1) c2 c3
    (exprAt_mono sub hT) (exprAt_mono sub hB), g⟩

theorem mkForallEBody_spec {σ : Type} (ra : RuntimeAssumptions) (t : PanSemStateFiniteExact 64 σ) (h : Heap)
    (p0 q r : BitVec 64) (ty b : ConLeche.Expr)
    (hf : t.locals.lookup nF = some (.val (.word q))) (ha : t.locals.lookup nA = some (.val (.word r)))
    (hhp : t.globals.lookup nHp = some (.val (.word p0)))
    (hi : ArenaInv t h p0) (hfit : ¬ t.topAddr - p0 < 32) (hnz : p0 ≠ 0)
    (hT : ExprAt h q ty) (hB : ExprAt h r b) :
    ∃ h', (evaluateHOLFiniteState t mkForallEBody).1 = some (.returned (.val (.word p0))) ∧
      ArenaInv (evaluateHOLFiniteState t mkForallEBody).2 h' (p0 + 32) ∧ Sub h h' ∧ ExprAt h' p0 (.forallE ty b) ∧
      (evaluateHOLFiniteState t mkForallEBody).2.globals.lookup nHp = some (.val (.word (p0 + 32))) := by
  obtain ⟨h', r1, ai, sub, ⟨c0, c1, c2, c3⟩, g⟩ := mkBinBody_spec t h p0 q r ty b 23 6 hf ha hhp hi hfit hT hB
  refine ⟨h', r1, ai, sub, .forallE hnz c0 (by rw [(bin_data_bv ra ty b).2]; exact c1) c2 c3
    (exprAt_mono sub hT) (exprAt_mono sub hB), g⟩

end ConPanqueque.BinCons
