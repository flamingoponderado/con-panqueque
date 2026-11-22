import ConPanqueque.ExprCons
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Sep ConPanqueque.Rep ConPanqueque.Logic ConPanqueque.Alloc ConPanqueque.ExprCons

/-- Allocate `|xs|` words at the heap pointer, write the locals `xs`, return the block. -/
def tailN (xs : List MlS) : ProgHOL 64 :=
  .dec nP .one (.var .global nHp)
    (.seq (.assign .global nHp (.op .add [.var .global nHp, .const (BitVec.ofNat 64 (8 * xs.length))]))
      (.seq (storeSeq nP xs 0) (.return (.var .local nP))))

theorem tailN_spec {σ : Type} (t : PanSemStateFiniteExact 64 σ) (h : Heap) (p0 : BitVec 64)
    (xs : List MlS) (vs : List (BitVec 64)) (hlen : xs.length = vs.length) (hnp : nP ∉ xs)
    (hsmall : 8 * xs.length < 2 ^ 64)
    (hx : ∀ j (hj : j < xs.length), t.locals.lookup xs[j] = some (.val (.word (vs[j]'(hlen ▸ hj)))))
    (hhp : t.globals.lookup nHp = some (.val (.word p0)))
    (hi : ArenaInv t h p0) (hfit : ¬ t.topAddr - p0 < BitVec.ofNat 64 (8 * xs.length)) :
    ∃ h', (evaluateHOLFiniteState t (tailN xs)).1 = some (.returned (.val (.word p0))) ∧
      ArenaInv (evaluateHOLFiniteState t (tailN xs)).2 h' (p0 + BitVec.ofNat 64 (8 * xs.length)) ∧ Sub h h' ∧
      (∀ j (hj : j < xs.length), h' (at8 p0 j) = some (.word (vs[j]'(hlen ▸ hj)))) ∧
      (evaluateHOLFiniteState t (tailN xs)).2.globals.lookup nHp =
        some (.val (.word (p0 + BitVec.ofNat 64 (8 * xs.length)))) := by
  obtain ⟨hfresh, hdist, hfree, hb⟩ := blockN xs.length hi hfit hsmall
  let n8 := BitVec.ofNat 64 (8 * xs.length)
  let t0 := setVarHOLFinite nP (.val (.word p0)) t
  let t1 := setKvarHOLFinite .global nHp (.val (.word (p0 + n8))) t0
  have e1 : evaluateHOLFiniteState t0 (.assign .global nHp (.op .add [.var .global nHp, .const n8])) =
      (none, t1) := by
    apply assign_ok
    · simp [evalHOLExact, evalListHOLExact, t0, setVarHOLFinite, hhp, wordOpHOL, wordOp, valueIsWord, valueWord]
    · simp [isValidValueHOLFinite, lookupKvarHOLFinite, t0, setVarHOLFinite, hhp, shapeOfHOLExact, shapeEqHOL]
  have l1 : ∀ n, n ≠ nP → t1.locals.lookup n = t.locals.lookup n := by
    intro n hn; simp only [t1, t0, setKvarHOLFinite, setGlobalHOLFinite]; exact lookup_setVar_other _ _ hn
  have lp1 : t1.locals.lookup nP = some (.val (.word p0)) := by
    simp [t1, t0, setKvarHOLFinite, setGlobalHOLFinite]
  obtain ⟨t2, ev2, hl2, hd2, ht2, hg2, hm2, hs2⟩ :=
    storeSeq_spec nP p0 xs vs 0 t1 h hlen lp1
      (fun j hj => by
        have hne : xs[j] ≠ nP := fun e => hnp (e ▸ List.getElem_mem hj)
        rw [l1 _ hne]; exact hx j hj)
      (inMem_of_eq (by simp [t1, t0, setKvarHOLFinite, setGlobalHOLFinite, setVarHOLFinite])
        (by simp [t1, t0, setKvarHOLFinite, setGlobalHOLFinite, setVarHOLFinite]) hi.1)
      (fun j hj => by
        obtain ⟨x, y⟩ := hfresh j hj
        exact ⟨by simpa [t1, t0, setKvarHOLFinite, setGlobalHOLFinite, setVarHOLFinite] using x, by simpa using y⟩)
      (fun j k hj hk hjk => by simpa using hdist j k hj hk hjk)
  have lp2 : t2.locals.lookup nP = some (.val (.word p0)) := by rw [hl2]; exact lp1
  have eret : evaluateHOLFiniteState t2 (.return (.var .local nP)) =
      (some (.returned (.val (.word p0))), emptyLocalsHOLFinite t2) := by
    rw [evaluateHOLFiniteState_eq_evaluate_def]; simp [evalHOLExact, lp2, shapeOfHOLExact]
  have einner : evaluateHOLFiniteState (setVarHOLFinite nP (.val (.word p0)) t)
      (.seq (.assign .global nHp (.op .add [.var .global nHp, .const n8]))
        (.seq (storeSeq nP xs 0) (.return (.var .local nP)))) =
      (some (.returned (.val (.word p0))), emptyLocalsHOLFinite t2) := by
    rw [seq_normal _ e1, seq_normal _ ev2, eret]
  obtain ⟨r1, rm, rd, rg, rt⟩ := dec_word t nP (.var .global nHp) p0 _ (by simp [evalHOLExact, hhp])
  rw [einner] at r1 rm rd rg rt
  unfold tailN
  refine ⟨extSeq h p0 vs 0, ?_, ⟨?_, ?_, ?_⟩, hs2, ?_, ?_⟩
  · exact r1
  · exact inMem_of_eq (by rw [rm]; simp [emptyLocalsHOLFinite]) (by rw [rd]; simp [emptyLocalsHOLFinite]) hm2
  · have hfr : Free t2 (p0 + n8) := by
      simp only [Free] at hfree ⊢
      rw [hd2, ht2]; simpa [t1, t0, setKvarHOLFinite, setGlobalHOLFinite, setVarHOLFinite] using hfree
    simp only [Free] at hfr ⊢
    rw [rd, rt]; simpa [emptyLocalsHOLFinite] using hfr
  · have ht : t.topAddr.toNat < 2 ^ 64 := t.topAddr.isLt
    intro x w hx
    by_cases hin : ∃ j, j < xs.length ∧ x = at8 p0 j
    · obtain ⟨j, hj, rfl⟩ := hin
      simp only [at8]
      have : (BitVec.ofNat 64 (8 * xs.length)).toNat = 8 * xs.length := by simp; omega
      bv_omega
    · have hx' : h x = some w := by
        rw [← extSeq_other p0 vs 0 h x (fun j hj e => hin ⟨j, by omega, by simpa using e⟩)]
        exact hx
      have := hi.2.2 x w hx'
      have : (BitVec.ofNat 64 (8 * xs.length)).toNat = 8 * xs.length := by simp; omega
      bv_omega
  · intro j hj
    have := extSeq_get p0 vs 0 h j (by omega)
      (fun j k hj hk hjk => by simpa using hdist j k (by omega) (by omega) hjk)
    simpa using this
  · rw [rg]; simp [emptyLocalsHOLFinite, hg2, t1, setKvarHOLFinite, setGlobalHOLFinite, FUPDATE, n8]
