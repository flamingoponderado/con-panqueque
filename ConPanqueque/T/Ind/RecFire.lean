import ConPanqueque.T.Ind.RecsRead

/-!
# How a recursor's rules fire (`recFire`), and the pieces it needs

`vlFill us o i`: the level list `us` copied into the value-heap block at `o` from position `i`. A heap store drops
the memory facts a view leaves, so the list is viewed again at each position.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG

def vlU := ofString "vl_u"
def vlD := ofString "vl_d"
def vlI := ofString "vl_i"
def vlX := ofString "vl_x"
def vlR := ofString "vl_r"
def fVlFill := ofString "vlFill"

def vlParams : List MlS := [vlU, vlD, vlI]
def vlLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, vlX, vlR]

def vlBody : ProgHOL 64 := prologue vlLocals
  (.seq (.assign .local lDh (vv vlU)) (.seq (.assign .local lFl (vv lFls)) (.seq lsViewP
  (.ite (.cmp .lower (vv vlI) (vv lRn))
    (.seq (.assign .local vlX (.load .one (.op .add [vv lRp, .shift .lsl (vv vlI) (.const 3)])))
    (.seq (.store (.op .add [vv vlD, .shift .lsl (.op .add [vv vlI, .const 1]) (.const 3)]) (vv vlX))
    (.seq (.call (some (some (.local, vlR), none)) fVlFill [vv vlU, vv vlD, .op .add [vv vlI, .const 1]])
      (.return (.const 0)))))
    (.return (.const 0))))))

def dpA := ofString "dp_a"
def dpD := ofString "dp_d"
def dpN := ofString "dp_n"
def dpI := ofString "dp_i"
def dpM := ofString "dp_m"
def dpX := ofString "dp_x"
def dpY := ofString "dp_y"
def dpR := ofString "dp_r"
def fDpFill := ofString "dpFill"

def dpParams : List MlS := [dpA, dpD, dpN, dpI, dpM]
def dpLocals : List MlS := [dpX, dpY, dpR]

/-- `exprDropVars n` over the args block at `dpA` (positions `i … m - 1`) into the block at `dpD`. -/
def dpBody : ProgHOL 64 := prologue dpLocals
  (.ite (.cmp .lower (vv dpI) (vv dpM))
    (.seq (.assign .local dpX (.load .one (.op .add [vv dpA, .shift .lsl (.op .add [vv dpI, .const 1]) (.const 3)])))
    (.seq (.call (some (some (.local, dpY), none)) fDropVars [vv dpN, vv dpX])
    (.seq (.store (.op .add [vv dpD, .shift .lsl (.op .add [vv dpI, .const 1]) (.const 3)]) (vv dpY))
    (.seq (.call (some (some (.local, dpR), none)) fDpFill [vv dpA, vv dpD, vv dpN, .op .add [vv dpI, .const 1], vv dpM])
      (.return (.const 0))))))
    (.return (.const 0)))

def fxTg := ofString "fx_tg"
def fxK := ofString "fx_k"
def fxMI := ofString "fx_mi"
def fxRP := ofString "fx_rp"
def fxT := ofString "fx_t"
def fxS := ofString "fx_s"
def fxSc := ofString "fx_sc"
def fxB := ofString "fx_b"
def fxDom := ofString "fx_dom"
def fxHd := ofString "fx_hd"
def fxUs := ofString "fx_us"
def fxN := ofString "fx_n"
def fxLv := ofString "fx_lv"
def fxA := ofString "fx_a"
def fxAl := ofString "fx_al"
def fxNI := ofString "fx_ni"
def fxM := ofString "fx_m"
def fxPs := ofString "fx_ps"
def fxX := ofString "fx_x"
def fxO := ofString "fx_o"
def fRecFire := ofString "recFire"

def fxParams : List MlS := [fxTg, fxK, fxMI, fxRP, fxT]
def fxLocals : List MlS := [lFl, lDh, lDt, lDg, lDi, lRp, lRn, fxS, fxSc, fxB, fxDom, fxHd, fxUs, fxN, fxLv, fxA, fxAl,
  fxNI, fxM, fxPs, fxX, fxO]

def fxPlain (C : Ctx) : ProgHOL 64 :=
  alloc6 C fxO (.const 0) (.const 0) (.const 0) (.const 0) (.const 0) (.const 0) (.return (vv fxO))

/-- The nested arm once `fxDom` (the major's domain) and `fxUs` (its head's levels) are known. -/
def fxNested (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local lDh (vv fxUs)) (.seq (.assign .local lFl (vv lFls)) (.seq lsViewP
  (.seq (.assign .local fxN (vv lRn))
  (guardP fxN 58
  (allocP C fxLv (.shift .lsl (.op .add [vv fxN, .const 1]) (.const 3))
  (.seq (.store (vv fxLv) (vv fxN))
  (.seq (.call (some (some (.local, fxX), none)) fVlFill [vv fxUs, vv fxLv, .const 0])
  (.seq (.call (some (some (.local, fxA), none)) fGaa [.const (BitVec.ofNat 64 coreWalkFuel), vv fxDom])
  (.seq (.assign .local fxAl (.load .one (vv fxA)))
  (.seq (.call (some (some (.local, fxNI), none)) fTSub [vv fxMI, vv fxRP])
  (.seq (.call (some (some (.local, fxM), none)) fTSub [vv fxAl, vv fxNI])
  (allocP C fxPs (.shift .lsl (.op .add [vv fxM, .const 1]) (.const 3))
  (.seq (.store (vv fxPs) (vv fxM))
  (.seq (.call (some (some (.local, fxX), none)) fDpFill [vv fxA, vv fxPs, vv fxNI, .const 0, vv fxM])
  (alloc6 C fxO (.const 1) (vv fxLv) (vv fxPs) (.const 0) (.const 0) (.const 0) (.return (vv fxO)))))))))))))))))

def fxBody (C : Ctx) : ProgHOL 64 := prologue fxLocals
  (.ite (.cmp .lower (vv fxTg) (vv fxK)) (fxPlain C)
  (.seq (.call (some (some (.local, fxS), none)) fStripPis [vv fxMI, vv fxT])
  (.ite (.cmp .equal (vv fxS) (.const 0)) (fxPlain C)
  (.seq (.assign .local fxSc (.load .one (vv fxS)))
  (.seq (.assign .local fxB (.load .one (.op .add [vv fxS, .shift .lsl (vv fxSc) (.const 3)])))
  (viewOf fxB
    (.ite (veEqC lDg 6)
      (.seq (.assign .local fxDom (.load .one (.op .add [vv lRp, .const 0])))
      (.seq (.call (some (some (.local, fxHd), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv fxDom])
      (viewOf fxHd
        (.ite (veEqC lDg 3)
          (.seq (.assign .local fxUs (.load .one (.op .add [vv lRp, .const 8]))) (fxNested C))
          (fxPlain C)))))
      (fxPlain C))))))))

section
variable {σ : Type}

/-- The level list's words from position `i` on, past the frozen prefix `Hc`. -/
def PostVL (C : Ctx) (Hc : List (BitVec 64)) (o : Nat) (vl : List LIdx) (i : Nat) (_ : Unit) (_ : BitVec 64)
    (s' : AState) (st : PState σ) : Prop :=
  ∃ H', Hc <+: H' ∧ SR (ctxH C H') s' st ∧ ∀ j (hj : j < vl.length), i ≤ j → H'[o + 1 + j]? = some (Enc.idxW vl[j])

theorem postVL_locals (C : Ctx) (Hc : List (BitVec 64)) (o : Nat) (vl : List LIdx) (i : Nat) :
    ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostVL C Hc o vl i a w s' st → PostVL C Hc o vl i a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h⟩

theorem vl_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ vlLocals → (ctxEnv C ++ vlParams.zip vals).get x = none :=
  Knot.params_none C vlLocals vlParams vals (by decide) (by decide)

/-- **`vlFill`** from position `i`. -/
theorem vl_spec (C : Ctx) (hok : CtxOK C)
    (hcode : C.code.lookup fVlFill = some (vlParams.map (fun p => (p, ShapeHOL.one)), vlBody, .one))
    (us : LsIdx) (vl : List LIdx) (o : Nat) :
    ∀ k i (H Hc : List (BitVec 64)) (s : AState), vl.length - i = k → i ≤ vl.length →
      s.store.lss.view us = some vl → Hc.length ≤ o + 1 + i → Hc <+: H → o + 1 + vl.length ≤ H.length →
      SpecR (Pre (σ := σ) (ctxH C H) s (vlParams.zip [Enc.idxW us, cellA C o, BitVec.ofNat 64 i])) vlBody s
        (pure ()) (PostVL C Hc o vl i) := by
  intro k
  induction k with
  | zero =>
    intro i H Hc s hk hi hv hHc hp hl
    refine specR_prologue (postVL_locals _ _ _ _ _) (vl_none _ _) ?_
    refine specR_assignI lDh (vv vlU) (Enc.idxW us) (by decide) (by simp +decide [sev, Env.get, vlParams, ctxEnv]) ?_
    refine specR_assignI lFl (vv lFls) (ctxH C H).FLs (by decide)
      (by simp +decide [Env.get_cons, Env.get, vlParams, ctxEnv] <;> rfl) ?_
    refine specR_lsviewPI (C := ctxH C H) us (by simp) (by simp +decide [Env.get_cons] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, vlParams, ctxEnv] <;> rfl) (by decide) (fun vl' P hv' htl hlenl => ?_)
    rw [hv] at hv'; cases hv'
    simp only [List.length_map] at hlenl
    refine specR_ifI _ 0 (by
        rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 i) (BitVec.ofNat 64 vl.length)
          (by simp +decide [sev, Env.get_cons, Env.get, vlParams, ctxEnv]) (by simp [sev, Env.get_cons]),
          wcL _ _ (by omega) (by omega)]; simp; omega) (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, hp, sr_of_eq ht.sr rfl rfl rfl rfl, fun j hj hij => by omega⟩)
  | succ k ih =>
    intro i H Hc s hk hi hv hHc hp hl
    refine specR_prologue (postVL_locals _ _ _ _ _) (vl_none _ _) ?_
    refine specR_assignI lDh (vv vlU) (Enc.idxW us) (by decide) (by simp +decide [sev, Env.get, vlParams, ctxEnv]) ?_
    refine specR_assignI lFl (vv lFls) (ctxH C H).FLs (by decide)
      (by simp +decide [Env.get_cons, Env.get, vlParams, ctxEnv] <;> rfl) ?_
    refine specR_lsviewPI (C := ctxH C H) us (by simp) (by simp +decide [Env.get_cons] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, vlParams, ctxEnv] <;> rfl) (by decide) (fun vl' P hv' htl hlenl => ?_)
    rw [hv] at hv'; cases hv'
    simp only [List.length_map] at hlenl
    have hil : i < vl.length := by omega
    refine specR_ifI _ 1 (by
        rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 i) (BitVec.ofNat 64 vl.length)
          (by simp +decide [sev, Env.get_cons, Env.get, vlParams, ctxEnv]) (by simp [sev, Env.get_cons]),
          wcL _ _ (by omega) (by omega)]; simp; omega) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_loadI' vlX _ (P + BitVec.ofNat 64 i <<< 3) (P + BitVec.ofNat 64 (8 * i)) (Enc.idxW vl[i]) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, vlParams, ctxEnv])
      (by apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega)
      (by have := wordsAt_get P (vl.map Enc.idxW) i (by simp; omega) []; simpa using this) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hj : o + 1 + i < (ctxH C H).H.length := by show o + 1 + i < H.length; omega
    refine specR_heapStoreI (ctxOK_H hok H) _ (vv vlX) (o + 1 + i) hj (Enc.idxW vl[i])
      (by
        simp +decide [sev, Env.get_cons, Env.get, vlParams, ctxEnv]
        show _ = cellA C (o + 1 + i)
        apply BitVec.eq_of_toNat_eq; simp [cellA, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega)
      (by simp [sev, Env.get_cons]) ?_
    change SpecR (Inv (ctxH C (H.set (o + 1 + i) (Enc.idxW vl[i]))) _ _ _ _) _ _ _ _
    generalize hB : H.set (o + 1 + i) (Enc.idxW vl[i]) = B
    have hBl : B.length = H.length := by rw [← hB]; simp
    have hBi : B[o + 1 + i]? = some (Enc.idxW vl[i]) := by rw [← hB, List.getElem?_set_self (by omega)]
    have hpB : Hc <+: B := by
      refine prefix_of_get? (by have := hp.length_le; omega) (fun j hj => ?_)
      rw [← hB, List.getElem?_set_ne (by omega), List.getElem?_eq_getElem hj]
      exact ConPanqueque.T.Decl.get_prefix (List.getElem?_eq_getElem hj) hp
    let Hc' := B.take (o + 2 + i)
    have hpc' : Hc' <+: B := List.take_prefix _ _
    have hHcc : Hc <+: Hc' := by
      refine prefix_of_get? (by simp [Hc']; have := hp.length_le; omega) (fun j hj => ?_)
      simp only [Hc']; rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj]
      exact ConPanqueque.T.Decl.get_prefix (List.getElem?_eq_getElem hj) hpB
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNIG (C := ctxH C B) vlR fVlFill vlParams [vv vlU, vv vlD, .op .add [vv vlI, .const 1]] vlBody
      [Enc.idxW us, cellA C o, BitVec.ofNat 64 (i + 1)] (by decide) rfl (by decide) hcode
      ⟨by simp +decide [sev, Env.get_cons, Env.get, vlParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, vlParams, ctxEnv],
        by
          show sev _ _ = _
          rw [sev_add2 _ _ _ (BitVec.ofNat 64 i) _ (by simp +decide [sev, Env.get_cons, Env.get, vlParams, ctxEnv]) rfl]
          exact congrArg some (word_add1_eq i), trivial⟩
      (fun a w s' st => (pure () : AM Unit) s = .ok (a, s') ∧ PostVL C Hc' o vl (i + 1) a w s' st)
      (fun a w s' H' => s' = s ∧ Hc' <+: H' ∧ ∀ j (hj : j < vl.length), i + 1 ≤ j → H'[o + 1 + j]? = some (Enc.idxW vl[j]))
      (fun a w s' st ⟨hr, H', hp', hs', hc'⟩ => by
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
        obtain ⟨-, rfl⟩ := hr
        exact ⟨H', ⟨rfl, hp', hc'⟩, hs'⟩)
      (fun u hu _ hlk => specR_run (fun w hw => by
        subst hw
        exact ih (i + 1) B Hc' s (by omega) (by omega) hv (by simp [Hc']; omega) hpc' (by omega) _
          (pre_of_lookups hu vlParams _ rfl hlk)))
      (fun a w s' H' ⟨hs', hp', hc'⟩ => ?_)
    subst hs'
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H', hHcc.trans hp', sr_of_eq ht.sr rfl rfl rfl rfl, fun j hj hij => by
      rcases Nat.lt_or_ge i j with h | h
      · exact hc' j hj (by omega)
      · have e : j = i := by omega
        subst e
        have := ConPanqueque.T.Decl.get_prefix (show Hc'[o + 1 + j]? = some (Enc.idxW vl[j]) by
          simp only [Hc']; rw [List.getElem?_take_of_lt (by omega)]; exact hBi) hp'
        exact this⟩)

def PostDP (C : Ctx) (Hc : List (BitVec 64)) (d i : Nat) (ps : List EIdx) (_ : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  ∃ H', Hc <+: H' ∧ SR (ctxH C H') s' st ∧ ∀ j (hj : j < ps.length), H'[d + 1 + i + j]? = some (Enc.idxW ps[j])

theorem postDP_locals (C : Ctx) (Hc : List (BitVec 64)) (d i : Nat) :
    ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostDP C Hc d i a w s' st → PostDP C Hc d i a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h⟩

theorem dp_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ dpLocals → (ctxEnv C ++ dpParams.zip vals).get x = none :=
  Knot.params_none C dpLocals dpParams vals (by decide) (by decide)

theorem take_drop_cons2 {α : Type} (l : List α) (m i : Nat) (hi : i < m) (hm : m ≤ l.length) :
    (l.take m).drop i = l[i]'(by omega) :: (l.take m).drop (i + 1) := by
  rw [List.drop_eq_getElem_cons (by simp; omega)]; simp

/-- **`dpFill`**: the dropped parameters from position `i`. -/
theorem dp_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcd : C.code.lookup fDropVars = some (dvParams.map (fun p => (p, ShapeHOL.one)), dvBody C, .one))
    (hcS : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one))
    (hcF : C.code.lookup fInst1F = some ([(pFu, .one), (pH, .one), (pV, .one), (pD, .one)], fastBody C, .one))
    (hcI : Codes C (body C))
    (hcode : C.code.lookup fDpFill = some (dpParams.map (fun p => (p, ShapeHOL.one)), dpBody, .one))
    (args : List EIdx) (oa d n m : Nat) (hn : n < 2 ^ 64) (hm : m ≤ args.length) (hdis : oa + 1 + args.length ≤ d) :
    ∀ k i (H Hc : List (BitVec 64)) (s : AState), m - i = k → i ≤ m → BlkAt H oa (args.map Enc.idxW) →
      Hc.length ≤ d + 1 + i → Hc <+: H → d + 1 + m ≤ H.length →
      SpecR (Pre (σ := σ) (ctxH C H) s (dpParams.zip [cellA C oa, cellA C d, BitVec.ofNat 64 n, BitVec.ofNat 64 i,
        BitVec.ofNat 64 m])) dpBody s (((args.take m).drop i).mapM (exprDropVars n)) (PostDP C Hc d i) := by
  intro k
  induction k with
  | zero =>
    intro i H Hc s hk hi hA hHc hp hl
    refine specR_prologue (postDP_locals _ _ _ _) (dp_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    refine specR_ifI _ 0 (by
        rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 i) (BitVec.ofNat 64 m)
          (by simp +decide [sev, Env.get, dpParams, ctxEnv]) (by simp +decide [sev, Env.get, dpParams, ctxEnv]),
          wcL _ _ (by omega) (by omega)]; simp; omega) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_of_length_le (by simp; omega)]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, hp, sr_of_eq ht.sr rfl rfl rfl rfl, fun j hj => by simp at hj⟩)
  | succ k ih =>
    intro i H Hc s hk hi hA hHc hp hl
    refine specR_prologue (postDP_locals _ _ _ _) (dp_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have him : i < m := by omega
    refine specR_ifI _ 1 (by
        rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 i) (BitVec.ofNat 64 m)
          (by simp +decide [sev, Env.get, dpParams, ctxEnv]) (by simp +decide [sev, Env.get, dpParams, ctxEnv]),
          wcL _ _ (by omega) (by omega)]; simp; omega) (fun _ => ?_) (fun h => absurd h (by decide))
    rw [take_drop_cons2 args m i him hm]
    have hxa : (ctxH C H).H[oa + 1 + i]? = some (Enc.idxW args[i]) := by
      have := hA.2 i (by simp; omega); show H[oa + 1 + i]? = _; simpa using this
    refine UD.specR_heapLoadI' (C := ctxH C H) dpX _ (oa + 1 + i) _ hxa (by decide)
      (by
        simp +decide [sev, Env.get, dpParams, ctxEnv]
        show _ = cellA C (oa + 1 + i)
        apply BitVec.eq_of_toNat_eq; simp [cellA, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega) ?_
    simp only [List.mapM_cons]
    refine ILP.callE_spec (C := ctxH C H) dpY fDropVars dvParams [vv dpN, vv dpX] (dvBody C)
      [BitVec.ofNat 64 n, Enc.idxW args[i]] (by decide) rfl (by decide) hcd
      ⟨by simp +decide [sev, Env.get_cons, Env.get, dpParams, ctxEnv], by simp [sev, Env.get_cons], trivial⟩
      (dv_spec ra (ctxH C H) (ctxOK_H hok H) hcd hcS hcF (ExIS.codes_H C H hcI) n hn s args[i]) (fun y s1 => ?_)
    have hj : d + 1 + i < (ctxH C H).H.length := by show d + 1 + i < H.length; omega
    refine specR_heapStoreI (ctxOK_H hok H) _ (vv dpY) (d + 1 + i) hj (Enc.idxW y)
      (by
        simp +decide [sev, Env.get_cons, Env.get, dpParams, ctxEnv]
        show _ = cellA C (d + 1 + i)
        apply BitVec.eq_of_toNat_eq; simp [cellA, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega)
      (by simp [sev, Env.get_cons]) ?_
    change SpecR (Inv (ctxH C (H.set (d + 1 + i) (Enc.idxW y))) _ _ _ _) _ _ _ _
    generalize hB : H.set (d + 1 + i) (Enc.idxW y) = B
    have hBl : B.length = H.length := by rw [← hB]; simp
    have hBi : B[d + 1 + i]? = some (Enc.idxW y) := by rw [← hB, List.getElem?_set_self (by omega)]
    have hpB : Hc <+: B := by
      refine prefix_of_get? (by have := hp.length_le; omega) (fun j hj => ?_)
      rw [← hB, List.getElem?_set_ne (by omega), List.getElem?_eq_getElem hj]
      exact ConPanqueque.T.Decl.get_prefix (List.getElem?_eq_getElem hj) hp
    have hAB : BlkAt B oa (args.map Enc.idxW) := by
      refine ⟨by rw [← hB, List.getElem?_set_ne (by omega)]; exact hA.1, fun j hj => ?_⟩
      simp only [List.length_map] at hj
      rw [← hB, List.getElem?_set_ne (by omega)]; exact hA.2 j (by simp; omega)
    let Hc' := B.take (d + 2 + i)
    have hpc' : Hc' <+: B := List.take_prefix _ _
    have hHcc : Hc <+: Hc' := by
      refine prefix_of_get? (by simp [Hc']; have := hp.length_le; omega) (fun j hj => ?_)
      simp only [Hc']; rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj]
      exact ConPanqueque.T.Decl.get_prefix (List.getElem?_eq_getElem hj) hpB
    refine specR_callNIG (C := ctxH C B) dpR fDpFill dpParams
      [vv dpA, vv dpD, vv dpN, .op .add [vv dpI, .const 1], vv dpM] dpBody
      [cellA C oa, cellA C d, BitVec.ofNat 64 n, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 m] (by decide) rfl
      (by decide) hcode
      ⟨by simp +decide [sev, Env.get_cons, Env.get, dpParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, dpParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, dpParams, ctxEnv],
        by
          show sev _ _ = _
          rw [sev_add2 _ _ _ (BitVec.ofNat 64 i) _ (by simp +decide [sev, Env.get_cons, Env.get, dpParams, ctxEnv]) rfl]
          exact congrArg some (word_add1_eq i),
        by simp +decide [sev, Env.get_cons, Env.get, dpParams, ctxEnv], trivial⟩
      (PostDP C Hc' d (i + 1))
      (fun ys w s' H' => Hc' <+: H' ∧ ∀ j (hj : j < ys.length), H'[d + 1 + (i + 1) + j]? = some (Enc.idxW ys[j]))
      (fun ys w s' st ⟨H', hp', hs', hc'⟩ => ⟨H', ⟨hp', hc'⟩, hs'⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu dpParams _ rfl hlk)
        (ih (i + 1) B Hc' s1 (by omega) (by omega) hAB (by simp [Hc']; omega) hpc' (by omega)))
      (fun ys w s2 H' ⟨hp', hc'⟩ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H', hHcc.trans hp', sr_of_eq ht.sr rfl rfl rfl rfl, fun j hj => by
      rcases j with _ | j
      · have := ConPanqueque.T.Decl.get_prefix (show Hc'[d + 1 + i]? = some (Enc.idxW y) by
          simp only [Hc']; rw [List.getElem?_take_of_lt (by omega)]; exact hBi) hp'
        simpa using this
      · have := hc' j (by simp at hj; omega)
        rw [show d + 1 + (i + 1) + j = d + 1 + i + (j + 1) by omega] at this
        simpa using this⟩)

/-- A fire record `[tag, levels, pins]` in the value heap. -/
def PostFX (C : Ctx) (f : IRecRuleFire) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st ∧ ∃ o, w = cellA C o ∧ FireE C.HB H' o f

theorem postFX_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostFX C a w s' st → PostFX C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h⟩

theorem fx_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ fxLocals → (ctxEnv C ++ fxParams.zip vals).get x = none :=
  Knot.params_none C fxLocals fxParams vals (by decide) (by decide)

/-- The code `recFire` runs. -/
structure FXCodes (C : Ctx) : Prop where
  sp : C.code.lookup fStripPis = some ([(pFu, .one), (pH, .one)], stripBody C fStripPis 6, .one)
  ga : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  gaa : C.code.lookup fGaa = some ([(pFu, .one), (pH, .one)], gaaBody C, .one)
  ts : C.code.lookup fTSub = some ([(tsA, .one), (tsB, .one)], tsBody, .one)
  vl : C.code.lookup fVlFill = some (vlParams.map (fun p => (p, ShapeHOL.one)), vlBody, .one)
  dp : C.code.lookup fDpFill = some (dpParams.map (fun p => (p, ShapeHOL.one)), dpBody, .one)
  dv : C.code.lookup fDropVars = some (dvParams.map (fun p => (p, ShapeHOL.one)), dvBody C, .one)
  srt : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one)
  ifa : C.code.lookup fInst1F = some ([(pFu, .one), (pH, .one), (pV, .one), (pD, .one)], fastBody C, .one)
  ic : Codes C (body C)

theorem fxPlain_spec (C : Ctx) (hok : CtxOK C) (H H0 : List (BitVec 64)) (hp : H0 <+: H) (s : AState) (Γ : Env)
    (M : Mem) (hx : fxO ∈ ctxLocals ++ fxLocals) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ fxLocals)) (fxPlain C) s (pure .plain)
      (PostFX (ctxH C H0)) := by
  unfold fxPlain
  refine specR_alloc6I (ctxOK_H hok H) fxO _ _ _ _ _ _ 0 0 0 0 0 0 hx (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun H2 ws hp2 hws hroom => ?_)
  obtain ⟨g0, -, -, -, -, -⟩ := img6_get H2 ws 0 0 0 0 0 0 hws
  exact specR_returnI _ (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht =>
    ⟨_, (hp.trans hp2).trans (img6_prefix _ _ _ _ _ _ _ _ hws), sr_of_eq ht.sr rfl rfl rfl rfl, H2.length, rfl, g0⟩)

/-- **`recFire`**. -/
theorem fx_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : FXCodes C)
    (p : BlockShape) (rc : RecShape) (htg : rc.tgt < 2 ^ 64) (hk : p.k < 2 ^ 64) (hmI : rc.mI < 2 ^ 63)
    (hrP : rc.rP < 2 ^ 63) (H : List (BitVec 64)) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (fxParams.zip [BitVec.ofNat 64 rc.tgt, BitVec.ofNat 64 p.k,
      BitVec.ofNat 64 rc.mI, BitVec.ofNat 64 rc.rP, Enc.idxW rc.cvR.type])) (fxBody C) s (recFire p rc)
      (PostFX (ctxH C H)) := by
  refine specR_prologue (postFX_locals _) (fx_none _ _) ?_
  unfold recFire
  let Γ0 : Env := ctxEnv (ctxH C H) ++ fxParams.zip [BitVec.ofNat 64 rc.tgt, BitVec.ofNat 64 p.k,
      BitVec.ofNat 64 rc.mI, BitVec.ofNat 64 rc.rP, Enc.idxW rc.cvR.type]
  have gTg : Γ0.get fxTg = some (BitVec.ofNat 64 rc.tgt) := by simp +decide [Γ0, Env.get, fxParams, ctxEnv]
  have gK : Γ0.get fxK = some (BitVec.ofNat 64 p.k) := by simp +decide [Γ0, Env.get, fxParams, ctxEnv]
  have gMI : Γ0.get fxMI = some (BitVec.ofNat 64 rc.mI) := by simp +decide [Γ0, Env.get, fxParams, ctxEnv]
  have gRP : Γ0.get fxRP = some (BitVec.ofNat 64 rc.rP) := by simp +decide [Γ0, Env.get, fxParams, ctxEnv]
  have gT : Γ0.get fxT = some (Enc.idxW rc.cvR.type) := by simp +decide [Γ0, Env.get, fxParams, ctxEnv]
  by_cases ht : rc.tgt < p.k
  · refine specR_ifI _ 1 (by
        rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 rc.tgt) (BitVec.ofNat 64 p.k) (by simp only [sev, sev_vv]; exact gTg)
          (by simp only [sev, sev_vv]; exact gK), wcL _ _ htg hk]; simp [ht]) (fun _ => ?_) (fun h => absurd h (by decide))
    rw [if_pos ht]
    exact fxPlain_spec C hok H H (List.prefix_refl _) s _ _ (by decide)
  refine specR_ifI _ 0 (by
      rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 rc.tgt) (BitVec.ofNat 64 p.k) (by simp only [sev, sev_vv]; exact gTg)
        (by simp only [sev, sev_vv]; exact gK), wcL _ _ htg hk]; simp [ht]) (fun h => absurd rfl h) (fun _ => ?_)
  rw [if_neg ht]
  refine ro_strip C hok hc.sp rc.mI (by omega) rc.cvR.type H s fxS (vv fxMI) (vv fxT) (by decide)
    (by simp only [sev, sev_vv]; exact gMI) (by simp only [sev, sev_vv]; exact gT) (fun o w s1 H1 hp1 hr1 hn1 hs1 => ?_)
  have hp1' : H <+: H1 := hp1
  rcases o with _ | ⟨tys, b⟩
  · have e0 := hn1 rfl
    subst e0
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact fxPlain_spec C hok H1 H hp1' s1 _ _ (by decide)
  obtain ⟨oa, rfl, hba⟩ := hs1 tys b rfl
  obtain ⟨ha0, haL, -⟩ := strip_last hba
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN => ?_)
  have hol := blkAt_lt hba
  have hHN' : H1.length ≤ C.HN := hHN
  have hne : cellA C oa ≠ 0 := cellA_ne0 C hok oa (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only
  refine UD.specR_heapLoadI' (C := ctxH C H1) fxSc (vv fxS) oa _ ha0 (by decide)
    (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H1) fxB _ (oa + 1 + tys.length) _ haL (by decide)
    (by
      simp only [sev, sev_vv, Env.get_cons]; simp +decide
      show cellA C oa + _ = cellA C _
      rw [cellA_shl3]; congr 1; omega) ?_
  have tagNo : ∀ (h : EIdx) (vh : ENodeView) (k : Nat) (u32 : UInt32), u32 = UInt32.ofNat k → k < 16 →
      h.tag = UInt32.ofNat vh.tagN → vh.tagN ≠ k → (h.tag == u32) = false := by
    intro h vh k u32 hu hk hat hne
    rw [hat, hu]
    have hl := ConPanqueque.T.Big.tagN_lt vh
    have : UInt32.ofNat vh.tagN ≠ UInt32.ofNat k := by
      intro e; have := congrArg UInt32.toNat e; simp at this; omega
    simpa using this
  have gTag : ∀ (Γ : Env) (vh : ENodeView) (k : Nat), k < 16 → Γ.get lDg = some (BitVec.ofNat 64 vh.tagN) →
      sev Γ (veEqC lDg k) = some (boolW (vh.tagN == k)) := by
    intro Γ vh k hk hg
    simp only [veEqC]
    rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 vh.tagN) (BitVec.ofNat 64 k) (by simp only [sev, sev_vv]; exact hg) rfl,
      wcE' _ _ (by have := ConPanqueque.T.Big.tagN_lt vh; omega) (by omega)]
    by_cases h : vh.tagN = k <;> simp [h, boolW]
  unfold viewOf
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get_cons, Env.get, fxParams, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv fxB) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
  refine ConPanqueque.T.Big.specR_viewP b (by simp) (by simp +decide [Env.get_cons] <;> rfl)
    (by simp +decide [Env.get_cons, Env.get, fxParams, ctxEnv] <;> rfl) (by decide) (fun vb P hvb htnb hlenb => ?_)
  have hatb := tag_of_tagN htnb
  by_cases h6 : vb.tagN = 6
  swap
  · refine specR_ifI _ _ (gTag _ vb 6 (by decide) (by simp [Env.get_cons])) (fun h => absurd h (by simp [boolW, h6]))
      (fun _ => ?_)
    simp only [tagNo b vb 6 ETag.forallE rfl (by decide) hatb h6, Bool.false_eq_true, ite_false]
    exact fxPlain_spec C hok H1 H hp1' s1 _ _ (by decide)
  refine specR_ifI _ _ (gTag _ vb 6 (by decide) (by simp [Env.get_cons])) (fun _ => ?_)
    (fun h => absurd h (by simp [boolW, h6]))
  rcases vb with _ | _ | _ | _ | _ | _ | ⟨dom, bd⟩ | _ | _ | _ <;> simp [ENodeView.tagN] at h6
  have htb : b.tag = ETag.forallE := by rw [hatb]; rfl
  simp only [htb, beq_self_eq_true, ite_true]
  refine specR_runBind (show viewBind b s1 = .ok (some (dom, bd), s1) by
    rw [WC.viewBind_run, WC.viewBind_of_view_forallE htb hvb]) ?_
  refine specR_loadI' fxDom _ (P + 0) (P + BitVec.ofNat 64 0) (Enc.idxW dom) (by decide)
    (by simp +decide [sev, Env.get_cons]) rfl
    (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW dom) [Enc.idxW bd] []) ?_
  refine specR_callNIM fxHd fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv fxDom]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW dom] (by decide) rfl (by decide) hc.ga
    ⟨rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (fun a w s' st => getAppFn coreWalkFuel dom s1 = .ok (a, s') ∧ Post (ctxH C H1) s1 a w s' st)
    (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u' hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec (ctxH C H1) hc.ga coreWalkFuel dom s1 CV.coreWalkFuel_lt t
        ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun hd w s' st ⟨hrun, hw, hs, _⟩ => ?_)
  subst hw
  have hs' : s1 = s' := hs.symm
  subst hs'
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get_cons, Env.get, fxParams, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv fxHd) (Enc.idxW hd) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
  refine ConPanqueque.T.Big.specR_viewP hd (by simp) (by simp +decide [Env.get_cons] <;> rfl)
    (by simp +decide [Env.get_cons, Env.get, fxParams, ctxEnv] <;> rfl) (by decide) (fun vh Ph hvh htnh hlenh => ?_)
  have hath := tag_of_tagN htnh
  by_cases h3 : vh.tagN = 3
  swap
  · refine specR_ifI _ _ (gTag _ vh 3 (by decide) (by simp [Env.get_cons])) (fun h => absurd h (by simp [boolW, h3]))
      (fun _ => ?_)
    simp only [tagNo hd vh 3 ETag.const rfl (by decide) hath h3, Bool.false_eq_true, ite_false]
    exact fxPlain_spec C hok H1 H hp1' s1 _ _ (by decide)
  refine specR_ifI _ _ (gTag _ vh 3 (by decide) (by simp [Env.get_cons])) (fun _ => ?_)
    (fun h => absurd h (by simp [boolW, h3]))
  rcases vh with _ | _ | _ | ⟨nm, us⟩ | _ | _ | _ | _ | _ | _ <;> simp [ENodeView.tagN] at h3
  have hth : hd.tag = ETag.const := by rw [hath]; rfl
  simp only [hth, beq_self_eq_true, ite_true]
  refine specR_runBind (show viewConst hd s1 = .ok (some (nm, us), s1) by
    rw [WC.viewConst_run, WC.viewConst_of_view hth hvh]) ?_
  refine specR_loadI' fxUs _ (Ph + 8) (Ph + BitVec.ofNat 64 8) (Enc.idxW us) (by decide)
    (by simp +decide [sev, Env.get_cons]) rfl
    (by have := wordsAt_mem1 Ph (Enc.idxW nm) (Enc.idxW us) [] []; simpa [encEView, Enc.encConst] using this) ?_
  unfold fxNested
  refine specR_assignI lDh (vv fxUs) (Enc.idxW us) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
  refine specR_assignI lFl (vv lFls) C.FLs (by decide) (by simp +decide [Env.get_cons, Env.get, fxParams, ctxEnv] <;> rfl) ?_
  refine specR_lsviewPI (C := ctxH C H1) us (by simp) (by simp +decide [Env.get_cons] <;> rfl)
    (by simp +decide [Env.get_cons, Env.get, fxParams, ctxEnv] <;> rfl) (by decide) (fun vl Pl hvl htl hlenl => ?_)
  simp only [List.length_map] at hlenl
  refine specR_runBind (show viewLs us s1 = .ok (vl, s1) by
    simp [viewLs, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure, StateT.pure, Except.bind,
      Except.pure, hvl]) ?_
  refine specR_assignI fxN (vv lRn) (BitVec.ofNat 64 vl.length) (by decide) (by simp [sev, Env.get_cons]) ?_
  refine specR_guardI fxN vl.length 58 (by decide) (by simp [Env.get_cons]) (by omega) (fun hvl58 => ?_)
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN1 => ?_)
  have hHN1' : H1.length ≤ C.HN := hHN1
  have hlay := hok.heapLay
  refine specR_allocI (C := ctxH C H1) fxLv _ (vl.length + 1) (by omega) (by decide) (fun v => ?_)
    (fun H2 ws hp2 hws hroom => ?_)
  · simp +decide [sev, Env.get_cons]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hp2' : H1 <+: H2 := hp2
  have hq0 : H2.length < (ctxH (ctxH C H1) (H2 ++ ws)).H.length := by show H2.length < (H2 ++ ws).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv fxLv) (vv fxN) H2.length hq0 (BitVec.ofNat 64 vl.length)
    (by simp +decide [sev, Env.get_cons] <;> rfl) (by simp +decide [sev, Env.get_cons]) ?_
  change SpecR (Inv (ctxH C ((H2 ++ ws).set H2.length (BitVec.ofNat 64 vl.length))) _ _ _ _) _ _ _ _
  generalize hB : (H2 ++ ws).set H2.length (BitVec.ofNat 64 vl.length) = B
  have hBlen : B.length = H2.length + (vl.length + 1) := by rw [← hB]; simp [hws]
  have hB0 : B[H2.length]? = some (BitVec.ofNat 64 vl.length) := by rw [← hB, List.getElem?_set_self (by simp; omega)]
  have hpB : H2 <+: B := by
    refine prefix_of_get? (by omega) (fun j hj => ?_)
    rw [← hB, List.getElem?_set_ne (by omega), List.getElem?_append_left hj]
  let Hc := B.take (H2.length + 1)
  refine specR_pureBind () ?_
  refine specR_callNIG (C := ctxH C B) fxX fVlFill vlParams [vv fxUs, vv fxLv, .const 0] vlBody
    [Enc.idxW us, cellA C H2.length, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.vl
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons]; rfl, rfl, trivial⟩
    (fun a w s' st => (pure () : AM Unit) s1 = .ok (a, s') ∧ PostVL C Hc H2.length vl 0 a w s' st)
    (fun a w s' H' => s' = s1 ∧ Hc <+: H' ∧ ∀ j (hj : j < vl.length), 0 ≤ j → H'[H2.length + 1 + j]? = some (Enc.idxW vl[j]))
    (fun a w s' st ⟨hr, H', hp', hs', hc'⟩ => by
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
      obtain ⟨-, rfl⟩ := hr
      exact ⟨H', ⟨rfl, hp', hc'⟩, hs'⟩)
    (fun u hu _ hlk => specR_run (fun w hw => by
      subst hw
      exact vl_spec C hok hc.vl us vl H2.length _ 0 B Hc s1 rfl (Nat.zero_le _) hvl (by simp [Hc])
        (List.take_prefix _ _) (by omega) _ (pre_of_lookups hu vlParams _ rfl hlk)))
    (fun a w s' H3 ⟨hs', hp3, hc3⟩ => ?_)
  subst s'
  have hpc : H2 <+: Hc := by
    refine prefix_of_get? (by simp [Hc]; omega) (fun j hj => ?_)
    simp only [Hc]; rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj]
    exact ConPanqueque.T.Decl.get_prefix (List.getElem?_eq_getElem hj) hpB
  have hlvB : BlkAt H3 H2.length (vl.map Enc.idxW) := by
    refine ⟨?_, fun j hj => ?_⟩
    · have := ConPanqueque.T.Decl.get_prefix (show Hc[H2.length]? = some (BitVec.ofNat 64 vl.length) by
        simp only [Hc]; rw [List.getElem?_take_of_lt (by omega)]; exact hB0) hp3
      simpa using this
    · simp only [List.length_map] at hj
      simpa using hc3 j hj (Nat.zero_le _)
  have hp13 : H1 <+: H3 := (hp2'.trans hpc).trans hp3
  refine specR_callNIH (C := ctxH C H3) fxA fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv fxDom] (gaaBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW dom] (by decide) rfl (by decide) hc.gaa
    ⟨rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (PostA (ctxH C H3)) (fun args w _ H' => ∃ oA, w = cellA C oA ∧ BlkAt H' oA (args.map Enc.idxW))
    (fun args w s' st ⟨H', oA, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨oA, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (ConPanqueque.T.ExG.gaa_spec C hok hc.gaa coreWalkFuel CV.coreWalkFuel_lt H3 dom s1))
    (fun args wA s2 H4 hp4 ⟨oA, hwA, hab⟩ => ?_)
  subst hwA
  have hp34 : H3 <+: H4 := hp4
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN4 => ?_)
  have hHN4' : H4.length ≤ C.HN := hHN4
  have hal := blkAt_len hab
  simp only [List.length_map] at hal
  have hA0 : (ctxH C H4).H[oA]? = some (BitVec.ofNat 64 args.length) := by show H4[oA]? = _; rw [hab.1]; simp
  refine UD.specR_heapLoadI' (C := ctxH C H4) fxAl (vv fxA) oA _ hA0 (by decide)
    (by simp [sev, Env.get_cons]; rfl) ?_
  refine specR_pureBind (rc.mI - rc.rP) ?_
  refine rb_tsub (D := ctxLocals ++ fxLocals) C hc.ts rc.mI rc.rP (by omega) (by omega) H4 s2 fxNI (vv fxMI) (vv fxRP)
    (by decide) (by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gMI; exact gMI)
    (by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gRP; exact gRP) (fun H4b hp4b => ?_)
  refine specR_pureBind (args.length - (rc.mI - rc.rP)) ?_
  refine rb_tsub (D := ctxLocals ++ fxLocals) C hc.ts args.length (rc.mI - rc.rP) (by omega) (by omega) H4b s2 fxM
    (vv fxAl) (vv fxNI) (by decide) (by simp +decide [sev, Env.get_cons]) (by simp +decide [sev, Env.get_cons])
    (fun H4c hp4c => ?_)
  have hp4c' : H4 <+: H4c := (show H4 <+: H4b from hp4b).trans hp4c
  have habc := blkAt_mono hab hp4c'
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN5 => ?_)
  have hHN5' : H4c.length ≤ C.HN := hHN5
  have hlA := blkAt_len habc
  simp only [List.length_map] at hlA
  generalize hmd : args.length - (rc.mI - rc.rP) = m at *
  refine specR_allocI (C := ctxH C H4c) fxPs _ (m + 1) (by omega) (by decide) (fun v => ?_)
    (fun H5 ws2 hp5 hws2 hroom2 => ?_)
  · simp +decide [sev, Env.get_cons]
    apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
  have hp5' : H4c <+: H5 := hp5
  have hq5 : H5.length < (ctxH (ctxH C H4c) (H5 ++ ws2)).H.length := by show H5.length < (H5 ++ ws2).length; simp; omega
  refine specR_heapStoreI (ctxOK_H hok _) (vv fxPs) (vv fxM) H5.length hq5 (BitVec.ofNat 64 m)
    (by simp +decide [sev, Env.get_cons] <;> rfl) (by simp +decide [sev, Env.get_cons]) ?_
  change SpecR (Inv (ctxH C ((H5 ++ ws2).set H5.length (BitVec.ofNat 64 m))) _ _ _ _) _ _ _ _
  generalize hB2 : (H5 ++ ws2).set H5.length (BitVec.ofNat 64 m) = B2
  have hB2len : B2.length = H5.length + (m + 1) := by rw [← hB2]; simp [hws2]
  have hB20 : B2[H5.length]? = some (BitVec.ofNat 64 m) := by rw [← hB2, List.getElem?_set_self (by simp; omega)]
  have hpB2 : H5 <+: B2 := by
    refine prefix_of_get? (by omega) (fun j hj => ?_)
    rw [← hB2, List.getElem?_set_ne (by omega), List.getElem?_append_left hj]
  have habB2 : BlkAt B2 oA (args.map Enc.idxW) := blkAt_mono habc (hp5'.trans hpB2)
  let Hc2 := B2.take (H5.length + 1)
  refine specR_callNIG (C := ctxH C B2) fxX fDpFill dpParams [vv fxA, vv fxPs, vv fxNI, .const 0, vv fxM] dpBody
    [cellA C oA, cellA C H5.length, BitVec.ofNat 64 (rc.mI - rc.rP), BitVec.ofNat 64 0, BitVec.ofNat 64 m]
    (by decide) rfl (by decide) hc.dp
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons]; rfl, by simp +decide [sev, Env.get_cons],
      rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (fun ps w s' st => (args.take m).mapM (exprDropVars (rc.mI - rc.rP)) s2 = .ok (ps, s') ∧
      PostDP C Hc2 H5.length 0 ps w s' st)
    (fun ps w s' H' => ps.length = (args.take m).length ∧ Hc2 <+: H' ∧
      ∀ j (hj : j < ps.length), H'[H5.length + 1 + 0 + j]? = some (Enc.idxW ps[j]))
    (fun ps w s' st ⟨hrun, H', hp', hs', hc'⟩ => ⟨H', ⟨mapM_len _ _ _ _ _ hrun, hp', hc'⟩, hs'⟩)
    (fun u hu _ hlk => specR_run (fun w' hw' => by
      subst hw'
      have h5l := hp5'.length_le
      have := dp_spec (σ := σ) ra C hok hc.dv hc.srt hc.ifa hc.ic hc.dp args oA H5.length (rc.mI - rc.rP) m (by omega)
        (by omega) (by omega) m 0 B2 Hc2 s2 (by omega) (Nat.zero_le _) habB2 (by simp [Hc2]) (List.take_prefix _ _)
        (by omega)
      simp only [List.drop_zero] at this
      exact this _ (pre_of_lookups hu dpParams _ rfl hlk)))
    (fun ps w s3 H6 ⟨hpl, hp6, hc6⟩ => ?_)
  have hpc2 : H5 <+: Hc2 := by
    refine prefix_of_get? (by simp [Hc2]; omega) (fun j hj => ?_)
    simp only [Hc2]; rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj]
    exact ConPanqueque.T.Decl.get_prefix (List.getElem?_eq_getElem hj) hpB2
  have hpl' : ps.length = m := by rw [hpl]; simp; omega
  have hpsB : BlkAt H6 H5.length (ps.map Enc.idxW) := by
    refine ⟨?_, fun j hj => ?_⟩
    · have := ConPanqueque.T.Decl.get_prefix (show Hc2[H5.length]? = some (BitVec.ofNat 64 m) by
        simp only [Hc2]; rw [List.getElem?_take_of_lt (by omega)]; exact hB20) hp6
      simpa [hpl'] using this
    · simp only [List.length_map] at hj
      have := hc6 j hj
      simpa using this
  have hp56 : H5 <+: H6 := hpc2.trans hp6
  have hlv6 : BlkAt H6 H2.length (vl.map Enc.idxW) :=
    blkAt_mono hlvB ((hp34.trans hp4c').trans (hp5'.trans hp56) |> fun h => by
      exact (show H3 <+: H6 from (hp34.trans ((show H4 <+: H4b from hp4b).trans hp4c)).trans (hp5'.trans hp56)))
  refine specR_alloc6I (ctxOK_H hok H6) fxO (.const 1) (vv fxLv) (vv fxPs) (.const 0) (.const 0) (.const 0)
    1 (cellA C H2.length) (cellA C H5.length) 0 0 0 (by decide) (fun _ => rfl)
    (fun _ => by simp +decide [sev, Env.get_cons]; rfl) (fun _ => by simp +decide [sev, Env.get_cons]; rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun H7 ws7 hp7 hws7 hroom7 => ?_)
  obtain ⟨g0, g1, g2, -, -, -⟩ := img6_get H7 ws7 1 (cellA C H2.length) (cellA C H5.length) 0 0 0 hws7
  have hpi := img6_prefix H7 ws7 1 (cellA C H2.length) (cellA C H5.length) 0 0 0 hws7
  have hp67 : H6 <+: H7 := hp7
  exact specR_returnI _ (cellA C H7.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht =>
    ⟨_, hp1'.trans (hp13.trans ((show H3 <+: H6 from (hp34.trans ((show H4 <+: H4b from hp4b).trans hp4c)).trans
        (hp5'.trans hp56)).trans (hp67.trans hpi))),
      sr_of_eq ht.sr rfl rfl rfl rfl, H7.length, rfl,
      ⟨g0, ⟨cellA C H2.length, g1, H2.length, rfl, blkAt_mono hlv6 (hp67.trans hpi)⟩,
        ⟨cellA C H5.length, g2, H5.length, rfl, blkAt_mono hpsB (hp67.trans hpi)⟩⟩⟩)

end

end ConPanqueque.T.Ind
