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

end

end ConPanqueque.T.Ind
