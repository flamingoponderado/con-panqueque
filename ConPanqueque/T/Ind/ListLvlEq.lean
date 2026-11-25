import ConPanqueque.T.Ind.LvlEqE

/-!
# Two lists pairwise equal up to equivalent levels (`listLvlEq`)

`ll(pa, pb, i)` compares the blocks at `pa` and `pb` from position `i` on with `lvlEq coreWalkFuel`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI

def llPa := ofString "ll_pa"
def llPb := ofString "ll_pb"
def llI := ofString "ll_i"
def llNa := ofString "ll_na"
def llNb := ofString "ll_nb"
def llX := ofString "ll_x"
def llY := ofString "ll_y"
def llR := ofString "ll_r"
def fListLvlEq := ofString "listLvlEq"

def llParams : List MlS := [llPa, llPb, llI]
def llLocals : List MlS := [llNa, llNb, llX, llY, llR]

def llBody : ProgHOL 64 := prologue llLocals
  (.seq (.assign .local llNa (.load .one (vv llPa)))
  (.seq (.assign .local llNb (.load .one (vv llPb)))
  (.ite (.cmp .lower (vv llI) (vv llNa))
    (.ite (.cmp .lower (vv llI) (vv llNb))
      (.seq (.assign .local llX (.load .one (.op .add [vv llPa, .shift .lsl (.op .add [vv llI, .const 1]) (.const 3)])))
      (.seq (.assign .local llY (.load .one (.op .add [vv llPb, .shift .lsl (.op .add [vv llI, .const 1]) (.const 3)])))
      (.seq (.call (some (some (.local, llR), none)) fLvlEqE
        [.const (BitVec.ofNat 64 coreWalkFuel), vv llX, vv llY])
      (.ite (veEqC llR 0) (.return (.const 0))
      (.seq (.call (some (some (.local, llR), none)) fListLvlEq [vv llPa, vv llPb, .op .add [vv llI, .const 1]])
        (.return (vv llR)))))))
      (.return (.const 0)))
    (.ite (.cmp .lower (vv llI) (vv llNb)) (.return (.const 0)) (.return (.const 1))))))

section
variable {σ : Type}

theorem ll_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ llLocals → (ctxEnv C ++ llParams.zip vals).get x = none :=
  Knot.params_none C llLocals llParams vals (by decide) (by decide)

theorem listLvlEq_drop_cons (as bs : List EIdx) (i : Nat) (ha : i < as.length) (hb : i < bs.length) :
    listLvlEq (as.drop i) (bs.drop i) = (lvlEq coreWalkFuel as[i] bs[i] >>= fun r =>
      if r then listLvlEq (as.drop (i + 1)) (bs.drop (i + 1)) else pure false) := by
  rw [List.drop_eq_getElem_cons ha, List.drop_eq_getElem_cons hb, listLvlEq]

theorem wcL (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) : Flapjack.Compiler.Encoders.Asm.wordCmpHOL .lower
    (BitVec.ofNat 64 a) (BitVec.ofNat 64 b) = decide (a < b) := by
  simp only [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  by_cases h : a < b
  · simp [h, (ofNat_lt_iff ha hb).mpr h]
  · simp [h, (ofNat_lt_iff ha hb).not.mpr h]

theorem sev_add2 (Γ : Env) (e1 e2 : ExpHOL 64) (a b : BitVec 64)
    (h1 : sev Γ e1 = some a) (h2 : sev Γ e2 = some b) : sev Γ (.op .add [e1, e2]) = some (a + b) := by
  simp [sev, h1, h2]

theorem coreWalkFuel_lt63 : coreWalkFuel < 2 ^ 63 := by unfold coreWalkFuel; decide


theorem ll_step (C : Ctx) (hok : CtxOK C) (hc : VECodes C)
    (hcl : C.code.lookup fListLvlEq = some (llParams.map (fun p => (p, ShapeHOL.one)), llBody, .one))
    (pa pb : Nat) (as bs : List EIdx) (i : Nat) (H : List (BitVec 64)) (s : AState) (hi : i ≤ as.length)
    (hA : BlkAt H pa (as.map Enc.idxW)) (hB : BlkAt H pb (bs.map Enc.idxW))
    (rec : i < as.length → ∀ (H' : List (BitVec 64)) (s' : AState), BlkAt H' pa (as.map Enc.idxW) →
      BlkAt H' pb (bs.map Enc.idxW) →
      SpecR (Pre (σ := σ) (ctxH C H') s' (llParams.zip [cellA C pa, cellA C pb, BitVec.ofNat 64 (i + 1)])) llBody s'
        (listLvlEq (as.drop (i + 1)) (bs.drop (i + 1))) (PostB (ctxH C H'))) :
    SpecR (Pre (σ := σ) (ctxH C H) s (llParams.zip [cellA C pa, cellA C pb, BitVec.ofNat 64 i])) llBody s
      (listLvlEq (as.drop i) (bs.drop i)) (PostB (ctxH C H)) := by
  refine specR_prologue (postB_locals _) (ll_none _ _) ?_
  let Γ0 : Env := ctxEnv (ctxH C H) ++ llParams.zip [cellA C pa, cellA C pb, BitVec.ofNat 64 i]
  have gPa : Γ0.get llPa = some (cellA C pa) := by simp +decide [Γ0, Env.get, llParams, ctxEnv]
  have gPb : Γ0.get llPb = some (cellA C pb) := by simp +decide [Γ0, Env.get, llParams, ctxEnv]
  have gI : Γ0.get llI = some (BitVec.ofNat 64 i) := by simp +decide [Γ0, Env.get, llParams, ctxEnv]
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : H.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  have hla := blkAt_len hA
  have hlb := blkAt_len hB
  simp only [List.length_map] at hla hlb
  have hA0 : (ctxH C H).H[pa]? = some (BitVec.ofNat 64 as.length) := by show H[pa]? = _; rw [hA.1]; simp
  have hB0 : (ctxH C H).H[pb]? = some (BitVec.ofNat 64 bs.length) := by show H[pb]? = _; rw [hB.1]; simp
  refine UD.specR_heapLoadI' (C := ctxH C H) llNa (vv llPa) pa _ hA0 (by simp +decide [ctxLocals, llLocals])
    (by simp only [sev, sev_vv]; exact gPa) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H) llNb (vv llPb) pb _ hB0 (by simp +decide [ctxLocals, llLocals])
    (by simp only [sev, sev_vv, Env.get_cons]; simp +decide; exact gPb) ?_
  have gI' : sev ((llNb, BitVec.ofNat 64 bs.length) :: (llNa, BitVec.ofNat 64 as.length) :: Γ0) (vv llI) =
      some (BitVec.ofNat 64 i) := by simp only [sev, sev_vv, Env.get_cons]; simp +decide; exact gI
  have ret : ∀ (Γ : Env) (b : Bool) (w : BitVec 64), w = boolW b →
      SpecR (σ := σ) (Inv (ctxH C H) s Γ [] (ctxLocals ++ llLocals)) (.return (.const w)) s (pure b)
        (PostB (ctxH C H)) := fun Γ b w hw =>
    specR_returnI _ w rfl (fun t ht => ⟨H, List.prefix_refl _, hw, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  by_cases hia : i < as.length
  · refine specR_ifI _ 1 (by
        rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 i) (BitVec.ofNat 64 as.length) gI' (by simp +decide [sev, Env.get_cons]),
          wcL _ _ (by omega) (by omega)]; simp [hia])
      (fun _ => ?_) (fun h => absurd h (by decide))
    by_cases hib : i < bs.length
    · refine specR_ifI _ 1 (by
          rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 i) (BitVec.ofNat 64 bs.length) gI' (by simp +decide [sev, Env.get_cons]),
            wcL _ _ (by omega) (by omega)]; simp [hib])
        (fun _ => ?_) (fun h => absurd h (by decide))
      rw [listLvlEq_drop_cons as bs i hia hib]
      have hxa : (ctxH C H).H[pa + 1 + i]? = some (Enc.idxW as[i]) := by
        have := hA.2 i (by simp; omega); show H[pa + 1 + i]? = _; simpa using this
      have hyb : (ctxH C H).H[pb + 1 + i]? = some (Enc.idxW bs[i]) := by
        have := hB.2 i (by simp; omega); show H[pb + 1 + i]? = _; simpa using this
      refine UD.specR_heapLoadI' (C := ctxH C H) llX _ (pa + 1 + i) _ hxa (by simp +decide [ctxLocals, llLocals])
        (by
          simp only [sev, sev_vv, Env.get_cons]; simp +decide
          simp only [Γ0] at gPa gI
          rw [gPa, gI]; simp
          show _ = cellA C (pa + 1 + i)
          apply BitVec.eq_of_toNat_eq; simp [cellA, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
          omega) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H) llY _ (pb + 1 + i) _ hyb (by simp +decide [ctxLocals, llLocals])
        (by
          simp only [sev, sev_vv, Env.get_cons]; simp +decide
          simp only [Γ0] at gPb gI
          rw [gPb, gI]; simp
          show _ = cellA C (pb + 1 + i)
          apply BitVec.eq_of_toNat_eq; simp [cellA, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
          omega) ?_
      refine specR_callNIH (C := ctxH C H) llR fLvlEqE veParams [.const (BitVec.ofNat 64 coreWalkFuel), vv llX, vv llY]
        veBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW as[i], Enc.idxW bs[i]] (by decide) rfl
        (by simp +decide [ctxLocals, llLocals]) hc.ve
        ⟨rfl, by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], trivial⟩
        (PostB (ctxH C H)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu veParams _ rfl hlk)
          (ve_spec C hok hc coreWalkFuel coreWalkFuel_lt63 H as[i] bs[i] s))
        (fun r w s1 H1 hp1 hw => ?_)
      subst hw
      have hp1' : H <+: H1 := hp1
      rcases r
      · refine specR_ifI _ 1 (by simp +decide [veEqC, sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun h => absurd h (by decide))
        exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      simp only [ite_true]
      refine specR_congr (m' := listLvlEq (as.drop (i + 1)) (bs.drop (i + 1)) >>= fun r => pure r) (by rw [bind_pure]) ?_
      refine specR_callNIH (C := ctxH C H1) llR fListLvlEq llParams [vv llPa, vv llPb, .op .add [vv llI, .const 1]]
        llBody [cellA C pa, cellA C pb, BitVec.ofNat 64 (i + 1)] (by decide) rfl
        (by simp +decide [ctxLocals, llLocals]) hcl
        ⟨by simp only [sev, sev_vv, Env.get_cons]; simp +decide; exact gPa,
          by simp only [sev, sev_vv, Env.get_cons]; simp +decide; exact gPb,
          by
            show sev _ _ = _
            rw [sev_add2 _ _ _ _ _ (by simp only [sev, sev_vv, Env.get_cons]; simp +decide; exact gI) rfl]
            exact congrArg some (word_add1_eq i), trivial⟩
        (PostB (ctxH C H1)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu llParams _ rfl hlk)
          (rec hia H1 s1 (blkAt_mono hA hp1') (blkAt_mono hB hp1')))
        (fun r2 w2 s2 H2 hp2 hw2 => ?_)
      subst hw2
      have hp2' : H1 <+: H2 := hp2
      exact specR_returnI _ _ (by simp [sev, Env.get_cons])
        (fun t ht => ⟨H2, hp1'.trans hp2', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_ifI _ 0 (by
          rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 i) (BitVec.ofNat 64 bs.length) gI' (by simp +decide [sev, Env.get_cons]),
            wcL _ _ (by omega) (by omega)]; simp [hib])
        (fun h => absurd rfl h) (fun _ => ?_)
      rw [List.drop_eq_getElem_cons hia, List.drop_of_length_le (by omega : bs.length ≤ i)]
      exact ret _ false 0 rfl
  · refine specR_ifI _ 0 (by
        rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 i) (BitVec.ofNat 64 as.length) gI' (by simp +decide [sev, Env.get_cons]),
          wcL _ _ (by omega) (by omega)]; simp [hia])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_of_length_le (by omega : as.length ≤ i)]
    by_cases hib : i < bs.length
    · refine specR_ifI _ 1 (by
          rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 i) (BitVec.ofNat 64 bs.length) gI' (by simp +decide [sev, Env.get_cons]),
            wcL _ _ (by omega) (by omega)]; simp [hib])
        (fun _ => ?_) (fun h => absurd h (by decide))
      rw [List.drop_eq_getElem_cons hib]
      exact ret _ false 0 rfl
    · refine specR_ifI _ 0 (by
          rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 i) (BitVec.ofNat 64 bs.length) gI' (by simp +decide [sev, Env.get_cons]),
            wcL _ _ (by omega) (by omega)]; simp [hib])
        (fun h => absurd rfl h) (fun _ => ?_)
      rw [List.drop_of_length_le (by omega : bs.length ≤ i)]
      exact ret _ true 1 rfl

/-- **`listLvlEq`** from position `i`. -/
theorem ll_spec (C : Ctx) (hok : CtxOK C) (hc : VECodes C)
    (hcl : C.code.lookup fListLvlEq = some (llParams.map (fun p => (p, ShapeHOL.one)), llBody, .one))
    (pa pb : Nat) (as bs : List EIdx) :
    ∀ k i (H : List (BitVec 64)) (s : AState), as.length - i = k → i ≤ as.length →
      BlkAt H pa (as.map Enc.idxW) → BlkAt H pb (bs.map Enc.idxW) →
      SpecR (Pre (σ := σ) (ctxH C H) s (llParams.zip [cellA C pa, cellA C pb, BitVec.ofNat 64 i])) llBody s
        (listLvlEq (as.drop i) (bs.drop i)) (PostB (ctxH C H)) := by
  intro k
  induction k with
  | zero =>
    intro i H s hk hi hA hB
    exact ll_step C hok hc hcl pa pb as bs i H s hi hA hB (fun h => absurd h (by omega))
  | succ k ih =>
    intro i H s hk hi hA hB
    exact ll_step C hok hc hcl pa pb as bs i H s hi hA hB
      (fun hia H' s' hA' hB' => ih (i + 1) H' s' (by omega) (by omega) hA' hB')

end

end ConPanqueque.T.Ind
