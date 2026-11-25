import ConPanqueque.T.Ind.ListAnnEq

/-!
# The two readings of a rule's parts are one (`paramsAnnEq`, `iotaPartsRel`)

`paramsAnnEq fe cnP cv pd`: the recursor's first `cnP` binder domains are the constructor's parameter domains
`pd` up to consumed annotations. The binder domains are copied out of `stripPis`'s answer into their own block.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP

def pqN := ofString "pq_n"
def pqT := ofString "pq_t"
def pqD := ofString "pq_d"
def pqS := ofString "pq_s"
def pqSc := ofString "pq_sc"
def pqI1 := ofString "pq_i1"
def pqR := ofString "pq_r"
def pqX := ofString "pq_x"
def fParamsAnnEq := ofString "paramsAnnEq"

def pqParams : List MlS := [pqN, pqT, pqD]
def pqLocals : List MlS := [pqS, pqSc, pqI1, pqR, pqX, lCn, lSrc, lDst, lCi, lCz]

def pqBody (C : Ctx) : ProgHOL 64 := prologue pqLocals
  (.seq (.call (some (some (.local, pqS), none)) fStripPis [vv pqN, vv pqT])
  (.ite (.cmp .equal (vv pqS) (.const 0)) (.return (.const 0))
  (.seq (.assign .local pqSc (.load .one (vv pqS)))
  (.seq (.assign .local pqI1 (.op .sub [vv pqSc, .const 1]))
  (sliceCopyP C pqR pqS (.const 0) pqI1
  (.seq (.call (some (some (.local, pqX), none)) fListAnnEq [vv pqR, vv pqD, .const 0]) (.return (vv pqX))))))))

def beA := ofString "be_a"
def beB := ofString "be_b"
def beI := ofString "be_i"
def beNa := ofString "be_na"
def beNb := ofString "be_nb"
def beX := ofString "be_x"
def beY := ofString "be_y"
def beR := ofString "be_r"
def fBlkEq := ofString "blkEq"

def beParams : List MlS := [beA, beB, beI]
def beLocals : List MlS := [beNa, beNb, beX, beY, beR]

/-- Two heap blocks of handles equal from position `i` on. -/
def beBody : ProgHOL 64 := prologue beLocals
  (.seq (.assign .local beNa (.load .one (vv beA)))
  (.seq (.assign .local beNb (.load .one (vv beB)))
  (.ite (.cmp .lower (vv beI) (vv beNa))
    (.ite (.cmp .lower (vv beI) (vv beNb))
      (.seq (.assign .local beX (.load .one (.op .add [vv beA, .shift .lsl (.op .add [vv beI, .const 1]) (.const 3)])))
      (.seq (.assign .local beY (.load .one (.op .add [vv beB, .shift .lsl (.op .add [vv beI, .const 1]) (.const 3)])))
      (.ite (.cmp .equal (vv beX) (vv beY))
        (.seq (.call (some (some (.local, beR), none)) fBlkEq [vv beA, vv beB, .op .add [vv beI, .const 1]])
          (.return (vv beR)))
        (.return (.const 0)))))
      (.return (.const 0)))
    (.ite (.cmp .lower (vv beI) (vv beNb)) (.return (.const 0)) (.return (.const 1))))))

def prN := ofString "pr_n"
def prT := ofString "pr_t"
def prQ := ofString "pr_q"
def prPp := ofString "pr_pp"
def prP := ofString "pr_p"
def prD := ofString "pr_d"
def prX := ofString "pr_x"
def prY := ofString "pr_y"
def prR := ofString "pr_r"
def prF1 := ofString "pr_f1"
def prF2 := ofString "pr_f2"
def prU1 := ofString "pr_u1"
def prU2 := ofString "pr_u2"
def prTg := ofString "pr_tg"
def fIotaPartsRel := ofString "iotaPartsRel"

def prParams : List MlS := [prN, prT, prQ, prPp, prP, prD]
def prLocals : List MlS := [prX, prY, prR, prF1, prF2, prU1, prU2, prTg]

def prBody : ProgHOL 64 := prologue prLocals
  (.seq (.assign .local prX (.load .one (.op .add [vv prPp, .const 8])))
  (.seq (.assign .local prY (.load .one (.op .add [vv prP, .const 8])))
  (.seq (.call (some (some (.local, prR), none)) fBlkEq [vv prX, vv prY, .const 0])
  (.ite (veEqC prR 0) (.return (.const 0))
  (.seq (.assign .local prU1 (.load .one (.op .add [vv prPp, .const 16])))
  (.seq (.assign .local prU2 (.load .one (.op .add [vv prP, .const 16])))
  (.ite (.cmp .equal (vv prU1) (vv prU2))
    (.seq (.assign .local prX (.load .one (.op .add [vv prPp, .const 24])))
    (.seq (.assign .local prY (.load .one (.op .add [vv prP, .const 24])))
    (.seq (.call (some (some (.local, prR), none)) fBlkEq [vv prX, vv prY, .const 0])
    (.ite (veEqC prR 0) (.return (.const 0))
    (.seq (.assign .local prF1 (.load .one (vv prPp)))
    (.seq (.assign .local prF2 (.load .one (vv prP)))
    (.seq (.call (some (some (.local, prR), none)) fListLvlEq [vv prF1, vv prF2, .const 0])
    (.ite (veEqC prR 0)
      (.seq (.assign .local prTg (.load .one (.op .add [vv prQ, .const 16])))
      (.ite (veEqC prTg 0)
        (.seq (.call (some (some (.local, prR), none)) fParamsAnnEq [vv prN, vv prT, vv prD])
        (.ite (veEqC prR 0) (.return (.const 0))
        (.seq (.call (some (some (.local, prR), none)) fListAnnEq [vv prF1, vv prF2, .const 0]) (.return (vv prR)))))
        (.return (.const 0))))
      (.return (.const 1))))))))))
    (.return (.const 0)))))))))

section
variable {σ : Type}

theorem pq_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ pqLocals → (ctxEnv C ++ pqParams.zip vals).get x = none :=
  Knot.params_none C pqLocals pqParams vals (by decide) (by decide)

/-- **`paramsAnnEq`** against the context's environment. -/
theorem pq_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : Front.FrontOK C)
    (hc : AECodes C) (hAn : denoteN C.St.ns anonH = some .anonymous)
    (hcs : C.code.lookup fStripPis = some ([(pFu, .one), (pH, .one)], stripBody C fStripPis 6, .one))
    (hcl : C.code.lookup fListAnnEq = some (laParams.map (fun p => (p, ShapeHOL.one)), laBody, .one))
    (cnP : Nat) (hcn : cnP < 2 ^ 58) (cv : IConstantVal) (pd : List EIdx) (opd : Nat) (H : List (BitVec 64))
    (hpd : BlkAt H opd (pd.map Enc.idxW)) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (pqParams.zip [BitVec.ofNat 64 cnP, Enc.idxW cv.type, cellA C opd]))
      (pqBody C) s (paramsAnnEq C.fe cnP cv pd) (PostB (ctxH C H)) := by
  refine specR_prologue (postB_locals _) (pq_none _ _) ?_
  unfold paramsAnnEq
  let Γ0 : Env := ctxEnv (ctxH C H) ++ pqParams.zip [BitVec.ofNat 64 cnP, Enc.idxW cv.type, cellA C opd]
  have gN : Γ0.get pqN = some (BitVec.ofNat 64 cnP) := by simp +decide [Γ0, Env.get, pqParams, ctxEnv]
  have gT : Γ0.get pqT = some (Enc.idxW cv.type) := by simp +decide [Γ0, Env.get, pqParams, ctxEnv]
  have gD : Γ0.get pqD = some (cellA C opd) := by simp +decide [Γ0, Env.get, pqParams, ctxEnv]
  have vZ : Γ0.get lCz = none := pq_none (ctxH C H) _ lCz (by decide)
  refine ro_strip C hok hcs cnP (by omega) cv.type H s pqS (vv pqN) (vv pqT) (by simp +decide [ctxLocals, pqLocals])
    (by simp only [sev, sev_vv]; exact gN) (by simp only [sev, sev_vv]; exact gT) (fun o w s1 H1 hp1 hr1 hn1 hs1 => ?_)
  have hp1' : H <+: H1 := hp1
  rcases o with _ | ⟨rd, b⟩
  · have e0 := hn1 rfl
    subst e0
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  obtain ⟨oa, rfl, hba⟩ := hs1 rd b rfl
  obtain ⟨ha0, -, -⟩ := strip_last hba
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN => ?_)
  have hol := blkAt_lt hba
  have hHN' : H1.length ≤ C.HN := hHN
  have hne : cellA C oa ≠ 0 := cellA_ne0 C hok oa (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine UD.specR_heapLoadI' (C := ctxH C H1) pqSc (vv pqS) oa _ ha0 (by simp +decide [ctxLocals, pqLocals])
    (by simp [sev, Env.get_cons]; rfl) ?_
  refine specR_assignI pqI1 _ (BitVec.ofNat 64 rd.length) (by simp +decide [ctxLocals, pqLocals])
    (by
      have hbl := blkAt_len hba
      simp only [List.length_append, List.length_map, List.length_singleton] at hbl
      have hlay := hok.heapLay
      rw [sev_sub2 _ _ _ (BitVec.ofNat 64 (rd.length + 1)) _ (by simp [sev, Env.get_cons]) rfl]; congr 1
      apply BitVec.eq_of_toNat_eq; simp; omega) ?_
  refine specR_sliceCopyI hok pqR pqS (.const 0) pqI1 oa 0 rd.length (rd.map Enc.idxW ++ [Enc.idxW b])
    (by simp +decide [ctxLocals, pqLocals]) (by simp +decide [Env.get_cons]) (fun _ _ => rfl) (by simp)
    (by simp [Env.get_cons]) hba (by simp +decide [Env.get_cons]; exact vZ) (by decide) (by decide)
    (fun H5 o5 hp5 hl5 hb5 => ?_)
  have hfd : ((rd.map Enc.idxW ++ [Enc.idxW b]).drop 0).take rd.length = rd.map Enc.idxW := by simp
  rw [hfd] at hb5
  have hp5' : H1 <+: H5 := hp5
  refine specR_congr (m' := listAnnEq C.fe (rd.drop 0) (pd.drop 0) >>= fun r => pure r) (by simp) ?_
  refine specR_callNIH (C := ctxH C H5) pqX fListAnnEq laParams [vv pqR, vv pqD, .const 0] laBody
    [cellA C o5, cellA C opd, BitVec.ofNat 64 0] (by decide) rfl (by simp +decide [ctxLocals, pqLocals]) hcl
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons]; exact gD, rfl, trivial⟩
    (PostB (ctxH C H5)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu laParams _ rfl hlk)
      (la_spec ra C hok hf hc hAn hcl o5 opd rd pd _ 0 H5 s1 rfl (Nat.zero_le _) hb5
        (blkAt_mono hpd (hp1'.trans hp5'))))
    (fun r w s2 H6 hp6 hw => ?_)
  subst hw
  have hp6' : H5 <+: H6 := hp6
  exact specR_returnI _ _ (by simp [sev, Env.get_cons])
    (fun t ht => ⟨H6, (hp1'.trans hp5').trans hp6', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem be_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ beLocals → (ctxEnv C ++ beParams.zip vals).get x = none :=
  Knot.params_none C beLocals beParams vals (by decide) (by decide)

theorem beq_drop_cons (as bs : List EIdx) (i : Nat) (ha : i < as.length) (hb : i < bs.length) :
    (as.drop i == bs.drop i) = (as[i] == bs[i] && as.drop (i + 1) == bs.drop (i + 1)) := by
  rw [List.drop_eq_getElem_cons ha, List.drop_eq_getElem_cons hb]; rfl

theorem be_step (C : Ctx) (hok : CtxOK C)
    (hcl : C.code.lookup fBlkEq = some (beParams.map (fun p => (p, ShapeHOL.one)), beBody, .one))
    (pa pb : Nat) (as bs : List EIdx) (i : Nat) (H : List (BitVec 64)) (s : AState) (hi : i ≤ as.length)
    (hA : BlkAt H pa (as.map Enc.idxW)) (hB : BlkAt H pb (bs.map Enc.idxW))
    (rec : i < as.length →
      SpecR (Pre (σ := σ) (ctxH C H) s (beParams.zip [cellA C pa, cellA C pb, BitVec.ofNat 64 (i + 1)])) beBody s
        (pure (as.drop (i + 1) == bs.drop (i + 1))) (PostB (ctxH C H))) :
    SpecR (Pre (σ := σ) (ctxH C H) s (beParams.zip [cellA C pa, cellA C pb, BitVec.ofNat 64 i])) beBody s
      (pure (as.drop i == bs.drop i)) (PostB (ctxH C H)) := by
  refine specR_prologue (postB_locals _) (be_none _ _) ?_
  let Γ0 : Env := ctxEnv (ctxH C H) ++ beParams.zip [cellA C pa, cellA C pb, BitVec.ofNat 64 i]
  have gPa : Γ0.get beA = some (cellA C pa) := by simp +decide [Γ0, Env.get, beParams, ctxEnv]
  have gPb : Γ0.get beB = some (cellA C pb) := by simp +decide [Γ0, Env.get, beParams, ctxEnv]
  have gI : Γ0.get beI = some (BitVec.ofNat 64 i) := by simp +decide [Γ0, Env.get, beParams, ctxEnv]
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : H.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  have hla := blkAt_len hA
  have hlb := blkAt_len hB
  simp only [List.length_map] at hla hlb
  have hA0 : (ctxH C H).H[pa]? = some (BitVec.ofNat 64 as.length) := by show H[pa]? = _; rw [hA.1]; simp
  have hB0 : (ctxH C H).H[pb]? = some (BitVec.ofNat 64 bs.length) := by show H[pb]? = _; rw [hB.1]; simp
  refine UD.specR_heapLoadI' (C := ctxH C H) beNa (vv beA) pa _ hA0 (by simp +decide [ctxLocals, beLocals])
    (by simp only [sev, sev_vv]; exact gPa) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H) beNb (vv beB) pb _ hB0 (by simp +decide [ctxLocals, beLocals])
    (by simp only [sev, sev_vv, Env.get_cons]; simp +decide; exact gPb) ?_
  have gI' : sev ((beNb, BitVec.ofNat 64 bs.length) :: (beNa, BitVec.ofNat 64 as.length) :: Γ0) (vv beI) =
      some (BitVec.ofNat 64 i) := by simp only [sev, sev_vv, Env.get_cons]; simp +decide; exact gI
  have ret : ∀ (Γ : Env) (b : Bool) (w : BitVec 64), w = boolW b →
      SpecR (σ := σ) (Inv (ctxH C H) s Γ [] (ctxLocals ++ beLocals)) (.return (.const w)) s (pure b)
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
      rw [beq_drop_cons as bs i hia hib]
      have hxa : (ctxH C H).H[pa + 1 + i]? = some (Enc.idxW as[i]) := by
        have := hA.2 i (by simp; omega); show H[pa + 1 + i]? = _; simpa using this
      have hyb : (ctxH C H).H[pb + 1 + i]? = some (Enc.idxW bs[i]) := by
        have := hB.2 i (by simp; omega); show H[pb + 1 + i]? = _; simpa using this
      refine UD.specR_heapLoadI' (C := ctxH C H) beX _ (pa + 1 + i) _ hxa (by simp +decide [ctxLocals, beLocals])
        (by
          simp only [sev, sev_vv, Env.get_cons]; simp +decide
          simp only [Γ0] at gPa gI
          rw [gPa, gI]; simp
          show _ = cellA C (pa + 1 + i)
          apply BitVec.eq_of_toNat_eq; simp [cellA, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
          omega) ?_
      refine UD.specR_heapLoadI' (C := ctxH C H) beY _ (pb + 1 + i) _ hyb (by simp +decide [ctxLocals, beLocals])
        (by
          simp only [sev, sev_vv, Env.get_cons]; simp +decide
          simp only [Γ0] at gPb gI
          rw [gPb, gI]; simp
          show _ = cellA C (pb + 1 + i)
          apply BitVec.eq_of_toNat_eq; simp [cellA, BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
          omega) ?_
      by_cases hxy : as[i] = bs[i]
      · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hxy])
          (fun _ => ?_) (fun h => absurd h (by decide))
        simp only [hxy, beq_self_eq_true, Bool.true_and]
        refine specR_congr (m' := (pure (as.drop (i + 1) == bs.drop (i + 1)) : AM Bool) >>= fun r => pure r)
          (by simp) ?_
        refine specR_callNIH (C := ctxH C H) beR fBlkEq beParams [vv beA, vv beB, .op .add [vv beI, .const 1]]
          beBody [cellA C pa, cellA C pb, BitVec.ofNat 64 (i + 1)] (by decide) rfl
          (by simp +decide [ctxLocals, beLocals]) hcl
          ⟨by simp only [sev, sev_vv, Env.get_cons]; simp +decide; exact gPa,
            by simp only [sev, sev_vv, Env.get_cons]; simp +decide; exact gPb,
            by
              show sev _ _ = _
              rw [sev_add2 _ _ _ _ _ (by simp only [sev, sev_vv, Env.get_cons]; simp +decide; exact gI) rfl]
              exact congrArg some (word_add1_eq i), trivial⟩
          (PostB (ctxH C H)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp, hw, hsr⟩ => ⟨H', hp, hw, hsr⟩)
          (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu beParams _ rfl hlk) (rec hia))
          (fun r w s2 H2 hp2 hw => ?_)
        subst hw
        exact specR_returnI _ _ (by simp [sev, Env.get_cons])
          (fun t ht => ⟨H2, hp2, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
      · have hne : Enc.idxW as[i] ≠ Enc.idxW bs[i] := fun h => hxy (Enc.idxW_inj h)
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
          (fun h => absurd rfl h) (fun _ => ?_)
        have : (as[i] == bs[i]) = false := by simpa using hxy
        simp only [this, Bool.false_and]
        exact ret _ false 0 rfl
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

/-- **Block equality** of handle lists from position `i`. -/
theorem be_spec (C : Ctx) (hok : CtxOK C)
    (hcl : C.code.lookup fBlkEq = some (beParams.map (fun p => (p, ShapeHOL.one)), beBody, .one))
    (pa pb : Nat) (as bs : List EIdx) (H : List (BitVec 64)) (s : AState)
    (hA : BlkAt H pa (as.map Enc.idxW)) (hB : BlkAt H pb (bs.map Enc.idxW)) :
    ∀ k i, as.length - i = k → i ≤ as.length →
      SpecR (Pre (σ := σ) (ctxH C H) s (beParams.zip [cellA C pa, cellA C pb, BitVec.ofNat 64 i])) beBody s
        (pure (as.drop i == bs.drop i)) (PostB (ctxH C H)) := by
  intro k
  induction k with
  | zero =>
    intro i hk hi
    exact be_step C hok hcl pa pb as bs i H s hi hA hB (fun h => absurd h (by omega))
  | succ k ih =>
    intro i hk hi
    exact be_step C hok hcl pa pb as bs i H s hi hA hB (fun hia => ih (i + 1) (by omega) (by omega))

/-- A `blkEq` call from position `0`: the twin is left unchanged, the answer in `r`. -/
theorem be_call {β : Type} (C : Ctx) (hok : CtxOK C)
    (hcb : C.code.lookup fBlkEq = some (beParams.map (fun p => (p, ShapeHOL.one)), beBody, .one))
    {H : List (BitVec 64)} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {m : AM β}
    {R : β → BitVec 64 → AState → PState σ → Prop} (r x y : MlS) (pa pb : Nat) (as bs : List EIdx) (hr : r ∈ D)
    (hA : BlkAt H pa (as.map Enc.idxW)) (hB : BlkAt H pb (bs.map Enc.idxW))
    (gx : Γ.get x = some (cellA C pa)) (gy : Γ.get y = some (cellA C pb))
    (hk : ∀ H1, H <+: H1 → SpecR (Inv (ctxH C H1) s ((r, boolW (as == bs)) :: Γ) [] D) rest s m R) :
    SpecR (Inv (ctxH C H) s Γ M D) (.seq (.call (some (some (.local, r), none)) fBlkEq [vv x, vv y, .const 0]) rest)
      s m R := by
  refine specR_pureBind (as.drop 0 == bs.drop 0) ?_
  refine specR_callNIH (C := ctxH C H) r fBlkEq beParams [vv x, vv y, .const 0] beBody
    [cellA C pa, cellA C pb, BitVec.ofNat 64 0] (by decide) rfl hr hcb
    ⟨by simp only [sev, sev_vv]; exact gx, by simp only [sev, sev_vv]; exact gy, rfl, trivial⟩
    (fun a w s' st => (pure (as.drop 0 == bs.drop 0) : AM Bool) s = .ok (a, s') ∧ PostB (ctxH C H) a w s' st)
    (fun a w s' H' => a = (as.drop 0 == bs.drop 0) ∧ s' = s ∧ w = boolW a)
    (fun a w s' st ⟨hrun, H', hp, hw, hsr⟩ => by
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      obtain ⟨rfl, rfl⟩ := hrun
      exact ⟨H', hp, ⟨rfl, rfl, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (fun w hw => by
      subst hw
      exact be_spec C hok hcb pa pb as bs H s hA hB _ 0 rfl (Nat.zero_le _) _ (pre_of_lookups hu beParams _ rfl hlk)))
    (fun a w s1 H1 hp1 ⟨ha, hs, hw⟩ => ?_)
  subst ha hs hw
  simp only [List.drop_zero]
  exact hk H1 hp1

theorem pr_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ prLocals → (ctxEnv C ++ prParams.zip vals).get x = none :=
  Knot.params_none C prLocals prParams vals (by decide) (by decide)

/-- The code `iotaPartsRel` runs. -/
structure PRCodes (C : Ctx) : Prop where
  ae : AECodes C
  sp : C.code.lookup fStripPis = some ([(pFu, .one), (pH, .one)], stripBody C fStripPis 6, .one)
  la : C.code.lookup fListAnnEq = some (laParams.map (fun p => (p, ShapeHOL.one)), laBody, .one)
  pq : C.code.lookup fParamsAnnEq = some (pqParams.map (fun p => (p, ShapeHOL.one)), pqBody C, .one)
  be : C.code.lookup fBlkEq = some (beParams.map (fun p => (p, ShapeHOL.one)), beBody, .one)
  ll : C.code.lookup fListLvlEq = some (llParams.map (fun p => (p, ShapeHOL.one)), llBody, .one)

/-- **`iotaPartsRel`** against the context's environment. -/
theorem pr_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hf : Front.FrontOK C)
    (hc : PRCodes C) (hAn : denoteN C.St.ns anonH = some .anonymous)
    (cnP : Nat) (hcn : cnP < 2 ^ 58) (cv : IConstantVal) (rl : IRecRule) (pp p : IIotaParts) (pd : List EIdx)
    (oq opp op opd : Nat) (H : List (BitVec 64)) (hq : RuleE C.HB H oq rl) (hpp : PartsRep C H opp pp)
    (hp : PartsRep C H op p) (hpd : BlkAt H opd (pd.map Enc.idxW)) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (prParams.zip [BitVec.ofNat 64 cnP, Enc.idxW cv.type, cellA C oq, cellA C opp,
      cellA C op, cellA C opd])) prBody s (iotaPartsRel C.fe cnP cv rl pp p pd) (PostB (ctxH C H)) := by
  refine specR_prologue (postB_locals _) (pr_none _ _) ?_
  unfold iotaPartsRel
  let Γ0 : Env := ctxEnv (ctxH C H) ++ prParams.zip [BitVec.ofNat 64 cnP, Enc.idxW cv.type, cellA C oq, cellA C opp,
      cellA C op, cellA C opd]
  have gN : Γ0.get prN = some (BitVec.ofNat 64 cnP) := by simp +decide [Γ0, Env.get, prParams, ctxEnv]
  have gT : Γ0.get prT = some (Enc.idxW cv.type) := by simp +decide [Γ0, Env.get, prParams, ctxEnv]
  have gQ : Γ0.get prQ = some (cellA C oq) := by simp +decide [Γ0, Env.get, prParams, ctxEnv]
  have gPp : Γ0.get prPp = some (cellA C opp) := by simp +decide [Γ0, Env.get, prParams, ctxEnv]
  have gP : Γ0.get prP = some (cellA C op) := by simp +decide [Γ0, Env.get, prParams, ctxEnv]
  have gD : Γ0.get prD = some (cellA C opd) := by simp +decide [Γ0, Env.get, prParams, ctxEnv]
  obtain ⟨⟨f1, hf1, hbf1⟩, ⟨i1, hi1, hbi1⟩, hu1, ⟨q1, hq1, hbq1⟩⟩ := hpp
  obtain ⟨⟨f2, hf2, hbf2⟩, ⟨i2, hi2, hbi2⟩, hu2, ⟨q2, hq2, hbq2⟩⟩ := hp
  have ret0 : ∀ (H1 : List (BitVec 64)) (s1 : AState) (Γ : Env) (M : Mem), H <+: H1 →
      SpecR (σ := σ) (Inv (ctxH C H1) s1 Γ M (ctxLocals ++ prLocals)) (.return (.const 0)) s1 (pure false)
        (PostB (ctxH C H)) := fun H1 s1 Γ M hp1 =>
    specR_returnI _ 0 rfl (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  have addr : ∀ (o k : Nat), cellA C o + BitVec.ofNat 64 (8 * k) = cellA C (o + k) := fun o k => cellA_plus C o k
  -- the indices
  refine UD.specR_heapLoadI' (C := ctxH C H) prX _ (opp + 1) _ hi1 (by simp +decide [ctxLocals, prLocals])
    (by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gPp; rw [gPp]; simp; exact addr opp 1) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H) prY _ (op + 1) _ hi2 (by simp +decide [ctxLocals, prLocals])
    (by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gP; rw [gP]; simp; exact addr op 1) ?_
  refine be_call C hok hc.be prR prX prY i1 i2 pp.idx p.idx (by simp +decide [ctxLocals, prLocals]) hbi1 hbi2
    (by simp +decide [Env.get_cons]) (by simp [Env.get_cons]) (fun H1 hp1 => ?_)
  by_cases hidx : pp.idx = p.idx
  swap
  · have e : (pp.idx == p.idx) = false := by simpa using hidx
    rw [e]
    refine specR_ifI _ 1 (by simp +decide [veEqC, sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [Bool.false_eq_true, ite_false]
    exact ret0 H1 s _ _ hp1
  have e : (pp.idx == p.idx) = true := by simpa using hidx
  rw [e]
  refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only [ite_true]
  refine UD.specR_heapLoadI' (C := ctxH C H1) prU1 _ (opp + 2) _ (ConPanqueque.T.Decl.get_prefix hu1 hp1)
    (by simp +decide [ctxLocals, prLocals])
    (by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gPp; rw [gPp]; simp; exact addr opp 2) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H1) prU2 _ (op + 2) _ (ConPanqueque.T.Decl.get_prefix hu2 hp1)
    (by simp +decide [ctxLocals, prLocals])
    (by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gP; rw [gP]; simp; exact addr op 2) ?_
  by_cases hus : pp.us = p.us
  swap
  · have hne : Enc.idxW pp.us ≠ Enc.idxW p.us := fun h => hus (Enc.idxW_inj h)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun h => absurd rfl h) (fun _ => ?_)
    have e : (pp.us == p.us) = false := by simpa using hus
    simp only [e, Bool.false_eq_true, ite_false]
    exact ret0 H1 s _ _ hp1
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hus])
    (fun _ => ?_) (fun h => absurd h (by decide))
  have e2 : (pp.us == p.us) = true := by simpa using hus
  simp only [e2, ite_true]
  refine UD.specR_heapLoadI' (C := ctxH C H1) prX _ (opp + 3) _ (ConPanqueque.T.Decl.get_prefix hq1 hp1)
    (by simp +decide [ctxLocals, prLocals])
    (by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gPp; rw [gPp]; simp; exact addr opp 3) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H1) prY _ (op + 3) _ (ConPanqueque.T.Decl.get_prefix hq2 hp1)
    (by simp +decide [ctxLocals, prLocals])
    (by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gP; rw [gP]; simp; exact addr op 3) ?_
  refine be_call C hok hc.be prR prX prY q1 q2 pp.params p.params (by simp +decide [ctxLocals, prLocals])
    (blkAt_mono hbq1 hp1) (blkAt_mono hbq2 hp1) (by simp +decide [Env.get_cons]) (by simp [Env.get_cons])
    (fun H2 hp2 => ?_)
  have hp12 : H <+: H2 := hp1.trans hp2
  by_cases hps : pp.params = p.params
  swap
  · have e : (pp.params == p.params) = false := by simpa using hps
    rw [e]
    refine specR_ifI _ 1 (by simp +decide [veEqC, sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [Bool.false_eq_true, ite_false]
    exact ret0 H2 s _ _ hp12
  have e3 : (pp.params == p.params) = true := by simpa using hps
  rw [e3]
  refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only [ite_true]
  refine UD.specR_heapLoadI' (C := ctxH C H2) prF1 _ opp _ (ConPanqueque.T.Decl.get_prefix hf1 hp12)
    (by simp +decide [ctxLocals, prLocals])
    (by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gPp; rw [gPp]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H2) prF2 _ op _ (ConPanqueque.T.Decl.get_prefix hf2 hp12)
    (by simp +decide [ctxLocals, prLocals])
    (by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gP; rw [gP]; rfl) ?_
  refine specR_congr (m' := listLvlEq (pp.fieldDoms.drop 0) (p.fieldDoms.drop 0) >>= fun r =>
    if r = true then pure true else match rl.fire with
      | .plain => do if ← paramsAnnEq C.fe cnP cv pd then listAnnEq C.fe pp.fieldDoms p.fieldDoms else pure false
      | _ => pure false) (by simp only [List.drop_zero]; rfl) ?_
  refine specR_callNIH (C := ctxH C H2) prR fListLvlEq llParams [vv prF1, vv prF2, .const 0] llBody
    [cellA C f1, cellA C f2, BitVec.ofNat 64 0] (by decide) rfl (by simp +decide [ctxLocals, prLocals]) hc.ll
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], rfl, trivial⟩
    (PostB (ctxH C H2)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu llParams _ rfl hlk)
      (ll_spec C hok hc.ae.ve hc.ll f1 f2 pp.fieldDoms p.fieldDoms _ 0 H2 s rfl (Nat.zero_le _)
        (blkAt_mono hbf1 hp12) (blkAt_mono hbf2 hp12)))
    (fun r w s3 H3 hp3 hw => ?_)
  subst hw
  have hp13 : H <+: H3 := hp12.trans hp3
  rcases r
  swap
  · refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [ite_true]
    exact specR_returnI _ 1 rfl (fun t ht => ⟨H3, hp13, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  refine specR_ifI _ 1 (by simp +decide [veEqC, sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun _ => ?_) (fun h => absurd h (by decide))
  simp only [Bool.false_eq_true, ite_false]
  have hfire := (ConPanqueque.T.Decl.ruleE_mono hp13 hq).2.2.1
  rcases hfr : rl.fire with _ | ⟨lv, pins⟩ | lv <;> rw [hfr] at hfire <;> simp only []
  · -- plain
    refine UD.specR_heapLoadI' (C := ctxH C H3) prTg _ (oq + 2) _ hfire (by simp +decide [ctxLocals, prLocals])
      (by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gQ; rw [gQ]; simp; exact addr oq 2) ?_
    refine specR_ifI _ 1 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_callNIH (C := ctxH C H3) prR fParamsAnnEq pqParams [vv prN, vv prT, vv prD] (pqBody C)
      [BitVec.ofNat 64 cnP, Enc.idxW cv.type, cellA C opd] (by decide) rfl (by simp +decide [ctxLocals, prLocals]) hc.pq
      ⟨by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gN; exact gN,
        by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gT; exact gT,
        by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gD; exact gD, trivial⟩
      (PostB (ctxH C H3)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pqParams _ rfl hlk)
        (pq_spec ra C hok hf hc.ae hAn hc.sp hc.la cnP hcn cv pd opd H3 (blkAt_mono hpd hp13) s3))
      (fun r w s4 H4 hp4 hw => ?_)
    subst hw
    have hp14 : H <+: H4 := hp13.trans hp4
    rcases r
    · refine specR_ifI _ 1 (by simp +decide [veEqC, sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [Bool.false_eq_true, ite_false]
      exact ret0 H4 s4 _ _ hp14
    refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [ite_true]
    refine specR_congr (m' := listAnnEq C.fe (pp.fieldDoms.drop 0) (p.fieldDoms.drop 0) >>= fun r => pure r)
      (by simp) ?_
    refine specR_callNIH (C := ctxH C H4) prR fListAnnEq laParams [vv prF1, vv prF2, .const 0] laBody
      [cellA C f1, cellA C f2, BitVec.ofNat 64 0] (by decide) rfl (by simp +decide [ctxLocals, prLocals]) hc.la
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], rfl, trivial⟩
      (PostB (ctxH C H4)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu laParams _ rfl hlk)
        (la_spec ra C hok hf hc.ae hAn hc.la f1 f2 pp.fieldDoms p.fieldDoms _ 0 H4 s4 rfl (Nat.zero_le _)
          (blkAt_mono hbf1 (hp12.trans (hp3.trans hp4))) (blkAt_mono hbf2 (hp12.trans (hp3.trans hp4)))))
      (fun r w s5 H5 hp5 hw => ?_)
    subst hw
    exact specR_returnI _ _ (by simp [sev, Env.get_cons])
      (fun t ht => ⟨H5, hp14.trans hp5, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · -- nested
    refine UD.specR_heapLoadI' (C := ctxH C H3) prTg _ (oq + 2) _ hfire.1 (by simp +decide [ctxLocals, prLocals])
      (by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gQ; rw [gQ]; simp; exact addr oq 2) ?_
    refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact ret0 H3 s3 _ _ hp13
  · -- recorded levels
    refine UD.specR_heapLoadI' (C := ctxH C H3) prTg _ (oq + 2) _ hfire.1 (by simp +decide [ctxLocals, prLocals])
      (by simp +decide [sev, Env.get_cons]; simp only [Γ0] at gQ; rw [gQ]; simp; exact addr oq 2) ?_
    refine specR_ifI _ 0 (by simp +decide [veEqC, sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact ret0 H3 s3 _ _ hp13

end

end ConPanqueque.T.Ind
