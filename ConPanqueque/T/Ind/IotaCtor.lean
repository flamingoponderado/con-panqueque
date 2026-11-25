import ConPanqueque.T.Ind.IotaParts

/-!
# A rule's parts, read through its constructor (the parameters)

`iotaBVars rP n i`: the prefix variables `bvar (rP - 1 - j)` for `j` from `i` below `n`, as a block.
`iotaParamsAt rl rP cnP`: a nested rule's recorded parameters, else the prefix's first `min cnP rP` variables.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.Decl
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.ExSP

def ibR := ofString "ib_r"
def ibN := ofString "ib_n"
def ibI := ofString "ib_i"
def fIotaBVars := ofString "iotaBVars"

def ibParams : List MlS := [ibR, ibN, ibI]

def ibBody (C : Ctx) : ProgHOL 64 := prologue gaaLocals
  (.ite (.cmp .lower (vv ibI) (vv ibN))
    (.seq (.call (some (some (.local, lA1), none)) fInternBVar [.op .sub [.op .sub [vv ibR, .const 1], vv ibI]])
    (.seq (.call (some (some (.local, ExS.lY), none)) fIotaBVars [vv ibR, vv ibN, .op .add [vv ibI, .const 1]])
      (prependP C lA1)))
    (alloc1 C lW (.const 0) (.return (vv lW))))

section
variable {σ : Type}

theorem ib_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ gaaLocals → (ctxEnv C ++ ibParams.zip vals).get x = none :=
  Knot.params_none C gaaLocals ibParams vals (by decide) (by decide)

/-- **`iotaBVars`** from `i`. -/
theorem ib_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fIotaBVars = some (ibParams.map (fun p => (p, ShapeHOL.one)), ibBody C, .one))
    (hcb : C.code.lookup fInternBVar = some ([(lIw, .one)], bvarBody, .one))
    (rP n : Nat) (hn : n ≤ rP) (hr : rP < 2 ^ 62) :
    ∀ f i (H : List (BitVec 64)) (s : AState), n - i = f → i ≤ n →
      SpecR (σ := σ) (Pre (ctxH C H) s (ibParams.zip [BitVec.ofNat 64 rP, BitVec.ofNat 64 n, BitVec.ofNat 64 i]))
        (ibBody C) s (iotaBVars rP n i) (PostA (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i H s hf hi
    have hin : i = n := by omega
    subst hin
    refine specR_prologue (postA_locals _) (ib_none _ _) ?_
    rw [iotaBVars, if_neg (by omega)]
    have hlw := nd_lt_iff i i (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, ibParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by simp +decide [ctxLocals, gaaLocals, inst1Locals])
      (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
    exact specR_returnI _ _ (by simp [sev] <;> rfl) (fun t ht => ⟨_, H2.length, hp2.trans (img1_prefix _ _ _ hws), rfl,
      ⟨by simpa using img1_get H2 ws (0 : BitVec 64) hws, fun i hi => absurd hi (by simp)⟩,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi
    have hin : i < n := by omega
    refine specR_prologue (postA_locals _) (ib_none _ _) ?_
    rw [iotaBVars, if_pos hin]
    have hlw := nd_lt_iff i n (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ibParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_internBVarI ra (ctxOK_H hok H) hcb lA1 _ (rP - 1 - i) (by omega)
      (by simp +decide [ctxLocals, gaaLocals, inst1Locals])
      (by simp +decide [sev, Env.get, ibParams, ctxEnv]
          rw [ConPanqueque.T.ExP.word_sub_eq rP 1 (by omega) (by omega), ConPanqueque.T.ExP.word_sub_eq _ i (by omega) (by omega)])
      (fun b s1 => ?_)
    refine specR_congr (m' := iotaBVars rP n (i + 1) >>= fun rest => pure (b :: rest)) (by simp) ?_
    refine specR_callNIH (C := ctxH C H) ExS.lY fIotaBVars ibParams [vv ibR, vv ibN, .op .add [vv ibI, .const 1]]
      (ibBody C) [BitVec.ofNat 64 rP, BitVec.ofNat 64 n, BitVec.ofNat 64 (i + 1)] (by decide) rfl
      (by simp +decide [ctxLocals, gaaLocals, inst1Locals]) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, ibParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, ibParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, ibParams, ctxEnv]; exact word_add1_eq i, trivial⟩
      (PostA (ctxH C H)) (fun ys w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (ys.map Enc.idxW))
      (fun ys w s' st ⟨H', o, hp', hw, hbk, hsr⟩ => ⟨H', hp', ⟨o, hw, hbk⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ibParams _ rfl hlk)
        (ih (i + 1) H s1 (by omega) (by omega)))
      (fun ys wr s2 H2 hp2 ⟨oy, hwr, hblk⟩ => ?_)
    subst hwr
    exact prepend_spec C hok lA1 (Enc.idxW b) oy _ (by simp +decide [ctxLocals, gaaLocals, inst1Locals])
      (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) hblk (by decide)
      (by simp +decide [Env.get_cons, Env.get, ibParams, ctxEnv]) (by decide)
      (fun H' o t hpH hbk hsr => ⟨H', o, hp2.trans hpH, rfl, by simpa using hbk, hsr⟩)

end

def paQ := ofString "pa_q"
def paR := ofString "pa_r"
def paC := ofString "pa_c"
def paT := ofString "pa_t"
def paM1 := ofString "pa_m1"
def paM := ofString "pa_m"
def paX := ofString "pa_x"
def fIotaParams := ofString "iotaParamsAt"

def paParams : List MlS := [paQ, paR, paC]
def paLocals : List MlS := [paT, paM1, paM, paX]

def paBody : ProgHOL 64 := prologue paLocals
  (.seq (.assign .local paT (.load .one (.op .add [vv paQ, .const 16])))
  (.ite (.cmp .equal (vv paT) (.const 1))
    (.seq (.assign .local paX (.load .one (.op .add [vv paQ, .const 32]))) (.return (vv paX)))
    (.seq (.call (some (some (.local, paM1), none)) fTSub [vv paC, vv paR])
    (.seq (.call (some (some (.local, paM), none)) fTSub [vv paC, vv paM1])
    (.seq (.call (some (some (.local, paX), none)) fIotaBVars [vv paR, vv paM, .const 0])
      (.return (vv paX)))))))

section
variable {σ : Type}

theorem pa_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ paLocals → (ctxEnv C ++ paParams.zip vals).get x = none :=
  Knot.params_none C paLocals paParams vals (by decide) (by decide)

/-- **`iotaParamsAt`**, the rule a record at `oq`. -/
theorem pa_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fIotaParams = some (paParams.map (fun p => (p, ShapeHOL.one)), paBody, .one))
    (hcs : C.code.lookup fTSub = some ([(tsA, .one), (tsB, .one)], tsBody, .one))
    (hci : C.code.lookup fIotaBVars = some (ibParams.map (fun p => (p, ShapeHOL.one)), ibBody C, .one))
    (hcb : C.code.lookup fInternBVar = some ([(lIw, .one)], bvarBody, .one))
    (rl : IRecRule) (oq rP cnP : Nat) (hr : rP < 2 ^ 62) (hc' : cnP < 2 ^ 62)
    (H : List (BitVec 64)) (hq : RuleE C.HB H oq rl) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (paParams.zip [cellA C oq, BitVec.ofNat 64 rP, BitVec.ofNat 64 cnP])) paBody s
      (iotaParamsAt rl rP cnP) (PostA (ctxH C H)) := by
  refine specR_prologue (postA_locals _) (pa_none _ _) ?_
  unfold iotaParamsAt
  obtain ⟨-, -, hf, -⟩ := hq
  let Γ0 : Env := ctxEnv (ctxH C H) ++ paParams.zip [cellA C oq, BitVec.ofNat 64 rP, BitVec.ofNat 64 cnP]
  have hsQ : ∀ k, sev Γ0 (.op .add [vv paQ, .const (BitVec.ofNat 64 (8 * k))]) = some (cellA C (oq + k)) := by
    intro k; simp +decide [Γ0, sev, Env.get, paParams, ctxEnv]; exact cellA_plus C oq k
  have rest : ∀ (tw : BitVec 64), tw ≠ 1 → (∀ M, SpecR (σ := σ) (Inv (ctxH C H) s ((paT, tw) :: Γ0) M
      (ctxLocals ++ paLocals)) (.ite (.cmp .equal (vv paT) (.const 1))
        (.seq (.assign .local paX (.load .one (.op .add [vv paQ, .const 32]))) (.return (vv paX)))
        (.seq (.call (some (some (.local, paM1), none)) fTSub [vv paC, vv paR])
        (.seq (.call (some (some (.local, paM), none)) fTSub [vv paC, vv paM1])
        (.seq (.call (some (some (.local, paX), none)) fIotaBVars [vv paR, vv paM, .const 0])
          (.return (vv paX)))))) s (iotaBVars rP (min cnP rP) 0) (PostA (ctxH C H))) := by
    intro tw htw M
    refine specR_ifI _ 0 (by simp [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact htw)
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [show min cnP rP = cnP - (cnP - rP) by omega]
    refine specR_pureBind (cnP - rP) ?_
    refine rb_tsub (D := ctxLocals ++ paLocals) C hcs cnP rP (by omega) (by omega) H s paM1 (vv paC) (vv paR)
      (by simp +decide [ctxLocals, paLocals]) (by simp +decide [Γ0, sev, Env.get_cons, Env.get, paParams, ctxEnv])
      (by simp +decide [Γ0, sev, Env.get_cons, Env.get, paParams, ctxEnv]) (fun H1 hp1 => ?_)
    refine specR_pureBind (cnP - (cnP - rP)) ?_
    refine rb_tsub (D := ctxLocals ++ paLocals) C hcs cnP (cnP - rP) (by omega) (by omega) H1 s paM (vv paC) (vv paM1)
      (by simp +decide [ctxLocals, paLocals]) (by simp +decide [Γ0, sev, Env.get_cons, Env.get, paParams, ctxEnv])
      (by simp +decide [sev, Env.get_cons]) (fun H2 hp2 => ?_)
    refine specR_congr (m' := iotaBVars rP (cnP - (cnP - rP)) 0 >>= fun r => pure r) (by simp) ?_
    refine specR_callNIH (C := ctxH C H2) paX fIotaBVars ibParams [vv paR, vv paM, .const 0] (ibBody C)
      [BitVec.ofNat 64 rP, BitVec.ofNat 64 (cnP - (cnP - rP)), BitVec.ofNat 64 0] (by decide) rfl
      (by simp +decide [ctxLocals, paLocals]) hci
      ⟨by simp +decide [Γ0, sev, Env.get_cons, Env.get, paParams, ctxEnv], by simp +decide [sev, Env.get_cons], rfl, trivial⟩
      (PostA (ctxH C H2)) (fun ys w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (ys.map Enc.idxW))
      (fun ys w s' st ⟨H', o, hp', hw, hbk, hsr⟩ => ⟨H', hp', ⟨o, hw, hbk⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ibParams _ rfl hlk)
        (ib_spec ra C hok hci hcb rP (cnP - (cnP - rP)) (by omega) hr _ 0 H2 s rfl (by omega)))
      (fun ys wr s2 H3 hp3 ⟨oy, hwr, hblk⟩ => ?_)
    subst hwr
    exact specR_returnI _ _ (by simp [sev, Env.get_cons] <;> rfl) (fun t ht => ⟨H3, oy, (hp1.trans hp2).trans hp3, rfl, hblk,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  rcases hrf : rl.fire with _ | ⟨lv, pins⟩ | lv <;> rw [hrf] at hf <;> simp only []
  · -- plain
    refine UD.specR_heapLoadI' (C := ctxH C H) paT _ (oq + 2) _ hf (by simp +decide [ctxLocals, paLocals]) (hsQ 2) ?_
    exact rest 0 (by decide) _
  · -- nested: the recorded parameters
    obtain ⟨h1, -, ⟨w, hw, hpins⟩⟩ := hf
    refine UD.specR_heapLoadI' (C := ctxH C H) paT _ (oq + 2) _ h1 (by simp +decide [ctxLocals, paLocals]) (hsQ 2) ?_
    refine specR_ifI _ 1 (by simp [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    obtain ⟨op, hwo, hpb⟩ := hpins
    have hw4 : (ctxH C H).H[oq + 4]? = some (cellA C op) := by
      show H[oq + 4]? = _; rw [show oq + 4 = oq + 2 + 2 by omega, hw, hwo]; rfl
    refine UD.specR_heapLoadI' (C := ctxH C H) paX _ (oq + 4) _ hw4 (by simp +decide [ctxLocals, paLocals])
      (by simp +decide [Γ0, sev, Env.get_cons, Env.get, paParams, ctxEnv]; exact cellA_plus C oq 4) ?_
    exact specR_returnI _ _ (by simp [sev, Env.get_cons] <;> rfl) (fun t ht => ⟨H, op, List.prefix_refl _, rfl, hpb,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · -- recorded levels
    obtain ⟨h1, -⟩ := hf
    refine UD.specR_heapLoadI' (C := ctxH C H) paT _ (oq + 2) _ h1 (by simp +decide [ctxLocals, paLocals]) (hsQ 2) ?_
    exact rest 2 (by decide) _

end

def clQ := ofString "cl_q"
def clL := ofString "cl_l"
def clT := ofString "cl_t"
def clW := ofString "cl_w"
def clD := ofString "cl_d"
def clR := ofString "cl_r"
def fCtorLevels := ofString "ctorLevelsAt"

def clParams : List MlS := [clQ, clL]
def clLocals : List MlS := [clT, clW, clD, clR, lSrc, lDst, lCi, lCz, lCn]

def clBody (C : Ctx) : ProgHOL 64 := prologue clLocals
  (.seq (.assign .local clT (.load .one (.op .add [vv clQ, .const 16])))
  (.ite (.cmp .equal (vv clT) (.const 0))
    (.seq (.call (some (some (.local, clR), none)) fParamLevels [vv clL]) (.return (vv clR)))
    (.seq (.assign .local clW (.load .one (.op .add [vv clQ, .const 24])))
    (.seq (.assign .local lCn (.load .one (vv clW)))
    (allocP C clD (.op .add [.panop .mul [vv lCn, .const 8], .const 8])
    (.seq (.assign .local lSrc (.op .add [vv clW, .const 8]))
    (.seq (.assign .local lDst (vv clD))
    (.seq (.assign .local lCi (.const 0))
    (.seq copyLoop
    (.seq (.call (some (some (.local, clR), none)) fInternLs [vv clD, vv lCn]) (.return (vv clR))))))))))))

section
variable {σ : Type}

theorem cl_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ clLocals → (ctxEnv C ++ clParams.zip vals).get x = none :=
  Knot.params_none C clLocals clParams vals (by decide) (by decide)

/-- The recorded levels `lvs` (a list block at `ow`), copied and interned. -/
theorem clLevels_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcIs : C.code.lookup fInternLs = some ([(pKey, .one), (lEc, .one)], internLsBody, .one))
    (lvs : List LIdx) (ow : Nat) (H : List (BitVec 64)) (s : AState) (Γ : Env) (M : Mem)
    (hb : EBlk H ow (lvs.map Enc.idxW)) (hw : Γ.get clW = some (cellA C ow)) (hz : Γ.get lCz = none) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ clLocals))
      (.seq (.assign .local lCn (.load .one (vv clW)))
      (allocP C clD (.op .add [.panop .mul [vv lCn, .const 8], .const 8])
      (.seq (.assign .local lSrc (.op .add [vv clW, .const 8]))
      (.seq (.assign .local lDst (vv clD))
      (.seq (.assign .local lCi (.const 0))
      (.seq copyLoop
      (.seq (.call (some (some (.local, clR), none)) fInternLs [vv clD, vv lCn]) (.return (vv clR)))))))))
      s (internLsNode lvs) (PostLsH (ctxH C H)) := by
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hHN' : H.length ≤ C.HN := hHN
  have hlay := hok.heapLay
  have hbl := blkAt_len hb
  simp only [List.length_map] at hbl
  have hc0 : (ctxH C H).H[ow]? = some (BitVec.ofNat 64 lvs.length) := by show H[ow]? = _; rw [hb.1]; simp
  refine UD.specR_heapLoadI' (C := ctxH C H) lCn (vv clW) ow _ hc0 (by simp +decide [ctxLocals, clLocals])
    (by simp only [sev, sev_vv, hw]; rfl) ?_
  refine specR_allocI (C := ctxH C H) clD _ (lvs.length + 1) (by omega) (by simp +decide [ctxLocals, clLocals])
    (fun v => by simp +decide [sev, Env.get_cons]; apply BitVec.eq_of_toNat_eq; simp; omega)
    (fun H1 ws hp1 hws hroom1 => ?_)
  have hp1' : H <+: H1 := hp1
  have hl1 := hp1'.length_le
  have hn : lvs.length < 2 ^ 60 := by
    have : (ctxH C H).HN = C.HN := rfl
    omega
  refine specR_assignI lSrc _ (cellA C (ow + 1 + 0)) (by simp +decide [ctxLocals, clLocals])
    (by simp only [sev, sev_vv, Env.get_cons, show clW ≠ clD by decide, show clW ≠ lCn by decide, ite_false, hw]
        simp; exact cellA_add8 C ow) ?_
  refine specR_assignI lDst _ (cellA C (H1.length + 0)) (by simp +decide [ctxLocals, clLocals])
    (by simp [sev, Env.get_cons]; rfl) ?_
  refine specR_assignI lCi (.const 0) (BitVec.ofNat 64 0) (by simp +decide [ctxLocals, clLocals]) rfl ?_
  refine specR_mono (P := Inv (ctxH C (H1 ++ ws)) s _ [] (ctxLocals ++ clLocals)) ?_
    (fun t ht => ⟨ht.sr, ht.env, fun _ _ h => (nomatch h), ht.decl⟩) (fun _ _ _ _ h => h)
  refine specR_copyI (D := ctxLocals ++ clLocals) hok (H1 ++ ws) (lvs.map Enc.idxW) (ow + 1) H1.length
    ⟨by simp +decide [ctxLocals, clLocals], by simp +decide [ctxLocals, clLocals], by simp +decide [ctxLocals, clLocals],
      by simp +decide [ctxLocals, clLocals]⟩
    (fun j hj => by
      have := hb.2 j hj
      rw [List.getElem?_append_left (by have := blkAt_len hb; simp at this hj; omega)]
      exact get_prefix this hp1')
    (by simp; omega) (by simp [hws]) (by simp; omega) ?_ (by decide) ?_ ?_
  · simp +decide [Env.get_cons]
  · simp +decide [Env.get_cons, hz]
  generalize hF : fillI (H1 ++ ws) (lvs.map Enc.idxW) H1.length (lvs.map Enc.idxW).length = F
  have hFlen : F.length = (H1 ++ ws).length := by rw [← hF, fillI_length]
  have hFg : ∀ k, F[k]? = if H1.length ≤ k ∧ k < H1.length + lvs.length ∧ k < (H1 ++ ws).length
      then some ((lvs.map Enc.idxW).getD (k - H1.length) 0) else (H1 ++ ws)[k]? := by
    intro k; rw [← hF, fillI_get?]; simp
  have hp1F : H1 <+: F := prefix_of_get? (by simp [hFlen]) (fun k hk => by
    rw [hFg k, ite_eq_right (by omega), List.getElem?_append_left hk])
  have hcells : ∀ j (hj : j < lvs.length), F[H1.length + j]? = some (Enc.idxW lvs[j]) := by
    intro j hj
    rw [hFg, ite_eq_left ⟨by omega, by omega, by simp [hws]; omega⟩]
    simp [List.getD_eq_getElem?_getD, hj]
  refine specR_congr (m' := internLsNode lvs >>= fun r => pure r) (by rw [bind_pure]) ?_
  refine specR_callNIA (C := ctxH (ctxH C (H1 ++ ws)) F) clR fInternLs [pKey, lEc] [vv clD, vv lCn] internLsBody
    [cellA C H1.length, BitVec.ofNat 64 lvs.length] (by decide) rfl (by simp +decide [ctxLocals, clLocals]) hcIs
    ⟨by simp +decide [sev, Env.get_cons] <;> rfl, by simp +decide [sev, Env.get_cons], trivial⟩
    (fun a w s' st => internLsNode lvs s = .ok (a, s') ∧ PostLs (ctxH (ctxH C F) H1) a w s' st)
    (fun a w s' H' => H' = H1 ∧ internLsNode lvs s = .ok (a, s') ∧ w = Enc.idxW a)
    (fun a w s' st ⟨hr, hw, hsr⟩ => ⟨H1, ⟨rfl, hr, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (fun w' hw' => by
      subst hw'
      exact internLs_body_spec ra (ctxH C F) (ctxOK_H hok F) s lvs H1.length H1 hp1F (Nat.le_refl _)
        (by show H1.length + lvs.length ≤ F.length; rw [hFlen]; simp [hws]) hn
        (fun j hj => hcells j hj) _ (pre_of_lookups hu [pKey, lEc] _ rfl hlk)))
    (fun h w2 s2 H' ⟨e, hr2, hw⟩ => ?_)
  subst e; subst hw
  exact specR_returnI (vv clR) (Enc.idxW h) (by simp) (fun t ht => ⟨_, hp1', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- **`ctorLevelsAt rl ctorLps`**: the recorded levels of a nested/levels rule, else the constructor's parameters. -/
theorem cl_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hcl : C.code.lookup fParamLevels = some (plParams.map (fun p => (p, ShapeHOL.one)), plBody C, .one))
    (hc : C.code.lookup fPlFill = some (pfParams.map (fun p => (p, ShapeHOL.one)), pfBody, .one))
    (hcP : C.code.lookup fInternLParam = some ([(lEn, .one)], internLParamBody, .one))
    (hcIs : C.code.lookup fInternLs = some ([(pKey, .one), (lEc, .one)], internLsBody, .one))
    (rl : IRecRule) (ctorLps : List NIdx) (hn : ctorLps.length < 2 ^ 59) (oq ol : Nat)
    (H : List (BitVec 64)) (hq : RuleE C.HB H oq rl) (hbl : EBlk H ol (ctorLps.map Enc.idxW)) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (clParams.zip [cellA C oq, cellA C ol])) (clBody C) s
      (ctorLevelsAt rl ctorLps) (PostLsH (ctxH C H)) := by
  refine specR_prologue (postLsH_locals _) (cl_none _ _) ?_
  unfold ctorLevelsAt
  obtain ⟨-, -, hf, -⟩ := hq
  let Γ0 : Env := ctxEnv (ctxH C H) ++ clParams.zip [cellA C oq, cellA C ol]
  have hsQ : ∀ k, sev Γ0 (.op .add [vv clQ, .const (BitVec.ofNat 64 (8 * k))]) = some (cellA C (oq + k)) := by
    intro k; simp +decide [Γ0, sev, Env.get, clParams, ctxEnv]; exact cellA_plus C oq k
  have rest : ∀ (tw : BitVec 64) (lv : List LIdx) (w : BitVec 64), tw ≠ 0 → H[oq + 2 + 1]? = some w →
      ENList C.HB H w lv → ∀ M, SpecR (σ := σ) (Inv (ctxH C H) s ((clT, tw) :: Γ0) M (ctxLocals ++ clLocals))
      (.ite (.cmp .equal (vv clT) (.const 0))
        (.seq (.call (some (some (.local, clR), none)) fParamLevels [vv clL]) (.return (vv clR)))
        (.seq (.assign .local clW (.load .one (.op .add [vv clQ, .const 24])))
        (.seq (.assign .local lCn (.load .one (vv clW)))
        (allocP C clD (.op .add [.panop .mul [vv lCn, .const 8], .const 8])
        (.seq (.assign .local lSrc (.op .add [vv clW, .const 8]))
        (.seq (.assign .local lDst (vv clD))
        (.seq (.assign .local lCi (.const 0))
        (.seq copyLoop
        (.seq (.call (some (some (.local, clR), none)) fInternLs [vv clD, vv lCn]) (.return (vv clR)))))))))))
      s (internLsNode lv) (PostLsH (ctxH C H)) := by
    intro tw lv w htw hw ⟨o', hwo, heb⟩ M
    refine specR_ifI _ 0 (by simp [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact htw)
      (fun h => absurd rfl h) (fun _ => ?_)
    have hw3 : (ctxH C H).H[oq + 3]? = some (cellA C o') := by
      show H[oq + 3]? = _; rw [show oq + 3 = oq + 2 + 1 by omega, hw, hwo]; rfl
    refine UD.specR_heapLoadI' (C := ctxH C H) clW _ (oq + 3) _ hw3 (by simp +decide [ctxLocals, clLocals])
      (by simp +decide [Γ0, sev, Env.get_cons, Env.get, clParams, ctxEnv]; exact cellA_plus C oq 3) ?_
    exact clLevels_spec ra C hok hcIs lv o' H s _ M heb (by simp [Env.get_cons])
      (by simp +decide only [Env.get_cons, ite_false]; exact cl_none (ctxH C H) _ lCz (by decide))
  rcases hrf : rl.fire with _ | ⟨lv, pins⟩ | lv <;> rw [hrf] at hf <;> simp only []
  · -- plain
    refine UD.specR_heapLoadI' (C := ctxH C H) clT _ (oq + 2) _ hf (by simp +decide [ctxLocals, clLocals]) (hsQ 2) ?_
    refine specR_ifI _ 1 (by simp [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    refine specR_congr (m' := paramLevels ctorLps >>= fun r => pure r) (by rw [bind_pure]) ?_
    refine specR_callNIH (C := ctxH C H) clR fParamLevels plParams [vv clL] (plBody C) [cellA C ol] (by decide) rfl
      (by simp +decide [ctxLocals, clLocals]) hcl
      ⟨by simp +decide [Γ0, sev, Env.get_cons, Env.get, clParams, ctxEnv], trivial⟩
      (PostLsH (ctxH C H)) (fun a w _ _ => w = Enc.idxW a)
      (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu plParams _ rfl hlk)
        (pl_spec ra C hok hcl hc hcP hcIs ctorLps ol hn H s hbl))
      (fun a w s1 H1 hp1 hw => ?_)
    subst hw
    exact specR_returnI (vv clR) _ (by simp) (fun t ht => ⟨_, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · -- nested
    obtain ⟨h1, ⟨w, hw, hl⟩, -⟩ := hf
    refine UD.specR_heapLoadI' (C := ctxH C H) clT _ (oq + 2) _ h1 (by simp +decide [ctxLocals, clLocals]) (hsQ 2) ?_
    exact rest 1 lv w (by decide) hw hl _
  · -- recorded levels
    obtain ⟨h1, w, hw, hl⟩ := hf
    refine UD.specR_heapLoadI' (C := ctxH C H) clT _ (oq + 2) _ h1 (by simp +decide [ctxLocals, clLocals]) (hsQ 2) ?_
    exact rest 2 lv w (by decide) hw hl _

end

end ConPanqueque.T.Ind
