import ConPanqueque.T.Ind.BlockFormers
import ConPanqueque.T.Ind.BlockEnv

/-!
# `blockReadsAt`

Phase A runs the twin's effects in its order, into value-heap blocks: the formers' never-zero bits (`zfFill`) and the
recursors' firing modes (`ffFill`, twice, as the twin reads `blockRecs` twice). Phase B writes the block's constants'
environment records and the block table, and `recsRead` reads the recursors through the block-aware finder.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.Decl

def zfMs := ofString "zf_ms"
def zfD := ofString "zf_d"
def zfI := ofString "zf_i"
def zfK := ofString "zf_k"
def zfO := ofString "zf_o"
def zfDc := ofString "zf_dc"
def zfZ := ofString "zf_z"
def zfR := ofString "zf_r"
def fZfFill := ofString "nzFill"

def zfParams : List MlS := [zfMs, zfD, zfI, zfK]
def zfLocals : List MlS := [zfO, zfDc, zfZ, zfR]

/-- The members' never-zero bits (pointer block at `zfMs`, from `zfI`) into the block at `zfD`. -/
def zfBody : ProgHOL 64 := prologue zfLocals
  (.ite (.cmp .lower (vv zfI) (vv zfK))
    (.seq (.assign .local zfO (.load .one (.op .add [vv zfMs, .op .add [.panop .mul [vv zfI, .const 8], .const 8]])))
    (.seq (.assign .local zfDc (.load .one (.op .add [vv zfO, .const 8])))
    (.seq (.call (some (some (.local, zfZ), none)) fMemberNZ [vv zfDc])
    (.seq (.store (.op .add [vv zfD, .op .add [.panop .mul [vv zfI, .const 8], .const 8]]) (vv zfZ))
    (.seq (.call (some (some (.local, zfR), none)) fZfFill [vv zfMs, vv zfD, .op .add [vv zfI, .const 1], vv zfK])
      (.return (.const 0)))))))
    (.return (.const 0)))

section
variable {σ : Type}

/-- The never-zero bits from position `i` on, past the frozen prefix `Hc`. -/
def PostZF (C : Ctx) (Hc : List (BitVec 64)) (d i : Nat) (nzs : List Bool) (_ : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  ∃ H', Hc <+: H' ∧ SR (ctxH C H') s' st ∧ ∀ j (hj : j < nzs.length), H'[d + 1 + i + j]? = some (boolW nzs[j])

theorem postZF_locals (C : Ctx) (Hc : List (BitVec 64)) (d i : Nat) :
    ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostZF C Hc d i a w s' st → PostZF C Hc d i a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', hp, hs, h⟩ => ⟨H', hp, sr_of_eq hs rfl rfl rfl rfl, h⟩

theorem zf_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ zfLocals → (ctxEnv C ++ zfParams.zip vals).get x = none :=
  Knot.params_none C zfLocals zfParams vals (by decide) (by decide)

/-- **`nzFill`**: the members' never-zero bits from position `i`. -/
theorem zf_spec (C : Ctx) (hok : CtxOK C) (hmv : MVCodes C)
    (hcm : C.code.lookup fMemberNZ = some (mvParams.map (fun p => (p, ShapeHOL.one)), mvBody, .one))
    (hcode : C.code.lookup fZfFill = some (zfParams.map (fun p => (p, ShapeHOL.one)), zfBody, .one))
    (ms : List MemberShape) (om d : Nat) (H0 : List (BitVec 64)) (hms : PtrsRep C H0 om (MemberRep C H0) ms) :
    ∀ k i (H Hc : List (BitVec 64)) (s : AState), ms.length - i = k → i ≤ ms.length → H0 <+: Hc →
      Hc.length ≤ d + 1 + i → Hc <+: H → d + 1 + ms.length ≤ H.length →
      SpecR (Pre (σ := σ) (ctxH C H) s (zfParams.zip [cellA C om, cellA C d, BitVec.ofNat 64 i,
        BitVec.ofNat 64 ms.length])) zfBody s
        ((ms.drop i).mapM fun m => formerZ m.declared >>= fun z => pure z.isNever) (PostZF C Hc d i) := by
  intro k
  induction k with
  | zero =>
    intro i H Hc s hk hi h0 hHc hp hl
    refine specR_prologue (postZF_locals _ _ _ _) (zf_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, zfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_of_length_le (by omega)]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, hp, sr_of_eq ht.sr rfl rfl rfl rfl, fun j hj => by simp at hj⟩)
  | succ k ih =>
    intro i H Hc s hk hi h0 hHc hp hl
    have hil : i < ms.length := by omega
    refine specR_prologue (postZF_locals _ _ _ _) (zf_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i ms.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, zfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have h0H := h0.trans hp
    obtain ⟨oi, h1, hmr⟩ := hms.2 i hil
    obtain ⟨od, hod, hcv⟩ := hmr.2.1
    refine UD.specR_heapLoadI' (C := ctxH C H) zfO _ (om + 1 + i) _ (get_prefix h1 h0H) (by decide)
      (by simp +decide [sev, Env.get, zfParams, ctxEnv]; exact cellA_mulIdx C om i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) zfDc _ (oi + 1) _ (get_prefix hod h0H) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C oi) ?_
    rw [List.drop_eq_getElem_cons hil, List.mapM_cons]
    refine specR_callNIH (C := ctxH C H) zfZ fMemberNZ mvParams [vv zfDc] mvBody [cellA C od] (by decide) rfl
      (by decide) hcm ⟨by simp +decide [sev, Env.get], trivial⟩
      (PostB (ctxH C H)) (fun r w _ _ => w = boolW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mvParams _ rfl hlk)
        (mv_spec (ctxH C H) ⟨hmv.fs, hmv.pir, hmv.nz⟩ ms[i].declared od H (List.prefix_refl _)
          (cvRep_mono h0H hcv) s))
      (fun y w s1 H1 hp1 hw => ?_)
    subst hw
    have hp1' : H <+: H1 := hp1
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN1 => ?_)
    have hHN1' : H1.length ≤ C.HN := hHN1
    have hj : d + 1 + i < (ctxH C H1).H.length := by show d + 1 + i < H1.length; have := hp1'.length_le; omega
    refine specR_heapStoreI (ctxOK_H hok H1) _ (vv zfZ) (d + 1 + i) hj (boolW y)
      (by simp +decide [sev, Env.get_cons, Env.get, zfParams, ctxEnv]; exact cellA_mulIdx C d i (by omega))
      (by simp [sev, Env.get_cons]) ?_
    change SpecR (Inv (ctxH C (H1.set (d + 1 + i) (boolW y))) _ _ _ _) _ _ _ _
    generalize hB : H1.set (d + 1 + i) (boolW y) = B
    have hBl : B.length = H1.length := by rw [← hB]; simp
    have hBi : B[d + 1 + i]? = some (boolW y) := by
      rw [← hB, List.getElem?_set_self (by have := hp1'.length_le; omega)]
    have hpB : Hc <+: B := by
      refine prefix_of_get? (by have := hp.length_le; have := hp1'.length_le; omega) (fun j hj => ?_)
      rw [← hB, List.getElem?_set_ne (by omega), List.getElem?_eq_getElem hj]
      exact get_prefix (List.getElem?_eq_getElem hj) (hp.trans hp1')
    let Hc' := B.take (d + 2 + i)
    have hpc' : Hc' <+: B := List.take_prefix _ _
    have hHcc : Hc <+: Hc' := by
      refine prefix_of_get? (by simp [Hc']; have := hp.length_le; have := hp1'.length_le; omega) (fun j hj => ?_)
      simp only [Hc']; rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj]
      exact get_prefix (List.getElem?_eq_getElem hj) hpB
    refine specR_callNIG (C := ctxH C B) zfR fZfFill zfParams
      [vv zfMs, vv zfD, .op .add [vv zfI, .const 1], vv zfK] zfBody
      [cellA C om, cellA C d, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 ms.length] (by decide) rfl (by decide) hcode
      ⟨by simp +decide [sev, Env.get_cons, Env.get, zfParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, zfParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, zfParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, zfParams, ctxEnv], trivial⟩
      (PostZF C Hc' d (i + 1))
      (fun ys w s' H' => Hc' <+: H' ∧ ∀ j (hj : j < ys.length), H'[d + 1 + (i + 1) + j]? = some (boolW ys[j]))
      (fun ys w s' st ⟨H', hp', hs', hc'⟩ => ⟨H', ⟨hp', hc'⟩, hs'⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu zfParams _ rfl hlk)
        (ih (i + 1) B Hc' s1 (by omega) (by omega) (h0.trans hHcc) (by simp [Hc']; omega) hpc'
          (by have := hp1'.length_le; omega)))
      (fun ys w s2 H' ⟨hp', hc'⟩ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H', hHcc.trans hp', sr_of_eq ht.sr rfl rfl rfl rfl, fun j hj => by
      rcases j with _ | j
      · have := get_prefix (show Hc'[d + 1 + i]? = some (boolW y) by
          simp only [Hc']; rw [List.getElem?_take_of_lt (by omega)]; exact hBi) hp'
        simpa using this
      · have := hc' j (by simp at hj; omega)
        rw [show d + 1 + (i + 1) + j = d + 1 + i + (j + 1) by omega] at this
        simpa using this⟩)

end

def ffRs := ofString "ff_rs"
def ffI := ofString "ff_i"
def ffN := ofString "ff_n"
def ffK := ofString "ff_k"
def ffR := ofString "ff_r"
def ffCv := ofString "ff_cv"
def ffTg := ofString "ff_tg"
def ffMi := ofString "ff_mi"
def ffRp := ofString "ff_rp"
def ffTy := ofString "ff_ty"
def ffF := ofString "ff_f"
def ffP := ofString "ff_p"
def ffX := ofString "ff_x"
def fFfFill := ofString "fireFill"

def ffParams : List MlS := [ffRs, ffI, ffN, ffK]
def ffLocals : List MlS := [ffR, ffCv, ffTg, ffMi, ffRp, ffTy, ffF, ffP, ffX]

/-- The recursors' firing modes (pointer block at `ffRs`, from `ffI`), into a block allocated once every mode is
read: the block's pointer is returned. -/
def ffBody (C : Ctx) : ProgHOL 64 := prologue ffLocals
  (.ite (.cmp .lower (vv ffI) (vv ffN))
    (.seq (.assign .local ffR (.load .one (.op .add [vv ffRs, .op .add [.panop .mul [vv ffI, .const 8], .const 8]])))
    (.seq (.assign .local ffCv (.load .one (vv ffR)))
    (.seq (.assign .local ffRp (.load .one (.op .add [vv ffR, .const 8])))
    (.seq (.assign .local ffMi (.load .one (.op .add [vv ffR, .const 16])))
    (.seq (.assign .local ffTg (.load .one (.op .add [vv ffR, .const 24])))
    (.seq (.assign .local ffTy (.load .one (.op .add [vv ffCv, .const 16])))
    (.seq (.call (some (some (.local, ffF), none)) fRecFire [vv ffTg, vv ffK, vv ffMi, vv ffRp, vv ffTy])
    (.seq (.call (some (some (.local, ffP), none)) fFfFill [vv ffRs, .op .add [vv ffI, .const 1], vv ffN, vv ffK])
    (.seq (.store (.op .add [vv ffP, .op .add [.panop .mul [vv ffI, .const 8], .const 8]]) (vv ffF))
      (.return (vv ffP)))))))))))
    (allocP C ffX (.shift .lsl (.op .add [vv ffN, .const 1]) (.const 3))
      (.seq (.store (vv ffX) (vv ffN)) (.return (vv ffX)))))

section
variable {σ : Type}

/-- The firing modes from position `i` on, in a block allocated past every mode's record. -/
def PostFF (C : Ctx) (n i : Nat) (fs : List IRecRuleFire) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' Hf od, C.H <+: Hf ∧ Hf <+: H' ∧ Hf.length ≤ od ∧ w = cellA C od ∧ H'[od]? = some (BitVec.ofNat 64 n) ∧
    od + 1 + n ≤ H'.length ∧ SR (ctxH C H') s' st ∧
    ∀ j (hj : j < fs.length), ∃ o, H'[od + 1 + i + j]? = some (cellA C o) ∧ FireE C.HB Hf o fs[j]

theorem postFF_locals (C : Ctx) (n i : Nat) :
    ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostFF C n i a w s' st → PostFF C n i a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', Hf, od, h1, h2, h3, h4, h5, h6, h7, h8⟩ => ⟨H', Hf, od, h1, h2, h3, h4, h5, h6, sr_of_eq h7 rfl rfl rfl rfl, h8⟩

theorem ff_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ffLocals → (ctxEnv C ++ ffParams.zip vals).get x = none :=
  Knot.params_none C ffLocals ffParams vals (by decide) (by decide)

theorem fireE_mono' {EB : BitVec 64} {H H' : List (BitVec 64)} (hp : H <+: H') {o : Nat} {f : IRecRuleFire}
    (h : FireE EB H o f) : FireE EB H' o f := fireE_mono hp h

/-- **`fireFill`**: the firing modes from position `i`. -/
theorem ff_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hfx : FXCodes C)
    (hcx : C.code.lookup fRecFire = some (fxParams.map (fun p => (p, ShapeHOL.one)), fxBody C, .one))
    (hcode : C.code.lookup fFfFill = some (ffParams.map (fun p => (p, ShapeHOL.one)), ffBody C, .one))
    (p : BlockShape) (hk : p.k < 2 ^ 64) (rcs : List RecShape) (orr : Nat)
    (hrs : PtrsRep C C.H orr (RecRep C C.H) rcs) :
    ∀ k i (H : List (BitVec 64)) (s : AState), rcs.length - i = k → i ≤ rcs.length → C.H <+: H →
      SpecR (Pre (σ := σ) (ctxH C H) s (ffParams.zip [cellA C orr, BitVec.ofNat 64 i, BitVec.ofNat 64 rcs.length,
        BitVec.ofNat 64 p.k])) (ffBody C) s ((rcs.drop i).mapM (recFire p)) (PostFF (ctxH C H) rcs.length i) := by
  intro k
  induction k with
  | zero =>
    intro i H s hk0 hi hp
    refine specR_prologue (postFF_locals _ _ _) (ff_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hrl : rcs.length + 2 < 2 ^ 61 := by
      have h0 := (List.getElem?_eq_some_iff.mp (get_prefix hrs.1 hp)).1
      rcases Nat.lt_or_ge 0 rcs.length with h | h
      · obtain ⟨oc, h1, -⟩ := hrs.2 (rcs.length - 1) (by omega)
        have := (List.getElem?_eq_some_iff.mp (get_prefix h1 hp)).1; omega
      · omega
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, ffParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_of_length_le (by omega)]
    refine specR_allocI (C := ctxH C H) ffX _ (rcs.length + 1) (by omega) (by decide) (fun v => ?_)
      (fun H2 ws hp2 hws hroom => ?_)
    · simp +decide [sev, Env.get, ffParams, ctxEnv]
      apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]; omega
    have hp2' : H <+: H2 := hp2
    have hq0 : H2.length < (ctxH (ctxH C H) (H2 ++ ws)).H.length := by show H2.length < (H2 ++ ws).length; simp; omega
    refine specR_heapStoreI (ctxOK_H hok _) (vv ffX) (vv ffN) H2.length hq0 (BitVec.ofNat 64 rcs.length)
      (by simp +decide [Env.get] <;> rfl) (by simp +decide [Env.get, ffParams, ctxEnv]) ?_
    have hpre : H2 <+: (H2 ++ ws).set H2.length (BitVec.ofNat 64 rcs.length) :=
      ConPanqueque.T.Big.prefix_set_ge (List.prefix_append _ _) _ (le_refl _) _
    exact specR_returnI _ _ (by simp +decide [Env.get] <;> rfl)
      (fun t ht => ⟨_, H2, H2.length, hp2', hpre, le_refl _, rfl, by simp [List.getElem?_set_self, hws],
        by simp [hws]; omega, sr_of_eq ht.sr rfl rfl rfl rfl, fun j hj => by simp at hj⟩)
  | succ k ih =>
    intro i H s hk0 hi hp
    have hil : i < rcs.length := by omega
    refine specR_prologue (postFF_locals _ _ _) (ff_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hrl : rcs.length + 2 < 2 ^ 61 := by
      obtain ⟨oc, h1, -⟩ := hrs.2 (rcs.length - 1) (by omega)
      have := (List.getElem?_eq_some_iff.mp (get_prefix h1 hp)).1; omega
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i rcs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, ffParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨orc, h1, hrr⟩ := hrs.2 i hil
    obtain ⟨⟨ocv, hocv, hcv⟩, ⟨hrp, hrpb⟩, ⟨hmi, hmib⟩, ⟨htg, htgb⟩, -, -⟩ := hrr
    refine UD.specR_heapLoadI' (C := ctxH C H) ffR _ (orr + 1 + i) _ (get_prefix h1 hp) (by decide)
      (by simp +decide [sev, Env.get, ffParams, ctxEnv]; exact cellA_mulIdx C orr i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) ffCv _ orc _ (get_prefix hocv hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) ffRp _ (orc + 1) _ (get_prefix hrp hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C orc) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) ffMi _ (orc + 2) _ (get_prefix hmi hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C orc 2) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) ffTg _ (orc + 3) _ (get_prefix htg hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C orc 3) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) ffTy _ (ocv + 2) _ (get_prefix hcv.2.2 hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C ocv 2) ?_
    rw [List.drop_eq_getElem_cons hil, List.mapM_cons]
    refine specR_callNIH (C := ctxH C H) ffF fRecFire fxParams [vv ffTg, vv ffK, vv ffMi, vv ffRp, vv ffTy] (fxBody C)
      [BitVec.ofNat 64 rcs[i].tgt, BitVec.ofNat 64 p.k, BitVec.ofNat 64 rcs[i].mI, BitVec.ofNat 64 rcs[i].rP,
        Enc.idxW rcs[i].cvR.type] (by decide) rfl (by decide) hcx
      ⟨by simp +decide [sev, Env.get], by simp +decide [sev, Env.get, ffParams, ctxEnv], by simp +decide [sev, Env.get],
        by simp +decide [sev, Env.get], by simp +decide [sev, Env.get], trivial⟩
      (PostFX (ctxH C H)) (fun f w _ H' => ∃ o, w = cellA C o ∧ FireE C.HB H' o f)
      (fun f w s' st ⟨H', hp', hs', h'⟩ => ⟨H', hp', h', hs'⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fxParams _ rfl hlk)
        (fx_spec ra C hok hfx p rcs[i] (by omega) hk hmib hrpb H s))
      (fun f w s1 H1 hp1 ⟨o, hwo, hfe⟩ => ?_)
    subst hwo
    have hp1' : H <+: H1 := hp1
    refine specR_callNIH (C := ctxH C H1) ffP fFfFill ffParams [vv ffRs, .op .add [vv ffI, .const 1], vv ffN, vv ffK]
      (ffBody C) [cellA C orr, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 rcs.length, BitVec.ofNat 64 p.k]
      (by decide) rfl (by decide) hcode
      ⟨by simp +decide [sev, Env.get, ffParams, ctxEnv],
        by simp +decide [sev, Env.get, ffParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get, ffParams, ctxEnv], by simp +decide [sev, Env.get, ffParams, ctxEnv], trivial⟩
      (PostFF (ctxH C H1) rcs.length (i + 1))
      (fun fs w s' H' => ∃ Hf od, H1 <+: Hf ∧ Hf <+: H' ∧ Hf.length ≤ od ∧ w = cellA C od ∧
        H'[od]? = some (BitVec.ofNat 64 rcs.length) ∧ od + 1 + rcs.length ≤ H'.length ∧
        ∀ j (hj : j < fs.length), ∃ o, H'[od + 1 + (i + 1) + j]? = some (cellA C o) ∧ FireE C.HB Hf o fs[j])
      (fun fs w s' st ⟨H', Hf, od, h1, h2, h3, h4, h5, h6, h7, h8⟩ =>
        ⟨H', h1.trans h2, ⟨Hf, od, h1, h2, h3, h4, h5, h6, h8⟩, h7⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ffParams _ rfl hlk)
        (ih (i + 1) H1 s1 (by omega) (by omega) (hp.trans hp1')))
      (fun fs w s2 H2 hp2 ⟨Hf, od, hHf, hfH, hfl, hwd, hd0, hdl, hfs⟩ => ?_)
    subst hwd
    have hj : od + 1 + i < (ctxH C H2).H.length := by show od + 1 + i < H2.length; omega
    refine specR_heapStoreI (ctxOK_H hok H2) _ (vv ffF) (od + 1 + i) hj (cellA C o)
      (by simp +decide [sev, Env.get_cons, Env.get, ffParams, ctxEnv]; exact cellA_mulIdx C od i (by omega))
      (by simp +decide [sev, Env.get_cons]) ?_
    have hfB : Hf <+: H2.set (od + 1 + i) (cellA C o) := ConPanqueque.T.Big.prefix_set_ge hfH _ (by omega) _
    exact specR_returnI _ _ (by simp +decide [Env.get] <;> rfl)
      (fun t ht => ⟨_, Hf, od, hp1'.trans hHf, hfB, hfl, rfl,
        by rw [List.getElem?_set_ne (by omega)]; exact hd0, by simp; omega, sr_of_eq ht.sr rfl rfl rfl rfl,
        fun j hj => by
          rcases j with _ | j
          · refine ⟨o, ?_, fireE_mono' hHf hfe⟩
            rw [show od + 1 + i + 0 = od + 1 + i by omega, List.getElem?_set_self (by omega)]; rfl
          · obtain ⟨o', ho', hfe'⟩ := hfs j (by simp at hj; omega)
            refine ⟨o', ?_, hfe'⟩
            rw [show od + 1 + i + (j + 1) = od + 1 + (i + 1) + j by omega, List.getElem?_set_ne (by omega)]
            exact ho'⟩)

end

end ConPanqueque.T.Ind
