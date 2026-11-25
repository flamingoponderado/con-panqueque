import ConPanqueque.T.Ind.BlockReads

/-!
# The block table

Phase B of `blockReadsAt`: each block constant's environment record, its name and record pointer written into the
block table (`BTabAt`), in the order of `blockConstants`: the formers (`tfFill`), the constructors, the recursors.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.Decl

def tfMs := ofString "tf_ms"
def tfNz := ofString "tf_nz"
def tfT := ofString "tf_t"
def tfT0 := ofString "tf_t0"
def tfI := ofString "tf_i"
def tfK := ofString "tf_k"
def tfIr := ofString "tf_ir"
def tfAll := ofString "tf_all"
def tfNp := ofString "tf_np"
def tfO := ofString "tf_o"
def tfDc := ofString "tf_dc"
def tfN := ofString "tf_n"
def tfZ := ofString "tf_z"
def tfX := ofString "tf_x"
def tfR := ofString "tf_r"
def fTfFill := ofString "formersTable"

def tfParams : List MlS := [tfMs, tfNz, tfT, tfT0, tfI, tfK, tfIr, tfAll, tfNp]
def tfLocals : List MlS := [tfO, tfDc, tfN, tfZ, tfX, tfR]

/-- The formers' records (members' pointer block at `tfMs`, never-zero bits at `tfNz`, from `tfI`) into the table at
`tfT`, entries from `tfT0`. -/
def tfBody : ProgHOL 64 := prologue tfLocals
  (.ite (.cmp .lower (vv tfI) (vv tfK))
    (.seq (.assign .local tfO (.load .one (.op .add [vv tfMs, .op .add [.panop .mul [vv tfI, .const 8], .const 8]])))
    (.seq (.assign .local tfDc (.load .one (.op .add [vv tfO, .const 8])))
    (.seq (.assign .local tfN (.load .one (vv tfDc)))
    (.seq (.assign .local tfZ (.load .one (.op .add [vv tfNz, .op .add [.panop .mul [vv tfI, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, tfX), none)) fFormerRec [vv tfO, vv tfIr, vv tfAll, vv tfNp, vv tfZ])
    (.seq (.store (.op .add [vv tfT, .op .add [.panop .mul [.op .add [vv tfT0, vv tfI], .const 16], .const 8]]) (vv tfN))
    (.seq (.store (.op .add [vv tfT, .op .add [.panop .mul [.op .add [vv tfT0, vv tfI], .const 16], .const 16]]) (vv tfX))
    (.seq (.call (some (some (.local, tfR), none)) fTfFill
      [vv tfMs, vv tfNz, vv tfT, vv tfT0, .op .add [vv tfI, .const 1], vv tfK, vv tfIr, vv tfAll, vv tfNp])
      (.return (.const 0))))))))))
    (.return (.const 0)))

theorem cellA_mul16b (C : Ctx) (o j : Nat) (hj : j < 2 ^ 60) :
    cellA C o + (BitVec.ofNat 64 j * 16#64 + 16#64) = cellA C (o + 2 + 2 * j) := by
  apply BitVec.eq_of_toNat_eq
  simp only [cellA, BitVec.toNat_add, BitVec.toNat_mul, BitVec.toNat_ofNat]; omega

section
variable {σ : Type}

/-- Table entries from `i` on: each constant's name and record pointer, its record in the environment heap. -/
def PostTF (C : Ctx) (Hc EH : List (BitVec 64)) (Lh ob t0 : Nat) (cs : List IConstantInfo) (i : Nat) (_ : Unit)
    (_ : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' EH', Hc <+: H' ∧ EH <+: EH' ∧ Lh ≤ H'.length ∧ SR (ctxE (ctxH C H') EH') s' st ∧
    ∀ j (hj : j < cs.length), i ≤ j → ∃ o, H'[ob + 1 + 2 * (t0 + j)]? = some (Enc.idxW cs[j].name) ∧
      H'[ob + 2 + 2 * (t0 + j)]? = some (ecell C o) ∧ CIE C.EB EH' o cs[j]

theorem postTF_locals (C : Ctx) (Hc EH : List (BitVec 64)) (Lh ob t0 : Nat) (cs : List IConstantInfo) (i : Nat) :
    ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostTF C Hc EH Lh ob t0 cs i a w s' st → PostTF C Hc EH Lh ob t0 cs i a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', EH', h1, h2, h0, h3, h4⟩ => ⟨H', EH', h1, h2, h0, sr_of_eq h3 rfl rfl rfl rfl, h4⟩

theorem tf_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ tfLocals → (ctxEnv C ++ tfParams.zip vals).get x = none :=
  Knot.params_none C tfLocals tfParams vals (by decide) (by decide)

/-- **`formersTable`**: the formers' records and table entries from position `i`. -/
theorem tf_spec (C : Ctx) (hok : CtxOK C)
    (hcp : C.code.lookup fCpy = some (cpParams.map (fun p => (p, ShapeHOL.one)), cpyBody, .one))
    (hcn : C.code.lookup fCnFill = some (cnParams.map (fun p => (p, ShapeHOL.one)), cnBody, .one))
    (hcw : C.code.lookup fConstRec = some (cwParams.map (fun p => (p, ShapeHOL.one)), cwBody C, .one))
    (hcf : C.code.lookup fFormerRec = some (fmParams.map (fun p => (p, ShapeHOL.one)), fmBody C, .one))
    (hcode : C.code.lookup fTfFill = some (tfParams.map (fun p => (p, ShapeHOL.one)), tfBody, .one))
    (p : BlockShape) (isRec : Bool) (nzs : List Bool) (hnzl : nzs.length = p.members.length)
    (om onz ob t0 : Nat) (H0 : List (BitVec 64)) (hms : PtrsRep C H0 om (MemberRep C H0) p.members)
    (hnz : ∀ j (hj : j < nzs.length), H0[onz + 1 + j]? = some (boolW nzs[j]))
    (wAll : BitVec 64) (hall : ENList C.EB C.EH wAll p.memberNames) (hnp : p.nP < 2 ^ 63)
    (hni : ∀ ms ∈ p.members, ms.nIdx < 2 ^ 63) (hlps : ∀ ms ∈ p.members, ms.declared.levelParams.length < 2 ^ 60) :
    ∀ k i (H Hc EH : List (BitVec 64)) (s : AState), p.members.length - i = k → i ≤ p.members.length →
      H0 <+: Hc → Hc.length ≤ ob + 1 + 2 * (t0 + i) → Hc <+: H → ob + 1 + 2 * (t0 + p.members.length) ≤ H.length →
      C.EH <+: EH →
      SpecR (Pre (σ := σ) (ctxE (ctxH C H) EH) s (tfParams.zip [cellA C om, cellA C onz, cellA C ob,
        BitVec.ofNat 64 t0, BitVec.ofNat 64 i, BitVec.ofNat 64 p.members.length, boolW isRec, wAll,
        BitVec.ofNat 64 p.nP])) tfBody s (pure ())
        (PostTF C Hc EH H.length ob t0 (formersOf p isRec p.members nzs) i) := by
  have hfl : (formersOf p isRec p.members nzs).length = p.members.length := by simp [formersOf, hnzl]
  intro k
  induction k with
  | zero =>
    intro i H Hc EH s hk hi h0 hHc hp hl hpe
    refine specR_prologue (postTF_locals _ _ _ _ _ _ _ _) (tf_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, tfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, EH, hp, List.prefix_refl _, le_refl _, sr_of_eq ht.sr rfl rfl rfl rfl,
      fun j hj hij => by omega⟩)
  | succ k ih =>
    intro i H Hc EH s hk hi h0 hHc hp hl hpe
    have hil : i < p.members.length := by omega
    refine specR_prologue (postTF_locals _ _ _ _ _ _ _ _) (tf_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i p.members.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, tfParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have h0H := h0.trans hp
    obtain ⟨oi, h1, hmr⟩ := hms.2 i hil
    have hmr' := memberRep_mono h0H hmr
    obtain ⟨od, hod, hcv⟩ := hmr'.2.1
    refine UD.specR_heapLoadI' (C := ctxE (ctxH C H) EH) tfO _ (om + 1 + i) _ (get_prefix h1 h0H) (by decide)
      (by simp +decide [sev, Env.get, tfParams, ctxEnv]; exact cellA_mulIdx C om i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxE (ctxH C H) EH) tfDc _ (oi + 1) _ hod (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C oi) ?_
    refine UD.specR_heapLoadI' (C := ctxE (ctxH C H) EH) tfN _ od _ hcv.1 (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    have hnzi := get_prefix (hnz i (by omega)) h0H
    refine UD.specR_heapLoadI' (C := ctxE (ctxH C H) EH) tfZ _ (onz + 1 + i) _ hnzi (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, tfParams, ctxEnv]; exact cellA_mulIdx C onz i (by omega)) ?_
    have hokE : CtxOK (ctxE (ctxH C H) EH) := ctxOK_E (ctxOK_H hok H) hpe
    have hmem : p.members[i] ∈ p.members := List.getElem_mem hil
    let ci : IConstantInfo := .indInfo p.members[i].declared (capsOf p p.members[i] isRec (nzs[i]'(by omega)))
    refine specR_congr (m' := (pure ci : AM IConstantInfo) >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNC (C := ctxE (ctxH C H) EH) tfX fFormerRec fmParams
      [vv tfO, vv tfIr, vv tfAll, vv tfNp, vv tfZ] (fmBody C)
      [cellA C oi, boolW isRec, wAll, BitVec.ofNat 64 p.nP, boolW (nzs[i]'(by omega))] (by decide) rfl (by decide) hcf
      ⟨by simp +decide [sev, Env.get], by simp +decide [sev, Env.get, tfParams, ctxEnv],
        by simp +decide [sev, Env.get, tfParams, ctxEnv], by simp +decide [sev, Env.get, tfParams, ctxEnv],
        by simp +decide [sev, Env.get], trivial⟩
      (fun c w s' st => (pure ci : AM IConstantInfo) s = .ok (c, s') ∧ PostFM (ctxE (ctxH C H) EH) c w s' st)
      (fun c w s' C' => c = ci ∧ ∃ H1 EH1 o, C' = ctxE (ctxH C H1) EH1 ∧ H <+: H1 ∧ EH <+: EH1 ∧ w = ecell C o ∧
        CIE C.EB EH1 o c)
      (fun c w s' st ⟨hr, H1, EH1, o, h1, h2, h3, h4, h5, h6⟩ => by
        simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hr
        exact ⟨_, ⟨hr.1.symm, H1, EH1, o, rfl, h1, h2, h4, h5⟩, h6⟩)
      (fun u hu _ hlk => specR_run (fun w' hw' => by
        subst hw'
        exact fm_spec (ctxE (ctxH C H) EH) hokE hcp hcn hcw p p.members[i] oi hmr' isRec wAll (enlist_mono hpe hall) hnp
          (hni _ hmem) (hlps _ hmem) (nzs[i]'(by omega)) s _ (pre_of_lookups hu fmParams _ rfl hlk)))
      (fun c w s1 C1 ⟨ec, H1, EH1, o, eC1, hp1, hpe1, hw, hcie⟩ => ?_)
    subst eC1 hw ec
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN1 => ?_)
    have hHN1' : H1.length ≤ C.HN := hHN1
    have hl1 := hp1.length_le
    have hj1 : ob + 1 + 2 * (t0 + i) < (ctxE (ctxH C H1) EH1).H.length := by show _ < H1.length; omega
    refine specR_heapStoreI (ctxOK_E (ctxOK_H hok H1) (hpe.trans hpe1)) _ (vv tfN) (ob + 1 + 2 * (t0 + i)) hj1
      (Enc.idxW p.members[i].declared.name)
      (by
        simp +decide [sev, Env.get_cons, Env.get, tfParams, ctxEnv]
        rw [BitVec.ofNat_add_ofNat]; exact cellA_mul16 C ob (t0 + i) (by omega))
      (by simp +decide [sev, Env.get_cons]) ?_
    change SpecR (Inv (ctxE (ctxH C (H1.set (ob + 1 + 2 * (t0 + i)) (Enc.idxW p.members[i].declared.name))) EH1) _ _ _ _)
      _ _ _ _
    generalize hB1 : H1.set (ob + 1 + 2 * (t0 + i)) (Enc.idxW p.members[i].declared.name) = B1
    have hB1l : B1.length = H1.length := by rw [← hB1]; simp
    have hj2 : ob + 2 + 2 * (t0 + i) < (ctxE (ctxH C B1) EH1).H.length := by show _ < B1.length; omega
    refine specR_heapStoreI (ctxOK_E (ctxOK_H hok B1) (hpe.trans hpe1)) _ (vv tfX) (ob + 2 + 2 * (t0 + i)) hj2
      (ecell C o)
      (by
        simp +decide [sev, Env.get_cons, Env.get, tfParams, ctxEnv]
        rw [BitVec.ofNat_add_ofNat]; exact cellA_mul16b C ob (t0 + i) (by omega))
      (by simp +decide [sev, Env.get_cons]) ?_
    change SpecR (Inv (ctxE (ctxH C (B1.set (ob + 2 + 2 * (t0 + i)) (ecell C o))) EH1) _ _ _ _) _ _ _ _
    generalize hB : B1.set (ob + 2 + 2 * (t0 + i)) (ecell C o) = B
    have hBl : B.length = H1.length := by rw [← hB, List.length_set, hB1l]
    have hBn : B[ob + 1 + 2 * (t0 + i)]? = some (Enc.idxW p.members[i].declared.name) := by
      rw [← hB, List.getElem?_set_ne (by omega), ← hB1, List.getElem?_set_self (by omega)]
    have hBo : B[ob + 2 + 2 * (t0 + i)]? = some (ecell C o) := by
      rw [← hB, List.getElem?_set_self (by omega)]
    have hpB : Hc <+: B := by
      refine prefix_of_get? (by have := hp.length_le; omega) (fun j hj => ?_)
      rw [← hB, List.getElem?_set_ne (by omega), ← hB1, List.getElem?_set_ne (by omega), List.getElem?_eq_getElem hj]
      exact get_prefix (List.getElem?_eq_getElem hj) (hp.trans hp1)
    let Hc' := B.take (ob + 3 + 2 * (t0 + i))
    have hpc' : Hc' <+: B := List.take_prefix _ _
    have hHcc : Hc <+: Hc' := by
      refine prefix_of_get? (by simp [Hc']; have := hp.length_le; omega) (fun j hj => ?_)
      simp only [Hc']; rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj]
      exact get_prefix (List.getElem?_eq_getElem hj) hpB
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNC (C := ctxE (ctxH C B) EH1) (D := ctxLocals ++ tfLocals) tfR fTfFill tfParams
      [vv tfMs, vv tfNz, vv tfT, vv tfT0, .op .add [vv tfI, .const 1], vv tfK, vv tfIr, vv tfAll, vv tfNp] tfBody
      [cellA C om, cellA C onz, cellA C ob, BitVec.ofNat 64 t0, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 p.members.length,
        boolW isRec, wAll, BitVec.ofNat 64 p.nP] (by decide) rfl (by decide) hcode ?_
      (PostTF C Hc' EH1 B.length ob t0 (formersOf p isRec p.members nzs) (i + 1))
      (fun a w s' C' => ∃ H' EH', C' = ctxE (ctxH C H') EH' ∧ Hc' <+: H' ∧ EH1 <+: EH' ∧ B.length ≤ H'.length ∧
        ∀ j (hj : j < (formersOf p isRec p.members nzs).length), i + 1 ≤ j → ∃ o,
          H'[ob + 1 + 2 * (t0 + j)]? = some (Enc.idxW (formersOf p isRec p.members nzs)[j].name) ∧
          H'[ob + 2 + 2 * (t0 + j)]? = some (ecell C o) ∧ CIE C.EB EH' o (formersOf p isRec p.members nzs)[j])
      (fun a w s' st ⟨H', EH', hp', hpe', hl', hs', hc'⟩ => ⟨_, ⟨H', EH', rfl, hp', hpe', hl', hc'⟩, hs'⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tfParams _ rfl hlk)
        (ih (i + 1) B Hc' EH1 s1 (by omega) (by omega) (h0.trans hHcc) (by simp [Hc']; omega) hpc' (by omega)
          (hpe.trans hpe1)))
      (fun a w s2 C2 ⟨H', EH', eC, hp', hpe', hl', hc'⟩ => ?_)
    · exact ⟨by simp +decide [sev, Env.get_cons, Env.get, tfParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, tfParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, tfParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, tfParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, tfParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, tfParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, tfParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, tfParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, tfParams, ctxEnv], trivial⟩
    subst eC
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H', EH', hHcc.trans hp', hpe1.trans hpe', by omega,
      sr_of_eq ht.sr rfl rfl rfl rfl,
      fun j hj hij => by
        rcases Nat.lt_or_ge i j with h | h
        · exact hc' j hj (by omega)
        · have e : j = i := by omega
          subst e
          refine ⟨o, ?_, ?_, ?_⟩
          · have := get_prefix (show Hc'[ob + 1 + 2 * (t0 + j)]? = some (Enc.idxW p.members[j].declared.name) by
              simp only [Hc']; rw [List.getElem?_take_of_lt (by omega)]; exact hBn) hp'
            simp only [formersOf, List.getElem_map, List.getElem_zip]
            exact this
          · exact get_prefix (show Hc'[ob + 2 + 2 * (t0 + j)]? = some (ecell C o) by
              simp only [Hc']; rw [List.getElem?_take_of_lt (by omega)]; exact hBo) hp'
          · have := cie_mono hpe' hcie
            simp only [formersOf, List.getElem_map, List.getElem_zip]
            exact this⟩)

end

def tcL := ofString "tc_l"
def tcT := ofString "tc_t"
def tcT0 := ofString "tc_t0"
def tcI := ofString "tc_i"
def tcN := ofString "tc_n"
def tcNp := ofString "tc_np"
def tcInd := ofString "tc_ind"
def tcOc := ofString "tc_oc"
def tcNf := ofString "tc_nf"
def tcNm := ofString "tc_nm"
def tcX := ofString "tc_x"
def tcR := ofString "tc_r"
def fTcFill := ofString "ctorsTable"

def tcParams : List MlS := [tcL, tcT, tcT0, tcI, tcN, tcNp, tcInd]
def tcLocals : List MlS := [tcOc, tcNf, tcNm, tcX, tcR]

/-- One member's constructors (pair block at `tcL`, from `tcI`) as records and table entries from `tcT0`. -/
def tcBody : ProgHOL 64 := prologue tcLocals
  (.ite (.cmp .lower (vv tcI) (vv tcN))
    (.seq (.assign .local tcOc (.load .one (.op .add [vv tcL, .op .add [.panop .mul [vv tcI, .const 16], .const 8]])))
    (.seq (.assign .local tcNf (.load .one (.op .add [vv tcL, .op .add [.panop .mul [vv tcI, .const 16], .const 16]])))
    (.seq (.assign .local tcNm (.load .one (vv tcOc)))
    (.seq (.call (some (some (.local, tcX), none)) fCtorRec [vv tcOc, vv tcNp, vv tcNf, vv tcInd])
    (.seq (.store (.op .add [vv tcT, .op .add [.panop .mul [.op .add [vv tcT0, vv tcI], .const 16], .const 8]]) (vv tcNm))
    (.seq (.store (.op .add [vv tcT, .op .add [.panop .mul [.op .add [vv tcT0, vv tcI], .const 16], .const 16]]) (vv tcX))
    (.seq (.call (some (some (.local, tcR), none)) fTcFill
      [vv tcL, vv tcT, vv tcT0, .op .add [vv tcI, .const 1], vv tcN, vv tcNp, vv tcInd])
      (.return (.const 0)))))))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem tc_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ tcLocals → (ctxEnv C ++ tcParams.zip vals).get x = none :=
  Knot.params_none C tcLocals tcParams vals (by decide) (by decide)

/-- A member's constructors' records. -/
def ctorsOf (np : Nat) (ind : NIdx) (cs : List (IConstantVal × Nat)) : List IConstantInfo :=
  cs.map fun c => .ctorInfo c.1 np c.2 ind

/-- **`ctorsTable`**: one member's constructors' records and table entries from position `i`. -/
theorem tc_spec (C : Ctx) (hok : CtxOK C)
    (hcp : C.code.lookup fCpy = some (cpParams.map (fun p => (p, ShapeHOL.one)), cpyBody, .one))
    (hcr : C.code.lookup fCtorRec = some (crParams.map (fun p => (p, ShapeHOL.one)), crBody C, .one))
    (hcode : C.code.lookup fTcFill = some (tcParams.map (fun p => (p, ShapeHOL.one)), tcBody, .one))
    (np : Nat) (hnp : np < 2 ^ 63) (ind : NIdx) (cs : List (IConstantVal × Nat)) (ol ob t0 : Nat)
    (H0 : List (BitVec 64)) (hcs : CtorsRep C H0 ol cs) (hlps : ∀ c ∈ cs, c.1.levelParams.length < 2 ^ 60) :
    ∀ k i (H Hc EH : List (BitVec 64)) (s : AState), cs.length - i = k → i ≤ cs.length →
      H0 <+: Hc → Hc.length ≤ ob + 1 + 2 * (t0 + i) → Hc <+: H → ob + 1 + 2 * (t0 + cs.length) ≤ H.length →
      C.EH <+: EH →
      SpecR (Pre (σ := σ) (ctxE (ctxH C H) EH) s (tcParams.zip [cellA C ol, cellA C ob, BitVec.ofNat 64 t0,
        BitVec.ofNat 64 i, BitVec.ofNat 64 cs.length, BitVec.ofNat 64 np, Enc.idxW ind])) tcBody s (pure ())
        (PostTF C Hc EH H.length ob t0 (ctorsOf np ind cs) i) := by
  have hfl : (ctorsOf np ind cs).length = cs.length := by simp [ctorsOf]
  intro k
  induction k with
  | zero =>
    intro i H Hc EH s hk hi h0 hHc hp hl hpe
    refine specR_prologue (postTF_locals _ _ _ _ _ _ _ _) (tc_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, tcParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, EH, hp, List.prefix_refl _, le_refl _, sr_of_eq ht.sr rfl rfl rfl rfl,
      fun j hj hij => by omega⟩)
  | succ k ih =>
    intro i H Hc EH s hk hi h0 hHc hp hl hpe
    have hil : i < cs.length := by omega
    refine specR_prologue (postTF_locals _ _ _ _ _ _ _ _) (tc_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i cs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, tcParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have h0H := h0.trans hp
    obtain ⟨oc, h1, hcv, ⟨hnf, hnfb⟩⟩ := hcs.2 i hil
    have h1b := (List.getElem?_eq_some_iff.mp (get_prefix h1 h0H)).1
    have hcv' := cvRep_mono h0H hcv
    refine UD.specR_heapLoadI' (C := ctxE (ctxH C H) EH) tcOc _ (ol + 1 + 2 * i) _ (get_prefix h1 h0H) (by decide)
      (by simp +decide [sev, Env.get, tcParams, ctxEnv]; exact cellA_mul16 C ol i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxE (ctxH C H) EH) tcNf _ (ol + 2 + 2 * i) _ (get_prefix hnf h0H) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, tcParams, ctxEnv]; exact cellA_mul16b C ol i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxE (ctxH C H) EH) tcNm _ oc _ hcv'.1 (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    have hokE : CtxOK (ctxE (ctxH C H) EH) := ctxOK_E (ctxOK_H hok H) hpe
    let ci : IConstantInfo := .ctorInfo cs[i].1 np cs[i].2 ind
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNC (C := ctxE (ctxH C H) EH) tcX fCtorRec crParams [vv tcOc, vv tcNp, vv tcNf, vv tcInd] (crBody C)
      [cellA C oc, BitVec.ofNat 64 np, BitVec.ofNat 64 cs[i].2, Enc.idxW ind] (by decide) rfl (by decide) hcr
      ⟨by simp +decide [sev, Env.get], by simp +decide [sev, Env.get, tcParams, ctxEnv], by simp +decide [sev, Env.get],
        by simp +decide [sev, Env.get, tcParams, ctxEnv], trivial⟩
      (fun a w s' st => (pure () : AM Unit) s = .ok (a, s') ∧ PostRec (ctxE (ctxH C H) EH) ci s a w s' st)
      (fun a w s' C' => s' = s ∧ ∃ EH1 o, C' = ctxE (ctxH C H) EH1 ∧ EH <+: EH1 ∧ w = ecell C o ∧ CIE C.EB EH1 o ci)
      (fun a w s' st ⟨hr, h0', EH1, o, h1', h2, h3, h4, h5⟩ =>
        ⟨_, ⟨pure_run_unit _ _ _ hr, EH1, o, rfl, h1', h3, h4⟩, by rw [pure_run_unit _ _ _ hr]; exact h5⟩)
      (fun u hu _ hlk => specR_run (fun w' hw' => by
        subst hw'
        exact cr_spec (ctxE (ctxH C H) EH) hokE hcp cs[i].1 oc hcv' (hlps _ (List.getElem_mem hil)) np cs[i].2 hnp hnfb
          ind s _ (pre_of_lookups hu crParams _ rfl hlk)))
      (fun _ w s1 C1 ⟨hs1, EH1, o, eC1, hpe1, hw, hcie⟩ => ?_)
    subst eC1 hw; subst s1
    have hj1 : ob + 1 + 2 * (t0 + i) < (ctxE (ctxH C H) EH1).H.length := by show _ < H.length; omega
    refine specR_heapStoreI (ctxOK_E (ctxOK_H hok H) (hpe.trans hpe1)) _ (vv tcNm) (ob + 1 + 2 * (t0 + i)) hj1
      (Enc.idxW cs[i].1.name)
      (by
        simp +decide [sev, Env.get_cons, Env.get, tcParams, ctxEnv]
        rw [BitVec.ofNat_add_ofNat]; exact cellA_mul16 C ob (t0 + i) (by omega))
      (by simp +decide [sev, Env.get_cons]) ?_
    change SpecR (Inv (ctxE (ctxH C (H.set (ob + 1 + 2 * (t0 + i)) (Enc.idxW cs[i].1.name))) EH1) _ _ _ _) _ _ _ _
    generalize hB1 : H.set (ob + 1 + 2 * (t0 + i)) (Enc.idxW cs[i].1.name) = B1
    have hB1l : B1.length = H.length := by rw [← hB1]; simp
    have hj2 : ob + 2 + 2 * (t0 + i) < (ctxE (ctxH C B1) EH1).H.length := by show _ < B1.length; omega
    refine specR_heapStoreI (ctxOK_E (ctxOK_H hok B1) (hpe.trans hpe1)) _ (vv tcX) (ob + 2 + 2 * (t0 + i)) hj2
      (ecell C o)
      (by
        simp +decide [sev, Env.get_cons, Env.get, tcParams, ctxEnv]
        rw [BitVec.ofNat_add_ofNat]; exact cellA_mul16b C ob (t0 + i) (by omega))
      (by simp +decide [sev, Env.get_cons]) ?_
    change SpecR (Inv (ctxE (ctxH C (B1.set (ob + 2 + 2 * (t0 + i)) (ecell C o))) EH1) _ _ _ _) _ _ _ _
    generalize hB : B1.set (ob + 2 + 2 * (t0 + i)) (ecell C o) = B
    have hBl : B.length = H.length := by rw [← hB, List.length_set, hB1l]
    have hBn : B[ob + 1 + 2 * (t0 + i)]? = some (Enc.idxW cs[i].1.name) := by
      rw [← hB, List.getElem?_set_ne (by omega), ← hB1, List.getElem?_set_self (by omega)]
    have hBo : B[ob + 2 + 2 * (t0 + i)]? = some (ecell C o) := by
      rw [← hB, List.getElem?_set_self (by omega)]
    have hpB : Hc <+: B := by
      refine prefix_of_get? (by have := hp.length_le; omega) (fun j hj => ?_)
      rw [← hB, List.getElem?_set_ne (by omega), ← hB1, List.getElem?_set_ne (by omega), List.getElem?_eq_getElem hj]
      exact get_prefix (List.getElem?_eq_getElem hj) hp
    let Hc' := B.take (ob + 3 + 2 * (t0 + i))
    have hpc' : Hc' <+: B := List.take_prefix _ _
    have hHcc : Hc <+: Hc' := by
      refine prefix_of_get? (by simp [Hc']; have := hp.length_le; omega) (fun j hj => ?_)
      simp only [Hc']; rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj]
      exact get_prefix (List.getElem?_eq_getElem hj) hpB
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNC (C := ctxE (ctxH C B) EH1) (D := ctxLocals ++ tcLocals) tcR fTcFill tcParams
      [vv tcL, vv tcT, vv tcT0, .op .add [vv tcI, .const 1], vv tcN, vv tcNp, vv tcInd] tcBody
      [cellA C ol, cellA C ob, BitVec.ofNat 64 t0, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 cs.length,
        BitVec.ofNat 64 np, Enc.idxW ind] (by decide) rfl (by decide) hcode ?_
      (PostTF C Hc' EH1 B.length ob t0 (ctorsOf np ind cs) (i + 1))
      (fun a w s' C' => ∃ H' EH', C' = ctxE (ctxH C H') EH' ∧ Hc' <+: H' ∧ EH1 <+: EH' ∧ B.length ≤ H'.length ∧
        ∀ j (hj : j < (ctorsOf np ind cs).length), i + 1 ≤ j → ∃ o,
          H'[ob + 1 + 2 * (t0 + j)]? = some (Enc.idxW (ctorsOf np ind cs)[j].name) ∧
          H'[ob + 2 + 2 * (t0 + j)]? = some (ecell C o) ∧ CIE C.EB EH' o (ctorsOf np ind cs)[j])
      (fun a w s' st ⟨H', EH', hp', hpe', hl', hs', hc'⟩ => ⟨_, ⟨H', EH', rfl, hp', hpe', hl', hc'⟩, hs'⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tcParams _ rfl hlk)
        (ih (i + 1) B Hc' EH1 s (by omega) (by omega) (h0.trans hHcc) (by simp [Hc']; omega) hpc' (by omega)
          (hpe.trans hpe1)))
      (fun a w s2 C2 ⟨H', EH', eC, hp', hpe', hl', hc'⟩ => ?_)
    · exact ⟨by simp +decide [sev, Env.get_cons, Env.get, tcParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, tcParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, tcParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, tcParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, tcParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, tcParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, tcParams, ctxEnv], trivial⟩
    subst eC
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H', EH', hHcc.trans hp', hpe1.trans hpe', by omega,
      sr_of_eq ht.sr rfl rfl rfl rfl,
      fun j hj hij => by
        rcases Nat.lt_or_ge i j with h | h
        · exact hc' j hj (by omega)
        · have e : j = i := by omega
          subst e
          refine ⟨o, ?_, ?_, ?_⟩
          · have := get_prefix (show Hc'[ob + 1 + 2 * (t0 + j)]? = some (Enc.idxW cs[j].1.name) by
              simp only [Hc']; rw [List.getElem?_take_of_lt (by omega)]; exact hBn) hp'
            simp only [ctorsOf, List.getElem_map]
            exact this
          · exact get_prefix (show Hc'[ob + 2 + 2 * (t0 + j)]? = some (ecell C o) by
              simp only [Hc']; rw [List.getElem?_take_of_lt (by omega)]; exact hBo) hp'
          · have := cie_mono hpe' hcie
            simp only [ctorsOf, List.getElem_map]
            exact this⟩)

end

end ConPanqueque.T.Ind
