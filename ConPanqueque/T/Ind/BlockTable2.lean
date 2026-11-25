import ConPanqueque.T.Ind.BlockTable

/-!
# The block table, continued: every member's constructors, the recursors
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.Decl

def tmMs := ofString "tm_ms"
def tmT := ofString "tm_t"
def tmT0 := ofString "tm_t0"
def tmI := ofString "tm_i"
def tmK := ofString "tm_k"
def tmNp := ofString "tm_np"
def tmO := ofString "tm_o"
def tmCv := ofString "tm_cv"
def tmInd := ofString "tm_ind"
def tmL := ofString "tm_l"
def tmNc := ofString "tm_nc"
def tmR := ofString "tm_r"
def tmR2 := ofString "tm_r2"
def fTmFill := ofString "membersCtorsTable"

def tmParams : List MlS := [tmMs, tmT, tmT0, tmI, tmK, tmNp]
def tmLocals : List MlS := [tmO, tmCv, tmInd, tmL, tmNc, tmR, tmR2]

/-- Every member's constructors (members' pointer block at `tmMs`, from `tmI`), table entries from `tmT0`. -/
def tmBody : ProgHOL 64 := prologue tmLocals
  (.ite (.cmp .lower (vv tmI) (vv tmK))
    (.seq (.assign .local tmO (.load .one (.op .add [vv tmMs, .op .add [.panop .mul [vv tmI, .const 8], .const 8]])))
    (.seq (.assign .local tmCv (.load .one (vv tmO)))
    (.seq (.assign .local tmInd (.load .one (vv tmCv)))
    (.seq (.assign .local tmL (.load .one (.op .add [vv tmO, .const 24])))
    (.seq (.assign .local tmNc (.load .one (vv tmL)))
    (.seq (.call (some (some (.local, tmR), none)) fTcFill [vv tmL, vv tmT, vv tmT0, .const 0, vv tmNc, vv tmNp, vv tmInd])
    (.seq (.call (some (some (.local, tmR2), none)) fTmFill
      [vv tmMs, vv tmT, .op .add [vv tmT0, vv tmNc], .op .add [vv tmI, .const 1], vv tmK, vv tmNp])
      (.return (.const 0)))))))))
    (.return (.const 0)))

/-- The constructors' records of the members, in block order. -/
def membersCtors (np : Nat) (ms : List MemberShape) : List IConstantInfo :=
  ms.flatMap fun m => ctorsOf np m.cvT.name m.ctors

theorem blockCtors_eq (p : BlockShape) : blockCtors p = membersCtors p.nP p.members := by
  simp [blockCtors, membersCtors, BlockShape.ctorGroups, ctorsOf, List.flatMap_map]

section
variable {σ : Type}

theorem tm_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ tmLocals → (ctxEnv C ++ tmParams.zip vals).get x = none :=
  Knot.params_none C tmLocals tmParams vals (by decide) (by decide)

theorem membersCtors_drop_cons (np : Nat) (ms : List MemberShape) (i : Nat) (hi : i < ms.length) :
    membersCtors np (ms.drop i) = ctorsOf np ms[i].cvT.name ms[i].ctors ++ membersCtors np (ms.drop (i + 1)) := by
  simp only [membersCtors]; rw [List.drop_eq_getElem_cons hi, List.flatMap_cons]

/-- **`membersCtorsTable`**: the members' constructors' records and table entries, from member `i` at entry `t`. -/
theorem tm_spec (C : Ctx) (hok : CtxOK C)
    (hcp : C.code.lookup fCpy = some (cpParams.map (fun p => (p, ShapeHOL.one)), cpyBody, .one))
    (hcr : C.code.lookup fCtorRec = some (crParams.map (fun p => (p, ShapeHOL.one)), crBody C, .one))
    (hct : C.code.lookup fTcFill = some (tcParams.map (fun p => (p, ShapeHOL.one)), tcBody, .one))
    (hcode : C.code.lookup fTmFill = some (tmParams.map (fun p => (p, ShapeHOL.one)), tmBody, .one))
    (np : Nat) (hnp : np < 2 ^ 63) (ms : List MemberShape) (om ob : Nat) (H0 : List (BitVec 64))
    (hms : PtrsRep C H0 om (MemberRep C H0) ms) (hlps : ∀ m ∈ ms, ∀ c ∈ m.ctors, c.1.levelParams.length < 2 ^ 60) :
    ∀ k i t (H Hc EH : List (BitVec 64)) (s : AState), ms.length - i = k → i ≤ ms.length →
      H0 <+: Hc → Hc.length ≤ ob + 1 + 2 * t → Hc <+: H →
      ob + 1 + 2 * (t + (membersCtors np (ms.drop i)).length) ≤ H.length → C.EH <+: EH →
      SpecR (Pre (σ := σ) (ctxE (ctxH C H) EH) s (tmParams.zip [cellA C om, cellA C ob, BitVec.ofNat 64 t,
        BitVec.ofNat 64 i, BitVec.ofNat 64 ms.length, BitVec.ofNat 64 np])) tmBody s (pure ())
        (PostTF C Hc EH H.length ob t (membersCtors np (ms.drop i)) 0) := by
  intro k
  induction k with
  | zero =>
    intro i t H Hc EH s hk hi h0 hHc hp hl hpe
    refine specR_prologue (postTF_locals _ _ _ _ _ _ _ _) (tm_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hml : ms.length < 2 ^ 61 := by
      have h0' := (List.getElem?_eq_some_iff.mp (get_prefix hms.1 (h0.trans hp))).1
      rcases Nat.lt_or_ge 0 ms.length with h | h
      · obtain ⟨oc, h1, -⟩ := hms.2 (ms.length - 1) (by omega)
        have := (List.getElem?_eq_some_iff.mp (get_prefix h1 (h0.trans hp))).1; omega
      · omega
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, tmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_of_length_le (by omega)]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, EH, hp, List.prefix_refl _, le_refl _, sr_of_eq ht.sr rfl rfl rfl rfl,
      fun j hj hij => by simp [membersCtors] at hj⟩)
  | succ k ih =>
    intro i t H Hc EH s hk hi h0 hHc hp hl hpe
    have hil : i < ms.length := by omega
    refine specR_prologue (postTF_locals _ _ _ _ _ _ _ _) (tm_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have h0H := h0.trans hp
    have hml : ms.length < 2 ^ 61 := by
      obtain ⟨oc, h1, -⟩ := hms.2 (ms.length - 1) (by omega)
      have := (List.getElem?_eq_some_iff.mp (get_prefix h1 h0H)).1; omega
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i ms.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, tmParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨oi, h1, hmr⟩ := hms.2 i hil
    obtain ⟨⟨oc, hoc, hcv⟩, -, -, ⟨ol, hol, hcs⟩⟩ := hmr
    refine UD.specR_heapLoadI' (C := ctxE (ctxH C H) EH) tmO _ (om + 1 + i) _ (get_prefix h1 h0H) (by decide)
      (by simp +decide [sev, Env.get, tmParams, ctxEnv]; exact cellA_mulIdx C om i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxE (ctxH C H) EH) tmCv _ oi _ (get_prefix hoc h0H) (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxE (ctxH C H) EH) tmInd _ oc _ (get_prefix hcv.1 h0H) (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxE (ctxH C H) EH) tmL _ (oi + 3) _ (get_prefix hol h0H) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C oi 3) ?_
    refine UD.specR_heapLoadI' (C := ctxE (ctxH C H) EH) tmNc _ ol _ (get_prefix hcs.1 h0H) (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    rw [membersCtors_drop_cons np ms i hil] at hl ⊢
    simp only [List.length_append] at hl
    have hcl : (ctorsOf np ms[i].cvT.name ms[i].ctors).length = ms[i].ctors.length := by simp [ctorsOf]
    rw [hcl] at hl
    have hmem : ms[i] ∈ ms := List.getElem_mem hil
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNC (C := ctxE (ctxH C H) EH) (D := ctxLocals ++ tmLocals) tmR fTcFill tcParams
      [vv tmL, vv tmT, vv tmT0, .const 0, vv tmNc, vv tmNp, vv tmInd] tcBody
      [cellA C ol, cellA C ob, BitVec.ofNat 64 t, BitVec.ofNat 64 0, BitVec.ofNat 64 ms[i].ctors.length,
        BitVec.ofNat 64 np, Enc.idxW ms[i].cvT.name] (by decide) rfl (by decide) hct
      ⟨by simp +decide [sev, Env.get], by simp +decide [sev, Env.get, tmParams, ctxEnv],
        by simp +decide [sev, Env.get, tmParams, ctxEnv], rfl, by simp +decide [sev, Env.get],
        by simp +decide [sev, Env.get, tmParams, ctxEnv], by simp +decide [sev, Env.get], trivial⟩
      (PostTF C Hc EH H.length ob t (ctorsOf np ms[i].cvT.name ms[i].ctors) 0)
      (fun a w s' C' => ∃ H1 EH1, C' = ctxE (ctxH C H1) EH1 ∧ Hc <+: H1 ∧ EH <+: EH1 ∧ H.length ≤ H1.length ∧
        ∀ j (hj : j < (ctorsOf np ms[i].cvT.name ms[i].ctors).length), 0 ≤ j → ∃ o,
          H1[ob + 1 + 2 * (t + j)]? = some (Enc.idxW (ctorsOf np ms[i].cvT.name ms[i].ctors)[j].name) ∧
          H1[ob + 2 + 2 * (t + j)]? = some (ecell C o) ∧ CIE C.EB EH1 o (ctorsOf np ms[i].cvT.name ms[i].ctors)[j])
      (fun a w s' st ⟨H1, EH1, hp1, hpe1, hl1, hs1, hc1⟩ => ⟨_, ⟨H1, EH1, rfl, hp1, hpe1, hl1, hc1⟩, hs1⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tcParams _ rfl hlk)
        (tc_spec C hok hcp hcr hct np hnp ms[i].cvT.name ms[i].ctors ol ob t H0 hcs (hlps _ hmem) _ 0 H Hc EH s rfl
          (Nat.zero_le _) h0 (by omega) hp (by omega) hpe))
      (fun a w s1 C1 ⟨H1, EH1, eC1, hp1, hpe1, hl1, hc1⟩ => ?_)
    subst eC1
    let Hc' := H1.take (ob + 1 + 2 * (t + ms[i].ctors.length))
    have hpc' : Hc' <+: H1 := List.take_prefix _ _
    have hHcc : Hc <+: Hc' := by
      refine prefix_of_get? (by simp [Hc']; omega) (fun j hj => ?_)
      simp only [Hc']; rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj]
      exact get_prefix (List.getElem?_eq_getElem hj) hp1
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNC (C := ctxE (ctxH C H1) EH1) (D := ctxLocals ++ tmLocals) tmR2 fTmFill tmParams
      [vv tmMs, vv tmT, .op .add [vv tmT0, vv tmNc], .op .add [vv tmI, .const 1], vv tmK, vv tmNp] tmBody
      [cellA C om, cellA C ob, BitVec.ofNat 64 (t + ms[i].ctors.length), BitVec.ofNat 64 (i + 1),
        BitVec.ofNat 64 ms.length, BitVec.ofNat 64 np] (by decide) rfl (by decide) hcode
      ⟨by simp +decide [sev, Env.get, tmParams, ctxEnv], by simp +decide [sev, Env.get, tmParams, ctxEnv],
        by simp +decide [sev, Env.get, tmParams, ctxEnv]; rw [BitVec.ofNat_add_ofNat],
        by simp +decide [sev, Env.get, tmParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get, tmParams, ctxEnv], by simp +decide [sev, Env.get, tmParams, ctxEnv], trivial⟩
      (PostTF C Hc' EH1 H1.length ob (t + ms[i].ctors.length) (membersCtors np (ms.drop (i + 1))) 0)
      (fun a w s' C' => ∃ H' EH', C' = ctxE (ctxH C H') EH' ∧ Hc' <+: H' ∧ EH1 <+: EH' ∧ H1.length ≤ H'.length ∧
        ∀ j (hj : j < (membersCtors np (ms.drop (i + 1))).length), 0 ≤ j → ∃ o,
          H'[ob + 1 + 2 * (t + ms[i].ctors.length + j)]? = some (Enc.idxW (membersCtors np (ms.drop (i + 1)))[j].name) ∧
          H'[ob + 2 + 2 * (t + ms[i].ctors.length + j)]? = some (ecell C o) ∧
          CIE C.EB EH' o (membersCtors np (ms.drop (i + 1)))[j])
      (fun a w s' st ⟨H', EH', hp', hpe', hl', hs', hc'⟩ => ⟨_, ⟨H', EH', rfl, hp', hpe', hl', hc'⟩, hs'⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tmParams _ rfl hlk)
        (ih (i + 1) (t + ms[i].ctors.length) H1 Hc' EH1 s1 (by omega) (by omega) (h0.trans hHcc)
          (by simp [Hc']) hpc' (by omega) (hpe.trans hpe1)))
      (fun a w s2 C2 ⟨H', EH', eC, hp', hpe', hl', hc'⟩ => ?_)
    subst eC
    exact specR_returnI _ 0 rfl (fun t' ht => ⟨H', EH', (hHcc.trans hp'), hpe1.trans hpe', by omega,
      sr_of_eq ht.sr rfl rfl rfl rfl, fun j hj _ => by
        simp only [List.length_append] at hj
        rcases Nat.lt_or_ge j (ctorsOf np ms[i].cvT.name ms[i].ctors).length with h | h
        · obtain ⟨o, h1', h2', h3'⟩ := hc1 j h (Nat.zero_le _)
          refine ⟨o, ?_, ?_, ?_⟩
          · simp only [List.getElem_append_left h]
            exact get_prefix (show Hc'[ob + 1 + 2 * (t + j)]? = _ by
              simp only [Hc']; rw [List.getElem?_take_of_lt (by rw [hcl] at h; omega)]; exact h1') hp'
          · exact get_prefix (show Hc'[ob + 2 + 2 * (t + j)]? = _ by
              simp only [Hc']; rw [List.getElem?_take_of_lt (by rw [hcl] at h; omega)]; exact h2') hp'
          · simp only [List.getElem_append_left h]; exact cie_mono hpe' h3'
        · obtain ⟨o, h1', h2', h3'⟩ := hc' (j - (ctorsOf np ms[i].cvT.name ms[i].ctors).length) (by omega) (Nat.zero_le _)
          have hA := h
          simp only [hcl] at h1' h2' h3' h
          refine ⟨o, ?_, ?_, ?_⟩
          · simp only [List.getElem_append_right hA, hcl]
            rw [show t + ms[i].ctors.length + (j - ms[i].ctors.length) = t + j by omega] at h1'
            exact h1'
          · rw [show t + ms[i].ctors.length + (j - ms[i].ctors.length) = t + j by omega] at h2'
            exact h2'
          · simp only [List.getElem_append_right hA, hcl]
            exact h3'⟩)

end

def tqRs := ofString "tq_rs"
def tqFb := ofString "tq_fb"
def tqT := ofString "tq_t"
def tqT0 := ofString "tq_t0"
def tqI := ofString "tq_i"
def tqN := ofString "tq_n"
def tqR := ofString "tq_r"
def tqF := ofString "tq_f"
def tqCv := ofString "tq_cv"
def tqNm := ofString "tq_nm"
def tqX := ofString "tq_x"
def tqR2 := ofString "tq_r2"
def fTqFill := ofString "recsTable"

def tqParams : List MlS := [tqRs, tqFb, tqT, tqT0, tqI, tqN]
def tqLocals : List MlS := [tqR, tqF, tqCv, tqNm, tqX, tqR2]

/-- The recursors' records (shapes' pointer block at `tqRs`, firing modes' block at `tqFb`, from `tqI`), table entries
from `tqT0`. -/
def tqBody : ProgHOL 64 := prologue tqLocals
  (.ite (.cmp .lower (vv tqI) (vv tqN))
    (.seq (.assign .local tqR (.load .one (.op .add [vv tqRs, .op .add [.panop .mul [vv tqI, .const 8], .const 8]])))
    (.seq (.assign .local tqF (.load .one (.op .add [vv tqFb, .op .add [.panop .mul [vv tqI, .const 8], .const 8]])))
    (.seq (.assign .local tqCv (.load .one (vv tqR)))
    (.seq (.assign .local tqNm (.load .one (vv tqCv)))
    (.seq (.call (some (some (.local, tqX), none)) fRecRec [vv tqR, vv tqF])
    (.seq (.store (.op .add [vv tqT, .op .add [.panop .mul [.op .add [vv tqT0, vv tqI], .const 16], .const 8]]) (vv tqNm))
    (.seq (.store (.op .add [vv tqT, .op .add [.panop .mul [.op .add [vv tqT0, vv tqI], .const 16], .const 16]]) (vv tqX))
    (.seq (.call (some (some (.local, tqR2), none)) fTqFill
      [vv tqRs, vv tqFb, vv tqT, vv tqT0, .op .add [vv tqI, .const 1], vv tqN])
      (.return (.const 0))))))))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem tq_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ tqLocals → (ctxEnv C ++ tqParams.zip vals).get x = none :=
  Knot.params_none C tqLocals tqParams vals (by decide) (by decide)

/-- The firing modes' block at `ofb`: each mode's value record, below `Hf`. -/
def FiresAt (C : Ctx) (H Hf : List (BitVec 64)) (ofb : Nat) (fs : List IRecRuleFire) : Prop :=
  ∀ j (hj : j < fs.length), ∃ o, H[ofb + 1 + j]? = some (cellA C o) ∧ FireE C.HB Hf o fs[j]

/-- **`recsTable`**: the recursors' records and table entries from position `i`. -/
theorem tq_spec (C : Ctx) (hok : CtxOK C)
    (hcp : C.code.lookup fCpy = some (cpParams.map (fun p => (p, ShapeHOL.one)), cpyBody, .one))
    (hcf : C.code.lookup fFireEnv = some (fwParams.map (fun p => (p, ShapeHOL.one)), fwBody C, .one))
    (hcr : C.code.lookup fRuleFill = some (rwParams.map (fun p => (p, ShapeHOL.one)), rwBody C, .one))
    (hcw : C.code.lookup fConstRec = some (cwParams.map (fun p => (p, ShapeHOL.one)), cwBody C, .one))
    (hcq : C.code.lookup fRecRec = some (rqParams.map (fun p => (p, ShapeHOL.one)), rqBody C, .one))
    (hcode : C.code.lookup fTqFill = some (tqParams.map (fun p => (p, ShapeHOL.one)), tqBody, .one))
    (rcs : List RecShape) (fs : List IRecRuleFire) (hfl : fs.length = rcs.length) (orr ofb ob t0 : Nat)
    (H0 Hf : List (BitVec 64)) (hrs : PtrsRep C H0 orr (RecRep C H0) rcs) (hfs : FiresAt C H0 Hf ofb fs)
    (hHf : Hf <+: H0) (hlps : ∀ rc ∈ rcs, rc.cvR.levelParams.length < 2 ^ 60) :
    ∀ k i (H Hc EH : List (BitVec 64)) (s : AState), rcs.length - i = k → i ≤ rcs.length →
      H0 <+: Hc → Hc.length ≤ ob + 1 + 2 * (t0 + i) → Hc <+: H → ob + 1 + 2 * (t0 + rcs.length) ≤ H.length →
      C.EH <+: EH →
      SpecR (Pre (σ := σ) (ctxE (ctxH C H) EH) s (tqParams.zip [cellA C orr, cellA C ofb, cellA C ob,
        BitVec.ofNat 64 t0, BitVec.ofNat 64 i, BitVec.ofNat 64 rcs.length])) tqBody s (pure ())
        (PostTF C Hc EH H.length ob t0 (recsOf rcs fs) i) := by
  have hrl : (recsOf rcs fs).length = rcs.length := by simp [recsOf, hfl]
  intro k
  induction k with
  | zero =>
    intro i H Hc EH s hk hi h0 hHc hp hl hpe
    refine specR_prologue (postTF_locals _ _ _ _ _ _ _ _) (tq_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, tqParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, EH, hp, List.prefix_refl _, le_refl _, sr_of_eq ht.sr rfl rfl rfl rfl,
      fun j hj hij => by omega⟩)
  | succ k ih =>
    intro i H Hc EH s hk hi h0 hHc hp hl hpe
    have hil : i < rcs.length := by omega
    refine specR_prologue (postTF_locals _ _ _ _ _ _ _ _) (tq_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i rcs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, tqParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have h0H := h0.trans hp
    obtain ⟨orc, h1, hrr⟩ := hrs.2 i hil
    have hrr' := recRep_mono h0H hrr
    obtain ⟨of, hof, hfe⟩ := hfs i (by omega)
    obtain ⟨⟨ocv, hocv, hcv⟩, -⟩ := hrr'
    refine UD.specR_heapLoadI' (C := ctxE (ctxH C H) EH) tqR _ (orr + 1 + i) _ (get_prefix h1 h0H) (by decide)
      (by simp +decide [sev, Env.get, tqParams, ctxEnv]; exact cellA_mulIdx C orr i (by omega)) ?_
    have hof' := get_prefix hof h0H
    have hofb := (List.getElem?_eq_some_iff.mp hof').1
    refine UD.specR_heapLoadI' (C := ctxE (ctxH C H) EH) tqF _ (ofb + 1 + i) _ hof' (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, tqParams, ctxEnv]; exact cellA_mulIdx C ofb i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxE (ctxH C H) EH) tqCv _ orc _ hocv (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxE (ctxH C H) EH) tqNm _ ocv _ hcv.1 (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    have hokE : CtxOK (ctxE (ctxH C H) EH) := ctxOK_E (ctxOK_H hok H) hpe
    have hmem : rcs[i] ∈ rcs := List.getElem_mem hil
    let ci : IConstantInfo := .recInfo rcs[i].cvR rcs[i].mI rcs[i].rP rcs[i].isK
      (rcs[i].rules.map ({ · with fire := fs[i]'(by omega) }))
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNC (C := ctxE (ctxH C H) EH) tqX fRecRec rqParams [vv tqR, vv tqF] (rqBody C)
      [cellA C orc, cellA C of] (by decide) rfl (by decide) hcq
      ⟨by simp +decide [sev, Env.get], by simp +decide [sev, Env.get], trivial⟩
      (fun a w s' st => (pure () : AM Unit) s = .ok (a, s') ∧ PostRQ (ctxE (ctxH C H) EH) ci s a w s' st)
      (fun a w s' C' => s' = s ∧ ∃ H1 EH1 o, C' = ctxE (ctxH C H1) EH1 ∧ H <+: H1 ∧ EH <+: EH1 ∧ w = ecell C o ∧
        CIE C.EB EH1 o ci)
      (fun a w s' st ⟨hr, h0', H1, EH1, o, h1', h2, h3, h4, h5, h6⟩ =>
        ⟨_, ⟨pure_run_unit _ _ _ hr, H1, EH1, o, rfl, h1', h2, h4, h5⟩, by rw [pure_run_unit _ _ _ hr]; exact h6⟩)
      (fun u hu _ hlk => specR_run (fun w' hw' => by
        subst hw'
        exact rq_spec (ctxE (ctxH C H) EH) hokE hcp hcf hcr hcw rcs[i] orc (recRep_mono h0H hrr) (hlps _ hmem)
          (fs[i]'(by omega)) of (fireE_mono' (hHf.trans h0H) hfe) s _ (pre_of_lookups hu rqParams _ rfl hlk)))
      (fun _ w s1 C1 ⟨hs1, H1, EH1, o, eC1, hp1, hpe1, hw, hcie⟩ => ?_)
    subst eC1 hw; subst s1
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN1 => ?_)
    have hl1 := hp1.length_le
    have hj1 : ob + 1 + 2 * (t0 + i) < (ctxE (ctxH C H1) EH1).H.length := by show _ < H1.length; omega
    refine specR_heapStoreI (ctxOK_E (ctxOK_H hok H1) (hpe.trans hpe1)) _ (vv tqNm) (ob + 1 + 2 * (t0 + i)) hj1
      (Enc.idxW rcs[i].cvR.name)
      (by
        simp +decide [sev, Env.get_cons, Env.get, tqParams, ctxEnv]
        rw [BitVec.ofNat_add_ofNat]; exact cellA_mul16 C ob (t0 + i) (by omega))
      (by simp +decide [sev, Env.get_cons]) ?_
    change SpecR (Inv (ctxE (ctxH C (H1.set (ob + 1 + 2 * (t0 + i)) (Enc.idxW rcs[i].cvR.name))) EH1) _ _ _ _) _ _ _ _
    generalize hB1 : H1.set (ob + 1 + 2 * (t0 + i)) (Enc.idxW rcs[i].cvR.name) = B1
    have hB1l : B1.length = H1.length := by rw [← hB1]; simp
    have hj2 : ob + 2 + 2 * (t0 + i) < (ctxE (ctxH C B1) EH1).H.length := by show _ < B1.length; omega
    refine specR_heapStoreI (ctxOK_E (ctxOK_H hok B1) (hpe.trans hpe1)) _ (vv tqX) (ob + 2 + 2 * (t0 + i)) hj2
      (ecell C o)
      (by
        simp +decide [sev, Env.get_cons, Env.get, tqParams, ctxEnv]
        rw [BitVec.ofNat_add_ofNat]; exact cellA_mul16b C ob (t0 + i) (by omega))
      (by simp +decide [sev, Env.get_cons]) ?_
    change SpecR (Inv (ctxE (ctxH C (B1.set (ob + 2 + 2 * (t0 + i)) (ecell C o))) EH1) _ _ _ _) _ _ _ _
    generalize hB : B1.set (ob + 2 + 2 * (t0 + i)) (ecell C o) = B
    have hBl : B.length = H1.length := by rw [← hB, List.length_set, hB1l]
    have hBn : B[ob + 1 + 2 * (t0 + i)]? = some (Enc.idxW rcs[i].cvR.name) := by
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
    refine specR_callNC (C := ctxE (ctxH C B) EH1) (D := ctxLocals ++ tqLocals) tqR2 fTqFill tqParams
      [vv tqRs, vv tqFb, vv tqT, vv tqT0, .op .add [vv tqI, .const 1], vv tqN] tqBody
      [cellA C orr, cellA C ofb, cellA C ob, BitVec.ofNat 64 t0, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 rcs.length]
      (by decide) rfl (by decide) hcode ?_
      (PostTF C Hc' EH1 B.length ob t0 (recsOf rcs fs) (i + 1))
      (fun a w s' C' => ∃ H' EH', C' = ctxE (ctxH C H') EH' ∧ Hc' <+: H' ∧ EH1 <+: EH' ∧ B.length ≤ H'.length ∧
        ∀ j (hj : j < (recsOf rcs fs).length), i + 1 ≤ j → ∃ o,
          H'[ob + 1 + 2 * (t0 + j)]? = some (Enc.idxW (recsOf rcs fs)[j].name) ∧
          H'[ob + 2 + 2 * (t0 + j)]? = some (ecell C o) ∧ CIE C.EB EH' o (recsOf rcs fs)[j])
      (fun a w s' st ⟨H', EH', hp', hpe', hl', hs', hc'⟩ => ⟨_, ⟨H', EH', rfl, hp', hpe', hl', hc'⟩, hs'⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tqParams _ rfl hlk)
        (ih (i + 1) B Hc' EH1 s (by omega) (by omega) (h0.trans hHcc) (by simp [Hc']; omega) hpc' (by omega)
          (hpe.trans hpe1)))
      (fun a w s2 C2 ⟨H', EH', eC, hp', hpe', hl', hc'⟩ => ?_)
    · exact ⟨by simp +decide [sev, Env.get_cons, Env.get, tqParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, tqParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, tqParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, tqParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, tqParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, tqParams, ctxEnv], trivial⟩
    subst eC
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H', EH', hHcc.trans hp', hpe1.trans hpe', by omega,
      sr_of_eq ht.sr rfl rfl rfl rfl, fun j hj hij => by
        rcases Nat.lt_or_ge i j with h | h
        · exact hc' j hj (by omega)
        · have e : j = i := by omega
          subst e
          refine ⟨o, ?_, ?_, ?_⟩
          · have := get_prefix (show Hc'[ob + 1 + 2 * (t0 + j)]? = some (Enc.idxW rcs[j].cvR.name) by
              simp only [Hc']; rw [List.getElem?_take_of_lt (by omega)]; exact hBn) hp'
            simp only [recsOf, List.getElem_map, List.getElem_zip]
            exact this
          · exact get_prefix (show Hc'[ob + 2 + 2 * (t0 + j)]? = some (ecell C o) by
              simp only [Hc']; rw [List.getElem?_take_of_lt (by omega)]; exact hBo) hp'
          · have := cie_mono hpe' hcie
            simp only [recsOf, List.getElem_map, List.getElem_zip]
            exact this⟩)

end

def txRs := ofString "tx_rs"
def txFb := ofString "tx_fb"
def txD := ofString "tx_d"
def txI := ofString "tx_i"
def txN := ofString "tx_n"
def txR := ofString "tx_r"
def txF := ofString "tx_f"
def txX := ofString "tx_x"
def txR2 := ofString "tx_r2"
def fTxFill := ofString "recsBlock"

def txParams : List MlS := [txRs, txFb, txD, txI, txN]
def txLocals : List MlS := [txR, txF, txX, txR2]

/-- The recursors' records (from `txI`), their pointers into the value block at `txD` (`RecsAt`). -/
def txBody : ProgHOL 64 := prologue txLocals
  (.ite (.cmp .lower (vv txI) (vv txN))
    (.seq (.assign .local txR (.load .one (.op .add [vv txRs, .op .add [.panop .mul [vv txI, .const 8], .const 8]])))
    (.seq (.assign .local txF (.load .one (.op .add [vv txFb, .op .add [.panop .mul [vv txI, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, txX), none)) fRecRec [vv txR, vv txF])
    (.seq (.store (.op .add [vv txD, .op .add [.panop .mul [vv txI, .const 8], .const 8]]) (vv txX))
    (.seq (.call (some (some (.local, txR2), none)) fTxFill [vv txRs, vv txFb, vv txD, .op .add [vv txI, .const 1], vv txN])
      (.return (.const 0)))))))
    (.return (.const 0)))

section
variable {σ : Type}

/-- Record pointers from `i` on in the block at `od`, each record in the environment heap. -/
def PostTX (C : Ctx) (Hc EH : List (BitVec 64)) (Lh od : Nat) (cs : List IConstantInfo) (i : Nat) (_ : Unit)
    (_ : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' EH', Hc <+: H' ∧ EH <+: EH' ∧ Lh ≤ H'.length ∧ SR (ctxE (ctxH C H') EH') s' st ∧
    ∀ j (hj : j < cs.length), i ≤ j → ∃ o, H'[od + 1 + j]? = some (ecell C o) ∧ CIE C.EB EH' o cs[j]

theorem postTX_locals (C : Ctx) (Hc EH : List (BitVec 64)) (Lh od : Nat) (cs : List IConstantInfo) (i : Nat) :
    ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostTX C Hc EH Lh od cs i a w s' st → PostTX C Hc EH Lh od cs i a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', EH', h1, h2, h0, h3, h4⟩ => ⟨H', EH', h1, h2, h0, sr_of_eq h3 rfl rfl rfl rfl, h4⟩

theorem tx_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ txLocals → (ctxEnv C ++ txParams.zip vals).get x = none :=
  Knot.params_none C txLocals txParams vals (by decide) (by decide)

/-- **`recsBlock`**: the recursors' records, their pointers from position `i`. -/
theorem tx_spec (C : Ctx) (hok : CtxOK C)
    (hcp : C.code.lookup fCpy = some (cpParams.map (fun p => (p, ShapeHOL.one)), cpyBody, .one))
    (hcf : C.code.lookup fFireEnv = some (fwParams.map (fun p => (p, ShapeHOL.one)), fwBody C, .one))
    (hcr : C.code.lookup fRuleFill = some (rwParams.map (fun p => (p, ShapeHOL.one)), rwBody C, .one))
    (hcw : C.code.lookup fConstRec = some (cwParams.map (fun p => (p, ShapeHOL.one)), cwBody C, .one))
    (hcq : C.code.lookup fRecRec = some (rqParams.map (fun p => (p, ShapeHOL.one)), rqBody C, .one))
    (hcode : C.code.lookup fTxFill = some (txParams.map (fun p => (p, ShapeHOL.one)), txBody, .one))
    (rcs : List RecShape) (fs : List IRecRuleFire) (hfl : fs.length = rcs.length) (orr ofb od : Nat)
    (H0 Hf : List (BitVec 64)) (hrs : PtrsRep C H0 orr (RecRep C H0) rcs) (hfs : FiresAt C H0 Hf ofb fs)
    (hHf : Hf <+: H0) (hlps : ∀ rc ∈ rcs, rc.cvR.levelParams.length < 2 ^ 60) :
    ∀ k i (H Hc EH : List (BitVec 64)) (s : AState), rcs.length - i = k → i ≤ rcs.length →
      H0 <+: Hc → Hc.length ≤ od + 1 + i → Hc <+: H → od + 1 + rcs.length ≤ H.length → C.EH <+: EH →
      SpecR (Pre (σ := σ) (ctxE (ctxH C H) EH) s (txParams.zip [cellA C orr, cellA C ofb, cellA C od,
        BitVec.ofNat 64 i, BitVec.ofNat 64 rcs.length])) txBody s (pure ())
        (PostTX C Hc EH H.length od (recsOf rcs fs) i) := by
  have hrl : (recsOf rcs fs).length = rcs.length := by simp [recsOf, hfl]
  intro k
  induction k with
  | zero =>
    intro i H Hc EH s hk hi h0 hHc hp hl hpe
    refine specR_prologue (postTX_locals _ _ _ _ _ _ _) (tx_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    refine specR_ifI _ 0 (by
        simp +decide [sev, Env.get, txParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]; omega) (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, EH, hp, List.prefix_refl _, le_refl _, sr_of_eq ht.sr rfl rfl rfl rfl,
      fun j hj hij => by omega⟩)
  | succ k ih =>
    intro i H Hc EH s hk hi h0 hHc hp hl hpe
    have hil : i < rcs.length := by omega
    refine specR_prologue (postTX_locals _ _ _ _ _ _ _) (tx_none _ _) ?_
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
    have hHN' : H.length ≤ C.HN := hHN
    have hlay := hok.heapLay
    have hlw := ConPanqueque.T.Decl.nd_lt_iff i rcs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, txParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have h0H := h0.trans hp
    obtain ⟨orc, h1, hrr⟩ := hrs.2 i hil
    obtain ⟨of, hof, hfe⟩ := hfs i (by omega)
    refine UD.specR_heapLoadI' (C := ctxE (ctxH C H) EH) txR _ (orr + 1 + i) _ (get_prefix h1 h0H) (by decide)
      (by simp +decide [sev, Env.get, txParams, ctxEnv]; exact cellA_mulIdx C orr i (by omega)) ?_
    have hof' := get_prefix hof h0H
    have hofb := (List.getElem?_eq_some_iff.mp hof').1
    refine UD.specR_heapLoadI' (C := ctxE (ctxH C H) EH) txF _ (ofb + 1 + i) _ hof' (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, txParams, ctxEnv]; exact cellA_mulIdx C ofb i (by omega)) ?_
    have hokE : CtxOK (ctxE (ctxH C H) EH) := ctxOK_E (ctxOK_H hok H) hpe
    have hmem : rcs[i] ∈ rcs := List.getElem_mem hil
    let ci : IConstantInfo := .recInfo rcs[i].cvR rcs[i].mI rcs[i].rP rcs[i].isK
      (rcs[i].rules.map ({ · with fire := fs[i]'(by omega) }))
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNC (C := ctxE (ctxH C H) EH) txX fRecRec rqParams [vv txR, vv txF] (rqBody C)
      [cellA C orc, cellA C of] (by decide) rfl (by decide) hcq
      ⟨by simp +decide [sev, Env.get], by simp +decide [sev, Env.get], trivial⟩
      (fun a w s' st => (pure () : AM Unit) s = .ok (a, s') ∧ PostRQ (ctxE (ctxH C H) EH) ci s a w s' st)
      (fun a w s' C' => s' = s ∧ ∃ H1 EH1 o, C' = ctxE (ctxH C H1) EH1 ∧ H <+: H1 ∧ EH <+: EH1 ∧ w = ecell C o ∧
        CIE C.EB EH1 o ci)
      (fun a w s' st ⟨hr, h0', H1, EH1, o, h1', h2, h3, h4, h5, h6⟩ =>
        ⟨_, ⟨pure_run_unit _ _ _ hr, H1, EH1, o, rfl, h1', h2, h4, h5⟩, by rw [pure_run_unit _ _ _ hr]; exact h6⟩)
      (fun u hu _ hlk => specR_run (fun w' hw' => by
        subst hw'
        exact rq_spec (ctxE (ctxH C H) EH) hokE hcp hcf hcr hcw rcs[i] orc (recRep_mono h0H hrr) (hlps _ hmem)
          (fs[i]'(by omega)) of (fireE_mono' (hHf.trans h0H) hfe) s _ (pre_of_lookups hu rqParams _ rfl hlk)))
      (fun _ w s1 C1 ⟨hs1, H1, EH1, o, eC1, hp1, hpe1, hw, hcie⟩ => ?_)
    subst eC1 hw; subst s1
    refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN1 => ?_)
    have hl1 := hp1.length_le
    have hj1 : od + 1 + i < (ctxE (ctxH C H1) EH1).H.length := by show _ < H1.length; omega
    refine specR_heapStoreI (ctxOK_E (ctxOK_H hok H1) (hpe.trans hpe1)) _ (vv txX) (od + 1 + i) hj1 (ecell C o)
      (by simp +decide [sev, Env.get_cons, Env.get, txParams, ctxEnv]; exact cellA_mulIdx C od i (by omega))
      (by simp +decide [sev, Env.get_cons]) ?_
    change SpecR (Inv (ctxE (ctxH C (H1.set (od + 1 + i) (ecell C o))) EH1) _ _ _ _) _ _ _ _
    generalize hB : H1.set (od + 1 + i) (ecell C o) = B
    have hBl : B.length = H1.length := by rw [← hB]; simp
    have hBo : B[od + 1 + i]? = some (ecell C o) := by rw [← hB, List.getElem?_set_self (by omega)]
    have hpB : Hc <+: B := by
      refine prefix_of_get? (by have := hp.length_le; omega) (fun j hj => ?_)
      rw [← hB, List.getElem?_set_ne (by omega), List.getElem?_eq_getElem hj]
      exact get_prefix (List.getElem?_eq_getElem hj) (hp.trans hp1)
    let Hc' := B.take (od + 2 + i)
    have hpc' : Hc' <+: B := List.take_prefix _ _
    have hHcc : Hc <+: Hc' := by
      refine prefix_of_get? (by simp [Hc']; have := hp.length_le; omega) (fun j hj => ?_)
      simp only [Hc']; rw [List.getElem?_take_of_lt (by omega), List.getElem?_eq_getElem hj]
      exact get_prefix (List.getElem?_eq_getElem hj) hpB
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ()) (by simp) ?_
    refine specR_callNC (C := ctxE (ctxH C B) EH1) (D := ctxLocals ++ txLocals) txR2 fTxFill txParams
      [vv txRs, vv txFb, vv txD, .op .add [vv txI, .const 1], vv txN] txBody
      [cellA C orr, cellA C ofb, cellA C od, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 rcs.length]
      (by decide) rfl (by decide) hcode ?_
      (PostTX C Hc' EH1 B.length od (recsOf rcs fs) (i + 1))
      (fun a w s' C' => ∃ H' EH', C' = ctxE (ctxH C H') EH' ∧ Hc' <+: H' ∧ EH1 <+: EH' ∧ B.length ≤ H'.length ∧
        ∀ j (hj : j < (recsOf rcs fs).length), i + 1 ≤ j → ∃ o,
          H'[od + 1 + j]? = some (ecell C o) ∧ CIE C.EB EH' o (recsOf rcs fs)[j])
      (fun a w s' st ⟨H', EH', hp', hpe', hl', hs', hc'⟩ => ⟨_, ⟨H', EH', rfl, hp', hpe', hl', hc'⟩, hs'⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu txParams _ rfl hlk)
        (ih (i + 1) B Hc' EH1 s (by omega) (by omega) (h0.trans hHcc) (by simp [Hc']; omega) hpc' (by omega)
          (hpe.trans hpe1)))
      (fun a w s2 C2 ⟨H', EH', eC, hp', hpe', hl', hc'⟩ => ?_)
    · exact ⟨by simp +decide [sev, Env.get_cons, Env.get, txParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, txParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, txParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, txParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, txParams, ctxEnv], trivial⟩
    subst eC
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H', EH', hHcc.trans hp', hpe1.trans hpe', by omega,
      sr_of_eq ht.sr rfl rfl rfl rfl, fun j hj hij => by
        rcases Nat.lt_or_ge i j with h | h
        · exact hc' j hj (by omega)
        · have e : j = i := by omega
          subst e
          refine ⟨o, ?_, ?_⟩
          · exact get_prefix (show Hc'[od + 1 + j]? = some (ecell C o) by
              simp only [Hc']; rw [List.getElem?_take_of_lt (by omega)]; exact hBo) hp'
          · have := cie_mono hpe' hcie
            simp only [recsOf, List.getElem_map, List.getElem_zip]
            exact this⟩)

end

end ConPanqueque.T.Ind
