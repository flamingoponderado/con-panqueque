import ConPanqueque.T.Ind.ClassKeys

/-!
# A class as a major premise (`targetMajorOf`, the member branch) and `classMajors`

An outside inductive (a nested block's container) halts: the subset the port checks is the unnested blocks.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

/-! ## The member index of a name -/

def mfiM := ofString "mfi_m"
def mfiX := ofString "mfi_x"
def mfiI := ofString "mfi_i"
def mfiN := ofString "mfi_n"
def mfiP := ofString "mfi_p"
def mfiC := ofString "mfi_c"
def mfiY := ofString "mfi_y"
def mfiR := ofString "mfi_r"
def fMemFindIdx := ofString "memberFindIdx"

def mfiParams : List MlS := [mfiM, mfiX, mfiI, mfiN]
def mfiLocals : List MlS := [mfiP, mfiC, mfiY, mfiR]

def mfiBody : ProgHOL 64 := prologue mfiLocals
  (.ite (.cmp .lower (vv mfiI) (vv mfiN))
    (.seq (.assign .local mfiP (.load .one (.op .add [vv mfiM, .op .add [.panop .mul [vv mfiI, .const 8], .const 8]])))
    (.seq (.assign .local mfiC (.load .one (vv mfiP)))
    (.seq (.assign .local mfiY (.load .one (vv mfiC)))
    (.ite (.cmp .equal (vv mfiY) (vv mfiX)) (.return (.op .add [vv mfiI, .const 1]))
      (.seq (.call (some (some (.local, mfiR), none)) fMemFindIdx [vv mfiM, vv mfiX, .op .add [vv mfiI, .const 1], vv mfiN])
        (.return (vv mfiR)))))))
    (.return (.const 0)))

section
variable {σ : Type}

theorem mfi_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ mfiLocals → (ctxEnv C ++ mfiParams.zip vals).get x = none :=
  Knot.params_none C mfiLocals mfiParams vals (by decide) (by decide)

theorem findIdx_drop_name (xs : List NIdx) (q : NIdx) (i : Nat) (hi : i < xs.length) :
    ((xs.drop i).findIdx? (· == q)).map (· + i) =
      if xs[i] = q then some i else ((xs.drop (i + 1)).findIdx? (· == q)).map (· + (i + 1)) := by
  rw [List.drop_eq_getElem_cons hi, List.findIdx?_cons]
  by_cases h : xs[i] = q
  · simp [h]
  · simp [h, Option.map_map, Function.comp_def]; congr 1; funext x; omega

/-- **`memberFindIdx`** from member `i`: the first member named `x`, as `optNatW`. -/
theorem mfi_spec (C : Ctx) (hok : CtxOK C)
    (hc : C.code.lookup fMemFindIdx = some (mfiParams.map (fun p => (p, ShapeHOL.one)), mfiBody, .one))
    (ms : List MemberShape) (x : NIdx) (om : Nat) (H : List (BitVec 64)) (hM : PtrsRep C H om (MemberRep C H) ms)
    (hml : ms.length < 2 ^ 59) :
    ∀ f i (s : AState), ms.length - i = f → i ≤ ms.length →
      SpecR (σ := σ) (Pre (ctxH C H) s (mfiParams.zip [cellA C om, Enc.idxW x, BitVec.ofNat 64 i, BitVec.ofNat 64 ms.length]))
        mfiBody s (pure ((((ms.map (·.cvT.name)).drop i).findIdx? (· == x)).map (· + i))) (PostON (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i s hf hi
    have hin : i = ms.length := by omega
    subst hin
    refine specR_prologue (postON_locals _) (mfi_none _ _) ?_
    have hlw := nd_lt_iff ms.length ms.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, mfiParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [show (ms.map (·.cvT.name)).drop ms.length = [] by simp]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨rfl, (fun _ h => by simp at h), sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i s hf hi
    have hin : i < ms.length := by omega
    refine specR_prologue (postON_locals _) (mfi_none _ _) ?_
    have hlw := nd_lt_iff i ms.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, mfiParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [findIdx_drop_name (ms.map (·.cvT.name)) x i (by simpa using hin)]
    obtain ⟨omi, hmi, hrep⟩ := hM.2 i hin
    obtain ⟨⟨oc, hoc, hcv⟩, -⟩ := hrep
    obtain ⟨hnm, -, -⟩ := hcv
    refine UD.specR_heapLoadI' (C := ctxH C H) mfiP _ (om + 1 + i) _ hmi (by decide)
      (by simp +decide [sev, Env.get, mfiParams, ctxEnv]; exact cellA_mulIdx C om i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) mfiC (vv mfiP) omi _ hoc (by decide) (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) mfiY (vv mfiC) oc _ hnm (by decide) (by simp +decide [sev, Env.get_cons]; rfl) ?_
    simp only [List.getElem_map]
    by_cases he : ms[i].cvT.name = x
    · rw [if_pos he]
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, mfiParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, he]) (fun _ => ?_) (fun h => absurd h (by decide))
      exact specR_returnI _ (BitVec.ofNat 64 (i + 1))
        (by simp +decide [sev, Env.get_cons, Env.get, mfiParams, ctxEnv]; exact word_add1_eq i)
        (fun t ht => ⟨rfl, (fun p hp => by cases hp; omega), sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    rw [if_neg he]
    have hw : Enc.idxW ms[i].cvT.name ≠ Enc.idxW x := fun e => he (Enc.idxW_inj e)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, mfiParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hw]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_congr (m' := (pure ((((ms.map (·.cvT.name)).drop (i + 1)).findIdx? (· == x)).map (· + (i + 1))) :
      AM (Option Nat)) >>= fun r => pure r) (by simp) ?_
    refine specR_callNIM mfiR fMemFindIdx mfiParams [vv mfiM, vv mfiX, .op .add [vv mfiI, .const 1], vv mfiN] mfiBody
      [cellA C om, Enc.idxW x, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 ms.length] (by decide) rfl (by decide) hc
      ⟨by simp +decide [sev, Env.get_cons, Env.get, mfiParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, mfiParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, mfiParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, mfiParams, ctxEnv], trivial⟩
      (PostON (ctxH C H)) (fun _ _ _ _ h => h.2.2)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mfiParams _ rfl hlk) (ih (i + 1) s (by omega) (by omega)))
      (fun r w s1 st ⟨hw', hb, _⟩ => ?_)
    subst hw'
    exact specR_returnI _ _ (by simp [Env.get]) (fun t ht => ⟨rfl, hb, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## `targetMajorOf` (the member branch) -/

/-- A target major at `o`: `[nIdx, ctors, member + 1, ptr]`, `ptr ↦ [ind, lvls, ds block, nPc]`. -/
def TMRep (C : Ctx) (H : List (BitVec 64)) (o : Nat) (m : TargetMajor) : Prop :=
  ∃ oa, H[o + 3]? = some (cellA C oa) ∧ H[oa]? = some (Enc.idxW m.ind) ∧ H[oa + 1]? = some (Enc.idxW m.lvls) ∧
    (∃ od, H[oa + 2]? = some (cellA C od) ∧ BlkAt H od (m.ds.map Enc.idxW)) ∧ NatE H (oa + 3) m.nPc ∧
    NatE H o m.nIdx ∧ (∃ oc, H[o + 1]? = some (cellA C oc) ∧ CtorsRep C H oc m.ctors) ∧
    H[o + 2]? = some (optNatW m.member)

theorem tmRep_mono {C : Ctx} {H H' : List (BitVec 64)} (hp : H <+: H') {o : Nat} {m : TargetMajor}
    (h : TMRep C H o m) : TMRep C H' o m := by
  obtain ⟨oa, a, b, c, ⟨od, d, e⟩, f, g, ⟨oc, i, j⟩, k⟩ := h
  exact ⟨oa, get_prefix a hp, get_prefix b hp, get_prefix c hp, ⟨od, get_prefix d hp, blkAt_mono e hp⟩, natE_mono hp f,
    natE_mono hp g, ⟨oc, get_prefix i hp, ctorsRep_mono hp j⟩, get_prefix k hp⟩

/-- A target major as a fresh record, at the openers `pfvs` with no normal forms. -/
def PostTM (C : Ctx) (pfvs : List EIdx) (m : TargetMajor) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' o, C.H <+: H' ∧ w = cellA C o ∧ TMRep C H' o m ∧ m.pfvs = pfvs ∧ m.nfs = [] ∧ SR (ctxH C H') s' st

theorem postTM_locals (C : Ctx) (pfvs : List EIdx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostTM (σ := σ) C pfvs a w s' st → PostTM C pfvs a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, hp, hw, h1, h2, h3, hs⟩ => ⟨H', o, hp, hw, h1, h2, h3, sr_of_eq hs rfl rfl rfl rfl⟩

def tmoM := ofString "tmo_m"
def tmoP := ofString "tmo_p"
def tmoL := ofString "tmo_l"
def tmoF := ofString "tmo_f"
def tmoT := ofString "tmo_t"
def tmoA := ofString "tmo_a"
def tmoHd := ofString "tmo_hd"
def tmoI := ofString "tmo_i"
def tmoUs := ofString "tmo_us"
def tmoK := ofString "tmo_k"
def tmoTi := ofString "tmo_ti"
def tmoMp := ofString "tmo_mp"
def tmoNx := ofString "tmo_nx"
def tmoCs := ofString "tmo_cs"
def tmoBl := ofString "tmo_bl"
def tmoAl := ofString "tmo_al"
def tmoFl := ofString "tmo_fl"
def tmoR := ofString "tmo_r"
def tmoRa := ofString "tmo_ra"
def tmoW := ofString "tmo_w"
def fTargetMajor := ofString "targetMajorOf"

def tmoParams : List MlS := [tmoM, tmoP, tmoL, tmoF, tmoT]
def tmoLocals : List MlS := gaaLocals ++ [tmoA, tmoHd, tmoI, tmoUs, tmoK, tmoTi, tmoMp, tmoNx, tmoCs, tmoBl, tmoAl, tmoFl,
  tmoR, tmoRa, tmoW]

def tmoRec (C : Ctx) : ProgHOL 64 :=
  alloc4 C tmoRa (vv tmoI) (vv tmoUs) (vv tmoF) (vv tmoP)
    (alloc4 C tmoW (vv tmoNx) (vv tmoCs) (.op .add [vv tmoTi, .const 1]) (vv tmoRa) (.return (vv tmoW)))

def tmoArgs (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local tmoAl (.load .one (vv tmoA)))
  (.ite (.cmp .lower (vv tmoAl) (vv tmoP)) hang
  (.seq (.assign .local tmoFl (.load .one (vv tmoF)))
  (.ite (.cmp .equal (vv tmoFl) (vv tmoP))
    (.seq (.call (some (some (.local, tmoR), none)) fPrefEq [vv tmoA, vv tmoF, .const 0, vv tmoP])
      (.ite (.cmp .equal (vv tmoR) (.const 0)) hang (tmoRec C)))
    hang)))

def tmoMember (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local tmoK (.load .one (vv tmoM)))
  (.seq (.call (some (some (.local, tmoTi), none)) fMemFindIdx [vv tmoM, vv tmoI, .const 0, vv tmoK])
  (.ite (.cmp .equal (vv tmoTi) (.const 0)) hang
  (.seq (.assign .local tmoTi (.op .sub [vv tmoTi, .const 1]))
  (.seq (.assign .local tmoMp (.load .one (.op .add [vv tmoM, .op .add [.panop .mul [vv tmoTi, .const 8], .const 8]])))
  (.seq (.assign .local tmoNx (.load .one (.op .add [vv tmoMp, .const 16])))
  (.seq (.assign .local tmoCs (.load .one (.op .add [vv tmoMp, .const 24])))
  (.seq (.call (some (some (.local, tmoBl), none)) fParamLevels [vv tmoL])
  (.ite (.cmp .equal (vv tmoUs) (vv tmoBl)) (tmoArgs C) hang))))))))

def tmoBody (C : Ctx) : ProgHOL 64 := prologue tmoLocals
  (.seq (.call (some (some (.local, tmoA), none)) ExG.fGaa [.const (BitVec.ofNat 64 coreWalkFuel), vv tmoT])
  (.seq (.call (some (some (.local, tmoHd), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv tmoT])
  (.ite (tagIsE tmoHd 3)
    (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv tmoHd)) (.seq eViewP
    (.seq (.assign .local tmoI (.load .one (vv lRp)))
    (.seq (.assign .local tmoUs (.load .one (.op .add [vv lRp, .const 8]))) (tmoMember C))))))
    hang)))

/-- The code `targetMajorOf` runs. -/
structure TMOCodes (C : Ctx) : Prop where
  self : C.code.lookup fTargetMajor = some (tmoParams.map (fun p => (p, ShapeHOL.one)), tmoBody C, .one)
  gaa : C.code.lookup ExG.fGaa = some ([(pFu, .one), (pH, .one)], ExG.gaaBody C, .one)
  gf : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  mfi : C.code.lookup fMemFindIdx = some (mfiParams.map (fun p => (p, ShapeHOL.one)), mfiBody, .one)
  pl : C.code.lookup fParamLevels = some (plParams.map (fun p => (p, ShapeHOL.one)), plBody C, .one)
  pf : C.code.lookup fPlFill = some (pfParams.map (fun p => (p, ShapeHOL.one)), pfBody, .one)
  ilp1 : C.code.lookup fInternLParam = some ([(lEn, .one)], internLParamBody, .one)
  ils : C.code.lookup fInternLs = some ([(pKey, .one), (lEc, .one)], internLsBody, .one)
  pe : C.code.lookup fPrefEq = some (peParams.map (fun p => (p, ShapeHOL.one)), peBody, .one)

section
variable {σ : Type}

theorem tmo_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ tmoLocals → (ctxEnv C ++ tmoParams.zip vals).get x = none :=
  Knot.params_none C tmoLocals tmoParams vals (by decide) (by decide)

set_option maxHeartbeats 16000000 in
/-- **`targetMajorOf`** at the openers (a non-member major halts). -/
theorem tmo_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : TMOCodes C)
    (mode : ConLeche.CheckMode) (fe : IFEnv) (p : BlockShape) (pfvs : List EIdx) (mty : EIdx) (om ol pf : Nat)
    (H : List (BitVec 64)) (hp : C.H <+: H) (hM : PtrsRep C H om (MemberRep C H) p.members)
    (hml : p.members.length < 2 ^ 59) (hpnP : p.nP < 2 ^ 63)
    (hnI : ∀ i (hi : i < p.members.length), p.members[i].nIdx < 2 ^ 63)
    (hlps : EBlk H ol (p.lps.map Enc.idxW)) (hlpl : p.lps.length < 2 ^ 59) (hpf : BlkAt H pf (pfvs.map Enc.idxW))
    (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (tmoParams.zip [cellA C om, BitVec.ofNat 64 p.nP, cellA C ol, cellA C pf,
      Enc.idxW mty])) (tmoBody C) s (targetMajorOf mode fe p pfvs pfvs mty) (PostTM (ctxH C H) pfvs) := by
  refine specR_prologue (postTM_locals _ _) (tmo_none _ _) ?_
  unfold targetMajorOf
  have hokH := ctxOK_H hok H
  refine specR_callNIH (C := ctxH C H) tmoA ExG.fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv tmoT]
    (ExG.gaaBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW mty] (by decide) rfl (by decide) hc.gaa
    ⟨rfl, by simp +decide [sev, Env.get, tmoParams, ctxEnv], trivial⟩
    (PostA (ctxH C H)) (fun a w _ H3 => ∃ o3, w = cellA C o3 ∧ BlkAt H3 o3 (a.map Enc.idxW))
    (fun a w s' st ⟨H3, o3, hp, hw, hb, hsr⟩ => ⟨H3, hp, ⟨o3, hw, hb⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
      (ExG.gaa_spec (ctxH C H) hokH hc.gaa coreWalkFuel CV.coreWalkFuel_lt H mty s))
    (fun args w s1 H1 hp1 ⟨oa, hw, hba⟩ => ?_)
  subst hw
  have hp1' : H <+: H1 := hp1
  refine specR_callNIM tmoHd fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv tmoT]
    getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW mty] (by decide) rfl (by decide) hc.gf
    ⟨rfl, by simp +decide [sev, Env.get_cons, Env.get, tmoParams, ctxEnv], trivial⟩
    (fun a w s' st => getAppFn coreWalkFuel mty s1 = .ok (a, s') ∧ Post (ctxH C H1) s1 a w s' st)
    (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
    (fun u hu _ hlk => specR_run (fun t ht => by
      subst ht
      exact getAppFn_spec (ctxH C H1) hc.gf coreWalkFuel mty s1 CV.coreWalkFuel_lt t
        ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
    (fun hd w s' st ⟨_, hw, hsA, _⟩ => ?_)
  subst hw
  have hs' : s1 = s' := hsA.symm
  subst hs'
  refine Knot.specR_tagIteV tmoHd hd 3 (by decide) (by decide) (by simp +decide [Env.get_cons]) (fun htc => ?_)
    (fun htc => ?_)
  swap
  · rw [ite_eq_right (show ¬ (hd.tag == ETag.const) = true by simpa [ETag.const] using htc)]
    exact specR_hangI
  rw [ite_eq_left (show (hd.tag == ETag.const) = true by simp [htc, ETag.const])]
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get_cons, Env.get, tmoParams, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv tmoHd) (Enc.idxW hd) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
  refine ConPanqueque.T.Big.specR_viewP hd (by simp) (by simp +decide [Env.get_cons, Env.get, tmoParams, ctxEnv] <;> rfl)
    (by simp +decide [Env.get_cons, Env.get, tmoParams, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
  have h3 : v.tagN = 3 := by rw [htn, htc]; rfl
  obtain ⟨iName, us, rfl⟩ := UD.tagN_const h3
  have hvc : s1.store.viewConst hd = some (iName, us) := ConPanqueque.T.WC.viewConst_of_view (by rw [htc]; rfl) hv
  refine specR_runBind (by rw [ConPanqueque.T.WC.viewConst_run, hvc]) ?_
  dsimp only
  refine specR_loadI' tmoI (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW iName) (by decide)
    (by simp [sev, Env.get_cons]) (by simp)
    (by simpa [encEView, Enc.encConst] using wordsAt_mem0 P (Enc.idxW iName) [Enc.idxW us] []) ?_
  refine specR_loadI' tmoUs _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW us) (by decide)
    (by simp +decide [sev, Env.get_cons]) rfl
    (by simpa [encEView, Enc.encConst] using wordsAt_mem1 P (Enc.idxW iName) (Enc.idxW us) [] []) ?_
  unfold tmoMember
  have hM1 : PtrsRep C H1 om (MemberRep C H1) p.members := ptrsRep_mono hp1' (fun _ _ h => memberRep_mono hp1' h) hM
  refine UD.specR_heapLoadI' (C := ctxH C H1) tmoK (vv tmoM) om _ hM1.1 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, tmoParams, ctxEnv]; rfl) ?_
  have hfi : p.memberNames.findIdx? (· == iName) =
      (((p.members.map (·.cvT.name)).drop 0).findIdx? (· == iName)).map (· + 0) := by
    simp [BlockShape.memberNames]
  rw [hfi]
  refine specR_pureBind ((((p.members.map (·.cvT.name)).drop 0).findIdx? (· == iName)).map (· + 0)) ?_
  refine specR_callNIM tmoTi fMemFindIdx mfiParams [vv tmoM, vv tmoI, .const 0, vv tmoK] mfiBody
    [cellA C om, Enc.idxW iName, BitVec.ofNat 64 0, BitVec.ofNat 64 p.members.length] (by decide) rfl (by decide) hc.mfi
    ⟨by simp +decide [sev, Env.get_cons, Env.get, tmoParams, ctxEnv], by simp +decide [sev, Env.get_cons], rfl,
      by simp +decide [sev, Env.get_cons], trivial⟩
    (fun a w s' st => (pure ((((p.members.map (·.cvT.name)).drop 0).findIdx? (· == iName)).map (· + 0)) : AM (Option Nat)) s1 =
      .ok (a, s') ∧ PostON (ctxH C H1) a w s' st) (fun _ _ _ _ h => h.2.2.2)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu mfiParams _ rfl hlk)
      (mfi_spec C hok hc.mfi p.members iName om H1 hM1 hml _ 0 s1 rfl (by omega))))
    (fun a w s2 st ⟨hrun, hw, hb, _⟩ => ?_)
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
  obtain ⟨hra, hs2⟩ := hrun
  subst hw; subst hs2
  rw [hra]
  rcases a with _ | t
  · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, optNatW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  have ht63 := hb t rfl
  have htl : t < p.members.length := by
    have h1 : ((p.members.map (·.cvT.name)).drop 0).findIdx? (· == iName) = some t := by
      have := hra; simp only [Option.map_eq_some_iff] at this; obtain ⟨a, ha, he⟩ := this; simp at he; rw [← he]; exact ha
    have := List.findIdx?_eq_some_iff_getElem.mp h1
    obtain ⟨hlt, -⟩ := this; simpa using hlt
  have hnt : BitVec.ofNat 64 (t + 1) ≠ 0#64 := by intro e; have := congrArg BitVec.toNat e; simp at this; omega
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, optNatW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hnt)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI tmoTi _ (BitVec.ofNat 64 t) (by decide)
    (by simp +decide [sev, Env.get_cons, optNatW]; exact word_sub_eq (t + 1) 1 (by omega) (by omega)) ?_
  obtain ⟨omt, hmt, hrep⟩ := hM1.2 t htl
  obtain ⟨-, -, hnx, ⟨oc, hcs, hcr⟩⟩ := hrep
  refine UD.specR_heapLoadI' (C := ctxH C H1) tmoMp _ (om + 1 + t) _ hmt (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, tmoParams, ctxEnv]; exact cellA_mulIdx C om t (by omega)) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H1) tmoNx _ (omt + 2) _ hnx (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C omt 2) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H1) tmoCs _ (omt + 3) _ hcs (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C omt 3) ?_
  simp only [List.getElem?_eq_getElem htl, unwrapOr, pure_bind]
  refine specR_callNIH (C := ctxH C H1) tmoBl fParamLevels plParams [vv tmoL] (plBody C) [cellA C ol] (by decide) rfl
    (by decide) hc.pl ⟨by simp +decide [sev, Env.get_cons, Env.get, tmoParams, ctxEnv], trivial⟩
    (PostLsH (ctxH C H1)) (fun h w _ _ => w = Enc.idxW h) (fun h w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu plParams _ rfl hlk)
      (pl_spec ra C hok hc.pl hc.pf hc.ilp1 hc.ils p.lps ol hlpl H1 s1 (eblk_mono hlps hp1')))
    (fun blvls wu s3 H3 hp3 hwu => ?_)
  subst hwu
  have hp3' : H1 <+: H3 := hp3
  by_cases hus : us = blvls
  swap
  · have hne : Enc.idxW us ≠ Enc.idxW blvls := fun e => hus (Enc.idxW_inj e)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  subst hus
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun _ => ?_) (fun h => absurd h (by decide))
  unfold tmoArgs
  have hba3 : BlkAt H3 oa (args.map Enc.idxW) := blkAt_mono hba hp3'
  have hpf3 : BlkAt H3 pf (pfvs.map Enc.idxW) := blkAt_mono hpf (hp1'.trans hp3')
  refine UD.specR_heapLoadI' (C := ctxH C H3) tmoAl (vv tmoA) oa _ hba3.1 (by decide) (by simp +decide [sev, Env.get_cons]; rfl) ?_
  refine specR_atEntry fun t3 ht3 => ?_
  have hal := Big.blk_small0 (ctxOK_H hok H3) ht3.sr hba3
  have hfl := Big.blk_small0 (ctxOK_H hok H3) ht3.sr hpf3
  simp only [List.length_map] at hal hfl
  have hlw := ConPanqueque.T.Decl.nd_lt_iff args.length p.nP (by omega) (by omega)
  by_cases hge : p.nP ≤ args.length
  swap
  · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, tmoParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr (by omega)]) (fun _ => specR_hangI) (fun h => absurd h (by decide))
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, tmoParams, ctxEnv,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; omega) (fun h => absurd rfl h) (fun _ => ?_)
  refine UD.specR_heapLoadI' (C := ctxH C H3) tmoFl (vv tmoF) pf _ hpf3.1 (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, tmoParams, ctxEnv]; rfl) ?_
  by_cases hfe : pfvs.length = p.nP
  swap
  · have hne : BitVec.ofNat 64 pfvs.length ≠ BitVec.ofNat 64 p.nP := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, tmoParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, tmoParams, ctxEnv,
      Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hfe]) (fun _ => ?_) (fun h => absurd h (by decide))
  refine specR_pureBind ((args.take p.nP).drop 0 == pfvs.drop 0) ?_
  refine specR_callCB (C := ctxH C H3) tmoR fPrefEq peParams [vv tmoA, vv tmoF, .const 0, vv tmoP] peBody
    [cellA C oa, cellA C pf, BitVec.ofNat 64 0, BitVec.ofNat 64 p.nP] (by decide) rfl (by decide) hc.pe
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, tmoParams, ctxEnv], rfl,
      by simp +decide [sev, Env.get_cons, Env.get, tmoParams, ctxEnv], trivial⟩
    (callee_of_pre rfl (pe_spec C hok hc.pe args pfvs oa pf p.nP hge hfe H3 hba3 hpf3 _ 0 s3 rfl
      (by omega))) (fun rb s4 H4 hp4 hrun => ?_)
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
  obtain ⟨hrb, hs4⟩ := hrun
  subst hs4
  have hp4' : H3 <+: H4 := hp4
  by_cases hb2 : rb = true
  swap
  · have hb2' : rb = false := by simpa using hb2
    subst hb2'
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  subst hb2
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun h => absurd rfl h) (fun _ => ?_)
  have htk : (List.take p.nP args == List.take p.nP pfvs) = true := by
    rw [List.take_of_length_le (show pfvs.length ≤ p.nP by omega)]; simpa only [List.drop_zero] using hrb
  rw [if_pos (by simp only [beq_self_eq_true, htk, Bool.true_and])]
  unfold tmoRec
  have hp34 : H1 <+: H4 := hp3'.trans hp4'
  refine specR_alloc4I (ctxOK_H hok H4) tmoRa (vv tmoI) (vv tmoUs) (vv tmoF) (vv tmoP)
    (Enc.idxW iName) (Enc.idxW us) (cellA C pf) (BitVec.ofNat 64 p.nP) (by decide)
    (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons])
    (fun _ => by simp +decide [sev, Env.get_cons, Env.get, tmoParams, ctxEnv])
    (fun _ => by simp +decide [sev, Env.get_cons, Env.get, tmoParams, ctxEnv]) (fun H5 ws5 hp5 hws5 _ => ?_)
  obtain ⟨a0, a1, a2, a3⟩ := img4_get H5 ws5 (Enc.idxW iName) (Enc.idxW us) (cellA C pf) (BitVec.ofNat 64 p.nP) hws5
  have h5 := img4_prefix H5 ws5 (Enc.idxW iName) (Enc.idxW us) (cellA C pf) (BitVec.ofNat 64 p.nP) hws5
  have hp45 : H4 <+: _ := (hp5 : H4 <+: H5).trans h5
  refine specR_alloc4I (ctxOK_H hok _) tmoW (vv tmoNx) (vv tmoCs) (.op .add [vv tmoTi, .const 1]) (vv tmoRa)
    (BitVec.ofNat 64 p.members[t].nIdx) (cellA C oc) (BitVec.ofNat 64 (t + 1)) (cellA C H5.length) (by decide)
    (fun _ => by simp +decide [sev, Env.get_cons]) (fun _ => by simp +decide [sev, Env.get_cons])
    (fun _ => by simp +decide [sev, Env.get_cons]; exact word_add1_eq t)
    (fun _ => by simp +decide [sev, Env.get_cons]; rfl) (fun H6 ws6 hp6 hws6 _ => ?_)
  obtain ⟨b0, b1, b2, b3⟩ := img4_get H6 ws6 (BitVec.ofNat 64 p.members[t].nIdx) (cellA C oc) (BitVec.ofNat 64 (t + 1))
    (cellA C H5.length) hws6
  have h6 := img4_prefix H6 ws6 (BitVec.ofNat 64 p.members[t].nIdx) (cellA C oc) (BitVec.ofNat 64 (t + 1))
    (cellA C H5.length) hws6
  have hp56 : _ <+: _ := (hp6 : _ <+: H6).trans h6
  have hpf6 := blkAt_mono hpf3 (hp4'.trans (hp45.trans hp56))
  refine specR_returnI (vv tmoW) (cellA C H6.length) (by simp [sev, Env.get_cons]; rfl) (fun tt htt => ?_)
  refine ⟨_, H6.length, (hp1'.trans hp34).trans (hp45.trans hp56), rfl, ⟨H5.length, b3, get_prefix a0 hp56,
    get_prefix a1 hp56, ⟨pf, get_prefix a2 hp56, by rw [List.take_of_length_le (by omega)]; exact hpf6⟩,
    ⟨get_prefix a3 hp56, hpnP⟩, ⟨b0, hnI t htl⟩, ⟨oc, b1, ctorsRep_mono (hp34.trans (hp45.trans hp56)) hcr⟩, by
      simpa [optNatW] using b2⟩, rfl, rfl, sr_of_eq htt.sr rfl rfl rfl rfl⟩

end

/-! ## `classMajors` -/

/-- A block of key records. -/
def KeyBlk (C : Ctx) (H : List (BitVec 64)) (o : Nat) (ks : List ClassKey) : Prop :=
  ∃ ps : List Nat, ps.length = ks.length ∧ BlkAt H o (ps.map (cellA C)) ∧
    ∀ k (hk : k < ks.length), ∃ op, ps[k]? = some op ∧ KeyRep C H op ks[k]

theorem keyBlk_mono {C : Ctx} {H H' : List (BitVec 64)} (hp : H <+: H') {o : Nat} {ks : List ClassKey}
    (h : KeyBlk C H o ks) : KeyBlk C H' o ks :=
  let ⟨ps, hl, hb, hr⟩ := h
  ⟨ps, hl, blkAt_mono hb hp, fun k hk => let ⟨op, h1, h2⟩ := hr k hk; ⟨op, h1, keyRep_mono hp h2⟩⟩

/-- A block of target-major records at the openers `pfvs`. -/
def TMBlk (C : Ctx) (H : List (BitVec 64)) (o : Nat) (pfvs : List EIdx) (ms : List TargetMajor) : Prop :=
  ∃ ps : List Nat, ps.length = ms.length ∧ BlkAt H o (ps.map (cellA C)) ∧
    ∀ k (hk : k < ms.length), ∃ op, ps[k]? = some op ∧ TMRep C H op ms[k] ∧ ms[k].pfvs = pfvs ∧ ms[k].nfs = []

theorem tmBlk_mono {C : Ctx} {H H' : List (BitVec 64)} (hp : H <+: H') {o : Nat} {pfvs : List EIdx}
    {ms : List TargetMajor} (h : TMBlk C H o pfvs ms) : TMBlk C H' o pfvs ms :=
  let ⟨ps, hl, hb, hr⟩ := h
  ⟨ps, hl, blkAt_mono hb hp, fun k hk => let ⟨op, h1, h2, h3, h4⟩ := hr k hk; ⟨op, h1, tmRep_mono hp h2, h3, h4⟩⟩

/-- The majors' answer: a fresh block. -/
def PostTMs (C : Ctx) (pfvs : List EIdx) (ms : List TargetMajor) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' o, C.H <+: H' ∧ w = cellA C o ∧ TMBlk C H' o pfvs ms ∧ SR (ctxH C H') s' st

theorem postTMs_locals (C : Ctx) (pfvs : List EIdx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostTMs (σ := σ) C pfvs a w s' st → PostTMs C pfvs a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, hp, hw, h1, hs⟩ => ⟨H', o, hp, hw, h1, sr_of_eq hs rfl rfl rfl rfl⟩

def cmjK := ofString "cmj_k"
def cmjI := ofString "cmj_i"
def cmjN := ofString "cmj_n"
def cmjM := ofString "cmj_m"
def cmjP := ofString "cmj_p"
def cmjL := ofString "cmj_l"
def cmjF := ofString "cmj_f"
def cmjKp := ofString "cmj_kp"
def cmjIn := ofString "cmj_in"
def cmjLv := ofString "cmj_lv"
def cmjDs := ofString "cmj_ds"
def cmjHd := ofString "cmj_hd"
def cmjDn := ofString "cmj_dn"
def cmjMt := ofString "cmj_mt"
def cmjR := ofString "cmj_r"
def cmjMb := ofString "cmj_mb"
def fClassMajors := ofString "classMajors"

def cmjParams : List MlS := [cmjK, cmjI, cmjN, cmjM, cmjP, cmjL, cmjF]
def cmjLocals : List MlS := gaaLocals ++ [cmjKp, cmjIn, cmjLv, cmjDs, cmjHd, cmjDn, cmjMt, cmjR, cmjMb]

def cmjBody (C : Ctx) : ProgHOL 64 := prologue cmjLocals
  (.ite (.cmp .lower (vv cmjI) (vv cmjN))
    (.seq (.assign .local cmjKp (.load .one (.op .add [vv cmjK, .op .add [.panop .mul [vv cmjI, .const 8], .const 8]])))
    (.seq (.assign .local cmjIn (.load .one (vv cmjKp)))
    (.seq (.assign .local cmjLv (.load .one (.op .add [vv cmjKp, .const 8])))
    (.seq (.assign .local cmjDs (.load .one (.op .add [vv cmjKp, .const 16])))
    (.seq (.call (some (some (.local, cmjHd), none)) fInternConst [vv cmjIn, vv cmjLv])
    (.seq (.assign .local cmjDn (.load .one (vv cmjDs)))
    (.seq (.call (some (some (.local, cmjMt), none)) ExK.fMka [vv cmjHd, vv cmjDs, .const 0, vv cmjDn])
    (.seq (.call (some (some (.local, cmjR), none)) fTargetMajor [vv cmjM, vv cmjP, vv cmjL, vv cmjF, vv cmjMt])
    (.seq (.assign .local cmjMb (.load .one (.op .add [vv cmjR, .const 16])))
    (.ite (.cmp .equal (vv cmjMb) (.const 0)) hang
    (.seq (.call (some (some (.local, ExS.lY), none)) fClassMajors
        [vv cmjK, .op .add [vv cmjI, .const 1], vv cmjN, vv cmjM, vv cmjP, vv cmjL, vv cmjF])
      (prependP C cmjR))))))))))))
    (alloc1 C lW (.const 0) (.return (vv lW))))

/-- The code `classMajors` runs. -/
structure CMJCodes (C : Ctx) : Prop where
  self : C.code.lookup fClassMajors = some (cmjParams.map (fun p => (p, ShapeHOL.one)), cmjBody C, .one)
  tmo : TMOCodes C
  ic : C.code.lookup fInternConst = some ([(lEn, .one), (lEus, .one)], constBody, .one)
  mka : C.code.lookup ExK.fMka = some ([(ExK.pF, .one), (ExK.pP, .one), (ExK.pI, .one), (ExK.pN, .one)], ExK.mkaBody, .one)
  app : C.code.lookup fInternApp = some ([(lEf, .one), (lEa, .one)], internAppBody, .one)

section
variable {σ : Type}

theorem cmj_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cmjLocals → (ctxEnv C ++ cmjParams.zip vals).get x = none :=
  Knot.params_none C cmjLocals cmjParams vals (by decide) (by decide)

theorem classMajors_drop (mode : ConLeche.CheckMode) (fe : IFEnv) (p : BlockShape) (pfvs : List EIdx)
    (keys : List ClassKey) (i : Nat) (hi : i < keys.length) :
    classMajors mode fe p pfvs (keys.drop i) = (do
      let hd ← internE (.const keys[i].ind keys[i].lvls)
      let mty ← mkAppN hd keys[i].ds
      let m ← targetMajorOf mode fe p pfvs pfvs mty
      targetMajorPins mode fe p.nP m
      let ms ← classMajors mode fe p pfvs (keys.drop (i + 1))
      pure (m :: ms)) := by
  rw [List.drop_eq_getElem_cons hi, classMajors]

set_option maxHeartbeats 8000000 in
/-- **`classMajors`** from key `i` (a non-member class halts). -/
theorem cmj_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CMJCodes C)
    (mode : ConLeche.CheckMode) (fe : IFEnv) (p : BlockShape) (pfvs : List EIdx) (keys : List ClassKey)
    (ok om ol pf : Nat) (H0 : List (BitVec 64)) (hK : KeyBlk C H0 ok keys) (hM : PtrsRep C H0 om (MemberRep C H0) p.members)
    (hml : p.members.length < 2 ^ 59) (hpnP : p.nP < 2 ^ 63)
    (hnI : ∀ i (hi : i < p.members.length), p.members[i].nIdx < 2 ^ 63)
    (hlps : EBlk H0 ol (p.lps.map Enc.idxW)) (hlpl : p.lps.length < 2 ^ 59) (hpf : BlkAt H0 pf (pfvs.map Enc.idxW))
    (hkl : keys.length < 2 ^ 59) :
    ∀ f i (H : List (BitVec 64)) (s : AState), keys.length - i = f → i ≤ keys.length → C.H <+: H → H0 <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (cmjParams.zip [cellA C ok, BitVec.ofNat 64 i, BitVec.ofNat 64 keys.length,
        cellA C om, BitVec.ofNat 64 p.nP, cellA C ol, cellA C pf])) (cmjBody C) s
        (classMajors mode fe p pfvs (keys.drop i)) (PostTMs (ctxH C H) pfvs) := by
  obtain ⟨ps, hpl, hpb, hpr⟩ := hK
  intro f
  induction f with
  | zero =>
    intro i H s hf hi hp h0
    have hin : i = keys.length := by omega
    subst hin
    refine specR_prologue (postTMs_locals _ _) (cmj_none _ _) ?_
    have hlw := nd_lt_iff keys.length keys.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, cmjParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length, classMajors]
    refine specR_alloc1I (ctxOK_H hok H) lW (.const 0) 0 (by decide) (fun _ => rfl) (fun H2 ws hp2 hws => ?_)
    have hg : ((H2 ++ ws).set H2.length (0 : BitVec 64))[H2.length]? = some 0 := List.getElem?_set_self (by simp [hws])
    have hpr' : H2 <+: (H2 ++ ws).set H2.length (0 : BitVec 64) := prefix_set (List.prefix_append _ _) (Nat.le_refl _) _
    exact specR_returnI _ (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht => ⟨_, H2.length,
      hp2.trans hpr', rfl, ⟨[], rfl, ⟨by simpa using hg, fun i hi => absurd hi (by simp)⟩, fun k hk => absurd hk (by simp)⟩,
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i H s hf hi hp h0
    have hin : i < keys.length := by omega
    refine specR_prologue (postTMs_locals _ _) (cmj_none _ _) ?_
    have hlw := nd_lt_iff i keys.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, cmjParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hin])
      (fun _ => ?_) (fun h => absurd h (by decide))
    rw [classMajors_drop mode fe p pfvs keys i hin]
    obtain ⟨okp, hokp, hkr⟩ := hpr i hin
    obtain ⟨hki, hkl', od, hkd, hds⟩ := hkr
    have hpi : (ps.map (cellA C))[i]'(by simp; omega) = cellA C okp := by
      simp only [List.getElem_map]; rw [List.getElem?_eq_some_iff] at hokp; obtain ⟨_, h⟩ := hokp; rw [h]
    have hcell := hpb.2 i (by simp; omega)
    rw [hpi] at hcell
    refine UD.specR_heapLoadI' (C := ctxH C H) cmjKp _ (ok + 1 + i) _ (get_prefix hcell h0) (by decide)
      (by simp +decide [sev, Env.get, cmjParams, ctxEnv]; exact cellA_mulIdx C ok i (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) cmjIn (vv cmjKp) okp _ (get_prefix hki h0) (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) cmjLv _ (okp + 1) _ (get_prefix hkl' h0) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C okp) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) cmjDs _ (okp + 2) _ (get_prefix hkd h0) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C okp 2) ?_
    have hokH := ctxOK_H hok H
    refine ILP.callE_spec (C := ctxH C H) cmjHd fInternConst [lEn, lEus] [vv cmjIn, vv cmjLv] constBody
      [Enc.idxW keys[i].ind, Enc.idxW keys[i].lvls] (by decide) rfl (by decide) hc.ic
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], trivial⟩
      (by exact const_body_spec ra (ctxH C H) hokH s _ _) (fun hd s1 => ?_)
    have hdsH := blkAt_mono hds h0
    refine UD.specR_heapLoadI' (C := ctxH C H) cmjDn (vv cmjDs) od _ hdsH.1 (by decide) (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine specR_atEntry fun t1 ht1 => ?_
    have hdl := Big.blk_small0 hokH ht1.sr hdsH
    simp only [List.length_map] at hdl
    refine ILP.callE_spec (C := ctxH C H) cmjMt ExK.fMka [ExK.pF, ExK.pP, ExK.pI, ExK.pN]
      [vv cmjHd, vv cmjDs, .const 0, vv cmjDn] ExK.mkaBody
      [Enc.idxW hd, cellA C od, BitVec.ofNat 64 0, BitVec.ofNat 64 keys[i].ds.length] (by decide) rfl (by decide) hc.mka
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], rfl,
        by simp +decide [sev, Env.get_cons, List.length_map], trivial⟩
      (by have := ExK.mkAppN_spec (σ := σ) ra (ctxH C H) hokH hc.mka hc.app od keys[i].ds hdsH (by omega) 0 (by omega) hd s1
          simp only [List.drop_zero] at this; exact this)
      (fun mty s2 => ?_)
    have hM' := ptrsRep_mono h0 (fun _ _ h => memberRep_mono h0 h) hM
    refine specR_callNIH (C := ctxH C H) cmjR fTargetMajor tmoParams [vv cmjM, vv cmjP, vv cmjL, vv cmjF, vv cmjMt]
      (tmoBody C) [cellA C om, BitVec.ofNat 64 p.nP, cellA C ol, cellA C pf, Enc.idxW mty] (by decide) rfl (by decide)
      hc.tmo.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cmjParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cmjParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cmjParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cmjParams, ctxEnv],
        by simp +decide [sev, Env.get_cons], trivial⟩
      (PostTM (ctxH C H) pfvs) (fun m w _ H' => ∃ o, w = cellA C o ∧ TMRep C H' o m ∧ m.pfvs = pfvs ∧ m.nfs = [])
      (fun m w s' st ⟨H', o, hp', hw, h1, h2, h3, hsr⟩ => ⟨H', hp', ⟨o, hw, h1, h2, h3⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tmoParams _ rfl hlk)
        (tmo_spec ra C hok hc.tmo mode fe p pfvs mty om ol pf H hp hM' hml hpnP hnI (eblk_mono hlps h0) hlpl
          (blkAt_mono hpf h0) s2))
      (fun m w s3 H3 hp3 ⟨om3, hw, htm, hpv, hnf⟩ => ?_)
    subst hw
    have hp3' : H <+: H3 := hp3
    obtain ⟨-, -, -, -, -, -, -, -, hmb⟩ := id htm
    refine UD.specR_heapLoadI' (C := ctxH C H3) cmjMb _ (om3 + 2) _ hmb (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C om3 2) ?_
    rcases hmm : m.member with _ | t
    · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, optNatW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => specR_hangI) (fun h => absurd h (by decide))
    by_cases hz : optNatW (some t) = 0#64
    · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hz, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => specR_hangI) (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hz)
      (fun h => absurd rfl h) (fun _ => ?_)
    have hpins : targetMajorPins mode fe p.nP m = pure () := by unfold targetMajorPins; rw [hmm]
    rw [hpins, pure_bind]
    refine specR_callNIH (C := ctxH C H3) ExS.lY fClassMajors cmjParams
      [vv cmjK, .op .add [vv cmjI, .const 1], vv cmjN, vv cmjM, vv cmjP, vv cmjL, vv cmjF] (cmjBody C)
      [cellA C ok, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 keys.length, cellA C om, BitVec.ofNat 64 p.nP, cellA C ol,
        cellA C pf] (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, cmjParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cmjParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [sev, Env.get_cons, Env.get, cmjParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cmjParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cmjParams, ctxEnv], by simp +decide [sev, Env.get_cons, Env.get, cmjParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cmjParams, ctxEnv], trivial⟩
      (PostTMs (ctxH C H3) pfvs) (fun ms w _ H' => ∃ o, w = cellA C o ∧ TMBlk C H' o pfvs ms)
      (fun ms w s' st ⟨H', o, hp', hw, hb, hsr⟩ => ⟨H', hp', ⟨o, hw, hb⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cmjParams _ rfl hlk)
        (ih (i + 1) H3 s3 (by omega) (by omega) (hp.trans hp3') (h0.trans hp3')))
      (fun ms w s4 H4 hp4 ⟨o4, hw, hb4⟩ => ?_)
    subst hw
    have hp4' : H3 <+: H4 := hp4
    obtain ⟨qs, hql, hqb, hqr⟩ := hb4
    refine ExPre.prepend_spec C hok (H := H4) cmjR (cellA C om3) o4 (qs.map (cellA C)) (by decide)
      (by simp +decide [Env.get_cons]) (by simp +decide [Env.get_cons]) hqb (by decide)
      (by simp +decide [Env.get_cons, Env.get, cmjParams, ctxEnv]) (by decide) (fun H' o t hp' hb hsr => ?_)
    exact ⟨H', o, (hp3'.trans hp4').trans hp', rfl, ⟨om3 :: qs, by simp [hql], by simp only [List.map_cons]; exact hb, fun k hk => by
      cases k with
      | zero => exact ⟨om3, rfl, tmRep_mono (hp4'.trans hp') htm, hpv, hnf⟩
      | succ k =>
        obtain ⟨op, h1, h2, h3, h4⟩ := hqr k (by simpa using hk)
        exact ⟨op, by simpa using h1, tmRep_mono hp' h2, h3, h4⟩⟩, hsr⟩

end

end ConPanqueque.T.Ind
