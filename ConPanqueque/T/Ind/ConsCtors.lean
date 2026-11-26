import ConPanqueque.T.Ind.CheckInds

/-!
# `consSumCtors`: a member's constructors installed

Constructor `j` from on: its ten-word `ctorInfo` record (`constRecW`, tag `4`, fields `nP`, `nF`, the family's
name), the index insert under its name, the literal flags, then the rest.  The twin pushes without a check; the
port's precondition is that every name still to come is fresh.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def cscC := ofString "csc_c"
def cscI := ofString "csc_i"
def cscN := ofString "csc_n"
def cscNP := ofString "csc_np"
def cscT := ofString "csc_t"
def cscO := ofString "csc_o"
def cscF := ofString "csc_f"
def cscX := ofString "csc_x"
def cscNm := ofString "csc_nm"
def cscRi := ofString "csc_ri"
def cscFl := ofString "csc_fl"
def cscR := ofString "csc_r"
def fConsCtors := ofString "consSumCtors"

def cscParams : List MlS := [cscC, cscI, cscN, cscNP, cscT]
def cscLocals : List MlS := [cscO, cscF, cscX, cscNm, cscRi, cscFl, cscR]

def cscBody (C : Ctx) : ProgHOL 64 := prologue cscLocals
  (.ite (.cmp .lower (vv cscI) (vv cscN))
    (.seq (.assign .local cscO (.load .one (.op .add [vv cscC, .op .add [.panop .mul [vv cscI, .const 16], .const 8]])))
    (.seq (.assign .local cscF (.load .one (.op .add [vv cscC, .op .add [.panop .mul [vv cscI, .const 16], .const 16]])))
    (.seq (.call (some (some (.local, cscX), none)) fConstRec
        [vv cscO, .const 4, vv cscNP, vv cscF, vv cscT, .const 0, .const 0, .const 0])
    (.seq (.assign .local cscNm (.load .one (vv cscO)))
    (idxInsP C (vv cscNm) (vv cscX) cscRi
    (.seq (.call (some (some (.local, cscFl), none)) fFlags [])
    (.seq (.call (some (some (.local, cscR), none)) fConsCtors
        [vv cscC, .op .add [vv cscI, .const 1], vv cscN, vv cscNP, vv cscT])
      (.return (.const 0)))))))))
    (.return (.const 0)))

structure CSCCodes (C : Ctx) : Prop where
  cp : C.code.lookup fCpy = some (Decl.cpParams.map (fun p => (p, ShapeHOL.one)), cpyBody, .one)
  cw : C.code.lookup fConstRec = some (cwParams.map (fun p => (p, ShapeHOL.one)), cwBody C, .one)
  k : KCodes C Comp.kBodies
  natF : C.code.lookup fNatF = some (([] : List MlS).map (fun p => (p, ShapeHOL.one)), natFBody C, .one)
  strF : C.code.lookup fStrF = some (([] : List MlS).map (fun p => (p, ShapeHOL.one)), strFBody C, .one)
  flags : C.code.lookup fFlags = some (([] : List MlS).map (fun p => (p, ShapeHOL.one)), Decl.flBody, .one)
  self : C.code.lookup fConsCtors = some (cscParams.map (fun p => (p, ShapeHOL.one)), cscBody C, .one)

section
variable {σ : Type}

theorem csc_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cscLocals → (ctxEnv C ++ cscParams.zip vals).get x = none :=
  Knot.params_none C cscLocals cscParams vals (by decide) (by decide)

/-- After an environment-growing stage: the next context (its environment the twin's). -/
def PostEnv (C : Ctx) (r : IFEnv) (_ : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ EH envM H, C.EH <+: EH ∧ C.H <+: H ∧ CtxOK (ctxNew C r EH envM H) ∧ SR (ctxNew C r EH envM H) s' st ∧
    TblGate r ∧ FlagsOK r ∧ LitsPinned r C.pins

theorem postEnv_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostEnv C a w s' st → PostEnv C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨EH, envM, H, h1, h2, h3, h4, h5⟩ => ⟨EH, envM, H, h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl, h5⟩

theorem consSumCtors_drop (nP : Nat) (T : NIdx) (cs : List (IConstantVal × Nat)) (j : Nat) (hj : j < cs.length)
    (fe : IFEnv) :
    consSumCtors nP T (cs.drop j) fe = consSumCtors nP T (cs.drop (j + 1)) (fe.push (.ctorInfo cs[j].1 nP cs[j].2 T)) := by
  rw [List.drop_eq_getElem_cons hj]; rfl

set_option maxHeartbeats 16000000 in
/-- **`consSumCtors`** from constructor `j` on, at any environment above `C`'s. -/
theorem csc_spec (C : Ctx) (hc : CSCCodes C) (nP : Nat) (hnP : nP < 2 ^ 63) (T : NIdx)
    (cs : List (IConstantVal × Nat)) (oq : Nat) (hcr : CtorsRep C C.H oq cs) (hcsl : cs.length < 2 ^ 58)
    (hden : ∀ c ∈ cs, CVDen c.1 C.St) (hnd : (cs.map (·.1.name)).Nodup) :
    ∀ f j (fe : IFEnv) (EH : List (BitVec 64)) envM (H : List (BitVec 64)) (s : AState),
      cs.length - j = f → j ≤ cs.length → C.H <+: H → C.EH <+: EH → CtxOK (ctxNew C fe EH envM H) →
      TblGate fe → FlagsOK fe → LitsPinned fe C.pins → (∀ c ∈ cs.drop j, fe.find? c.1.name = none) →
      SpecR (σ := σ) (Pre (ctxNew C fe EH envM H) s (cscParams.zip [cellA C oq, BitVec.ofNat 64 j,
          BitVec.ofNat 64 cs.length, BitVec.ofNat 64 nP, Enc.idxW T])) (cscBody C) s
        (pure (consSumCtors nP T (cs.drop j) fe)) (PostEnv C) := by
  intro f
  induction f with
  | zero =>
    intro j fe EH envM H s hf hj hpH hpE hok hg hF hL hnew
    have hjl : j = cs.length := by omega
    subst hjl
    refine specR_prologue (postEnv_locals _) (csc_none _ _) ?_
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, cscParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨EH, envM, H, hpE, hpH, hok, sr_of_eq ht.sr rfl rfl rfl rfl, hg, hF, hL⟩)
  | succ f ih =>
    intro j fe EH envM H s hf hj hpH hpE hok hg hF hL hnew
    have hjl : j < cs.length := by omega
    refine specR_prologue (postEnv_locals _) (csc_none _ _) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff j cs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, cscParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hjl]) (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨oc, hoc, hcv, hnfe⟩ := hcr.2 j hjl
    refine UD.specR_heapLoadI' (C := ctxNew C fe EH envM H) cscO _ (oq + 1 + 2 * j) _ (get_prefix hoc hpH) (by decide)
      (by simp +decide [sev, Env.get, cscParams, ctxEnv]; exact cellA_pair1 C oq j (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxNew C fe EH envM H) cscF _ (oq + 2 + 2 * j) _ (get_prefix hnfe.1 hpH)
      (by decide) (by simp +decide [sev, Env.get_cons, Env.get, cscParams, ctxEnv]; exact cellA_pair2 C oq j (by omega)) ?_
    have hdj := hden cs[j] (List.getElem_mem hjl)
    set ci : IConstantInfo := .ctorInfo cs[j].1 nP cs[j].2 T with hci
    rw [consSumCtors_drop nP T cs j hjl fe]
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => (pure (consSumCtors nP T (cs.drop (j + 1)) (fe.push ci)) :
      AM IFEnv)) (by simp [hci]) ?_
    refine specR_callNC (C := ctxNew C fe EH envM H) (D := ctxLocals ++ cscLocals) cscX fConstRec cwParams
      [vv cscO, .const 4, vv cscNP, vv cscF, vv cscT, .const 0, .const 0, .const 0] (cwBody C)
      [cellA C oc, 4, BitVec.ofNat 64 nP, BitVec.ofNat 64 cs[j].2, Enc.idxW T, 0, 0, 0]
      (by decide) rfl (by decide) hc.cw ?_
      (PostCW (ctxNew C fe EH envM H) cs[j].1 4 [BitVec.ofNat 64 nP, BitVec.ofNat 64 cs[j].2, Enc.idxW T, 0, 0, 0] s)
      (fun _ w s' C' => s' = s ∧ ∃ EH2 ox, C' = ctxE (ctxNew C fe EH envM H) EH2 ∧ EH <+: EH2 ∧
        w = ecell C ox ∧ CIE C.EB EH2 ox ci)
      (fun _ w s' st ⟨hs', EH2, ox, hp2, _, hw, hcve, htg, hfs, hsr⟩ => by subst hs'; exact ⟨_, ⟨rfl, EH2, ox, rfl, hp2, hw, hcve, htg,
        ⟨by simpa using hfs 0 (by simp), hnP⟩, ⟨by simpa using hfs 1 (by simp), hnfe.2⟩,
        by simpa using hfs 2 (by simp)⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cwParams _ rfl hlk)
        (cw_spec (ctxNew C fe EH envM H) hok (by ctx_tr hc.cp) cs[j].1 oc (cvRep_mono hpH hcv)
          (by have := hdj.2.2; omega) 4 _ _ _ 0 0 0 s))
      (fun _ w s3 C3 ⟨hs3, EH2, ox, eC, hpE2, hw, hcie⟩ => ?_)
    · exact ⟨by simp +decide [sev, Env.get_cons], rfl, by simp +decide [sev, Env.get_cons, Env.get, cscParams, ctxEnv],
        by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, cscParams, ctxEnv],
        rfl, rfl, rfl, trivial⟩
    subst eC hw s3
    refine UD.specR_heapLoadI' (C := ctxE (ctxNew C fe EH envM H) EH2) cscNm (vv cscO) oc _ (get_prefix hcv.1 hpH)
      (by decide) (by simp +decide [sev, Env.get_cons]; rfl) ?_
    refine specR_atEntry fun t5 ht5 => ?_
    have hd5 : CVDen cs[j].1 s.store := cvDen_ext hdj ht5.sr.floor
    have hnj : fe.find? cs[j].1.name = none := hnew _ (by rw [List.drop_eq_getElem_cons hjl]; exact List.mem_cons_self)
    have hdn : NewDen ci s.store := by
      refine ⟨hd5.1, hd5.2.1, hd5.2.2, fun _ _ _ h => (by simp [hci] at h), fun _ _ h => (by simp [hci] at h)⟩
    refine specR_idxInsI (C := ctxNew C fe EH envM H) hok hc.k.s hc.k.i hg ci hnj
      (fun _ _ _ _ _ h => by simp [hci] at h) EH2 ox hpE2 hdn (vv cscNm) (vv cscX) cscRi (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl)
      (fun v hv => by simp +decide [sev, Env.get_cons] at hv; exact hv.symm) (by simp +decide [sev, Env.get_cons]; rfl)
      (by simp +decide [Env.get_cons, Env.get, cscParams, ctxEnv]) (fun wr2 => ?_)
    have hokI := ctxOK_ins hok hpE2 hcie (pushOld_find fe ci) (pushOld_findTable hg ci hnj)
    have hfP : ∀ n, (fe.push ci).find? n = (ctxIns (ctxNew C fe EH envM H) ((fe.push ci).setFlags fe.natLit fe.strLit)
        EH2 (envM.insert ci.name (ecell C ox))).fe.find? n := fun n => (IFEnv.setFlags_find? _ _ _ n).symm
    have htP : ∀ n, (fe.push ci).findTable? n = (ctxIns (ctxNew C fe EH envM H) ((fe.push ci).setFlags fe.natLit
        fe.strLit) EH2 (envM.insert ci.name (ecell C ox))).fe.findTable? n := fun n => by
      show _ = ((fe.push ci).setFlags fe.natLit fe.strLit).findTable? n
      unfold IFEnv.findTable?; rw [IFEnv.setFlags_find?, IFEnv.setFlags_rawTable?]
    obtain ⟨hfn, hfs⟩ := push_flags_found (C := ctxNew C fe EH envM H) hF hL ci ox EH2
    refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => (pure (consSumCtors nP T (cs.drop (j + 1)) (fe.push ci)) :
      AM IFEnv)) (by simp) ?_
    refine specR_callNC (C := ctxIns (ctxNew C fe EH envM H) ((fe.push ci).setFlags fe.natLit fe.strLit) EH2
        (envM.insert ci.name (ecell C ox))) (D := ctxLocals ++ cscLocals) cscFl fFlags [] [] Decl.flBody []
      (by decide) rfl (by decide) hc.flags trivial
      (fun a w s' st => PostFl (ctxIns (ctxNew C fe EH envM H) ((fe.push ci).setFlags fe.natLit fe.strLit) EH2
        (envM.insert ci.name (ecell C ox))) (fe.push ci) a w s' st ∧ s' = s)
      (fun _ w s' C' => s' = s ∧ ∃ H6, C' = ctxFe (ctxH (ctxIns (ctxNew C fe EH envM H) ((fe.push ci).setFlags fe.natLit
        fe.strLit) EH2 (envM.insert ci.name (ecell C ox))) H6) (fe.push ci) ∧ H <+: H6)
      (fun a w s' st ⟨⟨H6, hp6, hsr⟩, hs'⟩ => ⟨_, ⟨hs', H6, rfl, hp6⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [] _ rfl hlk)
        (specR_pureState (fl_spec _ hokI (by ctx_tr hc.natF) (by ctx_tr hc.strF) (by ctx_tr hc.k.g) (by ctx_tr hc.k.p)
          s hfP htP hfn hfs)))
      (fun _ w s5 C5 ⟨hs5, H6, eC, hp6⟩ => ?_)
    subst eC s5
    have hokF := ctxOK_fe (ctxOK_H hokI H6) (fe := fe.push ci) (fun n => hfP n) (fun n => htP n)
    have hnew' : ∀ c ∈ cs.drop (j + 1), (fe.push ci).find? c.1.name = none := by
      intro c hcm
      rw [IFEnv.find?_push]
      have hndj : ((cs.drop j).map (·.1.name)).Nodup := hnd.sublist ((List.drop_sublist j cs).map _)
      rw [List.drop_eq_getElem_cons hjl, List.map_cons, List.nodup_cons] at hndj
      have hne : cs[j].1.name ≠ c.1.name := fun h => hndj.1 (List.mem_map.mpr ⟨c, hcm, h.symm⟩)
      have hne' : (ci.name == c.1.name) = false := by show (cs[j].1.name == c.1.name) = false; simpa using hne
      rw [if_neg (by simp [hne'])]
      exact hnew c (by rw [List.drop_eq_getElem_cons hjl]; exact List.mem_cons_of_mem _ hcm)
    refine specR_congr (m' := (pure (consSumCtors nP T (cs.drop (j + 1)) (fe.push ci)) : AM IFEnv) >>= fun r => pure r)
      (by simp only [bind_pure]) ?_
    refine specR_callNC (C := ctxFe (ctxH (ctxIns (ctxNew C fe EH envM H) ((fe.push ci).setFlags fe.natLit fe.strLit)
        EH2 (envM.insert ci.name (ecell C ox))) H6) (fe.push ci)) (D := ctxLocals ++ cscLocals) cscR fConsCtors cscParams
      [vv cscC, .op .add [vv cscI, .const 1], vv cscN, vv cscNP, vv cscT] (cscBody C)
      [cellA C oq, BitVec.ofNat 64 (j + 1), BitVec.ofNat 64 cs.length, BitVec.ofNat 64 nP, Enc.idxW T]
      (by decide) rfl (by decide) hc.self ?_
      (PostEnv C) (fun r w s' C' => ∃ EH envM H, C' = ctxNew C r EH envM H ∧ C.EH <+: EH ∧ C.H <+: H ∧
        CtxOK (ctxNew C r EH envM H) ∧ TblGate r ∧ FlagsOK r ∧ LitsPinned r C.pins)
      (fun r w s' st ⟨EH, envM, H, h1, h2, h3, h4, h5⟩ => ⟨_, ⟨EH, envM, H, rfl, h1, h2, h3, h5⟩, h4⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cscParams _ rfl hlk)
        (ih (j + 1) (fe.push ci) EH2 (envM.insert ci.name (ecell C ox)) H6 s (by omega) (by omega) (hpH.trans hp6)
          (hpE.trans hpE2) hokF (hg.push ci) (hF.push ci) (by unfold LitsPinned; rw [IFEnv.push_base]; exact hL) hnew'))
      (fun r w s6 C6 ⟨EH7, envM7, H7, eC, h1, h2, h3, h4⟩ => ?_)
    · exact ⟨by simp +decide [sev, Env.get_cons, Env.get, cscParams, ctxEnv] <;> rfl,
        by simp +decide [sev, Env.get_cons, Env.get, cscParams, ctxEnv]; exact e_succ j,
        by simp +decide [sev, Env.get_cons, Env.get, cscParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cscParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, cscParams, ctxEnv], trivial⟩
    subst eC
    exact specR_returnI _ 0 rfl (fun t ht => ⟨EH7, envM7, H7, h1, h2, h3, sr_of_eq ht.sr rfl rfl rfl rfl, h4⟩)

end

end ConPanqueque.T.Ind
