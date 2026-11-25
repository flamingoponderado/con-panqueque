import ConPanqueque.T.Ind.IdxIns

/-!
# A former's telescope (`checkBlockTele`)

The former's constant checked, its type stripped of `nP + nIdx` binders to a sort (`checkSumTele`), stripped
again and the body compared with that sort interned. Returns the sort's level.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.Decl ConPanqueque.T.WC

/-- What `checkConstantVal` runs. -/
structure CcvCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  g : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one)
  pr : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one)
  pim : C.code.lookup fPim = some (Decl.pmParams.map (fun p => (p, ShapeHOL.one)), pimBody C, .one)
  k : KCodes C Comp.kBodies
  ac : Comp.AllCodes mode C
  cl : C.code.lookup fLso = some ([lsQ].map (fun p => (p, ShapeHOL.one)), lsoBody C, .one)
  lso : LsoCodes C
  ndh : C.code.lookup fNdh = some (ndhParams.map (fun p => (p, ShapeHOL.one)), ndhBody, .one)
  ndg : C.code.lookup fNdg = some (ndgParams.map (fun p => (p, ShapeHOL.one)), ndgBody, .one)
  lbb : C.code.lookup ExM.fLBB = some ([pFu, ExM.pKb, pH].map (fun p => (p, ShapeHOL.one)), ExM.lbbBody, .one)
  cB : ExB.CodesB C (ExB.bodyB C)
  bvb : C.code.lookup ExB.fBvarB = some ([(pFu, .one), (pH, .one)], ExB.bvbBody C, .one)
  hf : C.code.lookup ExM.fHasFvar = some ([pFu, pH].map (fun p => (p, ShapeHOL.one)), ExM.hasFvarBody, .one)
  cF : ExF.CodesF C (ExF.bodyF C)
  fvb : C.code.lookup ExF.fFvarB = some ([(pFu, .one), (pH, .one)], ExF.fvbBody C, .one)
  atl : C.code.lookup fAt = some (atParams.map (fun p => (p, ShapeHOL.one)), atBody, .one)
  al : AlCodes C
  crff : C.code.lookup fCrff = some ([crffE].map (fun p => (p, ShapeHOL.one)), crffBody, .one)
  crf : CrfCodes C
  ens : C.code.lookup fEns = some (kParams.map (fun p => (p, ShapeHOL.one)), ensBody, .one)
  ccv : C.code.lookup fCcv = some (ccvParams.map (fun p => (p, ShapeHOL.one)), ccvBody C, .one)

def ctC := ofString "ct_c"
def ctN := ofString "ct_n"
def ctX := ofString "ct_x"
def ctT := ofString "ct_t"
def ctS := ofString "ct_s"
def ctSc := ofString "ct_sc"
def ctB := ofString "ct_b"
def ctU := ofString "ct_u"
def ctS2 := ofString "ct_s2"
def ctSc2 := ofString "ct_sc2"
def ctB2 := ofString "ct_b2"
def ctSr := ofString "ct_sr"
def fBlockTele := ofString "checkBlockTele"

def ctParams : List MlS := [ctC, ctN]
def ctLocals : List MlS := [ctX, ctT, ctS, ctSc, ctB, lFl, lDh, lDt, lDg, lDi, lRp, lRn, ctU, ctS2, ctSc2, ctB2, ctSr]

/-- After the sort is read: the second strip and the comparison with the interned sort. -/
def ctTail : ProgHOL 64 :=
  .seq (.assign .local ctU (.load .one (vv lRp)))
  (.seq (.call (some (some (.local, ctS2), none)) fStripPis [vv ctN, vv ctT])
  (.ite (.cmp .equal (vv ctS2) (.const 0)) hang
  (.seq (.assign .local ctSc2 (.load .one (vv ctS2)))
  (.seq (.assign .local ctB2 (.load .one (.op .add [vv ctS2, .shift .lsl (vv ctSc2) (.const 3)])))
  (.seq (.call (some (some (.local, ctSr), none)) fInternSort [vv ctU])
  (.ite (.cmp .equal (vv ctB2) (vv ctSr)) (.return (vv ctU)) hang))))))

/-- `checkBlockTele` at the former's constant `ctC` and the telescope length `ctN = nP + nIdx`. -/
def ctBody : ProgHOL 64 := prologue ctLocals
  (.seq (.call (some (some (.local, ctX), none)) fCcv [vv ctC, .const 0, .const 0, .const 0])
  (.seq (.assign .local ctT (.load .one (.op .add [vv ctC, .const 16])))
  (.seq (.call (some (some (.local, ctS), none)) fStripPis [vv ctN, vv ctT])
  (.ite (.cmp .equal (vv ctS) (.const 0)) hang
  (.seq (.assign .local ctSc (.load .one (vv ctS)))
  (.seq (.assign .local ctB (.load .one (.op .add [vv ctS, .shift .lsl (vv ctSc) (.const 3)])))
  (viewOf ctB
  (.ite (veEqC lDg 2) ctTail hang))))))))

section
variable {σ : Type}

theorem ct_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ctLocals → (ctxEnv C ++ ctParams.zip vals).get x = none :=
  Knot.params_none C ctLocals ctParams vals (by decide) (by decide)

/-- `checkBlockTele`'s answer: the former as given, its sort's level as the word; the heap grown. -/
def PostCT (C : Ctx) (cv : IConstantVal) (r : IConstantVal × LIdx) (w : BitVec 64) (s' : AState) (st : PState σ) :
    Prop :=
  r.1 = cv ∧ w = Enc.idxW r.2 ∧ ∃ H', C.H <+: H' ∧ SR (ctxH C H') s' st

theorem postCT_locals (C : Ctx) (cv : IConstantVal) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostCT C cv a w s' st → PostCT C cv a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨h1, h2, H', h3, h4⟩ => ⟨h1, h2, H', h3, sr_of_eq h4 rfl rfl rfl rfl⟩

/-- **`checkBlockTele`** at a member. -/
theorem ct_spec (mode : ConLeche.CheckMode) (fe : IFEnv) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx)
    (hok : CtxOK C) (hs : C.side = false) (hcc : CcvCodes mode C)
    (hcs : C.code.lookup fStripPis = some ([(pFu, .one), (pH, .one)], stripBody C fStripPis 6, .one))
    (hcS : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one))
    (hfe : fe = C.fe) (nP : Nat) (ms : MemberShape) (oc : Nat) (hn : nP + ms.nIdx < 2 ^ 64)
    (H : List (BitVec 64)) (hp : C.H <+: H) (hcv : CVRep C H oc ms.cvT)
    (hlen : ms.cvT.levelParams.length < 2 ^ 62) (ks : List ConLeche.Name) (hkl : ks.length = ms.cvT.levelParams.length)
    (hks : ∀ j (hj : j < ms.cvT.levelParams.length), denoteN C.St.ns ms.cvT.levelParams[j] = some (ks[j]'(by omega)))
    (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (ctParams.zip [cellA C oc, BitVec.ofNat 64 (nP + ms.nIdx)])) ctBody s
      (checkBlockTele mode fe nP ms) (PostCT (ctxH C H) ms.cvT) := by
  refine specR_prologue (postCT_locals _ _) (ct_none _ _) ?_
  obtain ⟨hn0, ⟨wl, hwl, ol, hwlo, hebl⟩, hty⟩ := hcv
  have hbl : BlkAt H ol (ms.cvT.levelParams.map Enc.idxW) := hebl
  unfold checkBlockTele
  -- the constant check
  refine specR_callNIH (C := ctxH C H) ctX fCcv ccvParams [vv ctC, .const 0, .const 0, .const 0] (ccvBody C)
    [cellA C oc, boolW false, boolW false, boolW false] (by decide) rfl (by decide) hcc.ccv
    ⟨by simp +decide [sev, Env.get, ctParams, ctxEnv], rfl, rfl, rfl, trivial⟩
    (Decl.PostU (ctxH C H)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ccvParams _ rfl hlk)
      (ccv_full mode (ctxH C H) (ctxOK_H hok H) hcc.g hcc.pr hcc.pim ra hs (by ctx_tr hcc.k) (by ctx_tr hcc.ac) hcc.cl
        (by ctx_tr hcc.lso) hcc.ndh hcc.ndg hcc.lbb (by ctx_tr hcc.cB) hcc.bvb hcc.hf (by ctx_tr hcc.cF) hcc.fvb hcc.atl
        (by ctx_tr hcc.al) hcc.crff (by ctx_tr hcc.crf) hcc.ens fe hfe ms.cvT false false false oc ol hn0
        (by show H[oc + 1]? = _; rw [hwl, hwlo]; rfl) hty hbl hlen ks hkl hks s))
    (fun _ w s1 H1 hp1 _ => ?_)
  have hp1' : H <+: H1 := hp1
  refine UD.specR_heapLoadI' (C := ctxH C H1) ctT _ (oc + 2) _ (get_prefix hty hp1') (by decide)
    (by simp +decide [sev, Env.get, ctParams, ctxEnv]; exact cellA_add_ofNat C oc 2) ?_
  -- the first strip
  unfold checkSumTele
  simp only [bind_assoc]
  refine ro_strip C hok hcs (nP + ms.nIdx) hn ms.cvT.type H1 s1 ctS (vv ctN) (vv ctT) (by decide)
    (by simp +decide [sev, Env.get, ctParams, ctxEnv]) (by simp +decide [sev, Env.get])
    (fun o w s2 H2 hp2 hr2 hn2 hs2 => ?_)
  have hp2' : H1 <+: H2 := hp2
  rcases o with _ | ⟨tys, b⟩
  · rw [hn2 rfl]
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  obtain ⟨ob, rfl, hba⟩ := hs2 tys b rfl
  obtain ⟨ha0, haL, -⟩ := strip_last hba
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN => ?_)
  have hol := blkAt_lt hba
  have hHN' : H2.length ≤ C.HN := hHN
  have hne : cellA C ob ≠ 0 := cellA_ne0 C hok ob (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne)
    (fun h => absurd rfl h) (fun _ => ?_)
  refine UD.specR_heapLoadI' (C := ctxH C H2) ctSc (vv ctS) ob _ ha0 (by decide) (by simp [sev, Env.get]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H2) ctB _ (ob + 1 + tys.length) _ haL (by decide)
    (by
      simp only [sev, sev_vv, Env.get_cons]; simp +decide
      show cellA C ob + _ = cellA C _
      rw [cellA_shl3]; congr 1; omega) ?_
  -- the body's view
  unfold viewOf
  refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get_cons, Env.get, ctParams, ctxEnv] <;> rfl) ?_
  refine specR_assignI lDh (vv ctB) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
  refine ConPanqueque.T.Big.specR_viewP b (by simp) (by simp +decide [Env.get_cons] <;> rfl)
    (by simp +decide [Env.get_cons, Env.get, ctParams, ctxEnv] <;> rfl) (by decide) (fun vb P hvb htnb hlenb => ?_)
  have hatb := tag_of_tagN htnb
  by_cases h2 : vb.tagN = 2
  swap
  · refine specR_ifI _ _ (by
        simp only [veEqC]
        rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 vb.tagN) (BitVec.ofNat 64 2) (by simp [sev, Env.get_cons]) rfl,
          wcE' _ _ (by have := ConPanqueque.T.Big.tagN_lt vb; omega) (by omega)]) (fun h => ?_) (fun _ => specR_hangI)
    exfalso; simp [boolW, h2] at h
  refine specR_ifI _ _ (by
      simp only [veEqC]
      rw [sev_cmp2 _ _ _ _ (BitVec.ofNat 64 vb.tagN) (BitVec.ofNat 64 2) (by simp [sev, Env.get_cons]) rfl,
        wcE' _ _ (by have := ConPanqueque.T.Big.tagN_lt vb; omega) (by omega)]) (fun _ => ?_)
    (fun h => absurd h (by simp [boolW, h2]))
  rcases vb with _ | _ | u | _ | _ | _ | _ | _ | _ | _ <;> simp [ENodeView.tagN] at h2
  have htb : b.tag = ETag.sort := by rw [hatb]; rfl
  simp only [htb, beq_self_eq_true, ite_true, bind_assoc]
  refine specR_runBind (show viewSort b s2 = .ok (some u, s2) by
    rw [Comp.viewSort_run, WC.viewSort_of_view htb hvb]) ?_
  simp only [pure_bind]
  unfold ctTail
  refine specR_loadI' ctU (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW u) (by decide) (by simp) (by simp)
    (by simpa [encEView, Enc.encSort] using wordsAt_mem0 P _ [] []) ?_
  -- the second strip
  refine ro_strip C hok hcs (nP + ms.nIdx) hn ms.cvT.type H2 s2 ctS2 (vv ctN) (vv ctT) (by decide)
    (by simp +decide [sev, Env.get, ctParams, ctxEnv]) (by simp +decide [sev, Env.get])
    (fun o w s3 H3 hp3 hr3 hn3 hs3 => ?_)
  have hp3' : H2 <+: H3 := hp3
  rcases o with _ | ⟨tys', b'⟩
  · rw [hn3 rfl]
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  obtain ⟨ob', rfl, hba'⟩ := hs3 tys' b' rfl
  obtain ⟨ha0', haL', -⟩ := strip_last hba'
  refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN3 => ?_)
  have hol' := blkAt_lt hba'
  have hHN3' : H3.length ≤ C.HN := hHN3
  have hne' : cellA C ob' ≠ 0 := cellA_ne0 C hok ob' (by omega)
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne')
    (fun h => absurd rfl h) (fun _ => ?_)
  refine UD.specR_heapLoadI' (C := ctxH C H3) ctSc2 (vv ctS2) ob' _ ha0' (by decide) (by simp [sev, Env.get]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H3) ctB2 _ (ob' + 1 + tys'.length) _ haL' (by decide)
    (by
      simp only [sev, sev_vv, Env.get_cons]; simp +decide
      show cellA C ob' + _ = cellA C _
      rw [cellA_shl3]; congr 1; omega) ?_
  dsimp only
  -- the sort interned, compared
  refine ILP.callE_spec ctSr fInternSort [lEu] [vv ctU] sortBody [Enc.idxW u] (by decide) rfl (by decide) hcS
    ⟨by simp +decide [sev, Env.get], trivial⟩ (sort_body_spec ra (ctxH C H3) (ctxOK_H hok H3) s3 u) (fun srt s4 => ?_)
  by_cases heq : b' = srt
  · subst heq
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    simp only [beq_self_eq_true, ite_true]
    exact specR_returnI _ (Enc.idxW u) (by simp +decide [Env.get])
      (fun t ht => ⟨rfl, rfl, H3, (hp1'.trans hp2').trans hp3', sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  · have hw : Enc.idxW b' ≠ Enc.idxW srt := fun h => heq (ConPanqueque.V.Enc.idxW_inj h)
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hw])
      (fun h => absurd rfl h) (fun _ => specR_hangI)

end

end ConPanqueque.T.Ind
