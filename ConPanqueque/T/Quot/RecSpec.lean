import ConPanqueque.T.Quot.ArmSpec

/-!
# `quotAt` and the install at a quotient recursor slot (`Quot.lift`, `Quot.ind`): the proof
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Quot

set_option autoImplicit false

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.Decl
open ConPanqueque.T.Lit ConPanqueque.Logic.PlainIntern
open ConPanqueque.T.ILP (fInstLPF ilpfBody ilpf_spec CodesILP ilpParams ilpBody PostILP)
open ConPanqueque.T.Ind (fParamLevels plParams plBody pl_spec PostLsH fPlFill pfParams pfBody)

/-- The recursor slots. -/
def QKR (k : ConLeche.QuotKind) (j : Nat) : Prop := (k = .lift ∧ j = 2) ∨ (k = .ind ∧ j = 3)

/-- The interned recursor pins: one rule, at `Quot.mk`, one field, firing at one level. -/
theorem quotBlk_rec {k : ConLeche.QuotKind} {j : Nat} (hkj : QKR k j)
    {s s' : AState} {blk : List IConstantInfo} (h : plainCIList quotBasis s = .ok (blk, s')) :
    ∃ v c u r, blk.getD j default = .recInfo v (recMI j) (recMI j) false [⟨c, 1, .levels [u], r⟩] := by
  simp only [quotBasis, ConLeche.BasisKind.decls, ConLeche.quotBasis, plainCIList] at h
  obtain ⟨_, _, -, h1⟩ := AM.bind_ok h
  obtain ⟨_, _, h2, h3⟩ := AM.bind_ok h1
  obtain ⟨rfl, -⟩ := AM.pure_ok h3
  obtain ⟨_, _, -, h4⟩ := AM.bind_ok h2
  obtain ⟨_, _, h5, h6⟩ := AM.bind_ok h4
  obtain ⟨rfl, -⟩ := AM.pure_ok h6
  obtain ⟨r2, _, h7, h8⟩ := AM.bind_ok h5
  obtain ⟨_, _, h9, h10⟩ := AM.bind_ok h8
  obtain ⟨rfl, -⟩ := AM.pure_ok h10
  obtain ⟨r3, _, h11, h12⟩ := AM.bind_ok h9
  obtain ⟨_, _, -, h13⟩ := AM.bind_ok h12
  obtain ⟨rfl, -⟩ := AM.pure_ok h13
  rcases hkj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [ConLeche.quotLiftA, plainCI, plainRules, plainRule, plainFire, internLevelList, ConLeche.BasisDSL.ruleAt,
      bind_assoc] at h7
    obtain ⟨v, _, -, g1⟩ := AM.bind_ok h7
    obtain ⟨c, _, -, g2⟩ := AM.bind_ok g1
    obtain ⟨u, _, -, g3⟩ := AM.bind_ok g2
    obtain ⟨_, _, g4, g5⟩ := AM.bind_ok g3
    obtain ⟨rfl, -⟩ := AM.pure_ok g4
    try simp only [pure_bind] at g5
    obtain ⟨r, _, -, g6⟩ := AM.bind_ok g5
    try simp only [pure_bind] at g6
    obtain ⟨rfl, -⟩ := AM.pure_ok g6
    exact ⟨v, c, u, r, rfl⟩
  · simp only [ConLeche.quotIndA, plainCI, plainRules, plainRule, plainFire, internLevelList, ConLeche.BasisDSL.ruleAt,
      bind_assoc] at h11
    obtain ⟨v, _, -, g1⟩ := AM.bind_ok h11
    obtain ⟨c, _, -, g2⟩ := AM.bind_ok g1
    obtain ⟨u, _, -, g3⟩ := AM.bind_ok g2
    obtain ⟨_, _, g4, g5⟩ := AM.bind_ok g3
    obtain ⟨rfl, -⟩ := AM.pure_ok g4
    try simp only [pure_bind] at g5
    obtain ⟨r, _, -, g6⟩ := AM.bind_ok g5
    try simp only [pure_bind] at g6
    obtain ⟨rfl, -⟩ := AM.pure_ok g6
    exact ⟨v, c, u, r, rfl⟩

theorem quotSlot_denCI {s s1 : AState} {blk : List IConstantInfo} (hst : StateOK s) (ho : InternRerun.Off s.store)
    (hr : plainCIList quotBasis s = .ok (blk, s1)) (j : Nat) (hj : j < 5) :
    ∃ x : ConLeche.ConstantInfo, Frontend.denoteCI s1.store (blk.getD j default) = some x := by
  have hd := basisDecls_plain .quotK ho hr
  obtain ⟨hs1, hden⟩ := ConRon.Bridge.BasisKind.decls_run hst hd
  have hlen := denoteCIList_length blk _ hden
  have hjl : j < blk.length := by rw [hlen]; simp [ConLeche.BasisKind.decls, ConLeche.quotBasis]; omega
  obtain ⟨x, -, hx⟩ := denoteCIList_get blk _ j blk[j] hden (List.getElem?_eq_getElem hjl)
  refine ⟨x, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl, Option.getD_some]
  exact hx

theorem denoteCI_rec1 {st : EStore} {v : IConstantVal} {mI rP : Nat} {isK : Bool} {c : NIdx} {nf : Nat} {u : LIdx}
    {r : EIdx} {x : ConLeche.ConstantInfo}
    (h : Frontend.denoteCI st (.recInfo v mI rP isK [⟨c, nf, .levels [u], r⟩]) = some x) :
    (denoteL st.ls u).isSome = true ∧ (denoteE st r).isSome = true := by
  simp only [Frontend.denoteCI] at h
  split at h
  · rename_i cv rules hcv hrs
    simp only [Frontend.denoteRules] at hrs
    split at hrs
    · rename_i x0 xs h0 h1
      simp only [Frontend.denoteRule] at h0
      split at h0
      · rename_i c0 f0 r0 hc0 hf0 hr0
        simp only [Frontend.denoteFire, Option.map_eq_some_iff] at hf0
        obtain ⟨ls, hls, -⟩ := hf0
        simp only [denoteLList] at hls
        refine ⟨?_, by rw [hr0]; rfl⟩
        cases hu : denoteL st.ls u with
        | none => rw [hu] at hls; simp [opt2] at hls
        | some _ => rfl
      · cases h0
    · cases hrs
  · cases h

section
variable {σ : Type}

theorem specR_appendNil {β : Type} {P : PState σ → Prop} {c : ProgHOL 64} {s : AState} {m : AM (List LIdx)}
    {K : List LIdx → AM β} {R : β → BitVec 64 → AState → PState σ → Prop}
    (h : SpecR P c s ((m >>= fun hs => pure ([] ++ hs)) >>= K) R) : SpecR P c s (m >>= K) R :=
  specR_congr (by simp) h

/-- The twin's name reads: caches only. -/
theorem specR_readNamesI {β : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {c : ProgHOL 64}
    {k : List ConLeche.Name → AM β} {R : β → BitVec 64 → AState → PState σ → Prop} (us : List NIdx)
    (xs : List ConLeche.Name) (hd : Frontend.denoteNList s.store.ns us = some xs)
    (h : ∀ c1 : Caches, SpecR (Inv C (withC s c1) Γ M D) c (withC s c1) (k xs) R) :
    SpecR (Inv C s Γ M D) c s (readNamesM us >>= k) R := by
  intro t ht
  obtain ⟨c1, e1, ec1, ok1⟩ := ConPanqueque.T.ILP.readNamesM_eq us s xs ht.sr.cok.rn hd
  exact specR_quiet e1 rfl rfl (by rw [ec1]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩) rfl
    (fun hc => cachesOK_caches hc c1 ec1 ok1) (h c1) t ht

set_option maxHeartbeats 8000000 in
/-- **`quotAt` and the install at a recursor slot.** -/
theorem restR_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode)
    (C : Ctx) (hok : CtxOK C) (hc : QCodes mode C)
    (hpl : C.saved = none) (hg : TblGate C.fe) (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins)
    (hf : ConPanqueque.Front.FrontOK C) (hA : denoteN C.St.ns default = some .anonymous)
    (k : ConLeche.QuotKind) (j : Nat) (hkj : QKR k j)
    (cv : IConstantVal) (q : Nat) (hrc : RecCVQ C q cv) (ol : Nat) (hb : BlkAt C.H ol (cv.levelParams.map Enc.idxW))
    (T : IFEnv → AM IFEnv) (hT : ∀ fe s', s'.pins = C.pins → T fe s' = .ok (fe, s'))
    (H4 : List (BitVec 64)) (hp04 : C.H <+: H4) (s3 : AState) (Γ' : Env) (hB' : Base C q Γ')
    (hRL : Γ'.get kqRL = some (cellA C ol)) :
    SpecR (σ := σ) (Inv (ctxH C H4) s3 Γ' [] (ctxLocals ++ kqLocals))
      (restR C j) s3 (do let ci ← quotAt k cv; let fe₂ ← installBasisDecl C.fe ci; flushCaches; T fe₂)
      (PostStep C) := by
  have hj5 : j < 5 := by rcases hkj with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  have hslot : k.slot = j := by rcases hkj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  obtain ⟨-, ks, -, -, -, -, hlen, hkl, hks, htyD⟩ := hrc
  have hD : ∀ x ∈ kqLocals, x ∈ ctxLocals ++ kqLocals := fun x hx => List.mem_append_right _ hx
  have G : GenEnv C (ctxLocals ++ kqLocals) 12 :=
    ⟨hok, hf, hA, hc.e, hD _ (by simp [kqLocals]), hD _ (by simp [kqLocals]),
      fun c hc' j hj => hD _ (List.mem_append_right _ (gv_mem_genLocals hc' hj))⟩
  have hq : ∀ x ∈ [qN, qL, qT, qU, qX, qW], x ∈ ctxLocals ++ kqLocals := fun x hx => hD x (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [kqLocals])
  unfold restR
  unfold quotAt quotPin
  simp only [bind_assoc]
  refine specR_fact (fun t ht => sr_stateOK ht.sr) (fun hst3 => ?_)
  refine specR_offCheckI ⟨hD _ (by simp [kqLocals]), hD _ (by simp [kqLocals]), hD _ (by simp [kqLocals]),
    hD _ (by simp [kqLocals])⟩ (fun ho3 => ?_)
  refine specR_basisQuot ho3 ?_
  have hB6 : Base C q ((ocD, 0) :: (ocC, 0) :: (ocB, 0) :: (ocA, 0) :: Γ') :=
    base_cons (base_cons (base_cons (base_cons hB' (by decide) (by decide) _) (by decide) (by decide) _)
      (by decide) (by decide) _) (by decide) (by decide) _
  refine quotSlot_spec ra G hq j hj5 H4 _ _ [] s3
    (fun blk2 s4 Γ2 H5 hp5 ag2 hr2 hP2 hX2 => ?_)
  have hB7 := base_agreeQ hB6 ag2
  have hRL7 : Γ2.get kqRL = some (cellA C ol) := by
    rw [ag2 kqRL (fun c j e => gv_ne_of (m := kqRL) (by simp [kqRL, ofString]) e.symm) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]
    simp +decide only [Env.get_cons, ite_true, ite_false]; exact hRL
  simp only [pure_bind, hslot]
  obtain ⟨v, c, u, r, hp2⟩ := quotBlk_rec hkj hr2
  obtain ⟨xCI, hxCI⟩ := quotSlot_denCI hst3 ho3 hr2 j hj5
  rw [hp2] at hxCI hP2 hX2
  obtain ⟨hudn, hrdn⟩ := denoteCI_rec1 hxCI
  obtain ⟨-, hlpP4, htyP4⟩ := ConRon.Bridge.denoteCV_inv (denoteCI_toConstantVal hxCI)
  obtain ⟨hPN2, ⟨op2, hPL2, hPb2⟩, hPT2⟩ := hP2
  obtain ⟨rl, u', hrs, hfire, hXc, hXu, hXw⟩ := hX2.2 _ _ _ _ _ rfl
  simp only [List.cons.injEq, and_true] at hrs
  subst hrs
  simp only [IRecRuleFire.levels.injEq, List.cons.injEq, and_true] at hfire
  subst hfire
  obtain ⟨hst4, -, -⟩ := quotSlot_den hst3 ho3 hr2 j hj5
  have hp45 : H4 <+: H5 := hp5
  have hp05 : C.H <+: H5 := hp04.trans hp45
  rw [hp2]
  simp only [IConstantInfo.atLps, IConstantVal.atLps, rulesAtLps, IRecRuleFire.atLps, bind_assoc, pure_bind]
  unfold atLpsP
  refine specR_fact (fun t ht => ht.sr.floor) (fun hfl4 => ?_)
  have hlpd4 : Frontend.denoteNList s4.store.ns cv.levelParams = some ks :=
    denoteNList_of_get _ _ hkl (fun j hj => denoteN_ext (hks j hj) hfl4)
  -- the type at the record's levels
  refine specR_callNIH (C := ctxH C H5) kqUs fParamLevels plParams [vv kqRL] (plBody C) [cellA C ol] (by decide) rfl
    (hD _ (by simp [kqLocals])) hc.pl ⟨by simp only [sev, sev_vv, hRL7], trivial⟩
    (fun a w s' st => paramLevels cv.levelParams s4 = .ok (a, s') ∧ PostLsH (ctxH C H5) a w s' st)
    (fun a w s' H' => paramLevels cv.levelParams s4 = .ok (a, s') ∧ w = Enc.idxW a)
    (fun a w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hr, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (fun w hw => by
      subst hw
      exact pl_spec ra C hok hc.pl hc.pf hc.ilp1 hc.e.ls cv.levelParams ol (by omega) H5 s4 (blkAt_mono hb hp05) _
        (pre_of_lookups hu plParams _ rfl hlk)))
    (fun us1 wu s5 H6 hp6 ⟨hr6, hwu⟩ => ?_)
  subst hwu
  have hp56 : H5 <+: H6 := hp6
  have hp06 : C.H <+: H6 := hp05.trans hp56
  obtain ⟨hs56, hus1⟩ := ConRon.Bridge.paramLevels_run hst4.ok hlpd4 hr6
  have hlpP5 : Frontend.denoteNList s5.store.ns v.levelParams = _ := denoteNList_ext hs56.ext.lss.ls.ns _ _ hlpP4
  have htyP5 : denoteE s5.store v.type = _ := denote_ext htyP4 hs56.ext
  have hg6 : ∀ x, (x = qN ∨ x = qL ∨ x = qT ∨ x = qU ∨ x = qX ∨ x = qW) →
      Env.get ((kqUs, Enc.idxW us1) :: Γ2) x = Γ2.get x := fun x hx => by
    rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e (by
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide))]
  refine specR_fact (fun t ht => (⟨ht.sr.cok.rn, ht.sr.cok.rl, ht.sr.cok.rls⟩ : ConRon.Bridge.ReadOK s5))
    (fun hrd5 => ?_)
  refine specR_callNIH (C := ctxH C H6) kqTy fInstLPF ilpParams
    [.const (BitVec.ofNat 64 coreWalkFuel), vv qT, vv qL, vv kqUs] (ilpfBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW v.type, cellA C op2, Enc.idxW us1] (by decide) rfl
    (hD _ (by simp [kqLocals])) hc.ilpf
    ⟨rfl, by simp only [sev, sev_vv, hg6 qT (by simp)]; exact hPT2,
      by simp only [sev, sev_vv, hg6 qL (by simp)]; exact hPL2,
      by simp only [sev, sev_vv, Env.get_cons, ite_true], trivial⟩
    (fun a w s' st => instLPFast coreWalkFuel v.levelParams us1 v.type s5 = .ok (a, s') ∧ PostILP (ctxH C H6) a w s' st)
    (fun a w s' _ => instLPFast coreWalkFuel v.levelParams us1 v.type s5 = .ok (a, s') ∧ w = Enc.idxW a)
    (fun a w s' st ⟨hr, H'', hp, hw, hsr⟩ => ⟨H'', hp, ⟨hr, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu ilpParams _ rfl hlk)
      (ilpf_spec ra C hok hc.ilp coreWalkFuel CV.coreWalkFuel_lt op2 v.levelParams _ us1 _ H6 s5
        v.type hlpP5 hus1 (sr_stateOK hu) hu.cok.rn hu.cok.rl hu.cok.rls (by rw [htyP5]; rfl)
        (blkAt_mono hPb2 hp56))))
    (fun ty2 wt s6 H7 hp7 ⟨hr7, hwt⟩ => ?_)
  subst hwt
  obtain ⟨hs67, hty2⟩ := ConRon.Bridge.instLPFast_run hs56.ok hrd5 hlpP5 hus1 htyP5 hr7
  have hp67 : H6 <+: H7 := hp7
  have hp07 : C.H <+: H7 := hp06.trans hp67
  have hg7 : ∀ x, (x = qN ∨ x = qL ∨ x = qT ∨ x = qU ∨ x = qX ∨ x = qW) →
      Env.get ((kqTy, Enc.idxW ty2) :: (kqUs, Enc.idxW us1) :: Γ2) x = Γ2.get x := fun x hx => by
    rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e (by
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)), hg6 x hx]
  -- the levels again
  have hlpd6 : Frontend.denoteNList s6.store.ns cv.levelParams = some ks :=
    denoteNList_ext (hs56.ext.trans hs67.ext).lss.ls.ns _ _ hlpd4
  refine specR_callNIH (C := ctxH C H7) kqUs fParamLevels plParams [vv kqRL] (plBody C) [cellA C ol] (by decide) rfl
    (hD _ (by simp [kqLocals])) hc.pl ⟨by simp +decide only [sev, sev_vv, Env.get_cons, ite_false]; exact hRL7, trivial⟩
    (fun a w s' st => paramLevels cv.levelParams s6 = .ok (a, s') ∧ PostLsH (ctxH C H7) a w s' st)
    (fun a w s' H' => paramLevels cv.levelParams s6 = .ok (a, s') ∧ w = Enc.idxW a)
    (fun a w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hr, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (fun w hw => by
      subst hw
      exact pl_spec ra C hok hc.pl hc.pf hc.ilp1 hc.e.ls cv.levelParams ol (by omega) H7 s6 (blkAt_mono hb hp07) _
        (pre_of_lookups hu plParams _ rfl hlk)))
    (fun us2 wu s7 H8 hp8 ⟨hr8, hwu⟩ => ?_)
  subst hwu
  have hp78 : H7 <+: H8 := hp8
  have hp08 : C.H <+: H8 := hp07.trans hp78
  obtain ⟨hs78, hus2⟩ := ConRon.Bridge.paramLevels_run hs67.ok hlpd6 hr8
  have hext47 : Ext s4.store s7.store := (hs56.ext.trans hs67.ext).trans hs78.ext
  have hlpP7 : Frontend.denoteNList s7.store.ns v.levelParams = _ := denoteNList_ext (hs56.ext.trans (hs67.ext.trans hs78.ext)).lss.ls.ns _ _ hlpP4
  have hlpd7 : Frontend.denoteNList s7.store.ns cv.levelParams = some ks :=
    denoteNList_ext hs78.ext.lss.ls.ns _ _ hlpd6
  -- the reads
  refine specR_readNamesI v.levelParams _ hlpP7 (fun c1 => ?_)
  refine specR_readNamesI cv.levelParams ks hlpd7 (fun c2 => ?_)
  -- the right-hand side at the record's levels
  refine specR_fact (fun t ht => (⟨ht.sr.cok.rn, ht.sr.cok.rl, ht.sr.cok.rls⟩ :
    ConRon.Bridge.ReadOK (withC (withC s7 c1) c2))) (fun hrd7 => ?_)
  have hst7 : StateOK (withC (withC s7 c1) c2) := ⟨hs78.ok.wf⟩
  have hg8 : ∀ x, (x = qN ∨ x = qL ∨ x = qT ∨ x = qU ∨ x = qX ∨ x = qW) →
      Env.get ((kqUs, Enc.idxW us2) :: (kqTy, Enc.idxW ty2) :: (kqUs, Enc.idxW us1) :: Γ2) x = Γ2.get x :=
    fun x hx => by
      rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e (by
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> decide)), hg7 x hx]
  have hrd7' : (denoteE s7.store r).isSome = true := denoteE_isSome_ext hext47 hrdn
  obtain ⟨rv, hrv⟩ := Option.isSome_iff_exists.mp hrd7'
  refine specR_callNIH (C := ctxH C H8) kqH fInstLPF ilpParams
    [.const (BitVec.ofNat 64 coreWalkFuel), vv qW, vv qL, vv kqUs] (ilpfBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW r, cellA C op2, Enc.idxW us2] (by decide) rfl
    (hD _ (by simp [kqLocals])) hc.ilpf
    ⟨rfl, by simp only [sev, sev_vv, hg8 qW (by simp)]; exact hXw,
      by simp only [sev, sev_vv, hg8 qL (by simp)]; exact hPL2,
      by simp only [sev, sev_vv, Env.get_cons, ite_true], trivial⟩
    (fun a w s' st => instLPFast coreWalkFuel v.levelParams us2 r (withC (withC s7 c1) c2) = .ok (a, s') ∧
      PostILP (ctxH C H8) a w s' st)
    (fun a w s' _ => instLPFast coreWalkFuel v.levelParams us2 r (withC (withC s7 c1) c2) = .ok (a, s') ∧
      w = Enc.idxW a)
    (fun a w s' st ⟨hr, H'', hp, hw, hsr⟩ => ⟨H'', hp, ⟨hr, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu ilpParams _ rfl hlk)
      (ilpf_spec ra C hok hc.ilp coreWalkFuel CV.coreWalkFuel_lt op2 v.levelParams _ us2 _ H8 _
        r hlpP7 hus2 (sr_stateOK hu) hu.cok.rn hu.cok.rl hu.cok.rls hrd7' (blkAt_mono hPb2 (hp56.trans (hp67.trans hp78))))))
    (fun rhs2 wr s8 H9 hp9 ⟨hr9, hwr⟩ => ?_)
  subst hwr
  obtain ⟨hs89, hrhs2⟩ := ConRon.Bridge.instLPFast_run hst7 hrd7 hlpP7 hus2 hrv hr9
  have hp89 : H8 <+: H9 := hp9
  have hp09 : C.H <+: H9 := hp08.trans hp89
  have hok9 := ctxOK_H hok H9
  have hext48 : Ext s4.store s8.store := hext47.trans hs89.ext
  -- the firing level, in an environment cell
  show SpecR (Inv (ctxH C H9) _ _ _ _) (envAllocP (ctxH C H9) kqB (.const 8) _) _ _ _
  refine specR_envAllocI kqB (.const 8) 1 (by decide) (hD _ (by simp [kqLocals])) (fun v => rfl)
    (fun ws1 hws1 hroom1 => ?_)
  have hj1 : C.EH.length < (C.EH ++ ws1).length := by simp; omega
  refine specR_envStoreI (C := ctxE (ctxH C H9) (C.EH ++ ws1)) (ctxOK_E hok9 (List.prefix_append _ _)) (vv kqB)
    (vv qU) C.EH.length hj1 (Enc.idxW u) (by simp only [sev, sev_vv, Env.get_cons, ite_true]; rfl)
    (by simp +decide only [sev, sev_vv, Env.get_cons, ite_false]; exact hXu) ?_
  show SpecR (Inv (ctxE (ctxH C H9) ((C.EH ++ ws1).set C.EH.length (Enc.idxW u))) _ _ _ _)
    (alloc1 (ctxE (ctxH C H9) ((C.EH ++ ws1).set C.EH.length (Enc.idxW u))) kqA (.const 0) _) _ _ _
  have hpE1 : C.EH <+: (C.EH ++ ws1).set C.EH.length (Enc.idxW u) :=
    prefix_set_ge (List.prefix_append _ _) _ (le_refl _) _
  have hE1u : ((C.EH ++ ws1).set C.EH.length (Enc.idxW u))[C.EH.length]? = some (Enc.idxW u) :=
    List.getElem?_set_self hj1
  generalize hE1 : (C.EH ++ ws1).set C.EH.length (Enc.idxW u) = E1 at hpE1 hE1u ⊢
  -- an empty accumulator block
  refine specR_alloc1I (C := ctxE (ctxH C H9) E1) (ctxOK_E hok9 hpE1) kqA (.const 0) 0 (hD _ (by simp [kqLocals]))
    (fun v => rfl) (fun H10 ws hp10 hws => ?_)
  have hg10 := img1_get H10 ws (0 : BitVec 64) hws
  have hp10' : H9 <+: (H10 ++ ws).set H10.length 0 := hp10.trans (img1_prefix H10 ws 0 hws)
  generalize hHa : (H10 ++ ws).set H10.length 0 = Ha at hg10 hp10' ⊢
  have hp0a : C.H <+: Ha := hp09.trans hp10'
  have hokA : CtxOK (ctxE C E1) := ctxOK_E hok hpE1
  -- the firing levels at the record's names
  refine specR_appendNil ?_
  have hlpP8 : Frontend.denoteNList s8.store.ns v.levelParams = _ :=
    denoteNList_ext hs89.ext.lss.ls.ns _ _ hlpP7
  have hus8 := denoteLs_ext hus2 hs89.ext
  unfold denoteLs at hus8
  split at hus8
  · cases hus8
  rename_i uh hview
  have hud8 : (denoteL s8.store.ls u).isSome = true := by
    obtain ⟨lu, hlu⟩ := Option.isSome_iff_exists.mp hudn
    rw [denoteL_ext hlu hext48]; rfl
  refine specR_fact (fun t ht => ht.sr.cok.rl) (fun hrl8 => ?_)
  refine specR_callNIH (C := ctxH (ctxE C E1) Ha) kqA ConPanqueque.T.WC.fRg ConPanqueque.T.WC.rgParams
    [.const 0, vv kqB, .const 1, vv qL, vv kqUs, vv kqA] (ConPanqueque.T.WC.rgBody C)
    [boolW false, ecell C C.EH.length, BitVec.ofNat 64 1, cellA C op2, Enc.idxW us2, cellA C H10.length]
    (by decide) rfl (hD _ (by simp [kqLocals])) hc.rg.self
    ⟨rfl, by simp only [sev, sev_vv, Env.get_cons]; simp +decide; rfl, rfl,
      by simp +decide only [sev, sev_vv, Env.get_cons, ite_false]; exact hPL2,
      by simp +decide only [sev, sev_vv, Env.get_cons, ite_false, ite_true],
      by simp only [sev, sev_vv, Env.get_cons, ite_true]; rfl, trivial⟩
    (fun a w s' st => (substLevelsAt _ (List.map ConLeche.Level.param ks) [u] >>= fun hs => pure ([] ++ hs)) s8 =
      .ok (a, s') ∧ ConPanqueque.T.WC.PostAL (ctxH (ctxE C E1) Ha) 0 a w s' st)
    (fun a w s' H' => (substLevelsAt _ (List.map ConLeche.Level.param ks) [u] >>= fun hs => pure ([] ++ hs)) s8 =
      .ok (a, s') ∧ ∃ o, w = cellA C o ∧ BlkAt H' o (a.map Enc.idxW))
    (fun a w s' st ⟨hr, H', o, hp, _, hw, hbk, hsr⟩ => ⟨H', hp, ⟨hr, o, hw, hbk⟩, hsr⟩)
    (fun u' hu _ hlk => specR_run (Knot.specR_of_pre u' (pre_of_lookups hu ConPanqueque.T.WC.rgParams _ rfl hlk)
      (ConPanqueque.T.WC.rgL_spec ra (ctxE C E1) hokA (by ctx_tr hc.rg) op2 v.levelParams _ us2 uh _ 0 [u]
        C.EH.length Ha [] H10.length s8 hp0a (fun j hj => by
          simp at hj; subst hj; exact hE1u)
        ⟨by simpa using hg10, fun i hi => by simp at hi⟩ (blkAt_mono hPb2 (hp56.trans (hp67.trans (hp78.trans
          (hp89.trans hp10'))))) hlpP8 hview hus8 hs89.ok.wf hrl8 (fun j hj => by simp at hj; subst hj; exact hud8)
        (by simp) (Nat.zero_le _) (Nat.zero_le _))))
    (fun lvs wa s9 H11 hp11 ⟨hr11, oa, hwa, hba⟩ => ?_)
  subst hwa
  -- the substituted level
  have hp1a : Ha <+: H11 := hp11
  have hp0b : C.H <+: H11 := hp0a.trans hp1a
  obtain ⟨hsl, s9', g1, g2⟩ := AM.bind_ok hr11
  obtain ⟨e1, e2⟩ := AM.pure_ok g2
  simp only [List.nil_append] at e1
  subst e1 e2
  obtain ⟨lu, hlu⟩ := Option.isSome_iff_exists.mp hud8
  obtain ⟨hs9, hden9⟩ := ConRon.Bridge.substLevelsAt_run _ _ [u] (L := [lu]) hs89.ok hs89.read
    (by simp [denoteLList, hlu, opt2]) g1
  obtain ⟨h', rfl⟩ : ∃ h', lvs = [h'] := by
    simp only [substLevelsAt] at g1
    obtain ⟨_, _, -, g3⟩ := AM.bind_ok g1
    obtain ⟨h0, _, -, g4⟩ := AM.bind_ok g3
    obtain ⟨rest, _, g5, g6⟩ := AM.bind_ok g4
    obtain ⟨rfl, -⟩ := AM.pure_ok g5
    obtain ⟨rfl, -⟩ := AM.pure_ok g6
    exact ⟨h0, rfl⟩
  have hh'd : (denoteL s9.store.ls h').isSome = true := by
    simp only [denoteLList] at hden9
    cases e : denoteL s9.store.ls h' with
    | none => rw [e] at hden9; simp [opt2] at hden9
    | some _ => rfl
  have hba1 : H11[oa + 1]? = some (Enc.idxW h') := by simpa using hba.2 0 (by simp)
  refine UD.specR_heapLoadI' (C := ctxH (ctxH (ctxE C E1) Ha) H11) kqE _ (oa + 1) _ hba1
    (hD _ (by simp [kqLocals])) (by simp only [sev, sev_vv, Env.get_cons, ite_true]; simp; exact cellA_add8 C oa) ?_
  have hokc : CtxOK (ctxH (ctxE C E1) H11) := ctxOK_H hokA H11
  -- the firing levels' block `[1, h']`
  show SpecR (Inv (ctxH (ctxE C E1) H11) _ _ _ _) (envAllocP (ctxH (ctxE C E1) H11) kqC (.const 16) _) _ _ _
  refine specR_envAllocI kqC (.const 16) 2 (by decide) (hD _ (by simp [kqLocals])) (fun v => rfl)
    (fun wsC hwsC hroomC => ?_)
  refine specR_envStoresI (C := ctxH (ctxE C E1) H11) hokc kqC E1.length (by simp [Env.get_cons]; rfl) (le_refl _)
    [.const 1, vv kqE] [1, Enc.idxW h'] 0 (E1 ++ wsC) [] (List.prefix_append _ _) (by simp [hwsC])
    ⟨rfl, by simp +decide only [sev, sev_vv, Env.get_cons, ite_false, ite_true], trivial⟩
    (fun E2 hpE2 hlE2 hloE2 hjE2 => ?_)
  have hE2l : E2.length = E1.length + 2 := by rw [hlE2]; simp [hwsC]
  have hokc2 : CtxOK (ctxH (ctxE C E2) H11) := ctxOK_H (ctxOK_E hok (hpE1.trans hpE2)) H11
  -- the rule's block `[ctor, 1, 2, levels, 0, rhs]`
  show SpecR (Inv (ctxH (ctxE C E2) H11) _ _ _ _) (envAllocP (ctxH (ctxE C E2) H11) kqD (.const 48) _) _ _ _
  refine specR_envAllocI kqD (.const 48) 6 (by decide) (hD _ (by simp [kqLocals])) (fun v => rfl)
    (fun wsD hwsD hroomD => ?_)
  refine specR_envStoresI (C := ctxH (ctxE C E2) H11) hokc2 kqD E2.length (by simp [Env.get_cons]; rfl) (le_refl _)
    [vv qX, .const 1, .const 2, vv kqC, .const 0, vv kqH]
    [Enc.idxW c, 1, 2, ecell C E1.length, 0, Enc.idxW rhs2] 0 (E2 ++ wsD) [] (List.prefix_append _ _) (by simp [hwsD])
    ⟨by simp +decide only [sev, sev_vv, Env.get_cons, ite_false]; exact hXc, rfl, rfl,
      by simp +decide only [sev, sev_vv, Env.get_cons, ite_false, ite_true]; rfl, rfl,
      by simp +decide only [sev, sev_vv, Env.get_cons, ite_false, ite_true], trivial⟩
    (fun E3 hpE3 hlE3 hloE3 hjE3 => ?_)
  have hE3l : E3.length = E2.length + 6 := by rw [hlE3]; simp [hwsD]
  have hokc3 : CtxOK (ctxH (ctxE C E3) H11) := ctxOK_H (ctxOK_E hok ((hpE1.trans hpE2).trans hpE3)) H11
  -- the rules' block `[1, rule]`
  show SpecR (Inv (ctxH (ctxE C E3) H11) _ _ _ _) (envAllocP (ctxH (ctxE C E3) H11) kqG (.const 16) _) _ _ _
  refine specR_envAllocI kqG (.const 16) 2 (by decide) (hD _ (by simp [kqLocals])) (fun v => rfl)
    (fun wsG hwsG hroomG => ?_)
  refine specR_envStoresI (C := ctxH (ctxE C E3) H11) hokc3 kqG E3.length (by simp [Env.get_cons]; rfl) (le_refl _)
    [.const 1, vv kqD] [1, ecell C E2.length] 0 (E3 ++ wsG) [] (List.prefix_append _ _) (by simp [hwsG])
    ⟨rfl, by simp +decide only [sev, sev_vv, Env.get_cons, ite_false, ite_true]; rfl, trivial⟩
    (fun E4 hpE4 hlE4 hloE4 hjE4 => ?_)
  have hE4l : E4.length = E3.length + 2 := by rw [hlE4]; simp [hwsG]
  have hpE14 : C.EH <+: E4 := ((hpE1.trans hpE2).trans hpE3).trans hpE4
  have hokc4 : CtxOK (ctxH (ctxE C E4) H11) := ctxOK_H (ctxOK_E hok hpE14) H11
  -- the record's constant value `[name, lps, type]`
  show SpecR (Inv (ctxH (ctxE C E4) H11) _ _ _ _) (alloc3 (ctxH (ctxE C E4) H11) kqR (vv qN) (vv kqRL) (vv kqTy) _)
    _ _ _
  refine specR_alloc3I (C := ctxH (ctxE C E4) H11) hokc4 kqR (vv qN) (vv kqRL) (vv kqTy) (Enc.idxW v.name)
    (cellA C ol) (Enc.idxW ty2) (hD _ (by simp [kqLocals]))
    (fun _ => by simp +decide only [sev, sev_vv, Env.get_cons, ite_false]; exact hPN2)
    (fun _ => by simp +decide only [sev, sev_vv, Env.get_cons, ite_false]; exact hRL7)
    (fun _ => by simp +decide only [sev, sev_vv, Env.get_cons, ite_false, ite_true])
    (fun H12 ws12 hp12 hws12 => ?_)
  obtain ⟨g0, g1, g2⟩ := img3_get H12 ws12 (Enc.idxW v.name) (cellA C ol) (Enc.idxW ty2) hws12
  have hp12' : H11 <+: _ := hp12.trans (img3_prefix H12 ws12 (Enc.idxW v.name) (cellA C ol) (Enc.idxW ty2) hws12)
  generalize hHr : (((H12 ++ ws12).set H12.length (Enc.idxW v.name)).set (H12.length + 1) (cellA C ol)).set
    (H12.length + 2) (Enc.idxW ty2) = Hr at g0 g1 g2 hp12' ⊢
  have hp0r : C.H <+: Hr := hp0b.trans hp12'
  have hokr : CtxOK (ctxH (ctxE C E4) Hr) := ctxOK_H (ctxOK_E hok hpE14) Hr
  -- the name fresh
  show SpecR (Inv (ctxH (ctxE C E4) Hr) _ _ _ _) (envFindP (ctxH (ctxE C E4) Hr) kqF (vv qN) _) _ _ _
  refine specR_envFindI hokr hc.d.k.g hc.d.k.p kqF (vv qN) v.name (hD _ (by simp [kqLocals]))
    (by simp +decide only [sev, sev_vv, Env.get_cons, ite_false]; exact hPN2)
    (by simp +decide only [Env.get_cons, ite_false]; exact hB7.2) ?_
  have hrel := find_rel hokr v.name
  revert hrel
  rcases hfn : (ctxH (ctxE C E4) Hr).fe.find? v.name with _ | ci0
  swap
  · intro ⟨o', hm, hci⟩
    rw [hm]
    refine specR_atEntry fun t ht => ?_
    have hoE : o' < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
    exact specR_guardNZ kqF (optWG id (some (ecell (ctxH (ctxE C E4) Hr) o'))) (by simp only [Env.get_cons, ite_true])
      (fun h => absurd h (show ecell (ctxH (ctxE C E4) Hr) o' + 1 ≠ 0 from ecell_succ_ne hokr hoE))
  intro hrel
  simp only at hrel
  rw [hrel]
  refine specR_guardNZ kqF (optWG id none) (by simp only [Env.get_cons, ite_true]) (fun _ => ?_)
  have hnew : C.fe.find? v.name = none := hfn
  simp only [installBasisDecl, IConstantInfo.name, hnew, Option.isNone_none, ↓reduceIte, pure_bind]
  refine specR_fact (fun t ht => ht.sr.floor) (fun hfl9 => ?_)
  have hext69 : Ext s6.store s9.store :=
    ((hs78.ext.trans (show Ext s7.store (withC (withC s7 c1) c2).store from Ext.refl _)).trans hs89.ext).trans hs9.ext
  have hden : NewDen (.recInfo ⟨v.name, cv.levelParams, ty2⟩ (recMI j) (recMI j) false
      [⟨c, 1, .levels [h'], rhs2⟩]) s9.store := by
    refine ⟨fun n hn' => ?_, ?_, by show cv.levelParams.length + 1 < 2 ^ 60; omega, fun _ _ _ e => (by cases e),
      fun _ _ e => (by cases e)⟩
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hn'
      exact Option.isSome_iff_exists.mpr ⟨_, denoteN_ext (hks j hj) hfl9⟩
    · show (denoteE s9.store ty2).isSome = true; rw [denote_ext hty2 hext69]; rfl
  have hblk : BlkAt Hr ol (cv.levelParams.map Enc.idxW) := blkAt_mono hb hp0r
  -- the three blocks, in the final image
  have l4 : ∀ p (x : BitVec 64), p < E3.length → E3[p]? = some x → E4[p]? = some x := fun p x hp hx => by
    rw [hloE4 p (by omega), List.getElem?_append_left (by omega)]; exact hx
  have l3 : ∀ p (x : BitVec 64), p < E2.length → E2[p]? = some x → E3[p]? = some x := fun p x hp hx => by
    rw [hloE3 p (by omega), List.getElem?_append_left (by omega)]; exact hx
  have l2 : ∀ p (x : BitVec 64), p < E1.length → E1[p]? = some x → E2[p]? = some x := fun p x hp hx => by
    rw [hloE2 p (by omega), List.getElem?_append_left (by omega)]; exact hx
  have c0 : E2[E1.length]? = some 1 := by simpa using hjE2 0 (by simp)
  have c1' : E2[E1.length + 1]? = some (Enc.idxW h') := by simpa using hjE2 1 (by simp)
  have d0 : E3[E2.length]? = some (Enc.idxW c) := by simpa using hjE3 0 (by simp)
  have d1 : E3[E2.length + 1]? = some 1 := by simpa using hjE3 1 (by simp)
  have d2 : E3[E2.length + 2]? = some 2 := by simpa using hjE3 2 (by simp)
  have d3 : E3[E2.length + 3]? = some (ecell C E1.length) := by simpa using hjE3 3 (by simp)
  have d5 : E3[E2.length + 5]? = some (Enc.idxW rhs2) := by simpa using hjE3 5 (by simp)
  have g0' : E4[E3.length]? = some 1 := by simpa using hjE4 0 (by simp)
  have g1' : E4[E3.length + 1]? = some (ecell C E2.length) := by simpa using hjE4 1 (by simp)
  show SpecR (Inv (ctxE (ctxH C Hr) E4) _ _ _ _) _ _ _ _
  refine instQcall_spec mode C hok hc hpl hg hF hL Hr E4 hp0r hpE14 s9 _
    (.recInfo ⟨v.name, cv.levelParams, ty2⟩ (recMI j) (recMI j) false [⟨c, 1, .levels [h'], rhs2⟩])
    H12.length ol g0 g1 g2 hblk (by show cv.levelParams.length < 2 ^ 60; omega)
    [.const 5, vv kqR, .const (BitVec.ofNat 64 (recMI j)), .const (BitVec.ofNat 64 (recMI j)), .const 0, vv kqG,
      .const 0, .const 0] 5 (BitVec.ofNat 64 (recMI j)) (BitVec.ofNat 64 (recMI j)) 0 (ecell C E3.length) 0 0
    ⟨rfl, by simp +decide only [sev, sev_vv, Env.get_cons, ite_false, ite_true]; rfl, rfl, rfl, rfl,
      by simp +decide only [sev, sev_vv, Env.get_cons, ite_false, ite_true]; rfl, rfl, rfl, trivial⟩
    (fun EH ox b hpE hlay => ?_) hnew hden ?_ T hT
  · obtain ⟨h1, h2, h3, hw, hbl⟩ := hlay
    have hmi : recMI j < 2 ^ 63 := by rcases hkj with ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
    refine ⟨⟨h1, ⟨ecell C b, h2, b, rfl, hbl⟩, h3⟩, hw 0 (by simp), ⟨hw 4 (by simp), hmi⟩, ⟨hw 5 (by simp), hmi⟩,
      hw 6 (by simp), ecell C E3.length, hw 7 (by simp), E3.length, rfl, ?_, fun i hi => ?_⟩
    · simpa using get_prefix g0' hpE
    · simp at hi; subst hi
      refine ⟨E2.length, by simpa [ecell] using get_prefix g1' hpE, get_prefix (l4 _ _ (by omega) d0) hpE,
        ⟨get_prefix (l4 _ _ (by omega) d1) hpE, by simp⟩,
        ⟨get_prefix (l4 _ _ (by omega) d2) hpE, ecell C E1.length, get_prefix (l4 _ _ (by omega) d3) hpE, E1.length, rfl,
          ⟨by simpa using get_prefix (l4 _ _ (by omega) (l3 _ _ (by omega) c0)) hpE, fun i hi => ?_⟩⟩,
        get_prefix (l4 _ _ (by omega) d5) hpE⟩
      simp at hi; subst hi
      simpa using get_prefix (l4 _ _ (by omega) (l3 _ _ (by omega) c1')) hpE
  · intro _ _ _ _ _ e rl hrl
    cases e
    simp at hrl; subst hrl
    refine ⟨fun lv hlv => ?_, fun _ _ e => by cases e⟩
    rcases hlv with ⟨_, e⟩ | e
    · cases e
    · cases e
      exact ⟨fun x hx => by simp at hx; subst hx; exact hh'd, by simp⟩

end

end ConPanqueque.T.Quot
