import ConPanqueque.T.Ind.CheckBlockK
import ConRon.Bridge.Inductives.BlockTail

/-! # The generated recursor type denotes

`crt_discharge`: con-ron's relational specs along the twin's run of `checkBlock` from a checking state at a
well-formed environment, up to the generated recursor type's check (`classRecTyOk`): the members at their
telescopes, the flush, `is_rec` (`checkBlock_bridge`'s steps), the pass (`checkBlockPass_of`), the tables
(`blockTables_run`), the tail's index sorts, the constructors consed and the flush (`checkBlockTail_of`'s
steps), the generator's data (`genRecCheck_spec`'s steps), the prefix (`ClassGen.prefixBinders_spec`) and the
check itself (`classRecTyOk_spec`), whose answer denotes. -/

open ConRon.Arena ConRon.Bridge ConRon.Bridge.Inductives

namespace ConPanqueque.T.Ind

set_option autoImplicit false

theorem mapM_some_mem' {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ∀ x ∈ xs, ∃ y ∈ ys, f x = some y
  | [], ys, _, x, hx => absurd hx List.not_mem_nil
  | a :: as, ys, h, x, hx => by
    obtain ⟨y, ys', rfl, ha, has⟩ := mapM_option_cons_inv h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨y, List.mem_cons_self, ha⟩
    · obtain ⟨y', hy', hf⟩ := mapM_some_mem' has x hx
      exact ⟨y', List.mem_cons_of_mem _ hy', hf⟩

theorem classStreamRecs_out {mode : ConLeche.CheckMode} {fe : IFEnv} :
    ∀ (recs : List RecShape) (s s' : AState) (r : List IConstantVal),
      classStreamRecs mode fe recs s = .ok (r, s') → r = recs.map (·.cvR)
  | [], s, s', r, h => by
    simp only [classStreamRecs] at h
    obtain ⟨rfl, -⟩ := AM.pure_ok h; rfl
  | rc :: rest, s, s', r, h => by
    simp only [classStreamRecs] at h
    obtain ⟨_, s1, -, h⟩ := AM.bind_ok h
    obtain ⟨r', s2, h2, h⟩ := AM.bind_ok h
    obtain ⟨rfl, -⟩ := AM.pure_ok h
    rw [classStreamRecs_out rest s1 s2 r' h2]; rfl

set_option maxHeartbeats 4000000 in
theorem crt_discharge {env : ConLeche.Env} {fe : IFEnv} {p₀ : BlockShape} {p₀P : ConLeche.BlockShape}
    {block : List IConstantInfo} {b : List ConLeche.ConstantInfo} {rc : RecShape}
    {s0 s s5 s6 s3 s7 s1 s' : AState} {ms : List MemberShape} {isRec : Bool} {q : BlockPass}
    {Q : List IProjTable} {m : TargetMajor} {g0 : ClassGen} {cvRis : List IConstantVal} {pre : List EIdx}
    {cv : IConstantVal}
    (hd : ∀ ms ∈ p₀P.members, ms.declared = ms.cvT)
    (hck : CheckOK false env fe s0) (henv : ConLeche.EnvWF env) (hrel : ConRon.Bridge.Inductives.EnvRel env fe s0.store)
    (hp : dShape s0.store p₀ = some p₀P) (hb : Frontend.denoteCIList s0.store block = some b)
    (hpre : cbkPre .verified fe p₀ s0 = .ok ((ms, isRec), s))
    (hpass : checkBlockPass .verified fe { p₀ with members := ms } isRec s = .ok (q, s5))
    (htab : blockTables p₀ p₀.members s5 = .ok (some Q, s6)) (hm : m ∈ q.cls) (hrc : rc ∈ q.p.recs)
    (hctb : ctbPre .verified q.env1 q.p s6 = .ok ((), s3))
    (hga : gaPre .verified (consBlockCtors q.p.nP q.p.ctorGroups q.env1) q.p q.params q.tbl q.rd m block s3 =
      .ok ((g0, cvRis), s7))
    (hpb : g0.prefixBinders s7 = .ok (some pre, s1))
    (hcro : classRecTyOk .verified (consBlockCtors q.p.nP q.p.ctorGroups q.env1) { g0 with pre := pre } q.p.k rc rc.cvR 0
      s1 = .ok (cv, s')) :
    (denoteE s'.store cv.type).isSome = true := by
  have hk : CoreSpec checkFuel := CoreSpec.of_core
  -- the members at their telescopes, the flush, `is_rec`
  obtain ⟨hms₀, -⟩ := dShape_inv hp
  unfold cbkPre at hpre
  obtain ⟨ms', s₁, h1, h2⟩ := AM.bind_ok hpre
  obtain ⟨c1, msP, hmsP, hF1⟩ := reduceMembers_spec fe hk henv p₀.nP p₀.members p₀P.members s0 s₁ ms' hck hms₀ h1
  have hnP₀ := (dShape_inv hp).2.2.1
  rw [hnP₀] at hF1
  obtain ⟨F1, hF1'⟩ := id hF1
  rw [ConLeche.reduceMembers_datF] at hF1'
  obtain ⟨hAt, -⟩ := ConLeche.reduceMembers_inv hd hF1'
  obtain ⟨u, s₂, h3, h4⟩ := AM.bind_ok h2
  obtain ⟨c2, i2, hs2⟩ := ReadOK.flush c1.ok.toR h3
  have x12 : Ext s0.store s₂.store := by rw [hs2]; exact c1.ext
  obtain ⟨isRec', s₃, h5, h6⟩ := AM.bind_ok h4
  obtain ⟨p3, -⟩ := blockIsRec_spec p₀ p₀P s₂ s₃ isRec' c2.state (dShape_ext x12 _ _ hp) h5
  obtain ⟨e6, rfl⟩ := AM.pure_ok h6
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj e6
  have c3 := p3.toCore c2
  have x13 := x12.trans p3.ext
  -- the pass
  obtain ⟨env₁, qP, i4, c4, hrel4, henv₁, hq, hT, henv₂, hMs, -, -⟩ :=
    checkBlockPass_of (p₀P := { p₀P with members := msP }) hk henv c3.ok
      (hrel.mono x13) (BT.dShape_members (dShape_ext x13 _ _ hp)
        (dMember_ext.list (show Ext s₁.store s.store by rw [← hs2]; exact p3.ext) _ _ hmsP))
      (fun m hm => (hAt m hm).declaredWF) hpass
  have x4 := i4.ext
  -- the tables
  obtain ⟨p41, -, -⟩ := blockTables_run p₀.members p₀P.members i4.state
    (dShape_ext (x13.trans x4) _ _ hp) (dMember_ext.list (x13.trans x4) _ _ hms₀) htab
  have c41 := p41.toCore c4
  have x06 : Ext s0.store s6.store := (x13.trans x4).trans p41.ext
  have hq6 := dPass_ext p41.ext hq
  obtain ⟨he, hsh, -, hpa, hrd, hcl, htb⟩ := dPass_inv hq6
  obtain ⟨env₁', pP, kindsP, paramsP, rdP, clsP, tblP⟩ := qP
  simp only at he hsh hpa hrd hcl htb hT henv₂ hMs
  subst env₁'
  obtain ⟨hmsq, hrecs, hnP, -, -, hlarge, -⟩ := dShape_inv hsh
  have hzT : ∀ ms ∈ pP.members, ConLeche.Expr.WScoped 0 ms.cvT.type :=
    fun ms hms => hT ms.cvT (List.mem_map_of_mem hms)
  -- the tail's index sorts, the constructors consed, the flush
  unfold ctbPre at hctb
  obtain ⟨u1, s₄, g1, g2⟩ := AM.bind_ok hctb
  obtain ⟨c5, -, -, -⟩ := checkBlockIdxSorts_specF q.env1 hk henv₁ q.p pP q.p.members pP.members hzT s6 s₄ u1
    c41.ok ⟨hsh, hmsq⟩ g1
  have hcss : q.p.ctorGroups.mapM (dGroup s₄.store) = some pP.ctorGroups :=
    ctorGroups_denote (dShape_ext c5.ext _ _ hsh)
  obtain ⟨env₂, hrel₂, he₂⟩ := (consBlockCtors_spec c5.ok.state.wf q.p.nP q.p.ctorGroups
    pP.ctorGroups q.env1 env₁ hcss (hrel4.mono (p41.ext.trans c5.ext))).denote
  rw [hnP] at he₂
  rw [← he₂] at henv₂
  generalize hfe₂ : consBlockCtors q.p.nP q.p.ctorGroups q.env1 = fe₂ at hrel₂ hga hcro
  obtain ⟨c6, -, hs6⟩ := ReadOK.flush (⟨c5.ok.state, c5.ok.pins, hrel₂.ifenv⟩ : ReadOK _ fe₂ s₄) g2
  have x43 : Ext s₄.store s3.store := by rw [hs6]; exact Ext.refl _
  have x03 : Ext s0.store s3.store := by rw [hs6]; exact x06.trans c5.ext
  -- the generator's data
  have hcvT := dShape_formers (dShape_ext (c5.ext.trans x43) _ _ hsh)
  obtain ⟨mP, hmP, hdm⟩ := mapM_some_mem' hcl m hm
  unfold gaPre at hga
  obtain ⟨u0, t1, k1, z1⟩ := AM.bind_ok hga
  obtain ⟨pp1, -⟩ := targetRecPins_spec q.p pP block b s3 t1 u0 c6.state c6.pins
    ⟨dShape_ext (c5.ext.trans x43) _ _ hsh, denoteCIList_mono x03 _ _ hb⟩ k1
  have cc1 := pp1.toCore c6
  obtain ⟨cvRis', t2, k2, z2⟩ := AM.bind_ok z1
  have hcvRout := classStreamRecs_out q.p.recs t1 t2 cvRis' k2
  have hx3t1 : Ext s6.store t1.store := (c5.ext.trans x43).trans cc1.ext
  obtain ⟨cc2, cvRisP, ⟨hcvRis, hwRis⟩, -⟩ := classStreamRecs_spec fe₂ hk henv₂ q.p.recs pP.recs t1 t2 cvRis' cc1.ok
    (dRec_ext.list hx3t1 _ _ hrecs) k2
  obtain ⟨u3, t3, k3, z3⟩ := AM.bind_ok z2
  have cc3 : CoreStep env₂ fe₂ t2 t3 := by
    by_cases hL : q.p.large = true
    · rw [if_pos hL] at k3
      obtain ⟨la, t, k, z⟩ := AM.bind_ok k3
      obtain ⟨c, -⟩ := blockLargeElimAllowed_cspec fe₂ q.p pP false t2 t la cc2.ok
        (dShape_ext (hx3t1.trans cc2.ext) _ _ hsh) k
      split at z
      · obtain ⟨-, rfl⟩ := AM.pure_ok z; exact c
      · exact absurd z (fun h => AM.fail_ok h)
    · rw [if_neg hL] at k3
      obtain ⟨-, rfl⟩ := AM.pure_ok k3
      exact CoreStep.refl cc2.ok
  have x3t3 : Ext s3.store t3.store := (cc1.ext.trans cc2.ext).trans cc3.ext
  have hformer : ∀ t ∈ pP.formers.map (·.type), ConLeche.Expr.WScoped 0 t := by
    intro t ht
    obtain ⟨cv, hcv, rfl⟩ := List.mem_map.mp ht
    exact hT cv hcv
  have hmM : [m].mapM (dMajor t3.store) = some [mP] := by
    have h := dMajor_ext ((c5.ext.trans x43).trans x3t3) _ _ hdm
    simp [h]
  obtain ⟨ms2, t4, k4, z4⟩ := AM.bind_ok z3
  obtain ⟨cc4, Ms2P, ⟨hms2, hMs2⟩, -⟩ := classesNfs_spec fe₂ hk henv₂ q.p pP _ _ q.tbl tblP.toList hformer
    [m] [mP] (fun M hM => by rw [List.mem_singleton] at hM; rw [hM]; exact (hMs mP hmP).1) t3 t4 ms2 cc3.ok
    ⟨dShape_ext ((c5.ext.trans x43).trans x3t3) _ _ hsh,
      GR.types_denote (dExt_denoteCV.list x3t3 _ _ hcvT),
      dCtorNf_ext.list ((c5.ext.trans x43).trans x3t3) _ _ htb, hmM⟩ k4
  obtain ⟨ctors, t5, k5, z5⟩ := AM.bind_ok z4
  have x3t4 := x3t3.trans cc4.ext
  obtain ⟨cc5, ctorsP, hctors, -⟩ := classesCtors_spec fe₂ hk henv₂ q.p pP _ _ q.rd rdP ms2 Ms2P
    hformer hMs2 ms2 Ms2P 0 t4 t5 ctors cc4.ok
    ⟨dShape_ext ((c5.ext.trans x43).trans x3t4) _ _ hsh,
      GR.types_denote (dExt_denoteCV.list x3t4 _ _ hcvT),
      dClassRead_ext ((c5.ext.trans x43).trans x3t4) _ _ hrd, hms2, hms2⟩ k5
  obtain ⟨u6, t6, k6, z6⟩ := AM.bind_ok z5
  have ht6 : t6 = t5 := by
    split at k6
    · obtain ⟨-, rfl⟩ := AM.pure_ok k6; rfl
    · exact absurd k6 (fun h => AM.fail_ok h)
  subst ht6
  have x3t5 := x3t4.trans cc5.ext
  obtain ⟨fTC, t7, k7, z7⟩ := AM.bind_ok z6
  obtain ⟨c7, fTCP, hfTC, -⟩ := GR.mapM_cspecF dMajor dMajor_ext (fun st e => denoteE st e)
    dExt_denoteE (fun st => q.p.formers.mapM (Frontend.denoteCV st) = some pP.formers)
    (fun hx h => dExt_denoteCV.list hx _ _ h) (classFormerTy .verified fe₂ q.p.formers)
    (ConLeche.classFormerTy (ConLeche.fueledOpsM .verified) (ConLeche.mkFEnv env₂) pP.formers)
    (fun m mP s₀ s' r hok hpre hrun => classFormerTy_spec fe₂ hk henv₂ q.p.formers pP.formers
      m mP s₀ s' r hok ⟨hpre.1, hpre.2⟩ hrun) ms2 Ms2P t6 t7 fTC cc5.ok
    ⟨dExt_denoteCV.list x3t5 _ _ hcvT, dMajor_ext.list cc5.ext _ _ hms2⟩ k7
  obtain ⟨elim, t8, k8, z8⟩ := AM.bind_ok z7
  obtain ⟨p8, helim⟩ := structElimLevel_spec q.p.elim pP.elim q.p.large t7 t8 elim c7.ok.state
    ((dShape_inv (dShape_ext ((c5.ext.trans x43).trans (x3t5.trans c7.ext)) _ _
      hsh)).2.2.2.1) k8
  obtain ⟨eg, rfl⟩ := AM.pure_ok z8
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj eg
  have c8 := p8.toCore c7.ok
  rw [hlarge] at helim
  have x3t8 : Ext s3.store s7.store := x3t5.trans (c7.ext.trans p8.ext)
  have x68 : Ext s6.store s7.store := (c5.ext.trans x43).trans x3t8
  have hg0 : dClassGen s7.store (⟨q.p.nP, q.params, ms2, fTC, q.rd.slots, ctors, elim, []⟩ : ClassGen) =
      some ⟨pP.nP, paramsP, Ms2P, fTCP, rdP.slots, ctorsP, ConLeche.structElimLevel pP.elim pP.large, []⟩ := by
    have hsl : q.rd.slots.mapM (dSlot s6.store) = some rdP.slots := by
      simp only [dClassRead, Option.map_eq_some_iff] at hrd
      obtain ⟨q', hq', rfl⟩ := hrd
      exact hq'
    have e1 := denoteEList_ext x68 _ _ hpa
    have e2 := dMajor_ext.list (cc5.ext.trans (c7.ext.trans p8.ext)) _ _ hms2
    have e3 := denoteEList_ext p8.ext _ _ (mapM_denoteE hfTC)
    have e4 := dSlot_ext.list x68 _ _ hsl
    have e5 := dClassCtors_ext (c7.ext.trans p8.ext) _ _ hctors
    simp only [dClassGen, e1, e2, e3, e4, e5, helim, Frontend.denoteEList, hnP,
      Option.bind_eq_bind, Option.bind_some, Option.pure_def]
  obtain ⟨p9, ho⟩ := ClassGen.prefixBinders_spec _ _ s7 s1 (some pre) c8.ok.state c8.ok.pins hg0 hpb
  obtain ⟨preP, -, hpre'⟩ := ho
  have hg := dClassGen_pre (dClassGen_ext p9.ext _ _ hg0) hpre'
  have c9 := p9.toCore c8.ok
  have x69 : Ext s6.store s1.store := x68.trans p9.ext
  obtain ⟨rcP, -, hdr⟩ := mapM_some_mem' (dRec_ext.list x69 _ _ hrecs) rc hrc
  have hcvR := (dRec_inv hdr).1
  have xt2s1 : Ext t2.store s1.store :=
    cc3.ext.trans (cc4.ext.trans (cc5.ext.trans (c7.ext.trans (p8.ext.trans p9.ext))))
  have hRi : ConLeche.Expr.WScoped 0 rcP.cvR.type := by
    have hmem : rc.cvR ∈ cvRis := by rw [hcvRout]; exact List.mem_map_of_mem hrc
    obtain ⟨v, hv, hdv⟩ := mapM_some_mem' hcvRis rc.cvR hmem
    have e := denoteCV_ext hdv xt2s1
    rw [hcvR] at e
    obtain rfl := Option.some.inj e
    exact hwRis _ hv
  obtain ⟨-, v, ⟨hv, -, -⟩, -⟩ := classRecTyOk_spec fe₂ hk henv₂ _ _ q.p.k rc rcP rc.cvR rcP.cvR 0 hRi s1 s' cv
    c9.ok ⟨hg, hdr, hcvR⟩ hcro
  rw [denoteCV_type hv]; rfl

end ConPanqueque.T.Ind
