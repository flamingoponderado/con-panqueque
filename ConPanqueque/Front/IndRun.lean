import ConPanqueque.Front.IndLine
import ConPanqueque.T.Ind.ReadBlockRecs
import ConPanqueque.T.Ind.NestCtxRun

/-! # The inductive record's twin-run facts, from the front end

`IndRun C block nP` (`T/Ind/IndArm2.lean`) is what the fold's inductive arm (`ki_spec`) takes of the
twin: facts of the block `readBlock` answers when it runs at a checking state (con-ron's `FoldOK`) at
which the block denotes.  `indRun_of_front` derives it from what the front end establishes of the
block (`IndFront`: the inductive line's `IndBounds` at a store below the fold's floor, where the block
denotes) and the facts not yet derived (`IndRunGap`).

The derivation reads `readBlock` through con-ron's relational spec (`readBlock_run`: the answer
denotes con-leche's `readBlock` of the denoted block) and con-leche's inversion (`readBlock_inv`):
every member, constructor and recursor of the answer denotes a record of the block, so the front
end's bounds on the block's records bound the answer's fields. -/

open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.Front

open ConPanqueque.T ConPanqueque.T.Ind

set_option autoImplicit false

/-! ## Helpers -/

theorem mapM_some_mem {α β : Type} {f : α → Option β} :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → ∀ x ∈ xs, ∃ y ∈ ys, f x = some y
  | [], ys, _, x, hx => absurd hx List.not_mem_nil
  | a :: as, ys, h, x, hx => by
    obtain ⟨y, ys', rfl, ha, has⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv h
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨y, List.mem_cons_self, ha⟩
    · obtain ⟨y', hy', hf⟩ := mapM_some_mem has x hx
      exact ⟨y', List.mem_cons_of_mem _ hy', hf⟩

theorem mapM_sum_eq {α β : Type} {f : α → Option β} (g : α → Nat) (g' : β → Nat)
    (hg : ∀ x y, f x = some y → g x = g' y) :
    ∀ {xs : List α} {ys : List β}, xs.mapM f = some ys → (xs.map g).sum = (ys.map g').sum
  | [], ys, h => by simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h; subst h; rfl
  | a :: as, ys, h => by
    obtain ⟨y, ys', rfl, ha, has⟩ := ConRon.Bridge.Inductives.mapM_option_cons_inv h
    simp only [List.map_cons, List.sum_cons, hg a y ha, mapM_sum_eq g g' hg has]

theorem denoteCV_parts {st : EStore} {v : IConstantVal} {c : ConLeche.ConstantVal}
    (h : Frontend.denoteCV st v = some c) :
    Frontend.denoteNList st.ns v.levelParams = some c.levelParams ∧ denoteE st v.type = some c.type := by
  simp only [Frontend.denoteCV] at h
  cases h1 : denoteN st.ns v.name <;> cases h2 : Frontend.denoteNList st.ns v.levelParams <;>
    cases h3 : denoteE st v.type <;> simp only [h1, h2, h3, reduceCtorEq, Option.some.injEq] at h
  subst h; exact ⟨rfl, rfl⟩

theorem lps_len_of_denote {st : EStore} {v : IConstantVal} {c : ConLeche.ConstantVal}
    (h : Frontend.denoteCV st v = some c) : v.levelParams.length = c.levelParams.length :=
  denoteNList_length (denoteCV_parts h).1

theorem cvDen_of_denote {st : EStore} {v : IConstantVal} {c : ConLeche.ConstantVal}
    (h : Frontend.denoteCV st v = some c) (hl : c.levelParams.length < 2 ^ 55) : CVDen v st := by
  obtain ⟨h1, h2⟩ := denoteCV_parts h
  have hl' := denoteNList_length h1
  refine ⟨fun n hn => ?_, by rw [h2]; rfl, by omega⟩
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hn
  rw [denoteNList_get h1 j hj (by omega)]; rfl

theorem ks_of_denote {st : EStore} {v : IConstantVal} {c : ConLeche.ConstantVal}
    (h : Frontend.denoteCV st v = some c) :
    ∃ ks : List ConLeche.Name, ∃ hkl : ks.length = v.levelParams.length,
      ∀ j (hj : j < v.levelParams.length), denoteN st.ns v.levelParams[j] = some (ks[j]'(by omega)) := by
  obtain ⟨h1, -⟩ := denoteCV_parts h
  have hl := denoteNList_length h1
  exact ⟨c.levelParams, hl.symm, fun j hj => denoteNList_get h1 j hj (by omega)⟩

/-! ## What the front end supplies, and what is left -/

/-- **What the front end establishes of an inductive record's block**: the inductive line's bounds
(`IndBounds`) at a state whose store is below the fold's floor, where the block denotes. -/
def IndFront (C : Ctx) (block : List IConstantInfo) (nP : Nat) : Prop :=
  ∃ s0 : AState, Ext s0.store C.St ∧ IndBounds s0 block nP ∧ (Frontend.denoteCIList s0.store block).isSome

/-- `CBKRun` less its walk's-context clause (`bn`, derived by `blockNestCtx_facts`) and its tables clause
(`tables`, derived by con-ron's `blockTables_run`). -/
structure CBKRunRest (mode : ConLeche.CheckMode) (C : Ctx) (p₀ : BlockShape) (ms0 : MemberShape) (rc : RecShape) :
    Prop where
  pass : ∀ (env : ConLeche.Env) (s0 : AState) (ms : List MemberShape) (isRec : Bool) (s : AState) (q : BlockPass)
    (s' : AState), CheckOK false env C.fe s0 → ConLeche.EnvWF env →
    ConRon.Bridge.Inductives.EnvRel env C.fe s0.store → Ext C.St s0.store →
    cbkPre mode C.fe p₀ s0 = .ok ((ms, isRec), s) →
    checkBlockPass mode C.fe { p₀ with members := ms } isRec s = .ok (q, s') → PassFacts q ms0
  crt : ∀ (env : ConLeche.Env) (s0 : AState) (ms : List MemberShape) (isRec : Bool) (s : AState) (q : BlockPass)
    (s' : AState), CheckOK false env C.fe s0 → ConLeche.EnvWF env →
    ConRon.Bridge.Inductives.EnvRel env C.fe s0.store → Ext C.St s0.store →
    cbkPre mode C.fe p₀ s0 = .ok ((ms, isRec), s) →
    checkBlockPass mode C.fe { p₀ with members := ms } isRec s = .ok (q, s') →
    (∀ m ∈ q.cls, ∀ (xs : List ClassCtor) (el : LIdx) (pre : List EIdx) s s' cv,
      classRecTyOk mode (consSumCtors p₀.nP ms0.cvT.name ms0.ctors q.env1)
        ⟨p₀.nP, q.params, [{ m with nfs := q.tbl }], [ms0.cvT.type], q.rd.slots, [xs], el, pre⟩
        p₀.k rc rc.cvR 0 s = .ok (cv, s') → (denoteE s'.store cv.type).isSome = true)

/-- **The facts `indRun_of_front` does not derive yet**, each in the shape `IndRun` asks for it: the
major index below `2⁵⁶` (the inductive line checks `2⁵⁷`), the firing modes' rules denoting, the
split's shape and `checkBlock`'s pass facts (`CBKRunRest`). -/
structure IndRunGap (C : Ctx) (block : List IConstantInfo) (nP : Nat) : Prop where
  mi : ∀ ci ∈ block, ∀ cv mi rp k rules, ci = .recInfo cv mi rp k rules → mi < 2 ^ 56
  fire : ∀ (env : ConLeche.Env) (fe : IFEnv) (b : List ConLeche.ConstantInfo) (s : AState) (p : BlockShape)
    (s' : AState), FoldOK env fe s → Ext C.St s.store → Frontend.denoteCIList s.store block = some b →
    readBlock nP block s = .ok (.ok p, s') →
    ∀ sa sb fs, StateOK sa → PinsOK sa → Ext s'.store sa.store → p.recs.mapM (recFire p) sa = .ok (fs, sb) →
      ∀ ci ∈ recsOf p.recs fs, ∀ cv mI rP isK rules, ci = .recInfo cv mI rP isK rules → ∀ rl ∈ rules,
        RuleDen rl sb.store
  cbk : ∀ (env : ConLeche.Env) (fe : IFEnv) (b : List ConLeche.ConstantInfo) (s : AState) (p : BlockShape)
    (s' : AState), FoldOK env fe s → Ext C.St s.store → Frontend.denoteCIList s.store block = some b →
    readBlock nP block s = .ok (.ok p, s') →
    ∀ C' : Ctx, C'.St = s'.store → C'.code = C.code → ∀ ms0 rc, p.members = [ms0] → p.recs = [rc] →
      SplitOK p block ∧ CBKRunRest .verified C' p ms0 rc

/-- **The inductive record's twin-run facts, from the front end's** (and `IndRunGap`): `readBlock`'s
answer denotes con-leche's (`readBlock_run`), whose records are the block's (`readBlock_records`), whose
counts and level-parameter lists the inductive line bounded (`IndBounds`). -/
theorem indRun_of_front {C : Ctx} {block : List IConstantInfo} {nP : Nat} (hF : IndFront C block nP)
    (hG : IndRunGap C block nP) : IndRun C block nP := by
  intro env fe b s p s' hfo hx hb hrun
  obtain ⟨s0, hx0, hB, hd0⟩ := hF
  obtain ⟨b0, hb0⟩ := Option.isSome_iff_exists.mp hd0
  have hb0' : Frontend.denoteCIList s.store block = some b0 := ConRon.Bridge.denoteCIList_mono (hx0.trans hx) _ _ hb0
  rw [hb0'] at hb
  obtain rfl := (Option.some.inj hb).symm
  obtain ⟨hps, hrel⟩ := ConRon.Bridge.Inductives.readBlock_run nP block b s s' (.ok p) hfo.check hb0' hrun
  obtain ⟨pP, hpP, hdsh⟩ := hrel
  have hpPr : ConLeche.readBlock nP b = .ok pP := ConRon.Bridge.Inductives.toOption_eq_some hpP
  obtain ⟨hnPP, hmemP, hrecP, hsumP⟩ := readBlock_records hpPr
  obtain ⟨hmsD, hrsD, hnPD, -, -, -, -⟩ := ConRon.Bridge.Inductives.dShape_inv hdsh
  have hlenb : block.length = b.length := denoteCIList_length hb0
  -- the block's records, bounded
  have H1 : ∀ c ∈ b, c.toConstantVal.levelParams.length < 2 ^ 55 ∧
      ConLeche.Frontend.indPiTeleLen c.toConstantVal.type < 2 ^ 55 := by
    intro c hc
    obtain ⟨ci, hci, hd⟩ := denoteCIList_mem hb0 c hc
    have hcv := denoteCI_toCV hd
    refine ⟨by rw [← lps_len_of_denote hcv]; exact hB.lps ci hci, hB.tele ci hci _ (denoteCV_parts hcv).2⟩
  have H2 : ∀ cv np nf T, ConLeche.ConstantInfo.ctorInfo cv np nf T ∈ b → np < 2 ^ 55 ∧ nf < 2 ^ 55 := by
    intro cv np nf T hc
    obtain ⟨ci, hci, hd⟩ := denoteCIList_mem hb0 _ hc
    obtain ⟨v, iT, rfl⟩ := denoteCI_ctor hd
    exact hB.ctor _ hci v np nf iT rfl
  have H3 : ∀ cv mi rp k rules, ConLeche.ConstantInfo.recInfo cv mi rp k rules ∈ b →
      mi < 2 ^ 56 ∧ rp < 2 ^ 57 ∧ rules.length < 2 ^ 55 := by
    intro cv mi rp k rules hc
    obtain ⟨ci, hci, hd⟩ := denoteCIList_mem hb0 _ hc
    obtain ⟨v, rs, rfl, hrl⟩ := denoteCI_rec hd
    obtain ⟨-, h2, h3, -⟩ := hB.rcs _ hci v mi rp k rs rfl
    exact ⟨hG.mi _ hci v mi rp k rs rfl, h2, by rw [← hrl]; exact h3⟩
  -- the answer's members and recursors, bounded
  have HM : ∀ ms ∈ p.members, ∃ mP ∈ pP.members, ConRon.Bridge.Inductives.dMember s'.store ms = some mP :=
    fun ms hms => mapM_some_mem hmsD ms hms
  have HR : ∀ rc ∈ p.recs, ∃ rcP ∈ pP.recs, ConRon.Bridge.Inductives.dRec s'.store rc = some rcP :=
    fun rc hrc => mapM_some_mem hrsD rc hrc
  have HMb : ∀ ms ∈ p.members, ms.nIdx < 2 ^ 56 ∧ CVDen ms.cvT s'.store ∧ CVDen ms.declared s'.store ∧
      ms.cvT.levelParams.length < 2 ^ 55 ∧ ms.declared.levelParams.length < 2 ^ 55 ∧
      ∀ c ∈ ms.ctors, CVDen c.1 s'.store ∧ c.1.levelParams.length < 2 ^ 55 ∧ c.2 < 2 ^ 55 := by
    intro ms hms
    obtain ⟨mP, hmP, hdm⟩ := HM ms hms
    obtain ⟨hcvT, hnI, hcs, hdecl⟩ := ConRon.Bridge.Inductives.dMember_inv hdm
    obtain ⟨⟨caps, hind⟩, hdeq, hnb, hcts⟩ := hmemP mP hmP
    have hlT : mP.cvT.levelParams.length < 2 ^ 55 := (H1 _ hind).1
    rw [hdeq] at hdecl
    refine ⟨?_, cvDen_of_denote hcvT hlT, cvDen_of_denote hdecl hlT, by rw [lps_len_of_denote hcvT]; exact hlT,
      by rw [lps_len_of_denote hdecl]; exact hlT, fun c hc => ?_⟩
    · rw [hnI]
      rcases hnb with ⟨caps', cv, hcv, hle⟩ | ⟨cv, mI, rP, isK, rules, hrc, hle⟩
      · have : ConLeche.Frontend.indPiTeleLen cv.type < 2 ^ 55 := (H1 _ hcv).2
        omega
      · have := (H3 _ _ _ _ _ hrc).1; omega
    · obtain ⟨cP, hcP, hdc⟩ := mapM_some_mem hcs c hc
      simp only [ConRon.Bridge.Inductives.dCtor, Option.map_eq_some_iff] at hdc
      obtain ⟨cv, hcv, rfl⟩ := hdc
      obtain ⟨np, T, hct⟩ := hcts _ hcP
      have hl : cv.levelParams.length < 2 ^ 55 := (H1 _ hct).1
      exact ⟨cvDen_of_denote hcv hl, by rw [lps_len_of_denote hcv]; exact hl, (H2 _ _ _ _ hct).2⟩
  have HRb : ∀ rc ∈ p.recs, CVDen rc.cvR s'.store ∧ rc.cvR.levelParams.length < 2 ^ 55 ∧ rc.mI < 2 ^ 56 ∧
      rc.rP < 2 ^ 57 ∧ rc.rules.length < 2 ^ 55 := by
    intro rc hrc
    obtain ⟨rcP, hrcP, hdr⟩ := HR rc hrc
    obtain ⟨hcvR, hrP, hmI, -, hrules, -⟩ := ConRon.Bridge.Inductives.dRec_inv hdr
    have hin := hrecP rcP hrcP
    have hl : rcP.cvR.levelParams.length < 2 ^ 55 := (H1 _ hin).1
    obtain ⟨h1, h2, h3⟩ := H3 _ _ _ _ _ hin
    exact ⟨cvDen_of_denote hcvR hl, by rw [lps_len_of_denote hcvR]; exact hl, by rw [hmI]; exact h1,
      by rw [hrP]; exact h2, by rw [denoteRules_length hrules]; exact h3⟩
  have hnPa : p.nP = nP := by rw [hnPD, hnPP]
  have hnP55 : nP < 2 ^ 55 := hB.np
  have hsum : (p.members.map (·.ctors.length)).sum < 2 ^ 58 := by
    have e := mapM_sum_eq (f := ConRon.Bridge.Inductives.dMember s'.store) (fun m => m.ctors.length)
      (fun m => m.ctors.length) (fun x y hxy => by
        obtain ⟨-, -, hcs, -⟩ := ConRon.Bridge.Inductives.dMember_inv hxy
        exact (ConLeche.option_mapM_length hcs).symm) hmsD
    have := hB.len
    rw [e]; omega
  refine ⟨⟨fun ms hms => by have := (HMb ms hms).1; omega, fun ms hms => by have := (HMb ms hms).1; omega,
    fun ms hms => by have := (HMb ms hms).2.2.2.2.1; omega,
    fun ms hms c hc => by have := ((HMb ms hms).2.2.2.2.2 c hc).2.1; omega,
    fun rc hrc => by have := (HRb rc hrc).2.1; omega, hsum,
    ⟨fun ms hms => ⟨(HMb ms hms).2.2.1, (HMb ms hms).2.1, fun c hc => ((HMb ms hms).2.2.2.2.2 c hc).1⟩,
      fun rc hrc => (HRb rc hrc).1⟩,
    hG.fire env fe b s p s' hfo hx hb0' hrun⟩, fun C' hSt hcode ms0 rc hm hr => ?_⟩
  obtain ⟨hsp, hcbk⟩ := hG.cbk env fe b s p s' hfo hx hb0' hrun C' hSt hcode ms0 rc hm hr
  have hms0 : ms0 ∈ p.members := by rw [hm]; exact List.mem_singleton_self _
  have hrc0 : rc ∈ p.recs := by rw [hr]; exact List.mem_singleton_self _
  obtain ⟨hni, hcvT, hdd, hlT, -, hcts⟩ := HMb ms0 hms0
  obtain ⟨hrd, hlR, hmI, hrP, hrl⟩ := HRb rc hrc0
  obtain ⟨mP, -, hdm⟩ := HM ms0 hms0
  obtain ⟨hcvT', -, -, -⟩ := ConRon.Bridge.Inductives.dMember_inv hdm
  obtain ⟨rcP, -, hdr⟩ := HR rc hrc0
  obtain ⟨hcvR', -, -, -, -, -⟩ := ConRon.Bridge.Inductives.dRec_inv hdr
  have hcl : ms0.ctors.length < 2 ^ 58 := by
    have := hsum; rw [hm] at this; simp at this; omega
  have hbn : ∀ (s0 : LIdx) (ip : Bool) (s₁ s₂ : AState) (ctx : NestCtx) (holes : List EIdx), StateOK s₁ →
      Ext C'.St s₁.store → (denoteL s₁.store.ls s0).isSome = true →
      blockNestCtx { p with resSort := s0, isProp := ip } s₁ = .ok ((ctx, holes), s₂) →
      (∃ vs, denoteLs s₂.store.lss ctx.lvls = some vs) ∧ ctx.params.length < 2 ^ 56 ∧ holes.length < 2 ^ 56 := by
    intro s0 ip s₁ s₂ ctx holes hst hxs hs0 hbnr
    obtain ⟨l, hl⟩ := Option.isSome_iff_exists.mp hs0
    rw [hSt] at hxs
    have hp' := dShape_at (ConRon.Bridge.Inductives.dShape_ext hxs _ _ hdsh) s0 ip l hl
    obtain ⟨h1, h2, h3⟩ := blockNestCtx_facts hst hp' hbnr
    refine ⟨h1, ?_, ?_⟩
    · rw [h2]; show p.nP < _; omega
    · rw [h3]; show p.members.length < _; rw [hm]; simp
  have htb : ∀ (s₁ : AState) (Q : List IProjTable) (s₂ : AState), StateOK s₁ → Ext C'.St s₁.store →
      blockTables p p.members s₁ = .ok (some Q, s₂) → ∀ t ∈ Q, ConPanqueque.T.Decl.NewTblDen t s₂.store ∧
        (∃ ks : List ConLeche.Name, ∃ hkl : ks.length = t.levelParams.length,
          ∀ j (hj : j < t.levelParams.length), denoteN s₂.store.ns t.levelParams[j] = some (ks[j]'(by rw [hkl]; exact hj))) ∧
        t.levelParams.length < 2 ^ 59 ∧ t.numParams < 2 ^ 62 ∧ t.numFields < 2 ^ 63 ∧ t.bodies.size < 2 ^ 58 := by
    intro s₁ Q s₂ hst hxs hbt t ht
    rw [hSt] at hxs
    have hd1 := ConRon.Bridge.Inductives.dShape_ext hxs _ _ hdsh
    obtain ⟨-, -, hR⟩ := ConRon.Bridge.Inductives.blockTables_run p.members pP.members hst hd1
      (ConRon.Bridge.Inductives.dShape_inv hd1).1 hbt
    obtain ⟨q, hq, hRT⟩ := hR
    obtain ⟨hQ, hok⟩ := hRT
    obtain ⟨pt, hpt, hdt⟩ := denoteProjTableList_mem hQ t ht
    obtain ⟨hl, hnp, hnf, hbd⟩ := denoteProjTable_parts hdt
    obtain ⟨hlps, hnP', m, hm, c, hc, hnfc⟩ := blockTables_mem pP.members q hq pt hpt
    have hlpsP : pP.lps.length < 2 ^ 55 := by
      unfold ConLeche.BlockShape.lps
      cases hmm : pP.members with
      | nil => simp
      | cons m0 rest =>
        obtain ⟨⟨caps, hind⟩, -⟩ := hmemP m0 (by rw [hmm]; exact List.mem_cons_self)
        have : m0.cvT.levelParams.length < 2 ^ 55 := (H1 _ hind).1
        simpa using this
    have hc2 : c.2 < 2 ^ 55 := by
      obtain ⟨-, -, -, hcts⟩ := hmemP m hm
      obtain ⟨np, T, hct⟩ := hcts c hc
      exact (H2 _ _ _ _ hct).2
    have hlen := denoteNList_length hl
    have hbs : t.bodies.size = t.numFields := (hok t ht).bodies
    have hlt : t.levelParams.length < 2 ^ 55 := by rw [hlen, hlps]; exact hlpsP
    refine ⟨⟨fun n hn => ?_, fun x hx => ?_, by omega, hbs⟩, ⟨pt.levelParams, hlen.symm,
      fun j hj => denoteNList_get hl j hj (by omega)⟩, by omega, by rw [hnp, hnP', hnPP]; omega,
      by rw [hnf, hnfc]; omega, by rw [hbs, hnf, hnfc]; omega⟩
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hn
      rw [denoteNList_get hl j hj (by omega)]; rfl
    · obtain ⟨ys, hys⟩ := Option.isSome_iff_exists.mp hbd
      exact denoteEList_get hys x hx
  refine ⟨hsp, by omega, by omega, by omega, hcl, fun c hc => ?_, hmI, by omega, by omega, by omega,
    by rw [hSt]; exact ks_of_denote hcvT', by rw [hSt]; exact ks_of_denote hcvR', by rw [hSt]; exact hdd,
    fun c hc => ?_, by rw [hSt]; exact hrd, ⟨hbn, hcbk.pass, hcbk.crt, htb⟩⟩
  · have := (hcts c hc).2.2; omega
  · obtain ⟨hcd, hcl', hc2⟩ := hcts c hc
    refine ⟨by rw [hSt]; exact hcd, by omega, by omega, ?_⟩
    obtain ⟨cP, -, hdc⟩ := mapM_some_mem (ConRon.Bridge.Inductives.dMember_inv hdm).2.2.1 c hc
    simp only [ConRon.Bridge.Inductives.dCtor, Option.map_eq_some_iff] at hdc
    obtain ⟨cv, hcv, -⟩ := hdc
    obtain ⟨ks, hkl, hks⟩ := ks_of_denote hcv
    refine ⟨ks, hkl, fun j hj => ?_⟩
    rw [hSt, hks j hj, List.getElem?_eq_getElem]

end ConPanqueque.Front
