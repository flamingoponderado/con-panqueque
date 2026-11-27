import ConLeche.Verify.Cached.BlockPushes
import ConRon.Bridge.Inductives.BlockInstall
import ConRon.Bridge.Inductives.RecCheck
import ConRon.Bridge.Inductives.GenRec
import ConRon.Bridge.Inductives.StreamRecs
import ConRon.Bridge.Inductives.Install
import ConLeche.Verify.Inductives.PositivityInv
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.Inductives.BlockInv
import ConLeche.Verify.Denote.IndFrame
import ConRon.Bridge.Inductives.ClassRead
import ConRon.Bridge.Inductives.BlockShape
import ConRon.Bridge.Inductives.Positivity
import ConRon.Bridge.Inductives.PosWalks
import ConRon.Bridge.Inductives.StructInstall
import ConRon.Bridge.Inductives.StructParts
import ConLeche.Verify.Cached.GenRecC
import ConRon.Bridge.Checker.Base
import ConRon.Bridge.Checker.Names
import ConRon.Bridge.Core.Walks.Guards
import ConRon.Bridge.EnvDenote
import ConRon.Bridge.Inductives.BlockTail
import ConRon.Bridge.Inductives.Decl
import ConLeche.Semantics.Inductives.DeclBlockWF

/-! # The checks after the pass, with the index they leave

`checkBlockTail_ofW`: con-ron's `checkBlockTail_of`, its conclusion widened by what its proof already
holds: the index handed back is related to con-leche's environment of the formers and the constructors,
answers as the constructors' consed index, and has its literal flags right. -/

set_option backward.isDefEq.respectTransparency false
set_option backward.do.legacy true

namespace ConRon.Bridge.Inductives

set_option autoImplicit false

open ConLeche ConRon.Arena ConRon.Bridge
open BT

theorem checkBlockTail_ofW (hk : CoreSpec Arena.checkFuel)
    {env₁ : Env} {q : Arena.BlockPass} {qP : ConLeche.BlockPass Env}
    {block : List IConstantInfo} {blockP : List ConstantInfo} {s s' : AState} {fe' : IFEnv}
    {Q : List IProjTable} {QP : List ProjTable}
    (henv₁ : EnvWF env₁) (hck : CheckOK false env₁ q.env1 s)
    (hrel : EnvRel env₁ q.env1 s.store) (hq : dPass s.store env₁ q = some qP)
    (hb : Frontend.denoteCIList s.store block = some blockP)
    (hT : ∀ cv ∈ qP.p.formers, Expr.WScoped 0 cv.type)
    (henv₂ : EnvWF (ConLeche.consBlockCtors qP.p.nP qP.p.ctorGroups env₁))
    (hMs : ∀ M ∈ qP.cls, ConLeche.Cached.ClassMajScoped qP.p.nP M)
    (hpl : qP.params.length = qP.p.nP)
    (hQ : Frontend.denoteProjTableList s.store Q = some QP)
    (hrun : Arena.checkBlockTail .verified block q Q s = .ok (fe', s')) :
    InstStep s s' ∧ FOk (ConLeche.checkBlockTail (fueledOpsM .verified) blockP qP QP) () ∧
      EnvRel (ConLeche.consBlockCtors qP.p.nP qP.p.ctorGroups env₁) fe' s'.store ∧
      GR.FEq fe' (Arena.consBlockCtors q.p.nP q.p.ctorGroups q.env1) ∧ FlagsOK fe' := by
  obtain ⟨he, hsh, hkd, hpa, hrd, hcl, htb⟩ := dPass_inv hq
  obtain ⟨env₁', pP, kindsP, paramsP, rdP, clsP, tblP⟩ := qP
  simp only at he hsh hkd hpa hrd hcl htb hT henv₂ hMs hpl
  subst env₁' hkd
  obtain ⟨hms, hrecs, hnP, -, -, -, -⟩ := dShape_inv hsh
  have hzT : ∀ ms ∈ pP.members, Expr.WScoped 0 ms.cvT.type :=
    fun ms hms => hT ms.cvT (List.mem_map_of_mem hms)
  simp only [Arena.checkBlockTail] at hrun
  -- the index binders' sorts
  obtain ⟨u1, s₁, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨c1, _, -, hisF⟩ := checkBlockIdxSorts_specF q.env1 hk henv₁ q.p pP
    q.p.members pP.members hzT s s₁ u1 hck ⟨hsh, hms⟩ h1
  have x1 := c1.ext
  -- the constructors consed
  have hcss : q.p.ctorGroups.mapM (dGroup s₁.store) = some pP.ctorGroups :=
    ctorGroups_denote (dShape_ext x1 _ _ hsh)
  obtain ⟨env₂, hrel₂, he₂⟩ := (consBlockCtors_spec c1.ok.state.wf q.p.nP q.p.ctorGroups
    pP.ctorGroups q.env1 env₁ hcss (hrel.mono x1)).denote
  rw [hnP] at hrel₂ h2 he₂
  rw [← he₂] at henv₂
  generalize hfe₂ : Arena.consBlockCtors pP.nP q.p.ctorGroups q.env1 = fe₂ at h2 hrel₂
  -- the flush entering them
  obtain ⟨u, s₂, h3, h4⟩ := AM.bind_ok h2
  obtain ⟨c2, i2, hs2⟩ := ReadOK.flush
    (⟨c1.ok.state, c1.ok.pins, hrel₂.ifenv⟩ : ReadOK _ fe₂ s₁) h3
  have x2 : Ext s.store s₂.store := by rw [hs2]; exact x1
  -- the recursor stage
  obtain ⟨⟨fe₂b, out⟩, s₃, h5, h6⟩ := AM.bind_ok h4
  simp only [Arena.checkBlockRec] at h5
  obtain ⟨c3, outP, ⟨hout, hfresh, hfeq, hfeqF⟩, hGRF⟩ := genRecCheck_spec fe₂ hk henv₂ hrel₂.gate
    q.p pP _ q.params paramsP q.tbl tblP.toList q.rd rdP q.cls clsP block blockP hMs hT s₂ s₃
    (fe₂b, out) c2
    ⟨dShape_ext x2 _ _ hsh, denoteEList_ext x2 _ _ hpa, dCtorNf_ext.list x2 _ _ htb,
      dClassRead_ext x2 _ _ hrd, dMajor_ext.list x2 _ _ hcl, denoteCIList_mono x2 _ _ hb⟩ h5
  rw [blockNestedBit_eq (dShape_ext x2 _ _ hsh)] at hGRF
  have x3 := c3.ext
  have x03 : Ext s.store s₃.store := x2.trans x3
  dsimp only at h6
  -- the K flags
  obtain ⟨uK, sK, hK1, hK2⟩ := AM.bind_ok h6
  obtain ⟨hsK, hKF⟩ := streamKCheck_run q.p.recs pP.recs out outP s₃ sK uK
    (dShape_ext x03 _ _ hsh) (dRec_ext.list x03 _ _ hrecs) hout hK1
  subst sK
  -- the generated family's records
  obtain ⟨infos, s₄, h7, h8⟩ := AM.bind_ok hK2
  obtain ⟨p4, hinfos⟩ := blockRecInfosTF_run q.p pP out outP 0 s₃ s₄ infos c3.ok.state
    (dShape_ext x03 _ _ hsh) hout h7
  have x4 := p4.ext
  have x04 : Ext s.store s₄.store := x03.trans x4
  -- pushed in place
  have henvG : EnvWF (ConLeche.consBlockRecsT pP 0 outP env₂) := by
    obtain ⟨FR, hFR⟩ := hGRF
    rw [genRecCheck_datF] at hFR
    exact ConLeche.Cached.genRecCheck_recsWF (mode := .verified) henv₂ hFR hpl
      (fun M hM => (hMs M hM).2.1)
  have hrel₂b : EnvRel env₂ fe₂b s₄.store :=
    EnvRel.feq hfeq (hrel₂.mono (show Ext s₁.store s₄.store by rw [← hs2]; exact x3.trans x4))
      (hfeqF (hrel₂.ienv s₁ rfl).flags)
  have hienvG : IFEnvOK (ConLeche.consBlockRecsT pP 0 outP env₂)
      (Arena.consBlockRecsTemp infos fe₂b []).1 s₄ := by
    rw [consBlockRecsT_eq]
    exact consBlockRecsTemp_ok p4.ok infos _ fe₂b env₂ [] hinfos hrel₂b.ifenv hrel₂b.gate
      hrel₂b.stored
  obtain ⟨news, hn, hpop⟩ := consBlockRecsTemp_pop infos fe₂b []
  rw [List.nil_append] at hn
  -- the flush entering it
  obtain ⟨u5, s₅, h9, h10⟩ := AM.bind_ok h8
  obtain ⟨c5, i5, hs5⟩ := ReadOK.flush
    (⟨p4.ok, c3.ok.pins.mono x4 p4.pins, hienvG⟩ : ReadOK _ _ s₄) h9
  have x05 : Ext s.store s₅.store := by rw [hs5]; exact x04
  -- the stream's recursors against it
  obtain ⟨u6, s₆, h11, h12⟩ := AM.bind_ok h10
  obtain ⟨c6, _, -, hFS⟩ := streamRecsCheck_spec _ hk henvG q.p.recs pP.recs out outP s₅ s₆ u6 c5
    ⟨dRec_ext.list x05 _ _ hrecs, dRecOut_ext.list (by rw [hs5]; exact x4) _ _ hout⟩ h11
  have x06 : Ext s.store s₆.store := x05.trans c6.ext
  -- the pops, and the flush leaving them
  rw [hn] at h12
  generalize hfe₃ : (news.foldr (fun (x : NIdx × Option IConstantInfo) acc =>
    acc.popTemp x.1 x.2) (Arena.consBlockRecsTemp infos fe₂b []).1).setFlags fe₂b.natLit
      fe₂b.strLit = fe₃
  have hpop₃ : GR.FEq fe₃ fe₂b := by rw [← hfe₃]; exact hpop
  have hfe₃' : (List.foldr (fun x acc => match x with
      | (n, prev) => IFEnv.popTemp acc n prev)
        (Arena.consBlockRecsTemp infos fe₂b []).1 news).setFlags fe₂b.natLit fe₂b.strLit
      = fe₃ := hfe₃
  rw [hfe₃'] at h12
  have hfl₃ : FlagsOK fe₃ := by
    rw [← hfe₃]
    exact (hrel₂b.ienv s₄ rfl).flags.of_same (hpop.2.2.1 ▸ rfl)
      (fun n => by rw [IFEnv.setFlags_find?]; exact hpop.find? n) rfl rfl
  have hrel₃ : EnvRel env₂ fe₃ s₆.store :=
    EnvRel.feq hpop₃ (hrel₂b.mono (by rw [← hs5]; exact c6.ext)) hfl₃
  obtain ⟨u7, s₇, h13, h14⟩ := AM.bind_ok h12
  obtain ⟨c7, i7, hs7⟩ := ReadOK.flush
    (⟨c6.ok.state, c6.ok.pins, hrel₃.ifenv⟩ : ReadOK env₂ fe₃ s₆) h13
  have x07 : Ext s.store s₇.store := by rw [hs7]; exact x06
  -- the projection tables
  obtain ⟨u8, s₈, h15, h16⟩ := AM.bind_ok h14
  obtain ⟨p8, hFT⟩ := checkBlockTables_spec fe₃ env₂ Q QP s₇ s₈ u8
    c7.state c7.pins (hrel₃.ienv.mono (by rw [hs7]; exact Ext.refl _))
    (denoteProjTableList_ext x07 hQ) h15
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h16
  have hrel₈ : EnvRel env₂ fe' s'.store :=
    hrel₃.mono (show Ext s₆.store s'.store from by have := p8.ext; rw [hs7] at this; exact this)
  refine ⟨((c1.toInst.trans i2).trans (c3.toInst.trans (p4.toInst.trans (i5.trans
    (c6.toInst.trans (i7.trans p8.toInst)))))), ?_, by rw [← he₂]; exact hrel₈, ?_, hfl₃⟩
  · unfold ConLeche.checkBlockTail
    subst he₂
    exact FOk.bind hisF (FOk.bind hGRF (FOk.seq hKF (FOk.seq hFS hFT)))
  · rw [hnP, hfe₂]; exact hpop₃.trans hfeq


/-! ## The formers and constructors the pass and the tail leave -/

theorem passEnv_eq {F1 F2 : Nat} {env : Env} {p₀P : ConLeche.BlockShape} {msP : List ConLeche.MemberShape}
    {isRec : Bool} {qP : ConLeche.BlockPass Env}
    (hd : ∀ m ∈ p₀P.members, m.declared = m.cvT)
    (hR : ConLeche.reduceMembers (m := CheckM) (fueledOps .verified F1) env p₀P.nP p₀P.members = .ok msP)
    (hP : ConLeche.checkBlockPass (fueledOps .verified F2) env { p₀P with members := msP } isRec = .ok qP) :
    ConLeche.consBlockCtors qP.p.nP qP.p.ctorGroups qP.env₁ =
      ⟨(ConLeche.blockFormers p₀P isRec ++ ConLeche.blockCtors p₀P).reverse ++ env.consts, env.tables⟩ := by
  obtain ⟨-, hdecl, hname, hidx, hctors⟩ := ConLeche.reduceMembers_inv hd hR
  obtain ⟨_, _, _, _, _, _, hInd, -⟩ := ConLeche.checkBlockPass_inv hP
  obtain ⟨ms0, rest, cvTa0, s0, cvs, -, hq, hcons, -⟩ := ConLeche.checkBlockInds_shape hInd
  rw [hq, hcons, ConLeche.consBlockCtors_eq, ConLeche.consBlockInds_consts']
  have hnm : ({ p₀P with members := msP } : ConLeche.BlockShape).memberNames = p₀P.memberNames := hname
  have hcaps : ∀ i r, ConLeche.blockCapsAt (({ p₀P with members := msP } : ConLeche.BlockShape).withSort s0) i r
      = ConLeche.blockCapsAt p₀P i r := fun i r =>
    ConLeche.blockCapsAt_congr (p := ({ p₀P with members := msP } : ConLeche.BlockShape)) (q := p₀P)
      rfl hnm hctors hidx hdecl i r
  have hgr : (({ p₀P with members := msP } : ConLeche.BlockShape).withSort s0).ctorGroups = p₀P.ctorGroups := by
    show msP.map (fun x => (x.cvT.name, x.ctors)) = p₀P.members.map (fun x => (x.cvT.name, x.ctors))
    rw [← List.zip_map', hname, hctors, List.zip_map']
  have hnP : (({ p₀P with members := msP } : ConLeche.BlockShape).withSort s0).nP = p₀P.nP := rfl
  unfold ConLeche.blockFormers ConLeche.blockCtors
  rw [hgr, hnP]
  simp only [hq, hcaps, List.reverse_append, List.append_assoc]
  show _ = _
  congr 2
  rw [hdecl]

/-! ## The tables pushed -/

theorem pushTable_find? (fe : IFEnv) (t : IProjTable) (n : NIdx) : (fe.pushTable t).find? n = fe.find? n := rfl

theorem pushTable_rawTable? (fe : IFEnv) (t : IProjTable) (n : NIdx) :
    (fe.pushTable t).rawTable? n = if t.structName = n then some t else fe.rawTable? n := by
  unfold IFEnv.rawTable? IFEnv.pushTable
  simp only [Std.HashMap.getElem?_insert]
  by_cases h : t.structName = n
  · simp [h]
  · simp [h]

theorem env_findTable?_cons (env : Env) (pt : ProjTable) (nm : Name) :
    Env.findTable? ⟨env.consts, pt :: env.tables⟩ nm =
      if (env.find? nm).isSome then (if pt.structName = nm then some pt else env.findTable? nm) else none := by
  unfold Env.findTable?
  simp only [Env.find?]
  split
  · by_cases h : pt.structName = nm <;> simp [List.find?_cons, h]
  · rfl

/-- **One projection table pushed**, at a stored structure. -/
theorem IFEnvOK.pushTable {env : Env} {fe : IFEnv} {s : AState} (h : IFEnvOK env fe s) (hst : StateOK s)
    {t : IProjTable} {pt : ProjTable} (ht : Frontend.denoteProjTable s.store t = some pt) (hok : IProjTableOK t) :
    IFEnvOK ⟨env.consts, pt :: env.tables⟩ (fe.pushTable t) s := by
  have hT := denoteProjTable_structName ht
  have hfind : ∀ nm, Env.find? ⟨env.consts, pt :: env.tables⟩ nm = env.find? nm := fun _ => rfl
  refine ⟨fun n ci hf => h.hit n ci hf, fun nm c hf => h.cover nm c hf, fun n t' hf => ?_, fun nm pt' hf => ?_,
    h.flags.of_same rfl (fun n => rfl) rfl rfl, h.lits⟩
  · unfold IFEnv.findTable? at hf
    rw [pushTable_find?] at hf
    split at hf
    · rename_i hs
      rw [pushTable_rawTable?] at hf
      by_cases e : t.structName = n
      · subst e
        rw [if_pos rfl] at hf; cases hf
        obtain ⟨ci, hci⟩ := Option.isSome_iff_exists.mp hs
        obtain ⟨nm, c, hd, -, hc⟩ := h.hit _ ci hci
        rw [hT] at hd; cases hd
        refine ⟨pt.structName, pt, hT, ht, ?_, hok⟩
        rw [env_findTable?_cons, if_pos (by rw [hc]; rfl), if_pos rfl]
      · rw [if_neg e] at hf
        have hold : fe.findTable? n = some t' := by unfold IFEnv.findTable?; rw [if_pos hs]; exact hf
        obtain ⟨nm, pt'', hd, hpt, he, hok'⟩ := h.tblHit n t' hold
        refine ⟨nm, pt'', hd, hpt, ?_, hok'⟩
        have hne : pt.structName ≠ nm := fun e' => e (denoteN_injS hst.wf hT (e' ▸ hd))
        have hs' : (env.find? nm).isSome = true := by
          unfold Env.findTable? at he; split at he
          · assumption
          · cases he
        rw [env_findTable?_cons, if_pos hs', if_neg hne]; exact he
    · cases hf
  · rw [env_findTable?_cons] at hf
    split at hf
    · rename_i hs
      by_cases e : pt.structName = nm
      · subst e
        rw [if_pos rfl] at hf; cases hf
        obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hs
        obtain ⟨n, ci, hd, hf', -⟩ := h.cover _ c hc
        have := denoteN_injS hst.wf hd hT; subst this
        refine ⟨t.structName, t, hT, ?_, ht⟩
        unfold IFEnv.findTable?
        rw [pushTable_find?, hf']
        simp only [Option.isSome_some, ite_true]
        rw [pushTable_rawTable?, if_pos rfl]
      · rw [if_neg e] at hf
        obtain ⟨n, t'', hd, hf', hpt⟩ := h.tblCover nm pt' hf
        refine ⟨n, t'', hd, ?_, hpt⟩
        have hne : t.structName ≠ n := fun e' => e (by rw [← e'] at hd; rw [hT] at hd; exact Option.some.inj hd)
        unfold IFEnv.findTable? at hf' ⊢
        rw [pushTable_find?]
        split at hf'
        · rename_i hs'; rw [if_pos hs', pushTable_rawTable?, if_neg hne]; exact hf'
        · cases hf'
    · cases hf

/-- **The tables pushed**, oldest first. -/
theorem IFEnvOK.pushTables {s : AState} (hst : StateOK s) :
    ∀ (Q : List IProjTable) (QP : List ProjTable) {env : Env} {fe : IFEnv}, IFEnvOK env fe s →
      Frontend.denoteProjTableList s.store Q = some QP → (∀ t ∈ Q, IProjTableOK t) →
      IFEnvOK ⟨env.consts, QP.reverse ++ env.tables⟩ (IFEnv.pushTables Q fe) s
  | [], QP, env, fe, h, hd, _ => by
    simp [Frontend.denoteProjTableList] at hd; subst hd; cases env; exact h
  | t :: Q, QP, env, fe, h, hd, hok => by
    simp only [Frontend.denoteProjTableList] at hd
    split at hd
    · rename_i pt pts h1 h2
      simp only [Option.some.injEq] at hd; subst hd
      have h' := IFEnvOK.pushTables hst Q pts (IFEnvOK.pushTable h hst h1 (hok t (by simp))) h2
        (fun t' ht' => hok t' (by simp [ht']))
      simpa [IFEnv.pushTables, List.reverse_cons] using h'
    · cases hd

/-! ## The recursors pushed -/

theorem consBlockRecsTemp_fst : ∀ (L : List IConstantInfo) (fe : IFEnv) (prevs : List (NIdx × Option IConstantInfo)),
    (Arena.consBlockRecsTemp L fe prevs).1 = IFEnv.pushAll L fe
  | [], _, _ => rfl
  | ci :: L, fe, prevs => consBlockRecsTemp_fst L (fe.push ci) _

theorem IFEnvOK.pushAll {s : AState} (hst : StateOK s) (L : List IConstantInfo) (LP : List ConstantInfo)
    {env : Env} {fe : IFEnv} (h : IFEnvOK env fe s) (hg : TblGate fe) (hts : TablesStored env)
    (hL : Frontend.denoteCIList s.store L = some LP) :
    IFEnvOK ⟨LP.reverse ++ env.consts, env.tables⟩ (IFEnv.pushAll L fe) s := by
  have := consBlockRecsTemp_ok hst L LP fe env [] hL h hg hts
  rwa [consBlockRecsTemp_fst] at this

/-! ## Coherence, the table gate and the tables' shape across the pushes -/

theorem IFEnvCoh.pushTable {fe : IFEnv} (h : IFEnvCoh fe) (t : IProjTable) : IFEnvCoh (fe.pushTable t) :=
  ⟨fun n => h.1 n, fun n => by
    show (fe.tbls.insert t.structName t)[n]? = ((mkIFEnvTblsGo fe.env.tables).insert t.structName t)[n]?
    simp only [Std.HashMap.getElem?_insert, h.2 n]⟩

theorem IFEnvCoh.pushTables : ∀ (Q : List IProjTable) {fe : IFEnv}, IFEnvCoh fe → IFEnvCoh (IFEnv.pushTables Q fe)
  | [], _, h => h
  | t :: Q, _, h => IFEnvCoh.pushTables Q (IFEnvCoh.pushTable h t)

theorem IFEnvCoh.pushAll : ∀ (L : List IConstantInfo) {fe : IFEnv}, IFEnvCoh fe → IFEnvCoh (IFEnv.pushAll L fe)
  | [], _, h => h
  | ci :: L, _, h => IFEnvCoh.pushAll L (h.push ci)

theorem IFEnvCoh.feq {a b : IFEnv} (hf : GR.FEq a b) (h : IFEnvCoh b) : IFEnvCoh a :=
  ⟨fun n => by rw [hf.2.1 n, h.1 n, hf.1], fun n => by rw [hf.2.2.2, h.2 n, hf.1]⟩

theorem TblGate.pushAll : ∀ (L : List IConstantInfo) {fe : IFEnv}, TblGate fe → TblGate (IFEnv.pushAll L fe)
  | [], _, h => h
  | ci :: L, _, h => TblGate.pushAll L (h.push ci)

theorem TblGate.pushTable {fe : IFEnv} (h : TblGate fe) (t : IProjTable) (ht : (fe.find? t.structName).isSome = true) :
    TblGate (fe.pushTable t) := by
  intro n t' hn
  rw [pushTable_rawTable?] at hn
  rw [pushTable_find?]
  split at hn
  · rename_i e; subst e; exact ht
  · exact h n t' hn

theorem TblGate.pushTables {fe : IFEnv} : ∀ (Q : List IProjTable), TblGate fe →
    (∀ t ∈ Q, (fe.find? t.structName).isSome = true) → TblGate (IFEnv.pushTables Q fe)
  | [], h, _ => h
  | t :: Q, h, hs => TblGate.pushTables (fe := fe.pushTable t) Q (TblGate.pushTable h t (hs t (by simp)))
      (fun t' ht' => by rw [pushTable_find?]; exact hs t' (by simp [ht']))

theorem pushAll_find?_some : ∀ (L : List IConstantInfo) (fe : IFEnv) (n : NIdx), (fe.find? n).isSome = true →
    ((IFEnv.pushAll L fe).find? n).isSome = true
  | [], _, _, h => h
  | ci :: L, fe, n, h => pushAll_find?_some L (fe.push ci) n (by
      rw [IFEnv.find?_push]; split
      · rfl
      · exact h)

theorem pushAll_tables : ∀ (L : List IConstantInfo) (fe : IFEnv), (IFEnv.pushAll L fe).env.tables = fe.env.tables
  | [], _ => rfl
  | ci :: L, fe => by
    show (IFEnv.pushAll L (fe.push ci)).env.tables = _
    rw [pushAll_tables L (fe.push ci), IFEnv.push_env]

theorem pushTables_tables : ∀ (Q : List IProjTable) (fe : IFEnv),
    (IFEnv.pushTables Q fe).env.tables = Q.reverse ++ fe.env.tables
  | [], _ => rfl
  | t :: Q, fe => by
    rw [IFEnv.pushTables, pushTables_tables Q (fe.pushTable t)]
    show Q.reverse ++ (t :: fe.env.tables) = _
    simp

theorem feq_setFlags (fe : IFEnv) (a b : Bool) : GR.FEq (fe.setFlags a b) fe := ⟨rfl, fun _ => rfl, rfl, rfl⟩

theorem consSumCtors_push (nP : Nat) (T : NIdx) : ∀ (cs : List (IConstantVal × Nat)) (fe : IFEnv),
    ∃ L, Arena.consSumCtors nP T cs fe = IFEnv.pushAll L fe
  | [], fe => ⟨[], rfl⟩
  | c :: cs, fe => by
    obtain ⟨L, hL⟩ := consSumCtors_push nP T cs (fe.push (.ctorInfo c.1 nP c.2 T))
    exact ⟨_ :: L, hL⟩

theorem pushAll_append : ∀ (L L' : List IConstantInfo) (fe : IFEnv),
    IFEnv.pushAll (L ++ L') fe = IFEnv.pushAll L' (IFEnv.pushAll L fe)
  | [], _, _ => rfl
  | ci :: L, L', fe => pushAll_append L L' (fe.push ci)

theorem consBlockCtors_push (nP : Nat) : ∀ (gs : List (NIdx × List (IConstantVal × Nat))) (fe : IFEnv),
    ∃ L, Arena.consBlockCtors nP gs fe = IFEnv.pushAll L fe
  | [], fe => ⟨[], rfl⟩
  | (T, cs) :: gs, fe => by
    obtain ⟨L1, h1⟩ := consSumCtors_push nP T cs fe
    obtain ⟨L2, h2⟩ := consBlockCtors_push nP gs (Arena.consSumCtors nP T cs fe)
    exact ⟨L1 ++ L2, by simp only [Arena.consBlockCtors]; rw [h2, h1, pushAll_append]⟩

theorem consBlockInds_push (p₁ : Arena.BlockShape) (isRec : Bool) : ∀ (cvs : List IConstantVal) (i : Nat)
    (fe : IFEnv) (s s' : AState) (fe' : IFEnv), Arena.consBlockInds p₁ isRec cvs i fe s = .ok (fe', s') →
    ∃ L, fe' = IFEnv.pushAll L fe
  | [], _, fe, s, s', fe', h => by
    simp only [Arena.consBlockInds] at h; obtain ⟨rfl, -⟩ := AM.pure_ok h; exact ⟨[], rfl⟩
  | cv :: cvs, i, fe, s, s', fe', h => by
    simp only [Arena.consBlockInds] at h
    obtain ⟨caps, s1, -, h2⟩ := AM.bind_ok h
    obtain ⟨L, hL⟩ := consBlockInds_push p₁ isRec cvs (i + 1) _ s1 s' fe' h2
    exact ⟨_ :: L, hL⟩

/-- The pass's formers' index: the entry index with constants pushed. -/
theorem checkBlockPass_push {mode : CheckMode} {fe : IFEnv} {p : Arena.BlockShape} {isRec : Bool} {s s' : AState}
    {q : Arena.BlockPass} (h : Arena.checkBlockPass mode fe p isRec s = .ok (q, s')) :
    ∃ L, q.env1 = IFEnv.pushAll L fe := by
  simp only [Arena.checkBlockPass] at h
  obtain ⟨⟨fe₁, p₁⟩, s1, h1, h2⟩ := AM.bind_ok h
  have hfe₁ : ∃ L, fe₁ = IFEnv.pushAll L fe := by
    simp only [Arena.checkBlockInds] at h1
    cases hm : p.members with
    | nil => rw [hm] at h1; exact absurd h1 (fun h => AM.fail_ok h)
    | cons ms0 rest =>
      rw [hm] at h1
      obtain ⟨_, _, -, k1⟩ := AM.bind_ok h1
      obtain ⟨_, _, -, k2⟩ := AM.bind_ok k1
      obtain ⟨_, _, -, k3⟩ := AM.bind_ok k2
      obtain ⟨_, _, -, k4⟩ := AM.bind_ok k3
      obtain ⟨fe₁', _, k5, k6⟩ := AM.bind_ok k4
      obtain ⟨e, -⟩ := AM.pure_ok k6
      simp only [Prod.mk.injEq] at e
      first | rw [e.1] | rw [← e.1]
      exact consBlockInds_push _ _ _ _ _ _ _ _ k5
  obtain ⟨L, hL⟩ := hfe₁
  -- the rest only reads `fe₁`
  obtain ⟨_, _, -, h3⟩ := AM.bind_ok h2
  obtain ⟨_, _, -, h4⟩ := AM.bind_ok h3
  obtain ⟨_, _, -, h5⟩ := AM.bind_ok h4
  obtain ⟨_, _, -, h6⟩ := AM.bind_ok h5
  obtain ⟨_, _, -, h7⟩ := AM.bind_ok h6
  obtain ⟨_, _, -, h8⟩ := AM.bind_ok h7
  obtain ⟨_, _, -, h9⟩ := AM.bind_ok h8
  obtain ⟨rfl, -⟩ := AM.pure_ok h9
  exact ⟨L, hL⟩

theorem denoteProjTableList_mem {st : EStore} : ∀ (Q : List IProjTable) (QP : List ProjTable),
    Frontend.denoteProjTableList st Q = some QP → ∀ t ∈ Q, ∃ pt ∈ QP, Frontend.denoteProjTable st t = some pt
  | [], _, _, t, ht => nomatch ht
  | t0 :: Q, QP, h, t, ht => by
    simp only [Frontend.denoteProjTableList] at h
    split at h
    · rename_i pt pts h1 h2
      simp only [Option.some.injEq] at h; subst h
      rcases List.mem_cons.mp ht with rfl | ht'
      · exact ⟨pt, by simp, h1⟩
      · obtain ⟨pt', hm, hd⟩ := denoteProjTableList_mem Q pts h2 t ht'
        exact ⟨pt', by simp [hm], hd⟩
    · cases h

/-- A name the environment stores is stored, at its handle, in an index answering as it. -/
theorem IFEnvOK.stored {env : Env} {fe : IFEnv} {s : AState} (h : IFEnvOK env fe s) (hst : StateOK s)
    {nm : Name} (hnm : (env.find? nm).isSome = true) {n : NIdx} (hn : denoteN s.store.ns n = some nm) :
    (fe.find? n).isSome = true := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hnm
  obtain ⟨n', ci, hd', hf', -⟩ := h.cover nm c hc
  rw [denoteN_injS hst.wf hn hd', hf']; rfl

theorem blockFormers_name (p : ConLeche.BlockShape) (r : Bool) {ms : ConLeche.MemberShape} (hms : ms ∈ p.members) :
    ∃ c ∈ ConLeche.blockFormers p r, c.name = ms.declared.name := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hms
  have hi' : i < ((p.members.map (·.declared)).zipIdx).length := by simp [hi]
  refine ⟨_, List.getElem_mem (l := ((p.members.map (·.declared)).zipIdx).map _) (by simpa using hi'), ?_⟩
  simp [ConstantInfo.name]
  rfl

/-- What the index a block leaves keeps of the entry index's invariants. -/
def BlockIdx (fe fe' : IFEnv) : Prop :=
  (IFEnvCoh fe → IFEnvCoh fe') ∧
    ((∀ t ∈ fe.env.tables, IProjTableOK t) → ∀ t ∈ fe'.env.tables, IProjTableOK t) ∧ TblGate fe'

/-! ## The block's check, with the index it leaves -/

theorem checkBlock_bridgeW (hk : CoreSpec Arena.checkFuel)
    {env : Env} {fe fe' : IFEnv} {s s' : AState} {block : List IConstantInfo}
    {b : List ConstantInfo} {p₀ : Arena.BlockShape} {p₀P : ConLeche.BlockShape}
    (hok : CheckOK false env fe s) (henv : EnvWF env) (hrel : EnvRel env fe s.store)
    (hb : Frontend.denoteCIList s.store block = some b) (hp : dShape s.store p₀ = some p₀P)
    (hd : ∀ ms ∈ p₀P.members, ms.declared = ms.cvT)
    (hrun : Arena.checkBlock .verified fe block p₀ s = .ok (fe', s')) :
    IndOut s s' (∃ env', FOk (ConLeche.checkBlock (fueledOpsM .verified) env b p₀P) env' ∧
      ∃ Q, env' = env.pushDelta (ConLeche.blockConstants p₀P) Q ∧ ConLeche.blockTables p₀P p₀P.members = some Q ∧
        IFEnvOK (env.pushDelta (ConLeche.blockConstants p₀P) Q) fe' s' ∧ BlockIdx fe fe') := by
  simp only [Arena.checkBlock] at hrun
  -- the distinct names
  have hnC := nameNodup_spec hok.state.wf _ _ (dCtors_names (BlockShape.allCtors_spec hp))
  have hnM := nameNodup_spec hok.state.wf _ _ (BlockShape.memberNames_spec hp)
  by_cases hc : (!nameNodup (p₀.allCtors.map (·.1.name)) ||
      !nameNodup p₀.memberNames) = true
  · rw [ite_eq_left hc] at hrun; exact absurd hrun (fun h => AM.fail_ok h)
  rw [ite_eq_right hc] at hrun
  have hnd : (p₀P.allCtors.map (·.1.name)).Nodup ∧ p₀P.memberNames.Nodup := by
    rw [hnC, hnM] at hc
    refine ⟨(name_nodup_iff _).1 ?_, (name_nodup_iff _).1 ?_⟩ <;> revert hc <;>
      cases ConLeche.Name.nodup (p₀P.allCtors.map (·.1.name)) <;>
      cases ConLeche.Name.nodup p₀P.memberNames <;> simp
  -- the `Bool` constructors' names
  obtain ⟨bt, s₀₁, kb1, zb1⟩ := AM.bind_ok hrun
  obtain ⟨hs01, hbt⟩ := pinAt_run hok.pins (by rfl) kb1
  subst s₀₁
  obtain ⟨bf, s₀₂, kb2, zb2⟩ := AM.bind_ok zb1
  obtain ⟨hs02, hbf⟩ := pinAt_run hok.pins (by rfl) kb2
  subst s₀₂
  have hct := contains_handle_eq hok.state.wf hbt (BlockShape.memberNames_spec hp)
  have hcf := contains_handle_eq hok.state.wf hbf (BlockShape.memberNames_spec hp)
  by_cases hbc : (p₀.memberNames.contains bt || p₀.memberNames.contains bf) = true
  · rw [ite_eq_left hbc] at zb2; exact absurd zb2 (fun h => AM.fail_ok h)
  rw [ite_eq_right hbc] at zb2
  have hbool : ConLeche.boolTrueName ∉ p₀P.memberNames ∧
      ConLeche.boolFalseName ∉ p₀P.memberNames := by
    rw [hct, hcf] at hbc
    simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hbc
    simp only [ConLeche.boolTrueName, ConLeche.boolFalseName, ConLeche.boolName]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hm := List.contains_iff_mem.mpr h
      rw [hbc.1] at hm; exact nomatch hm
    · have hm := List.contains_iff_mem.mpr h
      rw [hbc.2] at hm; exact nomatch hm
  -- the members at their telescopes
  obtain ⟨hms₀, -⟩ := dShape_inv hp
  obtain ⟨ms, s₁, h1, h2⟩ := AM.bind_ok zb2
  obtain ⟨c1, msP, hms, hF1⟩ := reduceMembers_spec fe hk henv p₀.nP p₀.members p₀P.members
    s s₁ ms hok hms₀ h1
  have hnP₀ := (dShape_inv hp).2.2.1
  rw [hnP₀] at hF1
  obtain ⟨F1, hF1'⟩ := id hF1
  rw [reduceMembers_datF] at hF1'
  obtain ⟨hAt, -⟩ := ConLeche.reduceMembers_inv hd hF1'
  -- the flush
  obtain ⟨u, s₂, h3, h4⟩ := AM.bind_ok h2
  obtain ⟨c2, i2, hs2⟩ := ReadOK.flush c1.ok.toR h3
  have x12 : Ext s.store s₂.store := by rw [hs2]; exact c1.ext
  -- official's `is_rec`
  obtain ⟨isRec, s₃, h5, h6⟩ := AM.bind_ok h4
  obtain ⟨p3, hisRec⟩ := blockIsRec_spec p₀ p₀P s₂ s₃ isRec c2.state (dShape_ext x12 _ _ hp) h5
  simp only [RV] at hisRec
  subst hisRec
  have c3 := p3.toCore c2
  have x13 := x12.trans p3.ext
  -- the pass
  obtain ⟨q, s₄, h7, h8⟩ := AM.bind_ok h6
  obtain ⟨env₁, qP, i4, c4, hrel4, henv₁, hq, hT, henv₂, hMs, hpl, hFP⟩ :=
    checkBlockPass_of (p₀P := { p₀P with members := msP }) hk henv c3.ok
      (hrel.mono x13) (dShape_members (dShape_ext x13 _ _ hp)
        (dMember_ext.list (show Ext s₁.store s₃.store by rw [← hs2]; exact p3.ext) _ _ hms))
      (fun m hm => (hAt m hm).declaredWF) h7
  have x4 := i4.ext
  -- the projection tables, read off the block once
  obtain ⟨oQ, s₄₁, h81, h82⟩ := AM.bind_ok h8
  obtain ⟨p41, -, hQ⟩ := blockTables_run p₀.members p₀P.members i4.state
    (dShape_ext (x13.trans x4) _ _ hp) (dMember_ext.list (x13.trans x4) _ _ hms₀) h81
  obtain ⟨Q, s₄₂, h83, h84⟩ := AM.bind_ok h82
  obtain ⟨rfl, rfl⟩ := unwrapOr_ok h83
  obtain ⟨QP, hQP, hQd, hQok⟩ := hQ
  have c41 := p41.toCore c4
  have x41 := x4.trans p41.ext
  -- the checks after it
  obtain ⟨fe₂, s₅, h9, h10⟩ := AM.bind_ok h84
  obtain ⟨i5, hFT, hrelT, hfeqT, -⟩ := checkBlockTail_ofW hk henv₁ c41.ok (hrel4.mono p41.ext)
    (dPass_ext p41.ext hq) (denoteCIList_mono (x13.trans x41) _ _ hb) hT henv₂ hMs hpl hQd h9
  have x5 := i5.ext
  -- the block's install, read off the block
  have x05 : Ext s.store s₅.store := (x13.trans x41).trans x5
  have hpins5 : s₅.pins = s.pins := by
    rw [i5.pins, p41.pins, i4.pins, p3.pins, i2.pins, c1.pins]
  obtain ⟨recs, s₆, h11, h12⟩ := AM.bind_ok h10
  obtain ⟨p6, -, hrecsD⟩ := blockRecs_run p₀.recs p₀P.recs i5.state
    (hok.pins.mono x05 hpins5) (dShape_ext x05 _ _ hp)
    (dRec_ext.list x05 _ _ (dShape_inv hp).2.1) h11
  obtain ⟨hfe', rfl⟩ := AM.pure_ok h12
  have hi := ((c1.toInst.trans i2).trans (p3.toInst.trans (i4.trans p41.toInst))).trans
    (i5.trans p6.toInst)
  refine ⟨hi.state, hi.ext, hi.pins,
    ⟨env.pushDelta (ConLeche.blockConstants p₀P) QP, ?_, QP, rfl, hQP, ?_⟩⟩
  rotate_left
  · -- the index the block leaves
    obtain ⟨he₁, -⟩ := dPass_inv hq
    obtain ⟨F2, hF2⟩ := id hFP
    rw [ConLeche.checkBlockPass_datF] at hF2
    have henv₂ := passEnv_eq hd hF1' hF2
    rw [he₁] at henv₂
    rw [henv₂] at hrelT
    have hie₆ := (hrelT.ienv s₅ rfl).mono p6.ext
    have hall := IFEnvOK.pushAll p6.ok recs _ hie₆ (hrelT.gate) hrelT.stored hrecsD
    have htab := IFEnvOK.pushTables p6.ok Q QP hall
      (denoteProjTableList_ext (x5.trans p6.ext) hQd) hQok
    have hgate₂ := hrelT.gate
    obtain ⟨L1, hL1⟩ := checkBlockPass_push h7
    obtain ⟨L2, hL2⟩ := consBlockCtors_push q.p.nP q.p.ctorGroups q.env1
    refine ⟨?_, ?_, ?_, ?_⟩
    · unfold Env.pushDelta ConLeche.blockConstants
      rw [hfe']
      simpa [IFEnv.pushDelta, List.reverse_append, List.append_assoc] using htab
    · intro hcoh
      rw [hfe']
      refine IFEnvCoh.pushTables Q (IFEnvCoh.pushAll recs (IFEnvCoh.feq hfeqT ?_))
      rw [hL2, hL1]
      exact IFEnvCoh.pushAll L2 (IFEnvCoh.pushAll L1 hcoh)
    · intro hsh t' ht'
      rw [hfe', IFEnv.pushDelta, pushTables_tables, pushAll_tables, hfeqT.1, hL2, pushAll_tables, hL1,
        pushAll_tables] at ht'
      rcases List.mem_append.mp ht' with h' | h'
      · exact hQok t' (List.mem_reverse.mp h')
      · exact hsh t' h'
    · rw [hfe', IFEnv.pushDelta]
      refine TblGate.pushTables Q (TblGate.pushAll recs hgate₂) (fun t' ht' => ?_)
      have hQd' := denoteProjTableList_ext (x5.trans p6.ext) hQd
      obtain ⟨pt, hpt, hdt⟩ := denoteProjTableList_mem Q QP hQd' t' ht'
      obtain ⟨ms, hms, hnm⟩ := ConLeche.blockTables_names p₀P p₀P.members QP hQP pt hpt
      refine IFEnvOK.stored hall p6.ok ?_ (by rw [denoteProjTable_structName hdt, hnm])
      show ((_ : List ConstantInfo).find? _).isSome = true
      rw [List.find?_isSome]
      obtain ⟨c, hc, hcn⟩ := blockFormers_name p₀P (ConLeche.blockIsRec p₀P) hms
      exact ⟨c, by simp [hc], by simp [hcn]⟩
  unfold ConLeche.checkBlock
  rw [ite_eq_left hnd, ite_eq_left hbool, hQP]
  dsimp only
  exact FOk.bind hF1 (FOk.bind hFP (FOk.bind FOk.unwrapOr (FOk.seq hFT (FOk.pure _))))

/-! ## The route -/

theorem blockReadsAt_feq {fe fe₀ : IFEnv} {p : Arena.BlockShape} {reads : Bool} {s s' : AState}
    (h : Arena.blockReadsAt fe p s = .ok ((reads, fe₀), s')) : GR.FEq fe₀ fe := by
  simp only [Arena.blockReadsAt] at h
  obtain ⟨cs, _, -, h1⟩ := AM.bind_ok h
  obtain ⟨recs, _, -, h2⟩ := AM.bind_ok h1
  obtain ⟨ok, _, -, h3⟩ := AM.bind_ok h2
  obtain ⟨e, -⟩ := AM.pure_ok h3
  simp only [Prod.mk.injEq] at e
  obtain ⟨news, hn, hpop⟩ := consBlockRecsTemp_pop cs fe []
  rw [List.nil_append] at hn
  first | rw [e.2] | rw [← e.2]
  rw [hn]
  exact (feq_setFlags _ _ _).trans hpop

theorem checkIndRoute_bridgeW {env : Env} {fe fe' : IFEnv}
    {s s' : AState} {block : List IConstantInfo} {b : List ConstantInfo}
    {nP : Nat} {pinsP : List NatOpPinSet}
    (hk : CoreSpec Arena.checkFuel)
    (hok : FoldOK env fe s)
    (hb : Frontend.denoteCIList s.store block = some b)
    (hrun : checkIndRoute fe block nP s = .ok (fe', s')) :
    IndOut s s' (∃ env' F,
      ConLeche.checkDeclKind (ConLeche.fueledOps .verified F) pinsP env (.indDecl b nP)
        = .ok env' ∧ env' = env.pushDelta (ConLeche.declConstants (.indDecl b nP))
          (ConLeche.declTables (.indDecl b nP)) ∧ EnvWF env' ∧ IFEnvOK env' fe' s' ∧ BlockIdx fe fe') := by
  simp only [checkIndRoute] at hrun
  -- the parameter-count gate
  obtain ⟨okb, s₁, h1, h2⟩ := AM.bind_ok hrun
  obtain ⟨hstep1, hr1⟩ := indParamsOk_spec nP block b s s₁ okb hok.check.state hb h1
  subst hr1
  cases hparams : ConLeche.indParamsOk nP b with
  | false => rw [hparams] at h2; exact absurd h2 (fun h => AM.fail_ok h)
  | true =>
  rw [hparams] at h2
  simp only [Bool.not_true, Bool.false_eq_true, ite_false] at h2
  -- the reader
  obtain ⟨o, s₂, h3, h4⟩ := AM.bind_ok h2
  have c1 := hstep1.toCore hok.check
  have hb₁ : Frontend.denoteCIList s₁.store block = some b :=
    denoteCIList_mono hstep1.ext _ _ hb
  obtain ⟨c2, hr2⟩ := readBlock_spec fe nP block b s₁ s₂ o c1.ok hb₁ h3
  have hext12 : Ext s.store s₂.store := hstep1.ext.trans c2.ext
  have hpins12 : s₂.pins = s.pins := by rw [c2.pins, hstep1.pins]
  cases o with
  | error e => exact absurd h4 (fun h => AM.fail_ok h)
  | ok p =>
  simp only [ROp] at hr2
  obtain ⟨q, hq, hrel⟩ := hr2
  have hq' := toOption_eq_some hq
  -- the ι reading rule, read at the input index with the block pushed
  obtain ⟨⟨reads, fe₀⟩, s₃, h5, h6⟩ := AM.bind_ok h4
  obtain ⟨c3, hrel3, x3, pn3, hreads⟩ := blockReadsAt_bridge c2.ok
    (EnvRel.ofCheck hok.check hok.gate hok.envWF |>.mono hext12) hrel h5
  -- the block's check, at the index the pops gave back
  obtain ⟨fe'', s₄, h7, h8⟩ := AM.bind_ok h6
  have hfe₀ := blockReadsAt_feq h5
  have out := checkBlock_bridgeW hk c3 hok.envWF hrel3
    (denoteCIList_mono (c2.ext.trans x3) _ _ hb₁) (dShape_ext x3 _ _ hrel)
    (ConLeche.readBlock_declared hq') h7
  obtain ⟨env', hF, Q, rfl, hQt, hie', hbi⟩ := out.run
  cases reads with
  | false => exact absurd h8 (fun h => AM.fail_ok h)
  | true =>
  obtain ⟨rfl, rfl⟩ := AM.pure_ok h8
  have hR := hreads rfl Q
  exact
    { state := out.state
      ext := (hext12.trans x3).trans out.ext
      pins := by rw [out.pins, pn3, hpins12]
      run := by
        obtain ⟨F, hF'⟩ := FOk.checkDeclKind (pins := pinsP) (by
          rw [checkDecl_ind_route hparams, hq']
          exact FOk.bind hF (by simp only [hR]; exact FOk.pure _))
        have hwf : EnvWF (env.pushDelta (ConLeche.blockConstants q) Q) := by
          obtain ⟨F3, hF3⟩ := hF
          rw [ConLeche.checkBlock_datF] at hF3
          exact ConLeche.Semantics.blockRun_envWF hok.envWF
            (ConLeche.Semantics.blockRun_of (ConLeche.readBlock_declared hq') hF3)
        refine ⟨_, F, hF', by simp [ConLeche.declConstants, ConLeche.declTables, hq', hQt], hwf, hie',
          fun hc => hbi.1 (IFEnvCoh.feq hfe₀ hc),
          fun hs t ht => hbi.2.1 (by rw [hfe₀.1]; exact hs) t ht, hbi.2.2⟩ }

end ConRon.Bridge.Inductives
