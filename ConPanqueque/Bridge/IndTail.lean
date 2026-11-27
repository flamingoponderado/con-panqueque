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

end ConRon.Bridge.Inductives
