import ConRon.Bridge.Checker.Arms
import ConRon.Bridge.Checker.Fold
import ConRon.Bridge.Checker.Pool
import ConRon.Bridge.Checker.Index
import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.Frontend.Rel
import ConRon.Bridge.Inductives.Decl

/-! # The sequential fold, bridged to con-leche

con-ron bridges its *pooled* check phase to con-leche's `checkDeclsPure`
(`ConRon.Arena.pooledAccepts_bridge`); the Pancake port refines the twin's *sequential*
`ConRon.Arena.checkDeclsPure` (`T/Decl/Start.lean`'s `checkDeclsPure_spec`).  This file closes that gap
for streams of value records (definitions, theorems, opaques), the kinds the port checks:

* each value arm of con-ron's per-declaration bridge, re-proved with one more output: the
  index the arm returns answers the pushed environment (`StepOK`), which con-ron's `DeclKindOut`
  drops because the pooled route reads every record's environment off a prebuilt index;
* the step (`andPinOk`, the flush, fresh memos, `checkDecl`) carrying a cache-free invariant
  `SeqOK` from one environment to the next;
* the fold, by induction on the stream with con-ron's `PrefixOK`, ending in
  `seq_bridge`: an accepting twin `checkDeclsPure .verified` run is an accepting con-leche
  `checkDeclsPure` run on the denoted stream.
-/

open ConLeche ConRon.Arena ConRon.Bridge

namespace ConPanqueque.Bridge

set_option autoImplicit false

/-- A value record: the kinds whose check the port carries out. -/
def IsValueDecl : IDeclaration → Prop
  | .defnDecl .. => True
  | .thmDecl .. => True
  | .opaqueDecl .. => True
  | _ => False

/-- What a value arm hands the next record: con-ron's per-arm output, the returned index
answering the pushed environment, and the index's table list unchanged. -/
structure KindOut (pinsP : List NatOpPinSet) (env : Env) (d : Declaration) (fe fe' : IFEnv)
    (s s' : AState) : Prop where
  out : DeclKindOut pinsP env d s s'
  step : StepOK (env.pushDelta (declConstants d) (declTables d)) fe' s'
  tbls : fe'.env.tables = fe.env.tables

theorem pushDelta_one (env : Env) (c : ConstantInfo) :
    env.pushDelta [c] [] = ⟨c :: env.consts, env.tables⟩ := rfl

/-- The theorem arm. -/
theorem kind_thm
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {cv : IConstantVal} {value : EIdx}
    {c : ConstantVal} {x : Expr}
    (hk : CoreSpec ConRon.Arena.checkFuel)
    (hok : FoldOK env fe s)
    (hcv : Frontend.denoteCV s.store cv = some c)
    (hv : denoteE s.store value = some x)
    (hrun : ConRon.Arena.checkDeclKind .verified pins fe (.thmDecl cv value) s = .ok (fe', s')) :
    KindOut pinsP env (.thmDecl c x) fe fe' s s' := by
  have hout := checkDeclKind_bridge_thm (pinsP := pinsP) hk hok hcv hv hrun
  simp only [ConRon.Arena.checkDeclKind] at hrun
  obtain ⟨_, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨hstep1, F1, hpure1⟩ := checkConstantVal_bridge_of_fold hk hok hcv g1
  have hcA : Frontend.denoteCV s1.store cv = some c := denoteCV_ext hcv hstep1.ext
  have hok1 : FoldOK env fe s1 := hok.ofCore hstep1
  have hv1 : denoteE s1.store value = some x := denote_ext hv hstep1.ext
  obtain ⟨ci, s2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨hstep2, rfl, hci2, hcw2, hsh2, -, -⟩ :=
    checkThmVal_bridge hk hok1 hcA (checkConstantVal_typeWF hpure1) hv1 g2
  obtain ⟨rfl, rfl⟩ := AM.pure_ok r2
  have hok2 : FoldOK env fe _ := hok1.ofCore hstep2
  exact ⟨hout, hok2.toStepOK.push hok2.check.state hci2 hsh2 hcw2, by simp⟩

/-- The opaque arm, with the compiler-trust `reduce*` gate. -/
theorem kind_opaque
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {cv : IConstantVal} {value : EIdx}
    {c : ConstantVal} {x : Expr}
    (hk : CoreSpec ConRon.Arena.checkFuel)
    (hok : FoldOK env fe s)
    (hcv : Frontend.denoteCV s.store cv = some c)
    (hv : denoteE s.store value = some x)
    (hrun : ConRon.Arena.checkDeclKind .verified pins fe (.opaqueDecl cv value) s = .ok (fe', s')) :
    KindOut pinsP env (.opaqueDecl c x) fe fe' s s' := by
  have hout := checkDeclKind_bridge_opaque (pinsP := pinsP) hk hok hcv hv hrun
  simp only [ConRon.Arena.checkDeclKind] at hrun
  obtain ⟨_, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨hstep1, F1, hpure1⟩ := checkConstantVal_bridge_of_fold hk hok hcv g1
  have hcA : Frontend.denoteCV s1.store cv = some c := denoteCV_ext hcv hstep1.ext
  have hok1 : FoldOK env fe s1 := hok.ofCore hstep1
  have hv1 : denoteE s1.store value = some x := denote_ext hv hstep1.ext
  obtain ⟨ci, s2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨hstep2, rfl, hci2, hcw2, hsh2, F2, hpure2⟩ :=
    checkOpaqueVal_bridge hk hok1 hcA (checkConstantVal_typeWF hpure1) hv1 g2
  have hx2 : Ext s1.store s2.store := hstep2.ext
  have hok2 : FoldOK env fe s2 := hok1.ofCore hstep2
  have hnm2 : denoteN s2.store.ns cv.name = some c.name :=
    denoteN_ext (denoteCV_inv hcA).1 hx2
  have hv2 : denoteE s2.store value = some x := denote_ext hv1 hx2
  obtain ⟨ns, s3, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨rfl, hns⟩ := reduceOpNames_run hok2.check.pins g3
  rcases AM.ite_ok r3 with ⟨hyes, hgood⟩ | ⟨hno, hgood⟩
  · obtain ⟨fe4, s4, g4, r4⟩ := AM.bind_ok hgood
    have hok2' : StepOK ⟨.axiomInfo c :: env.consts, env.tables⟩ (fe.push (.axiomInfo cv)) s3 :=
      hok2.toStepOK.push hok2.check.state hci2 hsh2 hcw2
    obtain ⟨hstep4, hsv4, -, -⟩ :=
      checkReducePin_bridge hk hok2.check hok2.envWF hok2' rfl hnm2 hv2
        (ConLeche.Expr.WScoped.of_not_hasFvar (checkOpaqueVal_noFvar hpure2)) g4
    obtain ⟨rfl, rfl⟩ := AM.pure_ok r4
    have hok4 : FoldOK env fe4 _ := (hok2.ofCore hstep4).sameView hsv4
    have hci4 := denoteCI_ext hci2 hstep4.ext
    exact ⟨hout, hok4.toStepOK.push hok4.check.state hci4 hsh2 hcw2,
      by simp [hsv4.env]⟩
  · replace hgood := AM.pure_bind_ok hgood
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hgood
    exact ⟨hout, hok2.toStepOK.push hok2.check.state hci2 hsh2 hcw2, by simp⟩

/-- The definition arm, with the structural-`Nat` and `Nat.div`/`Nat.mod` gates. -/
theorem kind_defn
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {cv : IConstantVal} {value : EIdx}
    {hint : ReducibilityHint} {c : ConstantVal} {x : Expr}
    (hk : CoreSpec ConRon.Arena.checkFuel)
    (hok : FoldOK env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hcv : Frontend.denoteCV s.store cv = some c)
    (hv : denoteE s.store value = some x)
    (hrun : ConRon.Arena.checkDeclKind .verified pins fe (.defnDecl cv value hint) s = .ok (fe', s')) :
    KindOut pinsP env (.defnDecl c x hint) fe fe' s s' := by
  have hout := checkDeclKind_bridge_defn hk hok hpins hcv hv hrun
  simp only [ConRon.Arena.checkDeclKind] at hrun
  obtain ⟨_, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨hstep1, F1, hpure1⟩ := checkConstantVal_bridge_of_fold hk hok hcv g1
  have hcA : Frontend.denoteCV s1.store cv = some c := denoteCV_ext hcv hstep1.ext
  have hok1 : FoldOK env fe s1 := hok.ofCore hstep1
  have hv1 : denoteE s1.store value = some x := denote_ext hv hstep1.ext
  obtain ⟨ci, s2, g2, r2⟩ := AM.bind_ok r1
  obtain ⟨hstep2, rfl, hci2, hcw2, hsh2, F2, hpure2⟩ :=
    checkDefnVal_bridge hk hok1 hcA (checkConstantVal_typeWF hpure1) hv1 g2
  have hok2 : FoldOK env fe s2 := hok1.ofCore hstep2
  have hnm2 : denoteN s2.store.ns cv.name = some c.name :=
    denoteN_ext (denoteCV_inv hcA).1 hstep2.ext
  obtain ⟨ns, s3, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨e3, -⟩ := natOpNames_run hok2.check.pins g3
  rw [e3] at r3
  -- the rest, from the index the first gate hands back
  have tail : ∀ (fe3 : IFEnv) (s4 : AState), CoreStep env fe s2 s4 →
      ConRon.Bridge.IFEnv.SameView fe3 fe →
      (do
          let d ← ConRon.Arena.natDivModNames
          if d.contains cv.name = true then do
            let y ← ConRon.Arena.checkDivModPin .verified pins fe3 (.defnInfo cv value hint) cv.name
            pure (y.push (.defnInfo cv value hint))
          else do
            let y ← pure fe3
            pure (y.push (.defnInfo cv value hint))) s4 = .ok (fe', s') →
      StepOK ⟨.defnInfo c x hint :: env.consts, env.tables⟩ fe' s' ∧
        fe'.env.tables = fe.env.tables := by
    intro fe3 s4 hstep4 hsv4 r4
    have hok4 : FoldOK env fe3 s4 := (hok2.ofCore hstep4).sameView hsv4
    have hnm4 : denoteN s4.store.ns cv.name = some c.name := denoteN_ext hnm2 hstep4.ext
    have hci4 : Frontend.denoteCI s4.store (.defnInfo cv value hint) =
        some (.defnInfo c x hint) := denoteCI_ext hci2 hstep4.ext
    obtain ⟨ds, s5, g5, r5⟩ := AM.bind_ok r4
    obtain ⟨e5, -⟩ := natDivModNames_run hok4.check.pins g5
    rw [e5] at r5
    have hx4 : Ext s.store s4.store := (hstep1.ext.trans hstep2.ext).trans hstep4.ext
    rcases AM.ite_ok r5 with ⟨-, k5⟩ | ⟨-, k5⟩
    · obtain ⟨fe5, s6, g6, r6⟩ := AM.bind_ok k5
      obtain ⟨rfl, rfl⟩ := AM.pure_ok r6
      have hok4' := hok4.toStepOK.push hok4.check.state hci4 hsh2 hcw2
      obtain ⟨hstep6, hsv6, -⟩ := checkDivModPin_bridge hk hok4.check hok4.envWF hok4' rfl
        (PinsDenote.mono hx4 _ _ hpins) hnm4 g6
      have hok6 : FoldOK env fe5 _ := (hok4.ofCore hstep6).sameView hsv6
      exact ⟨hok6.toStepOK.push hok6.check.state (denoteCI_ext hci4 hstep6.ext) hsh2 hcw2,
        by simp [hsv6.env, hsv4.env]⟩
    · replace k5 := AM.pure_bind_ok k5
      obtain ⟨rfl, rfl⟩ := AM.pure_ok k5
      exact ⟨hok4.toStepOK.push hok4.check.state hci4 hsh2 hcw2, by simp [hsv4.env]⟩
  rcases AM.ite_ok r3 with ⟨-, k3⟩ | ⟨-, k3⟩
  · obtain ⟨fe3, s4, g4, r4⟩ := AM.bind_ok k3
    have hok2' := hok2.toStepOK.push hok2.check.state hci2 hsh2 hcw2
    obtain ⟨hs, hsv, -⟩ :=
      checkStructuralNatPin_bridge hk hok2.check hok2.envWF hok2' rfl hnm2 g4
    obtain ⟨h1, h2⟩ := tail fe3 s4 hs hsv r4
    exact ⟨hout, h1, h2⟩
  · replace k3 := AM.pure_bind_ok k3
    obtain ⟨h1, h2⟩ := tail fe s2 (CoreStep.refl hok2.check)
      ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, id⟩ k3
    exact ⟨hout, h1, h2⟩

/-! ## The invariant between records -/

/-- **What holds between two records**: `FoldOK` without its caches, which every step flushes
before it reads them. -/
structure SeqOK (env : Env) (fe : IFEnv) (s : AState) : Prop where
  state : StateOK s
  pins : PinsOK s
  ienv : IFEnvOK env fe s
  envWF : EnvWF env
  tblShape : ∀ t ∈ fe.env.tables, IProjTableOK t
  persPins : PersPins s
  coh : IFEnvCoh fe
  gate : TblGate fe

theorem SeqOK.fold {env : Env} {fe : IFEnv} {s : AState} (h : SeqOK env fe s)
    (hc : s.caches = Caches.empty) : FoldOK env fe s :=
  ⟨⟨h.state, CacheOK.of_empty hc, h.pins, h.ienv⟩, h.envWF, h.tblShape, h.persPins, h.coh, h.gate⟩

/-- A value record's own checks, at the index it hands on. -/
theorem kind_value
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {pd : IDeclaration} {d : Declaration}
    (hk : CoreSpec ConRon.Arena.checkFuel)
    (hok : FoldOK env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hd : Frontend.denoteDecl s.store pd = some d) (hval : IsValueDecl pd)
    (hrun : ConRon.Arena.checkDeclKind .verified pins fe pd s = .ok (fe', s')) :
    KindOut pinsP env d fe fe' s s' := by
  cases pd with
  | defnDecl v e hint =>
    simp only [Frontend.denoteDecl] at hd
    cases hcv : Frontend.denoteCV s.store v with
    | none => rw [hcv] at hd; simp at hd
    | some cv =>
      cases he : denoteE s.store e with
      | none => rw [hcv, he] at hd; simp at hd
      | some x =>
        rw [hcv, he] at hd
        simp only [Option.some.injEq] at hd
        subst hd
        exact kind_defn hk hok hpins hcv he hrun
  | thmDecl v e =>
    simp only [Frontend.denoteDecl] at hd
    cases hcv : Frontend.denoteCV s.store v with
    | none => rw [hcv] at hd; simp at hd
    | some cv =>
      cases he : denoteE s.store e with
      | none => rw [hcv, he] at hd; simp at hd
      | some x =>
        rw [hcv, he] at hd
        simp only [Option.some.injEq] at hd
        subst hd
        exact kind_thm hk hok hcv he hrun
  | opaqueDecl v e =>
    simp only [Frontend.denoteDecl] at hd
    cases hcv : Frontend.denoteCV s.store v with
    | none => rw [hcv] at hd; simp at hd
    | some cv =>
      cases he : denoteE s.store e with
      | none => rw [hcv, he] at hd; simp at hd
      | some x =>
        rw [hcv, he] at hd
        simp only [Option.some.injEq] at hd
        subst hd
        exact kind_opaque hk hok hcv he hrun
  | _ => exact absurd hval id

/-- **A value record's check** (`checkDecl`): con-ron's per-declaration output, and the
invariant at the pushed environment. -/
theorem decl_value
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {pd : IDeclaration} {d : Declaration}
    (hk : CoreSpec ConRon.Arena.checkFuel) (hind : IndSpec)
    (hok : FoldOK env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hd : Frontend.denoteDecl s.store pd = some d) (hval : IsValueDecl pd)
    (hrun : ConRon.Arena.checkDecl .verified pins fe pd s = .ok (fe', s')) :
    DeclOut pinsP env d s s' ∧ SeqOK (env.pushDelta (declConstants d) (declTables d)) fe' s' := by
  have hout := ConRon.Bridge.Arena.checkDecl_bridge hk hind hok hpins hd hrun
  simp only [ConRon.Arena.checkDecl] at hrun
  obtain ⟨fe₂, s1, h1, h2⟩ := AM.bind_ok hrun
  have ko := kind_value hk hok hpins hd hval h1
  obtain ⟨u, s2, h3, h4⟩ := AM.bind_ok h2
  have e3 : flushCaches s1 = .ok ((), { s1 with caches := Caches.empty }) := rfl
  rw [e3] at h3
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj h3)
  obtain ⟨b, s3, h5, h6⟩ := AM.bind_ok h4
  have hrd : ReadOK { s1 with caches := Caches.empty } :=
    ⟨by intro k x hk; simp [Caches.empty] at hk, by intro k x hk; simp [Caches.empty] at hk,
      by intro k x hk; simp [Caches.empty] at hk⟩
  have hst2 : StateOK { s1 with caches := Caches.empty } := ⟨ko.out.state.wf⟩
  have hp2 : PinsOK { s1 with caches := Caches.empty } :=
    hok.check.pins.mono ko.out.ext ko.out.pins
  obtain ⟨hs3, -⟩ := basisNamesOk_run hst2 hrd hp2 (Frontend.denoteDecl_ext ko.out.ext hd) h5
  rcases AM.ite_ok h6 with ⟨-, k⟩ | ⟨-, k⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok k
    have hstep := ko.step.mono hs3.ext
    refine ⟨hout, ⟨hout.state, hok.check.pins.mono hout.ext hout.pins, hstep.ienv, hstep.envWF,
      by rw [ko.tbls]; exact hok.tblShape, hok.persPins.mono hout.pins, hstep.coh, hstep.gate⟩⟩
  · exact absurd k (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)

/-- **The twin's step** (`checkDeclStep`: the `And` pin, the flush, fresh memos, `checkDecl`) on
a value record, from the invariant to the invariant at the pushed environment. -/
theorem step_value
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {pd : IDeclaration} {d : Declaration}
    (hk : CoreSpec ConRon.Arena.checkFuel) (hind : IndSpec)
    (hok : SeqOK env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hd : Frontend.denoteDecl s.store pd = some d) (hval : IsValueDecl pd)
    (hrun : ConRon.Arena.checkDeclStep .verified pins fe pd s = .ok (fe', s')) :
    DeclOut pinsP env d s s' ∧ SeqOK (env.pushDelta (declConstants d) (declTables d)) fe' s' := by
  simp only [ConRon.Arena.checkDeclStep] at hrun
  obtain ⟨b, s1, ha, k1⟩ := AM.bind_ok hrun
  obtain ⟨hst1, hx1, -, hp1⟩ := andPinOk_run hok.state hok.pins hd ha
  rcases AM.ite_ok k1 with ⟨-, k2⟩ | ⟨-, k2⟩
  · let s2 : AState := { store := s1.store, memos := Memos.empty, caches := Caches.empty, pins := s1.pins }
    have e : ConRon.Arena.checkDecl .verified pins fe pd s2 = .ok (fe', s') := k2
    have hok2 : SeqOK env fe s2 :=
      ⟨⟨hst1.wf⟩, hok.pins.mono hx1 hp1, hok.ienv.mono hx1, hok.envWF, hok.tblShape,
        hok.persPins.mono hp1, hok.coh, hok.gate⟩
    obtain ⟨hout, hseq⟩ := decl_value hk hind (hok2.fold rfl)
      (PinsDenote.mono hx1 _ _ hpins) (Frontend.denoteDecl_ext hx1 hd) hval e
    exact ⟨⟨hout.state, hx1.trans hout.ext, hout.pins.trans hp1, hout.run⟩, hseq⟩
  · obtain ⟨_, _, hf, -⟩ := AM.bind_ok k2
    exact absurd hf (AM.Never.fail _ _ _ _)

/-! ## The fold -/

/-- **The fold from position `k`**: the invariant at the environment of the first `k` denoted
records and the prefix accepted, an accepting run of the twin's fold on the rest makes the whole
stream accepted. -/
theorem seq_fold
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet}
    (hk : CoreSpec ConRon.Arena.checkFuel) (hind : IndSpec)
    {ds : List IDeclaration} {dsP : List Declaration}
    (hval : ∀ pd ∈ ds, IsValueDecl pd) :
    ∀ m k (fe fe' : IFEnv) (s s' : AState), ds.length - k = m → k ≤ ds.length →
      SeqOK (ConLeche.streamEnv (dsP.take k)) fe s → PrefixOK pinsP dsP k →
      ((ConLeche.Cached.recsConsts (dsP.take k)).map (·.name)).Nodup →
      PinsDenote s.store pins pinsP → denoteDecls s.store ds = some dsP →
      ConRon.Arena.checkDeclsPureGo .verified pins fe (ds.drop k) s = .ok (fe', s') →
      PrefixOK pinsP dsP dsP.length := by
  intro m
  induction m with
  | zero =>
    intro k fe fe' s s' hm hk' _ hP _ _ hden _
    obtain ⟨hlen, -⟩ := denoteDecls_getElem hden
    have : k = dsP.length := by omega
    subst this; exact hP
  | succ m ih =>
    intro k fe fe' s s' hm hk' hok hP hnd hpins hden hrun
    have hlt : k < ds.length := by omega
    obtain ⟨hlen, hget⟩ := denoteDecls_getElem hden
    obtain ⟨hltP, hdk⟩ := hget k hlt
    rw [List.drop_eq_getElem_cons hlt, ConRon.Arena.checkDeclsPureGo] at hrun
    obtain ⟨fe1, s1, h1, h2⟩ := AM.bind_ok hrun
    obtain ⟨hout, hseq⟩ := step_value hk hind hok hpins hdk (hval _ (List.getElem_mem hlt)) h1
    obtain ⟨env', F, hF⟩ := hout.run
    obtain ⟨henv', hndD, hfr⟩ := kernelPushes pinsP hF
    obtain ⟨hstream, -⟩ := prefix_step hltP henv' hndD hfr hnd
    obtain ⟨hP', hnd'⟩ := PrefixOK.step (kernelPushes pinsP) hltP hP hF hnd
    have hseq' : SeqOK (ConLeche.streamEnv (dsP.take (k + 1))) fe1 s1 := by
      rw [hstream, henv']; exact hseq
    exact ih (k + 1) fe1 fe' s1 s' (by omega) (by omega) hseq' hP' hnd'
      (PinsDenote.mono hout.ext _ _ hpins) (Frontend.denoteDecls_ext hout.ext _ _ hden) h2

/-- The twin's start index is the driver's. -/
theorem mkIFEnvLits_driver {s : AState} (hp : PinsOK s) :
    mkIFEnvLits IEnv.empty s = .ok (driverFE s.pins, s) := by
  have hr : ∀ i, i < pinCount → pinAt i s = .ok (s.pins.names.getD i default, s) := by
    intro i hi
    have hlt : i < s.pins.names.size := by rw [hp.ready]; exact hi
    simp [pinAt, hlt, get, getThe, MonadStateOf.get, StateT.get, bind, StateT.bind, pure,
      StateT.pure, Except.bind, Except.pure, Array.getD_eq_getD_getElem?]
  simp only [mkIFEnvLits, ConRon.Arena.strLitNames, ConRon.Arena.natLitNames, pinNat, pinNatZero, pinNatSucc, pinString,
    pinStringOfList, pinList, pinListNil, pinListCons, pinChar, pinCharOfNat, bind, StateT.bind,
    Except.bind, hr PIN_NAT (by decide), hr PIN_NAT_ZERO (by decide), hr PIN_NAT_SUCC (by decide)]
  simp [driverFE, pure, StateT.pure, Except.pure, IEnv.empty, mkIFEnvGo, mkIFEnvTblsGo,
    hr PIN_STRING (by decide), hr PIN_STRING_OF_LIST (by decide), hr PIN_LIST (by decide),
    hr PIN_LIST_NIL (by decide), hr PIN_LIST_CONS (by decide), hr PIN_CHAR (by decide),
    hr PIN_CHAR_OF_NAT (by decide)]

/-- The invariant at the driver's start. -/
theorem seqOK_start {s : AState} (hst : StateOK s) (hp : PinsOK s) (hpp : PersPins s) :
    SeqOK Env.empty (driverFE s.pins) s := by
  have hie : IFEnvOK Env.empty (driverFE s.pins) s :=
    { hit := fun n ci h => by
        simp [driverFE, IFEnv.ofParts, IFEnv.find?, IFEnv.lookup, IFBase.find?] at h
      cover := fun nm c h => by simp [Env.empty, Env.find?] at h
      tblHit := fun n t h => by
        simp [driverFE, IFEnv.ofParts, IFEnv.findTable?, IFEnv.find?, IFEnv.lookup,
          IFBase.find?] at h
      tblCover := fun nm pt h => by simp [Env.empty, Env.findTable?, Env.find?] at h
      flags := FlagsOK.ofParts _ _ _ _
      lits := driverFE_lits hp }
  refine ⟨hst, hp, hie, ConLeche.Semantics.EnvWF.empty,
    by simp [driverFE, IFEnv.ofParts, IEnv.empty], hpp, ?_, ?_⟩
  · refine ⟨fun n => ?_, fun n => ?_⟩ <;>
      simp [driverFE, IFEnv.ofParts, IEnv.empty, mkIFEnvGo, mkIFEnvTblsGo]
  · intro n t ht
    simp [driverFE, IFEnv.ofParts, IFEnv.rawTable?, IFBase.findTable?] at ht

/-- **The sequential fold, bridged**: an accepting run of the twin's `checkDeclsPure .verified`
on a stream of value records is an accepting run of con-leche's pure fold on the stream the
records denote, ending at the environment they denote. -/
theorem seq_bridge
    (hk : CoreSpec ConRon.Arena.checkFuel) (hind : IndSpec)
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet}
    {ds : List IDeclaration} {dsP : List Declaration} {s s' : AState} {fe' : IFEnv}
    (hst : StateOK s) (hp : PinsOK s) (hpp : PersPins s)
    (hpins : PinsDenote s.store pins pinsP) (hden : denoteDecls s.store ds = some dsP)
    (hval : ∀ pd ∈ ds, IsValueDecl pd)
    (hrun : ConRon.Arena.checkDeclsPure .verified pins ds s = .ok (fe', s')) :
    ∃ F, ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified F) pinsP dsP
      = .ok (ConLeche.streamEnv dsP) := by
  simp only [ConRon.Arena.checkDeclsPure, bind, StateT.bind, mkIFEnvLits_driver hp,
    Except.bind] at hrun
  have hP := seq_fold (pinsP := pinsP) hk hind hval ds.length 0 _ fe' s s' (by simp) (by simp)
    (by rw [List.take_zero]; exact seqOK_start hst hp hpp) ⟨0, fun _ _ => rfl⟩
    (by simp [ConLeche.Cached.recsConsts]) hpins hden (by simpa using hrun)
  obtain ⟨F, hF⟩ := hP
  rw [List.take_of_length_le (Nat.le_refl _)] at hF
  exact ⟨F, hF F (Nat.le_refl _)⟩

/-- `seq_bridge` with con-ron's Core-tier and inductive hypotheses discharged
(`CoreSpec.of_core`, `indSpec_of_bridge`). -/
theorem seq_bridge'
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet}
    {ds : List IDeclaration} {dsP : List Declaration} {s s' : AState} {fe' : IFEnv}
    (hst : StateOK s) (hp : PinsOK s) (hpp : PersPins s)
    (hpins : PinsDenote s.store pins pinsP) (hden : denoteDecls s.store ds = some dsP)
    (hval : ∀ pd ∈ ds, IsValueDecl pd)
    (hrun : ConRon.Arena.checkDeclsPure .verified pins ds s = .ok (fe', s')) :
    ∃ F, ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified F) pinsP dsP
      = .ok (ConLeche.streamEnv dsP) :=
  seq_bridge CoreSpec.of_core Inductives.indSpec_of_bridge hst hp hpp hpins hden hval hrun

end ConPanqueque.Bridge
