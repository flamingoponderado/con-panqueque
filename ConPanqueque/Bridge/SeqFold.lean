import ConRon.Bridge.Checker.Arms
import ConRon.Bridge.Checker.Fold
import ConRon.Bridge.Checker.Pool
import ConRon.Bridge.Checker.Index
import ConRon.Bridge.Checker.Basis
import ConRon.Bridge.Frontend.Rel
import ConRon.Bridge.Inductives.Decl
import ConLeche.Semantics.DeclWF
import ConPanqueque.Bridge.IndTail

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

/-- The standard axioms' names. -/
def IsStdAxName (n : ConLeche.Name) : Prop :=
  n = ConLeche.propextName ∨ n = ConLeche.choiceName ∨ n = ConLeche.trustCompilerName ∨
    n = ConLeche.ofReduceNatName ∨ n = ConLeche.ofReduceBoolName

/-- A record the port checks: a value record, or the `sorryAx` axiom record (its name denoting
`sorryAx`), which con-leche skips. -/
def IsChecked (ns : NStore) : IDeclaration → Prop
  | .axiomDecl cv => denoteN ns cv.name = some ConLeche.sorryAxName ∨ denoteN ns cv.name = some ConLeche.quotSoundName ∨
      ∃ n, denoteN ns cv.name = some n ∧ IsStdAxName n
  | .quotDecl _ _ => True
  | .indDecl _ _ => True
  | d => IsValueDecl d

theorem isChecked_of_value {ns : NStore} {pd : IDeclaration} (h : IsValueDecl pd) : IsChecked ns pd := by
  cases pd <;> first | exact h | exact h.elim

/-- The pin slots naming the axiom records the front end accepts: `sorryAx`, `Quot.sound`, and the standard
and compiler-trust axioms. -/
def axPinSlots : List Nat :=
  [PIN_SORRY_AX, PIN_QUOT_SOUND, PIN_PROPEXT, PIN_CHOICE, PIN_TRUST_COMPILER, PIN_OF_REDUCE_NAT, PIN_OF_REDUCE_BOOL]

/-- The standard axioms' pin slots. -/
def stdPinSlots : List Nat := [PIN_PROPEXT, PIN_CHOICE, PIN_TRUST_COMPILER, PIN_OF_REDUCE_NAT, PIN_OF_REDUCE_BOOL]

/-- A name handle one of the accepted axioms' pins. -/
def AxPinName (P : Pins) (n : NIdx) : Prop := ∃ i ∈ axPinSlots, P.names[i]? = some n

/-- What the front end hands the fold: a value record, or an axiom record named by an accepted axiom's pin. -/
def IsFrontDecl (P : Pins) : IDeclaration → Prop
  | .axiomDecl cv => AxPinName P cv.name
  | .quotDecl _ _ => True
  | d => IsValueDecl d

theorem axPin_cases {P : Pins} {n : NIdx} (h : AxPinName P n) :
    (P.names[PIN_SORRY_AX]? = some n ∨ P.names[PIN_QUOT_SOUND]? = some n) ∨
      ∃ i ∈ stdPinSlots, P.names[i]? = some n := by
  obtain ⟨i, hi, h0⟩ := h
  simp only [axPinSlots, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl (Or.inl h0)
  · exact Or.inl (Or.inr h0)
  all_goals exact Or.inr ⟨_, by simp [stdPinSlots], h0⟩

theorem denoteNL_getElem? {st : EStore} : ∀ (xs : List NIdx) (ns : List ConLeche.Name), denoteNL st xs ns →
    ∀ (i : Nat) (x : NIdx) (y : ConLeche.Name), xs[i]? = some x → ns[i]? = some y → denoteN st.ns x = some y
  | [], _, _, i, x, y, hx, _ => by simp at hx
  | _ :: _, [], h, _, _, _, _, _ => h.elim
  | x0 :: xs, n0 :: ns, h, 0, x, y, hx, hy => by
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hx hy; subst hx hy; exact h.1
  | x0 :: xs, n0 :: ns, h, i + 1, x, y, hx, hy => by
    simp only [List.getElem?_cons_succ] at hx hy; exact denoteNL_getElem? xs ns h.2 i x y hx hy

theorem isChecked_of_front {s : AState} (hp : PinsOK s) {pd : IDeclaration} (h : IsFrontDecl s.pins pd) :
    IsChecked s.store.ns pd := by
  cases pd with
  | axiomDecl cv =>
    obtain ⟨i, hi, h0⟩ := (h : AxPinName s.pins cv.name)
    have h' : s.pins.names.toList[i]? = some cv.name := by simpa using h0
    simp only [axPinSlots, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl (denoteNL_getElem? _ _ hp.names _ cv.name ConLeche.sorryAxName h' (by decide))
    · exact Or.inr (Or.inl (denoteNL_getElem? _ _ hp.names _ cv.name ConLeche.quotSoundName h' (by decide)))
    · exact Or.inr (Or.inr ⟨_, denoteNL_getElem? _ _ hp.names _ cv.name ConLeche.propextName h' (by decide),
        Or.inl rfl⟩)
    · exact Or.inr (Or.inr ⟨_, denoteNL_getElem? _ _ hp.names _ cv.name ConLeche.choiceName h' (by decide),
        Or.inr (Or.inl rfl)⟩)
    · exact Or.inr (Or.inr ⟨_, denoteNL_getElem? _ _ hp.names _ cv.name ConLeche.trustCompilerName h' (by decide),
        Or.inr (Or.inr (Or.inl rfl))⟩)
    · exact Or.inr (Or.inr ⟨_, denoteNL_getElem? _ _ hp.names _ cv.name ConLeche.ofReduceNatName h' (by decide),
        Or.inr (Or.inr (Or.inr (Or.inl rfl)))⟩)
    · exact Or.inr (Or.inr ⟨_, denoteNL_getElem? _ _ hp.names _ cv.name ConLeche.ofReduceBoolName h' (by decide),
        Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩)
  | indDecl _ _ => trivial
  | _ => exact h

/-- An axiom record named by the `sorryAx` or the `Quot.sound` pin: its name denotes that pin's. -/
theorem front_axiom_names {s : AState} (hp : PinsOK s) {cv : IConstantVal}
    (h : s.pins.names[PIN_SORRY_AX]? = some cv.name ∨ s.pins.names[PIN_QUOT_SOUND]? = some cv.name) :
    denoteN s.store.ns cv.name = some ConLeche.sorryAxName ∨ denoteN s.store.ns cv.name = some ConLeche.quotSoundName := by
  rcases h with h0 | h0
  · have h' : s.pins.names.toList[PIN_SORRY_AX]? = some cv.name := by simpa using h0
    exact Or.inl (denoteNL_getElem? _ _ hp.names PIN_SORRY_AX cv.name ConLeche.sorryAxName h' (by decide))
  · have h' : s.pins.names.toList[PIN_QUOT_SOUND]? = some cv.name := by simpa using h0
    exact Or.inr (denoteNL_getElem? _ _ hp.names PIN_QUOT_SOUND cv.name ConLeche.quotSoundName h' (by decide))

theorem isChecked_ext {a b : EStore} (hx : Ext a b) {pd : IDeclaration} (h : IsChecked a.ns pd) :
    IsChecked b.ns pd := by
  cases pd with
  | axiomDecl cv =>
    exact h.imp (fun h => denoteN_ext h hx) (fun h => h.imp (fun h => denoteN_ext h hx)
      (fun ⟨n, hn, hs⟩ => ⟨n, denoteN_ext hn hx, hs⟩))
  | _ => exact h

/-- What a value arm hands the next record: con-ron's per-arm output, the returned index
answering the pushed environment, and the index's table list unchanged. -/
structure KindOut (pinsP : List NatOpPinSet) (env : Env) (d : Declaration) (fe fe' : IFEnv)
    (s s' : AState) : Prop where
  out : DeclKindOut pinsP env d s s'
  step : StepOK (env.pushDelta (declConstants d) (declTables d)) fe' s'
  tbls : (∀ t ∈ fe.env.tables, IProjTableOK t) → ∀ t ∈ fe'.env.tables, IProjTableOK t

theorem tbls_of_eq {fe fe' : IFEnv} (e : fe'.env.tables = fe.env.tables) :
    (∀ t ∈ fe.env.tables, IProjTableOK t) → ∀ t ∈ fe'.env.tables, IProjTableOK t :=
  fun h t ht => h t (e ▸ ht)

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
  exact ⟨hout, hok2.toStepOK.push hok2.check.state hci2 hsh2 hcw2, tbls_of_eq (by simp)⟩

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
      tbls_of_eq (by simp [hsv4.env])⟩
  · replace hgood := AM.pure_bind_ok hgood
    obtain ⟨rfl, rfl⟩ := AM.pure_ok hgood
    exact ⟨hout, hok2.toStepOK.push hok2.check.state hci2 hsh2 hcw2, tbls_of_eq (by simp)⟩

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
    exact ⟨hout, h1, tbls_of_eq h2⟩
  · replace k3 := AM.pure_bind_ok k3
    obtain ⟨h1, h2⟩ := tail fe s2 (CoreStep.refl hok2.check)
      ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, id⟩ k3
    exact ⟨hout, h1, tbls_of_eq h2⟩

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

/-- The `sorryAx` arm: skipped, the environment and index unchanged. -/
theorem kind_sorry
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {cv : IConstantVal} {c : ConstantVal}
    (hk : CoreSpec ConRon.Arena.checkFuel)
    (hok : FoldOK env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hcv : Frontend.denoteCV s.store cv = some c) (hs : c.name = ConLeche.sorryAxName)
    (hrun : ConRon.Arena.checkDeclKind .verified pins fe (.axiomDecl cv) s = .ok (fe', s')) :
    KindOut pinsP env (.axiomDecl c) fe fe' s s' := by
  have hout := checkDeclKind_bridge_axiom hk hok hpins hcv hrun
  simp only [ConRon.Arena.checkDeclKind] at hrun
  obtain ⟨hnm, -, -⟩ := denoteCV_inv hcv
  obtain ⟨qs, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨e1, d1⟩ := pinAt_run (x := ConLeche.quotSoundName) hok.check.pins rfl g1
  rw [e1] at r1
  have hqs := beq_handle_iff hok.check.state.wf hnm d1
  rcases AM.ite_ok r1 with ⟨hyes, -⟩ | ⟨-, hgood⟩
  · exact absurd (hqs.mp hyes) (by rw [hs]; decide)
  obtain ⟨_, s2, g2, r2⟩ := AM.bind_ok hgood
  obtain ⟨hstep2, F2, hpure2⟩ := checkConstantVal_bridge_of_fold hk hok hcv g2
  have hcA : Frontend.denoteCV s2.store cv = some c := denoteCV_ext hcv hstep2.ext
  have hok2 : FoldOK env fe s2 := hok.ofCore hstep2
  obtain ⟨b3, s3, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨hst3, hx3, hc3, hp3, he3⟩ := stdAxiomOk_run hok2 hcA g3
  have hok3 : FoldOK env fe s3 := hok2.step (hok2.check.mono hst3 hx3 hc3 hp3) hp3
  have hcA3 : Frontend.denoteCV s3.store cv = some c := denoteCV_ext hcA hx3
  have hnmA3 : denoteN s3.store.ns cv.name = some c.name := (denoteCV_inv hcA3).1
  rcases AM.ite_ok r3 with ⟨hy3, -⟩ | ⟨-, hg3⟩
  · have h := he3 ▸ hy3
    exfalso
    simp only [ConLeche.stdAxiomOk, hs, if_neg (by decide : sorryAxName ≠ ConLeche.propextName)] at h
    rw [if_neg (by decide : sorryAxName ≠ ConLeche.choiceName)] at h
    exact absurd h (by simp)
  obtain ⟨tc, s4, g4, r4⟩ := AM.bind_ok hg3
  obtain ⟨e4, d4⟩ := pinAt_run (x := ConLeche.trustCompilerName) hok3.check.pins rfl g4
  rw [e4] at r4
  have htc := beq_handle_iff hst3.wf hnmA3 d4
  rcases AM.ite_ok r4 with ⟨hy4, -⟩ | ⟨-, hg4⟩
  · exact absurd (htc.mp hy4) (by rw [hs]; decide)
  obtain ⟨rn, s6, g6, r6⟩ := AM.bind_ok hg4
  obtain ⟨e6, d6⟩ := pinAt_run (x := ConLeche.ofReduceNatName) hok3.check.pins rfl g6
  rw [e6] at r6
  obtain ⟨bn, s7, g7, r7⟩ := AM.bind_ok r6
  obtain ⟨e7, d7⟩ := pinAt_run (x := ConLeche.ofReduceBoolName) hok3.check.pins rfl g7
  rw [e7] at r7
  have hrn := beq_handle_iff hst3.wf hnmA3 d6
  have hbn := beq_handle_iff hst3.wf hnmA3 d7
  rcases AM.ite_ok r7 with ⟨hy7, -⟩ | ⟨-, hg7⟩
  · rcases Bool.or_eq_true _ _ |>.mp hy7 with h | h
    · exact absurd (hrn.mp h) (by rw [hs]; decide)
    · exact absurd (hbn.mp h) (by rw [hs]; decide)
  obtain ⟨pn, s8, g8, r8⟩ := AM.bind_ok hg7
  obtain ⟨e8, d8⟩ := pinAt_run (x := ConLeche.propextName) hok3.check.pins rfl g8
  rw [e8] at r8
  obtain ⟨cn, s9, g9, r9⟩ := AM.bind_ok r8
  obtain ⟨e9, d9⟩ := pinAt_run (x := ConLeche.choiceName) hok3.check.pins rfl g9
  rw [e9] at r9
  rcases AM.ite_ok r9 with ⟨-, hbad⟩ | ⟨-, hg9⟩
  · exact absurd hbad (by first | exact AM.Never.fail _ _ _ _ | exact AM.Never.fail_any _ _ _)
  obtain ⟨sn, s10, g10, r10⟩ := AM.bind_ok hg9
  obtain ⟨e10, d10⟩ := pinAt_run (x := ConLeche.sorryAxName) hok3.check.pins rfl g10
  rw [e10] at r10
  have hsn := beq_handle_iff hst3.wf hnmA3 d10
  rcases AM.ite_ok r10 with ⟨-, hg10⟩ | ⟨hn10, -⟩
  · obtain ⟨rfl, rfl⟩ := AM.pure_ok hg10
    have hdc : ConLeche.declConstants (.axiomDecl c) = [] := by
      simp [ConLeche.declConstants, hs, (by decide : sorryAxName ≠ ConLeche.quotSoundName)]
    refine ⟨hout, ?_, tbls_of_eq rfl⟩
    rw [hdc]
    exact hok3.toStepOK
  · exact absurd (hsn.mpr hs) hn10

open ConLeche.Term ConLeche.Verify ConLeche.Cached ConLeche.Semantics in
/-- A quotient record's check, at the index it hands on. -/
theorem quot_core {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {k : QuotKind} {v : IConstantVal} {c : ConstantVal}
    (hok : FoldOK env fe s) (hcv : Frontend.denoteCV s.store v = some c)
    (hrun : ConRon.Arena.checkQuotRecord fe k v s = .ok (fe', s')) :
    StepOK (env.pushDelta [ConLeche.quotAt k c] []) fe' s' ∧ fe'.env.tables = fe.env.tables := by
  simp only [ConRon.Arena.checkQuotRecord] at hrun
  have hst := hok.check.state
  have hr := hok.check.readOK
  obtain ⟨c1, s₁, g1, k1⟩ := AM.bind_ok hrun
  obtain ⟨hs1, hc1⟩ := quotPinHit_run hst hr hcv g1
  obtain ⟨hy1, k2⟩ := AM.dunless_ok AM.Never.fail_any k1
  replace k2 := AM.pure_bind_ok k2
  have hhit : ConLeche.quotPinHit k c = true := by rw [← hc1]; simpa using hy1
  obtain ⟨c2, s₂, g2, k3⟩ := AM.bind_ok k2
  obtain ⟨rfl, hc2⟩ := quotPredsOk_run hs1.ok (hok.check.pins.mono hs1.ext hs1.pins)
    (hok.check.ienv.mono hs1.ext) g2
  obtain ⟨hy2, k4⟩ := AM.dunless_ok AM.Never.fail_any k3
  replace k4 := AM.pure_bind_ok k4
  have hpred : ConLeche.quotPredsOk env.find? k = true := by rw [← hc2]; simpa using hy2
  obtain ⟨ci, s₃, g3, k5⟩ := AM.bind_ok k4
  obtain ⟨hs3, hci⟩ := quotAt_run hs1.ok hs1.read (denoteCV_ext hcv hs1.ext) g3
  simp only [ConRon.Arena.installBasisDecl] at k5
  obtain ⟨-, k6⟩ := AM.dunless_ok AM.Never.fail_any k5
  replace k6 := AM.pure_bind_ok k6
  obtain ⟨rfl, rfl⟩ := AM.pure_ok k6
  -- the pushed constant's well-formedness (con-leche's `declQuotRun_envWF`, piece by piece)
  simp only [ConLeche.quotPinHit, Bool.and_eq_true, beq_iff_eq] at hhit
  obtain ⟨⟨-, hlen⟩, -⟩ := hhit
  have hname : (ConLeche.quotAt k c).name = (ConLeche.quotPin k).name := atLps_name _ _
  have hpred' : ∀ n ∈ quotNeeds k, n ≠ (ConLeche.quotPin k).name → (env.find? n).isSome = true := by
    intro n hn hne
    cases k <;> simp only [quotNeeds, List.mem_cons, List.not_mem_nil, or_false] at hn <;>
      simp only [ConLeche.quotPredsOk, Bool.and_eq_true] at hpred <;>
      rcases hn with rfl | rfl | rfl | rfl <;> simp_all
  have hdom : ∀ n, ((quotStub k).find? n).isSome = true →
      (Env.find? ⟨ConLeche.quotAt k c :: env.consts, env.tables⟩ n).isSome = true := by
    intro n hn
    rw [Env.find?_cons]
    by_cases hs : (ConLeche.quotAt k c).name = n
    · rw [ite_eq_left hs]; rfl
    · rw [ite_eq_right hs]
      exact hpred' n (quotStub_find hn) fun he => hs (hname.trans he.symm)
  obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := quotPin_facts k
  have hshape : litShapeOk (ConLeche.quotAt k c) = true :=
    litShapeOk_of_not_lit (by rw [hname]; cases k <;> decide)
  refine ⟨?_, by simp only [IFEnv.push]; split <;> rfl⟩
  exact (hok.toStepOK.mono (hs1.ext.trans hs3.ext)).push hs3.ok hci hshape
    (constWF_atLps hdom (by rw [hlen]) f1 f2 f3 f4 f5 f6)
    (by
      intro cv' caps h hn
      cases k <;> simp [ConLeche.quotAt, ConLeche.quotPin, ConLeche.ConstantInfo.atLps, ConLeche.BasisKind.decls, ConLeche.QuotKind.slot,
        ConLeche.quotBasis, ConLeche.quotA, ConLeche.quotMkA, ConLeche.quotLiftA, ConLeche.quotIndA, ConLeche.quotSoundA] at h
      obtain ⟨-, rfl⟩ := h
      exact nomatch hn)
    (by
      intro cv' nP nF T h
      cases k <;> simp [ConLeche.quotAt, ConLeche.quotPin, ConLeche.ConstantInfo.atLps, ConLeche.BasisKind.decls, ConLeche.QuotKind.slot,
        ConLeche.quotBasis, ConLeche.quotA, ConLeche.quotMkA, ConLeche.quotLiftA, ConLeche.quotIndA, ConLeche.quotSoundA] at h
      obtain ⟨rfl, -, -, rfl⟩ := h
      exact ⟨_, rfl⟩)
    (ruleWF_atLps _ f7)

theorem kind_quot
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {k : QuotKind} {v : IConstantVal} {c : ConstantVal}
    (hok : FoldOK env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hcv : Frontend.denoteCV s.store v = some c)
    (hrun : ConRon.Arena.checkDeclKind .verified pins fe (.quotDecl k v) s = .ok (fe', s')) :
    KindOut pinsP env (.quotDecl k c) fe fe' s s' := by
  have hout := checkDeclKind_bridge_quot (pinsP := pinsP) hok hcv hrun
  simp only [ConRon.Arena.checkDeclKind] at hrun
  obtain ⟨h1, h2⟩ := quot_core hok hcv hrun
  exact ⟨hout, h1, tbls_of_eq h2⟩

/-- The `Quot.sound` axiom record: the quotient record's check at the soundness slot. -/
theorem kind_qsound
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {cv : IConstantVal} {c : ConstantVal}
    (hk : CoreSpec ConRon.Arena.checkFuel)
    (hok : FoldOK env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hcv : Frontend.denoteCV s.store cv = some c) (hs : c.name = ConLeche.quotSoundName)
    (hrun : ConRon.Arena.checkDeclKind .verified pins fe (.axiomDecl cv) s = .ok (fe', s')) :
    KindOut pinsP env (.axiomDecl c) fe fe' s s' := by
  have hout := checkDeclKind_bridge_axiom hk hok hpins hcv hrun
  simp only [ConRon.Arena.checkDeclKind] at hrun
  obtain ⟨hnm, -, -⟩ := denoteCV_inv hcv
  obtain ⟨qs, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨e1, d1⟩ := pinAt_run (x := ConLeche.quotSoundName) hok.check.pins rfl g1
  subst e1
  have hqs := beq_handle_iff hok.check.state.wf hnm d1
  rw [if_pos (hqs.mpr hs)] at r1
  obtain ⟨h1, h2⟩ := quot_core hok hcv r1
  have hdc : ConLeche.declConstants (.axiomDecl c) = [ConLeche.quotAt .sound c] := by
    simp [ConLeche.declConstants, hs]
  exact ⟨hout, by rw [hdc]; exact h1, tbls_of_eq h2⟩

/-- An inductive block: its install related (`checkIndRoute_bridgeW`). -/
theorem kind_ind
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {block : List IConstantInfo} {b : List ConstantInfo} {nP : Nat}
    (hk : CoreSpec ConRon.Arena.checkFuel)
    (hok : FoldOK env fe s) (hb : Frontend.denoteCIList s.store block = some b)
    (hrun : ConRon.Arena.checkDeclKind .verified pins fe (.indDecl block nP) s = .ok (fe', s')) :
    KindOut pinsP env (.indDecl b nP) fe fe' s s' := by
  have hout := checkDeclKind_bridge_ind (pinsP := pinsP) Inductives.indSpec_of_bridge hok hb hrun
  simp only [ConRon.Arena.checkDeclKind] at hrun
  have r := Inductives.checkIndRoute_bridgeW (pinsP := pinsP) hk hok hb hrun
  obtain ⟨env', F, -, henv', hwf, hie, hbi⟩ := r.run
  subst henv'
  exact ⟨hout, ⟨hie, hwf, hbi.1 hok.coh, hbi.2.2⟩, hbi.2.1⟩


theorem stdAx_basisNamesOk {c : ConstantVal} (hs : IsStdAxName c.name) : ConLeche.basisNamesOk (.axiomDecl c) = true := by
  simp only [ConLeche.basisNamesOk]
  rcases hs with h | h | h | h | h <;> rw [h] <;> decide

theorem stdAx_ne {c : ConstantVal} (hs : IsStdAxName c.name) :
    c.name ≠ ConLeche.quotSoundName ∧ c.name ≠ ConLeche.sorryAxName := by
  rcases hs with h | h | h | h | h <;> rw [h] <;> exact ⟨by decide, by decide⟩

/-- A standard axiom's arm: the axiom pushed. -/
theorem kind_stdAx
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {cv : IConstantVal} {c : ConstantVal}
    (hk : CoreSpec ConRon.Arena.checkFuel)
    (hok : FoldOK env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hcv : Frontend.denoteCV s.store cv = some c) (hs : IsStdAxName c.name)
    (hrun : ConRon.Arena.checkDeclKind .verified pins fe (.axiomDecl cv) s = .ok (fe', s')) :
    KindOut pinsP env (.axiomDecl c) fe fe' s s' := by
  have hout := checkDeclKind_bridge_axiom hk hok hpins hcv hrun
  obtain ⟨hnq, hns⟩ := stdAx_ne hs
  have hdc : ConLeche.declConstants (.axiomDecl c) = [.axiomInfo c] := by
    simp [ConLeche.declConstants, hnq, hns]
  -- con-leche's environment after the record
  obtain ⟨env', F, hL⟩ := hout.run
  have hL' : ConLeche.checkDecl .verified (ConLeche.fueledOps .verified F) pinsP env (.axiomDecl c) = .ok env' := by
    unfold ConLeche.checkDecl
    rw [hL]
    simp [stdAx_basisNamesOk hs, bind, Except.bind, pure, Except.pure]
  have hE' := ConLeche.Cached.checkDecl_pushes hL'
  rw [hdc] at hE'
  have hwE' : EnvWF env' := ConLeche.Semantics.checkDecl_envWF hok.envWF hL'
  rw [hE'] at hwE'
  have hmem : ConstantInfo.axiomInfo c ∈ (env.pushDelta [.axiomInfo c] []).consts := by
    simp [Env.pushDelta]
  have hsh : litShapeOk (.axiomInfo c) = true := hwE'.shapes _ hmem
  have hcw : ConstWF ⟨.axiomInfo c :: env.consts, env.tables⟩ (.axiomInfo c) := hwE'.consts _ hmem
  -- the twin's run
  simp only [ConRon.Arena.checkDeclKind] at hrun
  obtain ⟨hnm, -, -⟩ := denoteCV_inv hcv
  obtain ⟨qs, s1, g1, r1⟩ := AM.bind_ok hrun
  obtain ⟨e1, d1⟩ := pinAt_run (x := ConLeche.quotSoundName) hok.check.pins rfl g1
  rw [e1] at r1
  have hqs := beq_handle_iff hok.check.state.wf hnm d1
  rcases AM.ite_ok r1 with ⟨hyes, -⟩ | ⟨-, hgood⟩
  · exact absurd (hqs.mp hyes) hnq
  obtain ⟨_, s2, g2, r2⟩ := AM.bind_ok hgood
  obtain ⟨hstep2, F2, hpure2⟩ := checkConstantVal_bridge_of_fold hk hok hcv g2
  have hcA : Frontend.denoteCV s2.store cv = some c := denoteCV_ext hcv hstep2.ext
  have hok2 : FoldOK env fe s2 := hok.ofCore hstep2
  obtain ⟨b3, s3, g3, r3⟩ := AM.bind_ok r2
  obtain ⟨hst3, hx3, hc3, hp3, he3⟩ := stdAxiomOk_run hok2 hcA g3
  have hok3 : FoldOK env fe s3 := hok2.step (hok2.check.mono hst3 hx3 hc3 hp3) hp3
  have hcA3 : Frontend.denoteCV s3.store cv = some c := denoteCV_ext hcA hx3
  have hnmA3 : denoteN s3.store.ns cv.name = some c.name := (denoteCV_inv hcA3).1
  have hci : ∀ st : EStore, Frontend.denoteCV st cv = some c →
      Frontend.denoteCI st (.axiomInfo cv) = some (.axiomInfo c) := fun st h => by
    simp [Frontend.denoteCI, h]
  have fin : ∀ s₄ : AState, DeclKindOut pinsP env (.axiomDecl c) s s₄ → FoldOK env fe s₄ →
      Frontend.denoteCV s₄.store cv = some c →
      KindOut pinsP env (.axiomDecl c) fe (fe.push (.axiomInfo cv)) s s₄ := fun s₄ hout₄ hok₄ hc₄ => by
    refine ⟨hout₄, ?_, tbls_of_eq (by simp)⟩
    rw [hdc]
    exact hok₄.toStepOK.push hok₄.check.state (hci _ hc₄) hsh hcw
  rcases AM.ite_ok r3 with ⟨hy3, h3⟩ | ⟨hn3, hg3⟩
  · obtain ⟨ha, hb⟩ := AM.pure_ok h3
    subst ha hb
    exact fin _ hout hok3 hcA3
  obtain ⟨tc, s4, g4, r4⟩ := AM.bind_ok hg3
  obtain ⟨e4, d4⟩ := pinAt_run (x := ConLeche.trustCompilerName) hok3.check.pins rfl g4
  rw [e4] at r4
  rcases AM.ite_ok r4 with ⟨hy4, h4⟩ | ⟨-, hg4⟩
  · obtain ⟨b5, s5, g5, r5⟩ := AM.bind_ok h4
    obtain ⟨hst5, hx5, hc5, hp5, he5⟩ := trustCompilerOk_run hok3 hcA3 g5
    have hok5 : FoldOK env fe s5 := hok3.step (hok3.check.mono hst5 hx5 hc5 hp5) hp5
    rcases AM.ite_ok r5 with ⟨-, h5⟩ | ⟨-, hbad⟩
    · obtain ⟨ha, hb⟩ := AM.pure_ok h5
      subst ha hb
      exact fin _ hout hok5 (denoteCV_ext hcA3 hx5)
    · exact absurd hbad (by first | exact AM.Never.fail _ _ _ _ | exact AM.Never.fail_any _ _ _)
  obtain ⟨rn, s6, g6, r6⟩ := AM.bind_ok hg4
  obtain ⟨e6, d6⟩ := pinAt_run (x := ConLeche.ofReduceNatName) hok3.check.pins rfl g6
  rw [e6] at r6
  obtain ⟨bn, s7, g7, r7⟩ := AM.bind_ok r6
  obtain ⟨e7, d7⟩ := pinAt_run (x := ConLeche.ofReduceBoolName) hok3.check.pins rfl g7
  rw [e7] at r7
  rcases AM.ite_ok r7 with ⟨hy7, h7⟩ | ⟨-, hg7⟩
  · obtain ⟨b8, s8, g8, r8⟩ := AM.bind_ok h7
    obtain ⟨hst8, hx8, hc8, hp8, he8⟩ := ofReduceAxOk_run hok3 hcA3 g8
    have hok8 : FoldOK env fe s8 := hok3.step (hok3.check.mono hst8 hx8 hc8 hp8) hp8
    rcases AM.ite_ok r8 with ⟨-, h8⟩ | ⟨-, hbad⟩
    · obtain ⟨ha, hb⟩ := AM.pure_ok h8
      subst ha hb
      exact fin _ hout hok8 (denoteCV_ext hcA3 hx8)
    · exact absurd hbad (by first | exact AM.Never.fail _ _ _ _ | exact AM.Never.fail_any _ _ _)
  obtain ⟨pn, s9, g9, r9⟩ := AM.bind_ok hg7
  obtain ⟨e9, d9⟩ := pinAt_run (x := ConLeche.propextName) hok3.check.pins rfl g9
  rw [e9] at r9
  obtain ⟨cn, s10, g10, r10⟩ := AM.bind_ok r9
  obtain ⟨e10, d10⟩ := pinAt_run (x := ConLeche.choiceName) hok3.check.pins rfl g10
  rw [e10] at r10
  rcases AM.ite_ok r10 with ⟨-, hbad⟩ | ⟨hn10, hg10⟩
  · exact absurd hbad (by first | exact AM.Never.fail _ _ _ _ | exact AM.Never.fail_any _ _ _)
  obtain ⟨sn, s11, g11, r11⟩ := AM.bind_ok hg10
  obtain ⟨e11, d11⟩ := pinAt_run (x := ConLeche.sorryAxName) hok3.check.pins rfl g11
  rw [e11] at r11
  have hsn := beq_handle_iff hst3.wf hnmA3 d11
  rcases AM.ite_ok r11 with ⟨hy11, -⟩ | ⟨-, hbad⟩
  · exact absurd (hsn.mp hy11) hns
  · obtain ⟨_, _, _, hbad'⟩ := AM.bind_ok hbad
    exact absurd hbad' (by first | exact AM.Never.fail _ _ _ _ | exact AM.Never.fail_any _ _ _)

/-- A value record's own checks, at the index it hands on. -/
theorem kind_value
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {pd : IDeclaration} {d : Declaration}
    (hk : CoreSpec ConRon.Arena.checkFuel)
    (hok : FoldOK env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hd : Frontend.denoteDecl s.store pd = some d) (hval : IsChecked s.store.ns pd)
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
  | axiomDecl v =>
    simp only [Frontend.denoteDecl] at hd
    cases hcv : Frontend.denoteCV s.store v with
    | none => rw [hcv] at hd; simp at hd
    | some cv =>
      rw [hcv] at hd
      simp only [Option.map_some, Option.some.injEq] at hd
      subst hd
      have hn := (denoteCV_inv hcv).1
      rcases (hval : denoteN s.store.ns v.name = some ConLeche.sorryAxName ∨
          denoteN s.store.ns v.name = some ConLeche.quotSoundName ∨
          ∃ n, denoteN s.store.ns v.name = some n ∧ IsStdAxName n) with h | h | ⟨n, h, hstd⟩
      · rw [hn] at h
        exact kind_sorry hk hok hpins hcv (Option.some.inj h) hrun
      · rw [hn] at h
        exact kind_qsound hk hok hpins hcv (Option.some.inj h) hrun
      · rw [hn] at h
        obtain rfl := Option.some.inj h
        exact kind_stdAx hk hok hpins hcv hstd hrun
  | quotDecl qk v =>
    simp only [Frontend.denoteDecl] at hd
    cases hcv : Frontend.denoteCV s.store v with
    | none => rw [hcv] at hd; simp at hd
    | some cv =>
      rw [hcv] at hd
      simp only [Option.map_some, Option.some.injEq] at hd
      subst hd
      exact kind_quot hok hpins hcv hrun
  | indDecl block nP =>
    simp only [Frontend.denoteDecl] at hd
    cases hb : Frontend.denoteCIList s.store block with
    | none => rw [hb] at hd; simp at hd
    | some bl =>
      rw [hb] at hd
      simp only [Option.map_some, Option.some.injEq] at hd
      subst hd
      exact kind_ind hk hok hb hrun

/-- **A value record's check** (`checkDecl`): con-ron's per-declaration output, and the
invariant at the pushed environment. -/
theorem decl_value
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {pd : IDeclaration} {d : Declaration}
    (hk : CoreSpec ConRon.Arena.checkFuel) (hind : IndSpec)
    (hok : FoldOK env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hd : Frontend.denoteDecl s.store pd = some d) (hval : IsChecked s.store.ns pd)
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
      ko.tbls hok.tblShape, hok.persPins.mono hout.pins, hstep.coh, hstep.gate⟩⟩
  · exact absurd k (AM.Never.bind (fun _ => AM.Never.fail _) _ _ _)

/-- **The twin's step** (`checkDeclStep`: the `And` pin, the flush, fresh memos, `checkDecl`) on
a value record, from the invariant to the invariant at the pushed environment. -/
theorem step_value
    {pins : List INatOpPinSet} {pinsP : List NatOpPinSet} {env : Env}
    {fe fe' : IFEnv} {s s' : AState} {pd : IDeclaration} {d : Declaration}
    (hk : CoreSpec ConRon.Arena.checkFuel) (hind : IndSpec)
    (hok : SeqOK env fe s) (hpins : PinsDenote s.store pins pinsP)
    (hd : Frontend.denoteDecl s.store pd = some d) (hval : IsChecked s.store.ns pd)
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
      (PinsDenote.mono hx1 _ _ hpins) (Frontend.denoteDecl_ext hx1 hd) (isChecked_ext hx1 hval) e
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
    {ds : List IDeclaration} {dsP : List Declaration} :
    ∀ m k (fe fe' : IFEnv) (s s' : AState), ds.length - k = m → k ≤ ds.length →
      (∀ pd ∈ ds, IsChecked s.store.ns pd) →
      SeqOK (ConLeche.streamEnv (dsP.take k)) fe s → PrefixOK pinsP dsP k →
      ((ConLeche.Cached.recsConsts (dsP.take k)).map (·.name)).Nodup →
      PinsDenote s.store pins pinsP → denoteDecls s.store ds = some dsP →
      ConRon.Arena.checkDeclsPureGo .verified pins fe (ds.drop k) s = .ok (fe', s') →
      PrefixOK pinsP dsP dsP.length := by
  intro m
  induction m with
  | zero =>
    intro k fe fe' s s' hm hk' _ _ hP _ _ hden _
    obtain ⟨hlen, -⟩ := denoteDecls_getElem hden
    have : k = dsP.length := by omega
    subst this; exact hP
  | succ m ih =>
    intro k fe fe' s s' hm hk' hval hok hP hnd hpins hden hrun
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
    exact ih (k + 1) fe1 fe' s1 s' (by omega) (by omega) (fun pd h => isChecked_ext hout.ext (hval pd h)) hseq' hP' hnd'
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
    (hval : ∀ pd ∈ ds, IsChecked s.store.ns pd)
    (hrun : ConRon.Arena.checkDeclsPure .verified pins ds s = .ok (fe', s')) :
    ∃ F, ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified F) pinsP dsP
      = .ok (ConLeche.streamEnv dsP) := by
  simp only [ConRon.Arena.checkDeclsPure, bind, StateT.bind, mkIFEnvLits_driver hp,
    Except.bind] at hrun
  have hP := seq_fold (pinsP := pinsP) hk hind ds.length 0 _ fe' s s' (by simp) (by simp) hval
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
    (hval : ∀ pd ∈ ds, IsChecked s.store.ns pd)
    (hrun : ConRon.Arena.checkDeclsPure .verified pins ds s = .ok (fe', s')) :
    ∃ F, ConLeche.checkDeclsPure .verified (ConLeche.fueledOps .verified F) pinsP dsP
      = .ok (ConLeche.streamEnv dsP) :=
  seq_bridge CoreSpec.of_core Inductives.indSpec_of_bridge hst hp hpp hpins hden hval hrun

end ConPanqueque.Bridge
