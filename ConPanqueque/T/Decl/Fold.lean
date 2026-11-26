import ConPanqueque.T.Decl.Step
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# The fold over the records: `checkDeclsPureGo`

The records are a block of pointers in the value heap; each is checked by `checkDeclStep` in the context the
previous one left, which keeps every code fact (`ctx_tr`), the records' encodings (the heap only grows, the floor
stays), and the fold's invariants.
-/

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC
open ConPanqueque.V.Enc

/-- The level comparison's code. -/
structure LvlCodes (C : Ctx) : Prop where
  sub : C.code.lookup LSub.fSubst = some (LSub.substParams.map (fun p => (p, ShapeHOL.one)), LSub.substBody C, .one)
  neq : C.code.lookup NEq.fNeq = some ([(NEq.pNa, .one), (NEq.pNb, .one)], NEq.neqBody, .one)
  simp : C.code.lookup LSimp.fSimp = some ([(LEq.pLa, .one)], LSimp.simpBody C, .one)
  comb : C.code.lookup LComb.fComb = some ([(LEq.pLa, .one), (LEq.pLb, .one)], LComb.combBody C, .one)
  byc : C.code.lookup LLeq.fByC = some (LLeq.bcParams.map (fun p => (p, ShapeHOL.one)), LLeq.bcBody C, .one)
  itag : C.code.lookup LLeq.fITag = some ([(LEq.pLa, .one)], LLeq.itagBody, .one)
  imax : C.code.lookup LLeq.fImax = some (LLeq.leqParams.map (fun p => (p, ShapeHOL.one)), LLeq.imBody C, .one)
  eq : C.code.lookup LEq.fLvlEq = some ([(LEq.pLa, .one), (LEq.pLb, .one)], LEq.lvlEqBody, .one)
  rest : C.code.lookup LLeq.fRest = some (LLeq.leqParams.map (fun p => (p, ShapeHOL.one)), LLeq.restBody, .one)
  leq : C.code.lookup LLeq.fLeq = some (LLeq.leqParams.map (fun p => (p, ShapeHOL.one)), LLeq.leqBody, .one)

section
variable {σ : Type}

/-- The level comparison's spec, as `thm_spec` takes it. -/
theorem eqvS_of {C : Ctx} (hok : CtxOK C) (hl : LvlCodes C) :
    ∀ (H : List (BitVec 64)) (u v : LIdx) (s : AState) (lu lv : ConLeche.Level),
      denoteL s.store.ls u = some lu → denoteL s.store.ls v = some lv → CachesOK s →
      SpecR (σ := σ) (Pre (ctxH C H) s [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s (lvlEq? u v)
        (fun o w s' st => LLeq.PostOB (ctxH C H) o w s' st) := fun H u v s lu lv hu hv hco =>
  specR_mono (LLeq.lvlEqQ_spec C hok hl.sub hl.neq hl.simp hl.comb hl.byc hl.itag hl.imax hl.eq hl.rest hl.leq H u v s
    lu lv hu hv hco.rl hco.le) (fun _ h => h) (fun _ _ _ _ h => h.2.2)

end


def foP := ofString "fo_p"
def foI := ofString "fo_i"
def foN := ofString "fo_n"
def foQ := ofString "fo_q"
def foR := ofString "fo_r"
def fFold := ofString "checkDeclsGo"
def foParams : List MlS := [foP, foI, foN]
def foLocals : List MlS := [foQ, foR]

/-- Check records `i …` of the pointer block at `foP`. -/
def foldBody : ProgHOL 64 := prologue foLocals
  (.ite (.cmp .lower (vv foI) (vv foN))
    (.seq (.assign .local foQ (.load .one (.op .add [vv foP, .op .add [.panop .mul [vv foI, .const 8], .const 8]])))
    (.seq (.call (some (some (.local, foR), none)) fStep [vv foQ])
    (.seq (.call (some (some (.local, foR), none)) fFold [vv foP, .op .add [vv foI, .const 1], vv foN])
      (.return (vv foR)))))
    (.return (.const 0)))

/-- Every function the fold calls. -/
structure FoldCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  dc : DeclCodes mode C
  lc : LvlCodes C
  step : C.code.lookup fStep = some ([stQ].map (fun p => (p, ShapeHOL.one)), stepBody C, .one)
  fold : C.code.lookup fFold = some (foParams.map (fun p => (p, ShapeHOL.one)), foldBody, .one)
  kd : C.code.lookup fKd = some (kdParams.map (fun p => (p, ShapeHOL.one)), kdBody C, .one)
  kt : C.code.lookup fKt = some (kdParams.map (fun p => (p, ShapeHOL.one)), ktBody C, .one)
  ko : C.code.lookup fKo = some (kdParams.map (fun p => (p, ShapeHOL.one)), koBody C, .one)

theorem foldCodes_new {mode : ConLeche.CheckMode} {C : Ctx} (hc : FoldCodes mode C) (fe : IFEnv)
    (EH : List (BitVec 64)) (envM tblM : Std.HashMap NIdx (BitVec 64)) (H : List (BitVec 64)) :
    FoldCodes mode (ctxNewT C fe EH envM tblM H) := by ctx_tr hc

theorem recCV_new {C : Ctx} {q : Nat} {cv : IConstantVal} (h : RecCV C q cv) {fe : IFEnv} {EH : List (BitVec 64)}
    {envM tblM : Std.HashMap NIdx (BitVec 64)} {H : List (BitVec 64)} (hp : C.H <+: H) :
    RecCV (ctxNewT C fe EH envM tblM H) q cv := by
  obtain ⟨ol, ks, hn, hl, ht, hb, hlen, hkl, hks, htyD⟩ := h
  exact ⟨ol, ks, get_prefix hn hp, get_prefix hl hp, get_prefix ht hp, blkAt_mono hb hp, hlen, hkl, hks, htyD⟩

theorem recOK_new {C : Ctx} {o : Nat} {d : IDeclaration} (h : RecOK C o d) {fe : IFEnv} {EH : List (BitVec 64)}
    {envM tblM : Std.HashMap NIdx (BitVec 64)} {H : List (BitVec 64)} (hp : C.H <+: H) :
    RecOK (ctxNewT C fe EH envM tblM H) o d := by
  cases d with
  | defnDecl cv v hint =>
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
    exact ⟨get_prefix h1 hp, recCV_new h2 hp, get_prefix h3 hp, get_prefix h4 hp, h5, h6⟩
  | thmDecl cv v =>
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨get_prefix h1 hp, recCV_new h2 hp, get_prefix h3 hp⟩
  | opaqueDecl cv v =>
    obtain ⟨h1, h2, h3⟩ := h
    exact ⟨get_prefix h1 hp, recCV_new h2 hp, get_prefix h3 hp⟩
  | axiomDecl cv => obtain ⟨t, h1, h2⟩ := h; exact ⟨t, get_prefix h1 hp, h2⟩
  | indDecl b n => obtain ⟨t, h1, h2⟩ := h; exact ⟨t, get_prefix h1 hp, h2⟩
  | quotDecl k cv => obtain ⟨t, h1, h2⟩ := h; exact ⟨t, get_prefix h1 hp, h2⟩

section
variable {σ : Type}

theorem fo_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ foLocals → (ctxEnv C ++ foParams.zip vals).get x = none :=
  Knot.params_none C foLocals foParams vals (by decide) (by decide)

/-- The fold's answer: some context relates the end state. -/
def PostFold (_ : IFEnv) (_ : BitVec 64) (s' : AState) (st : PState σ) : Prop := ∃ C', SR C' s' st

/-- **The fold** over records `i …`. -/
theorem fold_spec (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (ra : ConPanqueque.Hash.RuntimeAssumptions)
    (rs : List (Nat × IDeclaration)) (ob : Nat) (hlenR : rs.length < 2 ^ 62) :
    ∀ k i (C : Ctx) (s : AState), CtxOK C → FoldCodes mode C → C.side = false → C.saved = none →
      TblGate C.fe → FlagsOK C.fe → LitsPinned C.fe C.pins → BlkAt C.H ob (rs.map (fun r => cellA C r.1)) →
      (∀ j (hj : j < rs.length), i ≤ j → RecOK C rs[j].1 rs[j].2) → rs.length - i = k → i ≤ rs.length →
      SpecR (σ := σ) (Pre C s (foParams.zip [cellA C ob, BitVec.ofNat 64 i, BitVec.ofNat 64 rs.length])) foldBody s
        (checkDeclsPureGo mode pins C.fe ((rs.drop i).map Prod.snd)) PostFold := by
  intro k
  induction k with
  | zero =>
    intro i C s hok hc hs hpl hg hF hL hb hrec hk hi
    have hil : i = rs.length := by omega
    subst hil
    refine specR_prologue (fun _ _ _ _ _ ⟨C', h⟩ => ⟨C', sr_of_eq h rfl rfl rfl rfl⟩) (fo_none C _) ?_
    have hlw := nd_lt_iff rs.length rs.length (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, foParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
      (fun h => absurd rfl h) (fun _ => ?_)
    simp only [List.drop_length, List.map_nil, checkDeclsPureGo]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨C, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ k ih =>
    intro i C s hok hc hs hpl hg hF hL hb hrec hk hi
    have hil : i < rs.length := by omega
    refine specR_prologue (fun _ _ _ _ _ ⟨C', h⟩ => ⟨C', sr_of_eq h rfl rfl rfl rfl⟩) (fo_none C _) ?_
    have hlw := nd_lt_iff i rs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, foParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hil])
      (fun _ => ?_) (fun h => absurd h (by decide))
    have hw : C.H[ob + 1 + i]? = some (cellA C rs[i].1) := by
      have := hb.2 i (by simp; omega); simpa using this
    refine UD.specR_heapLoadI' (C := C) foQ _ (ob + 1 + i) _ hw (by decide)
      (by simp +decide [sev, Env.get, foParams, ctxEnv]; exact cellA_idx C ob i) ?_
    rw [List.drop_eq_getElem_cons hil, List.map_cons, checkDeclsPureGo]
    refine specR_callNC (C := C) (D := ctxLocals ++ foLocals) foR fStep [stQ] [vv foQ] (stepBody C) [cellA C rs[i].1]
      (by decide) rfl (by decide) hc.step ?_ (PostStep C)
      (fun a w s' C' => ∃ EH envM tblM H, C' = ctxNewT C a EH envM tblM H ∧ C.H <+: H ∧ CtxOK C' ∧ TblGate a ∧
        FlagsOK a ∧ LitsPinned a C.pins)
      (fun a w s' st ⟨EH, envM, tblM, H, hpE, hpH, hokN, hsr, hgt, hfl, hlp⟩ =>
        ⟨ctxNewT C a EH envM tblM H, ⟨EH, envM, tblM, H, rfl, hpH, hokN, hgt, hfl, hlp⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [stQ] _ rfl hlk)
        (step_spec mode pins C hok hc.dc ra hs hpl hg hF hL hc.kd hc.kt hc.ko (eqvS_of hok hc.lc) rs[i].1 rs[i].2
          (hrec i hil (le_refl _)) s))
      (fun a w s1 C1 ⟨EH, envM, tblM, H1, eC, hpH, hokN, hgt, hfl, hlp⟩ => ?_)
    · exact ⟨by simp +decide [Env.get], trivial⟩
    subst eC
    refine specR_bindPure ?_
    refine specR_callNC (C := ctxNewT C a EH envM tblM H1) (D := ctxLocals ++ foLocals) foR fFold foParams
      [vv foP, .op .add [vv foI, .const 1], vv foN] foldBody
      [cellA C ob, BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 rs.length] (by decide) rfl (by decide) hc.fold ?_ PostFold
      (fun _ _ _ _ => True) (fun a w s' st ⟨C', h⟩ => ⟨C', trivial, h⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu foParams _ rfl hlk)
        (ih (i + 1) (ctxNewT C a EH envM tblM H1) s1 hokN (foldCodes_new hc a EH envM tblM H1) hs hpl hgt hfl hlp
          (blkAt_mono hb hpH) (fun j hj hij => recOK_new (hrec j hj (by omega)) hpH) (by omega) (by omega)))
      (fun _ w s2 C2 _ => ?_)
    · exact ⟨by simp +decide [Env.get, foParams, ctxEnv], by simp +decide [sev, Env.get, foParams, ctxEnv]; exact word_add1_eq i,
        by simp +decide [Env.get, foParams, ctxEnv], trivial⟩
    exact specR_returnI _ w (by simp +decide [Env.get]) (fun t ht => ⟨C2, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Decl
