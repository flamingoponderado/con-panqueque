import ConPanqueque.T.Quot.Arm

/-!
# `checkDecl` at a quotient record: the proof
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

/-- The code a quotient record runs. -/
structure QCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  d : DeclCodes mode C
  e : ECodes C
  pl : C.code.lookup fParamLevels = some (plParams.map (fun p => (p, ShapeHOL.one)), plBody C, .one)
  pf : C.code.lookup fPlFill = some (pfParams.map (fun p => (p, ShapeHOL.one)), pfBody, .one)
  ilp1 : C.code.lookup fInternLParam = some ([(lEn, .one)], internLParamBody, .one)
  ilpf : C.code.lookup fInstLPF = some (ilpParams.map (fun p => (p, ShapeHOL.one)), ilpfBody C, .one)
  ilp : CodesILP C (ilpBody C)
  iq : C.code.lookup fInstQ = some (iqParams.map (fun p => (p, ShapeHOL.one)), instQBody C, .one)

set_option maxRecDepth 8000 in
theorem qcodes_ctxH {mode : ConLeche.CheckMode} {C : Ctx} (h : QCodes mode C) (H : List (BitVec 64)) :
    QCodes mode (ctxH C H) := by
  obtain ⟨d, e, pl, pf, ilp1, ilpf, ilp, iq⟩ := h
  exact ⟨by ctx_tr d, by ctx_tr e, pl, pf, ilp1, ilpf, by ctx_tr ilp, iq⟩

/-- A record's constant value in the value heap at `q` (`Decl.RecCV`'s copy). -/
def RecCVQ (C : Ctx) (q : Nat) (cv : IConstantVal) : Prop :=
  ∃ (ol : Nat) (ks : List ConLeche.Name), C.H[q]? = some (Enc.idxW cv.name) ∧ C.H[q + 1]? = some (cellA C ol) ∧
    C.H[q + 2]? = some (Enc.idxW cv.type) ∧ BlkAt C.H ol (cv.levelParams.map Enc.idxW) ∧
    cv.levelParams.length < 2 ^ 59 ∧ ∃ hkl : ks.length = cv.levelParams.length,
    (∀ j (hj : j < cv.levelParams.length), denoteN C.St.ns cv.levelParams[j] = some (ks[j]'(by omega))) ∧
    (denoteE C.St cv.type).isSome = true

/-- The two locals the arm reads throughout: the record and the key buffer. -/
def Base (C : Ctx) (q : Nat) (Γ : Env) : Prop := Γ.get kdQ = some (cellA C q) ∧ Γ.get lKb = some C.KB

theorem base_cons {C : Ctx} {q : Nat} {Γ : Env} (h : Base C q Γ) {x : MlS} (h1 : x ≠ kdQ) (h2 : x ≠ lKb)
    (w : BitVec 64) : Base C q ((x, w) :: Γ) := by
  refine ⟨?_, ?_⟩
  · rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e.symm h1)]; exact h.1
  · rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e.symm h2)]; exact h.2

theorem base_agreeQ {C : Ctx} {q : Nat} {Γ Γ' : Env} (h : Base C q Γ) (ha : AgreeQ Γ Γ') : Base C q Γ' := by
  have hQ : ∀ c j, kdQ ≠ gv c j := fun c j e => gv_ne_of (m := kdQ) (by simp [kdQ, ofString]) e.symm
  have hK : ∀ c j, lKb ≠ gv c j := fun c j e => gv_ne_of (m := lKb) (by simp [lKb, ofString]) e.symm
  exact ⟨by rw [ha kdQ hQ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.1,
    by rw [ha lKb hK (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)]; exact h.2⟩

section
variable {σ : Type}

theorem bind_run_of {α β : Type} {A : AM α} {K : α → AM β} {s s' : AState} {a : α} (h : A s = .ok (a, s')) :
    (A >>= K) s = K a s' := by
  simp [bind, StateT.bind, h, Except.bind]

theorem specR_basisQuot {β : Type} {P : PState σ → Prop} {c : ProgHOL 64} {s : AState}
    {K : List IConstantInfo → AM β} {R : β → BitVec 64 → AState → PState σ → Prop} (ho : InternRerun.Off s.store)
    (h : SpecR P c s (plainCIList quotBasis >>= K) R) : SpecR P c s (ConRon.Arena.BasisKind.decls .quotK >>= K) R :=
  specR_okImp (fun a s' hr => by
    obtain ⟨b, s1, h1, h2⟩ := AM.bind_ok hr
    rw [bind_run_of (basisDecls_plain .quotK ho h1)]; exact h2) h

/-- `if x ≠ y then hang`: past it the two words agree. -/
theorem specR_guardNe {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x y : MlS) (a b : BitVec 64)
    (ha : Γ.get x = some a) (hb : Γ.get y = some b) (hk : a = b → SpecR (Inv C s Γ M D) rest s m R) :
    SpecR (Inv C s Γ M D) (.ite (.cmp .notEqual (vv x) (vv y)) hang rest) s m R := by
  by_cases e : a = b
  · subst e
    exact specR_ifI _ 0 (by simp [sev, sev_vv, ha, hb, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => hk rfl)
  · exact specR_ifI _ 1 (by simp [sev, sev_vv, ha, hb, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, e])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))

/-- `if x = 0 then hang`: past it the word is not `0`. -/
theorem specR_guardZ {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (a : BitVec 64)
    (ha : Γ.get x = some a) (hk : a ≠ 0 → SpecR (Inv C s Γ M D) rest s m R) :
    SpecR (Inv C s Γ M D) (.ite (.cmp .equal (vv x) (.const 0)) hang rest) s m R := by
  by_cases e : a = 0
  · subst e
    exact specR_ifI _ 1 (by simp [sev, sev_vv, ha, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  · exact specR_ifI _ 0 (by simp [sev, sev_vv, ha, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact e)
      (fun h => absurd rfl h) (fun _ => hk e)

/-- `if x ≠ 0 then hang`: past it the word is `0`. -/
theorem specR_guardNZ {α : Type} {C : Ctx} {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64}
    {m : AM α} {R : α → BitVec 64 → AState → PState σ → Prop} (x : MlS) (a : BitVec 64)
    (ha : Γ.get x = some a) (hk : a = 0 → SpecR (Inv C s Γ M D) rest s m R) :
    SpecR (Inv C s Γ M D) (.ite (.cmp .notEqual (vv x) (.const 0)) hang rest) s m R := by
  by_cases e : a = 0
  · subst e
    exact specR_ifI _ 0 (by simp [sev, sev_vv, ha, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => hk rfl)
  · exact specR_ifI _ 1 (by simp [sev, sev_vv, ha, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact e)
      (fun _ => specR_hangI) (fun h => absurd h (by decide))

/-- **One presence test**: pin `i`'s constant stored, else a hang. -/
theorem specR_predGuardI {α : Type} {C : Ctx} (hok : CtxOK C)
    (hcG : C.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcP : C.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    {s : AState} {Γ : Env} {M : Mem} {D : List MlS} {rest : ProgHOL 64} {m : AM α}
    {R : α → BitVec 64 → AState → PState σ → Prop} (i : Nat) (hi : i < pinCount) (hD : kqF ∈ D)
    (hkb : Γ.get lKb = some C.KB)
    (hk : ∀ w w', (C.fe.find? C.pins.names[i]!).isSome = true →
      SpecR (Inv C s ((kqF, w) :: (kqF, w') :: Γ) [] D) rest s m R) :
    SpecR (Inv C s Γ M D) (predGuard C i rest) s m R := by
  have hi' : i < C.pins.names.size := by rw [hok.pinsRel.1]; exact hi
  unfold predGuard
  refine specR_envLoadI kqF _ (C.PO + i) _ hD rfl (hok.pinsRel.2.1 i hi') ?_
  refine specR_envFindI hok hcG hcP kqF (vv kqF) C.pins.names[i] hD (by simp [sev, Env.get_cons])
    (by rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e (by decide))]; exact hkb) ?_
  have hrel := find_rel hok C.pins.names[i]
  have hb : C.pins.names[i]! = C.pins.names[i] := by simp [hi']
  revert hrel
  rcases hfn : C.fe.find? C.pins.names[i] with _ | ci0
  · intro hrel
    simp only at hrel
    rw [hrel]
    exact specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  · intro ⟨o', hm, hci⟩
    rw [hm]
    refine specR_atEntry fun t ht => ?_
    have hoE : o' < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
    exact specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
      (fun h => absurd rfl h) (fun _ => hk _ _ (by rw [hb, hfn]; rfl))

/-- `quotPredsOk`'s answer, read off the context's pins. -/
def predB (C : Ctx) : ConLeche.QuotKind → Bool
  | .type => (C.fe.find? C.pins.names[PIN_EQ]!).isSome
  | .ctor => (C.fe.find? C.pins.names[PIN_QUOT]!).isSome
  | .lift => (C.fe.find? C.pins.names[PIN_EQ]!).isSome && (C.fe.find? C.pins.names[PIN_QUOT]!).isSome &&
      (C.fe.find? C.pins.names[PIN_QUOT_MK]!).isSome
  | .ind => (C.fe.find? C.pins.names[PIN_QUOT]!).isSome && (C.fe.find? C.pins.names[PIN_QUOT_MK]!).isSome
  | .sound => (C.fe.find? C.pins.names[PIN_EQ]!).isSome && (C.fe.find? C.pins.names[PIN_QUOT]!).isSome &&
      (C.fe.find? C.pins.names[PIN_QUOT_MK]!).isSome

theorem quotPredsOk_run' {C : Ctx} (hok : CtxOK C) {s : AState} (hp : s.pins = C.pins) (k : ConLeche.QuotKind) :
    quotPredsOk C.fe k s = .ok (predB C k, s) := by
  have h := fun i (hi : i < pinCount) => pinAt_run hok hp i hi
  simp only [quotPredsOk, pinEq, pinQuot, pinQuotMk]
  simp only [bind, StateT.bind, Except.bind, h PIN_EQ (by decide), h PIN_QUOT (by decide), h PIN_QUOT_MK (by decide)]
  cases k <;> rfl

theorem gv_ne_kq (c : Char) (j : Nat) (x : MlS) (hx : x.explode.head? ≠ some (BitVec.ofNat 8 'g'.toNat)) :
    gv c j ≠ x := gv_ne_of hx

theorem quotSlot_den {s s1 : AState} {blk : List IConstantInfo} (hst : StateOK s) (ho : InternRerun.Off s.store)
    (hr : plainCIList quotBasis s = .ok (blk, s1)) (j : Nat) (hj : j < 5) :
    Frontend.IStepS s s1 ∧
      ∃ x : ConLeche.ConstantVal, Frontend.denoteCV s1.store (blk.getD j default).toConstantVal = some x := by
  have hd := basisDecls_plain .quotK ho hr
  obtain ⟨hs1, hden⟩ := ConRon.Bridge.BasisKind.decls_run hst hd
  have hlen := denoteCIList_length blk _ hden
  have hjl : j < blk.length := by rw [hlen]; simp [ConLeche.BasisKind.decls, ConLeche.quotBasis]; omega
  obtain ⟨x, -, hx⟩ := denoteCIList_get blk _ j blk[j] hden (List.getElem?_eq_getElem hjl)
  refine ⟨hs1, x.toConstantVal, ?_⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjl, Option.getD_some]
  exact denoteCI_toConstantVal hx

/-- The interned `Quot` pin: an inductive type with no capabilities. -/
def capsQ : IIndCaps := ⟨false, [], 0, 0, [], false⟩

theorem quotBlk_slot0 {s s' : AState} {blk : List IConstantInfo} (h : plainCIList quotBasis s = .ok (blk, s')) :
    ∃ v, blk.getD 0 default = .indInfo v capsQ := by
  simp only [quotBasis, ConLeche.BasisKind.decls, ConLeche.quotBasis, plainCIList] at h
  obtain ⟨r0, s1, h0, h1⟩ := AM.bind_ok h
  obtain ⟨rs, s2, -, h3⟩ := AM.bind_ok h1
  obtain ⟨rfl, -⟩ := AM.pure_ok h3
  simp only [ConLeche.quotA, plainCI] at h0
  obtain ⟨v, s3, -, h4⟩ := AM.bind_ok h0
  obtain ⟨c, s4, h5, h6⟩ := AM.bind_ok h4
  obtain ⟨rfl, -⟩ := AM.pure_ok h6
  have hc : c = capsQ := by
    simp only [ConRon.Arena.Frontend.internCaps, ConRon.Arena.Frontend.internNameList] at h5
    obtain ⟨a, s5, h7, h8⟩ := AM.bind_ok h5
    obtain ⟨rfl, -⟩ := AM.pure_ok h7
    obtain ⟨b, s6, h9, h10⟩ := AM.bind_ok h8
    obtain ⟨rfl, -⟩ := AM.pure_ok h9
    obtain ⟨rfl, -⟩ := AM.pure_ok h10
    rfl
  exact ⟨v, by rw [hc]; rfl⟩

theorem quotBlk_slot1 {s s' : AState} {blk : List IConstantInfo} (h : plainCIList quotBasis s = .ok (blk, s')) :
    ∃ v t, blk.getD 1 default = .ctorInfo v 2 1 t := by
  simp only [quotBasis, ConLeche.BasisKind.decls, ConLeche.quotBasis, plainCIList] at h
  obtain ⟨r0, s1, -, h1⟩ := AM.bind_ok h
  obtain ⟨rs, s2, h2, h3⟩ := AM.bind_ok h1
  obtain ⟨rfl, -⟩ := AM.pure_ok h3
  obtain ⟨r1, s5, h5, h6⟩ := AM.bind_ok h2
  obtain ⟨rs', s6, -, h7⟩ := AM.bind_ok h6
  obtain ⟨rfl, -⟩ := AM.pure_ok h7
  simp only [ConLeche.quotMkA, plainCI] at h5
  obtain ⟨v, s3, -, h8⟩ := AM.bind_ok h5
  obtain ⟨t, s4, -, h9⟩ := AM.bind_ok h8
  obtain ⟨rfl, -⟩ := AM.pure_ok h9
  exact ⟨v, t, rfl⟩

theorem quotBlk_slot4 {s s' : AState} {blk : List IConstantInfo} (h : plainCIList quotBasis s = .ok (blk, s')) :
    ∃ v, blk.getD 4 default = .axiomInfo v := by
  simp only [quotBasis, ConLeche.BasisKind.decls, ConLeche.quotBasis, plainCIList] at h
  obtain ⟨_, _, -, h1⟩ := AM.bind_ok h
  obtain ⟨_, _, h2, h3⟩ := AM.bind_ok h1
  obtain ⟨rfl, -⟩ := AM.pure_ok h3
  obtain ⟨_, _, -, h4⟩ := AM.bind_ok h2
  obtain ⟨_, _, h5, h6⟩ := AM.bind_ok h4
  obtain ⟨rfl, -⟩ := AM.pure_ok h6
  obtain ⟨_, _, -, h7⟩ := AM.bind_ok h5
  obtain ⟨_, _, h8, h9⟩ := AM.bind_ok h7
  obtain ⟨rfl, -⟩ := AM.pure_ok h9
  obtain ⟨_, _, -, h10⟩ := AM.bind_ok h8
  obtain ⟨_, _, h11, h12⟩ := AM.bind_ok h10
  obtain ⟨rfl, -⟩ := AM.pure_ok h12
  obtain ⟨r4, _, h13, h14⟩ := AM.bind_ok h11
  obtain ⟨_, _, -, h15⟩ := AM.bind_ok h14
  obtain ⟨rfl, -⟩ := AM.pure_ok h15
  simp only [ConLeche.quotSoundA, plainCI] at h13
  obtain ⟨v, _, -, h16⟩ := AM.bind_ok h13
  obtain ⟨rfl, -⟩ := AM.pure_ok h16
  exact ⟨v, rfl⟩

/-- The quotient slots the arm checks: the type former, the constructor, the soundness axiom. -/
def QKJ (k : ConLeche.QuotKind) (j : Nat) : Prop := (k = .type ∧ j = 0) ∨ (k = .ctor ∧ j = 1) ∨ (k = .sound ∧ j = 4)

theorem quotBlk_mk {k : ConLeche.QuotKind} {j : Nat} (hkj : QKJ k j)
    {s s' : AState} {blk : List IConstantInfo} (h : plainCIList quotBasis s = .ok (blk, s')) :
    ∃ mk : IConstantVal → IConstantInfo, (∀ v, (mk v).toConstantVal = v) ∧
      blk.getD j default = mk (blk.getD j default).toConstantVal ∧
      (∀ ps, (blk.getD j default).atLps ps = (do let v ← (blk.getD j default).toConstantVal.atLps ps; pure (mk v))) ∧
      ((k = .type ∧ j = 0 ∧ mk = fun v => .indInfo v capsQ) ∨
        (k = .ctor ∧ j = 1 ∧ ∃ t, mk = fun v => .ctorInfo v 2 1 t) ∨
        (k = .sound ∧ j = 4 ∧ mk = fun v => .axiomInfo v)) := by
  rcases hkj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · obtain ⟨v, hv⟩ := quotBlk_slot0 h
    rw [hv]
    exact ⟨fun v => .indInfo v capsQ, fun _ => rfl, rfl, fun ps => rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
  · obtain ⟨v, t, hv⟩ := quotBlk_slot1 h
    rw [hv]
    exact ⟨fun v => .ctorInfo v 2 1 t, fun _ => rfl, rfl, fun ps => rfl, Or.inr (Or.inl ⟨rfl, rfl, t, rfl⟩)⟩
  · obtain ⟨v, hv⟩ := quotBlk_slot4 h
    rw [hv]
    exact ⟨fun v => .axiomInfo v, fun _ => rfl, rfl, fun ps => rfl, Or.inr (Or.inr ⟨rfl, rfl, rfl⟩)⟩

theorem cv_beq_iff (cv : IConstantVal) (n : NIdx) (t : EIdx) :
    (cv == ⟨n, cv.levelParams, t⟩) = (cv.name == n && cv.type == t) := by
  cases cv with
  | mk n' l t' =>
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq, IConstantVal.mk.injEq, Bool.and_eq_true, true_and]

set_option maxHeartbeats 4000000 in
/-- **The install, the literal flags, the flush.** -/
theorem instQcall_spec (mode : ConLeche.CheckMode) (C : Ctx) (hok : CtxOK C) (hc : QCodes mode C)
    (hpl : C.saved = none) (hg : TblGate C.fe) (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins)
    (Hr E1 : List (BitVec 64)) (hpH : C.H <+: Hr) (hpE : C.EH <+: E1)
    (s : AState) (Γ : Env) (ci : IConstantInfo) (qr ol : Nat)
    (hn : Hr[qr]? = some (Enc.idxW ci.name)) (hl : Hr[qr + 1]? = some (cellA C ol))
    (ht : Hr[qr + 2]? = some (Enc.idxW ci.toConstantVal.type))
    (hb : BlkAt Hr ol (ci.toConstantVal.levelParams.map Enc.idxW)) (hlen : ci.toConstantVal.levelParams.length < 2 ^ 60)
    (es : List (ExpHOL 64)) (tW w4 w5 w6 w7 w8 w9 : BitVec 64)
    (hes : EvAll (fun e v => sev Γ e = some v) es [tW, cellA C qr, w4, w5, w6, w7, w8, w9])
    (hcie : ∀ EH ox b, E1 <+: EH → Lay10 C EH ox b [tW, Enc.idxW ci.name, ecell C b,
      Enc.idxW ci.toConstantVal.type, w4, w5, w6, w7, w8, w9] ci → CIE C.EB EH ox ci)
    (hnew : C.fe.find? ci.name = none) (hden : NewDen ci s.store)
    (hrec : ∀ cv mI rP isK rules, ci ≠ .recInfo cv mI rP isK rules)
    (T : IFEnv → AM IFEnv) (hT : ∀ fe s', s'.pins = C.pins → T fe s' = .ok (fe, s')) :
    SpecR (σ := σ) (Inv (ctxE (ctxH C Hr) E1) s Γ [] (ctxLocals ++ kqLocals)) (callR kdX fInstQ es (tailP C)) s
      (flushCaches >>= fun _ => T (C.fe.push ci)) (PostStep C) := by
  have hokr := ctxOK_H hok Hr
  have hok1 : CtxOK (ctxE (ctxH C Hr) E1) := ctxOK_E hokr hpE
  refine specR_congr (m' := (pure (C.fe.push ci) : AM IFEnv) >>= fun fe₂ =>
    ((pure () : AM Unit) >>= fun _ => flushCaches >>= fun _ => T fe₂)) (by simp) ?_
  refine specR_callNC (C := ctxE (ctxH C Hr) E1) (D := ctxLocals ++ kqLocals) kdX fInstQ iqParams es (instQBody C)
    [tW, cellA C qr, w4, w5, w6, w7, w8, w9] (by decide) rfl (by simp [kqLocals]) hc.iq hes
    (fun a w s' st => (pure (C.fe.push ci) : AM IFEnv) s = .ok (a, s') ∧
      PostInst (ctxE (ctxH C Hr) E1) ci a w s' st)
    (fun a w s' C' => s' = s ∧ a = C.fe.push ci ∧ ∃ EH ox, C' = ctxIns (ctxE (ctxH C Hr) E1)
        ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit) EH (C.envM.insert ci.name (ecell C ox)) ∧
        E1 <+: EH ∧ CIE C.EB EH ox ci)
    (fun a w s' st ⟨hrun, ⟨EH, ox, hpE', hcie', hsr⟩⟩ => by
      simp only [pure, StateT.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at hrun
      exact ⟨_, ⟨hrun.2.symm, hrun.1.symm, EH, ox, rfl, hpE', hcie'⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu iqParams _ rfl hlk)
      (specR_run (instQ_spec (ctxE (ctxH C Hr) E1) hok1 hc.d.cp hc.d.k.s hc.d.k.i s ci qr ol hn hl ht hb hlen
        tW w4 w5 w6 w7 w8 w9 (fun EH ox b hp h => hcie EH ox b hp h) hg hnew hden hrec)))
    (fun a w s3 C3 ⟨hs3, ha, EH, ox, eC, hpE', hcie'⟩ => ?_)
  subst eC ha
  subst s3
  -- the literal flags
  set CI := ctxIns (ctxE (ctxH C Hr) E1) ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit) EH
    (C.envM.insert ci.name (ecell C ox)) with hCI
  have hokI : CtxOK CI := ctxOK_ins hok1 hpE' hcie' (pushOld_find C.fe ci) (pushOld_findTable hg ci hnew)
  have hfP : ∀ n, (C.fe.push ci).find? n = CI.fe.find? n := fun n => (IFEnv.setFlags_find? _ _ _ n).symm
  have htP : ∀ n, (C.fe.push ci).findTable? n = CI.fe.findTable? n := fun n => by
    show _ = ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit).findTable? n
    unfold IFEnv.findTable?; rw [IFEnv.setFlags_find?, IFEnv.setFlags_rawTable?]
  obtain ⟨hfn, hfs⟩ := push_flags_found (C := ctxE (ctxH C Hr) E1) hF hL ci ox EH
  refine specR_callNC (C := CI) (D := ctxLocals ++ kqLocals) kdX fFlags [] [] flBody [] (by decide) rfl
    (by simp [kqLocals]) hc.d.flags trivial (fun a w s' st => PostFl CI (C.fe.push ci) a w s' st ∧ s' = s)
    (fun _ w s' C' => s' = s ∧ ∃ H5, C' = ctxFe (ctxH CI H5) (C.fe.push ci) ∧ CI.H <+: H5)
    (fun a w s' st ⟨⟨H5, hp5, hsr⟩, hs'⟩ => ⟨_, ⟨hs', H5, rfl, hp5⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [] _ rfl hlk)
      (specR_pureState (fl_spec CI hokI hc.d.natF hc.d.strF hc.d.k.g hc.d.k.p s hfP htP hfn hfs)))
    (fun _ w s4 C4 ⟨hs4, H5, eC, hp5⟩ => ?_)
  subst eC
  subst s4
  -- the flush
  have hokF : CtxOK (ctxFe (ctxH CI H5) (C.fe.push ci)) :=
    ctxOK_fe (ctxOK_H hokI H5) (fun n => hfP n) (fun n => htP n)
  refine specR_flushTopI hokF hpl false flushCaches rfl (by simp [kqLocals]) ?_
  refine specR_atEntry fun t9 ht9 => ?_
  refine specR_congr (m' := pure (C.fe.push ci)) (hT _ _ ht9.sr.pins) ?_
  exact specR_returnI _ 0 rfl (fun t ht => ⟨EH, C.envM.insert ci.name (ecell C ox), C.tblM, H5, hpE.trans hpE',
    hpH.trans hp5, hokF, sr_of_eq ht.sr rfl rfl rfl rfl, hg.push ci, hF.push ci,
    by unfold LitsPinned; rw [IFEnv.push_base]; exact hL⟩)

set_option maxHeartbeats 4000000 in
/-- **The record at slot `j`, up to the pin match.** -/
theorem arm_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode)
    (pins : List INatOpPinSet) (C : Ctx) (hok : CtxOK C) (hc : QCodes mode C)
    (hs : C.side = false) (hpl : C.saved = none) (hg : TblGate C.fe) (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins)
    (hf : ConPanqueque.Front.FrontOK C) (hA : denoteN C.St.ns default = some .anonymous)
    (k : ConLeche.QuotKind) (j : Nat) (hkj : QKJ k j)
    (cv : IConstantVal) (q : Nat) (hrc : RecCVQ C q cv) (H0 : List (BitVec 64)) (hH0 : C.H <+: H0)
    (s : AState) (Γ : Env) (hB : Base C q Γ)
    (T : IFEnv → AM IFEnv) (hT : ∀ fe s', s'.pins = C.pins → T fe s' = .ok (fe, s')) :
    SpecR (σ := σ) (Inv (ctxH C H0) s Γ [] (ctxLocals ++ kqLocals)) (armP C j) s
      (checkQuotRecord C.fe k cv >>= fun fe₂ => flushCaches >>= fun _ => T fe₂) (PostStep C) := by
  have hj5 : j < 5 := by rcases hkj with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> decide
  have hslot : k.slot = j := by rcases hkj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  obtain ⟨ol, ks, hn, hl, ht, hb, hlen, hkl, hks, htyD⟩ := hrc
  have hD : ∀ x ∈ kqLocals, x ∈ ctxLocals ++ kqLocals := fun x hx => List.mem_append_right _ hx
  have G : GenEnv C (ctxLocals ++ kqLocals) 12 :=
    ⟨hok, hf, hA, hc.e, hD _ (by simp [kqLocals]), hD _ (by simp [kqLocals]),
      fun c hc' j hj => hD _ (List.mem_append_right _ (gv_mem_genLocals hc' hj))⟩
  have hq : ∀ x ∈ [qN, qL, qT, qU, qX], x ∈ ctxLocals ++ kqLocals := fun x hx => hD x (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [kqLocals])
  unfold checkQuotRecord quotPinHit quotPin
  simp only [bind_assoc]
  unfold armP
  refine specR_fact (fun t ht => sr_stateOK ht.sr) (fun hst0 => ?_)
  refine specR_offCheckI ⟨hD _ (by simp [kqLocals]), hD _ (by simp [kqLocals]), hD _ (by simp [kqLocals]),
    hD _ (by simp [kqLocals])⟩ (fun ho => ?_)
  refine specR_basisQuot ho ?_
  have hB0 : Base C q ((ocD, 0) :: (ocC, 0) :: (ocB, 0) :: (ocA, 0) :: Γ) :=
    base_cons (base_cons (base_cons (base_cons hB (by decide) (by decide) _) (by decide) (by decide) _)
      (by decide) (by decide) _) (by decide) (by decide) _
  refine quotSlot_spec ra G hq j hj5 (by
      intro v mI rP isK rs he
      rcases hkj with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> cases he) H0 _ _ [] s
    (fun blk s1 Γ1 H1 hp1 ag1 hr1 hP1 hX1 => ?_)
  have hB1 := base_agreeQ hB0 ag1
  simp only [pure_bind, hslot]
  obtain ⟨hPN, ⟨op, hPL, hPb⟩, hPT⟩ := hP1
  have hp01 : C.H <+: H1 := hH0.trans hp1
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN1 => ?_)
  have hHN1' : H1.length ≤ C.HN := hHN1
  have hlay := hok.heapLay
  have hpl2 : (blk.getD j default).toConstantVal.levelParams.length < 2 ^ 61 := by
    have := blkAt_len hPb
    simp only [List.length_map] at this
    omega
  unfold hitP
  refine UD.specR_heapLoadI' (C := ctxH C H1) kqRL _ (q + 1) _ (get_prefix hl hp01) (hD _ (by simp [kqLocals]))
    (by simp only [sev, sev_vv, hB1.1]; simp; exact cellA_add8 C q) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H1) kqLn (vv kqRL) ol _ (by
      have := (blkAt_mono hb hp01).1; simp only [List.length_map] at this; exact this)
    (hD _ (by simp [kqLocals])) (by simp +decide [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H1) kqPl (vv qL) op _ (by
      have := hPb.1; simp only [List.length_map] at this; exact this)
    (hD _ (by simp [kqLocals])) (by simp +decide [sev, Env.get_cons, hPL]; rfl) ?_
  refine specR_guardNe kqLn kqPl (BitVec.ofNat 64 cv.levelParams.length)
    (BitVec.ofNat 64 (blk.getD j default).toConstantVal.levelParams.length)
    (by simp +decide only [Env.get_cons, ite_true, ite_false]) (by simp +decide only [Env.get_cons, ite_true, ite_false])
    (fun hlq => ?_)
  have hlq' : cv.levelParams.length = (blk.getD j default).toConstantVal.levelParams.length := by
    have := congrArg BitVec.toNat hlq
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
  set pcv := (blk.getD j default).toConstantVal with hpcv
  -- distinct
  refine ConPanqueque.T.WC.specR_callPure (C := ctxH C H1) kdX fNdg ndgParams [vv kqRL, .const 0, vv kqLn] ndgBody
    [cellA C ol, BitVec.ofNat 64 0, BitVec.ofNat 64 cv.levelParams.length] (nameNodup (cv.levelParams.drop 0))
    (by decide) rfl (hD _ (by simp [kqLocals])) hc.d.ndg
    ⟨by simp +decide only [sev, sev_vv, Env.get_cons, ite_true, ite_false], rfl,
      by simp +decide only [sev, sev_vv, Env.get_cons, ite_true, ite_false], trivial⟩
    (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ndgParams _ rfl hlk)
      (ndg_spec C hc.d.ndh hc.d.ndg cv.levelParams ol (by omega) _ 0 H1 s1 hp01 (blkAt_mono hb hp01) rfl
        (Nat.zero_le _)))
    (fun w H2 hp2 hw => ?_)
  subst hw
  refine specR_guardZ kdX (boolW (nameNodup (List.drop 0 cv.levelParams))) (by simp only [Env.get_cons, ite_true])
    (fun hnd => ?_)
  have hnd' : nameNodup cv.levelParams = true := by
    cases e : nameNodup cv.levelParams
    · simp [e, boolW] at hnd
    · rfl
  have hcond : (nameNodup cv.levelParams && cv.levelParams.length == pcv.levelParams.length) = true := by
    simp [hnd', hlq']
  rw [if_pos hcond]
  have hp12 : H1 <+: H2 := hp2
  have hp02 : C.H <+: H2 := hp01.trans hp12
  obtain ⟨hst1, xP, hxP⟩ := quotSlot_den hst0 ho hr1 j hj5
  obtain ⟨-, hlpP, htyP⟩ := ConRon.Bridge.denoteCV_inv hxP
  unfold atLpsP IConstantVal.atLps
  simp only [bind_assoc, pure_bind]
  refine specR_fact (fun t ht => ht.sr.floor) (fun hfl1 => ?_)
  have hlpd1 : Frontend.denoteNList s1.store.ns cv.levelParams = some ks :=
    denoteNList_of_get _ _ hkl (fun j hj => denoteN_ext (hks j hj) hfl1)
  refine specR_callNIH (C := ctxH C H2) kqUs fParamLevels plParams [vv kqRL] (plBody C) [cellA C ol] (by decide) rfl
    (hD _ (by simp [kqLocals])) hc.pl ⟨by simp +decide only [sev, sev_vv, Env.get_cons, ite_true, ite_false], trivial⟩
    (fun a w s' st => paramLevels cv.levelParams s1 = .ok (a, s') ∧ PostLsH (ctxH C H2) a w s' st)
    (fun a w s' H' => paramLevels cv.levelParams s1 = .ok (a, s') ∧ w = Enc.idxW a)
    (fun a w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hr, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (fun w hw => by
      subst hw
      exact pl_spec ra C hok hc.pl hc.pf hc.ilp1 hc.e.ls cv.levelParams ol (by omega) H2 s1 (blkAt_mono hb hp02) _
        (pre_of_lookups hu plParams _ rfl hlk)))
    (fun us wu s2 H3 hp3 ⟨hr3, hwu⟩ => ?_)
  subst hwu
  have hp23 : H2 <+: H3 := hp3
  have hp03 : C.H <+: H3 := hp02.trans hp23
  obtain ⟨hs23, hus⟩ := ConRon.Bridge.paramLevels_run hst1.ok hlpd1 hr3
  have hlpP2 := denoteNList_ext hs23.ext.lss.ls.ns _ _ hlpP
  have htyP2 := denote_ext htyP hs23.ext
  refine specR_callNIH (C := ctxH C H3) kqTy fInstLPF ilpParams
    [.const (BitVec.ofNat 64 coreWalkFuel), vv qT, vv qL, vv kqUs] (ilpfBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW pcv.type, cellA C op, Enc.idxW us] (by decide) rfl
    (hD _ (by simp [kqLocals])) hc.ilpf
    ⟨rfl, by simp +decide only [sev, sev_vv, Env.get_cons, ite_true, ite_false]; exact hPT,
      by simp +decide only [sev, sev_vv, Env.get_cons, ite_true, ite_false]; exact hPL,
      by simp +decide only [sev, sev_vv, Env.get_cons, ite_true, ite_false], trivial⟩
    (PostILP (ctxH C H3)) (fun a w _ _ => w = Enc.idxW a) (fun a w s' st ⟨H'', hp, hw, hsr⟩ => ⟨H'', hp, hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ilpParams _ rfl hlk)
      (ilpf_spec ra C hok hc.ilp coreWalkFuel CV.coreWalkFuel_lt op pcv.levelParams _ us _ H3 s2 pcv.type hlpP2 hus
        (sr_stateOK hu) hu.cok.rn hu.cok.rl hu.cok.rls (by rw [htyP2]; rfl) (blkAt_mono hPb (hp12.trans hp23))))
    (fun ty wt s3 H4 hp4 hwt => ?_)
  subst hwt
  have hp34 : H3 <+: H4 := hp4
  have hp04 : C.H <+: H4 := hp03.trans hp34
  refine UD.specR_heapLoadI' (C := ctxH C H4) kdN (vv kdQ) q _ (get_prefix hn hp04) (hD _ (by simp [kqLocals]))
    (by simp +decide only [sev, sev_vv, Env.get_cons, ite_true, ite_false]; exact hB1.1) ?_
  refine specR_guardNe kdN qN (Enc.idxW cv.name) (Enc.idxW pcv.name) (by simp only [Env.get_cons, ite_true])
    (by simp +decide only [Env.get_cons, ite_true, ite_false]; exact hPN) (fun hnm => ?_)
  have hnm' : cv.name = pcv.name := Enc.idxW_inj hnm
  refine UD.specR_heapLoadI' (C := ctxH C H4) kqT2 (.op .add [vv kdQ, .const 16]) (q + 2) _ (get_prefix ht hp04)
    (hD _ (by simp [kqLocals]))
    (by simp +decide only [sev, sev_vv, Env.get_cons, ite_true, ite_false, hB1.1]; simp; exact cellA_add_ofNat C q 2) ?_
  refine specR_guardNe kqT2 kqTy (Enc.idxW cv.type) (Enc.idxW ty) (by simp only [Env.get_cons, ite_true])
    (by simp +decide only [Env.get_cons, ite_true, ite_false]) (fun hty => ?_)
  have hty' : cv.type = ty := Enc.idxW_inj hty
  have hbeq : (cv == ⟨pcv.name, cv.levelParams, ty⟩) = true := by rw [cv_beq_iff, hnm', hty']; simp
  rw [if_pos hbeq]
  simp only [bind_assoc]
  -- the slots it needs
  refine specR_atEntry fun t5 ht5 => ?_
  refine specR_runBind (quotPredsOk_run' (ctxOK_H hok H4) ht5.sr.pins k) ?_
  have hok4 := ctxOK_H hok H4
  have hrest : ∀ Γ' : Env, Base C q Γ' → Γ'.get kqRL = some (cellA C ol) →
      SpecR (σ := σ) (Inv (ctxH C H4) s3 Γ' [] (ctxLocals ++ kqLocals))
        (offCheckP C (quotSlotP C j (callR kqUs fParamLevels [vv kqRL]
          (callR kqTy fInstLPF [.const (BitVec.ofNat 64 coreWalkFuel), vv qT, vv qL, vv kqUs]
          (alloc3 C kqR (vv qN) (vv kqRL) (vv kqTy)
          (envFindP C kqF (vv qN) (.ite (.cmp .notEqual (vv kqF) (.const 0)) hang (instP C j))))))))
        s3 (do let ci ← quotAt k cv; let fe₂ ← installBasisDecl C.fe ci; flushCaches; T fe₂) (PostStep C) := by
    intro Γ' hB' hRL
    unfold quotAt quotPin
    simp only [bind_assoc]
    refine specR_fact (fun t ht => sr_stateOK ht.sr) (fun hst3 => ?_)
    refine specR_offCheckI ⟨hD _ (by simp [kqLocals]), hD _ (by simp [kqLocals]), hD _ (by simp [kqLocals]),
      hD _ (by simp [kqLocals])⟩ (fun ho3 => ?_)
    refine specR_basisQuot ho3 ?_
    have hB6 : Base C q ((ocD, 0) :: (ocC, 0) :: (ocB, 0) :: (ocA, 0) :: Γ') :=
      base_cons (base_cons (base_cons (base_cons hB' (by decide) (by decide) _) (by decide) (by decide) _)
        (by decide) (by decide) _) (by decide) (by decide) _
    refine quotSlot_spec ra G hq j hj5 (by
        intro v mI rP isK rs he
        rcases hkj with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> cases he) H4 _ _ [] s3
      (fun blk2 s4 Γ2 H5 hp5 ag2 hr2 hP2 hX2 => ?_)
    have hB7 := base_agreeQ hB6 ag2
    have hRL7 : Γ2.get kqRL = some (cellA C ol) := by
      rw [ag2 kqRL (fun c j e => gv_ne_of (m := kqRL) (by simp [kqRL, ofString]) e.symm) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide)]
      simp +decide only [Env.get_cons, ite_true, ite_false]; exact hRL
    simp only [pure_bind, hslot]
    obtain ⟨hPN2, ⟨op2, hPL2, hPb2⟩, hPT2⟩ := hP2
    have hp45 : H4 <+: H5 := hp5
    have hp05 : C.H <+: H5 := hp04.trans hp45
    obtain ⟨hst4, xP2, hxP2⟩ := quotSlot_den hst3 ho3 hr2 j hj5
    obtain ⟨-, hlpP4, htyP4⟩ := ConRon.Bridge.denoteCV_inv hxP2
    obtain ⟨mk, hmk, hp2mk, hat, hkind⟩ := quotBlk_mk hkj hr2
    set p2 := blk2.getD j default with hp2def
    rw [hat]
    unfold IConstantVal.atLps
    simp only [bind_assoc, pure_bind]
    refine specR_fact (fun t ht => ht.sr.floor) (fun hfl4 => ?_)
    have hlpd4 : Frontend.denoteNList s4.store.ns cv.levelParams = some ks :=
      denoteNList_of_get _ _ hkl (fun j hj => denoteN_ext (hks j hj) hfl4)
    refine specR_callNIH (C := ctxH C H5) kqUs fParamLevels plParams [vv kqRL] (plBody C) [cellA C ol] (by decide) rfl
      (hD _ (by simp [kqLocals])) hc.pl ⟨by simp only [sev, sev_vv, hRL7], trivial⟩
      (fun a w s' st => paramLevels cv.levelParams s4 = .ok (a, s') ∧ PostLsH (ctxH C H5) a w s' st)
      (fun a w s' H' => paramLevels cv.levelParams s4 = .ok (a, s') ∧ w = Enc.idxW a)
      (fun a w s' st ⟨hr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hr, hw⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (fun w hw => by
        subst hw
        exact pl_spec ra C hok hc.pl hc.pf hc.ilp1 hc.e.ls cv.levelParams ol (by omega) H5 s4 (blkAt_mono hb hp05) _
          (pre_of_lookups hu plParams _ rfl hlk)))
      (fun us2 wu s5 H6 hp6 ⟨hr6, hwu⟩ => ?_)
    subst hwu
    have hp56 : H5 <+: H6 := hp6
    have hp06 : C.H <+: H6 := hp05.trans hp56
    obtain ⟨hs56, hus2⟩ := ConRon.Bridge.paramLevels_run hst4.ok hlpd4 hr6
    have hlpP5 := denoteNList_ext hs56.ext.lss.ls.ns _ _ hlpP4
    have htyP5 := denote_ext htyP4 hs56.ext
    have hg6 : ∀ x, (x = qN ∨ x = qL ∨ x = qT) → Env.get ((kqUs, Enc.idxW us2) :: Γ2) x = Γ2.get x := fun x hx => by
      rw [Env.get_cons, ite_eq_right_iff.mpr (fun e => absurd e (by rcases hx with rfl | rfl | rfl <;> decide))]
    refine specR_fact (fun t ht => (⟨ht.sr.cok.rn, ht.sr.cok.rl, ht.sr.cok.rls⟩ : ConRon.Bridge.ReadOK s5))
      (fun hrd5 => ?_)
    refine specR_callNIH (C := ctxH C H6) kqTy fInstLPF ilpParams
      [.const (BitVec.ofNat 64 coreWalkFuel), vv qT, vv qL, vv kqUs] (ilpfBody C)
      [BitVec.ofNat 64 coreWalkFuel, Enc.idxW p2.toConstantVal.type, cellA C op2, Enc.idxW us2] (by decide) rfl
      (hD _ (by simp [kqLocals])) hc.ilpf
      ⟨rfl, by simp only [sev, sev_vv, hg6 qT (by simp)]; exact hPT2,
        by simp only [sev, sev_vv, hg6 qL (by simp)]; exact hPL2,
        by simp only [sev, sev_vv, Env.get_cons, ite_true], trivial⟩
      (fun a w s' st => instLPFast coreWalkFuel p2.toConstantVal.levelParams us2 p2.toConstantVal.type s5 =
        .ok (a, s') ∧ PostILP (ctxH C H6) a w s' st)
      (fun a w s' _ => instLPFast coreWalkFuel p2.toConstantVal.levelParams us2 p2.toConstantVal.type s5 =
        .ok (a, s') ∧ w = Enc.idxW a)
      (fun a w s' st ⟨hr, H'', hp, hw, hsr⟩ => ⟨H'', hp, ⟨hr, hw⟩, hsr⟩)
      (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu ilpParams _ rfl hlk)
        (ilpf_spec ra C hok hc.ilp coreWalkFuel CV.coreWalkFuel_lt op2 p2.toConstantVal.levelParams _ us2 _ H6 s5
          p2.toConstantVal.type hlpP5 hus2 (sr_stateOK hu) hu.cok.rn hu.cok.rl hu.cok.rls (by rw [htyP5]; rfl)
          (blkAt_mono hPb2 hp56))))
      (fun ty2 wt s6 H7 hp7 ⟨hr7, hwt⟩ => ?_)
    subst hwt
    obtain ⟨hs67, hty2⟩ := ConRon.Bridge.instLPFast_run hs56.ok hrd5 hlpP5 hus2 htyP5 hr7
    have hp67 : H6 <+: H7 := hp7
    have hp07 : C.H <+: H7 := hp06.trans hp67
    have hok7 := ctxOK_H hok H7
    have hN7 : Env.get ((kqTy, Enc.idxW ty2) :: (kqUs, Enc.idxW us2) :: Γ2) qN = some (Enc.idxW p2.toConstantVal.name) := by
      simp +decide only [Env.get_cons, ite_false]; exact hPN2
    refine specR_alloc3I (C := ctxH C H7) hok7 kqR (vv qN) (vv kqRL) (vv kqTy) (Enc.idxW p2.toConstantVal.name)
      (cellA C ol) (Enc.idxW ty2) (hD _ (by simp [kqLocals]))
      (fun v => by simp +decide only [sev, sev_vv, Env.get_cons, ite_false]; exact hPN2)
      (fun v => by simp +decide only [sev, sev_vv, Env.get_cons, ite_false]; exact hRL7)
      (fun v => by simp +decide only [sev, sev_vv, Env.get_cons, ite_false, ite_true])
      (fun H8 ws hp8 hws => ?_)
    obtain ⟨g0, g1, g2⟩ := img3_get H8 ws (Enc.idxW p2.toConstantVal.name) (cellA C ol) (Enc.idxW ty2) hws
    have hp8' : H7 <+: _ := hp8.trans (img3_prefix H8 ws (Enc.idxW p2.toConstantVal.name) (cellA C ol) (Enc.idxW ty2) hws)
    generalize hHr : (((H8 ++ ws).set H8.length (Enc.idxW p2.toConstantVal.name)).set (H8.length + 1) (cellA C ol)).set
      (H8.length + 2) (Enc.idxW ty2) = Hr at g0 g1 g2 hp8' ⊢
    have hokr := ctxOK_H hok Hr
    have hp0r : C.H <+: Hr := hp07.trans hp8'
    show SpecR (Inv (ctxH C Hr) _ _ _ _) (envFindP (ctxH C Hr) kqF (vv qN) _) _ _ _
    refine specR_envFindI hokr hc.d.k.g hc.d.k.p kqF (vv qN) p2.toConstantVal.name (hD _ (by simp [kqLocals]))
      (by simp +decide only [sev, sev_vv, Env.get_cons, ite_false]; exact hPN2)
      (by simp +decide only [Env.get_cons, ite_false]; exact hB7.2) ?_
    have hrel := find_rel hokr p2.toConstantVal.name
    revert hrel
    rcases hfn : (ctxH C Hr).fe.find? p2.toConstantVal.name with _ | ci0
    swap
    · intro ⟨o', hm, hci⟩
      rw [hm]
      refine specR_atEntry fun t ht => ?_
      have hoE : o' < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
      exact specR_guardNZ kqF (optWG id (some (ecell (ctxH C Hr) o'))) (by simp only [Env.get_cons, ite_true])
        (fun h => absurd h (show ecell (ctxH C Hr) o' + 1 ≠ 0 from ecell_succ_ne hokr hoE))
    intro hrel
    simp only at hrel
    rw [hrel]
    refine specR_guardNZ kqF (optWG id none) (by simp only [Env.get_cons, ite_true]) (fun _ => ?_)
    have hname : ∀ v, (mk v).name = v.name := fun v => by
      have := hmk v
      cases hmk' : mk v <;> rw [hmk'] at this <;> simp [IConstantInfo.name, IConstantInfo.toConstantVal] at this ⊢ <;>
        rw [this]
    have hnew : C.fe.find? (mk ⟨p2.toConstantVal.name, cv.levelParams, ty2⟩).name = none := by
      rw [hname]; exact hfn
    simp only [installBasisDecl, hnew, Option.isNone_none, ↓reduceIte, pure_bind]
    refine specR_fact (fun t ht => ht.sr.floor) (fun hfl6 => ?_)
    have hden : NewDen (mk ⟨p2.toConstantVal.name, cv.levelParams, ty2⟩) s6.store := by
      refine ⟨fun n hn' => ?_, ?_, ?_, fun cv' v' h' e => ?_, fun cv' caps e => ?_⟩
      · rw [hmk] at hn'
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hn'
        exact Option.isSome_iff_exists.mpr ⟨_, denoteN_ext (hks j hj) hfl6⟩
      · rw [hmk]; show (denoteE s6.store ty2).isSome = true; rw [hty2]; rfl
      · rw [hmk]; show cv.levelParams.length + 1 < 2 ^ 60; omega
      · rcases hkind with ⟨-, -, rfl⟩ | ⟨-, -, t, rfl⟩ | ⟨-, -, rfl⟩ <;> cases e
      · rcases hkind with ⟨-, -, rfl⟩ | ⟨-, -, t, rfl⟩ | ⟨-, -, rfl⟩ <;> cases e
        show 0 + 0 < 2 ^ 63; decide
    have hblk : BlkAt Hr ol (cv.levelParams.map Enc.idxW) := blkAt_mono hb hp0r
    rcases hkind with ⟨-, rfl, rfl⟩ | ⟨-, rfl, t, rfl⟩ | ⟨-, rfl, rfl⟩
    · -- the type former: an empty name block, then the record
      show SpecR _ (envAllocP (ctxH C Hr) kqE (.const 8) _) _ _ _
      refine specR_envAllocI kqE (.const 8) 1 (by decide) (hD _ (by simp [kqLocals])) (fun v => rfl)
        (fun ws1 hws1 hroom1 => ?_)
      have hj1 : C.EH.length < (C.EH ++ ws1).length := by simp; omega
      refine specR_envStoreI (C := ctxE (ctxH C Hr) (C.EH ++ ws1)) (ctxOK_E hokr (List.prefix_append _ _)) (vv kqE)
        (.const 0) C.EH.length hj1 0 (by simp only [sev, sev_vv, Env.get_cons, ite_true]; rfl) rfl ?_
      have hz : ((C.EH ++ ws1).set C.EH.length 0)[C.EH.length]? = some 0 := List.getElem?_set_self hj1
      show SpecR (Inv (ctxE (ctxH C Hr) ((C.EH ++ ws1).set C.EH.length 0)) _ _ _ _) _ _ _ _
      refine instQcall_spec mode C hok hc hpl hg hF hL Hr _ hp0r (prefix_set_ge (List.prefix_append _ _) _ (le_refl _) _)
        s6 _ (.indInfo ⟨p2.toConstantVal.name, cv.levelParams, ty2⟩ capsQ) H8.length ol g0 g1 g2 hblk
        (by show cv.levelParams.length < 2 ^ 60; omega)
        [.const 3, vv kqR, .const 0, vv kqE, .const 0, .const 0, vv kqE, .const 0] 3 0 (ecell C C.EH.length)
        0 0 (ecell C C.EH.length) 0
        ⟨rfl, by simp +decide only [sev, sev_vv, Env.get_cons, ite_true, ite_false]; rfl, rfl,
          by simp only [sev, sev_vv, Env.get_cons, ite_true]; rfl, rfl, rfl,
          by simp only [sev, sev_vv, Env.get_cons, ite_true]; rfl, rfl, trivial⟩
        (fun EH ox b hpE hlay => ?_) hnew hden (fun _ _ _ _ _ e => by cases e) T hT
      obtain ⟨h1, h2, h3, hw, hbl⟩ := hlay
      have hz' : EH[C.EH.length]? = some 0 := get_prefix hz hpE
      refine ⟨⟨h1, ⟨ecell C b, h2, b, rfl, hbl⟩, h3⟩, hw 0 (by simp), by simpa [boolW, capsQ] using hw 4 (by simp),
        ⟨_, hw 5 (by simp), C.EH.length, rfl, by simpa [capsQ] using hz', fun i hi => by simp [capsQ] at hi⟩,
        ⟨by simpa [capsQ] using hw 6 (by simp), by decide⟩, ⟨by simpa [capsQ] using hw 7 (by simp), by decide⟩,
        ⟨_, hw 8 (by simp), C.EH.length, rfl, by simpa [capsQ] using hz', fun i hi => by simp [capsQ] at hi⟩,
        by simpa [boolW, capsQ] using hw 9 (by simp)⟩
    · -- the constructor
      have hx2 : Γ2.get qX = some (Enc.idxW t) := hX2 _ 2 1 t hp2mk
      show SpecR (Inv (ctxE (ctxH C Hr) C.EH) _ _ _ _) _ _ _ _
      refine instQcall_spec mode C hok hc hpl hg hF hL Hr C.EH hp0r (List.prefix_refl _)
        s6 _ (.ctorInfo ⟨p2.toConstantVal.name, cv.levelParams, ty2⟩ 2 1 t) H8.length ol g0 g1 g2 hblk
        (by show cv.levelParams.length < 2 ^ 60; omega)
        [.const 4, vv kqR, .const 2, .const 1, vv qX, .const 0, .const 0, .const 0] 4 2 1 (Enc.idxW t) 0 0 0
        ⟨rfl, by simp +decide only [sev, sev_vv, Env.get_cons, ite_true, ite_false]; rfl, rfl, rfl,
          by simp +decide only [sev, sev_vv, Env.get_cons, ite_true, ite_false]; exact hx2, rfl, rfl, rfl, trivial⟩
        (fun EH ox b hpE hlay => ?_) hnew hden (fun _ _ _ _ _ e => by cases e) T hT
      obtain ⟨h1, h2, h3, hw, hbl⟩ := hlay
      exact ⟨⟨h1, ⟨ecell C b, h2, b, rfl, hbl⟩, h3⟩, hw 0 (by simp), ⟨hw 4 (by simp), by decide⟩,
        ⟨hw 5 (by simp), by decide⟩, hw 6 (by simp)⟩
    · -- the soundness axiom
      show SpecR (Inv (ctxE (ctxH C Hr) C.EH) _ _ _ _) _ _ _ _
      refine instQcall_spec mode C hok hc hpl hg hF hL Hr C.EH hp0r (List.prefix_refl _)
        s6 _ (.axiomInfo ⟨p2.toConstantVal.name, cv.levelParams, ty2⟩) H8.length ol g0 g1 g2 hblk
        (by show cv.levelParams.length < 2 ^ 60; omega)
        [.const 0, vv kqR, .const 0, .const 0, .const 0, .const 0, .const 0, .const 0] 0 0 0 0 0 0 0
        ⟨rfl, by simp +decide only [sev, sev_vv, Env.get_cons, ite_true, ite_false]; rfl, rfl, rfl, rfl, rfl, rfl,
          rfl, trivial⟩
        (fun EH ox b hpE hlay => ?_) hnew hden (fun _ _ _ _ _ e => by cases e) T hT
      obtain ⟨h1, h2, h3, hw, hbl⟩ := hlay
      exact ⟨⟨h1, ⟨ecell C b, h2, b, rfl, hbl⟩, h3⟩, hw 0 (by simp)⟩
  have hB5 : Base C q ((kqT2, Enc.idxW cv.type) :: (kdN, Enc.idxW cv.name) :: (kqTy, Enc.idxW ty) ::
      (kqUs, Enc.idxW us) :: (kdX, boolW (nameNodup (List.drop 0 cv.levelParams))) ::
      (kqPl, BitVec.ofNat 64 pcv.levelParams.length) :: (kqLn, BitVec.ofNat 64 cv.levelParams.length) ::
      (kqRL, cellA C ol) :: Γ1) := by
    refine base_cons (base_cons (base_cons (base_cons (base_cons (base_cons (base_cons (base_cons hB1 ?_ ?_ _) ?_ ?_ _)
      ?_ ?_ _) ?_ ?_ _) ?_ ?_ _) ?_ ?_ _) ?_ ?_ _) ?_ ?_ _ <;> decide
  rcases hkj with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · show SpecR _ (predGuard (ctxH C H4) PIN_EQ _) _ _ _
    refine specR_predGuardI hok4 hc.d.k.g hc.d.k.p PIN_EQ (by decide) (hD _ (by simp [kqLocals])) hB5.2
      (fun w w' hfind => ?_)
    have e : predB (ctxH C H4) .type = true := hfind
    rw [e, if_pos rfl]
    simp only [bind_assoc]
    refine hrest _ (base_cons (base_cons hB5 (by decide) (by decide) _) (by decide) (by decide) _)
      (by simp +decide only [Env.get_cons, ite_true, ite_false])
  · show SpecR _ (predGuard (ctxH C H4) PIN_QUOT _) _ _ _
    refine specR_predGuardI hok4 hc.d.k.g hc.d.k.p PIN_QUOT (by decide) (hD _ (by simp [kqLocals])) hB5.2
      (fun w w' hfind => ?_)
    have e : predB (ctxH C H4) .ctor = true := hfind
    rw [e, if_pos rfl]
    simp only [bind_assoc]
    refine hrest _ (base_cons (base_cons hB5 (by decide) (by decide) _) (by decide) (by decide) _)
      (by simp +decide only [Env.get_cons, ite_true, ite_false])
  · show SpecR _ (predGuard (ctxH C H4) PIN_EQ (predGuard (ctxH C H4) PIN_QUOT (predGuard (ctxH C H4) PIN_QUOT_MK _)))
      _ _ _
    refine specR_predGuardI hok4 hc.d.k.g hc.d.k.p PIN_EQ (by decide) (hD _ (by simp [kqLocals])) hB5.2
      (fun w w' h1 => ?_)
    refine specR_predGuardI hok4 hc.d.k.g hc.d.k.p PIN_QUOT (by decide) (hD _ (by simp [kqLocals]))
      (by simp +decide only [Env.get_cons, ite_false]; exact hB5.2) (fun w2 w2' h2 => ?_)
    refine specR_predGuardI hok4 hc.d.k.g hc.d.k.p PIN_QUOT_MK (by decide) (hD _ (by simp [kqLocals]))
      (by simp +decide only [Env.get_cons, ite_false]; exact hB5.2) (fun w3 w3' h3 => ?_)
    have e : predB (ctxH C H4) .sound = true := by
      show ((_ && _) && _) = true; simp only [Bool.and_eq_true]; exact ⟨⟨h1, h2⟩, h3⟩
    rw [e, if_pos rfl]
    simp only [bind_assoc]
    refine hrest _ (base_cons (base_cons (base_cons (base_cons (base_cons (base_cons hB5 (by decide) (by decide) _)
      (by decide) (by decide) _) (by decide) (by decide) _) (by decide) (by decide) _) (by decide) (by decide) _)
      (by decide) (by decide) _) (by simp +decide only [Env.get_cons, ite_true, ite_false])

set_option maxHeartbeats 4000000 in
/-- **`checkDecl` at a quotient record**: the type former and the constructor; the recursors hang. -/
theorem kq_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode)
    (pins : List INatOpPinSet) (C : Ctx) (hok : CtxOK C) (hc : QCodes mode C)
    (hs : C.side = false) (hpl : C.saved = none) (hg : TblGate C.fe) (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins)
    (hf : ConPanqueque.Front.FrontOK C) (hA : denoteN C.St.ns default = some .anonymous)
    (k : ConLeche.QuotKind) (cv : IConstantVal) (q : Nat) (hrc : RecCVQ C q cv) (s : AState) :
    SpecR (σ := σ) (Pre C s (kdParams.zip [cellA C q, BitVec.ofNat 64 (qkN k), 0])) (kqBody C) s
      (checkDecl mode pins C.fe (.quotDecl k cv)) (PostStep C) := by
  refine specR_prologue (postStep_locals C) (kq_none C _) ?_
  have hB0 : Base C q (ctxEnv C ++ kdParams.zip [cellA C q, BitVec.ofNat 64 (qkN k), 0]) :=
    ⟨by simp +decide [Env.get, kdParams, ctxEnv], by simp +decide [Env.get, kdParams, ctxEnv]⟩
  have hV : (ctxEnv C ++ kdParams.zip [cellA C q, BitVec.ofNat 64 (qkN k), 0]).get kdV =
      some (BitVec.ofNat 64 (qkN k)) := by simp +decide [Env.get, kdParams, ctxEnv]
  rw [checkDecl_quot]
  have hT : ∀ (fe : IFEnv) (s' : AState), s'.pins = C.pins → (pure fe : AM IFEnv) s' = .ok (fe, s') :=
    fun _ _ _ => rfl
  cases k with
  | type =>
    refine specR_ifI _ 1 (by simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, qkN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact arm_spec ra mode pins C hok hc hs hpl hg hF hL hf hA .type 0 (Or.inl ⟨rfl, rfl⟩) cv q hrc C.H
      (List.prefix_refl _) s _ hB0 pure hT
  | ctor =>
    refine specR_ifI _ 0 (by simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, qkN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, qkN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact arm_spec ra mode pins C hok hc hs hpl hg hF hL hf hA .ctor 1 (Or.inr (Or.inl ⟨rfl, rfl⟩)) cv q hrc C.H
      (List.prefix_refl _) s _ hB0 pure hT
  | sound =>
    refine specR_ifI _ 0 (by simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, qkN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, qkN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, qkN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    exact arm_spec ra mode pins C hok hc hs hpl hg hF hL hf hA .sound 4 (Or.inr (Or.inr ⟨rfl, rfl⟩)) cv q hrc C.H
      (List.prefix_refl _) s _ hB0 pure hT
  | lift | ind =>
    refine specR_ifI _ 0 (by simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, qkN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, qkN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    exact specR_ifI _ 0 (by simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, qkN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => specR_hangI)

end

end ConPanqueque.T.Quot

namespace ConPanqueque.T.Quot

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Decl

/-- What `checkDecl` runs after the check at an axiom record: the reserved names. -/
def soundTail (cv : IConstantVal) (fe₂ : IFEnv) : AM IFEnv := do
  if ← basisNamesOk (.axiomDecl cv) then pure fe₂ else fail (← basisNamesError (.axiomDecl cv))

theorem soundTail_run {C : Ctx} (hok : CtxOK C) (cv : IConstantVal)
    (hq : cv.name = C.pins.names[PIN_QUOT_SOUND]!) (fe : IFEnv) (s : AState) (hp : s.pins = C.pins) :
    soundTail cv fe s = .ok (fe, s) := by
  simp only [soundTail, basisNamesOk, pinQuotSound, bind_assoc]
  rw [bind_run_of (pinAt_run hok hp _ (by decide))]
  simp [hq, bind, StateT.bind, Except.bind, pure, StateT.pure, Except.pure]

theorem checkDecl_sound {C : Ctx} (hok : CtxOK C) (mode : ConLeche.CheckMode) (pins : List INatOpPinSet)
    (cv : IConstantVal) (hq : cv.name = C.pins.names[PIN_QUOT_SOUND]!) (s : AState) (hp : s.pins = C.pins) :
    checkDecl mode pins C.fe (.axiomDecl cv) s =
      (checkQuotRecord C.fe .sound cv >>= fun fe₂ => flushCaches >>= fun _ => soundTail cv fe₂) s := by
  simp only [checkDecl, checkDeclKind, pinQuotSound, bind_assoc]
  rw [bind_run_of (pinAt_run hok hp _ (by decide))]
  simp only [hq, beq_self_eq_true, ite_true]
  rfl

section
variable {σ : Type}

set_option maxHeartbeats 4000000 in
/-- **`checkDecl` at the `Quot.sound` axiom record**: kind word `5`, the soundness slot. -/
theorem kqSound_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode)
    (pins : List INatOpPinSet) (C : Ctx) (hok : CtxOK C) (hc : QCodes mode C)
    (hs : C.side = false) (hpl : C.saved = none) (hg : TblGate C.fe) (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins)
    (hf : ConPanqueque.Front.FrontOK C) (hA : denoteN C.St.ns default = some .anonymous)
    (cv : IConstantVal) (hq : cv.name = C.pins.names[PIN_QUOT_SOUND]!) (q : Nat) (hrc : RecCVQ C q cv) (s : AState) :
    SpecR (σ := σ) (Pre C s (kdParams.zip [cellA C q, BitVec.ofNat 64 5, 0])) (kqBody C) s
      (checkDecl mode pins C.fe (.axiomDecl cv)) (PostStep C) := by
  refine specR_prologue (postStep_locals C) (kq_none C _) ?_
  refine specR_atEntry fun t0 ht0 => ?_
  refine specR_congr (checkDecl_sound hok mode pins cv hq s ht0.sr.pins) ?_
  have hB0 : Base C q (ctxEnv C ++ kdParams.zip [cellA C q, BitVec.ofNat 64 5, 0]) :=
    ⟨by simp +decide [Env.get, kdParams, ctxEnv], by simp +decide [Env.get, kdParams, ctxEnv]⟩
  refine specR_ifI _ 0 (by simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_ifI _ 0 (by simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_ifI _ 1 (by simp +decide [sev, sev_vv, Env.get, kdParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun _ => ?_) (fun h => absurd h (by decide))
  exact arm_spec ra mode pins C hok hc hs hpl hg hF hL hf hA .sound 4 (Or.inr (Or.inr ⟨rfl, rfl⟩)) cv q hrc C.H
    (List.prefix_refl _) s _ hB0 (soundTail cv) (fun fe s' hp => soundTail_run hok cv hq fe s' hp)

end

end ConPanqueque.T.Quot
