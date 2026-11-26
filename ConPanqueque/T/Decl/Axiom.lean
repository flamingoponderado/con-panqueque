import ConPanqueque.T.Decl.StepDefn

/-!
# `checkDecl` at an axiom

The port takes the axiom records the twin installs without a further check: `sorryAx` (the record is
skipped, the environment unchanged). `Quot.sound` and the standard and compiler-trust axioms (`propext`,
`Classical.choice`, `Lean.trustCompiler`, `Lean.ofReduceNat`, `Lean.ofReduceBool`) hang, as does every
other axiom (which the twin declines). Past the name tests: the front door (`checkConstantVal` at
`(false, false, true)`), the flush, and the reserved names.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC
open ConPanqueque.V.Enc

def fKa := ofString "checkAxiom"

/-- The name at `kdN` against pin `i`: equal hangs. -/
def pinGuard (C : Ctx) (i : Nat) (rest : ProgHOL 64) : ProgHOL 64 :=
  .seq (.assign .local kdL (.load .one (.const (ecell C (C.PO + i)))))
    (.ite (.cmp .equal (vv kdN) (vv kdL)) hang rest)

/-- `checkDecl` at an axiom (its constant value at `kdQ`). -/
def kaBody (C : Ctx) : ProgHOL 64 := prologue kdLocals
  (.seq (.assign .local kdN (.load .one (vv kdQ)))
  (pinGuard C PIN_QUOT_SOUND
  (callR kdX fCcv [vv kdQ, .const 0, .const 0, .const 1]
  (pinGuard C PIN_PROPEXT (pinGuard C PIN_CHOICE (pinGuard C PIN_TRUST_COMPILER
  (pinGuard C PIN_OF_REDUCE_NAT (pinGuard C PIN_OF_REDUCE_BOOL
  (.seq (.assign .local kdL (.load .one (.const (ecell C (C.PO + PIN_SORRY_AX)))))
  (.ite (.cmp .notEqual (vv kdN) (vv kdL)) hang
  (flushCode C (flushRegions false)
  (.seq (.assign .local kdL (.load .one (.const (ecell C (C.PO + pinCount + 4)))))
  (.seq (.assign .local kdLn (.load .one (vv kdL)))
  (callR kdX fRsm [vv kdN, vv kdL, .const 0, vv kdLn]
  (.ite (.cmp .notEqual (vv kdX) (.const 0)) rejectP (.return (.const 0)))))))))))))))))

section
variable {σ : Type}

/-- Past the front door, at `sorryAx` (no other pinned axiom name): the environment unchanged. -/
theorem axTail_run (fe : IFEnv) (cv : IConstantVal) (s : AState) (P : Pins) (hp : s.pins = P)
    (hsz : pinCount ≤ P.names.size)
    (h1 : cv.name ≠ P.names[PIN_PROPEXT]'(by unfold pinCount at hsz; unfold PIN_PROPEXT; omega))
    (h2 : cv.name ≠ P.names[PIN_CHOICE]'(by unfold pinCount at hsz; unfold PIN_CHOICE; omega))
    (h3 : cv.name ≠ P.names[PIN_TRUST_COMPILER]'(by unfold pinCount at hsz; unfold PIN_TRUST_COMPILER; omega))
    (h4 : cv.name ≠ P.names[PIN_OF_REDUCE_NAT]'(by unfold pinCount at hsz; unfold PIN_OF_REDUCE_NAT; omega))
    (h5 : cv.name ≠ P.names[PIN_OF_REDUCE_BOOL]'(by unfold pinCount at hsz; unfold PIN_OF_REDUCE_BOOL; omega))
    (h6 : cv.name = P.names[PIN_SORRY_AX]'(by unfold pinCount at hsz; unfold PIN_SORRY_AX; omega)) :
    (do
      if ← stdAxiomOk fe cv then pure (fe.push (.axiomInfo cv))
      else if cv.name == (← trustCompilerName) then
        if ← trustCompilerOk fe cv then pure (fe.push (.axiomInfo cv))
        else fail (.notImplemented "unsupported Lean.trustCompiler shape")
      else if cv.name == (← ofReduceNatName) || cv.name == (← ofReduceBoolName) then
        if ← ofReduceAxOk fe cv then pure (fe.push (.axiomInfo cv))
        else fail (.notImplemented "unsupported compiler-trust axiom environment")
      else if cv.name == (← propextName) || cv.name == (← choiceName) then
        fail (.notImplemented "standard axiom shape mismatch")
      else if cv.name == (← pinSorryAx) then pure fe
      else fail (.notImplemented (ConLeche.nonStdAxiomMsg (← readNameM cv.name))) : AM IFEnv) s = .ok (fe, s) := by
  subst hp
  have hl : ∀ i, i < pinCount → i < s.pins.names.size := fun i hi => by omega
  have e1 : (cv.name == s.pins.names[PIN_PROPEXT]'(hl _ (by decide))) = false := by simpa using h1
  have e2 : (cv.name == s.pins.names[PIN_CHOICE]'(hl _ (by decide))) = false := by simpa using h2
  have e3 : (cv.name == s.pins.names[PIN_TRUST_COMPILER]'(hl _ (by decide))) = false := by simpa using h3
  have e4 : (cv.name == s.pins.names[PIN_OF_REDUCE_NAT]'(hl _ (by decide))) = false := by simpa using h4
  have e5 : (cv.name == s.pins.names[PIN_OF_REDUCE_BOOL]'(hl _ (by decide))) = false := by simpa using h5
  have e6 : (cv.name == s.pins.names[PIN_SORRY_AX]'(hl _ (by decide))) = true := by simp [h6]
  simp only [stdAxiomOk, propextName, choiceName, trustCompilerName, ofReduceNatName, ofReduceBoolName,
    pinPropext, pinChoice, pinTrustCompiler, pinOfReduceNat, pinOfReduceBool, pinSorryAx, pinAt]
  simp [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, Except.bind, Except.pure,
    hl _ (by decide : PIN_PROPEXT < pinCount), hl _ (by decide : PIN_CHOICE < pinCount),
    hl _ (by decide : PIN_TRUST_COMPILER < pinCount), hl _ (by decide : PIN_OF_REDUCE_NAT < pinCount),
    hl _ (by decide : PIN_OF_REDUCE_BOOL < pinCount), hl _ (by decide : PIN_SORRY_AX < pinCount), e1, e2, e3, e4, e5, e6]

/-- An equality test of two name handles. -/
theorem cmpEq_idxW_t {a b : NIdx} (h : a = b) :
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal (Enc.idxW a) (Enc.idxW b) = true := by
  subst h; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem cmpEq_idxW_f {a b : NIdx} (h : a ≠ b) :
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL .equal (Enc.idxW a) (Enc.idxW b) = false := by
  have : Enc.idxW a ≠ Enc.idxW b := fun e => h (idxW_inj e)
  simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]

theorem cmpNe_idxW_t {a b : NIdx} (h : a ≠ b) :
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL .notEqual (Enc.idxW a) (Enc.idxW b) = true := by
  have : Enc.idxW a ≠ Enc.idxW b := fun e => h (idxW_inj e)
  simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL, this]

theorem cmpNe_idxW_f {a b : NIdx} (h : a = b) :
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL .notEqual (Enc.idxW a) (Enc.idxW b) = false := by
  subst h; simp [Flapjack.Compiler.Encoders.Asm.wordCmpHOL]

theorem bind_run_of {α β : Type} {A : AM α} {K : α → AM β} {s s' : AState} {a : α} (h : A s = .ok (a, s')) :
    (A >>= K) s = K a s' := by
  simp [bind, StateT.bind, h, Except.bind]

set_option maxHeartbeats 2000000 in
/-- **`checkDecl` at an axiom**: `sorryAx` passes with the environment unchanged; the other pinned axiom
names hang. -/
theorem ka_spec (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (C : Ctx) (hok : CtxOK C)
    (hc : DeclCodes mode C) (ra : ConPanqueque.Hash.RuntimeAssumptions) (hs : C.side = false)
    (hpl : C.saved = none) (hg : TblGate C.fe) (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins)
    (cv : IConstantVal) (wv : BitVec 64) (q o : Nat)
    (hn : C.H[q]? = some (Enc.idxW cv.name)) (hl : C.H[q + 1]? = some (cellA C o))
    (ht : C.H[q + 2]? = some (Enc.idxW cv.type)) (hb : BlkAt C.H o (cv.levelParams.map Enc.idxW))
    (hlen : cv.levelParams.length < 2 ^ 59) (ks : List ConLeche.Name) (hkl : ks.length = cv.levelParams.length)
    (hks : ∀ j (hj : j < cv.levelParams.length), denoteN C.St.ns cv.levelParams[j] = some (ks[j]'(by omega)))
    (s : AState) :
    SpecR (σ := σ) (Pre C s (kdParams.zip [cellA C q, wv, 0])) (kaBody C) s
      (checkDecl mode pins C.fe (.axiomDecl cv)) (PostStep C) := by
  refine specR_prologue (postStep_locals C) (kd_none C _) ?_
  unfold checkDecl checkDeclKind
  dsimp only
  simp only [bind_assoc]
  refine UD.specR_heapLoadI' (C := C) kdN _ q _ hn (by decide) (by simp +decide [Env.get, kdParams, ctxEnv]) ?_
  unfold pinGuard pinQuotSound
  refine specR_pinAtI hok PIN_QUOT_SOUND (by decide) kdL (by decide) ?_
  by_cases hq : cv.name = C.pins.names[PIN_QUOT_SOUND]'(by rw [hok.pinsRel.1]; decide)
  · exact specR_ifI _ 1 (by simp +decide [sev, Env.get]; exact cmpEq_idxW_t hq) (fun _ => specR_hangI)
      (fun h => absurd h (by decide))
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get]; exact cmpEq_idxW_f hq) (fun h => absurd rfl h) (fun _ => ?_)
  rw [ite_bindM, ite_eq_right_iff.mpr (fun h => absurd (by simpa using h) hq)]
  simp only [bind_assoc]
  -- the front door
  refine specR_callNIH (C := C) kdX fCcv ccvParams [vv kdQ, .const 0, .const 0, .const 1] (ccvBody C)
    [cellA C q, boolW false, boolW false, boolW true] (by decide) rfl (by decide) hc.ccv
    ⟨(by simp +decide [Env.get, kdParams, ctxEnv]), rfl, rfl, rfl, trivial⟩
    (fun a w s' st => checkConstantVal mode C.fe cv false false true s = .ok (a, s') ∧ PostU C a w s' st)
    (fun a w s' H' => checkConstantVal mode C.fe cv false false true s = .ok (a, s'))
    (fun a w s' st ⟨hrun, H', hp', hsr⟩ => ⟨H', hp', hrun, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ccvParams _ rfl hlk)
      (specR_run (ccv_full mode C hok hc.k.g hc.k.p hc.pim ra hs hc.k hc.ac hc.lso hc.lsoc hc.ndh hc.ndg hc.lbb hc.cB
        hc.bvb hc.hf hc.cF hc.fvb hc.atc hc.al hc.crff hc.crf hc.ens C.fe rfl cv false false true q o hn hl ht hb
        (by omega) ks hkl hks s)))
    (fun _ w s1 H1 hp1' _ => ?_)
  have hok1 := ctxOK_H hok H1
  have hsz : PIN_SORRY_AX < C.pins.names.size := by rw [hok.pinsRel.1]; decide
  -- the pinned axiom names
  have guard : ∀ (i : Nat) (hi : i < pinCount) (Γ : Env) (rest : ProgHOL 64) {β : Type} {m : AM β}
      {R : β → BitVec 64 → AState → PState σ → Prop},
      (cv.name ≠ C.pins.names[i]'(by rw [hok.pinsRel.1]; exact hi) →
        SpecR (Inv (ctxH C H1) s1 ((kdL, Enc.idxW (C.pins.names[i]'(by rw [hok.pinsRel.1]; exact hi))) :: Γ) []
          (ctxLocals ++ kdLocals)) rest s1 m R) →
      Γ.get kdN = some (Enc.idxW cv.name) →
      SpecR (Inv (ctxH C H1) s1 Γ [] (ctxLocals ++ kdLocals)) (pinGuard C i rest) s1 m R := by
    intro i hi Γ rest β m R hk hN
    have hi' : i < C.pins.names.size := by rw [hok.pinsRel.1]; exact hi
    refine specR_envLoadI (C := ctxH C H1) kdL _ (C.PO + i) _ (by decide) rfl (hok1.pinsRel.2.1 i hi') ?_
    by_cases he : cv.name = C.pins.names[i]
    · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hN, ctxH, cmpEq_idxW_t he])
        (fun _ => specR_hangI) (fun h => absurd h (by decide))
    · exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hN, ctxH, cmpEq_idxW_f he])
        (fun h => absurd rfl h) (fun _ => hk he)
  refine guard PIN_PROPEXT (by decide) _ _ (fun h1 => ?_) (by simp +decide [Env.get_cons])
  refine guard PIN_CHOICE (by decide) _ _ (fun h2 => ?_) (by simp +decide [Env.get_cons])
  refine guard PIN_TRUST_COMPILER (by decide) _ _ (fun h3 => ?_) (by simp +decide [Env.get_cons])
  refine guard PIN_OF_REDUCE_NAT (by decide) _ _ (fun h4 => ?_) (by simp +decide [Env.get_cons])
  refine guard PIN_OF_REDUCE_BOOL (by decide) _ _ (fun h5 => ?_) (by simp +decide [Env.get_cons])
  -- `sorryAx`
  refine specR_envLoadI (C := ctxH C H1) kdL _ (C.PO + PIN_SORRY_AX) _ (by decide) rfl (hok1.pinsRel.2.1 _ hsz) ?_
  by_cases h6 : cv.name = C.pins.names[PIN_SORRY_AX]
  swap
  · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ctxH, cmpNe_idxW_t h6]) (fun _ => specR_hangI)
      (fun h => absurd h (by decide))
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, ctxH, cmpNe_idxW_f h6]) (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_atEntry fun t1 ht1 => ?_
  have hp1 : s1.pins = C.pins := ht1.sr.pins
  have hr := axTail_run C.fe cv s1 C.pins hp1 (by rw [hok.pinsRel.1]) h1 h2 h3 h4 h5 h6
  refine specR_congr (m' := (do
      flushCaches
      let b ← basisNamesOk (IDeclaration.axiomDecl cv)
      if b = true then pure C.fe else do
        let e ← basisNamesError (IDeclaration.axiomDecl cv)
        fail e)) ?_ ?_
  · rw [← bind_assoc]
    exact bind_run_of hr
  -- the flush
  refine specR_flushTopI hok1 hpl false flushCaches rfl (by decide) ?_
  -- the reserved names
  refine specR_atEntry fun t4 ht4 => ?_
  have hp4 : (flushedS false s1).pins = C.pins := ht4.sr.pins
  have hqs : PIN_QUOT_SOUND < C.pins.names.size := by rw [hok.pinsRel.1]; decide
  have hb4 : basisNamesOk (.axiomDecl cv) (flushedS false s1) =
      .ok (!C.pins.reserved.contains cv.name, flushedS false s1) := by
    have hq' : (cv.name == C.pins.names[PIN_QUOT_SOUND]) = false := by simpa using hq
    have hu := basisUnres_run hok1 hp4 cv.name
    simp only [basisNamesOk, pinQuotSound, pinAt]
    simp only [bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, Except.bind, pure, StateT.pure, Except.pure]
    simp only [hp4, hqs, dite_true, StateT.pure, pure, Except.pure]
    simp only [hq', Bool.false_eq_true, if_false]
    exact hu
  refine specR_runBind hb4 ?_
  obtain ⟨wR, hwR, oR, hwoR, hblkR⟩ := hok1.pinsRel.2.2.2.2.2.2
  have hblkR' : EBlk C.EH oR (C.pins.reserved.map Enc.idxW) := hblkR
  refine specR_envLoadI kdL _ (C.PO + pinCount + 4) wR (by decide) rfl hwR ?_
  have hlR : (ctxH C H1).EH[oR]? = some (BitVec.ofNat 64 C.pins.reserved.length) := by
    have h := hblkR'.1; simp only [List.length_map] at h; exact h
  refine specR_envLoadI kdLn (vv kdL) oR _ (by decide) (by simp [Env.get, hwoR]; rfl) hlR ?_
  refine specR_atEntry fun t5 ht5 => ?_
  have hlenR : C.pins.reserved.length < 2 ^ 62 := by
    have hl2 : C.EH.length ≤ C.EN := ht5.sr.env.1.len
    have hlay : C.EB.toNat + 8 * C.EN + 8 < 2 ^ 64 := hok1.envLay
    rcases Nat.eq_zero_or_pos C.pins.reserved.length with h0 | hpos
    · omega
    · have h1 := hblkR'.2 (C.pins.reserved.length - 1) (by simp; omega)
      have hlt : oR + 1 + (C.pins.reserved.length - 1) < C.EH.length := (List.getElem?_eq_some_iff.mp h1).1
      omega
  refine specR_callPure (C := ctxH C H1) kdX fRsm rmParams
    [vv kdN, vv kdL, .const 0, vv kdLn] rsmBody
    [Enc.idxW cv.name, ecell C oR, BitVec.ofNat 64 0, BitVec.ofNat 64 C.pins.reserved.length]
    (C.pins.reserved.contains cv.name) (by decide) rfl (by decide) hc.rsm
    ⟨by simp +decide [Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, kdParams, ctxEnv], by simp [Env.get, hwoR]; rfl,
      rfl, by simp +decide [Env.get], trivial⟩
    (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b)
    (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rmParams _ rfl hlk)
      (rsm_spec (ctxH C H1) hc.rsm C.pins.reserved oR hblkR' hlenR cv.name _ _ 0
        (ctxH C H1).H (List.prefix_refl _) rfl (Nat.zero_le _)))
    (fun w H6 hp6 hw => ?_)
  subst hw
  refine specR_failIteF (c := !C.pins.reserved.contains cv.name) _ (boolW (C.pins.reserved.contains cv.name))
    (by simp +decide [sev, Env.get]; exact nez_b _)
    (fun h => by
      have e : C.pins.reserved.contains cv.name = false := by simpa using h
      rw [e]; rfl)
    (fun h => by
      have e : C.pins.reserved.contains cv.name = true := by simpa using h
      rw [e]; decide) (fun _ => ?_)
  exact specR_returnI _ 0 rfl (fun t ht => ⟨C.EH, C.envM, C.tblM, H6, List.prefix_refl _,
    hp1'.trans hp6, ctxOK_H hok H6, sr_of_eq ht.sr rfl rfl rfl rfl, hg, hF, hL⟩)

end

end ConPanqueque.T.Decl
