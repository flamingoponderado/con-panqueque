import ConPanqueque.T.Decl.StepRuns
import ConPanqueque.T.Ind.IndArm2
import ConPanqueque.T.Decl.Axiom
import ConPanqueque.T.Quot.KqSpec
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

/-!
# One record of the fold: `checkDeclStep`

The record's declaration is encoded in the value heap at `o`: its kind word, then its constant value (name,
level-parameter block, type), then the kind's fields (value, hint). Definitions, theorems and opaques are
checked in full; any other kind stops (its check is not ported yet).
-/

namespace ConPanqueque.T.Decl

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.Big ConPanqueque.T.WC
open ConPanqueque.V.Enc

/-- A record's constant value in the value heap at `q`, with what the front door and the install need. -/
def RecCV (C : Ctx) (q : Nat) (cv : IConstantVal) : Prop :=
  ∃ (ol : Nat) (ks : List ConLeche.Name), C.H[q]? = some (Enc.idxW cv.name) ∧ C.H[q + 1]? = some (cellA C ol) ∧
    C.H[q + 2]? = some (Enc.idxW cv.type) ∧ BlkAt C.H ol (cv.levelParams.map Enc.idxW) ∧
    cv.levelParams.length < 2 ^ 59 ∧ ∃ hkl : ks.length = cv.levelParams.length,
    (∀ j (hj : j < cv.levelParams.length), denoteN C.St.ns cv.levelParams[j] = some (ks[j]'(by omega))) ∧
    (denoteE C.St cv.type).isSome = true

/-- The inductive step's facts about the twin and the store floor (not code), at the record's block. -/
structure IndSem (C : Ctx) (block : List IConstantInfo) (nP : Nat) : Prop where
  fr : ConPanqueque.Front.FrontOK C
  an : denoteN C.St.ns anonH = some .anonymous
  bi : BasisInv C
  run : Ind.IndRun C block nP

/-- A record's declaration in the value heap at `o`. -/
def RecOK (C : Ctx) (o : Nat) : IDeclaration → Prop
  | .defnDecl cv v hint => C.H[o]? = some 1 ∧ RecCV C (o + 1) cv ∧ C.H[o + 4]? = some (Enc.idxW v) ∧
      C.H[o + 5]? = some (BitVec.ofNat 64 (hintN hint)) ∧ hintN hint < 2 ^ 63 ∧ (denoteE C.St v).isSome = true
  | .thmDecl cv v => C.H[o]? = some 2 ∧ RecCV C (o + 1) cv ∧ C.H[o + 4]? = some (Enc.idxW v)
  | .opaqueDecl cv v => C.H[o]? = some 3 ∧ RecCV C (o + 1) cv ∧ C.H[o + 4]? = some (Enc.idxW v)
  | .indDecl block nP => C.H[o]? = some 4 ∧ IndSem C block nP ∧ ∃ ob, C.H[o + 1]? = some (BitVec.ofNat 64 nP) ∧
      C.H[o + 2]? = some (cellA C ob) ∧ Ind.IndBlk C C.H ob block ∧ block.length < 2 ^ 59 ∧ nP < 2 ^ 59 ∧
      ∀ i (hi : i < block.length), block[i].toConstantVal.levelParams.length < 2 ^ 59
  | .axiomDecl cv => C.H[o]? = some 5 ∧ RecCV C (o + 1) cv ∧ ∃ w, C.H[o + 4]? = some w
  | .quotDecl k cv => C.H[o]? = some 6 ∧ RecCV C (o + 1) cv ∧ C.H[o + 4]? = some (BitVec.ofNat 64 (Quot.qkN k))

def stQ := ofString "st_q"
def stT := ofString "st_t"
def stN := ofString "st_n"
def stA := ofString "st_a"
def stB := ofString "st_b"
def stV := ofString "st_v"
def stH := ofString "st_h"
def stR := ofString "st_r"
def fKd := ofString "checkDefn"
def fKt := ofString "checkThm"
def fKo := ofString "checkOpaque"
def fStep := ofString "checkDeclStep"
def stLocals : List MlS := [stT, stN, stA, stB, stV, stH, stR, lJ0]

/-- `andPinOk` at a one-constant record, then the flush, then the kind's check `kf` (value word at `o + 4`,
hint at `o + 5` when `hint`). -/
def stepKind (C : Ctx) (kf : MlS) (hint : Bool) : ProgHOL 64 :=
  .seq (.assign .local stN (.load .one (.op .add [vv stQ, .const 8])))
  (.seq (.call (some (some (.local, stA), none)) fPim [vv stN, .const 11, .const 12])
  (.seq (.call (some (some (.local, stB), none)) fPim [vv stN, .const 48, .const 50])
  (.ite (.op .or [vv stA, vv stB]) rejectP
  (flushCode C (flushRegions true)
  (.seq (.assign .local stV (.load .one (.op .add [vv stQ, .const 32])))
  (.seq (.assign .local stH (if hint then .load .one (.op .add [vv stQ, .const 40]) else .const 0))
  (.seq (.call (some (some (.local, stR), none)) kf [.op .add [vv stQ, .const 8], vv stV, vv stH])
  (.return (vv stR)))))))))

def stepBody (C : Ctx) : ProgHOL 64 := prologue stLocals
  (.seq (.assign .local stT (.load .one (vv stQ)))
  (.ite (.cmp .equal (vv stT) (.const 1)) (stepKind C fKd true)
  (.ite (.cmp .equal (vv stT) (.const 2)) (stepKind C fKt false)
  (.ite (.cmp .equal (vv stT) (.const 3)) (stepKind C fKo false)
  (.ite (.cmp .equal (vv stT) (.const 4))
    (.seq (.call (some (some (.local, stR), none)) Ind.fKi [vv stQ]) (.return (vv stR)))
  (.ite (.cmp .equal (vv stT) (.const 5)) (stepKind C fKa false)
  (.ite (.cmp .equal (vv stT) (.const 6)) (stepKind C Quot.fKq false)
    rejectP)))))))



section
variable {σ : Type}

theorem st_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ stLocals → (ctxEnv C ++ [stQ].zip vals).get x = none :=
  Knot.params_none C stLocals [stQ] vals (by decide) (by decide)

theorem or_bw (a b : Bool) : (boolW a ||| boolW b) = boolW (a || b) := by cases a <;> cases b <;> decide

/-- The inductive record's code. With `IndSem`, what its step needs beyond the fold's own invariants; both read
only the code, the layout, the store floor and the pins, which the fold keeps. -/
structure IndCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  ki : C.code.lookup Ind.fKi = some (Ind.kiParams.map (fun p => (p, ShapeHOL.one)), Ind.kiBody C, .one)
  kc : Ind.KICodes mode C

set_option maxRecDepth 8000 in
/-- **One record** of the fold. -/
theorem step_spec (mode : ConLeche.CheckMode) (pins : List INatOpPinSet) (C : Ctx) (hok : CtxOK C)
    (hc : DeclCodes mode C) (ra : ConPanqueque.Hash.RuntimeAssumptions) (hs : C.side = false)
    (hpl : C.saved = none) (hg : TblGate C.fe) (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins)
    (hkd : C.code.lookup fKd = some (kdParams.map (fun p => (p, ShapeHOL.one)), kdBody C, .one))
    (hkt : C.code.lookup fKt = some (kdParams.map (fun p => (p, ShapeHOL.one)), ktBody C, .one))
    (hko : C.code.lookup fKo = some (kdParams.map (fun p => (p, ShapeHOL.one)), koBody C, .one))
    (hka : C.code.lookup fKa = some (kdParams.map (fun p => (p, ShapeHOL.one)), kaBody C, .one))
    (heqS : ∀ (H : List (BitVec 64)) (u v : LIdx) (s : AState) (lu lv : ConLeche.Level),
      denoteL s.store.ls u = some lu → denoteL s.store.ls v = some lv → CachesOK s →
      SpecR (σ := σ) (Pre (ctxH C H) s [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s (lvlEq? u v)
        (fun o w s' st => LLeq.PostOB (ctxH C H) o w s' st))
    (hic : IndCodes mode C)
    (hkq : C.code.lookup Quot.fKq = some (kdParams.map (fun p => (p, ShapeHOL.one)), Quot.kqBody C, .one))
    (hqc : Quot.QCodes mode C) (hfr : ConPanqueque.Front.FrontOK C)
    (hA : denoteN C.St.ns default = some .anonymous)
    (heqA : ∀ (C' : Ctx), SameLay C C' → CtxOK C' → ∀ (H : List (BitVec 64)) (u v : LIdx) (s : AState)
      (lu lv : ConLeche.Level), denoteL s.store.ls u = some lu → denoteL s.store.ls v = some lv → CachesOK s →
      SpecR (σ := σ) (Pre (ctxH C' H) s [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s (lvlEq? u v)
        (fun o w s' st => LLeq.PostOB (ctxH C' H) o w s' st))
    (hLE : ∀ (H : List (BitVec 64)) s1 (u v : LIdx), C.H <+: H → (denoteL s1.store.ls u).isSome = true →
      (denoteL s1.store.ls v).isSome = true →
      SpecR (σ := σ) (Pre (ctxH C H) s1 [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s1 (lvlEq? u v)
        (LLeq.PostOB (ctxH C H)))
    (o : Nat) (d : IDeclaration) (hrec : RecOK C o d) (s : AState) (hmode : mode = .verified) (env : ConLeche.Env)
    (hseq : ConPanqueque.Bridge.SeqOK env C.fe s) (hden : ∃ d', Frontend.denoteDecl s.store d = some d') :
    SpecR (σ := σ) (Pre C s [(stQ, cellA C o)]) (stepBody C) s (checkDeclStep mode pins C.fe d) (PostStep C) := by
  refine specR_prologue (postStep_locals C) (st_none C [cellA C o]) ?_
  cases d
  case defnDecl cv v hint =>
    obtain ⟨h1, ⟨ol, ks, hn, hl, ht, hb, hlen, hkl, hks, htyD⟩, hv, hh, hhint, hvD⟩ := hrec
    refine UD.specR_heapLoadI' (C := C) stT _ o _ h1 (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    unfold stepKind
    refine UD.specR_heapLoadI' (C := C) stN _ (o + 1) _ hn (by decide)
      (by simp +decide [sev, Env.get, ctxEnv]; exact cellA_add8 C o) ?_
    unfold checkDeclStep
    simp only [andPinOk]
    refine specR_atEntry fun t0 ht0 => ?_
    refine specR_runBind (andPin_run hok ht0.sr.pins cv.name) ?_
    refine specR_callPure (C := C) stA fPim pmParams [vv stN, .const 11, .const 12] (pimBody C)
      [Enc.idxW cv.name, BitVec.ofNat 64 11, BitVec.ofNat 64 12] (pinIn C 11 12 cv.name) (by decide) rfl (by decide) hc.pim
      ⟨by simp +decide [Env.get], rfl, rfl, trivial⟩ (PostB C) (fun b w _ _ => w = boolW b)
      (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pmParams _ rfl hlk)
        (pim_spec C hok hc.pim s cv.name 12 (by decide) _ 11 C.H (List.prefix_refl _) rfl (by omega)))
      (fun w H1 hp1 hw => ?_)
    subst hw
    refine specR_callPure (C := ctxH C H1) stB fPim pmParams [vv stN, .const 48, .const 50] (pimBody C)
      [Enc.idxW cv.name, BitVec.ofNat 64 48, BitVec.ofNat 64 50] (pinIn C 48 50 cv.name) (by decide) rfl (by decide) hc.pim
      ⟨by simp +decide [Env.get], rfl, rfl, trivial⟩ (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b)
      (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pmParams _ rfl hlk)
        (pim_spec C hok hc.pim s cv.name 50 (by decide) _ 48 H1 hp1 rfl (by omega)))
      (fun w H2 hp2 hw => ?_)
    subst hw
    refine specR_failIteF (c := !(pinIn C 11 12 cv.name || pinIn C 48 50 cv.name)) _
      (boolW (pinIn C 11 12 cv.name || pinIn C 48 50 cv.name)) (by simp +decide [sev, Env.get]; exact or_bw _ _)
      (fun h => by
        have e : (pinIn C 11 12 cv.name || pinIn C 48 50 cv.name) = false := by
          clear heqA hLE; cases e : (pinIn C 11 12 cv.name || pinIn C 48 50 cv.name) <;> simp_all
        rw [e]; rfl)
      (fun h => by
        have e : (pinIn C 11 12 cv.name || pinIn C 48 50 cv.name) = true := by
          clear heqA hLE; cases e : (pinIn C 11 12 cv.name || pinIn C 48 50 cv.name) <;> simp_all
        rw [e]; decide)
      (fun _ => ?_)
    simp only [pure_bind]
    refine specR_congr (m' := (flushCaches >>= fun _ => (get : AM AState) >>= fun s' =>
      set { s' with memos := Memos.empty }) >>= fun _ => checkDecl mode pins C.fe (.defnDecl cv v hint))
      (by simp only [bind_assoc]) ?_
    have hp12 : C.H <+: H2 := hp1.trans hp2
    have hok2 := ctxOK_H hok H2
    refine specR_flushTopI (C := ctxH C H2) hok2 hpl true _ (stepFlush_run s) (by decide) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H2) stV _ (o + 4) _ (get_prefix hv hp12) (by decide)
      (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ctxEnv]; exact cellA_add_ofNat C o 4) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H2) stH _ (o + 5) _ (get_prefix hh hp12) (by decide)
      (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ctxEnv]; exact cellA_add_ofNat C o 5) ?_
    refine specR_congr (m' := checkDecl mode pins C.fe (.defnDecl cv v hint) >>= fun fe => pure fe) (by simp) ?_
    refine specR_callNC (C := ctxH C H2) (D := ctxLocals ++ stLocals) stR fKd kdParams
      [.op .add [vv stQ, .const 8], vv stV, vv stH] (kdBody C)
      [cellA C (o + 1), Enc.idxW v, BitVec.ofNat 64 (hintN hint)] (by decide) rfl (by decide) hkd ?_
      (PostStep (ctxH C H2))
      (fun a w s' C' => ∃ EH envM tblM H, C' = ctxNewT C a EH envM tblM H ∧ C.EH <+: EH ∧ C.H <+: H ∧ CtxOK C' ∧
        TblGate a ∧ FlagsOK a ∧ LitsPinned a C.pins)
      (fun a w s' st ⟨EH, envM, tblM, H, hpE, hpH, hokN, hsr, hgt, hfl, hlp⟩ =>
        ⟨ctxNewT C a EH envM tblM H, ⟨EH, envM, tblM, H, rfl, hpE, hp12.trans hpH, hokN, hgt, hfl, hlp⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu kdParams _ rfl hlk)
        (kd_spec mode pins (ctxH C H2) hok2 (by ctx_tr hc) ra hs hpl hg hF hL cv v hint (o + 1) ol
          (get_prefix hn hp12) (get_prefix hl hp12) (get_prefix ht hp12) (blkAt_mono hb hp12) hlen ks hkl hks htyD hvD
          hhint _))
      (fun a w s5 C5 ⟨EH, envM, tblM, H, eC, hpE, hpH, hokN, hgt, hfl, hlp⟩ => ?_)
    · exact ⟨by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ctxEnv]; exact cellA_add8 C o,
        by simp +decide [Env.get], by simp +decide [Env.get], trivial⟩
    subst eC
    exact specR_returnI _ w (by simp +decide [Env.get])
      (fun t ht => ⟨EH, envM, tblM, H, hpE, hpH, hokN, sr_of_eq ht.sr rfl rfl rfl rfl, hgt, hfl, hlp⟩)
  case thmDecl cv v =>
    obtain ⟨h1, ⟨ol, ks, hn, hl, ht, hb, hlen, hkl, hks, htyD⟩, hv⟩ := hrec
    refine UD.specR_heapLoadI' (C := C) stT _ o _ h1 (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    unfold stepKind
    refine UD.specR_heapLoadI' (C := C) stN _ (o + 1) _ hn (by decide)
      (by simp +decide [sev, Env.get, ctxEnv]; exact cellA_add8 C o) ?_
    unfold checkDeclStep
    simp only [andPinOk]
    refine specR_atEntry fun t0 ht0 => ?_
    refine specR_runBind (andPin_run hok ht0.sr.pins cv.name) ?_
    refine specR_callPure (C := C) stA fPim pmParams [vv stN, .const 11, .const 12] (pimBody C)
      [Enc.idxW cv.name, BitVec.ofNat 64 11, BitVec.ofNat 64 12] (pinIn C 11 12 cv.name) (by decide) rfl (by decide) hc.pim
      ⟨by simp +decide [Env.get], rfl, rfl, trivial⟩ (PostB C) (fun b w _ _ => w = boolW b)
      (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pmParams _ rfl hlk)
        (pim_spec C hok hc.pim s cv.name 12 (by decide) _ 11 C.H (List.prefix_refl _) rfl (by omega)))
      (fun w H1 hp1 hw => ?_)
    subst hw
    refine specR_callPure (C := ctxH C H1) stB fPim pmParams [vv stN, .const 48, .const 50] (pimBody C)
      [Enc.idxW cv.name, BitVec.ofNat 64 48, BitVec.ofNat 64 50] (pinIn C 48 50 cv.name) (by decide) rfl (by decide) hc.pim
      ⟨by simp +decide [Env.get], rfl, rfl, trivial⟩ (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b)
      (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pmParams _ rfl hlk)
        (pim_spec C hok hc.pim s cv.name 50 (by decide) _ 48 H1 hp1 rfl (by omega)))
      (fun w H2 hp2 hw => ?_)
    subst hw
    refine specR_failIteF (c := !(pinIn C 11 12 cv.name || pinIn C 48 50 cv.name)) _
      (boolW (pinIn C 11 12 cv.name || pinIn C 48 50 cv.name)) (by simp +decide [sev, Env.get]; exact or_bw _ _)
      (fun h => by
        have e : (pinIn C 11 12 cv.name || pinIn C 48 50 cv.name) = false := by
          clear heqA hLE; cases e : (pinIn C 11 12 cv.name || pinIn C 48 50 cv.name) <;> simp_all
        rw [e]; rfl)
      (fun h => by
        have e : (pinIn C 11 12 cv.name || pinIn C 48 50 cv.name) = true := by
          clear heqA hLE; cases e : (pinIn C 11 12 cv.name || pinIn C 48 50 cv.name) <;> simp_all
        rw [e]; decide)
      (fun _ => ?_)
    simp only [pure_bind]
    refine specR_congr (m' := (flushCaches >>= fun _ => (get : AM AState) >>= fun s' =>
      set { s' with memos := Memos.empty }) >>= fun _ => checkDecl mode pins C.fe (.thmDecl cv v))
      (by simp only [bind_assoc]) ?_
    have hp12 : C.H <+: H2 := hp1.trans hp2
    have hok2 := ctxOK_H hok H2
    refine specR_flushTopI (C := ctxH C H2) hok2 hpl true _ (stepFlush_run s) (by decide) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H2) stV _ (o + 4) _ (get_prefix hv hp12) (by decide)
      (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ctxEnv]; exact cellA_add_ofNat C o 4) ?_
    refine specR_assignI stH (.const 0) 0 (by decide) rfl ?_
    refine specR_congr (m' := checkDecl mode pins C.fe (.thmDecl cv v) >>= fun fe => pure fe) (by simp) ?_
    refine specR_callNC (C := ctxH C H2) (D := ctxLocals ++ stLocals) stR fKt kdParams
      [.op .add [vv stQ, .const 8], vv stV, vv stH] (ktBody C)
      [cellA C (o + 1), Enc.idxW v, 0] (by decide) rfl (by decide) hkt ?_
      (PostStep (ctxH C H2))
      (fun a w s' C' => ∃ EH envM tblM H, C' = ctxNewT C a EH envM tblM H ∧ C.EH <+: EH ∧ C.H <+: H ∧ CtxOK C' ∧
        TblGate a ∧ FlagsOK a ∧ LitsPinned a C.pins)
      (fun a w s' st ⟨EH, envM, tblM, H, hpE, hpH, hokN, hsr, hgt, hfl, hlp⟩ =>
        ⟨ctxNewT C a EH envM tblM H, ⟨EH, envM, tblM, H, rfl, hpE, hp12.trans hpH, hokN, hgt, hfl, hlp⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu kdParams _ rfl hlk)
        (kt_spec mode pins (ctxH C H2) hok2 (by ctx_tr hc) ra hs hpl hg hF hL (fun H u' v' s' lu lv h1 h2 h3 => heqS H u' v' s' lu lv h1 h2 h3) cv v (o + 1) ol
          (get_prefix hn hp12) (get_prefix hl hp12) (get_prefix ht hp12) (blkAt_mono hb hp12) hlen ks hkl hks htyD _))
      (fun a w s5 C5 ⟨EH, envM, tblM, H, eC, hpE, hpH, hokN, hgt, hfl, hlp⟩ => ?_)
    · exact ⟨by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ctxEnv]; exact cellA_add8 C o,
        by simp +decide [Env.get], by simp +decide [Env.get], trivial⟩
    subst eC
    exact specR_returnI _ w (by simp +decide [Env.get])
      (fun t ht => ⟨EH, envM, tblM, H, hpE, hpH, hokN, sr_of_eq ht.sr rfl rfl rfl rfl, hgt, hfl, hlp⟩)
  case opaqueDecl cv v =>
    obtain ⟨h1, ⟨ol, ks, hn, hl, ht, hb, hlen, hkl, hks, htyD⟩, hv⟩ := hrec
    refine UD.specR_heapLoadI' (C := C) stT _ o _ h1 (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    unfold stepKind
    refine UD.specR_heapLoadI' (C := C) stN _ (o + 1) _ hn (by decide)
      (by simp +decide [sev, Env.get, ctxEnv]; exact cellA_add8 C o) ?_
    unfold checkDeclStep
    simp only [andPinOk]
    refine specR_atEntry fun t0 ht0 => ?_
    refine specR_runBind (andPin_run hok ht0.sr.pins cv.name) ?_
    refine specR_callPure (C := C) stA fPim pmParams [vv stN, .const 11, .const 12] (pimBody C)
      [Enc.idxW cv.name, BitVec.ofNat 64 11, BitVec.ofNat 64 12] (pinIn C 11 12 cv.name) (by decide) rfl (by decide) hc.pim
      ⟨by simp +decide [Env.get], rfl, rfl, trivial⟩ (PostB C) (fun b w _ _ => w = boolW b)
      (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pmParams _ rfl hlk)
        (pim_spec C hok hc.pim s cv.name 12 (by decide) _ 11 C.H (List.prefix_refl _) rfl (by omega)))
      (fun w H1 hp1 hw => ?_)
    subst hw
    refine specR_callPure (C := ctxH C H1) stB fPim pmParams [vv stN, .const 48, .const 50] (pimBody C)
      [Enc.idxW cv.name, BitVec.ofNat 64 48, BitVec.ofNat 64 50] (pinIn C 48 50 cv.name) (by decide) rfl (by decide) hc.pim
      ⟨by simp +decide [Env.get], rfl, rfl, trivial⟩ (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b)
      (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pmParams _ rfl hlk)
        (pim_spec C hok hc.pim s cv.name 50 (by decide) _ 48 H1 hp1 rfl (by omega)))
      (fun w H2 hp2 hw => ?_)
    subst hw
    refine specR_failIteF (c := !(pinIn C 11 12 cv.name || pinIn C 48 50 cv.name)) _
      (boolW (pinIn C 11 12 cv.name || pinIn C 48 50 cv.name)) (by simp +decide [sev, Env.get]; exact or_bw _ _)
      (fun h => by
        have e : (pinIn C 11 12 cv.name || pinIn C 48 50 cv.name) = false := by
          clear heqA hLE; cases e : (pinIn C 11 12 cv.name || pinIn C 48 50 cv.name) <;> simp_all
        rw [e]; rfl)
      (fun h => by
        have e : (pinIn C 11 12 cv.name || pinIn C 48 50 cv.name) = true := by
          clear heqA hLE; cases e : (pinIn C 11 12 cv.name || pinIn C 48 50 cv.name) <;> simp_all
        rw [e]; decide)
      (fun _ => ?_)
    simp only [pure_bind]
    refine specR_congr (m' := (flushCaches >>= fun _ => (get : AM AState) >>= fun s' =>
      set { s' with memos := Memos.empty }) >>= fun _ => checkDecl mode pins C.fe (.opaqueDecl cv v))
      (by simp only [bind_assoc]) ?_
    have hp12 : C.H <+: H2 := hp1.trans hp2
    have hok2 := ctxOK_H hok H2
    refine specR_flushTopI (C := ctxH C H2) hok2 hpl true _ (stepFlush_run s) (by decide) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H2) stV _ (o + 4) _ (get_prefix hv hp12) (by decide)
      (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ctxEnv]; exact cellA_add_ofNat C o 4) ?_
    refine specR_assignI stH (.const 0) 0 (by decide) rfl ?_
    refine specR_congr (m' := checkDecl mode pins C.fe (.opaqueDecl cv v) >>= fun fe => pure fe) (by simp) ?_
    refine specR_callNC (C := ctxH C H2) (D := ctxLocals ++ stLocals) stR fKo kdParams
      [.op .add [vv stQ, .const 8], vv stV, vv stH] (koBody C)
      [cellA C (o + 1), Enc.idxW v, 0] (by decide) rfl (by decide) hko ?_
      (PostStep (ctxH C H2))
      (fun a w s' C' => ∃ EH envM tblM H, C' = ctxNewT C a EH envM tblM H ∧ C.EH <+: EH ∧ C.H <+: H ∧ CtxOK C' ∧
        TblGate a ∧ FlagsOK a ∧ LitsPinned a C.pins)
      (fun a w s' st ⟨EH, envM, tblM, H, hpE, hpH, hokN, hsr, hgt, hfl, hlp⟩ =>
        ⟨ctxNewT C a EH envM tblM H, ⟨EH, envM, tblM, H, rfl, hpE, hp12.trans hpH, hokN, hgt, hfl, hlp⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu kdParams _ rfl hlk)
        (ko_spec mode pins (ctxH C H2) hok2 (by ctx_tr hc) ra hs hpl hg hF hL cv v (o + 1) ol
          (get_prefix hn hp12) (get_prefix hl hp12) (get_prefix ht hp12) (blkAt_mono hb hp12) hlen ks hkl hks htyD _))
      (fun a w s5 C5 ⟨EH, envM, tblM, H, eC, hpE, hpH, hokN, hgt, hfl, hlp⟩ => ?_)
    · exact ⟨by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ctxEnv]; exact cellA_add8 C o,
        by simp +decide [Env.get], by simp +decide [Env.get], trivial⟩
    subst eC
    exact specR_returnI _ w (by simp +decide [Env.get])
      (fun t ht => ⟨EH, envM, tblM, H, hpE, hpH, hokN, sr_of_eq ht.sr rfl rfl rfl rfl, hgt, hfl, hlp⟩)
  case axiomDecl cv =>
    obtain ⟨h1, ⟨ol, ks, hn, hl, ht, hb, hlen, hkl, hks, htyD⟩, wv, hv⟩ := hrec
    refine UD.specR_heapLoadI' (C := C) stT _ o _ h1 (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    unfold stepKind
    refine UD.specR_heapLoadI' (C := C) stN _ (o + 1) _ hn (by decide)
      (by simp +decide [sev, Env.get, ctxEnv]; exact cellA_add8 C o) ?_
    unfold checkDeclStep
    simp only [andPinOk]
    refine specR_atEntry fun t0 ht0 => ?_
    refine specR_runBind (andPin_run hok ht0.sr.pins cv.name) ?_
    refine specR_callPure (C := C) stA fPim pmParams [vv stN, .const 11, .const 12] (pimBody C)
      [Enc.idxW cv.name, BitVec.ofNat 64 11, BitVec.ofNat 64 12] (pinIn C 11 12 cv.name) (by decide) rfl (by decide) hc.pim
      ⟨by simp +decide [Env.get], rfl, rfl, trivial⟩ (PostB C) (fun b w _ _ => w = boolW b)
      (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pmParams _ rfl hlk)
        (pim_spec C hok hc.pim s cv.name 12 (by decide) _ 11 C.H (List.prefix_refl _) rfl (by omega)))
      (fun w H1 hp1 hw => ?_)
    subst hw
    refine specR_callPure (C := ctxH C H1) stB fPim pmParams [vv stN, .const 48, .const 50] (pimBody C)
      [Enc.idxW cv.name, BitVec.ofNat 64 48, BitVec.ofNat 64 50] (pinIn C 48 50 cv.name) (by decide) rfl (by decide) hc.pim
      ⟨by simp +decide [Env.get], rfl, rfl, trivial⟩ (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b)
      (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pmParams _ rfl hlk)
        (pim_spec C hok hc.pim s cv.name 50 (by decide) _ 48 H1 hp1 rfl (by omega)))
      (fun w H2 hp2 hw => ?_)
    subst hw
    refine specR_failIteF (c := !(pinIn C 11 12 cv.name || pinIn C 48 50 cv.name)) _
      (boolW (pinIn C 11 12 cv.name || pinIn C 48 50 cv.name)) (by simp +decide [sev, Env.get]; exact or_bw _ _)
      (fun h => by
        have e : (pinIn C 11 12 cv.name || pinIn C 48 50 cv.name) = false := by
          clear heqA hLE; cases e : (pinIn C 11 12 cv.name || pinIn C 48 50 cv.name) <;> simp_all
        rw [e]; rfl)
      (fun h => by
        have e : (pinIn C 11 12 cv.name || pinIn C 48 50 cv.name) = true := by
          clear heqA hLE; cases e : (pinIn C 11 12 cv.name || pinIn C 48 50 cv.name) <;> simp_all
        rw [e]; decide)
      (fun _ => ?_)
    simp only [pure_bind]
    refine specR_congr (m' := (flushCaches >>= fun _ => (get : AM AState) >>= fun s' =>
      set { s' with memos := Memos.empty }) >>= fun _ => checkDecl mode pins C.fe (.axiomDecl cv))
      (by simp only [bind_assoc]) ?_
    have hp12 : C.H <+: H2 := hp1.trans hp2
    have hok2 := ctxOK_H hok H2
    refine specR_flushTopI (C := ctxH C H2) hok2 hpl true _ (stepFlush_run s) (by decide) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H2) stV _ (o + 4) _ (get_prefix hv hp12) (by decide)
      (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ctxEnv]; exact cellA_add_ofNat C o 4) ?_
    refine specR_assignI stH (.const 0) 0 (by decide) rfl ?_
    refine specR_congr (m' := checkDecl mode pins C.fe (.axiomDecl cv) >>= fun fe => pure fe) (by simp) ?_
    refine specR_callNC (C := ctxH C H2) (D := ctxLocals ++ stLocals) stR fKa kdParams
      [.op .add [vv stQ, .const 8], vv stV, vv stH] (kaBody C)
      [cellA C (o + 1), wv, 0] (by decide) rfl (by decide) hka ?_
      (PostStep (ctxH C H2))
      (fun a w s' C' => ∃ EH envM tblM H, C' = ctxNewT C a EH envM tblM H ∧ C.EH <+: EH ∧ C.H <+: H ∧ CtxOK C' ∧
        TblGate a ∧ FlagsOK a ∧ LitsPinned a C.pins)
      (fun a w s' st ⟨EH, envM, tblM, H, hpE, hpH, hokN, hsr, hgt, hfl, hlp⟩ =>
        ⟨ctxNewT C a EH envM tblM H, ⟨EH, envM, tblM, H, rfl, hpE, hp12.trans hpH, hokN, hgt, hfl, hlp⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu kdParams _ rfl hlk)
        (ka_spec mode pins (ctxH C H2) hok2 (by ctx_tr hc) ra hs hpl hg hF hL cv wv (o + 1) ol
          (get_prefix hn hp12) (get_prefix hl hp12) (get_prefix ht hp12) (blkAt_mono hb hp12) hlen ks hkl hks htyD
          hkq (Quot.qcodes_ctxH hqc H2) (by ctx_tr hfr) hA _))
      (fun a w s5 C5 ⟨EH, envM, tblM, H, eC, hpE, hpH, hokN, hgt, hfl, hlp⟩ => ?_)
    · exact ⟨by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ctxEnv]; exact cellA_add8 C o,
        by simp +decide [Env.get], by simp +decide [Env.get], trivial⟩
    subst eC
    exact specR_returnI _ w (by simp +decide [Env.get])
      (fun t ht => ⟨EH, envM, tblM, H, hpE, hpH, hokN, sr_of_eq ht.sr rfl rfl rfl rfl, hgt, hfl, hlp⟩)
  case indDecl block nP =>
    obtain ⟨h1, hie, ob, hq1, hq2, hblk, hlen, hnP, hlp⟩ := hrec
    obtain ⟨d', hd'⟩ := hden
    have hbP : ∃ bP, Frontend.denoteCIList s.store block = some bP := by
      simp only [Frontend.denoteDecl] at hd'
      cases hb : Frontend.denoteCIList s.store block with
      | none => rw [hb] at hd'; simp at hd'
      | some bl => exact ⟨bl, rfl⟩
    obtain ⟨bP, hbP⟩ := hbP
    refine UD.specR_heapLoadI' (C := C) stT _ o _ h1 (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_congr (m' := checkDeclStep mode pins C.fe (.indDecl block nP) >>= fun fe => pure fe) (by simp) ?_
    refine specR_callNC (C := C) (D := ctxLocals ++ stLocals) stR Ind.fKi Ind.kiParams [vv stQ] (Ind.kiBody C)
      [cellA C o] (by decide) rfl (by decide) hic.ki ?_ (Ind.PostBlk C)
      (fun a w s' C' => ∃ EH envM tblM H, C' = ctxNewT C a EH envM tblM H ∧ C.EH <+: EH ∧ C.H <+: H ∧ CtxOK C' ∧
        TblGate a ∧ FlagsOK a ∧ LitsPinned a C.pins)
      (fun a w s' st ⟨EH, envM, tblM, H, hpE, hpH, hokN, hsr, hgt, hfl, hlp⟩ =>
        ⟨ctxNewT C a EH envM tblM H, ⟨EH, envM, tblM, H, rfl, hpE, hpH, hokN, hgt, hfl, hlp⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu Ind.kiParams _ rfl hlk)
        (Ind.ki_spec mode pins ra C hok hs hpl hic.kc hie.fr hg hF hL heqA hLE hie.an hie.bi block nP o ob hq1 hq2
          hblk hlen hnP hlp hie.run s hmode env hseq bP hbP))
      (fun a w s5 C5 ⟨EH, envM, tblM, H, eC, hpE, hpH, hokN, hgt, hfl, hlp⟩ => ?_)
    · exact ⟨by simp +decide [sev, Env.get, ctxEnv], trivial⟩
    subst eC
    exact specR_returnI _ w (by simp +decide [Env.get])
      (fun t ht => ⟨EH, envM, tblM, H, hpE, hpH, hokN, sr_of_eq ht.sr rfl rfl rfl rfl, hgt, hfl, hlp⟩)
  case quotDecl k cv =>
    obtain ⟨h1, ⟨ol, ks, hn, hl, ht, hb, hlen, hkl, hks, htyD⟩, hv⟩ := hrec
    refine UD.specR_heapLoadI' (C := C) stT _ o _ h1 (by decide) (by simp +decide [Env.get, ctxEnv]) ?_
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h)
      (fun _ => ?_)
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_)
      (fun h => absurd h (by decide))
    unfold stepKind
    refine UD.specR_heapLoadI' (C := C) stN _ (o + 1) _ hn (by decide)
      (by simp +decide [sev, Env.get, ctxEnv]; exact cellA_add8 C o) ?_
    unfold checkDeclStep
    simp only [andPinOk]
    refine specR_atEntry fun t0 ht0 => ?_
    refine specR_runBind (andPin_run hok ht0.sr.pins cv.name) ?_
    refine specR_callPure (C := C) stA fPim pmParams [vv stN, .const 11, .const 12] (pimBody C)
      [Enc.idxW cv.name, BitVec.ofNat 64 11, BitVec.ofNat 64 12] (pinIn C 11 12 cv.name) (by decide) rfl (by decide) hc.pim
      ⟨by simp +decide [Env.get], rfl, rfl, trivial⟩ (PostB C) (fun b w _ _ => w = boolW b)
      (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pmParams _ rfl hlk)
        (pim_spec C hok hc.pim s cv.name 12 (by decide) _ 11 C.H (List.prefix_refl _) rfl (by omega)))
      (fun w H1 hp1 hw => ?_)
    subst hw
    refine specR_callPure (C := ctxH C H1) stB fPim pmParams [vv stN, .const 48, .const 50] (pimBody C)
      [Enc.idxW cv.name, BitVec.ofNat 64 48, BitVec.ofNat 64 50] (pinIn C 48 50 cv.name) (by decide) rfl (by decide) hc.pim
      ⟨by simp +decide [Env.get], rfl, rfl, trivial⟩ (PostB (ctxH C H1)) (fun b w _ _ => w = boolW b)
      (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu pmParams _ rfl hlk)
        (pim_spec C hok hc.pim s cv.name 50 (by decide) _ 48 H1 hp1 rfl (by omega)))
      (fun w H2 hp2 hw => ?_)
    subst hw
    refine specR_failIteF (c := !(pinIn C 11 12 cv.name || pinIn C 48 50 cv.name)) _
      (boolW (pinIn C 11 12 cv.name || pinIn C 48 50 cv.name)) (by simp +decide [sev, Env.get]; exact or_bw _ _)
      (fun h => by
        have e : (pinIn C 11 12 cv.name || pinIn C 48 50 cv.name) = false := by
          clear heqA hLE; cases e : (pinIn C 11 12 cv.name || pinIn C 48 50 cv.name) <;> simp_all
        rw [e]; rfl)
      (fun h => by
        have e : (pinIn C 11 12 cv.name || pinIn C 48 50 cv.name) = true := by
          clear heqA hLE; cases e : (pinIn C 11 12 cv.name || pinIn C 48 50 cv.name) <;> simp_all
        rw [e]; decide)
      (fun _ => ?_)
    simp only [pure_bind]
    refine specR_congr (m' := (flushCaches >>= fun _ => (get : AM AState) >>= fun s' =>
      set { s' with memos := Memos.empty }) >>= fun _ => checkDecl mode pins C.fe (.quotDecl k cv))
      (by simp only [bind_assoc]) ?_
    have hp12 : C.H <+: H2 := hp1.trans hp2
    have hok2 := ctxOK_H hok H2
    refine specR_flushTopI (C := ctxH C H2) hok2 hpl true _ (stepFlush_run s) (by decide) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H2) stV _ (o + 4) _ (get_prefix hv hp12) (by decide)
      (by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ctxEnv]; exact cellA_add_ofNat C o 4) ?_
    refine specR_assignI stH (.const 0) 0 (by decide) rfl ?_
    refine specR_congr (m' := checkDecl mode pins C.fe (.quotDecl k cv) >>= fun fe => pure fe) (by simp) ?_
    refine specR_callNC (C := ctxH C H2) (D := ctxLocals ++ stLocals) stR Quot.fKq kdParams
      [.op .add [vv stQ, .const 8], vv stV, vv stH] (Quot.kqBody C)
      [cellA C (o + 1), BitVec.ofNat 64 (Quot.qkN k), 0] (by decide) rfl (by decide) hkq ?_
      (PostStep (ctxH C H2))
      (fun a w s' C' => ∃ EH envM tblM H, C' = ctxNewT C a EH envM tblM H ∧ C.EH <+: EH ∧ C.H <+: H ∧ CtxOK C' ∧
        TblGate a ∧ FlagsOK a ∧ LitsPinned a C.pins)
      (fun a w s' st ⟨EH, envM, tblM, H, hpE, hpH, hokN, hsr, hgt, hfl, hlp⟩ =>
        ⟨ctxNewT C a EH envM tblM H, ⟨EH, envM, tblM, H, rfl, hpE, hp12.trans hpH, hokN, hgt, hfl, hlp⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu kdParams _ rfl hlk)
        (Quot.kq_spec ra mode pins (ctxH C H2) hok2 (Quot.qcodes_ctxH hqc H2) hs hpl hg hF hL (by ctx_tr hfr) hA k cv (o + 1)
          ⟨ol, ks, get_prefix hn hp12, get_prefix hl hp12, get_prefix ht hp12, blkAt_mono hb hp12, hlen, hkl, hks, htyD⟩
          _))
      (fun a w s5 C5 ⟨EH, envM, tblM, H, eC, hpE, hpH, hokN, hgt, hfl, hlp⟩ => ?_)
    · exact ⟨by simp +decide [sev, Env.get, ConPanqueque.T.ExP.Env.get_kill_of_not_mem, ctxEnv]; exact cellA_add8 C o,
        by simp +decide [Env.get], by simp +decide [Env.get], trivial⟩
    subst eC
    exact specR_returnI _ w (by simp +decide [Env.get])
      (fun t ht => ⟨EH, envM, tblM, H, hpE, hpH, hokN, sr_of_eq ht.sr rfl rfl rfl rfl, hgt, hfl, hlp⟩)

end

end ConPanqueque.T.Decl
