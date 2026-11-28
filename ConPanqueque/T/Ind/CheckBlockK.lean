import ConPanqueque.T.SameLay
import ConPanqueque.T.Ind.CheckPass
import ConPanqueque.T.Ind.BlockTail
import ConPanqueque.T.Ind.CtorNames
import ConPanqueque.T.Ind.CtorsFresh
import ConPanqueque.T.Ind.CtorNamesAll
import ConPanqueque.T.Ind.MembersOk
import ConPanqueque.T.Ind.CtorsFreshAll
import ConPanqueque.T.Ind.CheckBlock
import ConPanqueque.T.Ind.BlockIsRec
import ConPanqueque.T.Ind.CheckBlockInst
import ConPanqueque.T.Ind.PassCls
import ConPanqueque.T.Ind.BlockTablesAll

/-!
# `checkBlock` (one member, one recursor at it, unnested)

`cbkBody`: the constructors' names distinct, the member not at a `Bool` constructor's name, its declared name
fresh, the members reduced (each already at its telescope), the flush, `blockIsRec`, the pass, the constructors
fresh at the formers' environment, the projection tables, the pass's pieces read (one class, at member 0; the
recursor's class `[0]`; slot 0 a motive; the field kinds flat; the recursor at member 0 — else hang), the tail,
the recursor installed (its rules fire `.plain`), the table (if any) installed.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def cbkSh := ofString "cbk_sh"
def cbkOm := ofString "cbk_om"
def cbkNm0 := ofString "cbk_nm0"
def cbkOmr := ofString "cbk_omr"
def cbkOc := ofString "cbk_oc"
def cbkNm := ofString "cbk_nm"
def cbkOd := ofString "cbk_od"
def cbkDnm := ofString "cbk_dnm"
def cbkOct := ofString "cbk_oct"
def cbkNct := ofString "cbk_nct"
def cbkOrl := ofString "cbk_orl"
def cbkNrl := ofString "cbk_nrl"
def cbkOrr := ofString "cbk_orr"
def cbkX := ofString "cbk_x"
def cbkBt := ofString "cbk_bt"
def cbkBf := ofString "cbk_bf"
def cbkY := ofString "cbk_y"
def cbkIr := ofString "cbk_ir"
def cbkQ := ofString "cbk_q"
def cbkO1 := ofString "cbk_o1"
def cbkNp := ofString "cbk_np"
def cbkTq := ofString "cbk_tq"
def cbkOm1 := ofString "cbk_om1"
def cbkOmr1 := ofString "cbk_omr1"
def cbkOc1 := ofString "cbk_oc1"
def cbkOlw := ofString "cbk_olw"
def cbkTy0 := ofString "cbk_ty0"
def cbkNm1 := ofString "cbk_nm1"
def cbkOr1 := ofString "cbk_or1"
def cbkOrr1 := ofString "cbk_orr1"
def cbkOb := ofString "cbk_ob"
def cbkOpp := ofString "cbk_opp"
def cbkNpp := ofString "cbk_npp"
def cbkOcb := ofString "cbk_ocb"
def cbkOrd := ofString "cbk_ord"
def cbkOs := ofString "cbk_os"
def cbkNsl := ofString "cbk_nsl"
def cbkOrc := ofString "cbk_orc"
def cbkNrc := ofString "cbk_nrc"
def cbkRc0 := ofString "cbk_rc0"
def cbkS0p := ofString "cbk_s0p"
def cbkTag := ofString "cbk_tag"
def cbkOms := ofString "cbk_oms"
def cbkNcl := ofString "cbk_ncl"
def cbkOp := ofString "cbk_op"
def cbkNi := ofString "cbk_ni"
def cbkOq := ofString "cbk_oq"
def cbkNq := ofString "cbk_nq"
def cbkMb := ofString "cbk_mb"
def cbkOa := ofString "cbk_oa"
def cbkInd := ofString "cbk_ind"
def cbkLv := ofString "cbk_lv"
def cbkPa := ofString "cbk_pa"
def cbkNd := ofString "cbk_nd"
def cbkNpc := ofString "cbk_npc"
def cbkOcp := ofString "cbk_ocp"
def cbkOo := ofString "cbk_oo"
def cbkNoo := ofString "cbk_noo"
def cbkOn := ofString "cbk_on"
def cbkNtb := ofString "cbk_ntb"
def cbkTgt := ofString "cbk_tgt"
def cbkNp1 := ofString "cbk_np1"
def cbkRs1 := ofString "cbk_rs1"
def cbkNqq := ofString "cbk_nqq"
def cbkR := ofString "cbk_r"
def cbkT := ofString "cbk_t"
def cbkTn := ofString "cbk_tn"
def fCbk := ofString "checkBlock"

def cbkParams : List MlS := [cbkSh]
def cbkLocals : List MlS := [cbkOm, cbkNm0, cbkOmr, cbkOc, cbkNm, cbkOd, cbkDnm, cbkOct, cbkNct, cbkOrl, cbkNrl, cbkOrr, cbkX, cbkBt, cbkBf, cbkY, cbkIr, cbkQ, cbkO1, cbkNp, cbkTq, cbkOm1, cbkOmr1, cbkOc1, cbkOlw, cbkTy0, cbkNm1, cbkOr1, cbkOrr1, cbkOb, cbkOpp, cbkNpp, cbkOcb, cbkOrd, cbkOs, cbkNsl, cbkOrc, cbkNrc, cbkRc0, cbkS0p, cbkTag, cbkOms, cbkNcl, cbkOp, cbkNi, cbkOq, cbkNq, cbkMb, cbkOa, cbkInd, cbkLv, cbkPa, cbkNd, cbkNpc, cbkOcp, cbkOo, cbkNoo, cbkOn, cbkNtb, cbkTgt, cbkNp1, cbkRs1, cbkNqq, cbkR, cbkT, cbkTn, lJ0]

def cbkBody (C : Ctx) : ProgHOL 64 := prologue cbkLocals
  (.seq (.assign .local cbkOm (.load .one (vv cbkSh)))
  (.seq (.assign .local cbkNm0 (.load .one (vv cbkOm)))
  (.ite (.cmp .equal (vv cbkNm0) (.const 1))
  (.seq (.assign .local cbkOmr (.load .one (.op .add [vv cbkOm, .const 8])))
  (.seq (.assign .local cbkOct (.load .one (.op .add [vv cbkOmr, .const 24])))
  (.seq (.assign .local cbkNct (.load .one (vv cbkOct)))
  (.seq (.assign .local cbkOrl (.load .one (.op .add [vv cbkSh, .const 8])))
  (.seq (.assign .local cbkNrl (.load .one (vv cbkOrl)))
  (.ite (.cmp .equal (vv cbkNrl) (.const 1))
  (.seq (.assign .local cbkOrr (.load .one (.op .add [vv cbkOrl, .const 8])))
  (.seq (.call (some (some (.local, cbkX), none)) fCnk [vv cbkOm, vv cbkNm0])
  (.ite (.cmp .equal (vv cbkX) (.const 0)) hang
  (.seq (.assign .local cbkBt (.load .one (.const (ecell C (C.PO + PIN_BOOL_TRUE)))))
  (.seq (.assign .local cbkBf (.load .one (.const (ecell C (C.PO + PIN_BOOL_FALSE)))))
  (.seq (.call (some (some (.local, cbkX), none)) fMok [vv cbkOm, .const 0, vv cbkNm0, vv cbkBt, vv cbkBf])
  (.seq (.call (some (some (.local, cbkX), none)) fRmFill [vv cbkOm, .const 0, vv cbkNm0])
  (flushCode C (flushRegions false)
  (.seq (.call (some (some (.local, cbkIr), none)) fBlockIsRec [vv cbkOm, vv cbkNm0])
  (.seq (.call (some (some (.local, cbkQ), none)) fCps [vv cbkSh, vv cbkIr])
  (.seq (.call (some (some (.local, cbkX), none)) fCfa [vv cbkOm, .const 0, vv cbkNm0])
  (.seq (.assign .local cbkNp (.load .one (.op .add [vv cbkSh, .const 16])))
  (.seq (.call (some (some (.local, cbkTq), none)) fBta [vv cbkOm, .const 0, vv cbkNm0, vv cbkNp])
  (.seq (.assign .local cbkO1 (.load .one (vv cbkQ)))
  (.seq (.assign .local cbkOm1 (.load .one (vv cbkO1)))
  (.seq (.assign .local cbkOmr1 (.load .one (.op .add [vv cbkOm1, .const 8])))
  (.seq (.assign .local cbkOc1 (.load .one (vv cbkOmr1)))
  (.seq (.assign .local cbkOlw (.load .one (.op .add [vv cbkOc1, .const 8])))
  (.seq (.assign .local cbkTy0 (.load .one (.op .add [vv cbkOc1, .const 16])))
  (.seq (.assign .local cbkNm1 (.load .one (vv cbkOc1)))
  (.seq (.assign .local cbkOr1 (.load .one (.op .add [vv cbkO1, .const 8])))
  (.seq (.assign .local cbkOrr1 (.load .one (.op .add [vv cbkOr1, .const 8])))
  (.seq (.assign .local cbkOb (.load .one (.op .add [vv cbkQ, .const 8])))
  (.seq (.assign .local cbkOpp (.load .one (vv cbkOb)))
  (.seq (.assign .local cbkNpp (.load .one (vv cbkOpp)))
  (guardP cbkNpp 56
  (.seq (.assign .local cbkOcb (.load .one (.op .add [vv cbkQ, .const 16])))
  (.seq (.assign .local cbkOrd (.load .one (vv cbkOcb)))
  (.seq (.assign .local cbkOs (.load .one (vv cbkOrd)))
  (.seq (.assign .local cbkNsl (.load .one (vv cbkOs)))
  (guardP cbkNsl 56
  (.seq (.assign .local cbkOrc (.load .one (.op .add [vv cbkOrd, .const 8])))
  (.seq (.assign .local cbkNrc (.load .one (vv cbkOrc)))
  (.ite (.cmp .equal (vv cbkNrc) (.const 1))
  (.seq (.assign .local cbkRc0 (.load .one (.op .add [vv cbkOrc, .const 8])))
  (.ite (.cmp .equal (vv cbkRc0) (.const 0))
  (.ite (.cmp .equal (vv cbkNsl) (.const 0)) hang
  (.seq (.assign .local cbkS0p (.load .one (.op .add [vv cbkOs, .const 8])))
  (.seq (.assign .local cbkTag (.load .one (vv cbkS0p)))
  (.ite (.cmp .equal (vv cbkTag) (.const 0))
  (.seq (.assign .local cbkOms (.load .one (.op .add [vv cbkOcb, .const 8])))
  (.seq (.assign .local cbkNcl (.load .one (vv cbkOms)))
  (.ite (.cmp .equal (vv cbkNcl) (.const 1))
  (.seq (.assign .local cbkOp (.load .one (.op .add [vv cbkOms, .const 8])))
  (.seq (.assign .local cbkNi (.load .one (vv cbkOp)))
  (guardP cbkNi 56
  (.seq (.assign .local cbkOq (.load .one (.op .add [vv cbkOp, .const 8])))
  (.seq (.assign .local cbkNq (.load .one (vv cbkOq)))
  (.seq (.assign .local cbkMb (.load .one (.op .add [vv cbkOp, .const 16])))
  (.ite (.cmp .equal (vv cbkMb) (.const 1))
  (.seq (.assign .local cbkOa (.load .one (.op .add [vv cbkOp, .const 24])))
  (.seq (.assign .local cbkInd (.load .one (vv cbkOa)))
  (.seq (.assign .local cbkLv (.load .one (.op .add [vv cbkOa, .const 8])))
  (.seq (.assign .local cbkPa (.load .one (.op .add [vv cbkOa, .const 16])))
  (.seq (.assign .local cbkNd (.load .one (vv cbkPa)))
  (guardP cbkNd 56
  (.seq (.assign .local cbkNpc (.load .one (.op .add [vv cbkOa, .const 24])))
  (guardP cbkNpc 62
  (.seq (.assign .local cbkOcp (.load .one (.op .add [vv cbkQ, .const 24])))
  (.seq (.assign .local cbkOo (.load .one (vv cbkOcp)))
  (.seq (.assign .local cbkNoo (.load .one (vv cbkOo)))
  (.seq (.call (some (some (.local, cbkX), none)) fKf3 [vv cbkOo, .const 0, vv cbkNoo])
  (.seq (.assign .local cbkOn (.load .one (.op .add [vv cbkOcp, .const 8])))
  (.seq (.assign .local cbkNtb (.load .one (vv cbkOn)))
  (guardP cbkNtb 58
  (.seq (.assign .local cbkTgt (.load .one (.op .add [vv cbkOrr1, .const 24])))
  (.ite (.cmp .equal (vv cbkTgt) (.const 0))
  (.seq (.assign .local cbkNp1 (.load .one (.op .add [vv cbkO1, .const 16])))
  (.seq (.assign .local cbkRs1 (.load .one (.op .add [vv cbkO1, .const 32])))
  (.seq (.assign .local cbkNqq (.load .one (vv cbkTq)))
  (guardP cbkNqq 1
  (.seq (.call (some (some (.local, cbkR), none)) fCtb [vv cbkO1, vv cbkOrr1, vv cbkOpp, vv cbkOn, vv cbkNtb, vv cbkOq, vv cbkNq, vv cbkLv, vv cbkOlw, vv cbkTy0, vv cbkOpp, vv cbkNpp, vv cbkPa, vv cbkNd, vv cbkNm1, vv cbkOs, vv cbkNsl, vv cbkOm1, vv cbkNct, vv cbkNi, vv cbkInd, vv cbkNpc, vv cbkNp1, vv cbkRs1, vv cbkTq, vv cbkOms, vv cbkNcl])
  (cbkInst C))))))
  hang)))))))))))))))))
  hang)))))))
  hang)))
  hang))))
  hang))
  hang))))))))))))))))))))))))))))))))))
  hang))))))
  hang)))

structure CBKCodes (mode : ConLeche.CheckMode) (C : Ctx) : Prop where
  cnn : CNNCodes C
  cnk : CNKCodes C
  mok : MOKCodes C
  cfa : C.code.lookup fCfa = some (cfaParams.map (fun p => (p, ShapeHOL.one)), cfaBody, .one)
  fs : C.code.lookup WC.fFs = some ([(WC.fsT, ShapeHOL.one)], WC.fsBody, .one)
  pir : C.code.lookup ExM.fPir = some ([(pFu, .one), (pH, .one)], ExM.pirBody, .one)
  rm : C.code.lookup fRmFill = some (rmParams.map (fun p => (p, ShapeHOL.one)), rmBody C, .one)
  bi : BICodes C
  nm : C.code.lookup fNmFill = some (nmParams.map (fun p => (p, ShapeHOL.one)), nmBody, .one)
  biS : C.code.lookup fBlockIsRec = some (biParams.map (fun p => (p, ShapeHOL.one)), biBody C, .one)
  cps : CPSCodes mode C
  cfh : CFHCodes C
  bt : BTCodes C
  bta : C.code.lookup fBta = some (btaParams.map (fun p => (p, ShapeHOL.one)), btaBody C, .one)
  kf1 : C.code.lookup fKf1 = some (kf1Params.map (fun p => (p, ShapeHOL.one)), kf1Body, .one)
  kf2 : C.code.lookup fKf2 = some (kf2Params.map (fun p => (p, ShapeHOL.one)), kf2Body, .one)
  kf3 : C.code.lookup fKf3 = some (kf3Params.map (fun p => (p, ShapeHOL.one)), kf3Body, .one)
  ctb : CTBCodes mode C
  rin : RINCodes C
  ria : C.code.lookup fRia = some (riaParams.map (fun p => (p, ShapeHOL.one)), riaBody, .one)
  cp : C.code.lookup fCpy = some (Decl.cpParams.map (fun p => (p, ShapeHOL.one)), cpyBody, .one)
  ms : C.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one)
  mi : C.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one)
  tw : C.code.lookup fTw = some (twParams.map (fun p => (p, ShapeHOL.one)), twBody C, .one)
  self : C.code.lookup fCbk = some (cbkParams.map (fun p => (p, ShapeHOL.one)), cbkBody C, .one)

/-- The twin's steps of `checkBlock` before the pass: the members at their telescopes, the flush, official's
`is_rec`. -/
def cbkPre (mode : ConLeche.CheckMode) (fe : IFEnv) (p₀ : BlockShape) : AM (List MemberShape × Bool) := do
  let ms ← reduceMembers mode fe p₀.nP p₀.members
  flushCaches
  let isRec ← blockIsRec p₀
  pure (ms, isRec)

theorem pairsRep_len {H : List (BitVec 64)} {o : Nat} {ps : List (Nat × Nat)} (h : PairsRep H o ps) :
    ps.length < H.length := by
  have h0 := (List.getElem?_eq_some_iff.mp h.1).1
  rcases Nat.eq_zero_or_pos ps.length with he | hp
  · omega
  · have := (List.getElem?_eq_some_iff.mp (h.2.1 (ps.length - 1) (by omega)).1).1; omega

/-- **The twin-run facts** `checkBlock` relies on, each at the twin's states the port's run reaches: the walk's
context at a well-formed store, the pass after `cbkPre` from a checking state (con-ron's `CheckOK` at a
well-formed environment related to the index), the tables at a well-formed store. -/
structure CBKRun (mode : ConLeche.CheckMode) (C : Ctx) (block : List IConstantInfo) (p₀ : BlockShape) (ms0 : MemberShape) (rc : RecShape) : Prop where
  bn : ∀ (s0 : LIdx) (ip : Bool) (s s1 : AState) (ctx : NestCtx) (holes : List EIdx), StateOK s → Ext C.St s.store →
    (denoteL s.store.ls s0).isSome = true →
    blockNestCtx { p₀ with resSort := s0, isProp := ip } s = .ok ((ctx, holes), s1) →
    (∃ vs, denoteLs s1.store.lss ctx.lvls = some vs) ∧ ctx.params.length < 2 ^ 56 ∧ holes.length < 2 ^ 56
  /-- The generated recursor type denotes, along the twin's run from a checking state (`crt_discharge`). -/
  crt : ∀ (env : ConLeche.Env) (s0 : AState) (ms : List MemberShape) (isRec : Bool) (s : AState) (q : BlockPass)
    (s5 : AState) (Q : List IProjTable) (s6 s3 : AState) (m : TargetMajor) (g0 : ClassGen) (cvRis : List IConstantVal)
    (s7 : AState) (pre : List EIdx) (s1 s' : AState) (cv : IConstantVal),
    CheckOK false env C.fe s0 → ConLeche.EnvWF env → ConRon.Bridge.Inductives.EnvRel env C.fe s0.store →
    Ext C.St s0.store → cbkPre mode C.fe p₀ s0 = .ok ((ms, isRec), s) →
    checkBlockPass mode C.fe { p₀ with members := ms } isRec s = .ok (q, s5) →
    blockTables p₀ p₀.members s5 = .ok (some Q, s6) → m ∈ q.cls → rc ∈ q.p.recs →
    ctbPre mode q.env1 q.p s6 = .ok ((), s3) →
    gaPre mode (consBlockCtors q.p.nP q.p.ctorGroups q.env1) q.p q.params q.tbl q.rd m block s3 =
      .ok ((g0, cvRis), s7) →
    g0.prefixBinders s7 = .ok (some pre, s1) →
    classRecTyOk mode (consBlockCtors q.p.nP q.p.ctorGroups q.env1) { g0 with pre := pre } q.p.k rc rc.cvR 0 s1 =
      .ok (cv, s') → (denoteE s'.store cv.type).isSome = true
  tables : ∀ (s : AState) (Q : List IProjTable) (s' : AState), StateOK s → Ext C.St s.store →
    blockTables p₀ p₀.members s = .ok (some Q, s') → ∀ t ∈ Q, NewTblDen t s'.store ∧
      (∃ ks : List ConLeche.Name, ∃ hkl : ks.length = t.levelParams.length,
        ∀ j (hj : j < t.levelParams.length), denoteN s'.store.ns t.levelParams[j] = some (ks[j]'(by rw [hkl]; exact hj))) ∧
      t.levelParams.length < 2 ^ 59 ∧ t.numParams < 2 ^ 62 ∧ t.numFields < 2 ^ 63 ∧ t.bodies.size < 2 ^ 58

section
variable {σ : Type}

theorem cbk_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cbkLocals → (ctxEnv C ++ cbkParams.zip vals).get x = none :=
  Knot.params_none C cbkLocals cbkParams vals (by decide) (by decide)

set_option maxHeartbeats 64000000 in
/-- **`checkBlock`**: one member, one recursor at it, unnested. -/
theorem cbk_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hpl : C.saved = none) (hc : CBKCodes mode C) (hf : ConPanqueque.Front.FrontOK C)
    (hg : TblGate C.fe) (hF : FlagsOK C.fe) (hL : LitsPinned C.fe C.pins)
    (heqS : ∀ (C' : Ctx), SameLay C C' → CtxOK C' → ∀ (H : List (BitVec 64)) (u v : LIdx) (s : AState)
      (lu lv : ConLeche.Level), denoteL s.store.ls u = some lu → denoteL s.store.ls v = some lv → CachesOK s →
      SpecR (σ := σ) (Pre (ctxH C' H) s [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s (lvlEq? u v)
        (fun o w s' st => LLeq.PostOB (ctxH C' H) o w s' st))
    (block : List IConstantInfo) (p₀ : BlockShape) (ms0 : MemberShape) (hms : p₀.members = [ms0]) (rc : RecShape)
    (hrecs : p₀.recs = [rc]) (hsp : SplitOK p₀ block) (osh : Nat) (hsh : ShapeRep C C.H osh p₀)
    (hnP : p₀.nP < 2 ^ 55) (hlp : ms0.cvT.levelParams.length < 2 ^ 58) (hni : ms0.nIdx < 2 ^ 56)
    (hcl : ms0.ctors.length < 2 ^ 58) (hnf : ∀ c ∈ ms0.ctors, p₀.nP + c.2 < 2 ^ 56)
    (hmI : rc.mI < 2 ^ 56) (hrP : rc.rP < 2 ^ 61) (hrl : rc.rules.length < 2 ^ 58)
    (hrlp : rc.cvR.levelParams.length < 2 ^ 59)
    (ks : List ConLeche.Name) (hkl : ks.length = ms0.cvT.levelParams.length)
    (hks : ∀ j (hj : j < ms0.cvT.levelParams.length), denoteN C.St.ns ms0.cvT.levelParams[j] = some (ks[j]'(by omega)))
    (kr : List ConLeche.Name) (hkr : kr.length = rc.cvR.levelParams.length)
    (hkrs : ∀ j (hj : j < rc.cvR.levelParams.length), denoteN C.St.ns rc.cvR.levelParams[j] = some (kr[j]'(by omega)))
    (hdd : CVDen ms0.declared C.St) (hcs : ∀ c ∈ ms0.ctors, CVDen c.1 C.St ∧ SumCtorOK C p₀.nP c)
    (hrd : CVDen rc.cvR C.St) (hrun : CBKRun mode C block p₀ ms0 rc) (s : AState)
    (hck : ∃ env, CheckOK false env C.fe s ∧ ConLeche.EnvWF env ∧
      ConRon.Bridge.Inductives.EnvRel env C.fe s.store) :
    SpecR (σ := σ) (Pre C s (cbkParams.zip [cellA C osh])) (cbkBody C) s (checkBlock mode C.fe block p₀) (PostBlk C) := by
  refine specR_prologue (postBlk_locals C) (cbk_none C _) ?_
  refine specR_atEntry fun t00 ht00 => ?_
  have hx00 : Ext C.St s.store := ht00.sr.floor
  obtain ⟨env, hck0, henv0, hrel0⟩ := hck
  simp only [checkBlock]
  obtain ⟨⟨om, hom, hM⟩, ⟨orl, horl, hR⟩, hnP0, hel0, hrs0, hlg0, hip0⟩ := hsh
  have hM0 := hM
  obtain ⟨hml0, hmp⟩ := hM0
  obtain ⟨omr, homr, hmr⟩ := hmp 0 (by simp [hms])
  simp only [hms, List.getElem_cons_zero] at hmr hml0
  have hmr0 := hmr
  obtain ⟨⟨oc, hoc, hcv⟩, ⟨od, hod, hcvd⟩, hni0, ⟨oct, hoct, hctr⟩⟩ := hmr0
  have hR0 := hR
  obtain ⟨hrl0, hrp⟩ := hR0
  obtain ⟨orr, horr, hrr⟩ := hrp 0 (by simp [hrecs])
  simp only [hrecs, List.getElem_cons_zero] at hrr hrl0
  refine UD.specR_heapLoadI' (C := C) cbkOm _ osh _ hom (by decide) (by simp +decide [sev, Env.get, cbkParams, ctxEnv]) ?_
  refine UD.specR_heapLoadI' (C := C) cbkNm0 (vv cbkOm) om _ hml0 (by decide) (by simp [sev, Env.get_cons]) ?_
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun _ => ?_) (fun h => absurd h (by decide))
  refine UD.specR_heapLoadI' (C := C) cbkOmr _ (om + 1 + 0) _ homr (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C om) ?_
  refine UD.specR_heapLoadI' (C := C) cbkOct _ (omr + 3) _ hoct (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C omr 3) ?_
  refine UD.specR_heapLoadI' (C := C) cbkNct (vv cbkOct) oct _ hctr.1 (by decide) (by simp [sev, Env.get_cons]) ?_
  refine UD.specR_heapLoadI' (C := C) cbkOrl _ (osh + 1) _ horl (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, cbkParams, ctxEnv]; exact cellA_add8 C osh) ?_
  refine UD.specR_heapLoadI' (C := C) cbkNrl (vv cbkOrl) orl _ hrl0 (by decide) (by simp [sev, Env.get_cons]) ?_
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun _ => ?_) (fun h => absurd h (by decide))
  refine UD.specR_heapLoadI' (C := C) cbkOrr _ (orl + 1 + 0) _ horr (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C orl) ?_
  have hcl0 : ∀ m ∈ p₀.members, m.ctors.length < 2 ^ 58 := fun m hm => by
    simp only [hms, List.mem_singleton] at hm; subst hm; exact hcl
  refine specR_congr (m' := (pure (nameNodup ((flatCtors p₀.members).map (·.1.name)) &&
      nameNodup (p₀.members.map (·.cvT.name))) : AM Bool) >>= fun b =>
      if (!b) = true then fail (CheckError.invalid "direct rec: duplicate constructor") else _)
    (by rw [pure_bind, Bool.not_and]; rfl) ?_
  refine specR_callNIH (C := C) cbkX fCnk cnkParams [vv cbkOm, vv cbkNm0] (cnkBody C)
    [cellA C om, BitVec.ofNat 64 1] (by decide) rfl (by decide) hc.cnk.self
    ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], trivial⟩
    (fun a w s' st => (pure (nameNodup ((flatCtors p₀.members).map (·.1.name)) &&
      nameNodup (p₀.members.map (·.cvT.name))) : AM Bool) s = .ok (a, s') ∧ PostB C a w s' st)
    (fun r w s' _ => r = (nameNodup ((flatCtors p₀.members).map (·.1.name)) &&
      nameNodup (p₀.members.map (·.cvT.name))) ∧ s' = s ∧ w = boolW r)
    (fun r w s' st ⟨hrun, H', hp', hw, hsr⟩ => by
      obtain ⟨e1, e2⟩ := AM.pure_ok hrun
      exact ⟨H', hp', ⟨e1, e2, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu cnkParams _ rfl hlk)
      (by
        have h := cnk_spec (σ := σ) C hok hc.cnk p₀.members om hM (by simp [hms]) hcl0 C.H (List.prefix_refl _) s
        simp only [hms, List.length_singleton] at h ⊢
        exact h)))
    (fun b w s1 H1 hp1 ⟨eb, es1, hw⟩ => ?_)
  subst hw es1
  have hp1' : C.H <+: H1 := hp1
  cases hb : b
  · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, boolW])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, boolW])
    (fun h => absurd rfl h) (fun _ => ?_)
  have hnd : (ms0.ctors.map (·.1.name)).Nodup := by
    have h1 : nameNodup ((flatCtors p₀.members).map (·.1.name)) = true := by
      rw [eb] at hb; exact (Bool.and_eq_true _ _ ▸ hb).1
    rw [hms, flatCtors_cons] at h1
    simpa [flatCtors] using nameNodup_nodup h1
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hok1 := ctxOK_H hok H1
  simp only [pinBoolTrue, pinBoolFalse, bind_assoc]
  refine specR_pinAtI hok1 PIN_BOOL_TRUE (by decide) cbkBt (by decide) ?_
  refine specR_pinAtI hok1 PIN_BOOL_FALSE (by decide) cbkBf (by decide) ?_
  refine specR_callPure (C := ctxH C H1) cbkX fMok mokParams [vv cbkOm, .const 0, vv cbkNm0, vv cbkBt, vv cbkBf]
    (mokBody C) [cellA C om, BitVec.ofNat 64 0, BitVec.ofNat 64 [ms0].length,
      Enc.idxW ((ctxH C H1).pins.names[PIN_BOOL_TRUE]'(by rw [hok1.pinsRel.1]; decide)),
      Enc.idxW ((ctxH C H1).pins.names[PIN_BOOL_FALSE]'(by rw [hok1.pinsRel.1]; decide))] () (by decide) rfl
    (by decide) (by ctx_tr hc.mok.self)
    ⟨by simp +decide [sev, Env.get_cons], by simp [sev], by simp +decide [sev, Env.get_cons],
      by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], trivial⟩
    (PostKF (ctxH C H1) s1 (MembersOk (ctxH C H1).fe ((ctxH C H1).pins.names[PIN_BOOL_TRUE]'(by rw [hok1.pinsRel.1]; decide))
      ((ctxH C H1).pins.names[PIN_BOOL_FALSE]'(by rw [hok1.pinsRel.1]; decide)) ([ms0].drop 0)))
    (fun _ _ _ H' => H' = H1 ∧ MembersOk C.fe ((ctxH C H1).pins.names[PIN_BOOL_TRUE]'(by rw [hok1.pinsRel.1]; decide))
      ((ctxH C H1).pins.names[PIN_BOOL_FALSE]'(by rw [hok1.pinsRel.1]; decide)) p₀.members)
    (fun a w s' st ⟨_, hP, hsr⟩ => ⟨H1, List.prefix_refl _, ⟨rfl, by rw [hms]; exact hP⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu mokParams _ rfl hlk)
      (mok_spec (ctxH C H1) hok1 (by ctx_tr hc.mok) [ms0] om (by rw [← hms]; exact ptrsRep_mono hp1' (fun _ _ h => memberRep_mono hp1' h) hM)
        (by simp) _ _ _ 0 s1 rfl (Nat.zero_le _)))
    (fun w H1' hpH ⟨eH, hmok⟩ => ?_)
  subst H1'
  rw [membersOk_contains hmok]
  simp only [Bool.false_eq_true, ↓reduceIte]
  have hfresh : C.fe.find? ms0.declared.name = none := (hmok ms0 (by simp [hms])).2.2
  simp only [hms]
  have hrm := rm_spec (σ := σ) mode C.fe p₀.nP C hok hpl hc.fs hc.pir hc.rm p₀.members om hM _ 0 H1 s1 rfl (by omega) hp1'
  simp only [hms, List.drop_zero, List.length_singleton] at hrm
  refine specR_callNIH (C := ctxH C H1) cbkX fRmFill rmParams [vv cbkOm, .const 0, vv cbkNm0] (rmBody C)
    [cellA C om, BitVec.ofNat 64 0, BitVec.ofNat 64 1] (by decide) rfl (by decide) (by ctx_tr hc.rm)
    ⟨by simp +decide [sev, Env.get_cons], by simp [sev], by simp +decide [sev, Env.get_cons], trivial⟩
    (fun r _ s' st => reduceMembers mode C.fe p₀.nP [ms0] s1 = .ok (r, s') ∧ r = [ms0] ∧ ∃ H', H1 <+: H' ∧ SR (ctxH C H') s' st)
    (fun r _ s' _ => reduceMembers mode C.fe p₀.nP [ms0] s1 = .ok (r, s') ∧ r = [ms0])
    (fun r w s' st ⟨hrr, hr, H', hp', hsr⟩ => ⟨H', hp', ⟨hrr, hr⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu rmParams _ rfl hlk)
      hrm))
    (fun r w s2 H2 hp2 ⟨hrmr, er⟩ => ?_)
  subst er
  have hp2' : H1 <+: H2 := hp2
  have hok2 := ctxOK_H hok H2
  refine specR_flushTopI hok2 hpl false flushCaches rfl (by decide) ?_
  generalize hsF : flushedS false s2 = s3
  have hbi := bi_spec (σ := σ) C hok hc.bi hc.nm p₀ om hM H2 (hp1'.trans hp2') s3
  simp only [hms, List.length_singleton] at hbi
  refine specR_callNIH (C := ctxH C H2) cbkIr fBlockIsRec biParams [vv cbkOm, vv cbkNm0] (biBody C)
    [cellA C om, BitVec.ofNat 64 1] (by decide) rfl (by decide) (by ctx_tr hc.biS)
    ⟨by simp +decide [sev, Env.get_cons, Env.kill], by simp +decide [sev, Env.get_cons, Env.kill], trivial⟩
    (fun r w s' st => blockIsRec p₀ s3 = .ok (r, s') ∧ PostB (ctxH C H2) r w s' st)
    (fun r w s' _ => blockIsRec p₀ s3 = .ok (r, s') ∧ w = boolW r)
    (fun r w s' st ⟨hbr, H', hp', hw, hsr⟩ => ⟨H', hp', ⟨hbr, hw⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu biParams _ rfl hlk)
      hbi))
    (fun isRec w s4 H4 hp4 ⟨hbir, hw⟩ => ?_)
  subst hw
  have hpre : cbkPre mode C.fe p₀ s1 = .ok ((p₀.members, isRec), s4) := by
    unfold cbkPre
    rw [hms, am_bind_run hrmr, am_bind_run (show flushCaches s2 = .ok ((), s3) by rw [← hsF]; rfl), am_bind_run hbir]
    rfl
  have hp4' : H2 <+: H4 := hp4
  rw [show ({ p₀ with members := [ms0] } : BlockShape) = p₀ by rw [← hms]]
  have hp14 : C.H <+: H4 := hp1'.trans (hp2'.trans hp4')
  have hok4 := ctxOK_H hok H4
  refine specR_atEntry fun t4 ht4 => ?_
  have hx4 : Ext C.St s4.store := ht4.sr.floor
  have hsh4 : ShapeRep C H4 osh p₀ := shapeRep_mono hp14 ⟨⟨om, hom, hM⟩, ⟨orl, horl, hR⟩, hnP0, hel0, hrs0, hlg0, hip0⟩
  refine specR_callNC (C := ctxH C H4) cbkQ fCps cpsParams [vv cbkSh, vv cbkIr] (cpsBody C) [cellA C osh, boolW isRec]
    (by decide) rfl (by decide) (by ctx_tr hc.cps.self)
    ⟨by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv], by simp +decide [sev, Env.get_cons], trivial⟩
    (fun a w s' st => checkBlockPass mode C.fe p₀ isRec s4 = .ok (a, s') ∧ PostCPS (ctxH C H4) p₀ a w s' st)
    (fun q w s' C' => checkBlockPass mode C.fe p₀ isRec s4 = .ok (q, s') ∧ ∃ EH envM H o,
      C' = ctxNew (ctxH C H4) q.env1 EH envM H ∧ C.EH <+: EH ∧ H4 <+: H ∧ CtxOK (ctxNew (ctxH C H4) q.env1 EH envM H) ∧
      TblGate q.env1 ∧ FlagsOK q.env1 ∧ LitsPinned q.env1 C.pins ∧
      (∀ n, (∀ ms ∈ p₀.members, ms.declared.name ≠ n) → q.env1.find? n = C.fe.find? n) ∧ w = cellA C o ∧
      (∃ o1, H[o]? = some (cellA C o1) ∧ ShapeRep C H o1 q.p) ∧
      (∃ s0 ip, q.p = { p₀ with resSort := s0, isProp := ip } ∧ ∃ l, denoteL s'.store.ls s0 = some l) ∧
      (∃ ob opp, H[o + 1]? = some (cellA C ob) ∧ H[ob]? = some (cellA C opp) ∧ BlkAt H opp (q.params.map Enc.idxW)) ∧
      (∃ ocb ord oms, H[o + 2]? = some (cellA C ocb) ∧ H[ocb]? = some (cellA C ord) ∧ ClassReadRep C H ord q.rd ∧
        H[ocb + 1]? = some (cellA C oms) ∧ TMBlk C H oms q.params q.cls) ∧
      (∃ ocp oo on outs, H[o + 3]? = some (cellA C ocp) ∧ H[ocp]? = some (cellA C oo) ∧ PRep C H oo (OutsRep C) outs ∧
        q.kinds = nestOutKinds outs ∧ H[ocp + 1]? = some (cellA C on) ∧ PRep C H on (NfRep C) q.tbl))
    (fun a w s' st ⟨hrun', EH, envM, H, o, h1, h2, h3, h4, h5⟩ => ⟨_, ⟨hrun', EH, envM, H, o, rfl, h1, h2, h3, h5⟩, h4⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu cpsParams _ rfl hlk)
      (cps_spec mode ra (ctxH C H4) hok4 hs hpl (by ctx_tr hc.cps) hg hF hL heqS p₀ (by simp [hms]) osh hsh4 isRec
        hnP (by simp [hms]) (by simp [hrecs])
        (fun ms hm => by
          simp only [hms, List.mem_singleton] at hm; subst hm
          exact ⟨by omega, hni, hcl, ⟨ks, hkl, hks⟩, hdd, hfresh, hcs⟩)
        (fun r hr => by simp only [hrecs, List.mem_singleton] at hr; subst hr; exact ⟨hmI, hrP⟩) hrun.bn s4)))
    (fun q w s5 C5 ⟨hqrun, EH5, envM5, H5, o, eC, hpE5, hp5, hok5, hg5, hF5, hL5, hf5, ew, ⟨o1, ho1, hsh1⟩,
      ⟨s0, ip, hqp, l0, hl0⟩, ⟨ob, opp, hob, hopp, hppb⟩, ⟨ocb, ord, oms, hocb, hord, hcrd, homs, htm⟩,
      ⟨ocp, oo, on, outs, hocp, hoo, houts, hkinds, hon, htbl⟩⟩ => ?_)
  subst eC ew
  have hqrun' : checkBlockPass mode C.fe { p₀ with members := p₀.members } isRec s4 = .ok (q, s5) := hqrun
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN5 => ?_)
  have hH5 : H5.length < 2 ^ 61 := by
    have := hok.heapLay; have h' : H5.length ≤ C.HN := hHN5; omega
  have hrd5 := checkBlockPass_rd hqrun
  rw [hqp] at hrd5
  have hrdB := hrd5 rc (by simp [hrecs])
  have hrcB : ∀ c ∈ q.rd.recCls, c < 2 ^ 63 := fun c hc => by have := hrdB.1 c hc; omega
  have hcb : ∀ sl ∈ q.rd.slots, ∀ c C' ihs, sl = .minor c C' ihs → c < 2 ^ 63 ∧ ihs.length < 2 ^ 63 := by
    intro sl hsl c C' ihs hm
    refine ⟨by have := hrdB.2 sl hsl c C' ihs hm; omega, ?_⟩
    obtain ⟨os, orc, -, ⟨ps, hpl, -, hps⟩, -, -⟩ := hcrd
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hsl
    obtain ⟨op, -, hrep⟩ := hps k hk
    rw [hm] at hrep
    obtain ⟨-, -, -, oi, -, hpr⟩ := hrep
    have := pairsRep_len hpr; omega
  have hel : ∀ e ∈ q.tbl, e.ds.length < 2 ^ 61 := fun e he => by
    obtain ⟨os, hosl, -, hos⟩ := htbl
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    obtain ⟨-, -, ⟨od, -, hb⟩, -⟩ := hos i hi (by omega)
    have := ConPanqueque.T.blkAt_len hb; simp only [List.length_map] at this; omega
  have hp5' : H4 <+: H5 := hp5
  have hpC5 : C.H <+: H5 := hp14.trans hp5'
  set C5 := ctxNew (ctxH C H4) q.env1 EH5 envM5 H5 with hC5
  refine specR_callPure (C := C5) cbkX fCfa cfaParams [vv cbkOm, .const 0, vv cbkNm0] cfaBody
    [cellA C om, BitVec.ofNat 64 0, BitVec.ofNat 64 [ms0].length] () (by decide) rfl (by decide)
    (by ctx_tr hc.cfa)
    ⟨by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv], by simp [sev],
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv], trivial⟩
    (PostKF C5 s5 (∀ m ∈ [ms0].drop 0, ∀ c ∈ m.ctors, C5.fe.find? c.1.name = none))
    (fun _ _ _ H' => H' = H5 ∧ ∀ c ∈ ms0.ctors, q.env1.find? c.1.name = none)
    (fun a w s' st ⟨_, hP, hsr⟩ => ⟨H5, List.prefix_refl _, ⟨rfl, fun c hc' => hP ms0 (by simp) c hc'⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu cfaParams _ rfl hlk)
      (cfa_spec C5 hok5 ⟨by ctx_tr hc.cfh, by ctx_tr hc.cfa⟩ [ms0] om
        (by rw [← hms]; exact ptrsRep_mono hpC5 (fun _ _ h => memberRep_mono hpC5 h) hM) (by simp)
        (fun m hm => by simp only [List.mem_singleton] at hm; subst hm; exact hcl) _ 0 s5 rfl (Nat.zero_le _)))
    (fun w H' _ ⟨eH, hcnew⟩ => ?_)
  subst H'
  refine specR_atEntry fun t5 ht5 => ?_
  have hx5 : Ext C.St s5.store := ht5.sr.floor
  refine specR_invRaise (R' := PostBlk (ctxSt C s5.store)) ?_ (fun a w s' t hx h => postBlk_lower (C := C) hx a w s' t h)
  set C5' := ctxSt C5 s5.store with hC5'
  have hok5' : CtxOK C5' := ctxOK_St hok5 _
  refine UD.specR_heapLoadI' (C := C5') cbkNp _ (osh + 2) _ (ConPanqueque.T.Decl.get_prefix hnP0.1 hpC5) (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv]; exact cellA_add_ofNat C osh 2) ?_
  have hbt := bta_spec (σ := σ) ra C5' hok5' ⟨by ctx_tr hc.bt, by ctx_tr hc.bta⟩ p₀ om
    (ptrsRep_mono hpC5 (fun _ _ h => memberRep_mono hpC5 h) hM) (by rw [hms]; simp) (by omega)
    (fun ms hm => by rw [hms, List.mem_singleton] at hm; subst hm; simp [BlockShape.lps, hms])
    (fun ms hm => by rw [hms, List.mem_singleton] at hm; subst hm; omega)
    (fun ms hm => by rw [hms, List.mem_singleton] at hm; subst hm; exact fun c hc' => by have := hnf c hc'; omega)
    (fun ms hm => by rw [hms, List.mem_singleton] at hm; subst hm; omega) _ 0 C5'.H s5 rfl (Nat.zero_le _)
    (List.prefix_refl _)
  rw [List.drop_zero, show blockTables p₀ p₀.members = blockTables p₀ [ms0] by rw [hms]] at hbt
  refine specR_callNIH (C := C5') cbkTq fBta btaParams [vv cbkOm, .const 0, vv cbkNm0, vv cbkNp] (btaBody C)
    [cellA C om, BitVec.ofNat 64 0, BitVec.ofNat 64 p₀.members.length, BitVec.ofNat 64 p₀.nP] (by decide) rfl
    (by decide) (by ctx_tr hc.bta)
    ⟨by simp +decide [sev, Env.get_cons, Env.kill] <;> rfl, by simp +decide [sev, Env.get_cons, Env.kill],
      by simp +decide [sev, Env.get_cons, Env.kill, hms] <;> rfl, by simp +decide [sev, Env.get_cons, Env.kill], trivial⟩
    (fun a w s' st => blockTables p₀ [ms0] s5 = .ok (a, s') ∧ PostBTb C5' a w s' st)
    (fun o w s' H' => blockTables p₀ [ms0] s5 = .ok (o, s') ∧ ∃ Q ob, o = some Q ∧ w = cellA C ob ∧
      PRep C H' ob (fun H o t => TblVRep C H o t) Q)
    (fun a w s' st ⟨hr, Q, H', ob, h1, h2, h3, h4, h5⟩ => ⟨H', h2, ⟨hr, Q, ob, h1, h3, h4⟩, h5⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu btaParams _ rfl hlk) hbt))
    (fun o w s6 H6 hp6 ⟨hbrun, Q, oQ, eo, ew, hqQ⟩ => ?_)
  subst eo ew
  simp only [unwrapOr, pure_bind]
  have hp6' : H5 <+: H6 := hp6
  have hpC6 : C.H <+: H6 := hpC5.trans hp6'
  refine specR_atEntry fun t6 ht6 => ?_
  have hx56 : Ext s5.store s6.store := ht6.sr.floor
  refine specR_invRaise (R' := PostBlk (ctxSt (ctxSt C s5.store) s6.store)) ?_
    (fun a w s' t hx h => postBlk_lower (C := ctxSt C s5.store) hx a w s' t h)
  set C6 := ctxSt (ctxH C5' H6) s6.store with hC6
  have hok6 : CtxOK C6 := ctxOK_St (ctxOK_H hok5' H6) _
  have hx6 : Ext C.St s6.store := hx5.trans hx56
  have htab := hrun.tables s5 Q s6 ⟨ht5.sr.twf⟩ hx5 (by rw [hms]; exact hbrun)
  have hqpm : q.p.members = [ms0] := by rw [hqp]; exact hms
  have hmc : ∀ m ∈ q.cls, m.member = some 0 → m.ctors = ms0.ctors := fun m hm h0 => by
    obtain ⟨ms, hms', he⟩ := checkBlockPass_cls hqrun m hm 0 h0
    rw [hqpm] at hms'
    simp only [List.getElem?_cons_zero, Option.some.injEq] at hms'
    rw [he, hms']
  have hqpr : q.p.recs = [rc] := by rw [hqp]; exact hrecs
  have hsh6 := shapeRep_mono hp6' hsh1
  obtain ⟨⟨om1, hom1, hM1⟩, ⟨or1, hor1, hR1⟩, hnP1, hel1, hrs1, hlg1, hip1⟩ := hsh6
  obtain ⟨omr1, homr1, hmr1⟩ := hM1.2 0 (by simp [hqpm])
  simp only [hqpm, List.getElem_cons_zero] at hmr1
  obtain ⟨⟨oc1, hoc1, hcv1⟩, -, -, -⟩ := hmr1
  obtain ⟨wl1, hwl1, olp1, hwo1, hlpb1⟩ := hcv1.2.1
  obtain ⟨orr1, horr1, hrr1⟩ := hR1.2 0 (by simp [hqpr])
  simp only [hqpr, List.getElem_cons_zero] at hrr1
  refine UD.specR_heapLoadI' (C := C6) cbkO1 (vv cbkQ) o _ (ConPanqueque.T.Decl.get_prefix ho1 hp6') (by decide)
    (by simp +decide [sev, Env.get_cons, Env.kill] <;> rfl) ?_
  refine UD.specR_heapLoadI' (C := C6) cbkOm1 (vv cbkO1) o1 _ hom1 (by decide) (by simp [sev, Env.get_cons] <;> rfl) ?_
  refine UD.specR_heapLoadI' (C := C6) cbkOmr1 _ (om1 + 1 + 0) _ homr1 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C om1) ?_
  refine UD.specR_heapLoadI' (C := C6) cbkOc1 (vv cbkOmr1) omr1 _ hoc1 (by decide) (by simp [sev, Env.get_cons] <;> rfl) ?_
  refine UD.specR_heapLoadI' (C := C6) cbkOlw _ (oc1 + 1) _ hwl1 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C oc1) ?_
  rw [hwo1]
  refine UD.specR_heapLoadI' (C := C6) cbkTy0 _ (oc1 + 2) _ hcv1.2.2 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C oc1 2) ?_
  refine UD.specR_heapLoadI' (C := C6) cbkNm1 (vv cbkOc1) oc1 _ hcv1.1 (by decide) (by simp [sev, Env.get_cons] <;> rfl) ?_
  refine UD.specR_heapLoadI' (C := C6) cbkOr1 _ (o1 + 1) _ hor1 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C o1) ?_
  refine UD.specR_heapLoadI' (C := C6) cbkOrr1 _ (or1 + 1 + 0) _ horr1 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C or1) ?_
  refine UD.specR_heapLoadI' (C := C6) cbkOb _ (o + 1) _ (ConPanqueque.T.Decl.get_prefix hob hp6') (by decide)
    (by simp +decide [sev, Env.get_cons, Env.kill]; exact cellA_add8 C o) ?_
  refine UD.specR_heapLoadI' (C := C6) cbkOpp (vv cbkOb) ob _ (ConPanqueque.T.Decl.get_prefix hopp hp6') (by decide) (by simp [sev, Env.get_cons] <;> rfl) ?_
  have hppb6 := blkAt_mono hppb hp6'
  have hnpp : H6[opp]? = some (BitVec.ofNat 64 q.params.length) := by simpa using hppb6.1
  refine UD.specR_heapLoadI' (C := C6) cbkNpp (vv cbkOpp) opp _ hnpp (by decide) (by simp [sev, Env.get_cons] <;> rfl) ?_
  refine specR_fact (fun t ht => inv_heapLen ht) (fun hHN => ?_)
  have hbpp := blkAt_len hok6 hHN hppb6
  simp only [List.length_map] at hbpp
  refine specR_guardI cbkNpp q.params.length 56 (by decide) (by simp [Env.get_cons]) (by omega) (fun hpml => ?_)
  refine UD.specR_heapLoadI' (C := C6) cbkOcb _ (o + 2) _ (ConPanqueque.T.Decl.get_prefix hocb hp6') (by decide)
    (by simp +decide [sev, Env.get_cons, Env.kill]; exact cellA_add_ofNat C o 2) ?_
  refine UD.specR_heapLoadI' (C := C6) cbkOrd (vv cbkOcb) ocb _ (ConPanqueque.T.Decl.get_prefix hord hp6') (by decide) (by simp [sev, Env.get_cons] <;> rfl) ?_
  obtain ⟨os, orc, hos, hsb, horc, hrcb⟩ := classReadRep_mono hp6' hcrd
  refine UD.specR_heapLoadI' (C := C6) cbkOs (vv cbkOrd) ord _ hos (by decide) (by simp [sev, Env.get_cons] <;> rfl) ?_
  obtain ⟨sps, hspl, hspb, hspr⟩ := hsb
  have hnsl : H6[os]? = some (BitVec.ofNat 64 q.rd.slots.length) := by simpa [hspl] using hspb.1
  refine UD.specR_heapLoadI' (C := C6) cbkNsl (vv cbkOs) os _ hnsl (by decide) (by simp [sev, Env.get_cons] <;> rfl) ?_
  have hbsl := blkAt_len hok6 hHN hspb
  simp only [List.length_map] at hbsl
  refine specR_guardI cbkNsl q.rd.slots.length 56 (by decide) (by simp [Env.get_cons]) (by omega) (fun hsl => ?_)
  refine UD.specR_heapLoadI' (C := C6) cbkOrc _ (ord + 1) _ horc (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C ord) ?_
  have hnrc : H6[orc]? = some (BitVec.ofNat 64 q.rd.recCls.length) := by simpa using hrcb.1
  refine UD.specR_heapLoadI' (C := C6) cbkNrc (vv cbkOrc) orc _ hnrc (by decide) (by simp [sev, Env.get_cons] <;> rfl) ?_
  have hbrc := blkAt_len hok6 hHN hrcb
  simp only [List.length_map] at hbrc
  by_cases hrc1 : q.rd.recCls.length = 1
  swap
  · refine specR_ifI _ 0 (by
      simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      intro h; apply hrc1
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega)] at this
      simpa using this) (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hrc1])
    (fun _ => ?_) (fun h => absurd h (by decide))
  have hrc0w := hrcb.2 0 (by simp [hrc1])
  simp only [List.getElem_map] at hrc0w
  refine UD.specR_heapLoadI' (C := C6) cbkRc0 _ (orc + 1 + 0) _ hrc0w (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C orc) ?_
  have hrc0b : q.rd.recCls[0]'(by omega) < 2 ^ 63 := hrcB _ (List.getElem_mem _)
  by_cases h0 : q.rd.recCls[0]'(by omega) = 0
  swap
  · refine specR_ifI _ 0 (by
      simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      intro h; apply h0
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega)] at this
      simpa using this) (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, h0])
    (fun _ => ?_) (fun h => absurd h (by decide))
  have hrc0 : q.rd.recCls = [0] := by
    apply List.ext_getElem (by simp [hrc1])
    intro i h1 h2
    have : i = 0 := by simp at h2; omega
    subst this; simpa using h0
  by_cases hsl0 : q.rd.slots.length = 0
  · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hsl0])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  refine specR_ifI _ 0 (by
      simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      intro h; apply hsl0
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega)] at this
      simpa using this) (fun h => absurd rfl h) (fun _ => ?_)
  have hsp0 := hspb.2 0 (by simp [hspl]; omega)
  simp only [List.getElem_map] at hsp0
  refine UD.specR_heapLoadI' (C := C6) cbkS0p _ (os + 1 + 0) _ hsp0 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C os) ?_
  obtain ⟨op0, hop0, hsrep⟩ := hspr 0 (by omega)
  have hop0' : sps[0]'(by omega) = op0 := by simpa [List.getElem?_eq_getElem (show 0 < sps.length by omega)] using hop0
  rw [hop0'] at hsp0 ⊢
  rcases hsle : q.rd.slots[0]'(by omega) with k0 | ⟨cm, cn, ihs⟩
  swap
  · rw [hsle] at hsrep
    refine UD.specR_heapLoadI' (C := C6) cbkTag (vv cbkS0p) op0 _ hsrep.1 (by decide) (by simp [sev, Env.get_cons] <;> rfl) ?_
    exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  rw [hsle] at hsrep
  refine UD.specR_heapLoadI' (C := C6) cbkTag (vv cbkS0p) op0 _ hsrep.1 (by decide) (by simp [sev, Env.get_cons] <;> rfl) ?_
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun _ => ?_) (fun h => absurd h (by decide))
  have hsl0' : q.rd.slots[0]? = some (.motive k0) := by rw [List.getElem?_eq_getElem (by omega), hsle]
  refine UD.specR_heapLoadI' (C := C6) cbkOms _ (ocb + 1) _ (ConPanqueque.T.Decl.get_prefix homs hp6') (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C ocb) ?_
  obtain ⟨tps, htpl, htpb, htpr⟩ := tmBlk_mono hp6' htm
  have hncl : H6[oms]? = some (BitVec.ofNat 64 q.cls.length) := by simpa [htpl] using htpb.1
  refine UD.specR_heapLoadI' (C := C6) cbkNcl (vv cbkOms) oms _ hncl (by decide) (by simp [sev, Env.get_cons] <;> rfl) ?_
  have hbcl := blkAt_len hok6 hHN htpb
  simp only [List.length_map] at hbcl
  by_cases hcl1 : q.cls.length = 1
  swap
  · refine specR_ifI _ 0 (by
      simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      intro h; apply hcl1
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega)] at this
      simpa using this) (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hcl1])
    (fun _ => ?_) (fun h => absurd h (by decide))
  have htp0 := htpb.2 0 (by simp [htpl]; omega)
  simp only [List.getElem_map] at htp0
  refine UD.specR_heapLoadI' (C := C6) cbkOp _ (oms + 1 + 0) _ htp0 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C oms) ?_
  obtain ⟨op, hop, htmr, hpfv, hnfs⟩ := htpr 0 (by omega)
  have hop' : tps[0]'(by omega) = op := by simpa [List.getElem?_eq_getElem (show 0 < tps.length by omega)] using hop
  rw [hop'] at htp0 ⊢
  set m := q.cls[0]'(by omega) with hm
  have hcls : q.cls = [m] := by
    apply List.ext_getElem (by simp [hcl1])
    intro i h1 h2
    have : i = 0 := by simp at h2; omega
    subst this; simp [hm]
  obtain ⟨oa, hoa, hind, hlv, ⟨od, hod, hdb⟩, hnpc, hni1, ⟨ocq, hocq, hcrq⟩, hmem, hmemb⟩ := htmr
  refine UD.specR_heapLoadI' (C := C6) cbkNi (vv cbkOp) op _ hni1.1 (by decide) (by simp [sev, Env.get_cons] <;> rfl) ?_
  refine specR_guardI cbkNi m.nIdx 56 (by decide) (by simp [Env.get_cons]) (by have := hni1.2; omega) (fun hni56 => ?_)
  refine UD.specR_heapLoadI' (C := C6) cbkOq _ (op + 1) _ hocq (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C op) ?_
  refine UD.specR_heapLoadI' (C := C6) cbkNq (vv cbkOq) ocq _ hcrq.1 (by decide) (by simp [sev, Env.get_cons] <;> rfl) ?_
  refine UD.specR_heapLoadI' (C := C6) cbkMb _ (op + 2) _ hmem (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C op 2) ?_
  rcases hmm0 : m.member with _ | t
  · exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, optNatW, hmm0])
      (fun h => absurd rfl h) (fun _ => specR_hangI)
  have ht62 := hmemb t hmm0
  by_cases ht0 : t = 0
  swap
  · refine specR_ifI _ 0 (by
      simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, optNatW, hmm0]
      intro h; apply ht0
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega)] at this
      omega) (fun h => absurd rfl h) (fun _ => specR_hangI)
  subst ht0
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, optNatW, hmm0])
    (fun _ => ?_) (fun h => absurd h (by decide))
  refine UD.specR_heapLoadI' (C := C6) cbkOa _ (op + 3) _ hoa (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C op 3) ?_
  refine UD.specR_heapLoadI' (C := C6) cbkInd (vv cbkOa) oa _ hind (by decide) (by simp [sev, Env.get_cons] <;> rfl) ?_
  refine UD.specR_heapLoadI' (C := C6) cbkLv _ (oa + 1) _ hlv (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C oa) ?_
  refine UD.specR_heapLoadI' (C := C6) cbkPa _ (oa + 2) _ hod (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C oa 2) ?_
  have hnd0 : H6[od]? = some (BitVec.ofNat 64 m.ds.length) := by simpa using hdb.1
  refine UD.specR_heapLoadI' (C := C6) cbkNd (vv cbkPa) od _ hnd0 (by decide) (by simp [sev, Env.get_cons] <;> rfl) ?_
  have hbd0 := blkAt_len hok6 hHN hdb
  simp only [List.length_map] at hbd0
  refine specR_guardI cbkNd m.ds.length 56 (by decide) (by simp [Env.get_cons]) (by omega) (fun hdl => ?_)
  refine UD.specR_heapLoadI' (C := C6) cbkNpc _ (oa + 3) _ hnpc.1 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C oa 3) ?_
  refine specR_guardI cbkNpc m.nPc 62 (by decide) (by simp [Env.get_cons]) (by have := hnpc.2; omega) (fun hnpc62 => ?_)
  refine UD.specR_heapLoadI' (C := C6) cbkOcp _ (o + 3) _ (ConPanqueque.T.Decl.get_prefix hocp hp6') (by decide)
    (by simp +decide [sev, Env.get_cons, Env.kill]; exact cellA_add_ofNat C o 3) ?_
  refine UD.specR_heapLoadI' (C := C6) cbkOo (vv cbkOcp) ocp _ (ConPanqueque.T.Decl.get_prefix hoo hp6') (by decide) (by simp [sev, Env.get_cons] <;> rfl) ?_
  have houts6 := pRep_mono hp6' (fun _ _ h => outsRep_mono hp6' h) houts
  have hnoo : H6[oo]? = some (BitVec.ofNat 64 outs.length) := by
    obtain ⟨ops, hopl, hopb, -⟩ := houts6; simpa [hopl] using hopb.1
  refine UD.specR_heapLoadI' (C := C6) cbkNoo (vv cbkOo) oo _ hnoo (by decide) (by simp [sev, Env.get_cons] <;> rfl) ?_
  refine specR_callPure (C := C6) cbkX fKf3 kf3Params [vv cbkOo, .const 0, vv cbkNoo] kf3Body
    [cellA C oo, BitVec.ofNat 64 0, BitVec.ofNat 64 outs.length] () (by decide) rfl (by decide) (by ctx_tr hc.kf3)
    ⟨by simp +decide [sev, Env.get_cons] <;> rfl, by simp [sev], by simp +decide [sev, Env.get_cons], trivial⟩
    (PostKF C6 s6 (∀ x ∈ outs.drop 0, ∀ y ∈ x, ∀ k ∈ y.1, k.flat = true))
    (fun _ _ _ H' => H' = H6 ∧ ∀ x ∈ outs, ∀ y ∈ x, ∀ k ∈ y.1, k.flat = true)
    (fun a w s' st ⟨_, hP, hsr⟩ => ⟨H6, List.prefix_refl _, ⟨rfl, fun x hx => hP x (by rw [List.drop_zero]; exact hx)⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu kf3Params _ rfl hlk)
      (kf3_spec C6 hok6 (by ctx_tr hc.kf1) (by ctx_tr hc.kf2) (by ctx_tr hc.kf3) outs oo houts6 _ 0 s6 rfl (Nat.zero_le _)))
    (fun w H' _ ⟨eH, hflat⟩ => ?_)
  subst H'
  refine UD.specR_heapLoadI' (C := C6) cbkOn _ (ocp + 1) _ (ConPanqueque.T.Decl.get_prefix hon hp6') (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C ocp) ?_
  have htbl6 := pRep_mono hp6' (fun _ _ h => nfRep_mono hp6' h) htbl
  obtain ⟨tbps, htbl_l, htbl_b, -⟩ := htbl6
  have hntb : H6[on]? = some (BitVec.ofNat 64 q.tbl.length) := by simpa [htbl_l] using htbl_b.1
  refine UD.specR_heapLoadI' (C := C6) cbkNtb (vv cbkOn) on _ hntb (by decide) (by simp [sev, Env.get_cons] <;> rfl) ?_
  have hbtb := blkAt_len hok6 hHN htbl_b
  simp only [List.length_map] at hbtb
  refine specR_guardI cbkNtb q.tbl.length 58 (by decide) (by simp [Env.get_cons]) (by omega) (fun htl => ?_)
  have hrr1k := hrr1
  obtain ⟨⟨ocr1, hocr1, hcvr1⟩, hrp1, hmi1, htg1, -, -⟩ := hrr1
  refine UD.specR_heapLoadI' (C := C6) cbkTgt _ (orr1 + 3) _ htg1.1 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C orr1 3) ?_
  by_cases htg0 : rc.tgt = 0
  swap
  · refine specR_ifI _ 0 (by
      simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
      intro h; apply htg0
      have := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by have := htg1.2; omega)] at this
      simpa using this) (fun h => absurd rfl h) (fun _ => specR_hangI)
  refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, htg0])
    (fun _ => ?_) (fun h => absurd h (by decide))
  refine UD.specR_heapLoadI' (C := C6) cbkNp1 _ (o1 + 2) _ hnP1.1 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C o1 2) ?_
  refine UD.specR_heapLoadI' (C := C6) cbkRs1 _ (o1 + 4) _ hrs1 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C o1 4) ?_
  obtain ⟨qps, hqQl, hqQb, hqQr⟩ := hqQ
  have hnqq : H6[oQ]? = some (BitVec.ofNat 64 Q.length) := by simpa [hqQl] using hqQb.1
  refine UD.specR_heapLoadI' (C := C6) cbkNqq (vv cbkTq) oQ _ hnqq (by decide)
    (by simp +decide [sev, Env.get_cons, Env.kill] <;> rfl) ?_
  have hbq := blkAt_len hok6 hHN hqQb
  simp only [List.length_map] at hbq
  refine specR_guardI cbkNqq Q.length 1 (by decide) (by simp [Env.get_cons]) (by omega) (fun hQ1 => ?_)
  have hnc_eq : q.p.numCtors = ms0.ctors.length := by simp [BlockShape.numCtors, numCtorsOf, hqpm]
  have hmc' : m.ctors = ms0.ctors := hmc m (by rw [hcls]; simp) hmm0
  have hnest : blockNestedBit q.p q.kinds = false := by
    have hfl : nestKindsFlat q.kinds = true := by
      rw [hkinds]
      simp only [nestKindsFlat, nestOutKinds, List.all_map, List.all_eq_true, Function.comp_apply]
      intro x hx y hy
      first
        | exact hflat x hx y hy
        | (simp only [List.all_eq_true]; exact hflat x hx y hy)
        | (intro k hk; exact hflat x hx y hy k hk)
    unfold blockNestedBit
    rw [hfl, hqpr]
    simp [htg0, BlockShape.k, hqpm]
  have hcF : CTBCodes mode ({ C with fe := q.env1, EH := EH5, envM := envM5, H := H6, St := s6.store } : Ctx) := by
    ctx_tr hc.ctb
  refine specR_callNC (C := C6) cbkR fCtb ctbParams
    [vv cbkO1, vv cbkOrr1, vv cbkOpp, vv cbkOn, vv cbkNtb, vv cbkOq, vv cbkNq, vv cbkLv, vv cbkOlw, vv cbkTy0, vv cbkOpp,
      vv cbkNpp, vv cbkPa, vv cbkNd, vv cbkNm1, vv cbkOs, vv cbkNsl, vv cbkOm1, vv cbkNct, vv cbkNi, vv cbkInd, vv cbkNpc,
      vv cbkNp1, vv cbkRs1, vv cbkTq, vv cbkOms, vv cbkNcl] (ctbBody C)
    ([cellA C o1, cellA C orr1, cellA C opp, cellA C on,
        BitVec.ofNat 64 q.tbl.length, cellA C ocq, BitVec.ofNat 64 m.ctors.length, Enc.idxW m.lvls, cellA C olp1,
        Enc.idxW ms0.cvT.type, cellA C opp, BitVec.ofNat 64 m.pfvs.length, cellA C od, BitVec.ofNat 64 m.ds.length,
        Enc.idxW ms0.cvT.name, cellA C os, BitVec.ofNat 64 q.rd.slots.length, cellA C om1, BitVec.ofNat 64 q.p.numCtors,
        BitVec.ofNat 64 m.nIdx, Enc.idxW m.ind, BitVec.ofNat 64 m.nPc] ++
        [BitVec.ofNat 64 q.p.nP, Enc.idxW q.p.resSort, cellA C oQ, cellA C oms, BitVec.ofNat 64 q.cls.length]) (by decide) rfl (by decide) hcF.self
    ⟨by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv, hpfv] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv, hnc_eq] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl,
      by simp +decide [sev, Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl, trivial⟩
    (PostCB C6 (consBlockCtors q.p.nP q.p.ctorGroups C6.fe))
    (fun fe₂ w s' C' => ∃ EH envM H, C' = ctxNew C6 fe₂ EH envM H ∧ C6.EH <+: EH ∧ C6.H <+: H ∧
      CtxOK (ctxNew C6 fe₂ EH envM H) ∧ TblGate fe₂ ∧ FlagsOK fe₂ ∧ LitsPinned fe₂ C6.pins ∧
      (∀ n, fe₂.find? n = (consBlockCtors q.p.nP q.p.ctorGroups C6.fe).find? n) ∧
      (∀ n, fe₂.findTable? n = (consBlockCtors q.p.nP q.p.ctorGroups C6.fe).findTable? n))
    (fun a w s' st ⟨EH, envM, H, h1, h2, h3, h4, h5⟩ => ⟨_, ⟨EH, envM, H, rfl, h1, h2, h3, h5⟩, h4⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ctbParams _ rfl hlk)
      (ctb_spec mode ra C6 hok6 hs hpl hcF (by obtain ⟨⟩ := hf; constructor <;> assumption) hg5 hF5 hL5
        (heqS C6 rfl hok6) q q.p rfl rfl ms0 hqpm block (by rw [hqp]; exact hsp) o1 (shapeRep_mono hp6' hsh1) hlp
        (by rw [hqpr]; simpa using hrlp) rc hqpr orr1 hrr1k (by omega) hrl kr hkr
        (fun j hj => hx6.lss.ls.ns _ _ (hkrs j hj)) l0
        (by show denoteL s6.store.ls q.p.resSort = _; rw [hqp]; exact denoteL_ext hl0 hx56)
        (by rw [hnc_eq]; omega) (by rw [hqp]; show p₀.nP < _; omega) opp hppb6 hpml on
        (pRep_mono hp6' (fun _ _ h => nfRep_mono hp6' h) htbl) htl hel m hcls hmm0 hmc' ocq hcrq (by rw [hmc']; omega)
        (by rw [hmc']; intro c hc'; have := hnf c hc'; omega) (fun c hc' => cvDen_ext (hcs c hc').1 hx6) hnd hcnew
        olp1 hlpb1 opp (by rw [hpfv]; exact hppb6) (by rw [hpfv]; omega) od hdb hdl os ⟨sps, hspl, hspb, hspr⟩ hsl hcb k0
        hsl0' om1 hM1 (by rw [hqp]; simp [BlockShape.k, hms]; omega) hni56 hnpc62 hni
        hrc0 hnest oms (tmBlk_mono hp6' htm) Q (by omega) oQ ⟨qps, hqQl, hqQb, hqQr⟩
        (fun t ht => (htab t ht).2.1)
        (fun t ht => by obtain ⟨-, -, b1, b2, b3, b4⟩ := htab t ht; exact ⟨by omega, b2, by omega, b4⟩) s6
        (fun s3 g0 cvRis s7 pre s1' s' cv hc3 hga hpb h => by
          rw [show C6.fe = q.env1 from rfl] at hga h
          exact hrun.crt env s1 p₀.members isRec s4 q s5 Q s6 s3 m g0 cvRis s7
            pre s1' s' cv hck0 henv0 hrel0 hx00 hpre hqrun' (by rw [hms]; exact hbrun) (by rw [hcls]; simp)
            (by rw [hqpr]; simp) hc3 hga hpb h)))
    (fun fe₂ w s7 C7 ⟨EH7, envM7, H7, eC, hpE7, hp7, hok7, hg7, hF7, hL7, hf7, ht7⟩ => ?_)
  subst eC
  have hp7' : H6 <+: H7 := hp7
  simp only [hrecs, blockRecs, recFire, BlockShape.k, hms, htg0, List.length_singleton, Nat.zero_lt_one, ↓reduceIte,
    pure_bind, IFEnv.pushDelta, IFEnv.pushAll]
  let CF7 : Ctx := { C with fe := fe₂, EH := EH7, envM := envM7, H := H7, St := s6.store }
  have hcR : RIACodes CF7 := ⟨by ctx_tr hc.rin, by ctx_tr hc.ria⟩
  have hcT : CF7.code.lookup fTw = some (twParams.map (fun p => (p, ShapeHOL.one)), twBody CF7, .one) := by
    ctx_tr hc.tw
  have hok7F : CtxOK CF7 := hok7
  have hqQF : PRep CF7 CF7.H oQ (fun H o t => TblVRep CF7 H o t) Q :=
    pRep_mono (hp7' : H6 <+: H7) (fun _ _ h => tblVRep_mono hp7' h) ⟨qps, hqQl, hqQb, hqQr⟩
  refine specR_mono (P := Inv CF7 s7 _ [] _) (R := PostBlk CF7)
    (ci_spec CF7 hok7F hcR hcT hc.cp hc.ms hc.mi hc.cfh.g hc.cfh.p hg7 hF7 hL7 [rc] or1
      (by rw [← hqpr]; exact ptrsRep_mono hp7' (fun _ _ h => recRep_mono hp7' h) hR1) (by simp)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; omega)
      (fun r hr => by simp only [List.mem_singleton] at hr; subst hr; exact cvDen_ext hrd hx6) Q (by omega) oQ hqQF
      (fun t ht => by obtain ⟨b0, -, b1, b2, b3, b4⟩ := htab t ht; exact ⟨b0, by omega, by omega, by omega, b3⟩)
      s7 _ _ (by decide) (by simp +decide [Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl)
      (by simp +decide [Env.get_cons, Env.get, Env.kill, cbkParams, ctxEnv] <;> rfl))
    (fun t ht => ht)
    (fun a w s' t ⟨EH, envM, tblM, H, h1, h2, h3, h4, h5⟩ =>
      ⟨EH, envM, tblM, H, hpE5.trans (hpE7.trans h1), hpC6.trans (hp7'.trans h2), h3, h4, h5⟩)

end

end ConPanqueque.T.Ind
