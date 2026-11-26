import ConPanqueque.T.Ind.TblWrite
import ConPanqueque.T.Ind.EnvRules
import ConPanqueque.T.Decl.IdxInsPlain

/-!
# A member's recursor installed (`blockRecs` + `pushAll`, plain firing)

`rinBody`: the recursor's name still absent (else a hang), its record written with its rules firing `.plain`,
its name inserted, the literal flags read.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def rinR := ofString "rin_r"
def rinC := ofString "rin_c"
def rinN := ofString "rin_n"
def rinY := ofString "rin_y"
def rinF := ofString "rin_f"
def rinX := ofString "rin_x"
def rinRi := ofString "rin_ri"
def rinFl := ofString "rin_fl"
def fRin := ofString "installRec"

def rinParams : List MlS := [rinR]
def rinLocals : List MlS := [rinC, rinN, rinY, rinF, rinX, rinRi, rinFl]

def rinBody (C : Ctx) : ProgHOL 64 := prologue rinLocals
  (.seq (.assign .local rinC (.load .one (vv rinR)))
  (.seq (.assign .local rinN (.load .one (vv rinC)))
  (envFindP C rinY (vv rinN)
  (.ite (.cmp .notEqual (vv rinY) (.const 0)) hang
  (alloc1 C rinF (.const 0)
  (.seq (.call (some (some (.local, rinX), none)) fRecRec [vv rinR, vv rinF])
  (idxInsP C (vv rinN) (vv rinX) rinRi
  (.seq (.call (some (some (.local, rinFl), none)) fFlags [])
    (.return (.const 0))))))))))

structure RINCodes (C : Ctx) : Prop where
  csc : CSCCodes C
  fw : C.code.lookup fFireEnv = some (fwParams.map (fun p => (p, ShapeHOL.one)), fwBody C, .one)
  rw : C.code.lookup fRuleFill = some (rwParams.map (fun p => (p, ShapeHOL.one)), rwBody C, .one)
  rq : C.code.lookup fRecRec = some (rqParams.map (fun p => (p, ShapeHOL.one)), rqBody C, .one)
  self : C.code.lookup fRin = some (rinParams.map (fun p => (p, ShapeHOL.one)), rinBody C, .one)

section
variable {σ : Type}

theorem rin_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rinLocals → (ctxEnv C ++ rinParams.zip vals).get x = none :=
  Knot.params_none C rinLocals rinParams vals (by decide) (by decide)

/-- The recursor `blockRecs` records, its rules firing plainly. -/
def plainRec (rc : RecShape) : IConstantInfo :=
  .recInfo rc.cvR rc.mI rc.rP rc.isK (rc.rules.map ({ · with fire := .plain }))

set_option maxHeartbeats 64000000 in
/-- **A member's recursor installed**, its rules firing plainly. -/
theorem rin_spec (C : Ctx) (hok : CtxOK C) (hc : RINCodes C) (hg : TblGate C.fe) (hF : FlagsOK C.fe)
    (hL : LitsPinned C.fe C.pins) (rc : RecShape) (orc : Nat) (hrr : RecRep C C.H orc rc)
    (hlps : rc.cvR.levelParams.length < 2 ^ 60) (hden : CVDen rc.cvR C.St) (s : AState) :
    SpecR (σ := σ) (Pre C s (rinParams.zip [cellA C orc])) (rinBody C) s (pure (C.fe.push (plainRec rc)))
      (PostEnv C) := by
  refine specR_prologue (postEnv_locals C) (rin_none C _) ?_
  have hrr0 := hrr
  obtain ⟨⟨oc, hoc, hcv⟩, -, -, -, -, -⟩ := hrr0
  refine UD.specR_heapLoadI' (C := C) rinC _ orc _ hoc (by decide) (by simp +decide [sev, Env.get, rinParams, ctxEnv]) ?_
  refine UD.specR_heapLoadI' (C := C) rinN (vv rinC) oc _ hcv.1 (by decide) (by simp [sev, Env.get_cons]) ?_
  refine specR_envFindI hok hc.csc.k.g hc.csc.k.p rinY (vv rinN) rc.cvR.name (by decide) (by simp +decide [sev, Env.get_cons])
    (by simp +decide [Env.get_cons, Env.get, rinParams, ctxEnv]) ?_
  have hrel := find_rel hok rc.cvR.name
  revert hrel
  rcases hfn : C.fe.find? rc.cvR.name with _ | ci0
  swap
  · intro ⟨o', hm, hci⟩
    rw [hm]
    refine specR_atEntry fun t ht => ?_
    have hoE : o' < C.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht.sr.env.1.len
    exact specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok hoE)
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  intro hrel
  simp only at hrel
  rw [hrel]
  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_alloc1I hok rinF (.const 0) 0 (by decide) (fun _ => rfl) (fun H1 ws1 hp1 hws1 => ?_)
  have hg1 : ((H1 ++ ws1).set H1.length (0 : BitVec 64))[H1.length]? = some 0 := List.getElem?_set_self (by simp [hws1])
  have hp1' : C.H <+: (H1 ++ ws1).set H1.length (0 : BitVec 64) :=
    (hp1 : C.H <+: H1).trans (prefix_set (List.prefix_append _ _) (Nat.le_refl _) _)
  set H1' := (H1 ++ ws1).set H1.length (0 : BitVec 64) with hH1'
  have hok1 := ctxOK_H hok H1'
  set ci : IConstantInfo := plainRec rc with hci
  refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => _) (by rw [pure_bind]) ?_
  refine specR_callNC (C := ctxH C H1') (D := ctxLocals ++ rinLocals) rinX fRecRec rqParams [vv rinR, vv rinF] (rqBody C)
    [cellA C orc, cellA C H1.length] (by decide) rfl (by decide) hc.rq
    ⟨by simp +decide [sev, Env.get_cons, Env.get, rinParams, ctxEnv], by simp +decide [sev, Env.get_cons], trivial⟩
    (PostRQ (ctxH C H1') ci s)
    (fun _ w s' C' => s' = s ∧ ∃ H' EH o, C' = ctxE (ctxH C H') EH ∧ H1' <+: H' ∧ C.EH <+: EH ∧ w = ecell C o ∧
      CIE C.EB EH o ci)
    (fun _ w s' st ⟨hs', H', EH, o, hpH, hpE, _, hw, hcie, hsr⟩ => by subst hs'; exact ⟨_, ⟨rfl, H', EH, o, rfl, hpH, hpE, hw, hcie⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rqParams _ rfl hlk)
      (rq_spec (ctxH C H1') hok1 (by ctx_tr hc.csc.cp) (by ctx_tr hc.fw) (by ctx_tr hc.rw) (by ctx_tr hc.csc.cw) rc orc
        (recRep_mono hp1' hrr) hlps .plain H1.length (show H1'[H1.length]? = some 0 from hg1) s))
    (fun _ w s3 C3 ⟨hs3, H2, EH2, ox, eC, hpH2, hpE2, hw, hcie⟩ => ?_)
  subst eC hw s3
  have hpC2 : C.H <+: H2 := hp1'.trans hpH2
  have hok2 := ctxOK_H hok H2
  refine specR_atEntry fun t5 ht5 => ?_
  have hd5 : CVDen rc.cvR s.store := cvDen_ext hden ht5.sr.floor
  have hdn : NewDen ci s.store := by
    refine ⟨hd5.1, hd5.2.1, hd5.2.2, fun _ _ _ h => (by simp [hci, plainRec] at h), fun _ _ h => (by simp [hci, plainRec] at h)⟩
  have hnew : (ctxH C H2).fe.find? ci.name = none := hfn
  refine specR_idxInsIP (C := ctxH C H2) hok2 hc.csc.k.s hc.csc.k.i hg ci hnew
    (fun _ _ _ _ _ h rl hrl => by
      simp only [hci, plainRec, IConstantInfo.recInfo.injEq] at h
      obtain ⟨-, -, -, -, rfl⟩ := h
      obtain ⟨r0, -, rfl⟩ := List.mem_map.mp hrl; rfl)
    EH2 ox hpE2 hdn (vv rinN) (vv rinX) rinRi (by decide)
    (by simp +decide [sev, Env.get_cons]; rfl) (by simp +decide [sev, Env.get_cons]; rfl)
    (by simp +decide [Env.get_cons, Env.get, rinParams, ctxEnv]; rfl) (fun wr2 => ?_)
  have hokI := ctxOK_ins hok2 hpE2 hcie (pushOld_find C.fe ci) (pushOld_findTable hg ci hnew)
  have hfP : ∀ n, (C.fe.push ci).find? n = (ctxIns (ctxH C H2) ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit)
      EH2 (C.envM.insert ci.name (ecell C ox))).fe.find? n := fun n => (IFEnv.setFlags_find? _ _ _ n).symm
  have htP : ∀ n, (C.fe.push ci).findTable? n = (ctxIns (ctxH C H2) ((C.fe.push ci).setFlags C.fe.natLit
      C.fe.strLit) EH2 (C.envM.insert ci.name (ecell C ox))).fe.findTable? n := fun n => by
    show _ = ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit).findTable? n
    unfold IFEnv.findTable?; rw [IFEnv.setFlags_find?, IFEnv.setFlags_rawTable?]
  obtain ⟨hfn', hfs'⟩ := push_flags_found (C := ctxH C H2) hF hL ci ox EH2
  refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => _) (by rw [pure_bind]) ?_
  refine specR_callNC (C := ctxIns (ctxH C H2) ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit) EH2
      (C.envM.insert ci.name (ecell C ox))) (D := ctxLocals ++ rinLocals) rinFl fFlags [] [] Decl.flBody []
    (by decide) rfl (by decide) hc.csc.flags trivial
    (fun a w s' st => PostFl (ctxIns (ctxH C H2) ((C.fe.push ci).setFlags C.fe.natLit C.fe.strLit) EH2
      (C.envM.insert ci.name (ecell C ox))) (C.fe.push ci) a w s' st ∧ s' = s)
    (fun _ w s' C' => s' = s ∧ ∃ H6, C' = ctxFe (ctxH (ctxIns (ctxH C H2) ((C.fe.push ci).setFlags C.fe.natLit
      C.fe.strLit) EH2 (C.envM.insert ci.name (ecell C ox))) H6) (C.fe.push ci) ∧ H2 <+: H6)
    (fun a w s' st ⟨⟨H6, hp6, hsr⟩, hs'⟩ => ⟨_, ⟨hs', H6, rfl, hp6⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [] _ rfl hlk)
      (specR_pureState (fl_spec _ hokI (by ctx_tr hc.csc.natF) (by ctx_tr hc.csc.strF) (by ctx_tr hc.csc.k.g)
        (by ctx_tr hc.csc.k.p) s hfP htP hfn' hfs')))
    (fun _ w s5 C5 ⟨hs5, H6, eC, hp6⟩ => ?_)
  subst eC s5
  have hokF := ctxOK_fe (ctxOK_H hokI H6) (fe := C.fe.push ci) (fun n => hfP n) (fun n => htP n)
  exact specR_returnI _ 0 rfl (fun t ht => ⟨EH2, C.envM.insert ci.name (ecell C ox), H6, hpE2, hpC2.trans hp6, hokF,
    sr_of_eq ht.sr rfl rfl rfl rfl, hg.push ci, hF.push ci, by unfold LitsPinned; rw [IFEnv.push_base]; exact hL⟩)

end

end ConPanqueque.T.Ind
