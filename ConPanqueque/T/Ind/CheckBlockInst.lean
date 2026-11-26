import ConPanqueque.T.Ind.TblWrite
import ConPanqueque.T.Ind.RecInstall
import ConPanqueque.T.Ind.BlockTables
import ConPanqueque.T.Ind.CtorsFresh

/-!
# `checkBlock`'s install: the recursor, then the table (if any)

`cbkInst`: the recursor installed (its rules fire `.plain`); with one table, its structure looked up (absent hangs)
and the table installed.  Stated over a plain context `K`, so no nested context is unfolded.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def ciX := ofString "cbk_x"
def ciOrr1 := ofString "cbk_orr1"
def ciNqq := ofString "cbk_nqq"
def ciTq := ofString "cbk_tq"
def ciT := ofString "cbk_t"
def ciTn := ofString "cbk_tn"
def ciY := ofString "cbk_y"

/-- The install: the recursor, then the table (if any). -/
def cbkInst (C : Ctx) : ProgHOL 64 :=
  .seq (.call (some (some (.local, ciX), none)) fRin [vv ciOrr1])
  (.ite (.cmp .equal (vv ciNqq) (.const 0)) (.return (.const 0))
    (.seq (.assign .local ciT (.load .one (.op .add [vv ciTq, .const 8])))
    (.seq (.assign .local ciTn (.load .one (vv ciT)))
    (envFindP C ciY (vv ciTn)
    (.ite (.cmp .equal (vv ciY) (.const 0)) hang
    (.seq (.call (some (some (.local, ciX), none)) fTw [vv ciT]) (.return (.const 0))))))))

/-- The context with an environment, its heap, constant table, table memo and value heap replaced. -/
def ctxNT (C : Ctx) (fe : IFEnv) (EH : List (BitVec 64)) (envM tblM : Std.HashMap NIdx (BitVec 64))
    (H : List (BitVec 64)) : Ctx := { C with fe := fe, EH := EH, envM := envM, tblM := tblM, H := H }

theorem tblGate_pushTable {fe : IFEnv} (h : TblGate fe) (t : IProjTable) (hs : (fe.find? t.structName).isSome = true) :
    TblGate (fe.pushTable t) := by
  intro n t' ht
  rw [find?_pushTable]
  rw [rawTable?_pushTable] at ht
  by_cases e : (t.structName == n) = true
  · have : t.structName = n := by simpa using e
    rw [← this]; exact hs
  · simp only [e, Bool.false_eq_true, ↓reduceIte] at ht; exact h n t' ht

section
variable {σ : Type}

/-- After the block: its install's context. -/
def PostBlk (C : Ctx) (fe : IFEnv) (_ : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ EH envM tblM H, C.EH <+: EH ∧ C.H <+: H ∧ CtxOK (ctxNT C fe EH envM tblM H) ∧ SR (ctxNT C fe EH envM tblM H) s' st ∧
    TblGate fe ∧ FlagsOK fe ∧ LitsPinned fe C.pins

theorem postBlk_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostBlk C a w s' st → PostBlk C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨EH, envM, tblM, H, h1, h2, h3, h4, h5⟩ =>
    ⟨EH, envM, tblM, H, h1, h2, h3, sr_of_eq h4 rfl rfl rfl rfl, h5⟩

theorem postBlk_lower {C : Ctx} {St : EStore} (hx : Ext C.St St) :
    ∀ a w s' (st : PState σ), PostBlk (ctxSt C St) a w s' st → PostBlk C a w s' st :=
  fun _ _ _ _ ⟨EH, envM, tblM, H, h1, h2, h3, h4, h5⟩ =>
    ⟨EH, envM, tblM, H, h1, h2, ctxOK_unSt h3, sr_lower (C := ctxNT C _ EH envM tblM H) h4 hx, h5⟩

set_option maxHeartbeats 8000000 in
/-- **The block's install** at a plain context. -/
theorem ci_spec (K : Ctx) (hok : CtxOK K) (hcR : RINCodes K)
    (hcT : K.code.lookup fTw = some (twParams.map (fun p => (p, ShapeHOL.one)), twBody K, .one))
    (hcp : K.code.lookup fCpy = some (Decl.cpParams.map (fun p => (p, ShapeHOL.one)), cpyBody, .one))
    (hcS : K.code.lookup fMemoSet = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoSetBody, .one))
    (hcI : K.code.lookup fMemoIns = some ([(pG, .one), (pLen, .one), (pVal, .one)], memoInsBody, .one))
    (hcG : K.code.lookup fMemoGet = some ([(pG, .one), (pLen, .one)], memoGetBody, .one))
    (hcP : K.code.lookup fMemoProbe = some ([(pG, .one), (pLen, .one)], memoProbeBody, .one))
    (hg : TblGate K.fe) (hF : FlagsOK K.fe) (hL : LitsPinned K.fe K.pins)
    (rc : RecShape) (orr : Nat) (hrr : RecRep K K.H orr rc) (hlps : rc.cvR.levelParams.length < 2 ^ 60)
    (hden : CVDen rc.cvR K.St) (Q : List IProjTable) (hQ : Q.length ≤ 1) (oQ : Nat)
    (hqQ : PRep K K.H oQ (fun H o t => TblVRep K H o t) Q)
    (htab : ∀ t ∈ Q, NewTblDen t K.St ∧ t.levelParams.length < 2 ^ 60 ∧ t.bodies.size < 2 ^ 60 ∧
      t.numParams < 2 ^ 63 ∧ t.numFields < 2 ^ 63)
    (s : AState) (Γ : Env) (D : List MlS) (hD : ciX ∈ D ∧ ciT ∈ D ∧ ciTn ∈ D ∧ ciY ∈ D)
    (hor : Γ.get ciOrr1 = some (cellA K orr)) (htq : Γ.get ciTq = some (cellA K oQ))
    (hnq : Γ.get ciNqq = some (BitVec.ofNat 64 Q.length)) (hkb : Γ.get lKb = some K.KB) :
    SpecR (σ := σ) (Inv K s Γ [] D) (cbkInst K) s (pure (IFEnv.pushTables Q (K.fe.push (plainRec rc)))) (PostBlk K) := by
  obtain ⟨hdX, hdT, hdTn, hdY⟩ := hD
  unfold cbkInst
  refine specR_congr (m' := (pure (K.fe.push (plainRec rc)) : AM IFEnv) >>= fun fe' => pure (IFEnv.pushTables Q fe'))
    (by rw [pure_bind]) ?_
  refine specR_callNC (C := K) ciX fRin rinParams [vv ciOrr1] (rinBody K) [cellA K orr]
    (by decide) rfl hdX hcR.self ⟨by simp [sev, hor], trivial⟩
    (fun a w s' st => (pure (K.fe.push (plainRec rc)) : AM IFEnv) s = .ok (a, s') ∧ PostEnv K a w s' st)
    (fun r w s' C' => r = K.fe.push (plainRec rc) ∧ s' = s ∧ ∃ EH envM H, C' = ctxNew K r EH envM H ∧
      K.EH <+: EH ∧ K.H <+: H ∧ CtxOK (ctxNew K r EH envM H) ∧ TblGate r ∧ FlagsOK r ∧ LitsPinned r K.pins)
    (fun a w s' st ⟨hrun, EH, envM, H, h1, h2, h3, h4, h5, h6, h7⟩ => by
      obtain ⟨e1, e2⟩ := AM.pure_ok hrun
      exact ⟨_, ⟨e1, e2, EH, envM, H, rfl, h1, h2, h3, h5, h6, h7⟩, h4⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu rinParams _ rfl hlk)
      (rin_spec K hok hcR hg hF hL rc orr hrr hlps hden s)))
    (fun fe' w s8 C8 ⟨efe, es8, EH8, envM8, H8, eC, hpE8, hp8, hok8, hg8, hF8, hL8⟩ => ?_)
  subst eC efe
  subst s8
  have hp8' : K.H <+: H8 := hp8
  rcases hQs : Q with _ | ⟨t, _ | ⟨t', Q'⟩⟩
  · subst hQs
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hnq, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [IFEnv.pushTables]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨EH8, envM8, K.tblM, H8, hpE8, hp8', hok8, sr_of_eq ht.sr rfl rfl rfl rfl,
      hg8, hF8, hL8⟩)
  swap
  · subst hQs; simp at hQ
  subst hQs
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hnq, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
    (fun h => absurd rfl h) (fun _ => ?_)
  simp only [IFEnv.pushTables]
  set C8 := ctxNew K (K.fe.push (plainRec rc)) EH8 envM8 H8 with hC8
  obtain ⟨qps, hqQl, hqQb, hqQr⟩ := hqQ
  have hq0 := hqQb.2 0 (by simp [hqQl])
  simp only [List.getElem_map] at hq0
  refine UD.specR_heapLoadI' (C := C8) ciT _ (oQ + 1 + 0) _ (ConPanqueque.T.Decl.get_prefix hq0 hp8') hdT
    (by simp +decide [sev, Env.get_cons, htq]; exact cellA_add8 K oQ) ?_
  have htv : TblVRep K H8 (qps[0]'(by simp [hqQl])) t :=
    tblVRep_mono hp8' (by simpa using hqQr 0 (by simp) (by simp [hqQl]))
  refine UD.specR_heapLoadI' (C := C8) ciTn (vv ciT) _ _ htv.1 hdTn (by simp [sev, Env.get_cons] <;> rfl) ?_
  refine specR_envFindI hok8 hcG hcP ciY (vv ciTn) t.structName hdY
    (by simp +decide [sev, Env.get_cons]) (by simp +decide [Env.get_cons, hkb] <;> rfl) ?_
  have hrel := find_rel hok8 t.structName
  revert hrel
  rcases hfn : C8.fe.find? t.structName with _ | ci0
  · intro hrel
    simp only at hrel
    rw [hrel]
    exact specR_ifI _ 1 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  intro ⟨o', hm, hci⟩
  rw [hm]
  refine specR_atEntry fun t8 ht8 => ?_
  have hoE : o' < C8.EN := Nat.lt_of_lt_of_le (cie_lt hci) ht8.sr.env.1.len
  refine specR_ifI _ 0 (by simp [sev, optWG, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact ecell_succ_ne hok8 hoE)
    (fun h => absurd rfl h) (fun _ => ?_)
  have hs : (C8.fe.find? t.structName).isSome = true := by rw [hfn]; rfl
  obtain ⟨hnew, b1, b2, b3, b4⟩ := htab t (by simp)
  refine specR_congr (m' := (pure () : AM Unit) >>= fun _ => pure ((K.fe.push (plainRec rc)).pushTable t))
    (by rw [pure_bind]) ?_
  refine specR_callNC (C := C8) ciX fTw twParams [vv ciT] (twBody K) [cellA K (qps[0]'(by simp [hqQl]))]
    (by decide) rfl hdX hcT ⟨by simp +decide [sev, Env.get_cons] <;> rfl, trivial⟩
    (PostTW C8 t s)
    (fun _ w s' C' => s' = s ∧ ∃ EH tblM, C' = ctxTb C8 (C8.fe.pushTable t) EH tblM ∧ C8.EH <+: EH ∧
      CtxOK (ctxTb C8 (C8.fe.pushTable t) EH tblM))
    (fun a w s' st ⟨hs', EH, tblM, h1, h2, h3⟩ => ⟨_, ⟨hs', EH, tblM, rfl, h1, h2⟩, h3⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu twParams _ rfl hlk)
      (tw_spec C8 hok8 hcp hcS hcI t _ htv hs hnew b1 b2 b3 b4 s))
    (fun _ w s9 C9 ⟨es9, EH9, tblM9, eC, hpE9, hok9⟩ => ?_)
  subst eC es9
  exact specR_returnI _ 0 rfl (fun t' ht => ⟨EH9, envM8, tblM9, H8, hpE8.trans hpE9, hp8', hok9,
    sr_of_eq ht.sr rfl rfl rfl rfl, tblGate_pushTable hg8 t hs,
    FlagsOK.of_same hF8 rfl (fun n => find?_pushTable _ t n) rfl rfl, by unfold LitsPinned; exact hL8⟩)

end

end ConPanqueque.T.Ind
