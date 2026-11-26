import ConPanqueque.T.Ind.ReplaceAppsGo

/-!
# The crests: `nestPhs`, `nestCanonCrest`, `nestCrest`

A stored constructor type instantiated at the canonical parameter variables, every whole member application
replaced by its hole; then (`nestCrest`) the key's parameters and holes put in — the `keyMap` replacement is the
`canon` one over `ds ++ holes`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

theorem nestKeyMap_eq (ds holes : List EIdx) (i : Nat) : nestKeyMap ds holes i = (ds ++ holes)[i]? := by
  unfold nestKeyMap
  by_cases h : i < ds.length
  · rw [if_pos h, List.getElem?_append_left h]
  · rw [if_neg h, List.getElem?_append_right (by omega)]

/-- The key map's replacement is the canonical one over the key's parameters and holes. -/
theorem rfv_keyMap (ds holes : List EIdx) : ∀ n memo h,
    replaceFVarsGo (.keyMap ds holes) memo n h = replaceFVarsGo (.canon (ds ++ holes)) memo n h := by
  intro n
  induction n with
  | zero => intro memo h; rw [replaceFVarsGo, replaceFVarsGo]
  | succ n ih =>
    intro memo h
    rw [replaceFVarsGo, replaceFVarsGo]
    simp only [ih, fvMapAt, nestKeyMap_eq]

theorem rf_keyMap (ds holes : List EIdx) (e : EIdx) :
    replaceFVars (.keyMap ds holes) e = targetCanonParams (ds ++ holes) e := by
  unfold targetCanonParams
  rw [replaceFVars, replaceFVars, rfv_keyMap]

/-! ## `replaceApps` at a fresh memo -/

def rptE := ofString "rpt_e"
def rptMs := ofString "rpt_ms"
def rptUs := ofString "rpt_us"
def rptB := ofString "rpt_b"
def rptN := ofString "rpt_n"
def rptQ := ofString "rpt_q"
def rptR := ofString "rpt_r"
def fRapTop := ofString "replaceApps"

def rptParams : List MlS := [rptE, rptMs, rptUs, rptB, rptN]
def rptLocals : List MlS := [rptQ, rptR]

def rptBody : ProgHOL 64 := prologue rptLocals
  (.seq (.call (some (some (.local, rptQ), none)) fRepApps
      [.const (BitVec.ofNat 64 coreWalkFuel), vv rptE, .const 0, vv rptMs, vv rptUs, vv rptB, vv rptN])
  (.seq (.assign .local rptR (.load .one (vv rptQ))) (.return (vv rptR))))

/-! ## `nestPhs`: the canonical parameter variables, appended one by one -/

def phsI := ofString "phs_i"
def phsN := ofString "phs_n"
def phsA := ofString "phs_a"
def phsZ := ofString "phs_z"
def phsS := ofString "phs_s"
def phsF := ofString "phs_f"
def phsA2 := ofString "phs_a2"
def phsR := ofString "phs_r"
def fPhs := ofString "nestPhs"

def phsParams : List MlS := [phsI, phsN, phsA]
def phsLocals : List MlS := [phsZ, phsS, phsF, phsA2, phsR]

def phsBody (C : Ctx) : ProgHOL 64 := prologue phsLocals
  (.ite (.cmp .equal (vv phsI) (vv phsN)) (.return (vv phsA))
  (.seq (.assign .local phsZ (.load .one (.const (ecell C (C.PO + pinCount + 1)))))
  (.seq (.call (some (some (.local, phsS), none)) fInternSort [vv phsZ])
  (.seq (.call (some (some (.local, phsF), none)) fInternFVar [vv phsS, vv phsI])
  (.seq (.call (some (some (.local, phsA2), none)) ExPre.fAppend [vv phsA, vv phsF])
  (.seq (.call (some (some (.local, phsR), none)) fPhs [.op .add [vv phsI, .const 1], vv phsN, vv phsA2])
    (.return (vv phsR))))))))

/-- One canonical parameter variable. -/
def phG : Nat → AM EIdx := fun i => do
  let z ← zeroLevel
  let s ← internSortE z
  internFVarE i s

theorem nestPhs_eq (n : Nat) : nestPhs n = (List.range' 0 (n - 0)).mapM phG >>= fun r => pure ([] ++ r) := by
  unfold nestPhs
  show (List.range n).mapM phG = _
  simp [List.range_eq_range']

/-! ## `nestCanonCrest` and `nestCrest` (a `none` hangs: the walk fails there) -/

def nccMs := ofString "ncc_ms"
def nccUs := ofString "ncc_us"
def nccN := ofString "ncc_n"
def nccT := ofString "ncc_t"
def nccA0 := ofString "ncc_a0"
def nccP := ofString "ncc_p"
def nccX := ofString "ncc_x"
def nccR := ofString "ncc_r"
def nccL := ofString "ncc_l"
def fNcc := ofString "nestCanonCrest"

def nccParams : List MlS := [nccMs, nccUs, nccN, nccT]
def nccLocals : List MlS := [nccA0, nccP, nccX, nccR, nccL]

def nccBody (C : Ctx) : ProgHOL 64 := prologue nccLocals
  (alloc1 C nccA0 (.const 0)
  (.seq (.call (some (some (.local, nccP), none)) fPhs [.const 0, vv nccN, vv nccA0])
  (.seq (.assign .local nccL (.load .one (vv nccP)))
  (.seq (.call (some (some (.local, nccX), none)) fInstPis [vv nccP, .const 0, vv nccL, vv nccT])
  (.seq (.call (some (some (.local, nccR), none)) fRapTop [vv nccX, vv nccMs, vv nccUs, .const 0, vv nccN])
    (.return (vv nccR)))))))

def ncrMs := ofString "ncr_ms"
def ncrUs := ofString "ncr_us"
def ncrN := ofString "ncr_n"
def ncrDH := ofString "ncr_dh"
def ncrT := ofString "ncr_t"
def ncrX := ofString "ncr_x"
def ncrR := ofString "ncr_r"
def fNcr := ofString "nestCrest"

def ncrParams : List MlS := [ncrMs, ncrUs, ncrN, ncrDH, ncrT]
def ncrLocals : List MlS := [ncrX, ncrR]

def ncrBody : ProgHOL 64 := prologue ncrLocals
  (.seq (.call (some (some (.local, ncrX), none)) fNcc [vv ncrMs, vv ncrUs, vv ncrN, vv ncrT])
  (.seq (.call (some (some (.local, ncrR), none)) fTcp [vv ncrX, vv ncrDH]) (.return (vv ncrR))))

structure CrestCodes (C : Ctx) : Prop where
  rap : RAPCodes C
  rt : C.code.lookup fRapTop = some (rptParams.map (fun p => (p, ShapeHOL.one)), rptBody, .one)
  srt : C.code.lookup fInternSort = some ([(lEu, .one)], sortBody, .one)
  fv : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one)
  app : C.code.lookup ExPre.fAppend = some (ExPre.appParams.map (fun p => (p, ShapeHOL.one)), ExPre.appBody C, .one)
  phs : C.code.lookup fPhs = some (phsParams.map (fun p => (p, ShapeHOL.one)), phsBody C, .one)
  ipw : C.code.lookup fInstPis = some (ipwParams.map (fun p => (p, ShapeHOL.one)), ipwBody, .one)
  i1 : C.code.lookup fInst1F = some ([(pFu, .one), (pH, .one), (pV, .one), (pD, .one)], fastBody C, .one)
  i1c : Codes C (ExI.body C)
  ncc : C.code.lookup fNcc = some (nccParams.map (fun p => (p, ShapeHOL.one)), nccBody C, .one)
  rfw : RFWCodes C
  tcp : C.code.lookup fTcp = some (tcpParams.map (fun p => (p, ShapeHOL.one)), tcpBody, .one)
  ncr : C.code.lookup fNcr = some (ncrParams.map (fun p => (p, ShapeHOL.one)), ncrBody, .one)

section
variable {σ : Type}

theorem rpt_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rptLocals → (ctxEnv C ++ rptParams.zip vals).get x = none :=
  Knot.params_none C rptLocals rptParams vals (by decide) (by decide)

theorem phs_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ phsLocals → (ctxEnv C ++ phsParams.zip vals).get x = none :=
  Knot.params_none C phsLocals phsParams vals (by decide) (by decide)

theorem ncc_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ nccLocals → (ctxEnv C ++ nccParams.zip vals).get x = none :=
  Knot.params_none C nccLocals nccParams vals (by decide) (by decide)

theorem ncr_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ncrLocals → (ctxEnv C ++ ncrParams.zip vals).get x = none :=
  Knot.params_none C ncrLocals ncrParams vals (by decide) (by decide)

/-- **`replaceApps`**. -/
theorem rpt_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CrestCodes C)
    (ms : List MemberShape) (om : Nat) (hml : ms.length < 2 ^ 59) (hM : PtrsRep C C.H om (MemberRep C C.H) ms)
    (us : LsIdx) (bb nn : Nat) (hbn : bb + nn < 2 ^ 62) (e : EIdx) (H : List (BitVec 64)) (hp : C.H <+: H) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (rptParams.zip [Enc.idxW e, cellA C om, Enc.idxW us, BitVec.ofNat 64 bb,
      BitVec.ofNat 64 nn])) rptBody s (replaceApps (ms.map (·.cvT.name)) us bb nn e) (PostK (ctxH C H)) := by
  refine specR_prologue (postK_locals _) (rpt_none _ _) ?_
  unfold replaceApps
  have hm0 : MemoRep C.HB H 0 ∅ := ⟨[], rfl, fun k => by simp⟩
  refine specR_callNIH (C := ctxH C H) rptQ fRepApps rapParams
    [.const (BitVec.ofNat 64 coreWalkFuel), vv rptE, .const 0, vv rptMs, vv rptUs, vv rptB, vv rptN] (rapBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e, 0, cellA C om, Enc.idxW us, BitVec.ofNat 64 bb, BitVec.ofNat 64 nn]
    (by decide) rfl (by decide) hc.rap.self
    ⟨rfl, (by simp +decide [sev, Env.get_cons, Env.get, rptParams, ctxEnv]), rfl, by simp +decide [sev, Env.get_cons, Env.get, rptParams, ctxEnv], (by simp +decide [sev, Env.get_cons, Env.get, rptParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, rptParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, rptParams, ctxEnv]), trivial⟩
    (PostRA (ctxH C H)) (fun r w _ H' => ∃ op mw', w = cellA C op ∧ H'[op]? = some (Enc.idxW r.1) ∧
      H'[op + 1]? = some mw' ∧ MemoRep C.HB H' mw' r.2)
    (fun r w s' st ⟨H', op, mw', hp', hw, h1, h2, h3, hsr⟩ => ⟨H', hp', ⟨op, mw', hw, h1, h2, by exact h3⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rapParams _ rfl hlk)
      (rap_spec ra C hok hc.rap ms om hml hM us bb nn hbn coreWalkFuel CV.coreWalkFuel_lt e ∅ 0 H s hp hm0))
    (fun r w s1 H1 hp1 ⟨op, mw', hw, h1, _, _⟩ => ?_)
  subst hw
  refine UD.specR_heapLoadI' (C := ctxH C H1) rptR (vv rptQ) op _ h1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  exact specR_returnI _ (Enc.idxW r.1) (by simp [sev, Env.get_cons])
    (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- **`nestPhs`** from `i` on, appended to `acc`. -/
theorem phs_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CrestCodes C) (n : Nat)
    (hn : n < 2 ^ 62) :
    ∀ f i (acc : List EIdx) (oa : Nat) (H : List (BitVec 64)) (s : AState), n - i = f → i ≤ n → C.H <+: H →
      BlkAt H oa (acc.map Enc.idxW) →
      SpecR (σ := σ) (Pre (ctxH C H) s (phsParams.zip [BitVec.ofNat 64 i, BitVec.ofNat 64 n, cellA C oa])) (phsBody C) s
        ((List.range' i (n - i)).mapM phG >>= fun r => pure (acc ++ r)) (PostA (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro i acc oa H s hf hi hp hb
    have hin : i = n := by omega
    subst hin
    refine specR_prologue (postA_locals _) (phs_none _ _) ?_
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get, phsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => ?_) (fun h => absurd h (by decide))
    simp only [Nat.sub_self, List.range'_zero, List.mapM_nil, pure_bind, List.append_nil]
    exact specR_returnI _ (cellA C oa) (by simp +decide [sev, Env.get, phsParams, ctxEnv])
      (fun t ht => ⟨H, oa, List.prefix_refl _, rfl, hb, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro i acc oa H s hf hi hp hb
    refine specR_prologue (postA_locals _) (phs_none _ _) ?_
    have hw : BitVec.ofNat 64 i ≠ BitVec.ofNat 64 n := by
      intro e; have := congrArg BitVec.toNat e; simp at this; omega
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, phsParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hw])
      (fun h => absurd rfl h) (fun _ => ?_)
    have hr : n - i = (n - (i + 1)) + 1 := by omega
    refine specR_congr (m' := (do let z ← zeroLevel; let s ← internSortE z; internFVarE i s) >>= fun x =>
      (List.range' (i + 1) (n - (i + 1))).mapM phG >>= fun r => pure ((acc ++ [x]) ++ r))
      (by rw [hr, List.range'_succ]; simp [List.mapM_cons, bind_assoc, phG]) ?_
    simp only [zeroLevel, bind_assoc]
    have hokH := ctxOK_H hok H
    refine specR_pinXI hokH pinZeroLevel 1 C.pins.zeroLevel _ (fun s hp => pinZeroLevel_run hokH hp)
      (pin_zeroLevel_cell hokH) phsZ (by decide) ?_
    refine ILP.callE_spec phsS fInternSort [lEu] [vv phsZ] sortBody [Enc.idxW C.pins.zeroLevel] (by decide) rfl
      (by decide) hc.srt ⟨by simp [sev, Env.get_cons]; rfl, trivial⟩
      (sort_body_spec ra (ctxH C H) hokH s C.pins.zeroLevel) (fun s0 s1 => ?_)
    refine ILP.specR_internFVarI ra hokH hc.fv phsF (vv phsS) (vv phsI) s0 i (by omega) (by decide)
      (by simp [sev, Env.get_cons]) (by simp +decide [sev, Env.get_cons, Env.get, phsParams, ctxEnv]) (fun x s2 => ?_)
    refine specR_appendI hok hc.app H phsA2 (vv phsA) (vv phsF) (acc.map Enc.idxW) (Enc.idxW x) oa hb (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, phsParams, ctxEnv]) (by simp [sev, Env.get_cons]) (fun H2 oa2 hp2 hb2 => ?_)
    refine specR_congr (m' := ((List.range' (i + 1) (n - (i + 1))).mapM phG >>= fun r => pure ((acc ++ [x]) ++ r)) >>=
      fun r => pure r) (by simp only [bind_pure]) ?_
    refine specR_callNIH (C := ctxH C H2) phsR fPhs phsParams [.op .add [vv phsI, .const 1], vv phsN, vv phsA2]
      (phsBody C) [BitVec.ofNat 64 (i + 1), BitVec.ofNat 64 n, cellA C oa2] (by decide) rfl (by decide) hc.phs
      ⟨by simp +decide [sev, Env.get_cons, Env.get, phsParams, ctxEnv]; exact e_succ i, (by simp +decide [sev, Env.get_cons, Env.get, phsParams, ctxEnv]),
        by simp [sev, Env.get_cons], trivial⟩
      (PostA (ctxH C H2)) (fun a w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (a.map Enc.idxW))
      (fun a w s' st ⟨H', o, hp', hw, hb', hsr⟩ => ⟨H', hp', ⟨o, hw, hb'⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu phsParams _ rfl hlk)
        (ih (i + 1) (acc ++ [x]) oa2 H2 s2 (by omega) (by omega) (hp.trans hp2) (by simpa using hb2)))
      (fun r w s3 H3 hp3 ⟨o3, hw3, hb3⟩ => ?_)
    subst hw3
    exact specR_returnI _ (cellA C o3) (by simp [sev, Env.get_cons])
      (fun t ht => ⟨H3, o3, hp2.trans hp3, rfl, hb3, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- Some handle (else Pancake hangs), the heap extended. -/
def PostSomeH (C : Ctx) (o : Option EIdx) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' t, C.H <+: H' ∧ o = some t ∧ w = Enc.idxW t ∧ SR (ctxH C H') s' st

theorem postSomeH_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostSomeH C a w s' st → PostSomeH C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', t, hp, h1, h2, hs⟩ => ⟨H', t, hp, h1, h2, sr_of_eq hs rfl rfl rfl rfl⟩

/-- **`nestCanonCrest`** (a type not binding the parameters hangs). -/
theorem ncc_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CrestCodes C)
    (ms : List MemberShape) (om : Nat) (hml : ms.length < 2 ^ 59) (hM : PtrsRep C C.H om (MemberRep C C.H) ms)
    (us : LsIdx) (n : Nat) (hn : n < 2 ^ 58) (cty : EIdx) (H : List (BitVec 64)) (hp : C.H <+: H) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (nccParams.zip [cellA C om, Enc.idxW us, BitVec.ofNat 64 n, Enc.idxW cty]))
      (nccBody C) s (nestCanonCrest (ms.map (·.cvT.name)) us n cty) (PostSomeH (ctxH C H)) := by
  refine specR_prologue (postSomeH_locals _) (ncc_none _ _) ?_
  rw [nestCanonCrest, nestPhs_eq]
  refine specR_alloc1I (ctxOK_H hok H) nccA0 (.const 0) 0 (by decide) (fun _ => rfl) (fun H0 ws hp0 hws => ?_)
  have g0 : ((H0 ++ ws).set H0.length 0)[H0.length]? = some 0 := by simp [List.getElem?_set, hws]
  have h0 : H0 <+: ((H0 ++ ws).set H0.length 0) := img1_prefix H0 ws 0 hws
  have hp0' : H <+: _ := (hp0 : H <+: H0).trans h0
  have hb0 : BlkAt ((H0 ++ ws).set H0.length 0) H0.length (([] : List EIdx).map Enc.idxW) :=
    ⟨by simpa using g0, fun i hi => by simp at hi⟩
  refine specR_callNIH (C := ctxH C _) nccP fPhs phsParams [.const 0, vv nccN, vv nccA0] (phsBody C)
    [BitVec.ofNat 64 0, BitVec.ofNat 64 n, cellA C H0.length] (by decide) rfl (by decide) hc.phs
    ⟨rfl, (by simp +decide [sev, Env.get_cons, Env.get, nccParams, ctxEnv]), by simp [sev, Env.get_cons]; rfl, trivial⟩
    (PostA (ctxH C _)) (fun a w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (a.map Enc.idxW))
    (fun a w s' st ⟨H', o, hp', hw, hb', hsr⟩ => ⟨H', hp', ⟨o, hw, hb'⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu phsParams _ rfl hlk)
      (phs_spec ra C hok hc n (by omega) _ 0 [] H0.length _ s rfl (by omega) (hp.trans hp0') hb0))
    (fun phs w s1 H1 hp1 ⟨o1, hw1, hb1⟩ => ?_)
  subst hw1
  have hp1' : H <+: H1 := hp0'.trans hp1
  refine UD.specR_heapLoadI' (C := ctxH C H1) nccL (vv nccP) o1 _ hb1.1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  rw [show instPisWith phs cty = instPisWith (phs.drop 0) cty by rw [List.drop_zero]]
  refine specR_callNIH (C := ctxH C H1) nccX fInstPis ipwParams [vv nccP, .const 0, vv nccL, vv nccT] ipwBody
    [cellA C o1, BitVec.ofNat 64 0, BitVec.ofNat 64 phs.length, Enc.idxW cty] (by decide) rfl (by decide) hc.ipw
    ⟨by simp +decide [sev, Env.get_cons], rfl, by simp [sev, Env.get_cons], (by simp +decide [sev, Env.get_cons, Env.get, nccParams, ctxEnv]), trivial⟩
    (PostSome (ctxH C H1)) (fun o w _ _ => ∃ t, o = some t ∧ w = Enc.idxW t)
    (fun o w s' st ⟨t, ho, hw, hsr⟩ => ⟨H1, List.prefix_refl _, ⟨t, ho, hw⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ipwParams _ rfl hlk)
      (ipw_spec ra C hok hc.ipw hc.i1 hc.i1c phs o1 H1 hb1 _ 0 s1 cty rfl (by omega)))
    (fun o w s2 H2 hp2 ⟨t, ho, hw⟩ => ?_)
  subst ho; subst hw
  have hp2' : H1 <+: H2 := hp2
  simp only
  refine specR_callNIH (C := ctxH C H2) nccR fRapTop rptParams [vv nccX, vv nccMs, vv nccUs, .const 0, vv nccN] rptBody
    [Enc.idxW t, cellA C om, Enc.idxW us, BitVec.ofNat 64 0, BitVec.ofNat 64 n] (by decide) rfl (by decide) hc.rt
    ⟨by simp [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, nccParams, ctxEnv], (by simp +decide [sev, Env.get_cons, Env.get, nccParams, ctxEnv]), rfl, (by simp +decide [sev, Env.get_cons, Env.get, nccParams, ctxEnv]), trivial⟩
    (PostK (ctxH C H2)) (fun r w _ _ => w = Enc.idxW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rptParams _ rfl hlk)
      (rpt_spec ra C hok hc ms om hml hM us 0 n (by omega) t H2 ((hp.trans hp1').trans hp2') s2))
    (fun r w s3 H3 hp3 hw => ?_)
  subst hw
  exact specR_returnI _ (Enc.idxW r) (by simp [sev, Env.get_cons])
    (fun tt ht => ⟨H3, r, (hp1'.trans hp2').trans hp3, rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- **`nestCrest`** at a key whose parameters and holes form one block (a `none` hangs). -/
theorem ncr_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : CrestCodes C)
    (ms : List MemberShape) (om : Nat) (hml : ms.length < 2 ^ 59) (hM : PtrsRep C C.H om (MemberRep C C.H) ms)
    (us : LsIdx) (ds holes : List EIdx) (hdl : ds.length < 2 ^ 58) (pdh : Nat) (cty : EIdx) (H : List (BitVec 64))
    (hp : C.H <+: H) (hdh : BlkAt H pdh ((ds ++ holes).map Enc.idxW)) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (ncrParams.zip [cellA C om, Enc.idxW us, BitVec.ofNat 64 ds.length, cellA C pdh,
      Enc.idxW cty])) ncrBody s (nestCrest (ms.map (·.cvT.name)) us ds holes cty) (PostSomeH (ctxH C H)) := by
  refine specR_prologue (postSomeH_locals _) (ncr_none _ _) ?_
  rw [nestCrest]
  refine specR_callNIH (C := ctxH C H) ncrX fNcc nccParams [vv ncrMs, vv ncrUs, vv ncrN, vv ncrT] (nccBody C)
    [cellA C om, Enc.idxW us, BitVec.ofNat 64 ds.length, Enc.idxW cty] (by decide) rfl (by decide) hc.ncc
    ⟨by simp +decide [sev, Env.get_cons, Env.get, ncrParams, ctxEnv], (by simp +decide [sev, Env.get_cons, Env.get, ncrParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, ncrParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, ncrParams, ctxEnv]), trivial⟩
    (PostSomeH (ctxH C H)) (fun o w _ _ => ∃ t, o = some t ∧ w = Enc.idxW t)
    (fun o w s' st ⟨H', t, hp', ho, hw, hsr⟩ => ⟨H', hp', ⟨t, ho, hw⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu nccParams _ rfl hlk)
      (ncc_spec ra C hok hc ms om hml hM us ds.length hdl cty H hp s))
    (fun o w s1 H1 hp1 ⟨c, ho, hw⟩ => ?_)
  subst ho; subst hw
  have hp1' : H <+: H1 := hp1
  simp only
  rw [rf_keyMap]
  refine specR_callNIH (C := ctxH C H1) ncrR fTcp tcpParams [vv ncrX, vv ncrDH] tcpBody [Enc.idxW c, cellA C pdh]
    (by decide) rfl (by decide) hc.tcp ⟨by simp [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, ncrParams, ctxEnv], trivial⟩
    (PostK (ctxH C H1)) (fun r w _ _ => w = Enc.idxW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu tcpParams _ rfl hlk)
      (tcp_spec ra C hok hc.rfw hc.tcp (ds ++ holes) pdh H1 (hp.trans hp1') (blkAt_mono hdh hp1') s1 c))
    (fun r w s2 H2 hp2 hw => ?_)
  subst hw
  exact specR_returnI _ (Enc.idxW r) (by simp [sev, Env.get_cons])
    (fun tt ht => ⟨H2, r, hp1'.trans hp2, rfl, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
