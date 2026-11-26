import ConPanqueque.T.Ind.RFHole

/-!
# `nestCtorNf` at the root frame: a constructor's record, its parameters and walked telescope read back
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def rxE := ofString "rx_e"
def rxMs := ofString "rx_ms"
def rxNP := ofString "rx_np"
def rxUs := ofString "rx_us"
def rxP := ofString "rx_p"
def rxQ := ofString "rx_q"
def rxR := ofString "rx_r"
def fRhiTop := ofString "replaceFVarsHole"

def rxParams : List MlS := [rxE, rxMs, rxNP, rxUs, rxP]
def rxLocals : List MlS := [rxQ, rxR]

def rxBody : ProgHOL 64 := prologue rxLocals
  (.seq (.call (some (some (.local, rxQ), none)) fRhi
      [.const (BitVec.ofNat 64 coreWalkFuel), vv rxE, .const 0, vv rxMs, vv rxNP, vv rxUs, vv rxP])
  (.seq (.assign .local rxR (.load .one (vv rxQ))) (.return (vv rxR))))

def rhmA := ofString "rhm_a"
def rhmJ := ofString "rhm_j"
def rhmAcc := ofString "rhm_acc"
def rhmMs := ofString "rhm_ms"
def rhmNP := ofString "rhm_np"
def rhmUs := ofString "rhm_us"
def rhmP := ofString "rhm_p"
def rhmL := ofString "rhm_l"
def rhmX := ofString "rhm_x"
def rhmY := ofString "rhm_y"
def rhmAcc2 := ofString "rhm_acc2"
def rhmR := ofString "rhm_r"
def fRhiMap := ofString "replaceFVarsHoleMap"

def rhmParams : List MlS := [rhmA, rhmJ, rhmAcc, rhmMs, rhmNP, rhmUs, rhmP]
def rhmLocals : List MlS := [rhmL, rhmX, rhmY, rhmAcc2, rhmR]

def rhmBody : ProgHOL 64 := prologue rhmLocals
  (.seq (.assign .local rhmL (.load .one (vv rhmA)))
  (.ite (.cmp .lower (vv rhmJ) (vv rhmL))
    (.seq (.assign .local rhmX (.load .one (.op .add [.op .add [vv rhmA, .const 8], .shift .lsl (vv rhmJ) (.const 3)])))
    (.seq (.call (some (some (.local, rhmY), none)) fRhiTop [vv rhmX, vv rhmMs, vv rhmNP, vv rhmUs, vv rhmP])
    (.seq (.call (some (some (.local, rhmAcc2), none)) ExPre.fAppend [vv rhmAcc, vv rhmY])
    (.seq (.call (some (some (.local, rhmR), none)) fRhiMap
        [vv rhmA, .op .add [vv rhmJ, .const 1], vv rhmAcc2, vv rhmMs, vv rhmNP, vv rhmUs, vv rhmP])
      (.return (vv rhmR))))))
    (.return (vv rhmAcc))))

def nnfNm := ofString "nnf_nm"
def nnfUs := ofString "nnf_us"
def nnfDs := ofString "nnf_ds"
def nnfCl := ofString "nnf_cl"
def nnfMs := ofString "nnf_ms"
def nnfNP := ofString "nnf_np"
def nnfP := ofString "nnf_p"
def nnfA0 := ofString "nnf_a0"
def nnfD2 := ofString "nnf_d2"
def nnfT := ofString "nnf_t"
def nnfR := ofString "nnf_r"
def fNnf := ofString "nestCtorNf"

def nnfParams : List MlS := [nnfNm, nnfUs, nnfDs, nnfCl, nnfMs, nnfNP, nnfP]
def nnfLocals : List MlS := [nnfA0, nnfD2, nnfT, nnfR]

def nnfBody (C : Ctx) : ProgHOL 64 := prologue nnfLocals
  (alloc1 C nnfA0 (.const 0)
  (.seq (.call (some (some (.local, nnfD2), none)) fRhiMap
      [vv nnfDs, .const 0, vv nnfA0, vv nnfMs, vv nnfNP, vv nnfUs, vv nnfP])
  (.seq (.call (some (some (.local, nnfT), none)) fRhiTop [vv nnfCl, vv nnfMs, vv nnfNP, vv nnfUs, vv nnfP])
    (alloc4 C nnfR (vv nnfNm) (vv nnfUs) (vv nnfD2) (vv nnfT) (.return (vv nnfR))))))

structure NNFCodes (C : Ctx) : Prop where
  rhi : RHICodes C
  rx : C.code.lookup fRhiTop = some (rxParams.map (fun p => (p, ShapeHOL.one)), rxBody, .one)
  app : C.code.lookup ExPre.fAppend = some (ExPre.appParams.map (fun p => (p, ShapeHOL.one)), ExPre.appBody C, .one)
  rm : C.code.lookup fRhiMap = some (rhmParams.map (fun p => (p, ShapeHOL.one)), rhmBody, .one)
  self : C.code.lookup fNnf = some (nnfParams.map (fun p => (p, ShapeHOL.one)), nnfBody C, .one)

/-- A constructor record at `o`: `[ctor, lvls, ds block, ty]`. -/
def NfRep (C : Ctx) (H : List (BitVec 64)) (o : Nat) (nf : NestCtorNf) : Prop :=
  H[o]? = some (Enc.idxW nf.ctor) ∧ H[o + 1]? = some (Enc.idxW nf.lvls) ∧
    (∃ od, H[o + 2]? = some (cellA C od) ∧ BlkAt H od (nf.ds.map Enc.idxW)) ∧ H[o + 3]? = some (Enc.idxW nf.ty)

theorem nfRep_mono {C : Ctx} {H H' : List (BitVec 64)} (hp : H <+: H') {o : Nat} {nf : NestCtorNf}
    (h : NfRep C H o nf) : NfRep C H' o nf :=
  let ⟨h1, h2, ⟨od, h3, h4⟩, h5⟩ := h
  ⟨get_prefix h1 hp, get_prefix h2 hp, ⟨od, get_prefix h3 hp, blkAt_mono h4 hp⟩, get_prefix h5 hp⟩

section
variable {σ : Type}

theorem rx_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rxLocals → (ctxEnv C ++ rxParams.zip vals).get x = none :=
  Knot.params_none C rxLocals rxParams vals (by decide) (by decide)

theorem rhm_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ rhmLocals → (ctxEnv C ++ rhmParams.zip vals).get x = none :=
  Knot.params_none C rhmLocals rhmParams vals (by decide) (by decide)

theorem nnf_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ nnfLocals → (ctxEnv C ++ nnfParams.zip vals).get x = none :=
  Knot.params_none C nnfLocals nnfParams vals (by decide) (by decide)

/-- **`replaceFVars` at the root frame's hole image**. -/
theorem rx_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : NNFCodes C)
    (ctx : NestCtx) (ms : List MemberShape) (om nP pp : Nat) (hml : ms.length < 2 ^ 59)
    (hM : PtrsRep C C.H om (MemberRep C C.H) ms) (hN : ctx.names = ms.map (·.cvT.name)) (hP : ctx.nP = nP)
    (hnP : nP < 2 ^ 62) (hpl : ctx.params.length < 2 ^ 59) (e : EIdx) (H : List (BitVec 64)) (hp : C.H <+: H)
    (hpp : BlkAt H pp (ctx.params.map Enc.idxW)) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (rxParams.zip [Enc.idxW e, cellA C om, BitVec.ofNat 64 nP, Enc.idxW ctx.lvls,
      cellA C pp])) rxBody s (replaceFVars (.holeImg ctx [] 0) e) (PostK (ctxH C H)) := by
  refine specR_prologue (postK_locals _) (rx_none _ _) ?_
  rw [replaceFVars]
  have hm0 : MemoRep C.HB H 0 ∅ := ⟨[], rfl, fun k => by simp⟩
  refine specR_callNIH (C := ctxH C H) rxQ fRhi rhiParams
    [.const (BitVec.ofNat 64 coreWalkFuel), vv rxE, .const 0, vv rxMs, vv rxNP, vv rxUs, vv rxP] (rhiBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e, 0, cellA C om, BitVec.ofNat 64 nP, Enc.idxW ctx.lvls, cellA C pp]
    (by decide) rfl (by decide) hc.rhi.self
    ⟨rfl, by simp +decide [sev, Env.get, rxParams, ctxEnv], rfl, by simp +decide [sev, Env.get, rxParams, ctxEnv],
      by simp +decide [sev, Env.get, rxParams, ctxEnv], by simp +decide [sev, Env.get, rxParams, ctxEnv],
      by simp +decide [sev, Env.get, rxParams, ctxEnv], trivial⟩
    (PostRHI (ctxH C H)) (fun r w _ H' => ∃ op mw', w = cellA C op ∧ H'[op]? = some (Enc.idxW r.1) ∧
      H'[op + 1]? = some mw' ∧ MemoRep C.HB H' mw' r.2)
    (fun r w s' st ⟨H', op, mw', hp', hw, h1, h2, h3, hsr⟩ => ⟨H', hp', ⟨op, mw', hw, h1, h2, by exact h3⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rhiParams _ rfl hlk)
      (rhi_spec ra C hok hc.rhi ctx ms om nP pp hml hM hN hP hnP hpl coreWalkFuel CV.coreWalkFuel_lt e ∅ 0 H s hp hpp hm0))
    (fun r w s1 H1 hp1 ⟨op, mw', hw, h1, _, _⟩ => ?_)
  subst hw
  refine UD.specR_heapLoadI' (C := ctxH C H1) rxR (vv rxQ) op _ h1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  exact specR_returnI _ (Enc.idxW r.1) (by simp [sev, Env.get_cons])
    (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

section
variable {σ : Type}

/-- **`xs.mapM (replaceFVars holeImg)`** from `j` on, appended to `acc`. -/
theorem rhm_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : NNFCodes C)
    (ctx : NestCtx) (ms : List MemberShape) (om nP pp : Nat) (hml : ms.length < 2 ^ 59)
    (hM : PtrsRep C C.H om (MemberRep C C.H) ms) (hN : ctx.names = ms.map (·.cvT.name)) (hP : ctx.nP = nP)
    (hnP : nP < 2 ^ 62) (hpl : ctx.params.length < 2 ^ 59) (xs : List EIdx) (oa : Nat) (hxl : xs.length < 2 ^ 58) :
    ∀ f j (acc : List EIdx) (oc : Nat) (H : List (BitVec 64)) (s : AState), xs.length - j = f → j ≤ xs.length →
      C.H <+: H → BlkAt H oa (xs.map Enc.idxW) → BlkAt H oc (acc.map Enc.idxW) → BlkAt H pp (ctx.params.map Enc.idxW) →
      SpecR (σ := σ) (Pre (ctxH C H) s (rhmParams.zip [cellA C oa, BitVec.ofNat 64 j, cellA C oc, cellA C om,
        BitVec.ofNat 64 nP, Enc.idxW ctx.lvls, cellA C pp])) rhmBody s
        ((xs.drop j).mapM (fun x => replaceFVars (.holeImg ctx [] 0) x) >>= fun r => pure (acc ++ r))
        (PostA (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro j acc oc H s hf hj hp hb hacc hpp
    have hjl : j = xs.length := by omega
    subst hjl
    refine specR_prologue (postA_locals _) (rhm_none _ _) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) rhmL (vv rhmA) oa _ hb.1 (by decide)
      (by simp +decide [sev, Env.get, rhmParams, ctxEnv]; rfl) ?_
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, rhmParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [List.drop_length, List.mapM_nil, pure_bind, List.append_nil]
    exact specR_returnI _ (cellA C oc) (by simp +decide [sev, Env.get_cons, Env.get, rhmParams, ctxEnv])
      (fun t ht => ⟨H, oc, List.prefix_refl _, rfl, hacc, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro j acc oc H s hf hj hp hb hacc hpp
    have hjl : j < xs.length := by omega
    refine specR_prologue (postA_locals _) (rhm_none _ _) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) rhmL (vv rhmA) oa _ hb.1 (by decide)
      (by simp +decide [sev, Env.get, rhmParams, ctxEnv]; rfl) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff j xs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, rhmParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hjl]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_congr (m' := replaceFVars (.holeImg ctx [] 0) xs[j] >>= fun y =>
      (xs.drop (j + 1)).mapM (fun x => replaceFVars (.holeImg ctx [] 0) x) >>= fun r => pure ((acc ++ [y]) ++ r))
      (by have hd : xs.drop j = xs[j] :: xs.drop (j + 1) := List.drop_eq_getElem_cons hjl
          rw [hd, List.mapM_cons]; simp only [bind_assoc, pure_bind, List.append_assoc, List.singleton_append]) ?_
    have h1 := hb.2 j (by simpa using hjl)
    rw [List.getElem_map] at h1
    refine UD.specR_heapLoadI' (C := ctxH C H) rhmX _ (oa + 1 + j) (Enc.idxW xs[j]) h1 (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, rhmParams, ctxEnv]; show _ = cellA C (oa + 1 + j)
          rw [← cellA_shl C (oa + 1) j (by omega), ← cellA_add8]; rfl) ?_
    refine specR_callNIH (C := ctxH C H) rhmY fRhiTop rxParams [vv rhmX, vv rhmMs, vv rhmNP, vv rhmUs, vv rhmP] rxBody
      [Enc.idxW xs[j], cellA C om, BitVec.ofNat 64 nP, Enc.idxW ctx.lvls, cellA C pp] (by decide) rfl (by decide) hc.rx
      ⟨by simp [sev, Env.get_cons], (by simp +decide [sev, Env.get_cons, Env.get, rhmParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, rhmParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, rhmParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, rhmParams, ctxEnv]), trivial⟩
      (PostK (ctxH C H)) (fun r w _ _ => w = Enc.idxW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rxParams _ rfl hlk)
        (rx_spec ra C hok hc ctx ms om nP pp hml hM hN hP hnP hpl xs[j] H hp hpp s))
      (fun y w s1 H1 hp1 hw => ?_)
    subst hw
    have hp1' : H <+: H1 := hp1
    refine specR_appendI hok hc.app H1 rhmAcc2 (vv rhmAcc) (vv rhmY) (acc.map Enc.idxW) (Enc.idxW y) oc
      (blkAt_mono hacc hp1') (by decide) (by simp +decide [sev, Env.get_cons, Env.get, rhmParams, ctxEnv]) (by simp [sev, Env.get_cons]) (fun H2 oc2 hp2 hacc2 => ?_)
    refine specR_congr (m' := ((xs.drop (j + 1)).mapM (fun x => replaceFVars (.holeImg ctx [] 0) x) >>=
      fun r => pure ((acc ++ [y]) ++ r)) >>= fun r => pure r) (by simp only [bind_pure]) ?_
    refine specR_callNIH (C := ctxH C H2) rhmR fRhiMap rhmParams
      [vv rhmA, .op .add [vv rhmJ, .const 1], vv rhmAcc2, vv rhmMs, vv rhmNP, vv rhmUs, vv rhmP] rhmBody
      [cellA C oa, BitVec.ofNat 64 (j + 1), cellA C oc2, cellA C om, BitVec.ofNat 64 nP, Enc.idxW ctx.lvls, cellA C pp]
      (by decide) rfl (by decide) hc.rm
      ⟨(by simp +decide [sev, Env.get_cons, Env.get, rhmParams, ctxEnv]), by simp +decide [sev, Env.get_cons, Env.get, rhmParams, ctxEnv]; exact e_succ j,
        by simp [sev, Env.get_cons], (by simp +decide [sev, Env.get_cons, Env.get, rhmParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, rhmParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, rhmParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, rhmParams, ctxEnv]), trivial⟩
      (PostA (ctxH C H2)) (fun a w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (a.map Enc.idxW))
      (fun a w s' st ⟨H', o, hp', hw, hb', hsr⟩ => ⟨H', hp', ⟨o, hw, hb'⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rhmParams _ rfl hlk)
        (ih (j + 1) (acc ++ [y]) oc2 H2 s1 (by omega) (by omega) ((hp.trans hp1').trans hp2)
          (blkAt_mono hb (hp1'.trans hp2)) (by simpa using hacc2) (blkAt_mono hpp (hp1'.trans hp2))))
      (fun r w s3 H3 hp3 ⟨o3, hw3, hb3⟩ => ?_)
    subst hw3
    exact specR_returnI _ (cellA C o3) (by simp [sev, Env.get_cons])
      (fun t ht => ⟨H3, o3, (hp1'.trans hp2).trans hp3, rfl, hb3, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- A record pointer, the heap extended. -/
def PostNNF (C : Ctx) (nf : NestCtorNf) (w : BitVec 64) (s' : AState) (st : PState σ) : Prop :=
  ∃ H' o, C.H <+: H' ∧ w = cellA C o ∧ NfRep C H' o nf ∧ SR (ctxH C H') s' st

theorem postNNF_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostNNF C a w s' st → PostNNF C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, hp, hw, h1, hs⟩ => ⟨H', o, hp, hw, h1, sr_of_eq hs rfl rfl rfl rfl⟩

/-- **`nestCtorNf`** at the root frame (its key the block's levels and canonical parameters). -/
theorem nnf_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C) (hc : NNFCodes C)
    (ctx : NestCtx) (ms : List MemberShape) (om nP pp : Nat) (hml : ms.length < 2 ^ 59)
    (hM : PtrsRep C C.H om (MemberRep C C.H) ms) (hN : ctx.names = ms.map (·.cvT.name)) (hP : ctx.nP = nP)
    (hnP : nP < 2 ^ 62) (hpl : ctx.params.length < 2 ^ 58) (cv : IConstantVal) (closed : EIdx)
    (H : List (BitVec 64)) (hp : C.H <+: H) (hpp : BlkAt H pp (ctx.params.map Enc.idxW)) (s : AState) :
    SpecR (σ := σ) (Pre (ctxH C H) s (nnfParams.zip [Enc.idxW cv.name, Enc.idxW ctx.lvls, cellA C pp, Enc.idxW closed,
      cellA C om, BitVec.ofNat 64 nP, cellA C pp])) (nnfBody C) s (nestCtorNf ctx [] ctx.lvls ctx.params cv closed)
      (PostNNF (ctxH C H)) := by
  refine specR_prologue (postNNF_locals _) (nnf_none _ _) ?_
  rw [nestCtorNf]
  simp only [List.length_nil]
  refine specR_alloc1I (ctxOK_H hok H) nnfA0 (.const 0) 0 (by decide) (fun _ => rfl) (fun H0 ws hp0 hws => ?_)
  have g0 : ((H0 ++ ws).set H0.length 0)[H0.length]? = some 0 := by simp [List.getElem?_set, hws]
  have h0 : H0 <+: ((H0 ++ ws).set H0.length 0) := img1_prefix H0 ws 0 hws
  have hp0' : H <+: _ := (hp0 : H <+: H0).trans h0
  have hb0 : BlkAt ((H0 ++ ws).set H0.length 0) H0.length (([] : List EIdx).map Enc.idxW) :=
    ⟨by simpa using g0, fun i hi => by simp at hi⟩
  refine specR_congr (m' := ((ctx.params.drop 0).mapM (fun x => replaceFVars (.holeImg ctx [] 0) x) >>=
    fun r => pure ([] ++ r)) >>= fun ds2 => replaceFVars (.holeImg ctx [] 0) closed >>= fun ty =>
      pure ({ ctor := cv.name, lvls := ctx.lvls, ds := ds2, ty } : NestCtorNf)) (by simp) ?_
  refine specR_callNIH (C := ctxH C _) nnfD2 fRhiMap rhmParams
    [vv nnfDs, .const 0, vv nnfA0, vv nnfMs, vv nnfNP, vv nnfUs, vv nnfP] rhmBody
    [cellA C pp, BitVec.ofNat 64 0, cellA C H0.length, cellA C om, BitVec.ofNat 64 nP, Enc.idxW ctx.lvls, cellA C pp]
    (by decide) rfl (by decide) hc.rm
    ⟨by simp +decide [sev, Env.get_cons, Env.get, nnfParams, ctxEnv], rfl, by simp [sev, Env.get_cons]; rfl,
      by simp +decide [sev, Env.get_cons, Env.get, nnfParams, ctxEnv], (by simp +decide [sev, Env.get_cons, Env.get, nnfParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nnfParams, ctxEnv]),
      by simp +decide [sev, Env.get_cons, Env.get, nnfParams, ctxEnv], trivial⟩
    (PostA (ctxH C _)) (fun a w _ H' => ∃ o, w = cellA C o ∧ BlkAt H' o (a.map Enc.idxW))
    (fun a w s' st ⟨H', o, hp', hw, hb', hsr⟩ => ⟨H', hp', ⟨o, hw, hb'⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rhmParams _ rfl hlk)
      (rhm_spec ra C hok hc ctx ms om nP pp hml hM hN hP hnP (by omega) ctx.params pp hpl _ 0 [] H0.length _ s rfl
        (by omega) (hp.trans hp0') (blkAt_mono hpp hp0') hb0 (blkAt_mono hpp hp0')))
    (fun ds2 w s1 H1 hp1 ⟨o1, hw1, hb1⟩ => ?_)
  subst hw1
  have hp1' : H <+: H1 := hp0'.trans hp1
  refine specR_callNIH (C := ctxH C H1) nnfT fRhiTop rxParams [vv nnfCl, vv nnfMs, vv nnfNP, vv nnfUs, vv nnfP] rxBody
    [Enc.idxW closed, cellA C om, BitVec.ofNat 64 nP, Enc.idxW ctx.lvls, cellA C pp] (by decide) rfl (by decide) hc.rx
    ⟨(by simp +decide [sev, Env.get_cons, Env.get, nnfParams, ctxEnv]), by simp +decide [sev, Env.get_cons, Env.get, nnfParams, ctxEnv], (by simp +decide [sev, Env.get_cons, Env.get, nnfParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nnfParams, ctxEnv]),
      by simp +decide [sev, Env.get_cons, Env.get, nnfParams, ctxEnv], trivial⟩
    (PostK (ctxH C H1)) (fun r w _ _ => w = Enc.idxW r) (fun r w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu rxParams _ rfl hlk)
      (rx_spec ra C hok hc ctx ms om nP pp hml hM hN hP hnP (by omega) closed H1 (hp.trans hp1') (blkAt_mono hpp hp1') s1))
    (fun ty w s2 H2 hp2 hw => ?_)
  subst hw
  have hp2' : H1 <+: H2 := hp2
  refine specR_alloc4I (ctxOK_H hok H2) nnfR (vv nnfNm) (vv nnfUs) (vv nnfD2) (vv nnfT) (Enc.idxW cv.name)
    (Enc.idxW ctx.lvls) (cellA C o1) (Enc.idxW ty) (by decide) (fun _ => (by simp +decide [sev, Env.get_cons, Env.get, nnfParams, ctxEnv])) (fun _ => (by simp +decide [sev, Env.get_cons, Env.get, nnfParams, ctxEnv]))
    (fun _ => (by simp +decide [sev, Env.get_cons, Env.get, nnfParams, ctxEnv])) (fun _ => (by simp +decide [sev, Env.get_cons, Env.get, nnfParams, ctxEnv])) (fun H4 ws4 hp4 hws4 _ => ?_)
  obtain ⟨k0, k1, k2, k3⟩ := img4_get H4 ws4 _ _ _ _ hws4
  have h4 := img4_prefix H4 ws4 (Enc.idxW cv.name) (Enc.idxW ctx.lvls) (cellA C o1) (Enc.idxW ty) hws4
  have hp4' : H2 <+: _ := (hp4 : H2 <+: H4).trans h4
  try simp only [List.nil_append]
  exact specR_returnI (vv nnfR) (cellA C H4.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht =>
    ⟨_, H4.length, ((hp1'.trans hp2').trans hp4'), rfl,
      ⟨k0, k1, ⟨o1, k2, blkAt_mono (blkAt_mono hb1 hp2') hp4'⟩, k3⟩, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
