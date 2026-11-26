import ConPanqueque.T.Ind.CloseTele
import ConPanqueque.T.Core.InferIOArms
import ConPanqueque.T.Core.FormerLoop

/-!
# `nestPos` (the unnested subset): the positivity walk of one field

The frame stack stays empty (a stored inductive's application, `nestCont`, hangs), so the walk's state passes
through unchanged.  Here: `nestOcc` at a fresh memo, and `args.anyM nestOcc`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def ntE := ofString "nt_e"
def ntMs := ofString "nt_ms"
def ntLo := ofString "nt_lo"
def ntHi := ofString "nt_hi"
def ntQ := ofString "nt_q"
def ntR := ofString "nt_r"
def fNocTop := ofString "nestOcc"

def ntParams : List MlS := [ntE, ntMs, ntLo, ntHi]
def ntLocals : List MlS := [ntQ, ntR]

def ntBody : ProgHOL 64 := prologue ntLocals
  (.seq (.call (some (some (.local, ntQ), none)) fNestOcc
      [.const (BitVec.ofNat 64 coreWalkFuel), vv ntE, .const 0, vv ntMs, vv ntLo, vv ntHi])
  (.seq (.assign .local ntR (.load .one (vv ntQ))) (.return (vv ntR))))

def ayA := ofString "ay_a"
def ayJ := ofString "ay_j"
def ayMs := ofString "ay_ms"
def ayLo := ofString "ay_lo"
def ayHi := ofString "ay_hi"
def ayL := ofString "ay_l"
def ayX := ofString "ay_x"
def ayO := ofString "ay_o"
def ayR := ofString "ay_r"
def fAnyNoc := ofString "anyNestOcc"

def ayParams : List MlS := [ayA, ayJ, ayMs, ayLo, ayHi]
def ayLocals : List MlS := [ayL, ayX, ayO, ayR]

def ayBody : ProgHOL 64 := prologue ayLocals
  (.seq (.assign .local ayL (.load .one (vv ayA)))
  (.ite (.cmp .lower (vv ayJ) (vv ayL))
    (.seq (.assign .local ayX (.load .one (.op .add [.op .add [vv ayA, .const 8], .shift .lsl (vv ayJ) (.const 3)])))
    (.seq (.call (some (some (.local, ayO), none)) fNocTop [vv ayX, vv ayMs, vv ayLo, vv ayHi])
    (.ite (.cmp .equal (vv ayO) (.const 0))
      (.seq (.call (some (some (.local, ayR), none)) fAnyNoc
          [vv ayA, .op .add [vv ayJ, .const 1], vv ayMs, vv ayLo, vv ayHi]) (.return (vv ayR)))
      (.return (.const 1)))))
    (.return (.const 0))))

structure NTCodes (C : Ctx) : Prop where
  noc : NOCCodes C
  top : C.code.lookup fNocTop = some (ntParams.map (fun p => (p, ShapeHOL.one)), ntBody, .one)
  any : C.code.lookup fAnyNoc = some (ayParams.map (fun p => (p, ShapeHOL.one)), ayBody, .one)

section
variable {σ : Type}

theorem nt_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ntLocals → (ctxEnv C ++ ntParams.zip vals).get x = none :=
  Knot.params_none C ntLocals ntParams vals (by decide) (by decide)

theorem ay_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ ayLocals → (ctxEnv C ++ ayParams.zip vals).get x = none :=
  Knot.params_none C ayLocals ayParams vals (by decide) (by decide)

/-- **`nestOcc`** at the block's members. -/
theorem nt_spec (C : Ctx) (hok : CtxOK C) (hc : NTCodes C) (ms : List MemberShape) (om : Nat)
    (hM : PtrsRep C C.H om (MemberRep C C.H) ms) (hml : ms.length < 2 ^ 59) (lo hi : Nat)
    (hlo : lo < 2 ^ 64) (hhi : hi < 2 ^ 64) (e : EIdx) (H : List (BitVec 64)) (s : AState) (hp : C.H <+: H) :
    SpecR (σ := σ) (Pre (ctxH C H) s (ntParams.zip [Enc.idxW e, cellA C om, BitVec.ofNat 64 lo, BitVec.ofNat 64 hi]))
      ntBody s (nestOcc (ms.map (·.cvT.name)) lo hi e) (PostB (ctxH C H)) := by
  refine specR_prologue (postB_locals _) (nt_none _ _) ?_
  rw [nestOcc]
  have hm0 : MemoRepB C.HB H 0 ∅ := ⟨[], rfl, fun k => by simp⟩
  refine specR_callNIH (C := ctxH C H) ntQ fNestOcc nocParams
    [.const (BitVec.ofNat 64 coreWalkFuel), vv ntE, .const 0, vv ntMs, vv ntLo, vv ntHi] (nocBody C)
    [BitVec.ofNat 64 coreWalkFuel, Enc.idxW e, 0, cellA C om, BitVec.ofNat 64 lo, BitVec.ofNat 64 hi] (by decide) rfl
    (by decide) hc.noc.self
    ⟨rfl, by simp +decide [sev, Env.get, ntParams, ctxEnv], rfl, by simp +decide [sev, Env.get, ntParams, ctxEnv],
      by simp +decide [sev, Env.get, ntParams, ctxEnv], by simp +decide [sev, Env.get, ntParams, ctxEnv], trivial⟩
    (PostNO (ctxH C H)) (fun r w _ H' => ∃ op mw', w = cellA C op ∧ H'[op]? = some (boolW r.1) ∧
      H'[op + 1]? = some mw' ∧ MemoRepB C.HB H' mw' r.2)
    (fun r w s' st ⟨H', op, mw', hp', hw, h1, h2, h3, hsr⟩ => ⟨H', hp', ⟨op, mw', hw, h1, h2, by exact h3⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu nocParams _ rfl hlk)
      (noc_spec C hok hc.noc ms om hM hml lo hi hlo hhi coreWalkFuel CV.coreWalkFuel_lt e ∅ 0 H s hp hm0))
    (fun r w s1 H1 hp1 ⟨op, mw', hw, h1, _, _⟩ => ?_)
  subst hw
  refine UD.specR_heapLoadI' (C := ctxH C H1) ntR (vv ntQ) op _ h1 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  exact specR_returnI _ (boolW r.1) (by simp [sev, Env.get_cons])
    (fun t ht => ⟨H1, hp1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

/-- **`args.anyM nestOcc`** over a block from `j` on. -/
theorem ay_spec (C : Ctx) (hok : CtxOK C) (hc : NTCodes C) (ms : List MemberShape) (om : Nat)
    (hM : PtrsRep C C.H om (MemberRep C C.H) ms) (hml : ms.length < 2 ^ 59) (lo hi : Nat)
    (hlo : lo < 2 ^ 64) (hhi : hi < 2 ^ 64) (xs : List EIdx) (oa : Nat) (hxl : xs.length < 2 ^ 58) :
    ∀ f j (H : List (BitVec 64)) (s : AState), xs.length - j = f → j ≤ xs.length → C.H <+: H →
      BlkAt H oa (xs.map Enc.idxW) →
      SpecR (σ := σ) (Pre (ctxH C H) s (ayParams.zip [cellA C oa, BitVec.ofNat 64 j, cellA C om, BitVec.ofNat 64 lo,
        BitVec.ofNat 64 hi])) ayBody s ((xs.drop j).anyM (fun x => nestOcc (ms.map (·.cvT.name)) lo hi x))
        (PostB (ctxH C H)) := by
  intro f
  induction f with
  | zero =>
    intro j H s hf hj hp hb
    have hjl : j = xs.length := by omega
    subst hjl
    refine specR_prologue (postB_locals _) (ay_none _ _) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) ayL (vv ayA) oa _ hb.1 (by decide)
      (by simp +decide [sev, Env.get, ayParams, ctxEnv]; rfl) ?_
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, ayParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro j H s hf hj hp hb
    have hjl : j < xs.length := by omega
    refine specR_prologue (postB_locals _) (ay_none _ _) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) ayL (vv ayA) oa _ hb.1 (by decide)
      (by simp +decide [sev, Env.get, ayParams, ctxEnv]; rfl) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff j xs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, ayParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hjl]) (fun _ => ?_) (fun h => absurd h (by decide))
    rw [List.drop_eq_getElem_cons hjl, List.anyM]
    have h1 := hb.2 j (by simpa using hjl)
    rw [List.getElem_map] at h1
    refine UD.specR_heapLoadI' (C := ctxH C H) ayX _ (oa + 1 + j) (Enc.idxW xs[j]) h1 (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, ayParams, ctxEnv]; show _ = cellA C (oa + 1 + j)
          rw [← cellA_shl C (oa + 1) j (by omega), ← cellA_add8]; rfl) ?_
    refine specR_callNIH (C := ctxH C H) ayO fNocTop ntParams [vv ayX, vv ayMs, vv ayLo, vv ayHi] ntBody
      [Enc.idxW xs[j], cellA C om, BitVec.ofNat 64 lo, BitVec.ofNat 64 hi] (by decide) rfl (by decide) hc.top
      ⟨by simp [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, ayParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, ayParams, ctxEnv],
        by simp +decide [sev, Env.get_cons, Env.get, ayParams, ctxEnv], trivial⟩
      (PostB (ctxH C H)) (fun a w _ _ => w = boolW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ntParams _ rfl hlk)
        (nt_spec C hok hc ms om hM hml lo hi hlo hhi xs[j] H s hp))
      (fun b w s1 H1 hp1 hw => ?_)
    subst hw
    have hp1' : H <+: H1 := hp1
    cases b
    · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only
      refine specR_congr (m' := (xs.drop (j + 1)).anyM (fun x => nestOcc (ms.map (·.cvT.name)) lo hi x) >>=
        fun r => pure r) (by simp) ?_
      refine specR_callNIH (C := ctxH C H1) ayR fAnyNoc ayParams
        [vv ayA, .op .add [vv ayJ, .const 1], vv ayMs, vv ayLo, vv ayHi] ayBody
        [cellA C oa, BitVec.ofNat 64 (j + 1), cellA C om, BitVec.ofNat 64 lo, BitVec.ofNat 64 hi] (by decide) rfl
        (by decide) hc.any
        ⟨by simp +decide [sev, Env.get_cons, Env.get, ayParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, ayParams, ctxEnv]; exact e_succ j,
          by simp +decide [sev, Env.get_cons, Env.get, ayParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, ayParams, ctxEnv],
          by simp +decide [sev, Env.get_cons, Env.get, ayParams, ctxEnv], trivial⟩
        (PostB (ctxH C H1)) (fun a w _ _ => w = boolW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ayParams _ rfl hlk)
          (ih (j + 1) H1 s1 (by omega) (by omega) (hp.trans hp1) (blkAt_mono hb hp1')))
        (fun r w s3 H3 hp3 hw => ?_)
      subst hw
      exact specR_returnI _ (boolW r) (by simp [sev, Env.get_cons])
        (fun t ht => ⟨H3, hp1'.trans hp3, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    · refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun h => absurd rfl h) (fun _ => ?_)
      simp only
      exact specR_returnI _ 1 rfl (fun t ht => ⟨H1, hp1', rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## The walk -/

def npFu := ofString "np_fu"
def npD := ofString "np_d"
def npKb := ofString "np_kb"
def npE := ofString "np_e"
def npMs := ofString "np_ms"
def npNP := ofString "np_np"
def npHi := ofString "np_hi"
def npW := ofString "np_w"
def npO := ofString "np_o"
def npA := ofString "np_a"
def npB := ofString "np_b"
def npF := ofString "np_f"
def npB2 := ofString "np_b2"
def npQ := ofString "np_q"
def npK := ofString "np_k"
def npNb := ofString "np_nb"
def npNb2 := ofString "np_nb2"
def npR2 := ofString "np_r2"
def npG := ofString "np_g"
def npHd := ofString "np_hd"
def npI := ofString "np_i"
def npT := ofString "np_t"
def npL := ofString "np_l"
def npP := ofString "np_p"
def npX := ofString "np_x"
def npN := ofString "np_n"
def npR := ofString "np_r"
def fNestPos := ofString "nestPos"

def npParams : List MlS := [npFu, npD, npKb, npE, npMs, npNP, npHi]
def npLocals : List MlS := gaaLocals ++ [npW, npO, npA, npB, npF, npB2, npQ, npK, npNb, npNb2, npR2, npG, npHd, npI, npT,
  npL, npP, npX, npN, npR]

/-- A field kind as a word. -/
def kindW : NestFieldKind → BitVec 64
  | .ordinary => 0
  | .recursive t => BitVec.ofNat 64 (4 * t + 1)
  | .reflexive t => BitVec.ofNat 64 (4 * t + 2)
  | .inProgress => 3
  | .nested false => 7
  | .nested true => 11

def npRet (C : Ctx) (k : ExpHOL 64) (x : MlS) : ProgHOL 64 := alloc2 C npR k (vv x) (.return (vv npR))

def npHole (C : Ctx) : ProgHOL 64 :=
  .ite (.cmp .lower (vv npI) (vv npNP)) hang
  (.seq (.assign .local npT (.op .sub [vv npI, vv npNP]))
  (.seq (.assign .local npL (.load .one (vv npMs)))
  (.ite (.cmp .lower (vv npT) (vv npL))
    (.seq (.assign .local npP (.load .one (.op .add [.op .add [vv npMs, .const 8], .shift .lsl (vv npT) (.const 3)])))
    (.seq (.assign .local npX (.load .one (.op .add [vv npP, .const 16])))
    (.seq (.call (some (some (.local, npO), none)) fAnyNoc [vv npG, .const 0, vv npMs, vv npNP, vv npHi])
    (.ite (.cmp .equal (vv npO) (.const 0))
      (.seq (.assign .local npN (.load .one (vv npG)))
      (.ite (.cmp .equal (vv npN) (vv npX))
        (.ite (.cmp .equal (vv npKb) (.const 0))
          (.seq (.assign .local npK (.op .add [.shift .lsl (vv npT) (.const 2), .const 1])) (npRet C (vv npK) npW))
          (.seq (.assign .local npK (.op .add [.shift .lsl (vv npT) (.const 2), .const 2])) (npRet C (vv npK) npW)))
        hang))
      hang))))
    hang)))

def npApp (C : Ctx) : ProgHOL 64 :=
  .seq (.call (some (some (.local, npG), none)) ExG.fGaa [.const (BitVec.ofNat 64 coreWalkFuel), vv npW])
  (.seq (.call (some (some (.local, npHd), none)) fGetAppFn [.const (BitVec.ofNat 64 coreWalkFuel), vv npW])
  (.seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv npHd)) (.seq eViewP
  (.ite (.cmp .equal (vv lDg) (.const 1))
    (.ite (.cmp .equal (vv lRn) (.const 1)) (.seq (.assign .local npI (.const 0)) (npHole C))
      (.ite (.cmp .equal (vv lRn) (.const 2))
        (.seq (.assign .local npI (.load .one (.op .add [vv lRp, .const 8]))) (npHole C)) hang))
    hang)))))

def npForall (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local lFl (vv lFle)) (.seq (.assign .local lDh (vv npW)) (.seq eViewP
  (.seq (.assign .local npA (.load .one (vv lRp)))
  (.seq (.assign .local npB (.load .one (.op .add [vv lRp, .const 8])))
  (.seq (.call (some (some (.local, npO), none)) fNocTop [vv npA, vv npMs, vv npNP, vv npHi])
  (.ite (.cmp .equal (vv npO) (.const 0))
    (.seq (.call (some (some (.local, npF), none)) fInternFVar [vv npA, vv npD])
    (.seq (.call (some (some (.local, npB2), none)) ExI.fInst1F
        [.const (BitVec.ofNat 64 coreWalkFuel), vv npB, vv npF, .const 0])
    (.seq (.call (some (some (.local, npQ), none)) fNestPos
        [.op .sub [vv npFu, .const 1], .op .add [vv npD, .const 1], .op .add [vv npKb, .const 1], vv npB2,
          vv npMs, vv npNP, vv npHi])
    (.seq (.assign .local npK (.load .one (vv npQ)))
    (.seq (.assign .local npNb (.load .one (.op .add [vv npQ, .const 8])))
    (.seq (.call (some (some (.local, npNb2), none)) ExA.fAbs1F
        [.const (BitVec.ofNat 64 coreWalkFuel), vv npD, .const 0, vv npNb])
    (.seq (.call (some (some (.local, npR2), none)) fInternForallE [vv npA, vv npNb2])
      (npRet C (vv npK) npR2))))))))
    hang))))))

def npBody (C : Ctx) : ProgHOL 64 := prologue npLocals
  (.ite (.cmp .equal (vv npFu) (.const 0)) hang
  (.seq (.call (some (some (.local, npW), none)) fW [.const (BitVec.ofNat 64 checkFuel), vv npD, vv npE])
  (.seq (.call (some (some (.local, npO), none)) fNocTop [vv npW, vv npMs, vv npNP, vv npHi])
  (.ite (.cmp .equal (vv npO) (.const 0))
    (.seq (.call (some (some (.local, npO), none)) fNocTop [vv npE, vv npMs, vv npNP, vv npHi])
      (.ite (.cmp .equal (vv npO) (.const 0)) (npRet C (.const 0) npE) (npRet C (.const 0) npW)))
    (.ite (tagIsE npW 6) (npForall C) (npApp C))))))

structure NPCodes (C : Ctx) : Prop where
  nt : NTCodes C
  w : C.code.lookup fW = some (pmap kParams, whnfE C fWB, .one)
  fv : C.code.lookup fInternFVar = some ([(lEty, .one), (lIw, .one)], fvarBody, .one)
  i1 : C.code.lookup ExI.fInst1F = some ([pFu, pH, ExI.pV, ExI.pD].map (fun p => (p, ShapeHOL.one)),
    ExI.fastBody C, .one)
  i1c : ExI.Codes C (ExI.body C)
  a1 : C.code.lookup ExA.fAbs1F = some ([pFu, ExA.pAd, ExI.pD, pH].map (fun p => (p, ShapeHOL.one)),
    ExA.fastBodyA C, .one)
  a1c : ExA.CodesA C (ExA.bodyA C)
  cR : ExR.CodesR C (ExR.bodyR C)
  gf : C.code.lookup fGetAppFn = some ([(pFu, .one), (pH, .one)], getAppFnBody, .one)
  gaa : C.code.lookup ExG.fGaa = some ([(pFu, .one), (pH, .one)], ExG.gaaBody C, .one)
  self : C.code.lookup fNestPos = some (npParams.map (fun p => (p, ShapeHOL.one)), npBody C, .one)

section
variable {σ : Type}

theorem np_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ npLocals → (ctxEnv C ++ npParams.zip vals).get x = none :=
  Knot.params_none C npLocals npParams vals (by decide) (by decide)

/-- The walk's answer `[kind, expr]`, the state unchanged. -/
def PostNP (C : Ctx) (ns : NestState) (r : NestFieldKind × EIdx × NestState) (w : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  ∃ H' op, C.H <+: H' ∧ w = cellA C op ∧ H'[op]? = some (kindW r.1) ∧ H'[op + 1]? = some (Enc.idxW r.2.1) ∧
    r.2.2 = ns ∧ SR (ctxH C H') s' st

theorem postNP_locals (C : Ctx) (ns : NestState) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostNP C ns a w s' st → PostNP C ns a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', op, hp, hw, h1, h2, h3, hs⟩ => ⟨H', op, hp, hw, h1, h2, h3, sr_of_eq hs rfl rfl rfl rfl⟩

theorem np_ret (C : Ctx) (hok : CtxOK C) {s : AState} {Γ : Env} {M : Mem} (H Hb : List (BitVec 64)) (hbH : Hb <+: H)
    (ke : ExpHOL 64) (k : NestFieldKind) (x : MlS) (e : EIdx) (ns : NestState)
    (hk : ∀ v, sev ((npR, v) :: Γ) ke = some (kindW k)) (gx : ∀ v, sev ((npR, v) :: Γ) (vv x) = some (Enc.idxW e)) :
    SpecR (σ := σ) (Inv (ctxH C H) s Γ M (ctxLocals ++ npLocals)) (npRet C ke x) s (pure (k, e, ns))
      (PostNP (ctxH C Hb) ns) := by
  unfold npRet
  refine specR_alloc2I (ctxOK_H hok H) npR ke (vv x) (kindW k) (Enc.idxW e) (by decide) hk gx (fun H2 ws hp2 hws => ?_)
  obtain ⟨g0, g1⟩ := img2_get H2 ws (kindW k) (Enc.idxW e) hws
  have h2 := img2_prefix H2 ws (kindW k) (Enc.idxW e) hws
  exact specR_returnI (vv npR) (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht =>
    ⟨_, H2.length, hbH.trans ((hp2 : H <+: H2).trans h2), rfl, g0, g1, rfl, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

theorem holeAt_some (ctx : NestCtx) (ms : List MemberShape) (nP i : Nat) (hN : ctx.names = ms.map (·.cvT.name))
    (hP : ctx.nP = nP) (hI : ctx.nIdxs = ms.map (·.nIdx)) (h1 : nP ≤ i) (h2 : i - nP < ms.length) :
    ∃ hh, nestHoleAt ctx [] i = some hh ∧ hh.nIdx = ms[i - nP].nIdx := by
  refine ⟨{ key := ⟨ms[i - nP].cvT.name, ctx.lvls, ctx.params⟩, base := ctx.nP, nIdx := ms[i - nP].nIdx }, ?_, rfl⟩
  unfold nestHoleAt NestCtx.rootHoles
  simp [hP, h1, hN, hI, h2]

theorem holeAt_none (ctx : NestCtx) (ms : List MemberShape) (nP i : Nat) (hN : ctx.names = ms.map (·.cvT.name))
    (hP : ctx.nP = nP) (h : ¬ (nP ≤ i ∧ i - nP < ms.length)) : nestHoleAt ctx [] i = none := by
  unfold nestHoleAt NestCtx.rootHoles
  by_cases h1 : nP ≤ i
  · have h2 : ¬ i - nP < ms.length := fun e => h ⟨h1, e⟩
    simp [hP, h1, hN]; omega
  · simp [hP, h1]

theorem shl2_eq (t : Nat) (ht : t < 2 ^ 60) (c : Nat) (hc : c < 4) :
    BitVec.ofNat 64 t <<< 2 + BitVec.ofNat 64 c = BitVec.ofNat 64 (4 * t + c) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, BitVec.toNat_add, Nat.shiftLeft_eq]
  omega

end

section
variable {σ : Type}

set_option maxHeartbeats 16000000 in
/-- **`nestPos`** with no frames (a container application hangs). -/
theorem np_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (C : Ctx) (hok : CtxOK C)
    (hc : NPCodes C) (ms : List MemberShape) (om : Nat) (hM : PtrsRep C C.H om (MemberRep C C.H) ms)
    (hml : ms.length < 2 ^ 59) (nP : Nat) (hnP : nP < 2 ^ 62) (ctx : NestCtx) (hN : ctx.names = ms.map (·.cvT.name))
    (hP : ctx.nP = nP) (hI : ctx.nIdxs = ms.map (·.nIdx)) (hnI : ∀ t (ht : t < ms.length), ms[t].nIdx < 2 ^ 63)
    (ns : NestState)
    (hW : ∀ (H : List (BitVec 64)) s1, C.H <+: H → ∀ d e', d < 2 ^ 63 → Callee (σ := σ) (ctxH C H) kParams
      [BitVec.ofNat 64 checkFuel, BitVec.ofNat 64 d, Enc.idxW e'] (whnfE C fWB) s1 (whnf mode C.fe checkFuel d e')
      (PostK (ctxH C H))) :
    ∀ n dep kb (e : EIdx) (H : List (BitVec 64)) (s : AState), C.H <+: H → dep + n < 2 ^ 62 → kb + n < 2 ^ 62 →
      SpecR (σ := σ) (Pre (ctxH C H) s (npParams.zip [BitVec.ofNat 64 n, BitVec.ofNat 64 dep, BitVec.ofNat 64 kb,
        Enc.idxW e, cellA C om, BitVec.ofNat 64 nP, BitVec.ofNat 64 (nP + ms.length)])) (npBody C) s
        (nestPos mode C.fe ctx n [] dep kb e ns) (PostNP (ctxH C H) ns) := by
  intro n
  induction n with
  | zero =>
    intro dep kb e H s hp hd hk
    refine specR_prologue (postNP_locals _ _) (np_none _ _) ?_
    exact specR_ifI _ 1 (by simp +decide [sev, Env.get, npParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun _ => specR_hangI) (fun h => absurd h (by decide))
  | succ n ih =>
    intro dep kb e H s hp hd hk
    refine specR_prologue (postNP_locals _ _) (np_none _ _) ?_
    have hne : BitVec.ofNat 64 (n + 1) ≠ 0#64 := ofNat_ne_zero (n + 1) (by omega) (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get, npParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hne])
      (fun h => absurd rfl h) (fun _ => ?_)
    have hhi : ctx.hiAt 0 = nP + ms.length := by simp [NestCtx.hiAt, hP, hN]
    rw [nestPos]
    simp only [List.length_nil, hhi, hN, hP]
    refine Big.specR_callKC (C := ctxH C H) npW fW kParams [.const (BitVec.ofNat 64 checkFuel), vv npD, vv npE]
      (whnfE C fWB) [BitVec.ofNat 64 checkFuel, BitVec.ofNat 64 dep, Enc.idxW e] (by decide) rfl (by decide) hc.w
      ⟨rfl, (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]), trivial⟩ (hW H s hp dep e (by omega)) (fun w s1 H1 hp1 _ => ?_)
    have hp1' : H <+: H1 := hp1
    refine specR_callNIH (C := ctxH C H1) npO fNocTop ntParams [vv npW, vv npMs, vv npNP, vv npHi] ntBody
      [Enc.idxW w, cellA C om, BitVec.ofNat 64 nP, BitVec.ofNat 64 (nP + ms.length)] (by decide) rfl (by decide) hc.nt.top
      ⟨(by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]), by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv], (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]), trivial⟩
      (PostB (ctxH C H1)) (fun a w _ _ => w = boolW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ntParams _ rfl hlk)
        (nt_spec C hok hc.nt ms om hM hml nP (nP + ms.length) (by omega) (by omega) w H1 s1 (hp.trans hp1')))
      (fun b2 w2 s2 H2 hp2 hw2 => ?_)
    subst hw2
    have hp2' : H1 <+: H2 := hp2
    cases b2
    · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
      simp only [Bool.not_false, ↓reduceIte]
      refine specR_callNIH (C := ctxH C H2) npO fNocTop ntParams [vv npE, vv npMs, vv npNP, vv npHi] ntBody
        [Enc.idxW e, cellA C om, BitVec.ofNat 64 nP, BitVec.ofNat 64 (nP + ms.length)] (by decide) rfl (by decide) hc.nt.top
        ⟨(by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]), by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv], (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]), trivial⟩
        (PostB (ctxH C H2)) (fun a w _ _ => w = boolW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ntParams _ rfl hlk)
          (nt_spec C hok hc.nt ms om hM hml nP (nP + ms.length) (by omega) (by omega) e H2 s2 ((hp.trans hp1').trans hp2')))
        (fun b3 w3 s3 H3 hp3 hw3 => ?_)
      subst hw3
      have hp3' : H2 <+: H3 := hp3
      cases b3
      · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
        simp only [Bool.false_eq_true, ↓reduceIte]
        exact np_ret C hok H3 H ((hp1'.trans hp2').trans hp3') (.const 0) .ordinary npE e ns
          (fun _ => by simp [sev, kindW]) (fun _ => (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]))
      · refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
        simp only [↓reduceIte]
        exact np_ret C hok H3 H ((hp1'.trans hp2').trans hp3') (.const 0) .ordinary npW w ns
          (fun _ => by simp [sev, kindW]) (fun _ => (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]))
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    refine Knot.specR_tagIteV npW w 6 (by decide) (by decide) (by simp +decide [Env.get_cons, Env.get, npParams, ctxEnv]) (fun htg => ?_) (fun htg => ?_)
    · rw [ite_eq_left (show (w.tag == ETag.forallE) = true by simp [htg, ETag.forallE])]
      unfold npForall
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get_cons, Env.get, npParams, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv npW) (Enc.idxW w) (by decide) (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]) ?_
      refine ConPanqueque.T.Big.specR_viewP (C := ctxH C H2) w (by simp) (by simp +decide [Env.get_cons, Env.get] <;> rfl)
        (by simp +decide [Env.get_cons, Env.get, npParams, ctxEnv] <;> rfl) (by decide) (fun v P hv htn _ => ?_)
      have h6 : v.tagN = 6 := by rw [htn, htg]; rfl
      obtain ⟨ty, b, rfl⟩ : ∃ ty b, v = .forallE ty b := by
        cases v <;> simp [ENodeView.tagN] at h6 ⊢
      have hvb : s2.store.viewBind w = some (ty, b) := WC.viewBind_of_view_forallE (by rw [htg]; rfl) hv
      refine specR_runBind (by rw [WC.viewBind_run, hvb]) ?_
      dsimp only
      refine specR_loadI' npA (vv lRp) P (P + BitVec.ofNat 64 0) (Enc.idxW ty) (by decide) (by simp [sev, Env.get_cons]) (by simp)
        (by simpa [encEView, Enc.encBind] using wordsAt_mem0 P (Enc.idxW ty) [Enc.idxW b] []) ?_
      refine specR_loadI' npB _ (P + 8) (P + BitVec.ofNat 64 8) (Enc.idxW b) (by decide) (by simp +decide [sev, Env.get_cons]) rfl
        (by simpa [encEView, Enc.encBind] using wordsAt_mem1 P (Enc.idxW ty) (Enc.idxW b) [] []) ?_
      refine specR_callNIH (C := ctxH C H2) npO fNocTop ntParams [vv npA, vv npMs, vv npNP, vv npHi] ntBody
        [Enc.idxW ty, cellA C om, BitVec.ofNat 64 nP, BitVec.ofNat 64 (nP + ms.length)] (by decide) rfl (by decide) hc.nt.top
        ⟨(by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]), by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv], (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]), trivial⟩
        (PostB (ctxH C H2)) (fun a w _ _ => w = boolW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ntParams _ rfl hlk)
          (nt_spec C hok hc.nt ms om hM hml nP (nP + ms.length) (by omega) (by omega) ty H2 s2 ((hp.trans hp1').trans hp2')))
        (fun b3 w3 s3 H3 hp3 hw3 => ?_)
      subst hw3
      have hp3' : H2 <+: H3 := hp3
      cases b3
      · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
        simp only [Bool.false_eq_true, ↓reduceIte]
        have hp3all : C.H <+: H3 := ((hp.trans hp1').trans hp2').trans hp3'
        refine ILP.specR_internFVarI ra (ctxOK_H hok H3) hc.fv npF (vv npA) (vv npD) ty dep (by omega) (by decide)
          (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]) (fun fv s4 => ?_)
        refine ILP.callE_spec (C := ctxH C H3) npB2 ExI.fInst1F [pFu, pH, ExI.pV, ExI.pD]
          [.const (BitVec.ofNat 64 coreWalkFuel), vv npB, vv npF, .const 0] (ExI.fastBody C)
          [BitVec.ofNat 64 coreWalkFuel, Enc.idxW b, Enc.idxW fv, BitVec.ofNat 64 0] (by decide) rfl (by decide) hc.i1
          ⟨rfl, (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]), rfl, trivial⟩
          (ExI.fast_spec ra (ctxH C H3) (ctxOK_H hok H3) (ExIS.codes_H C H3 hc.i1c) s4 coreWalkFuel b fv 0
            CV.coreWalkFuel_lt (by decide)) (fun b2 s5 => ?_)
        refine specR_callNIH (C := ctxH C H3) npQ fNestPos npParams
          [.op .sub [vv npFu, .const 1], .op .add [vv npD, .const 1], .op .add [vv npKb, .const 1], vv npB2,
            vv npMs, vv npNP, vv npHi] (npBody C)
          [BitVec.ofNat 64 n, BitVec.ofNat 64 (dep + 1), BitVec.ofNat 64 (kb + 1), Enc.idxW b2, cellA C om,
            BitVec.ofNat 64 nP, BitVec.ofNat 64 (nP + ms.length)] (by decide) rfl (by decide) hc.self
          ⟨by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]; exact ofNat_succ_sub_one n,
            by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]; exact e_succ dep,
            by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]; exact e_succ kb,
            (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]), by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv], (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]), trivial⟩
          (PostNP (ctxH C H3) ns) (fun r w _ H' => ∃ op, w = cellA C op ∧ H'[op]? = some (kindW r.1) ∧
            H'[op + 1]? = some (Enc.idxW r.2.1) ∧ r.2.2 = ns)
          (fun r w s' st ⟨H', op, hp', hw, h1, h2, h3, hsr⟩ => ⟨H', hp', ⟨op, hw, h1, h2, h3⟩, hsr⟩)
          (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu npParams _ rfl hlk)
            (ih (dep + 1) (kb + 1) b2 H3 s5 hp3all (by omega) (by omega)))
          (fun r wq s6 H4 hp4 ⟨oq, hwq, hq0, hq1, hns⟩ => ?_)
        obtain ⟨k, nb, ns2⟩ := r
        simp only at hq0 hq1 hns
        subst ns2; subst hwq
        have hp4' : H3 <+: H4 := hp4
        simp only
        refine UD.specR_heapLoadI' (C := ctxH C H4) npK (vv npQ) oq _ hq0 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
        refine UD.specR_heapLoadI' (C := ctxH C H4) npNb _ (oq + 1) _ hq1 (by decide)
          (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C oq) ?_
        refine ILP.callE_spec (C := ctxH C H4) npNb2 ExA.fAbs1F [pFu, ExA.pAd, ExI.pD, pH]
          [.const (BitVec.ofNat 64 coreWalkFuel), vv npD, .const 0, vv npNb] (ExA.fastBodyA C)
          [BitVec.ofNat 64 coreWalkFuel, BitVec.ofNat 64 dep, BitVec.ofNat 64 0, Enc.idxW nb] (by decide) rfl (by decide)
          hc.a1 ⟨rfl, (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]), rfl, (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]), trivial⟩
          (ExA.fastA_spec ra (ctxH C H4) (ctxOK_H hok H4) (codesA_H hc.a1c H4) s6 coreWalkFuel dep 0 nb
            CV.coreWalkFuel_lt (by omega) (by decide)) (fun nb2 s7 => ?_)
        refine specR_congr (m' := internForallEE ty nb2 >>= fun r => pure (k, r, ns)) (by simp) ?_
        refine specR_internForallEI ra (ctxOK_H hok H4) (codesR_H hc.cR H4).internForallE npR2 (vv npA) (vv npNb2)
          ty nb2 (by decide) (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]) (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]) (fun r2 s8 => ?_)
        exact np_ret C hok H4 H (((hp1'.trans hp2').trans hp3').trans hp4') (vv npK) k npR2 r2 ns
          (fun _ => (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv])) (fun _ => (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]))
      · exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => specR_hangI)
    · rw [ite_eq_right (show ¬ (w.tag == ETag.forallE) = true by simpa [ETag.forallE] using htg)]
      unfold npApp
      refine specR_callNIH (C := ctxH C H2) npG ExG.fGaa [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv npW]
        (ExG.gaaBody C) [BitVec.ofNat 64 coreWalkFuel, Enc.idxW w] (by decide) rfl (by decide) hc.gaa
        ⟨rfl, (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]), trivial⟩
        (PostA (ctxH C H2)) (fun a w _ H3 => ∃ o3, w = cellA C o3 ∧ BlkAt H3 o3 (a.map Enc.idxW))
        (fun a w s' st ⟨H3, o3, hp, hw, hb, hsr⟩ => ⟨H3, hp, ⟨o3, hw, hb⟩, hsr⟩)
        (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu [pFu, pH] _ rfl hlk)
          (ExG.gaa_spec (ctxH C H2) (ctxOK_H hok H2) hc.gaa coreWalkFuel CV.coreWalkFuel_lt H2 w s2))
        (fun args wg s3 H3 hp3 ⟨oa, hwg, hba⟩ => ?_)
      subst hwg
      have hp3' : H2 <+: H3 := hp3
      have hp3all : C.H <+: H3 := ((hp.trans hp1').trans hp2').trans hp3'
      have hpH3 : H <+: H3 := (hp1'.trans hp2').trans hp3'
      refine specR_atEntry fun t3 ht3 => ?_
      have hargl := Big.blk_small0 (ctxOK_H hok H3) ht3.sr hba
      simp only [List.length_map] at hargl
      refine specR_callNIM npHd fGetAppFn [pFu, pH] [.const (BitVec.ofNat 64 coreWalkFuel), vv npW]
        getAppFnBody [BitVec.ofNat 64 coreWalkFuel, Enc.idxW w] (by decide) rfl (by decide) hc.gf
        ⟨rfl, (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]), trivial⟩
        (fun a w' s' st => getAppFn coreWalkFuel w s3 = .ok (a, s') ∧ Post (ctxH C H3) s3 a w' s' st)
        (fun a w s' st ⟨_, _, hs, hsr⟩ => hs ▸ hsr)
        (fun u hu _ hlk => specR_run (fun t ht => by
          subst ht
          exact getAppFn_spec (ctxH C H3) hc.gf coreWalkFuel w s3 CV.coreWalkFuel_lt t
            ⟨hu, hlk 0 (by decide), hlk 1 (by decide)⟩))
        (fun hd wh s' st ⟨_, hwh, hs, _⟩ => ?_)
      subst hwh
      have hs' : s3 = s' := hs.symm
      subst hs'
      refine specR_assignI lFl (vv lFle) C.FLe (by decide) (by simp +decide [Env.get_cons, Env.get, npParams, ctxEnv] <;> rfl) ?_
      refine specR_assignI lDh (vv npHd) (Enc.idxW hd) (by decide) (by simp +decide [sev, Env.get_cons]) ?_
      refine ConPanqueque.T.Big.specR_viewP hd (by simp) (by simp +decide [Env.get_cons, Env.get, npParams, ctxEnv] <;> rfl)
        (by simp +decide [Env.get_cons, Env.get, npParams, ctxEnv] <;> rfl) (by decide) (fun v P hv htn hlen => ?_)
      refine specR_runBind (show ConRon.Arena.view hd s3 = .ok (v, s3) by rw [view_run, hv]) ?_
      by_cases hv1 : v.tagN = 1
      swap
      · have htb : v.tagN < 16 := by cases v <;> simp [ENodeView.tagN]
        have hw1 : BitVec.ofNat 64 v.tagN ≠ 1#64 := by
          intro e; have := congrArg BitVec.toNat e; simp at this; omega
        exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hw1)
          (fun h => absurd rfl h) (fun _ => specR_hangI)
      obtain ⟨i, ty, rfl⟩ : ∃ i ty, v = .fvar i ty := by cases v <;> simp [ENodeView.tagN] at hv1 ⊢
      refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, ENodeView.tagN, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
        (fun _ => ?_) (fun h => absurd h (by decide))
      simp only
      have hlen1 : (encEView (.fvar i ty)).length = 1 + (Enc.limbs i).length := by simp [encEView, Enc.encFVar]; omega
      by_cases i0 : i = 0
      · have hlim : (Enc.limbs i).length = 0 := by subst i0; simp [Enc.limbs]
        have hib : i < 2 ^ 64 := by omega
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hlen1, hlim, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_assignI npI (.const 0) (BitVec.ofNat 64 i) (by decide) (by rw [i0]; rfl) ?_
        unfold npHole
        have hiP := ConPanqueque.T.Decl.nd_lt_iff i nP hib (by omega)
        by_cases hlt : i < nP
        · rw [holeAt_none ctx ms nP i hN hP (by omega)]
          exact specR_ifI _ 1 (by simp only [sev, sev_vv]; simp +decide [Env.get_cons, Env.get, npParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hiP.mpr hlt])
            (fun _ => specR_hangI) (fun h => absurd h (by decide))
        refine specR_ifI _ 0 (by simp only [sev, sev_vv]; simp +decide [Env.get_cons, Env.get, npParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hiP.not.mpr hlt])
          (fun h => absurd rfl h) (fun _ => ?_)
        refine specR_assignI npT _ (BitVec.ofNat 64 (i - nP)) (by decide)
          (by simp only [sev, sev_vv]; simp +decide [Env.get_cons, Env.get, npParams, ctxEnv]
              apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega) ?_
        have hMH : PtrsRep C H3 om (MemberRep C H3) ms := ptrsRep_mono hp3all (fun _ _ => memberRep_mono hp3all) hM
        refine UD.specR_heapLoadI' (C := ctxH C H3) npL (vv npMs) om _ hMH.1 (by decide)
          (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]; rfl) ?_
        have htw := ConPanqueque.T.Decl.nd_lt_iff (i - nP) ms.length (by omega) (by omega)
        by_cases htl : i - nP < ms.length
        · obtain ⟨hh, hhe, hhn⟩ := holeAt_some ctx ms nP i hN hP hI (by omega) htl
          rw [hhe]
          refine specR_ifI _ 1 (by simp only [sev, sev_vv]; simp +decide [Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, htw.mpr htl])
            (fun _ => ?_) (fun h => absurd h (by decide))
          obtain ⟨ot, hot1, hot2⟩ := hMH.2 (i - nP) htl
          refine UD.specR_heapLoadI' (C := ctxH C H3) npP _ (om + 1 + (i - nP)) _ hot1 (by decide)
            (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]; show _ = cellA C (om + 1 + (i - nP))
                rw [← cellA_shl C (om + 1) (i - nP) (by omega), ← cellA_add8]; rfl) ?_
          refine UD.specR_heapLoadI' (C := ctxH C H3) npX _ (ot + 2) _ hot2.2.2.1 (by decide)
            (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C ot 2) ?_
          simp only [bind_assoc]
          refine specR_callNIH (C := ctxH C H3) npO fAnyNoc ayParams [vv npG, .const 0, vv npMs, vv npNP, vv npHi] ayBody
            [cellA C oa, BitVec.ofNat 64 0, cellA C om, BitVec.ofNat 64 nP, BitVec.ofNat 64 (nP + ms.length)] (by decide) rfl
            (by decide) hc.nt.any
            ⟨by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv], rfl,
              by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv], (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]), trivial⟩
            (PostB (ctxH C H3)) (fun a w _ _ => w = boolW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
            (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ayParams _ rfl hlk)
              (ay_spec C hok hc.nt ms om hM hml nP (nP + ms.length) (by omega) (by omega) args oa hargl _ 0 H3 s3 rfl
                (by omega) hp3all hba))
            (fun ba wa s9 H9 hp9 hwa => ?_)
          subst hwa
          have hp9' : H3 <+: H9 := hp9
          try rw [List.drop_zero]
          cases ba
          · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine UD.specR_heapLoadI' (C := ctxH C H9) npN (vv npG) oa _ (get_prefix hba.1 hp9') (by decide)
              (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]; rfl) ?_
            have hxw := ConPanqueque.T.Decl.nd_lt_iff 0 1 (by omega) (by omega)
            by_cases hln : args.length = ms[i - nP].nIdx
            · have hlw : BitVec.ofNat 64 (args.map Enc.idxW).length = BitVec.ofNat 64 ms[i - nP].nIdx := by simp [hln]
              refine specR_ifI _ 1 (by simp only [sev, sev_vv]; simp +decide [Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hln])
                (fun _ => ?_) (fun h => absurd h (by decide))
              have hbq : (args.length == hh.nIdx) = true := by simp [hhn, hln]
              have hih : i < nP + ms.length := by omega
              simp only [hbq, ↓reduceIte, hih]
              have hti : i - ctx.nP = i - nP := by rw [hP]
              try rw [hti]
              by_cases hk0 : kb = 0
              · subst hk0
                simp only [beq_self_eq_true, ↓reduceIte]
                refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
                  (fun _ => ?_) (fun h => absurd h (by decide))
                refine specR_assignI npK _ (BitVec.ofNat 64 (4 * (i - nP) + 1)) (by decide)
                  (by simp +decide [sev, Env.get_cons]; exact shl2_eq (i - nP) (by omega) 1 (by decide)) ?_
                exact np_ret C hok H9 H (hpH3.trans hp9') (vv npK) (.recursive (i - nP)) npW w ns
                  (fun _ => by simp +decide [sev, Env.get_cons, kindW]) (fun _ => (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]))
              · have hkw : BitVec.ofNat 64 kb ≠ 0#64 := ofNat_ne_zero kb hk0 (by omega)
                refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hkw)
                  (fun h => absurd rfl h) (fun _ => ?_)
                simp only [show (kb == 0) = false by simpa using hk0, Bool.false_eq_true, ↓reduceIte]
                refine specR_assignI npK _ (BitVec.ofNat 64 (4 * (i - nP) + 2)) (by decide)
                  (by simp +decide [sev, Env.get_cons]; exact shl2_eq (i - nP) (by omega) 2 (by decide)) ?_
                exact np_ret C hok H9 H (hpH3.trans hp9') (vv npK) (.reflexive (i - nP)) npW w ns
                  (fun _ => by simp +decide [sev, Env.get_cons, kindW]) (fun _ => (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]))
            · have hlw : BitVec.ofNat 64 args.length ≠ BitVec.ofNat 64 ms[i - nP].nIdx := by
                intro e; apply hln
                have h1 := congrArg BitVec.toNat e; have h2 := hnI (i - nP) htl; simp at h1; omega
              exact specR_ifI _ 0 (by simp only [sev, sev_vv]; simp +decide [Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
                (fun h => absurd rfl h) (fun _ => specR_hangI)
          · refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
            exact specR_hangI
        · rw [holeAt_none ctx ms nP i hN hP (by omega)]
          exact specR_ifI _ 0 (by simp only [sev, sev_vv]; simp +decide [Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, htw.not.mpr htl])
            (fun h => absurd rfl h) (fun _ => specR_hangI)
      by_cases ib : i < 2 ^ 64
      · have hib : i < 2 ^ 64 := ib
        have hl : Enc.limbs i = [BitVec.ofNat 64 i] := by rw [limbs_small i ib]; simp [i0]
        refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hlen1, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun hw => absurd rfl hw) (fun _ => ?_)
        refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, hlen1, hl, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
          (fun _ => ?_) (fun hw => absurd hw (by decide))
        refine specR_loadI' npI _ (P + 8) (P + BitVec.ofNat 64 8) (BitVec.ofNat 64 i) (by decide)
          (by simp +decide [sev, Env.get_cons]) rfl
          (by have := wordsAt_mem1 P (Enc.idxW ty) (BitVec.ofNat 64 i) [] (M := [])
              simpa [encEView, Enc.encFVar, hl] using this) ?_
        unfold npHole
        have hiP := ConPanqueque.T.Decl.nd_lt_iff i nP hib (by omega)
        by_cases hlt : i < nP
        · rw [holeAt_none ctx ms nP i hN hP (by omega)]
          exact specR_ifI _ 1 (by simp only [sev, sev_vv]; simp +decide [Env.get_cons, Env.get, npParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hiP.mpr hlt])
            (fun _ => specR_hangI) (fun h => absurd h (by decide))
        refine specR_ifI _ 0 (by simp only [sev, sev_vv]; simp +decide [Env.get_cons, Env.get, npParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hiP.not.mpr hlt])
          (fun h => absurd rfl h) (fun _ => ?_)
        refine specR_assignI npT _ (BitVec.ofNat 64 (i - nP)) (by decide)
          (by simp only [sev, sev_vv]; simp +decide [Env.get_cons, Env.get, npParams, ctxEnv]
              apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_sub]; omega) ?_
        have hMH : PtrsRep C H3 om (MemberRep C H3) ms := ptrsRep_mono hp3all (fun _ _ => memberRep_mono hp3all) hM
        refine UD.specR_heapLoadI' (C := ctxH C H3) npL (vv npMs) om _ hMH.1 (by decide)
          (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]; rfl) ?_
        have htw := ConPanqueque.T.Decl.nd_lt_iff (i - nP) ms.length (by omega) (by omega)
        by_cases htl : i - nP < ms.length
        · obtain ⟨hh, hhe, hhn⟩ := holeAt_some ctx ms nP i hN hP hI (by omega) htl
          rw [hhe]
          refine specR_ifI _ 1 (by simp only [sev, sev_vv]; simp +decide [Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, htw.mpr htl])
            (fun _ => ?_) (fun h => absurd h (by decide))
          obtain ⟨ot, hot1, hot2⟩ := hMH.2 (i - nP) htl
          refine UD.specR_heapLoadI' (C := ctxH C H3) npP _ (om + 1 + (i - nP)) _ hot1 (by decide)
            (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]; show _ = cellA C (om + 1 + (i - nP))
                rw [← cellA_shl C (om + 1) (i - nP) (by omega), ← cellA_add8]; rfl) ?_
          refine UD.specR_heapLoadI' (C := ctxH C H3) npX _ (ot + 2) _ hot2.2.2.1 (by decide)
            (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C ot 2) ?_
          simp only [bind_assoc]
          refine specR_callNIH (C := ctxH C H3) npO fAnyNoc ayParams [vv npG, .const 0, vv npMs, vv npNP, vv npHi] ayBody
            [cellA C oa, BitVec.ofNat 64 0, cellA C om, BitVec.ofNat 64 nP, BitVec.ofNat 64 (nP + ms.length)] (by decide) rfl
            (by decide) hc.nt.any
            ⟨by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv], rfl,
              by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv], (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]), trivial⟩
            (PostB (ctxH C H3)) (fun a w _ _ => w = boolW a) (fun a w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
            (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ayParams _ rfl hlk)
              (ay_spec C hok hc.nt ms om hM hml nP (nP + ms.length) (by omega) (by omega) args oa hargl _ 0 H3 s3 rfl
                (by omega) hp3all hba))
            (fun ba wa s9 H9 hp9 hwa => ?_)
          subst hwa
          have hp9' : H3 <+: H9 := hp9
          try rw [List.drop_zero]
          cases ba
          · refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
            simp only [Bool.false_eq_true, ↓reduceIte]
            refine UD.specR_heapLoadI' (C := ctxH C H9) npN (vv npG) oa _ (get_prefix hba.1 hp9') (by decide)
              (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]; rfl) ?_
            have hxw := ConPanqueque.T.Decl.nd_lt_iff 0 1 (by omega) (by omega)
            by_cases hln : args.length = ms[i - nP].nIdx
            · have hlw : BitVec.ofNat 64 (args.map Enc.idxW).length = BitVec.ofNat 64 ms[i - nP].nIdx := by simp [hln]
              refine specR_ifI _ 1 (by simp only [sev, sev_vv]; simp +decide [Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hln])
                (fun _ => ?_) (fun h => absurd h (by decide))
              have hbq : (args.length == hh.nIdx) = true := by simp [hhn, hln]
              have hih : i < nP + ms.length := by omega
              simp only [hbq, ↓reduceIte, hih]
              have hti : i - ctx.nP = i - nP := by rw [hP]
              try rw [hti]
              by_cases hk0 : kb = 0
              · subst hk0
                simp only [beq_self_eq_true, ↓reduceIte]
                refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
                  (fun _ => ?_) (fun h => absurd h (by decide))
                refine specR_assignI npK _ (BitVec.ofNat 64 (4 * (i - nP) + 1)) (by decide)
                  (by simp +decide [sev, Env.get_cons]; exact shl2_eq (i - nP) (by omega) 1 (by decide)) ?_
                exact np_ret C hok H9 H (hpH3.trans hp9') (vv npK) (.recursive (i - nP)) npW w ns
                  (fun _ => by simp +decide [sev, Env.get_cons, kindW]) (fun _ => (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]))
              · have hkw : BitVec.ofNat 64 kb ≠ 0#64 := ofNat_ne_zero kb hk0 (by omega)
                refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hkw)
                  (fun h => absurd rfl h) (fun _ => ?_)
                simp only [show (kb == 0) = false by simpa using hk0, Bool.false_eq_true, ↓reduceIte]
                refine specR_assignI npK _ (BitVec.ofNat 64 (4 * (i - nP) + 2)) (by decide)
                  (by simp +decide [sev, Env.get_cons]; exact shl2_eq (i - nP) (by omega) 2 (by decide)) ?_
                exact np_ret C hok H9 H (hpH3.trans hp9') (vv npK) (.reflexive (i - nP)) npW w ns
                  (fun _ => by simp +decide [sev, Env.get_cons, kindW]) (fun _ => (by simp +decide [sev, Env.get_cons, Env.get, npParams, ctxEnv]))
            · have hlw : BitVec.ofNat 64 args.length ≠ BitVec.ofNat 64 ms[i - nP].nIdx := by
                intro e; apply hln
                have h1 := congrArg BitVec.toNat e; have h2 := hnI (i - nP) htl; simp at h1; omega
              exact specR_ifI _ 0 (by simp only [sev, sev_vv]; simp +decide [Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw])
                (fun h => absurd rfl h) (fun _ => specR_hangI)
          · refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
            exact specR_hangI
        · rw [holeAt_none ctx ms nP i hN hP (by omega)]
          exact specR_ifI _ 0 (by simp only [sev, sev_vv]; simp +decide [Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL, htw.not.mpr htl])
            (fun h => absurd rfl h) (fun _ => specR_hangI)
      have hge : 2 ≤ (Enc.limbs i).length := by
        have := (Big.limbs_length_lt_iff i 1).not.mpr (by simp [Big.B]; omega); omega
      have hsh' : 1 + (Enc.limbs i).length < 2 ^ 61 := by rw [← hlen1]; exact hlen
      have hn1 : BitVec.ofNat 64 (1 + (Enc.limbs i).length) ≠ 1#64 := by
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      have hn2 : BitVec.ofNat 64 (1 + (Enc.limbs i).length) ≠ 2#64 := by
        intro e; have := congrArg BitVec.toNat e; simp at this; omega
      refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hlen1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hn1)
        (fun hw => absurd rfl hw) (fun _ => ?_)
      exact specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, hlen1, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hn2)
        (fun hw => absurd rfl hw) (fun _ => specR_hangI)

end

end ConPanqueque.T.Ind
