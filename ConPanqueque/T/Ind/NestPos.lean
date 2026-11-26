import ConPanqueque.T.Ind.CloseTele

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

end ConPanqueque.T.Ind
