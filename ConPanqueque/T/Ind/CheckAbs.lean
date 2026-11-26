import ConPanqueque.T.Ind.NestUniform

/-!
# `checkAbsCtorSortsAll`: every walked constructor's fields have sorts within the block's

Per constructor and its walked telescope: the telescope names only the block's level parameters, it binds the
fields (opened above `hi`), and `checkStructFieldSortsI` accepts them.  Failures hang.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def casCs := ofString "cas_cs"
def casOs := ofString "cas_os"
def casJ := ofString "cas_j"
def casLp := ofString "cas_lp"
def casLn := ofString "cas_ln"
def casHi := ofString "cas_hi"
def casSr := ofString "cas_sr"
def casIp := ofString "cas_ip"
def casL := ofString "cas_l"
def casLo := ofString "cas_lo"
def casNF := ofString "cas_nf"
def casOp := ofString "cas_op"
def casTy := ofString "cas_ty"
def casA := ofString "cas_a"
def casX := ofString "cas_x"
def casFv := ofString "cas_fv"
def casE0 := ofString "cas_e0"
def casU := ofString "cas_u"
def casR := ofString "cas_r"
def fCas := ofString "checkAbsCtorSorts"

def casParams : List MlS := [casCs, casOs, casJ, casLp, casLn, casHi, casSr, casIp]
def casLocals : List MlS := [casL, casLo, casNF, casOp, casTy, casA, casX, casFv, casE0, casU, casR]

def casBody (C : Ctx) : ProgHOL 64 := prologue casLocals
  (.seq (.assign .local casL (.load .one (vv casCs)))
  (.seq (.assign .local casLo (.load .one (vv casOs)))
  (.ite (.cmp .lower (vv casJ) (vv casL))
    (.ite (.cmp .lower (vv casJ) (vv casLo))
      (.seq (.assign .local casNF (.load .one (.op .add [.op .add [vv casCs, .const 16], .shift .lsl (vv casJ) (.const 4)])))
      (.seq (.assign .local casOp (.load .one (.op .add [.op .add [vv casOs, .const 8], .shift .lsl (vv casJ) (.const 3)])))
      (.seq (.assign .local casTy (.load .one (.op .add [vv casOp, .const 8])))
      (.seq (.call (some (some (.local, casA), none)) fAt [vv casTy, vv casLp, vv casLn])
      (.ite (.cmp .equal (vv casA) (.const 0)) hang
      (.seq (.call (some (some (.local, casX), none)) fOpenFvars [vv casNF, vv casTy, vv casHi])
      (.ite (.cmp .equal (vv casX) (.const 0)) hang
      (.seq (.assign .local casFv (.load .one (vv casX)))
      (alloc1 C casE0 (.const 0)
      (.seq (.call (some (some (.local, casU), none)) fFieldSorts
          [vv casFv, vv casE0, .const 0, vv casSr, vv casHi, vv casIp, .const 0, vv casNF])
      (.seq (.call (some (some (.local, casR), none)) fCas
          [vv casCs, vv casOs, .op .add [vv casJ, .const 1], vv casLp, vv casLn, vv casHi, vv casSr, vv casIp])
        (.return (.const 0)))))))))))))
      (.return (.const 0)))
    (.return (.const 0)))))

def caaT := ofString "caa_t"
def caaMs := ofString "caa_ms"
def caaOuts := ofString "caa_outs"
def caaLp := ofString "caa_lp"
def caaLn := ofString "caa_ln"
def caaHi := ofString "caa_hi"
def caaSr := ofString "caa_sr"
def caaIp := ofString "caa_ip"
def caaL := ofString "caa_l"
def caaLo := ofString "caa_lo"
def caaP := ofString "caa_p"
def caaCs := ofString "caa_cs"
def caaOs := ofString "caa_os"
def caaU := ofString "caa_u"
def caaR := ofString "caa_r"
def fCaa := ofString "checkAbsCtorSortsAll"

def caaParams : List MlS := [caaT, caaMs, caaOuts, caaLp, caaLn, caaHi, caaSr, caaIp]
def caaLocals : List MlS := [caaL, caaLo, caaP, caaCs, caaOs, caaU, caaR]

def caaBody : ProgHOL 64 := prologue caaLocals
  (.seq (.assign .local caaL (.load .one (vv caaMs)))
  (.seq (.assign .local caaLo (.load .one (vv caaOuts)))
  (.ite (.cmp .lower (vv caaT) (vv caaL))
    (.ite (.cmp .lower (vv caaT) (vv caaLo))
      (.seq (.assign .local caaP (.load .one (.op .add [.op .add [vv caaMs, .const 8], .shift .lsl (vv caaT) (.const 3)])))
      (.seq (.assign .local caaCs (.load .one (.op .add [vv caaP, .const 24])))
      (.seq (.assign .local caaOs (.load .one (.op .add [.op .add [vv caaOuts, .const 8], .shift .lsl (vv caaT) (.const 3)])))
      (.seq (.call (some (some (.local, caaU), none)) fCas
          [vv caaCs, vv caaOs, .const 0, vv caaLp, vv caaLn, vv caaHi, vv caaSr, vv caaIp])
      (.seq (.call (some (some (.local, caaR), none)) fCaa
          [.op .add [vv caaT, .const 1], vv caaMs, vv caaOuts, vv caaLp, vv caaLn, vv caaHi, vv caaSr, vv caaIp])
        (.return (.const 0)))))))
      (.return (.const 0)))
    (.return (.const 0)))))

structure CASCodes (C : Ctx) : Prop where
  atc : C.code.lookup fAt = some (atParams.map (fun p => (p, ShapeHOL.one)), atBody, .one)
  al : AlCodes C
  op : OpCodes C
  ofc : C.code.lookup fOpenFvars = some (ofParams.map (fun p => (p, ShapeHOL.one)), ofBody C, .one)
  fs : FSCodes C
  cas : C.code.lookup fCas = some (casParams.map (fun p => (p, ShapeHOL.one)), casBody C, .one)
  caa : C.code.lookup fCaa = some (caaParams.map (fun p => (p, ShapeHOL.one)), caaBody, .one)

section
variable {σ : Type}

theorem cas_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ casLocals → (ctxEnv C ++ casParams.zip vals).get x = none :=
  Knot.params_none C casLocals casParams vals (by decide) (by decide)

theorem caa_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ caaLocals → (ctxEnv C ++ caaParams.zip vals).get x = none :=
  Knot.params_none C caaLocals caaParams vals (by decide) (by decide)

set_option maxHeartbeats 16000000 in
/-- **`checkAbsCtorSorts`** from constructor `j` on. -/
theorem cas_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hk : KCodes C Comp.kBodies) (hac : Comp.AllCodes mode C) (hc : CASCodes C)
    (heqS : ∀ (H : List (BitVec 64)) (u v : LIdx) (s : AState) (lu lv : ConLeche.Level),
      denoteL s.store.ls u = some lu → denoteL s.store.ls v = some lv → CachesOK s →
      SpecR (σ := σ) (Pre (ctxH C H) s [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s (lvlEq? u v)
        (fun o w s' st => LLeq.PostOB (ctxH C H) o w s' st))
    (ctx : NestCtx) (isProp : Bool) (lsr : ConLeche.Level) (hSd : denoteL C.St.ls ctx.sort = some lsr)
    (hi : Nat) (hhi : ctx.hiAt 0 = hi) (hhi' : hi < 2 ^ 57)
    (olp : Nat) (ks : List ConLeche.Name) (hlpb : BlkAt C.H olp (ctx.lps.map Enc.idxW)) (hkl : ks.length = ctx.lps.length)
    (hks : ∀ j (hj : j < ctx.lps.length), denoteN C.St.ns ctx.lps[j] = some (ks[j]'(by rw [hkl]; exact hj)))
    (hlps : ctx.lps.length < 2 ^ 62)
    (cs : List (IConstantVal × Nat)) (ol : Nat) (hcs : CtorsRep C C.H ol cs) (hcsl : cs.length < 2 ^ 58)
    (hnf : ∀ c ∈ cs, c.2 < 2 ^ 56) (os : List (List NestFieldKind × EIdx)) (oos : Nat)
    (hos : PRep C C.H oos (OutRep C) os) (hosl : os.length < 2 ^ 58) :
    ∀ f j (H : List (BitVec 64)) (s : AState), cs.length - j = f → j ≤ cs.length → C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (casParams.zip [cellA C ol, cellA C oos, BitVec.ofNat 64 j, cellA C olp,
        BitVec.ofNat 64 ctx.lps.length, BitVec.ofNat 64 hi, Enc.idxW ctx.sort, boolW isProp])) (casBody C) s
        (checkAbsCtorSorts mode C.fe ctx isProp (cs.drop j) (os.drop j)) (Decl.PostU (ctxH C H)) := by
  obtain ⟨oss, hosl', hosb, hosr⟩ := hos
  intro f
  induction f with
  | zero =>
    intro j H s hf hj hp
    have hjl : j = cs.length := by omega
    subst hjl
    refine specR_prologue (Decl.postU_locals _) (cas_none _ _) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) casL (vv casCs) ol _ (get_prefix hcs.1 hp) (by decide)
      (by simp +decide [sev, Env.get, casParams, ctxEnv]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) casLo (vv casOs) oos _ (get_prefix hosb.1 hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, casParams, ctxEnv]; rfl) ?_
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, casParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length]
    unfold checkAbsCtorSorts
    try simp only
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro j H s hf hj hp
    have hjl : j < cs.length := by omega
    refine specR_prologue (Decl.postU_locals _) (cas_none _ _) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) casL (vv casCs) ol _ (get_prefix hcs.1 hp) (by decide)
      (by simp +decide [sev, Env.get, casParams, ctxEnv]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) casLo (vv casOs) oos _ (get_prefix hosb.1 hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, casParams, ctxEnv]; rfl) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff j cs.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, casParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hjl]) (fun _ => ?_) (fun h => absurd h (by decide))
    have hlo := ConPanqueque.T.Decl.nd_lt_iff j (oss.map (cellA C)).length (by omega) (by simp; omega)
    by_cases hjo : j < os.length
    swap
    · rw [List.drop_eq_nil_of_le (show os.length ≤ j by omega), List.drop_eq_getElem_cons hjl]
      unfold checkAbsCtorSorts
      try simp only
      refine specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, casParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hosl']; omega) (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_returnI _ 0 rfl (fun t ht => ⟨H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, casParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hosl']; omega) (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨oc, hoc, hcvr, hnfe⟩ := hcs.2 j hjl
    have hjos : j < oss.length := by omega
    have hop := hosb.2 j (by simpa using hjos)
    rw [List.getElem_map] at hop
    obtain ⟨⟨ok, hok1, hok2⟩, hty⟩ := hosr j hjo hjos
    have hnfj := hnf cs[j] (List.getElem_mem hjl)
    rw [List.drop_eq_getElem_cons hjl, List.drop_eq_getElem_cons hjo]
    unfold checkAbsCtorSorts
    simp only
    refine UD.specR_heapLoadI' (C := ctxH C H) casNF _ (ol + 2 + 2 * j) _ (get_prefix hnfe.1 hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, casParams, ctxEnv]; exact cellA_ctor_nf C ol j (by omega)) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) casOp _ (oos + 1 + j) _ (get_prefix hop hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, casParams, ctxEnv]; show _ = cellA C (oos + 1 + j)
          rw [← cellA_shl C (oos + 1) j (by omega), ← cellA_add8]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) casTy _ (oss[j] + 1) _ (get_prefix hty hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C oss[j]) ?_
    refine specR_atEntry fun t0 ht0 => ?_
    have hL : LpsAt (ctxH C H) s olp ctx.lps ks :=
      ⟨blkAt_mono hlpb hp, hkl, fun j hj => denoteN_ext (hks j hj) ht0.sr.floor, hlps⟩
    refine specR_callNIH (C := ctxH C H) casA fAt atParams [vv casTy, vv casLp, vv casLn] atBody
      [Enc.idxW os[j].2, cellA C olp, BitVec.ofNat 64 ctx.lps.length] (by decide) rfl (by decide) hc.atc
      ⟨by simp [sev, Env.get_cons], (by simp +decide [sev, Env.get_cons, Env.get, casParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, casParams, ctxEnv]), trivial⟩
      (PostB (ctxH C H)) (fun b w _ _ => w = boolW b) (fun b w s' st ⟨H', hp', hw, hsr⟩ => ⟨H', hp', hw, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu atParams _ rfl hlk)
        (at_spec (ctxH C H) (ctxOK_H hok H) (by ctx_tr hc.al) s os[j].2 hL))
      (fun b w s1 H1 hp1 hw => ?_)
    subst hw
    have hp1' : H <+: H1 := hp1
    cases b
    · exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI)
        (fun h => absurd h (by decide))
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, boolW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind, hhi]
    refine specR_callNIH (C := ctxH C H1) casX fOpenFvars ofParams [vv casNF, vv casTy, vv casHi] (ofBody C)
      [BitVec.ofNat 64 cs[j].2, Enc.idxW os[j].2, BitVec.ofNat 64 hi] (by decide) rfl (by decide) hc.ofc
      ⟨by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], (by simp +decide [sev, Env.get_cons, Env.get, casParams, ctxEnv]), trivial⟩
      (PostOF (ctxH C H1)) (fun o w _ H' => (o = none → w = 0) ∧ ∀ fvs e', o = some (fvs, e') → ∃ ob oa,
        w = cellA C ob ∧ H'[ob]? = some (cellA C oa) ∧ H'[ob + 1]? = some (Enc.idxW e') ∧ BlkAt H' oa (fvs.map Enc.idxW))
      (fun o w s' st ⟨H', hp', hsr, h1, h2⟩ => ⟨H', hp', ⟨h1, h2⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu ofParams _ rfl hlk)
        (of_spec ra C hok hc.op cs[j].2 os[j].2 hi (by omega) (by omega) H1 (hp.trans hp1') s1))
      (fun o w s2 H2 hp2 ⟨hn, hsm⟩ => ?_)
    have hp2' : H1 <+: H2 := hp2
    rcases o with _ | ⟨fvs, e'⟩
    · have e0 := hn rfl
      subst e0
      exact specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => specR_hangI)
        (fun h => absurd h (by decide))
    obtain ⟨ob, oa, rfl, hob, hoe, hfb⟩ := hsm fvs e' rfl
    refine specR_fact (fun t ht' => inv_heapLen ht') (fun hHN => ?_)
    have hol : ob < H2.length := (List.getElem?_eq_some_iff.mp hob).1
    have hHN' : H2.length ≤ C.HN := hHN
    have hne : cellA C ob ≠ 0 := cellA_ne0 C hok ob (by omega)
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hne) (fun h => absurd rfl h) (fun _ => ?_)
    simp only [unwrapOr, pure_bind]
    refine UD.specR_heapLoadI' (C := ctxH C H2) casFv (vv casX) ob _ hob (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
    refine specR_alloc1I (ctxOK_H hok H2) casE0 (.const 0) 0 (by decide) (fun _ => rfl) (fun H3 ws3 hp3 hws3 => ?_)
    have g3 : ((H3 ++ ws3).set H3.length 0)[H3.length]? = some 0 := by simp [List.getElem?_set, hws3]
    have hp3' : H2 <+: _ := (hp3 : H2 <+: H3).trans (img1_prefix H3 ws3 0 hws3)
    have he0 : BlkAt ((H3 ++ ws3).set H3.length 0) H3.length (([] : List EIdx).map Enc.idxW) :=
      ⟨by simpa using g3, fun i hi => by simp at hi⟩
    have hpC3 : C.H <+: ((H3 ++ ws3).set H3.length 0) := ((hp.trans hp1').trans hp2').trans hp3'
    refine specR_callNIH (C := ctxH C _) casU fFieldSorts fsParams
      [vv casFv, vv casE0, .const 0, vv casSr, vv casHi, vv casIp, .const 0, vv casNF] (fsBody C)
      [cellA C oa, cellA C H3.length, BitVec.ofNat 64 0, Enc.idxW ctx.sort, BitVec.ofNat 64 hi, boolW isProp,
        boolW false, BitVec.ofNat 64 cs[j].2] (by decide) rfl (by decide) hc.fs.self
      ⟨by simp +decide [sev, Env.get_cons] <;> rfl, by simp +decide [sev, Env.get_cons] <;> rfl, rfl, (by simp +decide [sev, Env.get_cons, Env.get, casParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, casParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, casParams, ctxEnv]),
        rfl, by simp +decide [sev, Env.get_cons], trivial⟩
      (Decl.PostU (ctxH C _)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu fsParams _ rfl hlk)
        (fs_spec mode ra C hok hs hk hac hc.fs heqS isProp false ctx.sort lsr hSd hi fvs [] 0 (by simp) oa H3.length
          cs[j].2 _ s2 (by omega) hpC3 (blkAt_mono hfb hp3') he0))
      (fun r w s4 H4 hp4 _ => ?_)
    have hp4' : _ <+: H4 := hp4
    refine specR_congr (m' := checkAbsCtorSorts mode C.fe ctx isProp (cs.drop (j + 1)) (os.drop (j + 1)) >>=
      fun r => pure r) (by simp only [bind_pure]) ?_
    refine specR_callNIH (C := ctxH C H4) casR fCas casParams
      [vv casCs, vv casOs, .op .add [vv casJ, .const 1], vv casLp, vv casLn, vv casHi, vv casSr, vv casIp] (casBody C)
      [cellA C ol, cellA C oos, BitVec.ofNat 64 (j + 1), cellA C olp, BitVec.ofNat 64 ctx.lps.length,
        BitVec.ofNat 64 hi, Enc.idxW ctx.sort, boolW isProp] (by decide) rfl (by decide) hc.cas
      ⟨by simp +decide [sev, Env.get_cons, Env.get, casParams, ctxEnv] <;> rfl, by simp +decide [sev, Env.get_cons, Env.get, casParams, ctxEnv] <;> rfl, by simp +decide [sev, Env.get_cons, Env.get, casParams, ctxEnv]; exact e_succ j, by simp +decide [sev, Env.get_cons, Env.get, casParams, ctxEnv] <;> rfl, (by simp +decide [sev, Env.get_cons, Env.get, casParams, ctxEnv]),
        (by simp +decide [sev, Env.get_cons, Env.get, casParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, casParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, casParams, ctxEnv]), trivial⟩
      (Decl.PostU (ctxH C H4)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu casParams _ rfl hlk)
        (ih (j + 1) H4 s4 (by omega) (by omega) (hpC3.trans hp4')))
      (fun r w s5 H5 hp5 _ => ?_)
    exact specR_returnI _ 0 rfl (fun t ht => ⟨H5, ((((hp1'.trans hp2').trans hp3').trans hp4').trans hp5),
      sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

section
variable {σ : Type}

set_option maxHeartbeats 16000000 in
/-- **`checkAbsCtorSortsAll`** from member `t` on. -/
theorem caa_spec (mode : ConLeche.CheckMode) (ra : ConPanqueque.Hash.RuntimeAssumptions) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hk : KCodes C Comp.kBodies) (hac : Comp.AllCodes mode C) (hc : CASCodes C)
    (heqS : ∀ (H : List (BitVec 64)) (u v : LIdx) (s : AState) (lu lv : ConLeche.Level),
      denoteL s.store.ls u = some lu → denoteL s.store.ls v = some lv → CachesOK s →
      SpecR (σ := σ) (Pre (ctxH C H) s [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s (lvlEq? u v)
        (fun o w s' st => LLeq.PostOB (ctxH C H) o w s' st))
    (ctx : NestCtx) (isProp : Bool) (lsr : ConLeche.Level) (hSd : denoteL C.St.ls ctx.sort = some lsr)
    (hi : Nat) (hhi : ctx.hiAt 0 = hi) (hhi' : hi < 2 ^ 57)
    (olp : Nat) (ks : List ConLeche.Name) (hlpb : BlkAt C.H olp (ctx.lps.map Enc.idxW)) (hkl : ks.length = ctx.lps.length)
    (hks : ∀ j (hj : j < ctx.lps.length), denoteN C.St.ns ctx.lps[j] = some (ks[j]'(by rw [hkl]; exact hj)))
    (hlps : ctx.lps.length < 2 ^ 62)
    (ms : List MemberShape) (om : Nat) (hml : ms.length < 2 ^ 56) (hM : PtrsRep C C.H om (MemberRep C C.H) ms)
    (hcs : ∀ m ∈ ms, m.ctors.length < 2 ^ 58 ∧ ∀ c ∈ m.ctors, c.2 < 2 ^ 56)
    (outs : List (List (List NestFieldKind × EIdx))) (oouts : Nat) (houts : PRep C C.H oouts (OutsRep C) outs)
    (houtl : ∀ o ∈ outs, o.length < 2 ^ 58) (hol : outs.length < 2 ^ 58) :
    ∀ f t (H : List (BitVec 64)) (s : AState), ms.length - t = f → t ≤ ms.length → C.H <+: H →
      SpecR (σ := σ) (Pre (ctxH C H) s (caaParams.zip [BitVec.ofNat 64 t, cellA C om, cellA C oouts, cellA C olp,
        BitVec.ofNat 64 ctx.lps.length, BitVec.ofNat 64 hi, Enc.idxW ctx.sort, boolW isProp])) caaBody s
        (checkAbsCtorSortsAll mode C.fe ctx isProp ((ms.drop t).map (·.ctors)) (outs.drop t)) (Decl.PostU (ctxH C H)) := by
  obtain ⟨ous, houl, houb, hour⟩ := houts
  intro f
  induction f with
  | zero =>
    intro t H s hf ht hp
    have htl : t = ms.length := by omega
    subst htl
    refine specR_prologue (Decl.postU_locals _) (caa_none _ _) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) caaL (vv caaMs) om _ (get_prefix hM.1 hp) (by decide)
      (by simp +decide [sev, Env.get, caaParams, ctxEnv]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) caaLo (vv caaOuts) oouts _ (get_prefix houb.1 hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, caaParams, ctxEnv]; rfl) ?_
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, caaParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length, List.map_nil]
    unfold checkAbsCtorSortsAll
    try simp only
    exact specR_returnI _ 0 rfl (fun tt ht => ⟨H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro t H s hf ht hp
    have htl : t < ms.length := by omega
    refine specR_prologue (Decl.postU_locals _) (caa_none _ _) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) caaL (vv caaMs) om _ (get_prefix hM.1 hp) (by decide)
      (by simp +decide [sev, Env.get, caaParams, ctxEnv]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) caaLo (vv caaOuts) oouts _ (get_prefix houb.1 hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, caaParams, ctxEnv]; rfl) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff t ms.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, caaParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr htl]) (fun _ => ?_) (fun h => absurd h (by decide))
    by_cases hto : t < outs.length
    swap
    · rw [List.drop_eq_nil_of_le (show outs.length ≤ t by omega), List.drop_eq_getElem_cons htl, List.map_cons]
      unfold checkAbsCtorSortsAll
      try simp only
      refine specR_ifI _ 0 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, caaParams, ctxEnv,
          Flapjack.Compiler.Encoders.Asm.wordCmpHOL, houl]; omega) (fun h => absurd rfl h) (fun _ => ?_)
      exact specR_returnI _ 0 rfl (fun tt ht => ⟨H, List.prefix_refl _, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, caaParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, houl]; omega) (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨omt, hmt, hrep⟩ := hM.2 t htl
    obtain ⟨-, -, -, ⟨ol, hol', hcsr⟩⟩ := hrep
    have hto' : t < ous.length := by omega
    have hop := houb.2 t (by simpa using hto')
    rw [List.getElem_map] at hop
    have hor := hour t hto hto'
    have hmc := hcs ms[t] (List.getElem_mem htl)
    refine UD.specR_heapLoadI' (C := ctxH C H) caaP _ (om + 1 + t) _ (get_prefix hmt hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, caaParams, ctxEnv]; show _ = cellA C (om + 1 + t)
          rw [← cellA_shl C (om + 1) t (by omega), ← cellA_add8]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) caaCs _ (omt + 3) _ (get_prefix hol' hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C omt 3) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) caaOs _ (oouts + 1 + t) _ (get_prefix hop hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, caaParams, ctxEnv]; show _ = cellA C (oouts + 1 + t)
          rw [← cellA_shl C (oouts + 1) t (by omega), ← cellA_add8]; rfl) ?_
    rw [List.drop_eq_getElem_cons htl, List.drop_eq_getElem_cons hto, List.map_cons]
    unfold checkAbsCtorSortsAll
    try simp only
    rw [show ms[t].ctors = ms[t].ctors.drop 0 from rfl, show outs[t] = outs[t].drop 0 from rfl]
    refine specR_callNIH (C := ctxH C H) caaU fCas casParams
      [vv caaCs, vv caaOs, .const 0, vv caaLp, vv caaLn, vv caaHi, vv caaSr, vv caaIp] (casBody C)
      [cellA C ol, cellA C ous[t], BitVec.ofNat 64 0, cellA C olp, BitVec.ofNat 64 ctx.lps.length, BitVec.ofNat 64 hi,
        Enc.idxW ctx.sort, boolW isProp] (by decide) rfl (by decide) hc.cas
      ⟨by simp +decide [sev, Env.get_cons] <;> rfl, by simp +decide [sev, Env.get_cons] <;> rfl, rfl, by simp +decide [sev, Env.get_cons, Env.get, caaParams, ctxEnv] <;> rfl, (by simp +decide [sev, Env.get_cons, Env.get, caaParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, caaParams, ctxEnv]),
        (by simp +decide [sev, Env.get_cons, Env.get, caaParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, caaParams, ctxEnv]), trivial⟩
      (Decl.PostU (ctxH C H)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu casParams _ rfl hlk)
        (cas_spec mode ra C hok hs hk hac hc heqS ctx isProp lsr hSd hi hhi hhi' olp ks hlpb hkl hks hlps ms[t].ctors ol hcsr
          hmc.1 hmc.2 outs[t] ous[t] hor (houtl outs[t] (List.getElem_mem hto)) _ 0 H s rfl (by omega) hp))
      (fun r w s1 H1 hp1 _ => ?_)
    have hp1' : H <+: H1 := hp1
    refine specR_congr (m' := checkAbsCtorSortsAll mode C.fe ctx isProp ((ms.drop (t + 1)).map (·.ctors))
      (outs.drop (t + 1)) >>= fun r => pure r) (by simp only [bind_pure]) ?_
    refine specR_callNIH (C := ctxH C H1) caaR fCaa caaParams
      [.op .add [vv caaT, .const 1], vv caaMs, vv caaOuts, vv caaLp, vv caaLn, vv caaHi, vv caaSr, vv caaIp] caaBody
      [BitVec.ofNat 64 (t + 1), cellA C om, cellA C oouts, cellA C olp, BitVec.ofNat 64 ctx.lps.length,
        BitVec.ofNat 64 hi, Enc.idxW ctx.sort, boolW isProp] (by decide) rfl (by decide) hc.caa
      ⟨by simp +decide [sev, Env.get_cons, Env.get, caaParams, ctxEnv]; exact e_succ t, by simp +decide [sev, Env.get_cons, Env.get, caaParams, ctxEnv] <;> rfl, by simp +decide [sev, Env.get_cons, Env.get, caaParams, ctxEnv] <;> rfl, by simp +decide [sev, Env.get_cons, Env.get, caaParams, ctxEnv] <;> rfl, (by simp +decide [sev, Env.get_cons, Env.get, caaParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, caaParams, ctxEnv]),
        (by simp +decide [sev, Env.get_cons, Env.get, caaParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, caaParams, ctxEnv]), trivial⟩
      (Decl.PostU (ctxH C H1)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu caaParams _ rfl hlk)
        (ih (t + 1) H1 s1 (by omega) (by omega) (hp.trans hp1')))
      (fun r w s2 H2 hp2 _ => ?_)
    exact specR_returnI _ 0 rfl (fun tt ht => ⟨H2, hp1'.trans hp2, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
