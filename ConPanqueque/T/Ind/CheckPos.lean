import ConPanqueque.T.Ind.CheckAbs

/-!
# `checkBlockPositivity` (unnested blocks): the walk's context, uniformity, the root frame, the sorts

`blockNestCtx`, then `nestUniform`, `nestRoot` from an empty state, the block's `Prop`-ness, and
`checkAbsCtorSortsAll`.  The parameters and holes are concatenated into one block for `nestCrest`.
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

/-! ## Appending a block's words to another (fresh blocks) -/

def catA := ofString "cat_a"
def catB := ofString "cat_b"
def catJ := ofString "cat_j"
def catL := ofString "cat_l"
def catX := ofString "cat_x"
def catA2 := ofString "cat_a2"
def catR := ofString "cat_r"
def fCat := ofString "appendBlock"

def catParams : List MlS := [catA, catB, catJ]
def catLocals : List MlS := [catL, catX, catA2, catR]

def catBody : ProgHOL 64 := prologue catLocals
  (.seq (.assign .local catL (.load .one (vv catB)))
  (.ite (.cmp .lower (vv catJ) (vv catL))
    (.seq (.assign .local catX (.load .one (.op .add [.op .add [vv catB, .const 8], .shift .lsl (vv catJ) (.const 3)])))
    (.seq (.call (some (some (.local, catA2), none)) ExPre.fAppend [vv catA, vv catX])
    (.seq (.call (some (some (.local, catR), none)) fCat [vv catA2, vv catB, .op .add [vv catJ, .const 1]])
      (.return (vv catR)))))
    (.return (vv catA))))

structure CatCodes (C : Ctx) : Prop where
  app : C.code.lookup ExPre.fAppend = some (ExPre.appParams.map (fun p => (p, ShapeHOL.one)), ExPre.appBody C, .one)
  self : C.code.lookup fCat = some (catParams.map (fun p => (p, ShapeHOL.one)), catBody, .one)

section
variable {σ : Type}

theorem cat_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ catLocals → (ctxEnv C ++ catParams.zip vals).get x = none :=
  Knot.params_none C catLocals catParams vals (by decide) (by decide)

/-- **`xs ++ ys.drop j`** as a fresh block (the state kept). -/
theorem cat_spec (C : Ctx) (hok : CtxOK C) (hc : CatCodes C) (ys : List (BitVec 64)) (ob : Nat)
    (hyl : ys.length < 2 ^ 58) :
    ∀ f j (xs : List (BitVec 64)) (oa : Nat) (H : List (BitVec 64)) (s : AState), ys.length - j = f → j ≤ ys.length →
      BlkAt H oa xs → BlkAt H ob ys →
      SpecR (σ := σ) (Pre (ctxH C H) s (catParams.zip [cellA C oa, cellA C ob, BitVec.ofNat 64 j])) catBody s
        (pure (xs ++ ys.drop j) : AM (List (BitVec 64)))
        (fun r w s' st => ∃ H' o, H <+: H' ∧ s' = s ∧ w = cellA C o ∧ BlkAt H' o r ∧ SR (ctxH C H') s' st) := by
  intro f
  induction f with
  | zero =>
    intro j xs oa H s hf hj ha hb
    have hjl : j = ys.length := by omega
    subst hjl
    refine specR_prologue (fun a w s' st L ⟨H', o, h1, h2, h3, h4, hsr⟩ => ⟨H', o, h1, h2, h3, h4,
      sr_of_eq hsr rfl rfl rfl rfl⟩) (cat_none _ _) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) catL (vv catB) ob _ hb.1 (by decide)
      (by simp +decide [sev, Env.get, catParams, ctxEnv]; rfl) ?_
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, catParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length, List.append_nil]
    exact specR_returnI _ (cellA C oa) (by simp +decide [sev, Env.get_cons, Env.get, catParams, ctxEnv])
      (fun t ht => ⟨H, oa, List.prefix_refl _, rfl, rfl, ha, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro j xs oa H s hf hj ha hb
    have hjl : j < ys.length := by omega
    refine specR_prologue (fun a w s' st L ⟨H', o, h1, h2, h3, h4, hsr⟩ => ⟨H', o, h1, h2, h3, h4,
      sr_of_eq hsr rfl rfl rfl rfl⟩) (cat_none _ _) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) catL (vv catB) ob _ hb.1 (by decide)
      (by simp +decide [sev, Env.get, catParams, ctxEnv]; rfl) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff j ys.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, catParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr hjl]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine UD.specR_heapLoadI' (C := ctxH C H) catX _ (ob + 1 + j) ys[j] (hb.2 j hjl) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, catParams, ctxEnv]; show _ = cellA C (ob + 1 + j)
          rw [← cellA_shl C (ob + 1) j (by omega), ← cellA_add8]; rfl) ?_
    have heq : xs ++ ys.drop j = (xs ++ [ys[j]]) ++ ys.drop (j + 1) := by
      rw [List.drop_eq_getElem_cons hjl]; simp
    rw [heq]
    refine specR_appendI hok hc.app H catA2 (vv catA) (vv catX) xs ys[j] oa ha (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, catParams, ctxEnv]) (by simp [sev, Env.get_cons])
      (fun H2 oa2 hp2 ha2 => ?_)
    refine specR_congr (m' := (pure ((xs ++ [ys[j]]) ++ ys.drop (j + 1)) : AM (List (BitVec 64))) >>= fun r => pure r)
      (by simp only [bind_pure]) ?_
    refine specR_callNIH (C := ctxH C H2) catR fCat catParams [vv catA2, vv catB, .op .add [vv catJ, .const 1]] catBody
      [cellA C oa2, cellA C ob, BitVec.ofNat 64 (j + 1)] (by decide) rfl (by decide) hc.self
      ⟨by simp [sev, Env.get_cons], by simp +decide [sev, Env.get_cons, Env.get, catParams, ctxEnv] <;> rfl,
        by simp +decide [sev, Env.get_cons, Env.get, catParams, ctxEnv]; exact e_succ j, trivial⟩
      (fun r w s' st => ∃ H' o, H2 <+: H' ∧ s' = s ∧ w = cellA C o ∧ BlkAt H' o r ∧ SR (ctxH C H') s' st)
      (fun r w s' H' => s' = s ∧ ∃ o, w = cellA C o ∧ BlkAt H' o r)
      (fun r w s' st ⟨H', o, hp', hs', hw, hb', hsr⟩ => ⟨H', hp', ⟨hs', o, hw, hb'⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu catParams _ rfl hlk)
        (ih (j + 1) (xs ++ [ys[j]]) oa2 H2 s (by omega) (by omega) ha2 (blkAt_mono hb hp2)))
      (fun r w s1 H3 hp3 ⟨hs1, o3, hw3, hb3⟩ => ?_)
    subst hs1; subst hw3
    exact specR_returnI _ (cellA C o3) (by simp [sev, Env.get_cons])
      (fun t ht => ⟨H3, o3, hp2.trans hp3, rfl, rfl, hb3, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

/-! ## The assembly -/

def cbpMs := ofString "cbp_ms"
def cbpNP := ofString "cbp_np"
def cbpSr := ofString "cbp_sr"
def cbpR := ofString "cbp_r"
def cbpPs := ofString "cbp_ps"
def cbpUs := ofString "cbp_us"
def cbpHs := ofString "cbp_hs"
def cbpA0 := ofString "cbp_a0"
def cbpP2 := ofString "cbp_p2"
def cbpDH := ofString "cbp_dh"
def cbpDn := ofString "cbp_dn"
def cbpL := ofString "cbp_l"
def cbpHi := ofString "cbp_hi"
def cbpU := ofString "cbp_u"
def cbpE0 := ofString "cbp_e0"
def cbpE1 := ofString "cbp_e1"
def cbpR2 := ofString "cbp_r2"
def cbpOuts := ofString "cbp_outs"
def cbpNs := ofString "cbp_ns"
def cbpZ := ofString "cbp_z"
def cbpO := ofString "cbp_o"
def cbpIp := ofString "cbp_ip"
def cbpP0 := ofString "cbp_p0"
def cbpQ0 := ofString "cbp_q0"
def cbpLp := ofString "cbp_lp"
def cbpLn := ofString "cbp_ln"
def cbpV := ofString "cbp_v"
def cbpR3 := ofString "cbp_r3"
def fCbp := ofString "checkBlockPositivity"

def cbpParams : List MlS := [cbpMs, cbpNP, cbpSr]
def cbpLocals : List MlS := [cbpR, cbpPs, cbpUs, cbpHs, cbpA0, cbpP2, cbpDH, cbpDn, cbpL, cbpHi, cbpU, cbpE0, cbpE1, cbpR2,
  cbpOuts, cbpNs, cbpZ, cbpO, cbpIp, cbpP0, cbpQ0, cbpLp, cbpLn, cbpV, cbpR3]

/-- The tail: the block's `Prop`-ness, the sorts check, the answer. -/
def cbpTail (C : Ctx) : ProgHOL 64 :=
  .seq (.assign .local cbpZ (.load .one (.const (ecell C (C.PO + pinCount + 1)))))
  (.seq (.call (some (some (.local, cbpO), none)) LLeq.fEqv [vv cbpSr, vv cbpZ])
  (.ite (.cmp .equal (vv cbpO) (.const 2))
    (.seq (.assign .local cbpIp (.const 1)) (cbpSorts C))
    (.seq (.assign .local cbpIp (.const 0)) (cbpSorts C))))
where
  cbpSorts (C : Ctx) : ProgHOL 64 :=
    .seq (.assign .local cbpP0 (.load .one (.op .add [vv cbpMs, .const 8])))
    (.seq (.assign .local cbpQ0 (.load .one (vv cbpP0)))
    (.seq (.assign .local cbpLp (.load .one (.op .add [vv cbpQ0, .const 8])))
    (.seq (.assign .local cbpLn (.load .one (vv cbpLp)))
    (.seq (.call (some (some (.local, cbpV), none)) fCaa
        [.const 0, vv cbpMs, vv cbpOuts, vv cbpLp, vv cbpLn, vv cbpHi, vv cbpSr, vv cbpIp])
      (alloc2 C cbpR3 (vv cbpOuts) (vv cbpNs) (.return (vv cbpR3)))))))

def cbpBody (C : Ctx) : ProgHOL 64 := prologue cbpLocals
  (.seq (.call (some (some (.local, cbpR), none)) fBlockNestCtx [vv cbpMs, vv cbpNP])
  (.seq (.assign .local cbpPs (.load .one (vv cbpR)))
  (.seq (.assign .local cbpUs (.load .one (.op .add [vv cbpR, .const 8])))
  (.seq (.assign .local cbpHs (.load .one (.op .add [vv cbpR, .const 16])))
  (alloc1 C cbpA0 (.const 0)
  (.seq (.call (some (some (.local, cbpP2), none)) fCat [vv cbpA0, vv cbpPs, .const 0])
  (.seq (.call (some (some (.local, cbpDH), none)) fCat [vv cbpP2, vv cbpHs, .const 0])
  (.seq (.assign .local cbpDn (.load .one (vv cbpPs)))
  (.seq (.assign .local cbpL (.load .one (vv cbpMs)))
  (.seq (.assign .local cbpHi (.op .add [vv cbpNP, vv cbpL]))
  (.seq (.call (some (some (.local, cbpU), none)) fNum [.const 0, vv cbpMs, vv cbpNP, vv cbpHi, vv cbpUs])
  (alloc1 C cbpE0 (.const 0) (alloc1 C cbpE1 (.const 0)
  (.seq (.call (some (some (.local, cbpR2), none)) fNrt
      [.const 0, vv cbpE0, vv cbpE1, vv cbpMs, vv cbpNP, vv cbpHi, vv cbpUs, vv cbpDH, vv cbpDn, vv cbpPs])
  (.seq (.assign .local cbpOuts (.load .one (vv cbpR2)))
  (.seq (.assign .local cbpNs (.load .one (.op .add [vv cbpR2, .const 8])))
    (cbpTail C)))))))))))))))))

structure CBPCodes (C : Ctx) : Prop where
  bn : BNCodes C
  cat : CatCodes C
  num : NUMCodes C
  nrt : NRTCodes C
  cas : CASCodes C
  eqv : C.code.lookup LLeq.fEqv = some ([LEq.pLa, LEq.pLb].map (fun p => (p, ShapeHOL.one)), LLeq.eqvBody, .one)
  self : C.code.lookup fCbp = some (cbpParams.map (fun p => (p, ShapeHOL.one)), cbpBody C, .one)

section
variable {σ : Type}

theorem cbp_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ cbpLocals → (ctxEnv C ++ cbpParams.zip vals).get x = none :=
  Knot.params_none C cbpLocals cbpParams vals (by decide) (by decide)

/-- `checkBlockPositivity`'s answer `[outs, ns]`. -/
def PostCBP (C : Ctx) (r : List (List (List NestFieldKind × EIdx)) × NestState) (w : BitVec 64) (s' : AState)
    (st : PState σ) : Prop :=
  ∃ H' o oo on, C.H <+: H' ∧ w = cellA C o ∧ H'[o]? = some (cellA C oo) ∧ PRep C H' oo (OutsRep C) r.1 ∧
    H'[o + 1]? = some (cellA C on) ∧ PRep C H' on (NfRep C) r.2.ctorNfs.toList ∧ SR (ctxH C H') s' st

theorem postCBP_locals (C : Ctx) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostCBP C a w s' st → PostCBP C a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, oo, on, hp, hw, h1, h2, h3, h4, hs⟩ =>
    ⟨H', o, oo, on, hp, hw, h1, h2, h3, h4, sr_of_eq hs rfl rfl rfl rfl⟩

theorem postCBP_lower {C : Ctx} {St : EStore} (hx : Ext C.St St) :
    ∀ a w s' (st : PState σ), PostCBP (ctxSt C St) a w s' st → PostCBP C a w s' st :=
  fun _ _ _ _ ⟨H', o, oo, on, hp, hw, h1, h2, h3, h4, hs⟩ =>
    ⟨H', o, oo, on, hp, hw, h1, h2, h3, h4, sr_lower (C := ctxH C H') hs hx⟩

end

section
variable {σ : Type}

set_option maxHeartbeats 32000000 in
/-- **`checkBlockPositivity`** (unnested blocks). -/
theorem cbp_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hk : KCodes C Comp.kBodies) (hac : Comp.AllCodes mode C) (hc : CBPCodes C)
    (heqS : ∀ (C' : Ctx), C'.code = C.code → CtxOK C' → ∀ (H : List (BitVec 64)) (u v : LIdx) (s : AState)
      (lu lv : ConLeche.Level), denoteL s.store.ls u = some lu → denoteL s.store.ls v = some lv → CachesOK s →
      SpecR (σ := σ) (Pre (ctxH C' H) s [(LEq.pLa, Enc.idxW u), (LEq.pLb, Enc.idxW v)]) LLeq.eqvBody s (lvlEq? u v)
        (fun o w s' st => LLeq.PostOB (ctxH C' H) o w s' st))
    (p : BlockShape) (om : Nat) (hM : PtrsRep C C.H om (MemberRep C C.H) p.members)
    (hml : p.members.length < 2 ^ 55) (hnP : p.nP < 2 ^ 55) (hlp : p.lps.length < 2 ^ 59)
    (hnI : ∀ t (ht : t < p.members.length), p.members[t].nIdx < 2 ^ 63)
    (hcs : ∀ m ∈ p.members, m.ctors.length < 2 ^ 58 ∧ ∀ c ∈ m.ctors, CVDen c.1 C.St ∧ c.2 < 2 ^ 56)
    (ks : List ConLeche.Name) (hkl : ks.length = p.lps.length)
    (hks : ∀ j (hj : j < p.lps.length), denoteN C.St.ns p.lps[j] = some (ks[j]'(by rw [hkl]; exact hj)))
    (lsr : ConLeche.Level) (hSd : denoteL C.St.ls p.resSort = some lsr)
    (s : AState)
    (hrun : ∀ (s1 : AState) (ctx : NestCtx) (holes : List EIdx), blockNestCtx p s = .ok ((ctx, holes), s1) →
      (∃ vs, denoteLs s1.store.lss ctx.lvls = some vs) ∧ ctx.params.length < 2 ^ 56 ∧ holes.length < 2 ^ 56)
    (H : List (BitVec 64)) (hp : C.H <+: H) :
    SpecR (σ := σ) (Pre (ctxH C H) s (cbpParams.zip [cellA C om, BitVec.ofNat 64 p.nP, Enc.idxW p.resSort]))
      (cbpBody C) s (checkBlockPositivity mode C.fe p) (PostCBP (ctxH C H)) := by
  refine specR_prologue (postCBP_locals _) (cbp_none _ _) ?_
  unfold checkBlockPositivity
  have hMH : PtrsRep C H om (MemberRep C H) p.members := ptrsRep_mono hp (fun _ _ => memberRep_mono hp) hM
  refine specR_callNIH (C := ctxH C H) cbpR fBlockNestCtx bnParams [vv cbpMs, vv cbpNP] (bnBody C)
    [cellA C om, BitVec.ofNat 64 p.nP] (by decide) rfl (by decide) hc.bn.self ⟨(by simp +decide [sev, Env.get_cons, Env.get, cbpParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, cbpParams, ctxEnv]), trivial⟩
    (fun a w s' st => blockNestCtx p s = .ok (a, s') ∧ PostBN (ctxH C H) p a w s' st)
    (fun a w s' H' => blockNestCtx p s = .ok (a, s') ∧ a.1.names = p.memberNames ∧ a.1.lps = p.lps ∧
      a.1.nP = p.nP ∧ a.1.nIdxs = p.nIdxs ∧ a.1.sort = p.resSort ∧ ∃ or_ oq oh, w = cellA C or_ ∧
      H'[or_]? = some (cellA C oq) ∧ BlkAt H' oq (a.1.params.map Enc.idxW) ∧ H'[or_ + 1]? = some (Enc.idxW a.1.lvls) ∧
      H'[or_ + 2]? = some (cellA C oh) ∧ BlkAt H' oh (a.2.map Enc.idxW))
    (fun a w s' st ⟨hr, H', hp', hsr, h1, h2, h3, h4, h5, _, h7⟩ => ⟨H', hp', ⟨hr, h1, h2, h3, h4, h5, h7⟩, hsr⟩)
    (fun u hu _ hlk => specR_run (Knot.specR_of_pre u (pre_of_lookups hu bnParams _ rfl hlk)
      (bn_spec ra C hok hc.bn p om H hp hMH (by omega) (by omega) hlp s)))
    (fun r w s1 H1 hp1 ⟨hr, hN, hL, hP, hI, hS, or_, oq, oh, hw, h0, hpb, h1, h2, hhb⟩ => ?_)
  subst hw
  obtain ⟨ctx, holes⟩ := r
  simp only at hN hL hP hI hS h1 hpb hhb hr ⊢
  obtain ⟨⟨vsL, hlv⟩, hpl, hhl⟩ := hrun s1 ctx holes hr
  have hp1' : H <+: H1 := hp1
  refine UD.specR_heapLoadI' (C := ctxH C H1) cbpPs (vv cbpR) or_ _ h0 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H1) cbpUs _ (or_ + 1) _ h1 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C or_) ?_
  refine UD.specR_heapLoadI' (C := ctxH C H1) cbpHs _ (or_ + 2) _ h2 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C or_ 2) ?_
  refine specR_atEntry fun t1 ht1 => ?_
  have hx1 : Ext C.St s1.store := ht1.sr.floor
  -- raise the floor to the walk's context's store
  refine specR_invRaise (R' := PostCBP (ctxSt (ctxH C H) s1.store)) ?_
    (fun a w s' t hx hpost => postCBP_lower (C := ctxH C H) hx a w s' t hpost)
  set C1 := ctxSt (ctxH C H) s1.store with hC1
  have hok1 : CtxOK C1 := ctxOK_St (ctxOK_H hok H) s1.store
  have hcode1 : C1.code = C.code := rfl
  have hp1C : C1.H <+: H1 := hp1'
  refine specR_alloc1I (ctxOK_H hok1 H1) cbpA0 (.const 0) 0 (by decide) (fun _ => rfl) (fun Ha wsa hpa hwsa => ?_)
  have ga : ((Ha ++ wsa).set Ha.length 0)[Ha.length]? = some 0 := by simp [List.getElem?_set, hwsa]
  have hpa' : H1 <+: _ := (hpa : H1 <+: Ha).trans (img1_prefix Ha wsa 0 hwsa)
  have ha0 : BlkAt ((Ha ++ wsa).set Ha.length 0) Ha.length ([] : List (BitVec 64)) :=
    ⟨by simpa using ga, fun i hi => by simp at hi⟩
  refine specR_callPure (C := ctxH C1 _) cbpP2 fCat catParams [vv cbpA0, vv cbpPs, .const 0] catBody
    [cellA C Ha.length, cellA C oq, BitVec.ofNat 64 0] ([] ++ (ctx.params.map Enc.idxW).drop 0) (by decide) rfl
    (by decide) hc.cat.self
    ⟨by simp [sev, Env.get_cons]; rfl, by simp +decide [sev, Env.get_cons] <;> rfl, rfl, trivial⟩
    (fun r w s' st => ∃ H' o, _ <+: H' ∧ s' = s1 ∧ w = cellA C o ∧ BlkAt H' o r ∧ SR (ctxH C1 H') s' st)
    (fun r w s' H' => ∃ o, w = cellA C o ∧ BlkAt H' o r)
    (fun r w s' st ⟨H', o, hp', hs', hw, hb', hsr⟩ => ⟨H', hp', ⟨o, hw, hb'⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu catParams _ rfl hlk)
      (cat_spec C1 hok1 (by ctx_tr hc.cat) (ctx.params.map Enc.idxW) oq (by simp; omega) _ 0 [] Ha.length _ s1 rfl
        (by omega) ha0 (blkAt_mono hpb hpa')))
    (fun w H2 hp2 ⟨o2, hw2, hb2⟩ => ?_)
  subst hw2
  try simp only [List.drop_zero, List.nil_append] at hb2
  have hp2' : _ <+: H2 := hp2
  refine specR_callPure (C := ctxH C1 H2) cbpDH fCat catParams [vv cbpP2, vv cbpHs, .const 0] catBody
    [cellA C o2, cellA C oh, BitVec.ofNat 64 0] (ctx.params.map Enc.idxW ++ (holes.map Enc.idxW).drop 0) (by decide) rfl
    (by decide) hc.cat.self
    ⟨by simp [sev, Env.get_cons], by simp +decide [sev, Env.get_cons] <;> rfl, rfl, trivial⟩
    (fun r w s' st => ∃ H' o, H2 <+: H' ∧ s' = s1 ∧ w = cellA C o ∧ BlkAt H' o r ∧ SR (ctxH C1 H') s' st)
    (fun r w s' H' => ∃ o, w = cellA C o ∧ BlkAt H' o r)
    (fun r w s' st ⟨H', o, hp', hs', hw, hb', hsr⟩ => ⟨H', hp', ⟨o, hw, hb'⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu catParams _ rfl hlk)
      (cat_spec C1 hok1 (by ctx_tr hc.cat) (holes.map Enc.idxW) oh (by simp; omega) _ 0 _ o2 H2 s1 rfl
        (by omega) hb2 (blkAt_mono hhb (hpa'.trans hp2'))))
    (fun w H3 hp3 ⟨o3, hw3, hb3⟩ => ?_)
  subst hw3
  try simp only [List.drop_zero] at hb3
  have hp3' : H2 <+: H3 := hp3
  have hdh : BlkAt H3 o3 ((ctx.params ++ holes).map Enc.idxW) := by simpa using hb3
  have hpH3 : H1 <+: H3 := (hpa'.trans hp2').trans hp3'
  refine UD.specR_heapLoadI' (C := ctxH C1 H3) cbpDn (vv cbpPs) oq _ (get_prefix hpb.1 hpH3) (by decide)
    (by simp +decide [sev, Env.get_cons] <;> rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C1 H3) cbpL (vv cbpMs) om _ (get_prefix hMH.1 (hp1'.trans hpH3)) (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, cbpParams, ctxEnv] <;> rfl) ?_
  refine specR_assignI cbpHi _ (BitVec.ofNat 64 (p.nP + p.members.length)) (by decide)
    (by simp +decide [sev, Env.get_cons, Env.get, cbpParams, ctxEnv]; rw [BitVec.ofNat_add_ofNat]) ?_
  set C2 := ctxH C1 H3 with hC2
  have hok2 : CtxOK C2 := ctxOK_H hok1 H3
  have hM2 : PtrsRep C2 C2.H om (MemberRep C2 C2.H) p.members :=
    ptrsRep_mono (hp1'.trans hpH3) (fun _ _ => memberRep_mono (hp1'.trans hpH3)) hMH
  have hN2 : ctx.names = p.members.map (·.cvT.name) := by rw [hN]; rfl
  have hI2 : ctx.nIdxs = p.members.map (·.nIdx) := by rw [hI]; rfl
  have hcs2 : ∀ m ∈ p.members, m.ctors.length < 2 ^ 58 ∧ ∀ c ∈ m.ctors, CVDen c.1 C2.St ∧ c.2 < 2 ^ 56 :=
    fun m hm => ⟨(hcs m hm).1, fun c hc' => ⟨cvDen_ext ((hcs m hm).2 c hc').1 hx1, ((hcs m hm).2 c hc').2⟩⟩
  have hmc : p.memberCtors = (p.members.drop 0).map (·.ctors) := by simp [BlockShape.memberCtors]
  rw [hmc]
  refine specR_callNIH (C := C2) cbpU fNum numParams [.const 0, vv cbpMs, vv cbpNP, vv cbpHi, vv cbpUs] numBody
    [BitVec.ofNat 64 0, cellA C om, BitVec.ofNat 64 p.nP, BitVec.ofNat 64 (p.nP + p.members.length), Enc.idxW ctx.lvls]
    (by decide) rfl (by decide) hc.num.num
    ⟨rfl, by simp +decide [sev, Env.get_cons, Env.get, cbpParams, ctxEnv] <;> rfl, by simp +decide [sev, Env.get_cons, Env.get, cbpParams, ctxEnv] <;> rfl, by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], trivial⟩
    (Decl.PostU C2) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu numParams _ rfl hlk)
      (num_spec ra C2 hok2 (by ctx_tr hc.num) p.members om (by omega) hM2 p.nP (by omega) ctx hN2 hP vsL hlv
        (fun m hm => ⟨(hcs2 m hm).1, fun c hc' => ((hcs2 m hm).2 c hc').1⟩) _ 0 H3 s1 rfl (by omega)
        (List.prefix_refl _)))
    (fun _ w s4 H4 hp4 _ => ?_)
  have hp4' : H3 <+: H4 := hp4
  refine specR_alloc1I (ctxOK_H hok1 H4) cbpE0 (.const 0) 0 (by decide) (fun _ => rfl) (fun Hb wsb hpb' hwsb => ?_)
  have gb : ((Hb ++ wsb).set Hb.length 0)[Hb.length]? = some 0 := by simp [List.getElem?_set, hwsb]
  have hpb2 : H4 <+: _ := (hpb' : H4 <+: Hb).trans (img1_prefix Hb wsb 0 hwsb)
  refine specR_alloc1I (ctxOK_H hok1 _) cbpE1 (.const 0) 0 (by decide) (fun _ => rfl) (fun Hc wsc hpc hwsc => ?_)
  have gc : ((Hc ++ wsc).set Hc.length 0)[Hc.length]? = some 0 := by simp [List.getElem?_set, hwsc]
  have hpc2 : _ <+: _ := (hpc : _ <+: Hc).trans (img1_prefix Hc wsc 0 hwsc)
  set H5 := (Hc ++ wsc).set Hc.length 0 with hH5
  have hp35 : H3 <+: H5 := (hp4'.trans hpb2).trans hpc2
  have hns0 : PRep C H5 Hb.length (NfRep C) ((({} : NestState).ctorNfs.toList)) :=
    ⟨[], rfl, ⟨by have := get_prefix gb hpc2; simpa using this, fun i hi => by simp at hi⟩, fun i hi => by simp at hi⟩
  have hout0 : PRep C H5 Hc.length (OutsRep C) ([] : List (List (List NestFieldKind × EIdx))) :=
    ⟨[], rfl, ⟨by simpa using gc, fun i hi => by simp at hi⟩, fun i hi => by simp at hi⟩
  refine specR_callNIH (C := ctxH C2 H5) cbpR2 fNrt nrtParams
    [.const 0, vv cbpE0, vv cbpE1, vv cbpMs, vv cbpNP, vv cbpHi, vv cbpUs, vv cbpDH, vv cbpDn, vv cbpPs] (nrtBody C)
    [BitVec.ofNat 64 0, cellA C Hb.length, cellA C Hc.length, cellA C om, BitVec.ofNat 64 p.nP,
      BitVec.ofNat 64 (p.nP + p.members.length), Enc.idxW ctx.lvls, cellA C o3, BitVec.ofNat 64 ctx.params.length,
      cellA C oq] (by decide) rfl (by decide) hc.nrt.self
    ⟨rfl, by simp +decide [sev, Env.get_cons] <;> rfl, by simp +decide [sev, Env.get_cons] <;> rfl, by simp +decide [sev, Env.get_cons, Env.get, cbpParams, ctxEnv] <;> rfl, by simp +decide [sev, Env.get_cons, Env.get, cbpParams, ctxEnv] <;> rfl,
      by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons] <;> rfl,
      by simp +decide [sev, Env.get_cons], by simp +decide [sev, Env.get_cons] <;> rfl, trivial⟩
    (PostNRT (ctxH C2 H5) {}) (fun r w _ H' => ∃ o oo on, w = cellA C o ∧ H'[o]? = some (cellA C oo) ∧
      PRep C H' oo (OutsRep C) r.1 ∧ H'[o + 1]? = some (cellA C on) ∧ PRep C H' on (NfRep C) r.2.ctorNfs.toList)
    (fun r w s' st ⟨H', o, oo, on, hp', hw, h1, h2, h3, h4, _, _, hsr⟩ => ⟨H', hp', ⟨o, oo, on, hw, h1, h2, h3, h4⟩, hsr⟩)
    (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu nrtParams _ rfl hlk)
      (nrt_spec ra mode (ctxH C2 H5) (ctxOK_H hok2 H5) hs (by ctx_tr hk) (by ctx_tr hac) (by ctx_tr hc.nrt) p.members om
        (by omega) (ptrsRep_mono hp35 (fun _ _ => memberRep_mono hp35) hM2) p.nP (by omega) ctx hN2 hP hI2 hnI
        (by omega) holes o3 oq (blkAt_mono hdh hp35) (blkAt_mono (blkAt_mono hpb hpH3) hp35) vsL hlv hcs2
        _ 0 {} [] Hb.length Hc.length H5 s4 rfl (by omega) (List.prefix_refl _) hns0 hout0))
    (fun r w s5 H6 hp6 ⟨o6, oo6, on6, hw6, h60, hout6, h61, hns6⟩ => ?_)
  subst hw6
  obtain ⟨outs, ns⟩ := r
  simp only at hout6 hns6 ⊢
  have hp6' : H5 <+: H6 := hp6
  refine UD.specR_heapLoadI' (C := ctxH C1 H6) cbpOuts (vv cbpR2) o6 _ h60 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
  refine UD.specR_heapLoadI' (C := ctxH C1 H6) cbpNs _ (o6 + 1) _ h61 (by decide)
    (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C o6) ?_
  have hpm : p.members ≠ [] := by
    intro he; rw [blockNestCtx] at hr; simp only [BlockShape.formers, he, List.map_nil] at hr; exact AM.fail_ok hr
  obtain ⟨m0, mrest, hm0⟩ : ∃ m0 mrest, p.members = m0 :: mrest := by
    cases hq : p.members with
    | nil => exact absurd hq hpm
    | cons a b => exact ⟨a, b, rfl⟩
  have hok6 := ctxOK_H hok1 H6
  refine specR_atEntry fun t6 ht6 => ?_
  have hx6 : Ext C.St s5.store := hx1.trans ht6.sr.floor
  have hSd5 : denoteL s5.store.ls ctx.sort = some lsr := by rw [hS]; exact denoteL_ext hSd hx6
  have hz := sr_zeroLevel ht6.sr
  have hco6 := ht6.sr.cok
  unfold cbpTail
  simp only [zeroLevel, bind_assoc]
  refine specR_pinXI (C := ctxH C1 H6) hok6 pinZeroLevel 1 C.pins.zeroLevel _
    (fun s hp => pinZeroLevel_run (C := ctxH C1 H6) hok6 hp) (pin_zeroLevel_cell hok6) cbpZ (by decide) ?_
  refine specR_callNIH (C := ctxH C1 H6) cbpO LLeq.fEqv [LEq.pLa, LEq.pLb] [vv cbpSr, vv cbpZ] LLeq.eqvBody
    [Enc.idxW ctx.sort, Enc.idxW C.pins.zeroLevel] (by decide) rfl (by decide) hc.eqv
    ⟨by simp +decide [sev, Env.get_cons, Env.get, cbpParams, ctxEnv, hS], by simp +decide [sev, Env.get_cons] <;> rfl, trivial⟩
    (LLeq.PostOB (ctxH C1 H6)) (fun o w s' H' => H' = H6 ∧ w = LLeq.obW o)
    (fun o w s' st ⟨hw, hsr⟩ => ⟨H6, List.prefix_refl _, ⟨rfl, hw⟩, hsr⟩)
    (fun u' hu _ hlk => Knot.specR_of_pre u' (pre_of_lookups hu [LEq.pLa, LEq.pLb] _ rfl hlk)
      (heqS C1 rfl hok1 H6 ctx.sort C.pins.zeroLevel s5 lsr .zero hSd5 hz hco6))
    (fun o w s7 H7 hp7 ⟨eH7, hw⟩ => ?_)
  subst hw; subst H7
  -- `isProp`, then the sorts
  have hrest : ∀ (ip : Bool), (o == some true) = ip → ∀ (Γ : Env) (M : Mem),
      Γ.get cbpIp = some (boolW ip) → Γ.get cbpOuts = some (cellA C oo6) → Γ.get cbpNs = some (cellA C on6) →
      Γ.get cbpMs = some (cellA C om) → Γ.get cbpHi = some (BitVec.ofNat 64 (p.nP + p.members.length)) →
      Γ.get cbpSr = some (Enc.idxW p.resSort) →
      SpecR (σ := σ) (Inv (ctxH C1 H6) s7 Γ M (ctxLocals ++ cbpLocals)) (cbpTail.cbpSorts C) s7
        (checkAbsCtorSortsAll mode C.fe ctx ip ((p.members.drop 0).map (·.ctors)) outs >>= fun _ => pure (outs, ns))
        (PostCBP (ctxSt (ctxH C H) s1.store)) := by
    intro ip hip Γ M gIp gO gN gM gHi gSr
    unfold cbpTail.cbpSorts
    have hp16 : H <+: H6 := ((((hp1'.trans hpa').trans hp2').trans hp3').trans hp35).trans hp6'
    have hMH6 : PtrsRep C H6 om (MemberRep C H6) p.members := ptrsRep_mono hp16 (fun _ _ => memberRep_mono hp16) hMH
    have h0l : 0 < p.members.length := by rw [hm0]; simp
    obtain ⟨o0, ho0, hrep0⟩ := hMH6.2 0 h0l
    obtain ⟨⟨oc0, hoc0, hcv0⟩, -, -, -⟩ := hrep0
    obtain ⟨-, ⟨wl, hwl, olp, hwlo, hlpb⟩, -⟩ := hcv0
    subst hwlo
    have hlps0 : p.members[0].cvT.levelParams = p.lps := by simp [BlockShape.lps, hm0]
    refine UD.specR_heapLoadI' (C := ctxH C1 H6) cbpP0 _ (om + 1 + 0) _ ho0 (by decide)
      (by simp only [sev, sev_vv]; simp [gM]; exact cellA_add8 C om) ?_
    refine UD.specR_heapLoadI' (C := ctxH C1 H6) cbpQ0 (vv cbpP0) o0 _ hoc0 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C1 H6) cbpLp _ (oc0 + 1) _ hwl (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C oc0) ?_
    refine UD.specR_heapLoadI' (C := ctxH C1 H6) cbpLn (vv cbpLp) olp _ hlpb.1 (by decide)
      (by simp +decide [sev, Env.get_cons]; rfl) ?_
    rw [hlps0] at hlpb
    refine specR_atEntry fun t7 ht7 => ?_
    obtain ⟨os6, hos6l, hos6b, hos6r⟩ := hout6
    have hol6 := Big.blk_small0 (ctxOK_H hok1 H6) ht7.sr hos6b
    simp only [List.length_map] at hol6
    have houtl : ∀ o ∈ outs, o.length < 2 ^ 58 := by
      intro o ho
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ho
      obtain ⟨osi, hosil, hosib, -⟩ := hos6r i hi (by omega)
      have := Big.blk_small0 (ctxOK_H hok1 H6) ht7.sr hosib
      simp only [List.length_map] at this; omega
    have hhi6 : ctx.hiAt 0 = p.nP + p.members.length := by simp [NestCtx.hiAt, hP, hN, BlockShape.memberNames]
    have hSd1 : denoteL (ctxH C1 H6).St.ls ctx.sort = some lsr := by rw [hS]; exact denoteL_ext hSd hx1
    have hkl1 : ks.length = ctx.lps.length := by rw [hL]; exact hkl
    have hks1 : ∀ j (hj : j < ctx.lps.length), denoteN (ctxH C1 H6).St.ns ctx.lps[j] = some (ks[j]'(by rw [hkl1]; exact hj)) :=
      fun j hj => by
        have hj' : j < p.lps.length := by rw [← hL]; exact hj
        have := denoteN_ext (hks j hj') hx1
        simp only [hL]; exact this
    have hlpb1 : BlkAt (ctxH C1 H6).H olp (ctx.lps.map Enc.idxW) := by rw [hL]; exact hlpb
    refine specR_callNIH (C := ctxH C1 H6) cbpV fCaa caaParams
      [.const 0, vv cbpMs, vv cbpOuts, vv cbpLp, vv cbpLn, vv cbpHi, vv cbpSr, vv cbpIp] caaBody
      [BitVec.ofNat 64 0, cellA C om, cellA C oo6, cellA C olp, BitVec.ofNat 64 ctx.lps.length,
        BitVec.ofNat 64 (p.nP + p.members.length), Enc.idxW ctx.sort, boolW ip] (by decide) rfl (by decide) hc.cas.caa
      ⟨rfl, by simp +decide [sev, Env.get_cons, gM], by simp +decide [sev, Env.get_cons, gO],
        by simp +decide [sev, Env.get_cons] <;> rfl,
        by simp +decide [sev, Env.get_cons, hL, hlps0],
        by simp +decide [sev, Env.get_cons, gHi], by simp +decide [sev, Env.get_cons, gSr, hS],
        by simp +decide [sev, Env.get_cons, gIp], trivial⟩
      (Decl.PostU (ctxH C1 H6)) (fun _ _ _ _ => True) (fun a w s' st ⟨H', hp', hsr⟩ => ⟨H', hp', trivial, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu caaParams _ rfl hlk)
        (caa_spec mode ra (ctxH C1 H6) hok6 hs (by ctx_tr hk) (by ctx_tr hac) (by ctx_tr hc.cas)
          (heqS (ctxH C1 H6) rfl hok6) ctx ip lsr hSd1 (p.nP + p.members.length) hhi6 (by omega) olp ks hlpb1 hkl1 hks1
          (by rw [hL]; omega) p.members om (by omega) hMH6
          (fun m hm => ⟨(hcs m hm).1, fun c hc' => ((hcs m hm).2 c hc').2⟩) outs oo6 ⟨os6, hos6l, hos6b, hos6r⟩ houtl
          (by omega) _ 0 H6 s7 rfl (by omega) (List.prefix_refl _)))
      (fun _ w s8 H8 hp8 _ => ?_)
    have hp8' : H6 <+: H8 := hp8
    refine specR_alloc2I (ctxOK_H hok1 H8) cbpR3 (vv cbpOuts) (vv cbpNs) (cellA C oo6) (cellA C on6) (by decide)
      (fun _ => by simp +decide [sev, Env.get_cons, gO]) (fun _ => by simp +decide [sev, Env.get_cons, gN])
      (fun H9 ws9 hp9 hws9 => ?_)
    obtain ⟨k0, k1⟩ := img2_get H9 ws9 (cellA C oo6) (cellA C on6) hws9
    have h9 := img2_prefix H9 ws9 (cellA C oo6) (cellA C on6) hws9
    have hp9' : H8 <+: _ := (hp9 : H8 <+: H9).trans h9
    have hp69 : H6 <+: _ := hp8'.trans hp9'
    exact specR_returnI (vv cbpR3) (cellA C H9.length) (by simp [sev, Env.get_cons]; rfl) (fun t ht =>
      ⟨_, H9.length, oo6, on6, hp16.trans hp69, rfl, k0,
        ⟨os6, hos6l, blkAt_mono hos6b hp69, fun i hi ho => outsRep_mono hp69 (hos6r i hi ho)⟩, k1,
        pRep_mono hp69 (fun _ _ => nfRep_mono hp69) hns6, sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  by_cases ho : o = some true
  · subst ho
    refine specR_ifI _ 1 (by simp +decide [sev, Env.get_cons, LLeq.obW, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]) (fun _ => ?_) (fun h => absurd h (by decide))
    refine specR_assignI cbpIp (.const 1) (boolW true) (by decide) (by simp [sev, boolW]) ?_
    exact hrest true rfl _ _ (by simp [Env.get_cons]) (by simp +decide [Env.get_cons, Env.get, cbpParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, cbpParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, cbpParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, cbpParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, cbpParams, ctxEnv])
  have hob : LLeq.obW o ≠ 2#64 := by
    rcases o with _ | ⟨_ | _⟩ <;> simp [LLeq.obW] at ho ⊢ <;> decide
  refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Flapjack.Compiler.Encoders.Asm.wordCmpHOL]; exact hob) (fun h => absurd rfl h) (fun _ => ?_)
  refine specR_assignI cbpIp (.const 0) (boolW false) (by decide) (by simp [sev, boolW]) ?_
  rw [show (o == some true) = false by simpa using ho]
  exact hrest false (by simpa using ho) _ _ (by simp [Env.get_cons]) (by simp +decide [Env.get_cons, Env.get, cbpParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, cbpParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, cbpParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, cbpParams, ctxEnv]) (by simp +decide [Env.get_cons, Env.get, cbpParams, ctxEnv])

end

end ConPanqueque.T.Ind
