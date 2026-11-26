import ConPanqueque.T.Ind.NestCtors

/-!
# `nestRoot`: every member's constructors through `nestCtors`, sharing the walk's state
-/

open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact Flapjack.Basis.Pure.MlString
open ConPanqueque.Logic ConPanqueque.V
open ConRon.Arena ConRon.Bridge

namespace ConPanqueque.T.Ind

open ConPanqueque.T ConPanqueque.T.Ex ConPanqueque.T.Knot ConPanqueque.T.ExS ConPanqueque.T.ExI ConPanqueque.T.ExSP
open ConPanqueque.T.ExG ConPanqueque.T.ExPre ConPanqueque.T.ExA ConPanqueque.T.Decl ConPanqueque.T.WC

def nrtT := ofString "nrt_t"
def nrtNs := ofString "nrt_ns"
def nrtOuts := ofString "nrt_outs"
def nrtMs := ofString "nrt_ms"
def nrtNP := ofString "nrt_np"
def nrtHi := ofString "nrt_hi"
def nrtUs := ofString "nrt_us"
def nrtDH := ofString "nrt_dh"
def nrtDn := ofString "nrt_dn"
def nrtPs := ofString "nrt_ps"
def nrtL := ofString "nrt_l"
def nrtP := ofString "nrt_p"
def nrtCs := ofString "nrt_cs"
def nrtE0 := ofString "nrt_e0"
def nrtR := ofString "nrt_r"
def nrtO := ofString "nrt_o"
def nrtNs2 := ofString "nrt_ns2"
def nrtOuts2 := ofString "nrt_outs2"
def nrtR2 := ofString "nrt_r2"
def fNrt := ofString "nestRoot"

def nrtParams : List MlS := [nrtT, nrtNs, nrtOuts, nrtMs, nrtNP, nrtHi, nrtUs, nrtDH, nrtDn, nrtPs]
def nrtLocals : List MlS := [nrtL, nrtP, nrtCs, nrtE0, nrtR, nrtO, nrtNs2, nrtOuts2, nrtR2]

def nrtBody (C : Ctx) : ProgHOL 64 := prologue nrtLocals
  (.seq (.assign .local nrtL (.load .one (vv nrtMs)))
  (.ite (.cmp .lower (vv nrtT) (vv nrtL))
    (.seq (.assign .local nrtP (.load .one (.op .add [.op .add [vv nrtMs, .const 8], .shift .lsl (vv nrtT) (.const 3)])))
    (.seq (.assign .local nrtCs (.load .one (.op .add [vv nrtP, .const 24])))
    (alloc1 C nrtE0 (.const 0)
    (.seq (.call (some (some (.local, nrtR), none)) fNct
        [vv nrtCs, .const 0, vv nrtNs, vv nrtE0, vv nrtMs, vv nrtNP, vv nrtHi, vv nrtUs, vv nrtDH, vv nrtDn, vv nrtPs])
    (.seq (.assign .local nrtO (.load .one (vv nrtR)))
    (.seq (.assign .local nrtNs2 (.load .one (.op .add [vv nrtR, .const 8])))
    (.seq (.call (some (some (.local, nrtOuts2), none)) ExPre.fAppend [vv nrtOuts, vv nrtO])
    (.seq (.call (some (some (.local, nrtR2), none)) fNrt
        [.op .add [vv nrtT, .const 1], vv nrtNs2, vv nrtOuts2, vv nrtMs, vv nrtNP, vv nrtHi, vv nrtUs, vv nrtDH,
          vv nrtDn, vv nrtPs])
      (.return (vv nrtR2))))))))))
    (alloc2 C nrtR (vv nrtOuts) (vv nrtNs) (.return (vv nrtR)))))

structure NRTCodes (C : Ctx) : Prop where
  nct : NCTCodes C
  self : C.code.lookup fNrt = some (nrtParams.map (fun p => (p, ShapeHOL.one)), nrtBody C, .one)

section
variable {σ : Type}

theorem nrt_none (C : Ctx) (vals : List (BitVec 64)) :
    ∀ x, x ∈ nrtLocals → (ctxEnv C ++ nrtParams.zip vals).get x = none :=
  Knot.params_none C nrtLocals nrtParams vals (by decide) (by decide)

/-- A member's outputs: a block of `(kinds, closed)` pointers. -/
def OutsRep (C : Ctx) (H : List (BitVec 64)) (o : Nat) (xs : List (List NestFieldKind × EIdx)) : Prop :=
  PRep C H o (OutRep C) xs

theorem outsRep_mono {C : Ctx} {H H' : List (BitVec 64)} (hp : H <+: H') {o : Nat}
    {xs : List (List NestFieldKind × EIdx)} (h : OutsRep C H o xs) : OutsRep C H' o xs :=
  pRep_mono hp (fun _ _ => outRep_mono hp) h

/-- `nestRoot`'s answer `[outs, ns]`. -/
def PostNRT (C : Ctx) (ns : NestState) (r : List (List (List NestFieldKind × EIdx)) × NestState) (w : BitVec 64)
    (s' : AState) (st : PState σ) : Prop :=
  ∃ H' o oo on, C.H <+: H' ∧ w = cellA C o ∧ H'[o]? = some (cellA C oo) ∧ PRep C H' oo (OutsRep C) r.1 ∧
    H'[o + 1]? = some (cellA C on) ∧ PRep C H' on (NfRep C) r.2.ctorNfs.toList ∧ r.2.keys = ns.keys ∧
    r.2.active = ns.active ∧ SR (ctxH C H') s' st

theorem postNRT_locals (C : Ctx) (ns : NestState) : ∀ a w s' (st : PState σ) (L : HolFiniteMapExact MlS (ValueHOL 64)),
    PostNRT C ns a w s' st → PostNRT C ns a w s' { st with locals := L } :=
  fun _ _ _ _ _ ⟨H', o, oo, on, hp, hw, h1, h2, h3, h4, h5, h6, hs⟩ =>
    ⟨H', o, oo, on, hp, hw, h1, h2, h3, h4, h5, h6, sr_of_eq hs rfl rfl rfl rfl⟩

end

section
variable {σ : Type}

set_option maxHeartbeats 16000000 in
/-- **`nestRoot`** over the members from `t` on. -/
theorem nrt_spec (ra : ConPanqueque.Hash.RuntimeAssumptions) (mode : ConLeche.CheckMode) (C : Ctx) (hok : CtxOK C)
    (hs : C.side = false) (hk : KCodes C Comp.kBodies) (hac : Comp.AllCodes mode C) (hc : NRTCodes C)
    (ms : List MemberShape) (om : Nat) (hml : ms.length < 2 ^ 56) (hM : PtrsRep C C.H om (MemberRep C C.H) ms)
    (nP : Nat) (hnP : nP < 2 ^ 56) (ctx : NestCtx) (hN : ctx.names = ms.map (·.cvT.name)) (hP : ctx.nP = nP)
    (hI : ctx.nIdxs = ms.map (·.nIdx)) (hnI : ∀ t (ht : t < ms.length), ms[t].nIdx < 2 ^ 63)
    (hpl : ctx.params.length < 2 ^ 56) (holes : List EIdx) (pdh pp : Nat)
    (hdh : BlkAt C.H pdh ((ctx.params ++ holes).map Enc.idxW)) (hpp : BlkAt C.H pp (ctx.params.map Enc.idxW))
    (vsL : List ConLeche.Level) (hlv : denoteLs C.St.lss ctx.lvls = some vsL)
    (hcs : ∀ m ∈ ms, m.ctors.length < 2 ^ 58 ∧ ∀ c ∈ m.ctors, CVDen c.1 C.St ∧ c.2 < 2 ^ 56) :
    ∀ f t (ns : NestState) (outs : List (List (List NestFieldKind × EIdx))) (ons oouts : Nat) (H : List (BitVec 64))
      (s : AState), ms.length - t = f → t ≤ ms.length → C.H <+: H →
      PRep C H ons (NfRep C) ns.ctorNfs.toList → PRep C H oouts (OutsRep C) outs →
      SpecR (σ := σ) (Pre (ctxH C H) s (nrtParams.zip [BitVec.ofNat 64 t, cellA C ons, cellA C oouts, cellA C om,
        BitVec.ofNat 64 nP, BitVec.ofNat 64 (nP + ms.length), Enc.idxW ctx.lvls, cellA C pdh,
        BitVec.ofNat 64 ctx.params.length, cellA C pp])) (nrtBody C) s
        (nestRoot mode C.fe ctx holes ((ms.drop t).map (·.ctors)) ns outs) (PostNRT (ctxH C H) ns) := by
  intro f
  induction f with
  | zero =>
    intro t ns outs ons oouts H s hf ht hp hns houts
    have htl : t = ms.length := by omega
    subst htl
    refine specR_prologue (postNRT_locals _ _) (nrt_none _ _) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) nrtL (vv nrtMs) om _ (get_prefix hM.1 hp) (by decide)
      (by simp +decide [sev, Env.get, nrtParams, ctxEnv]; rfl) ?_
    refine specR_ifI _ 0 (by simp +decide [sev, Env.get_cons, Env.get, nrtParams, ctxEnv, Flapjack.Compiler.Encoders.Asm.wordCmpHOL])
      (fun h => absurd rfl h) (fun _ => ?_)
    rw [List.drop_length, List.map_nil, nestRoot]
    obtain ⟨os1, hl1, hb1, hr1⟩ := houts
    obtain ⟨os2, hl2, hb2, hr2⟩ := hns
    refine specR_alloc2I (ctxOK_H hok H) nrtR (vv nrtOuts) (vv nrtNs) (cellA C oouts) (cellA C ons) (by decide)
      (fun _ => (by simp +decide [sev, Env.get_cons, Env.get, nrtParams, ctxEnv])) (fun _ => (by simp +decide [sev, Env.get_cons, Env.get, nrtParams, ctxEnv])) (fun H2 ws hp2 hws => ?_)
    obtain ⟨g0, g1⟩ := img2_get H2 ws (cellA C oouts) (cellA C ons) hws
    have h2 := img2_prefix H2 ws (cellA C oouts) (cellA C ons) hws
    have hp2' : H <+: _ := (hp2 : H <+: H2).trans h2
    exact specR_returnI (vv nrtR) (cellA C H2.length) (by simp [sev, Env.get_cons]; rfl) (fun tt ht =>
      ⟨_, H2.length, oouts, ons, hp2', rfl, g0,
        ⟨os1, hl1, blkAt_mono hb1 hp2', fun i hi ho => outsRep_mono hp2' (hr1 i hi ho)⟩, g1,
        ⟨os2, hl2, blkAt_mono hb2 hp2', fun i hi ho => nfRep_mono hp2' (hr2 i hi ho)⟩, rfl, rfl,
        sr_of_eq ht.sr rfl rfl rfl rfl⟩)
  | succ f ih =>
    intro t ns outs ons oouts H s hf ht hp hns houts
    have htl : t < ms.length := by omega
    refine specR_prologue (postNRT_locals _ _) (nrt_none _ _) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) nrtL (vv nrtMs) om _ (get_prefix hM.1 hp) (by decide)
      (by simp +decide [sev, Env.get, nrtParams, ctxEnv]; rfl) ?_
    have hlw := ConPanqueque.T.Decl.nd_lt_iff t ms.length (by omega) (by omega)
    refine specR_ifI _ 1 (by simp only [sev, sev_vv, Env.get_cons]; simp +decide [Env.get, nrtParams, ctxEnv,
        Flapjack.Compiler.Encoders.Asm.wordCmpHOL, hlw.mpr htl]) (fun _ => ?_) (fun h => absurd h (by decide))
    obtain ⟨omt, hmt, hrep⟩ := hM.2 t htl
    obtain ⟨-, -, -, ⟨ol, hol, hcsr⟩⟩ := hrep
    refine UD.specR_heapLoadI' (C := ctxH C H) nrtP _ (om + 1 + t) _ (get_prefix hmt hp) (by decide)
      (by simp +decide [sev, Env.get_cons, Env.get, nrtParams, ctxEnv]; show _ = cellA C (om + 1 + t)
          rw [← cellA_shl C (om + 1) t (by omega), ← cellA_add8]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H) nrtCs _ (omt + 3) _ (get_prefix hol hp) (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add_ofNat C omt 3) ?_
    rw [List.drop_eq_getElem_cons htl, List.map_cons, nestRoot]
    have hhi : ctx.hiAt 0 = nP + ms.length := by simp [NestCtx.hiAt, hP, hN]
    rw [hhi, hN]
    refine specR_alloc1I (ctxOK_H hok H) nrtE0 (.const 0) 0 (by decide) (fun _ => rfl) (fun Ha wsa hpa hwsa => ?_)
    have ga : ((Ha ++ wsa).set Ha.length 0)[Ha.length]? = some 0 := by simp [List.getElem?_set, hwsa]
    have hpa' : H <+: _ := (hpa : H <+: Ha).trans (img1_prefix Ha wsa 0 hwsa)
    have he0 : PRep C ((Ha ++ wsa).set Ha.length 0) Ha.length (OutRep C) ([] : List (List NestFieldKind × EIdx)) :=
      ⟨[], rfl, ⟨by simpa using ga, fun i hi => by simp at hi⟩, fun i hi => by simp at hi⟩
    have hmc := hcs ms[t] (List.getElem_mem htl)
    refine specR_callNIH (C := ctxH C _) nrtR fNct nctParams
      [vv nrtCs, .const 0, vv nrtNs, vv nrtE0, vv nrtMs, vv nrtNP, vv nrtHi, vv nrtUs, vv nrtDH, vv nrtDn, vv nrtPs]
      (nctBody C) [cellA C ol, BitVec.ofNat 64 0, cellA C ons, cellA C Ha.length, cellA C om, BitVec.ofNat 64 nP,
        BitVec.ofNat 64 (nP + ms.length), Enc.idxW ctx.lvls, cellA C pdh, BitVec.ofNat 64 ctx.params.length, cellA C pp]
      (by decide) rfl (by decide) hc.nct.self
      ⟨by simp +decide [sev, Env.get_cons] <;> rfl, rfl, by simp +decide [sev, Env.get_cons, Env.get, nrtParams, ctxEnv] <;> rfl, by simp +decide [sev, Env.get_cons] <;> rfl,
        by simp +decide [sev, Env.get_cons, Env.get, nrtParams, ctxEnv] <;> rfl, (by simp +decide [sev, Env.get_cons, Env.get, nrtParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nrtParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nrtParams, ctxEnv]), by simp +decide [sev, Env.get_cons, Env.get, nrtParams, ctxEnv] <;> rfl, (by simp +decide [sev, Env.get_cons, Env.get, nrtParams, ctxEnv]), by simp +decide [sev, Env.get_cons, Env.get, nrtParams, ctxEnv] <;> rfl, trivial⟩
      (PostNCT (ctxH C _) ns) (fun r w _ H' => ∃ o oo on, w = cellA C o ∧ H'[o]? = some (cellA C oo) ∧
        PRep C H' oo (OutRep C) r.1 ∧ H'[o + 1]? = some (cellA C on) ∧ PRep C H' on (NfRep C) r.2.ctorNfs.toList ∧
        r.2.keys = ns.keys ∧ r.2.active = ns.active)
      (fun r w s' st ⟨H', o, oo, on, hp', hw, h1, h2, h3, h4, h5, h6, hsr⟩ =>
        ⟨H', hp', ⟨o, oo, on, hw, h1, h2, h3, h4, h5, h6⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu nctParams _ rfl hlk)
        (nct_spec ra mode C hok hs hk hac hc.nct ms om hml hM nP hnP ctx hN hP hI hnI hpl holes pdh pp hdh hpp vsL hlv
          ms[t].ctors ol hcsr hmc.1 hmc.2 _ 0 ns [] ons Ha.length _ s rfl (by omega) (hp.trans hpa')
          (pRep_mono hpa' (fun _ _ => nfRep_mono hpa') hns) he0))
      (fun r w s1 H1 hp1 ⟨o1, oo1, on1, hw1, h10, hout1, h11, hns1, hk1, ha1⟩ => ?_)
    subst hw1
    obtain ⟨o, ns2⟩ := r
    simp only at hout1 hns1 hk1 ha1 ⊢
    have hp1' : _ <+: H1 := hp1
    refine UD.specR_heapLoadI' (C := ctxH C H1) nrtO (vv nrtR) o1 _ h10 (by decide) (by simp [sev, Env.get_cons]; rfl) ?_
    refine UD.specR_heapLoadI' (C := ctxH C H1) nrtNs2 _ (o1 + 1) _ h11 (by decide)
      (by simp +decide [sev, Env.get_cons]; exact cellA_add8 C o1) ?_
    obtain ⟨os1, hl1, hb1, hr1⟩ := pRep_mono (hpa'.trans hp1') (fun _ _ => outsRep_mono (hpa'.trans hp1')) houts
    refine specR_appendI hok hc.nct.nnf.app H1 nrtOuts2 (vv nrtOuts) (vv nrtO) (os1.map (cellA C)) (cellA C oo1) oouts hb1
      (by decide) (by simp +decide [sev, Env.get_cons, Env.get, nrtParams, ctxEnv]) (by simp +decide [sev, Env.get_cons]) (fun H2 oo2 hp2 hb2 => ?_)
    have hout2 : PRep C H2 oo2 (OutsRep C) (outs ++ [o]) :=
      pRep_snoc os1 hl1 (fun i hi ho => outsRep_mono hp2 (hr1 i hi ho)) (outsRep_mono hp2 hout1) hb2
    refine specR_congr (m' := nestRoot mode C.fe ctx holes ((ms.drop (t + 1)).map (·.ctors)) ns2 (outs ++ [o]) >>=
      fun r => pure r) (by simp only [bind_pure]) ?_
    have hpH2 : C.H <+: H2 := ((hp.trans hpa').trans hp1').trans hp2
    refine specR_callNIH (C := ctxH C H2) nrtR2 fNrt nrtParams
      [.op .add [vv nrtT, .const 1], vv nrtNs2, vv nrtOuts2, vv nrtMs, vv nrtNP, vv nrtHi, vv nrtUs, vv nrtDH, vv nrtDn,
        vv nrtPs] (nrtBody C)
      [BitVec.ofNat 64 (t + 1), cellA C on1, cellA C oo2, cellA C om, BitVec.ofNat 64 nP, BitVec.ofNat 64 (nP + ms.length),
        Enc.idxW ctx.lvls, cellA C pdh, BitVec.ofNat 64 ctx.params.length, cellA C pp] (by decide) rfl (by decide) hc.self
      ⟨by simp +decide [sev, Env.get_cons, Env.get, nrtParams, ctxEnv]; exact e_succ t,
        by simp +decide [sev, Env.get_cons] <;> rfl, by simp +decide [sev, Env.get_cons] <;> rfl, by simp +decide [sev, Env.get_cons, Env.get, nrtParams, ctxEnv] <;> rfl, (by simp +decide [sev, Env.get_cons, Env.get, nrtParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nrtParams, ctxEnv]), (by simp +decide [sev, Env.get_cons, Env.get, nrtParams, ctxEnv]),
        by simp +decide [sev, Env.get_cons, Env.get, nrtParams, ctxEnv] <;> rfl, (by simp +decide [sev, Env.get_cons, Env.get, nrtParams, ctxEnv]), by simp +decide [sev, Env.get_cons, Env.get, nrtParams, ctxEnv] <;> rfl, trivial⟩
      (PostNRT (ctxH C H2) ns2) (fun r w _ H' => ∃ o oo on, w = cellA C o ∧ H'[o]? = some (cellA C oo) ∧
        PRep C H' oo (OutsRep C) r.1 ∧ H'[o + 1]? = some (cellA C on) ∧ PRep C H' on (NfRep C) r.2.ctorNfs.toList ∧
        r.2.keys = ns2.keys ∧ r.2.active = ns2.active)
      (fun r w s' st ⟨H', o, oo, on, hp', hw, h1, h2, h3, h4, h5, h6, hsr⟩ =>
        ⟨H', hp', ⟨o, oo, on, hw, h1, h2, h3, h4, h5, h6⟩, hsr⟩)
      (fun u hu _ hlk => Knot.specR_of_pre u (pre_of_lookups hu nrtParams _ rfl hlk)
        (ih (t + 1) ns2 (outs ++ [o]) on1 oo2 H2 s1 (by omega) (by omega) hpH2
          (pRep_mono hp2 (fun _ _ => nfRep_mono hp2) hns1) hout2))
      (fun r w s3 H3 hp3 ⟨o3, oo3, on3, hw3, h1, h2, h3, h4, h5, h6⟩ => ?_)
    subst hw3
    exact specR_returnI _ (cellA C o3) (by simp [sev, Env.get_cons])
      (fun tt ht => ⟨H3, o3, oo3, on3, ((hpa'.trans hp1').trans hp2).trans hp3, rfl, h1, h2, h3, h4,
        h5.trans hk1, h6.trans ha1, sr_of_eq ht.sr rfl rfl rfl rfl⟩)

end

end ConPanqueque.T.Ind
